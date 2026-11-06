import concurrent.futures, argparse, datetime, hashlib, json, os, pathlib, re, shutil, subprocess, sys
from audit_output import check_axiom_output
from source_audit import lean_code, project_dependencies, fresh_lean_path, PROJECT_PREFIXES, forbidden_constructs
from verification_guards import verify_environment_pins, EnvironmentPinError, compile_checked
ROOT = pathlib.Path(__file__).resolve().parent
p = argparse.ArgumentParser()
p.add_argument('--module', action='append', required=True)
p.add_argument('--theorem', action='append', required=True)
p.add_argument('--jobs', type=int, default=6)
a = p.parse_args()
if not 1 <= a.jobs <= 12: p.error('jobs must be 1..12')
run = ROOT / 'verification' / datetime.datetime.now().strftime('%Y%m%d-%H%M%S-%f')
src, build, logs = run / 'src', run / 'build', run / 'logs'
for d in (src, build, logs): d.mkdir(parents=True)
sha = lambda data: hashlib.sha256(data).hexdigest()
modules, visiting, ordered = {}, set(), []
def visit(name):
    if name.split('.')[0] not in PROJECT_PREFIXES: raise RuntimeError('Unapproved project module: '+name)
    if name in modules: return
    if name in visiting: raise RuntimeError('cyclic imports: '+name)
    visiting.add(name)
    path = ROOT / (name.replace('.', '/')+'.lean')
    data = path.read_bytes()
    content = data.decode('utf-8-sig')
    deps = project_dependencies(content)
    for dep in deps: visit(dep)
    modules[name] = {'source':str(path), 'source_sha256':sha(data), 'dependencies':deps}
    dest = src / (name.replace('.', '/')+'.lean')
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(data)
    snapshot_hash = sha(dest.read_bytes())
    if snapshot_hash != modules[name]['source_sha256']:
        raise RuntimeError('snapshot creation hash mismatch: '+name)
    modules[name]['snapshot_creation_sha256'] = snapshot_hash
    if sha(path.read_bytes()) != sha(data): raise RuntimeError('source changed while snapshotting: '+name)
    visiting.remove(name); ordered.append(name)
for name in a.module: visit(name)
# Lexical source scanning also drives the explicit transitive import closure.
for name in ordered:
    s=(src/(name.replace('.', '/')+'.lean')).read_text(encoding='utf-8-sig')
    code=lean_code(s)
    bad=forbidden_constructs(s)
    if bad: raise RuntimeError('forbidden proof constructs in '+name+': '+str(sorted(set(bad))))
lean=shutil.which('lean')
if lean is None: raise RuntimeError('Run via the pinned lake env so lean and mathlib are available')
env=os.environ.copy()
env['LEAN_PATH'], excluded_paths = fresh_lean_path(env.get('LEAN_PATH',''), build, ROOT)
report={'passed':False,'run':str(run),'modules':modules,'order':ordered,'theorems':a.theorem,
        'lean_executable':lean,'lean_version':None,
        'project_source_prefixes':sorted(PROJECT_PREFIXES),'excluded_inherited_project_paths':excluded_paths,
        'effective_lean_path':env['LEAN_PATH']}
def save(): (run/'verification.json').write_text(json.dumps(report,indent=2),encoding='utf-8')
# Keep the package's pinned Lake files unchanged and record their identity.
report['project_pin_files'] = {name: sha((ROOT/name).read_bytes())
    for name in ('lean-toolchain','lakefile.toml','lakefile.lean') if (ROOT/name).is_file()}
try:
    report['environment_pins'] = verify_environment_pins(lean, env)
    report['lean_version'] = report['environment_pins']['lean_version_output']
except EnvironmentPinError as error:
    report['environment_pins'] = error.details
    report['failure'] = str(error)
    save()
    print('FAILED environment pins: '+str(error), flush=True)
    sys.exit(1)
def compile_one(name):
    source=src/(name.replace('.', '/')+'.lean')
    output=build/(name.replace('.', '/')+'.olean')
    output.parent.mkdir(parents=True,exist_ok=True)
    command=[lean,'-j','2','-t','0','-R',str(src),'-o',str(output),str(source)]
    # Audit is generated locally, rather than visited as a project source.
    expected_hash = (modules[name]['source_sha256'] if name in modules
                     else report['audit_source_sha256'])
    rec,stdout,stderr=compile_checked(command,source,expected_hash,env)
    rec['source_hash_kind'] = 'visited_snapshot' if name in modules else 'generated_audit'
    (logs/(name+'.stdout.log')).write_text(stdout,encoding='utf-8')
    (logs/(name+'.stderr.log')).write_text(stderr,encoding='utf-8')
    if rec['compiler_exit_code']==0 and output.is_file():
        rec['olean_sha256']=sha(output.read_bytes())
    print(name+': '+str(rec['exit_code']),flush=True)
    return rec,stdout
save()
pending, completed = set(ordered), set()
with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
    active = {}
    while pending or active:
        ready = [n for n in ordered if n in pending and set(modules[n]['dependencies']) <= completed]
        for n in ready[:max(0,a.jobs-len(active))]:
            pending.remove(n);active[pool.submit(compile_one,n)] = n
        if not active: raise RuntimeError('dependency scheduler stalled')
        done,_ = concurrent.futures.wait(active,return_when=concurrent.futures.FIRST_COMPLETED)
        for future in done:
            name=active.pop(future);rec,_=future.result()
            modules[name]['verification']=rec;save()
            if rec['exit_code']!=0:
                print('FAILED '+str(run),flush=True)
                for other in active: other.cancel()
                sys.exit(1)
            completed.add(name)
audit='\n'.join('import '+x for x in a.module)+'\n'+'\n'.join('#print axioms '+x for x in a.theorem)+'\n'
audit_data = audit.encode('utf-8')
(src/'Audit.lean').write_bytes(audit_data)
report['audit_source_sha256'] = sha(audit_data)
rec,stdout=compile_one('Audit');report['audit']=rec
axiom_check=check_axiom_output(stdout,a.theorem)
report['axiom_audit']=axiom_check
report['axioms']=axiom_check['axioms']
report['sources_unchanged']=all(sha(pathlib.Path(v['source']).read_bytes())==v['source_sha256'] for v in modules.values())
report['compiled_snapshot_hashes_match'] = all(
    v['verification']['source_hash_match']
    and v['verification']['source_sha256_before'] == v['source_sha256'] == v['snapshot_creation_sha256']
    and v['verification']['source_sha256_after'] == v['snapshot_creation_sha256']
    for v in modules.values())
report['snapshot_sources_unchanged'] = all(
    sha((src/(name.replace('.', '/')+'.lean')).read_bytes()) == v['snapshot_creation_sha256']
    for name,v in modules.items())
report['audit_snapshot_hash_matches'] = (
    rec['source_hash_match']
    and rec['source_sha256_before'] == report['audit_source_sha256'] == rec['source_sha256_after']
    and sha((src/'Audit.lean').read_bytes()) == report['audit_source_sha256'])
report['passed']=(rec['exit_code']==0 and axiom_check['passed'] and report['sources_unchanged']
    and report['environment_pins']['passed'] and report['compiled_snapshot_hashes_match']
    and report['snapshot_sources_unchanged'] and report['audit_snapshot_hash_matches'])
save();print(json.dumps({'passed':report['passed'],'certificate':str(run/'verification.json')}),flush=True)
sys.exit(0 if report['passed'] else 1)
