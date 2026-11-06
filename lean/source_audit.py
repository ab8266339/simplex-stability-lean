"""Import closure and source/environment checks for the expanded certificate."""
import pathlib,re,os
PROJECT_PREFIXES=frozenset({'SimplexFull','WeakSimplexConjectureLean','SimplexUniquenessLean'})
LIBRARY_PREFIXES=frozenset({'Mathlib','Lean','Std','Batteries','Aesop','Qq','ProofWidgets','ImportGraph','Plausible','Cli'})
def lean_code(s):
    out=[];i=0;depth=0;string=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i):depth+=1;i+=2
            elif s.startswith('-/',i):depth-=1;i+=2
            else:
                if s[i]=='\n':out.append('\n')
                i+=1
        elif string:
            if s[i]=='\\':i+=2
            elif s[i]=='"':string=False;out.append(' ');i+=1
            else:
                if s[i]=='\n':out.append('\n')
                i+=1
        elif s.startswith('/-',i):depth=1;out.append(' ');i+=2
        elif s.startswith('--',i):
            end=s.find('\n',i);i=len(s) if end<0 else end
        elif s[i]=='"':string=True;out.append(' ');i+=1
        else:out.append(s[i]);i+=1
    if depth or string:raise ValueError('Unterminated Lean comment or string')
    return ''.join(out)
def import_names(content):
    """Accept conventional one-line imports; reject ambiguous header layouts."""
    clean=lean_code(content)
    names=[];body=False
    starts={'set_option','noncomputable','open','namespace','section','variable','variables',
            'universe','universes','def','abbrev','theorem','lemma','example','instance',
            'structure','class','inductive','opaque','constant','private','protected',
            'local','scoped','attribute','macro','macro_rules','syntax','elab','elab_rules',
            'notation','infix','infixl','infixr','prefix','postfix','export','initialize',
            'builtin_initialize','end'}
    for raw in clean.splitlines():
        line=raw.strip()
        if not line:continue
        match=re.fullmatch(r'(?:public[ \t]+)?import(?:[ \t]+(.*))?',line)
        if match:
            if body:raise ValueError('Import after declaration header')
            value=match.group(1)
            if not value:raise ValueError('Unsupported multiline import header')
            for name in value.split():
                if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*',name):
                    raise ValueError('Unsupported import syntax: '+name)
                prefix=name.split('.')[0]
                if prefix not in PROJECT_PREFIXES|LIBRARY_PREFIXES:
                    raise ValueError('Unaudited import root: '+name)
                if name not in names:names.append(name)
        elif re.search(r'\bimport\b',line):
            raise ValueError('Unsupported import modifiers/layout: '+line)
        elif not body:
            if line in ('prelude','module'):continue
            word=line.split()[0]
            if word in starts or line.startswith(('@[','#')) or re.match(r'public\s+(?:section|meta|def|theorem|lemma|abbrev)\b',line):
                body=True
            else:raise ValueError('Unsupported Lean header: '+line)
    return names

def forbidden_constructs(content):
    return sorted(set(re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|debug\.skipKernelTC)\b',lean_code(content))))

def project_dependencies(content):
    return [n for n in import_names(content) if n.split('.')[0] in PROJECT_PREFIXES]
def fresh_lean_path(old_path,build,source_root):
    """Exclude inherited custom project oleans; only the empty new build can supply them."""
    build=pathlib.Path(build).resolve();source_root=pathlib.Path(source_root).resolve()
    keep=[];removed=[]
    for item in old_path.split(os.pathsep):
        if not item:continue
        q=pathlib.Path(item).resolve()
        is_project=(q==source_root/'build') or any((q/ns).exists() or any((q/(ns+ext)).is_file() for ext in ('.olean','.olean.private','.olean.server','.ilean')) for ns in PROJECT_PREFIXES)
        if is_project or q==build:removed.append(str(q))
        else:keep.append(str(q))
    return os.pathsep.join([str(build),*keep]),removed
