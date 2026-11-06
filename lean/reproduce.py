from pathlib import Path
import json,sys,subprocess
p=Path(__file__).resolve().parent
cmd=[sys.executable,str(p/'verify_full.py'),'--module','SimplexFull.VerifiedGlobal','--jobs','6']
for t in json.loads((p/'AUDIT_THEOREMS_GLOBAL.json').read_text(encoding='utf-8')):cmd+=['--theorem',t]
sys.exit(subprocess.run(cmd,cwd=p).returncode)
