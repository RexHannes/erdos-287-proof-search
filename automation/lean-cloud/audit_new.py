#!/usr/bin/env python3
"""Build and audit every new frontier module; empty source sets fail."""
from pathlib import Path
import subprocess,sys

ROOT=Path(__file__).resolve().parents[2]
PREFIX='RequestProject.Erdos287.Gold41'

def run(command, path):
    print('+ '+' '.join(command),flush=True)
    with path.open('w',encoding='utf-8') as log:
        process=subprocess.Popen(command,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        for line in process.stdout:
            print(line,end='',flush=True); log.write(line)
        code=process.wait()
    if code: raise subprocess.CalledProcessError(code,command)

def main():
    source=ROOT.joinpath(*PREFIX.split('.'))
    files=sorted(source.rglob('*.lean'))
    sibling=source.with_suffix('.lean')
    if sibling.is_file(): files.insert(0,sibling)
    if not files: raise ValueError('No new frontier Lean modules exist; no theorem has been verified.')
    modules=['.'.join(p.relative_to(ROOT).with_suffix('').parts) for p in files]
    output=ROOT/'.lake/frontier-verification'
    output.mkdir(parents=True,exist_ok=True)
    (output/'axioms.log').unlink(missing_ok=True)
    run(['lake','build',*modules],output/'build.log')
    body=(ROOT/'automation/lean-cloud/axiom_audit_body.lean').read_text().replace('Formalisation',PREFIX)
    check=output/'Audit.lean'
    check.write_text('\n'.join('import '+module for module in modules)+'\n'+body)
    run(['lake','env','lean',str(check)],output/'axioms.log')
    if 'AXIOM AUDIT PASSED:' not in (output/'axioms.log').read_text():
        raise ValueError('The audit did not emit its completion marker.')
    print(f'VERIFIED NEW FRONTIER: {len(modules)} modules; see {output}')

if __name__=='__main__':
    try: main()
    except (OSError,ValueError,subprocess.CalledProcessError) as error:
        print(f'FRONTIER VERIFICATION FAILED: {error}',file=sys.stderr); sys.exit(1)
