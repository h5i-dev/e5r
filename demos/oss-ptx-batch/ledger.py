"""Summarize evidence gates without counting source screens as attempts."""
import json
from pathlib import Path
D=Path(__file__).resolve().parent

def report():
    ledger=json.loads((D/'ledger.json').read_text())
    rows=ledger['kernels']
    totals={k:sum(bool(r.get(k)) for r in rows if not r.get('supplemental')) for k in ('optimization_attempt','gpu_tested','fair_timing','proof_attempt','strict_accepted','accepted_win')}
    ledger['totals']=totals
    (D/'ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
    out=['# Practical OSS PTX batch scoreboard','',f'Target: approximately 50 distinct real OSS kernels. Practical totals: {totals}.','',
         'Source/build screens do not count as optimization or proof attempts. A direct edit alone does not count as a completed attempt. Strict acceptance requires the exact bound programs, direct universal equivalence, safety/races/progress/frame, replay, axiom audit and negatives. Timing wins require normal and strongest applicable baseline evidence.','',
         '| Kernel | Phase | Edited | GPU | Fair timing | Proof attempted | Strict accepted |','| --- | --- | --- | --- | --- | --- | --- |']
    for r in rows:
        out.append('| '+ ' | '.join([r['id'],r['phase']]+[str(bool(r.get(k))) for k in ('optimization_attempt','gpu_tested','fair_timing','proof_attempt','strict_accepted')])+' |')
    (D/'SCOREBOARD.md').write_text('\n'.join(out)+'\n')
if __name__=='__main__':report()
