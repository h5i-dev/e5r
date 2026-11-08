#!/usr/bin/env python3
"""Generate checked no-device-read trace contracts without changing original statements."""
from pathlib import Path
import argparse,hashlib,json,re
ROOT=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--basis',type=Path,default=ROOT/'scripts/thermostat-quiet-basis.json')
parser.add_argument('--proof-dir',type=Path,default=ROOT/'verification/rv32/Projects/thermostat',help='directory compared by --check')
mode=parser.add_mutually_exclusive_group(required=True)
mode.add_argument('--check',action='store_true')
mode.add_argument('--emit',type=Path,help='emit companions into an empty/staging directory')
args=parser.parse_args()
rv=ROOT/'verification/rv32';base=rv/'Projects/thermostat'
basis=json.loads(args.basis.read_text());assert basis['schema']=='e5r.thermostat.quiet-basis.v1'
assert hashlib.sha256((rv/basis['elf']['path']).read_bytes()).hexdigest()==basis['elf']['sha256'],'ELF identity changed'
mods={}
for name,expected in basis['sources'].items():
 path=rv/name
 assert path.parent==base and path.suffix=='.lean',('invalid basis path',name)
 source=path.read_bytes();assert hashlib.sha256(source).hexdigest()==expected,('basis changed; review before updating',name)
 assert path.stem not in mods,path
 mods[path.stem]=source.decode()
rendered={};bindings=[]
# Generation is untrusted text manipulation. Every emitted theorem is checked
# by Lean, then the full job and independent kernel replay before acceptance.
def protect(text):
 assert '__QUIET_PROTECTED_' not in text,'reserved generation marker in source'
 protected=[];parts=[];i=0
 while i<len(text):
  start=i
  if text.startswith('--',i):
   j=text.find('\n',i);i=len(text)if j<0 else j
  elif text.startswith('/-',i):
   depth=1;i+=2
   while i<len(text)and depth:
    if text.startswith('/-',i):depth+=1;i+=2
    elif text.startswith('-/',i):depth-=1;i+=2
    else:i+=1
   assert depth==0,'unterminated source comment'
  elif text[i]=='"':
   i+=1
   while i<len(text):
    if text[i]=='\\':i+=2
    elif text[i]=='"':i+=1;break
    else:i+=1
  elif text[i]=="'" and re.match(r"'(?:[^'\\\n]|\\.)'",text[i:]):
   i+=len(re.match(r"'(?:[^'\\\n]|\\.)'",text[i:])[0])
  else:parts.append(text[i]);i+=1;continue
  key='__QUIET_PROTECTED_'+str(len(protected))+'__';protected.append((key,text[start:i]));parts.append(key)
 return ''.join(parts),protected
def restore(text,protected):
 for key,value in protected:text=text.replace(key,value)
 return text
for probe in ['"/state" -- state\n/- state /- nested -/ -/ state', "'a' state", '"escaped \\" state"']:
 masked,protected=protect(probe);assert restore(masked,protected)==probe
commands=re.compile(r'^(?:(?:private|protected) )?(?:theorem|def|abbrev|structure|inductive|namespace|end|open|set_option|variable)\b',re.M)
decls={};options={};ns_by_mod={}
for mod,s in mods.items():
 ns=[];items=list(commands.finditer(s));options[mod]=re.findall(r'^set_option .+$',s,re.M)
 for k,m in enumerate(items):
  t=s[m.start():items[k+1].start()if k+1<len(items)else len(s)]
  if t.startswith('namespace '):ns.append(t.splitlines()[0].split()[1]);continue
  if t.startswith('end '):
   if ns:ns.pop()
   continue
  if not t.startswith('theorem ')or not re.search(r'\bDetSteps?\b',t):continue
  name=re.match(r'theorem ([A-Za-z0-9_.\']+)',t)[1];namespace='.'.join(ns);full=namespace+'.'+name
  assert full not in decls,full
  decls[full]={'module':mod,'namespace':namespace,'name':name,'text':t}
roots=basis['roots']
special={'E5R.Thermostat.RamRun.sound':'E5R.Thermostat.RamRunQuiet.sound',
'E5R.Thermostat.Quiet.Step.det':'E5R.Thermostat.Quiet.Step.det_quiet',
'E5R.Thermostat.Quiet.Steps.det':'E5R.Thermostat.Quiet.Steps.det_quiet'}
# Longest qualified aliases first. A bare name resolves only in its original namespace.
def bound_names(text):
 names=set()
 for group in re.findall(r'[({]([A-Za-z_][A-Za-z0-9_\' ]*)\s*:',text):names.update(group.split())
 for group in re.findall(r'\b(?:let|have|intro|rintro)\s+([A-Za-z_][A-Za-z0-9_\' ]*)',text):names.update(group.split())
 for group in re.findall(r'(?:∀|\bfun)\s+([A-Za-z_][A-Za-z0-9_\' ]*)\s*(?::|=>)',text):names.update(group.split())
 return names
opened_by_mod={n:[word for line in re.findall(r'^open (.+)$',text,re.M)for word in line.split()if word not in {'scoped','in'}]for n,text in mods.items()}
aliases={}
for full in decls:
 aliases[full]=full;aliases[full.removeprefix('E5R.Thermostat.')]=full
def refs(d):
 found=set();bound=bound_names(protect(d['text'])[0])
 for token in re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*",protect(d['text'])[0]):
  full=aliases.get(token)
  if full is None and token not in bound:
   for opened in [d['namespace']]+list(reversed(opened_by_mod[d['module']])):
    if opened+'.'+token in decls:full=opened+'.'+token;break
  if full is not None:found.add(full)
 return found
chosen=set();deps={}
def visit(full):
 if full in chosen:return
 assert full in decls,full
 chosen.add(full)
 if full in special:return
 ds=refs(decls[full])-{full};deps[full]=ds
 for x in ds:visit(x)
for root in roots:visit(root)
# Dot-style uses of quiet erasure must retain the stronger proof.
for full in ['E5R.Thermostat.Quiet.Step.det','E5R.Thermostat.Quiet.Steps.det']:
 if full in decls and any('.det' in decls[d]['text']for d in chosen):chosen.add(full)
module_deps={};module_decls={}
for full in sorted(chosen):
 if full in special:continue
 d=decls[full];module_decls.setdefault(d['module'],[]).append(full)
 for dep in deps[full]:
  if dep not in special and decls[dep]['module']!=d['module']:module_deps.setdefault(d['module'],set()).add(decls[dep]['module'])
seen=set();active=set();order=[]
def module_visit(n):
 if n in seen:return
 assert n not in active,('cycle',n)
 active.add(n)
 for dep in sorted(module_deps.get(n,set())):module_visit(dep)
 active.remove(n);seen.add(n);order.append(n)
for root in roots:module_visit(decls[root]['module'])
for mod in order:
 # Preserve original declaration order, including dependencies in the same namespace/module.
 ordered=sorted(module_decls[mod],key=lambda f:mods[mod].index(decls[f]['text']))
 lines=['-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.',f'import Projects.thermostat.{mod}','import Projects.thermostat.QuietDet','import Projects.thermostat.RamRunQuiet']
 lines += ['import Projects.thermostat.'+n+'Quiet' for n in sorted(module_deps.get(mod,set()))]
 if mod=='ApplyCall':lines.append('import Projects.thermostat.ApplyCallSetupQuiet')
 lines += options[mod]
 lines += re.findall(r'^open .+$',mods[mod],re.M)
 for full in ordered:
  d=decls[full];t=d['text'];repls={}
  t=re.sub(r'\bend\s+'+re.escape(d['namespace'])+r'\s*$', '', t).rstrip()+'\n'
  while t.rstrip().endswith('-/'):
   cut=t.rfind('/--')
   if cut<0:break
   tail=t[cut:]
   if tail.count('/-')!=1 or tail.count('-/')!=1:break
   t=t[:cut].rstrip()+'\n'
  t,protected=protect(t);bound=bound_names(t);bare_rank={}
  for other in chosen:
   c=decls[other];new=special.get(other,other+'_quiet')
   for alias in[other,other.removeprefix('E5R.Thermostat.')]:repls[alias]=new
   rank=10000 if c['namespace']==d['namespace']else (opened_by_mod[mod].index(c['namespace'])if c['namespace']in opened_by_mod[mod]else -1)
   if rank>=0 and c['name']not in bound and c['name']not in {'none','some'} and rank>bare_rank.get(c['name'],-1):
    repls[c['name']]=new;bare_rank[c['name']]=rank
  # A single alternation prevents rewritten names being rewritten a second time.
  pattern=r'(?<![A-Za-z0-9_.])('+ '|'.join(re.escape(k)for k in sorted(repls,key=len,reverse=True))+r')(?![A-Za-z0-9_\'])'
  body_start=re.search(r':=\s*by\b',t)
  assert body_start,(full,'missing proof body')
  cut=body_start.start()
  body=t[cut:]
  def replace_reference(match):
   before=body[:match.start()].rsplit('\n',1)[-1]
   if re.search(r'(?:^\s*\||\bcase)\s*$',before):return match[1]
   return repls[match[1]]
  t=t[:cut]+re.sub(pattern,replace_reference,body)
  # The declaration name must stay relative to its namespace.
  t=re.sub(r'^theorem [^ (\n]+','theorem '+d['name']+'_quiet',t,count=1)
  t=t.replace('DetSteps','Quiet.Steps').replace('DetStep','Quiet.Step').replace('detStep_of','QuietDet.step_of')
  if mod=='Proof':t=t.replace('QuietDet.step_of','Quiet.step_of')
  if mod=='ApplyCall':t=t.replace('apply E5R.Thermostat.run_sound_quiet', 'apply E5R.Thermostat.run_sound_quiet (image := img) (B := B) (n := 5) (c := c) (d := setup c)')
  t=re.sub(r'\.det\b','.det_quiet',t)
  t=restore(t,protected)
  if full=='E5R.Thermostat.ParamReturn.none':t=t.replace('Result d none','Result d Option.none')
  if mod in {'EqualLiteral','Literal'}:t=t.replace('QuietDet.step_of','QuietDet.step_of (good := by simpa only [QuietDet.Good,bne_iff_ne] using site.rd_nonzero)',1)
  if full=='E5R.Thermostat.ApplyCall.setup_contract':
   cut=re.search(r':=\s*by\b',t).start()
   t=t[:cut]+':= by\n  exact ApplyCallSetupQuiet.contract B c ram hp\n'
  def header(text):
   end=re.search(r':=\s*by\b',text);assert end,(full,'no proof body');return text[:end.start()]
  original=header(d['text']);converted=header(t).replace('Quiet.Steps','DetSteps').replace('Quiet.Step','DetStep')
  if full=='E5R.Thermostat.ParamReturn.none':converted=converted.replace('Result d Option.none','Result d none')
  def normalize(text):
   text=re.sub(r'^theorem [^ (\n]+','theorem EXPECTED',text,count=1)
   text=re.sub(r'/-.*?-/', '',text,flags=re.S);text=re.sub(r'--[^\n]*','',text)
   return re.sub(r'\s+','',text)
  assert normalize(original)==normalize(converted),(full,'statement drift')
  bindings.append({'original':full,'stronger':full+'_quiet','normalized_original_statement_sha256':hashlib.sha256(normalize(original).encode()).hexdigest()})
  lines += ['namespace '+d['namespace'],t,'end '+d['namespace']]
 rendered[mod+'Quiet']='\n'.join(lines)+'\n'
assert len(bindings)==len(chosen-set(special)),('missing statement checks',len(bindings),len(chosen))
if args.check:
 for name,expected in rendered.items():
  path=args.proof_dir/(name+'.lean');assert path.read_text()==expected,('generated proof differs',path)
 print('PASS',len(rendered),'companions;',len(bindings),'preserved original signatures')
else:
 args.emit.mkdir(parents=True,exist_ok=True)
 assert not(args.emit/'statement-binding.json').exists(),('refuse overwrite',args.emit/'statement-binding.json')
 for name,source in rendered.items():
  path=args.emit/(name+'.lean');assert not path.exists(),('refuse overwrite',path)
 for name,source in rendered.items():(args.emit/(name+'.lean')).write_text(source)
 (args.emit/'statement-binding.json').write_text(json.dumps(bindings,indent=2)+'\n')
 print('Emitted',len(rendered),'companions;',len(bindings),'preserved original signatures')
