"""Scientific core ported from TG 6.11; no GUI or mutable global state."""
import csv, io, json, math, re
from pathlib import Path
import numpy as np
from scipy.stats import linregress
BANDS='UBVRI'
ALIASES=json.loads(Path(__file__).with_name('aliases.json').read_text())
SPECS=[('Tub','U-B','u-b',True),('Tbv','B-V','b-v',True),('Tbr','B-R','b-r',True),('Tbi','B-I','b-i',True),('Tvr','V-R','v-r',True),('Tri','R-I','r-i',True),('Tu_ub','U-B','U-u',False),('Tb_ub','U-B','B-b',False),('Tb_bv','B-V','B-b',False),('Tb_br','B-R','B-b',False),('Tb_bi','B-I','B-b',False),('Tv_bv','B-V','V-v',False),('Tv_vr','V-R','V-v',False),('Tr_vr','V-R','R-r',False),('Tr_ri','R-I','R-r',False),('Ti_ri','R-I','I-i',False),('Tvi','V-I','v-i',True),('Tv_vi','V-I','V-v',False),('Ti_vi','V-I','I-i',False),('Tr_vi','V-I','R-r',False)]
def number(v):
 try:
  n=float(str(v).replace(' ',''));return n if math.isfinite(n) and n>-999 else None
 except (ValueError,TypeError): return None

def parse_coord(v,is_ra=False):
 if v is None:return None
 try:return float(v)
 except (ValueError,TypeError):pass
 try:
  p=str(v).strip().split(':')
  if len(p)==3:
   sign=-1 if p[0].startswith('-') else 1
   val=sign*(abs(float(p[0]))+float(p[1])/60+float(p[2])/3600)
   return val*15 if is_ra else val
 except (ValueError,TypeError):pass
 return None

def references(text):
 if text.lstrip().startswith(('{','[')):
  data=json.loads(text); data=data.get('photometry',data.get('stars',[])) if isinstance(data,dict) else data
  out=[]
  for s in data:
   row={'id':str(s.get('auid',s.get('id',''))),'label':str(s.get('label','')),'ra':parse_coord(s.get('ra'),is_ra=True),'dec':parse_coord(s.get('dec'))}
   for b in BANDS:row[b]=number(s.get(b))
   for b in s.get('bands',[]):
    band=b['band'].replace('Rc','R').replace('Ic','I')
    if band in BANDS:row[band]=number(b.get('mag'))
   if row['id']:out.append(row)
 else:
  out=[]
  for s in csv.DictReader(io.StringIO(text.lstrip('\ufeff'))):
   s={k.strip():v for k,v in s.items() if k};row={'id':str(s.get('id',s.get('auid',''))),'label':s.get('label',''),'ra':parse_coord(s.get('ra'),is_ra=True),'dec':parse_coord(s.get('dec'))}
   row.update({b:number(s.get(b)) for b in BANDS})
   if row['id']:out.append(row)
 if len(out)<3:raise ValueError('Reference catalog must contain at least three identified stars.')
 return out

def parse_measurements(files,fmt,refs,field='',snr=20):
 lookup={s['id']:s for s in refs}; aliases=ALIASES.get(field,{})
 observations={}; warnings=set(); jd=''
 def add(sid,b,val):
  sid=aliases.get(sid,sid); val=number(val)
  if sid not in lookup: warnings.add('Unmatched star: '+sid); return
  if val is not None and val!=0: observations.setdefault(sid,{}).setdefault(b,[]).append(val)
 for filename,text in files:
  lines=text.lstrip('\ufeff').splitlines()
  if fmt=='CSV':
   rows=list(csv.DictReader(io.StringIO(text.lstrip('\ufeff'))))
   if not rows or 'id' not in rows[0]:raise ValueError('Measurement CSV requires id and lowercase u,b,v,r,i columns.')
   for r in rows:
    for b in BANDS:add(r['id'].strip(),b.lower(),r.get(b.lower()))
    jd=r.get('jd',jd)
  elif fmt in ('TG','AIP4WIN'):
   cols=None
   for line in lines:
    if line.strip().startswith('#') or not line.strip():continue
    r=[x.strip() for x in re.split('[;,\t]',line)]
    if r[0].lower()=='filt':cols=[x.lower().replace('tb','b').replace('tv','v').replace('tr','r') for x in r];continue
    if r[0].lower()=='jd':jd=next((x for x in r[1:] if number(x) is not None),jd);continue
    if cols:
     for i,b in enumerate(cols):
      if b in 'ubvri' and i<len(r):add(r[0],b,r[i])
   if cols is None:raise ValueError(filename+': missing Filt header.')
  elif fmt=='MaxIm':
   rows=list(csv.reader(lines,delimiter=';' if lines and lines[0].count(';')>lines[0].count(',') else ','))
   if not rows or [x.strip() for x in rows[0][:2]]!=['Timestamp (JD)','Filter']:raise ValueError('MaxIm header must begin Timestamp (JD), Filter.')
   cols=[(i,v.strip()[:-33].strip()) for i,v in enumerate(rows[0]) if v.strip().endswith(': Instrument Magnitude (Centroid)')]
   if not cols:raise ValueError('No MaxIm Instrument Magnitude (Centroid) columns found.')
   for r in rows[1:]:
    if len(r)<2:continue
    b=r[1].strip().lower();jd=r[0]
    if b not in 'ubvri' or len(b)!=1:continue
    for i,sid in cols:
     if i<len(r):add(sid,b,r[i])
  elif fmt=='VPhot':
   filt=None;header=None
   for line in lines:
    if line.startswith('Filter:'):filt=line.split(':',1)[1].strip().lower();continue
    if line.startswith('JD:'):jd=line.split(':',1)[1].strip();continue
    r=[x.strip().strip('"') for x in re.split('[\t;]',line)]
    if r and r[0]=='Star':header=['Ref-mag' if x.endswith('-mag') else x for x in r];continue
    if header and len(r)>=len(header) and filt in list('ubvri'):
     d=dict(zip(header,r));sid=d.get('AUID',d.get('Star',''))
     if sid not in lookup:
      candidates=[s for s in refs if str(s.get('label'))==d.get('Label')]
      if len(candidates)>1:
       candidates=[s for s in candidates if s.get(filt.upper()) is not None and s.get('B') is not None and s.get('V') is not None and number(d.get('Ref-mag')) is not None and number(d.get('B-V')) is not None and abs(s[filt.upper()]-number(d['Ref-mag']))<.001 and abs(s['B']-s['V']-number(d['B-V']))<.001]
      if len(candidates)==1:sid=candidates[0]['id']
     if d.get('Active','').lower()=='true' and (number(d.get('SNR')) or 0)>snr:add(sid,filt,d.get('IM'))
   if not header:raise ValueError(filename+': missing VPhot tab-separated Star header.')
  else:raise ValueError('Unknown input format.')
 rows=[]
 for sid,m in observations.items():
  row={'id':sid,'standard':lookup[sid],'instrument':{b:float(np.mean(v)) for b,v in m.items()},'counts':{b:len(v) for b,v in m.items()}};rows.append(row)
 if len(rows)<3:raise ValueError('Fewer than three matched stars with valid measurements. Check the catalog, IDs, format, and SNR threshold.')
 return {'stars':rows,'warnings':sorted(warnings),'jd':jd}

def calculate(stars,excluded=None):
 excluded=excluded or {};results=[]
 for name,xlabel,ylabel,inverse in SPECS:
  points=[]
  def val(s,b):return s['standard'].get(b) if b.isupper() else s['instrument'].get(b)
  for s in stars:
   values=[val(s,b) for b in (xlabel[0],xlabel[2],ylabel[0],ylabel[2])]
   if any(v is None for v in values):continue
   points.append({'id':s['id'],'x':values[0]-values[1],'y':values[2]-values[3],'used':s['id'] not in excluded.get(name,[])})
  if not points:continue
  r={'name':name,'x_label':xlabel,'y_label':ylabel,'inverse':inverse,'points':points,'n':sum(p['used'] for p in points),'error':None}
  used=[p for p in points if p['used']]
  if len(used)<3:r['error']='At least 3 included stars are required.'
  elif np.ptp([p['x'] for p in used])<1e-12:r['error']='Standard colors have no spread.'
  else:
   x=np.array([p['x'] for p in used]);y=np.array([p['y'] for p in used]);fit=linregress(x,y)
   # Preserve TG 6.11 reciprocal-error convention for reproducibility.
   if inverse and (abs(fit.slope)<1e-12 or abs(fit.slope-fit.stderr)<1e-12):r['error']='Reciprocal coefficient is singular.'
   else:
    r.update(value=float(1/fit.slope if inverse else fit.slope),stderr=float(abs(fit.stderr/(fit.slope*(fit.slope-fit.stderr))) if inverse else fit.stderr),r2=float(fit.rvalue**2),slope=float(fit.slope),intercept=float(fit.intercept),sigma=float(np.sqrt(np.sum((y-fit.intercept-fit.slope*x)**2)/(len(x)-2))))
  results.append(r)
 return results

def average(sets):
 if not sets:raise ValueError('Select at least one saved set.')
 if len({s['telescope'] for s in sets})>1:raise ValueError('Select sets from the same telescope.')
 out=[]
 for name,*_ in SPECS:
  rr=[r for s in sets for r in s['results'] if r['name']==name and not r.get('error')]
  if rr:
   v=np.array([r['value'] for r in rr]);e=np.array([r['stderr'] for r in rr]);out.append({'name':name,'value':float(np.mean(v)),'stderr':float(np.sqrt(np.mean(e**2)+np.std(v)**2)),'r2':float(np.mean([r['r2'] for r in rr])),'n':len(rr),'error':None})
 return out
