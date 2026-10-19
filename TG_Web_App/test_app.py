import io,json,pickle
import numpy as np
from engine import calculate,average,parse_measurements,references,SPECS
from app import app
from legacy import read_history

def sample():
 return [{'id':str(i),'standard':{'id':str(i),'B':12+i*.3,'V':12+i*.1,'U':13+i*.4,'R':11.8+i*.05,'I':11.5},'instrument':{'b':10+i*.4,'v':10+i*.1,'u':11+i*.5,'r':9.8+i*.05,'i':9.5}} for i in range(6)]
def test_equations():
 stars=sample();rs=calculate(stars);assert len(rs)==20
 r=next(r for r in rs if r['name']=='Tbv');assert abs(r['value']-2/3)<1e-12
 r=next(r for r in rs if r['name']=='Tv_bv');assert abs(r['value'])<1e-12
 for name,x,y,inverse in SPECS:
  result=next(r for r in rs if r['name']==name);assert result['n']==6
  a=[];b=[]
  for s in stars:
   get=lambda k:s['standard'][k] if k.isupper() else s['instrument'][k]
   a.append(get(x[0])-get(x[2]));b.append(get(y[0])-get(y[2]))
  slope=np.polyfit(a,b,1)[0];assert abs(result['value']-(1/slope if inverse else slope))<1e-10

def test_refit_and_error():
 stars=sample();stars[-1]['instrument']['b']+=.5
 rs=calculate(stars);r=next(r for r in rs if r['name']=='Tbv')
 from scipy.stats import linregress
 f=linregress([p['x'] for p in r['points']],[p['y'] for p in r['points']]);assert abs(r['stderr']-abs(f.stderr/(f.slope*(f.slope-f.stderr))))<1e-12
 r=next(r for r in calculate(stars,{'Tbv':['5']}) if r['name']=='Tbv');assert r['n']==5 and abs(r['value']-2/3)<1e-12
 assert next(r for r in calculate(stars,{'Tbv':['0','1','2','3']}) if r['name']=='Tbv')['error']

def test_importers():
 refs=[s['standard'] for s in sample()]
 data='id,b,v\n'+''.join(f'{i},{10+i*.4},{10+i*.1}\n' for i in range(6))
 assert len(parse_measurements([('x.csv',data)],'CSV',refs)['stars'])==6
 tg='Filt;b;v\nJD;2460000\n'+''.join(f'{i};{10+i*.4};{10+i*.1}\n' for i in range(6))
 assert parse_measurements([('x.txt',tg)],'TG',refs)['jd']=='2460000'
 header='Timestamp (JD),Filter,'+','.join(f'{i}: Instrument Magnitude (Centroid)' for i in range(6))+'\n'
 maxim=header+'2460000,B,'+','.join(str(10+i*.4) for i in range(6))+'\n2460000,V,'+','.join(str(10+i*.1) for i in range(6))
 assert len(parse_measurements([('x.csv',maxim)],'MaxIm',refs)['stars'])==6
 for s in refs:s['label']=s['id']
 vp='Filter: V\nJD: 2460000\nStar\tLabel\tActive\tSNR\tIM\tV-mag\tB-V\n'+''.join(f'{i}\t{i}\tTrue\t50\t{10+i*.1}\t12\t0\n' for i in range(6))
 assert len(parse_measurements([('v.txt',vp)],'VPhot',refs)['stars'])==6
 assert len(references(json.dumps(refs)))==6

def test_average():
 rows=[{'name':'Tbv','value':v,'stderr':.1,'r2':.9} for v in [1.,1.2]]
 result=average([{'telescope':'T','results':[r]} for r in rows])[0]
 assert abs(result['value']-1.1)<1e-12;assert abs(result['stderr']-np.sqrt(.02))<1e-12

def test_api_and_history():
 c=app.test_client();assert c.get('/').status_code==200
 rs=c.post('/api/calculate',json={'stars':sample()}).get_json()['results'];assert len(rs)==20
 for fmt in ['csv','ini']:
  r=c.post('/api/export',json={'results':rs,'format':fmt});assert r.status_code==200 and b'Tbv' in r.data
 raw=pickle.dumps(['Scope','2460000','20260101000000',['Tbv'],np.array([1.1]),np.array([.02]),np.array([.99]),'M67'])
 assert read_history(raw)[0]['results'][0]['value']==1.1
 r=c.post('/api/history',data={'history':(io.BytesIO(raw),'test.ptgp')});assert r.status_code==200
 import os
 try:read_history(pickle.dumps(os.system))
 except ValueError:pass
 else:raise AssertionError('Unsafe pickle global accepted')
 r=c.post('/api/import',data={'format':'CSV','catalog':(io.BytesIO(json.dumps([s['standard'] for s in sample()]).encode()),'c.json'),'measurements':(io.BytesIO(b'id,b,v\n0,10,10\n1,10.4,10.1\n2,10.8,10.2'),'m.csv')})
 assert r.status_code==200 and len(r.get_json()['stars'])==3
 assert c.post('/api/average',json={'sets':[]}).status_code==400
