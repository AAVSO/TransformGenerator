import csv, io, json, os
from datetime import datetime, timezone
import requests
from flask import Flask, render_template, request, jsonify, Response
from engine import references, parse_measurements, calculate, average
app=Flask(__name__)
app.config['MAX_CONTENT_LENGTH']=20*1024*1024
@app.errorhandler(413)
def too_large(e):return jsonify(error='Upload exceeds the 20 MB request limit.'),413
@app.errorhandler(ValueError)
def invalid(e):return jsonify(error=str(e)),400
@app.get('/')
def index():return render_template('index.html')
@app.post('/api/catalog')
def catalog():
 d=request.get_json();field=d.get('field','M67'); params={'format':'json','fov':179,'maglimit':16.5,'special':'std_field'}
 if field=='Coordinates':params.update(ra=d['ra'],dec=d['dec'])
 else:params['star']=field
 try:
  r=requests.get('https://app.aavso.org/vsp/api/chart/',params=params,timeout=35);r.raise_for_status();text=r.text;stars=references(text)
 except (requests.RequestException,ValueError) as e:raise ValueError('AAVSO catalog could not be loaded. Try again or upload a VSP JSON / reference CSV catalog.') from e
 return jsonify(stars=stars,source=r.url)
@app.post('/api/history')
def history():
 from legacy import read_history
 if 'history' not in request.files:raise ValueError('Choose a TG history file.')
 return jsonify(sets=read_history(request.files['history'].read()))
@app.post('/api/import')
def import_data():
 if 'catalog' not in request.files:raise ValueError('Load or upload a reference catalog first.')
 refs=references(request.files['catalog'].read().decode('utf-8-sig'))
 files=[(f.filename,f.read().decode('utf-8-sig',errors='replace')) for f in request.files.getlist('measurements')]
 if not files:raise ValueError('Choose at least one measurement file.')
 if request.form.get('format')=='MaxIm' and len(files)!=1:raise ValueError('MaxIm import accepts one file per set.')
 data=parse_measurements(files,request.form.get('format','CSV'),refs,request.form.get('field',''),float(request.form.get('snr',20)))
 data['results']=calculate(data['stars']);return jsonify(data)
@app.post('/api/calculate')
def recalculate():
 d=request.get_json();return jsonify(results=calculate(d['stars'],d.get('excluded',{})))
@app.post('/api/average')
def average_sets():return jsonify(results=average(request.get_json()['sets']))
@app.post('/api/export')
def export():
 d=request.get_json();rows=[r for r in d['results'] if not r.get('error')];fmt=d.get('format','csv');tel=str(d.get('telescope','')).replace('\n',' ').replace('\r',' ')
 if fmt=='ini':
  text='[Setup]\ndescription=TG Web, Telescope= '+tel+', Time created (UT) = '+datetime.now(timezone.utc).isoformat()+'\n'
  for section,key in [('Coefficients','value'),('Error','stderr'),('R Squared Values','r2')]:
   text+='['+section+']\n'+''.join(f"{r['name']}= {r[key]:.6f}\n" for r in rows)
  return Response(text,mimetype='text/plain',headers={'Content-Disposition':'attachment; filename=transforms.ini'})
 out=io.StringIO();w=csv.writer(out);w.writerow(['coefficient','value','error','r_squared','count']);w.writerows([r['name'],r['value'],r['stderr'],r['r2'],r.get('n','')] for r in rows)
 return Response(out.getvalue(),mimetype='text/csv',headers={'Content-Disposition':'attachment; filename=transforms.csv'})
if __name__=='__main__':app.run(host=os.environ.get('HOST','127.0.0.1'),port=int(os.environ.get('PORT',5000)),debug=False)
