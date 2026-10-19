"""Restricted reader for TG 6.11's sequential pickle records; never imports user classes."""
import io, pickle
import numpy as np
class TGReader(pickle.Unpickler):
 def find_class(self,module,name):
  allowed={('numpy','ndarray'):np.ndarray,('numpy','dtype'):np.dtype,('numpy.core.multiarray','_reconstruct'):np._core.multiarray._reconstruct,('numpy.core.multiarray','scalar'):np._core.multiarray.scalar,('numpy._core.multiarray','_reconstruct'):np._core.multiarray._reconstruct,('numpy._core.multiarray','scalar'):np._core.multiarray.scalar}
  if (module,name) in allowed:return allowed[module,name]
  raise ValueError('This history file contains an unsupported object type.')
def read_history(raw):
 stream=io.BytesIO(raw);out=[]
 while stream.tell()<len(raw):
  try:r=TGReader(stream).load()
  except (pickle.UnpicklingError,EOFError,TypeError,AttributeError) as e:raise ValueError('Cannot read this TG history file.') from e
  if not isinstance(r,(list,tuple)) or len(r)!=8:raise ValueError('Expected a TG 6.11 history record.')
  results=[]
  for i,name in enumerate(r[3]):
   v,e,r2=float(r[4][i]),float(r[5][i]),float(r[6][i])
   if all(np.isfinite(x) for x in (v,e,r2)) and v!=999:results.append({'name':str(name),'value':v,'stderr':abs(e),'r2':r2,'error':None})
  out.append({'telescope':str(r[0]),'jd':str(r[1]),'date':str(r[2]),'field':str(r[7]),'results':results,'stars':[],'excluded':{}})
  if len(out)>10000:raise ValueError('Too many history records.')
 return out
