import L from 'leaflet';
import 'leaflet/dist/leaflet.css';
import * as turf from '@turf/turf';
import shpwrite from 'shp-write';
import './style.css';

// GoogleMutant is a classic Leaflet plugin and expects Leaflet on window.
// Expose the same Leaflet instance used by this app before loading the plugin.
window.L=L;

const road=L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png',{maxNativeZoom:19,maxZoom:22,attribution:'© OpenStreetMap'});
const fallbackSat=L.tileLayer('https://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}',{maxNativeZoom:17,maxZoom:22,keepBuffer:4,updateWhenZooming:false,attribution:'© Esri'});
const map=L.map('map',{layers:[fallbackSat],maxZoom:22}).setView([-17.79,-50.92],13);
const layerControl=L.control.layers({'Satellite (fallback)':fallbackSat,'Road map':road},null,{collapsed:true,position:'topleft'}).addTo(map);
let googleSat=null;
let googleMutantPromise=null;
function loadGoogleMutant(){
  if(typeof L.gridLayer.googleMutant==='function')return Promise.resolve();
  if(googleMutantPromise)return googleMutantPromise;
  googleMutantPromise=new Promise((resolve,reject)=>{
    let s=document.createElement('script');
    s.id='googleMutantPlugin';
    s.src='https://unpkg.com/leaflet.gridlayer.googlemutant@0.16.0/dist/Leaflet.GoogleMutant.js';
    s.onload=()=>typeof L.gridLayer.googleMutant==='function'?resolve():reject(new Error('GoogleMutant plugin loaded but did not register with Leaflet'));
    s.onerror=()=>reject(new Error('Could not load the GoogleMutant map plugin'));
    document.head.appendChild(s);
  });
  return googleMutantPromise;
}
function loadGoogleMaps(key){return new Promise((resolve,reject)=>{if(window.google?.maps)return resolve();let old=document.getElementById('googleMapsApi');if(old)old.remove();let cb='__flbGoogleReady'+Date.now();let timer=setTimeout(()=>{delete window[cb];reject(new Error('Google Maps API timed out while loading'))},15000);window[cb]=()=>{clearTimeout(timer);delete window[cb];resolve()};let s=document.createElement('script');s.id='googleMapsApi';s.async=true;s.defer=true;s.src=`https://maps.googleapis.com/maps/api/js?key=${encodeURIComponent(key)}&callback=${cb}&loading=async`;s.onerror=()=>{clearTimeout(timer);delete window[cb];reject(new Error('Google Maps JavaScript API script was rejected or could not be downloaded'))};document.head.appendChild(s)})}
async function enableGoogleSatellite(key){try{await loadGoogleMutant();await loadGoogleMaps(key);if(!googleSat){googleSat=L.gridLayer.googleMutant({type:'satellite',maxZoom:22});layerControl.addBaseLayer(googleSat,'Google Satellite')}if(map.hasLayer(fallbackSat))map.removeLayer(fallbackSat);googleSat.addTo(map);return {ok:true}}catch(e){console.error('Google Satellite setup failed:',e);return {ok:false,error:e?.message||String(e)}}}
const savedGoogleKey=localStorage.getItem('flbGoogleMapsKey');
if(savedGoogleKey)enableGoogleSatellite(savedGoogleKey).then(r=>{if(!r.ok)console.error('Saved Google key could not enable satellite:',r.error)});

const $=s=>document.querySelector(s),drawer=$('#drawer'),home=$('#homeActions'),mapBar=$('#mapBar'),stageTitle=$('#stageTitle'),pointMenu=$('#pointMenu');
const emptyField=(name='')=>({id:Date.now()+Math.random(),name,boundary:[],sections:[],stage:'home',width:9,borderPasses:3,guidanceSets:[]});
let legacy=JSON.parse(localStorage.getItem('flb13')||'null'),DB=JSON.parse(localStorage.getItem('flbFields')||'null');
if(!DB)DB={fields:legacy&&legacy.name?[{...legacy,id:legacy.id||Date.now()}]:[],currentId:legacy&&legacy.name?(legacy.id||Date.now()):null};
let S=DB.fields.find(f=>f.id===DB.currentId)||emptyField();
let mode=null,selected=-1,first=-1,op=null,suppressNextMapTap=false,layer=L.layerGroup().addTo(map),guide=L.layerGroup().addTo(map),handle=null,polyLayer=null,dotMarkers=[],editHistory=[],guideDraft=null,guideMarkers=[],guideHandle=null,highlightLayer=null;

function save(){if(S&&S.name){let i=DB.fields.findIndex(f=>f.id===S.id);if(i>=0)DB.fields[i]=S;else DB.fields.push(S);DB.currentId=S.id}localStorage.setItem('flbFields',JSON.stringify(DB));localStorage.setItem('flb13',JSON.stringify(S))}
function open(html){removeHandle();removeGuideHandle();hidePointMenu();mapBar.classList.add('hidden');stageTitle.classList.add('hidden');drawer.innerHTML=html;drawer.classList.remove('hidden');home.classList.add('hidden')}
function close(){drawer.classList.add('hidden')}
function escapeHtml(v){return String(v).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]))}
function forwardIdx(a,b){let out=[a],i=a,n=S.boundary.length;while(i!==b){i=(i+1)%n;out.push(i);if(out.length>n+1)break}return out}
function pathMeters(arr){let d=0;for(let k=1;k<arr.length;k++)d+=turf.distance([S.boundary[arr[k-1]][1],S.boundary[arr[k-1]][0]],[S.boundary[arr[k]][1],S.boundary[arr[k]][0]],{units:'meters'});return d}
function idxs(a,b){let f=forwardIdx(a,b),r=forwardIdx(b,a).reverse();return pathMeters(f)<=pathMeters(r)?f:r}
function smoothLatLngs(points){
 // Shape-preserving Chaikin smoothing: follows the user's polyline and cannot overshoot like a spline.
 if(points.length<3)return points.map(p=>p.slice());
 let pts=points.map(p=>p.slice());
 for(let pass=0;pass<3;pass++){
  let out=[pts[0].slice()];
  for(let i=0;i<pts.length-1;i++){
   let a=pts[i],b=pts[i+1];
   out.push([a[0]*.75+b[0]*.25,a[1]*.75+b[1]*.25]);
   out.push([a[0]*.25+b[0]*.75,a[1]*.25+b[1]*.75]);
  }
  out.push(pts[pts.length-1].slice());pts=out;
 }
 return pts
}
function sectionIndices(s){
 if(Array.isArray(s.path)&&s.path.length>1)return s.path.slice();
 return idxs(s.start,s.end)
}
function sectionLatLngs(s){let pts=sectionIndices(s).map(i=>S.boundary[i]);return s.smooth?smoothLatLngs(pts):pts}
// Smoothing replaces the geometry of that border section for every downstream operation.
// The selected endpoints stay fixed, so the field remains closed; only the chosen side is rounded.
function boundaryLatLngs(){return S.boundary.map(p=>p.slice())}
function forwardSectionPath(s){
 let p=sectionIndices(s),n=S.boundary.length;if(p.length<2)return p;
 return p[1]===(p[0]+1)%n?p:p.slice().reverse()
}
function effectiveBoundaryLatLngs(){
 let n=S.boundary.length;if(n<3)return boundaryLatLngs();
 let smooth=(S.sections||[]).filter(s=>s.smooth).map(s=>({s,path:forwardSectionPath(s)})).filter(o=>o.path.length>1);
 if(!smooth.length)return boundaryLatLngs();
 let interior=new Set();smooth.forEach(o=>o.path.slice(1,-1).forEach(i=>interior.add(i)));
 let start=0;while(start<n&&interior.has(start))start++;if(start>=n)start=0;
 let byStart=new Map();smooth.forEach(o=>byStart.set(o.path[0],o));
 let out=[],i=start,edges=0,guard=0;
 while(edges<n&&guard++<n*4){
  let o=byStart.get(i);
  if(o){let pts=o.path.map(j=>S.boundary[j]),sm=smoothLatLngs(pts);out.push(...sm.slice(0,-1).map(p=>p.slice()));edges+=o.path.length-1;i=o.path[o.path.length-1];continue}
  out.push(S.boundary[i].slice());i=(i+1)%n;edges++
 }
 return out.length>=3?out:boundaryLatLngs()
}
function ring(useEffective=true){let src=useEffective?effectiveBoundaryLatLngs():boundaryLatLngs(),r=src.map(([a,b])=>[b,a]);if(r.length)r.push(r[0]);return r}
function poly(useEffective=true){let r=ring(useEffective);return r.length>3?turf.polygon([r]):null}
function area(){let p=poly(true);return p?turf.area(p)/10000:0}

function redraw(){
 layer.clearLayers();guide.clearLayers();dotMarkers=[];guideMarkers=[];polyLayer=null;if(highlightLayer){map.removeLayer(highlightLayer);highlightLayer=null}
 if(S.boundary.length){polyLayer=L.polygon(effectiveBoundaryLatLngs(),{color:'#1683ff',weight:3,fillOpacity:.07,interactive:false}).addTo(layer);
  if(['draw','locked','edit'].includes(S.stage))S.boundary.forEach((p,i)=>{let m=L.circleMarker(p,{radius:i===first?8:6,color:i===first?'#f0a000':'#1683ff',weight:3,fillColor:'#fff',fillOpacity:1,bubblingMouseEvents:false}).addTo(layer);dotMarkers[i]=m;m.on('click',e=>{L.DomEvent.stopPropagation(e);pointClick(i,e)})});
  S.sections.forEach(s=>L.polyline(sectionLatLngs(s),{color:'#f0a000',weight:5,opacity:.7,interactive:false}).addTo(layer));
 }
 for(const set of S.guidanceSets||[])for(const g of set.lines)L.polyline(g,{color:set.kind==='headland'?'#e18a00':'#27633f',weight:2,interactive:false}).addTo(guide);
 if(guideDraft){let pts=guideDraft.points||[];if(pts.length>1)L.polyline(guideDraft.type==='curve'?smoothLatLngs(pts):pts,{color:'#8d42c7',weight:3,dashArray:'7 5',interactive:false}).addTo(guide);pts.forEach((p,i)=>{let m=L.circleMarker(p,{radius:7,color:'#8d42c7',weight:3,fillColor:'#fff',fillOpacity:1,bubblingMouseEvents:false}).addTo(guide);guideMarkers[i]=m;m.on('click',e=>{L.DomEvent.stopPropagation(e);showGuideDragHandle(i)})})}
 $('#fieldTitle').textContent=S.name?`${S.name} • ${area().toFixed(2)} ha`:'';save()
}

$('#findMe').onclick=()=>map.locate({setView:true,maxZoom:20,enableHighAccuracy:true});
map.on('locationfound',e=>L.circleMarker(e.latlng,{radius:7,color:'#173f2a',fillOpacity:1}).addTo(layer).bindTooltip(`±${Math.round(e.accuracy)} m`).openTooltip());
map.on('locationerror',()=>alert('Allow location permission and try again.'));
$('#createNew').onclick=newField;$('#fieldsHome').onclick=showFieldsHome;
function newField(){open(`<h2>Create New Field</h2><label>Field name<input id="nm" placeholder="Field name"></label><button id="next" class="primary">Continue</button>`);$('#next').onclick=()=>{let n=$('#nm').value.trim();if(!n)return;S=emptyField(n);save();chooseMethod()}}
function chooseMethod(){open(`<h2>${escapeHtml(S.name)}</h2><p>How do you want to create the field boundary?</p><div class="row"><button id="manual" class="primary">Manual</button><button id="gps">GPS</button></div>`);$('#manual').onclick=drawScreen;$('#gps').onclick=()=>alert('GPS boundary recording is not enabled yet.')}
function setMapBar(html,title=''){drawer.classList.add('hidden');home.classList.add('hidden');stageTitle.classList.add('hidden');mapBar.innerHTML=(title?`<div class="bar-title">${escapeHtml(title)}</div>`:'')+`<div class="bar-actions">${html}</div>`;mapBar.classList.remove('hidden')}
function drawScreen(){removeHandle();hidePointMenu();S.stage='draw';mode='draw';setMapBar(`<button id="backDraw">← Back</button><button id="undo">↶ Undo</button><span id="cnt">${S.boundary.length} pts</span><button id="lock" class="primary">Save</button>`,'CREATE FIELD · Draw & Adjust Boundary');$('#backDraw').onclick=()=>S.boundary.length?showFieldsHome():chooseMethod();$('#undo').onclick=()=>{removeHandle();if(S.boundary.length)S.boundary.pop();redraw();drawScreen()};$('#lock').onclick=()=>{if(S.boundary.length<3)return alert('Add at least 3 points.');removeHandle();mode=null;S.stage='locked';sectionScreen()};redraw()}
function nearestPointAt(latlng,pixels=32){let q=map.latLngToContainerPoint(latlng),best=-1,dist=Infinity;S.boundary.forEach((p,i)=>{let d=q.distanceTo(map.latLngToContainerPoint(p));if(d<dist){dist=d;best=i}});return dist<=pixels?best:-1}
function nearestGuidePointAt(latlng,pixels=32){if(!guideDraft)return-1;let q=map.latLngToContainerPoint(latlng),best=-1,dist=Infinity;guideDraft.points.forEach((p,i)=>{let d=q.distanceTo(map.latLngToContainerPoint(p));if(d<dist){dist=d;best=i}});return dist<=pixels?best:-1}
map.on('click',e=>{if(suppressNextMapTap){suppressNextMapTap=false;return}hidePointMenu();if(handle){removeHandle();redraw();return}if(guideHandle){removeGuideHandle();redraw();return}
 if(S.stage==='draw'&&mode==='draw'){let near=nearestPointAt(e.latlng);if(near>=0){showDragHandle(near);return}S.boundary.push([e.latlng.lat,e.latlng.lng]);redraw();let c=$('#cnt');if(c)c.textContent=`${S.boundary.length} pts`;return}
 if(mode==='guide-draw'&&guideDraft){let near=nearestGuidePointAt(e.latlng);if(near>=0){showGuideDragHandle(near);return}if(guideDraft.type==='ab'&&guideDraft.points.length>=2)return;guideDraft.points.push([e.latlng.lat,e.latlng.lng]);redraw();updateGuideBar()}
});
function pointClick(i,e){if(S.stage==='draw'){showDragHandle(i);return}if(S.stage!=='locked')return;if(op&&first>=0){if(first===i){cancelSectionChoice();return}applySection(first,i);return}first=i;showPointMenu(i,e)}
function dragIcon(color='#173f2a'){return L.divIcon({className:'drag-handle-wrap',html:`<div class="drag-stem" style="background:${color}"></div><div class="drag-handle" style="background:${color}">↔<br>↕</div>`,iconSize:[76,76],iconAnchor:[12,12]})}
function showDragHandle(i){removeHandle();selected=i;handle=L.marker(S.boundary[i],{icon:dragIcon(),draggable:true,zIndexOffset:1000,autoPan:false}).addTo(map);handle.on('dragstart',()=>{suppressNextMapTap=true;map.dragging.disable()});handle.on('drag',ev=>{let q=ev.target.getLatLng();S.boundary[i]=[q.lat,q.lng];if(polyLayer)polyLayer.setLatLngs(boundaryLatLngs())});handle.on('dragend',()=>{if(!map.dragging.enabled())map.dragging.enable();save();removeHandle();redraw();setTimeout(()=>suppressNextMapTap=false,120)})}
function removeHandle(){if(handle){map.removeLayer(handle);handle=null}selected=-1}
function showGuideDragHandle(i){removeGuideHandle();guideHandle=L.marker(guideDraft.points[i],{icon:dragIcon('#8d42c7'),draggable:true,zIndexOffset:1100,autoPan:false}).addTo(map);guideHandle.on('dragstart',()=>{suppressNextMapTap=true;map.dragging.disable()});guideHandle.on('drag',ev=>{let q=ev.target.getLatLng();guideDraft.points[i]=[q.lat,q.lng]});guideHandle.on('dragend',()=>{if(!map.dragging.enabled())map.dragging.enable();removeGuideHandle();redraw();setTimeout(()=>suppressNextMapTap=false,120)})}
function removeGuideHandle(){if(guideHandle){map.removeLayer(guideHandle);guideHandle=null}}
function showPointMenu(i){removeHandle();first=i;redraw();let pt=map.latLngToContainerPoint(S.boundary[i]);pointMenu.style.left=Math.max(8,Math.min(window.innerWidth-220,pt.x+16))+'px';pointMenu.style.top=Math.max(82,Math.min(window.innerHeight-170,pt.y-18))+'px';pointMenu.classList.remove('hidden')}
function hidePointMenu(){pointMenu.classList.add('hidden')}
pointMenu.querySelectorAll('[data-op]').forEach(b=>b.onclick=e=>{e.stopPropagation();op=b.dataset.op;hidePointMenu();redraw()});
function cancelSectionChoice(){first=-1;op=null;hidePointMenu();redraw()}
function sectionScreen(){removeHandle();hidePointMenu();S.stage='locked';mode=null;setMapBar(`<button id="backPoints">← Back</button><button id="undoEdit">↶ Undo</button><button id="saveField" class="primary">Save</button>`,'EDIT FIELD · Name & Smooth Borders');$('#backPoints').onclick=()=>{first=-1;op=null;drawScreen()};$('#undoEdit').onclick=undoEdit;$('#saveField').onclick=()=>{S.stage='saved';first=-1;op=null;hidePointMenu();mapBar.classList.add('hidden');redraw();editFieldScreen()};redraw()}
function snapshotEdit(){editHistory.push({boundary:S.boundary.map(p=>p.slice()),sections:S.sections.map(s=>({...s}))});if(editHistory.length>30)editHistory.shift()}
function undoEdit(){let h=editHistory.pop();if(!h)return;S.boundary=h.boundary;S.sections=h.sections;first=-1;op=null;redraw();sectionScreen()}
function samePath(a,b){let A=sectionIndices(a),B=b;return A.length===B.length&&A.every((v,i)=>v===B[i])}
function applySection(a,b){if(!op)return;let path=idxs(a,b);snapshotEdit();if(op==='name'){let n=prompt('Border name');if(!n){editHistory.pop();cancelSectionChoice();return}let old=S.sections.find(s=>samePath(s,path));if(old){old.name=n;old.path=path.slice()}else S.sections.push({start:path[0],end:path[path.length-1],path:path.slice(),name:n,smooth:false})}else if(op==='straight'){let p0=S.boundary[path[0]],p1=S.boundary[path[path.length-1]],n=path.length-1;for(let k=1;k<n;k++){let t=k/n;S.boundary[path[k]]=[p0[0]+(p1[0]-p0[0])*t,p0[1]+(p1[1]-p0[1])*t]}}else if(op==='smooth'){let sec=S.sections.find(x=>samePath(x,path));if(!sec){sec={start:path[0],end:path[path.length-1],path:path.slice(),name:'',smooth:true};S.sections.push(sec)}sec.path=path.slice();sec.smooth=true}first=-1;op=null;redraw();sectionScreen()}

function viewFieldScreen(){S.stage='saved';close();mapBar.classList.remove('hidden');setMapBar(`<button id="allFields">← Fields</button><button id="editField" class="primary">Edit</button>`,'View Field');$('#allFields').onclick=showFieldsHome;$('#editField').onclick=editFieldScreen;redraw()}
function editFieldScreen(){S.stage='saved';open(`<h3>${escapeHtml(S.name)}</h3><div class="status">${area().toFixed(2)} ha • ${S.sections.filter(x=>x.name).length} named borders</div><div class="field-actions"><button id="guidance" class="primary">Guidance</button><button id="editGuidance">Edit Guidance</button><button id="headlands">Border Passes</button><button id="borders">Borders</button><button id="more">More ···</button></div>`);$('#guidance').onclick=guidanceMenu;$('#editGuidance').onclick=editGuidanceMenu;$('#headlands').onclick=borderPassMenu;$('#borders').onclick=bordersMenu;$('#more').onclick=moreMenu;redraw()}
function bordersMenu(){let named=S.sections.map((s,i)=>({s,i})).filter(o=>o.s.name);open(`<h3>Saved Borders</h3><p>Tap a border to highlight it. This list stays open so you can compare borders.</p><div class="section-list">${named.length?named.map(o=>`<button data-hi="${o.i}">${escapeHtml(o.s.name)}</button>`).join(''):'<div class="status">No named borders yet.</div>'}</div><button id="back">Back</button>`);document.querySelectorAll('[data-hi]').forEach(b=>b.onclick=()=>{if(highlightLayer)map.removeLayer(highlightLayer);let s=S.sections[+b.dataset.hi];highlightLayer=L.polyline(sectionLatLngs(s),{color:'#ff2d55',weight:8,opacity:.85,interactive:false}).addTo(map);document.querySelectorAll('[data-hi]').forEach(x=>x.classList.remove('selected'));b.classList.add('selected')});$('#back').onclick=editFieldScreen}
function borderPassMenu(){open(`<h3>Border Passes</h3><p>Create the passes planted around the outside of the field.</p><label>Implement width (m)<input id="w" type="number" step="0.01" value="${S.width||9}"></label><label>Number of border passes<input id="bp" type="number" min="0" step="1" value="${S.borderPasses??3}"></label><button id="make" class="primary">Create / Update Border Passes</button><button id="back">Back</button>`);$('#make').onclick=()=>{S.width=+$('#w').value||9;S.borderPasses=Math.max(0,+$('#bp').value||0);makeHeadlands();save();editFieldScreen()};$('#back').onclick=editFieldScreen}
function moreMenu(){open(`<h3>Field Options</h3><div class="field-actions"><button id="export">Export</button><button id="editSections">Edit Boundaries</button><button id="saveAndHome" class="primary">Save Field</button><button id="mapSetup">Google Map Setup</button></div><button id="back">Back</button>`);$('#export').onclick=exportScreen;$('#editSections').onclick=()=>{S.stage='locked';sectionScreen()};$('#saveAndHome').onclick=()=>{save();showFieldsHome()};$('#mapSetup').onclick=googleMapSetup;$('#back').onclick=editFieldScreen}
function googleMapSetup(){let has=!!localStorage.getItem('flbGoogleMapsKey');open(`<h3>Google Satellite Map</h3><p>${has?'Google Maps is configured on this device. You can replace the key below if needed.':'Paste your restricted Google Maps API key here once. It stays in this browser and is not stored in your field export.'}</p><label>Google Maps API key<input id="gkey" type="password" autocomplete="off" placeholder="${has?'Enter a new key to replace it':'Paste API key'}"></label><button id="useGoogle" class="primary">${has?'Keep / Update Google Satellite':'Enable Google Satellite'}</button>${has?'<button id="forgetGoogle">Remove saved key</button>':''}<button id="back">Back</button>`);$('#useGoogle').onclick=async()=>{let key=$('#gkey').value.trim()||localStorage.getItem('flbGoogleMapsKey');if(!key)return alert('Paste your Google Maps API key first.');let result=await enableGoogleSatellite(key);if(!result.ok)return alert('Google Satellite could not load.\n\n'+result.error);localStorage.setItem('flbGoogleMapsKey',key);alert('Google Satellite is enabled.');editFieldScreen()};if($('#forgetGoogle'))$('#forgetGoogle').onclick=()=>{localStorage.removeItem('flbGoogleMapsKey');location.reload()};$('#back').onclick=editFieldScreen}
function makeHeadlands(){S.guidanceSets=(S.guidanceSets||[]).filter(x=>x.kind!=='headland');let p=poly(true),lines=[];for(let i=0;i<S.borderPasses;i++){let d=-(i+.5)*S.width/1000,b=turf.buffer(p,d,{units:'kilometers'});if(!b)break;let coords=b.geometry.type==='Polygon'?b.geometry.coordinates[0]:b.geometry.coordinates[0][0];lines.push(coords.map(([x,y])=>[y,x]))}S.guidanceSets.push({name:'Border passes',kind:'headland',lines});redraw()}

function mainSets(){return(S.guidanceSets||[]).filter(x=>x.kind==='main')}
function editGuidanceMenu(){let sets=(S.guidanceSets||[]).map((x,i)=>({x,i})).filter(o=>o.x.kind==='main');if(!sets.length)return alert('There are no saved guidance lines to edit yet.');open(`<h3>Edit Guidance</h3><p>Select the guidance set you want to recreate or remove.</p><div class="section-list">${sets.map(o=>`<button data-g="${o.i}">${escapeHtml(o.x.name)} • ${o.x.lines.length} lines</button>`).join('')}</div><button id="back">Back</button>`);document.querySelectorAll('[data-g]').forEach(b=>b.onclick=()=>editGuidanceSet(+b.dataset.g));$('#back').onclick=editFieldScreen}
function editGuidanceSet(i){let set=S.guidanceSets[i];open(`<h3>${escapeHtml(set.name)}</h3><div class="status">${set.lines.length} guidance lines</div><div class="row"><button id="recreate" class="primary">Recreate / Adjust</button><button id="deleteG" class="danger">Delete</button></div><button id="back">Back</button>`);$('#deleteG').onclick=()=>{if(confirm('Delete this guidance set?')){S.guidanceSets.splice(i,1);redraw();editFieldScreen()}};$('#recreate').onclick=()=>{S.guidanceSets.splice(i,1);if(set.source==='border'&&Number.isInteger(set.borderIndex)&&S.sections[set.borderIndex]){S._border=set.borderIndex;guidanceOptions('border',false)}else if((set.source==='ab'||set.source==='curve')&&set.referencePoints){guideDraft={type:set.source,points:set.referencePoints.map(p=>p.slice()),additional:false};startGuideDraft(set.source,false)}else guidanceMenu()};$('#back').onclick=editGuidanceMenu}
function guidanceMenu(){let additional=mainSets().length>0;open(`<h3>${additional?'Create Additional Guide':'Create Guidance'}</h3><p>${additional?'Add another guidance area without replacing the existing guide.':'Choose how the main guidance reference is created.'}</p><div class="field-actions"><button id="from">Create from Border</button><button id="ab" class="primary">Draw AB</button><button id="curve">Draw Curve</button></div><button id="back">Back</button>`);$('#ab').onclick=()=>startGuideDraft('ab',additional);$('#curve').onclick=()=>startGuideDraft('curve',additional);$('#from').onclick=()=>borderList(additional);$('#back').onclick=editFieldScreen}
function borderList(additional=false){let named=S.sections.map((s,i)=>({s,i})).filter(o=>o.s.name);if(!named.length)return alert('Name at least one border section first.');open(`<h3>Create from Border</h3><p>Tap a border to highlight it, then use Select Highlighted Border.</p><div class="section-list">${named.map(o=>`<button data-i="${o.i}">${escapeHtml(o.s.name)}</button>`).join('')}</div><button id="useBorder" class="primary" disabled>Select Highlighted Border</button><button id="back">Back</button>`);let chosen=null;document.querySelectorAll('[data-i]').forEach(b=>b.onclick=()=>{chosen=+b.dataset.i;if(highlightLayer)map.removeLayer(highlightLayer);highlightLayer=L.polyline(sectionLatLngs(S.sections[chosen]),{color:'#ff2d55',weight:8,opacity:.85,interactive:false}).addTo(map);document.querySelectorAll('[data-i]').forEach(x=>x.classList.remove('selected'));b.classList.add('selected');$('#useBorder').disabled=false});$('#useBorder').onclick=()=>{if(chosen==null)return;S._border=chosen;if(highlightLayer){map.removeLayer(highlightLayer);highlightLayer=null}guidanceOptions('border',additional)};$('#back').onclick=guidanceMenu}
function startGuideDraft(type,additional=false){guideDraft=guideDraft&&guideDraft.type===type?guideDraft:{type,points:[],additional};guideDraft.additional=additional;mode='guide-draw';close();S.stage='saved';updateGuideBar();redraw()}
function updateGuideBar(){if(!guideDraft)return;let need=guideDraft.type==='ab'?2:2,ready=guideDraft.points.length>=need;setMapBar(`<button id="cancelGuide">← Back</button><button id="undoGuide">↶ Undo</button><span id="guideCount">${guideDraft.points.length} pts</span><button id="saveGuide" class="primary" ${ready?'':'disabled'}>Save</button>`,guideDraft.type==='ab'?'Place AB Points':'Place Curve Points');$('#cancelGuide').onclick=()=>{guideDraft=null;mode=null;redraw();guidanceMenu()};$('#undoGuide').onclick=()=>{removeGuideHandle();guideDraft.points.pop();redraw();updateGuideBar()};$('#saveGuide').onclick=()=>{if(!ready)return;let type=guideDraft.type,additional=guideDraft.additional;mode=null;removeGuideHandle();guidanceOptions(type,additional)}}
function guidanceOptions(source,additional=false){
 let label=source==='ab'?'A-B reference':source==='curve'?'Curved reference':'From '+S.sections[S._border].name;
 let extra=additional?`<label>Coverage<select id="coverage"><option value="remaining">Fill Remaining Space</option><option value="count">Set Left / Right Quantities</option></select></label><div id="qtyBox" class="hidden"><div class="row"><label>Left quantity<input id="leftQty" type="number" min="0" placeholder="0"></label><label>Right quantity<input id="rightQty" type="number" min="0" placeholder="0"></label></div><div class="muted">Leave a side blank for no lines on that side. The reference line itself is included when it fits.</div></div>`:`<label>Coverage<select id="coverage"><option value="fill">Fill Entire Field</option><option value="count">Set Number of Lines</option></select></label><label id="countLab" class="hidden">Number of lines<input id="gc" type="number" min="1" value="10"></label>`;
 open(`<h3>${additional?'Additional Guidance Settings':'Guidance Settings'}</h3><p>${escapeHtml(label)}</p><label>Guidance set name<input id="gn" value="${additional?'Additional rows':source==='border'?escapeHtml(S.sections[S._border].name)+' rows':'Main rows'}"></label><label>Implement width (m)<input id="gw" type="number" step="0.01" value="${S.width||9}"></label>${extra}<button id="preview" class="primary">Preview Guidance</button><button id="back">Back</button>`);
 if(additional)$('#coverage').onchange=()=>$('#qtyBox').classList.toggle('hidden',$('#coverage').value!=='count');else $('#coverage').onchange=()=>$('#countLab').classList.toggle('hidden',$('#coverage').value!=='count');
 $('#preview').onclick=()=>generateGuidance(source,additional);$('#back').onclick=()=>{if(source==='ab'||source==='curve')startGuideDraft(source,additional);else guidanceMenu()}
}
function usablePoly(){let p=poly(true);if(S.borderPasses>0){let b=turf.buffer(p,-S.borderPasses*S.width/1000,{units:'kilometers'});if(b&&b.geometry.type==='Polygon')return b}return p}
function polygonBoundaries(p){
 try{let q=turf.polygonToLine(p);return q.type==='FeatureCollection'?q.features:[q]}catch{return[]}
}
function clipLine(line,p){
 let parts=[line];
 try{for(const cutter of polygonBoundaries(p)){let next=[];for(const part of parts){let sp=turf.lineSplit(part,cutter);next.push(...(sp.features.length?sp.features:[part]))}parts=next}}
 catch(e){console.warn('clip split failed',e)}
 return parts.filter(f=>{let len=turf.length(f,{units:'meters'});if(len<.75)return false;let mid=turf.along(f,len/2,{units:'meters'});return turf.booleanPointInPolygon(mid,p)})
}
function existingMainLines(){return mainSets().flatMap(s=>s.lines)}
function existingCoverage(width){let ex=existingMainLines();if(!ex.length)return null;try{let buffs=ex.map(g=>turf.buffer(turf.lineString(g.map(([y,x])=>[x,y])),width*.995,{units:'meters'})).filter(Boolean);return buffs.length===1?buffs[0]:turf.union(turf.featureCollection(buffs))}catch(e){console.warn('coverage mask failed',e);return null}}
function splitOutsideCoverage(line,coverage){if(!coverage)return[line];let parts=[line];try{for(const cutter of polygonBoundaries(coverage)){let next=[];for(const part of parts){let sp=turf.lineSplit(part,cutter);next.push(...(sp.features.length?sp.features:[part]))}parts=next}}catch(e){console.warn('coverage split failed',e)}return parts.filter(f=>{let len=turf.length(f,{units:'meters'});if(len<.75)return false;let mid=turf.along(f,len/2,{units:'meters'});return !turf.booleanPointInPolygon(mid,coverage)})}
function baseReference(source){if(source==='border'){let sec=S.sections[S._border];return turf.lineString(sectionLatLngs(sec).map(([y,x])=>[x,y]))}let pts=guideDraft?.points||[];if(source==='curve')return turf.lineString(smoothLatLngs(pts).map(([y,x])=>[x,y]));return turf.lineString(pts.map(([y,x])=>[x,y]))}
function lineMid(f){let len=turf.length(f,{units:'meters'});return turf.along(f,len/2,{units:'meters'})}
function distanceToReference(f,base){try{return turf.pointToLineDistance(lineMid(f),base,{units:'meters'})}catch{return Infinity}}
function longestNearReference(parts,base,targetOffset,width,keepAll=false){
 let valid=parts.filter(f=>turf.length(f,{units:'meters'})>=Math.max(2,width*.35));if(!valid.length)return[];
 valid.sort((a,b)=>{let da=Math.abs(distanceToReference(a,base)-Math.abs(targetOffset)),db=Math.abs(distanceToReference(b,base)-Math.abs(targetOffset));if(Math.abs(da-db)>.5)return da-db;return turf.length(b,{units:'meters'})-turf.length(a,{units:'meters'})});
 if(!keepAll)return[valid[0]];
 // Fill wedges, but reject remote fragments created by an offset folding back across the field.
 let best=valid[0],bestD=distanceToReference(best,base);return valid.filter(f=>Math.abs(distanceToReference(f,base)-bestD)<=Math.max(width*.8,2));
}
function offsetCandidates(source,base,off,p){
 if(source==='ab'){
  let coords=base.geometry.coordinates,a=turf.point(coords[0]),b=turf.point(coords[coords.length-1]),bearing=turf.bearing(a,b),mid=turf.midpoint(a,b),box=turf.bbox(p),diag=turf.distance([box[0],box[1]],[box[2],box[3]],{units:'meters'}),c=turf.destination(mid,off,bearing+90,{units:'meters'}),x=turf.destination(c,diag*2,bearing+180,{units:'meters'}),y=turf.destination(c,diag*2,bearing,{units:'meters'});return clipLine(turf.lineString([x.geometry.coordinates,y.geometry.coordinates]),p)
 }
 let signs=source==='border'?[1,-1]:[1],best=[];
 for(const sign of signs){try{
  let ref=base;
  if(Math.abs(off)>=.001){
   // Densifying the curved reference before offsetting prevents Turf's miter joins
   // from producing long spikes at bends.
   if(source==='curve'){
    let len=turf.length(base,{units:'meters'}), coords=[];
    for(let d=0;d<len;d+=Math.max(1.5,Math.min(4,len/80)))coords.push(turf.along(base,d,{units:'meters'}).geometry.coordinates);
    coords.push(turf.along(base,len,{units:'meters'}).geometry.coordinates);
    ref=turf.lineString(coords);
   }
   ref=turf.lineOffset(ref,sign*off,{units:'meters'});
  }
  let parts=clipLine(ref,p).filter(f=>{
   // A clipped guidance fragment must actually live in/on the field. This also
   // removes the occasional lineOffset spike that lineSplit can leave behind.
   let c=f.geometry.coordinates;if(c.length<2)return false;
   let len=turf.length(f,{units:'meters'});if(len<.75)return false;
   for(let q=0;q<=4;q++){
    let pt=turf.along(f,len*q/4,{units:'meters'});
    if(!turf.booleanPointInPolygon(pt,p,{ignoreBoundary:false}))return false;
   }
   return true;
  });
  if(parts.length){best=parts;break}
 }catch(e){console.warn('offset failed',e)}}return best
}
function generateGuidance(source,additional=false){
 let width=+$('#gw').value||9,name=$('#gn').value.trim()||'Guidance',p=usablePoly(),lines=[],coverage=$('#coverage').value,base=baseReference(source);
 if(!p||!base||turf.length(base,{units:'meters'})<1)return alert('The reference line is too short.');
 let mask=additional?existingCoverage(width):null;
 let requested=!additional&&coverage==='count'?Math.max(1,+$('#gc').value||1):Infinity;
 let left=additional&&coverage==='count'?Math.max(0,+($('#leftQty')?.value||0)):Infinity;
 let right=additional&&coverage==='count'?Math.max(0,+($('#rightQty')?.value||0)):Infinity;
 let offsets=[];
 if(source==='border'){
  let start=(S.borderPasses+.5)*width;
  if(additional&&coverage==='count'){
   // Respect left/right quantities. Only the side that actually falls inside the field will survive clipping.
   for(let i=0;i<Math.max(left,right);i++){if(i<left)offsets.push(-(start+i*width));if(i<right)offsets.push(start+i*width)}
  }else{
   // Try both sides so border direction never decides whether guidance appears.
   for(let i=0;i<1000;i++){let d=start+i*width;offsets.push(d,-d)}
  }
 }else{
  offsets.push(0);
  if(additional&&coverage==='count'){for(let i=1;i<=Math.max(left,right);i++){if(i<=left)offsets.push(-i*width);if(i<=right)offsets.push(i*width)}}
  else for(let i=1;i<1000;i++)offsets.push(i*width,-i*width)
 }
 let accepted=0,emptyRun=0;
 for(const off of offsets){
  if(!additional&&coverage==='count'&&accepted>=requested)break;
  let parts=offsetCandidates(source,base,off,p);
  if(mask)parts=parts.flatMap(f=>splitOutsideCoverage(f,mask));
  let chosen=longestNearReference(parts,base,off,width,additional&&coverage==='remaining');
  if(!chosen.length){emptyRun++;if((coverage==='fill'||coverage==='remaining')&&emptyRun>80)break;continue}
  emptyRun=0;
  for(const f of chosen)lines.push(f.geometry.coordinates.map(([x,y])=>[y,x]));
  accepted++;
 }
 if(!lines.length)return alert(additional?'No open space was found for additional guidance at this reference.':'No guidance lines could be created from this reference.');
 S.width=width;let referencePoints=source==='border'?null:(guideDraft?.points||[]).map(p=>p.slice());
 S.guidanceSets.push({name,kind:'main',source,lines,borderIndex:source==='border'?S._border:null,referencePoints});guideDraft=null;redraw();
 open(`<h3>Guidance Preview</h3><div class="status">${escapeHtml(name)}<br>${lines.length} guidance lines • ${width.toFixed(2)} m</div><div class="row"><button id="keep" class="primary">Save Guidance</button><button id="remove">Discard</button></div>`);$('#keep').onclick=editFieldScreen;$('#remove').onclick=()=>{S.guidanceSets.pop();redraw();guidanceMenu()}
}

function exportScreen(){open(`<h3>Export</h3><p>Download the current field, named borders, border passes, and guidance sets.</p><button id="geo" class="primary">Download GeoJSON</button><button id="shp">Download Shapefile ZIP</button><div id="exportStatus" class="muted"></div><button id="back">Back</button>`);$('#geo').onclick=()=>downloadBlob(new Blob([JSON.stringify(fc(),null,2)],{type:'application/geo+json'}),safe(S.name)+'.geojson');$('#shp').onclick=async()=>{let b=$('#shp'),st=$('#exportStatus');try{b.disabled=true;st.textContent='Building ZIP…';let data=await shpwrite.zip(fc(),{folder:safe(S.name),types:{polygon:'boundary',line:'lines',point:'points'}});let blob=data instanceof Blob?data:new Blob([data],{type:'application/zip'});downloadBlob(blob,safe(S.name)+'.zip');st.textContent='ZIP ready. Check your Downloads folder.'}catch(e){console.error(e);st.textContent='Could not create ZIP: '+(e?.message||e)}finally{b.disabled=false}};$('#back').onclick=editFieldScreen}
function fc(){let f=[turf.polygon([ring(true)],{type:'boundary',field:S.name})];S.sections.filter(s=>s.name).forEach(s=>f.push(turf.lineString(sectionLatLngs(s).map(([y,x])=>[x,y]),{type:'border',name:s.name})));S.guidanceSets.forEach(set=>set.lines.forEach((g,i)=>f.push(turf.lineString(g.map(([y,x])=>[x,y]),{type:set.kind,name:set.name,pass:i+1,width_m:S.width}))));return turf.featureCollection(f)}
function safe(s){return(s||'field').replace(/[^a-z0-9_-]+/gi,'_')}
function downloadBlob(blob,n){let url=URL.createObjectURL(blob),a=document.createElement('a');a.href=url;a.download=n;a.style.display='none';document.body.appendChild(a);a.click();setTimeout(()=>{URL.revokeObjectURL(url);a.remove()},3000)}
function showFieldsHome(){removeHandle();removeGuideHandle();guideDraft=null;hidePointMenu();mode=null;mapBar.classList.add('hidden');stageTitle.classList.add('hidden');home.classList.add('hidden');let cards=DB.fields.map(f=>{let old=S;S=f;let a=area().toFixed(2);S=old;return `<div class="field-card"><div><b>${escapeHtml(f.name)}</b><small>${a} ha</small></div><div class="field-card-actions"><button data-view="${f.id}" class="primary">View</button><button data-menu="${f.id}">⋮</button></div></div>`}).join('');open(`<div class="fields-head"><h2>My Fields</h2><button id="newFromList" class="primary">+ New Field</button></div>${!localStorage.getItem('flbGoogleMapsKey')?'<button id="setupGoogleHome" class="primary">Enable Google Satellite</button>':''}${cards||'<p>No fields saved yet. Create your first field.</p>'}`);$('#newFromList').onclick=newField;if($('#setupGoogleHome'))$('#setupGoogleHome').onclick=googleMapSetup;document.querySelectorAll('[data-view]').forEach(b=>b.onclick=()=>openField(+b.dataset.view));document.querySelectorAll('[data-menu]').forEach(b=>b.onclick=()=>fieldItemMenu(+b.dataset.menu));redraw()}
function openField(id){let f=DB.fields.find(x=>x.id===id);if(!f)return;S=f;DB.currentId=id;save();if(S.boundary.length)map.fitBounds(L.latLngBounds(S.boundary),{padding:[45,45],maxZoom:19});viewFieldScreen()}
function fieldItemMenu(id){let f=DB.fields.find(x=>x.id===id);if(!f)return;open(`<h3>${escapeHtml(f.name)}</h3><button id="deleteField" class="danger">Delete Field</button><button id="back">Back</button>`);$('#deleteField').onclick=()=>{if(confirm(`Delete ${f.name}? This cannot be undone.`)){DB.fields=DB.fields.filter(x=>x.id!==id);if(DB.currentId===id)DB.currentId=null;localStorage.setItem('flbFields',JSON.stringify(DB));S=emptyField();redraw();showFieldsHome()}};$('#back').onclick=showFieldsHome}
showFieldsHome();redraw();
