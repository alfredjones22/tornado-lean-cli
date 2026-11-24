#!/usr/bin/env node
// Untrusted public-data certificate extractor. The native Lean loader
// independently regenerates all local equations and checks every derivation.
// This script never reads notes, keys, environment secrets, or an RPC endpoint.
import fs from 'node:fs';
import path from 'node:path';
import zlib from 'node:zlib';
import {createHash} from 'node:crypto';
import {fileURLToPath} from 'node:url';

function generateDAG(circuit,graph){
const q=21888242871839275222246405745257275088548364400416034343698204186575808495617n;
const mod=x=>(x%q+q)%q,pow=(x,n)=>{let r=1n;for(;n;n>>=1n,x=mod(x*x))if(n&1n)r=mod(r*x);return r;};
let nodes=[];const intern=new Map();function node(key,data){if(intern.has(key))return intern.get(key);let id=nodes.length;nodes.push(data);intern.set(key,id);return id;}
function constant(x){x=mod(BigInt(x));return node('c'+x,{kind:'constant',value:x});}
const zero=constant(0),one=constant(1);
function op(kind,...args){let values=args.map(i=>nodes[i].value);if(values.every(v=>v!==undefined)){let[a,b]=values;switch(kind){case'add':return constant(a+b);case'sub':return constant(a-b);case'mul':return constant(a*b);case'inv':if(a===0n)throw Error('zero const');return constant(pow(a,q-2n));}}
 return node(kind+':'+args.join(','),{kind,args});}
const add=(a,b)=>op('add',a,b),sub=(a,b)=>op('sub',a,b),mul=(a,b)=>op('mul',a,b),inv=a=>op('inv',a),C=constant;
const slots=new Map(),origins=new Map(),conflicts=[],aliases=[];let source='';
function write(index,id){if(slots.has(index)){let prev=slots.get(index);if(prev!==id)conflicts.push({index,previous:origins.get(index),current:source,prevNode:prev,newNode:id});else aliases.push({index,previous:origins.get(index),current:source});}else{slots.set(index,id);origins.set(index,source);}}
function read(i){if(!slots.has(i))throw Error('unassigned '+i+' at '+source);return slots.get(i);}
for(let i=0;i<50;i++){source='input:'+i;write(i,i===0?one:node('input:'+i,{kind:'input',index:i}));}
for(const n of graph.num2bits){source=n.name;for(let j=0;j<n.outputs.length;j++)write(n.outputs[j],node('bit:'+read(n.input)+':'+j,{kind:'bit',input:read(n.input),bit:j}));}
for(const b of graph.bases){source='base:'+b.index;write(b.index,C(b.value));}
function outputs(kind,i){let[x,y,z,w]=i;switch(kind){
case'MontgomeryAdd':{let l=mul(sub(w,y),inv(sub(z,x))),a=sub(sub(sub(mul(l,l),C(168698)),x),z);return[l,a,sub(mul(l,sub(x,a)),y)];}
case'MontgomeryDouble':{let xx=mul(x,x),l=mul(add(add(mul(C(3),xx),mul(C(337396),x)),one),inv(mul(C(2),y))),a=sub(sub(mul(l,l),C(168698)),mul(C(2),x));return[xx,l,a,sub(mul(l,sub(x,a)),y)];}
case'Edwards2Montgomery':{let a=mul(add(one,y),inv(sub(one,y)));return[a,mul(a,inv(x))];}
case'Montgomery2Edwards':return[mul(x,inv(y)),mul(sub(x,one),inv(add(x,one)))];
case'BabyAdd':{let b=mul(x,w),g=mul(y,z),d=mul(sub(y,mul(C(168700),x)),add(z,w)),t=mul(b,g);return[b,g,d,t,mul(add(b,g),inv(add(one,mul(C(168696),t)))),mul(sub(add(d,mul(C(168700),b)),g),inv(sub(one,mul(C(168696),t))))];}
case'Square':return[mul(x,x)];case'Window4':return[sub(x,mul(mul(C(2),x),y))];
case'MultiMux3':{let s10=mul(y,x),o=[s10],coords=[];for(let k=0;k<2;k++){let c=i.slice(3+8*k,11+8*k);let a210=mul(sub(add(add(sub(add(sub(sub(c[7],c[6]),c[5]),c[4]),c[3]),c[2]),c[1]),c[0]),s10),a21=mul(add(sub(sub(c[6],c[4]),c[2]),c[0]),y),a20=mul(add(sub(sub(c[5],c[4]),c[1]),c[0]),x),a2=sub(c[4],c[0]),a10=mul(add(sub(sub(c[3],c[2]),c[1]),c[0]),s10),a1=mul(sub(c[2],c[0]),y),a0=mul(sub(c[1],c[0]),x),out=add(mul(add(add(add(a210,a21),a20),a2),z),add(add(add(a10,a1),a0),c[0]));coords.push([a210,a21,a20,a2,a10,a1,a0,c[0],out]);}for(let j=0;j<9;j++)o.push(coords[0][j],coords[1][j]);return o;}
default:throw Error(kind);}}
for(const p of graph.primitives){source=p.name;let result=outputs(p.kind,p.inputs.map(read));result.forEach((id,j)=>write(p.outputs[j],id));}
const constants=['0',...JSON.parse(circuit.templates.MiMCFeistel.match(/ctx\.setVar\("c_partial", \[\], (\[[\s\S]*?\])\);/)[1]),'0'].map(C);
for(let k=0;k<20;k++){let m=graph.merkle[k],[f,g]=graph.feistel[k];source='merkle:'+k;let selector=read(m.selector),l=read(m.leftInput),r=read(m.rightInput);let bit=nodes[selector];let lm=node('mux:'+selector+':'+l+':'+r,{kind:'mux',selector,left:l,right:r}),rm=node('mux:'+selector+':'+r+':'+l,{kind:'mux',selector,left:r,right:l});write(m.leftOutput,lm);write(m.rightOutput,rm);
 write(f.key,zero);write(f.leftInput,lm);write(f.rightInput,zero);
 for(let j=0;j<2;j++){let h=j===0?f:g;if(j){write(g.key,zero);write(g.leftInput,add(read(f.leftOutput),read(m.rightOutput)));write(g.rightInput,read(f.rightOutput));}let a=read(h.leftInput),b=read(h.rightInput),key=read(h.key);for(let round=0;round<220;round++){source='feistel:'+k+':'+j+':'+round;let t=add(add(a,key),constants[round]),t2=mul(t,t),t4=mul(t2,t2),t5=mul(t4,t);write(h.t2[round],t2);write(h.t4[round],t4);if(round<219){let next=add(b,t5);write(h.leftRounds[round],next);write(h.rightRounds[round],a);b=a;a=next;}else{write(h.leftOutput,a);write(h.rightOutput,add(b,t5));}}}
 source='hash:'+k;write(m.hashOutput,read(g.leftOutput));}

if(conflicts.length!==1||conflicts[0].index!==49||slots.size!==graph.nSignals)throw Error('Pinned graph alias/coverage expectations differ.');
const serialNodes=nodes.map(value=>value.kind==='constant'?{kind:value.kind,value:String(value.value)}:value);
return {nodes:serialNodes,slots:[...slots].sort(([a],[b])=>a-b),statistics:{nodes:nodes.length,assigned:slots.size,aliases:aliases.length,commitmentAliases:conflicts.length}};
}

function generateElimination(circuit,rawGraph,dag){
const graph={...rawGraph,feistel:rawGraph.feistel.map(stages=>({first:stages[0],second:stages[1]}))};
const q=21888242871839275222246405745257275088548364400416034343698204186575808495617n;
const mod=x=>((x%q)+q)%q;
const pow=(x,n)=>{let r=1n;for(x=mod(x);n>0n;n>>=1n,x=mod(x*x))if(n&1n)r=mod(r*x);return r;};
const inv=x=>{if(mod(x)===0n)throw Error('constant inverse zero');return pow(x,q-2n);};
const norm=row=>new Map([...row].map(([i,c])=>[+i,mod(BigInt(c))]).filter(([i,c])=>c!==0n));
const zero=()=>new Map();const con=x=>norm([[0,x]]);const atom=i=>norm([[i,1n]]);
const plus=(...rows)=>{const out=new Map();for(const row of rows)for(const[i,c]of row)out.set(i,mod((out.get(i)??0n)+c));return norm(out);};
const times=(a,c)=>norm([...a].map(([i,x])=>[i,x*c]));const minus=(a,b)=>plus(a,times(b,-1n));
const asConst=row=>row.size===0?0n:row.size===1&&row.has(0)?row.get(0):null;
const constants=new Map(dag.slots.flatMap(([slot,index])=>dag.nodes[index].kind==='constant'?[[slot,BigInt(dag.nodes[index].value)]]:[]));const known=new Set(Array.from({length:50},(_,i)=>i));
const row=i=>constants.has(i)?con(constants.get(i)):atom(i);
const linear=[];const nonlinear=[];const sources=[];let constantPrimitives=0;
function lin(expression,source){if(expression.size)linear.push({row:expression,source});}
function equality(output,expression,source){lin(minus(atom(output),expression),source);const value=asConst(expression);if(value!==null){if(constants.has(output)&&constants.get(output)!==value)throw Error('constant conflict');constants.set(output,value);}known.add(output);}
function constraint(a,b,c,source){const x=asConst(a),y=asConst(b);if(x!==null)lin(minus(times(b,x),c),source);else if(y!==null)lin(minus(times(a,y),c),source);else nonlinear.push({a,b,c,source});}
function product(output,a,b,source){constraint(a,b,atom(output),source);const x=asConst(a),y=asConst(b);if(x!==null&&y!==null)constants.set(output,mod(x*y));known.add(output);}
for(const component of graph.num2bits){let reconstructed=zero();for(let i=0;i<component.outputs.length;i++){const out=component.outputs[i];constraint(row(out),minus(row(out),con(1n)),zero(),component.name+':boolean'+i);reconstructed=plus(reconstructed,times(row(out),1n<<BigInt(i)));known.add(out);}lin(minus(row(component.input),reconstructed),component.name+':reconstruct');}
for(const base of graph.bases)equality(base.index,con(BigInt(base.value)),'base:'+base.index);
const mul=(x,y)=>mod(x*y),add=(x,y)=>mod(x+y),sub=(x,y)=>mod(x-y);
function constantOutputs(kind,v){const[x,y,z,w]=v;switch(kind){
case'MontgomeryAdd':{const l=mul(sub(w,y),inv(sub(z,x))),a=sub(sub(sub(mul(l,l),168698n),x),z);return[l,a,sub(mul(l,sub(x,a)),y)];}
case'MontgomeryDouble':{const xx=mul(x,x),l=mul(add(add(mul(3n,xx),mul(337396n,x)),1n),inv(mul(2n,y))),a=sub(sub(mul(l,l),168698n),mul(2n,x));return[xx,l,a,sub(mul(l,sub(x,a)),y)];}
case'Edwards2Montgomery':{const a=mul(add(1n,y),inv(sub(1n,y)));return[a,mul(a,inv(x))];}
case'Montgomery2Edwards':return[mul(x,inv(y)),mul(sub(x,1n),inv(add(x,1n)))];
case'BabyAdd':{const b=mul(x,w),g=mul(y,z),d=mul(sub(y,mul(168700n,x)),add(z,w)),t=mul(b,g);return[b,g,d,t,mul(add(b,g),inv(add(1n,mul(168696n,t)))),mul(sub(add(d,mul(168700n,b)),g),inv(sub(1n,mul(168696n,t))))];}
case'Square':return[mul(x,x)];default:return null;}}
for(const p of graph.primitives){for(const i of p.inputs)if(!known.has(i))throw Error('unknown input '+i+' '+p.name);
 for(const output of p.outputs)if(constants.has(output))equality(output,con(constants.get(output)),p.name+':publicConstant');
 const i=p.inputs.map(row),o=p.outputs;const[X,Y,Z,W]=i;
 switch(p.kind){
 case'Square':product(o[0],X,X,p.name);break;
 case'MontgomeryAdd':constraint(row(o[0]),minus(Z,X),minus(W,Y),p.name+':slope');constraint(row(o[0]),row(o[0]),plus(row(o[1]),con(168698n),X,Z),p.name+':x');constraint(row(o[0]),minus(X,row(o[1])),plus(row(o[2]),Y),p.name+':y');break;
 case'MontgomeryDouble':product(o[0],X,X,p.name+':square');constraint(row(o[1]),times(Y,2n),plus(times(row(o[0]),3n),times(X,337396n),con(1n)),p.name+':slope');constraint(row(o[1]),row(o[1]),plus(row(o[2]),con(168698n),times(X,2n)),p.name+':x');constraint(row(o[1]),minus(X,row(o[2])),plus(row(o[3]),Y),p.name+':y');break;
 case'Edwards2Montgomery':constraint(row(o[0]),minus(con(1n),Y),plus(con(1n),Y),p.name+':x');constraint(row(o[1]),X,row(o[0]),p.name+':y');break;
 case'Montgomery2Edwards':constraint(row(o[0]),Y,X,p.name+':x');constraint(row(o[1]),plus(X,con(1n)),minus(X,con(1n)),p.name+':y');break;
 case'BabyAdd':product(o[0],X,W,p.name+':beta');product(o[1],Y,Z,p.name+':gamma');constraint(minus(Y,times(X,168700n)),plus(Z,W),row(o[2]),p.name+':delta');product(o[3],row(o[0]),row(o[1]),p.name+':tau');constraint(row(o[4]),plus(con(1n),times(row(o[3]),168696n)),plus(row(o[0]),row(o[1])),p.name+':x');constraint(row(o[5]),minus(con(1n),times(row(o[3]),168696n)),minus(plus(row(o[2]),times(row(o[0]),168700n)),row(o[1])),p.name+':y');break;
 case'Window4':constraint(times(X,2n),Y,minus(X,row(o[0])),p.name);break;
 case'MultiMux3':{product(o[0],i[1],i[0],p.name+':s10');for(let k=0;k<2;k++){const c=i.slice(3+8*k,11+8*k),ix=j=>o[1+j*2+k],out=j=>row(ix(j));const a210=plus(c[7],times(c[6],-1n),times(c[5],-1n),c[4],times(c[3],-1n),c[2],c[1],times(c[0],-1n));product(ix(0),a210,row(o[0]),p.name+':a210'+k);product(ix(1),plus(c[6],times(c[4],-1n),times(c[2],-1n),c[0]),i[1],p.name+':a21'+k);product(ix(2),plus(c[5],times(c[4],-1n),times(c[1],-1n),c[0]),i[0],p.name+':a20'+k);equality(ix(3),minus(c[4],c[0]),p.name+':a2'+k);product(ix(4),plus(c[3],times(c[2],-1n),times(c[1],-1n),c[0]),row(o[0]),p.name+':a10'+k);product(ix(5),minus(c[2],c[0]),i[1],p.name+':a1'+k);product(ix(6),minus(c[1],c[0]),i[0],p.name+':a0'+k);equality(ix(7),c[0],p.name+':a'+k);constraint(plus(out(0),out(1),out(2),out(3)),i[2],minus(out(8),plus(out(4),out(5),out(6),c[0])),p.name+':out'+k);}break;}
 default:throw Error('kind '+p.kind);}
 for(const out of o)known.add(out);
}
// The following are source semantic relations: the public nullifier is the
// Pedersen result, and the supplied root equals the selected MiMC path.
lin(minus(row(28300),row(2)),'source:nullifierHash');
let roundConstants=null;const match=circuit.templates.MiMCFeistel.match(/ctx\.setVar\("c_partial", \[\], (\[[\s\S]*?\])\);/);if(match)roundConstants=["0",...JSON.parse(match[1]),"0"];
if(!roundConstants)throw Error('Pinned MiMC constants could not be extracted.');
for(let level=0;level<20;level++){const m=graph.merkle[level],s=graph.feistel[level];
 constraint(minus(row(m.rightInput),row(m.leftInput)),row(m.selector),minus(row(m.leftOutput),row(m.leftInput)),'merkle'+level+':left');constraint(minus(row(m.leftInput),row(m.rightInput)),row(m.selector),minus(row(m.rightOutput),row(m.rightInput)),'merkle'+level+':right');constraint(row(m.selector),minus(row(m.selector),con(1n)),zero(),'merkle'+level+':bit');for(const out of[m.leftOutput,m.rightOutput])known.add(out);
 equality(s.first.key,con(0n),'mimc:key');equality(s.first.leftInput,row(m.leftOutput),'mimc:left');equality(s.first.rightInput,con(0n),'mimc:right');
 for(let stage=0;stage<2;stage++){const f=stage===0?s.first:s.second;if(stage===1){equality(f.key,con(0n),'mimc:key2');equality(f.leftInput,plus(row(s.first.leftOutput),row(m.rightOutput)),'mimc:absorb');equality(f.rightInput,row(s.first.rightOutput),'mimc:right2');}
  let left=row(f.leftInput),right=row(f.rightInput);for(let j=0;j<220;j++){const t=plus(left,row(f.key),con(BigInt(roundConstants[j])));product(f.t2[j],t,t,'mimc'+level+':t2:'+stage+':'+j);product(f.t4[j],row(f.t2[j]),row(f.t2[j]),'mimc'+level+':t4:'+stage+':'+j);if(j<219){constraint(row(f.t4[j]),t,minus(row(f.leftRounds[j]),right),'mimc'+level+':next:'+stage+':'+j);equality(f.rightRounds[j],left,'mimc:rightcopy');left=row(f.leftRounds[j]);right=row(f.rightRounds[j]);}else{equality(f.leftOutput,left,'mimc:leftout');constraint(row(f.t4[j]),t,minus(row(f.rightOutput),right),'mimc'+level+':last:'+stage);known.add(f.rightOutput);}}
 }
 equality(m.hashOutput,row(s.second.leftOutput),'mimc:hashout');}
lin(minus(row(graph.rootSignal),row(graph.merkle[19].hashOutput)),'source:root');
const stats={constantPrimitives,constantSignals:constants.size,linear:linear.length,nonlinear:nonlinear.length,known:known.size};
// Sparse Gaussian elimination only for non-R1CS signals. Every basis row is
// a combination of local linear equations, not a claimed R1CS equation.
const basis=new Map();const basisIds=new Map();const ruleIds=new Map();const steps=[];const rules=[];let nextRowID=linear.length;let maxWidth=0,zeroRows=0,remaining=[];
function derivedScale(source,scalar){const id=nextRowID++;steps.push({kind:'scale',source,scalar:String(mod(scalar))});return id;}
function derivedAdd(left,right){const id=nextRowID++;steps.push({kind:'add',left,right});return id;}
function reduce(r,id){r=new Map(r);for(;;){let pivot=-1;for(const i of r.keys())if(i>=circuit.nVars&&basis.has(i)&&i>pivot)pivot=i;if(pivot<0)break;const c=r.get(pivot);r=plus(r,times(basis.get(pivot),-c));id=derivedAdd(id,derivedScale(basisIds.get(pivot),-c));}return {row:r,id};}
for(let k=0;k<linear.length;k++){let reduced=reduce(linear[k].row,k);let r=reduced.row,id=reduced.id;let pivot=-1;for(const i of r.keys())if(i>=circuit.nVars&&i>pivot)pivot=i;if(pivot>=0){const s=inv(r.get(pivot));r=times(r,s);basis.set(pivot,r);id=derivedScale(id,s);basisIds.set(pivot,id);ruleIds.set(pivot,rules.length);rules.push({pivot,row:id});maxWidth=Math.max(maxWidth,r.size);}else if(r.size)remaining.push({row:r,source:linear[k].source});else zeroRows++;}
const substitutionTrace=r=>{let out=new Map(r),used=[];for(;;){let pivot=-1;for(const i of out.keys())if(i>=circuit.nVars&&i>pivot)pivot=i;if(pivot<0)break;if(!basis.has(pivot))throw Error('unsolved auxiliary '+pivot);const coeff=out.get(pivot);out=plus(out,times(basis.get(pivot),-coeff));used.push(ruleIds.get(pivot));}return {row:out,rules:used};};
const substitute=r=>substitutionTrace(r).row;
const poly=(a,b,c)=>{const p=new Map();for(const[i,x]of a)for(const[j,y]of b){const key=i<=j?i+','+j:j+','+i;p.set(key,mod((p.get(key)??0n)+x*y));}for(const[i,z]of c){const key='0,'+i;p.set(key,mod((p.get(key)??0n)-z));}return new Map([...p].filter(([k,v])=>v!==0n));};
function key(p){const terms=[...p].sort(([a],[b])=>{const[x,y]=a.split(',').map(Number),[z,w]=b.split(',').map(Number);return x-z||y-w;});if(!terms.length)return'zero';const coeff=inv(terms[0][1]);return terms.map(([k,v])=>k+':'+mod(v*coeff)).join('|');}
const generated=new Map();let localZero=0;for(let k=0;k<nonlinear.length;k++){const x=nonlinear[k];const p=poly(substitute(x.a),substitute(x.b),substitute(x.c));const hash=key(p);if(hash==='zero')localZero++;generated.set(hash,{source:x.source,k,poly:p});}
for(const x of remaining){const hash=key(poly(con(1n),substitute(x.row),zero()));generated.set(hash,{source:x.source,linear:true});}
const unmatched=[];const matches=[];for(let k=0;k<circuit.constraints.length;k++){const[a,b,c]=circuit.constraints[k].map(x=>norm(Object.entries(x)));const p=poly(a,b,c),hash=key(p);if(!generated.has(hash))unmatched.push(k);else {const source=generated.get(hash);const sorted=p=>[...p].sort(([a],[b])=>{const[x,y]=a.split(',').map(Number),[z,w]=b.split(',').map(Number);return x-z||y-w;});const scale=mod(sorted(p)[0][1]*inv(sorted(source.poly)[0][1]));matches.push({source:source.k,scale:String(scale)});}}

if(unmatched.length||remaining.length||matches.length!==circuit.constraints.length)throw Error('Generated equations do not match every target constraint.');
const substitutions=nonlinear.map(x=>({a:substitutionTrace(x.a).rules,b:substitutionTrace(x.b).rules,c:substitutionTrace(x.c).rules}));
return {certificate:{steps,rules,substitutions,matches},statistics:{linears:linear.length,nonlinear:nonlinear.length,steps:steps.length,rules:rules.length,targets:matches.length}};
}


let repoRoot=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'..');
let output=null;let write=false;
for(let index=2;index<process.argv.length;index++){
 const flag=process.argv[index];
 if(flag==='--write')write=true;
 else if(flag==='--check')write=false;
 else if(flag==='--root')repoRoot=path.resolve(process.argv[++index]??'');
 else if(flag==='--out')output=path.resolve(process.argv[++index]??'');
 else throw Error(`Unknown argument: ${flag}`);
}
output??=path.join(repoRoot,'assets/proving/tornado-witness-certificate-v1.json.gz');
const graph=JSON.parse(fs.readFileSync(path.join(repoRoot,'fixtures/witness-vm-selected-components.json'),'utf8'));
const circuit=JSON.parse(zlib.gunzipSync(fs.readFileSync(path.join(repoRoot,'assets/proving/tornado-3ddd61dbff09caee.json.gz'))));
const dag=generateDAG(circuit,graph);
const eliminated=generateElimination(circuit,graph,dag);
const text=JSON.stringify({schemaVersion:1,nodes:dag.nodes,certificate:eliminated.certificate});
const compressed=zlib.gzipSync(text,{level:9});
if(compressed.length>2*1024*1024||Buffer.byteLength(text)>16*1024*1024)throw Error('Certificate exceeds the native loader limits.');
if(write){fs.mkdirSync(path.dirname(output),{recursive:true});fs.writeFileSync(output,compressed);}
else if(!fs.existsSync(output)||!fs.readFileSync(output).equals(compressed))throw Error('Bundled witness certificate differs; regenerate with --write.');
console.log(`PASS: public witness certificate ${write?'generated':'reproduced'}; `+JSON.stringify({...dag.statistics,...eliminated.statistics,rawBytes:Buffer.byteLength(text),gzipBytes:compressed.length,sha256:createHash('sha256').update(compressed).digest('hex')}));
