#!/usr/bin/env node
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { constants, closeSync, existsSync, fstatSync, lstatSync, mkdirSync, openSync, readFileSync, readdirSync, readSync, realpathSync, writeFileSync } from 'node:fs';
import { isAbsolute, join, relative, resolve, sep } from 'node:path';
import { arch, platform, release, machine } from 'node:os';
import { fileURLToPath } from 'node:url';

const check=(condition,message)=>{if(!condition) throw new Error(message);};
const sha256=bytes=>createHash('sha256').update(bytes).digest('hex');
const hashPattern=/^[a-f0-9]{64}$/;
const defaultRoot=fileURLToPath(new URL('../',import.meta.url));
const publicPrefixes=['Tornado/','packages/lean-crypto/','proofs/','native/','tests/','scripts/','fixtures/','assets/','docs/'];
const rootInputs=new Set(['Main.lean','Tornado.lean','lakefile.lean','lake-manifest.json','lean-toolchain','README.md','LICENSE','.gitignore']);
const maxReportBytes=16*1024*1024;
function plainObject(value) { return value && typeof value==='object' && !Array.isArray(value); }
function safeRelative(value,{artifact=false}={}) {
  check(typeof value==='string' && value.length>0 && value.length<=4096 && !isAbsolute(value) &&
    !value.includes('\\') && !value.includes('\0') && (value==='.gitignore' || value.split('/').every(part=>
      /^[A-Za-z0-9][A-Za-z0-9._-]*$/.test(part) || artifact && part==='.lake')), 'Unsafe relative input path');
  return value;
}
function publicInput(value) {
  safeRelative(value);
  check(rootInputs.has(value) || publicPrefixes.some(prefix=>value.startsWith(prefix)), 'Verification input is outside the public inventory');
  check(!value.split('/').some(part=>['private','secrets','keystore','keys'].includes(part.toLowerCase())) &&
    !/\.(?:pem|key|p12|pfx|sqlite|db|env)$/i.test(value), 'Private input paths are not recorded');
  return value;
}
function inside(root,name,{artifact=false}={}) {
  safeRelative(name,{artifact});
  let current=root;
  for (const part of name.split('/')) {
    current=join(current,part);
    check(!lstatSync(current).isSymbolicLink(), 'Input contains a symbolic link');
  }
  check(current.startsWith(root+sep),'Input escaped project root');
  return current;
}
function hashFile(file) {
  check(!lstatSync(file).isSymbolicLink(),'Refusing a symbolic-link file');
  const fd=openSync(file,constants.O_RDONLY | (constants.O_NOFOLLOW ?? 0));
  try {
    const before=fstatSync(fd,{bigint:true});
    check(before.isFile() && before.size>=0n && before.size<=BigInt(Number.MAX_SAFE_INTEGER),'Input is not a regular file');
    const hash=createHash('sha256'),buffer=Buffer.allocUnsafe(1024*1024);
    let n;
    while((n=readSync(fd,buffer,0,buffer.length,null))>0) hash.update(buffer.subarray(0,n));
    const after=fstatSync(fd,{bigint:true});
    check(before.size===after.size && before.mtimeNs===after.mtimeNs && before.ctimeNs===after.ctimeNs,'Input changed while hashing');
    return {sha256:hash.digest('hex'),size:Number(after.size)};
  } finally { closeSync(fd); }
}
function readBounded(file,limit) {
  const fd=openSync(file,constants.O_RDONLY | (constants.O_NOFOLLOW ?? 0));
  try {
    const before=fstatSync(fd,{bigint:true});
    check(before.isFile() && before.size>0n && before.size<=BigInt(limit),'Invalid JSON file size or type');
    const bytes=Buffer.alloc(Number(before.size)+1);let used=0,n;
    while(used<bytes.length && (n=readSync(fd,bytes,used,bytes.length-used,null))>0) used+=n;
    const after=fstatSync(fd,{bigint:true});
    check(used===Number(before.size) && before.size===after.size && before.mtimeNs===after.mtimeNs &&
      before.ctimeNs===after.ctimeNs,'JSON input changed while reading');
    return bytes.subarray(0,used);
  } finally {closeSync(fd);}
}
function run(command,args,cwd,{optional=false}={}) {
  const result=spawnSync(command,args,{cwd,encoding:'utf8',timeout:15000,maxBuffer:1024*1024,
    env:{...process.env,NO_COLOR:'1',TZ:'UTC',GIT_OPTIONAL_LOCKS:'0'}});
  if(optional && (result.error || result.signal || result.status!==0)) return null;
  check(!result.error && !result.signal && result.status===0,`Metadata command failed: ${command}`);
  return (result.stdout+result.stderr).trim();
}
function environment(root) {
  // These are build tools, never the candidate CLI or prover worker.
  return {platform:platform(),architecture:arch(),osRelease:release(),machine:machine(),
    nodeVersion:process.version,nodeVersions:process.versions,
    leanVersion:run('lean',['--version'],root),lakeVersion:run('lake',['--version'],root),
    cCompiler:{command:'/usr/bin/cc',version:run('/usr/bin/cc',['--version'],root),
      ...hashFile(realpathSync('/usr/bin/cc'))}};
}
function gitInfo(root) {
  const top=run('git',['rev-parse','--show-toplevel'],root,{optional:true});
  if(!top || realpathSync(top)!==root) return {available:false};
  const head=run('git',['rev-parse','HEAD'],root,{optional:true});
  if(!head) return {available:false};
  const branch=run('git',['symbolic-ref','--quiet','--short','HEAD'],root,{optional:true});
  const status=run('git',['status','--porcelain=v1','--untracked-files=normal'],root,{optional:true});
  return {available:true,head,branch,dirty:status===null?null:status.length>0,
    informationalOnly:true}; // Never serialize filenames or private file contents.
}
function buildSourceInventory(root) {
  const found=[];
  function visit(directory) {
    for(const entry of readdirSync(directory,{withFileTypes:true})) {
      if(entry.name.startsWith('.') || ['node_modules','reports'].includes(entry.name)) continue;
      const path=join(directory,entry.name),name=relative(root,path).split(sep).join('/');
      check(!entry.isSymbolicLink(),'Build source inventory contains a symbolic link');
      if(entry.isDirectory()) visit(path);
      else if(entry.isFile() && (name.endsWith('.lean') || name.startsWith('native/') && /\.(?:c|h)$/.test(name))) found.push(name);
    }
  }
  visit(root);
  return found.sort();
}
function inventoryDigest(records) {
  return sha256(records.map(row=>`${row.path}\0${row.sha256}\0${row.size}\n`).join(''));
}
function sourceInput(row) {
  return row.path.endsWith('.lean') || row.path.startsWith('native/') ||
    row.path.startsWith('scripts/') || /(?:^|\/)(?:lakefile\.lean|lake-manifest\.json|lean-toolchain)$/.test(row.path);
}
function validateInventory(records,label) {
  check(Array.isArray(records) && records.length>0,`${label} inventory missing`);
  let previous;
  for(const row of records) {
    check(plainObject(row) && hashPattern.test(row.sha256) &&
      Number.isSafeInteger(row.size) && row.size>=0,`Invalid ${label.toLowerCase()} inventory record`);
    publicInput(row.path);
    check(previous===undefined || previous<row.path,`${label} inventory contains duplicate or unsorted paths`);
    previous=row.path;
  }
  return records;
}
function reportSnapshot(root,name,maxAgeSeconds) {
  safeRelative(name);
  check(name.startsWith('reports/'),'Verification report must be under reports/');
  const file=inside(root,name),bytes=readBounded(file,maxReportBytes);
  check(bytes.length>0 && bytes.length<=maxReportBytes,'Invalid verification report size');
  const report=JSON.parse(bytes.toString('utf8'));
  check(report.schemaVersion===1 && report.status==='PASS_WITH_LIMITATIONS' &&
    typeof report.runId==='string' && /^[a-f0-9-]{36}$/.test(report.runId),'Fresh full PASS_WITH_LIMITATIONS report required');
  const start=Date.parse(report.startedAtUTC),finish=Date.parse(report.finishedAtUTC),now=Date.now();
  check(Number.isFinite(start) && Number.isFinite(finish) && start<=finish && finish<=now &&
    now-finish<=maxAgeSeconds*1000,'Verification report is stale or has invalid timestamps');
  check(plainObject(report.inputHashes) && Object.keys(report.inputHashes).length>0,'Verification report input hashes are missing');
  check(Number.isSafeInteger(report.nativeLeanSourceFiles) && report.nativeLeanSourceFiles>0,
    'Verification report source inventory is missing');
  check(report.proofs?.noCustomAxiomsOrProofEscapes===true &&
    Number.isSafeInteger(report.proofs?.theoremCount) && report.proofs.theoremCount>0,'Verification proof result is missing');
  return {report,bytes,file,path:name};
}
function verifyInputs(root,report) {
  const records=[];
  for(const name of Object.keys(report.inputHashes).sort()) {
    publicInput(name);
    check(hashPattern.test(report.inputHashes[name]),'Malformed verification input hash');
    const actual=hashFile(inside(root,name));
    check(actual.sha256===report.inputHashes[name],`Verification input changed: ${name}`);
    records.push({path:name,...actual});
  }
  const sources=buildSourceInventory(root);
  for(const name of sources) check(Object.hasOwn(report.inputHashes,name),`Unverified build source: ${name}`);
  check(sources.filter(name=>name.endsWith('.lean')).length===report.nativeLeanSourceFiles,
    'Lean source inventory differs from verification report');
  for(const name of ['lakefile.lean','lake-manifest.json','lean-toolchain','scripts/verify.mjs',
    'scripts/build-provenance.mjs','scripts/check-build-integrity.mjs'])
    check(Object.hasOwn(report.inputHashes,name),`Missing required verification input: ${name}`);
  return records;
}
function parseOptions(argv,allowed) {
  const result={};
  for(let i=0;i<argv.length;i+=2) {
    check(allowed.includes(argv[i]) && argv[i+1] && !argv[i+1].startsWith('--') && !Object.hasOwn(result,argv[i]),'Invalid or duplicate provenance argument');
    result[argv[i]]=argv[i+1];
  }
  return result;
}
function validateManifest(value) {
  check(value?.schemaVersion===1 && value.kind==='tornado-lean-build-provenance' &&
    value.verification?.status==='PASS_WITH_LIMITATIONS' && hashPattern.test(value.verifiedInputContentSHA256) &&
    hashPattern.test(value.sourceContentSHA256) && plainObject(value.buildEnvironment),'Unsupported build manifest');
  for(const role of ['cli','worker']) check(hashPattern.test(value.artifacts?.[role]?.sha256) &&
    Number.isSafeInteger(value.artifacts[role].size) && value.artifacts[role].size>0,'Invalid binary manifest record');
  check(Array.isArray(value.assets) && value.assets.length>0,'Missing manifest assets');
  const inputs=validateInventory(value.verifiedInputs,'Verified input');
  const sources=validateInventory(value.sourceInventory,'Source');
  check(inventoryDigest(inputs)===value.verifiedInputContentSHA256,'Verified input inventory digest mismatch');
  check(inventoryDigest(sources)===value.sourceContentSHA256,'Source inventory digest mismatch');
  const expectedSources=inputs.filter(sourceInput);
  check(sources.length===expectedSources.length && sources.every((row,index)=>
    row.path===expectedSources[index].path && row.sha256===expectedSources[index].sha256 &&
    row.size===expectedSources[index].size),'Source inventory differs from verified input source records');
  return value;
}
function compare(argv) {
  const options=parseOptions(argv,['--first','--second','--candidate-root','--manifest-sha256']);
  check(options['--first'] && Boolean(options['--second'])!==Boolean(options['--candidate-root']),
    'Compare requires --first and exactly one of --second or --candidate-root');
  const read=name=>{
    const bytes=readBounded(resolve(name),maxReportBytes);
    return {bytes,value:validateManifest(JSON.parse(bytes.toString('utf8')))};
  };
  const firstRecord=read(options['--first']),first=firstRecord.value;
  if(options['--candidate-root']) {
    check(hashPattern.test(options['--manifest-sha256']) &&
      sha256(firstRecord.bytes)===options['--manifest-sha256'],'Trusted manifest digest mismatch');
    const root=realpathSync(resolve(options['--candidate-root']));
    check(Array.isArray(first.verifiedInputs) && first.verifiedInputs.length>0,'Baseline input inventory missing');
    const names=new Set();
    for(const row of first.verifiedInputs) {
      publicInput(row.path);check(hashPattern.test(row.sha256) && !names.has(row.path),'Invalid baseline input inventory');
      names.add(row.path);
      const actual=hashFile(inside(root,row.path));
      check(actual.sha256===row.sha256 && actual.size===row.size,`Rebuild source differs: ${row.path}`);
    }
    for(const name of buildSourceInventory(root)) check(names.has(name),`Unrecorded rebuild source: ${name}`);
    check(readFileSync(inside(root,'lean-toolchain'),'utf8').trim()===first.leanToolchain,'Rebuild Lean toolchain differs');
    check(JSON.stringify(environment(root))===JSON.stringify(first.buildEnvironment),'Rebuild toolchain/platform differs');
    for(const role of ['cli','worker']) {
      const actual=hashFile(inside(root,first.artifacts[role].path,{artifact:true}));
      check(actual.sha256===first.artifacts[role].sha256 && actual.size===first.artifacts[role].size,
        `Rebuild ${role} bytes differ: expected ${first.artifacts[role].sha256}, observed ${actual.sha256}`);
    }
    for(const asset of first.assets) {
      publicInput(asset.path);const actual=hashFile(inside(root,asset.path));
      check(actual.sha256===asset.sha256 && actual.size===asset.size,`Rebuild asset differs: ${asset.path}`);
    }
    console.log('MATCH: fresh candidate bytes match trusted baseline sources, toolchain, platform, CLI, worker and assets; no new verification verdict');
    return;
  }
  check(!options['--manifest-sha256'],'Manifest digest is only used with --candidate-root');
  const second=read(options['--second']).value;
  for(const key of ['sourceContentSHA256','verifiedInputContentSHA256','leanToolchain'])
    check(first[key]===second[key],`Rebuild source/toolchain differs: ${key}`);
  check(JSON.stringify(first.buildEnvironment)===JSON.stringify(second.buildEnvironment),'Rebuild toolchain/platform differs');
  for(const role of ['cli','worker']) check(first.artifacts[role].sha256===second.artifacts[role].sha256 &&
    first.artifacts[role].size===second.artifacts[role].size,`Rebuild ${role} bytes differ`);
  check(JSON.stringify(first.assets)===JSON.stringify(second.assets),'Rebuild assets differ');
  console.log('MATCH: recorded source, toolchain, platform, CLI, worker and assets agree; local comparison only');
}
function record(argv) {
  const options=parseOptions(argv,['--root','--report','--output','--cli','--worker','--max-age-seconds']);
  const root=realpathSync(resolve(options['--root']??defaultRoot));
  const reportName=options['--report']??'reports/verify.json';
  const output=options['--output']??'reports/build-provenance.json';
  safeRelative(output);check(output.startsWith('reports/'),'Manifest output must be under reports/');
  const maxAge=Number(options['--max-age-seconds']??3600);
  check(Number.isSafeInteger(maxAge) && maxAge>0 && maxAge<=86400,'Report maximum age must be 1..86400 seconds');
  const snapshot=reportSnapshot(root,reportName,maxAge),report=snapshot.report;
  for(const role of ['cli','worker']) {
    const item=report.buildArtifacts?.[role];
    check(item && hashPattern.test(item.sha256) && Number.isSafeInteger(item.size) && item.size>0 &&
      typeof item.path==='string','Verification report must bind tested CLI and worker bytes');
    safeRelative(item.path,{artifact:true});
  }
  const inputs=verifyInputs(root,report);
  check(hashFile(fileURLToPath(import.meta.url)).sha256===report.inputHashes['scripts/build-provenance.mjs'],
    'Executing provenance generator differs from verified source');
  const toolchain=readFileSync(inside(root,'lean-toolchain'),'utf8').trim();
  check(toolchain===report.leanToolchain,'Lean toolchain differs from verification report');
  const buildEnvironment=environment(root);
  check(buildEnvironment.leanVersion===report.leanVersion,'Lean executable version differs from verification report');
  const binary=(name,role)=>{
    const actual=hashFile(inside(root,name,{artifact:true}));
    const verified=report.buildArtifacts[role];
    check(actual.size>0 && name===verified.path && actual.size===verified.size &&
      actual.sha256===verified.sha256,`Tested ${role} bytes differ from verification report`);
    return {path:name,...actual};
  };
  const artifacts={cli:binary(options['--cli']??'.lake/build/bin/tornado','cli'),
    worker:binary(options['--worker']??'.lake/build/bin/tornado_prover_worker','worker')};
  check(Array.isArray(report.pinnedProvingAssets) && report.pinnedProvingAssets.length>0 &&
    report.pinnedProvingAssets.length<=64,'Verified proving-asset inventory is missing');
  const seen=new Set(),assets=report.pinnedProvingAssets.map(asset=>{
    check(asset && asset.result==='PASS' && typeof asset.file==='string' && asset.file.startsWith('assets/') &&
      hashPattern.test(asset.compressedSHA256) && hashPattern.test(asset.rawSHA256) &&
      Number.isSafeInteger(asset.rawSize) && asset.rawSize>0,'Malformed verified proving asset');
    publicInput(asset.file);check(!seen.has(asset.file),'Duplicate proving asset');seen.add(asset.file);
    check(report.inputHashes[asset.file]===asset.compressedSHA256,'Asset is absent from verified input hashes');
    const actual=hashFile(inside(root,asset.file));
    check(actual.sha256===asset.compressedSHA256,'Verified proving asset changed');
    return {path:asset.file,...actual,rawSHA256:asset.rawSHA256,rawSize:asset.rawSize};
  }).sort((a,b)=>a.path<b.path?-1:a.path>b.path?1:0);
  // Recheck after metadata collection and binary hashing, before recording.
  const finalInputs=verifyInputs(root,report);
  check(JSON.stringify(finalInputs)===JSON.stringify(inputs),'Verification inputs changed while recording');
  const finalReport=reportSnapshot(root,reportName,maxAge);
  check(sha256(finalReport.bytes)===sha256(snapshot.bytes),'Verification report changed while recording');
  for(const role of ['cli','worker']) check(JSON.stringify(hashFile(inside(root,artifacts[role].path,{artifact:true})))===
    JSON.stringify({sha256:artifacts[role].sha256,size:artifacts[role].size}),`${role} changed while recording`);
  const sources=inputs.filter(sourceInput);
  const manifest={schemaVersion:1,kind:'tornado-lean-build-provenance',generatedAtUTC:new Date().toISOString(),
    verification:{status:report.status,runId:report.runId,startedAtUTC:report.startedAtUTC,finishedAtUTC:report.finishedAtUTC,
      reportPath:reportName,reportSHA256:sha256(snapshot.bytes),reportSize:snapshot.bytes.length,
      maxReportAgeSeconds:maxAge,theoremCount:report.proofs.theoremCount},
    leanToolchain:toolchain,buildEnvironment,git:gitInfo(root),artifacts,assets,
    sourceContentSHA256:inventoryDigest(sources),sourceInventory:sources,
    verifiedInputContentSHA256:inventoryDigest(inputs),verifiedInputs:inputs,
    scope:{inputInventory:'Explicit public verification inputs; Lean/native source inventory excludes hidden directories, build caches, node_modules and reports',
      gitIsInformational:true,manifestRequiresIndependentTrust:true,
      executableAuthenticityProved:false,compilerCorrectnessProved:false,crossPlatformReproducibilityProved:false,
      runtimeWorkerPinningImplemented:false,sideChannelSafetyProved:false}};
  let parent=root;
  for(const part of output.split('/').slice(0,-1)) {
    parent=join(parent,part);
    if(!existsSync(parent)) mkdirSync(parent,{mode:0o755});
    const item=lstatSync(parent);
    check(item.isDirectory() && !item.isSymbolicLink(),'Manifest output contains a symbolic link');
  }
  const target=resolve(root,output);
  check(!existsSync(target),'Manifest output already exists; select a fresh output path');
  writeFileSync(target,JSON.stringify(manifest,null,2)+'\n',{flag:'wx',mode:0o644});
  const manifestHash=hashFile(target).sha256;
  console.log(`RECORDED: CLI, worker, ${assets.length} assets and ${inputs.length} stable verified inputs; manifest SHA256 ${manifestHash}`);
}
try {
  const [mode,...argv]=process.argv.slice(2);
  if(mode==='record') record(argv);
  else if(mode==='compare') compare(argv);
  else throw new Error('Use build-provenance.mjs record or build-provenance.mjs compare');
} catch(error) {
  console.error(`Build provenance failed: ${error instanceof Error?error.message:String(error)}`);
  process.exitCode=1;
}
