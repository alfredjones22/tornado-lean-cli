#!/usr/bin/env node
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { chmodSync, copyFileSync, existsSync, mkdirSync, mkdtempSync, readFileSync, renameSync, rmSync, symlinkSync, truncateSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { tmpdir } from 'node:os';
import { fileURLToPath } from 'node:url';
import { gzipSync } from 'node:zlib';

// Every gate report and binary in this regression is explicitly synthetic.
// The fake executable candidates leave markers if executed; neither tool may
// run them. These tests never produce a provenance record for the real CLI.
const stage=fileURLToPath(new URL('../',import.meta.url));
const root=mkdtempSync(join(tmpdir(),'tornado-provenance-public-test-'));
const hash=bytes=>createHash('sha256').update(bytes).digest('hex');
const inventoryDigest=records=>hash(records.map(row=>`${row.path}\0${row.sha256}\0${row.size}\n`).join(''));
const put=(name,content)=>{mkdirSync(dirname(join(root,name)),{recursive:true});writeFileSync(join(root,name),content);};
const get=name=>readFileSync(join(root,name));
const clone=value=>JSON.parse(JSON.stringify(value));
let checks=0;
function invoke(script,args,expect,needle,timeout=30000) {
  const result=spawnSync(process.execPath,[join(root,'scripts',script),...args],
    {cwd:root,encoding:'utf8',timeout,maxBuffer:1024*1024});
  assert.equal(result.error,undefined);assert.equal(result.signal,null);
  if(expect===0) assert.equal(result.status,0,result.stderr+result.stdout);
  else assert.notEqual(result.status,0,result.stderr+result.stdout);
  if(needle) assert.match(result.stdout+result.stderr,needle);
  assert.equal(existsSync(join(root,'CLI_EXECUTED')),false,'Candidate CLI was executed');
  assert.equal(existsSync(join(root,'WORKER_EXECUTED')),false,'Candidate worker was executed');
  checks++;
  return result;
}
try {
  for(const file of ['build-provenance.mjs','check-build-integrity.mjs']) {
    mkdirSync(join(root,'scripts'),{recursive:true});
    copyFileSync(join(stage,'scripts',file),join(root,'scripts',file));
  }
  put('lean-toolchain','leanprover/lean4:v4.29.1\n');
  put('lakefile.lean','import Lake\n');put('lake-manifest.json','{"version":"1.1.0","packages":[]}\n');
  put('Main.lean','def syntheticPublicValue : Nat := 7\n');
  put('packages/lean-crypto/LeanCrypto/PublicSynthetic.lean','def syntheticPureValue : Nat := 11\n');
  put('proofs/LeanCryptoProofs/PublicSynthetic.lean','theorem syntheticPublicProof : 1 = 1 := rfl\n');
  put('app-proofs/TornadoProofs/PublicSynthetic.lean','theorem syntheticApplicationProof : 2 = 2 := rfl\n');
  put('docs/BUILD_PROVENANCE.md','Public synthetic provenance scope.\n');
  put('docs/SECURITY_SPEC.md','Public synthetic verification boundary.\n');
  put('.gitignore','.lake/\nreports/\n');
  put('native/synthetic.c','int public_synthetic_value(void) { return 7; }\n');
  put('scripts/verify.mjs','throw new Error("Synthetic report only; not a real verifier");\n');
  const fakeExecutable=marker=>`#!/usr/bin/env node\nimport {writeFileSync} from 'node:fs';\nwriteFileSync(${JSON.stringify(join(root,marker))},'MUST NEVER EXECUTE');\nprocess.exit(99);\n`;
  put('.lake/build/bin/tornado',fakeExecutable('CLI_EXECUTED'));
  put('.lake/build/bin/tornado_prover_worker',fakeExecutable('WORKER_EXECUTED'));
  chmodSync(join(root,'.lake/build/bin/tornado'),0o755);chmodSync(join(root,'.lake/build/bin/tornado_prover_worker'),0o755);
  const assetNames=['assets/proving/public-circuit.json.gz','assets/proving/public-key.bin.gz'];
  const assets=assetNames.map((file,i)=>{
    const raw=Buffer.from(`PUBLIC SYNTHETIC ASSET ${i}\n`),compressed=gzipSync(raw);
    put(file,compressed);
    return {file,compressedSHA256:hash(compressed),rawSHA256:hash(raw),rawSize:raw.length,result:'PASS'};
  });
  const lean=spawnSync('lean',['--version'],{cwd:root,encoding:'utf8',timeout:15000});
  assert.equal(lean.status,0,lean.stderr);
  const inputs=['Main.lean','lakefile.lean','lake-manifest.json','lean-toolchain','native/synthetic.c',
    'packages/lean-crypto/LeanCrypto/PublicSynthetic.lean','proofs/LeanCryptoProofs/PublicSynthetic.lean',
    'app-proofs/TornadoProofs/PublicSynthetic.lean',
    'docs/BUILD_PROVENANCE.md','docs/SECURITY_SPEC.md','.gitignore',
    'scripts/verify.mjs','scripts/build-provenance.mjs','scripts/check-build-integrity.mjs',...assetNames];
  const artifacts=Object.fromEntries([['cli','.lake/build/bin/tornado'],['worker','.lake/build/bin/tornado_prover_worker']]
    .map(([role,path])=>[role,{path,sha256:hash(get(path)),size:get(path).length}]));
  const report={schemaVersion:1,status:'PASS_WITH_LIMITATIONS',runId:'00000000-0000-4000-8000-000000000001',
    startedAtUTC:new Date(Date.now()-5000).toISOString(),finishedAtUTC:new Date().toISOString(),
    leanToolchain:'leanprover/lean4:v4.29.1',leanVersion:lean.stdout.trim(),nativeLeanSourceFiles:5,
    inputHashes:Object.fromEntries(inputs.map(file=>[file,hash(get(file))])),pinnedProvingAssets:assets,
    buildArtifacts:artifacts,proofs:{theoremCount:1,noCustomAxiomsOrProofEscapes:true}};
  const writeReport=(value=report)=>put('reports/verify.json',JSON.stringify(value,null,2)+'\n');
  const record=(output='reports/manifest.json',extra=[])=>invoke('build-provenance.mjs',
    ['record','--root',root,'--output',output,...extra],0,/RECORDED:/);
  const rejectRecord=(mutate,needle)=>{
    const changed=clone(report);mutate(changed);writeReport(changed);
    invoke('build-provenance.mjs',['record','--root',root,'--output','reports/rejected.json'],1,needle);
    assert.equal(existsSync(join(root,'reports/rejected.json')),false);
    writeReport();
  };
  writeReport();record();
  const manifestBytes=get('reports/manifest.json'),manifest=JSON.parse(manifestBytes),pin=hash(manifestBytes);
  const checkArgs=['--manifest',join(root,'reports/manifest.json'),'--manifest-sha256',pin,
    '--cli',join(root,artifacts.cli.path),'--worker',join(root,artifacts.worker.path),'--asset-root',root];
  const integrity=(args=checkArgs,expected=0,needle=/PASS:/,timeout=30000)=>invoke('check-build-integrity.mjs',args,expected,needle,timeout);
  integrity();
  assert.equal(manifest.git.available,false);
  assert.equal(manifest.verifiedInputs.length,inputs.length);
  assert.equal(manifest.sourceInventory.some(x=>x.path==='Main.lean'),true);
  assert.equal(manifest.verifiedInputs.some(x=>x.path==='.gitignore'),true);
  assert.equal(manifest.verifiedInputs.some(x=>x.path==='docs/BUILD_PROVENANCE.md'),true);
  assert.equal(manifest.sourceInventory.some(x=>x.path==='proofs/LeanCryptoProofs/PublicSynthetic.lean'),true);
  assert.equal(manifest.sourceInventory.some(x=>x.path==='app-proofs/TornadoProofs/PublicSynthetic.lean'),true);
  assert.equal(manifest.sourceInventory.some(x=>x.path==='packages/lean-crypto/LeanCrypto/PublicSynthetic.lean'),true);
  assert.equal(JSON.stringify(manifest).includes('MUST NEVER EXECUTE'),false);
  checks++;

  for(const [file,needle] of [[artifacts.cli.path,/CLI integrity mismatch/],
      [artifacts.worker.path,/Worker integrity mismatch/],[assetNames[0],/Asset .* integrity mismatch/]]) {
    const original=get(file);put(file,Buffer.concat([original,Buffer.from('TAMPER')]));
    integrity(checkArgs,1,needle);put(file,original);
  }
  integrity(checkArgs.map(x=>x===pin?'0'.repeat(64):x),1,/manifest digest mismatch/);
  put('reports/tampered-manifest.json',Buffer.concat([manifestBytes,Buffer.from(' ')]));
  integrity(checkArgs.map(x=>x===join(root,'reports/manifest.json')?join(root,'reports/tampered-manifest.json'):x),1,/manifest digest mismatch/);
  const badManifest=(mutate,needle)=>{
    const changed=clone(manifest);mutate(changed);const bytes=Buffer.from(JSON.stringify(changed));
    put('reports/bad-manifest.json',bytes);
    integrity(checkArgs.map(x=>x===pin?hash(bytes):x===join(root,'reports/manifest.json')?join(root,'reports/bad-manifest.json'):x),1,needle);
  };
  badManifest(x=>x.assets[0].path='../outside',/Unsafe manifest asset path/);
  badManifest(x=>x.assets.push(x.assets[0]),/Duplicate manifest asset/);
  badManifest(x=>x.schemaVersion=2,/Unsupported or unverified manifest/);
  badManifest(x=>x.artifacts.cli.sha256='bad',/Invalid CLI integrity record/);
  badManifest(x=>x.assets=[],/Invalid asset inventory/);
  const originalCli=get(artifacts.cli.path);rmSync(join(root,artifacts.cli.path));
  integrity(checkArgs,1,/ENOENT/);put(artifacts.cli.path,originalCli);
  put('candidate-link-target',originalCli);rmSync(join(root,artifacts.cli.path));
  symlinkSync(join(root,'candidate-link-target'),join(root,artifacts.cli.path));
  integrity(checkArgs,1,/symbolic-link candidate/);rmSync(join(root,artifacts.cli.path));put(artifacts.cli.path,originalCli);
  const originalAsset=get(assetNames[0]);put('asset-link-target',originalAsset);rmSync(join(root,assetNames[0]));
  symlinkSync(join(root,'asset-link-target'),join(root,assetNames[0]));
  integrity(checkArgs,1,/symbolic-link asset path/);rmSync(join(root,assetNames[0]));put(assetNames[0],originalAsset);
  integrity([...checkArgs,'--cli',join(root,artifacts.cli.path)],1,/Invalid or duplicate/);
  renameSync(join(root,'assets/proving'),join(root,'assets/proving-real'));
  symlinkSync(join(root,'assets/proving-real'),join(root,'assets/proving'));
  integrity(checkArgs,1,/symbolic-link asset path/);
  rmSync(join(root,'assets/proving'));renameSync(join(root,'assets/proving-real'),join(root,'assets/proving'));
  put('reports/oversized-manifest.json',Buffer.alloc(16*1024*1024+1,32));
  integrity(checkArgs.map(x=>x===join(root,'reports/manifest.json')?join(root,'reports/oversized-manifest.json'):x),1,/Invalid manifest size/);
  rmSync(join(root,'reports/oversized-manifest.json'));
  for(const [file,option,needle] of [['candidate-fifo','--cli',/nonempty regular file/],
      ['manifest-fifo','--manifest',/Invalid manifest size or type/]]) {
    const fifo=join(root,file);
    const created=spawnSync('mkfifo',[fifo],{encoding:'utf8',timeout:5000});
    assert.equal(created.error,undefined);assert.equal(created.status,0,created.stderr);
    const index=checkArgs.indexOf(option)+1;
    const args=checkArgs.map((arg,i)=>i===index?fifo:arg);
    integrity(args,1,needle,2000);
    rmSync(fifo);
  }
  put('huge-candidate',Buffer.alloc(1));
  truncateSync(join(root,'huge-candidate'),16*1024*1024*1024);
  integrity(checkArgs.map((arg,i)=>i===checkArgs.indexOf('--cli')+1?join(root,'huge-candidate'):arg),
    1,/CLI integrity mismatch: candidate size differs from trusted manifest/,2000);
  rmSync(join(root,'huge-candidate'));

  rejectRecord(x=>x.finishedAtUTC=new Date(Date.now()-7200000).toISOString(),/stale|invalid timestamps/);
  rejectRecord(x=>x.finishedAtUTC=new Date(Date.now()+60000).toISOString(),/stale|invalid timestamps/);
  rejectRecord(x=>x.status='PROOFS_CHECKED_ONLY',/Fresh full/);
  rejectRecord(x=>x.status='FAIL',/Fresh full/);
  rejectRecord(x=>delete x.inputHashes['Main.lean'],/Unverified build source/);
  rejectRecord(x=>delete x.inputHashes['app-proofs/TornadoProofs/PublicSynthetic.lean'],/Unverified build source/);
  rejectRecord(x=>x.nativeLeanSourceFiles++,/Lean source inventory differs/);
  rejectRecord(x=>x.inputHashes['../outside']='0'.repeat(64),/Unsafe relative input path/);
  rejectRecord(x=>x.inputHashes['.env']='0'.repeat(64),/Unsafe relative input path/);
  rejectRecord(x=>x.inputHashes['docs/.private.md']='0'.repeat(64),/Unsafe relative input path/);
  rejectRecord(x=>x.inputHashes['docs/.gitignore']='0'.repeat(64),/Unsafe relative input path/);
  rejectRecord(x=>x.inputHashes['.gitignore/child']='0'.repeat(64),/Unsafe relative input path/);
  rejectRecord(x=>delete x.buildArtifacts,/must bind tested CLI and worker/);
  rejectRecord(x=>x.buildArtifacts.cli.sha256='0'.repeat(64),/Tested cli bytes differ/);
  rejectRecord(x=>delete x.inputHashes[assetNames[0]],/Asset is absent/);
  rejectRecord(x=>x.inputHashes['Main.lean']='bad',/Malformed verification input hash/);
  rejectRecord(x=>x.proofs.noCustomAxiomsOrProofEscapes=false,/Verification proof result is missing/);
  rejectRecord(x=>x.leanToolchain='wrong/toolchain',/Lean toolchain differs/);
  rejectRecord(x=>delete x.inputHashes['scripts/check-build-integrity.mjs'],/Missing required verification input/);
  rejectRecord(x=>x.inputHashes['fixtures/secrets/private.json']='0'.repeat(64),/Private input paths/);
  const main=get('Main.lean');put('Main.lean',Buffer.concat([main,Buffer.from('-- changed\n')]));
  invoke('build-provenance.mjs',['record','--root',root,'--output','reports/rejected.json'],1,/Verification input changed/);put('Main.lean',main);
  put('Added.lean','def addedPublicValue := 8\n');
  invoke('build-provenance.mjs',['record','--root',root,'--output','reports/rejected.json'],1,/Unverified build source/);rmSync(join(root,'Added.lean'));
  put('native/added.h','int added_public_value(void);\n');
  invoke('build-provenance.mjs',['record','--root',root,'--output','reports/rejected.json'],1,/Unverified build source/);rmSync(join(root,'native/added.h'));
  put('main-link-target',main);rmSync(join(root,'Main.lean'));symlinkSync(join(root,'main-link-target'),join(root,'Main.lean'));
  invoke('build-provenance.mjs',['record','--root',root,'--output','reports/rejected.json'],1,/symbolic link/);rmSync(join(root,'Main.lean'));put('Main.lean',main);
  invoke('build-provenance.mjs',['record','--root',root,'--output','reports/rejected.json','--max-age-seconds','0'],1,/maximum age/);
  invoke('build-provenance.mjs',['record','--root',root,'--output','reports/manifest.json'],1,/already exists/);
  mkdirSync(join(root,'unrelated-output'));symlinkSync(join(root,'unrelated-output'),join(root,'reports/output-link'));
  invoke('build-provenance.mjs',['record','--root',root,'--output','reports/output-link/new.json'],1,/Manifest output contains a symbolic link/);
  assert.equal(existsSync(join(root,'unrelated-output/new.json')),false);rmSync(join(root,'reports/output-link'));

  // A fresh recording of the same synthetic bytes compares successfully.
  report.runId='00000000-0000-4000-8000-000000000002';report.finishedAtUTC=new Date().toISOString();writeReport();record('reports/manifest2.json');
  const compareArgs=['compare','--first',join(root,'reports/manifest.json'),'--second',join(root,'reports/manifest2.json')];
  invoke('build-provenance.mjs',compareArgs,0,/MATCH:/);
  for(const [key,mutate,needle] of [
    ['binary',x=>x.artifacts.worker.sha256='0'.repeat(64),/worker bytes differ/],
    ['source',x=>x.sourceContentSHA256='0'.repeat(64),/Source inventory digest mismatch/],
    ['source-record',x=>x.sourceInventory[0].sha256='0'.repeat(64),/Source inventory digest mismatch/],
    ['input-record',x=>x.verifiedInputs[0].sha256='0'.repeat(64),/Verified input inventory digest mismatch/],
    ['input-missing',x=>x.verifiedInputs.pop(),/Verified input inventory digest mismatch/],
    ['input-duplicate',x=>x.verifiedInputs.push(x.verifiedInputs[0]),/duplicate or unsorted/],
    ['source-order',x=>x.sourceInventory.reverse(),/duplicate or unsorted/],
    ['source-subset',x=>{x.sourceInventory.pop();x.sourceContentSHA256=inventoryDigest(x.sourceInventory);},
      /Source inventory differs from verified input source records/],
    ['source-consistent-change',x=>{
      for(const records of [x.sourceInventory,x.verifiedInputs]) records.find(row=>row.path==='Main.lean').sha256='0'.repeat(64);
      x.sourceContentSHA256=inventoryDigest(x.sourceInventory);
      x.verifiedInputContentSHA256=inventoryDigest(x.verifiedInputs);
    },/Rebuild source\/toolchain differs/],
    ['input-size',x=>x.verifiedInputs[0].size=-1,/Invalid verified input inventory record/],
    ['environment',x=>x.buildEnvironment.osRelease+='-changed',/toolchain\/platform differs/],
    ['asset',x=>x.assets[0].sha256='0'.repeat(64),/assets differ/]]) {
    const changed=clone(manifest);mutate(changed);put(`reports/compare-${key}.json`,JSON.stringify(changed));
    invoke('build-provenance.mjs',compareArgs.map(x=>x===join(root,'reports/manifest2.json')?join(root,`reports/compare-${key}.json`):x),1,needle);
  }
  const freshArgs=['compare','--first',join(root,'reports/manifest.json'),'--candidate-root',root,'--manifest-sha256',pin];
  invoke('build-provenance.mjs',freshArgs,0,/fresh candidate bytes match/);
  put(artifacts.worker.path,Buffer.concat([get(artifacts.worker.path),Buffer.from('REBUILD-DIFFERENCE')]));
  invoke('build-provenance.mjs',freshArgs,1,/Rebuild worker bytes differ/);
  put(artifacts.worker.path,fakeExecutable('WORKER_EXECUTED'));
  invoke('build-provenance.mjs',freshArgs.map(x=>x===pin?'0'.repeat(64):x),1,/Trusted manifest digest mismatch/);
  put('Main.lean',Buffer.concat([main,Buffer.from('-- rebuild source changed\n')]));
  invoke('build-provenance.mjs',freshArgs,1,/Rebuild source differs/);put('Main.lean',main);
  console.log(`PASS: ${checks} synthetic provenance/integrity gates, tested-binary binding, source/report freshness, tampering and symlink rejection, rebuild comparison; candidates never executed`);
} finally { rmSync(root,{recursive:true,force:true}); }
