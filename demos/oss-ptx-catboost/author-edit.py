"""Direct textual edits of frozen NVCC PTX; never compile CUDA to create candidate."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent
for d in sorted(D.iterdir()):
 if not d.is_dir() or not (d/'freeze.json').exists():continue
 s=(d/'original.ptx').read_text();orig=s
 if d.name=='reverse':
  s=s.replace('\tmov.u32 \t%r4, %nctaid.x;\n\tcvt.u64.u32 \t%rd12, %r4;\n\tmul.lo.s64 \t%rd5, %rd12, %rd1;','')
  s=s.replace('\tadd.s64 \t%rd19, %rd19, %rd5;\n\tsetp.lt.u64 \t%p2, %rd19, %rd3;\n\t@%p2 bra \t$L__BB0_2;','')
  domain='4-byte aligned in-place uint32 array; size<2^63; covering 1D launch grid*block>=floor(size/2), grid*block<=2^32; no wrapping byte range. Normal uncapped dispatch covers this. Loop-elision specialized launch; all values unrestricted.'
 elif d.name=='zero_partitions':
  s=s.replace('%p<3>','%p<4>').replace('%rd<5>','%rd<7>')
  s=s.replace('\tmov.u32 \t%r9, %nctaid.x;\n\tmul.lo.s32 \t%r3, %r1, %r9;','')
  s=s.replace('\tst.global.u32 \t[%rd4+4], %r10;\n\tst.global.u32 \t[%rd4], %r10;', '\tand.b64 %rd5, %rd4, 7;\n\tsetp.eq.u64 %p3, %rd5, 0;\n\tmov.u64 %rd6, 0;\n\t@%p3 st.global.u64 [%rd4], %rd6;\n\t@!%p3 st.global.u32 [%rd4+4], %r10;\n\t@!%p3 st.global.u32 [%rd4], %r10;')
  s=s.replace('\tadd.s32 \t%r11, %r11, %r3;\n\tsetp.lt.u32 \t%p2, %r11, %r6;\n\t@%p2 bra \t$L__BB0_2;','')
  domain='4-byte aligned TDataPartition array (8-byte struct); 0<=partCount<=2^31; covering 1D grid*block>=partCount and <=2^31. 4-byte alignment retained with guarded 64-bit stores and scalar fallback; no wrapping byte range.'
 elif d.name=='zero_segments':
  s=s.replace('\tcvt.u64.u32 \t%rd1, %r1;\n','').replace('\tshl.b64 \t%rd8, %rd1, 2;\n','').replace('%rd9, %rd7, %rd8','%rd9, %rd7, %rd5')
  domain='4-byte aligned disjoint flags/output arrays of size uint32; covering 1D grid*block<=2^32; no wrapping byte ranges; all flags, flagMask and initial output values unrestricted.'
 elif d.name=='fill_query_end_mask':
  s=s.replace('\tmul.wide.u32 \t%rd11, %r2, 4;\n\tadd.s64 \t%rd12, %rd6, %rd11;','\tadd.s64 \t%rd12, %rd8, 4;')
  domain='4-byte aligned disjoint qids/docs/masks; docCount<=2^31; docs entries valid qids indices; covering 1D launch<=2^31; no wrapping byte ranges; all qids unrestricted.'
 elif d.name=='compute_group_ids':
  s=s.replace('\tmov.u64 \t%rd28, 0;\n\t@%p1 bra \t$L__BB0_2;','\t@%p1 bra \t$L__BB0_11;')
  s=s.replace('\tmov.u32 \t%r26, 0;\n\t@%p1 bra \t$L__BB0_4;','')
  s=s.replace('\tmul.wide.s32 \t%rd18, %r2, 4;\n','').replace('%rd19, %rd17, %rd18','%rd19, %rd17, %rd15')
  domain='Normal block128 grid ceil(qCount/4); 0<=qCount<2^29; query sizes<=2^31-128; valid offsetsBias and disjoint in-bounds per-query destination ranges, 4-byte aligned nonwrapping arrays; read inputs disjoint output.'
 else:continue
 assert s!=orig
 (d/'edited.ptx').write_text(s)
 (d/'edit.json').write_text(json.dumps({'method':'direct frozen PTX text edit','original_sha256':hashlib.sha256(orig.encode()).hexdigest(),'edited_sha256':hashlib.sha256(s.encode()).hexdigest(),'domain':domain,'strict_proof_accepted':False,'full_upstream_runtime_verified':False},indent=2)+'\n')
