import Ptx.Auto.OssInc
namespace E5rSpec
open Ptx Ptx.Auto
namespace Original
def «_Z9incKernelPiS_ii» : Kernel where
  name := "_Z9incKernelPiS_ii"
  params := [("_Z9incKernelPiS_ii_param_0", .u64), ("_Z9incKernelPiS_ii_param_1", .u64), ("_Z9incKernelPiS_ii_param_2", .u32), ("_Z9incKernelPiS_ii_param_3", .u32)]
  regs := [⟨.pred, "%p", (some 8)⟩, ⟨.b32, "%r", (some 26)⟩, ⟨.b64, "%rd", (some 8)⟩]
  body := [
    /- 0 -/ ⟨none, .ld .param .u64 "%rd3" (.param "_Z9incKernelPiS_ii_param_0" 0)⟩,
    /- 1 -/ ⟨none, .ld .param .u64 "%rd4" (.param "_Z9incKernelPiS_ii_param_1" 0)⟩,
    /- 2 -/ ⟨none, .ld .param .u32 "%r9" (.param "_Z9incKernelPiS_ii_param_2" 0)⟩,
    /- 3 -/ ⟨none, .ld .param .u32 "%r8" (.param "_Z9incKernelPiS_ii_param_3" 0)⟩,
    /- 4 -/ ⟨none, .mov .u32 "%r10" (.sreg (.ctaid .x))⟩,
    /- 5 -/ ⟨none, .mov .u32 "%r11" (.sreg (.ntid .x))⟩,
    /- 6 -/ ⟨none, .mov .u32 "%r12" (.sreg (.tid .x))⟩,
    /- 7 -/ ⟨none, .madLo .s32 "%r1" (.reg "%r10") (.reg "%r11") (.reg "%r12")⟩,
    /- 8 -/ ⟨none, .setp .ge .s32 "%p1" (.reg "%r1") (.reg "%r9")⟩,
    /- 9 -/ ⟨none, .setp .lt .s32 "%p2" (.reg "%r8") (.imm 1)⟩,
    /- 10 -/ ⟨none, .por "%p3" "%p1" "%p2"⟩,
    /- 11 -/ ⟨(some ⟨"%p3", false⟩), .bra false "$L__BB0_6"⟩,
    /- 12 -/ ⟨none, .cvtaGlobal "%rd5" (.reg "%rd4")⟩,
    /- 13 -/ ⟨none, .mulWide .s32 "%rd6" (.reg "%r1") (.imm 4)⟩,
    /- 14 -/ ⟨none, .add .s64 "%rd1" (.reg "%rd5") (.reg "%rd6")⟩,
    /- 15 -/ ⟨none, .cvtaGlobal "%rd7" (.reg "%rd3")⟩,
    /- 16 -/ ⟨none, .add .s64 "%rd2" (.reg "%rd7") (.reg "%rd6")⟩,
    /- 17 -/ ⟨none, .and .b32 "%r25" (.reg "%r8") (.imm 3)⟩,
    /- 18 -/ ⟨none, .add .s32 "%r13" (.reg "%r8") (.imm (-1))⟩,
    /- 19 -/ ⟨none, .setp .lt .u32 "%p4" (.reg "%r13") (.imm 3)⟩,
    /- 20 -/ ⟨(some ⟨"%p4", false⟩), .bra false "$L__BB0_4"⟩,
    /- 21 -/ ⟨none, .sub .s32 "%r24" (.reg "%r8") (.reg "%r25")⟩,
    /- 22 -/ ⟨none, .ld .global .u32 "%r14" (.reg "%rd1" 0)⟩,
    /- 23 -/ ⟨none, .add .s32 "%r15" (.reg "%r14") (.imm 1)⟩,
    /- 24 -/ ⟨none, .st .global .u32 (.reg "%rd2" 0) (.reg "%r15")⟩,
    /- 25 -/ ⟨none, .ld .global .u32 "%r16" (.reg "%rd1" 0)⟩,
    /- 26 -/ ⟨none, .add .s32 "%r17" (.reg "%r16") (.imm 1)⟩,
    /- 27 -/ ⟨none, .st .global .u32 (.reg "%rd2" 0) (.reg "%r17")⟩,
    /- 28 -/ ⟨none, .ld .global .u32 "%r18" (.reg "%rd1" 0)⟩,
    /- 29 -/ ⟨none, .add .s32 "%r19" (.reg "%r18") (.imm 1)⟩,
    /- 30 -/ ⟨none, .st .global .u32 (.reg "%rd2" 0) (.reg "%r19")⟩,
    /- 31 -/ ⟨none, .ld .global .u32 "%r20" (.reg "%rd1" 0)⟩,
    /- 32 -/ ⟨none, .add .s32 "%r21" (.reg "%r20") (.imm 1)⟩,
    /- 33 -/ ⟨none, .st .global .u32 (.reg "%rd2" 0) (.reg "%r21")⟩,
    /- 34 -/ ⟨none, .add .s32 "%r24" (.reg "%r24") (.imm (-4))⟩,
    /- 35 -/ ⟨none, .setp .ne .s32 "%p5" (.reg "%r24") (.imm 0)⟩,
    /- 36 -/ ⟨(some ⟨"%p5", false⟩), .bra false "$L__BB0_3"⟩,
    /- 37 -/ ⟨none, .setp .eq .s32 "%p6" (.reg "%r25") (.imm 0)⟩,
    /- 38 -/ ⟨(some ⟨"%p6", false⟩), .bra false "$L__BB0_6"⟩,
    /- 39 -/ ⟨none, .ld .global .u32 "%r22" (.reg "%rd1" 0)⟩,
    /- 40 -/ ⟨none, .add .s32 "%r23" (.reg "%r22") (.imm 1)⟩,
    /- 41 -/ ⟨none, .st .global .u32 (.reg "%rd2" 0) (.reg "%r23")⟩,
    /- 42 -/ ⟨none, .add .s32 "%r25" (.reg "%r25") (.imm (-1))⟩,
    /- 43 -/ ⟨none, .setp .ne .s32 "%p7" (.reg "%r25") (.imm 0)⟩,
    /- 44 -/ ⟨(some ⟨"%p7", false⟩), .bra false "$L__BB0_5"⟩,
    /- 45 -/ ⟨none, .ret⟩]
  labels := [("$L__BB0_3", 22), ("$L__BB0_4", 37), ("$L__BB0_5", 39), ("$L__BB0_6", 45)]


end Original
namespace Optimized
def «_Z9incKernelPiS_ii» : Kernel where
  name := "_Z9incKernelPiS_ii"
  params := [("_Z9incKernelPiS_ii_param_0", .u64), ("_Z9incKernelPiS_ii_param_1", .u64), ("_Z9incKernelPiS_ii_param_2", .u32), ("_Z9incKernelPiS_ii_param_3", .u32)]
  regs := [⟨.pred, "%p", (some 8)⟩, ⟨.b32, "%r", (some 26)⟩, ⟨.b64, "%rd", (some 8)⟩]
  body := [
    /- 0 -/ ⟨none, .ld .param .u64 "%rd3" (.param "_Z9incKernelPiS_ii_param_0" 0)⟩,
    /- 1 -/ ⟨none, .ld .param .u64 "%rd4" (.param "_Z9incKernelPiS_ii_param_1" 0)⟩,
    /- 2 -/ ⟨none, .ld .param .u32 "%r9" (.param "_Z9incKernelPiS_ii_param_2" 0)⟩,
    /- 3 -/ ⟨none, .ld .param .u32 "%r8" (.param "_Z9incKernelPiS_ii_param_3" 0)⟩,
    /- 4 -/ ⟨none, .mov .u32 "%r10" (.sreg (.ctaid .x))⟩,
    /- 5 -/ ⟨none, .mov .u32 "%r11" (.sreg (.ntid .x))⟩,
    /- 6 -/ ⟨none, .mov .u32 "%r12" (.sreg (.tid .x))⟩,
    /- 7 -/ ⟨none, .madLo .s32 "%r1" (.reg "%r10") (.reg "%r11") (.reg "%r12")⟩,
    /- 8 -/ ⟨none, .setp .ge .s32 "%p1" (.reg "%r1") (.reg "%r9")⟩,
    /- 9 -/ ⟨none, .setp .lt .s32 "%p2" (.reg "%r8") (.imm 1)⟩,
    /- 10 -/ ⟨none, .por "%p3" "%p1" "%p2"⟩,
    /- 11 -/ ⟨(some ⟨"%p3", false⟩), .bra false "$L__BB0_6"⟩,
    /- 12 -/ ⟨none, .cvtaGlobal "%rd5" (.reg "%rd4")⟩,
    /- 13 -/ ⟨none, .mulWide .s32 "%rd6" (.reg "%r1") (.imm 4)⟩,
    /- 14 -/ ⟨none, .add .s64 "%rd1" (.reg "%rd5") (.reg "%rd6")⟩,
    /- 15 -/ ⟨none, .cvtaGlobal "%rd7" (.reg "%rd3")⟩,
    /- 16 -/ ⟨none, .add .s64 "%rd2" (.reg "%rd7") (.reg "%rd6")⟩,
    /- 17 -/ ⟨none, .ld .global .u32 "%r22" (.reg "%rd1" 0)⟩,
    /- 18 -/ ⟨none, .add .s32 "%r23" (.reg "%r22") (.imm 1)⟩,
    /- 19 -/ ⟨none, .st .global .u32 (.reg "%rd2" 0) (.reg "%r23")⟩,
    /- 20 -/ ⟨none, .ret⟩]
  labels := [("$L__BB0_6", 20)]


end Optimized
def domain : OssInc.Spec := ⟨"_Z9incKernelPiS_ii_param_1", "_Z9incKernelPiS_ii_param_0", "_Z9incKernelPiS_ii_param_2", "_Z9incKernelPiS_ii_param_3"⟩

/-- The theorem a supplied proof must prove, generated by `e5r ptx check`. -/
def statement : Prop := OssInc.Spec.Equivalent domain Original.«_Z9incKernelPiS_ii» Optimized.«_Z9incKernelPiS_ii»

end E5rSpec
