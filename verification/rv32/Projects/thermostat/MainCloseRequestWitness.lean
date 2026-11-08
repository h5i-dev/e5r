import Projects.thermostat.MainCloseRequestReset
import Projects.thermostat.MainRequestMethodWitness
set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 5000000
namespace E5R.Thermostat.MainCloseRequestWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board
def header (kind : Fin 4) : List (BitVec 8) :=
  if kind=0 then [71,69,84,32,47,115,116,97,116,101,63,113,32,72,84,84,80,47,49,46,49,13,10,72,111,115,116,58,120,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,48,13,10,13,10]
  else if kind=1 then [71,69,84,32,47,115,116,97,116,101,63,113,32,72,84,84,80,47,49,46,49,13,10,72,111,115,116,58,120,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,48,13,10,67,111,110,110,101,99,116,105,111,110,58,107,101,101,112,45,97,108,105,118,101,44,32,67,108,79,115,69,13,10,13,10]
  else if kind=2 then [71,69,84,32,47,115,116,97,116,101,63,113,32,72,84,84,80,47,49,46,49,13,10,72,111,115,116,58,120,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,48,13,10,99,79,110,78,101,67,116,73,111,78,58,100,105,115,99,108,111,115,101,44,32,99,108,111,115,101,120,13,10,13,10]
  else [71,69,84,32,47,115,116,97,116,101,63,113,32,72,84,84,80,47,49,46,49,13,10,72,111,115,116,58,120,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,48,13,10,67,111,110,110,101,99,116,105,111,110,58,107,101,101,112,45,97,108,105,118,101,13,10,67,79,78,78,69,67,84,73,79,78,58,9,99,108,111,115,101,9,13,10,13,10]
def expected (kind : Fin 4) : Head :=
  if kind=0 then ⟨(0,3),(4,12),1,[⟨23,27,28,29⟩,⟨31,45,46,47⟩],51,.length 0⟩
  else if kind=1 then ⟨(0,3),(4,12),1,[⟨23,27,28,29⟩,⟨31,45,46,47⟩,⟨49,59,60,77⟩],81,.length 0⟩
  else if kind=2 then ⟨(0,3),(4,12),1,[⟨23,27,28,29⟩,⟨31,45,46,47⟩,⟨49,59,60,76⟩],80,.length 0⟩
  else ⟨(0,3),(4,12),1,[⟨23,27,28,29⟩,⟨31,45,46,47⟩,⟨49,59,60,70⟩,⟨72,82,84,89⟩],94,.length 0⟩
def wire (kind : Fin 4) (k : Nat) : BitVec 8 := (header kind)[k]?.getD 0#8
def plan (kind : Fin 4) : ChunkReceivePlan.Plan :=
  ⟨fun _ => [0#32,2#32],fun _ => 129#32,fun k => BitVec.ofNat 32 (wire kind k).toNat⟩
def closes (kind : Fin 4) : Bool := decide (kind=1 ∨ kind=3)
theorem valid (kind : Fin 4) (first count : Nat) : ChunkReceivePlan.Valid (plan kind) (wire kind) first count := by
  intro k hk he
  refine ⟨?_,(by change MainChunkPoll.mask 129#32≠0#32;decide +kernel),MainChunkStreamingWitness.byte_roundtrip (wire kind k)⟩
  intro status hs
  change status∈[0#32,2#32] at hs
  have casesStatus : status=0#32 ∨ status=2#32 := by simpa using hs
  rcases casesStatus with zero|two <;> subst status <;> decide +kernel

theorem consumed0 : consume (wire 0) (header 0).length []=⟨(header 0).length,header 0,.done (expected 0)⟩ := by
  have run50 : consume (wire 0) 1 ((header 0).take 50)=⟨1,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 50++[wire 0 ((header 0).take 50).length]=(header 0).take 51 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 51) 1024 1024=.done (expected 0) := by decide +kernel
    rw [consume,nextByte,parsed]
    congr 1
  have run49 : consume (wire 0) 2 ((header 0).take 49)=⟨2,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 49++[wire 0 ((header 0).take 49).length]=(header 0).take 50 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 50) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run50]
  have run48 : consume (wire 0) 3 ((header 0).take 48)=⟨3,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 48++[wire 0 ((header 0).take 48).length]=(header 0).take 49 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 49) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run49]
  have run47 : consume (wire 0) 4 ((header 0).take 47)=⟨4,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 47++[wire 0 ((header 0).take 47).length]=(header 0).take 48 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 48) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run48]
  have run46 : consume (wire 0) 5 ((header 0).take 46)=⟨5,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 46++[wire 0 ((header 0).take 46).length]=(header 0).take 47 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 47) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run47]
  have run45 : consume (wire 0) 6 ((header 0).take 45)=⟨6,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 45++[wire 0 ((header 0).take 45).length]=(header 0).take 46 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 46) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run46]
  have run44 : consume (wire 0) 7 ((header 0).take 44)=⟨7,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 44++[wire 0 ((header 0).take 44).length]=(header 0).take 45 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 45) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run45]
  have run43 : consume (wire 0) 8 ((header 0).take 43)=⟨8,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 43++[wire 0 ((header 0).take 43).length]=(header 0).take 44 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 44) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run44]
  have run42 : consume (wire 0) 9 ((header 0).take 42)=⟨9,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 42++[wire 0 ((header 0).take 42).length]=(header 0).take 43 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 43) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run43]
  have run41 : consume (wire 0) 10 ((header 0).take 41)=⟨10,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 41++[wire 0 ((header 0).take 41).length]=(header 0).take 42 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 42) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run42]
  have run40 : consume (wire 0) 11 ((header 0).take 40)=⟨11,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 40++[wire 0 ((header 0).take 40).length]=(header 0).take 41 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 41) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run41]
  have run39 : consume (wire 0) 12 ((header 0).take 39)=⟨12,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 39++[wire 0 ((header 0).take 39).length]=(header 0).take 40 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 40) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run40]
  have run38 : consume (wire 0) 13 ((header 0).take 38)=⟨13,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 38++[wire 0 ((header 0).take 38).length]=(header 0).take 39 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 39) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run39]
  have run37 : consume (wire 0) 14 ((header 0).take 37)=⟨14,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 37++[wire 0 ((header 0).take 37).length]=(header 0).take 38 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 38) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run38]
  have run36 : consume (wire 0) 15 ((header 0).take 36)=⟨15,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 36++[wire 0 ((header 0).take 36).length]=(header 0).take 37 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 37) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run37]
  have run35 : consume (wire 0) 16 ((header 0).take 35)=⟨16,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 35++[wire 0 ((header 0).take 35).length]=(header 0).take 36 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 36) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run36]
  have run34 : consume (wire 0) 17 ((header 0).take 34)=⟨17,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 34++[wire 0 ((header 0).take 34).length]=(header 0).take 35 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 35) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run35]
  have run33 : consume (wire 0) 18 ((header 0).take 33)=⟨18,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 33++[wire 0 ((header 0).take 33).length]=(header 0).take 34 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 34) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run34]
  have run32 : consume (wire 0) 19 ((header 0).take 32)=⟨19,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 32++[wire 0 ((header 0).take 32).length]=(header 0).take 33 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 33) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run33]
  have run31 : consume (wire 0) 20 ((header 0).take 31)=⟨20,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 31++[wire 0 ((header 0).take 31).length]=(header 0).take 32 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 32) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run32]
  have run30 : consume (wire 0) 21 ((header 0).take 30)=⟨21,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 30++[wire 0 ((header 0).take 30).length]=(header 0).take 31 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 31) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run31]
  have run29 : consume (wire 0) 22 ((header 0).take 29)=⟨22,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 29++[wire 0 ((header 0).take 29).length]=(header 0).take 30 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 30) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run30]
  have run28 : consume (wire 0) 23 ((header 0).take 28)=⟨23,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 28++[wire 0 ((header 0).take 28).length]=(header 0).take 29 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 29) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run29]
  have run27 : consume (wire 0) 24 ((header 0).take 27)=⟨24,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 27++[wire 0 ((header 0).take 27).length]=(header 0).take 28 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 28) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run28]
  have run26 : consume (wire 0) 25 ((header 0).take 26)=⟨25,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 26++[wire 0 ((header 0).take 26).length]=(header 0).take 27 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 27) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run27]
  have run25 : consume (wire 0) 26 ((header 0).take 25)=⟨26,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 25++[wire 0 ((header 0).take 25).length]=(header 0).take 26 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 26) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run26]
  have run24 : consume (wire 0) 27 ((header 0).take 24)=⟨27,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 24++[wire 0 ((header 0).take 24).length]=(header 0).take 25 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 25) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run25]
  have run23 : consume (wire 0) 28 ((header 0).take 23)=⟨28,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 23++[wire 0 ((header 0).take 23).length]=(header 0).take 24 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 24) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run24]
  have run22 : consume (wire 0) 29 ((header 0).take 22)=⟨29,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 22++[wire 0 ((header 0).take 22).length]=(header 0).take 23 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 23) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run23]
  have run21 : consume (wire 0) 30 ((header 0).take 21)=⟨30,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 21++[wire 0 ((header 0).take 21).length]=(header 0).take 22 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 22) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run22]
  have run20 : consume (wire 0) 31 ((header 0).take 20)=⟨31,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 20++[wire 0 ((header 0).take 20).length]=(header 0).take 21 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 21) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run21]
  have run19 : consume (wire 0) 32 ((header 0).take 19)=⟨32,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 19++[wire 0 ((header 0).take 19).length]=(header 0).take 20 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 20) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run20]
  have run18 : consume (wire 0) 33 ((header 0).take 18)=⟨33,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 18++[wire 0 ((header 0).take 18).length]=(header 0).take 19 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 19) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run19]
  have run17 : consume (wire 0) 34 ((header 0).take 17)=⟨34,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 17++[wire 0 ((header 0).take 17).length]=(header 0).take 18 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 18) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run18]
  have run16 : consume (wire 0) 35 ((header 0).take 16)=⟨35,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 16++[wire 0 ((header 0).take 16).length]=(header 0).take 17 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 17) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run17]
  have run15 : consume (wire 0) 36 ((header 0).take 15)=⟨36,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 15++[wire 0 ((header 0).take 15).length]=(header 0).take 16 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 16) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run16]
  have run14 : consume (wire 0) 37 ((header 0).take 14)=⟨37,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 14++[wire 0 ((header 0).take 14).length]=(header 0).take 15 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 15) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run15]
  have run13 : consume (wire 0) 38 ((header 0).take 13)=⟨38,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 13++[wire 0 ((header 0).take 13).length]=(header 0).take 14 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 14) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run14]
  have run12 : consume (wire 0) 39 ((header 0).take 12)=⟨39,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 12++[wire 0 ((header 0).take 12).length]=(header 0).take 13 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 13) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run13]
  have run11 : consume (wire 0) 40 ((header 0).take 11)=⟨40,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 11++[wire 0 ((header 0).take 11).length]=(header 0).take 12 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 12) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run12]
  have run10 : consume (wire 0) 41 ((header 0).take 10)=⟨41,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 10++[wire 0 ((header 0).take 10).length]=(header 0).take 11 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 11) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run11]
  have run9 : consume (wire 0) 42 ((header 0).take 9)=⟨42,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 9++[wire 0 ((header 0).take 9).length]=(header 0).take 10 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 10) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run10]
  have run8 : consume (wire 0) 43 ((header 0).take 8)=⟨43,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 8++[wire 0 ((header 0).take 8).length]=(header 0).take 9 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 9) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run9]
  have run7 : consume (wire 0) 44 ((header 0).take 7)=⟨44,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 7++[wire 0 ((header 0).take 7).length]=(header 0).take 8 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 8) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run8]
  have run6 : consume (wire 0) 45 ((header 0).take 6)=⟨45,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 6++[wire 0 ((header 0).take 6).length]=(header 0).take 7 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 7) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run7]
  have run5 : consume (wire 0) 46 ((header 0).take 5)=⟨46,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 5++[wire 0 ((header 0).take 5).length]=(header 0).take 6 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 6) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run6]
  have run4 : consume (wire 0) 47 ((header 0).take 4)=⟨47,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 4++[wire 0 ((header 0).take 4).length]=(header 0).take 5 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 5) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run5]
  have run3 : consume (wire 0) 48 ((header 0).take 3)=⟨48,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 3++[wire 0 ((header 0).take 3).length]=(header 0).take 4 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 4) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run4]
  have run2 : consume (wire 0) 49 ((header 0).take 2)=⟨49,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 2++[wire 0 ((header 0).take 2).length]=(header 0).take 3 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 3) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run3]
  have run1 : consume (wire 0) 50 ((header 0).take 1)=⟨50,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 1++[wire 0 ((header 0).take 1).length]=(header 0).take 2 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 2) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run2]
  have run0 : consume (wire 0) 51 ((header 0).take 0)=⟨51,header 0,.done (expected 0)⟩ := by
    have nextByte : (header 0).take 0++[wire 0 ((header 0).take 0).length]=(header 0).take 1 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 0).take 1) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run1]
  exact run0

theorem consumed1 : consume (wire 1) (header 1).length []=⟨(header 1).length,header 1,.done (expected 1)⟩ := by
  have run80 : consume (wire 1) 1 ((header 1).take 80)=⟨1,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 80++[wire 1 ((header 1).take 80).length]=(header 1).take 81 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 81) 1024 1024=.done (expected 1) := by decide +kernel
    rw [consume,nextByte,parsed]
    congr 1
  have run79 : consume (wire 1) 2 ((header 1).take 79)=⟨2,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 79++[wire 1 ((header 1).take 79).length]=(header 1).take 80 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 80) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run80]
  have run78 : consume (wire 1) 3 ((header 1).take 78)=⟨3,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 78++[wire 1 ((header 1).take 78).length]=(header 1).take 79 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 79) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run79]
  have run77 : consume (wire 1) 4 ((header 1).take 77)=⟨4,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 77++[wire 1 ((header 1).take 77).length]=(header 1).take 78 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 78) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run78]
  have run76 : consume (wire 1) 5 ((header 1).take 76)=⟨5,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 76++[wire 1 ((header 1).take 76).length]=(header 1).take 77 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 77) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run77]
  have run75 : consume (wire 1) 6 ((header 1).take 75)=⟨6,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 75++[wire 1 ((header 1).take 75).length]=(header 1).take 76 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 76) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run76]
  have run74 : consume (wire 1) 7 ((header 1).take 74)=⟨7,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 74++[wire 1 ((header 1).take 74).length]=(header 1).take 75 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 75) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run75]
  have run73 : consume (wire 1) 8 ((header 1).take 73)=⟨8,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 73++[wire 1 ((header 1).take 73).length]=(header 1).take 74 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 74) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run74]
  have run72 : consume (wire 1) 9 ((header 1).take 72)=⟨9,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 72++[wire 1 ((header 1).take 72).length]=(header 1).take 73 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 73) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run73]
  have run71 : consume (wire 1) 10 ((header 1).take 71)=⟨10,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 71++[wire 1 ((header 1).take 71).length]=(header 1).take 72 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 72) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run72]
  have run70 : consume (wire 1) 11 ((header 1).take 70)=⟨11,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 70++[wire 1 ((header 1).take 70).length]=(header 1).take 71 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 71) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run71]
  have run69 : consume (wire 1) 12 ((header 1).take 69)=⟨12,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 69++[wire 1 ((header 1).take 69).length]=(header 1).take 70 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 70) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run70]
  have run68 : consume (wire 1) 13 ((header 1).take 68)=⟨13,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 68++[wire 1 ((header 1).take 68).length]=(header 1).take 69 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 69) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run69]
  have run67 : consume (wire 1) 14 ((header 1).take 67)=⟨14,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 67++[wire 1 ((header 1).take 67).length]=(header 1).take 68 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 68) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run68]
  have run66 : consume (wire 1) 15 ((header 1).take 66)=⟨15,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 66++[wire 1 ((header 1).take 66).length]=(header 1).take 67 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 67) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run67]
  have run65 : consume (wire 1) 16 ((header 1).take 65)=⟨16,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 65++[wire 1 ((header 1).take 65).length]=(header 1).take 66 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 66) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run66]
  have run64 : consume (wire 1) 17 ((header 1).take 64)=⟨17,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 64++[wire 1 ((header 1).take 64).length]=(header 1).take 65 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 65) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run65]
  have run63 : consume (wire 1) 18 ((header 1).take 63)=⟨18,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 63++[wire 1 ((header 1).take 63).length]=(header 1).take 64 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 64) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run64]
  have run62 : consume (wire 1) 19 ((header 1).take 62)=⟨19,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 62++[wire 1 ((header 1).take 62).length]=(header 1).take 63 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 63) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run63]
  have run61 : consume (wire 1) 20 ((header 1).take 61)=⟨20,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 61++[wire 1 ((header 1).take 61).length]=(header 1).take 62 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 62) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run62]
  have run60 : consume (wire 1) 21 ((header 1).take 60)=⟨21,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 60++[wire 1 ((header 1).take 60).length]=(header 1).take 61 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 61) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run61]
  have run59 : consume (wire 1) 22 ((header 1).take 59)=⟨22,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 59++[wire 1 ((header 1).take 59).length]=(header 1).take 60 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 60) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run60]
  have run58 : consume (wire 1) 23 ((header 1).take 58)=⟨23,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 58++[wire 1 ((header 1).take 58).length]=(header 1).take 59 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 59) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run59]
  have run57 : consume (wire 1) 24 ((header 1).take 57)=⟨24,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 57++[wire 1 ((header 1).take 57).length]=(header 1).take 58 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 58) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run58]
  have run56 : consume (wire 1) 25 ((header 1).take 56)=⟨25,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 56++[wire 1 ((header 1).take 56).length]=(header 1).take 57 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 57) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run57]
  have run55 : consume (wire 1) 26 ((header 1).take 55)=⟨26,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 55++[wire 1 ((header 1).take 55).length]=(header 1).take 56 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 56) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run56]
  have run54 : consume (wire 1) 27 ((header 1).take 54)=⟨27,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 54++[wire 1 ((header 1).take 54).length]=(header 1).take 55 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 55) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run55]
  have run53 : consume (wire 1) 28 ((header 1).take 53)=⟨28,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 53++[wire 1 ((header 1).take 53).length]=(header 1).take 54 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 54) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run54]
  have run52 : consume (wire 1) 29 ((header 1).take 52)=⟨29,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 52++[wire 1 ((header 1).take 52).length]=(header 1).take 53 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 53) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run53]
  have run51 : consume (wire 1) 30 ((header 1).take 51)=⟨30,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 51++[wire 1 ((header 1).take 51).length]=(header 1).take 52 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 52) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run52]
  have run50 : consume (wire 1) 31 ((header 1).take 50)=⟨31,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 50++[wire 1 ((header 1).take 50).length]=(header 1).take 51 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 51) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run51]
  have run49 : consume (wire 1) 32 ((header 1).take 49)=⟨32,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 49++[wire 1 ((header 1).take 49).length]=(header 1).take 50 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 50) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run50]
  have run48 : consume (wire 1) 33 ((header 1).take 48)=⟨33,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 48++[wire 1 ((header 1).take 48).length]=(header 1).take 49 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 49) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run49]
  have run47 : consume (wire 1) 34 ((header 1).take 47)=⟨34,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 47++[wire 1 ((header 1).take 47).length]=(header 1).take 48 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 48) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run48]
  have run46 : consume (wire 1) 35 ((header 1).take 46)=⟨35,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 46++[wire 1 ((header 1).take 46).length]=(header 1).take 47 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 47) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run47]
  have run45 : consume (wire 1) 36 ((header 1).take 45)=⟨36,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 45++[wire 1 ((header 1).take 45).length]=(header 1).take 46 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 46) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run46]
  have run44 : consume (wire 1) 37 ((header 1).take 44)=⟨37,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 44++[wire 1 ((header 1).take 44).length]=(header 1).take 45 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 45) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run45]
  have run43 : consume (wire 1) 38 ((header 1).take 43)=⟨38,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 43++[wire 1 ((header 1).take 43).length]=(header 1).take 44 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 44) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run44]
  have run42 : consume (wire 1) 39 ((header 1).take 42)=⟨39,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 42++[wire 1 ((header 1).take 42).length]=(header 1).take 43 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 43) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run43]
  have run41 : consume (wire 1) 40 ((header 1).take 41)=⟨40,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 41++[wire 1 ((header 1).take 41).length]=(header 1).take 42 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 42) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run42]
  have run40 : consume (wire 1) 41 ((header 1).take 40)=⟨41,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 40++[wire 1 ((header 1).take 40).length]=(header 1).take 41 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 41) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run41]
  have run39 : consume (wire 1) 42 ((header 1).take 39)=⟨42,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 39++[wire 1 ((header 1).take 39).length]=(header 1).take 40 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 40) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run40]
  have run38 : consume (wire 1) 43 ((header 1).take 38)=⟨43,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 38++[wire 1 ((header 1).take 38).length]=(header 1).take 39 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 39) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run39]
  have run37 : consume (wire 1) 44 ((header 1).take 37)=⟨44,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 37++[wire 1 ((header 1).take 37).length]=(header 1).take 38 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 38) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run38]
  have run36 : consume (wire 1) 45 ((header 1).take 36)=⟨45,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 36++[wire 1 ((header 1).take 36).length]=(header 1).take 37 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 37) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run37]
  have run35 : consume (wire 1) 46 ((header 1).take 35)=⟨46,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 35++[wire 1 ((header 1).take 35).length]=(header 1).take 36 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 36) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run36]
  have run34 : consume (wire 1) 47 ((header 1).take 34)=⟨47,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 34++[wire 1 ((header 1).take 34).length]=(header 1).take 35 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 35) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run35]
  have run33 : consume (wire 1) 48 ((header 1).take 33)=⟨48,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 33++[wire 1 ((header 1).take 33).length]=(header 1).take 34 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 34) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run34]
  have run32 : consume (wire 1) 49 ((header 1).take 32)=⟨49,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 32++[wire 1 ((header 1).take 32).length]=(header 1).take 33 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 33) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run33]
  have run31 : consume (wire 1) 50 ((header 1).take 31)=⟨50,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 31++[wire 1 ((header 1).take 31).length]=(header 1).take 32 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 32) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run32]
  have run30 : consume (wire 1) 51 ((header 1).take 30)=⟨51,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 30++[wire 1 ((header 1).take 30).length]=(header 1).take 31 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 31) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run31]
  have run29 : consume (wire 1) 52 ((header 1).take 29)=⟨52,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 29++[wire 1 ((header 1).take 29).length]=(header 1).take 30 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 30) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run30]
  have run28 : consume (wire 1) 53 ((header 1).take 28)=⟨53,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 28++[wire 1 ((header 1).take 28).length]=(header 1).take 29 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 29) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run29]
  have run27 : consume (wire 1) 54 ((header 1).take 27)=⟨54,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 27++[wire 1 ((header 1).take 27).length]=(header 1).take 28 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 28) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run28]
  have run26 : consume (wire 1) 55 ((header 1).take 26)=⟨55,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 26++[wire 1 ((header 1).take 26).length]=(header 1).take 27 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 27) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run27]
  have run25 : consume (wire 1) 56 ((header 1).take 25)=⟨56,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 25++[wire 1 ((header 1).take 25).length]=(header 1).take 26 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 26) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run26]
  have run24 : consume (wire 1) 57 ((header 1).take 24)=⟨57,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 24++[wire 1 ((header 1).take 24).length]=(header 1).take 25 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 25) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run25]
  have run23 : consume (wire 1) 58 ((header 1).take 23)=⟨58,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 23++[wire 1 ((header 1).take 23).length]=(header 1).take 24 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 24) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run24]
  have run22 : consume (wire 1) 59 ((header 1).take 22)=⟨59,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 22++[wire 1 ((header 1).take 22).length]=(header 1).take 23 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 23) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run23]
  have run21 : consume (wire 1) 60 ((header 1).take 21)=⟨60,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 21++[wire 1 ((header 1).take 21).length]=(header 1).take 22 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 22) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run22]
  have run20 : consume (wire 1) 61 ((header 1).take 20)=⟨61,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 20++[wire 1 ((header 1).take 20).length]=(header 1).take 21 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 21) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run21]
  have run19 : consume (wire 1) 62 ((header 1).take 19)=⟨62,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 19++[wire 1 ((header 1).take 19).length]=(header 1).take 20 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 20) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run20]
  have run18 : consume (wire 1) 63 ((header 1).take 18)=⟨63,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 18++[wire 1 ((header 1).take 18).length]=(header 1).take 19 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 19) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run19]
  have run17 : consume (wire 1) 64 ((header 1).take 17)=⟨64,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 17++[wire 1 ((header 1).take 17).length]=(header 1).take 18 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 18) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run18]
  have run16 : consume (wire 1) 65 ((header 1).take 16)=⟨65,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 16++[wire 1 ((header 1).take 16).length]=(header 1).take 17 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 17) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run17]
  have run15 : consume (wire 1) 66 ((header 1).take 15)=⟨66,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 15++[wire 1 ((header 1).take 15).length]=(header 1).take 16 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 16) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run16]
  have run14 : consume (wire 1) 67 ((header 1).take 14)=⟨67,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 14++[wire 1 ((header 1).take 14).length]=(header 1).take 15 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 15) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run15]
  have run13 : consume (wire 1) 68 ((header 1).take 13)=⟨68,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 13++[wire 1 ((header 1).take 13).length]=(header 1).take 14 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 14) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run14]
  have run12 : consume (wire 1) 69 ((header 1).take 12)=⟨69,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 12++[wire 1 ((header 1).take 12).length]=(header 1).take 13 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 13) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run13]
  have run11 : consume (wire 1) 70 ((header 1).take 11)=⟨70,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 11++[wire 1 ((header 1).take 11).length]=(header 1).take 12 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 12) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run12]
  have run10 : consume (wire 1) 71 ((header 1).take 10)=⟨71,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 10++[wire 1 ((header 1).take 10).length]=(header 1).take 11 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 11) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run11]
  have run9 : consume (wire 1) 72 ((header 1).take 9)=⟨72,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 9++[wire 1 ((header 1).take 9).length]=(header 1).take 10 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 10) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run10]
  have run8 : consume (wire 1) 73 ((header 1).take 8)=⟨73,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 8++[wire 1 ((header 1).take 8).length]=(header 1).take 9 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 9) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run9]
  have run7 : consume (wire 1) 74 ((header 1).take 7)=⟨74,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 7++[wire 1 ((header 1).take 7).length]=(header 1).take 8 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 8) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run8]
  have run6 : consume (wire 1) 75 ((header 1).take 6)=⟨75,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 6++[wire 1 ((header 1).take 6).length]=(header 1).take 7 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 7) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run7]
  have run5 : consume (wire 1) 76 ((header 1).take 5)=⟨76,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 5++[wire 1 ((header 1).take 5).length]=(header 1).take 6 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 6) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run6]
  have run4 : consume (wire 1) 77 ((header 1).take 4)=⟨77,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 4++[wire 1 ((header 1).take 4).length]=(header 1).take 5 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 5) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run5]
  have run3 : consume (wire 1) 78 ((header 1).take 3)=⟨78,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 3++[wire 1 ((header 1).take 3).length]=(header 1).take 4 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 4) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run4]
  have run2 : consume (wire 1) 79 ((header 1).take 2)=⟨79,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 2++[wire 1 ((header 1).take 2).length]=(header 1).take 3 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 3) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run3]
  have run1 : consume (wire 1) 80 ((header 1).take 1)=⟨80,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 1++[wire 1 ((header 1).take 1).length]=(header 1).take 2 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 2) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run2]
  have run0 : consume (wire 1) 81 ((header 1).take 0)=⟨81,header 1,.done (expected 1)⟩ := by
    have nextByte : (header 1).take 0++[wire 1 ((header 1).take 0).length]=(header 1).take 1 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 1).take 1) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run1]
  exact run0

theorem consumed2 : consume (wire 2) (header 2).length []=⟨(header 2).length,header 2,.done (expected 2)⟩ := by
  have run79 : consume (wire 2) 1 ((header 2).take 79)=⟨1,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 79++[wire 2 ((header 2).take 79).length]=(header 2).take 80 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 80) 1024 1024=.done (expected 2) := by decide +kernel
    rw [consume,nextByte,parsed]
    congr 1
  have run78 : consume (wire 2) 2 ((header 2).take 78)=⟨2,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 78++[wire 2 ((header 2).take 78).length]=(header 2).take 79 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 79) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run79]
  have run77 : consume (wire 2) 3 ((header 2).take 77)=⟨3,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 77++[wire 2 ((header 2).take 77).length]=(header 2).take 78 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 78) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run78]
  have run76 : consume (wire 2) 4 ((header 2).take 76)=⟨4,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 76++[wire 2 ((header 2).take 76).length]=(header 2).take 77 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 77) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run77]
  have run75 : consume (wire 2) 5 ((header 2).take 75)=⟨5,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 75++[wire 2 ((header 2).take 75).length]=(header 2).take 76 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 76) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run76]
  have run74 : consume (wire 2) 6 ((header 2).take 74)=⟨6,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 74++[wire 2 ((header 2).take 74).length]=(header 2).take 75 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 75) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run75]
  have run73 : consume (wire 2) 7 ((header 2).take 73)=⟨7,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 73++[wire 2 ((header 2).take 73).length]=(header 2).take 74 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 74) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run74]
  have run72 : consume (wire 2) 8 ((header 2).take 72)=⟨8,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 72++[wire 2 ((header 2).take 72).length]=(header 2).take 73 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 73) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run73]
  have run71 : consume (wire 2) 9 ((header 2).take 71)=⟨9,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 71++[wire 2 ((header 2).take 71).length]=(header 2).take 72 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 72) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run72]
  have run70 : consume (wire 2) 10 ((header 2).take 70)=⟨10,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 70++[wire 2 ((header 2).take 70).length]=(header 2).take 71 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 71) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run71]
  have run69 : consume (wire 2) 11 ((header 2).take 69)=⟨11,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 69++[wire 2 ((header 2).take 69).length]=(header 2).take 70 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 70) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run70]
  have run68 : consume (wire 2) 12 ((header 2).take 68)=⟨12,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 68++[wire 2 ((header 2).take 68).length]=(header 2).take 69 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 69) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run69]
  have run67 : consume (wire 2) 13 ((header 2).take 67)=⟨13,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 67++[wire 2 ((header 2).take 67).length]=(header 2).take 68 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 68) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run68]
  have run66 : consume (wire 2) 14 ((header 2).take 66)=⟨14,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 66++[wire 2 ((header 2).take 66).length]=(header 2).take 67 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 67) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run67]
  have run65 : consume (wire 2) 15 ((header 2).take 65)=⟨15,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 65++[wire 2 ((header 2).take 65).length]=(header 2).take 66 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 66) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run66]
  have run64 : consume (wire 2) 16 ((header 2).take 64)=⟨16,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 64++[wire 2 ((header 2).take 64).length]=(header 2).take 65 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 65) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run65]
  have run63 : consume (wire 2) 17 ((header 2).take 63)=⟨17,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 63++[wire 2 ((header 2).take 63).length]=(header 2).take 64 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 64) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run64]
  have run62 : consume (wire 2) 18 ((header 2).take 62)=⟨18,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 62++[wire 2 ((header 2).take 62).length]=(header 2).take 63 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 63) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run63]
  have run61 : consume (wire 2) 19 ((header 2).take 61)=⟨19,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 61++[wire 2 ((header 2).take 61).length]=(header 2).take 62 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 62) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run62]
  have run60 : consume (wire 2) 20 ((header 2).take 60)=⟨20,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 60++[wire 2 ((header 2).take 60).length]=(header 2).take 61 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 61) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run61]
  have run59 : consume (wire 2) 21 ((header 2).take 59)=⟨21,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 59++[wire 2 ((header 2).take 59).length]=(header 2).take 60 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 60) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run60]
  have run58 : consume (wire 2) 22 ((header 2).take 58)=⟨22,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 58++[wire 2 ((header 2).take 58).length]=(header 2).take 59 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 59) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run59]
  have run57 : consume (wire 2) 23 ((header 2).take 57)=⟨23,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 57++[wire 2 ((header 2).take 57).length]=(header 2).take 58 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 58) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run58]
  have run56 : consume (wire 2) 24 ((header 2).take 56)=⟨24,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 56++[wire 2 ((header 2).take 56).length]=(header 2).take 57 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 57) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run57]
  have run55 : consume (wire 2) 25 ((header 2).take 55)=⟨25,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 55++[wire 2 ((header 2).take 55).length]=(header 2).take 56 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 56) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run56]
  have run54 : consume (wire 2) 26 ((header 2).take 54)=⟨26,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 54++[wire 2 ((header 2).take 54).length]=(header 2).take 55 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 55) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run55]
  have run53 : consume (wire 2) 27 ((header 2).take 53)=⟨27,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 53++[wire 2 ((header 2).take 53).length]=(header 2).take 54 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 54) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run54]
  have run52 : consume (wire 2) 28 ((header 2).take 52)=⟨28,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 52++[wire 2 ((header 2).take 52).length]=(header 2).take 53 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 53) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run53]
  have run51 : consume (wire 2) 29 ((header 2).take 51)=⟨29,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 51++[wire 2 ((header 2).take 51).length]=(header 2).take 52 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 52) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run52]
  have run50 : consume (wire 2) 30 ((header 2).take 50)=⟨30,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 50++[wire 2 ((header 2).take 50).length]=(header 2).take 51 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 51) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run51]
  have run49 : consume (wire 2) 31 ((header 2).take 49)=⟨31,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 49++[wire 2 ((header 2).take 49).length]=(header 2).take 50 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 50) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run50]
  have run48 : consume (wire 2) 32 ((header 2).take 48)=⟨32,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 48++[wire 2 ((header 2).take 48).length]=(header 2).take 49 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 49) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run49]
  have run47 : consume (wire 2) 33 ((header 2).take 47)=⟨33,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 47++[wire 2 ((header 2).take 47).length]=(header 2).take 48 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 48) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run48]
  have run46 : consume (wire 2) 34 ((header 2).take 46)=⟨34,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 46++[wire 2 ((header 2).take 46).length]=(header 2).take 47 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 47) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run47]
  have run45 : consume (wire 2) 35 ((header 2).take 45)=⟨35,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 45++[wire 2 ((header 2).take 45).length]=(header 2).take 46 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 46) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run46]
  have run44 : consume (wire 2) 36 ((header 2).take 44)=⟨36,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 44++[wire 2 ((header 2).take 44).length]=(header 2).take 45 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 45) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run45]
  have run43 : consume (wire 2) 37 ((header 2).take 43)=⟨37,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 43++[wire 2 ((header 2).take 43).length]=(header 2).take 44 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 44) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run44]
  have run42 : consume (wire 2) 38 ((header 2).take 42)=⟨38,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 42++[wire 2 ((header 2).take 42).length]=(header 2).take 43 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 43) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run43]
  have run41 : consume (wire 2) 39 ((header 2).take 41)=⟨39,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 41++[wire 2 ((header 2).take 41).length]=(header 2).take 42 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 42) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run42]
  have run40 : consume (wire 2) 40 ((header 2).take 40)=⟨40,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 40++[wire 2 ((header 2).take 40).length]=(header 2).take 41 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 41) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run41]
  have run39 : consume (wire 2) 41 ((header 2).take 39)=⟨41,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 39++[wire 2 ((header 2).take 39).length]=(header 2).take 40 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 40) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run40]
  have run38 : consume (wire 2) 42 ((header 2).take 38)=⟨42,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 38++[wire 2 ((header 2).take 38).length]=(header 2).take 39 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 39) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run39]
  have run37 : consume (wire 2) 43 ((header 2).take 37)=⟨43,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 37++[wire 2 ((header 2).take 37).length]=(header 2).take 38 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 38) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run38]
  have run36 : consume (wire 2) 44 ((header 2).take 36)=⟨44,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 36++[wire 2 ((header 2).take 36).length]=(header 2).take 37 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 37) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run37]
  have run35 : consume (wire 2) 45 ((header 2).take 35)=⟨45,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 35++[wire 2 ((header 2).take 35).length]=(header 2).take 36 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 36) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run36]
  have run34 : consume (wire 2) 46 ((header 2).take 34)=⟨46,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 34++[wire 2 ((header 2).take 34).length]=(header 2).take 35 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 35) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run35]
  have run33 : consume (wire 2) 47 ((header 2).take 33)=⟨47,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 33++[wire 2 ((header 2).take 33).length]=(header 2).take 34 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 34) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run34]
  have run32 : consume (wire 2) 48 ((header 2).take 32)=⟨48,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 32++[wire 2 ((header 2).take 32).length]=(header 2).take 33 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 33) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run33]
  have run31 : consume (wire 2) 49 ((header 2).take 31)=⟨49,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 31++[wire 2 ((header 2).take 31).length]=(header 2).take 32 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 32) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run32]
  have run30 : consume (wire 2) 50 ((header 2).take 30)=⟨50,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 30++[wire 2 ((header 2).take 30).length]=(header 2).take 31 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 31) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run31]
  have run29 : consume (wire 2) 51 ((header 2).take 29)=⟨51,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 29++[wire 2 ((header 2).take 29).length]=(header 2).take 30 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 30) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run30]
  have run28 : consume (wire 2) 52 ((header 2).take 28)=⟨52,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 28++[wire 2 ((header 2).take 28).length]=(header 2).take 29 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 29) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run29]
  have run27 : consume (wire 2) 53 ((header 2).take 27)=⟨53,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 27++[wire 2 ((header 2).take 27).length]=(header 2).take 28 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 28) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run28]
  have run26 : consume (wire 2) 54 ((header 2).take 26)=⟨54,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 26++[wire 2 ((header 2).take 26).length]=(header 2).take 27 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 27) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run27]
  have run25 : consume (wire 2) 55 ((header 2).take 25)=⟨55,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 25++[wire 2 ((header 2).take 25).length]=(header 2).take 26 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 26) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run26]
  have run24 : consume (wire 2) 56 ((header 2).take 24)=⟨56,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 24++[wire 2 ((header 2).take 24).length]=(header 2).take 25 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 25) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run25]
  have run23 : consume (wire 2) 57 ((header 2).take 23)=⟨57,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 23++[wire 2 ((header 2).take 23).length]=(header 2).take 24 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 24) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run24]
  have run22 : consume (wire 2) 58 ((header 2).take 22)=⟨58,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 22++[wire 2 ((header 2).take 22).length]=(header 2).take 23 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 23) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run23]
  have run21 : consume (wire 2) 59 ((header 2).take 21)=⟨59,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 21++[wire 2 ((header 2).take 21).length]=(header 2).take 22 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 22) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run22]
  have run20 : consume (wire 2) 60 ((header 2).take 20)=⟨60,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 20++[wire 2 ((header 2).take 20).length]=(header 2).take 21 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 21) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run21]
  have run19 : consume (wire 2) 61 ((header 2).take 19)=⟨61,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 19++[wire 2 ((header 2).take 19).length]=(header 2).take 20 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 20) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run20]
  have run18 : consume (wire 2) 62 ((header 2).take 18)=⟨62,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 18++[wire 2 ((header 2).take 18).length]=(header 2).take 19 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 19) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run19]
  have run17 : consume (wire 2) 63 ((header 2).take 17)=⟨63,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 17++[wire 2 ((header 2).take 17).length]=(header 2).take 18 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 18) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run18]
  have run16 : consume (wire 2) 64 ((header 2).take 16)=⟨64,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 16++[wire 2 ((header 2).take 16).length]=(header 2).take 17 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 17) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run17]
  have run15 : consume (wire 2) 65 ((header 2).take 15)=⟨65,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 15++[wire 2 ((header 2).take 15).length]=(header 2).take 16 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 16) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run16]
  have run14 : consume (wire 2) 66 ((header 2).take 14)=⟨66,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 14++[wire 2 ((header 2).take 14).length]=(header 2).take 15 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 15) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run15]
  have run13 : consume (wire 2) 67 ((header 2).take 13)=⟨67,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 13++[wire 2 ((header 2).take 13).length]=(header 2).take 14 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 14) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run14]
  have run12 : consume (wire 2) 68 ((header 2).take 12)=⟨68,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 12++[wire 2 ((header 2).take 12).length]=(header 2).take 13 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 13) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run13]
  have run11 : consume (wire 2) 69 ((header 2).take 11)=⟨69,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 11++[wire 2 ((header 2).take 11).length]=(header 2).take 12 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 12) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run12]
  have run10 : consume (wire 2) 70 ((header 2).take 10)=⟨70,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 10++[wire 2 ((header 2).take 10).length]=(header 2).take 11 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 11) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run11]
  have run9 : consume (wire 2) 71 ((header 2).take 9)=⟨71,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 9++[wire 2 ((header 2).take 9).length]=(header 2).take 10 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 10) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run10]
  have run8 : consume (wire 2) 72 ((header 2).take 8)=⟨72,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 8++[wire 2 ((header 2).take 8).length]=(header 2).take 9 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 9) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run9]
  have run7 : consume (wire 2) 73 ((header 2).take 7)=⟨73,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 7++[wire 2 ((header 2).take 7).length]=(header 2).take 8 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 8) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run8]
  have run6 : consume (wire 2) 74 ((header 2).take 6)=⟨74,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 6++[wire 2 ((header 2).take 6).length]=(header 2).take 7 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 7) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run7]
  have run5 : consume (wire 2) 75 ((header 2).take 5)=⟨75,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 5++[wire 2 ((header 2).take 5).length]=(header 2).take 6 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 6) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run6]
  have run4 : consume (wire 2) 76 ((header 2).take 4)=⟨76,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 4++[wire 2 ((header 2).take 4).length]=(header 2).take 5 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 5) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run5]
  have run3 : consume (wire 2) 77 ((header 2).take 3)=⟨77,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 3++[wire 2 ((header 2).take 3).length]=(header 2).take 4 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 4) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run4]
  have run2 : consume (wire 2) 78 ((header 2).take 2)=⟨78,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 2++[wire 2 ((header 2).take 2).length]=(header 2).take 3 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 3) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run3]
  have run1 : consume (wire 2) 79 ((header 2).take 1)=⟨79,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 1++[wire 2 ((header 2).take 1).length]=(header 2).take 2 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 2) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run2]
  have run0 : consume (wire 2) 80 ((header 2).take 0)=⟨80,header 2,.done (expected 2)⟩ := by
    have nextByte : (header 2).take 0++[wire 2 ((header 2).take 0).length]=(header 2).take 1 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 2).take 1) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run1]
  exact run0

theorem consumed3 : consume (wire 3) (header 3).length []=⟨(header 3).length,header 3,.done (expected 3)⟩ := by
  have run93 : consume (wire 3) 1 ((header 3).take 93)=⟨1,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 93++[wire 3 ((header 3).take 93).length]=(header 3).take 94 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 94) 1024 1024=.done (expected 3) := by decide +kernel
    rw [consume,nextByte,parsed]
    congr 1
  have run92 : consume (wire 3) 2 ((header 3).take 92)=⟨2,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 92++[wire 3 ((header 3).take 92).length]=(header 3).take 93 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 93) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run93]
  have run91 : consume (wire 3) 3 ((header 3).take 91)=⟨3,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 91++[wire 3 ((header 3).take 91).length]=(header 3).take 92 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 92) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run92]
  have run90 : consume (wire 3) 4 ((header 3).take 90)=⟨4,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 90++[wire 3 ((header 3).take 90).length]=(header 3).take 91 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 91) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run91]
  have run89 : consume (wire 3) 5 ((header 3).take 89)=⟨5,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 89++[wire 3 ((header 3).take 89).length]=(header 3).take 90 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 90) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run90]
  have run88 : consume (wire 3) 6 ((header 3).take 88)=⟨6,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 88++[wire 3 ((header 3).take 88).length]=(header 3).take 89 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 89) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run89]
  have run87 : consume (wire 3) 7 ((header 3).take 87)=⟨7,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 87++[wire 3 ((header 3).take 87).length]=(header 3).take 88 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 88) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run88]
  have run86 : consume (wire 3) 8 ((header 3).take 86)=⟨8,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 86++[wire 3 ((header 3).take 86).length]=(header 3).take 87 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 87) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run87]
  have run85 : consume (wire 3) 9 ((header 3).take 85)=⟨9,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 85++[wire 3 ((header 3).take 85).length]=(header 3).take 86 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 86) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run86]
  have run84 : consume (wire 3) 10 ((header 3).take 84)=⟨10,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 84++[wire 3 ((header 3).take 84).length]=(header 3).take 85 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 85) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run85]
  have run83 : consume (wire 3) 11 ((header 3).take 83)=⟨11,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 83++[wire 3 ((header 3).take 83).length]=(header 3).take 84 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 84) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run84]
  have run82 : consume (wire 3) 12 ((header 3).take 82)=⟨12,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 82++[wire 3 ((header 3).take 82).length]=(header 3).take 83 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 83) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run83]
  have run81 : consume (wire 3) 13 ((header 3).take 81)=⟨13,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 81++[wire 3 ((header 3).take 81).length]=(header 3).take 82 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 82) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run82]
  have run80 : consume (wire 3) 14 ((header 3).take 80)=⟨14,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 80++[wire 3 ((header 3).take 80).length]=(header 3).take 81 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 81) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run81]
  have run79 : consume (wire 3) 15 ((header 3).take 79)=⟨15,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 79++[wire 3 ((header 3).take 79).length]=(header 3).take 80 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 80) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run80]
  have run78 : consume (wire 3) 16 ((header 3).take 78)=⟨16,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 78++[wire 3 ((header 3).take 78).length]=(header 3).take 79 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 79) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run79]
  have run77 : consume (wire 3) 17 ((header 3).take 77)=⟨17,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 77++[wire 3 ((header 3).take 77).length]=(header 3).take 78 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 78) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run78]
  have run76 : consume (wire 3) 18 ((header 3).take 76)=⟨18,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 76++[wire 3 ((header 3).take 76).length]=(header 3).take 77 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 77) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run77]
  have run75 : consume (wire 3) 19 ((header 3).take 75)=⟨19,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 75++[wire 3 ((header 3).take 75).length]=(header 3).take 76 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 76) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run76]
  have run74 : consume (wire 3) 20 ((header 3).take 74)=⟨20,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 74++[wire 3 ((header 3).take 74).length]=(header 3).take 75 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 75) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run75]
  have run73 : consume (wire 3) 21 ((header 3).take 73)=⟨21,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 73++[wire 3 ((header 3).take 73).length]=(header 3).take 74 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 74) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run74]
  have run72 : consume (wire 3) 22 ((header 3).take 72)=⟨22,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 72++[wire 3 ((header 3).take 72).length]=(header 3).take 73 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 73) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run73]
  have run71 : consume (wire 3) 23 ((header 3).take 71)=⟨23,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 71++[wire 3 ((header 3).take 71).length]=(header 3).take 72 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 72) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run72]
  have run70 : consume (wire 3) 24 ((header 3).take 70)=⟨24,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 70++[wire 3 ((header 3).take 70).length]=(header 3).take 71 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 71) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run71]
  have run69 : consume (wire 3) 25 ((header 3).take 69)=⟨25,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 69++[wire 3 ((header 3).take 69).length]=(header 3).take 70 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 70) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run70]
  have run68 : consume (wire 3) 26 ((header 3).take 68)=⟨26,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 68++[wire 3 ((header 3).take 68).length]=(header 3).take 69 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 69) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run69]
  have run67 : consume (wire 3) 27 ((header 3).take 67)=⟨27,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 67++[wire 3 ((header 3).take 67).length]=(header 3).take 68 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 68) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run68]
  have run66 : consume (wire 3) 28 ((header 3).take 66)=⟨28,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 66++[wire 3 ((header 3).take 66).length]=(header 3).take 67 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 67) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run67]
  have run65 : consume (wire 3) 29 ((header 3).take 65)=⟨29,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 65++[wire 3 ((header 3).take 65).length]=(header 3).take 66 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 66) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run66]
  have run64 : consume (wire 3) 30 ((header 3).take 64)=⟨30,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 64++[wire 3 ((header 3).take 64).length]=(header 3).take 65 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 65) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run65]
  have run63 : consume (wire 3) 31 ((header 3).take 63)=⟨31,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 63++[wire 3 ((header 3).take 63).length]=(header 3).take 64 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 64) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run64]
  have run62 : consume (wire 3) 32 ((header 3).take 62)=⟨32,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 62++[wire 3 ((header 3).take 62).length]=(header 3).take 63 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 63) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run63]
  have run61 : consume (wire 3) 33 ((header 3).take 61)=⟨33,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 61++[wire 3 ((header 3).take 61).length]=(header 3).take 62 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 62) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run62]
  have run60 : consume (wire 3) 34 ((header 3).take 60)=⟨34,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 60++[wire 3 ((header 3).take 60).length]=(header 3).take 61 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 61) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run61]
  have run59 : consume (wire 3) 35 ((header 3).take 59)=⟨35,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 59++[wire 3 ((header 3).take 59).length]=(header 3).take 60 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 60) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run60]
  have run58 : consume (wire 3) 36 ((header 3).take 58)=⟨36,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 58++[wire 3 ((header 3).take 58).length]=(header 3).take 59 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 59) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run59]
  have run57 : consume (wire 3) 37 ((header 3).take 57)=⟨37,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 57++[wire 3 ((header 3).take 57).length]=(header 3).take 58 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 58) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run58]
  have run56 : consume (wire 3) 38 ((header 3).take 56)=⟨38,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 56++[wire 3 ((header 3).take 56).length]=(header 3).take 57 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 57) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run57]
  have run55 : consume (wire 3) 39 ((header 3).take 55)=⟨39,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 55++[wire 3 ((header 3).take 55).length]=(header 3).take 56 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 56) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run56]
  have run54 : consume (wire 3) 40 ((header 3).take 54)=⟨40,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 54++[wire 3 ((header 3).take 54).length]=(header 3).take 55 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 55) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run55]
  have run53 : consume (wire 3) 41 ((header 3).take 53)=⟨41,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 53++[wire 3 ((header 3).take 53).length]=(header 3).take 54 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 54) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run54]
  have run52 : consume (wire 3) 42 ((header 3).take 52)=⟨42,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 52++[wire 3 ((header 3).take 52).length]=(header 3).take 53 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 53) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run53]
  have run51 : consume (wire 3) 43 ((header 3).take 51)=⟨43,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 51++[wire 3 ((header 3).take 51).length]=(header 3).take 52 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 52) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run52]
  have run50 : consume (wire 3) 44 ((header 3).take 50)=⟨44,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 50++[wire 3 ((header 3).take 50).length]=(header 3).take 51 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 51) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run51]
  have run49 : consume (wire 3) 45 ((header 3).take 49)=⟨45,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 49++[wire 3 ((header 3).take 49).length]=(header 3).take 50 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 50) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run50]
  have run48 : consume (wire 3) 46 ((header 3).take 48)=⟨46,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 48++[wire 3 ((header 3).take 48).length]=(header 3).take 49 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 49) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run49]
  have run47 : consume (wire 3) 47 ((header 3).take 47)=⟨47,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 47++[wire 3 ((header 3).take 47).length]=(header 3).take 48 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 48) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run48]
  have run46 : consume (wire 3) 48 ((header 3).take 46)=⟨48,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 46++[wire 3 ((header 3).take 46).length]=(header 3).take 47 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 47) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run47]
  have run45 : consume (wire 3) 49 ((header 3).take 45)=⟨49,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 45++[wire 3 ((header 3).take 45).length]=(header 3).take 46 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 46) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run46]
  have run44 : consume (wire 3) 50 ((header 3).take 44)=⟨50,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 44++[wire 3 ((header 3).take 44).length]=(header 3).take 45 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 45) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run45]
  have run43 : consume (wire 3) 51 ((header 3).take 43)=⟨51,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 43++[wire 3 ((header 3).take 43).length]=(header 3).take 44 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 44) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run44]
  have run42 : consume (wire 3) 52 ((header 3).take 42)=⟨52,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 42++[wire 3 ((header 3).take 42).length]=(header 3).take 43 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 43) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run43]
  have run41 : consume (wire 3) 53 ((header 3).take 41)=⟨53,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 41++[wire 3 ((header 3).take 41).length]=(header 3).take 42 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 42) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run42]
  have run40 : consume (wire 3) 54 ((header 3).take 40)=⟨54,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 40++[wire 3 ((header 3).take 40).length]=(header 3).take 41 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 41) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run41]
  have run39 : consume (wire 3) 55 ((header 3).take 39)=⟨55,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 39++[wire 3 ((header 3).take 39).length]=(header 3).take 40 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 40) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run40]
  have run38 : consume (wire 3) 56 ((header 3).take 38)=⟨56,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 38++[wire 3 ((header 3).take 38).length]=(header 3).take 39 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 39) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run39]
  have run37 : consume (wire 3) 57 ((header 3).take 37)=⟨57,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 37++[wire 3 ((header 3).take 37).length]=(header 3).take 38 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 38) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run38]
  have run36 : consume (wire 3) 58 ((header 3).take 36)=⟨58,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 36++[wire 3 ((header 3).take 36).length]=(header 3).take 37 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 37) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run37]
  have run35 : consume (wire 3) 59 ((header 3).take 35)=⟨59,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 35++[wire 3 ((header 3).take 35).length]=(header 3).take 36 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 36) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run36]
  have run34 : consume (wire 3) 60 ((header 3).take 34)=⟨60,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 34++[wire 3 ((header 3).take 34).length]=(header 3).take 35 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 35) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run35]
  have run33 : consume (wire 3) 61 ((header 3).take 33)=⟨61,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 33++[wire 3 ((header 3).take 33).length]=(header 3).take 34 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 34) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run34]
  have run32 : consume (wire 3) 62 ((header 3).take 32)=⟨62,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 32++[wire 3 ((header 3).take 32).length]=(header 3).take 33 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 33) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run33]
  have run31 : consume (wire 3) 63 ((header 3).take 31)=⟨63,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 31++[wire 3 ((header 3).take 31).length]=(header 3).take 32 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 32) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run32]
  have run30 : consume (wire 3) 64 ((header 3).take 30)=⟨64,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 30++[wire 3 ((header 3).take 30).length]=(header 3).take 31 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 31) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run31]
  have run29 : consume (wire 3) 65 ((header 3).take 29)=⟨65,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 29++[wire 3 ((header 3).take 29).length]=(header 3).take 30 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 30) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run30]
  have run28 : consume (wire 3) 66 ((header 3).take 28)=⟨66,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 28++[wire 3 ((header 3).take 28).length]=(header 3).take 29 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 29) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run29]
  have run27 : consume (wire 3) 67 ((header 3).take 27)=⟨67,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 27++[wire 3 ((header 3).take 27).length]=(header 3).take 28 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 28) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run28]
  have run26 : consume (wire 3) 68 ((header 3).take 26)=⟨68,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 26++[wire 3 ((header 3).take 26).length]=(header 3).take 27 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 27) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run27]
  have run25 : consume (wire 3) 69 ((header 3).take 25)=⟨69,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 25++[wire 3 ((header 3).take 25).length]=(header 3).take 26 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 26) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run26]
  have run24 : consume (wire 3) 70 ((header 3).take 24)=⟨70,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 24++[wire 3 ((header 3).take 24).length]=(header 3).take 25 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 25) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run25]
  have run23 : consume (wire 3) 71 ((header 3).take 23)=⟨71,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 23++[wire 3 ((header 3).take 23).length]=(header 3).take 24 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 24) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run24]
  have run22 : consume (wire 3) 72 ((header 3).take 22)=⟨72,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 22++[wire 3 ((header 3).take 22).length]=(header 3).take 23 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 23) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run23]
  have run21 : consume (wire 3) 73 ((header 3).take 21)=⟨73,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 21++[wire 3 ((header 3).take 21).length]=(header 3).take 22 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 22) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run22]
  have run20 : consume (wire 3) 74 ((header 3).take 20)=⟨74,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 20++[wire 3 ((header 3).take 20).length]=(header 3).take 21 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 21) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run21]
  have run19 : consume (wire 3) 75 ((header 3).take 19)=⟨75,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 19++[wire 3 ((header 3).take 19).length]=(header 3).take 20 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 20) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run20]
  have run18 : consume (wire 3) 76 ((header 3).take 18)=⟨76,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 18++[wire 3 ((header 3).take 18).length]=(header 3).take 19 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 19) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run19]
  have run17 : consume (wire 3) 77 ((header 3).take 17)=⟨77,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 17++[wire 3 ((header 3).take 17).length]=(header 3).take 18 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 18) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run18]
  have run16 : consume (wire 3) 78 ((header 3).take 16)=⟨78,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 16++[wire 3 ((header 3).take 16).length]=(header 3).take 17 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 17) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run17]
  have run15 : consume (wire 3) 79 ((header 3).take 15)=⟨79,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 15++[wire 3 ((header 3).take 15).length]=(header 3).take 16 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 16) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run16]
  have run14 : consume (wire 3) 80 ((header 3).take 14)=⟨80,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 14++[wire 3 ((header 3).take 14).length]=(header 3).take 15 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 15) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run15]
  have run13 : consume (wire 3) 81 ((header 3).take 13)=⟨81,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 13++[wire 3 ((header 3).take 13).length]=(header 3).take 14 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 14) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run14]
  have run12 : consume (wire 3) 82 ((header 3).take 12)=⟨82,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 12++[wire 3 ((header 3).take 12).length]=(header 3).take 13 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 13) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run13]
  have run11 : consume (wire 3) 83 ((header 3).take 11)=⟨83,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 11++[wire 3 ((header 3).take 11).length]=(header 3).take 12 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 12) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run12]
  have run10 : consume (wire 3) 84 ((header 3).take 10)=⟨84,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 10++[wire 3 ((header 3).take 10).length]=(header 3).take 11 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 11) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run11]
  have run9 : consume (wire 3) 85 ((header 3).take 9)=⟨85,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 9++[wire 3 ((header 3).take 9).length]=(header 3).take 10 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 10) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run10]
  have run8 : consume (wire 3) 86 ((header 3).take 8)=⟨86,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 8++[wire 3 ((header 3).take 8).length]=(header 3).take 9 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 9) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run9]
  have run7 : consume (wire 3) 87 ((header 3).take 7)=⟨87,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 7++[wire 3 ((header 3).take 7).length]=(header 3).take 8 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 8) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run8]
  have run6 : consume (wire 3) 88 ((header 3).take 6)=⟨88,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 6++[wire 3 ((header 3).take 6).length]=(header 3).take 7 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 7) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run7]
  have run5 : consume (wire 3) 89 ((header 3).take 5)=⟨89,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 5++[wire 3 ((header 3).take 5).length]=(header 3).take 6 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 6) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run6]
  have run4 : consume (wire 3) 90 ((header 3).take 4)=⟨90,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 4++[wire 3 ((header 3).take 4).length]=(header 3).take 5 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 5) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run5]
  have run3 : consume (wire 3) 91 ((header 3).take 3)=⟨91,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 3++[wire 3 ((header 3).take 3).length]=(header 3).take 4 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 4) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run4]
  have run2 : consume (wire 3) 92 ((header 3).take 2)=⟨92,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 2++[wire 3 ((header 3).take 2).length]=(header 3).take 3 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 3) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run3]
  have run1 : consume (wire 3) 93 ((header 3).take 1)=⟨93,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 1++[wire 3 ((header 3).take 1).length]=(header 3).take 2 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 2) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run2]
  have run0 : consume (wire 3) 94 ((header 3).take 0)=⟨94,header 3,.done (expected 3)⟩ := by
    have nextByte : (header 3).take 0++[wire 3 ((header 3).take 0).length]=(header 3).take 1 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header 3).take 1) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run1]
  exact run0

theorem consumed (kind : Fin 4) : consume (wire kind) (header kind).length []=⟨(header kind).length,header kind,.done (expected kind)⟩ := by
  have kinds : kind=0 ∨ kind=1 ∨ kind=2 ∨ kind=3 := by omega
  rcases kinds with rfl|rfl|rfl|rfl
  · exact consumed0
  · exact consumed1
  · exact consumed2
  · exact consumed3

theorem facts : ∀ kind : Fin 4, (header kind).length≤100 ∧ (expected kind).len=(header kind).length ∧
    (expected kind).framing=.length 0 ∧ (expected kind).target.2-(expected kind).target.1=8 ∧
    (77+86*(expected kind).len)*(expected kind).headers.length≤40000 := by decide +kernel

theorem pure_close : ∀ kind : Fin 4, MainCloseSpec.mustClose (expected kind).minor 1 (header kind) (MainRequestInputs.entries (expected kind))=closes kind := by decide +kernel

/-- Satisfying reset/UART executions of the general scanned path: keep-alive,
    mixed-case close token, near misses, and a later duplicate Connection field.
    This ends at router entry, not at a response or a completed transaction. -/
theorem execution (kind : Fin 4) : ∃ n d after reads, n≤500000000 ∧
    Observed.Steps B img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩ reads [] ∧
      Observed.input reads=header kind ∧
      MainCloseReady.At d after (header kind) Spec.initial (expected kind) 0 1 (closes kind) := by
  have fs := facts kind
  have accepted : (consume (wire kind) (header kind).length []).result=.done (expected kind) := by rw [consumed kind]
  obtain ⟨n,d,after,close,limit,trace,state,bytes⟩ := MainCloseRequestReset.contract MainInitWitness.core MainInitWitness.ram (wire kind) (plan kind) (header kind).length (expected kind) 0 (plan kind)
    rfl (Or.inr rfl) rfl Blocking.stack_available (by omega) (valid kind _ _) accepted fs.2.2.1 (valid kind _ _)
  rw [consumed kind] at limit trace state bytes
  dsimp only at limit trace state bytes
  have missing : (expected kind).len+0-(header kind).length=0 := by rw [fs.2.1];omega
  rw [missing] at limit trace state bytes
  simp only [arrivals,List.range_zero,List.map_nil,List.append_nil] at state bytes
  have rawEq : MainRequestSpans.raw (header kind) (expected kind) 0=header kind := by simp only [MainRequestSpans.raw,Nat.add_zero,fs.2.1,List.take_length]
  have selected : close=closes kind := state.spec.trans (by rw [rawEq];exact pure_close kind)
  rw [selected] at state
  refine ⟨n,d,after,_,?_,trace,bytes,state⟩
  have hc (first count : Nat) : MainHeaderStreamPlan.cost (plan kind) first count=(47+8+HeadColdFutureComplete.budget 1024)*count := by
    induction count generalizing first with
    | zero => rfl
    | succ count ih => rw [MainHeaderStreamPlan.cost,ih,Nat.mul_succ];change (47+4*2+HeadColdFutureComplete.budget 1024)+_= _;omega
  rw [hc,fs.2.2.2.1] at limit
  have proofBound := fs.2.2.2.2
  simp only [Nat.add_zero,MainLengthStreamPlan.cost] at limit
  unfold HeadColdFutureComplete.budget HeadFieldsLoopComplete.budget at limit
  omega
end E5R.Thermostat.MainCloseRequestWitness
