import Projects.thermostat.MainTempReset
import Projects.thermostat.MainTempSuccessWitness
import Projects.thermostat.MainConsumeCongr
set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 5000000
namespace E5R.Thermostat.MainTempResetWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board
inductive Case where
  | good | malformed | unauth
  deriving DecidableEq
def missingHeader (close : Bool) : List (BitVec 8) := if close then [80,79,83,84,32,47,116,101,109,112,63,113,32,72,84,84,80,47,49,46,49,13,10,72,111,115,116,58,120,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,51,13,10,67,111,110,110,101,99,116,105,111,110,58,99,108,111,115,101,13,10,13,10] else [80,79,83,84,32,47,116,101,109,112,63,113,32,72,84,84,80,47,49,46,49,13,10,72,111,115,116,58,120,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,51,13,10,13,10]
def missingHead (close : Bool) : Head :=
  if close then ⟨(0,4),(5,12),1,[⟨23,27,28,29⟩,⟨31,45,46,47⟩,⟨49,59,60,65⟩],69,.length 3⟩
  else ⟨(0,4),(5,12),1,[⟨23,27,28,29⟩,⟨31,45,46,47⟩],51,.length 3⟩
def header : Case → Bool → List (BitVec 8)
  | .unauth => missingHeader
  | _ => MainTempSuccessWitness.header
def head : Case → Bool → Head
  | .unauth => missingHead
  | _ => MainTempSuccessWitness.expected
def body : Case → List (BitVec 8)
  | .good => MainTempSuccessWitness.body
  | _ => [98,97,100]
def wire (which : Case) (close : Bool) (k : Nat) : BitVec 8 := (header which close++body which)[k]?.getD 0#8

theorem missing_consumed_false : consume (wire .unauth false) (missingHeader false).length []=⟨(missingHeader false).length,missingHeader false,.done (missingHead false)⟩ := by
  have run50 : consume (wire .unauth false) 1 ((missingHeader false).take 50)=⟨1,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 50++[wire .unauth false ((missingHeader false).take 50).length]=(missingHeader false).take 51 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 51) 1024 1024=.done (missingHead false) := by decide +kernel
    rw [consume,nextByte,parsed]
    congr 1
  have run49 : consume (wire .unauth false) 2 ((missingHeader false).take 49)=⟨2,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 49++[wire .unauth false ((missingHeader false).take 49).length]=(missingHeader false).take 50 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 50) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run50]
  have run48 : consume (wire .unauth false) 3 ((missingHeader false).take 48)=⟨3,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 48++[wire .unauth false ((missingHeader false).take 48).length]=(missingHeader false).take 49 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 49) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run49]
  have run47 : consume (wire .unauth false) 4 ((missingHeader false).take 47)=⟨4,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 47++[wire .unauth false ((missingHeader false).take 47).length]=(missingHeader false).take 48 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 48) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run48]
  have run46 : consume (wire .unauth false) 5 ((missingHeader false).take 46)=⟨5,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 46++[wire .unauth false ((missingHeader false).take 46).length]=(missingHeader false).take 47 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 47) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run47]
  have run45 : consume (wire .unauth false) 6 ((missingHeader false).take 45)=⟨6,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 45++[wire .unauth false ((missingHeader false).take 45).length]=(missingHeader false).take 46 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 46) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run46]
  have run44 : consume (wire .unauth false) 7 ((missingHeader false).take 44)=⟨7,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 44++[wire .unauth false ((missingHeader false).take 44).length]=(missingHeader false).take 45 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 45) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run45]
  have run43 : consume (wire .unauth false) 8 ((missingHeader false).take 43)=⟨8,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 43++[wire .unauth false ((missingHeader false).take 43).length]=(missingHeader false).take 44 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 44) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run44]
  have run42 : consume (wire .unauth false) 9 ((missingHeader false).take 42)=⟨9,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 42++[wire .unauth false ((missingHeader false).take 42).length]=(missingHeader false).take 43 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 43) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run43]
  have run41 : consume (wire .unauth false) 10 ((missingHeader false).take 41)=⟨10,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 41++[wire .unauth false ((missingHeader false).take 41).length]=(missingHeader false).take 42 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 42) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run42]
  have run40 : consume (wire .unauth false) 11 ((missingHeader false).take 40)=⟨11,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 40++[wire .unauth false ((missingHeader false).take 40).length]=(missingHeader false).take 41 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 41) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run41]
  have run39 : consume (wire .unauth false) 12 ((missingHeader false).take 39)=⟨12,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 39++[wire .unauth false ((missingHeader false).take 39).length]=(missingHeader false).take 40 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 40) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run40]
  have run38 : consume (wire .unauth false) 13 ((missingHeader false).take 38)=⟨13,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 38++[wire .unauth false ((missingHeader false).take 38).length]=(missingHeader false).take 39 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 39) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run39]
  have run37 : consume (wire .unauth false) 14 ((missingHeader false).take 37)=⟨14,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 37++[wire .unauth false ((missingHeader false).take 37).length]=(missingHeader false).take 38 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 38) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run38]
  have run36 : consume (wire .unauth false) 15 ((missingHeader false).take 36)=⟨15,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 36++[wire .unauth false ((missingHeader false).take 36).length]=(missingHeader false).take 37 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 37) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run37]
  have run35 : consume (wire .unauth false) 16 ((missingHeader false).take 35)=⟨16,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 35++[wire .unauth false ((missingHeader false).take 35).length]=(missingHeader false).take 36 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 36) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run36]
  have run34 : consume (wire .unauth false) 17 ((missingHeader false).take 34)=⟨17,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 34++[wire .unauth false ((missingHeader false).take 34).length]=(missingHeader false).take 35 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 35) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run35]
  have run33 : consume (wire .unauth false) 18 ((missingHeader false).take 33)=⟨18,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 33++[wire .unauth false ((missingHeader false).take 33).length]=(missingHeader false).take 34 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 34) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run34]
  have run32 : consume (wire .unauth false) 19 ((missingHeader false).take 32)=⟨19,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 32++[wire .unauth false ((missingHeader false).take 32).length]=(missingHeader false).take 33 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 33) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run33]
  have run31 : consume (wire .unauth false) 20 ((missingHeader false).take 31)=⟨20,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 31++[wire .unauth false ((missingHeader false).take 31).length]=(missingHeader false).take 32 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 32) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run32]
  have run30 : consume (wire .unauth false) 21 ((missingHeader false).take 30)=⟨21,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 30++[wire .unauth false ((missingHeader false).take 30).length]=(missingHeader false).take 31 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 31) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run31]
  have run29 : consume (wire .unauth false) 22 ((missingHeader false).take 29)=⟨22,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 29++[wire .unauth false ((missingHeader false).take 29).length]=(missingHeader false).take 30 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 30) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run30]
  have run28 : consume (wire .unauth false) 23 ((missingHeader false).take 28)=⟨23,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 28++[wire .unauth false ((missingHeader false).take 28).length]=(missingHeader false).take 29 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 29) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run29]
  have run27 : consume (wire .unauth false) 24 ((missingHeader false).take 27)=⟨24,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 27++[wire .unauth false ((missingHeader false).take 27).length]=(missingHeader false).take 28 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 28) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run28]
  have run26 : consume (wire .unauth false) 25 ((missingHeader false).take 26)=⟨25,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 26++[wire .unauth false ((missingHeader false).take 26).length]=(missingHeader false).take 27 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 27) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run27]
  have run25 : consume (wire .unauth false) 26 ((missingHeader false).take 25)=⟨26,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 25++[wire .unauth false ((missingHeader false).take 25).length]=(missingHeader false).take 26 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 26) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run26]
  have run24 : consume (wire .unauth false) 27 ((missingHeader false).take 24)=⟨27,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 24++[wire .unauth false ((missingHeader false).take 24).length]=(missingHeader false).take 25 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 25) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run25]
  have run23 : consume (wire .unauth false) 28 ((missingHeader false).take 23)=⟨28,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 23++[wire .unauth false ((missingHeader false).take 23).length]=(missingHeader false).take 24 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 24) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run24]
  have run22 : consume (wire .unauth false) 29 ((missingHeader false).take 22)=⟨29,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 22++[wire .unauth false ((missingHeader false).take 22).length]=(missingHeader false).take 23 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 23) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run23]
  have run21 : consume (wire .unauth false) 30 ((missingHeader false).take 21)=⟨30,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 21++[wire .unauth false ((missingHeader false).take 21).length]=(missingHeader false).take 22 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 22) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run22]
  have run20 : consume (wire .unauth false) 31 ((missingHeader false).take 20)=⟨31,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 20++[wire .unauth false ((missingHeader false).take 20).length]=(missingHeader false).take 21 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 21) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run21]
  have run19 : consume (wire .unauth false) 32 ((missingHeader false).take 19)=⟨32,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 19++[wire .unauth false ((missingHeader false).take 19).length]=(missingHeader false).take 20 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 20) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run20]
  have run18 : consume (wire .unauth false) 33 ((missingHeader false).take 18)=⟨33,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 18++[wire .unauth false ((missingHeader false).take 18).length]=(missingHeader false).take 19 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 19) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run19]
  have run17 : consume (wire .unauth false) 34 ((missingHeader false).take 17)=⟨34,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 17++[wire .unauth false ((missingHeader false).take 17).length]=(missingHeader false).take 18 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 18) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run18]
  have run16 : consume (wire .unauth false) 35 ((missingHeader false).take 16)=⟨35,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 16++[wire .unauth false ((missingHeader false).take 16).length]=(missingHeader false).take 17 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 17) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run17]
  have run15 : consume (wire .unauth false) 36 ((missingHeader false).take 15)=⟨36,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 15++[wire .unauth false ((missingHeader false).take 15).length]=(missingHeader false).take 16 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 16) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run16]
  have run14 : consume (wire .unauth false) 37 ((missingHeader false).take 14)=⟨37,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 14++[wire .unauth false ((missingHeader false).take 14).length]=(missingHeader false).take 15 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 15) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run15]
  have run13 : consume (wire .unauth false) 38 ((missingHeader false).take 13)=⟨38,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 13++[wire .unauth false ((missingHeader false).take 13).length]=(missingHeader false).take 14 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 14) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run14]
  have run12 : consume (wire .unauth false) 39 ((missingHeader false).take 12)=⟨39,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 12++[wire .unauth false ((missingHeader false).take 12).length]=(missingHeader false).take 13 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 13) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run13]
  have run11 : consume (wire .unauth false) 40 ((missingHeader false).take 11)=⟨40,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 11++[wire .unauth false ((missingHeader false).take 11).length]=(missingHeader false).take 12 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 12) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run12]
  have run10 : consume (wire .unauth false) 41 ((missingHeader false).take 10)=⟨41,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 10++[wire .unauth false ((missingHeader false).take 10).length]=(missingHeader false).take 11 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 11) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run11]
  have run9 : consume (wire .unauth false) 42 ((missingHeader false).take 9)=⟨42,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 9++[wire .unauth false ((missingHeader false).take 9).length]=(missingHeader false).take 10 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 10) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run10]
  have run8 : consume (wire .unauth false) 43 ((missingHeader false).take 8)=⟨43,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 8++[wire .unauth false ((missingHeader false).take 8).length]=(missingHeader false).take 9 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 9) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run9]
  have run7 : consume (wire .unauth false) 44 ((missingHeader false).take 7)=⟨44,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 7++[wire .unauth false ((missingHeader false).take 7).length]=(missingHeader false).take 8 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 8) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run8]
  have run6 : consume (wire .unauth false) 45 ((missingHeader false).take 6)=⟨45,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 6++[wire .unauth false ((missingHeader false).take 6).length]=(missingHeader false).take 7 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 7) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run7]
  have run5 : consume (wire .unauth false) 46 ((missingHeader false).take 5)=⟨46,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 5++[wire .unauth false ((missingHeader false).take 5).length]=(missingHeader false).take 6 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 6) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run6]
  have run4 : consume (wire .unauth false) 47 ((missingHeader false).take 4)=⟨47,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 4++[wire .unauth false ((missingHeader false).take 4).length]=(missingHeader false).take 5 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 5) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run5]
  have run3 : consume (wire .unauth false) 48 ((missingHeader false).take 3)=⟨48,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 3++[wire .unauth false ((missingHeader false).take 3).length]=(missingHeader false).take 4 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 4) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run4]
  have run2 : consume (wire .unauth false) 49 ((missingHeader false).take 2)=⟨49,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 2++[wire .unauth false ((missingHeader false).take 2).length]=(missingHeader false).take 3 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 3) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run3]
  have run1 : consume (wire .unauth false) 50 ((missingHeader false).take 1)=⟨50,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 1++[wire .unauth false ((missingHeader false).take 1).length]=(missingHeader false).take 2 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 2) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run2]
  have run0 : consume (wire .unauth false) 51 ((missingHeader false).take 0)=⟨51,missingHeader false,.done (missingHead false)⟩ := by
    have nextByte : (missingHeader false).take 0++[wire .unauth false ((missingHeader false).take 0).length]=(missingHeader false).take 1 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader false).take 1) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run1]
  exact run0

theorem missing_consumed_true : consume (wire .unauth true) (missingHeader true).length []=⟨(missingHeader true).length,missingHeader true,.done (missingHead true)⟩ := by
  have run68 : consume (wire .unauth true) 1 ((missingHeader true).take 68)=⟨1,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 68++[wire .unauth true ((missingHeader true).take 68).length]=(missingHeader true).take 69 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 69) 1024 1024=.done (missingHead true) := by decide +kernel
    rw [consume,nextByte,parsed]
    congr 1
  have run67 : consume (wire .unauth true) 2 ((missingHeader true).take 67)=⟨2,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 67++[wire .unauth true ((missingHeader true).take 67).length]=(missingHeader true).take 68 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 68) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run68]
  have run66 : consume (wire .unauth true) 3 ((missingHeader true).take 66)=⟨3,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 66++[wire .unauth true ((missingHeader true).take 66).length]=(missingHeader true).take 67 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 67) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run67]
  have run65 : consume (wire .unauth true) 4 ((missingHeader true).take 65)=⟨4,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 65++[wire .unauth true ((missingHeader true).take 65).length]=(missingHeader true).take 66 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 66) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run66]
  have run64 : consume (wire .unauth true) 5 ((missingHeader true).take 64)=⟨5,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 64++[wire .unauth true ((missingHeader true).take 64).length]=(missingHeader true).take 65 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 65) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run65]
  have run63 : consume (wire .unauth true) 6 ((missingHeader true).take 63)=⟨6,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 63++[wire .unauth true ((missingHeader true).take 63).length]=(missingHeader true).take 64 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 64) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run64]
  have run62 : consume (wire .unauth true) 7 ((missingHeader true).take 62)=⟨7,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 62++[wire .unauth true ((missingHeader true).take 62).length]=(missingHeader true).take 63 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 63) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run63]
  have run61 : consume (wire .unauth true) 8 ((missingHeader true).take 61)=⟨8,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 61++[wire .unauth true ((missingHeader true).take 61).length]=(missingHeader true).take 62 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 62) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run62]
  have run60 : consume (wire .unauth true) 9 ((missingHeader true).take 60)=⟨9,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 60++[wire .unauth true ((missingHeader true).take 60).length]=(missingHeader true).take 61 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 61) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run61]
  have run59 : consume (wire .unauth true) 10 ((missingHeader true).take 59)=⟨10,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 59++[wire .unauth true ((missingHeader true).take 59).length]=(missingHeader true).take 60 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 60) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run60]
  have run58 : consume (wire .unauth true) 11 ((missingHeader true).take 58)=⟨11,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 58++[wire .unauth true ((missingHeader true).take 58).length]=(missingHeader true).take 59 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 59) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run59]
  have run57 : consume (wire .unauth true) 12 ((missingHeader true).take 57)=⟨12,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 57++[wire .unauth true ((missingHeader true).take 57).length]=(missingHeader true).take 58 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 58) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run58]
  have run56 : consume (wire .unauth true) 13 ((missingHeader true).take 56)=⟨13,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 56++[wire .unauth true ((missingHeader true).take 56).length]=(missingHeader true).take 57 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 57) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run57]
  have run55 : consume (wire .unauth true) 14 ((missingHeader true).take 55)=⟨14,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 55++[wire .unauth true ((missingHeader true).take 55).length]=(missingHeader true).take 56 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 56) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run56]
  have run54 : consume (wire .unauth true) 15 ((missingHeader true).take 54)=⟨15,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 54++[wire .unauth true ((missingHeader true).take 54).length]=(missingHeader true).take 55 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 55) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run55]
  have run53 : consume (wire .unauth true) 16 ((missingHeader true).take 53)=⟨16,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 53++[wire .unauth true ((missingHeader true).take 53).length]=(missingHeader true).take 54 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 54) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run54]
  have run52 : consume (wire .unauth true) 17 ((missingHeader true).take 52)=⟨17,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 52++[wire .unauth true ((missingHeader true).take 52).length]=(missingHeader true).take 53 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 53) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run53]
  have run51 : consume (wire .unauth true) 18 ((missingHeader true).take 51)=⟨18,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 51++[wire .unauth true ((missingHeader true).take 51).length]=(missingHeader true).take 52 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 52) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run52]
  have run50 : consume (wire .unauth true) 19 ((missingHeader true).take 50)=⟨19,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 50++[wire .unauth true ((missingHeader true).take 50).length]=(missingHeader true).take 51 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 51) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run51]
  have run49 : consume (wire .unauth true) 20 ((missingHeader true).take 49)=⟨20,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 49++[wire .unauth true ((missingHeader true).take 49).length]=(missingHeader true).take 50 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 50) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run50]
  have run48 : consume (wire .unauth true) 21 ((missingHeader true).take 48)=⟨21,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 48++[wire .unauth true ((missingHeader true).take 48).length]=(missingHeader true).take 49 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 49) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run49]
  have run47 : consume (wire .unauth true) 22 ((missingHeader true).take 47)=⟨22,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 47++[wire .unauth true ((missingHeader true).take 47).length]=(missingHeader true).take 48 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 48) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run48]
  have run46 : consume (wire .unauth true) 23 ((missingHeader true).take 46)=⟨23,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 46++[wire .unauth true ((missingHeader true).take 46).length]=(missingHeader true).take 47 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 47) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run47]
  have run45 : consume (wire .unauth true) 24 ((missingHeader true).take 45)=⟨24,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 45++[wire .unauth true ((missingHeader true).take 45).length]=(missingHeader true).take 46 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 46) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run46]
  have run44 : consume (wire .unauth true) 25 ((missingHeader true).take 44)=⟨25,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 44++[wire .unauth true ((missingHeader true).take 44).length]=(missingHeader true).take 45 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 45) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run45]
  have run43 : consume (wire .unauth true) 26 ((missingHeader true).take 43)=⟨26,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 43++[wire .unauth true ((missingHeader true).take 43).length]=(missingHeader true).take 44 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 44) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run44]
  have run42 : consume (wire .unauth true) 27 ((missingHeader true).take 42)=⟨27,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 42++[wire .unauth true ((missingHeader true).take 42).length]=(missingHeader true).take 43 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 43) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run43]
  have run41 : consume (wire .unauth true) 28 ((missingHeader true).take 41)=⟨28,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 41++[wire .unauth true ((missingHeader true).take 41).length]=(missingHeader true).take 42 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 42) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run42]
  have run40 : consume (wire .unauth true) 29 ((missingHeader true).take 40)=⟨29,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 40++[wire .unauth true ((missingHeader true).take 40).length]=(missingHeader true).take 41 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 41) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run41]
  have run39 : consume (wire .unauth true) 30 ((missingHeader true).take 39)=⟨30,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 39++[wire .unauth true ((missingHeader true).take 39).length]=(missingHeader true).take 40 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 40) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run40]
  have run38 : consume (wire .unauth true) 31 ((missingHeader true).take 38)=⟨31,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 38++[wire .unauth true ((missingHeader true).take 38).length]=(missingHeader true).take 39 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 39) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run39]
  have run37 : consume (wire .unauth true) 32 ((missingHeader true).take 37)=⟨32,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 37++[wire .unauth true ((missingHeader true).take 37).length]=(missingHeader true).take 38 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 38) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run38]
  have run36 : consume (wire .unauth true) 33 ((missingHeader true).take 36)=⟨33,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 36++[wire .unauth true ((missingHeader true).take 36).length]=(missingHeader true).take 37 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 37) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run37]
  have run35 : consume (wire .unauth true) 34 ((missingHeader true).take 35)=⟨34,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 35++[wire .unauth true ((missingHeader true).take 35).length]=(missingHeader true).take 36 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 36) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run36]
  have run34 : consume (wire .unauth true) 35 ((missingHeader true).take 34)=⟨35,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 34++[wire .unauth true ((missingHeader true).take 34).length]=(missingHeader true).take 35 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 35) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run35]
  have run33 : consume (wire .unauth true) 36 ((missingHeader true).take 33)=⟨36,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 33++[wire .unauth true ((missingHeader true).take 33).length]=(missingHeader true).take 34 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 34) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run34]
  have run32 : consume (wire .unauth true) 37 ((missingHeader true).take 32)=⟨37,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 32++[wire .unauth true ((missingHeader true).take 32).length]=(missingHeader true).take 33 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 33) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run33]
  have run31 : consume (wire .unauth true) 38 ((missingHeader true).take 31)=⟨38,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 31++[wire .unauth true ((missingHeader true).take 31).length]=(missingHeader true).take 32 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 32) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run32]
  have run30 : consume (wire .unauth true) 39 ((missingHeader true).take 30)=⟨39,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 30++[wire .unauth true ((missingHeader true).take 30).length]=(missingHeader true).take 31 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 31) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run31]
  have run29 : consume (wire .unauth true) 40 ((missingHeader true).take 29)=⟨40,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 29++[wire .unauth true ((missingHeader true).take 29).length]=(missingHeader true).take 30 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 30) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run30]
  have run28 : consume (wire .unauth true) 41 ((missingHeader true).take 28)=⟨41,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 28++[wire .unauth true ((missingHeader true).take 28).length]=(missingHeader true).take 29 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 29) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run29]
  have run27 : consume (wire .unauth true) 42 ((missingHeader true).take 27)=⟨42,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 27++[wire .unauth true ((missingHeader true).take 27).length]=(missingHeader true).take 28 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 28) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run28]
  have run26 : consume (wire .unauth true) 43 ((missingHeader true).take 26)=⟨43,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 26++[wire .unauth true ((missingHeader true).take 26).length]=(missingHeader true).take 27 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 27) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run27]
  have run25 : consume (wire .unauth true) 44 ((missingHeader true).take 25)=⟨44,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 25++[wire .unauth true ((missingHeader true).take 25).length]=(missingHeader true).take 26 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 26) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run26]
  have run24 : consume (wire .unauth true) 45 ((missingHeader true).take 24)=⟨45,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 24++[wire .unauth true ((missingHeader true).take 24).length]=(missingHeader true).take 25 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 25) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run25]
  have run23 : consume (wire .unauth true) 46 ((missingHeader true).take 23)=⟨46,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 23++[wire .unauth true ((missingHeader true).take 23).length]=(missingHeader true).take 24 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 24) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run24]
  have run22 : consume (wire .unauth true) 47 ((missingHeader true).take 22)=⟨47,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 22++[wire .unauth true ((missingHeader true).take 22).length]=(missingHeader true).take 23 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 23) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run23]
  have run21 : consume (wire .unauth true) 48 ((missingHeader true).take 21)=⟨48,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 21++[wire .unauth true ((missingHeader true).take 21).length]=(missingHeader true).take 22 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 22) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run22]
  have run20 : consume (wire .unauth true) 49 ((missingHeader true).take 20)=⟨49,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 20++[wire .unauth true ((missingHeader true).take 20).length]=(missingHeader true).take 21 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 21) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run21]
  have run19 : consume (wire .unauth true) 50 ((missingHeader true).take 19)=⟨50,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 19++[wire .unauth true ((missingHeader true).take 19).length]=(missingHeader true).take 20 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 20) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run20]
  have run18 : consume (wire .unauth true) 51 ((missingHeader true).take 18)=⟨51,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 18++[wire .unauth true ((missingHeader true).take 18).length]=(missingHeader true).take 19 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 19) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run19]
  have run17 : consume (wire .unauth true) 52 ((missingHeader true).take 17)=⟨52,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 17++[wire .unauth true ((missingHeader true).take 17).length]=(missingHeader true).take 18 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 18) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run18]
  have run16 : consume (wire .unauth true) 53 ((missingHeader true).take 16)=⟨53,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 16++[wire .unauth true ((missingHeader true).take 16).length]=(missingHeader true).take 17 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 17) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run17]
  have run15 : consume (wire .unauth true) 54 ((missingHeader true).take 15)=⟨54,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 15++[wire .unauth true ((missingHeader true).take 15).length]=(missingHeader true).take 16 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 16) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run16]
  have run14 : consume (wire .unauth true) 55 ((missingHeader true).take 14)=⟨55,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 14++[wire .unauth true ((missingHeader true).take 14).length]=(missingHeader true).take 15 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 15) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run15]
  have run13 : consume (wire .unauth true) 56 ((missingHeader true).take 13)=⟨56,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 13++[wire .unauth true ((missingHeader true).take 13).length]=(missingHeader true).take 14 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 14) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run14]
  have run12 : consume (wire .unauth true) 57 ((missingHeader true).take 12)=⟨57,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 12++[wire .unauth true ((missingHeader true).take 12).length]=(missingHeader true).take 13 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 13) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run13]
  have run11 : consume (wire .unauth true) 58 ((missingHeader true).take 11)=⟨58,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 11++[wire .unauth true ((missingHeader true).take 11).length]=(missingHeader true).take 12 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 12) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run12]
  have run10 : consume (wire .unauth true) 59 ((missingHeader true).take 10)=⟨59,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 10++[wire .unauth true ((missingHeader true).take 10).length]=(missingHeader true).take 11 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 11) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run11]
  have run9 : consume (wire .unauth true) 60 ((missingHeader true).take 9)=⟨60,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 9++[wire .unauth true ((missingHeader true).take 9).length]=(missingHeader true).take 10 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 10) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run10]
  have run8 : consume (wire .unauth true) 61 ((missingHeader true).take 8)=⟨61,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 8++[wire .unauth true ((missingHeader true).take 8).length]=(missingHeader true).take 9 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 9) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run9]
  have run7 : consume (wire .unauth true) 62 ((missingHeader true).take 7)=⟨62,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 7++[wire .unauth true ((missingHeader true).take 7).length]=(missingHeader true).take 8 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 8) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run8]
  have run6 : consume (wire .unauth true) 63 ((missingHeader true).take 6)=⟨63,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 6++[wire .unauth true ((missingHeader true).take 6).length]=(missingHeader true).take 7 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 7) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run7]
  have run5 : consume (wire .unauth true) 64 ((missingHeader true).take 5)=⟨64,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 5++[wire .unauth true ((missingHeader true).take 5).length]=(missingHeader true).take 6 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 6) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run6]
  have run4 : consume (wire .unauth true) 65 ((missingHeader true).take 4)=⟨65,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 4++[wire .unauth true ((missingHeader true).take 4).length]=(missingHeader true).take 5 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 5) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run5]
  have run3 : consume (wire .unauth true) 66 ((missingHeader true).take 3)=⟨66,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 3++[wire .unauth true ((missingHeader true).take 3).length]=(missingHeader true).take 4 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 4) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run4]
  have run2 : consume (wire .unauth true) 67 ((missingHeader true).take 2)=⟨67,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 2++[wire .unauth true ((missingHeader true).take 2).length]=(missingHeader true).take 3 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 3) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run3]
  have run1 : consume (wire .unauth true) 68 ((missingHeader true).take 1)=⟨68,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 1++[wire .unauth true ((missingHeader true).take 1).length]=(missingHeader true).take 2 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 2) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run2]
  have run0 : consume (wire .unauth true) 69 ((missingHeader true).take 0)=⟨69,missingHeader true,.done (missingHead true)⟩ := by
    have nextByte : (missingHeader true).take 0++[wire .unauth true ((missingHeader true).take 0).length]=(missingHeader true).take 1 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((missingHeader true).take 1) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run1]
  exact run0

theorem consumed (which : Case) (close : Bool) :
    consume (wire which close) (header which close).length []=⟨(header which close).length,header which close,.done (head which close)⟩ := by
  cases which with
  | unauth => cases close;exact missing_consumed_false;exact missing_consumed_true
  | good => exact MainTempSuccessWitness.consumed close
  | malformed =>
    have same := consume_congr (wire .malformed close) (MainTempSuccessWitness.wire close)
      (MainTempSuccessWitness.header close).length [] (by
        intro k lower upper
        simp only [List.length_nil,Nat.zero_add] at upper
        unfold wire MainTempSuccessWitness.wire
        change ((MainTempSuccessWitness.header close++body .malformed)[k]?).getD 0#8=
          ((MainTempSuccessWitness.header close++MainTempSuccessWitness.body)[k]?).getD 0#8
        rw [List.getElem?_append_left upper,List.getElem?_append_left upper])
    exact same.trans (MainTempSuccessWitness.consumed close)

def plan (which : Case) (close : Bool) : ChunkReceivePlan.Plan :=
  ⟨fun _ => [0#32,2#32],fun _ => 129#32,fun k => BitVec.ofNat 32 (wire which close k).toNat⟩
theorem valid (which : Case) (close : Bool) (first count : Nat) : ChunkReceivePlan.Valid (plan which close) (wire which close) first count := by
  intro k hk he
  refine ⟨?_,(by change MainChunkPoll.mask 129#32≠0#32;decide +kernel),MainChunkStreamingWitness.byte_roundtrip (wire which close k)⟩
  intro status hs
  change status∈[0#32,2#32] at hs
  have casesStatus : status=0#32 ∨ status=2#32 := by simpa using hs
  rcases casesStatus with zero|two <;> subst status <;> decide +kernel

def expected : Case → TempHttpSpec.Reply
  | .good => ⟨MainTempSuccessWitness.state,200,WireSpec.ascii "application/json",ReplyJson.snapshot MainTempSuccessWitness.state⟩
  | .malformed => ⟨Spec.initial,400,[],[]⟩
  | .unauth => ⟨Spec.initial,401,[],[]⟩
def headerSlots (which : Case) (close : Bool) := List.replicate
  (ResponseHeadSpec.bytes (expected which).status (expected which).mime (expected which).payload.length close).length UartWriteWitness.slot1
def bodySlots (which : Case) := List.replicate (expected which).payload.length UartWriteWitness.slot1

theorem delivered (which : Case) (close : Bool) :
    MainTempReset.received (wire which close) (header which close).length (head which close) 3=header which close++body which := by
  unfold MainTempReset.received MainTempSuccessReset.received
  rw [consumed]
  cases which <;> cases close <;> decide +kernel

theorem facts : ∀ (which : Case) (close : Bool), (header which close).length≤2048 ∧ (head which close).framing=.length 3 ∧
    MainRequestSpans.path (header which close++body which) (head which close)=WireSpec.ascii "/temp" ∧
    MainMethodSpec.decode (MainMethodBytes.token (header which close++body which) (head which close).method.2)=.post ∧
    AuthSpec.authorized (HeaderSpec.lookup (MainRequestSpans.raw (header which close++body which) (head which close) 3) (WireSpec.ascii "authorization") (MainRequestInputs.entries (head which close))) (WireSpec.ascii "dev-key")=(which != .unauth) ∧
    DecimalSpec.parse (TrimMath.trim (MainRequestSpans.body (header which close++body which) (head which close) 3))=(if which == .good then some 400#16 else none) ∧
    MainCloseSpec.mustClose (head which close).minor 1 (MainRequestSpans.raw (header which close++body which) (head which close) 3) (MainRequestInputs.entries (head which close))=close := by
  intro which close
  cases which <;> cases close <;> decide +kernel

theorem reply_eq (which : Case) (close : Bool) :
    MainTempReset.reply (wire which close) (header which close).length (head which close) 3=expected which := by
  unfold MainTempReset.reply
  rw [delivered]
  have fs := facts which close
  unfold TempHttpSpec.run
  rw [fs.2.2.2.2.1,fs.2.2.2.2.2.1]
  cases which <;> rfl

/-- Six real reset executions:200/400/401, each keep/close. Missing auth takes
    priority over the deliberately malformed body; refusals preserve App. -/
theorem execution (which : Case) (close : Bool) : ∃ n d after reads,
    Observed.Steps B img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩ reads
      (UartTxLoop.events (ResponseHeadSpec.bytes (expected which).status (expected which).mime (expected which).payload.length close)++UartTxLoop.events (expected which).payload) ∧
    Observed.input reads=header which close++body which ∧ d.pc=(if close then 0x80000978#32 else 0x800017be#32) ∧ d.mie_=false ∧
    AppState.At after (expected which).state ∧ Engine.InvariantAt after 0x80ffebbc#32 := by
  have fs := facts which close
  have accepted : (consume (wire which close) (header which close).length []).result=.done (head which close) := by rw [consumed]
  obtain ⟨n,d,after,selected,limit,trace,bytes,selection,pc,sp,fp,masked,app,inv⟩ := MainTempReset.contract
    MainInitWitness.core MainInitWitness.ram (wire which close) (plan which close) (header which close).length (head which close) 3 (plan which close)
    rfl (Or.inr rfl) rfl Blocking.stack_available fs.1 (valid which close _ _) accepted fs.2.1 (valid which close _ _)
    (by rw [delivered];exact fs.2.2.1) (by rw [delivered];exact fs.2.2.2.1)
    (headerSlots which) (bodySlots which) (fun _ => by rw [reply_eq];exact List.length_replicate) (by rw [reply_eq];exact List.length_replicate)
  rw [delivered] at bytes selection
  have selectedClose : selected=close := selection.trans fs.2.2.2.2.2.2
  rw [selectedClose,reply_eq] at trace
  rw [selectedClose] at bytes pc
  rw [reply_eq] at app
  exact ⟨n,d,after,_,trace,bytes,pc,masked,app,inv⟩
end E5R.Thermostat.MainTempResetWitness
