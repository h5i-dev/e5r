import Projects.thermostat.MainModeReset
import Projects.thermostat.MainConsumeCongr
import Projects.thermostat.MainInitWitness
import Projects.thermostat.Blocking
import Projects.thermostat.MainChunkStreamingWitness
import Projects.thermostat.UartWriteWitness
set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 5000000
namespace E5R.Thermostat.MainModeResetWitness
open E5R E5R.Thermostat HttpRequestSpec MainHeaderStreamSpec
abbrev B := UartPlatform.board
inductive Case where
  | good | malformed | autoMode | unauth
  deriving DecidableEq
def header (auth : Bool) : List (BitVec 8) := if auth then [80,85,84,32,47,109,111,100,101,32,72,84,84,80,47,49,46,49,13,10,72,111,115,116,58,120,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,52,13,10,65,117,116,104,111,114,105,122,97,116,105,111,110,58,66,101,97,114,101,114,32,100,101,118,45,107,101,121,13,10,13,10] else [80,85,84,32,47,109,111,100,101,32,72,84,84,80,47,49,46,49,13,10,72,111,115,116,58,120,13,10,67,111,110,116,101,110,116,45,76,101,110,103,116,104,58,52,13,10,13,10]
def head (auth : Bool) : Head := if auth then ⟨(0,3),(4,9),1,[⟨20,24,25,26⟩,⟨28,42,43,44⟩,⟨46,59,60,74⟩],78,.length 4⟩ else ⟨(0,3),(4,9),1,[⟨20,24,25,26⟩,⟨28,42,43,44⟩],48,.length 4⟩
def authenticated (which : Case) : Bool := which != .unauth
def body : Case → List (BitVec 8)
  | .good => [104,101,97,116]
  | .autoMode => [97,117,116,111]
  | _ => [110,111,112,101]
def wire (which : Case) (k : Nat) : BitVec 8 := (header (authenticated which)++body which)[k]?.getD 0#8

theorem consumed_unauth : consume (wire .unauth) (header false).length []=⟨(header false).length,header false,.done (head false)⟩ := by
  have run47 : consume (wire .unauth) 1 ((header false).take 47)=⟨1,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 47++[wire .unauth ((header false).take 47).length]=(header false).take 48 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 48) 1024 1024=.done (head false) := by decide +kernel
    rw [consume,nextByte,parsed]
    congr 1
  have run46 : consume (wire .unauth) 2 ((header false).take 46)=⟨2,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 46++[wire .unauth ((header false).take 46).length]=(header false).take 47 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 47) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run47]
  have run45 : consume (wire .unauth) 3 ((header false).take 45)=⟨3,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 45++[wire .unauth ((header false).take 45).length]=(header false).take 46 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 46) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run46]
  have run44 : consume (wire .unauth) 4 ((header false).take 44)=⟨4,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 44++[wire .unauth ((header false).take 44).length]=(header false).take 45 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 45) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run45]
  have run43 : consume (wire .unauth) 5 ((header false).take 43)=⟨5,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 43++[wire .unauth ((header false).take 43).length]=(header false).take 44 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 44) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run44]
  have run42 : consume (wire .unauth) 6 ((header false).take 42)=⟨6,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 42++[wire .unauth ((header false).take 42).length]=(header false).take 43 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 43) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run43]
  have run41 : consume (wire .unauth) 7 ((header false).take 41)=⟨7,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 41++[wire .unauth ((header false).take 41).length]=(header false).take 42 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 42) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run42]
  have run40 : consume (wire .unauth) 8 ((header false).take 40)=⟨8,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 40++[wire .unauth ((header false).take 40).length]=(header false).take 41 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 41) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run41]
  have run39 : consume (wire .unauth) 9 ((header false).take 39)=⟨9,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 39++[wire .unauth ((header false).take 39).length]=(header false).take 40 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 40) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run40]
  have run38 : consume (wire .unauth) 10 ((header false).take 38)=⟨10,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 38++[wire .unauth ((header false).take 38).length]=(header false).take 39 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 39) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run39]
  have run37 : consume (wire .unauth) 11 ((header false).take 37)=⟨11,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 37++[wire .unauth ((header false).take 37).length]=(header false).take 38 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 38) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run38]
  have run36 : consume (wire .unauth) 12 ((header false).take 36)=⟨12,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 36++[wire .unauth ((header false).take 36).length]=(header false).take 37 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 37) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run37]
  have run35 : consume (wire .unauth) 13 ((header false).take 35)=⟨13,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 35++[wire .unauth ((header false).take 35).length]=(header false).take 36 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 36) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run36]
  have run34 : consume (wire .unauth) 14 ((header false).take 34)=⟨14,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 34++[wire .unauth ((header false).take 34).length]=(header false).take 35 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 35) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run35]
  have run33 : consume (wire .unauth) 15 ((header false).take 33)=⟨15,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 33++[wire .unauth ((header false).take 33).length]=(header false).take 34 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 34) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run34]
  have run32 : consume (wire .unauth) 16 ((header false).take 32)=⟨16,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 32++[wire .unauth ((header false).take 32).length]=(header false).take 33 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 33) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run33]
  have run31 : consume (wire .unauth) 17 ((header false).take 31)=⟨17,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 31++[wire .unauth ((header false).take 31).length]=(header false).take 32 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 32) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run32]
  have run30 : consume (wire .unauth) 18 ((header false).take 30)=⟨18,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 30++[wire .unauth ((header false).take 30).length]=(header false).take 31 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 31) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run31]
  have run29 : consume (wire .unauth) 19 ((header false).take 29)=⟨19,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 29++[wire .unauth ((header false).take 29).length]=(header false).take 30 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 30) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run30]
  have run28 : consume (wire .unauth) 20 ((header false).take 28)=⟨20,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 28++[wire .unauth ((header false).take 28).length]=(header false).take 29 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 29) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run29]
  have run27 : consume (wire .unauth) 21 ((header false).take 27)=⟨21,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 27++[wire .unauth ((header false).take 27).length]=(header false).take 28 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 28) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run28]
  have run26 : consume (wire .unauth) 22 ((header false).take 26)=⟨22,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 26++[wire .unauth ((header false).take 26).length]=(header false).take 27 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 27) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run27]
  have run25 : consume (wire .unauth) 23 ((header false).take 25)=⟨23,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 25++[wire .unauth ((header false).take 25).length]=(header false).take 26 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 26) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run26]
  have run24 : consume (wire .unauth) 24 ((header false).take 24)=⟨24,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 24++[wire .unauth ((header false).take 24).length]=(header false).take 25 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 25) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run25]
  have run23 : consume (wire .unauth) 25 ((header false).take 23)=⟨25,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 23++[wire .unauth ((header false).take 23).length]=(header false).take 24 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 24) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run24]
  have run22 : consume (wire .unauth) 26 ((header false).take 22)=⟨26,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 22++[wire .unauth ((header false).take 22).length]=(header false).take 23 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 23) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run23]
  have run21 : consume (wire .unauth) 27 ((header false).take 21)=⟨27,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 21++[wire .unauth ((header false).take 21).length]=(header false).take 22 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 22) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run22]
  have run20 : consume (wire .unauth) 28 ((header false).take 20)=⟨28,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 20++[wire .unauth ((header false).take 20).length]=(header false).take 21 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 21) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run21]
  have run19 : consume (wire .unauth) 29 ((header false).take 19)=⟨29,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 19++[wire .unauth ((header false).take 19).length]=(header false).take 20 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 20) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run20]
  have run18 : consume (wire .unauth) 30 ((header false).take 18)=⟨30,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 18++[wire .unauth ((header false).take 18).length]=(header false).take 19 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 19) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run19]
  have run17 : consume (wire .unauth) 31 ((header false).take 17)=⟨31,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 17++[wire .unauth ((header false).take 17).length]=(header false).take 18 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 18) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run18]
  have run16 : consume (wire .unauth) 32 ((header false).take 16)=⟨32,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 16++[wire .unauth ((header false).take 16).length]=(header false).take 17 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 17) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run17]
  have run15 : consume (wire .unauth) 33 ((header false).take 15)=⟨33,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 15++[wire .unauth ((header false).take 15).length]=(header false).take 16 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 16) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run16]
  have run14 : consume (wire .unauth) 34 ((header false).take 14)=⟨34,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 14++[wire .unauth ((header false).take 14).length]=(header false).take 15 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 15) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run15]
  have run13 : consume (wire .unauth) 35 ((header false).take 13)=⟨35,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 13++[wire .unauth ((header false).take 13).length]=(header false).take 14 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 14) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run14]
  have run12 : consume (wire .unauth) 36 ((header false).take 12)=⟨36,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 12++[wire .unauth ((header false).take 12).length]=(header false).take 13 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 13) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run13]
  have run11 : consume (wire .unauth) 37 ((header false).take 11)=⟨37,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 11++[wire .unauth ((header false).take 11).length]=(header false).take 12 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 12) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run12]
  have run10 : consume (wire .unauth) 38 ((header false).take 10)=⟨38,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 10++[wire .unauth ((header false).take 10).length]=(header false).take 11 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 11) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run11]
  have run9 : consume (wire .unauth) 39 ((header false).take 9)=⟨39,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 9++[wire .unauth ((header false).take 9).length]=(header false).take 10 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 10) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run10]
  have run8 : consume (wire .unauth) 40 ((header false).take 8)=⟨40,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 8++[wire .unauth ((header false).take 8).length]=(header false).take 9 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 9) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run9]
  have run7 : consume (wire .unauth) 41 ((header false).take 7)=⟨41,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 7++[wire .unauth ((header false).take 7).length]=(header false).take 8 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 8) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run8]
  have run6 : consume (wire .unauth) 42 ((header false).take 6)=⟨42,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 6++[wire .unauth ((header false).take 6).length]=(header false).take 7 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 7) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run7]
  have run5 : consume (wire .unauth) 43 ((header false).take 5)=⟨43,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 5++[wire .unauth ((header false).take 5).length]=(header false).take 6 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 6) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run6]
  have run4 : consume (wire .unauth) 44 ((header false).take 4)=⟨44,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 4++[wire .unauth ((header false).take 4).length]=(header false).take 5 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 5) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run5]
  have run3 : consume (wire .unauth) 45 ((header false).take 3)=⟨45,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 3++[wire .unauth ((header false).take 3).length]=(header false).take 4 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 4) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run4]
  have run2 : consume (wire .unauth) 46 ((header false).take 2)=⟨46,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 2++[wire .unauth ((header false).take 2).length]=(header false).take 3 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 3) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run3]
  have run1 : consume (wire .unauth) 47 ((header false).take 1)=⟨47,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 1++[wire .unauth ((header false).take 1).length]=(header false).take 2 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 2) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run2]
  have run0 : consume (wire .unauth) 48 ((header false).take 0)=⟨48,header false,.done (head false)⟩ := by
    have nextByte : (header false).take 0++[wire .unauth ((header false).take 0).length]=(header false).take 1 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header false).take 1) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run1]
  exact run0

theorem consumed_good : consume (wire .good) (header true).length []=⟨(header true).length,header true,.done (head true)⟩ := by
  have run77 : consume (wire .good) 1 ((header true).take 77)=⟨1,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 77++[wire .good ((header true).take 77).length]=(header true).take 78 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 78) 1024 1024=.done (head true) := by decide +kernel
    rw [consume,nextByte,parsed]
    congr 1
  have run76 : consume (wire .good) 2 ((header true).take 76)=⟨2,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 76++[wire .good ((header true).take 76).length]=(header true).take 77 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 77) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run77]
  have run75 : consume (wire .good) 3 ((header true).take 75)=⟨3,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 75++[wire .good ((header true).take 75).length]=(header true).take 76 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 76) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run76]
  have run74 : consume (wire .good) 4 ((header true).take 74)=⟨4,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 74++[wire .good ((header true).take 74).length]=(header true).take 75 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 75) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run75]
  have run73 : consume (wire .good) 5 ((header true).take 73)=⟨5,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 73++[wire .good ((header true).take 73).length]=(header true).take 74 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 74) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run74]
  have run72 : consume (wire .good) 6 ((header true).take 72)=⟨6,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 72++[wire .good ((header true).take 72).length]=(header true).take 73 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 73) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run73]
  have run71 : consume (wire .good) 7 ((header true).take 71)=⟨7,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 71++[wire .good ((header true).take 71).length]=(header true).take 72 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 72) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run72]
  have run70 : consume (wire .good) 8 ((header true).take 70)=⟨8,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 70++[wire .good ((header true).take 70).length]=(header true).take 71 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 71) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run71]
  have run69 : consume (wire .good) 9 ((header true).take 69)=⟨9,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 69++[wire .good ((header true).take 69).length]=(header true).take 70 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 70) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run70]
  have run68 : consume (wire .good) 10 ((header true).take 68)=⟨10,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 68++[wire .good ((header true).take 68).length]=(header true).take 69 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 69) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run69]
  have run67 : consume (wire .good) 11 ((header true).take 67)=⟨11,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 67++[wire .good ((header true).take 67).length]=(header true).take 68 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 68) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run68]
  have run66 : consume (wire .good) 12 ((header true).take 66)=⟨12,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 66++[wire .good ((header true).take 66).length]=(header true).take 67 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 67) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run67]
  have run65 : consume (wire .good) 13 ((header true).take 65)=⟨13,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 65++[wire .good ((header true).take 65).length]=(header true).take 66 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 66) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run66]
  have run64 : consume (wire .good) 14 ((header true).take 64)=⟨14,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 64++[wire .good ((header true).take 64).length]=(header true).take 65 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 65) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run65]
  have run63 : consume (wire .good) 15 ((header true).take 63)=⟨15,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 63++[wire .good ((header true).take 63).length]=(header true).take 64 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 64) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run64]
  have run62 : consume (wire .good) 16 ((header true).take 62)=⟨16,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 62++[wire .good ((header true).take 62).length]=(header true).take 63 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 63) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run63]
  have run61 : consume (wire .good) 17 ((header true).take 61)=⟨17,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 61++[wire .good ((header true).take 61).length]=(header true).take 62 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 62) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run62]
  have run60 : consume (wire .good) 18 ((header true).take 60)=⟨18,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 60++[wire .good ((header true).take 60).length]=(header true).take 61 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 61) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run61]
  have run59 : consume (wire .good) 19 ((header true).take 59)=⟨19,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 59++[wire .good ((header true).take 59).length]=(header true).take 60 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 60) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run60]
  have run58 : consume (wire .good) 20 ((header true).take 58)=⟨20,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 58++[wire .good ((header true).take 58).length]=(header true).take 59 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 59) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run59]
  have run57 : consume (wire .good) 21 ((header true).take 57)=⟨21,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 57++[wire .good ((header true).take 57).length]=(header true).take 58 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 58) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run58]
  have run56 : consume (wire .good) 22 ((header true).take 56)=⟨22,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 56++[wire .good ((header true).take 56).length]=(header true).take 57 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 57) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run57]
  have run55 : consume (wire .good) 23 ((header true).take 55)=⟨23,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 55++[wire .good ((header true).take 55).length]=(header true).take 56 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 56) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run56]
  have run54 : consume (wire .good) 24 ((header true).take 54)=⟨24,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 54++[wire .good ((header true).take 54).length]=(header true).take 55 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 55) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run55]
  have run53 : consume (wire .good) 25 ((header true).take 53)=⟨25,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 53++[wire .good ((header true).take 53).length]=(header true).take 54 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 54) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run54]
  have run52 : consume (wire .good) 26 ((header true).take 52)=⟨26,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 52++[wire .good ((header true).take 52).length]=(header true).take 53 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 53) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run53]
  have run51 : consume (wire .good) 27 ((header true).take 51)=⟨27,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 51++[wire .good ((header true).take 51).length]=(header true).take 52 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 52) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run52]
  have run50 : consume (wire .good) 28 ((header true).take 50)=⟨28,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 50++[wire .good ((header true).take 50).length]=(header true).take 51 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 51) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run51]
  have run49 : consume (wire .good) 29 ((header true).take 49)=⟨29,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 49++[wire .good ((header true).take 49).length]=(header true).take 50 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 50) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run50]
  have run48 : consume (wire .good) 30 ((header true).take 48)=⟨30,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 48++[wire .good ((header true).take 48).length]=(header true).take 49 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 49) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run49]
  have run47 : consume (wire .good) 31 ((header true).take 47)=⟨31,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 47++[wire .good ((header true).take 47).length]=(header true).take 48 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 48) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run48]
  have run46 : consume (wire .good) 32 ((header true).take 46)=⟨32,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 46++[wire .good ((header true).take 46).length]=(header true).take 47 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 47) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run47]
  have run45 : consume (wire .good) 33 ((header true).take 45)=⟨33,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 45++[wire .good ((header true).take 45).length]=(header true).take 46 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 46) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run46]
  have run44 : consume (wire .good) 34 ((header true).take 44)=⟨34,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 44++[wire .good ((header true).take 44).length]=(header true).take 45 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 45) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run45]
  have run43 : consume (wire .good) 35 ((header true).take 43)=⟨35,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 43++[wire .good ((header true).take 43).length]=(header true).take 44 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 44) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run44]
  have run42 : consume (wire .good) 36 ((header true).take 42)=⟨36,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 42++[wire .good ((header true).take 42).length]=(header true).take 43 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 43) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run43]
  have run41 : consume (wire .good) 37 ((header true).take 41)=⟨37,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 41++[wire .good ((header true).take 41).length]=(header true).take 42 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 42) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run42]
  have run40 : consume (wire .good) 38 ((header true).take 40)=⟨38,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 40++[wire .good ((header true).take 40).length]=(header true).take 41 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 41) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run41]
  have run39 : consume (wire .good) 39 ((header true).take 39)=⟨39,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 39++[wire .good ((header true).take 39).length]=(header true).take 40 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 40) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run40]
  have run38 : consume (wire .good) 40 ((header true).take 38)=⟨40,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 38++[wire .good ((header true).take 38).length]=(header true).take 39 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 39) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run39]
  have run37 : consume (wire .good) 41 ((header true).take 37)=⟨41,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 37++[wire .good ((header true).take 37).length]=(header true).take 38 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 38) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run38]
  have run36 : consume (wire .good) 42 ((header true).take 36)=⟨42,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 36++[wire .good ((header true).take 36).length]=(header true).take 37 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 37) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run37]
  have run35 : consume (wire .good) 43 ((header true).take 35)=⟨43,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 35++[wire .good ((header true).take 35).length]=(header true).take 36 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 36) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run36]
  have run34 : consume (wire .good) 44 ((header true).take 34)=⟨44,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 34++[wire .good ((header true).take 34).length]=(header true).take 35 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 35) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run35]
  have run33 : consume (wire .good) 45 ((header true).take 33)=⟨45,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 33++[wire .good ((header true).take 33).length]=(header true).take 34 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 34) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run34]
  have run32 : consume (wire .good) 46 ((header true).take 32)=⟨46,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 32++[wire .good ((header true).take 32).length]=(header true).take 33 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 33) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run33]
  have run31 : consume (wire .good) 47 ((header true).take 31)=⟨47,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 31++[wire .good ((header true).take 31).length]=(header true).take 32 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 32) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run32]
  have run30 : consume (wire .good) 48 ((header true).take 30)=⟨48,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 30++[wire .good ((header true).take 30).length]=(header true).take 31 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 31) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run31]
  have run29 : consume (wire .good) 49 ((header true).take 29)=⟨49,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 29++[wire .good ((header true).take 29).length]=(header true).take 30 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 30) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run30]
  have run28 : consume (wire .good) 50 ((header true).take 28)=⟨50,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 28++[wire .good ((header true).take 28).length]=(header true).take 29 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 29) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run29]
  have run27 : consume (wire .good) 51 ((header true).take 27)=⟨51,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 27++[wire .good ((header true).take 27).length]=(header true).take 28 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 28) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run28]
  have run26 : consume (wire .good) 52 ((header true).take 26)=⟨52,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 26++[wire .good ((header true).take 26).length]=(header true).take 27 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 27) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run27]
  have run25 : consume (wire .good) 53 ((header true).take 25)=⟨53,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 25++[wire .good ((header true).take 25).length]=(header true).take 26 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 26) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run26]
  have run24 : consume (wire .good) 54 ((header true).take 24)=⟨54,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 24++[wire .good ((header true).take 24).length]=(header true).take 25 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 25) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run25]
  have run23 : consume (wire .good) 55 ((header true).take 23)=⟨55,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 23++[wire .good ((header true).take 23).length]=(header true).take 24 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 24) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run24]
  have run22 : consume (wire .good) 56 ((header true).take 22)=⟨56,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 22++[wire .good ((header true).take 22).length]=(header true).take 23 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 23) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run23]
  have run21 : consume (wire .good) 57 ((header true).take 21)=⟨57,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 21++[wire .good ((header true).take 21).length]=(header true).take 22 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 22) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run22]
  have run20 : consume (wire .good) 58 ((header true).take 20)=⟨58,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 20++[wire .good ((header true).take 20).length]=(header true).take 21 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 21) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run21]
  have run19 : consume (wire .good) 59 ((header true).take 19)=⟨59,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 19++[wire .good ((header true).take 19).length]=(header true).take 20 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 20) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run20]
  have run18 : consume (wire .good) 60 ((header true).take 18)=⟨60,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 18++[wire .good ((header true).take 18).length]=(header true).take 19 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 19) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run19]
  have run17 : consume (wire .good) 61 ((header true).take 17)=⟨61,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 17++[wire .good ((header true).take 17).length]=(header true).take 18 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 18) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run18]
  have run16 : consume (wire .good) 62 ((header true).take 16)=⟨62,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 16++[wire .good ((header true).take 16).length]=(header true).take 17 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 17) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run17]
  have run15 : consume (wire .good) 63 ((header true).take 15)=⟨63,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 15++[wire .good ((header true).take 15).length]=(header true).take 16 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 16) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run16]
  have run14 : consume (wire .good) 64 ((header true).take 14)=⟨64,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 14++[wire .good ((header true).take 14).length]=(header true).take 15 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 15) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run15]
  have run13 : consume (wire .good) 65 ((header true).take 13)=⟨65,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 13++[wire .good ((header true).take 13).length]=(header true).take 14 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 14) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run14]
  have run12 : consume (wire .good) 66 ((header true).take 12)=⟨66,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 12++[wire .good ((header true).take 12).length]=(header true).take 13 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 13) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run13]
  have run11 : consume (wire .good) 67 ((header true).take 11)=⟨67,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 11++[wire .good ((header true).take 11).length]=(header true).take 12 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 12) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run12]
  have run10 : consume (wire .good) 68 ((header true).take 10)=⟨68,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 10++[wire .good ((header true).take 10).length]=(header true).take 11 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 11) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run11]
  have run9 : consume (wire .good) 69 ((header true).take 9)=⟨69,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 9++[wire .good ((header true).take 9).length]=(header true).take 10 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 10) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run10]
  have run8 : consume (wire .good) 70 ((header true).take 8)=⟨70,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 8++[wire .good ((header true).take 8).length]=(header true).take 9 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 9) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run9]
  have run7 : consume (wire .good) 71 ((header true).take 7)=⟨71,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 7++[wire .good ((header true).take 7).length]=(header true).take 8 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 8) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run8]
  have run6 : consume (wire .good) 72 ((header true).take 6)=⟨72,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 6++[wire .good ((header true).take 6).length]=(header true).take 7 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 7) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run7]
  have run5 : consume (wire .good) 73 ((header true).take 5)=⟨73,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 5++[wire .good ((header true).take 5).length]=(header true).take 6 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 6) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run6]
  have run4 : consume (wire .good) 74 ((header true).take 4)=⟨74,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 4++[wire .good ((header true).take 4).length]=(header true).take 5 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 5) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run5]
  have run3 : consume (wire .good) 75 ((header true).take 3)=⟨75,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 3++[wire .good ((header true).take 3).length]=(header true).take 4 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 4) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run4]
  have run2 : consume (wire .good) 76 ((header true).take 2)=⟨76,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 2++[wire .good ((header true).take 2).length]=(header true).take 3 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 3) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run3]
  have run1 : consume (wire .good) 77 ((header true).take 1)=⟨77,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 1++[wire .good ((header true).take 1).length]=(header true).take 2 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 2) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run2]
  have run0 : consume (wire .good) 78 ((header true).take 0)=⟨78,header true,.done (head true)⟩ := by
    have nextByte : (header true).take 0++[wire .good ((header true).take 0).length]=(header true).take 1 := by decide +kernel
    have parsed : HttpRequestBytes.parse ((header true).take 1) 1024 1024=.incomplete := by decide +kernel
    rw [consume,nextByte,parsed]
    rw [run1]
  exact run0

theorem consumed (which : Case) : consume (wire which) (header (authenticated which)).length []=
    ⟨(header (authenticated which)).length,header (authenticated which),.done (head (authenticated which))⟩ := by
  have same (which : Case) (ha : authenticated which=true) : consume (wire which) (header true).length []=consume (wire .good) (header true).length [] := by
    apply consume_congr
    intro k lower upper
    simp only [List.length_nil,Nat.zero_add] at upper
    unfold wire
    rw [ha]
    change ((header true++body which)[k]?).getD 0#8=((header true++body .good)[k]?).getD 0#8
    rw [List.getElem?_append_left upper,List.getElem?_append_left upper]
  cases which with
  | good => exact consumed_good
  | malformed => exact (same .malformed rfl).trans consumed_good
  | autoMode => exact (same .autoMode rfl).trans consumed_good
  | unauth => exact consumed_unauth

def plan (which : Case) : ChunkReceivePlan.Plan :=
  ⟨fun _ => [0#32,2#32],fun _ => 129#32,fun k => BitVec.ofNat 32 (wire which k).toNat⟩
theorem valid (which : Case) (first count : Nat) : ChunkReceivePlan.Valid (plan which) (wire which) first count := by
  intro k hk he
  refine ⟨?_,(by change MainChunkPoll.mask 129#32≠0#32;decide +kernel),MainChunkStreamingWitness.byte_roundtrip (wire which k)⟩
  intro status hs
  change status∈[0#32,2#32] at hs
  have casesStatus : status=0#32 ∨ status=2#32 := by simpa using hs
  rcases casesStatus with zero|two <;> subst status <;> decide +kernel

def state : Spec.Snapshot := {Spec.initial with mode:=.heat,heater:=true}
def autoState : Spec.Snapshot := {Spec.initial with mode:=.auto}
def expected : Case → ApiWriteHttpSpec.Reply
  | .good => ⟨state,200,WireSpec.ascii "application/json",ReplyJson.snapshot state⟩
  | .malformed => ⟨Spec.initial,400,[],[]⟩
  | .autoMode => ⟨autoState,200,WireSpec.ascii "application/json",ReplyJson.snapshot autoState⟩
  | .unauth => ⟨Spec.initial,401,[],[]⟩
def headerSlots (which : Case) (close : Bool) := List.replicate
  (ResponseHeadSpec.bytes (expected which).status (expected which).mime (expected which).payload.length close).length UartWriteWitness.slot1
def bodySlots (which : Case) := List.replicate (expected which).payload.length UartWriteWitness.slot1

theorem delivered (which : Case) : MainModeReset.received (wire which) (header (authenticated which)).length (head (authenticated which)) 4=header (authenticated which)++body which := by
  unfold MainModeReset.received MainTempSuccessReset.received
  rw [consumed]
  cases which <;> decide +kernel

theorem facts : ∀ which : Case, (header (authenticated which)).length≤2048 ∧ (head (authenticated which)).framing=.length 4 ∧
    MainRequestSpans.path (header (authenticated which)++body which) (head (authenticated which))=WireSpec.ascii "/mode" ∧
    MainMethodSpec.decode (MainMethodBytes.token (header (authenticated which)++body which) (head (authenticated which)).method.2)=.put ∧
    MainCloseSpec.mustClose (head (authenticated which)).minor 1 (MainRequestSpans.raw (header (authenticated which)++body which) (head (authenticated which)) 4) (MainRequestInputs.entries (head (authenticated which)))=false := by
  intro which;cases which <;> decide +kernel

theorem reply_eq (which : Case) : MainModeReset.reply (wire which) (header (authenticated which)).length (head (authenticated which)) 4=expected which := by
  unfold MainModeReset.reply
  rw [delivered]
  cases which <;> rfl

/-- Real reset/UART executions ofheat/auto200,400,401 with the actual distinct
    mode future/return. Both valid modes commit; early refusals preserve state. -/
theorem execution (which : Case) : ∃ n d after reads,
    Observed.Steps B img n ⟨MainInitWitness.core,MainInitWitness.ram⟩ ⟨d,after⟩ reads
      (UartTxLoop.events (ResponseHeadSpec.bytes (expected which).status (expected which).mime (expected which).payload.length false)++UartTxLoop.events (expected which).payload) ∧
    Observed.input reads=header (authenticated which)++body which ∧ d.pc=0x800017be#32 ∧ d.mie_=false ∧
    AppState.At after (expected which).state ∧ Engine.InvariantAt after 0x80ffebbc#32 := by
  have fs := facts which
  have accepted : (consume (wire which) (header (authenticated which)).length []).result=.done (head (authenticated which)) := by rw [consumed]
  obtain ⟨n,d,after,selected,limit,trace,bytes,selection,pc,sp,fp,masked,app,inv⟩ := MainModeReset.contract
    MainInitWitness.core MainInitWitness.ram (wire which) (plan which) (header (authenticated which)).length (head (authenticated which)) 4 (plan which)
    rfl (Or.inr rfl) rfl Blocking.stack_available fs.1 (valid which _ _) accepted fs.2.1 (valid which _ _)
    (by rw [delivered];exact fs.2.2.1) (by rw [delivered];exact fs.2.2.2.1)
    (headerSlots which) (bodySlots which) (fun _ => by rw [reply_eq];exact List.length_replicate) (by rw [reply_eq];exact List.length_replicate)
  rw [delivered] at bytes selection
  have selectedClose : selected=false := selection.trans fs.2.2.2.2
  rw [selectedClose,reply_eq] at trace
  rw [selectedClose] at bytes pc
  rw [reply_eq] at app
  exact ⟨n,d,after,_,trace,bytes,pc,masked,app,inv⟩
end E5R.Thermostat.MainModeResetWitness
