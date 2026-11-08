import Projects.thermostat.FormatCallbackData
import Projects.thermostat.AppendEffect
import Projects.thermostat.I16Display
import Projects.thermostat.FormatBool
import Projects.thermostat.FormatSlice
namespace E5R.Thermostat.FormatCallback
open E5R E5R.Thermostat

/-- Closed composition of the three real callback implementations installed
    by encode_reply. No callback's desired output is assumed in Data. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p fmt obj dst : Word)
    (cap pos : Nat) (value : FormatValue.Value)
    (h : FormatCallbackData.Data B ram p fmt obj dst cap pos value)
    (hp : c.pc = FormatValue.entry value) (hs : c.get 2 = p+160#32)
    (h10 : c.get 10 = FormatValue.pointer value) (h11 : c.get 11 = fmt)
    (hfit : pos+(FormatValue.bytes value).length ≤ cap)
    (hstr : B.inRam 0x80005c10#32 4 = false) (hchar : B.inRam 0x80005c14#32 4 = false)
    (hrom : ∀ i : Fin 100, ∀ unit : Bool, B.inRam (DigitTable.address i unit) 1 = false) :
    ∃ d n r, n ≤ 292 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧ FormatCursor.Returned c d ∧ d.get 10 = 0#32 ∧
      AppendEffect.Effect B ram r p obj dst 160 cap pos (FormatValue.bytes value) := by
  cases h with
  | signed ptr v hd =>
    change pos+(ReplyJson.signed v).length ≤ cap at hfit
    obtain ⟨d,n,r,hn,td,hr⟩ := I16Display.contract B c ram p ptr fmt obj dst cap pos v hd hp hs h10 h11 hfit hstr hchar hrom
    exact ⟨d,n,r,hn,td,hr.returned,by simpa only [Cursor.resultWord,ite_eq_left hfit] using hr.result,AppendEffect.of_append hr⟩
  | boolean ptr v hb hd =>
    change pos+(ReplyJson.boolean v).length ≤ cap at hfit
    obtain ⟨d,n,r,hn,td,hr⟩ := FormatBool.contract B c ram (p+96#32) fmt obj ptr dst 0x60000020#32 cap pos v hp
      (by simpa only [BitVec.add_assoc,show 96#32+64#32 = 160#32 by decide +kernel] using hs) h10 h11 hb hd hstr
    have hl : (ReplyJson.boolean v).length ≤ 5 := by cases v <;> decide
    refine ⟨d,n,r,by omega,td,hr.returned,?_,?_⟩
    · simpa only [Cursor.resultWord,ite_eq_left hfit] using hr.result
    · exact AppendEffect.widen (p := p) (off := 96) (size := 64) (total := 160) (AppendEffect.of_formatter hr) (by decide)
  | mode ptr v hm ha hptr hlen hd =>
    change pos+(ReplyJson.mode v).length ≤ cap at hfit
    obtain ⟨d,n,r,hn,td,hr⟩ := FormatSlice.contract B c ram (p+96#32) fmt obj ptr (ModeLiterals.pointer v) dst 0x60000020#32 cap pos (ReplyJson.mode v) hp
      (by simpa only [BitVec.add_assoc,show 96#32+64#32 = 160#32 by decide +kernel] using hs) h10 h11 hm ha hptr hlen hd hstr
    have hl : (ReplyJson.mode v).length ≤ 4 := by cases v <;> decide
    refine ⟨d,n,r,by omega,td,hr.returned,?_,?_⟩
    · simpa only [Cursor.resultWord,ite_eq_left hfit] using hr.result
    · exact AppendEffect.widen (p := p) (off := 96) (size := 64) (total := 160) (AppendEffect.of_formatter hr) (by decide)
end E5R.Thermostat.FormatCallback
