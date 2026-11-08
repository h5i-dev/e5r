import Projects.thermostat.ResponseHeadPrefixSpec
import Projects.thermostat.ResponseHeadBodyMath
namespace E5R.Thermostat.ResponseHeadPlan
open E5R E5R.Thermostat

def ctName (ct : List (BitVec 8)) := if ct=[] then [] else WireSpec.ascii "Content-Type: "
def ctEnd (ct : List (BitVec 8)) := if ct=[] then [] else WireSpec.ascii "\r\n"
def clName (status : Nat) := if ResponseHeadSpec.hasBody status then WireSpec.ascii "Content-Length: " else []
def decimal (status body : Nat) := if ResponseHeadSpec.hasBody status then ReplyJson.decimal body else []
def clEnd (status : Nat) := if ResponseHeadSpec.hasBody status then WireSpec.ascii "\r\n" else []

def chunks (status : Nat) (ct : List (BitVec 8)) (body : Nat) (close : Bool) : List (List (BitVec 8)) :=
  [ResponseHeadPrefixSpec.bytes status, WireSpec.ascii (ResponseHeadSpec.reason status), WireSpec.ascii "\r\n",
    ctName ct,ct,ctEnd ct,clName status,decimal status body,clEnd status,ResponseHeadSpec.connection close,WireSpec.ascii "\r\n"]

def part (status : Nat) (ct : List (BitVec 8)) (body : Nat) (close : Bool) (i : Nat) :=
  ((chunks status ct body close).take i).flatten

theorem all (status : Nat) (ct : List (BitVec 8)) (body : Nat) (close : Bool) :
    part status ct body close 11=ResponseHeadSpec.bytes status ct body close := by
  unfold part chunks ResponseHeadPrefixSpec.bytes ResponseHeadSpec.bytes ResponseHeadSpec.statusLine
    ResponseHeadSpec.contentType ResponseHeadSpec.contentLength ctName ctEnd clName decimal clEnd
  by_cases ht : ct=[] <;> cases hb : ResponseHeadSpec.hasBody status <;>
    simp [ht,hb,List.append_assoc]

theorem bounds (status : Nat) (ct : List (BitVec 8)) (body : Nat) (close : Bool)
    (hlo : 100≤status) (hhi : status≤599) (hct : ct.length≤16) (hbody : body≤832) :
    (∀ i : Fin 12, (part status ct body close i.val).length≤120) ∧
    (part status ct body close 7).length≤94 := by
  have hp := ResponseHeadPrefixSpec.length status hlo hhi
  have hr := ResponseHeadSpec.reason_bound status
  have hd := ReplyJsonBounds.decimal_length 3 body (by decide) (by change body<1000;omega)
  have hc : (ctName ct).length≤14 := by unfold ctName;split <;> decide +kernel
  have he : (ctEnd ct).length≤2 := by unfold ctEnd;split <;> decide +kernel
  have hn : (clName status).length≤16 := by unfold clName;split <;> decide +kernel
  have hd' : (decimal status body).length≤3 := by unfold decimal;split;exact hd;decide
  have hl : (clEnd status).length≤2 := by unfold clEnd;split <;> decide +kernel
  have hk : (ResponseHeadSpec.connection close).length≤19 := by cases close <;> decide +kernel
  have hcr : (WireSpec.ascii "\r\n").length=2 := by decide +kernel
  constructor
  · intro i
    have hi := i.isLt
    have hs : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 ∨ i.val=6 ∨ i.val=7 ∨ i.val=8 ∨ i.val=9 ∨ i.val=10 ∨ i.val=11 := by omega
    rcases hs with h|h|h|h|h|h|h|h|h|h|h|h <;>
      simp only [part,chunks,h,List.take,List.flatten,List.append_eq,List.length_append,List.length_nil,List.nil_append,List.append_nil] <;> omega
  · simp only [part,chunks,List.take,List.flatten,List.append_eq,List.length_append,List.length_nil,List.nil_append,List.append_nil]
    omega
end E5R.Thermostat.ResponseHeadPlan
