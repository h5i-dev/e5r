import Projects.thermostat.ReplyJsonBounds
namespace E5R.Thermostat.ResponseHeadSpec
open E5R E5R.Thermostat

/-- Application reason phrases; unlisted status codes have an empty reason.
    HTTP status-line/message framing follows RFC 9112 sections 2, 4 and 6. -/
def reason : Nat → String
  | 200 => "OK" | 201 => "Created" | 204 => "No Content"
  | 400 => "Bad Request" | 401 => "Unauthorized" | 403 => "Forbidden"
  | 404 => "Not Found" | 405 => "Method Not Allowed" | 408 => "Request Timeout"
  | 409 => "Conflict" | 413 => "Content Too Large" | 414 => "URI Too Long"
  | 422 => "Unprocessable Content" | 431 => "Request Header Fields Too Large"
  | 500 => "Internal Server Error" | 501 => "Not Implemented"
  | 503 => "Service Unavailable" | 505 => "HTTP Version Not Supported" | _ => ""

def fieldByte (b : BitVec 8) : Prop := b.toNat=9 ∨ (32≤b.toNat ∧ b.toNat≠127)
instance (b : BitVec 8) : Decidable (fieldByte b) := inferInstanceAs (Decidable (_ ∨ (_ ∧ _)))
def Field (bs : List (BitVec 8)) : Prop := ∀ b ∈ bs, fieldByte b
instance (bs : List (BitVec 8)) : Decidable (Field bs) := inferInstanceAs (Decidable (∀ b ∈ bs, fieldByte b))

def hasBody (status : Nat) : Bool := decide (200≤status ∧ status≠204 ∧ status≠304)

def statusLine (status : Nat) : List (BitVec 8) :=
  WireSpec.ascii "HTTP/1.1 " ++ ReplyJson.decimal status ++ WireSpec.ascii " " ++
  WireSpec.ascii (reason status) ++ WireSpec.ascii "\r\n"

def contentType (ct : List (BitVec 8)) : List (BitVec 8) :=
  if ct=[] then [] else WireSpec.ascii "Content-Type: " ++ ct ++ WireSpec.ascii "\r\n"

def contentLength (status bodyLen : Nat) : List (BitVec 8) :=
  if hasBody status then WireSpec.ascii "Content-Length: " ++ ReplyJson.decimal bodyLen ++ WireSpec.ascii "\r\n" else []

def connection (close : Bool) : List (BitVec 8) := if close then WireSpec.ascii "Connection: close\r\n" else []

def bytes (status : Nat) (ct : List (BitVec 8)) (bodyLen : Nat) (close : Bool) :=
  statusLine status ++ contentType ct ++ contentLength status bodyLen ++ connection close ++ WireSpec.ascii "\r\n"

def encode (cap status : Nat) (ct : List (BitVec 8)) (bodyLen : Nat) (close : Bool) : Option (List (BitVec 8)) :=
  if 100≤status ∧ status≤599 ∧ Field ct ∧ (bytes status ct bodyLen close).length≤cap
  then some (bytes status ct bodyLen close) else none

/-- HEAD retains the representation length in its header while sending no body.
    The other no-body cases are 1xx, 204 and 304 (RFC 9112 section 6.3). -/
def body (status : Nat) (head : Bool) (payload : List (BitVec 8)) :=
  if head || !hasBody status then [] else payload

theorem field_controls : ¬fieldByte 0#8 ∧ ¬fieldByte 10#8 ∧ ¬fieldByte 13#8 ∧ ¬fieldByte 127#8 ∧ fieldByte 9#8 := by
  decide +kernel

theorem field_no_crlf {ct} (hf : Field ct) : 13#8∉ct ∧ 10#8∉ct := by
  constructor
  · intro h;exact field_controls.2.2.1 (hf _ h)
  · intro h;exact field_controls.2.1 (hf _ h)

theorem reason_bound (status : Nat) : (WireSpec.ascii (reason status)).length≤31 := by
  unfold reason
  split <;> decide +kernel

theorem head_empty (status : Nat) (payload : List (BitVec 8)) : body status true payload=[] := by rfl

theorem no_body (status : Nat) (head : Bool) (payload : List (BitVec 8))
    (h : hasBody status=false) : body status head payload=[] := by
  simp [body,h]

theorem body_statuses : hasBody 100=false ∧ hasBody 199=false ∧ hasBody 204=false ∧ hasBody 304=false ∧ hasBody 200=true := by
  decide +kernel

theorem json_field : Field (WireSpec.ascii "application/json") := by decide +kernel
theorem length (status : Nat) (ct : List (BitVec 8)) (bodyLen : Nat) (close : Bool) :
    (bytes status ct bodyLen close).length=
      14+(ReplyJson.decimal status).length+(WireSpec.ascii (reason status)).length+
      (if ct=[] then 0 else 16+ct.length)+
      (if hasBody status then 18+(ReplyJson.decimal bodyLen).length else 0)+(if close then 19 else 0) := by
  have h9 : (WireSpec.ascii "HTTP/1.1 ").length=9 := by decide
  have h1 : (WireSpec.ascii " ").length=1 := by decide
  have h2 : (WireSpec.ascii "\r\n").length=2 := by decide
  have h14 : (WireSpec.ascii "Content-Type: ").length=14 := by decide
  have h16 : (WireSpec.ascii "Content-Length: ").length=16 := by decide
  have h19 : (WireSpec.ascii "Connection: close\r\n").length=19 := by decide
  by_cases ht : ct=[] <;> cases hb : hasBody status <;> cases close <;>
    simp only [bytes,statusLine,contentType,contentLength,connection,ht,hb,ite_true,ite_false,Bool.false_eq_true,List.length_append,List.length_nil,h9,h1,h2,h14,h16,h19] <;> omega

/-- The firmware reserves 192 header bytes. Every valid status, a MIME value
    at most 16 bytes, and every RV32 body length fit within 127 bytes. -/
theorem fits_header_room (status : Nat) (ct : List (BitVec 8)) (bodyLen : Word) (close : Bool)
    (hs : status≤599) (hct : ct.length≤16) : (bytes status ct bodyLen.toNat close).length≤127 := by
  have hstatus := ReplyJsonBounds.decimal_length 3 status (by decide) (by change status<1000;omega)
  have hbody := ReplyJsonBounds.decimal_length 10 bodyLen.toNat (by decide) (by have hb := bodyLen.isLt;change bodyLen.toNat<10000000000;omega)
  have hr := reason_bound status
  rw [length]
  split <;> split <;> cases close <;> simp only [ite_true,Bool.false_eq_true,ite_false] <;> omega
theorem encode_header_room (status : Nat) (ct : List (BitVec 8)) (bodyLen : Word) (close : Bool)
    (hlo : 100≤status) (hhi : status≤599) (hct : ct.length≤16) (hf : Field ct) :
    encode 192 status ct bodyLen.toNat close=some (bytes status ct bodyLen.toNat close) := by
  have hl := fits_header_room status ct bodyLen close hhi hct
  rw [encode,if_pos ⟨hlo,hhi,hf,by omega⟩]

theorem json_ok_fixture : bytes 200 (WireSpec.ascii "application/json") 77 true=
    WireSpec.ascii "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: 77\r\nConnection: close\r\n\r\n" := by
  decide +kernel

theorem no_content_fixture : bytes 204 [] 77 false=WireSpec.ascii "HTTP/1.1 204 No Content\r\n\r\n" := by
  decide +kernel

theorem not_modified_fixture : bytes 304 [] 77 false=WireSpec.ascii "HTTP/1.1 304 \r\n\r\n" := by
  decide +kernel
end E5R.Thermostat.ResponseHeadSpec
