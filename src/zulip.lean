import CRT 
import data.nat.basic
import data.nat.modeq
import data.nat.gcd
import data.zmod.basic
import tactic
import data.equiv.ring
noncomputable theory

open nat nat.modeq zmod CRT

-------------------------ISOMORPHISM VERSION--------------------------
/--
A convenience method for extracting the property satisfied by a term which is merely equal to
`classical.some _`.
-/
lemma classical.spec_of_eq_some
  {α : Type*} {p : α → Prop} {a : α} {w : ∃ x, p x} (h : a = classical.some w) : p a :=
begin
  subst h,
  apply classical.some_spec,
end

lemma modular_equivalence {n : ℕ} {a b : zmod n} : (a : zmod n) = (b : zmod n) ↔  a.val ≡ b.val [MOD n] :=
begin
    sorry,
end


theorem CRTwith2 (n m : ℕ) (H: coprime n m) (npos: n > 0) (mpos: m > 0)  : zmod (n*m) ≃+* zmod n × zmod m :=
begin
    --define maps 
    use (λ x, (x, x)),
    intro xy, 
    have CRT := CRTwith2exist xy.1.val xy.2.val n m npos mpos H, 
    /-theorem CRTwith2exist (a1 a2 M1 M2 : ℕ ) (M1pos : 0 < M1) (M2pos : 0 < M2) (H : coprime M1 M2) :
                         ∃ x : ℕ , modeq M1 x a1 ∧ modeq M2 x a2 -/
    choose x Hx using CRT, 
    use x, 

    -- show inverses (needs classical.some)
    {
        intro y,
        simp,
        
        rw modular_equivalence, 
        rw ← modeq_and_modeq_iff_modeq_mul H,
        split, 
         
        
        -- Goal here: ⊢ ↑(classical.some _) = y
    },
    --show other proprties...
end
