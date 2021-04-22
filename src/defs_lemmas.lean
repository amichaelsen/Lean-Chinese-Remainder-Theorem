import data.nat.basic
import data.nat.modeq
import data.nat.gcd
import data.zmod.basic
import tactic
import algebra.euclidean_domain
import data.int.basic
import data.equiv.ring
import lemmas2
noncomputable theory

open nat nat.modeq zmod euclidean_domain lemmas2
namespace defs_lemmas


/- DEFINITIONS -/


/--
A structure for a congruence x ≡ a [MOD n] 
-/
def cong := (Σ (n : ℕ), zmod n)

/--
A list of congruence relations 
-/
def congruences := list cong

/-Examples of above definitions 
 def x : cong := ⟨5, ↑2⟩
 def y : congruences := [⟨5, ↑2⟩ , ⟨3, ↑2⟩]
-/


/- LIST PROPERTIES -/


/--
All moduli for the congruences in the list are pairwise coprime 
-/
def pairwise_coprime  (l : congruences) : Prop := 
            list.pairwise (λ (x y : cong), nat.coprime x.1 y.1) l

/--
All moduli for the congruences in the list are nonzero 
-/
def nonzero_cong ( l : congruences) : Prop :=
            list.all l (λ (c : cong), 0 < c.1)  

/--
Defines when x is a solution to the list of congruences in l 
-/
def solution (x : ℕ) (l : congruences) : Prop := 
            list.all l (λ (c : cong), modeq c.1 x c.2.val)

/--
Takes the product of the defining moduli of all congruences in the list 
-/
def cong_prod : congruences → ℕ
    | list.nil := 1
    | (h :: t) := h.1 * cong_prod t
--


/- LEMMAS ABOUT LIST PROPERTIES -/


/-- 
If a list satisfies nonzero_cong, so does the tail and the head has nonzero moduli
-/
lemma subset_nonzero (c : cong) (l : list cong) (H : nonzero_cong (c :: l)) :
                                 0 < c.1 ∧ nonzero_cong l :=
begin
    unfold nonzero_cong at H, 
    rw list.all_iff_forall_prop at H, 
    split, 
    { exact H c (by exact list.mem_cons_self c l), },
    {   unfold nonzero_cong, 
        rw list.all_iff_forall_prop,
        rintros a ha, 
        exact H a (by exact list.mem_cons_of_mem _ ha), }
end 

/--
If a list satisfies pairwise_coprime the head is coprime to all 
moduli in the tail and the tail satisfies pairwise_coprime 
-/
lemma subset_coprime (c : cong) (l : list cong) (H : pairwise_coprime (c :: l)) :
                (∀ (a : cong), a ∈ l → coprime c.1 a.1) ∧ pairwise_coprime l :=
begin
    unfold pairwise_coprime at H,
    rw list.pairwise_cons at H, 
    exact H,
end

/--
The modulus for an element of list of congruences will divide the 
cong_prod of the list, the product of all moduli in the list 
-/
lemma mem_div_prod (l : list cong) (a : cong) (H : a ∈ l) : a.1 ∣ cong_prod l :=
begin
    induction l with head tail ihtail,
     --nil case
    exfalso,
    exact H,
    --induction case
    dsimp[cong_prod],
    cases H,
    rw H,
    simp only [nat.dvd_mul_right],
    specialize ihtail H,
    cases ihtail with c hc,
    rw hc,
    rw mul_comm,
    use c * head.fst,
    ring,
end
 

/-  LEMMAS ABOUT CONG_PROD OUTPUTS -/ 


/--
 Given a list of congruences with nonzero (i.e. positive) 
   moduli, the product of those moduli will be positive 
-/
lemma pos_prod (l : congruences) (H : nonzero_cong l) : 0 < cong_prod l :=
begin
    induction l with head tail ihtail,
    {   dsimp [cong_prod],
        linarith, },
    {   have nonzero_parts := subset_nonzero head tail H,
        specialize ihtail nonzero_parts.right,
        dsimp [cong_prod],
        exact mul_pos nonzero_parts.left ihtail,}
end

/--
The modulus of the first congruence is coprime to the product of the moduli of 
the tail of the list assuming that the entire list satisfies pairwise_coprime
-/
lemma coprime_prod (c : cong) (l : list cong) (H : pairwise_coprime (c :: l)) :
                             coprime c.1 (cong_prod l) :=
begin
    induction l with head tail ihtail,
    {   dsimp[cong_prod],
        by exact c.fst.coprime_one_right, },
    {   dsimp[cong_prod],
        apply nat.coprime.mul_right,
        exact (subset_coprime c (head :: tail) H).left head (by exact list.mem_cons_self head tail),
        apply ihtail,
        unfold pairwise_coprime at *, 
        rw list.pairwise_cons at *, 
        split, 
        intros a ha, 
        refine H.left a (by exact list.mem_cons_of_mem head ha), 
        exact list.pairwise_of_pairwise_cons H.right, },
end 

end defs_lemmas
