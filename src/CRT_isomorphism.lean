import CRT 
import data.nat.basic
import data.nat.modeq
import data.nat.gcd
import data.zmod.basic
import tactic
import algebra.euclidean_domain
import data.int.basic
import data.equiv.ring
noncomputable theory

open nat nat.modeq zmod  CRT

-------------------------ISOMORPHISM VERSION--------------------------


def proj (n: ℕ) (m: ℕ) : zmod (n*m) → (zmod n) × (zmod m):=
begin
    intro a,
    use (a,a),
end

--def proj' (n:ℕ ) (m : ℕ) : (λ (a: zmod (n*m) ), ( (a : zmod n), (a:zmod m) ))



theorem CRTwith2 (n m : ℕ) (H: coprime n m) (npos: n > 0) (mpos: m > 0)  : zmod (n*m) ≃+* zmod n × zmod m :=
begin
    use proj n m,
    intro a,
    sorry,
    sorry,
    sorry,
    sorry,
    sorry,
end

lemma casting1 {n m : ℕ } {H_cop: coprime n m } {n_pos : 0 < n} {m_pos : 0 < m} (f: zmod n × zmod m → zmod (n*m)) (y: zmod n × zmod m) : 
    ((f y) :zmod n) = (((f y):zmod n).val : zmod n):=
begin
    rw @cast_val _  n_pos (f y),
end

lemma casting2 {n m : ℕ } {H_cop: coprime n m} {n_pos : 0 < n} {m_pos : 0 < m} (y: zmod n × zmod m) : 
    ((y.fst).val : zmod n) = y.fst ∧ ((y.snd).val : zmod m) = y.snd:=
begin
    split,
    rw @cast_val _ n_pos y.fst,
    rw @cast_val _ m_pos y.snd,
end

lemma casting3 {n m : ℕ } {H_cop: coprime n m } {n_pos : 0 < n} {m_pos : 0 < m} (f: zmod n × zmod m → zmod (n*m)) (y: zmod n × zmod m) :
    (((f y):zmod n).val) ≡ ((f y).val) [MOD n]:=
begin
    sorry,

end


lemma modular_equivalence {n : ℕ} {a b : zmod n} : (a : zmod n) = (b : zmod n) ↔  a.val ≡ b.val [MOD n] :=
begin
    sorry,
end

theorem CRTisowith2' {n m : ℕ} (H_cop: coprime n m ) (n_pos : 0 < n) (m_pos : 0 < m) :
 (zmod (n*m)) ≃+* (zmod n)×(zmod m) := 
begin 
    use (λ a, (a,a)),
    intro xy,
    have inv1 := nat_inv n m n_pos m_pos H_cop,
    have inv2 := nat_inv m n m_pos n_pos (coprime.symm H_cop),
    --  why doesn't this work??
    choose b1 Hb1 using inv1,
    choose b2 Hb2 using inv2,
    exact xy.fst * b1* m + xy.snd* b2* n,
    intro y,
    simp,
    cases CRTwith2exist ((y: zmod n).val) ((y: zmod m).val) n m (n_pos) (m_pos) (H_cop) with x hx,
    have hyn: y.val ≡ (y: zmod n).val [MOD n] ∧ y.val ≡ ((y: zmod m).val) [MOD m],
        begin
            sorry,
        end,   
    /-have choice : ∀ (xy : (zmod n)×(zmod m)),
     ∃ ( XY : (zmod (n*m)) ), modeq n XY.val xy.fst.val ∧ modeq m XY.val xy.snd.val,
    begin
        intro xy, 
        have CRT := CRTwith2exist xy.1.val xy.2.val n m n_pos m_pos H_cop,
        choose x Hx using CRT,
        use x, 
        split, 
        {
            --rw modular_equivalence,
            sorry,
        },
        {
            sorry, 
        }
    end,
    choose f Hf using choice, 
    use f,
    intro y,
    -/
    
    /-have := nat_inv n m n_pos m_pos H_cop,
    cases this, 
    have := nat_inv n m n_pos m_pos (coprime.symm H_cop),
    cases this with b2 Hb2, 
    --solution x = a1 b1 m2 + a2 b1 m2 
    use (λ (a1,a2), (a1*b1*m + a2*b2*n)),
    -/
    sorry,
    sorry,
    sorry, 
    sorry, 
end

--PLAYING AROUND WITH CLASSICAL.SOME AND .SOME_SPEC 
theorem isomorphism_test_classical {n m : ℕ} (H_cop: coprime n m ) (n_pos : 0 < n) (m_pos : 0 < m) :
 (zmod (n*m)) ≃+* (zmod n)×(zmod m) := 
begin 
    --define function and its inverse
    use (λ a, (a,a)),
    intro xy, 
    have CRT := CRTwith2exist xy.fst.val xy.snd.val n m n_pos m_pos H_cop,
    set k := classical.some CRT with H, 
    have k' := classical.some_spec CRT, 
    use (k : zmod (n*m) ), 

    --show these are inverses using classical.some_spec
    {
        intro y, 
        dsimp,
        rw modular_equivalence, 
        rw ← modeq.modeq_and_modeq_iff_modeq_mul H_cop,
        have k' := classical.some_spec (CRTwith2exist (y:zmod n).val (y : zmod n).val n m n_pos m_pos H_cop),
        sorry, 
    },
    sorry,sorry,sorry,
end

--lemma to use for final step of add/mul homomorphisms.
lemma casting4 {n m: ℕ} (H_cop: coprime n m ) (n_pos : 0 < n) (m_pos : 0 < m) ( x y : zmod (n*m)):
    ((x: zmod n)+ (y : zmod n)).val= ((x + y) : zmod n).val :=
begin
    exact rfl,
end

theorem CRTadd_hom {n m : ℕ} (H_cop: coprime n m ) (n_pos : 0 < n) (m_pos : 0 < m) (f : zmod (n*m)→ (zmod n × zmod m)) (H : ∀ xy: zmod (n*m), f(xy)=(xy,xy))
   : ∀ (x y : zmod (n*m)), f (x + y) = f x + f y:=
begin
    intros x y,
    have Hx := H x,
    have Hy := H y,
    have Hxy := H (x+y),
    rw Hx,
    rw Hy,
    rw Hxy,
    ext,
        simp,
        have add : (x : zmod n) + (y : zmod n) = ((x + y) : zmod n),
        refl,
        rw modular_equivalence,
        have nm_pos: 0<n*m,
            exact mul_pos n_pos m_pos,
        rw ← casting4 H_cop n_pos m_pos x y,
        sorry,

        simp,
        sorry,
                

end 



theorem CRTmul_hom {n m : ℕ} (H_cop: coprime n m ) (n_pos : 0 < n) (m_pos : 0 < m) (f : zmod (n*m)→ (zmod n × zmod m)) (H : ∀ xy: zmod (n*m), f(xy)=(xy,xy))
   : ∀ (x y : zmod (n*m)), f (x * y) = f x * f y:=
begin
    intros x y,
    have Hx := H x,
    have Hy := H y,
    have Hxy := H (x*y),
    rw Hx,
    rw Hy,
    rw Hxy,
    ext,
        simp,
        sorry,

        simp,
        sorry,  
end



theorem CRTisowith2 {n m : ℕ} (H_cop: coprime n m ) (n_pos : 0 < n) (m_pos : 0 < m) :
  (zmod n)×(zmod m) ≃+* (zmod (n*m)) := 
begin  
    -- defining a CRT lift (zmod n)×(zmod m) → (zmod (n*m))
    -- which satisfies the desired congruences
    have choice : ∀ (xy : (zmod n)×(zmod m)),
     ∃ ( XY : (zmod (n*m)) ), modeq n XY.val xy.fst.val ∧ modeq m XY.val xy.snd.val,
    begin
        intro xy, 
        have CRT := CRTwith2exist xy.1.val xy.2.val n m n_pos m_pos H_cop,
        choose x Hx using CRT,
        use x, 
        split, 
        {
            sorry, 
        },
        {
            sorry, 
        }
    end,
    choose f Hf using choice, 
    use f,
    intro x, 
    use (x,x), 
    intro y,
    ext, 
    {   simp, 
        have thing1 : ((f y) :zmod n) = (((f y):zmod n).val : zmod n), by sorry, 
        have thing2 : ((y.fst).val : zmod n) = y.fst, by sorry, 
        rw [thing1, ← thing2],  
        rw nat_coe_eq_nat_coe_iff _ _ _,
        specialize Hf y, 
        have thing3 : (((f y):zmod n).val) ≡ ((f y).val) [MOD n], by sorry, 
        exact modeq.trans thing3 Hf.left,       
    },
    {   simp, 
        have thing1 : ((f y) :zmod m) = (((f y):zmod m).val : zmod m), by sorry, 
        have thing2 : ((y.snd).val : zmod m) = y.snd, by sorry, 
        rw [thing1, ← thing2],  
        rw nat_coe_eq_nat_coe_iff _ _ _,
        specialize Hf y, 
        have thing3 : ((f y):zmod m).val ≡ (f y).val [MOD m], by sorry, 
        exact modeq.trans thing3 Hf.right,         
    },
    {
        intro y, 
        rw modular_equivalence, 
        apply CRTwith2unique _ _ y.val y.val,  
        simpa, simpa, 
        exact H_cop, 
        specialize Hf (((y:zmod n),(y:zmod m))),  
        {
            split, 
            have Hf' := Hf.left, 
            simp at *, 
            have this : (y : zmod n).val ≡ y.val [MOD n], by sorry, 
            exact modeq.trans Hf' this, 

            have Hf' := Hf.right, 
            simp at *, 
            have this : (y : zmod m).val ≡ y.val [MOD m], by sorry, 
            exact modeq.trans Hf' this,             
        },
        split; refl,
    },

    --multiplicative hom 
    {
        intros x y, 
        rw modular_equivalence, 
        rw ← modeq_and_modeq_iff_modeq_mul H_cop,
        split, 
        {
            have Hx := (Hf x).left, 
            have Hy := (Hf y).left, 
            have Hxy := (Hf (x*y)).left,  
            have step1 : ((f x)*(f y)).val ≡  (x.fst.val*y.fst.val) [MOD n] := 
            begin
                rw ← val_mul x.fst y.fst,

            end,
            have step2 : (f (x*y)).val ≡  (x.fst.val*y.fst.val) [MOD n] := 
            begin
                apply modeq.trans Hxy, 
                rw prod.fst_mul x y,
                rw val_mul, 
                exact modeq.mod_modeq (x.fst.val * y.fst.val) n,
            end,
            exact modeq.trans step2 (modeq.symm step1),             
        },
        {
            have Hx := (Hf x).right, 
            have Hy := (Hf y).right, 
            have Hxy := (Hf (x*y)).right,  
            have step1 : ((f x)*(f y)).val ≡  (x.snd.val*y.snd.val) [MOD m] := 
            begin
                sorry,
            end,
            have step2 : (f (x*y)).val ≡  (x.snd.val*y.snd.val) [MOD m] := 
            begin
                apply modeq.trans Hxy, 
                rw prod.snd_mul x y,
                rw val_mul, 
                exact modeq.mod_modeq (x.snd.val * y.snd.val) m,
            end,
            exact modeq.trans step2 (modeq.symm step1),             
        },
    },

    --additive hom 
    intros x y, 
    rw modular_equivalence, 
    rw ← modeq_and_modeq_iff_modeq_mul H_cop,
    split, 
    {
        have Hx := (Hf x).left, 
        have Hy := (Hf y).left, 
        have Hxy := (Hf (x+y)).left,  
        have step1 : ((f x)+(f y)).val ≡  (x.fst.val+y.fst.val) [MOD n] := 
        begin
            sorry,
        end,
        have step2 : (f (x+y)).val ≡  (x.fst.val+y.fst.val) [MOD n] := 
        begin
            apply modeq.trans Hxy, 
            rw prod.fst_add x y,
            rw @val_add n n_pos, 
            exact modeq.mod_modeq (x.fst.val + y.fst.val) n,
        end,
        exact modeq.trans step2 (modeq.symm step1),             
    },
    {
            have Hx := (Hf x).right, 
            have Hy := (Hf y).right, 
            have Hxy := (Hf (x+y)).right,  
            have step1 : ((f x)+(f y)).val ≡  (x.snd.val+y.snd.val) [MOD m] := 
            begin
                sorry,
            end,
            have step2 : (f (x+y)).val ≡  (x.snd.val+y.snd.val) [MOD m] := 
            begin
                apply modeq.trans Hxy, 
                rw prod.snd_add x y,
                rw @val_add n n_pos, 
                exact modeq.mod_modeq (x.snd.val + y.snd.val) m,
            end,
            exact modeq.trans step2 (modeq.symm step1),             
    },
end