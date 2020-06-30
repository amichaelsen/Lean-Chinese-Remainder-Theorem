import data.nat.basic
import data.nat.modeq
import data.nat.gcd

open nat nat.modeq


--  inverses mod n 

-- 2 congruence statements

theorem CRTwith2exist (a1 a2 M1 M2: ℕ ) (H: coprime M1 M2) : ∃ x : ℕ , modeq M1 x a1 ∧ modeq M2 x a2 :=
begin
    sorry,
end

theorem CRTwith2unique (x1 x2 a1 a2 M1 M2: ℕ) (H: coprime M1 M2) 
    (H1: modeq M1 x1 a1 ∧ modeq M2 x1 a2) (H2: modeq M1 x2 a1 ∧ modeq M2 x2 a2): modeq (M1*M2) x1 x2:=
begin
    sorry,
end

