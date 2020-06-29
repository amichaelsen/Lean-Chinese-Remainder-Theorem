import logic.function.basic

open function

--functions!

lemma left {α: Type} (f g : α → α)
  (hf : involutive f) (hfg : left_inverse g f) : f = g := 
  begin
    funext,
    rw ← (hf x),
    rw [hfg, hf],
  end

  #print left 

lemma right {α: Type} (f g : α → α)
  (hf : involutive f) (hfg : right_inverse g f) : f = g := 
  begin
    funext,
    rw ← hfg x,
    rw [hf, hfg],     
  end

  lemma left' {α: Type} (f g : α → α)
  (hf2 : involutive f) (hfg : left_inverse g f) : f = g := 
  left f g hf2 hfg
#print axioms left'

lemma right' {α: Type} (f g : α → α)
  (hf2 : involutive f) (hfg : right_inverse g f) : f = g := 
  right f g hf2 hfg
#print axioms right'