import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTail
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'`. Take `⟨hP', -, hsP', -, hres, hexc, -, -⟩` from `hpieces O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH`. Establish `hY₀G'` using `hdisj O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'`. Establish `hcmp` using `hcontr O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'`. Use `set P' := blowUpOf P (blowUpGens s g f m e) with hP'def`.

Use `set G := G'.comap (liftForm (J := BlowUpIdx ι) (ι := ι) (R := O)) with hGdef`. Establish `hP'prime : P'.IsPrime` using `hP'.multiProj.isPrime`. Establish `hPprime : P.IsPrime` using `hP.multiProj.isPrime`. Establish `hmul` using `DivCycleMul.proof O (Option K) (extIdx ι (BlowUpIdx ι)) P'`. Establish `hmul₀` using `DivCycleMul.proof O K ι P`.

Establish `nm : ∀ x y, x ∉ P' → y ∉ P' → x * y ∉ P'` using `fun x y hx hy h => (hP'prime.mem_or_mem h).elim hx hy`. Establish `hzero : ∀ x, x ∉ G' → divCycle P' x G' = 0` using `fun x hx => by`. Assume the negation of the conclusion as `h`. Conclude with `hx (form_mem_of_divCycle_ne_zero h)`. Establish `hG'supp : G' ∈ (P' ⊔ Ideal.span {liftForm s}).minimalPrimes ∧ IsRelevant G'`.

Assume the negation of the conclusion as `h`. Unfold `divCycle at hsG'`. Rewrite `hsG'` using `[dif_neg h]`. Conclude with `lt_irrefl _ hsG'`. Establish `hG'prime : G'.IsPrime` using `hG'supp.1.1.1`.

Establish `hP'G' : P' ≤ G'` using `le_sup_left.trans hG'supp.1.1.2`. Establish `hlift : ∀ p ∈ P, liftForm (J` using `BlowUpIdx ι) p ∈ P' := fun p hp => by`. Rewrite using `[hP'def, blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm, Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]`. Establish `hGprime : G.IsPrime` using `Ideal.comap_isPrime _ _`. Establish `hPG : P ≤ G` using `fun p hp => hP'G' (hlift p hp)`.

Establish `hGrel : IsRelevant G` using `fun k => by`. Take `⟨i, hi⟩` from `hG'supp.2 (some k)`. Conclude with `⟨i, fun h => hi (by simpa [hGdef, liftForm] using h)⟩`. Establish `hϖG : (C ϖ : MRing ι O) ∈ G`. Rewrite using `[hGdef, Ideal.mem_comap, liftForm_const]`.

Conclude with `hϖG'`. Take `⟨u, v, huG, huv⟩` from `hD.2 G hGprime hPG hGrel`. Establish `hfP` using `hD.1.num_not_mem`. Establish `hgP` using `hD.1.den_not_mem`. Establish `huP : u ∉ P` using `fun h => huG (hPG h)`.

Establish `hvP : v ∉ P` using `fun hv => by`. Establish `h : u * f ∈ P`. Rewrite using `[show u * f = (u * f - v * g) + v * g by ring]`. Conclude with `P.add_mem huv (P.mul_mem_right g hv)`. Conclude with `(hPprime.mem_or_mem h).elim huP hfP`.

Establish `hdown : ratDiv P f g G = divCycle P v G`. Establish `h1` using `congrFun (divCycle_congr_of_sub_mem huv) G`. Rewrite `h1` using `[hmul₀ u f hPprime huP hfP, hmul₀ v g hPprime hvP hgP]`. Establish `hu0 : divCycle P u G = 0`. Assume the negation of the conclusion as `h`.

Conclude with `huG (form_mem_of_divCycle_ne_zero h)`. Simplify using `only [Pi.add_apply] at h1`. Unfold `ratDiv`. Use linear arithmetic over natural numbers and integers. Establish `hluP' : liftForm (J` using `BlowUpIdx ι) u ∉ P' := fun h => huG (hP'G' h)`.

Establish `hlfP' : liftForm (J` using `BlowUpIdx ι) f ∉ P' := fun h => hexc.1.num_not_mem (by rw [map_mul]; exact P'.mul_mem_right _ h)`. Establish `hlgP' : liftForm (J` using `BlowUpIdx ι) g ∉ P' := fun h => hexc.1.den_not_mem (P'.mul_mem_right _ h)`. Establish `hluv : liftForm u * liftForm f - liftForm v * liftForm g ∈ P'`. Rewrite using `[← map_mul, ← map_mul, ← map_sub]`. Conclude with `hlift _ huv`.

Establish `hlvP' : liftForm (J` using `BlowUpIdx ι) v ∉ P' := fun hv => by`. Establish `h : liftForm u * liftForm f ∈ P'`. Rewrite using `[show liftForm u * liftForm f = (liftForm u * liftForm f - liftForm v * liftForm g) + liftForm v * liftForm g by ring]`. Conclude with `P'.add_mem hluv (P'.mul_mem_right _ hv)`. Conclude with `nm _ _ hluP' hlfP' h`.

Establish `hup : ratDiv P' (liftForm f) (liftForm g) G' = divCycle P' (liftForm v) G'`. Establish `h1` using `congrFun (divCycle_congr_of_sub_mem hluv) G'`. Rewrite `h1` using `[hmul _ _ hP'prime hluP' hlfP', hmul _ _ hP'prime hlvP' hlgP']`. Establish `hu0` using `hzero _ huG`. Simplify using `only [Pi.add_apply] at h1`.

Unfold `ratDiv`. Use linear arithmetic over natural numbers and integers. Establish `hY₁P' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ P'` using `hres.1.num_not_mem`. Establish `hlmP' : liftForm (J` using `BlowUpIdx ι) m ∉ P' := hres.1.den_not_mem`. Establish `hY₀P' : (newVar none : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ P'` using `fun h => hY₀G' (hP'G' h)`.

Establish `hrel` using `congrFun (divCycle_congr_of_sub_mem (blowUp_relation P s g f m e)) G'`. Rewrite `hrel` using `[map_mul, map_mul, hmul _ _ hP'prime (nm _ _ hsP' hlgP') hY₁P', hmul _ _ hP'prime (nm _ _ hlfP' hlmP') hY₀P', hmul _ _ hP'prime hsP' hlgP', hmul _ _ hP'prime hlfP' hlmP']`. Establish `hY₀0` using `hzero _ hY₀G'`. Simplify using `only [Pi.add_apply] at hrel`. Establish `hv` using `hcmp v hvP`.

Use `⟨G, hϖG, hcmp s hsP, ?_⟩` and prove the remaining obligations. Unfold `ratDiv at hup hdown ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem ResidualComparison.proof (hpieces : BlowUpDecomposition.Statement.{u})
    (hdisj : ResidualDisjoint.Statement.{u}) (hcontr : ResidualContraction.Statement.{u}) :
    ResidualComparison.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
  obtain ⟨hP', -, hsP', -, hres, hexc, -, -⟩ :=
    hpieces O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH
  have hY₀G' := hdisj O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
  have hcmp := hcontr O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
  set P' := blowUpOf P (blowUpGens s g f m e) with hP'def
  set G := G'.comap (liftForm (J := BlowUpIdx ι) (ι := ι) (R := O)) with hGdef
  have hP'prime : P'.IsPrime := hP'.multiProj.isPrime
  have hPprime : P.IsPrime := hP.multiProj.isPrime
  have hmul := DivCycleMul.proof O (Option K) (extIdx ι (BlowUpIdx ι)) P'
  have hmul₀ := DivCycleMul.proof O K ι P
  have nm : ∀ x y, x ∉ P' → y ∉ P' → x * y ∉ P' := fun x y hx hy h =>
    (hP'prime.mem_or_mem h).elim hx hy
  have hzero : ∀ x, x ∉ G' → divCycle P' x G' = 0 := fun x hx => by
    by_contra h; exact hx (form_mem_of_divCycle_ne_zero h)

  have hG'supp : G' ∈ (P' ⊔ Ideal.span {liftForm s}).minimalPrimes ∧ IsRelevant G' := by
    by_contra h; unfold divCycle at hsG'; rw [dif_neg h] at hsG'; exact lt_irrefl _ hsG'
  have hG'prime : G'.IsPrime := hG'supp.1.1.1
  have hP'G' : P' ≤ G' := le_sup_left.trans hG'supp.1.1.2
  have hlift : ∀ p ∈ P, liftForm (J := BlowUpIdx ι) p ∈ P' := fun p hp => by
    rw [hP'def, blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm,
      Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
  have hGprime : G.IsPrime := Ideal.comap_isPrime _ _
  have hPG : P ≤ G := fun p hp => hP'G' (hlift p hp)
  have hGrel : IsRelevant G := fun k => by
    obtain ⟨i, hi⟩ := hG'supp.2 (some k)
    exact ⟨i, fun h => hi (by simpa [hGdef, liftForm] using h)⟩
  have hϖG : (C ϖ : MRing ι O) ∈ G := by
    rw [hGdef, Ideal.mem_comap, liftForm_const]; exact hϖG'

  obtain ⟨u, v, huG, huv⟩ := hD.2 G hGprime hPG hGrel
  have hfP := hD.1.num_not_mem
  have hgP := hD.1.den_not_mem
  have huP : u ∉ P := fun h => huG (hPG h)
  have hvP : v ∉ P := fun hv => by
    have h : u * f ∈ P := by
      rw [show u * f = (u * f - v * g) + v * g by ring]
      exact P.add_mem huv (P.mul_mem_right g hv)
    exact (hPprime.mem_or_mem h).elim huP hfP
  have hdown : ratDiv P f g G = divCycle P v G := by
    have h1 := congrFun (divCycle_congr_of_sub_mem huv) G
    rw [hmul₀ u f hPprime huP hfP, hmul₀ v g hPprime hvP hgP] at h1
    have hu0 : divCycle P u G = 0 := by
      by_contra h; exact huG (form_mem_of_divCycle_ne_zero h)
    simp only [Pi.add_apply] at h1
    unfold ratDiv; omega

  have hluP' : liftForm (J := BlowUpIdx ι) u ∉ P' := fun h => huG (hP'G' h)
  have hlfP' : liftForm (J := BlowUpIdx ι) f ∉ P' := fun h =>
    hexc.1.num_not_mem (by rw [map_mul]; exact P'.mul_mem_right _ h)
  have hlgP' : liftForm (J := BlowUpIdx ι) g ∉ P' := fun h => hexc.1.den_not_mem (P'.mul_mem_right _ h)
  have hluv : liftForm u * liftForm f - liftForm v * liftForm g ∈ P' := by
    rw [← map_mul, ← map_mul, ← map_sub]; exact hlift _ huv
  have hlvP' : liftForm (J := BlowUpIdx ι) v ∉ P' := fun hv => by
    have h : liftForm u * liftForm f ∈ P' := by
      rw [show liftForm u * liftForm f = (liftForm u * liftForm f - liftForm v * liftForm g) +
        liftForm v * liftForm g by ring]
      exact P'.add_mem hluv (P'.mul_mem_right _ hv)
    exact nm _ _ hluP' hlfP' h
  have hup : ratDiv P' (liftForm f) (liftForm g) G' = divCycle P' (liftForm v) G' := by
    have h1 := congrFun (divCycle_congr_of_sub_mem hluv) G'
    rw [hmul _ _ hP'prime hluP' hlfP', hmul _ _ hP'prime hlvP' hlgP'] at h1
    have hu0 := hzero _ huG
    simp only [Pi.add_apply] at h1
    unfold ratDiv; omega

  have hY₁P' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ P' := hres.1.num_not_mem
  have hlmP' : liftForm (J := BlowUpIdx ι) m ∉ P' := hres.1.den_not_mem
  have hY₀P' : (newVar none : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ P' := fun h => hY₀G' (hP'G' h)
  have hrel := congrFun (divCycle_congr_of_sub_mem (blowUp_relation P s g f m e)) G'
  rw [map_mul, map_mul, hmul _ _ hP'prime (nm _ _ hsP' hlgP') hY₁P',
    hmul _ _ hP'prime (nm _ _ hlfP' hlmP') hY₀P', hmul _ _ hP'prime hsP' hlgP',
    hmul _ _ hP'prime hlfP' hlmP'] at hrel
  have hY₀0 := hzero _ hY₀G'
  simp only [Pi.add_apply] at hrel
  have hv := hcmp v hvP
  refine ⟨G, hϖG, hcmp s hsP, ?_⟩
  unfold ratDiv at hup hdown ⊢
  omega

end GroundTheory.Heights₂.Heights.NumbersDVR
