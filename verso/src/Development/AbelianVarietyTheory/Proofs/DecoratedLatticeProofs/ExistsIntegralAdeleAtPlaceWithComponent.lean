import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SigV
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupported
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FixedUnitNorm

/- English proof (translation)
Conclude with `RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y`.
-/
theorem evalAtPlace_singleAtPlace_self (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    evalV F v (singleV F v y) = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

/- English proof (translation)
Conclude with `RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y hw`.
-/
theorem evalAtPlace_singleAtPlace_of_ne (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) : evalV F w (singleV F v y) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y hw

/- English proof (translation)
Establish `hc : ∀ w : Pl D, compAt D w (pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E)) = evalV D.host.F w (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E)`. Introduce `w`. Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E) (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E))) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]`. Both sides reduce to the same expression.

Use `⟨pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]`. Use `⟨?_, fun w hw => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E)) = 0`. Rewrite using `[Algebra.TensorProduct.map_tmul]`.

Conclude with `TensorProduct.zero_tmul _ _`. Rewrite using `[hc, evalAtPlace_singleAtPlace_of_ne _ v a hw, TensorProduct.zero_tmul]`. Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E)) ∈ intAE D`. Rewrite using `[Algebra.TensorProduct.map_tmul]`. Use `AddSubgroup.subset_closure ⟨singleV D.host.F v a, fun w => ?_, x, rfl⟩` and prove the remaining obligations.

Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[evalAtPlace_singleAtPlace_self]`. Conclude with `ha`. Rewrite using `[evalAtPlace_singleAtPlace_of_ne _ v a hw]`.

Conclude with `zero_mem _`. Rewrite using `[hc, evalAtPlace_singleAtPlace_self]`.
-/
theorem exists_integralAdele_atPlace_component_tmul (D : D7) (v : Pl D) (a : Fv D.host.F v) (ha : a ∈ v.adicCompletionIntegers D.host.F)
    (x : 𝓞 D.host.E) : ∃ y ∈ intAt D (· = v), compAt D v y = a ⊗ₜ[D.host.F] (x : D.host.E) := by
  have hc : ∀ w : Pl D, compAt D w (pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E)) =
      evalV D.host.F w (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E) := by
    intro w
    change Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
        (pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E))) = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    rfl
  refine ⟨pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E), ⟨?_, ?_⟩, ?_⟩
  · rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
    refine ⟨?_, fun w hw => ?_⟩
    · change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
        (pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E)) = 0
      rw [Algebra.TensorProduct.map_tmul]
      exact TensorProduct.zero_tmul _ _
    · rw [hc, evalAtPlace_singleAtPlace_of_ne _ v a hw, TensorProduct.zero_tmul]
  · change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      (pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E)) ∈ intAE D
    rw [Algebra.TensorProduct.map_tmul]
    refine AddSubgroup.subset_closure ⟨singleV D.host.F v a, fun w => ?_, x, rfl⟩
    by_cases hw : w = v
    · subst hw; rw [evalAtPlace_singleAtPlace_self]; exact ha
    · rw [evalAtPlace_singleAtPlace_of_ne _ v a hw]; exact zero_mem _
  · rw [hc, evalAtPlace_singleAtPlace_self]

/- English proof (translation)
Introduce `D v z hz`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, x, rfl⟩` from `hy`. Conclude with `exists_integralAdele_atPlace_component_tmul D v a ha x`.

Consider the case `zero`. Conclude with `⟨0, ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩, map_zero _⟩`. Consider the case `add y z _ _ h1 h2`. Take `⟨a, ha, hya⟩` from `h1`. Take `⟨b, hb, hzb⟩` from `h2`.

Conclude with `⟨a + b, GlobalTheory.IwaPlace.SdComap.intAt_add ha hb, by rw [RingHom.map_add, hya, hzb]⟩`. Consider the case `neg y _ h`. Take `⟨a, ha, hya⟩` from `h`. Conclude with `⟨-a, ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩, by rw [RingHom.map_neg, hya]⟩`.
-/
theorem exists_intAt_compAt_eq : ∀ (D : D7) (v : Pl D) (z : Fv D.host.F v ⊗[D.host.F] D.host.E), z ∈ intV D v →
    ∃ x ∈ intAt D (· = v), compAt D v x = z := by
  intro D v z hz
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    exact exists_integralAdele_atPlace_component_tmul D v a ha x
  | zero =>
    exact ⟨0, ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩, map_zero _⟩
  | add y z _ _ h1 h2 =>
    obtain ⟨a, ha, hya⟩ := h1
    obtain ⟨b, hb, hzb⟩ := h2
    exact ⟨a + b, GlobalTheory.IwaPlace.SdComap.intAt_add ha hb, by rw [RingHom.map_add, hya, hzb]⟩
  | neg y _ h =>
    obtain ⟨a, ha, hya⟩ := h
    exact ⟨-a, ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩, by rw [RingHom.map_neg, hya]⟩

end GlobalTheory.FixedUnitNorm

end
