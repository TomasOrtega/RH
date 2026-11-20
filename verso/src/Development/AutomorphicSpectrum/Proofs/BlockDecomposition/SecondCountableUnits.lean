import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.BCT PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

noncomputable section

namespace GlobalTheory.CompanionTheory.LocalThetaTopology

/- English proof (translation)
The claim follows from `Units.isClosedEmbedding_embedProduct.locallyCompactSpace`.
-/
theorem locallyCompact_units {M : Type} [Ring M] [TopologicalSpace M] [IsTopologicalRing M] [T2Space M]
    [LocallyCompactSpace M] : LocallyCompactSpace Mˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

/- English proof (translation)
Use `haveI : SecondCountableTopology Mᵐᵒᵖ := (MulOpposite.opHomeomorph (M := M)).symm.secondCountableTopology`. Conclude with `Units.isEmbedding_embedProduct.secondCountableTopology`.
-/
theorem secondCountable_units {M : Type} [Monoid M] [TopologicalSpace M] [SecondCountableTopology M] :
    SecondCountableTopology Mˣ := by
  haveI : SecondCountableTopology Mᵐᵒᵖ := (MulOpposite.opHomeomorph (M := M)).symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

/- English proof (translation)
The claim follows from `Units.isEmbedding_embedProduct.t2Space`.
-/
theorem t2Space_units {M : Type} [Monoid M] [TopologicalSpace M] [T2Space M] : T2Space Mˣ :=
  Units.isEmbedding_embedProduct.t2Space

/- English proof (translation)
Use `haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))`. Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))`. Use `haveI : T2Space (Matrix (Fin n) (Fin n) R) := inferInstanceAs (T2Space (Fin n → Fin n → R))`. Conclude with `⟨locallyCompact_units, secondCountable_units, t2Space_units⟩`.
-/
theorem top_GL {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R] (n : ℕ) :
    LocallyCompactSpace (GL (Fin n) R) ∧ SecondCountableTopology (GL (Fin n) R) ∧ T2Space (GL (Fin n) R) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : T2Space (Matrix (Fin n) (Fin n) R) := inferInstanceAs (T2Space (Fin n → Fin n → R))
  exact ⟨locallyCompact_units, secondCountable_units, t2Space_units⟩

/- English proof (translation)
The claim follows from `Units.continuous_iff.2 ⟨(Units.continuous_coe_inv.matrix_map hσ).matrix_transpose, (Units.continuous_val.matrix_map hσ).matrix_transpose⟩`.
-/
theorem continuous_thetaR {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (σ : A →+* A)
    (hσ : Continuous σ) (n : ℕ) : Continuous (thetaR σ n) :=
  Units.continuous_iff.2 ⟨(Units.continuous_coe_inv.matrix_map hσ).matrix_transpose,
    (Units.continuous_val.matrix_map hσ).matrix_transpose⟩

/- English proof (translation)
Set `b` to `Module.finBasis ℚ E`. Conclude with `Function.Injective.countable b.equivFun.injective`.
-/
theorem countable_numberField (E : Type) [Field E] [NumberField E] : Countable E := by
  let b := Module.finBasis ℚ E
  exact Function.Injective.countable b.equivFun.injective

/- English proof (translation)
Use `haveI := countable_numberField E`. Use `haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))`. Conclude with `Function.Injective.countable (f := fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E)) fun _ _ h => Units.ext h`.
-/
theorem countable_GL (E : Type) [Field E] [NumberField E] (n : ℕ) : Countable (GL (Fin n) E) := by
  haveI := countable_numberField E
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  exact Function.Injective.countable (f := fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E)) fun _ _ h => Units.ext h

/- English proof (translation)
Establish `h : (thF E n : GL (Fin n) (Af E) → GL (Fin n) (Af E)) = fun g => PhiU n (Af E) * thetaR (conjFin (IsCMField.complexConj E).toRingEquiv) n g * (PhiU n (Af E))⁻¹`. Use function extensionality and compare the values at `fun g => thetaGL_eq n (Af E) _ g`. Rewrite using `[h]`. Conclude with `(continuous_const.mul (continuous_thetaR _ (continuous_conjFin _) n)).mul continuous_const`.
-/
theorem continuous_thF (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Continuous (thF E n) := by
  have h : (thF E n : GL (Fin n) (Af E) → GL (Fin n) (Af E)) = fun g =>
      PhiU n (Af E) * thetaR (conjFin (IsCMField.complexConj E).toRingEquiv) n g * (PhiU n (Af E))⁻¹ :=
    funext fun g => thetaGL_eq n (Af E) _ g
  rw [h]
  exact (continuous_const.mul (continuous_thetaR _ (continuous_conjFin _) n)).mul continuous_const

/- English proof (translation)
Introduce `E _ _ _ n`. Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E`.

Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E`. Take `⟨c1, c2, -⟩` from `top_GL (R := ℂ) n`. Conclude with `⟨top_GL n, top_GL n, ⟨c1, c2⟩, countable_GL E n, continuous_thF E n, continuous_thetaR _ Complex.continuous_conj n⟩`.
-/
theorem topo : Topo := by
  intro E _ _ _ n
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  obtain ⟨c1, c2, -⟩ := top_GL (R := ℂ) n
  exact ⟨top_GL n, top_GL n, ⟨c1, c2⟩, countable_GL E n, continuous_thF E n,
    continuous_thetaR _ Complex.continuous_conj n⟩

end GlobalTheory.CompanionTheory.LocalThetaTopology
