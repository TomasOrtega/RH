import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT

namespace PositivityTheory.Rg.BcB.G8

/- English proof (translation)
Establish `: LocallyCompactSpace (Matrix (Fin n) (Fin n) R)` using `inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))`. Establish `: SecondCountableTopology (Matrix (Fin n) (Fin n) R)` using `inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))`. Establish `: T2Space (Matrix (Fin n) (Fin n) R)` using `inferInstanceAs (T2Space (Fin n → Fin n → R))`. Establish `: LocallyCompactSpace (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ` using `(MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) R)).symm.isClosedEmbedding.locallyCompactSpace`. Establish `: SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ` using `(MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) R)).symm.isEmbedding.secondCountableTopology`.

Establish `: T2Space (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ` using `(MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) R)).symm.isEmbedding.t2Space`. Establish `h` using `Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) R)`. Conclude with `⟨h.locallyCompactSpace, h.isEmbedding.secondCountableTopology, h.isEmbedding.t2Space⟩`.
-/
theorem topo_units {R : Type} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R] (n : ℕ) :
    LocallyCompactSpace (GL (Fin n) R) ∧ SecondCountableTopology (GL (Fin n) R) ∧ T2Space (GL (Fin n) R) := by
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  have : T2Space (Matrix (Fin n) (Fin n) R) := inferInstanceAs (T2Space (Fin n → Fin n → R))
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) R)).symm.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) R)).symm.isEmbedding.secondCountableTopology
  have : T2Space (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) R)).symm.isEmbedding.t2Space
  have h := Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) R)
  exact ⟨h.locallyCompactSpace, h.isEmbedding.secondCountableTopology, h.isEmbedding.t2Space⟩

/- English proof (translation)
Rewrite using `[Units.continuous_iff]`. Conclude with `⟨(Units.continuous_coe_inv.matrix_map hc).matrix_transpose, (Units.continuous_val.matrix_map hc).matrix_transpose⟩`.
-/
theorem topo_thetaR_cont {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (c : R →+* R)
    (hc : Continuous c) (n : ℕ) : Continuous (thetaR c n) := by
  rw [Units.continuous_iff]
  exact ⟨(Units.continuous_coe_inv.matrix_map hc).matrix_transpose,
    (Units.continuous_val.matrix_map hc).matrix_transpose⟩

/- English proof (translation)
Establish `: Countable E` using `(Module.finBasis ℚ E).equivFun.injective.countable`. Establish `: Countable (Matrix (Fin n) (Fin n) E)` using `inferInstanceAs (Countable (Fin n → Fin n → E))`. Conclude with `Function.Injective.countable (f := fun u : GL (Fin n) E => (u : Matrix (Fin n) (Fin n) E)) fun _ _ h => Units.ext h`.
-/
theorem topo_countable (E : Type) [Field E] [NumberField E] (n : ℕ) : Countable (GL (Fin n) E) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  exact Function.Injective.countable (f := fun u : GL (Fin n) E => (u : Matrix (Fin n) (Fin n) E))
    fun _ _ h => Units.ext h

/- English proof (translation)
Establish `h : ∀ g, thF E n g = PhiU n (Af E) * thetaR (conjFin (IsCMField.complexConj E).toRingEquiv) n g * (PhiU n (Af E))⁻¹` using `fun g => thetaGL_eq n (Af E) _ g`. Rewrite using `[show (thF E n : GL (Fin n) (Af E) → GL (Fin n) (Af E)) = _ from funext h]`. Conclude with `(continuous_const.mul (topo_thetaR_cont _ (continuous_conjFin _) n)).mul continuous_const`.
-/
theorem topo_thF_cont (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Continuous (thF E n) := by
  have h : ∀ g, thF E n g = PhiU n (Af E) * thetaR (conjFin (IsCMField.complexConj E).toRingEquiv) n g *
      (PhiU n (Af E))⁻¹ := fun g => thetaGL_eq n (Af E) _ g
  rw [show (thF E n : GL (Fin n) (Af E) → GL (Fin n) (Af E)) = _ from funext h]
  exact (continuous_const.mul (topo_thetaR_cont _ (continuous_conjFin _) n)).mul continuous_const

/- English proof (translation)
Introduce `E _ _ _ n`. Use `GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E` as an intermediate fact. Use `GlobalTheory.AdelicUnitaryTop.secondCountable_adele E` as an intermediate fact. Use `GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E` as an intermediate fact. Use `GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E` as an intermediate fact.

Use `GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E` as an intermediate fact. Use `GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E` as an intermediate fact. Take `⟨hc, hs, -⟩` from `topo_units (R := ℂ) n`. Conclude with `⟨topo_units n, topo_units n, ⟨hc, hs⟩, topo_countable E n, topo_thF_cont E n, topo_thetaR_cont _ Complex.continuous_conj n⟩`.
-/
theorem topo_holds : Topo := by
  intro E _ _ _ n
  have := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  have := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele E
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele E
  have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  obtain ⟨hc, hs, -⟩ := topo_units (R := ℂ) n
  exact ⟨topo_units n, topo_units n, ⟨hc, hs⟩, topo_countable E n, topo_thF_cont E n,
    topo_thetaR_cont _ Complex.continuous_conj n⟩

end PositivityTheory.Rg.BcB.G8

end
