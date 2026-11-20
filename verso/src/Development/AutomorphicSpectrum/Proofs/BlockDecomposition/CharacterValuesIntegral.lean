import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.IntVal

open Polynomial

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isIntegral_of_norm_le_one (z : Om l) (h : ‖z‖ ≤ 1) : IsIntegral ℤ_[l] z := by
  have hz : IsIntegral ℚ_[l] z := Algebra.IsIntegral.isIntegral z
  rw [← PadicAlgCl.spectralNorm_eq] at h
  unfold spectralNorm at h
  rw [spectralValue_le_one_iff (minpoly.monic hz)] at h
  have hlift : minpoly ℚ_[l] z ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hlift (minpoly.monic hz)
  refine ⟨q, hqm, ?_⟩
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Om l), ← eval₂_map, hq, ← aeval_def]
  exact minpoly.aeval ℚ_[l] z

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem mem_OL_of_norm_le_one (K : FinExt l) (x : ↥K.1) (h : ‖((x : ↥K.1) : Om l)‖ ≤ 1) :
    x ∈ OL K := by
  change x ∈ integralClosure ℤ_[l] ↥K.1
  rw [mem_integralClosure_iff]
  haveI : IsScalarTower ℤ_[l] ↥K.1 (Om l) := IsScalarTower.of_algebraMap_eq fun z => by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l),
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1]
    rfl
  have hinj : Function.Injective (IsScalarTower.toAlgHom ℤ_[l] ↥K.1 (Om l)) :=
    (algebraMap ↥K.1 (Om l)).injective
  exact (isIntegral_algHom_iff _ hinj).1 (isIntegral_of_norm_le_one _ h)

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem compactSpace_GK (K : FinExt l) : CompactSpace ↥(GK K) := by
  have := K.2
  exact isCompact_iff_compactSpace.mp (IntermediateField.fixingSubgroup_isClosed K.1).isCompact

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Assume the negation of the conclusion and derive a contradiction.

Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem norm_le_one (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ)
    (hc : Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l))) (g : ↥(GK K)) :
    ‖(((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)‖ ≤ 1 := by
  haveI := compactSpace_GK K
  obtain ⟨M, hM⟩ := (isCompact_range hc).isBounded.exists_norm_le
  have hpow : ∀ n : ℕ, ‖(((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)‖ ^ n ≤ M := fun n => by
    have := hM _ ⟨g ^ n, rfl⟩
    simpa [map_pow, norm_pow] using this
  by_contra h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (not_le.1 h)
  exact absurd (hpow n) (not_le.2 hn)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem integral_values {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) :
    Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) →
    ∀ g, ∃ a : ↥(OL K), (a : ↥K.1) = ((χ g : (↥K.1)ˣ) : ↥K.1) := fun hc g =>
  ⟨⟨_, mem_OL_of_norm_le_one K _ (norm_le_one K χ hc g)⟩, rfl⟩

end GlobalTheory.CompanionTheory.LTPer.IntVal
