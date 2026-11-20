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
Establish `hz : IsIntegral ℚ_[l] z` using `Algebra.IsIntegral.isIntegral z`. Rewrite `h` using `[← PadicAlgCl.spectralNorm_eq]`. Unfold `spectralNorm at h`. Rewrite `h` using `[spectralValue_le_one_iff (minpoly.monic hz)]`. Establish `hlift : minpoly ℚ_[l] z ∈ lifts (algebraMap ℤ_[l] ℚ_[l])`.

Rewrite using `[lifts_iff_coeff_lifts]`. Introduce `n`. Conclude with `⟨⟨_, h n⟩, rfl⟩`. Take `⟨q, hq, -, hqm⟩` from `lifts_and_natDegree_eq_and_monic hlift (minpoly.monic hz)`. Use `⟨q, hqm, ?_⟩` and prove the remaining obligations.

Rewrite using `[IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Om l), ← eval₂_map, hq, ← aeval_def]`. Conclude with `minpoly.aeval ℚ_[l] z`.
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
Express the relevant statement in the definitionally equal form `x ∈ integralClosure ℤ_[l] ↥K.1`. Rewrite using `[mem_integralClosure_iff]`. Use `haveI : IsScalarTower ℤ_[l] ↥K.1 (Om l) := IsScalarTower.of_algebraMap_eq fun z => by`. Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l), IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1]`. Both sides reduce to the same expression.

Establish `hinj : Function.Injective (IsScalarTower.toAlgHom ℤ_[l] ↥K.1 (Om l))` using `(algebraMap ↥K.1 (Om l)).injective`. Conclude with `(isIntegral_algHom_iff _ hinj).1 (isIntegral_of_norm_le_one _ h)`.
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
Use `K.2` as an intermediate fact. Conclude with `isCompact_iff_compactSpace.mp (IntermediateField.fixingSubgroup_isClosed K.1).isCompact`.
-/
theorem compactSpace_GK (K : FinExt l) : CompactSpace ↥(GK K) := by
  have := K.2
  exact isCompact_iff_compactSpace.mp (IntermediateField.fixingSubgroup_isClosed K.1).isCompact

/- English proof (translation)
Use `haveI := compactSpace_GK K`. Take `⟨M, hM⟩` from `(isCompact_range hc).isBounded.exists_norm_le`. Establish `hpow : ∀ n : ℕ, ‖(((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)‖ ^ n ≤ M` using `fun n => by`. Use `hM _ ⟨g ^ n, rfl⟩` as an intermediate fact. Simplify `this` using `[map_pow, norm_pow]`.

Assume the negation of the conclusion as `h`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt M (not_le.1 h)`. Conclude with `absurd (hpow n) (not_le.2 hn)`.
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
Introduce `hc g` and use `⟨⟨_, mem_OL_of_norm_le_one K _ (norm_le_one K χ hc g)⟩, rfl⟩`.
-/
theorem integral_values {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) :
    Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) →
    ∀ g, ∃ a : ↥(OL K), (a : ↥K.1) = ((χ g : (↥K.1)ˣ) : ↥K.1) := fun hc g =>
  ⟨⟨_, mem_OL_of_norm_le_one K _ (norm_le_one K χ hc g)⟩, rfl⟩

end GlobalTheory.CompanionTheory.LTPer.IntVal
