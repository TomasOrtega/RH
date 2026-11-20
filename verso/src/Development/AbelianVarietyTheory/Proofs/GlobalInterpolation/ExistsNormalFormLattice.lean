import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.QNormalShape

section Abstract

variable {O F : Type} [CommRing O] [Field F] [Algebra O F]

/- English proof (translation)
The claim follows from `b.mem_span_iff_repr_mem O v`.
-/
theorem mem_span_basis_iff [IsDomain O] [IsFractionRing O F] {N : ℕ} (b : Module.Basis (Fin N) F (Fin N → F)) (v : Fin N → F) :
    v ∈ Submodule.span O (Set.range b) ↔ ∀ l, b.repr v l ∈ Set.range (algebraMap O F) :=
  b.mem_span_iff_repr_mem O v

/- English proof (translation)
The claim follows from `Submodule.fg_span (Set.finite_range _) span_eq_top := by rw [Submodule.span_span_of_tower, b.span_eq]`.
-/
theorem isLattice_span_basis {N : ℕ} (b : Module.Basis (Fin N) F (Fin N → F)) :
    Submodule.IsLattice F (Submodule.span O (Set.range b)) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by rw [Submodule.span_span_of_tower, b.span_eq]

/- English proof (translation)
Unfold `IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.normalForm`. Rewrite using `[← Submodule.span_range_eq_iSup, Submodule.mem_sup]`. Simplify using `only [Submodule.mem_span_range_iff_exists_fun]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm, _, ⟨s, rfl⟩, rfl⟩`.

Conclude with `⟨m, hm, s, rfl⟩`. Introduce and unpack `⟨m, hm, s, rfl⟩`. Conclude with `⟨m, hm, _, ⟨s, rfl⟩, rfl⟩`.
-/
theorem mem_normalForm_iff {Y : Type} [AddCommGroup Y] [Module F Y] [Module O Y] {c : ℕ} (q : O)
    (M : Submodule O Y) (a : Fin c → Y) (e : Fin c → ℤ) (z y : Y) :
    y ∈ IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.normalForm F q M a e z ↔ ∃ m ∈ M, ∃ s : Fin c → O,
      y = m + ∑ i, s i • ((algebraMap O F q) ^ (e i) • (a i + if i.1 = 0 then z else 0)) := by
  unfold IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.normalForm
  rw [← Submodule.span_range_eq_iSup, Submodule.mem_sup]
  simp only [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨m, hm, _, ⟨s, rfl⟩, rfl⟩
    exact ⟨m, hm, s, rfl⟩
  · rintro ⟨m, hm, s, rfl⟩
    exact ⟨m, hm, _, ⟨s, rfl⟩, rfl⟩

/- English proof (translation)
Use `⟨h1, fun a b hab => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_or]`. Conclude with `h2 (hab ▸ pow_two (IsLocalRing.maximalIdeal O) ▸ Ideal.mul_mem_mul h.1 h.2)`.
-/
theorem irreducible_of_notMem_sq [IsDomain O] [IsDiscreteValuationRing O] {q : O}
    (h1 : q ∈ IsLocalRing.maximalIdeal O) (h2 : q ∉ IsLocalRing.maximalIdeal O ^ 2) : Irreducible q := by
  refine ⟨h1, fun a b hab => ?_⟩
  by_contra h
  rw [not_or] at h
  exact h2 (hab ▸ pow_two (IsLocalRing.maximalIdeal O) ▸ Ideal.mul_mem_mul h.1 h.2)

end Abstract

/- English proof (translation)
Introduce `H E _ _ _ P hd n c h`. Establish `hP` using `P.isPrime`. Establish `hS : P.asIdeal.primeCompl ≤ (𝓞 E)⁰` using `Ideal.primeCompl_le_nonZeroDivisors _`. Set `A` to `Localization.subalgebra.ofField E P.asIdeal.primeCompl hS`. Establish `: IsLocalization.AtPrime A P.asIdeal` using `Localization.subalgebra.isLocalization_ofField E _ hS`.

Establish `: IsDiscreteValuationRing A` using `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) P.ne_bot A`. Establish `: IsFractionRing A E` using `Localization.subalgebra.isFractionRing_ofField E _ hS`. Establish `hA : ∀ a : E, a ∈ Set.range (algebraMap A E) ↔ IntAt P a`. Introduce `a`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨x, r, s, hs, rfl⟩, rfl⟩`. Use `⟨r, s, hs, ?_⟩` and prove the remaining obligations. Establish `: algebraMap (𝓞 E) E s ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hS hs)`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E s * (algebraMap (𝓞 E) E r * (algebraMap (𝓞 E) E s)⁻¹) = _`. Clear the denominators using the available nonvanishing facts.

Introduce and unpack `⟨r, s, hs, e⟩`. Establish `: algebraMap (𝓞 E) E s ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hS hs)`. Use `⟨⟨a, r, s, hs, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[← e]`. Clear the denominators using the available nonvanishing facts.

Establish `hmax : Ideal.map (algebraMap (𝓞 E) A) P.asIdeal = IsLocalRing.maximalIdeal A` using `IsLocalization.AtPrime.map_eq_maximalIdeal P.asIdeal A`. Establish `hq : Irreducible (algebraMap (𝓞 E) A ((qOf P : ℕ) : 𝓞 E))`. Use `irreducible_of_notMem_sq ?_ ?_` and prove the remaining obligations. Rewrite using `[← hmax]`. Conclude with `Ideal.mem_map_of_mem _ (Ideal.absNorm_mem _)`.

Rewrite using `[← hmax, ← Ideal.map_pow, IsLocalization.algebraMap_mem_map_algebraMap_iff P.asIdeal.primeCompl]`. Introduce and unpack `⟨s, hs, hm⟩`. Conclude with `(Ideal.IsPrime.mul_mem_pow _ hm).elim hs hd.2`. Take `⟨r, hr, e, z, hz⟩` from `H A E _ hq n c _ (isLattice_span_basis (Pi.basisFun E (Fin n))) _ (isLattice_span_basis ((Pi.basisFun E (Fin (n + c))).map h))`. Use `⟨r, hr, e, z, ?_⟩` and prove the remaining obligations.

Establish `hqE : algebraMap A E (algebraMap (𝓞 E) A ((qOf P : ℕ) : 𝓞 E)) = (qOf P : E)`. Rewrite using `[map_natCast, map_natCast]`. Use extensionality with `y`. Establish `hy` using `SetLike.ext_iff.1 hz y`. Rewrite `hy` using `[mem_normalForm_iff, hqE]`.

Simplify using `only [IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.moveBy, Submodule.mem_map, mem_span_basis_iff, hA, Module.Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe] at hy`. Simplify using `only [Set.mem_image, Set.mem_setOf_eq, IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat, mem_stdAt_iff, IndefiniteRowSideFullHecke.SandwichNormalForm.nfGen]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩`. Take `⟨_, ⟨l, hl, rfl⟩, s, hs⟩` from `hy.1 ⟨h v, by simpa [IntV] using hv, rfl⟩`.

Conclude with `⟨l, hl, fun i => algebraMap A E (s i), fun i => (hA _).1 ⟨_, rfl⟩, by simpa only [algebraMap_smul] using hs⟩`. Introduce and unpack `⟨l, hl, s, hs, rfl⟩ choose t ht using fun i => (hA _).2 (hs i)`. Take `⟨v, hv, hv'⟩` from `hy.2 ⟨_, ⟨l, hl, rfl⟩, t, by simp only [← ht, algebraMap_smul]⟩`. Use `⟨h.symm v, hv, ?_⟩` and prove the remaining obligations. Rewrite using `[← hv']`.

Simplify using the standard rewrite rules.
-/
theorem exists_shape : GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.LatticeNormalFormCoord → ∀ (E : Type) [Field E] [NumberField E] [StarRing E]
    (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (n c : ℕ)
    (h : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)), ∃ r ∈ Loc.R1 E n c, ∃ (e : Fin c → ℤ) (z : Fin n → E),
      (r * h) '' {v | IntV P v} = GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P n c e z := by
  intro H E _ _ _ P hd n c h
  have hP := P.isPrime
  have hS : P.asIdeal.primeCompl ≤ (𝓞 E)⁰ := Ideal.primeCompl_le_nonZeroDivisors _
  let A := Localization.subalgebra.ofField E P.asIdeal.primeCompl hS
  have : IsLocalization.AtPrime A P.asIdeal := Localization.subalgebra.isLocalization_ofField E _ hS
  have : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) P.ne_bot A
  have : IsFractionRing A E := Localization.subalgebra.isFractionRing_ofField E _ hS
  have hA : ∀ a : E, a ∈ Set.range (algebraMap A E) ↔ IntAt P a := by
    intro a
    constructor
    · rintro ⟨⟨x, r, s, hs, rfl⟩, rfl⟩
      refine ⟨r, s, hs, ?_⟩
      have : algebraMap (𝓞 E) E s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hS hs)
      change algebraMap (𝓞 E) E s * (algebraMap (𝓞 E) E r * (algebraMap (𝓞 E) E s)⁻¹) = _
      field_simp
    · rintro ⟨r, s, hs, e⟩
      have : algebraMap (𝓞 E) E s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hS hs)
      refine ⟨⟨a, r, s, hs, ?_⟩, rfl⟩
      rw [← e]
      field_simp
  have hmax : Ideal.map (algebraMap (𝓞 E) A) P.asIdeal = IsLocalRing.maximalIdeal A :=
    IsLocalization.AtPrime.map_eq_maximalIdeal P.asIdeal A
  have hq : Irreducible (algebraMap (𝓞 E) A ((qOf P : ℕ) : 𝓞 E)) := by
    refine irreducible_of_notMem_sq ?_ ?_
    · rw [← hmax]
      exact Ideal.mem_map_of_mem _ (Ideal.absNorm_mem _)
    · rw [← hmax, ← Ideal.map_pow, IsLocalization.algebraMap_mem_map_algebraMap_iff P.asIdeal.primeCompl]
      rintro ⟨s, hs, hm⟩
      exact (Ideal.IsPrime.mul_mem_pow _ hm).elim hs hd.2
  obtain ⟨r, hr, e, z, hz⟩ := H A E _ hq n c _ (isLattice_span_basis (Pi.basisFun E (Fin n))) _
    (isLattice_span_basis ((Pi.basisFun E (Fin (n + c))).map h))
  refine ⟨r, hr, e, z, ?_⟩
  have hqE : algebraMap A E (algebraMap (𝓞 E) A ((qOf P : ℕ) : 𝓞 E)) = (qOf P : E) := by
    rw [map_natCast, map_natCast]
  ext y
  have hy := SetLike.ext_iff.1 hz y
  rw [mem_normalForm_iff, hqE] at hy
  simp only [IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.moveBy, Submodule.mem_map, mem_span_basis_iff, hA, Module.Basis.map_repr,
    LinearEquiv.trans_apply, Pi.basisFun_repr, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe] at hy
  simp only [Set.mem_image, Set.mem_setOf_eq, IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat, mem_stdAt_iff, IndefiniteRowSideFullHecke.SandwichNormalForm.nfGen]
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨_, ⟨l, hl, rfl⟩, s, hs⟩ := hy.1 ⟨h v, by simpa [IntV] using hv, rfl⟩
    exact ⟨l, hl, fun i => algebraMap A E (s i), fun i => (hA _).1 ⟨_, rfl⟩, by simpa only [algebraMap_smul] using hs⟩
  · rintro ⟨l, hl, s, hs, rfl⟩
    choose t ht using fun i => (hA _).2 (hs i)
    obtain ⟨v, hv, hv'⟩ := hy.2 ⟨_, ⟨l, hl, rfl⟩, t, by simp only [← ht, algebraMap_smul]⟩
    refine ⟨h.symm v, hv, ?_⟩
    rw [← hv']
    simp

end GlobalTheory.QNormalShape
