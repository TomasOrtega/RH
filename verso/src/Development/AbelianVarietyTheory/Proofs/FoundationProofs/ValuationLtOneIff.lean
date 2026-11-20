import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerRankVanishing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.LengthValuationTwists

noncomputable section

namespace GlobalTheory.EmbInj

open Formalism.BasicNotions.Loc

section Local

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hx : IsIntegral ℚ_[l] x` using `Algebra.IsIntegral.isIntegral x`. Rewrite using `[← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)]`. Prove the components needed by the constructor for the conclusion. Introduce `h n`. Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]`.

Conclude with `((minpoly ℤ_[l] x).coeff n).2`. Introduce `h`. Establish `hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l])`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Conclude with `fun n => ⟨⟨_, h n⟩, rfl⟩`.

Take `⟨q, hq, -, hqm⟩` from `Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)`. Use `⟨q, hqm, ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]`.
-/
theorem isIntegral_iff_norm (x : Om l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact ((minpoly ℤ_[l] x).coeff n).2
  · intro h
    have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      exact fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

/- English proof (translation)
Rewrite using `[← isIntegral_iff_norm, OL, mem_integralClosure_iff]`. Conclude with `(isIntegral_algHom_iff (LL.1.val.restrictScalars ℤ_[l]) LL.1.val.toRingHom.injective).symm`.
-/
theorem mem_OL_iff (LL : FinExt l) (x : ↥LL.1) : x ∈ OL LL ↔ ‖(x : Om l)‖ ≤ 1 := by
  rw [← isIntegral_iff_norm, OL, mem_integralClosure_iff]
  exact (isIntegral_algHom_iff (LL.1.val.restrictScalars ℤ_[l]) LL.1.val.toRingHom.injective).symm

/- English proof (translation)
Rewrite using `[← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm]`. Establish `h1` using `minpoly.algHom_eq (L.1.val.comp τ) (L.1.val.comp τ).toRingHom.injective x`. Establish `h2` using `minpoly.algHom_eq K.1.val K.1.val.toRingHom.injective x`. Conclude with `congrArg spectralValue (h1.trans h2.symm)`.
-/
theorem norm_algHom (K L : FinExt l) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (x : ↥K.1) :
    ‖((τ x : ↥L.1) : Om l)‖ = ‖(x : Om l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm]
  have h1 := minpoly.algHom_eq (L.1.val.comp τ) (L.1.val.comp τ).toRingHom.injective x
  have h2 := minpoly.algHom_eq K.1.val K.1.val.toRingHom.injective x
  exact congrArg spectralValue (h1.trans h2.symm)

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type}
  [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (B : LocBridge l E Ω Gw O)

/- English proof (translation)
Rewrite using `[← mem_OL_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨B.eO.symm ⟨y, h⟩, ?_⟩` and prove the remaining obligations. Simplify using `[LocBridge.toLL]`.

Introduce and unpack `⟨n, rfl⟩`. Conclude with `(B.eO n).2`.
-/
theorem norm_le_one_iff (y : ↥B.LL.1) : ‖(y : Om l)‖ ≤ 1 ↔ ∃ n : O, y = B.toLL n := by
  rw [← mem_OL_iff]
  constructor
  · intro h
    refine ⟨B.eO.symm ⟨y, h⟩, ?_⟩
    simp [LocBridge.toLL]
  · rintro ⟨n, rfl⟩
    exact (B.eO n).2

/- English proof (translation)
Introduce `_ _ h` and use `B.eO.injective (Subtype.ext h)`.
-/
theorem toLL_inj : Function.Injective B.toLL := fun _ _ h => B.eO.injective (Subtype.ext h)

/- English proof (translation)
Distinguish the cases in `h : ‖(y : Om l)‖ ≤ 1`. Take `⟨n, hn⟩` from `(norm_le_one_iff B y).1 h`. Use `⟨n, 1, fun h1 => ?_, by simp [hn]⟩` and prove the remaining obligations. Use `congrArg B.toLL h1` as an intermediate fact. Simplify using `at this`.

Establish `hy : y ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h`. Establish `h' : ‖((y⁻¹ : ↥B.LL.1) : Om l)‖ ≤ 1`. Rewrite using `[IntermediateField.coe_inv, norm_inv]`.

Conclude with `inv_le_one_of_one_le₀ (not_le.1 h).le`. Take `⟨d, hd⟩` from `(norm_le_one_iff B _).1 h'`. Use `⟨1, d, fun h1 => ?_, by rw [← hd, map_one, inv_mul_cancel₀ hy]⟩` and prove the remaining obligations. Rewrite `hd` using `[h1, map_zero]`. Conclude with `hy (inv_eq_zero.1 hd)`.
-/
theorem exists_frac (y : ↥B.LL.1) : ∃ n d : O, d ≠ 0 ∧ B.toLL d * y = B.toLL n := by
  by_cases h : ‖(y : Om l)‖ ≤ 1
  · obtain ⟨n, hn⟩ := (norm_le_one_iff B y).1 h
    refine ⟨n, 1, fun h1 => ?_, by simp [hn]⟩
    have := congrArg B.toLL h1
    simp at this
  · have hy : y ≠ 0 := by
      rintro rfl
      simp at h
    have h' : ‖((y⁻¹ : ↥B.LL.1) : Om l)‖ ≤ 1 := by
      rw [IntermediateField.coe_inv, norm_inv]
      exact inv_le_one_of_one_le₀ (not_le.1 h).le
    obtain ⟨d, hd⟩ := (norm_le_one_iff B _).1 h'
    refine ⟨1, d, fun h1 => ?_, by rw [← hd, map_one, inv_mul_cancel₀ hy]⟩
    rw [h1, map_zero] at hd
    exact hy (inv_eq_zero.1 hd)

/- English proof (translation)
Use extensionality with `y`. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖((τ y : ↥B.LL.1) : Om l) - (τ' y : ↥B.LL.1)‖` using `norm_pos_iff.2 (sub_ne_zero.2 hne)`. Take `⟨_, ⟨x, rfl⟩, hx⟩` from `Metric.mem_closure_iff.1 (B.j_dense y.2) _ (half_pos hpos)`. Rewrite `hx` using `[dist_eq_norm]`.

Use `set z : ↥B.Kw.1 := ⟨B.j (algebraMap E Ω x), B.j_E x⟩ with hz`. Establish `e : ((τ y : ↥B.LL.1) : Om l) - (τ' y : ↥B.LL.1) = ((τ (y - z) : ↥B.LL.1) : Om l) - (τ' (y - z) : ↥B.LL.1)`. Rewrite using `[map_sub, map_sub, hz, h x]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `h1` using `norm_algHom _ _ τ (y - z)`. Establish `h2` using `norm_algHom _ _ τ' (y - z)`. Establish `h3` using `norm_sub_le ((τ (y - z) : ↥B.LL.1) : Om l) (τ' (y - z) : ↥B.LL.1)`. Establish `h4 : ‖((y - z : ↥B.Kw.1) : Om l)‖ < ‖((τ y : ↥B.LL.1) : Om l) - (τ' y : ↥B.LL.1)‖ / 2` using `hx`. Rewrite `h3` using `[← e, h1, h2]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem algHom_ext (τ τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥B.LL.1)
    (h : ∀ x : E, τ ⟨B.j (algebraMap E Ω x), B.j_E x⟩ = τ' ⟨B.j (algebraMap E Ω x), B.j_E x⟩) :
    τ = τ' := by
  ext y
  by_contra hne
  have hpos : 0 < ‖((τ y : ↥B.LL.1) : Om l) - (τ' y : ↥B.LL.1)‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.1 (B.j_dense y.2) _ (half_pos hpos)
  rw [dist_eq_norm] at hx
  set z : ↥B.Kw.1 := ⟨B.j (algebraMap E Ω x), B.j_E x⟩ with hz
  have e : ((τ y : ↥B.LL.1) : Om l) - (τ' y : ↥B.LL.1) =
      ((τ (y - z) : ↥B.LL.1) : Om l) - (τ' (y - z) : ↥B.LL.1) := by
    rw [map_sub, map_sub, hz, h x]
    push_cast
    ring
  have h1 := norm_algHom _ _ τ (y - z)
  have h2 := norm_algHom _ _ τ' (y - z)
  have h3 := norm_sub_le ((τ (y - z) : ↥B.LL.1) : Om l) (τ' (y - z) : ↥B.LL.1)
  have h4 : ‖((y - z : ↥B.Kw.1) : Om l)‖ < ‖((τ y : ↥B.LL.1) : Om l) - (τ' y : ↥B.LL.1)‖ / 2 := hx
  rw [← e, h1, h2] at h3
  linarith

end Local

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Establish `: A.valuation x ≠ 0` using `by simpa using hx`. Rewrite using `[← A.valuation_le_one_iff, map_inv₀, inv_le_one₀ (zero_lt_iff.2 this)]`. Simplify using `[hx]`.
-/
theorem valuation_lt_one_iff {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (x : Ω) :
    A.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ A := by
  by_cases hx : x = 0
  · simp [hx]
  · have : A.valuation x ≠ 0 := by simpa using hx
    rw [← A.valuation_le_one_iff, map_inv₀, inv_le_one₀ (zero_lt_iff.2 this)]
    simp [hx]

end GlobalTheory.EmbInj
