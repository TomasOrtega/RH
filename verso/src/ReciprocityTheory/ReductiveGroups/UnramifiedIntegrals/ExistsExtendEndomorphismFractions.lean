import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ExistsTeichmullerRepModPrime
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.MuMEvalPowEqZero

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Rewrite using `[norm_l_Cl]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)`.
-/
theorem norm_prime_lt_one_padicField : ‖(l : ℂ_[l])‖ < 1 := by
  rw [norm_l_Cl]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

/- English proof (translation)
Rewrite using `[norm_l_Cl]`. Conclude with `inv_pos.mpr (by exact_mod_cast (Fact.out : l.Prime).pos)`.
-/
theorem norm_prime_pos_padicField : 0 < ‖(l : ℂ_[l])‖ := by
  rw [norm_l_Cl]
  exact inv_pos.mpr (by exact_mod_cast (Fact.out : l.Prime).pos)

/- English proof (translation)
Take `⟨r, hr, h⟩` from `rmu_sigma_congr l s hs x`. Rewrite using `[h, norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (rmu_norm_le l hr)`.
-/
theorem frobeniusLift_near_pow (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l) :
    ‖((s x : Rmu l) : ℂ_[l]) - (x : ℂ_[l]) ^ l‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨r, hr, h⟩ := rmu_sigma_congr l s hs x
  rw [h, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (rmu_norm_le l hr)

/- English proof (translation)
Establish `h1 : ‖(x : ℂ_[l]) ^ l‖ = 1` using `by rw [norm_pow, hx, one_pow]`. Establish `h2 : ‖((s x : Rmu l) : ℂ_[l]) - (x : ℂ_[l]) ^ l‖ < ‖(x : ℂ_[l]) ^ l‖`. Rewrite using `[h1]`. Conclude with `lt_of_le_of_lt (frobeniusLift_near_pow l s hs x) (norm_prime_lt_one_padicField l)`. Establish `h3` using `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_lt h2)`.

Rewrite `h3` using `[sub_add_cancel, max_eq_right h2.le, h1]`. Conclude with `h3`.
-/
theorem frobeniusLift_norm_one (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l)
    (hx : ‖(x : ℂ_[l])‖ = 1) : ‖((s x : Rmu l) : ℂ_[l])‖ = 1 := by
  have h1 : ‖(x : ℂ_[l]) ^ l‖ = 1 := by rw [norm_pow, hx, one_pow]
  have h2 : ‖((s x : Rmu l) : ℂ_[l]) - (x : ℂ_[l]) ^ l‖ < ‖(x : ℂ_[l]) ^ l‖ := by
    rw [h1]; exact lt_of_le_of_lt (frobeniusLift_near_pow l s hs x) (norm_prime_lt_one_padicField l)
  have h3 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_lt h2)
  rw [sub_add_cancel, max_eq_right h2.le, h1] at h3
  exact h3

/- English proof (translation)
Distinguish the cases in `hx0 : x = 0`. Conclude with `⟨0, (Rmu l).zero_mem, 1, (Rmu l).one_mem, norm_one, by simp [hx0]⟩`. Take `⟨m, a, ha, b, hb, hna, hnb, h⟩` from `kmu_shape l hx hx0`. Establish `hb0 : b ≠ 0` using `by intro h0; rw [h0, norm_zero] at hnb; exact zero_ne_one hnb`. Establish `hn : ‖x‖ = ‖(l : ℂ_[l])‖ ^ m`.

Rewrite using `[h, norm_mul, norm_zpow, norm_div, hna, hnb]`. Simplify using the standard rewrite rules. Establish `hm : 0 ≤ m`. Assume the negation of the conclusion as `hneg`. Rewrite `hneg` using `[not_le]`.

Establish `: 1 < ‖(l : ℂ_[l])‖ ^ m` using `one_lt_zpow_of_neg₀ (norm_prime_pos_padicField l) (norm_prime_lt_one_padicField l) hneg`. Rewrite `this` using `[← hn]`. Conclude with `absurd h1 (not_le.mpr this)`. Take `⟨k, rfl⟩` from `Int.eq_ofNat_of_zero_le hm`. Use `⟨(l : ℂ_[l]) ^ k * a, (Rmu l).mul_mem ((Rmu l).pow_mem (natCast_mem _ l) k) ha, b, hb, hnb, ?_⟩` and prove the remaining obligations.

Rewrite using `[h, zpow_natCast]`. Clear the denominators using the available nonvanishing facts.
-/
theorem unitBall_eq_frac_normOne {x : ℂ_[l]} (hx : x ∈ Kmu l) (h1 : ‖x‖ ≤ 1) :
    ∃ a ∈ Rmu l, ∃ b ∈ Rmu l, ‖b‖ = 1 ∧ x * b = a := by
  by_cases hx0 : x = 0
  · exact ⟨0, (Rmu l).zero_mem, 1, (Rmu l).one_mem, norm_one, by simp [hx0]⟩
  obtain ⟨m, a, ha, b, hb, hna, hnb, h⟩ := kmu_shape l hx hx0
  have hb0 : b ≠ 0 := by intro h0; rw [h0, norm_zero] at hnb; exact zero_ne_one hnb
  have hn : ‖x‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [h, norm_mul, norm_zpow, norm_div, hna, hnb]; simp
  have hm : 0 ≤ m := by
    by_contra hneg
    rw [not_le] at hneg
    have : 1 < ‖(l : ℂ_[l])‖ ^ m :=
      one_lt_zpow_of_neg₀ (norm_prime_pos_padicField l) (norm_prime_lt_one_padicField l) hneg
    rw [← hn] at this
    exact absurd h1 (not_le.mpr this)
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  refine ⟨(l : ℂ_[l]) ^ k * a, (Rmu l).mul_mem ((Rmu l).pow_mem (natCast_mem _ l) k) ha,
    b, hb, hnb, ?_⟩
  rw [h, zpow_natCast]
  field_simp

/- English proof (translation)
Distinguish the cases in `hx0 : x = 0`. Simplify using `[hx0]`. Establish `hx0' : (x : ℂ_[l]) ≠ 0` using `fun h => hx0 (Subtype.ext h)`. Take `⟨m, a, ha, b, hb, hna, hnb, h⟩` from `kmu_shape l (rmu_le_kmu l x.2) hx0'`. Establish `hb0 : b ≠ 0` using `by intro h0; rw [h0, norm_zero] at hnb; exact zero_ne_one hnb`.

Establish `hn : ‖(x : ℂ_[l])‖ = ‖(l : ℂ_[l])‖ ^ m`. Rewrite using `[h, norm_mul, norm_zpow, norm_div, hna, hnb]`. Simplify using the standard rewrite rules. Establish `hm : 0 ≤ m`. Assume the negation of the conclusion as `hneg`.

Rewrite `hneg` using `[not_le]`. Establish `: 1 < ‖(l : ℂ_[l])‖ ^ m` using `one_lt_zpow_of_neg₀ (norm_prime_pos_padicField l) (norm_prime_lt_one_padicField l) hneg`. Rewrite `this` using `[← hn]`. Conclude with `absurd (rmu_norm_le l x.2) (not_le.mpr this)`. Take `⟨k, rfl⟩` from `Int.eq_ofNat_of_zero_le hm`.

Establish `he : x * (⟨b, hb⟩ : Rmu l) = (l : Rmu l) ^ k * (⟨a, ha⟩ : Rmu l)`. Apply `Subtype.ext` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[h, zpow_natCast]`. Clear the denominators using the available nonvanishing facts.

Establish `hs'` using `congrArg (fun z : Rmu l => ‖(z : ℂ_[l])‖) (congrArg s he)`. Simplify using `only [map_mul, map_pow, map_natCast] at hs'`. Move the coercions through the operations in `at hs'`. Rewrite `hs'` using `[norm_mul, norm_mul, norm_pow, frobeniusLift_norm_one l s hs ⟨b, hb⟩ hnb, frobeniusLift_norm_one l s hs ⟨a, ha⟩ hna, mul_one, mul_one]`. Rewrite using `[hs', hn, zpow_natCast]`.
-/
theorem rmu_sigma_norm (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l) :
    ‖((s x : Rmu l) : ℂ_[l])‖ = ‖(x : ℂ_[l])‖ := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx0' : (x : ℂ_[l]) ≠ 0 := fun h => hx0 (Subtype.ext h)
  obtain ⟨m, a, ha, b, hb, hna, hnb, h⟩ := kmu_shape l (rmu_le_kmu l x.2) hx0'
  have hb0 : b ≠ 0 := by intro h0; rw [h0, norm_zero] at hnb; exact zero_ne_one hnb
  have hn : ‖(x : ℂ_[l])‖ = ‖(l : ℂ_[l])‖ ^ m := by
    rw [h, norm_mul, norm_zpow, norm_div, hna, hnb]; simp
  have hm : 0 ≤ m := by
    by_contra hneg
    rw [not_le] at hneg
    have : 1 < ‖(l : ℂ_[l])‖ ^ m :=
      one_lt_zpow_of_neg₀ (norm_prime_pos_padicField l) (norm_prime_lt_one_padicField l) hneg
    rw [← hn] at this
    exact absurd (rmu_norm_le l x.2) (not_le.mpr this)
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  have he : x * (⟨b, hb⟩ : Rmu l) = (l : Rmu l) ^ k * (⟨a, ha⟩ : Rmu l) := by
    apply Subtype.ext
    push_cast
    rw [h, zpow_natCast]
    field_simp
  have hs' := congrArg (fun z : Rmu l => ‖(z : ℂ_[l])‖) (congrArg s he)
  simp only [map_mul, map_pow, map_natCast] at hs'
  push_cast at hs'
  rw [norm_mul, norm_mul, norm_pow, frobeniusLift_norm_one l s hs ⟨b, hb⟩ hnb,
    frobeniusLift_norm_one l s hs ⟨a, ha⟩ hna, mul_one, mul_one] at hs'
  rw [hs', hn, zpow_natCast]

section Generic

variable {K : Type*} [Field K] (R : Subring K) (F : Subfield K) (h : R ≤ F.toSubring)

def subringInclusionSubfield : R →+* F := Subring.inclusion h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem subringInclusionSubfield_coe (x : R) : ((subringInclusionSubfield R F h x : F) : K) = (x : K) := rfl

/- English proof (translation)
Introduce `x y e` and use `Subtype.ext (by rw [← subringInclusionSubfield_coe R F h, ← subringInclusionSubfield_coe R F h, e])`.
-/
theorem subringInclusionSubfield_injective : Function.Injective (subringInclusionSubfield R F h) := fun x y e =>
  Subtype.ext (by rw [← subringInclusionSubfield_coe R F h, ← subringInclusionSubfield_coe R F h, e])

/- English proof (translation)
Set `_ : Algebra R F` to `(subringInclusionSubfield R F h).toAlgebra`. Establish `: FaithfulSMul R F` using `(faithfulSMul_iff_algebraMap_injective _ _).mpr (subringInclusionSubfield_injective R F h)`. Apply `IsFractionRing.of_field` to reduce the goal to its premises. Introduce `z`. Take `⟨a, ha, b, hb, -, e⟩` from `hf z z.2`.

Use `⟨⟨a, ha⟩, ⟨b, hb⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Subfield.coe_div, e]`. Both sides reduce to the same expression.
-/
theorem isFractionRing_subringInclusion (hf : ∀ x ∈ F, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x = a / b) :
    @IsFractionRing R _ F _ (subringInclusionSubfield R F h).toAlgebra := by
  let _ : Algebra R F := (subringInclusionSubfield R F h).toAlgebra
  have : FaithfulSMul R F :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (subringInclusionSubfield_injective R F h)
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, ha, b, hb, -, e⟩ := hf z z.2
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, Subtype.ext ?_⟩
  rw [Subfield.coe_div, e]
  rfl

/- English proof (translation)
Set `_ : Algebra R F` to `(subringInclusionSubfield R F h).toAlgebra`. Establish `: IsFractionRing R F` using `isFractionRing_subringInclusion R F h hf`. Establish `hg : Function.Injective ((subringInclusionSubfield R F h).comp s)` using `(subringInclusionSubfield_injective R F h).comp hsinj`. Establish `hσ : ∀ x : R, IsFractionRing.lift hg (subringInclusionSubfield R F h x) = subringInclusionSubfield R F h (s x)` using `fun x => IsFractionRing.lift_algebraMap hg x`. Use `⟨IsFractionRing.lift hg, fun x a b e => ?_⟩` and prove the remaining obligations.

Establish `h' : x * subringInclusionSubfield R F h b = subringInclusionSubfield R F h a` using `Subtype.ext (by rw [Subfield.coe_mul, subringInclusionSubfield_coe, subringInclusionSubfield_coe, e])`. Establish `h2` using `congrArg (IsFractionRing.lift hg) h'`. Rewrite `h2` using `[map_mul, hσ, hσ]`. Rewrite using `[← subringInclusionSubfield_coe R F h, ← subringInclusionSubfield_coe R F h, ← Subfield.coe_mul, h2]`.
-/
theorem exists_extend_endomorphism_fractions (h : R ≤ F.toSubring) (hf : ∀ x ∈ F, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x = a / b)
    (s : R →+* R) (hsinj : Function.Injective s) :
    ∃ σ : F →+* F, ∀ (x : F) (a b : R), (x : K) * b = a →
      ((σ x : F) : K) * (s b : R) = (s a : R) := by
  let _ : Algebra R F := (subringInclusionSubfield R F h).toAlgebra
  have : IsFractionRing R F := isFractionRing_subringInclusion R F h hf
  have hg : Function.Injective ((subringInclusionSubfield R F h).comp s) := (subringInclusionSubfield_injective R F h).comp hsinj
  have hσ : ∀ x : R, IsFractionRing.lift hg (subringInclusionSubfield R F h x) = subringInclusionSubfield R F h (s x) :=
    fun x => IsFractionRing.lift_algebraMap hg x
  refine ⟨IsFractionRing.lift hg, fun x a b e => ?_⟩
  have h' : x * subringInclusionSubfield R F h b = subringInclusionSubfield R F h a :=
    Subtype.ext (by rw [Subfield.coe_mul, subringInclusionSubfield_coe, subringInclusionSubfield_coe, e])
  have h2 := congrArg (IsFractionRing.lift hg) h'
  rw [map_mul, hσ, hσ] at h2
  rw [← subringInclusionSubfield_coe R F h, ← subringInclusionSubfield_coe R F h, ← Subfield.coe_mul, h2]

end Generic

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Use `rmu_sigma_norm l s hs x` as an intermediate fact. Rewrite `this` using `[hx, Subring.coe_zero, norm_zero]`. Conclude with `Subtype.ext (norm_eq_zero.mp this.symm)`.
-/
theorem frobeniusLift_injective (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) : Function.Injective s := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have := rmu_sigma_norm l s hs x
  rw [hx, Subring.coe_zero, norm_zero] at this
  exact Subtype.ext (norm_eq_zero.mp this.symm)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem norm_unramifiedField_coe (x : Kmu l) : ‖x‖ = ‖(x : ℂ_[l])‖ := rfl

/- English proof (translation)
Take `⟨s, hs⟩` from `rmu_sigma l`. Take `⟨σ, key⟩` from `exists_extend_endomorphism_fractions (Rmu l) (Kmu l) (fun _ hx => rmu_le_kmu l hx) (fun _ hx => kmu_frac l hx) s (frobeniusLift_injective l s hs)`. Use `⟨σ, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Take `⟨a, ha, b, hb, hb0, h⟩` from `kmu_frac l x.2`.

Establish `h1 : (x : ℂ_[l]) * b = a` using `by rw [h]; field_simp`. Establish `h2` using `key x ⟨a, ha⟩ ⟨b, hb⟩ h1`. Establish `h3` using `congrArg norm h2`. Establish `h4` using `congrArg norm h1`. Rewrite `h3` using `[norm_mul, rmu_sigma_norm l s hs, rmu_sigma_norm l s hs]`.

Rewrite `h4` using `[norm_mul]`. Establish `hb' : ‖b‖ ≠ 0` using `norm_ne_zero_iff.mpr hb0`. Rewrite using `[norm_unramifiedField_coe, norm_unramifiedField_coe]`. Conclude with `mul_right_cancel₀ hb' (h3.trans h4.symm)`. Introduce `x hx`.

Rewrite `hx` using `[norm_unramifiedField_coe]`. Take `⟨a, ha, b, hb, hnb, h1⟩` from `unitBall_eq_frac_normOne l x.2 hx`. Establish `h2` using `key x ⟨a, ha⟩ ⟨b, hb⟩ h1`. Establish `hsb` using `frobeniusLift_norm_one l s hs ⟨b, hb⟩ hnb`. Establish `hna` using `frobeniusLift_near_pow l s hs ⟨a, ha⟩`.

Establish `hnb'` using `frobeniusLift_near_pow l s hs ⟨b, hb⟩`. Rewrite using `[norm_unramifiedField_coe, norm_unramifiedField_coe, Subfield.coe_sub, SubmonoidClass.coe_pow, SubringClass.coe_natCast]`. Generalize the expression as in `((s ⟨a, ha⟩ : Rmu l) : ℂ_[l]) = sa at h2 hna`. Generalize the expression as in `((s ⟨b, hb⟩ : Rmu l) : ℂ_[l]) = sb at h2 hnb' hsb`. Generalize the expression as in `((σ x : Kmu l) : ℂ_[l]) = y at h2 ⊢`.

Simplify using `only at hna hnb'`. Establish `e : (y - (x : ℂ_[l]) ^ l) * sb = (sa - a ^ l) + -((x : ℂ_[l]) ^ l * (sb - b ^ l))`. Rewrite using `[← h1, ← h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hxl : ‖(x : ℂ_[l]) ^ l‖ ≤ 1`.

Rewrite using `[norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) hx`. Establish `e2 : ‖(y - (x : ℂ_[l]) ^ l)‖ = ‖(sa - a ^ l) + -((x : ℂ_[l]) ^ l * (sb - b ^ l))‖`. Rewrite using `[← e, norm_mul, hsb, mul_one]`. Rewrite using `[e2]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hna ?_)` and prove the remaining obligations. Rewrite using `[norm_neg, norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) hxl).trans hnb'`.
-/
theorem kmu_sigma : ∃ s : Kmu l →+* Kmu l, (∀ x : Kmu l, ‖s x‖ = ‖x‖) ∧
    ∀ x : Kmu l, ‖x‖ ≤ 1 → ‖s x - x ^ l‖ ≤ ‖(l : Kmu l)‖ := by
  obtain ⟨s, hs⟩ := rmu_sigma l
  obtain ⟨σ, key⟩ := exists_extend_endomorphism_fractions (Rmu l) (Kmu l) (fun _ hx => rmu_le_kmu l hx)
    (fun _ hx => kmu_frac l hx) s (frobeniusLift_injective l s hs)
  refine ⟨σ, ?_, ?_⟩
  · intro x
    obtain ⟨a, ha, b, hb, hb0, h⟩ := kmu_frac l x.2
    have h1 : (x : ℂ_[l]) * b = a := by rw [h]; field_simp
    have h2 := key x ⟨a, ha⟩ ⟨b, hb⟩ h1
    have h3 := congrArg norm h2
    have h4 := congrArg norm h1
    rw [norm_mul, rmu_sigma_norm l s hs, rmu_sigma_norm l s hs] at h3
    rw [norm_mul] at h4
    have hb' : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb0
    rw [norm_unramifiedField_coe, norm_unramifiedField_coe]
    exact mul_right_cancel₀ hb' (h3.trans h4.symm)
  · intro x hx
    rw [norm_unramifiedField_coe] at hx
    obtain ⟨a, ha, b, hb, hnb, h1⟩ := unitBall_eq_frac_normOne l x.2 hx
    have h2 := key x ⟨a, ha⟩ ⟨b, hb⟩ h1
    have hsb := frobeniusLift_norm_one l s hs ⟨b, hb⟩ hnb
    have hna := frobeniusLift_near_pow l s hs ⟨a, ha⟩
    have hnb' := frobeniusLift_near_pow l s hs ⟨b, hb⟩
    rw [norm_unramifiedField_coe, norm_unramifiedField_coe, Subfield.coe_sub, SubmonoidClass.coe_pow, SubringClass.coe_natCast]
    generalize ((s ⟨a, ha⟩ : Rmu l) : ℂ_[l]) = sa at h2 hna
    generalize ((s ⟨b, hb⟩ : Rmu l) : ℂ_[l]) = sb at h2 hnb' hsb
    generalize ((σ x : Kmu l) : ℂ_[l]) = y at h2 ⊢
    simp only at hna hnb'
    have e : (y - (x : ℂ_[l]) ^ l) * sb = (sa - a ^ l) + -((x : ℂ_[l]) ^ l * (sb - b ^ l)) := by
      rw [← h1, ← h2]; ring
    have hxl : ‖(x : ℂ_[l]) ^ l‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    have e2 : ‖(y - (x : ℂ_[l]) ^ l)‖ = ‖(sa - a ^ l) + -((x : ℂ_[l]) ^ l * (sb - b ^ l))‖ := by
      rw [← e, norm_mul, hsb, mul_one]
    rw [e2]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hna ?_)
    rw [norm_neg, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hxl).trans hnb'

end ReciprocityTheory.ChartRestriction.L1
