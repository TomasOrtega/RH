import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.EvUniq

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

variable (Ω) in

def zpHom : ℤ_[p] →+* Ω :=
  (algebraMap (O0 p) Ω).comp ((algebraMap (Lau p) (O0 p)).comp HahnSeries.C)

/- English proof (translation)
Simplify using `[zpHom, zp, HahnSeries.C_apply]`.
-/
theorem zpHom_apply (z : ℤ_[p]) : zpHom Ω z = zp Ω z := by
  simp [zpHom, zp, HahnSeries.C_apply]

/- English proof (translation)
Rewrite using `[← zpHom_apply, map_neg, zpHom_apply]`.
-/
theorem zp_neg (z : ℤ_[p]) : zp Ω (-z) = - zp Ω z := by
  rw [← zpHom_apply, map_neg, zpHom_apply]

/- English proof (translation)
Use `haveI := Basic.charZero_of_isClo hc`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `m hm`. Assume the negation of the conclusion as `h0`. Rewrite `hm` using `[PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast]`.

Establish `hu : zpHom Ω ((PadicInt.unitCoeff h0 : ℤ_[p])) ≠ 0` using `((Units.isUnit (PadicInt.unitCoeff h0)).map (zpHom Ω)).ne_zero`. Establish `hp0 : (p : Ω) ^ m.valuation ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)`. Conclude with `mul_ne_zero hu hp0 hm`.
-/
theorem zpHom_injective (hc : IsClo p Ω) : Function.Injective (zpHom (p := p) Ω) := by
  haveI := Basic.charZero_of_isClo hc
  rw [injective_iff_map_eq_zero]
  intro m hm
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hm
  have hu : zpHom Ω ((PadicInt.unitCoeff h0 : ℤ_[p])) ≠ 0 :=
    ((Units.isUnit (PadicInt.unitCoeff h0)).map (zpHom Ω)).ne_zero
  have hp0 : (p : Ω) ^ m.valuation ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  exact mul_ne_zero hu hp0 hm

/- English proof (translation)
Use `letI : Algebra ℤ_[p] Ω := (zpHom (p := p) Ω).toAlgebra`. Establish `hsm : ∀ (m : ℤ_[p]) (x : Ω), m • x = zp Ω m * x` using `fun m x => by`. Rewrite using `[Algebra.smul_def, RingHom.algebraMap_toAlgebra, zpHom_apply]`. Use `haveI : NoZeroSMulDivisors ℤ_[p] Ω := ⟨fun {m x} hmx => by`. Rewrite `hmx` using `[hsm]`.

Break down `mul_eq_zero.1 hmx with h0 | h0` into its components or cases. Use the proof step `left; exact zpHom_injective hc (by rw [zpHom_apply, h0, map_zero])`. Use `right`. Conclude with `h0⟩`. Set `S : Submodule ℤ_[p] Ω` to `Submodule.span ℤ_[p] (Set.range E)`.

Use `haveI : Module.Finite ℤ_[p] S := Module.Finite.span_of_finite _ (Set.finite_range E)`. Use `haveI : Module.Free ℤ_[p] S := Module.free_of_finite_type_torsion_free'`. Set `b` to `Module.Free.chooseBasis ℤ_[p] S`. Establish `hE : ∀ k, E k ∈ S` using `fun k => Submodule.subset_span ⟨k, rfl⟩`. Use `⟨Module.Free.ChooseBasisIndex ℤ_[p] S, inferInstance, fun i => (b i : Ω), fun k i => b.repr ⟨E k, hE k⟩ i, ?_, ?_⟩` and prove the remaining obligations.

Introduce `k`. Establish `h2` using `congrArg Subtype.val (b.sum_repr ⟨E k, hE k⟩)`. Rewrite `h2` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul, hsm] at h2`. Conclude with `h2.symm`.

Introduce `v hv i`. Establish `h0 : (∑ k, v k • (⟨E k, hE k⟩ : S)) = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul, hsm, Submodule.coe_zero]`.

Conclude with `hv`. Use `congrArg (fun s => b.repr s i) h0` as an intermediate fact. Simplify using `only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at this`. Conclude with `this`.
-/
theorem exists_coords (hc : IsClo p Ω) {ι : Type} [Fintype ι] (E : ι → Ω) :
    ∃ (κ : Type) (_ : Fintype κ) (f : κ → Ω) (M : ι → κ → ℤ_[p]),
      (∀ k, E k = ∑ i, zp Ω (M k i) * f i) ∧
      ∀ v : ι → ℤ_[p], ∑ k, zp Ω (v k) * E k = 0 → ∀ i, ∑ k, v k * M k i = 0 := by
  letI : Algebra ℤ_[p] Ω := (zpHom (p := p) Ω).toAlgebra
  have hsm : ∀ (m : ℤ_[p]) (x : Ω), m • x = zp Ω m * x := fun m x => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, zpHom_apply]
  haveI : NoZeroSMulDivisors ℤ_[p] Ω := ⟨fun {m x} hmx => by
    rw [hsm] at hmx
    rcases mul_eq_zero.1 hmx with h0 | h0
    · left; exact zpHom_injective hc (by rw [zpHom_apply, h0, map_zero])
    · right; exact h0⟩
  let S : Submodule ℤ_[p] Ω := Submodule.span ℤ_[p] (Set.range E)
  haveI : Module.Finite ℤ_[p] S := Module.Finite.span_of_finite _ (Set.finite_range E)
  haveI : Module.Free ℤ_[p] S := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ_[p] S
  have hE : ∀ k, E k ∈ S := fun k => Submodule.subset_span ⟨k, rfl⟩
  refine ⟨Module.Free.ChooseBasisIndex ℤ_[p] S, inferInstance, fun i => (b i : Ω),
    fun k i => b.repr ⟨E k, hE k⟩ i, ?_, ?_⟩
  · intro k
    have h2 := congrArg Subtype.val (b.sum_repr ⟨E k, hE k⟩)
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul, hsm] at h2
    exact h2.symm
  · intro v hv i
    have h0 : (∑ k, v k • (⟨E k, hE k⟩ : S)) = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul, hsm, Submodule.coe_zero]
      exact hv
    have := congrArg (fun s => b.repr s i) h0
    simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
    exact this

/- English proof (translation)
Rewrite using `[h.sub (HahnSeries.C m) (HahnSeries.C m), zp, HahnSeries.C_apply]`. Introduce `i`. Simplify using `only [HahnSeries.C_apply, HahnSeries.coeff_single]`. Distinguish the cases in `hi : i = 0`. Simplify using `[hi]`.

Establish `: (p : ℤ) ^ n * i ≠ 0` using `mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)) hi`. Simplify using `[hi, this]`. Introduce `r hr`. Establish `: r ≠ 0` using `by rintro rfl; exact hr (dvd_zero _)`. Simplify using `[HahnSeries.C_apply, HahnSeries.coeff_single, this]`.
-/
theorem psi_C {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) (m : ℤ_[p]) :
    ψ (algebraMap (Lau p) (O0 p) (HahnSeries.C m)) = zp Ω m := by
  rw [h.sub (HahnSeries.C m) (HahnSeries.C m), zp, HahnSeries.C_apply]
  · intro i
    simp only [HahnSeries.C_apply, HahnSeries.coeff_single]
    by_cases hi : i = 0
    · simp [hi]
    · have : (p : ℤ) ^ n * i ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)) hi
      simp [hi, this]
  · intro r hr
    have : r ≠ 0 := by rintro rfl; exact hr (dvd_zero _)
    simp [HahnSeries.C_apply, HahnSeries.coeff_single, this]

/- English proof (translation)
Take `⟨κ, _, f, M, hE, hind⟩` from `exists_coords hc E`. Establish `hB : ∀ i, ∑ k, HahnSeries.C (M k i) * G k = 0`. Introduce `i`. Use extensionality with `r`. Rewrite using `[HahnSeries.coeff_sum]`.

Simplify using `only [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, hG, HahnSeries.coeff_zero]`. Establish `h1` using `hind (fun k => (A k).coeff r) (by rw [← hA r]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _) i`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring`. Use `_ = 0 := by rw [h1, mul_zero]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [map_sum, map_mul, psi_C h, hE, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring`. Use `_ = 0 := by simp only [hB, map_zero, mul_zero, Finset.sum_const_zero]`.
-/
theorem sum_psi_eq_zero (hc : IsClo p Ω) {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ)
    {ι : Type} [Fintype ι] (E : ι → Ω) (A G : ι → Lau p) (φ : ℤ → ℤ_[p])
    (hA : ∀ r, ∑ k, E k * zp Ω ((A k).coeff r) = 0)
    (hG : ∀ k r, (G k).coeff r = φ r * (A k).coeff r) :
    ∑ k, E k * ψ (algebraMap (Lau p) (O0 p) (G k)) = 0 := by
  obtain ⟨κ, _, f, M, hE, hind⟩ := exists_coords hc E
  have hB : ∀ i, ∑ k, HahnSeries.C (M k i) * G k = 0 := by
    intro i
    ext r
    rw [HahnSeries.coeff_sum]
    simp only [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, hG,
      HahnSeries.coeff_zero]
    have h1 := hind (fun k => (A k).coeff r) (by rw [← hA r]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _) i
    calc ∑ k, M k i * (φ r * (A k).coeff r) = φ r * ∑ k, (A k).coeff r * M k i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      _ = 0 := by rw [h1, mul_zero]
  calc ∑ k, E k * ψ (algebraMap (Lau p) (O0 p) (G k))
      = ∑ i, f i * ψ (algebraMap (Lau p) (O0 p) (∑ k, HahnSeries.C (M k i) * G k)) := by
        simp only [map_sum, map_mul, psi_C h, hE, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    _ = 0 := by simp only [hB, map_zero, mul_zero, Finset.sum_const_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem thL_coeff (a : Lau p) (r : ℤ) : (thL a).coeff r = (r : ℤ_[p]) * a.coeff r := rfl

/- English proof (translation)
Introduce `p _ Ω _ _ hc T n ψ h c x x' y y' hx hy`. Take `⟨d, e, a, -, hca, rfl, rfl⟩` from `hx`. Take `⟨d', e', a', -, hca', rfl, rfl⟩` from `hy`. Set `E : Fin d ⊕ Fin d' → Ω` to `Sum.elim e e'`. Set `A : Fin d ⊕ Fin d' → Lau p` to `Sum.elim a (fun s => -a' s)`.

Establish `hA : ∀ r, ∑ k, E k * zp Ω ((A k).coeff r) = 0`. Introduce `r`. Simplify using `only [E, A, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, HahnSeries.coeff_neg, zp_neg, mul_neg, Finset.sum_neg_distrib]`. Take the linear combination `hca' r - hca r`. Establish `h1` using `sum_psi_eq_zero hc h E A A (fun _ => 1) hA (fun k r => by simp)`.

Establish `h2` using `sum_psi_eq_zero hc h E A (fun k => thL (A k)) (fun r => (r : ℤ_[p])) hA (fun k r => thL_coeff _ _)`. Establish `thL_neg : ∀ b : Lau p, thL (-b) = - thL b` using `fun b => by`. Use extensionality with `r`. Simplify using `only [thL_coeff, HahnSeries.coeff_neg]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [E, A, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, map_neg, mul_neg, Finset.sum_neg_distrib, thL_neg] at h1 h2`. Conclude with `⟨sub_eq_zero.1 (by simpa [sub_eq_add_neg] using h1), sub_eq_zero.1 (by simpa [sub_eq_add_neg] using h2)⟩`.
-/
theorem ev_unique : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∀ (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (c : ℤ → Ω) (x x' y y' : Ω),
    Ev ψ c x x' → Ev ψ c y y' → x = y ∧ x' = y' := by
  intro p _ Ω _ _ hc T n ψ h c x x' y y' hx hy
  obtain ⟨d, e, a, -, hca, rfl, rfl⟩ := hx
  obtain ⟨d', e', a', -, hca', rfl, rfl⟩ := hy
  let E : Fin d ⊕ Fin d' → Ω := Sum.elim e e'
  let A : Fin d ⊕ Fin d' → Lau p := Sum.elim a (fun s => -a' s)
  have hA : ∀ r, ∑ k, E k * zp Ω ((A k).coeff r) = 0 := by
    intro r
    simp only [E, A, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, HahnSeries.coeff_neg, zp_neg,
      mul_neg, Finset.sum_neg_distrib]
    linear_combination hca' r - hca r
  have h1 := sum_psi_eq_zero hc h E A A (fun _ => 1) hA (fun k r => by simp)
  have h2 := sum_psi_eq_zero hc h E A (fun k => thL (A k)) (fun r => (r : ℤ_[p])) hA
    (fun k r => thL_coeff _ _)
  have thL_neg : ∀ b : Lau p, thL (-b) = - thL b := fun b => by
    ext r; simp only [thL_coeff, HahnSeries.coeff_neg]; ring
  simp only [E, A, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, map_neg, mul_neg,
    Finset.sum_neg_distrib, thL_neg] at h1 h2
  exact ⟨sub_eq_zero.1 (by simpa [sub_eq_add_neg] using h1), sub_eq_zero.1 (by simpa [sub_eq_add_neg] using h2)⟩

end GlobalTheory.EvUniq
