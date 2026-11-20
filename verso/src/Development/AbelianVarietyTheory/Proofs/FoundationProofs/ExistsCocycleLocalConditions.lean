import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CohomologyKernelModPrimePowerKilledByFixedPowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryInertiaIndependentStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemIntegersOfNormLeOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfMem

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.Unbounded

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem`. Consider the case `exact _root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem`. Consider the case `(apply _root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem ..)`.
-/
theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem
  | exact _root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem
  | (apply _root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem ..)

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]`. Conclude with `c.O.add_mem (c.O.mul_mem (hM i 0) (hx 0)) (c.O.mul_mem (hM i 1) (hx 1))`.
-/
theorem mulVec_mem (c : Coef l) {M : Matrix (Fin 2) (Fin 2) (Qbar l)} {x : Fin 2 → Qbar l}
    (hM : ∀ i j, M i j ∈ c.O) (hx : ∀ j, x j ∈ c.O) (i : Fin 2) : (M *ᵥ x) i ∈ c.O := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact c.O.add_mem (c.O.mul_mem (hM i 0) (hx 0)) (c.O.mul_mem (hM i 1) (hx 1))

/- English proof (translation)
The claim follows from `pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)`.
-/
theorem lpow_ne_zero (n : ℕ) : ((l : ℕ) : Qbar l) ^ n ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

/- English proof (translation)
Use `GlobalTheory.T.mem_integers_of_norm_le_one l c _ ⟨n, ?_⟩ ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, mul_inv_cancel₀ (lpow_ne_zero n), one_mul]`. Conclude with `c.O.sub_mem ha hb`. Rewrite using `[norm_mul, norm_inv]`. Establish `hp : 0 < ‖((l : ℕ) : Qbar l) ^ n‖` using `norm_pos_iff.2 (lpow_ne_zero n)`.

Rewrite using `[inv_mul_le_iff₀ hp, mul_one]`. Conclude with `h`.
-/
theorem inv_mul_sub_mem (c : Coef l) (n : ℕ) {a b : Qbar l} (ha : a ∈ c.O) (hb : b ∈ c.O) (h : Cg n a b) :
    (((l : ℕ) : Qbar l) ^ n)⁻¹ * (a - b) ∈ c.O := by
  refine GlobalTheory.T.mem_integers_of_norm_le_one l c _ ⟨n, ?_⟩ ?_
  · rw [← mul_assoc, mul_inv_cancel₀ (lpow_ne_zero n), one_mul]
    exact c.O.sub_mem ha hb
  · rw [norm_mul, norm_inv]
    have hp : 0 < ‖((l : ℕ) : Qbar l) ^ n‖ := norm_pos_iff.2 (lpow_ne_zero n)
    rw [inv_mul_le_iff₀ hp, mul_one]
    exact h

end GlobalTheory.Ord2.Unbounded

namespace GlobalTheory.Ord2.Unbounded

/- English proof (translation)
Introduce `l _ Ω _ _ _ S A W c hW hg H m`. Take `⟨r, hr⟩` from `GlobalTheory.T.cohomologyKernel_modPrimePower_killed_by_fixed_pow l Ω W c hW hg`. Take `⟨n, z, hcoc, hker, hine, hdec, hnot⟩` from `H (m + r)`. Establish `hz : ∀ s i, z s i ∈ c.O` using `hcoc.2.1`. Establish `hL0 : ((l : ℕ) : Qbar l) ^ n ≠ 0` using `lpow_ne_zero n`.

Use `set L : Qbar l := ((l : ℕ) : Qbar l) ^ n with hL`. Establish `hLO : L ∈ c.O` using `natPow_mem c n`. Set `ζ : G ℚ Ω → Fin 2 → Qbar l` to `fun s => L⁻¹ • z s`. Establish `hζ : ∀ s i, ζ s i = L⁻¹ * z s i` using `fun s i => rfl`. Establish `hmem : ζ ∈ divSelCoc c W S A`.

Use `⟨⟨n, fun s i => ?_⟩, fun s t i => ?_, fun s => ?_, fun a ha i => ?_, fun q hq hl B' hB' => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hζ, ← mul_assoc, ← hL, mul_inv_cancel₀ hL0, one_mul]`. Conclude with `hz s i`. Establish `e : ζ (s * t) i - ζ s i - (mat W s *ᵥ ζ t) i = L⁻¹ * (z (s * t) i - (z s + mat W s *ᵥ z t) i)`. Simplify using `only [ζ, Matrix.mulVec_smul, Pi.smul_apply, Pi.add_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `inv_mul_sub_mem c n (hz _ _) (c.O.add_mem (hz s i) (mulVec_mem c (hW s) (hz t) i)) (hcoc.2.2 s trivial t trivial i)`. Establish `hc : Continuous z`. Use `hcoc.1` as an intermediate fact.

Rewrite `this` using `[Subgroup.coe_top, continuousOn_univ]`. Conclude with `this`. Establish `hp : 0 < ‖L‖` using `norm_pos_iff.2 hL0`. Use `filter_upwards [Metric.tendsto_nhds.1 (hc.tendsto s) _ hp] with t ht i`. Establish `e : ζ t i - ζ s i = L⁻¹ * (z t i - z s i)`.

Simplify using `only [ζ, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `inv_mul_sub_mem c n (hz t i) (hz s i) ?_` and prove the remaining obligations. Unfold `Cg`.

Rewrite `ht` using `[dist_eq_norm]`. Conclude with `le_trans (norm_le_pi_norm (z t - z s) i) ht.le`. Establish `e : ζ a i = L⁻¹ * (z a i - 0)` using `by rw [sub_zero, hζ]`. Rewrite using `[e]`. Conclude with `inv_mul_sub_mem c n (hz a i) c.O.zero_mem (hker a ha i)`.

Take `⟨B, hB, hcob⟩` from `hine q hq hl`. Take `⟨x, hx, hxs⟩` from `GlobalTheory.T.coboundary_inertia_independent l Ω W c n z q B B' hW hcoc hB hB' hcob`. Use `⟨L⁻¹ • x, ⟨n, fun i => ?_⟩, fun s hs i => ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← hL, mul_inv_cancel₀ hL0, one_mul]`. Conclude with `hx i`.

Establish `e : ζ s i - (mat W s *ᵥ (L⁻¹ • x) - L⁻¹ • x) i = L⁻¹ * (z s i - (mat W s *ᵥ x - x) i)`. Simplify using `only [ζ, Matrix.mulVec_smul, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `inv_mul_sub_mem c n (hz s i) (c.O.sub_mem (mulVec_mem c (hW s) hx i) (hx i)) (hxs s hs i)`.

Take `⟨x, hx, hxs⟩` from `hdec`. Use `⟨L⁻¹ * x, ⟨n, ?_⟩, fun s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← hL, mul_inv_cancel₀ hL0, one_mul]`. Conclude with `hx`. Establish `e : ζ s 1 - (mat W s 1 1 * (L⁻¹ * x) - L⁻¹ * x) = L⁻¹ * (z s 1 - (mat W s 1 1 * x - x))`.

Rewrite using `[hζ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `inv_mul_sub_mem c n (hz s 1) (c.O.sub_mem (c.O.mul_mem (hW s 1 1) hx) hx) (hxs s hs)`. Use `⟨QuotientAddGroup.mk ⟨ζ, hmem⟩, fun h0 => hnot ?_⟩` and prove the remaining obligations.

Rewrite `h0` using `[← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]`. Take `⟨y, ⟨k, hk⟩, hy⟩` from `h0`. Establish `hy' : ∀ s i, ((l : ℕ) : Qbar l) ^ m * ζ s i - (mat W s *ᵥ y - y) i ∈ c.O`. Introduce `s i`. Use `hy s i` as an intermediate fact.

Simplify using `only [AddSubgroup.coe_nsmul, Pi.smul_apply, nsmul_eq_mul] at this`. Move the coercions through the operations in `at this`. Conclude with `this`. Establish `key` using `hr n (fun s => ((l : ℕ) : Qbar l) ^ m • z s) (L • y) (fun s i => by rw [Pi.smul_apply, smul_eq_mul]; exact c.O.mul_mem (natPow_mem c m) (hz s i)) ⟨k, fun i => by`. Rewrite using `[Pi.smul_apply, smul_eq_mul, mul_left_comm]`.

Conclude with `c.O.mul_mem hLO (hk i)⟩`. Use the proof step `(fun s i => by`. Establish `e : (((l : ℕ) : Qbar l) ^ m • z s) i - (mat W s *ᵥ (L • y) - L • y) i = L * (((l : ℕ) : Qbar l) ^ m * ζ s i - (mat W s *ᵥ y - y) i)`. Rewrite using `[hζ]`. Simplify using `only [Matrix.mulVec_smul, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]`.

Rewrite using `[mul_sub L, mul_sub L, mul_left_comm L, mul_inv_cancel_left₀ hL0]`. Unfold `Cg`. Rewrite using `[e, norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (norm_le_one_of_mem c (hy' s i)))`. Establish `hf : (fun s => ((l : ℕ) : Qbar l) ^ r • (fun s => ((l : ℕ) : Qbar l) ^ m • z s) s) = fun s => ((l : ℕ) : Qbar l) ^ (m + r) • z s`.

Use function extensionality and compare the values at `s`. Rewrite using `[smul_smul, ← pow_add, add_comm]`. Rewrite `key` using `[hf]`. Conclude with `key`.
-/
theorem divSel_unbounded : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), (∀ s i j, mat W s i j ∈ c.O) → (∃ g, (mat W g - 1).det ≠ 0) →
    (∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n W ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧
      (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n W (Ine (F := ℚ) B) z) ∧
      (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat W s 1 1 * x - x)) ∧
      ¬ Cob1 c n W ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s)) →
    ∀ m : ℕ, ∃ x : DivSel c W S A, l ^ m • x ≠ 0 := by
  intro l _ Ω _ _ _ S A W c hW hg H m
  obtain ⟨r, hr⟩ := GlobalTheory.T.cohomologyKernel_modPrimePower_killed_by_fixed_pow l Ω W c hW hg
  obtain ⟨n, z, hcoc, hker, hine, hdec, hnot⟩ := H (m + r)
  have hz : ∀ s i, z s i ∈ c.O := hcoc.2.1
  have hL0 : ((l : ℕ) : Qbar l) ^ n ≠ 0 := lpow_ne_zero n
  set L : Qbar l := ((l : ℕ) : Qbar l) ^ n with hL
  have hLO : L ∈ c.O := natPow_mem c n
  let ζ : G ℚ Ω → Fin 2 → Qbar l := fun s => L⁻¹ • z s
  have hζ : ∀ s i, ζ s i = L⁻¹ * z s i := fun s i => rfl
  have hmem : ζ ∈ divSelCoc c W S A := by
    refine ⟨⟨n, fun s i => ?_⟩, fun s t i => ?_, fun s => ?_, fun a ha i => ?_, fun q hq hl B' hB' => ?_, ?_⟩
    · rw [hζ, ← mul_assoc, ← hL, mul_inv_cancel₀ hL0, one_mul]; exact hz s i
    · have e : ζ (s * t) i - ζ s i - (mat W s *ᵥ ζ t) i = L⁻¹ * (z (s * t) i - (z s + mat W s *ᵥ z t) i) := by
        simp only [ζ, Matrix.mulVec_smul, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
      rw [e]
      exact inv_mul_sub_mem c n (hz _ _) (c.O.add_mem (hz s i) (mulVec_mem c (hW s) (hz t) i))
        (hcoc.2.2 s trivial t trivial i)
    · have hc : Continuous z := by
        have := hcoc.1
        rw [Subgroup.coe_top, continuousOn_univ] at this
        exact this
      have hp : 0 < ‖L‖ := norm_pos_iff.2 hL0
      filter_upwards [Metric.tendsto_nhds.1 (hc.tendsto s) _ hp] with t ht i
      have e : ζ t i - ζ s i = L⁻¹ * (z t i - z s i) := by
        simp only [ζ, Pi.smul_apply, smul_eq_mul]; ring
      rw [e]
      refine inv_mul_sub_mem c n (hz t i) (hz s i) ?_
      unfold Cg
      rw [dist_eq_norm] at ht
      exact le_trans (norm_le_pi_norm (z t - z s) i) ht.le
    · have e : ζ a i = L⁻¹ * (z a i - 0) := by rw [sub_zero, hζ]
      rw [e]
      exact inv_mul_sub_mem c n (hz a i) c.O.zero_mem (hker a ha i)
    · obtain ⟨B, hB, hcob⟩ := hine q hq hl
      obtain ⟨x, hx, hxs⟩ := GlobalTheory.T.coboundary_inertia_independent l Ω W c n z q B B' hW hcoc hB hB' hcob
      refine ⟨L⁻¹ • x, ⟨n, fun i => ?_⟩, fun s hs i => ?_⟩
      · rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← hL, mul_inv_cancel₀ hL0, one_mul]; exact hx i
      · have e : ζ s i - (mat W s *ᵥ (L⁻¹ • x) - L⁻¹ • x) i = L⁻¹ * (z s i - (mat W s *ᵥ x - x) i) := by
          simp only [ζ, Matrix.mulVec_smul, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
        rw [e]
        exact inv_mul_sub_mem c n (hz s i) (c.O.sub_mem (mulVec_mem c (hW s) hx i) (hx i)) (hxs s hs i)
    · obtain ⟨x, hx, hxs⟩ := hdec
      refine ⟨L⁻¹ * x, ⟨n, ?_⟩, fun s hs => ?_⟩
      · rw [← mul_assoc, ← hL, mul_inv_cancel₀ hL0, one_mul]; exact hx
      · have e : ζ s 1 - (mat W s 1 1 * (L⁻¹ * x) - L⁻¹ * x) = L⁻¹ * (z s 1 - (mat W s 1 1 * x - x)) := by
          rw [hζ]; ring
        rw [e]
        exact inv_mul_sub_mem c n (hz s 1) (c.O.sub_mem (c.O.mul_mem (hW s 1 1) hx) hx) (hxs s hs)
  refine ⟨QuotientAddGroup.mk ⟨ζ, hmem⟩, fun h0 => hnot ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h0
  obtain ⟨y, ⟨k, hk⟩, hy⟩ := h0
  have hy' : ∀ s i, ((l : ℕ) : Qbar l) ^ m * ζ s i - (mat W s *ᵥ y - y) i ∈ c.O := by
    intro s i
    have := hy s i
    simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, nsmul_eq_mul] at this
    push_cast at this
    exact this
  have key := hr n (fun s => ((l : ℕ) : Qbar l) ^ m • z s) (L • y)
    (fun s i => by rw [Pi.smul_apply, smul_eq_mul]; exact c.O.mul_mem (natPow_mem c m) (hz s i))
    ⟨k, fun i => by
      rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]; exact c.O.mul_mem hLO (hk i)⟩
    (fun s i => by
      have e : (((l : ℕ) : Qbar l) ^ m • z s) i - (mat W s *ᵥ (L • y) - L • y) i =
          L * (((l : ℕ) : Qbar l) ^ m * ζ s i - (mat W s *ᵥ y - y) i) := by
        rw [hζ]
        simp only [Matrix.mulVec_smul, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rw [mul_sub L, mul_sub L, mul_left_comm L, mul_inv_cancel_left₀ hL0]
      unfold Cg
      rw [e, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one_of_mem c (hy' s i)))
  have hf : (fun s => ((l : ℕ) : Qbar l) ^ r • (fun s => ((l : ℕ) : Qbar l) ^ m • z s) s) =
      fun s => ((l : ℕ) : Qbar l) ^ (m + r) • z s := by
    funext s; rw [smul_smul, ← pow_add, add_comm]
  rw [hf] at key
  exact key

end GlobalTheory.Ord2.Unbounded

end
