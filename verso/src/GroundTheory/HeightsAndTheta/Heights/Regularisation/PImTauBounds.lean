import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Matrix Filter Topology

noncomputable section

/- English proof (translation)
Rewrite using `[Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_smul {g : ℕ} (M : Matrix (Fin g) (Fin g) ℝ) (t : ℝ) (v : Fin g → ℝ) :
    (t • v) ⬝ᵥ M *ᵥ (t • v) = t ^ 2 * (v ⬝ᵥ M *ᵥ v) := by
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)`.
-/
theorem dot_self_nonneg {g : ℕ} (v : Fin g → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

def unitSphereDot (g : ℕ) : Set (Fin g → ℝ) := {u | u ⬝ᵥ u = 1}

/- English proof (translation)
Establish `hc : IsClosed (unitSphereDot g)` using `isClosed_eq (continuous_id.dotProduct continuous_id) continuous_const`. Use `(isCompact_closedBall (0 : Fin g → ℝ) 1).of_isClosed_subset hc ?_` and prove the remaining obligations. Introduce `u hu`. Establish `hu' : u ⬝ᵥ u = 1` using `hu`. Rewrite using `[mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]`.

Introduce `i`. Rewrite using `[Real.norm_eq_abs, abs_le_one_iff_mul_self_le_one]`. Establish `: u i * u i ≤ u ⬝ᵥ u` using `Finset.single_le_sum (f := fun j => u j * u j) (fun j _ => mul_self_nonneg (u j)) (Finset.mem_univ i)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem isCompact_unitSphereDot (g : ℕ) : IsCompact (unitSphereDot g) := by
  have hc : IsClosed (unitSphereDot g) :=
    isClosed_eq (continuous_id.dotProduct continuous_id) continuous_const
  refine (isCompact_closedBall (0 : Fin g → ℝ) 1).of_isClosed_subset hc ?_
  intro u hu
  have hu' : u ⬝ᵥ u = 1 := hu
  rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs, abs_le_one_iff_mul_self_le_one]
  have : u i * u i ≤ u ⬝ᵥ u :=
    Finset.single_le_sum (f := fun j => u j * u j) (fun j _ => mul_self_nonneg (u j))
      (Finset.mem_univ i)
  linarith

/- English proof (translation)
Establish `hpos : 0 < v ⬝ᵥ v` using `lt_of_le_of_ne (dot_self_nonneg v) (fun h => hv (dotProduct_self_eq_zero.mp h.symm))`. Use `set s := Real.sqrt (v ⬝ᵥ v) with hs`. Establish `hs0 : 0 < s` using `Real.sqrt_pos.mpr hpos`. Establish `hs2 : s ^ 2 = v ⬝ᵥ v` using `Real.sq_sqrt hpos.le`. Establish `hvu : v = s • (s⁻¹ • v)` using `by rw [smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]`.

Use `⟨s⁻¹ • v, ?_, fun M => ?_⟩` and prove the remaining obligations. Use `show (s⁻¹ • v) ⬝ᵥ (s⁻¹ • v) = 1`. Use `quad_smul (1 : Matrix (Fin g) (Fin g) ℝ) s⁻¹ v` as an intermediate fact. Rewrite `this` using `[one_mulVec, one_mulVec]`. Rewrite using `[this, ← hs2]`.

Clear the denominators using the available nonvanishing facts. Use `conv_lhs => rw [hvu]`. Rewrite using `[quad_smul, hs2]`.
-/
theorem exists_unit_of_ne_zero {g : ℕ} {v : Fin g → ℝ} (hv : v ≠ 0) :
    ∃ u ∈ unitSphereDot g, ∀ M : Matrix (Fin g) (Fin g) ℝ,
      v ⬝ᵥ M *ᵥ v = (v ⬝ᵥ v) * (u ⬝ᵥ M *ᵥ u) := by
  have hpos : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (dot_self_nonneg v) (fun h => hv (dotProduct_self_eq_zero.mp h.symm))
  set s := Real.sqrt (v ⬝ᵥ v) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
  have hs2 : s ^ 2 = v ⬝ᵥ v := Real.sq_sqrt hpos.le
  have hvu : v = s • (s⁻¹ • v) := by rw [smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
  refine ⟨s⁻¹ • v, ?_, fun M => ?_⟩
  · show (s⁻¹ • v) ⬝ᵥ (s⁻¹ • v) = 1
    have := quad_smul (1 : Matrix (Fin g) (Fin g) ℝ) s⁻¹ v
    rw [one_mulVec, one_mulVec] at this
    rw [this, ← hs2]; field_simp
  · conv_lhs => rw [hvu]
    rw [quad_smul, hs2]

/- English proof (translation)
Establish `hΦ : Continuous fun q : Matrix (Fin g) (Fin g) ℝ × (Fin g → ℝ) => q.2 ⬝ᵥ q.1 *ᵥ q.2` using `continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd)`. Establish `hc : ContinuousOn (fun p : Z × (Fin g → ℝ) => p.2 ⬝ᵥ M p.1 *ᵥ p.2) (K ×ˢ unitSphereDot g)` using `hΦ.comp_continuousOn ((hM.comp continuous_fst.continuousOn fun p hp => hp.1).prodMk continuous_snd.continuousOn)`. Take `⟨A, hA⟩` from `(hK.prod (isCompact_unitSphereDot g)).exists_bound_of_continuousOn hc`. Use `⟨max A 0, le_max_right _ _, fun z hz v => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hv : v = 0`.

Substitute `hv` using the available equality. Simplify using the standard rewrite rules. Take `⟨u, hu, huM⟩` from `exists_unit_of_ne_zero hv`. Rewrite using `[huM]`. Establish `h1` using `hA (z, u) ⟨hz, hu⟩`.

Establish `h2 : u ⬝ᵥ M z *ᵥ u ≤ max A 0` using `((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h1)).trans (le_max_left _ _)`. Rewrite using `[mul_comm]`. Conclude with `mul_le_mul_of_nonneg_right h2 (dot_self_nonneg v)`.
-/
theorem quad_upper_core {Z : Type*} [TopologicalSpace Z] {g : ℕ} {K : Set Z} (hK : IsCompact K)
    (M : Z → Matrix (Fin g) (Fin g) ℝ) (hM : ContinuousOn M K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z ∈ K, ∀ v : Fin g → ℝ, v ⬝ᵥ M z *ᵥ v ≤ A * (v ⬝ᵥ v) := by
  have hΦ : Continuous fun q : Matrix (Fin g) (Fin g) ℝ × (Fin g → ℝ) => q.2 ⬝ᵥ q.1 *ᵥ q.2 :=
    continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd)
  have hc : ContinuousOn (fun p : Z × (Fin g → ℝ) => p.2 ⬝ᵥ M p.1 *ᵥ p.2)
      (K ×ˢ unitSphereDot g) :=
    hΦ.comp_continuousOn ((hM.comp continuous_fst.continuousOn fun p hp => hp.1).prodMk
      continuous_snd.continuousOn)
  obtain ⟨A, hA⟩ := (hK.prod (isCompact_unitSphereDot g)).exists_bound_of_continuousOn hc
  refine ⟨max A 0, le_max_right _ _, fun z hz v => ?_⟩
  by_cases hv : v = 0
  · subst hv; simp
  obtain ⟨u, hu, huM⟩ := exists_unit_of_ne_zero hv
  rw [huM]
  have h1 := hA (z, u) ⟨hz, hu⟩
  have h2 : u ⬝ᵥ M z *ᵥ u ≤ max A 0 :=
    ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h1)).trans (le_max_left _ _)
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right h2 (dot_self_nonneg v)

/- English proof (translation)
Establish `hSnn : ∀ v : Fin g → ℝ, 0 ≤ v ⬝ᵥ S *ᵥ v` using `fun v => by`. Simplify using `using (posSemidef_iff_dotProduct_mulVec.mp hS).2 v`. Establish `hΦ : Continuous fun q : Matrix (Fin g) (Fin g) ℝ × (Fin g → ℝ) => q.2 ⬝ᵥ q.1 *ᵥ q.2` using `continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd)`. Set `F : ℕ → Z × (Fin g → ℝ) → ℝ` to `fun m p => (m : ℝ) * (p.2 ⬝ᵥ S *ᵥ p.2) + p.2 ⬝ᵥ M p.1 *ᵥ p.2`. Establish `hFc : ∀ m, ContinuousOn (F m) (W ×ˢ Set.univ)`.

Introduce `m`. Establish `hQ : ContinuousOn (fun p : Z × (Fin g → ℝ) => p.2 ⬝ᵥ M p.1 *ᵥ p.2) (W ×ˢ Set.univ)` using `hΦ.comp_continuousOn ((hM.comp continuous_fst.continuousOn fun p hp => hp.1).prodMk continuous_snd.continuousOn)`. Establish `hS' : Continuous fun p : Z × (Fin g → ℝ) => p.2 ⬝ᵥ S *ᵥ p.2` using `continuous_snd.dotProduct (continuous_const.matrix_mulVec continuous_snd)`. Conclude with `(continuous_const.mul hS').continuousOn.add hQ`. Set `U : ℕ → Set (Z × (Fin g → ℝ))` to `fun m => (W ×ˢ Set.univ) ∩ F m ⁻¹' Set.Ioi (1 / ((m : ℝ) + 1))`.

Establish `hUo : ∀ m, IsOpen (U m)` using `fun m => (hFc m).isOpen_inter_preimage (hW.prod isOpen_univ) isOpen_Ioi`. Establish `hmono : Monotone U`. Introduce `m m' hmm' p hp`. Use `⟨hp.1, ?_⟩` and prove the remaining obligations. Establish `hp2 : 1 / ((m : ℝ) + 1) < F m p` using `hp.2`.

Establish `hmm : (m : ℝ) ≤ m'` using `Nat.cast_le.mpr hmm'`. Establish `h1 : F m p ≤ F m' p`. Use `hSnn p.2` as an intermediate fact. Use `show (m : ℝ) * (p.2 ⬝ᵥ S *ᵥ p.2) + _ ≤ (m' : ℝ) * (p.2 ⬝ᵥ S *ᵥ p.2) + _`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h2 : 1 / ((m' : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1)` using `by gcongr`. Use `show 1 / ((m' : ℝ) + 1) < F m' p`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcover : K ×ˢ unitSphereDot g ⊆ ⋃ m, U m`. Introduce and unpack `⟨z, u⟩ ⟨hz, hu⟩`.

Establish `hu' : u ⬝ᵥ u = 1` using `hu`. Establish `hu0 : u ≠ 0` using `by rintro rfl; simp at hu'`. Simplify using `only [Set.mem_iUnion]`. Establish `hm0 : ∀ m : ℕ, (0 : ℝ) ≤ m` using `fun m => Nat.cast_nonneg m`. Distinguish the cases in `hSu : S *ᵥ u = 0`.

Establish `hQ` using `hpos z hz u hu0 hSu`. Take `⟨m, hm⟩` from `exists_nat_one_div_lt hQ`. Use `⟨m, ⟨⟨hKW hz, trivial⟩, ?_⟩⟩` and prove the remaining obligations. Use `show 1 / ((m : ℝ) + 1) < (m : ℝ) * (u ⬝ᵥ S *ᵥ u) + u ⬝ᵥ M z *ᵥ u`. Use `hSnn u` as an intermediate fact.

Use polynomial arithmetic with `[hm0 m]`. Establish `hs : 0 < u ⬝ᵥ S *ᵥ u`. Use `lt_of_le_of_ne (hSnn u) (fun h => hSu ?_)` and prove the remaining obligations. Use `(hS.dotProduct_mulVec_zero_iff u).mp` as an intermediate fact. Simplify using `only [star_trivial] at this`.

Conclude with `this h.symm`. Take `⟨m, hm⟩` from `exists_nat_gt ((1 - u ⬝ᵥ M z *ᵥ u) / (u ⬝ᵥ S *ᵥ u))`. Use `⟨m, ⟨⟨hKW hz, trivial⟩, ?_⟩⟩` and prove the remaining obligations. Use `show 1 / ((m : ℝ) + 1) < (m : ℝ) * (u ⬝ᵥ S *ᵥ u) + u ⬝ᵥ M z *ᵥ u`. Establish `h1 : 1 - u ⬝ᵥ M z *ᵥ u < (m : ℝ) * (u ⬝ᵥ S *ᵥ u)` using `by rwa [div_lt_iff₀ hs] at hm`.

Establish `h2 : 1 / ((m : ℝ) + 1) ≤ 1`. Rewrite using `[div_le_one (by positivity)]; linarith [hm0 m]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨m, hm⟩` from `(hK.prod (isCompact_unitSphereDot g)).elim_directed_cover U hUo hcover hmono.directed_le`. Use `⟨m, 1 / ((m : ℝ) + 1), by positivity, fun z hz v => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hv : v = 0`. Substitute `hv` using the available equality. Simplify using the standard rewrite rules. Take `⟨u, hu, huM⟩` from `exists_unit_of_ne_zero hv`. Establish `hp : 1 / ((m : ℝ) + 1) < F m (z, u)` using `(hm ⟨hz, hu⟩).2`.

Establish `hvv` using `dot_self_nonneg v`. Rewrite using `[huM S, huM (M z)]`. Establish `h` using `mul_le_mul_of_nonneg_left hp.le hvv`. Simplify using `only [F] at h`. Use polynomial arithmetic with `[h]`.
-/
theorem quad_lower_core {Z : Type*} [TopologicalSpace Z] {g : ℕ} {K W : Set Z}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (M : Z → Matrix (Fin g) (Fin g) ℝ) (hM : ContinuousOn M W)
    (S : Matrix (Fin g) (Fin g) ℝ) (hS : S.PosSemidef)
    (hpos : ∀ z ∈ K, ∀ v : Fin g → ℝ, v ≠ 0 → S *ᵥ v = 0 → 0 < v ⬝ᵥ M z *ᵥ v) :
    ∃ L ε : ℝ, 0 < ε ∧ ∀ z ∈ K, ∀ v : Fin g → ℝ,
      ε * (v ⬝ᵥ v) ≤ L * (v ⬝ᵥ S *ᵥ v) + v ⬝ᵥ M z *ᵥ v := by
  have hSnn : ∀ v : Fin g → ℝ, 0 ≤ v ⬝ᵥ S *ᵥ v := fun v => by
    simpa using (posSemidef_iff_dotProduct_mulVec.mp hS).2 v
  have hΦ : Continuous fun q : Matrix (Fin g) (Fin g) ℝ × (Fin g → ℝ) => q.2 ⬝ᵥ q.1 *ᵥ q.2 :=
    continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd)
  let F : ℕ → Z × (Fin g → ℝ) → ℝ := fun m p =>
    (m : ℝ) * (p.2 ⬝ᵥ S *ᵥ p.2) + p.2 ⬝ᵥ M p.1 *ᵥ p.2
  have hFc : ∀ m, ContinuousOn (F m) (W ×ˢ Set.univ) := by
    intro m
    have hQ : ContinuousOn (fun p : Z × (Fin g → ℝ) => p.2 ⬝ᵥ M p.1 *ᵥ p.2) (W ×ˢ Set.univ) :=
      hΦ.comp_continuousOn ((hM.comp continuous_fst.continuousOn fun p hp => hp.1).prodMk
        continuous_snd.continuousOn)
    have hS' : Continuous fun p : Z × (Fin g → ℝ) => p.2 ⬝ᵥ S *ᵥ p.2 :=
      continuous_snd.dotProduct (continuous_const.matrix_mulVec continuous_snd)
    exact (continuous_const.mul hS').continuousOn.add hQ
  let U : ℕ → Set (Z × (Fin g → ℝ)) := fun m =>
    (W ×ˢ Set.univ) ∩ F m ⁻¹' Set.Ioi (1 / ((m : ℝ) + 1))
  have hUo : ∀ m, IsOpen (U m) := fun m =>
    (hFc m).isOpen_inter_preimage (hW.prod isOpen_univ) isOpen_Ioi
  have hmono : Monotone U := by
    intro m m' hmm' p hp
    refine ⟨hp.1, ?_⟩
    have hp2 : 1 / ((m : ℝ) + 1) < F m p := hp.2
    have hmm : (m : ℝ) ≤ m' := Nat.cast_le.mpr hmm'
    have h1 : F m p ≤ F m' p := by
      have := hSnn p.2
      show (m : ℝ) * (p.2 ⬝ᵥ S *ᵥ p.2) + _ ≤ (m' : ℝ) * (p.2 ⬝ᵥ S *ᵥ p.2) + _
      nlinarith
    have h2 : 1 / ((m' : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by gcongr
    show 1 / ((m' : ℝ) + 1) < F m' p
    linarith
  have hcover : K ×ˢ unitSphereDot g ⊆ ⋃ m, U m := by
    rintro ⟨z, u⟩ ⟨hz, hu⟩
    have hu' : u ⬝ᵥ u = 1 := hu
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu'
    simp only [Set.mem_iUnion]
    have hm0 : ∀ m : ℕ, (0 : ℝ) ≤ m := fun m => Nat.cast_nonneg m
    by_cases hSu : S *ᵥ u = 0
    · have hQ := hpos z hz u hu0 hSu
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hQ
      refine ⟨m, ⟨⟨hKW hz, trivial⟩, ?_⟩⟩
      show 1 / ((m : ℝ) + 1) < (m : ℝ) * (u ⬝ᵥ S *ᵥ u) + u ⬝ᵥ M z *ᵥ u
      have := hSnn u
      nlinarith [hm0 m]
    · have hs : 0 < u ⬝ᵥ S *ᵥ u := by
        refine lt_of_le_of_ne (hSnn u) (fun h => hSu ?_)
        have := (hS.dotProduct_mulVec_zero_iff u).mp
        simp only [star_trivial] at this
        exact this h.symm
      obtain ⟨m, hm⟩ := exists_nat_gt ((1 - u ⬝ᵥ M z *ᵥ u) / (u ⬝ᵥ S *ᵥ u))
      refine ⟨m, ⟨⟨hKW hz, trivial⟩, ?_⟩⟩
      show 1 / ((m : ℝ) + 1) < (m : ℝ) * (u ⬝ᵥ S *ᵥ u) + u ⬝ᵥ M z *ᵥ u
      have h1 : 1 - u ⬝ᵥ M z *ᵥ u < (m : ℝ) * (u ⬝ᵥ S *ᵥ u) := by rwa [div_lt_iff₀ hs] at hm
      have h2 : 1 / ((m : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [hm0 m]
      linarith
  obtain ⟨m, hm⟩ := (hK.prod (isCompact_unitSphereDot g)).elim_directed_cover U hUo hcover
    hmono.directed_le
  refine ⟨m, 1 / ((m : ℝ) + 1), by positivity, fun z hz v => ?_⟩
  by_cases hv : v = 0
  · subst hv; simp
  obtain ⟨u, hu, huM⟩ := exists_unit_of_ne_zero hv
  have hp : 1 / ((m : ℝ) + 1) < F m (z, u) := (hm ⟨hz, hu⟩).2
  have hvv := dot_self_nonneg v
  rw [huM S, huM (M z)]
  have h := mul_le_mul_of_nonneg_left hp.le hvv
  simp only [F] at h
  nlinarith [h]

namespace PeriodPolydisc

variable {n a g : ℕ} (P : PeriodPolydisc n a g)

def realB (i : Fin a) : Matrix (Fin g) (Fin g) ℝ := (P.B i).map (Int.cast : ℤ → ℝ)

/- English proof (translation)
Establish `hτ : P.τ w = T0 (expCover a w) + ∑ i : Fin a, (w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I)) • (P.B i).map (Int.cast : ℤ → ℂ)`. Rewrite using `[← hT0.2 w hw, PeriodPolydisc.tau0, sub_add_cancel]`. Use extensionality with `p q`. Rewrite using `[hτ]`. Simplify using `[Matrix.sum_apply, Complex.im_sum, Complex.mul_im, im_div_two_pi_I, realB]`.
-/
theorem im_tau_eq {T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ} (hT0 : P.IsTau0Ext T0)
    {w : Fin n → ℂ} (hw : w ∈ logCover P.a_le) :
    (P.τ w).map Complex.im = (T0 (expCover a w)).map Complex.im +
      ∑ i : Fin a, (-(w (Fin.castLE P.a_le i)).re / (2 * Real.pi)) • P.realB i := by
  have hτ : P.τ w = T0 (expCover a w) + ∑ i : Fin a,
      (w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I)) • (P.B i).map (Int.cast : ℤ → ℂ) := by
    rw [← hT0.2 w hw, PeriodPolydisc.tau0, sub_add_cancel]
  ext p q
  rw [hτ]
  simp [Matrix.sum_apply, Complex.im_sum, Complex.mul_im, im_div_two_pi_I, realB]

end PeriodPolydisc

/- English proof (translation)
Rewrite using `[Matrix.add_mulVec, dotProduct_add, Matrix.sum_mulVec, dotProduct_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]`.
-/
theorem quad_add_sum {g a : ℕ} (A : Matrix (Fin g) (Fin g) ℝ) (l : Fin a → ℝ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (v : Fin g → ℝ) :
    v ⬝ᵥ (A + ∑ i, l i • B i) *ᵥ v = v ⬝ᵥ A *ᵥ v + ∑ i, l i * (v ⬝ᵥ B i *ᵥ v) := by
  rw [Matrix.add_mulVec, dotProduct_add, Matrix.sum_mulVec, dotProduct_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Introduce `n a g P`. Take `⟨hB, T0, hT0⟩` from `h0 n a g P`. Establish `hBpsd : ∀ i, (P.realB i).PosSemidef` using `hB`. Establish `hBnn : ∀ i (v : Fin g → ℝ), 0 ≤ v ⬝ᵥ P.realB i *ᵥ v` using `fun i v => by`. Simplify using `using (posSemidef_iff_dotProduct_mulVec.mp (hBpsd i)).2 v`.

Use `set S := ∑ i, P.realB i with hSdef`. Establish `hSv : ∀ v : Fin g → ℝ, v ⬝ᵥ S *ᵥ v = ∑ i, v ⬝ᵥ P.realB i *ᵥ v` using `fun v => by`. Rewrite using `[hSdef, Matrix.sum_mulVec, dotProduct_sum]`. Establish `hS : S.PosSemidef` using `posSemidef_sum Finset.univ fun i _ => hBpsd i`. Use `set Mz : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℝ := fun z => (T0 z).map Complex.im with hMz`.

Establish `hMc : ContinuousOn Mz (ball 0 1)`. Use `continuousOn_pi.mpr fun p => continuousOn_pi.mpr fun q => ?_` and prove the remaining obligations. Conclude with `Complex.continuous_im.comp_continuousOn (hT0.1 p q).continuousOn`. Establish `hK : IsCompact (closedBall (0 : Fin n → ℂ) (1 / 2))` using `isCompact_closedBall _ _`. Establish `hKW : closedBall (0 : Fin n → ℂ) (1 / 2) ⊆ ball 0 1` using `closedBall_subset_ball (by norm_num)`.

Establish `hpos : ∀ z ∈ closedBall (0 : Fin n → ℂ) (1 / 2), ∀ v : Fin g → ℝ, v ≠ 0 → S *ᵥ v = 0 → 0 < v ⬝ᵥ Mz z *ᵥ v`. Introduce `z hz v hv hSv0`. Use `h1 n a g P T0 hT0 v hv (fun i => ?_) z (hKW hz)` and prove the remaining obligations. Establish `h` using `hSv v`. Rewrite `h` using `[hSv0, dotProduct_zero]`.

Establish `hi` using `(Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hBnn j v)).mp h.symm i (Finset.mem_univ i)`. Use `((hBpsd i).dotProduct_mulVec_zero_iff v).mp` as an intermediate fact. Simplify using `only [star_trivial] at this`. Conclude with `this hi`. Take `⟨L, ε, hε, hlow⟩` from `quad_lower_core hK isOpen_ball hKW Mz hMc S hS hpos`.

Take `⟨A, hA0, hA⟩` from `quad_upper_core hK Mz (hMc.mono hKW)`. Establish `hBup : ∀ i, ∃ β : ℝ, 0 ≤ β ∧ ∀ v : Fin g → ℝ, v ⬝ᵥ P.realB i *ᵥ v ≤ β * (v ⬝ᵥ v)`. Introduce `i`. Take `⟨β, hβ0, hβ⟩` from `quad_upper_core hK (fun _ => P.realB i) continuousOn_const`. Conclude with `⟨β, hβ0, hβ 0 (mem_closedBall_self (by norm_num))⟩`.

Use `choose β hβ0 hβ using hBup`. Use `⟨min (1 / 2) (Real.exp (-(2 * Real.pi) * L)), ε, A + ∑ i, β i, lt_min (by norm_num) (Real.exp_pos _), lt_of_le_of_lt (min_le_left _ _) (by norm_num), hε, ?_⟩` and prove the remaining obligations. Introduce `w hw hz`. Establish `hzK : expCover a w ∈ closedBall (0 : Fin n → ℂ) (1 / 2)` using `closedBall_subset_closedBall (min_le_left _ _) hz`. Establish `hdec` using `P.im_tau_eq hT0 hw`.

Use `set z := expCover a w with hzdef`. Use `set l : Fin a → ℝ := fun i => -(w (Fin.castLE P.a_le i)).re / (2 * Real.pi) with hl`. Establish `hquad : ∀ v : Fin g → ℝ, v ⬝ᵥ (P.τ w).map Complex.im *ᵥ v = v ⬝ᵥ Mz z *ᵥ v + ∑ i, l i * (v ⬝ᵥ P.realB i *ᵥ v)`. Introduce `v`. Rewrite using `[hdec]`.

Conclude with `quad_add_sum _ _ _ v`. Establish `hzi : ∀ i : Fin a, z (Fin.castLE P.a_le i) = Complex.exp (w (Fin.castLE P.a_le i))`. Introduce `i`. Simplify using `[hzdef, expCover, i.isLt]`. Establish `hre : ∀ i : Fin a, (w (Fin.castLE P.a_le i)).re < 0` using `hw.1`.

Establish `hnorm : ∀ i : Fin a, Real.exp (w (Fin.castLE P.a_le i)).re ≤ Real.exp (-(2 * Real.pi) * L)`. Introduce `i`. Establish `h1 : ‖z (Fin.castLE P.a_le i)‖ ≤ ‖z‖` using `norm_le_pi_norm z _`. Establish `h2 : ‖z‖ ≤ min (1 / 2) (Real.exp (-(2 * Real.pi) * L))`. Simplify `hz` using `[mem_closedBall, dist_zero_right]`.

Rewrite `h1` using `[hzi, Complex.norm_exp]`. Conclude with `h1.trans (h2.trans (min_le_right _ _))`. Establish `hlL : ∀ i, L ≤ l i`. Introduce `i`. Use `Real.exp_le_exp.mp (hnorm i)` as an intermediate fact.

Use `show L ≤ -(w (Fin.castLE P.a_le i)).re / (2 * Real.pi)`. Rewrite using `[le_div_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hterm : ∀ j : Fin a, Real.log (‖cuspCoord P.a_le z j‖ ^ 2)⁻¹ = -2 * (w (Fin.castLE P.a_le j)).re`. Introduce `j`.

Rewrite using `[cuspCoord, hzi, Complex.norm_exp, Real.log_inv, Real.log_pow, Real.log_exp]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hsum0 : 0 ≤ ∑ j, Real.log (‖cuspCoord P.a_le z j‖ ^ 2)⁻¹` using `Finset.sum_nonneg fun j _ => by rw [hterm j]; linarith [hre j]`. Establish `hr1 : 1 ≤ chartRadius P.a_le z`.

Rewrite using `[chartRadius]`. Establish `he : 1 ≤ Real.exp 1` using `by have := Real.add_one_le_exp 1; linarith`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlr : ∀ i, l i ≤ chartRadius P.a_le z`. Introduce `i`.

Rewrite using `[chartRadius]`. Establish `hsum : -2 * (w (Fin.castLE P.a_le i)).re ≤ ∑ j, Real.log (‖cuspCoord P.a_le z j‖ ^ 2)⁻¹`. Rewrite using `[← hterm i]`. Conclude with `Finset.single_le_sum (f := fun j => Real.log (‖cuspCoord P.a_le z j‖ ^ 2)⁻¹) (fun j _ => by rw [hterm j]; linarith [hre j]) (Finset.mem_univ i)`. Establish `hli : l i ≤ -2 * (w (Fin.castLE P.a_le i)).re` using `by show -(w (Fin.castLE P.a_le i)).re / (2 * Real.pi) ≤ _`.

Rewrite using `[div_le_iff₀ (by positivity)]`. Use `hre i` as an intermediate fact. Use polynomial arithmetic with `[Real.pi_gt_three]`. Establish `he : 0 ≤ Real.exp 1` using `(Real.exp_pos 1).le`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hsymm : ((P.τ w).map Complex.im)ᵀ = (P.τ w).map Complex.im`. Rewrite using `[← Matrix.transpose_map, P.symm w hw]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[posSemidef_iff_dotProduct_mulVec]`. Use `⟨?_, fun v => ?_⟩` and prove the remaining obligations.

Rewrite using `[IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_smul, transpose_one, hsymm]`. Simplify using `only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]`. Rewrite using `[hquad]`. Establish `h1` using `hlow z hzK v`. Rewrite `h1` using `[hSv, Finset.mul_sum]`.

Establish `h2 : ∑ i, L * (v ⬝ᵥ P.realB i *ᵥ v) ≤ ∑ i, l i * (v ⬝ᵥ P.realB i *ᵥ v)` using `Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hlL i) (hBnn i v)`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[posSemidef_iff_dotProduct_mulVec]`. Use `⟨?_, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_smul, transpose_one, hsymm]`.

Simplify using `only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]`. Rewrite using `[hquad]`. Establish `hvv` using `dot_self_nonneg v`. Establish `h1` using `hA z hzK v`. Establish `h2 : ∑ i, l i * (v ⬝ᵥ P.realB i *ᵥ v) ≤ ∑ i, chartRadius P.a_le z * (β i * (v ⬝ᵥ v))` using `Finset.sum_le_sum fun i _ => mul_le_mul (hlr i) (hβ i v) (hBnn i v) (by linarith)`.

Establish `h3 : ∑ i, chartRadius P.a_le z * (β i * (v ⬝ᵥ v)) = chartRadius P.a_le z * (∑ i, β i) * (v ⬝ᵥ v)`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Establish `h4 : A * (v ⬝ᵥ v) ≤ A * chartRadius P.a_le z * (v ⬝ᵥ v)`. Use `mul_le_mul_of_nonneg_left hr1 (mul_nonneg hA0 hvv)` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem ImTauBounds.proof (h0 : Tau0Holomorphic.Statement) (h1 : KernelPositive.Statement) :
    ImTauBounds.Statement := by
  intro n a g P
  obtain ⟨hB, T0, hT0⟩ := h0 n a g P
  have hBpsd : ∀ i, (P.realB i).PosSemidef := hB
  have hBnn : ∀ i (v : Fin g → ℝ), 0 ≤ v ⬝ᵥ P.realB i *ᵥ v := fun i v => by
    simpa using (posSemidef_iff_dotProduct_mulVec.mp (hBpsd i)).2 v
  set S := ∑ i, P.realB i with hSdef
  have hSv : ∀ v : Fin g → ℝ, v ⬝ᵥ S *ᵥ v = ∑ i, v ⬝ᵥ P.realB i *ᵥ v := fun v => by
    rw [hSdef, Matrix.sum_mulVec, dotProduct_sum]
  have hS : S.PosSemidef := posSemidef_sum Finset.univ fun i _ => hBpsd i
  set Mz : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℝ := fun z => (T0 z).map Complex.im with hMz
  have hMc : ContinuousOn Mz (ball 0 1) := by
    refine continuousOn_pi.mpr fun p => continuousOn_pi.mpr fun q => ?_
    exact Complex.continuous_im.comp_continuousOn (hT0.1 p q).continuousOn
  have hK : IsCompact (closedBall (0 : Fin n → ℂ) (1 / 2)) := isCompact_closedBall _ _
  have hKW : closedBall (0 : Fin n → ℂ) (1 / 2) ⊆ ball 0 1 :=
    closedBall_subset_ball (by norm_num)
  have hpos : ∀ z ∈ closedBall (0 : Fin n → ℂ) (1 / 2), ∀ v : Fin g → ℝ, v ≠ 0 →
      S *ᵥ v = 0 → 0 < v ⬝ᵥ Mz z *ᵥ v := by
    intro z hz v hv hSv0
    refine h1 n a g P T0 hT0 v hv (fun i => ?_) z (hKW hz)
    have h := hSv v
    rw [hSv0, dotProduct_zero] at h
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hBnn j v)).mp h.symm i
      (Finset.mem_univ i)
    have := ((hBpsd i).dotProduct_mulVec_zero_iff v).mp
    simp only [star_trivial] at this
    exact this hi
  obtain ⟨L, ε, hε, hlow⟩ := quad_lower_core hK isOpen_ball hKW Mz hMc S hS hpos
  obtain ⟨A, hA0, hA⟩ := quad_upper_core hK Mz (hMc.mono hKW)
  have hBup : ∀ i, ∃ β : ℝ, 0 ≤ β ∧ ∀ v : Fin g → ℝ,
      v ⬝ᵥ P.realB i *ᵥ v ≤ β * (v ⬝ᵥ v) := by
    intro i
    obtain ⟨β, hβ0, hβ⟩ := quad_upper_core hK (fun _ => P.realB i) continuousOn_const
    exact ⟨β, hβ0, hβ 0 (mem_closedBall_self (by norm_num))⟩
  choose β hβ0 hβ using hBup
  refine ⟨min (1 / 2) (Real.exp (-(2 * Real.pi) * L)), ε, A + ∑ i, β i,
    lt_min (by norm_num) (Real.exp_pos _), lt_of_le_of_lt (min_le_left _ _) (by norm_num), hε, ?_⟩
  intro w hw hz
  have hzK : expCover a w ∈ closedBall (0 : Fin n → ℂ) (1 / 2) :=
    closedBall_subset_closedBall (min_le_left _ _) hz
  have hdec := P.im_tau_eq hT0 hw
  set z := expCover a w with hzdef
  set l : Fin a → ℝ := fun i => -(w (Fin.castLE P.a_le i)).re / (2 * Real.pi) with hl
  have hquad : ∀ v : Fin g → ℝ, v ⬝ᵥ (P.τ w).map Complex.im *ᵥ v =
      v ⬝ᵥ Mz z *ᵥ v + ∑ i, l i * (v ⬝ᵥ P.realB i *ᵥ v) := by
    intro v; rw [hdec]; exact quad_add_sum _ _ _ v
  have hzi : ∀ i : Fin a, z (Fin.castLE P.a_le i) = Complex.exp (w (Fin.castLE P.a_le i)) := by
    intro i; simp [hzdef, expCover, i.isLt]
  have hre : ∀ i : Fin a, (w (Fin.castLE P.a_le i)).re < 0 := hw.1
  have hnorm : ∀ i : Fin a,
      Real.exp (w (Fin.castLE P.a_le i)).re ≤ Real.exp (-(2 * Real.pi) * L) := by
    intro i
    have h1 : ‖z (Fin.castLE P.a_le i)‖ ≤ ‖z‖ := norm_le_pi_norm z _
    have h2 : ‖z‖ ≤ min (1 / 2) (Real.exp (-(2 * Real.pi) * L)) := by
      simpa [mem_closedBall, dist_zero_right] using hz
    rw [hzi, Complex.norm_exp] at h1
    exact h1.trans (h2.trans (min_le_right _ _))
  have hlL : ∀ i, L ≤ l i := by
    intro i
    have := Real.exp_le_exp.mp (hnorm i)
    show L ≤ -(w (Fin.castLE P.a_le i)).re / (2 * Real.pi)
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hterm : ∀ j : Fin a,
      Real.log (‖cuspCoord P.a_le z j‖ ^ 2)⁻¹ = -2 * (w (Fin.castLE P.a_le j)).re := by
    intro j
    rw [cuspCoord, hzi, Complex.norm_exp, Real.log_inv, Real.log_pow, Real.log_exp]
    push_cast; ring
  have hsum0 : 0 ≤ ∑ j, Real.log (‖cuspCoord P.a_le z j‖ ^ 2)⁻¹ :=
    Finset.sum_nonneg fun j _ => by rw [hterm j]; linarith [hre j]
  have hr1 : 1 ≤ chartRadius P.a_le z := by
    rw [chartRadius]
    have he : 1 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
    linarith
  have hlr : ∀ i, l i ≤ chartRadius P.a_le z := by
    intro i
    rw [chartRadius]
    have hsum : -2 * (w (Fin.castLE P.a_le i)).re ≤
        ∑ j, Real.log (‖cuspCoord P.a_le z j‖ ^ 2)⁻¹ := by
      rw [← hterm i]
      exact Finset.single_le_sum (f := fun j => Real.log (‖cuspCoord P.a_le z j‖ ^ 2)⁻¹)
        (fun j _ => by rw [hterm j]; linarith [hre j]) (Finset.mem_univ i)
    have hli : l i ≤ -2 * (w (Fin.castLE P.a_le i)).re := by
      show -(w (Fin.castLE P.a_le i)).re / (2 * Real.pi) ≤ _
      rw [div_le_iff₀ (by positivity)]
      have := hre i
      nlinarith [Real.pi_gt_three]
    have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    linarith
  have hsymm : ((P.τ w).map Complex.im)ᵀ = (P.τ w).map Complex.im := by
    rw [← Matrix.transpose_map, P.symm w hw]
  refine ⟨?_, ?_⟩
  · rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun v => ?_⟩
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_smul,
        transpose_one, hsymm]
    · simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
      rw [hquad]
      have h1 := hlow z hzK v
      rw [hSv, Finset.mul_sum] at h1
      have h2 : ∑ i, L * (v ⬝ᵥ P.realB i *ᵥ v) ≤ ∑ i, l i * (v ⬝ᵥ P.realB i *ᵥ v) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hlL i) (hBnn i v)
      linarith
  · rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun v => ?_⟩
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_smul,
        transpose_one, hsymm]
    · simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
      rw [hquad]
      have hvv := dot_self_nonneg v
      have h1 := hA z hzK v
      have h2 : ∑ i, l i * (v ⬝ᵥ P.realB i *ᵥ v) ≤
          ∑ i, chartRadius P.a_le z * (β i * (v ⬝ᵥ v)) :=
        Finset.sum_le_sum fun i _ => mul_le_mul (hlr i) (hβ i v) (hBnn i v) (by linarith)
      have h3 : ∑ i, chartRadius P.a_le z * (β i * (v ⬝ᵥ v)) =
          chartRadius P.a_le z * (∑ i, β i) * (v ⬝ᵥ v) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      have h4 : A * (v ⬝ᵥ v) ≤ A * chartRadius P.a_le z * (v ⬝ᵥ v) := by
        have := mul_le_mul_of_nonneg_left hr1 (mul_nonneg hA0 hvv)
        nlinarith
      nlinarith

end

end GroundTheory.Heights₂.Heights.Regular
