import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

/- English proof (translation)
The claim follows from `(Complex.le_def.1 ((hh w).posSemidef.dotProduct_mulVec_nonneg x)).1`.
-/
private theorem re_nonneg {h : HS L N} (hh : h ∈ Pos L N) (w : InfinitePlace L) (x : Fin N → ℂ) :
    0 ≤ (star x ⬝ᵥ (mat h w *ᵥ x)).re :=
  (Complex.le_def.1 ((hh w).posSemidef.dotProduct_mulVec_nonneg x)).1

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun w _ => re_nonneg hh w _`.
-/
private theorem qR_nonneg {h : HS L N} (hh : h ∈ Pos L N) (z : VR L N) : 0 ≤ qR h z :=
  Finset.sum_nonneg fun w _ => re_nonneg hh w _

/- English proof (translation)
Simplify using `only [qR, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.sub_apply, Pi.add_apply, star_sub, star_add, mulVec_sub, mulVec_add, sub_dotProduct, add_dotProduct, dotProduct_sub, dotProduct_add, Complex.sub_re, Complex.add_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem qR_para (h : HS L N) (a b : VR L N) : qR h (a - b) + qR h (a + b) = 2 * qR h a + 2 * qR h b := by
  simp only [qR, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Pi.sub_apply, Pi.add_apply, star_sub, star_add, mulVec_sub, mulVec_add, sub_dotProduct, add_dotProduct,
    dotProduct_sub, dotProduct_add, Complex.sub_re, Complex.add_re]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `w a`. Simplify using `[toR]`.
-/
private theorem toR_add (u v : Lat L N) : toR (u + v) = toR u + toR v := by
  funext w a; simp [toR]

private def bb (h : HS L N) (u v : Lat L N) : ℝ := ∑ w, (star (toR u w) ⬝ᵥ (mat h w *ᵥ toR v w)).re

/- English proof (translation)
Simplify using `only [bb, q, qR, toR_add, Pi.add_apply, mulVec_add, dotProduct_add, Complex.add_re, Finset.sum_add_distrib]`.
-/
private theorem bb_add (h : HS L N) (u v : Lat L N) : bb h u (v + u) = bb h u v + q h u := by
  simp only [bb, q, qR, toR_add, Pi.add_apply, mulVec_add, dotProduct_add, Complex.add_re, Finset.sum_add_distrib]

/- English proof (translation)
Establish `e : ∀ w, (star (toR u w) ⬝ᵥ (mat (rk h v) w *ᵥ toR u w)).re = Complex.normSq (star (toR u w) ⬝ᵥ (mat h w *ᵥ toR v w))`. Introduce `w`. Establish `e1 : mat (rk h v) w = vecMulVec (mat h w *ᵥ toR v w) (star (mat h w *ᵥ toR v w))` using `rfl`. Rewrite using `[e1, dotProduct_mulVec, vecMul_vecMulVec, smul_dotProduct, smul_eq_mul, star_dotProduct (mat h w *ᵥ toR v w), Complex.star_def, Complex.mul_conj, Complex.ofReal_re]`. Establish `e2 : qR (rk h v) (toR u) = ∑ w, Complex.normSq (star (toR u w) ⬝ᵥ (mat h w *ᵥ toR v w))` using `Finset.sum_congr rfl fun w _ => e w`.

Rewrite using `[e2]`. Use `⟨Finset.sum_nonneg fun w _ => Complex.normSq_nonneg _, sq_sum_le_card_mul_sum_sq.trans ?_⟩` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ => ?_) (Nat.cast_nonneg _)` and prove the remaining obligations. Rewrite using `[sq]`. Conclude with `Complex.re_sq_le_normSq _`.
-/
private theorem bb_sq (h : HS L N) (u v : Lat L N) :
    0 ≤ qR (rk h v) (toR u) ∧ bb h u v ^ 2 ≤ Fintype.card (InfinitePlace L) * qR (rk h v) (toR u) := by
  have e : ∀ w, (star (toR u w) ⬝ᵥ (mat (rk h v) w *ᵥ toR u w)).re =
      Complex.normSq (star (toR u w) ⬝ᵥ (mat h w *ᵥ toR v w)) := by
    intro w
    have e1 : mat (rk h v) w = vecMulVec (mat h w *ᵥ toR v w) (star (mat h w *ᵥ toR v w)) := rfl
    rw [e1, dotProduct_mulVec, vecMul_vecMulVec, smul_dotProduct, smul_eq_mul,
      star_dotProduct (mat h w *ᵥ toR v w), Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  have e2 : qR (rk h v) (toR u) = ∑ w, Complex.normSq (star (toR u w) ⬝ᵥ (mat h w *ᵥ toR v w)) :=
    Finset.sum_congr rfl fun w _ => e w
  rw [e2]
  refine ⟨Finset.sum_nonneg fun w _ => Complex.normSq_nonneg _, sq_sum_le_card_mul_sum_sq.trans ?_⟩
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ => ?_) (Nat.cast_nonneg _)
  rw [sq]; exact Complex.re_sq_le_normSq _

/- English proof (translation)
Assemble the required witnesses or components as `⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩`.
-/
private theorem rho_mem (x : ℝ) : 0 ≤ rho x ∧ rho x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/- English proof (translation)
The claim follows from `Real.smoothTransition.one_of_one_le (by linarith)`.
-/
private theorem rho_one {x : ℝ} (hx : x ≤ 1) : rho x = 1 := Real.smoothTransition.one_of_one_le (by linarith)

/- English proof (translation)
The claim follows from `Real.smoothTransition.zero_of_nonpos (by linarith)`.
-/
private theorem rho_zero {x : ℝ} (hx : 4 ≤ x) : rho x = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)

/- English proof (translation)
Use polynomial arithmetic with `[sq_nonneg (2 * B + a)]`.
-/
private theorem num1 {r B a F G : ℝ} (h1 : B ^ 2 ≤ r * F) (h2 : (B + a) ^ 2 ≤ r * G) : a ^ 2 / 2 ≤ r * (F + G) := by
  nlinarith [sq_nonneg (2 * B + a)]

/- English proof (translation)
Rewrite using `[← div_eq_inv_mul, div_le_div_iff₀ (by positivity) (by positivity)]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem num2 {r a s C n Z W : ℝ} (hr : 0 < r) (ha : 0 < a) (hs : 0 < s) (hC : 0 < C) (hZ : 1 ≤ Z) (hW : 0 ≤ W)
    (h1 : s ≤ 16 * a) (h2 : Z ≤ C * n) (h3 : n * (a ^ 2 / 2) ≤ r * (W + W)) : 1 / (1024 * r * C) ≤ (s ^ 2 * Z)⁻¹ * W := by
  rw [← div_eq_inv_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  calc 1 * (s ^ 2 * Z) ≤ 1 * ((16 * a) ^ 2 * (C * n)) := by gcongr
    _ = 512 * C * (n * (a ^ 2 / 2)) := by ring
    _ ≤ 512 * C * (r * (W + W)) := by gcongr
    _ = _ := by ring

/- English proof (translation)
Establish `hz : ∀ v, v ∉ (hfin (16 * (s / 4))).toFinset → rho (q h v / s) = 0` using `fun v hv => by`. Rewrite `hv` using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le]`. Conclude with `rho_zero (by rw [le_div_iff₀ hs]; linarith)`. Establish `hone : ∀ v, q h v ≤ s → v ∈ (hfin (16 * (s / 4))).toFinset ∧ rho (q h v / s) = 1` using `fun v hv => ⟨by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]; linarith, rho_one ((div_le_one hs).2 hv)⟩`. Rewrite `hcnt` using `[Set.ncard_eq_toFinset_card _ (hfin _), Set.ncard_eq_toFinset_card _ (hfin _)]`.

Establish `hS : ∀ v ∈ (hfin (s / 4)).toFinset, q h v ≤ s / 4` using `fun v hv => by`. Rewrite `hv` using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq]`. Then use the resulting hypothesis. Generalize the expression as in `(hfin (16 * (s / 4))).toFinset = T at hz hone hcnt`. Generalize the expression as in `(hfin (s / 4)).toFinset = S at hS hcnt`. Establish `eZ : zed s h = ∑ v ∈ T, rho (q h v / s)` using `finsum_eq_sum_of_support_subset _ fun v hv => by_contra fun hn => hv (hz v hn)`.

Establish `eW : (∑ᶠ v : Lat L N, rho (q h v / s) • rk h v) = ∑ v ∈ T, rho (q h v / s) • rk h v` using `finsum_eq_sum_of_support_subset _ fun v hv => by_contra fun hn => hv (by simp only [hz v hn, zero_smul])`. Establish `eT : qR (term s h) (toR u) = (s ^ 2 * zed s h)⁻¹ * ∑ v ∈ T, rho (q h v / s) * qR (rk h v) (toR u)`. Rewrite using `[← evR_apply, term, eW, map_smul, map_sum]`. Simplify using `only [map_smul, smul_eq_mul, evR_apply]`. Establish `hq0 : q h 0 ≤ s`.

Establish `: toR (0 : Lat L N) = 0` using `by funext w a; simp [toR]`. Simplify using `[q, qR, this, hs.le]`. Establish `hZ1 : 1 ≤ zed s h`. Rewrite using `[eZ, ← (hone 0 hq0).2]`. Conclude with `Finset.single_le_sum (f := fun v => rho (q h v / s)) (fun v _ => (rho_mem _).1) (hone 0 hq0).1`.

Establish `hZ2 : zed s h ≤ C * S.card`. Use `le_trans ?_ hcnt` and prove the remaining obligations. Rewrite using `[eZ]`. Conclude with `(Finset.sum_le_card_nsmul _ _ 1 fun v _ => (rho_mem _).2).trans (by simp)`. Establish `hnn : ∀ v, 0 ≤ rho (q h v / s) * qR (rk h v) (toR u)` using `fun v => mul_nonneg (rho_mem _).1 (bb_sq h u v).1`.

Establish `hsub : ∀ S' : Finset (Lat L N), (∀ v ∈ S', q h v ≤ s) → ∑ v ∈ S', qR (rk h v) (toR u) ≤ ∑ v ∈ T, rho (q h v / s) * qR (rk h v) (toR u)`. Introduce `S' hS'`. Use `le_trans (le_of_eq (Finset.sum_congr rfl fun v hv => ?_)) (Finset.sum_le_sum_of_subset_of_nonneg (fun v hv => (hone v (hS' v hv)).1) fun v _ _ => hnn v)` and prove the remaining obligations. Rewrite using `[(hone v (hS' v hv)).2, one_mul]`. Establish `a1` using `hsub S fun v hv => (hS v hv).trans (by linarith)`.

Establish `a2` using `hsub (S.image (· + u)) fun v' hv' => by`. Take `⟨v, hv, rfl⟩` from `Finset.mem_image.1 hv'`. Establish `k1` using `qR_para h (toR v) (toR u)`. Establish `k2` using `qR_nonneg hh (toR v - toR u)`. Establish `k3` using `hS v hv`.

Rewrite `k1` using `[← toR_add]`. Unfold `q at k3 h2 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `a2` using `[Finset.sum_image fun a _ b _ e => add_right_cancel e]`. Establish `hr : (0 : ℝ) < Fintype.card (InfinitePlace L)` using `Nat.cast_pos.2 Fintype.card_pos`.

Rewrite using `[eT]`. Use `num2 hr ha hs hC hZ1 (Finset.sum_nonneg fun v _ => hnn v) h1 hZ2 ?_` and prove the remaining obligations. Use `le_trans ?_ (mul_le_mul_of_nonneg_left (add_le_add a1 a2) hr.le)` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib, Finset.mul_sum, ← nsmul_eq_mul]`. Use `Finset.card_nsmul_le_sum _ _ _ fun v _ => num1 (bb_sq h u v).2 ?_` and prove the remaining obligations.

Rewrite using `[← bb_add]`. Conclude with `(bb_sq h u _).2`.
-/
private theorem term_low {C : ℝ} (hC : 0 < C) {h : HS L N} (hh : h ∈ Pos L N)
    (hfin : ∀ B : ℝ, {v : Lat L N | q h v ≤ B}.Finite) {s : ℝ} (hs : 0 < s)
    (hcnt : (({v : Lat L N | q h v ≤ 16 * (s / 4)}.ncard : ℕ) : ℝ) ≤ C * ({v : Lat L N | q h v ≤ s / 4}.ncard : ℕ))
    (u : Lat L N) (ha : 0 < q h u) (h1 : s ≤ 16 * q h u) (h2 : 4 * q h u ≤ s) :
    1 / (1024 * (Fintype.card (InfinitePlace L) : ℝ) * C) ≤ qR (term s h) (toR u) := by
  classical
  have hz : ∀ v, v ∉ (hfin (16 * (s / 4))).toFinset → rho (q h v / s) = 0 := fun v hv => by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] at hv
    exact rho_zero (by rw [le_div_iff₀ hs]; linarith)
  have hone : ∀ v, q h v ≤ s → v ∈ (hfin (16 * (s / 4))).toFinset ∧ rho (q h v / s) = 1 := fun v hv =>
    ⟨by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]; linarith, rho_one ((div_le_one hs).2 hv)⟩
  rw [Set.ncard_eq_toFinset_card _ (hfin _), Set.ncard_eq_toFinset_card _ (hfin _)] at hcnt
  have hS : ∀ v ∈ (hfin (s / 4)).toFinset, q h v ≤ s / 4 := fun v hv => by
    rwa [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv
  generalize (hfin (16 * (s / 4))).toFinset = T at hz hone hcnt
  generalize (hfin (s / 4)).toFinset = S at hS hcnt
  have eZ : zed s h = ∑ v ∈ T, rho (q h v / s) :=
    finsum_eq_sum_of_support_subset _ fun v hv => by_contra fun hn => hv (hz v hn)
  have eW : (∑ᶠ v : Lat L N, rho (q h v / s) • rk h v) = ∑ v ∈ T, rho (q h v / s) • rk h v :=
    finsum_eq_sum_of_support_subset _ fun v hv => by_contra fun hn => hv (by simp only [hz v hn, zero_smul])
  have eT : qR (term s h) (toR u) = (s ^ 2 * zed s h)⁻¹ * ∑ v ∈ T, rho (q h v / s) * qR (rk h v) (toR u) := by
    rw [← evR_apply, term, eW, map_smul, map_sum]
    simp only [map_smul, smul_eq_mul, evR_apply]
  have hq0 : q h 0 ≤ s := by
    have : toR (0 : Lat L N) = 0 := by funext w a; simp [toR]
    simp [q, qR, this, hs.le]
  have hZ1 : 1 ≤ zed s h := by
    rw [eZ, ← (hone 0 hq0).2]
    exact Finset.single_le_sum (f := fun v => rho (q h v / s)) (fun v _ => (rho_mem _).1) (hone 0 hq0).1
  have hZ2 : zed s h ≤ C * S.card := by
    refine le_trans ?_ hcnt
    rw [eZ]
    exact (Finset.sum_le_card_nsmul _ _ 1 fun v _ => (rho_mem _).2).trans (by simp)
  have hnn : ∀ v, 0 ≤ rho (q h v / s) * qR (rk h v) (toR u) := fun v => mul_nonneg (rho_mem _).1 (bb_sq h u v).1
  have hsub : ∀ S' : Finset (Lat L N), (∀ v ∈ S', q h v ≤ s) →
      ∑ v ∈ S', qR (rk h v) (toR u) ≤ ∑ v ∈ T, rho (q h v / s) * qR (rk h v) (toR u) := by
    intro S' hS'
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun v hv => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (fun v hv => (hone v (hS' v hv)).1) fun v _ _ => hnn v)
    rw [(hone v (hS' v hv)).2, one_mul]
  have a1 := hsub S fun v hv => (hS v hv).trans (by linarith)
  have a2 := hsub (S.image (· + u)) fun v' hv' => by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hv'
    have k1 := qR_para h (toR v) (toR u)
    have k2 := qR_nonneg hh (toR v - toR u)
    have k3 := hS v hv
    rw [← toR_add] at k1
    unfold q at k3 h2 ⊢
    linarith
  rw [Finset.sum_image fun a _ b _ e => add_right_cancel e] at a2
  have hr : (0 : ℝ) < Fintype.card (InfinitePlace L) := Nat.cast_pos.2 Fintype.card_pos
  rw [eT]
  refine num2 hr ha hs hC hZ1 (Finset.sum_nonneg fun v _ => hnn v) h1 hZ2 ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (add_le_add a1 a2) hr.le)
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← nsmul_eq_mul]
  refine Finset.card_nsmul_le_sum _ _ _ fun v _ => num1 (bb_sq h u v).2 ?_
  rw [← bb_add]; exact (bb_sq h u _).2

/- English proof (translation)
Introduce `hB hCt hE hTL L _ _ N hN μ hμ`. Take `⟨C, hC, hcnt⟩` from `hCt L N 16`. Take `⟨_, hT⟩` from `hTL L N hN`. Take `⟨c, C2, hc, hcmp⟩` from `hμ.cmp`. Establish `hr : (0 : ℝ) < Fintype.card (InfinitePlace L)` using `Nat.cast_pos.2 Fintype.card_pos`.

Use `⟨min (1 / 16) (1 / (1024 * (Fintype.card (InfinitePlace L) : ℝ) * C)), lt_min (by norm_num) (one_div_pos.2 (mul_pos (mul_pos (by norm_num) hr) hC)), fun h hh => ?_⟩` and prove the remaining obligations. Take `⟨-, hRP, hge⟩` from `hE L N hN μ hμ h hh`. Take `⟨u, hu, e⟩` from `((hB L N hN).1 _ hRP).2.2.1`. Take `⟨hl, hlq, -, hdP, hfin⟩` from `(hB L N hN).1 h hh`. Establish `hμ0 : 0 < μ h` using `(mul_pos hc ((hB L N hN).1 _ hdP).1).trans_le (hcmp h hh).1`.

Establish `ha : 0 < q h u` using `hl.trans_le (hlq u hu)`. Rewrite using `[← e]`. Distinguish the cases in `hcase : 1 / 16 ≤ μ h * q h u`. Conclude with `(min_le_left _ _).trans (hcase.trans (hge (toR u)))`. Use `(min_le_right _ _).trans ?_` and prove the remaining obligations.

Take `⟨k, hk0, hk1⟩` from `exists_mem_Ico_zpow (mul_pos (show (0 : ℝ) < 16 by norm_num) ha) (show (1 : ℝ) < 4 by norm_num)`. Establish `hp : ∀ j : ℤ, (0 : ℝ) < 4 ^ j` using `fun j => zpow_pos (by norm_num) _`. Rewrite `hk1` using `[zpow_add_one₀ (by norm_num)]`. Use `(term_low hC hh hfin (hp k) (hcnt h hh _ (div_pos (hp k) (by norm_num)).le) u ha hk0 (by linarith)).trans ?_` and prove the remaining obligations. Take `⟨k1, -, hk1'⟩` from `exists_mem_Ico_zpow (div_pos (show (0 : ℝ) < 4 by norm_num) hμ0) (show (1 : ℝ) < 4 by norm_num)`.

Take `⟨k2, hk2, -⟩` from `exists_mem_Ico_zpow hl (show (1 : ℝ) < 4 by norm_num)`. Establish `hsupp : (Function.support fun j : ℤ => rho ((4 : ℝ) ^ j * μ h) • term ((4 : ℝ) ^ j) h) ⊆ (insert k (Finset.Icc k2 k1) : Finset ℤ)`. Introduce `j hj`. Assume the negation of the conclusion as `hn`. Establish `hn' : j < k2 ∨ k1 < j`.

Simplify using `only [Finset.coe_insert, Finset.coe_Icc, Set.mem_insert_iff, Set.mem_Icc] at hn`. Use linear arithmetic over natural numbers and integers. Use `hj ?_` and prove the remaining obligations. Break down `hn' with h1 | h1` into its components or cases. Establish `: 4 * (4 : ℝ) ^ j ≤ lam h`.

Use `le_trans ?_ hk2` and prove the remaining obligations. Rewrite using `[mul_comm, ← zpow_add_one₀ (by norm_num)]`. Conclude with `zpow_le_zpow_right₀ (by norm_num) (by omega)`. Simplify using `only [(hT _ (hp j) h hh 0).2.1 this, smul_zero]`. Establish `: 4 ≤ (4 : ℝ) ^ j * μ h`.

Rewrite using `[← div_le_iff₀ hμ0]`. Conclude with `hk1'.le.trans (zpow_le_zpow_right₀ (by norm_num) (by omega))`. Simplify using `only [rho_zero this, zero_smul]`. Establish `h1 : rho ((4 : ℝ) ^ k * μ h) = 1`. Use `rho_one ((mul_le_mul_of_nonneg_right hk0 hμ0.le).trans ?_)` and prove the remaining obligations.

Use `not_le.1 hcase` as an intermediate fact. Combine the linear relations using `[mul_comm (μ h) (q h u), mul_assoc 16 (q h u) (μ h)]`. Express the relevant statement in the definitionally equal form `_ ≤ evR (toR u) (ret μ h)`. Rewrite using `[ret, finsum_eq_sum_of_support_subset _ hsupp, map_add, map_sum]`. Simplify using `only [map_smul, smul_eq_mul, evR_apply]`.

Use `le_add_of_nonneg_of_le (mul_nonneg hμ0.le (qR_nonneg hh _)) ?_` and prove the remaining obligations. Use `le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun j : ℤ => rho ((4 : ℝ) ^ j * μ h) * qR (term ((4 : ℝ) ^ j) h) (toR u)) (fun j _ => mul_nonneg (rho_mem _).1 (hT _ (hp j) h hh _).1.1) (Finset.mem_insert_self k _))` and prove the remaining obligations. Simplify using `only [h1, one_mul]`.
-/
theorem pf_GRLow : GRLow := by
  intro hB hCt hE hTL L _ _ N hN μ hμ
  obtain ⟨C, hC, hcnt⟩ := hCt L N 16
  obtain ⟨_, hT⟩ := hTL L N hN
  obtain ⟨c, C2, hc, hcmp⟩ := hμ.cmp
  have hr : (0 : ℝ) < Fintype.card (InfinitePlace L) := Nat.cast_pos.2 Fintype.card_pos
  refine ⟨min (1 / 16) (1 / (1024 * (Fintype.card (InfinitePlace L) : ℝ) * C)),
    lt_min (by norm_num) (one_div_pos.2 (mul_pos (mul_pos (by norm_num) hr) hC)), fun h hh => ?_⟩
  obtain ⟨-, hRP, hge⟩ := hE L N hN μ hμ h hh
  obtain ⟨u, hu, e⟩ := ((hB L N hN).1 _ hRP).2.2.1
  obtain ⟨hl, hlq, -, hdP, hfin⟩ := (hB L N hN).1 h hh
  have hμ0 : 0 < μ h := (mul_pos hc ((hB L N hN).1 _ hdP).1).trans_le (hcmp h hh).1
  have ha : 0 < q h u := hl.trans_le (hlq u hu)
  rw [← e]
  by_cases hcase : 1 / 16 ≤ μ h * q h u
  · exact (min_le_left _ _).trans (hcase.trans (hge (toR u)))
  refine (min_le_right _ _).trans ?_
  obtain ⟨k, hk0, hk1⟩ := exists_mem_Ico_zpow (mul_pos (show (0 : ℝ) < 16 by norm_num) ha) (show (1 : ℝ) < 4 by norm_num)
  have hp : ∀ j : ℤ, (0 : ℝ) < 4 ^ j := fun j => zpow_pos (by norm_num) _
  rw [zpow_add_one₀ (by norm_num)] at hk1
  refine (term_low hC hh hfin (hp k) (hcnt h hh _ (div_pos (hp k) (by norm_num)).le) u ha hk0 (by linarith)).trans ?_
  obtain ⟨k1, -, hk1'⟩ := exists_mem_Ico_zpow (div_pos (show (0 : ℝ) < 4 by norm_num) hμ0) (show (1 : ℝ) < 4 by norm_num)
  obtain ⟨k2, hk2, -⟩ := exists_mem_Ico_zpow hl (show (1 : ℝ) < 4 by norm_num)
  have hsupp : (Function.support fun j : ℤ => rho ((4 : ℝ) ^ j * μ h) • term ((4 : ℝ) ^ j) h) ⊆
      (insert k (Finset.Icc k2 k1) : Finset ℤ) := by
    intro j hj
    by_contra hn
    have hn' : j < k2 ∨ k1 < j := by
      simp only [Finset.coe_insert, Finset.coe_Icc, Set.mem_insert_iff, Set.mem_Icc] at hn
      omega
    refine hj ?_
    rcases hn' with h1 | h1
    · have : 4 * (4 : ℝ) ^ j ≤ lam h := by
        refine le_trans ?_ hk2
        rw [mul_comm, ← zpow_add_one₀ (by norm_num)]
        exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      simp only [(hT _ (hp j) h hh 0).2.1 this, smul_zero]
    · have : 4 ≤ (4 : ℝ) ^ j * μ h := by
        rw [← div_le_iff₀ hμ0]
        exact hk1'.le.trans (zpow_le_zpow_right₀ (by norm_num) (by omega))
      simp only [rho_zero this, zero_smul]
  have h1 : rho ((4 : ℝ) ^ k * μ h) = 1 := by
    refine rho_one ((mul_le_mul_of_nonneg_right hk0 hμ0.le).trans ?_)
    have := not_le.1 hcase
    linarith [mul_comm (μ h) (q h u), mul_assoc 16 (q h u) (μ h)]
  change _ ≤ evR (toR u) (ret μ h)
  rw [ret, finsum_eq_sum_of_support_subset _ hsupp, map_add, map_sum]
  simp only [map_smul, smul_eq_mul, evR_apply]
  refine le_add_of_nonneg_of_le (mul_nonneg hμ0.le (qR_nonneg hh _)) ?_
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun j : ℤ => rho ((4 : ℝ) ^ j * μ h) * qR (term ((4 : ℝ) ^ j) h) (toR u))
    (fun j _ => mul_nonneg (rho_mem _).1 (hT _ (hp j) h hh _).1.1) (Finset.mem_insert_self k _))
  simp only [h1, one_mul]

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
