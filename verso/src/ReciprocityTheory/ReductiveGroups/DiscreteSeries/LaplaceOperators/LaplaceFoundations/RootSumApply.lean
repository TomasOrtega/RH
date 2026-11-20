import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.EqSmulHighestWeightOfIsWeight

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas

open ReciprocityTheory.ChartRestriction.DS

section Wt

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)

/- English proof (translation)
The claim follows from `(dgk_mem t).1`.
-/
theorem dgk_unit (t : Fin k → ℝ) : dgk t ∈ Matrix.unitaryGroup (Fin k) ℂ := (dgk_mem t).1

/- English proof (translation)
Introduce `θ _`. Express the relevant statement in the definitionally equal form `HW.torepSig T (dg θ) x = _`. Rewrite using `[dg_split, torep_mul T (kE_mem_Kset hε (dgk_unit _)) (dg_mem _), spanW_scalar T hε θ hx, map_smul]`. Establish `h1 : HW.torepSig T (kE k r (dgk (th1 θ))) x = Complex.exp (((∑ q, μ q * th1 θ q : ℝ) : ℂ) * Complex.I) • x` using `hμ (th1 θ) (dgk_mem _)`. Rewrite using `[h1, smul_smul, ← Complex.exp_add]`.

Use `congr 1`. Establish `hs : (∑ a, (if h : a.val < k then μ ⟨a.val, h⟩ else Λ a) * θ a) = (∑ a, Λ a * th2 θ a) + ∑ q, μ q * th1 θ q`. Establish `e : ∑ q, μ q * th1 θ q = ∑ a : Fin (2 * r + k + 1), (if h : a.val < k then μ ⟨a.val, h⟩ * θ a else 0)`. Rewrite using `[sumF' (k := k) (r := r) (fun a : Fin (2 * r + k + 1) => if h : a.val < k then μ ⟨a.val, h⟩ * θ a else 0) (fun p hp => by rw [dif_neg hp])]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Establish `hq : (fI k r q).val < k` using `q.2`. Rewrite using `[dif_pos hq]`. Both sides reduce to the same expression. Rewrite using `[e, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Distinguish the cases in `ha : a.val < k`. Simplify using `[th2, ha]`. Simplify using `[th2, ha]`. Rewrite using `[hs, Complex.ofReal_add, add_mul]`.
-/
theorem wt_full (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {x : T.V}
    (hx : x ∈ spanW (k := k) (r := r) T) {μ : Fin k → ℝ}
    (hμ : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T) μ x) :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (HW.torepSig T)
      (fun a => if h : a.val < k then μ ⟨a.val, h⟩ else Λ a) x := by
  intro θ _
  change HW.torepSig T (dg θ) x = _
  rw [dg_split, torep_mul T (kE_mem_Kset hε (dgk_unit _)) (dg_mem _), spanW_scalar T hε θ hx, map_smul]
  have h1 : HW.torepSig T (kE k r (dgk (th1 θ))) x =
      Complex.exp (((∑ q, μ q * th1 θ q : ℝ) : ℂ) * Complex.I) • x := hμ (th1 θ) (dgk_mem _)
  rw [h1, smul_smul, ← Complex.exp_add]
  congr 1
  have hs : (∑ a, (if h : a.val < k then μ ⟨a.val, h⟩ else Λ a) * θ a) =
      (∑ a, Λ a * th2 θ a) + ∑ q, μ q * th1 θ q := by
    have e : ∑ q, μ q * th1 θ q = ∑ a : Fin (2 * r + k + 1), (if h : a.val < k then μ ⟨a.val, h⟩ * θ a else 0) := by
      rw [sumF' (k := k) (r := r) (fun a : Fin (2 * r + k + 1) => if h : a.val < k then μ ⟨a.val, h⟩ * θ a else 0)
        (fun p hp => by rw [dif_neg hp])]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hq : (fI k r q).val < k := q.2
      rw [dif_pos hq]
      rfl
    rw [e, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a.val < k
    · simp [th2, ha]
    · simp [th2, ha]
  rw [hs, Complex.ofReal_add, add_mul]

/- English proof (translation)
Simplify using `only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]`. Use `congr 1`. Rewrite using `[Finset.sum_comm]`. Simplify using `[Finset.sum_ite_eq]`. Simplify using `[Finset.sum_ite_eq]`.
-/
theorem root_sum_apply {m : ℕ} (c : Fin m → Fin m → ℕ) (x : Fin m) :
    (∑ a, ∑ b, (c a b : ℝ) • (Pi.single a (1 : ℝ) - Pi.single b 1 : Fin m → ℝ)) x =
      ∑ b, (c x b : ℝ) - ∑ a, (c a x : ℝ) := by
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  congr 1
  · rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq]
  · simp [Finset.sum_ite_eq]

/- English proof (translation)
Establish `hfull` using `wt_full T hε hx hμ`. Take `⟨c, hc, he⟩` from `HW.KType.weight_le T hx0 (HW.torep_dτ_of_wt T hfull)`. Establish `he' : ∀ y, (Λ - fun a => if h : a.val < k then μ ⟨a.val, h⟩ else Λ a) y = ∑ b, (c y b : ℝ) - ∑ a, (c a y : ℝ)`. Introduce `y`. Rewrite using `[he]`.

Conclude with `root_sum_apply c y`. Establish `hzero : ∀ a b : Fin (2 * r + k + 1), a.val < k → ¬ b.val < k → c a b = 0`. Set `g : Fin (2 * r + k + 1) → ℝ` to `fun y => if y.val < k then 0 else 1`. Establish `hsum : ∑ y, g y * (∑ b, (c y b : ℝ) - ∑ a, (c a y : ℝ)) = 0`. Use `Finset.sum_eq_zero fun y _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hy : y.val < k`. Simplify using `[g, hy]`. Rewrite using `[← he' y]`. Simplify using `[g, hy]`. Establish `hsum2 : ∑ y, g y * (∑ b, (c y b : ℝ) - ∑ a, (c a y : ℝ)) = ∑ a, ∑ b, (c a b : ℝ) * (g a - g b)`.

Simplify using `only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`.

Rewrite `hsum` using `[hsum2]`. Establish `hnp : ∀ a b : Fin (2 * r + k + 1), (c a b : ℝ) * (g a - g b) ≤ 0`. Introduce `a b`. Distinguish the cases in `h0 : c a b = 0`. Simplify using `[h0]`.

Establish `hab` using `(hc a b h0).1`. Establish `hab' : a.val < b.val` using `hab`. Use `mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) ?_` and prove the remaining obligations. Simplify using `only [g]`. Apply the tactic sequence `split_ifs with h1 h2 h2 <;> norm_num`.

Use linear arithmetic over natural numbers and integers. Establish `hall` using `(Finset.sum_eq_zero_iff_of_nonpos (fun a _ => Finset.sum_nonpos fun b _ => hnp a b)).1 hsum`. Introduce `a b ha hb`. Establish `h1` using `(Finset.sum_eq_zero_iff_of_nonpos (fun b _ => hnp a b)).1 (hall a (Finset.mem_univ _)) b (Finset.mem_univ _)`. Simplify using `only [g, if_pos ha, if_neg hb] at h1`.

Evaluate the numerical expressions using `at h1`. Conclude with `h1` after adjusting the coercions. Use `⟨fun q q' => c (fI k r q) (fI k r q'), fun q q' h => ⟨?_, rfl⟩, ?_⟩` and prove the remaining obligations. Use `(hc _ _ h).1` as an intermediate fact. Conclude with `this`.

Use function extensionality and compare the values at `q`. Establish `hq : (fI k r q).val < k` using `q.2`. Establish `h1` using `he' (fI k r q)`. Simplify using `only [Pi.sub_apply, dif_pos hq] at h1`. Establish `e1 : ∑ b, (c (fI k r q) b : ℝ) = ∑ q', (c (fI k r q) (fI k r q') : ℝ)` using `sumF' _ (fun p hp => by rw [hzero _ _ hq hp]; simp)`.

Establish `e2 : ∑ a, (c a (fI k r q) : ℝ) = ∑ q', (c (fI k r q') (fI k r q) : ℝ)`. Use `sumF' _ (fun p hp => ?_)` and prove the remaining obligations. Distinguish the cases in `h0 : c p (fI k r q) = 0`. Simplify using `[h0]`. Use `(hc _ _ h0).1` as an intermediate fact.

Establish `: p.val < (fI k r q).val` using `this`. Conclude with `absurd (lt_trans this hq) hp`. Rewrite `h1` using `[e1, e2]`. Establish `e3 : (⟨(fI k r q).val, hq⟩ : Fin k) = q` using `Fin.ext rfl`. Rewrite `h1` using `[e3]`.

Rewrite using `[show ((fun q => Λ (fI k r q)) - μ) q = Λ (fI k r q) - μ q from rfl, h1]`. Use `root_sum_apply (fun q q' => c (fI k r q) (fI k r q')) q` as an intermediate fact. Rewrite using `[← this]`. Both sides reduce to the same expression.
-/
theorem wt_cdom (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {x : T.V}
    (hx : x ∈ spanW (k := k) (r := r) T) (hx0 : x ≠ 0) {μ : Fin k → ℝ}
    (hμ : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T) μ x) :
    Formalism.MainNotions.S.CDom (Formalism.MainNotions.S.allPos k) μ (fun q => Λ (fI k r q)) := by
  have hfull := wt_full T hε hx hμ
  obtain ⟨c, hc, he⟩ := HW.KType.weight_le T hx0 (HW.torep_dτ_of_wt T hfull)
  have he' : ∀ y, (Λ - fun a => if h : a.val < k then μ ⟨a.val, h⟩ else Λ a) y =
      ∑ b, (c y b : ℝ) - ∑ a, (c a y : ℝ) := by
    intro y
    rw [he]
    exact root_sum_apply c y

  have hzero : ∀ a b : Fin (2 * r + k + 1), a.val < k → ¬ b.val < k → c a b = 0 := by
    let g : Fin (2 * r + k + 1) → ℝ := fun y => if y.val < k then 0 else 1
    have hsum : ∑ y, g y * (∑ b, (c y b : ℝ) - ∑ a, (c a y : ℝ)) = 0 := by
      refine Finset.sum_eq_zero fun y _ => ?_
      by_cases hy : y.val < k
      · simp [g, hy]
      · rw [← he' y]; simp [g, hy]
    have hsum2 : ∑ y, g y * (∑ b, (c y b : ℝ) - ∑ a, (c a y : ℝ)) =
        ∑ a, ∑ b, (c a b : ℝ) * (g a - g b) := by
      simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [hsum2] at hsum
    have hnp : ∀ a b : Fin (2 * r + k + 1), (c a b : ℝ) * (g a - g b) ≤ 0 := by
      intro a b
      by_cases h0 : c a b = 0
      · simp [h0]
      · have hab := (hc a b h0).1
        have hab' : a.val < b.val := hab
        refine mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) ?_
        simp only [g]
        split_ifs with h1 h2 h2 <;> norm_num
        omega
    have hall := (Finset.sum_eq_zero_iff_of_nonpos (fun a _ => Finset.sum_nonpos fun b _ => hnp a b)).1 hsum
    intro a b ha hb
    have h1 := (Finset.sum_eq_zero_iff_of_nonpos (fun b _ => hnp a b)).1 (hall a (Finset.mem_univ _)) b
      (Finset.mem_univ _)
    simp only [g, if_pos ha, if_neg hb] at h1
    norm_num at h1
    exact_mod_cast h1
  refine ⟨fun q q' => c (fI k r q) (fI k r q'), fun q q' h => ⟨?_, rfl⟩, ?_⟩
  · have := (hc _ _ h).1
    exact this
  · funext q
    have hq : (fI k r q).val < k := q.2
    have h1 := he' (fI k r q)
    simp only [Pi.sub_apply, dif_pos hq] at h1
    have e1 : ∑ b, (c (fI k r q) b : ℝ) = ∑ q', (c (fI k r q) (fI k r q') : ℝ) :=
      sumF' _ (fun p hp => by rw [hzero _ _ hq hp]; simp)
    have e2 : ∑ a, (c a (fI k r q) : ℝ) = ∑ q', (c (fI k r q') (fI k r q) : ℝ) := by
      refine sumF' _ (fun p hp => ?_)
      by_cases h0 : c p (fI k r q) = 0
      · simp [h0]
      · have := (hc _ _ h0).1
        have : p.val < (fI k r q).val := this
        exact absurd (lt_trans this hq) hp
    rw [e1, e2] at h1
    have e3 : (⟨(fI k r q).val, hq⟩ : Fin k) = q := Fin.ext rfl
    rw [e3] at h1
    rw [show ((fun q => Λ (fI k r q)) - μ) q = Λ (fI k r q) - μ q from rfl, h1]
    have := root_sum_apply (fun q q' => c (fI k r q) (fI k r q')) q
    rw [← this]
    rfl

end Wt

section Irr

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ} (T : S7.KType ε Λ)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [dg, Matrix.diagonal_apply]`. Distinguish the cases in `hi : i.val < k`. Distinguish the cases in `hj : j.val < k`. Simplify using `only [kE, dgk, dif_pos hi, dif_pos hj, Matrix.diagonal_apply]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg hij, if_neg (by intro e; apply hij; exact Fin.ext (by simpa using e))]`. Rewrite using `[kE_col _ _ hj, if_neg (by rintro rfl; exact hj hi)]; simp [show i ≠ j by rintro rfl; exact hj hi]`.

Rewrite using `[kE_row _ _ hi]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[hi]`. Simplify using `[hij]`.
-/
theorem kE_dgk (t : Fin k → ℝ) :
    kE k r (dgk t) = dg (fun a : Fin (2 * r + k + 1) => if h : a.val < k then t ⟨a.val, h⟩ else 0) := by
  ext i j
  simp only [dg, Matrix.diagonal_apply]
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simp only [kE, dgk, dif_pos hi, dif_pos hj, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (by intro e; apply hij; exact Fin.ext (by simpa using e))]
    · rw [kE_col _ _ hj, if_neg (by rintro rfl; exact hj hi)]; simp [show i ≠ j by rintro rfl; exact hj hi]
  · rw [kE_row _ _ hi]
    by_cases hij : i = j
    · subst hij; simp [hi]
    · simp [hij]

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [kE]`. Use `split_ifs`. Conclude with `(continuous_apply _).comp (continuous_apply _)`. Conclude with `continuous_const`.

Conclude with `continuous_const`. Conclude with `continuous_const`.
-/
theorem kE_cont : Continuous (kE k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [kE]
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const

/- English proof (translation)
Introduce `t _`. Express the relevant statement in the definitionally equal form `HW.torepSig T (kE k r (dgk t)) T.w = _`. Rewrite using `[kE_dgk]`. Unfold `dg`. Rewrite using `[HW.torep_wt_w T _ (dg_mem _)]`.

Use `congr 3`. Use `congr 1`. Use `(sumF' (M := ℝ) (k := k) (r := r) _ (fun p hp => ?_)).trans (Finset.sum_congr rfl fun q _ => ?_)` and prove the remaining obligations. Simplify using `[hp]`. Establish `hq : (fI k r q).val < k` using `q.2`.

Simplify using `only [dif_pos hq]`. Both sides reduce to the same expression.
-/
theorem w_wtK : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T)
    (fun q => Λ (fI k r q)) T.w := by
  intro t _
  change HW.torepSig T (kE k r (dgk t)) T.w = _
  rw [kE_dgk]
  unfold dg
  rw [HW.torep_wt_w T _ (dg_mem _)]
  congr 3
  congr 1
  refine (sumF' (M := ℝ) (k := k) (r := r) _ (fun p hp => ?_)).trans (Finset.sum_congr rfl fun q _ => ?_)
  · simp [hp]
  · have hq : (fI k r q).val < k := q.2
    simp only [dif_pos hq]
    rfl

/- English proof (translation)
Unfold `rhoK`. Rewrite using `[kE_one, (HW.torep_isURepOn T).1.1]`. Both sides reduce to the same expression.
-/
theorem rhoK_one (v : T.V) : rhoK (k := k) (r := r) T 1 v = v := by
  unfold rhoK
  rw [kE_one, (HW.torep_isURepOn T).1.1]
  rfl

/- English proof (translation)
Unfold `rhoK`. Rewrite using `[kE_mul, torep_mul T (kE_mem_Kset hε ha) (kE_mem_Kset hε hb)]`.
-/
theorem rhoK_mul (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {a b : Matrix (Fin k) (Fin k) ℂ}
    (ha : a ∈ Matrix.unitaryGroup (Fin k) ℂ) (hb : b ∈ Matrix.unitaryGroup (Fin k) ℂ) (v : T.V) :
    rhoK (k := k) (r := r) T (a * b) v = rhoK (k := k) (r := r) T a (rhoK (k := k) (r := r) T b v) := by
  unfold rhoK
  rw [kE_mul, torep_mul T (kE_mem_Kset hε ha) (kE_mem_Kset hε hb)]

/- English proof (translation)
The claim follows from `(HW.torep_isURepOn T).2.1 _ (kE_mem_Kset hε ha) v`.
-/
theorem rhoK_norm (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {a : Matrix (Fin k) (Fin k) ℂ}
    (ha : a ∈ Matrix.unitaryGroup (Fin k) ℂ) (v : T.V) : ‖rhoK (k := k) (r := r) T a v‖ = ‖v‖ :=
  (HW.torep_isURepOn T).2.1 _ (kE_mem_Kset hε ha) v

/- English proof (translation)
Establish `hs : star h ∈ Matrix.unitaryGroup (Fin k) ℂ` using `Unitary.star_mem hh`. Establish `hinv : rhoK (k` using `k) (r := r) T (star h) (rhoK (k := k) (r := r) T h v) = v := by`. Rewrite using `[← rhoK_mul T hε hs hh, Unitary.star_mul_self_of_mem hh, rhoK_one]`. Set `Lm : T.V →ₗᵢ[ℂ] T.V` to `{ toLinearMap := (rhoK (k := k) (r := r) T (star h) : T.V →ₗ[ℂ] T.V), norm_map' := rhoK_norm T hε hs }`. Use `Lm.inner_map_map u (rhoK (k := k) (r := r) T h v)` as an intermediate fact.

Express the relevant statement in the definitionally equal form `⟪rhoK (k := k) (r := r) T (star h) u, rhoK (k := k) (r := r) T (star h) (rhoK (k := k) (r := r) T h v)⟫_ℂ = _ at this`. Rewrite `this` using `[hinv]`. Conclude with `this.symm`.
-/
theorem rhoK_adj (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) {h : Matrix (Fin k) (Fin k) ℂ}
    (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) (u v : T.V) :
    ⟪u, rhoK (k := k) (r := r) T h v⟫_ℂ = ⟪rhoK (k := k) (r := r) T (star h) u, v⟫_ℂ := by
  have hs : star h ∈ Matrix.unitaryGroup (Fin k) ℂ := Unitary.star_mem hh
  have hinv : rhoK (k := k) (r := r) T (star h) (rhoK (k := k) (r := r) T h v) = v := by
    rw [← rhoK_mul T hε hs hh, Unitary.star_mul_self_of_mem hh, rhoK_one]
  let Lm : T.V →ₗᵢ[ℂ] T.V :=
    { toLinearMap := (rhoK (k := k) (r := r) T (star h) : T.V →ₗ[ℂ] T.V), norm_map' := rhoK_norm T hε hs }
  have := Lm.inner_map_map u (rhoK (k := k) (r := r) T h v)
  change ⟪rhoK (k := k) (r := r) T (star h) u, rhoK (k := k) (r := r) T (star h) (rhoK (k := k) (r := r) T h v)⟫_ℂ = _
    at this
  rw [hinv] at this
  exact this.symm

/- English proof (translation)
Establish `hperp : ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v ∈ S'ᗮ, rhoK (k` using `k) (r := r) T h v ∈ S'ᗮ := by`. Introduce `h hh v hv`. Rewrite `hv`, the goal using `[Submodule.mem_orthogonal]`. Introduce `u hu`. Rewrite using `[rhoK_adj T hε hh]`.

Conclude with `hv _ (hS' _ (Unitary.star_mem hh) u hu)`. Establish `hbot : ∀ x, x ∈ S' → x ∈ S'ᗮ → x = 0`. Introduce `x h1 h2`. Establish `hm : x ∈ S' ⊓ S'ᗮ` using `⟨h1, h2⟩`. Rewrite `hm` using `[Submodule.inf_orthogonal_eq_bot]`.

Conclude with `(Submodule.mem_bot ℂ).1 hm`. Take `⟨p, hp, q, hq, hpq⟩` from `S'.exists_add_mem_mem_orthogonal T.w`. Establish `hpw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k` using `k) (r := r) T) (fun q => Λ (fI k r q)) p := by`. Introduce `t ht`. Establish `hu : dgk t ∈ Matrix.unitaryGroup (Fin k) ℂ` using `ht.1`.

Establish `h1` using `w_wtK T t ht`. Use `set c := Complex.exp (((∑ a, Λ (fI k r a) * t a : ℝ) : ℂ) * Complex.I)`. Express the relevant statement in the definitionally equal form `rhoK (k := k) (r := r) T (dgk t) T.w = c • T.w at h1`. Express the relevant statement in the definitionally equal form `rhoK (k := k) (r := r) T (dgk t) p = c • p`. Rewrite `h1` using `[hpq, map_add, smul_add]`.

Establish `hA : rhoK (k` using `k) (r := r) T (dgk t) p - c • p ∈ S' := S'.sub_mem (hS' _ hu _ hp) (S'.smul_mem _ hp)`. Establish `hB : rhoK (k` using `k) (r := r) T (dgk t) p - c • p ∈ S'ᗮ := by`. Establish `e : rhoK (k` using `k) (r := r) T (dgk t) p - c • p = c • q - rhoK (k := k) (r := r) T (dgk t) q := by`. Rewrite using `[sub_eq_sub_iff_add_eq_add, h1]`. Conclude with `add_comm _ _`.

Rewrite using `[e]`. Conclude with `S'ᗮ.sub_mem (S'ᗮ.smul_mem _ hq) (hperp _ hu _ hq)`. Conclude with `sub_eq_zero.1 (hbot _ hA hB)`. Establish `hqw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k` using `k) (r := r) T) (fun q => Λ (fI k r q)) q := by`. Introduce `t ht`.

Establish `h1` using `w_wtK T t ht`. Establish `h2` using `hpw t ht`. Establish `e : q = T.w - p` using `by rw [hpq]; abel`. Rewrite using `[e, map_sub, h1, h2, smul_sub]`. Establish `hpS : p ∈ spanW (k` using `k) (r := r) T := hle hp`.

Establish `hqS : q ∈ spanW (k` using `k) (r := r) T := by`. Establish `e : q = T.w - p` using `by rw [hpq]; abel`. Rewrite using `[e]`. Conclude with `sub_mem (w_mem_spanW T) hpS`. Establish `hfix : (fun a : Fin (2 * r + k + 1) => if h : a.val < k then (fun q => Λ (fI k r q)) ⟨a.val, h⟩ else Λ a) = Λ`.

Apply the tactic sequence `funext a; split_ifs <;> rfl`. Establish `hp2` using `wt_full T hε hpS hpw`. Establish `hq2` using `wt_full T hε hqS hqw`. Rewrite `hp2`, `hq2` using `[hfix]`. Take `⟨a, ha⟩` from `eq_smul_highestWeight_of_isWeight T hp2`.

Take `⟨b, hb⟩` from `eq_smul_highestWeight_of_isWeight T hq2`. Establish `hinner : ⟪p, q⟫_ℂ = 0` using `Submodule.inner_right_of_mem_orthogonal hp hq`. Rewrite `hinner` using `[ha, hb, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K, T.w_norm]`. Simplify using `only [RCLike.ofReal_one, one_pow, mul_one] at hinner`. Break down `mul_eq_zero.1 hinner with h | h` into its components or cases.

Use `left`. Establish `ha0 : a = 0` using `by simpa using h`. Establish `hq' : T.w = q` using `by rw [hpq, ha, ha0, zero_smul, zero_add]`. Establish `hle' : spanW (k` using `k) (r := r) T ≤ S'ᗮ := spanW_le T (hq' ▸ hq) hperp`. Rewrite using `[Submodule.eq_bot_iff]`.

Introduce `x hx`. Conclude with `hbot x hx (hle' (hle hx))`. Use `right`. Establish `hp' : T.w = p` using `by rw [hpq, hb, h, zero_smul, add_zero]`. Conclude with `spanW_le T (hp' ▸ hp) hS'`.
-/
theorem spanW_irred (hε : ∀ a : Fin (2 * r + k + 1), a.val < k → ε a = true) (S' : Submodule ℂ T.V)
    (hle : S' ≤ spanW (k := k) (r := r) T)
    (hS' : ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v ∈ S', rhoK (k := k) (r := r) T h v ∈ S') :
    S' = ⊥ ∨ spanW (k := k) (r := r) T ≤ S' := by
  have hperp : ∀ h ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ v ∈ S'ᗮ, rhoK (k := k) (r := r) T h v ∈ S'ᗮ := by
    intro h hh v hv
    rw [Submodule.mem_orthogonal] at hv ⊢
    intro u hu
    rw [rhoK_adj T hε hh]
    exact hv _ (hS' _ (Unitary.star_mem hh) u hu)
  have hbot : ∀ x, x ∈ S' → x ∈ S'ᗮ → x = 0 := by
    intro x h1 h2
    have hm : x ∈ S' ⊓ S'ᗮ := ⟨h1, h2⟩
    rw [Submodule.inf_orthogonal_eq_bot] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  obtain ⟨p, hp, q, hq, hpq⟩ := S'.exists_add_mem_mem_orthogonal T.w
  have hpw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T)
      (fun q => Λ (fI k r q)) p := by
    intro t ht
    have hu : dgk t ∈ Matrix.unitaryGroup (Fin k) ℂ := ht.1
    have h1 := w_wtK T t ht
    set c := Complex.exp (((∑ a, Λ (fI k r a) * t a : ℝ) : ℂ) * Complex.I)
    change rhoK (k := k) (r := r) T (dgk t) T.w = c • T.w at h1
    change rhoK (k := k) (r := r) T (dgk t) p = c • p
    rw [hpq, map_add, smul_add] at h1
    have hA : rhoK (k := k) (r := r) T (dgk t) p - c • p ∈ S' := S'.sub_mem (hS' _ hu _ hp) (S'.smul_mem _ hp)
    have hB : rhoK (k := k) (r := r) T (dgk t) p - c • p ∈ S'ᗮ := by
      have e : rhoK (k := k) (r := r) T (dgk t) p - c • p = c • q - rhoK (k := k) (r := r) T (dgk t) q := by
        rw [sub_eq_sub_iff_add_eq_add, h1]
        exact add_comm _ _
      rw [e]
      exact S'ᗮ.sub_mem (S'ᗮ.smul_mem _ hq) (hperp _ hu _ hq)
    exact sub_eq_zero.1 (hbot _ hA hB)
  have hqw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k)) (rhoK (k := k) (r := r) T)
      (fun q => Λ (fI k r q)) q := by
    intro t ht
    have h1 := w_wtK T t ht
    have h2 := hpw t ht
    have e : q = T.w - p := by rw [hpq]; abel
    rw [e, map_sub, h1, h2, smul_sub]
  have hpS : p ∈ spanW (k := k) (r := r) T := hle hp
  have hqS : q ∈ spanW (k := k) (r := r) T := by
    have e : q = T.w - p := by rw [hpq]; abel
    rw [e]; exact sub_mem (w_mem_spanW T) hpS
  have hfix : (fun a : Fin (2 * r + k + 1) => if h : a.val < k then (fun q => Λ (fI k r q)) ⟨a.val, h⟩ else Λ a) = Λ := by
    funext a; split_ifs <;> rfl
  have hp2 := wt_full T hε hpS hpw
  have hq2 := wt_full T hε hqS hqw
  rw [hfix] at hp2 hq2
  obtain ⟨a, ha⟩ := eq_smul_highestWeight_of_isWeight T hp2
  obtain ⟨b, hb⟩ := eq_smul_highestWeight_of_isWeight T hq2
  have hinner : ⟪p, q⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal hp hq
  rw [ha, hb, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K, T.w_norm] at hinner
  simp only [RCLike.ofReal_one, one_pow, mul_one] at hinner
  rcases mul_eq_zero.1 hinner with h | h
  · left
    have ha0 : a = 0 := by simpa using h
    have hq' : T.w = q := by rw [hpq, ha, ha0, zero_smul, zero_add]
    have hle' : spanW (k := k) (r := r) T ≤ S'ᗮ := spanW_le T (hq' ▸ hq) hperp
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact hbot x hx (hle' (hle hx))
  · right
    have hp' : T.w = p := by rw [hpq, hb, h, zero_smul, add_zero]
    exact spanW_le T (hp' ▸ hp) hS'

end Irr

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.SchurOrthogonalityLemmas
