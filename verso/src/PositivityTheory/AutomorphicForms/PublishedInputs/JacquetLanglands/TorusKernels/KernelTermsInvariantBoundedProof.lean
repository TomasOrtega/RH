import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk

namespace KernelTermsInvariantLemmas

/- English proof (translation)
Establish `ha : g 0 0 ≠ 0`. Introduce `h0`. Apply `g.det_ne_zero` to reduce the goal to its premises. Simplify using `[det_eq, hb, hc, h0, ← h]`. Establish `hden : den g z.1 = ((g 0 0 : ℝ) : ℂ)`.

Simplify using `[den, hc, h]`. Establish `hr : |g.val.det| ^ (-(k : ℝ) / 2) = (|g 0 0| ^ k)⁻¹`. Establish `e : |g.val.det| = |g 0 0| ^ ((2 : ℕ) : ℝ)`. Rewrite using `[Real.rpow_natCast, det_eq, hb, hc, ← h]`. Simplify using `[sq, abs_mul]`.

Rewrite using `[e, ← Real.rpow_mul (abs_nonneg _)]`. Establish `e2 : ((2 : ℕ) : ℝ) * (-(k : ℝ) / 2) = -((k : ℕ) : ℝ)` using `by push_cast; ring`. Rewrite using `[e2, Real.rpow_neg (abs_nonneg _), Real.rpow_natCast]`. Establish `key : g 0 0 ^ k * (|g 0 0| ^ k)⁻¹ = (SignType.sign (g 0 0) : ℝ) ^ k`. Establish `hs : g 0 0 ^ k = (SignType.sign (g 0 0) : ℝ) ^ k * |g 0 0| ^ k`.

Rewrite using `[← mul_pow, sign_mul_abs]`. Rewrite using `[hs, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (abs_ne_zero.2 ha)), mul_one]`. Combine the equalities or inequalities in the displayed calculation. Unfold `j1`. Rewrite using `[hr, hden, Complex.ofReal_mul, Complex.ofReal_pow]`.

Use `_ = ((SignType.sign (g 0 0) : ℝ) : ℂ) ^ k := by rw [key, Complex.ofReal_pow]`.
-/
theorem automorphy_factor_scalar_matrix (k : ℕ) (g : GL (Fin 2) ℝ) (hb : g 0 1 = 0) (hc : g 1 0 = 0) (h : g 0 0 = g 1 1) (z : P) :
    j1 k g z = ((SignType.sign (g 0 0) : ℝ) : ℂ) ^ k := by
  have ha : g 0 0 ≠ 0 := by
    intro h0
    apply g.det_ne_zero
    simp [det_eq, hb, hc, h0, ← h]
  have hden : den g z.1 = ((g 0 0 : ℝ) : ℂ) := by
    simp [den, hc, h]
  have hr : |g.val.det| ^ (-(k : ℝ) / 2) = (|g 0 0| ^ k)⁻¹ := by
    have e : |g.val.det| = |g 0 0| ^ ((2 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast, det_eq, hb, hc, ← h]
      simp [sq, abs_mul]
    rw [e, ← Real.rpow_mul (abs_nonneg _)]
    have e2 : ((2 : ℕ) : ℝ) * (-(k : ℝ) / 2) = -((k : ℕ) : ℝ) := by push_cast; ring
    rw [e2, Real.rpow_neg (abs_nonneg _), Real.rpow_natCast]
  have key : g 0 0 ^ k * (|g 0 0| ^ k)⁻¹ = (SignType.sign (g 0 0) : ℝ) ^ k := by
    have hs : g 0 0 ^ k = (SignType.sign (g 0 0) : ℝ) ^ k * |g 0 0| ^ k := by
      rw [← mul_pow, sign_mul_abs]
    rw [hs, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (abs_ne_zero.2 ha)), mul_one]
  calc j1 k g z = ((g 0 0 ^ k * (|g 0 0| ^ k)⁻¹ : ℝ) : ℂ) := by
        unfold j1
        rw [hr, hden, Complex.ofReal_mul, Complex.ofReal_pow]
    _ = ((SignType.sign (g 0 0) : ℝ) : ℂ) ^ k := by rw [key, Complex.ofReal_pow]

/- English proof (translation)
Establish `h1 : j1 k 1 w = 1`. Establish `e` using `hco k 1 1 w`. Rewrite `e` using `[one_mul, one_smul]`. Establish `hne` using `hn k 1 w`. Establish `h0 : j1 k 1 w * (j1 k 1 w - 1) = 0` using `by rw [mul_sub, mul_one, ← e, sub_self]`.

Break down `mul_eq_zero.1 h0 with h0 | h0` into its components or cases. Conclude with `absurd h0 hne`. Conclude with `sub_eq_zero.1 h0`. Establish `hAB : j1 k G⁻¹ (G • w) * j1 k G w = 1`. Rewrite using `[← hco, inv_mul_cancel, h1]`.

Establish `e1 : j1 k (G * g * G⁻¹) (G • w) = j1 k G (g • w) * j1 k g w * j1 k G⁻¹ (G • w)`. Rewrite using `[hco, inv_smul_smul, hco]`. Establish `e2` using `hq k G w (g • w)`. Rewrite using `[e1]`. Take the linear combination `(j1 k g w * j1 k G⁻¹ (G • w)) * e2 + (q1 k w (g • w) * j1 k g w) * hAB`.
-/
theorem block_frame_conjugation_identity (hco : ∀ (k : ℕ) (g h : GL (Fin 2) ℝ) (z : P), j1 k (g * h) z = j1 k g (h • z) * j1 k h z)
    (hn : ∀ (k : ℕ) (g : GL (Fin 2) ℝ) (z : P), j1 k g z ≠ 0)
    (hq : ∀ (k : ℕ) (g : GL (Fin 2) ℝ) (z w : P), q1 k (g • z) (g • w) * j1 k g w = j1 k g z * q1 k z w)
    (k : ℕ) (G g : GL (Fin 2) ℝ) (w : P) :
    q1 k (G • w) (G • g • w) * j1 k (G * g * G⁻¹) (G • w) = q1 k w (g • w) * j1 k g w := by
  have h1 : j1 k 1 w = 1 := by
    have e := hco k 1 1 w
    rw [one_mul, one_smul] at e
    have hne := hn k 1 w
    have h0 : j1 k 1 w * (j1 k 1 w - 1) = 0 := by rw [mul_sub, mul_one, ← e, sub_self]
    rcases mul_eq_zero.1 h0 with h0 | h0
    · exact absurd h0 hne
    · exact sub_eq_zero.1 h0
  have hAB : j1 k G⁻¹ (G • w) * j1 k G w = 1 := by
    rw [← hco, inv_mul_cancel, h1]
  have e1 : j1 k (G * g * G⁻¹) (G • w) = j1 k G (g • w) * j1 k g w * j1 k G⁻¹ (G • w) := by
    rw [hco, inv_smul_smul, hco]
  have e2 := hq k G w (g • w)
  rw [e1]
  linear_combination (j1 k g w * j1 k G⁻¹ (G • w)) * e2 + (q1 k w (g • w) * j1 k g w) * hAB

/- English proof (translation)
Take `⟨-, -, -, -, h5, h6, -, -, -⟩` from `hB`. Establish `hz : z.1.im ≠ 0` using `z.2`. Establish `hgz : (g • z).1.im ≠ 0` using `(g • z).2`. Establish `ha : 0 < |z.1.im| ^ ((k : ℝ) / 2)` using `Real.rpow_pos_of_pos (abs_pos.2 hz) _`. Establish `hb : 0 < |(g • z).1.im| ^ ((k : ℝ) / 2)` using `Real.rpow_pos_of_pos (abs_pos.2 hgz) _`.

Establish `e5` using `h5 k g z`. Establish `e6` using `h6 k z (g • z) hk`. Rewrite using `[norm_mul]`. Apply `mul_right_cancel₀ (mul_pos ha hb).ne'` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_qj (hB : B1b) (k : ℕ) (hk : 1 ≤ k) (g : GL (Fin 2) ℝ) (z : P) :
    ‖q1 k z (g • z) * j1 k g z‖ = ((k : ℝ) - 1) / (4 * Real.pi) * kap z (g • z) ^ ((k : ℝ) / 2) := by
  obtain ⟨-, -, -, -, h5, h6, -, -, -⟩ := hB
  have hz : z.1.im ≠ 0 := z.2
  have hgz : (g • z).1.im ≠ 0 := (g • z).2
  have ha : 0 < |z.1.im| ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos (abs_pos.2 hz) _
  have hb : 0 < |(g • z).1.im| ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos (abs_pos.2 hgz) _
  have e5 := h5 k g z
  have e6 := h6 k z (g • z) hk
  rw [norm_mul]
  apply mul_right_cancel₀ (mul_pos ha hb).ne'
  calc ‖q1 k z (g • z)‖ * ‖j1 k g z‖ * (|z.1.im| ^ ((k : ℝ) / 2) * |(g • z).1.im| ^ ((k : ℝ) / 2))
      = (‖q1 k z (g • z)‖ * |z.1.im| ^ ((k : ℝ) / 2)) * (‖j1 k g z‖ * |(g • z).1.im| ^ ((k : ℝ) / 2)) := by ring
    _ = ((k : ℝ) - 1) / (4 * Real.pi) * kap z (g • z) ^ ((k : ℝ) / 2) *
        (|z.1.im| ^ ((k : ℝ) / 2) * |(g • z).1.im| ^ ((k : ℝ) / 2)) := by rw [e5, e6]; ring

variable {F I Gf ι : Type} [Field F] [Group Gf] [Fintype I] [Fintype ι] (D : Dat F I Gf)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem r_apply (v : I) (γ : GL (Fin 2) F) (i j : Fin 2) : D.r v γ i j = D.σ v (γ i j) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem act_apply (γ : GL (Fin 2) F) (z : X I) (v : I) : D.act γ z v = D.r v γ • z v := rfl

/- English proof (translation)
Unfold `Dat.ee`. Distinguish the cases in `hu : u ∈ D.H`. Establish `hhu : (h : Gf) * u ∈ D.H` using `D.H.mul_mem h.2 hu`. Rewrite using `[dif_pos hhu, dif_pos hu]`. Establish `e : (⟨(h : Gf) * u, hhu⟩ : D.H) = h * ⟨u, hu⟩` using `rfl`.

Rewrite using `[e, map_mul, Units.val_mul]`. Establish `hhu : (h : Gf) * u ∉ D.H` using `fun hm => hu (by simpa using D.H.mul_mem (D.H.inv_mem h.2) hm)`. Rewrite using `[dif_neg hhu, dif_neg hu, mul_zero]`.
-/
theorem ee_mul_left (h : D.H) (u : Gf) : D.ee (h * u) = D.χ h * D.ee u := by
  unfold Dat.ee
  by_cases hu : u ∈ D.H
  · have hhu : (h : Gf) * u ∈ D.H := D.H.mul_mem h.2 hu
    rw [dif_pos hhu, dif_pos hu]
    have e : (⟨(h : Gf) * u, hhu⟩ : D.H) = h * ⟨u, hu⟩ := rfl
    rw [e, map_mul, Units.val_mul]
  · have hhu : (h : Gf) * u ∉ D.H := fun hm => hu (by simpa using D.H.mul_mem (D.H.inv_mem h.2) hm)
    rw [dif_neg hhu, dif_neg hu, mul_zero]

/- English proof (translation)
Unfold `Dat.ee`. Distinguish the cases in `hu : u ∈ D.H`. Establish `hhu : u * (h : Gf) ∈ D.H` using `D.H.mul_mem hu h.2`. Rewrite using `[dif_pos hhu, dif_pos hu]`. Establish `e : (⟨u * (h : Gf), hhu⟩ : D.H) = ⟨u, hu⟩ * h` using `rfl`.

Rewrite using `[e, map_mul, Units.val_mul]`. Establish `hhu : u * (h : Gf) ∉ D.H` using `fun hm => hu (by simpa using D.H.mul_mem hm (D.H.inv_mem h.2))`. Rewrite using `[dif_neg hhu, dif_neg hu, zero_mul]`.
-/
theorem ee_mul_right (u : Gf) (h : D.H) : D.ee (u * h) = D.ee u * D.χ h := by
  unfold Dat.ee
  by_cases hu : u ∈ D.H
  · have hhu : u * (h : Gf) ∈ D.H := D.H.mul_mem hu h.2
    rw [dif_pos hhu, dif_pos hu]
    have e : (⟨u * (h : Gf), hhu⟩ : D.H) = ⟨u, hu⟩ * h := rfl
    rw [e, map_mul, Units.val_mul]
  · have hhu : u * (h : Gf) ∉ D.H := fun hm => hu (by simpa using D.H.mul_mem hm (D.H.inv_mem h.2))
    rw [dif_neg hhu, dif_neg hu, zero_mul]

/- English proof (translation)
Establish `e` using `ee_mul_left D h⁻¹ u`. Rewrite `e` using `[Subgroup.coe_inv, map_inv, Units.val_inv_eq_inv_val]`. Conclude with `e`.
-/
theorem ee_inv_mul (h : D.H) (u : Gf) : D.ee ((h : Gf)⁻¹ * u) = (D.χ h : ℂ)⁻¹ * D.ee u := by
  have e := ee_mul_left D h⁻¹ u
  rw [Subgroup.coe_inv, map_inv, Units.val_inv_eq_inv_val] at e
  exact e

/- English proof (translation)
Unfold `Dat.ee`. Use `split_ifs with hu`. Conclude with `(hx.χn _).le`. Simplify using the standard rewrite rules.
-/
theorem norm_ee_le (hx : D.Ax) (u : Gf) : ‖D.ee u‖ ≤ 1 := by
  unfold Dat.ee
  split_ifs with hu
  · exact (hx.χn _).le
  · simp

/- English proof (translation)
Unfold `Dat.Te`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_Te_le (hx : D.Ax) (a : ι → Gf) (γ : GL (Fin 2) F) (x : Gf) : ‖D.Te a γ x‖ ≤ Fintype.card ι := by
  unfold Dat.Te
  calc ‖∑ i, D.ee (x⁻¹ * (D.j γ)⁻¹ * x * a i)‖ ≤ ∑ i : ι, ‖D.ee (x⁻¹ * (D.j γ)⁻¹ * x * a i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => norm_ee_le D hx _
    _ = (Fintype.card ι : ℝ) := by simp

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `center_entries hc`. Apply `center_smul` to reduce the goal to its premises. Rewrite using `[r_apply, h1, map_zero]`. Rewrite using `[r_apply, h2, map_zero]`. Rewrite using `[r_apply, r_apply, h3]`.
-/
theorem smul_center (v : I) (c : GL (Fin 2) F) (hc : c ∈ Subgroup.center (GL (Fin 2) F)) (w : P) : D.r v c • w = w := by
  obtain ⟨h1, h2, h3⟩ := center_entries hc
  apply center_smul
  · rw [r_apply, h1, map_zero]
  · rw [r_apply, h2, map_zero]
  · rw [r_apply, r_apply, h3]

/- English proof (translation)
Use function extensionality and compare the values at `v`. Rewrite using `[act_apply, act_apply, map_mul, mul_smul, smul_center D v c hc]`.
-/
theorem act_mul_center (γ c : GL (Fin 2) F) (hc : c ∈ Subgroup.center (GL (Fin 2) F)) (z : X I) :
    D.act (γ * c) z = D.act γ z := by
  funext v
  rw [act_apply, act_apply, map_mul, mul_smul, smul_center D v c hc]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `center_entries hc`. Rewrite using `[automorphy_factor_scalar_matrix (k v) (D.r v c) (by rw [r_apply, h1, map_zero]) (by rw [r_apply, h2, map_zero]) (by rw [r_apply, r_apply, h3]) w, r_apply]`.
-/
theorem J_center (k : I → ℕ) (c : GL (Fin 2) F) (hc : c ∈ Subgroup.center (GL (Fin 2) F)) (w : P) (v : I) :
    j1 (k v) (D.r v c) w = ((SignType.sign (D.σ v (c 0 0)) : ℝ) : ℂ) ^ k v := by
  obtain ⟨h1, h2, h3⟩ := center_entries hc
  rw [automorphy_factor_scalar_matrix (k v) (D.r v c) (by rw [r_apply, h1, map_zero]) (by rw [r_apply, h2, map_zero])
    (by rw [r_apply, r_apply, h3]) w, r_apply]

/- English proof (translation)
Unfold `Dat.Te`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hc' : (D.j c)⁻¹ ∈ Subgroup.center Gf` using `Subgroup.inv_mem _ (D.cenC c hc)`. Rewrite `hc'` using `[Subgroup.mem_center_iff]`.

Establish `e : x⁻¹ * (D.j (γ * c))⁻¹ * x * a i = (D.j c)⁻¹ * (x⁻¹ * (D.j γ)⁻¹ * x * a i)`. Rewrite using `[map_mul, _root_.mul_inv_rev]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = ((D.j c)⁻¹ * x⁻¹) * ((D.j γ)⁻¹ * x * a i) := by rw [hc' x⁻¹]`.

Use `_ = (D.j c)⁻¹ * (x⁻¹ * (D.j γ)⁻¹ * x * a i) := by simp only [mul_assoc]`. Rewrite using `[e]`. Conclude with `ee_inv_mul D ⟨D.j c, D.cenH c hc⟩ _`.
-/
theorem Te_mul_center (a : ι → Gf) (γ c : GL (Fin 2) F) (hc : c ∈ Subgroup.center (GL (Fin 2) F)) (x : Gf) :
    D.Te a (γ * c) x = (D.χ ⟨D.j c, D.cenH c hc⟩ : ℂ)⁻¹ * D.Te a γ x := by
  unfold Dat.Te
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc' : (D.j c)⁻¹ ∈ Subgroup.center Gf := Subgroup.inv_mem _ (D.cenC c hc)
  rw [Subgroup.mem_center_iff] at hc'
  have e : x⁻¹ * (D.j (γ * c))⁻¹ * x * a i = (D.j c)⁻¹ * (x⁻¹ * (D.j γ)⁻¹ * x * a i) := by
    rw [map_mul, _root_.mul_inv_rev]
    calc x⁻¹ * ((D.j c)⁻¹ * (D.j γ)⁻¹) * x * a i = (x⁻¹ * (D.j c)⁻¹) * ((D.j γ)⁻¹ * x * a i) := by
          simp only [mul_assoc]
      _ = ((D.j c)⁻¹ * x⁻¹) * ((D.j γ)⁻¹ * x * a i) := by rw [hc' x⁻¹]
      _ = (D.j c)⁻¹ * (x⁻¹ * (D.j γ)⁻¹ * x * a i) := by simp only [mul_assoc]
  rw [e]
  exact ee_inv_mul D ⟨D.j c, D.cenH c hc⟩ _

/- English proof (translation)
Establish `hJ : D.J k (γ * c) z = D.J k γ z * (D.χ ⟨D.j c, D.cenH c hc⟩ : ℂ)`. Rewrite using `[hC c hc]`. Unfold `Dat.J`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, hB.1, smul_center D v c hc, J_center D k c hc (z v) v]`. Establish `hne : (D.χ ⟨D.j c, D.cenH c hc⟩ : ℂ) ≠ 0` using `Units.ne_zero _`. Unfold `Dat.kt`. Rewrite using `[act_mul_center D γ c hc z, Te_mul_center D a γ c hc x, hJ]`. Combine the equalities or inequalities in the displayed calculation.

Expand and normalize the polynomial expressions, which then agree. Use `_ = D.Te a γ x * (qq k z (D.act γ z) * D.J k γ z) := by rw [inv_mul_cancel₀ hne, one_mul]`.
-/
theorem kt_mul_center (hB : B1b) (k : I → ℕ) (a : ι → Gf) (hC : D.Compat k) (γ c : GL (Fin 2) F)
    (hc : c ∈ Subgroup.center (GL (Fin 2) F)) (z : X I) (x : Gf) :
    D.kt k a (γ * c) z x = D.kt k a γ z x := by
  have hJ : D.J k (γ * c) z = D.J k γ z * (D.χ ⟨D.j c, D.cenH c hc⟩ : ℂ) := by
    rw [hC c hc]
    unfold Dat.J
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_mul, hB.1, smul_center D v c hc, J_center D k c hc (z v) v]
  have hne : (D.χ ⟨D.j c, D.cenH c hc⟩ : ℂ) ≠ 0 := Units.ne_zero _
  unfold Dat.kt
  rw [act_mul_center D γ c hc z, Te_mul_center D a γ c hc x, hJ]
  calc (D.χ ⟨D.j c, D.cenH c hc⟩ : ℂ)⁻¹ * D.Te a γ x * (qq k z (D.act γ z) * (D.J k γ z * (D.χ ⟨D.j c, D.cenH c hc⟩ : ℂ)))
      = ((D.χ ⟨D.j c, D.cenH c hc⟩ : ℂ)⁻¹ * (D.χ ⟨D.j c, D.cenH c hc⟩ : ℂ)) * (D.Te a γ x * (qq k z (D.act γ z) * D.J k γ z)) := by
        ring
    _ = D.Te a γ x * (qq k z (D.act γ z) * D.J k γ z) := by rw [inv_mul_cancel₀ hne, one_mul]

/- English proof (translation)
Establish `hf : ∀ (y : Gf) (h' : D.H), D.ee ((x⁻¹ * (D.j γ)⁻¹ * x) * (y * h')) = D.χ h' * D.ee ((x⁻¹ * (D.j γ)⁻¹ * x) * y)`. Introduce `y h'`. Rewrite using `[← mul_assoc]`. Conclude with `(ee_mul_right D _ _).trans (mul_comm _ _)`. Establish `key` using `hG (fun y => D.ee ((x⁻¹ * (D.j γ)⁻¹ * x) * y)) hf 1 h`.

Simplify using `only [one_mul] at key`. Unfold `Dat.Te`. Establish `e1 : ∀ i, (x * h)⁻¹ * (D.j γ)⁻¹ * (x * h) * a i = ((h : Gf))⁻¹ * ((x⁻¹ * (D.j γ)⁻¹ * x) * ((h : Gf) * a i))`. Introduce `i`. Use `group`.

Simplify using `only [e1, ee_inv_mul, ← Finset.mul_sum]`. Rewrite using `[key, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]`.
-/
theorem Te_mul_H (a : ι → Gf) (hG : D.Good a) (γ : GL (Fin 2) F) (x : Gf) (h : D.H) :
    D.Te a γ (x * h) = D.Te a γ x := by
  have hf : ∀ (y : Gf) (h' : D.H), D.ee ((x⁻¹ * (D.j γ)⁻¹ * x) * (y * h')) = D.χ h' * D.ee ((x⁻¹ * (D.j γ)⁻¹ * x) * y) := by
    intro y h'
    rw [← mul_assoc]
    exact (ee_mul_right D _ _).trans (mul_comm _ _)
  have key := hG (fun y => D.ee ((x⁻¹ * (D.j γ)⁻¹ * x) * y)) hf 1 h
  simp only [one_mul] at key
  unfold Dat.Te
  have e1 : ∀ i, (x * h)⁻¹ * (D.j γ)⁻¹ * (x * h) * a i =
      ((h : Gf))⁻¹ * ((x⁻¹ * (D.j γ)⁻¹ * x) * ((h : Gf) * a i)) := by
    intro i; group
  simp only [e1, ee_inv_mul, ← Finset.mul_sum]
  rw [key, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]

/- English proof (translation)
Unfold `Dat.kt`. Rewrite using `[Te_mul_H D a hG γ x h]`.
-/
theorem kt_mul_H (k : I → ℕ) (a : ι → Gf) (hG : D.Good a) (γ : GL (Fin 2) F) (z : X I) (x : Gf) (h : D.H) :
    D.kt k a γ z (x * h) = D.kt k a γ z x := by
  unfold Dat.kt
  rw [Te_mul_H D a hG γ x h]

/- English proof (translation)
Establish `hT : D.Te a (d * g * d⁻¹) (D.j d * x) = D.Te a g x`. Unfold `Dat.Te`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 1`. Simplify using `only [map_mul, map_inv]`.

Use `group`. Establish `hQ : qq k (D.act d z) (D.act (d * g * d⁻¹) (D.act d z)) * D.J k (d * g * d⁻¹) (D.act d z) = qq k z (D.act g z) * D.J k g z`. Unfold `qq Dat.J`. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations.

Simplify using `only [act_apply]`. Establish `e : D.r v (d * g * d⁻¹) • D.r v d • z v = D.r v d • D.r v g • z v`. Rewrite using `[smul_smul, smul_smul, ← map_mul, ← map_mul, inv_mul_cancel_right]`. Rewrite using `[e, map_mul, map_mul, map_inv]`. Conclude with `block_frame_conjugation_identity hB.1 hB.2.1 hB.2.2.1 (k v) (D.r v d) (D.r v g) (z v)`.

Unfold `Dat.kt`. Rewrite using `[hT, hQ]`.
-/
theorem kt_conj (hB : B1b) (k : I → ℕ) (a : ι → Gf) (d g : GL (Fin 2) F) (z : X I) (x : Gf) :
    D.kt k a (d * g * d⁻¹) (D.act d z) (D.j d * x) = D.kt k a g z x := by
  have hT : D.Te a (d * g * d⁻¹) (D.j d * x) = D.Te a g x := by
    unfold Dat.Te
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    simp only [map_mul, map_inv]
    group
  have hQ : qq k (D.act d z) (D.act (d * g * d⁻¹) (D.act d z)) * D.J k (d * g * d⁻¹) (D.act d z) =
      qq k z (D.act g z) * D.J k g z := by
    unfold qq Dat.J
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    simp only [act_apply]
    have e : D.r v (d * g * d⁻¹) • D.r v d • z v = D.r v d • D.r v g • z v := by
      rw [smul_smul, smul_smul, ← map_mul, ← map_mul, inv_mul_cancel_right]
    rw [e, map_mul, map_mul, map_inv]
    exact block_frame_conjugation_identity hB.1 hB.2.1 hB.2.2.1 (k v) (D.r v d) (D.r v g) (z v)
  unfold Dat.kt
  rw [hT, hQ]

/- English proof (translation)
Establish `hQJ : ‖qq k z (D.act g z) * D.J k g z‖ = (∏ v, ((k v : ℝ) - 1) / (4 * Real.pi)) * Kap k z (D.act g z)`. Unfold `qq Dat.J Kap`. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, norm_prod]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[act_apply]`.

Conclude with `norm_qj hB (k v) (hk v) (D.r v g) (z v)`. Unfold `Dat.kt`. Rewrite using `[norm_mul, mul_assoc]`. Establish `h0 : 0 ≤ ‖qq k z (D.act g z) * D.J k g z‖` using `norm_nonneg _`. Rewrite `h0`, the goal using `[hQJ]`.

Conclude with `mul_le_mul_of_nonneg_right (norm_Te_le D hx a g x) h0`.
-/
theorem norm_kt (hx : D.Ax) (hB : B1b) (k : I → ℕ) (hk : ∀ v, 1 ≤ k v) (a : ι → Gf) (g : GL (Fin 2) F)
    (z : X I) (x : Gf) :
    ‖D.kt k a g z x‖ ≤ (Fintype.card ι * ∏ v, ((k v : ℝ) - 1) / (4 * Real.pi)) * Kap k z (D.act g z) := by
  have hQJ : ‖qq k z (D.act g z) * D.J k g z‖ =
      (∏ v, ((k v : ℝ) - 1) / (4 * Real.pi)) * Kap k z (D.act g z) := by
    unfold qq Dat.J Kap
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, norm_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [act_apply]
    exact norm_qj hB (k v) (hk v) (D.r v g) (z v)
  unfold Dat.kt
  rw [norm_mul, mul_assoc]
  have h0 : 0 ≤ ‖qq k z (D.act g z) * D.J k g z‖ := norm_nonneg _
  rw [hQJ] at h0 ⊢
  exact mul_le_mul_of_nonneg_right (norm_Te_le D hx a g x) h0

/- English proof (translation)
Take `⟨-, -, -, -, -, -, hj, hq, -⟩` from `hB`. Take `⟨-, -, hs⟩` from `hA`. Unfold `qq Dat.J`. Apply `Continuous.mul` to reduce the goal to its premises. Apply `continuous_finsetProd` to reduce the goal to its premises.

Introduce `v _`. Simplify using `only [act_apply]`. Establish `h1 : Continuous fun z : X I => z v` using `continuous_apply v`. Establish `h2 : Continuous fun z : X I => D.r v g • z v` using `(hs (D.r v g)).1.comp h1`. Conclude with `(hq (k v)).comp (h1.prodMk h2)`.

Apply `continuous_finsetProd` to reduce the goal to its premises. Introduce `v _`. Conclude with `(hj (k v) (D.r v g)).comp (continuous_apply v)`.
-/
theorem cont_qJ (hA : B1a) (hB : B1b) (k : I → ℕ) (g : GL (Fin 2) F) :
    Continuous fun z : X I => qq k z (D.act g z) * D.J k g z := by
  obtain ⟨-, -, -, -, -, -, hj, hq, -⟩ := hB
  obtain ⟨-, -, hs⟩ := hA
  unfold qq Dat.J
  apply Continuous.mul
  · apply continuous_finsetProd
    intro v _
    simp only [act_apply]
    have h1 : Continuous fun z : X I => z v := continuous_apply v
    have h2 : Continuous fun z : X I => D.r v g • z v := (hs (D.r v g)).1.comp h1
    exact (hq (k v)).comp (h1.prodMk h2)
  · apply continuous_finsetProd
    intro v _
    exact (hj (k v) (D.r v g)).comp (continuous_apply v)

/- English proof (translation)
Take `⟨c, hc⟩` from `QuotientGroup.mk_out_eq_mul (Subgroup.center (GL (Fin 2) F)) g`. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul D.H x`. Unfold `Dat.kk Dat.rep`. Simplify using `only`. Rewrite using `[hc, hh, kt_mul_center D hB k a hH.compat g c c.2 z (x * h), kt_mul_H D k a hH.good g z x h]`.
-/
theorem kk_mk (hB : B1b) (k : I → ℕ) (a : ι → Gf) (hH : D.Hyp k a) (g : GL (Fin 2) F) (x : Gf) (z : D.Xs) :
    D.kk k a (g : PG F) (((x : Gf ⧸ D.H) : D.Om), z) = D.kt k a g z x := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL (Fin 2) F)) g
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul D.H x
  unfold Dat.kk Dat.rep
  dsimp only
  rw [hc, hh, kt_mul_center D hB k a hH.compat g c c.2 z (x * h), kt_mul_H D k a hH.good g z x h]

/- English proof (translation)
Establish `h1 : ((γ.out : GL (Fin 2) F) : PG F) = γ` using `QuotientGroup.out_eq' γ`. Establish `h2` using `D.mk_smulO γ.out (D.rep y)`. Rewrite `h2` using `[h1]`. Use `Eq.trans ?_ h2` and prove the remaining obligations. Conclude with `congrArg (fun w : D.Om => γ • w) (QuotientGroup.out_eq' y).symm`.
-/
theorem smul_eq (γ : PG F) (y : D.Om) : γ • y = ((D.j γ.out * D.rep y : Gf) : Gf ⧸ D.H) := by
  have h1 : ((γ.out : GL (Fin 2) F) : PG F) = γ := QuotientGroup.out_eq' γ
  have h2 := D.mk_smulO γ.out (D.rep y)
  rw [h1] at h2
  refine Eq.trans ?_ h2
  exact congrArg (fun w : D.Om => γ • w) (QuotientGroup.out_eq' y).symm

end KernelTermsInvariantLemmas

end UpperTheory.Esk

/- English proof (translation)
Take `⟨y1, y2⟩` from `y`. Take `⟨d, rfl⟩` from `QuotientGroup.mk_surjective δ`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective γ`. Take `⟨x, rfl⟩ : ∃ x : Gf, ((x : Gf ⧸ D.H) : D.Om) = y1` from `QuotientGroup.mk_surjective y1`. Establish `e1 : (d : UpperTheory.Esk.PG F) * (g : UpperTheory.Esk.PG F) * (d : UpperTheory.Esk.PG F)⁻¹ = ((d * g * d⁻¹ : GL (Fin 2) F) : UpperTheory.Esk.PG F)`.

Simplify using `only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]`. Establish `e2 : (d : UpperTheory.Esk.PG F) • ((((x : Gf ⧸ D.H) : D.Om), y2) : D.Y) = ((((D.j d * x : Gf) : Gf ⧸ D.H) : D.Om), D.act d y2)` using `Prod.ext (D.mk_smulO d x) (D.mk_smulX d y2)`. Rewrite using `[e1, e2]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem UpperTheory.Esk.kk_conj_smul_eq {F I Gf ι : Type} [Field F] [Group Gf] [Fintype I] [Fintype ι]
    (D : UpperTheory.Esk.Dat F I Gf) (hB : UpperTheory.Esk.B1b) (k : I → ℕ) (a : ι → Gf) (hH : D.Hyp k a)
    (δ γ : UpperTheory.Esk.PG F) (y : D.Y) :
    D.kk k a (δ * γ * δ⁻¹) (δ • y) = D.kk k a γ y := by
  obtain ⟨y1, y2⟩ := y
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective δ
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
  obtain ⟨x, rfl⟩ : ∃ x : Gf, ((x : Gf ⧸ D.H) : D.Om) = y1 := QuotientGroup.mk_surjective y1
  have e1 : (d : UpperTheory.Esk.PG F) * (g : UpperTheory.Esk.PG F) * (d : UpperTheory.Esk.PG F)⁻¹ =
      ((d * g * d⁻¹ : GL (Fin 2) F) : UpperTheory.Esk.PG F) := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have e2 : (d : UpperTheory.Esk.PG F) • ((((x : Gf ⧸ D.H) : D.Om), y2) : D.Y) =
      ((((D.j d * x : Gf) : Gf ⧸ D.H) : D.Om), D.act d y2) :=
    Prod.ext (D.mk_smulO d x) (D.mk_smulX d y2)
  rw [e1, e2]
  calc _ = D.kt k a (d * g * d⁻¹) (D.act d y2) (D.j d * x) := UpperTheory.Esk.KernelTermsInvariantLemmas.kk_mk D hB k a hH _ _ _
    _ = D.kt k a g y2 x := UpperTheory.Esk.KernelTermsInvariantLemmas.kt_conj D hB k a d g y2 x
    _ = D.kk k a (g : UpperTheory.Esk.PG F) (((x : Gf ⧸ D.H) : D.Om), y2) := (UpperTheory.Esk.KernelTermsInvariantLemmas.kk_mk D hB k a hH _ _ _).symm

/- English proof (translation)
Establish `: Countable D.Om` using `hH.ax.cO`. Establish `: MeasurableSingletonClass D.Om` using `⟨fun _ => trivial⟩`. Establish `hm : ∀ ω : D.Om, Measurable fun z : D.Xs => D.kk k a γ (ω, z)`. Introduce `ω`. Establish `hc` using `(UpperTheory.Esk.KernelTermsInvariantLemmas.cont_qJ D hA hB k γ.out).measurable`.

Use `show Measurable fun z : D.Xs => D.Te a γ.out (D.rep ω) * (UpperTheory.Esk.qq k z (D.act γ.out z) * D.J k γ.out z)`. Conclude with `measurable_const.mul hc`. Establish `h1 : Measurable (fun p : D.Xs × D.Om => D.kk k a γ (p.2, p.1))` using `measurable_from_prod_countable_left hm`. Establish `h3 : D.kk k a γ = (fun p : D.Xs × D.Om => D.kk k a γ (p.2, p.1)) ∘ Prod.swap`. Use function extensionality and compare the values at `p`.

Both sides reduce to the same expression. Rewrite using `[h3]`. Conclude with `h1.comp measurable_swap`.
-/
private theorem UpperTheory.Esk.measurable_kk {F I Gf ι : Type} [Field F] [Group Gf] [Fintype I] [Fintype ι]
    (D : UpperTheory.Esk.Dat F I Gf) (hA : UpperTheory.Esk.B1a) (hB : UpperTheory.Esk.B1b) (k : I → ℕ) (a : ι → Gf) (hH : D.Hyp k a)
    (γ : UpperTheory.Esk.PG F) : Measurable (D.kk k a γ) := by
  have : Countable D.Om := hH.ax.cO
  have : MeasurableSingletonClass D.Om := ⟨fun _ => trivial⟩
  have hm : ∀ ω : D.Om, Measurable fun z : D.Xs => D.kk k a γ (ω, z) := by
    intro ω
    have hc := (UpperTheory.Esk.KernelTermsInvariantLemmas.cont_qJ D hA hB k γ.out).measurable
    show Measurable fun z : D.Xs => D.Te a γ.out (D.rep ω) * (UpperTheory.Esk.qq k z (D.act γ.out z) * D.J k γ.out z)
    exact measurable_const.mul hc
  have h1 : Measurable (fun p : D.Xs × D.Om => D.kk k a γ (p.2, p.1)) :=
    measurable_from_prod_countable_left hm
  have h3 : D.kk k a γ = (fun p : D.Xs × D.Om => D.kk k a γ (p.2, p.1)) ∘ Prod.swap := by
    funext p
    rfl
  rw [h3]
  exact h1.comp measurable_swap

/- English proof (translation)
Use `⟨Fintype.card ι * ∏ v, ((k v : ℝ) - 1) / (4 * Real.pi), fun γ y => ?_⟩` and prove the remaining obligations. Establish `e : (γ • y.2 : D.Xs) = D.act γ.out y.2`. Establish `h2` using `D.mk_smulX γ.out y.2`. Rewrite `h2` using `[QuotientGroup.out_eq']`. Then use the resulting hypothesis. Rewrite using `[e]`.

Conclude with `UpperTheory.Esk.KernelTermsInvariantLemmas.norm_kt D hH.ax hB k (fun v => le_trans (by norm_num) (hH.four v)) a γ.out y.2 (D.rep y.1)`.
-/
private theorem UpperTheory.Esk.exists_norm_kk_le_mul_kap {F I Gf ι : Type} [Field F] [Group Gf] [Fintype I] [Fintype ι]
    (D : UpperTheory.Esk.Dat F I Gf) (hB : UpperTheory.Esk.B1b) (k : I → ℕ) (a : ι → Gf) (hH : D.Hyp k a) :
    ∃ C : ℝ, ∀ (γ : UpperTheory.Esk.PG F) (y : D.Y), ‖D.kk k a γ y‖ ≤ C * UpperTheory.Esk.Kap k y.2 (γ • y.2 : D.Xs) := by
  refine ⟨Fintype.card ι * ∏ v, ((k v : ℝ) - 1) / (4 * Real.pi), fun γ y => ?_⟩
  have e : (γ • y.2 : D.Xs) = D.act γ.out y.2 := by
    have h2 := D.mk_smulX γ.out y.2
    rwa [QuotientGroup.out_eq'] at h2
  rw [e]
  exact UpperTheory.Esk.KernelTermsInvariantLemmas.norm_kt D hH.ax hB k (fun v => le_trans (by norm_num) (hH.four v)) a γ.out y.2 (D.rep y.1)

/- English proof (translation)
Unfold `UpperTheory.Esk.Dat.Te at hT`. Take `⟨i, -, hi⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hT`. Establish `hm : (D.rep y)⁻¹ * (D.j γ.out)⁻¹ * D.rep y * a i ∈ D.H`. Assume the negation of the conclusion as `hn`. Apply `hi` to reduce the goal to its premises.

Simplify using `[UpperTheory.Esk.Dat.ee, hn]`. Use `⟨i, ?_⟩` and prove the remaining obligations. Rewrite using `[UpperTheory.Esk.KernelTermsInvariantLemmas.smul_eq D γ y]`. Apply `QuotientGroup.eq.2` to reduce the goal to its premises. Establish `e : (D.j γ.out * D.rep y)⁻¹ * (D.rep y * a i) = (D.rep y)⁻¹ * (D.j γ.out)⁻¹ * D.rep y * a i` using `by group`.

Rewrite using `[e]`. Conclude with `hm`.
-/
private theorem UpperTheory.Esk.exists_smul_eq_rep_mul_of_te_ne_zero {F I Gf ι : Type} [Field F] [Group Gf] [Fintype I] [Fintype ι]
    (D : UpperTheory.Esk.Dat F I Gf) (a : ι → Gf) (γ : UpperTheory.Esk.PG F) (y : D.Om)
    (hT : D.Te a γ.out (D.rep y) ≠ 0) : ∃ i, γ • y = ((D.rep y * a i : Gf) : Gf ⧸ D.H) := by
  unfold UpperTheory.Esk.Dat.Te at hT
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
  have hm : (D.rep y)⁻¹ * (D.j γ.out)⁻¹ * D.rep y * a i ∈ D.H := by
    by_contra hn
    apply hi
    simp [UpperTheory.Esk.Dat.ee, hn]
  refine ⟨i, ?_⟩
  rw [UpperTheory.Esk.KernelTermsInvariantLemmas.smul_eq D γ y]
  apply QuotientGroup.eq.2
  have e : (D.j γ.out * D.rep y)⁻¹ * (D.rep y * a i) = (D.rep y)⁻¹ * (D.j γ.out)⁻¹ * D.rep y * a i := by
    group
  rw [e]
  exact hm

/- English proof (translation)
Rewrite `hγ` using `[UpperTheory.Esk.KernelTermsInvariantLemmas.smul_eq D γ y]`. Establish `hm` using `QuotientGroup.eq.1 hγ`. Apply `hH.reg γ.out (D.rep y) i` to reduce the goal to its premises. Establish `e : (a i)⁻¹ * ((D.rep y)⁻¹ * D.j γ.out * D.rep y) = ((D.j γ.out * D.rep y)⁻¹ * (D.rep y * a i))⁻¹` using `by group`. Rewrite using `[e]`.

Conclude with `D.H.inv_mem hm`.
-/
private theorem UpperTheory.Esk.trace_ne_zero_and_sq_ne_four_det_of_smul {F I Gf ι : Type} [Field F] [Group Gf] [Fintype I] [Fintype ι]
    (D : UpperTheory.Esk.Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (hH : D.Hyp k a) (γ : UpperTheory.Esk.PG F) (y : D.Om) (i : ι)
    (hγ : γ • y = ((D.rep y * a i : Gf) : Gf ⧸ D.H)) :
    γ.out.val.trace ≠ 0 ∧ γ.out.val.trace ^ 2 ≠ 4 * γ.out.val.det := by
  rw [UpperTheory.Esk.KernelTermsInvariantLemmas.smul_eq D γ y] at hγ
  have hm := QuotientGroup.eq.1 hγ
  apply hH.reg γ.out (D.rep y) i
  have e : (a i)⁻¹ * ((D.rep y)⁻¹ * D.j γ.out * D.rep y) = ((D.j γ.out * D.rep y)⁻¹ * (D.rep y * a i))⁻¹ := by
    group
  rw [e]
  exact D.H.inv_mem hm

open UpperTheory.Esk UpperTheory.Esk.KernelTermsInvariantLemmas in
/- English proof (translation)
Introduce `hA hB`. Unfold `KernelTermsInvariantBounded AllH`. Introduce `F I Gf ι _ _ _ _ D k a hH`. Conclude with `⟨fun γ z x => kk_mk D hB k a hH γ x z, fun δ γ y => kk_conj_smul_eq D hB k a hH δ γ y, fun γ => measurable_kk D hA hB k a hH γ, exists_norm_kk_le_mul_kap D hB k a hH, fun γ y hT => exists_smul_eq_rep_mul_of_te_ne_zero D a γ y hT, fun γ y i hγ => trace_ne_zero_and_sq_ne_four_det_o …`.
-/
theorem UpperTheory.Esk.kernel_terms_invariant_bounded_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.KernelTermsInvariantBounded := by
  intro hA hB
  unfold KernelTermsInvariantBounded AllH
  intro F I Gf ι _ _ _ _ D k a hH
  exact ⟨fun γ z x => kk_mk D hB k a hH γ x z, fun δ γ y => kk_conj_smul_eq D hB k a hH δ γ y,
    fun γ => measurable_kk D hA hB k a hH γ, exists_norm_kk_le_mul_kap D hB k a hH,
    fun γ y hT => exists_smul_eq_rep_mul_of_te_ne_zero D a γ y hT, fun γ y i hγ => trace_ne_zero_and_sq_ne_four_det_of_smul D k a hH γ y i hγ⟩
