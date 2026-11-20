import Formalism.FilteredPoleLength.ReducedBasisBounds.ParameterInequalities

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Finset Matrix Polynomial

/- English proof (translation)
Introduce `ρ hρ`. Establish `hρ0 : (1:ℝ) ≤ ρ` using `by exact_mod_cast hρ`. Establish `hpos : (0:ℝ) < ρ` using `by linarith`. Establish `hx0 : 0 ≤ (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10` using `by positivity`. Establish `hρx : (ρ:ℝ) * ((ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10) ≤ 1 / 10`.

Establish `e : (ρ:ℝ) * (ρ:ℝ) ^ (-(3:ℝ)/2) = (ρ:ℝ) ^ (-(1:ℝ)/2)`. Rewrite using `[show (-(1:ℝ)/2) = 1 + (-(3:ℝ)/2) by norm_num, Real.rpow_add hpos, Real.rpow_one]`. Establish `h1 : (ρ:ℝ) ^ (-(1:ℝ)/2) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hρ0 (by norm_num)`. Rewrite using `[mul_div_assoc', e]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1 : (1 + (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10) ^ ρ ≤ Real.exp ((ρ:ℝ) * ((ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10))`. Rewrite using `[Real.exp_nat_mul]`. Conclude with `pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp ((ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10)]) ρ`. Establish `h2 : Real.exp ((ρ:ℝ) * ((ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10)) ≤ Real.exp (1/10)` using `Real.exp_le_exp.2 hρx`. Establish `h3 : Real.exp (1/10) ≤ 3/2`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h4 : (3/2:ℝ)^10 < Real.exp (1/10) ^ 10` using `pow_lt_pow_left₀ hc (by norm_num) (by norm_num)`. Rewrite `h4` using `[← Real.exp_nat_mul]`. Evaluate the numerical expressions using `at h4`.

Combine the linear relations using `[Real.exp_one_lt_d9]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem detPerturbNumeric : DetPerturbNumeric := by
  intro ρ hρ
  have hρ0 : (1:ℝ) ≤ ρ := by exact_mod_cast hρ
  have hpos : (0:ℝ) < ρ := by linarith
  have hx0 : 0 ≤ (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10 := by positivity
  have hρx : (ρ:ℝ) * ((ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10) ≤ 1 / 10 := by
    have e : (ρ:ℝ) * (ρ:ℝ) ^ (-(3:ℝ)/2) = (ρ:ℝ) ^ (-(1:ℝ)/2) := by
      rw [show (-(1:ℝ)/2) = 1 + (-(3:ℝ)/2) by norm_num, Real.rpow_add hpos, Real.rpow_one]
    have h1 : (ρ:ℝ) ^ (-(1:ℝ)/2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hρ0 (by norm_num)
    rw [mul_div_assoc', e]
    linarith
  have h1 : (1 + (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10) ^ ρ
      ≤ Real.exp ((ρ:ℝ) * ((ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith)
      (by linarith [Real.add_one_le_exp ((ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10)]) ρ
  have h2 : Real.exp ((ρ:ℝ) * ((ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10)) ≤ Real.exp (1/10) :=
    Real.exp_le_exp.2 hρx
  have h3 : Real.exp (1/10) ≤ 3/2 := by
    by_contra hc
    push_neg at hc
    have h4 : (3/2:ℝ)^10 < Real.exp (1/10) ^ 10 := pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
    rw [← Real.exp_nat_mul] at h4
    norm_num at h4
    linarith [Real.exp_one_lt_d9]
  linarith

/- English proof (translation)
Introduce `𝕜 _ i κ _ w σ₀ ε Δmax hΔ`. Establish `hΔ0 : 0 ≤ Δmax` using `(norm_nonneg _).trans (hΔ σ₀)`. Establish `hdet : ∀ v : Fin i → Fin i → 𝕜, (Matrix.of fun a j => v j a).det = Matrix.detRowAlternating v`. Introduce `v`. Rewrite using `[← Matrix.det_transpose]`.

Both sides reduce to the same expression. Set `c : Fin i → Option κ → 𝕜` to `fun j o => Option.elim o 1 (ε j)`. Set `τ : Fin i → Option κ → κ` to `fun j o => Option.elim o (σ₀ j) id`. Establish `hcol : (fun j => w (σ₀ j) + ∑ k, ε j k • w k) = fun j => ∑ o, c j o • w (τ j o)`. Use function extensionality and compare the values at `j`.

Rewrite using `[Fintype.sum_option]`. Simplify using `[c, τ]`. Establish `h1` using `(Matrix.detRowAlternating (n := Fin i) (R := 𝕜)).toMultilinearMap.map_sum (fun j o => c j o • w (τ j o))`. Establish `h2 : ∀ r : Fin i → Option κ, (Matrix.detRowAlternating (n` using `Fin i) (R := 𝕜)).toMultilinearMap (fun j => c j (r j) • w (τ j (r j))) = (∏ j, c j (r j)) * Matrix.detRowAlternating (fun j => w (τ j (r j))) := by`. Introduce `r`.

Rewrite using `[MultilinearMap.map_smul_univ, smul_eq_mul]`. Both sides reduce to the same expression. Establish `hpert : (Matrix.of fun a j => (w (σ₀ j) + ∑ k, ε j k • w k) a).det = ∑ r : Fin i → Option κ, (∏ j, c j (r j)) * Matrix.detRowAlternating (fun j => w (τ j (r j)))`. Rewrite using `[hdet (fun j => w (σ₀ j) + ∑ k, ε j k • w k), hcol]`. Conclude with `h1.trans (Finset.sum_congr rfl (fun r _ => h2 r))`.

Establish `hbase : (Matrix.of fun a j => w (σ₀ j) a).det = Matrix.detRowAlternating (fun j => w (σ₀ j))` using `hdet _`. Set `r0 : Fin i → Option κ` to `fun _ => none`. Establish `hr0 : (∏ j, c j (r0 j)) * Matrix.detRowAlternating (fun j => w (τ j (r0 j))) = Matrix.detRowAlternating (fun j => w (σ₀ j))`. Simplify using `[c, τ, r0]`. Rewrite using `[hpert, hbase, ← Finset.add_sum_erase _ _ (Finset.mem_univ r0), hr0, add_sub_cancel_left]`.

Establish `hb : ∀ r : Fin i → Option κ, ‖(∏ j, c j (r j)) * Matrix.detRowAlternating (fun j => w (τ j (r j)))‖ ≤ (∏ j, ‖c j (r j)‖) * Δmax`. Introduce `r`. Rewrite using `[norm_mul, norm_prod]`. Apply `mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => norm_nonneg _))` to reduce the goal to its premises. Use `hΔ (fun j => τ j (r j))` as an intermediate fact.

Rewrite `this` using `[hdet]`. Then use the resulting hypothesis. Establish `hsum : ∏ j, (1 + ∑ k, ‖ε j k‖) = ∑ r : Fin i → Option κ, ∏ j, ‖c j (r j)‖`. Establish `e : ∀ j, (1 + ∑ k, ‖ε j k‖) = ∑ o, ‖c j o‖`. Introduce `j`. Rewrite using `[Fintype.sum_option]`.

Simplify using `[c]`. Repeatedly rewrite using `[e]`. Rewrite using `[Finset.prod_univ_sum]`. Apply the tactic sequence `try rw [Fintype.piFinset_univ]`. Establish `hr0n : ∏ j, ‖c j (r0 j)‖ = 1` using `by simp [c, r0]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.sum_mul, Finset.sum_erase_eq_sub (Finset.mem_univ r0), hr0n, hsum]`.
-/
theorem detPerturbation : DetPerturbation := by
  intro 𝕜 _ i κ _ w σ₀ ε Δmax hΔ
  classical
  have hΔ0 : 0 ≤ Δmax := (norm_nonneg _).trans (hΔ σ₀)
  have hdet : ∀ v : Fin i → Fin i → 𝕜,
      (Matrix.of fun a j => v j a).det = Matrix.detRowAlternating v := by
    intro v
    rw [← Matrix.det_transpose]
    rfl
  let c : Fin i → Option κ → 𝕜 := fun j o => Option.elim o 1 (ε j)
  let τ : Fin i → Option κ → κ := fun j o => Option.elim o (σ₀ j) id
  have hcol : (fun j => w (σ₀ j) + ∑ k, ε j k • w k) = fun j => ∑ o, c j o • w (τ j o) := by
    funext j
    rw [Fintype.sum_option]
    simp [c, τ]
  have h1 := (Matrix.detRowAlternating (n := Fin i) (R := 𝕜)).toMultilinearMap.map_sum
    (fun j o => c j o • w (τ j o))
  have h2 : ∀ r : Fin i → Option κ,
      (Matrix.detRowAlternating (n := Fin i) (R := 𝕜)).toMultilinearMap
        (fun j => c j (r j) • w (τ j (r j)))
      = (∏ j, c j (r j)) * Matrix.detRowAlternating (fun j => w (τ j (r j))) := by
    intro r
    rw [MultilinearMap.map_smul_univ, smul_eq_mul]
    rfl
  have hpert : (Matrix.of fun a j => (w (σ₀ j) + ∑ k, ε j k • w k) a).det
      = ∑ r : Fin i → Option κ, (∏ j, c j (r j)) * Matrix.detRowAlternating (fun j => w (τ j (r j))) := by
    rw [hdet (fun j => w (σ₀ j) + ∑ k, ε j k • w k), hcol]
    exact h1.trans (Finset.sum_congr rfl (fun r _ => h2 r))
  have hbase : (Matrix.of fun a j => w (σ₀ j) a).det = Matrix.detRowAlternating (fun j => w (σ₀ j)) :=
    hdet _
  let r0 : Fin i → Option κ := fun _ => none
  have hr0 : (∏ j, c j (r0 j)) * Matrix.detRowAlternating (fun j => w (τ j (r0 j)))
      = Matrix.detRowAlternating (fun j => w (σ₀ j)) := by
    simp [c, τ, r0]
  rw [hpert, hbase, ← Finset.add_sum_erase _ _ (Finset.mem_univ r0), hr0, add_sub_cancel_left]
  have hb : ∀ r : Fin i → Option κ,
      ‖(∏ j, c j (r j)) * Matrix.detRowAlternating (fun j => w (τ j (r j)))‖
        ≤ (∏ j, ‖c j (r j)‖) * Δmax := by
    intro r
    rw [norm_mul, norm_prod]
    apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    have := hΔ (fun j => τ j (r j))
    rwa [hdet] at this
  have hsum : ∏ j, (1 + ∑ k, ‖ε j k‖) = ∑ r : Fin i → Option κ, ∏ j, ‖c j (r j)‖ := by
    have e : ∀ j, (1 + ∑ k, ‖ε j k‖) = ∑ o, ‖c j o‖ := by
      intro j
      rw [Fintype.sum_option]
      simp [c]
    simp_rw [e]
    rw [Finset.prod_univ_sum]
    try rw [Fintype.piFinset_univ]
  have hr0n : ∏ j, ‖c j (r0 j)‖ = 1 := by simp [c, r0]
  calc ‖∑ r ∈ Finset.univ.erase r0, (∏ j, c j (r j)) * Matrix.detRowAlternating (fun j => w (τ j (r j)))‖
      ≤ ∑ r ∈ Finset.univ.erase r0, ‖(∏ j, c j (r j)) * Matrix.detRowAlternating (fun j => w (τ j (r j)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.univ.erase r0, (∏ j, ‖c j (r j)‖) * Δmax := Finset.sum_le_sum (fun r _ => hb r)
    _ = ((∏ j, (1 + ∑ k, ‖ε j k‖)) - 1) * Δmax := by
        rw [← Finset.sum_mul, Finset.sum_erase_eq_sub (Finset.mem_univ r0), hr0n, hsum]

/- English proof (translation)
Break down `subsingleton_or_nontrivial K with hK | hK` into its components or cases. Conclude with `Subsingleton.elim _ _`. Establish `e : (1 + (X : K[X]) • M.map C) = 1 - (X : K[X]) • (-M).map C`. Establish `hm : (-M).map C = -(M.map C)`. Use extensionality with `a b`.

Simplify using the standard rewrite rules. Rewrite using `[hm, smul_neg, sub_neg_eq_add]`. Rewrite using `[e]`. Express the relevant statement in the definitionally equal form `(Matrix.charpolyRev (-M)).coeff i = M.det`. Rewrite using `[← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, Polynomial.revAt_le (le_refl i), Nat.sub_self]`.

Establish `h` using `Matrix.det_eq_sign_charpoly_coeff (-M)`. Rewrite `h` using `[Fintype.card_fin, Matrix.det_neg, Fintype.card_fin]`. Establish `hu : IsUnit ((-1 : K) ^ i)` using `(isUnit_one.neg).pow i`. Conclude with `(hu.mul_left_cancel h).symm`.
-/
lemma coeff_top_det {K : Type*} [CommRing K] {i : ℕ} (M : Matrix (Fin i) (Fin i) K) :
    (det (1 + (X : K[X]) • M.map C)).coeff i = M.det := by
  rcases subsingleton_or_nontrivial K with hK | hK
  · exact Subsingleton.elim _ _
  · have e : (1 + (X : K[X]) • M.map C) = 1 - (X : K[X]) • (-M).map C := by
      have hm : (-M).map C = -(M.map C) := by
        ext a b
        simp
      rw [hm, smul_neg, sub_neg_eq_add]
    rw [e]
    change (Matrix.charpolyRev (-M)).coeff i = M.det
    rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin, Polynomial.revAt_le (le_refl i), Nat.sub_self]
    have h := Matrix.det_eq_sign_charpoly_coeff (-M)
    rw [Fintype.card_fin, Matrix.det_neg, Fintype.card_fin] at h
    have hu : IsUnit ((-1 : K) ^ i) := (isUnit_one.neg).pow i
    exact (hu.mul_left_cancel h).symm

/- English proof (translation)
Rewrite using `[← coeff_top_det (A * B)]`. Establish `h1 : (1 : Matrix (Fin i) (Fin i) K[X]) + (X : K[X]) • (A * B).map C = 1 + ((X : K[X]) • A.map C) * (B.map C)`. Rewrite using `[Matrix.map_mul, Matrix.smul_mul]`. Establish `h2 : (B.map C) * ((X : K[X]) • A.map C) = (X : K[X]) • (B * A).map C`. Rewrite using `[Matrix.mul_smul]`.

Use `congr 1`. Simplify using `[Matrix.map_mul]`. Rewrite using `[h1, det_one_add_mul_comm, h2, coeff_det_one_add_X_smul_eq_sum_minors]`.
-/
lemma det_mul_eq_sum_principal {K : Type*} [CommRing K] {i n : ℕ} (A : Matrix (Fin i) (Fin n) K)
    (B : Matrix (Fin n) (Fin i) K) :
    (A * B).det = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
      ((B * A).submatrix (Subtype.val : S → Fin n) Subtype.val).det := by
  rw [← coeff_top_det (A * B)]
  have h1 : (1 : Matrix (Fin i) (Fin i) K[X]) + (X : K[X]) • (A * B).map C
      = 1 + ((X : K[X]) • A.map C) * (B.map C) := by
    rw [Matrix.map_mul, Matrix.smul_mul]
  have h2 : (B.map C) * ((X : K[X]) • A.map C) = (X : K[X]) • (B * A).map C := by
    rw [Matrix.mul_smul]; congr 1; simp [Matrix.map_mul]
  rw [h1, det_one_add_mul_comm, h2, coeff_det_one_add_X_smul_eq_sum_minors]

/- English proof (translation)
Rewrite using `[← Matrix.det_submatrix_equiv_self (S.orderIsoOfFin hS).toEquiv]`. Rewrite using `[show ((B * A).submatrix (Subtype.val : S → Fin n) Subtype.val).submatrix (S.orderIsoOfFin hS).toEquiv (S.orderIsoOfFin hS).toEquiv = B.submatrix (S.orderEmbOfFin hS) id * A.submatrix id (S.orderEmbOfFin hS) from by`. Use extensionality with `a b`. Simplify using `[Matrix.mul_apply, Finset.coe_orderIsoOfFin_apply]]`. Rewrite using `[Matrix.det_mul]`.
-/
lemma principal_minor_factor {K : Type*} [CommRing K] {i n : ℕ} (A : Matrix (Fin i) (Fin n) K)
    (B : Matrix (Fin n) (Fin i) K) (S : Finset (Fin n)) (hS : S.card = i) :
    ((B * A).submatrix (Subtype.val : S → Fin n) Subtype.val).det
      = (B.submatrix (S.orderEmbOfFin hS) id).det * (A.submatrix id (S.orderEmbOfFin hS)).det := by
  rw [← Matrix.det_submatrix_equiv_self (S.orderIsoOfFin hS).toEquiv]
  rw [show ((B * A).submatrix (Subtype.val : S → Fin n) Subtype.val).submatrix
      (S.orderIsoOfFin hS).toEquiv (S.orderIsoOfFin hS).toEquiv
      = B.submatrix (S.orderEmbOfFin hS) id * A.submatrix id (S.orderEmbOfFin hS) from by
    ext a b
    simp [Matrix.mul_apply, Finset.coe_orderIsoOfFin_apply]]
  rw [Matrix.det_mul]

/- English proof (translation)
Introduce `i N r M hM hNr`. Set `g : Finset (Fin N) → ℝ` to `fun S => if h : S.card = i then ‖(M.submatrix id (S.orderEmbOfFin h)).det‖ ^ 2 else 0`. Establish `h1 : (1 : ℂ) = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard i, ((Mᴴ * M).submatrix (Subtype.val : S → Fin N) Subtype.val).det`. Rewrite using `[← det_mul_eq_sum_principal M Mᴴ, hM, Matrix.det_one]`. Establish `h2 : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard i, ((Mᴴ * M).submatrix (Subtype.val : S → Fin N) Subtype.val).det = ((g S : ℝ) : ℂ)`.

Introduce `S hS`. Establish `hc` using `(Finset.mem_powersetCard.1 hS).2`. Rewrite using `[principal_minor_factor M Mᴴ S hc]`. Simplify using `only [g, dif_pos hc]`. Establish `e : Mᴴ.submatrix (S.orderEmbOfFin hc) id = (M.submatrix id (S.orderEmbOfFin hc))ᴴ`.

Use extensionality with `a b`. Simplify using `[Matrix.conjTranspose_apply]`. Rewrite using `[e, Matrix.det_conjTranspose, Complex.star_def, Complex.conj_mul']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `h3 : (1 : ℝ) = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard i, g S`. Use `h1.trans (Finset.sum_congr rfl h2)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Establish `hlt : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard i, g S < (2 : ℝ) ^ (-(r : ℝ))`. Introduce `S hS`. Establish `hc` using `(Finset.mem_powersetCard.1 hS).2`. Simplify using `only [g, dif_pos hc]`. Establish `h4` using `hcon _ (S.orderEmbOfFin hc).strictMono`.

Establish `h5 : ‖(M.submatrix id (S.orderEmbOfFin hc)).det‖ ^ 2 < ((2 : ℝ) ^ (-(r : ℝ) / 2)) ^ 2` using `pow_lt_pow_left₀ h4 (norm_nonneg _) (by norm_num)`. Establish `h6 : ((2 : ℝ) ^ (-(r : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ (-(r : ℝ))`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]`. Evaluate the numerical expressions. Conclude with `h5.trans_eq h6`.

Distinguish the cases in `hne : ((Finset.univ : Finset (Fin N)).powersetCard i).Nonempty`. Establish `h6` using `Finset.sum_lt_sum_of_nonempty hne hlt`. Rewrite `h6` using `[Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]`. Establish `h7 : ((N.choose i : ℕ) : ℝ) ≤ (2 : ℝ) ^ (N : ℝ)`. Rewrite using `[Real.rpow_natCast]`.

Conclude with `Nat.choose_le_two_pow N i` after adjusting the coercions. Establish `h8 : (2 : ℝ) ^ (N : ℝ) * (2 : ℝ) ^ (-(r : ℝ)) ≤ 1`. Rewrite using `[← Real.rpow_add (by norm_num)]`. Apply `Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)` to reduce the goal to its premises. Establish `: (N : ℝ) ≤ r` using `by exact_mod_cast hNr`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h9 : ((N.choose i : ℕ) : ℝ) * (2 : ℝ) ^ (-(r : ℝ)) ≤ (2 : ℝ) ^ (N : ℝ) * (2 : ℝ) ^ (-(r : ℝ))` using `mul_le_mul_of_nonneg_right h7 (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hne` using `[Finset.not_nonempty_iff_eq_empty]`. Rewrite `h3` using `[hne, Finset.sum_empty]`.

Evaluate the numerical expressions using `at h3`.
-/
theorem cauchyBinetMax : CauchyBinetMax := by
  intro i N r M hM hNr
  classical
  let g : Finset (Fin N) → ℝ := fun S =>
    if h : S.card = i then ‖(M.submatrix id (S.orderEmbOfFin h)).det‖ ^ 2 else 0
  have h1 : (1 : ℂ) = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard i,
      ((Mᴴ * M).submatrix (Subtype.val : S → Fin N) Subtype.val).det := by
    rw [← det_mul_eq_sum_principal M Mᴴ, hM, Matrix.det_one]
  have h2 : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard i,
      ((Mᴴ * M).submatrix (Subtype.val : S → Fin N) Subtype.val).det = ((g S : ℝ) : ℂ) := by
    intro S hS
    have hc := (Finset.mem_powersetCard.1 hS).2
    rw [principal_minor_factor M Mᴴ S hc]
    simp only [g, dif_pos hc]
    have e : Mᴴ.submatrix (S.orderEmbOfFin hc) id = (M.submatrix id (S.orderEmbOfFin hc))ᴴ := by
      ext a b
      simp [Matrix.conjTranspose_apply]
    rw [e, Matrix.det_conjTranspose, Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  have h3 : (1 : ℝ) = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard i, g S := by
    have := h1.trans (Finset.sum_congr rfl h2)
    exact_mod_cast this
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard i, g S < (2 : ℝ) ^ (-(r : ℝ)) := by
    intro S hS
    have hc := (Finset.mem_powersetCard.1 hS).2
    simp only [g, dif_pos hc]
    have h4 := hcon _ (S.orderEmbOfFin hc).strictMono
    have h5 : ‖(M.submatrix id (S.orderEmbOfFin hc)).det‖ ^ 2 < ((2 : ℝ) ^ (-(r : ℝ) / 2)) ^ 2 :=
      pow_lt_pow_left₀ h4 (norm_nonneg _) (by norm_num)
    have h6 : ((2 : ℝ) ^ (-(r : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ (-(r : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    exact h5.trans_eq h6
  by_cases hne : ((Finset.univ : Finset (Fin N)).powersetCard i).Nonempty
  · have h6 := Finset.sum_lt_sum_of_nonempty hne hlt
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin] at h6
    have h7 : ((N.choose i : ℕ) : ℝ) ≤ (2 : ℝ) ^ (N : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast Nat.choose_le_two_pow N i
    have h8 : (2 : ℝ) ^ (N : ℝ) * (2 : ℝ) ^ (-(r : ℝ)) ≤ 1 := by
      rw [← Real.rpow_add (by norm_num)]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      have : (N : ℝ) ≤ r := by exact_mod_cast hNr
      linarith
    have h9 : ((N.choose i : ℕ) : ℝ) * (2 : ℝ) ^ (-(r : ℝ)) ≤ (2 : ℝ) ^ (N : ℝ) * (2 : ℝ) ^ (-(r : ℝ)) :=
      mul_le_mul_of_nonneg_right h7 (by positivity)
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at h3
    norm_num at h3

open MeasureTheory in
/- English proof (translation)
Introduce `n P δ R hδ hδR hR hsep`. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality. Simplify using `only [pow_zero]`. Establish `: P.card ≤ 1` using `Finset.card_le_one.2 (fun a _ b _ => PiLp.ext (fun i => Fin.elim0 i))`.

Conclude with `this` after adjusting the coercions. Use `haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hn) classical`. Establish `hd2 : 0 < δ / 2` using `by linarith`. Establish `hV0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0` using `(Metric.measure_ball_pos volume _ one_pos).ne'`. Establish `hVt : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤` using `measure_ball_lt_top.ne`.

Establish `hball : ∀ (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 ≤ ρ → volume (Metric.ball x ρ) = ENNReal.ofReal (ρ ^ n) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)`. Introduce `x ρ hρ`. Rewrite using `[Measure.addHaar_ball _ _ hρ, finrank_euclideanSpace_fin]`. Establish `hdisj : Set.PairwiseDisjoint (↑P : Set (EuclideanSpace ℝ (Fin n))) (fun x => Metric.ball x (δ / 2))`. Introduce `x hx y hy hxy`.

Conclude with `Metric.ball_disjoint_ball (by linarith [hsep x hx y hy hxy])`. Establish `hsub : (⋃ x ∈ P, Metric.ball x (δ / 2)) ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + δ / 2)`. Introduce `z hz`. Simplify using `only [Set.mem_iUnion] at hz`. Take `⟨x, hx, hz⟩` from `hz`.

Rewrite using `[Metric.mem_ball, dist_zero_right]`. Rewrite `hz` using `[Metric.mem_ball, dist_eq_norm]`. Use `norm_le_norm_add_norm_sub' z x` as an intermediate fact. Combine the linear relations using `[hR x hx]`. Establish `hmeas : volume (⋃ x ∈ P, Metric.ball x (δ / 2)) = ∑ x ∈ P, volume (Metric.ball x (δ / 2))` using `measure_biUnion_finset hdisj (fun x _ => measurableSet_ball)`.

Establish `key : ∑ x ∈ P, volume (Metric.ball x (δ / 2)) ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + δ / 2))`. Rewrite using `[← hmeas]`. Conclude with `measure_mono hsub`. Simplify using `only [hball _ _ hd2.le, hball _ _ (by linarith : (0:ℝ) ≤ R + δ / 2), Finset.sum_const, nsmul_eq_mul] at key`. Rewrite `key` using `[← mul_assoc]`.

Establish `key2` using `(ENNReal.mul_le_mul_iff_left hV0 hVt).1 key`. Rewrite `key2` using `[← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_le_ofReal_iff (pow_nonneg (by linarith) n)]`. Establish `hfin : (R + δ / 2) ^ n ≤ (3 * R / δ) ^ n * (δ / 2) ^ n`. Rewrite using `[← mul_pow]`. Apply `pow_le_pow_left₀ (by linarith)` to reduce the goal to its premises.

Establish `e : 3 * R / δ * (δ / 2) = 3 * R / 2`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `le_of_mul_le_mul_right (key2.trans hfin) (pow_pos hd2 n)`.
-/
theorem packingCount : PackingCount := by
  intro n P δ R hδ hδR hR hsep
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [pow_zero]
    have : P.card ≤ 1 := Finset.card_le_one.2 (fun a _ b _ => PiLp.ext (fun i => Fin.elim0 i))
    exact_mod_cast this
  · haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hn)
    classical
    have hd2 : 0 < δ / 2 := by linarith
    have hV0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 :=
      (Metric.measure_ball_pos volume _ one_pos).ne'
    have hVt : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ := measure_ball_lt_top.ne
    have hball : ∀ (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 ≤ ρ →
        volume (Metric.ball x ρ) = ENNReal.ofReal (ρ ^ n) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      intro x ρ hρ
      rw [Measure.addHaar_ball _ _ hρ, finrank_euclideanSpace_fin]
    have hdisj : Set.PairwiseDisjoint (↑P : Set (EuclideanSpace ℝ (Fin n))) (fun x => Metric.ball x (δ / 2)) := by
      intro x hx y hy hxy
      exact Metric.ball_disjoint_ball (by linarith [hsep x hx y hy hxy])
    have hsub : (⋃ x ∈ P, Metric.ball x (δ / 2)) ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + δ / 2) := by
      intro z hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨x, hx, hz⟩ := hz
      rw [Metric.mem_ball, dist_zero_right]
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have := norm_le_norm_add_norm_sub' z x
      linarith [hR x hx]
    have hmeas : volume (⋃ x ∈ P, Metric.ball x (δ / 2)) = ∑ x ∈ P, volume (Metric.ball x (δ / 2)) :=
      measure_biUnion_finset hdisj (fun x _ => measurableSet_ball)
    have key : ∑ x ∈ P, volume (Metric.ball x (δ / 2))
        ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + δ / 2)) := by
      rw [← hmeas]
      exact measure_mono hsub
    simp only [hball _ _ hd2.le, hball _ _ (by linarith : (0:ℝ) ≤ R + δ / 2), Finset.sum_const,
      nsmul_eq_mul] at key
    rw [← mul_assoc] at key
    have key2 := (ENNReal.mul_le_mul_iff_left hV0 hVt).1 key
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_le_ofReal_iff (pow_nonneg (by linarith) n)] at key2
    have hfin : (R + δ / 2) ^ n ≤ (3 * R / δ) ^ n * (δ / 2) ^ n := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by linarith)
      have e : 3 * R / δ * (δ / 2) = 3 * R / 2 := by
        field_simp
      rw [e]
      linarith
    exact le_of_mul_le_mul_right (key2.trans hfin) (pow_pos hd2 n)

end Formalism.LatticeBaseChangeAlt
