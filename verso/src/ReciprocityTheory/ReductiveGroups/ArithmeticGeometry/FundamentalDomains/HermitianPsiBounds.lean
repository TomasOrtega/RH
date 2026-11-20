import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CompactEntryBounds

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace HermitianPsiBounds

open Matrix NumberField Complex QuadraticLatticeForms
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

noncomputable def Cinv : ℝ := ∑ τ : X.Ψ, 1 / X.c τ

/- English proof (translation)
Unfold `Cinv`. Conclude with `Finset.single_le_sum (f := fun τ => 1 / X.c τ) (fun τ' _ => by unfold Data.c; positivity) (Finset.mem_univ τ)`.
-/
theorem inv_c_le (τ : X.Ψ) : 1 / X.c τ ≤ Cinv X := by
  unfold Cinv
  exact Finset.single_le_sum (f := fun τ => 1 / X.c τ)
    (fun τ' _ => by unfold Data.c; positivity) (Finset.mem_univ τ)

/- English proof (translation)
Unfold `Cinv`. Conclude with `Finset.sum_nonneg fun τ _ => by unfold Data.c; positivity`.
-/
theorem Cinv_nonneg : 0 ≤ Cinv X := by
  unfold Cinv
  exact Finset.sum_nonneg fun τ _ => by unfold Data.c; positivity

/- English proof (translation)
Establish `hc : 0 < X.c τ`. Establish `h1 : τ.1 X.ξ0 ≠ 0` using `(map_ne_zero _).mpr X.ξ0_ne`. Use `norm_pos_iff.mpr h1` as an intermediate fact. Unfold `Data.c`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `key : ∀ s : ℝ, 0 ≤ s → X.c τ * s ≤ Qy X y p → s ≤ Qy X y p * Cinv X`. Introduce `s hs h1`. Establish `h2` using `inv_c_le X τ`. Establish `hQ : 0 ≤ Qy X y p` using `le_trans (mul_nonneg hc.le hs) h1`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_comm (X.c τ), mul_assoc, mul_one_div_cancel hc.ne', mul_one]`. Use `_ ≤ Qy X y p * Cinv X := mul_le_mul h1 h2 (by positivity) hQ`. Apply `key _ (Finset.sum_nonneg fun _ _ => by positivity)` to reduce the goal to its premises. Unfold `Qy`. Conclude with `Finset.single_le_sum (f := fun τ' => X.c τ' * ∑ a, ‖((y τ')⁻¹ *ᵥ Data.emb τ'.1 p) a‖ ^ 2) (fun τ' _ => mul_nonneg (by unfold Data.c; positivity) (Finset.sum_nonneg fun _ _ => by positivity)) (Finset.mem_univ τ)`.
-/
theorem sum_sq_le (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (τ : X.Ψ) (p : Fin r → E) :
    ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2 ≤ Qy X y p * Cinv X := by
  have hc : 0 < X.c τ := by
    have h1 : τ.1 X.ξ0 ≠ 0 := (map_ne_zero _).mpr X.ξ0_ne
    have := norm_pos_iff.mpr h1
    unfold Data.c
    linarith
  have key : ∀ s : ℝ, 0 ≤ s → X.c τ * s ≤ Qy X y p → s ≤ Qy X y p * Cinv X := by
    intro s hs h1
    have h2 := inv_c_le X τ
    have hQ : 0 ≤ Qy X y p := le_trans (mul_nonneg hc.le hs) h1
    calc s = (X.c τ * s) * (1 / X.c τ) := by
          rw [mul_comm (X.c τ), mul_assoc, mul_one_div_cancel hc.ne', mul_one]
      _ ≤ Qy X y p * Cinv X := mul_le_mul h1 h2 (by positivity) hQ
  apply key _ (Finset.sum_nonneg fun _ _ => by positivity)
  unfold Qy
  exact Finset.single_le_sum
    (f := fun τ' => X.c τ' * ∑ a, ‖((y τ')⁻¹ *ᵥ Data.emb τ'.1 p) a‖ ^ 2)
    (fun τ' _ => mul_nonneg (by unfold Data.c; positivity)
      (Finset.sum_nonneg fun _ _ => by positivity)) (Finset.mem_univ τ)

/- English proof (translation)
Take `⟨g, hg⟩ : ∃ g : Fin r → ℂ, ∀ u, hermC τ G u w = ∑ i, u i * g i` from `⟨fun i => ∑ k, τ (G i k) * conj (w k), fun u => by simp only [hermC, Finset.mul_sum, mul_assoc]⟩`. Simplify using `only [hg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring`.
-/
private lemma hermC_sum_left_lemma (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : Fin r → ℂ)
    (y : Fin r → Fin r → ℂ) (w : Fin r → ℂ) :
    hermC τ G (∑ b, c b • y b) w = ∑ b, c b * hermC τ G (y b) w := by
  obtain ⟨g, hg⟩ : ∃ g : Fin r → ℂ, ∀ u, hermC τ G u w = ∑ i, u i * g i :=
    ⟨fun i => ∑ k, τ (G i k) * conj (w k), fun u => by simp only [hermC, Finset.mul_sum, mul_assoc]⟩
  simp only [hg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Take `⟨g, hg⟩ : ∃ g : Fin r → ℂ, ∀ w, hermC τ G u w = ∑ k, g k * conj (w k)` from `⟨fun k => ∑ i, u i * τ (G i k), fun w => by simp only [hermC, Finset.sum_mul]; exact Finset.sum_comm⟩`. Simplify using `only [hg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring`.
-/
private lemma hermC_sum_right_lemma_2 (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u : Fin r → ℂ)
    (c : Fin r → ℂ) (y : Fin r → Fin r → ℂ) :
    hermC τ G u (∑ b, c b • y b) = ∑ b, conj (c b) * hermC τ G u (y b) := by
  obtain ⟨g, hg⟩ : ∃ g : Fin r → ℂ, ∀ w, hermC τ G u w = ∑ k, g k * conj (w k) :=
    ⟨fun k => ∑ i, u i * τ (G i k), fun w => by simp only [hermC, Finset.sum_mul]; exact Finset.sum_comm⟩
  simp only [hg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Take `⟨hdet, hg⟩` from `hy τ`. Establish `hu : IsUnit (y τ).det` using `isUnit_iff_ne_zero.mpr hdet`. Establish `hyinv : ∀ u : Fin r → ℂ, y τ *ᵥ ((y τ)⁻¹ *ᵥ u) = u` using `fun u => by`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]`. Establish `hcols : ∀ γ : Fin r → ℂ, y τ *ᵥ γ = ∑ k, γ k • col (y τ) k` using `fun γ => by`.

Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, col, Finset.sum_apply, mul_comm]`. Establish `hgl : ∀ k l, hermC τ.1 X.Gm (col (y τ) k) (col (y τ) l) = if k = l then ((sgn X.p0 (k : ℕ) : ℝ) : ℂ) else 0` using `fun k l => by`. Establish `h` using `congrFun (congrFun hg k) l`. Simplify `h` using `[gram, Matrix.diagonal_apply]`.

Establish `hSp` using `sum_sq_le X y τ p`. Establish `hSq` using `sum_sq_le X y τ q`. Rewrite using `[← hermC_emb, ← hyinv (Data.emb τ.1 p), ← hyinv (Data.emb τ.1 q), hcols, hcols, hermC_sum_left_lemma]`. Simplify using `only [hermC_sum_right_lemma_2, hgl, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Use `set A := (y τ)⁻¹ *ᵥ Data.emb τ.1 p with hA`.

Use `set B := (y τ)⁻¹ *ᵥ Data.emb τ.1 q with hB`. Establish `hterm : ∀ k, ‖A k * (conj (B k) * ((sgn X.p0 (k : ℕ) : ℝ) : ℂ))‖ ≤ ‖A k‖ ^ 2 + ‖B k‖ ^ 2`. Introduce `k`. Establish `hε : ‖((sgn X.p0 (k : ℕ) : ℝ) : ℂ)‖ = 1`. Unfold `sgn`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[norm_mul, norm_mul, Complex.norm_conj, hε, mul_one]`. Use polynomial arithmetic with `[sq_nonneg (‖A k‖ - ‖B k‖), norm_nonneg (A k), norm_nonneg (B k)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem herm_bound_psi {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IntegralBasisReduction.IsNormal X y) (τ : X.Ψ)
    (p q : Fin r → E) : ‖τ.1 (herm X.Gm p q)‖ ≤ (Qy X y p + Qy X y q) * Cinv X := by
  obtain ⟨hdet, hg⟩ := hy τ
  have hu : IsUnit (y τ).det := isUnit_iff_ne_zero.mpr hdet
  have hyinv : ∀ u : Fin r → ℂ, y τ *ᵥ ((y τ)⁻¹ *ᵥ u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have hcols : ∀ γ : Fin r → ℂ, y τ *ᵥ γ = ∑ k, γ k • col (y τ) k := fun γ => by
    ext i
    simp [Matrix.mulVec, dotProduct, col, Finset.sum_apply, mul_comm]
  have hgl : ∀ k l, hermC τ.1 X.Gm (col (y τ) k) (col (y τ) l) =
      if k = l then ((sgn X.p0 (k : ℕ) : ℝ) : ℂ) else 0 := fun k l => by
    have h := congrFun (congrFun hg k) l
    simpa [gram, Matrix.diagonal_apply] using h
  have hSp := sum_sq_le X y τ p
  have hSq := sum_sq_le X y τ q
  rw [← hermC_emb, ← hyinv (Data.emb τ.1 p), ← hyinv (Data.emb τ.1 q), hcols, hcols,
    hermC_sum_left_lemma]
  simp only [hermC_sum_right_lemma_2, hgl, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  set A := (y τ)⁻¹ *ᵥ Data.emb τ.1 p with hA
  set B := (y τ)⁻¹ *ᵥ Data.emb τ.1 q with hB
  have hterm : ∀ k, ‖A k * (conj (B k) * ((sgn X.p0 (k : ℕ) : ℝ) : ℂ))‖ ≤ ‖A k‖ ^ 2 + ‖B k‖ ^ 2 := by
    intro k
    have hε : ‖((sgn X.p0 (k : ℕ) : ℝ) : ℂ)‖ = 1 := by
      unfold sgn
      split_ifs <;> simp
    rw [norm_mul, norm_mul, Complex.norm_conj, hε, mul_one]
    nlinarith [sq_nonneg (‖A k‖ - ‖B k‖), norm_nonneg (A k), norm_nonneg (B k)]
  calc ‖∑ k, A k * (conj (B k) * ((sgn X.p0 (k : ℕ) : ℝ) : ℂ))‖
      ≤ ∑ k, ‖A k * (conj (B k) * ((sgn X.p0 (k : ℕ) : ℝ) : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ k, (‖A k‖ ^ 2 + ‖B k‖ ^ 2) := Finset.sum_le_sum fun k _ => hterm k
    _ = ∑ k, ‖A k‖ ^ 2 + ∑ k, ‖B k‖ ^ 2 := Finset.sum_add_distrib
    _ ≤ (Qy X y p + Qy X y q) * Cinv X := by nlinarith [hSp, hSq]

/- English proof (translation)
Distinguish the cases in `hσ : σ ∈ X.Ψ`. Conclude with `herm_bound_psi X hy ⟨σ, hσ⟩ p q`. Establish `hc : ComplexEmbedding.conjugate σ ∈ X.Ψ`. Rewrite using `[X.cmType]`. Use `first`.

Consider the case `(rw [show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ from star_star σ]`. Conclude with `hσ)`. Consider the case `simpa using hσ`. Establish `h` using `herm_bound_psi X hy ⟨_, hc⟩ p q`. Use `first`.

Consider the case `simpa [ComplexEmbedding.conjugate_coe_eq] using h`. Consider the case `(simp only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at h; exact h)`.
-/
theorem herm_bound {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IntegralBasisReduction.IsNormal X y) (σ : E →+* ℂ)
    (p q : Fin r → E) : ‖σ (herm X.Gm p q)‖ ≤ (Qy X y p + Qy X y q) * Cinv X := by
  by_cases hσ : σ ∈ X.Ψ
  · exact herm_bound_psi X hy ⟨σ, hσ⟩ p q
  · have hc : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
      rw [X.cmType]
      first
      | (rw [show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ from star_star σ]
         exact hσ)
      | simpa using hσ
    have h := herm_bound_psi X hy ⟨_, hc⟩ p q
    first
    | simpa [ComplexEmbedding.conjugate_coe_eq] using h
    | (simp only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at h; exact h)

/- English proof (translation)
Unfold `Qy`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun τ _ => ?_` and prove the remaining obligations. Establish `e : Data.emb τ.1 (α • p) = τ.1 α • Data.emb τ.1 p`. Use function extensionality and compare the values at `a`.

Simplify using `[Data.emb]`. Establish `e2 : ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 (α • p)) a‖ ^ 2 = ‖τ.1 α‖ ^ 2 * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2`. Rewrite using `[e, Matrix.mulVec_smul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]`.

Rewrite using `[e2]`. Establish `h1 : ‖τ.1 α‖ ^ 2 ≤ ∑ σ : X.Ψ, ‖σ.1 α‖ ^ 2` using `Finset.single_le_sum (f := fun σ : X.Ψ => ‖σ.1 α‖ ^ 2) (fun σ _ => by positivity) (Finset.mem_univ τ)`. Establish `h2 : 0 ≤ X.c τ * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2` using `mul_nonneg (c_pos X τ).le (Finset.sum_nonneg fun a _ => by positivity)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem Qy_smul (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (α : E) (p : Fin r → E) :
    Qy X y (α • p) ≤ (∑ τ : X.Ψ, ‖τ.1 α‖ ^ 2) * Qy X y p := by
  unfold Qy
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  have e : Data.emb τ.1 (α • p) = τ.1 α • Data.emb τ.1 p := by
    funext a; simp [Data.emb]
  have e2 : ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 (α • p)) a‖ ^ 2 =
      ‖τ.1 α‖ ^ 2 * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2 := by
    rw [e, Matrix.mulVec_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [e2]
  have h1 : ‖τ.1 α‖ ^ 2 ≤ ∑ σ : X.Ψ, ‖σ.1 α‖ ^ 2 :=
    Finset.single_le_sum (f := fun σ : X.Ψ => ‖σ.1 α‖ ^ 2) (fun σ _ => by positivity)
      (Finset.mem_univ τ)
  have h2 : 0 ≤ X.c τ * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2 :=
    mul_nonneg (c_pos X τ).le (Finset.sum_nonneg fun a _ => by positivity)
  calc X.c τ * (‖τ.1 α‖ ^ 2 * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2)
      = ‖τ.1 α‖ ^ 2 * (X.c τ * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2) := by ring
    _ ≤ (∑ σ : X.Ψ, ‖σ.1 α‖ ^ 2) * (X.c τ * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2) :=
      mul_le_mul_of_nonneg_right h1 h2

/- English proof (translation)
Establish `hQ : ∀ w : Fin r → E, ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 w) = Qy X y w`. Introduce `w`. Unfold `Qy`. Simplify using `only [hm]`. Establish `hnn : ∀ t ∈ {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)}, 0 ≤ t`.

Introduce and unpack `t ⟨w, -, -, rfl⟩`. Rewrite using `[hQ]`. Unfold `Qy`. Conclude with `Finset.sum_nonneg fun τ _ => mul_nonneg (by unfold Data.c; positivity) (Finset.sum_nonneg fun _ _ => by positivity)`. Establish `hmem : Qy X y v ∈ {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)}` using `⟨v, hv, hv0, (hQ v).symm⟩`.

Establish `h1 : X.firstMinimumSq x ≤ Qy X y v` using `csInf_le ⟨0, hnn⟩ hmem`. Establish `h0 : 0 ≤ X.firstMinimumSq x` using `Real.sInf_nonneg hnn`. Establish `h2 : ε ^ 2 ≤ X.la1 x ^ 2` using `by nlinarith`. Rewrite `h2` using `[Data.la1, Real.sq_sqrt h0]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sq_le_Qy_of_le_firstMinimum {x : Frame X.Ψ r} {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ}
    (hm : ∀ τ u, X.maj x τ u = ∑ a, ‖((y τ)⁻¹ *ᵥ u) a‖ ^ 2) {ε : ℝ} (hε : 0 < ε) (hl : ε ≤ X.la1 x)
    {v : Fin r → E} (hv : v ∈ X.Λ) (hv0 : v ≠ 0) : ε ^ 2 ≤ Qy X y v := by
  have hQ : ∀ w : Fin r → E, ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 w) = Qy X y w := by
    intro w
    unfold Qy
    simp only [hm]
  have hnn : ∀ t ∈ {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)}, 0 ≤ t := by
    rintro t ⟨w, -, -, rfl⟩
    rw [hQ]
    unfold Qy
    exact Finset.sum_nonneg fun τ _ => mul_nonneg (by unfold Data.c; positivity)
      (Finset.sum_nonneg fun _ _ => by positivity)
  have hmem : Qy X y v ∈ {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)} :=
    ⟨v, hv, hv0, (hQ v).symm⟩
  have h1 : X.firstMinimumSq x ≤ Qy X y v := csInf_le ⟨0, hnn⟩ hmem
  have h0 : 0 ≤ X.firstMinimumSq x := Real.sInf_nonneg hnn
  have h2 : ε ^ 2 ≤ X.la1 x ^ 2 := by nlinarith
  rw [Data.la1, Real.sq_sqrt h0] at h2
  linarith

end HermitianPsiBounds

end ReciprocityTheory.ChartRestriction.G.FD
