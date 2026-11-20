import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

/- English proof (translation)
Simplify using `[actM, add_smul, Finset.sum_add_distrib]`.
-/
theorem actM_add' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (X Y : Matrix (Fin n) (Fin n) ℂ) : actM E (X + Y) = actM E X + actM E Y := by
  simp [actM, add_smul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[actM, Finset.smul_sum, mul_smul]`.
-/
theorem actM_smul' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : actM E (c • X) = c • actM E X := by
  simp [actM, Finset.smul_sum, mul_smul]

/- English proof (translation)
Unfold `IsURepOn at hσ`. Set `L : H →ₗᵢ[ℂ] H` to `{ toLinearMap := (σ g).toLinearMap, norm_map' := hσ.2.1 g hg }`. Conclude with `L.inner_map_map x y`.
-/
theorem inner_map_map_of_isURep (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (x y : H) : inner ℂ (σ g x) (σ g y) = inner ℂ x y := by
  unfold IsURepOn at hσ
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g).toLinearMap, norm_map' := hσ.2.1 g hg }
  exact L.inner_map_map x y

/- English proof (translation)
Establish `hσ'` using `hσ`. Unfold `IsURepOn at hσ'`. Take `⟨-, -, hder⟩` from `hD`. Establish `hd` using `(hder X hX v).inner ℂ (hder X hX w)`. Establish `hc : HasDerivAt (fun t : ℝ => inner ℂ ((σ (NormedSpace.exp ((t : ℂ) • X))) (v : H)) ((σ (NormedSpace.exp ((t : ℂ) • X))) (w : H))) 0 0`.

Establish `e : (fun t : ℝ => inner ℂ ((σ (NormedSpace.exp ((t : ℂ) • X))) (v : H)) ((σ (NormedSpace.exp ((t : ℂ) • X))) (w : H))) = fun _ => inner ℂ (v : H) (w : H)`. Use function extensionality and compare the values at `t`. Conclude with `inner_map_map_of_isURep hσ (exp_smul_mem_UJset hX t) _ _`. Rewrite using `[e]`. Conclude with `hasDerivAt_const _ _`.

Establish `h0` using `hd.unique hc`. Simplify using `[hσ'.1.1] at h0`. Use `first`. Consider the case `(rw [Submodule.coe_inner, Submodule.coe_inner]; linear_combination h0)`. Consider the case `(simpa [add_comm] using h0)`.
-/
theorem inner_actM_add_inner_actM (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v w : D) :
    inner ℂ (actM E X v) w + inner ℂ v (actM E X w) = 0 := by
  have hσ' := hσ
  unfold IsURepOn at hσ'
  obtain ⟨-, -, hder⟩ := hD
  have hd := (hder X hX v).inner ℂ (hder X hX w)
  have hc : HasDerivAt (fun t : ℝ => inner ℂ ((σ (NormedSpace.exp ((t : ℂ) • X))) (v : H))
      ((σ (NormedSpace.exp ((t : ℂ) • X))) (w : H))) 0 0 := by
    have e : (fun t : ℝ => inner ℂ ((σ (NormedSpace.exp ((t : ℂ) • X))) (v : H))
        ((σ (NormedSpace.exp ((t : ℂ) • X))) (w : H))) = fun _ => inner ℂ (v : H) (w : H) := by
      funext t
      exact inner_map_map_of_isURep hσ (exp_smul_mem_UJset hX t) _ _
    rw [e]
    exact hasDerivAt_const _ _
  have h0 := hd.unique hc
  simp [hσ'.1.1] at h0
  first
    | (rw [Submodule.coe_inner, Submodule.coe_inner]; linear_combination h0)
    | (simpa [add_comm] using h0)

/- English proof (translation)
Simplify using `[actM, Matrix.single_apply, ite_smul]`. Rewrite using `[Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem actM_single' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (a b : Fin n) : actM E (Matrix.single a b 1) = E a b := by
  simp [actM, Matrix.single_apply, ite_smul]
  rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `simp [Jm, Matrix.diagonal_apply, Matrix.conjTranspose_apply] <;> split_ifs <;> simp_all`.
-/
theorem Jm_conjTranspose (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  ext i j
  simp [Jm, Matrix.diagonal_apply, Matrix.conjTranspose_apply] <;> split_ifs <;> simp_all

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `simp [Jm, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp_all`.
-/
theorem Jm_mul_Jm (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  ext i j
  simp [Jm, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp_all

/- English proof (translation)
Rewrite using `[← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]`.
-/
theorem Jm_mul_Jm_mul (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Jm ε * (Jm ε * X) = X := by
  rw [← Matrix.mul_assoc, Jm_mul_Jm, Matrix.one_mul]

/- English proof (translation)
Unfold `inG`. Apply the tactic sequence `simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Jm_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, Jm_mul_Jm, Jm_mul_Jm_mul, Matrix.mul_one] <;> abel`.
-/
theorem inG_sub_theta (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (M - Jm ε * Mᴴ * Jm ε) := by
  unfold inG
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Jm_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, Jm_mul_Jm,
    Jm_mul_Jm_mul, Matrix.mul_one] <;> abel

/- English proof (translation)
Unfold `inG`. Establish `hs : star (-Complex.I) = Complex.I` using `by simp`. Simplify using `only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Jm_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Jm_mul_Jm, Jm_mul_Jm_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul]`. Rewrite using `[hs, neg_smul, smul_add, smul_add]`. Normalize the expressions using the abelian group laws.
-/
theorem inG_add_theta (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    inG ε ((-Complex.I) • (M + Jm ε * Mᴴ * Jm ε)) := by
  unfold inG
  have hs : star (-Complex.I) = Complex.I := by simp
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Jm_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, Jm_mul_Jm, Jm_mul_Jm_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul]
  rw [hs, neg_smul, smul_add, smul_add]
  abel

/- English proof (translation)
Establish `skA` using `inner_actM_add_inner_actM hσ hD (inG_sub_theta ε M) x y`. Establish `skB` using `inner_actM_add_inner_actM hσ hD (inG_add_theta ε M) x y`. Establish `hc : Complex.I / 2 * -Complex.I = 1 / 2`. Rewrite using `[div_mul_eq_mul_div, mul_neg, Complex.I_mul_I]`. Evaluate the numerical expressions.

Establish `hM : M = (1 / 2 : ℂ) • (M - Jm ε * Mᴴ * Jm ε) + (Complex.I / 2) • ((-Complex.I) • (M + Jm ε * Mᴴ * Jm ε))`. Rewrite using `[smul_smul, hc]`. Use `first`. Consider the case `module`. Consider the case `(ext i j; simp; ring)`.

Establish `hT : Jm ε * Mᴴ * Jm ε = (-(1 / 2) : ℂ) • (M - Jm ε * Mᴴ * Jm ε) + (Complex.I / 2) • ((-Complex.I) • (M + Jm ε * Mᴴ * Jm ε))`. Rewrite using `[smul_smul, hc]`. Use `first`. Consider the case `module`. Consider the case `(ext i j; simp; ring)`.

Rewrite using `[hT]`. Use `conv_lhs => rw [hM]`. Rewrite using `[actM_add', actM_add', actM_smul' E (1 / 2 : ℂ), actM_smul' E (-(1 / 2) : ℂ), actM_smul' E (Complex.I / 2)]`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, map_div₀, map_one, map_ofNat, Complex.conj_I]`. Take the linear combination `(1 / 2 : ℂ) * skA - (Complex.I / 2) * skB`.
-/
theorem inner_actM_eq (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (M : Matrix (Fin n) (Fin n) ℂ) (x y : D) :
    inner ℂ (actM E M x) y = inner ℂ x (actM E (Jm ε * Mᴴ * Jm ε) y) := by
  have skA := inner_actM_add_inner_actM hσ hD (inG_sub_theta ε M) x y
  have skB := inner_actM_add_inner_actM hσ hD (inG_add_theta ε M) x y
  have hc : Complex.I / 2 * -Complex.I = 1 / 2 := by
    rw [div_mul_eq_mul_div, mul_neg, Complex.I_mul_I]
    norm_num
  have hM : M = (1 / 2 : ℂ) • (M - Jm ε * Mᴴ * Jm ε) +
      (Complex.I / 2) • ((-Complex.I) • (M + Jm ε * Mᴴ * Jm ε)) := by
    rw [smul_smul, hc]
    first
      | module
      | (ext i j; simp; ring)
  have hT : Jm ε * Mᴴ * Jm ε = (-(1 / 2) : ℂ) • (M - Jm ε * Mᴴ * Jm ε) +
      (Complex.I / 2) • ((-Complex.I) • (M + Jm ε * Mᴴ * Jm ε)) := by
    rw [smul_smul, hc]
    first
      | module
      | (ext i j; simp; ring)
  rw [hT]
  conv_lhs => rw [hM]
  rw [actM_add', actM_add', actM_smul' E (1 / 2 : ℂ), actM_smul' E (-(1 / 2) : ℂ),
    actM_smul' E (Complex.I / 2)]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, map_div₀, map_one, map_ofNat, Complex.conj_I]
  linear_combination (1 / 2 : ℂ) * skA - (Complex.I / 2) * skB

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `simp [Jm, adjSign, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply, Matrix.conjTranspose_apply, Matrix.smul_apply] <;> split_ifs <;> simp_all`.
-/
theorem theta_single (ε : Fin n → Bool) (a b : Fin n) :
    Jm ε * (Matrix.single a b (1 : ℂ))ᴴ * Jm ε = adjSign ε a b • Matrix.single b a 1 := by
  ext i j
  simp [Jm, adjSign, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply,
    Matrix.conjTranspose_apply, Matrix.smul_apply] <;> split_ifs <;> simp_all

/- English proof (translation)
Unfold `IsInfUnitary`. Introduce `a b v w`. Rewrite using `[← actM_single' E a b, inner_actM_eq hσ hD, theta_single, actM_smul', actM_single']`. Rewrite using `[LinearMap.smul_apply, inner_smul_right]`.
-/
theorem isInfUnitary_of_isDerivedOn (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) :
    IsInfUnitary ε E := by
  unfold IsInfUnitary
  intro a b v w
  rw [← actM_single' E a b, inner_actM_eq hσ hD, theta_single, actM_smul', actM_single']
  rw [LinearMap.smul_apply, inner_smul_right]

end Rep

end ReciprocityTheory.ChartRestriction.DS
