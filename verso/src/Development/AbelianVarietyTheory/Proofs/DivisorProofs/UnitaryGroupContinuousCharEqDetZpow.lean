import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CircleHomEqZpow
open Matrix

namespace GlobalTheory.UnitaryChar

variable {n : ℕ}

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨z, hz1, hz⟩ : ∃ z : ℂ, ‖z‖ = 1 ∧ z ∉ spectrum ℂ (u : Matrix (Fin n) (Fin n) ℂ) := by`. Establish `hfin` using `Matrix.finite_spectrum (u : Matrix (Fin n) (Fin n) ℂ)`. Establish `hinf : (Metric.sphere (0 : ℂ) 1).Infinite`. Establish `hc : IsConnected (Metric.sphere (0 : ℂ) 1)` using `isConnected_sphere (by simp) 0 zero_le_one`. Use `hc.isPreconnected.infinite_of_nontrivial ⟨1, by simp, -1, by simp, by norm_num⟩` and prove the remaining obligations.

Take `⟨z, h1, h2⟩` from `hinf.exists_notMem_finite hfin`. Conclude with `⟨z, by simpa using h1, h2⟩`. Establish `hzz : star z * z = 1`. Rewrite using `[mul_comm]`. Simplify using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hz1]`.

Use `set U : Matrix (Fin n) (Fin n) ℂ := (u : Matrix (Fin n) (Fin n) ℂ) with hU`. Establish `hUU : star U * U = 1` using `u.2.1`. Establish `hA : IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) - U)`. Use `spectrum.notMem_iff.1 hz` as an intermediate fact. Rewrite `this` using `[Algebra.algebraMap_eq_smul_one]`. Then use the resulting hypothesis.

Take `⟨B, hAB, hBA⟩ : ∃ B : Matrix (Fin n) (Fin n) ℂ, (z • 1 - U) * B = 1 ∧ B * (z • 1 - U) = 1` from `isUnit_iff_exists.1 hA`. Establish `hBA' : star B * (star z • 1 - star U) = 1`. Use `congrArg star hAB` as an intermediate fact. Simplify `this` using `[star_mul, star_smul]`. Establish `key : z • B + star z • star B = 1`.

Establish `h1 : (star z • 1 - star U) * (z • 1 - U) = z • (star z • 1 - star U) + star z • (z • (1 : Matrix (Fin n) (Fin n) ℂ) - U)`. Simplify using `only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hUU, smul_sub, smul_smul, hzz, mul_comm z (star z), one_smul]`. Normalize the expressions using the abelian group laws. Establish `h2 : star B * ((star z • 1 - star U) * (z • 1 - U)) * B = 1`. Rewrite using `[← mul_assoc, hBA', one_mul, hAB]`.

Rewrite `h2` using `[h1, mul_add, add_mul, mul_smul_comm, hBA', mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_assoc, hAB, one_mul, mul_one]`. Conclude with `h2`. Establish `hH : (Complex.I • (z • B - (1 / 2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))).IsHermitian`. Establish `h3 : star z • star B = 1 - z • B` using `by rw [← key]; abel`. Express the relevant statement in the definitionally equal form `star _ = _`.

Rewrite using `[star_smul, star_sub, star_smul, h3, star_smul]`. Simplify using `only [star_one, RCLike.star_def, Complex.conj_I, map_div₀, map_one, map_ofNat]`. Use `module`. Establish `hs` using `hH.conjStarAlgAut_star_eigenvectorUnitary`. Use `set V := hH.eigenvectorUnitary`.

Generalize the expression as in `(RCLike.ofReal ∘ hH.eigenvalues : Fin n → ℂ) = e at hs`. Rewrite `hs` using `[Unitary.conjStarAlgAut_star_apply]`. Use `set W : Matrix (Fin n) (Fin n) ℂ := (V : Matrix (Fin n) (Fin n) ℂ) with hW`. Establish `hWW : star W * W = 1` using `V.2.1`. Establish `hWW' : W * star W = 1` using `V.2.2`.

Establish `hz0 : z ≠ 0` using `by rintro rfl; simp at hz1`. Establish `hB : star W * B * W = diagonal (fun i => z⁻¹ * (-Complex.I * e i + 1 / 2))`. Establish `h4 : diagonal (fun i => z⁻¹ * (-Complex.I * e i + 1 / 2)) = z⁻¹ • ((-Complex.I) • diagonal e + (1 / 2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))`. Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [diagonal_apply, one_apply, h]`.

Rewrite using `[h4, ← hs]`. Simplify using `only [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one, hWW, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, sub_add_cancel, inv_mul_cancel₀ hz0]`. Generalize the expression as in `(fun i => z⁻¹ * (-Complex.I * e i + 1 / 2)) = b at hB`. Establish `h5 : (z • 1 - star W * U * W) * diagonal b = 1`. Establish `h6 : z • 1 - star W * U * W = star W * (z • 1 - U) * W`.

Simplify using `only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, hWW]`. Rewrite using `[h6, ← hB]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨V, fun i => (star W * U * W) i i, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `star W * U * W = _`.

Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `h7` using `congrFun (congrFun h5 i) j`.

Establish `h8` using `congrFun (congrFun h5 j) j`. Rewrite `h7`, `h8` using `[mul_diagonal]`. Rewrite `h8` using `[one_apply_eq]`. Establish `hb : b j ≠ 0` using `right_ne_zero_of_mul_eq_one h8`. Rewrite `h7` using `[one_apply_ne h, mul_eq_zero]`.

Rewrite using `[diagonal_apply_ne _ h]`. Simplify `h7.resolve_right hb` using `[one_apply_ne h]`.
-/
theorem exists_conj_diagonal (u : Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ (V : Matrix.unitaryGroup (Fin n) ℂ) (d : Fin n → ℂ),
      ((V⁻¹ * u * V : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = diagonal d := by
  obtain ⟨z, hz1, hz⟩ : ∃ z : ℂ, ‖z‖ = 1 ∧ z ∉ spectrum ℂ (u : Matrix (Fin n) (Fin n) ℂ) := by
    have hfin := Matrix.finite_spectrum (u : Matrix (Fin n) (Fin n) ℂ)
    have hinf : (Metric.sphere (0 : ℂ) 1).Infinite := by
      have hc : IsConnected (Metric.sphere (0 : ℂ) 1) :=
        isConnected_sphere (by simp) 0 zero_le_one
      refine hc.isPreconnected.infinite_of_nontrivial ⟨1, by simp, -1, by simp, by norm_num⟩
    obtain ⟨z, h1, h2⟩ := hinf.exists_notMem_finite hfin
    exact ⟨z, by simpa using h1, h2⟩
  have hzz : star z * z = 1 := by
    rw [mul_comm]; simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz1]
  set U : Matrix (Fin n) (Fin n) ℂ := (u : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : star U * U = 1 := u.2.1
  have hA : IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) - U) := by
    have := spectrum.notMem_iff.1 hz
    rwa [Algebra.algebraMap_eq_smul_one] at this
  obtain ⟨B, hAB, hBA⟩ : ∃ B : Matrix (Fin n) (Fin n) ℂ, (z • 1 - U) * B = 1 ∧ B * (z • 1 - U) = 1 :=
    isUnit_iff_exists.1 hA
  have hBA' : star B * (star z • 1 - star U) = 1 := by
    have := congrArg star hAB
    simpa [star_mul, star_smul] using this
  have key : z • B + star z • star B = 1 := by
    have h1 : (star z • 1 - star U) * (z • 1 - U) =
        z • (star z • 1 - star U) + star z • (z • (1 : Matrix (Fin n) (Fin n) ℂ) - U) := by
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hUU, smul_sub,
        smul_smul, hzz, mul_comm z (star z), one_smul]
      abel
    have h2 : star B * ((star z • 1 - star U) * (z • 1 - U)) * B = 1 := by
      rw [← mul_assoc, hBA', one_mul, hAB]
    rw [h1, mul_add, add_mul, mul_smul_comm, hBA', mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
      mul_assoc, hAB, one_mul, mul_one] at h2
    exact h2
  have hH : (Complex.I • (z • B - (1 / 2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))).IsHermitian := by
    have h3 : star z • star B = 1 - z • B := by rw [← key]; abel
    change star _ = _
    rw [star_smul, star_sub, star_smul, h3, star_smul]
    simp only [star_one, RCLike.star_def, Complex.conj_I, map_div₀, map_one, map_ofNat]
    module
  have hs := hH.conjStarAlgAut_star_eigenvectorUnitary
  set V := hH.eigenvectorUnitary
  generalize (RCLike.ofReal ∘ hH.eigenvalues : Fin n → ℂ) = e at hs
  rw [Unitary.conjStarAlgAut_star_apply] at hs
  set W : Matrix (Fin n) (Fin n) ℂ := (V : Matrix (Fin n) (Fin n) ℂ) with hW
  have hWW : star W * W = 1 := V.2.1
  have hWW' : W * star W = 1 := V.2.2
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz1
  have hB : star W * B * W = diagonal (fun i => z⁻¹ * (-Complex.I * e i + 1 / 2)) := by
    have h4 : diagonal (fun i => z⁻¹ * (-Complex.I * e i + 1 / 2)) =
        z⁻¹ • ((-Complex.I) • diagonal e + (1 / 2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
      ext i j
      by_cases h : i = j <;> simp [diagonal_apply, one_apply, h]
    rw [h4, ← hs]
    simp only [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one, hWW, smul_smul, neg_mul,
      Complex.I_mul_I, neg_neg, one_smul, sub_add_cancel, inv_mul_cancel₀ hz0]
  generalize (fun i => z⁻¹ * (-Complex.I * e i + 1 / 2)) = b at hB
  have h5 : (z • 1 - star W * U * W) * diagonal b = 1 := by
    have h6 : z • 1 - star W * U * W = star W * (z • 1 - U) * W := by
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, hWW]
    rw [h6, ← hB]
    calc star W * (z • 1 - U) * W * (star W * B * W)
        = star W * ((z • 1 - U) * (W * star W) * B) * W := by simp only [mul_assoc]
      _ = 1 := by rw [hWW', mul_one, hAB, mul_one, hWW]
  refine ⟨V, fun i => (star W * U * W) i i, ?_⟩
  change star W * U * W = _
  ext i j
  by_cases h : i = j
  · subst h; simp
  · have h7 := congrFun (congrFun h5 i) j
    have h8 := congrFun (congrFun h5 j) j
    rw [mul_diagonal] at h7 h8
    rw [one_apply_eq] at h8
    have hb : b j ≠ 0 := right_ne_zero_of_mul_eq_one h8
    rw [one_apply_ne h, mul_eq_zero] at h7
    rw [diagonal_apply_ne _ h]
    simpa [one_apply_ne h] using h7.resolve_right hb

noncomputable def diagHom (n : ℕ) : (Fin n → Circle) →* Matrix.unitaryGroup (Fin n) ℂ where
  toFun t := ⟨diagonal fun i => (t i : ℂ), by
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    simp [Complex.mul_conj]⟩
  map_one' := by ext i j; simp
  map_mul' s t := by
    apply Subtype.ext
    simp [diagonal_mul_diagonal]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_diagHom (t : Fin n → Circle) :
    (diagHom n t : Matrix (Fin n) (Fin n) ℂ) = diagonal fun i => (t i : ℂ) := rfl

/- English proof (translation)
Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations. Conclude with `Continuous.matrix_diagonal (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i))`.
-/
theorem continuous_diagHom : Continuous (diagHom n) := by
  refine Continuous.subtype_mk ?_ _
  exact Continuous.matrix_diagonal (continuous_pi fun i =>
    continuous_subtype_val.comp (continuous_apply i))

/- English proof (translation)
Take `⟨V, d, h⟩` from `exists_conj_diagonal u`. Establish `h1` using `(V⁻¹ * u * V).2.2`. Rewrite `h1` using `[h, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal]`. Establish `h2 : ∀ i, ‖d i‖ = 1` using `fun i => by`. Use `congrFun (congrFun h1 i) i` as an intermediate fact.

Simplify using `only [diagonal_apply_eq, one_apply_eq, Pi.star_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq] at this`. Establish `h3 : ‖d i‖ ^ 2 = 1` using `by exact_mod_cast this`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3`. Conclude with `⟨V, fun i => ⟨d i, by simpa [Submonoid.unitSphere] using h2 i⟩, Subtype.ext h⟩`.
-/
theorem exists_conj_diagHom (u : Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ (V : Matrix.unitaryGroup (Fin n) ℂ) (t : Fin n → Circle), V⁻¹ * u * V = diagHom n t := by
  obtain ⟨V, d, h⟩ := exists_conj_diagonal u
  have h1 := (V⁻¹ * u * V).2.2
  rw [h, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal] at h1
  have h2 : ∀ i, ‖d i‖ = 1 := fun i => by
    have := congrFun (congrFun h1 i) i
    simp only [diagonal_apply_eq, one_apply_eq, Pi.star_apply, RCLike.star_def,
      Complex.mul_conj, Complex.normSq_eq_norm_sq] at this
    have h3 : ‖d i‖ ^ 2 = 1 := by exact_mod_cast this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3
  exact ⟨V, fun i => ⟨d i, by simpa [Submonoid.unitSphere] using h2 i⟩, Subtype.ext h⟩

/- English proof (translation)
Use `⟨⟨σ.permMatrix ℂ, ?_⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_permMatrix, ← permMatrix_mul]`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `σ.permMatrix ℂ * diagonal _ = diagonal _ * σ.permMatrix ℂ`. Use extensionality with `i j`.

Rewrite using `[mul_diagonal, diagonal_mul]`. Distinguish the cases in `h : σ i = j`. Simplify using `[Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h]`. Simplify using `[Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h]`.
-/
theorem exists_conj_perm (σ : Equiv.Perm (Fin n)) (t : Fin n → Circle) :
    ∃ P : Matrix.unitaryGroup (Fin n) ℂ, P * diagHom n t = diagHom n (t ∘ σ) * P := by
  refine ⟨⟨σ.permMatrix ℂ, ?_⟩, Subtype.ext ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_permMatrix,
      ← permMatrix_mul]
    simp
  · change σ.permMatrix ℂ * diagonal _ = diagonal _ * σ.permMatrix ℂ
    ext i j
    rw [mul_diagonal, diagonal_mul]
    by_cases h : σ i = j
    · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h]
    · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h]

/- English proof (translation)
Introduce `n c hc`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Use `⟨0, fun u => ?_⟩` and prove the remaining obligations. Establish `: u = 1` using `Subtype.ext (Subsingleton.elim _ _)`. Simplify using `[this]`.

Use `set i₀ : Fin n := ⟨0, hn⟩`. Take `⟨m, hm⟩` from `GlobalTheory.circle_hom_eq_zpow (c.comp ((diagHom n).comp (MonoidHom.mulSingle (fun _ : Fin n => Circle) i₀))) (hc.comp (continuous_diagHom.comp (continuous_mulSingle (A := fun _ : Fin n => Circle) i₀)))`. Establish `hi : ∀ i z, c (diagHom n (Pi.mulSingle i z)) = z ^ m` using `fun i z => by`. Take `⟨P, hP⟩` from `exists_conj_perm (Equiv.swap i₀ i) (Pi.mulSingle i₀ z)`. Establish `h1 : (Pi.mulSingle i₀ z : Fin n → Circle) ∘ (Equiv.swap i₀ i) = Pi.mulSingle i z`.

Use extensionality with `j`. Simplify using `only [Function.comp_apply, Pi.mulSingle_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]`. Establish `h2` using `congrArg c hP`. Rewrite `h2` using `[h1, map_mul, map_mul, mul_comm]`. Rewrite using `[← mul_right_cancel h2]`.

Conclude with `hm z`. Use `⟨m, fun u => ?_⟩` and prove the remaining obligations. Take `⟨V, t, h⟩` from `exists_conj_diagHom u`. Establish `h1 : c u = c (diagHom n t)`. Rewrite using `[← h, map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]`.

Establish `h2 : (u : Matrix (Fin n) (Fin n) ℂ).det = ∏ i, (t i : ℂ)`. Rewrite using `[← det_diagonal, ← coe_diagHom, ← h]`. Establish `h3 : (V : Matrix (Fin n) (Fin n) ℂ) * star (V : Matrix (Fin n) (Fin n) ℂ) = 1` using `V.2.2`. Express the relevant statement in the definitionally equal form `_ = (star (V : Matrix (Fin n) (Fin n) ℂ) * u * V).det`. Rewrite using `[det_mul_comm, ← mul_assoc, h3, one_mul]`.

Establish `h4 : c (diagHom n t) = (∏ i, t i) ^ m`. Establish `h5` using `map_prod (c.comp (diagHom n)) (fun i => Pi.mulSingle i (t i)) Finset.univ`. Rewrite `h5` using `[Finset.univ_prod_mulSingle]`. Simplify using `only [MonoidHom.comp_apply, hi] at h5`. Rewrite using `[h5, Finset.prod_zpow]`.

Rewrite using `[h1, h2, h4, Circle.coe_zpow]`. Use `congr 1`. Conclude with `map_prod Circle.coeHom _ _`.
-/
theorem char_eq_det_zpow : ∀ (n : ℕ) (c : Matrix.unitaryGroup (Fin n) ℂ →* Circle), Continuous c → ∃ m : ℤ, ∀ u : Matrix.unitaryGroup (Fin n) ℂ, ((c u : Circle) : ℂ) = (Matrix.det (u : Matrix (Fin n) (Fin n) ℂ)) ^ m := by
  intro n c hc
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, fun u => ?_⟩
    have : u = 1 := Subtype.ext (Subsingleton.elim _ _)
    simp [this]
  set i₀ : Fin n := ⟨0, hn⟩
  obtain ⟨m, hm⟩ := GlobalTheory.circle_hom_eq_zpow
    (c.comp ((diagHom n).comp (MonoidHom.mulSingle (fun _ : Fin n => Circle) i₀)))
    (hc.comp (continuous_diagHom.comp (continuous_mulSingle (A := fun _ : Fin n => Circle) i₀)))
  have hi : ∀ i z, c (diagHom n (Pi.mulSingle i z)) = z ^ m := fun i z => by
    obtain ⟨P, hP⟩ := exists_conj_perm (Equiv.swap i₀ i) (Pi.mulSingle i₀ z)
    have h1 : (Pi.mulSingle i₀ z : Fin n → Circle) ∘ (Equiv.swap i₀ i) = Pi.mulSingle i z := by
      ext j
      simp only [Function.comp_apply, Pi.mulSingle_apply, Equiv.swap_apply_eq_iff,
        Equiv.swap_apply_left]
    have h2 := congrArg c hP
    rw [h1, map_mul, map_mul, mul_comm] at h2
    rw [← mul_right_cancel h2]
    exact hm z
  refine ⟨m, fun u => ?_⟩
  obtain ⟨V, t, h⟩ := exists_conj_diagHom u
  have h1 : c u = c (diagHom n t) := by
    rw [← h, map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  have h2 : (u : Matrix (Fin n) (Fin n) ℂ).det = ∏ i, (t i : ℂ) := by
    rw [← det_diagonal, ← coe_diagHom, ← h]
    have h3 : (V : Matrix (Fin n) (Fin n) ℂ) * star (V : Matrix (Fin n) (Fin n) ℂ) = 1 := V.2.2
    change _ = (star (V : Matrix (Fin n) (Fin n) ℂ) * u * V).det
    rw [det_mul_comm, ← mul_assoc, h3, one_mul]
  have h4 : c (diagHom n t) = (∏ i, t i) ^ m := by
    have h5 := map_prod (c.comp (diagHom n)) (fun i => Pi.mulSingle i (t i)) Finset.univ
    rw [Finset.univ_prod_mulSingle] at h5
    simp only [MonoidHom.comp_apply, hi] at h5
    rw [h5, Finset.prod_zpow]
  rw [h1, h2, h4, Circle.coe_zpow]
  congr 1
  exact map_prod Circle.coeHom _ _

end GlobalTheory.UnitaryChar
