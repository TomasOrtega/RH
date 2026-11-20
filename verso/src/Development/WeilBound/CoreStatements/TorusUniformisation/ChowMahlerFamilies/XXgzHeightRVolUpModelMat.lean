import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat

/- English proof (translation)
Establish `hinj : Function.Injective τ`. Rewrite using `[RingHom.injective_iff_ker_eq_bot]`. Apply `Ideal.eq_bot_of_comap_eq_bot (R := ℤ)` to reduce the goal to its premises. Establish `h : Function.Injective (τ.comp (algebraMap ℤ (𝓞 K)))` using `RingHom.injective_int _`. Rewrite `h` using `[RingHom.injective_iff_ker_eq_bot]`.

Conclude with `(RingHom.comap_ker τ (algebraMap ℤ (𝓞 K))).trans h`. Use `⟨IsFractionRing.lift (A := 𝓞 K) (K := K) (L := ℂ) (g := τ) hinj, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Conclude with `IsFractionRing.lift_algebraMap (K := K) hinj x`.
-/
theorem exists_ext (K : Type) [Field K] [NumberField K] (τ : 𝓞 K →+* ℂ) :
    ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = τ := by
  have hinj : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    have h : Function.Injective (τ.comp (algebraMap ℤ (𝓞 K))) := RingHom.injective_int _
    rw [RingHom.injective_iff_ker_eq_bot] at h
    exact (RingHom.comap_ker τ (algebraMap ℤ (𝓞 K))).trans h
  refine ⟨IsFractionRing.lift (A := 𝓞 K) (K := K) (L := ℂ) (g := τ) hinj, ?_⟩
  ext x
  exact IsFractionRing.lift_algebraMap (K := K) hinj x

/- English proof (translation)
The claim follows from `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 K)) h`.
-/
theorem ext_unique (K : Type) [Field K] [NumberField K] {σ σ' : K →+* ℂ}
    (h : σ.comp (algebraMap (𝓞 K) K) = σ'.comp (algebraMap (𝓞 K) K)) : σ = σ' :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 K)) h

/- English proof (translation)
Establish `h1 : ∀ y : EuclideanSpace ℂ (Fin N), ‖Matrix.toEuclideanLin W y‖ = ‖y‖` using `fun y => by`. Rewrite using `[EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]`. Conclude with `h y.ofLp`. Establish `h2` using `(LinearMap.norm_map_iff_inner_map_map (Matrix.toEuclideanLin W)).1 h1`. Rewrite using `[Matrix.mem_unitaryGroup_iff']`.

Use extensionality with `i j`. Use `h2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)` as an intermediate fact. Rewrite `this` using `[EuclideanSpace.inner_single_left]`. Simplify using `only [PiLp.inner_apply] at this`. Simplify `this` using `[Matrix.mul_apply, Matrix.one_apply, Matrix.toEuclideanLin, mul_comm, eq_comm]`.
-/
theorem unitary_of_norm {N : ℕ} (W : Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ y : Fin N → ℂ, Real.sqrt (∑ i, ‖W.mulVec y i‖ ^ 2) = Real.sqrt (∑ i, ‖y i‖ ^ 2)) :
    W ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have h1 : ∀ y : EuclideanSpace ℂ (Fin N), ‖Matrix.toEuclideanLin W y‖ = ‖y‖ := fun y => by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    exact h y.ofLp
  have h2 := (LinearMap.norm_map_iff_inner_map_map (Matrix.toEuclideanLin W)).1 h1
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have := h2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  rw [EuclideanSpace.inner_single_left] at this
  simp only [PiLp.inner_apply] at this
  simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.toEuclideanLin, mul_comm, eq_comm] using this

/- English proof (translation)
Establish `hW : B⁻¹ * A.map (starRingEnd ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ`. Use `unitary_of_norm _ fun y => ?_` and prove the remaining obligations. Use `h (A.mulVec fun j => (starRingEnd ℂ) (y j))` as an intermediate fact. Unfold `GlobalTheory.ChowHt.frameNorm at this`. Rewrite `this` using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA.isUnit, Matrix.one_mulVec]`.

Establish `e : (fun j => (starRingEnd ℂ) (A.mulVec (fun j => (starRingEnd ℂ) (y j)) j)) = (A.map (starRingEnd ℂ)).mulVec y`. Use function extensionality and compare the values at `j`. Simplify using `[Matrix.mulVec, dotProduct]`. Rewrite `this` using `[e, Matrix.mulVec_mulVec]`. Simplify using `using this`.

Use `⟨star (B⁻¹ * A.map (starRingEnd ℂ)), Unitary.star_mem hW, ?_⟩` and prove the remaining obligations. Establish `h1` using `Matrix.mem_unitaryGroup_iff.1 hW`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB.isUnit, Matrix.one_mul]`.
-/
theorem exists_unitary {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (h : ∀ x : Fin N → ℂ, GlobalTheory.ChowHt.frameNorm B (fun j => (starRingEnd ℂ) (x j)) = GlobalTheory.ChowHt.frameNorm A x) :
    ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ, B = A.map (starRingEnd ℂ) * U := by
  have hW : B⁻¹ * A.map (starRingEnd ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ := by
    refine unitary_of_norm _ fun y => ?_
    have := h (A.mulVec fun j => (starRingEnd ℂ) (y j))
    unfold GlobalTheory.ChowHt.frameNorm at this
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA.isUnit, Matrix.one_mulVec] at this
    have e : (fun j => (starRingEnd ℂ) (A.mulVec (fun j => (starRingEnd ℂ) (y j)) j)) =
        (A.map (starRingEnd ℂ)).mulVec y := by
      funext j
      simp [Matrix.mulVec, dotProduct]
    rw [e, Matrix.mulVec_mulVec] at this
    simpa using this
  refine ⟨star (B⁻¹ * A.map (starRingEnd ℂ)), Unitary.star_mem hW, ?_⟩
  have h1 := Matrix.mem_unitaryGroup_iff.1 hW
  calc B = B * ((B⁻¹ * A.map (starRingEnd ℂ)) * star (B⁻¹ * A.map (starRingEnd ℂ))) := by rw [h1, mul_one]
    _ = _ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB.isUnit, Matrix.one_mul]

/- English proof (translation)
Establish `hs : LinearMap.range g.mulVecLin = ⊤`. Rewrite using `[Matrix.range_mulVecLin]`. Conclude with `hg`. Take `⟨s, hs'⟩` from `LinearMap.exists_rightInverse_of_surjective _ hs`. Establish `hs2 : ∀ x, g.mulVecLin (s x) = x` using `fun x => LinearMap.congr_fun hs' x`.

Use `set r := Module.finrank K (LinearMap.ker g.mulVecLin) with hr`. Establish `hdim : N + r = m`. Use `LinearMap.finrank_range_add_finrank_ker g.mulVecLin` as an intermediate fact. Rewrite `this` using `[hs, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun]`. Conclude with `this`.

Set `e : Fin m ≃ Fin N ⊕ Fin r` to `(finCongr hdim.symm).trans finSumFinEquiv.symm`. Set `c : (Fin r → K) ≃ₗ[K] LinearMap.ker g.mulVecLin` to `(Module.finBasis K _).equivFun.symm`. Set `φ : (Fin m → K) →ₗ[K] (Fin m → K)` to `s ∘ₗ LinearMap.funLeft K K (fun i => e.symm (Sum.inl i)) + (LinearMap.ker g.mulVecLin).subtype ∘ₗ c.toLinearMap ∘ₗ LinearMap.funLeft K K (fun i => e.symm (Sum.inr i))`. Establish `hφ : ∀ v, φ v = s (fun i => v (e.symm (Sum.inl i))) + (c (fun i => v (e.symm (Sum.inr i))) : Fin m → K)` using `fun v => rfl`. Establish `hgφ : ∀ v, g.mulVecLin (φ v) = fun i => v (e.symm (Sum.inl i))` using `fun v => by`.

Rewrite using `[hφ, map_add, hs2, LinearMap.mem_ker.1 (c _).2, add_zero]`. Use `⟨r, e, LinearMap.toMatrix' φ, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Take `⟨v, hv, hv0⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Rewrite `hv0` using `[LinearMap.toMatrix'_mulVec]`.

Establish `h1 : (fun i => v (e.symm (Sum.inl i))) = 0` using `by rw [← hgφ, hv0, map_zero]`. Establish `h2 : (fun i => v (e.symm (Sum.inr i))) = 0`. Rewrite `hv0` using `[hφ, h1, map_zero, zero_add]`. Conclude with `c.map_eq_zero_iff.1 (Subtype.ext hv0)`. Use `hv (funext fun a => ?_)` and prove the remaining obligations.

Take `⟨a, rfl⟩` from `e.symm.surjective a`. Break down `a with i | i` into its components or cases. Conclude with `congrFun h1 i`. Conclude with `congrFun h2 i`. Use extensionality with `j a`.

Use `congrFun (hgφ (Pi.single a 1)) j` as an intermediate fact. Rewrite `this` using `[Matrix.mulVecLin_apply, ← LinearMap.toMatrix'_mulVec φ, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]`. Rewrite using `[show (g * LinearMap.toMatrix' φ) j a = _ from this]`. Take `⟨a, rfl⟩` from `e.symm.surjective a`. Apply the tactic sequence `rcases a with i | i <;> simp [Pi.single_apply, Matrix.one_apply]`.
-/
theorem exists_P {K : Type} [Field K] {N m : ℕ} (g : Matrix (Fin N) (Fin m) K)
    (hg : Submodule.span K (Set.range g.col) = ⊤) :
    ∃ (r : ℕ) (e : Fin m ≃ Fin N ⊕ Fin r) (P : Matrix (Fin m) (Fin m) K), P.det ≠ 0 ∧
      g * P = (Matrix.fromCols (1 : Matrix (Fin N) (Fin N) K) (0 : Matrix (Fin N) (Fin r) K)).submatrix id e := by
  have hs : LinearMap.range g.mulVecLin = ⊤ := by
    rw [Matrix.range_mulVecLin]; exact hg
  obtain ⟨s, hs'⟩ := LinearMap.exists_rightInverse_of_surjective _ hs
  have hs2 : ∀ x, g.mulVecLin (s x) = x := fun x => LinearMap.congr_fun hs' x
  set r := Module.finrank K (LinearMap.ker g.mulVecLin) with hr
  have hdim : N + r = m := by
    have := LinearMap.finrank_range_add_finrank_ker g.mulVecLin
    rw [hs, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at this
    exact this
  let e : Fin m ≃ Fin N ⊕ Fin r := (finCongr hdim.symm).trans finSumFinEquiv.symm
  let c : (Fin r → K) ≃ₗ[K] LinearMap.ker g.mulVecLin := (Module.finBasis K _).equivFun.symm
  let φ : (Fin m → K) →ₗ[K] (Fin m → K) :=
    s ∘ₗ LinearMap.funLeft K K (fun i => e.symm (Sum.inl i)) +
      (LinearMap.ker g.mulVecLin).subtype ∘ₗ c.toLinearMap ∘ₗ LinearMap.funLeft K K (fun i => e.symm (Sum.inr i))
  have hφ : ∀ v, φ v = s (fun i => v (e.symm (Sum.inl i))) + (c (fun i => v (e.symm (Sum.inr i))) : Fin m → K) :=
    fun v => rfl
  have hgφ : ∀ v, g.mulVecLin (φ v) = fun i => v (e.symm (Sum.inl i)) := fun v => by
    rw [hφ, map_add, hs2, LinearMap.mem_ker.1 (c _).2, add_zero]
  refine ⟨r, e, LinearMap.toMatrix' φ, ?_, ?_⟩
  · intro h0
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    rw [LinearMap.toMatrix'_mulVec] at hv0
    have h1 : (fun i => v (e.symm (Sum.inl i))) = 0 := by rw [← hgφ, hv0, map_zero]
    have h2 : (fun i => v (e.symm (Sum.inr i))) = 0 := by
      rw [hφ, h1, map_zero, zero_add] at hv0
      exact c.map_eq_zero_iff.1 (Subtype.ext hv0)
    refine hv (funext fun a => ?_)
    obtain ⟨a, rfl⟩ := e.symm.surjective a
    rcases a with i | i
    · exact congrFun h1 i
    · exact congrFun h2 i
  · ext j a
    have := congrFun (hgφ (Pi.single a 1)) j
    rw [Matrix.mulVecLin_apply, ← LinearMap.toMatrix'_mulVec φ, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at this
    rw [show (g * LinearMap.toMatrix' φ) j a = _ from this]
    obtain ⟨a, rfl⟩ := e.symm.surjective a
    rcases a with i | i <;> simp [Pi.single_apply, Matrix.one_apply]

end PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat

/- English proof (translation)
Introduce `K V _ _ _ _ _ Nm L N m b g A hF`. Take `⟨r, e, P, hP, hgP⟩` from `PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.exists_P g hF.full`. Use `choose ext hext using PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.exists_ext K`. Establish `hu : ∀ σ : K →+* ℂ, ext (σ.comp (algebraMap (𝓞 K) K)) = σ` using `fun σ => PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.ext_unique K (hext _)`. Establish `hc : ∀ τ, ext ((starRingEnd ℂ).comp τ) = (starRingEnd ℂ).comp (ext τ)` using `fun τ => PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.ext_unique K (by rw [hext, RingHom.comp_assoc, hext])`.

Use `⟨fun τ => P.map (ext τ) * (Matrix.fromBlocks (A (ext τ)) 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e, fun τ => ?_, fun τ => ?_, fun σ x => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]`. Use `mul_ne_zero ?_ (hF.herm _)` and prove the remaining obligations. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(map_ne_zero _).2 hP`.

Take `⟨U, hU, hB⟩` from `PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.exists_unitary (A (ext τ)) (A ((starRingEnd ℂ).comp (ext τ))) (hF.herm _) (hF.herm _) (hF.conj _)`. Use `⟨(Matrix.fromBlocks U 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hU`, the goal using `[Matrix.mem_unitaryGroup_iff]`. Rewrite `hU`, the goal using `[Matrix.star_eq_conjTranspose]`. Rewrite using `[Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]`.

Simplify using `[hU]`. Simplify using `only []`. Rewrite using `[hc, hB, Matrix.map_mul, Matrix.mul_assoc, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.map_map]`. Simplify using the standard rewrite rules. Simplify using `only [hu]`.

Establish `key : g.map σ * (P.map σ * (Matrix.fromBlocks (A σ) 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e) = (Matrix.fromCols (A σ) (0 : Matrix (Fin N) (Fin r) ℂ)).submatrix id e`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.map_mul, hgP, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv, Matrix.fromCols_map, Matrix.fromCols_mul_fromBlocks]`. Simplify using the standard rewrite rules. Establish `k2 : ∀ a, ∑ k, (P.map σ * (Matrix.fromBlocks (A σ) 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e) k a * ∑ j, σ (g j k) * x j = ∑ j, Matrix.fromCols (A σ) (0 : Matrix (Fin N) (Fin r) ℂ) j (e a) * x j`. Introduce `a`.

Generalize the expression as in `P.map σ * (Matrix.fromBlocks (A σ) 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e = M at key`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `congrFun (congrFun key j) a` as an intermediate fact.

Rewrite `this` using `[Matrix.submatrix_apply, id, Matrix.mul_apply]`. Rewrite using `[← this, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.map_apply]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [k2]`. Rewrite using `[GlobalTheory.Adelic.archSize, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Equiv.sum_comp e (fun a => ‖∑ j, Matrix.fromCols (A σ) (0 : Matrix (Fin N) (Fin r) ℂ) j a * x j‖ ^ 2), Fintype.sum_sum_type]`. Simplify using the standard rewrite rules.
-/
theorem PositivityTheory.Xgn.t_xgz_height_r_vol_up_model_mat : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] (Nm : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (N m : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin m) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), IsFrame Nm L b g A → ∃ Mt : (𝓞 K →+* ℂ) → Matrix (Fin m) (Fin m) ℂ, (∀ σ, (Mt σ).det ≠ 0) ∧ (∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin m) ℂ, Mt ((starRingEnd ℂ).comp σ) = (Mt σ).map (starRingEnd ℂ) * U) ∧ ∀ (σ : K →+* ℂ) (x : Fin N → ℂ), ∑ a, ‖∑ k, Mt (σ.comp (algebraMap (𝓞 K) K)) k a * ∑ j, σ (g j k) * x j‖ ^ 2 = GlobalTheory.Adelic.archSize (A σ) x ^ 2 := by
  intro K V _ _ _ _ _ Nm L N m b g A hF
  obtain ⟨r, e, P, hP, hgP⟩ := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.exists_P g hF.full
  choose ext hext using PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.exists_ext K
  have hu : ∀ σ : K →+* ℂ, ext (σ.comp (algebraMap (𝓞 K) K)) = σ := fun σ =>
    PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.ext_unique K (hext _)
  have hc : ∀ τ, ext ((starRingEnd ℂ).comp τ) = (starRingEnd ℂ).comp (ext τ) := fun τ =>
    PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.ext_unique K (by rw [hext, RingHom.comp_assoc, hext])
  refine ⟨fun τ => P.map (ext τ) * (Matrix.fromBlocks (A (ext τ)) 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e,
    fun τ => ?_, fun τ => ?_, fun σ x => ?_⟩
  · rw [Matrix.det_mul, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
    refine mul_ne_zero ?_ (hF.herm _)
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 hP
  · obtain ⟨U, hU, hB⟩ := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_mat.exists_unitary (A (ext τ))
      (A ((starRingEnd ℂ).comp (ext τ))) (hF.herm _) (hF.herm _) (hF.conj _)
    refine ⟨(Matrix.fromBlocks U 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e, ?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff] at hU ⊢
      rw [Matrix.star_eq_conjTranspose] at hU ⊢
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_conjTranspose,
        Matrix.fromBlocks_multiply]
      simp [hU]
    · simp only []
      rw [hc, hB, Matrix.map_mul, Matrix.mul_assoc, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv,
        Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.map_map]
      simp
  · simp only [hu]
    have key : g.map σ * (P.map σ * (Matrix.fromBlocks (A σ) 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e) =
        (Matrix.fromCols (A σ) (0 : Matrix (Fin N) (Fin r) ℂ)).submatrix id e := by
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, hgP, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv,
        Matrix.fromCols_map, Matrix.fromCols_mul_fromBlocks]
      simp
    have k2 : ∀ a, ∑ k, (P.map σ * (Matrix.fromBlocks (A σ) 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e) k a *
        ∑ j, σ (g j k) * x j = ∑ j, Matrix.fromCols (A σ) (0 : Matrix (Fin N) (Fin r) ℂ) j (e a) * x j := by
      intro a
      generalize P.map σ * (Matrix.fromBlocks (A σ) 0 0 (1 : Matrix (Fin r) (Fin r) ℂ)).submatrix e e = M at key
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := congrFun (congrFun key j) a
      rw [Matrix.submatrix_apply, id, Matrix.mul_apply] at this
      rw [← this, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.map_apply]; ring
    simp only [k2]
    rw [GlobalTheory.Adelic.archSize, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Equiv.sum_comp e (fun a => ‖∑ j, Matrix.fromCols (A σ) (0 : Matrix (Fin N) (Fin r) ℂ) j a * x j‖ ^ 2),
      Fintype.sum_sum_type]
    simp
