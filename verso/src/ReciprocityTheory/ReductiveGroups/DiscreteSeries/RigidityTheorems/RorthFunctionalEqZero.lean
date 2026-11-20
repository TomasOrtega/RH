import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Alg

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {lam : Fin n → ℝ} {V : Submodule ℂ M}

/- English proof (translation)
Unfold `genSub at hy ⊢`. Rewrite `hy`, the goal using `[Submodule.mem_sInf]`. Introduce `T hT`. Conclude with `hT.2 a b y (hy T hT)`.
-/
theorem rorth_apply_mem_genSub (a b : Fin n) {y : M} (hy : y ∈ genSub E V) :
    E a b y ∈ genSub E V := by
  unfold genSub at hy ⊢
  rw [Submodule.mem_sInf] at hy ⊢
  intro T hT
  exact hT.2 a b y (hy T hT)

/- English proof (translation)
Unfold `genSub`. Conclude with `le_sInf fun T hT => hT.1`.
-/
theorem rorth_le_genSub : V ≤ genSub E V := by
  unfold genSub
  exact le_sInf fun T hT => hT.1

/- English proof (translation)
Introduce `y hy`. Rewrite `hy` using `[genSub_eq_iSup_layer hE hV.2.1, Submodule.mem_iSup_of_directed _ (Monotone.directed_le fun _ _ h => layer_mono h)]`. Take `⟨k, hk⟩` from `hy`. Use `set W := layer ε E V k with hW`. Establish `: FiniteDimensional ℂ W` using `finiteDimensional_layer hV.1 k`.

Establish `: CompleteSpace W` using `FiniteDimensional.complete ℂ W`. Establish `hWK : IsKStableSub ε E W` using `layer_kStable hE hV.2.1 k`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u : W, ∀ w : W, inner ℂ (u : M) (w : M) = f w := by`. Use `⟨(InnerProductSpace.toDual ℂ W).symm (LinearMap.toContinuousLinearMap (f.comp W.subtype)), fun w => ?_⟩` and prove the remaining obligations. Use `InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (x := w) (y := LinearMap.toContinuousLinearMap (f.comp W.subtype))` as an intermediate fact.

Conclude with `this`. Establish `hsg : ∀ a b, ε a = ε b → adjSign ε a b = 1` using `fun a b h => by simp [adjSign, h]`. Establish `hkhw : IsKHWVec ε E (lowK ε lam) (u : M)`. Use `⟨fun a => ?_, fun a b hab h => ?_⟩` and prove the remaining obligations. Establish `hz : E a a u - (lowK ε lam a : ℂ) • (u : M) ∈ W` using `W.sub_mem (hWK a a rfl _ u.2) (W.smul_mem _ u.2)`.

Rewrite using `[← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℂ)]`. Establish `key : ∀ z ∈ W, inner ℂ (E a a u - (lowK ε lam a : ℂ) • (u : M)) z = 0`. Introduce `z hz`. Rewrite using `[inner_sub_left, inner_smul_left, hU a a, hsg a a rfl, one_mul, hu ⟨_, hWK a a rfl _ hz⟩, hu ⟨z, hz⟩]`. Simplify using `[hfd]`.

Conclude with `key _ hz`. Establish `hz : E a b u ∈ W` using `hWK a b h _ u.2`. Rewrite using `[← inner_self_eq_zero (𝕜 := ℂ), hU a b, hsg a b h, one_mul]`. Conclude with `(hu ⟨_, hWK b a h.symm _ hz⟩).trans (hfl a b hab h _)`. Establish `huV : (u : M) ∈ V` using `khw_lowK_mem hE hU hV hc hgap (layer_le_genSub k u.2) hkhw`.

Establish `hu0 : (u : M) = 0`. Rewrite using `[← inner_self_eq_zero (𝕜 := ℂ), hu u]`. Conclude with `hfV _ huV`. Rewrite using `[← hu ⟨y, hk⟩, hu0, inner_zero_left]`.
-/
theorem rorth_functional_eq_zero (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) (f : M →ₗ[ℂ] ℂ) (hfV : ∀ v ∈ V, f v = 0)
    (hfd : ∀ a y, f (E a a y) = (lowK ε lam a : ℂ) * f y)
    (hfl : ∀ a b, a < b → ε a = ε b → ∀ y, f (E b a y) = 0) :
    ∀ y ∈ genSub E V, f y = 0 := by
  intro y hy
  rw [genSub_eq_iSup_layer hE hV.2.1,
    Submodule.mem_iSup_of_directed _ (Monotone.directed_le fun _ _ h => layer_mono h)] at hy
  obtain ⟨k, hk⟩ := hy
  set W := layer ε E V k with hW
  have : FiniteDimensional ℂ W := finiteDimensional_layer hV.1 k
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hWK : IsKStableSub ε E W := layer_kStable hE hV.2.1 k
  obtain ⟨u, hu⟩ : ∃ u : W, ∀ w : W, inner ℂ (u : M) (w : M) = f w := by
    refine ⟨(InnerProductSpace.toDual ℂ W).symm
      (LinearMap.toContinuousLinearMap (f.comp W.subtype)), fun w => ?_⟩
    have := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (x := w)
      (y := LinearMap.toContinuousLinearMap (f.comp W.subtype))
    exact this
  have hsg : ∀ a b, ε a = ε b → adjSign ε a b = 1 := fun a b h => by simp [adjSign, h]
  have hkhw : IsKHWVec ε E (lowK ε lam) (u : M) := by
    refine ⟨fun a => ?_, fun a b hab h => ?_⟩
    · have hz : E a a u - (lowK ε lam a : ℂ) • (u : M) ∈ W :=
        W.sub_mem (hWK a a rfl _ u.2) (W.smul_mem _ u.2)
      rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℂ)]
      have key : ∀ z ∈ W, inner ℂ (E a a u - (lowK ε lam a : ℂ) • (u : M)) z = 0 := by
        intro z hz
        rw [inner_sub_left, inner_smul_left, hU a a, hsg a a rfl, one_mul,
          hu ⟨_, hWK a a rfl _ hz⟩, hu ⟨z, hz⟩]
        simp [hfd]
      exact key _ hz
    · have hz : E a b u ∈ W := hWK a b h _ u.2
      rw [← inner_self_eq_zero (𝕜 := ℂ), hU a b, hsg a b h, one_mul]
      exact (hu ⟨_, hWK b a h.symm _ hz⟩).trans (hfl a b hab h _)
  have huV : (u : M) ∈ V := khw_lowK_mem hE hU hV hc hgap (layer_le_genSub k u.2) hkhw
  have hu0 : (u : M) = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ), hu u]
    exact hfV _ huV
  rw [← hu ⟨y, hk⟩, hu0, inner_zero_left]

end Alg

section Mat

/- English proof (translation)
Simplify using `only [actM, Matrix.add_apply, add_smul, Finset.sum_add_distrib]`.
-/
theorem rorth_actM_add {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    actM E (X + Y) = actM E X + actM E Y := by
  simp only [actM, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [actM, Matrix.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]`.
-/
theorem rorth_actM_smul {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    actM E (c • X) = c • actM E X := by
  simp only [actM, Matrix.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]

/- English proof (translation)
Unfold `actM`. Rewrite using `[Finset.sum_eq_single a, Finset.sum_eq_single b]`. Simplify using `[Matrix.single_apply_same]`. Introduce `b' _ hb`. Rewrite using `[Matrix.single_apply_of_col_ne _ _ (Ne.symm hb), zero_smul]`.

Simplify using the standard rewrite rules. Introduce `a' _ ha`. Use `Finset.sum_eq_zero fun b' _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.single_apply_of_row_ne (Ne.symm ha), zero_smul]`. Simplify using the standard rewrite rules.
-/
theorem rorth_actM_single {M : Type*} [AddCommGroup M] [Module ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    actM E (Matrix.single a b (1 : ℂ)) = E a b := by
  unfold actM
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp [Matrix.single_apply_same]
  · intro b' _ hb; rw [Matrix.single_apply_of_col_ne _ _ (Ne.symm hb), zero_smul]
  · simp
  · intro a' _ ha
    refine Finset.sum_eq_zero fun b' _ => ?_
    rw [Matrix.single_apply_of_row_ne (Ne.symm ha), zero_smul]
  · simp

/- English proof (translation)
Take `⟨hu, hJ⟩` from `hk`. Establish `h1 : kᴴ * k = 1` using `(Matrix.mem_unitaryGroup_iff'.1 hu)`. Use `show kᴴ * Jm ε * k = Jm ε`. Rewrite using `[Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, h1, Matrix.one_mul]`.
-/
theorem rorth_mem_UJset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    k ∈ UJset ε := by
  obtain ⟨hu, hJ⟩ := hk
  have h1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff'.1 hu)
  show kᴴ * Jm ε * k = Jm ε
  rw [Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, h1, Matrix.one_mul]

/- English proof (translation)
Use `⟨?_, h2⟩` and prove the remaining obligations. Unfold `inG`. Rewrite using `[h1, Matrix.neg_mul, h2, neg_add_cancel]`.
-/
theorem rorth_inK_of_skew {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (h1 : Zᴴ = -Z)
    (h2 : Z * Jm ε = Jm ε * Z) : inK ε Z := by
  refine ⟨?_, h2⟩
  unfold inG
  rw [h1, Matrix.neg_mul, h2, neg_add_cancel]

/- English proof (translation)
Take `⟨h1, h2⟩` from `hZ`. Use `⟨?_, by rw [Matrix.smul_mul, Matrix.mul_smul, h2]⟩` and prove the remaining obligations. Unfold `inG at h1 ⊢`. Establish `hs : star (t : ℂ) = t` using `Complex.conj_ofReal t`. Rewrite using `[Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]`.
-/
theorem rorth_inK_smul {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) (t : ℝ) :
    inK ε ((t : ℂ) • Z) := by
  obtain ⟨h1, h2⟩ := hZ
  refine ⟨?_, by rw [Matrix.smul_mul, Matrix.mul_smul, h2]⟩
  unfold inG at h1 ⊢
  have hs : star (t : ℂ) = t := Complex.conj_ofReal t
  rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]

/- English proof (translation)
Use extensionality with `i j`. Unfold `Jm`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]`. Distinguish the cases in `hij : a = i ∧ b = j`. Take `⟨rfl, rfl⟩` from `hij`.

Simplify using `[h]`. Simplify using `[hij]`.
-/
theorem rorth_single_comm {ε : Fin n → Bool} {a b : Fin n} (h : ε a = ε b) :
    Matrix.single a b (1 : ℂ) * Jm ε = Jm ε * Matrix.single a b (1 : ℂ) := by
  ext i j
  unfold Jm
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  by_cases hij : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := hij
    simp [h]
  · simp [hij]

/- English proof (translation)
Apply `rorth_inK_of_skew` to reduce the goal to its premises. Simplify using `only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_single, star_one, star_star, neg_smul, Matrix.conjTranspose_neg, neg_add_rev, neg_neg]`. Rewrite using `[Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, rorth_single_comm h, rorth_single_comm h.symm]`.
-/
theorem rorth_inK_comb {ε : Fin n → Bool} {a b : Fin n} (h : ε a = ε b) (c : ℂ) :
    inK ε (c • Matrix.single a b (1 : ℂ) + (-star c) • Matrix.single b a (1 : ℂ)) := by
  apply rorth_inK_of_skew
  · simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_single,
      star_one, star_star, neg_smul, Matrix.conjTranspose_neg, neg_add_rev, neg_neg]
  · rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_smul, rorth_single_comm h, rorth_single_comm h.symm]

end Mat

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

/- English proof (translation)
The claim follows from `(LinearIsometry.mk (σ g : H →ₗ[ℂ] H) (hσ.2.1 g hg)).inner_map_map x y`.
-/
theorem rorth_inner_map (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (x y : H) : inner ℂ (σ g x) (σ g y) = inner ℂ x y :=
  (LinearIsometry.mk (σ g : H →ₗ[ℂ] H) (hσ.2.1 g hg)).inner_map_map x y

/- English proof (translation)
Set `ι : V →ₗ[ℂ] H` to `D.subtype.comp V.subtype`. Establish `hι : Function.Injective ι` using `D.injective_subtype.comp V.injective_subtype`. Set `S : Submodule ℂ H` to `LinearMap.range ι`. Establish `: FiniteDimensional ℂ S` using `inferInstance`. Establish `: CompleteSpace S` using `FiniteDimensional.complete ℂ S`.

Set `e : V ≃ₗ[ℂ] S` to `LinearEquiv.ofInjective ι hι`. Use `⟨(LinearMap.toContinuousLinearMap (j.comp e.symm.toLinearMap)).comp S.orthogonalProjectionOnto, fun v => ?_⟩` and prove the remaining obligations. Establish `h1 : S.orthogonalProjectionOnto ((v : D) : H) = e v` using `S.orthogonalProjectionOnto_mem_subspace_eq_self (e v)`. Simplify using `[h1]`.
-/
theorem rorth_exists_ext (hVf : FiniteDimensional ℂ V) (j : V →ₗ[ℂ] H) :
    ∃ φ : H →L[ℂ] H, ∀ v : V, φ ((v : D) : H) = j v := by
  let ι : V →ₗ[ℂ] H := D.subtype.comp V.subtype
  have hι : Function.Injective ι := D.injective_subtype.comp V.injective_subtype
  let S : Submodule ℂ H := LinearMap.range ι
  have : FiniteDimensional ℂ S := inferInstance
  have : CompleteSpace S := FiniteDimensional.complete ℂ S
  let e : V ≃ₗ[ℂ] S := LinearEquiv.ofInjective ι hι
  refine ⟨(LinearMap.toContinuousLinearMap (j.comp e.symm.toLinearMap)).comp
    S.orthogonalProjectionOnto, fun v => ?_⟩
  have h1 : S.orthogonalProjectionOnto ((v : D) : H) = e v :=
    S.orthogonalProjectionOnto_mem_subspace_eq_self (e v)
  simp [h1]

/- English proof (translation)
Establish `h1` using `hD.deriv Z hZ.1 (v : D)`. Establish `h2` using `hD.deriv Z hZ.1 x`. Establish `h1'` using `(φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1`. Establish `h3` using `HasDerivAt.inner ℂ h1' h2`. Establish `hconst : (fun t : ℝ => inner ℂ (((φ.restrictScalars ℝ) ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Z)) ((v : D) : H)) t) (σ (NormedSpace.exp ((t : ℂ) • Z)) (x : H))) = fun _ => inner ℂ (j v) (x : H)`.

Use function extensionality and compare the values at `t`. Establish `hk` using `exp_mem_Kset (rorth_inK_smul hZ t)`. Take `⟨w, hw, hwe⟩` from `hVK _ hk v v.2`. Establish `h4` using `hj _ hk v ⟨w, hw⟩ hwe`. Simplify using `only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']`.

Rewrite using `[← hwe, hφ ⟨w, hw⟩, h4, rorth_inner_map hσ (rorth_mem_UJset hk)]`. Rewrite `h3` using `[hconst]`. Establish `h5` using `h3.unique (hasDerivAt_const (0 : ℝ) _)`. Simplify using `only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', exp_zero_smul, hσ.1.1, one_apply_eq_self, hφ] at h5`. Conclude with `h5`.
-/
theorem rorth_inner_actM (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (j : V →ₗ[ℂ] H)
    (hj : ∀ k ∈ Kset ε, ∀ v w : V, ((w : D) : H) = σ k ((v : D) : H) → j w = σ k (j v))
    (φ : H →L[ℂ] H) (hφ : ∀ v : V, φ ((v : D) : H) = j v)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) (v : V) (x : D) :
    inner ℂ (j v) ((actM E Z x : D) : H) + inner ℂ (φ ((actM E Z v : D) : H)) (x : H) = 0 := by
  have h1 := hD.deriv Z hZ.1 (v : D)
  have h2 := hD.deriv Z hZ.1 x
  have h1' := (φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 := HasDerivAt.inner ℂ h1' h2
  have hconst : (fun t : ℝ => inner ℂ
      (((φ.restrictScalars ℝ) ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Z)) ((v : D) : H)) t)
      (σ (NormedSpace.exp ((t : ℂ) • Z)) (x : H))) = fun _ => inner ℂ (j v) (x : H) := by
    funext t
    have hk := exp_mem_Kset (rorth_inK_smul hZ t)
    obtain ⟨w, hw, hwe⟩ := hVK _ hk v v.2
    have h4 := hj _ hk v ⟨w, hw⟩ hwe
    simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
    rw [← hwe, hφ ⟨w, hw⟩, h4, rorth_inner_map hσ (rorth_mem_UJset hk)]
  rw [hconst] at h3
  have h5 := h3.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', exp_zero_smul, hσ.1.1,
    one_apply_eq_self, hφ] at h5
  exact h5

/- English proof (translation)
Establish `h1` using `rorth_inner_actM hσ hD hVK j hj φ hφ (rorth_inK_comb h 1) v x`. Establish `h2` using `rorth_inner_actM hσ hD hVK j hj φ hφ (rorth_inK_comb h Complex.I) v x`. Simplify using `only [rorth_actM_add, rorth_actM_smul, rorth_actM_single, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, star_one, map_one, map_neg, Complex.star_def, Complex …`. Establish `hI` using `Complex.I_mul_I`. Take the linear combination `(1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 - (1 / 2 : ℂ) * (inner ℂ (j v) ((E a b x : D) : H) + inner ℂ (j v) ((E b a x : D) : H) - inner ℂ (φ ((E a b v : D) : H)) (x : H) - inner ℂ (φ ((E b a v : D) : H)) (x : H)) * hI`.
-/
theorem rorth_inner_E (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (j : V →ₗ[ℂ] H)
    (hj : ∀ k ∈ Kset ε, ∀ v w : V, ((w : D) : H) = σ k ((v : D) : H) → j w = σ k (j v))
    (φ : H →L[ℂ] H) (hφ : ∀ v : V, φ ((v : D) : H) = j v)
    {a b : Fin n} (h : ε a = ε b) (v : V) (x : D) :
    inner ℂ (φ ((E a b v : D) : H)) (x : H) = inner ℂ (j v) ((E b a x : D) : H) := by
  have h1 := rorth_inner_actM hσ hD hVK j hj φ hφ (rorth_inK_comb h 1) v x
  have h2 := rorth_inner_actM hσ hD hVK j hj φ hφ (rorth_inK_comb h Complex.I) v x
  simp only [rorth_actM_add, rorth_actM_smul, rorth_actM_single, LinearMap.add_apply,
    LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, star_one, map_one, map_neg,
    Complex.star_def, Complex.conj_I, neg_neg] at h1 h2
  have hI := Complex.I_mul_I
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 -
    (1 / 2 : ℂ) * (inner ℂ (j v) ((E a b x : D) : H) + inner ℂ (j v) ((E b a x : D) : H) -
      inner ℂ (φ ((E a b v : D) : H)) (x : H) - inner ℂ (φ ((E b a v : D) : H)) (x : H)) * hI

/- English proof (translation)
Take `⟨φ, hφ⟩` from `rorth_exists_ext hV.1 j`. Establish `hrel` using `fun a b (h : ε a = ε b) => rorth_inner_E hσ hD hVK j hj φ hφ h`. Take `⟨w, hwV, hw0, hw⟩` from `hV.2.2.2`. Establish `h0 : ∀ y ∈ genSub E V, inner ℂ (j ⟨w, hwV⟩) (y : H) = 0`. Use `rorth_functional_eq_zero hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hc hgap ((innerₛₗ ℂ (j ⟨w, hwV⟩)).comp D.subtype) (fun v hv => horth ⟨v, hv⟩ _) (fun a y => ?_) (fun a b hab h y => ?_)` and prove the remaining obligations.

Use `hrel a a rfl ⟨w, hwV⟩ y` as an intermediate fact. Simplify using `only [hw.1 a, Submodule.coe_smul, map_smul, inner_smul_left, Complex.conj_ofReal, hφ ⟨w, hwV⟩] at this`. Conclude with `this.symm`. Use `hrel a b h ⟨w, hwV⟩ y` as an intermediate fact. Simplify using `only [hw.2 a b hab h, Submodule.coe_zero, map_zero, inner_zero_left] at this`.

Conclude with `this.symm`. Set `S : Submodule ℂ D` to `{ carrier := {v | v ∈ V ∧ ∀ y ∈ genSub E V, inner ℂ (φ (v : H)) (y : H) = 0} add_mem' := fun {u v} hu hv => ⟨V.add_mem hu.1 hv.1, fun y hy => by`. Simplify using `[hu.2 y hy, hv.2 y hy]⟩`. Use the proof step `zero_mem' := ⟨V.zero_mem, fun y _ => by simp⟩`. Use the proof step `smul_mem' := fun c v hv => ⟨V.smul_mem c hv.1, fun y hy => by`.

Simplify using `[hv.2 y hy]⟩ }`. Establish `hSK : IsKStableSub ε E S`. Introduce `a b h v hv`. Use `⟨hV.2.1 a b h v hv.1, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[hrel a b h ⟨v, hv.1⟩ y, ← hφ]`.

Conclude with `hv.2 _ (rorth_apply_mem_genSub b a hy)`. Establish `hwS : w ∈ S` using `⟨hwV, fun y hy => by rw [hφ ⟨w, hwV⟩]; exact h0 y hy⟩`. Break down `hV.2.2.1 S (fun v hv => hv.1) hSK with h | h` into its components or cases. Rewrite `hwS` using `[h]`. Conclude with `absurd ((Submodule.mem_bot ℂ).1 hwS) hw0`.

Introduce `v' y hy`. Establish `hv' : (v' : D) ∈ S` using `by rw [h]; exact v'.2`. Rewrite using `[← hφ]`. Conclude with `hv'.2 y hy`.
-/
theorem rigid_orth_genSub {lam : Fin n → ℝ} (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ)
    (hD : IsDerivedOn ε σ D E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (j : V →ₗ[ℂ] H)
    (hj : ∀ k ∈ Kset ε, ∀ v w : V, ((w : D) : H) = σ k ((v : D) : H) → j w = σ k (j v))
    (horth : ∀ v v' : V, inner ℂ (j v') ((v : D) : H) = 0) :
    ∀ v' : V, ∀ y ∈ genSub E V, inner ℂ (j v') (y : H) = 0 := by
  obtain ⟨φ, hφ⟩ := rorth_exists_ext hV.1 j
  have hrel := fun a b (h : ε a = ε b) => rorth_inner_E hσ hD hVK j hj φ hφ h
  obtain ⟨w, hwV, hw0, hw⟩ := hV.2.2.2
  have h0 : ∀ y ∈ genSub E V, inner ℂ (j ⟨w, hwV⟩) (y : H) = 0 := by
    refine rorth_functional_eq_zero hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hc hgap
      ((innerₛₗ ℂ (j ⟨w, hwV⟩)).comp D.subtype) (fun v hv => horth ⟨v, hv⟩ _) (fun a y => ?_)
      (fun a b hab h y => ?_)
    · have := hrel a a rfl ⟨w, hwV⟩ y
      simp only [hw.1 a, Submodule.coe_smul, map_smul, inner_smul_left, Complex.conj_ofReal,
        hφ ⟨w, hwV⟩] at this
      exact this.symm
    · have := hrel a b h ⟨w, hwV⟩ y
      simp only [hw.2 a b hab h, Submodule.coe_zero, map_zero, inner_zero_left] at this
      exact this.symm
  let S : Submodule ℂ D :=
    { carrier := {v | v ∈ V ∧ ∀ y ∈ genSub E V, inner ℂ (φ (v : H)) (y : H) = 0}
      add_mem' := fun {u v} hu hv => ⟨V.add_mem hu.1 hv.1, fun y hy => by
        simp [hu.2 y hy, hv.2 y hy]⟩
      zero_mem' := ⟨V.zero_mem, fun y _ => by simp⟩
      smul_mem' := fun c v hv => ⟨V.smul_mem c hv.1, fun y hy => by
        simp [hv.2 y hy]⟩ }
  have hSK : IsKStableSub ε E S := by
    intro a b h v hv
    refine ⟨hV.2.1 a b h v hv.1, fun y hy => ?_⟩
    rw [hrel a b h ⟨v, hv.1⟩ y, ← hφ]
    exact hv.2 _ (rorth_apply_mem_genSub b a hy)
  have hwS : w ∈ S := ⟨hwV, fun y hy => by rw [hφ ⟨w, hwV⟩]; exact h0 y hy⟩
  rcases hV.2.2.1 S (fun v hv => hv.1) hSK with h | h
  · rw [h] at hwS
    exact absurd ((Submodule.mem_bot ℂ).1 hwS) hw0
  · intro v' y hy
    have hv' : (v' : D) ∈ S := by rw [h]; exact v'.2
    rw [← hφ]
    exact hv'.2 y hy

/- English proof (translation)
Introduce `v' x hx`. Establish `hle : ((genSub E V).map D.subtype).topologicalClosure ≤ (ℂ ∙ j v')ᗮ`. Use `Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `Submodule.mem_orthogonal_singleton_iff_inner_right.2 (rigid_orth_genSub hgap hσ hD hV hc hVK j hj horth v' y hy)`.

Conclude with `Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hx)`.
-/
theorem rigid_orth_closure {lam : Fin n → ℝ} (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ)
    (hD : IsDerivedOn ε σ D E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (j : V →ₗ[ℂ] H)
    (hj : ∀ k ∈ Kset ε, ∀ v w : V, ((w : D) : H) = σ k ((v : D) : H) → j w = σ k (j v))
    (horth : ∀ v v' : V, inner ℂ (j v') ((v : D) : H) = 0) :
    ∀ v' : V, ∀ x ∈ ((genSub E V).map D.subtype).topologicalClosure, inner ℂ (j v') x = 0 := by
  intro v' x hx
  have hle : ((genSub E V).map D.subtype).topologicalClosure ≤ (ℂ ∙ j v')ᗮ := by
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.2
      (rigid_orth_genSub hgap hσ hD hV hc hVK j hj horth v' y hy)
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hx)

end Rep

end ReciprocityTheory.ChartRestriction.DS
