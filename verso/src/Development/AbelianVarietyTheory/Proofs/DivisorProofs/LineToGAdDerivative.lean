import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixOneParameterGroupEqExpOfContinuous

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

open scoped TensorProduct Matrix ContDiff

namespace GlobalTheory.LineDerSum

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

/- English proof (translation)
Establish `h1 : ∀ t : ℝ, (NormedSpace.exp (t • Z))ᴴ = NormedSpace.exp (t • Zᴴ)` using `fun t => by`. Rewrite using `[← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, star_trivial]`. Establish `hd` using `((hasDerivAt_exp_smul_const (𝕂 := ℝ) Zᴴ (0 : ℝ)).mul_const A).mul (hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ))`. Establish `he : ((fun t : ℝ => NormedSpace.exp (t • Zᴴ) * A) * fun t : ℝ => NormedSpace.exp (t • Z)) = fun _ => A`. Use function extensionality and compare the values at `fun t => by rw [Pi.mul_apply, ← h1, h]`.

Simplify using `using hd.unique ((hasDerivAt_const (0 : ℝ) A).congr_of_eventuallyEq (.of_forall (congrFun he)))`.
-/
theorem skew_of_exp_unitary {n : ℕ} (A Z : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, (NormedSpace.exp (t • Z))ᴴ * A * NormedSpace.exp (t • Z) = A) : Zᴴ * A + A * Z = 0 := by
  have h1 : ∀ t : ℝ, (NormedSpace.exp (t • Z))ᴴ = NormedSpace.exp (t • Zᴴ) := fun t => by
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, star_trivial]
  have hd := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) Zᴴ (0 : ℝ)).mul_const A).mul (hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ))
  have he : ((fun t : ℝ => NormedSpace.exp (t • Zᴴ) * A) * fun t : ℝ => NormedSpace.exp (t • Z)) = fun _ => A :=
    funext fun t => by rw [Pi.mul_apply, ← h1, h]
  simpa using hd.unique ((hasDerivAt_const (0 : ℝ) A).congr_of_eventuallyEq (.of_forall (congrFun he)))

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => exact i.elim0`. Consider the case `succ r ih`. Rewrite using `[List.ofFn_succ, List.prod_cons]`. Proceed by induction on `i using Fin.cases with`.

Consider the case `zero`. Rewrite using `[List.prod_eq_one, mul_one]`. Introduce `x hx`. Take `⟨j, rfl⟩` from `List.mem_ofFn.1 hx`. Conclude with `hi _ (Fin.succ_ne_zero j)`.

Consider the case `succ i`. Rewrite using `[hi 0 (Fin.succ_ne_zero i).symm, one_mul]`. Conclude with `ih (fun j => h j.succ) i fun j hj => hi _ fun e => hj (Fin.succ_injective _ e)`.
-/
theorem prod_ofFn_single {M : Type*} [Monoid M] {r : ℕ} (h : Fin r → M) (i : Fin r) (hi : ∀ j, j ≠ i → h j = 1) :
    (List.ofFn h).prod = h i := by
  induction r with
  | zero => exact i.elim0
  | succ r ih =>
    rw [List.ofFn_succ, List.prod_cons]
    induction i using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact hi _ (Fin.succ_ne_zero j)
    | succ i =>
      rw [hi 0 (Fin.succ_ne_zero i).symm, one_mul]
      exact ih (fun j => h j.succ) i fun j hj => hi _ fun e => hj (Fin.succ_injective _ e)

/- English proof (translation)
Establish `h1 : ∀ v : Fin r → ℝ, HasDerivAt (fun t : ℝ => Φ (t • v)) (fderiv ℝ Φ 0 v) 0` using `fun v => by`. Establish `hl : HasDerivAt (fun t : ℝ => t • v) v 0` using `by simpa using (hasDerivAt_id (0 : ℝ)).smul_const v`. Conclude with `HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hΦ.hasFDerivAt hl (by simp)`. Establish `h2 : ∀ i, deriv (fun t : ℝ => Φ (Pi.single i t)) 0 = fderiv ℝ Φ 0 (Pi.single i 1)` using `fun i => by`. Rewrite using `[← (h1 (Pi.single i 1)).deriv]`.

Use `congr 1`. Use function extensionality and compare the values at `t`. Rewrite using `[← Pi.single_smul', smul_eq_mul, mul_one]`. Establish `h3` using `h1 fun _ => 1`. Simplify using `only [h2, ← map_sum, Finset.univ_sum_single (fun _ : Fin r => (1 : ℝ))]`.

Use `h3 using 3` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `_`. Simplify using the standard rewrite rules.
-/
theorem hasDerivAt_diag {r : ℕ} (Φ : (Fin r → ℝ) → ℂ) (hΦ : DifferentiableAt ℝ Φ 0) :
    HasDerivAt (fun t : ℝ => Φ fun _ => t) (∑ i, deriv (fun t : ℝ => Φ (Pi.single i t)) 0) 0 := by
  have h1 : ∀ v : Fin r → ℝ, HasDerivAt (fun t : ℝ => Φ (t • v)) (fderiv ℝ Φ 0 v) 0 := fun v => by
    have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    exact HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hΦ.hasFDerivAt hl (by simp)
  have h2 : ∀ i, deriv (fun t : ℝ => Φ (Pi.single i t)) 0 = fderiv ℝ Φ 0 (Pi.single i 1) := fun i => by
    rw [← (h1 (Pi.single i 1)).deriv]
    congr 1
    funext t
    rw [← Pi.single_smul', smul_eq_mul, mul_one]
  have h3 := h1 fun _ => 1
  simp only [h2, ← map_sum, Finset.univ_sum_single (fun _ : Fin r => (1 : ℝ))]
  convert h3 using 3
  funext _
  simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (EmbOver E w)` from `inferInstance`. Take `⟨Z, hZ⟩` from `GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter (fun t => GlobalTheory.Orb.archMat σ J τ (projArch σ J w (δ t))) ((GlobalTheory.Orb.continuous_archMat σ J τ).comp ((continuous_projArch σ J w).comp hc)) (by simp only [h0, map_one]) (fun s t => by simp only [hm, map_m …`. Use `⟨w, τ, Z, skew_of_exp_unitary _ _ fun t => ?_, fun t => ⟨_, rfl, hZ t⟩⟩` and prove the remaining obligations. Rewrite using `[← hZ t, GlobalTheory.Orb.archMat_eq_archEquiv J hcm]`. Conclude with `(archEquiv J hcm τ _).2`.
-/
theorem isRealLine_component (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (δ : ℝ → GAd σ J)
    (hc : Continuous δ) (h0 : δ 0 = 1) (hm : ∀ s t, δ (s + t) = δ s * δ t) (w : InfinitePlace F) :
    IsRealLine σ J fun t => embArch σ J w (projArch σ J w (δ t)) := by
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  obtain ⟨Z, hZ⟩ := GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter
    (fun t => GlobalTheory.Orb.archMat σ J τ (projArch σ J w (δ t)))
    ((GlobalTheory.Orb.continuous_archMat σ J τ).comp ((continuous_projArch σ J w).comp hc))
    (by simp only [h0, map_one]) (fun s t => by simp only [hm, map_mul])
  refine ⟨w, τ, Z, skew_of_exp_unitary _ _ fun t => ?_, fun t => ⟨_, rfl, hZ t⟩⟩
  rw [← hZ t, GlobalTheory.Orb.archMat_eq_archEquiv J hcm]
  exact (archEquiv J hcm τ _).2

/- English proof (translation)
Set `e` to `(Fintype.equivFin (InfinitePlace F)).symm`. Set `β : Fin (Fintype.card (InfinitePlace F)) → ℝ → GAd σ J` to `fun i t => embArch σ J (e i) (projArch σ J (e i) (δ t))`. Establish `hβ : ∀ i, IsRealLine σ J (β i)` using `fun i => isRealLine_component hcm J δ hc h0 hm (e i)`. Establish `hβ0 : ∀ i, β i 0 = 1` using `fun i => by simp only [β, h0, map_one]`. Establish `hprod : ∀ t, (List.ofFn fun i => β i t).prod = δ t` using `fun t => by`.

Use `GAd_ext σ J (fun w => ?_) fun v => ?_` and prove the remaining obligations. Take `⟨i, rfl⟩` from `e.surjective w`. Rewrite using `[map_list_prod, List.map_ofFn, prod_ofFn_single _ i fun j hj => ?_]`. Conclude with `projArch_embArch_self σ J _ _`. Conclude with `projArch_embArch_ne σ J (fun h => hj (e.injective h).symm) _`.

Rewrite using `[mem_infPts_iff_forall.1 (hi t) v, map_list_prod, List.map_ofFn]`. Use `List.prod_eq_one fun x hx => ?_` and prove the remaining obligations. Take `⟨j, rfl⟩` from `List.mem_ofFn.1 hx`. Simplify using `[β]`. Use `⟨_, β, hβ, fun f hf g => ?_⟩` and prove the remaining obligations.

Establish `hd` using `hasDerivAt_diag _ (((hf _ β hβ g).differentiable (by simp)) 0)`. Simplify using `only [hprod] at hd`. Use `hd using 2 with i` and compare the differences between its conclusion and the goal. Unfold `lineDer`. Use `congr 1`.

Use function extensionality and compare the values at `t`. Rewrite using `[prod_ofFn_single _ i fun j hj => by rw [Pi.single_eq_of_ne hj, hβ0], Pi.single_eq_same]`.
-/
theorem exists_lines_of_infPts (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (δ : ℝ → GAd σ J)
    (hc : Continuous δ) (h0 : δ 0 = 1) (hm : ∀ s t, δ (s + t) = δ s * δ t) (hi : ∀ t, δ t ∈ infPts σ J) :
    ∃ (r : ℕ) (β : Fin r → ℝ → GAd σ J), (∀ i, IsRealLine σ J (β i)) ∧
      ∀ f, IsSm σ J f → ∀ g, HasDerivAt (fun t : ℝ => f (g * δ t)) (∑ i, lineDer (β i) f g) 0 := by
  let e := (Fintype.equivFin (InfinitePlace F)).symm
  let β : Fin (Fintype.card (InfinitePlace F)) → ℝ → GAd σ J :=
    fun i t => embArch σ J (e i) (projArch σ J (e i) (δ t))
  have hβ : ∀ i, IsRealLine σ J (β i) := fun i => isRealLine_component hcm J δ hc h0 hm (e i)
  have hβ0 : ∀ i, β i 0 = 1 := fun i => by simp only [β, h0, map_one]
  have hprod : ∀ t, (List.ofFn fun i => β i t).prod = δ t := fun t => by
    refine GAd_ext σ J (fun w => ?_) fun v => ?_
    · obtain ⟨i, rfl⟩ := e.surjective w
      rw [map_list_prod, List.map_ofFn, prod_ofFn_single _ i fun j hj => ?_]
      · exact projArch_embArch_self σ J _ _
      · exact projArch_embArch_ne σ J (fun h => hj (e.injective h).symm) _
    · rw [mem_infPts_iff_forall.1 (hi t) v, map_list_prod, List.map_ofFn]
      refine List.prod_eq_one fun x hx => ?_
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      simp [β]
  refine ⟨_, β, hβ, fun f hf g => ?_⟩
  have hd := hasDerivAt_diag _ (((hf _ β hβ g).differentiable (by simp)) 0)
  simp only [hprod] at hd
  convert hd using 2 with i
  unfold lineDer
  congr 1
  funext t
  rw [prod_ofFn_single _ i fun j hj => by rw [Pi.single_eq_of_ne hj, hβ0], Pi.single_eq_same]

/- English proof (translation)
Establish `h` using `hg ((0, 1) : Ainf F × Af F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))`. Establish `key : ∀ z : AF F ⊗[F] E, Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((show AF F from ((0, 1) : Ainf F × Af F)) • z) = Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z` using `fun z => by`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [smul_zero]`. Consider the case `add x y hx hy => rw [smul_add, map_add, map_add, hx, hy]`.

Consider the case `tmul a b`. Rewrite using `[TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, smul_eq_mul, map_mul]`. Conclude with `congrArg (· ⊗ₜ[F] _) (one_mul _)`. Use `Units.ext (Matrix.ext fun r s => ?_)` and prove the remaining obligations. Establish `h2` using `key ((mat g - 1) r s)`.

Rewrite `h2` using `[show _ • (mat g - 1) r s = 0 from congrFun (congrFun h r) s, map_zero, Matrix.sub_apply, map_sub, eq_comm, sub_eq_zero]`. Use `h2.trans ?_` and prove the remaining obligations. Distinguish the cases in `e : r = s`. Substitute `e` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Matrix.one_apply_ne e]`.
-/
theorem toGAd_mem_infPts (hσ : ∀ x, σ (σ x) = x) {d : ℕ} (W : Spc F E d) {c : E} (hc : c ≠ 0) {g : UA σ W.J}
    (hg : g ∈ UAt σ W (evI F)) : toGAd hσ W.J hc g ∈ infPts σ (c • W.J.map σ) := by
  have h := hg ((0, 1) : Ainf F × Af F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))
  have key : ∀ z : AF F ⊗[F] E, Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)
      ((show AF F from ((0, 1) : Ainf F × Af F)) • z) = Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy]
    | tmul a b =>
      rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, smul_eq_mul, map_mul]
      exact congrArg (· ⊗ₜ[F] _) (one_mul _)
  refine Units.ext (Matrix.ext fun r s => ?_)
  have h2 := key ((mat g - 1) r s)
  rw [show _ • (mat g - 1) r s = 0 from congrFun (congrFun h r) s, map_zero, Matrix.sub_apply, map_sub, eq_comm,
    sub_eq_zero] at h2
  refine h2.trans ?_
  by_cases e : r = s
  · subst e; simp
  · simp [Matrix.one_apply_ne e]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ hcm d W c hc γ hγ`. Establish `hs : Continuous (toGAd hσ W.J hc)` using `continuous_induced_rng.2 continuous_subtype_val`. Conclude with `exists_lines_of_infPts hcm _ (fun t => toGAd hσ W.J hc (γ (Multiplicative.ofAdd t))) (hs.comp (hγ.1.comp continuous_ofAdd)) (by simp) (fun s t => by rw [ofAdd_add, map_mul, map_mul]) fun t => toGAd_mem_infPts hσ W hc (hγ.2 _)`.
-/
theorem exists_lines_hasDerivAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x), IsCMExt F E σ → ∀ (d : ℕ) (W : Spc F E d) (c : E) (hc : c ≠ 0),
    ∀ γ ∈ Lines σ W, ∃ (r : ℕ) (β : Fin r → ℝ → GAd σ (c • W.J.map σ)), (∀ i, IsRealLine σ (c • W.J.map σ) (β i)) ∧
      ∀ f, IsSm σ (c • W.J.map σ) f → ∀ g,
        HasDerivAt (fun t : ℝ => f (g * toGAd hσ W.J hc (γ (Multiplicative.ofAdd t)))) (∑ i, lineDer (β i) f g) 0 := by
  intro F E _ _ _ _ _ σ hσ hcm d W c hc γ hγ
  have hs : Continuous (toGAd hσ W.J hc) := continuous_induced_rng.2 continuous_subtype_val
  exact exists_lines_of_infPts hcm _ (fun t => toGAd hσ W.J hc (γ (Multiplicative.ofAdd t)))
    (hs.comp (hγ.1.comp continuous_ofAdd)) (by simp) (fun s t => by rw [ofAdd_add, map_mul, map_mul])
    fun t => toGAd_mem_infPts hσ W hc (hγ.2 _)

end GlobalTheory.LineDerSum
