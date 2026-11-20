import Mathlib
import GroundTheory.AutomorphicForms.DixmierMalliavinBasic

namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open NormedSpace Set Filter

set_option linter.unusedSectionVars false

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]

noncomputable def prodExpVal {d : ℕ} (X : Fin d → 𝔸) (t : Fin d → ℝ) : 𝔸 :=
  (List.ofFn fun i => exp (t i • X i)).prod

/- English proof (translation)
Simplify using `[prodExpVal, List.ofFn_succ]`.
-/
theorem prodExpVal_succ {d : ℕ} (X : Fin (d + 1) → 𝔸) (t : Fin (d + 1) → ℝ) :
    prodExpVal X t = exp (t 0 • X 0) * prodExpVal (fun i => X i.succ) (fun i => t i.succ) := by
  simp [prodExpVal, List.ofFn_succ]

/- English proof (translation)
Simplify using `[prodExpVal]`.
-/
theorem prodExpVal_zero {d : ℕ} (X : Fin d → 𝔸) : prodExpVal X 0 = 1 := by
  simp [prodExpVal]

/- English proof (translation)
The claim follows from `prodExpVal_zero X`.
-/
theorem prodExpVal_zero' {d : ℕ} (X : Fin d → 𝔸) : prodExpVal X (fun _ => 0) = 1 :=
  prodExpVal_zero X

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero`. Establish `e : prodExpVal X = fun _ => 1` using `funext fun t => by simp [prodExpVal]`. Rewrite using `[e]`. Conclude with `contDiff_const`.

Consider the case `succ d ih`. Establish `e : prodExpVal X = fun t => exp (t 0 • X 0) * prodExpVal (fun i => X i.succ) (fun i => t i.succ)` using `funext (prodExpVal_succ X)`. Rewrite using `[e]`. Conclude with `((contDiff_exp ℝ 𝔸).comp ((contDiff_apply ℝ ℝ 0).smul contDiff_const)).mul ((ih _).comp (contDiff_pi.2 fun i => contDiff_apply ℝ ℝ i.succ))`.
-/
theorem contDiff_prodExpVal {d : ℕ} (X : Fin d → 𝔸) : ContDiff ℝ ∞ (prodExpVal X) := by
  induction d with
  | zero =>
    have e : prodExpVal X = fun _ => 1 := funext fun t => by simp [prodExpVal]
    rw [e]; exact contDiff_const
  | succ d ih =>
    have e : prodExpVal X = fun t => exp (t 0 • X 0) *
        prodExpVal (fun i => X i.succ) (fun i => t i.succ) := funext (prodExpVal_succ X)
    rw [e]
    exact ((contDiff_exp ℝ 𝔸).comp ((contDiff_apply ℝ ℝ 0).smul contDiff_const)).mul
      ((ih _).comp (contDiff_pi.2 fun i => contDiff_apply ℝ ℝ i.succ))

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero`. Establish `e : prodExpVal X = fun _ => 1` using `funext fun t => by simp [prodExpVal]`. Rewrite using `[e]`. Use `(hasFDerivAt_const (1 : 𝔸) (0 : Fin 0 → ℝ)).congr_fderiv ?_` and prove the remaining obligations.

Use extensionality with `t`. Simplify using the standard rewrite rules. Consider the case `succ d ih`. Establish `e : prodExpVal X = fun t => exp (t 0 • X 0) * prodExpVal (fun i => X i.succ) (fun i => t i.succ)` using `funext (prodExpVal_succ X)`. Rewrite using `[e]`.

Establish `hA : HasFDerivAt (fun t : Fin (d + 1) → ℝ => exp (t 0 • X 0)) ((ContinuousLinearMap.proj 0 : (Fin (d + 1) → ℝ) →L[ℝ] ℝ).smulRight (X 0)) 0`. Establish `hL : HasFDerivAt (fun t : Fin (d + 1) → ℝ => t 0 • X 0) ((ContinuousLinearMap.proj 0 : (Fin (d + 1) → ℝ) →L[ℝ] ℝ).smulRight (X 0)) 0` using `((ContinuousLinearMap.proj 0 : (Fin (d + 1) → ℝ) →L[ℝ] ℝ).smulRight (X 0)).hasFDerivAt`. Establish `hE : HasFDerivAt (exp : 𝔸 → 𝔸) (1 : 𝔸 →L[ℝ] 𝔸) ((0 : Fin (d + 1) → ℝ) 0 • X 0)`. Establish `: (0 : Fin (d + 1) → ℝ) 0 • X 0 = 0` using `by simp`. Rewrite using `[this]`.

Conclude with `hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)`. Conclude with `(hE.comp (0 : Fin (d + 1) → ℝ) hL).congr_fderiv (by ext t; simp)`. Set `T : (Fin (d + 1) → ℝ) →L[ℝ] (Fin d → ℝ)` to `ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ`. Establish `hB : HasFDerivAt (fun t : Fin (d + 1) → ℝ => prodExpVal (fun i => X i.succ) (fun i => t i.succ)) ((∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (X i.succ)).comp T) 0`. Establish `h0 : T 0 = 0` using `map_zero T`.

Use `(ih (fun i => X i.succ))` as an intermediate fact. Rewrite `this` using `[← h0]`. Conclude with `this.comp (0 : Fin (d + 1) → ℝ) (T.hasFDerivAt)`. Use `(hA.mul' hB).congr_fderiv ?_` and prove the remaining obligations. Use extensionality with `t`.

Simplify using `[T, Fin.sum_univ_succ, prodExpVal_zero']`. Rewrite using `[add_comm]`.
-/
theorem hasFDerivAt_prodExpVal_zero {d : ℕ} (X : Fin d → 𝔸) :
    HasFDerivAt (prodExpVal X)
      (∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (X i)) 0 := by
  induction d with
  | zero =>
    have e : prodExpVal X = fun _ => 1 := funext fun t => by simp [prodExpVal]
    rw [e]
    refine (hasFDerivAt_const (1 : 𝔸) (0 : Fin 0 → ℝ)).congr_fderiv ?_
    ext t; simp
  | succ d ih =>
    have e : prodExpVal X = fun t => exp (t 0 • X 0) *
        prodExpVal (fun i => X i.succ) (fun i => t i.succ) := funext (prodExpVal_succ X)
    rw [e]
    have hA : HasFDerivAt (fun t : Fin (d + 1) → ℝ => exp (t 0 • X 0))
        ((ContinuousLinearMap.proj 0 : (Fin (d + 1) → ℝ) →L[ℝ] ℝ).smulRight (X 0)) 0 := by
      have hL : HasFDerivAt (fun t : Fin (d + 1) → ℝ => t 0 • X 0)
          ((ContinuousLinearMap.proj 0 : (Fin (d + 1) → ℝ) →L[ℝ] ℝ).smulRight (X 0)) 0 :=
        ((ContinuousLinearMap.proj 0 : (Fin (d + 1) → ℝ) →L[ℝ] ℝ).smulRight (X 0)).hasFDerivAt
      have hE : HasFDerivAt (exp : 𝔸 → 𝔸) (1 : 𝔸 →L[ℝ] 𝔸) ((0 : Fin (d + 1) → ℝ) 0 • X 0) := by
        have : (0 : Fin (d + 1) → ℝ) 0 • X 0 = 0 := by simp
        rw [this]; exact hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)
      exact (hE.comp (0 : Fin (d + 1) → ℝ) hL).congr_fderiv (by ext t; simp)
    let T : (Fin (d + 1) → ℝ) →L[ℝ] (Fin d → ℝ) :=
      ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ
    have hB : HasFDerivAt (fun t : Fin (d + 1) → ℝ =>
        prodExpVal (fun i => X i.succ) (fun i => t i.succ))
        ((∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (X i.succ)).comp T)
        0 := by
      have h0 : T 0 = 0 := map_zero T
      have := (ih (fun i => X i.succ))
      rw [← h0] at this
      exact this.comp (0 : Fin (d + 1) → ℝ) (T.hasFDerivAt)
    refine (hA.mul' hB).congr_fderiv ?_
    ext t
    simp [T, Fin.sum_univ_succ, prodExpVal_zero']
    rw [add_comm]

/- English proof (translation)
Establish `hd : HasFDerivAt (expPartialHomeomorph ℝ 𝔸) ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) ((expPartialHomeomorph ℝ 𝔸).symm 1)`. Rewrite using `[expPartialHomeomorph_symm_one, coe_expPartialHomeomorph]`. Conclude with `(hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)).congr_fderiv (by ext; simp)`. Conclude with `((expPartialHomeomorph ℝ 𝔸).hasFDerivAt_symm (one_mem_expPartialHomeomorph_target ℝ 𝔸) hd).congr_fderiv (by ext; simp)`.
-/
theorem hasFDerivAt_expSymm_one :
    HasFDerivAt (expPartialHomeomorph ℝ 𝔸).symm (1 : 𝔸 →L[ℝ] 𝔸) 1 := by
  have hd : HasFDerivAt (expPartialHomeomorph ℝ 𝔸)
      ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸)
      ((expPartialHomeomorph ℝ 𝔸).symm 1) := by
    rw [expPartialHomeomorph_symm_one, coe_expPartialHomeomorph]
    exact (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)).congr_fderiv (by ext; simp)
  exact ((expPartialHomeomorph ℝ 𝔸).hasFDerivAt_symm
    (one_mem_expPartialHomeomorph_target ℝ 𝔸) hd).congr_fderiv (by ext; simp)

variable {𝔤 : Submodule ℝ 𝔸}

noncomputable def logCoord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (w : 𝔸) : Fin d → ℝ :=
  b.equivFun.toContinuousLinearEquiv (subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm w))

/- English proof (translation)
The claim follows from `(b.equivFun.toContinuousLinearEquiv.contDiff.comp (subspaceProj 𝔤).contDiff).comp_contDiffOn (contDiffOn_expPartialHomeomorph_symm ℝ 𝔸)`.
-/
theorem contDiffOn_logCoord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ContDiffOn ℝ ∞ (logCoord b) (expPartialHomeomorph ℝ 𝔸).target :=
  (b.equivFun.toContinuousLinearEquiv.contDiff.comp (subspaceProj 𝔤).contDiff).comp_contDiffOn
    (contDiffOn_expPartialHomeomorph_symm ℝ 𝔸)

/- English proof (translation)
Simplify using `[logCoord, expPartialHomeomorph_symm_one]`.
-/
theorem logCoord_one {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) : logCoord b (1 : 𝔸) = 0 := by
  simp [logCoord, expPartialHomeomorph_symm_one]

/- English proof (translation)
Establish `: (∑ i, t i • (b i : 𝔸)) = ((b.equivFun.symm t : 𝔤) : 𝔸)`. Rewrite using `[Module.Basis.equivFun_symm_apply]`. Simplify using the standard rewrite rules. Rewrite using `[this, subspaceProj_coe]`. Conclude with `b.equivFun.apply_symm_apply t`.
-/
theorem logCoord_coe_sum {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (t : Fin d → ℝ) :
    b.equivFun.toContinuousLinearEquiv (subspaceProj 𝔤 (∑ i, t i • (b i : 𝔸))) = t := by
  have : (∑ i, t i • (b i : 𝔸)) = ((b.equivFun.symm t : 𝔤) : 𝔸) := by
    rw [Module.Basis.equivFun_symm_apply]; simp
  rw [this, subspaceProj_coe]
  exact b.equivFun.apply_symm_apply t

noncomputable def prodExpCoord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (t : Fin d → ℝ) :
    Fin d → ℝ :=
  logCoord b (prodExpVal (fun i => (b i : 𝔸)) t)

/- English proof (translation)
Simplify using `[prodExpCoord, prodExpVal_zero, logCoord_one]`.
-/
theorem prodExpCoord_zero {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) : prodExpCoord b 0 = 0 := by
  simp [prodExpCoord, prodExpVal_zero, logCoord_one]

/- English proof (translation)
The claim follows from `(contDiffOn_logCoord b).comp (contDiff_prodExpVal _).contDiffOn (fun _ ht => ht)`.
-/
theorem contDiffOn_prodExpCoord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ContDiffOn ℝ ∞ (prodExpCoord b)
      {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ (expPartialHomeomorph ℝ 𝔸).target} :=
  (contDiffOn_logCoord b).comp (contDiff_prodExpVal _).contDiffOn (fun _ ht => ht)

/- English proof (translation)
The claim follows from `(expPartialHomeomorph ℝ 𝔸).open_target.preimage (contDiff_prodExpVal _).continuous`.
-/
theorem isOpen_prodExpCoord_domain {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    IsOpen {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ (expPartialHomeomorph ℝ 𝔸).target} :=
  (expPartialHomeomorph ℝ 𝔸).open_target.preimage (contDiff_prodExpVal _).continuous

/- English proof (translation)
Establish `hL : HasFDerivAt (fun w : 𝔸 => b.equivFun.toContinuousLinearEquiv (subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm w))) (((b.equivFun.toContinuousLinearEquiv : 𝔤 →L[ℝ] (Fin d → ℝ)).comp (subspaceProj 𝔤)).comp (1 : 𝔸 →L[ℝ] 𝔸)) (prodExpVal (fun i => (b i : 𝔸)) 0)`. Rewrite using `[prodExpVal_zero]`. Conclude with `(((b.equivFun.toContinuousLinearEquiv : 𝔤 →L[ℝ] (Fin d → ℝ)).comp (subspaceProj 𝔤)).hasFDerivAt).comp (1 : 𝔸) hasFDerivAt_expSymm_one`. Use `(hL.comp (0 : Fin d → ℝ) (hasFDerivAt_prodExpVal_zero _)).congr_fderiv ?_` and prove the remaining obligations. Use extensionality with `t : 1`.

Simplify using `using logCoord_coe_sum b t`.
-/
theorem hasFDerivAt_prodExpCoord_zero {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    HasFDerivAt (prodExpCoord b)
      ((ContinuousLinearEquiv.refl ℝ (Fin d → ℝ) : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) :
        (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) 0 := by
  have hL : HasFDerivAt (fun w : 𝔸 => b.equivFun.toContinuousLinearEquiv
      (subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm w)))
      (((b.equivFun.toContinuousLinearEquiv : 𝔤 →L[ℝ] (Fin d → ℝ)).comp (subspaceProj 𝔤)).comp
        (1 : 𝔸 →L[ℝ] 𝔸)) (prodExpVal (fun i => (b i : 𝔸)) 0) := by
    rw [prodExpVal_zero]
    exact (((b.equivFun.toContinuousLinearEquiv : 𝔤 →L[ℝ] (Fin d → ℝ)).comp
      (subspaceProj 𝔤)).hasFDerivAt).comp (1 : 𝔸) hasFDerivAt_expSymm_one
  refine (hL.comp (0 : Fin d → ℝ) (hasFDerivAt_prodExpVal_zero _)).congr_fderiv ?_
  ext t : 1
  simpa using logCoord_coe_sum b t

/- English proof (translation)
The claim follows from `(contDiffOn_prodExpCoord b).contDiffAt ((isOpen_prodExpCoord_domain b).mem_nhds (by simp [prodExpVal_zero, one_mem_expPartialHomeomorph_target]))`.
-/
theorem contDiffAt_prodExpCoord_zero {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ContDiffAt ℝ ∞ (prodExpCoord b) 0 :=
  (contDiffOn_prodExpCoord b).contDiffAt ((isOpen_prodExpCoord_domain b).mem_nhds
    (by simp [prodExpVal_zero, one_mem_expPartialHomeomorph_target]))

namespace IsExpLieAlgebra

variable {G : Subgroup 𝔸ˣ} (h : IsExpLieAlgebra G 𝔤)

/- English proof (translation)
Use `set Φ := prodExpCoord b with hΦdef`. Use `set U := {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ (expPartialHomeomorph ℝ 𝔸).target} with hUdef`. Establish `hU : IsOpen U` using `isOpen_prodExpCoord_domain b`. Establish `hΦU : ContDiffOn ℝ ∞ Φ U` using `contDiffOn_prodExpCoord b`. Set `F₀` to `(contDiffAt_prodExpCoord_zero b).toOpenPartialHomeomorph Φ (hasFDerivAt_prodExpCoord_zero b) (by simp)`.

Establish `hcont : ContinuousOn (fderiv ℝ Φ) U` using `hΦU.continuousOn_fderiv_of_isOpen hU (by simp)`. Establish `hS₁ : IsOpen (U ∩ fderiv ℝ Φ ⁻¹' {u | IsUnit u})` using `hcont.isOpen_inter_preimage hU Units.isOpen`. Establish `hN : IsOpen {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ h.nhdOne}` using `h.isOpen_nhdOne.preimage (contDiff_prodExpVal _).continuous`. Use `set S₂ := (U ∩ fderiv ℝ Φ ⁻¹' {u | IsUnit u}) ∩ {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ h.nhdOne} with hS₂def`. Establish `hS₂ : IsOpen S₂` using `hS₁.inter hN`.

Set `F` to `F₀.restrOpen S₂ hS₂`. Establish `hF : (F : (Fin d → ℝ) → (Fin d → ℝ)) = Φ` using `rfl`. Use `⟨F.source, F.target, F.symm, F.open_source, F.open_target, ?_, ?_, F.mapsTo_symm, fun z hz => F.left_inv hz, fun w hw => F.right_inv hw, ?_, ?_⟩` and prove the remaining obligations. Use `⟨(contDiffAt_prodExpCoord_zero b).mem_toOpenPartialHomeomorph_source _ _, ?_⟩` and prove the remaining obligations. Establish `h0 : prodExpVal (fun i => (b i : 𝔸)) 0 = 1` using `prodExpVal_zero _`.

Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show prodExpVal (fun i => (b i : 𝔸)) 0 ∈ (expPartialHomeomorph ℝ 𝔸).target`. Rewrite using `[h0]`. Conclude with `one_mem_expPartialHomeomorph_target ℝ 𝔸`. Use `show IsUnit (fderiv ℝ Φ 0)`.

Rewrite using `[(hasFDerivAt_prodExpCoord_zero b).fderiv]`. Conclude with `isUnit_one`. Use `show prodExpVal (fun i => (b i : 𝔸)) 0 ∈ h.nhdOne`. Rewrite using `[h0]`. Conclude with `h.one_mem_nhdOne`.

Introduce `z hz`. Rewrite using `[← hF]`. Conclude with `F.map_source hz`. Introduce `w hw`. Apply `ContDiffAt.contDiffWithinAt` to reduce the goal to its premises.

Establish `hz : F.symm w ∈ F.source` using `F.map_target hw`. Establish `hzS : F.symm w ∈ S₂` using `hz.2`. Establish `hu : IsUnit (fderiv ℝ Φ (F.symm w))` using `hzS.1.2`. Establish `hΦz : ContDiffAt ℝ ∞ Φ (F.symm w)` using `hΦU.contDiffAt (hU.mem_nhds hzS.1.1)`. Establish `hdiff : HasFDerivAt Φ (fderiv ℝ Φ (F.symm w)) (F.symm w)` using `(hΦz.differentiableAt (by simp)).hasFDerivAt`.

Establish `key : ((ContinuousLinearEquiv.unitsEquiv ℝ (Fin d → ℝ) hu.unit : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) = fderiv ℝ Φ (F.symm w)`. Use extensionality with `x`. Simplify using the standard rewrite rules. Conclude with `F.contDiffAt_symm hw (key ▸ hdiff) hΦz`. Introduce `z hz`.

Conclude with `hz.2.2`.
-/
theorem exists_prodExp_coord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ (S T : Set (Fin d → ℝ)) (ψ : (Fin d → ℝ) → (Fin d → ℝ)), IsOpen S ∧ IsOpen T ∧
      (0 : Fin d → ℝ) ∈ S ∧ MapsTo (prodExpCoord b) S T ∧ MapsTo ψ T S ∧
      (∀ z ∈ S, ψ (prodExpCoord b z) = z) ∧ (∀ w ∈ T, prodExpCoord b (ψ w) = w) ∧
      ContDiffOn ℝ ∞ ψ T ∧ (∀ z ∈ S, prodExpVal (fun i => (b i : 𝔸)) z ∈ h.nhdOne) := by
  set Φ := prodExpCoord b with hΦdef
  set U := {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ (expPartialHomeomorph ℝ 𝔸).target} with hUdef
  have hU : IsOpen U := isOpen_prodExpCoord_domain b
  have hΦU : ContDiffOn ℝ ∞ Φ U := contDiffOn_prodExpCoord b
  let F₀ := (contDiffAt_prodExpCoord_zero b).toOpenPartialHomeomorph Φ
    (hasFDerivAt_prodExpCoord_zero b) (by simp)
  have hcont : ContinuousOn (fderiv ℝ Φ) U := hΦU.continuousOn_fderiv_of_isOpen hU (by simp)
  have hS₁ : IsOpen (U ∩ fderiv ℝ Φ ⁻¹' {u | IsUnit u}) :=
    hcont.isOpen_inter_preimage hU Units.isOpen
  have hN : IsOpen {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ h.nhdOne} :=
    h.isOpen_nhdOne.preimage (contDiff_prodExpVal _).continuous
  set S₂ := (U ∩ fderiv ℝ Φ ⁻¹' {u | IsUnit u}) ∩
    {t | prodExpVal (fun i => (b i : 𝔸)) t ∈ h.nhdOne} with hS₂def
  have hS₂ : IsOpen S₂ := hS₁.inter hN
  let F := F₀.restrOpen S₂ hS₂
  have hF : (F : (Fin d → ℝ) → (Fin d → ℝ)) = Φ := rfl
  refine ⟨F.source, F.target, F.symm, F.open_source, F.open_target, ?_, ?_, F.mapsTo_symm,
    fun z hz => F.left_inv hz, fun w hw => F.right_inv hw, ?_, ?_⟩
  · refine ⟨(contDiffAt_prodExpCoord_zero b).mem_toOpenPartialHomeomorph_source _ _, ?_⟩
    have h0 : prodExpVal (fun i => (b i : 𝔸)) 0 = 1 := prodExpVal_zero _
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show prodExpVal (fun i => (b i : 𝔸)) 0 ∈ (expPartialHomeomorph ℝ 𝔸).target
      rw [h0]; exact one_mem_expPartialHomeomorph_target ℝ 𝔸
    · show IsUnit (fderiv ℝ Φ 0)
      rw [(hasFDerivAt_prodExpCoord_zero b).fderiv]
      exact isUnit_one
    · show prodExpVal (fun i => (b i : 𝔸)) 0 ∈ h.nhdOne
      rw [h0]; exact h.one_mem_nhdOne
  · intro z hz; rw [← hF]; exact F.map_source hz
  · intro w hw
    apply ContDiffAt.contDiffWithinAt
    have hz : F.symm w ∈ F.source := F.map_target hw
    have hzS : F.symm w ∈ S₂ := hz.2
    have hu : IsUnit (fderiv ℝ Φ (F.symm w)) := hzS.1.2
    have hΦz : ContDiffAt ℝ ∞ Φ (F.symm w) := hΦU.contDiffAt (hU.mem_nhds hzS.1.1)
    have hdiff : HasFDerivAt Φ (fderiv ℝ Φ (F.symm w)) (F.symm w) :=
      (hΦz.differentiableAt (by simp)).hasFDerivAt
    have key : ((ContinuousLinearEquiv.unitsEquiv ℝ (Fin d → ℝ) hu.unit :
        (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) =
        fderiv ℝ Φ (F.symm w) := by
      ext x; simp
    exact F.contDiffAt_symm hw (key ▸ hdiff) hΦz
  · intro z hz; exact hz.2.2

/- English proof (translation)
The claim follows from `Units.isOpenEmbedding_val.isEmbedding.comp Topology.IsEmbedding.subtypeVal`.
-/
theorem isEmbedding_coe_coe :
    Topology.IsEmbedding (fun x : G => ((x : 𝔸ˣ) : 𝔸)) :=
  Units.isOpenEmbedding_val.isEmbedding.comp Topology.IsEmbedding.subtypeVal

include h in

/- English proof (translation)
The claim follows from `isEmbedding_coe_coe.secondCountableTopology`.
-/
theorem secondCountableTopology : SecondCountableTopology G :=
  isEmbedding_coe_coe.secondCountableTopology

/- English proof (translation)
Set `f : G →* 𝔸` to `(Units.coeHom 𝔸).comp G.subtype`. Use `show f (List.ofFn fun i => h.expG (t i • X i)).prod = _`. Rewrite using `[map_list_prod, List.map_ofFn]`. Simplify using `[prodExpVal, f, Function.comp_def]`.
-/
theorem val_prodExp {d : ℕ} (X : Fin d → 𝔤) (t : Fin d → ℝ) :
    (((h.prodExp X t : G) : 𝔸ˣ) : 𝔸) = prodExpVal (fun i => (X i : 𝔸)) t := by
  let f : G →* 𝔸 := (Units.coeHom 𝔸).comp G.subtype
  show f (List.ofFn fun i => h.expG (t i • X i)).prod = _
  rw [map_list_prod, List.map_ofFn]
  simp [prodExpVal, f, Function.comp_def]

/- English proof (translation)
Rewrite using `[isEmbedding_coe_coe.continuous_iff]`. Establish `: (fun x : G => ((x : 𝔸ˣ) : 𝔸)) ∘ h.prodExp X = prodExpVal (fun i => (X i : 𝔸))`. Use function extensionality and compare the values at `fun t => h.val_prodExp X t`. Rewrite using `[this]`. Conclude with `(contDiff_prodExpVal _).continuous`.
-/
theorem continuous_prodExp {d : ℕ} (X : Fin d → 𝔤) : Continuous (h.prodExp X) := by
  rw [isEmbedding_coe_coe.continuous_iff]
  have : (fun x : G => ((x : 𝔸ˣ) : 𝔸)) ∘ h.prodExp X = prodExpVal (fun i => (X i : 𝔸)) :=
    funext fun t => h.val_prodExp X t
  rw [this]; exact (contDiff_prodExpVal _).continuous

/- English proof (translation)
Use `set w := logCoord b ((y : 𝔸ˣ) : 𝔸)`. Use `set z := ψ w`. Establish `hz : logCoord b (prodExpVal (fun i => (b i : 𝔸)) z) = w` using `hψT w hyT`. Establish `hPz : (((h.prodExp (⇑b) z : G) : 𝔸ˣ) : 𝔸) = prodExpVal (fun i => (b i : 𝔸)) z` using `h.val_prodExp _ z`. Establish `hzN : (((h.prodExp (⇑b) z : G) : 𝔸ˣ) : 𝔸) ∈ h.nhdOne` using `hPz ▸ hN w hyT`.

Establish `h1` using `h.symm_mem_lie hzN`. Establish `h2` using `h.symm_mem_lie hy`. Establish `e1 : subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm (((h.prodExp (⇑b) z : G) : 𝔸ˣ) : 𝔸)) = subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm ((y : 𝔸ˣ) : 𝔸))`. Apply `b.equivFun.toContinuousLinearEquiv.injective` to reduce the goal to its premises. Rewrite using `[hPz]`.

Conclude with `hz`. Establish `e2` using `congrArg Subtype.val e1`. Rewrite `e2` using `[subspaceProj_of_mem h1, subspaceProj_of_mem h2]`. Establish `e3` using `congrArg exp e2`. Rewrite `e3` using `[h.exp_symm hzN, h.exp_symm hy]`.

Conclude with `Subtype.ext (Units.ext e3)`.
-/
theorem prodExp_coord_eq {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) {T : Set (Fin d → ℝ)}
    {ψ : (Fin d → ℝ) → (Fin d → ℝ)} (hψT : ∀ w ∈ T, prodExpCoord b (ψ w) = w)
    (hN : ∀ w ∈ T, prodExpVal (fun i => (b i : 𝔸)) (ψ w) ∈ h.nhdOne) {y : G}
    (hy : ((y : 𝔸ˣ) : 𝔸) ∈ h.nhdOne) (hyT : logCoord b ((y : 𝔸ˣ) : 𝔸) ∈ T) :
    h.prodExp (⇑b) (ψ (logCoord b ((y : 𝔸ˣ) : 𝔸))) = y := by
  set w := logCoord b ((y : 𝔸ˣ) : 𝔸)
  set z := ψ w
  have hz : logCoord b (prodExpVal (fun i => (b i : 𝔸)) z) = w := hψT w hyT
  have hPz : (((h.prodExp (⇑b) z : G) : 𝔸ˣ) : 𝔸) = prodExpVal (fun i => (b i : 𝔸)) z :=
    h.val_prodExp _ z
  have hzN : (((h.prodExp (⇑b) z : G) : 𝔸ˣ) : 𝔸) ∈ h.nhdOne := hPz ▸ hN w hyT
  have h1 := h.symm_mem_lie hzN
  have h2 := h.symm_mem_lie hy
  have e1 : subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm
      (((h.prodExp (⇑b) z : G) : 𝔸ˣ) : 𝔸)) =
      subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm ((y : 𝔸ˣ) : 𝔸)) := by
    apply b.equivFun.toContinuousLinearEquiv.injective
    rw [hPz]; exact hz
  have e2 := congrArg Subtype.val e1
  rw [subspaceProj_of_mem h1, subspaceProj_of_mem h2] at e2
  have e3 := congrArg exp e2
  rw [h.exp_symm hzN, h.exp_symm hy] at e3
  exact Subtype.ext (Units.ext e3)

end IsExpLieAlgebra

/- English proof (translation)
Establish `e : (fun f : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => f.det) = fun f => ∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, f (Pi.single i 1) (σ i)`. Use function extensionality and compare the values at `f`. Rewrite using `[ContinuousLinearMap.det, ← LinearMap.det_toMatrix', Matrix.det_apply]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def, zsmul_eq_mul]`.

Use `congr 1`. Rewrite using `[e]`. Use `ContDiff.sum fun σ _ => contDiff_const.mul ?_` and prove the remaining obligations. Use `contDiff_prod fun i _ => ?_` and prove the remaining obligations. Conclude with `((ContinuousLinearMap.proj (σ i) : (Fin d → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.apply ℝ (Fin d → ℝ) (Pi.single i (1 : ℝ) : Fin d → ℝ) : ((Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) →L[ℝ] (Fin d → ℝ))).contDiff`.
-/
theorem contDiff_det_pi {d : ℕ} :
    ContDiff ℝ ∞ (fun f : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => f.det) := by
  have e : (fun f : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => f.det) = fun f =>
      ∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, f (Pi.single i 1) (σ i) := by
    funext f
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    congr 1
  rw [e]
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  refine contDiff_prod fun i _ => ?_
  exact ((ContinuousLinearMap.proj (σ i) : (Fin d → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.apply ℝ (Fin d → ℝ) (Pi.single i (1 : ℝ) : Fin d → ℝ) :
      ((Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) →L[ℝ] (Fin d → ℝ))).contDiff

/- English proof (translation)
Rewrite using `[contDiff_iff_contDiffAt]`. Introduce `x`. Distinguish the cases in `hx : x ∈ O`. Conclude with `hg.contDiffAt.smul (hf.contDiffAt (hO.mem_nhds hx))`. Establish `hx' : x ∉ tsupport g` using `fun h' => hx (hgO h')`.

Establish `: (fun x => g x • f x) =ᶠ[𝓝 x] fun _ => 0` using `by filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy`. Simplify using `[hy]`. Conclude with `contDiffAt_const.congr_of_eventuallyEq this`.
-/
theorem contDiff_smul_of_tsupport {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {O : Set V} (hO : IsOpen O) {f : V → F}
    {g : V → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiff ℝ ∞ g) (hgO : tsupport g ⊆ O) :
    ContDiff ℝ ∞ (fun x => g x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ O
  · exact hg.contDiffAt.smul (hf.contDiffAt (hO.mem_nhds hx))
  · have hx' : x ∉ tsupport g := fun h' => hx (hgO h')
    have : (fun x => g x • f x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq this

open MeasureTheory in

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `W F _ _ _ _ _ Ξ hΞ hc`. Take `⟨C, hC⟩` from `hΞ.continuous.bounded_above_of_compact_support hc`. Rewrite using `[Nat.cast_zero, contDiff_zero]`.

Use `continuous_of_dominated (bound := fun _ => C) (fun z => ?_) (fun z => ?_) (integrable_const C) (Eventually.of_forall fun a => ?_)` and prove the remaining obligations. Conclude with `(hΞ.continuous.comp (hu.prodMk continuous_const)).aestronglyMeasurable`. Conclude with `Eventually.of_forall fun a => hC _`. Conclude with `hΞ.continuous.comp (continuous_const.prodMk continuous_id)`. Consider the case `succ n ih`.

Introduce `W F _ _ _ _ _ Ξ hΞ hc`. Use `set Ξ' : V × W → (W →L[ℝ] F) := fun q => (fderiv ℝ Ξ q).comp (ContinuousLinearMap.inr ℝ V W) with hΞ'def`. Establish `hΞ'c : ContDiff ℝ ∞ Ξ'` using `ContDiff.clm_comp (𝕜 := ℝ) (g := fun q => fderiv ℝ Ξ q) (f := fun _ => ContinuousLinearMap.inr ℝ V W) (hΞ.fderiv_right (m := ∞) (by simp)) contDiff_const`. Establish `hΞ's : HasCompactSupport Ξ'` using `(hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : V × W →L[ℝ] F => L.comp (ContinuousLinearMap.inr ℝ V W)) (ContinuousLinearMap.zero_comp _)`. Take `⟨C, hC⟩` from `hΞ'c.continuous.bounded_above_of_compact_support hΞ's`.

Take `⟨C₀, hC₀⟩` from `hΞ.continuous.bounded_above_of_compact_support hc`. Establish `hdiff : ∀ (v : V) (z : W), HasFDerivAt (fun z => Ξ (v, z)) (Ξ' (v, z)) z`. Introduce `v z`. Establish `h1 : HasFDerivAt Ξ (fderiv ℝ Ξ (v, z)) (v, z)` using `((hΞ.differentiable (by simp)) (v, z)).hasFDerivAt`. Conclude with `h1.comp z ((hasFDerivAt_const v z).prodMk (hasFDerivAt_id z))`.

Rewrite using `[Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]`. Use `⟨fun z => ∫ x, Ξ' (u x, z) ∂ν, ih Ξ' hΞ'c hΞ's, fun z₀ => ?_⟩` and prove the remaining obligations. Use `hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ) (bound := fun _ => C) (F := fun z a => Ξ (u a, z)) (F' := fun z a => Ξ' (u a, z)) univ_mem (Eventually.of_forall fun z => ?_) ?_ ?_ ?_ (integrable_const C) ?_` and prove the remaining obligations. Conclude with `(hΞ.continuous.comp (hu.prodMk continuous_const)).aestronglyMeasurable`. Conclude with `Integrable.of_bound (hΞ.continuous.comp (hu.prodMk continuous_const)).aestronglyMeasurable C₀ (Eventually.of_forall fun a => hC₀ _)`.

Conclude with `(hΞ'c.continuous.comp (hu.prodMk continuous_const)).aestronglyMeasurable`. Conclude with `Eventually.of_forall fun a z _ => hC _`. Conclude with `Eventually.of_forall fun a z _ => hdiff (u a) z`.
-/
theorem contDiff_integral_comp_of_hasCompactSupport {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopology X] (ν : Measure X)
    [IsFiniteMeasure ν] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {u : X → V}
    (hu : Continuous u) (n : ℕ) :
    ∀ {W F : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup F]
      [NormedSpace ℝ F] [CompleteSpace F] (Ξ : V × W → F), ContDiff ℝ ∞ Ξ → HasCompactSupport Ξ →
      ContDiff ℝ n (fun z => ∫ x, Ξ (u x, z) ∂ν) := by
  induction n with
  | zero =>
    intro W F _ _ _ _ _ Ξ hΞ hc
    obtain ⟨C, hC⟩ := hΞ.continuous.bounded_above_of_compact_support hc
    rw [Nat.cast_zero, contDiff_zero]
    refine continuous_of_dominated (bound := fun _ => C) (fun z => ?_) (fun z => ?_)
      (integrable_const C) (Eventually.of_forall fun a => ?_)
    · exact (hΞ.continuous.comp (hu.prodMk continuous_const)).aestronglyMeasurable
    · exact Eventually.of_forall fun a => hC _
    · exact hΞ.continuous.comp (continuous_const.prodMk continuous_id)
  | succ n ih =>
    intro W F _ _ _ _ _ Ξ hΞ hc
    set Ξ' : V × W → (W →L[ℝ] F) := fun q => (fderiv ℝ Ξ q).comp (ContinuousLinearMap.inr ℝ V W)
      with hΞ'def
    have hΞ'c : ContDiff ℝ ∞ Ξ' :=
      ContDiff.clm_comp (𝕜 := ℝ) (g := fun q => fderiv ℝ Ξ q)
        (f := fun _ => ContinuousLinearMap.inr ℝ V W)
        (hΞ.fderiv_right (m := ∞) (by simp)) contDiff_const
    have hΞ's : HasCompactSupport Ξ' :=
      (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : V × W →L[ℝ] F => L.comp (ContinuousLinearMap.inr ℝ V W))
        (ContinuousLinearMap.zero_comp _)
    obtain ⟨C, hC⟩ := hΞ'c.continuous.bounded_above_of_compact_support hΞ's
    obtain ⟨C₀, hC₀⟩ := hΞ.continuous.bounded_above_of_compact_support hc
    have hdiff : ∀ (v : V) (z : W), HasFDerivAt (fun z => Ξ (v, z)) (Ξ' (v, z)) z := by
      intro v z
      have h1 : HasFDerivAt Ξ (fderiv ℝ Ξ (v, z)) (v, z) :=
        ((hΞ.differentiable (by simp)) (v, z)).hasFDerivAt
      exact h1.comp z ((hasFDerivAt_const v z).prodMk (hasFDerivAt_id z))
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun z => ∫ x, Ξ' (u x, z) ∂ν, ih Ξ' hΞ'c hΞ's, fun z₀ => ?_⟩
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ) (bound := fun _ => C)
      (F := fun z a => Ξ (u a, z)) (F' := fun z a => Ξ' (u a, z))
      univ_mem (Eventually.of_forall fun z => ?_) ?_ ?_ ?_ (integrable_const C) ?_
    · exact (hΞ.continuous.comp (hu.prodMk continuous_const)).aestronglyMeasurable
    · exact Integrable.of_bound
        (hΞ.continuous.comp (hu.prodMk continuous_const)).aestronglyMeasurable C₀
        (Eventually.of_forall fun a => hC₀ _)
    · exact (hΞ'c.continuous.comp (hu.prodMk continuous_const)).aestronglyMeasurable
    · exact Eventually.of_forall fun a z _ => hC _
    · exact Eventually.of_forall fun a z _ => hdiff (u a) z

end GroundTheory.Automorphic
