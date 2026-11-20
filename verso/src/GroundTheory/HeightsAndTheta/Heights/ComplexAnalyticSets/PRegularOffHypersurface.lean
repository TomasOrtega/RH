import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularOffHypersurface
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RegularLocus
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFrameGraphGeneric
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

/- English proof (translation)
Establish `: J.IsPrime` using `hJ`. Establish `hge : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J)` using `ringKrullDim_nonneg_of_nontrivial`. Establish `hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : WithBot ℕ∞)`. Use `(ringKrullDim_quotient_le J).trans ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]`.

Generalize the expression as in `ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = x at hge hle`. Proceed by induction on `x using WithBot.recBotCoe with`. Consider the case `bot => exact absurd hge (by simp)`. Consider the case `coe m`. Proceed by induction on `m using ENat.recTopCoe with`.

Consider the case `top => exact absurd hle (by norm_cast)`. Consider the case `coe d => exact ⟨d, rfl⟩`.
-/
theorem exists_ringKrullDim_quotient_eq_nat {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime) :
    ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by
  have : J.IsPrime := hJ
  have hge : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
    ringKrullDim_nonneg_of_nontrivial
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : WithBot ℕ∞) := by
    refine (ringKrullDim_quotient_le J).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
      Fintype.card_fin, zero_add]
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = x at hge hle
  induction x using WithBot.recBotCoe with
  | bot => exact absurd hge (by simp)
  | coe m =>
    induction m using ENat.recTopCoe with
    | top => exact absurd hle (by norm_cast)
    | coe d => exact ⟨d, rfl⟩

/- English proof (translation)
Introduce `y hy`. Use `AnalyticAt.pi fun s => ?_` and prove the remaining obligations. Establish `hs : DifferentiableOn ℂ (fun x => G x s) U` using `(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) s).differentiable.comp_differentiableOn hG`. Use `analyticOnNhd_of_continuousOn_of_separately hU hs.continuousOn (fun z hz i => ?_) y hy` and prove the remaining obligations. Establish `h1 : DifferentiableAt ℂ (fun x => G x s) (Function.update z i (z i))`.

Rewrite using `[Function.update_eq_self]`. Conclude with `hs.differentiableAt (hU.mem_nhds hz)`. Conclude with `h1.comp (z i) (hasFDerivAt_update (𝕜 := ℂ) z (z i)).differentiableAt`.
-/
theorem analyticOnNhd_of_differentiableOn_fin {d : ℕ} {σ : Type} [Fintype σ] {U : Set (Fin d → ℂ)}
    {G : (Fin d → ℂ) → σ → ℂ} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U) : AnalyticOnNhd ℂ G U := by
  intro y hy
  refine AnalyticAt.pi fun s => ?_
  have hs : DifferentiableOn ℂ (fun x => G x s) U :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) s).differentiable.comp_differentiableOn hG
  refine analyticOnNhd_of_continuousOn_of_separately hU hs.continuousOn (fun z hz i => ?_) y hy
  have h1 : DifferentiableAt ℂ (fun x => G x s) (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact hs.differentiableAt (hU.mem_nhds hz)
  exact h1.comp (z i) (hasFDerivAt_update (𝕜 := ℂ) z (z i)).differentiableAt

/- English proof (translation)
Introduce `σ _ I hI`. Use `set n := Fintype.card σ`. Use `set e : σ ≃ Fin n := Fintype.equivFin σ`. Use `set φ : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ := renameEquiv ℂ e.symm`. Use `set J : Ideal (MvPolynomial (Fin n) ℂ) := I.comap φ`.

Establish `hJ : J.IsPrime` using `Ideal.IsPrime.comap _`. Establish `hφ : ∀ (x : σ → ℂ) (q : MvPolynomial (Fin n) ℂ), eval x (φ q) = eval (x ∘ e.symm) q` using `fun x q => by`. Simplify using `[φ, eval_rename]`. Take `⟨d, hd⟩` from `exists_ringKrullDim_quotient_eq_nat J hJ`. Set `b` to `EuclideanSpace.basisFun (Fin n) ℂ`.

Take `⟨I₀, q, hcard, hqJ, hreg⟩` from `hG n d J hJ hd b`. Set `T : (σ → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)` to `((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).comp (ContinuousLinearMap.pi fun i : Fin n => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm i))`. Set `S : EuclideanSpace ℂ (Fin n) →L[ℂ] (σ → ℂ)` to `(ContinuousLinearMap.pi fun s : σ => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (e s)).comp ((EuclideanSpace.equiv (Fin n) ℂ : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)))`. Establish `hT : ∀ x i, T x i = x (e.symm i)` using `fun x i => rfl`. Establish `hS : ∀ w s, S w s = w (e s)` using `fun w s => rfl`.

Establish `hST : ∀ x, S (T x) = x` using `fun x => funext fun s => by simp [hS, hT]`. Establish `hTS : ∀ w, T (S w) = w` using `fun w => by ext i; simp [hS, hT]`. Establish `hZ : ∀ x : σ → ℂ, x ∈ zeroSetIn I ↔ T x ∈ zeroSetEuc J`. Introduce `x`. Establish `hx : (fun i => T x i) = x ∘ e.symm` using `rfl`.

Simplify using `only [zeroSetIn, zeroSetEuc, Set.mem_ofPred_eq, hx]`. Prove the components needed by the constructor for the conclusion. Introduce `h p hp`. Rewrite using `[← hφ]`. Conclude with `h _ (Ideal.mem_comap.mp hp)`.

Introduce `h p hp`. Use `h (φ.symm p) (by simpa [J, Ideal.mem_comap] using hp)` as an intermediate fact. Rewrite `this` using `[← hφ, AlgEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Use `⟨φ q, fun h => hqJ (Ideal.mem_comap.mpr h), ?_⟩` and prove the remaining obligations. Introduce `z hz hzh`.

Take `⟨Ω, V, g, hΩ, hV, hzV, hg, hproj, hgraph⟩` from `hreg (T z) ((hZ z).mp hz) (by rwa [hφ] at hzh)`. Set `eI : I₀ ≃ Fin d` to `I₀.equivFinOfCardEq hcard`. Set `Ψ : (Fin d → ℂ) →L[ℂ] (I₀ → ℂ)` to `ContinuousLinearMap.pi fun i : I₀ => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) (eI i)`. Set `A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)` to `ContinuousLinearMap.pi fun k : Fin d => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm (eI.symm k))`. Establish `hΨ : ∀ y i, Ψ y i = y (eI i)` using `fun y i => rfl`.

Establish `hA : ∀ x k, A x k = x (e.symm (eI.symm k))` using `fun x k => rfl`. Establish `hO : IsOpen (Ψ ⁻¹' Ω)` using `hΩ.preimage Ψ.continuous`. Use `⟨hz, d, A, Ψ ⁻¹' Ω, T ⁻¹' V, fun y => S (g (Ψ y)), hO, hV.preimage T.continuous, hzV, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `analyticOnNhd_of_differentiableOn_fin hO (S.differentiable.comp_differentiableOn (hg.comp Ψ.differentiable.differentiableOn fun y hy => hy))`. Introduce `y hy`.

Use extensionality with `k`. Establish `h1` using `congrFun (hproj (Ψ y) hy) (eI.symm k)`. Simplify using `only [frameProj, b, EuclideanSpace.basisFun_inner] at h1`. Use `show A (S (g (Ψ y))) k = y k`. Rewrite using `[hA, hS, Equiv.apply_symm_apply, h1, hΨ, Equiv.apply_symm_apply]`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hxZ, hxV⟩`. Establish `hmem : T x ∈ zeroSetEuc J ∩ V` using `⟨(hZ x).mp hxZ, hxV⟩`. Rewrite `hmem` using `[hgraph]`.

Take `⟨u, hu, hgu⟩` from `hmem`. Establish `hΨu : Ψ (fun k => u (eI.symm k)) = u` using `funext fun i => by simp [hΨ]`. Use `⟨fun k => u (eI.symm k), ?_, ?_⟩` and prove the remaining obligations. Use `show Ψ _ ∈ Ω`. Rewrite using `[hΨu]` and apply the resulting hypothesis.

Simplify using `only [hΨu, hgu, hST]`. Introduce and unpack `⟨y, hy, rfl⟩`. Establish `hmem : g (Ψ y) ∈ zeroSetEuc J ∩ V` using `hgraph ▸ Set.mem_image_of_mem g hy`. Use `⟨(hZ _).mpr ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hTS]`.

Conclude with `hmem.1`. Use `show T (S (g (Ψ y))) ∈ V`. Rewrite using `[hTS]`. Conclude with `hmem.2`.
-/
theorem RegularOffHypersurface.proof (hG : FrameGraphGeneric.Statement) : RegularOffHypersurface.Statement := by
  intro σ _ I hI
  set n := Fintype.card σ
  set e : σ ≃ Fin n := Fintype.equivFin σ
  set φ : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ := renameEquiv ℂ e.symm
  set J : Ideal (MvPolynomial (Fin n) ℂ) := I.comap φ
  have hJ : J.IsPrime := Ideal.IsPrime.comap _
  have hφ : ∀ (x : σ → ℂ) (q : MvPolynomial (Fin n) ℂ), eval x (φ q) = eval (x ∘ e.symm) q := fun x q => by
    simp [φ, eval_rename]
  obtain ⟨d, hd⟩ := exists_ringKrullDim_quotient_eq_nat J hJ
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, q, hcard, hqJ, hreg⟩ := hG n d J hJ hd b

  let T : (σ → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    ((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).comp
      (ContinuousLinearMap.pi fun i : Fin n => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm i))
  let S : EuclideanSpace ℂ (Fin n) →L[ℂ] (σ → ℂ) :=
    (ContinuousLinearMap.pi fun s : σ => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (e s)).comp
      ((EuclideanSpace.equiv (Fin n) ℂ : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)))
  have hT : ∀ x i, T x i = x (e.symm i) := fun x i => rfl
  have hS : ∀ w s, S w s = w (e s) := fun w s => rfl
  have hST : ∀ x, S (T x) = x := fun x => funext fun s => by simp [hS, hT]
  have hTS : ∀ w, T (S w) = w := fun w => by ext i; simp [hS, hT]
  have hZ : ∀ x : σ → ℂ, x ∈ zeroSetIn I ↔ T x ∈ zeroSetEuc J := by
    intro x
    have hx : (fun i => T x i) = x ∘ e.symm := rfl
    simp only [zeroSetIn, zeroSetEuc, Set.mem_ofPred_eq, hx]
    constructor
    · intro h p hp
      rw [← hφ]
      exact h _ (Ideal.mem_comap.mp hp)
    · intro h p hp
      have := h (φ.symm p) (by simpa [J, Ideal.mem_comap] using hp)
      rwa [← hφ, AlgEquiv.apply_symm_apply] at this
  refine ⟨φ q, fun h => hqJ (Ideal.mem_comap.mpr h), ?_⟩
  intro z hz hzh
  obtain ⟨Ω, V, g, hΩ, hV, hzV, hg, hproj, hgraph⟩ :=
    hreg (T z) ((hZ z).mp hz) (by rwa [hφ] at hzh)
  let eI : I₀ ≃ Fin d := I₀.equivFinOfCardEq hcard
  let Ψ : (Fin d → ℂ) →L[ℂ] (I₀ → ℂ) :=
    ContinuousLinearMap.pi fun i : I₀ => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) (eI i)
  let A : (σ → ℂ) →L[ℂ] (Fin d → ℂ) :=
    ContinuousLinearMap.pi fun k : Fin d =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm (eI.symm k))
  have hΨ : ∀ y i, Ψ y i = y (eI i) := fun y i => rfl
  have hA : ∀ x k, A x k = x (e.symm (eI.symm k)) := fun x k => rfl
  have hO : IsOpen (Ψ ⁻¹' Ω) := hΩ.preimage Ψ.continuous
  refine ⟨hz, d, A, Ψ ⁻¹' Ω, T ⁻¹' V, fun y => S (g (Ψ y)), hO, hV.preimage T.continuous, hzV, ?_, ?_, ?_⟩
  · exact analyticOnNhd_of_differentiableOn_fin hO (S.differentiable.comp_differentiableOn
      (hg.comp Ψ.differentiable.differentiableOn fun y hy => hy))
  · intro y hy
    ext k
    have h1 := congrFun (hproj (Ψ y) hy) (eI.symm k)
    simp only [frameProj, b, EuclideanSpace.basisFun_inner] at h1
    show A (S (g (Ψ y))) k = y k
    rw [hA, hS, Equiv.apply_symm_apply, h1, hΨ, Equiv.apply_symm_apply]
  · ext x
    constructor
    · rintro ⟨hxZ, hxV⟩
      have hmem : T x ∈ zeroSetEuc J ∩ V := ⟨(hZ x).mp hxZ, hxV⟩
      rw [hgraph] at hmem
      obtain ⟨u, hu, hgu⟩ := hmem
      have hΨu : Ψ (fun k => u (eI.symm k)) = u := funext fun i => by simp [hΨ]
      refine ⟨fun k => u (eI.symm k), ?_, ?_⟩
      · show Ψ _ ∈ Ω
        rwa [hΨu]
      · simp only [hΨu, hgu, hST]
    · rintro ⟨y, hy, rfl⟩
      have hmem : g (Ψ y) ∈ zeroSetEuc J ∩ V := hgraph ▸ Set.mem_image_of_mem g hy
      refine ⟨(hZ _).mpr ?_, ?_⟩
      · rw [hTS]; exact hmem.1
      · show T (S (g (Ψ y))) ∈ V
        rw [hTS]; exact hmem.2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
