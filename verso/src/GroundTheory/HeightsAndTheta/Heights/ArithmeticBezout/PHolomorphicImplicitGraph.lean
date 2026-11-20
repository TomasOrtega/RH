import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsHolomorphicImplicitGraph
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module Function

noncomputable section

namespace HolomorphicImplicitGraph

/- English proof (translation)
Establish `hmn : m ≤ n`. Use `Submodule.finrank_le (LinearMap.ker L)` as an intermediate fact. Simplify `this` using `[hL]`. Establish `hrange : LinearMap.range L = ⊤`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises.

Use `LinearMap.finrank_range_add_finrank_ker L` as an intermediate fact. Simplify using `only [finrank_euclideanSpace_fin, hL] at this`. Simplify using `only [Module.finrank_fin_fun]`. Use linear arithmetic over natural numbers and integers. Set `w : Fin n → (Fin (n - m) → ℂ)` to `fun j => L (EuclideanSpace.single j 1)`.

Establish `hw : Submodule.span ℂ (Set.range w) = ⊤`. Rewrite using `[← hrange, LinearMap.range_eq_map, ← (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.span_eq, Submodule.map_span, ← Set.range_comp]`. Use `congr 2`. Use extensionality with `j`. Simplify using `[w]`.

Take `⟨κ, a, ha, hsp, hli⟩` from `exists_linearIndependent' ℂ w`. Establish `: Finite κ` using `Finite.of_injective a ha`. Set `: Fintype κ` to `Fintype.ofFinite κ`. Establish `hcardκ : Fintype.card κ = n - m`. Use `finrank_span_eq_card hli` as an intermediate fact.

Rewrite `this` using `[hsp, hw, finrank_top, Module.finrank_fin_fun]`. Conclude with `this.symm`. Set `s : Set (Fin n)` to `Set.range a`. Establish `hcs : Fintype.card s = n - m`. Rewrite using `[← hcardκ]`.

Conclude with `Fintype.card_congr (Equiv.ofInjective a ha).symm`. Establish `hcc : Fintype.card (sᶜ : Set (Fin n)) = m`. Rewrite using `[Fintype.card_compl_set, hcs, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Set `eS : s ≃ Fin (n - m)` to `Fintype.equivFinOfCardEq hcs`.

Set `eM : (sᶜ : Set (Fin n)) ≃ Fin m` to `Fintype.equivFinOfCardEq hcc`. Set `e : Fin n ≃ Fin m ⊕ Fin (n - m)` to `(Equiv.Set.sumCompl s).symm.trans ((Equiv.sumComm _ _).trans (Equiv.sumCongr eM eS))`. Use `⟨e, fun v hv hLv => ?_⟩` and prove the remaining obligations. Establish `hout : ∀ j ∉ s, v j = 0` using `fun j hj => hv j (eM ⟨j, hj⟩) (by simp [e, Equiv.Set.sumCompl_symm_apply_of_notMem hj])`. Establish `hv' : L v = ∑ j, v j • w j` using `by conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr v]`.

Simplify using `[w, map_sum, map_smul]`. Establish `hsum : ∑ c, v (a c) • w (a c) = 0`. Rewrite using `[Fintype.sum_of_injective a ha (fun c => v (a c) • w (a c)) (fun j => v j • w j) (fun j hj => by rw [hout j hj, zero_smul]) (fun c => rfl), ← hv', hLv]`. Establish `hin : ∀ c, v (a c) = 0` using `Fintype.linearIndependent_iff.1 hli (fun c => v (a c)) hsum`. Use `PiLp.ext fun j => ?_` and prove the remaining obligations.

Distinguish the cases in `hj : j ∈ s`. Take `⟨c, rfl⟩` from `hj`. Simplify using `using hin c`. Simplify using `using hout j hj`.
-/
theorem exists_coordSplitting {n m : ℕ} (L : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin (n - m) → ℂ))
    (hL : finrank ℂ (LinearMap.ker L) = m) :
    ∃ e : Fin n ≃ Fin m ⊕ Fin (n - m), ∀ v : EuclideanSpace ℂ (Fin n),
      (∀ j k, e j = Sum.inl k → v j = 0) → L v = 0 → v = 0 := by
  classical
  have hmn : m ≤ n := by
    have := Submodule.finrank_le (LinearMap.ker L)
    simpa [hL] using this
  have hrange : LinearMap.range L = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := LinearMap.finrank_range_add_finrank_ker L
    simp only [finrank_euclideanSpace_fin, hL] at this
    simp only [Module.finrank_fin_fun]
    omega
  let w : Fin n → (Fin (n - m) → ℂ) := fun j => L (EuclideanSpace.single j 1)
  have hw : Submodule.span ℂ (Set.range w) = ⊤ := by
    rw [← hrange, LinearMap.range_eq_map, ← (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.span_eq,
      Submodule.map_span, ← Set.range_comp]
    congr 2
    ext j
    simp [w]
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' ℂ w
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcardκ : Fintype.card κ = n - m := by
    have := finrank_span_eq_card hli
    rw [hsp, hw, finrank_top, Module.finrank_fin_fun] at this
    exact this.symm
  let s : Set (Fin n) := Set.range a
  have hcs : Fintype.card s = n - m := by
    rw [← hcardκ]
    exact Fintype.card_congr (Equiv.ofInjective a ha).symm
  have hcc : Fintype.card (sᶜ : Set (Fin n)) = m := by
    rw [Fintype.card_compl_set, hcs, Fintype.card_fin]
    omega
  let eS : s ≃ Fin (n - m) := Fintype.equivFinOfCardEq hcs
  let eM : (sᶜ : Set (Fin n)) ≃ Fin m := Fintype.equivFinOfCardEq hcc
  let e : Fin n ≃ Fin m ⊕ Fin (n - m) :=
    (Equiv.Set.sumCompl s).symm.trans ((Equiv.sumComm _ _).trans (Equiv.sumCongr eM eS))
  refine ⟨e, fun v hv hLv => ?_⟩
  have hout : ∀ j ∉ s, v j = 0 := fun j hj =>
    hv j (eM ⟨j, hj⟩) (by simp [e, Equiv.Set.sumCompl_symm_apply_of_notMem hj])
  have hv' : L v = ∑ j, v j • w j := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr v]
    simp [w, map_sum, map_smul]
  have hsum : ∑ c, v (a c) • w (a c) = 0 := by
    rw [Fintype.sum_of_injective a ha (fun c => v (a c) • w (a c)) (fun j => v j • w j)
      (fun j hj => by rw [hout j hj, zero_smul]) (fun c => rfl), ← hv', hLv]
  have hin : ∀ c, v (a c) = 0 := Fintype.linearIndependent_iff.1 hli (fun c => v (a c)) hsum
  refine PiLp.ext fun j => ?_
  by_cases hj : j ∈ s
  · obtain ⟨c, rfl⟩ := hj
    simpa using hin c
  · simpa using hout j hj

end HolomorphicImplicitGraph

/- English proof (translation)
Introduce `n m f y V hf hV hyV hfy hK`. Set `L : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin (n - m) → ℂ)` to `LinearMap.pi fun i => (fderiv ℂ (f i) y : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ)`. Take `⟨e, he⟩` from `exists_coordSplitting L (by rw [LinearMap.ker_pi]; exact hK)`. Set `F : EuclideanSpace ℂ (Fin n) → (Fin n → ℂ)` to `fun z j => Sum.elim (fun _ => z j) (fun i => f i z) (e j)`. Set `D : EuclideanSpace ℂ (Fin n) → (EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ))` to `fun z => ContinuousLinearMap.pi fun j => Sum.elim (fun _ => EuclideanSpace.proj j) (fun i => fderiv ℂ (f i) z) (e j)`.

Establish `hFd : ∀ z, HasFDerivAt F (D z) z`. Introduce `z`. Use `hasFDerivAt_pi.2 fun j => ?_` and prove the remaining obligations. Break down `h : e j with k | i` into its components or cases. Simplify using `only [Sum.elim_inl]`.

Conclude with `(EuclideanSpace.proj (𝕜 := ℂ) j).hasFDerivAt`. Simplify using `only [Sum.elim_inr]`. Conclude with `((hf i).differentiable one_ne_zero z).hasFDerivAt`. Establish `hFc : ContDiff ℂ 1 F`. Use `contDiff_pi.2 fun j => ?_` and prove the remaining obligations.

Break down `h : e j with k | i` into its components or cases. Simplify using `only [F, h, Sum.elim_inl]`. Conclude with `(EuclideanSpace.proj (𝕜 := ℂ) j).contDiff`. Simplify using `only [F, h, Sum.elim_inr]`. Conclude with `hf i`.

Establish `hDy : Injective (D y)`. Use `(injective_iff_map_eq_zero (D y)).2 fun v hv => he v (fun j k hj => ?_) ?_` and prove the remaining obligations. Use `congr_fun hv j` as an intermediate fact. Simplify `this` using `[D, hj]`. Use function extensionality and compare the values at `i`.

Use `congr_fun hv (e.symm (Sum.inr i))` as an intermediate fact. Simplify `this` using `[D, L]`. Set `A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ)` to `(LinearEquiv.ofInjectiveOfFinrankEq (D y : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ)) hDy (by simp)).toContinuousLinearEquiv`. Establish `hA : (A : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)) = D y` using `by ext1 v`. Both sides reduce to the same expression.

Set `P` to `hFc.contDiffAt.toOpenPartialHomeomorph F (f' := A) (by rw [hA]; exact hFd y) one_ne_zero`. Set `W : Set (EuclideanSpace ℂ (Fin n))` to `(fun z => fderiv ℂ F z) ⁻¹' Set.range ((↑) : (EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ)) → _)`. Establish `hW : IsOpen W` using `ContinuousLinearEquiv.isOpen.preimage (hFc.continuous_fderiv one_ne_zero)`. Establish `hyW : y ∈ W` using `⟨A, by rw [hA]; exact (hFd y).fderiv.symm⟩`. Establish `hWinj : ∀ z ∈ W, Injective (D z)`.

Introduce and unpack `z ⟨A', hA'⟩`. Establish `hA'' : (A' : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ F z` using `hA'`. Rewrite using `[← (hFd z).fderiv, ← hA'']`. Conclude with `A'.injective`. Set `U` to `P.source ∩ V ∩ W`.

Establish `hU : IsOpen U` using `(P.open_source.inter hV).inter hW`. Establish `hyU : y ∈ U` using `⟨⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _, hyV⟩, hyW⟩`. Set `ι : EuclideanSpace ℂ (Fin m) →L[ℂ] (Fin n → ℂ)` to `ContinuousLinearMap.pi fun j => Sum.elim (fun k => EuclideanSpace.proj k) (fun _ => (0 : EuclideanSpace ℂ (Fin m) →L[ℂ] ℂ)) (e j)`. Set `g` to `P.symm`. Set `Φ : EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin (n - m))` to `fun x => WithLp.toLp 2 fun i => g (ι x) (e.symm (Sum.inr i))`.

Set `Ω : Set (EuclideanSpace ℂ (Fin m))` to `ι ⁻¹' (P.target ∩ g ⁻¹' U)`. Establish `hΩ : IsOpen Ω` using `(P.isOpen_inter_preimage_symm hU).preimage ι.continuous`. Establish `hG : ∀ x, ι x ∈ P.target → graphPt e Φ x = g (ι x)`. Introduce `x hx`. Establish `hFg : F (g (ι x)) = ι x` using `P.right_inv hx`.

Use `PiLp.ext fun j => ?_` and prove the remaining obligations. Establish `hj` using `congr_fun hFg j`. Break down `h : e j with k | i` into its components or cases. Simplify using `[graphPt, F, ι, h] at hj ⊢`. Conclude with `hj.symm`.

Establish `hs : e.symm (Sum.inr i) = j` using `e.symm_apply_eq.2 h.symm`. Simplify using `[graphPt, Φ, h, hs]`. Establish `hzero : ∀ x, ι x ∈ P.target → ∀ i, f i (g (ι x)) = 0`. Introduce `x hx i`. Use `congr_fun (P.right_inv hx) (e.symm (Sum.inr i))` as an intermediate fact.

Simplify `this` using `[P, F, ι]`. Set `pin : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin m)` to `fun z => WithLp.toLp 2 fun k => z (e.symm (Sum.inl k))`. Establish `hFpin : ∀ z, (∀ i, f i z = 0) → F z = ι (pin z)`. Introduce `z hz`. Use function extensionality and compare the values at `j`.

Break down `h : e j with k | i` into its components or cases. Establish `hs : e.symm (Sum.inl k) = j` using `e.symm_apply_eq.2 h.symm`. Simplify using `[F, ι, pin, h, hs]`. Simplify using `[F, ι, h, hz i]`. Establish `hgdiff : ∀ x ∈ Ω, DifferentiableAt ℂ g (ι x)`.

Introduce `x hx`. Take `⟨A', hA'⟩` from `hx.2.2`. Establish `h1 : HasFDerivAt P (A' : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)) (P.symm (ι x))`. Rewrite using `[hA']`. Conclude with `(hFd _).differentiableAt.hasFDerivAt`.

Conclude with `(P.contDiffAt_symm hx.1 h1 hFc.contDiffAt).differentiableAt one_ne_zero`. Use `⟨e, Ω, Φ, U, hU, hyU, fun z hz => hz.1.2, hΩ, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Use `(differentiableAt_euclidean.2 fun i => ?_).differentiableWithinAt` and prove the remaining obligations. Use `show DifferentiableAt ℂ (fun x => g (ι x) (e.symm (Sum.inr i))) x`.

Conclude with `(EuclideanSpace.proj (𝕜 := ℂ) (e.symm (Sum.inr i))).differentiableAt.comp x ((hgdiff x hx).comp x ι.differentiableAt)`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Rewrite using `[hG x hx.1]`.

Conclude with `⟨hx.2, hzero x hx.1⟩`. Introduce and unpack `⟨hzU, hz0⟩`. Establish `hFz` using `hFpin z hz0`. Establish `ht : ι (pin z) ∈ P.target`. Rewrite using `[← hFz]`.

Conclude with `P.map_source hzU.1.1`. Establish `hgz : g (ι (pin z)) = z`. Rewrite using `[← hFz]`. Conclude with `P.left_inv hzU.1.1`. Use `⟨pin z, ⟨ht, ?_⟩, by rw [hG _ ht, hgz]⟩` and prove the remaining obligations.

Use `show g (ι (pin z)) ∈ U`. Rewrite using `[hgz]`. Conclude with `hzU`. Introduce `x hx`. Establish `hgx` using `hgdiff x hx`.

Set `g'` to `fderiv ℂ g (ι x)`. Establish `hGd : HasFDerivAt (graphPt e Φ) (g'.comp ι) x`. Establish `h1 : HasFDerivAt (fun x => g (ι x)) (g'.comp ι) x` using `hgx.hasFDerivAt.comp x ι.hasFDerivAt`. Use `h1.congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hΩ.mem_nhds hx] with x' hx' using hG x' hx'.1`.

Establish `hDg : ∀ w, D (g (ι x)) (g' w) = w`. Establish `h1 : HasFDerivAt (fun w => F (g w)) ((D (g (ι x))).comp g') (ι x)` using `(hFd _).comp (ι x) hgx.hasFDerivAt`. Establish `h2 : HasFDerivAt (fun w => F (g w)) (ContinuousLinearMap.id ℂ (Fin n → ℂ)) (ι x)`. Use `(hasFDerivAt_id (ι x)).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [P.open_target.mem_nhds hx.1] with w hw using P.right_inv hw`.

Introduce `w`. Use `congr_arg (fun T => T w) (h1.unique h2)` as an intermediate fact. Simplify using `using this`. Rewrite using `[hGd.fderiv, hG x hx.1]`. Use extensionality with `u`.

Simplify using `only [LinearMap.mem_range, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, rfl⟩ i`. Use `congr_fun (hDg (ι v)) (e.symm (Sum.inr i))` as an intermediate fact. Simplify `this` using `[D, ι]`.

Introduce `hu`. Use `⟨pin u, ?_⟩` and prove the remaining obligations. Use `show g' (ι (pin u)) = u`. Apply `hWinj _ hx.2.2` to reduce the goal to its premises. Rewrite using `[hDg]`.

Use function extensionality and compare the values at `j`. Break down `h : e j with k | i` into its components or cases. Establish `hs : e.symm (Sum.inl k) = j` using `e.symm_apply_eq.2 h.symm`. Simplify using `[D, ι, pin, h, hs]`. Establish `h2 : D (g (ι x)) u j = 0`.

Simplify using `only [D, ContinuousLinearMap.pi_apply, h, Sum.elim_inr]`. Conclude with `hu i`. Rewrite using `[h2]`. Simplify using `[ι, h]`.
-/
theorem HolomorphicImplicitGraph.proof : HolomorphicImplicitGraph.Statement := by
  classical
  intro n m f y V hf hV hyV hfy hK

  let L : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin (n - m) → ℂ) :=
    LinearMap.pi fun i => (fderiv ℂ (f i) y : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ)
  obtain ⟨e, he⟩ := exists_coordSplitting L (by rw [LinearMap.ker_pi]; exact hK)

  let F : EuclideanSpace ℂ (Fin n) → (Fin n → ℂ) := fun z j =>
    Sum.elim (fun _ => z j) (fun i => f i z) (e j)
  let D : EuclideanSpace ℂ (Fin n) → (EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)) := fun z =>
    ContinuousLinearMap.pi fun j =>
      Sum.elim (fun _ => EuclideanSpace.proj j) (fun i => fderiv ℂ (f i) z) (e j)
  have hFd : ∀ z, HasFDerivAt F (D z) z := by
    intro z
    refine hasFDerivAt_pi.2 fun j => ?_
    rcases h : e j with k | i
    · simp only [Sum.elim_inl]
      exact (EuclideanSpace.proj (𝕜 := ℂ) j).hasFDerivAt
    · simp only [Sum.elim_inr]
      exact ((hf i).differentiable one_ne_zero z).hasFDerivAt
  have hFc : ContDiff ℂ 1 F := by
    refine contDiff_pi.2 fun j => ?_
    rcases h : e j with k | i
    · simp only [F, h, Sum.elim_inl]
      exact (EuclideanSpace.proj (𝕜 := ℂ) j).contDiff
    · simp only [F, h, Sum.elim_inr]
      exact hf i

  have hDy : Injective (D y) := by
    refine (injective_iff_map_eq_zero (D y)).2 fun v hv => he v (fun j k hj => ?_) ?_
    · have := congr_fun hv j
      simpa [D, hj] using this
    · funext i
      have := congr_fun hv (e.symm (Sum.inr i))
      simpa [D, L] using this
  let A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ) :=
    (LinearEquiv.ofInjectiveOfFinrankEq (D y : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ)) hDy
      (by simp)).toContinuousLinearEquiv
  have hA : (A : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)) = D y := by
    ext1 v
    rfl
  let P := hFc.contDiffAt.toOpenPartialHomeomorph F (f' := A) (by rw [hA]; exact hFd y) one_ne_zero

  let W : Set (EuclideanSpace ℂ (Fin n)) := (fun z => fderiv ℂ F z) ⁻¹'
    Set.range ((↑) : (EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ)) → _)
  have hW : IsOpen W := ContinuousLinearEquiv.isOpen.preimage (hFc.continuous_fderiv one_ne_zero)
  have hyW : y ∈ W := ⟨A, by rw [hA]; exact (hFd y).fderiv.symm⟩
  have hWinj : ∀ z ∈ W, Injective (D z) := by
    rintro z ⟨A', hA'⟩
    have hA'' : (A' : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ F z := hA'
    rw [← (hFd z).fderiv, ← hA'']
    exact A'.injective
  let U := P.source ∩ V ∩ W
  have hU : IsOpen U := (P.open_source.inter hV).inter hW
  have hyU : y ∈ U := ⟨⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _, hyV⟩, hyW⟩

  let ι : EuclideanSpace ℂ (Fin m) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi fun j =>
    Sum.elim (fun k => EuclideanSpace.proj k) (fun _ => (0 : EuclideanSpace ℂ (Fin m) →L[ℂ] ℂ)) (e j)
  let g := P.symm
  let Φ : EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin (n - m)) := fun x =>
    WithLp.toLp 2 fun i => g (ι x) (e.symm (Sum.inr i))
  let Ω : Set (EuclideanSpace ℂ (Fin m)) := ι ⁻¹' (P.target ∩ g ⁻¹' U)
  have hΩ : IsOpen Ω := (P.isOpen_inter_preimage_symm hU).preimage ι.continuous
  have hG : ∀ x, ι x ∈ P.target → graphPt e Φ x = g (ι x) := by
    intro x hx
    have hFg : F (g (ι x)) = ι x := P.right_inv hx
    refine PiLp.ext fun j => ?_
    have hj := congr_fun hFg j
    rcases h : e j with k | i
    · simp [graphPt, F, ι, h] at hj ⊢
      exact hj.symm
    · have hs : e.symm (Sum.inr i) = j := e.symm_apply_eq.2 h.symm
      simp [graphPt, Φ, h, hs]
  have hzero : ∀ x, ι x ∈ P.target → ∀ i, f i (g (ι x)) = 0 := by
    intro x hx i
    have := congr_fun (P.right_inv hx) (e.symm (Sum.inr i))
    simpa [P, F, ι] using this
  let pin : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin m) := fun z =>
    WithLp.toLp 2 fun k => z (e.symm (Sum.inl k))
  have hFpin : ∀ z, (∀ i, f i z = 0) → F z = ι (pin z) := by
    intro z hz
    funext j
    rcases h : e j with k | i
    · have hs : e.symm (Sum.inl k) = j := e.symm_apply_eq.2 h.symm
      simp [F, ι, pin, h, hs]
    · simp [F, ι, h, hz i]
  have hgdiff : ∀ x ∈ Ω, DifferentiableAt ℂ g (ι x) := by
    intro x hx
    obtain ⟨A', hA'⟩ := hx.2.2
    have h1 : HasFDerivAt P (A' : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)) (P.symm (ι x)) := by
      rw [hA']
      exact (hFd _).differentiableAt.hasFDerivAt
    exact (P.contDiffAt_symm hx.1 h1 hFc.contDiffAt).differentiableAt one_ne_zero
  refine ⟨e, Ω, Φ, U, hU, hyU, fun z hz => hz.1.2, hΩ, ?_, ?_, ?_⟩
  · intro x hx
    refine (differentiableAt_euclidean.2 fun i => ?_).differentiableWithinAt
    show DifferentiableAt ℂ (fun x => g (ι x) (e.symm (Sum.inr i))) x
    exact (EuclideanSpace.proj (𝕜 := ℂ) (e.symm (Sum.inr i))).differentiableAt.comp x
      ((hgdiff x hx).comp x ι.differentiableAt)
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hG x hx.1]
      exact ⟨hx.2, hzero x hx.1⟩
    · rintro ⟨hzU, hz0⟩
      have hFz := hFpin z hz0
      have ht : ι (pin z) ∈ P.target := by
        rw [← hFz]
        exact P.map_source hzU.1.1
      have hgz : g (ι (pin z)) = z := by
        rw [← hFz]
        exact P.left_inv hzU.1.1
      refine ⟨pin z, ⟨ht, ?_⟩, by rw [hG _ ht, hgz]⟩
      show g (ι (pin z)) ∈ U
      rw [hgz]
      exact hzU
  · intro x hx
    have hgx := hgdiff x hx
    let g' := fderiv ℂ g (ι x)
    have hGd : HasFDerivAt (graphPt e Φ) (g'.comp ι) x := by
      have h1 : HasFDerivAt (fun x => g (ι x)) (g'.comp ι) x :=
        hgx.hasFDerivAt.comp x ι.hasFDerivAt
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hΩ.mem_nhds hx] with x' hx' using hG x' hx'.1
    have hDg : ∀ w, D (g (ι x)) (g' w) = w := by
      have h1 : HasFDerivAt (fun w => F (g w)) ((D (g (ι x))).comp g') (ι x) :=
        (hFd _).comp (ι x) hgx.hasFDerivAt
      have h2 : HasFDerivAt (fun w => F (g w)) (ContinuousLinearMap.id ℂ (Fin n → ℂ)) (ι x) := by
        refine (hasFDerivAt_id (ι x)).congr_of_eventuallyEq ?_
        filter_upwards [P.open_target.mem_nhds hx.1] with w hw using P.right_inv hw
      intro w
      have := congr_arg (fun T => T w) (h1.unique h2)
      simpa using this
    rw [hGd.fderiv, hG x hx.1]
    ext u
    simp only [LinearMap.mem_range, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    constructor
    · rintro ⟨v, rfl⟩ i
      have := congr_fun (hDg (ι v)) (e.symm (Sum.inr i))
      simpa [D, ι] using this
    · intro hu
      refine ⟨pin u, ?_⟩
      show g' (ι (pin u)) = u
      apply hWinj _ hx.2.2
      rw [hDg]
      funext j
      rcases h : e j with k | i
      · have hs : e.symm (Sum.inl k) = j := e.symm_apply_eq.2 h.symm
        simp [D, ι, pin, h, hs]
      · have h2 : D (g (ι x)) u j = 0 := by
          simp only [D, ContinuousLinearMap.pi_apply, h, Sum.elim_inr]
          exact hu i
        rw [h2]
        simp [ι, h]

end

end GroundTheory.Heights₂.Heights
