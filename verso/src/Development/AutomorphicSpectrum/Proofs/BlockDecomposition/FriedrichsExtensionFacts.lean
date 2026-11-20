import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.FriedrichsFc

open UniformSpace (Completion)

/- English proof (translation)
Set `f' : E →L[ℂ] F` to `f.mkContinuous 1 (by simpa using hf)`. Set `e : E →L[ℂ] Completion E` to `UniformSpace.Completion.toComplL`. Establish `hd : DenseRange e` using `UniformSpace.Completion.denseRange_coe`. Establish `hu : IsUniformInducing e` using `UniformSpace.Completion.isUniformInducing_coe E`. Establish `he : ∀ u : E, (f'.extend e) (u : Completion E) = f u` using `fun u => f'.extend_eq hd hu u`.

Use `⟨f'.extend e, he, ?_⟩` and prove the remaining obligations. Use `ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_` and prove the remaining obligations. Proceed by induction on `x using UniformSpace.Completion.induction_on with`. Consider the case `hp => exact isClosed_le (by fun_prop) (by fun_prop)`. Consider the case `ih u`.

Rewrite using `[he, UniformSpace.Completion.norm_coe, one_mul]`. Conclude with `hf u`.
-/
theorem exists_extension {E F : Type} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (f : E →ₗ[ℂ] F) (hf : ∀ u, ‖f u‖ ≤ ‖u‖) :
    ∃ g : Completion E →L[ℂ] F, (∀ u : E, g (u : Completion E) = f u) ∧ ‖g‖ ≤ 1 := by
  let f' : E →L[ℂ] F := f.mkContinuous 1 (by simpa using hf)
  let e : E →L[ℂ] Completion E := UniformSpace.Completion.toComplL
  have hd : DenseRange e := UniformSpace.Completion.denseRange_coe
  have hu : IsUniformInducing e := UniformSpace.Completion.isUniformInducing_coe E
  have he : ∀ u : E, (f'.extend e) (u : Completion E) = f u := fun u => f'.extend_eq hd hu u
  refine ⟨f'.extend e, he, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    rw [he, UniformSpace.Completion.norm_coe, one_mul]
    exact hf u

/- English proof (translation)
Establish `key : ⟪V₀ u, V₀ u⟫_ℂ = ⟪u, u⟫_ℂ`. Establish `h2 : V' (V (ι u)) = ι u`. Use `congrArg (fun W : H →L[ℂ] H => W (ι u)) h1` as an intermediate fact. Simplify using `using this`. Rewrite using `[← hB, hBV, ← hι, hadj, h2, hB]`.

Establish `: ‖V₀ u‖ ^ 2 = ‖u‖ ^ 2`. Rewrite using `[@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, key]`. Conclude with `le_of_eq ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this)`.
-/
theorem norm_map_le {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ι B : E →ₗ[ℂ] H) (hB : ∀ u v, ⟪B u, ι v⟫_ℂ = ⟪u, v⟫_ℂ)
    (V V' : H →L[ℂ] H) (V₀ : E →ₗ[ℂ] E) (h1 : V' * V = 1)
    (hadj : ∀ u v, ⟪V u, v⟫_ℂ = ⟪u, V' v⟫_ℂ)
    (hι : ∀ u, V (ι u) = ι (V₀ u)) (hBV : ∀ u, B (V₀ u) = V (B u)) (u : E) :
    ‖V₀ u‖ ≤ ‖u‖ := by
  have key : ⟪V₀ u, V₀ u⟫_ℂ = ⟪u, u⟫_ℂ := by
    have h2 : V' (V (ι u)) = ι u := by
      have := congrArg (fun W : H →L[ℂ] H => W (ι u)) h1
      simpa using this
    rw [← hB, hBV, ← hι, hadj, h2, hB]
  have : ‖V₀ u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, key]
  exact le_of_eq ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this)

/- English proof (translation)
Take `⟨g, hg, hgn⟩` from `exists_extension ι hι`. Set `S : H →L[ℂ] Completion E` to `ContinuousLinearMap.adjoint g`. Establish `hSi : ∀ h c, ⟪S h, c⟫_ℂ = ⟪h, g c⟫_ℂ` using `fun h c => ContinuousLinearMap.adjoint_inner_left g c h`. Establish `hS : ∀ u : E, S (B u) = (u : Completion E)`. Introduce `u`.

Use `ext_inner_right ℂ fun c => ?_` and prove the remaining obligations. Rewrite using `[hSi]`. Proceed by induction on `c using UniformSpace.Completion.induction_on with`. Consider the case `hp => exact isClosed_eq (by fun_prop) (by fun_prop)`. Consider the case `ih v => rw [hg, hB, UniformSpace.Completion.inner_coe]`.

Establish `hSn : ‖S‖ ≤ 1`. Establish `: ‖S‖ = ‖g‖` using `by simp [S]`. Rewrite using `[this]`. Conclude with `hgn`. Establish `hTpos : (g ∘L S).IsPositive` using `ContinuousLinearMap.isPositive_self_comp_adjoint g`.

Use `⟨g ∘L S, hTpos.isSelfAdjoint, ?_, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Introduce `u`. Simplify using `only [ContinuousLinearMap.comp_apply]`. Rewrite using `[hS, hg]`.

Introduce `U U' U₀ U₀' hUU' hU'U hadj hι₀ hι₀' hB₀ hB₀'`. Establish `hadj' : ∀ u v, ⟪U' u, v⟫_ℂ = ⟪u, U v⟫_ℂ` using `fun u v => by`. Rewrite using `[← inner_conj_symm, ← hadj, inner_conj_symm]`. Set `c : E →ₗ[ℂ] Completion E` to `(UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := E)).toLinearMap`. Establish `hc : ∀ u : E, c u = (u : Completion E)` using `fun _ => rfl`.

Take `⟨U₁, hU₁, -⟩` from `exists_extension (c ∘ₗ U₀) (fun u => by`. Simplify `norm_map_le ι B hB U U' U₀ hU'U hadj hι₀ hB₀ u)` using `[hc]`. Take `⟨U₁', hU₁', -⟩` from `exists_extension (c ∘ₗ U₀') (fun u => by`. Simplify `norm_map_le ι B hB U' U U₀' hUU' hadj' hι₀' hB₀' u)` using `[hc]`. Establish `h1 : ∀ x, g (U₁ x) = U (g x)`.

Introduce `x`. Proceed by induction on `x using UniformSpace.Completion.induction_on with`. Consider the case `hp => exact isClosed_eq (by fun_prop) (by fun_prop)`. Consider the case `ih u => rw [hU₁, LinearMap.comp_apply, hc, hg, hg, hι₀]`. Establish `h1' : ∀ x, g (U₁' x) = U' (g x)`.

Introduce `x`. Proceed by induction on `x using UniformSpace.Completion.induction_on with`. Consider the case `hp => exact isClosed_eq (by fun_prop) (by fun_prop)`. Consider the case `ih u => rw [hU₁', LinearMap.comp_apply, hc, hg, hg, hι₀']`. Establish `h3 : ∀ a x, ⟪U₁ a, x⟫_ℂ = ⟪a, U₁' x⟫_ℂ`.

Introduce `a x`. Proceed by induction on `a using UniformSpace.Completion.induction_on with`. Consider the case `hp => exact isClosed_eq (by fun_prop) (by fun_prop)`. Consider the case `ih u`. Proceed by induction on `x using UniformSpace.Completion.induction_on with`.

Consider the case `hp => exact isClosed_eq (by fun_prop) (by fun_prop)`. Consider the case `ih v`. Rewrite using `[hU₁, hU₁', LinearMap.comp_apply, LinearMap.comp_apply, hc, hc, UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe, ← hB, hB₀, hadj, hι₀', hB]`. Establish `h4 : ∀ h, S (U h) = U₁ (S h)`. Introduce `h`.

Use `ext_inner_right ℂ fun x => ?_` and prove the remaining obligations. Rewrite using `[hSi, hadj, ← h1', ← hSi, h3]`. Use extensionality with `h`. Simplify using `only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]`. Rewrite using `[h4, h1]`.
-/
theorem exists_inverse_of_form {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ι B : E →ₗ[ℂ] H) (hB : ∀ u v, ⟪B u, ι v⟫_ℂ = ⟪u, v⟫_ℂ) (hι : ∀ u, ‖ι u‖ ≤ ‖u‖) :
    ∃ T : H →L[ℂ] H, IsSelfAdjoint T ∧ ‖T‖ ≤ 1 ∧ (∀ u, T (B u) = ι u) ∧
      ∀ (U U' : H →L[ℂ] H) (U₀ U₀' : E →ₗ[ℂ] E), U * U' = 1 → U' * U = 1 →
        (∀ u v, ⟪U u, v⟫_ℂ = ⟪u, U' v⟫_ℂ) → (∀ u, U (ι u) = ι (U₀ u)) →
        (∀ u, U' (ι u) = ι (U₀' u)) → (∀ u, B (U₀ u) = U (B u)) →
        (∀ u, B (U₀' u) = U' (B u)) → U * T = T * U := by
  obtain ⟨g, hg, hgn⟩ := exists_extension ι hι
  let S : H →L[ℂ] Completion E := ContinuousLinearMap.adjoint g
  have hSi : ∀ h c, ⟪S h, c⟫_ℂ = ⟪h, g c⟫_ℂ := fun h c =>
    ContinuousLinearMap.adjoint_inner_left g c h
  have hS : ∀ u : E, S (B u) = (u : Completion E) := by
    intro u
    refine ext_inner_right ℂ fun c => ?_
    rw [hSi]
    induction c using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih v => rw [hg, hB, UniformSpace.Completion.inner_coe]
  have hSn : ‖S‖ ≤ 1 := by
    have : ‖S‖ = ‖g‖ := by simp [S]
    rw [this]; exact hgn
  have hTpos : (g ∘L S).IsPositive := ContinuousLinearMap.isPositive_self_comp_adjoint g
  refine ⟨g ∘L S, hTpos.isSelfAdjoint, ?_, ?_, ?_⟩
  · calc ‖g ∘L S‖ ≤ ‖g‖ * ‖S‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  · intro u
    simp only [ContinuousLinearMap.comp_apply]
    rw [hS, hg]
  · intro U U' U₀ U₀' hUU' hU'U hadj hι₀ hι₀' hB₀ hB₀'
    have hadj' : ∀ u v, ⟪U' u, v⟫_ℂ = ⟪u, U v⟫_ℂ := fun u v => by
      rw [← inner_conj_symm, ← hadj, inner_conj_symm]
    let c : E →ₗ[ℂ] Completion E :=
      (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := E)).toLinearMap
    have hc : ∀ u : E, c u = (u : Completion E) := fun _ => rfl
    obtain ⟨U₁, hU₁, -⟩ := exists_extension (c ∘ₗ U₀) (fun u => by
      simpa [hc] using norm_map_le ι B hB U U' U₀ hU'U hadj hι₀ hB₀ u)
    obtain ⟨U₁', hU₁', -⟩ := exists_extension (c ∘ₗ U₀') (fun u => by
      simpa [hc] using norm_map_le ι B hB U' U U₀' hUU' hadj' hι₀' hB₀' u)
    have h1 : ∀ x, g (U₁ x) = U (g x) := by
      intro x
      induction x using UniformSpace.Completion.induction_on with
      | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih u => rw [hU₁, LinearMap.comp_apply, hc, hg, hg, hι₀]
    have h1' : ∀ x, g (U₁' x) = U' (g x) := by
      intro x
      induction x using UniformSpace.Completion.induction_on with
      | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih u => rw [hU₁', LinearMap.comp_apply, hc, hg, hg, hι₀']
    have h3 : ∀ a x, ⟪U₁ a, x⟫_ℂ = ⟪a, U₁' x⟫_ℂ := by
      intro a x
      induction a using UniformSpace.Completion.induction_on with
      | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih u =>
        induction x using UniformSpace.Completion.induction_on with
        | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
        | ih v =>
          rw [hU₁, hU₁', LinearMap.comp_apply, LinearMap.comp_apply, hc, hc,
            UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe,
            ← hB, hB₀, hadj, hι₀', hB]
    have h4 : ∀ h, S (U h) = U₁ (S h) := by
      intro h
      refine ext_inner_right ℂ fun x => ?_
      rw [hSi, hadj, ← h1', ← hSi, h3]
    ext h
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    rw [h4, h1]

/- English proof (translation)
Use `letI core : PreInnerProductSpace.Core ℂ D := { inner := fun u v => ⟪B u, ι v⟫_ℂ conj_inner_symm := fun x y => by show (starRingEnd ℂ) ⟪B y, ι x⟫_ℂ = ⟪B x, ι y⟫_ℂ`. Rewrite using `[inner_conj_symm, hsym]`. Use `re_inner_nonneg := fun x => le_trans (sq_nonneg _) (hpos x)`. Use `add_left := fun x y z => by show ⟪B (x + y), ι z⟫_ℂ = ⟪B x, ι z⟫_ℂ + ⟪B y, ι z⟫_ℂ`. Rewrite using `[map_add, inner_add_left]`.

Use `smul_left := fun x y r => by show ⟪B (r • x), ι y⟫_ℂ = (starRingEnd ℂ) r * ⟪B x, ι y⟫_ℂ`. Rewrite using `[map_smul, inner_smul_left] }`. Use `letI sn : SeminormedAddCommGroup D := InnerProductSpace.Core.toSeminormedAddCommGroup (c := core)`. Use `letI ips : InnerProductSpace ℂ D := InnerProductSpace.ofCore core`. Establish `hι : ∀ u : D, ‖ι u‖ ≤ ‖u‖` using `fun u => by`.

Establish `h : ‖u‖ ^ 2 = (⟪B u, ι u⟫_ℂ).re` using `@norm_sq_eq_re_inner ℂ D _ sn ips u`. Conclude with `(sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h ▸ hpos u)`. Conclude with `exists_inverse_of_form ι B (fun _ _ => rfl) hι`.
-/
theorem exists_inverse_of_coercive {H D : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [AddCommGroup D] [Module ℂ D] (ι B : D →ₗ[ℂ] H)
    (hsym : ∀ u v, ⟪B u, ι v⟫_ℂ = ⟪ι u, B v⟫_ℂ)
    (hpos : ∀ u, ‖ι u‖ ^ 2 ≤ (⟪B u, ι u⟫_ℂ).re) :
    ∃ T : H →L[ℂ] H, IsSelfAdjoint T ∧ ‖T‖ ≤ 1 ∧ (∀ u, T (B u) = ι u) ∧
      ∀ (U U' : H →L[ℂ] H) (U₀ U₀' : D →ₗ[ℂ] D), U * U' = 1 → U' * U = 1 →
        (∀ u v, ⟪U u, v⟫_ℂ = ⟪u, U' v⟫_ℂ) → (∀ u, U (ι u) = ι (U₀ u)) →
        (∀ u, U' (ι u) = ι (U₀' u)) → (∀ u, B (U₀ u) = U (B u)) →
        (∀ u, B (U₀' u) = U' (B u)) → U * T = T * U := by
  letI core : PreInnerProductSpace.Core ℂ D :=
    { inner := fun u v => ⟪B u, ι v⟫_ℂ
      conj_inner_symm := fun x y => by
        show (starRingEnd ℂ) ⟪B y, ι x⟫_ℂ = ⟪B x, ι y⟫_ℂ
        rw [inner_conj_symm, hsym]
      re_inner_nonneg := fun x => le_trans (sq_nonneg _) (hpos x)
      add_left := fun x y z => by
        show ⟪B (x + y), ι z⟫_ℂ = ⟪B x, ι z⟫_ℂ + ⟪B y, ι z⟫_ℂ
        rw [map_add, inner_add_left]
      smul_left := fun x y r => by
        show ⟪B (r • x), ι y⟫_ℂ = (starRingEnd ℂ) r * ⟪B x, ι y⟫_ℂ
        rw [map_smul, inner_smul_left] }
  letI sn : SeminormedAddCommGroup D := InnerProductSpace.Core.toSeminormedAddCommGroup (c := core)
  letI ips : InnerProductSpace ℂ D := InnerProductSpace.ofCore core
  have hι : ∀ u : D, ‖ι u‖ ≤ ‖u‖ := fun u => by
    have h : ‖u‖ ^ 2 = (⟪B u, ι u⟫_ℂ).re := @norm_sq_eq_re_inner ℂ D _ sn ips u
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h ▸ hpos u)
  exact exists_inverse_of_form ι B (fun _ _ => rfl) hι

/- English proof (translation)
Introduce `H _ _ _ D A hsym hpos`. Take `⟨R, hR, hRn, hRA, hRU⟩` from `exists_inverse_of_coercive (D := D) D.subtype A (fun x y => hsym x y) (fun x => hpos x)`. Use `⟨R, hR, hRn, fun x => hRA x, ?_⟩` and prove the remaining obligations. Introduce `U hU1 hU2 hD hD'`. Establish `lift : ∀ (V : H →L[ℂ] H), (∀ x : D, ∃ y : D, (y : H) = V x ∧ A y = V (A x)) → ∃ V₀ : D →ₗ[ℂ] D, (∀ u, V (D.subtype u) = D.subtype (V₀ u)) ∧ ∀ u, A (V₀ u) = V (A u)`.

Introduce `V hV`. Establish `hmem : ∀ x : D, (V.toLinearMap ∘ₗ D.subtype) x ∈ D` using `fun x => by`. Take `⟨y, hy, -⟩` from `hV x`. Simplify `y.2` using `[← hy]`. Use `⟨LinearMap.codRestrict D (V.toLinearMap ∘ₗ D.subtype) hmem, fun u => rfl, fun u => ?_⟩` and prove the remaining obligations.

Take `⟨y, hy, hAy⟩` from `hV u`. Establish `: LinearMap.codRestrict D (V.toLinearMap ∘ₗ D.subtype) hmem u = y` using `Subtype.ext (by simp [hy])`. Rewrite using `[this, hAy]`. Take `⟨U₀, h1, h2⟩` from `lift U hD`. Take `⟨U₀', h1', h2'⟩` from `lift (ContinuousLinearMap.adjoint U) hD'`.

Conclude with `hRU U (ContinuousLinearMap.adjoint U) U₀ U₀' hU2 hU1 (fun u v => (ContinuousLinearMap.adjoint_inner_right U u v).symm) h1 h1' h2 h2'`.
-/
theorem friedrichs : PositivityTheory.RgBcC.Fc.Friedrichs := by
  intro H _ _ _ D A hsym hpos
  obtain ⟨R, hR, hRn, hRA, hRU⟩ := exists_inverse_of_coercive (D := D) D.subtype A
    (fun x y => hsym x y) (fun x => hpos x)
  refine ⟨R, hR, hRn, fun x => hRA x, ?_⟩
  intro U hU1 hU2 hD hD'
  have lift : ∀ (V : H →L[ℂ] H), (∀ x : D, ∃ y : D, (y : H) = V x ∧ A y = V (A x)) →
      ∃ V₀ : D →ₗ[ℂ] D, (∀ u, V (D.subtype u) = D.subtype (V₀ u)) ∧ ∀ u, A (V₀ u) = V (A u) := by
    intro V hV
    have hmem : ∀ x : D, (V.toLinearMap ∘ₗ D.subtype) x ∈ D := fun x => by
      obtain ⟨y, hy, -⟩ := hV x
      simpa [← hy] using y.2
    refine ⟨LinearMap.codRestrict D (V.toLinearMap ∘ₗ D.subtype) hmem, fun u => rfl, fun u => ?_⟩
    obtain ⟨y, hy, hAy⟩ := hV u
    have : LinearMap.codRestrict D (V.toLinearMap ∘ₗ D.subtype) hmem u = y :=
      Subtype.ext (by simp [hy])
    rw [this, hAy]
  obtain ⟨U₀, h1, h2⟩ := lift U hD
  obtain ⟨U₀', h1', h2'⟩ := lift (ContinuousLinearMap.adjoint U) hD'
  exact hRU U (ContinuousLinearMap.adjoint U) U₀ U₀' hU2 hU1
    (fun u v => (ContinuousLinearMap.adjoint_inner_right U u v).symm) h1 h1' h2 h2'

end GlobalTheory.CompanionTheory.FriedrichsFc
