import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ComplexUniformizationSigOne
import Development.AutomorphicArithmetic.RealSpanData.RealData
import Development.AutomorphicArithmetic.RealSpanData.JSpan

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨1, 0, one_ne_zero, by simp⟩`. Consider the case `tmul q z`. Use `⟨(q.den : ℤ), q.num • z, by exact_mod_cast q.den_nz, ?_⟩` and prove the remaining obligations. Establish `h : ((q.den : ℤ)) • q = q.num • (1 : ℚ)`.

Rewrite using `[zsmul_eq_mul, zsmul_eq_mul, Int.cast_natCast, _root_.mul_one]`. Conclude with `Rat.den_mul_eq_num q`. Rewrite using `[TensorProduct.smul_tmul', h, TensorProduct.smul_tmul]`. Consider the case `add a b ha hb`. Take `⟨n, z, hn, h⟩` from `ha`.

Take `⟨m, w, hm, h'⟩` from `hb`. Use `⟨n * m, m • z + n • w, mul_ne_zero hn hm, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← h, ← h', smul_smul, smul_smul, mul_comm m n]`.
-/
private theorem exists_den {Λ : Type} [AddCommGroup Λ] (t : ℚ ⊗[ℤ] Λ) :
    ∃ (n : ℤ) (z : Λ), n ≠ 0 ∧ n • t = (1 : ℚ) ⊗ₜ[ℤ] z := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul q z =>
    refine ⟨(q.den : ℤ), q.num • z, by exact_mod_cast q.den_nz, ?_⟩
    have h : ((q.den : ℤ)) • q = q.num • (1 : ℚ) := by
      rw [zsmul_eq_mul, zsmul_eq_mul, Int.cast_natCast, _root_.mul_one]
      exact Rat.den_mul_eq_num q
    rw [TensorProduct.smul_tmul', h, TensorProduct.smul_tmul]
  | add a b ha hb =>
    obtain ⟨n, z, hn, h⟩ := ha
    obtain ⟨m, w, hm, h'⟩ := hb
    refine ⟨n * m, m • z + n • w, mul_ne_zero hn hm, ?_⟩
    rw [smul_add, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← h, ← h',
      smul_smul, smul_smul, mul_comm m n]

/- English proof (translation)
Take `⟨n, z, hn, e⟩` from `exists_den a`. Establish `hz : z = 0`. Apply `hB` to reduce the goal to its premises. Introduce `w`. Establish `h2 : B.baseChange ℚ ((1 : ℚ) ⊗ₜ[ℤ] z) ((1 : ℚ) ⊗ₜ[ℤ] w) = 0`.

Rewrite using `[← e, map_zsmul, LinearMap.smul_apply, h, smul_zero]`. Simplify `h2` using `[LinearMap.BilinForm.baseChange_tmul]`. Rewrite `e` using `[hz, TensorProduct.tmul_zero]`. Establish `hn' : (n : ℚ) ≠ 0` using `by exact_mod_cast hn`. Rewrite `e` using `[← Int.cast_smul_eq_zsmul ℚ]`.

Conclude with `(smul_eq_zero.1 e).resolve_left hn'`.
-/
private theorem sep_bc {Λ : Type} [AddCommGroup Λ] (B : LinearMap.BilinForm ℤ Λ)
    (hB : ∀ x, (∀ y, B x y = 0) → x = 0) (a : ℚ ⊗[ℤ] Λ) (h : ∀ w, B.baseChange ℚ a w = 0) : a = 0 := by
  obtain ⟨n, z, hn, e⟩ := exists_den a
  have hz : z = 0 := by
    apply hB
    intro w
    have h2 : B.baseChange ℚ ((1 : ℚ) ⊗ₜ[ℤ] z) ((1 : ℚ) ⊗ₜ[ℤ] w) = 0 := by
      rw [← e, map_zsmul, LinearMap.smul_apply, h, smul_zero]
    simpa [LinearMap.BilinForm.baseChange_tmul] using h2
  rw [hz, TensorProduct.tmul_zero] at e
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  rw [← Int.cast_smul_eq_zsmul ℚ] at e
  exact (smul_eq_zero.1 e).resolve_left hn'

/- English proof (translation)
Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]`. Consider the case `tmul q x`. Proceed by induction on `w using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul r y => simp [LinearMap.BilinForm.baseChange_tmul, h]`.
-/
private theorem adj_bc {Λ : Type} [AddCommGroup Λ] (B : LinearMap.BilinForm ℤ Λ) (f g : Λ →ₗ[ℤ] Λ)
    (h : ∀ x y, B (f x) y = B x (g y)) (u w : ℚ ⊗[ℤ] Λ) :
    B.baseChange ℚ (f.baseChange ℚ u) w = B.baseChange ℚ u (g.baseChange ℚ w) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul q x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul r y => simp [LinearMap.BilinForm.baseChange_tmul, h]

/- English proof (translation)
Establish `anti : ∀ x y, B x y = - B y x` using `fun x y => by`. Use `h (x + y)` as an intermediate fact. Simplify using `only [map_add, LinearMap.add_apply, h, zero_add, add_zero] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Proceed by induction on `u using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `tmul q x`. Proceed by induction on `w using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `tmul r y`. Simplify using `only [LinearMap.BilinForm.baseChange_tmul]`.

Rewrite using `[anti x y]`. Rewrite using `[mul_comm q r, neg_smul]`.
-/
private theorem anti_bc {Λ : Type} [AddCommGroup Λ] (B : LinearMap.BilinForm ℤ Λ) (h : ∀ x, B x x = 0)
    (u w : ℚ ⊗[ℤ] Λ) : B.baseChange ℚ u w = - B.baseChange ℚ w u := by
  have anti : ∀ x y, B x y = - B y x := fun x y => by
    have := h (x + y)
    simp only [map_add, LinearMap.add_apply, h, zero_add, add_zero] at this
    linarith
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]; ring
  | tmul q x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]; ring
    | tmul r y =>
      simp only [LinearMap.BilinForm.baseChange_tmul]
      rw [anti x y]
      rw [mul_comm q r, neg_smul]

/- English proof (translation)
Establish `inj : Function.Injective (E : V →ₗ[ℚ] Module.Dual ℚ V)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Conclude with `hE a fun w => by rw [ha]; rfl`. Set `Φ : V ≃ₗ[ℚ] Module.Dual ℚ V` to `LinearMap.linearEquivOfInjective (E : V →ₗ[ℚ] Module.Dual ℚ V) inj (Subspace.dual_finrank_eq).symm`.

Use `⟨(1 / 2 : ℚ) • (Φ.symm.toLinearMap ∘ₗ (F : V →ₗ[ℚ] Module.Dual ℚ V)), fun u w => ?_⟩` and prove the remaining obligations. Establish `h : E (Φ.symm (F u)) = F u` using `Φ.apply_symm_apply (F u)`. Simplify using `only [LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_smul, h, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exists_rep {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (E F : LinearMap.BilinForm ℚ V) (hE : ∀ a, (∀ w, E a w = 0) → a = 0) :
    ∃ b : Module.End ℚ V, ∀ u w, F u w = 2 * E (b u) w := by
  have inj : Function.Injective (E : V →ₗ[ℚ] Module.Dual ℚ V) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    exact hE a fun w => by rw [ha]; rfl
  let Φ : V ≃ₗ[ℚ] Module.Dual ℚ V :=
    LinearMap.linearEquivOfInjective (E : V →ₗ[ℚ] Module.Dual ℚ V) inj (Subspace.dual_finrank_eq).symm
  refine ⟨(1 / 2 : ℚ) • (Φ.symm.toLinearMap ∘ₗ (F : V →ₗ[ℚ] Module.Dual ℚ V)), fun u w => ?_⟩
  have h : E (Φ.symm (F u)) = F u := Φ.apply_symm_apply (F u)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_smul, h, smul_eq_mul]
  ring

/- English proof (translation)
Introduce `p _ D G L Y j hj`. Use `haveI := D.finLa`. Use `set E := D.EF.baseChange ℚ with hEdef`. Establish `sepE : ∀ a, (∀ w, E a w = 0) → a = 0` using `fun a h => sep_bc D.EF (fun x hx => D.nondeg (by rw [map_zero]; ext y; simpa using hx y)) a h`. Establish `sepY : ∀ a, (∀ w, Y.EF.baseChange ℚ a w = 0) → a = 0` using `fun a h => sep_bc Y.EF Y.nondeg a h`.

Establish `eqE : ∀ a a', (∀ w, E a w = E a' w) → a = a'` using `fun a a' h => by`. Rewrite using `[← sub_eq_zero]`. Conclude with `sepE _ fun w => by rw [map_sub, LinearMap.sub_apply, h, sub_self]`. Set `F : LinearMap.BilinForm ℚ (VQ D)` to `((Y.EF.baseChange ℚ).compl₁₂ j.symm.toLinearMap j.symm.toLinearMap)`. Establish `hF : ∀ u w, F u w = Y.EF.baseChange ℚ (j.symm u) (j.symm w)` using `fun u w => rfl`.

Take `⟨b, hb⟩` from `exists_rep E F sepE`. Establish `hinj : Function.Injective b`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `u hu`. Establish `: j.symm u = 0` using `sepY _ fun w => by`.

Establish `h` using `hb u (j w)`. Rewrite `h` using `[hu, map_zero, LinearMap.zero_apply, MulZeroClass.mul_zero, hF, j.symm_apply_apply]`. Conclude with `h`. Simplify using `using this`. Establish `comm : ∀ c : D.O, b * actQ D c = actQ D c * b`.

Introduce `c`. Use `LinearMap.ext fun u => eqE _ _ fun w => ?_` and prove the remaining obligations. Establish `hc : j.symm (actQ D c u) = (DistribMulAction.toLinearMap ℤ Y.La c).baseChange ℚ (j.symm u)`. Rewrite using `[LinearEquiv.symm_apply_eq, hj, j.apply_symm_apply]`. Establish `hc' : ∀ w, j.symm (actQ D (D.inv c) w) = (DistribMulAction.toLinearMap ℤ Y.La (D.inv c)).baseChange ℚ (j.symm w)` using `fun w => by`.

Rewrite using `[LinearEquiv.symm_apply_eq, hj, j.apply_symm_apply]`. Establish `h1 : F (actQ D c u) w = F u (actQ D (D.inv c) w)`. Rewrite using `[hF, hF, hc, hc']`. Conclude with `adj_bc Y.EF _ _ (fun x y => Y.adj c x y) _ _`. Establish `h2 : E (actQ D c (b u)) w = E (b u) (actQ D (D.inv c) w)` using `adj_bc D.EF _ _ (fun x y => D.adj c x y) _ _`.

Establish `h3` using `hb (actQ D c u) w`. Establish `h4` using `hb u (actQ D (D.inv c) w)`. Simplify using `only [Module.End.mul_apply]`. Rewrite using `[h2]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hsym : ∀ u w, E (b u) w = E u (b w)`. Introduce `u w`. Establish `h1` using `hb u w`. Establish `h2` using `hb w u`. Establish `h3 : F u w = - F w u`.

Rewrite using `[hF, hF]`. Conclude with `anti_bc Y.EF Y.alt _ _`. Establish `h4 : E (b w) u = - E u (b w)` using `anti_bc D.EF D.alt _ _`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨b₀, hb₀⟩` from `(L.rep_range b).2 comm`.

Set `e : VQ D ≃ₗ[ℚ] VQ D` to `LinearEquiv.ofInjectiveEndo b hinj`. Establish `he : ∀ u, b (e.symm u) = u` using `fun u => e.apply_symm_apply u`. Establish `he' : ∀ u, e.symm (b u) = u` using `fun u => e.symm_apply_apply u`. Establish `comm' : ∀ c : D.O, (e.symm.toLinearMap : Module.End ℚ (VQ D)) * actQ D c = actQ D c * e.symm.toLinearMap`. Introduce `c`.

Use `LinearMap.ext fun u => hinj ?_` and prove the remaining obligations. Establish `h` using `LinearMap.congr_fun (comm c) (e.symm u)`. Simplify using `only [Module.End.mul_apply, LinearEquiv.coe_coe, he] at h ⊢`. Conclude with `h.symm`. Take `⟨b₁, hb₁⟩` from `(L.rep_range _).2 comm'`.

Establish `h01 : b₀ * b₁ = 1`. Apply `L.rep_inj` to reduce the goal to its premises. Rewrite using `[map_mul, map_one, hb₀, hb₁]`. Conclude with `LinearMap.ext fun u => he u`. Establish `h10 : b₁ * b₀ = 1`.

Apply `L.rep_inj` to reduce the goal to its premises. Rewrite using `[map_mul, map_one, hb₀, hb₁]`. Conclude with `LinearMap.ext fun u => he' u`. Establish `hadj : ∀ x v w, E (L.rep x v) w = E v (L.rep (sh G x) w)` using `L.adj`. Establish `shsh : sh G (sh G b₀) = b₀` using `G.star_star b₀`.

Establish `shmul : ∀ x y, sh G (x * y) = sh G y * sh G x` using `fun x y => by`. Unfold `sh`. Rewrite using `[map_mul, MulOpposite.unop_mul]`. Establish `shone : sh G 1 = 1`. Unfold `sh`.

Rewrite using `[map_one, MulOpposite.unop_one]`. Establish `hs : sh G b₀ = b₀`. Apply `L.rep_inj` to reduce the goal to its premises. Use `LinearMap.ext fun u => eqE _ _ fun w => ?_` and prove the remaining obligations. Rewrite using `[hadj, shsh, hb₀, hsym]`.

Establish `hs1 : sh G b₁ = b₁`. Establish `h : sh G b₁ * b₀ = 1`. Establish `h'` using `shmul b₀ b₁`. Rewrite `h'` using `[h01, shone, hs]`. Conclude with `h'.symm`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨⟨b₁, b₀, h10, h01⟩, hs1, fun u w => ?_⟩` and prove the remaining obligations. Establish `h` using `hb (j u) (j w)`. Rewrite `h` using `[hF, j.symm_apply_apply, j.symm_apply_apply]`. Rewrite using `[h]`.

Use `show _ = 2 * E (L.rep b₀ (j u)) (j w)`. Rewrite using `[hb₀]`.
-/
theorem UpperTheory.exists_unitary_unit_hermitian_form_of_cm_lattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (Y : PLat D.O D.inv) (j : (ℚ ⊗[ℤ] Y.La) ≃ₗ[ℚ] VQ D), (∀ (c : D.O) (u : ℚ ⊗[ℤ] Y.La), j ((DistribMulAction.toLinearMap ℤ Y.La c).baseChange ℚ u) = actQ D c (j u)) → ∃ β : G.Cˣ, sh G β = β ∧ ∀ u w : ℚ ⊗[ℤ] Y.La, Y.EF.baseChange ℚ u w = 2 * D.EF.baseChange ℚ (L.rep ((β⁻¹ : G.Cˣ) : G.C) (j u)) (j w) := by
  intro p _ D G L Y j hj
  haveI := D.finLa
  set E := D.EF.baseChange ℚ with hEdef
  have sepE : ∀ a, (∀ w, E a w = 0) → a = 0 := fun a h =>
    sep_bc D.EF (fun x hx => D.nondeg (by rw [map_zero]; ext y; simpa using hx y)) a h
  have sepY : ∀ a, (∀ w, Y.EF.baseChange ℚ a w = 0) → a = 0 := fun a h => sep_bc Y.EF Y.nondeg a h
  have eqE : ∀ a a', (∀ w, E a w = E a' w) → a = a' := fun a a' h => by
    rw [← sub_eq_zero]
    exact sepE _ fun w => by rw [map_sub, LinearMap.sub_apply, h, sub_self]
  let F : LinearMap.BilinForm ℚ (VQ D) :=
    ((Y.EF.baseChange ℚ).compl₁₂ j.symm.toLinearMap j.symm.toLinearMap)
  have hF : ∀ u w, F u w = Y.EF.baseChange ℚ (j.symm u) (j.symm w) := fun u w => rfl
  obtain ⟨b, hb⟩ := exists_rep E F sepE
  have hinj : Function.Injective b := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    have : j.symm u = 0 := sepY _ fun w => by
      have h := hb u (j w)
      rw [hu, map_zero, LinearMap.zero_apply, MulZeroClass.mul_zero, hF, j.symm_apply_apply] at h
      exact h
    simpa using this
  have comm : ∀ c : D.O, b * actQ D c = actQ D c * b := by
    intro c
    refine LinearMap.ext fun u => eqE _ _ fun w => ?_
    have hc : j.symm (actQ D c u) = (DistribMulAction.toLinearMap ℤ Y.La c).baseChange ℚ (j.symm u) := by
      rw [LinearEquiv.symm_apply_eq, hj, j.apply_symm_apply]
    have hc' : ∀ w, j.symm (actQ D (D.inv c) w) = (DistribMulAction.toLinearMap ℤ Y.La (D.inv c)).baseChange ℚ (j.symm w) := fun w => by
      rw [LinearEquiv.symm_apply_eq, hj, j.apply_symm_apply]
    have h1 : F (actQ D c u) w = F u (actQ D (D.inv c) w) := by
      rw [hF, hF, hc, hc']
      exact adj_bc Y.EF _ _ (fun x y => Y.adj c x y) _ _
    have h2 : E (actQ D c (b u)) w = E (b u) (actQ D (D.inv c) w) :=
      adj_bc D.EF _ _ (fun x y => D.adj c x y) _ _
    have h3 := hb (actQ D c u) w
    have h4 := hb u (actQ D (D.inv c) w)
    simp only [Module.End.mul_apply]
    rw [h2]
    linarith
  have hsym : ∀ u w, E (b u) w = E u (b w) := by
    intro u w
    have h1 := hb u w
    have h2 := hb w u
    have h3 : F u w = - F w u := by
      rw [hF, hF]
      exact anti_bc Y.EF Y.alt _ _
    have h4 : E (b w) u = - E u (b w) := anti_bc D.EF D.alt _ _
    linarith
  obtain ⟨b₀, hb₀⟩ := (L.rep_range b).2 comm
  let e : VQ D ≃ₗ[ℚ] VQ D := LinearEquiv.ofInjectiveEndo b hinj
  have he : ∀ u, b (e.symm u) = u := fun u => e.apply_symm_apply u
  have he' : ∀ u, e.symm (b u) = u := fun u => e.symm_apply_apply u
  have comm' : ∀ c : D.O, (e.symm.toLinearMap : Module.End ℚ (VQ D)) * actQ D c = actQ D c * e.symm.toLinearMap := by
    intro c
    refine LinearMap.ext fun u => hinj ?_
    have h := LinearMap.congr_fun (comm c) (e.symm u)
    simp only [Module.End.mul_apply, LinearEquiv.coe_coe, he] at h ⊢
    exact h.symm
  obtain ⟨b₁, hb₁⟩ := (L.rep_range _).2 comm'
  have h01 : b₀ * b₁ = 1 := by
    apply L.rep_inj
    rw [map_mul, map_one, hb₀, hb₁]
    exact LinearMap.ext fun u => he u
  have h10 : b₁ * b₀ = 1 := by
    apply L.rep_inj
    rw [map_mul, map_one, hb₀, hb₁]
    exact LinearMap.ext fun u => he' u
  have hadj : ∀ x v w, E (L.rep x v) w = E v (L.rep (sh G x) w) := L.adj
  have shsh : sh G (sh G b₀) = b₀ := G.star_star b₀
  have shmul : ∀ x y, sh G (x * y) = sh G y * sh G x := fun x y => by
    unfold sh
    rw [map_mul, MulOpposite.unop_mul]
  have shone : sh G 1 = 1 := by
    unfold sh
    rw [map_one, MulOpposite.unop_one]
  have hs : sh G b₀ = b₀ := by
    apply L.rep_inj
    refine LinearMap.ext fun u => eqE _ _ fun w => ?_
    rw [hadj, shsh, hb₀, hsym]
  have hs1 : sh G b₁ = b₁ := by
    have h : sh G b₁ * b₀ = 1 := by
      have h' := shmul b₀ b₁
      rw [h01, shone, hs] at h'
      exact h'.symm
    calc sh G b₁ = sh G b₁ * (b₀ * b₁) := by rw [h01, _root_.mul_one]
      _ = (sh G b₁ * b₀) * b₁ := (_root_.mul_assoc _ _ _).symm
      _ = b₁ := by rw [h, _root_.one_mul]
  refine ⟨⟨b₁, b₀, h10, h01⟩, hs1, fun u w => ?_⟩
  have h := hb (j u) (j w)
  rw [hF, j.symm_apply_apply, j.symm_apply_apply] at h
  rw [h]
  show _ = 2 * E (L.rep b₀ (j u)) (j w)
  rw [hb₀]
