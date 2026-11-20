import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

/- English proof (translation)
Introduce `x y hxy`. Rewrite using `[RingCon.ker_apply, ← sub_eq_zero, ← map_sub]`. Rewrite `hxy` using `[TwoSidedIdeal.rel_iff]`. Establish `hle : TwoSidedIdeal.span I ≤ TwoSidedIdeal.comap f ⊥`. Rewrite using `[TwoSidedIdeal.span_le]`.

Introduce `z hz`. Rewrite using `[SetLike.mem_coe, TwoSidedIdeal.mem_comap, TwoSidedIdeal.mem_bot]`. Conclude with `h z hz`. Establish `h1` using `hle hxy`. Rewrite `h1` using `[TwoSidedIdeal.mem_comap, TwoSidedIdeal.mem_bot]`. Then use the resulting hypothesis.
-/
private theorem span_le_ker {R S : Type} [Ring R] [Ring S] (f : R →+* S) (I : Set R) (h : ∀ x ∈ I, f x = 0) :
    (TwoSidedIdeal.span I).ringCon ≤ RingCon.ker f := by
  intro x y hxy
  rw [RingCon.ker_apply, ← sub_eq_zero, ← map_sub]
  rw [TwoSidedIdeal.rel_iff] at hxy
  have hle : TwoSidedIdeal.span I ≤ TwoSidedIdeal.comap f ⊥ := by
    rw [TwoSidedIdeal.span_le]
    intro z hz
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap, TwoSidedIdeal.mem_bot]
    exact h z hz
  have h1 := hle hxy
  rwa [TwoSidedIdeal.mem_comap, TwoSidedIdeal.mem_bot] at h1

/- English proof (translation)
Rewrite using `[← map_zero (TwoSidedIdeal.span I).ringCon.mk']`. Conclude with `(RingCon.eq _).2 ((TwoSidedIdeal.rel_iff _ _ _).2 (by simpa using TwoSidedIdeal.subset_span hx))`.
-/
private theorem mk_eq_zero {R : Type} [Ring R] (I : Set R) {x : R} (hx : x ∈ I) :
    (TwoSidedIdeal.span I).ringCon.mk' x = 0 := by
  rw [← map_zero (TwoSidedIdeal.span I).ringCon.mk']
  exact (RingCon.eq _).2 ((TwoSidedIdeal.rel_iff _ _ _).2 (by simpa using TwoSidedIdeal.subset_span hx))

/- English proof (translation)
Introduce `κ κ' G _ _ _ _ I`. Set `φ : MonoidAlgebra κ G →+* MonoidAlgebra κ' G` to `MonoidAlgebra.mapRingHom G (algebraMap κ κ')`. Set `J` to `(TwoSidedIdeal.span I).ringCon`. Set `J'` to `(TwoSidedIdeal.span (φ '' I)).ringCon`. Set `T` to `κ' ⊗[κ] J.Quotient`.

Establish `hφ : ∀ x ∈ I, ((RingCon.mk' J').comp φ) x = 0` using `fun x hx => mk_eq_zero _ ⟨x, hx, rfl⟩`. Set `g0 : J.Quotient →+* J'.Quotient` to `RingCon.lift J ((RingCon.mk' J').comp φ) (span_le_ker _ _ hφ)`. Establish `hg0 : ∀ x, g0 (RingCon.mk' J x) = RingCon.mk' J' (φ x)` using `fun x => RingCon.lift_mk' _ x`. Set `g : J.Quotient →ₐ[κ] J'.Quotient` to `{ g0 with commutes' := fun r => by`. Express the relevant statement in the definitionally equal form `g0 (RingCon.mk' J (algebraMap κ _ r)) = RingCon.mk' J' (algebraMap κ _ r)`.

Rewrite using `[hg0]`. Use `congr 1`. Simplify using `[φ, MonoidAlgebra.coe_algebraMap, MonoidAlgebra.mapRingHom_single] }`. Set `α : T →ₐ[κ'] J'.Quotient` to `Algebra.TensorProduct.lift (Algebra.ofId κ' J'.Quotient) g (fun x y => Algebra.commutes _ _)`. Set `β : MonoidAlgebra κ' G →ₐ[κ'] T` to `MonoidAlgebra.lift κ' T G { toFun := fun m => (1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single m 1) map_one' := by`.

Express the relevant statement in the definitionally equal form `(1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single 1 1) = 1`. Rewrite using `[← MonoidAlgebra.one_def, map_one]`. Both sides reduce to the same expression. Use the proof step `map_mul' := fun a b => by`. Express the relevant statement in the definitionally equal form `(1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single (a * b) 1) = ((1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single a 1)) * ((1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single b 1))`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← map_mul, MonoidAlgebra.single_mul_single, mul_one] }`. Establish `hβs : ∀ (m : G) (c : κ'), β (MonoidAlgebra.single m c) = c • ((1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single m 1))`. Introduce `m c`. Rewrite using `[MonoidAlgebra.lift_single]`. Both sides reduce to the same expression.

Establish `hβφ : ∀ x, β (φ x) = (1 : κ') ⊗ₜ RingCon.mk' J x`. Introduce `x`. Establish `key : (β : MonoidAlgebra κ' G →+* T).comp φ = ((Algebra.TensorProduct.includeRight : J.Quotient →ₐ[κ] T) : J.Quotient →+* T).comp (RingCon.mk' J)`. Apply `MonoidAlgebra.ringHom_ext` to reduce the goal to its premises. Introduce `r`.

Simplify using `only [RingHom.coe_comp, Function.comp_apply, φ, MonoidAlgebra.mapRingHom_single, RingHom.coe_coe, hβs]`. Rewrite using `[TensorProduct.smul_tmul', algebraMap_smul, TensorProduct.smul_tmul, Algebra.TensorProduct.includeRight_apply]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `r • ((MonoidAlgebra.single 1 1 : MonoidAlgebra κ G) : J.Quotient) = ((MonoidAlgebra.single 1 r : MonoidAlgebra κ G) : J.Quotient)`. Rewrite using `[← RingCon.coe_smul, MonoidAlgebra.smul_single', mul_one]`.

Introduce `m`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, φ, MonoidAlgebra.mapRingHom_single, RingHom.coe_coe, hβs, map_one, one_smul]`. Both sides reduce to the same expression. Conclude with `congrArg (fun h => h x) key`. Establish `hβ0 : ∀ y ∈ φ '' I, (β : MonoidAlgebra κ' G →+* T) y = 0`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[RingHom.coe_coe, hβφ, mk_eq_zero I hx, TensorProduct.tmul_zero]`. Set `β' : J'.Quotient →+* T` to `RingCon.lift J' (β : MonoidAlgebra κ' G →+* T) (span_le_ker _ _ hβ0)`. Establish `hβ' : ∀ y, β' (RingCon.mk' J' y) = β y` using `fun y => RingCon.lift_mk' _ y`. Set `q' : MonoidAlgebra κ' G →ₐ[κ'] J'.Quotient` to `{ RingCon.mk' J' with commutes' := fun _ => rfl }`.

Establish `hα : ∀ (a : κ') (q : J.Quotient), α (a ⊗ₜ q) = algebraMap κ' J'.Quotient a * g0 q` using `fun a q => Algebra.TensorProduct.lift_tmul _ _ _ a q`. Establish `hαβ : ∀ z : J'.Quotient, α (β' z) = z`. Introduce `z`. Take `⟨y, rfl⟩` from `RingCon.mk'_surjective J' z`. Rewrite using `[hβ']`.

Establish `key : α.comp β = q'`. Apply `MonoidAlgebra.algHom_ext` to reduce the goal to its premises. Introduce `m`. Rewrite using `[AlgHom.comp_apply, hβs, one_smul, hα, map_one, one_mul, hg0, MonoidAlgebra.mapRingHom_single, map_one]`. Both sides reduce to the same expression.

Conclude with `Subsingleton.elim _ _`. Conclude with `congrArg (fun h => h y) key`. Establish `hβα : ∀ t : T, β' (α t) = t`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => rw [map_zero, map_zero]`. Consider the case `tmul a q`. Take `⟨x, rfl⟩` from `RingCon.mk'_surjective J q`. Rewrite using `[hα, map_mul, hg0]`. Express the relevant statement in the definitionally equal form `β' (RingCon.mk' J' (algebraMap κ' _ a)) * β' (RingCon.mk' J' (φ x)) = _`.

Rewrite using `[hβ', hβ', AlgHom.commutes, hβφ, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Both sides reduce to the same expression. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`. Conclude with `⟨{ toFun := α, invFun := β', left_inv := hβα, right_inv := hαβ, map_mul' := map_mul α, map_add' := map_add α }⟩`.
-/
theorem UpperTheory.V.Pa.BC.grp_quot_bc :
    ∀ (κ κ' G : Type) [Field κ] [Field κ'] [Algebra κ κ'] [Group G] (I : Set (MonoidAlgebra κ G)), Nonempty (κ' ⊗[κ] (TwoSidedIdeal.span I).ringCon.Quotient ≃+* (TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G (algebraMap κ κ') '' I)).ringCon.Quotient) := by
  intro κ κ' G _ _ _ _ I
  let φ : MonoidAlgebra κ G →+* MonoidAlgebra κ' G := MonoidAlgebra.mapRingHom G (algebraMap κ κ')
  let J := (TwoSidedIdeal.span I).ringCon
  let J' := (TwoSidedIdeal.span (φ '' I)).ringCon
  let T := κ' ⊗[κ] J.Quotient
  have hφ : ∀ x ∈ I, ((RingCon.mk' J').comp φ) x = 0 := fun x hx =>
    mk_eq_zero _ ⟨x, hx, rfl⟩
  let g0 : J.Quotient →+* J'.Quotient := RingCon.lift J ((RingCon.mk' J').comp φ) (span_le_ker _ _ hφ)
  have hg0 : ∀ x, g0 (RingCon.mk' J x) = RingCon.mk' J' (φ x) := fun x => RingCon.lift_mk' _ x
  let g : J.Quotient →ₐ[κ] J'.Quotient :=
    { g0 with
      commutes' := fun r => by
        change g0 (RingCon.mk' J (algebraMap κ _ r)) = RingCon.mk' J' (algebraMap κ _ r)
        rw [hg0]
        congr 1
        simp [φ, MonoidAlgebra.coe_algebraMap, MonoidAlgebra.mapRingHom_single] }
  let α : T →ₐ[κ'] J'.Quotient :=
    Algebra.TensorProduct.lift (Algebra.ofId κ' J'.Quotient) g (fun x y => Algebra.commutes _ _)
  let β : MonoidAlgebra κ' G →ₐ[κ'] T :=
    MonoidAlgebra.lift κ' T G
      { toFun := fun m => (1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single m 1)
        map_one' := by
          change (1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single 1 1) = 1
          rw [← MonoidAlgebra.one_def, map_one]
          rfl
        map_mul' := fun a b => by
          change (1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single (a * b) 1) =
            ((1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single a 1)) *
              ((1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single b 1))
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← map_mul,
            MonoidAlgebra.single_mul_single, mul_one] }
  have hβs : ∀ (m : G) (c : κ'), β (MonoidAlgebra.single m c) =
      c • ((1 : κ') ⊗ₜ RingCon.mk' J (MonoidAlgebra.single m 1)) := by
    intro m c
    rw [MonoidAlgebra.lift_single]
    rfl
  have hβφ : ∀ x, β (φ x) = (1 : κ') ⊗ₜ RingCon.mk' J x := by
    intro x
    have key : (β : MonoidAlgebra κ' G →+* T).comp φ =
        ((Algebra.TensorProduct.includeRight : J.Quotient →ₐ[κ] T) : J.Quotient →+* T).comp (RingCon.mk' J) := by
      apply MonoidAlgebra.ringHom_ext
      · intro r
        simp only [RingHom.coe_comp, Function.comp_apply, φ, MonoidAlgebra.mapRingHom_single, RingHom.coe_coe, hβs]
        rw [TensorProduct.smul_tmul', algebraMap_smul, TensorProduct.smul_tmul,
          Algebra.TensorProduct.includeRight_apply]
        congr 1
        change r • ((MonoidAlgebra.single 1 1 : MonoidAlgebra κ G) : J.Quotient) =
          ((MonoidAlgebra.single 1 r : MonoidAlgebra κ G) : J.Quotient)
        rw [← RingCon.coe_smul, MonoidAlgebra.smul_single', mul_one]
      · intro m
        simp only [RingHom.coe_comp, Function.comp_apply, φ, MonoidAlgebra.mapRingHom_single, RingHom.coe_coe, hβs, map_one, one_smul]
        rfl
    exact congrArg (fun h => h x) key
  have hβ0 : ∀ y ∈ φ '' I, (β : MonoidAlgebra κ' G →+* T) y = 0 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [RingHom.coe_coe, hβφ, mk_eq_zero I hx, TensorProduct.tmul_zero]
  let β' : J'.Quotient →+* T := RingCon.lift J' (β : MonoidAlgebra κ' G →+* T) (span_le_ker _ _ hβ0)
  have hβ' : ∀ y, β' (RingCon.mk' J' y) = β y := fun y => RingCon.lift_mk' _ y
  let q' : MonoidAlgebra κ' G →ₐ[κ'] J'.Quotient :=
    { RingCon.mk' J' with commutes' := fun _ => rfl }
  have hα : ∀ (a : κ') (q : J.Quotient), α (a ⊗ₜ q) = algebraMap κ' J'.Quotient a * g0 q :=
    fun a q => Algebra.TensorProduct.lift_tmul _ _ _ a q
  have hαβ : ∀ z : J'.Quotient, α (β' z) = z := by
    intro z
    obtain ⟨y, rfl⟩ := RingCon.mk'_surjective J' z
    rw [hβ']
    have key : α.comp β = q' := by
      apply MonoidAlgebra.algHom_ext
      · intro m
        rw [AlgHom.comp_apply, hβs, one_smul, hα, map_one, one_mul, hg0, MonoidAlgebra.mapRingHom_single, map_one]
        rfl
      · exact Subsingleton.elim _ _
    exact congrArg (fun h => h y) key
  have hβα : ∀ t : T, β' (α t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a q =>
      obtain ⟨x, rfl⟩ := RingCon.mk'_surjective J q
      rw [hα, map_mul, hg0]
      change β' (RingCon.mk' J' (algebraMap κ' _ a)) * β' (RingCon.mk' J' (φ x)) = _
      rw [hβ', hβ', AlgHom.commutes, hβφ, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  exact ⟨{ toFun := α, invFun := β', left_inv := hβα, right_inv := hαβ, map_mul' := map_mul α, map_add' := map_add α }⟩
