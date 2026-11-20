import ReciprocityTheory.GroupCohomology.TransgressionStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.LowHolds
import ReciprocityTheory.GroupCohomology.LowNat
import ReciprocityTheory.GroupCohomology.ConnNatHolds
import ReciprocityTheory.GroupCohomology.PairHomFCoeOfId
import ReciprocityTheory.GroupCohomology.InfRes
import ReciprocityTheory.GroupCohomology.ResNormalHolds

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal LowDeg

universe u

section SlopeTestRemainingChoices

variable {R : Type u} [CommRing R] {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

/- English proof (translation)
Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Conclude with `Subtype.ext (congrArg P.u (congrArg y.1.1 (Subsingleton.elim _ _)))`.
-/
theorem lowLES_h0Equiv_pair {M : TRep R G} {M' : TRep R G'} (P : Pair M M') (x : M.H 0) :
    cohomZeroEquivContinuous M' (P.hom.H 0 x) = P.h0 (cohomZeroEquivContinuous M x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x

  exact Subtype.ext (congrArg P.u (congrArg y.1.1 (Subsingleton.elim _ _)))

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `y`. Take `⟨x, rfl⟩` from `e₂.surjective y`. Rewrite using `[← hg, LinearEquiv.map_eq_zero_iff, h x]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`.

Conclude with `⟨e₁ z, (hf z).symm⟩`. Introduce and unpack `⟨w, hw⟩`. Take `⟨z, rfl⟩` from `e₁.surjective w`. Use `⟨z, e₂.injective ?_⟩` and prove the remaining obligations. Rewrite using `[hf]`.

Conclude with `hw`.
-/
private theorem exact_of_linearEquiv_conj {R X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*} [CommRing R]
    [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂] [AddCommGroup X₃] [Module R X₃]
    [AddCommGroup Y₁] [Module R Y₁] [AddCommGroup Y₂] [Module R Y₂] [AddCommGroup Y₃] [Module R Y₃]
    {f : X₁ →ₗ[R] X₂} {g : X₂ →ₗ[R] X₃} {f' : Y₁ →ₗ[R] Y₂} {g' : Y₂ →ₗ[R] Y₃}
    (e₁ : X₁ ≃ₗ[R] Y₁) (e₂ : X₂ ≃ₗ[R] Y₂) (e₃ : X₃ ≃ₗ[R] Y₃)
    (hf : ∀ x, e₂ (f x) = f' (e₁ x)) (hg : ∀ x, e₃ (g x) = g' (e₂ x))
    (h : Function.Exact f g) : Function.Exact f' g' := by
  intro y
  obtain ⟨x, rfl⟩ := e₂.surjective y
  rw [← hg, LinearEquiv.map_eq_zero_iff, h x]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨e₁ z, (hf z).symm⟩
  · rintro ⟨w, hw⟩
    obtain ⟨z, rfl⟩ := e₁.surjective w
    refine ⟨z, e₂.injective ?_⟩
    rw [hf]
    exact hw

/- English proof (translation)
Introduce `a b hab`. Take `⟨x, rfl⟩` from `e₁.surjective a`. Take `⟨z, rfl⟩` from `e₁.surjective b`. Rewrite `hab` using `[← hf, ← hf]`. Rewrite using `[h (e₂.injective hab)]`.
-/
private theorem injective_of_linearEquiv_conj {R X₁ X₂ Y₁ Y₂ : Type*} [CommRing R]
    [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂]
    [AddCommGroup Y₁] [Module R Y₁] [AddCommGroup Y₂] [Module R Y₂]
    {f : X₁ →ₗ[R] X₂} {f' : Y₁ →ₗ[R] Y₂} (e₁ : X₁ ≃ₗ[R] Y₁) (e₂ : X₂ ≃ₗ[R] Y₂)
    (hf : ∀ x, e₂ (f x) = f' (e₁ x)) (h : Function.Injective f) : Function.Injective f' := by
  intro a b hab
  obtain ⟨x, rfl⟩ := e₁.surjective a
  obtain ⟨z, rfl⟩ := e₁.surjective b
  rw [← hf, ← hf] at hab
  rw [h (e₂.injective hab)]

/- English proof (translation)
Introduce `y`. Take `⟨x, hx⟩` from `h (e₂.symm y)`. Use `⟨e₁ x, ?_⟩` and prove the remaining obligations. Rewrite using `[← hf, hx, LinearEquiv.apply_symm_apply]`.
-/
private theorem surjective_of_linearEquiv_conj {R X₁ X₂ Y₁ Y₂ : Type*} [CommRing R]
    [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂]
    [AddCommGroup Y₁] [Module R Y₁] [AddCommGroup Y₂] [Module R Y₂]
    {f : X₁ →ₗ[R] X₂} {f' : Y₁ →ₗ[R] Y₂} (e₁ : X₁ ≃ₗ[R] Y₁) (e₂ : X₂ ≃ₗ[R] Y₂)
    (hf : ∀ x, e₂ (f x) = f' (e₁ x)) (h : Function.Surjective f) : Function.Surjective f' := by
  intro y
  obtain ⟨x, hx⟩ := h (e₂.symm y)
  refine ⟨e₁ x, ?_⟩
  rw [← hf, hx, LinearEquiv.apply_symm_apply]

/- English proof (translation)
Introduce `R _ G _ _ _ A B C i p hadm`. Establish `hses` using `admissibility_holds R G A B C i p hadm`. Take `⟨⟨δ, hconn, hles⟩, -⟩` from `lES_holds R _ _ _ i.hom p.hom hses`. Establish `n0 : ∀ x : C.H 0, h1EquivOfOrderTwo A (δ 0 x) = ((h1EquivOfOrderTwo A).toLinearMap ∘ₗ δ 0 ∘ₗ (cohomZeroEquivContinuous C).symm.toLinearMap) (cohomZeroEquivContinuous C x)`. Introduce `x`.

Use `show h1EquivOfOrderTwo A (δ 0 x) = h1EquivOfOrderTwo A (δ 0 ((cohomZeroEquivContinuous C).symm (cohomZeroEquivContinuous C x)))`. Rewrite using `[LinearEquiv.symm_apply_apply]`. Establish `n1 : ∀ x : C.H 1, h2EquivOfOrderTwo A (δ 1 x) = ((h2EquivOfOrderTwo A).toLinearMap ∘ₗ δ 1 ∘ₗ (h1EquivOfOrderTwo C).symm.toLinearMap) (h1EquivOfOrderTwo C x)`. Introduce `x`. Use `show h2EquivOfOrderTwo A (δ 1 x) = h2EquivOfOrderTwo A (δ 1 ((h1EquivOfOrderTwo C).symm (h1EquivOfOrderTwo C x)))`.

Rewrite using `[LinearEquiv.symm_apply_apply]`. Use `⟨(h1EquivOfOrderTwo A).toLinearMap ∘ₗ δ 0 ∘ₗ (cohomZeroEquivContinuous C).symm.toLinearMap, (h2EquivOfOrderTwo A).toLinearMap ∘ₗ δ 1 ∘ₗ (h1EquivOfOrderTwo C).symm.toLinearMap, ?_, ?_, injective_of_linearEquiv_conj (cohomZeroEquivContinuous A) (cohomZeroEquivContinuous B) (fun x = …` and prove the remaining obligations. Introduce `c b a hb ha`. Set `b₀ : B.coch.X 0` to `⟨fun _ => b, continuous_const⟩`. Establish `hz : A.coch.d 1 ((oneCocyclesEquivFunctions A).symm a).1 = 0` using `((oneCocyclesEquivFunctions A).symm a).2`.

Establish `key : B.coch.d 0 b₀ = i.hom.f 1 ((oneCocyclesEquivFunctions A).symm a).1`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `v`. Use `show dn B.rho 0 (fun _ => b) v = i.u (a.1 (i.φ (v 0)))`. Rewrite using `[hadm.i_id]`.

Use `show dn B.rho 0 (fun _ => b) v = i.u (a.1 (v 0))`. Rewrite using `[ha (v 0), dn_zero_apply]`. Apply the tactic sequence `all_goals rfl`. Establish `hcd : C.coch.d 0 (p.hom.f 0 b₀) = 0`. Rewrite using `[← p.hom.comm, key]`.

Conclude with `(hses.exact 1).apply_apply_eq_zero _`. Establish `e₁ : (cohomZeroEquivContinuous C).symm c = C.coch.cls 0 (p.hom.f 0 b₀) hcd`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Conclude with `Subtype.ext hb.symm`. Establish `e₂ : h1EquivOfOrderTwo A (A.coch.cls 1 _ hz) = Submodule.Quotient.mk a` using `by show Submodule.Quotient.mk (oneCocyclesEquivFunctions A ((oneCocyclesEquivFunctions A).symm a)) = _`.

Rewrite using `[LinearEquiv.apply_symm_apply]`. Use `show h1EquivOfOrderTwo A (δ 0 ((cohomZeroEquivContinuous C).symm c)) = _`. Rewrite using `[e₁, hconn 0 b₀ _ hcd hz key]`. Conclude with `e₂`. Introduce `c b a hbc hpb hia`.

Set `b₁ : B.coch.X 1` to `⟨fun v => b (v 0), hbc.comp (continuous_apply 0)⟩`. Establish `hz : A.coch.d 2 ((twoCocyclesEquivFunctions A).symm a).1 = 0` using `((twoCocyclesEquivFunctions A).symm a).2`. Establish `key : B.coch.d 1 b₁ = i.hom.f 2 ((twoCocyclesEquivFunctions A).symm a).1`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `v`.

Use `show dn B.rho 1 (fun w => b (w 0)) v = i.u (a.1 (i.φ (v 0), i.φ (v 1)))`. Rewrite using `[hadm.i_id]`. Use `show dn B.rho 1 (fun w => b (w 0)) v = i.u (a.1 (v 0, v 1))`. Rewrite using `[hia (v 0, v 1), dn_one_apply, d1_apply]`. Apply the tactic sequence `all_goals rfl`.

Establish `hcd : C.coch.d 1 (p.hom.f 1 b₁) = 0`. Rewrite using `[← p.hom.comm, key]`. Conclude with `(hses.exact 2).apply_apply_eq_zero _`. Establish `e₁ : (h1EquivOfOrderTwo C).symm (Submodule.Quotient.mk c) = C.coch.cls 1 (p.hom.f 1 b₁) hcd`. Rewrite using `[LinearEquiv.symm_apply_eq]`.

Use `congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))` and prove the remaining obligations. Use `show c.1 g = p.u (b (p.φ g))`. Rewrite using `[hadm.p_id]`. Conclude with `(hpb g).symm`. Establish `e₂ : h2EquivOfOrderTwo A (A.coch.cls 2 _ hz) = Submodule.Quotient.mk a` using `by show Submodule.Quotient.mk (twoCocyclesEquivFunctions A ((twoCocyclesEquivFunctions A).symm a)) = _`.

Rewrite using `[LinearEquiv.apply_symm_apply]`. Use `show h2EquivOfOrderTwo A (δ 1 ((h1EquivOfOrderTwo C).symm (Submodule.Quotient.mk c))) = _`. Rewrite using `[e₁, hconn 1 b₁ _ hcd hz key]`. Conclude with `e₂`.
-/
theorem low_degree_long_exact_sequence : LowLESStatement.{u} := by
  intro R _ G _ _ _ A B C i p hadm
  have hses := admissibility_holds R G A B C i p hadm
  obtain ⟨⟨δ, hconn, hles⟩, -⟩ := lES_holds R _ _ _ i.hom p.hom hses

  have n0 : ∀ x : C.H 0, h1EquivOfOrderTwo A (δ 0 x) =
      ((h1EquivOfOrderTwo A).toLinearMap ∘ₗ δ 0 ∘ₗ (cohomZeroEquivContinuous C).symm.toLinearMap) (cohomZeroEquivContinuous C x) := by
    intro x
    show h1EquivOfOrderTwo A (δ 0 x) = h1EquivOfOrderTwo A (δ 0 ((cohomZeroEquivContinuous C).symm (cohomZeroEquivContinuous C x)))
    rw [LinearEquiv.symm_apply_apply]
  have n1 : ∀ x : C.H 1, h2EquivOfOrderTwo A (δ 1 x) =
      ((h2EquivOfOrderTwo A).toLinearMap ∘ₗ δ 1 ∘ₗ (h1EquivOfOrderTwo C).symm.toLinearMap) (h1EquivOfOrderTwo C x) := by
    intro x
    show h2EquivOfOrderTwo A (δ 1 x) = h2EquivOfOrderTwo A (δ 1 ((h1EquivOfOrderTwo C).symm (h1EquivOfOrderTwo C x)))
    rw [LinearEquiv.symm_apply_apply]
  refine ⟨(h1EquivOfOrderTwo A).toLinearMap ∘ₗ δ 0 ∘ₗ (cohomZeroEquivContinuous C).symm.toLinearMap,
    (h2EquivOfOrderTwo A).toLinearMap ∘ₗ δ 1 ∘ₗ (h1EquivOfOrderTwo C).symm.toLinearMap, ?_, ?_,
    injective_of_linearEquiv_conj (cohomZeroEquivContinuous A) (cohomZeroEquivContinuous B) (fun x => lowLES_h0Equiv_pair i x) hles.inj,
    exact_of_linearEquiv_conj (cohomZeroEquivContinuous A) (cohomZeroEquivContinuous B) (cohomZeroEquivContinuous C) (fun x => lowLES_h0Equiv_pair i x)
      (fun x => lowLES_h0Equiv_pair p x) (hles.exB 0),
    exact_of_linearEquiv_conj (cohomZeroEquivContinuous B) (cohomZeroEquivContinuous C) (h1EquivOfOrderTwo A) (fun x => lowLES_h0Equiv_pair p x)
      n0 (hles.exC 0),
    exact_of_linearEquiv_conj (cohomZeroEquivContinuous C) (h1EquivOfOrderTwo A) (h1EquivOfOrderTwo B) n0
      (fun x => h1Equiv_pair (P := i) (x := x)) (hles.exA 0),
    exact_of_linearEquiv_conj (h1EquivOfOrderTwo A) (h1EquivOfOrderTwo B) (h1EquivOfOrderTwo C) (fun x => h1Equiv_pair (P := i) (x := x))
      (fun x => h1Equiv_pair (P := p) (x := x)) (hles.exB 1),
    exact_of_linearEquiv_conj (h1EquivOfOrderTwo B) (h1EquivOfOrderTwo C) (h2EquivOfOrderTwo A) (fun x => h1Equiv_pair (P := p) (x := x))
      n1 (hles.exC 1),
    exact_of_linearEquiv_conj (h1EquivOfOrderTwo C) (h2EquivOfOrderTwo A) (h2EquivOfOrderTwo B) n1
      (fun x => h2Equiv_pair (P := i) (x := x)) (hles.exA 1),
    exact_of_linearEquiv_conj (h2EquivOfOrderTwo A) (h2EquivOfOrderTwo B) (h2EquivOfOrderTwo C) (fun x => h2Equiv_pair (P := i) (x := x))
      (fun x => h2Equiv_pair (P := p) (x := x)) (hles.exB 2),
    fun hsub => surjective_of_linearEquiv_conj (h2EquivOfOrderTwo B) (h2EquivOfOrderTwo C) (fun x => h2Equiv_pair (P := p) (x := x))
      (fun y => (hles.exC 2 y).1 (@Subsingleton.elim _ hsub _ _))⟩
  ·
    intro c b a hb ha
    let b₀ : B.coch.X 0 := ⟨fun _ => b, continuous_const⟩
    have hz : A.coch.d 1 ((oneCocyclesEquivFunctions A).symm a).1 = 0 := ((oneCocyclesEquivFunctions A).symm a).2
    have key : B.coch.d 0 b₀ = i.hom.f 1 ((oneCocyclesEquivFunctions A).symm a).1 := by
      apply Subtype.ext
      funext v
      show dn B.rho 0 (fun _ => b) v = i.u (a.1 (i.φ (v 0)))
      rw [hadm.i_id]
      show dn B.rho 0 (fun _ => b) v = i.u (a.1 (v 0))
      rw [ha (v 0), dn_zero_apply]
      all_goals rfl
    have hcd : C.coch.d 0 (p.hom.f 0 b₀) = 0 := by
      rw [← p.hom.comm, key]
      exact (hses.exact 1).apply_apply_eq_zero _
    have e₁ : (cohomZeroEquivContinuous C).symm c = C.coch.cls 0 (p.hom.f 0 b₀) hcd := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext hb.symm
    have e₂ : h1EquivOfOrderTwo A (A.coch.cls 1 _ hz) = Submodule.Quotient.mk a := by
      show Submodule.Quotient.mk (oneCocyclesEquivFunctions A ((oneCocyclesEquivFunctions A).symm a)) = _
      rw [LinearEquiv.apply_symm_apply]
    show h1EquivOfOrderTwo A (δ 0 ((cohomZeroEquivContinuous C).symm c)) = _
    rw [e₁, hconn 0 b₀ _ hcd hz key]
    exact e₂
  ·
    intro c b a hbc hpb hia
    let b₁ : B.coch.X 1 := ⟨fun v => b (v 0), hbc.comp (continuous_apply 0)⟩
    have hz : A.coch.d 2 ((twoCocyclesEquivFunctions A).symm a).1 = 0 := ((twoCocyclesEquivFunctions A).symm a).2
    have key : B.coch.d 1 b₁ = i.hom.f 2 ((twoCocyclesEquivFunctions A).symm a).1 := by
      apply Subtype.ext
      funext v
      show dn B.rho 1 (fun w => b (w 0)) v = i.u (a.1 (i.φ (v 0), i.φ (v 1)))
      rw [hadm.i_id]
      show dn B.rho 1 (fun w => b (w 0)) v = i.u (a.1 (v 0, v 1))
      rw [hia (v 0, v 1), dn_one_apply, d1_apply]
      all_goals rfl
    have hcd : C.coch.d 1 (p.hom.f 1 b₁) = 0 := by
      rw [← p.hom.comm, key]
      exact (hses.exact 2).apply_apply_eq_zero _
    have e₁ : (h1EquivOfOrderTwo C).symm (Submodule.Quotient.mk c) = C.coch.cls 1 (p.hom.f 1 b₁) hcd := by
      rw [LinearEquiv.symm_apply_eq]
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      show c.1 g = p.u (b (p.φ g))
      rw [hadm.p_id]
      exact (hpb g).symm
    have e₂ : h2EquivOfOrderTwo A (A.coch.cls 2 _ hz) = Submodule.Quotient.mk a := by
      show Submodule.Quotient.mk (twoCocyclesEquivFunctions A ((twoCocyclesEquivFunctions A).symm a)) = _
      rw [LinearEquiv.apply_symm_apply]
    show h2EquivOfOrderTwo A (δ 1 ((h1EquivOfOrderTwo C).symm (Submodule.Quotient.mk c))) = _
    rw [e₁, hconn 1 b₁ _ hcd hz key]
    exact e₂

end ReciprocityTheory.Coh
