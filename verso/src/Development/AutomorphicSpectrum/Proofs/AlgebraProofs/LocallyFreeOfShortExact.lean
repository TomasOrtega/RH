import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeFiniteProjectiveBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeOfFiniteProjectiveStatement

open GlobalTheory.CompanionTheory.Ar.Num TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeKernel

/- English proof (translation)
Set `φ : S ⊗[R] M₁ →ₗ[S] E₁` to `LinearMap.liftBaseChange S f₁`. Establish `c₁ : ∀ t, i (φ t) = hf.equiv (j.baseChange S t)`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a x => simp [φ, IsBaseChange.equiv_tmul, h₁]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Establish `c₂ : ∀ t, q (hf.equiv t) = hf₂.equiv (π.baseChange S t)`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a x => simp [IsBaseChange.equiv_tmul, h₂]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Establish `c₃ : ∀ t, p.baseChange S (j.baseChange S t) = t`. Introduce `t`.

Rewrite using `[← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hpj, LinearMap.baseChange_id]`. Both sides reduce to the same expression. Establish `c₄ : ∀ t, j.baseChange S (p.baseChange S t) + s.baseChange S (π.baseChange S t) = t`. Introduce `t`. Rewrite using `[← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, ← LinearMap.add_apply, ← LinearMap.baseChange_add, hsum, LinearMap.baseChange_id]`.

Both sides reduce to the same expression. Establish `hinj : Function.Injective φ`. Introduce `a b hab`. Establish `: j.baseChange S a = j.baseChange S b`. Apply `hf.equiv.injective` to reduce the goal to its premises.

Rewrite using `[← c₁, ← c₁, hab]`. Rewrite using `[← c₃ a, this, c₃]`. Establish `hsurj : Function.Surjective φ`. Introduce `e`. Take `⟨t, ht⟩` from `hf.equiv.surjective (i e)`.

Establish `h0 : π.baseChange S t = 0`. Apply `hf₂.equiv.injective` to reduce the goal to its premises. Rewrite using `[← c₂, ht, hqi, map_zero]`. Use `⟨p.baseChange S t, hi ?_⟩` and prove the remaining obligations. Use `c₄ t` as an intermediate fact.

Rewrite `this` using `[h0, map_zero, add_zero]`. Rewrite using `[c₁, this, ht]`. Conclude with `IsBaseChange.of_equiv (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩) (by`. Introduce `x`. Use `show φ (1 ⊗ₜ[R] x) = f₁ x`.

Rewrite using `[LinearMap.liftBaseChange_tmul, one_smul])`.
-/
theorem isBaseChange_of_split {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M₁ M M₂ E₁ E E₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M] [Module R M]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup E₁] [Module R E₁] [Module S E₁]
    [IsScalarTower R S E₁] [AddCommGroup E] [Module R E] [Module S E] [IsScalarTower R S E]
    [AddCommGroup E₂] [Module R E₂] [Module S E₂] [IsScalarTower R S E₂]
    (j : M₁ →ₗ[R] M) (p : M →ₗ[R] M₁) (π : M →ₗ[R] M₂) (s : M₂ →ₗ[R] M)
    (hpj : p ∘ₗ j = LinearMap.id) (hsum : j ∘ₗ p + s ∘ₗ π = LinearMap.id)
    (f₁ : M₁ →ₗ[R] E₁) (f : M →ₗ[R] E) (f₂ : M₂ →ₗ[R] E₂)
    (i : E₁ →ₗ[S] E) (q : E →ₗ[S] E₂) (hi : Function.Injective i) (hqi : ∀ x, q (i x) = 0)
    (h₁ : ∀ x, i (f₁ x) = f (j x)) (h₂ : ∀ x, q (f x) = f₂ (π x))
    (hf : IsBaseChange S f) (hf₂ : IsBaseChange S f₂) : IsBaseChange S f₁ := by
  let φ : S ⊗[R] M₁ →ₗ[S] E₁ := LinearMap.liftBaseChange S f₁
  have c₁ : ∀ t, i (φ t) = hf.equiv (j.baseChange S t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [φ, IsBaseChange.equiv_tmul, h₁]
    | add a b ha hb => simp only [map_add, ha, hb]
  have c₂ : ∀ t, q (hf.equiv t) = hf₂.equiv (π.baseChange S t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [IsBaseChange.equiv_tmul, h₂]
    | add a b ha hb => simp only [map_add, ha, hb]
  have c₃ : ∀ t, p.baseChange S (j.baseChange S t) = t := by
    intro t
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hpj, LinearMap.baseChange_id]
    rfl
  have c₄ : ∀ t, j.baseChange S (p.baseChange S t) + s.baseChange S (π.baseChange S t) = t := by
    intro t
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_comp, ← LinearMap.add_apply, ← LinearMap.baseChange_add, hsum,
      LinearMap.baseChange_id]
    rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    have : j.baseChange S a = j.baseChange S b := by
      apply hf.equiv.injective
      rw [← c₁, ← c₁, hab]
    rw [← c₃ a, this, c₃]
  have hsurj : Function.Surjective φ := by
    intro e
    obtain ⟨t, ht⟩ := hf.equiv.surjective (i e)
    have h0 : π.baseChange S t = 0 := by
      apply hf₂.equiv.injective
      rw [← c₂, ht, hqi, map_zero]
    refine ⟨p.baseChange S t, hi ?_⟩
    have := c₄ t
    rw [h0, map_zero, add_zero] at this
    rw [c₁, this, ht]
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩) (by
    intro x
    show φ (1 ⊗ₜ[R] x) = f₁ x
    rw [LinearMap.liftBaseChange_tmul, one_smul])

/- English proof (translation)
Introduce `o Ω _ _ _ R E E₁ E₂ _ _ _ _ _ _ i q hi hq hex L r₁ r₂ hL hL₂`. Set `M : Submodule R E` to `{ L with smul_mem' := fun a e he => hL.1 a a.2 e he }`. Set `M₁ : Submodule R E₁` to `M.comap (i.restrictScalars R)`. Set `M₂ : Submodule R E₂` to `M.map (q.restrictScalars R)`. Take `⟨hfin, hproj, hrk, hbc⟩` from `GlobalTheory.T.locally_free_finite_projective_base_change R (r₁ + r₂) M hL`.

Take `⟨hfin₂, hproj₂, hrk₂, hbc₂⟩` from `GlobalTheory.T.locally_free_finite_projective_base_change R r₂ M₂ hL₂`. Establish `hqi : ∀ x, q (i x) = 0` using `fun x => by`. Rewrite using `[← LinearMap.mem_ker, ← hex]`. Conclude with `LinearMap.mem_range_self i x`. Set `j : M₁ →ₗ[R] M` to `(i.restrictScalars R).restrict (fun x hx => hx)`.

Set `π : M →ₗ[R] M₂` to `(q.restrictScalars R).restrict (fun x hx => ⟨x, hx, rfl⟩)`. Establish `hπ : Function.Surjective π`. Introduce and unpack `⟨_, x, hx, rfl⟩`. Conclude with `⟨⟨x, hx⟩, rfl⟩`. Establish `hj : Function.Injective j`.

Introduce `a b hab`. Conclude with `Subtype.ext (hi (congrArg Subtype.val hab))`. Take `⟨s, hs⟩` from `Module.projective_lifting_property π LinearMap.id hπ`. Establish `hmem : ∀ x : M, (LinearMap.id - s ∘ₗ π : M →ₗ[R] M) x ∈ LinearMap.range j`. Introduce `x`.

Establish `h0 : π (x - s (π x)) = 0`. Use `LinearMap.congr_fun hs (π x)` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply] at this`. Rewrite using `[map_sub, this, sub_self]`. Establish `h1 : ((x - s (π x) : M) : E) ∈ LinearMap.range i`.

Rewrite using `[hex]`. Conclude with `congrArg Subtype.val h0`. Take `⟨y, hy⟩` from `h1`. Use `⟨⟨y, ?_⟩, Subtype.ext hy⟩` and prove the remaining obligations. Use `show i y ∈ M`.

Rewrite using `[hy]`. Conclude with `(x - s (π x) : M).2`. Set `p : M →ₗ[R] M₁` to `(LinearEquiv.ofInjective j hj).symm.toLinearMap ∘ₗ LinearMap.codRestrict _ (LinearMap.id - s ∘ₗ π : M →ₗ[R] M) hmem`. Establish `hjp : ∀ x, j (p x) = x - s (π x)`. Introduce `x`.

Conclude with `congrArg Subtype.val ((LinearEquiv.ofInjective j hj).apply_symm_apply (LinearMap.codRestrict _ (LinearMap.id - s ∘ₗ π : M →ₗ[R] M) hmem x))`. Establish `hπj : ∀ x, π (j x) = 0` using `fun x => Subtype.ext (hqi x)`. Establish `hpj : p ∘ₗ j = LinearMap.id` using `by ext1 x`. Apply `hj` to reduce the goal to its premises. Rewrite using `[LinearMap.comp_apply, hjp, hπj, map_zero, sub_zero, LinearMap.id_apply]`.

Establish `hsum : j ∘ₗ p + s ∘ₗ π = LinearMap.id` using `by ext1 x`. Simplify using `only [LinearMap.add_apply, LinearMap.comp_apply, hjp, LinearMap.id_apply, sub_add_cancel]`. Establish `hbc₁ : IsBaseChange Ω M₁.subtype` using `isBaseChange_of_split j p π s hpj hsum M₁.subtype M.subtype M₂.subtype i q hi hqi (fun _ => rfl) (fun _ => rfl) hbc hbc₂`. Establish `hfin₁ : Module.Finite R M₁` using `Module.Finite.of_surjective p (fun x => ⟨j x, LinearMap.congr_fun hpj x⟩)`. Establish `hproj₁ : Module.Projective R M₁` using `Module.Projective.of_split j p hpj`.

Establish `: Module.Finite Ω E` using `Module.Finite.equiv hbc.equiv`. Establish `hrk₁ : Module.finrank Ω E₁ = r₁`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker q`. Rewrite `h1` using `[LinearMap.range_eq_top.2 hq, finrank_top, ← hex, LinearMap.finrank_range_of_inj hi, hrk, hrk₂]`. Use linear arithmetic over natural numbers and integers.

Conclude with `GlobalTheory.T.locally_free_of_finite_projective R r₁ M₁ hfin₁ hproj₁ hrk₁ hbc₁`.
-/
theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E E₁ E₂ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] [AddCommGroup E₂] [Module Ω E₂] (i : E₁ →ₗ[Ω] E) (q : E →ₗ[Ω] E₂), Function.Injective i → Function.Surjective q → LinearMap.range i = LinearMap.ker q → ∀ (L : AddSubgroup E) (r₁ r₂ : ℕ), LocFree R (r₁ + r₂) L → LocFree R r₂ (L.map q.toAddMonoidHom) → LocFree R r₁ (L.comap i.toAddMonoidHom) := by
  intro o Ω _ _ _ R E E₁ E₂ _ _ _ _ _ _ i q hi hq hex L r₁ r₂ hL hL₂
  let M : Submodule R E :=
    { L with smul_mem' := fun a e he => hL.1 a a.2 e he }
  let M₁ : Submodule R E₁ := M.comap (i.restrictScalars R)
  let M₂ : Submodule R E₂ := M.map (q.restrictScalars R)
  obtain ⟨hfin, hproj, hrk, hbc⟩ := GlobalTheory.T.locally_free_finite_projective_base_change R (r₁ + r₂) M hL
  obtain ⟨hfin₂, hproj₂, hrk₂, hbc₂⟩ := GlobalTheory.T.locally_free_finite_projective_base_change R r₂ M₂ hL₂
  have hqi : ∀ x, q (i x) = 0 := fun x => by
    rw [← LinearMap.mem_ker, ← hex]; exact LinearMap.mem_range_self i x
  let j : M₁ →ₗ[R] M := (i.restrictScalars R).restrict (fun x hx => hx)
  let π : M →ₗ[R] M₂ := (q.restrictScalars R).restrict (fun x hx => ⟨x, hx, rfl⟩)
  have hπ : Function.Surjective π := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hj : Function.Injective j := by
    intro a b hab
    exact Subtype.ext (hi (congrArg Subtype.val hab))
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hmem : ∀ x : M, (LinearMap.id - s ∘ₗ π : M →ₗ[R] M) x ∈ LinearMap.range j := by
    intro x
    have h0 : π (x - s (π x)) = 0 := by
      have := LinearMap.congr_fun hs (π x)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
      rw [map_sub, this, sub_self]
    have h1 : ((x - s (π x) : M) : E) ∈ LinearMap.range i := by
      rw [hex]; exact congrArg Subtype.val h0
    obtain ⟨y, hy⟩ := h1
    refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
    show i y ∈ M
    rw [hy]; exact (x - s (π x) : M).2
  let p : M →ₗ[R] M₁ := (LinearEquiv.ofInjective j hj).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict _ (LinearMap.id - s ∘ₗ π : M →ₗ[R] M) hmem
  have hjp : ∀ x, j (p x) = x - s (π x) := by
    intro x
    exact congrArg Subtype.val ((LinearEquiv.ofInjective j hj).apply_symm_apply
      (LinearMap.codRestrict _ (LinearMap.id - s ∘ₗ π : M →ₗ[R] M) hmem x))
  have hπj : ∀ x, π (j x) = 0 := fun x => Subtype.ext (hqi x)
  have hpj : p ∘ₗ j = LinearMap.id := by
    ext1 x
    apply hj
    rw [LinearMap.comp_apply, hjp, hπj, map_zero, sub_zero, LinearMap.id_apply]
  have hsum : j ∘ₗ p + s ∘ₗ π = LinearMap.id := by
    ext1 x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hjp, LinearMap.id_apply, sub_add_cancel]
  have hbc₁ : IsBaseChange Ω M₁.subtype :=
    isBaseChange_of_split j p π s hpj hsum M₁.subtype M.subtype M₂.subtype i q hi hqi
      (fun _ => rfl) (fun _ => rfl) hbc hbc₂
  have hfin₁ : Module.Finite R M₁ :=
    Module.Finite.of_surjective p (fun x => ⟨j x, LinearMap.congr_fun hpj x⟩)
  have hproj₁ : Module.Projective R M₁ := Module.Projective.of_split j p hpj
  have : Module.Finite Ω E := Module.Finite.equiv hbc.equiv
  have hrk₁ : Module.finrank Ω E₁ = r₁ := by
    have h1 := LinearMap.finrank_range_add_finrank_ker q
    rw [LinearMap.range_eq_top.2 hq, finrank_top, ← hex, LinearMap.finrank_range_of_inj hi,
      hrk, hrk₂] at h1
    omega
  exact GlobalTheory.T.locally_free_of_finite_projective R r₁ M₁ hfin₁ hproj₁ hrk₁ hbc₁

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeKernel
