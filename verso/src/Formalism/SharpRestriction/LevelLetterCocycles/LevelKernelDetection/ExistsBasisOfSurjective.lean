import Mathlib

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Module

/- English proof (translation)
Use `⟨(Pi.basisFun R (Fin m₂)).constr R (fun j => (hf (Pi.single j 1)).choose), ?_⟩` and prove the remaining obligations. Establish `h : f ∘ₗ (Pi.basisFun R (Fin m₂)).constr R (fun j => (hf (Pi.single j 1)).choose) = LinearMap.id`. Use `(Pi.basisFun R (Fin m₂)).ext fun j => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, Basis.constr_basis, LinearMap.id_apply, Pi.basisFun_apply]`. Conclude with `(hf (Pi.single j 1)).choose_spec`.

Introduce `y`. Conclude with `LinearMap.congr_fun h y`.
-/
private theorem exists_linear_rightInverse_of_surjective {R : Type} [CommRing R] {m₁ m₂ : ℕ}
    (f : (Fin m₁ → R) →ₗ[R] (Fin m₂ → R)) (hf : Function.Surjective f) :
    ∃ s : (Fin m₂ → R) →ₗ[R] (Fin m₁ → R), ∀ y, f (s y) = y := by
  refine ⟨(Pi.basisFun R (Fin m₂)).constr R (fun j => (hf (Pi.single j 1)).choose), ?_⟩
  have h : f ∘ₗ (Pi.basisFun R (Fin m₂)).constr R (fun j => (hf (Pi.single j 1)).choose)
      = LinearMap.id := by
    refine (Pi.basisFun R (Fin m₂)).ext fun j => ?_
    rw [LinearMap.comp_apply, Basis.constr_basis, LinearMap.id_apply, Pi.basisFun_apply]
    exact (hf (Pi.single j 1)).choose_spec
  intro y
  exact LinearMap.congr_fun h y

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_linear_rightInverse_of_surjective f hf`. Establish `hfk : ∀ k : LinearMap.ker f, f (k : Fin m₁ → R) = 0` using `fun k => LinearMap.mem_ker.mp k.2`. Set `q : (Fin m₁ → R) →ₗ[R] (Fin m₁ → R)` to `LinearMap.id - s ∘ₗ f`. Establish `hq : ∀ x, q x = x - s (f x)` using `fun x => by first`. Consider the case `rfl`.

Consider the case `simp [q]`. Establish `hmem : ∀ x, q x ∈ LinearMap.ker f` using `fun x => by`. Rewrite using `[hq, LinearMap.mem_ker, map_sub, hs, sub_self]`. Set `r : (Fin m₁ → R) →ₗ[R] LinearMap.ker f` to `LinearMap.codRestrict (LinearMap.ker f) q hmem`. Establish `hr : ∀ x, (r x : Fin m₁ → R) = x - s (f x)` using `fun x => by first`.

Consider the case `exact hq x`. Consider the case `simp [r, hq]`. Establish `hrk : ∀ k : LinearMap.ker f, r k = k` using `fun k => by`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hr, hfk k, map_zero, sub_zero]`.

Establish `hfg : ∀ p : (Fin m₂ → R) × LinearMap.ker f, f (s p.1 + (p.2 : Fin m₁ → R)) = p.1` using `fun p => by rw [map_add, hs, hfk, add_zero]`. Set `g : (Fin m₂ → R) × LinearMap.ker f →ₗ[R] (Fin m₁ → R)` to `LinearMap.coprod s (LinearMap.ker f).subtype`. Set `h : (Fin m₁ → R) →ₗ[R] (Fin m₂ → R) × LinearMap.ker f` to `LinearMap.prod f r`. Establish `hg : ∀ p, g p = s p.1 + (p.2 : Fin m₁ → R)` using `fun p => by first`. Consider the case `rfl`.

Consider the case `simp [g]`. Establish `hh : ∀ x, h x = (f x, r x)` using `fun x => by first`. Consider the case `rfl`. Consider the case `simp [h]`. Establish `h₁ : g ∘ₗ h = LinearMap.id` using `LinearMap.ext fun x => by`.

Rewrite using `[LinearMap.comp_apply, hh, hg, LinearMap.id_apply]`. Use `show s (f x) + (r x : Fin m₁ → R) = x`. Rewrite using `[hr]`. Normalize the expressions using the abelian group laws. Establish `h₂ : h ∘ₗ g = LinearMap.id` using `LinearMap.ext fun p => by`.

Rewrite using `[LinearMap.comp_apply, hg, hh, LinearMap.id_apply, hfg p]`. Use `Prod.ext rfl (Subtype.ext ?_)` and prove the remaining obligations. Use `show (r (s p.1 + (p.2 : Fin m₁ → R)) : Fin m₁ → R) = p.2`. Rewrite using `[hr, hfg p]`. Normalize the expressions using the abelian group laws.

Set `e : ((Fin m₂ → R) × LinearMap.ker f) ≃ₗ[R] (Fin m₁ → R)` to `LinearEquiv.ofLinear g h h₁ h₂`. Establish `he : ∀ p, f (e p) = p.1` using `fun p => by show f (g p) = p.1`. Rewrite using `[hg, hfg p]`. Establish `hproj : Module.Projective R (LinearMap.ker f)` using `Module.Projective.of_split (LinearMap.ker f).subtype r (LinearMap.ext fun k => by`. Rewrite using `[LinearMap.comp_apply, Submodule.subtype_apply, hrk, LinearMap.id_apply])`.

Establish `hfin : Module.Finite R (LinearMap.ker f)` using `Module.Finite.of_surjective r (fun k => ⟨k, hrk k⟩)`. Establish `hfree : Module.Free R (LinearMap.ker f)` using `by first`. Consider the case `exact Module.free_of_flat_of_isLocalRing`. Consider the case `exact Module.free_of_projective_of_isLocalRing`. Consider the case `infer_instance`.

Set `bk` to `Module.Free.chooseBasis R (LinearMap.ker f)`. Set `bp` to `(Pi.basisFun R (Fin m₂)).prod bk`. Set `b` to `bp.map e`. Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex R (LinearMap.ker f)) = m₁ - m₂`. Establish `h1` using `Module.finrank_eq_card_basis b`.

Rewrite `h1` using `[Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Establish `hb : ∀ i, f (b i) = (bp i).1` using `fun i => by`. Rewrite using `[Basis.map_apply, he]`. Use `⟨b.reindex (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFinOfCardEq hcard)), fun j => ?_, fun j => ?_⟩` and prove the remaining obligations.

Rewrite using `[Basis.reindex_apply, hb] first`. Consider the case `simp [bp, Basis.prod_apply]`. Consider the case `simp [bp]`. Rewrite using `[Basis.reindex_apply, hb] first`. Consider the case `simp [bp, Basis.prod_apply]`.

Consider the case `simp [bp]`.
-/
theorem exists_basis_of_surjective {R : Type} [CommRing R] [IsLocalRing R] {m₁ m₂ : ℕ}
    (f : (Fin m₁ → R) →ₗ[R] (Fin m₂ → R)) (hf : Function.Surjective f) :
    ∃ B : Module.Basis (Fin m₂ ⊕ Fin (m₁ - m₂)) R (Fin m₁ → R),
      (∀ j, f (B (Sum.inl j)) = Pi.single j 1) ∧ ∀ j, f (B (Sum.inr j)) = 0 := by
  obtain ⟨s, hs⟩ := exists_linear_rightInverse_of_surjective f hf
  have hfk : ∀ k : LinearMap.ker f, f (k : Fin m₁ → R) = 0 := fun k => LinearMap.mem_ker.mp k.2
  let q : (Fin m₁ → R) →ₗ[R] (Fin m₁ → R) := LinearMap.id - s ∘ₗ f
  have hq : ∀ x, q x = x - s (f x) := fun x => by
    first
    | rfl
    | simp [q]
  have hmem : ∀ x, q x ∈ LinearMap.ker f := fun x => by
    rw [hq, LinearMap.mem_ker, map_sub, hs, sub_self]
  let r : (Fin m₁ → R) →ₗ[R] LinearMap.ker f := LinearMap.codRestrict (LinearMap.ker f) q hmem
  have hr : ∀ x, (r x : Fin m₁ → R) = x - s (f x) := fun x => by
    first
    | exact hq x
    | simp [r, hq]
  have hrk : ∀ k : LinearMap.ker f, r k = k := fun k => by
    apply Subtype.ext
    rw [hr, hfk k, map_zero, sub_zero]
  have hfg : ∀ p : (Fin m₂ → R) × LinearMap.ker f, f (s p.1 + (p.2 : Fin m₁ → R)) = p.1 :=
    fun p => by rw [map_add, hs, hfk, add_zero]
  let g : (Fin m₂ → R) × LinearMap.ker f →ₗ[R] (Fin m₁ → R) :=
    LinearMap.coprod s (LinearMap.ker f).subtype
  let h : (Fin m₁ → R) →ₗ[R] (Fin m₂ → R) × LinearMap.ker f := LinearMap.prod f r
  have hg : ∀ p, g p = s p.1 + (p.2 : Fin m₁ → R) := fun p => by
    first
    | rfl
    | simp [g]
  have hh : ∀ x, h x = (f x, r x) := fun x => by
    first
    | rfl
    | simp [h]
  have h₁ : g ∘ₗ h = LinearMap.id := LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, hh, hg, LinearMap.id_apply]
    show s (f x) + (r x : Fin m₁ → R) = x
    rw [hr]
    abel
  have h₂ : h ∘ₗ g = LinearMap.id := LinearMap.ext fun p => by
    rw [LinearMap.comp_apply, hg, hh, LinearMap.id_apply, hfg p]
    refine Prod.ext rfl (Subtype.ext ?_)
    show (r (s p.1 + (p.2 : Fin m₁ → R)) : Fin m₁ → R) = p.2
    rw [hr, hfg p]
    abel
  let e : ((Fin m₂ → R) × LinearMap.ker f) ≃ₗ[R] (Fin m₁ → R) := LinearEquiv.ofLinear g h h₁ h₂
  have he : ∀ p, f (e p) = p.1 := fun p => by
    show f (g p) = p.1
    rw [hg, hfg p]
  have hproj : Module.Projective R (LinearMap.ker f) :=
    Module.Projective.of_split (LinearMap.ker f).subtype r (LinearMap.ext fun k => by
      rw [LinearMap.comp_apply, Submodule.subtype_apply, hrk, LinearMap.id_apply])
  have hfin : Module.Finite R (LinearMap.ker f) :=
    Module.Finite.of_surjective r (fun k => ⟨k, hrk k⟩)
  have hfree : Module.Free R (LinearMap.ker f) := by
    first
    | exact Module.free_of_flat_of_isLocalRing
    | exact Module.free_of_projective_of_isLocalRing
    | infer_instance
  let bk := Module.Free.chooseBasis R (LinearMap.ker f)
  let bp := (Pi.basisFun R (Fin m₂)).prod bk
  let b := bp.map e
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R (LinearMap.ker f)) = m₁ - m₂ := by
    have h1 := Module.finrank_eq_card_basis b
    rw [Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at h1
    omega
  have hb : ∀ i, f (b i) = (bp i).1 := fun i => by
    rw [Basis.map_apply, he]
  refine ⟨b.reindex (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFinOfCardEq hcard)),
    fun j => ?_, fun j => ?_⟩
  · rw [Basis.reindex_apply, hb]
    first
    | simp [bp, Basis.prod_apply]
    | simp [bp]
  · rw [Basis.reindex_apply, hb]
    first
    | simp [bp, Basis.prod_apply]
    | simp [bp]

end Formalism.MainNotions.N.Ln03.Pf
