import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Mathlib.GroupTheory.FiniteAbelian.Duality

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

/- English proof (translation)
Use `haveI : NeZero (Nat.card kˣ) := ⟨Nat.card_pos.ne'⟩`. Use `HasEnoughRootsOfUnity.of_card_le ?_` and prove the remaining obligations. Establish `htop : rootsOfUnity (Nat.card kˣ) k = ⊤`. Use `eq_top_iff.mpr fun x _ => ?_` and prove the remaining obligations. Rewrite using `[mem_rootsOfUnity]`.

Conclude with `pow_card_eq_one'`. Rewrite using `[htop, Subgroup.card_top]`.
-/
private theorem UpperTheory.V.Loc.finite_field_enough_roots_of_unity (k : Type) [Field k] [Finite k] :
    HasEnoughRootsOfUnity k (Nat.card kˣ) := by
  haveI : NeZero (Nat.card kˣ) := ⟨Nat.card_pos.ne'⟩
  refine HasEnoughRootsOfUnity.of_card_le ?_
  have htop : rootsOfUnity (Nat.card kˣ) k = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    rw [mem_rootsOfUnity]
    exact pow_card_eq_one'
  rw [htop, Subgroup.card_top]

/- English proof (translation)
Set `Φ : G →* (J → kˣ)` to `Pi.monoidHom χ`. Set `A` to `Φ.range`. Establish `hker : Φ.ker ≤ ω.ker` using `fun g hg => by`. Rewrite `hg`, the goal using `[MonoidHom.mem_ker]`. Conclude with `h g fun j => congrFun hg j`.

Set `ψ : A →* kˣ` to `(QuotientGroup.lift Φ.ker ω hker).comp (QuotientGroup.quotientKerEquivRange Φ).symm.toMonoidHom`. Establish `hψ : ∀ g, ψ (Φ.rangeRestrict g) = ω g`. Introduce `g`. Establish `hs : (QuotientGroup.quotientKerEquivRange Φ).symm (Φ.rangeRestrict g) = (g : G ⧸ Φ.ker)`. Rewrite using `[MulEquiv.symm_apply_eq]`.

Both sides reduce to the same expression. Use `show QuotientGroup.lift Φ.ker ω hker ((QuotientGroup.quotientKerEquivRange Φ).symm (Φ.rangeRestrict g)) = ω g`. Rewrite using `[hs]`. Both sides reduce to the same expression. Set `e : J → (A →* kˣ)` to `fun j => (Pi.evalMonoidHom (fun _ : J => kˣ) j).comp A.subtype`.

Establish `he : ∀ j, (e j).comp Φ.rangeRestrict = χ j` using `fun j => by`. Use extensionality with `g`. Both sides reduce to the same expression. Establish `hω : ω = ψ.comp Φ.rangeRestrict`. Use extensionality with `g`.

Rewrite using `[MonoidHom.comp_apply, hψ]`. Use `haveI : Finite (A →* kˣ) := Finite.of_injective (fun f : A →* kˣ => (f : A → kˣ)) DFunLike.coe_injective`. Use `haveI : NeZero (Nat.card kˣ) := ⟨Nat.card_pos.ne'⟩`. Use `haveI := UpperTheory.V.Loc.finite_field_enough_roots_of_unity k`. Use `haveI : HasEnoughRootsOfUnity k (Monoid.exponent A) := by`.

Use `HasEnoughRootsOfUnity.of_dvd k (n := Nat.card kˣ) ?_` and prove the remaining obligations. Use `Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_` and prove the remaining obligations. Use `Subtype.ext (funext fun j => ?_)` and prove the remaining obligations. Simplify using `[pow_card_eq_one']`. Use `haveI : HasEnoughRootsOfUnity k (Monoid.exponent (A →* kˣ)) := by`.

Use `HasEnoughRootsOfUnity.of_dvd k (n := Nat.card kˣ) ?_` and prove the remaining obligations. Use `Monoid.exponent_dvd_of_forall_pow_eq_one fun f => ?_` and prove the remaining obligations. Use `MonoidHom.ext fun a => ?_` and prove the remaining obligations. Simplify using `[pow_card_eq_one']`. Establish `hS : ψ ∈ Subgroup.closure (Set.range e)`.

Rewrite using `[← CommGroup.forall_monoidHom_apply_eq_one_iff k]`. Introduce `η hη`. Establish `ha : CommGroup.monoidHomMonoidHomEquiv A k η = 1`. Use `Subtype.ext (funext fun j => ?_)` and prove the remaining obligations. Establish `hj` using `CommGroup.apply_monoidHomMonoidHomEquiv k (e j) η`.

Rewrite `hj` using `[hη _ (Subgroup.subset_closure ⟨j, rfl⟩)]`. Conclude with `hj`. Rewrite using `[← CommGroup.apply_monoidHomMonoidHomEquiv k ψ η, ha, map_one]`. Establish `key : ∀ φ ∈ Subgroup.closure (Set.range e), φ.comp Φ.rangeRestrict ∈ Subgroup.closure (Set.range χ)`. Introduce `φ hφ`.

Proceed by induction on `hφ using Subgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨j, rfl⟩` from `hx`. Rewrite using `[he]`. Conclude with `Subgroup.subset_closure ⟨j, rfl⟩`.

Consider the case `one`. Rewrite using `[MonoidHom.one_comp]`. Conclude with `one_mem _`. Consider the case `mul x y _ _ hx hy`. Rewrite using `[MonoidHom.mul_comp]`.

Conclude with `mul_mem hx hy`. Consider the case `inv x _ hx`. Rewrite using `[MonoidHom.inv_comp]`. Conclude with `inv_mem hx`. Rewrite using `[hω]`.

Conclude with `key ψ hS`.
-/
private theorem UpperTheory.V.Loc.mem_closure_of_kernel_containment {G k J : Type} [Group G] [Field k] [Finite k] [Finite J]
    (χ : J → G →* kˣ) (ω : G →* kˣ) (h : ∀ g, (∀ j, χ j g = 1) → ω g = 1) :
    ω ∈ Subgroup.closure (Set.range χ) := by
  classical
  let Φ : G →* (J → kˣ) := Pi.monoidHom χ
  let A := Φ.range
  have hker : Φ.ker ≤ ω.ker := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    exact h g fun j => congrFun hg j
  let ψ : A →* kˣ := (QuotientGroup.lift Φ.ker ω hker).comp
    (QuotientGroup.quotientKerEquivRange Φ).symm.toMonoidHom
  have hψ : ∀ g, ψ (Φ.rangeRestrict g) = ω g := by
    intro g
    have hs : (QuotientGroup.quotientKerEquivRange Φ).symm (Φ.rangeRestrict g)
        = (g : G ⧸ Φ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift Φ.ker ω hker
      ((QuotientGroup.quotientKerEquivRange Φ).symm (Φ.rangeRestrict g)) = ω g
    rw [hs]
    rfl
  let e : J → (A →* kˣ) := fun j => (Pi.evalMonoidHom (fun _ : J => kˣ) j).comp A.subtype
  have he : ∀ j, (e j).comp Φ.rangeRestrict = χ j := fun j => by
    ext g
    rfl
  have hω : ω = ψ.comp Φ.rangeRestrict := by
    ext g
    rw [MonoidHom.comp_apply, hψ]
  haveI : Finite (A →* kˣ) :=
    Finite.of_injective (fun f : A →* kˣ => (f : A → kˣ)) DFunLike.coe_injective
  haveI : NeZero (Nat.card kˣ) := ⟨Nat.card_pos.ne'⟩
  haveI := UpperTheory.V.Loc.finite_field_enough_roots_of_unity k
  haveI : HasEnoughRootsOfUnity k (Monoid.exponent A) := by
    refine HasEnoughRootsOfUnity.of_dvd k (n := Nat.card kˣ) ?_
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
    refine Subtype.ext (funext fun j => ?_)
    simp [pow_card_eq_one']
  haveI : HasEnoughRootsOfUnity k (Monoid.exponent (A →* kˣ)) := by
    refine HasEnoughRootsOfUnity.of_dvd k (n := Nat.card kˣ) ?_
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun f => ?_
    refine MonoidHom.ext fun a => ?_
    simp [pow_card_eq_one']
  have hS : ψ ∈ Subgroup.closure (Set.range e) := by
    rw [← CommGroup.forall_monoidHom_apply_eq_one_iff k]
    intro η hη
    have ha : CommGroup.monoidHomMonoidHomEquiv A k η = 1 := by
      refine Subtype.ext (funext fun j => ?_)
      have hj := CommGroup.apply_monoidHomMonoidHomEquiv k (e j) η
      rw [hη _ (Subgroup.subset_closure ⟨j, rfl⟩)] at hj
      exact hj
    rw [← CommGroup.apply_monoidHomMonoidHomEquiv k ψ η, ha, map_one]
  have key : ∀ φ ∈ Subgroup.closure (Set.range e),
      φ.comp Φ.rangeRestrict ∈ Subgroup.closure (Set.range χ) := by
    intro φ hφ
    induction hφ using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [he]
      exact Subgroup.subset_closure ⟨j, rfl⟩
    | one =>
      rw [MonoidHom.one_comp]
      exact one_mem _
    | mul x y _ _ hx hy =>
      rw [MonoidHom.mul_comp]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [MonoidHom.inv_comp]
      exact inv_mem hx
  rw [hω]
  exact key ψ hS

/- English proof (translation)
Introduce `G k ι _ _ _ _ κ ω`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, hω⟩ hmem`. Apply `hω` to reduce the goal to its premises. Use `Subgroup.closure_induction (p := fun x _ => x g = 1) ?_ ?_ ?_ ?_ hmem` and prove the remaining obligations.

Introduce and unpack `_ ⟨q, rfl⟩`. Simplify using `[hg q.1 q.2]`. Both sides reduce to the same expression. Introduce `x y _ _ hx hy`. Simplify using `[hx, hy]`.

Introduce `x _ hx`. Simplify using `[hx]`. Introduce `hn`. Assume the negation of the conclusion as `hc`. Apply `hn` to reduce the goal to its premises.

Use `UpperTheory.V.Loc.mem_closure_of_kernel_containment _ ω fun g hg => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Use `hc ⟨g, fun i j => ?_, hne⟩` and prove the remaining obligations. Use `hg (i, j)` as an intermediate fact. Simplify `this` using `[div_eq_one]`.
-/
theorem UpperTheory.V.Loc.v0e :
    ∀ {G k ι : Type} [Group G] [Field k] [Finite k] [Finite ι] (κ : ι → G →* kˣ) (ω : G →* kˣ), (∃ g, (∀ i j, κ i g = κ j g) ∧ ω g ≠ 1) ↔ ω ∉ Subgroup.closure (Set.range fun q : ι × ι => κ q.1 / κ q.2) := by
  intro G k ι _ _ _ _ κ ω
  constructor
  · rintro ⟨g, hg, hω⟩ hmem
    apply hω
    refine Subgroup.closure_induction (p := fun x _ => x g = 1) ?_ ?_ ?_ ?_ hmem
    · rintro _ ⟨q, rfl⟩
      simp [hg q.1 q.2]
    · rfl
    · intro x y _ _ hx hy
      simp [hx, hy]
    · intro x _ hx
      simp [hx]
  · intro hn
    by_contra hc
    apply hn
    refine UpperTheory.V.Loc.mem_closure_of_kernel_containment _ ω fun g hg => ?_
    by_contra hne
    refine hc ⟨g, fun i j => ?_, hne⟩
    have := hg (i, j)
    simpa [div_eq_one] using this
