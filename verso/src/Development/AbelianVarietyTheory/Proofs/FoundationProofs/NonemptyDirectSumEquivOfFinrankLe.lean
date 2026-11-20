import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Formalism.LocalToGlobal.Columns.PolyFn
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory

/- English proof (translation)
Establish `hρ : ∀ g (x : ⨁ i, V i) j, (Representation.directSum ρ g x) j = ρ j g (x j)`. Introduce `g x j`. Both sides reduce to the same expression. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`.

Introduce `x hx _`. Use extensionality with `j`. Conclude with `hx j (Finset.notMem_empty j)`. Consider the case `insert i t hi ih`. Set `K : Submodule k (⨁ i, V i)` to `{ carrier := {x | (∀ j, j ∉ insert i t → x j = 0) ∧ Φ x = 0} add_mem' := fun {a b} ha hb => ⟨fun j hj => by`.

Rewrite using `[DirectSum.add_apply, ha.1 j hj, hb.1 j hj, add_zero],`. Use `by rw [map_add, ha.2, hb.2, add_zero]⟩`. Use the proof step `zero_mem' := ⟨fun j _ => rfl, map_zero Φ⟩`. Use the proof step `smul_mem' := fun c a ha => ⟨fun j hj => by`. Rewrite using `[DirectSum.smul_apply, ha.1 j hj, smul_zero],`.

Use `by rw [map_smul, ha.2, smul_zero]⟩ }`. Establish `hK : ∀ g x, x ∈ K → Representation.directSum ρ g x ∈ K`. Introduce `g x hx`. Use `⟨fun j hj => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hρ, hx.1 j hj, map_zero]`.

Rewrite using `[Φ.isIntertwining, hx.2, map_zero]`. Establish `hz : ∀ x ∈ K, x i = 0 → x = 0`. Introduce `x hx h0`. Use `ih x (fun j hj => ?_) hx.2` and prove the remaining obligations. Distinguish the cases in `hji : j = i`.

Substitute `hji` using the available equality. Conclude with `h0`. Conclude with `hx.1 j (by simp [hji, hj])`. Set `p : K →ₗ[k] V i` to `DirectSum.component k ι V i ∘ₗ K.subtype`. Establish `hp : ∀ x : K, p x = x.1 i` using `fun x => rfl`.

Establish `hinj : Function.Injective p`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Conclude with `Subtype.ext (hz x.1 x.2 hx)`. Set `R : Subrepresentation (ρ i)` to `{ toSubmodule := LinearMap.range p apply_mem_toSubmodule := by`.

Introduce and unpack `g _ ⟨x, rfl⟩`. Conclude with `⟨⟨_, hK g x.1 x.2⟩, rfl⟩ }`. Introduce `x hx1 hx2`. Establish `hx : x ∈ K` using `⟨hx1, hx2⟩`. Use `hirr i` as an intermediate fact.

Break down `eq_bot_or_eq_top R with hR | hR` into its components or cases. Apply `hz x hx` to reduce the goal to its premises. Establish `: x i ∈ R.toSubmodule` using `⟨⟨x, hx⟩, rfl⟩`. Rewrite `this` using `[hR]`. Conclude with `this`.

Establish `hsurj : Function.Surjective p`. Introduce `v`. Establish `: v ∈ R.toSubmodule` using `by rw [hR]; trivial`. Conclude with `this`. Set `e` to `LinearEquiv.ofBijective p ⟨hinj, hsurj⟩`.

Establish `he : ∀ y : K, e.symm (y.1 i) = y` using `fun y => e.symm_apply_apply y`. Establish `hoff : ∀ j, j ≠ i → x j = 0`. Introduce `j hj`. Set `ψ : (ρ i).IntertwiningMap (ρ j)` to `LinearMap.intertwiningMap_of_isIntertwiningMap (ρ i) (ρ j) (DirectSum.component k ι V j ∘ₗ K.subtype ∘ₗ e.symm.toLinearMap) (by`. Introduce `g v`.

Take `⟨y, rfl⟩` from `hsurj v`. Establish `h1` using `he ⟨_, hK g y.1 y.2⟩`. Establish `h2` using `he y`. Express the relevant statement in the definitionally equal form `((e.symm (ρ i g (y.1 i)) : K) : ⨁ i, V i) j = ρ j g (((e.symm (y.1 i) : K) : ⨁ i, V i) j)`. Rewrite using `[h2, ← hρ, h1]`.

Use the proof step `rfl)`. Establish `h0 : ψ = 0` using `hdis i j (Ne.symm hj) ψ`. Establish `h3 : ψ (x i) = x j`. Express the relevant statement in the definitionally equal form `((e.symm (x i) : K) : ⨁ i, V i) j = x j`. Rewrite using `[he ⟨x, hx⟩]`.

Rewrite using `[← h3, h0]`. Both sides reduce to the same expression. Establish `hxe : x = DirectSum.lof k ι V i (x i)`. Use extensionality with `j`. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Simplify using `[DirectSum.lof_eq_of]`. Rewrite using `[hoff j hj, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hj]`. Apply `hz x hx` to reduce the goal to its premises. Apply `hΦ` to reduce the goal to its premises.

Rewrite using `[← hxe]`. Conclude with `hx2`.
-/
theorem directSum_eq_zero_of_toModule_eq_zero {k G ι W : Type} [Field k] [Group G] [DecidableEq ι]
    {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [AddCommGroup W] [Module k W] (ρ : ∀ i, Representation k G (V i)) (σ : Representation k G W)
    (hirr : ∀ i, (ρ i).IsIrreducible)
    (hdis : ∀ i j, i ≠ j → ∀ φ : (ρ i).IntertwiningMap (ρ j), φ = 0)
    (Φ : (Representation.directSum ρ).IntertwiningMap σ)
    (hΦ : ∀ i (v : V i), Φ (DirectSum.lof k ι V i v) = 0 → v = 0) (s : Finset ι) :
    ∀ x : ⨁ i, V i, (∀ j, j ∉ s → x j = 0) → Φ x = 0 → x = 0 := by
  have hρ : ∀ g (x : ⨁ i, V i) j, (Representation.directSum ρ g x) j = ρ j g (x j) := by
    intro g x j
    rfl
  induction s using Finset.induction_on with
  | empty =>
    intro x hx _
    ext j
    exact hx j (Finset.notMem_empty j)
  | insert i t hi ih =>
    let K : Submodule k (⨁ i, V i) :=
      { carrier := {x | (∀ j, j ∉ insert i t → x j = 0) ∧ Φ x = 0}
        add_mem' := fun {a b} ha hb => ⟨fun j hj => by
          rw [DirectSum.add_apply, ha.1 j hj, hb.1 j hj, add_zero],
          by rw [map_add, ha.2, hb.2, add_zero]⟩
        zero_mem' := ⟨fun j _ => rfl, map_zero Φ⟩
        smul_mem' := fun c a ha => ⟨fun j hj => by
          rw [DirectSum.smul_apply, ha.1 j hj, smul_zero],
          by rw [map_smul, ha.2, smul_zero]⟩ }
    have hK : ∀ g x, x ∈ K → Representation.directSum ρ g x ∈ K := by
      intro g x hx
      refine ⟨fun j hj => ?_, ?_⟩
      · rw [hρ, hx.1 j hj, map_zero]
      · rw [Φ.isIntertwining, hx.2, map_zero]
    have hz : ∀ x ∈ K, x i = 0 → x = 0 := by
      intro x hx h0
      refine ih x (fun j hj => ?_) hx.2
      by_cases hji : j = i
      · subst hji; exact h0
      · exact hx.1 j (by simp [hji, hj])
    let p : K →ₗ[k] V i := DirectSum.component k ι V i ∘ₗ K.subtype
    have hp : ∀ x : K, p x = x.1 i := fun x => rfl
    have hinj : Function.Injective p := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      exact Subtype.ext (hz x.1 x.2 hx)
    let R : Subrepresentation (ρ i) :=
      { toSubmodule := LinearMap.range p
        apply_mem_toSubmodule := by
          rintro g _ ⟨x, rfl⟩
          exact ⟨⟨_, hK g x.1 x.2⟩, rfl⟩ }
    intro x hx1 hx2
    have hx : x ∈ K := ⟨hx1, hx2⟩
    have := hirr i
    rcases eq_bot_or_eq_top R with hR | hR
    · apply hz x hx
      have : x i ∈ R.toSubmodule := ⟨⟨x, hx⟩, rfl⟩
      rw [hR] at this
      exact this
    · have hsurj : Function.Surjective p := by
        intro v
        have : v ∈ R.toSubmodule := by rw [hR]; trivial
        exact this
      let e := LinearEquiv.ofBijective p ⟨hinj, hsurj⟩
      have he : ∀ y : K, e.symm (y.1 i) = y := fun y => e.symm_apply_apply y
      have hoff : ∀ j, j ≠ i → x j = 0 := by
        intro j hj
        let ψ : (ρ i).IntertwiningMap (ρ j) :=
          LinearMap.intertwiningMap_of_isIntertwiningMap (ρ i) (ρ j)
            (DirectSum.component k ι V j ∘ₗ K.subtype ∘ₗ e.symm.toLinearMap) (by
              intro g v
              obtain ⟨y, rfl⟩ := hsurj v
              have h1 := he ⟨_, hK g y.1 y.2⟩
              have h2 := he y
              change ((e.symm (ρ i g (y.1 i)) : K) : ⨁ i, V i) j
                = ρ j g (((e.symm (y.1 i) : K) : ⨁ i, V i) j)
              rw [h2, ← hρ, h1]
              rfl)
        have h0 : ψ = 0 := hdis i j (Ne.symm hj) ψ
        have h3 : ψ (x i) = x j := by
          change ((e.symm (x i) : K) : ⨁ i, V i) j = x j
          rw [he ⟨x, hx⟩]
        rw [← h3, h0]
        rfl
      have hxe : x = DirectSum.lof k ι V i (x i) := by
        ext j
        by_cases hj : j = i
        · subst hj
          simp [DirectSum.lof_eq_of]
        · rw [hoff j hj, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hj]
      apply hz x hx
      apply hΦ
      rw [← hxe]
      exact hx2

/- English proof (translation)
Introduce `k G ι W _ _ _ V _ _ _ _ _ _ ρ σ hirr hdis hex hle`. Use `Fintype.ofFinite ι` as an intermediate fact. Use `choose φ hφ using hex`. Set `Φ : (Representation.directSum ρ).IntertwiningMap σ` to `⟨DirectSum.toModule k ι W (fun i => (φ i).toLinearMap), fun g => by`. Use extensionality with `i v`.

Simplify using `[(φ i).isIntertwining]⟩`. Establish `hinj : Function.Injective Φ.toLinearMap`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Use `directSum_eq_zero_of_toModule_eq_zero ρ σ hirr hdis Φ ?_ Finset.univ x (fun j hj => absurd (Finset.mem_univ j) hj) hx` and prove the remaining obligations.

Introduce `i v hv`. Use `hirr i` as an intermediate fact. Establish `hi` using `(Representation.IsIrreducible.injective_or_eq_zero (φ i)).resolve_right (hφ i)`. Establish `h1 : Φ (DirectSum.lof k ι V i v) = φ i v` using `DirectSum.toModule_lof k (φ := fun i => (φ i).toLinearMap) i v`. Apply `hi` to reduce the goal to its premises.

Rewrite using `[← h1, hv, map_zero]`. Establish `heq : Module.finrank k (⨁ i, V i) = Module.finrank k W` using `le_antisymm (LinearMap.finrank_le_finrank_of_injective hinj) hle`. Establish `hsurj` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hinj`. Conclude with `⟨Representation.Equiv.mk (LinearEquiv.ofBijective Φ.toLinearMap ⟨hinj, hsurj⟩) Φ.isIntertwining'⟩`.
-/
theorem nonempty_directSum_equiv_of_finrank_le : ∀ (k G ι W : Type) [Field k] [Group G] [Finite ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] [AddCommGroup W] [Module k W] [FiniteDimensional k W] (ρ : ∀ i, Representation k G (V i)) (σ : Representation k G W), (∀ i, (ρ i).IsIrreducible) → (∀ i j, i ≠ j → ∀ φ : (ρ i).IntertwiningMap (ρ j), φ = 0) → (∀ i, ∃ φ : (ρ i).IntertwiningMap σ, φ ≠ 0) → Module.finrank k W ≤ Module.finrank k (⨁ i, V i) → Nonempty ((Representation.directSum ρ).Equiv σ) := by
  intro k G ι W _ _ _ V _ _ _ _ _ _ ρ σ hirr hdis hex hle
  classical
  have := Fintype.ofFinite ι
  choose φ hφ using hex
  let Φ : (Representation.directSum ρ).IntertwiningMap σ :=
    ⟨DirectSum.toModule k ι W (fun i => (φ i).toLinearMap), fun g => by
      ext i v
      simp [(φ i).isIntertwining]⟩
  have hinj : Function.Injective Φ.toLinearMap := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine directSum_eq_zero_of_toModule_eq_zero ρ σ hirr hdis Φ ?_ Finset.univ x
      (fun j hj => absurd (Finset.mem_univ j) hj) hx
    intro i v hv
    have := hirr i
    have hi := (Representation.IsIrreducible.injective_or_eq_zero (φ i)).resolve_right (hφ i)
    have h1 : Φ (DirectSum.lof k ι V i v) = φ i v :=
      DirectSum.toModule_lof k (φ := fun i => (φ i).toLinearMap) i v
    apply hi
    rw [← h1, hv, map_zero]
  have heq : Module.finrank k (⨁ i, V i) = Module.finrank k W :=
    le_antisymm (LinearMap.finrank_le_finrank_of_injective hinj) hle
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hinj
  exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective Φ.toLinearMap ⟨hinj, hsurj⟩)
    Φ.isIntertwining'⟩

end GlobalTheory
