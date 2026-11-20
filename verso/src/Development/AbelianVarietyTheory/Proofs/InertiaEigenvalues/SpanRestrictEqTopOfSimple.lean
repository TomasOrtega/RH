import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Proof.span_restrict_eq_top_of_simple

/- English proof (translation)
Establish `hker : W ⊓ LinearMap.ker p = ⊥`. Break down `hirr (W ⊓ LinearMap.ker p) inf_le_left (by` into its components or cases. Introduce `g v hv`. Use `⟨hW g v hv.1, ?_⟩` and prove the remaining obligations. Establish `h2 : p v = 0` using `hv.2`.

Use `show p (ρ g v) = 0`. Rewrite using `[hp, h2, map_zero]) with h | h`. Conclude with `h`. It suffices to derive a contradiction. Apply `hpw` to reduce the goal to its premises.

Establish `: w0 ∈ W ⊓ LinearMap.ker p` using `by rw [h]; exact hw0`. Conclude with `this.2`. Establish `hinj : Function.Injective (p.domRestrict W)`. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `w hw`.

Establish `h1 : (w : V) ∈ W ⊓ LinearMap.ker p` using `⟨w.2, hw⟩`. Rewrite `h1` using `[hker]`. Conclude with `Subtype.ext h1`. Establish `hsurj : Function.Surjective (p.domRestrict W)`. Introduce `y`.

Take `⟨φ, hφ⟩` from `Module.Projective.exists_dual_eq_one k hpw`. Establish `key : ∀ f ∈ Submodule.span k (Set.range σ), f (p w0) ∈ LinearMap.range (p.domRestrict W)`. Introduce `f hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨g, rfl⟩` from `hx`. Conclude with `⟨⟨ρ g w0, hW g w0 hw0⟩, hp g w0⟩`. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => exact Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx => exact Submodule.smul_mem _ a hx`.

Use `key (φ.smulRight y) (by rw [hσ]; trivial)` as an intermediate fact. Simplify `this` using `[hφ]`. Set `e : W ≃ₗ[k] Y` to `LinearEquiv.ofBijective (p.domRestrict W) ⟨hinj, hsurj⟩`. Establish `he : ∀ g, e.symm.conj (σ g) = (ρ g).restrict (hW g)`. Introduce `g`.

Use `ext1 w`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[LinearEquiv.conj_apply_apply]`. Simplify using `only [LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]`. Conclude with `(hp g w).symm`.

Establish `hr : (Set.range fun g => (ρ g).restrict (hW g)) = (e.symm.conj : Module.End k Y →ₗ[k] Module.End k W) '' Set.range σ`. Rewrite using `[← Set.range_comp]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Conclude with `(he g).symm`.

Rewrite using `[hr, ← Submodule.map_span, hσ, Submodule.map_top, LinearEquiv.range]`.
-/
theorem span_eq_top_of_equivariant {k Γ : Type} [Field k] [Group Γ] {V : Type} [AddCommGroup V]
    [Module k V] {Y : Type} [AddCommGroup Y] [Module k Y] (ρ : Representation k Γ V)
    (σ : Γ → (Y →ₗ[k] Y)) (hσ : Submodule.span k (Set.range σ) = ⊤)
    (p : V →ₗ[k] Y) (hp : ∀ g v, p (ρ g v) = σ g (p v))
    (W : Submodule k V) (hW : Stable ρ W) (w0 : V) (hw0 : w0 ∈ W) (hpw : p w0 ≠ 0)
    (hirr : ∀ U : Submodule k V, U ≤ W → Stable ρ U → U = ⊥ ∨ U = W) :
    Submodule.span k (Set.range fun g => (ρ g).restrict (hW g)) = ⊤ := by
  have hker : W ⊓ LinearMap.ker p = ⊥ := by
    rcases hirr (W ⊓ LinearMap.ker p) inf_le_left (by
      intro g v hv
      refine ⟨hW g v hv.1, ?_⟩
      have h2 : p v = 0 := hv.2
      show p (ρ g v) = 0
      rw [hp, h2, map_zero]) with h | h
    · exact h
    · exfalso
      apply hpw
      have : w0 ∈ W ⊓ LinearMap.ker p := by rw [h]; exact hw0
      exact this.2
  have hinj : Function.Injective (p.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro w hw
    have h1 : (w : V) ∈ W ⊓ LinearMap.ker p := ⟨w.2, hw⟩
    rw [hker] at h1
    exact Subtype.ext h1
  have hsurj : Function.Surjective (p.domRestrict W) := by
    intro y
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hpw
    have key : ∀ f ∈ Submodule.span k (Set.range σ), f (p w0) ∈ LinearMap.range (p.domRestrict W) := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        exact ⟨⟨ρ g w0, hW g w0 hw0⟩, hp g w0⟩
      | zero => exact Submodule.zero_mem _
      | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
      | smul a x _ hx => exact Submodule.smul_mem _ a hx
    have := key (φ.smulRight y) (by rw [hσ]; trivial)
    simpa [hφ] using this
  let e : W ≃ₗ[k] Y := LinearEquiv.ofBijective (p.domRestrict W) ⟨hinj, hsurj⟩
  have he : ∀ g, e.symm.conj (σ g) = (ρ g).restrict (hW g) := by
    intro g
    ext1 w
    apply e.injective
    rw [LinearEquiv.conj_apply_apply]
    simp only [LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
    exact (hp g w).symm
  have hr : (Set.range fun g => (ρ g).restrict (hW g))
      = (e.symm.conj : Module.End k Y →ₗ[k] Module.End k W) '' Set.range σ := by
    rw [← Set.range_comp]
    congr 1
    funext g
    exact (he g).symm
  rw [hr, ← Submodule.map_span, hσ, Submodule.map_top, LinearEquiv.range]

/- English proof (translation)
Introduce `k Γ _ _ V _ _ _ ρ h W hW hne hirr`. Take `⟨ι, _, _, Vs, hs, hI, -, hspan, -⟩` from `h`. Set `D` to `LinearEquiv.ofBijective (DirectSum.coeLinearMap Vs) hI`. Set `p : ∀ j, V →ₗ[k] Vs j` to `fun j => (DirectSum.component k ι (fun j => Vs j) j).comp D.symm.toLinearMap`. Establish `hpdef : ∀ j v, p j v = D.symm v j` using `fun _ _ => rfl`.

Establish `hp : ∀ j g v, p j (ρ g v) = (ρ g).restrict (hs j g) (p j v)`. Introduce `j g v`. Establish `hv : v ∈ ⨆ i, Vs i` using `by rw [hI.submodule_iSup_eq_top]; trivial`. Proceed by induction on `hv using Submodule.iSup_induction' with`. Consider the case `mem i x hx`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[hpdef, hpdef, hI.ofBijective_coeLinearMap_of_mem hx, hI.ofBijective_coeLinearMap_of_mem (hs i g x hx)]`. Both sides reduce to the same expression. Rewrite using `[hpdef, hpdef, hI.ofBijective_coeLinearMap_of_mem_ne hij hx, hI.ofBijective_coeLinearMap_of_mem_ne hij (hs i g x hx), map_zero]`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp only [map_add, hx, hy]`. Take `⟨w0, hw0, hw0'⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Establish `: ∃ j, p j w0 ≠ 0`. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Apply `hw0'` to reduce the goal to its premises. Establish `: D.symm w0 = 0` using `DFinsupp.ext hcon`. Simplify using `using this`. Take `⟨j, hj⟩` from `this`.

Conclude with `span_eq_top_of_equivariant ρ _ (hspan j) (p j) (hp j) W hW w0 hw0 hj hirr`.
-/
theorem span_restrict_eq_top_of_irreducible : ∀ {k Γ : Type} [Field k] [Group Γ] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k Γ V), AbsIrrDistinct ρ → ∀ (W : Submodule k V) (hW : Stable ρ W), W ≠ ⊥ → (∀ U : Submodule k V, U ≤ W → Stable ρ U → U = ⊥ ∨ U = W) → Submodule.span k (Set.range fun g => (ρ g).restrict (hW g)) = ⊤ := by
  intro k Γ _ _ V _ _ _ ρ h W hW hne hirr
  obtain ⟨ι, _, _, Vs, hs, hI, -, hspan, -⟩ := h
  let D := LinearEquiv.ofBijective (DirectSum.coeLinearMap Vs) hI
  let p : ∀ j, V →ₗ[k] Vs j := fun j =>
    (DirectSum.component k ι (fun j => Vs j) j).comp D.symm.toLinearMap
  have hpdef : ∀ j v, p j v = D.symm v j := fun _ _ => rfl
  have hp : ∀ j g v, p j (ρ g v) = (ρ g).restrict (hs j g) (p j v) := by
    intro j g v
    have hv : v ∈ ⨆ i, Vs i := by rw [hI.submodule_iSup_eq_top]; trivial
    induction hv using Submodule.iSup_induction' with
    | mem i x hx =>
      by_cases hij : i = j
      · subst hij
        rw [hpdef, hpdef, hI.ofBijective_coeLinearMap_of_mem hx,
          hI.ofBijective_coeLinearMap_of_mem (hs i g x hx)]
        rfl
      · rw [hpdef, hpdef, hI.ofBijective_coeLinearMap_of_mem_ne hij hx,
          hI.ofBijective_coeLinearMap_of_mem_ne hij (hs i g x hx), map_zero]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
  obtain ⟨w0, hw0, hw0'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have : ∃ j, p j w0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hw0'
    have : D.symm w0 = 0 := DFinsupp.ext hcon
    simpa using this
  obtain ⟨j, hj⟩ := this
  exact span_eq_top_of_equivariant ρ _ (hspan j) (p j) (hp j) W hW w0 hw0 hj hirr

end GlobalTheory.Proof.span_restrict_eq_top_of_simple
