import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.CardUNeZero

noncomputable section

open Classical

namespace PI.GGConvScalarW

open Formalism.L2.SG.GGMirabolic

/- English proof (translation)
Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nontrivial_iff_subsingleton]`. Establish `hs : IsSimpleOrder (Subrepresentation π)` using `hπ`. Take `⟨a, b, hab⟩` from `hs.toNontrivial.exists_pair_ne`. Apply `hab` to reduce the goal to its premises.

Break down `a with ⟨a, ha⟩` into its components or cases. Break down `b with ⟨b, hb⟩` into its components or cases. Use `congr 1`. Conclude with `Subsingleton.elim a b`.
-/
theorem nontrivial_of_irreducible {G : Type} [Monoid G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hπ : π.IsIrreducible) : Nontrivial V := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have hs : IsSimpleOrder (Subrepresentation π) := hπ
  obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
  apply hab
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  congr 1
  exact Subsingleton.elim a b

/- English proof (translation)
Introduce `F _ _ k V _ _ _ π hπ`. Use `haveI := nontrivial_of_irreducible π hπ`. Conclude with `Module.finrank_pos`.
-/
theorem representation_dimension_pos : DimPos := by
  intro F _ _ k V _ _ _ π hπ
  haveI := nontrivial_of_irreducible π hπ
  exact Module.finrank_pos

/- English proof (translation)
Introduce `F _ _ k V _ _ _ π hπ f hf`. Use `haveI := nontrivial_of_irreducible π hπ`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue f`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `hinv : ∀ (g : GL (Fin k) F) ⦃v : V⦄, v ∈ LinearMap.ker (f - c • LinearMap.id) → π g v ∈ LinearMap.ker (f - c • LinearMap.id)`.

Introduce `g v hv`. Simplify using `only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hv ⊢`. Establish `h1` using `congrArg (fun φ : V →ₗ[ℂ] V => φ v) (hf g)`. Simplify using `only [LinearMap.comp_apply] at h1`. Rewrite using `[← h1, ← map_smul, ← map_sub, hv, map_zero]`.

Set `W : Subrepresentation π` to `⟨LinearMap.ker (f - c • LinearMap.id), hinv⟩`. Establish `hs : IsSimpleOrder (Subrepresentation π)` using `hπ`. Take `⟨v, hv⟩` from `hc.exists_hasEigenvector`. Break down `hs.eq_bot_or_eq_top W with hW | hW` into its components or cases. It suffices to derive a contradiction.

Apply `hv.2` to reduce the goal to its premises. Establish `hvW : v ∈ LinearMap.ker (f - c • LinearMap.id)`. Simplify using `only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]`. Rewrite using `[hv.apply_eq_smul, sub_self]`. Establish `h2` using `congrArg Subrepresentation.toSubmodule hW`.

Express the relevant statement in the definitionally equal form `LinearMap.ker (f - c • LinearMap.id) = _ at h2`. Rewrite `hvW` using `[h2]`. Establish `h3 : v ∈ (⊥ : Submodule ℂ V)` using `hvW`. Simplify using `using h3`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `x`. Establish `h2` using `congrArg Subrepresentation.toSubmodule hW`. Express the relevant statement in the definitionally equal form `LinearMap.ker (f - c • LinearMap.id) = _ at h2`. Establish `hx : x ∈ LinearMap.ker (f - c • LinearMap.id)`. Rewrite using `[h2]`.

Conclude with `(show x ∈ (⊤ : Submodule ℂ V) from Submodule.mem_top)`. Simplify using `only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx`. Simplify `hx` using `[sub_eq_zero]`.
-/
theorem schur_lemma_complex : SchurC := by
  intro F _ _ k V _ _ _ π hπ f hf
  haveI := nontrivial_of_irreducible π hπ
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
  refine ⟨c, ?_⟩
  have hinv : ∀ (g : GL (Fin k) F) ⦃v : V⦄, v ∈ LinearMap.ker (f - c • LinearMap.id) →
      π g v ∈ LinearMap.ker (f - c • LinearMap.id) := by
    intro g v hv
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hv ⊢
    have h1 := congrArg (fun φ : V →ₗ[ℂ] V => φ v) (hf g)
    simp only [LinearMap.comp_apply] at h1
    rw [← h1, ← map_smul, ← map_sub, hv, map_zero]
  let W : Subrepresentation π := ⟨LinearMap.ker (f - c • LinearMap.id), hinv⟩
  have hs : IsSimpleOrder (Subrepresentation π) := hπ
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  rcases hs.eq_bot_or_eq_top W with hW | hW
  · exfalso
    apply hv.2
    have hvW : v ∈ LinearMap.ker (f - c • LinearMap.id) := by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [hv.apply_eq_smul, sub_self]
    have h2 := congrArg Subrepresentation.toSubmodule hW
    change LinearMap.ker (f - c • LinearMap.id) = _ at h2
    rw [h2] at hvW
    have h3 : v ∈ (⊥ : Submodule ℂ V) := hvW
    simpa using h3
  · apply LinearMap.ext
    intro x
    have h2 := congrArg Subrepresentation.toSubmodule hW
    change LinearMap.ker (f - c • LinearMap.id) = _ at h2
    have hx : x ∈ LinearMap.ker (f - c • LinearMap.id) := by
      rw [h2]
      exact (show x ∈ (⊤ : Submodule ℂ V) from Submodule.mem_top)
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx
    simpa [sub_eq_zero] using hx

end PI.GGConvScalarW
