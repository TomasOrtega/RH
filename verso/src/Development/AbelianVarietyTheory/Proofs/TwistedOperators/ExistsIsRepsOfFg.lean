import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

/- English proof (translation)
Establish `h1 : Finite (𝒪[k] ⧸ Ideal.span {ϖ})`. Rewrite using `[← hϖ.maximalIdeal_eq]`. Conclude with `(inferInstance : Finite 𝓀[k])`. Establish `hfin : Module.Finite 𝒪[k] M` using `Module.Finite.iff_fg.mpr hM`. Use `set N : Submodule 𝒪[k] M := Ideal.span {ϖ} • ⊤ with hN`.

Establish `h2 : Finite (M ⧸ N)`. Establish `: Finite (M ⧸ (⊤ : Submodule 𝒪[k] M))`. Establish `: Subsingleton (M ⧸ (⊤ : Submodule 𝒪[k] M))` using `Submodule.Quotient.subsingleton_iff.mpr rfl`. Use `infer_instance`. Conclude with `Submodule.finite_quotient_smul _ Module.Finite.fg_top`.

Establish `hmem : ∀ x : M, x ∈ N ↔ (x : ι → k) ∈ ϖ • M`. Introduce `x`. Rewrite using `[hN, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_smul_pointwise_iff_exists]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, -, rfl⟩`.

Conclude with `⟨b, b.2, rfl⟩`. Introduce and unpack `⟨b, hb, h⟩`. Conclude with `⟨⟨b, hb⟩, trivial, Subtype.ext h⟩`. Use `Fintype.ofFinite (M ⧸ N)` as an intermediate fact. Use `choose s hs using Submodule.Quotient.mk_surjective N`.

Use `⟨Finset.univ.image fun q => (s q : ι → k), ?_, ?_⟩` and prove the remaining obligations. Introduce `t ht`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.mp ht`. Conclude with `(s q).2`. Introduce `v hv`.

Establish `key : ∀ q, v - (s q : ι → k) ∈ ϖ • M ↔ Submodule.Quotient.mk (⟨v, hv⟩ : M) = q`. Introduce `q`. Use `conv_rhs => rw [← hs q, Submodule.Quotient.eq, hmem]`. Both sides reduce to the same expression. Use `⟨s (Submodule.Quotient.mk ⟨v, hv⟩), ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, (key _).mpr rfl⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `t ⟨ht, h⟩`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.mp ht`. Rewrite using `[(key q).mp h]`.
-/
theorem exists_isReps_of_fg (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι] (ϖ : 𝒪[k])
    (hϖ : Irreducible ϖ) (M : Submodule 𝒪[k] (ι → k)) (hM : M.FG) :
    ∃ T : Finset (ι → k), IsReps ϖ M T := by
  classical
  have h1 : Finite (𝒪[k] ⧸ Ideal.span {ϖ}) := by
    rw [← hϖ.maximalIdeal_eq]
    exact (inferInstance : Finite 𝓀[k])
  have hfin : Module.Finite 𝒪[k] M := Module.Finite.iff_fg.mpr hM
  set N : Submodule 𝒪[k] M := Ideal.span {ϖ} • ⊤ with hN
  have h2 : Finite (M ⧸ N) := by
    have : Finite (M ⧸ (⊤ : Submodule 𝒪[k] M)) := by
      have : Subsingleton (M ⧸ (⊤ : Submodule 𝒪[k] M)) :=
        Submodule.Quotient.subsingleton_iff.mpr rfl
      infer_instance
    exact Submodule.finite_quotient_smul _ Module.Finite.fg_top
  have hmem : ∀ x : M, x ∈ N ↔ (x : ι → k) ∈ ϖ • M := by
    intro x
    rw [hN, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists,
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨b, -, rfl⟩
      exact ⟨b, b.2, rfl⟩
    · rintro ⟨b, hb, h⟩
      exact ⟨⟨b, hb⟩, trivial, Subtype.ext h⟩
  have := Fintype.ofFinite (M ⧸ N)
  choose s hs using Submodule.Quotient.mk_surjective N
  refine ⟨Finset.univ.image fun q => (s q : ι → k), ?_, ?_⟩
  · intro t ht
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    exact (s q).2
  · intro v hv
    have key : ∀ q, v - (s q : ι → k) ∈ ϖ • M ↔ Submodule.Quotient.mk (⟨v, hv⟩ : M) = q := by
      intro q
      conv_rhs => rw [← hs q, Submodule.Quotient.eq, hmem]
      rfl
    refine ⟨s (Submodule.Quotient.mk ⟨v, hv⟩), ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩,
      (key _).mpr rfl⟩, ?_⟩
    rintro t ⟨ht, h⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    rw [(key q).mp h]

end GlobalTheory.RootEx.UnfoldShape
