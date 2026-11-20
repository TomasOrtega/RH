import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

/- English proof (translation)
Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem x hx => exact hS x hx`. Consider the case `zero => exact ⟨fun _ _ _ => rfl, fun _ => W.zero_mem⟩`. Consider the case `add x y _ _ hx hy`. Use `⟨fun u hu g => ?_, fun g => W.add_mem (hx.2 g) (hy.2 g)⟩` and prove the remaining obligations.

Use `show x.1 (g * finGL E N u) + y.1 (g * finGL E N u) = x.1 g + y.1 g`. Rewrite using `[hx.1 u hu g, hy.1 u hu g]`. Consider the case `smul c x _ hx`. Use `⟨fun u hu g => ?_, fun g => W.smul_mem c (hx.2 g)⟩` and prove the remaining obligations. Use `show c • x.1 (g * finGL E N u) = c • x.1 g`.

Rewrite using `[hx.1 u hu g]`.
-/
theorem typeB_of_mem_span {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {K : Subgroup (GL (Fin N) (Af E))} {W : Submodule ℂ (Kinf E N → ℂ)} {S : Set (Sm E N)}
    (hS : ∀ φ ∈ S, TypeB K W φ) {φ : Sm E N} (hφ : φ ∈ Submodule.span ℂ S) : TypeB K W φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨fun _ _ _ => rfl, fun _ => W.zero_mem⟩
  | add x y _ _ hx hy =>
    refine ⟨fun u hu g => ?_, fun g => W.add_mem (hx.2 g) (hy.2 g)⟩
    show x.1 (g * finGL E N u) + y.1 (g * finGL E N u) = x.1 g + y.1 g
    rw [hx.1 u hu g, hy.1 u hu g]
  | smul c x _ hx =>
    refine ⟨fun u hu g => ?_, fun g => W.smul_mem c (hx.2 g)⟩
    show c • x.1 (g * finGL E N u) = c • x.1 g
    rw [hx.1 u hu g]

/- English proof (translation)
Introduce `E _ _ _ N K W S hS hfd`. Establish `hst : IsStable (hull S)` using `fun o φ hφ => Submodule.mem_sInf.2 fun U hU => hU.2 o φ (Submodule.mem_sInf.1 hφ U hU)`. Use `⟨hst, ?_⟩` and prove the remaining obligations. Establish `hsub : S ⊆ hull S` using `fun φ hφ => Submodule.mem_sInf.2 fun U hU => hU.1 hφ`. Take `⟨t, ht⟩` from `(Submodule.fg_iff_finiteDimensional _).2 hfd`.

Establish `htS : ∀ φ ∈ t, φ ∈ Submodule.span ℂ S` using `fun φ hφ => ht ▸ Submodule.subset_span hφ`. Use `⟨t, fun φ hφ => typeB_of_mem_span hS (htS φ hφ), fun φ hφ => ?_, fun U' hU' htU => ?_⟩` and prove the remaining obligations. Conclude with `(Submodule.span_le.2 hsub) (htS φ hφ)`. Use `sInf_le ⟨?_, hU'⟩` and prove the remaining obligations. Establish `h : Submodule.span ℂ S ≤ U'` using `ht ▸ Submodule.span_le.2 htU`.

Conclude with `Submodule.subset_span.trans h`.
-/
theorem hullGen : HullGen := by
  intro E _ _ _ N K W S hS hfd
  have hst : IsStable (hull S) := fun o φ hφ =>
    Submodule.mem_sInf.2 fun U hU => hU.2 o φ (Submodule.mem_sInf.1 hφ U hU)
  refine ⟨hst, ?_⟩
  have hsub : S ⊆ hull S := fun φ hφ => Submodule.mem_sInf.2 fun U hU => hU.1 hφ
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional _).2 hfd
  have htS : ∀ φ ∈ t, φ ∈ Submodule.span ℂ S := fun φ hφ => ht ▸ Submodule.subset_span hφ
  refine ⟨t, fun φ hφ => typeB_of_mem_span hS (htS φ hφ), fun φ hφ => ?_, fun U' hU' htU => ?_⟩
  · exact (Submodule.span_le.2 hsub) (htS φ hφ)
  · refine sInf_le ⟨?_, hU'⟩
    have h : Submodule.span ℂ S ≤ U' := ht ▸ Submodule.span_le.2 htU
    exact Submodule.subset_span.trans h

end GlobalTheory.CompanionTheory.EGlue

end
