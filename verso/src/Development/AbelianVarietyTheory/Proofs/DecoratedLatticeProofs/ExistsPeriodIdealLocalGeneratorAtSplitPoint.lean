import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSelfDualLatticeSplitPlaceDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentMulIdemSumEqZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSplitPlaceHermitianFrameGLEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open NumberField

noncomputable section

namespace GlobalTheory.FinPl.LocGen

/- English proof (translation)
Introduce `h`. Establish `h1` using `D.host.𝔟_spec.1`. Rewrite `h1` using `[h, Ideal.bot_mul]`. Conclude with `differentIdeal_ne_bot h1`.
-/
theorem half_diff_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h1 := D.host.𝔟_spec.1
  rw [h, Ideal.bot_mul] at h1
  exact differentIdeal_ne_bot h1

/- English proof (translation)
Establish `hb0 : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 (half_diff_ne_bot D)`. Establish `hc0 : ((D.host.ccE : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0`. Use `FractionalIdeal.coeIdeal_ne_zero.2 ?_` and prove the remaining obligations. Rewrite using `[Host.ccE, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]`. Conclude with `D.host.ccK_ne_bot`.

Conclude with `mul_ne_zero hc0 (inv_ne_zero hb0)`.
-/
theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  have hb0 : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (half_diff_ne_bot D)
  have hc0 : ((D.host.ccE : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
    refine FractionalIdeal.coeIdeal_ne_zero.2 ?_
    rw [Host.ccE, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact D.host.ccK_ne_bot
  exact mul_ne_zero hc0 (inv_ne_zero hb0)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `h1 : IsIntegral ℤ (q.pr (incA D (x : D.host.E)))` using `(x.2).map ((q.pr.comp (incA D)).toIntAlgHom)`. Establish `h2 : IsIntegral 𝒪[k] (q.pr (incA D (x : D.host.E)))` using `h1.tower_top`. Conclude with `(Valuation.integer.integers (valuation k)).mem_of_integral h2`.
-/
theorem pr_incA_int (q : SplitPt D k) (x : 𝓞 D.host.E) : q.pr (incA D (x : D.host.E)) ∈ 𝒪[k] := by
  have h1 : IsIntegral ℤ (q.pr (incA D (x : D.host.E))) := (x.2).map ((q.pr.comp (incA D)).toIntAlgHom)
  have h2 : IsIntegral 𝒪[k] (q.pr (incA D (x : D.host.E))) := h1.tower_top
  exact (Valuation.integer.integers (valuation k)).mem_of_integral h2

/- English proof (translation)
Introduce `D k _ _ _ _ q`. Use `set π : D.host.E →+* k := q.pr.comp (incA D) with hπ`. Establish `hinj : Function.Injective π` using `π.injective`. Establish `hfg : ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E)).FG` using `FractionalIdeal.fg_unit (Units.mk0 D.host.AA (AA_ne_zero D))`. Take `⟨s, hs⟩` from `hfg`.

Establish `hsne : s.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty]`. Introduce and unpack `rfl`. Apply `AA_ne_zero D` to reduce the goal to its premises. Rewrite using `[← FractionalIdeal.coeToSubmodule_eq_bot, ← hs]`.

Simplify using the standard rewrite rules. Take `⟨j, hj, hmax⟩` from `s.exists_max_image (fun x => valuation k (π x)) hsne`. Establish `hjmem : j ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)` using `hs ▸ Submodule.subset_span hj`. Establish `hj0 : π j ≠ 0`. Introduce `h0`.

Apply `AA_ne_zero D` to reduce the goal to its premises. Rewrite using `[← FractionalIdeal.coeToSubmodule_eq_bot, ← hs, Submodule.span_eq_bot]`. Introduce `i hi`. Establish `h1` using `hmax i hi`. Rewrite `h1` using `[h0, map_zero, le_zero_iff, Valuation.zero_iff]`.

Conclude with `hinj (h1.trans π.map_zero.symm)`. Use `⟨j, hjmem, hj0, ?_⟩` and prove the remaining obligations. Introduce `a ha`. Establish `ha' : a ∈ Submodule.span (𝓞 D.host.E) (s : Set D.host.E)` using `hs.symm ▸ ha`. Express the relevant statement in the definitionally equal form `π a / π j ∈ 𝒪[k]`.

Use `clear ha`. Proceed by induction on `ha' using Submodule.span_induction with`. Consider the case `mem x hx`. Rewrite using `[Valuation.mem_integer_iff, map_div₀]`. Conclude with `div_le_one_of_le₀ (hmax x hx) zero_le'`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, add_div]`. Conclude with `add_mem hx hy`. Consider the case `smul r x _ hx`. Rewrite using `[Algebra.smul_def, map_mul, mul_div_assoc]`.

Conclude with `mul_mem (pr_incA_int q r) hx`.
-/
theorem exists_gen : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k), ∃ a₀ ∈ (D.host.AA : Set D.host.E), q.pr (incA D a₀) ≠ 0 ∧
      ∀ a ∈ (D.host.AA : Set D.host.E), q.pr (incA D a) / q.pr (incA D a₀) ∈ 𝒪[k] := by
  intro D k _ _ _ _ q
  classical
  set π : D.host.E →+* k := q.pr.comp (incA D) with hπ
  have hinj : Function.Injective π := π.injective
  have hfg : ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E)).FG :=
    FractionalIdeal.fg_unit (Units.mk0 D.host.AA (AA_ne_zero D))
  obtain ⟨s, hs⟩ := hfg
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply AA_ne_zero D
    rw [← FractionalIdeal.coeToSubmodule_eq_bot, ← hs]; simp
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun x => valuation k (π x)) hsne
  have hjmem : j ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) := hs ▸ Submodule.subset_span hj
  have hj0 : π j ≠ 0 := by
    intro h0
    apply AA_ne_zero D
    rw [← FractionalIdeal.coeToSubmodule_eq_bot, ← hs, Submodule.span_eq_bot]
    intro i hi
    have h1 := hmax i hi
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at h1
    exact hinj (h1.trans π.map_zero.symm)
  refine ⟨j, hjmem, hj0, ?_⟩
  intro a ha
  have ha' : a ∈ Submodule.span (𝓞 D.host.E) (s : Set D.host.E) := hs.symm ▸ ha
  change π a / π j ∈ 𝒪[k]
  clear ha
  induction ha' using Submodule.span_induction with
  | mem x hx =>
    rw [Valuation.mem_integer_iff, map_div₀]
    exact div_le_one_of_le₀ (hmax x hx) zero_le'
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, add_div]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [Algebra.smul_def, map_mul, mul_div_assoc]
    exact mul_mem (pr_incA_int q r) hx

end GlobalTheory.FinPl.LocGen
