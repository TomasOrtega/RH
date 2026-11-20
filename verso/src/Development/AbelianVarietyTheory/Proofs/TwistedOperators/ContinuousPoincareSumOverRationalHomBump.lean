import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittExtensionSumMulMiddleCoordinate

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

namespace GlobalTheory.BumpMix

/- English proof (translation)
Take `⟨hg, -, -, ht2, hdisc, -⟩` from `lattice_Mx D m n`. Use `haveI : IsTopologicalAddGroup (Mx D m n) := hg`. Use `haveI : T2Space (Mx D m n) := ht2`. Use `haveI : DiscreteTopology (ratMx D m n) := hdisc`. Establish `hcl : IsClosed (ratMx D m n : Set (Mx D m n))` using `AddSubgroup.isClosed_of_discrete`.

Establish `hS : IsCompact ((Subtype.val : ratMx D m n → Mx D m n) ⁻¹' K)` using `hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK`. Establish `hfin` using `(hS.finite_of_discrete.image Subtype.val).preimage (rat_injective (D := D) (m := m) (n := n)).injOn`. Use `hfin.subset fun γ hγ => ?_` and prove the remaining obligations. Conclude with `⟨⟨rat γ, rat_mem γ⟩, hγ, rfl⟩`.
-/
theorem finite_rat_mem_of_isCompact {D : D7} {m n : ℕ} (K : Set (Mx D m n)) (hK : IsCompact K) :
    {γ : Matrix (Fin m) (Fin n) D.host.E | rat γ ∈ K}.Finite := by
  obtain ⟨hg, -, -, ht2, hdisc, -⟩ := lattice_Mx D m n
  haveI : IsTopologicalAddGroup (Mx D m n) := hg
  haveI : T2Space (Mx D m n) := ht2
  haveI : DiscreteTopology (ratMx D m n) := hdisc
  have hcl : IsClosed (ratMx D m n : Set (Mx D m n)) := AddSubgroup.isClosed_of_discrete
  have hS : IsCompact ((Subtype.val : ratMx D m n → Mx D m n) ⁻¹' K) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hfin := (hS.finite_of_discrete.image Subtype.val).preimage (rat_injective (D := D) (m := m) (n := n)).injOn
  refine hfin.subset fun γ hγ => ?_
  exact ⟨⟨rat γ, rat_mem γ⟩, hγ, rfl⟩

/- English proof (translation)
Introduce `D ψ hψ S S₀ T ρ d β hβ`. Take `⟨hg, hlc, -, -, -, -⟩` from `lattice_Mx D T.rank S.rank`. Use `haveI : IsTopologicalAddGroup (WO S T) := hg`. Use `haveI : LocallyCompactSpace (WO S T) := hlc`. Take `⟨hg', -, -, -, -, -⟩` from `lattice_Mx D T.rank ρ`.

Use `haveI : IsTopologicalAddGroup (Mx D T.rank ρ) := hg'`. Use `haveI : ContinuousSub (Mx D T.rank ρ) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hg'`. Establish `hjX : Continuous fun u : WO S T => u ⬝ d.jX` using `Continuous.matrix_mul (A := fun u : WO S T => u) continuous_id continuous_const`. Establish `hjY : Continuous fun u : WO S T => u ⬝ d.jY` using `Continuous.matrix_mul (A := fun u : WO S T => u) continuous_id continuous_const`. Establish `hterm : ∀ γ : Matrix (Fin T.rank) (Fin ρ) D.host.E, Continuous fun u : WO S T => ψ (trHalf D (pairS T (u ⬝ d.jX + 2 • rat γ) (u ⬝ d.jY))) * β (u ⬝ d.jX + rat γ)`.

Introduce `γ`. Establish `e : (fun u : WO S T => trHalf D (pairS T (u ⬝ d.jX + 2 • rat γ) (u ⬝ d.jY))) = fun u : WO S T => symplOH S T (d.extX T (u ⬝ d.jX + 2 • rat γ)) (d.extY T (u ⬝ d.jY))`. Use function extensionality and compare the values at `fun u => (d.symplOH_extX_extY T _ _).symm`. Establish `hc : Continuous fun u : WO S T => trHalf D (pairS T (u ⬝ d.jX + 2 • rat γ) (u ⬝ d.jY))`. Rewrite using `[e]`.

Use `GlobalTheory.OrientedHeis.continuous_symplOH ?_ ?_` and prove the remaining obligations. Simplify using `only [HypDec.extX_apply]`. Conclude with `(hjX.add continuous_const).matrix_mul continuous_const`. Simplify using `only [HypDec.extY_apply]`. Conclude with `hjY.matrix_mul continuous_const`.

Conclude with `(hψ.1.1.comp hc).mul (hβ.cont.comp (hjX.add continuous_const))`. Use `continuous_iff_continuousAt.2 fun u₀ => ?_` and prove the remaining obligations. Take `⟨U, hU, hUn⟩` from `exists_compact_mem_nhds u₀`. Establish `hK : IsCompact ((fun p : Mx D T.rank ρ × WO S T => p.1 - p.2 ⬝ d.jX) '' (tsupport β ×ˢ U))` using `(hβ.supp.isCompact.prod hU).image (continuous_fst.sub (Continuous.matrix_mul (A := fun p : Mx D T.rank ρ × WO S T => p.2) continuous_snd continuous_const))`. Establish `hF` using `finite_rat_mem_of_isCompact _ hK`.

Establish `vanish : ∀ u ∈ U, ∀ γ, γ ∉ hF.toFinset → β (u ⬝ d.jX + rat γ) = 0`. Introduce `u hu γ hγ`. Assume the negation of the conclusion as `hne`. Conclude with `hγ (hF.mem_toFinset.2 ⟨(u ⬝ d.jX + rat γ, u), ⟨subset_tsupport β hne, hu⟩, add_sub_cancel_left _ _⟩)`. Use `(continuous_finset_sum hF.toFinset fun γ _ => hterm γ).continuousAt.congr (Filter.eventually_of_mem hUn fun u hu => ?_)` and prove the remaining obligations.

Use `show _ = poinX ψ d T β u`. Unfold `poinX`. Use `(tsum_eq_sum fun γ hγ => ?_).symm` and prove the remaining obligations. Rewrite using `[vanish u hu γ hγ, mul_zero]`.
-/
theorem poinX_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (β : Mx D T.rank ρ → ℂ), IsBump β → Continuous (poinX ψ d T β) := by
  intro D ψ hψ S S₀ T ρ d β hβ
  obtain ⟨hg, hlc, -, -, -, -⟩ := lattice_Mx D T.rank S.rank
  haveI : IsTopologicalAddGroup (WO S T) := hg
  haveI : LocallyCompactSpace (WO S T) := hlc
  obtain ⟨hg', -, -, -, -, -⟩ := lattice_Mx D T.rank ρ
  haveI : IsTopologicalAddGroup (Mx D T.rank ρ) := hg'
  haveI : ContinuousSub (Mx D T.rank ρ) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hg'
  have hjX : Continuous fun u : WO S T => u ⬝ d.jX := Continuous.matrix_mul (A := fun u : WO S T => u) continuous_id continuous_const
  have hjY : Continuous fun u : WO S T => u ⬝ d.jY := Continuous.matrix_mul (A := fun u : WO S T => u) continuous_id continuous_const
  have hterm : ∀ γ : Matrix (Fin T.rank) (Fin ρ) D.host.E, Continuous fun u : WO S T =>
      ψ (trHalf D (pairS T (u ⬝ d.jX + 2 • rat γ) (u ⬝ d.jY))) * β (u ⬝ d.jX + rat γ) := by
    intro γ
    have e : (fun u : WO S T => trHalf D (pairS T (u ⬝ d.jX + 2 • rat γ) (u ⬝ d.jY))) =
        fun u : WO S T => symplOH S T (d.extX T (u ⬝ d.jX + 2 • rat γ)) (d.extY T (u ⬝ d.jY)) :=
      funext fun u => (d.symplOH_extX_extY T _ _).symm
    have hc : Continuous fun u : WO S T => trHalf D (pairS T (u ⬝ d.jX + 2 • rat γ) (u ⬝ d.jY)) := by
      rw [e]
      refine GlobalTheory.OrientedHeis.continuous_symplOH ?_ ?_
      · simp only [HypDec.extX_apply]
        exact (hjX.add continuous_const).matrix_mul continuous_const
      · simp only [HypDec.extY_apply]
        exact hjY.matrix_mul continuous_const
    exact (hψ.1.1.comp hc).mul (hβ.cont.comp (hjX.add continuous_const))
  refine continuous_iff_continuousAt.2 fun u₀ => ?_
  obtain ⟨U, hU, hUn⟩ := exists_compact_mem_nhds u₀
  have hK : IsCompact ((fun p : Mx D T.rank ρ × WO S T => p.1 - p.2 ⬝ d.jX) '' (tsupport β ×ˢ U)) :=
    (hβ.supp.isCompact.prod hU).image (continuous_fst.sub (Continuous.matrix_mul (A := fun p : Mx D T.rank ρ × WO S T => p.2) continuous_snd continuous_const))
  have hF := finite_rat_mem_of_isCompact _ hK
  have vanish : ∀ u ∈ U, ∀ γ, γ ∉ hF.toFinset → β (u ⬝ d.jX + rat γ) = 0 := by
    intro u hu γ hγ
    by_contra hne
    exact hγ (hF.mem_toFinset.2 ⟨(u ⬝ d.jX + rat γ, u), ⟨subset_tsupport β hne, hu⟩, add_sub_cancel_left _ _⟩)
  refine (continuous_finset_sum hF.toFinset fun γ _ => hterm γ).continuousAt.congr
    (Filter.eventually_of_mem hUn fun u hu => ?_)
  show _ = poinX ψ d T β u
  unfold poinX
  refine (tsum_eq_sum fun γ hγ => ?_).symm
  rw [vanish u hu γ hγ, mul_zero]

end GlobalTheory.BumpMix

end
