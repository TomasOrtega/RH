import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSubgroupOfSiegelAndOppositeNhdsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFixedNearOneSiegelParabolicStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hη _ _ μ _ κ ω hKW`. Introduce `v`. Set `U : Subgroup (UG c (stdJ ν E))` to `{ carrier := {g | ω g v = v} one_mem' := by simp mul_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`.

Rewrite using `[map_mul, Module.End.mul_apply, hb, ha]`. Use the proof step `inv_mem' := by`. Introduce `a ha`. Simplify using `only [Set.mem_setOf_eq] at ha ⊢`. Use `conv_lhs => rw [← ha]`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }`. Establish `key : ∀ u : SB (Matrix α ν E), ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → ω g u = u`. Introduce `u`. Use `filter_upwards [GlobalTheory.T.schwartzBruhat_fixed_near_one_siegelParabolic F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hη (u : Matrix α ν E → ℂ) u.2] with g hg hs`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hKW.par g hs u]`. Conclude with `hg hs`. Establish `hU : IsOpen (U : Set (UG c (stdJ ν E)))`. Use `GlobalTheory.T.isOpen_subgroup_of_siegel_and_opposite_nhds F E c δ hE ν U (key v) ?_` and prove the remaining obligations. Use `filter_upwards [key (ω (weyl c ν) v)] with g hg hs`.

Express the relevant statement in the definitionally equal form `ω ((weyl c ν)⁻¹ * g * weyl c ν) v = v`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg hs, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Conclude with `hU`.
-/
theorem isKW_isSmoothRep : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → GlobalTheory.SplitWeil.IsSmoothRep ω := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hη _ _ μ _ κ ω hKW
  intro v
  let U : Subgroup (UG c (stdJ ν E)) :=
    { carrier := {g | ω g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have key : ∀ u : SB (Matrix α ν E), ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → ω g u = u := by
    intro u
    filter_upwards [GlobalTheory.T.schwartzBruhat_fixed_near_one_siegelParabolic F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hη (u : Matrix α ν E → ℂ) u.2] with g hg hs
    apply Subtype.ext
    rw [hKW.par g hs u]
    exact hg hs
  have hU : IsOpen (U : Set (UG c (stdJ ν E))) := by
    refine GlobalTheory.T.isOpen_subgroup_of_siegel_and_opposite_nhds F E c δ hE ν U (key v) ?_
    filter_upwards [key (ω (weyl c ν) v)] with g hg hs
    change ω ((weyl c ν)⁻¹ * g * weyl c ν) v = v
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg hs, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply]
  exact hU

end GlobalTheory.KSp
