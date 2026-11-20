import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WittIdxBound

/- English proof (translation)
Introduce `D V r X Y h`. Take `⟨ev, hev⟩` from `GlobalTheory.BesselCompare.eMat_surj V X`. Take `⟨ev', hev'⟩` from `GlobalTheory.BesselCompare.eMat_surj V Y`. Establish `hiso : ∀ a b, V.hT (ev a) (ev b) = 0` using `fun a b => by`. Rewrite using `[← GlobalTheory.BesselCompare.cT_mul, hev]`.

Conclude with `congrFun (congrFun h.xx a) b`. Establish `hpair : ∀ i j, V.hT (ev i) (ev' j) = if i = j then 1 else 0` using `fun i j => by`. Rewrite using `[← GlobalTheory.BesselCompare.cT_mul, hev, hev', h.xy]`. Simplify using `[Matrix.one_apply]`. Establish `hli : LinearIndependent D.host.E ev`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc j`. Establish `h1` using `congrArg (fun v => V.hT v (ev' j)) hc`. Simplify using `only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hpair, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_zero, LinearMap.zero_apply] at h1`. Simplify using `using h1`.

Establish `hmem : ∀ x ∈ Submodule.span D.host.E (Set.range ev), ∃ c : Fin r → D.host.E, ∑ i, c i • ev i = x` using `fun x hx => (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx`. Unfold `Formalism.MainNotions.SchurIrreducible.wittIdx`. Apply `le_csSup` to reduce the goal to its premises. Use `⟨Module.finrank D.host.E V.V, ?_⟩` and prove the remaining obligations. Introduce and unpack `k ⟨W, rfl, -⟩`.

Conclude with `Submodule.finrank_le W`. Use `⟨Submodule.span D.host.E (Set.range ev), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[finrank_span_eq_card hli, Fintype.card_fin]`. Introduce `x hx y hy`. Take `⟨c, rfl⟩` from `hmem x hx`.

Take `⟨d, rfl⟩` from `hmem y hy`. Simplify using `[map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hiso]`.
-/
theorem witt_frame_le_wittIdx : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E),
    GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → r ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  intro D V r X Y h
  obtain ⟨ev, hev⟩ := GlobalTheory.BesselCompare.eMat_surj V X
  obtain ⟨ev', hev'⟩ := GlobalTheory.BesselCompare.eMat_surj V Y
  have hiso : ∀ a b, V.hT (ev a) (ev b) = 0 := fun a b => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hev]
    exact congrFun (congrFun h.xx a) b
  have hpair : ∀ i j, V.hT (ev i) (ev' j) = if i = j then 1 else 0 := fun i j => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hev, hev', h.xy]
    simp [Matrix.one_apply]
  have hli : LinearIndependent D.host.E ev := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 := congrArg (fun v => V.hT v (ev' j)) hc
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hpair, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_zero, LinearMap.zero_apply] at h1
    simpa using h1
  have hmem : ∀ x ∈ Submodule.span D.host.E (Set.range ev), ∃ c : Fin r → D.host.E, ∑ i, c i • ev i = x :=
    fun x hx => (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx
  unfold Formalism.MainNotions.SchurIrreducible.wittIdx
  apply le_csSup
  · refine ⟨Module.finrank D.host.E V.V, ?_⟩
    rintro k ⟨W, rfl, -⟩
    exact Submodule.finrank_le W
  · refine ⟨Submodule.span D.host.E (Set.range ev), ?_, ?_⟩
    · rw [finrank_span_eq_card hli, Fintype.card_fin]
    · intro x hx y hy
      obtain ⟨c, rfl⟩ := hmem x hx
      obtain ⟨d, rfl⟩ := hmem y hy
      simp [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hiso]

end GlobalTheory.WittIdxBound
