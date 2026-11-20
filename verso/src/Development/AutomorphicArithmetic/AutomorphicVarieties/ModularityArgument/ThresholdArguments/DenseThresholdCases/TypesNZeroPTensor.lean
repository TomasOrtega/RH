import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Tensor2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroCJDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct
open Module
namespace UpperTheory.TNZ.Grp.Tensor₂
section Contr
variable {ι : Type} [Fintype ι] [hd : DecidableEq ι] {Y : ι → Type} [∀ b, AddCommGroup (Y b)]
  [∀ b, Module ℂ (Y b)]
end Contr
end UpperTheory.TNZ.Grp.Tensor₂
namespace UpperTheory.TNZ.Grp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
/- English proof (translation)
Introduce `hN X _ _ σ hs hirr hη`. Take `⟨y, hy0, hy⟩` from `hη`. Take `⟨s, ⟨E⟩⟩` from `GlobalTheory.LeviFactor.exists_equiv_piTensor_levi hN.loc.bz k (Fin G.s) (fun a => Fin (G.d a)) { V := X, ρ := σ, smooth := hs, irr := hirr }`. Use `⟨fun a => (s a).V, fun a => inferInstance, fun a => inferInstance, fun a => (s a).ρ, fun a => (s a).smooth, fun a => (s a).irr, fun a => ?_, ⟨E⟩⟩` and prove the remaining obligations. Establish `hE : ∀ m, E (σ m y) = piTensor (fun b => (s b).ρ) m (E y)` using `fun m => LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' m) y`.

Establish `hEy : E y ≠ 0` using `(map_ne_zero_iff E (EquivLike.injective E)).2 hy0`. Establish `hK : ∀ g ∈ (KO k (Fin (G.d a)) : Set (GL (Fin (G.d a)) k)), piTensor (fun b => (s b).ρ) (Pi.mulSingle a g) (E y) = ((G.μ a (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • E y`. Introduce `g hg`. Establish `hm : (Pi.mulSingle a g : Levi k fun b : Fin G.s => Fin (G.d b)) ∈ leviK k (m` using `fun b : Fin G.s => Fin (G.d b)) := by`. Rewrite using `[leviK, Subgroup.mem_pi]`.

Introduce `b _`. Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality. Rewrite using `[Pi.mulSingle_eq_same]`. Conclude with `hg`.

Rewrite using `[Pi.mulSingle_eq_of_ne hb]`. Conclude with `one_mem _`. Rewrite using `[← hE, hy _ hm, map_smul]`. Use `congr 1`. Rewrite using `[eta, Finset.prod_eq_single a]`.

Rewrite using `[Pi.mulSingle_eq_same]`. Introduce `b _ hb`. Rewrite using `[Pi.mulSingle_eq_of_ne hb, map_one, map_one, Units.val_one]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ a) h`.

Conclude with `Tensor₂.exists_factor_vec (fun b => (s b).ρ) a (E y) hEy _ _ hK`.
-/
theorem step_tensor_alt {n : ℕ} (G : Grp k n) : G.Step_tensor_alt := by
  intro hN X _ _ σ hs hirr hη
  obtain ⟨y, hy0, hy⟩ := hη
  obtain ⟨s, ⟨E⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi hN.loc.bz k (Fin G.s)
    (fun a => Fin (G.d a)) { V := X, ρ := σ, smooth := hs, irr := hirr }
  refine ⟨fun a => (s a).V, fun a => inferInstance, fun a => inferInstance, fun a => (s a).ρ,
    fun a => (s a).smooth, fun a => (s a).irr, fun a => ?_, ⟨E⟩⟩
  have hE : ∀ m, E (σ m y) = piTensor (fun b => (s b).ρ) m (E y) := fun m =>
    LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' m) y
  have hEy : E y ≠ 0 := (map_ne_zero_iff E (EquivLike.injective E)).2 hy0
  have hK : ∀ g ∈ (KO k (Fin (G.d a)) : Set (GL (Fin (G.d a)) k)),
      piTensor (fun b => (s b).ρ) (Pi.mulSingle a g) (E y) =
        ((G.μ a (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • E y := by
    intro g hg
    have hm : (Pi.mulSingle a g : Levi k fun b : Fin G.s => Fin (G.d b)) ∈
        leviK k (m := fun b : Fin G.s => Fin (G.d b)) := by
      rw [leviK, Subgroup.mem_pi]
      intro b _
      by_cases hb : b = a
      · subst hb
        rw [Pi.mulSingle_eq_same]
        exact hg
      · rw [Pi.mulSingle_eq_of_ne hb]
        exact one_mem _
    rw [← hE, hy _ hm, map_smul]
    congr 1
    rw [eta, Finset.prod_eq_single a]
    · rw [Pi.mulSingle_eq_same]
    · intro b _ hb
      rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one, Units.val_one]
    · intro h
      exact absurd (Finset.mem_univ a) h
  exact Tensor₂.exists_factor_vec (fun b => (s b).ρ) a (E y) hEy _ _ hK
end UpperTheory.TNZ.Grp
end
end
