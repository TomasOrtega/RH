import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDifferentialsConnectedPDivGroupCoordinaStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

noncomputable section

namespace GlobalTheory.Katz

/- English proof (translation)
Set `L : MvPowerSeries (Fin d ⊕ Fin d) k →ₗ[k] (∀ n, G.A n ⊗[k] G.A n)` to `LinearMap.pi fun n => (c.ev₂ n).toLinearMap`. Set `S : Submodule k (MvPowerSeries (Fin d ⊕ Fin d) k)` to `G.cocycles.comap L`. Set `T₀ : S →ₗ[k] G.cocycles` to `L.restrict (fun x hx => hx)`. Take `⟨T, hT⟩` from `LinearMap.exists_extend T₀`. Establish `hU` using `(GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates p k d G c).1`.

Set `U : (Fin d → k) →ₗ[k] G.omega` to `{ toFun := fun w => ⟨fun n => ∑ i, w i • dUnit k (c.x n i), hU w⟩ map_add' := fun a b => Subtype.ext (funext fun n => by`. Simplify using `[add_smul, Finset.sum_add_distrib])`. Use the proof step `map_smul' := fun r a => Subtype.ext (funext fun n => by`. Simplify using `[Finset.smul_sum, smul_smul]) }`. Use `⟨G.rigMk ∘ₗ T.prodMap U, fun s w z u hz hu => ?_⟩` and prove the remaining obligations.

Establish `hs : s ∈ S`. Express the relevant statement in the definitionally equal form `L s ∈ G.cocycles`. Establish `: L s = z.1` using `funext fun n => (hz n).symm`. Rewrite using `[this]`. Conclude with `z.2`.

Establish `h1 : T s = z`. Use `LinearMap.congr_fun hT ⟨s, hs⟩` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply] at this`. Rewrite using `[this]`. Conclude with `Subtype.ext (funext fun n => (hz n).symm)`.

Establish `h2 : U w = u` using `Subtype.ext (funext fun n => (hu n).symm)`. Simplify using `[h1, h2]`.
-/
theorem exists_rigMap (p : ℕ) (k : Type) [Field k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d) :
    ∃ ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] G.RigExt,
      (∀ s w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n s) →
        (∀ n, u.1 n = ∑ i, w i • dUnit k (c.x n i)) → ρ (s, w) = G.rigMk (z, u)) := by
  classical
  let L : MvPowerSeries (Fin d ⊕ Fin d) k →ₗ[k] (∀ n, G.A n ⊗[k] G.A n) :=
    LinearMap.pi fun n => (c.ev₂ n).toLinearMap
  let S : Submodule k (MvPowerSeries (Fin d ⊕ Fin d) k) := G.cocycles.comap L
  let T₀ : S →ₗ[k] G.cocycles := L.restrict (fun x hx => hx)
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T₀
  have hU := (GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates p k d G c).1
  let U : (Fin d → k) →ₗ[k] G.omega :=
    { toFun := fun w => ⟨fun n => ∑ i, w i • dUnit k (c.x n i), hU w⟩
      map_add' := fun a b => Subtype.ext (funext fun n => by
        simp [add_smul, Finset.sum_add_distrib])
      map_smul' := fun r a => Subtype.ext (funext fun n => by
        simp [Finset.smul_sum, smul_smul]) }
  refine ⟨G.rigMk ∘ₗ T.prodMap U, fun s w z u hz hu => ?_⟩
  have hs : s ∈ S := by
    change L s ∈ G.cocycles
    have : L s = z.1 := funext fun n => (hz n).symm
    rw [this]; exact z.2
  have h1 : T s = z := by
    have := LinearMap.congr_fun hT ⟨s, hs⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this]
    exact Subtype.ext (funext fun n => (hz n).symm)
  have h2 : U w = u := Subtype.ext (funext fun n => (hu n).symm)
  simp [h1, h2]

end GlobalTheory.Katz
