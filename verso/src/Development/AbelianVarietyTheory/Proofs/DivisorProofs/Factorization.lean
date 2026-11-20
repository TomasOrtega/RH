import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVectorBundlePullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedIntCastLeIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeDegreeNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHermUnitConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqNsmulOfActs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfOrderPullbackAlongHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo.LiftSys

/- English proof (translation)
Introduce `p _ D h₀ hh`. Use `haveI := D.freeLa`. Use `haveI := D.finLa`. Set `Ix` to `Module.Free.ChooseBasisIndex ℤ D.La`. Set `b : Module.Basis Ix ℤ D.La` to `Module.Free.chooseBasis ℤ D.La`.

Set `iA : D.La →+ AfP p ⊗[ℚ] VQ D` to `AddMonoidHom.mk' (inAf D) (fun x y => by simp only [inAf, TensorProduct.tmul_add])`. Establish `hiA : ∀ x, iA x = inAf D x` using `fun _ => rfl`. Establish `key : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ i : Ix, ∃ (x : D.La) (w : AfP p ⊗[ℚ] VQ D), w ∈ LaHat D ∧ h₀ (inAf D (b i)) = inAf D x + n • w` using `fun n hn hnp i => exists_inAf_add_nsmul_of_mem_laHat p D n hn hnp _ (hh _ (AddSubgroup.subset_closure ⟨1, b i, fun v => by rw [map_one]; exact one_mem _, rfl⟩))`. Set `h : ℕ → D.La →+ D.La` to `fun n => if hn : 0 < n ∧ n.Coprime p then (b.constr ℤ (fun i => (key n hn.1 hn.2 i).choose)).toAddMonoidHom else 0`. Use `⟨h, fun n hn hnp x => ?_⟩` and prove the remaining obligations.

Establish `hx : x ∈ Submodule.span ℤ (Set.range b)` using `by rw [b.span_eq]; trivial`. Establish `hh' : h n = (b.constr ℤ (fun i => (key n hn hnp i).choose)).toAddMonoidHom`. Simplify using `only [h, dif_pos (And.intro hn hnp)]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨i, rfl⟩` from `hy`. Take `⟨hw, e⟩` from `(key n hn hnp i).choose_spec.choose_spec`. Establish `hbi : h n (b i) = (key n hn hnp i).choose`. Rewrite using `[hh']`. Simplify using `[Module.Basis.constr_basis]`.

Use `⟨_, hw, e.trans ?_⟩` and prove the remaining obligations. Rewrite using `[hbi]`. Consider the case `zero`. Use `⟨0, zero_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[← hiA, ← hiA, map_zero, map_zero, map_zero, map_zero, smul_zero, add_zero]`.

Consider the case `add y z _ _ hy hz`. Take `⟨w₁, hw₁, e₁⟩` from `hy`. Take `⟨w₂, hw₂, e₂⟩` from `hz`. Use `⟨w₁ + w₂, add_mem hw₁ hw₂, ?_⟩` and prove the remaining obligations. Rewrite using `[← hiA, ← hiA, map_add, map_add, map_add, map_add, hiA, hiA, hiA, hiA, e₁, e₂, smul_add]`.

Normalize the expressions using the abelian group laws. Consider the case `smul c y _ hy`. Take `⟨w, hw, e⟩` from `hy`. Use `⟨c • w, zsmul_mem hw c, ?_⟩` and prove the remaining obligations. Rewrite using `[← hiA, ← hiA, map_zsmul, map_zsmul, map_zsmul, hiA, hiA, e, smul_add, smul_comm c (n : ℕ) w]`.

Rewrite using `[← hiA (c • _), map_zsmul, hiA]`.
-/
theorem exists_lift_sys : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), (∀ v ∈ LaHat D, h₀ v ∈ LaHat D) → ∃ h : ℕ → D.La →+ D.La, ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, h₀ (inAf D x) = inAf D (h n x) + n • w := by
  intro p _ D h₀ hh
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let Ix := Module.Free.ChooseBasisIndex ℤ D.La
  let b : Module.Basis Ix ℤ D.La := Module.Free.chooseBasis ℤ D.La
  let iA : D.La →+ AfP p ⊗[ℚ] VQ D :=
    AddMonoidHom.mk' (inAf D) (fun x y => by simp only [inAf, TensorProduct.tmul_add])
  have hiA : ∀ x, iA x = inAf D x := fun _ => rfl
  have key : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ i : Ix, ∃ (x : D.La) (w : AfP p ⊗[ℚ] VQ D),
      w ∈ LaHat D ∧ h₀ (inAf D (b i)) = inAf D x + n • w := fun n hn hnp i =>
    exists_inAf_add_nsmul_of_mem_laHat p D n hn hnp _ (hh _ (AddSubgroup.subset_closure ⟨1, b i, fun v => by rw [map_one]; exact one_mem _, rfl⟩))
  let h : ℕ → D.La →+ D.La := fun n =>
    if hn : 0 < n ∧ n.Coprime p then
      (b.constr ℤ (fun i => (key n hn.1 hn.2 i).choose)).toAddMonoidHom
    else 0
  refine ⟨h, fun n hn hnp x => ?_⟩
  have hx : x ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; trivial
  have hh' : h n = (b.constr ℤ (fun i => (key n hn hnp i).choose)).toAddMonoidHom := by
    simp only [h, dif_pos (And.intro hn hnp)]
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    obtain ⟨hw, e⟩ := (key n hn hnp i).choose_spec.choose_spec
    have hbi : h n (b i) = (key n hn hnp i).choose := by
      rw [hh']; simp [Module.Basis.constr_basis]
    refine ⟨_, hw, e.trans ?_⟩
    rw [hbi]
  | zero =>
    refine ⟨0, zero_mem _, ?_⟩
    rw [← hiA, ← hiA, map_zero, map_zero, map_zero, map_zero, smul_zero, add_zero]
  | add y z _ _ hy hz =>
    obtain ⟨w₁, hw₁, e₁⟩ := hy
    obtain ⟨w₂, hw₂, e₂⟩ := hz
    refine ⟨w₁ + w₂, add_mem hw₁ hw₂, ?_⟩
    rw [← hiA, ← hiA, map_add, map_add, map_add, map_add, hiA, hiA, hiA, hiA, e₁, e₂, smul_add]
    abel
  | smul c y _ hy =>
    obtain ⟨w, hw, e⟩ := hy
    refine ⟨c • w, zsmul_mem hw c, ?_⟩
    rw [← hiA, ← hiA, map_zsmul, map_zsmul, map_zsmul, hiA, hiA, e, smul_add, smul_comm c (n : ℕ) w]
    rw [← hiA (c • _), map_zsmul, hiA]

end GlobalTheory.LKGeo.LiftSys
