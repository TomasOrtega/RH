import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.WS

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mem_Ln_zero_iff (v : F × F) : v ∈ Ln F 0 ↔ v.1 ∈ 𝒪[F] ∧ v.2 ∈ 𝒪[F] := by
  simp only [Ln, Set.mem_setOf_eq, mem_valBall_zero_iff]

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem rowAct_mem_Ln_zero {k : GL (Fin 2) F} (h : ∀ i j, k.val i j ∈ 𝒪[F]) {v : F × F}
    (hv : v ∈ Ln F 0) : rowAct k v ∈ Ln F 0 := by
  rw [mem_Ln_zero_iff] at hv ⊢
  exact ⟨add_mem (mul_mem hv.1 (h 0 0)) (mul_mem hv.2 (h 1 0)),
    add_mem (mul_mem hv.1 (h 0 1)) (mul_mem hv.2 (h 1 1))⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem rowAct_inv_rowAct (k : GL (Fin 2) F) (v : F × F) : rowAct k⁻¹ (rowAct k v) = v := by
  obtain ⟨m, hm⟩ : ∃ m : Matrix (Fin 2) (Fin 2) F, m = (k⁻¹).val := ⟨_, rfl⟩
  have h : k.val * m = 1 := by
    rw [hm, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel]; rfl
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  ext
  · simp only [rowAct, ← hm]
    linear_combination v.1 * e00 + v.2 * e10
  · simp only [rowAct, ← hm]
    linear_combination v.1 * e01 + v.2 * e11

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Apply function extensionality and compare values at an arbitrary argument.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem standard_lattice_indicator_invariant (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (k : GL (Fin 2) F)
    (hk : k ∈ GLnLocal.integralGL F 2) : lat0 F ∘ rowAct k = lat0 F := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
  have key : ∀ v, rowAct k v ∈ Ln F 0 ↔ v ∈ Ln F 0 := fun v =>
    ⟨fun h => by
      have := rowAct_mem_Ln_zero (k := k⁻¹) h2 h
      rwa [rowAct_inv_rowAct] at this, rowAct_mem_Ln_zero h1⟩
  funext v
  by_cases hv : v ∈ Ln F 0
  · simp [lat0, Set.indicator_of_mem hv, Set.indicator_of_mem ((key v).2 hv)]
  · simp [lat0, Set.indicator_of_notMem hv, Set.indicator_of_notMem (fun h => hv ((key v).1 h))]

end GlobalTheory.CompanionTheory.WS
