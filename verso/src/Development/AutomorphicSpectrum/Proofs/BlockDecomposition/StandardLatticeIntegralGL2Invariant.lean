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
Simplify using `only [Ln, Set.mem_setOf_eq, mem_valBall_zero_iff]`.
-/
theorem mem_Ln_zero_iff (v : F × F) : v ∈ Ln F 0 ↔ v.1 ∈ 𝒪[F] ∧ v.2 ∈ 𝒪[F] := by
  simp only [Ln, Set.mem_setOf_eq, mem_valBall_zero_iff]

/- English proof (translation)
Rewrite `hv`, the goal using `[mem_Ln_zero_iff]`. Conclude with `⟨add_mem (mul_mem hv.1 (h 0 0)) (mul_mem hv.2 (h 1 0)), add_mem (mul_mem hv.1 (h 0 1)) (mul_mem hv.2 (h 1 1))⟩`.
-/
theorem rowAct_mem_Ln_zero {k : GL (Fin 2) F} (h : ∀ i j, k.val i j ∈ 𝒪[F]) {v : F × F}
    (hv : v ∈ Ln F 0) : rowAct k v ∈ Ln F 0 := by
  rw [mem_Ln_zero_iff] at hv ⊢
  exact ⟨add_mem (mul_mem hv.1 (h 0 0)) (mul_mem hv.2 (h 1 0)),
    add_mem (mul_mem hv.1 (h 0 1)) (mul_mem hv.2 (h 1 1))⟩

/- English proof (translation)
Take `⟨m, hm⟩ : ∃ m : Matrix (Fin 2) (Fin 2) F, m = (k⁻¹).val` from `⟨_, rfl⟩`. Establish `h : k.val * m = 1`. Rewrite using `[hm, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel]`. Both sides reduce to the same expression. Establish `e00` using `congrFun (congrFun h 0) 0`.

Establish `e01` using `congrFun (congrFun h 0) 1`. Establish `e10` using `congrFun (congrFun h 1) 0`. Establish `e11` using `congrFun (congrFun h 1) 1`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11`. Use `ext`.

Simplify using `only [rowAct, ← hm]`. Take the linear combination `v.1 * e00 + v.2 * e10`. Simplify using `only [rowAct, ← hm]`. Take the linear combination `v.1 * e01 + v.2 * e11`.
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
Take `⟨h1, h2⟩` from `(GLnLocal.mem_integralGL_iff F 2).1 hk`. Establish `key : ∀ v, rowAct k v ∈ Ln F 0 ↔ v ∈ Ln F 0` using `fun v => ⟨fun h => by`. Use `rowAct_mem_Ln_zero (k := k⁻¹) h2 h` as an intermediate fact. Rewrite using `[rowAct_inv_rowAct] at this, rowAct_mem_Ln_zero h1⟩` and apply the resulting hypothesis. Use function extensionality and compare the values at `v`.

Distinguish the cases in `hv : v ∈ Ln F 0`. Simplify using `[lat0, Set.indicator_of_mem hv, Set.indicator_of_mem ((key v).2 hv)]`. Simplify using `[lat0, Set.indicator_of_notMem hv, Set.indicator_of_notMem (fun h => hv ((key v).1 h))]`.
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
