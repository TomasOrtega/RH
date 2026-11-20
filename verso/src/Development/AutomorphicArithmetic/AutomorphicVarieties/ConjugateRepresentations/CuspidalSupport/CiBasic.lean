import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing in
/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Treat this case separately.

Treat this case separately.
-/
private theorem one_mem_centerU (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) :
    UniversalEnvelopingAlgebra.ι ℝ (UpperTheory.V.Cm.lieEq E a (oneL E a)) ∈ (isExpLieAlgebra E a).centerU := by
  refine Subalgebra.mem_center_iff.2 fun u => ?_
  induction u using GroundTheory.Automorphic.AutomorphicForm.UEnv.induction with
  | halg r => exact Algebra.commutes r _
  | hι Y =>
    have h : ⁅Y, UpperTheory.V.Cm.lieEq E a (oneL E a)⁆ = 0 := by
      refine Subtype.ext ?_
      rw [LieSubalgebra.coe_bracket, UpperTheory.V.Cm.lieEq_oneL, Ring.lie_def, mul_one, one_mul, sub_self]
      rfl
    rw [← sub_eq_zero, ← Ring.lie_def, ← LieHom.map_lie, h, map_zero]
  | hmul x y hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  | hadd x y hx hy => rw [add_mul, mul_add, hx, hy]

/- English proof (translation)
Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately.

Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
private theorem scalar_of_mem_Zalg {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (m : (E →+* ℂ) → Multiset ℂ) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ c : ℂ, ∀ φ ∈ CI a m, z φ = c • φ := by
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨t, u, rfl⟩ := hz
    exact ⟨_, fun φ hφ => (mem_CI.1 hφ).2 t u⟩
  | algebraMap r => exact ⟨r, fun φ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨c + d, fun φ hφ => by rw [LinearMap.add_apply, hc φ hφ, hd φ hφ, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨d * c, fun φ hφ => by rw [Module.End.mul_apply, hd φ hφ, map_smul, hc φ hφ, mul_smul]⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Cj.S.ciBasic :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.CiBasic := by
  intro hc E _ _ _ a m
  refine ⟨fun o φ hφ => mem_CI.2 ⟨UpperTheory.V.Cm.isCuspForm_act o (mem_CI.1 hφ).1, fun t u => ?_⟩, ?_⟩
  · have h := LinearMap.congr_fun ((hc E a t u).2.1 o).eq φ
    rw [Module.End.mul_apply, Module.End.mul_apply, (mem_CI.1 hφ).2 t u, map_smul] at h
    exact h
  · rw [← UpperTheory.V.Cm.uTC_ι]
    exact scalar_of_mem_Zalg m (UpperTheory.V.Cm.uTC_mem_Zalg (one_mem_centerU E a))
