import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DvdOfMemIk
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

namespace GlobalTheory.Ord2.SelPerp

/- English proof (translation)
Use `haveI : Module.IsTorsionFree ℤ_[l] c.O := by`. Use `Module.IsTorsionFree.of_smul_eq_zero fun a x h => ?_` and prove the remaining obligations. Establish `h' : a • (x : Qbar l) = 0` using `by rw [← Subalgebra.coe_smul, h]; rfl`. Rewrite `h'` using `[Algebra.smul_def, mul_eq_zero]`. Break down `h' with h' | h'` into its components or cases.

Use `left`. Use `congrArg norm h'` as an intermediate fact. Rewrite `this` using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap', norm_zero]`. Establish `h2 : ((a : ℤ_[l]) : ℚ_[l]) = 0` using `norm_eq_zero.1 this`. Conclude with `PadicInt.coe_eq_zero.1 h2`.

Use `right`. Conclude with `Subtype.ext h'`. Use `infer_instance`.
-/
theorem coef_free_pairSurj (l : ℕ) [Fact l.Prime] (c : Coef l) : Module.Free ℤ_[l] c.O := by
  haveI : Module.IsTorsionFree ℤ_[l] c.O := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun a x h => ?_
    have h' : a • (x : Qbar l) = 0 := by rw [← Subalgebra.coe_smul, h]; rfl
    rw [Algebra.smul_def, mul_eq_zero] at h'
    rcases h' with h' | h'
    · left
      have := congrArg norm h'
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap', norm_zero] at this
      have h2 : ((a : ℤ_[l]) : ℚ_[l]) = 0 := norm_eq_zero.1 this
      exact PadicInt.coe_eq_zero.1 h2
    · right
      exact Subtype.ext h'
  infer_instance

/- English proof (translation)
Use `haveI := coef_free_pairSurj l c`. Set `e` to `Module.Free.chooseBasis ℤ_[l] c.O`. Set `f : c.O →ₗ[ℤ_[l]] ℤ_[l]` to `e.constr ℤ_[l] fun i => (((φ (red c n (e i))).val : ℕ) : ℤ_[l])`. Establish `hf : ∀ x : c.O, PadicInt.toZModPow n (f x) = φ (red c n x)`. Introduce `x`.

Establish `hx : x ∈ Submodule.span ℤ_[l] (Set.range e)` using `by rw [e.span_eq]; trivial`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Simplify using `only [f, Module.Basis.constr_basis]`.

Rewrite using `[map_natCast, ZMod.natCast_zmod_val]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]`. Consider the case `smul a x _ hx`. Rewrite using `[map_smul, smul_eq_mul, map_mul, hx, red_smul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]`.

Take `⟨b, hb, -⟩` from `tau_spec c f`. Use `⟨red c n b, fun a => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `red_surjective c n a`. Rewrite using `[← hf, hb, ← map_mul, tbA_red, mul_comm]`.
-/
theorem exists_eq_tbA_mul (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (φ : Qn c n →+ ZMod (l ^ n)) :
    ∃ b : Qn c n, ∀ a : Qn c n, φ a = GlobalTheory.Ord2.SelPerp.tbA c n (a * b) := by
  classical
  haveI := coef_free_pairSurj l c
  let e := Module.Free.chooseBasis ℤ_[l] c.O
  let f : c.O →ₗ[ℤ_[l]] ℤ_[l] := e.constr ℤ_[l] fun i => (((φ (red c n (e i))).val : ℕ) : ℤ_[l])
  have hf : ∀ x : c.O, PadicInt.toZModPow n (f x) = φ (red c n x) := by
    intro x
    have hx : x ∈ Submodule.span ℤ_[l] (Set.range e) := by rw [e.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      simp only [f, Module.Basis.constr_basis]
      rw [map_natCast, ZMod.natCast_zmod_val]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
    | smul a x _ hx =>
      rw [map_smul, smul_eq_mul, map_mul, hx, red_smul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  obtain ⟨b, hb, -⟩ := tau_spec c f
  refine ⟨red c n b, fun a => ?_⟩
  obtain ⟨x, rfl⟩ := red_surjective c n a
  rw [← hf, hb, ← map_mul, tbA_red, mul_comm]

end GlobalTheory.Ord2.SelPerp
