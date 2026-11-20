import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemISupInfWeightSubmoduleOfDiagonalStableStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockIrr

/- English proof (translation)
Establish `h1` using `(Submodule.mem_iInf _).1 h a`. Rewrite `h1` using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]`. Conclude with `sub_eq_zero.1 h1`.
-/
theorem act_diag_of_mem_wtSub {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {v : V} (h : v ∈ wtSub act μ)
    (a : Ix p q) : act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
  have h1 := (Submodule.mem_iInf _).1 h a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1
  exact sub_eq_zero.1 h1

/- English proof (translation)
Introduce `p q M H _ _ E hE hadj S hS μ v U hv hU hline N hNU hN`. Distinguish the cases in `hvN : v ∈ N`. Conclude with `Or.inr (le_antisymm hNU (hU N hvN hN))`. Use `left`. Establish `horth : ∀ x ∈ N, inner ℂ (E x) (E v) = 0`.

Introduce `x hx`. Establish `hx'` using `GlobalTheory.T.mem_iSup_inf_weightSubmodule_of_diagonal_stable p q M.V M.act N (fun a => hN a a (hS.refl a)) x hx (M.wts x)`. Use `clear hx`. Proceed by induction on `hx' using Submodule.iSup_induction' with`. Consider the case `mem ν y hy`.

Take `⟨hyN, hyν⟩` from `hy`. Distinguish the cases in `hν : ν = μ`. Substitute `hν` using the available equality. Take `⟨c, hc⟩` from `hline y (hNU hyN) hyν`. Distinguish the cases in `hc0 : c = 0`.

Simplify using `[hc, hc0]`. It suffices to derive a contradiction. Apply `hvN` to reduce the goal to its premises. Establish `: v = c⁻¹ • y` using `by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Rewrite using `[this]`.

Conclude with `N.smul_mem _ hyN`. Take `⟨a, ha⟩` from `Function.ne_iff.1 hν`. Establish `h1` using `hadj (Eab a a) y v`. Rewrite `h1` using `[GlobalTheory.FockTensor.adjZ_Eab, GlobalTheory.FockTensor.sgnIx_mul_self, one_smul, act_diag_of_mem_wtSub hyν, act_diag_of_mem_wtSub hv, map_smul, map_smul, inner_smul_left, inner_smul_right, map_ratCast]`. Establish `hne : ((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ) ≠ 0`.

Rewrite using `[sub_ne_zero]`. Conclude with `ha` after adjusting the coercions. Establish `h2 : (((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) * inner ℂ (E y) (E v) = 0`. Rewrite using `[sub_mul, h1, sub_self]`. Conclude with `(mul_eq_zero.1 h2).resolve_left hne`.

Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [map_add, inner_add_left, hy, hz, add_zero]`. Set `U' : Submodule ℂ M.V` to `{ carrier := {y | ∀ x ∈ N, inner ℂ (E x) (E y) = 0} add_mem' := fun {y z} hy hz x hx => by`. Rewrite using `[map_add, inner_add_right, hy x hx, hz x hx, add_zero]`. Use the proof step `zero_mem' := fun x _ => by simp`.

Use the proof step `smul_mem' := fun c y hy x hx => by`. Rewrite using `[map_smul, inner_smul_right, hy x hx, mul_zero] }`. Establish `hUU' : U ≤ U'`. Use `hU U' horth ?_` and prove the remaining obligations. Introduce `a b hab y hy x hx`.

Establish `h1` using `hadj (adjZ (Eab a b)) x y`. Rewrite `h1` using `[GlobalTheory.FockTensor.adjZ_adjZ]`. Rewrite using `[← h1]`. Apply `hy` to reduce the goal to its premises. Rewrite using `[GlobalTheory.FockTensor.adjZ_Eab, map_smul, LinearMap.smul_apply]`.

Conclude with `N.smul_mem _ (hN b a (hS.symm hab) x hx)`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Establish `h0 : inner ℂ (E x) (E x) = 0` using `hUU' (hNU hx) x hx`. Rewrite `h0` using `[inner_self_eq_zero]`.

Conclude with `(Submodule.mem_bot ℂ).2 (hE (by rw [h0, map_zero]))`.
-/
theorem irreducible_of_weight_line : ∀ (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H), Function.Injective E → (∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) → ∀ (S : Ix p q → Ix p q → Prop), Equivalence S → ∀ (μ : Ix p q → ℚ) (v : M.V) (U : Submodule ℂ M.V), v ∈ wtSub M.act μ → (∀ U' : Submodule ℂ M.V, v ∈ U' → (∀ a b, S a b → ∀ x ∈ U', M.act (Eab a b) x ∈ U') → U ≤ U') → (∀ x ∈ U, x ∈ wtSub M.act μ → ∃ c : ℂ, x = c • v) → ∀ N : Submodule ℂ M.V, N ≤ U → (∀ a b, S a b → ∀ x ∈ N, M.act (Eab a b) x ∈ N) → N = ⊥ ∨ N = U := by
  intro p q M H _ _ E hE hadj S hS μ v U hv hU hline N hNU hN
  by_cases hvN : v ∈ N
  · exact Or.inr (le_antisymm hNU (hU N hvN hN))
  left
  have horth : ∀ x ∈ N, inner ℂ (E x) (E v) = 0 := by
    intro x hx
    have hx' := GlobalTheory.T.mem_iSup_inf_weightSubmodule_of_diagonal_stable p q M.V M.act N (fun a => hN a a (hS.refl a)) x hx (M.wts x)
    clear hx
    induction hx' using Submodule.iSup_induction' with
    | mem ν y hy =>
      obtain ⟨hyN, hyν⟩ := hy
      by_cases hν : ν = μ
      · subst hν
        obtain ⟨c, hc⟩ := hline y (hNU hyN) hyν
        by_cases hc0 : c = 0
        · simp [hc, hc0]
        · exfalso
          apply hvN
          have : v = c⁻¹ • y := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
          rw [this]
          exact N.smul_mem _ hyN
      · obtain ⟨a, ha⟩ := Function.ne_iff.1 hν
        have h1 := hadj (Eab a a) y v
        rw [GlobalTheory.FockTensor.adjZ_Eab, GlobalTheory.FockTensor.sgnIx_mul_self, one_smul,
          act_diag_of_mem_wtSub hyν, act_diag_of_mem_wtSub hv, map_smul, map_smul,
          inner_smul_left, inner_smul_right, map_ratCast] at h1
        have hne : ((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ) ≠ 0 := by
          rw [sub_ne_zero]; exact_mod_cast ha
        have h2 : (((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) * inner ℂ (E y) (E v) = 0 := by
          rw [sub_mul, h1, sub_self]
        exact (mul_eq_zero.1 h2).resolve_left hne
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, inner_add_left, hy, hz, add_zero]
  let U' : Submodule ℂ M.V :=
    { carrier := {y | ∀ x ∈ N, inner ℂ (E x) (E y) = 0}
      add_mem' := fun {y z} hy hz x hx => by
        rw [map_add, inner_add_right, hy x hx, hz x hx, add_zero]
      zero_mem' := fun x _ => by simp
      smul_mem' := fun c y hy x hx => by
        rw [map_smul, inner_smul_right, hy x hx, mul_zero] }
  have hUU' : U ≤ U' := by
    refine hU U' horth ?_
    intro a b hab y hy x hx
    have h1 := hadj (adjZ (Eab a b)) x y
    rw [GlobalTheory.FockTensor.adjZ_adjZ] at h1
    rw [← h1]
    apply hy
    rw [GlobalTheory.FockTensor.adjZ_Eab, map_smul, LinearMap.smul_apply]
    exact N.smul_mem _ (hN b a (hS.symm hab) x hx)
  rw [eq_bot_iff]
  intro x hx
  have h0 : inner ℂ (E x) (E x) = 0 := hUU' (hNU hx) x hx
  rw [inner_self_eq_zero] at h0
  exact (Submodule.mem_bot ℂ).2 (hE (by rw [h0, map_zero]))

end GlobalTheory.FockIrr
