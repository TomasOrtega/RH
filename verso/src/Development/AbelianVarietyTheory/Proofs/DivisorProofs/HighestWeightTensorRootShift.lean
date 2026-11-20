import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult

/- English proof (translation)
Take `⟨⟨y1, y2⟩, hy⟩` from `y`. Take `⟨⟨x1, x2⟩, hx⟩` from `x`. Simplify using `only [adP, Eab, Matrix.single_apply, Subtype.mk.injEq, Prod.mk.injEq]`. Apply the tactic sequence `split_ifs <;> aesop`.
-/
lemma adP_Eab_diag {R S : ℕ} (c : Ix R S) (y x : NC R S) :
    adP (Eab c c) y x =
      if y = x then ((if c = y.1.1 then 1 else 0) - (if c = y.1.2 then 1 else 0)) else 0 := by
  obtain ⟨⟨y1, y2⟩, hy⟩ := y
  obtain ⟨⟨x1, x2⟩, hx⟩ := x
  simp only [adP, Eab, Matrix.single_apply, Subtype.mk.injEq, Prod.mk.injEq]
  split_ifs <;> aesop

/- English proof (translation)
Introduce `R S W _ _ _ actW Λ v hL hwts hv hgen ν y hy`. Establish `hirr : ∀ U, KStable actW U → U = ⊥ ∨ U = ⊤`. Introduce `U hU`. Break down `GlobalTheory.BlockReps.gen_irred (W := ⊤) hL (fun Z _ w _ => Submodule.mem_top) (fun w _ => hwts w) Submodule.mem_top hv U hU (hgen ▸ le_top) with h | h` into its components or cases. Conclude with `Or.inl h`.

Conclude with `Or.inr (top_le_iff.1 (hgen ▸ GlobalTheory.BlockReps.gen_le h hU))`. Take `⟨φ, hφ, h1, h2⟩` from `GlobalTheory.TensorHW.exists_dual hL hv hirr`. Take `⟨hy0, hy⟩` from `hy`. Rewrite `hy` using `[GlobalTheory.TensorHW.mem_hw]`. Take `⟨hyw, hyr⟩` from `hy`.

Establish `hupd : ∀ (g : Fin 1 → NC R S) (x : NC R S), Function.update g 0 x = fun _ => x`. Introduce `g x`. Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i 0]`. Simplify using the standard rewrite rules.

Establish `hex : ∃ x : NC R S, φ (y fun _ => x) ≠ 0`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hall : ∀ g, φ (y g) = 0` using `fun g => by`. Establish `: g = fun _ => g 0` using `by funext i; rw [Subsingleton.elim i 0]`.

Rewrite using `[this]`. Conclude with `hne _`. Establish `hbot` using `GlobalTheory.TensorHW.ker_bot hL hirr φ hφ h1 h2 (Submodule.span ℂ (Set.range y)) ?_ ?_`. Apply `hy0` to reduce the goal to its premises. Use function extensionality and compare the values at `g`.

Establish `: y g ∈ Submodule.span ℂ (Set.range y)` using `Submodule.subset_span ⟨g, rfl⟩`. Rewrite `this` using `[hbot]`. Conclude with `this`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`.

Conclude with `hall g`. Introduce `a b hab`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`. Use `congrFun (hyr a b hab) g` as an intermediate fact.

Rewrite `this` using `[tAct_apply]`. Simplify using `only [Pi.zero_apply] at this`. Use `show actW (Eab a b) (y g) ∈ Submodule.span ℂ (Set.range y)`. Rewrite using `[eq_neg_of_add_eq_zero_left this]`. Conclude with `Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))`.

Take `⟨x, hx⟩` from `hex`. Use `⟨x.1.1, x.1.2, x.2, funext fun c => ?_⟩` and prove the remaining obligations. Use `congrArg φ (congrFun (hyw c) (fun _ => x))` as an intermediate fact. Rewrite `this` using `[tAct_apply]`. Simplify using `only [Fin.sum_univ_one, adP_Eab_diag, hupd, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_add, map_smul, h1, Pi.smul_apply, smul_eq_mul] at this`.

Establish `key : ((ν c : ℚ) : ℂ) = ((GlobalTheory.RealLift.addRoot Λ x.1.1 x.1.2 c : ℚ) : ℂ)`. Apply `mul_right_cancel₀ hx` to reduce the goal to its premises. Rewrite using `[← this]`. Simplify using `only [GlobalTheory.RealLift.addRoot]`. Apply the tactic sequence `split_ifs <;> push_cast <;> ring`.

Conclude with `key` after adjusting the coercions.
-/
theorem hw_tensor_one : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (Λ : Ix R S → ℚ) (v : W), IsKLieAct actW →
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ) → IsHW actW Λ v → GlobalTheory.BlockReps.gen actW v = ⊤ →
    ∀ (ν : Ix R S → ℚ) (y : (Fin 1 → NC R S) → W), IsHW (tAct 1 actW) ν y →
      ∃ a b, ¬ sameBlock a b ∧ ν = GlobalTheory.RealLift.addRoot Λ a b := by
  intro R S W _ _ _ actW Λ v hL hwts hv hgen ν y hy
  have hirr : ∀ U, KStable actW U → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    rcases GlobalTheory.BlockReps.gen_irred (W := ⊤) hL (fun Z _ w _ => Submodule.mem_top) (fun w _ => hwts w)
      Submodule.mem_top hv U hU (hgen ▸ le_top) with h | h
    · exact Or.inl h
    · exact Or.inr (top_le_iff.1 (hgen ▸ GlobalTheory.BlockReps.gen_le h hU))
  obtain ⟨φ, hφ, h1, h2⟩ := GlobalTheory.TensorHW.exists_dual hL hv hirr
  obtain ⟨hy0, hy⟩ := hy
  rw [GlobalTheory.TensorHW.mem_hw] at hy
  obtain ⟨hyw, hyr⟩ := hy
  have hupd : ∀ (g : Fin 1 → NC R S) (x : NC R S), Function.update g 0 x = fun _ => x := by
    intro g x; funext i; rw [Subsingleton.elim i 0]; simp
  have hex : ∃ x : NC R S, φ (y fun _ => x) ≠ 0 := by
    by_contra hne
    push_neg at hne
    have hall : ∀ g, φ (y g) = 0 := fun g => by
      have : g = fun _ => g 0 := by funext i; rw [Subsingleton.elim i 0]
      rw [this]; exact hne _
    have hbot := GlobalTheory.TensorHW.ker_bot hL hirr φ hφ h1 h2 (Submodule.span ℂ (Set.range y)) ?_ ?_
    · apply hy0
      funext g
      have : y g ∈ Submodule.span ℂ (Set.range y) := Submodule.subset_span ⟨g, rfl⟩
      rw [hbot] at this
      exact this
    · rw [Submodule.span_le]; rintro _ ⟨g, rfl⟩; exact hall g
    · intro a b hab
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      have := congrFun (hyr a b hab) g
      rw [tAct_apply] at this
      simp only [Pi.zero_apply] at this
      show actW (Eab a b) (y g) ∈ Submodule.span ℂ (Set.range y)
      rw [eq_neg_of_add_eq_zero_left this]
      exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun x _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
  obtain ⟨x, hx⟩ := hex
  refine ⟨x.1.1, x.1.2, x.2, funext fun c => ?_⟩
  have := congrArg φ (congrFun (hyw c) (fun _ => x))
  rw [tAct_apply] at this
  simp only [Fin.sum_univ_one, adP_Eab_diag, hupd, ite_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, map_add, map_smul, h1, Pi.smul_apply, smul_eq_mul] at this
  have key : ((ν c : ℚ) : ℂ) = ((GlobalTheory.RealLift.addRoot Λ x.1.1 x.1.2 c : ℚ) : ℂ) := by
    apply mul_right_cancel₀ hx
    rw [← this]
    simp only [GlobalTheory.RealLift.addRoot]
    split_ifs <;> push_cast <;> ring
  exact_mod_cast key

end GlobalTheory.SteepMult
