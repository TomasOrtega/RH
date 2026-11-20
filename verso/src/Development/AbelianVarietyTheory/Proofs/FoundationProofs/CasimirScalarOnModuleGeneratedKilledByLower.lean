import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirCentralAndOnHighestWeight

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.CasimirLowest

open GlobalTheory.CasimirHighest

/- English proof (translation)
Simplify using `only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv`. Take `⟨hw, hr⟩` from `hv`. Establish `h1` using `casimir_on_highest_rat (fun i j : Fin p => act (Eab (.inl i) (.inl j))) (fun i j => by simpa using act_Eab_comm h (.inl i) (.inl j) (.inl j) (.inl i)) e (fun i => Λ (.inl i)) (fun i j hij => hr _ _ hij) (fun i => hw _)`. Establish `h2` using `casimir_on_highest_rat (fun i j : Fin q => act (Eab (.inr i) (.inr j))) (fun i j => by simpa using act_Eab_comm h (.inr i) (.inr j) (.inr j) (.inr i)) e (fun i => Λ (.inr i)) (fun i j hij => hr _ _ hij) (fun i => hw _)`. Establish `h3 : ∀ (a : Fin p) (b : Fin q), act (Eab (.inl a) (.inr b)) (act (Eab (.inr b) (.inl a)) e) = 0`.

Introduce `a b`. Rewrite using `[hk a b, map_zero]`. Establish `h4 : ∀ (b : Fin q) (a : Fin p), act (Eab (.inr b) (.inl a)) (act (Eab (.inl a) (.inr b)) e) = ((Λ (.inr b) - Λ (.inl a) : ℚ) : ℂ) • e`. Introduce `b a`. Establish `h5` using `congrArg (fun f : Module.End ℂ V => f e) (act_Eab_comm h (.inr b) (.inl a) (.inl a) (.inr b))`.

Simplify using `only [if_true, LinearMap.sub_apply, Module.End.mul_apply, h3, sub_zero, hw] at h5`. Rewrite using `[h5, Rat.cast_sub, sub_smul]`. Establish `h6 : ∑ b : Fin q, ∑ a : Fin p, ((Λ (.inr b) - Λ (.inl a) : ℚ) : ℂ) • e = ((∑ b : Fin q, ∑ a : Fin p, (Λ (.inr b) - Λ (.inl a)) : ℚ) : ℂ) • e`. Simplify using `only [Rat.cast_sum, Finset.sum_smul]`. Simplify using `only [casimir, LinearMap.sum_apply, LinearMap.add_apply, Module.End.mul_apply, Fintype.sum_sum_type, Finset.sum_add_distrib, h3, h4, Finset.sum_const_zero, zero_add]`.

Rewrite using `[h1, h2, h6, ← add_smul, ← add_smul, ← Rat.cast_add, ← Rat.cast_add]`. Use `congr 2`. Establish `e1 : ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) = ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - 1 - 2 * (i : ℕ)) - q * ∑ i : Fin p, Λ (Sum.inl i)`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.

Establish `e2 : ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ)) = ∑ j : Fin q, Λ (Sum.inr j) * ((q : ℚ) - 1 - 2 * (j : ℕ)) + p * ∑ j : Fin q, Λ (Sum.inr j)`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Establish `e3 : ∑ b : Fin q, ∑ a : Fin p, (Λ (.inr b) - Λ (.inl a)) = p * ∑ j : Fin q, Λ (Sum.inr j) - q * ∑ i : Fin p, Λ (Sum.inl i)`. Simplify using `only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]`.

Rewrite using `[e1, e2, e3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem casimir_on_vector {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) (Λ : Ix p q → ℚ) (e : V)
    (hv : e ∈ hwSub act Λ) (hk : KilledByLower act e) :
    casimir act e = (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) +
      ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • e := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv
  obtain ⟨hw, hr⟩ := hv
  have h1 := casimir_on_highest_rat (fun i j : Fin p => act (Eab (.inl i) (.inl j)))
    (fun i j => by simpa using act_Eab_comm h (.inl i) (.inl j) (.inl j) (.inl i)) e
    (fun i => Λ (.inl i)) (fun i j hij => hr _ _ hij) (fun i => hw _)
  have h2 := casimir_on_highest_rat (fun i j : Fin q => act (Eab (.inr i) (.inr j)))
    (fun i j => by simpa using act_Eab_comm h (.inr i) (.inr j) (.inr j) (.inr i)) e
    (fun i => Λ (.inr i)) (fun i j hij => hr _ _ hij) (fun i => hw _)
  have h3 : ∀ (a : Fin p) (b : Fin q),
      act (Eab (.inl a) (.inr b)) (act (Eab (.inr b) (.inl a)) e) = 0 := by
    intro a b; rw [hk a b, map_zero]
  have h4 : ∀ (b : Fin q) (a : Fin p),
      act (Eab (.inr b) (.inl a)) (act (Eab (.inl a) (.inr b)) e) =
        ((Λ (.inr b) - Λ (.inl a) : ℚ) : ℂ) • e := by
    intro b a
    have h5 := congrArg (fun f : Module.End ℂ V => f e)
      (act_Eab_comm h (.inr b) (.inl a) (.inl a) (.inr b))
    simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply, h3, sub_zero, hw] at h5
    rw [h5, Rat.cast_sub, sub_smul]
  have h6 : ∑ b : Fin q, ∑ a : Fin p, ((Λ (.inr b) - Λ (.inl a) : ℚ) : ℂ) • e =
      ((∑ b : Fin q, ∑ a : Fin p, (Λ (.inr b) - Λ (.inl a)) : ℚ) : ℂ) • e := by
    simp only [Rat.cast_sum, Finset.sum_smul]
  simp only [casimir, LinearMap.sum_apply, LinearMap.add_apply, Module.End.mul_apply,
    Fintype.sum_sum_type, Finset.sum_add_distrib, h3, h4, Finset.sum_const_zero, zero_add]
  rw [h1, h2, h6, ← add_smul, ← add_smul, ← Rat.cast_add, ← Rat.cast_add]
  congr 2
  have e1 : ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) =
      ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - 1 - 2 * (i : ℕ)) - q * ∑ i : Fin p, Λ (Sum.inl i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ)) =
      ∑ j : Fin q, Λ (Sum.inr j) * ((q : ℚ) - 1 - 2 * (j : ℕ)) + p * ∑ j : Fin q, Λ (Sum.inr j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ b : Fin q, ∑ a : Fin p, (Λ (.inr b) - Λ (.inl a)) =
      p * ∑ j : Fin q, Λ (Sum.inr j) - q * ∑ i : Fin p, Λ (Sum.inl i) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.mul_sum]
  rw [e1, e2, e3]
  ring

/- English proof (translation)
Introduce `p q V _ _ act h Λ e hv hk hg x`. Establish `he` using `casimir_on_vector h Λ e hv hk`. Generalize the expression as in `(((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) + ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) = c at he ⊢`. Establish `hc` using `(casimir_central_and_highest p q V act h).1`. Establish `hle : genSub act {e} ≤ LinearMap.ker (casimir act - c • LinearMap.id)`.

Use `sInf_le ⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `y rfl`. Simplify using `[he]`. Introduce `Z y hy`. Simplify using `only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hy ⊢`.

Use `congrArg (fun f : Module.End ℂ V => f y) (hc Z)` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`. Rewrite using `[this, hy, map_smul]`. Establish `hx` using `hle (hg ▸ Submodule.mem_top : x ∈ genSub act {e})`. Simplify `hx` using `[sub_eq_zero]`.
-/
theorem casimir_on_generated : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (Λ : Ix p q → ℚ) (e : V), e ∈ hwSub act Λ → KilledByLower act e → genSub act {e} = ⊤ → ∀ x, casimir act x = (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) + ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • x := by
  intro p q V _ _ act h Λ e hv hk hg x
  have he := casimir_on_vector h Λ e hv hk
  generalize (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) +
      ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) = c at he ⊢
  have hc := (casimir_central_and_highest p q V act h).1
  have hle : genSub act {e} ≤ LinearMap.ker (casimir act - c • LinearMap.id) := by
    refine sInf_le ⟨?_, ?_⟩
    · rintro y rfl
      simp [he]
    · intro Z y hy
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] at hy ⊢
      have := congrArg (fun f : Module.End ℂ V => f y) (hc Z)
      simp only [Module.End.mul_apply] at this
      rw [this, hy, map_smul]
  have hx := hle (hg ▸ Submodule.mem_top : x ∈ genSub act {e})
  simpa [sub_eq_zero] using hx

end GlobalTheory.CasimirLowest
