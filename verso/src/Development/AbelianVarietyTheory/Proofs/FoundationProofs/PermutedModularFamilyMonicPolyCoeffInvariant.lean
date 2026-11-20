import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermutedModularFamilySumEsymmSlashInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosed

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
open Polynomial

namespace GlobalTheory.QFam

/- English proof (translation)
Use `set n := Fintype.card ι with hn`. Use `set P : ℂ[X] := ∏ l, (X + C (-y l)) with hP`. Establish `hmon : P.Monic` using `monic_prod_of_monic _ _ fun l _ => monic_X_add_C _`. Establish `hdeg : P.natDegree = n`. Rewrite using `[hP, natDegree_prod_of_monic _ _ fun l _ => monic_X_add_C _]`.

Simplify using `only [natDegree_X_add_C, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hn]`. Establish `hroot : P.eval (y i) = 0`. Rewrite using `[hP, eval_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp)`. Establish `hcoeff : ∀ j ≤ n, P.coeff j = (-1) ^ (n - j) * ∑ t ∈ Finset.powersetCard (n - j) Finset.univ, ∏ l ∈ t, y l`.

Introduce `j hj`. Rewrite using `[hP, Finset.prod_X_add_C_coeff _ _ (by simpa [hn] using hj), Finset.card_univ, ← hn, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun t ht => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_neg, (Finset.mem_powersetCard.mp ht).2]`. Establish `h1 : P.coeff n = 1` using `hdeg ▸ hmon.coeff_natDegree`.

Rewrite `hroot` using `[eval_eq_sum_range, hdeg, Finset.sum_range_succ, h1, one_mul]`. Rewrite using `[← hroot, add_comm]`. Use `congr 1`. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun m => P.coeff m * y i ^ m)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[hcoeff j j.2.le]`.
-/
theorem vieta_root {ι : Type} [Fintype ι] (y : ι → ℂ) (i : ι) :
    y i ^ Fintype.card ι + ∑ j : Fin (Fintype.card ι),
      ((-1) ^ (Fintype.card ι - (j : ℕ)) *
        ∑ t ∈ Finset.powersetCard (Fintype.card ι - (j : ℕ)) Finset.univ, ∏ l ∈ t, y l) *
        y i ^ (j : ℕ) = 0 := by
  classical
  set n := Fintype.card ι with hn
  set P : ℂ[X] := ∏ l, (X + C (-y l)) with hP
  have hmon : P.Monic := monic_prod_of_monic _ _ fun l _ => monic_X_add_C _
  have hdeg : P.natDegree = n := by
    rw [hP, natDegree_prod_of_monic _ _ fun l _ => monic_X_add_C _]
    simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hn]
  have hroot : P.eval (y i) = 0 := by
    rw [hP, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hcoeff : ∀ j ≤ n, P.coeff j =
      (-1) ^ (n - j) * ∑ t ∈ Finset.powersetCard (n - j) Finset.univ, ∏ l ∈ t, y l := by
    intro j hj
    rw [hP, Finset.prod_X_add_C_coeff _ _ (by simpa [hn] using hj), Finset.card_univ, ← hn,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.prod_neg, (Finset.mem_powersetCard.mp ht).2]
  have h1 : P.coeff n = 1 := hdeg ▸ hmon.coeff_natDegree
  rw [eval_eq_sum_range, hdeg, Finset.sum_range_succ, h1, one_mul] at hroot
  rw [← hroot, add_comm]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun m => P.coeff m * y i ^ m)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hcoeff j j.2.le]

end GlobalTheory.QFam

/- English proof (translation)
Introduce `ι _ act k N F R _ hb hF hQ`. Use `⟨fun j τ => (-1) ^ (Fintype.card ι - (j : ℕ)) * ∑ t ∈ Finset.powersetCard (Fintype.card ι - (j : ℕ)) Finset.univ, ∏ l ∈ t, F l τ, fun j => ⟨fun γ => ?_, ?_⟩, fun i τ => vieta_root (fun l => F l τ) i⟩` and prove the remaining obligations. Establish `hE` using `IsFam.esymm_slash hb hF γ (Fintype.card ι - (j : ℕ))`. Establish `hw : (((k * (Fintype.card ι - (j : ℕ)) : ℕ) : ℤ)) = (((Fintype.card ι - (j : ℕ) : ℕ) : ℤ) * (k : ℤ))`. Rewrite using `[Nat.cast_mul, mul_comm]`.

Use function extensionality and compare the values at `τ`. Establish `hEτ` using `congrFun hE τ`. Rewrite `hEτ` using `[ModularForm.SL_slash_apply]`. Rewrite using `[hw, ModularForm.SL_slash_apply, mul_assoc, hEτ]`. Conclude with `QAllSubring.mul (QAllSubring.const (R.pow_mem (R.neg_mem R.one_mem) _)) (QAllSubring.sum _ fun t _ => QAllSubring.prod _ fun l _ => hQ l)`.
-/
theorem GlobalTheory.QFam.minpoly_coeff_invariant : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (k N : ℕ) (F : ι → ℍ → ℂ) (R : Subring ℂ), 0 < N → ActBij act → IsFam act k F → (∀ i, QAll (· ∈ R) N (F i)) → ∃ s : Fin (Fintype.card ι) → ℍ → ℂ, (∀ j : Fin (Fintype.card ι), (∀ γ : SL(2, ℤ), s j ∣[((k * (Fintype.card ι - j) : ℕ) : ℤ)] γ = s j) ∧ QAll (· ∈ R) N (s j)) ∧ ∀ i τ, F i τ ^ Fintype.card ι + ∑ j, s j τ * F i τ ^ (j : ℕ) = 0 := by
  intro ι _ act k N F R _ hb hF hQ
  refine ⟨fun j τ => (-1) ^ (Fintype.card ι - (j : ℕ)) *
      ∑ t ∈ Finset.powersetCard (Fintype.card ι - (j : ℕ)) Finset.univ, ∏ l ∈ t, F l τ,
    fun j => ⟨fun γ => ?_, ?_⟩, fun i τ => vieta_root (fun l => F l τ) i⟩
  · have hE := IsFam.esymm_slash hb hF γ (Fintype.card ι - (j : ℕ))
    have hw : (((k * (Fintype.card ι - (j : ℕ)) : ℕ) : ℤ)) =
        (((Fintype.card ι - (j : ℕ) : ℕ) : ℤ) * (k : ℤ)) := by
      rw [Nat.cast_mul, mul_comm]
    funext τ
    have hEτ := congrFun hE τ
    rw [ModularForm.SL_slash_apply] at hEτ
    rw [hw, ModularForm.SL_slash_apply, mul_assoc, hEτ]
  · exact QAllSubring.mul (QAllSubring.const (R.pow_mem (R.neg_mem R.one_mem) _))
      (QAllSubring.sum _ fun t _ => QAllSubring.prod _ fun l _ => hQ l)
