import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqrtNegPrimeKernelCyclicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPKerRepsPowFourMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSqModPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroSquaresSumEquivIcoModFourStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

/- English proof (translation)
Take `⟨hmul, -, hrep⟩` from `GlobalTheory.T.sqrtNegPrime_kernel_cyclic p F L t hp h4 h3 hD`. Establish `ht0 : t ≠ 0`. Introduce and unpack `rfl`. Conclude with `hD.notMem (zero_mem _)`. Establish `hp0 : (p : ℂ) ≠ 0` using `by exact_mod_cast hp.ne_zero`.

Establish `hα2 : sqrtNegNat p ^ 2 = -(p : ℂ)`. Simplify using `only [sqrtNegNat, mul_pow, Complex.I_sq]`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hα0 : sqrtNegNat p ≠ 0`. Introduce `h`. Apply `hp0` to reduce the goal to its premises. Use `hα2` as an intermediate fact. Rewrite `this` using `[h]`.

Simplify using `at this`. Conclude with `this` after adjusting the coercions. Establish `hα12 : sqrtNegNat p ^ 12 = (p : ℂ) ^ 6`. Rewrite using `[show (12 : ℕ) = 2 * 6 from rfl, pow_mul, hα2]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hinj : Set.InjOn (fun k : ℕ => (k : ℂ) * t) (Finset.Ico 1 p : Set ℕ)`. Introduce `a _ b _ hab`. Conclude with `mul_right_cancel₀ ht0 hab` after adjusting the coercions. Use `set S := (Finset.Ico 1 p).image fun k : ℕ => (k : ℂ) * t with hS`. Establish `hcard : S.card = p - 1`.

Rewrite using `[hS, Finset.card_image_of_injOn hinj, Nat.card_Ico]`. Establish `hodd : Odd p` using `hp.odd_of_ne_two (by omega)`. Establish `heven : Even S.card`. Rewrite using `[hcard]; obtain ⟨m, hm⟩ := hodd; exact ⟨m, by omega⟩`. Establish `hpf` using `GlobalTheory.T.prod_derivWeierstrassP_kerReps_pow_four_mul' L (sqrtNegNat p) S hα0 hD.mul hrep heven`.

Rewrite `hpf` using `[hcard, hα12]`. Rewrite using `[← hpf]`. Use `congr 1`. Establish `hprod : ∏ x ∈ S, L.derivWeierstrassP x = ∏ k ∈ Finset.Ico 1 p, L.derivWeierstrassP ((k : ℂ) * t)`. Rewrite using `[hS, Finset.prod_image hinj]`.

Take `⟨e, he⟩` from `GlobalTheory.T.nonzeroSquares_sum_equiv_Ico_mod_four p hp h4`. Establish `hpt : (p : ℂ) * t ∈ L.lattice`. Use `(hmul (p : ℤ)).2 dvd_rfl` as an intermediate fact. Simplify using `using this`. Establish `hsplit : ∏ k ∈ Finset.Ico 1 p, L.derivWeierstrassP ((k : ℂ) * t) = ∏ s : Sq p ⊕ Sq p, L.derivWeierstrassP (((e s : ℕ) : ℂ) * t)`.

Rewrite using `[← Finset.prod_coe_sort]`. Conclude with `(Fintype.prod_equiv e _ _ (fun _ => rfl)).symm`. Establish `hneg : ∀ k : Sq p, L.derivWeierstrassP (((e (Sum.inr k) : ℕ) : ℂ) * t) = -L.derivWeierstrassP (sqPt p t k)`. Introduce `k`. Rewrite using `[(he k).2, Nat.cast_sub (le_of_lt k.1.2), sub_mul, sqPt]`.

Use `L.derivWeierstrassP_add_coe (-((k.1 : ℕ) : ℂ) * t) ⟨_, hpt⟩` as an intermediate fact. Simplify using `only at this`. Rewrite using `[show (p : ℂ) * t - ((k.1 : ℕ) : ℂ) * t = -((k.1 : ℕ) : ℂ) * t + (p : ℂ) * t by ring, this, neg_mul, L.derivWeierstrassP_neg]`. Establish `hpos : ∀ k : Sq p, L.derivWeierstrassP (((e (Sum.inl k) : ℕ) : ℂ) * t) = L.derivWeierstrassP (sqPt p t k)`. Introduce `k`.

Rewrite using `[(he k).1, sqPt]`. Rewrite using `[hprod, hsplit, Fintype.prod_sum_type]`. Simplify using `only [hneg, hpos, Finset.prod_neg]`. Establish `h1 : ((-1 : ℂ) ^ (Finset.univ : Finset (Sq p)).card) ^ 4 = 1`. Rewrite using `[← pow_mul, mul_comm, pow_mul]`.

Evaluate the numerical expressions. Rewrite using `[sqProd, mul_pow, mul_pow, h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sqProd_pow_eight_mul (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ)
    (hp : p.Prime) (h4 : p % 4 = 3) (h3 : 3 < p) (hD : Datum p F L t) :
    sqProd p L t ^ 8 * (p : ℂ) ^ 6 = (latticeCurve L).Δ ^ (p - 1) := by
  obtain ⟨hmul, -, hrep⟩ := GlobalTheory.T.sqrtNegPrime_kernel_cyclic p F L t hp h4 h3 hD
  have ht0 : t ≠ 0 := by
    rintro rfl; exact hD.notMem (zero_mem _)
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hα2 : sqrtNegNat p ^ 2 = -(p : ℂ) := by
    simp only [sqrtNegNat, mul_pow, Complex.I_sq]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
    push_cast; ring
  have hα0 : sqrtNegNat p ≠ 0 := by
    intro h; apply hp0; have := hα2; rw [h] at this; simp at this; exact_mod_cast this
  have hα12 : sqrtNegNat p ^ 12 = (p : ℂ) ^ 6 := by
    rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul, hα2]; ring
  have hinj : Set.InjOn (fun k : ℕ => (k : ℂ) * t) (Finset.Ico 1 p : Set ℕ) := by
    intro a _ b _ hab
    exact_mod_cast mul_right_cancel₀ ht0 hab
  set S := (Finset.Ico 1 p).image fun k : ℕ => (k : ℂ) * t with hS
  have hcard : S.card = p - 1 := by
    rw [hS, Finset.card_image_of_injOn hinj, Nat.card_Ico]
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have heven : Even S.card := by
    rw [hcard]; obtain ⟨m, hm⟩ := hodd; exact ⟨m, by omega⟩
  have hpf := GlobalTheory.T.prod_derivWeierstrassP_kerReps_pow_four_mul' L (sqrtNegNat p) S hα0 hD.mul hrep heven
  rw [hcard, hα12] at hpf
  rw [← hpf]
  congr 1

  have hprod : ∏ x ∈ S, L.derivWeierstrassP x
      = ∏ k ∈ Finset.Ico 1 p, L.derivWeierstrassP ((k : ℂ) * t) := by
    rw [hS, Finset.prod_image hinj]
  obtain ⟨e, he⟩ := GlobalTheory.T.nonzeroSquares_sum_equiv_Ico_mod_four p hp h4
  have hpt : (p : ℂ) * t ∈ L.lattice := by
    have := (hmul (p : ℤ)).2 dvd_rfl
    simpa using this
  have hsplit : ∏ k ∈ Finset.Ico 1 p, L.derivWeierstrassP ((k : ℂ) * t)
      = ∏ s : Sq p ⊕ Sq p, L.derivWeierstrassP (((e s : ℕ) : ℂ) * t) := by
    rw [← Finset.prod_coe_sort]
    exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
  have hneg : ∀ k : Sq p, L.derivWeierstrassP (((e (Sum.inr k) : ℕ) : ℂ) * t)
      = -L.derivWeierstrassP (sqPt p t k) := by
    intro k
    rw [(he k).2, Nat.cast_sub (le_of_lt k.1.2), sub_mul, sqPt]
    have := L.derivWeierstrassP_add_coe (-((k.1 : ℕ) : ℂ) * t) ⟨_, hpt⟩
    simp only at this
    rw [show (p : ℂ) * t - ((k.1 : ℕ) : ℂ) * t = -((k.1 : ℕ) : ℂ) * t + (p : ℂ) * t by ring, this,
      neg_mul, L.derivWeierstrassP_neg]
  have hpos : ∀ k : Sq p, L.derivWeierstrassP (((e (Sum.inl k) : ℕ) : ℂ) * t)
      = L.derivWeierstrassP (sqPt p t k) := by
    intro k; rw [(he k).1, sqPt]
  rw [hprod, hsplit, Fintype.prod_sum_type]
  simp only [hneg, hpos, Finset.prod_neg]
  have h1 : ((-1 : ℂ) ^ (Finset.univ : Finset (Sq p)).card) ^ 4 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [sqProd, mul_pow, mul_pow, h1]
  ring

end GlobalTheory.CMModel
