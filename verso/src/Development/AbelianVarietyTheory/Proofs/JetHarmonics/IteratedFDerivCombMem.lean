import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IteratedFDerivProdCoordAt

open scoped BigOperators

namespace GlobalTheory.AlgJetComb

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero`. Introduce `n`. Simplify using `only [pow_zero, iteratedDeriv_const]`. Use `split_ifs with hn`.

Substitute `hn` using the available equality. Simplify using `using one_mem _`. Simplify using `using zero_mem _`. Consider the case `succ a ih`. Introduce `n`.

Establish `e : (fun x => f x ^ (a + 1)) = (fun x => f x ^ a) * f`. Use function extensionality and compare the values at `x`. Simplify using `[pow_succ]`. Establish `h1 : ContDiffAt ℂ n (fun x => f x ^ a) 0` using `(hf.pow a).contDiff.contDiffAt`. Establish `h2 : ContDiffAt ℂ n f 0` using `hf.contDiff.contDiffAt`.

Rewrite using `[e, iteratedDeriv_mul h1 h2, Finset.mul_sum]`. Use `sum_mem fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i ≤ n` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)`. Establish `e2 : δ ^ n * ((n.choose i : ℂ) * iteratedDeriv i (fun x => f x ^ a) 0 * iteratedDeriv (n - i) f 0) = (n.choose i : ℂ) * ((δ ^ i * iteratedDeriv i (fun x => f x ^ a) 0) * (δ ^ (n - i) * iteratedDeriv (n - i) f 0))`. Establish `: δ ^ n = δ ^ i * δ ^ (n - i)` using `by rw [← pow_add, Nat.add_sub_cancel' hi']`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Conclude with `mul_mem (natCast_mem _ _) (mul_mem (ih i) (h _))`.
-/
theorem pow_mem (δ : ℂ) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h : ∀ n, δ ^ n * iteratedDeriv n f 0 ∈ algebraicClosure ℚ ℂ) (a : ℕ) :
    ∀ n, δ ^ n * iteratedDeriv n (fun x => f x ^ a) 0 ∈ algebraicClosure ℚ ℂ := by
  induction a with
  | zero =>
    intro n
    simp only [pow_zero, iteratedDeriv_const]
    split_ifs with hn
    · subst hn; simpa using one_mem _
    · simpa using zero_mem _
  | succ a ih =>
    intro n
    have e : (fun x => f x ^ (a + 1)) = (fun x => f x ^ a) * f := by
      funext x; simp [pow_succ]
    have h1 : ContDiffAt ℂ n (fun x => f x ^ a) 0 := (hf.pow a).contDiff.contDiffAt
    have h2 : ContDiffAt ℂ n f 0 := hf.contDiff.contDiffAt
    rw [e, iteratedDeriv_mul h1 h2, Finset.mul_sum]
    refine sum_mem fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e2 : δ ^ n * ((n.choose i : ℂ) * iteratedDeriv i (fun x => f x ^ a) 0
        * iteratedDeriv (n - i) f 0) = (n.choose i : ℂ) *
        ((δ ^ i * iteratedDeriv i (fun x => f x ^ a) 0)
          * (δ ^ (n - i) * iteratedDeriv (n - i) f 0)) := by
      have : δ ^ n = δ ^ i * δ ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hi']
      rw [this]; ring
    rw [e2]
    exact mul_mem (natCast_mem _ _) (mul_mem (ih i) (h _))

/- English proof (translation)
Introduce `g m k δ a c f ys hf hj hc hy`. Establish `hF : ∀ j, ContDiff ℂ k (fun z : Fin g → ℂ => ∏ i, f j i (z i) ^ a i)` using `fun j => contDiff_prod fun i _ => (((hf j i).contDiff).comp (contDiff_apply ℂ ℂ i)).pow _`. Rewrite using `[iteratedFDeriv_fun_sum_apply (f := fun j (z : Fin g → ℂ) => c j * ∏ i, f j i (z i) ^ a i) (fun j _ => (contDiff_const.mul (hF j)).contDiffAt), ContinuousMultilinearMap.sum_apply]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Establish `e` using `iteratedFDeriv_const_smul_apply' (a := c j) (x := 0) (hF j).contDiffAt`.

Simplify using `only [smul_eq_mul] at e`. Rewrite using `[e, ContinuousMultilinearMap.smul_apply, smul_eq_mul]`. Use `mul_mem (hc j) ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.CoordProdDeriv.iteratedFDeriv_prod_coord g k (fun i x => f j i x ^ a i) _ (fun i => (hf j i).pow _)]`. Use `sum_mem fun σ _ => ?_` and prove the remaining obligations.

Establish `hk : ∑ i, (Finset.univ.filter (fun l => σ l = i)).card = k`. Rewrite using `[← Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := σ) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]`. Simplify using the standard rewrite rules. Establish `e2 : (∏ l, (δ⁻¹ • ys l) (σ l)) * ∏ i, iteratedDeriv (Finset.univ.filter (fun l => σ l = i)).card (fun x => f j i x ^ a i) 0 = (∏ l, ys l (σ l)) * ∏ i, (δ⁻¹ ^ (Finset.univ.filter (fun l => σ l = i)).card * iteratedDeriv (Finset.univ.filter (fun l => σ l = i)).card (fun x => f j i …`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hk]`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Conclude with `mul_mem (prod_mem fun l _ => hy _ _) (prod_mem fun i _ => pow_mem δ⁻¹ (f j i) (hf j i) (hj j i) _ _)`.
-/
theorem iteratedFDeriv_comb_mem :
    ∀ (g m k : ℕ) (δ : ℂ) (a : Fin g → ℕ) (c : Fin m → ℂ) (f : Fin m → Fin g → ℂ → ℂ)
      (ys : Fin k → Fin g → ℂ), (∀ j i, Differentiable ℂ (f j i)) →
      (∀ j i n, δ⁻¹ ^ n * iteratedDeriv n (f j i) 0 ∈ algebraicClosure ℚ ℂ) →
      (∀ j, c j ∈ algebraicClosure ℚ ℂ) → (∀ l i, ys l i ∈ algebraicClosure ℚ ℂ) →
      iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∑ j, c j * ∏ i, f j i (z i) ^ a i) 0
        (fun l => δ⁻¹ • ys l) ∈ algebraicClosure ℚ ℂ := by
  intro g m k δ a c f ys hf hj hc hy
  have hF : ∀ j, ContDiff ℂ k (fun z : Fin g → ℂ => ∏ i, f j i (z i) ^ a i) := fun j =>
    contDiff_prod fun i _ => (((hf j i).contDiff).comp (contDiff_apply ℂ ℂ i)).pow _
  rw [iteratedFDeriv_fun_sum_apply (f := fun j (z : Fin g → ℂ) => c j * ∏ i, f j i (z i) ^ a i)
    (fun j _ => (contDiff_const.mul (hF j)).contDiffAt), ContinuousMultilinearMap.sum_apply]
  refine sum_mem fun j _ => ?_
  have e := iteratedFDeriv_const_smul_apply' (a := c j) (x := 0) (hF j).contDiffAt
  simp only [smul_eq_mul] at e
  rw [e, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  refine mul_mem (hc j) ?_
  rw [GlobalTheory.CoordProdDeriv.iteratedFDeriv_prod_coord g k (fun i x => f j i x ^ a i) _
    (fun i => (hf j i).pow _)]
  refine sum_mem fun σ _ => ?_
  have hk : ∑ i, (Finset.univ.filter (fun l => σ l = i)).card = k := by
    rw [← Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := σ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
    simp
  have e2 : (∏ l, (δ⁻¹ • ys l) (σ l)) *
      ∏ i, iteratedDeriv (Finset.univ.filter (fun l => σ l = i)).card
        (fun x => f j i x ^ a i) 0
      = (∏ l, ys l (σ l)) * ∏ i, (δ⁻¹ ^ (Finset.univ.filter (fun l => σ l = i)).card *
        iteratedDeriv (Finset.univ.filter (fun l => σ l = i)).card
        (fun x => f j i x ^ a i) 0) := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hk]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    ring
  rw [e2]
  exact mul_mem (prod_mem fun l _ => hy _ _)
    (prod_mem fun i _ => pow_mem δ⁻¹ (f j i) (hf j i) (hj j i) _ _)

end GlobalTheory.AlgJetComb
