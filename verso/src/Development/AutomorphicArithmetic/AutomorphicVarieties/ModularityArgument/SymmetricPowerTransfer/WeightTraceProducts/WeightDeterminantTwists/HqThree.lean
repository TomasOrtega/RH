import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.HOption

open Polynomial UpperTheory.V.Z.Sym.Wt

/- English proof (translation)
Establish `ev : ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (y : τ → ℂ) (n : ℕ), MvPolynomial.eval y (MvPolynomial.hsymm τ ℂ n) = ∑ s : Sym τ n, ((s : Multiset τ).map y).prod`. Introduce `τ _ _ y n`. Rewrite using `[MvPolynomial.hsymm, map_sum]`. Use `Finset.sum_congr rfl (fun s _ => ?_)` and prove the remaining obligations. Rewrite using `[map_multiset_prod, Multiset.map_map]`.

Use `congr 1`. Conclude with `Multiset.map_congr rfl (fun a _ => MvPolynomial.eval_X _)`. Rewrite using `[ev, ev, ev]`. Rewrite using `[← (symOptionSuccEquiv (α := σ) (n := j)).symm.sum_comp, Fintype.sum_sum_type, Finset.mul_sum]`. Use `congr 1`.

Use `Finset.sum_congr rfl (fun s _ => ?_) show ((none ::ₘ (s : Multiset (Option σ))).map x).prod = _` and prove the remaining obligations. Rewrite using `[Multiset.map_cons, Multiset.prod_cons]`. Use `Finset.sum_congr rfl (fun s _ => ?_) show ((Multiset.map some (s : Multiset σ)).map x).prod = _` and prove the remaining obligations. Rewrite using `[Multiset.map_map]`.
-/
private theorem hs_opt {σ : Type} [Fintype σ] [DecidableEq σ] (x : Option σ → ℂ) (j : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm (Option σ) ℂ (j + 1)) =
      x none * MvPolynomial.eval x (MvPolynomial.hsymm (Option σ) ℂ j) +
        MvPolynomial.eval (x ∘ some) (MvPolynomial.hsymm σ ℂ (j + 1)) := by
  have ev : ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (y : τ → ℂ) (n : ℕ),
      MvPolynomial.eval y (MvPolynomial.hsymm τ ℂ n) = ∑ s : Sym τ n, ((s : Multiset τ).map y).prod := by
    intro τ _ _ y n
    rw [MvPolynomial.hsymm, map_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [map_multiset_prod, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl (fun a _ => MvPolynomial.eval_X _)
  rw [ev, ev, ev]
  rw [← (symOptionSuccEquiv (α := σ) (n := j)).symm.sum_comp, Fintype.sum_sum_type, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun s _ => ?_)
    show ((none ::ₘ (s : Multiset (Option σ))).map x).prod = _
    rw [Multiset.map_cons, Multiset.prod_cons]
  · refine Finset.sum_congr rfl (fun s _ => ?_)
    show ((Multiset.map some (s : Multiset σ)).map x).prod = _
    rw [Multiset.map_map]

/- English proof (translation)
Establish `e1 : ∀ n, MvPolynomial.hsymm (Fin (d + 1)) ℂ n = MvPolynomial.rename (finSuccEquiv' k).symm (MvPolynomial.hsymm (Option (Fin d)) ℂ n)` using `fun n => (MvPolynomial.rename_hsymm (Option (Fin d)) ℂ n (finSuccEquiv' k).symm).symm`. Rewrite using `[e1, e1, MvPolynomial.eval_rename, MvPolynomial.eval_rename, hs_opt]`. Establish `h1 : (x ∘ (finSuccEquiv' k).symm) none = x k` using `by simp`. Establish `h2 : (x ∘ (finSuccEquiv' k).symm) ∘ some = x ∘ k.succAbove`. Use extensionality with `i`.

Simplify using the standard rewrite rules. Rewrite using `[h1, h2]`.
-/
private theorem hs_succ {d : ℕ} (x : Fin (d + 1) → ℂ) (k : Fin (d + 1)) (j : ℕ) :
    MvPolynomial.eval x (MvPolynomial.hsymm (Fin (d + 1)) ℂ (j + 1)) =
      x k * MvPolynomial.eval x (MvPolynomial.hsymm (Fin (d + 1)) ℂ j) +
        MvPolynomial.eval (x ∘ k.succAbove) (MvPolynomial.hsymm (Fin d) ℂ (j + 1)) := by
  have e1 : ∀ n, MvPolynomial.hsymm (Fin (d + 1)) ℂ n =
      MvPolynomial.rename (finSuccEquiv' k).symm (MvPolynomial.hsymm (Option (Fin d)) ℂ n) :=
    fun n => (MvPolynomial.rename_hsymm (Option (Fin d)) ℂ n (finSuccEquiv' k).symm).symm
  rw [e1, e1, MvPolynomial.eval_rename, MvPolynomial.eval_rename, hs_opt]
  have h1 : (x ∘ (finSuccEquiv' k).symm) none = x k := by simp
  have h2 : (x ∘ (finSuccEquiv' k).symm) ∘ some = x ∘ k.succAbove := by
    ext i
    simp
  rw [h1, h2]

/- English proof (translation)
Introduce `j a b`. Establish `hv : (![a, 1, b] ∘ (1 : Fin 3).succAbove) = ![a, b]`. Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> rfl`. Rewrite using `[hs_succ ![a, 1, b] 1 j, hv, UpperTheory.V.Z.Sym.Wt.hqTwo]`.

Simplify using `only [Matrix.cons_val_one, Matrix.cons_val_zero, one_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Z.Sym.Wt.hqThree :
    UpperTheory.V.Z.Sym.Wt.HqThree := by
  intro j a b
  have hv : (![a, 1, b] ∘ (1 : Fin 3).succAbove) = ![a, b] := by
    ext i
    fin_cases i <;> rfl
  rw [hs_succ ![a, 1, b] 1 j, hv, UpperTheory.V.Z.Sym.Wt.hqTwo]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, one_mul]
  ring
