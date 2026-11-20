import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace PositivityTheory.UnitarySelfGeneration

/- English proof (translation)
Establish `e1 : ∀ k : Fin N, (((if (k:ℕ) + 1 = (m:ℕ) then (1:ℤ) else 0) - if k = m then 1 else 0) * (if n ≤ k then -1 else 0)) = (if k = m then (if n ≤ k then (1:ℤ) else 0) else 0) - (if (k:ℕ) + 1 = m then (if n ≤ k then (1:ℤ) else 0) else 0)`. Introduce `k`. Distinguish the cases in `h1 : (k:ℕ) + 1 = m`. Apply the tactic sequence `have : k ≠ m := by intro h; subst h; omega split_ifs <;> simp_all`. Apply the tactic sequence `split_ifs <;> simp_all`.

Simplify using `only [e1, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Break down `m with ⟨m, hm⟩` into its components or cases. Break down `n with ⟨n, hn⟩` into its components or cases. Consider the cases of `m with`. Consider the case `zero`.

Establish `: ∀ k : Fin N, ¬ ((k:ℕ) + 1 = 0)` using `fun k => by omega`. Simplify using `only [this, if_false, Finset.sum_const_zero, sub_zero, Fin.le_def, Fin.mk.injEq]`. Apply the tactic sequence `split_ifs <;> omega`. Consider the case `succ m`. Rewrite using `[Finset.sum_eq_single ⟨m, by omega⟩]`.

Apply the tactic sequence `simp only [Fin.le_def, Fin.mk.injEq] split_ifs <;> omega`. Introduce `b _ hb`. Establish `hb' : (b:ℕ) ≠ m` using `fun h => hb (Fin.ext h)`. Establish `: ¬ ((b:ℕ) + 1 = ((⟨m + 1, hm⟩ : Fin N) : ℕ))` using `by simp only [Fin.val_mk]; omega`. Rewrite using `[if_neg this]`.

Simplify using the standard rewrite rules.
-/
private theorem sum_shift_mul_neg_indicator_eq_ite (N : ℕ) (m n : Fin N) :
    ∑ k : Fin N, (((if (k:ℕ) + 1 = (m:ℕ) then (1:ℤ) else 0) - if k = m then 1 else 0) * (if n ≤ k then -1 else 0))
      = if n = m then 1 else 0 := by
  have e1 : ∀ k : Fin N, (((if (k:ℕ) + 1 = (m:ℕ) then (1:ℤ) else 0) - if k = m then 1 else 0) * (if n ≤ k then -1 else 0))
      = (if k = m then (if n ≤ k then (1:ℤ) else 0) else 0) - (if (k:ℕ) + 1 = m then (if n ≤ k then (1:ℤ) else 0) else 0) := by
    intro k
    by_cases h1 : (k:ℕ) + 1 = m
    · have : k ≠ m := by intro h; subst h; omega
      split_ifs <;> simp_all
    · split_ifs <;> simp_all
  simp only [e1, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rcases m with ⟨m, hm⟩
  rcases n with ⟨n, hn⟩
  cases m with
  | zero =>
    have : ∀ k : Fin N, ¬ ((k:ℕ) + 1 = 0) := fun k => by omega
    simp only [this, if_false, Finset.sum_const_zero, sub_zero, Fin.le_def, Fin.mk.injEq]
    split_ifs <;> omega
  | succ m =>
    rw [Finset.sum_eq_single ⟨m, by omega⟩]
    · simp only [Fin.le_def, Fin.mk.injEq]
      split_ifs <;> omega
    · intro b _ hb
      have hb' : (b:ℕ) ≠ m := fun h => hb (Fin.ext h)
      have : ¬ ((b:ℕ) + 1 = ((⟨m + 1, hm⟩ : Fin N) : ℕ)) := by simp only [Fin.val_mk]; omega
      rw [if_neg this]
    · simp

/- English proof (translation)
Introduce `Ψ _ _ N r r'`. Use `⟨?_, fun π => ?_⟩` and prove the remaining obligations. Take `⟨p, m⟩` from `r`. Take `⟨q, n⟩` from `r'`. Rewrite using `[Fintype.sum_prod_type]`.

Simplify using `only [rootOnFund, fundOnRoot]`. Rewrite using `[Finset.sum_eq_single p (fun b _ hb => by simp [hb]) (by simp)]`. Distinguish the cases in `hq : q = p`. Substitute `hq` using the available equality. Simplify using `only [if_true, true_and, Prod.mk.injEq]`.

Rewrite using `[sum_shift_mul_neg_indicator_eq_ite N m n]`. Distinguish the cases in `h : n = m`. Simplify using `[h]`. Simplify using `[h, Ne.symm h]`. Establish `: ¬ (p = q)` using `fun h => hq h.symm`.

Simplify using `[hq, this]`. Simplify using `[rootOnFund, fundOnRoot, π.injective.eq_iff]`.
-/
theorem h_fundinv : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (r r' : Ψ × Fin N), (∑ a, rootOnFund r a * fundOnRoot a r' = if r = r' then 1 else 0) ∧ (∀ π : Ψ ≃ Ψ, rootOnFund (π r.1, r.2) (π r'.1, r'.2) = rootOnFund r r' ∧ fundOnRoot (π r.1, r.2) (π r'.1, r'.2) = fundOnRoot r r') := by
  intro Ψ _ _ N r r'
  refine ⟨?_, fun π => ?_⟩
  · obtain ⟨p, m⟩ := r
    obtain ⟨q, n⟩ := r'
    rw [Fintype.sum_prod_type]
    simp only [rootOnFund, fundOnRoot]
    rw [Finset.sum_eq_single p (fun b _ hb => by simp [hb]) (by simp)]
    by_cases hq : q = p
    · subst hq
      simp only [if_true, true_and, Prod.mk.injEq]
      rw [sum_shift_mul_neg_indicator_eq_ite N m n]
      by_cases h : n = m
      · simp [h]
      · simp [h, Ne.symm h]
    · have : ¬ (p = q) := fun h => hq h.symm
      simp [hq, this]
  · simp [rootOnFund, fundOnRoot, π.injective.eq_iff]

end PositivityTheory.UnitarySelfGeneration
