import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeAlgebraMap

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open Polynomial (nthRootsFinset)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSChoice.BaseChange

/- English proof (translation)
Establish `: Nonempty s` using `hne.to_subtype`. Establish `hsup : (g.support.sup fun m => (v (coeff m g)).toNNReal) = s.sup fun m => (v (coeff m g)).toNNReal`. Use `le_antisymm (Finset.sup_mono hs) (Finset.sup_le fun m hm => ?_)` and prove the remaining obligations. Distinguish the cases in `hm' : m ∈ g.support`. Conclude with `Finset.le_sup (f := fun m => (v (coeff m g)).toNNReal) hm'`.

Rewrite using `[MvPolynomial.notMem_support_iff.1 hm', map_zero, Real.toNNReal_zero]`. Conclude with `bot_le`. Unfold `gaussAbs`. Rewrite using `[hsup]`. Take `⟨k, hk, hkeq⟩` from `Finset.exists_mem_eq_sup s hne fun m => (v (coeff m g)).toNNReal`.

Rewrite using `[hkeq, Real.coe_toNNReal _ (apply_nonneg _ _)]`. Use `le_antisymm (le_ciSup (f := fun k : s => v (coeff (k : ι →₀ ℕ) g)) (Set.finite_range _).bddAbove ⟨k, hk⟩) (ciSup_le fun m => ?_)` and prove the remaining obligations. Establish `h1 : (v (coeff (m : ι →₀ ℕ) g)).toNNReal ≤ (v (coeff k g)).toNNReal`. Rewrite using `[← hkeq]`. Conclude with `Finset.le_sup (f := fun m => (v (coeff m g)).toNNReal) m.2`.

Establish `h2` using `(Real.toNNReal_le_toNNReal_iff (apply_nonneg _ _)).1 h1`. Conclude with `h2`.
-/
theorem gaussAbs_eq_iSup {K ι : Type} [Field K] [NumberField K] (v : FinitePlace K) (g : MvPolynomial ι K)
    (s : Finset (ι →₀ ℕ)) (hs : g.support ⊆ s) (hne : s.Nonempty) :
    gaussAbs v g = ⨆ k : s, v (coeff (k : ι →₀ ℕ) g) := by
  classical
  have : Nonempty s := hne.to_subtype
  have hsup : (g.support.sup fun m => (v (coeff m g)).toNNReal) = s.sup fun m => (v (coeff m g)).toNNReal := by
    refine le_antisymm (Finset.sup_mono hs) (Finset.sup_le fun m hm => ?_)
    by_cases hm' : m ∈ g.support
    · exact Finset.le_sup (f := fun m => (v (coeff m g)).toNNReal) hm'
    · rw [MvPolynomial.notMem_support_iff.1 hm', map_zero, Real.toNNReal_zero]
      exact bot_le
  unfold gaussAbs
  rw [hsup]
  obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup s hne fun m => (v (coeff m g)).toNNReal
  rw [hkeq, Real.coe_toNNReal _ (apply_nonneg _ _)]
  refine le_antisymm (le_ciSup (f := fun k : s => v (coeff (k : ι →₀ ℕ) g)) (Set.finite_range _).bddAbove ⟨k, hk⟩)
    (ciSup_le fun m => ?_)
  have h1 : (v (coeff (m : ι →₀ ℕ) g)).toNNReal ≤ (v (coeff k g)).toNNReal := by
    rw [← hkeq]; exact Finset.le_sup (f := fun m => (v (coeff m g)).toNNReal) m.2
  have h2 := (Real.toNNReal_le_toNNReal_iff (apply_nonneg _ _)).1 h1
  exact h2

end GlobalTheory.HSChoice.BaseChange
