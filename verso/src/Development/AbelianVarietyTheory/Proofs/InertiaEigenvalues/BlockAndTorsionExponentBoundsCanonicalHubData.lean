import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatLogFloorExpLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentLeTwentyFiveMul
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubX

/- English proof (translation)
Introduce `D L HW R X hX hL c hc`. Establish `ht : 1 ≤ D.R.t` using `D.R.t_odd.pos`. Establish `hn : 1 ≤ D.R.n` using `D.R.ord_pos`. Establish `hnV : 1 ≤ D.R.nV` using `by show 1 ≤ D.R.r + D.R.t`. Use linear arithmetic over natural numbers and integers.

Establish `htR : (1 : ℝ) ≤ D.R.t` using `by exact_mod_cast ht`. Establish `hnR : (1 : ℝ) ≤ D.R.n` using `by exact_mod_cast hn`. Establish `hnVR : (1 : ℝ) ≤ D.R.nV` using `by exact_mod_cast hnV`. Establish `hN : 1 ≤ 4 * D.R.n * D.R.nV`. Use `Nat.mul_le_mul hn hnV` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `hb : L.sc.b = Real.exp L.sc.L` using `rfl`. Establish `hLg : Formalism.MainNotions.TwistedPlaces.large₂ L = L.sc.L` using `rfl`. Establish `hL0 : (0 : ℝ) ≤ L.sc.L` using `by linarith`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `i _ _ _`. Establish `hl : 2 ≤ D.nd.l i` using `(D.nd.lPrime i).out.two_le`. Rewrite using `[hX.cB]`. Establish `h` using `GlobalTheory.HubLoc.cBnum_le_thirty (D.nd.l i) D.R.t (4 * D.R.n * D.R.nV) L.sc.L hl ht hN hL`. Simplify using `only [cBof, hb, hLg]`.

Move the coercions through the operations in `at h`. Establish `hp : (0 : ℝ) ≤ (D.R.t : ℝ) * D.R.n * D.R.nV * L.sc.L` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Introduce `i _ _ _ _ u _`. Establish `hl : 2 ≤ D.nd.l i` using `(D.nd.lPrime i).out.two_le`.

Rewrite using `[hX.c0]`. Establish `h` using `GlobalTheory.HubLoc.torsionExponent_le_twentyFive_mul (D.nd.l i) (4 * D.R.n * D.R.nV) L.sc.L hl hN hL`. Simplify using `only [c0of, hOf, hb, hLg]`. Move the coercions through the operations in `at h ⊢`. Establish `hp : (0 : ℝ) ≤ (D.R.n : ℝ) * D.R.nV * L.sc.L` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem blockAndTorsionExponentBounds_canonicalHubData : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D), GlobalTheory.HubX.Canon L HW R X → 1 ≤ L.sc.L → ∀ c : ℝ, 120 ≤ c → GlobalTheory.HubX.CondCB L X c ∧ KillingConditions.ConstantColumnBound L X c := by
  intro D L HW R X hX hL c hc
  have ht : 1 ≤ D.R.t := D.R.t_odd.pos
  have hn : 1 ≤ D.R.n := D.R.ord_pos
  have hnV : 1 ≤ D.R.nV := by
    show 1 ≤ D.R.r + D.R.t
    omega
  have htR : (1 : ℝ) ≤ D.R.t := by exact_mod_cast ht
  have hnR : (1 : ℝ) ≤ D.R.n := by exact_mod_cast hn
  have hnVR : (1 : ℝ) ≤ D.R.nV := by exact_mod_cast hnV
  have hN : 1 ≤ 4 * D.R.n * D.R.nV := by
    have := Nat.mul_le_mul hn hnV
    nlinarith
  have hb : L.sc.b = Real.exp L.sc.L := rfl
  have hLg : Formalism.MainNotions.TwistedPlaces.large₂ L = L.sc.L := rfl
  have hL0 : (0 : ℝ) ≤ L.sc.L := by linarith
  refine ⟨?_, ?_⟩
  · intro i _ _ _
    have hl : 2 ≤ D.nd.l i := (D.nd.lPrime i).out.two_le
    rw [hX.cB]
    have h := GlobalTheory.HubLoc.cBnum_le_thirty (D.nd.l i) D.R.t (4 * D.R.n * D.R.nV) L.sc.L hl ht hN hL
    simp only [cBof, hb, hLg]
    push_cast at h
    have hp : (0 : ℝ) ≤ (D.R.t : ℝ) * D.R.n * D.R.nV * L.sc.L := by positivity
    nlinarith
  · intro i _ _ _ _ u _
    have hl : 2 ≤ D.nd.l i := (D.nd.lPrime i).out.two_le
    rw [hX.c0]
    have h := GlobalTheory.HubLoc.torsionExponent_le_twentyFive_mul (D.nd.l i) (4 * D.R.n * D.R.nV) L.sc.L hl hN hL
    simp only [c0of, hOf, hb, hLg]
    push_cast at h ⊢
    have hp : (0 : ℝ) ≤ (D.R.n : ℝ) * D.R.nV * L.sc.L := by positivity
    nlinarith

end GlobalTheory.HubX
