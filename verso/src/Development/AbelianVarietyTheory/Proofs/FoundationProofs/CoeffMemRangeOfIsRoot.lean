import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfFiniteComplexAutomorphismOrbitStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.PsRoot

/- English proof (translation)
Establish `hi : IsIntegral E x` using `hx.isIntegral`. Establish `h1 : (minpoly E x).natDegree = 1`. Use `IsAlgClosed.degree_eq_one_of_irreducible E (minpoly.irreducible hi)` as an intermediate fact. Conclude with `Polynomial.natDegree_eq_of_degree_eq_some this`. Take `⟨y, hy⟩` from `(minpoly.natDegree_eq_one_iff).1 h1`.

Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem mem_of_isAlgebraic_of_isAlgClosed (E : Subfield ℂ) [IsAlgClosed E] {x : ℂ}
    (hx : IsAlgebraic E x) : x ∈ E := by
  have hi : IsIntegral E x := hx.isIntegral
  have h1 : (minpoly E x).natDegree = 1 := by
    have := IsAlgClosed.degree_eq_one_of_irreducible E (minpoly.irreducible hi)
    exact Polynomial.natDegree_eq_of_degree_eq_some this
  obtain ⟨y, hy⟩ := (minpoly.natDegree_eq_one_iff).1 h1
  rw [← hy]
  exact y.2

/- English proof (translation)
Introduce `Ω _ _ ε b Q hQ hcoef hb k`. Set `E : Subfield ℂ` to `ε.fieldRange`. Use `haveI : IsAlgClosed E := IsAlgClosed.of_ringEquiv Ω E ε.rangeRestrictFieldEquiv`. Establish `hE : ∀ z : ℂ, z ∈ ε.range → z ∈ E` using `fun z hz => by`. Take `⟨y, rfl⟩` from `hz`.

Conclude with `⟨y, rfl⟩`. Establish `hroot : ∀ g : ℂ ≃ₐ[E] ℂ, Q.IsRoot (PowerSeries.map (g : ℂ →+* ℂ) b)`. Introduce `g`. Establish `hfix : Q.map (PowerSeries.map (g : ℂ →+* ℂ)) = Q`. Use extensionality with `i j`.

Rewrite using `[Polynomial.coeff_map, PowerSeries.coeff_map]`. Take `⟨y, hy⟩` from `hE _ (hcoef i j)`. Rewrite using `[← hy]`. Conclude with `g.commutes ⟨_, ⟨y, rfl⟩⟩`. Establish `h2` using `Polynomial.eval_map_apply (PowerSeries.map (g : ℂ →+* ℂ)) (p := Q) b`.

Use `show Q.eval _ = 0`. Rewrite `h2` using `[hfix, hb, map_zero]`. Conclude with `h2`. Establish `hfin : (Set.range fun g : ℂ ≃ₐ[E] ℂ => g (PowerSeries.coeff k b)).Finite`. Use `((Polynomial.finite_setOf_isRoot hQ).image (PowerSeries.coeff k)).subset ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨g, rfl⟩`. Use `⟨PowerSeries.map (g : ℂ →+* ℂ) b, hroot g, ?_⟩` and prove the remaining obligations. Simplify using `[PowerSeries.coeff_map]`. Take `⟨y, hy⟩` from `mem_of_isAlgebraic_of_isAlgClosed E (GlobalTheory.T.isAlgebraic_of_finite_complex_automorphism_orbit E _ hfin)`. Conclude with `⟨y, hy⟩`.
-/
theorem coeff_mem_range_of_isRoot : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ)
    (b : PowerSeries ℂ) (Q : Polynomial (PowerSeries ℂ)), Q ≠ 0 →
    (∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ ε.range) → Q.eval b = 0 →
    ∀ k, PowerSeries.coeff k b ∈ ε.range := by
  intro Ω _ _ ε b Q hQ hcoef hb k
  let E : Subfield ℂ := ε.fieldRange
  haveI : IsAlgClosed E := IsAlgClosed.of_ringEquiv Ω E ε.rangeRestrictFieldEquiv
  have hE : ∀ z : ℂ, z ∈ ε.range → z ∈ E := fun z hz => by
    obtain ⟨y, rfl⟩ := hz
    exact ⟨y, rfl⟩

  have hroot : ∀ g : ℂ ≃ₐ[E] ℂ, Q.IsRoot (PowerSeries.map (g : ℂ →+* ℂ) b) := by
    intro g
    have hfix : Q.map (PowerSeries.map (g : ℂ →+* ℂ)) = Q := by
      ext i j
      rw [Polynomial.coeff_map, PowerSeries.coeff_map]
      obtain ⟨y, hy⟩ := hE _ (hcoef i j)
      rw [← hy]
      exact g.commutes ⟨_, ⟨y, rfl⟩⟩
    have h2 := Polynomial.eval_map_apply (PowerSeries.map (g : ℂ →+* ℂ)) (p := Q) b
    show Q.eval _ = 0
    rw [hfix, hb, map_zero] at h2
    exact h2
  have hfin : (Set.range fun g : ℂ ≃ₐ[E] ℂ => g (PowerSeries.coeff k b)).Finite := by
    refine ((Polynomial.finite_setOf_isRoot hQ).image (PowerSeries.coeff k)).subset ?_
    rintro _ ⟨g, rfl⟩
    refine ⟨PowerSeries.map (g : ℂ →+* ℂ) b, hroot g, ?_⟩
    simp [PowerSeries.coeff_map]
  obtain ⟨y, hy⟩ := mem_of_isAlgebraic_of_isAlgClosed E (GlobalTheory.T.isAlgebraic_of_finite_complex_automorphism_orbit E _ hfin)
  exact ⟨y, hy⟩

end GlobalTheory.PsRoot
