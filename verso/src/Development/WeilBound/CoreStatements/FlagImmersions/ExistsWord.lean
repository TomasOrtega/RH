import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LowerBoundOfBaseSetting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace RootFieldNumerics.HH

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `m hm`. Use `⟨Fin.elim0, ?_⟩` and prove the remaining obligations.

Rewrite using `[(Finsupp.degree_eq_zero_iff m).1 hm]`. Simplify using the standard rewrite rules. Consider the case `succ d ih`. Introduce `m hm`. Establish `hne : m ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at hm`. Take `⟨j, hj⟩` from `Finsupp.ne_iff.mp hne`. Establish `hle : Finsupp.single j 1 ≤ m`. Rewrite using `[Finsupp.single_le_iff]`.

Simplify using `only [Finsupp.coe_zero, Pi.zero_apply] at hj`. Use linear arithmetic over natural numbers and integers. Establish `hsplit : m = Finsupp.single j 1 + (m - Finsupp.single j 1)` using `(add_tsub_cancel_of_le hle).symm`. Establish `hdeg : Finsupp.degree (m - Finsupp.single j 1) = d`. Establish `h2` using `congrArg Finsupp.degree hsplit`.

Rewrite `h2` using `[map_add, Finsupp.degree_single, hm]`. Use linear arithmetic over natural numbers and integers. Take `⟨w', hw'⟩` from `ih _ hdeg`. Use `⟨Fin.cons j w', ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_succ]`.

Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[← hw']`. Conclude with `hsplit`.
-/
theorem exists_word {J : Type} : ∀ (d : ℕ) (m : J →₀ ℕ), m.degree = d →
    ∃ w : Fin d → J, m = ∑ k, Finsupp.single (w k) 1 := by
  intro d
  induction d with
  | zero =>
    intro m hm
    refine ⟨Fin.elim0, ?_⟩
    rw [(Finsupp.degree_eq_zero_iff m).1 hm]
    simp
  | succ d ih =>
    intro m hm
    have hne : m ≠ 0 := by
      rintro rfl
      simp at hm
    obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hne
    have hle : Finsupp.single j 1 ≤ m := by
      rw [Finsupp.single_le_iff]
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hj
      omega
    have hsplit : m = Finsupp.single j 1 + (m - Finsupp.single j 1) :=
      (add_tsub_cancel_of_le hle).symm
    have hdeg : Finsupp.degree (m - Finsupp.single j 1) = d := by
      have h2 := congrArg Finsupp.degree hsplit
      rw [map_add, Finsupp.degree_single, hm] at h2
      omega
    obtain ⟨w', hw'⟩ := ih _ hdeg
    refine ⟨Fin.cons j w', ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hw']
    exact hsplit

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

/- English proof (translation)
Establish `hdeg : (∑ i, Finsupp.single (w i) (1 : ℕ)).degree = dimFl Ψ N + 1`. Rewrite using `[map_sum]`. Simplify using `[Finsupp.degree_single]`. Rewrite using `[HhModel.hhFl_monomial, hdeg]`. Use `congr 2`.

Conclude with `GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.hFlMono_sum_single Ψ N II hII hP w`.
-/
theorem hhFl_word (II : IntersectionSystem) (hII : IsIntersectionSystem II)
    (hP : IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1))
    (w : Fin (dimFl Ψ N + 1) → Ψ × Fin N) (c : ℝ) :
    hhFl Ψ N II (monomial (∑ k, Finsupp.single (w k) 1) c) = c * ((-1) ^ (dimFl Ψ N + 1) *
      II (GroundTheory.Heights₂.Heights.LowerBoundFree.FlBlock Ψ N) (GroundTheory.Heights₂.Heights.LowerBoundFree.FlIdx Ψ N)
        (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1)
        (fun k => GroundTheory.Heights₂.Heights.LowerBoundFree.xLine Ψ N (w k))) := by
  have hdeg : (∑ i, Finsupp.single (w i) (1 : ℕ)).degree = dimFl Ψ N + 1 := by
    rw [map_sum]
    simp [Finsupp.degree_single]
  rw [HhModel.hhFl_monomial, hdeg]
  congr 2
  exact GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.hFlMono_sum_single Ψ N II hII hP w

end RootFieldNumerics.HH
