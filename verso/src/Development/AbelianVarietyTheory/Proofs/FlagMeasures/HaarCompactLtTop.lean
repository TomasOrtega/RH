import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedSubgroupBesselHaarFiniteCompactPosOpenStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf

variable {k r : ℕ}

def oneM (k r : ℕ) : Mt k r := fun i j => (1 : Mat k r) i j

def nbd (k r : ℕ) (j : ℕ) : Set (Mt k r) := Metric.closedBall (oneM k r) (1 / ((j : ℝ) + 1))

def avgR {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℝ Wp] (μ : Measure (Mt k r)) (j : ℕ)
    (g : Mt k r → Wp) (x : Mt k r) : Wp :=
  ((μ (nbd k r j)).toReal)⁻¹ • ∫ y in nbd k r j, g (rmulM (Matrix.of x) y) ∂μ

/- English proof (translation)
Unfold `nbd`. Conclude with `isCompact_closedBall _ _`.
-/
theorem isCompact_nbd (j : ℕ) : IsCompact (nbd k r j) := by
  unfold nbd
  exact isCompact_closedBall _ _

/- English proof (translation)
Unfold `nbd`. Conclude with `Metric.mem_closedBall_self (by positivity)`.
-/
theorem oneM_mem_nbd (j : ℕ) : oneM k r ∈ nbd k r j := by
  unfold nbd
  exact Metric.mem_closedBall_self (by positivity)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `i hi`. Establish `hne : i ≠ ⟨r + k, by omega⟩`. Introduce and unpack `rfl`. Simplify using `at hi`.

Simplify using `[hne]`. Simplify using `only [Formalism.QuantumDeterminants.Tz, Formalism.QuantumDeterminants.herm, Formalism.QuantumDeterminants.Hpk, dotProduct, mulVec, Pi.single_apply, Pi.star_apply, Complex.re_sum, neg_pos]`. Rewrite using `[Finset.sum_eq_single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1))]`. Establish `h1 : ¬ (r + k < r)` using `by omega`. Simplify using `[h1, Finset.sum_ite_eq']`.

Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules.
-/
private lemma single_mem_inWb_and_Tz_pos (k r : ℕ) :
    Formalism.QuantumDeterminants.inWb k r (Pi.single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1)) 1) ∧
      0 < Formalism.QuantumDeterminants.Tz k r (Pi.single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1)) 1) := by
  constructor
  · intro i hi
    have hne : i ≠ ⟨r + k, by omega⟩ := by
      rintro rfl
      simp at hi
    simp [hne]
  · simp only [Formalism.QuantumDeterminants.Tz, Formalism.QuantumDeterminants.herm, Formalism.QuantumDeterminants.Hpk, dotProduct, mulVec, Pi.single_apply,
      Pi.star_apply, Complex.re_sum, neg_pos]
    rw [Finset.sum_eq_single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1))]
    · have h1 : ¬ (r + k < r) := by omega
      simp [h1, Finset.sum_ite_eq']
    · intro b _ hb
      simp [hb]
    · simp

/- English proof (translation)
The claim follows from `(GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r _ (single_mem_inWb_and_Tz_pos k r).1 (single_mem_inWb_and_Tz_pos k r).2).1`.
-/
theorem gg_closedSub (k r : ℕ) : IsClosedSub k r (GG k r) :=
  (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r _ (single_mem_inWb_and_Tz_pos k r).1 (single_mem_inWb_and_Tz_pos k r).2).1

/- English proof (translation)
The claim follows from `(GlobalTheory.T.closedSubgroupBessel_haar_finite_compact_pos_open k r (GG k r) μ (gg_closedSub k r) hμ).1 C hC`.
-/
theorem haar_compact_lt_top {μ : Measure (Mt k r)} (hμ : IsHaarOn (GG k r) μ) {C : Set (Mt k r)}
    (hC : IsCompact C) : μ C < ⊤ :=
  (GlobalTheory.T.closedSubgroupBessel_haar_finite_compact_pos_open k r (GG k r) μ (gg_closedSub k r) hμ).1 C hC

/- English proof (translation)
Establish `h1 : Matrix.of (oneM k r) = (1 : Mat k r)`. Use extensionality with `a b`. Simplify using `[oneM]`. Establish `hone : Matrix.of (oneM k r) ∈ GG k r`. Rewrite using `[h1]`.

Conclude with `(gg_closedSub k r).2.2.1`. Establish `hU` using `(GlobalTheory.T.closedSubgroupBessel_haar_finite_compact_pos_open k r (GG k r) μ (gg_closedSub k r) hμ).2 (Metric.ball (oneM k r) (1 / ((j : ℝ) + 1))) Metric.isOpen_ball ⟨oneM k r, Metric.mem_ball_self (by positivity), hone⟩`. Unfold `nbd`. Conclude with `lt_of_lt_of_le hU (measure_mono Metric.ball_subset_closedBall)`.
-/
theorem nbd_pos {μ : Measure (Mt k r)} (hμ : IsHaarOn (GG k r) μ) (j : ℕ) : 0 < μ (nbd k r j) := by
  have h1 : Matrix.of (oneM k r) = (1 : Mat k r) := by
    ext a b
    simp [oneM]
  have hone : Matrix.of (oneM k r) ∈ GG k r := by
    rw [h1]
    exact (gg_closedSub k r).2.2.1
  have hU := (GlobalTheory.T.closedSubgroupBessel_haar_finite_compact_pos_open k r (GG k r) μ (gg_closedSub k r) hμ).2
    (Metric.ball (oneM k r) (1 / ((j : ℝ) + 1))) Metric.isOpen_ball
    ⟨oneM k r, Metric.mem_ball_self (by positivity), hone⟩
  unfold nbd
  exact lt_of_lt_of_le hU (measure_mono Metric.ball_subset_closedBall)

end GlobalTheory.SgInf
