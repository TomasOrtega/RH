import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.InfinityTypes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaWeightArithmeticAtPlaceProofStatement
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.OneLeAPlLast
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JointHarm

open GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes in

/- English proof (translation)
Introduce `D i σ hσ M _`. Substitute `hσ` using the available equality. Establish `hnr : ∃ s : ℕ, D.R.r + D.R.t = 2 * s`. Take `⟨a, ha⟩` from `Formalism.L2.NTheta.odd_r D.R`. Take `⟨b, hb⟩` from `D.R.t_odd`.

Conclude with `⟨a + b + 1, by omega⟩`. Take `⟨s, hs⟩` from `hnr`. Establish `hsq : (D.R.r : ℚ) + D.R.t = 2 * s` using `by exact_mod_cast hs`. Use `choose e he using fun τ : D.what₂.Tau => (D.hc τ).e_int i`. Use `choose d hd using fun τ : D.what₂.Tau => (GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ).d_int`.

Use `⟨fun τ => -e τ + s, fun τ => -e τ - s, fun τ => -d τ, fun τ => ?_⟩` and prove the remaining obligations. Establish `A` using `GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ`. Take `⟨hpq, hV⟩` from `A.rank`. Establish `hVq : ((Vc D i).rank : ℚ) = 2 * s` using `by rw [hV, hs]; push_cast; rfl`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[he, hVq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he, hVq]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `hd τ` as an intermediate fact. Unfold `dShift at this`. Use `push_cast`. Rewrite using `[← this]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hen` using `M.enum τ`. Rewrite `hen` using `[GlobalTheory.ThetaFiresProbe.parAt_fixed]`. Take `⟨hn, hx⟩` from `GlobalTheory.HolDS.lowK_holPar (Formalism.L2.NTheta.holOK_kapW (D.hc τ) _ _ hpq) hen`. Introduce `a`.

Take `⟨x, rfl⟩ : ∃ x, a = Fin.cast hn (finSumFinEquiv x)` from `⟨finSumFinEquiv.symm (Fin.cast hn.symm a), by simp⟩`. Rewrite using `[hx x]`. Use `congr 1`. Break down `x with c | c` into its components or cases. Establish `h1` using `A.kap_plus c`.

Rewrite `h1` using `[hsq, eS, he]`. Establish `h2 : Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inl c) = (aP D i τ c : ℤ) + (-e τ + s)`. Establish `: ((Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inl c) : ℤ) : ℚ) = (((aP D i τ c : ℤ) + (-e τ + s) : ℤ) : ℚ)` using `by rw [h1]; push_cast; ring`. Conclude with `this` after adjusting the coercions. Rewrite using `[h2]`.

Unfold `wtK`. Rewrite using `[if_pos (by simp)]`. Simplify using the standard rewrite rules. Establish `h1` using `A.kap_minus c`. Rewrite `h1` using `[hsq, eS, he]`.

Establish `h2 : Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inr c) = -(aM D i τ (qS D i τ - 1 - c) : ℤ) + (-e τ - s)`. Establish `: ((Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inr c) : ℤ) : ℚ) = ((-(aM D i τ (qS D i τ - 1 - c) : ℤ) + (-e τ - s) : ℤ) : ℚ)` using `by rw [h1]; push_cast; ring`. Conclude with `this` after adjusting the coercions. Rewrite using `[h2]`. Unfold `wtK`.

Rewrite using `[if_neg (by simp)]`. Establish `h3 : (Wc D i).rank - 1 - ((Fin.cast hn (finSumFinEquiv (Sum.inr c)) : Fin (Wc D i).rank) : ℕ) = qS D i τ - 1 - c`. Simplify using `only [finSumFinEquiv_apply_right, Fin.val_cast, Fin.val_natAdd]`. Rewrite using `[← hn]`. Simplify using `only [qS]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[h3]`. Introduce `j`. Establish `h1` using `A.coef_eq j`. Rewrite `h1` using `[hd]`.

Establish `h2 : (Bridge.lamLdef (D` using `D) (Vc D i).rank ((i : ℕ) + 1) τ).w j = thetaWt D i τ j + d τ := by`. Conclude with `h1` after adjusting the coercions. Rewrite using `[h2]`. Establish `hj` using `j.2`. Unfold `wtU thetaWt`.

Simplify using `only [pS, qS] at hpq ⊢`. Distinguish the cases in `c1 : (j : ℕ) < ((Wc D i).sig (tauE D τ)).1`. Establish `ht` using `D.R.three_m_lt_t`. Rewrite using `[if_pos c1, if_pos c1, if_neg (by omega)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_neg c1, if_neg c1]`. Distinguish the cases in `c2 : (j : ℕ) < ((Wc D i).sig (tauE D τ)).1 + D.R.t`. Rewrite using `[if_pos c2, if_neg (by omega)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg c2, if_pos (by omega)]`.

Establish `h3 : (Vc D i).rank - 1 - (j : ℕ) = ((Wc D i).sig (tauE D τ)).2 - 1 - (j - (((Wc D i).sig (tauE D τ)).1 + D.R.t))`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weights_of_minors : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), σ = D.what₂.embLL → ∀ M : DSModel (Wc D i) (parAt (Wc D i) σ), (∀ τ a, M.ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)) → ∃ x₁ x₂ x₃ : D.what₂.Tau → ℤ, ∀ τ, (x₁ τ : ℚ) = -(D.hc τ).e i + ((Vc D i).rank : ℚ) / 2 ∧ (x₂ τ : ℚ) = -(D.hc τ).e i - ((Vc D i).rank : ℚ) / 2 ∧ (x₃ τ : ℚ) = -(((((Wc D i).sig (tauE D τ)).1 : ℚ) - ((Wc D i).sig (tauE D τ)).2) / 2 + (-(D.hc τ).e i - 1 / 2)) ∧ (∀ a, Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ) a = (wtK ((Wc D i).sig (tauE D τ)).1 (aPl D i ((Wc D i).sig (tauE D τ)).1 τ) (aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ) (x₁ τ) (x₂ τ) a : ℝ)) ∧ ∀ j : Fin (Vc D i).rank, wtU ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 (aPl D i ((Wc D i).sig (tauE D τ)).1 τ) (aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ) (x₃ τ) j = -(Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w j := by
  intro D i σ hσ M _
  subst hσ
  have hnr : ∃ s : ℕ, D.R.r + D.R.t = 2 * s := by
    obtain ⟨a, ha⟩ := Formalism.L2.NTheta.odd_r D.R
    obtain ⟨b, hb⟩ := D.R.t_odd
    exact ⟨a + b + 1, by omega⟩
  obtain ⟨s, hs⟩ := hnr
  have hsq : (D.R.r : ℚ) + D.R.t = 2 * s := by exact_mod_cast hs
  choose e he using fun τ : D.what₂.Tau => (D.hc τ).e_int i
  choose d hd using fun τ : D.what₂.Tau => (GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ).d_int
  refine ⟨fun τ => -e τ + s, fun τ => -e τ - s, fun τ => -d τ, fun τ => ?_⟩
  have A := GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ
  obtain ⟨hpq, hV⟩ := A.rank
  have hVq : ((Vc D i).rank : ℚ) = 2 * s := by rw [hV, hs]; push_cast; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [he, hVq]; push_cast; ring
  · rw [he, hVq]; push_cast; ring
  · have := hd τ
    unfold dShift at this
    push_cast
    rw [← this]
    ring
  · have hen := M.enum τ
    rw [GlobalTheory.ThetaFiresProbe.parAt_fixed] at hen
    obtain ⟨hn, hx⟩ := GlobalTheory.HolDS.lowK_holPar (Formalism.L2.NTheta.holOK_kapW (D.hc τ) _ _ hpq) hen
    intro a
    obtain ⟨x, rfl⟩ : ∃ x, a = Fin.cast hn (finSumFinEquiv x) :=
      ⟨finSumFinEquiv.symm (Fin.cast hn.symm a), by simp⟩
    rw [hx x]
    congr 1
    rcases x with c | c
    · have h1 := A.kap_plus c
      rw [hsq, eS, he] at h1
      have h2 : Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inl c) = (aP D i τ c : ℤ) + (-e τ + s) := by
        have : ((Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inl c) : ℤ) : ℚ) =
            (((aP D i τ c : ℤ) + (-e τ + s) : ℤ) : ℚ) := by rw [h1]; push_cast; ring
        exact_mod_cast this
      rw [h2]
      unfold wtK
      rw [if_pos (by simp)]
      simp
    · have h1 := A.kap_minus c
      rw [hsq, eS, he] at h1
      have h2 : Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inr c) =
          -(aM D i τ (qS D i τ - 1 - c) : ℤ) + (-e τ - s) := by
        have : ((Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inr c) : ℤ) : ℚ) =
            ((-(aM D i τ (qS D i τ - 1 - c) : ℤ) + (-e τ - s) : ℤ) : ℚ) := by rw [h1]; push_cast; ring
        exact_mod_cast this
      rw [h2]
      unfold wtK
      rw [if_neg (by simp)]
      have h3 : (Wc D i).rank - 1 - ((Fin.cast hn (finSumFinEquiv (Sum.inr c)) : Fin (Wc D i).rank) : ℕ) =
          qS D i τ - 1 - c := by
        simp only [finSumFinEquiv_apply_right, Fin.val_cast, Fin.val_natAdd]
        rw [← hn]
        simp only [qS]
        omega
      rw [h3]
  · intro j
    have h1 := A.coef_eq j
    rw [hd] at h1
    have h2 : (Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w j = thetaWt D i τ j + d τ := by
      exact_mod_cast h1
    rw [h2]
    have hj := j.2
    unfold wtU thetaWt
    simp only [pS, qS] at hpq ⊢
    by_cases c1 : (j : ℕ) < ((Wc D i).sig (tauE D τ)).1
    · have ht := D.R.three_m_lt_t
      rw [if_pos c1, if_pos c1, if_neg (by omega)]
      ring
    · rw [if_neg c1, if_neg c1]
      by_cases c2 : (j : ℕ) < ((Wc D i).sig (tauE D τ)).1 + D.R.t
      · rw [if_pos c2, if_neg (by omega)]
        ring
      · rw [if_neg c2, if_pos (by omega)]
        have h3 : (Vc D i).rank - 1 - (j : ℕ) = ((Wc D i).sig (tauE D τ)).2 - 1 - (j - (((Wc D i).sig (tauE D τ)).1 + D.R.t)) := by
          omega
        rw [h3]
        ring

end GlobalTheory.JointHarm
