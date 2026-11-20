import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ObjectsTied
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PGenLeadMinorNeZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

/- English proof (translation)
Use extensionality with `p q`. Simplify using `only [genMat0Fr, genMatFr, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem genMat0Fr_eq_map (F : Type) [Field F] (Ψ : Type) (n j : ℕ) (τ : Ψ) :
    genMat0Fr F Ψ n j τ = (algebraMap (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n)).mapMatrix
      (Matrix.of fun (p q : Fin n) => if (p : ℕ) < j ∧ j ≤ (q : ℕ) then 0 else
        (X (τ, p, q) : MvPolynomial (Ψ × Fin n × Fin n) F)) := by
  ext p q
  simp only [genMat0Fr, genMatFr, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

/- English proof (translation)
Introduce `F _ Ψ n j τ a`. Rewrite using `[genMat0Fr_eq_map, ← leadMinor_map]`. Use `(map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n))).2 ?_` and prove the remaining obligations. Introduce `h0`. Establish `h1` using `congrArg (MvPolynomial.eval (fun q : Ψ × Fin n × Fin n => if q.2.1 = q.2.2 then (1 : F) else 0)) h0`.

Rewrite `h1` using `[leadMinor_map, map_zero]`. Establish `hP : (MvPolynomial.eval (fun q : Ψ × Fin n × Fin n => if q.2.1 = q.2.2 then (1 : F) else 0)).mapMatrix (Matrix.of fun (p q : Fin n) => if (p : ℕ) < j ∧ j ≤ (q : ℕ) then 0 else (X (τ, p, q) : MvPolynomial (Ψ × Fin n × Fin n) F)) = 1`. Use extensionality with `p q`. Distinguish the cases in `hc : (p : ℕ) < j ∧ j ≤ (q : ℕ)`. Establish `hpq : p ≠ q`.

Introduce and unpack `rfl`. Take `⟨hc₁, hc₂⟩` from `hc`. Use linear arithmetic over natural numbers and integers. Simplify using `[hc, hpq]`. Simplify using `[hc, Matrix.one_apply]`.

Rewrite `h1` using `[hP, leadMinor_one]`. Conclude with `one_ne_zero h1`.
-/
theorem GenLeadMinor0NeZero.full : GenLeadMinor0NeZero.Statement := by
  intro F _ Ψ n j τ a
  rw [genMat0Fr_eq_map, ← leadMinor_map]
  refine (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n))).2 ?_
  intro h0
  have h1 := congrArg (MvPolynomial.eval (fun q : Ψ × Fin n × Fin n => if q.2.1 = q.2.2 then (1 : F) else 0)) h0
  rw [leadMinor_map, map_zero] at h1
  have hP : (MvPolynomial.eval (fun q : Ψ × Fin n × Fin n => if q.2.1 = q.2.2 then (1 : F) else 0)).mapMatrix
      (Matrix.of fun (p q : Fin n) => if (p : ℕ) < j ∧ j ≤ (q : ℕ) then 0 else
        (X (τ, p, q) : MvPolynomial (Ψ × Fin n × Fin n) F)) = 1 := by
    ext p q
    by_cases hc : (p : ℕ) < j ∧ j ≤ (q : ℕ)
    · have hpq : p ≠ q := by
        rintro rfl
        obtain ⟨hc₁, hc₂⟩ := hc
        omega
      simp [hc, hpq]
    · simp [hc, Matrix.one_apply]
  rw [hP, leadMinor_one] at h1
  exact one_ne_zero h1

end GroundTheory.Heights₂.Heights.LowerBoundFree
