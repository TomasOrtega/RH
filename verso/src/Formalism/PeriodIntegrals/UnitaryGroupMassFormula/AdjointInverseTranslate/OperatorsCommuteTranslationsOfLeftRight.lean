import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.CoefLeftAAv

open Matrix

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

/- English proof (translation)
Establish `ha' : aᴴ * H * a = H` using `ha`. Establish `hb' : bᴴ * H * b = H` using `hb`. Use `show (a * b)ᴴ * H * (a * b) = H`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem inUH_mul {n : ℕ} {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hb : inUH H b) :
    inUH H (a * b) := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha', hb']

/- English proof (translation)
Unfold `OperatorsCommuteTranslations`. Introduce `E _ _ k r z z' m hm u ell f _ _ hf s hs s' hs' g hg`. Establish `hsg : inUH (Hpk k r) (s * g)` using `inUH_mul (hS k r z s hs) hg`. Take `⟨hL1, hL2⟩` from `hL E k r z m hm u ell (fun x => f (x * s')) s g hs hg`. Take `⟨hR1, hR2⟩` from `hR E k r z' m hm u ell f s' (s * g) hf hs' hsg`.

Conclude with `⟨hL1.trans hR1, hL2.trans hR2⟩`.
-/
theorem operators_commute_translations_of_left_right (hL : LeftAA) (hR : RightAA) (hS : SsetUH) : OperatorsCommuteTranslations := by
  unfold OperatorsCommuteTranslations
  intro E _ _ k r z z' m hm u ell f _ _ hf s hs s' hs' g hg
  have hsg : inUH (Hpk k r) (s * g) := inUH_mul (hS k r z s hs) hg
  obtain ⟨hL1, hL2⟩ := hL E k r z m hm u ell (fun x => f (x * s')) s g hs hg
  obtain ⟨hR1, hR2⟩ := hR E k r z' m hm u ell f s' (s * g) hf hs' hsg
  exact ⟨hL1.trans hR1, hL2.trans hR2⟩

end AAInvW
