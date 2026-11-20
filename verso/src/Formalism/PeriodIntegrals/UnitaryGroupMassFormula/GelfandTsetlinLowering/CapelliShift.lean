import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.CapelliEqv
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

/- English proof (translation)
Establish `key : ∀ (p : Prop) [Decidable p] (y : A), (if p then algebraMap ℂ A c else 0) * y = y * (if p then algebraMap ℂ A c else 0)`. Introduce `p _ y`. Use `split_ifs`. Conclude with `Algebra.commutes c y`. Simplify using the standard rewrite rules.

Introduce `i j k l`. Simplify using `only`. Establish `h1` using `key (i = j) (E k l)`. Establish `h2` using `key (k = l) (E i j)`. Establish `h3` using `key (i = j) (if k = l then algebraMap ℂ A c else 0)`.

Combine the equalities or inequalities in the displayed calculation. Apply the tactic sequence `by_cases hjk : j = k <;> by_cases hli : l = i`. Substitute `hjk` using the available equality. Substitute `hli` using the available equality. Simplify using the standard rewrite rules.

Establish `hil : ¬ i = l` using `fun h => hli h.symm`. Simplify using `[hjk, hli, hil]`. Establish `hkj : ¬ k = j` using `fun h => hjk h.symm`. Simplify using `[hjk, hli, hkj]`. Simplify using `[hjk, hli]`.
-/
theorem glRel_shift {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : Formalism.REAL.GlRel E) (c : ℂ) :
    Formalism.REAL.GlRel (fun a b => E a b + if a = b then algebraMap ℂ A c else 0) := by
  have key : ∀ (p : Prop) [Decidable p] (y : A),
      (if p then algebraMap ℂ A c else 0) * y = y * (if p then algebraMap ℂ A c else 0) := by
    intro p _ y
    split_ifs
    · exact Algebra.commutes c y
    · simp
  intro i j k l
  simp only
  have h1 := key (i = j) (E k l)
  have h2 := key (k = l) (E i j)
  have h3 := key (i = j) (if k = l then algebraMap ℂ A c else 0)
  calc (E i j + if i = j then algebraMap ℂ A c else 0) * (E k l + if k = l then algebraMap ℂ A c else 0) -
        (E k l + if k = l then algebraMap ℂ A c else 0) * (E i j + if i = j then algebraMap ℂ A c else 0)
      = (E i j * E k l - E k l * E i j)
        + ((if i = j then algebraMap ℂ A c else 0) * E k l - E k l * (if i = j then algebraMap ℂ A c else 0))
        - ((if k = l then algebraMap ℂ A c else 0) * E i j - E i j * (if k = l then algebraMap ℂ A c else 0))
        + ((if i = j then algebraMap ℂ A c else 0) * (if k = l then algebraMap ℂ A c else 0)
          - (if k = l then algebraMap ℂ A c else 0) * (if i = j then algebraMap ℂ A c else 0)) := by
        noncomm_ring
    _ = E i j * E k l - E k l * E i j := by rw [h1, h2, h3]; abel
    _ = (if j = k then E i l else 0) - (if l = i then E k j else 0) := hE i j k l
    _ = _ := by
        by_cases hjk : j = k <;> by_cases hli : l = i
        · subst hjk; subst hli; simp
        · have hil : ¬ i = l := fun h => hli h.symm
          simp [hjk, hli, hil]
        · have hkj : ¬ k = j := fun h => hjk h.symm
          simp [hjk, hli, hkj]
        · simp [hjk, hli]

def capE {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (a b : Fin n) :
    Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
  pol ℂ (Fin.castLE (by omega) a) (Fin.castLE (by omega) b) +
    if a = b then algebraMap ℂ _ (lam.detShift : ℂ) else 0

/- English proof (translation)
Establish `hP` using `pol_glRel N N`. Establish `hR : Formalism.REAL.GlRel (fun a b : Fin n => (pol ℂ (Fin.castLE (by omega : n ≤ N) a) (Fin.castLE (by omega : n ≤ N) b) : Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ)))`. Introduce `i j k l`. Use `hP (Fin.castLE (by omega) i) (Fin.castLE (by omega) j) (Fin.castLE (by omega) k) (Fin.castLE (by omega) l)` as an intermediate fact. Simplify using `only [Fin.castLE_inj] at this`.

Conclude with `this`. Conclude with `glRel_shift _ hR _`.
-/
theorem capE_glRel {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) : Formalism.REAL.GlRel (capE h lam) := by
  have hP := pol_glRel N N
  have hR : Formalism.REAL.GlRel (fun a b : Fin n =>
      (pol ℂ (Fin.castLE (by omega : n ≤ N) a) (Fin.castLE (by omega : n ≤ N) b) :
        Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ))) := by
    intro i j k l
    have := hP (Fin.castLE (by omega) i) (Fin.castLE (by omega) j) (Fin.castLE (by omega) k)
      (Fin.castLE (by omega) l)
    simp only [Fin.castLE_inj] at this
    exact this
  exact glRel_shift _ hR _

/- English proof (translation)
Unfold `capE`. Use `split_ifs`. Rewrite using `[LinearMap.add_apply, Module.algebraMap_end_apply]`. Simplify using the standard rewrite rules.
-/
theorem capE_apply {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (a b : Fin n) (x : MvPolynomial (Fin N × Fin N) ℂ) :
    capE h lam a b x = pol ℂ (Fin.castLE (by omega) a) (Fin.castLE (by omega) b) x +
      if a = b then (lam.detShift : ℂ) • x else 0 := by
  unfold capE
  split_ifs
  · rw [LinearMap.add_apply, Module.algebraMap_end_apply]
  · simp

end PI.WGL
