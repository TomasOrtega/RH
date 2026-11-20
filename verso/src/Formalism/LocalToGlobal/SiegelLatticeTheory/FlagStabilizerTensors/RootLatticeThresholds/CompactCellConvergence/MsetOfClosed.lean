import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.RStabInv
import Formalism.PeriodIntegrals.ContinuousExpLie

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf.CC

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

/- English proof (translation)
Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Establish `hH` using `Formalism.FourierDecayAlt.P.BetaSesquilinearity.Hdet k r`. Establish `h` using `congrArg Matrix.det hg'`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_mul]`. Rewrite using `[isUnit_iff_ne_zero]`.

Introduce `h0`. Rewrite `h` using `[h0, mul_zero]`. Conclude with `hH.ne_zero h.symm`.
-/
theorem uh_isUnit {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    IsUnit g.det := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hH := Formalism.FourierDecayAlt.P.BetaSesquilinearity.Hdet k r
  have h := congrArg Matrix.det hg'
  rw [Matrix.det_mul, Matrix.det_mul] at h
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at h
  exact hH.ne_zero h.symm

/- English proof (translation)
The claim follows from `hg.1`.
-/
theorem n_sub {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ Nset k r) :
    g ∈ UH (Hpk k r) := hg.1

def Good (L : LocBessel k r) (x : PairSp k r) : Prop :=
  Matrix.of x.1.2 ∈ Nset k r ∧ Matrix.of x.2.2 ∈ Nset k r ∧ Matrix.of x.1.1 ∈ UWset k r L.z ∧
    Matrix.of x.2.1 ∈ UWset k r L.z'

/- English proof (translation)
Establish `hU : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | gᴴ * Hpk k r * g = Hpk k r}` using `isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const`. Establish `h2 : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → g i (eI k r a) = if i = eI k r a then 1 else 0}`. Simplify using `only [Set.setOf_forall]`. Conclude with `isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (continuous_id.matrix_elem _ _) continuous_const`. Establish `h3 : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val → g i j = if i = j then 1 else 0}`.

Simplify using `only [Set.setOf_forall]`. Conclude with `isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_eq (continuous_id.matrix_elem _ _) continuous_const`. Conclude with `hU.inter (h2.inter h3)`.
-/
theorem nset_closed : IsClosed (Nset k r) := by
  have hU : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | gᴴ * Hpk k r * g = Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  have h2 : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ |
      ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
        g i (eI k r a) = if i = eI k r a then 1 else 0} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (continuous_id.matrix_elem _ _) continuous_const
  have h3 : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ |
      ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
        g i j = if i = j then 1 else 0} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_eq (continuous_id.matrix_elem _ _) continuous_const
  exact hU.inter (h2.inter h3)

/- English proof (translation)
Establish `hU : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | gᴴ * Hpk k r * g = Hpk k r}` using `isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const`. Establish `h2 : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)}`. Simplify using `only [Set.setOf_forall, Set.setOf_and]`. Conclude with `isClosed_iInter fun a => (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const).inter (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)`. Establish `h3 : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | g *ᵥ z = z}` using `isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const`.

Conclude with `hU.inter (h2.inter h3)`.
-/
theorem uw_closed (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (UWset k r z) := by
  have hU : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | gᴴ * Hpk k r * g = Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  have h2 : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ |
      ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)} := by
    simp only [Set.setOf_forall, Set.setOf_and]
    exact isClosed_iInter fun a =>
      (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const).inter
        (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)
  have h3 : IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | g *ᵥ z = z} :=
    isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
  exact hU.inter (h2.inter h3)

/- English proof (translation)
Establish `hc : Continuous (fun x : Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))` using `continuous_id`. Conclude with `(hs.preimage hc).measurableSet`.
-/
theorem mset_of_closed {s : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)} (hs : IsClosed s) :
    MeasurableSet {x : Mt k r | Matrix.of x ∈ s} := by
  have hc : Continuous (fun x : Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
    continuous_id
  exact (hs.preimage hc).measurableSet

/- English proof (translation)
Establish `h1` using `mset_of_closed (nset_closed (k := k) (r := r))`. Establish `h2` using `mset_of_closed (uw_closed (k := k) (r := r) L.z)`. Establish `h3` using `mset_of_closed (uw_closed (k := k) (r := r) L.z')`. Conclude with `(h1.preimage measurable_fst.snd).inter ((h1.preimage measurable_snd.snd).inter ((h2.preimage measurable_fst.fst).inter (h3.preimage measurable_snd.fst)))`.
-/
theorem good_mset (L : LocBessel k r) : MeasurableSet {x : PairSp k r | Good L x} := by
  have h1 := mset_of_closed (nset_closed (k := k) (r := r))
  have h2 := mset_of_closed (uw_closed (k := k) (r := r) L.z)
  have h3 := mset_of_closed (uw_closed (k := k) (r := r) L.z')
  exact (h1.preimage measurable_fst.snd).inter ((h1.preimage measurable_snd.snd).inter
    ((h2.preimage measurable_fst.fst).inter (h3.preimage measurable_snd.fst)))

/- English proof (translation)
Establish `hmul : ∀ b ∈ Nset k r, ∀ m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, b * m ∈ Nset k r ↔ m ∈ Nset k r`. Introduce `b hb m`. Use `⟨fun h => ?_, fun h => Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul hb h⟩` and prove the remaining obligations. Establish `hu` using `uh_isUnit (n_sub hb)`. Use `Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul (Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hb) h` as an intermediate fact.

Rewrite `this` using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]`. Then use the resulting hypothesis. Use `show (a * Matrix.of x.1.2 ∈ Nset k r ∧ γ⁻¹ * a * γ * Matrix.of x.2.2 ∈ Nset k r ∧ Matrix.of x.1.1 ∈ UWset k r L.z ∧ Matrix.of x.2.1 ∈ UWset k r L.z') ↔ Good L x`. Rewrite using `[hmul a ha.1, hmul _ ha.2]`. Both sides reduce to the same expression.
-/
theorem good_stabAct (L : LocBessel k r) {γ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ RStab k r γ) (x : PairSp k r) : Good L (stabAct γ a x) ↔ Good L x := by
  have hmul : ∀ b ∈ Nset k r, ∀ m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      b * m ∈ Nset k r ↔ m ∈ Nset k r := by
    intro b hb m
    refine ⟨fun h => ?_, fun h => Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul hb h⟩
    have hu := uh_isUnit (n_sub hb)
    have := Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul (Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hb) h
    rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul] at this
  show (a * Matrix.of x.1.2 ∈ Nset k r ∧ γ⁻¹ * a * γ * Matrix.of x.2.2 ∈ Nset k r ∧
      Matrix.of x.1.1 ∈ UWset k r L.z ∧ Matrix.of x.2.1 ∈ UWset k r L.z') ↔ Good L x
  rw [hmul a ha.1, hmul _ ha.2]
  rfl

end Formalism.MainNotions.S.Pv.AmpDDPf.CC
