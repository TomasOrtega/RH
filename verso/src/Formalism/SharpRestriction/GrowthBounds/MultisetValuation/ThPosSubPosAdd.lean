import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ThRestGcVOf
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TheoremSFromKOneOf

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lamF altF)

section CgCalc

variable {ι K : Type} [Field K] (R : Subring K) (pp : K)

def Cg (f g : MvPowerSeries ι K) : Prop := ∃ Y : MvPowerSeries ι K, IntR R Y ∧ f = g + MvPowerSeries.C pp * Y

variable {R pp}

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem cg_refl (f : MvPowerSeries ι K) : Cg R pp f f := ⟨0, IntR_zero, by simp⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cg_of_eq {f g : MvPowerSeries ι K} (h : f = g) : Cg R pp f g := h ▸ cg_refl f

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem cg_symm {f g : MvPowerSeries ι K} (h : Cg R pp f g) : Cg R pp g f := by
  obtain ⟨Y, hY, e⟩ := h
  exact ⟨-Y, IntR_neg hY, by rw [e]; ring⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem cg_trans {f g k : MvPowerSeries ι K} (h1 : Cg R pp f g) (h2 : Cg R pp g k) : Cg R pp f k := by
  obtain ⟨Y, hY, e⟩ := h1
  obtain ⟨Y', hY', e'⟩ := h2
  exact ⟨Y + Y', IntR_add hY hY', by rw [e, e']; ring⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem cg_add {f g f' g' : MvPowerSeries ι K} (h1 : Cg R pp f g) (h2 : Cg R pp f' g') :
    Cg R pp (f + f') (g + g') := by
  obtain ⟨Y, hY, e⟩ := h1
  obtain ⟨Y', hY', e'⟩ := h2
  exact ⟨Y + Y', IntR_add hY hY', by rw [e, e']; ring⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem cg_sub {f g f' g' : MvPowerSeries ι K} (h1 : Cg R pp f g) (h2 : Cg R pp f' g') :
    Cg R pp (f - f') (g - g') := by
  obtain ⟨Y, hY, e⟩ := h1
  obtain ⟨Y', hY', e'⟩ := h2
  exact ⟨Y + -Y', IntR_add hY (IntR_neg hY'), by rw [e, e']; ring⟩

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cg_sum {α : Type} (s : Finset α) (F G : α → MvPowerSeries ι K) (h : ∀ a ∈ s, Cg R pp (F a) (G a)) :
    Cg R pp (∑ a ∈ s, F a) (∑ a ∈ s, G a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact cg_refl _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact cg_add (h a (Finset.mem_insert_self _ _)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem cg_mul {f g f' g' : MvPowerSeries ι K} (hf' : IntR R f') (hg : IntR R g) (h1 : Cg R pp f g)
    (h2 : Cg R pp f' g') : Cg R pp (f * f') (g * g') := by
  obtain ⟨Y, hY, e⟩ := h1
  obtain ⟨Y', hY', e'⟩ := h2
  refine ⟨g * Y' + Y * f', IntR_add (IntR_mul hg hY') (IntR_mul hY hf'), ?_⟩
  rw [e]
  conv_lhs => rw [add_mul, e']
  conv_rhs => rw [e']
  ring

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem cg_pow {f g : MvPowerSeries ι K} (hf : IntR R f) (hg : IntR R g) (h : Cg R pp f g) (k : ℕ) :
    Cg R pp (f ^ k) (g ^ k) := by
  induction k with
  | zero => exact cg_of_eq (by simp)
  | succ k ih => rw [pow_succ, pow_succ]; exact cg_mul hf (IntR_pow hg k) ih h

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem cg_of_coeff {f g : MvPowerSeries ι K}
    (h : ∀ n, ∃ y ∈ R, MvPowerSeries.coeff n f = MvPowerSeries.coeff n g + pp * y) : Cg R pp f g := by
  choose y hy he using h
  let Y : MvPowerSeries ι K := fun n => y n
  have hYc : ∀ n, MvPowerSeries.coeff n Y = y n := fun _ => rfl
  refine ⟨Y, fun n => by rw [hYc]; exact hy n, ?_⟩
  ext n
  rw [map_add, MvPowerSeries.coeff_C_mul, he n, hYc]

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem cg_coeff {f g : MvPowerSeries ι K} (h : Cg R pp f g) (n : ι →₀ ℕ) :
    ∃ y ∈ R, MvPowerSeries.coeff n f = MvPowerSeries.coeff n g + pp * y := by
  obtain ⟨Y, hY, e⟩ := h
  exact ⟨_, hY n, by rw [e, map_add, MvPowerSeries.coeff_C_mul]⟩

end CgCalc

section Pos

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem th_posSub_posAdd {n' : ℕ} (s : Fin n') (d : ℕ) : posSub (posAdd s d) d = s := by
  obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by have := s.pos; omega⟩
  apply Fin.ext
  show ((s.val + d) % (m + 1) + (m + 1) * d - d) % (m + 1) = s.val
  have e : (s.val + d) % (m + 1) + (m + 1) * d - d = (s.val + d) % (m + 1) + m * d := by
    have : (m + 1) * d = m * d + d := by ring
    omega
  rw [e, Nat.mod_add_mod]
  have e2 : s.val + d + m * d = s.val + (m + 1) * d := by ring
  rw [e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt s.isLt]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem th_posAdd_posSub {n' : ℕ} (t : Fin n') (d : ℕ) : posAdd (posSub t d) d = t := by
  obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by have := t.pos; omega⟩
  apply Fin.ext
  show ((t.val + (m + 1) * d - d) % (m + 1) + d) % (m + 1) = t.val
  have e : t.val + (m + 1) * d - d = t.val + m * d := by
    have : (m + 1) * d = m * d + d := by ring
    omega
  rw [e, Nat.mod_add_mod]
  have e2 : t.val + m * d + d = t.val + (m + 1) * d := by ring
  rw [e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt t.isLt]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem th_odd_posAdd {n' : ℕ} (hev : Even n') (s : Fin n') (d : ℕ) :
    (posAdd s d).val % 2 = (s.val + d) % 2 := by
  show (s.val + d) % n' % 2 = _
  exact Nat.mod_mod_of_dvd _ hev.two_dvd

end Pos

end Formalism.MainNotions.FormalGroupSystem.Pf
