import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountPositivity.CardLeOfNegFamily

noncomputable section

namespace PI.CntNotPosW

open Matrix Formalism.BasicNotions Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E] [StarRing E]

section Form

variable (S : HSpace E)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hl_sub (x y z : S.V) : S.hT (x - y) z = S.hT x z - S.hT y z := by
  simp
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hl_add (x y z : S.V) : S.hT (x + y) z = S.hT x z + S.hT y z := by
  simp
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hl_smul (c : E) (x z : S.V) : S.hT (c • x) z = star c * S.hT x z := by
  simp [starRingEnd_apply]
/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem hl_sum {ι : Type} (s : Finset ι) (x : ι → S.V) (z : S.V) :
    S.hT (∑ i ∈ s, x i) z = ∑ i ∈ s, S.hT (x i) z := by
  rw [map_sum, LinearMap.sum_apply]
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hr_sub (x y z : S.V) : S.hT z (x - y) = S.hT z x - S.hT z y := by
  simp
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hr_add (x y z : S.V) : S.hT z (x + y) = S.hT z x + S.hT z y := by
  simp
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hr_smul (c : E) (x z : S.V) : S.hT z (c • x) = c * S.hT z x := by
  simp
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hr_sum {ι : Type} (s : Finset ι) (x : ι → S.V) (z : S.V) :
    S.hT z (∑ i ∈ s, x i) = ∑ i ∈ s, S.hT z (x i) := by
  exact map_sum (S.hT z) x s
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem h_swap (x y : S.V) : S.hT y x = star (S.hT x y) := by
  exact (S.herm.eq x y).symm
/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem h_zero_swap {x y : S.V} (h : S.hT x y = 0) : S.hT y x = 0 := by
  rw [h_swap, h, star_zero]

end Form

section Flags

variable {S : HSpace E} {r : ℕ} {T T' : ℕ}

def Pm (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a b => S.hT (F.e a) (F'.e b)

def ed (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) (b : Fin r) : S.V :=
  ∑ c, (Pm F F')⁻¹ c b • F'.e c

def vv (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) (a : Fin r) : S.V := F.e a - ed F F' a

def cz (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) (b : Fin r) : E := S.hT (ed F F' b) F.z

def zt (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) : S.V := F.z - ∑ a, cz F F' a • F.e a

def cz' (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) (b : Fin r) : E := S.hT (F.e b) F'.z

def zt' (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) : S.V := F'.z - ∑ a, cz' F F' a • ed F F' a

def beta (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) : E := S.hT (zt F F') (zt' F F')

def zt2 (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E)) : S.V :=
  zt' F F' + (beta F F' / (T : E)) • zt F F'

variable (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E))

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem h_e_ed (hP : (Pm F F').det ≠ 0) (a b : Fin r) :
    S.hT (F.e a) (ed F F' b) = if a = b then 1 else 0 := by
  have h1 : Pm F F' * (Pm F F')⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP)
  have h2 := congrFun (congrFun h1 a) b
  rw [Matrix.mul_apply, Matrix.one_apply] at h2
  rw [← h2]
  unfold ed
  rw [hr_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hr_smul, mul_comm]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem h_ed_e (hP : (Pm F F').det ≠ 0) (a b : Fin r) :
    S.hT (ed F F' a) (F.e b) = if a = b then 1 else 0 := by
  rw [h_swap, h_e_ed F F' hP b a]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, Ne.symm hab]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem h_ed_ed (a b : Fin r) : S.hT (ed F F' a) (ed F F' b) = 0 := by
  simp [ed, hl_sum, hr_sum, hl_smul, hr_smul, F'.e_iso]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem h_ed_zp (a : Fin r) : S.hT (ed F F' a) F'.z = 0 := by
  simp [ed, hl_sum, hl_smul, F'.z_orth]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem h_zp_ed (a : Fin r) : S.hT F'.z (ed F F' a) = 0 := by
  exact h_zero_swap _ (h_ed_zp F F' a)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem h_z_e (a : Fin r) : S.hT F.z (F.e a) = 0 := by
  exact h_zero_swap _ (F.z_orth a)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem h_v_v (hP : (Pm F F').det ≠ 0) (a b : Fin r) :
    S.hT (vv F F' a) (vv F F' b) = if a = b then -2 else 0 := by
  unfold vv
  rw [hl_sub, hr_sub, hr_sub, F.e_iso, h_e_ed F F' hP, h_ed_e F F' hP, h_ed_ed]
  split_ifs <;> ring

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem h_ed_zt (hP : (Pm F F').det ≠ 0) (b : Fin r) : S.hT (ed F F' b) (zt F F') = 0 := by
  unfold zt
  rw [hr_sub, hr_sum]
  simp only [hr_smul, h_ed_e F F' hP]
  simp [cz]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem h_e_zt (b : Fin r) : S.hT (F.e b) (zt F F') = 0 := by
  simp [zt, hr_sub, hr_sum, hr_smul, F.z_orth, F.e_iso]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation.
-/
theorem h_zt_zt : S.hT (zt F F') (zt F F') = -(T : E) := by
  have h1 : S.hT (∑ a, cz F F' a • F.e a) (zt F F') = 0 := by
    simp [hl_sum, hl_smul, h_e_zt]
  have h2 : S.hT F.z (zt F F') = -(T : E) := by
    simp [zt, hr_sub, hr_sum, hr_smul, h_z_e, F.z_norm]
  calc S.hT (zt F F') (zt F F')
      = S.hT F.z (zt F F') - S.hT (∑ a, cz F F' a • F.e a) (zt F F') := hl_sub S _ _ _
    _ = -(T : E) := by rw [h1, h2, sub_zero]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem h_e_zt' (hP : (Pm F F').det ≠ 0) (b : Fin r) : S.hT (F.e b) (zt' F F') = 0 := by
  unfold zt'
  rw [hr_sub, hr_sum]
  simp only [hr_smul, h_e_ed F F' hP]
  simp [cz']

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem h_ed_zt' (b : Fin r) : S.hT (ed F F' b) (zt' F F') = 0 := by
  simp [zt', hr_sub, hr_sum, hr_smul, h_ed_zp, h_ed_ed]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation.
-/
theorem h_zt'_zt' : S.hT (zt' F F') (zt' F F') = -(T' : E) := by
  have h1 : S.hT (∑ a, cz' F F' a • ed F F' a) (zt' F F') = 0 := by
    simp [hl_sum, hl_smul, h_ed_zt']
  have h2 : S.hT F'.z (zt' F F') = -(T' : E) := by
    simp [zt', hr_sub, hr_sum, hr_smul, h_zp_ed, F'.z_norm]
  calc S.hT (zt' F F') (zt' F F')
      = S.hT F'.z (zt' F F') - S.hT (∑ a, cz' F F' a • ed F F' a) (zt' F F') := hl_sub S _ _ _
    _ = -(T' : E) := by rw [h1, h2, sub_zero]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem h_v_zt (hP : (Pm F F').det ≠ 0) (a : Fin r) : S.hT (vv F F' a) (zt F F') = 0 := by
  simp [vv, hl_sub, h_e_zt, h_ed_zt F F' hP]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem h_v_zt' (hP : (Pm F F').det ≠ 0) (a : Fin r) : S.hT (vv F F' a) (zt' F F') = 0 := by
  simp [vv, hl_sub, h_e_zt' F F' hP, h_ed_zt']

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem hermForm_anisotropic_orth_second (hT : (T : E) ≠ 0) : S.hT (zt F F') (zt2 F F') = 0 := by
  unfold zt2
  rw [hr_add, hr_smul, h_zt_zt]
  have h1 : beta F F' / (T : E) * -(T : E) = -beta F F' := by
    rw [mul_neg, div_mul_cancel₀ _ hT]
  rw [h1]
  simp [beta]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hermForm_vector_orth_second (hP : (Pm F F').det ≠ 0) (a : Fin r) : S.hT (vv F F' a) (zt2 F F') = 0 := by
  simp [zt2, hr_add, hr_smul, h_v_zt F F' hP, h_v_zt' F F' hP]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermForm_second_anisotropic (hT : (T : E) ≠ 0) :
    S.hT (zt2 F F') (zt2 F F') = -(T' : E) + beta F F' * star (beta F F') / (T : E) := by
  have hb : S.hT (zt' F F') (zt F F') = star (beta F F') := h_swap S (zt F F') (zt' F F')
  have hb' : S.hT (zt F F') (zt' F F') = beta F F' := rfl
  unfold zt2
  rw [hl_add, hl_smul, hr_add, hr_add, hr_smul, hr_smul, h_zt'_zt', h_zt_zt, hb, hb',
    star_div₀, star_natCast]
  field_simp
  ring

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem zp_eq : F'.z = zt' F F' + ∑ c, (∑ a, cz' F F' a * (Pm F F')⁻¹ c a) • F'.e c := by
  have hX : ∑ a, cz' F F' a • ed F F' a
      = ∑ c, (∑ a, cz' F F' a * (Pm F F')⁻¹ c a) • F'.e c := by
    simp only [ed, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
  show F'.z = (F'.z - ∑ a, cz' F F' a • ed F F' a) + _
  rw [hX, sub_add_cancel]

end Flags

end PI.CntNotPosW
