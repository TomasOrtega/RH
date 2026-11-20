import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementB
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.EvalSecondZeroAtVariableZero
import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LogarithmEquivalence

noncomputable section

namespace Formalism.L2.Th1.B.Jets

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3)
open Formalism.G.LogP (hs2 psubst_subst constantCoeff_subst_of_zero psubst_injective)

section Alg

variable {K : Type} [Field K] [CharZero K]

/- English proof (translation)
Establish `h` using `PowerSeries.coeff_derivative l 0`. Simplify `h` using `[h1]`.
-/
theorem cc_dz {l : PowerSeries K} (h1 : PowerSeries.coeff 1 l = 1) :
    PowerSeries.constantCoeff (dz l) = 1 := by
  have h := PowerSeries.coeff_derivative l 0
  simpa [h1] using h

/- English proof (translation)
The claim follows from `PowerSeries.inv_mul_cancel _ (by rw [cc_dz h1]; exact one_ne_zero)`.
-/
theorem inv_mul_dz {l : PowerSeries K} (h1 : PowerSeries.coeff 1 l = 1) :
    (dz l)⁻¹ * dz l = 1 := PowerSeries.inv_mul_cancel _ (by rw [cc_dz h1]; exact one_ne_zero)

/- English proof (translation)
Conclude with `MvPowerSeries.constantCoeff_X i`.
-/
theorem ccX {ι : Type} (i : ι) :
    MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries ι K) = 0 := by
  exact MvPowerSeries.constantCoeff_X i

/- English proof (translation)
Establish `hs : PowerSeries.HasSubst U` using `PowerSeries.HasSubst.of_constantCoeff_zero hU`. Rewrite using `[← PowerSeries.coe_substAlgHom hs, ← map_mul, inv_mul_dz h1, map_one]`.
-/
theorem inv_mul_dz_subst {ι : Type} {l : PowerSeries K} (h1 : PowerSeries.coeff 1 l = 1)
    {U : MvPowerSeries ι K} (hU : MvPowerSeries.constantCoeff U = 0) :
    PowerSeries.subst U (dz l)⁻¹ * PowerSeries.subst U (dz l) = 1 := by
  have hs : PowerSeries.HasSubst U := PowerSeries.HasSubst.of_constantCoeff_zero hU
  rw [← PowerSeries.coe_substAlgHom hs, ← map_mul, inv_mul_dz h1, map_one]

def Dj (l : PowerSeries K) (j : Fin 3) (g : MvPowerSeries (Fin 3) K) : MvPowerSeries (Fin 3) K :=
  at1 j (dz l)⁻¹ * pd j g

/- English proof (translation)
Simplify using `only [Dj, pd, map_sub, mul_sub]`.
-/
theorem Dj_sub (l : PowerSeries K) (j : Fin 3) (a b : MvPowerSeries (Fin 3) K) :
    Dj l j (a - b) = Dj l j a - Dj l j b := by
  simp only [Dj, pd, map_sub, mul_sub]

/- English proof (translation)
Establish `hinv` using `inv_mul_dz_subst h1 hU`. Simplify using `only [dz] at hinv`. Simplify using `only [Dj, pd, Dinv, dz]`. Rewrite using `[Formalism.G.LogCR.pderiv_psubst hU, Formalism.G.LogCR.pderiv_psubst hU, PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero hU)]`. Take the linear combination `(-(at1 j (PowerSeries.derivative K l)⁻¹ * PowerSeries.subst U (PowerSeries.derivative K g) * MvPowerSeries.pderiv K j U)) * hinv`.
-/
theorem Dj_psubst {l : PowerSeries K} (h1 : PowerSeries.coeff 1 l = 1) (j : Fin 3)
    (g : PowerSeries K) {U : MvPowerSeries (Fin 3) K} (hU : MvPowerSeries.constantCoeff U = 0) :
    Dj l j (PowerSeries.subst U g) =
      PowerSeries.subst U (Dinv l g) * (at1 j (dz l)⁻¹ * pd j (PowerSeries.subst U l)) := by
  have hinv := inv_mul_dz_subst h1 hU
  simp only [dz] at hinv
  simp only [Dj, pd, Dinv, dz]
  rw [Formalism.G.LogCR.pderiv_psubst hU, Formalism.G.LogCR.pderiv_psubst hU,
    PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero hU)]
  linear_combination (-(at1 j (PowerSeries.derivative K l)⁻¹ *
    PowerSeries.subst U (PowerSeries.derivative K g) * MvPowerSeries.pderiv K j U)) * hinv

/- English proof (translation)
Establish `hX : MvPowerSeries.constantCoeff (MvPowerSeries.X k : MvPowerSeries (Fin 3) K) = 0` using `ccX k`. Simplify using `only [pd]`. Rewrite using `[Formalism.G.LogCR.pderiv_psubst hX]`. Distinguish the cases in `hkj : k = j`. Substitute `hkj` using the available equality.

Rewrite using `[MvPowerSeries.pderiv_X_self, mul_one, if_pos rfl]`. Conclude with `inv_mul_dz_subst h1 hX`. Rewrite using `[MvPowerSeries.pderiv_X_of_ne hkj, mul_zero, mul_zero, if_neg hkj]`.
-/
theorem key {l : PowerSeries K} (h1 : PowerSeries.coeff 1 l = 1) (j k : Fin 3) :
    at1 j (dz l)⁻¹ * pd j (PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries (Fin 3) K) l) =
      if k = j then 1 else 0 := by
  have hX : MvPowerSeries.constantCoeff (MvPowerSeries.X k : MvPowerSeries (Fin 3) K) = 0 := ccX k
  simp only [pd]
  rw [Formalism.G.LogCR.pderiv_psubst hX]
  by_cases hkj : k = j
  · subst hkj
    rw [MvPowerSeries.pderiv_X_self, mul_one, if_pos rfl]
    exact inv_mul_dz_subst h1 hX
  · rw [MvPowerSeries.pderiv_X_of_ne hkj, mul_zero, mul_zero, if_neg hkj]

/- English proof (translation)
Establish `hAB : MvPowerSeries.HasSubst ![A, B]` using `hs2 hA hB`. Simplify using `only [cob, at1]`. Rewrite using `[MvPowerSeries.subst_sub hAB, MvPowerSeries.subst_sub hAB, psubst_subst f hF hAB, psubst_subst f (MvPowerSeries.constantCoeff_X 0) hAB, psubst_subst f (MvPowerSeries.constantCoeff_X 1) hAB, MvPowerSeries.subst_X hAB, MvPowerSeries.subst_X hAB]`. Simplify using the standard rewrite rules.
-/
theorem cob_subst {ι : Type} {F : MvPowerSeries (Fin 2) K}
    (hF : MvPowerSeries.constantCoeff F = 0) (f : PowerSeries K) {A B : MvPowerSeries ι K}
    (hA : MvPowerSeries.constantCoeff A = 0) (hB : MvPowerSeries.constantCoeff B = 0) :
    MvPowerSeries.subst ![A, B] (cob F f) =
      PowerSeries.subst (MvPowerSeries.subst ![A, B] F) f - PowerSeries.subst A f -
        PowerSeries.subst B f := by
  have hAB : MvPowerSeries.HasSubst ![A, B] := hs2 hA hB
  simp only [cob, at1]
  rw [MvPowerSeries.subst_sub hAB, MvPowerSeries.subst_sub hAB, psubst_subst f hF hAB,
    psubst_subst f (MvPowerSeries.constantCoeff_X 0) hAB,
    psubst_subst f (MvPowerSeries.constantCoeff_X 1) hAB,
    MvPowerSeries.subst_X hAB, MvPowerSeries.subst_X hAB]
  simp

/- English proof (translation)
Establish `e` using `cob_subst hF l hA hB`. Rewrite `e` using `[hc, Formalism.G.LogP.subst_zero' (hs2 hA hB)]`. Take the linear combination `-e`.
-/
theorem law_subst {ι : Type} {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K}
    (hF : MvPowerSeries.constantCoeff F = 0) (hc : cob F l = 0) {A B : MvPowerSeries ι K}
    (hA : MvPowerSeries.constantCoeff A = 0) (hB : MvPowerSeries.constantCoeff B = 0) :
    PowerSeries.subst (MvPowerSeries.subst ![A, B] F) l =
      PowerSeries.subst A l + PowerSeries.subst B l := by
  have e := cob_subst hF l hA hB
  rw [hc, Formalism.G.LogP.subst_zero' (hs2 hA hB)] at e
  linear_combination -e

/- English proof (translation)
The claim follows from `MvPowerSeries.constantCoeff_subst_eq_zero (hs2 hA hB) (fun i => by fin_cases i <;> simp [hA, hB]) hF`.
-/
theorem cc_law {ι : Type} {F : MvPowerSeries (Fin 2) K}
    (hF : MvPowerSeries.constantCoeff F = 0) {A B : MvPowerSeries ι K}
    (hA : MvPowerSeries.constantCoeff A = 0) (hB : MvPowerSeries.constantCoeff B = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst ![A, B] F) = 0 := MvPowerSeries.constantCoeff_subst_eq_zero (hs2 hA hB)
    (fun i => by fin_cases i <;> simp [hA, hB]) hF

def U2 (F : MvPowerSeries (Fin 2) K) (a b : Fin 3) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![(MvPowerSeries.X a : MvPowerSeries (Fin 3) K), MvPowerSeries.X b] F

def U3 (F : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![U2 F 0 1, MvPowerSeries.X 2] F

/- English proof (translation)
Unfold `U2`. Conclude with `cc_law hF (ccX a) (ccX b)`.
-/
theorem constantCoeff_law_pair {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (a b : Fin 3) : MvPowerSeries.constantCoeff (U2 F a b) = 0 := by
  unfold U2
  exact cc_law hF (ccX a) (ccX b)

/- English proof (translation)
Unfold `U3`. Conclude with `cc_law hF (constantCoeff_law_pair hF 0 1) (ccX 2)`.
-/
theorem constantCoeff_law_three {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (U3 F) = 0 := by
  unfold U3
  exact cc_law hF (constantCoeff_law_pair hF 0 1) (ccX 2)

/- English proof (translation)
Establish `e : in3 F = U2 F 0 1` using `rfl`. Simplify using `only [d1]`. Rewrite using `[e, cob_subst hF f (constantCoeff_law_pair hF 0 1) (ccX 2), cob_subst hF f (ccX 0) (ccX 2), cob_subst hF f (ccX 1) (ccX 2)]`. Both sides reduce to the same expression.
-/
theorem coboundary_formal_add_biextension {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f : PowerSeries K) :
    d1 F (cob F f) =
      PowerSeries.subst (U3 F) f - PowerSeries.subst (U2 F 0 1) f -
          PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) f -
        (PowerSeries.subst (U2 F 0 2) f -
          PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) f -
          PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) f) -
        (PowerSeries.subst (U2 F 1 2) f -
          PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) f -
          PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) f) := by
  have e : in3 F = U2 F 0 1 := rfl
  simp only [d1]
  rw [e, cob_subst hF f (constantCoeff_law_pair hF 0 1) (ccX 2), cob_subst hF f (ccX 0) (ccX 2),
    cob_subst hF f (ccX 1) (ccX 2)]
  rfl

section Steps

variable {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K}

/- English proof (translation)
Rewrite using `[Dj_psubst h1 j g (ccX k), key h1 j k]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem Dj_X (h1 : PowerSeries.coeff 1 l = 1) (j k : Fin 3) (g : PowerSeries K) :
    Dj l j (PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries (Fin 3) K) g) =
      if k = j then PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries (Fin 3) K) (Dinv l g)
      else 0 := by
  rw [Dj_psubst h1 j g (ccX k), key h1 j k]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[Dj_psubst h1 j g (constantCoeff_law_pair hF a b)]`. Establish `hl : PowerSeries.subst (U2 F a b) l = PowerSeries.subst (MvPowerSeries.X a : MvPowerSeries (Fin 3) K) l + PowerSeries.subst (MvPowerSeries.X b : MvPowerSeries (Fin 3) K) l` using `law_subst hF hc (ccX a) (ccX b)`. Establish `ka` using `key h1 j a`. Establish `kb` using `key h1 j b`. Simplify using `only [pd] at ka kb`.

Rewrite using `[hl]`. Simplify using `only [pd, map_add, mul_add]`. Rewrite using `[ka, kb]`. Apply the tactic sequence `rcases eq_or_ne a j with ha | ha <;> rcases eq_or_ne b j with hb | hb`. Conclude with `absurd (ha.trans hb.symm) hab`.

Simplify using `[ha, hb]`. Simplify using `[ha, hb]`. Simplify using `[ha, hb]`.
-/
theorem invariant_derivation_subst_law_pair (hF : MvPowerSeries.constantCoeff F = 0) (hc : cob F l = 0)
    (h1 : PowerSeries.coeff 1 l = 1) (j a b : Fin 3) (hab : a ≠ b) (g : PowerSeries K) :
    Dj l j (PowerSeries.subst (U2 F a b) g) =
      if a = j ∨ b = j then PowerSeries.subst (U2 F a b) (Dinv l g) else 0 := by
  rw [Dj_psubst h1 j g (constantCoeff_law_pair hF a b)]
  have hl : PowerSeries.subst (U2 F a b) l =
      PowerSeries.subst (MvPowerSeries.X a : MvPowerSeries (Fin 3) K) l +
        PowerSeries.subst (MvPowerSeries.X b : MvPowerSeries (Fin 3) K) l :=
    law_subst hF hc (ccX a) (ccX b)
  have ka := key h1 j a
  have kb := key h1 j b
  simp only [pd] at ka kb
  rw [hl]
  simp only [pd, map_add, mul_add]
  rw [ka, kb]
  rcases eq_or_ne a j with ha | ha <;> rcases eq_or_ne b j with hb | hb
  · exact absurd (ha.trans hb.symm) hab
  · simp [ha, hb]
  · simp [ha, hb]
  · simp [ha, hb]

/- English proof (translation)
Rewrite using `[Dj_psubst h1 j g (constantCoeff_law_three hF)]`. Establish `e1 : PowerSeries.subst (U3 F) l = PowerSeries.subst (U2 F 0 1) l + PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) l`. Unfold `U3`. Conclude with `law_subst hF hc (constantCoeff_law_pair hF 0 1) (ccX 2)`. Establish `e2 : PowerSeries.subst (U2 F 0 1) l = PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) l + PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) l` using `law_subst hF hc (ccX 0) (ccX 1)`.

Establish `k0` using `key h1 j 0`. Establish `k1` using `key h1 j 1`. Establish `k2` using `key h1 j 2`. Simplify using `only [pd] at k0 k1 k2`. Rewrite using `[e1, e2]`.

Simplify using `only [pd, map_add, mul_add]`. Rewrite using `[k0, k1, k2]`. Apply the tactic sequence `have hsum : ((if (0 : Fin 3) = j then 1 else 0) + (if (1 : Fin 3) = j then 1 else 0) + (if (2 : Fin 3) = j then 1 else 0) : MvPowerSeries (Fin 3) K) = 1 := by fin_cases j <;> simp`. Rewrite using `[← mul_add, ← mul_add, hsum, mul_one]`.
-/
theorem invariant_derivation_subst_law_three (hF : MvPowerSeries.constantCoeff F = 0) (hc : cob F l = 0)
    (h1 : PowerSeries.coeff 1 l = 1) (j : Fin 3) (g : PowerSeries K) :
    Dj l j (PowerSeries.subst (U3 F) g) = PowerSeries.subst (U3 F) (Dinv l g) := by
  rw [Dj_psubst h1 j g (constantCoeff_law_three hF)]
  have e1 : PowerSeries.subst (U3 F) l =
      PowerSeries.subst (U2 F 0 1) l +
        PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) l := by
    unfold U3
    exact law_subst hF hc (constantCoeff_law_pair hF 0 1) (ccX 2)
  have e2 : PowerSeries.subst (U2 F 0 1) l =
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) l +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) l :=
    law_subst hF hc (ccX 0) (ccX 1)
  have k0 := key h1 j 0
  have k1 := key h1 j 1
  have k2 := key h1 j 2
  simp only [pd] at k0 k1 k2
  rw [e1, e2]
  simp only [pd, map_add, mul_add]
  rw [k0, k1, k2]
  have hsum : ((if (0 : Fin 3) = j then 1 else 0) + (if (1 : Fin 3) = j then 1 else 0) +
      (if (2 : Fin 3) = j then 1 else 0) : MvPowerSeries (Fin 3) K) = 1 := by
    fin_cases j <;> simp
  rw [← mul_add, ← mul_add, hsum, mul_one]

/- English proof (translation)
Rewrite using `[coboundary_formal_add_biextension hF f]`. Simplify using `only [Dj_sub, invariant_derivation_subst_law_three hF hc h1, Dj_X h1]`. Rewrite using `[invariant_derivation_subst_law_pair hF hc h1 2 0 1 (by decide), invariant_derivation_subst_law_pair hF hc h1 2 0 2 (by decide), invariant_derivation_subst_law_pair hF hc h1 2 1 2 (by decide)]`. Simplify using the standard rewrite rules.
-/
theorem step2 (hF : MvPowerSeries.constantCoeff F = 0) (hc : cob F l = 0)
    (h1 : PowerSeries.coeff 1 l = 1) (f : PowerSeries K) :
    Dj l 2 (d1 F (cob F f)) =
      PowerSeries.subst (U3 F) (Dinv l f) - PowerSeries.subst (U2 F 0 2) (Dinv l f) -
        (PowerSeries.subst (U2 F 1 2) (Dinv l f) -
          PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) (Dinv l f)) := by
  rw [coboundary_formal_add_biextension hF f]
  simp only [Dj_sub, invariant_derivation_subst_law_three hF hc h1, Dj_X h1]
  rw [invariant_derivation_subst_law_pair hF hc h1 2 0 1 (by decide), invariant_derivation_subst_law_pair hF hc h1 2 0 2 (by decide),
    invariant_derivation_subst_law_pair hF hc h1 2 1 2 (by decide)]
  simp

/- English proof (translation)
Simplify using `only [Dj_sub, invariant_derivation_subst_law_three hF hc h1, Dj_X h1]`. Rewrite using `[invariant_derivation_subst_law_pair hF hc h1 1 0 2 (by decide), invariant_derivation_subst_law_pair hF hc h1 1 1 2 (by decide)]`. Simplify using the standard rewrite rules.
-/
theorem step1 (hF : MvPowerSeries.constantCoeff F = 0) (hc : cob F l = 0)
    (h1 : PowerSeries.coeff 1 l = 1) (g : PowerSeries K) :
    Dj l 1 (PowerSeries.subst (U3 F) g - PowerSeries.subst (U2 F 0 2) g -
        (PowerSeries.subst (U2 F 1 2) g -
          PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) g)) =
      PowerSeries.subst (U3 F) (Dinv l g) - PowerSeries.subst (U2 F 1 2) (Dinv l g) := by
  simp only [Dj_sub, invariant_derivation_subst_law_three hF hc h1, Dj_X h1]
  rw [invariant_derivation_subst_law_pair hF hc h1 1 0 2 (by decide), invariant_derivation_subst_law_pair hF hc h1 1 1 2 (by decide)]
  simp

/- English proof (translation)
Simplify using `only [Dj_sub, invariant_derivation_subst_law_three hF hc h1]`. Rewrite using `[invariant_derivation_subst_law_pair hF hc h1 0 1 2 (by decide)]`. Simplify using the standard rewrite rules.
-/
theorem step0 (hF : MvPowerSeries.constantCoeff F = 0) (hc : cob F l = 0)
    (h1 : PowerSeries.coeff 1 l = 1) (g : PowerSeries K) :
    Dj l 0 (PowerSeries.subst (U3 F) g - PowerSeries.subst (U2 F 1 2) g) =
      PowerSeries.subst (U3 F) (Dinv l g) := by
  simp only [Dj_sub, invariant_derivation_subst_law_three hF hc h1]
  rw [invariant_derivation_subst_law_pair hF hc h1 0 1 2 (by decide)]
  simp

/- English proof (translation)
Establish `base : Dj l 0 (Dj l 1 (Dj l 2 (d1 F (cob F f)))) = PowerSeries.subst (U3 F) ((Dinv l)^[3] f)`. Rewrite using `[step2 hF hc h1 f, step1 hF hc h1, step0 hF hc h1]`. Both sides reduce to the same expression. Proceed by induction on `k with`. Consider the case `zero => exact base`.

Consider the case `succ k ih`. Rewrite using `[Function.iterate_succ_apply' (Dj l 0), ih, invariant_derivation_subst_law_three hF hc h1]`. Use `congr 1`. Rewrite using `[show k + 1 + 3 = (k + 3) + 1 by omega]`. Conclude with `(Function.iterate_succ_apply' (Dinv l) (k + 3) f).symm`.
-/
theorem chain (hF : MvPowerSeries.constantCoeff F = 0) (hc : cob F l = 0)
    (h1 : PowerSeries.coeff 1 l = 1) (f : PowerSeries K) (k : ℕ) :
    (Dj l 0)^[k] (Dj l 0 (Dj l 1 (Dj l 2 (d1 F (cob F f))))) =
      PowerSeries.subst (U3 F) ((Dinv l)^[k + 3] f) := by
  have base : Dj l 0 (Dj l 1 (Dj l 2 (d1 F (cob F f)))) =
      PowerSeries.subst (U3 F) ((Dinv l)^[3] f) := by
    rw [step2 hF hc h1 f, step1 hF hc h1, step0 hF hc h1]
    rfl
  induction k with
  | zero => exact base
  | succ k ih =>
    rw [Function.iterate_succ_apply' (Dj l 0), ih, invariant_derivation_subst_law_three hF hc h1]
    congr 1
    rw [show k + 1 + 3 = (k + 3) + 1 by omega]
    exact (Function.iterate_succ_apply' (Dinv l) (k + 3) f).symm

/- English proof (translation)
Establish `hs` using `PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_law_three hF)`. Establish `hg : g = PowerSeries.C (PowerSeries.constantCoeff g) + (g - PowerSeries.C (PowerSeries.constantCoeff g))` using `by ring`. Establish `h0 : PowerSeries.constantCoeff (g - PowerSeries.C (PowerSeries.constantCoeff g)) = 0`. Simplify using the standard rewrite rules. Use `conv_lhs => rw [hg]`.

Rewrite using `[PowerSeries.subst_add hs, PowerSeries.subst_C, map_add, MvPowerSeries.constantCoeff_C, PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_law_three hF) _ h0, add_zero]`.
-/
theorem constantCoeff_subst_law_three (hF : MvPowerSeries.constantCoeff F = 0) (g : PowerSeries K) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (U3 F) g) = PowerSeries.constantCoeff g := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_law_three hF)
  have hg : g = PowerSeries.C (PowerSeries.constantCoeff g) +
      (g - PowerSeries.C (PowerSeries.constantCoeff g)) := by ring
  have h0 : PowerSeries.constantCoeff (g - PowerSeries.C (PowerSeries.constantCoeff g)) = 0 := by
    simp
  conv_lhs => rw [hg]
  rw [PowerSeries.subst_add hs, PowerSeries.subst_C, map_add, MvPowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_law_three hF) _ h0, add_zero]

/- English proof (translation)
Establish `hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0` using `PowerSeries.constantCoeff_X`. Establish `hz : MvPowerSeries.constantCoeff (0 : PowerSeries K) = 0` using `map_zero _`. Establish `hev : ev0 F = PowerSeries.X`. Establish `hl` using `law_subst hF hc hX hz`. Apply `psubst_injective h0 h1 (cc_law hF hX hz) hX` to reduce the goal to its premises.

Rewrite using `[hl, PowerSeries.subst_zero_of_constantCoeff_zero h0, add_zero]`. Establish `hcob : PowerSeries.subst F l = at1 0 l + at1 1 l`. Establish `e` using `hc`. Simplify using `only [cob] at e`. Take the linear combination `e`.

Establish `hd` using `congrArg (MvPowerSeries.pderiv K 1) hcob`. Simplify using `only [at1] at hd`. Rewrite `hd` using `[Formalism.G.LogCR.pderiv_psubst hF, map_add, Formalism.G.LogCR.pderiv_psubst (ccX (0 : Fin 2)), Formalism.G.LogCR.pderiv_psubst (ccX (1 : Fin 2)), MvPowerSeries.pderiv_X_of_ne (by decide), MvPowerSeries.pderiv_X_self, mul_zero, zero_add, mul_one]`. Establish `he` using `congrArg ev0 hd`. Establish `w` using `restrictSecondZero_inVar_one (K := K) (dz l)`.

Establish `c1` using `cc_dz h1`. Simplify using `only [at1, dz] at w c1`. Rewrite `he` using `[evalYZero_mul, evalYZero_subst _ hF, hev, w, c1, map_one]`. Rewrite `he` using `[PowerSeries.X_subst]`. Use `symm`.

Rewrite using `[PowerSeries.eq_inv_iff_mul_eq_one (by rw [cc_dz h1]; exact one_ne_zero)]`. Simplify using `only [pd, dz]`. Rewrite using `[mul_comm]`. Conclude with `he`.
-/
theorem inv_dz_eq (hF : MvPowerSeries.constantCoeff F = 0) (hc : cob F l = 0)
    (h0 : PowerSeries.constantCoeff l = 0) (h1 : PowerSeries.coeff 1 l = 1) :
    (dz l)⁻¹ = ev0 (pd 1 F) := by
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0 :=
    PowerSeries.constantCoeff_X
  have hz : MvPowerSeries.constantCoeff (0 : PowerSeries K) = 0 := map_zero _
  have hev : ev0 F = PowerSeries.X := by
    have hl := law_subst hF hc hX hz
    apply psubst_injective h0 h1 (cc_law hF hX hz) hX
    rw [hl,
      PowerSeries.subst_zero_of_constantCoeff_zero h0, add_zero]
  have hcob : PowerSeries.subst F l = at1 0 l + at1 1 l := by
    have e := hc
    simp only [cob] at e
    linear_combination e
  have hd := congrArg (MvPowerSeries.pderiv K 1) hcob
  simp only [at1] at hd
  rw [Formalism.G.LogCR.pderiv_psubst hF, map_add, Formalism.G.LogCR.pderiv_psubst (ccX (0 : Fin 2)),
    Formalism.G.LogCR.pderiv_psubst (ccX (1 : Fin 2)), MvPowerSeries.pderiv_X_of_ne (by decide),
    MvPowerSeries.pderiv_X_self, mul_zero, zero_add, mul_one] at hd
  have he := congrArg ev0 hd
  have w := restrictSecondZero_inVar_one (K := K) (dz l)
  have c1 := cc_dz h1
  simp only [at1, dz] at w c1
  rw [evalYZero_mul, evalYZero_subst _ hF, hev, w, c1, map_one] at he
  rw [PowerSeries.X_subst] at he
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by rw [cc_dz h1]; exact one_ne_zero)]
  simp only [pd, dz]
  rw [mul_comm]
  exact he

end Steps

end Alg

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

/- English proof (translation)
Introduce `n`. Simplify using `only [pd]`. Rewrite using `[MvPowerSeries.coeff_pderiv, norm_mul]`. Establish `hn : ‖((n j : K) + 1)‖ ≤ 1`. Conclude with `IsUltrametricDist.norm_natCast_le_one K (n j + 1)` after adjusting the coercions.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem integral_pd {ι : Type} (j : ι) {f : MvPowerSeries ι K} (hf : Integral f) :
    Integral (pd j f) := by
  intro n
  simp only [pd]
  rw [MvPowerSeries.coeff_pderiv, norm_mul]
  have hn : ‖((n j : K) + 1)‖ ≤ 1 := by
    exact_mod_cast IsUltrametricDist.norm_natCast_le_one K (n j + 1)
  calc _ ≤ 1 * 1 := mul_le_mul (hf _) hn (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/- English proof (translation)
Introduce `n`. Rewrite using `[MvPowerSeries.coeff_X]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem integral_X {ι : Type} (x : ι) : Integral (MvPowerSeries.X x : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

/- English proof (translation)
Introduce `n`. Rewrite using `[Finsupp.unique_single n]`. Use `show ‖PowerSeries.coeff (n default) (ev0 h)‖ ≤ 1`. Rewrite using `[coeff_evalYZero]`. Conclude with `hh _`.
-/
theorem integral_eval_second_zero {h : MvPowerSeries (Fin 2) K} (hh : Integral h) :
    Integral (ι := Unit) (ev0 h) := by
  intro n
  rw [Finsupp.unique_single n]
  show ‖PowerSeries.coeff (n default) (ev0 h)‖ ≤ 1
  rw [coeff_evalYZero]
  exact hh _

/- English proof (translation)
Rewrite using `[inv_dz_eq h.1 h.2.2.2.2 h.2.2.1 h.2.2.2.1]`. Conclude with `Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (φ := fun _ : Unit => (MvPowerSeries.X j : MvPowerSeries (Fin 3) K)) (fun _ => ccX j) (fun _ => integral_X j) (integral_eval_second_zero (integral_pd 1 h.2.1))`.
-/
theorem integral_om {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (j : Fin 3) : Integral (at1 j (dz l)⁻¹) := by
  rw [inv_dz_eq h.1 h.2.2.2.2 h.2.2.1 h.2.2.2.1]
  exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst'
    (φ := fun _ : Unit => (MvPowerSeries.X j : MvPowerSeries (Fin 3) K))
    (fun _ => ccX j) (fun _ => integral_X j) (integral_eval_second_zero (integral_pd 1 h.2.1))

/- English proof (translation)
The claim follows from `Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' (integral_om h j) hg`.
-/
theorem integral_Dj {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (j : Fin 3) {g : MvPowerSeries (Fin 3) K} (hg : Integral (pd j g)) : Integral (Dj l j g) := Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' (integral_om h j) hg

/- English proof (translation)
Take `⟨hc0, hE⟩` from `hT`. Rewrite `hc0`, `hE` using `[sub_zero]`. Establish `hneg : MvPowerSeries.constantCoeff (-T) = 0` using `by rw [map_neg, hc0, neg_zero]`. Establish `hprod : mvExp (-T) * mvExp T = 1`. Establish `e` using `fExp_add hneg hc0`.

Rewrite `e` using `[neg_add_cancel]`. Express the relevant statement in the definitionally equal form `fExp (-T) * fExp T = 1`. Rewrite using `[← e]`. Conclude with `Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.mvExp_zero'`. Establish `hinvI : Integral (mvExp (-T))` using `Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_of_mul_eq_one hE (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.constantCoeff_mvExp' hc0) hprod`.

Establish `hpdT : pd j T = mvExp (-T) * pd j (mvExp T)`. Establish `hpd` using `pd_fExp j hc0`. Express the relevant statement in the definitionally equal form `pd j T = fExp (-T) * pd j (fExp T)`. Rewrite using `[hpd, ← mul_assoc]`. Express the relevant statement in the definitionally equal form `pd j T = mvExp (-T) * mvExp T * pd j T`.

Rewrite using `[hprod, one_mul]`. Rewrite using `[hpdT]`. Conclude with `Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' hinvI (integral_pd j hE)`.
-/
theorem integral_pd_of_simeq {ι : Type} [Finite ι] {T : MvPowerSeries ι K} (hT : Simeq T 0)
    (j : ι) : Integral (pd j T) := by
  obtain ⟨hc0, hE⟩ := hT
  rw [sub_zero] at hc0 hE
  have hneg : MvPowerSeries.constantCoeff (-T) = 0 := by rw [map_neg, hc0, neg_zero]
  have hprod : mvExp (-T) * mvExp T = 1 := by
    have e := fExp_add hneg hc0
    rw [neg_add_cancel] at e
    change fExp (-T) * fExp T = 1
    rw [← e]
    exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.mvExp_zero'
  have hinvI : Integral (mvExp (-T)) :=
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_of_mul_eq_one hE (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.constantCoeff_mvExp' hc0) hprod
  have hpdT : pd j T = mvExp (-T) * pd j (mvExp T) := by
    have hpd := pd_fExp j hc0
    change pd j T = fExp (-T) * pd j (fExp T)
    rw [hpd, ← mul_assoc]
    change pd j T = mvExp (-T) * mvExp T * pd j T
    rw [hprod, one_mul]
  rw [hpdT]
  exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' hinvI (integral_pd j hE)

/- English proof (translation)
Establish `step : ∀ (j : Fin 3) (g : MvPowerSeries (Fin 3) K), Integral g → Integral (Dj l j g)` using `fun j g hg => integral_Dj h j (integral_pd j hg)`. Establish `base : Integral (Dj l 0 (Dj l 1 (Dj l 2 T)))` using `step 0 _ (step 1 _ (integral_Dj h 2 (integral_pd_of_simeq hT 2)))`. Proceed by induction on `k with`. Consider the case `zero => exact base`. Consider the case `succ k ih`.

Rewrite using `[Function.iterate_succ_apply']`. Conclude with `step 0 _ ih`.
-/
theorem integral_chain {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    {T : MvPowerSeries (Fin 3) K} (hT : Simeq T 0) (k : ℕ) :
    Integral ((Dj l 0)^[k] (Dj l 0 (Dj l 1 (Dj l 2 T)))) := by
  have step : ∀ (j : Fin 3) (g : MvPowerSeries (Fin 3) K), Integral g → Integral (Dj l j g) :=
    fun j g hg => integral_Dj h j (integral_pd j hg)
  have base : Integral (Dj l 0 (Dj l 1 (Dj l 2 T))) :=
    step 0 _ (step 1 _ (integral_Dj h 2 (integral_pd_of_simeq hT 2)))
  induction k with
  | zero => exact base
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact step 0 _ ih

end Norm

/- English proof (translation)
Introduce `K _ _ _ F l f h hs n hn`. Take `⟨k, rfl⟩ : ∃ k, n = k + 3` from `⟨n - 3, by omega⟩`. Establish `hI` using `integral_chain h hs k`. Rewrite `hI` using `[chain h.1 h.2.2.2.2 h.2.2.2.1 f k]`. Establish `e` using `hI 0`.

Rewrite `e` using `[MvPowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_subst_law_three h.1]`. Conclude with `e`.
-/
theorem jets_three_variables_holds : JetsThree := by
  intro K _ _ _ F l f h hs n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hI := integral_chain h hs k
  rw [chain h.1 h.2.2.2.2 h.2.2.2.1 f k] at hI
  have e := hI 0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_subst_law_three h.1] at e
  exact e

end Formalism.L2.Th1.B.Jets
