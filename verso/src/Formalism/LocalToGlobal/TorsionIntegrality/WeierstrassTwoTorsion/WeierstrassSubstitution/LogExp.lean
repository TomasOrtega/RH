import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementZ
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementT

open PowerSeries

universe u

noncomputable section

namespace Formalism.L2.Th1.A

section SlopeTestRemainingChoices

variable {R : Type u} [CommRing R]

/- English proof (translation)
Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem subst_neg' {a : R⟦X⟧} (ha : HasSubst a) (f : R⟦X⟧) : (-f).subst a = -f.subst a := by
  first
    | (rw [← PowerSeries.coe_substAlgHom ha]; exact map_neg _ f)
    | simp [PowerSeries.subst_neg ha]

/- English proof (translation)
Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem subst_one' {a : R⟦X⟧} (ha : HasSubst a) : (1 : R⟦X⟧).subst a = 1 := by
  first
    | (rw [← PowerSeries.coe_substAlgHom ha]; exact map_one _)
    | simp

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
private theorem hasSubst_lemma {a : R⟦X⟧} (h : constantCoeff a = 0) : HasSubst a := by
  first
  | exact HasSubst.of_constantCoeff_zero' h
  | exact HasSubst.of_constantCoeff_zero h
  | exact PowerSeries.HasSubst.of_constantCoeff_zero' h

/- English proof (translation)
Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
private theorem powerSeries_subst_mul_of_hasSubst {a : R⟦X⟧} (ha : HasSubst a) (f g : R⟦X⟧) :
    (f * g).subst a = f.subst a * g.subst a := by
  first
  | exact PowerSeries.subst_mul ha f g
  | (rw [← PowerSeries.coe_substAlgHom ha]; exact map_mul _ f g)

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.
-/
private theorem constantCoeff_powerSeries_subst_eq_zero {a f : R⟦X⟧} (ha0 : constantCoeff a = 0) (hf : constantCoeff f = 0) :
    constantCoeff (f.subst a) = 0 := by
  obtain ⟨h, rfl⟩ := (PowerSeries.X_dvd_iff).mpr hf
  rw [powerSeries_subst_mul_of_hasSubst (hasSubst_lemma ha0), PowerSeries.subst_X (hasSubst_lemma ha0), map_mul, ha0, zero_mul]

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
private theorem powerSeries_subst_subst_eq_subst_subst {a b f : R⟦X⟧} (ha : HasSubst a) (hb : HasSubst b) :
    PowerSeries.subst b (PowerSeries.subst a f : R⟦X⟧)
      = PowerSeries.subst (PowerSeries.subst b a : R⟦X⟧) f := by
  first
  | exact PowerSeries.subst_comp_subst_apply ha hb f
  | exact (PowerSeries.subst_comp_subst_apply ha hb f).symm
  | rw [PowerSeries.subst_comp_subst_apply ha hb]

/- English proof (translation)
Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem subst_injective_of_leftInverse {l e a b : R⟦X⟧} (hl : HasSubst l) (ha : HasSubst a)
    (hb : HasSubst b) (hel : e.subst l = X) (h : l.subst a = l.subst b) : a = b := by
  calc a = e.subst (l.subst a) := by
        rw [← powerSeries_subst_subst_eq_subst_subst hl ha, hel, PowerSeries.subst_X ha]
    _ = e.subst (l.subst b) := by rw [h]
    _ = b := by rw [← powerSeries_subst_subst_eq_subst_subst hl hb, hel, PowerSeries.subst_X hb]

end SlopeTestRemainingChoices

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem logSpec_of (hI : IntegSpec.{u}) (hU : UnitSpec.{u}) : LogSpec.{u} := by
  intro K _ _ W
  obtain ⟨hc, hd, -⟩ := hI K (om W)
  obtain ⟨-, hfo, ho0, -⟩ := hU K W
  refine ⟨hc, ?_, hd, ?_⟩
  · simp only [logSer, integ, coeff_mk]
    simp [ho0]
  · simp only [D, logSer, Derivation.smul_apply, smul_eq_mul, hd, hfo]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem expSpec_of (hI : IntegSpec.{u}) (hC : CompInvSpec.{u}) (hU : UnitSpec.{u}) :
    ExpSpec.{u} := by
  intro K _ _ W
  obtain ⟨hL0, hL1, hLd, -⟩ := logSpec_of hI hU K W
  obtain ⟨-, hfo, -⟩ := hU K W
  obtain ⟨hE0, hLE, hEL, hcoef, -⟩ := hC K (logSer W) hL0 (by rw [hL1]; exact isUnit_one)
  have hE0' : constantCoeff (expSer W) = 0 := hE0
  have hLE' : (logSer W).subst (expSer W) = X := hLE
  have hs : HasSubst (expSer W) := hasSubst_lemma hE0'
  refine ⟨hE0, ?_, hLE, hEL, ?_⟩
  · have h : coeff 1 (expSer W) * coeff 1 (logSer W) = 1 := hcoef
    rwa [hL1, mul_one] at h
  · have h1 := congrArg (derivative K) hLE'
    rw [derivative_subst hs, hLd, derivative_X] at h1
    have h2 : (fw W).subst (expSer W) * (om W).subst (expSer W) = 1 := by
      rw [← powerSeries_subst_mul_of_hasSubst hs, hfo, subst_one' hs]
    calc derivative K (expSer W)
        = ((fw W).subst (expSer W) * (om W).subst (expSer W)) * derivative K (expSer W) := by
          rw [h2, one_mul]
      _ = (fw W).subst (expSer W) := by rw [mul_assoc, h1, mul_one]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities.
-/
theorem chainZ_of (hI : IntegSpec.{u}) (hC : CompInvSpec.{u}) (hU : UnitSpec.{u}) :
    ChainZ.{u} := by
  intro K _ _ W f
  obtain ⟨hE0, -, -, -, hEd⟩ := expSpec_of hI hC hU K W
  have hs : HasSubst (expSer W) := hasSubst_lemma hE0
  rw [derivative_subst hs, hEd]
  simp only [D, Derivation.smul_apply, smul_eq_mul]
  rw [powerSeries_subst_mul_of_hasSubst hs, mul_comm]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities.
-/
theorem logNeg_of (hI : IntegSpec.{u}) (hC : CompInvSpec.{u}) (hU : UnitSpec.{u})
    (hS : ISerSpec.{u}) : LogNeg.{u} := by
  intro K _ _ W
  obtain ⟨hL0, -, hLd, -⟩ := logSpec_of hI hU K W
  obtain ⟨hE0, -, hLE, hEL, -⟩ := expSpec_of hI hC hU K W
  obtain ⟨hi0, -, -, -, -, -, -, hiom⟩ := hS K W
  have hsi : HasSubst (iSer W) := hasSubst_lemma hi0
  have hsE : HasSubst (expSer W) := hasSubst_lemma hE0
  have hL' : (logSer W).subst (iSer W) = -logSer W := by
    obtain ⟨-, -, huniq⟩ := hI K (-om W)
    have e1 := huniq ((logSer W).subst (iSer W)) (constantCoeff_powerSeries_subst_eq_zero hi0 hL0)
      (by rw [derivative_subst hsi, hLd, hiom])
    have e2 := huniq (-logSer W) (by rw [map_neg, hL0, neg_zero]) (by rw [map_neg, hLd])
    rw [e1, e2]
  refine ⟨hL', ?_⟩
  have hnX0 : constantCoeff (-X : K⟦X⟧) = 0 := by simp
  have hsn : HasSubst (-X : K⟦X⟧) := hasSubst_lemma hnX0
  apply subst_injective_of_leftInverse (l := logSer W) (e := expSer W) (hasSubst_lemma hL0)
    (hasSubst_lemma (constantCoeff_powerSeries_subst_eq_zero hnX0 hE0)) (hasSubst_lemma (constantCoeff_powerSeries_subst_eq_zero hE0 hi0)) hEL
  rw [← powerSeries_subst_subst_eq_subst_subst hsE hsn, hLE, PowerSeries.subst_X hsn, ← powerSeries_subst_subst_eq_subst_subst hsi hsE, hL',
    subst_neg' hsE, hLE]

end Formalism.L2.Th1.A
