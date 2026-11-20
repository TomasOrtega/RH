import Formalism.HermitianCurvature.StatementQ
import Formalism.PeriodIntegrals.ContractionsCovariantIff
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmColExp
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowExp
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowForm
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmSkip
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmStar
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmIndep
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmLemD
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovLin
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovDet
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovHat
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CovariantHatSqOfLin
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnAdapted
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnEabGl
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnEabPres
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnFFZero
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnMinorLeft
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnRdSkew
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnRuleRight
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnVMonic
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylLevelElementProperties
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnYLeibniz
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnZeroLevel

/- English proof (translation)
The claim follows from `PI.QmColExpWork.expFirstCol`.
-/
theorem Formalism.FourierDecayAlt.P.expansion_first_column : Formalism.FourierDecayAlt.Q.ExpFirstCol := PI.QmColExpWork.expFirstCol

/- English proof (translation)
The claim follows from `PI.QmColExpWork.expLastCol`.
-/
theorem Formalism.FourierDecayAlt.P.expansion_last_column : Formalism.FourierDecayAlt.Q.ExpLastCol := PI.QmColExpWork.expLastCol

/- English proof (translation)
The claim follows from `PI.QmRowExpWork.expFirstRow_of quantum_minor_row_form`.
-/
theorem Formalism.FourierDecayAlt.P.expansion_first_line : Formalism.FourierDecayAlt.Q.ExpFirstRow := PI.QmRowExpWork.expFirstRow_of quantum_minor_row_form

/- English proof (translation)
The claim follows from `PI.QmRowExpWork.expLastRow_of quantum_minor_row_form`.
-/
theorem Formalism.FourierDecayAlt.P.expansion_last_line : Formalism.FourierDecayAlt.Q.ExpLastRow := PI.QmRowExpWork.expLastRow_of quantum_minor_row_form

/- English proof (translation)
The claim follows from `quantum_minor_row_form`.
-/
theorem Formalism.FourierDecayAlt.P.line_form_of_minor : Formalism.FourierDecayAlt.Q.RowForm := quantum_minor_row_form

/- English proof (translation)
The claim follows from `PI.QmSkipWork.skipSucc`.
-/
theorem Formalism.FourierDecayAlt.P.skip_succ_identity : Formalism.FourierDecayAlt.Q.SkipSucc := PI.QmSkipWork.skipSucc

/- English proof (translation)
The claim follows from `PI.QmSkipWork.skipSucc2`.
-/
theorem Formalism.FourierDecayAlt.P.skip_succ_double_identity : Formalism.FourierDecayAlt.Q.SkipSucc2 := PI.QmSkipWork.skipSucc2

/- English proof (translation)
The claim follows from `quantum_minor_star`.
-/
theorem Formalism.FourierDecayAlt.P.star_quantum_minor : Formalism.FourierDecayAlt.Q.StarMinor := quantum_minor_star

/- English proof (translation)
The claim follows from `rtt_independence'`.
-/
theorem Formalism.FourierDecayAlt.P.rtt_independence : Formalism.FourierDecayAlt.Q.RTTIndependence := rtt_independence'

/- English proof (translation)
The claim follows from `quantum_minor_D`.
-/
theorem Formalism.FourierDecayAlt.P.lemma_d_determinant_identity : Formalism.FourierDecayAlt.Q.LemmaD := quantum_minor_D

/- English proof (translation)
The claim follows from `PI.contractionsCovariant_iff.mpr ⟨covariant_det_of_lin covariant_linear, covariant_hat_of_lin covariant_linear, covariant_hat_sq_of_lin covariant_linear⟩`.
-/
theorem Formalism.FourierDecayAlt.P.contractions_covariant : Formalism.FourierDecayAlt.Q.ContractionsCovariant := PI.contractionsCovariant_iff.mpr ⟨covariant_det_of_lin covariant_linear, covariant_hat_of_lin covariant_linear, covariant_hat_sq_of_lin covariant_linear⟩

/- English proof (translation)
The claim follows from `(contraction_adapted Formalism.FourierDecayAlt.P.contractions_covariant).1`.
-/
theorem Formalism.FourierDecayAlt.P.first_contraction_adapted : Formalism.FourierDecayAlt.Q.ChatAdapted := (contraction_adapted Formalism.FourierDecayAlt.P.contractions_covariant).1

/- English proof (translation)
The claim follows from `(contraction_adapted Formalism.FourierDecayAlt.P.contractions_covariant).2`.
-/
theorem Formalism.FourierDecayAlt.P.second_contraction_adapted : Formalism.FourierDecayAlt.Q.Chat2Adapted := (contraction_adapted Formalism.FourierDecayAlt.P.contractions_covariant).2

/- English proof (translation)
The claim follows from `qnEabGl`.
-/
theorem Formalism.FourierDecayAlt.P.generator_gl_level : Formalism.FourierDecayAlt.Q.EabGlLev := qnEabGl

/- English proof (translation)
The claim follows from `qnEabPres`.
-/
theorem Formalism.FourierDecayAlt.P.generator_action_preserved : Formalism.FourierDecayAlt.Q.EabPres := qnEabPres

/- English proof (translation)
The claim follows from `quantum_ff_zero`.
-/
theorem Formalism.FourierDecayAlt.P.fusion_form_vanishes : Formalism.FourierDecayAlt.Q.FFZero :=
  quantum_ff_zero

/- English proof (translation)
The claim follows from `quantum_minor_left`.
-/
theorem Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian : Formalism.FourierDecayAlt.Q.QMinorLeftH := quantum_minor_left

/- English proof (translation)
The claim follows from `qnRdSkew`.
-/
theorem Formalism.FourierDecayAlt.P.right_differential_skew : Formalism.FourierDecayAlt.Q.RdSkew := qnRdSkew

/- English proof (translation)
The claim follows from `qnRuleRight`.
-/
theorem Formalism.FourierDecayAlt.P.right_action_rule : Formalism.FourierDecayAlt.Q.RuleRight := qnRuleRight

/- English proof (translation)
The claim follows from `quantum_v_monic`.
-/
theorem Formalism.FourierDecayAlt.P.capelli_polynomial_monic : Formalism.FourierDecayAlt.Q.VMonic := quantum_v_monic

/- English proof (translation)
The claim follows from `weyl_level_element_properties'`.
-/
theorem Formalism.FourierDecayAlt.P.weyl_level_element_properties : Formalism.FourierDecayAlt.Q.WeylLevelElementFacts := weyl_level_element_properties'

/- English proof (translation)
The claim follows from `qnYLeibniz`.
-/
theorem Formalism.FourierDecayAlt.P.twisted_leibniz_rule : Formalism.FourierDecayAlt.Q.YLeibniz := qnYLeibniz

/- English proof (translation)
Introduce `E _ _ k r u f`. Both sides reduce to the same expression.
-/
theorem Formalism.FourierDecayAlt.P.capelli_level_zero : Formalism.FourierDecayAlt.Q.CapLZero := by
  intro E _ _ k r u f
  rfl

/- English proof (translation)
The claim follows from `capelli_zero_level.2`.
-/
theorem Formalism.FourierDecayAlt.P.operator_level_zero : Formalism.FourierDecayAlt.Q.TLZero :=
  capelli_zero_level.2
