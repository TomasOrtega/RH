import Formalism.LocalRingCardinality.DataForced
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LpLower
import Formalism.LocalToGlobal.Columns.CoefficientsModP
import Formalism.LocalRingCardinality.MinkMEqMinkowskiNumber
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

noncomputable section

namespace Formalism.BasicNotions

open Formalism.MainNotions.G
open scoped BigOperators

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Supply the required witnesses or components.
-/
theorem posPl_bijective (D : D7) (p e : ℕ) : Function.Bijective (fun z => posPl D p z e) := by
  have hinj : Function.Injective (fun z => posPl D p z e) := by
    intro z z' h
    have h' := congrArg (fun y => posPl D p y (nP D p * e - e)) h
    simp only [posPl_add] at h'
    have he : e + (nP D p * e - e) = nP D p * e := by
      have : e ≤ nP D p * e := Nat.le_mul_of_pos_left e (Nat.pos_of_ne_zero (NeZero.ne _))
      omega
    rwa [he, posPl_mul_period, posPl_mul_period] at h'
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem tauPl_bij (D : D7) : Function.Bijective (tauPl D) := by
  have hI := D.R.toFrame.iota_bijective.1
  have hP := factPlaces D.R.toFrame
  constructor
  · rintro ⟨β, t⟩ ⟨β', t'⟩ h
    have h1 : plGG D (β, t) = plGG D (β', t') := congrArg Subtype.val (D.eTau.symm.injective h)
    cases β <;> cases β'
    · have h2 : D.R.tau1 t = D.R.tau1 t' := h1
      rw [hI (Prod.ext_iff.1 h2).2]
    · exact absurd (show D.R.tau1 t = D.R.tau2 t' from h1) (hP.2 t t')
    · exact absurd (show D.R.tau1 t' = D.R.tau2 t from h1.symm) (hP.2 t' t)
    · have h2 : D.R.tau2 t = D.R.tau2 t' := h1
      rw [hI (Prod.ext_iff.1 h2).2]
  · intro τ
    rcases (hP.1 _).1 (D.eTau τ).2 with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨(false, t), (Equiv.symm_apply_eq _).2 (Subtype.ext ht.symm)⟩
    · exact ⟨(true, t), (Equiv.symm_apply_eq _).2 (Subtype.ext ht.symm)⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lpF_ge_sum (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) (hl : 2 ≤ l) (hD : ∀ s, 0 ≤ Ds s) :
    (∑ s, Ds s) / ((l : ℝ) ^ 2 - 1) ≤ lpF l d Ds :=
  lp_lower_bound l d Ds hl hD

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem fInertGe (D : D7) : FInertGe D := by
  intro j _ p hp _ hw
  have hk : 0 ≤ (D.R.k : ℝ) - 1 := by
    have h := D.R.m_add_three_le_k
    have h1 : (1 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast (by omega : 1 ≤ D.R.k)
    linarith
  have hwP : ∀ z, 0 ≤ wPl D j z := fun z => hw _
  unfold FInert
  split_ifs with h
  · exact le_rfl
  · have hn : (0 : ℝ) < (nP D p : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne _))
    rw [le_div_iff₀ hn]
    have h1 : ∀ z, (∑ s : ZMod (nP D p), ((D.R.k : ℝ) - 1) * wPl D j (posPl D p z s.val)) / ((p : ℝ) ^ 2 - 1) ≤
        FOrb D j p z :=
      fun z => lpF_ge_sum p (nP D p) _ hp.two_le (fun s => mul_nonneg hk (hwP _))
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun z _ => h1 z)
    have h2 : ∀ s : ZMod (nP D p), ∑ z : Bool × HH D, ((D.R.k : ℝ) - 1) * wPl D j (posPl D p z s.val) =
        ∑ τ : D.what₂.Tau, ((D.R.k : ℝ) - 1) * wj D j τ := fun s => by
      rw [(posPl_bijective D p s.val).sum_comp (fun z => ((D.R.k : ℝ) - 1) * wPl D j z)]
      exact (tauPl_bij D).sum_comp (fun τ => ((D.R.k : ℝ) - 1) * wj D j τ)
    have h3 : ∑ z : Bool × HH D, ∑ s : ZMod (nP D p), ((D.R.k : ℝ) - 1) * wPl D j (posPl D p z s.val) =
        (nP D p : ℝ) * ∑ τ : D.what₂.Tau, ((D.R.k : ℝ) - 1) * wj D j τ := by
      rw [Finset.sum_comm, Finset.sum_congr rfl fun s _ => h2 s, Finset.sum_const, Finset.card_univ, ZMod.card,
        nsmul_eq_mul]
    rw [← Finset.sum_div, ← Finset.sum_div, h3]
    ring

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem factDelDualNabla : FactDelDualNabla := factDelDualNabla_of Formalism.L2.DIV.weylEqDualNabla

section Check
/- English proof (translation)
A detailed English derivation is pending.
-/
example : bridge_cols_conj := bridge_cols_conj_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactSigYDceil := factSigYDceil
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactBuUnique := factBuUnique
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactPsiCardViaTau := factPsiCardViaTau
/- English proof (translation)
A detailed English derivation is pending.
-/
example : AnisotropicLineIndepOfMember := anisotropicLine_indep_of_member
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactUnitRuleAgree := factUnitRuleAgree
/- English proof (translation)
A detailed English derivation is pending.
-/
example : bridge_ccb_unit := bridge_ccb_unit_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
example : bridge_ccb_integral := bridge_ccb_integral_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
example : bridge_unit_rule := bridge_unit_rule_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactUnitNormalisation := factUnitNormalisation
/- English proof (translation)
A detailed English derivation is pending.
-/
example : bridge_hn_mu := bridge_hn_mu_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
example : bridge_dual_mu := bridge_dual_mu_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
example : bridge_ccb_dual := bridge_ccb_dual_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
example : RankBoundMonotoneInDimension := rankBound_monotone_in_dimension
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactHHcc := factHHcc
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactNc := factNc
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactNatW := factNatW
/- English proof (translation)
A detailed English derivation is pending.
-/
example : bridge_round_square := bridge_round_square_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactSqActMul := factSqActMul
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactSqStable := factSqStable
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactSqHighestWeight := factSqHighestWeight
/- English proof (translation)
A detailed English derivation is pending.
-/
example : bridge_normFock_extremal := bridge_normFock_extremal_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactNormFockUnitary := factNormFockUnitary
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactDelDualNabla := factDelDualNabla
/- English proof (translation)
A detailed English derivation is pending.
-/
example : bridge_hc_rho := bridge_hc_rho_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactIota := factIota
/- English proof (translation)
A detailed English derivation is pending.
-/
example : bridge_iota := bridge_iota_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
example : bridge_star := bridge_star_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactCardPsi := factCardPsi
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactEmb := factEmb
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactPlaces := factPlaces
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactTopsThick := factTopsThick
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactRd := factRd
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactMMUnimodular := factMMUnimodular
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactClassFrob := factClassFrob
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactFrobGeom := factFrobGeom
/- English proof (translation)
A detailed English derivation is pending.
-/
example : bridge_lidx_det := Formalism.L2.Col.bridge_lidx_det_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactWtPos := factWtPos
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactWtZero := factWtZero
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactWtInt := factWtInt
/- English proof (translation)
A detailed English derivation is pending.
-/
example : bridge_KD_succ := bridge_KD_succ_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
example : bridge_thl_index := bridge_thl_index_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactSDivSharp := factSDivSharp
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactEInt := factEInt
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactDuLe := factDuLe
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactGaussRam := factGaussRam
/- English proof (translation)
A detailed English derivation is pending.
-/
example : bridge_autL_not_column := bridge_autL_not_column_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactEtaMean := factEtaMean
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactLpF := factLpF
/- English proof (translation)
A detailed English derivation is pending.
-/
example : Rows.FactKaBlocks := Rows.factKaBlocks
/- English proof (translation)
A detailed English derivation is pending.
-/
example : Rows.FactShimRange := Rows.factShimRange
/- English proof (translation)
A detailed English derivation is pending.
-/
example : Rows.FactQZ := Rows.factQZ
/- English proof (translation)
A detailed English derivation is pending.
-/
example : Rows.FactBuDetermined := Rows.factBuDetermined
/- English proof (translation)
A detailed English derivation is pending.
-/
example : Rows.FactLamPNonneg := Rows.factLamPNonneg
/- English proof (translation)
A detailed English derivation is pending.
-/
example : Rows.FactDleDall := Rows.factDleDall
/- English proof (translation)
A detailed English derivation is pending.
-/
example : Rows.FactZeMu0 := Rows.factZeMu0
/- English proof (translation)
A detailed English derivation is pending.
-/
example : Rows.FactAjConj := Rows.factAjConj
/- English proof (translation)
A detailed English derivation is pending.
-/
example : Spaces.bridge_hD := bridge_hD_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
example : Spaces.bridge_sigRank := bridge_sigRank_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
example : RankBaseSpaceEq := rank_base_space
/- English proof (translation)
A detailed English derivation is pending.
-/
example : SignatureBaseSpaceSum := signature_base_space
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactSigW := factSigW
/- English proof (translation)
A detailed English derivation is pending.
-/
example : SignatureBaseMiddleEq := signature_base_space_graded
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactWmDef := factWmDef
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactXm := factXm
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactYm := factYm
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactNStep := factNStep
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactNEven := factNEven
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactROdd := factROdd
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactSigmaCount := factSigmaCount
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactSShift := factSShift
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactWG := factWG
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactSInt := factSInt
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactNV := factNV
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FactHCMono := factHCMono

/- English proof (translation)
A detailed English derivation is pending.
-/
example (R : Ranks) : FactSigYD R := factSigYD R
/- English proof (translation)
A detailed English derivation is pending.
-/
example (R : Ranks) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] :
    BaseSpacePosDef R F E := baseSpace_posDef R F
/- English proof (translation)
A detailed English derivation is pending.
-/
example (R : Ranks) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] :
    FactXmDef R F E := factXmDef R F
/- English proof (translation)
A detailed English derivation is pending.
-/
example (R : Ranks) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] :
    FactVSig R F E := factVSig R F
/- English proof (translation)
A detailed English derivation is pending.
-/
example (R : Ranks) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] :
    FactWmPosDef R F E := factWmPosDef R F E
/- English proof (translation)
A detailed English derivation is pending.
-/
example (D : D7) (X : DivX D) : Idx.FactStepBz X := Idx.factStepBz X
/- English proof (translation)
A detailed English derivation is pending.
-/
example (D : D7) : FInertGe D := fInertGe D

/- English proof (translation)
A detailed English derivation is pending.
-/
example (h1 : DiffKPrincipal) (h2 : CcNorm) : FactPrincipalDatum := factPrincipalDatum_of h1 h2
/- English proof (translation)
A detailed English derivation is pending.
-/
example (D : D7) (h : DGamMink D) (hD : DGamDef D) : FactDGam D 12 := DGamMink.fact h hD

end Check

end Formalism.BasicNotions

end
