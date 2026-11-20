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
Establish `hinj : Function.Injective (fun z => posPl D p z e)`. Introduce `z z' h`. Establish `h'` using `congrArg (fun y => posPl D p y (nP D p * e - e)) h`. Simplify using `only [posPl_add] at h'`. Establish `he : e + (nP D p * e - e) = nP D p * e`.

Establish `: e ≤ nP D p * e` using `Nat.le_mul_of_pos_left e (Nat.pos_of_ne_zero (NeZero.ne _))`. Use linear arithmetic over natural numbers and integers. Rewrite `h'` using `[he, posPl_mul_period, posPl_mul_period]`. Then use the resulting hypothesis. Conclude with `⟨hinj, Finite.surjective_of_injective hinj⟩`.
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
Establish `hI` using `D.R.toFrame.iota_bijective.1`. Establish `hP` using `factPlaces D.R.toFrame`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨β, t⟩ ⟨β', t'⟩ h`. Establish `h1 : plGG D (β, t) = plGG D (β', t')` using `congrArg Subtype.val (D.eTau.symm.injective h)`.

Apply the tactic sequence `cases β <;> cases β'`. Establish `h2 : D.R.tau1 t = D.R.tau1 t'` using `h1`. Rewrite using `[hI (Prod.ext_iff.1 h2).2]`. Conclude with `absurd (show D.R.tau1 t = D.R.tau2 t' from h1) (hP.2 t t')`. Conclude with `absurd (show D.R.tau1 t' = D.R.tau2 t from h1.symm) (hP.2 t' t)`.

Establish `h2 : D.R.tau2 t = D.R.tau2 t'` using `h1`. Rewrite using `[hI (Prod.ext_iff.1 h2).2]`. Introduce `τ`. Break down `(hP.1 _).1 (D.eTau τ).2 with ⟨t, ht⟩ | ⟨t, ht⟩` into its components or cases. Conclude with `⟨(false, t), (Equiv.symm_apply_eq _).2 (Subtype.ext ht.symm)⟩`.

Conclude with `⟨(true, t), (Equiv.symm_apply_eq _).2 (Subtype.ext ht.symm)⟩`.
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
The claim follows from `lp_lower_bound l d Ds hl hD`.
-/
theorem lpF_ge_sum (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) (hl : 2 ≤ l) (hD : ∀ s, 0 ≤ Ds s) :
    (∑ s, Ds s) / ((l : ℝ) ^ 2 - 1) ≤ lpF l d Ds :=
  lp_lower_bound l d Ds hl hD

/- English proof (translation)
Introduce `j _ p hp _ hw`. Establish `hk : 0 ≤ (D.R.k : ℝ) - 1`. Establish `h` using `D.R.m_add_three_le_k`. Establish `h1 : (1 : ℝ) ≤ (D.R.k : ℝ)` using `by exact_mod_cast (by omega : 1 ≤ D.R.k)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hwP : ∀ z, 0 ≤ wPl D j z` using `fun z => hw _`. Unfold `FInert`. Use `split_ifs with h`. Conclude with `le_rfl`. Establish `hn : (0 : ℝ) < (nP D p : ℝ)` using `Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne _))`.

Rewrite using `[le_div_iff₀ hn]`. Establish `h1 : ∀ z, (∑ s : ZMod (nP D p), ((D.R.k : ℝ) - 1) * wPl D j (posPl D p z s.val)) / ((p : ℝ) ^ 2 - 1) ≤ FOrb D j p z` using `fun z => lpF_ge_sum p (nP D p) _ hp.two_le (fun s => mul_nonneg hk (hwP _))`. Use `le_trans (le_of_eq ?_) (Finset.sum_le_sum fun z _ => h1 z)` and prove the remaining obligations. Establish `h2 : ∀ s : ZMod (nP D p), ∑ z : Bool × HH D, ((D.R.k : ℝ) - 1) * wPl D j (posPl D p z s.val) = ∑ τ : D.what₂.Tau, ((D.R.k : ℝ) - 1) * wj D j τ` using `fun s => by`. Rewrite using `[(posPl_bijective D p s.val).sum_comp (fun z => ((D.R.k : ℝ) - 1) * wPl D j z)]`.

Conclude with `(tauPl_bij D).sum_comp (fun τ => ((D.R.k : ℝ) - 1) * wj D j τ)`. Establish `h3 : ∑ z : Bool × HH D, ∑ s : ZMod (nP D p), ((D.R.k : ℝ) - 1) * wPl D j (posPl D p z s.val) = (nP D p : ℝ) * ∑ τ : D.what₂.Tau, ((D.R.k : ℝ) - 1) * wj D j τ`. Rewrite using `[Finset.sum_comm, Finset.sum_congr rfl fun s _ => h2 s, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]`. Rewrite using `[← Finset.sum_div, ← Finset.sum_div, h3]`. Expand and normalize the polynomial expressions, which then agree.
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
The claim follows from `factDelDualNabla_of Formalism.L2.DIV.weylEqDualNabla`.
-/
theorem factDelDualNabla : FactDelDualNabla := factDelDualNabla_of Formalism.L2.DIV.weylEqDualNabla

section Check
/- English proof (translation)
The claim follows from `bridge_cols_conj_holds`.
-/
example : bridge_cols_conj := bridge_cols_conj_holds
/- English proof (translation)
The claim follows from `factSigYDceil`.
-/
example : FactSigYDceil := factSigYDceil
/- English proof (translation)
The claim follows from `factBuUnique`.
-/
example : FactBuUnique := factBuUnique
/- English proof (translation)
The claim follows from `factPsiCardViaTau`.
-/
example : FactPsiCardViaTau := factPsiCardViaTau
/- English proof (translation)
The claim follows from `anisotropicLine_indep_of_member`.
-/
example : AnisotropicLineIndepOfMember := anisotropicLine_indep_of_member
/- English proof (translation)
The claim follows from `factUnitRuleAgree`.
-/
example : FactUnitRuleAgree := factUnitRuleAgree
/- English proof (translation)
The claim follows from `bridge_ccb_unit_holds`.
-/
example : bridge_ccb_unit := bridge_ccb_unit_holds
/- English proof (translation)
The claim follows from `bridge_ccb_integral_holds`.
-/
example : bridge_ccb_integral := bridge_ccb_integral_holds
/- English proof (translation)
The claim follows from `bridge_unit_rule_holds`.
-/
example : bridge_unit_rule := bridge_unit_rule_holds
/- English proof (translation)
The claim follows from `factUnitNormalisation`.
-/
example : FactUnitNormalisation := factUnitNormalisation
/- English proof (translation)
The claim follows from `bridge_hn_mu_holds`.
-/
example : bridge_hn_mu := bridge_hn_mu_holds
/- English proof (translation)
The claim follows from `bridge_dual_mu_holds`.
-/
example : bridge_dual_mu := bridge_dual_mu_holds
/- English proof (translation)
The claim follows from `bridge_ccb_dual_holds`.
-/
example : bridge_ccb_dual := bridge_ccb_dual_holds
/- English proof (translation)
The claim follows from `rankBound_monotone_in_dimension`.
-/
example : RankBoundMonotoneInDimension := rankBound_monotone_in_dimension
/- English proof (translation)
The claim follows from `factHHcc`.
-/
example : FactHHcc := factHHcc
/- English proof (translation)
The claim follows from `factNc`.
-/
example : FactNc := factNc
/- English proof (translation)
The claim follows from `factNatW`.
-/
example : FactNatW := factNatW
/- English proof (translation)
The claim follows from `bridge_round_square_holds`.
-/
example : bridge_round_square := bridge_round_square_holds
/- English proof (translation)
The claim follows from `factSqActMul`.
-/
example : FactSqActMul := factSqActMul
/- English proof (translation)
The claim follows from `factSqStable`.
-/
example : FactSqStable := factSqStable
/- English proof (translation)
The claim follows from `factSqHighestWeight`.
-/
example : FactSqHighestWeight := factSqHighestWeight
/- English proof (translation)
The claim follows from `bridge_normFock_extremal_holds`.
-/
example : bridge_normFock_extremal := bridge_normFock_extremal_holds
/- English proof (translation)
The claim follows from `factNormFockUnitary`.
-/
example : FactNormFockUnitary := factNormFockUnitary
/- English proof (translation)
The claim follows from `factDelDualNabla`.
-/
example : FactDelDualNabla := factDelDualNabla
/- English proof (translation)
The claim follows from `bridge_hc_rho_holds`.
-/
example : bridge_hc_rho := bridge_hc_rho_holds
/- English proof (translation)
The claim follows from `factIota`.
-/
example : FactIota := factIota
/- English proof (translation)
The claim follows from `bridge_iota_holds`.
-/
example : bridge_iota := bridge_iota_holds
/- English proof (translation)
The claim follows from `bridge_star_holds`.
-/
example : bridge_star := bridge_star_holds
/- English proof (translation)
The claim follows from `factCardPsi`.
-/
example : FactCardPsi := factCardPsi
/- English proof (translation)
The claim follows from `factEmb`.
-/
example : FactEmb := factEmb
/- English proof (translation)
The claim follows from `factPlaces`.
-/
example : FactPlaces := factPlaces
/- English proof (translation)
The claim follows from `factTopsThick`.
-/
example : FactTopsThick := factTopsThick
/- English proof (translation)
The claim follows from `factRd`.
-/
example : FactRd := factRd
/- English proof (translation)
The claim follows from `factMMUnimodular`.
-/
example : FactMMUnimodular := factMMUnimodular
/- English proof (translation)
The claim follows from `factClassFrob`.
-/
example : FactClassFrob := factClassFrob
/- English proof (translation)
The claim follows from `factFrobGeom`.
-/
example : FactFrobGeom := factFrobGeom
/- English proof (translation)
The claim follows from `Formalism.L2.Col.bridge_lidx_det_holds`.
-/
example : bridge_lidx_det := Formalism.L2.Col.bridge_lidx_det_holds
/- English proof (translation)
The claim follows from `factWtPos`.
-/
example : FactWtPos := factWtPos
/- English proof (translation)
The claim follows from `factWtZero`.
-/
example : FactWtZero := factWtZero
/- English proof (translation)
The claim follows from `factWtInt`.
-/
example : FactWtInt := factWtInt
/- English proof (translation)
The claim follows from `bridge_KD_succ_holds`.
-/
example : bridge_KD_succ := bridge_KD_succ_holds
/- English proof (translation)
The claim follows from `bridge_thl_index_holds`.
-/
example : bridge_thl_index := bridge_thl_index_holds
/- English proof (translation)
The claim follows from `factSDivSharp`.
-/
example : FactSDivSharp := factSDivSharp
/- English proof (translation)
The claim follows from `factEInt`.
-/
example : FactEInt := factEInt
/- English proof (translation)
The claim follows from `factDuLe`.
-/
example : FactDuLe := factDuLe
/- English proof (translation)
The claim follows from `factGaussRam`.
-/
example : FactGaussRam := factGaussRam
/- English proof (translation)
The claim follows from `bridge_autL_not_column_holds`.
-/
example : bridge_autL_not_column := bridge_autL_not_column_holds
/- English proof (translation)
The claim follows from `factEtaMean`.
-/
example : FactEtaMean := factEtaMean
/- English proof (translation)
The claim follows from `factLpF`.
-/
example : FactLpF := factLpF
/- English proof (translation)
The claim follows from `Rows.factKaBlocks`.
-/
example : Rows.FactKaBlocks := Rows.factKaBlocks
/- English proof (translation)
The claim follows from `Rows.factShimRange`.
-/
example : Rows.FactShimRange := Rows.factShimRange
/- English proof (translation)
The claim follows from `Rows.factQZ`.
-/
example : Rows.FactQZ := Rows.factQZ
/- English proof (translation)
The claim follows from `Rows.factBuDetermined`.
-/
example : Rows.FactBuDetermined := Rows.factBuDetermined
/- English proof (translation)
The claim follows from `Rows.factLamPNonneg`.
-/
example : Rows.FactLamPNonneg := Rows.factLamPNonneg
/- English proof (translation)
The claim follows from `Rows.factDleDall`.
-/
example : Rows.FactDleDall := Rows.factDleDall
/- English proof (translation)
The claim follows from `Rows.factZeMu0`.
-/
example : Rows.FactZeMu0 := Rows.factZeMu0
/- English proof (translation)
The claim follows from `Rows.factAjConj`.
-/
example : Rows.FactAjConj := Rows.factAjConj
/- English proof (translation)
The claim follows from `bridge_hD_holds`.
-/
example : Spaces.bridge_hD := bridge_hD_holds
/- English proof (translation)
The claim follows from `bridge_sigRank_holds`.
-/
example : Spaces.bridge_sigRank := bridge_sigRank_holds
/- English proof (translation)
The claim follows from `rank_base_space`.
-/
example : RankBaseSpaceEq := rank_base_space
/- English proof (translation)
The claim follows from `signature_base_space`.
-/
example : SignatureBaseSpaceSum := signature_base_space
/- English proof (translation)
The claim follows from `factSigW`.
-/
example : FactSigW := factSigW
/- English proof (translation)
The claim follows from `signature_base_space_graded`.
-/
example : SignatureBaseMiddleEq := signature_base_space_graded
/- English proof (translation)
The claim follows from `factWmDef`.
-/
example : FactWmDef := factWmDef
/- English proof (translation)
The claim follows from `factXm`.
-/
example : FactXm := factXm
/- English proof (translation)
The claim follows from `factYm`.
-/
example : FactYm := factYm
/- English proof (translation)
The claim follows from `factNStep`.
-/
example : FactNStep := factNStep
/- English proof (translation)
The claim follows from `factNEven`.
-/
example : FactNEven := factNEven
/- English proof (translation)
The claim follows from `factROdd`.
-/
example : FactROdd := factROdd
/- English proof (translation)
The claim follows from `factSigmaCount`.
-/
example : FactSigmaCount := factSigmaCount
/- English proof (translation)
The claim follows from `factSShift`.
-/
example : FactSShift := factSShift
/- English proof (translation)
The claim follows from `factWG`.
-/
example : FactWG := factWG
/- English proof (translation)
The claim follows from `factSInt`.
-/
example : FactSInt := factSInt
/- English proof (translation)
The claim follows from `factNV`.
-/
example : FactNV := factNV
/- English proof (translation)
The claim follows from `factHCMono`.
-/
example : FactHCMono := factHCMono

/- English proof (translation)
The claim follows from `factSigYD R`.
-/
example (R : Ranks) : FactSigYD R := factSigYD R
/- English proof (translation)
The claim follows from `baseSpace_posDef R F`.
-/
example (R : Ranks) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] :
    BaseSpacePosDef R F E := baseSpace_posDef R F
/- English proof (translation)
The claim follows from `factXmDef R F`.
-/
example (R : Ranks) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] :
    FactXmDef R F E := factXmDef R F
/- English proof (translation)
The claim follows from `factVSig R F`.
-/
example (R : Ranks) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] :
    FactVSig R F E := factVSig R F
/- English proof (translation)
The claim follows from `factWmPosDef R F E`.
-/
example (R : Ranks) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] :
    FactWmPosDef R F E := factWmPosDef R F E
/- English proof (translation)
The claim follows from `Idx.factStepBz X`.
-/
example (D : D7) (X : DivX D) : Idx.FactStepBz X := Idx.factStepBz X
/- English proof (translation)
The claim follows from `fInertGe D`.
-/
example (D : D7) : FInertGe D := fInertGe D

/- English proof (translation)
The claim follows from `factPrincipalDatum_of h1 h2`.
-/
example (h1 : DiffKPrincipal) (h2 : CcNorm) : FactPrincipalDatum := factPrincipalDatum_of h1 h2
/- English proof (translation)
The claim follows from `DGamMink.fact h hD`.
-/
example (D : D7) (h : DGamMink D) (hD : DGamDef D) : FactDGam D 12 := DGamMink.fact h hD

end Check

end Formalism.BasicNotions

end
