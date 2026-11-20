import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjCongr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDvdNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePeriodMemFiltrationZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDegreeOfNotMemFilTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRingEmbeddingProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LtSeriesCoeffEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EvaluationPowerSeriesShift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingNoZeroDivisors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodTensorMapInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiedTensorInj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEqZeroOfStable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEigenFilOneIsUnitExactDegree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLaws

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.BKReal GlobalTheory.ConjPeriod
open GlobalTheory.MemLoc GlobalTheory.ConjNorm Formalism.BasicNotions.Examples₂.LB GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.ConjDegree

variable {l : ℕ} [hl : Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

/- English proof (translation)
Use `haveI := Formalism.BasicNotions.Examples₂.LB.OL_resFinite K`. Establish `hπ : Irreducible π` using `hD.1`. Take `⟨hf, hE⟩` from `GlobalTheory.T.lubin_tate_endomorphism_unique l K π hπ`. Take `⟨ω, hω0, hθ, hφ, hg⟩` from `GlobalTheory.T.lubin_tate_period_galois_expansion l K χ π z hD`. Establish `hθ' : ω ∈ RingHom.ker (thetaK K)` using `hθ`.

Take `⟨L', u, -, -, -, ht⟩` from `GlobalTheory.AcrisK.ev_shift l K _ (onDisc_log hπ hf) ω hθ _ (ev_ltLog hπ hf ω hθ)`. Rewrite `ht` using `[PowerSeries.coeff_zero_eq_constantCoeff_apply, GlobalTheory.LTLog.constantCoeff_log _ hπ hf, map_zero, zero_add]`. Use `⟨ω, ltLog hπ hf ω hθ, u, hθ, ht, GlobalTheory.T.lubin_tate_log_ne_zero l K π hπ _ hf ω hθ (GlobalTheory.T.lubin_tate_period_theta_kernel l K χ π z hD ω hω0 hθ hφ hg), ?_, fun g => ?_⟩` and prove the remaining obligations. Use `ev_log_self hπ hf hθ (y := frobq K ω) (fun n => ?_) (Ev.frob (ev_ltLog hπ hf ω hθ))` and prove the remaining obligations. Rewrite using `[hφ, GlobalTheory.LTPer.ltSeries_eval]`.

Conclude with `GlobalTheory.LTPer.sum_sub_sum_mem _ hθ' _ _ (fun j hj => GlobalTheory.LTPer.ltSeries_coeff_eq_zero K π j hj) n`. Take `⟨a, ha, φ, hφE, -⟩` from `hD.2.2.2.2 g`. Establish `hy` using `hg g a φ ha hφE`. Rewrite `hy` using `[(hE a φ).1 hφE]`. Rewrite using `[ev_log_hom hπ hf a hθ hy (Ev.gal g (ev_ltLog hπ hf ω hθ)), ← ha]`.

Both sides reduce to the same expression.
-/
theorem exists_period (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l) (hD : LTData K χ π z) :
    ∃ (ω : AK K) (t u : BK K), thetaK K ω = 0 ∧ t = toB K (ofA K ω) * u ∧ t ≠ 0 ∧
      frobB K t = inK K (π : ↥K.1) * t ∧ ∀ g : ↥(GK K), galB g t = inK K (χ g : ↥K.1) * t := by
  haveI := Formalism.BasicNotions.Examples₂.LB.OL_resFinite K
  have hπ : Irreducible π := hD.1
  obtain ⟨hf, hE⟩ := GlobalTheory.T.lubin_tate_endomorphism_unique l K π hπ
  obtain ⟨ω, hω0, hθ, hφ, hg⟩ := GlobalTheory.T.lubin_tate_period_galois_expansion l K χ π z hD
  have hθ' : ω ∈ RingHom.ker (thetaK K) := hθ
  obtain ⟨L', u, -, -, -, ht⟩ := GlobalTheory.AcrisK.ev_shift l K _ (onDisc_log hπ hf) ω hθ _ (ev_ltLog hπ hf ω hθ)
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, GlobalTheory.LTLog.constantCoeff_log _ hπ hf, map_zero, zero_add] at ht
  refine ⟨ω, ltLog hπ hf ω hθ, u, hθ, ht,
    GlobalTheory.T.lubin_tate_log_ne_zero l K π hπ _ hf ω hθ (GlobalTheory.T.lubin_tate_period_theta_kernel l K χ π z hD ω hω0 hθ hφ hg), ?_, fun g => ?_⟩
  · refine ev_log_self hπ hf hθ (y := frobq K ω) (fun n => ?_) (Ev.frob (ev_ltLog hπ hf ω hθ))
    rw [hφ, GlobalTheory.LTPer.ltSeries_eval]
    exact GlobalTheory.LTPer.sum_sub_sum_mem _ hθ' _ _ (fun j hj => GlobalTheory.LTPer.ltSeries_coeff_eq_zero K π j hj) n
  · obtain ⟨a, ha, φ, hφE, -⟩ := hD.2.2.2.2 g
    have hy := hg g a φ ha hφE
    rw [(hE a φ).1 hφE] at hy
    rw [ev_log_hom hπ hf a hθ hy (Ev.gal g (ev_ltLog hπ hf ω hθ)), ← ha]
    rfl

variable (T : LocTied l P AI) (K : FinExt l)

def jB : Per.Acris l →+* P.R.B := T.eB.symm.toRingHom.comp (algebraMap (Per.Acris l) (Per.Bcris l))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem uj_eq (j : ℕ) (a : Per.Acris l) : uj T j a = P.ιB (jB T ((phiA l ^ j) a)) := rfl

/- English proof (translation)
Rewrite using `[uj_eq, uj_eq, pow_add]`. Both sides reduce to the same expression.
-/
theorem uj_add (i j : ℕ) (a : Per.Acris l) : uj T (i + j) a = uj T i ((phiA l ^ j) a) := by
  rw [uj_eq, uj_eq, pow_add]
  rfl

/- English proof (translation)
Take `⟨C⟩` from `GlobalTheory.MemLoc.nonempty_core l`. Conclude with `T.eB.symm.injective.comp (GlobalTheory.MemLoc.AwayT.acris_injective C)`.
-/
theorem jB_injective : Function.Injective (jB T) := by
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  exact T.eB.symm.injective.comp (GlobalTheory.MemLoc.AwayT.acris_injective C)

/- English proof (translation)
Use `GlobalTheory.PZ.ColmezVec.pow_phi_acris T K 1 a` as an intermediate fact. Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis.
-/
theorem phi_jB (a : Per.Acris l) : (P.PD K).φ (jB T a) = jB T (phiA l a) := by
  have := GlobalTheory.PZ.ColmezVec.pow_phi_acris T K 1 a
  rwa [pow_one] at this

/- English proof (translation)
Take `⟨C⟩` from `GlobalTheory.MemLoc.nonempty_core l`. Apply `GlobalTheory.MemLoc.ULaws.iota_injective C` to reduce the goal to its premises. Rewrite using `[GlobalTheory.MemLoc.ULaws.iota_aB, C.ι_j]`. Conclude with `congrArg _ (GlobalTheory.MemLoc.TFil.j_alg C.j_cris a).symm`.
-/
private theorem aB_eq_alg_aC (a : Per.Ainf l) :
    Per.aB l a = algebraMap (Per.Acris l) (Per.Bcris l) (aC l a) := by
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  apply GlobalTheory.MemLoc.ULaws.iota_injective C
  rw [GlobalTheory.MemLoc.ULaws.iota_aB, C.ι_j]
  exact congrArg _ (GlobalTheory.MemLoc.TFil.j_alg C.j_cris a).symm

/- English proof (translation)
Introduce `w` and use `(GlobalTheory.WittCompat.exists_unramified_witt_element l P AI T K w).elim fun c hc => ((P.PD_ι K _).symm.trans ((congrArg (P.PD K).ι (hc.2.trans (congrArg T.eB.symm (aB_eq_alg_aC _)))).symm.trans ((P.PD K).ι.commutes c))).trans ((IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.B …`.
-/
theorem compat_zero : Compat T K 0 K.1.val := fun w =>
  (GlobalTheory.WittCompat.exists_unramified_witt_element l P AI T K w).elim fun c hc =>
    ((P.PD_ι K _).symm.trans ((congrArg (P.PD K).ι
      (hc.2.trans (congrArg T.eB.symm (aB_eq_alg_aC _)))).symm.trans ((P.PD K).ι.commutes c))).trans
      ((IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR c).trans (congrArg _ hc.1))

/- English proof (translation)
Take `⟨C, hC⟩` from `GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T`. Establish `hD : ∀ a, T.eD (uj T 0 a) = algebraMap (Per.BdRp l) (Per.BdR l) (C.j a)` using `fun a => by`. Rewrite using `[uj_eq, hC.ι, ← C.ι_j]`. Conclude with `congrArg C.ι (T.eB.apply_symm_apply _)`. Establish `hA : ∀ x : AK K, T.eD (conj T K 0 K.1.val (compat_zero T K) (toB K (ofA K x))) = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.CrisToDR.psiA C K x)` using `fun x => GlobalTheory.AinfK.induction_on x (fun a c => by`.

Simplify using `only [map_mul]`. Rewrite using `[ofA_inA, ofA_inO, ← inK_oK, conj_inK, conj_inC, hD, GlobalTheory.CrisToDR.psiA_inA, GlobalTheory.CrisToDR.psiA_inO]`. Use `congr 1`. Conclude with `congrArg _ (GlobalTheory.MemLoc.TFil.j_alg C.j_cris a)`. Conclude with `hC.o _)`.

Use `fun x y hx hy => by simp only [map_add, hx, hy]`. Rewrite using `[T.fil, hA]`. Use `GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD 1 (((thetaD_props l).2.1 _).1 ?_)` and prove the remaining obligations. Rewrite using `[GlobalTheory.CrisToDR.thetaD_psiA, hx]`. Both sides reduce to the same expression.
-/
theorem conj_zero_mem (x : AK K) (hx : thetaK K x = 0) :
    conj T K 0 K.1.val (compat_zero T K) (toB K (ofA K x)) ∈ (P.PD K).Fil 1 := by
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  have hD : ∀ a, T.eD (uj T 0 a) = algebraMap (Per.BdRp l) (Per.BdR l) (C.j a) := fun a => by
    rw [uj_eq, hC.ι, ← C.ι_j]
    exact congrArg C.ι (T.eB.apply_symm_apply _)
  have hA : ∀ x : AK K, T.eD (conj T K 0 K.1.val (compat_zero T K) (toB K (ofA K x))) =
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.CrisToDR.psiA C K x) := fun x =>
    GlobalTheory.AinfK.induction_on x (fun a c => by
      simp only [map_mul]
      rw [ofA_inA, ofA_inO, ← inK_oK, conj_inK, conj_inC, hD, GlobalTheory.CrisToDR.psiA_inA, GlobalTheory.CrisToDR.psiA_inO]
      congr 1
      · exact congrArg _ (GlobalTheory.MemLoc.TFil.j_alg C.j_cris a)
      · exact hC.o _)
      fun x y hx hy => by simp only [map_add, hx, hy]
  rw [T.fil, hA]
  refine GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD 1 (((thetaD_props l).2.1 _).1 ?_)
  rw [GlobalTheory.CrisToDR.thetaD_psiA, hx]
  rfl

include T in

/- English proof (translation)
Use `haveI : IsDomain P.R.BdR := (GlobalTheory.RegularRing.isField_of_tied T).isDomain`. Use `Function.Injective.isDomain ((conj T K 0 K.1.val (compat_zero T K)).comp (toB K)) ((injective_iff_map_eq_zero _).2 fun z hz => ?_)` and prove the remaining obligations. Set `b` to `Module.finBasis (W0 K) ↥(OL K)`. Establish `hb` using `GlobalTheory.UnramDisjoint.linearIndependent_Kur l K _ _ (GlobalTheory.CrisInj.li_of_frac (W := W0 K) (F := ↥(K0 K)) (oK K) (IsFractionRing.injective ↥(OL K) ↥K.1) (thetaW_injective K) (GlobalTheory.CrisInj.exists_frac K) _ b.linearIndependent)`. Take `⟨a, ha⟩` from `GlobalTheory.CrisInj.exists_coord (A := Per.Acris l) b z`.

Establish `ha' : z = ∑ i, inC K (a i) * inI K (b i)` using `ha.trans (Finset.sum_congr (M := CK K) rfl fun i _ => GlobalTheory.AcrisK.tmul_eq K _ _)`. Establish `h0` using `GlobalTheory.LocTensor.tied_tensor_inj l P AI T _ _ hb (fun i => jB T (a i)) (by`. Rewrite using `[← hz, ha', map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, map_mul, map_mul, ← inK_oK, conj_inC, conj_inK, mul_comm]`.

Use the proof step `rfl)`. Rewrite using `[ha']`. Conclude with `Finset.sum_eq_zero fun i _ => by`. Rewrite using `[jB_injective T ((h0 i).trans (map_zero _).symm), map_zero, zero_mul]`.
-/
theorem isDomain_CK : IsDomain (CK K) := by
  haveI : IsDomain P.R.BdR := (GlobalTheory.RegularRing.isField_of_tied T).isDomain
  refine Function.Injective.isDomain ((conj T K 0 K.1.val (compat_zero T K)).comp (toB K))
    ((injective_iff_map_eq_zero _).2 fun z hz => ?_)
  let b := Module.finBasis (W0 K) ↥(OL K)
  have hb := GlobalTheory.UnramDisjoint.linearIndependent_Kur l K _ _
    (GlobalTheory.CrisInj.li_of_frac (W := W0 K) (F := ↥(K0 K)) (oK K) (IsFractionRing.injective ↥(OL K) ↥K.1)
      (thetaW_injective K) (GlobalTheory.CrisInj.exists_frac K) _ b.linearIndependent)
  obtain ⟨a, ha⟩ := GlobalTheory.CrisInj.exists_coord (A := Per.Acris l) b z
  have ha' : z = ∑ i, inC K (a i) * inI K (b i) :=
    ha.trans (Finset.sum_congr (M := CK K) rfl fun i _ => GlobalTheory.AcrisK.tmul_eq K _ _)
  have h0 := GlobalTheory.LocTensor.tied_tensor_inj l P AI T _ _ hb (fun i => jB T (a i)) (by
    rw [← hz, ha', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RingHom.comp_apply, map_mul, map_mul, ← inK_oK, conj_inC, conj_inK, mul_comm]
    rfl)
  rw [ha']
  exact Finset.sum_eq_zero fun i _ => by
    rw [jB_injective T ((h0 i).trans (map_zero _).symm), map_zero, zero_mul]

include T in
/- English proof (translation)
Take `⟨y, hy, -⟩` from `T.om x`. Rewrite using `[T.fil, hy]`. Conclude with `GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero y`.
-/
theorem om_mem (x : Om l) : algebraMap (Om l) P.R.BdR x ∈ (P.PD K).Fil 0 := by
  obtain ⟨y, hy, -⟩ := T.om x
  rw [T.fil, hy]
  exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero y

/- English proof (translation)
Take `⟨y, hy⟩` from `eD_uj_mem T j a`. Rewrite using `[T.fil, ← hy]`. Conclude with `GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero y`.
-/
theorem uj_mem (j : ℕ) (a : Per.Acris l) : uj T j a ∈ (P.PD K).Fil 0 := by
  obtain ⟨y, hy⟩ := eD_uj_mem T j a
  rw [T.fil, ← hy]
  exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero y

/- English proof (translation)
Simplify using `using (P.PD K).Fil_mul 0 a _ _ hx hy`.
-/
theorem mul_mem_left {a : ℤ} {x y : P.R.BdR} (hx : x ∈ (P.PD K).Fil 0) (hy : y ∈ (P.PD K).Fil a) :
    x * y ∈ (P.PD K).Fil a := by
  simpa using (P.PD K).Fil_mul 0 a _ _ hx hy

include T in

/- English proof (translation)
Use `haveI : IsDomain P.R.BdR := (GlobalTheory.RegularRing.isField_of_tied T).isDomain`. Establish `hι : ∀ b, (P.PD K).ι.toRingHom b = P.ιB b` using `P.PD_ι K`. Establish `hlu : IsUnit (l : P.R.B)`. Simplify using `using ((Nat.cast_ne_zero.2 hl.out.ne_zero : (l : ℚ_[l]) ≠ 0).isUnit).map (algebraMap ℚ_[l] P.R.B)`. Establish `h` using `GlobalTheory.MemLoc.EigenDegree.abstract (P.PD K).ι.toRingHom (P.PD K).ι_inj (P.PD K).φ.toRingHom (fun a y => y ∈ (P.PD K).Fil a) (P.PD K).one_mem (P.PD K).Fil_mul (l : P.R.B) (P.PD K).t hlu (P.PD K).t_unit (by`.

Use `(P.PD K).t_φ` as an intermediate fact. Rewrite using `[P.PD_p, Algebra.smul_def, map_natCast] at this) (P.PD K).not_mem_filtration_two` and apply the resulting hypothesis. Use the proof step `(fun y hy => by`. Take `⟨z, hz, e⟩` from `((GlobalTheory.MemLoc.TiedUnif.tied_uniformiser l P AI T).2.2 K 0 y).1 (by rwa [zero_add])`. Conclude with `⟨z, hz, by rw [hι, P.period_datum_t_eq]; exact e⟩)`.

Use the proof step `(fun b hb hb0 hne => by`. Take `⟨c, rfl⟩` from `(P.PD K).fund b hb hb0`. Establish `hc : c ≠ 0`. Introduce and unpack `rfl`. Conclude with `hne (map_zero _)`.

Use `⟨algebraMap ℚ_[l] P.R.B c⁻¹, by rw [← map_mul, inv_mul_cancel₀ hc, map_one], ?_⟩` and prove the remaining obligations. Rewrite using `[hι, AlgHom.commutes, IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR]`. Conclude with `om_mem T K _) 1 one_pos x hx h0 (by rwa [hι]) (fun j hj => by`. Take `rfl : j = 0` from `by omega`. Rewrite using `[hι]`.

Conclude with `(P.PD K).Fil_anti 0 h1)`. Rewrite using `[← hι]`. Conclude with `h.2.1`.
-/
theorem not_mem_two (x : P.R.B) (hx : (P.PD K).φ x = (l : P.R.B) * x) (h0 : x ≠ 0)
    (h1 : P.ιB x ∈ (P.PD K).Fil 1) : P.ιB x ∉ (P.PD K).Fil 2 := by
  haveI : IsDomain P.R.BdR := (GlobalTheory.RegularRing.isField_of_tied T).isDomain
  have hι : ∀ b, (P.PD K).ι.toRingHom b = P.ιB b := P.PD_ι K
  have hlu : IsUnit (l : P.R.B) := by
    simpa using ((Nat.cast_ne_zero.2 hl.out.ne_zero : (l : ℚ_[l]) ≠ 0).isUnit).map (algebraMap ℚ_[l] P.R.B)
  have h := GlobalTheory.MemLoc.EigenDegree.abstract (P.PD K).ι.toRingHom (P.PD K).ι_inj (P.PD K).φ.toRingHom
    (fun a y => y ∈ (P.PD K).Fil a) (P.PD K).one_mem (P.PD K).Fil_mul (l : P.R.B) (P.PD K).t hlu (P.PD K).t_unit
    (by
      have := (P.PD K).t_φ
      rwa [P.PD_p, Algebra.smul_def, map_natCast] at this) (P.PD K).not_mem_filtration_two
    (fun y hy => by
      obtain ⟨z, hz, e⟩ := ((GlobalTheory.MemLoc.TiedUnif.tied_uniformiser l P AI T).2.2 K 0 y).1 (by rwa [zero_add])
      exact ⟨z, hz, by rw [hι, P.period_datum_t_eq]; exact e⟩)
    (fun b hb hb0 hne => by
      obtain ⟨c, rfl⟩ := (P.PD K).fund b hb hb0
      have hc : c ≠ 0 := by
        rintro rfl
        exact hne (map_zero _)
      refine ⟨algebraMap ℚ_[l] P.R.B c⁻¹, by rw [← map_mul, inv_mul_cancel₀ hc, map_one], ?_⟩
      rw [hι, AlgHom.commutes, IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR]
      exact om_mem T K _) 1 one_pos x hx h0 (by rwa [hι]) (fun j hj => by
      obtain rfl : j = 0 := by omega
      rw [hι]
      exact (P.PD K).Fil_anti 0 h1)
  rw [← hι]
  exact h.2.1

def filZero : Subring P.R.BdR where
  carrier := (P.PD K).Fil 0
  mul_mem' := mul_mem_left K
  one_mem' := (P.PD K).one_mem
  add_mem' := add_mem
  zero_mem' := zero_mem _
  neg_mem' := neg_mem

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : ↥(OL K), s' (oK K c) - s (oK K c) ≠ 0 := by`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Conclude with `hs (AlgHom.coe_ringHom_injective (ringHom_extK fun c => sub_eq_zero.1 (hn c)))`. Take `⟨y, hy⟩` from `mul_dvd_norm (A := Per.Acris l) (((conj T K j s h).comp (toB K)).codRestrict (filZero K) fun x => conj_mem_Fil_zero l P AI T K j s h _) (((conj T K j s' h').comp (toB K)).codRestrict (filZero K) fun x => conj_mem_Fil_zero l P AI T K j s' h' _) (fun a => Subtype.ext ((conj_inC T K …`.

Express the relevant statement in the definitionally equal form `(conj T K j s' h' (toB K (inI K c)) - conj T K j s h (toB K (inI K c))) * algebraMap _ _ _ = 1`. Rewrite using `[← inK_oK, conj_inK, conj_inK, ← map_sub, ← map_mul, mul_inv_cancel₀ hc, map_one]))) z`. Establish `hy' : conj T K j s h (toB K (inC K (Algebra.norm (Per.Acris l) z))) = conj T K j s h (toB K z) * conj T K j s' h' (toB K z) * y.1` using `congrArg Subtype.val hy`. Rewrite `hy'` using `[conj_inC]`. Rewrite using `[hy', mul_comm]`.

Conclude with `mul_mem_left K y.2 ((P.PD K).Fil_mul 1 1 _ _ h1 h2)`.
-/
theorem norm_mem_two {j : ℕ} {s s' : ↥K.1 →ₐ[ℚ_[l]] Om l} (h : Compat T K j s) (h' : Compat T K j s') (hs : s' ≠ s)
    (z : CK K) (h1 : conj T K j s h (toB K z) ∈ (P.PD K).Fil 1) (h2 : conj T K j s' h' (toB K z) ∈ (P.PD K).Fil 1) :
    uj T j (Algebra.norm (Per.Acris l) z) ∈ (P.PD K).Fil 2 := by
  obtain ⟨c, hc⟩ : ∃ c : ↥(OL K), s' (oK K c) - s (oK K c) ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hs (AlgHom.coe_ringHom_injective (ringHom_extK fun c => sub_eq_zero.1 (hn c)))
  obtain ⟨y, hy⟩ := mul_dvd_norm (A := Per.Acris l)
    (((conj T K j s h).comp (toB K)).codRestrict (filZero K) fun x => conj_mem_Fil_zero l P AI T K j s h _)
    (((conj T K j s' h').comp (toB K)).codRestrict (filZero K) fun x => conj_mem_Fil_zero l P AI T K j s' h' _)
    (fun a => Subtype.ext ((conj_inC T K j s' h' a).trans (conj_inC T K j s h a).symm)) (inI K c)
    (IsUnit.of_mul_eq_one ⟨_, om_mem T K (s' (oK K c) - s (oK K c))⁻¹⟩ (Subtype.ext (by
      change (conj T K j s' h' (toB K (inI K c)) - conj T K j s h (toB K (inI K c))) * algebraMap _ _ _ = 1
      rw [← inK_oK, conj_inK, conj_inK, ← map_sub, ← map_mul, mul_inv_cancel₀ hc, map_one]))) z
  have hy' : conj T K j s h (toB K (inC K (Algebra.norm (Per.Acris l) z))) =
      conj T K j s h (toB K z) * conj T K j s' h' (toB K z) * y.1 := congrArg Subtype.val hy
  rw [conj_inC] at hy'
  rw [hy', mul_comm]
  exact mul_mem_left K y.2 ((P.PD K).Fil_mul 1 1 _ _ h1 h2)

/- English proof (translation)
Take `⟨y, hy⟩` from `dvd_norm (A := Per.Acris l) z`. Rewrite using `[← conj_inC T K j s h, hy, map_mul, map_mul, mul_comm]`. Conclude with `mul_mem_left K (conj_mem_Fil_zero l P AI T K j s h _) h1`.
-/
theorem norm_mem_one {j : ℕ} {s : ↥K.1 →ₐ[ℚ_[l]] Om l} (h : Compat T K j s) (z : CK K)
    (h1 : conj T K j s h (toB K z) ∈ (P.PD K).Fil 1) :
    uj T j (Algebra.norm (Per.Acris l) z) ∈ (P.PD K).Fil 1 := by
  obtain ⟨y, hy⟩ := dvd_norm (A := Per.Acris l) z
  rw [← conj_inC T K j s h, hy, map_mul, map_mul, mul_comm]
  exact mul_mem_left K (conj_mem_Fil_zero l P AI T K j s h _) h1

def basisC : Module.Basis (Module.Free.ChooseBasisIndex (W0 K) ↥(OL K)) (Per.Acris l) (CK K) :=
  Algebra.TensorProduct.basis (Per.Acris l) (Module.Free.chooseBasis (W0 K) ↥(OL K))

/- English proof (translation)
The claim follows from `Algebra.TensorProduct.basis_apply _ i`.
-/
theorem basisC_apply (i) : basisC K i = inI K (Module.Free.chooseBasis (W0 K) ↥(OL K) i) :=
  Algebra.TensorProduct.basis_apply _ i

/- English proof (translation)
The claim follows from `norm_map (basisC K) (basisC K) _ (frobC K) (fun a => by rw [frobC_inC, RingHom.coe_pow]) (fun i => by rw [basisC_apply, frobC_inI]) z`.
-/
theorem norm_frobC (z : CK K) :
    Algebra.norm (Per.Acris l) (frobC K z) = (phiA l ^ fK K) (Algebra.norm (Per.Acris l) z) :=
  norm_map (basisC K) (basisC K) _ (frobC K) (fun a => by rw [frobC_inC, RingHom.coe_pow])
    (fun i => by rw [basisC_apply, frobC_inI]) z

/- English proof (translation)
The claim follows from `norm_map (Module.Free.chooseBasis (W0 K) ↥(OL K)) (basisC K) ((aC l).comp (wA l (fK K)).toRingHom) (inI K) (fun w => (inC_wA K w).symm) (fun i => (basisC_apply K i).symm) c`.
-/
theorem norm_inI (c : ↥(OL K)) :
    Algebra.norm (Per.Acris l) (inI K c) = aC l (wA l (fK K) (Algebra.norm (W0 K) c)) :=
  norm_map (Module.Free.chooseBasis (W0 K) ↥(OL K)) (basisC K) ((aC l).comp (wA l (fK K)).toRingHom) (inI K)
    (fun w => (inC_wA K w).symm) (fun i => (basisC_apply K i).symm) c

/- English proof (translation)
Use `haveI := isDomain_CK T K`. Use `haveI := (GlobalTheory.AcrisNZD.acris_dom l).1`. Establish `hN0 : Algebra.norm (Per.Acris l) z ≠ 0` using `fun h => h0 (Algebra.norm_eq_zero_iff.1 h)`. Take `⟨u, hu, hn⟩` from `norm_unif K hπ`. Establish `hf` using `norm_frobC K z`.

Rewrite `hf` using `[hφ, map_mul, norm_inI, hn, map_mul, map_mul, map_natCast, map_natCast]`. Generalize the expression as in `Algebra.norm (Per.Acris l) z = N at hN0 hf h1 ⊢`. Take `⟨v, hv⟩` from `hu.exists_right_inv`. Take `⟨a, ha, hφa⟩` from `exists_lang K v (IsUnit.of_mul_eq_one_right u hv)`. Establish `hφa' : phiA l (aC l a) = aC l (wA l (fK K) v) * aC l a`.

Use `phiA_pow_aC 1 a` as an intermediate fact. Rewrite `this` using `[pow_one, pow_one, hφa, map_mul]`. Then use the resulting hypothesis. Establish `huv : aC l (wA l (fK K) u) * aC l (wA l (fK K) v) = 1`. Rewrite using `[← map_mul, ← map_mul, hv, map_one, map_one]`. Establish `hinj : Function.Injective (phiA l)` using `fun x y e => jB_injective T ((P.PD K).φ_inj (by rw [phi_jB, phi_jB, e]))`.

Establish `hne : ∀ j : ℕ, (phiA l ^ j) N ≠ 0` using `fun j e => hN0 (by`. Rewrite `e` using `[RingHom.coe_pow]`. Conclude with `hinj.iterate j (e.trans (iterate_map_zero _ _).symm))`. Take `⟨M, hM⟩ : ∃ M, M = ∏ j ∈ Finset.range (fK K), (phiA l ^ j) N` from `⟨_, rfl⟩`. Establish `hφM : phiA l M = (l : Per.Acris l) * aC l (wA l (fK K) u) * M`.

Apply `mul_right_cancel₀ hN0` to reduce the goal to its premises. Establish `e1` using `Finset.prod_range_succ (fun j => (phiA l ^ j) N) (fK K)`. Establish `e2` using `Finset.prod_range_succ' (fun j => (phiA l ^ j) N) (fK K)`. Establish `e3 : ∀ j, (phiA l ^ (j + 1)) N = phiA l ((phiA l ^ j) N)` using `fun j => by rw [pow_succ']; rfl`. Simplify using `only [e3] at e2`.

Rewrite `e2` using `[← map_prod, ← hM, e1, ← hM, ← hf]`. Use `e2.symm.trans ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hMu : uj T 0 M = ∏ j ∈ Finset.range (fK K), uj T j N`. Rewrite using `[hM, map_prod]`.

Conclude with `Finset.prod_congr rfl fun j _ => by rw [← uj_add, zero_add]`. Establish `hM1 : uj T 0 M ∈ (P.PD K).Fil 1`. Rewrite using `[hMu, ← Finset.mul_prod_erase _ _ (Finset.mem_range.2 (NeZero.pos (fK K))), mul_comm]`. Conclude with `mul_mem_left K (GlobalTheory.prod_mem_Fil_zero_of_factors P K _ _ fun j _ => uj_mem T K j N) h1`. Establish `hx : ∀ y, P.ιB (jB T y) = uj T 0 y` using `fun _ => rfl`.

Introduce `h2`. Use `not_mem_two T K (jB T (aC l a * M)) ?_ (fun e => ?_) ?_ ?_` and prove the remaining obligations. Rewrite using `[phi_jB, ← map_natCast (jB T), ← map_mul, map_mul, hφa', hφM]`. Use `congr 1`. Take the linear combination `((l : Per.Acris l) * aC l a * M) * huv`.

Use `mul_ne_zero (ha.map (aC l)).ne_zero ?_ (jB_injective T (e.trans (map_zero _).symm))` and prove the remaining obligations. Rewrite using `[hM]`. Conclude with `Finset.prod_ne_zero_iff.2 fun j _ => hne j`. Rewrite using `[hx, map_mul]`. Conclude with `mul_mem_left K (uj_mem T K 0 _) hM1`.

Rewrite using `[hx, map_mul, hMu]`. Conclude with `mul_mem_left K (uj_mem T K 0 _) h2`.
-/
theorem prod_not_mem_two {π : ↥(OL K)} (hπ : Irreducible π) (z : CK K) (h0 : z ≠ 0) (hφ : frobC K z = inI K π * z)
    (h1 : uj T 0 (Algebra.norm (Per.Acris l) z) ∈ (P.PD K).Fil 1) :
    ∏ j ∈ Finset.range (fK K), uj T j (Algebra.norm (Per.Acris l) z) ∉ (P.PD K).Fil 2 := by
  haveI := isDomain_CK T K
  haveI := (GlobalTheory.AcrisNZD.acris_dom l).1
  have hN0 : Algebra.norm (Per.Acris l) z ≠ 0 := fun h => h0 (Algebra.norm_eq_zero_iff.1 h)
  obtain ⟨u, hu, hn⟩ := norm_unif K hπ
  have hf := norm_frobC K z
  rw [hφ, map_mul, norm_inI, hn, map_mul, map_mul, map_natCast, map_natCast] at hf
  generalize Algebra.norm (Per.Acris l) z = N at hN0 hf h1 ⊢
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨a, ha, hφa⟩ := exists_lang K v (IsUnit.of_mul_eq_one_right u hv)
  have hφa' : phiA l (aC l a) = aC l (wA l (fK K) v) * aC l a := by
    have := phiA_pow_aC 1 a
    rwa [pow_one, pow_one, hφa, map_mul] at this
  have huv : aC l (wA l (fK K) u) * aC l (wA l (fK K) v) = 1 := by
    rw [← map_mul, ← map_mul, hv, map_one, map_one]
  have hinj : Function.Injective (phiA l) := fun x y e =>
    jB_injective T ((P.PD K).φ_inj (by rw [phi_jB, phi_jB, e]))
  have hne : ∀ j : ℕ, (phiA l ^ j) N ≠ 0 := fun j e => hN0 (by
    rw [RingHom.coe_pow] at e
    exact hinj.iterate j (e.trans (iterate_map_zero _ _).symm))
  obtain ⟨M, hM⟩ : ∃ M, M = ∏ j ∈ Finset.range (fK K), (phiA l ^ j) N := ⟨_, rfl⟩
  have hφM : phiA l M = (l : Per.Acris l) * aC l (wA l (fK K) u) * M := by
    apply mul_right_cancel₀ hN0
    have e1 := Finset.prod_range_succ (fun j => (phiA l ^ j) N) (fK K)
    have e2 := Finset.prod_range_succ' (fun j => (phiA l ^ j) N) (fK K)
    have e3 : ∀ j, (phiA l ^ (j + 1)) N = phiA l ((phiA l ^ j) N) := fun j => by rw [pow_succ']; rfl
    simp only [e3] at e2
    rw [← map_prod, ← hM, e1, ← hM, ← hf] at e2
    refine e2.symm.trans ?_
    ring
  have hMu : uj T 0 M = ∏ j ∈ Finset.range (fK K), uj T j N := by
    rw [hM, map_prod]
    exact Finset.prod_congr rfl fun j _ => by rw [← uj_add, zero_add]
  have hM1 : uj T 0 M ∈ (P.PD K).Fil 1 := by
    rw [hMu, ← Finset.mul_prod_erase _ _ (Finset.mem_range.2 (NeZero.pos (fK K))), mul_comm]
    exact mul_mem_left K (GlobalTheory.prod_mem_Fil_zero_of_factors P K _ _ fun j _ => uj_mem T K j N) h1
  have hx : ∀ y, P.ιB (jB T y) = uj T 0 y := fun _ => rfl
  intro h2
  refine not_mem_two T K (jB T (aC l a * M)) ?_ (fun e => ?_) ?_ ?_
  · rw [phi_jB, ← map_natCast (jB T), ← map_mul, map_mul, hφa', hφM]
    congr 1
    linear_combination ((l : Per.Acris l) * aC l a * M) * huv
  · refine mul_ne_zero (ha.map (aC l)).ne_zero ?_ (jB_injective T (e.trans (map_zero _).symm))
    rw [hM]
    exact Finset.prod_ne_zero_iff.2 fun j _ => hne j
  · rw [hx, map_mul]
    exact mul_mem_left K (uj_mem T K 0 _) hM1
  · rw [hx, map_mul, hMu]
    exact mul_mem_left K (uj_mem T K 0 _) h2

/- English proof (translation)
Introduce `w` and use `by rw [← h w, uj_add, phiA_pow_aC, iter_wA]`.
-/
theorem compat_of_add {j : ℕ} {s : ↥K.1 →ₐ[ℚ_[l]] Om l} (h : Compat T K (j + fK K) s) : Compat T K j s := fun w => by
  rw [← h w, uj_add, phiA_pow_aC, iter_wA]

/- English proof (translation)
The claim follows from `RingHom.congr_fun (GlobalTheory.PZ.ColmezVec.ext_BK (conj T K (j + fK K) s h) ((conj T K j s (compat_of_add T K h)).comp (frobB K)) (fun c => by rw [RingHom.comp_apply, frobB_inK, conj_inK, conj_inK]) fun a => by rw [RingHom.comp_apply, frobB_toB, frobC_inC, conj_inC, conj_inC, u …`.
-/
theorem conj_add {j : ℕ} {s : ↥K.1 →ₐ[ℚ_[l]] Om l} (h : Compat T K (j + fK K) s) (b : BK K) :
    conj T K (j + fK K) s h b = conj T K j s (compat_of_add T K h) (frobB K b) :=
  RingHom.congr_fun (GlobalTheory.PZ.ColmezVec.ext_BK (conj T K (j + fK K) s h)
    ((conj T K j s (compat_of_add T K h)).comp (frobB K))
    (fun c => by rw [RingHom.comp_apply, frobB_inK, conj_inK, conj_inK])
    fun a => by rw [RingHom.comp_apply, frobB_toB, frobC_inC, conj_inC, conj_inC, uj_add, RingHom.coe_pow]) b

/- English proof (translation)
Take `⟨D, z, hz⟩` from `exists_pow_mul t`. Establish `hz0 : z ≠ 0` using `fun e => h0 (((isUnit_l K).pow D).mul_right_eq_zero.1 (by rw [hz, e, map_zero]))`. Establish `hφz : frobC K z = inI K π * z` using `toB_injective K (by`. Rewrite using `[← frobB_toB, map_mul, ← hz, map_mul, map_pow, map_natCast, hφ, ← inK_oK, mul_left_comm]`. Use the proof step `rfl)`.

Establish `hmem : ∀ (j : ℕ) (s : ↥K.1 →ₐ[ℚ_[l]] Om l) (h : Compat T K j s), conj T K j s h t ∈ (P.PD K).Fil 1 → conj T K j s h (toB K z) ∈ (P.PD K).Fil 1` using `fun j s h hm => by`. Rewrite using `[← hz, map_mul]`. Conclude with `mul_mem_left K (conj_mem_Fil_zero l P AI T K j s h _) hm`. Establish `hN1` using `norm_mem_one T K _ z (hmem _ _ _ h1)`. Take `⟨hA, hB⟩` from `GlobalTheory.prod_degree_of_not_mem_Fil_two l P K (Finset.range (fK K)) (fun j => uj T j (Algebra.norm (Per.Acris l) z)) 0 (Finset.mem_range.2 (NeZero.pos (fK K))) (fun j _ => uj_mem T K j _) hN1 (prod_not_mem_two T K hπ z hz0 hφz hN1)`.

Proceed by induction on `j using Nat.strong_induction_on with`. Consider the case `_ j ih`. Introduce `hm`. Break down `lt_or_ge j (fK K) with hj | hj` into its components or cases. Break down `eq_or_ne j 0 with rfl | hj0` into its components or cases.

Conclude with `hA (norm_mem_two T K _ h hs z (hmem _ _ _ h1) (hmem _ _ _ hm))`. Conclude with `hB j (Finset.mem_range.2 hj) hj0 (norm_mem_one T K h z (hmem _ _ _ hm))`. Take `⟨i, rfl⟩` from `Nat.exists_eq_add_of_le' hj`. Use `ih i (Nat.lt_add_of_pos_right (NeZero.pos (fK K))) (compat_of_add T K h) ?_` and prove the remaining obligations. Rewrite `hm` using `[conj_add, hφ, map_mul, conj_inK]`.

Establish `hp : s (π : ↥K.1) ≠ 0` using `(map_ne_zero s).2 fun e => hπ.ne_zero (Subtype.ext e)`. Use `mul_mem_left K (om_mem T K (s (π : ↥K.1))⁻¹) hm` as an intermediate fact. Rewrite `this` using `[← mul_assoc, ← map_mul, inv_mul_cancel₀ hp, map_one, one_mul]`. Then use the resulting hypothesis.
-/
theorem conj_not_mem {π : ↥(OL K)} (hπ : Irreducible π) (t : BK K) (h0 : t ≠ 0)
    (hφ : frobB K t = inK K (π : ↥K.1) * t) (h1 : conj T K 0 K.1.val (compat_zero T K) t ∈ (P.PD K).Fil 1)
    (j : ℕ) (s : ↥K.1 →ₐ[ℚ_[l]] Om l) (h : Compat T K j s) (hs : s ≠ K.1.val) :
    conj T K j s h t ∉ (P.PD K).Fil 1 := by
  obtain ⟨D, z, hz⟩ := exists_pow_mul t
  have hz0 : z ≠ 0 := fun e => h0 (((isUnit_l K).pow D).mul_right_eq_zero.1 (by rw [hz, e, map_zero]))
  have hφz : frobC K z = inI K π * z := toB_injective K (by
    rw [← frobB_toB, map_mul, ← hz, map_mul, map_pow, map_natCast, hφ, ← inK_oK, mul_left_comm]
    rfl)
  have hmem : ∀ (j : ℕ) (s : ↥K.1 →ₐ[ℚ_[l]] Om l) (h : Compat T K j s), conj T K j s h t ∈ (P.PD K).Fil 1 →
      conj T K j s h (toB K z) ∈ (P.PD K).Fil 1 := fun j s h hm => by
    rw [← hz, map_mul]
    exact mul_mem_left K (conj_mem_Fil_zero l P AI T K j s h _) hm
  have hN1 := norm_mem_one T K _ z (hmem _ _ _ h1)
  obtain ⟨hA, hB⟩ := GlobalTheory.prod_degree_of_not_mem_Fil_two l P K (Finset.range (fK K))
    (fun j => uj T j (Algebra.norm (Per.Acris l) z)) 0 (Finset.mem_range.2 (NeZero.pos (fK K)))
    (fun j _ => uj_mem T K j _) hN1 (prod_not_mem_two T K hπ z hz0 hφz hN1)
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hm
    rcases lt_or_ge j (fK K) with hj | hj
    · rcases eq_or_ne j 0 with rfl | hj0
      · exact hA (norm_mem_two T K _ h hs z (hmem _ _ _ h1) (hmem _ _ _ hm))
      · exact hB j (Finset.mem_range.2 hj) hj0 (norm_mem_one T K h z (hmem _ _ _ hm))
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hj
      refine ih i (Nat.lt_add_of_pos_right (NeZero.pos (fK K))) (compat_of_add T K h) ?_
      rw [conj_add, hφ, map_mul, conj_inK] at hm
      have hp : s (π : ↥K.1) ≠ 0 := (map_ne_zero s).2 fun e => hπ.ne_zero (Subtype.ext e)
      have := mul_mem_left K (om_mem T K (s (π : ↥K.1))⁻¹) hm
      rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hp, map_one, one_mul] at this

/- English proof (translation)
Introduce `l _ P AI T K χ π z hD`. Take `⟨ω, t, u, hω, ht, h0, hφ, hg⟩` from `exists_period K χ π z hD`. Use `⟨t, hg, conj_not_mem T K hD.1 t h0 hφ ?_⟩` and prove the remaining obligations. Rewrite using `[ht, map_mul, mul_comm]`. Conclude with `mul_mem_left K (conj_mem_Fil_zero l P AI T K 0 _ _ u) (conj_zero_mem T K ω hω)`.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l), LTData K χ π z →
    ∃ t : BK K, (∀ g : ↥(GK K), galB g t = inK K (χ g : ↥K.1) * t) ∧
      ∀ (j : ℕ) (s : ↥K.1 →ₐ[ℚ_[l]] Om l) (h : Compat T K j s), s ≠ K.1.val →
        conj T K j s h t ∉ (P.PD K).Fil 1 := by
  intro l _ P AI T K χ π z hD
  obtain ⟨ω, t, u, hω, ht, h0, hφ, hg⟩ := exists_period K χ π z hD
  refine ⟨t, hg, conj_not_mem T K hD.1 t h0 hφ ?_⟩
  rw [ht, map_mul, mul_comm]
  exact mul_mem_left K (conj_mem_Fil_zero l P AI T K 0 _ _ u) (conj_zero_mem T K ω hω)

end GlobalTheory.ConjDegree

end
