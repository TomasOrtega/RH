import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOneOfCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalStrongMultiplicityOneOfAnalytic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyFactorizationSemisimple
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature

noncomputable section

namespace GlobalTheory.ResLoc

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie
  GlobalTheory.SplitRead GlobalTheory.XiOver Formalism.L2.Host

/- English proof (translation)
Introduce `i`. Take `⟨ρ, hρ, hwd, -⟩` from `(h2 i).2.2 D.naut.etaTinv (-(D.R.t : ℝ) / 2) (inf_int D hA)`. Establish `hun : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.unr (D.naut.wdOf i ρ w)` using `fun w hw => by`. Rewrite using `[hwd w hw]`. Conclude with `(D.naut.unr_tw _ _).2 (D.naut.etaTinv_def w).1`.

Establish `hfrob : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om), IsPlaceOver (F` using `D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ → D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) = {D.naut.iotaQC i (((ρ σ : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0)} := by`. Introduce `w hw B σ hB hσ`. Establish `e` using `D.naut.wdOf_frob i ρ w hw hρ (hun w hw) B σ hB hσ`. Take `⟨a, ha⟩` from `Multiset.card_eq_one.1 ((D.naut.frobEig_card _ (hun w hw)).trans (D.naut.wdOf_dim i ρ w))`. Rewrite `e` using `[ha, charpoly_fin_one]`.

Simplify using `only [Multiset.map_singleton, Multiset.prod_singleton, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at e`. Establish `e2` using `C_injective (sub_right_injective e)`. Rewrite using `[← hwd w hw, ha]`. Conclude with `congrArg _ e2.symm`. Set `d : G D.host.E D.nd.Om →* Qbar (D.nd.l i)` to `(Units.coeHom _).comp (Matrix.GeneralLinearGroup.det.comp ρ)`.

Establish `hde : ∀ g, d g = ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0` using `fun g => Matrix.det_fin_one _`. Establish `hd : Continuous d`. Establish `: (d : G D.host.E D.nd.Om → Qbar (D.nd.l i)) = fun g => ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0` using `funext hde`. Rewrite using `[this]`. Conclude with `(continuous_apply_apply 0 0).comp hρ`.

Establish `hfin : (placesOver D.host.E (D.nd.l i)).Finite` using `GlobalTheory.SplitRead.finite_placesOver _ (Fact.out : (D.nd.l i).Prime).ne_zero`. Establish `hS : closure {σ : G D.host.E D.nd.Om | ∃ w ∉ placesOver D.host.E (D.nd.l i), IsSplitPl D.host w ∧ ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F` using `D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ} = Set.univ := by`. Establish `hd` using `(h5 hfin.toFinset).closure_eq`. Use `hd using 4 with σ` and compare the differences between its conclusion and the goal. Simplify using `[Set.Finite.mem_toFinset]`.

Take `⟨ξ, hξc, hξ⟩` from `exists_integral_char D.nd D.naut i d hd _ hS (by`. Introduce and unpack `σ ⟨w, hw, -, B, hB, hσ⟩`. Take `⟨x, hx⟩` from `frob_value D C nch Tp T V w`. Establish `e` using `hfrob w hw B σ hB hσ`. Rewrite `e` using `[hx, Multiset.singleton_inj, ← D.naut.iota_LL i x, ← hde]`.

Conclude with `⟨_, (D.naut.iotaQC i).injective e⟩)`. Use `⟨ξ, hξc, fun w hw => ⟨fun σ hσ => ?_, fun B σ hB hσ => ?_⟩⟩` and prove the remaining obligations. Establish `h1` using `(D.naut.wdOf_unr i ρ w hw hρ).1 (hun w hw) σ hσ`. Apply `Units.ext` to reduce the goal to its premises. Apply `iota_inj D.nd D.naut i` to reduce the goal to its premises.

Rewrite using `[hξ, hde, h1]`. Simplify using the standard rewrite rules. Rewrite using `[hfrob w hw B σ hB hσ, ← hde, ← hξ]`. Both sides reduce to the same expression.
-/
theorem xiOverO (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch)
    (T : Formalism.L2.Host.NCharTied D C nch Tp) (V : Formalism.L2.Host.ValLL0 D C) (hA : Formalism.MainNotions.SumRepresentations.At.TieAut D.nd D.naut)
    (h2 : Formalism.MainNotions.SumRepresentations.adm2 D) (h5 : ChebSplit D.nd) : XiOverO D.nd D.naut := by
  intro i
  obtain ⟨ρ, hρ, hwd, -⟩ := (h2 i).2.2 D.naut.etaTinv (-(D.R.t : ℝ) / 2) (inf_int D hA)
  have hun : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.unr (D.naut.wdOf i ρ w) := fun w hw => by
    rw [hwd w hw]
    exact (D.naut.unr_tw _ _).2 (D.naut.etaTinv_def w).1
  have hfrob : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
      D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) =
        {D.naut.iotaQC i (((ρ σ : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0)} := by
    intro w hw B σ hB hσ
    have e := D.naut.wdOf_frob i ρ w hw hρ (hun w hw) B σ hB hσ
    obtain ⟨a, ha⟩ := Multiset.card_eq_one.1
      ((D.naut.frobEig_card _ (hun w hw)).trans (D.naut.wdOf_dim i ρ w))
    rw [ha, charpoly_fin_one] at e
    simp only [Multiset.map_singleton, Multiset.prod_singleton, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C] at e
    have e2 := C_injective (sub_right_injective e)
    rw [← hwd w hw, ha]
    exact congrArg _ e2.symm
  let d : G D.host.E D.nd.Om →* Qbar (D.nd.l i) :=
    (Units.coeHom _).comp (Matrix.GeneralLinearGroup.det.comp ρ)
  have hde : ∀ g, d g = ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 :=
    fun g => Matrix.det_fin_one _
  have hd : Continuous d := by
    have : (d : G D.host.E D.nd.Om → Qbar (D.nd.l i)) = fun g =>
        ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 := funext hde
    rw [this]
    exact (continuous_apply_apply 0 0).comp hρ
  have hfin : (placesOver D.host.E (D.nd.l i)).Finite :=
    GlobalTheory.SplitRead.finite_placesOver _ (Fact.out : (D.nd.l i).Prime).ne_zero
  have hS : closure {σ : G D.host.E D.nd.Om | ∃ w ∉ placesOver D.host.E (D.nd.l i), IsSplitPl D.host w ∧
      ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ} = Set.univ := by
    have hd := (h5 hfin.toFinset).closure_eq
    convert hd using 4 with σ
    simp [Set.Finite.mem_toFinset]
  obtain ⟨ξ, hξc, hξ⟩ := exists_integral_char D.nd D.naut i d hd _ hS (by
    rintro σ ⟨w, hw, -, B, hB, hσ⟩
    obtain ⟨x, hx⟩ := frob_value D C nch Tp T V w
    have e := hfrob w hw B σ hB hσ
    rw [hx, Multiset.singleton_inj, ← D.naut.iota_LL i x, ← hde] at e
    exact ⟨_, (D.naut.iotaQC i).injective e⟩)
  refine ⟨ξ, hξc, fun w hw => ⟨fun σ hσ => ?_, fun B σ hB hσ => ?_⟩⟩
  · have h1 := (D.naut.wdOf_unr i ρ w hw hρ).1 (hun w hw) σ hσ
    apply Units.ext
    apply iota_inj D.nd D.naut i
    rw [hξ, hde, h1]
    simp
  · rw [hfrob w hw B σ hB hσ, ← hde, ← hξ]
    rfl

end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.LocalInv
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts GlobalTheory.ParamRep

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

/- English proof (translation)
Establish `e2 : (heckePol N i x w).map (iotaO N A i) = galPol A (A.lpTw (A.locV i P w) ((1 - (R.nV : ℝ)) / 2))` using `A.pt_loc i P x hP w hw`. Establish `s1` using `galPol_speh N A ⟨R.r, A.tw π A.etaTinv, 1⟩ w hu ((1 - (R.nV : ℝ)) / 2)`. Establish `s2` using `galPol_speh N A ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ w (A.chi_mu i w hw).1 ((1 - (R.nV : ℝ)) / 2)`. Establish `e4 : isoLoc N A (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A i]) A.etaTinv) w = A.lpSum (spehLoc N A ⟨R.r, A.tw π A.etaTinv, 1⟩ w) (A.lpSum (spehLoc N A ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ w) (A.lpZero w))` using `rfl`. Establish `e5 : ∏ c ∈ Finset.Icc 1 R.t, (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)).map (iotaO N A i) = ∏ k ∈ Finset.range R.t, galPol A (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w) (((R.t : ℝ) - 1) / 2 - k + (1 - (R.nV : ℝ)) / 2))`.

Rewrite using `[← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]`. Use `Finset.prod_congr rfl fun k hk => ?_` and prove the remaining obligations. Establish `hx : ((R.t : ℝ) - 1) / 2 - k + (1 - (R.nV : ℝ)) / 2 = ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + (-(k : ℝ))` using `by ring`. Rewrite using `[hx, galPol_block N A i hw hBw hσ, add_comm 1 k, chi_apply N i k (Finset.mem_range.mp hk)]`. Establish `hq` using `iota_eps N A i hw.2.1 hBw hσ`.

Establish `hinv : iotaO N A i ((((eps N i σ) ^ k)⁻¹ : (N.O i)ˣ) : N.O i) = ((normV w : ℕ) : ℂ) ^ (((-(k : ℝ) : ℝ)) : ℂ)`. Rewrite using `[Complex.ofReal_neg, Complex.cpow_neg, Complex.ofReal_natCast, Complex.cpow_natCast, ← hq, map_units_inv, Units.val_pow_eq_pow_val, map_pow]`. Rewrite using `[Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Units.val_mul, map_mul, hinv]`. Rewrite using `[e2, ← e3, e4, A.lpSum_zero, galPol_tw_sum N A _ _ s1.1 s2.1, s1.2, s2.2, e5]`. Simplify using the standard rewrite rules.
-/
theorem hecke_of_loc (i : N.Loc) (x : N.X i) (π : A.CG R.r) (P : A.AV i) (hP : A.ptV i P = some x)
    {w : PlE H} (e3 : isoLoc N A (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A i]) A.etaTinv) w = A.locV i P w)
    (hw : SplitOut N i w) (hu : A.unr (A.locG (A.tw π A.etaTinv) w))
    {B : ValuationSubring N.Om} {σ : G H.E N.Om} (hBw : IsPlaceOver (F := H.E) B w)
    (hσ : IsFrob (F := H.E) B (normV w) σ) :
    (heckePol N i x w).map (iotaO N A i) =
      galPol A (A.lpTw (A.locG (A.tw π A.etaTinv) w) ((1 - (R.nV : ℝ)) / 2)) *
        ∏ c ∈ Finset.Icc 1 R.t, (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)).map (iotaO N A i) := by
  have e2 : (heckePol N i x w).map (iotaO N A i) =
      galPol A (A.lpTw (A.locV i P w) ((1 - (R.nV : ℝ)) / 2)) := A.pt_loc i P x hP w hw
  have s1 := galPol_speh N A ⟨R.r, A.tw π A.etaTinv, 1⟩ w hu ((1 - (R.nV : ℝ)) / 2)
  have s2 := galPol_speh N A ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ w (A.chi_mu i w hw).1
    ((1 - (R.nV : ℝ)) / 2)
  have e4 : isoLoc N A (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A i]) A.etaTinv) w =
      A.lpSum (spehLoc N A ⟨R.r, A.tw π A.etaTinv, 1⟩ w)
        (A.lpSum (spehLoc N A ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ w) (A.lpZero w)) := rfl
  have e5 : ∏ c ∈ Finset.Icc 1 R.t,
        (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)).map (iotaO N A i) =
      ∏ k ∈ Finset.range R.t, galPol A (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w)
        (((R.t : ℝ) - 1) / 2 - k + (1 - (R.nV : ℝ)) / 2)) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hx : ((R.t : ℝ) - 1) / 2 - k + (1 - (R.nV : ℝ)) / 2 =
        ((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + (-(k : ℝ)) := by ring
    rw [hx, galPol_block N A i hw hBw hσ, add_comm 1 k, chi_apply N i k (Finset.mem_range.mp hk)]
    have hq := iota_eps N A i hw.2.1 hBw hσ
    have hinv : iotaO N A i ((((eps N i σ) ^ k)⁻¹ : (N.O i)ˣ) : N.O i) =
        ((normV w : ℕ) : ℂ) ^ (((-(k : ℝ) : ℝ)) : ℂ) := by
      rw [Complex.ofReal_neg, Complex.cpow_neg, Complex.ofReal_natCast, Complex.cpow_natCast, ← hq,
        map_units_inv, Units.val_pow_eq_pow_val, map_pow]
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Units.val_mul, map_mul, hinv]
  rw [e2, ← e3, e4, A.lpSum_zero, galPol_tw_sum N A _ _ s1.1 s2.1, s1.2, s2.2, e5]
  simp

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `g`. Rewrite using `[ContinuousAt, ← tendsto_sub_nhds_zero_iff, (N.O_adic i).hasBasis_nhds_zero.tendsto_right_iff]`. Introduce `k _`. Take `⟨δ, hδ, hk⟩` from `GlobalTheory.XiOver.mem_pow_of_norm_lt N A i k`.

Establish `hcd : ∀ᶠ x in nhds g, ‖iotaOQ N A i (u x) - iotaOQ N A i (u g)‖ < δ` using `(Metric.tendsto_nhds.1 (hd.tendsto g) δ hδ).mono fun x hx => by simpa [dist_eq_norm] using hx`. Use `filter_upwards [hcd] with x hx`. Apply `hk` to reduce the goal to its premises. Rewrite using `[map_sub]`. Conclude with `hx`.
-/
theorem continuous_of_iota (i : N.Loc) {Y : Type} [TopologicalSpace Y] (u : Y → N.O i)
    (hd : Continuous fun y => iotaOQ N A i (u y)) : Continuous u := by
  rw [continuous_iff_continuousAt]
  intro g
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff, (N.O_adic i).hasBasis_nhds_zero.tendsto_right_iff]
  intro k _
  obtain ⟨δ, hδ, hk⟩ := GlobalTheory.XiOver.mem_pow_of_norm_lt N A i k
  have hcd : ∀ᶠ x in nhds g, ‖iotaOQ N A i (u x) - iotaOQ N A i (u g)‖ < δ :=
    (Metric.tendsto_nhds.1 (hd.tendsto g) δ hδ).mono fun x hx => by simpa [dist_eq_norm] using hx
  filter_upwards [hcd] with x hx
  apply hk
  rw [map_sub]
  exact hx

/- English proof (translation)
Use `haveI : IsGalois H.E N.Om := {}`. Take `⟨ξ, hξc, hξ⟩` from `hXi a`. Establish `hιc : Continuous (iotaOQ N A a)` using `GlobalTheory.CoeffEmbedding.continuous_iotaOQ_of_data N A a`. Establish `hcomp : iotaO N A a = (A.iotaQC a).toRingHom.comp (iotaOQ N A a)` using `rfl`. Establish `hinj : Function.Injective (Polynomial.map (A.iotaQC a).toRingHom)` using `Polynomial.map_injective _ (A.iotaQC a).injective`.

Set `R1` to `Formalism.MainNotions.SumRepresentations.At.twGL ρ₀ ((Units.map (iotaOQ N A a).toMonoidHom).comp ξ)`. Establish `hR1 : ∀ g, ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))) = iotaOQ N A a ((ξ g : (N.O a)ˣ) : N.O a) • ((ρ₀ g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a)))` using `fun g => coe_twGL _ _ g`. Establish `hR1c : Continuous fun g => ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a)))`. Simplify using `only [hR1]`. Conclude with `(hιc.comp hξc).smul hc0`.

Establish `hR1C : ∀ g, ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).map (A.iotaQC a).toRingHom = iotaO N A a ((ξ g : (N.O a)ˣ) : N.O a) • ((ρ₀ g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).map (A.iotaQC a).toRingHom`. Introduce `g`. Rewrite using `[hR1, map_smul_matrix]`. Both sides reduce to the same expression. Establish `hfin` using `placesOver_finite_joint_conditions_zpowers H.E (N.l a) (N.lPrime a).out.ne_zero`.

Set `χ : Fin R.t → G H.E N.Om →* (Qbar (N.l a))ˣ` to `fun c => (Units.map (iotaOQ N A a).toMonoidHom).comp (N.chi a ((c : ℕ) + 1))`. Set `Rq : G H.E N.Om →* GL (Fin (R.r + R.t)) (Qbar (N.l a))` to `(GlobalTheory.SSComplement.blockM finSumFinEquiv R1 (GlobalTheory.SSComplement.diagM χ).toHomUnits).toHomUnits`. Establish `hRq : ∀ g, ((Rq g : GL _ _) : Matrix (Fin (R.r + R.t)) (Fin (R.r + R.t)) (Qbar (N.l a))) = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))) 0 0 (Matrix.diagonal fun c : Fin R.t => iotaOQ N A a ((N.chi a …` using `fun g => rfl`. Establish `hRqc : Continuous fun g => ((Rq g : GL _ _) : Matrix (Fin (R.r + R.t)) (Fin (R.r + R.t)) (Qbar (N.l a)))`. Simplify using `only [hRq]`.

Use `Continuous.matrix_reindex ?_ _ _` and prove the remaining obligations. Use `Continuous.matrix_fromBlocks hR1c continuous_const continuous_const ?_` and prove the remaining obligations. Conclude with `Continuous.matrix_diagonal (continuous_pi fun c => hιc.comp (N.chi_cont a _))`. Establish `hRqs : IsSSRep Rq` using `GlobalTheory.SSComplement.blockM_ss _ _ _ (isSSRep_twGL _ _ hs0) (GlobalTheory.SSComplement.diagM_ss χ)`. Establish `hq : Formalism.MainNotions.SumRepresentations.At.IsHeckeGaloisQ N A a x Rq`.

Use `⟨hRqc, hRqs, fun v hso B g hBv hg => ?_⟩` and prove the remaining obligations. Establish `h4 : A.unr (A.locG π v)` using `hun v fun k hk => hso.2.2.1 ((N.S_def a v).2 ⟨by fin_cases k`. Conclude with `Or.inl hk`. Conclude with `Or.inr (Or.inl hk), hso.2.1⟩)`. Establish `h5 : A.unr (A.locG (A.tw π A.etaTinv) v)`.

Rewrite using `[A.locG_tw]`. Conclude with `A.unr_char _ _ (A.locG_dim _ _) h4 (A.etaTinv_def v).1`. Establish `h1` using `hso.2.1`. Establish `e3 : isoLoc N A (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A a]) A.etaTinv) v = A.locV a P v`. Rewrite using `[GlobalTheory.Proof.SplitPlaceGoodSignature.isoLoc_lift N A hLaw, hloc v hso.1]`.

Use `congr 1`. Simplify using `[isoLoc, spehLoc, A.lpSum_zero, A.lpTw_zero]`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[Polynomial.map_map, ← hcomp]`. Use `Eq.trans (congrArg (Polynomial.map (A.iotaQC a).toRingHom) ((congrArg Matrix.charpoly (hRq g)).trans (charpoly_block _ _))) ?_` and prove the remaining obligations.

Use `symm`. Rewrite using `[Polynomial.map_mul, ← Matrix.charpoly_map, hR1C g, hecke_of_loc N A a x π P hP e3 hso h5 hBv hg, galPol_twist N A π h4 _ ((hξ v h1).2 B g hBv hg), charpoly_smul_of_prod _ _ _ (hfr v h1 h4 B g hBv hg), prod_Icc_eq_fin, Polynomial.map_prod]`. Use `congr 1`. Use `Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]`.

Both sides reduce to the same expression. Take `⟨rf, Pm, hPm⟩` from `hO a x Rq hq`. Establish `hval : ∀ g, ((rf g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a)).map (iotaOQ N A a) = ((Pm⁻¹ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l a))) * (show Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l a)) from ((Rq g : GL _ _) : Matrix (Fin (R.r + R.t)) (Fin (R.r + R.t)) (Qbar ( …` using `fun g => congrArg Units.val (hPm g)`. Establish `hrc : Continuous fun g => ((rf g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a))`. Establish `hc : Continuous fun g => ((rf g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a)).map (iotaOQ N A a)`.

Simplify using `only [hval]`. Conclude with `(continuous_const.mul hRqc).mul continuous_const`. Conclude with `continuous_pi fun p => continuous_pi fun q => continuous_of_iota N A a _ (hc.matrix_elem p q)`. Establish `hrs : IsSSRep (mapRep (algebraMap (N.O a) (Kf N a)) rf)`. Use `GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_of_mapRep (A.iotaQ a) _ ?_` and prove the remaining obligations.

Rewrite using `[GlobalTheory.RowRepOcc.mapRep_mapRep]`. Conclude with `GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_conj (ρ := (Rq : G H.E N.Om →* GL (Fin R.nV) (Qbar (N.l a)))) Pm⁻¹ (fun g => hPm g) hRqs`. Use `haveI : CharZero (Qbar (N.l a)) := (RingHom.charZero_iff (A.iotaQC a).toRingHom.injective).2 inferInstance`. Use `haveI : CharZero (Kf N a) := (RingHom.charZero_iff (A.iotaQ a).injective).2 inferInstance`. Establish `hkey' : ∀ g, (((rf g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a))).charpoly.map (iotaOQ N A a) = ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).charpoly * ∏ c : Fin R.t, (X - C (iotaOQ N A a ((N.chi a ((c : ℕ) + 1) g : (N.O a)ˣ) : N.O a)))`.

Introduce `g`. Rewrite using `[← Matrix.charpoly_map, hval g, Matrix.coe_units_inv, Matrix.charpoly_units_conj']`. Conclude with `(congrArg Matrix.charpoly (hRq g)).trans (charpoly_block _ _)`. Take `⟨ρ', hρc, hρs, hρp⟩` from `GlobalTheory.LatticeComplement.exists_lattice_complement (G H.E N.Om) (N.O a) (Kf N a) R.r R.t (rf) (fun c : Fin R.t => N.chi a ((c : ℕ) + 1)) hrc hrs ⟨Qbar (N.l a), inferInstance, A.iotaQ a, R1, hkey'⟩`. Establish `hcan : ∀ g, ((ρ' g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a)).charpoly.map (iotaOQ N A a) = ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).charpoly`.

Introduce `g`. Establish `e1 : (((rf g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a))).charpoly.map (iotaOQ N A a) = ((ρ' g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a)).charpoly.map (iotaOQ N A a) * ∏ c : Fin R.t, (X - C (iotaOQ N A a ((N.chi a ((c : ℕ) + 1) g : (N.O a)ˣ) : N.O a)))`. Use `congrArg (Polynomial.map (iotaOQ N A a)) (hρp g)` as an intermediate fact. Rewrite `this` using `[Polynomial.map_mul, Polynomial.map_prod]`. Use `this.trans ?_` and prove the remaining obligations.

Use `congr 1`. Use `Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]`. Establish `hne : (∏ c : Fin R.t, (X - C (iotaOQ N A a ((N.chi a ((c : ℕ) + 1) g : (N.O a)ˣ) : N.O a)))) ≠ 0` using `(monic_prod_of_monic _ _ fun c _ => monic_X_sub_C _).ne_zero`. Conclude with `mul_right_cancel₀ hne (e1.symm.trans (hkey' g))`.

Use `⟨Formalism.MainNotions.SumRepresentations.At.twGL ρ' ξ⁻¹, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e : (fun g => ((Formalism.MainNotions.SumRepresentations.At.twGL ρ' ξ⁻¹ g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a))) = fun g => ((ξ g⁻¹ : (N.O a)ˣ) : N.O a) • ((ρ' g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a))`. Use function extensionality and compare the values at `g`. Rewrite using `[coe_twGL, MonoidHom.inv_apply, map_inv]`. Rewrite using `[e]`.

Conclude with `(hξc.comp continuous_inv).smul hρc`. Rewrite using `[mapRep_twGL]`. Conclude with `isSSRep_twGL _ _ hρs`. Use `filter_upwards [hfin.eventually_cofinite_notMem, A.locG_unr_ae π] with w h1 h2 B σ hBw hσ`. Establish `iso : isoLoc N A [⟨R.r, π, 1⟩] w = A.locG π w`.

Simplify using `[isoLoc, spehLoc, A.lpSum_zero, A.lpTw_zero]`. Rewrite using `[iso]`. Establish `h0` using `hfr w h1 h2 B σ hBw hσ`. Establish `c1 : (((ρ' σ : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a)).map (iotaO N A a)).charpoly = (((A.frobEig (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2))).map (· * iotaO N A a ((ξ σ : (N.O a)ˣ) : N.O a))).map fun α => X - C α).prod`. Rewrite using `[Matrix.charpoly_map, hcomp, ← Polynomial.map_map, hcan σ, ← Matrix.charpoly_map, hR1C σ]`.

Conclude with `charpoly_smul_of_prod _ _ _ h0`. Establish `c2` using `charpoly_smul_of_prod _ (iotaO N A a (((ξ⁻¹ σ : (N.O a)ˣ)) : N.O a)) _ c1`. Establish `huv : iotaO N A a ((ξ σ : (N.O a)ˣ) : N.O a) * iotaO N A a (((ξ⁻¹ σ : (N.O a)ˣ)) : N.O a) = 1`. Rewrite using `[← map_mul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel]`. Simplify using the standard rewrite rules.

Establish `hL : ((A.frobEig (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2))).map (· * iotaO N A a ((ξ σ : (N.O a)ˣ) : N.O a))).map (· * iotaO N A a (((ξ⁻¹ σ : (N.O a)ˣ)) : N.O a)) = A.frobEig (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2))`. Rewrite using `[Multiset.map_map]`. Use `(Multiset.map_congr rfl fun α _ => ?_).trans (Multiset.map_id _)` and prove the remaining obligations. Use `show α * _ * _ = α`. Rewrite using `[mul_assoc, huv, mul_one]`.

Rewrite using `[← Matrix.charpoly_map, coe_twGL, map_smul_matrix, c2, hL]`. Both sides reduce to the same expression.
-/
theorem lattice_of_point (hLaw : GlobalTheory.ThetaExh.ParamLaws N A) (hO : Formalism.MainNotions.SumRepresentations.At.OLarge N A)
    (hXi : GlobalTheory.SplitRead.XiOverO N A) (a : N.Loc) (x : N.X a) (P : A.AV a) (hP : A.ptV a P = some x) (π : A.CG R.r)
    (hloc : ∀ w, IsSplitPl H w → A.locV a P w = GlobalTheory.ThetaExh.liftPar N A a w (A.locG π w))
    (hun : ∀ w, (∀ k, w ∉ placesOver H.E (H.g k)) → A.unr (A.locG π w))
    (ρ₀ : G H.E N.Om →* GL (Fin R.r) (Qbar (N.l a)))
    (hc0 : Continuous fun g => ((ρ₀ g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a)))) (hs0 : IsSSRep ρ₀)
    (hfr : ∀ w, w ∉ placesOver H.E (N.l a) → A.unr (A.locG π w) → ∀ (B : ValuationSubring N.Om)
      (σ : G H.E N.Om), IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
      (((ρ₀ σ : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).map (A.iotaQC a).toRingHom).charpoly =
        galPol A (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2))) :
    ∃ ρ : G H.E N.Om →* GL (Fin R.r) (N.O a), IsRepOfSig N A a [⟨R.r, π, 1⟩] ρ := by
  haveI : IsGalois H.E N.Om := {}
  obtain ⟨ξ, hξc, hξ⟩ := hXi a
  have hιc : Continuous (iotaOQ N A a) := GlobalTheory.CoeffEmbedding.continuous_iotaOQ_of_data N A a
  have hcomp : iotaO N A a = (A.iotaQC a).toRingHom.comp (iotaOQ N A a) := rfl
  have hinj : Function.Injective (Polynomial.map (A.iotaQC a).toRingHom) :=
    Polynomial.map_injective _ (A.iotaQC a).injective

  let R1 := Formalism.MainNotions.SumRepresentations.At.twGL ρ₀ ((Units.map (iotaOQ N A a).toMonoidHom).comp ξ)
  have hR1 : ∀ g, ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))) =
      iotaOQ N A a ((ξ g : (N.O a)ˣ) : N.O a) • ((ρ₀ g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))) :=
    fun g => coe_twGL _ _ g
  have hR1c : Continuous fun g => ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))) := by
    simp only [hR1]
    exact (hιc.comp hξc).smul hc0
  have hR1C : ∀ g, ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).map (A.iotaQC a).toRingHom =
      iotaO N A a ((ξ g : (N.O a)ˣ) : N.O a) •
        ((ρ₀ g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).map (A.iotaQC a).toRingHom := by
    intro g
    rw [hR1, map_smul_matrix]
    rfl
  have hfin := placesOver_finite_joint_conditions_zpowers H.E (N.l a) (N.lPrime a).out.ne_zero

  let χ : Fin R.t → G H.E N.Om →* (Qbar (N.l a))ˣ := fun c =>
    (Units.map (iotaOQ N A a).toMonoidHom).comp (N.chi a ((c : ℕ) + 1))
  let Rq : G H.E N.Om →* GL (Fin (R.r + R.t)) (Qbar (N.l a)) :=
    (GlobalTheory.SSComplement.blockM finSumFinEquiv R1 (GlobalTheory.SSComplement.diagM χ).toHomUnits).toHomUnits
  have hRq : ∀ g, ((Rq g : GL _ _) : Matrix (Fin (R.r + R.t)) (Fin (R.r + R.t)) (Qbar (N.l a))) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks
      ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))) 0 0
      (Matrix.diagonal fun c : Fin R.t => iotaOQ N A a ((N.chi a ((c : ℕ) + 1) g : (N.O a)ˣ) : N.O a))) := fun g => rfl
  have hRqc : Continuous fun g => ((Rq g : GL _ _) : Matrix (Fin (R.r + R.t)) (Fin (R.r + R.t)) (Qbar (N.l a))) := by
    simp only [hRq]
    refine Continuous.matrix_reindex ?_ _ _
    refine Continuous.matrix_fromBlocks hR1c continuous_const continuous_const ?_
    exact Continuous.matrix_diagonal (continuous_pi fun c => hιc.comp (N.chi_cont a _))
  have hRqs : IsSSRep Rq :=
    GlobalTheory.SSComplement.blockM_ss _ _ _ (isSSRep_twGL _ _ hs0) (GlobalTheory.SSComplement.diagM_ss χ)
  have hq : Formalism.MainNotions.SumRepresentations.At.IsHeckeGaloisQ N A a x Rq := by
    refine ⟨hRqc, hRqs, fun v hso B g hBv hg => ?_⟩
    have h4 : A.unr (A.locG π v) := hun v fun k hk => hso.2.2.1 ((N.S_def a v).2 ⟨by
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk), hso.2.1⟩)
    have h5 : A.unr (A.locG (A.tw π A.etaTinv) v) := by
      rw [A.locG_tw]
      exact A.unr_char _ _ (A.locG_dim _ _) h4 (A.etaTinv_def v).1
    have h1 := hso.2.1
    have e3 : isoLoc N A (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A a]) A.etaTinv) v = A.locV a P v := by
      rw [GlobalTheory.Proof.SplitPlaceGoodSignature.isoLoc_lift N A hLaw, hloc v hso.1]
      congr 1
      simp [isoLoc, spehLoc, A.lpSum_zero, A.lpTw_zero]
    apply hinj
    rw [Polynomial.map_map, ← hcomp]
    refine Eq.trans (congrArg (Polynomial.map (A.iotaQC a).toRingHom)
      ((congrArg Matrix.charpoly (hRq g)).trans (charpoly_block _ _))) ?_
    symm
    rw [Polynomial.map_mul, ← Matrix.charpoly_map, hR1C g,
      hecke_of_loc N A a x π P hP e3 hso h5 hBv hg,
      galPol_twist N A π h4 _ ((hξ v h1).2 B g hBv hg),
      charpoly_smul_of_prod _ _ _ (hfr v h1 h4 B g hBv hg), prod_Icc_eq_fin, Polynomial.map_prod]
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  obtain ⟨rf, Pm, hPm⟩ := hO a x Rq hq
  have hval : ∀ g, ((rf g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a)).map (iotaOQ N A a) =
      ((Pm⁻¹ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l a))) *
        (show Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l a)) from
          ((Rq g : GL _ _) : Matrix (Fin (R.r + R.t)) (Fin (R.r + R.t)) (Qbar (N.l a)))) *
        ((Pm : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l a))) := fun g => congrArg Units.val (hPm g)
  have hrc : Continuous fun g => ((rf g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a)) := by
    have hc : Continuous fun g => ((rf g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a)).map (iotaOQ N A a) := by
      simp only [hval]
      exact (continuous_const.mul hRqc).mul continuous_const
    exact continuous_pi fun p => continuous_pi fun q => continuous_of_iota N A a _ (hc.matrix_elem p q)
  have hrs : IsSSRep (mapRep (algebraMap (N.O a) (Kf N a)) rf) := by
    refine GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_of_mapRep (A.iotaQ a) _ ?_
    rw [GlobalTheory.RowRepOcc.mapRep_mapRep]
    exact GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_conj (ρ := (Rq : G H.E N.Om →* GL (Fin R.nV) (Qbar (N.l a)))) Pm⁻¹
      (fun g => hPm g) hRqs

  haveI : CharZero (Qbar (N.l a)) := (RingHom.charZero_iff (A.iotaQC a).toRingHom.injective).2 inferInstance
  haveI : CharZero (Kf N a) := (RingHom.charZero_iff (A.iotaQ a).injective).2 inferInstance
  have hkey' : ∀ g, (((rf g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a))).charpoly.map (iotaOQ N A a) =
      ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).charpoly *
        ∏ c : Fin R.t, (X - C (iotaOQ N A a ((N.chi a ((c : ℕ) + 1) g : (N.O a)ˣ) : N.O a))) := by
    intro g
    rw [← Matrix.charpoly_map, hval g, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
    exact (congrArg Matrix.charpoly (hRq g)).trans (charpoly_block _ _)
  obtain ⟨ρ', hρc, hρs, hρp⟩ := GlobalTheory.LatticeComplement.exists_lattice_complement (G H.E N.Om) (N.O a) (Kf N a)
    R.r R.t (rf) (fun c : Fin R.t => N.chi a ((c : ℕ) + 1)) hrc hrs
    ⟨Qbar (N.l a), inferInstance, A.iotaQ a, R1, hkey'⟩
  have hcan : ∀ g, ((ρ' g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a)).charpoly.map (iotaOQ N A a) =
      ((R1 g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (Qbar (N.l a))).charpoly := by
    intro g
    have e1 : (((rf g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O a))).charpoly.map (iotaOQ N A a) =
        ((ρ' g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a)).charpoly.map (iotaOQ N A a) *
          ∏ c : Fin R.t, (X - C (iotaOQ N A a ((N.chi a ((c : ℕ) + 1) g : (N.O a)ˣ) : N.O a))) := by
      have := congrArg (Polynomial.map (iotaOQ N A a)) (hρp g)
      rw [Polynomial.map_mul, Polynomial.map_prod] at this
      refine this.trans ?_
      congr 1
      refine Finset.prod_congr rfl fun c _ => ?_
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    have hne : (∏ c : Fin R.t, (X - C (iotaOQ N A a ((N.chi a ((c : ℕ) + 1) g : (N.O a)ˣ) : N.O a)))) ≠ 0 :=
      (monic_prod_of_monic _ _ fun c _ => monic_X_sub_C _).ne_zero
    exact mul_right_cancel₀ hne (e1.symm.trans (hkey' g))
  refine ⟨Formalism.MainNotions.SumRepresentations.At.twGL ρ' ξ⁻¹, ?_, ?_, ?_⟩
  · have e : (fun g => ((Formalism.MainNotions.SumRepresentations.At.twGL ρ' ξ⁻¹ g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a))) =
        fun g => ((ξ g⁻¹ : (N.O a)ˣ) : N.O a) • ((ρ' g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a)) := by
      funext g
      rw [coe_twGL, MonoidHom.inv_apply, map_inv]
    rw [e]
    exact (hξc.comp continuous_inv).smul hρc
  · rw [mapRep_twGL]
    exact isSSRep_twGL _ _ hρs
  · filter_upwards [hfin.eventually_cofinite_notMem, A.locG_unr_ae π] with w h1 h2 B σ hBw hσ
    have iso : isoLoc N A [⟨R.r, π, 1⟩] w = A.locG π w := by
      simp [isoLoc, spehLoc, A.lpSum_zero, A.lpTw_zero]
    rw [iso]
    have h0 := hfr w h1 h2 B σ hBw hσ
    have c1 : (((ρ' σ : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O a)).map (iotaO N A a)).charpoly =
        (((A.frobEig (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2))).map
          (· * iotaO N A a ((ξ σ : (N.O a)ˣ) : N.O a))).map fun α => X - C α).prod := by
      rw [Matrix.charpoly_map, hcomp, ← Polynomial.map_map, hcan σ, ← Matrix.charpoly_map, hR1C σ]
      exact charpoly_smul_of_prod _ _ _ h0
    have c2 := charpoly_smul_of_prod _ (iotaO N A a (((ξ⁻¹ σ : (N.O a)ˣ)) : N.O a)) _ c1
    have huv : iotaO N A a ((ξ σ : (N.O a)ˣ) : N.O a) * iotaO N A a (((ξ⁻¹ σ : (N.O a)ˣ)) : N.O a) = 1 := by
      rw [← map_mul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel]
      simp
    have hL : ((A.frobEig (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2))).map
          (· * iotaO N A a ((ξ σ : (N.O a)ˣ) : N.O a))).map
          (· * iotaO N A a (((ξ⁻¹ σ : (N.O a)ˣ)) : N.O a)) =
        A.frobEig (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2)) := by
      rw [Multiset.map_map]
      refine (Multiset.map_congr rfl fun α _ => ?_).trans (Multiset.map_id _)
      show α * _ * _ = α
      rw [mul_assoc, huv, mul_one]
    rw [← Matrix.charpoly_map, coe_twGL, map_smul_matrix, c2, hL]
    rfl

end GlobalTheory.ResLoc

end
