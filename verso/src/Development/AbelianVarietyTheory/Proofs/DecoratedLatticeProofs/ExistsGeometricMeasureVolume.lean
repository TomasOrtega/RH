import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarAdelicUnitaryProductRealFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicUnitaryRealMulFiniteDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBoxFinitePosProductHaarUnitaryGroupsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarFinitePointsFourierJacobiBesselStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MapWittEmbeddingZeroRankIsHaarMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.MeasCommon

open scoped ENNReal NNReal

/- English proof (translation)
Introduce `D V T K good hgood μf hμf ν hν`. Use `haveI : SecondCountableTopology (GA D V) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1`. Take `⟨μR, μi, hR, hprod⟩` from `GlobalTheory.T.exists_haar_adelicUnitary_product_real_finite D V μf hμf`. Take `⟨hdec, hfin⟩` from `GlobalTheory.T.adelicUnitary_real_mul_finite_decomposition D V`. Break down `isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩` into its components or cases.

Conclude with `⟨μR, hR, fun t => isEmptyElim t⟩`. Take `⟨⟨θ, hθ⟩, hθall⟩` from `(hν t₀).2`. Take `⟨⟨A, hA⟩, hAall⟩` from `hθall θ hθ`. Take `⟨⟨m, hm⟩, -⟩` from `hAall A hA`. Take `⟨B, hBm, hB0, hBT⟩` from `GlobalTheory.T.exists_box_finite_pos_product_haar_unitaryGroups D.what₂.Tau (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) m (fun ρ => hgood ρ _ (hm ρ))`.

Use `haveI hνH : ∀ t, (ν t).IsHaarMeasure := fun t => (hν t).1`. Set `S : Set (GinfC V)` to `{a | ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) (a : GA D V)}`. Establish `key : ∀ t, ((ν t).haarScalarFactor μR : ℝ≥0∞) * (μi S * μf {k | Lev.finE V k.1 ∈ K t}) = ∏ ρ, m ρ (B ρ)`. Introduce `t`. Use `haveI : (ν t).IsHaarMeasure := (hν t).1`.

Establish `e` using `Measure.isMulLeftInvariant_eq_smul (ν t) μR`. Establish `hbox` using `(((hν t).2.2 θ hθ).2 A hA).2 m hm B hBm`. Establish `hset : {h : GA D V | Lev.finE V h ∈ K t ∧ ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h} = {h | ∃ a ∈ S, ∃ k ∈ {k : GfC V | Lev.finE V k.1 ∈ K t}, h = (a : GA D V) * k}`. Use extensionality with `h`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Take `⟨a, ha, k, hk, rfl⟩` from `hdec h`. Take `⟨e1, e2⟩` from `hfin a ha k hk`. Use `⟨⟨a, ha⟩, fun ρ => ?_, ⟨k, hk⟩, ?_, rfl⟩` and prove the remaining obligations. Take `⟨b, hb, hb'⟩` from `h2 ρ`.

Conclude with `⟨b, hb, by rw [hb', e2 (θ ρ)]⟩`. Use `show Lev.finE V k ∈ K t`. Rewrite using `[← e1]`. Conclude with `h1`. Introduce and unpack `⟨a, ha, k, hk, rfl⟩`.

Take `⟨e1, e2⟩` from `hfin a.1 a.2 k.1 k.2`. Use `⟨by rw [e1]; exact hk, fun ρ => ?_⟩` and prove the remaining obligations. Take `⟨b, hb, hb'⟩` from `ha ρ`. Conclude with `⟨b, hb, by rw [hb', e2 (θ ρ)]⟩`. Rewrite `hbox` using `[e, hset, Measure.smul_apply, hprod]`.

Rewrite using `[← hbox, ENNReal.smul_def, smul_eq_mul]`. Establish `hc0 : ∀ t, ((ν t).haarScalarFactor μR : ℝ≥0∞) ≠ 0` using `fun t => by haveI : (ν t).IsHaarMeasure := (hν t).1`. Conclude with `(Measure.haarScalarFactor_pos_of_isHaarMeasure (ν t) μR).ne'` after adjusting the coercions. Establish `hcT : ∀ t, ((ν t).haarScalarFactor μR : ℝ≥0∞) ≠ ⊤` using `fun t => ENNReal.coe_ne_top`. Establish `hX0 : μi S ≠ 0` using `fun h0 => hB0 (by rw [← key t₀, h0, zero_mul, mul_zero])`.

Establish `hY0 : ∀ t, μf {k | Lev.finE V k.1 ∈ K t} ≠ 0` using `fun t h0 => hB0 (by rw [← key t, h0, mul_zero, mul_zero])`. Establish `hXT : μi S ≠ ⊤` using `fun h0 => hBT (by rw [← key t₀, h0, ENNReal.top_mul (hY0 t₀), ENNReal.mul_top (hc0 t₀)])`. Establish `hYT : ∀ t, μf {k | Lev.finE V k.1 ∈ K t} ≠ ⊤` using `fun t h0 => hBT (by rw [← key t, h0, ENNReal.mul_top hX0, ENNReal.mul_top (hc0 t)])`. Use `⟨((∏ ρ, m ρ (B ρ)) / μi S) • μR, ?_, fun t => ⟨hY0 t, hYT t, ?_⟩⟩` and prove the remaining obligations. Conclude with `Measure.IsHaarMeasure.smul _ (ENNReal.div_pos_iff.2 ⟨hB0, hXT⟩).ne' (ENNReal.div_ne_top hBT hX0)`.

Use `haveI : (ν t).IsHaarMeasure := (hν t).1`. Establish `e` using `Measure.isMulLeftInvariant_eq_smul (ν t) μR`. Establish `hv : μf {k | Lev.finE V k.1 ∈ K t} * ((ν t).haarScalarFactor μR : ℝ≥0∞) = (∏ ρ, m ρ (B ρ)) / μi S`. Rewrite using `[ENNReal.eq_div_iff hX0 hXT, ← key t]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← hv]`. Use `conv_lhs => rw [e]`. Use extensionality with `s _`. Simplify using `only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def, mul_assoc]`.
-/
theorem common_measure : ∀ (D : D7) (V : HSp D) (T : Type) (K : T → Subgroup (GL (Fin V.rank) (Lev.EAf D))) (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop), (∀ ρ m, good ρ m → m.IsHaarMeasure) → ∀ (μf : Measure (GfC V)), μf.IsHaarMeasure → ∀ (ν : T → Measure (GA D V)), (∀ t, Lev.IsMeasLevW V (K t) good (ν t)) → ∃ ν₀ : Measure (GA D V), ν₀.IsHaarMeasure ∧ ∀ t, μf {k | Lev.finE V k.1 ∈ K t} ≠ 0 ∧ μf {k | Lev.finE V k.1 ∈ K t} ≠ ⊤ ∧ μf {k | Lev.finE V k.1 ∈ K t} • ν t = ν₀ := by
  intro D V T K good hgood μf hμf ν hν
  haveI : SecondCountableTopology (GA D V) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  obtain ⟨μR, μi, hR, hprod⟩ := GlobalTheory.T.exists_haar_adelicUnitary_product_real_finite D V μf hμf
  obtain ⟨hdec, hfin⟩ := GlobalTheory.T.adelicUnitary_real_mul_finite_decomposition D V
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · exact ⟨μR, hR, fun t => isEmptyElim t⟩
  obtain ⟨⟨θ, hθ⟩, hθall⟩ := (hν t₀).2
  obtain ⟨⟨A, hA⟩, hAall⟩ := hθall θ hθ
  obtain ⟨⟨m, hm⟩, -⟩ := hAall A hA
  obtain ⟨B, hBm, hB0, hBT⟩ := GlobalTheory.T.exists_box_finite_pos_product_haar_unitaryGroups D.what₂.Tau (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) m
    (fun ρ => hgood ρ _ (hm ρ))
  haveI hνH : ∀ t, (ν t).IsHaarMeasure := fun t => (hν t).1
  let S : Set (GinfC V) := {a | ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) (a : GA D V)}
  have key : ∀ t, ((ν t).haarScalarFactor μR : ℝ≥0∞) * (μi S * μf {k | Lev.finE V k.1 ∈ K t}) = ∏ ρ, m ρ (B ρ) := by
    intro t
    haveI : (ν t).IsHaarMeasure := (hν t).1
    have e := Measure.isMulLeftInvariant_eq_smul (ν t) μR
    have hbox := (((hν t).2.2 θ hθ).2 A hA).2 m hm B hBm
    have hset : {h : GA D V | Lev.finE V h ∈ K t ∧ ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h} =
        {h | ∃ a ∈ S, ∃ k ∈ {k : GfC V | Lev.finE V k.1 ∈ K t}, h = (a : GA D V) * k} := by
      ext h
      constructor
      · rintro ⟨h1, h2⟩
        obtain ⟨a, ha, k, hk, rfl⟩ := hdec h
        obtain ⟨e1, e2⟩ := hfin a ha k hk
        refine ⟨⟨a, ha⟩, fun ρ => ?_, ⟨k, hk⟩, ?_, rfl⟩
        · obtain ⟨b, hb, hb'⟩ := h2 ρ
          exact ⟨b, hb, by rw [hb', e2 (θ ρ)]⟩
        · show Lev.finE V k ∈ K t
          rw [← e1]; exact h1
      · rintro ⟨a, ha, k, hk, rfl⟩
        obtain ⟨e1, e2⟩ := hfin a.1 a.2 k.1 k.2
        refine ⟨by rw [e1]; exact hk, fun ρ => ?_⟩
        obtain ⟨b, hb, hb'⟩ := ha ρ
        exact ⟨b, hb, by rw [hb', e2 (θ ρ)]⟩
    rw [e, hset, Measure.smul_apply, hprod] at hbox
    rw [← hbox, ENNReal.smul_def, smul_eq_mul]
  have hc0 : ∀ t, ((ν t).haarScalarFactor μR : ℝ≥0∞) ≠ 0 := fun t => by
    haveI : (ν t).IsHaarMeasure := (hν t).1
    exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure (ν t) μR).ne'
  have hcT : ∀ t, ((ν t).haarScalarFactor μR : ℝ≥0∞) ≠ ⊤ := fun t => ENNReal.coe_ne_top
  have hX0 : μi S ≠ 0 := fun h0 => hB0 (by rw [← key t₀, h0, zero_mul, mul_zero])
  have hY0 : ∀ t, μf {k | Lev.finE V k.1 ∈ K t} ≠ 0 := fun t h0 => hB0 (by rw [← key t, h0, mul_zero, mul_zero])
  have hXT : μi S ≠ ⊤ := fun h0 => hBT (by rw [← key t₀, h0, ENNReal.top_mul (hY0 t₀), ENNReal.mul_top (hc0 t₀)])
  have hYT : ∀ t, μf {k | Lev.finE V k.1 ∈ K t} ≠ ⊤ := fun t h0 =>
    hBT (by rw [← key t, h0, ENNReal.mul_top hX0, ENNReal.mul_top (hc0 t)])
  refine ⟨((∏ ρ, m ρ (B ρ)) / μi S) • μR, ?_, fun t => ⟨hY0 t, hYT t, ?_⟩⟩
  · exact Measure.IsHaarMeasure.smul _ (ENNReal.div_pos_iff.2 ⟨hB0, hXT⟩).ne' (ENNReal.div_ne_top hBT hX0)
  · haveI : (ν t).IsHaarMeasure := (hν t).1
    have e := Measure.isMulLeftInvariant_eq_smul (ν t) μR
    have hv : μf {k | Lev.finE V k.1 ∈ K t} * ((ν t).haarScalarFactor μR : ℝ≥0∞) = (∏ ρ, m ρ (B ρ)) / μi S := by
      rw [ENNReal.eq_div_iff hX0 hXT, ← key t]
      ring
    rw [← hv]
    conv_lhs => rw [e]
    ext s _
    simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def, mul_assoc]

noncomputable def volOf {D : D7} {V : HSp D} (μ : Measure (GA D V)) (h : μ.IsHaarMeasure) : Vol V :=
  ⟨μ, (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ h).2.choose, h,
    (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ h).2.choose_spec⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem volOf_μ {D : D7} {V : HSp D} (μ : Measure (GA D V)) (h : μ.IsHaarMeasure) : (volOf μ h).μ = μ := rfl

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Yd cX ex W u hP a y b _`. Establish `hM : (pk W).IsModels` using `hP.bot.hyp.2.2.2.1.models`. Establish `hm2` using `D.R.two_le_m`. Use `haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V => (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1`. Use `choose μf hμf using fun j => (GlobalTheory.T.exists_haar_finitePoints_fourierJacobi_bessel D (Yc D j)).1`.

Take `⟨μT, hμT⟩` from `(GlobalTheory.T.exists_haar_finitePoints_fourierJacobi_bessel D D.sp.X').1`. Use `choose ρJ hρJ using fun j ρ h => ((GlobalTheory.T.exists_haar_finitePoints_fourierJacobi_bessel D (Yc D (j + 1))).2 _ _ (y.jac j ρ h).d).1`. Use `choose ρB hρB using fun j ρ h => ((GlobalTheory.T.exists_haar_finitePoints_fourierJacobi_bessel D (Yc D j)).2 _ _ (y.bes j ρ h).d).2 _ _ (y.bes j ρ h).o`. Establish `hc : ∀ k, ∃ ν₀ : Measure (GA D (Yc D k)), ν₀.IsHaarMeasure ∧ (k < D.R.m → ∀ t, μf k {g | Lev.finE (Yc D k) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram ((pk W).βY k) ((pk W).datYt t k (pk W).triv)} ≠ 0 ∧ μf k {g | Lev.finE (Yc D k) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D k). …`. Introduce `k`.

Distinguish the cases in `hk : k < D.R.m`. Establish `hw : ∃ good : ∀ ρ : D.what₂.Tau, Measure (UpqT ((Yc D k).sig (tauE D ρ)).1 ((Yc D k).sig (tauE D ρ)).2) → Prop, (∀ ρ m, good ρ m → m.IsHaarMeasure) ∧ ∀ t, Lev.IsMeasLevW (Yc D k) (Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram ((pk W).βY k) ((pk W).datYt t k (pk W).triv)) good ((pk W …`. Distinguish the cases in `hk' : k + 1 < D.R.m`. Conclude with `⟨fun _ m => Lev.IsMinf m, fun _ _ h => h.1, fun t => (hM.νY t k hk').1⟩`. Take `rfl : k = D.R.m - 1` from `by omega`.

Conclude with `⟨fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m, fun _ _ h => h.1, fun t => (hM.νY' t).1⟩`. Take `⟨good, hg, hw⟩` from `hw`. Take `⟨ν₀, h1, h2⟩` from `common_measure D (Yc D k) _ _ good hg (μf k) (hμf k) _ hw`. Conclude with `⟨ν₀, h1, fun _ => h2⟩`. Conclude with `⟨_, (Classical.choice (GlobalTheory.Unf.VolExist.nonempty_vol (Yc D k))).haar, fun h => absurd h hk⟩`.

Use `choose ν₀ hν₀H hν₀ using hc`. Take `⟨ν₀T, hν₀TH, hν₀T⟩` from `common_measure D D.sp.X' _ (fun t => Formalism.L2.DIV.lev D.sp.cm D.sp.X'.gram (pk W).βX ((pk W).datXt t)) (fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m) (fun _ _ h => h.1) μT hμT (fun t => (pk W).νX t) (fun t => (hM.νX t).1)`. Establish `hLH : ∀ j (h : j + 2 * 0 + 2 = D.R.m), (Measure.map (y.jac j 0 h).d.emb0 (a.x (j + 1)).vol.μ).IsHaarMeasure` using `fun j h => GlobalTheory.T.isHaarMeasure_map_emb0_of_rank_zero_decomposition D _ _ _ _ (a.x (j + 1)).vol.haar`. Set `vS : ∀ j, Vol (Yc D (j + 1))` to `fun j => if h : j + 2 * 0 + 2 = D.R.m then volOf _ (hLH j h) else volOf (ν₀ (j + 1)) (hν₀H (j + 1))`. Establish `hvS1 : ∀ j (h : j + 2 * 0 + 2 = D.R.m), (vS j).μ = Measure.map (y.jac j 0 h).d.emb0 (a.x (j + 1)).vol.μ`.

Introduce `j h`. Simplify using `only [vS, dif_pos h, volOf_μ]`. Establish `hvS2 : ∀ j, ¬ (j + 2 * 0 + 2 = D.R.m) → (vS j).μ = ν₀ (j + 1)`. Introduce `j h`. Simplify using `only [vS, dif_neg h, volOf_μ]`.

Set `vol : ∀ k, Vol (Yc D k)` to `fun k => Nat.casesOn (motive := fun k => Vol (Yc D k)) k (volOf (ν₀ 0) (hν₀H 0)) vS`. Set `κ : ℕ → ℝ` to `fun k => Nat.casesOn (motive := fun _ => ℝ) k 1 fun j => if h : j + 2 * 0 + 2 = D.R.m then ((Measure.map (y.jac j 0 h).d.emb0 (a.x (j + 1)).vol.μ).haarScalarFactor (ν₀ (j + 1)) : ℝ) else 1`. Establish `hκ1 : ∀ j (h : j + 2 * 0 + 2 = D.R.m), κ (j + 1) = ((Measure.map (y.jac j 0 h).d.emb0 (a.x (j + 1)).vol.μ).haarScalarFactor (ν₀ (j + 1)) : ℝ)`. Introduce `j h`. Simplify using `only [κ, dif_pos h]`.

Establish `hκ2 : ∀ k, k + 1 ≠ D.R.m → κ k = 1`. Introduce `k hk`. Consider the cases of `k with`. Consider the case `zero => rfl`. Consider the case `succ j => simp only [κ, dif_neg (show ¬ (j + 2 * 0 + 2 = D.R.m) by omega)]`.

Establish `hκpos : ∀ k, 0 < κ k`. Introduce `k`. Distinguish the cases in `hk : k + 1 = D.R.m`. Take `⟨j, rfl⟩ : ∃ j, k = j + 1` from `⟨k - 1, by omega⟩`. Establish `h : j + 2 * 0 + 2 = D.R.m` using `by omega`.

Rewrite using `[hκ1 j h]`. Use `haveI := hLH j h`. Use `haveI := hν₀H (j + 1)`. Conclude with `Measure.haarScalarFactor_pos_of_isHaarMeasure _ _` after adjusting the coercions. Rewrite using `[hκ2 k hk]`.

Conclude with `one_pos`. Establish `hset : ∀ k (β : GL (Fin (Yc D k).rank) (Lev.EAf D)) (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ (Yc D k).rank), ({g : GfC (Yc D k) | g.1 ∈ levS _ β Ld} : Set (GfC (Yc D k))) = {g | Lev.finE (Yc D k) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram β Ld}`. Introduce `k β Ld`. Use extensionality with `g`. Conclude with `⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩`.

Use `⟨⟨vol, volOf ν₀T hν₀TH, μf, μT, ρJ, ρB, κ⟩, ⟨hμf, hμT, hρJ, hρB, hκpos, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `t j hj`. Establish `hX` using `hν₀ (j + 1) hj t`. Use `show (vS j).μ = _`. Rewrite using `[GlobalTheory.Fam.volLev, if_pos hj]`.

Express the relevant statement in the definitionally equal form `(vS j).μ = ENNReal.ofReal (κ (j + 1) * (μf (j + 1) {g | g.1 ∈ levS _ ((pk W).βY (j + 1)) ((pk W).datYt t (j + 1) (pk W).triv)}).toReal) • (pk W).νY t (j + 1)`. Rewrite using `[hset]`. Take `⟨hX0, hXT, hXe⟩` from `hX`. Generalize the expression as in `μf (j + 1) {g | Lev.finE (Yc D (j + 1)) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D (j + 1)).gram ((pk W).βY (j + 1)) ((pk W).datYt t (j + 1) (pk W).triv)} = X at hX0 hXT hXe ⊢`. Distinguish the cases in `hL : j + 2 * 0 + 2 = D.R.m`.

Rewrite using `[hvS1 j hL, hκ1 j hL] haveI := hLH j hL haveI := hν₀H (j + 1)`. Establish `e` using `Measure.isMulLeftInvariant_eq_smul (Measure.map (y.jac j 0 hL).d.emb0 (a.x (j + 1)).vol.μ) (ν₀ (j + 1))`. Generalize the expression as in `(Measure.map (y.jac j 0 hL).d.emb0 (a.x (j + 1)).vol.μ).haarScalarFactor (ν₀ (j + 1)) = c at e ⊢`. Rewrite using `[e, ← hXe, ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hXT, mul_smul]`. Use extensionality with `s _`.

Simplify using `only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def]`. Rewrite using `[hvS2 j hL, hκ2 (j + 1) (by omega), one_mul, ENNReal.ofReal_toReal hXT, hXe]`. Introduce `t`. Take `⟨hX0, hXT, hXe⟩` from `hν₀T t`. Use `show ν₀T = _`.

Rewrite using `[GlobalTheory.Fam.volLev, if_neg (by omega)]`. Express the relevant statement in the definitionally equal form `ν₀T = ENNReal.ofReal (κ D.R.m * (μT {k | k.1 ∈ levS _ (pk W).βX ((pk W).datXt t)}).toReal) • (pk W).νX t`. Rewrite using `[hκ2 D.R.m (by omega), one_mul]`. Establish `hs : {g : GfC D.sp.X' | g.1 ∈ levS _ (pk W).βX ((pk W).datXt t)} = {g | Lev.finE D.sp.X' g.1 ∈ Formalism.L2.DIV.lev D.sp.cm D.sp.X'.gram (pk W).βX ((pk W).datXt t)}`. Use extensionality with `g`.

Conclude with `⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩`. Rewrite using `[hs, ENNReal.ofReal_toReal hXT, hXe]`. Introduce `j h`. Conclude with `hvS1 j h`.
-/
theorem measures_common : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (b : ∀ j, GA D (Yc D j)), (∀ j, j ≤ D.R.m → (a.x j).Is) → ∃ m : YMeas y, GeoMeas (pk W) (mkGeo m b) ∧ (commOf (pk W) u (mkGeo m b)).VolLast := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP a y b _
  have hM : (pk W).IsModels := hP.bot.hyp.2.2.2.1.models
  have hm2 := D.R.two_le_m
  haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V =>
    (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  choose μf hμf using fun j => (GlobalTheory.T.exists_haar_finitePoints_fourierJacobi_bessel D (Yc D j)).1
  obtain ⟨μT, hμT⟩ := (GlobalTheory.T.exists_haar_finitePoints_fourierJacobi_bessel D D.sp.X').1
  choose ρJ hρJ using fun j ρ h => ((GlobalTheory.T.exists_haar_finitePoints_fourierJacobi_bessel D (Yc D (j + 1))).2 _ _ (y.jac j ρ h).d).1
  choose ρB hρB using fun j ρ h => ((GlobalTheory.T.exists_haar_finitePoints_fourierJacobi_bessel D (Yc D j)).2 _ _ (y.bes j ρ h).d).2 _ _ (y.bes j ρ h).o
  have hc : ∀ k, ∃ ν₀ : Measure (GA D (Yc D k)), ν₀.IsHaarMeasure ∧ (k < D.R.m → ∀ t,
      μf k {g | Lev.finE (Yc D k) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram ((pk W).βY k) ((pk W).datYt t k (pk W).triv)} ≠ 0 ∧
      μf k {g | Lev.finE (Yc D k) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram ((pk W).βY k) ((pk W).datYt t k (pk W).triv)} ≠ ⊤ ∧
      μf k {g | Lev.finE (Yc D k) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram ((pk W).βY k) ((pk W).datYt t k (pk W).triv)} •
        (pk W).νY t k = ν₀) := by
    intro k
    by_cases hk : k < D.R.m
    · have hw : ∃ good : ∀ ρ : D.what₂.Tau, Measure (UpqT ((Yc D k).sig (tauE D ρ)).1 ((Yc D k).sig (tauE D ρ)).2) → Prop,
          (∀ ρ m, good ρ m → m.IsHaarMeasure) ∧ ∀ t, Lev.IsMeasLevW (Yc D k)
            (Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram ((pk W).βY k) ((pk W).datYt t k (pk W).triv)) good ((pk W).νY t k) := by
        by_cases hk' : k + 1 < D.R.m
        · exact ⟨fun _ m => Lev.IsMinf m, fun _ _ h => h.1, fun t => (hM.νY t k hk').1⟩
        · obtain rfl : k = D.R.m - 1 := by omega
          exact ⟨fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m, fun _ _ h => h.1, fun t => (hM.νY' t).1⟩
      obtain ⟨good, hg, hw⟩ := hw
      obtain ⟨ν₀, h1, h2⟩ := common_measure D (Yc D k) _ _ good hg (μf k) (hμf k) _ hw
      exact ⟨ν₀, h1, fun _ => h2⟩
    · exact ⟨_, (Classical.choice (GlobalTheory.Unf.VolExist.nonempty_vol (Yc D k))).haar, fun h => absurd h hk⟩
  choose ν₀ hν₀H hν₀ using hc
  obtain ⟨ν₀T, hν₀TH, hν₀T⟩ := common_measure D D.sp.X' _
    (fun t => Formalism.L2.DIV.lev D.sp.cm D.sp.X'.gram (pk W).βX ((pk W).datXt t))
    (fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m) (fun _ _ h => h.1) μT hμT (fun t => (pk W).νX t)
    (fun t => (hM.νX t).1)
  have hLH : ∀ j (h : j + 2 * 0 + 2 = D.R.m), (Measure.map (y.jac j 0 h).d.emb0 (a.x (j + 1)).vol.μ).IsHaarMeasure :=
    fun j h => GlobalTheory.T.isHaarMeasure_map_emb0_of_rank_zero_decomposition D _ _ _ _ (a.x (j + 1)).vol.haar
  let vS : ∀ j, Vol (Yc D (j + 1)) := fun j => if h : j + 2 * 0 + 2 = D.R.m then volOf _ (hLH j h)
    else volOf (ν₀ (j + 1)) (hν₀H (j + 1))
  have hvS1 : ∀ j (h : j + 2 * 0 + 2 = D.R.m), (vS j).μ = Measure.map (y.jac j 0 h).d.emb0 (a.x (j + 1)).vol.μ := by
    intro j h; simp only [vS, dif_pos h, volOf_μ]
  have hvS2 : ∀ j, ¬ (j + 2 * 0 + 2 = D.R.m) → (vS j).μ = ν₀ (j + 1) := by
    intro j h; simp only [vS, dif_neg h, volOf_μ]
  let vol : ∀ k, Vol (Yc D k) := fun k => Nat.casesOn (motive := fun k => Vol (Yc D k)) k (volOf (ν₀ 0) (hν₀H 0)) vS
  let κ : ℕ → ℝ := fun k => Nat.casesOn (motive := fun _ => ℝ) k 1 fun j => if h : j + 2 * 0 + 2 = D.R.m then
    ((Measure.map (y.jac j 0 h).d.emb0 (a.x (j + 1)).vol.μ).haarScalarFactor (ν₀ (j + 1)) : ℝ) else 1
  have hκ1 : ∀ j (h : j + 2 * 0 + 2 = D.R.m), κ (j + 1) =
      ((Measure.map (y.jac j 0 h).d.emb0 (a.x (j + 1)).vol.μ).haarScalarFactor (ν₀ (j + 1)) : ℝ) := by
    intro j h; simp only [κ, dif_pos h]
  have hκ2 : ∀ k, k + 1 ≠ D.R.m → κ k = 1 := by
    intro k hk
    cases k with
    | zero => rfl
    | succ j => simp only [κ, dif_neg (show ¬ (j + 2 * 0 + 2 = D.R.m) by omega)]
  have hκpos : ∀ k, 0 < κ k := by
    intro k
    by_cases hk : k + 1 = D.R.m
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have h : j + 2 * 0 + 2 = D.R.m := by omega
      rw [hκ1 j h]
      haveI := hLH j h
      haveI := hν₀H (j + 1)
      exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
    · rw [hκ2 k hk]; exact one_pos
  have hset : ∀ k (β : GL (Fin (Yc D k).rank) (Lev.EAf D)) (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ (Yc D k).rank),
      ({g : GfC (Yc D k) | g.1 ∈ levS _ β Ld} : Set (GfC (Yc D k))) =
        {g | Lev.finE (Yc D k) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D k).gram β Ld} := by
    intro k β Ld; ext g; exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
  refine ⟨⟨vol, volOf ν₀T hν₀TH, μf, μT, ρJ, ρB, κ⟩, ⟨hμf, hμT, hρJ, hρB, hκpos, ?_, ?_⟩, ?_⟩
  · intro t j hj
    have hX := hν₀ (j + 1) hj t
    show (vS j).μ = _
    rw [GlobalTheory.Fam.volLev, if_pos hj]
    change (vS j).μ = ENNReal.ofReal (κ (j + 1) * (μf (j + 1) {g | g.1 ∈ levS _ ((pk W).βY (j + 1))
      ((pk W).datYt t (j + 1) (pk W).triv)}).toReal) • (pk W).νY t (j + 1)
    rw [hset]
    obtain ⟨hX0, hXT, hXe⟩ := hX
    generalize μf (j + 1) {g | Lev.finE (Yc D (j + 1)) g.1 ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D (j + 1)).gram ((pk W).βY (j + 1))
      ((pk W).datYt t (j + 1) (pk W).triv)} = X at hX0 hXT hXe ⊢
    by_cases hL : j + 2 * 0 + 2 = D.R.m
    · rw [hvS1 j hL, hκ1 j hL]
      haveI := hLH j hL
      haveI := hν₀H (j + 1)
      have e := Measure.isMulLeftInvariant_eq_smul (Measure.map (y.jac j 0 hL).d.emb0 (a.x (j + 1)).vol.μ) (ν₀ (j + 1))
      generalize (Measure.map (y.jac j 0 hL).d.emb0 (a.x (j + 1)).vol.μ).haarScalarFactor (ν₀ (j + 1)) = c at e ⊢
      rw [e, ← hXe, ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hXT, mul_smul]
      ext s _
      simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def]
    · rw [hvS2 j hL, hκ2 (j + 1) (by omega), one_mul, ENNReal.ofReal_toReal hXT, hXe]
  · intro t
    obtain ⟨hX0, hXT, hXe⟩ := hν₀T t
    show ν₀T = _
    rw [GlobalTheory.Fam.volLev, if_neg (by omega)]
    change ν₀T = ENNReal.ofReal (κ D.R.m * (μT {k | k.1 ∈ levS _ (pk W).βX ((pk W).datXt t)}).toReal) • (pk W).νX t
    rw [hκ2 D.R.m (by omega), one_mul]
    have hs : {g : GfC D.sp.X' | g.1 ∈ levS _ (pk W).βX ((pk W).datXt t)} =
        {g | Lev.finE D.sp.X' g.1 ∈ Formalism.L2.DIV.lev D.sp.cm D.sp.X'.gram (pk W).βX ((pk W).datXt t)} := by
      ext g; exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
    rw [hs, ENNReal.ofReal_toReal hXT, hXe]
  · intro j h
    exact hvS1 j h

end GlobalTheory.MeasCommon
