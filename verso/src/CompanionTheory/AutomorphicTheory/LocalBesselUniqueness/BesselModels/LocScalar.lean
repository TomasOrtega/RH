import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.CoefWeightedLocHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotProdK
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeSquareIntegrable.Closed
import Formalism.SharpRestriction.CuspSpanNormBounds.ExpansionFromLemmaB

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.WuDecay
open scoped InnerProductSpace ENNReal NNReal
open Matrix

namespace Formalism.L2.SG.Pf.WuDec.LS

open Formalism.L2.SG.Pf.WuDec

section Facts

open Classical Formalism.L2.SG.Pf.WFL

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def Hfix (v : InfinitePlace X.B.I.F) : Set (Formalism.REAL.UJ (X.B.I.ε v)) :=
  {g | (∀ a, uMat g *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a)) ∧
    (∀ a, uMat g *ᵥ rv X.B.I v (X.fR a) = rv X.B.I v (X.fR a)) ∧ uMat g *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u)}

/- English proof (translation)
Unfold `NHloc QPK.prodSet Hfix`. Rewrite using `[Hloc_eq]`.
-/
theorem NHloc_eq (v : InfinitePlace X.B.I.F) : NHloc X u v = QPK.prodSet (Nloc X u v) (Hfix X u v) := by
  unfold NHloc QPK.prodSet Hfix; rw [Hloc_eq]

/- English proof (translation)
Establish `hT : (0 : ℝ) < ((D.mem u).A.T : ℝ)` using `by exact_mod_cast (D.mem u).A.T_prime.pos`. Establish `R` using `fun p q => Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v p q`. Establish `hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0` using `fun a b => by`. Use `R (X.eX a) (X.eX b)` as an intermediate fact. Rewrite `this` using `[X.ee, map_zero]`.

Conclude with `this`. Establish `hff : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.fR b)) = 0` using `fun a b => by`. Use `R (X.fY a) (X.fY b)` as an intermediate fact. Rewrite `this` using `[X.ff, map_zero]`. Conclude with `this`.

Establish `hef : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.fR b)) = if a = b then 1 else 0` using `fun a b => by`. Apply the tactic sequence `have := R (X.eX a) (X.fY b); rw [X.ef] at this; rw [show X.eR a = X.crd (X.eX a) from rfl, show X.fR b = X.crd (X.fY b) from rfl, this]; split_ifs <;> simp`. Establish `hez : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) = 0` using `fun a => by`. Use `R (X.eX a) (X.zu u)` as an intermediate fact. Rewrite `this` using `[(X.zu_orth u a).1, map_zero]`.

Conclude with `this`. Establish `hfz : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) = 0` using `fun a => by`. Use `R (X.fY a) (X.zu u)` as an intermediate fact. Rewrite `this` using `[(X.zu_orth u a).2, map_zero]`. Conclude with `this`.

Establish `hzz : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) = -(((D.mem u).A.T : ℝ) : ℂ)`. Use `R (X.zu u) (X.zu u)` as an intermediate fact. Rewrite `this` using `[X.zu_norm, map_neg, map_natCast]`. Rewrite using `[show X.zR u = X.crd (X.zu u) from rfl, this]`. Use `push_cast`.

Both sides reduce to the same expression. Establish `hew : ∀ c a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR c)) (X.wfr u v a) = 0` using `fun c a => ((X.wfr_perp u v a).1 c).1`. Establish `hfw : ∀ c a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR c)) (X.wfr u v a) = 0` using `fun c a => ((X.wfr_perp u v a).1 c).2`. Establish `hzw : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (X.wfr u v a) = 0` using `fun a => (X.wfr_perp u v a).2`. Establish `hP` using `locHN_cast Formalism.L2.SG.Pf.WFL.locHNProps_holds (hdim X) (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) (X.wfr u v) hT hee hff hef hez hfz hzz (X.wfr_on u v) hew hfw hzw`.

Establish `hU` using `nUnimod_cast Formalism.L2.SG.Closed.BM.NUnimodLoc_holds (hdim X) (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) (X.wfr u v) hT hee hff hef hez hfz hzz (X.wfr_on u v) hew hfw hzw`. Conclude with `⟨hP.1, hP.2.1, hP.2.2.1, ⟨fix_one, fun a ha b hb => fix_mul ha hb, fun a ha => fix_inv ha⟩, fun h hh m hm => hP.2.2.2 h hh m hm, hU⟩`.
-/
theorem place_facts (v : InfinitePlace X.B.I.F) :
    IsClosed (Nloc X u v) ∧ IsCompact (Hfix X u v) ∧ QPK.IsGrp (Nloc X u v) ∧ QPK.IsGrp (Hfix X u v) ∧
    (∀ h ∈ Hfix X u v, ∀ m ∈ Nloc X u v, h * m * h⁻¹ ∈ Nloc X u v) ∧
    (∀ μ : Measure (Formalism.REAL.UJ (X.B.I.ε v)), SigmaFinite μ → μ ≠ 0 → μ (Nloc X u v)ᶜ = 0 →
      (∀ s ∈ Nloc X u v, μ.map (fun x => s * x) = μ) → ∀ s ∈ Nloc X u v, μ.map (fun x => x * s) = μ) := by
  have hT : (0 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.pos
  have R := fun p q => Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v p q
  have hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := fun a b => by
    have := R (X.eX a) (X.eX b); rw [X.ee, map_zero] at this; exact this
  have hff : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.fR b)) = 0 := fun a b => by
    have := R (X.fY a) (X.fY b); rw [X.ff, map_zero] at this; exact this
  have hef : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.fR b)) = if a = b then 1 else 0 :=
    fun a b => by
      have := R (X.eX a) (X.fY b); rw [X.ef] at this; rw [show X.eR a = X.crd (X.eX a) from rfl,
        show X.fR b = X.crd (X.fY b) from rfl, this]; split_ifs <;> simp
  have hez : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) = 0 := fun a => by
    have := R (X.eX a) (X.zu u); rw [(X.zu_orth u a).1, map_zero] at this; exact this
  have hfz : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) = 0 := fun a => by
    have := R (X.fY a) (X.zu u); rw [(X.zu_orth u a).2, map_zero] at this; exact this
  have hzz : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) = -(((D.mem u).A.T : ℝ) : ℂ) := by
    have := R (X.zu u) (X.zu u); rw [X.zu_norm, map_neg, map_natCast] at this
    rw [show X.zR u = X.crd (X.zu u) from rfl, this]; push_cast; rfl
  have hew : ∀ c a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR c)) (X.wfr u v a) = 0 := fun c a => ((X.wfr_perp u v a).1 c).1
  have hfw : ∀ c a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR c)) (X.wfr u v a) = 0 := fun c a => ((X.wfr_perp u v a).1 c).2
  have hzw : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (X.wfr u v a) = 0 := fun a => (X.wfr_perp u v a).2
  have hP := locHN_cast Formalism.L2.SG.Pf.WFL.locHNProps_holds (hdim X) (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a))
    (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) (X.wfr u v) hT hee hff hef hez hfz hzz (X.wfr_on u v)
    hew hfw hzw
  have hU := nUnimod_cast Formalism.L2.SG.Closed.BM.NUnimodLoc_holds (hdim X) (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a))
    (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) (X.wfr u v) hT hee hff hef hez hfz hzz (X.wfr_on u v)
    hew hfw hzw
  exact ⟨hP.1, hP.2.1, hP.2.2.1, ⟨fix_one, fun a ha b hb => fix_mul ha hb, fun a ha => fix_inv ha⟩,
    fun h hh m hm => hP.2.2.2 h hh m hm, hU⟩

end Facts

section K1

open Classical Formalism.L2.SG.Pf.WFL

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

/- English proof (translation)
Take `⟨hNc, hHc, hNg, hHg, hnorm, hunim⟩` from `place_facts X u v`. Take `⟨-, -, hloc, -⟩` from `hQ`. Take `⟨hSv, hW⟩` from `hloc v`. Take `⟨μN, μH, β, -, -, hM, hβm, hβ1, -⟩` from `QPK.locPack_of QPK.haar_measure_existence QPK.conjugation_invariant_measure QPK.siegel_measure_definition QPK.bruhat_decomposition' QPK.local_weil_representation (Formalism.REAL.UJ (X.B.I.ε v)) (Formalism.REAL.muG (X.B.I.ε v)) (Nloc X u v) (Hfix X u v) hNc hHc hNg hHg hnorm hunim`. Establish `hK` using `QPK.prodSet_isClosed hNc hHc`.

Establish `hKg` using `QPK.prodSet_isGrp hNg hHg hnorm`. Establish `hSv' : QPK.InvOn (μS v) (QPK.prodSet (Nloc X u v) (Hfix X u v))`. Rewrite using `[← NHloc_eq]`. Conclude with `hSv`. Take `⟨c, hc0, hct, hμS⟩` from `QPK.haar_measure_uniqueness (Formalism.REAL.UJ (X.B.I.ε v)) _ hK hKg (μS v) _ hSv' hM`.

Use `set β' : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞ := fun x => c⁻¹ * β x with hβ'`. Establish `hβ'm : Measurable β'` using `measurable_const.mul hβm`. Establish `hβ'1 : ∀ x, ∫⁻ s, β' (s * x) ∂(μS v) = 1`. Introduce `x`. Rewrite using `[hμS, lintegral_smul_measure, hβ', lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0), hβ1 x, mul_one, smul_eq_mul, ENNReal.mul_inv_cancel hc0 hct]`.

Establish `hinv' : ∀ s ∈ NHloc X u v, ∀ x, F (s * x * g) = F (x * g)` using `fun s hs x => by`. Rewrite using `[mul_assoc]`. Conclude with `hinv s hs (x * g)`. Establish `hae : ∀ x, ∀ᵐ s ∂(μS v), F (s * x * g) = F (x * g)`. Introduce `x`.

Establish `h0 : (μS v) (NHloc X u v)ᶜ = 0` using `hSv.2.2.1`. Use `filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with s hs`. Conclude with `hinv' s (by simpa using hs) x`. Establish `hae2 : ∀ x, ∀ᵐ s ∂(μS v), F (s * x) = F x`. Introduce `x`.

Establish `h0 : (μS v) (NHloc X u v)ᶜ = 0` using `hSv.2.2.1`. Use `filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with s hs`. Conclude with `hinv s (by simpa using hs) x`. Establish `hR` using `Formalism.REAL.unimodular _ (X.B.I.ε v) g`. Establish `hmg : Measurable fun y : Formalism.REAL.UJ (X.B.I.ε v) => y * g` using `measurable_mul_const g`.

Establish `hmgi : Measurable fun y : Formalism.REAL.UJ (X.B.I.ε v) => y * g⁻¹` using `measurable_mul_const g⁻¹`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[lintegral_congr_ae ((hae x).mono fun s hs => by rw [hs]), lintegral_const_mul (f := fun s => β' (s * x)) _ (hβ'm.comp (measurable_mul_const x)), hβ'1 x, mul_one]`. Use `_ = ∫⁻ y, F (y * g) * β' y ∂(Formalism.REAL.muG (X.B.I.ε v)) := (hW (fun y => F (y * g) * β' y) ((hF.comp hmg).mul hβ'm)).symm`.

Use `_ = ∫⁻ y, F y * β' (y * g⁻¹) ∂(Formalism.REAL.muG (X.B.I.ε v)) := by conv_rhs => rw [← hR]`. Establish `hm2 : Measurable fun y : Formalism.REAL.UJ (X.B.I.ε v) => F y * β' (y * g⁻¹)` using `hF.mul (hβ'm.comp hmgi)`. Rewrite using `[lintegral_map hm2 hmg]`. Simplify using `only [mul_inv_cancel_right]`. Use `_ = ∫⁻ x, ∫⁻ s, F (s * x) * β' (s * x * g⁻¹) ∂(μS v) ∂(νl v) := hW (fun y => F y * β' (y * g⁻¹)) (hF.mul (hβ'm.comp hmgi))`.

Use `_ = ∫⁻ x, F x ∂(νl v) := by`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[lintegral_congr_ae ((hae2 x).mono fun s hs => by rw [hs]), lintegral_const_mul (f := fun s => β' (s * x * g⁻¹)) _ (hβ'm.comp ((measurable_mul_const x).mul_const g⁻¹))]`. Simplify using `only [mul_assoc]`. Rewrite using `[hβ'1 (x * g⁻¹), mul_one]`.
-/
theorem quot_rightInv {μS νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))} {C : ℝ≥0∞} (hQ : QuotWit X u μS νl C)
    (v : InfinitePlace X.B.I.F) (F : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞) (hF : Measurable F)
    (hinv : ∀ s ∈ NHloc X u v, ∀ x, F (s * x) = F x) (g : Formalism.REAL.UJ (X.B.I.ε v)) :
    ∫⁻ x, F (x * g) ∂(νl v) = ∫⁻ x, F x ∂(νl v) := by
  obtain ⟨hNc, hHc, hNg, hHg, hnorm, hunim⟩ := place_facts X u v
  obtain ⟨-, -, hloc, -⟩ := hQ
  obtain ⟨hSv, hW⟩ := hloc v
  obtain ⟨μN, μH, β, -, -, hM, hβm, hβ1, -⟩ := QPK.locPack_of QPK.haar_measure_existence QPK.conjugation_invariant_measure QPK.siegel_measure_definition
    QPK.bruhat_decomposition' QPK.local_weil_representation (Formalism.REAL.UJ (X.B.I.ε v)) (Formalism.REAL.muG (X.B.I.ε v)) (Nloc X u v)
    (Hfix X u v) hNc hHc hNg hHg hnorm hunim
  have hK := QPK.prodSet_isClosed hNc hHc
  have hKg := QPK.prodSet_isGrp hNg hHg hnorm
  have hSv' : QPK.InvOn (μS v) (QPK.prodSet (Nloc X u v) (Hfix X u v)) := by
    rw [← NHloc_eq]; exact hSv
  obtain ⟨c, hc0, hct, hμS⟩ := QPK.haar_measure_uniqueness (Formalism.REAL.UJ (X.B.I.ε v)) _ hK hKg (μS v) _ hSv' hM
  set β' : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞ := fun x => c⁻¹ * β x with hβ'
  have hβ'm : Measurable β' := measurable_const.mul hβm
  have hβ'1 : ∀ x, ∫⁻ s, β' (s * x) ∂(μS v) = 1 := by
    intro x
    rw [hμS, lintegral_smul_measure, hβ', lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0), hβ1 x, mul_one,
      smul_eq_mul, ENNReal.mul_inv_cancel hc0 hct]
  have hinv' : ∀ s ∈ NHloc X u v, ∀ x, F (s * x * g) = F (x * g) := fun s hs x => by
    rw [mul_assoc]; exact hinv s hs (x * g)
  have hae : ∀ x, ∀ᵐ s ∂(μS v), F (s * x * g) = F (x * g) := by
    intro x
    have h0 : (μS v) (NHloc X u v)ᶜ = 0 := hSv.2.2.1
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with s hs
    exact hinv' s (by simpa using hs) x
  have hae2 : ∀ x, ∀ᵐ s ∂(μS v), F (s * x) = F x := by
    intro x
    have h0 : (μS v) (NHloc X u v)ᶜ = 0 := hSv.2.2.1
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with s hs
    exact hinv s (by simpa using hs) x
  have hR := Formalism.REAL.unimodular _ (X.B.I.ε v) g
  have hmg : Measurable fun y : Formalism.REAL.UJ (X.B.I.ε v) => y * g := measurable_mul_const g
  have hmgi : Measurable fun y : Formalism.REAL.UJ (X.B.I.ε v) => y * g⁻¹ := measurable_mul_const g⁻¹
  calc ∫⁻ x, F (x * g) ∂(νl v)
      = ∫⁻ x, ∫⁻ s, F (s * x * g) * β' (s * x) ∂(μS v) ∂(νl v) := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_congr_ae ((hae x).mono fun s hs => by rw [hs]),
          lintegral_const_mul (f := fun s => β' (s * x)) _ (hβ'm.comp (measurable_mul_const x)), hβ'1 x, mul_one]
    _ = ∫⁻ y, F (y * g) * β' y ∂(Formalism.REAL.muG (X.B.I.ε v)) :=
        (hW (fun y => F (y * g) * β' y) ((hF.comp hmg).mul hβ'm)).symm
    _ = ∫⁻ y, F y * β' (y * g⁻¹) ∂(Formalism.REAL.muG (X.B.I.ε v)) := by
        conv_rhs => rw [← hR]
        have hm2 : Measurable fun y : Formalism.REAL.UJ (X.B.I.ε v) => F y * β' (y * g⁻¹) := hF.mul (hβ'm.comp hmgi)
        rw [lintegral_map hm2 hmg]
        simp only [mul_inv_cancel_right]
    _ = ∫⁻ x, ∫⁻ s, F (s * x) * β' (s * x * g⁻¹) ∂(μS v) ∂(νl v) :=
        hW (fun y => F y * β' (y * g⁻¹)) (hF.mul (hβ'm.comp hmgi))
    _ = ∫⁻ x, F x ∂(νl v) := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_congr_ae ((hae2 x).mono fun s hs => by rw [hs]),
          lintegral_const_mul (f := fun s => β' (s * x * g⁻¹)) _ (hβ'm.comp ((measurable_mul_const x).mul_const g⁻¹))]
        simp only [mul_assoc]; rw [hβ'1 (x * g⁻¹), mul_one]

/- English proof (translation)
Take `⟨hNc, hHc, hNg, hHg, hnorm, hunim⟩` from `place_facts X u v`. Take `⟨-, -, hloc, -⟩` from `hQ`. Take `⟨hSv, hW⟩` from `hloc v`. Take `⟨μN, μH, β, -, -, hM, hβm, hβ1, -⟩` from `QPK.locPack_of QPK.haar_measure_existence QPK.conjugation_invariant_measure QPK.siegel_measure_definition QPK.bruhat_decomposition' QPK.local_weil_representation (Formalism.REAL.UJ (X.B.I.ε v)) (Formalism.REAL.muG (X.B.I.ε v)) (Nloc X u v) (Hfix X u v) hNc hHc hNg hHg hnorm hunim`. Establish `hK` using `QPK.prodSet_isClosed hNc hHc`.

Establish `hKg` using `QPK.prodSet_isGrp hNg hHg hnorm`. Establish `hSv' : QPK.InvOn (μS v) (QPK.prodSet (Nloc X u v) (Hfix X u v))`. Rewrite using `[← NHloc_eq]`. Conclude with `hSv`. Take `⟨c, hc0, hct, hμS⟩` from `QPK.haar_measure_uniqueness (Formalism.REAL.UJ (X.B.I.ε v)) _ hK hKg (μS v) _ hSv' hM`.

Use `⟨fun x => c⁻¹ * β x, measurable_const.mul hβm, fun F hF hinv => ?_⟩` and prove the remaining obligations. Establish `hβ'1 : ∀ x, ∫⁻ s, c⁻¹ * β (s * x) ∂(μS v) = 1`. Introduce `x`. Rewrite using `[hμS, lintegral_smul_measure, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0), hβ1 x, mul_one, smul_eq_mul, ENNReal.mul_inv_cancel hc0 hct]`. Establish `hae : ∀ x, ∀ᵐ s ∂(μS v), F (s * x) = F x`.

Introduce `x`. Establish `h0 : (μS v) (NHloc X u v)ᶜ = 0` using `hSv.2.2.1`. Use `filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with s hs`. Conclude with `hinv s (by simpa using hs) x`. Combine the equalities or inequalities in the displayed calculation.

Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[lintegral_congr_ae ((hae x).mono fun s hs => by rw [hs]), lintegral_const_mul (f := fun s => c⁻¹ * β (s * x)) _ (measurable_const.mul (hβm.comp (measurable_mul_const x))), hβ'1 x, mul_one]`. Use `_ = ∫⁻ x, F x * (c⁻¹ * β x) ∂(Formalism.REAL.muG (X.B.I.ε v)) := (hW (fun y => F y * (c⁻¹ * β y)) (hF.mul (measurable_const.mul hβm))).symm`.
-/
theorem quot_bruhat {μS νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))} {C : ℝ≥0∞} (hQ : QuotWit X u μS νl C)
    (v : InfinitePlace X.B.I.F) : ∃ β : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable β ∧
      ∀ F : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable F → (∀ s ∈ NHloc X u v, ∀ x, F (s * x) = F x) →
        ∫⁻ x, F x ∂(νl v) = ∫⁻ x, F x * β x ∂(Formalism.REAL.muG (X.B.I.ε v)) := by
  obtain ⟨hNc, hHc, hNg, hHg, hnorm, hunim⟩ := place_facts X u v
  obtain ⟨-, -, hloc, -⟩ := hQ
  obtain ⟨hSv, hW⟩ := hloc v
  obtain ⟨μN, μH, β, -, -, hM, hβm, hβ1, -⟩ := QPK.locPack_of QPK.haar_measure_existence QPK.conjugation_invariant_measure QPK.siegel_measure_definition
    QPK.bruhat_decomposition' QPK.local_weil_representation (Formalism.REAL.UJ (X.B.I.ε v)) (Formalism.REAL.muG (X.B.I.ε v)) (Nloc X u v)
    (Hfix X u v) hNc hHc hNg hHg hnorm hunim
  have hK := QPK.prodSet_isClosed hNc hHc
  have hKg := QPK.prodSet_isGrp hNg hHg hnorm
  have hSv' : QPK.InvOn (μS v) (QPK.prodSet (Nloc X u v) (Hfix X u v)) := by
    rw [← NHloc_eq]; exact hSv
  obtain ⟨c, hc0, hct, hμS⟩ := QPK.haar_measure_uniqueness (Formalism.REAL.UJ (X.B.I.ε v)) _ hK hKg (μS v) _ hSv' hM
  refine ⟨fun x => c⁻¹ * β x, measurable_const.mul hβm, fun F hF hinv => ?_⟩
  have hβ'1 : ∀ x, ∫⁻ s, c⁻¹ * β (s * x) ∂(μS v) = 1 := by
    intro x
    rw [hμS, lintegral_smul_measure, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0), hβ1 x, mul_one,
      smul_eq_mul, ENNReal.mul_inv_cancel hc0 hct]
  have hae : ∀ x, ∀ᵐ s ∂(μS v), F (s * x) = F x := by
    intro x
    have h0 : (μS v) (NHloc X u v)ᶜ = 0 := hSv.2.2.1
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with s hs
    exact hinv s (by simpa using hs) x
  calc ∫⁻ x, F x ∂(νl v)
      = ∫⁻ x, ∫⁻ s, F (s * x) * (c⁻¹ * β (s * x)) ∂(μS v) ∂(νl v) := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_congr_ae ((hae x).mono fun s hs => by rw [hs]),
          lintegral_const_mul (f := fun s => c⁻¹ * β (s * x)) _
            (measurable_const.mul (hβm.comp (measurable_mul_const x))), hβ'1 x, mul_one]
    _ = ∫⁻ x, F x * (c⁻¹ * β x) ∂(Formalism.REAL.muG (X.B.I.ε v)) :=
        (hW (fun y => F y * (c⁻¹ * β y)) (hF.mul (measurable_const.mul hβm))).symm

end K1

section Schur

open Classical

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Use `haveI : (Formalism.REAL.muG (X.B.I.ε v)).IsInvInvariant := ⟨Formalism.REAL.invInvariant _ (X.B.I.ε v)⟩`. Establish `hds` using `X.ds v`. Establish `hU` using `hds.2.2.1`. Establish `hURep : Formalism.L2.SG.ProjRows.IsURep (fun g : Formalism.REAL.UJ (X.B.I.ε v) => X.B.σ v (uMat g))`. Use `⟨?_, fun a b => ?_, fun g w => hU.2.1 _ g.2 w, fun w => ?_⟩` and prove the remaining obligations.

Use `show X.B.σ v (uMat 1) = 1`. Rewrite using `[uMat_one']`. Conclude with `hU.1.1`. Use `show X.B.σ v (uMat (a * b)) = (X.B.σ v (uMat a)).comp (X.B.σ v (uMat b))`. Rewrite using `[Formalism.L2.SG.WuDecayPf.uMat_mul']`.

Conclude with `hU.1.2 _ a.2 _ b.2`. Conclude with `(hU.2.2 w).comp_continuous Formalism.L2.SG.WuDecayPf.continuous_uMat (fun g => g.2)`. Use `haveI : Nontrivial (X.B.H v) := hds.2.1`. Take `⟨d', hd'⟩` from `PIW.HCFdeg.formal_degree_abstract_form _ (X.B.I.ε v) (X.B.H v) (X.B.σ v) hds.2.2.1 hds.2.2.2.1 hds.2.2.2.2.1`. Establish `hw1 : ‖X.B.w v‖ = 1` using `(X.low v).1`.

Establish `hw0 : X.B.w v ≠ 0` using `by intro h; rw [h, norm_zero] at hw1; exact zero_ne_one hw1`. Establish `hdd : X.dv v = d'` using `Formalism.MainNotions.DiscreteSeriesInnerProducts.fdegOf_eq hd' hw0`. Establish `hF : Formalism.L2.SG.ProjRows.IsFdegG (Formalism.REAL.muG (X.B.I.ε v)) (fun g : Formalism.REAL.UJ (X.B.I.ε v) => X.B.σ v (uMat g)) (X.dv v)`. Rewrite using `[hdd]`. Conclude with `⟨hd'.1, fun a b a' b' => hd'.2 a b a' b'⟩`.

Take `⟨hPC, -⟩` from `Formalism.L2.SG.Closed.SchurConv_holds (Formalism.REAL.UJ (X.B.I.ε v)) (Formalism.REAL.muG (X.B.I.ε v)) (X.B.H v) (fun g => X.B.σ v (uMat g)) (X.dv v) (X.B.w v) hURep hF hw1`. Take `⟨h1, -, h3⟩` from `hPC`. Take `⟨hi, he⟩` from `h3 1 y`. Simplify using `only [inv_one, one_mul] at hi he`. Rewrite `he` using `[h1, one_mul]`.

Conclude with `⟨hi, he⟩`.
-/
theorem pv_conv (v : InfinitePlace X.B.I.F) (y : Formalism.REAL.UJ (X.B.I.ε v)) :
    Integrable (fun g => Pv X v g * Pv X v (g⁻¹ * y)) (Formalism.REAL.muG (X.B.I.ε v)) ∧
      ∫ g, Pv X v g * Pv X v (g⁻¹ * y) ∂(Formalism.REAL.muG (X.B.I.ε v)) = Pv X v y := by
  haveI : (Formalism.REAL.muG (X.B.I.ε v)).IsInvInvariant := ⟨Formalism.REAL.invInvariant _ (X.B.I.ε v)⟩
  have hds := X.ds v
  have hU := hds.2.2.1
  have hURep : Formalism.L2.SG.ProjRows.IsURep (fun g : Formalism.REAL.UJ (X.B.I.ε v) => X.B.σ v (uMat g)) := by
    refine ⟨?_, fun a b => ?_, fun g w => hU.2.1 _ g.2 w, fun w => ?_⟩
    · show X.B.σ v (uMat 1) = 1
      rw [uMat_one']; exact hU.1.1
    · show X.B.σ v (uMat (a * b)) = (X.B.σ v (uMat a)).comp (X.B.σ v (uMat b))
      rw [Formalism.L2.SG.WuDecayPf.uMat_mul']; exact hU.1.2 _ a.2 _ b.2
    · exact (hU.2.2 w).comp_continuous Formalism.L2.SG.WuDecayPf.continuous_uMat (fun g => g.2)
  haveI : Nontrivial (X.B.H v) := hds.2.1
  obtain ⟨d', hd'⟩ := PIW.HCFdeg.formal_degree_abstract_form _ (X.B.I.ε v) (X.B.H v) (X.B.σ v) hds.2.2.1 hds.2.2.2.1 hds.2.2.2.2.1
  have hw1 : ‖X.B.w v‖ = 1 := (X.low v).1
  have hw0 : X.B.w v ≠ 0 := by intro h; rw [h, norm_zero] at hw1; exact zero_ne_one hw1
  have hdd : X.dv v = d' := Formalism.MainNotions.DiscreteSeriesInnerProducts.fdegOf_eq hd' hw0
  have hF : Formalism.L2.SG.ProjRows.IsFdegG (Formalism.REAL.muG (X.B.I.ε v)) (fun g : Formalism.REAL.UJ (X.B.I.ε v) => X.B.σ v (uMat g))
      (X.dv v) := by
    rw [hdd]; exact ⟨hd'.1, fun a b a' b' => hd'.2 a b a' b'⟩
  obtain ⟨hPC, -⟩ := Formalism.L2.SG.Closed.SchurConv_holds (Formalism.REAL.UJ (X.B.I.ε v)) (Formalism.REAL.muG (X.B.I.ε v)) (X.B.H v)
    (fun g => X.B.σ v (uMat g)) (X.dv v) (X.B.w v) hURep hF hw1
  obtain ⟨h1, -, h3⟩ := hPC
  obtain ⟨hi, he⟩ := h3 1 y
  simp only [inv_one, one_mul] at hi he
  rw [h1, one_mul] at he
  exact ⟨hi, he⟩

end Schur

section Main

open Classical Formalism.L2.SG.SplitPrimeNormLemmas

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

/- English proof (translation)
Establish `h` using `Formalism.L2.SG.WuDecayPf.coef_integrable_of_weighted X (coefWeighted_of_gap X Formalism.L2.SG.Closed.BM.CoefWeightedLoc_holds hG) v`. Establish `e : Pv X v = fun g => ((X.dv v : ℝ) : ℂ) * star (Formalism.L2.SG.WuDecayPf.coefV X v g)`. Use function extensionality and compare the values at `g`. Both sides reduce to the same expression. Use `Integrable.mono' (h.norm.const_mul |X.dv v|) (continuous_Pv X v).aestronglyMeasurable (ae_of_all _ fun g => le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[e]`. Simplify using `only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]`.
-/
theorem pv_integrable (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (v : InfinitePlace X.B.I.F) :
    Integrable (Pv X v) (Formalism.REAL.muG (X.B.I.ε v)) := by
  have h := Formalism.L2.SG.WuDecayPf.coef_integrable_of_weighted X (coefWeighted_of_gap X Formalism.L2.SG.Closed.BM.CoefWeightedLoc_holds hG) v
  have e : Pv X v = fun g => ((X.dv v : ℝ) : ℂ) * star (Formalism.L2.SG.WuDecayPf.coefV X v g) := by
    funext g; rfl
  refine Integrable.mono' (h.norm.const_mul |X.dv v|) (continuous_Pv X v).aestronglyMeasurable
    (ae_of_all _ fun g => le_of_eq ?_)
  rw [e]
  simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]

/- English proof (translation)
Break down `le_total a b with h | h` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ennreal_mul_le_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

/- English proof (translation)
Introduce `D hG X u μS νl C hQ v c hc0 hc`. Use `set μ := Formalism.REAL.muG (X.B.I.ε v) with hμ`. Use `set f := X.Wloc u v with hfdef`. Use `set ph := Pv X v with hph`. Establish `hfc : Continuous f` using `X.Wloc_cont u v`.

Establish `hpc : Continuous ph` using `continuous_Pv X v`. Establish `hpI : Integrable ph μ` using `pv_integrable X hG v`. Take `⟨hL0, hLt⟩` from `localRepresentationL2 X u hQ v`. Take `⟨β, hβm, hβ⟩` from `quot_bruhat X u hQ v`. Use `set ν' := μ.withDensity β with hν'`.

Establish `htr : ∀ F : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable F → (∀ s ∈ NHloc X u v, ∀ x, F (s * x) = F x) → ∫⁻ x, F x ∂(νl v) = ∫⁻ x, F x ∂ν'`. Introduce `F hF hi`. Rewrite using `[hβ F hF hi, hν', lintegral_withDensity_eq_lintegral_mul _ hβm hF]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Simplify using `only [Pi.mul_apply]`.

Expand and normalize the polynomial expressions, which then agree. Use `set L := ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(νl v) with hL`. Establish `hinvN : ∀ s ∈ NHloc X u v, ∀ x, ‖f (s * x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2`. Introduce `s hs x`. Take `⟨m, hm, h, hh, rfl⟩` from `hs`.

Establish `hs' : m * h ∈ Sloc X u v` using `mul_mem_Sloc X u v (Nloc_sub X u v hm) (Hloc_sub X u v hh)`. Rewrite using `[← enorm_norm (f (m * h * x)), norm_Wloc_inv X u v hs', enorm_norm]`. Establish `hK1 : ∀ y, ∫⁻ x, ‖f (x * y)‖ₑ ^ 2 ∂ν' = L` using `fun y => by`. Rewrite using `[← htr (fun x => ‖f (x * y)‖ₑ ^ 2) ((hfc.comp (continuous_id.mul continuous_const)).enorm.measurable.pow_const 2) (fun s hs x => by simp only [mul_assoc]; exact hinvN s hs (x * y))]`. Conclude with `quot_rightInv X u hQ v (fun x => ‖f x‖ₑ ^ 2) (hfc.enorm.measurable.pow_const 2) hinvN y`.

Establish `hL' : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂ν' = L` using `(htr _ (hfc.enorm.measurable.pow_const 2) hinvN).symm`. Establish `hin : ∀ y, ∫⁻ x, ‖f x‖ₑ * ‖f (x * y)‖ₑ ∂ν' ≤ 2 * L`. Introduce `y`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_add_left (hfc.enorm.measurable.pow_const 2), hK1 y, hL']`.

Use `_ = 2 * L := (two_mul L).symm`. Establish `mf : Measurable fun y => ‖f y‖ₑ` using `hfc.enorm.measurable`. Establish `mp : Measurable fun y => ‖ph y‖ₑ` using `hpc.enorm.measurable`. Use `set A : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞ := fun x => ∫⁻ g, ‖ph g‖ₑ * ∫⁻ h, ‖ph h‖ₑ * ‖f (x * g * h)‖ₑ ∂μ ∂μ with hA`. Use `set T : Formalism.REAL.UJ (X.B.I.ε v) → Formalism.REAL.UJ (X.B.I.ε v) → Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞ := fun x g h => ‖f x‖ₑ * (‖ph g‖ₑ * (‖ph h‖ₑ * ‖f (x * g * h)‖ₑ)) with hTdef`.

Establish `hTm : Measurable fun p : (Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v)) × Formalism.REAL.UJ (X.B.I.ε v) => T p.1.1 p.1.2 p.2`. Establish `h3 : Continuous fun p : (Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v)) × Formalism.REAL.UJ (X.B.I.ε v) => f (p.1.1 * p.1.2 * p.2)` using `hfc.comp (((continuous_fst.comp continuous_fst).mul (continuous_snd.comp continuous_fst)).mul continuous_snd)`. Conclude with `(mf.comp (measurable_fst.comp measurable_fst)).mul ((mp.comp (measurable_snd.comp measurable_fst)).mul ((mp.comp measurable_snd).mul h3.enorm.measurable))`. Establish `hTm' : ∀ g, Measurable fun p : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => T p.1 g p.2`. Introduce `g`.

Conclude with `hTm.comp (measurable_fst.prodMk measurable_const |>.prodMk measurable_snd)`. Establish `e1 : ∫⁻ x, ‖f x‖ₑ * A x ∂ν' = ∫⁻ g, ∫⁻ h, ∫⁻ x, T x g h ∂ν' ∂μ ∂μ`. Establish `step1 : ∀ x, ‖f x‖ₑ * A x = ∫⁻ g, ∫⁻ h, T x g h ∂μ ∂μ`. Introduce `x`. Rewrite using `[hA]`.

Simplify using `only []`. Rewrite using `[← lintegral_const_mul' _ _ enorm_ne_top]`. Use `lintegral_congr fun g => ?_` and prove the remaining obligations. Rewrite using `[← lintegral_const_mul' _ _ enorm_ne_top, ← lintegral_const_mul' _ _ enorm_ne_top]`. Simplify using `only [step1]`.

Rewrite using `[lintegral_lintegral_swap (hTm.lintegral_prod_right').aemeasurable]`. Use `lintegral_congr fun g => ?_` and prove the remaining obligations. Conclude with `lintegral_lintegral_swap (hTm' g).aemeasurable`. Establish `hT : ∫⁻ x, ‖f x‖ₑ * A x ∂ν' < ⊤`. Rewrite using `[e1]`.

Establish `hb : ∀ g h, ∫⁻ x, T x g h ∂ν' ≤ ‖ph g‖ₑ * (‖ph h‖ₑ * (2 * L))`. Introduce `g h`. Establish `: ∀ x, T x g h = ‖ph g‖ₑ * (‖ph h‖ₑ * (‖f x‖ₑ * ‖f (x * (g * h))‖ₑ))`. Introduce `x`. Simplify using `only [hTdef, mul_assoc]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [this]`. Rewrite using `[lintegral_const_mul' _ _ enorm_ne_top, lintegral_const_mul' _ _ enorm_ne_top]`. Use `gcongr`. Conclude with `hin _`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← lintegral_mul_const _ mp]`. Use `lintegral_congr fun g => ?_` and prove the remaining obligations. Rewrite using `[lintegral_const_mul' _ _ enorm_ne_top, lintegral_mul_const _ mp]`. Use `_ < ⊤ := ENNReal.mul_lt_top hpI.2 (ENNReal.mul_lt_top hpI.2 (ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.2 hLt)))`.

Choose the witnesses or unpack the hypotheses as in `⟨x, hfx, hAx⟩ : ∃ x, f x ≠ 0 ∧ A x < ⊤ := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Use `set E := {x | f x ≠ 0} with hE`. Establish `hEm : MeasurableSet E` using `(isClosed_eq hfc continuous_const).isOpen_compl.measurableSet`.

Establish `hE0 : ν' E ≠ 0`. Introduce `h0`. Apply `hL0` to reduce the goal to its premises. Rewrite using `[← hL']`. Apply `(lintegral_eq_zero_iff (mf.pow_const 2)).2` to reduce the goal to its premises.

Establish `: ∀ᵐ y ∂ν', y ∉ E` using `measure_eq_zero_iff_ae_notMem.1 h0`. Use `filter_upwards [this] with y hy`. Simplify using `only [hE, Set.mem_setOf_eq, not_not] at hy`. Simplify using `[hy]`. Establish `hle : ∀ y, E.indicator (fun _ => (⊤ : ℝ≥0∞)) y ≤ ‖f y‖ₑ * A y`.

Introduce `y`. Distinguish the cases in `hy : y ∈ E`. Rewrite using `[Set.indicator_of_mem hy, top_le_iff, top_le_iff.1 (hcon y hy), ENNReal.mul_top]`. Conclude with `enorm_ne_zero.2 hy`. Rewrite using `[Set.indicator_of_notMem hy]`.

Conclude with `zero_le`. Use `lt_of_le_of_lt (lintegral_mono hle) hT` as an intermediate fact. Rewrite `this` using `[lintegral_indicator_const hEm, ENNReal.top_mul hE0]`. Conclude with `lt_irrefl _ this`. Use `set Φ : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) → X.Vloc u v := fun p => ph p.1 • (ph p.2 • f (x * p.1 * p.2)) with hΦ`.

Establish `hΦc : Continuous Φ` using `(hpc.comp continuous_fst).smul ((hpc.comp continuous_snd).smul (hfc.comp ((continuous_const.mul continuous_fst).mul continuous_snd)))`. Establish `hΦi : Integrable Φ (μ.prod μ)`. Use `⟨hΦc.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Use `show ∫⁻ p, ‖Φ p‖ₑ ∂(μ.prod μ) < ⊤`. Rewrite using `[lintegral_prod _ hΦc.enorm.aemeasurable]`.

Establish `e2 : ∀ g, ∫⁻ h, ‖Φ (g, h)‖ₑ ∂μ = ‖ph g‖ₑ * ∫⁻ h, ‖ph h‖ₑ * ‖f (x * g * h)‖ₑ ∂μ` using `fun g => by`. Simplify using `only [hΦ, enorm_smul]`. Rewrite using `[lintegral_const_mul' _ _ enorm_ne_top]`. Simplify using `only [e2]`. Conclude with `hAx`.

Establish `hΦv : ∫ p, Φ p ∂(μ.prod μ) = c • c • f x`. Rewrite using `[integral_prod _ hΦi]`. Establish `e3 : ∀ g, ∫ h, Φ (g, h) ∂μ = c • (ph g • f (x * g))` using `fun g => by`. Simplify using `only [hΦ]`. Rewrite using `[integral_smul, (hc (x * g)).2, smul_comm]`.

Simplify using `only [e3]`. Rewrite using `[integral_smul, (hc x).2]`. Establish `hS` using `measurePreserving_prod_mul μ μ`. Establish `he : MeasurableEmbedding (fun z : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => (z.1, z.1 * z.2))` using `(MeasurableEquiv.shearMulRight (Formalism.REAL.UJ (X.B.I.ε v))).measurableEmbedding`. Use `set Ψ : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) → X.Vloc u v := fun p => ph p.1 • (ph (p.1⁻¹ * p.2) • f (x * p.2)) with hΨ`.

Establish `hcomp : Ψ ∘ (fun z : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => (z.1, z.1 * z.2)) = Φ`. Use function extensionality and compare the values at `z`. Simplify using `only [Function.comp_apply, hΨ, hΦ, inv_mul_cancel_left, mul_assoc]`. Establish `hΨi : Integrable Ψ (μ.prod μ)` using `(hS.integrable_comp_emb he).1 (by rw [hcomp]; exact hΦi)`. Establish `hΨv : ∫ p, Ψ p ∂(μ.prod μ) = c • f x`.

Rewrite using `[integral_prod_symm _ hΨi]`. Establish `e4 : ∀ y, ∫ g, Ψ (g, y) ∂μ = ph y • f (x * y)` using `fun y => by`. Simplify using `only [hΨ, smul_smul]`. Rewrite using `[integral_smul_const, (pv_conv X v y).2]`. Simplify using `only [e4]`.

Conclude with `(hc x).2`. Establish `hΦΨ : ∫ p, Φ p ∂(μ.prod μ) = ∫ p, Ψ p ∂(μ.prod μ)`. Rewrite using `[← hcomp]`. Conclude with `hS.integral_comp he Ψ`. Rewrite `hΦΨ` using `[hΦv, hΨv, smul_smul]`.

Establish `h5 : (c * c - c) • f x = 0` using `by rw [sub_smul, hΦΨ, sub_self]`. Establish `h6 : c * c - c = 0` using `(smul_eq_zero.1 h5).resolve_right hfx`. Establish `h7 : c * (c - 1) = 0` using `by rw [mul_sub, mul_one]; exact h6`. Conclude with `sub_eq_zero.1 ((mul_eq_zero.1 h7).resolve_left hc0)`.
-/
theorem local_scalar_reduction : LocScalarStep := by
  intro D hG X u μS νl C hQ v c hc0 hc
  set μ := Formalism.REAL.muG (X.B.I.ε v) with hμ
  set f := X.Wloc u v with hfdef
  set ph := Pv X v with hph
  have hfc : Continuous f := X.Wloc_cont u v
  have hpc : Continuous ph := continuous_Pv X v
  have hpI : Integrable ph μ := pv_integrable X hG v
  obtain ⟨hL0, hLt⟩ := localRepresentationL2 X u hQ v
  obtain ⟨β, hβm, hβ⟩ := quot_bruhat X u hQ v
  set ν' := μ.withDensity β with hν'
  have htr : ∀ F : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable F → (∀ s ∈ NHloc X u v, ∀ x, F (s * x) = F x) →
      ∫⁻ x, F x ∂(νl v) = ∫⁻ x, F x ∂ν' := by
    intro F hF hi
    rw [hβ F hF hi, hν', lintegral_withDensity_eq_lintegral_mul _ hβm hF]
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply]; ring
  set L := ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(νl v) with hL
  have hinvN : ∀ s ∈ NHloc X u v, ∀ x, ‖f (s * x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2 := by
    intro s hs x
    obtain ⟨m, hm, h, hh, rfl⟩ := hs
    have hs' : m * h ∈ Sloc X u v := mul_mem_Sloc X u v (Nloc_sub X u v hm) (Hloc_sub X u v hh)
    rw [← enorm_norm (f (m * h * x)), norm_Wloc_inv X u v hs', enorm_norm]
  have hK1 : ∀ y, ∫⁻ x, ‖f (x * y)‖ₑ ^ 2 ∂ν' = L := fun y => by
    rw [← htr (fun x => ‖f (x * y)‖ₑ ^ 2) ((hfc.comp (continuous_id.mul continuous_const)).enorm.measurable.pow_const 2)
      (fun s hs x => by simp only [mul_assoc]; exact hinvN s hs (x * y))]
    exact quot_rightInv X u hQ v (fun x => ‖f x‖ₑ ^ 2) (hfc.enorm.measurable.pow_const 2) hinvN y
  have hL' : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂ν' = L := (htr _ (hfc.enorm.measurable.pow_const 2) hinvN).symm
  have hin : ∀ y, ∫⁻ x, ‖f x‖ₑ * ‖f (x * y)‖ₑ ∂ν' ≤ 2 * L := by
    intro y
    calc ∫⁻ x, ‖f x‖ₑ * ‖f (x * y)‖ₑ ∂ν' ≤ ∫⁻ x, (‖f x‖ₑ ^ 2 + ‖f (x * y)‖ₑ ^ 2) ∂ν' :=
          lintegral_mono fun x => ennreal_mul_le_sq _ _
      _ = L + L := by
          rw [lintegral_add_left (hfc.enorm.measurable.pow_const 2), hK1 y, hL']
      _ = 2 * L := (two_mul L).symm
  have mf : Measurable fun y => ‖f y‖ₑ := hfc.enorm.measurable
  have mp : Measurable fun y => ‖ph y‖ₑ := hpc.enorm.measurable
  set A : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞ := fun x =>
    ∫⁻ g, ‖ph g‖ₑ * ∫⁻ h, ‖ph h‖ₑ * ‖f (x * g * h)‖ₑ ∂μ ∂μ with hA

  set T : Formalism.REAL.UJ (X.B.I.ε v) → Formalism.REAL.UJ (X.B.I.ε v) → Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞ :=
    fun x g h => ‖f x‖ₑ * (‖ph g‖ₑ * (‖ph h‖ₑ * ‖f (x * g * h)‖ₑ)) with hTdef
  have hTm : Measurable fun p : (Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v)) × Formalism.REAL.UJ (X.B.I.ε v) =>
      T p.1.1 p.1.2 p.2 := by
    have h3 : Continuous fun p : (Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v)) × Formalism.REAL.UJ (X.B.I.ε v) =>
        f (p.1.1 * p.1.2 * p.2) :=
      hfc.comp (((continuous_fst.comp continuous_fst).mul (continuous_snd.comp continuous_fst)).mul continuous_snd)
    exact (mf.comp (measurable_fst.comp measurable_fst)).mul ((mp.comp (measurable_snd.comp measurable_fst)).mul
      ((mp.comp measurable_snd).mul h3.enorm.measurable))
  have hTm' : ∀ g, Measurable fun p : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => T p.1 g p.2 := by
    intro g
    exact hTm.comp (measurable_fst.prodMk measurable_const |>.prodMk measurable_snd)
  have e1 : ∫⁻ x, ‖f x‖ₑ * A x ∂ν' = ∫⁻ g, ∫⁻ h, ∫⁻ x, T x g h ∂ν' ∂μ ∂μ := by
    have step1 : ∀ x, ‖f x‖ₑ * A x = ∫⁻ g, ∫⁻ h, T x g h ∂μ ∂μ := by
      intro x
      rw [hA]
      simp only []
      rw [← lintegral_const_mul' _ _ enorm_ne_top]
      refine lintegral_congr fun g => ?_
      rw [← lintegral_const_mul' _ _ enorm_ne_top, ← lintegral_const_mul' _ _ enorm_ne_top]
    simp only [step1]
    rw [lintegral_lintegral_swap (hTm.lintegral_prod_right').aemeasurable]
    refine lintegral_congr fun g => ?_
    exact lintegral_lintegral_swap (hTm' g).aemeasurable
  have hT : ∫⁻ x, ‖f x‖ₑ * A x ∂ν' < ⊤ := by
    rw [e1]
    have hb : ∀ g h, ∫⁻ x, T x g h ∂ν' ≤ ‖ph g‖ₑ * (‖ph h‖ₑ * (2 * L)) := by
      intro g h
      have : ∀ x, T x g h = ‖ph g‖ₑ * (‖ph h‖ₑ * (‖f x‖ₑ * ‖f (x * (g * h))‖ₑ)) := by
        intro x; simp only [hTdef, mul_assoc]; ring
      simp only [this]
      rw [lintegral_const_mul' _ _ enorm_ne_top, lintegral_const_mul' _ _ enorm_ne_top]
      gcongr
      exact hin _
    calc ∫⁻ g, ∫⁻ h, ∫⁻ x, T x g h ∂ν' ∂μ ∂μ ≤ ∫⁻ g, ∫⁻ h, ‖ph g‖ₑ * (‖ph h‖ₑ * (2 * L)) ∂μ ∂μ :=
          lintegral_mono fun g => lintegral_mono fun h => hb g h
      _ = (∫⁻ g, ‖ph g‖ₑ ∂μ) * ((∫⁻ h, ‖ph h‖ₑ ∂μ) * (2 * L)) := by
          rw [← lintegral_mul_const _ mp]
          refine lintegral_congr fun g => ?_
          rw [lintegral_const_mul' _ _ enorm_ne_top, lintegral_mul_const _ mp]
      _ < ⊤ := ENNReal.mul_lt_top hpI.2 (ENNReal.mul_lt_top hpI.2
          (ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.2 hLt)))

  obtain ⟨x, hfx, hAx⟩ : ∃ x, f x ≠ 0 ∧ A x < ⊤ := by
    by_contra hcon
    push Not at hcon
    set E := {x | f x ≠ 0} with hE
    have hEm : MeasurableSet E := (isClosed_eq hfc continuous_const).isOpen_compl.measurableSet
    have hE0 : ν' E ≠ 0 := by
      intro h0
      apply hL0
      rw [← hL']
      apply (lintegral_eq_zero_iff (mf.pow_const 2)).2
      have : ∀ᵐ y ∂ν', y ∉ E := measure_eq_zero_iff_ae_notMem.1 h0
      filter_upwards [this] with y hy
      simp only [hE, Set.mem_setOf_eq, not_not] at hy
      simp [hy]
    have hle : ∀ y, E.indicator (fun _ => (⊤ : ℝ≥0∞)) y ≤ ‖f y‖ₑ * A y := by
      intro y
      by_cases hy : y ∈ E
      · rw [Set.indicator_of_mem hy, top_le_iff, top_le_iff.1 (hcon y hy), ENNReal.mul_top]
        exact enorm_ne_zero.2 hy
      · rw [Set.indicator_of_notMem hy]; exact zero_le
    have := lt_of_le_of_lt (lintegral_mono hle) hT
    rw [lintegral_indicator_const hEm, ENNReal.top_mul hE0] at this
    exact lt_irrefl _ this

  set Φ : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) → X.Vloc u v :=
    fun p => ph p.1 • (ph p.2 • f (x * p.1 * p.2)) with hΦ
  have hΦc : Continuous Φ :=
    (hpc.comp continuous_fst).smul ((hpc.comp continuous_snd).smul
      (hfc.comp ((continuous_const.mul continuous_fst).mul continuous_snd)))
  have hΦi : Integrable Φ (μ.prod μ) := by
    refine ⟨hΦc.aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖Φ p‖ₑ ∂(μ.prod μ) < ⊤
    rw [lintegral_prod _ hΦc.enorm.aemeasurable]
    have e2 : ∀ g, ∫⁻ h, ‖Φ (g, h)‖ₑ ∂μ = ‖ph g‖ₑ * ∫⁻ h, ‖ph h‖ₑ * ‖f (x * g * h)‖ₑ ∂μ := fun g => by
      simp only [hΦ, enorm_smul]
      rw [lintegral_const_mul' _ _ enorm_ne_top]
    simp only [e2]
    exact hAx
  have hΦv : ∫ p, Φ p ∂(μ.prod μ) = c • c • f x := by
    rw [integral_prod _ hΦi]
    have e3 : ∀ g, ∫ h, Φ (g, h) ∂μ = c • (ph g • f (x * g)) := fun g => by
      simp only [hΦ]
      rw [integral_smul, (hc (x * g)).2, smul_comm]
    simp only [e3]
    rw [integral_smul, (hc x).2]
  have hS := measurePreserving_prod_mul μ μ
  have he : MeasurableEmbedding (fun z : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => (z.1, z.1 * z.2)) :=
    (MeasurableEquiv.shearMulRight (Formalism.REAL.UJ (X.B.I.ε v))).measurableEmbedding
  set Ψ : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) → X.Vloc u v :=
    fun p => ph p.1 • (ph (p.1⁻¹ * p.2) • f (x * p.2)) with hΨ
  have hcomp : Ψ ∘ (fun z : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => (z.1, z.1 * z.2)) = Φ := by
    funext z
    simp only [Function.comp_apply, hΨ, hΦ, inv_mul_cancel_left, mul_assoc]
  have hΨi : Integrable Ψ (μ.prod μ) := (hS.integrable_comp_emb he).1 (by rw [hcomp]; exact hΦi)
  have hΨv : ∫ p, Ψ p ∂(μ.prod μ) = c • f x := by
    rw [integral_prod_symm _ hΨi]
    have e4 : ∀ y, ∫ g, Ψ (g, y) ∂μ = ph y • f (x * y) := fun y => by
      simp only [hΨ, smul_smul]
      rw [integral_smul_const, (pv_conv X v y).2]
    simp only [e4]
    exact (hc x).2
  have hΦΨ : ∫ p, Φ p ∂(μ.prod μ) = ∫ p, Ψ p ∂(μ.prod μ) := by
    rw [← hcomp]
    exact hS.integral_comp he Ψ
  rw [hΦv, hΨv, smul_smul] at hΦΨ
  have h5 : (c * c - c) • f x = 0 := by rw [sub_smul, hΦΨ, sub_self]
  have h6 : c * c - c = 0 := (smul_eq_zero.1 h5).resolve_right hfx
  have h7 : c * (c - 1) = 0 := by rw [mul_sub, mul_one]; exact h6
  exact sub_eq_zero.1 ((mul_eq_zero.1 h7).resolve_left hc0)

end Main

end Formalism.L2.SG.Pf.WuDec.LS
