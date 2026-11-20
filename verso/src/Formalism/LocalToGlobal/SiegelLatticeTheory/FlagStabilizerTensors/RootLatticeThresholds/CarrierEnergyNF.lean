import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyCV
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ConstPinOfStd

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.Carrier.EnergyNF

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf
  Formalism.L2.SG.Pf.Carrier.EnergyPlace Formalism.L2.SG.Pf.Carrier.EnergyFinal Formalism.L2.SG.AdBridge Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `hm : Measurable (fun x : ι → E => ∏ i, F i (x i))` using `Finset.measurable_prod _ fun i _ => (hF i).comp (measurable_pi_apply i)`. Establish `key : ∀ s : Finset ι, ∀ x : ι → E, (∫⋯∫⁻_s, (fun x : ι → E => ∏ i, F i (x i)) ∂μ) x = (∏ i ∈ s, ∫⁻ y, F i y ∂(μ i)) * ∏ i ∈ sᶜ, F i (x i)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro x`.

Simplify using the standard rewrite rules. Consider the case `insert i s hi ih`. Introduce `x`. Rewrite using `[lmarginal_insert _ hm hi]`. Repeatedly rewrite using `[ih]`.

Establish `hsplit : ∀ y, ∏ j ∈ sᶜ, F j (Function.update x i y j) = F i y * ∏ j ∈ (insert i s)ᶜ, F j (x j)`. Introduce `y`. Establish `hic : i ∈ sᶜ` using `Finset.mem_compl.2 hi`. Rewrite using `[← Finset.mul_prod_erase _ _ hic, Function.update_self, Finset.compl_insert]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hj)]`. Repeatedly rewrite using `[hsplit]`. Establish `h2 : ∀ y, (∏ i ∈ s, ∫⁻ y, F i y ∂(μ i)) * (F i y * ∏ j ∈ (insert i s)ᶜ, F j (x j)) = ((∏ i ∈ s, ∫⁻ y, F i y ∂(μ i)) * ∏ j ∈ (insert i s)ᶜ, F j (x j)) * F i y` using `fun y => by ring`. Repeatedly rewrite using `[h2]`.

Rewrite using `[lintegral_const_mul _ (hF i), Finset.prod_insert hi]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[lintegral_eq_lmarginal_univ (fun _ => Classical.arbitrary E), key, Finset.compl_univ, Finset.prod_empty, mul_one]`.
-/
theorem lintegral_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E] [Nonempty E]
    (μ : ι → Measure E) [∀ i, SigmaFinite (μ i)] (F : ι → E → ℝ≥0∞) (hF : ∀ i, Measurable (F i)) :
    ∫⁻ x, ∏ i, F i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ y, F i y ∂(μ i) := by
  have hm : Measurable (fun x : ι → E => ∏ i, F i (x i)) :=
    Finset.measurable_prod _ fun i _ => (hF i).comp (measurable_pi_apply i)
  have key : ∀ s : Finset ι, ∀ x : ι → E,
      (∫⋯∫⁻_s, (fun x : ι → E => ∏ i, F i (x i)) ∂μ) x = (∏ i ∈ s, ∫⁻ y, F i y ∂(μ i)) * ∏ i ∈ sᶜ, F i (x i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x; simp
    | insert i s hi ih =>
      intro x
      rw [lmarginal_insert _ hm hi]
      simp_rw [ih]
      have hsplit : ∀ y, ∏ j ∈ sᶜ, F j (Function.update x i y j) = F i y * ∏ j ∈ (insert i s)ᶜ, F j (x j) := by
        intro y
        have hic : i ∈ sᶜ := Finset.mem_compl.2 hi
        rw [← Finset.mul_prod_erase _ _ hic, Function.update_self, Finset.compl_insert]
        congr 1
        refine Finset.prod_congr rfl fun j hj => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      simp_rw [hsplit]
      have h2 : ∀ y, (∏ i ∈ s, ∫⁻ y, F i y ∂(μ i)) * (F i y * ∏ j ∈ (insert i s)ᶜ, F j (x j)) =
          ((∏ i ∈ s, ∫⁻ y, F i y ∂(μ i)) * ∏ j ∈ (insert i s)ᶜ, F j (x j)) * F i y := fun y => by ring
      simp_rw [h2]
      rw [lintegral_const_mul _ (hF i), Finset.prod_insert hi]
      ring
  rw [lintegral_eq_lmarginal_univ (fun _ => Classical.arbitrary E), key, Finset.compl_univ, Finset.prod_empty,
    mul_one]

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}

/- English proof (translation)
Take `⟨hpos, hLc⟩` from `hL`. Establish `hG : MeasurableSet (Good X u u')`. Rewrite using `[good_eq_pi]`. Conclude with `MeasurableSet.univ_pi fun _ => goodV_meas u u'`. Establish `hpt : ∀ c ∈ Good X u u', ENNReal.ofReal (Formalism.L2.SG.RealObj.wt X u u' c * hilbertSchmidtSqGram X u u' 1 c) = ∏ v, ENNReal.ofReal (wtV u u' (c v) * L v (c v))`.

Introduce `c hc`. Establish `hcv : ∀ v, c v ∈ GoodV u u'` using `fun v => hc v`. Rewrite using `[← ENNReal.ofReal_prod_of_nonneg (fun v _ => mul_nonneg (wtV_nonneg u u' (hcv v)) ((hpos v).2 _))]`. Use `congr 1`. Establish `hO : hilbertSchmidtSqGram X u u' 1 c = ∏ v, L v (c v)`.

Unfold `hilbertSchmidtSqGram`. Rewrite using `[hilbert_schmidt_tensor_product_factor]`. Conclude with `Finset.prod_congr rfl fun v _ => hLc c hc v`. Rewrite using `[hO, Finset.prod_mul_distrib]`. Both sides reduce to the same expression.

Unfold `intCe`. Rewrite using `[setLIntegral_congr_fun hG hpt, good_eq_pi]`. Establish `h2s : SigmaFinite ((2 : ℝ≥0∞) • (volume : Measure ℂ))`. Establish `h : ((2 : ℝ≥0∞) • (volume : Measure ℂ)) = ((2 : NNReal) • (volume : Measure ℂ))`. Rewrite using `[ENNReal.smul_def]`.

Simplify using the standard rewrite rules. Rewrite using `[h]`. Use `infer_instance`. Unfold `dcInf`. Rewrite using `[Measure.restrict_pi_pi]`.

Establish `hdc : SigmaFinite ((dcV (D` using `D)).restrict (GoodV u u')) := by unfold dcV; infer_instance`. Rewrite using `[show (Measure.pi fun _ : Fin (D.R.rS + 1) => (2 : ℝ≥0∞) • (volume : Measure ℂ)) = dcV (D := D) from rfl]`. Conclude with `lintegral_pi_prod _ (fun v cv => ENNReal.ofReal (wtV u u' cv * L v cv)) (fun v => ENNReal.measurable_ofReal.comp ((wtV_cont u u').measurable.mul (hpos v).1))`.
-/
theorem intCe_eq_prodE (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) (hL : LocRep X u u' L) :
    intCe X u u' 1 = ∏ v, ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv * L v cv) ∂(dcV (D := D)) := by
  obtain ⟨hpos, hLc⟩ := hL
  have hG : MeasurableSet (Good X u u') := by
    rw [good_eq_pi]; exact MeasurableSet.univ_pi fun _ => goodV_meas u u'
  have hpt : ∀ c ∈ Good X u u', ENNReal.ofReal (Formalism.L2.SG.RealObj.wt X u u' c * hilbertSchmidtSqGram X u u' 1 c) =
      ∏ v, ENNReal.ofReal (wtV u u' (c v) * L v (c v)) := by
    intro c hc
    have hcv : ∀ v, c v ∈ GoodV u u' := fun v => hc v
    rw [← ENNReal.ofReal_prod_of_nonneg (fun v _ =>
      mul_nonneg (wtV_nonneg u u' (hcv v)) ((hpos v).2 _))]
    congr 1
    have hO : hilbertSchmidtSqGram X u u' 1 c = ∏ v, L v (c v) := by
      unfold hilbertSchmidtSqGram
      rw [hilbert_schmidt_tensor_product_factor]
      exact Finset.prod_congr rfl fun v _ => hLc c hc v
    rw [hO, Finset.prod_mul_distrib]
    rfl
  unfold intCe
  rw [setLIntegral_congr_fun hG hpt, good_eq_pi]
  have h2s : SigmaFinite ((2 : ℝ≥0∞) • (volume : Measure ℂ)) := by
    have h : ((2 : ℝ≥0∞) • (volume : Measure ℂ)) = ((2 : NNReal) • (volume : Measure ℂ)) := by
      rw [ENNReal.smul_def]; simp
    rw [h]; infer_instance
  unfold dcInf
  rw [Measure.restrict_pi_pi]
  have hdc : SigmaFinite ((dcV (D := D)).restrict (GoodV u u')) := by unfold dcV; infer_instance
  rw [show (Measure.pi fun _ : Fin (D.R.rS + 1) => (2 : ℝ≥0∞) • (volume : Measure ℂ)) = dcV (D := D) from rfl]
  exact lintegral_pi_prod _ (fun v cv => ENNReal.ofReal (wtV u u' cv * L v cv))
    (fun v => ENNReal.measurable_ofReal.comp ((wtV_cont u u').measurable.mul (hpos v).1))

def PlaceEnergyE (P : Parts X u u') (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ)
    (K : InfinitePlace X.B.I.F → ℝ) : Prop :=
  ∀ v, ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv * L v cv) ∂(dcV (D := D)) =
    ENNReal.ofReal (K v) * Formalism.FourierDecayAlt.B.normSq (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))

/- English proof (translation)
Use `set n : InfinitePlace X.B.I.F → ℝ := fun v => (Formalism.FourierDecayAlt.B.normSq (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))).toReal with hn`. Establish `hC : IntC X u u' 1 = (∏ v, K v) * ∏ v, n v`. Unfold `IntC`. Rewrite using `[intCe_eq_prodE L h1]`. Rewrite using `[Finset.prod_congr rfl (fun v _ => h2 v)]`.

Rewrite using `[ENNReal.toReal_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.toReal_mul, ENNReal.toReal_ofReal (h3.1 v)]`. Unfold `Parts.EnergyNorm IntNX`. Rewrite using `[hC]`.

Establish `hre : (∏ j, (Formalism.FourierDecayAlt.B.normSq (P.T j).base (P.f j)).toReal / P.Gam0) = (∏ v, n v) * (P.Gam0 ^ P.S.f)⁻¹`. Rewrite using `[← Equiv.prod_comp P.τ.symm, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, ← Fintype.card_congr P.τ, Fintype.card_fin, div_eq_mul_inv]`. Rewrite using `[hre, ← h3.2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem energyNorm_of_stepsE (P : Parts X u u') (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) (K : InfinitePlace X.B.I.F → ℝ)
    (h1 : LocRep X u u' L) (h2 : PlaceEnergyE P L K) (h3 : ConstPin P ψ K) :
    P.EnergyNorm (IntNX X u u' ψ) := by
  set n : InfinitePlace X.B.I.F → ℝ :=
    fun v => (Formalism.FourierDecayAlt.B.normSq (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))).toReal with hn
  have hC : IntC X u u' 1 = (∏ v, K v) * ∏ v, n v := by
    unfold IntC
    rw [intCe_eq_prodE L h1]
    rw [Finset.prod_congr rfl (fun v _ => h2 v)]
    rw [ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (h3.1 v)]
  unfold Parts.EnergyNorm IntNX
  rw [hC]
  have hre : (∏ j, (Formalism.FourierDecayAlt.B.normSq (P.T j).base (P.f j)).toReal / P.Gam0) =
      (∏ v, n v) * (P.Gam0 ^ P.S.f)⁻¹ := by
    rw [← Equiv.prod_comp P.τ.symm, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
      ← Fintype.card_congr P.τ, Fintype.card_fin, div_eq_mul_inv]
  rw [hre, ← h3.2]
  ring

/- English proof (translation)
Introduce `v`. Rewrite using `[setLIntegral_congr_fun (goodV_meas u u') (fun cv hcv => by rw [hPN v cv hcv])]`. Rewrite using `[hCV hk hT v (fun q => ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF (P.T (P.τ.symm v)).base (P.f (P.τ.symm v)) (Formalism.FourierDecayAlt.B.gq (P.T (P.τ.symm v)).base q))‖ ^ 2) (fun q => by positivity)]`. Rewrite using `[← Formalism.L2.SG.Pf.Carrier.EnergyKM.kMatch_holds P hg hrd hr hk hg0 hk1]`. Both sides reduce to the same expression.
-/
theorem placeEnergyE_of_steps (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hk : P.S.G.k = D.R.k)
    (hT : ∀ v, Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z = Tw (D := D) u ∧
      Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z' = Tw (D := D) u')
    (hg : (P.S.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ)) (hrd : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE)
    (hg0 : 0 < P.S.g) (hk1 : 1 ≤ P.S.G.k)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ)
    (hPN : PlaceNorm P hr L) (hCV : ChangeVar P hr) :
    PlaceEnergyE P L (fun _ => EnergyConst.Kexp P) := by
  intro v
  rw [setLIntegral_congr_fun (goodV_meas u u') (fun cv hcv => by rw [hPN v cv hcv])]
  rw [hCV hk hT v (fun q => ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))
      (Formalism.FourierDecayAlt.B.gq (P.T (P.τ.symm v)).base q))‖ ^ 2) (fun q => by positivity)]
  rw [← Formalism.L2.SG.Pf.Carrier.EnergyKM.kMatch_holds P hg hrd hr hk hg0 hk1]
  rfl

/- English proof (translation)
Take `⟨L, hL⟩` from `Formalism.L2.SG.Pf.Carrier.EnergyPfLoc.locRep_holds X u u'`. Rewrite using `[intN_massDataY]`. Conclude with `energyNorm_of_stepsE P ψ L (fun _ => EnergyConst.Kexp P) hL (placeEnergyE_of_steps P hr hk hT hg hrd hg0 hk1 L (placeNorm_of_G P hr hPN L hL) hCV) (EnergyConst.constPin_of P ψ hC hMS hf)`.
-/
theorem energyNorm_bookY_of_placeNormG_of_changeVar (hb : AdBridgeIso X.B.I) (Y : Full X)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hk : P.S.G.k = D.R.k)
    (hT : ∀ v, Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z = Tw (D := D) u ∧
      Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z' = Tw (D := D) u')
    (hg : (P.S.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ)) (hrd : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE)
    (hg0 : 0 < P.S.g) (hk1 : 1 ≤ P.S.G.k) (hf : Fintype.card (InfinitePlace X.B.I.F) = D.R.f)
    (hC : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hMS : EnergyConst.LemmaMS X u u' ψ)
    (hPN : PlaceNormG P hr) (hCV : ChangeVar P hr) :
    P.EnergyNorm (massDataY X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).IntN := by
  obtain ⟨L, hL⟩ := Formalism.L2.SG.Pf.Carrier.EnergyPfLoc.locRep_holds X u u'
  rw [intN_massDataY]
  exact energyNorm_of_stepsE P ψ L (fun _ => EnergyConst.Kexp P) hL
    (placeEnergyE_of_steps P hr hk hT hg hrd hg0 hk1 L (placeNorm_of_G P hr hPN L hL) hCV)
    (EnergyConst.constPin_of P ψ hC hMS hf)

/- English proof (translation)
The claim follows from `energyNorm_bookY_of_placeNormG_of_changeVar hb Y X0 ψ sd C Th vR Q i0 i0' νq P hr hk hT hg hrd hg0 hk1 hf hC hMS hPN (Formalism.L2.SG.Pf.Carrier.EnergyCV.changeVar_of_pos P hr hg0)`.
-/
theorem energy_norm_bound_second_form (hb : AdBridgeIso X.B.I) (Y : Full X)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hk : P.S.G.k = D.R.k)
    (hT : ∀ v, Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z = Tw (D := D) u ∧
      Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z' = Tw (D := D) u')
    (hg : (P.S.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ)) (hrd : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE)
    (hg0 : 0 < P.S.g) (hk1 : 1 ≤ P.S.G.k) (hf : Fintype.card (InfinitePlace X.B.I.F) = D.R.f)
    (hC : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hMS : EnergyConst.LemmaMS X u u' ψ)
    (hPN : PlaceNormG P hr) :
    P.EnergyNorm (massDataY X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).IntN :=
  energyNorm_bookY_of_placeNormG_of_changeVar hb Y X0 ψ sd C Th vR Q i0 i0' νq P hr hk hT hg hrd hg0 hk1 hf hC hMS hPN
    (Formalism.L2.SG.Pf.Carrier.EnergyCV.changeVar_of_pos P hr hg0)

/- English proof (translation)
The claim follows from `energy_norm_bound_second_form hb Y X0 ψ sd C Th vR Q i0 i0' νq P hr hk hT hg hrd hg0 hk1 hf hC (hMS hψ hstd hC) hPN`.
-/
theorem energy_norm_bound_third_form (hb : AdBridgeIso X.B.I) (Y : Full X)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hk : P.S.G.k = D.R.k)
    (hT : ∀ v, Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z = Tw (D := D) u ∧
      Formalism.QuantumDeterminants.Tz P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z' = Tw (D := D) u')
    (hg : (P.S.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ)) (hrd : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE)
    (hg0 : 0 < P.S.g) (hk1 : 1 ≤ P.S.G.k) (hf : Fintype.card (InfinitePlace X.B.I.F) = D.R.f)
    (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hstd : Formalism.L2.SG.LocVol.IsStdChar ψ)
    (hC : Formalism.L2.SG.LocVol.ProdConv X u u' ψ) (hMS : EnergyConst2.LemmaMSStd X u u' ψ)
    (hPN : PlaceNormG P hr) :
    P.EnergyNorm (massDataY X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).IntN :=
  energy_norm_bound_second_form hb Y X0 ψ sd C Th vR Q i0 i0' νq P hr hk hT hg hrd hg0 hk1 hf hC (hMS hψ hstd hC) hPN

end Formalism.L2.SG.Pf.Carrier.EnergyNF
