import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLowerWittTowerIsotropicSplitEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharactersStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairLift.LowCusp

variable {D : D7}

/- English proof (translation)
Take `⟨T, hT, rfl⟩` from `hF`. Establish `key : ∀ w : M.Vec, P (T w)`. Proceed by induction on `hT using Submodule.span_induction with`. Consider the case `mem T hT => exact fun w => hcusp _ (hT.aut w) (hT.cusp w)`. Consider the case `zero => intro w`.

Simplify using `using h0`. Consider the case `add T T' _ _ h h' => intro w`. Simplify using `using hadd _ _ (h w) (h' w)`. Consider the case `smul c T _ h => intro w`. Simplify using `using hsmul c _ (h w)`.

Proceed by induction on `v using PiTensorProduct.induction_on with`. Consider the case `smul_tprod c w`. Simplify using `using hsmul c _ (key w)`. Consider the case `add x y hx hy`. Simplify using `using hadd _ _ hx hy`.
-/
theorem multT_ind {W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S)
    (J : Set (GA D W)) (χ : GA D W → ℂ) (P : (GA D W → ℂ) → Prop) (h0 : P 0)
    (hadd : ∀ φ φ', P φ → P φ' → P (φ + φ')) (hsmul : ∀ (c : ℂ) φ, P φ → P (c • φ))
    (hcusp : ∀ φ, IsAutFunSm θ W φ → IsCuspFun W φ → P φ)
    (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M) : P (F v) := by
  obtain ⟨T, hT, rfl⟩ := hF
  have key : ∀ w : M.Vec, P (T w) := by
    induction hT using Submodule.span_induction with
    | mem T hT => exact fun w => hcusp _ (hT.aut w) (hT.cusp w)
    | zero => intro w; simpa using h0
    | add T T' _ _ h h' => intro w; simpa using hadd _ _ (h w) (h' w)
    | smul c T _ h => intro w; simpa using hsmul c _ (h w)
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c w =>
    simpa using hsmul c _ (key w)
  | add x y hx hy =>
    simpa using hadd _ _ hx hy

/- English proof (translation)
Unfold `Lift.liftInt`. Rewrite using `[← integral_add h h']`. Simplify using `only [Pi.add_apply, mul_add]`.
-/
theorem liftInt_add' {G H S : Type*} [MeasurableSpace H] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {s : S}
    {φ φ' : H → ℂ} {g : G} (h : IntegrableOn (fun x => th g x s * φ x) 𝓕 ν)
    (h' : IntegrableOn (fun x => th g x s * φ' x) 𝓕 ν) :
    Lift.liftInt ν 𝓕 th s (φ + φ') g = Lift.liftInt ν 𝓕 th s φ g + Lift.liftInt ν 𝓕 th s φ' g := by
  unfold Lift.liftInt
  rw [← integral_add h h']
  simp only [Pi.add_apply, mul_add]

/- English proof (translation)
Unfold `Lift.liftInt`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem liftInt_smul' {G H S : Type*} [MeasurableSpace H] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {s : S}
    (c : ℂ) (φ : H → ℂ) (g : G) :
    Lift.liftInt ν 𝓕 th s (c • φ) g = c * Lift.liftInt ν 𝓕 th s φ g := by
  unfold Lift.liftInt
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]; ring

/- English proof (translation)
Simplify using `[Lift.liftInt]`.
-/
theorem liftInt_zero' {G H S : Type*} [MeasurableSpace H] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {s : S}
    (g : G) : Lift.liftInt ν 𝓕 th s (0 : H → ℂ) g = 0 := by
  simp [Lift.liftInt]

structure CtGood {V V' W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ))
    (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (κ : Measure (NI V C)) (𝓝 : Set (NI V C))
    (f : WO V W → ℂ) (f' : WO V' W → ℂ) (g : GA D V) (c : ℂ) (φ : GA D W → ℂ) : Prop where
  integ : ∀ g₁, IntegrableOn (fun h => thetaKO ω g₁ h f * φ h) 𝓕 ν
  integ' : IntegrableOn (fun h => thetaKO ω' 1 h f' * φ h) 𝓕 ν
  mean : IntegrableOn (fun n : NI V C => Lift.liftInt ν 𝓕 (thetaKO ω) f φ ((n : GA D V) * g)) 𝓝 κ
  eq : ∫ n in 𝓝, Lift.liftInt ν 𝓕 (thetaKO ω) f φ ((n : GA D V) * g) ∂κ =
    c * Lift.liftInt ν 𝓕 (thetaKO ω') f' φ 1

section CtGood

variable {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)}
  {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {κ : Measure (NI V C)} {𝓝 : Set (NI V C)}
  {f : WO V W → ℂ} {f' : WO V' W → ℂ} {g : GA D V} {c : ℂ}

/- English proof (translation)
Simplify using `integ' := by simp mean := by simp [liftInt_zero'] eq := by simp [liftInt_zero']`.
-/
theorem CtGood.zero : CtGood C ω ω' ν 𝓕 κ 𝓝 f f' g c 0 where
  integ g₁ := by simp
  integ' := by simp
  mean := by simp [liftInt_zero']
  eq := by simp [liftInt_zero']

/- English proof (translation)
Establish `e : (fun n : NI V C => Lift.liftInt ν 𝓕 (thetaKO ω) f (φ + φ') ((n : GA D V) * g)) = fun n : NI V C => Lift.liftInt ν 𝓕 (thetaKO ω) f φ ((n : GA D V) * g) + Lift.liftInt ν 𝓕 (thetaKO ω) f φ' ((n : GA D V) * g)`. Use function extensionality and compare the values at `fun n => liftInt_add' (h.integ _) (h'.integ _)`. Use `⟨fun g₁ => ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `((h.integ g₁).add (h'.integ g₁)).congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `[mul_add]`.

Use `(h.integ'.add h'.integ').congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `[mul_add]`. Rewrite using `[e]`. Conclude with `h.mean.add h'.mean`. Rewrite using `[e, integral_add h.mean h'.mean, h.eq, h'.eq, liftInt_add' h.integ' h'.integ', mul_add]`.
-/
theorem CtGood.add {φ φ' : GA D W → ℂ} (h : CtGood C ω ω' ν 𝓕 κ 𝓝 f f' g c φ)
    (h' : CtGood C ω ω' ν 𝓕 κ 𝓝 f f' g c φ') : CtGood C ω ω' ν 𝓕 κ 𝓝 f f' g c (φ + φ') := by
  have e : (fun n : NI V C => Lift.liftInt ν 𝓕 (thetaKO ω) f (φ + φ') ((n : GA D V) * g)) =
      fun n : NI V C => Lift.liftInt ν 𝓕 (thetaKO ω) f φ ((n : GA D V) * g) +
        Lift.liftInt ν 𝓕 (thetaKO ω) f φ' ((n : GA D V) * g) :=
    funext fun n => liftInt_add' (h.integ _) (h'.integ _)
  refine ⟨fun g₁ => ?_, ?_, ?_, ?_⟩
  · refine ((h.integ g₁).add (h'.integ g₁)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp [mul_add]
  · refine (h.integ'.add h'.integ').congr (Filter.Eventually.of_forall fun x => ?_)
    simp [mul_add]
  · rw [e]; exact h.mean.add h'.mean
  · rw [e, integral_add h.mean h'.mean, h.eq, h'.eq, liftInt_add' h.integ' h'.integ', mul_add]

/- English proof (translation)
Establish `e : (fun n : NI V C => Lift.liftInt ν 𝓕 (thetaKO ω) f (a • φ) ((n : GA D V) * g)) = fun n : NI V C => a * Lift.liftInt ν 𝓕 (thetaKO ω) f φ ((n : GA D V) * g)`. Use function extensionality and compare the values at `fun n => liftInt_smul' a φ _`. Use `⟨fun g₁ => ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `((h.integ g₁).const_mul a).congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Use `(h.integ'.const_mul a).congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `h.mean.const_mul a`. Rewrite using `[e, integral_const_mul, h.eq, liftInt_smul']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem CtGood.smul {φ : GA D W → ℂ} (a : ℂ) (h : CtGood C ω ω' ν 𝓕 κ 𝓝 f f' g c φ) :
    CtGood C ω ω' ν 𝓕 κ 𝓝 f f' g c (a • φ) := by
  have e : (fun n : NI V C => Lift.liftInt ν 𝓕 (thetaKO ω) f (a • φ) ((n : GA D V) * g)) =
      fun n : NI V C => a * Lift.liftInt ν 𝓕 (thetaKO ω) f φ ((n : GA D V) * g) :=
    funext fun n => liftInt_smul' a φ _
  refine ⟨fun g₁ => ?_, ?_, ?_, ?_⟩
  · refine ((h.integ g₁).const_mul a).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  · refine (h.integ'.const_mul a).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  · rw [e]; exact h.mean.const_mul a
  · rw [e, integral_const_mul, h.eq, liftInt_smul']; ring

end CtGood

/- English proof (translation)
Take `⟨μ, 𝓨, hc⟩` from `GlobalTheory.MixModel.exists_isCovolOne D W.rank r`. Establish `form` using `hct V V' W r C B hs ψ χS χT χT' ω ω' hω hω' μ 𝓨 hc ν 𝓕 hν h𝓕 κ 𝓝 hκ h𝓝`. Establish `h0 : GlobalTheory.Grow.RapidDec W (0 : GA D W → ℂ)` using `⟨fun _ _ _ => rfl, continuous_const, fun N => ⟨0, fun g => by simp⟩⟩`. Establish `hc0 : IsCuspFun W (0 : GA D W → ℂ)` using `fun _ _ _ _ _ _ _ _ => by simp`. Establish `ht` using `(form 0 h0 hc0 f hf g).2.2.1`.

Establish `good : CtGood C ω ω' ν 𝓕 κ 𝓝 f (res V V' W C B μ 𝓨 (ω (g, 1) f)) g (((κ 𝓝).toReal : ℝ) : ℂ) (F v)`. Use `multT_ind θ M J χ _ CtGood.zero (fun _ _ h h' => h.add h') (fun a _ h => h.smul a) (fun φ ha hcu => ?_) F hF v` and prove the remaining obligations. Take `⟨-, -, -, h1, h2, h3, h4⟩` from `form φ (GlobalTheory.Size.rapidDecSm_of_cuspForm hP hθ ha hcu).rapidDec hcu f hf g`. Conclude with `⟨h1, h2, h3, h4⟩`. Rewrite using `[good.eq, hlow _ ht, mul_zero]`.
-/
theorem constTerm_eq_zero (hct : TowerConstTerm D) (hP : GlobalTheory.Published.CuspRapidDecay)
    {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B)
    {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {χS χT χT' : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)}
    (hω : IsWeilDatumO ψ V W χS χT ω) (hω' : IsWeilDatumO ψ V' W χS χT' ω')
    {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν)
    {S : D.what₂.Tau → SPar} (M : DSModel W S) (J : Set (GA D W)) (χ : GA D W → ℂ)
    (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M)
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (hlow : ∀ f', IsThetaFunO ψ V' W f' → Lift.liftInt ν 𝓕 (thetaKO ω') f' (F v) 1 = 0)
    (κ : Measure (NI V C)) (𝓝 : Set (NI V C)) (hκ : κ.IsHaarMeasure) (h𝓝 : IsFundamentalDomain (NIQ V C) 𝓝 κ)
    (g : GA D V) : ∫ n in 𝓝, Lift.liftInt ν 𝓕 (thetaKO ω) f (F v) ((n : GA D V) * g) ∂κ = 0 := by
  obtain ⟨μ, 𝓨, hc⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank r
  have form := hct V V' W r C B hs ψ χS χT χT' ω ω' hω hω' μ 𝓨 hc ν 𝓕 hν h𝓕 κ 𝓝 hκ h𝓝
  have h0 : GlobalTheory.Grow.RapidDec W (0 : GA D W → ℂ) :=
    ⟨fun _ _ _ => rfl, continuous_const, fun N => ⟨0, fun g => by simp⟩⟩
  have hc0 : IsCuspFun W (0 : GA D W → ℂ) := fun _ _ _ _ _ _ _ _ => by simp
  have ht := (form 0 h0 hc0 f hf g).2.2.1
  have good : CtGood C ω ω' ν 𝓕 κ 𝓝 f (res V V' W C B μ 𝓨 (ω (g, 1) f)) g (((κ 𝓝).toReal : ℝ) : ℂ) (F v) := by
    refine multT_ind θ M J χ _ CtGood.zero (fun _ _ h h' => h.add h') (fun a _ h => h.smul a) (fun φ ha hcu => ?_) F hF v
    obtain ⟨-, -, -, h1, h2, h3, h4⟩ := form φ (GlobalTheory.Size.rapidDecSm_of_cuspForm hP hθ ha hcu).rapidDec hcu f hf g
    exact ⟨h1, h2, h3, h4⟩
  rw [good.eq, hlow _ ht, mul_zero]

end GlobalTheory.PairLift.LowCusp

namespace GlobalTheory.PairLift

/- English proof (translation)
Introduce `D X hI hL S S' aS aT hR V W _M M' θ ψ hθ ω hω ν 𝓕 hν h𝓕 F hF v f hf r C hC κ 𝓝 hκ h𝓝 g`. Take `⟨V', B, hs, hsig⟩` from `GlobalTheory.T.exists_lowerWittTower_isotropicSplitEmbedding D V S _M r C hC`. Take `⟨χS, χT, hW, hexp⟩` from `hω`. Take `⟨η, hη⟩` from `GlobalTheory.Mem.EtaTilde.exists_etaTilde D`. Establish `hpar : V.rank % 2 = V'.rank % 2` using `by rw [hs.rank]; omega`.

Take `⟨ω', hω'⟩` from `GlobalTheory.T.exists_weilDatum_of_splittingCharacters D ψ hW.std V' W χS χT ⟨η, hη.1, hη.2.2.2, hη.2.2.1, hη.2.1⟩ hW.hecS hW.hecT (resEta_parity hW.resS hpar) hW.resT`. Use `LowCusp.constTerm_eq_zero hI.const hI.decay hs hθ hW hω' hν h𝓕 M' ∅ 1 F hF v hf (fun f' hf' => ?_) κ 𝓝 hκ h𝓝 g` and prove the remaining obligations. Conclude with `congrFun (hL S S' aS aT hR r V' W M' θ ψ hθ hC.1 hsig ω' ⟨χS, χT, hω', hexp⟩ ν 𝓕 hν h𝓕 F hF v f' hf') 1`.
-/
theorem cuspAll_of_lowAll : ∀ (D : D7) (X : ProvA), Inputs D X → LowAll D X → CuspAll D X := by
  intro D X hI hL S S' aS aT hR V W _M M' θ ψ hθ ω hω ν 𝓕 hν h𝓕 F hF v f hf r C hC κ 𝓝 hκ h𝓝 g
  obtain ⟨V', B, hs, hsig⟩ := GlobalTheory.T.exists_lowerWittTower_isotropicSplitEmbedding D V S _M r C hC
  obtain ⟨χS, χT, hW, hexp⟩ := hω
  obtain ⟨η, hη⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  have hpar : V.rank % 2 = V'.rank % 2 := by rw [hs.rank]; omega
  obtain ⟨ω', hω'⟩ := GlobalTheory.T.exists_weilDatum_of_splittingCharacters D ψ hW.std V' W χS χT ⟨η, hη.1, hη.2.2.2, hη.2.2.1, hη.2.1⟩ hW.hecS hW.hecT
    (resEta_parity hW.resS hpar) hW.resT
  refine LowCusp.constTerm_eq_zero hI.const hI.decay hs hθ hW hω' hν h𝓕 M' ∅ 1 F hF v hf
    (fun f' hf' => ?_) κ 𝓝 hκ h𝓝 g
  exact congrFun (hL S S' aS aT hR r V' W M' θ ψ hθ hC.1 hsig ω' ⟨χS, χT, hω', hexp⟩ ν 𝓕 hν h𝓕 F hF v f' hf') 1

end GlobalTheory.PairLift

end
