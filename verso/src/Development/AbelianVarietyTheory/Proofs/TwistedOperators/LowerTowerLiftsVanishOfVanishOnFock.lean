import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameExistsSignCompat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace ENNReal NNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift GlobalTheory.Size GlobalTheory.Grow GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift

namespace GlobalTheory.PairLift.LowAllPf

variable {D : D7}

section Kernel

variable {V W : HSp D} (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (g : GA D V) (h : GA D W)

/- English proof (translation)
Simplify using `[thetaKO]`.
-/
theorem kernel_zero : thetaKO ω g h 0 = 0 := by simp [thetaKO]

/- English proof (translation)
Simplify using `[thetaKO, map_add]`.
-/
theorem kernel_add (f f' : WO V W → ℂ) : thetaKO ω g h (f + f') = thetaKO ω g h f + thetaKO ω g h f' := by
  simp [thetaKO, map_add]

/- English proof (translation)
Simplify using `[thetaKO, map_sub]`.
-/
theorem kernel_sub (f f' : WO V W → ℂ) : thetaKO ω g h (f - f') = thetaKO ω g h f - thetaKO ω g h f' := by
  simp [thetaKO, map_sub]

/- English proof (translation)
Simplify using `[thetaKO, map_smul]`.
-/
theorem kernel_smul (c : ℂ) (f : WO V W → ℂ) : thetaKO ω g h (c • f) = c * thetaKO ω g h f := by
  simp [thetaKO, map_smul]

end Kernel

/- English proof (translation)
Take `⟨T, hT, rfl⟩` from `hF`. Establish `hT'` using `(GlobalTheory.MultMem.mem_mult_iff D θ W S M J χ T).1 hT`. Proceed by induction on `v using PiTensorProduct.induction_on with`. Consider the case `smul_tprod c w`. Simplify using `only [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]`.

Conclude with `⟨GlobalTheory.MultMem.isAutFunSm_smul c (hT'.aut w), GlobalTheory.MultMem.isCuspFun_smul c (hT'.cusp w)⟩`. Consider the case `add x y hx hy`. Rewrite using `[map_add]`. Conclude with `⟨GlobalTheory.MultMem.isAutFunSm_add hx.1 hy.1, GlobalTheory.MultMem.isCuspFun_add hx.1.toIsAutFun hy.1.toIsAutFun hx.2 hy.2⟩`.
-/
theorem multT_apply_smooth_cusp {W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S)
    (J : Set (GA D W)) (χ : GA D W → ℂ) (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M) :
    IsAutFunSm θ W (F v) ∧ IsCuspFun W (F v) := by
  obtain ⟨T, hT, rfl⟩ := hF
  have hT' := (GlobalTheory.MultMem.mem_mult_iff D θ W S M J χ T).1 hT
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c w =>
    simp only [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul c (hT'.aut w), GlobalTheory.MultMem.isCuspFun_smul c (hT'.cusp w)⟩
  | add x y hx hy =>
    rw [map_add]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add hx.1 hy.1,
      GlobalTheory.MultMem.isCuspFun_add hx.1.toIsAutFun hy.1.toIsAutFun hx.2 hy.2⟩

/- English proof (translation)
Introduce `g hg`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem g hg => exact hs g hg`. Consider the case `zero`. Use `⟨GlobalTheory.OrientedHeis.theta_zero, funext fun x => ?_⟩` and prove the remaining obligations.

Simplify using `[Lift.liftInt, kernel_zero]`. Consider the case `add a b _ _ ha hb`. Use `⟨GlobalTheory.OrientedHeis.theta_add ha.1 hb.1, funext fun x => ?_⟩` and prove the remaining obligations. Establish `e : Lift.liftInt ν 𝓕 (thetaKO ω) (a + b) Φ x = Lift.liftInt ν 𝓕 (thetaKO ω) a Φ x + Lift.liftInt ν 𝓕 (thetaKO ω) b Φ x`. Simplify using `only [Lift.liftInt, kernel_add, add_mul]`.

Conclude with `integral_add (hI a ha.1 x) (hI b hb.1 x)`. Simplify using `[e, congrFun ha.2 x, congrFun hb.2 x]`. Consider the case `smul c a _ ha`. Use `⟨GlobalTheory.OrientedHeis.theta_smul c ha.1, funext fun x => ?_⟩` and prove the remaining obligations. Establish `e : Lift.liftInt ν 𝓕 (thetaKO ω) (c • a) Φ x = c * Lift.liftInt ν 𝓕 (thetaKO ω) a Φ x`.

Simplify using `only [Lift.liftInt, kernel_smul, mul_assoc]`. Conclude with `integral_const_mul c _`. Simplify using `[e, congrFun ha.2 x]`.
-/
theorem liftInt_span_zero {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {Φ : GA D W → ℂ}
    (hI : ∀ f, IsThetaFunO ψ V W f → ∀ x, IntegrableOn (fun h => thetaKO ω x h f * Φ h) 𝓕 ν)
    {s : Set (WO V W → ℂ)} (hs : ∀ g ∈ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0) :
    ∀ g ∈ Submodule.span ℂ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg => exact hs g hg
  | zero =>
    refine ⟨GlobalTheory.OrientedHeis.theta_zero, funext fun x => ?_⟩
    simp [Lift.liftInt, kernel_zero]
  | add a b _ _ ha hb =>
    refine ⟨GlobalTheory.OrientedHeis.theta_add ha.1 hb.1, funext fun x => ?_⟩
    have e : Lift.liftInt ν 𝓕 (thetaKO ω) (a + b) Φ x =
        Lift.liftInt ν 𝓕 (thetaKO ω) a Φ x + Lift.liftInt ν 𝓕 (thetaKO ω) b Φ x := by
      simp only [Lift.liftInt, kernel_add, add_mul]
      exact integral_add (hI a ha.1 x) (hI b hb.1 x)
    simp [e, congrFun ha.2 x, congrFun hb.2 x]
  | smul c a _ ha =>
    refine ⟨GlobalTheory.OrientedHeis.theta_smul c ha.1, funext fun x => ?_⟩
    have e : Lift.liftInt ν 𝓕 (thetaKO ω) (c • a) Φ x = c * Lift.liftInt ν 𝓕 (thetaKO ω) a Φ x := by
      simp only [Lift.liftInt, kernel_smul, mul_assoc]
      exact integral_const_mul c _
    simp [e, congrFun ha.2 x]

/- English proof (translation)
Use `le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le` and prove the remaining obligations. Rewrite using `[zero_add]`. Break down `eq_or_ne K 0 with hK0 | hK0` into its components or cases. Establish `h1` using `h 1 one_pos`. Rewrite `h1` using `[hK0, zero_mul]`.

Conclude with `h1.trans zero_le`. Use `(h (ε / K) (ENNReal.div_pos (ENNReal.coe_ne_zero.2 hε.ne') hK)).trans (le_of_eq ?_)` and prove the remaining obligations. Conclude with `ENNReal.mul_div_cancel hK0 hK`.
-/
theorem eq_zero_of_le_mul_all {a K : ℝ≥0∞} (hK : K ≠ ∞) (h : ∀ δ : ℝ≥0∞, 0 < δ → a ≤ K * δ) : a = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
  rw [zero_add]
  rcases eq_or_ne K 0 with hK0 | hK0
  · have h1 := h 1 one_pos
    rw [hK0, zero_mul] at h1
    exact h1.trans zero_le
  · refine (h (ε / K) (ENNReal.div_pos (ENNReal.coe_ne_zero.2 hε.ne') hK)).trans (le_of_eq ?_)
    exact ENNReal.mul_div_cancel hK0 hK

/- English proof (translation)
Take `⟨A, hA⟩` from `hL.bound`. Take `⟨d, hd⟩` from `hA 0`. Take `⟨C, hC⟩` from `hd μ 𝓓 hμ h𝓓 U hU`. Establish `hKt : (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ ≠ ∞` using `ENNReal.mul_ne_top ENNReal.coe_ne_top (hL.decay_ne_top Φ hΦ A)`. Use function extensionality and compare the values at `x`.

Establish `hI : ∀ f', IsThetaFunO ψ V W f' → IntegrableOn (fun h => thetaKO ω x h f' * Φ h) 𝓕 ν` using `fun f' hf' => by`. Simplify `hL.integ f' Φ hf' hΦ x 1` using `only [rTr, mul_one]`. Establish `key : ∀ δ : ℝ≥0∞, 0 < δ → ENNReal.ofReal (‖Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x‖ / height V x ^ A) ≤ (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ * δ`. Introduce `δ hδ`. Take `⟨g, hgU, hg0, hlt⟩` from `happ d δ hδ`.

Establish `hfg : f - g ∈ thetaLevel ψ V W U` using `sub_mem hf hgU`. Establish `e : Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x = Lift.liftInt ν 𝓕 (thetaKO ω) (f - g) Φ x`. Establish `e' : Lift.liftInt ν 𝓕 (thetaKO ω) (f - g) Φ x = Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x - Lift.liftInt ν 𝓕 (thetaKO ω) g Φ x`. Simplify using `only [Lift.liftInt, kernel_sub, sub_mul]`. Conclude with `integral_sub (hI f hf.1) (hI g hgU.1)`.

Rewrite using `[e', congrFun hg0 x, Pi.zero_apply, sub_zero]`. Establish `h2 : ENNReal.ofReal (‖Lift.liftInt ν 𝓕 (thetaKO ω) (f - g) Φ x‖ / height V x ^ A) ≤ growthSob θ V 0 A (lift ω ν 𝓕 (f - g) Φ)`. Simplify using `only [growthSob, wordSum_zero, growthSize]`. Conclude with `le_iSup (fun y => ENNReal.ofReal (‖lift ω ν 𝓕 (f - g) Φ y‖ / height V y ^ A)) x`. Rewrite using `[e]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h0` using `eq_zero_of_le_mul_all hKt key`. Rewrite `h0` using `[ENNReal.ofReal_eq_zero]`. Establish `hpos : 0 < height V x ^ A` using `pow_pos (height_pos V x) A`. Establish `h3 : ‖Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x‖ ≤ 0`.

Simplify using `using (div_le_iff₀ hpos).1 h0`. Conclude with `norm_le_zero_iff.1 h3`.
-/
theorem liftInt_zero_of_approx {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
    {cls : (GA D W → ℂ) → Prop} (hL : LiftLaws θ ψ ω ν 𝓕 cls) {Φ : GA D W → ℂ} (hΦ : cls Φ)
    {μ : Measure (WO V W)} {𝓓 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure)
    (h𝓓 : IsAddFundamentalDomain (ratL W V) 𝓓 μ) {U : AddSubgroup (WO V W)} (hU : IsOpen (U : Set (WO V W)))
    {f : WO V W → ℂ} (hf : f ∈ thetaLevel ψ V W U)
    (happ : ∀ (d : ℕ) (δ : ℝ≥0∞), 0 < δ → ∃ g ∈ thetaLevel ψ V W U,
      Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 ∧ sobO ψ θ μ 𝓓 d (f - g) < δ) :
    Lift.liftInt ν 𝓕 (thetaKO ω) f Φ = 0 := by
  obtain ⟨A, hA⟩ := hL.bound
  obtain ⟨d, hd⟩ := hA 0
  obtain ⟨C, hC⟩ := hd μ 𝓓 hμ h𝓓 U hU
  have hKt : (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top (hL.decay_ne_top Φ hΦ A)
  funext x
  have hI : ∀ f', IsThetaFunO ψ V W f' → IntegrableOn (fun h => thetaKO ω x h f' * Φ h) 𝓕 ν := fun f' hf' => by
    simpa only [rTr, mul_one] using hL.integ f' Φ hf' hΦ x 1
  have key : ∀ δ : ℝ≥0∞, 0 < δ → ENNReal.ofReal (‖Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x‖ / height V x ^ A) ≤
      (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ * δ := by
    intro δ hδ
    obtain ⟨g, hgU, hg0, hlt⟩ := happ d δ hδ
    have hfg : f - g ∈ thetaLevel ψ V W U := sub_mem hf hgU
    have e : Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x = Lift.liftInt ν 𝓕 (thetaKO ω) (f - g) Φ x := by
      have e' : Lift.liftInt ν 𝓕 (thetaKO ω) (f - g) Φ x =
          Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x - Lift.liftInt ν 𝓕 (thetaKO ω) g Φ x := by
        simp only [Lift.liftInt, kernel_sub, sub_mul]
        exact integral_sub (hI f hf.1) (hI g hgU.1)
      rw [e', congrFun hg0 x, Pi.zero_apply, sub_zero]
    have h2 : ENNReal.ofReal (‖Lift.liftInt ν 𝓕 (thetaKO ω) (f - g) Φ x‖ / height V x ^ A) ≤
        growthSob θ V 0 A (lift ω ν 𝓕 (f - g) Φ) := by
      simp only [growthSob, wordSum_zero, growthSize]
      exact le_iSup (fun y => ENNReal.ofReal (‖lift ω ν 𝓕 (f - g) Φ y‖ / height V y ^ A)) x
    rw [e]
    calc _ ≤ _ := h2
      _ ≤ C * sobO ψ θ μ 𝓓 d (f - g) * decayInt ν 𝓕 A Φ := hC (f - g) hfg Φ hΦ
      _ = (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ * sobO ψ θ μ 𝓓 d (f - g) := by ring
      _ ≤ (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ * δ := by gcongr
  have h0 := eq_zero_of_le_mul_all hKt key
  rw [ENNReal.ofReal_eq_zero] at h0
  have hpos : 0 < height V x ^ A := pow_pos (height_pos V x) A
  have h3 : ‖Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x‖ ≤ 0 := by
    simpa using (div_le_iff₀ hpos).1 h0
  exact norm_le_zero_iff.1 h3

end GlobalTheory.PairLift.LowAllPf

namespace GlobalTheory.PairLift

/- English proof (translation)
Introduce `D X hIn hLF S S' aS aT hR i V' W M' θ ψ hθ hi hs ω' hω ν 𝓕 hν h𝓕 F hF v f' hf`. Take `⟨χS, χT, hW, -⟩` from `id hω`. Establish `hL` using `hIn.laws V' W θ ψ χS χT ω' hθ hW ν 𝓕 hν h𝓕`. Establish `hFv` using `LowAllPf.multT_apply_smooth_cusp θ M' ∅ 1 F hF v`. Take `⟨A⟩` from `(GlobalTheory.FrameExists.frame_exists_signCompat D V').1`.

Take `⟨μ, 𝓓, hμ⟩` from `GlobalTheory.Size.exists_isCovolOne V' W`. Take `⟨U, hU, hfU, happ⟩` from `hIn.dense V' W A (Fr.ofModel M') θ ψ hW.std hθ μ 𝓓 hμ f' hf`. Establish `hI : ∀ f, IsThetaFunO ψ V' W f → ∀ x, IntegrableOn (fun h => thetaKO ω' x h f * F v h) 𝓕 ν` using `fun f hf x => by simpa only [rTr, mul_one] using hL.integ f (F v) hf hFv x 1`. Establish `hspan` using `LowAllPf.liftInt_span_zero hI (s := {g | ∃ f₀ P, IsVacF ψ θ A (Fr.ofModel M') f₀ ∧ f₀ ∈ thetaLevel ψ V' W U ∧ g = ptF ψ θ A (Fr.ofModel M') f₀ P}) (by`. Introduce and unpack `_ ⟨f₀, P, hv, -, rfl⟩`.

Conclude with `⟨GlobalTheory.Chain.InnerSteps.theta_pureTensorO hW.std hθ _ _ _ _ hv.1 P, hLF S S' aS aT hR i V' W M' θ ψ hθ hi hs ω' hω ν 𝓕 hν h𝓕 F hF v A f₀ hv P⟩)`. Use `LowAllPf.liftInt_zero_of_approx hL hFv hμ.1 hμ.2.1 hU hfU fun d δ hδ => ?_` and prove the remaining obligations. Take `⟨g, hg, hgU, hlt⟩` from `happ d δ hδ`. Conclude with `⟨g, hgU, (hspan g hg).2, hlt⟩`.
-/
theorem lowAll_of_lowFock : ∀ (D : D7) (X : ProvA), Inputs D X → LowFock D X → LowAll D X := by
  intro D X hIn hLF S S' aS aT hR i V' W M' θ ψ hθ hi hs ω' hω ν 𝓕 hν h𝓕 F hF v f' hf
  obtain ⟨χS, χT, hW, -⟩ := id hω
  have hL := hIn.laws V' W θ ψ χS χT ω' hθ hW ν 𝓕 hν h𝓕
  have hFv := LowAllPf.multT_apply_smooth_cusp θ M' ∅ 1 F hF v
  obtain ⟨A⟩ := (GlobalTheory.FrameExists.frame_exists_signCompat D V').1
  obtain ⟨μ, 𝓓, hμ⟩ := GlobalTheory.Size.exists_isCovolOne V' W
  obtain ⟨U, hU, hfU, happ⟩ := hIn.dense V' W A (Fr.ofModel M') θ ψ hW.std hθ μ 𝓓 hμ f' hf
  have hI : ∀ f, IsThetaFunO ψ V' W f → ∀ x, IntegrableOn (fun h => thetaKO ω' x h f * F v h) 𝓕 ν :=
    fun f hf x => by simpa only [rTr, mul_one] using hL.integ f (F v) hf hFv x 1
  have hspan := LowAllPf.liftInt_span_zero hI
    (s := {g | ∃ f₀ P, IsVacF ψ θ A (Fr.ofModel M') f₀ ∧ f₀ ∈ thetaLevel ψ V' W U ∧
      g = ptF ψ θ A (Fr.ofModel M') f₀ P})
    (by
      rintro _ ⟨f₀, P, hv, -, rfl⟩
      exact ⟨GlobalTheory.Chain.InnerSteps.theta_pureTensorO hW.std hθ _ _ _ _ hv.1 P,
        hLF S S' aS aT hR i V' W M' θ ψ hθ hi hs ω' hω ν 𝓕 hν h𝓕 F hF v A f₀ hv P⟩)
  refine LowAllPf.liftInt_zero_of_approx hL hFv hμ.1 hμ.2.1 hU hfU fun d δ hδ => ?_
  obtain ⟨g, hg, hgU, hlt⟩ := happ d δ hδ
  exact ⟨g, hgU, (hspan g hg).2, hlt⟩

end GlobalTheory.PairLift

end
