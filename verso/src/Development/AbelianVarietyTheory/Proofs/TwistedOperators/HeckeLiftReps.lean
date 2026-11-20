import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsGeneratorRatioEqOneOfUnitFrameMove
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyLiftsToLatticeMapScalingForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeThetaValueIdentityUnitFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeThetaTraceValuesAtComplexPoints
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSimilitudeTriangularPeriodsOfHeckePoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfFlagOfHermFormPreserving
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeLiftEqSmul
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
noncomputable section

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeLiftReps

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.MoveValues GlobalTheory.HeckeValues

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Substitute `hu hu'` using the available equality. Establish `hCk : ψp.ker = C` using `hk.2.2.2.2.2.1`. Take `⟨gam, h, hg1, hg2, -, hex⟩` from `GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog E H Dw l Xo _ g _ F i₁ i₂ Pm Pm' p C ψ ψp hP hP' hp hC2 hk`. Establish `eadd` using `F.ex_add i₁ Pm hP`. Establish `eadd'` using `F.ex_add i₂ Pm' hP'`.

Establish `eker` using `F.ex_ker i₁ Pm hP`. Establish `eker'` using `F.ex_ker i₂ Pm' hP'`. Establish `hspan : Submodule.span ℝ (Pm.range : Set (Fin g → ℂ)) = ⊤`. Rewrite using `[AddMonoidHom.coe_range]`. Conclude with `hP.2.2.2.1`.

Establish `hsmul : ∀ (d : ℂ) z w, hermForm (d • Hm) z w = d * hermForm Hm z w` using `fun d z w => by`. Simplify using `only [hermForm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]`. Take `⟨M, hM⟩ : ∃ M : Matrix (Fin g) (Fin g) ℂ, ∀ z, M *ᵥ z = h z` from `⟨LinearMap.toMatrix' h.toLinearMap, fun z => by rw [LinearMap.toMatrix'_mulVec]; rfl⟩`. Establish `hpR : ((p : ℂ) ^ 2) = (((p : ℝ) ^ 2 : ℝ) : ℂ)` using `by push_cast; ring`. Establish `hHH : ∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w`.

Establish `key` using `GlobalTheory.UnitFrameGen.hermForm_eq_of_im _ hspan (((p : ℂ) ^ 2) • Hm) Hm' M (by`. Introduce and unpack `_ ⟨a, rfl⟩ _ ⟨a', rfl⟩`. Rewrite using `[hM, hM, ← hg2, ← hg2, him', hg1, hsmul, hpR, Complex.im_ofReal_mul, him]`. Use `push_cast`. Use the proof step `ring)`.

Introduce `z w`. Rewrite using `[← hM, ← hM, key, hsmul]`. Establish `hpow : ∀ (m : ℕ) w, F.ex i₁ Pm (m • w) = F.ex i₁ Pm w ^ m` using `fun m w => by`. Proceed by induction on `m with`. Consider the case `zero => rw [zero_smul, pow_zero]`.

Conclude with `(eker 0).2 ⟨0, map_zero Pm⟩`. Consider the case `succ m ih => rw [succ_nsmul, eadd, ih, pow_succ]`. Establish `hL : ∀ a ∈ Pm.range, h a ∈ Pm'.range`. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `⟨gam a, hg2 a⟩`.

Establish `hhol` using `GlobalTheory.ClassUniq.isHolTo_ex F i₁ Pm hP`. Establish `hhol'` using `GlobalTheory.ClassUniq.isHolTo_ex F i₂ Pm' hP'`. Establish `hfr` using `GlobalTheory.T.heckeIsogeny_appellHumbertFrame_pull_eq_transition_mul E H Dw l Xo (F.u i₁ Pm) (F.u i₂ Pm') p ψp b g Pm.range Pm'.range (F.ex i₁ Pm) (F.ex i₂ Pm') h hspan hhol hhol' eadd (fun a ha => (eker a).2 ha) hex hL hb0 hbt hbr (hbh g _ hhol) Hm χl fr hH hd hn hc h0 (by rint …`. Use `choose wm hwm using fun m => F.ex_onto i₁ Pm hP (cr m)`. Establish `hwmΛ : ∀ m, ∃ b', h (wm m) = Pm' b'` using `fun m => by`.

Establish `e1 : F.ex i₂ Pm' (h (wm m)) = 1`. Rewrite using `[hex, hwm, ← MonoidHom.mem_ker, hCk]`. Conclude with `hr.1 m`. Take `⟨b', hb'⟩` from `(eker' _).1 e1`. Conclude with `⟨b', hb'.symm⟩`.

Establish `hder : ∀ (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ pullback Xo.univ.t.G.hom (F.u i₁ Pm)), v ≫ pullback.snd _ _ = spMap (algebraMap ℂ (DualNumber ℂ)) → IsDerivAt0 (fun z => (F.ex i₁ Pm z).left) w (v ≫ pullback.fst _ _) → IsDerivAt0 (fun z => (F.ex i₂ Pm' z).left) (h w) (v ≫ ψ ≫ pul …`. Introduce `w v hvs hdv`. Establish `hfst : ∀ z, fibPt Xo.univ.t.G (F.ex i₁ Pm z) ≫ pullback.fst _ _ = (F.ex i₁ Pm z).left` using `fun z => pullback.lift_fst _ _ _`. Establish `d0 : IsDerivAt0 (fun z => fibPt Xo.univ.t.G (F.ex i₁ Pm z)) w v`. Use `FibreDeriv.isDerivAt0_of_isPullback (IsPullback.of_hasPullback Xo.univ.t.G.hom (F.u i₁ Pm)) (fun z => pullback.lift_snd _ _ _) ?_ hvs ?_` and prove the remaining obligations.

Use `ExpChain.isHolTo_ex F i₁ Pm hP using 2 with z` and compare the differences between its conclusion and the goal. Conclude with `hfst z`. Use `hdv using 2 with z` and compare the differences between its conclusion and the goal. Conclude with `hfst z`. Establish `d1` using `FibreDeriv.isDerivAt0_comp d0 (ψ ≫ pullback.fst _ _)`.

Establish `e1 : ∀ z, fibPt Xo.univ.t.G (F.ex i₁ Pm z) ≫ ψ ≫ pullback.fst _ _ = (F.ex i₂ Pm' (h z)).left` using `fun z => by`. Rewrite using `[← Category.assoc, hk.2.2.1, hex]`. Conclude with `pullback.lift_fst _ _ _`. Simplify using `only [e1] at d1`. Conclude with `(ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F i₂ Pm' hP') h.toLinearMap w _).1 d1`.

Establish `hinj : ∀ m m' a, (p : ℂ) • wm m - (p : ℂ) • wm m' = Pm a → m = m'`. Introduce `m m' a hma`. Establish `e1 : cr m * (cr m')⁻¹ = F.ex i₁ Pm (wm m - wm m')`. Rewrite using `[mul_inv_eq_iff_eq_mul, ← hwm, ← hwm, ← eadd, sub_add_cancel]`. Establish `e2 : (cr m * (cr m')⁻¹) ^ p = 1`.

Rewrite using `[e1, ← hpow, ← Nat.cast_smul_eq_nsmul ℂ, smul_sub, hma]`. Conclude with `(eker _).2 ⟨a, rfl⟩`. Conclude with `(hr.2 (cr m) (hr.1 m)).unique (by rw [mul_inv_cancel, one_pow]) e2`. Use `⟨h, wm, fun a => ⟨gam a, (hg2 a).symm⟩, hHH, hwmΛ, hinj, fun w => ?_, hder⟩` and prove the remaining obligations. Take `⟨j, hj⟩` from `GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (F.ex i₂ Pm' (h w)).left`.

Use `⟨j, hj, ?_⟩` and prove the remaining obligations. Establish `hjz : ⊤ ≤ (ψp (F.ex i₁ Pm w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j` using `by rw [← hex]; exact hj`. Use `choose jm hjm using fun m => GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB ((cr m * F.ex i₁ Pm w) ^ p).left`. Establish `hsum` using `hbv (F.ex i₁ Pm w) j jm hjz hjm`. Establish `e1` using `congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 (Over.mk (F.u i₂ Pm'))) (ψp (F.ex i₁ Pm w)))`.

Establish `e2` using `congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 (Over.mk (F.u i₂ Pm'))) (ψp (F.ex i₁ Pm w)))`. Rewrite `hsum`, `e1`, `e2` using `[← hex]`. Rewrite `hsum` using `[hv' j (h w) _ e1 e2 hj]`. Rewrite using `[_root_.mul_assoc, hsum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Establish `hq : cr m * F.ex i₁ Pm w = F.ex i₁ Pm (w + wm m)` using `by rw [← hwm, ← eadd, add_comm]`. Establish `hpw : F.ex i₁ Pm (w + wm m) ^ p = F.ex i₁ Pm ((p : ℂ) • (w + wm m))`. Rewrite using `[Nat.cast_smul_eq_nsmul, hpow]`. Establish `hjm'` using `hjm m`. Rewrite `hjm'`, the goal using `[hq, hpw]`.

Establish `f1` using `congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 (Over.mk (F.u i₁ Pm))) (F.ex i₁ Pm ((p : ℂ) • (w + wm m))))`. Establish `f2` using `congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 (Over.mk (F.u i₁ Pm))) (F.ex i₁ Pm ((p : ℂ) • (w + wm m))))`. Rewrite using `[hv (jm m) _ _ f1 f2 hjm']`. Take `⟨b', hb'⟩` from `hwmΛ m`. Establish `hjw : ⊤ ≤ (F.ex i₂ Pm' (h (w + wm m))).left ⁻¹ᵁ Xo.univ.t.PP.L.U j`.

Rewrite using `[map_add, eadd', hb', (eker' _).2 ⟨b', rfl⟩, _root_.mul_one]`. Conclude with `hj`. Establish `hf` using `hfr (w + wm m) j (jm m) hjw hjm'`. Rewrite `hf` using `[map_add]`. Rewrite using `[hf]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem core_reps (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (P : Ideal (𝓞 E)) (p i : ℕ)
    (yx zx : Sp ℂ ⟶ Xo.X) (ys : LB.Sec (PPx yx)) (zs : LB.Sec (PPx zx)) (C : Subgroup (Over.mk yx ⟶ Xo.univ.t.G))
    (ψ : pullback Xo.univ.t.G.hom yx ⟶ pullback Xo.univ.t.G.hom zx)
    (ψp : (Over.mk yx ⟶ Xo.univ.t.G) →* (Over.mk zx ⟶ Xo.univ.t.G))
    (cr : Fin (Ideal.absNorm P ^ i) → (Over.mk yx ⟶ Xo.univ.t.G))
    (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk yx ⟶ Xo.univ.t.G) → ℂ) (t0 : ℂ)
    (hp : p.Prime) (hC2 : ∀ a ∈ C, a ^ p ^ 2 = 1) (hk : IsHkIsog p yx zx C ψ ψp)
    (hr : GlobalTheory.ThetaTrace.IsRepsModTors C p cr)
    (hb0 : ∀ i j (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0)
    (hbt : ∀ i j i' j' (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
      ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
        valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a)
    (hbr : ∀ i j, ⊤ ≤ (1 : Over.mk zx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      ⊤ ≤ (1 : Over.mk yx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
        b i j 1 * valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val)
    (hbh : ∀ (g : ℕ) (e : (Fin g → ℂ) → (Over.mk yx ⟶ Xo.univ.t.G)), IsHolTo Set.univ (fun w => (e w).left) →
      ∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
        {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
    (hbv : ∀ (a : Over.mk yx ⟶ Xo.univ.t.G) q (jm : Fin (Ideal.absNorm P ^ i) → Xo.univ.t.PP.L.ι), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U q →
      (∀ m, ⊤ ≤ ((cr m * a) ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U (jm m)) →
      valAt' (lift (𝟙 (Over.mk zx)) (ψp a)).left ((PPx zx).U (fun _ => q)) (zs.f (fun _ => q)) =
        ∑ m, b q (jm m) (cr m * a) *
          valAt' (lift (𝟙 (Over.mk yx)) ((cr m * a) ^ p)).left ((PPx yx).U (fun _ => jm m)) (ys.f (fun _ => jm m)))
    (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
    (i₁ i₂ : Fin F.n) (Pm : (F.Di i₁).La →+ (Fin g → ℂ)) (Pm' : (F.Di i₂).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i₁) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm)
    (hP' : IsPeriod (F.Di i₂) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm')
    (hu : yx = F.u i₁ Pm) (hu' : zx = F.u i₂ Pm')
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ : (Fin g → ℂ) → ℂ)
    (hH : Hm.IsHermitian)
    (him : ∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di i₁).EF a b)
    (hd : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex i₁ Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
    (hn : ∀ j z, ⊤ ≤ (F.ex i₁ Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0)
    (hc : ∀ j j' z, ⊤ ≤ (F.ex i₁ Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (F.ex i₁ Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr j' z)
    (h0 : ∀ j, ⊤ ≤ (F.ex i₁ Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val)
    (ha : ∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex i₁ Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
        Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a)))
    (hv : ∀ j z (pt : Sp ℂ ⟶ Gx yx),
      pt ≫ Formalism.L2.PjFree.gxFst yx = (F.ex i₁ Pm z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd yx = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex i₁ Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx yx).U (fun _ => j)) (ys.f (fun _ => j)) = θ z * fr j z)
    (Hm' : Matrix (Fin g) (Fin g) ℂ) (χl' : (Fin g → ℂ) → ℂ) (fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ' : (Fin g → ℂ) → ℂ)
    (him' : ∀ a b, (hermForm Hm' (Pm' a) (Pm' b)).im = (F.Di i₂).EF a b)
    (hd' : ∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (F.ex i₂ Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
    (hc' : ∀ j j' z, ⊤ ≤ (F.ex i₂ Pm' z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr' j z = valAt' (F.ex i₂ Pm' z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr' j' z)
    (h0' : ∀ j, ⊤ ≤ (F.ex i₂ Pm' 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j 0 = valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val)
    (ha' : ∀ a j z, ‖χl' (Pm' a)‖ = 1 ∧ (⊤ ≤ (F.ex i₂ Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j z = χl' (Pm' a) * Complex.exp (Real.pi * hermForm Hm' z (Pm' a) +
        Real.pi / 2 * hermForm Hm' (Pm' a) (Pm' a)) * fr' j (z + Pm' a)))
    (hv' : ∀ j z (pt : Sp ℂ ⟶ Gx zx),
      pt ≫ Formalism.L2.PjFree.gxFst zx = (F.ex i₂ Pm' z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd zx = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex i₂ Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx zx).U (fun _ => j)) (zs.f (fun _ => j)) = t0 * (θ' z * fr' j z)) :
    ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (wm : Fin (Ideal.absNorm P ^ i) → (Fin g → ℂ)),
      (∀ a, ∃ b, h (Pm a) = Pm' b) ∧ (∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w) ∧
      (∀ m, ∃ b, h (wm m) = Pm' b) ∧ (∀ m m' a, (p : ℂ) • wm m - (p : ℂ) • wm m' = Pm a → m = m') ∧
      (∀ w, ∃ j, ⊤ ≤ (F.ex i₂ Pm' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j ∧
        t0 * θ' (h w) * fr' j (h w) = ∑ m, θ ((p : ℂ) • (w + wm m)) * fr' j (h w + h (wm m))) ∧
      ∀ (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ pullback Xo.univ.t.G.hom yx),
        v ≫ pullback.snd _ _ = spMap (algebraMap ℂ (DualNumber ℂ)) →
        IsDerivAt0 (fun z => (F.ex i₁ Pm z).left) w (v ≫ pullback.fst _ _) →
        IsDerivAt0 (fun z => (F.ex i₂ Pm' z).left) (h w) (v ≫ ψ ≫ pullback.fst _ _) := by
  subst hu hu'
  have hCk : ψp.ker = C := hk.2.2.2.2.2.1
  obtain ⟨gam, h, hg1, hg2, -, hex⟩ := GlobalTheory.HeckeLift.exists_linearMap_of_isHkIsog E H Dw l Xo _ g _ F i₁ i₂ Pm Pm' p C
    ψ ψp hP hP' hp hC2 hk
  have eadd := F.ex_add i₁ Pm hP
  have eadd' := F.ex_add i₂ Pm' hP'
  have eker := F.ex_ker i₁ Pm hP
  have eker' := F.ex_ker i₂ Pm' hP'
  have hspan : Submodule.span ℝ (Pm.range : Set (Fin g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hP.2.2.2.1
  have hsmul : ∀ (d : ℂ) z w, hermForm (d • Hm) z w = d * hermForm Hm z w := fun d z w => by
    simp only [hermForm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin g) (Fin g) ℂ, ∀ z, M *ᵥ z = h z :=
    ⟨LinearMap.toMatrix' h.toLinearMap, fun z => by rw [LinearMap.toMatrix'_mulVec]; rfl⟩
  have hpR : ((p : ℂ) ^ 2) = (((p : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hHH : ∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w := by
    have key := GlobalTheory.UnitFrameGen.hermForm_eq_of_im _ hspan (((p : ℂ) ^ 2) • Hm) Hm' M (by
      rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
      rw [hM, hM, ← hg2, ← hg2, him', hg1, hsmul, hpR, Complex.im_ofReal_mul, him]
      push_cast; ring)
    intro z w
    rw [← hM, ← hM, key, hsmul]
  have hpow : ∀ (m : ℕ) w, F.ex i₁ Pm (m • w) = F.ex i₁ Pm w ^ m := fun m w => by
    induction m with
    | zero => rw [zero_smul, pow_zero]; exact (eker 0).2 ⟨0, map_zero Pm⟩
    | succ m ih => rw [succ_nsmul, eadd, ih, pow_succ]
  have hL : ∀ a ∈ Pm.range, h a ∈ Pm'.range := by
    rintro _ ⟨a, rfl⟩; exact ⟨gam a, hg2 a⟩
  have hhol := GlobalTheory.ClassUniq.isHolTo_ex F i₁ Pm hP
  have hhol' := GlobalTheory.ClassUniq.isHolTo_ex F i₂ Pm' hP'
  have hfr := GlobalTheory.T.heckeIsogeny_appellHumbertFrame_pull_eq_transition_mul E H Dw l Xo (F.u i₁ Pm) (F.u i₂ Pm') p ψp b g Pm.range Pm'.range (F.ex i₁ Pm)
    (F.ex i₂ Pm') h hspan hhol hhol' eadd (fun a ha => (eker a).2 ha) hex hL hb0 hbt hbr (hbh g _ hhol) Hm χl fr hH
    hd hn hc h0 (by rintro _ ⟨a, rfl⟩ j z; exact ha a j z) Hm' χl' fr' hHH hd' hc' h0'
    (by rintro _ ⟨a, rfl⟩ j z; exact ha' a j z)
  choose wm hwm using fun m => F.ex_onto i₁ Pm hP (cr m)
  have hwmΛ : ∀ m, ∃ b', h (wm m) = Pm' b' := fun m => by
    have e1 : F.ex i₂ Pm' (h (wm m)) = 1 := by
      rw [hex, hwm, ← MonoidHom.mem_ker, hCk]; exact hr.1 m
    obtain ⟨b', hb'⟩ := (eker' _).1 e1
    exact ⟨b', hb'.symm⟩
  have hder : ∀ (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ pullback Xo.univ.t.G.hom (F.u i₁ Pm)),
      v ≫ pullback.snd _ _ = spMap (algebraMap ℂ (DualNumber ℂ)) →
      IsDerivAt0 (fun z => (F.ex i₁ Pm z).left) w (v ≫ pullback.fst _ _) →
      IsDerivAt0 (fun z => (F.ex i₂ Pm' z).left) (h w) (v ≫ ψ ≫ pullback.fst _ _) := by
    intro w v hvs hdv
    have hfst : ∀ z, fibPt Xo.univ.t.G (F.ex i₁ Pm z) ≫ pullback.fst _ _ = (F.ex i₁ Pm z).left := fun z =>
      pullback.lift_fst _ _ _
    have d0 : IsDerivAt0 (fun z => fibPt Xo.univ.t.G (F.ex i₁ Pm z)) w v := by
      refine FibreDeriv.isDerivAt0_of_isPullback (IsPullback.of_hasPullback Xo.univ.t.G.hom (F.u i₁ Pm))
        (fun z => pullback.lift_snd _ _ _) ?_ hvs ?_
      · convert ExpChain.isHolTo_ex F i₁ Pm hP using 2 with z
        exact hfst z
      · convert hdv using 2 with z
        exact hfst z
    have d1 := FibreDeriv.isDerivAt0_comp d0 (ψ ≫ pullback.fst _ _)
    have e1 : ∀ z, fibPt Xo.univ.t.G (F.ex i₁ Pm z) ≫ ψ ≫ pullback.fst _ _ = (F.ex i₂ Pm' (h z)).left := fun z => by
      rw [← Category.assoc, hk.2.2.1, hex]
      exact pullback.lift_fst _ _ _
    simp only [e1] at d1
    exact (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F i₂ Pm' hP') h.toLinearMap w _).1 d1
  have hinj : ∀ m m' a, (p : ℂ) • wm m - (p : ℂ) • wm m' = Pm a → m = m' := by
    intro m m' a hma
    have e1 : cr m * (cr m')⁻¹ = F.ex i₁ Pm (wm m - wm m') := by
      rw [mul_inv_eq_iff_eq_mul, ← hwm, ← hwm, ← eadd, sub_add_cancel]
    have e2 : (cr m * (cr m')⁻¹) ^ p = 1 := by
      rw [e1, ← hpow, ← Nat.cast_smul_eq_nsmul ℂ, smul_sub, hma]
      exact (eker _).2 ⟨a, rfl⟩
    exact (hr.2 (cr m) (hr.1 m)).unique (by rw [mul_inv_cancel, one_pow]) e2
  refine ⟨h, wm, fun a => ⟨gam a, (hg2 a).symm⟩, hHH, hwmΛ, hinj, fun w => ?_, hder⟩
  obtain ⟨j, hj⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (F.ex i₂ Pm' (h w)).left
  refine ⟨j, hj, ?_⟩
  have hjz : ⊤ ≤ (ψp (F.ex i₁ Pm w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by rw [← hex]; exact hj
  choose jm hjm using fun m => GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB ((cr m * F.ex i₁ Pm w) ^ p).left
  have hsum := hbv (F.ex i₁ Pm w) j jm hjz hjm
  have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 (Over.mk (F.u i₂ Pm'))) (ψp (F.ex i₁ Pm w)))
  have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 (Over.mk (F.u i₂ Pm'))) (ψp (F.ex i₁ Pm w)))
  rw [← hex] at hsum e1 e2
  rw [hv' j (h w) _ e1 e2 hj] at hsum
  rw [_root_.mul_assoc, hsum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hq : cr m * F.ex i₁ Pm w = F.ex i₁ Pm (w + wm m) := by rw [← hwm, ← eadd, add_comm]
  have hpw : F.ex i₁ Pm (w + wm m) ^ p = F.ex i₁ Pm ((p : ℂ) • (w + wm m)) := by
    rw [Nat.cast_smul_eq_nsmul, hpow]
  have hjm' := hjm m
  rw [hq, hpw] at hjm' ⊢
  have f1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 (Over.mk (F.u i₁ Pm))) (F.ex i₁ Pm ((p : ℂ) • (w + wm m))))
  have f2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 (Over.mk (F.u i₁ Pm))) (F.ex i₁ Pm ((p : ℂ) • (w + wm m))))
  rw [hv (jm m) _ _ f1 f2 hjm']
  obtain ⟨b', hb'⟩ := hwmΛ m
  have hjw : ⊤ ≤ (F.ex i₂ Pm' (h (w + wm m))).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
    rw [map_add, eadd', hb', (eker' _).2 ⟨b', rfl⟩, _root_.mul_one]; exact hj
  have hf := hfr (w + wm m) j (jm m) hjw hjm'
  rw [map_add] at hf
  rw [hf]; ring

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ r U _ _ P p i k k' x x' C z t hA hK hz hb ht1 g e F ik Pm Pm' hP hP' hu hu' hdu hdu' Hm χl fr θ hH hpos him hd hn hc h0 ha hv Hm' χl' fr' θ' hHm' _ _ him' hd' _ hc' h0' ha' hv'`. Take `⟨ψ, ψp, n, cr, b, hk, hL, hr, hb0, hbt, hbr, hbh, hbv⟩` from `GlobalTheory.HeckeLiftScalar.hkPtC_values_lie E H Dw l Xo c σ p (U.un k x) z C hz`. Establish `hcard : n = Ideal.absNorm P ^ i`. Use `letI := fieldCAt σ`. Use `haveI := algClosedCAt σ`.

Conclude with `GlobalTheory.ThetaTrace.card_reps hA.2.2.1.pos hK hr`. Substitute `hcard` using the available equality. Take `⟨hzx, hcfB, hbc⟩` from `hb`. Establish `hS : Out.SecTwistSt` using `GlobalTheory.abelianSchemeLaws_all.2.secTwist`. Establish `hid : spMap (RingHom.id ℂ) = 𝟙 _` using `by simp [spMap]`.

Establish `hbc' : GlobalTheory.Frames.SecBC (RingHom.id ℂ) (Formalism.L2.PjFree.toC (t none : CAt σ)) (U.un k' x').x z.x (U.un k' x').s z.s`. Take `⟨pm, p1, p2, p3⟩` from `hbc`. Conclude with `⟨pm, p1, by rw [hid]; exact p2.trans (Category.comp_id _).symm, p3⟩`. Establish `hv'' : ∀ j w (pt : Sp ℂ ⟶ Gx z.x), pt ≫ Formalism.L2.PjFree.gxFst z.x = (F.ex (ik k') Pm' w).left → pt ≫ Formalism.L2.PjFree.gxSnd z.x = 𝟙 (Sp ℂ) → ⊤ ≤ (F.ex (ik k') Pm' w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → valAt' pt ((PPx z.x).U (fun _ => j)) (z.s.f (fun _ => j)) = Formalism.L2.PjFr …`. Introduce `j w pt e1 e2 hj`.

Establish `hw0' : (F.ex (ik k') Pm' w).left ≫ Xo.univ.t.G.hom = ((U.un k' x').x : Sp ℂ ⟶ Xo.X)` using `(Over.w (F.ex (ik k') Pm' w)).trans hu'.symm`. Conclude with `GlobalTheory.ThetaPtChg.val_of_secBC hS (Xo := Xo) _ _ hzx _ _ _ hbc' (Over.homMk (F.ex (ik k') Pm' w).left hw0') j _ _ (fun pt' h1 h2 => hv' j w pt' h1 h2 hj) (fun pt' h1 h2 => by`. Take `rfl : pt' = pt` from `Limits.pullback.hom_ext (h2.trans e2.symm) (h1.trans e1.symm)`. Use the proof step `rfl)`. Take `⟨h, wm, hPm, hHH, hwmΛ, hinj, hval, hder⟩` from `core_reps E H Dw l Xo c σ P p i (U.un k x).x z.x (U.un k x).s z.s C ψ ψp cr b _ hA.2.2.1 (fun a ha => GlobalTheory.HkPts.pow_eq_one hA.2.2.2.1 hK ha) hk hr hb0 hbt hbr hbh hbv g e F (ik k) (ik k') Pm Pm' hP hP' hu (hzx.trans hu') Hm χl fr θ hH him hd hn hc h0 ha hv Hm' χl' fr' θ' …`.

Establish `hp0 : (p : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hA.2.2.1.ne_zero`. Use `choose cf hcf1 hcf2 hcf3 using hcfB`. Establish `hcol : ∀ τ m, h (Pi.single (e.symm ⟨τ, m⟩) 1) = ∑ j, ((p : ℂ) * Formalism.L2.PjFree.toC (cf τ m j)) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)`. Introduce `τ m`. Take `⟨wv, hw1, hw2, hw3⟩` from `hL τ m`.

Establish `d2` using `hder (Pi.single (e.symm ⟨τ, m⟩) 1) wv hw2 (by have q := hdu τ m; rw [← hw1] at q; exact q)`. Establish `d1` using `(GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ Pm' hP' _ ((U.un k' x').u τ) _ (hdu' τ) (cf τ m) (z.u τ m)).1 (hu' ▸ hcf3 τ m)`. Establish `d3` using `ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_smul d1 (p : ℂ)`. Establish `e1 : spMap (epsMul (1 : ℂ)) = 𝟙 _`. Establish `e0 : epsMul (1 : ℂ) = RingHom.id _`.

Apply `RingHom.ext` to reduce the goal to its premises. Introduce `a`. Apply the tactic sequence `ext <;> simp [epsMul]`. Rewrite using `[e0]`. Apply the tactic sequence `first | rfl | exact Spec.map_id _ | simp [spMap] | (rw [CommRingCat.ofHom_id]; exact Spec.map_id _)`.

Establish `e3 : spMap (epsMul (p : ℂ)) ≫ z.u τ m = wv ≫ ψ ≫ pullback.fst _ _`. Rewrite using `[hw3]`. Use `(spMap_epsMul_comp (p : ℂ) ((p : ℂ)⁻¹) _).trans ?_` and prove the remaining obligations. Rewrite using `[inv_mul_cancel₀ hp0, e1]`. Conclude with `Category.id_comp _`.

Rewrite `d3` using `[e3]`. Establish `tn` using `GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ Pm' hP'`. Rewrite using `[(tn.2.2 _ (tn.1 _ _ d2)).unique d2 d3, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Conclude with `(smul_smul (p : ℂ) (Formalism.L2.PjFree.toC (cf τ m j)) (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ))`.

Establish `hflag : h = LinearEquiv.smulOfNeZero ℂ (Fin g → ℂ) (p : ℂ) hp0`. Use `GlobalTheory.FlagEq.eq_of_flag_of_hermForm e Hm hpos h _ ?_ (fun τ j => Pi.single (e.symm ⟨τ, j⟩) 1) (p : ℂ) hp0 ?_ ?_` and prove the remaining obligations. Introduce `u w`. Substitute `hHm'` using the available equality. Rewrite using `[hHH]`.

Simplify using `only [LinearEquiv.smulOfNeZero_apply, hermForm, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]`. Establish `hs : star (p : ℂ) = p` using `by simp`. Rewrite using `[hs]`. Expand and normalize the polynomial expressions, which then agree. Introduce `τ m`.

Rewrite using `[hcol]`. Establish `hdiag : Formalism.L2.PjFree.toC (cf τ m m) = 1`. Rewrite using `[hcf1, ht1 _ (by simp)]`. Both sides reduce to the same expression. Establish `key : ∀ j : Fin (Dw.mult τ), ((p : ℂ) * Formalism.L2.PjFree.toC (cf τ m j)) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ) = (if j < m then ((p : ℂ) * Formalism.L2.PjFree.toC (cf τ m j)) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ) else 0) + (if j = m then (p : ℂ) • (Pi.single (e.sym …`.

Introduce `j`. Break down `lt_trichotomy j m with hj | rfl | hj` into its components or cases. Simplify using `[hj, hj.ne]`. Simplify using `[hdiag]`. Establish `h0j : cf τ m j = 0` using `hcf2 τ m j hj`.

Establish `: Formalism.L2.PjFree.toC (cf τ m j) = 0` using `by rw [h0j]; rfl`. Simplify using `[this, not_lt.2 hj.le, hj.ne']`. Rewrite using `[Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ m, if_pos (Finset.mem_univ _), add_sub_cancel_right, ← Finset.sum_filter]`. Use `Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, ?_, rfl⟩)` and prove the remaining obligations. Simplify using `using hj`.

Introduce `τ m`. Simplify using the standard rewrite rules. Establish `hh : ∀ v, h v = (p : ℂ) • v` using `fun v => by rw [hflag]; rfl`. Use `⟨wm, fun a => ?_, fun m => ?_, hinj, fun w => ?_⟩` and prove the remaining obligations. Take `⟨b', hb'⟩` from `hPm a`.

Conclude with `⟨b', by rw [← hh]; exact hb'⟩`. Take `⟨b', hb'⟩` from `hwmΛ m`. Conclude with `⟨b', by rw [← hh]; exact hb'⟩`. Take `⟨j, hj1, hj2⟩` from `hval w`. Use `⟨j, by rw [← hh]; exact hj1, ?_⟩` and prove the remaining obligations.

Simplify `hj2` using `only [hh]`.
-/
theorem hecke_lift_reps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U →
  ∀ (P : Ideal (𝓞 E)) (p i : ℕ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (C : Subgroup (Over.mk (U.un k x).x ⟶ Xo.univ.t.G)) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ),
    admitted l P p → Xo.univ.t.HeckeKer (Over.mk (U.un k x).x) Dw P p i C → HkPtC p (U.un k x) C z → FrBor t (U.un k' x') z →
    (∀ j, j ≠ none → t j = 1) →
  ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (Pm : (F.Di (ik k)).La →+ (Fin g → ℂ)) (Pm' : (F.Di (ik k')).La →+ (Fin g → ℂ)),
    IsPeriod (F.Di (ik k)) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm →
    IsPeriod (F.Di (ik k')) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm' →
    (U.un k x).x = F.u (ik k) Pm → (U.un k' x').x = F.u (ik k') Pm' →
    (∀ τ (j : Fin (Dw.mult τ)), IsDerivAt0 (fun w => (F.ex (ik k) Pm w).left) (Pi.single (e.symm ⟨τ, j⟩) 1) ((U.un k x).u τ j)) →
    (∀ τ (j : Fin (Dw.mult τ)), IsDerivAt0 (fun w => (F.ex (ik k') Pm' w).left) (Pi.single (e.symm ⟨τ, j⟩) 1) ((U.un k' x').u τ j)) →
  ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ : (Fin g → ℂ) → ℂ),
    Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di (ik k)).EF a b) →
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (F.ex (ik k) Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr j' z) →
    (∀ j, ⊤ ≤ (F.ex (ik k) Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' (U.un k x).x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
        Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) →
    (∀ j z (pt : Sp ℂ ⟶ Gx (U.un k x).x),
      pt ≫ Formalism.L2.PjFree.gxFst (U.un k x).x = (F.ex (ik k) Pm z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd (U.un k x).x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (U.un k x).x).U (fun _ => j)) ((U.un k x).s.f (fun _ => j)) = θ z * fr j z) →
  ∀ (Hm' : Matrix (Fin g) (Fin g) ℂ) (χl' : (Fin g → ℂ) → ℂ) (fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ' : (Fin g → ℂ) → ℂ),
    Hm' = Hm → Hm'.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re) →
    (∀ a b, (hermForm Hm' (Pm' a) (Pm' b)).im = (F.Di (ik k')).EF a b) →
    (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr' j z = valAt' (F.ex (ik k') Pm' z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr' j' z) →
    (∀ j, ⊤ ≤ (F.ex (ik k') Pm' 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j 0 = valAt' (U.un k' x').x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a j z, ‖χl' (Pm' a)‖ = 1 ∧ (⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j z = χl' (Pm' a) * Complex.exp (Real.pi * hermForm Hm' z (Pm' a) +
        Real.pi / 2 * hermForm Hm' (Pm' a) (Pm' a)) * fr' j (z + Pm' a))) →
    (∀ j z (pt : Sp ℂ ⟶ Gx (U.un k' x').x),
      pt ≫ Formalism.L2.PjFree.gxFst (U.un k' x').x = (F.ex (ik k') Pm' z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd (U.un k' x').x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex (ik k') Pm' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (U.un k' x').x).U (fun _ => j)) ((U.un k' x').s.f (fun _ => j)) = θ' z * fr' j z) →
  ∃ wm : Fin (Ideal.absNorm P ^ i) → (Fin g → ℂ),
    (∀ a, ∃ b, (p : ℂ) • Pm a = Pm' b) ∧ (∀ m, ∃ b, (p : ℂ) • wm m = Pm' b) ∧
    (∀ m m' a, (p : ℂ) • wm m - (p : ℂ) • wm m' = Pm a → m = m') ∧
    ∀ w, ∃ j, ⊤ ≤ (F.ex (ik k') Pm' ((p : ℂ) • w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j ∧
      Formalism.L2.PjFree.toC (t none : CAt σ) * θ' ((p : ℂ) • w) * fr' j ((p : ℂ) • w) =
        ∑ m, θ ((p : ℂ) • (w + wm m)) * fr' j ((p : ℂ) • w + (p : ℂ) • wm m) := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U _ _ P p i k k' x x' C z t hA hK hz hb ht1 g e F ik Pm Pm' hP hP' hu hu' hdu hdu'
    Hm χl fr θ hH hpos him hd hn hc h0 ha hv Hm' χl' fr' θ' hHm' _ _ him' hd' _ hc' h0' ha' hv'
  obtain ⟨ψ, ψp, n, cr, b, hk, hL, hr, hb0, hbt, hbr, hbh, hbv⟩ :=
    GlobalTheory.HeckeLiftScalar.hkPtC_values_lie E H Dw l Xo c σ p (U.un k x) z C hz
  have hcard : n = Ideal.absNorm P ^ i := by
    letI := fieldCAt σ
    haveI := algClosedCAt σ
    exact GlobalTheory.ThetaTrace.card_reps hA.2.2.1.pos hK hr
  subst hcard
  obtain ⟨hzx, hcfB, hbc⟩ := hb
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := by simp [spMap]
  have hbc' : GlobalTheory.Frames.SecBC (RingHom.id ℂ) (Formalism.L2.PjFree.toC (t none : CAt σ)) (U.un k' x').x z.x
      (U.un k' x').s z.s := by
    obtain ⟨pm, p1, p2, p3⟩ := hbc
    exact ⟨pm, p1, by rw [hid]; exact p2.trans (Category.comp_id _).symm, p3⟩
  have hv'' : ∀ j w (pt : Sp ℂ ⟶ Gx z.x), pt ≫ Formalism.L2.PjFree.gxFst z.x = (F.ex (ik k') Pm' w).left →
      pt ≫ Formalism.L2.PjFree.gxSnd z.x = 𝟙 (Sp ℂ) → ⊤ ≤ (F.ex (ik k') Pm' w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx z.x).U (fun _ => j)) (z.s.f (fun _ => j)) =
        Formalism.L2.PjFree.toC (t none : CAt σ) * (θ' w * fr' j w) := by
    intro j w pt e1 e2 hj
    have hw0' : (F.ex (ik k') Pm' w).left ≫ Xo.univ.t.G.hom = ((U.un k' x').x : Sp ℂ ⟶ Xo.X) :=
      (Over.w (F.ex (ik k') Pm' w)).trans hu'.symm
    exact GlobalTheory.ThetaPtChg.val_of_secBC hS (Xo := Xo) _ _ hzx _ _ _ hbc'
      (Over.homMk (F.ex (ik k') Pm' w).left hw0') j _ _
      (fun pt' h1 h2 => hv' j w pt' h1 h2 hj)
      (fun pt' h1 h2 => by
        obtain rfl : pt' = pt := Limits.pullback.hom_ext (h2.trans e2.symm) (h1.trans e1.symm)
        rfl)
  obtain ⟨h, wm, hPm, hHH, hwmΛ, hinj, hval, hder⟩ := core_reps E H Dw l Xo c σ P p i (U.un k x).x z.x (U.un k x).s z.s C ψ ψp
    cr b _ hA.2.2.1 (fun a ha => GlobalTheory.HkPts.pow_eq_one hA.2.2.2.1 hK ha) hk hr hb0 hbt hbr hbh hbv g e F (ik k) (ik k')
    Pm Pm' hP hP' hu (hzx.trans hu') Hm χl fr θ hH him hd hn hc h0 ha hv Hm' χl' fr' θ' him' hd' hc'
    (by rw [hzx]; exact h0') ha' hv''
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hA.2.2.1.ne_zero
  choose cf hcf1 hcf2 hcf3 using hcfB
  have hcol : ∀ τ m, h (Pi.single (e.symm ⟨τ, m⟩) 1) =
      ∑ j, ((p : ℂ) * Formalism.L2.PjFree.toC (cf τ m j)) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ) := by
    intro τ m
    obtain ⟨wv, hw1, hw2, hw3⟩ := hL τ m
    have d2 := hder (Pi.single (e.symm ⟨τ, m⟩) 1) wv hw2 (by have q := hdu τ m; rw [← hw1] at q; exact q)
    have d1 := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ Pm' hP' _ ((U.un k' x').u τ) _ (hdu' τ)
      (cf τ m) (z.u τ m)).1 (hu' ▸ hcf3 τ m)
    have d3 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_smul d1 (p : ℂ)
    have e1 : spMap (epsMul (1 : ℂ)) = 𝟙 _ := by
      have e0 : epsMul (1 : ℂ) = RingHom.id _ := by
        apply RingHom.ext
        intro a
        ext <;> simp [epsMul]
      rw [e0]
      first | rfl | exact Spec.map_id _ | simp [spMap] | (rw [CommRingCat.ofHom_id]; exact Spec.map_id _)
    have e3 : spMap (epsMul (p : ℂ)) ≫ z.u τ m = wv ≫ ψ ≫ pullback.fst _ _ := by
      rw [hw3]
      refine (spMap_epsMul_comp (p : ℂ) ((p : ℂ)⁻¹) _).trans ?_
      rw [inv_mul_cancel₀ hp0, e1]
      exact Category.id_comp _
    rw [e3] at d3
    have tn := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ Pm' hP'
    rw [(tn.2.2 _ (tn.1 _ _ d2)).unique d2 d3, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (smul_smul (p : ℂ) (Formalism.L2.PjFree.toC (cf τ m j)) (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ))
  have hflag : h = LinearEquiv.smulOfNeZero ℂ (Fin g → ℂ) (p : ℂ) hp0 := by
    refine GlobalTheory.FlagEq.eq_of_flag_of_hermForm e Hm hpos h _ ?_ (fun τ j => Pi.single (e.symm ⟨τ, j⟩) 1) (p : ℂ) hp0
      ?_ ?_
    · intro u w
      subst hHm'
      rw [hHH]
      simp only [LinearEquiv.smulOfNeZero_apply, hermForm, Matrix.mulVec_smul, star_smul, smul_dotProduct,
        dotProduct_smul, smul_eq_mul]
      have hs : star (p : ℂ) = p := by simp
      rw [hs]
      ring
    · intro τ m
      rw [hcol]
      have hdiag : Formalism.L2.PjFree.toC (cf τ m m) = 1 := by
        rw [hcf1, ht1 _ (by simp)]
        rfl
      have key : ∀ j : Fin (Dw.mult τ), ((p : ℂ) * Formalism.L2.PjFree.toC (cf τ m j)) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ) =
          (if j < m then ((p : ℂ) * Formalism.L2.PjFree.toC (cf τ m j)) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ) else 0) +
            (if j = m then (p : ℂ) • (Pi.single (e.symm ⟨τ, m⟩) 1 : Fin g → ℂ) else 0) := by
        intro j
        rcases lt_trichotomy j m with hj | rfl | hj
        · simp [hj, hj.ne]
        · simp [hdiag]
        · have h0j : cf τ m j = 0 := hcf2 τ m j hj
          have : Formalism.L2.PjFree.toC (cf τ m j) = 0 := by rw [h0j]; rfl
          simp [this, not_lt.2 hj.le, hj.ne']
      rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ m,
        if_pos (Finset.mem_univ _), add_sub_cancel_right, ← Finset.sum_filter]
      refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, ?_, rfl⟩)
      simpa using hj
    · intro τ m
      simp
  have hh : ∀ v, h v = (p : ℂ) • v := fun v => by rw [hflag]; rfl
  refine ⟨wm, fun a => ?_, fun m => ?_, hinj, fun w => ?_⟩
  · obtain ⟨b', hb'⟩ := hPm a
    exact ⟨b', by rw [← hh]; exact hb'⟩
  · obtain ⟨b', hb'⟩ := hwmΛ m
    exact ⟨b', by rw [← hh]; exact hb'⟩
  · obtain ⟨j, hj1, hj2⟩ := hval w
    refine ⟨j, by rw [← hh]; exact hj1, ?_⟩
    simpa only [hh] using hj2

end GlobalTheory.HeckeLiftReps
