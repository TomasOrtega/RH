import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommute
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.UU

noncomputable section

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ I D A F _ _ _ N hN lab E E' hE hE'`. Establish `hN1 : 1 ≤ N` using `hN.pos`. Establish `hNF : (N : F) ≠ 0`. Establish `h1 : (N : R) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Establish `h2 : (N : FractionRing R) ≠ 0` using `fun h => h1 (IsFractionRing.injective R (FractionRing R) (by rw [map_natCast, map_zero]; exact h))`.

Introduce `h`. Apply `h2` to reduce the goal to its premises. Apply `(algebraMap (FractionRing R) F).injective` to reduce the goal to its premises. Rewrite using `[map_zero, map_natCast]`. Conclude with `h` after adjusting the coercions.

Set `p : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (FractionRing R))` to `jFK (R := R) F`. Set `mkE : ∀ G : Fam D.toPre F N → SecK A.L (snd (TFK (R` to `R) F) A.A).left N, Eqv D.toPre A F N lab G → (Fam D.toPre F N →ₗ[F] EA A p N) := fun G hG => { toFun := fun s => SecMod.mk _ (G s) map_add' := fun s t => SecMod.ext_coord fun j => hG.add s t (s + t) (fun _ _ => rfl) j map_smul' := fun c s => SecMod.ext_coord fun j => hG.smul c s …`. Establish `hbij : ∀ G hG, Function.Bijective (mkE G hG)` using `fun G hG => hG.bij`. Set `e` to `LinearEquiv.ofBijective (mkE E hE) (hbij E hE)`. Set `T : EA A p N →ₗ[F] EA A p N` to `(mkE E' hE').comp e.symm.toLinearMap`.

Establish `hTe : ∀ s, T (mkE E hE s) = mkE E' hE' s` using `fun s => by show mkE E' hE' (e.symm (e s)) = _`. Rewrite using `[e.symm_apply_apply]`. Take `⟨ρ, hact, -, -, -⟩` from `GlobalTheory.thetaGrp_acts_linearly GlobalTheory.allSixLaws.1.globalFns _ A (N : ℤ) (TFK (R := R) F)`. Establish `huniq : ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R` using `R) F)) (a : EA A p N) (b b' : SecK A.L (snd (TFK (R := R) F) A.A).left N), IsActOf A.A A.L (N : ℤ) θ a.sec b → IsActOf A.A A.L (N : ℤ) θ a.sec b' → b = b' := fun θ a b b' h h' => by`. Use `((hact θ _ _).1 h).symm.trans ((hact θ _ _).1 h')` as an intermediate fact.

Conclude with `SecMod.ext_coord (p := (fst (Over.mk p) A.A).left) (s := SecMod.mk _ b) (t := SecMod.mk _ b') fun j => congrFun (congrArg Subtype.val this) j`. Establish `hT : ∀ x : Over.mk p ⟶ A.A, x ^ N = 1 → ∃ θ : ThetaGrp A.A A.L (N : ℤ) (Over.mk p), θ.pt = x ∧ ∀ v v' : EA A p N, IsActOf A.A A.L (N : ℤ) θ v.sec v'.sec → IsActOf A.A A.L (N : ℤ) θ (T v).sec (T v').sec`. Introduce `x hx`. Take `⟨p₀, hp₀⟩` from `(hE.onto x).1 hx`. Take `⟨w, hw⟩` from `hE.frame p₀`.

Take `⟨θ, hθ⟩` from `hE.lift p₀`. Take `⟨Φ, hΦ⟩` from `ReciprocityTheory.ChartRestriction.G.DVR.phiFun_of GlobalTheory.allSixLaws.1 R I D F N hN1 p₀ w hw.1`. Use `⟨θ, hθ.pt_eq.trans hp₀, fun v v' hvv => ?_⟩` and prove the remaining obligations. Take `⟨s, rfl⟩` from `(hbij E hE).2 v`. Establish `hPhi` using `(hΦ s (Φ s)).2 rfl`.

Establish `h₁` using `hE.act p₀ w θ s (Φ s) hw hθ hPhi`. Establish `h₂` using `hE'.act p₀ w θ s (Φ s) hw hθ hPhi`. Establish `e₁ : v' = mkE E hE (Φ s)` using `huniq θ _ _ _ hvv h₁`. Rewrite using `[e₁, hTe, hTe]`. Conclude with `h₂`.

Take `⟨c, hc⟩` from `GlobalTheory.ThetaCommutant.eq_smul_of_commute A F p N hNF T hT`. Establish `hpos : 0 < Module.finrank F (EA A p N)`. Rewrite using `[GlobalTheory.ThetaCommutant.finrank_eq A F p N hNF]`. Check the signs of the components of the expression. Use `haveI : Nontrivial (EA A p N) := Module.nontrivial_of_finrank_pos hpos`.

Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Take `⟨v, hv⟩` from `exists_ne (0 : EA A p N)`. Take `⟨s, rfl⟩` from `(hbij E hE).2 v`. Establish `h0 : mkE E' hE' s = mkE E' hE' 0` using `by rw [← hTe, hc, zero_smul, map_zero]`.

Use `(hbij E' hE').1 h0` as an intermediate fact. Substitute `this` using the available equality. Conclude with `hv (map_zero _)`. Use `⟨Units.mk0 c hc0, fun s j => ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun v : EA A p N => v.sec.f j) ((hTe s).symm.trans (hc _))`.

Conclude with `h`.
-/
theorem eqv_eq_smul : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ lab E E', Eqv D.toPre A F N lab E → Eqv D.toPre A F N lab E' → ∃ c : Fˣ, ∀ s j, (E' s).f j = liftFun A.A _ (fnF F c.val) * (E s).f j := by
  intro R _ _ _ I D A F _ _ _ N hN lab E E' hE hE'
  have hN1 : 1 ≤ N := hN.pos
  have hNF : (N : F) ≠ 0 := by
    have h1 : (N : R) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have h2 : (N : FractionRing R) ≠ 0 := fun h =>
      h1 (IsFractionRing.injective R (FractionRing R) (by rw [map_natCast, map_zero]; exact h))
    intro h
    apply h2
    apply (algebraMap (FractionRing R) F).injective
    rw [map_zero, map_natCast]
    exact_mod_cast h
  let p : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (FractionRing R)) := jFK (R := R) F
  let mkE : ∀ G : Fam D.toPre F N → SecK A.L (snd (TFK (R := R) F) A.A).left N, Eqv D.toPre A F N lab G →
      (Fam D.toPre F N →ₗ[F] EA A p N) := fun G hG =>
    { toFun := fun s => SecMod.mk _ (G s)
      map_add' := fun s t => SecMod.ext_coord fun j => hG.add s t (s + t) (fun _ _ => rfl) j
      map_smul' := fun c s => SecMod.ext_coord fun j =>
        hG.smul c s (c • s) ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff c s _).2 rfl) j }
  have hbij : ∀ G hG, Function.Bijective (mkE G hG) := fun G hG => hG.bij
  let e := LinearEquiv.ofBijective (mkE E hE) (hbij E hE)
  let T : EA A p N →ₗ[F] EA A p N := (mkE E' hE').comp e.symm.toLinearMap
  have hTe : ∀ s, T (mkE E hE s) = mkE E' hE' s := fun s => by
    show mkE E' hE' (e.symm (e s)) = _
    rw [e.symm_apply_apply]
  obtain ⟨ρ, hact, -, -, -⟩ := GlobalTheory.thetaGrp_acts_linearly GlobalTheory.allSixLaws.1.globalFns _ A (N : ℤ) (TFK (R := R) F)
  have huniq : ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (a : EA A p N) (b b' : SecK A.L (snd (TFK (R := R) F) A.A).left N),
      IsActOf A.A A.L (N : ℤ) θ a.sec b → IsActOf A.A A.L (N : ℤ) θ a.sec b' → b = b' := fun θ a b b' h h' => by
    have := ((hact θ _ _).1 h).symm.trans ((hact θ _ _).1 h')
    exact SecMod.ext_coord (p := (fst (Over.mk p) A.A).left) (s := SecMod.mk _ b) (t := SecMod.mk _ b')
      fun j => congrFun (congrArg Subtype.val this) j
  have hT : ∀ x : Over.mk p ⟶ A.A, x ^ N = 1 → ∃ θ : ThetaGrp A.A A.L (N : ℤ) (Over.mk p), θ.pt = x ∧
      ∀ v v' : EA A p N, IsActOf A.A A.L (N : ℤ) θ v.sec v'.sec →
        IsActOf A.A A.L (N : ℤ) θ (T v).sec (T v').sec := by
    intro x hx
    obtain ⟨p₀, hp₀⟩ := (hE.onto x).1 hx
    obtain ⟨w, hw⟩ := hE.frame p₀
    obtain ⟨θ, hθ⟩ := hE.lift p₀
    obtain ⟨Φ, hΦ⟩ := ReciprocityTheory.ChartRestriction.G.DVR.phiFun_of GlobalTheory.allSixLaws.1 R I D F N hN1 p₀ w hw.1
    refine ⟨θ, hθ.pt_eq.trans hp₀, fun v v' hvv => ?_⟩
    obtain ⟨s, rfl⟩ := (hbij E hE).2 v
    have hPhi := (hΦ s (Φ s)).2 rfl
    have h₁ := hE.act p₀ w θ s (Φ s) hw hθ hPhi
    have h₂ := hE'.act p₀ w θ s (Φ s) hw hθ hPhi
    have e₁ : v' = mkE E hE (Φ s) := huniq θ _ _ _ hvv h₁
    rw [e₁, hTe, hTe]
    exact h₂
  obtain ⟨c, hc⟩ := GlobalTheory.ThetaCommutant.eq_smul_of_commute A F p N hNF T hT
  have hpos : 0 < Module.finrank F (EA A p N) := by
    rw [GlobalTheory.ThetaCommutant.finrank_eq A F p N hNF]; positivity
  haveI : Nontrivial (EA A p N) := Module.nontrivial_of_finrank_pos hpos
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := exists_ne (0 : EA A p N)
    obtain ⟨s, rfl⟩ := (hbij E hE).2 v
    have h0 : mkE E' hE' s = mkE E' hE' 0 := by rw [← hTe, hc, zero_smul, map_zero]
    have := (hbij E' hE').1 h0
    subst this
    exact hv (map_zero _)
  refine ⟨Units.mk0 c hc0, fun s j => ?_⟩
  have h := congrArg (fun v : EA A p N => v.sec.f j) ((hTe s).symm.trans (hc _))
  exact h

end GlobalTheory.Mum
