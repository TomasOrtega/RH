import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}

def UValOn (Xo : Moduli D l) (c : Coeff l) {S : Scheme.{0}} (j : Xo.XF c ⟶ S) (φ : InvFun (𝓞 E)) (J : S.IdealSheafData)
    (d : ℕ) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ →
    ∀ (χ : Sp W ⟶ S) (y : Sp (FractionRing W) ⟶ Xo.XF c), y ≫ j = jK W ≫ χ →
    ∀ (t : SAB H (Sp W)) (tK : SAB H (Sp (FractionRing W))), Nonempty (SABMap tK t (jK W)) →
      Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∀ P : PELUnif (maximalIdeal W) t,
      ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] →
        ∃ n : ℕ, (n : ℝ) = d * φ.evalZ be ∧ idlAlong J χ = Ideal.span {ϖ ^ n}

def GenOf (Xo : Moduli D l) (c : Coeff l) {R : Type} [CommRing R] [IsDomain R] (y : Sp (FractionRing R) ⟶ Xo.XF c)
    (t : SAB H (Sp R)) : Prop :=
  ∃ tK : SAB H (Sp (FractionRing R)), Nonempty (SABMap tK t (jK R)) ∧ Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _))

def UPoinOn (Xo : Moduli D l) (c : Coeff l) (φ : InvFun (𝓞 E)) {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z)
    (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) (BD : EffCartierData S) :
    Prop :=
  (IsProjOver zs ∧ IsNormalScheme Z ∧ IsOpenImmersion i ∧ Dense (Set.range i) ∧ i ≫ zs = pullback.snd _ _ ∧
    OZ.IsLB ∧ IsAmpleLB OZ) ∧
  (1 ≤ N ∧ ∀ (Y : Model Xo c (RingHom.id c.F)) (f : Y.X ⟶ Z), Y.j ≫ f = i → (GlobalTheory.FlagMod.detOm Y).IsLB →
    LBIso (OZ.pull f) (lbPow (GlobalTheory.FlagMod.detOm Y) N)) ∧
  (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)),
    Nonempty (PELUnif (maximalIdeal R) t) → ∀ y : Sp (FractionRing R) ⟶ Xo.XF c, GenOf Xo c y t →
      ∀ σ : Sp R ⟶ Sp c.F, jK R ≫ σ = y ≫ pullback.snd _ _ → ∃ ξ : Sp R ⟶ Z, jK R ≫ ξ = y ≫ i ∧ ξ ≫ zs = σ) ∧
  (1 ≤ d ∧ (∀ x ∈ J.support, x ∉ Set.range i) ∧ UValOn Xo c i φ J d) ∧
  (GlobalTheory.Poinc.IsNormBl π J ∧ IsProjOver (π ≫ zs) ∧ IsOpenImmersion j ∧ Dense (Set.range j) ∧ j ≫ π = i ∧
    π ⁻¹' Set.range i = Set.range j ∧ BD.idealSheaf = J.comap π ∧ UValOn Xo c j φ BD.idealSheaf d) ∧
  ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → IsAmpleLB (CechPic.tens (lbPow (OZ.pull π) k) (CechPic.dual BD.lb))

def UPoinSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ →
      ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l),
        ∃ (Z : Scheme.{0}) (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData)
          (S : Scheme.{0}) (π : S ⟶ Z) (j : Xo.XF c ⟶ S) (BD : EffCartierData S), UPoinOn Xo c φ zs i OZ N d J π j BD

variable {Xo : Moduli D l} {c : Coeff l}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨σ, -⟩ n hn`. Use `(IsUnit.mk0 (n : c.F) (Nat.cast_ne_zero.2 hn)).map (Spec.preimage σ).hom` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Introduce `hu haveI := c.fin`.

Set `g : c.F →+* FractionRing R` to `(Spec.preimage (y ≫ pullback.snd _ _)).hom`. Establish `hint : ∀ a : c.F, ∃ r : R, algebraMap R (FractionRing R) r = g a` using `fun a => by`. Take `⟨m, hm, ha⟩` from `((IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).2 (Algebra.IsAlgebraic.isAlgebraic a)).exists_integral_multiple`. Establish `hint : IsIntegral R (g (m • a))`. Take `⟨p, hp, h0⟩` from `ha`.

Use `⟨p.map (Int.castRingHom R), hp.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map, RingHom.ext_int ((algebraMap R (FractionRing R)).comp (Int.castRingHom R)) (g.comp (algebraMap ℤ c.F)), ← Polynomial.hom_eval₂, h0, map_zero]`. Take `⟨r, hr⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hint`. Establish `hum : IsUnit (m : R)`. Use `hu m.natAbs (by simpa using hm)` as an intermediate fact.

Apply the tactic sequence `rcases Int.natAbs_eq m with e | e <;> rw [e] <;> simpa using this`. Take `⟨u, hu'⟩` from `hum`. Use `⟨(↑u⁻¹ : R) * r, ?_⟩` and prove the remaining obligations. Establish `e : g (m • a) = algebraMap R (FractionRing R) u * g a` using `by simp [hu']`. Rewrite using `[map_mul, hr, e, ← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]`.

Use `choose f hf using hint`. Establish `hi` using `IsFractionRing.injective R (FractionRing R)`. Set `b : c.F →+* R` to `{ toFun := f map_one' := hi (by simp [hf]) map_mul' := fun _ _ => hi (by simp [hf]) map_zero' := hi (by simp [hf]) map_add' := fun _ _ => hi (by simp [hf]) }`. Use `⟨spMap b, ?_⟩` and prove the remaining obligations. Rewrite using `[← Spec.map_preimage (y ≫ pullback.snd _ _), ← Spec.map_comp]`.

Use `congr 1`. Use extensionality with `a`. Conclude with `hf a`.
-/
theorem exists_over_iff {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (y : Sp (FractionRing R) ⟶ Xo.XF c) :
    (∃ σ : Sp R ⟶ Sp c.F, jK R ≫ σ = y ≫ pullback.snd _ _) ↔ ∀ n : ℕ, n ≠ 0 → IsUnit (n : R) := by
  constructor
  · rintro ⟨σ, -⟩ n hn
    have := (IsUnit.mk0 (n : c.F) (Nat.cast_ne_zero.2 hn)).map (Spec.preimage σ).hom
    rwa [map_natCast] at this
  · intro hu
    haveI := c.fin
    let g : c.F →+* FractionRing R := (Spec.preimage (y ≫ pullback.snd _ _)).hom
    have hint : ∀ a : c.F, ∃ r : R, algebraMap R (FractionRing R) r = g a := fun a => by
      obtain ⟨m, hm, ha⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).2
        (Algebra.IsAlgebraic.isAlgebraic a)).exists_integral_multiple
      have hint : IsIntegral R (g (m • a)) := by
        obtain ⟨p, hp, h0⟩ := ha
        refine ⟨p.map (Int.castRingHom R), hp.map _, ?_⟩
        rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap R (FractionRing R)).comp (Int.castRingHom R))
          (g.comp (algebraMap ℤ c.F)), ← Polynomial.hom_eval₂, h0, map_zero]
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
      have hum : IsUnit (m : R) := by
        have := hu m.natAbs (by simpa using hm)
        rcases Int.natAbs_eq m with e | e <;> rw [e] <;> simpa using this
      obtain ⟨u, hu'⟩ := hum
      refine ⟨(↑u⁻¹ : R) * r, ?_⟩
      have e : g (m • a) = algebraMap R (FractionRing R) u * g a := by simp [hu']
      rw [map_mul, hr, e, ← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]
    choose f hf using hint
    have hi := IsFractionRing.injective R (FractionRing R)
    let b : c.F →+* R :=
      { toFun := f
        map_one' := hi (by simp [hf])
        map_mul' := fun _ _ => hi (by simp [hf])
        map_zero' := hi (by simp [hf])
        map_add' := fun _ _ => hi (by simp [hf]) }
    refine ⟨spMap b, ?_⟩
    rw [← Spec.map_preimage (y ≫ pullback.snd _ _), ← Spec.map_comp]
    congr 1
    ext a
    exact hf a

/- English proof (translation)
Use `haveI : IsIntegrallyClosed R := hR.1.2.2.1`. Take `⟨σ, hσ⟩` from `(exists_over_iff y).2 fun n hn => by`. Rewrite using `[← map_natCast (algebraMap ℚ R)]`. Conclude with `(IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn)).map _`. Conclude with `(h.2.2.1 R hR t ⟨P⟩ y hy σ hσ).imp fun _ h => h.1`.
-/
theorem UPoinOn.exists_extension {φ : InvFun (𝓞 E)} {Z : Scheme.{0}} {zs : Z ⟶ Sp c.F} {i : Xo.XF c ⟶ Z} {OZ : LB Z}
    {N d : ℕ} {J : Z.IdealSheafData} {S : Scheme.{0}} {π : S ⟶ Z} {j : Xo.XF c ⟶ S} {BD : EffCartierData S}
    (h : UPoinOn Xo c φ zs i OZ N d J π j BD) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra ℚ R]
    (hR : GlobalTheory.Mum.Base R) {t : SAB H (Sp R)} (P : PELUnif (maximalIdeal R) t) {y : Sp (FractionRing R) ⟶ Xo.XF c}
    (hy : GenOf Xo c y t) : ∃ ξ : Sp R ⟶ Z, jK R ≫ ξ = y ≫ i := by
  haveI : IsIntegrallyClosed R := hR.1.2.2.1
  obtain ⟨σ, hσ⟩ := (exists_over_iff y).2 fun n hn => by
    rw [← map_natCast (algebraMap ℚ R)]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn)).map _
  exact (h.2.2.1 R hR t ⟨P⟩ y hy σ hσ).imp fun _ h => h.1

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ χ _ _ _ _ _ _ _ _ _ _` and use `⟨0, by simp, (idlAlong_top χ).trans (by simp)⟩`.
-/
example {S : Scheme.{0}} (j : Xo.XF c ⟶ S) (φ : InvFun (𝓞 E)) : UValOn Xo c j φ ⊤ 0 :=
  fun _ _ _ _ _ _ _ χ _ _ _ _ _ _ _ _ _ _ => ⟨0, by simp, (idlAlong_top χ).trans (by simp)⟩

/- English proof (translation)
Rewrite using `[hq, Nat.min_zero]`. Conclude with `⟨isPolFan_zero, noSelfInt_zero⟩`.
-/
example (hq : D.q = 0) (φ : InvFun (𝓞 E)) : IsPolFan H.bar (min D.p D.q) φ ∧ NoSelfInt H.bar (min D.p D.q) φ := by
  rw [hq, Nat.min_zero]
  exact ⟨isPolFan_zero, noSelfInt_zero⟩

/- English proof (translation)
Use `⟨⟨GlobalTheory.Mum.base_powerSeries, fun n hn => ?_⟩, fun y σ h => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_natCast (algebraMap ℚ (PowerSeries ℚ))]`. Conclude with `(IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn)).map _`. Conclude with `PadicInt.irreducible_p.not_isUnit ((exists_over_iff y).1 ⟨σ, h⟩ p hp.out.ne_zero)`.
-/
example (p : ℕ) [hp : Fact p.Prime] : (GlobalTheory.Mum.Base (PowerSeries ℚ) ∧ ∀ n : ℕ, n ≠ 0 → IsUnit (n : PowerSeries ℚ)) ∧
    ∀ (y : Sp (FractionRing ℤ_[p]) ⟶ Xo.XF c) (σ : Sp ℤ_[p] ⟶ Sp c.F), jK ℤ_[p] ≫ σ ≠ y ≫ pullback.snd _ _ := by
  refine ⟨⟨GlobalTheory.Mum.base_powerSeries, fun n hn => ?_⟩, fun y σ h => ?_⟩
  · rw [← map_natCast (algebraMap ℚ (PowerSeries ℚ))]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn)).map _
  · exact PadicInt.irreducible_p.not_isUnit ((exists_over_iff y).1 ⟨σ, h⟩ p hp.out.ne_zero)

end GlobalTheory.UPoinc
