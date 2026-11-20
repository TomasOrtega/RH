import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

/- English proof (translation)
Introduce `B H _ V _ _ _ hV G _ _ hG D A U ξ β hβ σ hσ k w hk hw F _ _ _ c x hx hxσ κ _ b hb Gκ _ m hm τ hτ z hz`. Establish `hk0 : k ≠ 0` using `by omega`. Set `u : Vˣ` to `Units.ofPowEqOne w k hw hk0`. Establish `hu : (u : V) = w` using `Units.val_ofPowEqOne w k hw hk0`. Establish `huk : u ^ k = 1` using `Units.pow_ofPowEqOne hw hk0`.

Set `τV : Multiplicative D.toPre.X →* Vˣ` to `(zpowersHom Vˣ u).comp (AddMonoidHom.toMultiplicative c)`. Establish `hτVv : ∀ χ, τV χ = u ^ c (Multiplicative.toAdd χ)` using `fun χ => rfl`. Establish `hτV : τV ^ k = 1` using `MonoidHom.ext fun χ => by`. Rewrite using `[MonoidHom.pow_apply, MonoidHom.one_apply, hτVv, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, huk, one_zpow]`. Establish `powk : ∀ {L : Type} [Field L] (t : Multiplicative D.toPre.X →* Lˣ) (y : L), y ^ k = 1 → (∀ χ, (t (Multiplicative.ofAdd χ) : L) = y ^ c χ) → t ^ k = 1`.

Introduce `L _ t y hy ht`. Use `MonoidHom.ext fun χ => Units.ext ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one, ← ofAdd_toAdd χ, ht, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]`. Establish `mapv : ∀ {L : Type} [Field L] (f : V →+* L) (χ : Multiplicative D.toPre.X), f (τV χ : V) = f w ^ c (Multiplicative.toAdd χ)`. Introduce `L _ f χ`.

Rewrite using `[hτVv, ← hu]`. Use `show ((Units.map (f : V →* L) (u ^ c (Multiplicative.toAdd χ)) : Lˣ) : L) = _`. Rewrite using `[map_zpow, Units.val_zpow_eq_zpow_val]`. Both sides reduce to the same expression. Take `⟨s, s1, s2, s3, s4⟩` from `GlobalTheory.ToricTorsionUnif.main V hV G hG D A U k hk`.

Set `sV` to `s V (RingHom.id V) τV hτV`. Set `σ₁ : Sp V ⟶ G.left` to `hβ.1.lift σ (𝟙 _) (by rw [hσ, Category.id_comp])`. Establish `hσ₁β : σ₁ ≫ β = σ` using `hβ.1.lift_fst _ _ _`. Establish `hσ₁G : σ₁ ≫ G.hom = 𝟙 _` using `hβ.1.lift_snd _ _ _`. Establish `hsVG : sV.left ≫ G.hom = 𝟙 _`.

Rewrite using `[Over.w sV]`. Use `show Spec.map (CommRingCat.ofHom (RingHom.id V)) = _`. Conclude with `Spec.map_id _`. Set `a : V →+* F` to `(algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))`. Establish `ha : spMap a = spMap (algebraMap (FractionRing V) F) ≫ jK V` using `by dsimp only [a, spMap, jK]`.

Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Establish `haI : Function.Injective a` using `(algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V (FractionRing V))`. Use `haveI : IsDominant (spMap a) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical a).2 (by rw [(RingHom.injective_iff_ker_eq_bot _).1 haI]; exact bot_le)⟩`. Use `haveI : IsSeparated G.hom := hG.separated`.

Take `⟨τF, q, hτF, hq, hqt, hqx⟩` from `hx`. Establish `hτFk : τF ^ k = 1` using `powk τF _ (by rw [← map_pow, ← map_pow, hw, map_one, map_one]) hτF`. Establish `e4` using `s4 F a τF hτFk q x rfl hq hqt hqx`. Establish `e2` using `s2 V F (RingHom.id V) a a τV hτV τF hτFk (RingHom.comp_id a).symm (fun χ => by`. Rewrite using `[mapv a χ]`.

Conclude with `hτF (Multiplicative.toAdd χ))`. Express the relevant statement in the definitionally equal form `_ = spMap a ≫ sV.left at e2`. Establish `hi : σ₁ = sV.left`. Use `ext_of_isDominant_of_isSeparated G.hom (hσ₁G.trans hsVG.symm) (spMap a) ?_` and prove the remaining obligations. Use `hβ.1.hom_ext ?_ ?_` and prove the remaining obligations.

Establish `l : spMap a ≫ σ₁ ≫ β = x.left ≫ genMap U ≫ β`. Rewrite using `[hσ₁β, hxσ, ha, Category.assoc]`. Establish `r : spMap a ≫ sV.left ≫ β = x.left ≫ genMap U ≫ β`. Rewrite using `[← Category.assoc, ← e2, ← e4, Category.assoc]`. Rewrite using `[Category.assoc, Category.assoc, l, r]`.

Simplify using `only [Category.assoc]`. Conclude with `congrArg (spMap a ≫ ·) (hσ₁G.trans hsVG.symm)`. Establish `hτk : τ ^ k = 1` using `powk τ (b w) (by rw [← map_pow, hw, map_one]) hτ`. Establish `e2'` using `s2 V κ (RingHom.id V) b b τV hτV τ hτk (RingHom.comp_id b).symm (fun χ => by`. Rewrite using `[mapv b χ]`.

Conclude with `hτ (Multiplicative.toAdd χ))`. Establish `e3` using `s3 κ κ b hb b (RingHom.id κ) Gκ m hm τ hτk z (RingHom.id_comp b).symm hz`. Rewrite using `[← hσ₁β, hi, ← Category.assoc, ← e2', e3, Category.assoc]`.
-/
theorem GlobalTheory.ToricTorsionClosedPt.main : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (ξ : Sp V ⟶ B) (β : G.left ⟶ H.left), IsGrpPullback G H ξ β → ∀ (σ : Sp V ⟶ H.left), σ ≫ H.hom = ξ → ∀ (k : ℕ) (w : V), 1 ≤ k → w ^ k = 1 → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (c : D.toPre.X →+ ℤ) (x : TFK (R := V) F ⟶ A.A), TorAt U F k (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) w)) c x → x.left ≫ genMap U ≫ β = spMap (algebraMap (FractionRing V) F) ≫ jK V ≫ σ → ∀ (κ : Type) [Field κ] (b : V →+* κ) (hb : ∀ y ∈ maximalIdeal V ^ (0 + 1), b y = 0) (Gκ : Over (Sp κ)) [GrpObj Gκ] (m : Gκ.left ⟶ G.left) (hm : IsGrpPullback Gκ G (spMap b) m) (τ : Multiplicative D.toPre.X →* κˣ), (∀ χ, (τ (Multiplicative.ofAdd χ) : κ) = b w ^ c χ) → ∀ (z : Over.mk (spMap (RingHom.id κ)) ⟶ splitTorus (Sp κ) D.toPre.X), (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) → spMap b ≫ σ = (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hb hm).left ≫ m ≫ β := by
  intro B H _ V _ _ _ hV G _ _ hG D A U ξ β hβ σ hσ k w hk hw F _ _ _ c x hx hxσ κ _ b hb Gκ _ m hm τ hτ z hz
  have hk0 : k ≠ 0 := by omega
  let u : Vˣ := Units.ofPowEqOne w k hw hk0
  have hu : (u : V) = w := Units.val_ofPowEqOne w k hw hk0
  have huk : u ^ k = 1 := Units.pow_ofPowEqOne hw hk0
  let τV : Multiplicative D.toPre.X →* Vˣ := (zpowersHom Vˣ u).comp (AddMonoidHom.toMultiplicative c)
  have hτVv : ∀ χ, τV χ = u ^ c (Multiplicative.toAdd χ) := fun χ => rfl
  have hτV : τV ^ k = 1 := MonoidHom.ext fun χ => by
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, hτVv, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, huk, one_zpow]
  have powk : ∀ {L : Type} [Field L] (t : Multiplicative D.toPre.X →* Lˣ) (y : L), y ^ k = 1 →
      (∀ χ, (t (Multiplicative.ofAdd χ) : L) = y ^ c χ) → t ^ k = 1 := by
    intro L _ t y hy ht
    refine MonoidHom.ext fun χ => Units.ext ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one,
      ← ofAdd_toAdd χ, ht, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  have mapv : ∀ {L : Type} [Field L] (f : V →+* L) (χ : Multiplicative D.toPre.X),
      f (τV χ : V) = f w ^ c (Multiplicative.toAdd χ) := by
    intro L _ f χ
    rw [hτVv, ← hu]
    show ((Units.map (f : V →* L) (u ^ c (Multiplicative.toAdd χ)) : Lˣ) : L) = _
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  obtain ⟨s, s1, s2, s3, s4⟩ := GlobalTheory.ToricTorsionUnif.main V hV G hG D A U k hk
  let sV := s V (RingHom.id V) τV hτV
  let σ₁ : Sp V ⟶ G.left := hβ.1.lift σ (𝟙 _) (by rw [hσ, Category.id_comp])
  have hσ₁β : σ₁ ≫ β = σ := hβ.1.lift_fst _ _ _
  have hσ₁G : σ₁ ≫ G.hom = 𝟙 _ := hβ.1.lift_snd _ _ _
  have hsVG : sV.left ≫ G.hom = 𝟙 _ := by
    rw [Over.w sV]
    show Spec.map (CommRingCat.ofHom (RingHom.id V)) = _
    exact Spec.map_id _

  let a : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
  have ha : spMap a = spMap (algebraMap (FractionRing V) F) ≫ jK V := by
    dsimp only [a, spMap, jK]
    rw [← Spec.map_comp]
    rfl
  have haI : Function.Injective a :=
    (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V (FractionRing V))
  haveI : IsDominant (spMap a) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical a).2
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 haI]; exact bot_le)⟩
  haveI : IsSeparated G.hom := hG.separated
  obtain ⟨τF, q, hτF, hq, hqt, hqx⟩ := hx
  have hτFk : τF ^ k = 1 := powk τF _ (by rw [← map_pow, ← map_pow, hw, map_one, map_one]) hτF
  have e4 := s4 F a τF hτFk q x rfl hq hqt hqx
  have e2 := s2 V F (RingHom.id V) a a τV hτV τF hτFk (RingHom.comp_id a).symm (fun χ => by
    rw [mapv a χ]; exact hτF (Multiplicative.toAdd χ))
  change _ = spMap a ≫ sV.left at e2
  have hi : σ₁ = sV.left := by
    refine ext_of_isDominant_of_isSeparated G.hom (hσ₁G.trans hsVG.symm) (spMap a) ?_
    refine hβ.1.hom_ext ?_ ?_
    · have l : spMap a ≫ σ₁ ≫ β = x.left ≫ genMap U ≫ β := by
        rw [hσ₁β, hxσ, ha, Category.assoc]
      have r : spMap a ≫ sV.left ≫ β = x.left ≫ genMap U ≫ β := by
        rw [← Category.assoc, ← e2, ← e4, Category.assoc]
      rw [Category.assoc, Category.assoc, l, r]
    · simp only [Category.assoc]
      exact congrArg (spMap a ≫ ·) (hσ₁G.trans hsVG.symm)
  have hτk : τ ^ k = 1 := powk τ (b w) (by rw [← map_pow, hw, map_one]) hτ
  have e2' := s2 V κ (RingHom.id V) b b τV hτV τ hτk (RingHom.comp_id b).symm (fun χ => by
    rw [mapv b χ]; exact hτ (Multiplicative.toAdd χ))
  have e3 := s3 κ κ b hb b (RingHom.id κ) Gκ m hm τ hτk z (RingHom.id_comp b).symm hz
  rw [← hσ₁β, hi, ← Category.assoc, ← e2', e3, Category.assoc]

end
