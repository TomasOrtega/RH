import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOneLeft
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOfGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OverPointsExtOfInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RatioTranslate
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeIdPowFiniteEtaleSurjective

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj

namespace GlobalTheory.GoodPol

/- English proof (translation)
Establish `e` using `mul_geom_sum z n`. Rewrite `e` using `[hz, sub_self]`. Use `sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_right fun h0 => ?_)` and prove the remaining obligations. Establish `e'` using `congrArg (IsLocalRing.residue O) h0`. Simplify using `only [map_sum, map_pow, h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, _root_.mul_one, map_zero] at e'`.

Conclude with `(hn.map (IsLocalRing.residue O)).ne_zero ((map_natCast _ n).trans e')`.
-/
theorem eq_one_of_pow_eq_one {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {n : ℕ} (hn : IsUnit (n : O))
    {z : O} (hz : z ^ n = 1) (h : IsLocalRing.residue O z = 1) : z = 1 := by
  have e := mul_geom_sum z n
  rw [hz, sub_self] at e
  refine sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_right fun h0 => ?_)
  have e' := congrArg (IsLocalRing.residue O) h0
  simp only [map_sum, map_pow, h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, _root_.mul_one,
    map_zero] at e'
  exact (hn.map (IsLocalRing.residue O)).ne_zero ((map_natCast _ n).trans e')

/- English proof (translation)
Set `e` to `(Scheme.ΓSpecIso (CommRingCat.of O)).commRingCatIsoToRingEquiv`. Establish `hn' : IsUnit (n : O)` using `by simpa using hn.map e`. Establish `h₁ : e z.val = 1`. Use `eq_one_of_pow_eq_one hn' ?_ ?_` and prove the remaining obligations. Rewrite using `[← map_pow, ← Units.val_pow_eq_pow_val, hz, Units.val_one, map_one]`.

Establish `h₂` using `congrArg (fun q => q.hom z.val) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (IsLocalRing.residue O)))`. Establish `h₃ : (spMap (IsLocalRing.residue O)).appTop.hom z.val = 1` using `congrArg Units.val h`. Conclude with `h₂.symm.trans ((congrArg (Scheme.ΓSpecIso _).hom.hom h₃).trans (map_one _))`. Conclude with `Units.ext (e.injective (h₁.trans (map_one e).symm))`.
-/
theorem unit_eq_one {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {n : ℕ} (hn : IsUnit (n : Γ(Sp O, ⊤)))
    {z : Γ(Sp O, ⊤)ˣ} (hz : z ^ n = 1)
    (h : Units.map (spMap (IsLocalRing.residue O)).appTop.hom.toMonoidHom z = 1) : z = 1 := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of O)).commRingCatIsoToRingEquiv
  have hn' : IsUnit (n : O) := by simpa using hn.map e
  have h₁ : e z.val = 1 := by
    refine eq_one_of_pow_eq_one hn' ?_ ?_
    · rw [← map_pow, ← Units.val_pow_eq_pow_val, hz, Units.val_one, map_one]
    · have h₂ := congrArg (fun q => q.hom z.val)
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (IsLocalRing.residue O)))
      have h₃ : (spMap (IsLocalRing.residue O)).appTop.hom z.val = 1 := congrArg Units.val h
      exact h₂.symm.trans ((congrArg (Scheme.ΓSpecIso _).hom.hom h₃).trans (map_one _))
  exact Units.ext (e.injective (h₁.trans (map_one e).symm))

/- English proof (translation)
Substitute `hpk` using the available equality. Use `hA.proper` as an intermediate fact. Set `ρK : Over.mk (spMap (algebraMap O K) ≫ p) ⟶ Over.mk p` to `Over.homMk (spMap (algebraMap O K)) rfl`. Set `ρk : Over.mk (spMap (IsLocalRing.residue O) ≫ p) ⟶ Over.mk p` to `Over.homMk (spMap (IsLocalRing.residue O)) rfl`. Establish `inj : ∀ y y' : Over.mk p ⟶ A, ρK ≫ y = ρK ≫ y' → y = y'` using `fun y y' e => over_points_ext_of_injective S A O K _ (IsFractionRing.injective O K) p y y' (congrArg (fun q => q.left) e)`.

Establish `hnO : IsUnit (n : Γ(Sp O, ⊤))` using `by simpa using hn.map p.appTop.hom`. Establish `hnK : (n : K) ≠ 0`. Establish `h₁ : IsUnit (n : O)`. Simplify using `using hnO.map (Scheme.ΓSpecIso (CommRingCat.of O)).commRingCatIsoToRingEquiv`. Simplify using `using (h₁.map (algebraMap O K)).ne_zero`.

Choose the witnesses or unpack the hypotheses as in `⟨X, hX, hXx⟩ : ∃ X : Over.mk p ⟶ A, X ^ n = 1 ∧ ρk ≫ X = x := by`. Take `⟨-, -, het⟩` from `GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hn`. Take `⟨z, hz, -⟩` from `LatticeTorsion.existsUnique_torsion A n x hx`. Take `⟨y, hy, hy'⟩` from `(valuationRing_henselian_and_lift_of_isAlgClosed O K).2.2 _ (pullback.snd (torsion A n).hom p) inferInstance (pullback.lift z.left (spMap (IsLocalRing.residue O)) (Over.w z)) (pullback.lift_snd _ _ _)`. Set `w : Over.mk p ⟶ torsion A n` to `Over.homMk (y ≫ pullback.fst _ _) (by show (y ≫ _) ≫ _ = p`.

Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, hy, Category.id_comp])`. Establish `hw : ρk ≫ w = z` using `Over.OverMorphism.ext (by show spMap (IsLocalRing.residue O) ≫ y ≫ _ = _`. Rewrite using `[← Category.assoc, hy', pullback.lift_fst])`. Use `⟨w ≫ torsion.ι A n, ?_, by rw [← Category.assoc, hw, hz]⟩` and prove the remaining obligations. Rewrite using `[← MonObj.comp_pow, LatticeTorsion.torsionι_pow_eq_one, MonObj.comp_one]`.

Establish `hE : ValuativeCriterion.Existence A.hom`. Establish `h : UniversallyClosed A.hom` using `inferInstance`. Rewrite `h` using `[UniversallyClosed.eq_valuativeCriterion]`. Conclude with `h.1`. Take `⟨-, hfin, het, hsurj⟩` from `abelianScheme_id_pow_finite_etale_surjective S A n hA hn`.

Establish `hXK : (ρK ≫ X) ^ n = 1` using `by rw [← MonObj.comp_pow, hX, MonObj.comp_one]`. Establish `key : ρK ≫ X = 1`. Use `hgen _ (CubNondeg.main hL S A hA L c K _ n hnK hfin inferInstance hsurj _ hXK fun y hy => ?_)` and prove the remaining obligations. Take `⟨l, hl₁, hl₂⟩` from `(hE { R := O, K := K, commSq := ⟨Over.w y⟩, .. }).exists_lift`. Set `Y : Over.mk p ⟶ A` to `Over.homMk l hl₂`.

Establish `hYy : ρK ≫ Y = y` using `Over.OverMorphism.ext hl₁`. Establish `hY : Y ^ n = 1` using `inj _ _ (by rw [MonObj.comp_pow, hYy, hy, MonObj.comp_one])`. Take `⟨ex, -, pow, pull, -⟩` from `cubWeil_basic S A L c n (Over.mk p)`. Take `⟨ζ, hζ, -⟩` from `ex X Y hX hY`. Establish `hYk : (ρk ≫ Y) ^ n = 1` using `by rw [← MonObj.comp_pow, hY, MonObj.comp_one]`.

Establish `h₁` using `pull _ ρk X Y ζ hζ`. Rewrite `h₁` using `[hXx]`. Establish `h₂` using `KerPair.cubWeil_of_gen hL.globalFns S A hA L c n _ x (ρk ≫ Y) hx hYk ht`. Establish `h₃` using `((cubWeil_basic S A L c n _).1 x (ρk ≫ Y) hx hYk).unique h₁ h₂`. Establish `h₄ : ζ = 1` using `unit_eq_one hnO (pow X Y ζ hζ).2 h₃`.

Establish `h₅` using `pull _ ρK X Y ζ hζ`. Rewrite `h₅` using `[h₄, map_one, hYy]`. Then use the resulting hypothesis. Rewrite using `[← hXx, inj X 1 (key.trans (MonObj.comp_one _).symm), MonObj.comp_one]`.
-/
theorem eq_one_of_triv (hL : Out.Laws) {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {L : RigLB A} (c : CubicalStr A L) (O K : Type) [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (p : Sp O ⟶ S)
    {pk : Sp (IsLocalRing.ResidueField O) ⟶ S} (hpk : pk = spMap (IsLocalRing.residue O) ≫ p) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤)))
    (hgen : ∀ x : Over.mk (spMap (algebraMap O K) ≫ p) ⟶ A, Triv (Out.translDiff A L.L x) → x = 1)
    (x : Over.mk pk ⟶ A) (hx : x ^ n = 1) (ht : Triv (Out.translDiff A L.L x)) : x = 1 := by
  subst hpk
  have := hA.proper
  let ρK : Over.mk (spMap (algebraMap O K) ≫ p) ⟶ Over.mk p := Over.homMk (spMap (algebraMap O K)) rfl
  let ρk : Over.mk (spMap (IsLocalRing.residue O) ≫ p) ⟶ Over.mk p := Over.homMk (spMap (IsLocalRing.residue O)) rfl
  have inj : ∀ y y' : Over.mk p ⟶ A, ρK ≫ y = ρK ≫ y' → y = y' := fun y y' e =>
    over_points_ext_of_injective S A O K _ (IsFractionRing.injective O K) p y y' (congrArg (fun q => q.left) e)
  have hnO : IsUnit (n : Γ(Sp O, ⊤)) := by simpa using hn.map p.appTop.hom
  have hnK : (n : K) ≠ 0 := by
    have h₁ : IsUnit (n : O) := by
      simpa using hnO.map (Scheme.ΓSpecIso (CommRingCat.of O)).commRingCatIsoToRingEquiv
    simpa using (h₁.map (algebraMap O K)).ne_zero

  obtain ⟨X, hX, hXx⟩ : ∃ X : Over.mk p ⟶ A, X ^ n = 1 ∧ ρk ≫ X = x := by
    obtain ⟨-, -, het⟩ := GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hn
    obtain ⟨z, hz, -⟩ := LatticeTorsion.existsUnique_torsion A n x hx
    obtain ⟨y, hy, hy'⟩ := (valuationRing_henselian_and_lift_of_isAlgClosed O K).2.2 _
      (pullback.snd (torsion A n).hom p) inferInstance
      (pullback.lift z.left (spMap (IsLocalRing.residue O)) (Over.w z)) (pullback.lift_snd _ _ _)
    let w : Over.mk p ⟶ torsion A n := Over.homMk (y ≫ pullback.fst _ _) (by
      show (y ≫ _) ≫ _ = p
      rw [Category.assoc, pullback.condition, ← Category.assoc, hy, Category.id_comp])
    have hw : ρk ≫ w = z := Over.OverMorphism.ext (by
      show spMap (IsLocalRing.residue O) ≫ y ≫ _ = _
      rw [← Category.assoc, hy', pullback.lift_fst])
    refine ⟨w ≫ torsion.ι A n, ?_, by rw [← Category.assoc, hw, hz]⟩
    rw [← MonObj.comp_pow, LatticeTorsion.torsionι_pow_eq_one, MonObj.comp_one]
  have hE : ValuativeCriterion.Existence A.hom := by
    have h : UniversallyClosed A.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨-, hfin, het, hsurj⟩ := abelianScheme_id_pow_finite_etale_surjective S A n hA hn
  have hXK : (ρK ≫ X) ^ n = 1 := by rw [← MonObj.comp_pow, hX, MonObj.comp_one]
  have key : ρK ≫ X = 1 := by
    refine hgen _ (CubNondeg.main hL S A hA L c K _ n hnK hfin inferInstance hsurj _ hXK fun y hy => ?_)
    obtain ⟨l, hl₁, hl₂⟩ := (hE { R := O, K := K, commSq := ⟨Over.w y⟩, .. }).exists_lift
    let Y : Over.mk p ⟶ A := Over.homMk l hl₂
    have hYy : ρK ≫ Y = y := Over.OverMorphism.ext hl₁
    have hY : Y ^ n = 1 := inj _ _ (by rw [MonObj.comp_pow, hYy, hy, MonObj.comp_one])
    obtain ⟨ex, -, pow, pull, -⟩ := cubWeil_basic S A L c n (Over.mk p)
    obtain ⟨ζ, hζ, -⟩ := ex X Y hX hY
    have hYk : (ρk ≫ Y) ^ n = 1 := by rw [← MonObj.comp_pow, hY, MonObj.comp_one]
    have h₁ := pull _ ρk X Y ζ hζ
    rw [hXx] at h₁
    have h₂ := KerPair.cubWeil_of_gen hL.globalFns S A hA L c n _ x (ρk ≫ Y) hx hYk ht
    have h₃ := ((cubWeil_basic S A L c n _).1 x (ρk ≫ Y) hx hYk).unique h₁ h₂
    have h₄ : ζ = 1 := unit_eq_one hnO (pow X Y ζ hζ).2 h₃
    have h₅ := pull _ ρK X Y ζ hζ
    rwa [h₄, map_one, hYy] at h₅
  rw [← hXx, inj X 1 (key.trans (MonObj.comp_one _).symm), MonObj.comp_one]

end GlobalTheory.GoodPol
