import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.NormCover

/- English proof (translation)
Rewrite using `[← Z.isoOfEq_hom_ι hV, ← Z.topIso_hom]`. Use `infer_instance`.
-/
theorem isIso_ι_of_eq_top {Z : Scheme.{0}} (V : Z.Opens) (hV : V = ⊤) : IsIso V.ι := by
  rw [← Z.isoOfEq_hom_ι hV, ← Z.topIso_hom]
  infer_instance

/- English proof (translation)
The claim follows from `Z.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => (Z.mem_basicOpen _ x hx).1 (h.ge hx)`.
-/
theorem isUnit_of_basicOpen_eq_top {Z : Scheme.{0}} (a : Γ(Z, ⊤)) (h : Z.basicOpen a = ⊤) : IsUnit a :=
  Z.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => (Z.mem_basicOpen _ x hx).1 (h.ge hx)

/- English proof (translation)
Use `top_unique fun x _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(g ≫ U.ι) x ∈ U`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `(g x).2`.
-/
theorem preimage_eq_top {X Y₀ : Scheme.{0}} (U : X.Opens) (g : Y₀ ⟶ U) : (g ≫ U.ι) ⁻¹ᵁ U = ⊤ := by
  refine top_unique fun x _ => ?_
  change (g ≫ U.ι) x ∈ U
  rw [Scheme.Hom.comp_apply]
  exact (g x).2

/- English proof (translation)
Set `s₀` to `g ≫ U.ι`. Use `haveI : QuasiCompact s₀ := inferInstance`. Use `haveI : QuasiSeparated s₀ := inferInstance`. Use `haveI : Smooth (s₀ ≫ π) := inferInstance`. Use `haveI : GlobalTheory.IsNormalScheme Y₀ := GlobalTheory.isNormalScheme_of_smooth (s₀ ≫ π)`.

Use `haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π`. Use `haveI : IsLocallyNoetherian Y₀ := LocallyOfFiniteType.isLocallyNoetherian (s₀ ≫ π)`. Use `haveI : IsReduced Y₀ := inferInstance`. Use `haveI hfin : IsFinite s₀.fromNormalization := GlobalTheory.isFinite_fromNormalization_of_locallyOfFiniteType (o := CommRingCat.of R) s₀ π fun y _ => hchar y`. Use `haveI : GlobalTheory.IsNormalScheme s₀.normalization := GlobalTheory.IsNormalScheme.normalization s₀`.

Establish `htop₀ : s₀ ⁻¹ᵁ U = ⊤` using `preimage_eq_top U g`. Use `haveI : IsIntegralHom (s₀ ∣_ U) := by haveI := isIso_ι_of_eq_top _ htop₀`. Establish `e : s₀ ∣_ U = (s₀ ⁻¹ᵁ U).ι ≫ g`. Rewrite using `[← cancel_mono U.ι, morphismRestrict_ι, Category.assoc]`. Rewrite using `[e]`.

Use `infer_instance`. Set `W` to `s₀.fromNormalization ⁻¹ᵁ U`. Use `haveI hiso : IsIso (s₀.toNormalization ∣_ W) := GlobalTheory.isIso_toNormalization_morphismRestrict s₀ U`. Establish `htop : s₀.toNormalization ⁻¹ᵁ W = ⊤`. Use `top_unique fun x _ => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `s₀.fromNormalization (s₀.toNormalization x) ∈ U`. Rewrite using `[← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]`. Conclude with `(g x).2`. Use `haveI := isIso_ι_of_eq_top _ htop`. Establish `hi : s₀.toNormalization = inv (s₀.toNormalization ⁻¹ᵁ W).ι ≫ (s₀.toNormalization ∣_ W) ≫ W.ι`.

Rewrite using `[morphismRestrict_ι, IsIso.inv_hom_id_assoc]`. Use `haveI : Flat (s₀.toNormalization ≫ s₀.fromNormalization ≫ π) := by`. Rewrite using `[← Category.assoc, Scheme.Hom.toNormalization_fromNormalization]`. Use `infer_instance`. Use `⟨s₀.normalization, s₀.fromNormalization, s₀.toNormalization, ?_, inferInstance, Scheme.Hom.toNormalization_fromNormalization s₀, hfin, fun y => ((GlobalTheory.isNormalScheme_iff _).mp inferInstance y).2, GlobalTheory.flat_normalization s₀ (s₀.fromNormalization ≫ π), LocallyOfFini …` and prove the remaining obligations.

Rewrite using `[hi] infer_instance`. Introduce `S f hf`. Establish `hr : Set.range f ⊆ Set.range W.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨x, rfl⟩`.

Conclude with `hf ⟨x, rfl⟩`. Use `⟨IsOpenImmersion.lift W.ι f hr ≫ inv (s₀.toNormalization ∣_ W) ≫ (s₀.toNormalization ⁻¹ᵁ W).ι, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, IsOpenImmersion.lift_fac]`.
-/
theorem exists_normalization_of_etale {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X Y₀ : Scheme.{0}} (π : X ⟶ Sp R) [Smooth π] (U : X.Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (g : Y₀ ⟶ U) [IsFinite g] [Etale g] (hchar : ∀ y : Y₀, CharZero (Y₀.residueField y)) :
    ∃ (Y : Scheme.{0}) (s : Y ⟶ X) (i : Y₀ ⟶ Y), IsOpenImmersion i ∧ IsDominant i ∧ i ≫ s = g ≫ U.ι ∧
      IsFinite s ∧ (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧ Flat (s ≫ π) ∧
      IsLocallyNoetherian Y ∧
      ∀ (S : Scheme.{0}) (f : S ⟶ Y), Set.range (f ≫ s) ⊆ U → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f := by
  let s₀ := g ≫ U.ι
  haveI : QuasiCompact s₀ := inferInstance
  haveI : QuasiSeparated s₀ := inferInstance
  haveI : Smooth (s₀ ≫ π) := inferInstance
  haveI : GlobalTheory.IsNormalScheme Y₀ := GlobalTheory.isNormalScheme_of_smooth (s₀ ≫ π)
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  haveI : IsLocallyNoetherian Y₀ := LocallyOfFiniteType.isLocallyNoetherian (s₀ ≫ π)
  haveI : IsReduced Y₀ := inferInstance
  haveI hfin : IsFinite s₀.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_locallyOfFiniteType (o := CommRingCat.of R) s₀ π fun y _ => hchar y
  haveI : GlobalTheory.IsNormalScheme s₀.normalization := GlobalTheory.IsNormalScheme.normalization s₀
  have htop₀ : s₀ ⁻¹ᵁ U = ⊤ := preimage_eq_top U g
  haveI : IsIntegralHom (s₀ ∣_ U) := by
    haveI := isIso_ι_of_eq_top _ htop₀
    have e : s₀ ∣_ U = (s₀ ⁻¹ᵁ U).ι ≫ g := by
      rw [← cancel_mono U.ι, morphismRestrict_ι, Category.assoc]
    rw [e]
    infer_instance
  let W := s₀.fromNormalization ⁻¹ᵁ U
  haveI hiso : IsIso (s₀.toNormalization ∣_ W) := GlobalTheory.isIso_toNormalization_morphismRestrict s₀ U
  have htop : s₀.toNormalization ⁻¹ᵁ W = ⊤ := by
    refine top_unique fun x _ => ?_
    change s₀.fromNormalization (s₀.toNormalization x) ∈ U
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]
    exact (g x).2
  haveI := isIso_ι_of_eq_top _ htop
  have hi : s₀.toNormalization = inv (s₀.toNormalization ⁻¹ᵁ W).ι ≫ (s₀.toNormalization ∣_ W) ≫ W.ι := by
    rw [morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  haveI : Flat (s₀.toNormalization ≫ s₀.fromNormalization ≫ π) := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
    infer_instance
  refine ⟨s₀.normalization, s₀.fromNormalization, s₀.toNormalization, ?_, inferInstance,
    Scheme.Hom.toNormalization_fromNormalization s₀, hfin,
    fun y => ((GlobalTheory.isNormalScheme_iff _).mp inferInstance y).2,
    GlobalTheory.flat_normalization s₀ (s₀.fromNormalization ≫ π),
    LocallyOfFiniteType.isLocallyNoetherian s₀.fromNormalization, ?_⟩
  · rw [hi]
    infer_instance
  · intro S f hf
    have hr : Set.range f ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hf ⟨x, rfl⟩
    refine ⟨IsOpenImmersion.lift W.ι f hr ≫ inv (s₀.toNormalization ∣_ W) ≫ (s₀.toNormalization ⁻¹ᵁ W).ι, ?_⟩
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, IsOpenImmersion.lift_fac]

end GlobalTheory.UPel.HT.ES.NormCover

namespace GlobalTheory.UPel.HT.ES.NormCover

/- English proof (translation)
Introduce `p _ D R _ _ _ _ b N _ M Y₀ s₀ g hgf hge hs`. Substitute `hs` using the available equality. Use `haveI := M.smooth`. Use `haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s`. Establish `hp : IsUnit ((p : ℕ) : Γ(Y₀, ⊤))`.

Apply `isUnit_of_basicOpen_eq_top` to reduce the goal to its premises. Establish `h` using `preimage_eq_top (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) g`. Rewrite `h` using `[Scheme.Hom.preimage_basicOpen, map_natCast]`. Conclude with `h`. Establish `hcop : ∀ m : ℕ, m.Coprime p → IsUnit ((m : ℕ) : Γ(Y₀, ⊤))`.

Introduce `m hm`. Use `(b.unit m hm).map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (g ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι ≫ M.s).appTop).hom` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hunit : ∀ n : ℕ, n ≠ 0 → IsUnit ((n : ℕ) : Γ(Y₀, ⊤))`. Introduce `n hn`.

Take `⟨a, m, hm, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).ne_one`. Use `push_cast`. Conclude with `(hp.pow a).mul (hcop m ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm).symm)`. Establish `hchar : ∀ y : Y₀, CharZero (Y₀.residueField y)`. Introduce `y`.

Use `charZero_of_inj_zero fun n hn => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Use `(hunit n h).map (Y₀.Γevaluation y).hom` as an intermediate fact. Rewrite `this` using `[map_natCast, hn]`. Conclude with `not_isUnit_zero this`.

Take `⟨Y, s, i, h1, h2, h3, h4, h5, h6, h7, h8⟩` from `exists_normalization_of_etale M.s _ g hchar`. Use `⟨Y, s, i, h1, h2, h3, h4, h5, h6, h7, fun S f hpS => h8 S f ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Establish `hx : x ∈ (f ≫ s) ⁻¹ᵁ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))`. Rewrite using `[Scheme.Hom.preimage_basicOpen, map_natCast]`.

Establish `hpS' : IsUnit ((p : ℕ) : Γ(S, (f ≫ s) ⁻¹ᵁ ⊤))` using `hpS`. Conclude with `(Scheme.basicOpen_of_isUnit S hpS').ge trivial`. Conclude with `hx`.
-/
theorem exists_finite_normal_model : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (M : Model b N) (Y₀ : Scheme.{0}) (s₀ : Y₀ ⟶ M.X) (g : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), IsFinite g → Etale g → g ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → ∃ (Y : Scheme.{0}) (s : Y ⟶ M.X) (i : Y₀ ⟶ Y), IsOpenImmersion i ∧ IsDominant i ∧ i ≫ s = s₀ ∧ IsFinite s ∧ (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧ Flat (s ≫ M.s) ∧ IsLocallyNoetherian Y ∧ (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) := by
  intro p _ D R _ _ _ _ b N _ M Y₀ s₀ g hgf hge hs
  subst hs
  haveI := M.smooth
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  have hp : IsUnit ((p : ℕ) : Γ(Y₀, ⊤)) := by
    apply isUnit_of_basicOpen_eq_top
    have h := preimage_eq_top (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) g
    rw [Scheme.Hom.preimage_basicOpen, map_natCast] at h
    exact h
  have hcop : ∀ m : ℕ, m.Coprime p → IsUnit ((m : ℕ) : Γ(Y₀, ⊤)) := by
    intro m hm
    have := (b.unit m hm).map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (g ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι ≫ M.s).appTop).hom
    rwa [map_natCast] at this
  have hunit : ∀ n : ℕ, n ≠ 0 → IsUnit ((n : ℕ) : Γ(Y₀, ⊤)) := by
    intro n hn
    obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).ne_one
    push_cast
    exact (hp.pow a).mul (hcop m ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm).symm)
  have hchar : ∀ y : Y₀, CharZero (Y₀.residueField y) := by
    intro y
    refine charZero_of_inj_zero fun n hn => ?_
    by_contra h
    have := (hunit n h).map (Y₀.Γevaluation y).hom
    rw [map_natCast, hn] at this
    exact not_isUnit_zero this
  obtain ⟨Y, s, i, h1, h2, h3, h4, h5, h6, h7, h8⟩ := exists_normalization_of_etale M.s _ g hchar
  refine ⟨Y, s, i, h1, h2, h3, h4, h5, h6, h7, fun S f hpS => h8 S f ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ (f ≫ s) ⁻¹ᵁ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)) := by
    rw [Scheme.Hom.preimage_basicOpen, map_natCast]
    have hpS' : IsUnit ((p : ℕ) : Γ(S, (f ≫ s) ⁻¹ᵁ ⊤)) := hpS
    exact (Scheme.basicOpen_of_isUnit S hpS').ge trivial
  exact hx

end GlobalTheory.UPel.HT.ES.NormCover
