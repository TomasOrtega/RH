import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendAffineLineMorphismToProperAcrossPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineToAbelianVarietyConstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInversionCoordinateLocalizationPolynomialStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.NoRatCurve

section
variable (k : Type) [Field k] (P : Polynomial k)

def rhoMap : Localization.Away (Polynomial.X : Polynomial k) →+* Localization.Away (Polynomial.X * P) :=
  IsLocalization.Away.awayToAwayRight (S := Localization.Away (Polynomial.X : Polynomial k))
    (P := Localization.Away (Polynomial.X * P)) (Polynomial.X : Polynomial k) P

/- English proof (translation)
The claim follows from `IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away (Polynomial.X : Polynomial k)) (P := Localization.Away (Polynomial.X * P)) _ _ x`.
-/
theorem rhoMap_algebraMap (x : Polynomial k) :
    rhoMap k P (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)) x) =
      algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) x :=
  IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away (Polynomial.X : Polynomial k))
    (P := Localization.Away (Polynomial.X * P)) _ _ x

/- English proof (translation)
Establish `hu1 : IsUnit (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) Polynomial.X)` using `isUnit_of_mul_isUnit_left (x := algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) Polynomial.X) (y := algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P) (by rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit _)`. Apply `hu1.mul_left_cancel` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rhoMap_invSelf : rhoMap k P (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k)) =
    algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P *
      IsLocalization.Away.invSelf (Polynomial.X * P) := by
  have hu1 : IsUnit (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) Polynomial.X) :=
    isUnit_of_mul_isUnit_left (x := algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) Polynomial.X)
      (y := algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P)
      (by rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit _)
  apply hu1.mul_left_cancel
  calc _ = rhoMap k P (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)) Polynomial.X *
        IsLocalization.Away.invSelf (Polynomial.X : Polynomial k)) := by rw [map_mul, rhoMap_algebraMap]
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf, map_one]
    _ = _ := by rw [← _root_.mul_assoc, ← map_mul, IsLocalization.Away.mul_invSelf]

/- English proof (translation)
The claim follows from `RingHom.ext (rhoMap_algebraMap k P)`.
-/
theorem rhoMap_comp_algebraMap : (rhoMap k P).comp (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) =
    algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) :=
  RingHom.ext (rhoMap_algebraMap k P)

/- English proof (translation)
Use `Polynomial.ringHom_ext (fun a => ?_) ?_` and prove the remaining obligations. Establish `e1 : (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) : Localization.Away (Polynomial.X : Polynomial k))) (Polynomial.C a) = algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)) (Polynomial.C a)`. Rewrite using `[Polynomial.aeval_C]`. Both sides reduce to the same expression. Establish `e2 : (Polynomial.aeval (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P * IsLocalization.Away.invSelf (Polynomial.X * P))) (Polynomial.C a) = algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) (Polynomial.C a)`.

Rewrite using `[Polynomial.aeval_C]`. Both sides reduce to the same expression. Rewrite using `[RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, e1, e2, rhoMap_algebraMap]`. Rewrite using `[RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X, Polynomial.aeval_X]`. Conclude with `rhoMap_invSelf k P`.
-/
theorem rhoMap_comp_aeval : (rhoMap k P).comp (Polynomial.aeval (R := k) (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) :
      Localization.Away (Polynomial.X : Polynomial k))).toRingHom =
    (Polynomial.aeval (R := k) (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P *
      IsLocalization.Away.invSelf (Polynomial.X * P))).toRingHom := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · have e1 : (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) :
        Localization.Away (Polynomial.X : Polynomial k))) (Polynomial.C a) =
        algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)) (Polynomial.C a) := by
      rw [Polynomial.aeval_C]; rfl
    have e2 : (Polynomial.aeval (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P *
        IsLocalization.Away.invSelf (Polynomial.X * P))) (Polynomial.C a) =
        algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) (Polynomial.C a) := by
      rw [Polynomial.aeval_C]; rfl
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, e1, e2,
      rhoMap_algebraMap]
  · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Polynomial.aeval_X, Polynomial.aeval_X]
    exact rhoMap_invSelf k P

end

/- English proof (translation)
Simplify using `only [spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp]; rfl

/- English proof (translation)
Establish `hXP : (Polynomial.X * P : Polynomial k) ≠ 0` using `mul_ne_zero Polynomial.X_ne_zero hP`. Establish `hinj : Function.Injective (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)))` using `IsLocalization.injective (Localization.Away (Polynomial.X * P)) (powers_le_nonZeroDivisors_of_noZeroDivisors hXP)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (Submonoid.powers (Polynomial.X : Polynomial k)) z`.

Establish `e` using `rhoMap_algebraMap k P a`. Establish `h1 : IsLocalization.mk' (Localization.Away (Polynomial.X : Polynomial k)) a s * algebraMap _ _ (s : Polynomial k) = algebraMap _ _ a` using `IsLocalization.mk'_spec _ _ _`. Establish `h2` using `congrArg (rhoMap k P) h1`. Rewrite `h2` using `[map_mul, hz, zero_mul, e]`. Establish `ha : a = 0` using `hinj (by rw [← h2, map_zero])`.

Substitute `ha` using the available equality. Simplify using the standard rewrite rules.
-/
theorem awayToAwayRight_injective (k : Type) [Field k] (P : Polynomial k) (hP : P ≠ 0) :
    Function.Injective (rhoMap k P) := by
  have hXP : (Polynomial.X * P : Polynomial k) ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hP
  have hinj : Function.Injective (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P))) :=
    IsLocalization.injective (Localization.Away (Polynomial.X * P)) (powers_le_nonZeroDivisors_of_noZeroDivisors hXP)
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (Polynomial.X : Polynomial k)) z
  have e := rhoMap_algebraMap k P a
  have h1 : IsLocalization.mk' (Localization.Away (Polynomial.X : Polynomial k)) a s *
      algebraMap _ _ (s : Polynomial k) = algebraMap _ _ a := IsLocalization.mk'_spec _ _ _
  have h2 := congrArg (rhoMap k P) h1
  rw [map_mul, hz, zero_mul, e] at h2
  have ha : a = 0 := hinj (by rw [← h2, map_zero])
  subst ha
  simp

/- English proof (translation)
Introduce `k _ _ B _ _ P hP`. Proceed by induction on `hn : P.natDegree generalizing P with`. Consider the case `zero`. Introduce `u hu`. Take `⟨a, rfl⟩` from `Polynomial.natDegree_eq_zero.1 hn`.

Establish `ha : IsUnit (Polynomial.C a)` using `Polynomial.isUnit_C.2 (isUnit_iff_ne_zero.2 (by rintro rfl; simp at hP))`. Set `φ : Localization.Away (Polynomial.C a) →+* Polynomial k` to `IsLocalization.Away.lift (g := RingHom.id (Polynomial k)) (Polynomial.C a) ha`. Establish `hφ : (algebraMap (Polynomial k) (Localization.Away (Polynomial.C a))).comp φ = RingHom.id _` using `IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.C a)) (RingHom.ext fun x => by`. Simplify using `[φ, IsLocalization.Away.lift, IsLocalization.lift_eq])`. Use `⟨spMap φ ≫ u, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, hu, ← spMap_comp']`. Use `congr 1`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, IsScalarTower.algebraMap_apply k (Polynomial k) (Localization.Away (Polynomial.C a))]`. Simplify using `[φ, IsLocalization.Away.lift, IsLocalization.lift_eq]`.

Rewrite using `[← Category.assoc, ← spMap_comp', hφ] show Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ u = u`. Rewrite using `[CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]`. Consider the case `succ n ih`. Introduce `u hu`. Take `⟨c, hc⟩` from `IsAlgClosed.exists_root P (by rw [Polynomial.degree_eq_natDegree hP, hn]; exact_mod_cast Nat.succ_ne_zero n)`.

Take `⟨P', rfl⟩ : ∃ P', P = P' * (Polynomial.X - Polynomial.C c)` from `⟨P /ₘ (Polynomial.X - Polynomial.C c), by rw [mul_comm, Polynomial.mul_divByMonic_eq_iff_isRoot.2 hc]⟩`. Establish `hP' : P' ≠ 0` using `left_ne_zero_of_mul hP`. Establish `hn' : P'.natDegree = n`. Rewrite `hn` using `[Polynomial.natDegree_mul hP' (Polynomial.X_sub_C_ne_zero c), Polynomial.natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers.

Take `⟨v', hv', ev'⟩` from `GlobalTheory.T.extend_affineLine_morphism_to_proper_across_point k B P' c hP' u hu`. Take `⟨v, hv, ev⟩` from `ih P' hP' hn' v' hv'`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Rewrite using `[← ev', ← ev, ← Category.assoc, ← spMap_comp']`. Use `congr 2`.

Conclude with `RingHom.ext fun x => (IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away P') (P := Localization.Away (P' * (Polynomial.X - Polynomial.C c))) P' (Polynomial.X - Polynomial.C c) x).symm`.
-/
theorem extend_to_line : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [IsProper B.hom] [LocallyOfFinitePresentation B.hom] (P : Polynomial k), P ≠ 0 → ∀ u : Sp (Localization.Away P) ⟶ B.left, u ≫ B.hom = spMap (algebraMap k (Localization.Away P)) → ∃ v : Sp (Polynomial k) ⟶ B.left, v ≫ B.hom = spMap (algebraMap k (Polynomial k)) ∧ spMap (algebraMap (Polynomial k) (Localization.Away P)) ≫ v = u := by
  intro k _ _ B _ _ P hP
  induction hn : P.natDegree generalizing P with
  | zero =>
    intro u hu
    obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.1 hn
    have ha : IsUnit (Polynomial.C a) := Polynomial.isUnit_C.2 (isUnit_iff_ne_zero.2 (by rintro rfl; simp at hP))
    let φ : Localization.Away (Polynomial.C a) →+* Polynomial k := IsLocalization.Away.lift (g := RingHom.id (Polynomial k)) (Polynomial.C a) ha
    have hφ : (algebraMap (Polynomial k) (Localization.Away (Polynomial.C a))).comp φ = RingHom.id _ :=
      IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.C a)) (RingHom.ext fun x => by
        simp [φ, IsLocalization.Away.lift, IsLocalization.lift_eq])
    refine ⟨spMap φ ≫ u, ?_, ?_⟩
    · rw [Category.assoc, hu, ← spMap_comp']
      congr 1
      refine RingHom.ext fun x => ?_
      rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k (Polynomial k) (Localization.Away (Polynomial.C a))]
      simp [φ, IsLocalization.Away.lift, IsLocalization.lift_eq]
    · rw [← Category.assoc, ← spMap_comp', hφ]
      show Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ u = u
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  | succ n ih =>
    intro u hu
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_root P (by rw [Polynomial.degree_eq_natDegree hP, hn]; exact_mod_cast Nat.succ_ne_zero n)
    obtain ⟨P', rfl⟩ : ∃ P', P = P' * (Polynomial.X - Polynomial.C c) :=
      ⟨P /ₘ (Polynomial.X - Polynomial.C c), by rw [mul_comm, Polynomial.mul_divByMonic_eq_iff_isRoot.2 hc]⟩
    have hP' : P' ≠ 0 := left_ne_zero_of_mul hP
    have hn' : P'.natDegree = n := by
      rw [Polynomial.natDegree_mul hP' (Polynomial.X_sub_C_ne_zero c), Polynomial.natDegree_X_sub_C] at hn
      omega
    obtain ⟨v', hv', ev'⟩ := GlobalTheory.T.extend_affineLine_morphism_to_proper_across_point k B P' c hP' u hu
    obtain ⟨v, hv, ev⟩ := ih P' hP' hn' v' hv'
    refine ⟨v, hv, ?_⟩
    rw [← ev', ← ev, ← Category.assoc, ← spMap_comp']
    congr 2
    exact RingHom.ext fun x => (IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away P')
      (P := Localization.Away (P' * (Polynomial.X - Polynomial.C c))) P' (Polynomial.X - Polynomial.C c) x).symm

/- English proof (translation)
Introduce `k _ _ B _ hB P hP u a b hu`. Use `haveI := hB.smooth`. Use `haveI := hB.proper`. Take `⟨Q, hQ, σ, τ, h1, h2⟩` from `GlobalTheory.T.exists_inversion_coordinate_localization_polynomial k P hP`. Take `⟨f₀, hf₀, e₀⟩` from `extend_to_line k B P hP u hu`.

Establish `hu' : (spMap σ.toRingHom ≫ u) ≫ B.hom = spMap (algebraMap k (Localization.Away Q))`. Rewrite using `[Category.assoc, hu, ← spMap_comp']`. Use `congr 1`. Use extensionality with `x`. Conclude with `σ.commutes x`.

Take `⟨f₁, hf₁, e₁⟩` from `extend_to_line k B Q hQ _ hu'`. Use `haveI : IsDominant (spMap (rhoMap k P)) := by`. Rewrite using `[isDominant_iff]`. Use `show DenseRange (PrimeSpectrum.comap (rhoMap k P))`. Rewrite using `[PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot _).1 (awayToAwayRight_injective k P hP)]`.

Conclude with `bot_le`. Establish `hc : spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) : Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁`. Use `ext_of_isDominant_of_isSeparated B.hom ?_ (spMap (rhoMap k P)) ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, hf₀, hf₁, ← spMap_comp', ← spMap_comp']`. Use `congr 1`.

Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]`. Conclude with `(IsScalarTower.algebraMap_apply _ _ _ _).symm`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[spMap_comp' (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) (rhoMap k P), Category.assoc]`.

Use `_ = spMap τ.toRingHom ≫ spMap σ.toRingHom ≫ u := by`. Rewrite using `[rhoMap_comp_algebraMap, ← h1, spMap_comp', Category.assoc, e₀]`. Use `show spMap (τ.toRingHom.comp σ.toRingHom) ≫ u = _`. Rewrite using `[spMap_comp', Category.assoc]`. Use `_ = spMap (τ.toRingHom.comp (algebraMap (Polynomial k) (Localization.Away Q))) ≫ f₁ := by`.

Rewrite using `[spMap_comp', Category.assoc, e₁]`. Use `_ = _ := by`. Rewrite using `[h2, ← rhoMap_comp_aeval, spMap_comp', Category.assoc]`. Establish `key` using `GlobalTheory.T.projectiveLine_to_abelianVariety_const k B hB f₀ f₁ hf₀ hf₁ hc (a.comp (IsScalarTower.toAlgHom k (Polynomial k) (Localization.Away P))) (b.comp (IsScalarTower.toAlgHom k (Polynomial k) (Localization.Away P)))`. Rewrite using `[← e₀, ← Category.assoc, ← Category.assoc, ← spMap_comp', ← spMap_comp']`.

Conclude with `key`.
-/
theorem maps_from_open_line_const : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (P : Polynomial k), P ≠ 0 → ∀ (u : Sp (Localization.Away P) ⟶ B.left) (a b : Localization.Away P →ₐ[k] k), u ≫ B.hom = spMap (algebraMap k (Localization.Away P)) → spMap a.toRingHom ≫ u = spMap b.toRingHom ≫ u := by
  intro k _ _ B _ hB P hP u a b hu
  haveI := hB.smooth
  haveI := hB.proper
  obtain ⟨Q, hQ, σ, τ, h1, h2⟩ := GlobalTheory.T.exists_inversion_coordinate_localization_polynomial k P hP
  obtain ⟨f₀, hf₀, e₀⟩ := extend_to_line k B P hP u hu
  have hu' : (spMap σ.toRingHom ≫ u) ≫ B.hom = spMap (algebraMap k (Localization.Away Q)) := by
    rw [Category.assoc, hu, ← spMap_comp']
    congr 1
    ext x
    exact σ.commutes x
  obtain ⟨f₁, hf₁, e₁⟩ := extend_to_line k B Q hQ _ hu'
  haveI : IsDominant (spMap (rhoMap k P)) := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap (rhoMap k P))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (awayToAwayRight_injective k P hP)]
    exact bot_le
  have hc : spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) :
        Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁ := by
    refine ext_of_isDominant_of_isSeparated B.hom ?_ (spMap (rhoMap k P)) ?_
    · rw [Category.assoc, Category.assoc, hf₀, hf₁, ← spMap_comp', ← spMap_comp']
      congr 1
      refine RingHom.ext fun x => ?_
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
      exact (IsScalarTower.algebraMap_apply _ _ _ _).symm
    · calc spMap (rhoMap k P) ≫ spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀
          = spMap ((rhoMap k P).comp (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)))) ≫ f₀ := by
            rw [spMap_comp' (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) (rhoMap k P),
              Category.assoc]
        _ = spMap τ.toRingHom ≫ spMap σ.toRingHom ≫ u := by
            rw [rhoMap_comp_algebraMap, ← h1, spMap_comp', Category.assoc, e₀]
            show spMap (τ.toRingHom.comp σ.toRingHom) ≫ u = _
            rw [spMap_comp', Category.assoc]
        _ = spMap (τ.toRingHom.comp (algebraMap (Polynomial k) (Localization.Away Q))) ≫ f₁ := by
            rw [spMap_comp', Category.assoc, e₁]
        _ = _ := by
            rw [h2, ← rhoMap_comp_aeval, spMap_comp', Category.assoc]
  have key := GlobalTheory.T.projectiveLine_to_abelianVariety_const k B hB f₀ f₁ hf₀ hf₁ hc
    (a.comp (IsScalarTower.toAlgHom k (Polynomial k) (Localization.Away P)))
    (b.comp (IsScalarTower.toAlgHom k (Polynomial k) (Localization.Away P)))
  rw [← e₀, ← Category.assoc, ← Category.assoc, ← spMap_comp', ← spMap_comp']
  exact key

end GlobalTheory.NoRatCurve
end
