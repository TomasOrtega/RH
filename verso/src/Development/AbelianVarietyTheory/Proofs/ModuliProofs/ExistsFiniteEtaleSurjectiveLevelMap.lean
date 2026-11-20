import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.LevelMap

/- English proof (translation)
Substitute `hi` using the available equality. Set `p : pullback s₀ (i₁ ≫ k) ⟶ pullback s₀ k` to `pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ i₁) (by simp [pullback.condition])`. Establish `hp : IsPullback p (pullback.snd _ _) (pullback.snd s₀ k) i₁`. Use `IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback s₀ k)` and prove the remaining obligations. Establish `: p ≫ pullback.fst s₀ k = pullback.fst _ _` using `pullback.lift_fst _ _ _`.

Rewrite using `[this]`. Conclude with `IsPullback.of_hasPullback _ _`. Establish `hq : IsPullback (pullback.fst s₁ i₁) rF (pullback.lift r s₁ hr) p`. Use `IsPullback.of_bot ?_ ?_ hp` and prove the remaining obligations. Rewrite using `[h₂, pullback.lift_snd]`.

Conclude with `IsPullback.of_hasPullback _ _`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst, h₁]`. Rewrite using `[Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd, reassoc_of% h₂, pullback.condition]`. Use `MorphismProperty.of_isPullback_of_descendsAlong (P := P) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hq.flip ⟨⟨?_, ?_⟩, ?_⟩ h` and prove the remaining obligations.

Conclude with `MorphismProperty.of_isPullback (P := @Surjective) hp.flip ‹_›`. Conclude with `MorphismProperty.of_isPullback (P := @Flat) hp.flip ‹_›`. Conclude with `MorphismProperty.of_isPullback (P := @QuasiCompact) hp.flip ‹_›`.
-/
theorem of_baseChange (P : MorphismProperty Scheme.{0})
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    {X₀ X₁ S₀ S₁ T : Scheme.{0}} (s₀ : X₀ ⟶ S₀) (s₁ : X₁ ⟶ S₁) (k : S₁ ⟶ S₀) (r : X₁ ⟶ X₀)
    (hr : r ≫ s₀ = s₁ ≫ k) (i₀ : T ⟶ S₀) (i₁ : T ⟶ S₁) (hi : i₁ ≫ k = i₀)
    [Surjective i₁] [Flat i₁] [QuasiCompact i₁]
    (rF : pullback s₁ i₁ ⟶ pullback s₀ i₀) (h₁ : rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r)
    (h₂ : rF ≫ pullback.snd _ _ = pullback.snd _ _) (h : P rF) : P (pullback.lift r s₁ hr) := by
  subst hi
  let p : pullback s₀ (i₁ ≫ k) ⟶ pullback s₀ k :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ i₁) (by simp [pullback.condition])
  have hp : IsPullback p (pullback.snd _ _) (pullback.snd s₀ k) i₁ := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback s₀ k)
    have : p ≫ pullback.fst s₀ k = pullback.fst _ _ := pullback.lift_fst _ _ _
    rw [this]
    exact IsPullback.of_hasPullback _ _
  have hq : IsPullback (pullback.fst s₁ i₁) rF (pullback.lift r s₁ hr) p := by
    refine IsPullback.of_bot ?_ ?_ hp
    · rw [h₂, pullback.lift_snd]
      exact IsPullback.of_hasPullback _ _
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst, h₁]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd, reassoc_of% h₂, pullback.condition]
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := P)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hq.flip ⟨⟨?_, ?_⟩, ?_⟩ h
  · exact MorphismProperty.of_isPullback (P := @Surjective) hp.flip ‹_›
  · exact MorphismProperty.of_isPullback (P := @Flat) hp.flip ‹_›
  · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hp.flip ‹_›

/- English proof (translation)
Use `isAffineHom_descendsAlong_fpqc.{0}` as an intermediate fact. Use `⟨fun {A X Y Z fst snd f g} H hf hfst => ?_⟩` and prove the remaining obligations. Establish `a2 : IsAffineHom g` using `MorphismProperty.of_isPullback_of_descendsAlong (P := @IsAffineHom) H hf inferInstance`. Establish `a3 : UniversallyClosed g` using `MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) H hf inferInstance`. Establish `a4 : LocallyOfFiniteType g` using `MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType) H hf inferInstance`.

Conclude with `(IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, a4⟩`.
-/
theorem isFinite_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@IsFinite : MorphismProperty Scheme.{0})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := isAffineHom_descendsAlong_fpqc.{0}
  refine ⟨fun {A X Y Z fst snd f g} H hf hfst => ?_⟩
  have a2 : IsAffineHom g := MorphismProperty.of_isPullback_of_descendsAlong (P := @IsAffineHom) H hf inferInstance
  have a3 : UniversallyClosed g :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) H hf inferInstance
  have a4 : LocallyOfFiniteType g :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType) H hf inferInstance
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
    ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, a4⟩

/- English proof (translation)
Use `⟨fun x => ?_⟩` and prove the remaining obligations. Take `⟨y⟩ : Nonempty (Sp L)` from `inferInstanceAs (Nonempty (PrimeSpectrum L))`. Conclude with `⟨y, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩`.
-/
theorem surjective_spMap {K L : Type} [Field K] [Field L] (k : K →+* L) : Surjective (spMap k) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨y⟩ : Nonempty (Sp L) := inferInstanceAs (Nonempty (PrimeSpectrum L))
  exact ⟨y, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩

/- English proof (translation)
Rewrite using `[Flat.SpecMap_iff]`. Use `algebraize [k]`. Conclude with `(inferInstance : Module.Flat K L)`.
-/
theorem flat_spMap {K L : Type} [Field K] [Field L] (k : K →+* L) : Flat (spMap k) := by
  rw [Flat.SpecMap_iff]
  algebraize [k]
  exact (inferInstance : Module.Flat K L)

/- English proof (translation)
Use `algebraize [k]`. Establish `: IsScalarTower ℚ K L` using `IsScalarTower.of_algebraMap_eq fun x => by simp`. Establish `hf : Module.Finite K L` using `Module.Finite.of_restrictScalars_finite ℚ K L`. Prove the components needed by the constructor for the conclusion. Rewrite using `[IsFinite.SpecMap_iff]`.

Conclude with `hf`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Etale)]`. Establish `: Algebra.FormallyEtale K L` using `Algebra.FormallyEtale.of_isSeparable K L`. Establish `: Algebra.FinitePresentation K L` using `Algebra.FinitePresentation.of_finiteType.mp inferInstance`. Conclude with `(⟨inferInstance, inferInstance⟩ : Algebra.Etale K L)`.
-/
theorem finite_etale_spMap {K L : Type} [Field K] [Field L] [CharZero K] [CharZero L] [FiniteDimensional ℚ L]
    (k : K →+* L) : IsFinite (spMap k) ∧ Etale (spMap k) := by
  algebraize [k]
  have : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun x => by simp
  have hf : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  constructor
  · rw [IsFinite.SpecMap_iff]
    exact hf
  · rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
    have : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact (⟨inferInstance, inferInstance⟩ : Algebra.Etale K L)

/- English proof (translation)
Introduce `E _ _ _ H D Xo hN l₀ l₁ hd`. Take `⟨r, k, ν, hk, hr, h1, h2, -, hc⟩` from `hN l₀ l₁ (Xo l₀) (Xo l₁) hd`. Take `⟨c₁⟩ : Nonempty (Coeff l₁)` from `inferInstance`. Establish `hle : KA l₀ ≤ c₁.F` using `fun x hx => by`. Use `c₁.le (k ⟨x, hx⟩).2` as an intermediate fact.

Rewrite `this` using `[hk]`. Then use the resulting hypothesis. Set `c₀ : Coeff l₀` to `{ F := c₁.F fin := c₁.fin conj := c₁.conj zeta_mem := by`. Take `⟨e, he⟩` from `LevelExist.zeta_eq_pow_of_dvd (a := l₀.M') (LevelExist.M'_pos l₁) (Nat.lcm_dvd (hd.1.trans (Nat.dvd_lcm_left _ _)) (hd.2.2.trans (Nat.dvd_lcm_right _ _)) : l₀.M' ∣ l₁.M')`. Rewrite using `[he]`. Conclude with `pow_mem c₁.zeta_mem e`.

Use `le := hle }`. Take `⟨rF, e1, e2, f1, f2, f3, -⟩` from `hc c₀ c₁ rfl`. Establish `hid : spMap (IntermediateField.inclusion (le_refl c₁.F)).toRingHom = 𝟙 (Sp c₁.F)`. Rewrite using `[← Spec.map_id]`. Both sides reduce to the same expression.

Establish `e2' : rF ≫ pullback.snd _ _ = pullback.snd _ _` using `e2.trans ((congrArg _ hid).trans (Category.comp_id _))`. Establish `hi : spMap (IntermediateField.inclusion c₁.le).toRingHom ≫ spMap k = spMap (IntermediateField.inclusion c₀.le).toRingHom`. Rewrite using `[← Spec.map_comp]`. Use `congr 1`. Use extensionality with `x`.

Conclude with `hk x`. Use `surjective_spMap (IntermediateField.inclusion c₁.le).toRingHom` as an intermediate fact. Use `flat_spMap (IntermediateField.inclusion c₁.le).toRingHom` as an intermediate fact. Use `isFinite_descendsAlong_fpqc` as an intermediate fact. Establish `g1 : IsFinite (pullback.lift r _ hr)` using `of_baseChange @IsFinite _ _ _ r hr _ _ hi rF e1 e2' f1`.

Establish `g2 : Etale (pullback.lift r _ hr)` using `of_baseChange @Etale _ _ _ r hr _ _ hi rF e1 e2' f2`. Establish `g3 : Surjective (pullback.lift r _ hr)` using `of_baseChange @Surjective _ _ _ r hr _ _ hi rF e1 e2' f3`. Use `c₁.fin` as an intermediate fact. Establish `: FiniteDimensional ℚ (KA l₁)` using `FiniteDimensional.of_injective (IntermediateField.inclusion c₁.le).toLinearMap (IntermediateField.inclusion c₁.le).injective`. Take `⟨k1, k2⟩` from `finite_etale_spMap k`.

Establish `k3` using `surjective_spMap k`. Establish `hfac : pullback.lift r _ hr ≫ pullback.fst _ _ = r` using `pullback.lift_fst _ _ _`. Use `⟨k, r, ν, hr, hk, ⟨h1, h2⟩, g1, g2, g3, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `all_goals`. Rewrite using `[← hfac]`.

Use `infer_instance`.
-/
theorem exists_levelMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₁ : Level H), l₀.Dvd l₁ → ∃ (k : KA l₀ →+* KA l₁) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (hr : r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k), IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k ∧ LevComp (Xo l₁).univ (Xo l₀).univ r ν ∧ IsFinite (pullback.lift r _ hr) ∧ Etale (pullback.lift r _ hr) ∧ Surjective (pullback.lift r _ hr) ∧ IsFinite r ∧ Etale r ∧ Surjective r := by
  intro E _ _ _ H D Xo hN l₀ l₁ hd
  obtain ⟨r, k, ν, hk, hr, h1, h2, -, hc⟩ := hN l₀ l₁ (Xo l₀) (Xo l₁) hd
  obtain ⟨c₁⟩ : Nonempty (Coeff l₁) := inferInstance
  have hle : KA l₀ ≤ c₁.F := fun x hx => by
    have := c₁.le (k ⟨x, hx⟩).2
    rwa [hk] at this
  let c₀ : Coeff l₀ :=
    { F := c₁.F
      fin := c₁.fin
      conj := c₁.conj
      zeta_mem := by
        obtain ⟨e, he⟩ := LevelExist.zeta_eq_pow_of_dvd (a := l₀.M') (LevelExist.M'_pos l₁)
          (Nat.lcm_dvd (hd.1.trans (Nat.dvd_lcm_left _ _)) (hd.2.2.trans (Nat.dvd_lcm_right _ _)) : l₀.M' ∣ l₁.M')
        rw [he]
        exact pow_mem c₁.zeta_mem e
      le := hle }
  obtain ⟨rF, e1, e2, f1, f2, f3, -⟩ := hc c₀ c₁ rfl
  have hid : spMap (IntermediateField.inclusion (le_refl c₁.F)).toRingHom = 𝟙 (Sp c₁.F) := by
    rw [← Spec.map_id]
    rfl
  have e2' : rF ≫ pullback.snd _ _ = pullback.snd _ _ := e2.trans ((congrArg _ hid).trans (Category.comp_id _))
  have hi : spMap (IntermediateField.inclusion c₁.le).toRingHom ≫ spMap k =
      spMap (IntermediateField.inclusion c₀.le).toRingHom := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact hk x
  have := surjective_spMap (IntermediateField.inclusion c₁.le).toRingHom
  have := flat_spMap (IntermediateField.inclusion c₁.le).toRingHom
  have := isFinite_descendsAlong_fpqc
  have g1 : IsFinite (pullback.lift r _ hr) := of_baseChange @IsFinite _ _ _ r hr _ _ hi rF e1 e2' f1
  have g2 : Etale (pullback.lift r _ hr) := of_baseChange @Etale _ _ _ r hr _ _ hi rF e1 e2' f2
  have g3 : Surjective (pullback.lift r _ hr) := of_baseChange @Surjective _ _ _ r hr _ _ hi rF e1 e2' f3
  have := c₁.fin
  have : FiniteDimensional ℚ (KA l₁) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion c₁.le).toLinearMap
      (IntermediateField.inclusion c₁.le).injective
  obtain ⟨k1, k2⟩ := finite_etale_spMap k
  have k3 := surjective_spMap k
  have hfac : pullback.lift r _ hr ≫ pullback.fst _ _ = r := pullback.lift_fst _ _ _
  refine ⟨k, r, ν, hr, hk, ⟨h1, h2⟩, g1, g2, g3, ?_, ?_, ?_⟩
  all_goals
    rw [← hfac]
    infer_instance

end GlobalTheory.LevelMap

end
