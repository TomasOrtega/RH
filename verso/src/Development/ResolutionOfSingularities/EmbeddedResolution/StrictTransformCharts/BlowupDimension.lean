import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupClosedSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StalkKrullDimension
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FiniteKrullDim
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Establish `: IsIso (g.stalkMap y)` using `inferInstance`. Establish `e : (W.presheaf.stalk (g.base y)) ≅ (Y.presheaf.stalk y)` using `asIso (g.stalkMap y)`. Conclude with `(ringKrullDim_eq_of_ringEquiv e.commRingCatIsoToRingEquiv).symm`.
-/
theorem ringKrullDim_stalk_eq_of_isOpenImmersion {Y W : Scheme.{u}} (g : Y ⟶ W)
    [AlgebraicGeometry.IsOpenImmersion g] (y : Y) :
    ringKrullDim (Y.presheaf.stalk y) = ringKrullDim (W.presheaf.stalk (g.base y)) := by
  have : IsIso (g.stalkMap y) := inferInstance
  have e : (W.presheaf.stalk (g.base y)) ≅ (Y.presheaf.stalk y) := asIso (g.stalkMap y)
  exact (ringKrullDim_eq_of_ringEquiv e.commRingCatIsoToRingEquiv).symm

/- English proof (translation)
Establish `: IsIso (g.stalkMap y)` using `inferInstance`. Conclude with `isNoetherianRing_of_ringEquiv _ (CategoryTheory.asIso (g.stalkMap y)).commRingCatIsoToRingEquiv`.
-/
theorem isNoetherianRing_stalk_of_isOpenImmersion {Y W : Scheme.{u}} (g : Y ⟶ W)
    [AlgebraicGeometry.IsOpenImmersion g] (y : Y)
    [IsNoetherianRing (W.presheaf.stalk (g.base y))] :
    IsNoetherianRing (Y.presheaf.stalk y) := by
  have : IsIso (g.stalkMap y) := inferInstance
  exact isNoetherianRing_of_ringEquiv _
    (CategoryTheory.asIso (g.stalkMap y)).commRingCatIsoToRingEquiv

/- English proof (translation)
Use `c.isEtale` as an intermediate fact. Establish `hbase : U.ι.base (⟨y, hy⟩ : ↥U) = y` using `rfl`. Establish `h0 : IsNoetherianRing (Y.presheaf.stalk (U.ι.base (⟨y, hy⟩ : ↥U)))`. Rewrite using `[hbase]`. Conclude with `inferInstance`.

Establish `h1 : IsNoetherianRing (U.toScheme.presheaf.stalk (⟨y, hy⟩ : ↥U))` using `isNoetherianRing_stalk_of_isOpenImmersion U.ι (⟨y, hy⟩ : ↥U)`. Establish `h2` using `ringKrullDim_stalk_le_of_etale_affineSpace c.map (⟨y, hy⟩ : ↥U)`. Establish `h3` using `ringKrullDim_stalk_eq_of_isOpenImmersion U.ι (⟨y, hy⟩ : ↥U)`. Rewrite `h3` using `[hbase]`. Rewrite using `[← h3]`.

Conclude with `h2`.
-/
theorem ringKrullDim_stalk_le_of_etaleChart {k : Type u} [Field k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.IsLocallyNoetherian Y]
    {U : Y.Opens} {m : ℕ} (c : EtaleChart p U m) (y : Y) (hy : y ∈ U) :
    ringKrullDim (Y.presheaf.stalk y) ≤ ((m : ℕ∞) : WithBot ℕ∞) := by
  have := c.isEtale
  have hbase : U.ι.base (⟨y, hy⟩ : ↥U) = y := rfl
  have h0 : IsNoetherianRing (Y.presheaf.stalk (U.ι.base (⟨y, hy⟩ : ↥U))) := by
    rw [hbase]
    exact inferInstance
  have h1 : IsNoetherianRing (U.toScheme.presheaf.stalk (⟨y, hy⟩ : ↥U)) :=
    isNoetherianRing_stalk_of_isOpenImmersion U.ι (⟨y, hy⟩ : ↥U)
  have h2 := ringKrullDim_stalk_le_of_etale_affineSpace c.map (⟨y, hy⟩ : ↥U)
  have h3 := ringKrullDim_stalk_eq_of_isOpenImmersion U.ι (⟨y, hy⟩ : ↥U)
  rw [hbase] at h3
  rw [← h3]
  exact h2

/- English proof (translation)
Establish `: AlgebraicGeometry.Etale c.map` using `c.isEtale`. Establish `: AlgebraicGeometry.IsLocallyNoetherian X` using `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian p`. Take `⟨x0, hx0⟩` from `hU`. Take `⟨V, hVaff, hxv, -⟩` from `exists_isAffineOpen_mem_and_subset (X := U.toScheme) (x := ⟨x0, hx0⟩) (U := ⊤) trivial`. Take `⟨y, hy⟩` from `exists_isClosed_singleton_of_isAffineOpen V hVaff ⟨_, hxv⟩`.

Establish `he1 : AlgebraicGeometry.Etale (Scheme.Opens.ι V)` using `inferInstance`. Establish `he2 : AlgebraicGeometry.Etale (V.ι ≫ c.map)` using `inferInstance`. Establish `: IsNoetherianRing (X.presheaf.stalk ((V.ι ≫ U.ι).base y))` using `inferInstance`. Establish `: IsNoetherianRing (V.toScheme.presheaf.stalk y)` using `isNoetherianRing_stalk_of_isOpenImmersion (V.ι ≫ U.ι) y`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem le_topologicalKrullDim_of_etaleChart {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (hU : (U : Set X).Nonempty) :
    ((m : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim ↥X := by
  have : AlgebraicGeometry.Etale c.map := c.isEtale
  have : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨x0, hx0⟩ := hU
  obtain ⟨V, hVaff, hxv, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := U.toScheme) (x := ⟨x0, hx0⟩) (U := ⊤) trivial
  obtain ⟨y, hy⟩ := exists_isClosed_singleton_of_isAffineOpen V hVaff ⟨_, hxv⟩
  have he1 : AlgebraicGeometry.Etale (Scheme.Opens.ι V) := inferInstance
  have he2 : AlgebraicGeometry.Etale (V.ι ≫ c.map) := inferInstance
  have : IsNoetherianRing (X.presheaf.stalk ((V.ι ≫ U.ι).base y)) := inferInstance
  have : IsNoetherianRing (V.toScheme.presheaf.stalk y) :=
    isNoetherianRing_stalk_of_isOpenImmersion (V.ι ≫ U.ι) y
  calc ((m : ℕ∞) : WithBot ℕ∞)
      = ringKrullDim (V.toScheme.presheaf.stalk y) :=
        (ringKrullDim_stalk_eq_of_etale_affineSpace (V.ι ≫ c.map) y hy).symm
    _ = ringKrullDim (X.presheaf.stalk ((V.ι ≫ U.ι).base y)) :=
        ringKrullDim_stalk_eq_of_isOpenImmersion (V.ι ≫ U.ι) y
    _ ≤ topologicalKrullDim ↥X :=
        ringKrullDim_stalk_le_topologicalKrullDim X ((V.ι ≫ U.ι).base y)

/- English proof (translation)
Take `⟨W, hWeq⟩ : ∃ W : X.Opens, (W : Set X) = (Z.support : Set X)ᶜ` from `⟨⟨(Z.support : Set X)ᶜ, Z.support.2.isOpen_compl⟩, rfl⟩`. Establish `hW : ∀ x : X, x ∈ W → x ∉ Z.support`. Introduce `x hxm`. Establish `h2 : x ∈ (W : Set X)` using `hxm`. Rewrite `h2` using `[hWeq]`.

Conclude with `h2`. Establish `hxW : π.base x₁ ∈ W`. Establish `h2 : π.base x₁ ∈ (Z.support : Set X)ᶜ` using `hx₁`. Rewrite `h2` using `[← hWeq]`. Conclude with `h2`.

Establish `hx : x₁ ∈ π ⁻¹ᵁ W` using `hxW`. Establish `hiso : IsIso (π ∣_ W)` using `isIso_morphismRestrict_of_isBlowupAlongIdealSheaf hπ W hW`. Establish `hoi : AlgebraicGeometry.IsOpenImmersion (π ∣_ W)` using `inferInstance`. Establish `e1` using `ringKrullDim_stalk_eq_of_isOpenImmersion (Scheme.Opens.ι (π ⁻¹ᵁ W)) (⟨x₁, hx⟩ : ↥(π ⁻¹ᵁ W))`. Establish `e2` using `ringKrullDim_stalk_eq_of_isOpenImmersion ((π ∣_ W) ≫ Scheme.Opens.ι W) (⟨x₁, hx⟩ : ↥(π ⁻¹ᵁ W))`.

Rewrite `e2` using `[morphismRestrict_ι]`. Conclude with `e1.symm.trans e2`.
-/
theorem ringKrullDim_stalk_eq_of_isBlowupAlongIdealSheaf_of_notMem {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (x₁ : X₁) (hx₁ : π.base x₁ ∉ Z.support) :
    ringKrullDim (X₁.presheaf.stalk x₁) = ringKrullDim (X.presheaf.stalk (π.base x₁)) := by
  obtain ⟨W, hWeq⟩ : ∃ W : X.Opens, (W : Set X) = (Z.support : Set X)ᶜ :=
    ⟨⟨(Z.support : Set X)ᶜ, Z.support.2.isOpen_compl⟩, rfl⟩
  have hW : ∀ x : X, x ∈ W → x ∉ Z.support := by
    intro x hxm
    have h2 : x ∈ (W : Set X) := hxm
    rw [hWeq] at h2
    exact h2
  have hxW : π.base x₁ ∈ W := by
    have h2 : π.base x₁ ∈ (Z.support : Set X)ᶜ := hx₁
    rw [← hWeq] at h2
    exact h2
  have hx : x₁ ∈ π ⁻¹ᵁ W := hxW
  have hiso : IsIso (π ∣_ W) := isIso_morphismRestrict_of_isBlowupAlongIdealSheaf hπ W hW
  have hoi : AlgebraicGeometry.IsOpenImmersion (π ∣_ W) := inferInstance
  have e1 := ringKrullDim_stalk_eq_of_isOpenImmersion (Scheme.Opens.ι (π ⁻¹ᵁ W))
    (⟨x₁, hx⟩ : ↥(π ⁻¹ᵁ W))
  have e2 := ringKrullDim_stalk_eq_of_isOpenImmersion ((π ∣_ W) ≫ Scheme.Opens.ι W)
    (⟨x₁, hx⟩ : ↥(π ⁻¹ᵁ W))
  rw [morphismRestrict_ι] at e2
  exact e1.symm.trans e2

/- English proof (translation)
Establish `hXN : AlgebraicGeometry.IsLocallyNoetherian X` using `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian p`. Establish `hX₁N : AlgebraicGeometry.IsLocallyNoetherian X₁` using `isLocallyNoetherian_of_isBlowupAlongIdealSheaf π Z hπ`. Use `topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le X₁ _ ?_` and prove the remaining obligations. Introduce `x₁`. Distinguish the cases in `hx : π.base x₁ ∈ Z.support`.

Take `⟨U, hU, m, c, a, S, h1, h2, h3, h4⟩` from `hZE.exists_etaleChart hx`. Establish `hxU : x₁ ∈ π ⁻¹ᵁ U` using `hU`. Take `⟨s, hs, hmem⟩` from `exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ h4 x₁ hxU`. Establish `hle` using `ringKrullDim_stalk_le_of_etaleChart (π ≫ p) (blowupChartOfIsBlowup π c S hπ h4 s hs).chart x₁ hmem`. Conclude with `hle.trans (le_topologicalKrullDim_of_etaleChart p c ⟨π.base x₁, hU⟩)`.

Rewrite using `[ringKrullDim_stalk_eq_of_isBlowupAlongIdealSheaf_of_notMem π Z hπ x₁ hx]`. Conclude with `ringKrullDim_stalk_le_topologicalKrullDim X (π.base x₁)`.
-/
theorem topologicalKrullDim_le_of_blowup_strictNormalCrossings {k : Type u} [Field k] {X X₁ : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    (π : X₁ ⟶ X) (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (hZE : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    topologicalKrullDim ↥X₁ ≤ topologicalKrullDim ↥X := by
  have hXN : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian p
  have hX₁N : AlgebraicGeometry.IsLocallyNoetherian X₁ :=
    isLocallyNoetherian_of_isBlowupAlongIdealSheaf π Z hπ
  refine topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le X₁ _ ?_
  intro x₁
  by_cases hx : π.base x₁ ∈ Z.support
  · obtain ⟨U, hU, m, c, a, S, h1, h2, h3, h4⟩ := hZE.exists_etaleChart hx
    have hxU : x₁ ∈ π ⁻¹ᵁ U := hU
    obtain ⟨s, hs, hmem⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ h4 x₁ hxU
    have hle := ringKrullDim_stalk_le_of_etaleChart (π ≫ p)
      (blowupChartOfIsBlowup π c S hπ h4 s hs).chart x₁ hmem
    exact hle.trans (le_topologicalKrullDim_of_etaleChart p c ⟨π.base x₁, hU⟩)
  · rw [ringKrullDim_stalk_eq_of_isBlowupAlongIdealSheaf_of_notMem π Z hπ x₁ hx]
    exact ringKrullDim_stalk_le_topologicalKrullDim X (π.base x₁)

/- English proof (translation)
Use `revert hab hb`. Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot`. Introduce `_ _`. Rewrite using `[withBotSuccToNat_bot]`.

Conclude with `Nat.zero_le _`. Consider the case `coe x`. Proceed by induction on `b using WithBot.recBotCoe with`. Consider the case `bot`. Introduce `hab _`.

Conclude with `absurd (le_bot_iff.mp hab) (by simp)`. Consider the case `coe y`. Introduce `hab hb`. Establish `hy : y ≠ ⊤` using `fun h => hb.ne (by simp [h])`. Take `⟨n, rfl⟩` from `ENat.ne_top_iff_exists.mp hy`.

Establish `hxy : x ≤ ((n : ℕ) : ℕ∞)` using `WithBot.coe_le_coe.mp hab`. Establish `hx : x ≠ ⊤`. Introduce `h`. Rewrite `hxy` using `[h, top_le_iff]`. Conclude with `absurd hxy (by simp)`.

Take `⟨m, rfl⟩` from `ENat.ne_top_iff_exists.mp hx`. Establish `hmn : m ≤ n` using `by exact_mod_cast hxy`. Rewrite using `[withBotSuccToNat_coe, withBotSuccToNat_coe]`. Establish `h1 : ((m : ℕ) : ℕ∞).toNat = m` using `by simp`. Establish `h2 : ((n : ℕ) : ℕ∞).toNat = n` using `by simp`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem withBotSuccToNat_mono_of_lt_top {a b : WithBot ℕ∞} (hab : a ≤ b) (hb : b < ⊤) :
    withBotSuccToNat a ≤ withBotSuccToNat b := by
  revert hab hb
  induction a using WithBot.recBotCoe with
  | bot =>
      intro _ _
      rw [withBotSuccToNat_bot]
      exact Nat.zero_le _
  | coe x =>
      induction b using WithBot.recBotCoe with
      | bot =>
          intro hab _
          exact absurd (le_bot_iff.mp hab) (by simp)
      | coe y =>
          intro hab hb
          have hy : y ≠ ⊤ := fun h => hb.ne (by simp [h])
          obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hy
          have hxy : x ≤ ((n : ℕ) : ℕ∞) := WithBot.coe_le_coe.mp hab
          have hx : x ≠ ⊤ := by
            intro h
            rw [h, top_le_iff] at hxy
            exact absurd hxy (by simp)
          obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp hx
          have hmn : m ≤ n := by exact_mod_cast hxy
          rw [withBotSuccToNat_coe, withBotSuccToNat_coe]
          have h1 : ((m : ℕ) : ℕ∞).toNat = m := by simp
          have h2 : ((n : ℕ) : ℕ∞).toNat = n := by simp
          omega

/- English proof (translation)
Establish `h1 : topologicalKrullDim ↥X₁ ≤ topologicalKrullDim ↥X` using `topologicalKrullDim_le_of_blowup_strictNormalCrossings p π Z E hZE hπ`. Establish `h2 : topologicalKrullDim ↥X < ⊤` using `topologicalKrullDim_lt_top_of_finiteType p inferInstance inferInstance`. Simplify using `only [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim]`. Conclude with `withBotSuccToNat_mono_of_lt_top h1 h2`.
-/
theorem krullDimSucc_le_of_blowup_strictNormalCrossings {k : Type u} [Field k] {X X₁ : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (π : X₁ ⟶ X) (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (hZE : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    krullDimSucc X₁ ≤ krullDimSucc X := by
  have h1 : topologicalKrullDim ↥X₁ ≤ topologicalKrullDim ↥X :=
    topologicalKrullDim_le_of_blowup_strictNormalCrossings p π Z E hZE hπ
  have h2 : topologicalKrullDim ↥X < ⊤ :=
    topologicalKrullDim_lt_top_of_finiteType p inferInstance inferInstance
  simp only [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim]
  exact withBotSuccToNat_mono_of_lt_top h1 h2

end FunctorialResolution.EmbeddedResolution
