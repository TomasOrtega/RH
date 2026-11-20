import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoOfDensePartOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompPowEqOneOfPullbackHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteTorsionSemiAbelian
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfSchemeTheoreticallyDominant
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteOfIsClosedOfFiniteInterClosedPoints

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.HomExt

/- English proof (translation)
Take `⟨ξ, hξ, hs⟩` from `exists_mem_genericPoints_specializes z`. Establish `hξ'` using `genericPoints_subset_range_of_isDominant i hξ`. Distinguish the cases in `hne : ξ = z`. Conclude with `.inl (hne ▸ hξ')`. Take `⟨O, _, _, -, a, h₀, h₁⟩` from `exists_complete_discreteValuationRing_of_specializes hs hne`.

Take `⟨c, hc⟩` from `exists_lift_of_range_subset i (spMap (algebraMap O (FractionRing O)) ≫ a) (by`. Introduce and unpack `_ ⟨t, rfl⟩`. Establish `: spMap (algebraMap O (FractionRing O)) t = (⊥ : PrimeSpectrum O)`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap O (FractionRing O)) t.asIdeal = ⊥`.

Rewrite using `[@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime]`. Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)`. Rewrite using `[Scheme.Hom.comp_apply, this]`. Conclude with `h₀ ▸ hξ')`. Conclude with `.inr ⟨O, inferInstance, inferInstance, inferInstance, a, c, hc, h₁⟩`.
-/
theorem mem_range_or_exists_dvr {W Z : Scheme.{0}} (i : W ⟶ Z) [IsPreimmersion i] [Flat i]
    [IsDominant i] [QuasiCompact i] [IsLocallyNoetherian Z] (z : Z) :
    z ∈ Set.range i ∨ ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T)
      (_ : IsDiscreteValuationRing T) (a : Sp T ⟶ Z) (c : Sp (FractionRing T) ⟶ W),
      c ≫ i = spMap (algebraMap T (FractionRing T)) ≫ a ∧ a (IsLocalRing.closedPoint T) = z := by
  obtain ⟨ξ, hξ, hs⟩ := exists_mem_genericPoints_specializes z
  have hξ' := genericPoints_subset_range_of_isDominant i hξ
  by_cases hne : ξ = z
  · exact .inl (hne ▸ hξ')
  obtain ⟨O, _, _, -, a, h₀, h₁⟩ := exists_complete_discreteValuationRing_of_specializes hs hne
  obtain ⟨c, hc⟩ := exists_lift_of_range_subset i
    (spMap (algebraMap O (FractionRing O)) ≫ a) (by
      rintro _ ⟨t, rfl⟩
      have : spMap (algebraMap O (FractionRing O)) t = (⊥ : PrimeSpectrum O) := by
        apply PrimeSpectrum.ext
        change Ideal.comap (algebraMap O (FractionRing O)) t.asIdeal = ⊥
        rw [@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime]
        exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
      rw [Scheme.Hom.comp_apply, this]
      exact h₀ ▸ hξ')
  exact .inr ⟨O, inferInstance, inferInstance, inferInstance, a, c, hc, h₁⟩

/- English proof (translation)
Use `GlobalTheory.finite_torsion_semiAbelian Ω _ (IsSemiAbelian.pullback t G hG) n hn` as an intermediate fact. Set `e` to `TorsionLift.ptsEquiv t G (𝟙_ (Over (Sp Ω))) t (Category.id_comp _)`. Use `Finite.of_injective (β := {x : 𝟙_ (Over (Sp Ω)) ⟶ (Over.pullback t).obj G // x ^ n = 1}) (fun x ↦ ⟨e.symm x.1, (map_pow e.symm x.1 n).symm.trans ((congrArg e.symm x.2).trans (map_one e.symm))⟩) fun a b h ↦ ?_` and prove the remaining obligations. Conclude with `Subtype.ext (e.symm.injective (congrArg Subtype.val h))`.
-/
theorem finite_torsion_points {X : Scheme.{0}} {G : Over X} [GrpObj G] (hG : IsSemiAbelian G)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ X) {n : ℕ} (hn : 0 < n) :
    Finite {x : Over.mk t ⟶ G // x ^ n = 1} := by
  have := GlobalTheory.finite_torsion_semiAbelian Ω _ (IsSemiAbelian.pullback t G hG) n hn
  let e := TorsionLift.ptsEquiv t G (𝟙_ (Over (Sp Ω))) t (Category.id_comp _)
  refine Finite.of_injective
    (β := {x : 𝟙_ (Over (Sp Ω)) ⟶ (Over.pullback t).obj G // x ^ n = 1})
    (fun x ↦ ⟨e.symm x.1, (map_pow e.symm x.1 n).symm.trans
      ((congrArg e.symm x.2).trans (map_one e.symm))⟩) fun a b h ↦ ?_
  exact Subtype.ext (e.symm.injective (congrArg Subtype.val h))

/- English proof (translation)
Establish `: JacobsonSpace Γ.left` using `jacobsonSpace_of_locallyOfFiniteType_int (p.left ≫ G.hom ≫ z)`. Establish `: JacobsonSpace G.left` using `jacobsonSpace_of_locallyOfFiniteType_int (G.hom ≫ z)`. Use `locallyQuasiFinite_of_finite_fibres_closedPoints p.left fun w hw ↦ ?_` and prove the remaining obligations. Establish `hσ : IsClosed ({p.left w} : Set G.left)` using `p.left.closePoints_subset_preimage_closedPoints hw`. Generalize the expression as in `p.left w = σ at hσ`.

Establish `: Finite (G.left.residueField σ)` using `(jacobson_closedPoints_tools_int G.left (G.hom ≫ z)).2.1 σ hσ`. Set `t₀ : Sp (G.left.residueField σ) ⟶ X` to `G.left.fromSpecResidueField σ ≫ G.hom`. Use `SemiAbTorsion.finite_points_over z G (G.left.residueField σ) t₀` as an intermediate fact. Set `x₀ : Over.mk t₀ ⟶ G` to `Over.homMk (G.left.fromSpecResidueField σ) rfl`. Establish `hn : 0 < Nat.card (Over.mk t₀ ⟶ G)` using `Nat.card_pos`.

Establish `hx₀ : x₀ ^ Nat.card (Over.mk t₀ ⟶ G) = 1` using `pow_card_eq_one'`. Generalize the expression as in `Nat.card (Over.mk t₀ ⟶ G) = n at hn hx₀`. Set `Ω` to `AlgebraicClosure (G.left.residueField σ)`. Set `r : Sp Ω ⟶ Sp (G.left.residueField σ)` to `spMap (algebraMap (G.left.residueField σ) Ω)`. Set `y : Sp Ω ⟶ G.left` to `r ≫ G.left.fromSpecResidueField σ`.

Establish `hy : σ ∈ Set.range y` using `⟨default, (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply σ _)⟩`. Set `r' : Over.mk (y ≫ G.hom) ⟶ Over.mk t₀` to `Over.homMk r (Category.assoc _ _ _).symm`. Use `finite_torsion_points hG' (y ≫ G.hom) hn` as an intermediate fact. Use `(finite_preimage_of_finite_lifts p.left y ?_).subset (Set.preimage_mono (Set.singleton_subset_iff.mpr hy))` and prove the remaining obligations. Set `l : {x : Sp Ω ⟶ Γ.left // x ≫ p.left = y} → (Over.mk (y ≫ G.hom) ⟶ Γ)` to `fun x ↦ Over.homMk x.1 (by`.

Express the relevant statement in the definitionally equal form `x.1 ≫ Γ.hom = y ≫ G.hom`. Rewrite using `[← Over.w p, ← Category.assoc, x.2])`. Establish `hl (x) : (l x ≫ q) ^ n = 1`. Establish `e : l x ≫ p = r' ≫ x₀` using `Over.OverMorphism.ext x.2`. Establish `h₁ : l x ≫ p ^ n = l x ≫ (1 : Γ ⟶ G)`.

Rewrite using `[SemiAbTorsion.comp_pow_points, e, ← SemiAbTorsion.comp_pow_points, hx₀, MonObj.comp_one, MonObj.comp_one]`. Establish `h₂ : l x ≫ q ^ n = l x ≫ (1 : Γ ⟶ G')` using `Over.OverMorphism.ext (key Ω x.1 n (congrArg CommaMorphism.left h₁))`. Rewrite `h₂` using `[SemiAbTorsion.comp_pow_points, MonObj.comp_one]`. Then use the resulting hypothesis. Use `Finite.of_injective (β := {x : Over.mk (y ≫ G.hom) ⟶ G' // x ^ n = 1}) (fun x ↦ ⟨l x ≫ q, hl x⟩) fun a b h ↦ Subtype.ext (hext _ _ (a.2.trans b.2.symm) ?_)` and prove the remaining obligations. Conclude with `congrArg (fun u ↦ u.1.left) h`.
-/
theorem locallyQuasiFinite_of_torsion {X : Scheme.{0}} (z : X ⟶ Sp ℤ) [LocallyOfFiniteType z]
    {G G' Γ : Over X} [GrpObj G] [GrpObj G'] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (hG' : IsSemiAbelian G') (p : Γ ⟶ G) (q : Γ ⟶ G') [LocallyOfFiniteType p.left]
    (hext : ∀ {T : Scheme.{0}} (a b : T ⟶ Γ.left), a ≫ p.left = b ≫ p.left →
      a ≫ q.left = b ≫ q.left → a = b)
    (key : ∀ (k : Type) [Field k] (c : Sp k ⟶ Γ.left) (n : ℕ),
      c ≫ (p ^ n).left = c ≫ (1 : Γ ⟶ G).left → c ≫ (q ^ n).left = c ≫ (1 : Γ ⟶ G').left) :
    LocallyQuasiFinite p.left := by
  have : JacobsonSpace Γ.left := jacobsonSpace_of_locallyOfFiniteType_int (p.left ≫ G.hom ≫ z)
  have : JacobsonSpace G.left := jacobsonSpace_of_locallyOfFiniteType_int (G.hom ≫ z)
  refine locallyQuasiFinite_of_finite_fibres_closedPoints p.left fun w hw ↦ ?_
  have hσ : IsClosed ({p.left w} : Set G.left) := p.left.closePoints_subset_preimage_closedPoints hw
  generalize p.left w = σ at hσ
  have : Finite (G.left.residueField σ) :=
    (jacobson_closedPoints_tools_int G.left (G.hom ≫ z)).2.1 σ hσ
  let t₀ : Sp (G.left.residueField σ) ⟶ X := G.left.fromSpecResidueField σ ≫ G.hom
  have := SemiAbTorsion.finite_points_over z G (G.left.residueField σ) t₀
  let x₀ : Over.mk t₀ ⟶ G := Over.homMk (G.left.fromSpecResidueField σ) rfl
  have hn : 0 < Nat.card (Over.mk t₀ ⟶ G) := Nat.card_pos
  have hx₀ : x₀ ^ Nat.card (Over.mk t₀ ⟶ G) = 1 := pow_card_eq_one'
  generalize Nat.card (Over.mk t₀ ⟶ G) = n at hn hx₀
  let Ω := AlgebraicClosure (G.left.residueField σ)
  let r : Sp Ω ⟶ Sp (G.left.residueField σ) := spMap (algebraMap (G.left.residueField σ) Ω)
  let y : Sp Ω ⟶ G.left := r ≫ G.left.fromSpecResidueField σ
  have hy : σ ∈ Set.range y :=
    ⟨default, (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply σ _)⟩
  let r' : Over.mk (y ≫ G.hom) ⟶ Over.mk t₀ := Over.homMk r (Category.assoc _ _ _).symm
  have := finite_torsion_points hG' (y ≫ G.hom) hn
  refine (finite_preimage_of_finite_lifts p.left y ?_).subset
    (Set.preimage_mono (Set.singleton_subset_iff.mpr hy))
  let l : {x : Sp Ω ⟶ Γ.left // x ≫ p.left = y} → (Over.mk (y ≫ G.hom) ⟶ Γ) := fun x ↦
    Over.homMk x.1 (by
      change x.1 ≫ Γ.hom = y ≫ G.hom
      rw [← Over.w p, ← Category.assoc, x.2])
  have hl (x) : (l x ≫ q) ^ n = 1 := by
    have e : l x ≫ p = r' ≫ x₀ := Over.OverMorphism.ext x.2
    have h₁ : l x ≫ p ^ n = l x ≫ (1 : Γ ⟶ G) := by
      rw [SemiAbTorsion.comp_pow_points, e, ← SemiAbTorsion.comp_pow_points, hx₀, MonObj.comp_one,
        MonObj.comp_one]
    have h₂ : l x ≫ q ^ n = l x ≫ (1 : Γ ⟶ G') :=
      Over.OverMorphism.ext (key Ω x.1 n (congrArg CommaMorphism.left h₁))
    rwa [SemiAbTorsion.comp_pow_points, MonObj.comp_one] at h₂
  refine Finite.of_injective (β := {x : Over.mk (y ≫ G.hom) ⟶ G' // x ^ n = 1})
    (fun x ↦ ⟨l x ≫ q, hl x⟩) fun a b h ↦ Subtype.ext (hext _ _ (a.2.trans b.2.symm) ?_)
  exact congrArg (fun u ↦ u.1.left) h

end GlobalTheory.HomExt

open GlobalTheory GlobalTheory.HomExt in

/- English proof (translation)
Introduce and unpack `H X U j ⟨hX, z, _, -⟩ _ _ _ _ G G' _ _ hG hG' f hf`. Use `hG.smooth` as an intermediate fact. Use `hG'.smooth` as an intermediate fact. Use `hG.quasiCompact` as an intermediate fact. Use `hG'.quasiCompact` as an intermediate fact.

Use `hG'.separated` as an intermediate fact. Establish `: GlobalTheory.IsNormalScheme X` using `(GlobalTheory.isNormalScheme_iff X).mpr hX`. Establish `: GlobalTheory.IsNormalScheme G.left` using `(GlobalTheory.isNormalScheme_iff _).mpr (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth G.hom hX)`. Establish `: IsSchemeTheoreticallyDominant j` using `IsSchemeTheoreticallyDominant.of_isDominant j`. Set `u : pullback G.hom j ⟶ G.left` to `pullback.fst G.hom j`.

Set `φ : pullback G.hom j ⟶ G'.left` to `f.left ≫ pullback.fst G'.hom j`. Establish `hw : f.left ≫ pullback.snd G'.hom j = pullback.snd G.hom j` using `Over.w f`. Establish `huφ : u ≫ G.hom = φ ≫ G'.hom`. Rewrite using `[Category.assoc, pullback.condition, pullback.condition, reassoc_of% hw]`. Establish `: IsDominant u` using `isDominant_pullback_fst_of_isOpenMap j G.hom G.hom.isOpenMap`.

Establish `: IsPreimmersion u` using `inferInstanceAs (IsPreimmersion (pullback.fst G.hom j))`. Establish `: Flat u` using `inferInstanceAs (Flat (pullback.fst G.hom j))`. Establish `: QuasiCompact u` using `inferInstanceAs (QuasiCompact (pullback.fst G.hom j))`. Establish `hus` using `isIso_stalkMap_of_flat_of_surjectiveOnStalks u`. Establish `: GlobalTheory.IsNormalScheme (pullback G.hom j)` using `GlobalTheory.IsNormalScheme.of_isIso_stalkMap u`.

Set `Γ` to `graphClosure G.hom G'.hom u φ huφ`. Set `p : Γ ⟶ G.left` to `graphClosure.fst G.hom G'.hom u φ huφ`. Set `q : Γ ⟶ G'.left` to `graphClosure.snd G.hom G'.hom u φ huφ`. Set `i : pullback G.hom j ⟶ Γ` to `graphClosure.incl G.hom G'.hom u φ huφ`. Establish `hip : i ≫ p = u` using `graphClosure.incl_fst ..`.

Establish `hiq : i ≫ q = φ` using `graphClosure.incl_snd ..`. Establish `hpq : p ≫ G.hom = q ≫ G'.hom` using `graphClosure.condition ..`. Establish `hpb` using `graphClosure.isPullback_incl G.hom G'.hom u φ huφ`. Establish `: IsPreimmersion i` using `MorphismProperty.of_isPullback hpb ‹IsPreimmersion u›`. Establish `: Flat i` using `MorphismProperty.of_isPullback hpb ‹Flat u›`.

Establish `: QuasiCompact i` using `graphClosure.quasiCompact_incl ..`. Establish `: IsSchemeTheoreticallyDominant i` using `graphClosure.schemeDominant_incl ..`. Establish `: IsDominant i` using `inferInstance`. Establish `: IsReduced Γ` using `graphClosure.isReduced ..`. Establish `: LocallyOfFiniteType p` using `graphClosure.locallyOfFiniteType_fst ..`.

Establish `: QuasiCompact p` using `graphClosure.quasiCompact_fst ..`. Establish `: IsSeparated p` using `graphClosure.isSeparated_fst ..`. Establish `: IsLocallyNoetherian G.left` using `LocallyOfFiniteType.isLocallyNoetherian (G.hom ≫ z)`. Establish `: IsLocallyNoetherian Γ` using `LocallyOfFiniteType.isLocallyNoetherian p`. Establish `: Surjective p`.

Use `⟨fun σ ↦ ?_⟩` and prove the remaining obligations. Break down `mem_range_or_exists_dvr u σ with ⟨w, rfl⟩ | ⟨T, _, _, _, a, c, hc, rfl⟩` into its components or cases. Conclude with `⟨i w, by rw [← Scheme.Hom.comp_apply, hip]⟩`. Take `⟨F, s, -, -, hs₂, hs⟩` from `exists_hom_along_dvr H j hG hG' f T _ a c hc`. Use `schemeTheoreticallyDominant_fractionField T (FractionRing T)` as an intermediate fact.

Establish `hF : F.left ≫ pullback.snd G'.hom (a ≫ G.hom) = pullback.snd G.hom (a ≫ G.hom)` using `Over.w F`. Take `⟨l, ⟨hl, -⟩, -⟩` from `graphClosure.existsUnique_lift G.hom G'.hom u φ huφ a (s ≫ F.left ≫ pullback.fst G'.hom (a ≫ G.hom)) (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hF, reassoc_of% hs₂]) (spMap (algebraMap T (FractionRing T))) c hc.symm hs`. Conclude with `⟨l (IsLocalRing.closedPoint T), by rw [← hl]; rfl⟩`. Set `Γ' : Over X` to `Over.mk (p ≫ G.hom)`. Set `p' : Γ' ⟶ G` to `Over.homMk p rfl`.

Set `q' : Γ' ⟶ G'` to `Over.homMk q hpq.symm`. Establish `: LocallyOfFiniteType p'.left` using `‹LocallyOfFiniteType p›`. Establish `: LocallyQuasiFinite p`. Use `locallyQuasiFinite_of_torsion z hG' p' q' (fun a b ↦ graphClosure.hom_ext G.hom G'.hom u φ huφ) fun k _ x n hx ↦ ?_` and prove the remaining obligations. Break down `mem_range_or_exists_dvr i (x default) with hw | ⟨T, _, _, _, a, c, hc, ha⟩` into its components or cases.

Take `⟨c, rfl⟩` from `exists_lift_of_range_subset i x (by`. Introduce and unpack `_ ⟨t, rfl⟩`. Rewrite using `[Subsingleton.elim t default])` and apply the resulting hypothesis. Conclude with `comp_pow_eq_one_of_pullback_hom j f p' q' _ c (by rw [Category.assoc]; exact congrArg (c ≫ ·) hip.symm) (by rw [Category.assoc]; exact congrArg (c ≫ ·) hiq.symm) n hx`. Take `⟨F, s, _, hs₁, hs₂, hs⟩` from `exists_hom_along_dvr H j hG hG' f T _ (a ≫ p) c (by rw [← reassoc_of% hc, hip])`.

Use `schemeTheoreticallyDominant_fractionField T (FractionRing T)` as an intermediate fact. Establish `hF : F.left ≫ pullback.snd G'.hom ((a ≫ p) ≫ G.hom) = pullback.snd G.hom ((a ≫ p) ≫ G.hom)` using `Over.w F`. Establish `hb : s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom) = a ≫ q`. Use `over_ext_of_schemeTheoreticallyDominant (Y := Over.mk ((a ≫ p) ≫ G.hom)) (X := G') (spMap (algebraMap T (FractionRing T))) (a := Over.homMk (s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom)) (by` as an intermediate fact. Express the relevant statement in the definitionally equal form `(s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom)) ≫ G'.hom = (a ≫ p) ≫ G.hom`.

Rewrite using `[Category.assoc s, Category.assoc F.left, pullback.condition, reassoc_of% hF, reassoc_of% hs₂]))`. Use the proof step `(b := Over.homMk (a ≫ q) (by`. Express the relevant statement in the definitionally equal form `(a ≫ q) ≫ G'.hom = (a ≫ p) ≫ G.hom`. Rewrite using `[Category.assoc, Category.assoc, hpq]))`. Use the proof step `(hs.trans (by`.

Express the relevant statement in the definitionally equal form `_ = spMap (algebraMap T (FractionRing T)) ≫ a ≫ q`. Rewrite using `[← reassoc_of% hc, hiq]))`. Conclude with `congrArg CommaMorphism.left this`. Set `r : Sp (IsLocalRing.ResidueField T) ⟶ Sp T` to `spMap (IsLocalRing.residue T)`. Establish `hr : x default ∈ Set.range (r ≫ a)`.

Use `⟨IsLocalRing.closedPoint _, ?_⟩` and prove the remaining obligations. Conclude with `(Scheme.Hom.comp_apply r a _).trans ((congrArg a (IsLocalRing.comap_closedPoint (IsLocalRing.residue T))).trans ha)`. Rewrite `hx`, the goal using `[field_point_comp_eq_iff _ _ x _ ⟨default, rfl⟩, ← field_point_comp_eq_iff (Z := Γ'.left) _ _ (r ≫ a) _ hr]`. Conclude with `comp_pow_eq_one_of_pullback_hom _ F p' q' (r ≫ a) (r ≫ s) (by rw [Category.assoc, hs₁, Category.assoc]; rfl) (by rw [Category.assoc, hb, Category.assoc]; rfl) n hx`. Establish `: IsIso p`.

Establish `: IsPreimmersion (i ≫ p)` using `by rwa [hip]`. Establish `: Flat (i ≫ p)` using `by rwa [hip]`. Establish `: IsDominant (i ≫ p)` using `by rwa [hip]`. Establish `: QuasiCompact (i ≫ p)` using `by rwa [hip]`. Conclude with `isIso_of_densePart i p`.

Take `⟨ψ, hψ, huψ⟩` from `graphClosure.exists_extension_of_isIso_fst G.hom G'.hom u φ huφ`. Set `F : G ⟶ G'` to `Over.homMk ψ hψ.symm`. Establish `hF : (Over.pullback j).map F = f` using `by ext1`. Apply `pullback.hom_ext` to reduce the goal to its premises. Conclude with `(pullback.lift_fst _ _ _).trans huψ`.

Conclude with `(Over.w _).trans hw.symm`. Use `⟨F, ⟨?_, hF⟩, fun F' hF' ↦ pullback_map_injective_of_flat j (hF'.2.trans hF.symm)⟩` and prove the remaining obligations. Establish `: IsMonHom ((Over.pullback j).map F)` using `hF ▸ hf`. Conclude with `isMonHom_of_pullback_of_flat j F`.
-/
theorem GlobalTheory.existsUnique_hom_extension_semiAbelian_normal :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (X U : Scheme.{0}) (j : U ⟶ X), (ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (G G' : Over X) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f := by
  rintro H X U j ⟨hX, z, _, -⟩ _ _ _ _ G G' _ _ hG hG' f hf
  have := hG.smooth
  have := hG'.smooth
  have := hG.quasiCompact
  have := hG'.quasiCompact
  have := hG'.separated
  have : GlobalTheory.IsNormalScheme X := (GlobalTheory.isNormalScheme_iff X).mpr hX
  have : GlobalTheory.IsNormalScheme G.left := (GlobalTheory.isNormalScheme_iff _).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth G.hom hX)
  have : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isDominant j
  let u : pullback G.hom j ⟶ G.left := pullback.fst G.hom j
  let φ : pullback G.hom j ⟶ G'.left := f.left ≫ pullback.fst G'.hom j
  have hw : f.left ≫ pullback.snd G'.hom j = pullback.snd G.hom j := Over.w f
  have huφ : u ≫ G.hom = φ ≫ G'.hom := by
    rw [Category.assoc, pullback.condition, pullback.condition, reassoc_of% hw]
  have : IsDominant u := isDominant_pullback_fst_of_isOpenMap j G.hom G.hom.isOpenMap
  have : IsPreimmersion u := inferInstanceAs (IsPreimmersion (pullback.fst G.hom j))
  have : Flat u := inferInstanceAs (Flat (pullback.fst G.hom j))
  have : QuasiCompact u := inferInstanceAs (QuasiCompact (pullback.fst G.hom j))
  have hus := isIso_stalkMap_of_flat_of_surjectiveOnStalks u
  have : GlobalTheory.IsNormalScheme (pullback G.hom j) := GlobalTheory.IsNormalScheme.of_isIso_stalkMap u
  let Γ := graphClosure G.hom G'.hom u φ huφ
  let p : Γ ⟶ G.left := graphClosure.fst G.hom G'.hom u φ huφ
  let q : Γ ⟶ G'.left := graphClosure.snd G.hom G'.hom u φ huφ
  let i : pullback G.hom j ⟶ Γ := graphClosure.incl G.hom G'.hom u φ huφ
  have hip : i ≫ p = u := graphClosure.incl_fst ..
  have hiq : i ≫ q = φ := graphClosure.incl_snd ..
  have hpq : p ≫ G.hom = q ≫ G'.hom := graphClosure.condition ..
  have hpb := graphClosure.isPullback_incl G.hom G'.hom u φ huφ
  have : IsPreimmersion i := MorphismProperty.of_isPullback hpb ‹IsPreimmersion u›
  have : Flat i := MorphismProperty.of_isPullback hpb ‹Flat u›
  have : QuasiCompact i := graphClosure.quasiCompact_incl ..
  have : IsSchemeTheoreticallyDominant i := graphClosure.schemeDominant_incl ..
  have : IsDominant i := inferInstance
  have : IsReduced Γ := graphClosure.isReduced ..
  have : LocallyOfFiniteType p := graphClosure.locallyOfFiniteType_fst ..
  have : QuasiCompact p := graphClosure.quasiCompact_fst ..
  have : IsSeparated p := graphClosure.isSeparated_fst ..
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian (G.hom ≫ z)
  have : IsLocallyNoetherian Γ := LocallyOfFiniteType.isLocallyNoetherian p
  have : Surjective p := by
    refine ⟨fun σ ↦ ?_⟩
    rcases mem_range_or_exists_dvr u σ with ⟨w, rfl⟩ | ⟨T, _, _, _, a, c, hc, rfl⟩
    · exact ⟨i w, by rw [← Scheme.Hom.comp_apply, hip]⟩
    obtain ⟨F, s, -, -, hs₂, hs⟩ := exists_hom_along_dvr H j hG hG' f T _ a c hc
    have := schemeTheoreticallyDominant_fractionField T (FractionRing T)
    have hF : F.left ≫ pullback.snd G'.hom (a ≫ G.hom) = pullback.snd G.hom (a ≫ G.hom) := Over.w F
    obtain ⟨l, ⟨hl, -⟩, -⟩ := graphClosure.existsUnique_lift G.hom G'.hom u φ huφ a
      (s ≫ F.left ≫ pullback.fst G'.hom (a ≫ G.hom))
      (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hF, reassoc_of% hs₂])
      (spMap (algebraMap T (FractionRing T))) c hc.symm hs
    exact ⟨l (IsLocalRing.closedPoint T), by rw [← hl]; rfl⟩
  let Γ' : Over X := Over.mk (p ≫ G.hom)
  let p' : Γ' ⟶ G := Over.homMk p rfl
  let q' : Γ' ⟶ G' := Over.homMk q hpq.symm
  have : LocallyOfFiniteType p'.left := ‹LocallyOfFiniteType p›
  have : LocallyQuasiFinite p := by
    refine locallyQuasiFinite_of_torsion z hG' p' q'
      (fun a b ↦ graphClosure.hom_ext G.hom G'.hom u φ huφ) fun k _ x n hx ↦ ?_
    rcases mem_range_or_exists_dvr i (x default) with hw | ⟨T, _, _, _, a, c, hc, ha⟩
    · obtain ⟨c, rfl⟩ := exists_lift_of_range_subset i x (by
        rintro _ ⟨t, rfl⟩
        rwa [Subsingleton.elim t default])
      exact comp_pow_eq_one_of_pullback_hom j f p' q' _ c
        (by rw [Category.assoc]; exact congrArg (c ≫ ·) hip.symm)
        (by rw [Category.assoc]; exact congrArg (c ≫ ·) hiq.symm) n hx
    obtain ⟨F, s, _, hs₁, hs₂, hs⟩ := exists_hom_along_dvr H j hG hG' f T _ (a ≫ p) c
      (by rw [← reassoc_of% hc, hip])
    have := schemeTheoreticallyDominant_fractionField T (FractionRing T)
    have hF : F.left ≫ pullback.snd G'.hom ((a ≫ p) ≫ G.hom) =
      pullback.snd G.hom ((a ≫ p) ≫ G.hom) := Over.w F
    have hb : s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom) = a ≫ q := by
      have := over_ext_of_schemeTheoreticallyDominant (Y := Over.mk ((a ≫ p) ≫ G.hom)) (X := G')
        (spMap (algebraMap T (FractionRing T)))
        (a := Over.homMk (s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom)) (by
          change (s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom)) ≫ G'.hom = (a ≫ p) ≫ G.hom
          rw [Category.assoc s, Category.assoc F.left, pullback.condition, reassoc_of% hF,
            reassoc_of% hs₂]))
        (b := Over.homMk (a ≫ q) (by
          change (a ≫ q) ≫ G'.hom = (a ≫ p) ≫ G.hom
          rw [Category.assoc, Category.assoc, hpq]))
        (hs.trans (by
          change _ = spMap (algebraMap T (FractionRing T)) ≫ a ≫ q
          rw [← reassoc_of% hc, hiq]))
      exact congrArg CommaMorphism.left this
    let r : Sp (IsLocalRing.ResidueField T) ⟶ Sp T := spMap (IsLocalRing.residue T)
    have hr : x default ∈ Set.range (r ≫ a) := by
      refine ⟨IsLocalRing.closedPoint _, ?_⟩
      exact (Scheme.Hom.comp_apply r a _).trans
        ((congrArg a (IsLocalRing.comap_closedPoint (IsLocalRing.residue T))).trans ha)
    rw [field_point_comp_eq_iff _ _ x _ ⟨default, rfl⟩,
      ← field_point_comp_eq_iff (Z := Γ'.left) _ _ (r ≫ a) _ hr] at hx ⊢
    exact comp_pow_eq_one_of_pullback_hom _ F p' q' (r ≫ a) (r ≫ s)
      (by rw [Category.assoc, hs₁, Category.assoc]; rfl)
      (by rw [Category.assoc, hb, Category.assoc]; rfl) n hx
  have : IsIso p := by
    have : IsPreimmersion (i ≫ p) := by rwa [hip]
    have : Flat (i ≫ p) := by rwa [hip]
    have : IsDominant (i ≫ p) := by rwa [hip]
    have : QuasiCompact (i ≫ p) := by rwa [hip]
    exact isIso_of_densePart i p
  obtain ⟨ψ, hψ, huψ⟩ := graphClosure.exists_extension_of_isIso_fst G.hom G'.hom u φ huφ
  let F : G ⟶ G' := Over.homMk ψ hψ.symm
  have hF : (Over.pullback j).map F = f := by
    ext1
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans huψ
    · exact (Over.w _).trans hw.symm
  refine ⟨F, ⟨?_, hF⟩, fun F' hF' ↦ pullback_map_injective_of_flat j (hF'.2.trans hF.symm)⟩
  have : IsMonHom ((Over.pullback j).map F) := hF ▸ hf
  exact isMonHom_of_pullback_of_flat j F
