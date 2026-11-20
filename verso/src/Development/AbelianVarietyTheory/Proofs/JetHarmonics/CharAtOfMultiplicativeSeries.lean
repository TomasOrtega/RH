import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharacterOnPoints
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueJet
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FiniteAugmentedConnectedPartLocalisation
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualNumberValueToJet
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfFiniteBasis
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MapDofIterate
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RepJetAugCompTrunc
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ToJetOneEqSum
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RelatedMap

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SeriesCharacter

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FamGerm GlobalTheory.HodgeTateStep GlobalTheory.KernelNoTorsion GlobalTheory.TorsionCharacter
open GlobalTheory.SeriesValue
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev Dof)

/- English proof (translation)
Establish `hpow : ∀ g c (n : ℕ), Rel g c → Rel (g ^ n) (c ^ n)` using `fun g c n h => by`. Proceed by induction on `n with`. Consider the case `zero => simpa using h1`. Consider the case `succ n ih => rw [pow_succ, pow_succ]`. Conclude with `hmul _ _ _ _ ih h`.

Set `H : Subgroup N` to `{ carrier := {g | g ^ p = 1 ∧ ∃ c, Rel g c} mul_mem' := by`. Introduce and unpack `a b ⟨ha, c, hc⟩ ⟨hb, c', hc'⟩`. Conclude with `⟨by rw [mul_pow, ha, hb, _root_.mul_one], _, hmul _ _ _ _ hc hc'⟩`. Use the proof step `one_mem' := ⟨one_pow _, 1, h1⟩`. Use the proof step `inv_mem' := by`.

Introduce and unpack `a ⟨ha, c, hc⟩`. Establish `: a⁻¹ = a ^ (p - 1)`. Rewrite using `[inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hp), ha]`. Conclude with `⟨by rw [inv_pow, ha, inv_one], _, this ▸ hpow _ _ _ hc⟩ }`. Use `choose c hc using fun h : H => h.2.2`.

Establish `hc0 : ∀ h, c h ≠ 0` using `fun h h0 => by`. Use `hpow _ _ p (hc h)` as an intermediate fact. Rewrite `this` using `[h.2.1, h0, zero_pow hp]`. Conclude with `zero_ne_one (huniq _ _ _ this h1)`. Set `χ : H →* Fˣ` to `MonoidHom.mk' (fun h => Units.mk0 (c h) (hc0 h)) fun a b => Units.ext (huniq _ _ _ (hc (a * b)) (hmul _ _ _ _ (hc a) (hc b)))`.

Take `⟨κ, hκ⟩` from `exists_extend_character (Φ.comp H.subtype) (hΦ.comp Subtype.val_injective) χ`. Use `⟨κ, fun g k hg hk => ?_⟩` and prove the remaining obligations. Rewrite using `[show κ (Φ g) = χ ⟨g, hg, k, hk⟩ from hκ ⟨g, hg, k, hk⟩]`. Conclude with `huniq _ _ _ (hc ⟨g, hg, k, hk⟩) hk`.
-/
theorem exists_character_of_rel {N M F : Type} [CommGroup N] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : N →* M) (hΦ : Function.Injective Φ) (Rel : N → F → Prop) (h1 : Rel 1 1)
    (hmul : ∀ g g' c c', Rel g c → Rel g' c' → Rel (g * g') (c * c'))
    (huniq : ∀ g c c', Rel g c → Rel g c' → c = c') {p : ℕ} (hp : p ≠ 0) :
    ∃ κ : M →* Fˣ, ∀ g c, g ^ p = 1 → Rel g c → (κ (Φ g) : F) = c := by
  have hpow : ∀ g c (n : ℕ), Rel g c → Rel (g ^ n) (c ^ n) := fun g c n h => by
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ, pow_succ]; exact hmul _ _ _ _ ih h
  let H : Subgroup N :=
    { carrier := {g | g ^ p = 1 ∧ ∃ c, Rel g c}
      mul_mem' := by
        rintro a b ⟨ha, c, hc⟩ ⟨hb, c', hc'⟩
        exact ⟨by rw [mul_pow, ha, hb, _root_.mul_one], _, hmul _ _ _ _ hc hc'⟩
      one_mem' := ⟨one_pow _, 1, h1⟩
      inv_mem' := by
        rintro a ⟨ha, c, hc⟩
        have : a⁻¹ = a ^ (p - 1) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hp), ha]
        exact ⟨by rw [inv_pow, ha, inv_one], _, this ▸ hpow _ _ _ hc⟩ }
  choose c hc using fun h : H => h.2.2
  have hc0 : ∀ h, c h ≠ 0 := fun h h0 => by
    have := hpow _ _ p (hc h)
    rw [h.2.1, h0, zero_pow hp] at this
    exact zero_ne_one (huniq _ _ _ this h1)
  let χ : H →* Fˣ := MonoidHom.mk' (fun h => Units.mk0 (c h) (hc0 h)) fun a b =>
    Units.ext (huniq _ _ _ (hc (a * b)) (hmul _ _ _ _ (hc a) (hc b)))
  obtain ⟨κ, hκ⟩ := exists_extend_character (Φ.comp H.subtype) (hΦ.comp Subtype.val_injective) χ
  refine ⟨κ, fun g k hg hk => ?_⟩
  rw [show κ (Φ g) = χ ⟨g, hg, k, hk⟩ from hκ ⟨g, hg, k, hk⟩]
  exact huniq _ _ _ (hc ⟨g, hg, k, hk⟩) hk

/- English proof (translation)
Use `congrArg CommRingCat.Hom.hom (Spec.map_injective (congrArg (·.left) h))` as an intermediate fact. Conclude with `AlgHom.ext fun a => RingHom.congr_fun this a`.
-/
theorem ptMap_injective {O A R : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [Algebra O R]
    {φ ψ : A →ₐ[O] R} (h : ptMap φ = ptMap ψ) : φ = ψ := by
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective (congrArg (·.left) h))
  exact AlgHom.ext fun a => RingHom.congr_fun this a

/- English proof (translation)
Establish `h` using `(ChartBaseChange.fnVal_spec θ (𝟙 _) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom k) le_rfl).2`. Rewrite `h` using `[Category.comp_id]`. Rewrite using `[h, JetSer.fnVal, dif_pos (show ⊤ ≤ (𝟙 (Spec (CommRingCat.of A))) ⁻¹ᵁ ⊤ from le_rfl)]`. Use `congr 1`. Establish `e : (𝟙 (Spec (CommRingCat.of A)) : _ ⟶ _).appLE ⊤ ⊤ le_rfl = 𝟙 _` using `(Scheme.Hom.app_eq_appLE (𝟙 (Spec (CommRingCat.of A))) (U := ⊤)).symm.trans (Scheme.Hom.id_app _)`.

Use `erw [e]`. Conclude with `(Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply k`.
-/
theorem fnVal_spec_top {A R : Type} [CommRing A] [CommRing R] (θ : A →+* R) (k : A) :
    JetSer.fnVal (Spec.map (CommRingCat.ofHom θ)) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom k) = θ k := by
  have h := (ChartBaseChange.fnVal_spec θ (𝟙 _) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom k) le_rfl).2
  rw [Category.comp_id] at h
  rw [h, JetSer.fnVal, dif_pos (show ⊤ ≤ (𝟙 (Spec (CommRingCat.of A))) ⁻¹ᵁ ⊤ from le_rfl)]
  congr 1
  have e : (𝟙 (Spec (CommRingCat.of A)) : _ ⟶ _).appLE ⊤ ⊤ le_rfl = 𝟙 _ :=
    (Scheme.Hom.app_eq_appLE (𝟙 (Spec (CommRingCat.of A))) (U := ⊤)).symm.trans (Scheme.Hom.id_app _)
  erw [e]
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply k

/- English proof (translation)
Take `⟨A, _, _, hfin, hfree, ⟨i⟩⟩` from `exists_finite_free (torsion Gt N)`. Take `⟨aug, haug⟩` from `exists_ptMap (torsionLift (1 : specO W W ⟶ Gt) (one_pow N) ≫ i.inv)`. Establish `haug' : ptMap aug ≫ i.hom ≫ torsion.ι Gt N = 1`. Rewrite using `[← haug, Category.assoc, Iso.inv_hom_id_assoc, torsionLift_ι]`. Take `⟨s, hs, ⟨m, hm⟩, hu⟩` from `GlobalTheory.finite_augmented_connected_part_localisation F W p hp A aug`.

Set `loc` to `IsScalarTower.toAlgHom W A (Localization.Away s)`. Establish `lift : ∀ (R : Type) [CommRing R] [Algebra W R] (w : A →ₐ[W] R), (∀ t ∈ RingHom.ker aug, IsNilpotent (w t)) → ∃ w' : Localization.Away s →ₐ[W] R, w'.comp loc = w` using `fun R _ _ w hw => ⟨IsLocalization.Away.liftAlgHom s (hu R w hw), AlgHom.ext fun a => IsLocalization.Away.lift_eq s (hu R w hw) a⟩`. Take `⟨aug', h'⟩` from `lift W aug fun t ht => by rw [show aug t = 0 from ht]; exact IsNilpotent.zero`. Establish `: Module.Finite W (Localization.Away s)` using `Module.Finite.of_surjective loc.toLinearMap hs`. Establish `: Module.Flat A (Localization.Away s)` using `IsLocalization.flat _ (Submonoid.powers s)`.

Establish `: Module.Flat W (Localization.Away s)` using `Module.Flat.trans W A _`. Use `⟨Localization.Away s, inferInstance, inferInstance, ptMap loc ≫ i.hom, aug', _, m, inferInstance, Module.free_of_flat_of_isLocalRing, ?_, ?_, ?_, hm, fun R _ _ w hw => ?_⟩` and prove the remaining obligations. Establish `: IsIso i.hom.left` using `inferInstanceAs (IsIso ((Over.forget _).map i.hom))`. Establish `: IsOpenImmersion (ptMap loc).left` using `inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s)))))`. Establish `: IsOpenImmersion (ptMap loc ≫ i.hom).left` using `by rw [Over.comp_left]; infer_instance`.

Establish `: IsOpenImmersion (specO W F ◁ (ptMap loc ≫ i.hom)).left`. Rewrite using `[Over.whiskerLeft_left]`. Conclude with `MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance this (by simp) (Over.w _).symm`. Conclude with `isReduced_of_isOpenImmersion (specO W F ◁ (ptMap loc ≫ i.hom)).left`. Rewrite using `[Category.assoc, ← Category.assoc (ptMap aug'), TangentPow.ptMap_comp_ptMap, h', haug']`.

Use `RingHom.ext fun b => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `hs b`. Use `show _ = Ideal.Quotient.mk _ (algebraMap W _ (aug'.comp loc a))`. Rewrite using `[h', Ideal.Quotient.eq, IsScalarTower.algebraMap_apply W A, ← map_sub]`. Use `Ideal.mem_map_of_mem _ ?_` and prove the remaining obligations.

Use `show aug _ = 0`. Rewrite using `[map_sub, AlgHom.commutes]`. Conclude with `sub_self _`. Take `⟨ψ, hψ⟩` from `exists_ptMap (w ≫ i.inv)`. Establish `e : (TrivSqZeroExt.fstHom W R R).comp ψ = (Algebra.ofId W R).comp aug`.

Apply `ptMap_injective` to reduce the goal to its premises. Rewrite using `[← cancel_mono i.hom]`. Apply `torsion_hom_ext` to reduce the goal to its premises. Rewrite using `[← TangentPow.ptMap_comp_ptMap, ← TangentPow.ptMap_comp_ptMap, ← hψ]`. Simplify using `only [Category.assoc, Iso.inv_hom_id_assoc]`.

Rewrite using `[hw, haug', MonObj.comp_one]`. Take `⟨ψ', hψ'⟩` from `lift _ ψ fun t ht => by`. Rewrite using `[TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst, show (ψ t).fst = 0 from (AlgHom.congr_fun e t).trans (by rw [AlgHom.comp_apply, show aug t = 0 from ht, map_zero])]`. Conclude with `IsNilpotent.zero`. Use `⟨ψ', ?_⟩` and prove the remaining obligations.

Rewrite using `[← Category.assoc, TangentPow.ptMap_comp_ptMap, hψ', ← hψ, Category.assoc, Iso.inv_hom_id, Category.comp_id]`.
-/
theorem exists_connected_part {F : Type} [Field F] [IsAlgClosed F] (W : ValuationSubring F) (p : W)
    (hp : ∀ a : W, ¬ IsUnit a → ∃ n : ℕ, a ^ n ∈ Ideal.span {p}) (Gt : Over (Spec (CommRingCat.of W))) [GrpObj Gt]
    [IsCommMonObj Gt] (N : ℕ) [IsFinite (torsion Gt N).hom] [Flat (torsion Gt N).hom]
    (hred : IsReduced (specO W F ⊗ torsion Gt N).left) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra W A) (X : specO W A ⟶ torsion Gt N) (aug : A →ₐ[W] W) (I : Ideal A)
      (m : ℕ), Module.Finite W A ∧ Module.Free W A ∧ IsReduced (specO W F ⊗ specO W A).left ∧
      ptMap aug ≫ X ≫ torsion.ι Gt N = 1 ∧
      Ideal.Quotient.mk I = (algebraMap W (A ⧸ I)).comp aug.toRingHom ∧ I ^ m ≤ Ideal.span {algebraMap W A p} ∧
      ∀ (R : Type) [CommRing R] [Algebra W R] (w : specO W (DualNumber R) ⟶ torsion Gt N),
        ptMap (TrivSqZeroExt.fstHom W R R) ≫ w ≫ torsion.ι Gt N = 1 → ∃ ψ : A →ₐ[W] DualNumber R, w = ptMap ψ ≫ X := by
  obtain ⟨A, _, _, hfin, hfree, ⟨i⟩⟩ := exists_finite_free (torsion Gt N)
  obtain ⟨aug, haug⟩ := exists_ptMap (torsionLift (1 : specO W W ⟶ Gt) (one_pow N) ≫ i.inv)
  have haug' : ptMap aug ≫ i.hom ≫ torsion.ι Gt N = 1 := by
    rw [← haug, Category.assoc, Iso.inv_hom_id_assoc, torsionLift_ι]
  obtain ⟨s, hs, ⟨m, hm⟩, hu⟩ := GlobalTheory.finite_augmented_connected_part_localisation F W p hp A aug
  let loc := IsScalarTower.toAlgHom W A (Localization.Away s)
  have lift : ∀ (R : Type) [CommRing R] [Algebra W R] (w : A →ₐ[W] R), (∀ t ∈ RingHom.ker aug, IsNilpotent (w t)) →
      ∃ w' : Localization.Away s →ₐ[W] R, w'.comp loc = w := fun R _ _ w hw =>
    ⟨IsLocalization.Away.liftAlgHom s (hu R w hw), AlgHom.ext fun a => IsLocalization.Away.lift_eq s (hu R w hw) a⟩
  obtain ⟨aug', h'⟩ := lift W aug fun t ht => by rw [show aug t = 0 from ht]; exact IsNilpotent.zero
  have : Module.Finite W (Localization.Away s) := Module.Finite.of_surjective loc.toLinearMap hs
  have : Module.Flat A (Localization.Away s) := IsLocalization.flat _ (Submonoid.powers s)
  have : Module.Flat W (Localization.Away s) := Module.Flat.trans W A _
  refine ⟨Localization.Away s, inferInstance, inferInstance, ptMap loc ≫ i.hom, aug', _, m, inferInstance,
    Module.free_of_flat_of_isLocalRing, ?_, ?_, ?_, hm, fun R _ _ w hw => ?_⟩
  · have : IsIso i.hom.left := inferInstanceAs (IsIso ((Over.forget _).map i.hom))
    have : IsOpenImmersion (ptMap loc).left :=
      inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s)))))
    have : IsOpenImmersion (ptMap loc ≫ i.hom).left := by rw [Over.comp_left]; infer_instance
    have : IsOpenImmersion (specO W F ◁ (ptMap loc ≫ i.hom)).left := by
      rw [Over.whiskerLeft_left]
      exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance this (by simp) (Over.w _).symm
    exact isReduced_of_isOpenImmersion (specO W F ◁ (ptMap loc ≫ i.hom)).left
  · rw [Category.assoc, ← Category.assoc (ptMap aug'), TangentPow.ptMap_comp_ptMap, h', haug']
  · refine RingHom.ext fun b => ?_
    obtain ⟨a, rfl⟩ := hs b
    show _ = Ideal.Quotient.mk _ (algebraMap W _ (aug'.comp loc a))
    rw [h', Ideal.Quotient.eq, IsScalarTower.algebraMap_apply W A, ← map_sub]
    refine Ideal.mem_map_of_mem _ ?_
    show aug _ = 0
    rw [map_sub, AlgHom.commutes]
    exact sub_self _
  · obtain ⟨ψ, hψ⟩ := exists_ptMap (w ≫ i.inv)
    have e : (TrivSqZeroExt.fstHom W R R).comp ψ = (Algebra.ofId W R).comp aug := by
      apply ptMap_injective
      rw [← cancel_mono i.hom]
      apply torsion_hom_ext
      rw [← TangentPow.ptMap_comp_ptMap, ← TangentPow.ptMap_comp_ptMap, ← hψ]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [hw, haug', MonObj.comp_one]
    obtain ⟨ψ', hψ'⟩ := lift _ ψ fun t ht => by
      rw [TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst, show (ψ t).fst = 0 from
        (AlgHom.congr_fun e t).trans (by rw [AlgHom.comp_apply, show aug t = 0 from ht, map_zero])]
      exact IsNilpotent.zero
    refine ⟨ψ', ?_⟩
    rw [← Category.assoc, TangentPow.ptMap_comp_ptMap, hψ', ← hψ, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/- English proof (translation)
Use `⟨m, fun j => φ (Chart.zR m j), ψ, hψ, ?_, rfl⟩` and prove the remaining obligations. Establish `w` using `Over.w g`. Rewrite `w` using `[hg, Category.assoc, Over.w (x m)]`. Express the relevant statement in the definitionally equal form `Spec.map _ ≫ Spec.map _ = Spec.map _ at w`. Rewrite `w` using `[← Spec.map_comp]`.

Establish `w'` using `congrArg CommRingCat.Hom.hom (Spec.map_injective w)`. Establish `: φ = ψ.toRingHom.comp (jetIn V d O m).toRingHom`. Use `Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) fun j => ?_)` and prove the remaining obligations. Use `(RingHom.congr_fun w' r).trans ?_ show _ = ψ (jetIn V d O m (algebraMap V _ r))` and prove the remaining obligations. Rewrite using `[AlgHom.commutes, IsScalarTower.algebraMap_apply V O, AlgHom.commutes]`.

Both sides reduce to the same expression. Use `show _ = ψ (jetIn V d O m (Chart.zR m j))`. Rewrite using `[jetIn_zR, hψ]`. Both sides reduce to the same expression. Rewrite using `[hg, this]`.
-/
theorem hasVal_of_ringHom {V O A : Type} [CommRing V] [CommRing O] [Algebra V O] [CommRing A] [Algebra O A]
    {G : Over (Spec (CommRingCat.of V))} {d m : ℕ} (x : JetSer.Fam G (Fin d)) (u : PS O 1 d)
    (g : specV (algebraMap V O) A ⟶ G) (φ : Chart.JetR V (Fin d) m →+* A)
    (hg : g.left = Spec.map (CommRingCat.ofHom φ) ≫ (x m).left) (ψ : Chart.JetR O (Fin 1 × Fin d) m →ₐ[O] A)
    (hψ : ∀ q, ψ (Chart.zR m q) = φ (Chart.zR m q.2)) : HasVal x u g.left (ψ (JetSer.toJet m u)) := by
  refine ⟨m, fun j => φ (Chart.zR m j), ψ, hψ, ?_, rfl⟩
  have w := Over.w g
  rw [hg, Category.assoc, Over.w (x m)] at w
  change Spec.map _ ≫ Spec.map _ = Spec.map _ at w
  rw [← Spec.map_comp] at w
  have w' := congrArg CommRingCat.Hom.hom (Spec.map_injective w)
  have : φ = ψ.toRingHom.comp (jetIn V d O m).toRingHom := by
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) fun j => ?_)
    · refine (RingHom.congr_fun w' r).trans ?_
      show _ = ψ (jetIn V d O m (algebraMap V _ r))
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply V O, AlgHom.commutes]
      rfl
    · show _ = ψ (jetIn V d O m (Chart.zR m j))
      rw [jetIn_zR, hψ]
      rfl
  rw [hg, this]

/- English proof (translation)
Apply `DualNumber.algHom_ext` to reduce the goal to its premises. Use `show dualBC _ (TrivSqZeroExt.map _ (TrivSqZeroExt.inr 1)) = algebraMap O (DualNumber R) (TrivSqZeroExt.inr 1 : DualNumber O).fst`. Rewrite using `[TrivSqZeroExt.map_inr, dualBC_inr, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, _root_.mul_one, hs, TrivSqZeroExt.fst_inr, map_zero, TrivSqZeroExt.inr_zero]`.
-/
theorem dualBC_comp_dualScale_zero {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (s : O)
    (hs : algebraMap O R s = 0) :
    (dualBC (Algebra.ofId O R)).comp (dualScale s) =
      (Algebra.ofId O (DualNumber R)).comp (TrivSqZeroExt.fstHom O O O) := by
  apply DualNumber.algHom_ext
  show dualBC _ (TrivSqZeroExt.map _ (TrivSqZeroExt.inr 1)) =
    algebraMap O (DualNumber R) (TrivSqZeroExt.inr 1 : DualNumber O).fst
  rw [TrivSqZeroExt.map_inr, dualBC_inr, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul,
    _root_.mul_one, hs, TrivSqZeroExt.fst_inr, map_zero, TrivSqZeroExt.inr_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (y : Pt1 E H V F)

/- English proof (translation)
Set `_` to `H.starRing`. Set `_ : Algebra V (TWO.Ov y.v)` to `(TWO.fO y.v y.hϖ y.hv).toAlgebra`. Take `⟨A, _, _, X₀, aug, I, m, hfin, hfree, hAred, haug, hI, hIm, hlift⟩` from `exists_connected_part (TWO.Ov y.v) p hnil Gt p hred`. Establish `hA : Admissible (TWO.fO y.v y.hϖ y.hv) A` using `Or.inl ⟨hfin, hfree⟩`. Establish `hO : Admissible (TWO.fO y.v y.hϖ y.hv) (TWO.Ov y.v)` using `Or.inl ⟨inferInstance, inferInstance⟩`.

Use `ρ.hom (b' * a')` as an intermediate fact. Use `ρ.hom a'` as an intermediate fact. Use `ρ.hom b'` as an intermediate fact. Use `ρ.hom b` as an intermediate fact. Use `y.P.U.gen_hom` as an intermediate fact.

Establish `gpG : IsGrpPullback y.P.A.A y.t.G (jK V) (y.P.U.gen.inv.left ≫ pullback.fst y.t.G.hom (jK V))`. Establish `: IsMonHom y.P.U.gen.symm.hom` using `by show IsMonHom y.P.U.gen.inv; infer_instance`. Conclude with `((isGrpPullback_of_iso y.P.U.gen.symm).comp (isGrpPullback_pullback y.t.G (jK V))).congr (Category.id_comp _) rfl`. Set `T : Over (Spec (CommRingCat.of V))` to `Over.mk ((TFK (R := V) F).hom ≫ jK V)`. Set `r : T ⟶ specV (TWO.fO y.v y.hϖ y.hv) (TWO.Ov y.v)` to `Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (TWO.Ov y.v) F))) (by show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _`.

Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Use the proof step `rfl)`. Establish `hsep` using `y.t.semi.separated`. Establish `hcomp' : IsAdicComplete (Ideal.span {algebraMap (TWO.Ov y.v) (TWO.Ov y.v) p}) (TWO.Ov y.v)` using `hcomp`. Take `⟨κ', hκ'⟩` from `exists_character_of_rel (F := F) (MonoidHom.mk' (fun w : specV (TWO.fO y.v y.hϖ y.hv) (TWO.Ov y.v) ⟶ y.t.G => r ≫ w) fun w w' => MonObj.comp_mul _ _ _) (fun w w' h => Over.OverMorphism.ext (TWO.lift_unique y.v y.hϖ y.hv y.t.G.hom _ _ (Over.w w) (Over.w w') (congrArg (·.left) h))) …`.

Introduce and unpack `g g' _ _ ⟨k, hk, rfl⟩ ⟨k', hk', rfl⟩`. Conclude with `⟨k * k', LimVal.mul y.hx hL hu hk hk', rfl⟩)`. Use the proof step `(by`. Introduce and unpack `g _ _ ⟨k, hk, rfl⟩ ⟨k', hk', rfl⟩`. Rewrite using `[hk.unique y.hx hk']) hp0`.

Set `X : specO (TWO.Ov y.v) A ⟶ Gt` to `X₀ ≫ torsion.ι Gt p ≫ ρ.act (b' * a')`. Establish `J1 : ∀ (B : Type) [CommRing B] [Algebra (TWO.Ov y.v) B] (hB), J B hB 1 = 1` using `fun B _ _ hB => by`. Use `(hJ B hB).1 1 1` as an intermediate fact. Rewrite `this` using `[_root_.mul_one]`. Conclude with `left_eq_mul.mp this`.

Establish `h2 : X ≫ ρ.act a = 1`. Simplify using `only [X, Category.assoc]`. Rewrite using `[← ρ.map_mul, show a * (b' * a') = b' * (p : 𝓞 E) by rw [← haa]; ring, ρ.map_mul, ringAct_natCast, ← Category.assoc (torsion.ι _ _), MonObj.comp_pow, Category.comp_id, torsionι_pow, MonObj.one_comp, MonObj.comp_one]`. Establish `h3 : J A hA X ^ p = 1`. Establish `h4 : X ^ p = 1`.

Rewrite using `[← Category.comp_id X, ← MonObj.comp_pow, ← ringAct_natCast ρ, ← haa, ρ.map_mul, ← Category.assoc, h2, MonObj.one_comp]`. Use `map_pow (MonoidHom.mk' (J A hA) (hJ A hA).1) X p` as an intermediate fact. Rewrite `this` using `[h4, map_one]`. Conclude with `this.symm`. Establish `hAc : IsAdicComplete (Ideal.span {algebraMap (TWO.Ov y.v) A p}) A`.

Use `FlatComplete.isAdicComplete_of_finite_flat _ _ hcomp A` as an intermediate fact. Rewrite `this` using `[Ideal.map_span, Set.image_singleton]`. Then use the resulting hypothesis. Take `⟨k, hk⟩` from `exists_limVal y.hx u (p : TWO.Ov y.v) I hIm (J A hA X) (by`. Establish `e1 : res V aug ≫ J A hA X = res V aug ≫ 1`. Rewrite using `[MonObj.comp_one, ← J1 _ hO]`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `(hnat A _ hA hO aug X).symm.trans ?_` and prove the remaining obligations. Simplify using `only [X]`. Rewrite using `[← Category.assoc X₀, ← Category.assoc, haug, MonObj.one_comp]`. Establish `e2 : Spec.map (CommRingCat.ofHom aug.toRingHom) ≫ (J A hA X).left = Spec.map (CommRingCat.ofHom aug.toRingHom) ≫ (1 : specV (TWO.fO y.v y.hϖ y.hv) A ⟶ y.t.G).left` using `congrArg (·.left) e1`.

Rewrite using `[hI, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc, e2])`. Use `⟨fun z => κ' (pushHom gpG (TFK (R := V) F) z), specO (TWO.Ov y.v) A, (J A hA X).left, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom k, fun z z' _ _ => by beta_reduce; rw [map_mul, map_mul], ?_, ?_, hAred, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hfin)`. Conclude with `(HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)`. Rewrite using `[Over.w (J A hA X)] show Spec.map _ = Spec.map _ ≫ Spec.map _`.

Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Rewrite using `[← Over.comp_left, ← Over.comp_left, ← (hJ A hA).2, h2, J1, MonObj.comp_one]`. Introduce `c z hz`. Take `⟨φ, rfl⟩` from `exists_ptMap c`.

Take `⟨ψ, rfl⟩` from `exists_algHom_valuationSubring _ φ`. Establish `e1 : pushHom gpG (TFK (R` using `V) F) z = r ≫ (res V ψ ≫ J A hA X) := by`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `Eq.trans (Category.assoc _ _ _).symm (hz.trans ?_)` and prove the remaining obligations. Rewrite using `[← TangentPow.ptMap_comp_ptMap]`.

Conclude with `Category.assoc _ _ _`. Use `beta_reduce`. Rewrite using `[e1]`. Use `(fnVal_spec_top _ k).trans (hκ' (res V ψ ≫ J A hA X) _ ?_ ⟨ψ k, hk.map ψ, rfl⟩).symm` and prove the remaining obligations. Rewrite using `[← MonObj.comp_pow]`.

Conclude with `(congrArg _ h3).trans (MonObj.comp_one _)`. Introduce `l`. Take `⟨φ, hφ, hφ'⟩` from `het l`. Take `⟨s, hs, hs'⟩` from `hfix l`. Set `R` to `TWO.Ov y.v ⧸ Ideal.span {(p : TWO.Ov y.v)}`.

Establish `hpR : (p : R) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk _)]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)`. Establish `hR : Admissible (TWO.fO y.v y.hϖ y.hv) (DualNumber R)` using `Or.inr (hn.imp fun n h b hb => by`. Rewrite using `[IsScalarTower.algebraMap_apply (TWO.Ov y.v) R (DualNumber R)]`.

Rewrite using `[show algebraMap (TWO.Ov y.v) R (TWO.fO y.v y.hϖ y.hv b) = 0 from Ideal.Quotient.eq_zero_iff_mem.2 (h b hb), map_zero])`. Set `β` to `dualBC (Algebra.ofId (TWO.Ov y.v) R)`. Establish `htan : ptMap (TrivSqZeroExt.fstHom (TWO.Ov y.v) R R) ≫ ptMap β ≫ (et l).1 = 1`. Rewrite using `[← Category.assoc, TangentPow.ptMap_comp_ptMap, fst_comp_dualBC, ← TangentPow.ptMap_comp_ptMap, Category.assoc, (et l).2]`. Conclude with `MonObj.comp_one _`.

Take `⟨w, hw, -⟩` from `(TangentPow.pow_eq_scale_and_existsUnique_torsion _ Gt R p (ptMap β ≫ (et l).1) htan).2 hpR`. Establish `e0 : (ptMap β ≫ (et l).1) ≫ ρ.act a = 1`. Rewrite using `[Category.assoc, hs', ← Category.assoc, TangentPow.ptMap_comp_ptMap, dualBC_comp_dualScale_zero s (Ideal.Quotient.eq_zero_iff_mem.2 hs), ← TangentPow.ptMap_comp_ptMap, Category.assoc, (et l).2]`. Conclude with `MonObj.comp_one _`. Establish `e1 : (ptMap β ≫ (et l).1) ≫ ρ.act (b' * a') = ptMap β ≫ (et l).1`.

Establish `h` using `congrArg (fun c => (ptMap β ≫ (et l).1) ≫ ρ.act c) hbb`. Establish `hadd : ρ.act (b * a + b' * a') = ρ.act (b * a) * ρ.act (b' * a')` using `ρ.map_add _ _`. Rewrite `h` using `[hadd, ρ.map_one, Category.comp_id, MonObj.comp_mul, ρ.map_mul b a, ← Category.assoc, e0, MonObj.one_comp, _root_.one_mul]`. Conclude with `h`. Take `⟨ψ, hψ⟩` from `hlift R w (by rw [hw, htan])`.

Establish `e3 : ptMap ψ ≫ X = ptMap β ≫ (et l).1`. Rewrite using `[← e1, ← hw, hψ]`. Simplify using `only [X, Category.assoc]`. Establish `e4` using `hnat A _ hA hR ψ X`. Establish `e5 : (J _ hR (ptMap β ≫ (et l).1)).left = Spec.map (CommRingCat.ofHom (β.toRingHom.comp φ)) ≫ (y.x 1).left`.

Rewrite using `[hnat _ _ hD hR, hφ', ← Category.assoc, ← Spec.map_comp]`. Both sides reduce to the same expression. Establish `e6 : ∀ i, β (φ (Chart.zR 1 i)) = TrivSqZeroExt.inr (algebraMap _ R (e l i))` using `fun i => by`. Rewrite using `[hφ, dualBC_inr]`. Rewrite `e4` using `[e3]`.

Use `⟨ptMap ψ, β.toRingHom.comp φ, e6, e4.symm.trans e5, (fnVal_spec_top _ k).trans ?_⟩` and prove the remaining obligations. Set `θ : Chart.JetR (TWO.Ov y.v) (Fin 1 × Fin y.d) 1 →ₐ[TWO.Ov y.v] DualNumber (TWO.Ov y.v)` to `Chart.jetLift _ (RingHom.ker (Chart.fstD (TWO.Ov y.v))) Chart.kerD_sq (fun q => TrivSqZeroExt.inr (e l q.2)) (fun q => TrivSqZeroExt.fst_inr _ (e l q.2))`. Establish `hθ : ∀ q, (β.comp θ) (Chart.zR 1 q) = TrivSqZeroExt.inr (algebraMap _ R (e l q.2))` using `fun q => by`. Establish `h0 : θ (Chart.zR 1 q) = TrivSqZeroExt.inr (e l q.2)` using `Chart.jetLift_zR (RingHom.ker (Chart.fstD (TWO.Ov y.v))) Chart.kerD_sq _ (fun q : Fin 1 × Fin y.d => TrivSqZeroExt.fst_inr _ (e l q.2)) q`. Conclude with `(congrArg β h0).trans (dualBC_inr _)`.

Establish `v1` using `hasVal_of_ringHom y.x u (J _ hR (ptMap β ≫ (et l).1)) _ e5 (β.comp θ) fun q => (hθ q).trans (e6 q.2).symm`. Establish `v2` using `hk (DualNumber R) ψ (by`. Rewrite using `[IsScalarTower.algebraMap_apply (TWO.Ov y.v) R (DualNumber R), map_natCast, hpR, map_zero]`. Conclude with `IsNilpotent.zero)`. Rewrite `v2` using `[← e4]`.

Use `(v2.unique y.hx v1).trans ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.JetSer.dualNumber_value_toJet V _ (TWO.fO y.v y.hϖ y.hv) y.d L (e l) u R _ hθ, hu1, map_one]`. Both sides reduce to the same expression.
-/
theorem charAt_of_series (a a' b b' : 𝓞 E) (p : ℕ) (hp0 : p ≠ 0) (haa : a' * a = (p : 𝓞 E)) (hbb : b * a + b' * a' = 1)
    (hcomp : IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v))
    (hnil : ∀ c : TWO.Ov y.v, ¬ IsUnit c → ∃ n : ℕ, c ^ n ∈ Ideal.span {(p : TWO.Ov y.v)})
    (Gt : Over (Spec (CommRingCat.of (TWO.Ov y.v)))) [GrpObj Gt] [IsCommMonObj Gt] (ρ : RingAct Gt (𝓞 E))
    (J : ∀ (A : Type) [CommRing A] [Algebra (TWO.Ov y.v) A], Admissible (TWO.fO y.v y.hϖ y.hv) A →
      (specO (TWO.Ov y.v) A ⟶ Gt) → (specV (TWO.fO y.v y.hϖ y.hv) A ⟶ y.t.G))
    (hnat : ∀ (A A' : Type) [CommRing A] [Algebra (TWO.Ov y.v) A] [CommRing A'] [Algebra (TWO.Ov y.v) A']
      (hA : Admissible (TWO.fO y.v y.hϖ y.hv) A) (hA' : Admissible (TWO.fO y.v y.hϖ y.hv) A')
      (φ : A →ₐ[TWO.Ov y.v] A') (x : specO (TWO.Ov y.v) A ⟶ Gt),
      (J A' hA' (ptMap φ ≫ x)).left = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (J A hA x).left)
    (hJ : ∀ (A : Type) [CommRing A] [Algebra (TWO.Ov y.v) A] (hA : Admissible (TWO.fO y.v y.hϖ y.hv) A),
      (∀ x x', J A hA (x * x') = J A hA x * J A hA x') ∧
      (∀ x (a : 𝓞 E), J A hA (x ≫ ρ.act a) = J A hA x ≫ y.t.act.act a))
    [IsFinite (torsion Gt p).hom] [Flat (torsion Gt p).hom]
    (hred : IsReduced (specO (TWO.Ov y.v) F ⊗ torsion Gt p).left)
    (hn : ∃ n : ℕ, ∀ b ∈ maximalIdeal V ^ n, TWO.fO y.v y.hϖ y.hv b ∈ Ideal.span {(p : TWO.Ov y.v)})
    {Λ : Type} (e : Λ → Fin y.d → TWO.Ov y.v) (et : Λ → LieG Gt)
    (hD : Admissible (TWO.fO y.v y.hϖ y.hv) (DualNumber (TWO.Ov y.v)))
    (het : ∀ l, ∃ φ : Chart.JetR V (Fin y.d) 1 →+* DualNumber (TWO.Ov y.v),
      (∀ i, φ (Chart.zR 1 i) = TrivSqZeroExt.inr (e l i)) ∧
        (J _ hD (et l).1).left = Spec.map (CommRingCat.ofHom φ) ≫ (y.x 1).left)
    (hfix : ∀ l, ∃ s : TWO.Ov y.v, s ∈ Ideal.span {(p : TWO.Ov y.v)} ∧
      (et l).1 ≫ ρ.act a = ptMap (dualScale s) ≫ (et l).1)
    (L : Germ.FGLaw V y.d) (hL : JetSer.IsLawOf y.x L.F) (u : PS (TWO.Ov y.v) 1 y.d)
    (hu1 : MvPowerSeries.constantCoeff u = 1)
    (hu : ev (n := 2) ![L.mapF (TWO.fO y.v y.hϖ y.hv)] u =
      ev (n := 2) ![Germ.pt _ y.d 0] u * ev (n := 2) ![Germ.pt _ y.d 1] u) :
    y.CharAt a p e fun l => MvPowerSeries.constantCoeff (Dof (L.mapF (TWO.fO y.v y.hϖ y.hv)) (e l) u) := by
  let _ := H.starRing
  let _ : Algebra V (TWO.Ov y.v) := (TWO.fO y.v y.hϖ y.hv).toAlgebra
  obtain ⟨A, _, _, X₀, aug, I, m, hfin, hfree, hAred, haug, hI, hIm, hlift⟩ :=
    exists_connected_part (TWO.Ov y.v) p hnil Gt p hred
  have hA : Admissible (TWO.fO y.v y.hϖ y.hv) A := Or.inl ⟨hfin, hfree⟩
  have hO : Admissible (TWO.fO y.v y.hϖ y.hv) (TWO.Ov y.v) := Or.inl ⟨inferInstance, inferInstance⟩
  have := ρ.hom (b' * a')
  have := ρ.hom a'
  have := ρ.hom b'
  have := ρ.hom b
  have := y.P.U.gen_hom
  have gpG : IsGrpPullback y.P.A.A y.t.G (jK V) (y.P.U.gen.inv.left ≫ pullback.fst y.t.G.hom (jK V)) := by
    have : IsMonHom y.P.U.gen.symm.hom := by show IsMonHom y.P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso y.P.U.gen.symm).comp (isGrpPullback_pullback y.t.G (jK V))).congr
      (Category.id_comp _) rfl
  let T : Over (Spec (CommRingCat.of V)) := Over.mk ((TFK (R := V) F).hom ≫ jK V)
  let r : T ⟶ specV (TWO.fO y.v y.hϖ y.hv) (TWO.Ov y.v) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (TWO.Ov y.v) F))) (by
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp]
      rfl)
  have hsep := y.t.semi.separated
  have hcomp' : IsAdicComplete (Ideal.span {algebraMap (TWO.Ov y.v) (TWO.Ov y.v) p}) (TWO.Ov y.v) := hcomp
  obtain ⟨κ', hκ'⟩ := exists_character_of_rel (F := F)
    (MonoidHom.mk' (fun w : specV (TWO.fO y.v y.hϖ y.hv) (TWO.Ov y.v) ⟶ y.t.G => r ≫ w)
      fun w w' => MonObj.comp_mul _ _ _)
    (fun w w' h => Over.OverMorphism.ext (TWO.lift_unique y.v y.hϖ y.hv y.t.G.hom _ _
      (Over.w w) (Over.w w') (congrArg (·.left) h)))
    (fun g c => ∃ k : TWO.Ov y.v, LimVal y.x u (p : TWO.Ov y.v) g.left k ∧ c = (k : F))
    ⟨1, limVal_one y.hx hu1, rfl⟩
    (by
      rintro g g' _ _ ⟨k, hk, rfl⟩ ⟨k', hk', rfl⟩
      exact ⟨k * k', LimVal.mul y.hx hL hu hk hk', rfl⟩)
    (by
      rintro g _ _ ⟨k, hk, rfl⟩ ⟨k', hk', rfl⟩
      rw [hk.unique y.hx hk']) hp0
  let X : specO (TWO.Ov y.v) A ⟶ Gt := X₀ ≫ torsion.ι Gt p ≫ ρ.act (b' * a')
  have J1 : ∀ (B : Type) [CommRing B] [Algebra (TWO.Ov y.v) B] (hB), J B hB 1 = 1 := fun B _ _ hB => by
    have := (hJ B hB).1 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.mp this
  have h2 : X ≫ ρ.act a = 1 := by
    simp only [X, Category.assoc]
    rw [← ρ.map_mul, show a * (b' * a') = b' * (p : 𝓞 E) by rw [← haa]; ring, ρ.map_mul, ringAct_natCast,
      ← Category.assoc (torsion.ι _ _), MonObj.comp_pow, Category.comp_id, torsionι_pow, MonObj.one_comp,
      MonObj.comp_one]
  have h3 : J A hA X ^ p = 1 := by
    have h4 : X ^ p = 1 := by
      rw [← Category.comp_id X, ← MonObj.comp_pow, ← ringAct_natCast ρ, ← haa, ρ.map_mul, ← Category.assoc, h2,
        MonObj.one_comp]
    have := map_pow (MonoidHom.mk' (J A hA) (hJ A hA).1) X p
    rw [h4, map_one] at this
    exact this.symm
  have hAc : IsAdicComplete (Ideal.span {algebraMap (TWO.Ov y.v) A p}) A := by
    have := FlatComplete.isAdicComplete_of_finite_flat _ _ hcomp A
    rwa [Ideal.map_span, Set.image_singleton] at this
  obtain ⟨k, hk⟩ := exists_limVal y.hx u (p : TWO.Ov y.v) I hIm (J A hA X) (by
    have e1 : res V aug ≫ J A hA X = res V aug ≫ 1 := by
      rw [MonObj.comp_one, ← J1 _ hO]
      apply Over.OverMorphism.ext
      refine (hnat A _ hA hO aug X).symm.trans ?_
      simp only [X]
      rw [← Category.assoc X₀, ← Category.assoc, haug, MonObj.one_comp]
    have e2 : Spec.map (CommRingCat.ofHom aug.toRingHom) ≫ (J A hA X).left =
      Spec.map (CommRingCat.ofHom aug.toRingHom) ≫ (1 : specV (TWO.fO y.v y.hϖ y.hv) A ⟶ y.t.G).left :=
      congrArg (·.left) e1
    rw [hI, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc, e2])
  refine ⟨fun z => κ' (pushHom gpG (TFK (R := V) F) z), specO (TWO.Ov y.v) A, (J A hA X).left,
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom k,
    fun z z' _ _ => by beta_reduce; rw [map_mul, map_mul], ?_, ?_, hAred, ?_, ?_, ?_, ?_⟩
  · exact (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hfin)
  · exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  · rw [Over.w (J A hA X)]
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  · rw [← Over.comp_left, ← Over.comp_left, ← (hJ A hA).2, h2, J1, MonObj.comp_one]
  · intro c z hz
    obtain ⟨φ, rfl⟩ := exists_ptMap c
    obtain ⟨ψ, rfl⟩ := exists_algHom_valuationSubring _ φ
    have e1 : pushHom gpG (TFK (R := V) F) z = r ≫ (res V ψ ≫ J A hA X) := by
      apply Over.OverMorphism.ext
      refine Eq.trans (Category.assoc _ _ _).symm (hz.trans ?_)
      rw [← TangentPow.ptMap_comp_ptMap]
      exact Category.assoc _ _ _
    beta_reduce
    rw [e1]
    refine (fnVal_spec_top _ k).trans (hκ' (res V ψ ≫ J A hA X) _ ?_ ⟨ψ k, hk.map ψ, rfl⟩).symm
    rw [← MonObj.comp_pow]
    exact (congrArg _ h3).trans (MonObj.comp_one _)
  · intro l
    obtain ⟨φ, hφ, hφ'⟩ := het l
    obtain ⟨s, hs, hs'⟩ := hfix l
    let R := TWO.Ov y.v ⧸ Ideal.span {(p : TWO.Ov y.v)}
    have hpR : (p : R) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk _)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    have hR : Admissible (TWO.fO y.v y.hϖ y.hv) (DualNumber R) := Or.inr (hn.imp fun n h b hb => by
      rw [IsScalarTower.algebraMap_apply (TWO.Ov y.v) R (DualNumber R)]
      rw [show algebraMap (TWO.Ov y.v) R (TWO.fO y.v y.hϖ y.hv b) = 0 from
        Ideal.Quotient.eq_zero_iff_mem.2 (h b hb), map_zero])
    let β := dualBC (Algebra.ofId (TWO.Ov y.v) R)
    have htan : ptMap (TrivSqZeroExt.fstHom (TWO.Ov y.v) R R) ≫ ptMap β ≫ (et l).1 = 1 := by
      rw [← Category.assoc, TangentPow.ptMap_comp_ptMap, fst_comp_dualBC, ← TangentPow.ptMap_comp_ptMap,
        Category.assoc, (et l).2]
      exact MonObj.comp_one _
    obtain ⟨w, hw, -⟩ := (TangentPow.pow_eq_scale_and_existsUnique_torsion _ Gt R p (ptMap β ≫ (et l).1) htan).2 hpR
    have e0 : (ptMap β ≫ (et l).1) ≫ ρ.act a = 1 := by
      rw [Category.assoc, hs', ← Category.assoc, TangentPow.ptMap_comp_ptMap,
        dualBC_comp_dualScale_zero s (Ideal.Quotient.eq_zero_iff_mem.2 hs), ← TangentPow.ptMap_comp_ptMap,
        Category.assoc, (et l).2]
      exact MonObj.comp_one _
    have e1 : (ptMap β ≫ (et l).1) ≫ ρ.act (b' * a') = ptMap β ≫ (et l).1 := by
      have h := congrArg (fun c => (ptMap β ≫ (et l).1) ≫ ρ.act c) hbb
      have hadd : ρ.act (b * a + b' * a') = ρ.act (b * a) * ρ.act (b' * a') := ρ.map_add _ _
      rw [hadd, ρ.map_one, Category.comp_id, MonObj.comp_mul, ρ.map_mul b a, ← Category.assoc, e0,
        MonObj.one_comp, _root_.one_mul] at h
      exact h
    obtain ⟨ψ, hψ⟩ := hlift R w (by rw [hw, htan])
    have e3 : ptMap ψ ≫ X = ptMap β ≫ (et l).1 := by
      rw [← e1, ← hw, hψ]
      simp only [X, Category.assoc]
    have e4 := hnat A _ hA hR ψ X
    have e5 : (J _ hR (ptMap β ≫ (et l).1)).left =
        Spec.map (CommRingCat.ofHom (β.toRingHom.comp φ)) ≫ (y.x 1).left := by
      rw [hnat _ _ hD hR, hφ', ← Category.assoc, ← Spec.map_comp]
      rfl
    have e6 : ∀ i, β (φ (Chart.zR 1 i)) = TrivSqZeroExt.inr (algebraMap _ R (e l i)) := fun i => by
      rw [hφ, dualBC_inr]
    rw [e3] at e4
    refine ⟨ptMap ψ, β.toRingHom.comp φ, e6, e4.symm.trans e5, (fnVal_spec_top _ k).trans ?_⟩
    let θ : Chart.JetR (TWO.Ov y.v) (Fin 1 × Fin y.d) 1 →ₐ[TWO.Ov y.v] DualNumber (TWO.Ov y.v) :=
      Chart.jetLift _ (RingHom.ker (Chart.fstD (TWO.Ov y.v))) Chart.kerD_sq
        (fun q => TrivSqZeroExt.inr (e l q.2)) (fun q => TrivSqZeroExt.fst_inr _ (e l q.2))
    have hθ : ∀ q, (β.comp θ) (Chart.zR 1 q) = TrivSqZeroExt.inr (algebraMap _ R (e l q.2)) := fun q => by
      have h0 : θ (Chart.zR 1 q) = TrivSqZeroExt.inr (e l q.2) :=
        Chart.jetLift_zR (RingHom.ker (Chart.fstD (TWO.Ov y.v))) Chart.kerD_sq _
          (fun q : Fin 1 × Fin y.d => TrivSqZeroExt.fst_inr _ (e l q.2)) q
      exact (congrArg β h0).trans (dualBC_inr _)
    have v1 := hasVal_of_ringHom y.x u (J _ hR (ptMap β ≫ (et l).1)) _ e5 (β.comp θ)
      fun q => (hθ q).trans (e6 q.2).symm
    have v2 := hk (DualNumber R) ψ (by
      rw [IsScalarTower.algebraMap_apply (TWO.Ov y.v) R (DualNumber R), map_natCast, hpR, map_zero]
      exact IsNilpotent.zero)
    rw [← e4] at v2
    refine (v2.unique y.hx v1).trans ?_
    rw [GlobalTheory.JetSer.dualNumber_value_toJet V _ (TWO.fO y.v y.hϖ y.hv) y.d L (e l) u R _ hθ, hu1, map_one]
    rfl

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB in

/- English proof (translation)
Introduce `hL _ hL4 _ p hpp E _ _ _ H V _ _ _ F _ _ _ _ _ _ y`. Set `_` to `H.starRing`. Introduce `hcomp hp a ha ⟨b, b', hbb⟩ Λ e α hα heig u hu hu1 humul yy hyy`. Use `y.complete` as an intermediate fact. Establish `hJ : JetSer.JetAlgSt` using `JetSer.jetAlg`.

Establish `hD : JetSer.DLinSt` using `(GlobalTheory.JetMap.mapSt_and_dLinSt hJ (JetSer.repSt_of_jetAlgSt hJ)).2`. Establish `hpF : (p : F) ≠ 0` using `Nat.cast_ne_zero.2 hpp.ne_zero`. Establish `hp0 : (p : TWO.Ov y.v) ≠ 0` using `fun h => hpF (by simpa using congrArg Subtype.val h)`. Set `f` to `TWO.fO y.v y.hϖ y.hv`. Establish `hloc : IsLocalHom f` using `TWO.isLocalHom_fO _ _ _`.

Establish `hf : ∀ r, algebraMap (TWO.Ov y.v) F (f r) = algebraMap V F r` using `fun r => (IsScalarTower.algebraMap_apply V (FractionRing V) F r).symm`. Establish `hϖ0 : f y.ϖ ≠ 0` using `fun h => by`. Establish `h1` using `hf y.ϖ`. Rewrite `h1` using `[h, map_zero, IsScalarTower.algebraMap_apply V (FractionRing V) F, eq_comm, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]`. Conclude with `y.hϖ.ne_zero h1`.

Establish `hϖu : ¬ IsUnit (f y.ϖ)` using `fun h => y.hϖ.not_isUnit (hloc.map_nonunit _ h)`. Establish `hmap : (maximalIdeal V).map f = Ideal.span {f y.ϖ}`. Rewrite using `[y.hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]`. Take `⟨n₁, hn₁⟩` from `exists_pow_mem_span y.v _ _ hϖu hp0`. Take `⟨n₂, hn₂⟩` from `exists_pow_mem_span y.v _ _ hp hϖ0`.

Establish `hle₁ : (maximalIdeal V).map f ^ n₁ ≤ Ideal.span {(p : TWO.Ov y.v)}`. Rewrite using `[hmap, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]`. Conclude with `hn₁`. Establish `hle₂ : Ideal.span {(p : TWO.Ov y.v)} ^ n₂ ≤ (maximalIdeal V).map f`. Rewrite using `[hmap, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]`.

Conclude with `hn₂`. Take `⟨Ex, B, hB, hB', Gt, _, _, ρ, J, hGt, hfin, hnat, hJJ⟩` from `GlobalTheory.T.torusExtension_over_completeLocal_dvr hL hL4 E H V y.t y.P (TWO.Ov y.v) f hloc (isAdicComplete_of_pow_le hle₂ hle₁) (fun b hb => by rw [hmap]; exact exists_pow_mem_span y.v _ _ hb hϖ0)`. Establish `hp1 : 1 ≤ p` using `hpp.one_le`. Take `⟨hZ₁, hZ₂⟩` from `isFinite_flat_torsion_of_isGt _ Ex Gt hGt _ hp1 (hfin _ hp1).1 (hfin _ hp1).2`. Establish `hred` using `isReduced_torsion_geometric_fibre (TWO.Ov y.v) F Gt p hpF hZ₁`.

Establish `hDn : Admissible f (DualNumber (TWO.Ov y.v))` using `Or.inl ⟨inferInstanceAs (Module.Finite _ (TWO.Ov y.v × TWO.Ov y.v)), inferInstanceAs (Module.Free _ (TWO.Ov y.v × TWO.Ov y.v))⟩`. Take `⟨co, tv, -, -, htv, hact⟩` from `exists_lie_coordinates hJ hD f y.t.G y.x y.hx Gt (J _ hDn) (hJJ _ hDn).1 (hJJ _ hDn).2.2.1 (fun φ w => hnat _ _ hDn hDn φ w) (fun g hg => by`. Use `(hJJ _ hDn).2.2.2.2 (RingHom.ker (Chart.fstD (TWO.Ov y.v))) g ⟨1 + 1, by rw [Chart.kerD_sq, Ideal.zero_eq_bot]⟩ ?_` and prove the remaining obligations. Establish `e1 : Ideal.Quotient.mk (RingHom.ker (Chart.fstD (TWO.Ov y.v))) = ((Ideal.Quotient.mk (RingHom.ker (Chart.fstD (TWO.Ov y.v)))).comp (algebraMap (TWO.Ov y.v) _)).comp (Chart.fstD (TWO.Ov y.v)).toRingHom` using `RingHom.ext fun z => Ideal.Quotient.eq.2 (by show Chart.fstD _ (z - algebraMap _ _ (Chart.fstD _ z)) = 0`. Rewrite using `[map_sub, AlgHom.commutes]`.

Conclude with `sub_self _)`. Rewrite using `[e1, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc, hg])`. Establish `heig' : ∀ l, (tv (e l)).1 ≫ ρ.act a = ptMap (dualScale (α l)) ≫ (tv (e l)).1` using `fun l => by`. Use `y.t.act.hom a` as an intermediate fact. Use `hact (y.t.act.act a) (ρ.act a) _ (y.hB.map a) (fun w => (hJJ _ hDn).2.1 w a) _ _ ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Establish `h1` using `congrFun (heig l) i`. Rewrite `h1` using `[dAct_eq_map f hf]`. Apply `Subtype.val_injective` to reduce the goal to its premises. Conclude with `(RingHom.map_mulVec (algebraMap (TWO.Ov y.v) F) _ _ i).trans h1`.

Set `u₀ : PS (TWO.Ov y.v) 1 y.d` to `fun mo => ⟨MvPowerSeries.coeff mo u, hu mo⟩`. Establish `hu₀ : MvPowerSeries.map (algebraMap (TWO.Ov y.v) F) u₀ = u`. Use extensionality with `mo`. Both sides reduce to the same expression. Establish `hFK : (fun i => MvPowerSeries.map (algebraMap (TWO.Ov y.v) F) (y.B.G.mapF f i)) = y.B.FK F`.

Use function extensionality and compare the values at `i`. Use extensionality with `mo`. Conclude with `hf _`. Establish `hyy' : yy = fun l => MvPowerSeries.constantCoeff (Dof (y.B.G.mapF f) (e l) u₀)`. Use function extensionality and compare the values at `l`.

Apply `Subtype.val_injective` to reduce the goal to its premises. Rewrite using `[hyy, ← hu₀, ← hFK]`. Use `congrArg MvPowerSeries.constantCoeff (InvDerMap.map_Dof (algebraMap (TWO.Ov y.v) F) (y.B.G.mapF f) (e l) u₀)` as an intermediate fact. Rewrite `this` using `[MvPowerSeries.constantCoeff_map]`. Conclude with `this.symm`.

Rewrite using `[hyy']`. Use `charAt_of_series y a (star a) b b' p hpp.ne_zero (by rw [← ha, mul_comm]) hbb hcomp (fun c hc => exists_pow_mem_span y.v _ _ hc hp0) Gt ρ J hnat (fun A _ _ hA => ⟨(hJJ A hA).1, (hJJ A hA).2.1⟩) hred ⟨n₁, fun z hz => hle₁ (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hz)⟩ …` and prove the remaining obligations. Establish `hinj : Function.Injective (MvPowerSeries.map (σ` using `Fin 2 × Fin y.d) (algebraMap (TWO.Ov y.v) F)) := fun g g' h => by`. Use extensionality with `mo`. Conclude with `congrArg (MvPowerSeries.coeff mo) h`.

Establish `hpt : ∀ i : Fin 2, JetSer.IntTrans.mP (algebraMap (TWO.Ov y.v) F) (pt _ y.d i) = pt F y.d i` using `fun i =>`. Use function extensionality and compare the values at `fun j => MvPowerSeries.map_X _ _`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, JetSer.IntTrans.map_ev1 _ (WickVanishing.gp_pt 0), JetSer.IntTrans.map_ev1 _ (WickVanishing.gp_pt 1), JetSer.IntTrans.map_ev1 _ (fun i => by show MvPowerSeries.constantCoeff (MvPowerSeries.map f _) = 0`. Rewrite using `[MvPowerSeries.constantCoeff_map, y.B.G.const, map_zero]), hpt, hpt, hu₀, ← humul, ← hFK]`.

Both sides reduce to the same expression.
-/
theorem charAt_of_multiplicative_series : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (p : ℕ), p.Prime → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ a : 𝓞 E, a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∀ (Λ : Type) (e : Λ → Fin y.d → TWO.Ov y.v) (α : Λ → TWO.Ov y.v), (∀ l, α l ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ l, (dAct F y.B a).mulVec (fun i => (e l i : F)) = (α l : F) • fun i => (e l i : F)) → ∀ u : PS F 1 y.d, (∀ mo, 0 ≤ y.v (MvPowerSeries.coeff mo u)) → MvPowerSeries.constantCoeff u = 1 → ev (n := 2) ![y.B.FK F] u = ev (n := 2) ![pt F y.d 0] u * ev (n := 2) ![pt F y.d 1] u → ∀ yy : Λ → TWO.Ov y.v, (∀ l, (yy l : F) = MvPowerSeries.constantCoeff (Dof (y.B.FK F) (fun i => (e l i : F)) u)) → y.CharAt a p e yy := by
  intro hL _ hL4 _ p hpp E _ _ _ H V _ _ _ F _ _ _ _ _ _ y
  let _ := H.starRing
  intro hcomp hp a ha ⟨b, b', hbb⟩ Λ e α hα heig u hu hu1 humul yy hyy
  have := y.complete
  have hJ : JetSer.JetAlgSt := JetSer.jetAlg
  have hD : JetSer.DLinSt := (GlobalTheory.JetMap.mapSt_and_dLinSt hJ (JetSer.repSt_of_jetAlgSt hJ)).2
  have hpF : (p : F) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
  have hp0 : (p : TWO.Ov y.v) ≠ 0 := fun h => hpF (by simpa using congrArg Subtype.val h)
  let f := TWO.fO y.v y.hϖ y.hv
  have hloc : IsLocalHom f := TWO.isLocalHom_fO _ _ _
  have hf : ∀ r, algebraMap (TWO.Ov y.v) F (f r) = algebraMap V F r := fun r =>
    (IsScalarTower.algebraMap_apply V (FractionRing V) F r).symm
  have hϖ0 : f y.ϖ ≠ 0 := fun h => by
    have h1 := hf y.ϖ
    rw [h, map_zero, IsScalarTower.algebraMap_apply V (FractionRing V) F, eq_comm, map_eq_zero,
      FaithfulSMul.algebraMap_eq_zero_iff] at h1
    exact y.hϖ.ne_zero h1
  have hϖu : ¬ IsUnit (f y.ϖ) := fun h => y.hϖ.not_isUnit (hloc.map_nonunit _ h)
  have hmap : (maximalIdeal V).map f = Ideal.span {f y.ϖ} := by
    rw [y.hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  obtain ⟨n₁, hn₁⟩ := exists_pow_mem_span y.v _ _ hϖu hp0
  obtain ⟨n₂, hn₂⟩ := exists_pow_mem_span y.v _ _ hp hϖ0
  have hle₁ : (maximalIdeal V).map f ^ n₁ ≤ Ideal.span {(p : TWO.Ov y.v)} := by
    rw [hmap, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    exact hn₁
  have hle₂ : Ideal.span {(p : TWO.Ov y.v)} ^ n₂ ≤ (maximalIdeal V).map f := by
    rw [hmap, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    exact hn₂
  obtain ⟨Ex, B, hB, hB', Gt, _, _, ρ, J, hGt, hfin, hnat, hJJ⟩ := GlobalTheory.T.torusExtension_over_completeLocal_dvr hL hL4 E H V y.t y.P (TWO.Ov y.v) f hloc
    (isAdicComplete_of_pow_le hle₂ hle₁)
    (fun b hb => by rw [hmap]; exact exists_pow_mem_span y.v _ _ hb hϖ0)
  have hp1 : 1 ≤ p := hpp.one_le
  obtain ⟨hZ₁, hZ₂⟩ := isFinite_flat_torsion_of_isGt _ Ex Gt hGt _ hp1 (hfin _ hp1).1 (hfin _ hp1).2
  have hred := isReduced_torsion_geometric_fibre (TWO.Ov y.v) F Gt p hpF hZ₁
  have hDn : Admissible f (DualNumber (TWO.Ov y.v)) := Or.inl
    ⟨inferInstanceAs (Module.Finite _ (TWO.Ov y.v × TWO.Ov y.v)),
      inferInstanceAs (Module.Free _ (TWO.Ov y.v × TWO.Ov y.v))⟩
  obtain ⟨co, tv, -, -, htv, hact⟩ := exists_lie_coordinates hJ hD f y.t.G y.x y.hx Gt (J _ hDn)
    (hJJ _ hDn).1 (hJJ _ hDn).2.2.1 (fun φ w => hnat _ _ hDn hDn φ w) (fun g hg => by
      refine (hJJ _ hDn).2.2.2.2 (RingHom.ker (Chart.fstD (TWO.Ov y.v))) g
        ⟨1 + 1, by rw [Chart.kerD_sq, Ideal.zero_eq_bot]⟩ ?_
      have e1 : Ideal.Quotient.mk (RingHom.ker (Chart.fstD (TWO.Ov y.v))) =
          ((Ideal.Quotient.mk (RingHom.ker (Chart.fstD (TWO.Ov y.v)))).comp (algebraMap (TWO.Ov y.v) _)).comp
            (Chart.fstD (TWO.Ov y.v)).toRingHom := RingHom.ext fun z => Ideal.Quotient.eq.2 (by
        show Chart.fstD _ (z - algebraMap _ _ (Chart.fstD _ z)) = 0
        rw [map_sub, AlgHom.commutes]
        exact sub_self _)
      rw [e1, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc, hg])
  have heig' : ∀ l, (tv (e l)).1 ≫ ρ.act a = ptMap (dualScale (α l)) ≫ (tv (e l)).1 := fun l => by
    have := y.t.act.hom a
    refine hact (y.t.act.act a) (ρ.act a) _ (y.hB.map a) (fun w => (hJJ _ hDn).2.1 w a) _ _ ?_
    funext i
    have h1 := congrFun (heig l) i
    rw [dAct_eq_map f hf] at h1
    apply Subtype.val_injective
    exact (RingHom.map_mulVec (algebraMap (TWO.Ov y.v) F) _ _ i).trans h1
  let u₀ : PS (TWO.Ov y.v) 1 y.d := fun mo => ⟨MvPowerSeries.coeff mo u, hu mo⟩
  have hu₀ : MvPowerSeries.map (algebraMap (TWO.Ov y.v) F) u₀ = u := by
    ext mo
    rfl
  have hFK : (fun i => MvPowerSeries.map (algebraMap (TWO.Ov y.v) F) (y.B.G.mapF f i)) = y.B.FK F := by
    funext i
    ext mo
    exact hf _
  have hyy' : yy = fun l => MvPowerSeries.constantCoeff (Dof (y.B.G.mapF f) (e l) u₀) := by
    funext l
    apply Subtype.val_injective
    rw [hyy, ← hu₀, ← hFK]
    have := congrArg MvPowerSeries.constantCoeff
      (InvDerMap.map_Dof (algebraMap (TWO.Ov y.v) F) (y.B.G.mapF f) (e l) u₀)
    rw [MvPowerSeries.constantCoeff_map] at this
    exact this.symm
  rw [hyy']
  refine charAt_of_series y a (star a) b b' p hpp.ne_zero (by rw [← ha, mul_comm]) hbb hcomp
    (fun c hc => exists_pow_mem_span y.v _ _ hc hp0) Gt ρ J hnat
    (fun A _ _ hA => ⟨(hJJ A hA).1, (hJJ A hA).2.1⟩) hred
    ⟨n₁, fun z hz => hle₁ (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hz)⟩ e (fun l => tv (e l)) hDn
    (fun l => htv (e l)) (fun l => ⟨α l, hα l, heig' l⟩) y.B.G y.hB.law u₀ (Subtype.ext hu1) ?_
  have hinj : Function.Injective (MvPowerSeries.map (σ := Fin 2 × Fin y.d) (algebraMap (TWO.Ov y.v) F)) :=
    fun g g' h => by
      ext mo
      exact congrArg (MvPowerSeries.coeff mo) h
  have hpt : ∀ i : Fin 2, JetSer.IntTrans.mP (algebraMap (TWO.Ov y.v) F) (pt _ y.d i) = pt F y.d i := fun i =>
    funext fun j => MvPowerSeries.map_X _ _
  apply hinj
  rw [map_mul, JetSer.IntTrans.map_ev1 _ (WickVanishing.gp_pt 0), JetSer.IntTrans.map_ev1 _ (WickVanishing.gp_pt 1),
    JetSer.IntTrans.map_ev1 _ (fun i => by
      show MvPowerSeries.constantCoeff (MvPowerSeries.map f _) = 0
      rw [MvPowerSeries.constantCoeff_map, y.B.G.const, map_zero]), hpt, hpt, hu₀, ← humul, ← hFK]
  rfl

end GlobalTheory.SeriesCharacter
