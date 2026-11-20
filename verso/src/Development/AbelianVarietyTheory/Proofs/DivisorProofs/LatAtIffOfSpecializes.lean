import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianOfIsGrpPullbackSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitSpreadingTorusPartOfSpecialisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusPartGenericFibreClosedFibreDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCompatOfCompatOverFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCompatOfCompatClosedPointStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.FibLat

open GlobalTheory.SplitTorus (torusMap bcMap)

/- English proof (translation)
Establish `h1` using `Spec.map_injective h`. Establish `h2` using `congrArg CommRingCat.Hom.hom h1`. Simplify using `using h2`.
-/
theorem ringHom_eq_of_spMap {A B : Type} [CommRing A] [CommRing B] {a b : A →+* B} (h : spMap a = spMap b) : a = b := by
  have h1 := Spec.map_injective h
  have h2 := congrArg CommRingCat.Hom.hom h1
  simpa using h2

/- English proof (translation)
Simplify using `only [spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨(Spec.preimage s).hom, by simp [spMap]⟩`.
-/
theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (s : Sp B ⟶ Sp A) : ∃ a : A →+* B, s = spMap a := ⟨(Spec.preimage s).hom, by simp [spMap]⟩

/- English proof (translation)
Use `⟨IsPullback.of_hasPullback _ _, ?_⟩` and prove the remaining obligations. Introduce `T x y x₀ y₀ hx hy`. Establish `key : ∀ (z : T ⟶ (Over.pullback f).obj G) (z₀ : (Over.map f).obj T ⟶ G), z₀.left = z.left ≫ pullback.fst G.hom f → z = (Over.mapPullbackAdj f).unit.app T ≫ (Over.pullback f).map z₀`. Introduce `z z₀ hz`. Use `ext`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [Over.pullback_obj_left, Over.mapPullbackAdj_unit_app, Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp, hz, Over.homMk_left] erw [pullback.lift_fst_assoc, Category.id_comp]`. Simplify using `only [Over.pullback_obj_left, Over.mapPullbackAdj_unit_app, Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp, Over.homMk_left] erw [pullback.lift_snd]`. Conclude with `Over.w z`. Rewrite using `[key x x₀ hx, key y y₀ hy, ← MonObj.comp_mul, ← Functor.map_mul]`.

Simplify using the standard rewrite rules. Use `erw [pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]`.
-/
private theorem isGrpPullback_pullback_fst {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    IsGrpPullback ((Over.pullback f).obj G) G f (pullback.fst G.hom f) := by
  refine ⟨IsPullback.of_hasPullback _ _, ?_⟩
  intro T x y x₀ y₀ hx hy
  have key : ∀ (z : T ⟶ (Over.pullback f).obj G) (z₀ : (Over.map f).obj T ⟶ G),
      z₀.left = z.left ≫ pullback.fst G.hom f → z = (Over.mapPullbackAdj f).unit.app T ≫ (Over.pullback f).map z₀ := by
    intro z z₀ hz
    ext
    apply pullback.hom_ext
    · simp only [Over.pullback_obj_left, Over.mapPullbackAdj_unit_app, Over.comp_left, Over.pullback_map_left,
        Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp, hz, Over.homMk_left]
      erw [pullback.lift_fst_assoc, Category.id_comp]
    · simp only [Over.pullback_obj_left, Over.mapPullbackAdj_unit_app, Over.comp_left, Over.pullback_map_left,
        Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp, Over.homMk_left]
      erw [pullback.lift_snd]
      exact Over.w z
  rw [key x x₀ hx, key y y₀ hy, ← MonObj.comp_mul, ← Functor.map_mul]
  simp
  erw [pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]

/- English proof (translation)
Take `⟨z, -, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := s) (g := s') _ _ hs`. Take `⟨K, _, ⟨p⟩⟩ : ∃ (K : Type) (_ : Field K), Nonempty (Sp K ⟶ pullback s s')` from `⟨_, inferInstance, ⟨(pullback s s').fromSpecResidueField z⟩⟩`. Take `⟨b, hb⟩` from `exists_spMap (p ≫ pullback.fst s s')`. Take `⟨b', hb'⟩` from `exists_spMap (p ≫ pullback.snd s s')`. Establish `e : spMap b ≫ s = spMap b' ≫ s'`.

Rewrite using `[← hb, ← hb', Category.assoc, Category.assoc, pullback.condition]`. Establish `hψ` using `isGrpPullback_pullback_fst (spMap b) G₀`. Use `set ψ := pullback.fst G₀.hom (spMap b)`. Use `set GK := (Over.pullback (spMap b)).obj G₀`. Establish `w0 : (ψ ≫ φ) ≫ G.hom = (GK.hom ≫ spMap b') ≫ s'`.

Simplify using `only [Category.assoc]`. Rewrite using `[hφ.1.w, ← Category.assoc ψ, hψ.1.w, Category.assoc, e]`. Use `⟨K, inferInstance, b, b', GK, inferInstance, ψ, hφ'.1.lift (ψ ≫ φ) (GK.hom ≫ spMap b') w0, e, hψ, ?_, (hφ'.1.lift_fst _ _ _).symm⟩` and prove the remaining obligations. Establish `n` using `hψ.comp hφ`. Rewrite `n` using `[e, ← hφ'.1.lift_fst (ψ ≫ φ) (GK.hom ≫ spMap b') w0]`.

Conclude with `IsGrpPullback.cancel hφ' n (hφ'.1.lift_snd _ _ _)`.
-/
theorem exists_common_pullback {Y : Scheme.{0}} {G : Over Y} [GrpObj G] {κ κ' : Type} [Field κ] [Field κ'] {s : Sp κ ⟶ Y}
    {s' : Sp κ' ⟶ Y} (hs : s (closedPoint κ) = s' (closedPoint κ')) {G₀ : Over (Sp κ)} [GrpObj G₀] {φ : G₀.left ⟶ G.left}
    {G₀' : Over (Sp κ')} [GrpObj G₀'] {φ' : G₀'.left ⟶ G.left} (hφ : IsGrpPullback G₀ G s φ)
    (hφ' : IsGrpPullback G₀' G s' φ') :
    ∃ (K : Type) (_ : Field K) (b : κ →+* K) (b' : κ' →+* K) (GK : Over (Sp K)) (_ : GrpObj GK) (ψ : GK.left ⟶ G₀.left)
      (ψ' : GK.left ⟶ G₀'.left), spMap b ≫ s = spMap b' ≫ s' ∧ IsGrpPullback GK G₀ (spMap b) ψ ∧
      IsGrpPullback GK G₀' (spMap b') ψ' ∧ ψ ≫ φ = ψ' ≫ φ' := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := s) (g := s') _ _ hs
  obtain ⟨K, _, ⟨p⟩⟩ : ∃ (K : Type) (_ : Field K), Nonempty (Sp K ⟶ pullback s s') :=
    ⟨_, inferInstance, ⟨(pullback s s').fromSpecResidueField z⟩⟩
  obtain ⟨b, hb⟩ := exists_spMap (p ≫ pullback.fst s s')
  obtain ⟨b', hb'⟩ := exists_spMap (p ≫ pullback.snd s s')
  have e : spMap b ≫ s = spMap b' ≫ s' := by
    rw [← hb, ← hb', Category.assoc, Category.assoc, pullback.condition]
  have hψ := isGrpPullback_pullback_fst (spMap b) G₀
  set ψ := pullback.fst G₀.hom (spMap b)
  set GK := (Over.pullback (spMap b)).obj G₀
  have w0 : (ψ ≫ φ) ≫ G.hom = (GK.hom ≫ spMap b') ≫ s' := by
    simp only [Category.assoc]
    rw [hφ.1.w, ← Category.assoc ψ, hψ.1.w, Category.assoc, e]
  refine ⟨K, inferInstance, b, b', GK, inferInstance, ψ, hφ'.1.lift (ψ ≫ φ) (GK.hom ≫ spMap b') w0, e, hψ, ?_,
    (hφ'.1.lift_fst _ _ _).symm⟩
  have n := hψ.comp hφ
  rw [e, ← hφ'.1.lift_fst (ψ ≫ φ) (GK.hom ≫ spMap b') w0] at n
  exact IsGrpPullback.cancel hφ' n (hφ'.1.lift_snd _ _ _)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {G : Over M.Z} [GrpObj G]
  {I T : Type} {f : I → (G ⟶ G)} {gγ : T → (Over.mk M.pt ⟶ G)} {ζ : oˣ} {L : ℕ}

/- English proof (translation)
Take `⟨X, _, _, _, κ, _, s, G₀, _, φ, tι, hs, hφ, ht, rfl⟩` from `h`. Take `⟨X', _, _, _, κ', _, s', G₀', _, φ', tι', hs', hφ', ht', rfl⟩` from `h'`. Take `⟨K, _, b, b', GK, _, ψ, ψ', -, hψ, hψ', -⟩` from `exists_common_pullback (hs.trans hs'.symm) hφ hφ'`. Take `⟨e, -⟩` from `IsTorPart.exists_equiv (ht.pull hψ) (ht'.pull hψ')`. Conclude with `e.toIntLinearEquiv.finrank_eq`.
-/
theorem RkAt.unique {w : M.Z} {r r' : ℕ} (h : RkAt G w r) (h' : RkAt G w r') : r = r' := by
  obtain ⟨X, _, _, _, κ, _, s, G₀, _, φ, tι, hs, hφ, ht, rfl⟩ := h
  obtain ⟨X', _, _, _, κ', _, s', G₀', _, φ', tι', hs', hφ', ht', rfl⟩ := h'
  obtain ⟨K, _, b, b', GK, _, ψ, ψ', -, hψ, hψ', -⟩ := exists_common_pullback (hs.trans hs'.symm) hφ hφ'
  obtain ⟨e, -⟩ := IsTorPart.exists_equiv (ht.pull hψ) (ht'.pull hψ')
  exact e.toIntLinearEquiv.finrank_eq

/- English proof (translation)
Take `⟨κ, _, s, a, G₀, _, φ, tι, hs, ha, hφ, ht, hc⟩` from `h`. Take `⟨K, _, b, b', GK, _, ψ, ψ', e1, hψ, hψ', e2⟩` from `exists_common_pullback (hs.trans hs'.symm) hφ hφ'`. Take `⟨e, he⟩` from `IsTorPart.exists_equiv (ht'.pull hψ') (ht.pull hψ)`. Establish `hab : b.comp a = b'.comp a'`. Apply `ringHom_eq_of_spMap` to reduce the goal to its premises.

Rewrite using `[← spMap_comp', ← spMap_comp', ← ha, ← ha', reassoc_of% e1]`. Use `⟨e, K, inferInstance, b', GK, inferInstance, ψ', hψ', ?_⟩` and prove the remaining obligations. Establish `hc2` using `hc.pull b hψ`. Rewrite `hc2` using `[he, e1, hab, e2]`. Conclude with `hc2`.
-/
theorem LatAt.transfer {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {m : I → X →+ X}
    {c : T → X →+ ZMod L} {w : M.Z} (h : LatAt f gγ ζ L m c w) {κ' : Type} [Field κ'] {s' : Sp κ' ⟶ M.Z}
    (hs' : s' (closedPoint κ') = w) {a' : o →+* κ'} (ha' : s' ≫ M.s = spMap a') {G₀' : Over (Sp κ')} [GrpObj G₀']
    {φ' : G₀'.left ⟶ G.left} (hφ' : IsGrpPullback G₀' G s' φ') {X' : Type} [AddCommGroup X'] [Module.Free ℤ X']
    [Module.Finite ℤ X'] {t' : splitTorus (Sp κ') X' ⟶ G₀'} (ht' : IsTorPart t') :
    ∃ (e : X' ≃+ X) (K : Type) (_ : Field K) (b : κ' →+* K) (GK : Over (Sp K)) (_ : GrpObj GK) (ψ : GK.left ⟶ G₀'.left)
      (hψ : IsGrpPullback GK G₀' (spMap b) ψ),
      Compat f gγ ζ L m c (spMap b ≫ s') (b.comp a') (ψ ≫ φ') (torusMap _ e.toAddMonoidHom ≫ pullTorus hψ t') := by
  obtain ⟨κ, _, s, a, G₀, _, φ, tι, hs, ha, hφ, ht, hc⟩ := h
  obtain ⟨K, _, b, b', GK, _, ψ, ψ', e1, hψ, hψ', e2⟩ := exists_common_pullback (hs.trans hs'.symm) hφ hφ'
  obtain ⟨e, he⟩ := IsTorPart.exists_equiv (ht'.pull hψ') (ht.pull hψ)
  have hab : b.comp a = b'.comp a' := by
    apply ringHom_eq_of_spMap
    rw [← spMap_comp', ← spMap_comp', ← ha, ← ha', reassoc_of% e1]
  refine ⟨e, K, inferInstance, b', GK, inferInstance, ψ', hψ', ?_⟩
  have hc2 := hc.pull b hψ
  rw [he, e1, hab, e2] at hc2
  exact hc2

/- English proof (translation)
Take `⟨hm, hc⟩` from `h`. Take `⟨hm', hc'⟩` from `h'`. Prove the components needed by the constructor for the conclusion. Use function extensionality and compare the values at `e`. Apply `ht.cancel` to reduce the goal to its premises.

Apply `hom_ext_of_pullback hφ` to reduce the goal to its premises. Rewrite using `[← hm e, ← hm' e]`. Use function extensionality and compare the values at `tt`. Take `⟨z, hz, hv⟩` from `hc tt`. Take `⟨z', hz', hv'⟩` from `hc' tt`.

Establish `hzz : z = z'`. Use `ht.mono` as an intermediate fact. Apply `(cancel_mono t).1` to reduce the goal to its premises. Apply `hom_ext_of_pullback hφ` to reduce the goal to its premises. Conclude with `ValAt.unique hv hv'`.

Substitute `hzz` using the available equality. Use extensionality with `χ`. Establish `h3` using `congrArg Units.val (GlobalTheory.ZH.TorusPerp.unitOn_injective ((hz χ).symm.trans (hz' χ)))`. Simplify using `only [Units.val_pow_eq_pow_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h3`. Use `haveI : NeZero L := ⟨hL.ne'⟩`.

Conclude with `ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3)`.
-/
theorem Compat.unique [IsSeparated G.hom] (hL : 0 < L) {X : Type} [AddCommGroup X] {m m' : I → X →+ X}
    {c c' : T → X →+ ZMod L} {K : Type} [Field K] {s : Sp K ⟶ M.Z} {a : o →+* K} (hζ : IsPrimitiveRoot (a ζ) L)
    {G₀ : Over (Sp K)} [GrpObj G₀] {φ : G₀.left ⟶ G.left} (hφ : IsGrpPullback G₀ G s φ) {t : splitTorus (Sp K) X ⟶ G₀}
    (ht : IsTorPart t) (h : Compat f gγ ζ L m c s a φ t) (h' : Compat f gγ ζ L m' c' s a φ t) : m = m' ∧ c = c' := by
  obtain ⟨hm, hc⟩ := h
  obtain ⟨hm', hc'⟩ := h'
  constructor
  · funext e
    apply ht.cancel
    apply hom_ext_of_pullback hφ
    rw [← hm e, ← hm' e]
  · funext tt
    obtain ⟨z, hz, hv⟩ := hc tt
    obtain ⟨z', hz', hv'⟩ := hc' tt
    have hzz : z = z' := by
      have := ht.mono
      apply (cancel_mono t).1
      apply hom_ext_of_pullback hφ
      exact ValAt.unique hv hv'
    subst hzz
    ext χ
    have h3 := congrArg Units.val (GlobalTheory.ZH.TorusPerp.unitOn_injective ((hz χ).symm.trans (hz' χ)))
    simp only [Units.val_pow_eq_pow_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h3
    haveI : NeZero L := ⟨hL.ne'⟩
    exact ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3)

/- English proof (translation)
Take `⟨κ', _, s', a', G₀', _, φ', tι', hs', ha', hφ', ht', hc'⟩` from `h'`. Take `⟨e, K, _, b, GK, _, ψ, hψ, hc⟩` from `h.transfer hs' ha' hφ' ht'`. Establish `hc2` using `(hc'.pull b hψ).equiv e (m' := fun i => (e : X' →+ X).comp ((m' i).comp (e.symm : X →+ X'))) (c' := fun t => (c' t).comp (e.symm : X →+ X')) (fun i x => by simp) (fun t x => by simp)`. Take `⟨h1, h2⟩` from `Compat.unique hL (hζ K (b.comp a')) (hψ.comp hφ') ((ht'.pull hψ).equiv e) hc hc2`. Substitute `h1 h2` using the available equality.

Apply the tactic sequence `refine ⟨e.symm, fun i x => ?_, fun t x => ?_⟩ <;> simp`.
-/
theorem LatAt.unique [IsSeparated G.hom] (hL : 0 < L) (hζ : ∀ (κ : Type) [Field κ] (a : o →+* κ), IsPrimitiveRoot (a ζ) L)
    {X X' : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X']
    [Module.Finite ℤ X'] {m : I → X →+ X} {c : T → X →+ ZMod L} {m' : I → X' →+ X'} {c' : T → X' →+ ZMod L} {w : M.Z}
    (h : LatAt f gγ ζ L m c w) (h' : LatAt f gγ ζ L m' c' w) :
    ∃ θ : X ≃+ X', (∀ e x, θ (m e x) = m' e (θ x)) ∧ ∀ t x, c' t (θ x) = c t x := by
  obtain ⟨κ', _, s', a', G₀', _, φ', tι', hs', ha', hφ', ht', hc'⟩ := h'
  obtain ⟨e, K, _, b, GK, _, ψ, hψ, hc⟩ := h.transfer hs' ha' hφ' ht'
  have hc2 := (hc'.pull b hψ).equiv e (m' := fun i => (e : X' →+ X).comp ((m' i).comp (e.symm : X →+ X')))
    (c' := fun t => (c' t).comp (e.symm : X →+ X')) (fun i x => by simp) (fun t x => by simp)
  obtain ⟨h1, h2⟩ := Compat.unique hL (hζ K (b.comp a')) (hψ.comp hφ') ((ht'.pull hψ).equiv e) hc hc2
  subst h1 h2
  refine ⟨e.symm, fun i x => ?_, fun t x => ?_⟩ <;> simp

/- English proof (translation)
Take `⟨κ, _, s, a, G₀, _, φ, tι, hs, ha, hφ, ht, hcc⟩` from `h`. Conclude with `⟨κ, _, s, a, G₀, _, φ, _, hs, ha, hφ, ht.equiv e, hcc.equiv e hm hc⟩`.
-/
theorem LatAt.equiv {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {m : I → X →+ X} {c : T → X →+ ZMod L}
    {m' : I → X' →+ X'} {c' : T → X' →+ ZMod L} {w : M.Z} (h : LatAt f gγ ζ L m c w)
    (e : X ≃+ X') (hm : ∀ i x, e (m i x) = m' i (e x)) (hc : ∀ t x, c' t (e x) = c t x) : LatAt f gγ ζ L m' c' w := by
  obtain ⟨κ, _, s, a, G₀, _, φ, tι, hs, ha, hφ, ht, hcc⟩ := h
  exact ⟨κ, _, s, a, G₀, _, φ, _, hs, ha, hφ, ht.equiv e, hcc.equiv e hm hc⟩

/- English proof (translation)
Use `M.lft` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Introduce `U`. Establish `h1` using `HasRingHomProperty.appLE @LocallyOfFiniteType M.s this ⟨⊤, isAffineOpen_top _⟩ U (by simp)`. Establish `: IsNoetherianRing Γ(Sp o, ⊤)` using `IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩`.

Use `letI := (M.s.appLE ⊤ U.1 (by simp)).hom.toAlgebra`. Establish `: Algebra.FiniteType Γ(Sp o, ⊤) Γ(M.Z, U.1)` using `h1`. Conclude with `Algebra.FiniteType.isNoetherianRing Γ(Sp o, ⊤) Γ(M.Z, U.1)`.
-/
private theorem ratModel_isLocallyNoetherian {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o]
    (M : RatModel o Ω) : IsLocallyNoetherian M.Z := by
  have := M.lft
  constructor
  intro U
  have h1 := HasRingHomProperty.appLE @LocallyOfFiniteType M.s this ⟨⊤, isAffineOpen_top _⟩ U (by simp)
  have : IsNoetherianRing Γ(Sp o, ⊤) := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  letI := (M.s.appLE ⊤ U.1 (by simp)).hom.toAlgebra
  have : Algebra.FiniteType Γ(Sp o, ⊤) Γ(M.Z, U.1) := h1
  exact Algebra.FiniteType.isNoetherianRing Γ(Sp o, ⊤) Γ(M.Z, U.1)

/- English proof (translation)
Distinguish the cases in `hww : w = w'`. Substitute `hww` using the available equality. Conclude with `Iff.rfl`. Use `ratModel_isLocallyNoetherian M` as an intermediate fact. Take `⟨V, _, _, _, ξ, G₁, _, _, φ₁, X₁, _, _, _, j, GK, _, ψ, hψ, hξ', hξ, hφ₁, hj, hjt⟩` from `GlobalTheory.T.exists_trait_spreading_torusPart_of_specialisation M.Z G hG w w' hw hww`.

Use `hj` as an intermediate fact. Take `⟨a, ha⟩` from `exists_spMap (ξ ≫ M.s)`. Establish `hG₁ : IsSemiAbelian G₁` using `GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square _ _ ξ G G₁ φ₁ hφ₁ hG`. Establish `hgen : IsGrpPullback GK G (spMap (algebraMap V (FractionRing V)) ≫ ξ) (ψ ≫ φ₁)` using `hψ.comp hφ₁`. Establish `hrX : r = Module.finrank ℤ X₁` using `RkAt.unique hr ⟨X₁, _, inferInstance, inferInstance, FractionRing V, inferInstance, _, GK, inferInstance, _, _, hξ, hgen, hjt, rfl⟩`.

Take `⟨X₀, _, _, _, κ₀, _, s₀, G₀, _, φ₀, t₀, hs₀, hφ₀, ht₀, hrk₀⟩` from `hr'`. Establish `hGc` using `isGrpPullback_pullback_fst (spMap (IsLocalRing.residue V)) G₁`. Establish `hcl : (spMap (IsLocalRing.residue V) ≫ ξ) (closedPoint (IsLocalRing.ResidueField V)) = w'` using `(congrArg (fun x => ξ x) (GtDescent.spMap_cpt (IsLocalRing.residue V))).trans hξ'`. Take `⟨K, _, b₀, b₁, GK', _, ψ₀, ψ₁, -, hψ₀, hψ₁, -⟩` from `exists_common_pullback (hs₀.trans hcl.symm) hφ₀ (hGc.comp hφ₁)`. Establish `hψc : IsGrpPullback GK' G₁ (spMap (b₁.comp (IsLocalRing.residue V))) (ψ₁ ≫ pullback.fst G₁.hom (spMap (IsLocalRing.residue V)))`.

Rewrite using `[← spMap_comp']`. Conclude with `hψ₁.comp hGc`. Establish `ht0 : IsTorPart (pullTorus hψc j)` using `GlobalTheory.T.splitTorusPart_generic_fibre_closed_fibre_dvr V G₁ hG₁ X₁ j hj GK ψ hψ hjt K (b₁.comp (IsLocalRing.residue V)) inferInstance GK' _ hψc X₀ _ (ht₀.pull hψ₀) (hrk₀.trans hrX)`. Establish `hsc : (spMap (b₁.comp (IsLocalRing.residue V)) ≫ ξ) (closedPoint K) = w'` using `(congrArg (fun x => ξ x) (GtDescent.spMap_cpt (b₁.comp (IsLocalRing.residue V)))).trans hξ'`. Establish `ha_gen : (spMap (algebraMap V (FractionRing V)) ≫ ξ) ≫ M.s = spMap ((algebraMap V (FractionRing V)).comp a)`.

Rewrite using `[Category.assoc, ha, spMap_comp']`. Establish `ha_cl : (spMap (b₁.comp (IsLocalRing.residue V)) ≫ ξ) ≫ M.s = spMap ((b₁.comp (IsLocalRing.residue V)).comp a)`. Rewrite using `[Category.assoc, ha, spMap_comp']`. Establish `hextV : ∀ t, ExtNear (gγ t) (ξ (closedPoint V))`. Rewrite using `[hξ']`.

Conclude with `hext`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨e, K₂, _, b₂, GK₂, _, ψ₂, hψ₂, hc⟩` from `h.transfer hξ ha_gen hgen hjt`. Establish `hψ₂' : IsGrpPullback GK₂ G₁ (spMap (b₂.comp (algebraMap V (FractionRing V)))) (ψ₂ ≫ ψ)`.

Rewrite using `[← spMap_comp']`. Conclude with `hψ₂.comp hψ`. Establish `hinj : Function.Injective (b₂.comp (algebraMap V (FractionRing V)))` using `b₂.injective.comp (IsFractionRing.injective V (FractionRing V))`. Establish `hcV : Compat f gγ ζ L m c ξ a φ₁ (torusMap _ e.toAddMonoidHom ≫ j)`. Use `GlobalTheory.T.torusCompat_of_compat_over_field o Ω M G hG I T f gγ ζ L hL hζ X m c V ξ a G₁ φ₁ hφ₁ _ hextV K₂ _ hinj GK₂ _ hψ₂' ?_` and prove the remaining obligations.

Rewrite using `[pullTorus_torusMap_comp, ← pullTorus_pullTorus hψ₂ hψ hψ₂' (spMap_comp' _ _).symm rfl, ← spMap_comp']`. Simplify `hc` using `only [Category.assoc, RingHom.comp_assoc]`. Establish `hc2` using `hcV.pull (b₁.comp (IsLocalRing.residue V)) hψc`. Rewrite `hc2` using `[pullTorus_torusMap_comp]`. Conclude with `⟨K, _, _, _, GK', _, _, _, hsc, ha_cl, hψc.comp hφ₁, ht0.equiv e, hc2⟩`.

Introduce `h`. Take `⟨e, K₂, _, b₂, GK₂, _, ψ₂, hψ₂, hc⟩` from `h.transfer hsc ha_cl (hψc.comp hφ₁) ht0`. Establish `hψ₃ : IsGrpPullback GK₂ G₁ (spMap (b₂.comp (b₁.comp (IsLocalRing.residue V)))) (ψ₂ ≫ ψ₁ ≫ pullback.fst G₁.hom (spMap (IsLocalRing.residue V)))`. Rewrite using `[← spMap_comp']`. Conclude with `hψ₂.comp hψc`.

Establish `hcV : Compat f gγ ζ L m c ξ a φ₁ (torusMap _ e.toAddMonoidHom ≫ j)`. Use `GlobalTheory.T.torusCompat_of_compat_closedPoint o Ω M G hG I T f gγ ζ L hL hζ hu hf hγ X m c V ξ a G₁ φ₁ hφ₁ _ inferInstance hextV GK ψ hψ ?_ K₂ _ inferInstance GK₂ _ hψ₃ ?_ ?_` and prove the remaining obligations. Rewrite using `[pullTorus_torusMap_comp]`. Conclude with `hjt.equiv e`. Rewrite using `[pullTorus_torusMap_comp, ← pullTorus_pullTorus hψ₂ hψc hψ₃ (spMap_comp' _ _).symm rfl]`.

Conclude with `(ht0.pull hψ₂).equiv e`. Rewrite using `[pullTorus_torusMap_comp, ← pullTorus_pullTorus hψ₂ hψc hψ₃ (spMap_comp' _ _).symm rfl, ← spMap_comp']`. Simplify `hc` using `only [Category.assoc, RingHom.comp_assoc]`. Establish `hc3` using `hcV.pull (algebraMap V (FractionRing V)) hψ`. Rewrite `hc3` using `[pullTorus_torusMap_comp]`.

Conclude with `⟨FractionRing V, _, _, _, GK, _, _, _, hξ, ha_gen, hgen, hjt.equiv e, hc3⟩`.
-/
theorem latAt_iff_of_specializes [IsNoetherianRing o] [IsCommMonObj G] (hG : IsSemiAbelian G) (hL : 0 < L) (hζ : ζ ^ L = 1)
    (hu : IsUnit (L : o)) (hf : ∀ e, IsMonHom (f e)) (hγ : ∀ t, gγ t ^ L = 1) {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (m : I → X →+ X) (c : T → X →+ ZMod L) {w w' : M.Z} (hw : w ⤳ w') {r : ℕ}
    (hr : RkAt G w r) (hr' : RkAt G w' r) (hext : ∀ t, ExtNear (gγ t) w') :
    LatAt f gγ ζ L m c w ↔ LatAt f gγ ζ L m c w' := by
  by_cases hww : w = w'
  · subst hww
    exact Iff.rfl
  have := ratModel_isLocallyNoetherian M
  obtain ⟨V, _, _, _, ξ, G₁, _, _, φ₁, X₁, _, _, _, j, GK, _, ψ, hψ, hξ', hξ, hφ₁, hj, hjt⟩ :=
    GlobalTheory.T.exists_trait_spreading_torusPart_of_specialisation M.Z G hG w w' hw hww
  have := hj
  obtain ⟨a, ha⟩ := exists_spMap (ξ ≫ M.s)
  have hG₁ : IsSemiAbelian G₁ := GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square _ _ ξ G G₁ φ₁ hφ₁ hG
  have hgen : IsGrpPullback GK G (spMap (algebraMap V (FractionRing V)) ≫ ξ) (ψ ≫ φ₁) := hψ.comp hφ₁
  have hrX : r = Module.finrank ℤ X₁ :=
    RkAt.unique hr ⟨X₁, _, inferInstance, inferInstance, FractionRing V, inferInstance, _, GK, inferInstance, _, _, hξ,
      hgen, hjt, rfl⟩
  obtain ⟨X₀, _, _, _, κ₀, _, s₀, G₀, _, φ₀, t₀, hs₀, hφ₀, ht₀, hrk₀⟩ := hr'
  have hGc := isGrpPullback_pullback_fst (spMap (IsLocalRing.residue V)) G₁
  have hcl : (spMap (IsLocalRing.residue V) ≫ ξ) (closedPoint (IsLocalRing.ResidueField V)) = w' :=
    (congrArg (fun x => ξ x) (GtDescent.spMap_cpt (IsLocalRing.residue V))).trans hξ'
  obtain ⟨K, _, b₀, b₁, GK', _, ψ₀, ψ₁, -, hψ₀, hψ₁, -⟩ := exists_common_pullback (hs₀.trans hcl.symm) hφ₀ (hGc.comp hφ₁)
  have hψc : IsGrpPullback GK' G₁ (spMap (b₁.comp (IsLocalRing.residue V)))
      (ψ₁ ≫ pullback.fst G₁.hom (spMap (IsLocalRing.residue V))) := by
    rw [← spMap_comp']
    exact hψ₁.comp hGc
  have ht0 : IsTorPart (pullTorus hψc j) :=
    GlobalTheory.T.splitTorusPart_generic_fibre_closed_fibre_dvr V G₁ hG₁ X₁ j hj GK ψ hψ hjt K (b₁.comp (IsLocalRing.residue V)) inferInstance GK' _ hψc X₀ _
      (ht₀.pull hψ₀) (hrk₀.trans hrX)
  have hsc : (spMap (b₁.comp (IsLocalRing.residue V)) ≫ ξ) (closedPoint K) = w' :=
    (congrArg (fun x => ξ x) (GtDescent.spMap_cpt (b₁.comp (IsLocalRing.residue V)))).trans hξ'
  have ha_gen : (spMap (algebraMap V (FractionRing V)) ≫ ξ) ≫ M.s = spMap ((algebraMap V (FractionRing V)).comp a) := by
    rw [Category.assoc, ha, spMap_comp']
  have ha_cl : (spMap (b₁.comp (IsLocalRing.residue V)) ≫ ξ) ≫ M.s = spMap ((b₁.comp (IsLocalRing.residue V)).comp a) := by
    rw [Category.assoc, ha, spMap_comp']
  have hextV : ∀ t, ExtNear (gγ t) (ξ (closedPoint V)) := by
    rw [hξ']
    exact hext
  constructor
  · intro h
    obtain ⟨e, K₂, _, b₂, GK₂, _, ψ₂, hψ₂, hc⟩ := h.transfer hξ ha_gen hgen hjt
    have hψ₂' : IsGrpPullback GK₂ G₁ (spMap (b₂.comp (algebraMap V (FractionRing V)))) (ψ₂ ≫ ψ) := by
      rw [← spMap_comp']
      exact hψ₂.comp hψ
    have hinj : Function.Injective (b₂.comp (algebraMap V (FractionRing V))) :=
      b₂.injective.comp (IsFractionRing.injective V (FractionRing V))
    have hcV : Compat f gγ ζ L m c ξ a φ₁ (torusMap _ e.toAddMonoidHom ≫ j) := by
      refine GlobalTheory.T.torusCompat_of_compat_over_field o Ω M G hG I T f gγ ζ L hL hζ X m c V ξ a G₁ φ₁ hφ₁ _ hextV K₂ _ hinj GK₂ _ hψ₂' ?_
      rw [pullTorus_torusMap_comp, ← pullTorus_pullTorus hψ₂ hψ hψ₂' (spMap_comp' _ _).symm rfl, ← spMap_comp']
      simpa only [Category.assoc, RingHom.comp_assoc] using hc
    have hc2 := hcV.pull (b₁.comp (IsLocalRing.residue V)) hψc
    rw [pullTorus_torusMap_comp] at hc2
    exact ⟨K, _, _, _, GK', _, _, _, hsc, ha_cl, hψc.comp hφ₁, ht0.equiv e, hc2⟩
  · intro h
    obtain ⟨e, K₂, _, b₂, GK₂, _, ψ₂, hψ₂, hc⟩ := h.transfer hsc ha_cl (hψc.comp hφ₁) ht0
    have hψ₃ : IsGrpPullback GK₂ G₁ (spMap (b₂.comp (b₁.comp (IsLocalRing.residue V))))
        (ψ₂ ≫ ψ₁ ≫ pullback.fst G₁.hom (spMap (IsLocalRing.residue V))) := by
      rw [← spMap_comp']
      exact hψ₂.comp hψc
    have hcV : Compat f gγ ζ L m c ξ a φ₁ (torusMap _ e.toAddMonoidHom ≫ j) := by
      refine GlobalTheory.T.torusCompat_of_compat_closedPoint o Ω M G hG I T f gγ ζ L hL hζ hu hf hγ X m c V ξ a G₁ φ₁ hφ₁ _ inferInstance hextV GK ψ hψ
        ?_ K₂ _ inferInstance GK₂ _ hψ₃ ?_ ?_
      · rw [pullTorus_torusMap_comp]
        exact hjt.equiv e
      · rw [pullTorus_torusMap_comp, ← pullTorus_pullTorus hψ₂ hψc hψ₃ (spMap_comp' _ _).symm rfl]
        exact (ht0.pull hψ₂).equiv e
      · rw [pullTorus_torusMap_comp, ← pullTorus_pullTorus hψ₂ hψc hψ₃ (spMap_comp' _ _).symm rfl, ← spMap_comp']
        simpa only [Category.assoc, RingHom.comp_assoc] using hc
    have hc3 := hcV.pull (algebraMap V (FractionRing V)) hψ
    rw [pullTorus_torusMap_comp] at hc3
    exact ⟨FractionRing V, _, _, _, GK, _, _, _, hξ, ha_gen, hgen, hjt.equiv e, hc3⟩

end GlobalTheory.Poinc.FibLat
