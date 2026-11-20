import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackKernelBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapCompCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapDescends
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ClosedPol

/- English proof (translation)
Distinguish the cases in `hp : p = ⊥`. Set `K` to `FractionRing R`. Establish `hi : Function.Injective ((PowerSeries.C (R` using `K)).comp (algebraMap R K)) := PowerSeries.C_injective.comp (IsFractionRing.injective R K)`. Use `⟨PowerSeries K, inferInstance, inferInstance, inferInstance, (PowerSeries.C (R := K)).comp (algebraMap R K), ⟨inferInstance, ?_, charZero_of_injective_ringHom hi⟩, hi, ?_⟩` and prove the remaining obligations. Rewrite using `[PowerSeries.maximalIdeal_eq_span_X] infer_instance`.

Rewrite using `[hp, eq_bot_iff]`. Introduce `r hr`. Assume the negation of the conclusion as `h`. Establish `h' : algebraMap R K r ≠ 0` using `fun e => h ((IsFractionRing.to_map_eq_zero_iff).1 e)`. Conclude with `hr ((Ne.isUnit h').map (PowerSeries.C (R := K)))`.

Take `⟨O, _, _, hO, hc, φ, h1, h2⟩` from `exists_complete_discreteValuationRing_of_prime_lt (⊥ : Ideal R) p (bot_lt_iff_ne_bot.2 hp)`. Establish `hi : Function.Injective φ` using `(RingHom.injective_iff_ker_eq_bot φ).2 h1`. Conclude with `⟨O, inferInstance, inferInstance, inferInstance, φ, ⟨hO, hc, charZero_of_injective_ringHom hi⟩, hi, h2⟩`.
-/
theorem exists_cdvr (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (p : Ideal R) [p.IsPrime] :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (φ : R →+* V), CDVR V ∧ Function.Injective φ ∧
      (IsLocalRing.maximalIdeal V).comap φ = p := by
  by_cases hp : p = ⊥
  · let K := FractionRing R
    have hi : Function.Injective ((PowerSeries.C (R := K)).comp (algebraMap R K)) :=
      PowerSeries.C_injective.comp (IsFractionRing.injective R K)
    refine ⟨PowerSeries K, inferInstance, inferInstance, inferInstance, (PowerSeries.C (R := K)).comp (algebraMap R K),
      ⟨inferInstance, ?_, charZero_of_injective_ringHom hi⟩, hi, ?_⟩
    · rw [PowerSeries.maximalIdeal_eq_span_X]
      infer_instance
    · rw [hp, eq_bot_iff]
      intro r hr
      by_contra h
      have h' : algebraMap R K r ≠ 0 := fun e => h ((IsFractionRing.to_map_eq_zero_iff).1 e)
      exact hr ((Ne.isUnit h').map (PowerSeries.C (R := K)))
  · obtain ⟨O, _, _, hO, hc, φ, h1, h2⟩ :=
      exists_complete_discreteValuationRing_of_prime_lt (⊥ : Ideal R) p (bot_lt_iff_ne_bot.2 hp)
    have hi : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 h1
    exact ⟨O, inferInstance, inferInstance, inferInstance, φ, ⟨hO, hc, charZero_of_injective_ringHom hi⟩, hi, h2⟩

/- English proof (translation)
Take `⟨w, hw⟩` from `H`. Conclude with `⟨relAmple_pull h.1 hL hL' ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top S) (fun _ => trivial) hB.1, kTriv_pull h hL hL' ((isGen_iff w).1 hw) hB.2⟩`.
-/
theorem pol_pull {S S' : Scheme.{0}} [IsAffine S] {f : S' ⟶ S} {B : Over S} {B' : Over S'} [GrpObj B] [GrpObj B']
    {φ : B'.left ⟶ B.left} (h : IsGrpPullback B' B f φ) {L : LB B.left} {L' : LB B'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (H : LBIso L' (L.pull φ)) (hB : RelAmple B L ∧ KTriv B L) : RelAmple B' L' ∧ KTriv B' L' := by
  obtain ⟨w, hw⟩ := H
  exact ⟨relAmple_pull h.1 hL hL' ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top S) (fun _ => trivial) hB.1,
    kTriv_pull h hL hL' ((isGen_iff w).1 hw) hB.2⟩

/- English proof (translation)
The claim follows from `LBIso.chartPull (Geo.Tor.chartPullPull L c c rfl) (chartPullLinComb L a (fun _ : PUnit => b) (fun _ => 𝟙 X) (fun _ => 1) c (fun _ => e.trans (Category.comp_id _).symm)) ⟨idIso L, idIso_isGen hL⟩`.
-/
theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y) (c : Z ⟶ X)
    (e : b ≫ a = c) : LBIso (L.pull c) ((L.pull a).pull b) :=
  LBIso.chartPull (Geo.Tor.chartPullPull L c c rfl) (chartPullLinComb L a (fun _ : PUnit => b) (fun _ => 𝟙 X) (fun _ => 1) c
    (fun _ => e.trans (Category.comp_id _).symm)) ⟨idIso L, idIso_isGen hL⟩

/- English proof (translation)
Establish `hp : (RingHom.ker a).IsPrime` using `RingHom.ker_isPrime a`. Set `F` to `FractionRing (A ⧸ RingHom.ker a)`. Set `c : A →+* F` to `(algebraMap (A ⧸ RingHom.ker a) F).comp (Ideal.Quotient.mk _)`. Establish `fac : ∀ {K : Type} [Field K] (d : A →+* K), RingHom.ker a = RingHom.ker d → ∃ i : F →+* K, spMap i ≫ spMap c = spMap d` using `fun {K} _ d hd => by`. Establish `hi : Function.Injective (Ideal.Quotient.lift (RingHom.ker a) d (fun x hx => hd.le hx))` using `RingHom.lift_injective_of_ker_le_ideal _ _ hd.ge`.

Use `⟨IsFractionRing.lift hi, ?_⟩` and prove the remaining obligations. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Use extensionality with `x`. Conclude with `IsFractionRing.lift_algebraMap hi _`.

Use `hB.proper` as an intermediate fact. Use `hB.smooth` as an intermediate fact. Set `B₀` to `(Over.pullback (spMap c)).obj B`. Establish `h₀ : IsGrpPullback B₀ B (spMap c) (pullback.fst _ _)` using `isGrpPullback_pullback B _`. Establish `step : ∀ {K : Type} [Field K] (d : A →+* K) (i : F →+* K), spMap i ≫ spMap c = spMap d → ∀ (C : Over (Spec (CommRingCat.of K))) [GrpObj C] (g : C.left ⟶ B.left), IsGrpPullback C B (spMap d) g → ∃ ψ : C.left ⟶ B₀.left, IsGrpPullback C B₀ (spMap i) ψ ∧ ψ ≫ pullback.fst _ _ = g` using `fun d i e C _ g hg => by`.

Establish `w : g ≫ B.hom = (C.hom ≫ spMap i) ≫ spMap c` using `by rw [hg.1.w, Category.assoc, e]`. Use `⟨pullback.lift g _ w, h₀.cancel (hg.congr e.symm (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _), pullback.lift_fst _ _ _⟩` and prove the remaining obligations. Establish `L₀ : (L.pull (pullback.fst B.hom (spMap c))).IsLB` using `pull_isLB hL _`. Take `⟨i, hi⟩` from `fac a rfl`. Take `⟨j, hj⟩` from `fac b hab`.

Take `⟨ψ, hψ, eψ⟩` from `step a i hi _ _ (isGrpPullback_pullback B (spMap a))`. Take `⟨χ, hχ, eχ⟩` from `step b j hj _ _ hβ`. Establish `: IsProper B₀.hom` using `inferInstanceAs (IsProper (pullback.snd _ _))`. Establish `: Smooth B₀.hom` using `inferInstanceAs (Smooth (pullback.snd _ _))`. Use `(GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension F κ j B₀ B' χ hχ _ L' L₀ hL' (H.trans hL' (pull_isLB hL _) (pull_isLB L₀ _) (lbIso_pull_comp hL _ _ _ eχ)) (MorphismProperty.of_isPullback hβ.1 hB.proper) h.1 h.2).2` as an intermediate fact.

Conclude with `pol_pull hψ L₀ (pull_isLB hL _) (lbIso_pull_comp hL _ _ _ eψ) this`.
-/
theorem pol_of_ker_eq {A k κ : Type} [CommRing A] [Field k] [Field κ] (a : A →+* k) (b : A →+* κ)
    (hab : RingHom.ker a = RingHom.ker b) (B : Over (Spec (CommRingCat.of A))) [GrpObj B] (hB : IsAbelianScheme B)
    {L : LB B.left} (hL : L.IsLB) (B' : Over (Spec (CommRingCat.of κ))) [GrpObj B'] {β : B'.left ⟶ B.left}
    (hβ : IsGrpPullback B' B (spMap b) β) {L' : LB B'.left} (hL' : L'.IsLB) (H : LBIso L' (L.pull β))
    (h : RelAmple B' L' ∧ KTriv B' L') :
    RelAmple ((Over.pullback (spMap a)).obj B) (L.pull (pullback.fst _ (spMap a))) ∧
      KTriv ((Over.pullback (spMap a)).obj B) (L.pull (pullback.fst _ (spMap a))) := by
  have hp : (RingHom.ker a).IsPrime := RingHom.ker_isPrime a
  let F := FractionRing (A ⧸ RingHom.ker a)
  let c : A →+* F := (algebraMap (A ⧸ RingHom.ker a) F).comp (Ideal.Quotient.mk _)
  have fac : ∀ {K : Type} [Field K] (d : A →+* K), RingHom.ker a = RingHom.ker d →
      ∃ i : F →+* K, spMap i ≫ spMap c = spMap d := fun {K} _ d hd => by
    have hi : Function.Injective (Ideal.Quotient.lift (RingHom.ker a) d (fun x hx => hd.le hx)) :=
      RingHom.lift_injective_of_ker_le_ideal _ _ hd.ge
    refine ⟨IsFractionRing.lift hi, ?_⟩
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact IsFractionRing.lift_algebraMap hi _
  have := hB.proper
  have := hB.smooth
  let B₀ := (Over.pullback (spMap c)).obj B
  have h₀ : IsGrpPullback B₀ B (spMap c) (pullback.fst _ _) := isGrpPullback_pullback B _
  have step : ∀ {K : Type} [Field K] (d : A →+* K) (i : F →+* K), spMap i ≫ spMap c = spMap d →
      ∀ (C : Over (Spec (CommRingCat.of K))) [GrpObj C] (g : C.left ⟶ B.left), IsGrpPullback C B (spMap d) g →
      ∃ ψ : C.left ⟶ B₀.left, IsGrpPullback C B₀ (spMap i) ψ ∧ ψ ≫ pullback.fst _ _ = g := fun d i e C _ g hg => by
    have w : g ≫ B.hom = (C.hom ≫ spMap i) ≫ spMap c := by rw [hg.1.w, Category.assoc, e]
    refine ⟨pullback.lift g _ w, h₀.cancel (hg.congr e.symm (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _),
      pullback.lift_fst _ _ _⟩
  have L₀ : (L.pull (pullback.fst B.hom (spMap c))).IsLB := pull_isLB hL _
  obtain ⟨i, hi⟩ := fac a rfl
  obtain ⟨j, hj⟩ := fac b hab
  obtain ⟨ψ, hψ, eψ⟩ := step a i hi _ _ (isGrpPullback_pullback B (spMap a))
  obtain ⟨χ, hχ, eχ⟩ := step b j hj _ _ hβ
  have : IsProper B₀.hom := inferInstanceAs (IsProper (pullback.snd _ _))
  have : Smooth B₀.hom := inferInstanceAs (Smooth (pullback.snd _ _))
  have := (GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension F κ j B₀ B' χ hχ _ L' L₀ hL'
    (H.trans hL' (pull_isLB hL _) (pull_isLB L₀ _) (lbIso_pull_comp hL _ _ _ eχ))
    (MorphismProperty.of_isPullback hβ.1 hB.proper) h.1 h.2).2
  exact pol_pull hψ L₀ (pull_isLB hL _) (lbIso_pull_comp hL _ _ _ eψ) this

/- English proof (translation)
Use `Q.q_hom` as an intermediate fact. Use `Q.i_hom` as an intermediate fact. Use `Q.q_affine` as an intermediate fact. Use `Q.isAb.proper` as an intermediate fact. Establish `: ConnectedSpace (Spec (CommRingCat.of A))` using `SplitTorus.connectedSpace_of_isLocalRing A`.

Take `⟨β, hβ, e⟩` from `GlobalTheory.flatQuotient_iso_of_same_kernel _ G B₁ Q.B _ _ q i Q.q Q.i hq hi inferInstance inferInstance inferInstance ker Q.q_hom Q.i_hom Q.q_flat Q.q_surj inferInstance Q.isKernel (GlobalTheory.splitTorus_hom_proper_trivial_local A X B₁ _ inferInstance) (GlobalTheory.splitToru …`. Establish `hp : IsGrpPullback Q.B B f (β.hom.left ≫ b)` using `((isGrpPullback_of_iso β).comp hb).congr (Category.id_comp _) rfl`. Substitute `e` using the available equality. Establish `key : ∀ (F : G.left ⟶ B.left) (_ : F = Q.q.left ≫ β.hom.left ≫ b) hw w, IsCPMap P M f F hw w → ∃ v, IsCPMap D.M M f _ hp.1.w v`. Introduce and unpack `_ rfl hw w H`.

Conclude with `GlobalTheory.isCPMap_descends _ _ f X G Q P D B M _ hp.1.w hw w (fun T x y => Over.OverMorphism.ext (hp.2 T x y _ _ rfl rfl).symm) H`. Take `⟨v, hv⟩` from `key _ (Category.assoc _ _ _) _ _ H`. Conclude with `pol_pull hp M.L.isLB D.M.L.isLB ⟨v, hv.gen⟩ hM`.
-/
theorem pol_of_second_quotient {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X X' : Type}
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X']
    {G : Over (Spec (CommRingCat.of A))} [GrpObj G] [IsCommMonObj G] [ConnectedSpace G.left] (Q : TQ G X) {P : CP G}
    (D : Q.Desc P) {B₁ : Over (Spec (CommRingCat.of A))} [GrpObj B₁] [IsProper B₁.hom] (q : G ⟶ B₁)
    (i : splitTorus _ X' ⟶ G) [hq : IsMonHom q] [hi : IsMonHom i] [Flat q.left] [Surjective q.left]
    [QuasiCompact q.left] (ker : IsPullback i (toUnit _) q (η[B₁])) {S : Scheme.{0}} [IsAffine S]
    {f : Spec (CommRingCat.of A) ⟶ S} {B : Over S} [GrpObj B] [IsCommMonObj B] (M : CP B) {b : B₁.left ⟶ B.left}
    (hb : IsGrpPullback B₁ B f b) {hw w} (H : IsCPMap P M f (q.left ≫ b) hw w)
    (hM : RelAmple B M.L.L ∧ KTriv B M.L.L) : RelAmple Q.B D.M.L.L ∧ KTriv Q.B D.M.L.L := by
  have := Q.q_hom
  have := Q.i_hom
  have := Q.q_affine
  have := Q.isAb.proper
  have : ConnectedSpace (Spec (CommRingCat.of A)) := SplitTorus.connectedSpace_of_isLocalRing A
  obtain ⟨β, hβ, e⟩ := GlobalTheory.flatQuotient_iso_of_same_kernel _ G B₁ Q.B _ _ q i Q.q Q.i hq hi inferInstance inferInstance
    inferInstance ker Q.q_hom Q.i_hom Q.q_flat Q.q_surj inferInstance Q.isKernel
    (GlobalTheory.splitTorus_hom_proper_trivial_local A X B₁ _ inferInstance)
    (GlobalTheory.splitTorus_hom_proper_trivial_local A X' Q.B _ inferInstance)
  have hp : IsGrpPullback Q.B B f (β.hom.left ≫ b) :=
    ((isGrpPullback_of_iso β).comp hb).congr (Category.id_comp _) rfl
  subst e
  have key : ∀ (F : G.left ⟶ B.left) (_ : F = Q.q.left ≫ β.hom.left ≫ b) hw w, IsCPMap P M f F hw w →
      ∃ v, IsCPMap D.M M f _ hp.1.w v := by
    rintro _ rfl hw w H
    exact GlobalTheory.isCPMap_descends _ _ f X G Q P D B M _ hp.1.w hw w
      (fun T x y => Over.OverMorphism.ext (hp.2 T x y _ _ rfl rfl).symm) H
  obtain ⟨v, hv⟩ := key _ (Category.assoc _ _ _) _ _ H
  exact pol_pull hp M.L.isLB D.M.L.isLB ⟨v, hv.gen⟩ hM

/- English proof (translation)
Use `congrArg LB.Gen.mk (funext fun j => unit_ext fun y hy => ?_)` and prove the remaining obligations. Take `⟨I, hI⟩` from `exists_good_pt hM y`. Conclude with `(gen_trans hu (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y))).trans ((congrArg _ (h y I hI)).trans (gen_trans hu' (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y))).symm)`.
-/
theorem gen_eq_of_val {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {u u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u (𝟙 Y) y J = val u' (𝟙 Y) y J) : u = u' := by
  refine congrArg LB.Gen.mk (funext fun j => unit_ext fun y hy => ?_)
  obtain ⟨I, hI⟩ := exists_good_pt hM y
  exact (gen_trans hu (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y))).trans ((congrArg _ (h y I hI)).trans
    (gen_trans hu' (𝟙 Y) y hy (Good.mem hI φ (𝟙 Y))).symm)

/- English proof (translation)
Take `⟨L, ⟨t, ht, c₁, c₂, c₃, c₄⟩, s, hs, s₁, s₂⟩` from `P`. Take `⟨L', ⟨t', ht', c₁', c₂', c₃', c₄'⟩, s', hs', s₁', s₂'⟩` from `P'`. Take `rfl : L = L'` from `h`. Establish `: Flat (G3 G).hom` using `by show Flat (pullback.fst G.hom (pullback.fst G.hom G.hom ≫ G.hom) ≫ G.hom) infer_instance`. Choose the witnesses or unpack the hypotheses as in `rfl : t = t' := by`.

Set `e : Over.mk (jK R) ⟶ G3 G` to `lift 1 (lift 1 1)`. Use `gen_eq_of_val L.isLB ht ht' (ValueForm.gen_unique_of_injective L.isLB (fun _ _ _ => rfl) (pullback.fst (G3 G).hom (jK R)) (ValueForm.app_generic_injective _) (pullback.snd _ _) (pullback.lift e.left (𝟙 _) ((Over.w e).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _) (Va …` and prove the remaining obligations. Rewrite using `[pullback.lift_fst]`. Conclude with `((isCub_cubV (T := Over.mk (jK R)) ⟨t, ht, c₁, c₂, c₃, c₄⟩ hJ).face 1 1).trans ((isCub_cubV (T := Over.mk (jK R)) ⟨t', ht', c₁', c₂', c₃', c₄'⟩ hJ).face 1 1).symm`. Choose the witnesses or unpack the hypotheses as in `rfl : s = s' := by`.

Set `e : Over.mk (jK R) ⟶ G` to `1`. Establish `sj : Function.Surjective (pullback.snd G.hom (jK R)).appTop.hom`. Establish `hw : gen.hom.left ≫ A.hom = pullback.snd G.hom (jK R)` using `Over.w gen.hom`. Establish `: IsIso gen.hom.left` using `((Over.forget _).mapIso gen).isIso_hom`. Establish `: IsIso gen.hom.left.appTop` using `inferInstanceAs (IsIso (gen.hom.left.app ⊤))`.

Rewrite using `[← hw]`. Conclude with `surj_comp (ConcreteCategory.bijective_of_isIso gen.hom.left.appTop).2 (hG _ _ hA).2`. Use `gen_eq_of_val L.isLB hs hs' (ValueForm.gen_unique_of_injective L.isLB (fun _ _ _ => rfl) (pullback.fst G.hom (jK R)) (ValueForm.app_generic_injective _) (pullback.snd _ _) (pullback.lift e.left (𝟙 _) ((Over.w e).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _) sj hs hs …` and prove the remaining obligations. Rewrite using `[pullback.lift_fst]`. Conclude with `(CP.val_sym_one ⟨L, _, s, hs, s₁, s₂⟩ (T := Over.mk (jK R)) hJ).trans (CP.val_sym_one ⟨L, _, s', hs', s₁', s₂'⟩ (T := Over.mk (jK R)) hJ).symm`.

Both sides reduce to the same expression.
-/
theorem cp_eq (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] [Flat G.hom] {A : Over (Spec (CommRingCat.of (FractionRing R)))} [GrpObj A]
    (hA : IsAbelianScheme A) (gen : (Over.pullback (jK R)).obj G ≅ A) {P P' : CP G} (h : P.L = P'.L) : P = P' := by
  obtain ⟨L, ⟨t, ht, c₁, c₂, c₃, c₄⟩, s, hs, s₁, s₂⟩ := P
  obtain ⟨L', ⟨t', ht', c₁', c₂', c₃', c₄'⟩, s', hs', s₁', s₂'⟩ := P'
  obtain rfl : L = L' := h
  have : Flat (G3 G).hom := by
    show Flat (pullback.fst G.hom (pullback.fst G.hom G.hom ≫ G.hom) ≫ G.hom)
    infer_instance
  obtain rfl : t = t' := by
    let e : Over.mk (jK R) ⟶ G3 G := lift 1 (lift 1 1)
    refine gen_eq_of_val L.isLB ht ht' (ValueForm.gen_unique_of_injective L.isLB (fun _ _ _ => rfl)
      (pullback.fst (G3 G).hom (jK R)) (ValueForm.app_generic_injective _) (pullback.snd _ _)
      (pullback.lift e.left (𝟙 _) ((Over.w e).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _)
      (ValueForm.surjective_cube_baseChange hG _ hA gen) ht ht' (fun y J hJ => ?_) _ _)
    rw [pullback.lift_fst]
    exact ((isCub_cubV (T := Over.mk (jK R)) ⟨t, ht, c₁, c₂, c₃, c₄⟩ hJ).face 1 1).trans
      ((isCub_cubV (T := Over.mk (jK R)) ⟨t', ht', c₁', c₂', c₃', c₄'⟩ hJ).face 1 1).symm
  obtain rfl : s = s' := by
    let e : Over.mk (jK R) ⟶ G := 1
    have sj : Function.Surjective (pullback.snd G.hom (jK R)).appTop.hom := by
      have hw : gen.hom.left ≫ A.hom = pullback.snd G.hom (jK R) := Over.w gen.hom
      have : IsIso gen.hom.left := ((Over.forget _).mapIso gen).isIso_hom
      have : IsIso gen.hom.left.appTop := inferInstanceAs (IsIso (gen.hom.left.app ⊤))
      rw [← hw]
      exact surj_comp (ConcreteCategory.bijective_of_isIso gen.hom.left.appTop).2 (hG _ _ hA).2
    refine gen_eq_of_val L.isLB hs hs' (ValueForm.gen_unique_of_injective L.isLB (fun _ _ _ => rfl)
      (pullback.fst G.hom (jK R)) (ValueForm.app_generic_injective _) (pullback.snd _ _)
      (pullback.lift e.left (𝟙 _) ((Over.w e).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _)
      sj hs hs' (fun y J hJ => ?_) _ _)
    rw [pullback.lift_fst]
    exact (CP.val_sym_one ⟨L, _, s, hs, s₁, s₂⟩ (T := Over.mk (jK R)) hJ).trans
      (CP.val_sym_one ⟨L, _, s', hs', s₁', s₂'⟩ (T := Over.mk (jK R)) hJ).symm
  rfl

/- English proof (translation)
Use `(U.gt e).q_hom` as an intermediate fact. Use `⟨fun T x y => ?_, U.w_gen e, fun T z J' J hJ' hJ W hW => ?_⟩` and prove the remaining obligations. Use `toBase_mul_pullback D.P.A (thick R I e) T (x ≫ (U.gt e).q) (y ≫ (U.gt e).q)` as an intermediate fact. Rewrite `this` using `[← MonObj.mul_comp]`. Establish `a : ∀ x : T ⟶ thickObj R I e G, toBase (Over.w (U.gt e).pG) x = toBase (A` using `D.P.A) (g := pullback.fst D.P.A.hom (thick R I e)) pullback.condition (x ≫ (U.gt e).q) := fun x => Over.OverMorphism.ext (Category.assoc _ _ _).symm`.

Conclude with `(a _).trans (this.trans (congrArg₂ (· * ·) (a x) (a y)).symm)`. Take `⟨N, hN⟩` from `exists_good_pt U.P.L.isLB z`. Take `⟨W₀, hW₀⟩ : ∃ W₀ : (T ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ, ∀ x, W₀ x = gw (U.w e) x.left z (J (x.left ≫ (U.gt e).pG.left)) (fun _ => N (x.left ≫ (fstG I e G).left))` from `⟨_, fun _ => rfl⟩`. Take `⟨V, hV⟩ : ∃ V : (T ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ, ∀ x, V x = gw (pullIso U.P.L.L (pullback.fst G.hom (thick R I e))) x.left z (N (x.left ≫ pullback.fst G.hom (thick R I e))) (J' x.left)` from `⟨_, fun _ => rfl⟩`. Take `⟨a₁, a₂, a₃⟩` from `U.w_vals e T z N J hN hJ W₀ hW₀`.

Take `⟨b₁, b₂, b₃⟩` from `H.vals T z J' N hJ' hN V hV`. Establish `hW' : ∀ x, W x = W₀ x * V x` using `fun x => by`. Establish `g` using `(isGen_iff _).1 (U.w_gen e) _ x.left z (J (x.left ≫ (U.gt e).pG.left)) (J (x.left ≫ (U.gt e).pG.left)) (fun _ => N (x.left ≫ (fstG I e G).left)) (J' x.left) (hJ (x.left ≫ (U.gt e).pG.left)) (hJ (x.left ≫ (U.gt e).pG.left)) (mem_pull.2 (hN (x.left ≫ (fstG I e G).left))) (hJ' x.lef …`. Rewrite `g` using `[gm_self D.P.isLB _ z (hJ (x.left ≫ (U.gt e).pG.left)), _root_.one_mul]`. Establish `g' : W₀ x = (V x)⁻¹ * W x` using `(hW₀ x).trans (g.trans (congrArg₂ (fun a b => a⁻¹ * b) (hV x).symm (hW x).symm))`.

Rewrite using `[g', mul_comm, mul_inv_cancel_left]`. Use `⟨?_, fun x => ?_, fun x y u => ?_⟩` and prove the remaining obligations. Rewrite using `[hW', _root_.mul_assoc]`. Conclude with `a₁.trans (congrArg (W₀ 1 * ·) b₁)`. Rewrite using `[hW', hW', ← _root_.mul_assoc, _root_.mul_assoc (W₀ x⁻¹)]`.

Conclude with `(congrArg (· * V x) (a₂ x)).trans ((_root_.mul_assoc _ _ _).trans (congrArg (W₀ x⁻¹ * ·) (b₂ x)))`. Establish `key : ∀ C C' C'' : (T.left.presheaf.stalk z)ˣ, C * W₀ (x * y) * W₀ (x * u) * W₀ (y * u) * W₀ 1 = W₀ (x * y * u) * W₀ x * W₀ y * W₀ u * C' → C' * V (x * y) * V (x * u) * V (y * u) * V 1 = V (x * y * u) * V x * V y * V u * C'' → C * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * …` using `fun C C' C'' a b => by`. Simplify using `only [hW']`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `a'` using `congrArg Additive.ofMul a`.

Establish `b'` using `congrArg Additive.ofMul b`. Simplify using `only [ofMul_mul] at a' b' ⊢`. Take the linear combination `(norm := abel) a' + b'`. Conclude with `key _ _ _ (a₃ x y u) (b₃ x y u)`.
-/
theorem isCPMap_w (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : PreU I D A G) (e : ℕ) {rig hL hr c s h₁ h₂ h₃}
    (H : IsCPMap (G' := thickObj R I e G) ⟨⟨U.P.L.L.pull (pullback.fst G.hom (thick R I e)), rig, hL, hr⟩, c, s, h₁, h₂, h₃⟩
      U.P (thick R I e) (pullback.fst G.hom (thick R I e)) pullback.condition (pullIso _ _)) :
    IsCPMap (G' := thickObj R I e G) ⟨⟨U.P.L.L.pull (pullback.fst G.hom (thick R I e)), rig, hL, hr⟩, c, s, h₁, h₂, h₃⟩
      (CP.ofDegPre hG D) (thick R I e) ((U.gt e).q.left ≫ pullback.fst D.P.A.hom (thick R I e)) (Over.w (U.gt e).pG)
      (U.w e) := by
  have := (U.gt e).q_hom
  refine ⟨fun T x y => ?_, U.w_gen e, fun T z J' J hJ' hJ W hW => ?_⟩
  · have := toBase_mul_pullback D.P.A (thick R I e) T (x ≫ (U.gt e).q) (y ≫ (U.gt e).q)
    rw [← MonObj.mul_comp] at this
    have a : ∀ x : T ⟶ thickObj R I e G, toBase (Over.w (U.gt e).pG) x =
        toBase (A := D.P.A) (g := pullback.fst D.P.A.hom (thick R I e)) pullback.condition (x ≫ (U.gt e).q) :=
      fun x => Over.OverMorphism.ext (Category.assoc _ _ _).symm
    exact (a _).trans (this.trans (congrArg₂ (· * ·) (a x) (a y)).symm)
  obtain ⟨N, hN⟩ := exists_good_pt U.P.L.isLB z
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : (T ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ, ∀ x, W₀ x = gw (U.w e) x.left z
    (J (x.left ≫ (U.gt e).pG.left)) (fun _ => N (x.left ≫ (fstG I e G).left)) := ⟨_, fun _ => rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : (T ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ, ∀ x, V x =
    gw (pullIso U.P.L.L (pullback.fst G.hom (thick R I e))) x.left z
      (N (x.left ≫ pullback.fst G.hom (thick R I e))) (J' x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨a₁, a₂, a₃⟩ := U.w_vals e T z N J hN hJ W₀ hW₀
  obtain ⟨b₁, b₂, b₃⟩ := H.vals T z J' N hJ' hN V hV
  have hW' : ∀ x, W x = W₀ x * V x := fun x => by
    have g := (isGen_iff _).1 (U.w_gen e) _ x.left z (J (x.left ≫ (U.gt e).pG.left)) (J (x.left ≫ (U.gt e).pG.left))
      (fun _ => N (x.left ≫ (fstG I e G).left)) (J' x.left) (hJ (x.left ≫ (U.gt e).pG.left))
      (hJ (x.left ≫ (U.gt e).pG.left)) (mem_pull.2 (hN (x.left ≫ (fstG I e G).left))) (hJ' x.left)
    rw [gm_self D.P.isLB _ z (hJ (x.left ≫ (U.gt e).pG.left)), _root_.one_mul] at g
    have g' : W₀ x = (V x)⁻¹ * W x := (hW₀ x).trans (g.trans (congrArg₂ (fun a b => a⁻¹ * b) (hV x).symm (hW x).symm))
    rw [g', mul_comm, mul_inv_cancel_left]
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · rw [hW', _root_.mul_assoc]
    exact a₁.trans (congrArg (W₀ 1 * ·) b₁)
  · rw [hW', hW', ← _root_.mul_assoc, _root_.mul_assoc (W₀ x⁻¹)]
    exact (congrArg (· * V x) (a₂ x)).trans ((_root_.mul_assoc _ _ _).trans (congrArg (W₀ x⁻¹ * ·) (b₂ x)))
  · have key : ∀ C C' C'' : (T.left.presheaf.stalk z)ˣ,
        C * W₀ (x * y) * W₀ (x * u) * W₀ (y * u) * W₀ 1 = W₀ (x * y * u) * W₀ x * W₀ y * W₀ u * C' →
        C' * V (x * y) * V (x * u) * V (y * u) * V 1 = V (x * y * u) * V x * V y * V u * C'' →
        C * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * C'' := fun C C' C'' a b => by
      simp only [hW']
      apply Additive.ofMul.injective
      have a' := congrArg Additive.ofMul a
      have b' := congrArg Additive.ofMul b
      simp only [ofMul_mul] at a' b' ⊢
      linear_combination (norm := abel) a' + b'
    exact key _ _ _ (a₃ x y u) (b₃ x y u)

/- English proof (translation)
Substitute `e e'` using the available equality. Conclude with `⟨w, h⟩`.
-/
theorem cpMap_congr {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {P : CP G} {P' : CP G'} {f f' : S' ⟶ S} {F F' : G'.left ⟶ G.left} (e : f = f') (e' : F = F')
    {hw w} (h : IsCPMap P' P f F hw w) (hw') : ∃ w', IsCPMap P' P f' F' hw' w' := by
  subst e e'
  exact ⟨w, h⟩

/- English proof (translation)
Take `⟨D, U₀, hL, -, -⟩` from `hU V A G s`. Take `⟨w, hw⟩` from `U₀.ext`. Use `s.cdvr.1` as an intermediate fact. Use `s.semi.smooth` as an intermediate fact. Use `s.semi.geomConnected` as an intermediate fact.

Set `U` to `ValueForm.toPreU U₀.toUnifPre laws.globalFns s.semi w hw`. Establish `hP : U.P = s.P` using `cp_eq laws.globalFns A.isAb s.gen hL`. Take `⟨w₀, h₀⟩ : IsLevelCP _ 0 s.P₀ U.P` from `hP ▸ s.lev₀`. Take `⟨rig, hr, c, σ, h₁, h₂, h₃, H⟩` from `exists_isCPMap U.P (toBase_mul_pullback G (thick V _ 0)) _ (pull_isLB U.P.L.isLB _) _ (pullIso_isGen U.P.L.isLB (pullback.fst G.hom (thick V (IsLocalRing.maximalIdeal V) 0)))`. Take `⟨w₁, k₁⟩` from `cpMap_congr (Category.id_comp _).symm (Category.id_comp _).symm h₀ (by rw [Category.id_comp, Category.id_comp]; exact pullback.condition)`.

Take `⟨w₂, k₂, -⟩` from `(isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ s.P₀ _ _ _ (𝟙 _) (by simp) _ H).2 (toBase_mul_of_isMonHom (𝟙 _) _) w₁ k₁`. Establish `H'` using `isCPMap_w laws.globalFns U 0 H`. Take `⟨w₃, -, k₃⟩` from `H'.exists_comp k₂ (by rw [Category.id_comp, Category.id_comp]; exact Over.w (U.gt 0).pG)`. Take `⟨w₄, k₄⟩` from `cpMap_congr (Category.id_comp _) (Category.id_comp _) k₃ (Over.w (U.gt 0).pG)`. Establish `: IsLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1))`.

Establish `: Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1))` using `Ideal.Quotient.nontrivial_iff.2 (by`. Rewrite using `[zero_add, pow_one]`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal V).ne_top)`. Use the proof step `.of_surjective' _ Ideal.Quotient.mk_surjective`. Use `SplitTorus.connectedSpace_of_isLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1))` as an intermediate fact.

Establish `: ConnectedSpace (Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1))))` using `this`. Establish `: Smooth (thickObj V (IsLocalRing.maximalIdeal V) 0 G).hom` using `inferInstanceAs (Smooth (pullback.snd _ _))`. Establish `: GeometricallyConnected (thickObj V (IsLocalRing.maximalIdeal V) 0 G).hom` using `inferInstanceAs (GeometricallyConnected (pullback.snd _ _))`. Establish `: ConnectedSpace (thickObj V (IsLocalRing.maximalIdeal V) 0 G).left` using `GeometricallyConnected.connectedSpace _ (thickObj V (IsLocalRing.maximalIdeal V) 0 G).hom.isOpenMap`. Use `D.toPre.P.isAb.proper` as an intermediate fact.

Establish `: IsProper (thickObj V (IsLocalRing.maximalIdeal V) 0 D.toPre.P.A).hom` using `inferInstanceAs (IsProper (pullback.snd _ _))`. Use `(U.gt 0).q_hom` as an intermediate fact. Use `(U.gt 0).i_hom` as an intermediate fact. Use `(U.gt 0).q_flat` as an intermediate fact. Use `(U.gt 0).q_surj` as an intermediate fact.

Use `(U.gt 0).q_affine` as an intermediate fact. Conclude with `pol_of_second_quotient s.Q₀ D₀ (U.gt 0).q (U.gt 0).i (U.gt 0).isKernel (CP.ofDegPre laws.globalFns D.toPre) (isGrpPullback_pullback _ _) k₄ ⟨D.toPre.P.ample, D.toPre.P.ktriv⟩`.
-/
theorem pol_dvr (laws : Laws) (hU : USt) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
    [IsCommMonObj G] (s : HidaSetting V A G) (D₀ : s.Q₀.Desc s.P₀) :
    RelAmple s.Q₀.B D₀.M.L.L ∧ KTriv s.Q₀.B D₀.M.L.L := by
  obtain ⟨D, U₀, hL, -, -⟩ := hU V A G s
  obtain ⟨w, hw⟩ := U₀.ext
  have := s.cdvr.1
  have := s.semi.smooth
  have := s.semi.geomConnected
  let U := ValueForm.toPreU U₀.toUnifPre laws.globalFns s.semi w hw
  have hP : U.P = s.P := cp_eq laws.globalFns A.isAb s.gen hL
  obtain ⟨w₀, h₀⟩ : IsLevelCP _ 0 s.P₀ U.P := hP ▸ s.lev₀
  obtain ⟨rig, hr, c, σ, h₁, h₂, h₃, H⟩ := exists_isCPMap U.P (toBase_mul_pullback G (thick V _ 0)) _
    (pull_isLB U.P.L.isLB _) _ (pullIso_isGen U.P.L.isLB (pullback.fst G.hom (thick V (IsLocalRing.maximalIdeal V) 0)))
  obtain ⟨w₁, k₁⟩ := cpMap_congr (Category.id_comp _).symm (Category.id_comp _).symm h₀
    (by rw [Category.id_comp, Category.id_comp]; exact pullback.condition)
  obtain ⟨w₂, k₂, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ s.P₀ _ _ _ (𝟙 _) (by simp) _ H).2
    (toBase_mul_of_isMonHom (𝟙 _) _) w₁ k₁
  have H' := isCPMap_w laws.globalFns U 0 H
  obtain ⟨w₃, -, k₃⟩ := H'.exists_comp k₂ (by rw [Category.id_comp, Category.id_comp]; exact Over.w (U.gt 0).pG)
  obtain ⟨w₄, k₄⟩ := cpMap_congr (Category.id_comp _) (Category.id_comp _) k₃ (Over.w (U.gt 0).pG)
  have : IsLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) :=
    have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 (by
      rw [zero_add, pow_one]; exact (IsLocalRing.maximalIdeal.isMaximal V).ne_top)
    .of_surjective' _ Ideal.Quotient.mk_surjective
  have := SplitTorus.connectedSpace_of_isLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1))
  have : ConnectedSpace (Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)))) := this
  have : Smooth (thickObj V (IsLocalRing.maximalIdeal V) 0 G).hom := inferInstanceAs (Smooth (pullback.snd _ _))
  have : GeometricallyConnected (thickObj V (IsLocalRing.maximalIdeal V) 0 G).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd _ _))
  have : ConnectedSpace (thickObj V (IsLocalRing.maximalIdeal V) 0 G).left :=
    GeometricallyConnected.connectedSpace _ (thickObj V (IsLocalRing.maximalIdeal V) 0 G).hom.isOpenMap
  have := D.toPre.P.isAb.proper
  have : IsProper (thickObj V (IsLocalRing.maximalIdeal V) 0 D.toPre.P.A).hom :=
    inferInstanceAs (IsProper (pullback.snd _ _))
  have := (U.gt 0).q_hom
  have := (U.gt 0).i_hom
  have := (U.gt 0).q_flat
  have := (U.gt 0).q_surj
  have := (U.gt 0).q_affine
  exact pol_of_second_quotient s.Q₀ D₀ (U.gt 0).q (U.gt 0).i (U.gt 0).isKernel (CP.ofDegPre laws.globalFns D.toPre)
    (isGrpPullback_pullback _ _) k₄ ⟨D.toPre.P.ample, D.toPre.P.ktriv⟩

/- English proof (translation)
Establish `h` using `isGrpPullback_pullback G f`. Set `U` to `pushPt h.1.w (𝟙 ((Over.pullback f).obj G))`. Use `LBIso.chartPull (Geo.Tor.chartPullPull L _ U.left (Category.id_comp _)) (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) H` and prove the remaining obligations. Use `fin_cases i`. Simplify using `[U]`.

Conclude with `Over.OverMorphism.ext ((pullback.lift_fst _ _ _).trans (congrArg (· ≫ w.left) (Category.id_comp _).symm))`.
-/
theorem prim_pull {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} {w : G ⟶ G}
    (H : LBIso L (cubeLB G ![𝟙 G, w] L)) : LBIso (L.pull (pullback.fst G.hom f))
      (cubeLB ((Over.pullback f).obj G) ![𝟙 _, (Over.pullback f).map w] (L.pull (pullback.fst G.hom f))) := by
  have h := isGrpPullback_pullback G f
  let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj G))
  refine LBIso.chartPull (Geo.Tor.chartPullPull L _ U.left (Category.id_comp _))
    (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) H
  fin_cases i
  · simp [U]
  · exact Over.OverMorphism.ext ((pullback.lift_fst _ _ _).trans (congrArg (· ≫ w.left) (Category.id_comp _).symm))

end GlobalTheory.ClosedPol

end
