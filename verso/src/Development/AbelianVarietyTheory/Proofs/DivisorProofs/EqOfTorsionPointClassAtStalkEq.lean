import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

/- English proof (translation)
Introduce `X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ K _ _ t P Q PT QT hPT hQT x c hcP hcQ`. Use `haveI hEt : Etale (torsion G n).hom := GlobalTheory.GrpTangent.etale_torsion G hn`. Establish `hιT : (torsion.ι G n).left ≫ G.hom = (torsion G n).hom` using `Over.w (torsion.ι G n)`. Establish `hPt : PT ≫ (torsion G n).hom = t`. Rewrite using `[← hιT, ← Category.assoc, hPT]`.

Conclude with `Over.w P`. Establish `hQt : QT ≫ (torsion G n).hom = t`. Rewrite using `[← hιT, ← Category.assoc, hQT]`. Conclude with `Over.w Q`. Take `rfl : x = IsLocalRing.closedPoint K` from `Subsingleton.elim _ _`.

Set `pq : Sp K ⟶ pullback (torsion G n).hom (torsion G n).hom` to `pullback.lift PT QT (hPt.trans hQt.symm)`. Set `q` to `pq (IsLocalRing.closedPoint K)`. Establish `hfq : (pullback.fst (torsion G n).hom (torsion G n).hom) q = PT (IsLocalRing.closedPoint K)` using `by show (pq ≫ pullback.fst (torsion G n).hom (torsion G n).hom) (IsLocalRing.closedPoint K) = _`. Rewrite using `[pullback.lift_fst]`. Establish `hsq : (pullback.snd (torsion G n).hom (torsion G n).hom) q = QT (IsLocalRing.closedPoint K)` using `by show (pq ≫ pullback.snd (torsion G n).hom (torsion G n).hom) (IsLocalRing.closedPoint K) = _`.

Rewrite using `[pullback.lift_snd]`. Use `haveI hdom : IsDomain ((pullback (torsion G n).hom (torsion G n).hom).presheaf.stalk q) := isDomain_stalk_of_etale (pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom) q`. Set `Wp` to `pullback (torsion G n).hom (torsion G n).hom`. Set `R : Type` to `Wp.presheaf.stalk q`. Set `Ω` to `AlgebraicClosure (FractionRing R)`.

Set `φ : R →+* Ω` to `algebraMap R Ω`. Establish `hφ : Function.Injective φ`. Establish `e : φ = (algebraMap (FractionRing R) Ω).comp (algebraMap R (FractionRing R))` using `IsScalarTower.algebraMap_eq R (FractionRing R) Ω`. Rewrite using `[e]`. Conclude with `(algebraMap (FractionRing R) Ω).injective.comp (IsFractionRing.injective R (FractionRing R))`.

Set `ybar : Sp Ω ⟶ Spec (Wp.presheaf.stalk q)` to `Spec.map (CommRingCat.ofHom φ)`. Use `haveI hyd : IsDominant ybar := by`. Rewrite using `[isDominant_iff]`. Use `show DenseRange (PrimeSpectrum.comap φ)`. Rewrite using `[PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]`.

Conclude with `bot_le`. Set `s0 : Sp Ω` to `IsLocalRing.closedPoint Ω`. Establish `hgen : ∀ e, ybar s0 ⤳ e`. Introduce `e`. Establish `hr : Set.range ybar = {ybar s0}` using `Set.eq_singleton_iff_unique_mem.mpr ⟨⟨s0, rfl⟩, by rintro _ ⟨s, rfl⟩; rw [Subsingleton.elim s s0]⟩`.

Rewrite using `[specializes_iff_mem_closure, ← hr, ybar.denseRange.closure_range]`. Discharge the goal by the elementary cases of `trivial`. Set `f : Spec (Wp.presheaf.stalk q) ⟶ X'` to `Wp.fromSpecStalk q ≫ pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom`. Take `⟨w', hw'q, hw'ξ⟩` from `Flat.generalizingMap (pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom) (genericPoint_specializes ((pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom) q))`. Establish `hw'r : w' ∈ Set.range (Wp.fromSpecStalk q)` using `by rw [Scheme.range_fromSpecStalk]; exact hw'q`.

Take `⟨d, hd⟩` from `hw'r`. Establish `hξV : genericPoint X' ∈ Set.range ℓ`. Rewrite using `[(genericPoint_spec X').mem_open_set_iff ℓ.isOpenEmbedding.isOpen_range]`. Take `⟨v⟩` from `‹Nonempty V›`. Conclude with `⟨ℓ v, trivial, v, rfl⟩`.

Establish `hsp : (ybar ≫ f) s0 ⤳ genericPoint X'`. Establish `h1` using `(hgen d).map f.continuous`. Establish `e2 : f d = (pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom) w'`. Rewrite using `[← hd]`. Both sides reduce to the same expression.

Rewrite using `[show (ybar ≫ f) s0 = f (ybar s0) from rfl, ← hw'ξ, ← e2]`. Conclude with `h1`. Establish `H : Set.range (ybar ≫ f) ⊆ Set.range ℓ`. Introduce and unpack `_ ⟨s, rfl⟩`. Rewrite using `[Subsingleton.elim s s0]`.

Conclude with `hsp.mem_open ℓ.isOpenEmbedding.isOpen_range hξV`. Set `z : Sp Ω ⟶ V` to `IsOpenImmersion.lift ℓ (ybar ≫ f) H`. Establish `hz : z ≫ ℓ = ybar ≫ f` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hcP' : ValAt G n ℓ w ((pullback.fst (torsion G n).hom (torsion G n).hom) q) c` using `by rw [hfq]; exact hcP`. Establish `hcQ' : ValAt G n ℓ w ((pullback.snd (torsion G n).hom (torsion G n).hom) q) c` using `by rw [hsq]; exact hcQ`.

Establish `k1 : Spec.map ((pullback.fst (torsion G n).hom (torsion G n).hom).stalkMap q) ≫ (torsion G n).left.fromSpecStalk ((pullback.fst (torsion G n).hom (torsion G n).hom) q) = Wp.fromSpecStalk q ≫ pullback.fst (torsion G n).hom (torsion G n).hom` using `Scheme.SpecMap_stalkMap_fromSpecStalk _`. Establish `k2 : Spec.map ((pullback.snd (torsion G n).hom (torsion G n).hom).stalkMap q) ≫ (torsion G n).left.fromSpecStalk ((pullback.snd (torsion G n).hom (torsion G n).hom) q) = Wp.fromSpecStalk q ≫ pullback.snd (torsion G n).hom (torsion G n).hom` using `Scheme.SpecMap_stalkMap_fromSpecStalk _`. Establish `h1` using `hcP' Ω (ybar ≫ Spec.map ((pullback.fst (torsion G n).hom (torsion G n).hom).stalkMap q)) z (by`. Rewrite using `[hz, Category.assoc, reassoc_of% k1])`. Establish `h2` using `hcQ' Ω (ybar ≫ Spec.map ((pullback.snd (torsion G n).hom (torsion G n).hom).stalkMap q)) z (by`.

Rewrite using `[hz, Category.assoc, reassoc_of% k2, ← pullback.condition])`. Rewrite `h1` using `[Category.assoc, reassoc_of% k1]`. Rewrite `h2` using `[Category.assoc, reassoc_of% k2]`. Establish `hu : Wp.fromSpecStalk q ≫ pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left = Wp.fromSpecStalk q ≫ pullback.snd (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left`. Use `ext_of_isDominant_of_isSeparated G.hom ?_ ybar (h1.trans h2.symm)` and prove the remaining obligations.

Simplify using `only [Category.assoc, hιT, pullback.condition]`. Establish `hpq : Spec.map (Scheme.stalkClosedPointTo pq) ≫ Wp.fromSpecStalk q = pq` using `Scheme.Spec_stalkClosedPointTo_fromSpecStalk pq`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[← hPT, ← hQT]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← Category.assoc, pullback.lift_fst]`. Use `_ = Spec.map (Scheme.stalkClosedPointTo pq) ≫ Wp.fromSpecStalk q ≫ pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by`. Rewrite using `[reassoc_of% hpq]`. Use `_ = Spec.map (Scheme.stalkClosedPointTo pq) ≫ Wp.fromSpecStalk q ≫ pullback.snd (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by`. Rewrite using `[hu]`.

Use `_ = QT ≫ (torsion.ι G n).left := by`. Rewrite using `[reassoc_of% hpq, ← Category.assoc, pullback.lift_snd]`.
-/
theorem eq_of_valAt_eq : ∀ {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [IsSeparated G.hom]
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (P Q : Over.mk t ⟶ G)
    (PT QT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hQT : QT ≫ (torsion.ι G n).left = Q.left) (x : Sp K) (c : M) (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) c)
    (hcQ : GlobalTheory.TorsSpec.ValAt G n ℓ w (QT x) c), P = Q := by
  intro X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ K _ _ t P Q PT QT hPT hQT x c hcP hcQ
  haveI hEt : Etale (torsion G n).hom := GlobalTheory.GrpTangent.etale_torsion G hn
  have hιT : (torsion.ι G n).left ≫ G.hom = (torsion G n).hom := Over.w (torsion.ι G n)
  have hPt : PT ≫ (torsion G n).hom = t := by
    rw [← hιT, ← Category.assoc, hPT]; exact Over.w P
  have hQt : QT ≫ (torsion G n).hom = t := by
    rw [← hιT, ← Category.assoc, hQT]; exact Over.w Q
  obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  let pq : Sp K ⟶ pullback (torsion G n).hom (torsion G n).hom := pullback.lift PT QT (hPt.trans hQt.symm)
  let q := pq (IsLocalRing.closedPoint K)
  have hfq : (pullback.fst (torsion G n).hom (torsion G n).hom) q = PT (IsLocalRing.closedPoint K) := by
    show (pq ≫ pullback.fst (torsion G n).hom (torsion G n).hom) (IsLocalRing.closedPoint K) = _
    rw [pullback.lift_fst]
  have hsq : (pullback.snd (torsion G n).hom (torsion G n).hom) q = QT (IsLocalRing.closedPoint K) := by
    show (pq ≫ pullback.snd (torsion G n).hom (torsion G n).hom) (IsLocalRing.closedPoint K) = _
    rw [pullback.lift_snd]
  haveI hdom : IsDomain ((pullback (torsion G n).hom (torsion G n).hom).presheaf.stalk q) :=
    isDomain_stalk_of_etale (pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom) q
  let Wp := pullback (torsion G n).hom (torsion G n).hom
  let R : Type := Wp.presheaf.stalk q
  let Ω := AlgebraicClosure (FractionRing R)
  let φ : R →+* Ω := algebraMap R Ω
  have hφ : Function.Injective φ := by
    have e : φ = (algebraMap (FractionRing R) Ω).comp (algebraMap R (FractionRing R)) :=
      IsScalarTower.algebraMap_eq R (FractionRing R) Ω
    rw [e]
    exact (algebraMap (FractionRing R) Ω).injective.comp (IsFractionRing.injective R (FractionRing R))
  let ybar : Sp Ω ⟶ Spec (Wp.presheaf.stalk q) := Spec.map (CommRingCat.ofHom φ)
  haveI hyd : IsDominant ybar := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap φ)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
    exact bot_le
  let s0 : Sp Ω := IsLocalRing.closedPoint Ω
  have hgen : ∀ e, ybar s0 ⤳ e := by
    intro e
    have hr : Set.range ybar = {ybar s0} := Set.eq_singleton_iff_unique_mem.mpr
      ⟨⟨s0, rfl⟩, by rintro _ ⟨s, rfl⟩; rw [Subsingleton.elim s s0]⟩
    rw [specializes_iff_mem_closure, ← hr, ybar.denseRange.closure_range]
    trivial
  let f : Spec (Wp.presheaf.stalk q) ⟶ X' :=
    Wp.fromSpecStalk q ≫ pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom
  obtain ⟨w', hw'q, hw'ξ⟩ := Flat.generalizingMap (pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom)
    (genericPoint_specializes ((pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom) q))
  have hw'r : w' ∈ Set.range (Wp.fromSpecStalk q) := by rw [Scheme.range_fromSpecStalk]; exact hw'q
  obtain ⟨d, hd⟩ := hw'r
  have hξV : genericPoint X' ∈ Set.range ℓ := by
    rw [(genericPoint_spec X').mem_open_set_iff ℓ.isOpenEmbedding.isOpen_range]
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨ℓ v, trivial, v, rfl⟩
  have hsp : (ybar ≫ f) s0 ⤳ genericPoint X' := by
    have h1 := (hgen d).map f.continuous
    have e2 : f d = (pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion G n).hom) w' := by
      rw [← hd]; rfl
    rw [show (ybar ≫ f) s0 = f (ybar s0) from rfl, ← hw'ξ, ← e2]
    exact h1
  have H : Set.range (ybar ≫ f) ⊆ Set.range ℓ := by
    rintro _ ⟨s, rfl⟩
    rw [Subsingleton.elim s s0]
    exact hsp.mem_open ℓ.isOpenEmbedding.isOpen_range hξV
  let z : Sp Ω ⟶ V := IsOpenImmersion.lift ℓ (ybar ≫ f) H
  have hz : z ≫ ℓ = ybar ≫ f := IsOpenImmersion.lift_fac _ _ _
  have hcP' : ValAt G n ℓ w ((pullback.fst (torsion G n).hom (torsion G n).hom) q) c := by rw [hfq]; exact hcP
  have hcQ' : ValAt G n ℓ w ((pullback.snd (torsion G n).hom (torsion G n).hom) q) c := by rw [hsq]; exact hcQ
  have k1 : Spec.map ((pullback.fst (torsion G n).hom (torsion G n).hom).stalkMap q) ≫
      (torsion G n).left.fromSpecStalk ((pullback.fst (torsion G n).hom (torsion G n).hom) q) =
      Wp.fromSpecStalk q ≫ pullback.fst (torsion G n).hom (torsion G n).hom := Scheme.SpecMap_stalkMap_fromSpecStalk _
  have k2 : Spec.map ((pullback.snd (torsion G n).hom (torsion G n).hom).stalkMap q) ≫
      (torsion G n).left.fromSpecStalk ((pullback.snd (torsion G n).hom (torsion G n).hom) q) =
      Wp.fromSpecStalk q ≫ pullback.snd (torsion G n).hom (torsion G n).hom := Scheme.SpecMap_stalkMap_fromSpecStalk _
  have h1 := hcP' Ω (ybar ≫ Spec.map ((pullback.fst (torsion G n).hom (torsion G n).hom).stalkMap q)) z (by
    rw [hz, Category.assoc, reassoc_of% k1])
  have h2 := hcQ' Ω (ybar ≫ Spec.map ((pullback.snd (torsion G n).hom (torsion G n).hom).stalkMap q)) z (by
    rw [hz, Category.assoc, reassoc_of% k2, ← pullback.condition])
  rw [Category.assoc, reassoc_of% k1] at h1
  rw [Category.assoc, reassoc_of% k2] at h2
  have hu : Wp.fromSpecStalk q ≫ pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left =
      Wp.fromSpecStalk q ≫ pullback.snd (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by
    refine ext_of_isDominant_of_isSeparated G.hom ?_ ybar (h1.trans h2.symm)
    simp only [Category.assoc, hιT, pullback.condition]
  have hpq : Spec.map (Scheme.stalkClosedPointTo pq) ≫ Wp.fromSpecStalk q = pq :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk pq
  apply Over.OverMorphism.ext
  rw [← hPT, ← hQT]
  calc PT ≫ (torsion.ι G n).left
      = pq ≫ pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by
        rw [← Category.assoc, pullback.lift_fst]
    _ = Spec.map (Scheme.stalkClosedPointTo pq) ≫ Wp.fromSpecStalk q ≫
          pullback.fst (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by
        rw [reassoc_of% hpq]
    _ = Spec.map (Scheme.stalkClosedPointTo pq) ≫ Wp.fromSpecStalk q ≫
          pullback.snd (torsion G n).hom (torsion G n).hom ≫ (torsion.ι G n).left := by
        rw [hu]
    _ = QT ≫ (torsion.ι G n).left := by
        rw [reassoc_of% hpq, ← Category.assoc, pullback.lift_snd]

end GlobalTheory.TorsSpec
