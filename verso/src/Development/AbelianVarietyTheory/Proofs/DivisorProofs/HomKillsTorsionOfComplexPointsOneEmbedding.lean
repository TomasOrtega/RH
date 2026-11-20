import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulAFiniteFlatSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeIdPowFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne
open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.TorsionKill

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `GlobalTheory.KernelNoTorsion.eq_of_isSchemeTheoreticallyDominant X.hom ((Over.w a).trans (Over.w b).symm) (pullback.fst Y.hom t) ?_` and prove the remaining obligations. Establish `h'` using `congr(($h).left ≫ pullback.fst X.hom t)`. Conclude with `(pullback.lift_fst _ _ _).symm.trans (h'.trans (pullback.lift_fst _ _ _))`.
-/
theorem eq_of_pullback_eq {S S' : Scheme.{0}} (t : S' ⟶ S) [IsSchemeTheoreticallyDominant t]
    [QuasiCompact t] {Y X : Over S} [Flat Y.hom] [IsSeparated X.hom] {a b : Y ⟶ X}
    (h : (Over.pullback t).map a = (Over.pullback t).map b) : a = b := by
  apply Over.OverMorphism.ext
  refine GlobalTheory.KernelNoTorsion.eq_of_isSchemeTheoreticallyDominant X.hom ((Over.w a).trans (Over.w b).symm)
    (pullback.fst Y.hom t) ?_
  have h' := congr(($h).left ≫ pullback.fst X.hom t)
  exact (pullback.lift_fst _ _ _).symm.trans (h'.trans (pullback.lift_fst _ _ _))

/- English proof (translation)
Establish `: IsDominant (spMap (σ.comp (algebraMap (𝓞 K) K)))`. Rewrite using `[isDominant_iff]`. Use `(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_` and prove the remaining obligations. Establish `hinj : Function.Injective (σ.comp (algebraMap (𝓞 K) K))`. Rewrite using `[RingHom.coe_comp]`.

Conclude with `σ.injective.comp (IsFractionRing.injective (𝓞 K) K)`. Conclude with `((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le`. Conclude with `IsSchemeTheoreticallyDominant.of_isDominant _`.
-/
theorem isSchemeTheoreticallyDominant_complexPoint (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) :
    IsSchemeTheoreticallyDominant (spMap (σ.comp (algebraMap (𝓞 K) K))) := by
  have : IsDominant (spMap (σ.comp (algebraMap (𝓞 K) K))) := by
    rw [isDominant_iff]
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_
    have hinj : Function.Injective (σ.comp (algebraMap (𝓞 K) K)) := by
      rw [RingHom.coe_comp]; exact σ.injective.comp (IsFractionRing.injective (𝓞 K) K)
    exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
  exact IsSchemeTheoreticallyDominant.of_isDominant _

/- English proof (translation)
Establish `hf` using `(GlobalTheory.PairKernel.mulA_finite_flat_surjective S P m hm).2.1`. Establish `hp` using `(IsPullback.of_hasPullback (𝟙 P.A ^ m) η[P.A]).map (Over.forget S)`. Establish `he : Flat (pullback.snd (𝟙 P.A ^ m) η[P.A]).left` using `MorphismProperty.of_isPullback (P := @Flat) hp hf`. Establish `hw : (pullback.snd (𝟙 P.A ^ m) η[P.A]).left = (pullback (𝟙 P.A ^ m) η[P.A]).hom`. Simplify using `using Over.w (pullback.snd (𝟙 P.A ^ m) η[P.A])`.

Rewrite `he` using `[hw]`. Then use the resulting hypothesis.
-/
theorem flat_ker (S : Scheme.{0}) (P : Out.PolAV S) (m : ℕ) (hm : 1 ≤ m) :
    Flat (pullback (𝟙 P.A ^ m) η[P.A]).hom := by
  have hf := (GlobalTheory.PairKernel.mulA_finite_flat_surjective S P m hm).2.1
  have hp := (IsPullback.of_hasPullback (𝟙 P.A ^ m) η[P.A]).map (Over.forget S)
  have he : Flat (pullback.snd (𝟙 P.A ^ m) η[P.A]).left :=
    MorphismProperty.of_isPullback (P := @Flat) hp hf
  have hw : (pullback.snd (𝟙 P.A ^ m) η[P.A]).left = (pullback (𝟙 P.A ^ m) η[P.A]).hom := by
    simpa using Over.w (pullback.snd (𝟙 P.A ^ m) η[P.A])
  rwa [hw] at he

/- English proof (translation)
Establish `hunit : IsUnit ((N : ℕ) : Γ(Sp ℂ, ⊤))`. Use `(IsUnit.mk0 (N : ℂ) (by exact_mod_cast (show N ≠ 0 by omega))).map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Take `⟨-, -, het, -⟩` from `abelianScheme_id_pow_finite_etale_surjective _ A' N hA hunit`. Establish `hp` using `(IsPullback.of_hasPullback ((𝟙 A' ^ N)) η[A']).map (Over.forget (Sp ℂ))`.

Establish `he : Etale (pullback.snd ((𝟙 A' ^ N)) η[A']).left` using `MorphismProperty.of_isPullback (P := @Etale) hp het`. Establish `hw : (pullback.snd ((𝟙 A' ^ N)) η[A']).left = (pullback (𝟙 A' ^ N) η[A']).hom`. Simplify using `using Over.w (pullback.snd ((𝟙 A' ^ N)) η[A'])`. Rewrite `he` using `[hw]`. Establish `: IsReduced (pullback (𝟙 A' ^ N) η[A']).left` using `GlobalTheory.isReduced_of_smooth_of_isReduced (pullback (𝟙 A' ^ N) η[A']).hom`.

Use `Over.OverMorphism.ext ?_` and prove the remaining obligations. Establish `: LocallyOfFiniteType ((pullback.fst (𝟙 A' ^ N) η[A'] ≫ φ).left ≫ B'.hom)`. Rewrite using `[Over.w]`. Use `infer_instance`. Use `ext_of_apply_eq B'.hom Set.univ isClosed_univ.isLocallyClosed dense_univ (fun z _ hz => ?_) ((Over.w _).trans (Over.w _).symm)` and prove the remaining obligations.

Set `p : Over.mk (𝟙 (Sp ℂ)) ⟶ pullback (𝟙 A' ^ N) η[A']` to `Over.homMk (pointOfClosedPoint (pullback (𝟙 A' ^ N) η[A']).hom z hz) (pointOfClosedPoint_comp _ _ _)`. Establish `e` using `h p`. Establish `e'` using `congrArg (fun q => q.left (IsLocalRing.closedPoint ℂ)) e`. Establish `hz' : p.left (IsLocalRing.closedPoint ℂ) = z` using `pointOfClosedPoint_apply _ z hz _`. Simplify using `only [Over.comp_left] at e'`.

Rewrite using `[← hz']`. Conclude with `e'`.
-/
theorem kill_complex (A' B' : Over (Sp ℂ)) [GrpObj A'] [GrpObj B'] (hA : IsAbelianScheme A')
    [IsSeparated B'.hom] [LocallyOfFiniteType B'.hom] (N : ℕ) (hN : 1 ≤ N) (φ : A' ⟶ B')
    (h : ∀ p : Over.mk (𝟙 (Sp ℂ)) ⟶ pullback (𝟙 A' ^ N) η[A'],
      p ≫ pullback.fst (𝟙 A' ^ N) η[A'] ≫ φ = p ≫ 1) :
    pullback.fst (𝟙 A' ^ N) η[A'] ≫ φ = 1 := by
  have hunit : IsUnit ((N : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have := (IsUnit.mk0 (N : ℂ) (by exact_mod_cast (show N ≠ 0 by omega))).map
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨-, -, het, -⟩ := abelianScheme_id_pow_finite_etale_surjective _ A' N hA hunit
  have hp := (IsPullback.of_hasPullback ((𝟙 A' ^ N)) η[A']).map (Over.forget (Sp ℂ))
  have he : Etale (pullback.snd ((𝟙 A' ^ N)) η[A']).left :=
    MorphismProperty.of_isPullback (P := @Etale) hp het
  have hw : (pullback.snd ((𝟙 A' ^ N)) η[A']).left = (pullback (𝟙 A' ^ N) η[A']).hom := by
    simpa using Over.w (pullback.snd ((𝟙 A' ^ N)) η[A'])
  rw [hw] at he
  have : IsReduced (pullback (𝟙 A' ^ N) η[A']).left :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback (𝟙 A' ^ N) η[A']).hom
  refine Over.OverMorphism.ext ?_
  have : LocallyOfFiniteType ((pullback.fst (𝟙 A' ^ N) η[A'] ≫ φ).left ≫ B'.hom) := by
    rw [Over.w]; infer_instance
  refine ext_of_apply_eq B'.hom Set.univ isClosed_univ.isLocallyClosed dense_univ (fun z _ hz => ?_)
    ((Over.w _).trans (Over.w _).symm)
  let p : Over.mk (𝟙 (Sp ℂ)) ⟶ pullback (𝟙 A' ^ N) η[A'] :=
    Over.homMk (pointOfClosedPoint (pullback (𝟙 A' ^ N) η[A']).hom z hz) (pointOfClosedPoint_comp _ _ _)
  have e := h p
  have e' := congrArg (fun q => q.left (IsLocalRing.closedPoint ℂ)) e
  have hz' : p.left (IsLocalRing.closedPoint ℂ) = z := pointOfClosedPoint_apply _ z hz _
  simp only [Over.comp_left] at e'
  rw [← hz']
  exact e'

end GlobalTheory.TorsionKill

noncomputable section
namespace GlobalTheory.TorsionKill

def ptOf {S : Scheme.{0}} (t : Sp ℂ ⟶ S) {A : Over S}
    (y : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback t).obj A) : Over.mk t ⟶ A :=
  Over.homMk (y.left ≫ pullback.fst A.hom t) (by
    have hy : y.left ≫ pullback.snd A.hom t = 𝟙 _ := by simpa using Over.w y
    simp only [Over.mk_hom, Category.assoc, pullback.condition, reassoc_of% hy, Category.id_comp])

/- English proof (translation)
Use `ext`. Simplify using `[ptOf, pullback.lift_fst]`.
-/
theorem ptOf_comp {S : Scheme.{0}} (t : Sp ℂ ⟶ S) {A B : Over S}
    (y : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback t).obj A) (f : A ⟶ B) :
    ptOf t (y ≫ (Over.pullback t).map f) = ptOf t y ≫ f := by
  ext
  simp [ptOf, pullback.lift_fst]

/- English proof (translation)
Introduce `y y' h`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `pullback.hom_ext` to reduce the goal to its premises. Conclude with `congrArg (fun q => q.left) h`. Establish `hy : y.left ≫ pullback.snd A.hom t = 𝟙 _` using `by simpa using Over.w y`.

Establish `hy' : y'.left ≫ pullback.snd A.hom t = 𝟙 _` using `by simpa using Over.w y'`. Rewrite using `[hy, hy']`.
-/
theorem ptOf_injective {S : Scheme.{0}} (t : Sp ℂ ⟶ S) {A : Over S} :
    Function.Injective (ptOf t (A := A)) := by
  intro y y' h
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg (fun q => q.left) h
  · have hy : y.left ≫ pullback.snd A.hom t = 𝟙 _ := by simpa using Over.w y
    have hy' : y'.left ≫ pullback.snd A.hom t = 𝟙 _ := by simpa using Over.w y'
    rw [hy, hy']

/- English proof (translation)
Establish `e : (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback t).obj A) = (toUnit _ ≫ Functor.LaxMonoidal.ε (Over.pullback t)) ≫ (Over.pullback t).map η[A]`. Rewrite using `[Hom.one_def, Category.assoc]`. Both sides reduce to the same expression. Rewrite using `[e, ptOf_comp, Hom.one_def, toUnit_unique (ptOf t _) (toUnit _)]`.
-/
theorem ptOf_one {S : Scheme.{0}} (t : Sp ℂ ⟶ S) {A : Over S} [GrpObj A] :
    ptOf t (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback t).obj A) = 1 := by
  have e : (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback t).obj A) =
      (toUnit _ ≫ Functor.LaxMonoidal.ε (Over.pullback t)) ≫ (Over.pullback t).map η[A] := by
    rw [Hom.one_def, Category.assoc]; rfl
  rw [e, ptOf_comp, Hom.one_def, toUnit_unique (ptOf t _) (toUnit _)]

end GlobalTheory.TorsionKill

noncomputable section
namespace GlobalTheory.TorsionKill

/- English proof (translation)
Introduce `E _ _ _ H K _ _ σ A B G _ m hm hpt T x hx`. Set `inc : pullback (𝟙 A.t.G ^ m) η[A.t.G] ⟶ A.t.G` to `pullback.fst _ _`. It suffices to establish `hY : inc ≫ G = 1 by`. Establish `hx' : x ≫ (𝟙 A.t.G ^ m) = toUnit T ≫ η[A.t.G]`. Rewrite using `[MonObj.comp_pow, Category.comp_id]`.

Conclude with `hx`. Rewrite using `[← pullback.lift_fst x (toUnit T) hx', Category.assoc]`. Express the relevant statement in the definitionally equal form `_ ≫ inc ≫ G = 1`. Rewrite using `[hY, MonObj.comp_one]`. Use `flat_ker _ A.pol m hm` as an intermediate fact.

Use `isSchemeTheoreticallyDominant_complexPoint K σ` as an intermediate fact. Use `B.ab.proper` as an intermediate fact. Use `A.ab.proper` as an intermediate fact. Establish `: IsSeparated B.t.G.hom` using `inferInstance`. Use `eq_of_pullback_eq (spMap (σ.comp (algebraMap (𝓞 K) K))) ?_` and prove the remaining obligations.

Use `set t := spMap (σ.comp (algebraMap (𝓞 K) K)) with ht`. Set `F` to `Over.pullback t`. Establish `hA' : IsAbelianScheme (F.obj A.t.G)` using `ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A.t.G A.ab`. Establish `: IsSeparated (F.obj B.t.G).hom` using `by change IsSeparated (pullback.snd _ _); infer_instance`. Establish `: LocallyOfFiniteType (F.obj B.t.G).hom` using `by change LocallyOfFiniteType (pullback.snd _ _); infer_instance`.

Establish `hpow : F.map (𝟙 A.t.G ^ m) = 𝟙 (F.obj A.t.G) ^ m`. Simplify using `using map_pow (F.homMonoidHom (X := A.t.G) (M := A.t.G)) (𝟙 A.t.G) m`. Establish `hinc : inc ≫ (𝟙 A.t.G ^ m) = 1`. Rewrite using `[show inc ≫ (𝟙 A.t.G ^ m) = pullback.snd (𝟙 A.t.G ^ m) η[A.t.G] ≫ η[A.t.G] from pullback.condition, toUnit_unique (pullback.snd (𝟙 A.t.G ^ m) η[A.t.G]) (toUnit _)]`. Both sides reduce to the same expression.

Establish `hFinc : F.map inc ≫ (𝟙 (F.obj A.t.G) ^ m) = toUnit _ ≫ η[F.obj A.t.G]`. Rewrite using `[← hpow, ← F.map_comp, hinc, Functor.map_one]`. Both sides reduce to the same expression. Establish `key` using `kill_complex (F.obj A.t.G) (F.obj B.t.G) hA' m hm (F.map G) (fun p => by`. Set `y` to `p ≫ pullback.fst (𝟙 (F.obj A.t.G) ^ m) η[F.obj A.t.G]`.

Establish `hy1 : y ≫ 𝟙 (F.obj A.t.G) ^ m = 1`. Establish `c : pullback.fst (𝟙 (F.obj A.t.G) ^ m) η[F.obj A.t.G] ≫ 𝟙 (F.obj A.t.G) ^ m = pullback.snd (𝟙 (F.obj A.t.G) ^ m) η[F.obj A.t.G] ≫ η[F.obj A.t.G]` using `pullback.condition`. Simplify using `only [y, Category.assoc, c]`. Rewrite using `[← Category.assoc, toUnit_unique (p ≫ pullback.snd _ _) (toUnit _)]`. Both sides reduce to the same expression.

Establish `hyp : ptOf t y ^ m = 1`. Rewrite using `[← Category.comp_id (ptOf t y), ← MonObj.comp_pow, ← ptOf_comp, hpow, hy1, ptOf_one]`. Establish `h2 : ptOf t (y ≫ F.map G) = ptOf t 1`. Rewrite using `[ptOf_comp, ptOf_one]`. Conclude with `hpt _ hyp`.

Establish `h3` using `ptOf_injective t h2`. Simplify using `only [y, Category.assoc] at h3`. Rewrite using `[h3, MonObj.comp_one])`. Establish `hl : F.map inc = pullback.lift (F.map inc) (toUnit _) hFinc ≫ pullback.fst _ _` using `(pullback.lift_fst _ _ _).symm`. Rewrite using `[F.map_comp, Functor.map_one, hl, Category.assoc, key, MonObj.comp_one]`.
-/
theorem kill_torsion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (G : A.t.G ⟶ B.t.G),
    IsMonHom G → ∀ m : ℕ, 0 < m →
    (∀ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.t.G, x ^ m = 1 → x ≫ G = 1) →
    ∀ (T : Over (Sp (𝓞 K))) (x : T ⟶ A.t.G), x ^ m = 1 → x ≫ G = 1 := by
  intro E _ _ _ H K _ _ σ A B G _ m hm hpt T x hx
  let inc : pullback (𝟙 A.t.G ^ m) η[A.t.G] ⟶ A.t.G := pullback.fst _ _
  suffices hY : inc ≫ G = 1 by
    have hx' : x ≫ (𝟙 A.t.G ^ m) = toUnit T ≫ η[A.t.G] := by
      rw [MonObj.comp_pow, Category.comp_id]; exact hx
    rw [← pullback.lift_fst x (toUnit T) hx', Category.assoc]
    change _ ≫ inc ≫ G = 1
    rw [hY, MonObj.comp_one]
  have := flat_ker _ A.pol m hm
  have := isSchemeTheoreticallyDominant_complexPoint K σ
  have := B.ab.proper
  have := A.ab.proper
  have : IsSeparated B.t.G.hom := inferInstance
  refine eq_of_pullback_eq (spMap (σ.comp (algebraMap (𝓞 K) K))) ?_
  set t := spMap (σ.comp (algebraMap (𝓞 K) K)) with ht
  let F := Over.pullback t
  have hA' : IsAbelianScheme (F.obj A.t.G) := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A.t.G A.ab
  have : IsSeparated (F.obj B.t.G).hom := by change IsSeparated (pullback.snd _ _); infer_instance
  have : LocallyOfFiniteType (F.obj B.t.G).hom := by change LocallyOfFiniteType (pullback.snd _ _); infer_instance
  have hpow : F.map (𝟙 A.t.G ^ m) = 𝟙 (F.obj A.t.G) ^ m := by
    simpa using map_pow (F.homMonoidHom (X := A.t.G) (M := A.t.G)) (𝟙 A.t.G) m
  have hinc : inc ≫ (𝟙 A.t.G ^ m) = 1 := by
    rw [show inc ≫ (𝟙 A.t.G ^ m) = pullback.snd (𝟙 A.t.G ^ m) η[A.t.G] ≫ η[A.t.G] from pullback.condition,
      toUnit_unique (pullback.snd (𝟙 A.t.G ^ m) η[A.t.G]) (toUnit _)]
    rfl
  have hFinc : F.map inc ≫ (𝟙 (F.obj A.t.G) ^ m) = toUnit _ ≫ η[F.obj A.t.G] := by
    rw [← hpow, ← F.map_comp, hinc, Functor.map_one]; rfl
  have key := kill_complex (F.obj A.t.G) (F.obj B.t.G) hA' m hm (F.map G) (fun p => by
    let y := p ≫ pullback.fst (𝟙 (F.obj A.t.G) ^ m) η[F.obj A.t.G]
    have hy1 : y ≫ 𝟙 (F.obj A.t.G) ^ m = 1 := by
      have c : pullback.fst (𝟙 (F.obj A.t.G) ^ m) η[F.obj A.t.G] ≫ 𝟙 (F.obj A.t.G) ^ m =
          pullback.snd (𝟙 (F.obj A.t.G) ^ m) η[F.obj A.t.G] ≫ η[F.obj A.t.G] := pullback.condition
      simp only [y, Category.assoc, c]
      rw [← Category.assoc, toUnit_unique (p ≫ pullback.snd _ _) (toUnit _)]
      rfl
    have hyp : ptOf t y ^ m = 1 := by
      rw [← Category.comp_id (ptOf t y), ← MonObj.comp_pow, ← ptOf_comp, hpow, hy1, ptOf_one]
    have h2 : ptOf t (y ≫ F.map G) = ptOf t 1 := by
      rw [ptOf_comp, ptOf_one]; exact hpt _ hyp
    have h3 := ptOf_injective t h2
    simp only [y, Category.assoc] at h3
    rw [h3, MonObj.comp_one])
  have hl : F.map inc = pullback.lift (F.map inc) (toUnit _) hFinc ≫ pullback.fst _ _ :=
    (pullback.lift_fst _ _ _).symm
  rw [F.map_comp, Functor.map_one, hl, Category.assoc, key, MonObj.comp_one]

end GlobalTheory.TorsionKill
