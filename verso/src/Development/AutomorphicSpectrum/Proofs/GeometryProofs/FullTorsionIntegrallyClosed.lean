import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsOfPolAV
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NatCastSmulMemHtLat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorsionQuasiFiniteGroupStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingPullbackIffStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGenericWeilPairingStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.OmLink

section push
variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

/- English proof (translation)
The claim follows from `Over.OverMorphism.ext (hp.2 T x y _ _ rfl rfl).symm`.
-/
theorem push_mul (hp : IsGrpPullback G' G f φ) {T : Over S'} (x y : T ⟶ G') :
    pushPt hp.1.w (x * y) = pushPt hp.1.w x * pushPt hp.1.w y :=
  Over.OverMorphism.ext (hp.2 T x y _ _ rfl rfl).symm

def pushHom (hp : IsGrpPullback G' G f φ) (T : Over S') : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MonoidHom.mk' (pushPt hp.1.w) (push_mul hp)

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `hp.1.hom_ext` to reduce the goal to its premises. Conclude with `congrArg (fun z => z.left) h`. Rewrite using `[Over.w x, Over.w y]`.
-/
theorem push_inj (hp : IsGrpPullback G' G f φ) {T : Over S'} {x y : T ⟶ G'}
    (h : pushPt hp.1.w x = pushPt hp.1.w y) : x = y := by
  apply Over.OverMorphism.ext
  apply hp.1.hom_ext
  · exact congrArg (fun z => z.left) h
  · rw [Over.w x, Over.w y]

end push

/- English proof (translation)
Establish `hnt : Nontrivial D.La`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nontrivial_iff_subsingleton]`. Use `D.rank` as an intermediate fact. Rewrite `this` using `[Module.finrank_zero_of_subsingleton]`.

Use linear arithmetic over natural numbers and integers. Use `haveI := D.fin`. Use `haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La`. Use `haveI : Module.IsTorsionFree ℤ D.La := by`. Use `⟨fun r hr a b hab => D.unimod.1 ?_⟩` and prove the remaining obligations.

Establish `hr0 : r ≠ 0` using `hr.ne_zero`. Use extensionality with `y`. Establish `h : r • D.EF a y = r • D.EF b y`. Use `congrArg (fun z => D.EF z y) hab` as an intermediate fact. Simplify `this` using `only [map_smul, LinearMap.smul_apply]`.

Conclude with `mul_left_cancel₀ hr0 h`. Set `bs` to `Module.Free.chooseBasis ℤ D.La`. Take `⟨j⟩ : Nonempty (Module.Free.ChooseBasisIndex ℤ D.La)` from `bs.index_nonempty`. Take `⟨a, ha⟩` from `D.unimod.2 (bs.coord j)`. Conclude with `⟨a, bs j, by rw [ha]; simp⟩`.
-/
theorem exists_EF_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    (hpq : 0 < D.p + D.q) : ∃ a b, D.EF a b = 1 := by
  have hnt : Nontrivial D.La := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have := D.rank
    rw [Module.finrank_zero_of_subsingleton] at this
    omega
  haveI := D.fin
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : Module.IsTorsionFree ℤ D.La := by
    refine ⟨fun r hr a b hab => D.unimod.1 ?_⟩
    have hr0 : r ≠ 0 := hr.ne_zero
    ext y
    have h : r • D.EF a y = r • D.EF b y := by
      have := congrArg (fun z => D.EF z y) hab
      simpa only [map_smul, LinearMap.smul_apply] using this
    exact mul_left_cancel₀ hr0 h
  let bs := Module.Free.chooseBasis ℤ D.La
  obtain ⟨j⟩ : Nonempty (Module.Free.ChooseBasisIndex ℤ D.La) := bs.index_nonempty
  obtain ⟨a, ha⟩ := D.unimod.2 (bs.coord j)
  exact ⟨a, bs j, by rw [ha]; simp⟩

/- English proof (translation)
Use `haveI := D.fin`. Use `haveI := D.proj`. Establish `h` using `D.rank`. Rewrite `h` using `[hpq]`. Conclude with `Module.finrank_zero_iff.1 h`.
-/
theorem subsingleton_La {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    (hpq : D.p + D.q = 0) : Subsingleton D.La := by
  haveI := D.fin
  haveI := D.proj
  have h := D.rank
  rw [hpq] at h
  exact Module.finrank_zero_iff.1 h

/- English proof (translation)
Substitute `h` using the available equality. Introduce `k _ i g hg`. Set `i' : Ω →+* k` to `i.comp κ.symm.toRingHom`. Establish `e : spMap i ≫ ξ' = spMap i' ≫ spMap κ.toRingHom ≫ ξ'`. Rewrite using `[← Category.assoc]`.

Use `congr 1`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Use extensionality with `x`. Simplify using `[i']`.

Establish `tr : ∀ {a b : Sp k ⟶ X} (_ : a = b) (g : Over.mk a ⟶ G), g ^ n = 1 → ∃ g' : Over.mk b ⟶ G, g'.left = g.left ∧ g' ^ n = 1`. Introduce `a b h g hg`. Substitute `h` using the available equality. Conclude with `⟨g, rfl, hg⟩`. Take `⟨g', hl, hg'⟩` from `tr e g hg`.

Take `⟨x, hx⟩` from `hf k i' g' hg'`. Establish `h1 : spMap κ.symm.toRingHom ≫ spMap κ.toRingHom = 𝟙 _`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Establish `: κ.symm.toRingHom.comp κ.toRingHom = RingHom.id _` using `by ext; simp`. Rewrite using `[this]`.

Conclude with `Spec.map_id _`. Establish `h2 : spMap i' = spMap i ≫ spMap κ.symm.toRingHom`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `⟨Over.homMk (spMap κ.symm.toRingHom ≫ x.left) ?_, ?_⟩` and prove the remaining obligations. Use `Over.w x` as an intermediate fact.

Simplify using `only [Over.mk_left, Over.mk_hom, Functor.id_obj, Functor.const_obj_obj, Functor.id_map] at this ⊢`. Simplify using `only [Category.assoc, this]`. Rewrite using `[← Category.assoc, h1, Category.id_comp]`. Simplify using `only [Over.homMk_left]`. Rewrite using `[← hl, hx, h2, Category.assoc]`.
-/
theorem fullTorsion_of_equiv {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {G : Over X} [GrpObj G]
    (κ : Ω' ≃+* Ω) {ξ' : Sp Ω' ⟶ X} {ξ : Sp Ω ⟶ X} (h : spMap κ.toRingHom ≫ ξ' = ξ) {n : ℕ}
    (hf : FullTorsion G ξ n) : FullTorsion G ξ' n := by
  subst h
  intro k _ i g hg
  let i' : Ω →+* k := i.comp κ.symm.toRingHom
  have e : spMap i ≫ ξ' = spMap i' ≫ spMap κ.toRingHom ≫ ξ' := by
    rw [← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [i']
  have tr : ∀ {a b : Sp k ⟶ X} (_ : a = b) (g : Over.mk a ⟶ G), g ^ n = 1 →
      ∃ g' : Over.mk b ⟶ G, g'.left = g.left ∧ g' ^ n = 1 := by
    intro a b h g hg
    subst h
    exact ⟨g, rfl, hg⟩
  obtain ⟨g', hl, hg'⟩ := tr e g hg
  obtain ⟨x, hx⟩ := hf k i' g' hg'
  have h1 : spMap κ.symm.toRingHom ≫ spMap κ.toRingHom = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : κ.symm.toRingHom.comp κ.toRingHom = RingHom.id _ := by ext; simp
    rw [this]
    exact Spec.map_id _
  have h2 : spMap i' = spMap i ≫ spMap κ.symm.toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine ⟨Over.homMk (spMap κ.symm.toRingHom ≫ x.left) ?_, ?_⟩
  · have := Over.w x
    simp only [Over.mk_left, Over.mk_hom, Functor.id_obj, Functor.const_obj_obj, Functor.id_map] at this ⊢
    simp only [Category.assoc, this]
    rw [← Category.assoc, h1, Category.id_comp]
  · simp only [Over.homMk_left]
    rw [← hl, hx, h2, Category.assoc]

/- English proof (translation)
Establish `h1 : Flat (spMap f)`. Set `_` to `f.toAlgebra`. Conclude with `HasRingHomProperty.Spec_iff.2 (show (algebraMap K k).Flat from RingHom.flat_algebraMap_iff.2 inferInstance)`. Establish `h2 : Surjective (spMap f)` using `⟨fun x => ⟨IsLocalRing.closedPoint k, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩`. Conclude with `Flat.epi_of_flat_of_surjective _`.
-/
theorem epi_sp {K k : Type} [Field K] [Field k] (f : K →+* k) : Epi (spMap f) := by
  have h1 : Flat (spMap f) := by
    let _ := f.toAlgebra
    exact HasRingHomProperty.Spec_iff.2 (show (algebraMap K k).Flat from
      RingHom.flat_algebraMap_iff.2 inferInstance)
  have h2 : Surjective (spMap f) := ⟨fun x => ⟨IsLocalRing.closedPoint k, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

section desc
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G' : Over (Sp Ω)} {G : Over X} [GrpObj G'] [GrpObj G]
  {φ : G'.left ⟶ G.left}

def ex {k : Type} [Field k] (i : Ω →+* k) : Over.mk (spMap i) ⟶ Over.mk (𝟙 (Sp Ω)) :=
  Over.homMk (spMap i) (by simp)

/- English proof (translation)
Use `haveI := epi_sp i`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[← cancel_epi (spMap i)]`. Conclude with `congrArg (fun z => z.left) h`.
-/
theorem eq_of_ex {k : Type} [Field k] (i : Ω →+* k) {y y' : Over.mk (𝟙 (Sp Ω)) ⟶ G'} (h : ex i ≫ y = ex i ≫ y') :
    y = y' := by
  haveI := epi_sp i
  apply Over.OverMorphism.ext
  rw [← cancel_epi (spMap i)]
  exact congrArg (fun z => z.left) h

/- English proof (translation)
Establish `hg : (pushPt hp.1.w a) ^ n = 1`. Use `map_pow (pushHom hp (Over.mk (spMap i))) a n` as an intermediate fact. Rewrite `this` using `[ha, map_one]`. Conclude with `this.symm`. Take `⟨x, hx⟩` from `hf k i (pushPt hp.1.w a) hg`.

Establish `hw : x.left ≫ G.hom = 𝟙 _ ≫ ξ` using `by simpa using Over.w x`. Set `y : Over.mk (𝟙 (Sp Ω)) ⟶ G'` to `Over.homMk (hp.1.lift x.left (𝟙 _) hw) (hp.1.lift_snd _ _ _)`. Establish `hy : a = ex i ≫ y`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `hp.1.hom_ext` to reduce the goal to its premises.

Establish `h1 : y.left ≫ φ = x.left` using `hp.1.lift_fst _ _ _ show a.left ≫ φ = (spMap i ≫ y.left) ≫ φ`. Rewrite using `[Category.assoc, h1]`. Conclude with `hx`. Establish `h1 : y.left ≫ G'.hom = 𝟙 _` using `hp.1.lift_snd _ _ _ show a.left ≫ G'.hom = (spMap i ≫ y.left) ≫ G'.hom`. Rewrite using `[Category.assoc, h1]`.

Conclude with `(Over.w a).trans (Category.comp_id (spMap i)).symm`. Use `⟨y, eq_of_ex i ?_, hy⟩` and prove the remaining obligations. Rewrite using `[MonObj.comp_pow, ← hy, ha, MonObj.comp_one]`.
-/
theorem desc (hp : IsGrpPullback G' G ξ φ) {n : ℕ} (hf : FullTorsion G ξ n) {k : Type} [Field k] (i : Ω →+* k)
    (a : Over.mk (spMap i) ⟶ G') (ha : a ^ n = 1) :
    ∃ y : Over.mk (𝟙 (Sp Ω)) ⟶ G', y ^ n = 1 ∧ a = ex i ≫ y := by
  have hg : (pushPt hp.1.w a) ^ n = 1 := by
    have := map_pow (pushHom hp (Over.mk (spMap i))) a n
    rw [ha, map_one] at this
    exact this.symm
  obtain ⟨x, hx⟩ := hf k i (pushPt hp.1.w a) hg
  have hw : x.left ≫ G.hom = 𝟙 _ ≫ ξ := by simpa using Over.w x
  let y : Over.mk (𝟙 (Sp Ω)) ⟶ G' := Over.homMk (hp.1.lift x.left (𝟙 _) hw) (hp.1.lift_snd _ _ _)
  have hy : a = ex i ≫ y := by
    apply Over.OverMorphism.ext
    apply hp.1.hom_ext
    · have h1 : y.left ≫ φ = x.left := hp.1.lift_fst _ _ _
      show a.left ≫ φ = (spMap i ≫ y.left) ≫ φ
      rw [Category.assoc, h1]
      exact hx
    · have h1 : y.left ≫ G'.hom = 𝟙 _ := hp.1.lift_snd _ _ _
      show a.left ≫ G'.hom = (spMap i ≫ y.left) ≫ G'.hom
      rw [Category.assoc, h1]
      exact (Over.w a).trans (Category.comp_id (spMap i)).symm
  refine ⟨y, eq_of_ex i ?_, hy⟩
  rw [MonObj.comp_pow, ← hy, ha, MonObj.comp_one]

/- English proof (translation)
Establish `hw : (GenWeilModel.ext i ≫ g).left ≫ G.hom = spMap i ≫ ξ` using `Over.w (GenWeilModel.ext i ≫ g)`. Set `a : Over.mk (spMap i) ⟶ G'` to `Over.homMk (hp.1.lift (GenWeilModel.ext i ≫ g).left (spMap i) hw) (hp.1.lift_snd _ _ _)`. Establish `ha : pushPt hp.1.w a = GenWeilModel.ext i ≫ g` using `Over.OverMorphism.ext (hp.1.lift_fst _ _ _)`. Use `⟨a, push_inj hp ?_, ha⟩` and prove the remaining obligations. Establish `h1` using `map_pow (pushHom hp (Over.mk (spMap i))) a n`.

Establish `h2 : pushHom hp (Over.mk (spMap i)) a = GenWeilModel.ext i ≫ g` using `ha`. Establish `h3 : (GenWeilModel.ext i ≫ g) ^ n = 1` using `by rw [← MonObj.comp_pow, hg, MonObj.comp_one]`. Rewrite `h1` using `[h2, h3]`. Conclude with `h1.trans (map_one (pushHom hp (Over.mk (spMap i)))).symm`.
-/
theorem pull_point (hp : IsGrpPullback G' G ξ φ) {n : ℕ} {k : Type} [Field k] (i : Ω →+* k)
    (g : Over.mk ξ ⟶ G) (hg : g ^ n = 1) :
    ∃ a : Over.mk (spMap i) ⟶ G', a ^ n = 1 ∧ pushPt hp.1.w a = GenWeilModel.ext i ≫ g := by
  have hw : (GenWeilModel.ext i ≫ g).left ≫ G.hom = spMap i ≫ ξ := Over.w (GenWeilModel.ext i ≫ g)
  let a : Over.mk (spMap i) ⟶ G' :=
    Over.homMk (hp.1.lift (GenWeilModel.ext i ≫ g).left (spMap i) hw) (hp.1.lift_snd _ _ _)
  have ha : pushPt hp.1.w a = GenWeilModel.ext i ≫ g := Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  refine ⟨a, push_inj hp ?_, ha⟩
  have h1 := map_pow (pushHom hp (Over.mk (spMap i))) a n
  have h2 : pushHom hp (Over.mk (spMap i)) a = GenWeilModel.ext i ≫ g := ha
  have h3 : (GenWeilModel.ext i ≫ g) ^ n = 1 := by rw [← MonObj.comp_pow, hg, MonObj.comp_one]
  rw [h2, h3] at h1
  exact h1.trans (map_one (pushHom hp (Over.mk (spMap i)))).symm

end desc

section weil
open ReciprocityTheory.ChartRestriction.G.Out

variable {Ω : Type} [Field Ω]

/- English proof (translation)
Establish `hW` using `GlobalTheory.PairingLawZeroCounterexample.laws.1`. Take `⟨c₀, hc₀, -⟩` from `(hW _ P n (Over.mk (𝟙 (Sp Ω)))).1 y y' hy hy'`. Take `⟨u, rfl⟩` from `(GenWeilModel.unitOn_bij (R := Ω)).2 c₀`. Use `⟨u, fun c => ?_⟩` and prove the remaining obligations. Establish `hp` using `(GlobalTheory.weilIs_alternating_skew_natural GlobalTheory.laws_without_cohomology.1 GlobalTheory.PairingLawZeroCounterexample.lifts _ P n _).2.2 _ (ex i) y y' _ hc₀`.

Establish `hp' : WeilIs P.A P.L n (ex i ≫ y) (ex i ≫ y') (unitOn (Units.map i.toMonoidHom u))` using `GenWeilModel.unitOn_ext i u ▸ hp`. Establish `hx : (ex i ≫ y) ^ n = 1` using `by rw [← MonObj.comp_pow, hy, MonObj.comp_one]`. Establish `hg : (ex i ≫ y') ^ n = 1` using `by rw [← MonObj.comp_pow, hy', MonObj.comp_one]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `(GenWeilModel.unitOn_bij (R := k)).1 (((hW _ P n _).1 _ _ hx hg).unique h hp')`. Introduce and unpack `rfl`. Conclude with `hp'`.
-/
theorem weil_desc (P : PolAV (Sp Ω)) {n : ℕ} {k : Type} [Field k] (i : Ω →+* k)
    {y y' : Over.mk (𝟙 (Sp Ω)) ⟶ P.A} (hy : y ^ n = 1) (hy' : y' ^ n = 1) :
    ∃ u : Ωˣ, ∀ c : kˣ, WeilIs P.A P.L n (ex i ≫ y) (ex i ≫ y') (unitOn c) ↔ c = Units.map i.toMonoidHom u := by
  have hW := GlobalTheory.PairingLawZeroCounterexample.laws.1
  obtain ⟨c₀, hc₀, -⟩ := (hW _ P n (Over.mk (𝟙 (Sp Ω)))).1 y y' hy hy'
  obtain ⟨u, rfl⟩ := (GenWeilModel.unitOn_bij (R := Ω)).2 c₀
  refine ⟨u, fun c => ?_⟩
  have hp := (GlobalTheory.weilIs_alternating_skew_natural GlobalTheory.laws_without_cohomology.1 GlobalTheory.PairingLawZeroCounterexample.lifts
    _ P n _).2.2 _ (ex i) y y' _ hc₀
  have hp' : WeilIs P.A P.L n (ex i ≫ y) (ex i ≫ y') (unitOn (Units.map i.toMonoidHom u)) :=
    GenWeilModel.unitOn_ext i u ▸ hp
  have hx : (ex i ≫ y) ^ n = 1 := by rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  have hg : (ex i ≫ y') ^ n = 1 := by rw [← MonObj.comp_pow, hy', MonObj.comp_one]
  constructor
  · intro h
    exact (GenWeilModel.unitOn_bij (R := k)).1 (((hW _ P n _).1 _ _ hx hg).unique h hp')
  · rintro rfl
    exact hp'

end weil

section obj
open ReciprocityTheory.ChartRestriction.G.Out

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {s : Sp Ω ⟶ Sp B}

/- English proof (translation)
Take `⟨β₀, rfl⟩ : ∃ β₀ : B →+* Ω, spMap β₀ = s` from `⟨(Spec.preimage s).hom, by simp [spMap]⟩`. Establish `h : spMap i ≫ spMap β₀ = spMap (i.comp β₀)`. Simplify using `only [spMap]`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Take `⟨-, I, -⟩` from `o.geom k (spMap i) (i.comp β₀) h`.

Conclude with `⟨I⟩`.
-/
theorem exists_tate (o : Obj D l b s) {k : Type} [Field k] [IsAlgClosed k] (i : Ω →+* k) :
    Nonempty (TateIso D k (Over.mk (spMap i) ⟶ o.t.G) (fun a g => g ≫ o.t.act.act a)
        (fun n g g' c => Out.WeilIs o.t.G o.t.PP.L n g g' (unitOn c))) := by
  obtain ⟨β₀, rfl⟩ : ∃ β₀ : B →+* Ω, spMap β₀ = s := ⟨(Spec.preimage s).hom, by simp [spMap]⟩
  have h : spMap i ≫ spMap β₀ = spMap (i.comp β₀) := by
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨-, I, -⟩ := o.geom k (spMap i) (i.comp β₀) h
  exact ⟨I⟩

/- English proof (translation)
Take `⟨a, a', hab⟩` from `exists_EF_one D hpq`. Set `i` to `algebraMap Ω (AlgebraicClosure Ω)`. Take `⟨I⟩` from `exists_tate o i`. Take `⟨y, hy, hya⟩` from `desc m.cart hf i _ ((I.onto n hn (I.ev n a)).2 ⟨a, rfl⟩)`. Take `⟨y', hy', hyb⟩` from `desc m.cart hf i _ ((I.onto n hn (I.ev n a')).2 ⟨a', rfl⟩)`.

Take `⟨u, hu⟩` from `weil_desc (GlobalTheory.Obj.toPolAV o) (n := n) i (y := y) (y' := y') hy hy'`. Establish `h1` using `I.isom n hn a a'`. Rewrite `h1` using `[hab, zpow_one, hya, hyb]`. Establish `h2` using `(hu _).1 h1`. Use `⟨u, ?_⟩` and prove the remaining obligations.

Establish `h3 : IsPrimitiveRoot (Units.map i.toMonoidHom u) n` using `h2 ▸ I.ζ_prim n hn`. Establish `h4 : IsPrimitiveRoot u n` using `h3.of_map_of_injective (f := Units.map i.toMonoidHom) (Units.map_injective i.injective)`. Conclude with `IsPrimitiveRoot.coe_units_iff.2 h4`.
-/
theorem root (o : Obj D l b s) (t : SAB H X) (m : SABMap o.t t ξ) {n : ℕ} (hf : FullTorsion t.G ξ n) (hn : 0 < n)
    (hpq : 0 < D.p + D.q) : ∃ ζ : Ω, IsPrimitiveRoot ζ n := by
  obtain ⟨a, a', hab⟩ := exists_EF_one D hpq
  let i := algebraMap Ω (AlgebraicClosure Ω)
  obtain ⟨I⟩ := exists_tate o i
  obtain ⟨y, hy, hya⟩ := desc m.cart hf i _ ((I.onto n hn (I.ev n a)).2 ⟨a, rfl⟩)
  obtain ⟨y', hy', hyb⟩ := desc m.cart hf i _ ((I.onto n hn (I.ev n a')).2 ⟨a', rfl⟩)
  obtain ⟨u, hu⟩ := weil_desc (GlobalTheory.Obj.toPolAV o) (n := n) i (y := y) (y' := y') hy hy'
  have h1 := I.isom n hn a a'
  rw [hab, zpow_one, hya, hyb] at h1
  have h2 := (hu _).1 h1
  refine ⟨u, ?_⟩
  have h3 : IsPrimitiveRoot (Units.map i.toMonoidHom u) n := h2 ▸ I.ζ_prim n hn
  have h4 : IsPrimitiveRoot u n :=
    h3.of_map_of_injective (f := Units.map i.toMonoidHom) (Units.map_injective i.injective)
  exact IsPrimitiveRoot.coe_units_iff.2 h4
end obj

section obj2
open ReciprocityTheory.ChartRestriction.G.Out

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {s : Sp Ω ⟶ Sp B}

/- English proof (translation)
The claim follows from `map_one (pushHom hp T)`.
-/
theorem push_one {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) (T : Over S') :
    pushPt hp.1.w (1 : T ⟶ G') = 1 := map_one (pushHom hp T)

/- English proof (translation)
Use `haveI := subsingleton_La D hpq`. Set `i` to `algebraMap Ω (AlgebraicClosure Ω)`. Take `⟨I⟩` from `exists_tate o i`. Establish `hp` using `m.cart`. Take `⟨a, han, ha⟩` from `pull_point hp i g hg`.

Take `⟨c, hc⟩` from `(I.onto n hn a).1 han`. Establish `h0 : I.ev n 0 = 1`. Use `I.add n 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_mul.1 this`.

Establish `ha1 : a = 1` using `by rw [← hc, Subsingleton.elim c 0, h0]`. Use `haveI := epi_sp i`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[← cancel_epi (spMap i)]`. Establish `h2 : GenWeilModel.ext i ≫ g = GenWeilModel.ext i ≫ 1`.

Rewrite using `[MonObj.comp_one, ← ha, ha1]`. Conclude with `push_one hp _`. Conclude with `congrArg (fun z => z.left) h2`.
-/
theorem tors_trivial (o : Obj D l b s) (t : SAB H X) (m : SABMap o.t t ξ) {n : ℕ} (hn : 0 < n)
    (hpq : D.p + D.q = 0) (g : Over.mk ξ ⟶ t.G) (hg : g ^ n = 1) : g = 1 := by
  haveI := subsingleton_La D hpq
  let i := algebraMap Ω (AlgebraicClosure Ω)
  obtain ⟨I⟩ := exists_tate o i
  have hp := m.cart
  obtain ⟨a, han, ha⟩ := pull_point hp i g hg
  obtain ⟨c, hc⟩ := (I.onto n hn a).1 han
  have h0 : I.ev n 0 = 1 := by
    have := I.add n 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have ha1 : a = 1 := by rw [← hc, Subsingleton.elim c 0, h0]
  haveI := epi_sp i
  apply Over.OverMorphism.ext
  rw [← cancel_epi (spMap i)]
  have h2 : GenWeilModel.ext i ≫ g = GenWeilModel.ext i ≫ 1 := by
    rw [MonObj.comp_one, ← ha, ha1]
    exact push_one hp _
  exact congrArg (fun z => z.left) h2

/- English proof (translation)
Establish `triv` using `tors_trivial o t m hn hpq`. Establish `hW` using `GlobalTheory.PairingLawZeroCounterexample.laws.1`. Use `{ finite := ?_, mul_left := ?_, mul_right := ?_, perfect := ?_, nondeg := ?_, weil := ?_ }` and prove the remaining obligations. Use `haveI : Subsingleton {x : Over.mk ξ ⟶ t.G // x ^ n = 1} := ⟨fun a b => Subtype.ext ((triv _ a.2).trans (triv _ b.2).symm)⟩`. Conclude with `Finite.of_subsingleton`.

Use `intros`. Simplify using the standard rewrite rules. Use `intros`. Simplify using the standard rewrite rules. Introduce `χ hχ`.

Use `⟨1, one_pow n, fun g hg => ?_⟩` and prove the remaining obligations. Rewrite using `[triv g hg]`. Use `hχ 1 1 (one_pow n) (one_pow n)` as an intermediate fact. Rewrite `this` using `[_root_.mul_one]`. Conclude with `left_eq_mul.1 this`.

Conclude with `fun g hg _ => triv g hg`. Introduce `x g hx hg k _ _ i xk gk c hxk hgk`. Take `rfl` from `triv x hx`. Take `rfl` from `triv g hg`. Establish `e1 : ∀ z : Over.mk (spMap i ≫ ξ) ⟶ t.G, z.left = spMap i ≫ (1 : Over.mk ξ ⟶ t.G).left → (1 : Over.mk (spMap i) ⟶ o.t.G).left ≫ m.φ = z.left`.

Introduce `z hz`. Establish `h1 : (GenWeilModel.ext i ≫ (1 : Over.mk ξ ⟶ t.G)) = 1` using `MonObj.comp_one _`. Establish `h2` using `congrArg (fun w => w.left) (push_one m.cart (Over.mk (spMap i)))`. Rewrite using `[hz]`. Conclude with `h2.trans (congrArg (fun w => w.left) h1).symm`.

Rewrite using `[← GlobalTheory.T.weil_pairing_pullback_iff E H X (Sp Ω) t o.t ξ m k (spMap i) 1 1 xk gk n c (e1 xk hxk) (e1 gk hgk)]`. Establish `hx1` using `hW _ (GlobalTheory.Obj.toPolAV o) n (Over.mk (spMap i))`. Establish `h1 : WeilIs o.t.G o.t.PP.L n (1 : Over.mk (spMap i) ⟶ o.t.G) 1 (unitOn (1 : kˣ))`. Rewrite using `[GenWeilModel.unitOn_one]`. Conclude with `hx1.2.2.1 1 (one_pow n)`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `(GenWeilModel.unitOn_bij (R := k)).1 ((hx1.1 1 1 (one_pow n) (one_pow n)).unique h h1)` as an intermediate fact. Simplify using `[this]`. Introduce `h`.

Establish `: c = 1` using `Units.ext (by simpa using h)`. Rewrite using `[this]`. Conclude with `h1`.
-/
theorem genWeil_trivial (o : Obj D l b s) (t : SAB H X) (m : SABMap o.t t ξ) {n : ℕ} (hn : 0 < n)
    (hpq : D.p + D.q = 0) : GenWeil t.G t.PP.L ξ n (fun _ _ => 1) := by
  have triv := tors_trivial o t m hn hpq
  have hW := GlobalTheory.PairingLawZeroCounterexample.laws.1
  refine { finite := ?_, mul_left := ?_, mul_right := ?_, perfect := ?_, nondeg := ?_, weil := ?_ }
  · haveI : Subsingleton {x : Over.mk ξ ⟶ t.G // x ^ n = 1} :=
      ⟨fun a b => Subtype.ext ((triv _ a.2).trans (triv _ b.2).symm)⟩
    exact Finite.of_subsingleton
  · intros; simp
  · intros; simp
  · intro χ hχ
    refine ⟨1, one_pow n, fun g hg => ?_⟩
    rw [triv g hg]
    have := hχ 1 1 (one_pow n) (one_pow n)
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  · exact fun g hg _ => triv g hg
  · intro x g hx hg k _ _ i xk gk c hxk hgk
    obtain rfl := triv x hx
    obtain rfl := triv g hg
    have e1 : ∀ z : Over.mk (spMap i ≫ ξ) ⟶ t.G, z.left = spMap i ≫ (1 : Over.mk ξ ⟶ t.G).left →
        (1 : Over.mk (spMap i) ⟶ o.t.G).left ≫ m.φ = z.left := by
      intro z hz
      have h1 : (GenWeilModel.ext i ≫ (1 : Over.mk ξ ⟶ t.G)) = 1 := MonObj.comp_one _
      have h2 := congrArg (fun w => w.left) (push_one m.cart (Over.mk (spMap i)))
      rw [hz]
      exact h2.trans (congrArg (fun w => w.left) h1).symm
    rw [← GlobalTheory.T.weil_pairing_pullback_iff E H X (Sp Ω) t o.t ξ m k (spMap i) 1 1 xk gk n c (e1 xk hxk) (e1 gk hgk)]
    have hx1 := hW _ (GlobalTheory.Obj.toPolAV o) n (Over.mk (spMap i))
    have h1 : WeilIs o.t.G o.t.PP.L n (1 : Over.mk (spMap i) ⟶ o.t.G) 1 (unitOn (1 : kˣ)) := by
      rw [GenWeilModel.unitOn_one]
      exact hx1.2.2.1 1 (one_pow n)
    constructor
    · intro h
      have := (GenWeilModel.unitOn_bij (R := k)).1 ((hx1.1 1 1 (one_pow n) (one_pow n)).unique h h1)
      simp [this]
    · intro h
      have : c = 1 := Units.ext (by simpa using h)
      rw [this]
      exact h1

end obj2

/- English proof (translation)
Set `κ₀ : FractionRing (X.presheaf.stalk q.1) →+* Ω` to `IsFractionRing.lift (hξ.inj q)`. Establish `hκ : ∀ r, κ₀ (algebraMap _ _ r) = genMap ξ q r` using `fun r => IsFractionRing.lift_algebraMap (hξ.inj q) r`. Establish `hb : Function.Bijective κ₀` using `⟨κ₀.injective, fun a => by`. Take `⟨b, c, hc, h⟩` from `GlobalTheory.T.exists_stalk_fraction_of_generic ξ hξ q a`. Use `⟨algebraMap _ _ b / algebraMap _ _ c, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_div₀, hκ, hκ, ← h]`. Use the proof step `field_simp⟩`. Use `fullTorsion_of_equiv (RingEquiv.ofBijective κ₀ hb) ?_ hf` and prove the remaining obligations. Establish `e : spMap (RingEquiv.ofBijective κ₀ hb).toRingHom ≫ spMap (algebraMap (X.presheaf.stalk q.1) (FractionRing (X.presheaf.stalk q.1))) = Spec.map (CommRingCat.ofHom (genMap ξ q))`. Simplify using `only [spMap]`.

Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Use extensionality with `r`. Conclude with `hκ r`. Rewrite using `[← Category.assoc, e]`.

Conclude with `HTTie.hk_stalk ξ q`.
-/
theorem fullTorsion_frac {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (hξ : IsCptGen ξ) (q : Cpt ξ)
    [IsDomain (X.presheaf.stalk q.1)] {G : Over X} [GrpObj G] {n : ℕ} (hf : FullTorsion G ξ n) :
    FullTorsion G (spMap (algebraMap (X.presheaf.stalk q.1) (FractionRing (X.presheaf.stalk q.1))) ≫
      X.fromSpecStalk q.1) n := by
  let κ₀ : FractionRing (X.presheaf.stalk q.1) →+* Ω := IsFractionRing.lift (hξ.inj q)
  have hκ : ∀ r, κ₀ (algebraMap _ _ r) = genMap ξ q r := fun r => IsFractionRing.lift_algebraMap (hξ.inj q) r
  have hb : Function.Bijective κ₀ := ⟨κ₀.injective, fun a => by
    obtain ⟨b, c, hc, h⟩ := GlobalTheory.T.exists_stalk_fraction_of_generic ξ hξ q a
    refine ⟨algebraMap _ _ b / algebraMap _ _ c, ?_⟩
    rw [map_div₀, hκ, hκ, ← h]
    field_simp⟩
  refine fullTorsion_of_equiv (RingEquiv.ofBijective κ₀ hb) ?_ hf
  have e : spMap (RingEquiv.ofBijective κ₀ hb).toRingHom ≫ spMap (algebraMap (X.presheaf.stalk q.1)
      (FractionRing (X.presheaf.stalk q.1))) = Spec.map (CommRingCat.ofHom (genMap ξ q)) := by
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    exact hκ r
  rw [← Category.assoc, e]
  exact HTTie.hk_stalk ξ q

/- English proof (translation)
Introduce `E _ _ _ H D l B _ b X Ω _ _ ξ s o t m V _ _ M n q hξ hn hfull hic hno`. Use `haveI := t.semi`. Use `haveI := hic`. Use `haveI := hno`. Use `haveI hd : IsDomain (X.presheaf.stalk q.1) := (hξ.inj q).isDomain (genMap ξ q)`.

Use `haveI hc : CharZero (X.presheaf.stalk q.1) := ⟨fun a b h => Nat.cast_injective (R := Ω) (by`. Rewrite using `[← map_natCast (genMap ξ q), h, map_natCast])⟩`. Establish `hft` using `fullTorsion_frac hξ q hfull`. Take `⟨T, _, _, Γ', i, htor⟩` from `@GlobalTheory.T.exists_torsion_quasi_finite_group (X.presheaf.stalk q.1) _ hd _ hc X t.G _ (X.fromSpecStalk q.1) n t.semi hn hft`. Establish `hroot : 0 < D.p + D.q → ∃ ζ : Ω, IsPrimitiveRoot ζ n` using `fun h => root o t m hfull hn h`.

Establish `hw : ∃ e, GenWeil t.G t.PP.L ξ n e`. Break down `Nat.eq_zero_or_pos (D.p + D.q) with h | h` into its components or cases. Conclude with `⟨_, genWeil_trivial o t m hn h⟩`. Use `GlobalTheory.T.exists_generic_weil_pairing GlobalTheory.PairingLawZeroCounterexample.laws.1 E H D l B b (Sp Ω) X s o t ξ m Ω (𝟙 _) n hn (by rwa [Category.id_comp]) (by simpa using hroot h)` as an intermediate fact. Rewrite `this` using `[Category.id_comp]`. Then use the resulting hypothesis.

Take `⟨e, hw⟩` from `hw`. Use `haveI := t.semi.separated`. Use `⟨?_, hroot, (LieModel.htLat_eq_htOm hξ M t.PP.L hn.ne' hfull hw q ⟨hd, T, _, Γ', i, htor⟩).symm⟩` and prove the remaining obligations. Use `HTTie.core_smul (hξ.inj q) (HTTie.hk_stalk ξ q) M Γ' i htor (w := 0) (fun e' v _ _ => ⟨0, by simp⟩)` as an intermediate fact. Rewrite `this` using `[smul_zero]`. Then use the resulting hypothesis.
-/
theorem htOm_eq_htLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (s : Sp Ω ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (_ : SABMap o.t t ξ) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (n : ℕ) (q : Cpt ξ), IsCptGen ξ → 0 < n → FullTorsion t.G ξ n → IsIntegrallyClosed (X.presheaf.stalk q.1) → IsNoetherianRing (X.presheaf.stalk q.1) → M.IsHTFormAt n q 0 ∧ (0 < D.p + D.q → ∃ ζ : Ω, IsPrimitiveRoot ζ n) ∧ M.htOm t.PP.L n q = M.htLat n q := by
  intro E _ _ _ H D l B _ b X Ω _ _ ξ s o t m V _ _ M n q hξ hn hfull hic hno
  haveI := t.semi
  haveI := hic
  haveI := hno
  haveI hd : IsDomain (X.presheaf.stalk q.1) := (hξ.inj q).isDomain (genMap ξ q)
  haveI hc : CharZero (X.presheaf.stalk q.1) := ⟨fun a b h => Nat.cast_injective (R := Ω) (by
    rw [← map_natCast (genMap ξ q), h, map_natCast])⟩
  have hft := fullTorsion_frac hξ q hfull
  obtain ⟨T, _, _, Γ', i, htor⟩ := @GlobalTheory.T.exists_torsion_quasi_finite_group (X.presheaf.stalk q.1) _ hd _ hc X t.G _ (X.fromSpecStalk q.1) n t.semi hn hft
  have hroot : 0 < D.p + D.q → ∃ ζ : Ω, IsPrimitiveRoot ζ n := fun h => root o t m hfull hn h
  have hw : ∃ e, GenWeil t.G t.PP.L ξ n e := by
    rcases Nat.eq_zero_or_pos (D.p + D.q) with h | h
    · exact ⟨_, genWeil_trivial o t m hn h⟩
    · have := GlobalTheory.T.exists_generic_weil_pairing GlobalTheory.PairingLawZeroCounterexample.laws.1 E H D l B b (Sp Ω) X s o t ξ m Ω (𝟙 _) n hn
        (by rwa [Category.id_comp]) (by simpa using hroot h)
      rwa [Category.id_comp] at this
  obtain ⟨e, hw⟩ := hw
  haveI := t.semi.separated
  refine ⟨?_, hroot, (LieModel.htLat_eq_htOm hξ M t.PP.L hn.ne' hfull hw q ⟨hd, T, _, Γ', i, htor⟩).symm⟩
  have := HTTie.core_smul (hξ.inj q) (HTTie.hk_stalk ξ q) M Γ' i htor (w := 0)
    (fun e' v _ _ => ⟨0, by simp⟩)
  rwa [smul_zero] at this

end GlobalTheory.CompanionTheory.Ar.OmLink
