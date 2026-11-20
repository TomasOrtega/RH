import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLevelOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivOfPeriod
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp unitOn omegaStd IsGrpPullback LBIso pushPt)

/- English proof (translation)
Establish `hinj` using `hv.hom_inj`. Establish `: IsDomain O` using `hinj.isDomain`. Establish `: ValuationRing O` using `ValuationRing.of_integers v hv`. Establish `: IsFractionRing O C` using `hv.isFractionRing`. Establish `hex : ValuativeCriterion.Existence X.hom`.

Establish `hu : UniversallyClosed X.hom` using `inferInstance`. Rewrite `hu` using `[UniversallyClosed.eq_valuativeCriterion]`. Conclude with `hu.1`. Establish `huq : ValuativeCriterion.Uniqueness X.hom` using `IsSeparated.valuativeCriterion X.hom`. Establish `he : e.left = Geo.Tor.spMap (algebraMap O C)`.

Establish `hw` using `Over.w e`. Simplify using `using hw`. Establish `hsec : ∀ x : 𝟙_ (Over (Sp O)) ⟶ X, x.left ≫ X.hom = 𝟙 _`. Introduce `x`. Conclude with `Over.w x`.

Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Establish `hxy' : (e ≫ x).left = (e ≫ y).left` using `congrArg CommaMorphism.left hxy`. Set `S : ValuativeCommSq X.hom` to `{ R := O, K := C, i₁ := (e ≫ x).left, i₂ := 𝟙 _, commSq := ⟨by simp [Over.comp_left, hsec x, he]⟩ }`. Establish `hsub` using `huq S`.

Set `lx : S.commSq.LiftStruct` to `{ l := x.left, fac_left := by simp [S, Over.comp_left, he], fac_right := hsec x }`. Set `ly : S.commSq.LiftStruct` to `{ l := y.left, fac_left := by simp [S, hxy', Over.comp_left, he], fac_right := hsec y }`. Establish `hl : lx = ly` using `Subsingleton.elim _ _`. Use `ext`. Conclude with `congrArg CommSq.LiftStruct.l hl`.

Introduce `z`. Set `S : ValuativeCommSq X.hom` to `{ R := O, K := C, i₁ := z.left, i₂ := 𝟙 _, commSq := ⟨by simp⟩ }`. Establish `hl` using `hex S`. Use `⟨Over.homMk S.commSq.lift S.commSq.fac_right, ?_⟩` and prove the remaining obligations. Use `ext`.

Simplify using `only [Over.comp_left, Over.homMk_left, he]`. Conclude with `S.commSq.fac_left`.
-/
private theorem levInt_bij {O C : Type} [CommRing O] [Field C] [Algebra O C]
    {v : Valuation C NNReal} (hv : v.Integers O) (X : Over (Sp O)) [IsProper X.hom]
    (e : Over.mk (Geo.Tor.spMap (algebraMap O C)) ⟶ 𝟙_ (Over (Sp O))) :
    Function.Bijective fun x : 𝟙_ (Over (Sp O)) ⟶ X => e ≫ x := by
  have hinj := hv.hom_inj
  have : IsDomain O := hinj.isDomain
  have : ValuationRing O := ValuationRing.of_integers v hv
  have : IsFractionRing O C := hv.isFractionRing
  have hex : ValuativeCriterion.Existence X.hom := by
    have hu : UniversallyClosed X.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at hu
    exact hu.1
  have huq : ValuativeCriterion.Uniqueness X.hom := IsSeparated.valuativeCriterion X.hom
  have he : e.left = Geo.Tor.spMap (algebraMap O C) := by
    have hw := Over.w e
    simpa using hw
  have hsec : ∀ x : 𝟙_ (Over (Sp O)) ⟶ X, x.left ≫ X.hom = 𝟙 _ := by
    intro x
    exact Over.w x
  constructor
  · intro x y hxy
    have hxy' : (e ≫ x).left = (e ≫ y).left := congrArg CommaMorphism.left hxy
    let S : ValuativeCommSq X.hom :=
      { R := O, K := C, i₁ := (e ≫ x).left, i₂ := 𝟙 _,
        commSq := ⟨by simp [Over.comp_left, hsec x, he]⟩ }
    have hsub := huq S
    let lx : S.commSq.LiftStruct :=
      { l := x.left, fac_left := by simp [S, Over.comp_left, he], fac_right := hsec x }
    let ly : S.commSq.LiftStruct :=
      { l := y.left, fac_left := by simp [S, hxy', Over.comp_left, he], fac_right := hsec y }
    have hl : lx = ly := Subsingleton.elim _ _
    ext
    exact congrArg CommSq.LiftStruct.l hl
  · intro z
    let S : ValuativeCommSq X.hom :=
      { R := O, K := C, i₁ := z.left, i₂ := 𝟙 _,
        commSq := ⟨by simp⟩ }
    have hl := hex S
    refine ⟨Over.homMk S.commSq.lift S.commSq.fac_right, ?_⟩
    ext
    simp only [Over.comp_left, Over.homMk_left, he]
    exact S.commSq.fac_left

/- English proof (translation)
Substitute `hg` using the available equality. Conclude with `levInt_bij hv X e`.
-/
private theorem bijective_comp_of_isProper_integers {O C : Type} [CommRing O] [Field C] [Algebra O C]
    {v : Valuation C NNReal} (hv : v.Integers O) (X : Over (Sp O)) [IsProper X.hom]
    (g : Sp C ⟶ Sp O) (hg : g = Geo.Tor.spMap (algebraMap O C)) (e : Over.mk g ⟶ 𝟙_ (Over (Sp O))) :
    Function.Bijective fun x : 𝟙_ (Over (Sp O)) ⟶ X => e ≫ x := by
  subst hg
  exact levInt_bij hv X e

/- English proof (translation)
Establish `p1 : ∀ (x y : 𝟙_ (Over (Sp O)) ⟶ Q.A) (Z : Over (Sp O)) (f : Z ⟶ 𝟙_ (Over (Sp O))), f ≫ (x * y) = f ≫ x * f ≫ y` using `fun x y _ f => comp_mul f x y`. Establish `p2 : ∀ (x : 𝟙_ (Over (Sp O)) ⟶ Q.A) (Z : Over (Sp O)) (f : Z ⟶ 𝟙_ (Over (Sp O))) (n : ℕ), f ≫ (x ^ n) = (f ≫ x) ^ n` using `fun x _ f n => SymLiftOdd.comp_pow' f x n`. Establish `hprop : IsProper Q.A.hom`. Conclude with `Q.isAb.proper`. Establish `hcomm : IsCommMonObj Q.A` using `Q.isAb.comm`.

Establish `hsecO : ∀ x : 𝟙_ (Over (Sp O)) ⟶ Q.A, x.left ≫ Q.A.hom = 𝟙 _` using `fun x => Over.w x`. Establish `hsecC : ∀ x : 𝟙_ (Over (Sp C)) ⟶ Q'.A, x.left ≫ Q'.A.hom = 𝟙 _` using `fun x => Over.w x`. Set `f` to `Geo.Tor.spMap (algebraMap O C)`. Set `e : Over.mk ((𝟙_ (Over (Sp C))).hom ≫ f) ⟶ 𝟙_ (Over (Sp O))` to `toUnit _`. Establish `he : e.left = f`.

Establish `hw` using `Over.w e`. Simplify using `using hw`. Set `r : (𝟙_ (Over (Sp O)) ⟶ Q.A) → (𝟙_ (Over (Sp C)) ⟶ Q'.A)` to `fun x => Over.homMk (H.1.lift (f ≫ x.left) (𝟙 _) (by rw [Category.assoc, hsecO x]; simp [f])) (H.1.lift_snd _ _ _)`. Establish `hr : ∀ x, (r x).left ≫ ψ = (e ≫ x).left`. Introduce `x`.

Simplify using `[r, he]`. Establish `hext : ∀ a b : 𝟙_ (Over (Sp C)) ⟶ Q'.A, a.left ≫ ψ = b.left ≫ ψ → a = b`. Introduce `a b hab`. Use `ext`. Conclude with `H.1.hom_ext hab (by rw [hsecC a, hsecC b])`.

Establish `hmul : ∀ x y, r (x * y) = r x * r y`. Introduce `x y`. Apply `hext` to reduce the goal to its premises. Rewrite using `[hr, p1]`. Conclude with `H.2 _ (r x) (r y) (e ≫ x) (e ≫ y) (hr x).symm (hr y).symm`.

Establish `hbij` using `bijective_comp_of_isProper_integers hv Q.A _ (by simp [f]) e`. Use `⟨MonoidHom.mk' r hmul, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `x y hxy`. Apply `hbij.1` to reduce the goal to its premises. Establish `hxy' : (r x).left ≫ ψ = (r y).left ≫ ψ`.

Use `congrArg (fun a : 𝟙_ (Over (Sp C)) ⟶ Q'.A => a.left ≫ ψ) hxy` as an intermediate fact. Simplify using `using this`. Rewrite `hxy'` using `[hr, hr]`. Use `ext`. Conclude with `hxy'`.

Introduce `s`. Take `⟨x, hx⟩` from `hbij.2 (Over.homMk (s.left ≫ ψ) (by show (s.left ≫ ψ) ≫ Q.A.hom = (𝟙_ (Over (Sp C))).hom ≫ f`. Rewrite using `[Category.assoc, H.1.w, ← Category.assoc, hsecC s]`. Use the proof step `rfl))`. Use `⟨x, hext _ _ ?_⟩` and prove the remaining obligations.

Simplify using `only at hx`. Rewrite using `[MonoidHom.mk'_apply, hr, hx]`. Both sides reduce to the same expression. Introduce `n x y u hx hy hW`. Establish `hW' : Out.WeilIs Q.A Q.L n (e ≫ x) (e ≫ y) (Geo.Tor.unitOn (Units.map (algebraMap O C).toMonoidHom u))` using `(GlobalTheory.weilIs_grpPullback_of_comm _ _ Q.A Q'.A f ψ Q.L Q'.L Q.isLB Q'.isLB H hw' _ n (r x) (r y) (e ≫ x) (e ≫ y) _ (hr x).symm (hr y).symm).1 hW`.

Take `⟨c, hc, -⟩` from `GlobalTheory.LevelCompare.weil_existsUnique Q n x y hx hy`. Establish `hc'` using `(GlobalTheory.LevelCompare.weil_skew_natural Q n (𝟙_ _)).2 _ e x y c hc`. Establish `hx' : (e ≫ x) ^ n = 1` using `by rw [← p2, hx]; simp`. Establish `hy' : (e ≫ y) ^ n = 1` using `by rw [← p2, hy]; simp`. Take `⟨c2, -, hu⟩` from `GlobalTheory.LevelCompare.weil_existsUnique Q n (e ≫ x) (e ≫ y) hx' hy'`.

Establish `h1` using `(hu _ hW').trans (hu _ hc').symm`. Establish `key : ∀ a : O, e.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a) = (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (algebraMap O C a)`. Introduce `a`. Rewrite using `[he]`. Use `Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap O C))` as an intermediate fact.

Conclude with `(congrArg (fun k => k.hom a) this).symm`. Establish `hmapu : Units.map e.left.appTop.hom.toMonoidHom (Geo.Tor.unitOn u) = Geo.Tor.unitOn (Units.map (algebraMap O C).toMonoidHom u)`. Use `ext`. Simplify using `only [Geo.Tor.unitOn, Units.coe_map]`. Conclude with `key u`.

Establish `hinjA : Function.Injective e.left.appTop.hom`. Introduce `a b hab`. Take `⟨a', rfl⟩ : ∃ a', (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a' = a` from `⟨(Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom a, by simp⟩`. Take `⟨b', rfl⟩ : ∃ b', (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom b' = b` from `⟨(Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom b, by simp⟩`. Rewrite `hab` using `[key, key]`.

Use `congrArg (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom hab` as an intermediate fact. Simplify using `at this`. Rewrite using `[hv.hom_inj this]`. Establish `hcu : c = Geo.Tor.unitOn u` using `Units.map_injective (f := e.left.appTop.hom.toMonoidHom) hinjA (by rw [hmapu]; exact h1.symm)`. Rewrite using `[← hcu]`.

Conclude with `hc`.
-/
private theorem levInt_secHom {O C : Type} [CommRing O] [Field C] [Algebra O C]
    {v : Valuation C NNReal} (hv : v.Integers O) {Q : Out.PolAV (Sp O)}
    {Q' : Out.PolAV (Sp C)} {ψ : Q'.A.left ⟶ Q.A.left}
    (H : IsGrpPullback Q'.A Q.A (Geo.Tor.spMap (algebraMap O C)) ψ) (hw' : LBIso Q'.L (Q.L.pull ψ)) :
    ∃ ρ : (𝟙_ (Over (Sp O)) ⟶ Q.A) →* (𝟙_ (Over (Sp C)) ⟶ Q'.A), Function.Bijective ρ ∧
      ∀ (n : ℕ) x y (u : Oˣ), x ^ n = 1 → y ^ n = 1 →
        Out.WeilIs Q'.A Q'.L n (ρ x) (ρ y) (unitOn (Units.map (algebraMap O C).toMonoidHom u)) →
        Out.WeilIs Q.A Q.L n x y (unitOn u) := by
  have p1 : ∀ (x y : 𝟙_ (Over (Sp O)) ⟶ Q.A) (Z : Over (Sp O)) (f : Z ⟶ 𝟙_ (Over (Sp O))),
      f ≫ (x * y) = f ≫ x * f ≫ y := fun x y _ f => comp_mul f x y
  have p2 : ∀ (x : 𝟙_ (Over (Sp O)) ⟶ Q.A) (Z : Over (Sp O)) (f : Z ⟶ 𝟙_ (Over (Sp O))) (n : ℕ),
      f ≫ (x ^ n) = (f ≫ x) ^ n := fun x _ f n => SymLiftOdd.comp_pow' f x n
  have hprop : IsProper Q.A.hom := by
    exact Q.isAb.proper
  have hcomm : IsCommMonObj Q.A := Q.isAb.comm
  have hsecO : ∀ x : 𝟙_ (Over (Sp O)) ⟶ Q.A, x.left ≫ Q.A.hom = 𝟙 _ := fun x => Over.w x
  have hsecC : ∀ x : 𝟙_ (Over (Sp C)) ⟶ Q'.A, x.left ≫ Q'.A.hom = 𝟙 _ := fun x => Over.w x
  let f := Geo.Tor.spMap (algebraMap O C)
  let e : Over.mk ((𝟙_ (Over (Sp C))).hom ≫ f) ⟶ 𝟙_ (Over (Sp O)) := toUnit _
  have he : e.left = f := by
    have hw := Over.w e
    simpa using hw
  let r : (𝟙_ (Over (Sp O)) ⟶ Q.A) → (𝟙_ (Over (Sp C)) ⟶ Q'.A) := fun x =>
    Over.homMk (H.1.lift (f ≫ x.left) (𝟙 _) (by rw [Category.assoc, hsecO x]; simp [f])) (H.1.lift_snd _ _ _)
  have hr : ∀ x, (r x).left ≫ ψ = (e ≫ x).left := by
    intro x
    simp [r, he]
  have hext : ∀ a b : 𝟙_ (Over (Sp C)) ⟶ Q'.A, a.left ≫ ψ = b.left ≫ ψ → a = b := by
    intro a b hab
    ext
    exact H.1.hom_ext hab (by rw [hsecC a, hsecC b])
  have hmul : ∀ x y, r (x * y) = r x * r y := by
    intro x y
    apply hext
    rw [hr, p1]
    exact H.2 _ (r x) (r y) (e ≫ x) (e ≫ y) (hr x).symm (hr y).symm
  have hbij := bijective_comp_of_isProper_integers hv Q.A _ (by simp [f]) e
  refine ⟨MonoidHom.mk' r hmul, ⟨?_, ?_⟩, ?_⟩
  · intro x y hxy
    apply hbij.1
    have hxy' : (r x).left ≫ ψ = (r y).left ≫ ψ := by
      have := congrArg (fun a : 𝟙_ (Over (Sp C)) ⟶ Q'.A => a.left ≫ ψ) hxy
      simpa using this
    rw [hr, hr] at hxy'
    ext
    exact hxy'
  · intro s
    obtain ⟨x, hx⟩ := hbij.2 (Over.homMk (s.left ≫ ψ) (by
      show (s.left ≫ ψ) ≫ Q.A.hom = (𝟙_ (Over (Sp C))).hom ≫ f
      rw [Category.assoc, H.1.w, ← Category.assoc, hsecC s]
      rfl))
    refine ⟨x, hext _ _ ?_⟩
    simp only at hx
    rw [MonoidHom.mk'_apply, hr, hx]
    rfl
  · intro n x y u hx hy hW
    have hW' : Out.WeilIs Q.A Q.L n (e ≫ x) (e ≫ y)
        (Geo.Tor.unitOn (Units.map (algebraMap O C).toMonoidHom u)) :=
      (GlobalTheory.weilIs_grpPullback_of_comm _ _ Q.A Q'.A f ψ Q.L Q'.L Q.isLB Q'.isLB H hw' _ n (r x) (r y)
        (e ≫ x) (e ≫ y) _ (hr x).symm (hr y).symm).1 hW
    obtain ⟨c, hc, -⟩ := GlobalTheory.LevelCompare.weil_existsUnique Q n x y hx hy
    have hc' := (GlobalTheory.LevelCompare.weil_skew_natural Q n (𝟙_ _)).2 _ e x y c hc
    have hx' : (e ≫ x) ^ n = 1 := by rw [← p2, hx]; simp
    have hy' : (e ≫ y) ^ n = 1 := by rw [← p2, hy]; simp
    obtain ⟨c2, -, hu⟩ := GlobalTheory.LevelCompare.weil_existsUnique Q n (e ≫ x) (e ≫ y) hx' hy'
    have h1 := (hu _ hW').trans (hu _ hc').symm
    have key : ∀ a : O, e.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a) =
        (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (algebraMap O C a) := by
      intro a
      rw [he]
      have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap O C))
      exact (congrArg (fun k => k.hom a) this).symm
    have hmapu : Units.map e.left.appTop.hom.toMonoidHom (Geo.Tor.unitOn u) =
        Geo.Tor.unitOn (Units.map (algebraMap O C).toMonoidHom u) := by
      ext
      simp only [Geo.Tor.unitOn, Units.coe_map]
      exact key u
    have hinjA : Function.Injective e.left.appTop.hom := by
      intro a b hab
      obtain ⟨a', rfl⟩ : ∃ a', (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a' = a :=
        ⟨(Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom a, by simp⟩
      obtain ⟨b', rfl⟩ : ∃ b', (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom b' = b :=
        ⟨(Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom b, by simp⟩
      rw [key, key] at hab
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom hab
      simp at this
      rw [hv.hom_inj this]
    have hcu : c = Geo.Tor.unitOn u :=
      Units.map_injective (f := e.left.appTop.hom.toMonoidHom) hinjA (by rw [hmapu]; exact h1.symm)
    rw [← hcu]
    exact hc

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ hv _ _ T _ _ P₀ io P φ hφ hL hg h M ze hh hM hze`. Take `⟨Q', g, hpb, hgg, hmul, t, ht⟩` from `(polBaseChange_holds : Out.PolBaseChangeSt) _ _ (Geo.Tor.spMap (algebraMap O C)) P`. Establish `hGP : Geo.Tor.IsGrpPullback Q'.A P.A (Geo.Tor.spMap (algebraMap O C)) g`. Use `⟨hpb, ?_⟩` and prove the remaining obligations. Introduce `T' x y x₀ y₀ hx hy`.

Establish `ex : ∀ (z : T' ⟶ Q'.A) (z₀ : Over.mk (T'.hom ≫ Geo.Tor.spMap (algebraMap O C)) ⟶ P.A), z₀.left = z.left ≫ g → z₀ = Out.toBase hpb.w z`. Introduce `z z₀ hz`. Use `ext`. Rewrite using `[hz]`. Unfold `Out.toBase`.

Simplify using the standard rewrite rules. Rewrite using `[ex x x₀ hx, ex y y₀ hy, ← hmul]`. Unfold `Out.toBase`. Simplify using the standard rewrite rules. Establish `hLB : Geo.Tor.LBIso Q'.L (P.L.pull g)` using `Geo.Tor.LBIso.symm ⟨t, ht⟩`.

Establish `hOnt : Nontrivial O` using `(algebraMap O C).domain_nontrivial`. Establish `hM0 : M ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hM`. Establish `hNZ : NeZero M` using `⟨hM0⟩`.

Establish `hMC : (M : C) ≠ 0` using `by simpa using (hM.map (algebraMap O C)).ne_zero`. Set `zeC : Cˣ` to `Units.map (algebraMap O C).toMonoidHom ze`. Establish `hzeC : IsPrimitiveRoot zeC M`. Rewrite using `[← IsPrimitiveRoot.coe_units_iff]`. Simplify `hze` using `[zeC]`.

Take `⟨ℓ⟩` from `GlobalTheory.nonempty_level_of_isAlgClosed C Q' M zeC hMC hzeC`. Take `⟨ρ, hρ, hW⟩` from `levInt_secHom hv hGP hLB`. Set `E` to `MulEquiv.ofBijective ρ hρ`. Establish `hg' : Q'.g = h` using `hgg.trans hh`. Set `σ : Fin Q'.g ⊕ Fin Q'.g ≃ Fin h ⊕ Fin h` to `Equiv.sumCongr (finCongr hg') (finCongr hg')`.

Set `levC : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Geo.Tor.Sp C)) ⟶ Q'.A)` to `fun x => GlobalTheory.LevelCompare.homOfBasis ℓ (Multiplicative.ofAdd (IndefiniteRowSideFullHecke.LevelStructureForms.reduce M (x ∘ σ)))`. Establish `hω : ∀ x y : Fin h ⊕ Fin h → ℤ, IndefiniteRowSideFullHecke.LevelStructureForms.stdForm (x ∘ σ) (y ∘ σ) = Geo.Tor.omegaStd x y`. Introduce `x y`. Unfold `IndefiniteRowSideFullHecke.LevelStructureForms.stdForm Geo.Tor.omegaStd`. Conclude with `Equiv.sum_comp (finCongr hg') (fun j => x (Sum.inl j) * y (Sum.inr j) - x (Sum.inr j) * y (Sum.inl j))`.

Establish `hpow : ∀ x, levC x ^ M = 1` using `fun x => GlobalTheory.LevelCompare.hom_pow _ _`. Establish `h1 : ∀ z, ρ (E.symm z) = z` using `fun z => E.apply_symm_apply z`. Use `⟨fun x => E.symm (levC x), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y show E.symm (levC (x + y)) = E.symm (levC x) * E.symm (levC y)`. Simplify using `only [levC]`.

Rewrite using `[show (x + y) ∘ σ = x ∘ σ + y ∘ σ from rfl, GlobalTheory.LevelCompare.reduce_add, ofAdd_add, map_mul, map_mul]`. Introduce `x show E.symm (levC x) ^ M = 1`. Rewrite using `[← map_pow, hpow, map_one]`. Introduce `x y`. Apply `hW M _ _ (ze ^ Geo.Tor.omegaStd x y)` to reduce the goal to its premises.

Rewrite using `[← map_pow, hpow, map_one]`. Rewrite using `[← map_pow, hpow, map_one]`. Rewrite using `[h1, h1]`. Establish `hp` using `GlobalTheory.LevelCompare.pairing_of_basis ℓ (x ∘ σ) (y ∘ σ)`. Rewrite `hp` using `[hω]`.

Use `hp using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Geo.Tor.unitOn, zeC, map_zpow]`.
-/
theorem exists_level_over_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (T : Type) [CommRing T] [IsNoetherianRing T] (P₀ : Out.PolAV (Geo.Tor.Sp T)) (io : T →+* O) (P : Out.PolAV (Geo.Tor.Sp O)) (φ : P.A.left ⟶ P₀.A.left), Geo.Tor.IsGrpPullback P.A P₀.A (Geo.Tor.spMap io) φ → Geo.Tor.LBIso P.L (P₀.L.pull φ) → P.g = P₀.g → ∀ (h M : ℕ) (ze : Oˣ), P.g = h → IsUnit (M : O) → IsPrimitiveRoot (algebraMap O C ze) M → ∃ lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Geo.Tor.Sp O)) ⟶ P.A), (∀ x y, lev (x + y) = lev x * lev y) ∧ (∀ x, lev x ^ M = 1) ∧ ∀ x y, Out.WeilIs P.A P.L M (lev x) (lev y) (Geo.Tor.unitOn (ze ^ Geo.Tor.omegaStd x y)) := by
  intro p _ C _ _ _ v O _ _ hv _ _ T _ _ P₀ io P φ hφ hL hg h M ze hh hM hze
  obtain ⟨Q', g, hpb, hgg, hmul, t, ht⟩ :=
    (polBaseChange_holds : Out.PolBaseChangeSt) _ _ (Geo.Tor.spMap (algebraMap O C)) P
  have hGP : Geo.Tor.IsGrpPullback Q'.A P.A (Geo.Tor.spMap (algebraMap O C)) g := by
    refine ⟨hpb, ?_⟩
    intro T' x y x₀ y₀ hx hy
    have ex : ∀ (z : T' ⟶ Q'.A) (z₀ : Over.mk (T'.hom ≫ Geo.Tor.spMap (algebraMap O C)) ⟶ P.A),
        z₀.left = z.left ≫ g → z₀ = Out.toBase hpb.w z := by
      intro z z₀ hz
      ext
      rw [hz]
      unfold Out.toBase
      simp
    rw [ex x x₀ hx, ex y y₀ hy, ← hmul]
    unfold Out.toBase
    simp
  have hLB : Geo.Tor.LBIso Q'.L (P.L.pull g) := Geo.Tor.LBIso.symm ⟨t, ht⟩
  have hOnt : Nontrivial O := (algebraMap O C).domain_nontrivial
  have hM0 : M ≠ 0 := by
    rintro rfl
    simp at hM
  have hNZ : NeZero M := ⟨hM0⟩
  have hMC : (M : C) ≠ 0 := by simpa using (hM.map (algebraMap O C)).ne_zero
  let zeC : Cˣ := Units.map (algebraMap O C).toMonoidHom ze
  have hzeC : IsPrimitiveRoot zeC M := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    simpa [zeC] using hze
  obtain ⟨ℓ⟩ := GlobalTheory.nonempty_level_of_isAlgClosed C Q' M zeC hMC hzeC
  obtain ⟨ρ, hρ, hW⟩ := levInt_secHom hv hGP hLB
  let E := MulEquiv.ofBijective ρ hρ
  have hg' : Q'.g = h := hgg.trans hh
  let σ : Fin Q'.g ⊕ Fin Q'.g ≃ Fin h ⊕ Fin h := Equiv.sumCongr (finCongr hg') (finCongr hg')
  let levC : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Geo.Tor.Sp C)) ⟶ Q'.A) := fun x =>
    GlobalTheory.LevelCompare.homOfBasis ℓ (Multiplicative.ofAdd (IndefiniteRowSideFullHecke.LevelStructureForms.reduce M (x ∘ σ)))
  have hω : ∀ x y : Fin h ⊕ Fin h → ℤ,
      IndefiniteRowSideFullHecke.LevelStructureForms.stdForm (x ∘ σ) (y ∘ σ) = Geo.Tor.omegaStd x y := by
    intro x y
    unfold IndefiniteRowSideFullHecke.LevelStructureForms.stdForm Geo.Tor.omegaStd
    exact Equiv.sum_comp (finCongr hg')
      (fun j => x (Sum.inl j) * y (Sum.inr j) - x (Sum.inr j) * y (Sum.inl j))
  have hpow : ∀ x, levC x ^ M = 1 := fun x => GlobalTheory.LevelCompare.hom_pow _ _
  have h1 : ∀ z, ρ (E.symm z) = z := fun z => E.apply_symm_apply z
  refine ⟨fun x => E.symm (levC x), ?_, ?_, ?_⟩
  · intro x y
    show E.symm (levC (x + y)) = E.symm (levC x) * E.symm (levC y)
    simp only [levC]
    rw [show (x + y) ∘ σ = x ∘ σ + y ∘ σ from rfl, GlobalTheory.LevelCompare.reduce_add, ofAdd_add, map_mul,
      map_mul]
  · intro x
    show E.symm (levC x) ^ M = 1
    rw [← map_pow, hpow, map_one]
  · intro x y
    apply hW M _ _ (ze ^ Geo.Tor.omegaStd x y)
    · rw [← map_pow, hpow, map_one]
    · rw [← map_pow, hpow, map_one]
    · rw [h1, h1]
      have hp := GlobalTheory.LevelCompare.pairing_of_basis ℓ (x ∘ σ) (y ∘ σ)
      rw [hω] at hp
      convert hp using 1
      simp only [Geo.Tor.unitOn, zeC, map_zpow]

end GlobalTheory
