import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TorsionRationalOverFiniteExtensionLevelStructure
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsCdvrFiniteExtension
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFramedPointBaseChangeStable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsExtensionAllModelsUniformized
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularReframeCompBaseChangeBorel
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralIff
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.VVAlgebraMapNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTraceOrthogonalityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralScalarOfPulledBackGeneratorExtendsModelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModuliPointIntegralFrameAfterFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieLatticeOntoStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaTraceBaseChangeIffStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumSymmetricTranslatesThetaPullbackExtendsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsExtPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearHeckeIsogenyInverseUpToPSqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsRigIsoOfBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTraceIsTranslSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FibreIsogenyPairDefinedOverFiniteSubextensionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFibreMapBaseChangeAndIsogenyPairIffStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAndIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFrameExtensionOfRankZeroSignatureStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieImageCompatibleWithBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsProperModelOfExtendsFibreIsogenyStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramedPointDescendsFiniteSubextensionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodReductionStableValuationRingExtensionStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HkIntegral

open GlobalTheory.FlagTan GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39

/- English proof (translation)
Use `letI := j.toAlgebra`. Use `letI := i.toAlgebra`. Use `haveI : Module.Finite L L' := hi`. Set `τ : L' →ₐ[L] Ω` to `IsAlgClosed.lift`. Conclude with `⟨τ.toRingHom, RingHom.ext fun a => τ.commutes a⟩`.
-/
theorem exists_lift {L L' Ω : Type} [Field L] [Field L'] [Field Ω] [IsAlgClosed Ω] (j : L →+* Ω) (i : L →+* L')
    (hi : i.Finite) : ∃ j' : L' →+* Ω, j'.comp i = j := by
  letI := j.toAlgebra
  letI := i.toAlgebra
  haveI : Module.Finite L L' := hi
  let τ : L' →ₐ[L] Ω := IsAlgClosed.lift
  exact ⟨τ.toRingHom, RingHom.ext fun a => τ.commutes a⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Establish `e₁` using `(GlobalTheory.T.exists_fibreMap_baseChange_and_isogenyPair_iff E H Dw l Xo K L φ.toRingHom y.x z.x y'.x z'.x).2 f f' g g' (p ^ 2) h h'`. Establish `e₂ : ∀ τ j, IsLieImageH p f.left (y.u τ j) (z.u τ j) ↔ IsLieImageH p g.left (y'.u τ j) (z'.u τ j)` using `fun τ j => by`. Rewrite using `[hy.2.1, hz.2.1]`. Conclude with `GlobalTheory.T.lie_image_compatible_with_base_change E H Dw l Xo K L φ.toRingHom y.x z.x y'.x z'.x f g p _ _ h (y.tan τ j)`. Establish `e₃` using `fun a b => GlobalTheory.T.isThetaTrace_conj_iff_of_rigIso E H Dw l Xo c K L φ y z y' z' f f' g p hp hy hz a h hR b`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, b, d⟩`. Establish `⟨β, _, _, _, _, _, hβ, _⟩` using `d`. Conclude with `⟨e₁.1 a, fun τ j => (e₂ τ j).1 (b τ j), (e₃ a ⟨β, hβ⟩).1 d⟩`. Introduce and unpack `⟨a, b, d⟩`.

Establish `⟨β, _, _, _, _, _, hβ, _⟩` using `d`. Establish `a'` using `e₁.2 a`. Conclude with `⟨a', fun τ j => (e₂ τ j).2 (b τ j), (e₃ a' (GlobalTheory.T.exists_isRigIso_of_baseChange' E H Dw l Xo K L φ.toRingHom y.x z.x y'.x z'.x f g _ h a'.1 ⟨β, hβ⟩)).2 d⟩`.
-/
theorem hkWith_iff {K L : Type} [Field K] [Field L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) {p : ℕ}
    (hp : 0 < p) {y z : FrPt Xo c K} {y' z' : FrPt Xo c L} (hy : FrMap φ y y') (hz : FrMap φ z z')
    {f : Fib Xo y.x ⟶ Fib Xo z.x} {f' : Fib Xo z.x ⟶ Fib Xo y.x} {g : Fib Xo y'.x ⟶ Fib Xo z'.x}
    {g' : Fib Xo z'.x ⟶ Fib Xo y'.x} (h : IsBC φ.toRingHom f g) (h' : IsBC φ.toRingHom f' g')
    (hR : AllRat Xo y.x (p ^ 2)) : HkWith p y z f f' ↔ HkWith p y' z' g g' := by
  have e₁ := (GlobalTheory.T.exists_fibreMap_baseChange_and_isogenyPair_iff E H Dw l Xo K L φ.toRingHom y.x z.x y'.x z'.x).2 f f' g g' (p ^ 2) h h'
  have e₂ : ∀ τ j, IsLieImageH p f.left (y.u τ j) (z.u τ j) ↔ IsLieImageH p g.left (y'.u τ j) (z'.u τ j) :=
    fun τ j => by
      rw [hy.2.1, hz.2.1]
      exact GlobalTheory.T.lie_image_compatible_with_base_change E H Dw l Xo K L φ.toRingHom y.x z.x y'.x z'.x f g p _ _ h (y.tan τ j)
  have e₃ := fun a b => GlobalTheory.T.isThetaTrace_conj_iff_of_rigIso E H Dw l Xo c K L φ y z y' z' f f' g p hp hy hz a h hR b
  constructor
  · rintro ⟨a, b, d⟩
    have ⟨β, _, _, _, _, _, hβ, _⟩ := d
    exact ⟨e₁.1 a, fun τ j => (e₂ τ j).1 (b τ j), (e₃ a ⟨β, hβ⟩).1 d⟩
  · rintro ⟨a, b, d⟩
    have ⟨β, _, _, _, _, _, hβ, _⟩ := d
    have a' := e₁.2 a
    exact ⟨a', fun τ j => (e₂ τ j).2 (b τ j),
      (e₃ a' (GlobalTheory.T.exists_isRigIso_of_baseChange' E H Dw l Xo K L φ.toRingHom y.x z.x y'.x z'.x f g _ h a'.1 ⟨β, hβ⟩)).2 d⟩

/- English proof (translation)
The claim follows from `hw ▸ ((torsion_rational_over_finite_extension E H Dw l Xo K x M hM).2 h).1 L φ`.
-/
theorem allRat_up {K L : Type} [Field K] [Field L] (φ : K →+* L) {x : Sp K ⟶ Xo.X} {w : Sp L ⟶ Xo.X} {M : ℕ}
    (hM : 0 < M) (hw : w = spMap φ ≫ x) (h : AllRat Xo x M) : AllRat Xo w M :=
  hw ▸ ((torsion_rational_over_finite_extension E H Dw l Xo K x M hM).2 h).1 L φ

/- English proof (translation)
Take `⟨h₁, h₂, f, f', h⟩` from `h`. Take `⟨g, hg⟩` from `(GlobalTheory.T.exists_fibreMap_baseChange_and_isogenyPair_iff E H Dw l Xo K L φ.toRingHom y.x z.x y'.x z'.x).1 hy.1 hz.1 f`. Take `⟨g', hg'⟩` from `(GlobalTheory.T.exists_fibreMap_baseChange_and_isogenyPair_iff E H Dw l Xo K L φ.toRingHom z.x y.x z'.x y'.x).1 hz.1 hy.1 f'`. Conclude with `⟨allRat_up _ (pow_pos hp _) hy.1 h₁, allRat_up _ (pow_pos hp _) hz.1 h₂, g, g', (hkWith_iff φ hp hy hz hg hg' h₁).1 h⟩`.
-/
theorem HkOver.up {K L : Type} [Field K] [Field L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) {p : ℕ}
    (hp : 0 < p) {y z : FrPt Xo c K} {y' z' : FrPt Xo c L} (hy : FrMap φ y y') (hz : FrMap φ z z')
    (h : HkOver p y z) : HkOver p y' z' := by
  obtain ⟨h₁, h₂, f, f', h⟩ := h
  obtain ⟨g, hg⟩ := (GlobalTheory.T.exists_fibreMap_baseChange_and_isogenyPair_iff E H Dw l Xo K L φ.toRingHom y.x z.x y'.x z'.x).1 hy.1 hz.1 f
  obtain ⟨g', hg'⟩ := (GlobalTheory.T.exists_fibreMap_baseChange_and_isogenyPair_iff E H Dw l Xo K L φ.toRingHom z.x y.x z'.x y'.x).1 hz.1 hy.1 f'
  exact ⟨allRat_up _ (pow_pos hp _) hy.1 h₁, allRat_up _ (pow_pos hp _) hz.1 h₂, g, g',
    (hkWith_iff φ hp hy hz hg hg' h₁).1 h⟩

/- English proof (translation)
Take `⟨g, g', h⟩` from `h`. Take `⟨L₁, _, _, i₁, j₁, z₁, e₁, f₁, hz₁⟩` from `GlobalTheory.T.framedPoint_descends_finite_subextension E H Dw l Xo c K Ω k z hk`. Take `⟨y₁, hy₁⟩` from `exists_frMap i₁ y`. Establish `hw₁ : FrMap j₁ y₁ w` using `frMap_of_comp hy₁ hw fun a => DFunLike.congr_fun e₁ a`. Take `⟨L₂, _, _, f₂, r₂⟩` from `(torsion_rational_over_finite_extension E H Dw l Xo L₁ y₁.x _ (pow_pos hp 2)).1`.

Take `⟨L₃, _, _, f₃, r₃⟩` from `(torsion_rational_over_finite_extension E H Dw l Xo L₂ (spMap (algebraMap L₁ L₂) ≫ z₁.x) _ (pow_pos hp 3)).1`. Set `a : L₁ →+* L₃` to `(algebraMap L₂ L₃).comp (algebraMap L₁ L₂)`. Establish `fa : a.Finite` using `(RingHom.finite_algebraMap.2 f₃).comp (RingHom.finite_algebraMap.2 f₂)`. Take `⟨j₃, e₃⟩` from `exists_lift j₁.toRingHom a fa`. Establish `hint : j₃.IsIntegral`.

Use `RingHom.IsIntegral.tower_top (a.comp i₁.toRingHom) j₃ ?_` and prove the remaining obligations. Rewrite using `[← RingHom.comp_assoc, e₃]`. Substitute `e₁` using the available equality. Conclude with `hk`. Establish `sq : ∀ x : Sp L₁ ⟶ Xo.X, spMap j₁.toRingHom ≫ x = spMap j₃ ≫ spMap a ≫ x` using `fun x => by`.

Rewrite using `[← Category.assoc, TorsionRat.sp_comp, e₃]`. Take `⟨M, _, i₄, j₄, e₄, f₄, hM⟩` from `GlobalTheory.T.fibreIsogenyPair_defined_over_finite_subextension E H Dw l Xo L₃ Ω j₃ (spMap a ≫ y₁.x) (spMap a ≫ z₁.x) w.x z.x g g' hint (hw₁.1.trans (sq _)) (hz₁.1.trans (sq _)) h.1.1 h.1.2.1`. Use `letI : Algebra c.F M := ((i₄.comp a).comp (algebraMap c.F L₁)).toAlgebra`. Set `b : L₁ →ₐ[c.F] M` to `⟨i₄.comp a, fun _ => rfl⟩`. Establish `eb : ∀ u, j₄ (b u) = j₁ u` using `fun u => (DFunLike.congr_fun e₄ (a u)).trans (DFunLike.congr_fun e₃ u)`.

Set `j : M →ₐ[c.F] Ω` to `⟨j₄, fun u => (eb _).trans (j₁.commutes u)⟩`. Take `⟨y', hy'⟩` from `exists_frMap b y₁`. Take `⟨z', hz'⟩` from `exists_frMap b z₁`. Establish `sq' : ∀ x : Sp L₁ ⟶ Xo.X, spMap b.toRingHom ≫ x = spMap i₄ ≫ spMap a ≫ x` using `fun x => by`. Rewrite using `[← Category.assoc, TorsionRat.sp_comp]`.

Take `⟨f, f', hf, hf'⟩` from `hM y'.x z'.x (hy'.1.trans (sq' _)) (hz'.1.trans (sq' _))`. Establish `hyw : FrMap j y' w` using `frMap_of_comp hy' hw₁ eb`. Establish `hzz : FrMap j z' z` using `frMap_of_comp hz' hz₁ eb`. Establish `R₁ : AllRat Xo y'.x (p ^ 2)` using `allRat_up (i₄.comp (algebraMap L₂ L₃)) (pow_pos hp _) (hy'.1.trans (by rw [← Category.assoc, TorsionRat.sp_comp])) r₂`. Establish `R₂ : AllRat Xo z'.x (p ^ 3)` using `allRat_up i₄ (pow_pos hp _) (hz'.1.trans (by rw [← Category.assoc, ← Category.assoc, TorsionRat.sp_comp, TorsionRat.sp_comp])) r₃`.

Use `⟨M, inferInstance, inferInstance, b.comp i₁, j, y', z', AlgHom.ext fun u => (eb _).trans (DFunLike.congr_fun e₁ u), (f₄.comp fa).comp f₁, frMap_comp hy₁ hy' fun _ => rfl, hzz, R₁, R₂, f, f', (hkWith_iff j hp hyw hzz hf hf' R₁).2 h⟩` and prove the remaining obligations.
-/
theorem exists_hkOver {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω] [Algebra c.F K] [Algebra c.F Ω]
    (k : K →ₐ[c.F] Ω) (hk : k.toRingHom.IsIntegral) {p : ℕ} (hp : 0 < p) {y : FrPt Xo c K} {w z : FrPt Xo c Ω}
    (hw : FrMap k y w) (h : ∃ g g', HkWith p w z g g') :
    ∃ (L : Type) (_ : Field L) (_ : Algebra c.F L) (i : K →ₐ[c.F] L) (j : L →ₐ[c.F] Ω) (y' z' : FrPt Xo c L),
      j.comp i = k ∧ i.toRingHom.Finite ∧ FrMap i y y' ∧ FrMap j z' z ∧ HkOver p y' z' := by
  obtain ⟨g, g', h⟩ := h
  obtain ⟨L₁, _, _, i₁, j₁, z₁, e₁, f₁, hz₁⟩ := GlobalTheory.T.framedPoint_descends_finite_subextension E H Dw l Xo c K Ω k z hk
  obtain ⟨y₁, hy₁⟩ := exists_frMap i₁ y
  have hw₁ : FrMap j₁ y₁ w := frMap_of_comp hy₁ hw fun a => DFunLike.congr_fun e₁ a
  obtain ⟨L₂, _, _, f₂, r₂⟩ := (torsion_rational_over_finite_extension E H Dw l Xo L₁ y₁.x _ (pow_pos hp 2)).1
  obtain ⟨L₃, _, _, f₃, r₃⟩ := (torsion_rational_over_finite_extension E H Dw l Xo L₂
    (spMap (algebraMap L₁ L₂) ≫ z₁.x) _ (pow_pos hp 3)).1
  let a : L₁ →+* L₃ := (algebraMap L₂ L₃).comp (algebraMap L₁ L₂)
  have fa : a.Finite := (RingHom.finite_algebraMap.2 f₃).comp (RingHom.finite_algebraMap.2 f₂)
  obtain ⟨j₃, e₃⟩ := exists_lift j₁.toRingHom a fa
  have hint : j₃.IsIntegral := by
    refine RingHom.IsIntegral.tower_top (a.comp i₁.toRingHom) j₃ ?_
    rw [← RingHom.comp_assoc, e₃]
    subst e₁
    exact hk
  have sq : ∀ x : Sp L₁ ⟶ Xo.X, spMap j₁.toRingHom ≫ x = spMap j₃ ≫ spMap a ≫ x := fun x => by
    rw [← Category.assoc, TorsionRat.sp_comp, e₃]
  obtain ⟨M, _, i₄, j₄, e₄, f₄, hM⟩ := GlobalTheory.T.fibreIsogenyPair_defined_over_finite_subextension E H Dw l Xo L₃ Ω j₃ (spMap a ≫ y₁.x) (spMap a ≫ z₁.x) w.x z.x g g'
    hint (hw₁.1.trans (sq _)) (hz₁.1.trans (sq _)) h.1.1 h.1.2.1
  letI : Algebra c.F M := ((i₄.comp a).comp (algebraMap c.F L₁)).toAlgebra
  let b : L₁ →ₐ[c.F] M := ⟨i₄.comp a, fun _ => rfl⟩
  have eb : ∀ u, j₄ (b u) = j₁ u := fun u =>
    (DFunLike.congr_fun e₄ (a u)).trans (DFunLike.congr_fun e₃ u)
  let j : M →ₐ[c.F] Ω := ⟨j₄, fun u => (eb _).trans (j₁.commutes u)⟩
  obtain ⟨y', hy'⟩ := exists_frMap b y₁
  obtain ⟨z', hz'⟩ := exists_frMap b z₁
  have sq' : ∀ x : Sp L₁ ⟶ Xo.X, spMap b.toRingHom ≫ x = spMap i₄ ≫ spMap a ≫ x := fun x => by
    rw [← Category.assoc, TorsionRat.sp_comp]
  obtain ⟨f, f', hf, hf'⟩ := hM y'.x z'.x (hy'.1.trans (sq' _)) (hz'.1.trans (sq' _))
  have hyw : FrMap j y' w := frMap_of_comp hy' hw₁ eb
  have hzz : FrMap j z' z := frMap_of_comp hz' hz₁ eb
  have R₁ : AllRat Xo y'.x (p ^ 2) := allRat_up (i₄.comp (algebraMap L₂ L₃)) (pow_pos hp _)
    (hy'.1.trans (by rw [← Category.assoc, TorsionRat.sp_comp])) r₂
  have R₂ : AllRat Xo z'.x (p ^ 3) := allRat_up i₄ (pow_pos hp _)
    (hz'.1.trans (by rw [← Category.assoc, ← Category.assoc, TorsionRat.sp_comp, TorsionRat.sp_comp])) r₃
  refine ⟨M, inferInstance, inferInstance, b.comp i₁, j, y', z', AlgHom.ext fun u => (eb _).trans
    (DFunLike.congr_fun e₁ u), (f₄.comp fa).comp f₁, frMap_comp hy₁ hy' fun _ => rfl, hzz, R₁, R₂, f, f',
    (hkWith_iff j hp hyw hzz hf hf' R₁).2 h⟩

/- English proof (translation)
Take `⟨x, xo, u, tan, eig, basis, s, gen⟩` from `z`. Take `⟨hx, -, pm, h₁, h₂, h₃⟩` from `hb`. Simplify using `only at hx`. Substitute `hx` using the available equality. Take `rfl : pm = 𝟙 _` from `gx_ext (h₂.trans (Category.id_comp _).symm) (h₁.trans (Category.id_comp _).symm)`.

Use `⟨u, tan, eig, basis, s, gen, rfl, fun i => ?_⟩` and prove the remaining obligations. Establish `e : Scheme.Hom.appLE (𝟙 (Gx y.x)) ((PPx y.x).U i) ((PPx y.x).U i) le_rfl = 𝟙 _`. Simplify using `only [Scheme.Hom.appLE, Scheme.Hom.id_app]`. Conclude with `(Category.id_comp _).trans (CategoryTheory.Functor.map_id _ _)`. Use `h₃ i le_rfl` as an intermediate fact.

Rewrite `this` using `[e]`. Conclude with `this.symm`.
-/
theorem frBor_reduce {S : Type} [CommRing S] [Algebra c.F S] {y z : FrPt Xo c S} {t : Ix Dw → Sˣ}
    (hb : FrBor t y z) : ∃ u tan eig basis s gen, z = ⟨y.x, y.x_over, u, tan, eig, basis, s, gen⟩ ∧
      ∀ i, s.f i = scal y.x (t none : S) i * y.s.f i := by
  obtain ⟨x, xo, u, tan, eig, basis, s, gen⟩ := z
  obtain ⟨hx, -, pm, h₁, h₂, h₃⟩ := hb
  dsimp only at hx
  subst hx
  obtain rfl : pm = 𝟙 _ := gx_ext (h₂.trans (Category.id_comp _).symm) (h₁.trans (Category.id_comp _).symm)
  refine ⟨u, tan, eig, basis, s, gen, rfl, fun i => ?_⟩
  have e : Scheme.Hom.appLE (𝟙 (Gx y.x)) ((PPx y.x).U i) ((PPx y.x).U i) le_rfl = 𝟙 _ := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (Category.id_comp _).trans (CategoryTheory.Functor.map_id _ _)
  have := h₃ i le_rfl
  rw [e] at this
  exact this.symm

/- English proof (translation)
Take `⟨g, hg2, hg1, hg⟩` from `(GlobalTheory.Frames.frBor_iff_frChg y y' t).1 h`. Establish `hc` using `(frMap_iff_frChg hg hz).1 hz'`. Conclude with `(GlobalTheory.Frames.frBor_iff_frChg z z' _).2 ⟨fun τ => (g τ).map φ, fun τ i j hij => by simp [hg2 τ i j hij], fun τ i => by simp [hg1], hc⟩`.
-/
theorem frBor_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} (h : FrBor t y y')
    (hz : FrMap φ y z) (hz' : FrMap φ y' z') : FrBor (fun i => Units.map (φ : S →* T) (t i)) z z' := by
  obtain ⟨g, hg2, hg1, hg⟩ := (GlobalTheory.Frames.frBor_iff_frChg y y' t).1 h
  have hc := (frMap_iff_frChg hg hz).1 hz'
  exact (GlobalTheory.Frames.frBor_iff_frChg z z' _).2
    ⟨fun τ => (g τ).map φ, fun τ i j hij => by simp [hg2 τ i j hij], fun τ i => by simp [hg1], hc⟩

section Theta

variable {T : CDVR} {io : c.F →+* T.Fr} {p : ℕ}

/- English proof (translation)
Use `letI := io.toAlgebra`. Introduce `z t h hb`. Take `⟨u, tan, eig, basis, s, gen, rfl, hs⟩` from `frBor_reduce hb`. Take `⟨-, -, f, f', hP, -, hT⟩` from `h`. Take `⟨I⟩` from `(GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y.1).1 y.2.2`.

Take `⟨I'⟩` from `(GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y'.1).1 y'.2.2`. Take `⟨F, F', a₁, a₂, a₃, -, -, a₄, -⟩` from `GlobalTheory.T.exists_ext_pair_alt E H Dw l Xo T _ _ I.G I'.G I.t' I'.t' I.m1 I.m2 I'.m1 I'.m2 f f' hP.1 hP.2.1`. Take `⟨w, w₁, w₂⟩` from `GlobalTheory.T.exists_pull_isTranslSum_of_isThetaTrace E H Dw l Xo T.Fr _ _ f f' p y.1.s y'.1.s s _ hP hs hT`. Conclude with `GlobalTheory.T.integral_scalar_of_pulledBack_generator_extends_model E H Dw l Xo c T io y y' I I' f F F' (p ^ 2) p _ w a₁ a₂ a₃ (a₄ _ hP.2.2.2.1) (by rw [Nat.cast_pow]; exact hp.pow 2) w₁ (GlobalTheory.T.sum_symmetricTranslates_thetaPullback_extends E H Dw l Xo c T io y I p w (hU …`.
-/
theorem theta_low (hp : IsUnit (p : T.V)) (y y' : IntFr Xo c T io)
    (hU : ∀ I : IntData Xo c T io y.1, ∃ P : PELUnif (IsLocalRing.maximalIdeal T.V) I.G, P.TorsionIso) :
    letI := io.toAlgebra
    ∀ (z : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), HkOver p y.1 z → FrBor t y'.1 z →
      (t none : T.Fr) ∈ Set.range (algebraMap T.V T.Fr) := by
  letI := io.toAlgebra
  intro z t h hb
  obtain ⟨u, tan, eig, basis, s, gen, rfl, hs⟩ := frBor_reduce hb
  obtain ⟨-, -, f, f', hP, -, hT⟩ := h
  obtain ⟨I⟩ := (GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y.1).1 y.2.2
  obtain ⟨I'⟩ := (GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y'.1).1 y'.2.2
  obtain ⟨F, F', a₁, a₂, a₃, -, -, a₄, -⟩ :=
    GlobalTheory.T.exists_ext_pair_alt E H Dw l Xo T _ _ I.G I'.G I.t' I'.t' I.m1 I.m2 I'.m1 I'.m2 f f' hP.1 hP.2.1
  obtain ⟨w, w₁, w₂⟩ := GlobalTheory.T.exists_pull_isTranslSum_of_isThetaTrace E H Dw l Xo T.Fr _ _ f f' p y.1.s y'.1.s s _ hP hs hT
  exact GlobalTheory.T.integral_scalar_of_pulledBack_generator_extends_model E H Dw l Xo c T io y y' I I' f F F' (p ^ 2) p _ w a₁ a₂ a₃ (a₄ _ hP.2.2.2.1)
    (by rw [Nat.cast_pow]; exact hp.pow 2) w₁ (GlobalTheory.T.sum_symmetricTranslates_thetaPullback_extends E H Dw l Xo c T io y I p w (hU I) hp w₂)

/- English proof (translation)
Use `letI := io.toAlgebra`. Introduce `z t h hb`. Take `⟨u, tan, eig, basis, s, gen, rfl, hs⟩` from `frBor_reduce hb`. Take `⟨-, hR, f, f', hP, -, hT⟩` from `h`. Take `⟨I⟩` from `(GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y.1).1 y.2.2`.

Take `⟨I'⟩` from `(GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y'.1).1 y'.2.2`. Take `⟨b, ζ, m, hζ, hab, f₂, hf₂, hff, w, w₁, w₂⟩` from `GlobalTheory.T.exists_orth_pull_isTranslSum_of_isThetaTrace E H Dw l Xo T.Fr _ _ f f' p y.1.s y'.1.s s _ hpp hP hR (t none).ne_zero hs hT`. Take `⟨F, F', a₁, a₂, -, a₃, a₄, -⟩` from `GlobalTheory.T.exists_ext_pair_alt E H Dw l Xo T _ _ I.G I'.G I.t' I'.t' I.m1 I.m2 I'.m1 I'.m2 f f₂ hP.1 hf₂`. Take `⟨b₀, rfl⟩` from `GlobalTheory.T.integral_scalar_of_pulledBack_generator_extends_model E H Dw l Xo c T io y' y I' I f₂ F' F (p ^ 3) (p ^ 2) b w a₂ a₁ a₃ (a₄ _ hff) (by rw [Nat.cast_pow]; exact hp.pow 3) w₁ (GlobalTheory.T.sum_symmetricTranslates_thetaPullback_extends E H Dw l Xo c T io y' I' (p ^ …`. Establish `hζ0 : ζ ≠ 0` using `fun h => by simp [h, hpp.ne_zero] at hζ`.

Establish `hp0 : (p : T.Fr) ≠ 0` using `by simpa using (hp.map (algebraMap T.V T.Fr)).ne_zero`. Establish `vp : vV T.V (p : T.Fr) = 0`. Simplify using `using GlobalTheory.IntegralFrameCheck.vV_map_unit (V := T.V) (V' := T.V) (RingHom.id T.Fr) (fun a => ⟨a, rfl⟩) hp.unit`. Establish `vζ : vV T.V ζ = 0`. Use `GlobalTheory.IntegralFrameCheck.vV_pow (V := T.V) hζ0 p` as an intermediate fact.

Rewrite `this` using `[hζ, GlobalTheory.IntegralFrameCheck.vV_one]`. Conclude with `(mul_eq_zero.1 this.symm).resolve_left (by exact_mod_cast hpp.ne_zero)`. Establish `hb0 : algebraMap T.V T.Fr b₀ ≠ 0` using `fun h => by`. Rewrite `hab` using `[h, mul_zero]`. Conclude with `mul_ne_zero (pow_ne_zero _ hp0) hζ0 hab.symm`.

Establish `e` using `congrArg (vV T.V) hab`. Rewrite `e` using `[vV_mul (t none).ne_zero hb0, vV_mul (pow_ne_zero _ hp0) hζ0, GlobalTheory.IntegralFrameCheck.vV_pow hp0, vp, vζ]`. Use `GlobalTheory.IntegralFrameCheck.vV_algebraMap_nonneg (K' := T.Fr) b₀` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem theta_high (hpp : p.Prime) (hp : IsUnit (p : T.V)) (y y' : IntFr Xo c T io)
    (hU : ∀ I : IntData Xo c T io y'.1, ∃ P : PELUnif (IsLocalRing.maximalIdeal T.V) I.G, P.TorsionIso) :
    letI := io.toAlgebra
    ∀ (z : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), HkOver p y.1 z → FrBor t y'.1 z →
      vV T.V (t none : T.Fr) ≤ 0 := by
  letI := io.toAlgebra
  intro z t h hb
  obtain ⟨u, tan, eig, basis, s, gen, rfl, hs⟩ := frBor_reduce hb
  obtain ⟨-, hR, f, f', hP, -, hT⟩ := h
  obtain ⟨I⟩ := (GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y.1).1 y.2.2
  obtain ⟨I'⟩ := (GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y'.1).1 y'.2.2
  obtain ⟨b, ζ, m, hζ, hab, f₂, hf₂, hff, w, w₁, w₂⟩ :=
    GlobalTheory.T.exists_orth_pull_isTranslSum_of_isThetaTrace E H Dw l Xo T.Fr _ _ f f' p y.1.s y'.1.s s _ hpp hP hR (t none).ne_zero hs hT
  obtain ⟨F, F', a₁, a₂, -, a₃, a₄, -⟩ :=
    GlobalTheory.T.exists_ext_pair_alt E H Dw l Xo T _ _ I.G I'.G I.t' I'.t' I.m1 I.m2 I'.m1 I'.m2 f f₂ hP.1 hf₂
  obtain ⟨b₀, rfl⟩ := GlobalTheory.T.integral_scalar_of_pulledBack_generator_extends_model E H Dw l Xo c T io y' y I' I f₂ F' F (p ^ 3) (p ^ 2) b w a₂ a₁ a₃ (a₄ _ hff)
    (by rw [Nat.cast_pow]; exact hp.pow 3) w₁
    (GlobalTheory.T.sum_symmetricTranslates_thetaPullback_extends E H Dw l Xo c T io y' I' (p ^ 2) w (hU I') (by rw [Nat.cast_pow]; exact hp.pow 2) w₂)
  have hζ0 : ζ ≠ 0 := fun h => by simp [h, hpp.ne_zero] at hζ
  have hp0 : (p : T.Fr) ≠ 0 := by simpa using (hp.map (algebraMap T.V T.Fr)).ne_zero
  have vp : vV T.V (p : T.Fr) = 0 := by
    simpa using GlobalTheory.IntegralFrameCheck.vV_map_unit (V := T.V) (V' := T.V) (RingHom.id T.Fr) (fun a => ⟨a, rfl⟩) hp.unit
  have vζ : vV T.V ζ = 0 := by
    have := GlobalTheory.IntegralFrameCheck.vV_pow (V := T.V) hζ0 p
    rw [hζ, GlobalTheory.IntegralFrameCheck.vV_one] at this
    exact (mul_eq_zero.1 this.symm).resolve_left (by exact_mod_cast hpp.ne_zero)
  have hb0 : algebraMap T.V T.Fr b₀ ≠ 0 := fun h => by
    rw [h, mul_zero] at hab
    exact mul_ne_zero (pow_ne_zero _ hp0) hζ0 hab.symm
  have e := congrArg (vV T.V) hab
  rw [vV_mul (t none).ne_zero hb0, vV_mul (pow_ne_zero _ hp0) hζ0, GlobalTheory.IntegralFrameCheck.vV_pow hp0, vp, vζ] at e
  have := GlobalTheory.IntegralFrameCheck.vV_algebraMap_nonneg (K' := T.Fr) b₀
  omega

/- English proof (translation)
Establish `hu : (algebraMap T.V T.Fr (hp.unit⁻¹ : T.Vˣ)) ≠ 0` using `((hp.unit⁻¹).isUnit.map _).ne_zero`. Take `⟨b, hb⟩` from `Formalism.L2.PjFree.mem_range_of_vV_nonneg (V := T'.V) (x := i (algebraMap T.V T.Fr (hp.unit⁻¹ : T.Vˣ))) (by rw [hi _ hu]; exact mul_nonneg (Int.natCast_nonneg _) (GlobalTheory.IntegralFrameCheck.vV_algebraMap_nonneg _))`. Use `IsUnit.of_mul_eq_one b (IsFractionRing.injective T'.V T'.Fr ?_)` and prove the remaining obligations. Rewrite using `[map_mul, hb, map_natCast, ← map_natCast (i.comp (algebraMap T.V T.Fr)), RingHom.comp_apply, ← map_mul, ← map_mul, hp.mul_val_inv, map_one, map_one, map_one]`.
-/
theorem isUnit_natCast_up {T' : CDVR} (hp : IsUnit (p : T.V)) (i : T.Fr →+* T'.Fr) {r : ℕ}
    (hi : ∀ a : T.Fr, a ≠ 0 → vV T'.V (i a) = (r : ℤ) * vV T.V a) : IsUnit (p : T'.V) := by
  have hu : (algebraMap T.V T.Fr (hp.unit⁻¹ : T.Vˣ)) ≠ 0 := ((hp.unit⁻¹).isUnit.map _).ne_zero
  obtain ⟨b, hb⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg (V := T'.V) (x := i (algebraMap T.V T.Fr (hp.unit⁻¹ : T.Vˣ)))
    (by rw [hi _ hu]; exact mul_nonneg (Int.natCast_nonneg _) (GlobalTheory.IntegralFrameCheck.vV_algebraMap_nonneg _))
  refine IsUnit.of_mul_eq_one b (IsFractionRing.injective T'.V T'.Fr ?_)
  rw [map_mul, hb, map_natCast, ← map_natCast (i.comp (algebraMap T.V T.Fr)), RingHom.comp_apply, ← map_mul,
    ← map_mul, hp.mul_val_inv, map_one, map_one, map_one]

/- English proof (translation)
Use `letI := io.toAlgebra`. Establish `key : ∀ (i : T.Fr →+* T'.Fr), io' = i.comp io → letI` using `io'.toAlgebra ∀ (φ : T.Fr →ₐ[c.F] T'.Fr), φ.toRingHom = i → (∀ a : T.Fr, a ≠ 0 → vV T'.V (i a) = (e : ℤ) * vV T.V a) → ∀ w : IntFr Xo c T io, ∃ w' : IntFr Xo c T' io', FrMap φ w.1 w'.1 := by`. Introduce and unpack `i rfl φ hφ hv w`. Take `⟨w', ψ, hψ, hm⟩` from `GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c T T' io w i e he hv`. Use `letI := (i.comp io).toAlgebra`.

Take `rfl : ψ = φ` from `AlgHom.coe_ringHom_injective (hψ.trans hφ.symm)`. Conclude with `⟨w', hm⟩`. Use `letI := io'.toAlgebra`. Conclude with `fun φ hφ => key φ.toRingHom (RingHom.ext fun a => (φ.commutes a).symm) φ rfl hφ`.
-/
theorem exists_intFr_up {T' : CDVR} {io' : c.F →+* T'.Fr} {e : ℕ} (he : 0 < e) :
    letI := io.toAlgebra; letI := io'.toAlgebra
    ∀ (φ : T.Fr →ₐ[c.F] T'.Fr), (∀ a : T.Fr, a ≠ 0 → vV T'.V (φ a) = (e : ℤ) * vV T.V a) →
      ∀ w : IntFr Xo c T io, ∃ w' : IntFr Xo c T' io', FrMap φ w.1 w'.1 := by
  letI := io.toAlgebra
  have key : ∀ (i : T.Fr →+* T'.Fr), io' = i.comp io → letI := io'.toAlgebra
      ∀ (φ : T.Fr →ₐ[c.F] T'.Fr), φ.toRingHom = i → (∀ a : T.Fr, a ≠ 0 → vV T'.V (i a) = (e : ℤ) * vV T.V a) →
      ∀ w : IntFr Xo c T io, ∃ w' : IntFr Xo c T' io', FrMap φ w.1 w'.1 := by
    rintro i rfl φ hφ hv w
    obtain ⟨w', ψ, hψ, hm⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c T T' io w i e he hv
    letI := (i.comp io).toAlgebra
    obtain rfl : ψ = φ := AlgHom.coe_ringHom_injective (hψ.trans hφ.symm)
    exact ⟨w', hm⟩
  letI := io'.toAlgebra
  exact fun φ hφ => key φ.toRingHom (RingHom.ext fun a => (φ.commutes a).symm) φ rfl hφ

/- English proof (translation)
Use `letI := io.toAlgebra`. Introduce `z t h hb`. Apply `le_antisymm` to reduce the goal to its premises. Take `⟨T', io', y₁', e, -, he, hU, φ, hφ, hm'⟩` from `GlobalTheory.IntegralPull.exists_ext_all_models_uniformised E H Dw l Xo c T io y' hT`. Use `letI := io'.toAlgebra`.

Take `⟨y₁, hm⟩` from `exists_intFr_up he φ hφ y`. Take `⟨z₁, hz⟩` from `exists_frMap φ z`. Use `theta_high hpp (isUnit_natCast_up hp φ.toRingHom hφ) y₁ y₁' hU z₁ _ (h.up φ hpp.pos hm hz) (frBor_map φ hb hm' hz)` as an intermediate fact. Establish `e₁ : vV T'.V (φ (t none)) ≤ 0` using `this`. Rewrite `e₁` using `[hφ _ (t none).ne_zero]`.

Conclude with `nonpos_of_mul_nonpos_right e₁ (by exact_mod_cast he)`. Take `⟨T', io', y₁, e, -, he, hU, φ, hφ, hm⟩` from `GlobalTheory.IntegralPull.exists_ext_all_models_uniformised E H Dw l Xo c T io y hT`. Use `letI := io'.toAlgebra`. Take `⟨y₁', hm'⟩` from `exists_intFr_up he φ hφ y'`. Take `⟨z₁, hz⟩` from `exists_frMap φ z`.

Take `⟨b, hb'⟩` from `theta_low (isUnit_natCast_up hp φ.toRingHom hφ) y₁ y₁' hU z₁ _ (h.up φ hpp.pos hm hz) (frBor_map φ hb hm' hz)`. Establish `e₁ : 0 ≤ vV T'.V (φ (t none))`. Use `GlobalTheory.IntegralFrameCheck.vV_algebraMap_nonneg (K' := T'.Fr) b` as an intermediate fact. Rewrite `this` using `[hb']`. Then use the resulting hypothesis. Rewrite `e₁` using `[hφ _ (t none).ne_zero]`.

Conclude with `nonneg_of_mul_nonneg_right e₁ (by exact_mod_cast he)`.
-/
theorem theta_unit (hpp : p.Prime) (hp : IsUnit (p : T.V)) (hT : T.FinRes) (y y' : IntFr Xo c T io) :
    letI := io.toAlgebra
    ∀ (z : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), HkOver p y.1 z → FrBor t y'.1 z →
      vV T.V (t none : T.Fr) = 0 := by
  letI := io.toAlgebra
  intro z t h hb
  apply le_antisymm
  · obtain ⟨T', io', y₁', e, -, he, hU, φ, hφ, hm'⟩ :=
      GlobalTheory.IntegralPull.exists_ext_all_models_uniformised E H Dw l Xo c T io y' hT
    letI := io'.toAlgebra
    obtain ⟨y₁, hm⟩ := exists_intFr_up he φ hφ y
    obtain ⟨z₁, hz⟩ := exists_frMap φ z
    have := theta_high hpp (isUnit_natCast_up hp φ.toRingHom hφ) y₁ y₁' hU z₁ _ (h.up φ hpp.pos hm hz)
      (frBor_map φ hb hm' hz)
    have e₁ : vV T'.V (φ (t none)) ≤ 0 := this
    rw [hφ _ (t none).ne_zero] at e₁
    exact nonpos_of_mul_nonpos_right e₁ (by exact_mod_cast he)
  · obtain ⟨T', io', y₁, e, -, he, hU, φ, hφ, hm⟩ :=
      GlobalTheory.IntegralPull.exists_ext_all_models_uniformised E H Dw l Xo c T io y hT
    letI := io'.toAlgebra
    obtain ⟨y₁', hm'⟩ := exists_intFr_up he φ hφ y'
    obtain ⟨z₁, hz⟩ := exists_frMap φ z
    obtain ⟨b, hb'⟩ := theta_low (isUnit_natCast_up hp φ.toRingHom hφ) y₁ y₁' hU z₁ _ (h.up φ hpp.pos hm hz)
      (frBor_map φ hb hm' hz)
    have e₁ : 0 ≤ vV T'.V (φ (t none)) := by
      have := GlobalTheory.IntegralFrameCheck.vV_algebraMap_nonneg (K' := T'.Fr) b
      rwa [hb'] at this
    rw [hφ _ (t none).ne_zero] at e₁
    exact nonneg_of_mul_nonneg_right e₁ (by exact_mod_cast he)

end Theta

section Frame

variable {T : CDVR} {io : c.F →+* T.Fr} {p : ℕ}

/- English proof (translation)
Take `⟨b, hb⟩` from `Formalism.L2.PjFree.mem_range_of_vV_nonneg h.ge`. Establish `h'` using `vV_mul (V := T.V) a.ne_zero a⁻¹.ne_zero`. Rewrite `h'` using `[Units.mul_inv, GlobalTheory.IntegralFrameCheck.vV_one, h, zero_add]`. Take `⟨b', hb'⟩` from `Formalism.L2.PjFree.mem_range_of_vV_nonneg h'.le`. Establish `e : b * b' = 1` using `IsFractionRing.injective T.V T.Fr (by rw [map_mul, hb, hb', Units.mul_inv, map_one])`.

Conclude with `⟨Units.mkOfMulEqOne b b' e, hb⟩`.
-/
theorem exists_unit_of_vV {a : T.Frˣ} (h : vV T.V (a : T.Fr) = 0) : ∃ u : T.Vˣ, algebraMap T.V T.Fr u = a := by
  obtain ⟨b, hb⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg h.ge
  have h' := vV_mul (V := T.V) a.ne_zero a⁻¹.ne_zero
  rw [Units.mul_inv, GlobalTheory.IntegralFrameCheck.vV_one, h, zero_add] at h'
  obtain ⟨b', hb'⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg h'.le
  have e : b * b' = 1 := IsFractionRing.injective T.V T.Fr (by rw [map_mul, hb, hb', Units.mul_inv, map_one])
  exact ⟨Units.mkOfMulEqOne b b' e, hb⟩

/- English proof (translation)
Use `letI := io.toAlgebra`. Introduce `z hx h`. Take `⟨x, xo, u, tan, eig, basis, s, gen⟩` from `z`. Simplify using `only at hx`. Substitute `hx` using the available equality.

Establish `⟨_, _, f, f', hP, hL, _⟩` using `h`. Take `⟨I⟩` from `(GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y.1).1 y.2.2`. Take `⟨I'⟩` from `(GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y₀.1).1 y₀.2.2`. Take `⟨F, F', a₁, a₂, a₃, -, a₄, a₅, a₆, a₇⟩` from `GlobalTheory.T.exists_ext_pair_alt E H Dw l Xo T _ _ I.G I'.G I.t' I'.t' I.m1 I.m2 I'.m1 I'.m2 f f' hP.1 hP.2.1`. Take `⟨k, hk, hc⟩` from `GlobalTheory.T.lieLattice_onto_of_monHom_pair_pow_p_sq E H Dw l Xo c T io y y₀ I I' f F F' p u hp a₁ a₂ a₃ (a₄ _ hP.2.2.1) (a₅ _ hP.2.2.2.1) (a₆ hP.2.2.2.2.1) (a₇ hP.2.2.2.2.2) hL`.

Take `⟨y', -, hx, hu, -⟩` from `GlobalTheory.IntRebase.intRebase GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c T io y₀ ⟨_, xo, u, tan, eig, basis, s, gen⟩ rfl k hk`. Establish `hu' : ∀ τ i, u τ i = y'.1.u τ i` using `fun τ i => Formalism.L2.PjFree.isCombAt_unique (hc τ i) (hu τ i)`. Establish `hs : ∀ τ i, IsCombAt y'.1.x (y'.1.u τ) (Pi.single i 1) (u τ i)` using `fun τ i => hu' τ i ▸ Formalism.L2.PjFree.isCombAt_single (y'.1.tan τ) i`. Take `⟨t, ht⟩` from `(GlobalTheory.Frames.frBor_calculus E H Dw l Xo c T.Fr y'.1 ⟨_, xo, u, tan, eig, basis, s, gen⟩ y'.1).2.1 hx.symm fun τ i => ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne hj.ne' _, hs τ i⟩`. Take `⟨u₀, hu₀⟩` from `exists_unit_of_vV (theta_unit hpp hp hT y y' _ t h ht)`.

Use `⟨y', fun a => Option.elim a u₀ fun _ => 1, ?_, ht.1, fun τ i => ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne hj.ne' _, hs τ i⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨G, t₁, m₁, m₂, hG⟩`. Take `⟨F₁, -, -, -, b₁, -⟩` from `GlobalTheory.T.exists_ext_pair_alt E H Dw l Xo T _ _ G I'.G t₁ I'.t' m₁ m₂ I'.m1 I'.m2 f f' hP.1 hP.2.1`. Conclude with `⟨I'.G, I'.t', hx ▸ I'.m1, I'.m2, GlobalTheory.T.isProper_model_of_extends_fibreIsogeny E H Dw l Xo T _ _ G I'.G t₁ I'.t' m₁ m₂ I'.m1 I'.m2 f f' F₁ _ b₁ hP.2.2.2.1 (pow_pos hpp.pos 2) hG⟩`. Use `ht.2.2` as an intermediate fact.

Rewrite `this` using `[← hu₀]`. Conclude with `this`.
-/
theorem exists_frBor_unit (hpp : p.Prime) (hp : IsUnit (p : T.V)) (hT : T.FinRes) (y y₀ : IntFr Xo c T io) :
    letI := io.toAlgebra
    ∀ z : FrPt Xo c T.Fr, z.x = y₀.1.x → HkOver p y.1 z →
      ∃ (y' : IntFr Xo c T io) (u : Ix Dw → T.Vˣ), (GlobalTheory.GoodPts.Good y → GlobalTheory.GoodPts.Good y') ∧
        FrBor (fun a => Units.map (algebraMap T.V T.Fr).toMonoidHom (u a)) y'.1 z := by
  letI := io.toAlgebra
  intro z hx h
  obtain ⟨x, xo, u, tan, eig, basis, s, gen⟩ := z
  dsimp only at hx
  subst hx
  have ⟨_, _, f, f', hP, hL, _⟩ := h
  obtain ⟨I⟩ := (GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y.1).1 y.2.2
  obtain ⟨I'⟩ := (GlobalTheory.IntegralData.integralIff E H Dw l Xo c T io y₀.1).1 y₀.2.2
  obtain ⟨F, F', a₁, a₂, a₃, -, a₄, a₅, a₆, a₇⟩ :=
    GlobalTheory.T.exists_ext_pair_alt E H Dw l Xo T _ _ I.G I'.G I.t' I'.t' I.m1 I.m2 I'.m1 I'.m2 f f' hP.1 hP.2.1
  obtain ⟨k, hk, hc⟩ := GlobalTheory.T.lieLattice_onto_of_monHom_pair_pow_p_sq E H Dw l Xo c T io y y₀ I I' f F F' p u hp a₁ a₂ a₃ (a₄ _ hP.2.2.1) (a₅ _ hP.2.2.2.1)
    (a₆ hP.2.2.2.2.1) (a₇ hP.2.2.2.2.2) hL
  obtain ⟨y', -, hx, hu, -⟩ := GlobalTheory.IntRebase.intRebase GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c T io y₀
    ⟨_, xo, u, tan, eig, basis, s, gen⟩ rfl k hk
  have hu' : ∀ τ i, u τ i = y'.1.u τ i := fun τ i => Formalism.L2.PjFree.isCombAt_unique (hc τ i) (hu τ i)
  have hs : ∀ τ i, IsCombAt y'.1.x (y'.1.u τ) (Pi.single i 1) (u τ i) := fun τ i =>
    hu' τ i ▸ Formalism.L2.PjFree.isCombAt_single (y'.1.tan τ) i
  obtain ⟨t, ht⟩ := (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c T.Fr y'.1 ⟨_, xo, u, tan, eig, basis, s, gen⟩ y'.1).2.1
    hx.symm fun τ i => ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne hj.ne' _,
      hs τ i⟩
  obtain ⟨u₀, hu₀⟩ := exists_unit_of_vV (theta_unit hpp hp hT y y' _ t h ht)
  refine ⟨y', fun a => Option.elim a u₀ fun _ => 1, ?_, ht.1, fun τ i => ⟨Pi.single i 1, by simp,
    fun j hj => Pi.single_eq_of_ne hj.ne' _, hs τ i⟩, ?_⟩
  · rintro ⟨G, t₁, m₁, m₂, hG⟩
    obtain ⟨F₁, -, -, -, b₁, -⟩ := GlobalTheory.T.exists_ext_pair_alt E H Dw l Xo T _ _ G I'.G t₁ I'.t' m₁ m₂ I'.m1 I'.m2 f f' hP.1 hP.2.1
    exact ⟨I'.G, I'.t', hx ▸ I'.m1, I'.m2, GlobalTheory.T.isProper_model_of_extends_fibreIsogeny E H Dw l Xo T _ _ G I'.G t₁ I'.t' m₁ m₂ I'.m1 I'.m2 f f' F₁ _ b₁
      hP.2.2.2.1 (pow_pos hpp.pos 2) hG⟩
  · have := ht.2.2
    rw [← hu₀] at this
    exact this

end Frame

/- English proof (translation)
The claim follows from `(Nat.eq_zero_or_pos (Dw.p + Dw.q)).elim (GlobalTheory.T.integralFrameExtension_of_rank_zero_signature E H Dw l Xo c) (GlobalTheory.T.moduliPoint_integralFrame_after_finiteExtension E H Dw l Xo c)`.
-/
theorem intFrExt (Xo : Moduli Dw l) (c : Coeff l) : IntFrExt Xo c :=
  (Nat.eq_zero_or_pos (Dw.p + Dw.q)).elim (GlobalTheory.T.integralFrameExtension_of_rank_zero_signature E H Dw l Xo c) (GlobalTheory.T.moduliPoint_integralFrame_after_finiteExtension E H Dw l Xo c)

/- English proof (translation)
Introduce `la P p n hP hla T io e ho y hy hc Ω _ _ _`. Use `letI := io.toAlgebra`. Introduce `k hk w hw C z hz`. Establish `hpp : p.Prime` using `hP.2.2.1`. Establish `hk' : k.toRingHom.IsIntegral`.

Use `letI := k.toRingHom.toAlgebra`. Use `haveI := hk`. Conclude with `fun a => Algebra.IsIntegral.isIntegral (R := T.Fr) a`. Take `⟨L, _, _, i₁, j₁, y₁, z₁, e₁, f₁, hy₁, hz₁, h₁⟩` from `exists_hkOver k hk' hpp.pos hw (GlobalTheory.T.exists_linear_heckeIsogeny_inverse_up_to_p_sq E H Dw l Xo c P p n hP Ω w C z hz)`. Choose the witnesses or unpack the hypotheses as in `⟨T₁, iT, r₁, ψ, hr₁, hv₁, hψ, hT₁⟩ : ∃ (T₁ : CDVR) (iT : T.Fr →+* T₁.Fr) (r : ℕ) (ψ : L ≃+* T₁.Fr), 0 < r ∧ (∀ a : T.Fr, vV T₁.V (iT a) = (r : ℤ) * vV T.V a) ∧ (∀ a, ψ (i₁ a) = iT a) ∧ T₁.FinRes := by`.

Use `letI := i₁.toRingHom.toAlgebra`. Use `haveI : FiniteDimensional T.Fr L := f₁`. Take `⟨T₁, iT, r, ψ, -, a, b, d, -, g⟩` from `GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T L`. Conclude with `⟨T₁, iT, r, ψ, a, b, d, g hy⟩`. Take `⟨T₂, i₂, r₂, hr₂, hv₂, hT₂, y₀, hx₀⟩` from `intFrExt Xo c T₁ (iT.comp io) hT₁ (spMap ψ.toRingHom ≫ z₁.x) (by`.

Rewrite using `[Category.assoc, z₁.x_over, sOf, sOf, TorsionRat.sp_comp]`. Use `congr 1`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Conclude with `(congrArg ψ (i₁.commutes _).symm).trans (hψ _))`. Set `i : T.Fr →+* T₂.Fr` to `i₂.comp iT`.

Establish `hv : ∀ a, vV T₂.V (i a) = ((r₂ * r₁ : ℕ) : ℤ) * vV T.V a` using `fun a => by`. Rewrite using `[RingHom.comp_apply, hv₂, hv₁, Nat.cast_mul, _root_.mul_assoc]`. Establish `hr : 0 < r₂ * r₁` using `Nat.mul_pos hr₂ hr₁`. Take `⟨j, hj⟩` from `exists_lift (j₁.toRingHom.comp ψ.symm.toRingHom) i₂ (GlobalTheory.T.ringHom_finite_and_isIntegral_of_valuation_scaled T₁ T₂ i₂ r₂ hr₂ hv₂ hT₂).1`. Establish `hj' : ∀ a : L, j (i₂ (ψ a)) = j₁ a` using `fun a => by simpa using DFunLike.congr_fun hj (ψ a)`.

Use `letI := (i.comp io).toAlgebra`. Set `b : L →ₐ[c.F] T₂.Fr` to `⟨i₂.comp ψ.toRingHom, fun a => congrArg i₂ ((congrArg ψ (i₁.commutes a).symm).trans (hψ _))⟩`. Set `φ : T.Fr →ₐ[c.F] T₂.Fr` to `⟨i, fun _ => rfl⟩`. Establish `hφ : ∀ a, b (i₁ a) = φ a` using `fun a => congrArg i₂ (hψ a)`. Establish `hjk : ∀ a, j (i a) = k a` using `fun a => (congrArg j (hφ a).symm).trans ((hj' _).trans (DFunLike.congr_fun e₁ a))`.

Set `J : T₂.Fr →ₐ[c.F] Ω` to `⟨j, fun a => (hjk _).trans (k.commutes a)⟩`. Take `⟨y₂, hy₂⟩` from `exists_intFr_up (io' := i.comp io) hr φ (fun a _ => hv a) y`. Take `⟨z₂, hz₂⟩` from `exists_frMap b z₁`. Take `⟨y', u, hg, hb⟩` from `exists_frBor_unit (io := i.comp io) hpp (isUnit_natCast_up (PullbackSections.isUnit_natCast_of_overLa T ho hla) i fun a _ => hv a) hT₂ y₂ y₀ z₂ (hz₂.1.trans (hx₀.trans (by rw [← Category.assoc, TorsionRat.sp_comp])).symm) (h₁.up b hpp.pos (frMap_of_comp hy₁ hy₂ hφ) hz₂)`. Take `⟨w', hw'⟩` from `exists_frMap J y'.1`.

Use `⟨T₂, i, ⟨(GlobalTheory.T.ringHom_finite_and_isIntegral_of_valuation_scaled T T₂ i _ hr hv hT₂).1, _, hr, hv⟩, J, RingHom.ext hjk, y', hT₂, hcls T io y T₂ _ y' hc fun h => hg (GlobalTheory.T.goodReduction_stable_valuationRing_extension E H Dw l Xo c T T₂ io _ y y₂ i _ hr hv hy₂.1 …` and prove the remaining obligations. Conclude with `frBor_map J hb hw' (frMap_of_comp hz₂ hz₁ hj')`.
-/
theorem heckeFrameInt (cls : PtClass Xo c)
    (hcls : ∀ T io y T' io' y', cls T io y → (GlobalTheory.GoodPts.Good y → GlobalTheory.GoodPts.Good y') → cls T' io' y') :
    HeckeFrameInt Xo c cls := by
  intro la P p n hP hla T io e ho y hy hc Ω _ _ _
  letI := io.toAlgebra
  intro k hk w hw C z hz
  have hpp : p.Prime := hP.2.2.1
  have hk' : k.toRingHom.IsIntegral := by
    letI := k.toRingHom.toAlgebra
    haveI := hk
    exact fun a => Algebra.IsIntegral.isIntegral (R := T.Fr) a
  obtain ⟨L, _, _, i₁, j₁, y₁, z₁, e₁, f₁, hy₁, hz₁, h₁⟩ :=
    exists_hkOver k hk' hpp.pos hw (GlobalTheory.T.exists_linear_heckeIsogeny_inverse_up_to_p_sq E H Dw l Xo c P p n hP Ω w C z hz)
  obtain ⟨T₁, iT, r₁, ψ, hr₁, hv₁, hψ, hT₁⟩ : ∃ (T₁ : CDVR) (iT : T.Fr →+* T₁.Fr) (r : ℕ) (ψ : L ≃+* T₁.Fr), 0 < r ∧
      (∀ a : T.Fr, vV T₁.V (iT a) = (r : ℤ) * vV T.V a) ∧ (∀ a, ψ (i₁ a) = iT a) ∧ T₁.FinRes := by
    letI := i₁.toRingHom.toAlgebra
    haveI : FiniteDimensional T.Fr L := f₁
    obtain ⟨T₁, iT, r, ψ, -, a, b, d, -, g⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T L
    exact ⟨T₁, iT, r, ψ, a, b, d, g hy⟩
  obtain ⟨T₂, i₂, r₂, hr₂, hv₂, hT₂, y₀, hx₀⟩ := intFrExt Xo c T₁ (iT.comp io) hT₁ (spMap ψ.toRingHom ≫ z₁.x) (by
    rw [Category.assoc, z₁.x_over, sOf, sOf, TorsionRat.sp_comp]
    congr 1
    refine RingHom.ext fun a => ?_
    exact (congrArg ψ (i₁.commutes _).symm).trans (hψ _))
  let i : T.Fr →+* T₂.Fr := i₂.comp iT
  have hv : ∀ a, vV T₂.V (i a) = ((r₂ * r₁ : ℕ) : ℤ) * vV T.V a := fun a => by
    rw [RingHom.comp_apply, hv₂, hv₁, Nat.cast_mul, _root_.mul_assoc]
  have hr : 0 < r₂ * r₁ := Nat.mul_pos hr₂ hr₁
  obtain ⟨j, hj⟩ := exists_lift (j₁.toRingHom.comp ψ.symm.toRingHom) i₂ (GlobalTheory.T.ringHom_finite_and_isIntegral_of_valuation_scaled T₁ T₂ i₂ r₂ hr₂ hv₂ hT₂).1
  have hj' : ∀ a : L, j (i₂ (ψ a)) = j₁ a := fun a => by simpa using DFunLike.congr_fun hj (ψ a)
  letI := (i.comp io).toAlgebra
  let b : L →ₐ[c.F] T₂.Fr := ⟨i₂.comp ψ.toRingHom, fun a =>
    congrArg i₂ ((congrArg ψ (i₁.commutes a).symm).trans (hψ _))⟩
  let φ : T.Fr →ₐ[c.F] T₂.Fr := ⟨i, fun _ => rfl⟩
  have hφ : ∀ a, b (i₁ a) = φ a := fun a => congrArg i₂ (hψ a)
  have hjk : ∀ a, j (i a) = k a := fun a =>
    (congrArg j (hφ a).symm).trans ((hj' _).trans (DFunLike.congr_fun e₁ a))
  let J : T₂.Fr →ₐ[c.F] Ω := ⟨j, fun a => (hjk _).trans (k.commutes a)⟩
  obtain ⟨y₂, hy₂⟩ := exists_intFr_up (io' := i.comp io) hr φ (fun a _ => hv a) y
  obtain ⟨z₂, hz₂⟩ := exists_frMap b z₁
  obtain ⟨y', u, hg, hb⟩ := exists_frBor_unit (io := i.comp io) hpp
    (isUnit_natCast_up (PullbackSections.isUnit_natCast_of_overLa T ho hla) i fun a _ => hv a) hT₂ y₂ y₀ z₂
    (hz₂.1.trans (hx₀.trans (by rw [← Category.assoc, TorsionRat.sp_comp])).symm)
    (h₁.up b hpp.pos (frMap_of_comp hy₁ hy₂ hφ) hz₂)
  obtain ⟨w', hw'⟩ := exists_frMap J y'.1
  refine ⟨T₂, i, ⟨(GlobalTheory.T.ringHom_finite_and_isIntegral_of_valuation_scaled T T₂ i _ hr hv hT₂).1, _, hr, hv⟩, J, RingHom.ext hjk, y', hT₂,
    hcls T io y T₂ _ y' hc fun h => hg (GlobalTheory.T.goodReduction_stable_valuationRing_extension E H Dw l Xo c T T₂ io _ y y₂ i _ hr hv hy₂.1 h), w', u, hw', ?_⟩
  exact frBor_map J hb hw' (frMap_of_comp hz₂ hz₁ hj')

/- English proof (translation)
Introduce `la P p n hP hla T io e ho y hy hc Ω _ _ _`. Use `letI := io.toAlgebra`. Introduce `k hk w hw C z hz`. Use `⟨fromTest_of_isLocalRing z, fun a m f hf hv => ?_⟩` and prove the remaining obligations. Take `⟨T', i, ⟨-, r, hr, hi⟩, j, hj, y', hy', -, w', u, hw', hb⟩` from `h la P p n hP hla T io e ho y hy hc Ω k hk w hw C z hz`.

Use `letI := (i.comp io).toAlgebra`. Establish `h0 : 0 ≤ nval T'.V (r * e) (evI y' f)` using `hv _ ⟨PtV.mk la (ho.bc i hr hi) y' hy' () trivial, rfl⟩`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb'⟩ : evI y' f ∈ Set.range (algebraMap T'.V T'.Fr) := by`. Distinguish the cases in `hx : evI y' f = 0`. Conclude with `⟨0, by rw [hx, map_zero]⟩`.

Use `Formalism.L2.PjFree.mem_range_of_vV_nonneg ?_` and prove the remaining obligations. Rewrite `h0` using `[nval_of_ne hx, EReal.coe_nonneg, le_div_iff₀ (by exact_mod_cast Nat.mul_pos hr ho.1), zero_mul]`. Conclude with `h0` after adjusting the coercions. Establish `e₁` using `(GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 Ω inferInstance a m f hf _ w' z hb`. Establish `e₂ : evR Xo c f w' = j (algebraMap T'.V T'.Fr b)` using `(evR_frMap hf.1 hw').trans (congrArg j hb'.symm)`.

Establish `e₃ : evR Xo c f z = j (algebraMap T'.V T'.Fr (wchar (ex Dw a m) u * b))`. Rewrite using `[e₁, e₂, map_mul, map_mul]`. Use `congr 1`. Simplify using `[wchar]`. Take `⟨q, hq, hq'⟩` from `(GlobalTheory.T.ringHom_finite_and_isIntegral_of_valuation_scaled T T' i r hr hi hy').2 (wchar (ex Dw a m) u * b)`.

Use `⟨q, hq, ?_⟩` and prove the remaining obligations. Rewrite using `[e₃, ← hj, RingHom.comp_assoc]`. Conclude with `(Polynomial.hom_eval₂ q _ j.toRingHom _).symm.trans ((congrArg j.toRingHom hq').trans (map_zero _))`.
-/
theorem heckeValueInt (cls : PtClass Xo c) (h : HeckeFrameInt Xo c cls) : HeckeValueInt Xo c cls := by
  intro la P p n hP hla T io e ho y hy hc Ω _ _ _
  letI := io.toAlgebra
  intro k hk w hw C z hz
  refine ⟨fromTest_of_isLocalRing z, fun a m f hf hv => ?_⟩
  obtain ⟨T', i, ⟨-, r, hr, hi⟩, j, hj, y', hy', -, w', u, hw', hb⟩ :=
    h la P p n hP hla T io e ho y hy hc Ω k hk w hw C z hz
  letI := (i.comp io).toAlgebra
  have h0 : 0 ≤ nval T'.V (r * e) (evI y' f) := hv _ ⟨PtV.mk la (ho.bc i hr hi) y' hy' () trivial, rfl⟩
  obtain ⟨b, hb'⟩ : evI y' f ∈ Set.range (algebraMap T'.V T'.Fr) := by
    by_cases hx : evI y' f = 0
    · exact ⟨0, by rw [hx, map_zero]⟩
    refine Formalism.L2.PjFree.mem_range_of_vV_nonneg ?_
    rw [nval_of_ne hx, EReal.coe_nonneg, le_div_iff₀ (by exact_mod_cast Nat.mul_pos hr ho.1), zero_mul] at h0
    exact_mod_cast h0
  have e₁ := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 Ω inferInstance
    a m f hf _ w' z hb
  have e₂ : evR Xo c f w' = j (algebraMap T'.V T'.Fr b) := (evR_frMap hf.1 hw').trans (congrArg j hb'.symm)
  have e₃ : evR Xo c f z = j (algebraMap T'.V T'.Fr (wchar (ex Dw a m) u * b)) := by
    rw [e₁, e₂, map_mul, map_mul]
    congr 1
    simp [wchar]
  obtain ⟨q, hq, hq'⟩ := (GlobalTheory.T.ringHom_finite_and_isIntegral_of_valuation_scaled T T' i r hr hi hy').2 (wchar (ex Dw a m) u * b)
  refine ⟨q, hq, ?_⟩
  rw [e₃, ← hj, RingHom.comp_assoc]
  exact (Polynomial.hom_eval₂ q _ j.toRingHom _).symm.trans ((congrArg j.toRingHom hq').trans (map_zero _))

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ Xo c` and use `have g : HeckeFrameInt Xo c (goodCls Xo c) := heckeFrameInt _ fun _ _ _ _ _ _ a b => b a have a : HeckeFrameInt Xo c (GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.trivialClassCondition Xo c) := heckeFrameInt _ fun _ _ _ _ _ _ _ _ => trivial ⟨⟨g, heckeValueInt _ g⟩, a, hec …`.
-/
theorem heckeInt : HeckeInt := fun _ _ _ _ _ _ _ Xo c =>
  have g : HeckeFrameInt Xo c (goodCls Xo c) := heckeFrameInt _ fun _ _ _ _ _ _ a b => b a
  have a : HeckeFrameInt Xo c (GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.trivialClassCondition Xo c) := heckeFrameInt _ fun _ _ _ _ _ _ _ _ => trivial
  ⟨⟨g, heckeValueInt _ g⟩, a, heckeValueInt _ a⟩

end GlobalTheory.HkIntegral
