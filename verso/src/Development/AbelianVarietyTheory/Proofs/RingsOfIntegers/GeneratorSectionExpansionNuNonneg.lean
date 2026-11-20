import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaFrameExpansionFramedPointGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
namespace GlobalTheory.GeneratorNu

/- English proof (translation)
Take `⟨g, gF, hg, he, -⟩` from `hθ`. Use `(n1a V ϖ hϖ D Q hQ F v hv 1 le_rfl {0} (fun χ => ⟨0, Finset.mem_singleton_self _, χ, by simp⟩) θ 0).2 ?_` and prove the remaining obligations. Introduce `α hα`. Rewrite `hα` using `[Finset.mem_singleton]`. Substitute `hα` using the available equality.

Use `⟨1, fun _ => 1, fun _ => g, fun _ => gF, fun _ => hg, fun _ => ?_, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[QForm.Q_zero hϖ D hQ]`. Simplify using the standard rewrite rules. Simplify using `[DegPre.constBF, he j]`.
-/
theorem nuGe_of_thFrame {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ) (hQ : IsQ D.toPre ϖ Q) (F : Type) [Field F]
    [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) (θ : Fam D.toPre F 1)
    (hθ : GlobalTheory.PowGerm.ThFrame D ϖ F θ) : NuGe D Q F v 1 θ 0 := by
  obtain ⟨g, gF, hg, he, -⟩ := hθ
  refine (n1a V ϖ hϖ D Q hQ F v hv 1 le_rfl {0} (fun χ => ⟨0, Finset.mem_singleton_self _, χ, by simp⟩) θ 0).2 ?_
  intro α hα
  rw [Finset.mem_singleton] at hα
  subst hα
  refine ⟨1, fun _ => 1, fun _ => g, fun _ => gF, fun _ => hg, fun _ => ?_, fun j => ?_⟩
  · rw [QForm.Q_zero hϖ D hQ]; simp
  · simp [DegPre.constBF, he j]

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c T io y I P _ ϖ hϖ Q hQ F _ _ _ _ _ v hv xF h hl hh hpull σ s htie hexp`. Use `letI := io.toAlgebra`. Use `letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra`. Set `φ : T.Fr →ₐ[c.F] F` to `{ algebraMap T.Fr F with commutes' := fun _ => rfl }`. Take `⟨z, hz⟩` from `GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ φ y.1`.

Establish `hx : xF = z.x`. Use `Over.w h` as an intermediate fact. Rewrite `this` using `[hl]`. Conclude with `this.symm.trans hz.1.symm`. Substitute `hx` using the available equality.

Establish `hs : ∀ j, hh.f j = z.s.f j`. Take `⟨-, -, pm, h1, h2, h3⟩` from `hz`. Establish `e : pm = (h ▷ Xo.univ.t.G).left`. Apply `pullback.hom_ext` to reduce the goal to its premises. Use `h2.trans ?_` and prove the remaining obligations.

Use `congrArg Over.Hom.left (whiskerRight_fst h Xo.univ.t.G)` as an intermediate fact. Rewrite `this` using `[Over.comp_left, Over.comp_left, hl]`. Conclude with `this.symm`. Use `h1.trans ?_` and prove the remaining obligations. Use `congrArg Over.Hom.left (whiskerRight_snd h Xo.univ.t.G)` as an intermediate fact.

Rewrite `this` using `[Over.comp_left]`. Conclude with `this.symm`. Substitute `e` using the available equality. Introduce `j`. Conclude with `(hpull j).trans (h3 j _)`.

Establish `hs' : hh = z.s`. Consider the cases of `hh`. Break down `hzs : z.s with ⟨f, hf⟩` into its components or cases. Rewrite `hs` using `[hzs]`. Reduce the equality to equality of the corresponding arguments.

Conclude with `funext hs`. Substitute `hs'` using the available equality. Conclude with `nuGe_of_thFrame hϖ P.D Q hQ F v hv s (GlobalTheory.T.thetaFrame_expansion_framedPoint_generator E H Dw l Xo c T io y.1 I P ϖ hϖ F φ rfl z hz σ s htie hexp)`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (P : PELUnif (maximalIdeal T.V) I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (xF : Sp F ⟶ Xo.X) (h : ptO Xo xF ⟶ ptO Xo (xOf y)), h.left = spMap (algebraMap T.Fr F) → ∀ hh : SecN Xo xF 1, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((1 : ℕ) : ℤ) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (sOf1 y) hh → (∀ σ s, SecTieF I P F xF 1 σ hh → P.U.toUnifPre.ExpandsG F 1 σ s → NuGe P.D Q F v 1 s 0) := by
  intro E _ _ _ H Dw l Xo c T io y I P _ ϖ hϖ Q hQ F _ _ _ _ _ v hv xF h hl hh hpull σ s htie hexp
  letI := io.toAlgebra
  letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra
  let φ : T.Fr →ₐ[c.F] F := { algebraMap T.Fr F with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ φ y.1
  have hx : xF = z.x := by
    have := Over.w h
    rw [hl] at this
    exact this.symm.trans hz.1.symm
  subst hx
  have hs : ∀ j, hh.f j = z.s.f j := by
    obtain ⟨-, -, pm, h1, h2, h3⟩ := hz
    have e : pm = (h ▷ Xo.univ.t.G).left := by
      apply pullback.hom_ext
      · refine h2.trans ?_
        have := congrArg Over.Hom.left (whiskerRight_fst h Xo.univ.t.G)
        rw [Over.comp_left, Over.comp_left, hl] at this
        exact this.symm
      · refine h1.trans ?_
        have := congrArg Over.Hom.left (whiskerRight_snd h Xo.univ.t.G)
        rw [Over.comp_left] at this
        exact this.symm
    subst e
    intro j
    exact (hpull j).trans (h3 j _)
  have hs' : hh = z.s := by
    cases hh
    rcases hzs : z.s with ⟨f, hf⟩
    rw [hzs] at hs
    congr
    exact funext hs
  subst hs'
  exact nuGe_of_thFrame hϖ P.D Q hQ F v hv s (GlobalTheory.T.thetaFrame_expansion_framedPoint_generator E H Dw l Xo c T io y.1 I P ϖ hϖ F φ rfl z hz σ s htie hexp)

end GlobalTheory.GeneratorNu
