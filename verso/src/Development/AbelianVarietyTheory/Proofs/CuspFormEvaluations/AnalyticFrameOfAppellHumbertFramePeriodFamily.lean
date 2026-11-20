import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.AnChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Establish `hA : ∀ z ∈ s, ∀ w, (B z w).im = 0`. Introduce `z hz w`. Establish `hw : w ∈ Submodule.span ℝ s` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw => exact h0 z hz w hw`.

Consider the case `zero => simpa using congrArg Complex.im (h4 0 z 0)`. Consider the case `add w w' _ _ e e' => rw [h3, Complex.add_im, e, e', add_zero]`. Consider the case `smul r w _ e => rw [h4, Complex.im_ofReal_mul, e, mul_zero]`. Establish `hB : ∀ z w, (B z w).im = 0`. Introduce `z w`.

Establish `hz : z ∈ Submodule.span ℝ s` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz => exact hA z hz w`. Consider the case `zero => simpa using congrArg Complex.im (h2 0 0 w)`. Consider the case `add z z' _ _ e e' => rw [h1, Complex.add_im, e, e', add_zero]`.

Consider the case `smul r z _ e`. Establish `: r • z = (r : ℂ) • z` using `by ext k; simp`. Rewrite using `[this, h2, Complex.im_ofReal_mul, e, mul_zero]`. Apply `Complex.ext` to reduce the goal to its premises. Use `hB (Complex.I • z) w` as an intermediate fact.

Rewrite `this` using `[h2]`. Simplify using `using this`. Simplify using `using hB z w`.
-/
theorem form_eq_zero_of_im_span {g : ℕ} (s : Set (Fin g → ℂ)) (hs : Submodule.span ℝ s = ⊤)
    (B : (Fin g → ℂ) → (Fin g → ℂ) → ℂ) (h1 : ∀ z z' w, B (z + z') w = B z w + B z' w)
    (h2 : ∀ (r : ℂ) z w, B (r • z) w = r * B z w) (h3 : ∀ z w w', B z (w + w') = B z w + B z w')
    (h4 : ∀ (r : ℝ) z w, B z (r • w) = r * B z w) (h0 : ∀ z ∈ s, ∀ w ∈ s, (B z w).im = 0) (z w : Fin g → ℂ) :
    B z w = 0 := by
  have hA : ∀ z ∈ s, ∀ w, (B z w).im = 0 := by
    intro z hz w
    have hw : w ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w hw => exact h0 z hz w hw
    | zero => simpa using congrArg Complex.im (h4 0 z 0)
    | add w w' _ _ e e' => rw [h3, Complex.add_im, e, e', add_zero]
    | smul r w _ e => rw [h4, Complex.im_ofReal_mul, e, mul_zero]
  have hB : ∀ z w, (B z w).im = 0 := by
    intro z w
    have hz : z ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => exact hA z hz w
    | zero => simpa using congrArg Complex.im (h2 0 0 w)
    | add z z' _ _ e e' => rw [h1, Complex.add_im, e, e', add_zero]
    | smul r z _ e =>
      have : r • z = (r : ℂ) • z := by ext k; simp
      rw [this, h2, Complex.im_ofReal_mul, e, mul_zero]
  apply Complex.ext
  · have := hB (Complex.I • z) w
    rw [h2] at this
    simpa using this
  · simpa using hB z w

/- English proof (translation)
Establish `hr : ∀ (r : ℝ) (w : Fin g → ℂ), r • w = (r : ℂ) • w` using `fun r w => by ext k; simp`. Establish `l1 : ∀ z z' w, hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w` using `fun z z' w => by`. Simplify using `only [hermForm, add_dotProduct]`. Establish `l2 : ∀ (r : ℂ) z w, hermForm Hm (r • z) w = r * hermForm Hm z w` using `fun r z w => by`. Simplify using `only [hermForm, smul_dotProduct, smul_eq_mul]`.

Establish `l3 : ∀ z w w', hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w'` using `fun z w w' => by`. Simplify using `only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]`. Establish `l4 : ∀ (r : ℝ) z w, hermForm Hm z ((r : ℂ) • w) = r * hermForm Hm z w` using `fun r z w => by`. Simplify using `only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]`. Use `sub_eq_zero.mp (form_eq_zero_of_im_span s hs (fun z w => hermForm Hm (A z) w - hermForm Hm z (A' w)) ?_ ?_ ?_ ?_ ?_ z w)` and prove the remaining obligations.

Introduce `z z' w`. Simplify using `only [map_add, l1]`. Expand and normalize the polynomial expressions, which then agree. Introduce `r z w`. Simplify using `only [map_smul, l2]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `z w w'`. Simplify using `only [map_add, l3]`. Expand and normalize the polynomial expressions, which then agree. Introduce `r z w`.

Simplify using `only [hr, map_smul, l4]`. Expand and normalize the polynomial expressions, which then agree. Introduce `z hz w hw`. Simplify using `only [Complex.sub_im, h0 z hz w hw, sub_self]`.
-/
theorem hermForm_adj_of_im_span {g : ℕ} (s : Set (Fin g → ℂ)) (hs : Submodule.span ℝ s = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (A A' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h0 : ∀ z ∈ s, ∀ w ∈ s, (hermForm Hm (A z) w).im = (hermForm Hm z (A' w)).im) (z w : Fin g → ℂ) :
    hermForm Hm (A z) w = hermForm Hm z (A' w) := by
  have hr : ∀ (r : ℝ) (w : Fin g → ℂ), r • w = (r : ℂ) • w := fun r w => by ext k; simp
  have l1 : ∀ z z' w, hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := fun z z' w => by
    simp only [hermForm, add_dotProduct]
  have l2 : ∀ (r : ℂ) z w, hermForm Hm (r • z) w = r * hermForm Hm z w := fun r z w => by
    simp only [hermForm, smul_dotProduct, smul_eq_mul]
  have l3 : ∀ z w w', hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := fun z w w' => by
    simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]
  have l4 : ∀ (r : ℝ) z w, hermForm Hm z ((r : ℂ) • w) = r * hermForm Hm z w := fun r z w => by
    simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.star_def,
      Complex.conj_ofReal]
  refine sub_eq_zero.mp (form_eq_zero_of_im_span s hs
    (fun z w => hermForm Hm (A z) w - hermForm Hm z (A' w)) ?_ ?_ ?_ ?_ ?_ z w)
  · intro z z' w
    simp only [map_add, l1]; ring
  · intro r z w
    simp only [map_smul, l2]; ring
  · intro z w w'
    simp only [map_add, l3]; ring
  · intro r z w
    simp only [hr, map_smul, l4]; ring
  · intro z hz w hw
    simp only [Complex.sub_im, h0 z hz w hw, sub_self]

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ y g ty el σ' F i Pm Hm χl fr hP hy hA hd`. Take `⟨x, xo, u, tan, eig, bas, s, gen⟩` from `y`. Simplify using `only at hy hd`. Substitute `hy` using the available equality. Take `⟨hH, -, hE, f1, f2, f3, f4, f5⟩` from `hA`.

Establish `hlin : ∀ (α : 𝓞 E) b, Pm (α • b) = tyAct ty α (Pm b)` using `fun α b => by`. Use extensionality with `k`. Simplify `hP.1 α b k` using `[tyAct]`. Use `⟨{ e := F.ex i Pm lat := Pm.range span := by simpa using hP.2.2.2.1 e_add := F.ex_add i Pm hP e_onto := F.ex_onto i Pm hP e_ker := F.ex_ker i Pm hP hol := anHol F i Pm hP Hm := Hm herm := hH χ := χl fr := fr fr_hol := f1 fr_ne := f2 fr_g := f3 fr_0 := f4 χ_norm := ?_ fr_per := ?_ …` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`.

Establish `hc : (F.ex i Pm 0).left.base (IsLocalRing.closedPoint ℂ) ∈ (⨆ j, Xo.univ.t.PP.L.U j : Xo.univ.t.G.left.Opens)`. Rewrite using `[Xo.univ.t.PP.isLB.cover]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨j, -⟩` from `TopologicalSpace.Opens.mem_iSup.1 hc`. Conclude with `(f5 a j 0).1`.

Introduce and unpack `_ ⟨a, rfl⟩ j z hz`. Conclude with `(f5 a j z).2 hz`. Introduce `a`. Use `hermForm_adj_of_im_span _ hP.2.2.2.1 Hm _ _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨b, rfl⟩ _ ⟨b', rfl⟩`.

Rewrite using `[← hlin, ← hlin, hE, hE, (F.Di i).adj]`.
-/
theorem anPt_of_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (σ' : KA l →+* ℂ) (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (Pm : (F.Di i).La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ), IsPeriod (F.Di i) ty Pm → y.x = F.u i Pm → AHFrame F i Pm Hm χl fr → (∀ ℓ : Lt1 Dw, IsDerivAt0 (fun z => (F.ex i Pm z).left) (Pi.single (el.symm ℓ) 1) (y.u ℓ.1 ℓ.2)) → ∃ Φ : AnPt y g ty el, Φ.OfFam F i Pm ∧ Φ.Hm = Hm ∧ Φ.χ = χl ∧ Φ.fr = fr ∧ (∀ (α : 𝓞 E) a, Pm (F.t i (α • a)) = tyAct ty α (Pm (F.t i a))) ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo y.x a = Φ.e ((l.M : ℂ)⁻¹ • Pm (F.t i a)) := by
  intro E _ _ _ H Dw l Xo c _ y g ty el σ' F i Pm Hm χl fr hP hy hA hd
  obtain ⟨x, xo, u, tan, eig, bas, s, gen⟩ := y
  dsimp only at hy hd
  subst hy
  obtain ⟨hH, -, hE, f1, f2, f3, f4, f5⟩ := hA
  have hlin : ∀ (α : 𝓞 E) b, Pm (α • b) = tyAct ty α (Pm b) := fun α b => by
    ext k
    simpa [tyAct] using hP.1 α b k
  refine ⟨{ e := F.ex i Pm
            lat := Pm.range
            span := by simpa using hP.2.2.2.1
            e_add := F.ex_add i Pm hP
            e_onto := F.ex_onto i Pm hP
            e_ker := F.ex_ker i Pm hP
            hol := anHol F i Pm hP
            Hm := Hm
            herm := hH
            χ := χl
            fr := fr
            fr_hol := f1
            fr_ne := f2
            fr_g := f3
            fr_0 := f4
            χ_norm := ?_
            fr_per := ?_
            lin := fun a z => F.ex_lin i Pm hP a z
            adj := ?_
            der := hd }, ⟨fun _ => rfl, rfl, hE⟩, rfl, rfl, rfl, fun α a => by rw [map_smul, hlin],
          fun a ha => F.ex_eta i Pm hP a ha⟩
  · rintro _ ⟨a, rfl⟩
    have hc : (F.ex i Pm 0).left.base (IsLocalRing.closedPoint ℂ) ∈
        (⨆ j, Xo.univ.t.PP.L.U j : Xo.univ.t.G.left.Opens) := by
      rw [Xo.univ.t.PP.isLB.cover]; trivial
    obtain ⟨j, -⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    exact (f5 a j 0).1
  · rintro _ ⟨a, rfl⟩ j z hz
    exact (f5 a j z).2 hz
  · intro a
    refine hermForm_adj_of_im_span _ hP.2.2.2.1 Hm _ _ ?_
    rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
    rw [← hlin, ← hlin, hE, hE, (F.Di i).adj]

end GlobalTheory.AnVal
