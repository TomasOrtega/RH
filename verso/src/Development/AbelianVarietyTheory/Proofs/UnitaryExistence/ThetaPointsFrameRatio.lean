import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecValuesComplexFibreAbelianScheme
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

/- English proof (translation)
Take `⟨h1, h2, -⟩` from `sec_values_complex_fibre hT E H Dw l Xo x s`. Take `⟨a, ha, -⟩` from `hs s'`. Take `⟨i, pt, hp, hne⟩` from `h2.1 hs`. Establish `hi : i = fun _ => i (0 : Fin 1)` using `funext fun k => congrArg i (Subsingleton.elim _ _)`. Take `⟨j, rfl⟩ : ∃ j, i = fun _ => j` from `⟨_, hi⟩`.

Establish `cond : gxFst x ≫ Xo.univ.t.G.hom = gxSnd x ≫ x` using `pullback.condition.symm`. Take `⟨z, hz⟩` from `hex (Over.homMk (pt ≫ gxFst x) (by show (pt ≫ gxFst x) ≫ Xo.univ.t.G.hom = x`. Rewrite using `[Category.assoc, cond, ← Category.assoc, hp, Category.id_comp]))`. Establish `hz' : pt ≫ gxFst x = (ex z).left` using `by rw [hz]; rfl`. Establish `hU : ⊤ ≤ pt ⁻¹ᵁ (PPx x).U (fun _ => j)`.

Assume the negation of the conclusion as `h`. Conclude with `hne (by unfold valAt'; rw [dif_neg h])`. Establish `hU' : ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j`. Rewrite using `[← hz']`. Introduce `p hp'`.

Conclude with `Set.mem_iInter.1 (hU hp') (0 : Fin 1)`. Establish `e` using `hv j z pt hz' hp hU'`. Establish `e'` using `(congrArg (valAt' pt ((PPx x).U (fun _ => j))) (ha (fun _ => j))).trans (h1 a _ pt hp)`. Establish `hat : a = t` using `mul_right_cancel₀ hne (e'.symm.trans e)`. Rewrite using `[← hat]`.

Conclude with `ha`.
-/
theorem sec_eq_scal_of_values (hT : Out.SecTwistSt) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {V : Type}
    (x : Sp ℂ ⟶ Xo.X) (ex : V → (Over.mk x ⟶ Xo.univ.t.G)) (hex : Function.Surjective ex)
    (s s' : LB.Sec (PPx x)) (hs : SecGen x s) (t : ℂ)
    (hv : ∀ j z (pt : Sp ℂ ⟶ Gx x), pt ≫ gxFst x = (ex z).left → pt ≫ gxSnd x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx x).U (fun _ => j)) (s'.f (fun _ => j)) =
        t * valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j))) :
    ∀ i, s'.f i = scal x t i * s.f i := by
  obtain ⟨h1, h2, -⟩ := sec_values_complex_fibre hT E H Dw l Xo x s
  obtain ⟨a, ha, -⟩ := hs s'
  obtain ⟨i, pt, hp, hne⟩ := h2.1 hs
  have hi : i = fun _ => i (0 : Fin 1) := funext fun k => congrArg i (Subsingleton.elim _ _)
  obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨_, hi⟩
  have cond : gxFst x ≫ Xo.univ.t.G.hom = gxSnd x ≫ x := pullback.condition.symm
  obtain ⟨z, hz⟩ := hex (Over.homMk (pt ≫ gxFst x) (by
    show (pt ≫ gxFst x) ≫ Xo.univ.t.G.hom = x
    rw [Category.assoc, cond, ← Category.assoc, hp, Category.id_comp]))
  have hz' : pt ≫ gxFst x = (ex z).left := by rw [hz]; rfl
  have hU : ⊤ ≤ pt ⁻¹ᵁ (PPx x).U (fun _ => j) := by
    by_contra h
    exact hne (by unfold valAt'; rw [dif_neg h])
  have hU' : ⊤ ≤ (ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
    rw [← hz']
    intro p hp'
    exact Set.mem_iInter.1 (hU hp') (0 : Fin 1)
  have e := hv j z pt hz' hp hU'
  have e' := (congrArg (valAt' pt ((PPx x).U (fun _ => j))) (ha (fun _ => j))).trans (h1 a _ pt hp)
  have hat : a = t := mul_right_cancel₀ hne (e'.symm.trans e)
  rw [← hat]
  exact ha

/- English proof (translation)
Take `⟨N, _, _, v, ρ, -, h2, h3, -⟩` from `TanMod.exists_tangent_module E H Dw l Xo S x`. Use `choose n hn using fun j => (h2 _).1 (tan j)`. Take `rfl : u = fun j => v (n j)` from `funext fun j => (hn j).symm`. Rewrite using `[h3]`. Use `show v (n i) = _`.

Use `congr 1`. Rewrite using `[Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]) (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem isCombAt_single_of_isTanAt {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S]
    (x : Sp S ⟶ Xo.X) {m : ℕ} (u : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (tan : ∀ j, IsTanAt x (u j))
    (i : Fin m) : IsCombAt x u (Pi.single i 1) (u i) := by
  obtain ⟨N, _, _, v, ρ, -, h2, h3, -⟩ := TanMod.exists_tangent_module E H Dw l Xo S x
  choose n hn using fun j => (h2 _).1 (tan j)
  obtain rfl : u = fun j => v (n j) := funext fun j => (hn j).symm
  rw [h3]
  show v (n i) = _
  congr 1
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]) (by simp)]
  simp

/- English proof (translation)
Establish `: Scheme.Hom.appLE (𝟙 X) U U h = 𝟙 _`. Rewrite using `[Scheme.Hom.appLE, Scheme.Hom.id_app]`. Conclude with `(Category.id_comp _).trans (X.presheaf.map_id _)`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem appLE_id_apply_self {X : Scheme.{0}} (U : X.Opens) (h : U ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) (f : Γ(X, U)) :
    (Scheme.Hom.appLE (𝟙 X) U U h).hom f = f := by
  have : Scheme.Hom.appLE (𝟙 X) U U h = 𝟙 _ := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (Category.id_comp _).trans (X.presheaf.map_id _)
  rw [this]
  rfl

/- English proof (translation)
Introduce `hT E _ _ _ H Dw l Xo c σ g e F r M k T b hb κ t₀ y y' hy hy'`. Establish `hP` using `T.isPer _ hb`. Take `⟨x, xo, u, tan, eig, basis, s, gen⟩` from `y`. Take `⟨x', xo', u', tan', eig', basis', s', gen'⟩` from `y'`. Take `⟨hx, hu, hs⟩` from `hy`.

Take `⟨hx', hu', hs'⟩` from `hy'`. Simplify using `only at hx hu hs hx' hu' hs'`. Substitute `hx hx'` using the available equality. Take `⟨-, hd, -⟩` from `isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k _ hP`. Establish `huu : ∀ τ i, u' τ i = u τ i` using `fun τ i => (hd _).unique (hu' τ i) (hu τ i)`.

Use `⟨rfl, fun τ i => ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne hj.ne' _, ?_⟩, 𝟙 _, Category.id_comp _, Category.id_comp _, fun i h => ?_⟩` and prove the remaining obligations. Use `show IsCombAt _ (u τ) _ (u' τ i)`. Rewrite using `[huu]`. Conclude with `isCombAt_single_of_isTanAt (S := CAt σ) _ _ (tan τ) i`. Establish `key` using `sec_eq_scal_of_values hT (F.u k (T.Pf (T.co b))) (F.ex k (T.Pf (T.co b))) (F.ex_onto k _ hP) s s' gen (toC (t₀ : CAt σ)) (fun j z pt h1 h2 h3 => by`.

Use `(hs' j z pt h1 h2 h3).trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ (congrArg (toC (t₀ : CAt σ) * ·) (hs j z pt h1 h2 h3).symm)` and prove the remaining obligations. Use the proof step `ring)`. Use `Eq.trans ?_ (key i).symm` and prove the remaining obligations. Conclude with `appLE_id_apply_self _ h _`.
-/
theorem frBor_of_isThetaPt : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ : ℂ) (t₀ : (CAt σ)ˣ) (y y' : FrPt Xo c (CAt σ)), IsThetaPt T b κ y → IsThetaPt T b (toC (t₀ : CAt σ) * κ) y' → FrBor (fun i => Option.elim i t₀ (fun _ => 1)) y y' := by
  intro hT E _ _ _ H Dw l Xo c σ g e F r M k T b hb κ t₀ y y' hy hy'
  have hP := T.isPer _ hb
  obtain ⟨x, xo, u, tan, eig, basis, s, gen⟩ := y
  obtain ⟨x', xo', u', tan', eig', basis', s', gen'⟩ := y'
  obtain ⟨hx, hu, hs⟩ := hy
  obtain ⟨hx', hu', hs'⟩ := hy'
  dsimp only at hx hu hs hx' hu' hs'
  subst hx hx'
  obtain ⟨-, hd, -⟩ := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k _ hP
  have huu : ∀ τ i, u' τ i = u τ i := fun τ i => (hd _).unique (hu' τ i) (hu τ i)
  refine ⟨rfl, fun τ i => ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne hj.ne' _, ?_⟩, 𝟙 _,
    Category.id_comp _, Category.id_comp _, fun i h => ?_⟩
  · show IsCombAt _ (u τ) _ (u' τ i)
    rw [huu]
    exact isCombAt_single_of_isTanAt (S := CAt σ) _ _ (tan τ) i
  · have key := sec_eq_scal_of_values hT (F.u k (T.Pf (T.co b))) (F.ex k (T.Pf (T.co b))) (F.ex_onto k _ hP)
      s s' gen (toC (t₀ : CAt σ)) (fun j z pt h1 h2 h3 => by
        refine (hs' j z pt h1 h2 h3).trans ?_
        refine Eq.trans ?_ (congrArg (toC (t₀ : CAt σ) * ·) (hs j z pt h1 h2 h3).symm)
        ring)
    refine Eq.trans ?_ (key i).symm
    exact appLE_id_apply_self _ h _

end GlobalTheory
