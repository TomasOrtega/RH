import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAnalyticFrameOfAnalyticFibre
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AppellHumbertFrameSemicharacter
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilEqIffHermFormEqComplex
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PointEqIffIsometryClosed
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Dict.SameFibre

open GlobalTheory.AnVal
open GlobalTheory.UnifPoint

/- English proof (translation)
Take `⟨s, hs', hsp, hli⟩` from `exists_linearIndependent ℝ (Λ : Set (Fin g → ℂ))`. Establish `: Finite s` using `hli.finite`. Use `choose k hk using hi`. Set `f : Λ → (s → ℤ)` to `fun a b => k a a.2 b (hs' b.2)`. Establish `hf : ∀ a b, ((f a b : ℤ) : ℝ) = (hermForm M a b).im` using `fun a b => (hk _ _ _ _).symm`.

Use `DiscreteTopology.of_continuous_injective (f := f) (continuous_pi fun b => ?_) fun a a' h => ?_` and prove the remaining obligations. Use `Int.isClosedEmbedding_coe_real.isEmbedding.continuous_iff.2 ?_` and prove the remaining obligations. Establish `: (Int.cast ∘ fun a => f a b : Λ → ℝ) = fun a : Λ => (hermForm M a b).im` using `funext fun a => hf a b`. Rewrite using `[this]`. Unfold `hermForm`.

Use `fun_prop`. Establish `h0 : ∀ w, (hermForm M (a - a') w).im = 0` using `fun w => by`. Establish `hw : w ∈ Submodule.span ℝ s` using `by rw [hsp, hs]; trivial`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw`.

Use `hf a ⟨w, hw⟩` as an intermediate fact. Rewrite `this` using `[h, hf]`. Simplify using `only [hermForm, sub_dotProduct, Complex.sub_im] at this ⊢`. Rewrite using `[this, sub_self]`. Consider the case `zero => simp [hermForm]`.

Consider the case `add x y _ _ hx hy`. Simplify using `only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im] at hx hy ⊢`. Rewrite using `[hx, hy, add_zero]`. Consider the case `smul r x _ hx`. Rewrite using `[← Complex.coe_smul]`.

Simplify using `only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal, Complex.im_ofReal_mul] at hx ⊢`. Rewrite using `[hx, mul_zero]`. Assume the negation of the conclusion as `hne`. Establish `h1` using `pos (a - a') (sub_ne_zero.2 fun e => hne (Subtype.ext e))`. Establish `h2` using `h0 (Complex.I • ((a : Fin g → ℂ) - a'))`.

Simplify using `only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.star_def, Complex.conj_I, neg_mul, Complex.neg_im, Complex.I_mul_im, neg_eq_zero] at h1 h2`. Conclude with `h1.ne' h2`.
-/
theorem discrete_of_im_int {g : ℕ} (Λ : AddSubgroup (Fin g → ℂ)) (M : Matrix (Fin g) (Fin g) ℂ)
    (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (pos : ∀ z, z ≠ 0 → 0 < (hermForm M z z).re)
    (hi : ∀ a ∈ Λ, ∀ b ∈ Λ, ∃ k : ℤ, (hermForm M a b).im = k) : DiscreteTopology Λ := by
  obtain ⟨s, hs', hsp, hli⟩ := exists_linearIndependent ℝ (Λ : Set (Fin g → ℂ))
  have : Finite s := hli.finite
  choose k hk using hi
  let f : Λ → (s → ℤ) := fun a b => k a a.2 b (hs' b.2)
  have hf : ∀ a b, ((f a b : ℤ) : ℝ) = (hermForm M a b).im := fun a b => (hk _ _ _ _).symm
  refine DiscreteTopology.of_continuous_injective (f := f) (continuous_pi fun b => ?_) fun a a' h => ?_
  · refine Int.isClosedEmbedding_coe_real.isEmbedding.continuous_iff.2 ?_
    have : (Int.cast ∘ fun a => f a b : Λ → ℝ) = fun a : Λ => (hermForm M a b).im := funext fun a => hf a b
    rw [this]
    unfold hermForm
    fun_prop
  · have h0 : ∀ w, (hermForm M (a - a') w).im = 0 := fun w => by
      have hw : w ∈ Submodule.span ℝ s := by rw [hsp, hs]; trivial
      induction hw using Submodule.span_induction with
      | mem w hw =>
        have := hf a ⟨w, hw⟩
        rw [h, hf] at this
        simp only [hermForm, sub_dotProduct, Complex.sub_im] at this ⊢
        rw [this, sub_self]
      | zero => simp [hermForm]
      | add x y _ _ hx hy =>
        simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im] at hx hy ⊢
        rw [hx, hy, add_zero]
      | smul r x _ hx =>
        rw [← Complex.coe_smul]
        simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
          Complex.star_def, Complex.conj_ofReal, Complex.im_ofReal_mul] at hx ⊢
        rw [hx, mul_zero]
    by_contra hne
    have h1 := pos (a - a') (sub_ne_zero.2 fun e => hne (Subtype.ext e))
    have h2 := h0 (Complex.I • ((a : Fin g → ℂ) - a'))
    simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
      Complex.star_def, Complex.conj_I, neg_mul, Complex.neg_im, Complex.I_mul_im, neg_eq_zero] at h1 h2
    exact h1.ne' h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}

/- English proof (translation)
Take `⟨w, hw, -⟩` from `m.lin`. Take `⟨w', hw'⟩` from `LBIso.symm ⟨w, hw⟩`. Establish `hL` using `t₁.PP.isLB`. Establish `hM` using `pull_isLB t.PP.isLB m.φ`. Set `u₁` to `OrthoMetric.fibreUnif m.cart Φ.e Φ.lat Φ.fr Φ.e_add Φ.e_onto Φ.e_ker (discrete_of_im_int Φ.lat Φ.Hm Φ.span pos fun a ha b hb => Φ.herm_im_int ha hb) Φ.span (fun U f => by simpa only [Set.mem_univ, true_and] using Φ.hol U f) Φ.fr_hol Φ.fr_ne Φ.fr_g`.

Establish `hA₁ : u₁.IsAH Φ.Hm fun a => Φ.χ a` using `⟨Φ.herm, pos, fun a => Φ.χ_norm a a.2, fun a j z hj => Φ.fr_per a a.2 _ z ((OrthoMetric.lift_le m.cart _ j).1 hj)⟩`. Conclude with `⟨ArchMetricCompare.carry u₁ hM hL hw', _, fun _ => Iff.rfl, fun z => OrthoMetric.liftPt_comp m.cart _, ArchMetricCompare.carry_isAH hM hL hw' hA₁⟩`.
-/
theorem exists_holUnif {S : Scheme.{0}} {t : SAB H S} {y : Sp ℂ ⟶ S} {t₁ : SAB H (Sp ℂ)} (m : SABMap t₁ t y)
    (Φ : AnFr t.G t.PP y g) (pos : ∀ z, z ≠ 0 → 0 < (hermForm Φ.Hm z z).re) :
    ∃ (u : HolUnif t₁.G t₁.PP.L g) (χ : u.Λ → ℂ), (∀ z, z ∈ u.Λ ↔ z ∈ Φ.lat) ∧
      (∀ z, (u.ex z).left ≫ m.φ = (Φ.e z).left) ∧ u.IsAH Φ.Hm χ := by
  obtain ⟨w, hw, -⟩ := m.lin
  obtain ⟨w', hw'⟩ := LBIso.symm ⟨w, hw⟩
  have hL := t₁.PP.isLB
  have hM := pull_isLB t.PP.isLB m.φ
  let u₁ := OrthoMetric.fibreUnif m.cart Φ.e Φ.lat Φ.fr Φ.e_add Φ.e_onto Φ.e_ker
    (discrete_of_im_int Φ.lat Φ.Hm Φ.span pos fun a ha b hb => Φ.herm_im_int ha hb) Φ.span
    (fun U f => by simpa only [Set.mem_univ, true_and] using Φ.hol U f) Φ.fr_hol Φ.fr_ne Φ.fr_g
  have hA₁ : u₁.IsAH Φ.Hm fun a => Φ.χ a :=
    ⟨Φ.herm, pos, fun a => Φ.χ_norm a a.2, fun a j z hj =>
      Φ.fr_per a a.2 _ z ((OrthoMetric.lift_le m.cart _ j).1 hj)⟩
  exact ⟨ArchMetricCompare.carry u₁ hM hL hw', _, fun _ => Iff.rfl, fun z => OrthoMetric.liftPt_comp m.cart _,
    ArchMetricCompare.carry_isAH hM hL hw' hA₁⟩

/- English proof (translation)
Establish `hT` using `thetaUnifAV_all`. Establish `hL : Out.Laws` using `firstFiveLaws.1`. Establish `p₁` using `obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ o₁`. Establish `p₂` using `obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ o₂`. Take `⟨E₁, e₁, -, g₁, -, -, w₁⟩` from `AHWeil.tangent_and_weil_of_isAH hT (objPol o₁ p₁) g u₁ M₁ χ₁ h₁`.

Take `⟨E₂, e₂, -, g₂, -, -, w₂⟩` from `AHWeil.tangent_and_weil_of_isAH hT (objPol o₂ p₂) g u₂ M₂ χ₂ h₂`. Take `⟨α, hα, hα'⟩ : ∃ α : o₁.t.G ⟶ o₂.t.G, IsMonHom α ∧ ∀ z, u₂.ex z = u₁.ex z ≫ α` from `exists_isMonHom_of_map_lattice hT hL (objPol o₁ p₁) (objPol o₂ p₂) g u₁ u₂ LinearMap.id g₁.symm g₂.symm fun z hz => (hΛ z).1 hz`. Take `⟨β, -, hβ'⟩ : ∃ β : o₂.t.G ⟶ o₁.t.G, IsMonHom β ∧ ∀ z, u₁.ex z = u₂.ex z ≫ β` from `exists_isMonHom_of_map_lattice hT hL (objPol o₂ p₂) (objPol o₁ p₁) g u₂ u₁ LinearMap.id g₂.symm g₁.symm fun z hz => (hΛ z).2 hz`. Use `p₁.1.smooth` as an intermediate fact. Use `p₂.1.smooth` as an intermediate fact.

Use `p₁.1.proper` as an intermediate fact. Use `p₂.1.proper` as an intermediate fact. Establish `: IsReduced o₁.t.G.left` using `isReduced_of_smooth_complex _ o₁.t.G.hom inferInstance`. Establish `: IsReduced o₂.t.G.left` using `isReduced_of_smooth_complex _ o₂.t.G.hom inferInstance`. Set `ψ : o₁.t.G ≅ o₂.t.G` to `{ hom := α inv := β hom_inv_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by`.

Take `⟨z, rfl⟩` from `u₁.ex_onto x`. Rewrite using `[← Category.assoc, ← hα', ← hβ', Category.comp_id]`. Use `inv_hom_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by`. Take `⟨z, rfl⟩` from `u₂.ex_onto x`. Rewrite using `[← Category.assoc, ← hβ', ← hα', Category.comp_id] }`.

Establish `hact : ∀ a, o₁.t.act.act a ≫ α = α ≫ o₂.t.act.act a` using `fun a => ComplexPoints.over_hom_ext_of_complexPoints fun x => by`. Take `⟨z, rfl⟩` from `u₁.ex_onto x`. Rewrite using `[← Category.assoc, ← Category.assoc, ← a₁, ← hα', ← hα', ← a₂]`. Establish `hlam` using `lam_iso_of_weil_pairings hL ℂ (objPol o₁ p₁) (objPol o₂ p₂) α 2 1 hα Nat.prime_two inferInstance fun k x y c hk _ hx hy hw => by`. Take `⟨a, rfl⟩` from `CM.HermWeil.exists_eq_ex_div u₁ hk x hx`.

Take `⟨a', rfl⟩` from `CM.HermWeil.exists_eq_ex_div u₁ hk y hy`. Establish `w` using `w₁ k a a' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl`. Take `rfl` from `weilIs_unique_fieldPoint _ _ _ o₁.t.PP.isLB ℂ (𝟙 _) k _ _ _ _ hw w`. Establish `w'` using `w₂ k ⟨a, (hΛ _).1 a.2⟩ ⟨a', (hΛ _).1 a'.2⟩ (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl`. Establish `e : E₂ ⟨a, (hΛ _).1 a.2⟩ ⟨a', (hΛ _).1 a'.2⟩ = E₁ a a'`.

Establish `h` using `e₁ a a'`. Rewrite `h` using `[hM, ← e₂ ⟨a, (hΛ _).1 a.2⟩ ⟨a', (hΛ _).1 a'.2⟩]`. Conclude with `h.symm` after adjusting the coercions. Rewrite `w'` using `[hα', hα', e]`. Rewrite using `[pow_one]`.

Conclude with `w'`. Establish `: IsMonHom ψ.hom` using `hα`. Conclude with `⟨⟨CubeMap.ofHom α, isGrpPullback_of_iso ψ, rfl, fun a => congrArg (fun z => z.left) (hact a), HeckePoint.isPullCubical_of_iso hL.globalFns p₁.1 α o₁.t.cub o₂.t.cub (HeckePoint.iso_of_lam o₁.t o₂.t α hact hlam)⟩, fun z => congrArg (fun q => q.left) (hα' z).symm⟩`.
-/
theorem exists_sabMap_of_isAH {D : Datum H} {l : Geo.Tor.Level H} {b : Base l ℂ} {s : Sp ℂ ⟶ Sp ℂ}
    (o₁ o₂ : Obj D l b s) (u₁ : HolUnif o₁.t.G o₁.t.PP.L g) (u₂ : HolUnif o₂.t.G o₂.t.PP.L g)
    {M₁ M₂ : Matrix (Fin g) (Fin g) ℂ} {χ₁ : u₁.Λ → ℂ} {χ₂ : u₂.Λ → ℂ} (h₁ : u₁.IsAH M₁ χ₁) (h₂ : u₂.IsAH M₂ χ₂)
    (hΛ : ∀ z, z ∈ u₁.Λ ↔ z ∈ u₂.Λ) (hM : ∀ z w, hermForm M₁ z w = hermForm M₂ z w)
    (F : 𝓞 E → (Fin g → ℂ) → (Fin g → ℂ)) (a₁ : ∀ a z, u₁.ex (F a z) = u₁.ex z ≫ o₁.t.act.act a)
    (a₂ : ∀ a z, u₂.ex (F a z) = u₂.ex z ≫ o₂.t.act.act a) :
    ∃ m : SABMap o₁.t o₂.t (𝟙 _), ∀ z, (u₁.ex z).left ≫ m.φ = (u₂.ex z).left := by
  have hT := thetaUnifAV_all
  have hL : Out.Laws := firstFiveLaws.1
  have p₁ := obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ o₁
  have p₂ := obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ o₂
  obtain ⟨E₁, e₁, -, g₁, -, -, w₁⟩ := AHWeil.tangent_and_weil_of_isAH hT (objPol o₁ p₁) g u₁ M₁ χ₁ h₁
  obtain ⟨E₂, e₂, -, g₂, -, -, w₂⟩ := AHWeil.tangent_and_weil_of_isAH hT (objPol o₂ p₂) g u₂ M₂ χ₂ h₂
  obtain ⟨α, hα, hα'⟩ : ∃ α : o₁.t.G ⟶ o₂.t.G, IsMonHom α ∧ ∀ z, u₂.ex z = u₁.ex z ≫ α :=
    exists_isMonHom_of_map_lattice hT hL (objPol o₁ p₁) (objPol o₂ p₂) g u₁ u₂ LinearMap.id g₁.symm g₂.symm
      fun z hz => (hΛ z).1 hz
  obtain ⟨β, -, hβ'⟩ : ∃ β : o₂.t.G ⟶ o₁.t.G, IsMonHom β ∧ ∀ z, u₁.ex z = u₂.ex z ≫ β :=
    exists_isMonHom_of_map_lattice hT hL (objPol o₂ p₂) (objPol o₁ p₁) g u₂ u₁ LinearMap.id g₂.symm g₁.symm
      fun z hz => (hΛ z).2 hz
  have := p₁.1.smooth
  have := p₂.1.smooth
  have := p₁.1.proper
  have := p₂.1.proper
  have : IsReduced o₁.t.G.left := isReduced_of_smooth_complex _ o₁.t.G.hom inferInstance
  have : IsReduced o₂.t.G.left := isReduced_of_smooth_complex _ o₂.t.G.hom inferInstance
  let ψ : o₁.t.G ≅ o₂.t.G :=
    { hom := α
      inv := β
      hom_inv_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u₁.ex_onto x
        rw [← Category.assoc, ← hα', ← hβ', Category.comp_id]
      inv_hom_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u₂.ex_onto x
        rw [← Category.assoc, ← hβ', ← hα', Category.comp_id] }
  have hact : ∀ a, o₁.t.act.act a ≫ α = α ≫ o₂.t.act.act a := fun a =>
    ComplexPoints.over_hom_ext_of_complexPoints fun x => by
      obtain ⟨z, rfl⟩ := u₁.ex_onto x
      rw [← Category.assoc, ← Category.assoc, ← a₁, ← hα', ← hα', ← a₂]
  have hlam := lam_iso_of_weil_pairings hL ℂ (objPol o₁ p₁) (objPol o₂ p₂) α 2 1 hα Nat.prime_two inferInstance
    fun k x y c hk _ hx hy hw => by
      obtain ⟨a, rfl⟩ := CM.HermWeil.exists_eq_ex_div u₁ hk x hx
      obtain ⟨a', rfl⟩ := CM.HermWeil.exists_eq_ex_div u₁ hk y hy
      have w := w₁ k a a' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
      obtain rfl := weilIs_unique_fieldPoint _ _ _ o₁.t.PP.isLB ℂ (𝟙 _) k _ _ _ _ hw w
      have w' := w₂ k ⟨a, (hΛ _).1 a.2⟩ ⟨a', (hΛ _).1 a'.2⟩ (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
      have e : E₂ ⟨a, (hΛ _).1 a.2⟩ ⟨a', (hΛ _).1 a'.2⟩ = E₁ a a' := by
        have h := e₁ a a'
        rw [hM, ← e₂ ⟨a, (hΛ _).1 a.2⟩ ⟨a', (hΛ _).1 a'.2⟩] at h
        exact_mod_cast h.symm
      rw [hα', hα', e] at w'
      rw [pow_one]
      exact w'
  have : IsMonHom ψ.hom := hα
  exact ⟨⟨CubeMap.ofHom α, isGrpPullback_of_iso ψ, rfl, fun a => congrArg (fun z => z.left) (hact a),
    HeckePoint.isPullCubical_of_iso hL.globalFns p₁.1 α o₁.t.cub o₂.t.cub
      (HeckePoint.iso_of_lam o₁.t o₂.t α hact hlam)⟩,
    fun z => congrArg (fun q => q.left) (hα' z).symm⟩

end GlobalTheory.Dict.SameFibre

open GlobalTheory.Dict.SameFibre GlobalTheory.UnifPoint GlobalTheory.AnVal in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ hA r g X bas idx e x L y y' A A' hs hx hL mk _ hm hm'`. Take `⟨Φ, k₁, -, l₁, m₁, -⟩` from `AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A hs hx hL`. Take `⟨Φ', k₂, -, l₂, m₂, -⟩` from `AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y' A' hs hx hL`. Take `⟨-, pos, -⟩` from `hx_laws E r X g bas idx 0 hs Even.zero x hx`. Set `σ : KA l →+* ℂ` to `(algebraMap c.F ℂ).comp (IntermediateField.inclusion c.le).toRingHom`.

Establish `hy : y.x ≫ Xo.s = 𝟙 _ ≫ spMap σ` using `y.x_over.trans (Category.id_comp _).symm`. Establish `hy' : y'.x ≫ Xo.s = 𝟙 _ ≫ spMap σ` using `y'.x_over.trans (Category.id_comp _).symm`. Take `⟨o₁, ⟨n₁⟩⟩` from `obj_pull E H Dw l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) y.x rfl rfl hy Xo.univ`. Take `⟨o₂, ⟨n₂⟩⟩` from `obj_pull E H Dw l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) y'.x rfl rfl hy' Xo.univ`. Take `⟨u₁, χ₁, b₁, f₁, h₁⟩` from `exists_holUnif n₁.toSABMap Φ.toAnFr fun z hz => by rw [m₁]; exact pos z hz`.

Take `⟨u₂, χ₂, b₂, f₂, h₂⟩` from `exists_holUnif n₂.toSABMap Φ'.toAnFr fun z hz => by rw [m₂]; exact pos z hz`. Take `⟨m, hm₀⟩` from `exists_sabMap_of_isAH o₁ o₂ u₁ u₂ h₁ h₂ (fun z => by rw [b₁, b₂, l₁, l₂]) (fun z w => by rw [m₁, m₂]) (fun a => tyAct (fun j => rowType X (idx j)) a) (fun a z => OrthoMetric.pt_ext n₁.cart (by`. Rewrite using `[f₁, Φ.lin, Over.comp_left, Over.comp_left, Category.assoc, n₁.act, ← Category.assoc, f₁]))`. Use the proof step `(fun a z => OrthoMetric.pt_ext n₂.cart (by`. Rewrite using `[f₂, Φ'.lin, Over.comp_left, Over.comp_left, Category.assoc, n₂.act, ← Category.assoc, f₂]))`.

Take `⟨k⟩` from `exists_objMap o₁ o₂ m (fun a ha => by`. Establish `c₁ : o₁.eta a = u₁.ex _` using `OrthoMetric.pt_ext n₁.cart ((n₁.eta a).trans ((congrArg (fun q => q.left) ((hm a ha).trans (k₁ _).symm)).trans (f₁ _).symm))`. Establish `c₂ : o₂.eta a = u₂.ex _` using `OrthoMetric.pt_ext n₂.cart ((n₂.eta a).trans ((congrArg (fun q => q.left) ((hm' a ha).trans (k₂ _).symm)).trans (f₂ _).symm))`. Rewrite using `[c₁, c₂, hm₀])`. Use the proof step `(fun a => by`.

Establish `c₁` using `o₁.etaA_ker a`. Establish `c₂` using `o₂.etaA_ker a`. Rewrite `c₁`, `c₂` using `[hA, one_smul]`. Rewrite using `[c₁, c₂, ← CM.HermWeil.ex_zero u₁, ← CM.HermWeil.ex_zero u₂, hm₀])`. Take `⟨k', -⟩` from `((ObjMaps.id_comp_cancel E H Dw l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2 y'.x (𝟙 _) n₂).1 k`.

Rewrite `k'` using `[Category.id_comp]`. Conclude with `(moduli_rep_of_base ObjMaps.id_comp_cancel E H Dw l Xo ℂ (baseOfEmb σ) σ _ (𝟙 _) o₁ inferInstance`. Use `rfl rfl).unique ⟨hy', ⟨k'⟩⟩ ⟨hy, ⟨n₁⟩⟩`.
-/
theorem GlobalTheory.Dict.anFib_point_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ], l.A = 1 → ∀ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x L y'), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → A.Marked mk → A'.Marked mk → y'.x = y.x := by
  intro E _ _ _ H Dw l Xo c _ hA r g X bas idx e x L y y' A A' hs hx hL mk _ hm hm'
  obtain ⟨Φ, k₁, -, l₁, m₁, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  obtain ⟨Φ', k₂, -, l₂, m₂, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y' A' hs hx hL
  obtain ⟨-, pos, -⟩ := hx_laws E r X g bas idx 0 hs Even.zero x hx
  let σ : KA l →+* ℂ := (algebraMap c.F ℂ).comp (IntermediateField.inclusion c.le).toRingHom
  have hy : y.x ≫ Xo.s = 𝟙 _ ≫ spMap σ := y.x_over.trans (Category.id_comp _).symm
  have hy' : y'.x ≫ Xo.s = 𝟙 _ ≫ spMap σ := y'.x_over.trans (Category.id_comp _).symm
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H Dw l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) y.x rfl rfl hy Xo.univ
  obtain ⟨o₂, ⟨n₂⟩⟩ := obj_pull E H Dw l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) y'.x rfl rfl hy' Xo.univ
  obtain ⟨u₁, χ₁, b₁, f₁, h₁⟩ := exists_holUnif n₁.toSABMap Φ.toAnFr fun z hz => by rw [m₁]; exact pos z hz
  obtain ⟨u₂, χ₂, b₂, f₂, h₂⟩ := exists_holUnif n₂.toSABMap Φ'.toAnFr fun z hz => by rw [m₂]; exact pos z hz
  obtain ⟨m, hm₀⟩ := exists_sabMap_of_isAH o₁ o₂ u₁ u₂ h₁ h₂ (fun z => by rw [b₁, b₂, l₁, l₂])
    (fun z w => by rw [m₁, m₂]) (fun a => tyAct (fun j => rowType X (idx j)) a)
    (fun a z => OrthoMetric.pt_ext n₁.cart (by
      rw [f₁, Φ.lin, Over.comp_left, Over.comp_left, Category.assoc, n₁.act, ← Category.assoc, f₁]))
    (fun a z => OrthoMetric.pt_ext n₂.cart (by
      rw [f₂, Φ'.lin, Over.comp_left, Over.comp_left, Category.assoc, n₂.act, ← Category.assoc, f₂]))
  obtain ⟨k⟩ := exists_objMap o₁ o₂ m
    (fun a ha => by
      have c₁ : o₁.eta a = u₁.ex _ := OrthoMetric.pt_ext n₁.cart
        ((n₁.eta a).trans ((congrArg (fun q => q.left) ((hm a ha).trans (k₁ _).symm)).trans (f₁ _).symm))
      have c₂ : o₂.eta a = u₂.ex _ := OrthoMetric.pt_ext n₂.cart
        ((n₂.eta a).trans ((congrArg (fun q => q.left) ((hm' a ha).trans (k₂ _).symm)).trans (f₂ _).symm))
      rw [c₁, c₂, hm₀])
    (fun a => by
      have c₁ := o₁.etaA_ker a
      have c₂ := o₂.etaA_ker a
      rw [hA, one_smul] at c₁ c₂
      rw [c₁, c₂, ← CM.HermWeil.ex_zero u₁, ← CM.HermWeil.ex_zero u₂, hm₀])
  obtain ⟨k', -⟩ := ((ObjMaps.id_comp_cancel E H Dw l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2 y'.x (𝟙 _) n₂).1 k
  rw [Category.id_comp] at k'
  exact (moduli_rep_of_base ObjMaps.id_comp_cancel E H Dw l Xo ℂ (baseOfEmb σ) σ _ (𝟙 _) o₁ inferInstance
    rfl rfl).unique ⟨hy', ⟨k'⟩⟩ ⟨hy, ⟨n₁⟩⟩
