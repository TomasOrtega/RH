import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValSectionUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.E8Ring
open GlobalTheory.Mum.UnitValuedLeadingSection

noncomputable section

namespace GlobalTheory.Mum.UnitValuedLeadingSection

/- English proof (translation)
The claim follows from `Over.w s`.
-/
theorem left_comp_hom_unit {R : Type} [CommRing R] {B : Over (Spec (CommRingCat.of R))}
    (s : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) : s.left ≫ B.hom = 𝟙 _ :=
  Over.w s

/- English proof (translation)
The claim follows from `Over.w (toUnit (TK R))`.
-/
theorem toUnit_TK_left (R : Type) [CommRing R] [IsDomain R] : (toUnit (TK R)).left = jK R :=
  Over.w (toUnit (TK R))

/- English proof (translation)
Establish `hG` using `hJ.1`. Use `set P : D.X → ((TK R).left.presheaf.stalk z)ˣ := fun χ => val (D.psi χ) (𝟙 _) z J with hPdef`. Establish `hP : ∀ χ, val (D.psi χ) (𝟙 _) z J = P χ` using `fun _ => rfl`. Use `set rg := val D.rigK (𝟙 _) z J with hrgdef`. Establish `h1 : ∀ a b, val (D.tau a b) (𝟙 _) z J = P (a + b) * (P a)⁻¹ * (P b)⁻¹ * rg⁻¹`.

Introduce `a b`. Unfold `DegPre.tau`. Rewrite using `[val_mul hG, val_mul hG, val_mul hG, val_inv, val_inv, val_inv]`. Choose the witnesses or unpack the hypotheses as in `⟨r, hr⟩ : ∃ u : Rˣ, rg = uK R z u := by`. Rewrite using `[hrgdef]`.

Unfold `DegPre.rigK`. Rewrite using `[val_pull hG, Category.id_comp, toUnit_TK_left]`. Establish `e : jK R = jK R ≫ (𝟙 (Spec (CommRingCat.of R)) : Spec (CommRingCat.of R) ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left)` using `(Category.comp_id _).symm`. Rewrite using `[e]`. Conclude with `val_section_unit D.P z J hJ D.rig _ (fun _ => by`.

Rewrite using `[Category.id_comp]`. Conclude with `left_comp_hom_unit (η[D.P.A]))`. Use `set C : D.X → D.X → D.X → ((TK R).left.presheaf.stalk z)ˣ := fun a a' b => val D.cub.t (D.pt3 a a' b) z J with hCdef`. Establish `h2 : ∀ a a' b, val (D.tau (a + a') b) (𝟙 _) z J * C a a' b = val (D.tau a b) (𝟙 _) z J * val (D.tau a' b) (𝟙 _) z J`. Introduce `a a' b`.

Use `(val_mul hG _ _ _).symm.trans ((val_corr hG (hT a a' b) (𝟙 _)).trans (val_mul hG _ _ _))` as an intermediate fact. Establish `hp : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J = C a a' b` using `(val_pull hG D.cub.t (D.pt3 a a' b) (𝟙 _)).trans (by rw [Category.id_comp])`. Conclude with `(congrArg (fun x => val (D.tau (a + a') b) (𝟙 _) z J * x) hp).symm.trans this`. Establish `hC : ∀ a a' b, ∃ u : Rˣ, C a a' b = uK R z u`. Introduce `a a' b`.

Establish `e : D.pt3 a a' b = jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left`. Unfold `DegPre.pt3`. Rewrite using `[← comp_lift, ← comp_lift, Over.comp_left, toUnit_TK_left]`. Use `show ∃ u : Rˣ, val D.cub.t (D.pt3 a a' b) z J = uK R z u`. Rewrite using `[e]`.

Conclude with `val_section_unit D.P z J hJ D.cub.t _ (fun k => by`. Rewrite using `[← Over.comp_left]`. Conclude with `left_comp_hom_unit _)`. Use `set S : D.X → ((TK R).left.presheaf.stalk z)ˣ := fun χ => val D.sym (D.xK χ) z J with hSdef`. Establish `h3 : ∀ χ, P (-χ) * S χ = P χ`.

Introduce `χ`. Use `(val_mul hG _ _ _).symm.trans (val_corr hG (hE χ) (𝟙 _))` as an intermediate fact. Rewrite `this` using `[val_pull hG, Category.id_comp]`. Conclude with `this`. Establish `hS : ∀ χ, ∃ u : Rˣ, S χ = uK R z u`.

Introduce `χ`. Establish `e : D.xK χ = jK R ≫ (D.c χ).left` using `by show (toUnit (TK R) ≫ D.c χ).left = _`. Rewrite using `[Over.comp_left, toUnit_TK_left]`. Use `show ∃ u : Rˣ, val D.sym (D.xK χ) z J = uK R z u`. Rewrite using `[e]`.

Use `val_section_unit D.P z J hJ D.sym _ (fun k => ?_)` and prove the remaining obligations. Use `fin_cases k`. Use `show ((D.c χ).left ≫ (ι[D.P.A]).left) ≫ D.P.A.hom = 𝟙 _`. Rewrite using `[← Over.comp_left]`. Conclude with `left_comp_hom_unit _`.

Use `show ((D.c χ).left ≫ 𝟙 D.P.A.left) ≫ D.P.A.hom = 𝟙 _`. Rewrite using `[Category.comp_id]`. Conclude with `left_comp_hom_unit _`. Take `⟨c0, hc0⟩` from `hC 0 0 0`. Take `⟨c1, hc1⟩` from `hC y (-y) y`.

Take `⟨s, hs⟩` from `hS y`. Establish `e0` using `h2 0 0 0`. Simplify using `only [h1, add_zero] at e0`. Establish `hP0 : P 0 = (C 0 0 0 * rg)⁻¹`. Establish `: C 0 0 0 = P 0 * (P 0)⁻¹ * (P 0)⁻¹ * rg⁻¹` using `mul_left_cancel e0`.

Rewrite using `[this]`. Use `group`. Establish `e1` using `h2 y (-y) y`. Simplify using `only [h1, add_neg_cancel, zero_add, neg_add_cancel] at e1`. Establish `hPm : P (-y) = P y * (S y)⁻¹` using `by rw [← h3 y]; group`.

Rewrite `e1` using `[hPm, hP0]`. Use `⟨(c0 * r) ^ 2 * c1 * s⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, map_mul, map_mul, map_inv, map_pow, map_mul, ← hc0, ← hc1, ← hs, ← hr, hP y]`. Rewrite using `[eq_mul_inv_of_mul_eq e1.symm]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_inv, ofMul_pow]`. Normalize the expressions using the abelian group laws.
-/
theorem tau_diag_eq_unit_mul_psi_sq (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R)
    (hT : D.TauBimult) (hE : D.PsiEven) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι)
    (hJ : TopGood D.P z J) (y : D.X) :
    ∃ u : Rˣ, val (D.tau y y) (𝟙 _) z J = uK R z u * val (D.psi y) (𝟙 _) z J ^ 2 := by
  have hG := hJ.1
  set P : D.X → ((TK R).left.presheaf.stalk z)ˣ := fun χ => val (D.psi χ) (𝟙 _) z J with hPdef
  have hP : ∀ χ, val (D.psi χ) (𝟙 _) z J = P χ := fun _ => rfl
  set rg := val D.rigK (𝟙 _) z J with hrgdef

  have h1 : ∀ a b, val (D.tau a b) (𝟙 _) z J = P (a + b) * (P a)⁻¹ * (P b)⁻¹ * rg⁻¹ := by
    intro a b
    unfold DegPre.tau
    rw [val_mul hG, val_mul hG, val_mul hG, val_inv, val_inv, val_inv]

  obtain ⟨r, hr⟩ : ∃ u : Rˣ, rg = uK R z u := by
    rw [hrgdef]
    unfold DegPre.rigK
    rw [val_pull hG, Category.id_comp, toUnit_TK_left]
    have e : jK R = jK R ≫ (𝟙 (Spec (CommRingCat.of R)) : Spec (CommRingCat.of R) ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left) :=
      (Category.comp_id _).symm
    rw [e]
    exact val_section_unit D.P z J hJ D.rig _ (fun _ => by
      rw [Category.id_comp]; exact left_comp_hom_unit (η[D.P.A]))

  set C : D.X → D.X → D.X → ((TK R).left.presheaf.stalk z)ˣ :=
    fun a a' b => val D.cub.t (D.pt3 a a' b) z J with hCdef
  have h2 : ∀ a a' b, val (D.tau (a + a') b) (𝟙 _) z J * C a a' b =
      val (D.tau a b) (𝟙 _) z J * val (D.tau a' b) (𝟙 _) z J := by
    intro a a' b
    have := (val_mul hG _ _ _).symm.trans ((val_corr hG (hT a a' b) (𝟙 _)).trans (val_mul hG _ _ _))
    have hp : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J = C a a' b :=
      (val_pull hG D.cub.t (D.pt3 a a' b) (𝟙 _)).trans (by rw [Category.id_comp])
    exact (congrArg (fun x => val (D.tau (a + a') b) (𝟙 _) z J * x) hp).symm.trans this
  have hC : ∀ a a' b, ∃ u : Rˣ, C a a' b = uK R z u := by
    intro a a' b
    have e : D.pt3 a a' b = jK R ≫ (lift (D.c a) (lift (D.c a') (D.c b))).left := by
      unfold DegPre.pt3
      rw [← comp_lift, ← comp_lift, Over.comp_left, toUnit_TK_left]
    show ∃ u : Rˣ, val D.cub.t (D.pt3 a a' b) z J = uK R z u
    rw [e]
    exact val_section_unit D.P z J hJ D.cub.t _ (fun k => by
      rw [← Over.comp_left]; exact left_comp_hom_unit _)

  set S : D.X → ((TK R).left.presheaf.stalk z)ˣ :=
    fun χ => val D.sym (D.xK χ) z J with hSdef
  have h3 : ∀ χ, P (-χ) * S χ = P χ := by
    intro χ
    have := (val_mul hG _ _ _).symm.trans (val_corr hG (hE χ) (𝟙 _))
    rw [val_pull hG, Category.id_comp] at this
    exact this
  have hS : ∀ χ, ∃ u : Rˣ, S χ = uK R z u := by
    intro χ
    have e : D.xK χ = jK R ≫ (D.c χ).left := by
      show (toUnit (TK R) ≫ D.c χ).left = _
      rw [Over.comp_left, toUnit_TK_left]
    show ∃ u : Rˣ, val D.sym (D.xK χ) z J = uK R z u
    rw [e]
    refine val_section_unit D.P z J hJ D.sym _ (fun k => ?_)
    fin_cases k
    · show ((D.c χ).left ≫ (ι[D.P.A]).left) ≫ D.P.A.hom = 𝟙 _
      rw [← Over.comp_left]; exact left_comp_hom_unit _
    · show ((D.c χ).left ≫ 𝟙 D.P.A.left) ≫ D.P.A.hom = 𝟙 _
      rw [Category.comp_id]; exact left_comp_hom_unit _

  obtain ⟨c0, hc0⟩ := hC 0 0 0
  obtain ⟨c1, hc1⟩ := hC y (-y) y
  obtain ⟨s, hs⟩ := hS y
  have e0 := h2 0 0 0
  simp only [h1, add_zero] at e0

  have hP0 : P 0 = (C 0 0 0 * rg)⁻¹ := by
    have : C 0 0 0 = P 0 * (P 0)⁻¹ * (P 0)⁻¹ * rg⁻¹ := mul_left_cancel e0
    rw [this]; group
  have e1 := h2 y (-y) y
  simp only [h1, add_neg_cancel, zero_add, neg_add_cancel] at e1
  have hPm : P (-y) = P y * (S y)⁻¹ := by rw [← h3 y]; group
  rw [hPm, hP0] at e1
  refine ⟨(c0 * r) ^ 2 * c1 * s⁻¹, ?_⟩
  rw [h1, map_mul, map_mul, map_inv, map_pow, map_mul, ← hc0, ← hc1, ← hs, ← hr, hP y]

  rw [eq_mul_inv_of_mul_eq e1.symm]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

end GlobalTheory.Mum.UnitValuedLeadingSection
