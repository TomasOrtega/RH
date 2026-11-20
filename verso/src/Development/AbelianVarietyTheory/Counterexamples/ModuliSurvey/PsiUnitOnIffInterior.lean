import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

noncomputable section
namespace GlobalTheory.DegActCheck
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {R : Type} [CommRing R] [IsDomain R]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h j V hV hU => h j V hV (hU.trans interior_subset), fun h j V hV hU => h j V hV (interior_maximal hU V.isOpen)⟩`.
-/
theorem psiUnitOn_iff_interior (D : Out.DegPre R) (χ : D.X) (U : Set (Sp R)) :
    PsiUnitOn D χ U ↔ PsiUnitOn D χ (interior U) :=
  ⟨fun h j V hV hU => h j V hV (hU.trans interior_subset),
   fun h j V hV hU => h j V hV (interior_maximal hU V.isOpen)⟩

/- English proof (translation)
Establish `h1` using `Over.w p.g.b`. Establish `h2` using `Over.w p'.g.b`. Rewrite `h2` using `[h.2.1]`. Establish `h3 : spMap f ≫ (Out.jFK (R` using `R) F ≫ Out.jK R) = Out.jFK (R := R) F' ≫ Out.jK R := by`. Use `Eq.trans ?_ h2` and prove the remaining obligations.

Use `Eq.trans ?_ (Category.assoc _ _ _).symm` and prove the remaining obligations. Conclude with `congrArg (spMap f ≫ ·) h1.symm`. Establish `h4 : CommRingCat.ofHom ((f.comp (algebraMap (FractionRing R) F)).comp (algebraMap R (FractionRing R))) = CommRingCat.ofHom ((algebraMap (FractionRing R) F').comp (algebraMap R (FractionRing R)))`. Apply `Spec.map_injective` to reduce the goal to its premises. Simplify using `only [CommRingCat.ofHom_comp, Spec.map_comp]`.

Conclude with `(Category.assoc _ _ _).trans h3`. Conclude with `IsLocalization.ringHom_ext (nonZeroDivisors R) (congrArg CommRingCat.Hom.hom h4)`.
-/
theorem qkExt_compat {D : Out.DegPre R} {F F' : Type} [Field F] [Algebra (FractionRing R) F]
    [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F') {k : ℕ} (p : Out.QkPt D F k)
    (p' : Out.QkPt D F' k) (h : QkExt f p p') :
    f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' := by
  have h1 := Over.w p.g.b
  have h2 := Over.w p'.g.b
  rw [h.2.1] at h2
  have h3 : spMap f ≫ (Out.jFK (R := R) F ≫ Out.jK R) = Out.jFK (R := R) F' ≫ Out.jK R := by
    refine Eq.trans ?_ h2
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    exact congrArg (spMap f ≫ ·) h1.symm
  have h4 : CommRingCat.ofHom ((f.comp (algebraMap (FractionRing R) F)).comp (algebraMap R (FractionRing R))) =
      CommRingCat.ofHom ((algebraMap (FractionRing R) F').comp (algebraMap R (FractionRing R))) := by
    apply Spec.map_injective
    simp only [CommRingCat.ofHom_comp, Spec.map_comp]
    exact (Category.assoc _ _ _).trans h3
  exact IsLocalization.ringHom_ext (nonZeroDivisors R) (congrArg CommRingCat.Hom.hom h4)

/- English proof (translation)
Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Establish `hsq : (H.bar H.rt) ^ 2 = H.rt ^ 2` using `by rw [← map_pow, H.rt_sq, map_neg, map_natCast]`. Establish `hne : H.bar H.rt ≠ H.rt`. Introduce `h`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`.

Establish `h1 : IsCMField.complexConj E (H.rt : E) = (H.rt : E)` using `by rw [← H.bar_eq, h]`. Establish `h2` using `IsCMField.complexEmbedding_complexConj E τ (H.rt : E)`. Rewrite `h2` using `[h1]`. Establish `h3 : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ)`. Use `congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq` as an intermediate fact.

Simplify using `using this`. Take `⟨r, hr⟩` from `Complex.conj_eq_iff_real.1 h2.symm`. Rewrite `h3` using `[hr]`. Establish `: r ^ 2 = -(H.d : ℝ)` using `by exact_mod_cast h3`. Use polynomial arithmetic with `[sq_nonneg r]`.

Establish `hb : H.bar H.rt = -H.rt` using `(sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left hne`. Establish `h2 : 2 * H.bar H.w0 = 1 - H.rt`. Use `congrArg H.bar H.two_weight_eq_one_add_root` as an intermediate fact. Rewrite `this` using `[map_mul, map_add, map_one, hb, map_ofNat]`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Establish `: (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1` using `by rw [mul_add, H.two_weight_eq_one_add_root, h2]; ring`. Conclude with `mul_left_cancel₀ two_ne_zero this`.
-/
theorem halfUnit_add_star {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 + H.bar H.w0 = 1 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hsq : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have hne : H.bar H.rt ≠ H.rt := by
    intro h
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h1 : IsCMField.complexConj E (H.rt : E) = (H.rt : E) := by rw [← H.bar_eq, h]
    have h2 := IsCMField.complexEmbedding_complexConj E τ (H.rt : E)
    rw [h1] at h2
    have h3 : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq
      simpa using this
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2.symm
    rw [hr] at h3
    have : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h3
    nlinarith [sq_nonneg r]
  have hb : H.bar H.rt = -H.rt := (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left hne
  have h2 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    rw [map_mul, map_add, map_one, hb, map_ofNat] at this
    rw [this]; ring
  have : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by rw [mul_add, H.two_weight_eq_one_add_root, h2]; ring
  exact mul_left_cancel₀ two_ne_zero this

section Sums
variable {O : Type} [CommRing O] [StarRing O] (D : Out.DegPre R) [Module O D.X] (oa : D.OAct O) (w : O) (y : D.X)

/- English proof (translation)
Use `show (toUnit (Out.TK R) ≫ D.c y).left ≫ _ = (toUnit (Out.TK R) ≫ D.c (w • y)).left`. Rewrite using `[oa.c_lin, ← Over.comp_left, Category.assoc]`.
-/
theorem pt_act : D.xK y ≫ (oa.onB.act w).left = D.xK (w • y) := by
  show (toUnit (Out.TK R) ≫ D.c y).left ≫ _ = (toUnit (Out.TK R) ≫ D.c (w • y)).left
  rw [oa.c_lin, ← Over.comp_left, Category.assoc]

/- English proof (translation)
Use `show (toUnit (Out.TK R) ≫ D.c y).left ≫ _ = (toUnit (Out.TK R) ≫ D.c (y + w • y)).left`. Rewrite using `[D.c_add, oa.c_lin, ← Over.comp_left]`. Use `congr 1`. Simplify using `only [padd, Category.assoc, comp_lift_assoc, Category.comp_id]`.
-/
theorem pt_sum : D.xK y ≫ (padd D.P.A (𝟙 _) (oa.onB.act w)).left = D.xK (y + w • y) := by
  show (toUnit (Out.TK R) ≫ D.c y).left ≫ _ = (toUnit (Out.TK R) ≫ D.c (y + w • y)).left
  rw [D.c_add, oa.c_lin, ← Over.comp_left]
  congr 1
  simp only [padd, Category.assoc, comp_lift_assoc, Category.comp_id]

/- English proof (translation)
Use `show (toUnit (Out.TK R) ≫ D.c y).left ≫ _ = (toUnit (Out.TK R)).left ≫ (η[D.P.A]).left`. Rewrite using `[← Over.comp_left, ← Over.comp_left, ← Category.assoc, comp_toUnit]`.
-/
theorem pt_zero : D.xK y ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (toUnit (Out.TK R)).left ≫ eSec D.P.A := by
  show (toUnit (Out.TK R) ≫ D.c y).left ≫ _ = (toUnit (Out.TK R)).left ≫ (η[D.P.A]).left
  rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc, comp_toUnit]

end Sums

end GlobalTheory.DegActCheck
