import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XMemOne
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

noncomputable section

namespace GlobalTheory.PD.XCover

/- English proof (translation)
Use `letI := ψ.toAlgebra`. Use `haveI : Module.Finite B A := hψ`. Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := B) (M := A)`. Set `M : Submodule F K` to `Submodule.span F (g '' (s : Set A))`. Establish `hMfg : M.FG` using `Submodule.fg_span (s.finite_toSet.image g)`.

Establish `hM : ∀ a : A, g a ∈ M`. Introduce `a`. Establish `ha : a ∈ Submodule.span B (s : Set A)` using `hs ▸ Submodule.mem_top`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `M.add_mem hx hy`. Consider the case `smul b x _ hx`. Take `⟨c, hc⟩` from `hB b`.

Rewrite using `[Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, ← hc, ← Algebra.smul_def]`. Conclude with `M.smul_mem c hx`. Set `R` to `Algebra.adjoin F (Set.range g)`. Establish `hRM : Subalgebra.toSubmodule R ≤ M`. Rewrite using `[Algebra.adjoin_eq_span]`.

Use `Submodule.span_le.2 fun x hx => ?_` and prove the remaining obligations. Establish `hx' : x ∈ g.range.toSubmonoid` using `(Submonoid.closure_le.2 (fun y hy => hy)) hx`. Take `⟨a, rfl⟩` from `hx'`. Conclude with `hM a`. Establish `hRfg : (Subalgebra.toSubmodule R).FG` using `by haveI : FiniteDimensional F M := Module.Finite.iff_fg.2 hMfg`.

Conclude with `isNoetherian_submodule.1 inferInstance _ hRM`. Establish `htop : ∀ z : K, z ∈ M`. Introduce `z`. Take `⟨a, b, hb, e⟩` from `hfr z`. Establish `hbR : g b ∈ R` using `Algebra.subset_adjoin ⟨b, rfl⟩`.

Establish `hint : IsIntegral F (g b)` using `IsIntegral.of_mem_of_fg R hRfg _ hbR`. Establish `hinv : (g b)⁻¹ ∈ R` using `Subalgebra.inv_mem_of_algebraic R (x := ⟨g b, hbR⟩) hint.isAlgebraic`. Establish `hz : z = g a * (g b)⁻¹` using `by rw [← e, mul_assoc, mul_inv_cancel₀ hb, mul_one]`. Rewrite using `[hz]`. Conclude with `hRM (R.mul_mem (Algebra.subset_adjoin ⟨a, rfl⟩) hinv)`.

Establish `: M = ⊤` using `eq_top_iff.2 fun z _ => htop z`. Conclude with `⟨this ▸ hMfg⟩`.
-/
theorem finiteDimensional_of_finite {A B F K : Type} [CommRing A] [CommRing B] [Field F] [Field K] [Algebra F K]
    (ψ : B →+* A) (hψ : ψ.Finite) (g : A →+* K) (hB : ∀ b, g (ψ b) ∈ Set.range (algebraMap F K))
    (hfr : ∀ x : K, ∃ a b : A, g b ≠ 0 ∧ x * g b = g a) : FiniteDimensional F K := by
  letI := ψ.toAlgebra
  haveI : Module.Finite B A := hψ
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := B) (M := A)
  let M : Submodule F K := Submodule.span F (g '' (s : Set A))
  have hMfg : M.FG := Submodule.fg_span (s.finite_toSet.image g)
  have hM : ∀ a : A, g a ∈ M := by
    intro a
    have ha : a ∈ Submodule.span B (s : Set A) := hs ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact M.add_mem hx hy
    | smul b x _ hx =>
      obtain ⟨c, hc⟩ := hB b
      rw [Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, ← hc, ← Algebra.smul_def]
      exact M.smul_mem c hx
  let R := Algebra.adjoin F (Set.range g)
  have hRM : Subalgebra.toSubmodule R ≤ M := by
    rw [Algebra.adjoin_eq_span]
    refine Submodule.span_le.2 fun x hx => ?_
    have hx' : x ∈ g.range.toSubmonoid := (Submonoid.closure_le.2 (fun y hy => hy)) hx
    obtain ⟨a, rfl⟩ := hx'
    exact hM a
  have hRfg : (Subalgebra.toSubmodule R).FG := by
    haveI : FiniteDimensional F M := Module.Finite.iff_fg.2 hMfg
    exact isNoetherian_submodule.1 inferInstance _ hRM
  have htop : ∀ z : K, z ∈ M := by
    intro z
    obtain ⟨a, b, hb, e⟩ := hfr z
    have hbR : g b ∈ R := Algebra.subset_adjoin ⟨b, rfl⟩
    have hint : IsIntegral F (g b) := IsIntegral.of_mem_of_fg R hRfg _ hbR
    have hinv : (g b)⁻¹ ∈ R := Subalgebra.inv_mem_of_algebraic R (x := ⟨g b, hbR⟩) hint.isAlgebraic
    have hz : z = g a * (g b)⁻¹ := by rw [← e, mul_assoc, mul_inv_cancel₀ hb, mul_one]
    rw [hz]
    exact hRM (R.mul_mem (Algebra.subset_adjoin ⟨a, rfl⟩) hinv)
  have : M = ⊤ := eq_top_iff.2 fun z _ => htop z
  exact ⟨this ▸ hMfg⟩

variable {d : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

/- English proof (translation)
Use `(GlobalTheory.ProjFrac.awayToSection_mk (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i) 1 _).trans ?_` and prove the remaining obligations. Conclude with `GlobalTheory.ProjFrac.frac_eq (by ring)`.
-/
theorem ratioSec_eq (i j : Fin (d + 1)) : ratioSec d i j = GlobalTheory.ProjSpace.ratio ℂ d i j := by
  refine (GlobalTheory.ProjFrac.awayToSection_mk (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i) 1 _).trans ?_
  exact GlobalTheory.ProjFrac.frac_eq (by ring)

/- English proof (translation)
Use `haveI : Nonempty U := ⟨⟨_, h⟩⟩`. Use `haveI := functionField_isFractionRing_of_isAffineOpen Z U hU`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := Γ(Z, U)) x`. Establish `hb' : algebraMap Γ(Z, U) Z.functionField b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb`. Conclude with `⟨a, b, hb', div_mul_cancel₀ _ hb'⟩`.
-/
theorem exists_frac_germ (Z : Scheme.{0}) [IsIntegral Z] (U : Z.Opens) (hU : IsAffineOpen U) (h : genericPoint Z ∈ U)
    (x : Z.functionField) : ∃ a b : Γ(Z, U), (Z.presheaf.germ U _ h).hom b ≠ 0 ∧
      x * (Z.presheaf.germ U _ h).hom b = (Z.presheaf.germ U _ h).hom a := by
  haveI : Nonempty U := ⟨⟨_, h⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen Z U hU
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Z, U)) x
  have hb' : algebraMap Γ(Z, U) Z.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  exact ⟨a, b, hb', div_mul_cancel₀ _ hb'⟩

/- English proof (translation)
Use `letI := ffAlg p`. Take `⟨P, rfl⟩` from `GlobalTheory.ProjSpace.aeval_ratio_surjective ℂ d 0 b`. Establish `e` using `congrArg (fun t => t P) (GlobalTheory.ProjSpace.appLE_comp_aeval_ratio (φ := φ) (W := φ ⁻¹ᵁ chart d 0) (i := 0) (hi := le_rfl))`. Simplify using `only [RingHom.comp_apply, RingHom.coe_coe] at e`. Rewrite using `[← Scheme.Hom.appLE_eq_app, e, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]`.

Use `MvPolynomial.eval₂_mem (fun _ _ => ?_) (fun j => ?_)` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, hp]`. Establish `hc : ∀ c : ℂ, (Z.presheaf.germ _ _ h).hom ((GlobalTheory.QCoh.Qcqs.baseRingHom p (φ ⁻¹ᵁ chart d 0)).hom c) = algebraMap ℂ Z.functionField c`. Introduce `c`. Rewrite using `[← GlobalTheory.QCoh.Qcqs.baseRingHom_res p (le_top : φ ⁻¹ᵁ chart d 0 ≤ ⊤), Z.presheaf.germ_res_apply, GlobalTheory.QCoh.Qcqs.baseRingHom_top]`.

Both sides reduce to the same expression. Rewrite using `[hc]`. Conclude with `IntermediateField.algebraMap_mem _ _`. Establish `hr : (Z.presheaf.germ _ _ h).hom (GlobalTheory.ProjSpace.pullRatio φ (φ ⁻¹ᵁ chart d 0) 0 le_rfl j) = rat φ 0 j`. Rewrite using `[rat, dif_pos h, ratioSec_eq, ← Scheme.Hom.appLE_eq_app]`.

Both sides reduce to the same expression. Simplify using `only [Function.comp_apply]`. Rewrite using `[hr]`. Conclude with `IntermediateField.subset_adjoin ℂ _ ⟨j, rfl⟩`.
-/
theorem germ_app_mem (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) (φ : Z ⟶ PSpace ℂ d)
    (hp : φ ≫ PSpace.str ℂ d = p) (h : genericPoint Z ∈ φ ⁻¹ᵁ chart d 0) (b : Γ(PSpace ℂ d, chart d 0)) :
    letI := ffAlg p
    (Z.presheaf.germ _ _ h).hom ((φ.app (chart d 0)).hom b) ∈ fld φ := by
  letI := ffAlg p
  obtain ⟨P, rfl⟩ := GlobalTheory.ProjSpace.aeval_ratio_surjective ℂ d 0 b
  have e := congrArg (fun t => t P) (GlobalTheory.ProjSpace.appLE_comp_aeval_ratio (φ := φ) (W := φ ⁻¹ᵁ chart d 0) (i := 0) (hi := le_rfl))
  simp only [RingHom.comp_apply, RingHom.coe_coe] at e
  rw [← Scheme.Hom.appLE_eq_app, e, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
  refine MvPolynomial.eval₂_mem (fun _ _ => ?_) (fun j => ?_)
  · rw [RingHom.comp_apply, hp]
    have hc : ∀ c : ℂ, (Z.presheaf.germ _ _ h).hom ((GlobalTheory.QCoh.Qcqs.baseRingHom p (φ ⁻¹ᵁ chart d 0)).hom c) =
        algebraMap ℂ Z.functionField c := by
      intro c
      rw [← GlobalTheory.QCoh.Qcqs.baseRingHom_res p (le_top : φ ⁻¹ᵁ chart d 0 ≤ ⊤), Z.presheaf.germ_res_apply,
        GlobalTheory.QCoh.Qcqs.baseRingHom_top]
      rfl
    rw [hc]
    exact IntermediateField.algebraMap_mem _ _
  · have hr : (Z.presheaf.germ _ _ h).hom (GlobalTheory.ProjSpace.pullRatio φ (φ ⁻¹ᵁ chart d 0) 0 le_rfl j) = rat φ 0 j := by
      rw [rat, dif_pos h, ratioSec_eq, ← Scheme.Hom.appLE_eq_app]
      rfl
    simp only [Function.comp_apply]
    rw [hr]
    exact IntermediateField.subset_adjoin ℂ _ ⟨j, rfl⟩

/- English proof (translation)
Introduce `d Z _ p _ inst hinst φ _ hp hgen`. Substitute `hinst` using the available equality. Establish `hC : IsAffineOpen (chart d 0)` using `GlobalTheory.ProjSpace.isAffineOpen_chart ℂ d 0`. Establish `hU : IsAffineOpen (φ ⁻¹ᵁ chart d 0)` using `hC.preimage φ`. Conclude with `finiteDimensional_of_finite (φ.app (chart d 0)).hom (φ.finite_app _ hC) (Z.presheaf.germ _ _ (hgen 0)).hom (fun b => ⟨⟨_, germ_app_mem Z p φ hp (hgen 0) b⟩, rfl⟩) (exists_frac_germ Z _ hU (hgen 0))`.
-/
theorem finiteDimensional_fld : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p]
    [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p →
    (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → FiniteDimensional (fld φ) Z.functionField := by
  intro d Z _ p _ inst hinst φ _ hp hgen
  subst hinst
  have hC : IsAffineOpen (chart d 0) := GlobalTheory.ProjSpace.isAffineOpen_chart ℂ d 0
  have hU : IsAffineOpen (φ ⁻¹ᵁ chart d 0) := hC.preimage φ
  exact finiteDimensional_of_finite (φ.app (chart d 0)).hom (φ.finite_app _ hC) (Z.presheaf.germ _ _ (hgen 0)).hom
    (fun b => ⟨⟨_, germ_app_mem Z p φ hp (hgen 0) b⟩, rfl⟩) (exists_frac_germ Z _ hU (hgen 0))

end GlobalTheory.PD.XCover
