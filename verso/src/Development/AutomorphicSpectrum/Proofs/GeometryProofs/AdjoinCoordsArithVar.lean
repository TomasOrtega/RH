import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ZarhinBundleKernelFirstCoordEquations
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectivePointImageReducedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StandardSmoothBasicOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LiftGenericPointOverIsoOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectivePointCoordsExistStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularValuesInAdjoinedFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreProductAffineChartStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartOfSmoothCoordsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStandardSmoothLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StandardSmoothChartOfNonzeroStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomogeneousFormNonvanishingPointStatement

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.CompanionTheory.Ar.SncRes
variable {Ω : Type} [Field Ω] [CharZero Ω]

/- English proof (translation)
The claim follows from `GlobalTheory.T.projective_point_image_reduced Ω N x hx`.
-/
theorem closure_facts {N : ℕ} (x : Fin (N + 1) → Ω) (hx : x ≠ 0) :
    IsReduced (point ℚ x hx).image ∧ IsDominant (point ℚ x hx).toImage :=
  GlobalTheory.T.projective_point_image_reduced Ω N x hx

/- English proof (translation)
The claim follows from `GlobalTheory.T.standard_smooth_basic_open Ω Z ζ g e W hW h A hA σ g₀ hg`.
-/
theorem smooth_basicOpen {Z : Scheme.{0}} (ζ : Sp Ω ⟶ Z) [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ)
    (e : ℕ) {W : Z.Opens} (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω)
    (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W)) (g₀ : A) (hg : (g₀ : Ω) = valR ζ W σ)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀)] :
    SmoothOfRelativeDimension e ((Z.basicOpen σ).ι ≫ g) :=
  GlobalTheory.T.standard_smooth_basic_open Ω Z ζ g e W hW h A hA σ g₀ hg

/- English proof (translation)
The claim follows from `GlobalTheory.T.lift_generic_point_over_iso_open Ω X X' ξ f U hd hU`.
-/
theorem lift_generic {X X' : Scheme.{0}} (ξ : Sp Ω ⟶ X) [IsDominant ξ] (f : X' ⟶ X) (U : X.Opens)
    [IsIso (f ∣_ U)] (hd : Dense ((f ⁻¹ᵁ U : X'.Opens) : Set X')) (hU : ⊤ ≤ ξ ⁻¹ᵁ U) :
    ∃ ζ : Sp Ω ⟶ X', ζ ≫ f = ξ ∧ IsDominant ζ ∧ ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U) :=
  GlobalTheory.T.lift_generic_point_over_iso_open Ω X X' ξ f U hd hU

/- English proof (translation)
The claim follows from `GlobalTheory.T.projective_point_coords_exist Ω r p`.
-/
theorem exists_coords {r : ℕ} (p : Sp Ω ⟶ PSpace ℚ r) : ∃ (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0), p = point ℚ x' hx' :=
  GlobalTheory.T.projective_point_coords_exist Ω r p

/- English proof (translation)
The claim follows from `GlobalTheory.T.regular_values_in_adjoined_field Ω X X' ξ f U ζ hζ hU W₀ hW₀ h₀ A hA W' h' s`.
-/
theorem val_mem_field {X X' : Scheme.{0}} (ξ : Sp Ω ⟶ X) [IsDominant ξ] [IsReduced X] (f : X' ⟶ X) (U : X.Opens)
    [IsIso (f ∣_ U)] (ζ : Sp Ω ⟶ X') (hζ : ζ ≫ f = ξ) (hU : ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U)) {W₀ : X.Opens}
    (hW₀ : IsAffineOpen W₀) (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ξ W₀ h₀).hom = A)
    (W' : X'.Opens) (h' : ⊤ ≤ ζ ⁻¹ᵁ W') (s : Γ(X', W')) :
    valR ζ W' s ∈ IntermediateField.adjoin ℚ (A : Set Ω) :=
  GlobalTheory.T.regular_values_in_adjoined_field Ω X X' ξ f U ζ hζ hU W₀ hW₀ h₀ A hA W' h' s

/- English proof (translation)
The claim follows from `GlobalTheory.T.segre_product_affine_chart Ω N r Z j ζ x hx x' hx' h₁ h₂ a l ha hl`.
-/
theorem prod_chart {N r : ℕ} {Z : Scheme.{0}} (j : Z ⟶ pullback (PSpace.str ℚ N) (PSpace.str ℚ r))
    [IsClosedImmersion j] (ζ : Sp Ω ⟶ Z) (x : Fin (N + 1) → Ω) (hx : x ≠ 0) (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0)
    (h₁ : ζ ≫ j ≫ pullback.fst _ _ = point ℚ x hx) (h₂ : ζ ≫ j ≫ pullback.snd _ _ = point ℚ x' hx')
    (a : Fin (N + 1)) (l : Fin (r + 1)) (ha : x a ≠ 0) (hl : x' l ≠ 0) :
    IsAffineOpen ((j ≫ pullback.fst _ _) ⁻¹ᵁ chart ℚ N a ⊓ (j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l) ∧
      ∃ h : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.fst _ _) ⁻¹ᵁ chart ℚ N a ⊓ (j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l),
        Set.range (valMap ζ _ h).hom =
          Algebra.adjoin ℚ (Set.range (fun k => x k / x a) ∪ Set.range (fun k => x' k / x' l)) :=
  GlobalTheory.T.segre_product_affine_chart Ω N r Z j ζ x hx x' hx' h₁ h₂ a l ha hl

/- English proof (translation)
The claim follows from `GlobalTheory.T.snc_chart_of_smooth_coords Ω Z ζ g e T hsm hc W hW h A hA σ hσ`.
-/
theorem snc_transfer {Z : Scheme.{0}} (ζ : Sp Ω ⟶ Z) [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ) (e : ℕ) (T : Set Z)
    (hsm : SmoothOfRelativeDimension e g) (hc : HasSncCoords g e T) {W : Z.Opens} (hW : IsAffineOpen W)
    (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W))
    (hσ : ∀ t ∈ W, t ∈ T ↔ t ∉ Z.basicOpen σ) : SncChart A e (valR ζ W σ) :=
  GlobalTheory.T.snc_chart_of_smooth_coords Ω Z ζ g e T hsm hc W hW h A hA σ hσ

/- English proof (translation)
Use `⟨(u.appLE _ W hi).hom (formOn (chart ℚ N a) a le_rfl n G hG), ?_, ?_⟩` and prove the remaining obligations. Establish `ha : x a ≠ 0` using `ne_zero_of_le hu hW hi`. Establish `h : ⊤ ≤ point ℚ x hx ⁻¹ᵁ chart ℚ N a` using `(le_point_preimage_iff a).2 ha`. Rewrite using `[valR_appLE η u hi hW, hu, formOn_eq_aeval, valR_eq _ _ h]`. Conclude with `(valMap_eval₂Hom point_str h _ G).trans (by simp only [valR_point_ratio ha])`.

Rewrite using `[Scheme.basicOpen_appLE, basicOpen_formOn]`. Use `le_antisymm (le_inf inf_le_left (inf_le_right.trans (u.preimage_mono inf_le_right))) (le_inf inf_le_left ?_)` and prove the remaining obligations. Introduce and unpack `t ⟨h1, h2⟩`. Conclude with `⟨hi h1, h2⟩`.
-/
theorem form_section {N : ℕ} {Z : Scheme.{0}} (u : Z ⟶ PSpace ℚ N) (η : Sp Ω ⟶ Z) (x : Fin (N + 1) → Ω) (hx : x ≠ 0)
    (hu : η ≫ u = point ℚ x hx) {W : Z.Opens} (hW : ⊤ ≤ η ⁻¹ᵁ W) {a : Fin (N + 1)} (hi : W ≤ u ⁻¹ᵁ chart ℚ N a)
    {n : ℕ} {G : MvPolynomial (Fin (N + 1)) ℚ} (hG : G.IsHomogeneous n) :
    ∃ σ : Γ(Z, W), valR η W σ = aeval (fun j => x j / x a) G ∧
      Z.basicOpen σ = W ⊓ u ⁻¹ᵁ Proj.basicOpen (grading ℚ N) G := by
  refine ⟨(u.appLE _ W hi).hom (formOn (chart ℚ N a) a le_rfl n G hG), ?_, ?_⟩
  · have ha : x a ≠ 0 := ne_zero_of_le hu hW hi
    have h : ⊤ ≤ point ℚ x hx ⁻¹ᵁ chart ℚ N a := (le_point_preimage_iff a).2 ha
    rw [valR_appLE η u hi hW, hu, formOn_eq_aeval, valR_eq _ _ h]
    exact (valMap_eval₂Hom point_str h _ G).trans (by simp only [valR_point_ratio ha])
  · rw [Scheme.basicOpen_appLE, basicOpen_formOn]
    refine le_antisymm (le_inf inf_le_left (inf_le_right.trans (u.preimage_mono inf_le_right)))
      (le_inf inf_le_left ?_)
    rintro t ⟨h1, h2⟩
    exact ⟨hi h1, h2⟩

/- English proof (translation)
Establish `hc` using `(isAffineOpen_chart ℚ N a)`. Use `⟨hc.preimage i, le_preimage_chart hi ha, ?_⟩` and prove the remaining obligations. Establish `h₁ : ⊤ ≤ point ℚ x hx ⁻¹ᵁ chart ℚ N a` using `(le_point_preimage_iff a).2 ha`. Rewrite using `[← range_valMap_point h₁, ← (i.app_surjective _ hc).range_comp]`. Use `congr 1`.

Use function extensionality and compare the values at `s`. Use `valR_comp ζ i (chart ℚ N a) s` as an intermediate fact. Rewrite `this` using `[hi, valR_eq _ _ h₁, valR_eq _ _ (le_preimage_chart hi ha)]`. Conclude with `this.symm`.
-/
theorem chart_single {N : ℕ} {Z : Scheme.{0}} (i : Z ⟶ PSpace ℚ N) [IsClosedImmersion i] (ζ : Sp Ω ⟶ Z)
    (x : Fin (N + 1) → Ω) (hx : x ≠ 0) (hi : ζ ≫ i = point ℚ x hx) (a : Fin (N + 1)) (ha : x a ≠ 0) :
    IsAffineOpen (i ⁻¹ᵁ chart ℚ N a) ∧ ∃ h : ⊤ ≤ ζ ⁻¹ᵁ (i ⁻¹ᵁ chart ℚ N a),
      Set.range (valMap ζ _ h).hom = Algebra.adjoin ℚ (Set.range fun k => x k / x a) := by
  have hc := (isAffineOpen_chart ℚ N a)
  refine ⟨hc.preimage i, le_preimage_chart hi ha, ?_⟩
  have h₁ : ⊤ ≤ point ℚ x hx ⁻¹ᵁ chart ℚ N a := (le_point_preimage_iff a).2 ha
  rw [← range_valMap_point h₁, ← (i.app_surjective _ hc).range_comp]
  congr 1
  funext s
  have := valR_comp ζ i (chart ℚ N a) s
  rw [hi, valR_eq _ _ h₁, valR_eq _ _ (le_preimage_chart hi ha)] at this
  exact this.symm

/- English proof (translation)
Establish `hx : x ≠ 0` using `fun h => hc₀ (by simp [h])`. Take `⟨hred, hdom⟩` from `closure_facts x hx`. Use `set p := point ℚ x hx with hp`. Establish `hπ : p.toImage ≫ p.imageι = point ℚ x hx` using `Scheme.Hom.toImage_imageι p`. Take `⟨hW₀, h₀, hA₀⟩` from `chart_single p.imageι p.toImage x hx hπ c₀ hc₀`.

Take `⟨σ₀, hσ₀, hb₀⟩` from `form_section p.imageι p.toImage x hx hπ h₀ le_rfl hG`. Establish `hsub : Proj.basicOpen (grading ℚ N) G ≤ chart ℚ N c₀`. Take `⟨G', rfl⟩` from `hdiv`. Rewrite using `[Proj.basicOpen_mul]`. Conclude with `inf_le_left`.

Use `set U : (p.image).Opens := p.imageι ⁻¹ᵁ Proj.basicOpen (grading ℚ N) G with hUdef`. Establish `hUb : p.image.basicOpen σ₀ = U`. Rewrite using `[hb₀]`. Conclude with `inf_eq_right.2 (p.imageι.preimage_mono hsub)`. Establish `hval : valR p.toImage _ σ₀ = g₀` using `by rw [hσ₀, hg₀]`.

Establish `hUtop : ⊤ ≤ p.toImage ⁻¹ᵁ U`. Rewrite using `[← hUb, le_preimage_basicOpen_iff _ h₀, hval]`. Conclude with `isUnit_iff_ne_zero.2 (by simpa using h0)`. Establish `hsmU : SmoothOfRelativeDimension e (U.ι ≫ p.imageι ≫ PSpace.str ℚ N)`. Use `smooth_basicOpen p.toImage (p.imageι ≫ PSpace.str ℚ N) e hW₀ h₀ _ hA₀ σ₀ g₀ hval.symm` as an intermediate fact.

Rewrite `this` using `[hUb]`. Then use the resulting hypothesis. Establish `hdense : Dense (U : Set p.image)`. Use `p.toImage.denseRange.mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `hUtop (Set.mem_univ y)`.

Take `⟨r, X', j, f, hj, hf, hsm, hiso, hd, hco⟩` from `hR ℚ N e p.image p.imageι U ⟨inferInstance, hred, hdense, hsmU⟩`. Take `⟨ζ, hζ, hdomζ, hζU⟩` from `lift_generic p.toImage f U hd hUtop`. Take `⟨x', hx', hp₂⟩` from `exists_coords (ζ ≫ j ≫ pullback.snd _ _)`. Establish `hp₁ : ζ ≫ j ≫ pullback.fst _ _ = point ℚ x hx`. Rewrite using `[← hf, reassoc_of% hζ, hπ]`.

Establish `: Smooth (f ≫ p.imageι ≫ PSpace.str ℚ N)` using `hsm.smooth`. Establish `hredX' : IsReduced X'` using `GlobalTheory.isReduced_of_smooth_of_isReduced (f ≫ p.imageι ≫ PSpace.str ℚ N)`. Use `⟨r, x', hx', fun i l hl => ?_, fun a l ha hl => ?_⟩` and prove the remaining obligations. Establish `hW : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l)` using `le_preimage_chart (by simpa using hp₂) hl`. Use `val_mem_field p.toImage f U ζ hζ hζU hW₀ h₀ _ hA₀ _ hW (pullRatio (j ≫ pullback.snd _ _) _ l le_rfl i)` as an intermediate fact.

Rewrite `this` using `[valR_pullRatio (by simpa using hp₂) hW]`. Then use the resulting hypothesis. Take `⟨hWa, hW, hAW⟩` from `prod_chart j ζ x hx x' hx' hp₁ hp₂ a l ha hl`. Take `⟨σ, hσ, hb⟩` from `form_section (j ≫ pullback.fst _ _) ζ x hx (by simpa using hp₁) hW inf_le_left hG`. Rewrite using `[← hσ]`. Use `snc_transfer ζ (f ≫ p.imageι ≫ PSpace.str ℚ N) e _ hsm hco hWa hW _ hAW σ fun t ht => ?_` and prove the remaining obligations.

Rewrite using `[hb]`. Establish `e₁ : (j ≫ pullback.fst _ _) t = p.imageι (f t)`. Rewrite using `[← hf]`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `h ⟨-, h2⟩`. Conclude with `h (show p.imageι (f t) ∈ Proj.basicOpen (grading ℚ N) G from e₁ ▸ h2)`. Introduce `h h2`. Conclude with `h ⟨ht, show (j ≫ pullback.fst _ _) t ∈ Proj.basicOpen (grading ℚ N) G from e₁ ▸ h2⟩`.
-/
theorem snc_of_res (hR : ResKStatement) (N e d : ℕ) (x : Fin (N + 1) → Ω) (c₀ : Fin (N + 1)) (hc₀ : x c₀ ≠ 0)
    (G : MvPolynomial (Fin (N + 1)) ℚ) (hG : G.IsHomogeneous (d + 1)) (hdiv : (X c₀ : MvPolynomial _ ℚ) ∣ G)
    (g₀ : Algebra.adjoin ℚ (Set.range fun j => x j / x c₀))
    (hg₀ : (g₀ : Ω) = aeval (fun j => x j / x c₀) G) (h0 : g₀ ≠ 0)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀)] :
    ∃ (r : ℕ) (x' : Fin (r + 1) → Ω), x' ≠ 0 ∧
      (∀ i l, x' l ≠ 0 → x' i / x' l ∈
        IntermediateField.adjoin ℚ ((Algebra.adjoin ℚ (Set.range fun j => x j / x c₀) : Subalgebra ℚ Ω) : Set Ω)) ∧
      ∀ a l, x a ≠ 0 → x' l ≠ 0 →
        SncChart (Algebra.adjoin ℚ (Set.range (fun k => x k / x a) ∪ Set.range (fun k => x' k / x' l))) e
          (aeval (fun j => x j / x a) G) := by
  have hx : x ≠ 0 := fun h => hc₀ (by simp [h])
  obtain ⟨hred, hdom⟩ := closure_facts x hx
  set p := point ℚ x hx with hp
  have hπ : p.toImage ≫ p.imageι = point ℚ x hx := Scheme.Hom.toImage_imageι p
  obtain ⟨hW₀, h₀, hA₀⟩ := chart_single p.imageι p.toImage x hx hπ c₀ hc₀
  obtain ⟨σ₀, hσ₀, hb₀⟩ := form_section p.imageι p.toImage x hx hπ h₀ le_rfl hG
  have hsub : Proj.basicOpen (grading ℚ N) G ≤ chart ℚ N c₀ := by
    obtain ⟨G', rfl⟩ := hdiv
    rw [Proj.basicOpen_mul]
    exact inf_le_left
  set U : (p.image).Opens := p.imageι ⁻¹ᵁ Proj.basicOpen (grading ℚ N) G with hUdef
  have hUb : p.image.basicOpen σ₀ = U := by
    rw [hb₀]
    exact inf_eq_right.2 (p.imageι.preimage_mono hsub)
  have hval : valR p.toImage _ σ₀ = g₀ := by rw [hσ₀, hg₀]
  have hUtop : ⊤ ≤ p.toImage ⁻¹ᵁ U := by
    rw [← hUb, le_preimage_basicOpen_iff _ h₀, hval]
    exact isUnit_iff_ne_zero.2 (by simpa using h0)
  have hsmU : SmoothOfRelativeDimension e (U.ι ≫ p.imageι ≫ PSpace.str ℚ N) := by
    have := smooth_basicOpen p.toImage (p.imageι ≫ PSpace.str ℚ N) e hW₀ h₀ _ hA₀ σ₀ g₀ hval.symm
    rwa [hUb] at this
  have hdense : Dense (U : Set p.image) := by
    refine p.toImage.denseRange.mono ?_
    rintro _ ⟨y, rfl⟩
    exact hUtop (Set.mem_univ y)
  obtain ⟨r, X', j, f, hj, hf, hsm, hiso, hd, hco⟩ := hR ℚ N e p.image p.imageι U ⟨inferInstance, hred, hdense, hsmU⟩
  obtain ⟨ζ, hζ, hdomζ, hζU⟩ := lift_generic p.toImage f U hd hUtop
  obtain ⟨x', hx', hp₂⟩ := exists_coords (ζ ≫ j ≫ pullback.snd _ _)
  have hp₁ : ζ ≫ j ≫ pullback.fst _ _ = point ℚ x hx := by
    rw [← hf, reassoc_of% hζ, hπ]
  have : Smooth (f ≫ p.imageι ≫ PSpace.str ℚ N) := hsm.smooth
  have hredX' : IsReduced X' := GlobalTheory.isReduced_of_smooth_of_isReduced (f ≫ p.imageι ≫ PSpace.str ℚ N)
  refine ⟨r, x', hx', fun i l hl => ?_, fun a l ha hl => ?_⟩
  · have hW : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l) := le_preimage_chart (by simpa using hp₂) hl
    have := val_mem_field p.toImage f U ζ hζ hζU hW₀ h₀ _ hA₀ _ hW
      (pullRatio (j ≫ pullback.snd _ _) _ l le_rfl i)
    rwa [valR_pullRatio (by simpa using hp₂) hW] at this
  · obtain ⟨hWa, hW, hAW⟩ := prod_chart j ζ x hx x' hx' hp₁ hp₂ a l ha hl
    obtain ⟨σ, hσ, hb⟩ := form_section (j ≫ pullback.fst _ _) ζ x hx (by simpa using hp₁) hW inf_le_left hG
    rw [← hσ]
    refine snc_transfer ζ (f ≫ p.imageι ≫ PSpace.str ℚ N) e _ hsm hco hWa hW _ hAW σ fun t ht => ?_
    rw [hb]
    have e₁ : (j ≫ pullback.fst _ _) t = p.imageι (f t) := by
      rw [← hf]
      rfl
    constructor
    · rintro h ⟨-, h2⟩
      exact h (show p.imageι (f t) ∈ Proj.basicOpen (grading ℚ N) G from e₁ ▸ h2)
    · intro h h2
      exact h ⟨ht, show (j ≫ pullback.fst _ _) t ∈ Proj.basicOpen (grading ℚ N) G from e₁ ▸ h2⟩

section Top
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_standard_smooth_localization Ω K ι y e hA N E c₀ hc`.
-/
theorem exists_smooth (y : (Σ k, ι k) → Ω) (e : ℕ) (hA : IsArithVar (mCoordIdeal y) (e + 1)) (N : ℕ)
    (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1)) (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) :
    ∃ s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩), s ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s) :=
  GlobalTheory.T.exists_standard_smooth_localization Ω K ι y e hA N E c₀ hc

/- English proof (translation)
The claim follows from `GlobalTheory.T.standard_smooth_chart_of_nonzero Ω K ι y e β b hb hβ N E c₀ hc s hs`.
-/
theorem exists_form (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ) (hb : IsMultiHomog β b)
    (hβ : β ∉ mCoordIdeal y) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))
    (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0)
    (s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)) (hs : s ≠ 0)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s)] :
    ∃ (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ)
      (g₀ : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)),
      Gz.IsHomogeneous (d + 1) ∧ (X c₀ : MvPolynomial _ ℤ) ∣ Gz ∧
      (g₀ : Ω) = aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) Gz ∧ g₀ ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀) ∧
      ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 →
        eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0 :=
  GlobalTheory.T.standard_smooth_chart_of_nonzero Ω K ι y e β b hb hβ N E c₀ hc s hs

/- English proof (translation)
The claim follows from `GlobalTheory.T.homogeneous_form_nonvanishing_point Ω K ι y e β N E d Gz r x' hG h0 hβ hx' hF hch`.
-/
theorem final_data (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k))
    (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ) (r : ℕ) (x' : Fin (r + 1) → Ω)
    (hG : Gz.IsHomogeneous (d + 1)) (h0 : aeval (fun j => ∏ k, y ⟨k, E j k⟩) Gz ≠ 0)
    (hβ : ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 →
      eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0)
    (hx' : x' ≠ 0) (hF : ∀ i l, x' l ≠ 0 → x' i / x' l ∈ blockFnField y)
    (hch : ∀ a l, (∏ k, y ⟨k, E a k⟩) ≠ 0 → x' l ≠ 0 →
      SncChart (Algebra.adjoin ℚ (Set.range (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) ∪
        Set.range (fun k => x' k / x' l))) e
        (aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) (map (algebraMap ℤ ℚ) Gz))) :
    ∃ (y' : (Σ _ : Unit, Fin (r + 1)) → Ω) (J : Ideal (MRing (joinIdx ι fun _ : Unit => Fin (r + 1)))),
      (∃ i, y' ⟨(), i⟩ ≠ 0) ∧ blockFnField (joinVec y y') = blockFnField y ∧ IsMultiHomogIdeal J ∧
      ¬ J ≤ mCoordIdeal (joinVec y y') ∧ IsSncModel (joinVec y y') e J ∧
      ∀ z ∈ mcPts (mCoordIdeal (joinVec y y')),
        evC z (rename (joinInl ι fun _ : Unit => Fin (r + 1)) β) = 0 → z ∈ mcPts J :=
  GlobalTheory.T.homogeneous_form_nonvanishing_point Ω K ι y e β N E d Gz r x' hG h0 hβ hx' hF hch

/- English proof (translation)
Rewrite using `[IntermediateField.adjoin_le_iff]`. Establish `h1 : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) ≤ (blockFnField y).toSubalgebra`. Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨j, rfl⟩`. Express the relevant statement in the definitionally equal form `(∏ k, y ⟨k, E j k⟩) / (∏ k, y ⟨k, E c₀ k⟩) ∈ blockFnField y`.

Rewrite using `[← Finset.prod_div_distrib]`. Conclude with `prod_mem fun k _ => IntermediateField.subset_adjoin _ _ ⟨⟨k, E j k⟩, ⟨k, E c₀ k⟩, rfl, rfl⟩`. Conclude with `h1`.
-/
theorem adjoin_seg_le (y : (Σ k, ι k) → Ω) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))
    (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) :
    IntermediateField.adjoin ℚ ((Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) :
      Subalgebra ℚ Ω) : Set Ω) ≤ blockFnField y := by
  rw [IntermediateField.adjoin_le_iff]
  have h1 : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) ≤
      (blockFnField y).toSubalgebra := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    change (∏ k, y ⟨k, E j k⟩) / (∏ k, y ⟨k, E c₀ k⟩) ∈ blockFnField y
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => IntermediateField.subset_adjoin _ _ ⟨⟨k, E j k⟩, ⟨k, E c₀ k⟩, rfl, rfl⟩
  exact h1

/- English proof (translation)
Introduce `hR K _ ι _ Ω _ _ y e β b hA hb hβ`. Take `⟨-, ⟨-, -, hrel⟩, -, -⟩` from `id hA`. Use `choose c hc using hrel`. Establish `hc' : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k h0 => hc k (by`. Rewrite using `[mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul])`.

Establish `: Nonempty ((k : K) → ι k)` using `⟨c⟩`. Take `⟨N, hN⟩ : ∃ N, Fintype.card ((k : K) → ι k) = N + 1` from `Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero`. Set `E : Fin (N + 1) ≃ ((k : K) → ι k)` to `(Fintype.equivFinOfCardEq hN).symm`. Set `c₀` to `E.symm c`. Establish `hE : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0` using `fun k => by simpa [c₀] using hc' k`.

Take `⟨s, hs, hsm⟩` from `exists_smooth y e hA N E c₀ hE`. Take `⟨d, Gz, g₀, hG, hdiv, hg₀, hg0, hsm₀, hz⟩` from `exists_form y e β b hb hβ N E c₀ hE s hs`. Set `x : Fin (N + 1) → Ω` to `fun j => ∏ k, y ⟨k, E j k⟩`. Establish `hx₀ : x c₀ ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => hE k`. Set `G` to `map (algebraMap ℤ ℚ) Gz`.

Take `⟨r, x', hx', hF, hch⟩` from `snc_of_res hR N e d x c₀ hx₀ G (hG.map _) (by simpa [G] using map_dvd (MvPolynomial.map (algebraMap ℤ ℚ)) hdiv) g₀ (by rw [hg₀]; exact (aeval_map_algebraMap ℚ _ _).symm) hg0`. Take `⟨y', J, h⟩` from `final_data y e β N E d Gz r x' hG (by`. Introduce `h`. Establish `h1 : aeval (fun j => x j / x c₀) Gz = 0`. Simplify using `only [div_eq_inv_mul]`.

Rewrite using `[GlobalTheory.CompanionTheory.Ar.ProjCoord.aeval_mul_of_isHomogeneous x _ hG]`. Conclude with `mul_eq_zero_of_right _ h`. Conclude with `hg0 (Subtype.ext (hg₀.trans h1))) hz hx'`. Use the proof step `(fun i l hl => adjoin_seg_le y N E c₀ hE (hF i l hl)) (fun a l ha hl => hch a l ha hl)`. Conclude with `⟨r + 1, y', J, h⟩`.
-/
theorem exists_snc_model : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomog β b → β ∉ mCoordIdeal y → ∃ (M : ℕ) (y' : (Σ _ : Unit, Fin M) → Ω) (J : Ideal (MRing (joinIdx ι fun _ : Unit => Fin M))), (∃ i, y' ⟨(), i⟩ ≠ 0) ∧ blockFnField (joinVec y y') = blockFnField y ∧ IsMultiHomogIdeal J ∧ ¬ J ≤ mCoordIdeal (joinVec y y') ∧ IsSncModel (joinVec y y') e J ∧ ∀ z ∈ mcPts (mCoordIdeal (joinVec y y')), evC z (rename (joinInl ι fun _ : Unit => Fin M) β) = 0 → z ∈ mcPts J := by
  intro hR K _ ι _ Ω _ _ y e β b hA hb hβ
  classical
  obtain ⟨-, ⟨-, -, hrel⟩, -, -⟩ := id hA
  choose c hc using hrel
  have hc' : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hc k (by
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul])
  have : Nonempty ((k : K) → ι k) := ⟨c⟩
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card ((k : K) → ι k) = N + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let E : Fin (N + 1) ≃ ((k : K) → ι k) := (Fintype.equivFinOfCardEq hN).symm
  let c₀ := E.symm c
  have hE : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0 := fun k => by simpa [c₀] using hc' k
  obtain ⟨s, hs, hsm⟩ := exists_smooth y e hA N E c₀ hE
  obtain ⟨d, Gz, g₀, hG, hdiv, hg₀, hg0, hsm₀, hz⟩ := exists_form y e β b hb hβ N E c₀ hE s hs
  let x : Fin (N + 1) → Ω := fun j => ∏ k, y ⟨k, E j k⟩
  have hx₀ : x c₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hE k
  let G := map (algebraMap ℤ ℚ) Gz
  obtain ⟨r, x', hx', hF, hch⟩ := snc_of_res hR N e d x c₀ hx₀ G (hG.map _)
    (by simpa [G] using map_dvd (MvPolynomial.map (algebraMap ℤ ℚ)) hdiv) g₀
    (by rw [hg₀]; exact (aeval_map_algebraMap ℚ _ _).symm) hg0
  obtain ⟨y', J, h⟩ := final_data y e β N E d Gz r x' hG (by
      intro h
      have h1 : aeval (fun j => x j / x c₀) Gz = 0 := by
        simp only [div_eq_inv_mul]
        rw [GlobalTheory.CompanionTheory.Ar.ProjCoord.aeval_mul_of_isHomogeneous x _ hG]
        exact mul_eq_zero_of_right _ h
      exact hg0 (Subtype.ext (hg₀.trans h1))) hz hx'
    (fun i l hl => adjoin_seg_le y N E c₀ hE (hF i l hl)) (fun a l ha hl => hch a l ha hl)
  exact ⟨r + 1, y', J, h⟩
end Top

end GlobalTheory.CompanionTheory.Ar.SncRes
