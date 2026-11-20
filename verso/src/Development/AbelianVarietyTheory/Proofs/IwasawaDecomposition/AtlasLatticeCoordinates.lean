import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeftInverseOfFibrewiseInjective
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GrCl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F} {M : Model Xo c V.subtype}
  {X : Scheme.{0}} {π : X ⟶ M.X}

def LCrd.frvecEmbL (D : LCrd M π) (α : D.C.A) {S : Type} [CommRing S] (z : Sp S ⟶ X) (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α) :
    TanM (z ≫ π) M.t.G →ₗ[S] (Fin (D.N + 1) → S) :=
  (Matrix.mulVecLin ((D.Em.A α).map (ev z _ h))).comp (D.crd α S z h)

/- English proof (translation)
Unfold `LCrd.emb`. Rewrite using `[D.bc α S S' φ z _ rfl h h' e v, FlagMod.ev_spMap φ z _ h h']`. Use function extensionality and compare the values at `r`. Rewrite using `[Function.comp_apply, RingHom.map_mulVec, Matrix.map_map]`. Both sides reduce to the same expression.
-/
theorem LCrd.frvec_emb_tanPull (D : LCrd M π) (α : D.C.A) {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (z : Sp S ⟶ X) (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α) (h' : ⊤ ≤ (spMap φ ≫ z) ⁻¹ᵁ D.C.B α)
    (e : spMap φ ≫ z ≫ π = (spMap φ ≫ z) ≫ π) (v : TanM (z ≫ π) M.t.G) :
    D.emb α (spMap φ ≫ z) h' (tanPull φ e v) = φ ∘ D.emb α z h v := by
  unfold LCrd.emb
  rw [D.bc α S S' φ z _ rfl h h' e v, FlagMod.ev_spMap φ z _ h h']
  funext r
  rw [Function.comp_apply, RingHom.map_mulVec, Matrix.map_map]
  rfl

/- English proof (translation)
Take `⟨u, hu⟩` from `D.Em.compat α β S z hα hβ`. Use `⟨u, fun v => ?_⟩` and prove the remaining obligations. Unfold `LCrd.emb`. Rewrite using `[← D.tr α β S z hα hβ v, Matrix.mulVec_mulVec]`. Rewrite using `[hu]`.

Use extensionality with `r`. Simplify using `[Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`.
-/
theorem LCrd.frvec_exists_emb_eq_smul (D : LCrd M π) (α β : D.C.A) {S : Type} [CommRing S] (z : Sp S ⟶ X)
    (hα : ⊤ ≤ z ⁻¹ᵁ D.C.B α) (hβ : ⊤ ≤ z ⁻¹ᵁ D.C.B β) :
    ∃ u : Sˣ, ∀ v, D.emb α z hα v = (u : S) • D.emb β z hβ v := by
  obtain ⟨u, hu⟩ := D.Em.compat α β S z hα hβ
  refine ⟨u, fun v => ?_⟩
  unfold LCrd.emb
  rw [← D.tr α β S z hα hβ v, Matrix.mulVec_mulVec]
  rw [hu]
  ext r
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Take `⟨A', hA'⟩` from `D.Em.linv α`. Establish `h1 : A'.map (ev z _ h) * (D.Em.A α).map (ev z _ h) = 1`. Rewrite using `[← Matrix.map_mul, hA', Matrix.map_one _ (map_zero _) (map_one _)]`. Introduce `x y hxy`. Simplify using `only [LCrd.frvecEmbL, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply] at hxy`.

Use `congrArg (fun w => (A'.map (ev z _ h)).mulVec w) hxy` as an intermediate fact. Simplify using `only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at this`. Conclude with `D.inj α K z h hz this`.
-/
theorem LCrd.frvec_emb_injective (D : LCrd M π) (α : D.C.A) {K : Type} [Field K] (z : Sp K ⟶ X) (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α)
    (hz : Set.range z ⊆ π ⁻¹' Set.range M.j) : Function.Injective (D.frvecEmbL α z h) := by
  obtain ⟨A', hA'⟩ := D.Em.linv α
  have h1 : A'.map (ev z _ h) * (D.Em.A α).map (ev z _ h) = 1 := by
    rw [← Matrix.map_mul, hA', Matrix.map_one _ (map_zero _) (map_one _)]
  intro x y hxy
  simp only [LCrd.frvecEmbL, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply] at hxy
  have := congrArg (fun w => (A'.map (ev z _ h)).mulVec w) hxy
  simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at this
  exact D.inj α K z h hz this

/- English proof (translation)
Rewrite using `[initSpan, initSpan, Submodule.map_span, Set.image_image]`.
-/
theorem frvec_initSpan_map {K P Q : Type} [Field K] [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q] {m : ℕ}
    (F : P →ₗ[K] Q) (v : Fin m → P) (e : ℕ) : initSpan K (fun i => F (v i)) e = (initSpan K v e).map F := by
  rw [initSpan, initSpan, Submodule.map_span, Set.image_image]

/- English proof (translation)
Use `le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨j, hj, rfl⟩`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)`. Introduce and unpack `_ ⟨j, hj, rfl⟩`. Establish `: v j = ((u⁻¹ : Kˣ) : K) • ((u : K) • v j)` using `by rw [smul_smul, Units.inv_mul, one_smul]`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)`.
-/
theorem frvec_initSpan_smul {K Q : Type} [Field K] [AddCommGroup Q] [Module K Q] {m : ℕ}
    (u : Kˣ) (v : Fin m → Q) (e : ℕ) : initSpan K (fun i => (u : K) • v i) e = initSpan K v e := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨j, hj, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · rintro _ ⟨j, hj, rfl⟩
    have : v j = ((u⁻¹ : Kˣ) : K) • ((u : K) • v j) := by rw [smul_smul, Units.inv_mul, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)

/- English proof (translation)
Establish `: {j : Fin m | (j : ℕ) < m} = Set.univ` using `Set.eq_univ_of_forall fun j => j.2`. Rewrite using `[initSpan, this, Set.image_univ]`.
-/
theorem frvec_initSpan_top {K Q : Type} [Field K] [AddCommGroup Q] [Module K Q] {m : ℕ}
    (v : Fin m → Q) : initSpan K v m = Submodule.span K (Set.range v) := by
  have : {j : Fin m | (j : ℕ) < m} = Set.univ := Set.eq_univ_of_forall fun j => j.2
  rw [initSpan, this, Set.image_univ]

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c V M X π ty A D σ α hα`. Establish `hu : ∀ a, ∃ u : TVecs Dw M.t (A.ch.χ a ≫ π), up u = A.fr a` using `fun a => exists_up fun σ i => ((A.frame a).1 σ i).1`. Use `choose u₀ hu₀ using hu`. Set `cv : ∀ a, Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R a` to `fun a i => D.emb (α a) (A.ch.χ a) (hα a) (u₀ a σ i)`. Establish `key : IsFrVec D A σ α cv`.

Introduce `a S _ φ z ez h u hup i`. Substitute `ez` using the available equality. Establish `e' : spMap φ ≫ A.ch.χ a ≫ π = (spMap φ ≫ A.ch.χ a) ≫ π` using `(Category.assoc _ _ _).symm`. Establish `hu : u = fun σ i => tanPull φ e' (u₀ a σ i)`. Apply `up_injective` to reduce the goal to its premises.

Rewrite using `[up_tanPull, hu₀, hup]`. Rewrite using `[hu]`. Conclude with `(D.frvec_emb_tanPull (α a) φ (A.ch.χ a) (hα a) h e' (u₀ a σ i)).symm`. Establish `li : ∀ (a : A.ch.ι) (K : Type) [Field K] (φ : A.ch.R a →+* K), LinearIndependent K fun i => φ ∘ cv a i`. Introduce `a K _ φ`.

Establish `h : ⊤ ≤ (spMap φ ≫ A.ch.χ a) ⁻¹ᵁ D.C.B (α a)` using `FlagMod.le_preimage_comp _ (hα a)`. Take `⟨u, hu⟩` from `A.exists_up_fr (rfl : spMap φ ≫ A.ch.χ a = _)`. Establish `hf` using `A.isFrame_bc (rfl : spMap φ ≫ A.ch.χ a = _)`. Rewrite `hf` using `[← hu]`. Establish `hr : Set.range (spMap φ ≫ A.ch.χ a) ⊆ π ⁻¹' Set.range M.j`.

Rewrite using `[← A.cover]`. Conclude with `A.ch.range_subset rfl`. Use `((isFrame_up_iff _ _).1 hf σ).1.map' (D.frvecEmbL (α a) _ h) (LinearMap.ker_eq_bot.2 (D.frvec_emb_injective (α a) _ h hr))` as an intermediate fact. Establish `e : (fun i => φ ∘ cv a i) = D.frvecEmbL (α a) _ h ∘ u σ` using `funext fun i => key a K φ _ rfl h u hu i`. Rewrite using `[e]`.

Conclude with `this`. Establish `hD : ∀ a, ∃ Dv : Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R a, LeftInv Dv (cv a)`. Introduce `a`. Take `⟨Q, hQ⟩` from `GlobalTheory.matrix_exists_left_inverse_of_forall_field (A.ch.R a) (D.N + 1) (Dw.mult σ) (Matrix.of fun r i => cv a i r) fun K _ φ => by`. Rewrite using `[Matrix.mulVec_injective_iff]`.

Conclude with `li a K φ`. Use `⟨fun z r => Q z r, fun z z' => ?_⟩` and prove the remaining obligations. Use `congrFun (congrFun hQ z) z'` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [Matrix.of_apply] at this`.

Use `this` and compare the differences between its conclusion and the goal. Use `choose Dv hDv using hD`. Use `⟨cv, Dv, key, hDv, fun K _ a a' φ φ' hz e he => ?_⟩` and prove the remaining obligations. Establish `h : ⊤ ≤ (spMap φ ≫ A.ch.χ a) ⁻¹ᵁ D.C.B (α a)` using `FlagMod.le_preimage_comp _ (hα a)`. Establish `h' : ⊤ ≤ (spMap φ ≫ A.ch.χ a) ⁻¹ᵁ D.C.B (α a')`.

Rewrite using `[hz]`. Conclude with `FlagMod.le_preimage_comp _ (hα a')`. Take `⟨u, hu⟩` from `A.exists_up_fr (rfl : spMap φ ≫ A.ch.χ a = _)`. Take `⟨u', hu'⟩` from `A.exists_up_fr hz.symm`. Take `⟨s, hs⟩` from `D.frvec_exists_emb_eq_smul (α a') (α a) _ h' h`.

Establish `e1 : (fun i => φ ∘ cv a i) = fun i => D.frvecEmbL (α a) _ h (u σ i)`. Use function extensionality and compare the values at `fun i => key a K φ _ rfl h u hu i`. Establish `e2 : (fun i => φ' ∘ cv a' i) = fun i => (s : K) • D.frvecEmbL (α a) _ h (u' σ i)`. Use function extensionality and compare the values at `fun i => (key a' K φ' _ hz.symm h' u' hu' i).trans (hs _)`. Rewrite using `[e1, e2, frvec_initSpan_smul, frvec_initSpan_map, frvec_initSpan_map]`.

Use `congr 1`. Break down `he with he | rfl | rfl` into its components or cases. Establish `f1` using `A.flagAt_fr (rfl : spMap φ ≫ A.ch.χ a = _)`. Establish `f2` using `A.flagAt_fr hz.symm`. Rewrite `f1` using `[← hu]`.

Rewrite `f2` using `[← hu']`. Conclude with `Atlas.FlagAt.initSpan_eq f1 f2 σ he`. Simplify using `[initSpan]`. Establish `f1` using `A.isFrame_bc (rfl : spMap φ ≫ A.ch.χ a = _)`. Establish `f2` using `A.isFrame_bc hz.symm`.

Rewrite `f1` using `[← hu]`. Rewrite `f2` using `[← hu', ← A.alg_eq rfl hz.symm]`. Rewrite using `[frvec_initSpan_top, frvec_initSpan_top, ((isFrame_up_iff _ _).1 f1 σ).2, ((isFrame_up_iff _ _).1 f2 σ).2]`.
-/
theorem exists_isFrVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (D : LCrd M π) (σ : E →+* ℂ) (α : A.ch.ι → D.C.A), (∀ a, ⊤ ≤ A.ch.χ a ⁻¹ᵁ D.C.B (α a)) → ∃ (cv Dv : ∀ a, Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R a), IsFrVec D A σ α cv ∧ (∀ a, LeftInv (Dv a) (cv a)) ∧ ∀ (K : Type) [Field K] (a a' : A.ch.ι) (φ : A.ch.R a →+* K) (φ' : A.ch.R a' →+* K), spMap φ ≫ A.ch.χ a = spMap φ' ≫ A.ch.χ a' → ∀ e : ℕ, e ∈ ty σ ∨ e = 0 ∨ e = Dw.mult σ → initSpan K (fun i => φ ∘ cv a i) e = initSpan K (fun i => φ' ∘ cv a' i) e := by
  intro E _ _ _ H Dw l Xo c V M X π ty A D σ α hα
  have hu : ∀ a, ∃ u : TVecs Dw M.t (A.ch.χ a ≫ π), up u = A.fr a :=
    fun a => exists_up fun σ i => ((A.frame a).1 σ i).1
  choose u₀ hu₀ using hu
  let cv : ∀ a, Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R a :=
    fun a i => D.emb (α a) (A.ch.χ a) (hα a) (u₀ a σ i)
  have key : IsFrVec D A σ α cv := by
    intro a S _ φ z ez h u hup i
    subst ez
    have e' : spMap φ ≫ A.ch.χ a ≫ π = (spMap φ ≫ A.ch.χ a) ≫ π := (Category.assoc _ _ _).symm
    have hu : u = fun σ i => tanPull φ e' (u₀ a σ i) := by
      apply up_injective
      rw [up_tanPull, hu₀, hup]
    rw [hu]
    exact (D.frvec_emb_tanPull (α a) φ (A.ch.χ a) (hα a) h e' (u₀ a σ i)).symm
  have li : ∀ (a : A.ch.ι) (K : Type) [Field K] (φ : A.ch.R a →+* K),
      LinearIndependent K fun i => φ ∘ cv a i := by
    intro a K _ φ
    have h : ⊤ ≤ (spMap φ ≫ A.ch.χ a) ⁻¹ᵁ D.C.B (α a) := FlagMod.le_preimage_comp _ (hα a)
    obtain ⟨u, hu⟩ := A.exists_up_fr (rfl : spMap φ ≫ A.ch.χ a = _)
    have hf := A.isFrame_bc (rfl : spMap φ ≫ A.ch.χ a = _)
    rw [← hu] at hf
    have hr : Set.range (spMap φ ≫ A.ch.χ a) ⊆ π ⁻¹' Set.range M.j := by
      rw [← A.cover]
      exact A.ch.range_subset rfl
    have := ((isFrame_up_iff _ _).1 hf σ).1.map' (D.frvecEmbL (α a) _ h)
      (LinearMap.ker_eq_bot.2 (D.frvec_emb_injective (α a) _ h hr))
    have e : (fun i => φ ∘ cv a i) = D.frvecEmbL (α a) _ h ∘ u σ := funext fun i => key a K φ _ rfl h u hu i
    rw [e]
    exact this
  have hD : ∀ a, ∃ Dv : Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R a, LeftInv Dv (cv a) := by
    intro a
    obtain ⟨Q, hQ⟩ := GlobalTheory.matrix_exists_left_inverse_of_forall_field (A.ch.R a) (D.N + 1) (Dw.mult σ)
      (Matrix.of fun r i => cv a i r) fun K _ φ => by
        rw [Matrix.mulVec_injective_iff]
        exact li a K φ
    refine ⟨fun z r => Q z r, fun z z' => ?_⟩
    have := congrFun (congrFun hQ z) z'
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simp only [Matrix.of_apply] at this
    convert this
  choose Dv hDv using hD
  refine ⟨cv, Dv, key, hDv, fun K _ a a' φ φ' hz e he => ?_⟩
  have h : ⊤ ≤ (spMap φ ≫ A.ch.χ a) ⁻¹ᵁ D.C.B (α a) := FlagMod.le_preimage_comp _ (hα a)
  have h' : ⊤ ≤ (spMap φ ≫ A.ch.χ a) ⁻¹ᵁ D.C.B (α a') := by
    rw [hz]; exact FlagMod.le_preimage_comp _ (hα a')
  obtain ⟨u, hu⟩ := A.exists_up_fr (rfl : spMap φ ≫ A.ch.χ a = _)
  obtain ⟨u', hu'⟩ := A.exists_up_fr hz.symm
  obtain ⟨s, hs⟩ := D.frvec_exists_emb_eq_smul (α a') (α a) _ h' h
  have e1 : (fun i => φ ∘ cv a i) = fun i => D.frvecEmbL (α a) _ h (u σ i) :=
    funext fun i => key a K φ _ rfl h u hu i
  have e2 : (fun i => φ' ∘ cv a' i) = fun i => (s : K) • D.frvecEmbL (α a) _ h (u' σ i) :=
    funext fun i => (key a' K φ' _ hz.symm h' u' hu' i).trans (hs _)
  rw [e1, e2, frvec_initSpan_smul, frvec_initSpan_map, frvec_initSpan_map]
  congr 1
  rcases he with he | rfl | rfl
  · have f1 := A.flagAt_fr (rfl : spMap φ ≫ A.ch.χ a = _)
    have f2 := A.flagAt_fr hz.symm
    rw [← hu] at f1
    rw [← hu'] at f2
    exact Atlas.FlagAt.initSpan_eq f1 f2 σ he
  · simp [initSpan]
  · have f1 := A.isFrame_bc (rfl : spMap φ ≫ A.ch.χ a = _)
    have f2 := A.isFrame_bc hz.symm
    rw [← hu] at f1
    rw [← hu', ← A.alg_eq rfl hz.symm] at f2
    rw [frvec_initSpan_top, frvec_initSpan_top, ((isFrame_up_iff _ _).1 f1 σ).2, ((isFrame_up_iff _ _).1 f2 σ).2]

end GlobalTheory.GrCl
