import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AutomorphicArithmetic.DivisorFrames.ExistsChartTransition
import Development.AutomorphicArithmetic.DivisorFrames.ExistsFlagOfTriangularCharts
import Development.AutomorphicArithmetic.DivisorFrames.FlagChartTransitionTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

/- English proof (translation)
Establish `h : (A * B).BlockTriangular id` using `BlockTriangular.mul (b := id) (fun _ _ h => hA _ _ h) (fun _ _ h => hB _ _ h)`. Conclude with `fun _ _ h' => h h'`.
-/
private theorem tri_mul {K : Type} [CommRing K] {r : ℕ} {A B : Matrix (Fin r) (Fin r) K} (hA : IsTri A) (hB : IsTri B) :
    IsTri (A * B) := by
  have h : (A * B).BlockTriangular id :=
    BlockTriangular.mul (b := id) (fun _ _ h => hA _ _ h) (fun _ _ h => hB _ _ h)
  exact fun _ _ h' => h h'

/- English proof (translation)
Use `invertibleOfIsUnitDet A hu` as an intermediate fact. Establish `h : A⁻¹.BlockTriangular id` using `blockTriangular_inv_of_blockTriangular fun _ _ h => hA _ _ h`. Conclude with `fun _ _ h' => h h'`.
-/
private theorem tri_inv {K : Type} [CommRing K] {r : ℕ} {A : Matrix (Fin r) (Fin r) K} (hA : IsTri A)
    (hu : IsUnit A.det) : IsTri A⁻¹ := by
  have := invertibleOfIsUnitDet A hu
  have h : A⁻¹.BlockTriangular id := blockTriangular_inv_of_blockTriangular fun _ _ h => hA _ _ h
  exact fun _ _ h' => h h'

/- English proof (translation)
Consider the cases of `dual`. Conclude with `⟨hu, hu⟩`. Prove the components needed by the constructor for the conclusion. Express the relevant statement in the definitionally equal form `IsUnit (A.submatrix Fin.revPerm id).det`. Rewrite using `[det_permute]`.

Conclude with `(Units.isUnit _ |>.map (Int.castRingHom K)).mul hu`. Express the relevant statement in the definitionally equal form `IsUnit (A.submatrix id Fin.revPerm).det`. Rewrite using `[det_permute']`. Conclude with `(Units.isUnit _ |>.map (Int.castRingHom K)).mul hu`.
-/
private theorem unit_sub {K : Type} [CommRing K] {r : ℕ} (dual : Bool) {A : Matrix (Fin r) (Fin r) K}
    (hu : IsUnit A.det) : IsUnit (A.submatrix (pos dual) id).det ∧ IsUnit (A.submatrix id (pos dual)).det := by
  cases dual
  · exact ⟨hu, hu⟩
  · constructor
    · change IsUnit (A.submatrix Fin.revPerm id).det
      rw [det_permute]
      exact (Units.isUnit _ |>.map (Int.castRingHom K)).mul hu
    · change IsUnit (A.submatrix id Fin.revPerm).det
      rw [det_permute']
      exact (Units.isUnit _ |>.map (Int.castRingHom K)).mul hu

/- English proof (translation)
Consider the cases of `dual`. Conclude with `tri_inv hU hu`. Introduce `a i h`. Simplify using `only [lieMat, pos, cond_true, nonsing_inv_nonsing_inv _ hu, submatrix_apply, transpose_apply]`. Conclude with `hU _ _ (Fin.rev_lt_rev.2 h)`.
-/
private theorem tri_lie {K : Type} [CommRing K] {r : ℕ} (dual : Bool) {U : Matrix (Fin r) (Fin r) K} (hU : IsTri U)
    (hu : IsUnit U.det) : IsTri ((lieMat dual U⁻¹).submatrix (pos dual) (pos dual)) := by
  cases dual
  · exact tri_inv hU hu
  · intro a i h
    simp only [lieMat, pos, cond_true, nonsing_inv_nonsing_inv _ hu, submatrix_apply, transpose_apply]
    exact hU _ _ (Fin.rev_lt_rev.2 h)

/- English proof (translation)
Establish `hu'` using `(unit_sub dual hu).1`. Establish `e : (A * T).submatrix (pos dual) id = A.submatrix (pos dual) id * T` using `rfl`. Use `tri_mul (tri_inv hA hu') hA'` as an intermediate fact. Rewrite `this` using `[e, ← Matrix.mul_assoc, nonsing_inv_mul _ hu', Matrix.one_mul]`. Then use the resulting hypothesis.
-/
private theorem tri_of_mul {K : Type} [CommRing K] {r : ℕ} (dual : Bool) {A T : Matrix (Fin r) (Fin r) K}
    (hu : IsUnit A.det) (hA : IsTri (A.submatrix (pos dual) id)) (hA' : IsTri ((A * T).submatrix (pos dual) id)) :
    IsTri T := by
  have hu' := (unit_sub dual hu).1
  have e : (A * T).submatrix (pos dual) id = A.submatrix (pos dual) id * T := rfl
  have := tri_mul (tri_inv hA hu') hA'
  rwa [e, ← Matrix.mul_assoc, nonsing_inv_mul _ hu', Matrix.one_mul] at this

/- English proof (translation)
Use `(injective_iff_map_eq_zero _).2 fun a ha => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h0`. Establish `hb : X.basicOpen a ≠ ⊥` using `fun hb => h0 ((basicOpen_eq_bot_iff a).1 hb)`. Take `⟨x, hx⟩` from `(TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hb`. Establish `hu : IsUnit (resG X (X.basicOpen_le a) a)` using `X.toRingedSpace.isUnit_res_basicOpen a`.

Use `hu.map (evalPt ξ _ (hξ _ x hx))` as an intermediate fact. Rewrite `this` using `[evalPt_res ξ _ h, ha]`. Conclude with `not_isUnit_zero this`.
-/
private theorem evalPt_inj {X : Scheme.{0}} {K : Type} [Field K] [IsIntegral X] {ξ : Sp K ⟶ X}
    (hξ : ∀ (U : X.Opens) (x : X), x ∈ U → ⊤ ≤ ξ ⁻¹ᵁ U) (U : X.Opens)
    (h : ⊤ ≤ ξ ⁻¹ᵁ U) : Function.Injective (evalPt ξ U h) := by
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  by_contra h0
  have hb : X.basicOpen a ≠ ⊥ := fun hb => h0 ((basicOpen_eq_bot_iff a).1 hb)
  obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hb
  have hu : IsUnit (resG X (X.basicOpen_le a) a) := X.toRingedSpace.isUnit_res_basicOpen a
  have := hu.map (evalPt ξ _ (hξ _ x hx))
  rw [evalPt_res ξ _ h, ha] at this
  exact not_isUnit_zero this

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Z F _ _ e C τ M hM dual A hA`. Establish `key : ∀ y : C.Y.X, ∃ ch : Chart M (Dw.mult τ), y ∈ ch.U ∧ IsTri ((A ch).submatrix (pos dual) id)`. Introduce `y`. Take `⟨φ, f, t, h1, -⟩` from `C.gr_spec y`. Take `⟨k, hk⟩` from `exists_isMap_toFn (e := e) (ρ := C.π) f h1.2.1`.

Establish `hU : IsTri (k.co C.f0 τ)` using `(h1.co τ hk).1`. Establish `hu : IsUnit (k.co C.f0 τ).det` using `k.isUnit_det_co _ τ`. Establish `hf : Fits C.f0 τ y φ f (k.co C.f0 τ)⁻¹` using `(fits_iff h1.2.1 hk).2 (inv_eq_left_inv ((EigFrame.co_mul _ _ _ τ).trans (EigFrame.co_self _ τ))).symm`. Take `⟨U, s, hy, hs⟩` from `hM y`. Set `ch₀ : Chart M (Dw.mult τ)` to `⟨U, s, hs⟩`.

Establish `hy₀ : (𝟙 C.Y.X : C.Y.X ⟶ C.Y.X) y ∈ ch₀.U` using `hy`. Take `⟨φ₀, f₀, hf₀⟩` from `hA.2 ch₀ y hy₀`. Take `rfl : φ₀ = φ` from `hf₀.φ_eq hf`. Establish `e1` using `hf₀.eq_mul hf`. Establish `hc : IsUnit (f₀.co f τ).det` using `f₀.isUnit_det_co f τ`.

Take `⟨ch, hch, hT⟩` from `UpperTheory.exists_chart_transition _ M _ ch₀ y hy ((lieMat dual (f₀.co f τ)).submatrix id (pos dual)) (unit_sub dual (isUnit_det_lieMat dual hc)).2`. Establish `hy₁ : (𝟙 C.Y.X : C.Y.X ⟶ C.Y.X) y ∈ ch.U` using `hch`. Use `⟨ch, hch, ?_⟩` and prove the remaining obligations. Establish `e2 : A ch = (lieMat dual (k.co C.f0 τ)⁻¹).submatrix id (pos dual)`. Rewrite using `[hA.1.2 ch₀ ch (gen_le _ hy₀) (gen_le _ hy₁), trAt_gen _ ch₀ ch hy₀ hy₁, Category.comp_id, e1, lieMat_mul, lieMat_lieMat _ (hA.1.1 ch₀ (gen_le _ hy₀)), lieMat_map _ _ hc]`.

Conclude with `congrArg (fun T => A ch₀ * T.map (toFn y)) hT`. Rewrite using `[e2]`. Conclude with `tri_lie dual hU hu`. Use `choose ch hch htri using key`. Establish `hg : ∀ y, ⊤ ≤ (genericPt C.Y ≫ 𝟙 C.Y.X) ⁻¹ᵁ (ch y).U` using `fun y => gen_le (y := y) _ (hch y)`.

Take `⟨fl, hfl⟩` from `UpperTheory.exists_flag_of_triangular_charts _ M _ C.Y.X ch (fun x => ⟨x, hch x⟩) fun y y' => by`. Establish `h` using `htri y'`. Rewrite `h` using `[hA.1.2 _ _ (hg y) (hg y')]`. Establish `h'` using `tri_of_mul dual (hA.1.1 _ (hg y)) (htri y) h`. Rewrite `h'` using `[trAt_eq _ _ (le_inf_pre (hg y) (hg y'))]`.

Conclude with `fun a i hi => evalPt_inj (fun U x hx => gen_le (y := x) _ hx) _ (le_inf_pre (hg y) (hg y')) ((h' a i hi).trans (map_zero _).symm)`. Use `⟨fl, fun c' ha hc' => ?_⟩` and prove the remaining obligations. Set `η` to `genericPoint C.Y.X`. Establish `h` using `(UpperTheory.flag_chart_transition_triangular _ M _ fl (ch η) c' (hfl η) ha).1`. Rewrite using `[hA.1.2 _ _ (hg η) hc', trAt_eq _ _ (le_inf_pre (hg η) hc')]`.

Conclude with `tri_mul (htri η) fun a i hi => (congrArg (evalPt _ _ (le_inf_pre (hg η) hc')) (h a i hi)).trans (map_zero _)`.
-/
theorem UpperTheory.flag_compact_vector_bundle :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C : FlagCpt Z e) (τ : E →+* ℂ) (M : C.Y.X.Modules) (hM : IsVB M (Dw.mult τ)) (dual : Bool) (A : Chart M (Dw.mult τ) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) C.Y.Fn), IsLie C.f0 τ (𝟙 C.Y.X) dual A → ∃ fl : Vert.Flag M (Dw.mult τ), IsFlag (genericPt C.Y ≫ 𝟙 C.Y.X) dual A fl := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e C τ M hM dual A hA
  have key : ∀ y : C.Y.X, ∃ ch : Chart M (Dw.mult τ), y ∈ ch.U ∧ IsTri ((A ch).submatrix (pos dual) id) := by
    intro y
    obtain ⟨φ, f, t, h1, -⟩ := C.gr_spec y
    obtain ⟨k, hk⟩ := exists_isMap_toFn (e := e) (ρ := C.π) f h1.2.1
    have hU : IsTri (k.co C.f0 τ) := (h1.co τ hk).1
    have hu : IsUnit (k.co C.f0 τ).det := k.isUnit_det_co _ τ
    have hf : Fits C.f0 τ y φ f (k.co C.f0 τ)⁻¹ := (fits_iff h1.2.1 hk).2
      (inv_eq_left_inv ((EigFrame.co_mul _ _ _ τ).trans (EigFrame.co_self _ τ))).symm
    obtain ⟨U, s, hy, hs⟩ := hM y
    let ch₀ : Chart M (Dw.mult τ) := ⟨U, s, hs⟩
    have hy₀ : (𝟙 C.Y.X : C.Y.X ⟶ C.Y.X) y ∈ ch₀.U := hy
    obtain ⟨φ₀, f₀, hf₀⟩ := hA.2 ch₀ y hy₀
    obtain rfl : φ₀ = φ := hf₀.φ_eq hf
    have e1 := hf₀.eq_mul hf
    have hc : IsUnit (f₀.co f τ).det := f₀.isUnit_det_co f τ
    obtain ⟨ch, hch, hT⟩ := UpperTheory.exists_chart_transition _ M _ ch₀ y hy ((lieMat dual (f₀.co f τ)).submatrix id (pos dual))
      (unit_sub dual (isUnit_det_lieMat dual hc)).2
    have hy₁ : (𝟙 C.Y.X : C.Y.X ⟶ C.Y.X) y ∈ ch.U := hch
    refine ⟨ch, hch, ?_⟩
    have e2 : A ch = (lieMat dual (k.co C.f0 τ)⁻¹).submatrix id (pos dual) := by
      rw [hA.1.2 ch₀ ch (gen_le _ hy₀) (gen_le _ hy₁), trAt_gen _ ch₀ ch hy₀ hy₁, Category.comp_id, e1, lieMat_mul,
        lieMat_lieMat _ (hA.1.1 ch₀ (gen_le _ hy₀)), lieMat_map _ _ hc]
      exact congrArg (fun T => A ch₀ * T.map (toFn y)) hT
    rw [e2]
    exact tri_lie dual hU hu
  choose ch hch htri using key
  have hg : ∀ y, ⊤ ≤ (genericPt C.Y ≫ 𝟙 C.Y.X) ⁻¹ᵁ (ch y).U := fun y => gen_le (y := y) _ (hch y)
  obtain ⟨fl, hfl⟩ := UpperTheory.exists_flag_of_triangular_charts _ M _ C.Y.X ch (fun x => ⟨x, hch x⟩) fun y y' => by
    have h := htri y'
    rw [hA.1.2 _ _ (hg y) (hg y')] at h
    have h' := tri_of_mul dual (hA.1.1 _ (hg y)) (htri y) h
    rw [trAt_eq _ _ (le_inf_pre (hg y) (hg y'))] at h'
    exact fun a i hi => evalPt_inj (fun U x hx => gen_le (y := x) _ hx) _ (le_inf_pre (hg y) (hg y'))
      ((h' a i hi).trans (map_zero _).symm)
  refine ⟨fl, fun c' ha hc' => ?_⟩
  let η := genericPoint C.Y.X
  have h := (UpperTheory.flag_chart_transition_triangular _ M _ fl (ch η) c' (hfl η) ha).1
  rw [hA.1.2 _ _ (hg η) hc', trAt_eq _ _ (le_inf_pre (hg η) hc')]
  exact tri_mul (htri η) fun a i hi =>
    (congrArg (evalPt _ _ (le_inf_pre (hg η) hc')) (h a i hi)).trans (map_zero _)
