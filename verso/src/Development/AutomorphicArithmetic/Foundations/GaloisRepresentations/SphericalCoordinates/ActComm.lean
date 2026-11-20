import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.PActY

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
The claim follows from `G.star_star a`.
-/
private theorem sh_sh' (G : HTGroup p) (a : G.C) : sh G (sh G a) = a := G.star_star a

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Simplify using `only [_root_.mul_assoc, Units.inv_mul_cancel_left]`. Use `_ = ((β⁻¹ : G.Cˣ) : G.C) * ((y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C s * β) * ((β⁻¹ : G.Cˣ) : G.C) * y := by`. Rewrite using `[h]`. Use `_ = algebraMap ℚ G.C s * ((β⁻¹ : G.Cˣ) : G.C) := by`.

Simplify using `only [_root_.mul_assoc, Units.mul_inv_cancel_left]`. Rewrite using `[Algebra.commutes s (y : G.C), Units.inv_mul_cancel_left]`. Conclude with `(Algebra.commutes s _).symm`.
-/
private theorem key (G : HTGroup p) (β y : G.Cˣ) (s : ℚ)
    (h : (y : G.C) * β * sh G y = algebraMap ℚ G.C s * β) :
    sh G y * ((β⁻¹ : G.Cˣ) : G.C) * y = algebraMap ℚ G.C s * ((β⁻¹ : G.Cˣ) : G.C) := by
  calc sh G y * ((β⁻¹ : G.Cˣ) : G.C) * y
      = ((β⁻¹ : G.Cˣ) : G.C) * ((y⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * β * sh G y) * ((β⁻¹ : G.Cˣ) : G.C) * y := by
        simp only [_root_.mul_assoc, Units.inv_mul_cancel_left]
    _ = ((β⁻¹ : G.Cˣ) : G.C) * ((y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C s * β) * ((β⁻¹ : G.Cˣ) : G.C) * y := by
        rw [h]
    _ = algebraMap ℚ G.C s * ((β⁻¹ : G.Cˣ) : G.C) := by
        simp only [_root_.mul_assoc, Units.mul_inv_cancel_left]
        rw [Algebra.commutes s (y : G.C), Units.inv_mul_cancel_left]
        exact (Algebra.commutes s _).symm

/- English proof (translation)
Establish `hk` using `key G β (y : G.Cˣ × ℚˣ).1 (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) y.2.1`. Establish `h1` using `L.adj (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (L.rep ((β⁻¹ : G.Cˣ) : G.C) (L.rep (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) u)) w`. Rewrite `h1` using `[sh_sh']`. Establish `h2 : L.rep (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (L.rep ((β⁻¹ : G.Cˣ) : G.C) (L.rep (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) u)) = (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) • L.rep ((β⁻¹ : G.Cˣ) : G.C) u`. Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hk, map_mul, AlgHom.commutes, Module.End.mul_apply, Module.algebraMap_end_apply]`.

Simplify using `only [formB, actY]`. Rewrite using `[← h1, h2, map_smul, LinearMap.smul_apply, smul_eq_mul]`.
-/
private theorem form_act {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ) (y : GlobalTheory.LKCx.grp G β)
    (u w : VQ D) : formB L β (actY L y u) (actY L y w) = (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) * formB L β u w := by
  have hk := key G β (y : G.Cˣ × ℚˣ).1 (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) y.2.1
  have h1 := L.adj (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))
    (L.rep ((β⁻¹ : G.Cˣ) : G.C) (L.rep (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) u)) w
  rw [sh_sh'] at h1
  have h2 : L.rep (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))
      (L.rep ((β⁻¹ : G.Cˣ) : G.C) (L.rep (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) u)) =
      (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) • L.rep ((β⁻¹ : G.Cˣ) : G.C) u := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hk, map_mul,
      AlgHom.commutes, Module.End.mul_apply, Module.algebraMap_end_apply]
  simp only [formB, actY]
  rw [← h1, h2, map_smul, LinearMap.smul_apply, smul_eq_mul]

/- English proof (translation)
Establish `h` using `(L.rep_range (actY L y)).1 ⟨_, rfl⟩ c`. Conclude with `LinearMap.congr_fun h w`.
-/
private theorem act_comm {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ) (y : GlobalTheory.LKCx.grp G β)
    (c : D.O) (w : VQ D) : actY L y (actQ D c w) = actQ D c (actY L y w) := by
  have h := (L.rep_range (actY L y)).1 ⟨_, rfl⟩ c
  exact LinearMap.congr_fun h w

/- English proof (translation)
Simplify using `only [actY]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one, Module.End.one_apply]`.
-/
private theorem act_inv {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ) (y : GlobalTheory.LKCx.grp G β)
    (w : VQ D) : actY L y (L.rep (((((y : G.Cˣ × ℚˣ).1 : G.Cˣ))⁻¹ : G.Cˣ) : G.C) w) = w := by
  simp only [actY]
  rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one, Module.End.one_apply]

/- English proof (translation)
Take `⟨h1, h2, Hm, hH, hpos, him⟩` from `hP`. Establish `hsc : ∀ (c : ℂ) (z z' : Fin D.g → ℂ), hermForm (c • Hm) z z' = c * hermForm Hm z z'`. Introduce `c z z'`. Simplify using `only [hermForm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]`. Establish `hr : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ)`.

Conclude with `y.prop.2` after adjusting the coercions. Establish `hQ' : ∀ u, Q' u = Q (L.rep ((((y : G.Cˣ × ℚˣ).1 : G.Cˣ)⁻¹ : G.Cˣ) : G.C) u)`. Introduce `u`. Rewrite using `[← hQ, act_inv]`. Use `⟨fun c w => ?_, ?_, (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) : ℂ) • Hm, ?_, fun z hz => ?_, fun u w => ?_⟩` and prove the remaining obligations.

Rewrite using `[hQ', hQ', ← h1]`. Use `congr 1`. Conclude with `LinearMap.congr_fun ((L.rep_range _).1 ⟨_, rfl⟩ c) w`. Rewrite using `[eq_top_iff, ← h2]`. Apply `Submodule.span_mono` to reduce the goal to its premises.

Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `⟨_, hQ w⟩`. Simplify using `[Matrix.IsHermitian, Matrix.conjTranspose_smul, hH.eq, Complex.star_def, Complex.conj_ofReal]`. Rewrite using `[hsc, Complex.re_ofReal_mul]`. Conclude with `mul_pos hr (hpos z hz)`.

Rewrite using `[← act_inv L β y u, ← act_inv L β y w, hQ, hQ, hsc, form_act, Complex.im_ofReal_mul, him]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem per_act {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ) (y : GlobalTheory.LKCx.grp G β)
    (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Q Q' : VQ D →+ (Fin D.g → ℂ)) (hP : IsPerQ L β ρ Q)
    (hQ : ∀ w, Q' (actY L y w) = Q w) : IsPerQ L β ρ Q' := by
  obtain ⟨h1, h2, Hm, hH, hpos, him⟩ := hP
  have hsc : ∀ (c : ℂ) (z z' : Fin D.g → ℂ), hermForm (c • Hm) z z' = c * hermForm Hm z z' := by
    intro c z z'
    simp only [hermForm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hr : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by
    exact_mod_cast y.prop.2
  have hQ' : ∀ u, Q' u = Q (L.rep ((((y : G.Cˣ × ℚˣ).1 : G.Cˣ)⁻¹ : G.Cˣ) : G.C) u) := by
    intro u
    rw [← hQ, act_inv]
  refine ⟨fun c w => ?_, ?_, (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) : ℂ) • Hm, ?_, fun z hz => ?_, fun u w => ?_⟩
  · rw [hQ', hQ', ← h1]
    congr 1
    exact LinearMap.congr_fun ((L.rep_range _).1 ⟨_, rfl⟩ c) w
  · rw [eq_top_iff, ← h2]
    apply Submodule.span_mono
    rintro _ ⟨w, rfl⟩
    exact ⟨_, hQ w⟩
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_smul, hH.eq, Complex.star_def, Complex.conj_ofReal]
  · rw [hsc, Complex.re_ofReal_mul]
    exact mul_pos hr (hpos z hz)
  · rw [← act_inv L β y u, ← act_inv L β y w, hQ, hQ, hsc, form_act, Complex.im_ofReal_mul, him]
    push_cast
    ring

/- English proof (translation)
Establish `he : v.embedding (algebraMap ℚ G.F s) = (s : ℂ)` using `map_ratCast (v.embedding.comp (algebraMap ℚ G.F)) s`. Rewrite using `[IsScalarTower.algebraMap_apply ℚ G.F G.C, G.psi_F, he]`. Use extensionality with `i j`. Simplify using `[Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]`.
-/
private theorem psi_rat (G : HTGroup p) (v : InfinitePlace G.F) (s : ℚ) :
    G.psi v (algebraMap ℚ G.C s) = ((s : ℝ) : ℂ) • (1 : Matrix (Fin G.n) (Fin G.n) ℂ) := by
  have he : v.embedding (algebraMap ℚ G.F s) = (s : ℂ) := map_ratCast (v.embedding.comp (algebraMap ℚ G.F)) s
  rw [IsScalarTower.algebraMap_apply ℚ G.F G.C, G.psi_F, he]
  ext i j
  simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]

/- English proof (translation)
Establish `hk` using `key G β (y : G.Cˣ × ℚˣ).1 (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) y.prop.1`. Establish `hr : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ)`. Conclude with `y.prop.2` after adjusting the coercions. Establish `hV : ((GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ)) = G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)` using `rfl`. Establish `hg : (G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * G.gram v = G.gram v * G.psi v (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))`.

Rewrite using `[show sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = MulOpposite.unop (G.star (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) from rfl, G.psi_star, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (G.gram_det v)), Matrix.one_mul]`. Establish `hpsi : G.psi v (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * G.psi v ((β⁻¹ : G.Cˣ) : G.C) * G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) : ℂ) • G.psi v ((β⁻¹ : G.Cˣ) : G.C)`. Rewrite using `[← map_mul, ← map_mul, hk, map_mul, psi_rat, smul_one_mul]`. Establish `hM : (G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * GlobalTheory.LKCx.herm G v β * G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) : ℂ) • GlobalTheory.LKCx.herm G v β`. Simplify using `only [GlobalTheory.LKCx.herm]`.

Rewrite using `[← Matrix.mul_assoc, hg, ← Matrix.mul_smul, ← hpsi]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hV, Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hM, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]`. Conclude with `mul_pos hr z.2`.
-/
private theorem pos_act (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : GlobalTheory.LKCx.grp G β)
    (z : GlobalTheory.LKCx.PosV G v β) :
    0 < (star ((GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1) ⬝ᵥ
      (GlobalTheory.LKCx.herm G v β *ᵥ ((GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1))).re := by
  have hk := key G β (y : G.Cˣ × ℚˣ).1 (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) y.prop.1
  have hr : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by
    exact_mod_cast y.prop.2
  have hV : ((GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ)) =
      G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := rfl
  have hg : (G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * G.gram v =
      G.gram v * G.psi v (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) := by
    rw [show sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      MulOpposite.unop (G.star (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) from rfl, G.psi_star,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (G.gram_det v)), Matrix.one_mul]
  have hpsi : G.psi v (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * G.psi v ((β⁻¹ : G.Cˣ) : G.C) *
      G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) : ℂ) • G.psi v ((β⁻¹ : G.Cˣ) : G.C) := by
    rw [← map_mul, ← map_mul, hk, map_mul, psi_rat, smul_one_mul]
  have hM : (G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * GlobalTheory.LKCx.herm G v β *
      G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) : ℂ) • GlobalTheory.LKCx.herm G v β := by
    simp only [GlobalTheory.LKCx.herm]
    rw [← Matrix.mul_assoc, hg, ← Matrix.mul_smul, ← hpsi]
    simp only [Matrix.mul_assoc]
  rw [hV, Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hM, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  exact mul_pos hr z.2

end UpperTheory.Gal.W2.PActY

open UpperTheory.Gal.W2.PActY in
/- English proof (translation)
Introduce `p _ D G L β y`. Conclude with `⟨form_act L β y, act_comm L β y, fun ρ Q Q' hP hQ => per_act L β y ρ Q Q' hP hQ, fun v z _ => ⟨⟨_, pos_act G v β y z⟩, rfl⟩⟩`.
-/
theorem UpperTheory.Gal.W2.actY_of :
    UpperTheory.Gal.W2.ActY := by
  intro p _ D G L β y
  exact ⟨form_act L β y, act_comm L β y, fun ρ Q Q' hP hQ => per_act L β y ρ Q Q' hP hQ,
    fun v z _ => ⟨⟨_, pos_act G v β y z⟩, rfl⟩⟩
