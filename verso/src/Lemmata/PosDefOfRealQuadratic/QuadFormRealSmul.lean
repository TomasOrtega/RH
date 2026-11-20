import Mathlib

universe u_1

namespace Bl.PosDefOfRealQuadratic

/- English proof (translation)
Rewrite using `[Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]`. Simplify using `only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma quadForm_real_smul {m : Nat} (M : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) (r : ℝ) :
    star ((r : ℂ) • v) ⬝ᵥ (Matrix.mulVec (M) ((r : ℂ) • v)) = ((r ^ 2 : ℝ) : ℂ) * (star v ⬝ᵥ (Matrix.mulVec (M) v)) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

open scoped ComplexOrder in
/- English proof (translation)
The claim follows from `(Complex.pos_iff.mp (h.dotProduct_mulVec_pos hy)).1`.
-/
private lemma re_quad_pos {m : Nat} {M : Matrix (Fin m) (Fin m) ℂ} (h : M.PosDef) {y : Fin m → ℂ}
    (hy : y ≠ 0) : 0 < (star y ⬝ᵥ (Matrix.mulVec M y)).re :=
  (Complex.pos_iff.mp (h.dotProduct_mulVec_pos hy)).1

open scoped ComplexOrder in
/- English proof (translation)
The claim follows from `Matrix.PosDef.of_dotProduct_mulVec_pos hH fun v hv => Complex.pos_iff.mpr ⟨h v hv, (hH.im_star_dotProduct_mulVec_self v).symm⟩`.
-/
private lemma posDef_of_re {m : Nat} {M : Matrix (Fin m) (Fin m) ℂ} (hH : M.IsHermitian)
    (h : ∀ v : Fin m → ℂ, v ≠ 0 → 0 < (star v ⬝ᵥ (Matrix.mulVec M v)).re) : M.PosDef :=
  Matrix.PosDef.of_dotProduct_mulVec_pos hH fun v hv =>
    Complex.pos_iff.mpr ⟨h v hv, (hH.im_star_dotProduct_mulVec_self v).symm⟩

/- English proof (translation)
Introduce `X inst m A hA hH x0 h0`. Establish `hAc : Continuous A` using `continuous_pi fun i => continuous_pi fun j => hA i j`. Use `set K : Set (Fin m → ℂ) := Metric.sphere 0 1 with hK`. Establish `hKc : IsCompact K` using `isCompact_sphere 0 1`. Establish `hq : Continuous fun p : X × (Fin m → ℂ) => star p.2 ⬝ᵥ (Matrix.mulVec (A p.1) p.2)` using `(continuous_snd.star).dotProduct ((hAc.comp continuous_fst).matrix_mulVec continuous_snd)`.

Establish `key : ∀ᶠ x in nhds x0, ∀ y ∈ K, 0 < (star y ⬝ᵥ (Matrix.mulVec (A x) y)).re`. Use `hKc.eventually_forall_of_forall_eventually fun y hy => ?_` and prove the remaining obligations. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Simplify using `[hK] at hy`.

Establish `hpos : 0 < (star y ⬝ᵥ (Matrix.mulVec (A x0) y)).re` using `re_quad_pos h0 hy0`. Establish `hev` using `(continuousAt_const (x := (x0, y))).eventually_lt ((Complex.continuous_re.comp hq).continuousAt (x := (x0, y))) hpos`. Use `filter_upwards [hev] with z hz using hz`. Use `filter_upwards [key] with x hx`. Use `posDef_of_re (hH x) fun v hv => ?_` and prove the remaining obligations.

Establish `hn : 0 < ‖v‖` using `norm_pos_iff.mpr hv`. Establish `hw : ((‖v‖⁻¹ : ℝ) : ℂ) • v ∈ K`. Rewrite using `[hK, mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']`. Establish `h1` using `hx _ hw`. Rewrite `h1` using `[quadForm_real_smul, Complex.re_ofReal_mul]`.

Conclude with `pos_of_mul_pos_right h1 (by positivity)`.
-/
theorem goal1 :
  ∀ {X : Type u_1} [inst : TopologicalSpace.{u_1} X] {m : Nat} (A : X → Matrix.{0, 0, 0} (Fin m) (Fin m) Complex),
  (∀ (i j : Fin m),
      @Continuous.{u_1, 0} X Complex inst
        (@UniformSpace.toTopologicalSpace.{0} Complex
          (@PseudoMetricSpace.toUniformSpace.{0} Complex
            (@SeminormedRing.toPseudoMetricSpace.{0} Complex
              (@SeminormedCommRing.toSeminormedRing.{0} Complex
                (@NormedCommRing.toSeminormedCommRing.{0} Complex
                  (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))))
        fun (x : X) ↦ A x i j) →
    (∀ (x : X),
        @Matrix.IsHermitian.{0, 0} Complex (Fin m)
          (@InvolutiveStar.toStar.{0} Complex
            (@StarAddMonoid.toInvolutiveStar.{0} Complex
              (@AddCommMonoid.toAddMonoid.{0} Complex
                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))))
              (@StarRing.toStarAddMonoid.{0} Complex
                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
                Complex.instStarRing)))
          (A x)) →
      ∀ (x0 : X),
        @Matrix.PosDef.{0, 0} (Fin m) Complex Complex.instRing Complex.partialOrder Complex.instStarRing (A x0) →
          @Filter.Eventually.{u_1} X
            (fun (x : X) ↦
              @Matrix.PosDef.{0, 0} (Fin m) Complex Complex.instRing Complex.partialOrder Complex.instStarRing (A x))
            (@nhds.{u_1} X inst x0) := by
  intro X inst m A hA hH x0 h0
  have hAc : Continuous A := continuous_pi fun i => continuous_pi fun j => hA i j
  set K : Set (Fin m → ℂ) := Metric.sphere 0 1 with hK
  have hKc : IsCompact K := isCompact_sphere 0 1
  have hq : Continuous fun p : X × (Fin m → ℂ) => star p.2 ⬝ᵥ (Matrix.mulVec (A p.1) p.2) :=
    (continuous_snd.star).dotProduct ((hAc.comp continuous_fst).matrix_mulVec continuous_snd)
  have key : ∀ᶠ x in nhds x0, ∀ y ∈ K, 0 < (star y ⬝ᵥ (Matrix.mulVec (A x) y)).re := by
    refine hKc.eventually_forall_of_forall_eventually fun y hy => ?_
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp [hK] at hy
    have hpos : 0 < (star y ⬝ᵥ (Matrix.mulVec (A x0) y)).re :=
      re_quad_pos h0 hy0
    have hev := (continuousAt_const (x := (x0, y))).eventually_lt
      ((Complex.continuous_re.comp hq).continuousAt (x := (x0, y))) hpos
    filter_upwards [hev] with z hz using hz
  filter_upwards [key] with x hx
  refine posDef_of_re (hH x) fun v hv => ?_
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hw : ((‖v‖⁻¹ : ℝ) : ℂ) • v ∈ K := by
    rw [hK, mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, norm_inv, norm_norm,
      inv_mul_cancel₀ hn.ne']
  have h1 := hx _ hw
  rw [quadForm_real_smul, Complex.re_ofReal_mul] at h1
  exact pos_of_mul_pos_right h1 (by positivity)

end Bl.PosDefOfRealQuadratic
