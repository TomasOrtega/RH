import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.UnimodularGram.StarRingOfInvolution

namespace KStar.Cstarloc

variable {R : Type*} [CommRing R] [StarRing R] {M : Type*} [AddCommGroup M] [Module R M]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hh`. Use extensionality with `i j`. Simplify using `only [gram, Matrix.conjTranspose_apply, Matrix.of_apply]`. Conclude with `(hh (b j) (b i)).symm`.

Introduce `hG x y`. Establish `hb : ∀ i j, star (h (b i) (b j)) = h (b j) (b i)` using `fun i j => by`. Use `congrFun (congrFun hG j) i` as an intermediate fact. Simplify `this` using `[gram, Matrix.conjTranspose_apply]`. Rewrite using `[← b.sum_repr x, ← b.sum_repr y]`.

Simplify using `only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, RingHom.id_apply, starRingEnd_apply, smul_eq_mul, star_sum, star_mul', star_star, hb, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isHerm_iff_gram {ι : Type*} [Fintype ι] (h : Sesq R M) (b : Module.Basis ι R M) :
    IsHerm h ↔ (gram h b).IsHermitian := by
  constructor
  · intro hh
    ext i j
    simp only [gram, Matrix.conjTranspose_apply, Matrix.of_apply]
    exact (hh (b j) (b i)).symm
  · intro hG x y
    have hb : ∀ i j, star (h (b i) (b j)) = h (b j) (b i) := fun i j => by
      have := congrFun (congrFun hG j) i
      simpa [gram, Matrix.conjTranspose_apply] using this
    rw [← b.sum_repr x, ← b.sum_repr y]
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, RingHom.id_apply,
      starRingEnd_apply, smul_eq_mul, star_sum, star_mul', star_star, hb, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/- English proof (translation)
Establish `hmv : Function.Bijective (gram h b).mulVec ↔ IsUnit (gram h b).det`. Rewrite using `[← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]`. Use `⟨fun hb => hb.2, fun hs => ⟨?_, hs⟩⟩` and prove the remaining obligations. Establish `hu : IsUnit (gram h b).det` using `(Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_surjective_iff_isUnit.mp hs)`. Introduce `v w hvw`.

Use `congrArg (gram h b)⁻¹.mulVec hvw` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu]`. Establish `hcomp : (b.dualBasis.equivFun ∘ (LinearMap.flip h) ∘ b.equivFun.symm) = (gram h b).mulVec ∘ star`. Use function extensionality and compare the values at `v i`. Simplify using `[Module.Basis.equivFun_symm_apply, Module.Basis.dualBasis_repr, gram, Matrix.mulVec, dotProduct, map_sum, map_smulₛₗ, mul_comm, starRingEnd_apply]`.

Establish `hfl : Function.Bijective (LinearMap.flip h) ↔ Function.Bijective ((gram h b).mulVec ∘ star)`. Rewrite using `[← hcomp, EquivLike.comp_bijective, EquivLike.bijective_comp]`. Rewrite using `[IsUnimod, hfl, Function.Bijective.of_comp_iff _ (Function.Involutive.bijective star_involutive), hmv]`.
-/
theorem isUnimod_iff_gram {ι : Type*} [Fintype ι] [DecidableEq ι] (h : Sesq R M)
    (b : Module.Basis ι R M) : IsUnimod h ↔ IsUnit (gram h b).det := by
  have hmv : Function.Bijective (gram h b).mulVec ↔ IsUnit (gram h b).det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]
    refine ⟨fun hb => hb.2, fun hs => ⟨?_, hs⟩⟩
    have hu : IsUnit (gram h b).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_surjective_iff_isUnit.mp hs)
    intro v w hvw
    have := congrArg (gram h b)⁻¹.mulVec hvw
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu] using this
  have hcomp : (b.dualBasis.equivFun ∘ (LinearMap.flip h) ∘ b.equivFun.symm) =
      (gram h b).mulVec ∘ star := by
    funext v i
    simp [Module.Basis.equivFun_symm_apply, Module.Basis.dualBasis_repr, gram, Matrix.mulVec, dotProduct,
      map_sum, map_smulₛₗ, mul_comm, starRingEnd_apply]
  have hfl : Function.Bijective (LinearMap.flip h) ↔ Function.Bijective ((gram h b).mulVec ∘ star) := by
    rw [← hcomp, EquivLike.comp_bijective, EquivLike.bijective_comp]
  rw [IsUnimod, hfl, Function.Bijective.of_comp_iff _ (Function.Involutive.bijective star_involutive), hmv]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [gram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, starRingEnd_apply]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_comb {ι κ : Type*} [Fintype κ] (h : Sesq R M) (x : κ → M) (P : Matrix ι κ R) :
    gram h (fun i => ∑ j, P i j • x j) = P * gram h x * P.conjTranspose := by
  ext i j
  simp only [gram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    starRingEnd_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

end KStar.Cstarloc
