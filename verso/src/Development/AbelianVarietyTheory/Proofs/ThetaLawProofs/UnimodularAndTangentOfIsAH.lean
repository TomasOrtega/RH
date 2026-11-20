import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory
namespace UnifCompare

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

/- English proof (translation)
Rewrite using `[← u₀.ker, ← u.ker, hF]`.
-/
lemma mem_iff (u u₀ : HolUnif A L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u₀.ex (F z) = u.ex z) (z : Fin g → ℂ) : F z ∈ u₀.Λ ↔ z ∈ u.Λ := by
  rw [← u₀.ker, ← u.ker, hF]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`. Establish `hm : ∀ t : ℂ, t • z ∈ u.Λ` using `fun t => by`. Rewrite using `[← mem_iff u u₀ F hF, map_smul, hz, smul_zero]`. Conclude with `u₀.Λ.zero_mem`.

Use `u.discrete` as an intermediate fact. Establish `hc : Continuous fun t : ℂ => (⟨t • z, hm t⟩ : u.Λ)` using `Continuous.subtype_mk (continuous_id.smul continuous_const) _`. Establish `h` using `PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℂ) hc (x := 1) (y := 0)`. Simplify using `using congrArg Subtype.val h`.
-/
lemma injective (u u₀ : HolUnif A L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u₀.ex (F z) = u.ex z) : Function.Injective F := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hm : ∀ t : ℂ, t • z ∈ u.Λ := fun t => by
    rw [← mem_iff u u₀ F hF, map_smul, hz, smul_zero]
    exact u₀.Λ.zero_mem
  have := u.discrete
  have hc : Continuous fun t : ℂ => (⟨t • z, hm t⟩ : u.Λ) :=
    Continuous.subtype_mk (continuous_id.smul continuous_const) _
  have h := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℂ) hc (x := 1) (y := 0)
  simpa using congrArg Subtype.val h

/- English proof (translation)
Establish `key : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w = fderiv ℂ (fun z => valAt' (u₀.ex z).left U f) 0 (F w)` using `fun U f => by`. Establish `e : (fun z => valAt' (u.ex z).left U f) = (fun z => valAt' (u₀.ex z).left U f) ∘ F`. Use function extensionality and compare the values at `z`. Simplify using `only [Function.comp, hF]`. Rewrite using `[e, ContinuousLinearEquiv.comp_right_fderiv, map_zero]`.

Both sides reduce to the same expression. Simplify using `only [HolUnif.IsDiff, key]`.
-/
lemma isDiff_iff (u u₀ : HolUnif A L g) (F : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u₀.ex (F z) = u.ex z) (w : Fin g → ℂ) (v : epsR ℂ ⟶ A) :
    u.IsDiff w v ↔ u₀.IsDiff (F w) v := by
  have key : ∀ (U : A.left.Opens) (f : Γ(A.left, U)),
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w =
        fderiv ℂ (fun z => valAt' (u₀.ex z).left U f) 0 (F w) := fun U f => by
    have e : (fun z => valAt' (u.ex z).left U f) = (fun z => valAt' (u₀.ex z).left U f) ∘ F := by
      funext z
      simp only [Function.comp, hF]
    rw [e, ContinuousLinearEquiv.comp_right_fderiv, map_zero]
    rfl
  simp only [HolUnif.IsDiff, key]

open PullHermitian in

/- English proof (translation)
Establish `hΛ : ∀ l : u.Λ, F l ∈ u₀.Λ` using `fun l => (mem_iff u u₀ F hF l).2 l.2`. Establish `hper : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z` using `fun l z => by`. Rewrite using `[u.ex_add, (u.ker l).2 l.2, _root_.mul_one]`. Establish `hFd : Differentiable ℂ F` using `(LinearMap.toContinuousLinearMap F).differentiable`. Establish `tr : ∀ {U : A.left.Opens} {z}, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → ⊤ ≤ (u₀.ex (F z)).left ⁻¹ᵁ U` using `fun h => by rwa [hF]`.

Take `⟨r, hr, hrφ⟩` from `exists_glue (fun i : L.ι => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i}) (fun i => (u.hol _ 0).1) (fun z => exists_chart (u.ex z).left hL) (fun i z => u₀.fr i (F z) / u.fr i z) (fun i => by`. Establish `d2` using `(u₀.fr_hol i).comp (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i}) hFd.differentiableOn fun z hz => tr hz`. Simplify using `only [div_eq_mul_inv]`. Conclude with `d2.mul ((u.fr_hol i).inv fun z hz => u.fr_ne i z hz))`. Use the proof step `(fun i j z hi hj => by`.

Establish `h1` using `u.fr_compat i j z (inf_of _ hi hj)`. Establish `h2` using `u₀.fr_compat i j (F z) (tr (inf_of _ hi hj))`. Rewrite `h2` using `[hF]`. Rewrite using `[div_eq_div_iff (u.fr_ne _ _ hi) (u.fr_ne _ _ hj), h1, h2]`. Use the proof step `ring)`.

Use `set H₂ := (LinearMap.toMatrix' F).transpose * H₀ * (LinearMap.toMatrix' F).transpose.conjTranspose with hH₂`. Establish `hH₂h : H₂.IsHermitian` using `Matrix.isHermitian_mul_mul_conjTranspose _ hu₀.1`. Establish `hsub : ∀ z w, hermForm (Hm - H₂) z w = hermForm Hm z w - hermForm H₀ (F z) (F w)` using `fun z w => by`. Use `hermForm_sub_smul Hm H₂ 1 1 z w` as an intermediate fact. Rewrite `this` using `[one_smul, one_smul, _root_.one_mul, _root_.one_mul, hH₂, hermForm_pull]`. Then use the resulting hypothesis.

Use `u.discrete` as an intermediate fact. Establish `key` using `appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full (Hm - H₂) (fun l => χ l / χ₀ ⟨F l, hΛ l⟩) r (hu.1.sub hH₂h) (fun l => by simp [hu.2.2.1, hu₀.2.2.1]) hr (fun z => by`. Take `⟨i, hi⟩` from `exists_chart (u.ex z).left hL`. Rewrite using `[hrφ i z hi]`. Conclude with `div_ne_zero (u₀.fr_ne _ _ (tr hi)) (u.fr_ne _ _ hi))`.

Use the proof step `(fun l z => by`. Take `⟨i, hi⟩` from `exists_chart (u.ex z).left hL`. Establish `hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i` using `by rwa [hper]`. Establish `h1` using `hu.2.2.2 l i z hi`. Establish `h2` using `hu₀.2.2.2 ⟨F l, hΛ l⟩ i (F z) (tr hi)`.

Establish `h3 : χ l ≠ 0` using `norm_ne_zero_iff.1 (by rw [hu.2.2.1]; exact one_ne_zero)`. Establish `h4 : χ₀ ⟨F l, hΛ l⟩ ≠ 0` using `norm_ne_zero_iff.1 (by rw [hu₀.2.2.1]; exact one_ne_zero)`. Establish `h5` using `u.fr_ne _ _ hi'`. Rewrite using `[hrφ i z hi, hrφ i (z + l) hi']`. Simplify using `only [hsub, map_add]`.

Rewrite using `[h1, h2]`. Simplify using `only [hermForm]`. Generalize the expression as in `(z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) = a`. Generalize the expression as in `((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) = b`. Generalize the expression as in `(F z ⬝ᵥ H₀.mulVec (star (F l))) = a'`.

Generalize the expression as in `(F l ⬝ᵥ H₀.mulVec (star (F l))) = b'`. Establish `e : Complex.exp (Real.pi * (a - a') + Real.pi / 2 * (b - b')) = Complex.exp (Real.pi * a + Real.pi / 2 * b) / Complex.exp (Real.pi * a' + Real.pi / 2 * b')`. Rewrite using `[← Complex.exp_sub]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `h6` using `Complex.exp_ne_zero (Real.pi * a + Real.pi / 2 * b)`. Establish `h7` using `Complex.exp_ne_zero (Real.pi * a' + Real.pi / 2 * b')`. Rewrite using `[e]`. Generalize the expression as in `Complex.exp (Real.pi * a + Real.pi / 2 * b) = s at h6`. Generalize the expression as in `Complex.exp (Real.pi * a' + Real.pi / 2 * b') = s' at h7`.

Use the proof step `field_simp)`. Establish `h` using `hsub z w`. Rewrite `h` using `[key.1]`. Establish `h0 : hermForm (0 : Matrix (Fin g) (Fin g) ℂ) z w = 0` using `by simp [hermForm]`. Rewrite `h` using `[h0]`.

Conclude with `(sub_eq_zero.1 h.symm).symm`.
-/
lemma hermForm_eq (hL : L.IsLB) (u u₀ : HolUnif A L g) {Hm H₀ : Matrix (Fin g) (Fin g) ℂ}
    {χ : u.Λ → ℂ} {χ₀ : u₀.Λ → ℂ} (hu : u.IsAH Hm χ) (hu₀ : u₀.IsAH H₀ χ₀)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ z, u₀.ex (F z) = u.ex z) (z w : Fin g → ℂ) :
    hermForm H₀ (F z) (F w) = hermForm Hm z w := by
  have hΛ : ∀ l : u.Λ, F l ∈ u₀.Λ := fun l => (mem_iff u u₀ F hF l).2 l.2
  have hper : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => by
    rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  have hFd : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  have tr : ∀ {U : A.left.Opens} {z}, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → ⊤ ≤ (u₀.ex (F z)).left ⁻¹ᵁ U :=
    fun h => by rwa [hF]
  obtain ⟨r, hr, hrφ⟩ := exists_glue
    (fun i : L.ι => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i})
    (fun i => (u.hol _ 0).1)
    (fun z => exists_chart (u.ex z).left hL)
    (fun i z => u₀.fr i (F z) / u.fr i z)
    (fun i => by
      have d2 := (u₀.fr_hol i).comp (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i})
        hFd.differentiableOn fun z hz => tr hz
      simp only [div_eq_mul_inv]
      exact d2.mul ((u.fr_hol i).inv fun z hz => u.fr_ne i z hz))
    (fun i j z hi hj => by
      have h1 := u.fr_compat i j z (inf_of _ hi hj)
      have h2 := u₀.fr_compat i j (F z) (tr (inf_of _ hi hj))
      rw [hF] at h2
      rw [div_eq_div_iff (u.fr_ne _ _ hi) (u.fr_ne _ _ hj), h1, h2]
      ring)
  set H₂ := (LinearMap.toMatrix' F).transpose * H₀ * (LinearMap.toMatrix' F).transpose.conjTranspose
    with hH₂
  have hH₂h : H₂.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose _ hu₀.1
  have hsub : ∀ z w, hermForm (Hm - H₂) z w = hermForm Hm z w - hermForm H₀ (F z) (F w) :=
    fun z w => by
      have := hermForm_sub_smul Hm H₂ 1 1 z w
      rwa [one_smul, one_smul, _root_.one_mul, _root_.one_mul, hH₂, hermForm_pull] at this
  have := u.discrete
  have key := appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full
    (Hm - H₂) (fun l => χ l / χ₀ ⟨F l, hΛ l⟩) r (hu.1.sub hH₂h)
    (fun l => by simp [hu.2.2.1, hu₀.2.2.1]) hr
    (fun z => by
      obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hL
      rw [hrφ i z hi]
      exact div_ne_zero (u₀.fr_ne _ _ (tr hi)) (u.fr_ne _ _ hi))
    (fun l z => by
      obtain ⟨i, hi⟩ := exists_chart (u.ex z).left hL
      have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i := by rwa [hper]
      have h1 := hu.2.2.2 l i z hi
      have h2 := hu₀.2.2.2 ⟨F l, hΛ l⟩ i (F z) (tr hi)
      have h3 : χ l ≠ 0 := norm_ne_zero_iff.1 (by rw [hu.2.2.1]; exact one_ne_zero)
      have h4 : χ₀ ⟨F l, hΛ l⟩ ≠ 0 := norm_ne_zero_iff.1 (by rw [hu₀.2.2.1]; exact one_ne_zero)
      have h5 := u.fr_ne _ _ hi'
      rw [hrφ i z hi, hrφ i (z + l) hi']
      simp only [hsub, map_add]
      rw [h1, h2]
      simp only [hermForm]
      generalize (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) = a
      generalize ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) = b
      generalize (F z ⬝ᵥ H₀.mulVec (star (F l))) = a'
      generalize (F l ⬝ᵥ H₀.mulVec (star (F l))) = b'
      have e : Complex.exp (Real.pi * (a - a') + Real.pi / 2 * (b - b')) =
          Complex.exp (Real.pi * a + Real.pi / 2 * b) /
            Complex.exp (Real.pi * a' + Real.pi / 2 * b') := by
        rw [← Complex.exp_sub]
        congr 1
        ring
      have h6 := Complex.exp_ne_zero (Real.pi * a + Real.pi / 2 * b)
      have h7 := Complex.exp_ne_zero (Real.pi * a' + Real.pi / 2 * b')
      rw [e]
      generalize Complex.exp (Real.pi * a + Real.pi / 2 * b) = s at h6
      generalize Complex.exp (Real.pi * a' + Real.pi / 2 * b') = s' at h7
      field_simp)
  have h := hsub z w
  rw [key.1] at h
  have h0 : hermForm (0 : Matrix (Fin g) (Fin g) ℂ) z w = 0 := by simp [hermForm]
  rw [h0] at h
  exact (sub_eq_zero.1 h.symm).symm

end UnifCompare

open UnifCompare in

/- English proof (translation)
Introduce `hT P rig hrig u Hm χ hu`. Take `⟨u₀, H₀, χ₀, E₀, hu₀, -, hv, hw, -, -, hE, hEb, -⟩` from `hT P rig hrig`. Take `⟨F, hF, -⟩` from `GlobalTheory.existsUnique_linear_lift_of_isHolTo P.A P.isAb P.L P.g P.g u₀ hv hw u.ex u.ex_add (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)`. Establish `hinj` using `injective u u₀ F hF`. Set `e : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ)` to `LinearEquiv.ofInjectiveEndo F hinj`.

Establish `he : ∀ z, e z = F z` using `fun z => rfl`. Establish `hd : ∀ w v, u.IsDiff w v ↔ u₀.IsDiff (e w) v` using `isDiff_iff u u₀ e.toContinuousLinearEquiv hF`. Use `⟨?_, fun v hv' => ?_, fun w => ?_⟩` and prove the remaining obligations. Set `φ : u.Λ ≃ₗ[ℤ] u₀.Λ` to `{ toFun := fun a => ⟨e a, (mem_iff u u₀ F hF a).2 a.2⟩ invFun := fun b => ⟨e.symm b, (mem_iff u u₀ F hF _).1 (by`. Rewrite using `[← he, e.apply_symm_apply]`.

Conclude with `b.2)⟩`. Use the proof step `map_add' := fun a b => Subtype.ext (map_add e a.1 b.1)`. Use the proof step `map_smul' := fun n a => Subtype.ext (map_zsmul e n a.1)`. Use `left_inv := fun a => Subtype.ext (e.symm_apply_apply a.1)`. Use `right_inv := fun b => Subtype.ext (e.apply_symm_apply b.1) }`.

Use `⟨φ.dualMap.toLinearMap ∘ₗ E₀ ∘ₗ φ.toLinearMap, fun a b => ?_, φ.dualMap.bijective.comp (hEb.comp φ.bijective)⟩` and prove the remaining obligations. Rewrite using `[← hermForm_eq P.isLB u u₀ hu hu₀ F hF]`. Conclude with `hE (φ a) (φ b)`. Take `⟨w, h1, h2⟩` from `hv v hv'`. Use `⟨e.symm w, (hd _ _).2 (by rwa [e.apply_symm_apply]), fun y hy => ?_⟩` and prove the remaining obligations.

Rewrite using `[← h2 _ ((hd _ _).1 hy), e.symm_apply_apply]`. Simplify using `only [hd]`. Conclude with `hw (e w)`.
-/
theorem unimodular_and_tangent_of_isAH :
    ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen →
    ∀ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ →
    (∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef) ∧
    (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) := by
  intro hT P rig hrig u Hm χ hu
  obtain ⟨u₀, H₀, χ₀, E₀, hu₀, -, hv, hw, -, -, hE, hEb, -⟩ := hT P rig hrig
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo P.A P.isAb P.L P.g P.g u₀ hv hw u.ex u.ex_add
    (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  have hinj := injective u u₀ F hF
  let e : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ) := LinearEquiv.ofInjectiveEndo F hinj
  have he : ∀ z, e z = F z := fun z => rfl
  have hd : ∀ w v, u.IsDiff w v ↔ u₀.IsDiff (e w) v :=
    isDiff_iff u u₀ e.toContinuousLinearEquiv hF
  refine ⟨?_, fun v hv' => ?_, fun w => ?_⟩
  · let φ : u.Λ ≃ₗ[ℤ] u₀.Λ :=
      { toFun := fun a => ⟨e a, (mem_iff u u₀ F hF a).2 a.2⟩
        invFun := fun b => ⟨e.symm b, (mem_iff u u₀ F hF _).1 (by
          rw [← he, e.apply_symm_apply]; exact b.2)⟩
        map_add' := fun a b => Subtype.ext (map_add e a.1 b.1)
        map_smul' := fun n a => Subtype.ext (map_zsmul e n a.1)
        left_inv := fun a => Subtype.ext (e.symm_apply_apply a.1)
        right_inv := fun b => Subtype.ext (e.apply_symm_apply b.1) }
    refine ⟨φ.dualMap.toLinearMap ∘ₗ E₀ ∘ₗ φ.toLinearMap, fun a b => ?_,
      φ.dualMap.bijective.comp (hEb.comp φ.bijective)⟩
    rw [← hermForm_eq P.isLB u u₀ hu hu₀ F hF]
    exact hE (φ a) (φ b)
  · obtain ⟨w, h1, h2⟩ := hv v hv'
    refine ⟨e.symm w, (hd _ _).2 (by rwa [e.apply_symm_apply]), fun y hy => ?_⟩
    rw [← h2 _ ((hd _ _).1 hy), e.symm_apply_apply]
  · simp only [hd]
    exact hw (e w)

end GlobalTheory
