import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandCLMInfApply
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

/- English proof (translation)
Use `set W := InfinitePlace E`. Use `set M : Matrix (Fin n) (Fin n) (Cinf E) := (A : Matrix (Fin n) (Fin n) (Cinf E)) with hM`. Use `set L : (Fin n → Fin n → Cinf E) →ₗ[ℝ] (Fin n → Fin n → Cinf E) := { toFun := fun x i j => (M * Matrix.of x) i j map_add' := fun x y => by`. Use function extensionality and compare the values at `i j`. Express the relevant statement in the definitionally equal form `(M * (Matrix.of x + Matrix.of y)) i j = (M * Matrix.of x) i j + (M * Matrix.of y) i j`.

Rewrite using `[mul_add, Matrix.add_apply]`. Use the proof step `map_smul' := fun c x => by`. Use function extensionality and compare the values at `i j`. Express the relevant statement in the definitionally equal form `(M * (c • Matrix.of x)) i j = c • (M * Matrix.of x) i j`. Rewrite using `[Matrix.mul_smul, Matrix.smul_apply] } with hLdef`.

Establish `hL : ∀ h, L h = fun i j => (M * Matrix.of h) i j` using `fun h => rfl`. Set `e : (Fin n → Fin n → Cinf E) ≃ₗ[ℝ] (W → Fin n → Fin n → ℂ)` to `{ toFun := fun h w i j => h i j w invFun := fun g i j w => g w i j map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Set `Lw : W → (Fin n → Fin n → ℂ) →ₗ[ℝ] (Fin n → Fin n → ℂ)` to `fun w => (LinearMap.mulLeft ℂ (M.map (fun z => z w))).restrictScalars ℝ`. Establish `hconj : (e : _ →ₗ[ℝ] _) ∘ₗ L ∘ₗ (e.symm : _ →ₗ[ℝ] _) = LinearMap.pi (fun w => Lw w ∘ₗ LinearMap.proj w)`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `g`. Use function extensionality and compare the values at `w i j`. Express the relevant statement in the definitionally equal form `(M * Matrix.of (fun i j w => g w i j)) i j w = (M.map (fun z => z w) * Matrix.of (g w)) i j`. Simplify using `[Matrix.mul_apply, Finset.sum_apply, Matrix.map_apply]`. Establish `hdetw : ∀ w, LinearMap.det (Lw w) = Complex.normSq (M.det w) ^ n`.

Introduce `w`. Use `GroundTheory.Automorphic.det_restrictScalars_mulLeft (M.map (fun z => z w))` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin, ← Complex.normSq_eq_norm_sq]`. Use `show LinearMap.det ((LinearMap.mulLeft ℂ (M.map fun z => z w)).restrictScalars ℝ) = _`. Rewrite using `[this]`.

Use `congr 2`. Conclude with `(RingHom.map_det (Pi.evalRingHom (fun _ : W => ℂ) w) M).symm`. Establish `hdet : LinearMap.det L = jacInf M`. Rewrite using `[← LinearMap.det_conj L e, hconj, LinearMap.det_pi]`. Simplify using `only [hdetw]`.

Both sides reduce to the same expression. Establish `hpos : 0 < jacInf M`. Establish `hdA : M.det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).ne_zero`. Use `Finset.prod_pos fun w _ => pow_pos (Complex.normSq_pos.2 ?_) n` and prove the remaining obligations. Introduce `h0`.

Establish `hu : IsUnit M.det` using `(Matrix.isUnit_iff_isUnit_det _).1 A.isUnit`. Establish `: IsUnit (M.det w)` using `hu.map (Pi.evalRingHom (fun _ : W => ℂ) w)`. Conclude with `this.ne_zero h0`. Establish `hd0 : LinearMap.det L ≠ 0` using `by rw [hdet]; exact hpos.ne'`. Establish `hmap : Measure.map L (volume : Measure (Fin n → Fin n → Cinf E)) = ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume` using `Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd0`.

Use `set Le : (Fin n → Fin n → Cinf E) ≃L[ℝ] (Fin n → Fin n → Cinf E) := (LinearMap.equivOfDetNeZero L hd0).toContinuousLinearEquiv`. Establish `hLe : (Le : (Fin n → Fin n → Cinf E) → (Fin n → Fin n → Cinf E)) = L` using `rfl`. Establish `hemb : MeasurableEmbedding (L : (Fin n → Fin n → Cinf E) → (Fin n → Fin n → Cinf E))`. Rewrite using `[← hLe]`. Conclude with `Le.toHomeomorph.measurableEmbedding`.

Repeatedly rewrite using `[← hL]`. Rewrite using `[integral_const_mul, ← hemb.integral_map, hmap, integral_smul_measure, hdet, abs_of_pos (inv_pos.2 hpos), ENNReal.toReal_ofReal (inv_pos.2 hpos).le, Complex.real_smul, ← mul_assoc]`. Use `push_cast`. Rewrite using `[mul_inv_cancel₀ (by exact_mod_cast hpos.ne'), one_mul]`.
-/
theorem integral_eq_integral_mulLeft_matrixInf (E : Type) [Field E] [NumberField E] (n : ℕ)
    (A : GL (Fin n) (Cinf E)) (F : (Fin n → Fin n → Cinf E) → ℂ) :
    ∫ a, F a = ∫ h : (Fin n → Fin n → Cinf E), ((jacInf (A : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) *
      F (fun i j => ((A : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) := by
  set W := InfinitePlace E
  set M : Matrix (Fin n) (Fin n) (Cinf E) := (A : Matrix (Fin n) (Fin n) (Cinf E)) with hM
  set L : (Fin n → Fin n → Cinf E) →ₗ[ℝ] (Fin n → Fin n → Cinf E) :=
    { toFun := fun x i j => (M * Matrix.of x) i j
      map_add' := fun x y => by
        funext i j
        change (M * (Matrix.of x + Matrix.of y)) i j = (M * Matrix.of x) i j + (M * Matrix.of y) i j
        rw [mul_add, Matrix.add_apply]
      map_smul' := fun c x => by
        funext i j
        change (M * (c • Matrix.of x)) i j = c • (M * Matrix.of x) i j
        rw [Matrix.mul_smul, Matrix.smul_apply] } with hLdef
  have hL : ∀ h, L h = fun i j => (M * Matrix.of h) i j := fun h => rfl

  let e : (Fin n → Fin n → Cinf E) ≃ₗ[ℝ] (W → Fin n → Fin n → ℂ) :=
    { toFun := fun h w i j => h i j w
      invFun := fun g i j w => g w i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let Lw : W → (Fin n → Fin n → ℂ) →ₗ[ℝ] (Fin n → Fin n → ℂ) := fun w =>
    (LinearMap.mulLeft ℂ (M.map (fun z => z w))).restrictScalars ℝ
  have hconj : (e : _ →ₗ[ℝ] _) ∘ₗ L ∘ₗ (e.symm : _ →ₗ[ℝ] _) =
      LinearMap.pi (fun w => Lw w ∘ₗ LinearMap.proj w) := by
    apply LinearMap.ext; intro g; funext w i j
    change (M * Matrix.of (fun i j w => g w i j)) i j w = (M.map (fun z => z w) * Matrix.of (g w)) i j
    simp [Matrix.mul_apply, Finset.sum_apply, Matrix.map_apply]
  have hdetw : ∀ w, LinearMap.det (Lw w) = Complex.normSq (M.det w) ^ n := by
    intro w
    have := GroundTheory.Automorphic.det_restrictScalars_mulLeft (M.map (fun z => z w))
    rw [Fintype.card_fin, ← Complex.normSq_eq_norm_sq] at this
    show LinearMap.det ((LinearMap.mulLeft ℂ (M.map fun z => z w)).restrictScalars ℝ) = _
    rw [this]
    congr 2
    exact (RingHom.map_det (Pi.evalRingHom (fun _ : W => ℂ) w) M).symm
  have hdet : LinearMap.det L = jacInf M := by
    rw [← LinearMap.det_conj L e, hconj, LinearMap.det_pi]
    simp only [hdetw]
    rfl
  have hpos : 0 < jacInf M := by
    have hdA : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).ne_zero
    refine Finset.prod_pos fun w _ => pow_pos (Complex.normSq_pos.2 ?_) n
    intro h0
    have hu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit
    have : IsUnit (M.det w) := hu.map (Pi.evalRingHom (fun _ : W => ℂ) w)
    exact this.ne_zero h0
  have hd0 : LinearMap.det L ≠ 0 := by rw [hdet]; exact hpos.ne'
  have hmap : Measure.map L (volume : Measure (Fin n → Fin n → Cinf E)) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd0
  set Le : (Fin n → Fin n → Cinf E) ≃L[ℝ] (Fin n → Fin n → Cinf E) :=
    (LinearMap.equivOfDetNeZero L hd0).toContinuousLinearEquiv
  have hLe : (Le : (Fin n → Fin n → Cinf E) → (Fin n → Fin n → Cinf E)) = L := rfl
  have hemb : MeasurableEmbedding (L : (Fin n → Fin n → Cinf E) → (Fin n → Fin n → Cinf E)) := by
    rw [← hLe]; exact Le.toHomeomorph.measurableEmbedding
  simp_rw [← hL]
  rw [integral_const_mul, ← hemb.integral_map, hmap, integral_smul_measure, hdet,
    abs_of_pos (inv_pos.2 hpos), ENNReal.toReal_ofReal (inv_pos.2 hpos).le, Complex.real_smul, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hpos.ne'), one_mul]

end GlobalTheory.JSW.MirCinf
