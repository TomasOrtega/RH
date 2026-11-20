import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueTimesThetaFramesEntireStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section
namespace GlobalTheory.MBLow.Cl

section Analytic

variable {B : NumB ℂ} {g : ℕ} (d : AB B g)

/- English proof (translation)
Establish `h` using `d.ex_add 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `mul_eq_left.1 h.symm`.
-/
theorem ex_zero' : d.ex 0 = 1 := by
  have h := d.ex_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

/- English proof (translation)
Simplify using `only [autV, ← Complex.exp_add]`. Use `congr 1`. Simplify using `only [dotProduct_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem autV_cube (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (M N : Fin g → ℤ) (x y z : Fin g → ℂ) :
    autV τ a b M N (x + y + z) * autV τ a b M N z = autV τ a b M N (x + z) * autV τ a b M N (y + z) := by
  simp only [autV, ← Complex.exp_add]
  congr 1
  simp only [dotProduct_add]
  ring

/- English proof (translation)
The claim follows from `Complex.exp_ne_zero _`.
-/
theorem autV_ne (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (M N : Fin g → ℤ) (w : Fin g → ℂ) :
    autV τ a b M N w ≠ 0 := Complex.exp_ne_zero _

/- English proof (translation)
Rewrite using `[d.fr_per M N w, mul_div_cancel_left₀ _ (autV_ne _ _ _ _ _ _)]`.
-/
theorem fr_shift (M N : Fin g → ℤ) (w : Fin g → ℂ) :
    (d.fr (w + perV d.τ M N) : ℂ) = d.fr w / autV d.τ d.a d.b M N w := by
  rw [d.fr_per M N w, mul_div_cancel_left₀ _ (autV_ne _ _ _ _ _ _)]

/- English proof (translation)
Establish `hP : d.ex (perV d.τ M N) = 1` using `(d.ker _).2 ⟨M, N, rfl⟩`. Establish `e1 : x + (z + perV d.τ M N) = x + z + perV d.τ M N` using `by abel`. Establish `e2 : y + (z + perV d.τ M N) = y + z + perV d.τ M N` using `by abel`. Establish `e3 : x + y + (z + perV d.τ M N) = x + y + z + perV d.τ M N` using `by abel`. Unfold `cubF`.

Rewrite using `[d.ex_add, hP, _root_.mul_one, e1, e2, e3, fr_shift, fr_shift, fr_shift, fr_shift]`. Establish `A` using `autV_cube d.τ d.a d.b M N x y z`. Establish `h1` using `autV_ne d.τ d.a d.b M N (x + z)`. Establish `h2` using `autV_ne d.τ d.a d.b M N (y + z)`. Establish `h3` using `autV_ne d.τ d.a d.b M N (x + y + z)`.

Establish `h4` using `autV_ne d.τ d.a d.b M N z`. Establish `u1` using `(d.fr (x + y + z)).ne_zero`. Establish `u2` using `(d.fr x).ne_zero`. Establish `u3` using `(d.fr y).ne_zero`. Establish `u4` using `(d.fr z).ne_zero`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `A`.
-/
theorem cubF_per (x y : Fin g → ℂ) (M N : Fin g → ℤ) (z : Fin g → ℂ) :
    cubF d x y (z + perV d.τ M N) = cubF d x y z := by
  have hP : d.ex (perV d.τ M N) = 1 := (d.ker _).2 ⟨M, N, rfl⟩
  have e1 : x + (z + perV d.τ M N) = x + z + perV d.τ M N := by abel
  have e2 : y + (z + perV d.τ M N) = y + z + perV d.τ M N := by abel
  have e3 : x + y + (z + perV d.τ M N) = x + y + z + perV d.τ M N := by abel
  unfold cubF
  rw [d.ex_add, hP, _root_.mul_one, e1, e2, e3, fr_shift, fr_shift, fr_shift, fr_shift]
  have A := autV_cube d.τ d.a d.b M N x y z
  have h1 := autV_ne d.τ d.a d.b M N (x + z)
  have h2 := autV_ne d.τ d.a d.b M N (y + z)
  have h3 := autV_ne d.τ d.a d.b M N (x + y + z)
  have h4 := autV_ne d.τ d.a d.b M N z
  have u1 := (d.fr (x + y + z)).ne_zero
  have u2 := (d.fr x).ne_zero
  have u3 := (d.fr y).ne_zero
  have u4 := (d.fr z).ne_zero
  field_simp
  linear_combination A

end Analytic

section Bound

variable {B : NumB ℂ} {g : ℕ}

def rv (s : Fin g → ℝ) : Fin g → ℂ := fun i => (s i : ℂ)

/- English proof (translation)
Establish `hT : IsUnit (τ.map Complex.im).det` using `isUnit_iff_ne_zero.2 hpos.det_pos.ne'`. Use `set t : Fin g → ℝ := (τ.map Complex.im)⁻¹ *ᵥ (fun i => (z i).im) with ht`. Use `⟨(fun i => (z i).re) - (τ.map Complex.re) *ᵥ t, t, ?_⟩` and prove the remaining obligations. Establish `hIm : (τ.map Complex.im) *ᵥ t = fun i => (z i).im`. Rewrite using `[ht, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hT, Matrix.one_mulVec]`.

Use function extensionality and compare the values at `i`. Establish `hi` using `congrFun hIm i`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply] at hi`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[rv, Matrix.mulVec, dotProduct, Complex.re_sum]`.

Simplify using `[rv, Matrix.mulVec, dotProduct, Complex.im_sum, hi]`.
-/
theorem exists_real_coords (τ : Matrix (Fin g) (Fin g) ℂ) (hpos : (τ.map Complex.im).PosDef) (z : Fin g → ℂ) :
    ∃ s t : Fin g → ℝ, z = rv s + τ *ᵥ rv t := by
  have hT : IsUnit (τ.map Complex.im).det := isUnit_iff_ne_zero.2 hpos.det_pos.ne'
  set t : Fin g → ℝ := (τ.map Complex.im)⁻¹ *ᵥ (fun i => (z i).im) with ht
  refine ⟨(fun i => (z i).re) - (τ.map Complex.re) *ᵥ t, t, ?_⟩
  have hIm : (τ.map Complex.im) *ᵥ t = fun i => (z i).im := by
    rw [ht, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hT, Matrix.one_mulVec]
  funext i
  have hi := congrFun hIm i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply] at hi
  apply Complex.ext
  · simp [rv, Matrix.mulVec, dotProduct, Complex.re_sum]
  · simp [rv, Matrix.mulVec, dotProduct, Complex.im_sum, hi]

/- English proof (translation)
Take `⟨s, t, rfl⟩` from `exists_real_coords d.τ d.pos z`. Use `⟨fun i => ⌊s i⌋, fun i => ⌊t i⌋, fun i => Int.fract (s i), fun i => Int.fract (t i), fun i => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, fun i => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, ?_⟩` and prove the remaining obligations. Establish `hs : rv s = rv (fun i => Int.fract (s i)) + cv (fun i => ⌊s i⌋)`. Use function extensionality and compare the values at `i`. Simplify using `only [rv, cv, Pi.add_apply, Int.fract]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `ht : rv t = rv (fun i => Int.fract (t i)) + cv (fun i => ⌊t i⌋)`. Use function extensionality and compare the values at `i`. Simplify using `only [rv, cv, Pi.add_apply, Int.fract]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hs, ht, perV, Matrix.mulVec_add]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_reduce (d : AB B g) (z : Fin g → ℂ) : ∃ (M N : Fin g → ℤ) (s t : Fin g → ℝ),
    (∀ i, s i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) ∧ z = rv s + d.τ *ᵥ rv t + perV d.τ M N := by
  obtain ⟨s, t, rfl⟩ := exists_real_coords d.τ d.pos z
  refine ⟨fun i => ⌊s i⌋, fun i => ⌊t i⌋, fun i => Int.fract (s i), fun i => Int.fract (t i),
    fun i => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, fun i => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, ?_⟩
  have hs : rv s = rv (fun i => Int.fract (s i)) + cv (fun i => ⌊s i⌋) := by
    funext i; simp only [rv, cv, Pi.add_apply, Int.fract]; push_cast; ring
  have ht : rv t = rv (fun i => Int.fract (t i)) + cv (fun i => ⌊t i⌋) := by
    funext i; simp only [rv, cv, Pi.add_apply, Int.fract]; push_cast; ring
  rw [hs, ht, perV, Matrix.mulVec_add]
  abel

/- English proof (translation)
Establish `hrv : Continuous (fun s : Fin g → ℝ => rv s)` using `continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)`. Establish `hΦ : Continuous (fun p : (Fin g → ℝ) × (Fin g → ℝ) => rv p.1 + d.τ *ᵥ rv p.2)` using `(hrv.comp continuous_fst).add (continuous_const.matrix_mulVec (hrv.comp continuous_snd))`. Establish `hK : IsCompact ((Set.univ.pi fun _ : Fin g => Set.Icc (0 : ℝ) 1) ×ˢ (Set.univ.pi fun _ : Fin g => Set.Icc (0 : ℝ) 1))` using `(isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)`. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn (hc.comp hΦ).continuousOn`. Use `isBounded_iff_forall_norm_le.2 ⟨C, ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨z, rfl⟩`. Take `⟨M, N, s, t, hs, ht, rfl⟩` from `exists_reduce d z`. Rewrite using `[hper]`. Conclude with `hC (s, t) ⟨fun i _ => hs i, fun i _ => ht i⟩`.
-/
theorem bounded_of_per (d : AB B g) (F : (Fin g → ℂ) → ℂ) (hc : Continuous F)
    (hper : ∀ M N z, F (z + perV d.τ M N) = F z) : Bornology.IsBounded (Set.range F) := by
  have hrv : Continuous (fun s : Fin g → ℝ => rv s) :=
    continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
  have hΦ : Continuous (fun p : (Fin g → ℝ) × (Fin g → ℝ) => rv p.1 + d.τ *ᵥ rv p.2) :=
    (hrv.comp continuous_fst).add (continuous_const.matrix_mulVec (hrv.comp continuous_snd))
  have hK : IsCompact ((Set.univ.pi fun _ : Fin g => Set.Icc (0 : ℝ) 1) ×ˢ (Set.univ.pi fun _ : Fin g => Set.Icc (0 : ℝ) 1)) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc.comp hΦ).continuousOn
  refine isBounded_iff_forall_norm_le.2 ⟨C, ?_⟩
  rintro _ ⟨z, rfl⟩
  obtain ⟨M, N, s, t, hs, ht, rfl⟩ := exists_reduce d z
  rw [hper]
  exact hC (s, t) ⟨fun i _ => hs i, fun i _ => ht i⟩

/- English proof (translation)
Introduce `x y z`. Establish `hb` using `bounded_of_per d _ (h x y).continuous (cubF_per d x y)`. Establish `e` using `(h x y).apply_eq_apply_of_bounded hb z 0`. Establish `u1` using `(d.fr (x + y + z)).ne_zero`. Establish `u2` using `(d.fr x).ne_zero`.

Establish `u3` using `(d.fr y).ne_zero`. Establish `u4` using `(d.fr z).ne_zero`. Establish `u5` using `(d.fr (x + y)).ne_zero`. Establish `h0 : cubF d x y 0 = 1`. Unfold `cubF`.

Rewrite using `[ex_zero', B.cub.face₃, add_zero, add_zero, add_zero, d.fr_zero]`. Simplify using `only [Units.val_one, _root_.one_mul, _root_.mul_one]`. Clear the denominators using the available nonvanishing facts. Rewrite `e` using `[h0]`. Unfold `cubF at e`.

Rewrite `e` using `[div_eq_one_iff_eq (by simp [u1, u2, u3, u4])]`. Apply `Units.ext` to reduce the goal to its premises. Simplify `e` using `only [Units.val_mul]`.
-/
theorem cub_of_diff (d : AB B g) (h : ∀ x y : Fin g → ℂ, Differentiable ℂ (cubF d x y)) : d.Cub := by
  intro x y z
  have hb := bounded_of_per d _ (h x y).continuous (cubF_per d x y)
  have e := (h x y).apply_eq_apply_of_bounded hb z 0
  have u1 := (d.fr (x + y + z)).ne_zero
  have u2 := (d.fr x).ne_zero
  have u3 := (d.fr y).ne_zero
  have u4 := (d.fr z).ne_zero
  have u5 := (d.fr (x + y)).ne_zero
  have h0 : cubF d x y 0 = 1 := by
    unfold cubF
    rw [ex_zero', B.cub.face₃, add_zero, add_zero, add_zero, d.fr_zero]
    simp only [Units.val_one, _root_.one_mul, _root_.mul_one]
    field_simp
  rw [h0] at e
  unfold cubF at e
  rw [div_eq_one_iff_eq (by simp [u1, u2, u3, u4])] at e
  apply Units.ext
  simpa only [Units.val_mul] using e

end Bound

/- English proof (translation)
Introduce `R _ _ _ _ D hψ hτ _ N ν g d hG`. Conclude with `cub_of_diff d (GlobalTheory.T.cubeValueTimesThetaFrames_entire R D hψ hτ N ν g d hG)`.
-/
theorem cub_of_geo : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g), Nonempty (Geo ν d) → d.Cub := by
  intro R _ _ _ _ D hψ hτ _ N ν g d hG
  exact cub_of_diff d (GlobalTheory.T.cubeValueTimesThetaFrames_entire R D hψ hτ N ν g d hG)

end GlobalTheory.MBLow.Cl
