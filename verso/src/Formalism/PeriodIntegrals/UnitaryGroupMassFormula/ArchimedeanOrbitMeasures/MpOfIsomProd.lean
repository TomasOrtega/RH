import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetMulRCReal

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix ComplexConjugate

section Iso

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Establish `hinj : Function.Injective f`. Introduce `a b hab`. Establish `h0 : ‖a - b‖ = 0` using `by rw [← hn, map_sub, hab, sub_self, norm_zero]`. Conclude with `sub_eq_zero.mp (norm_eq_zero.mp h0)`. Set `e : E ≃ₗ[ℝ] F` to `LinearEquiv.ofBijective f ⟨hinj, hs⟩`.

Set `g : E ≃ₗᵢ[ℝ] F` to `{ e with norm_map' := hn }`. Conclude with `g.measurePreserving`.
-/
theorem mp_of_isom (f : E →ₗ[ℝ] F) (hn : ∀ x, ‖f x‖ = ‖x‖) (hs : Function.Surjective f) :
    MeasurePreserving f volume volume := by
  have hinj : Function.Injective f := by
    intro a b hab
    have h0 : ‖a - b‖ = 0 := by rw [← hn, map_sub, hab, sub_self, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  let e : E ≃ₗ[ℝ] F := LinearEquiv.ofBijective f ⟨hinj, hs⟩
  let g : E ≃ₗᵢ[ℝ] F := { e with norm_map' := hn }
  exact g.measurePreserving

variable {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/- English proof (translation)
Set `L : WithLp 2 (U × V) ≃ₗ[ℝ] U × V` to `WithLp.linearEquiv 2 ℝ (U × V)`. Establish `h1 : MeasurePreserving (f.comp L.toLinearMap) volume volume`. Apply `mp_of_isom` to reduce the goal to its premises. Introduce `t`. Establish `h` using `hn (L t).1 (L t).2`.

Establish `h2` using `WithLp.prod_norm_sq_eq_of_L2 t`. Establish `e : (L t) = ((L t).1, (L t).2)` using `rfl`. Rewrite `h` using `[← e]`. Establish `h3 : ‖f (L t)‖ ^ 2 = ‖t‖ ^ 2` using `by rw [h, h2]; rfl`. Conclude with `(pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3`.

Conclude with `hs.comp L.surjective`. Establish `h2` using `WithLp.volume_preserving_toLp U V`. Establish `h3 : (⇑(f.comp L.toLinearMap) ∘ WithLp.toLp 2) = ⇑f`. Use function extensionality and compare the values at `x`. Both sides reduce to the same expression.

Establish `h4` using `h1.comp h2`. Rewrite `h4` using `[h3]`. Then use the resulting hypothesis.
-/
theorem mp_of_isom_prod (f : U × V →ₗ[ℝ] F) (hn : ∀ a b, ‖f (a, b)‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2)
    (hs : Function.Surjective f) : MeasurePreserving f volume volume := by
  let L : WithLp 2 (U × V) ≃ₗ[ℝ] U × V := WithLp.linearEquiv 2 ℝ (U × V)
  have h1 : MeasurePreserving (f.comp L.toLinearMap) volume volume := by
    apply mp_of_isom
    · intro t
      have h := hn (L t).1 (L t).2
      have h2 := WithLp.prod_norm_sq_eq_of_L2 t
      have e : (L t) = ((L t).1, (L t).2) := rfl
      rw [← e] at h
      have h3 : ‖f (L t)‖ ^ 2 = ‖t‖ ^ 2 := by rw [h, h2]; rfl
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3
    · exact hs.comp L.surjective
  have h2 := WithLp.volume_preserving_toLp U V
  have h3 : (⇑(f.comp L.toLinearMap) ∘ WithLp.toLp 2) = ⇑f := by
    funext x
    rfl
  have h4 := h1.comp h2
  rwa [h3] at h4

end Iso

def reimL {n m : ℕ} : Matrix (Fin n) (Fin m) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin m × Bool) where
  toFun := reim
  map_add' Y Z := by
    ext p
    rcases p with ⟨i, j, s⟩
    cases s <;> simp [reim]
  map_smul' c Y := by
    ext p
    rcases p with ⟨i, j, s⟩
    cases s <;> simp [reim]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem reimL_apply {n m : ℕ} (Y : Matrix (Fin n) (Fin m) ℂ) : reimL Y = reim Y := rfl

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]`. Simplify using `only [reim, Fintype.sum_prod_type, Fintype.sum_bool]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_reim_sq {n m : ℕ} (Y : Matrix (Fin n) (Fin m) ℂ) :
    ‖reim Y‖ ^ 2 = ∑ i, ∑ j, ‖Y i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp only [reim, Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/- English proof (translation)
Use `⟨Matrix.of fun i j => ⟨y.ofLp (i, j, true), y.ofLp (i, j, false)⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `p`. Break down `p with ⟨i, j, s⟩` into its components or cases. Apply the tactic sequence `cases s <;> simp [reim]`.
-/
theorem reim_surj {n m : ℕ} (y : EuclideanSpace ℝ (Fin n × Fin m × Bool)) :
    ∃ Y : Matrix (Fin n) (Fin m) ℂ, reim Y = y := by
  refine ⟨Matrix.of fun i j => ⟨y.ofLp (i, j, true), y.ofLp (i, j, false)⟩, ?_⟩
  ext p
  rcases p with ⟨i, j, s⟩
  cases s <;> simp [reim]

/- English proof (translation)
Establish `hA' : ∀ i j, A j i = conj (A i j)` using `fun i j => by`. Simplify `(congrFun (congrFun hA j) i).symm` using `[Matrix.conjTranspose_apply]`. Establish `hB' : ∀ i j, B j i = conj (B i j)` using `fun i j => by`. Simplify `(congrFun (congrFun hB j) i).symm` using `[Matrix.conjTranspose_apply]`. Establish `hc : conj (∑ i, ∑ j, A i j * conj (B i j)) = ∑ i, ∑ j, A i j * conj (B i j)`.

Simplify using `only [map_sum, map_mul, Complex.conj_conj]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hA' j i, hB' j i, Complex.conj_conj]`. Conclude with `Complex.conj_eq_iff_im.mp hc`.
-/
theorem herm_cross {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    (∑ i, ∑ j, A i j * conj (B i j)).im = 0 := by
  have hA' : ∀ i j, A j i = conj (A i j) := fun i j => by
    simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun hA j) i).symm
  have hB' : ∀ i j, B j i = conj (B i j) := fun i j => by
    simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun hB j) i).symm
  have hc : conj (∑ i, ∑ j, A i j * conj (B i j)) = ∑ i, ∑ j, A i j * conj (B i j) := by
    simp only [map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hA' j i, hB' j i, Complex.conj_conj]
  exact Complex.conj_eq_iff_im.mp hc

/- English proof (translation)
Establish `key : ∀ i j, ‖(Complex.I • A + B) i j‖ ^ 2 = ‖A i j‖ ^ 2 + ‖B i j‖ ^ 2 - 2 * (A i j * conj (B i j)).im`. Introduce `i j`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree. Establish `h0` using `herm_cross A B hA hB`.

Simplify using `only [Complex.im_sum] at h0`. Simplify using `only [key, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, h0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_pyth {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    ∑ i, ∑ j, ‖(Complex.I • A + B) i j‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 + ∑ i, ∑ j, ‖B i j‖ ^ 2 := by
  have key : ∀ i j, ‖(Complex.I • A + B) i j‖ ^ 2 =
      ‖A i j‖ ^ 2 + ‖B i j‖ ^ 2 - 2 * (A i j * conj (B i j)).im := by
    intro i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.sq_norm,
      Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
    ring
  have h0 := herm_cross A B hA hB
  simp only [Complex.im_sum] at h0
  simp only [key, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, h0]
  ring

def psiLp {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ) :
    EuclideanSpace ℝ η × EuclideanSpace ℝ η →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) where
  toFun z := reimL (Complex.I • H z.1 + H z.2)
  map_add' a b := by
    show reimL (Complex.I • H (a + b).1 + H (a + b).2) =
      reimL (Complex.I • H a.1 + H a.2) + reimL (Complex.I • H b.1 + H b.2)
    rw [← map_add]
    congr 1
    simp only [Prod.fst_add, Prod.snd_add, map_add, smul_add]
    abel
  map_smul' c z := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply]
    rw [smul_comm Complex.I c, ← smul_add, map_smul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem psiLp_apply {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (z : EuclideanSpace ℝ η × EuclideanSpace ℝ η) : psiLp H z = reim (Complex.I • H z.1 + H z.2) := rfl

/- English proof (translation)
Apply `mp_of_isom_prod` to reduce the goal to its premises. Introduce `a b`. Rewrite using `[psiLp_apply, norm_reim_sq, herm_pyth _ _ (hH a) (hH b), hn a, hn b]`. Introduce `y`. Take `⟨Y, rfl⟩` from `reim_surj y`.

Use `set A : Matrix (Fin m) (Fin m) ℂ := (-(Complex.I / 2)) • (Y - Yᴴ) with hAdef`. Use `set B : Matrix (Fin m) (Fin m) ℂ := (1 / 2 : ℂ) • (Y + Yᴴ) with hBdef`. Establish `hA : Aᴴ = A`. Rewrite using `[hAdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]`. Use extensionality with `i j`.

Simplify using `[Complex.ext_iff]`. Apply the tactic sequence `constructor <;> ring`. Establish `hB : Bᴴ = B`. Rewrite using `[hBdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]`. Use extensionality with `i j`.

Simplify using `[Complex.ext_iff]`. Apply the tactic sequence `constructor <;> ring`. Take `⟨s, hsA⟩` from `hs A hA`. Take `⟨t, htB⟩` from `hs B hB`. Use `⟨(s, t), ?_⟩` and prove the remaining obligations.

Rewrite using `[psiLp_apply]`. Use `congr 1`. Simplify using `only [hsA, htB]`. Use extensionality with `i j`. Simplify using `[hAdef, hBdef, Complex.ext_iff]`.

Apply the tactic sequence `constructor <;> ring`.
-/
theorem psi_mp {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (hH : ∀ t, (H t)ᴴ = H t) (hn : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2)
    (hs : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) :
    MeasurePreserving (psiLp H) volume volume := by
  apply mp_of_isom_prod
  · intro a b
    rw [psiLp_apply, norm_reim_sq, herm_pyth _ _ (hH a) (hH b), hn a, hn b]
  · intro y
    obtain ⟨Y, rfl⟩ := reim_surj y
    set A : Matrix (Fin m) (Fin m) ℂ := (-(Complex.I / 2)) • (Y - Yᴴ) with hAdef
    set B : Matrix (Fin m) (Fin m) ℂ := (1 / 2 : ℂ) • (Y + Yᴴ) with hBdef
    have hA : Aᴴ = A := by
      rw [hAdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_conjTranspose]
      ext i j
      simp [Complex.ext_iff]
      constructor <;> ring
    have hB : Bᴴ = B := by
      rw [hBdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
        Matrix.conjTranspose_conjTranspose]
      ext i j
      simp [Complex.ext_iff]
      constructor <;> ring
    obtain ⟨s, hsA⟩ := hs A hA
    obtain ⟨t, htB⟩ := hs B hB
    refine ⟨(s, t), ?_⟩
    rw [psiLp_apply]
    congr 1
    simp only [hsA, htB]
    ext i j
    simp [hAdef, hBdef, Complex.ext_iff]
    constructor <;> ring

end PI.AprimeInfW
