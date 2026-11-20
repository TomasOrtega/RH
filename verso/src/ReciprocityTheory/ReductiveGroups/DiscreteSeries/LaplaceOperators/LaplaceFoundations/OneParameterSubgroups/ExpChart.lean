import Mathlib

open MeasureTheory Filter Topology Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N

section Abstract
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- English proof (translation)
Set `b` to `Module.finBasis ℝ E`. Set `N : E →ₗ[ℝ] E` to `(D : E →ₗ[ℝ] E) - LinearMap.id`. Establish `hNpow : ∀ k, ∀ x, (N ^ k) x ∈ G k`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => intro x`. Rewrite using `[hG0]`. Conclude with `Submodule.mem_top`. Consider the case `succ k ih`. Introduce `x`.

Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `hD k _ (ih x)`. Establish `hnil : IsNilpotent N`. Use `⟨L, LinearMap.ext fun x => ?_⟩` and prove the remaining obligations. Establish `h` using `hNpow L x`.

Rewrite `h` using `[hL, Submodule.mem_bot]`. Rewrite using `[LinearMap.zero_apply]`. Conclude with `h`. Establish `hpowM : ∀ k, (LinearMap.toMatrix b b N) ^ k = LinearMap.toMatrix b b (N ^ k)`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero, pow_zero]`. Conclude with `(LinearMap.toMatrix_one b).symm`. Consider the case `succ k ih => rw [pow_succ, pow_succ, LinearMap.toMatrix_mul, ih]`. Establish `hM : IsNilpotent (LinearMap.toMatrix b b N)`.

Take `⟨k, hk⟩` from `hnil`. Conclude with `⟨k, by rw [hpowM, hk, map_zero]⟩`. Establish `key : ∀ M : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ, IsNilpotent M → (1 + M).det = 1`. Introduce `M hM`. Establish `hch : M.charpoly = Polynomial.X ^ Fintype.card (Fin (Module.finrank ℝ E))` using `sub_eq_zero.mp (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hM).eq_zero`.

Establish `hmat : (Matrix.charmatrix M).map (Polynomial.eval (-1 : ℝ)) = -(1 + M)`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `only [Matrix.map_apply, Matrix.charmatrix_apply, Matrix.diagonal_apply_eq, Matrix.neg_apply, Matrix.add_apply, Matrix.one_apply_eq, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Matrix.map_apply, Matrix.charmatrix_apply, Matrix.diagonal_apply_ne _ h, Matrix.neg_apply, Matrix.add_apply, Matrix.one_apply_ne h, Polynomial.eval_sub, Polynomial.eval_zero, Polynomial.eval_C]`. Expand and normalize the polynomial expressions, which then agree. Establish `hev : Polynomial.eval (-1 : ℝ) M.charpoly = (-(1 + M)).det`. Rewrite using `[← hmat, Matrix.charpoly, ← Polynomial.coe_evalRingHom, RingHom.map_det, RingHom.mapMatrix_apply]`.

Rewrite `hev` using `[hch, Matrix.det_neg, Polynomial.eval_pow, Polynomial.eval_X]`. Establish `hne : ((-1 : ℝ)) ^ Fintype.card (Fin (Module.finrank ℝ E)) ≠ 0` using `pow_ne_zero _ (by norm_num)`. Conclude with `mul_left_cancel₀ hne (hev.symm.trans (mul_one _).symm)`. Establish `hD' : LinearMap.toMatrix b b (D : E →ₗ[ℝ] E) = 1 + LinearMap.toMatrix b b N`. Rewrite using `[← LinearMap.toMatrix_id b, ← map_add]`.

Use `congr 1`. Use extensionality with `x`. Simplify using `[N]`. Use `show LinearMap.det (D : E →ₗ[ℝ] E) = 1`. Rewrite using `[← LinearMap.det_toMatrix b, hD']`.

Conclude with `key _ hM`.
-/
theorem det_of_shear (G : ℕ → Submodule ℝ E) (L : ℕ) (hG0 : G 0 = ⊤) (hL : G L = ⊥)
    (D : E →L[ℝ] E) (hD : ∀ j, ∀ x ∈ G j, D x - x ∈ G (j + 1)) : D.det = 1 := by
  let b := Module.finBasis ℝ E
  let N : E →ₗ[ℝ] E := (D : E →ₗ[ℝ] E) - LinearMap.id
  have hNpow : ∀ k, ∀ x, (N ^ k) x ∈ G k := by
    intro k
    induction k with
    | zero => intro x; rw [hG0]; exact Submodule.mem_top
    | succ k ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply]
      exact hD k _ (ih x)
  have hnil : IsNilpotent N := by
    refine ⟨L, LinearMap.ext fun x => ?_⟩
    have h := hNpow L x
    rw [hL, Submodule.mem_bot] at h
    rw [LinearMap.zero_apply]
    exact h
  have hpowM : ∀ k, (LinearMap.toMatrix b b N) ^ k = LinearMap.toMatrix b b (N ^ k) := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero]; exact (LinearMap.toMatrix_one b).symm
    | succ k ih => rw [pow_succ, pow_succ, LinearMap.toMatrix_mul, ih]
  have hM : IsNilpotent (LinearMap.toMatrix b b N) := by
    obtain ⟨k, hk⟩ := hnil
    exact ⟨k, by rw [hpowM, hk, map_zero]⟩
  have key : ∀ M : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ,
      IsNilpotent M → (1 + M).det = 1 := by
    intro M hM
    have hch : M.charpoly = Polynomial.X ^ Fintype.card (Fin (Module.finrank ℝ E)) :=
      sub_eq_zero.mp (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hM).eq_zero
    have hmat : (Matrix.charmatrix M).map (Polynomial.eval (-1 : ℝ)) = -(1 + M) := by
      ext i j
      by_cases h : i = j
      · subst h
        simp only [Matrix.map_apply, Matrix.charmatrix_apply, Matrix.diagonal_apply_eq,
          Matrix.neg_apply, Matrix.add_apply, Matrix.one_apply_eq, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C]
        ring
      · simp only [Matrix.map_apply, Matrix.charmatrix_apply, Matrix.diagonal_apply_ne _ h,
          Matrix.neg_apply, Matrix.add_apply, Matrix.one_apply_ne h, Polynomial.eval_sub,
          Polynomial.eval_zero, Polynomial.eval_C]
        ring
    have hev : Polynomial.eval (-1 : ℝ) M.charpoly = (-(1 + M)).det := by
      rw [← hmat, Matrix.charpoly, ← Polynomial.coe_evalRingHom, RingHom.map_det,
        RingHom.mapMatrix_apply]
    rw [hch, Matrix.det_neg, Polynomial.eval_pow, Polynomial.eval_X] at hev
    have hne : ((-1 : ℝ)) ^ Fintype.card (Fin (Module.finrank ℝ E)) ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    exact mul_left_cancel₀ hne (hev.symm.trans (mul_one _).symm)
  have hD' : LinearMap.toMatrix b b (D : E →ₗ[ℝ] E) = 1 + LinearMap.toMatrix b b N := by
    rw [← LinearMap.toMatrix_id b, ← map_add]
    congr 1
    ext x
    simp [N]
  show LinearMap.det (D : E →ₗ[ℝ] E) = 1
  rw [← LinearMap.det_toMatrix b, hD']
  exact key _ hM

variable [MeasurableSpace E] [BorelSpace E]

/- English proof (translation)
Establish `hD : ∀ x, ∀ j, ∀ v ∈ G j, fderiv ℝ Φ x v - v ∈ G (j + 1)`. Introduce `x j v hv`. Establish `h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0`. Simplify using `using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x`. Establish `h2 : HasFDerivAt Φ (fderiv ℝ Φ x) ((fun t : ℝ => x + t • v) 0)`.

Simplify using `using (hΦ x).hasFDerivAt`. Establish `hd` using `h2.comp_hasDerivAt (0 : ℝ) h1`. Establish `hS : IsClosed {w : E | w - v ∈ G (j + 1)}` using `(Submodule.closed_of_finiteDimensional (G (j + 1))).preimage (continuous_id.sub continuous_const)`. Use `hS.mem_of_tendsto hd.tendsto_slope_zero (eventually_nhdsWithin_of_forall fun t ht => ?_)` and prove the remaining obligations. Establish `ht0 : t ≠ 0` using `Set.mem_compl_singleton_iff.mp ht`.

Establish `hmem` using `hsh j (x + t • v) x (by rw [add_sub_cancel_left]; exact (G j).smul_mem t hv)`. Rewrite `hmem` using `[add_sub_cancel_left]`. Use `show t⁻¹ • ((Φ ∘ fun t : ℝ => x + t • v) (0 + t) - (Φ ∘ fun t : ℝ => x + t • v) 0) - v ∈ G (j + 1)`. Establish `e : t⁻¹ • ((Φ ∘ fun t : ℝ => x + t • v) (0 + t) - (Φ ∘ fun t : ℝ => x + t • v) 0) - v = t⁻¹ • (Φ (x + t • v) - Φ x - t • v)`. Simplify using `only [Function.comp_apply, zero_add, zero_smul, add_zero, smul_sub, smul_smul, inv_mul_cancel₀ ht0, one_smul]`.

Establish `hm2` using `(G (j + 1)).smul_mem t⁻¹ hmem`. Rewrite `hm2` using `[← e]`. Conclude with `hm2`. Establish `hmeas : Measurable Φ` using `hΦ.continuous.measurable`. Use `⟨hmeas, ?_⟩` and prove the remaining obligations.

Establish `key` using `MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar μ MeasurableSet.univ (f' := fderiv ℝ Φ) (fun x _ => (hΦ x).hasFDerivAt.hasFDerivWithinAt) hbij.1.injOn`. Establish `hdet : (fun x => ENNReal.ofReal |(fderiv ℝ Φ x).det|) = fun _ => 1`. Use function extensionality and compare the values at `x`. Rewrite using `[det_of_shear G L hG0 hL _ (hD x), abs_one, ENNReal.ofReal_one]`. Rewrite `key` using `[hdet]`.

Establish `key' : Measure.map Φ ((μ.restrict (Set.univ : Set E)).withDensity fun _ => (1 : ENNReal)) = μ.restrict (Φ '' (Set.univ : Set E))` using `key`. Establish `h1 : μ.withDensity (fun _ => (1 : ENNReal)) = μ` using `withDensity_one`. Rewrite `key'` using `[Measure.restrict_univ, Set.image_univ, hbij.2.range_eq, Measure.restrict_univ, h1]`. Conclude with `key'`.
-/
theorem shear_preserving (μ : Measure E) [μ.IsAddHaarMeasure] (G : ℕ → Submodule ℝ E) (L : ℕ)
    (hG0 : G 0 = ⊤) (hL : G L = ⊥) (Φ : E → E) (hΦ : Differentiable ℝ Φ)
    (hbij : Function.Bijective Φ)
    (hsh : ∀ j x y, x - y ∈ G j → Φ x - Φ y - (x - y) ∈ G (j + 1)) : MeasurePreserving Φ μ μ := by
  have hD : ∀ x, ∀ j, ∀ v ∈ G j, fderiv ℝ Φ x v - v ∈ G (j + 1) := by
    intro x j v hv
    have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    have h2 : HasFDerivAt Φ (fderiv ℝ Φ x) ((fun t : ℝ => x + t • v) 0) := by
      simpa using (hΦ x).hasFDerivAt
    have hd := h2.comp_hasDerivAt (0 : ℝ) h1
    have hS : IsClosed {w : E | w - v ∈ G (j + 1)} :=
      (Submodule.closed_of_finiteDimensional (G (j + 1))).preimage (continuous_id.sub continuous_const)
    refine hS.mem_of_tendsto hd.tendsto_slope_zero (eventually_nhdsWithin_of_forall fun t ht => ?_)
    have ht0 : t ≠ 0 := Set.mem_compl_singleton_iff.mp ht
    have hmem := hsh j (x + t • v) x (by rw [add_sub_cancel_left]; exact (G j).smul_mem t hv)
    rw [add_sub_cancel_left] at hmem
    show t⁻¹ • ((Φ ∘ fun t : ℝ => x + t • v) (0 + t) - (Φ ∘ fun t : ℝ => x + t • v) 0) - v ∈ G (j + 1)
    have e : t⁻¹ • ((Φ ∘ fun t : ℝ => x + t • v) (0 + t) - (Φ ∘ fun t : ℝ => x + t • v) 0) - v =
        t⁻¹ • (Φ (x + t • v) - Φ x - t • v) := by
      simp only [Function.comp_apply, zero_add, zero_smul, add_zero, smul_sub, smul_smul,
        inv_mul_cancel₀ ht0, one_smul]
    have hm2 := (G (j + 1)).smul_mem t⁻¹ hmem
    rw [← e] at hm2
    exact hm2
  have hmeas : Measurable Φ := hΦ.continuous.measurable
  refine ⟨hmeas, ?_⟩
  have key := MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar μ MeasurableSet.univ
    (f' := fderiv ℝ Φ) (fun x _ => (hΦ x).hasFDerivAt.hasFDerivWithinAt) hbij.1.injOn
  have hdet : (fun x => ENNReal.ofReal |(fderiv ℝ Φ x).det|) = fun _ => 1 := by
    funext x
    rw [det_of_shear G L hG0 hL _ (hD x), abs_one, ENNReal.ofReal_one]
  rw [hdet] at key
  have key' : Measure.map Φ ((μ.restrict (Set.univ : Set E)).withDensity fun _ => (1 : ENNReal)) =
      μ.restrict (Φ '' (Set.univ : Set E)) := key
  have h1 : μ.withDensity (fun _ => (1 : ENNReal)) = μ := withDensity_one
  rw [Measure.restrict_univ, Set.image_univ, hbij.2.range_eq, Measure.restrict_univ, h1] at key'
  exact key'

end Abstract

section Fil
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

structure IsFil (F : ℕ → Submodule ℝ A) (L : ℕ) : Prop where
  anti : ∀ i j, i ≤ j → F j ≤ F i
  mul : ∀ i j x y, x ∈ F i → y ∈ F j → x * y ∈ F (i + j + 1)
  bot : F L = ⊥

def IsShear (F : ℕ → Submodule ℝ A) (f : A → A) : Prop :=
  (∀ x ∈ F 0, f x ∈ F 0) ∧
    ∀ j, ∀ x ∈ F 0, ∀ y ∈ F 0, x - y ∈ F j → f x - f y - (x - y) ∈ F (j + 1)

def iter (f : A → A) : ℕ → A → A
  | 0, _ => 0
  | i + 1, z => iter f i z + (z - f (iter f i z))

variable {F : ℕ → Submodule ℝ A} {L : ℕ} {f g : A → A}

/- English proof (translation)
Establish `key : ∀ j, x - y ∈ F j`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => exact (F 0).sub_mem hx hy`. Consider the case `succ j ih`.

Establish `h1` using `hf.2 j x hx y hy ih`. Rewrite `h1` using `[h, sub_self, zero_sub]`. Simplify using `using (F (j + 1)).neg_mem h1`. Establish `h2` using `key L`. Rewrite `h2` using `[hF.bot, Submodule.mem_bot, sub_eq_zero]`.

Conclude with `h2`.
-/
theorem IsShear.inj (hF : IsFil F L) (hf : IsShear F f) {x y : A} (hx : x ∈ F 0) (hy : y ∈ F 0)
    (h : f x = f y) : x = y := by
  have key : ∀ j, x - y ∈ F j := by
    intro j
    induction j with
    | zero => exact (F 0).sub_mem hx hy
    | succ j ih =>
      have h1 := hf.2 j x hx y hy ih
      rw [h, sub_self, zero_sub] at h1
      simpa using (F (j + 1)).neg_mem h1
  have h2 := key L
  rw [hF.bot, Submodule.mem_bot, sub_eq_zero] at h2
  exact h2

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => show (0 : A) ∈ F 0 ∧ z - f 0 ∈ F 0`. Conclude with `⟨(F 0).zero_mem, (F 0).sub_mem hz (hf.1 _ (F 0).zero_mem)⟩`. Consider the case `succ i ih`.

Take `⟨hw, hr⟩` from `ih`. Establish `hfw : f (iter f i z) ∈ F 0` using `hf.1 _ hw`. Establish `hr0 : z - f (iter f i z) ∈ F 0` using `(F 0).sub_mem hz hfw`. Establish `hw' : iter f (i + 1) z ∈ F 0` using `(F 0).add_mem hw hr0`. Use `⟨hw', ?_⟩` and prove the remaining obligations.

Establish `hd : iter f (i + 1) z - iter f i z ∈ F i` using `by show iter f i z + (z - f (iter f i z)) - iter f i z ∈ F i`. Simplify using `using hr`. Establish `h2` using `hf.2 i (iter f (i + 1) z) hw' (iter f i z) hw hd`. Establish `h3 : z - f (iter f (i + 1) z) = -(f (iter f (i + 1) z) - f (iter f i z) - (iter f (i + 1) z - iter f i z))` using `by show z - f (iter f (i + 1) z) = -(f (iter f (i + 1) z) - f (iter f i z) - (iter f i z + (z - f (iter f i z)) - iter f i z))`. Normalize the expressions using the abelian group laws.

Rewrite using `[h3]`. Conclude with `(F (i + 1)).neg_mem h2`.
-/
theorem IsShear.iter_mem (hf : IsShear F f) {z : A} (hz : z ∈ F 0) :
    ∀ i, iter f i z ∈ F 0 ∧ z - f (iter f i z) ∈ F i := by
  intro i
  induction i with
  | zero =>
    show (0 : A) ∈ F 0 ∧ z - f 0 ∈ F 0
    exact ⟨(F 0).zero_mem, (F 0).sub_mem hz (hf.1 _ (F 0).zero_mem)⟩
  | succ i ih =>
    obtain ⟨hw, hr⟩ := ih
    have hfw : f (iter f i z) ∈ F 0 := hf.1 _ hw
    have hr0 : z - f (iter f i z) ∈ F 0 := (F 0).sub_mem hz hfw
    have hw' : iter f (i + 1) z ∈ F 0 := (F 0).add_mem hw hr0
    refine ⟨hw', ?_⟩
    have hd : iter f (i + 1) z - iter f i z ∈ F i := by
      show iter f i z + (z - f (iter f i z)) - iter f i z ∈ F i
      simpa using hr
    have h2 := hf.2 i (iter f (i + 1) z) hw' (iter f i z) hw hd
    have h3 : z - f (iter f (i + 1) z) = -(f (iter f (i + 1) z) - f (iter f i z) - (iter f (i + 1) z - iter f i z)) := by
      show z - f (iter f (i + 1) z) = -(f (iter f (i + 1) z) - f (iter f i z) - (iter f i z + (z - f (iter f i z)) - iter f i z))
      abel
    rw [h3]
    exact (F (i + 1)).neg_mem h2

/- English proof (translation)
Establish `h` using `(IsShear.iter_mem hf hz L).2`. Rewrite `h` using `[hF.bot, Submodule.mem_bot, sub_eq_zero]`. Conclude with `h.symm`.
-/
theorem IsShear.right_inv (hF : IsFil F L) (hf : IsShear F f) {z : A} (hz : z ∈ F 0) :
    f (iter f L z) = z := by
  have h := (IsShear.iter_mem hf hz L).2
  rw [hF.bot, Submodule.mem_bot, sub_eq_zero] at h
  exact h.symm

/- English proof (translation)
Establish `hfx : f x ∈ F 0` using `hf.1 x hx`. Conclude with `IsShear.inj hF hf (IsShear.iter_mem hf hfx L).1 hx (IsShear.right_inv hF hf hfx)`.
-/
theorem IsShear.left_inv (hF : IsFil F L) (hf : IsShear F f) {x : A} (hx : x ∈ F 0) :
    iter f L (f x) = x := by
  have hfx : f x ∈ F 0 := hf.1 x hx
  exact IsShear.inj hF hf (IsShear.iter_mem hf hfx L).1 hx (IsShear.right_inv hF hf hfx)

/- English proof (translation)
Use `⟨fun z hz => (IsShear.iter_mem hf hz L).1, ?_⟩` and prove the remaining obligations. Introduce `j x hx y hy hxy`. Establish `hu0 : iter f L x ∈ F 0` using `(IsShear.iter_mem hf hx L).1`. Establish `hv0 : iter f L y ∈ F 0` using `(IsShear.iter_mem hf hy L).1`. Establish `hfu : f (iter f L x) = x` using `IsShear.right_inv hF hf hx`.

Establish `hfv : f (iter f L y) = y` using `IsShear.right_inv hF hf hy`. Establish `key : ∀ k, k ≤ j → iter f L x - iter f L y ∈ F k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _`.

Conclude with `(F 0).sub_mem hu0 hv0`. Consider the case `succ k ih`. Introduce `hk`. Establish `h1` using `hf.2 k _ hu0 _ hv0 (ih (by omega))`. Rewrite `h1` using `[hfu, hfv]`.

Establish `h2 : x - y ∈ F (k + 1)` using `hF.anti (k + 1) j hk hxy`. Establish `h3 : iter f L x - iter f L y = (x - y) - (x - y - (iter f L x - iter f L y))` using `by abel`. Rewrite using `[h3]`. Conclude with `(F (k + 1)).sub_mem h2 h1`. Establish `h1` using `hf.2 j _ hu0 _ hv0 (key j le_rfl)`.

Rewrite `h1` using `[hfu, hfv]`. Establish `h3 : iter f L x - iter f L y - (x - y) = -(x - y - (iter f L x - iter f L y))` using `by abel`. Rewrite using `[h3]`. Conclude with `(F (j + 1)).neg_mem h1`.
-/
theorem IsShear.inv (hF : IsFil F L) (hf : IsShear F f) : IsShear F (iter f L) := by
  refine ⟨fun z hz => (IsShear.iter_mem hf hz L).1, ?_⟩
  intro j x hx y hy hxy
  have hu0 : iter f L x ∈ F 0 := (IsShear.iter_mem hf hx L).1
  have hv0 : iter f L y ∈ F 0 := (IsShear.iter_mem hf hy L).1
  have hfu : f (iter f L x) = x := IsShear.right_inv hF hf hx
  have hfv : f (iter f L y) = y := IsShear.right_inv hF hf hy
  have key : ∀ k, k ≤ j → iter f L x - iter f L y ∈ F k := by
    intro k
    induction k with
    | zero => intro _; exact (F 0).sub_mem hu0 hv0
    | succ k ih =>
      intro hk
      have h1 := hf.2 k _ hu0 _ hv0 (ih (by omega))
      rw [hfu, hfv] at h1
      have h2 : x - y ∈ F (k + 1) := hF.anti (k + 1) j hk hxy
      have h3 : iter f L x - iter f L y = (x - y) - (x - y - (iter f L x - iter f L y)) := by abel
      rw [h3]
      exact (F (k + 1)).sub_mem h2 h1
  have h1 := hf.2 j _ hu0 _ hv0 (key j le_rfl)
  rw [hfu, hfv] at h1
  have h3 : iter f L x - iter f L y - (x - y) = -(x - y - (iter f L x - iter f L y)) := by abel
  rw [h3]
  exact (F (j + 1)).neg_mem h1

/- English proof (translation)
Use `⟨fun x hx => hf.1 _ (hg.1 x hx), ?_⟩` and prove the remaining obligations. Introduce `j x hx y hy hxy`. Use `show f (g x) - f (g y) - (x - y) ∈ F (j + 1)`. Establish `h1` using `hg.2 j x hx y hy hxy`. Establish `hgxy : g x - g y ∈ F j`.

Establish `h2 : g x - g y = (g x - g y - (x - y)) + (x - y)` using `by abel`. Rewrite using `[h2]`. Conclude with `(F j).add_mem (hF.anti j (j + 1) (Nat.le_succ j) h1) hxy`. Establish `h3` using `hf.2 j (g x) (hg.1 x hx) (g y) (hg.1 y hy) hgxy`. Establish `h4 : f (g x) - f (g y) - (x - y) = (f (g x) - f (g y) - (g x - g y)) + (g x - g y - (x - y))` using `by abel`.

Rewrite using `[h4]`. Conclude with `(F (j + 1)).add_mem h3 h1`.
-/
theorem IsShear.comp (hF : IsFil F L) (hf : IsShear F f) (hg : IsShear F g) : IsShear F (f ∘ g) := by
  refine ⟨fun x hx => hf.1 _ (hg.1 x hx), ?_⟩
  intro j x hx y hy hxy
  show f (g x) - f (g y) - (x - y) ∈ F (j + 1)
  have h1 := hg.2 j x hx y hy hxy
  have hgxy : g x - g y ∈ F j := by
    have h2 : g x - g y = (g x - g y - (x - y)) + (x - y) := by abel
    rw [h2]
    exact (F j).add_mem (hF.anti j (j + 1) (Nat.le_succ j) h1) hxy
  have h3 := hf.2 j (g x) (hg.1 x hx) (g y) (hg.1 y hy) hgxy
  have h4 : f (g x) - f (g y) - (x - y) = (f (g x) - f (g y) - (g x - g y)) + (g x - g y - (x - y)) := by abel
  rw [h4]
  exact (F (j + 1)).add_mem h3 h1

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Establish `h : iter f 0 = fun _ => (0 : A)` using `funext fun _ => rfl`. Rewrite using `[h]`.

Conclude with `differentiable_const 0`. Consider the case `succ i ih`. Establish `h : iter f (i + 1) = fun z => iter f i z + (z - f (iter f i z))` using `funext fun _ => rfl`. Rewrite using `[h]`. Conclude with `ih.add (differentiable_id.sub (hf.comp ih))`.
-/
theorem iter_differentiable (hf : Differentiable ℝ f) : ∀ i, Differentiable ℝ (iter f i) := by
  intro i
  induction i with
  | zero =>
    have h : iter f 0 = fun _ => (0 : A) := funext fun _ => rfl
    rw [h]
    exact differentiable_const 0
  | succ i ih =>
    have h : iter f (i + 1) = fun z => iter f i z + (z - f (iter f i z)) := funext fun _ => rfl
    rw [h]
    exact ih.add (differentiable_id.sub (hf.comp ih))

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero`. Use `⟨0, 0, le_refl 0, fun z _ => ?_⟩` and prove the remaining obligations. Use `show ‖(0 : A)‖ ≤ 0 * ‖z‖ * (1 + ‖z‖) ^ 0`. Simplify using the standard rewrite rules.

Consider the case `succ i ih`. Take `⟨C, M, hC, hbd⟩` from `ih`. Establish `hK : 0 ≤ Cf * C * (1 + C) ^ Mf` using `mul_nonneg (mul_nonneg hCf hC) (pow_nonneg (by linarith) Mf)`. Use `⟨C + 1 + Cf * C * (1 + C) ^ Mf, M + (M + 1) * Mf, by linarith, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hw0 : iter f i z ∈ F 0` using `(IsShear.iter_mem hf hz i).1`.

Establish `hw : ‖iter f i z‖ ≤ C * ‖z‖ * (1 + ‖z‖) ^ M` using `hbd z hz`. Establish `hfw : ‖f (iter f i z)‖ ≤ Cf * ‖iter f i z‖ * (1 + ‖iter f i z‖) ^ Mf` using `hb _ hw0`. Establish `ht : 0 ≤ ‖z‖` using `norm_nonneg _`. Establish `hp : 1 ≤ 1 + ‖z‖` using `by linarith`. Establish `hQ1 : 1 ≤ (1 + ‖z‖) ^ (M + 1)` using `one_le_pow₀ hp`.

Establish `hR : 1 ≤ (1 + ‖z‖) ^ ((M + 1) * Mf)` using `one_le_pow₀ hp`. Establish `hQ : 1 ≤ (1 + ‖z‖) ^ M` using `one_le_pow₀ hp`. Establish `hwp : ‖iter f i z‖ ≤ C * (1 + ‖z‖) ^ (M + 1)`. Establish `e : C * (1 + ‖z‖) ^ (M + 1) = C * (1 + ‖z‖) * (1 + ‖z‖) ^ M` using `by ring`. Rewrite using `[e]`.

Conclude with `hw.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC) (by positivity))`. Establish `h1w : 1 + ‖iter f i z‖ ≤ (1 + C) * (1 + ‖z‖) ^ (M + 1)` using `by nlinarith`. Establish `hpow : (1 + ‖iter f i z‖) ^ Mf ≤ (1 + C) ^ Mf * (1 + ‖z‖) ^ ((M + 1) * Mf)`. Rewrite using `[pow_mul, ← mul_pow]`. Conclude with `pow_le_pow_left₀ (by positivity) h1w Mf`.

Establish `hfw2 : ‖f (iter f i z)‖ ≤ Cf * (C * ‖z‖ * (1 + ‖z‖) ^ M) * ((1 + C) ^ Mf * (1 + ‖z‖) ^ ((M + 1) * Mf))` using `hfw.trans (mul_le_mul (mul_le_mul_of_nonneg_left hw hCf) hpow (by positivity) (mul_nonneg hCf (mul_nonneg (mul_nonneg hC ht) (by positivity))))`. Establish `hsum : ‖iter f (i + 1) z‖ ≤ ‖iter f i z‖ + (‖z‖ + ‖f (iter f i z)‖)` using `by show ‖iter f i z + (z - f (iter f i z))‖ ≤ _`. Conclude with `(norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))`. Establish `e1 : C * ‖z‖ * (1 + ‖z‖) ^ M ≤ C * ‖z‖ * (1 + ‖z‖) ^ M * (1 + ‖z‖) ^ ((M + 1) * Mf)` using `le_mul_of_one_le_right (mul_nonneg (mul_nonneg hC ht) (by positivity)) hR`. Establish `e2 : ‖z‖ ≤ ‖z‖ * ((1 + ‖z‖) ^ M * (1 + ‖z‖) ^ ((M + 1) * Mf))` using `le_mul_of_one_le_right ht (one_le_mul_of_one_le_of_one_le hQ hR)`.

Rewrite using `[pow_add]`. Use polynomial arithmetic with `[hsum, hw, hfw2, e1, e2]`.
-/
theorem IsShear.iter_growth (hf : IsShear F f) {Cf : ℝ} {Mf : ℕ} (hCf : 0 ≤ Cf)
    (hb : ∀ x ∈ F 0, ‖f x‖ ≤ Cf * ‖x‖ * (1 + ‖x‖) ^ Mf) (i : ℕ) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ z ∈ F 0, ‖iter f i z‖ ≤ C * ‖z‖ * (1 + ‖z‖) ^ M := by
  induction i with
  | zero =>
    refine ⟨0, 0, le_refl 0, fun z _ => ?_⟩
    show ‖(0 : A)‖ ≤ 0 * ‖z‖ * (1 + ‖z‖) ^ 0
    simp
  | succ i ih =>
    obtain ⟨C, M, hC, hbd⟩ := ih
    have hK : 0 ≤ Cf * C * (1 + C) ^ Mf :=
      mul_nonneg (mul_nonneg hCf hC) (pow_nonneg (by linarith) Mf)
    refine ⟨C + 1 + Cf * C * (1 + C) ^ Mf, M + (M + 1) * Mf, by linarith, fun z hz => ?_⟩
    have hw0 : iter f i z ∈ F 0 := (IsShear.iter_mem hf hz i).1
    have hw : ‖iter f i z‖ ≤ C * ‖z‖ * (1 + ‖z‖) ^ M := hbd z hz
    have hfw : ‖f (iter f i z)‖ ≤ Cf * ‖iter f i z‖ * (1 + ‖iter f i z‖) ^ Mf := hb _ hw0
    have ht : 0 ≤ ‖z‖ := norm_nonneg _
    have hp : 1 ≤ 1 + ‖z‖ := by linarith
    have hQ1 : 1 ≤ (1 + ‖z‖) ^ (M + 1) := one_le_pow₀ hp
    have hR : 1 ≤ (1 + ‖z‖) ^ ((M + 1) * Mf) := one_le_pow₀ hp
    have hQ : 1 ≤ (1 + ‖z‖) ^ M := one_le_pow₀ hp
    have hwp : ‖iter f i z‖ ≤ C * (1 + ‖z‖) ^ (M + 1) := by
      have e : C * (1 + ‖z‖) ^ (M + 1) = C * (1 + ‖z‖) * (1 + ‖z‖) ^ M := by ring
      rw [e]
      exact hw.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC)
        (by positivity))
    have h1w : 1 + ‖iter f i z‖ ≤ (1 + C) * (1 + ‖z‖) ^ (M + 1) := by nlinarith
    have hpow : (1 + ‖iter f i z‖) ^ Mf ≤ (1 + C) ^ Mf * (1 + ‖z‖) ^ ((M + 1) * Mf) := by
      rw [pow_mul, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h1w Mf
    have hfw2 : ‖f (iter f i z)‖ ≤
        Cf * (C * ‖z‖ * (1 + ‖z‖) ^ M) * ((1 + C) ^ Mf * (1 + ‖z‖) ^ ((M + 1) * Mf)) :=
      hfw.trans (mul_le_mul (mul_le_mul_of_nonneg_left hw hCf) hpow (by positivity)
        (mul_nonneg hCf (mul_nonneg (mul_nonneg hC ht) (by positivity))))
    have hsum : ‖iter f (i + 1) z‖ ≤ ‖iter f i z‖ + (‖z‖ + ‖f (iter f i z)‖) := by
      show ‖iter f i z + (z - f (iter f i z))‖ ≤ _
      exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
    have e1 : C * ‖z‖ * (1 + ‖z‖) ^ M ≤ C * ‖z‖ * (1 + ‖z‖) ^ M * (1 + ‖z‖) ^ ((M + 1) * Mf) :=
      le_mul_of_one_le_right (mul_nonneg (mul_nonneg hC ht) (by positivity)) hR
    have e2 : ‖z‖ ≤ ‖z‖ * ((1 + ‖z‖) ^ M * (1 + ‖z‖) ^ ((M + 1) * Mf)) :=
      le_mul_of_one_le_right ht (one_le_mul_of_one_le_of_one_le hQ hR)
    rw [pow_add]
    nlinarith [hsum, hw, hfw2, e1, e2]

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using hx`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`.

Establish `h` using `hF.mul k 0 _ _ ih hx`. Rewrite `h` using `[Nat.add_zero]`. Then use the resulting hypothesis.
-/
theorem IsFil.pow_mem (hF : IsFil F L) {x : A} (hx : x ∈ F 0) : ∀ k, x ^ (k + 1) ∈ F k := by
  intro k
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ]
    have h := hF.mul k 0 _ _ ih hx
    rwa [Nat.add_zero] at h

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using h`. Consider the case `succ k ih`. Establish `e : x ^ (k + 1 + 1) - y ^ (k + 1 + 1) = (x ^ (k + 1) - y ^ (k + 1)) * x + y ^ (k + 1) * (x - y)`.

Rewrite using `[pow_succ x (k + 1), pow_succ y (k + 1), sub_mul, mul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Establish `h1` using `hF.mul (j + k) 0 _ _ ih hx`. Establish `h2` using `hF.mul k j _ _ (hF.pow_mem hy k) h`.

Rewrite `h1` using `[Nat.add_zero]`. Use `(F (j + (k + 1))).add_mem ?_ ?_` and prove the remaining obligations. Establish `e1 : j + (k + 1) = j + k + 1` using `by omega`. Rewrite using `[e1]`. Conclude with `h1`.

Establish `e2 : j + (k + 1) = k + j + 1` using `by omega`. Rewrite using `[e2]`. Conclude with `h2`.
-/
theorem IsFil.pow_sub_mem (hF : IsFil F L) {x y : A} (hx : x ∈ F 0) (hy : y ∈ F 0) {j : ℕ}
    (h : x - y ∈ F j) : ∀ k, x ^ (k + 1) - y ^ (k + 1) ∈ F (j + k) := by
  intro k
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have e : x ^ (k + 1 + 1) - y ^ (k + 1 + 1) =
        (x ^ (k + 1) - y ^ (k + 1)) * x + y ^ (k + 1) * (x - y) := by
      rw [pow_succ x (k + 1), pow_succ y (k + 1), sub_mul, mul_sub]
      abel
    rw [e]
    have h1 := hF.mul (j + k) 0 _ _ ih hx
    have h2 := hF.mul k j _ _ (hF.pow_mem hy k) h
    rw [Nat.add_zero] at h1
    refine (F (j + (k + 1))).add_mem ?_ ?_
    · have e1 : j + (k + 1) = j + k + 1 := by omega
      rw [e1]
      exact h1
    · have e2 : j + (k + 1) = k + j + 1 := by omega
      rw [e2]
      exact h2

/- English proof (translation)
Rewrite using `[NormedSpace.exp_eq_tsum ℝ]`. Use `show ∑' n : ℕ, ((n.factorial : ℝ))⁻¹ • x ^ n = _`. Establish `hz : ∀ n ∉ Finset.range (L + 2), ((n.factorial : ℝ))⁻¹ • x ^ n = 0`. Introduce `n hn`. Rewrite `hn` using `[Finset.mem_range, not_lt]`.

Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Establish `h1 : x ^ (m + 1) ∈ F L` using `hF.anti L m (by omega) (hF.pow_mem hx m)`. Rewrite `h1` using `[hF.bot, Submodule.mem_bot]`. Rewrite using `[h1, smul_zero]`. Rewrite using `[tsum_eq_sum hz, Finset.sum_range_succ', Finset.sum_range_succ']`.

Simplify using `only [Nat.factorial_zero, zero_add, Nat.factorial_one, pow_zero, pow_one, Nat.cast_one, inv_one, one_smul]`. Establish `hs : (∑ i ∈ Finset.range L, ((i + 1 + 1).factorial : ℝ)⁻¹ • x ^ (i + 1 + 1)) = ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2)` using `rfl`. Rewrite using `[hs]`. Normalize the expressions using the abelian group laws.
-/
theorem IsFil.exp_eq (hF : IsFil F L) {x : A} (hx : x ∈ F 0) :
    NormedSpace.exp x = 1 + (x + ∑ k ∈ range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2)) := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  show ∑' n : ℕ, ((n.factorial : ℝ))⁻¹ • x ^ n = _
  have hz : ∀ n ∉ Finset.range (L + 2), ((n.factorial : ℝ))⁻¹ • x ^ n = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h1 : x ^ (m + 1) ∈ F L := hF.anti L m (by omega) (hF.pow_mem hx m)
    rw [hF.bot, Submodule.mem_bot] at h1
    rw [h1, smul_zero]
  rw [tsum_eq_sum hz, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.factorial_zero, zero_add, Nat.factorial_one, pow_zero, pow_one, Nat.cast_one,
    inv_one, one_smul]
  have hs : (∑ i ∈ Finset.range L, ((i + 1 + 1).factorial : ℝ)⁻¹ • x ^ (i + 1 + 1)) =
      ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2) := rfl
  rw [hs]
  abel

/- English proof (translation)
Establish `hS : ∀ x ∈ F 0, NormedSpace.exp x - 1 = x + ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2)`. Introduce `x hx`. Rewrite using `[hF.exp_eq hx]`. Normalize the expressions using the abelian group laws. Use `⟨fun x hx => ?_, fun j x hx y hy hxy => ?_⟩` and prove the remaining obligations.

Use `show NormedSpace.exp x - 1 ∈ F 0`. Rewrite using `[hS x hx]`. Use `(F 0).add_mem hx (sum_mem fun k _ => (F 0).smul_mem _ ?_)` and prove the remaining obligations. Conclude with `hF.anti 0 (k + 1) (Nat.zero_le _) (hF.pow_mem hx (k + 1))`. Use `show NormedSpace.exp x - 1 - (NormedSpace.exp y - 1) - (x - y) ∈ F (j + 1)`.

Rewrite using `[hS x hx, hS y hy]`. Establish `e : x + ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2) - (y + ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • y ^ (k + 2)) - (x - y) = ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • (x ^ (k + 2) - y ^ (k + 2))`. Simplify using `only [smul_sub, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Use `sum_mem fun k _ => (F (j + 1)).smul_mem _ ?_` and prove the remaining obligations. Conclude with `hF.anti (j + 1) (j + (k + 1)) (by omega) (hF.pow_sub_mem hx hy hxy (k + 1))`.
-/
theorem IsFil.exp_shear (hF : IsFil F L) : IsShear F (fun x => NormedSpace.exp x - 1) := by
  have hS : ∀ x ∈ F 0, NormedSpace.exp x - 1 =
      x + ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2) := by
    intro x hx
    rw [hF.exp_eq hx]
    abel
  refine ⟨fun x hx => ?_, fun j x hx y hy hxy => ?_⟩
  · show NormedSpace.exp x - 1 ∈ F 0
    rw [hS x hx]
    refine (F 0).add_mem hx (sum_mem fun k _ => (F 0).smul_mem _ ?_)
    exact hF.anti 0 (k + 1) (Nat.zero_le _) (hF.pow_mem hx (k + 1))
  · show NormedSpace.exp x - 1 - (NormedSpace.exp y - 1) - (x - y) ∈ F (j + 1)
    rw [hS x hx, hS y hy]
    have e : x + ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2) -
        (y + ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • y ^ (k + 2)) - (x - y) =
        ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • (x ^ (k + 2) - y ^ (k + 2)) := by
      simp only [smul_sub, Finset.sum_sub_distrib]
      abel
    rw [e]
    refine sum_mem fun k _ => (F (j + 1)).smul_mem _ ?_
    exact hF.anti (j + 1) (j + (k + 1)) (by omega) (hF.pow_sub_mem hx hy hxy (k + 1))

/- English proof (translation)
Establish `hE : NormedSpace.exp x - 1 = x + ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2)`. Rewrite using `[hF.exp_eq hx]`. Normalize the expressions using the abelian group laws. Rewrite using `[hE]`. Establish `ht : 0 ≤ ‖x‖` using `norm_nonneg _`.

Establish `hp : 1 ≤ 1 + ‖x‖` using `by linarith`. Establish `hPL : 1 ≤ (1 + ‖x‖) ^ L` using `one_le_pow₀ hp`. Establish `hterm : ∀ k ∈ Finset.range L, ‖(((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2)‖ ≤ ‖x‖ * (1 + ‖x‖) ^ L`. Introduce `k hk`. Rewrite `hk` using `[Finset.mem_range]`.

Rewrite using `[norm_smul]`. Establish `hc : ‖(((k + 2).factorial : ℝ)⁻¹)‖ ≤ 1`. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (by positivity)]`. Conclude with `inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (Nat.factorial_pos _))`. Establish `hxk : ‖x ^ (k + 2)‖ ≤ ‖x‖ ^ (k + 2)` using `norm_pow_le' x (by omega)`.

Establish `hk2 : ‖x‖ ^ (k + 2) ≤ ‖x‖ * (1 + ‖x‖) ^ L`. Establish `e : ‖x‖ ^ (k + 2) = ‖x‖ * ‖x‖ ^ (k + 1)` using `by ring`. Rewrite using `[e]`. Apply `mul_le_mul_of_nonneg_left _ ht` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Establish `hsum : ‖∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2)‖ ≤ L * (‖x‖ * (1 + ‖x‖) ^ L)`. Combine the equalities or inequalities in the displayed calculation. Establish `hx1 : ‖x‖ ≤ ‖x‖ * (1 + ‖x‖) ^ L` using `le_mul_of_one_le_right ht hPL`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations.

Use polynomial arithmetic with `[hsum, hx1]`.
-/
theorem IsFil.exp_bound (hF : IsFil F L) {x : A} (hx : x ∈ F 0) :
    ‖NormedSpace.exp x - 1‖ ≤ ((L : ℝ) + 1) * ‖x‖ * (1 + ‖x‖) ^ L := by
  have hE : NormedSpace.exp x - 1 =
      x + ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2) := by
    rw [hF.exp_eq hx]
    abel
  rw [hE]
  have ht : 0 ≤ ‖x‖ := norm_nonneg _
  have hp : 1 ≤ 1 + ‖x‖ := by linarith
  have hPL : 1 ≤ (1 + ‖x‖) ^ L := one_le_pow₀ hp
  have hterm : ∀ k ∈ Finset.range L,
      ‖(((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2)‖ ≤ ‖x‖ * (1 + ‖x‖) ^ L := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [norm_smul]
    have hc : ‖(((k + 2).factorial : ℝ)⁻¹)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (Nat.factorial_pos _))
    have hxk : ‖x ^ (k + 2)‖ ≤ ‖x‖ ^ (k + 2) := norm_pow_le' x (by omega)
    have hk2 : ‖x‖ ^ (k + 2) ≤ ‖x‖ * (1 + ‖x‖) ^ L := by
      have e : ‖x‖ ^ (k + 2) = ‖x‖ * ‖x‖ ^ (k + 1) := by ring
      rw [e]
      apply mul_le_mul_of_nonneg_left _ ht
      calc ‖x‖ ^ (k + 1) ≤ (1 + ‖x‖) ^ (k + 1) := pow_le_pow_left₀ ht (by linarith) _
        _ ≤ (1 + ‖x‖) ^ L := pow_le_pow_right₀ hp (by omega)
    calc ‖(((k + 2).factorial : ℝ)⁻¹)‖ * ‖x ^ (k + 2)‖ ≤ 1 * ‖x ^ (k + 2)‖ :=
          mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ ‖x‖ * (1 + ‖x‖) ^ L := by rw [one_mul]; exact hxk.trans hk2
  have hsum : ‖∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2)‖ ≤
      L * (‖x‖ * (1 + ‖x‖) ^ L) := by
    calc _ ≤ ∑ k ∈ Finset.range L, ‖(((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range L, ‖x‖ * (1 + ‖x‖) ^ L := Finset.sum_le_sum hterm
      _ = L * (‖x‖ * (1 + ‖x‖) ^ L) := by simp
  have hx1 : ‖x‖ ≤ ‖x‖ * (1 + ‖x‖) ^ L := le_mul_of_one_le_right ht hPL
  refine (norm_add_le _ _).trans ?_
  nlinarith [hsum, hx1]

/- English proof (translation)
Establish `hE` using `hF.exp_shear`. Take `⟨C, M, hC, hbd⟩` from `IsShear.iter_growth hE (Cf := (L : ℝ) + 1) (Mf := L) (by positivity) (fun x hx => hF.exp_bound hx) L`. Use `⟨C, M, hC, fun Y hY => ?_⟩` and prove the remaining obligations. Establish `hY' : iter (fun x => NormedSpace.exp x - 1) L (NormedSpace.exp Y - 1) = Y` using `IsShear.left_inv hF hE hY`. Establish `h1` using `hbd (NormedSpace.exp Y - 1) (hE.1 Y hY)`.

Rewrite `h1` using `[hY']`. Conclude with `h1`.
-/
theorem IsFil.log_growth (hF : IsFil F L) : ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ Y ∈ F 0,
    ‖Y‖ ≤ C * ‖NormedSpace.exp Y - 1‖ * (1 + ‖NormedSpace.exp Y - 1‖) ^ M := by
  have hE := hF.exp_shear
  obtain ⟨C, M, hC, hbd⟩ := IsShear.iter_growth hE (Cf := (L : ℝ) + 1) (Mf := L) (by positivity)
    (fun x hx => hF.exp_bound hx) L
  refine ⟨C, M, hC, fun Y hY => ?_⟩
  have hY' : iter (fun x => NormedSpace.exp x - 1) L (NormedSpace.exp Y - 1) = Y :=
    IsShear.left_inv hF hE hY
  have h1 := hbd (NormedSpace.exp Y - 1) (hE.1 Y hY)
  rw [hY'] at h1
  exact h1

section Group
variable [FiniteDimensional ℝ A]

structure IsAdj (F : ℕ → Submodule ℝ A) (st : A →ₗ[ℝ] A) : Prop where
  mul : ∀ x y, st (x * y) = st y * st x
  one : st 1 = 1
  mem : ∀ x ∈ F 0, st x ∈ F 0

noncomputable def lieN (F : ℕ → Submodule ℝ A) (st : A →ₗ[ℝ] A) : Submodule ℝ A :=
  F 0 ⊓ LinearMap.ker (st + LinearMap.id)

def grpN (F : ℕ → Submodule ℝ A) (st : A →ₗ[ℝ] A) : Set A := {g | g - 1 ∈ F 0 ∧ st g * g = 1}

variable {st : A →ₗ[ℝ] A}

omit [FiniteDimensional ℝ A] in
/- English proof (translation)
Simplify using `only [lieN, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, eq_neg_of_add_eq_zero_left h2⟩`. Introduce and unpack `⟨h1, h2⟩`.

Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite using `[h2]`. Normalize the expressions using the abelian group laws.
-/
theorem mem_lieN {Y : A} : Y ∈ lieN F st ↔ Y ∈ F 0 ∧ st Y = -Y := by
  simp only [lieN, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, eq_neg_of_add_eq_zero_left h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [h2]
    abel

/- English proof (translation)
Use `haveI : CompleteSpace A := FiniteDimensional.complete ℝ A`. Use `letI : Algebra ℚ A := Algebra.compHom A (algebraMap ℚ ℝ)`. Use `letI : NormedAlgebra ℚ A := { norm_smul_le := fun q x => by show ‖(algebraMap ℚ ℝ q) • x‖ ≤ ‖q‖ * ‖x‖`. Rewrite using `[norm_smul, eq_ratCast, Rat.norm_cast_real] }`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl Y)), neg_add_cancel, NormedSpace.exp_zero]`. Rewrite using `[← NormedSpace.exp_add_of_commute (Commute.neg_right (Commute.refl Y)), add_neg_cancel, NormedSpace.exp_zero]`.
-/
theorem exp_neg_mul (Y : A) : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 ∧
    NormedSpace.exp Y * NormedSpace.exp (-Y) = 1 := by
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ A
  letI : Algebra ℚ A := Algebra.compHom A (algebraMap ℚ ℝ)
  letI : NormedAlgebra ℚ A :=
    { norm_smul_le := fun q x => by
        show ‖(algebraMap ℚ ℝ q) • x‖ ≤ ‖q‖ * ‖x‖
        rw [norm_smul, eq_ratCast, Rat.norm_cast_real] }
  constructor
  · rw [← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  · rw [← NormedSpace.exp_add_of_commute (Commute.neg_right (Commute.refl Y)), add_neg_cancel,
      NormedSpace.exp_zero]

omit [FiniteDimensional ℝ A] in
/- English proof (translation)
Establish `hpow : ∀ n : ℕ, st (Y ^ n) = (st Y) ^ n`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [hst.one]`. Consider the case `succ n ih => rw [pow_succ, hst.mul, ih, pow_succ']`.

Rewrite using `[hF.exp_eq hY, hF.exp_eq (hst.mem Y hY), map_add, map_add, map_sum, hst.one]`. Simplify using `only [map_smul, hpow]`.
-/
theorem st_exp (hF : IsFil F L) (hst : IsAdj F st) {Y : A} (hY : Y ∈ F 0) :
    st (NormedSpace.exp Y) = NormedSpace.exp (st Y) := by
  have hpow : ∀ n : ℕ, st (Y ^ n) = (st Y) ^ n := by
    intro n
    induction n with
    | zero => simp [hst.one]
    | succ n ih => rw [pow_succ, hst.mul, ih, pow_succ']
  rw [hF.exp_eq hY, hF.exp_eq (hst.mem Y hY), map_add, map_add, map_sum, hst.one]
  simp only [map_smul, hpow]

/- English proof (translation)
Take `⟨hY0, hY1⟩` from `(mem_lieN (st := st)).1 hY`. Use `show NormedSpace.exp Y - 1 ∈ F 0 ∧ st (NormedSpace.exp Y) * NormedSpace.exp Y = 1`. Use `⟨hF.exp_shear.1 Y hY0, ?_⟩` and prove the remaining obligations. Rewrite using `[st_exp hF hst hY0, hY1]`. Conclude with `(exp_neg_mul Y).1`.
-/
theorem exp_mem_grpN (hF : IsFil F L) (hst : IsAdj F st) {Y : A} (hY : Y ∈ lieN F st) :
    NormedSpace.exp Y ∈ grpN F st := by
  obtain ⟨hY0, hY1⟩ := (mem_lieN (st := st)).1 hY
  show NormedSpace.exp Y - 1 ∈ F 0 ∧ st (NormedSpace.exp Y) * NormedSpace.exp Y = 1
  refine ⟨hF.exp_shear.1 Y hY0, ?_⟩
  rw [st_exp hF hst hY0, hY1]
  exact (exp_neg_mul Y).1

omit [FiniteDimensional ℝ A] in
/- English proof (translation)
Conclude with `IsShear.inj hF hF.exp_shear hY hY' (by show NormedSpace.exp Y - 1 = NormedSpace.exp Y' - 1; rw [h])`.
-/
theorem exp_injOn (hF : IsFil F L) {Y Y' : A} (hY : Y ∈ F 0) (hY' : Y' ∈ F 0)
    (h : NormedSpace.exp Y = NormedSpace.exp Y') : Y = Y' := by
  exact IsShear.inj hF hF.exp_shear hY hY'
    (by show NormedSpace.exp Y - 1 = NormedSpace.exp Y' - 1; rw [h])

noncomputable def lg (L : ℕ) (g : A) : A := iter (fun x => NormedSpace.exp x - 1) L (g - 1)

/- English proof (translation)
Take `⟨hg1, hg2⟩` from `hg`. Establish `hE` using `hF.exp_shear`. Establish `hY0 : lg L g ∈ F 0` using `(IsShear.iter_mem hE hg1 L).1`. Establish `hexp : NormedSpace.exp (lg L g) = g`. Establish `h' : NormedSpace.exp (lg L g) - 1 = g - 1` using `IsShear.right_inv hF hE hg1`.

Simplify using `using h'`. Use `⟨?_, hexp⟩` and prove the remaining obligations. Rewrite using `[mem_lieN]`. Use `⟨hY0, ?_⟩` and prove the remaining obligations. Establish `hinv` using `exp_neg_mul (lg L g)`.

Rewrite `hinv` using `[hexp]`. Establish `hst_g : st g = NormedSpace.exp (-(lg L g))`. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : NormedSpace.exp (st (lg L g)) = NormedSpace.exp (-(lg L g))`. Rewrite using `[← st_exp hF hst hY0, hexp, hst_g]`.

Conclude with `exp_injOn hF (hst.mem _ hY0) ((F 0).neg_mem hY0) h1`.
-/
theorem lg_spec (hF : IsFil F L) (hst : IsAdj F st) {g : A} (hg : g ∈ grpN F st) :
    lg L g ∈ lieN F st ∧ NormedSpace.exp (lg L g) = g := by
  obtain ⟨hg1, hg2⟩ := hg
  have hE := hF.exp_shear
  have hY0 : lg L g ∈ F 0 := (IsShear.iter_mem hE hg1 L).1
  have hexp : NormedSpace.exp (lg L g) = g := by
    have h' : NormedSpace.exp (lg L g) - 1 = g - 1 := IsShear.right_inv hF hE hg1
    simpa using h'
  refine ⟨?_, hexp⟩
  rw [mem_lieN]
  refine ⟨hY0, ?_⟩
  have hinv := exp_neg_mul (lg L g)
  rw [hexp] at hinv
  have hst_g : st g = NormedSpace.exp (-(lg L g)) := by
    calc st g = st g * (g * NormedSpace.exp (-(lg L g))) := by rw [hinv.2, mul_one]
      _ = (st g * g) * NormedSpace.exp (-(lg L g)) := (mul_assoc _ _ _).symm
      _ = NormedSpace.exp (-(lg L g)) := by rw [hg2, one_mul]
  have h1 : NormedSpace.exp (st (lg L g)) = NormedSpace.exp (-(lg L g)) := by
    rw [← st_exp hF hst hY0, hexp, hst_g]
  exact exp_injOn hF (hst.mem _ hY0) ((F 0).neg_mem hY0) h1

omit [FiniteDimensional ℝ A] in
/- English proof (translation)
Take `⟨hs1, hs2⟩` from `hs`. Take `⟨hg1, hg2⟩` from `hg`. Use `show s * g - 1 ∈ F 0 ∧ st (s * g) * (s * g) = 1`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `e : s * g - 1 = (s - 1) * (g - 1) + (s - 1) + (g - 1)` using `by noncomm_ring`.

Rewrite using `[e]`. Establish `h1` using `hF.mul 0 0 _ _ hs1 hg1`. Conclude with `(F 0).add_mem ((F 0).add_mem (hF.anti 0 (0 + 0 + 1) (Nat.zero_le _) h1) hs1) hg1`. Rewrite using `[hst.mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mul_mem_grpN (hF : IsFil F L) (hst : IsAdj F st) {s g : A} (hs : s ∈ grpN F st)
    (hg : g ∈ grpN F st) : s * g ∈ grpN F st := by
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨hg1, hg2⟩ := hg
  show s * g - 1 ∈ F 0 ∧ st (s * g) * (s * g) = 1
  refine ⟨?_, ?_⟩
  · have e : s * g - 1 = (s - 1) * (g - 1) + (s - 1) + (g - 1) := by noncomm_ring
    rw [e]
    have h1 := hF.mul 0 0 _ _ hs1 hg1
    exact (F 0).add_mem ((F 0).add_mem (hF.anti 0 (0 + 0 + 1) (Nat.zero_le _) h1) hs1) hg1
  · rw [hst.mul]
    calc st g * st s * (s * g) = st g * (st s * s) * g := by simp only [mul_assoc]
      _ = 1 := by rw [hs2, mul_one, hg2]

/- English proof (translation)
Establish `hE` using `hF.exp_shear`. Establish `hY0 : ∀ Y : lieN F st, (Y : A) ∈ F 0` using `fun Y => (mem_lieN.1 Y.2).1`. Establish `hmem : ∀ Y : lieN F st, s * NormedSpace.exp (Y : A) ∈ grpN F st` using `fun Y => mul_mem_grpN hF hst hs (exp_mem_grpN hF hst Y.2)`. Set `Φ : lieN F st → lieN F st` to `fun Y => ⟨lg L (s * NormedSpace.exp (Y : A)), (lg_spec hF hst (hmem Y)).1⟩`. Establish `hΦ : ∀ Y, NormedSpace.exp (Φ Y : A) = s * NormedSpace.exp (Y : A)` using `fun Y => (lg_spec hF hst (hmem Y)).2`.

Use `⟨Φ, ?_, hΦ⟩` and prove the remaining obligations. Establish `hs'` using `hs`. Take `⟨hs1, hs2⟩` from `hs'`. Establish `hmulS : IsShear F (fun u => s * (u + 1) - 1)`. Use `⟨fun u hu => ?_, fun j u hu v hv huv => ?_⟩` and prove the remaining obligations.

Use `show s * (u + 1) - 1 ∈ F 0`. Establish `e : s * (u + 1) - 1 = (s - 1) * u + u + (s - 1)` using `by noncomm_ring`. Rewrite using `[e]`. Conclude with `(F 0).add_mem ((F 0).add_mem (hF.anti 0 (0 + 0 + 1) (Nat.zero_le _) (hF.mul 0 0 _ _ hs1 hu)) hu) hs1`. Use `show s * (u + 1) - 1 - (s * (v + 1) - 1) - (u - v) ∈ F (j + 1)`.

Establish `e : s * (u + 1) - 1 - (s * (v + 1) - 1) - (u - v) = (s - 1) * (u - v)` using `by noncomm_ring`. Rewrite using `[e]`. Establish `h` using `hF.mul 0 j _ _ hs1 huv`. Rewrite `h` using `[Nat.zero_add]`. Then use the resulting hypothesis. Establish `hT` using `IsShear.comp hF (IsShear.inv hF hE) (IsShear.comp hF hmulS hE)`.

Establish `hΦT : ∀ Y : lieN F st, (Φ Y : A) = (iter (fun x => NormedSpace.exp x - 1) L ∘ ((fun u => s * (u + 1) - 1) ∘ (fun x => NormedSpace.exp x - 1))) (Y : A)`. Introduce `Y`. Use `show lg L (s * NormedSpace.exp (Y : A)) = iter (fun x => NormedSpace.exp x - 1) L (s * (NormedSpace.exp (Y : A) - 1 + 1) - 1)`. Rewrite using `[sub_add_cancel]`. Both sides reduce to the same expression.

Set `E' : A → A` to `fun x => x + ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2)`. Establish `hEE' : ∀ x ∈ F 0, E' x = NormedSpace.exp x - 1`. Introduce `x hx`. Use `show x + _ = _`. Rewrite using `[hF.exp_eq hx]`.

Normalize the expressions using the abelian group laws. Establish `hpw : ∀ m : ℕ, Differentiable ℝ (fun x : A => x ^ m)`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp only [pow_zero]`.

Conclude with `differentiable_const _`. Consider the case `succ m ih => simp only [pow_succ]`. Conclude with `ih.mul differentiable_id`. Establish `hsd : Differentiable ℝ (fun x : A => ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2))`. Establish `h : Differentiable ℝ (∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • fun x : A => x ^ (k + 2))` using `Differentiable.sum fun k _ => (hpw (k + 2)).const_smul _`.

Rewrite `h` using `[Finset.sum_fn]`. Conclude with `h`. Establish `hE'd : Differentiable ℝ E'` using `differentiable_id.add hsd`. Establish `hiter : ∀ z ∈ F 0, ∀ i, iter E' i z = iter (fun x => NormedSpace.exp x - 1) i z`. Introduce `z hz i`.

Proceed by induction on `i with`. Consider the case `zero => rfl`. Consider the case `succ i ih => show iter E' i z + (z - E' (iter E' i z)) = iter (fun x => NormedSpace.exp x - 1) i z + (z - (NormedSpace.exp (iter (fun x => NormedSpace.exp x - 1) i z) - 1))`. Rewrite using `[ih, hEE' _ (IsShear.iter_mem hE hz i).1]`. Establish `hgΦ : ∀ Y : lieN F st, (Φ Y : A) = iter E' L (s * (E' (Y : A) + 1) - 1)`.

Introduce `Y`. Rewrite using `[hΦT Y, hEE' _ (hY0 Y)]`. Establish `hz : s * (NormedSpace.exp (Y : A) - 1 + 1) - 1 ∈ F 0` using `hmulS.1 _ (hE.1 _ (hY0 Y))`. Conclude with `(hiter _ hz L).symm`. Take `⟨q, hq⟩` from `Submodule.exists_isCompl (lieN F st)`.

Set `π : A →L[ℝ] lieN F st` to `LinearMap.toContinuousLinearMap (Submodule.linearProjOfIsCompl (lieN F st) q hq)`. Establish `hπ : ∀ Y : lieN F st, π (Y : A) = Y` using `fun Y => Submodule.linearProjOfIsCompl_apply_left hq Y`. Establish `hΦd : Differentiable ℝ Φ`. Establish `e : Φ = fun Y : lieN F st => π (iter E' L (s * (E' (Y : A) + 1) - 1))`. Use function extensionality and compare the values at `Y`.

Rewrite using `[← hgΦ Y, hπ]`. Rewrite using `[e]`. Establish `hsub : Differentiable ℝ (fun Y : lieN F st => (Y : A))` using `(lieN F st).subtypeL.differentiable`. Conclude with `π.differentiable.comp ((iter_differentiable hE'd L).comp ((((hE'd.comp hsub).add_const 1).const_mul s).sub_const 1))`. Use `shear_preserving μ (fun j => (F j).comap (lieN F st).subtype) L ?_ ?_ Φ hΦd ?_ ?_` and prove the remaining obligations.

Rewrite using `[eq_top_iff]`. Introduce `Y _`. Conclude with `hY0 Y`. Rewrite using `[eq_bot_iff]`. Introduce `Y hY`.

Establish `h : (Y : A) ∈ F L` using `hY`. Rewrite `h` using `[hF.bot, Submodule.mem_bot]`. Rewrite using `[Submodule.mem_bot]`. Conclude with `Subtype.ext h`. Use `⟨fun Y Y' h => ?_, fun Z => ?_⟩` and prove the remaining obligations.

Establish `h2 : s * NormedSpace.exp (Y : A) = s * NormedSpace.exp (Y' : A)`. Rewrite using `[← hΦ Y, ← hΦ Y', h]`. Establish `h3 : NormedSpace.exp (Y : A) = NormedSpace.exp (Y' : A)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Subtype.ext (exp_injOn hF (hY0 Y) (hY0 Y') h3)`.

Take `⟨hls, hexps⟩` from `lg_spec hF hst hs`. Establish `hsinv : s * NormedSpace.exp (-(lg L s)) = 1`. Establish `h4` using `(exp_neg_mul (lg L s)).2`. Rewrite `h4` using `[hexps]`. Then use the resulting hypothesis. Establish `hm` using `mul_mem_grpN hF hst (exp_mem_grpN hF hst ((lieN F st).neg_mem hls)) (exp_mem_grpN hF hst Z.2)`.

Use `⟨⟨lg L (NormedSpace.exp (-(lg L s)) * NormedSpace.exp (Z : A)), (lg_spec hF hst hm).1⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `exp_injOn hF (hY0 _) (hY0 Z)` to reduce the goal to its premises. Rewrite using `[hΦ]`. Use `show s * NormedSpace.exp (lg L (NormedSpace.exp (-(lg L s)) * NormedSpace.exp (Z : A))) = _`.

Rewrite using `[(lg_spec hF hst hm).2, ← mul_assoc, hsinv, one_mul]`. Introduce `j x y hxy`. Establish `hxy' : (x : A) - (y : A) ∈ F j` using `hxy`. Use `show (Φ x : A) - (Φ y : A) - ((x : A) - (y : A)) ∈ F (j + 1)`. Rewrite using `[hΦT x, hΦT y]`.

Conclude with `hT.2 j _ (hY0 x) _ (hY0 y) hxy'`.
-/
theorem exp_chart_invariant (hF : IsFil F L) (hst : IsAdj F st)
    [MeasurableSpace (lieN F st)] [BorelSpace (lieN F st)] (μ : Measure (lieN F st))
    [μ.IsAddHaarMeasure] {s : A} (hs : s ∈ grpN F st) :
    ∃ Φ : lieN F st → lieN F st, MeasurePreserving Φ μ μ ∧
      ∀ Y, NormedSpace.exp (Φ Y : A) = s * NormedSpace.exp (Y : A) := by
  have hE := hF.exp_shear
  have hY0 : ∀ Y : lieN F st, (Y : A) ∈ F 0 := fun Y => (mem_lieN.1 Y.2).1
  have hmem : ∀ Y : lieN F st, s * NormedSpace.exp (Y : A) ∈ grpN F st :=
    fun Y => mul_mem_grpN hF hst hs (exp_mem_grpN hF hst Y.2)
  let Φ : lieN F st → lieN F st := fun Y =>
    ⟨lg L (s * NormedSpace.exp (Y : A)), (lg_spec hF hst (hmem Y)).1⟩
  have hΦ : ∀ Y, NormedSpace.exp (Φ Y : A) = s * NormedSpace.exp (Y : A) :=
    fun Y => (lg_spec hF hst (hmem Y)).2
  refine ⟨Φ, ?_, hΦ⟩
  have hs' := hs
  obtain ⟨hs1, hs2⟩ := hs'
  have hmulS : IsShear F (fun u => s * (u + 1) - 1) := by
    refine ⟨fun u hu => ?_, fun j u hu v hv huv => ?_⟩
    · show s * (u + 1) - 1 ∈ F 0
      have e : s * (u + 1) - 1 = (s - 1) * u + u + (s - 1) := by noncomm_ring
      rw [e]
      exact (F 0).add_mem ((F 0).add_mem
        (hF.anti 0 (0 + 0 + 1) (Nat.zero_le _) (hF.mul 0 0 _ _ hs1 hu)) hu) hs1
    · show s * (u + 1) - 1 - (s * (v + 1) - 1) - (u - v) ∈ F (j + 1)
      have e : s * (u + 1) - 1 - (s * (v + 1) - 1) - (u - v) = (s - 1) * (u - v) := by
        noncomm_ring
      rw [e]
      have h := hF.mul 0 j _ _ hs1 huv
      rwa [Nat.zero_add] at h
  have hT := IsShear.comp hF (IsShear.inv hF hE) (IsShear.comp hF hmulS hE)
  have hΦT : ∀ Y : lieN F st, (Φ Y : A) = (iter (fun x => NormedSpace.exp x - 1) L ∘
      ((fun u => s * (u + 1) - 1) ∘ (fun x => NormedSpace.exp x - 1))) (Y : A) := by
    intro Y
    show lg L (s * NormedSpace.exp (Y : A)) =
      iter (fun x => NormedSpace.exp x - 1) L (s * (NormedSpace.exp (Y : A) - 1 + 1) - 1)
    rw [sub_add_cancel]
    rfl
  let E' : A → A := fun x => x + ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2)
  have hEE' : ∀ x ∈ F 0, E' x = NormedSpace.exp x - 1 := by
    intro x hx
    show x + _ = _
    rw [hF.exp_eq hx]
    abel
  have hpw : ∀ m : ℕ, Differentiable ℝ (fun x : A => x ^ m) := by
    intro m
    induction m with
    | zero => simp only [pow_zero]; exact differentiable_const _
    | succ m ih => simp only [pow_succ]; exact ih.mul differentiable_id
  have hsd : Differentiable ℝ
      (fun x : A => ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • x ^ (k + 2)) := by
    have h : Differentiable ℝ
        (∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • fun x : A => x ^ (k + 2)) :=
      Differentiable.sum fun k _ => (hpw (k + 2)).const_smul _
    rw [Finset.sum_fn] at h
    exact h
  have hE'd : Differentiable ℝ E' := differentiable_id.add hsd
  have hiter : ∀ z ∈ F 0, ∀ i, iter E' i z = iter (fun x => NormedSpace.exp x - 1) i z := by
    intro z hz i
    induction i with
    | zero => rfl
    | succ i ih =>
      show iter E' i z + (z - E' (iter E' i z)) = iter (fun x => NormedSpace.exp x - 1) i z +
        (z - (NormedSpace.exp (iter (fun x => NormedSpace.exp x - 1) i z) - 1))
      rw [ih, hEE' _ (IsShear.iter_mem hE hz i).1]
  have hgΦ : ∀ Y : lieN F st, (Φ Y : A) = iter E' L (s * (E' (Y : A) + 1) - 1) := by
    intro Y
    rw [hΦT Y, hEE' _ (hY0 Y)]
    have hz : s * (NormedSpace.exp (Y : A) - 1 + 1) - 1 ∈ F 0 := hmulS.1 _ (hE.1 _ (hY0 Y))
    exact (hiter _ hz L).symm
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (lieN F st)
  let π : A →L[ℝ] lieN F st :=
    LinearMap.toContinuousLinearMap (Submodule.linearProjOfIsCompl (lieN F st) q hq)
  have hπ : ∀ Y : lieN F st, π (Y : A) = Y := fun Y =>
    Submodule.linearProjOfIsCompl_apply_left hq Y
  have hΦd : Differentiable ℝ Φ := by
    have e : Φ = fun Y : lieN F st => π (iter E' L (s * (E' (Y : A) + 1) - 1)) := by
      funext Y
      rw [← hgΦ Y, hπ]
    rw [e]
    have hsub : Differentiable ℝ (fun Y : lieN F st => (Y : A)) :=
      (lieN F st).subtypeL.differentiable
    exact π.differentiable.comp ((iter_differentiable hE'd L).comp
      ((((hE'd.comp hsub).add_const 1).const_mul s).sub_const 1))
  refine shear_preserving μ (fun j => (F j).comap (lieN F st).subtype) L ?_ ?_ Φ hΦd ?_ ?_
  · rw [eq_top_iff]
    intro Y _
    exact hY0 Y
  · rw [eq_bot_iff]
    intro Y hY
    have h : (Y : A) ∈ F L := hY
    rw [hF.bot, Submodule.mem_bot] at h
    rw [Submodule.mem_bot]
    exact Subtype.ext h
  · refine ⟨fun Y Y' h => ?_, fun Z => ?_⟩
    · have h2 : s * NormedSpace.exp (Y : A) = s * NormedSpace.exp (Y' : A) := by
        rw [← hΦ Y, ← hΦ Y', h]
      have h3 : NormedSpace.exp (Y : A) = NormedSpace.exp (Y' : A) := by
        calc NormedSpace.exp (Y : A) = st s * s * NormedSpace.exp (Y : A) := by rw [hs2, one_mul]
          _ = st s * (s * NormedSpace.exp (Y' : A)) := by rw [mul_assoc, h2]
          _ = NormedSpace.exp (Y' : A) := by rw [← mul_assoc, hs2, one_mul]
      exact Subtype.ext (exp_injOn hF (hY0 Y) (hY0 Y') h3)
    · obtain ⟨hls, hexps⟩ := lg_spec hF hst hs
      have hsinv : s * NormedSpace.exp (-(lg L s)) = 1 := by
        have h4 := (exp_neg_mul (lg L s)).2
        rwa [hexps] at h4
      have hm := mul_mem_grpN hF hst (exp_mem_grpN hF hst ((lieN F st).neg_mem hls))
        (exp_mem_grpN hF hst Z.2)
      refine ⟨⟨lg L (NormedSpace.exp (-(lg L s)) * NormedSpace.exp (Z : A)),
        (lg_spec hF hst hm).1⟩, ?_⟩
      apply Subtype.ext
      apply exp_injOn hF (hY0 _) (hY0 Z)
      rw [hΦ]
      show s * NormedSpace.exp (lg L (NormedSpace.exp (-(lg L s)) * NormedSpace.exp (Z : A))) = _
      rw [(lg_spec hF hst hm).2, ← mul_assoc, hsinv, one_mul]
  · intro j x y hxy
    have hxy' : (x : A) - (y : A) ∈ F j := hxy
    show (Φ x : A) - (Φ y : A) - ((x : A) - (y : A)) ∈ F (j + 1)
    rw [hΦT x, hΦT y]
    exact hT.2 j _ (hY0 x) _ (hY0 y) hxy'

end Group

section Haar
variable [FiniteDimensional ℝ A] {st : A →ₗ[ℝ] A} [MeasurableSpace A] [BorelSpace A]

/- English proof (translation)
Establish `hY0 : ∀ Y : lieN F st, (Y : A) ∈ F 0` using `fun Y => (mem_lieN.1 Y.2).1`. Establish `hcont : Continuous (fun Y : lieN F st => NormedSpace.exp (Y : A))`. Establish `e : (fun Y : lieN F st => NormedSpace.exp (Y : A)) = fun Y : lieN F st => 1 + ((Y : A) + ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • (Y : A) ^ (k + 2))`. Use function extensionality and compare the values at `Y`. Conclude with `hF.exp_eq (hY0 Y)`.

Rewrite using `[e]`. Conclude with `continuous_const.add (continuous_subtype_val.add (continuous_finset_sum _ fun k _ => (continuous_subtype_val.pow _).const_smul _))`. Use `haveI : ProperSpace (lieN F st) := FiniteDimensional.proper_real _`. Conclude with `hcont.measurableEmbedding fun Y Y' h => Subtype.ext (exp_injOn hF (hY0 Y) (hY0 Y') h)`.
-/
theorem exp_chart_embedding (hF : IsFil F L) :
    MeasurableEmbedding (fun Y : lieN F st => NormedSpace.exp (Y : A)) := by
  have hY0 : ∀ Y : lieN F st, (Y : A) ∈ F 0 := fun Y => (mem_lieN.1 Y.2).1
  have hcont : Continuous (fun Y : lieN F st => NormedSpace.exp (Y : A)) := by
    have e : (fun Y : lieN F st => NormedSpace.exp (Y : A)) = fun Y : lieN F st =>
        1 + ((Y : A) + ∑ k ∈ Finset.range L, (((k + 2).factorial : ℝ)⁻¹) • (Y : A) ^ (k + 2)) := by
      funext Y
      exact hF.exp_eq (hY0 Y)
    rw [e]
    exact continuous_const.add (continuous_subtype_val.add (continuous_finset_sum _ fun k _ =>
      (continuous_subtype_val.pow _).const_smul _))
  haveI : ProperSpace (lieN F st) := FiniteDimensional.proper_real _
  exact hcont.measurableEmbedding fun Y Y' h => Subtype.ext (exp_injOn hF (hY0 Y) (hY0 Y') h)

/- English proof (translation)
Introduce `ν`. Establish `hemb` using `exp_chart_embedding (st := st) hF`. Use `⟨hemb.sigmaFinite_map, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `h1 : ν Set.univ = μ Set.univ` using `by show Measure.map (fun Y : lieN F st => NormedSpace.exp (Y : A)) μ Set.univ = μ Set.univ`.

Rewrite using `[hemb.map_apply, Set.preimage_univ]`. Rewrite `h1` using `[h0]`. Conclude with `(isOpen_univ.measure_ne_zero μ Set.univ_nonempty) (by simpa using h1.symm)`. Use `show Measure.map (fun Y : lieN F st => NormedSpace.exp (Y : A)) μ {x | x ∉ grpN F st} = 0`. Rewrite using `[hemb.map_apply]`.

Establish `e : (fun Y : lieN F st => NormedSpace.exp (Y : A)) ⁻¹' {x | x ∉ grpN F st} = ∅`. Use extensionality with `Y`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]`. Conclude with `exp_mem_grpN hF hst Y.2`. Rewrite using `[e, measure_empty]`.

Introduce `s hs`. Take `⟨Φ, hΦm, hΦ⟩` from `exp_chart_invariant hF hst μ hs`. Use `show Measure.map (s * ·) (Measure.map (fun Y : lieN F st => NormedSpace.exp (Y : A)) μ) = Measure.map (fun Y : lieN F st => NormedSpace.exp (Y : A)) μ`. Rewrite using `[Measure.map_map (continuous_mul_left s).measurable hemb.measurable]`. Establish `hcomp : (s * ·) ∘ (fun Y : lieN F st => NormedSpace.exp (Y : A)) = (fun Y : lieN F st => NormedSpace.exp (Y : A)) ∘ Φ`.

Use function extensionality and compare the values at `Y`. Simplify using `[hΦ]`. Rewrite using `[hcomp, ← Measure.map_map hemb.measurable hΦm.measurable, hΦm.map_eq]`.
-/
theorem exp_chart_haar (hF : IsFil F L) (hst : IsAdj F st) (μ : Measure (lieN F st))
    [μ.IsAddHaarMeasure] :
    let ν := μ.map (fun Y : lieN F st => NormedSpace.exp (Y : A))
    SigmaFinite ν ∧ ν ≠ 0 ∧ ν {x | x ∉ grpN F st} = 0 ∧ ∀ s ∈ grpN F st, ν.map (s * ·) = ν := by
  intro ν
  have hemb := exp_chart_embedding (st := st) hF
  refine ⟨hemb.sigmaFinite_map, ?_, ?_, ?_⟩
  · intro h0
    have h1 : ν Set.univ = μ Set.univ := by
      show Measure.map (fun Y : lieN F st => NormedSpace.exp (Y : A)) μ Set.univ = μ Set.univ
      rw [hemb.map_apply, Set.preimage_univ]
    rw [h0] at h1
    exact (isOpen_univ.measure_ne_zero μ Set.univ_nonempty) (by simpa using h1.symm)
  · show Measure.map (fun Y : lieN F st => NormedSpace.exp (Y : A)) μ {x | x ∉ grpN F st} = 0
    rw [hemb.map_apply]
    have e : (fun Y : lieN F st => NormedSpace.exp (Y : A)) ⁻¹' {x | x ∉ grpN F st} = ∅ := by
      ext Y
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact exp_mem_grpN hF hst Y.2
    rw [e, measure_empty]
  · intro s hs
    obtain ⟨Φ, hΦm, hΦ⟩ := exp_chart_invariant hF hst μ hs
    show Measure.map (s * ·) (Measure.map (fun Y : lieN F st => NormedSpace.exp (Y : A)) μ) =
      Measure.map (fun Y : lieN F st => NormedSpace.exp (Y : A)) μ
    rw [Measure.map_map (continuous_mul_left s).measurable hemb.measurable]
    have hcomp : (s * ·) ∘ (fun Y : lieN F st => NormedSpace.exp (Y : A)) =
        (fun Y : lieN F st => NormedSpace.exp (Y : A)) ∘ Φ := by
      funext Y
      simp [hΦ]
    rw [hcomp, ← Measure.map_map hemb.measurable hΦm.measurable, hΦm.map_eq]

end Haar

end Fil

section Matrices
open Matrix
open scoped Matrix.Norms.Operator
variable {n : ℕ}

def levF (lev : Fin n → ℕ) (j : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | ∀ a b, lev b < lev a + j + 1 → X a b = 0}
  add_mem' := fun hX hY a b h => by simp [hX a b h, hY a b h]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := fun c X hX a b h => by simp [hX a b h]

noncomputable def adjH (H : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := H * Xᴴ * H
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

/- English proof (translation)
Establish `hadj : adjH H g = H * gᴴ * H` using `rfl`. Use `show g - 1 ∈ levF lev 0 ∧ adjH H g * g = 1 ↔ _`. Rewrite using `[hadj]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Use `⟨h1, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mem_grpN_iff (lev : Fin n → ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H * H = 1)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ grpN (levF lev) (adjH H) ↔ g - 1 ∈ levF lev 0 ∧ gᴴ * H * g = H := by
  have hadj : adjH H g = H * gᴴ * H := rfl
  show g - 1 ∈ levF lev 0 ∧ adjH H g * g = 1 ↔ _
  rw [hadj]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    calc gᴴ * H * g = (H * H) * (gᴴ * H * g) := by rw [hH, Matrix.one_mul]
      _ = H * (H * gᴴ * H * g) := by simp only [Matrix.mul_assoc]
      _ = H := by rw [h2, Matrix.mul_one]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    calc H * gᴴ * H * g = H * (gᴴ * H * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2, hH]

end Matrices

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
