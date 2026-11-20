import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

noncomputable section

namespace GlobalTheory.WhitBump.Shear

/- English proof (translation)
Set `b` to `Module.finBasis ℝ V`. Rewrite using `[← LinearMap.det_toMatrix b]`. Use `set B := LinearMap.toMatrix b b f with hB`. Establish `hBB : LinearMap.toMatrixAlgEquiv b f = B`. Use extensionality with `i j`.

Simplify using `[hB, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]`. Establish `h3 : IsNilpotent (B - 1)`. Establish `: B - 1 = LinearMap.toMatrixAlgEquiv b (f - 1)`. Rewrite using `[map_sub, map_one, hBB]`. Rewrite using `[this]`.

Conclude with `hf.map _`. Establish `h4 : IsNilpotent (1 - B)` using `by rw [← neg_sub]; exact h3.neg`. Establish `h5` using `(Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h4).map (Polynomial.evalRingHom (1 : ℝ))`. Rewrite `h5` using `[Polynomial.coe_evalRingHom, Polynomial.eval_sub, Matrix.eval_charpoly, Polynomial.eval_pow, Polynomial.eval_X, one_pow, map_one, sub_sub_cancel]`. Conclude with `sub_eq_zero.1 h5.eq_zero`.
-/
theorem det_eq_one_of_isNilpotent_sub_one {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (f : V →ₗ[ℝ] V) (hf : IsNilpotent (f - 1)) : LinearMap.det f = 1 := by
  let b := Module.finBasis ℝ V
  rw [← LinearMap.det_toMatrix b]
  set B := LinearMap.toMatrix b b f with hB
  have hBB : LinearMap.toMatrixAlgEquiv b f = B := by
    ext i j; simp [hB, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  have h3 : IsNilpotent (B - 1) := by
    have : B - 1 = LinearMap.toMatrixAlgEquiv b (f - 1) := by
      rw [map_sub, map_one, hBB]
    rw [this]; exact hf.map _
  have h4 : IsNilpotent (1 - B) := by rw [← neg_sub]; exact h3.neg
  have h5 := (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h4).map (Polynomial.evalRingHom (1 : ℝ))
  rw [Polynomial.coe_evalRingHom, Polynomial.eval_sub, Matrix.eval_charpoly, Polynomial.eval_pow, Polynomial.eval_X,
    one_pow, map_one, sub_sub_cancel] at h5
  exact sub_eq_zero.1 h5.eq_zero

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def above (M : Matrix (Fin n) (Fin n) (Cinf E)) : Vp E n := fun p => M p.1.1 p.1.2

def sU (t : Vp E n) : Matrix (Fin n) (Fin n) (Cinf E) :=
  Matrix.of fun i j => if h : i < j then t ⟨(i, j), h⟩ else 0

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [nu, sU, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]`. Distinguish the cases in `h : i < j`. Simplify using `[h, ne_of_lt h]`. Distinguish the cases in `h' : i = j`.

Substitute `h'` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, h']`.
-/
theorem nu_eq (t : Vp E n) : nu t = 1 + sU t := by
  ext i j
  simp only [nu, sU, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
  by_cases h : i < j
  · simp [h, ne_of_lt h]
  · by_cases h' : i = j
    · subst h'; simp
    · simp [h, h']

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [nu, above, Matrix.of_apply]`. Break down `lt_trichotomy i j with h | h | h` into its components or cases. Simplify using `[h]`. Substitute `h` using the available equality.

Simplify using `[hd]`. Simplify using `[not_lt_of_gt h, ne_of_gt h, hl i j h]`.
-/
theorem nu_above {M : Matrix (Fin n) (Fin n) (Cinf E)} (hl : ∀ i j, j < i → M i j = 0) (hd : ∀ i, M i i = 1) :
    nu (above M) = M := by
  ext i j
  simp only [nu, above, Matrix.of_apply]
  rcases lt_trichotomy i j with h | h | h
  · simp [h]
  · subst h; simp [hd]
  · simp [not_lt_of_gt h, ne_of_gt h, hl i j h]

def lin (u : Matrix (Fin n) (Fin n) (Cinf E)) : Vp E n →ₗ[ℝ] Vp E n where
  toFun t := above (sU t * u)
  map_add' a b := by
    have : sU (a + b) = sU a + sU b := by
      ext i j; simp only [sU, Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp
    rw [this, Matrix.add_mul]; rfl
  map_smul' r a := by
    have : sU (r • a) = r • sU a := by
      ext i j; simp only [sU, Matrix.of_apply, Matrix.smul_apply]; split_ifs <;> simp
    rw [this, Matrix.smul_mul]; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lin_apply (u : Matrix (Fin n) (Fin n) (Cinf E)) (t : Vp E n) : lin u t = above (sU t * u) := rfl

/- English proof (translation)
Introduce `p hp`. Take `⟨⟨i, j⟩, hij⟩` from `p`. Simplify using `only at hp hij`. Rewrite using `[LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, lin_apply, sub_eq_zero]`. Simplify using `only [above, Matrix.mul_apply]`.

Rewrite using `[Finset.sum_eq_single j]`. Simplify using `[sU, hij, hd]`. Introduce `k _ hkj`. Break down `lt_or_gt_of_ne hkj with hk | hk` into its components or cases. Establish `: sU t i k = 0`.

Simplify using `only [sU, Matrix.of_apply]`. Use `split_ifs with h`. Conclude with `ht _ (by simp only; have := Fin.lt_def.1 hk; omega)`. Both sides reduce to the same expression. Rewrite using `[this, zero_mul]`.

Rewrite using `[hl k j hk, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ j) h`.
-/
theorem sub_one_vanish {u : Matrix (Fin n) (Fin n) (Cinf E)} (hl : ∀ i j, j < i → u i j = 0) (hd : ∀ i, u i i = 1)
    (c : ℕ) (t : Vp E n) (ht : ∀ p : Idx n, p.1.2.val < c → t p = 0) :
    ∀ p : Idx n, p.1.2.val < c + 1 → ((lin u - 1) t) p = 0 := by
  intro p hp
  obtain ⟨⟨i, j⟩, hij⟩ := p
  simp only at hp hij
  rw [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, lin_apply, sub_eq_zero]
  simp only [above, Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · simp [sU, hij, hd]
  · intro k _ hkj
    rcases lt_or_gt_of_ne hkj with hk | hk
    · have : sU t i k = 0 := by
        simp only [sU, Matrix.of_apply]
        split_ifs with h
        · exact ht _ (by simp only; have := Fin.lt_def.1 hk; omega)
        · rfl
      rw [this, zero_mul]
    · rw [hl k j hk, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/- English proof (translation)
Establish `key : ∀ m : ℕ, ∀ t : Vp E n, ∀ p : Idx n, p.1.2.val < m → (((lin u - 1) ^ m) t) p = 0`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro t p hp`. Conclude with `absurd hp (Nat.not_lt_zero _)`.

Consider the case `succ m ih`. Introduce `t p hp`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `sub_one_vanish hl hd m _ (ih t) p hp`. Conclude with `⟨n, LinearMap.ext fun t => funext fun p => key n t p p.1.2.isLt⟩`.
-/
theorem isNilpotent_lin_sub_one {u : Matrix (Fin n) (Fin n) (Cinf E)} (hl : ∀ i j, j < i → u i j = 0)
    (hd : ∀ i, u i i = 1) : IsNilpotent (lin u - 1) := by
  have key : ∀ m : ℕ, ∀ t : Vp E n, ∀ p : Idx n, p.1.2.val < m → (((lin u - 1) ^ m) t) p = 0 := by
    intro m
    induction m with
    | zero => intro t p hp; exact absurd hp (Nat.not_lt_zero _)
    | succ m ih =>
      intro t p hp
      rw [pow_succ', Module.End.mul_apply]
      exact sub_one_vanish hl hd m _ (ih t) p hp
  exact ⟨n, LinearMap.ext fun t => funext fun p => key n t p p.1.2.isLt⟩

/- English proof (translation)
The claim follows from `det_eq_one_of_isNilpotent_sub_one _ (isNilpotent_lin_sub_one hl hd)`.
-/
theorem det_lin {u : Matrix (Fin n) (Fin n) (Cinf E)} (hl : ∀ i j, j < i → u i j = 0)
    (hd : ∀ i, u i i = 1) : LinearMap.det (lin u) = 1 :=
  det_eq_one_of_isNilpotent_sub_one _ (isNilpotent_lin_sub_one hl hd)

end GlobalTheory.WhitBump.Shear

open GlobalTheory.WhitBump.Shear in

/- English proof (translation)
Introduce `E _ _ n u hu`. Take `⟨hl, hd⟩` from `(GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu`. Use `haveI : Measure.IsAddHaarMeasure (volume : Measure (Vp E n)) := Measure.pi.isAddHaarMeasure _`. Use `set L := lin (u : Matrix (Fin n) (Fin n) (Cinf E)) with hLdef`. Establish `hdet : LinearMap.det L = 1` using `det_lin hl hd`.

Establish `hdet0 : LinearMap.det L ≠ 0` using `by rw [hdet]; exact one_ne_zero`. Set `e` to `(LinearMap.equivOfDetNeZero L hdet0).toContinuousLinearEquiv`. Set `h` to `e.toHomeomorph.trans (Homeomorph.addLeft (above (u : Matrix (Fin n) (Fin n) (Cinf E))))`. Use `⟨h.toMeasurableEquiv, ?_, ?_⟩` and prove the remaining obligations. Establish `hL : MeasurePreserving L volume volume` using `⟨L.continuous_of_finiteDimensional.measurable, by`.

Rewrite using `[Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet0, hdet]`. Use the proof step `simp⟩`. Use `(measurePreserving_add_left volume (above (u : Matrix (Fin n) (Fin n) (Cinf E)))).comp hL` as an intermediate fact. Conclude with `this`. Introduce `t`.

Establish `hmem : nuGL t * u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n)` using `mul_mem (nuGL_mem t) hu`. Take `⟨hl', hd'⟩` from `(GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hmem`. Simplify using `only [Units.val_mul, nuGL_val] at hl' hd'`. Establish `: h.toMeasurableEquiv t = above (nu t * (u : Matrix (Fin n) (Fin n) (Cinf E)))` using `by show above _ + L t = _`. Rewrite using `[hLdef, lin_apply, nu_eq, Matrix.add_mul, Matrix.one_mul]`.

Both sides reduce to the same expression. Rewrite using `[this, nu_above hl' hd']`.
-/
theorem GlobalTheory.WhitBump.exists_shear_measurePreserving : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ)
    (u : GL (Fin n) (Cinf E)), u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) →
    ∃ τ : Vp E n ≃ᵐ Vp E n, MeasurePreserving τ volume volume ∧
      ∀ t, nu (τ t) = nu t * (u : Matrix (Fin n) (Fin n) (Cinf E)) := by
  intro E _ _ n u hu
  obtain ⟨hl, hd⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Vp E n)) := Measure.pi.isAddHaarMeasure _
  set L := lin (u : Matrix (Fin n) (Fin n) (Cinf E)) with hLdef
  have hdet : LinearMap.det L = 1 := det_lin hl hd
  have hdet0 : LinearMap.det L ≠ 0 := by rw [hdet]; exact one_ne_zero
  let e := (LinearMap.equivOfDetNeZero L hdet0).toContinuousLinearEquiv
  let h := e.toHomeomorph.trans (Homeomorph.addLeft (above (u : Matrix (Fin n) (Fin n) (Cinf E))))
  refine ⟨h.toMeasurableEquiv, ?_, ?_⟩
  · have hL : MeasurePreserving L volume volume :=
      ⟨L.continuous_of_finiteDimensional.measurable, by
        rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet0, hdet]; simp⟩
    have := (measurePreserving_add_left volume (above (u : Matrix (Fin n) (Fin n) (Cinf E)))).comp hL
    exact this
  · intro t
    have hmem : nuGL t * u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) := mul_mem (nuGL_mem t) hu
    obtain ⟨hl', hd'⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hmem
    simp only [Units.val_mul, nuGL_val] at hl' hd'
    have : h.toMeasurableEquiv t = above (nu t * (u : Matrix (Fin n) (Fin n) (Cinf E))) := by
      show above _ + L t = _
      rw [hLdef, lin_apply, nu_eq, Matrix.add_mul, Matrix.one_mul]
      rfl
    rw [this, nu_above hl' hd']
