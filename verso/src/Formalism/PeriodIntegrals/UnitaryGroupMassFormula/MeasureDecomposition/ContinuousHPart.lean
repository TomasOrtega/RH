import Mathlib
import Formalism.PeriodIntegrals.ScMuExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDecomp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.ContinuousUMatApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.HJMulVecGen

noncomputable section

open Matrix

namespace PI.ScMuExists.UnitaryGroupMassFormula

section Real

variable {n r : ℕ} (ε : Fin n → Bool)

def RFrame (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Prop :=
  (∀ a b, hJ ε (e a) (e b) = 0) ∧ (∀ a b, hJ ε (f a) (f b) = 0) ∧
  (∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0) ∧
  (∀ a, hJ ε (e a) z = 0 ∧ hJ ε (f a) z = 0) ∧ hJ ε z z ≠ 0

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5⟩` from `hF`. Use `⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[rv_hJ, h1, map_zero]`. Rewrite using `[rv_hJ, h2, map_zero]`. Apply the tactic sequence `rw [rv_hJ, h3]; split_ifs <;> simp`.

Rewrite using `[rv_hJ, (h4 a).1, map_zero]`. Rewrite using `[rv_hJ, (h4 a).2, map_zero]`. Rewrite using `[rv_hJ]`. Conclude with `fun h => h5 ((map_eq_zero_iff _ (I.φ v).injective).mp h)`.
-/
theorem rFrame_of {I : Formalism.MainNotions.S.AutInst} {r : ℕ} {e f : Fin r → Fin I.n → I.E} {z : Fin I.n → I.E}
    (hF : IsFrame I e f z) (v : NumberField.InfinitePlace I.F) :
    RFrame (I.ε v) (fun a => rv I v (e a)) (fun a => rv I v (f a)) (rv I v z) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hF
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [rv_hJ, h1, map_zero]
  · rw [rv_hJ, h2, map_zero]
  · rw [rv_hJ, h3]; split_ifs <;> simp
  · rw [rv_hJ, (h4 a).1, map_zero]
  · rw [rv_hJ, (h4 a).2, map_zero]
  · rw [rv_hJ]
    exact fun h => h5 ((map_eq_zero_iff _ (I.φ v).injective).mp h)

def hJL (u : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun := hJ ε u
  map_add' x y := by simp [hJ, Matrix.mulVec_add, dotProduct_add]
  map_smul' c x := by simp [hJ, Matrix.mulVec_smul, dotProduct_smul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hJL_apply (u x : Fin n → ℂ) : hJL ε u x = hJ ε u x := rfl

def piW (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.id - ∑ a, (hJL ε (f a)).smulRight (e a) - ∑ a, (hJL ε (e a)).smulRight (f a) -
    ((hJ ε z z)⁻¹ • hJL ε z).smulRight z

/- English proof (translation)
Simplify using `[piW, hJL_apply, smul_eq_mul, mul_comm]`.
-/
theorem piW_apply (e f : Fin r → Fin n → ℂ) (z x : Fin n → ℂ) :
    piW ε e f z x = x - ∑ a, hJ ε (f a) x • e a - ∑ a, hJ ε (e a) x • f a -
      ((hJ ε z z)⁻¹ * hJ ε z x) • z := by
  simp [piW, hJL_apply, smul_eq_mul, mul_comm]

variable {ε}

/- English proof (translation)
Simplify using `[hJ, Matrix.mulVec_sub, dotProduct_sub]`.
-/
theorem hJ_sub_right (u x y : Fin n → ℂ) : hJ ε u (x - y) = hJ ε u x - hJ ε u y := by
  simp [hJ, Matrix.mulVec_sub, dotProduct_sub]

/- English proof (translation)
Conclude with `map_sum (hJL ε u) g s`.
-/
theorem hJ_sum_right {ι : Type*} (s : Finset ι) (u : Fin n → ℂ) (g : ι → Fin n → ℂ) :
    hJ ε u (∑ i ∈ s, g i) = ∑ i ∈ s, hJ ε u (g i) := by
  exact map_sum (hJL ε u) g s

/- English proof (translation)
Simplify using `[hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
theorem hJ_smul_right (u x : Fin n → ℂ) (c : ℂ) : hJ ε u (c • x) = c * hJ ε u x := by
  simp [hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

variable {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ}

/- English proof (translation)
Take `⟨hee, hff, hef, hz, hzz⟩` from `hF`. Rewrite using `[piW_apply]`. Simplify using `only [hJ_sub_right, hJ_sum_right, hJ_smul_right, hee, hef, (hz b).1]`. Simplify using the standard rewrite rules.
-/
theorem hJ_e_piW (hF : RFrame ε e f z) (b : Fin r) (x : Fin n → ℂ) : hJ ε (e b) (piW ε e f z x) = 0 := by
  obtain ⟨hee, hff, hef, hz, hzz⟩ := hF
  rw [piW_apply]
  simp only [hJ_sub_right, hJ_sum_right, hJ_smul_right, hee, hef, (hz b).1]
  simp

/- English proof (translation)
Unfold `hJ`. Simplify using `only [Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, star_sum, star_mul', star_star, Pi.star_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp <;> ring`.
-/
private theorem hJ_conj_lemma (x y : Fin n → ℂ) : hJ ε x y = star (hJ ε y x) := by
  unfold hJ
  simp only [Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp <;> ring

/- English proof (translation)
Take `⟨hee, hff, hef, hz, hzz⟩` from `hF`. Establish `h1 : ∀ a, hJ ε (f b) (e a) = if a = b then 1 else 0` using `fun a => by`. Rewrite using `[hJ_conj_lemma, hef a b]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h]`. Rewrite using `[piW_apply]`. Simplify using `only [hJ_sub_right, hJ_sum_right, hJ_smul_right, hff, h1, (hz b).2]`. Simplify using the standard rewrite rules.
-/
theorem hJ_f_piW (hF : RFrame ε e f z) (b : Fin r) (x : Fin n → ℂ) : hJ ε (f b) (piW ε e f z x) = 0 := by
  obtain ⟨hee, hff, hef, hz, hzz⟩ := hF
  have h1 : ∀ a, hJ ε (f b) (e a) = if a = b then 1 else 0 := fun a => by
    rw [hJ_conj_lemma, hef a b]
    by_cases h : a = b
    · subst h; simp
    · simp [h]
  rw [piW_apply]
  simp only [hJ_sub_right, hJ_sum_right, hJ_smul_right, hff, h1, (hz b).2]
  simp

/- English proof (translation)
Take `⟨hee, hff, hef, hz, hzz⟩` from `hF`. Establish `h1 : ∀ a, hJ ε z (e a) = 0` using `fun a => by rw [hJ_conj_lemma, (hz a).1, star_zero]`. Establish `h2 : ∀ a, hJ ε z (f a) = 0` using `fun a => by rw [hJ_conj_lemma, (hz a).2, star_zero]`. Rewrite using `[piW_apply]`. Simplify using `only [hJ_sub_right, hJ_sum_right, hJ_smul_right, h1, h2, mul_zero, Finset.sum_const_zero, sub_zero]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hJ_z_piW (hF : RFrame ε e f z) (x : Fin n → ℂ) : hJ ε z (piW ε e f z x) = 0 := by
  obtain ⟨hee, hff, hef, hz, hzz⟩ := hF
  have h1 : ∀ a, hJ ε z (e a) = 0 := fun a => by rw [hJ_conj_lemma, (hz a).1, star_zero]
  have h2 : ∀ a, hJ ε z (f a) = 0 := fun a => by rw [hJ_conj_lemma, (hz a).2, star_zero]
  rw [piW_apply]
  simp only [hJ_sub_right, hJ_sum_right, hJ_smul_right, h1, h2, mul_zero, Finset.sum_const_zero, sub_zero]
  field_simp
  ring

/- English proof (translation)
Rewrite using `[piW_apply]`. Simplify using `[he, hf, hz]`.
-/
theorem piW_of_perp {y : Fin n → ℂ} (he : ∀ a, hJ ε (e a) y = 0) (hf : ∀ a, hJ ε (f a) y = 0)
    (hz : hJ ε z y = 0) : piW ε e f z y = y := by
  rw [piW_apply]
  simp [he, hf, hz]

/- English proof (translation)
Take `⟨hee, hff, hef, hz, hzz⟩` from `hF`. Establish `h1 : ∀ a, hJ ε (f a) (e b) = if a = b then 1 else 0` using `fun a => by`. Rewrite using `[hJ_conj_lemma, hef b a]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`. Establish `h2 : hJ ε z (e b) = 0` using `by rw [hJ_conj_lemma, (hz b).1, star_zero]`. Rewrite using `[piW_apply]`. Simplify using `[h1, hee, h2]`.
-/
theorem piW_e (hF : RFrame ε e f z) (b : Fin r) : piW ε e f z (e b) = 0 := by
  obtain ⟨hee, hff, hef, hz, hzz⟩ := hF
  have h1 : ∀ a, hJ ε (f a) (e b) = if a = b then 1 else 0 := fun a => by
    rw [hJ_conj_lemma, hef b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  have h2 : hJ ε z (e b) = 0 := by rw [hJ_conj_lemma, (hz b).1, star_zero]
  rw [piW_apply]
  simp [h1, hee, h2]

/- English proof (translation)
Establish `hle : spanLt e a ≤ LinearMap.ker (piW ε e f z)`. Rewrite using `[spanLt, Submodule.span_le]`. Introduce and unpack `_ ⟨b, -, rfl⟩`. Conclude with `LinearMap.mem_ker.mpr (piW_e hF b)`. Conclude with `LinearMap.mem_ker.mp (hle hx)`.
-/
theorem piW_spanLt (hF : RFrame ε e f z) (a : ℕ) {x : Fin n → ℂ} (hx : x ∈ spanLt e a) :
    piW ε e f z x = 0 := by
  have hle : spanLt e a ≤ LinearMap.ker (piW ε e f z) := by
    rw [spanLt, Submodule.span_le]
    rintro _ ⟨b, -, rfl⟩
    exact LinearMap.mem_ker.mpr (piW_e hF b)
  exact LinearMap.mem_ker.mp (hle hx)

/- English proof (translation)
Establish `hx : x - piW ε e f z x = ∑ a, hJ ε (f a) x • e a + ∑ a, hJ ε (e a) x • f a + ((hJ ε z z)⁻¹ * hJ ε z x) • z`. Rewrite using `[piW_apply]`. Normalize the expressions using the abelian group laws. Rewrite using `[hx]`. Simplify using `only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, he, hf, hz]`.
-/
theorem fix_sub_piW {h : Matrix (Fin n) (Fin n) ℂ} (he : ∀ a, h *ᵥ e a = e a)
    (hf : ∀ a, h *ᵥ f a = f a) (hz : h *ᵥ z = z) (x : Fin n → ℂ) :
    h *ᵥ (x - piW ε e f z x) = x - piW ε e f z x := by
  have hx : x - piW ε e f z x = ∑ a, hJ ε (f a) x • e a + ∑ a, hJ ε (e a) x • f a +
      ((hJ ε z z)⁻¹ * hJ ε z x) • z := by
    rw [piW_apply]; abel
  rw [hx]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, he, hf, hz]

def PwM (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix' (piW ε e f z)

def hPart (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  1 - PwM ε e f z + PwM ε e f z * g * PwM ε e f z

/- English proof (translation)
Unfold `hPart`. Use `fun_prop`.
-/
theorem continuous_hPart (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    Continuous (hPart ε e f z) := by
  unfold hPart
  fun_prop

/- English proof (translation)
Establish `hP : ∀ y, PwM ε e f z *ᵥ y = piW ε e f z y` using `fun y => by`. Rewrite using `[PwM, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']`. Simplify using `only [hPart, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hP]`.
-/
theorem hPart_mulVec (g : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    hPart ε e f z g *ᵥ x = x - piW ε e f z x + piW ε e f z (g *ᵥ piW ε e f z x) := by
  have hP : ∀ y, PwM ε e f z *ᵥ y = piW ε e f z y := fun y => by
    rw [PwM, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  simp only [hPart, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hP]

/- English proof (translation)
Unfold `Formalism.REAL.inUJ at hU`. Unfold `hJ`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hU]`.
-/
private theorem hJ_mulVec_of_inUJ' {h : Matrix (Fin n) (Fin n) ℂ} (hU : Formalism.REAL.inUJ ε h) (u v : Fin n → ℂ) :
    hJ ε (h *ᵥ u) (h *ᵥ v) = hJ ε u v := by
  unfold Formalism.REAL.inUJ at hU
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hU]

/- English proof (translation)
Use `Matrix.toLin'.injective (LinearMap.ext fun x => ?_)` and prove the remaining obligations. Rewrite using `[Matrix.toLin'_apply, Matrix.toLin'_apply, hPart_mulVec]`. Establish `hey : ∀ a, hJ ε (e a) (h *ᵥ piW ε e f z x) = 0` using `fun a => by`. Use `hJ_mulVec_of_inUJ' hU (e a) (piW ε e f z x)` as an intermediate fact. Rewrite `this` using `[he a]`.

Rewrite using `[this]`. Conclude with `hJ_e_piW hF a x`. Establish `hfy : ∀ a, hJ ε (f a) (h *ᵥ piW ε e f z x) = 0` using `fun a => by`. Use `hJ_mulVec_of_inUJ' hU (f a) (piW ε e f z x)` as an intermediate fact. Rewrite `this` using `[hf a]`.

Rewrite using `[this]`. Conclude with `hJ_f_piW hF a x`. Establish `hzy : hJ ε z (h *ᵥ piW ε e f z x) = 0`. Use `hJ_mulVec_of_inUJ' hU z (piW ε e f z x)` as an intermediate fact. Rewrite `this` using `[hz]`.

Rewrite using `[this]`. Conclude with `hJ_z_piW hF x`. Establish `h0 : piW ε e f z ((nm - 1) *ᵥ (h *ᵥ piW ε e f z x)) = 0` using `piW_spanLt hF r (hn.2 _ hey)`. Establish `hpy : piW ε e f z (h *ᵥ piW ε e f z x) = h *ᵥ piW ε e f z x` using `piW_of_perp hey hfy hzy`. Establish `hsplit : (nm * h) *ᵥ piW ε e f z x = h *ᵥ piW ε e f z x + (nm - 1) *ᵥ (h *ᵥ piW ε e f z x)`.

Rewrite using `[← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws. Establish `hx : h *ᵥ x = (x - piW ε e f z x) + h *ᵥ piW ε e f z x`. Rewrite using `[← fix_sub_piW he hf hz x, ← Matrix.mulVec_add, sub_add_cancel]`. Rewrite using `[hsplit, map_add, hpy, h0, add_zero, hx]`.
-/
theorem hPart_mul (hF : RFrame ε e f z) {nm h : Matrix (Fin n) (Fin n) ℂ} (hn : InN ε e z nm)
    (hU : Formalism.REAL.inUJ ε h) (he : ∀ a, h *ᵥ e a = e a) (hf : ∀ a, h *ᵥ f a = f a) (hz : h *ᵥ z = z) :
    hPart ε e f z (nm * h) = h := by
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hPart_mulVec]
  have hey : ∀ a, hJ ε (e a) (h *ᵥ piW ε e f z x) = 0 := fun a => by
    have := hJ_mulVec_of_inUJ' hU (e a) (piW ε e f z x)
    rw [he a] at this
    rw [this]; exact hJ_e_piW hF a x
  have hfy : ∀ a, hJ ε (f a) (h *ᵥ piW ε e f z x) = 0 := fun a => by
    have := hJ_mulVec_of_inUJ' hU (f a) (piW ε e f z x)
    rw [hf a] at this
    rw [this]; exact hJ_f_piW hF a x
  have hzy : hJ ε z (h *ᵥ piW ε e f z x) = 0 := by
    have := hJ_mulVec_of_inUJ' hU z (piW ε e f z x)
    rw [hz] at this
    rw [this]; exact hJ_z_piW hF x
  have h0 : piW ε e f z ((nm - 1) *ᵥ (h *ᵥ piW ε e f z x)) = 0 :=
    piW_spanLt hF r (hn.2 _ hey)
  have hpy : piW ε e f z (h *ᵥ piW ε e f z x) = h *ᵥ piW ε e f z x := piW_of_perp hey hfy hzy
  have hsplit : (nm * h) *ᵥ piW ε e f z x =
      h *ᵥ piW ε e f z x + (nm - 1) *ᵥ (h *ᵥ piW ε e f z x) := by
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  have hx : h *ᵥ x = (x - piW ε e f z x) + h *ᵥ piW ε e f z x := by
    rw [← fix_sub_piW he hf hz x, ← Matrix.mulVec_add, sub_add_cancel]
  rw [hsplit, map_add, hpy, h0, add_zero, hx]

end Real

end PI.ScMuExists.UnitaryGroupMassFormula
