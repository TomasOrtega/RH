import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NGClosed
open Matrix

noncomputable section

namespace GlobalTheory.UnipRadNilp

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n r : ℕ}

/- English proof (translation)
Unfold `hJ`. Rewrite using `[mulVec_sub, dotProduct_sub]`.
-/
theorem hJ_sub_right (ε : Fin n → Bool) (x y w : Fin n → ℂ) : hJ ε x (y - w) = hJ ε x y - hJ ε x w := by
  unfold hJ; rw [mulVec_sub, dotProduct_sub]

/- English proof (translation)
Unfold `hJ`. Rewrite using `[star_sub, sub_dotProduct]`.
-/
theorem hJ_sub_left (ε : Fin n → Bool) (x y w : Fin n → ℂ) : hJ ε (x - y) w = hJ ε x w - hJ ε y w := by
  unfold hJ; rw [star_sub, sub_dotProduct]

/- English proof (translation)
Unfold `hJ`. Rewrite using `[star_add, add_dotProduct]`.
-/
theorem hJ_add_left (ε : Fin n → Bool) (x y w : Fin n → ℂ) : hJ ε (x + y) w = hJ ε x w + hJ ε y w := by
  unfold hJ; rw [star_add, add_dotProduct]

/- English proof (translation)
Unfold `hJ`. Rewrite using `[star_smul, smul_dotProduct, smul_eq_mul]`.
-/
theorem hJ_smul_left (ε : Fin n → Bool) (c : ℂ) (x w : Fin n → ℂ) : hJ ε (c • x) w = star c * hJ ε x w := by
  unfold hJ; rw [star_smul, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Unfold `hJ`. Simplify using the standard rewrite rules.
-/
theorem hJ_zero_left' (ε : Fin n → Bool) (w : Fin n → ℂ) : hJ ε 0 w = 0 := by
  unfold hJ; simp

/- English proof (translation)
Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨c, hc, rfl⟩` from `hy`. Conclude with `hw c hc`.

Consider the case `zero => exact hJ_zero_left' ε w`. Consider the case `add x y _ _ hx hy => rw [hJ_add_left, hx, hy, add_zero]`. Consider the case `smul c x _ hx => rw [hJ_smul_left, hx, mul_zero]`.
-/
theorem orth_span (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (b : ℕ) (w : Fin n → ℂ)
    (hw : ∀ c : Fin r, c.1 < b → hJ ε (e c) w = 0) : ∀ v ∈ spanLt e b, hJ ε v w = 0 := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    exact hw c hc
  | zero => exact hJ_zero_left' ε w
  | add x y _ _ hx hy => rw [hJ_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [hJ_smul_left, hx, mul_zero]

/- English proof (translation)
Unfold `spanLt`. Establish `: (e '' {b : Fin r | b.1 < 0}) = ∅`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[this, Submodule.span_empty]`.
-/
theorem spanLt_zero (e : Fin r → Fin n → ℂ) : spanLt e 0 = ⊥ := by
  unfold spanLt
  have : (e '' {b : Fin r | b.1 < 0}) = ∅ := by
    ext x; simp
  rw [this, Submodule.span_empty]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro m v hv`. Simplify using `using hv`. Consider the case `succ k ih`. Introduce `m v hv`.

Establish `h1 : (G - 1) *ᵥ v ∈ spanLt e (m + k)`. Establish `hle : spanLt e (m + (k + 1)) ≤ (spanLt e (m + k)).comap (Matrix.mulVecLin (G - 1))`. Unfold `spanLt`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨b, hb, rfl⟩`.

Establish `hb' : (b : ℕ) < m + (k + 1)` using `hb`. Simplify using `only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]`. Use `Submodule.span_mono ?_ (hG.1 b)` and prove the remaining obligations. Introduce and unpack `_ ⟨c, hc, rfl⟩`. Establish `hc' : (c : ℕ) < b` using `hc`.

Conclude with `⟨c, show (c : ℕ) < m + k by omega, rfl⟩`. Conclude with `hle hv`. Rewrite using `[pow_succ, ← mulVec_mulVec]`. Conclude with `ih m _ h1`.
-/
theorem pow_lower (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) {G : Matrix (Fin n) (Fin n) ℂ}
    (hG : InS e z G) (k : ℕ) : ∀ m, ∀ v ∈ spanLt e (m + k), (G - 1) ^ k *ᵥ v ∈ spanLt e m := by
  induction k with
  | zero => intro m v hv; simpa using hv
  | succ k ih =>
    intro m v hv
    have h1 : (G - 1) *ᵥ v ∈ spanLt e (m + k) := by
      have hle : spanLt e (m + (k + 1)) ≤ (spanLt e (m + k)).comap (Matrix.mulVecLin (G - 1)) := by
        unfold spanLt
        rw [Submodule.span_le]
        rintro _ ⟨b, hb, rfl⟩
        have hb' : (b : ℕ) < m + (k + 1) := hb
        simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
        refine Submodule.span_mono ?_ (hG.1 b)
        rintro _ ⟨c, hc, rfl⟩
        have hc' : (c : ℕ) < b := hc
        exact ⟨c, show (c : ℕ) < m + k by omega, rfl⟩
      exact hle hv
    rw [pow_succ, ← mulVec_mulVec]
    exact ih m _ h1

/- English proof (translation)
Use `set G := Formalism.MainNotions.S.uMat g with hGdef`. Establish `hN : InN ε e z G` using `hg`. Establish `hS' : InS e z (Formalism.MainNotions.S.uMat g⁻¹)` using `(Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI.SG ε e z).inv_mem hg.1`. Establish `hGG' : G * Formalism.MainNotions.S.uMat g⁻¹ = 1` using `Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.uMat_mul_inv ε g`. Establish `hiso` using `Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.isIsom_uMat ε g`.

Establish `adj : ∀ b : Fin r, ∀ w, hJ ε (e b) ((G - 1) *ᵥ w) = hJ ε ((Formalism.MainNotions.S.uMat g⁻¹ - 1) *ᵥ e b) w`. Introduce `b w`. Establish `h1 : hJ ε (e b) (G *ᵥ w) = hJ ε (Formalism.MainNotions.S.uMat g⁻¹ *ᵥ e b) w`. Use `hiso (Formalism.MainNotions.S.uMat g⁻¹ *ᵥ e b) w` as an intermediate fact. Rewrite `this` using `[mulVec_mulVec, hGG', one_mulVec]`.

Conclude with `this`. Rewrite using `[sub_mulVec, one_mulVec, hJ_sub_right, h1, sub_mulVec, one_mulVec, hJ_sub_left]`. Establish `step1 : ∀ k, ∀ x, ∀ b : Fin r, b.1 < k → hJ ε (e b) ((G - 1) ^ k *ᵥ x) = 0`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => intro x b hb`. Use linear arithmetic over natural numbers and integers. Consider the case `succ k ih`. Introduce `x b hb`. Rewrite using `[pow_succ', ← mulVec_mulVec, adj]`.

Use `orth_span ε e b.1 _ (fun c hc => ih x c (by omega)) _ (hS'.1 b)` and prove the remaining obligations. Establish `step2 : ∀ x, (G - 1) ^ (r + 1) *ᵥ x ∈ spanLt e r`. Introduce `x`. Rewrite using `[pow_succ', ← mulVec_mulVec]`. Conclude with `hN.2 _ (fun a => step1 r x a a.2)`.

Establish `step3 : ∀ x, (G - 1) ^ (2 * r + 1) *ᵥ x = 0`. Introduce `x`. Establish `: (G - 1) ^ (2 * r + 1) = (G - 1) ^ r * (G - 1) ^ (r + 1)`. Rewrite using `[← pow_add]`. Put the polynomial expressions in normal form.

Rewrite using `[this, ← mulVec_mulVec]`. Establish `hm` using `pow_lower e z hN.1 r 0 _ (by rw [zero_add]; exact step2 x)`. Rewrite `hm` using `[spanLt_zero]`. Conclude with `(Submodule.mem_bot ℂ).1 hm`. Use extensionality with `i j`.

Use `congrFun (step3 (Pi.single j 1)) i` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_single]`.
-/
theorem nilp (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Formalism.REAL.UJ ε)
    (hg : g ∈ NLoc ε e z) : (Formalism.MainNotions.S.uMat g - 1) ^ (2 * r + 1) = 0 := by
  set G := Formalism.MainNotions.S.uMat g with hGdef
  have hN : InN ε e z G := hg
  have hS' : InS e z (Formalism.MainNotions.S.uMat g⁻¹) :=
    (Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI.SG ε e z).inv_mem hg.1
  have hGG' : G * Formalism.MainNotions.S.uMat g⁻¹ = 1 := Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.uMat_mul_inv ε g
  have hiso := Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.isIsom_uMat ε g

  have adj : ∀ b : Fin r, ∀ w, hJ ε (e b) ((G - 1) *ᵥ w) = hJ ε ((Formalism.MainNotions.S.uMat g⁻¹ - 1) *ᵥ e b) w := by
    intro b w
    have h1 : hJ ε (e b) (G *ᵥ w) = hJ ε (Formalism.MainNotions.S.uMat g⁻¹ *ᵥ e b) w := by
      have := hiso (Formalism.MainNotions.S.uMat g⁻¹ *ᵥ e b) w
      rw [mulVec_mulVec, hGG', one_mulVec] at this
      exact this
    rw [sub_mulVec, one_mulVec, hJ_sub_right, h1, sub_mulVec, one_mulVec, hJ_sub_left]

  have step1 : ∀ k, ∀ x, ∀ b : Fin r, b.1 < k → hJ ε (e b) ((G - 1) ^ k *ᵥ x) = 0 := by
    intro k
    induction k with
    | zero => intro x b hb; omega
    | succ k ih =>
      intro x b hb
      rw [pow_succ', ← mulVec_mulVec, adj]
      refine orth_span ε e b.1 _ (fun c hc => ih x c (by omega)) _ (hS'.1 b)
  have step2 : ∀ x, (G - 1) ^ (r + 1) *ᵥ x ∈ spanLt e r := by
    intro x
    rw [pow_succ', ← mulVec_mulVec]
    exact hN.2 _ (fun a => step1 r x a a.2)
  have step3 : ∀ x, (G - 1) ^ (2 * r + 1) *ᵥ x = 0 := by
    intro x
    have : (G - 1) ^ (2 * r + 1) = (G - 1) ^ r * (G - 1) ^ (r + 1) := by
      rw [← pow_add]; ring_nf
    rw [this, ← mulVec_mulVec]
    have hm := pow_lower e z hN.1 r 0 _ (by rw [zero_add]; exact step2 x)
    rw [spanLt_zero] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  ext i j
  have := congrFun (step3 (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

end GlobalTheory.UnipRadNilp

/- English proof (translation)
Introduce `ε e z g hg` and use `GlobalTheory.UnipRadNilp.nilp ε e z g hg`.
-/
theorem GlobalTheory.unipRad_pow_eq_zero : ∀ {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Formalism.REAL.UJ ε), g ∈ Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc ε e z → (Formalism.MainNotions.S.uMat g - 1) ^ (2 * r + 1) = 0 :=
  fun ε e z g hg => GlobalTheory.UnipRadNilp.nilp ε e z g hg
