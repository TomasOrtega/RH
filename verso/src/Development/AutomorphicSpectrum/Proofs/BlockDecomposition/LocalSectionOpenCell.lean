import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `e : (two (stdSum h)).symm (stdSum h (Sum.inl (Fin.last i))) = ⟨false, Fin.last i⟩`. Rewrite using `[Equiv.symm_apply_eq]`. Both sides reduce to the same expression. Use `show ePG i t ((two (stdSum h)).symm (stdSum h (Sum.inl (Fin.last i)))) = _`. Rewrite using `[e, ePG_false_last]`.
-/
theorem wPerm_last {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    wPerm h (stdSum h (Sum.inl (Fin.last i))) = Fin.last (i + t) := by
  have e : (two (stdSum h)).symm (stdSum h (Sum.inl (Fin.last i))) = ⟨false, Fin.last i⟩ := by
    rw [Equiv.symm_apply_eq]
    rfl
  show ePG i t ((two (stdSum h)).symm (stdSum h (Sum.inl (Fin.last i)))) = _
  rw [e, ePG_false_last]

/- English proof (translation)
Use extensionality with `c`. Rewrite using `[Matrix.single_one_vecMul]`. Use `show (1 : Matrix _ _ k) (wPerm h (stdSum h (Sum.inl (Fin.last i)))) c = _`. Rewrite using `[wPerm_last]`. Simplify using `[eLast, Matrix.one_apply, Pi.single_apply, eq_comm]`.
-/
theorem vecMul_wGL {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    vecMul (Pi.single (stdSum h (Sum.inl (Fin.last i))) (1 : k))
      (wGL k h : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t) := by
  ext c
  rw [Matrix.single_one_vecMul]
  show (1 : Matrix _ _ k) (wPerm h (stdSum h (Sum.inl (Fin.last i)))) c = _
  rw [wPerm_last]
  simp [eLast, Matrix.one_apply, Pi.single_apply, eq_comm]

/- English proof (translation)
Rewrite using `[← vecMul_wGL (k := k) h, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]`.
-/
theorem vecMul_wGL_inv {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    vecMul (eLast k (i + t)) (((wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      Pi.single (stdSum h (Sum.inl (Fin.last i))) (1 : k) := by
  rw [← vecMul_wGL (k := k) h, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

/- English proof (translation)
Rewrite using `[mem_parab_iff]`. Introduce `a b x z hab`. Establish `hab' : a = true ∧ b = false` using `by clear x z revert hab`. Apply the tactic sequence `cases a <;> cases b <;> decide`. Take `⟨rfl, rfl⟩` from `hab'`.

Establish `hne : two (stdSum h) ⟨true, x⟩ ≠ stdSum h (Sum.inl (Fin.last i))`. Introduce `e`. Use `(stdSum h).injective e` as an intermediate fact. Simplify using `at this`. Establish `hne2 : two (stdSum h) ⟨true, x⟩ ≠ two (stdSum h) ⟨false, z⟩`.

Introduce `e`. Use `(two (stdSum h)).injective e` as an intermediate fact. Simplify using `at this`. Rewrite using `[hg, Matrix.updateRow_ne hne, Matrix.one_apply_ne hne2]`.
-/
theorem mem_parab_of_row {i t : ℕ} (h : (i + 1) + t = i + t + 1) (g : GL (Fin (i + t + 1)) k)
    (y : Fin (i + t + 1) → k)
    (hg : (g : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      (1 : Matrix _ _ k).updateRow (stdSum h (Sum.inl (Fin.last i))) y) :
    g ∈ parab k (two (stdSum h)) := by
  rw [mem_parab_iff]
  intro a b x z hab
  have hab' : a = true ∧ b = false := by
    clear x z
    revert hab
    cases a <;> cases b <;> decide
  obtain ⟨rfl, rfl⟩ := hab'
  have hne : two (stdSum h) ⟨true, x⟩ ≠ stdSum h (Sum.inl (Fin.last i)) := by
    intro e
    have := (stdSum h).injective e
    simp at this
  have hne2 : two (stdSum h) ⟨true, x⟩ ≠ two (stdSum h) ⟨false, z⟩ := by
    intro e
    have := (two (stdSum h)).injective e
    simp at this
  rw [hg, Matrix.updateRow_ne hne, Matrix.one_apply_ne hne2]

/- English proof (translation)
Introduce `OQ hOQ OP hOP`. Use `set a₁ := stdSum h (Sum.inl (Fin.last i)) with ha₁`. Use `set w := wGL k h with hw`. Take `⟨b, hbc, hb1, hb⟩` from `exists_rowSec (k := k) a₁`. Set `y : GL (Fin (i + t + 1)) k → Fin (i + t + 1) → k` to `fun u => vecMul (eLast k (i + t)) (((w * u)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)`.

Establish `hyc : Continuous y` using `continuous_const.matrix_vecMul (Units.continuous_val.comp (continuous_const.mul continuous_id).inv)`. Establish `hy1 : y 1 = Pi.single a₁ 1`. Simplify using `only [y, mul_one]`. Conclude with `vecMul_wGL_inv h`. Establish `hBc : ContinuousAt (fun u => b (y u)) 1` using `ContinuousAt.comp (f := y) (g := b) (by rw [hy1]; exact hbc) hyc.continuousAt`.

Establish `hB1 : b (y 1) = 1` using `by rw [hy1, hb1]`. Establish `hS : ContinuousAt (fun u => (b (y u))⁻¹) 1` using `hBc.inv`. Establish `hP : ContinuousAt (fun u => w⁻¹ * b (y u) * w * u) 1` using `((continuousAt_const.mul hBc).mul continuousAt_const).mul continuousAt_id`. Establish `hS' : ∀ᶠ u in 𝓝 (1 : GL (Fin (i + t + 1)) k), (b (y u))⁻¹ ∈ OQ` using `hS.eventually_mem (by simpa [hB1] using hOQ)`. Establish `hP' : ∀ᶠ u in 𝓝 (1 : GL (Fin (i + t + 1)) k), w⁻¹ * b (y u) * w * u ∈ OP` using `hP.eventually_mem (by simpa [hB1] using hOP)`.

Establish `hne : ∀ᶠ u in 𝓝 (1 : GL (Fin (i + t + 1)) k), y u a₁ ≠ 0`. Establish `: ContinuousAt (fun u => y u a₁) 1` using `((continuous_apply a₁).comp hyc).continuousAt`. Conclude with `this.eventually_ne (by rw [hy1]; simp)`. Use `⟨_, hS'.and (hP'.and hne), ?_⟩` and prove the remaining obligations. Introduce and unpack `u ⟨h1, h2, h3⟩ -`.

Establish `hBm` using `hb (y u) h3`. Use `⟨(b (y u))⁻¹, inv_mem (mem_parab_of_row h _ _ hBm), h1, w⁻¹ * b (y u) * w * u, ?_, h2, by group⟩` and prove the remaining obligations. Use `show vecMul (eLast k (i + t)) _ = eLast k (i + t)`. Establish `e1 : vecMul (vecMul (eLast k (i + t)) ((w⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)) (b (y u) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = y u`. Rewrite using `[vecMul_wGL_inv h, hBm, Matrix.single_one_vecMul]`.

Conclude with `Matrix.updateRow_self`. Establish `e2 : vecMul (y u) ((w * u : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t)`. Simplify using `only [y]`. Rewrite using `[Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]`. Establish `e3 : ((w⁻¹ * b (y u) * w * u : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = ((w⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) * (b (y u) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) * ((w * u : GL (Fin (i + t + 1)) k) …`.

Simplify using `only [Units.val_mul, Matrix.mul_assoc]`. Rewrite using `[e3, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, e1, e2]`.
-/
theorem locSec_wGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ}
    (h : (i + 1) + t = i + t + 1) : LocSec (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h) := by
  intro OQ hOQ OP hOP
  set a₁ := stdSum h (Sum.inl (Fin.last i)) with ha₁
  set w := wGL k h with hw
  obtain ⟨b, hbc, hb1, hb⟩ := exists_rowSec (k := k) a₁
  let y : GL (Fin (i + t + 1)) k → Fin (i + t + 1) → k := fun u =>
    vecMul (eLast k (i + t)) (((w * u)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
  have hyc : Continuous y :=
    continuous_const.matrix_vecMul (Units.continuous_val.comp (continuous_const.mul continuous_id).inv)
  have hy1 : y 1 = Pi.single a₁ 1 := by
    simp only [y, mul_one]
    exact vecMul_wGL_inv h
  have hBc : ContinuousAt (fun u => b (y u)) 1 :=
    ContinuousAt.comp (f := y) (g := b) (by rw [hy1]; exact hbc) hyc.continuousAt
  have hB1 : b (y 1) = 1 := by rw [hy1, hb1]
  have hS : ContinuousAt (fun u => (b (y u))⁻¹) 1 := hBc.inv
  have hP : ContinuousAt (fun u => w⁻¹ * b (y u) * w * u) 1 :=
    ((continuousAt_const.mul hBc).mul continuousAt_const).mul continuousAt_id
  have hS' : ∀ᶠ u in 𝓝 (1 : GL (Fin (i + t + 1)) k), (b (y u))⁻¹ ∈ OQ :=
    hS.eventually_mem (by simpa [hB1] using hOQ)
  have hP' : ∀ᶠ u in 𝓝 (1 : GL (Fin (i + t + 1)) k), w⁻¹ * b (y u) * w * u ∈ OP :=
    hP.eventually_mem (by simpa [hB1] using hOP)
  have hne : ∀ᶠ u in 𝓝 (1 : GL (Fin (i + t + 1)) k), y u a₁ ≠ 0 := by
    have : ContinuousAt (fun u => y u a₁) 1 := ((continuous_apply a₁).comp hyc).continuousAt
    exact this.eventually_ne (by rw [hy1]; simp)
  refine ⟨_, hS'.and (hP'.and hne), ?_⟩
  rintro u ⟨h1, h2, h3⟩ -
  have hBm := hb (y u) h3
  refine ⟨(b (y u))⁻¹, inv_mem (mem_parab_of_row h _ _ hBm), h1, w⁻¹ * b (y u) * w * u, ?_, h2, by group⟩
  show vecMul (eLast k (i + t)) _ = eLast k (i + t)
  have e1 : vecMul (vecMul (eLast k (i + t)) ((w⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k))
      (b (y u) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = y u := by
    rw [vecMul_wGL_inv h, hBm, Matrix.single_one_vecMul]
    exact Matrix.updateRow_self
  have e2 : vecMul (y u) ((w * u : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t) := by
    simp only [y]
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  have e3 : ((w⁻¹ * b (y u) * w * u : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      ((w⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) *
        (b (y u) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) *
          ((w * u : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) := by
    simp only [Units.val_mul, Matrix.mul_assoc]
  rw [e3, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, e1, e2]

end GlobalTheory.CompanionTheory.BZRes

end
