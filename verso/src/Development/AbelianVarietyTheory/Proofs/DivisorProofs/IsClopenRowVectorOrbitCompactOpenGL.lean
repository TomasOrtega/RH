import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp

noncomputable section

open Matrix Topology

namespace GlobalTheory.JSW.Orbit

/- English proof (translation)
Introduce `F _ n B hBc hBo r₀ hr₀`. Establish `hset : {r : Fin n → F | ∃ b ∈ B, r = r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F)} = (fun b : GL (Fin n) F => r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F)) '' (B : Set (GL (Fin n) F))`. Use extensionality with `r`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, rfl⟩`.

Conclude with `⟨b, hb, rfl⟩`. Introduce and unpack `⟨b, hb, rfl⟩`. Conclude with `⟨b, hb, rfl⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hset]`.

Conclude with `(hBc.image (continuous_const.matrix_vecMul Units.continuous_val)).isClosed`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce and unpack `_ ⟨b, hb, rfl⟩`. Use `set r := r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F) with hr`. Establish `hr0 : r ≠ 0`.

Introduce `h`. Apply `hr₀` to reduce the goal to its premises. Establish `: r ᵥ* ((b⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = r₀`. Rewrite using `[hr, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]`. Rewrite using `[← this, h, zero_vecMul]`.

Take `⟨i, hi⟩` from `Function.ne_iff.1 hr0`. Set `c : Fin n → F` to `Pi.single i (r i)⁻¹`. Establish `hc : r ⬝ᵥ c = 1`. Simplify using `only [c, dotProduct_single]`. Conclude with `mul_inv_cancel₀ hi`.

Take `⟨O, hO, hOB⟩` from `GlobalTheory.JSW.KirFin.isEmbedding_coe.isInducing.isOpen_iff.1 hBo`. Set `s : (Fin n → F) → Matrix (Fin n) (Fin n) F` to `fun y => 1 + vecMulVec c (y - r)`. Establish `hs : Continuous s` using `continuous_const.add (continuous_const.matrix_vecMulVec (continuous_id.sub continuous_const))`. Establish `hs1 : s r = 1` using `by simp [s]`. Establish `h1O : (1 : Matrix (Fin n) (Fin n) F) ∈ O`.

Establish `: (1 : GL (Fin n) F) ∈ (B : Set (GL (Fin n) F))` using `B.one_mem`. Rewrite `this` using `[← hOB]`. Conclude with `this`. Establish `e1 : ∀ᶠ y in 𝓝 r, s y ∈ O` using `hs.continuousAt.eventually_mem (hO.mem_nhds (by rw [hs1]; exact h1O))`. Establish `e2 : ∀ᶠ y in 𝓝 r, (s y).det ≠ 0` using `hs.matrix_det.continuousAt.eventually_ne (by simp [hs1])`.

Use `filter_upwards [e1, e2] with y hy1 hy2`. Set `u : GL (Fin n) F` to `GeneralLinearGroup.mkOfDetNeZero _ hy2`. Establish `hu : u ∈ B`. Establish `: u ∈ (fun g : GL (Fin n) F => g.val) ⁻¹' O` using `hy1`. Rewrite `this` using `[hOB]`.

Conclude with `this`. Use `⟨b * u, B.mul_mem hb hu, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `y = r₀ ᵥ* ((b : Matrix (Fin n) (Fin n) F) * s y)`. Rewrite using `[← vecMul_vecMul, ← hr]`. Express the relevant statement in the definitionally equal form `y = r ᵥ* (1 + vecMulVec c (y - r))`.

Rewrite using `[vecMul_add, vecMul_one, vecMul_vecMulVec, hc]`. Simplify using the standard rewrite rules.
-/
theorem isClopen_orbit : ∀ {F : Type} [NormedField F] {n : ℕ} (B : Subgroup (GL (Fin n) F)),
    IsCompact (B : Set (GL (Fin n) F)) → IsOpen (B : Set (GL (Fin n) F)) → ∀ r₀ : Fin n → F, r₀ ≠ 0 →
    IsClopen {r : Fin n → F | ∃ b ∈ B, r = r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F)} := by
  intro F _ n B hBc hBo r₀ hr₀
  classical
  have hset : {r : Fin n → F | ∃ b ∈ B, r = r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F)} =
      (fun b : GL (Fin n) F => r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F)) '' (B : Set (GL (Fin n) F)) := by
    ext r
    constructor
    · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact (hBc.image (continuous_const.matrix_vecMul Units.continuous_val)).isClosed
  · rw [isOpen_iff_mem_nhds]
    rintro _ ⟨b, hb, rfl⟩
    set r := r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F) with hr
    have hr0 : r ≠ 0 := by
      intro h
      apply hr₀
      have : r ᵥ* ((b⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = r₀ := by
        rw [hr, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
      rw [← this, h, zero_vecMul]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hr0
    let c : Fin n → F := Pi.single i (r i)⁻¹
    have hc : r ⬝ᵥ c = 1 := by
      simp only [c, dotProduct_single]
      exact mul_inv_cancel₀ hi
    obtain ⟨O, hO, hOB⟩ := GlobalTheory.JSW.KirFin.isEmbedding_coe.isInducing.isOpen_iff.1 hBo
    let s : (Fin n → F) → Matrix (Fin n) (Fin n) F := fun y => 1 + vecMulVec c (y - r)
    have hs : Continuous s :=
      continuous_const.add (continuous_const.matrix_vecMulVec (continuous_id.sub continuous_const))
    have hs1 : s r = 1 := by simp [s]
    have h1O : (1 : Matrix (Fin n) (Fin n) F) ∈ O := by
      have : (1 : GL (Fin n) F) ∈ (B : Set (GL (Fin n) F)) := B.one_mem
      rw [← hOB] at this
      exact this
    have e1 : ∀ᶠ y in 𝓝 r, s y ∈ O := hs.continuousAt.eventually_mem (hO.mem_nhds (by rw [hs1]; exact h1O))
    have e2 : ∀ᶠ y in 𝓝 r, (s y).det ≠ 0 := hs.matrix_det.continuousAt.eventually_ne (by simp [hs1])
    filter_upwards [e1, e2] with y hy1 hy2
    let u : GL (Fin n) F := GeneralLinearGroup.mkOfDetNeZero _ hy2
    have hu : u ∈ B := by
      have : u ∈ (fun g : GL (Fin n) F => g.val) ⁻¹' O := hy1
      rw [hOB] at this
      exact this
    refine ⟨b * u, B.mul_mem hb hu, ?_⟩
    change y = r₀ ᵥ* ((b : Matrix (Fin n) (Fin n) F) * s y)
    rw [← vecMul_vecMul, ← hr]
    change y = r ᵥ* (1 + vecMulVec c (y - r))
    rw [vecMul_add, vecMul_one, vecMul_vecMulVec, hc]
    simp

end GlobalTheory.JSW.Orbit
