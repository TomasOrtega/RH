import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.ClosedOrbit

/- English proof (translation)
Use extensionality with `j`. Simplify using `[eLast, vecMul, dotProduct, Pi.single_apply]`.
-/
theorem eLast_vecMul {k : Type} [Field k] (n : ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :
    vecMul (eLast k n) M = M (Fin.last n) := by
  ext j
  simp [eLast, vecMul, dotProduct, Pi.single_apply]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hg a b ha hb`. Establish `hlt : (a : ℕ) - r < t` using `by have := a.isLt; omega`. Establish `ea : stdSum h (Sum.inr ⟨(a : ℕ) - r, hlt⟩) = a` using `Fin.ext (by rw [stdSum_inr]; simp only []; omega)`. Establish `eb : stdSum h (Sum.inl ⟨(b : ℕ), hb⟩) = b` using `Fin.ext (by rw [stdSum_inl])`.

Use `mem_parab_iff.1 hg true false (⟨(a : ℕ) - r, hlt⟩ : Fin t) (⟨(b : ℕ), hb⟩ : Fin r) (by decide)` as an intermediate fact. Rewrite `this` using `[two_true, two_false, ea, eb]`. Conclude with `this`. Introduce `hg`. Use `mem_parab_iff.2 ?_` and prove the remaining obligations.

Introduce `x y u v hxy`. Apply the tactic sequence `cases x <;> cases y <;> first | exact absurd hxy (by decide) | skip`. Use `hg _ _ ?_ ?_` and prove the remaining obligations. Use `show r ≤ ((stdSum h (Sum.inr u) : Fin N) : ℕ)`. Rewrite using `[stdSum_inr]`.

Use linear arithmetic over natural numbers and integers. Use `show ((stdSum h (Sum.inl v) : Fin N) : ℕ) < r`. Rewrite using `[stdSum_inl]`. Conclude with `v.isLt`.
-/
theorem mem_two_iff {k : Type} [Field k] {r t N : ℕ} (h : r + t = N) (g : GL (Fin N) k) :
    g ∈ parab k (two (stdSum h)) ↔
      ∀ a b : Fin N, r ≤ (a : ℕ) → (b : ℕ) < r → (g : Matrix (Fin N) (Fin N) k) a b = 0 := by
  constructor
  · intro hg a b ha hb
    have hlt : (a : ℕ) - r < t := by have := a.isLt; omega
    have ea : stdSum h (Sum.inr ⟨(a : ℕ) - r, hlt⟩) = a := Fin.ext (by rw [stdSum_inr]; simp only []; omega)
    have eb : stdSum h (Sum.inl ⟨(b : ℕ), hb⟩) = b := Fin.ext (by rw [stdSum_inl])
    have := mem_parab_iff.1 hg true false (⟨(a : ℕ) - r, hlt⟩ : Fin t) (⟨(b : ℕ), hb⟩ : Fin r) (by decide)
    rw [two_true, two_false, ea, eb] at this
    exact this
  · intro hg
    refine mem_parab_iff.2 ?_
    intro x y u v hxy
    cases x <;> cases y <;> first | exact absurd hxy (by decide) | skip
    refine hg _ _ ?_ ?_
    · show r ≤ ((stdSum h (Sum.inr u) : Fin N) : ℕ)
      rw [stdSum_inr]; omega
    · show ((stdSum h (Sum.inl v) : Fin N) : ℕ) < r
      rw [stdSum_inl]; exact v.isLt

/- English proof (translation)
Introduce `k _ _ _ _ i t h ht g`. Establish `hlast : i + 1 ≤ ((Fin.last (i + t) : Fin (i + t + 1)) : ℕ)`. Rewrite using `[Fin.val_last]`. Use linear arithmetic over natural numbers and integers. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨q, hq, p, hp, rfl⟩ a`. Establish `hpi : p⁻¹ ∈ Mir k (i + t)` using `inv_mem hp`. Establish `hpi' : vecMul (eLast k (i + t)) ((p⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t)` using `hpi`. Establish `e : (q * 1 * p)⁻¹ = p⁻¹ * q⁻¹` using `by simp`. Establish `h1 : vecMul (eLast k (i + t)) ((p⁻¹ * q⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = vecMul (eLast k (i + t)) ((q⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)`.

Rewrite using `[Units.val_mul, ← vecMul_vecMul, hpi']`. Establish `hrow` using `(eLast_vecMul (i + t) _).symm.trans (h1.trans (eLast_vecMul (i + t) _))`. Rewrite using `[e]`. Use `(congrFun hrow _).trans ((mem_two_iff h _).1 (inv_mem hq) _ _ hlast ?_)` and prove the remaining obligations. Rewrite using `[stdSum_inl]`.

Conclude with `a.isLt`. Introduce `hy classical`. Set `y : Fin (i + t + 1) → k` to `((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t))`. Establish `hyg : vecMul y (g : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t)`. Establish `: y = vecMul (eLast k (i + t)) ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)` using `(eLast_vecMul _ _).symm`.

Rewrite using `[this, vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one]`. Establish `hfirst : ∀ c : Fin (i + t + 1), (c : ℕ) < i + 1 → y c = 0`. Introduce `c hc`. Establish `e : stdSum h (Sum.inl ⟨(c : ℕ), hc⟩) = c` using `Fin.ext (by rw [stdSum_inl])`. Use `hy ⟨(c : ℕ), hc⟩` as an intermediate fact.

Rewrite `this` using `[e]`. Conclude with `this`. Choose the witnesses or unpack the hypotheses as in `⟨a₀, ha₀⟩ : ∃ c, y c ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Establish `h0 : y = 0` using `funext hcon`. Rewrite `hyg` using `[h0, zero_vecMul]`. Use `congrFun hyg (Fin.last (i + t))` as an intermediate fact. Simplify using `[eLast] at this`. Establish `hblock : i + 1 ≤ (a₀ : ℕ)`.

Assume the negation of the conclusion as `hlt`. Conclude with `ha₀ (hfirst a₀ (by omega))`. Set `σ : Equiv.Perm (Fin (i + t + 1))` to `Equiv.swap a₀ (Fin.last (i + t))`. Establish `hσ : ∀ r : Fin (i + t + 1), i + 1 ≤ (r : ℕ) → i + 1 ≤ (σ r : ℕ)`. Introduce `r hr`.

Simplify using `only [σ, Equiv.swap_apply_def]`. Use `split_ifs`. Conclude with `hlast`. Conclude with `hblock`. Conclude with `hr`.

Set `B : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k` to `((1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).updateRow a₀ y).submatrix σ id`. Establish `hdet : B.det ≠ 0`. Simplify using `only [B]`. Rewrite using `[Matrix.det_permute, det_updateRow_one]`. Use `mul_ne_zero ?_ ha₀` and prove the remaining obligations.

Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]`. Set `b : GL (Fin (i + t + 1)) k` to `Matrix.GeneralLinearGroup.mkOfDetNeZero B hdet`. Establish `hb : (b : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = B` using `rfl`. Establish `hbQ : b ∈ parab k (two (stdSum h))`. Use `(mem_two_iff h b).2 fun r c hr hc => ?_` and prove the remaining obligations.

Rewrite using `[hb]`. Simplify using `only [B, submatrix_apply, id]`. Distinguish the cases in `e : σ r = a₀`. Rewrite using `[e, updateRow_self]`. Conclude with `hfirst c hc`.

Rewrite using `[updateRow_ne e, one_apply_ne]`. Introduce `e2`. Use `hσ r hr` as an intermediate fact. Rewrite `this` using `[e2]`. Use linear arithmetic over natural numbers and integers.

Use `⟨b⁻¹, inv_mem hbQ, b * g, ?_, by simp⟩` and prove the remaining obligations. Use `show vecMul (eLast k (i + t)) ((b * g : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t)`. Establish `hB : B (Fin.last (i + t)) = y`. Use function extensionality and compare the values at `c`. Simplify using `[B, σ]`.

Rewrite using `[Units.val_mul, ← vecMul_vecMul, eLast_vecMul, hb, hB]`. Conclude with `hyg`.
-/
theorem mem_dcos_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ}
    (h : (i + 1) + t = i + t + 1), 0 < t → ∀ g : GL (Fin (i + t + 1)) k,
    g ∈ dcos (parab k (two (stdSum h))) (Mir k (i + t)) 1 ↔
      ∀ a : Fin (i + 1), ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
        (Fin.last (i + t)) (stdSum h (Sum.inl a)) = 0 := by
  intro k _ _ _ _ i t h ht g
  have hlast : i + 1 ≤ ((Fin.last (i + t) : Fin (i + t + 1)) : ℕ) := by
    rw [Fin.val_last]; omega
  constructor
  · rintro ⟨q, hq, p, hp, rfl⟩ a
    have hpi : p⁻¹ ∈ Mir k (i + t) := inv_mem hp
    have hpi' : vecMul (eLast k (i + t)) ((p⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
        eLast k (i + t) := hpi
    have e : (q * 1 * p)⁻¹ = p⁻¹ * q⁻¹ := by simp
    have h1 : vecMul (eLast k (i + t)) ((p⁻¹ * q⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
        vecMul (eLast k (i + t)) ((q⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) := by
      rw [Units.val_mul, ← vecMul_vecMul, hpi']
    have hrow := (eLast_vecMul (i + t) _).symm.trans (h1.trans (eLast_vecMul (i + t) _))
    rw [e]
    refine (congrFun hrow _).trans ((mem_two_iff h _).1 (inv_mem hq) _ _ hlast ?_)
    rw [stdSum_inl]; exact a.isLt
  · intro hy
    classical
    let y : Fin (i + t + 1) → k :=
      ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t))
    have hyg : vecMul y (g : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t) := by
      have : y = vecMul (eLast k (i + t))
          ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) := (eLast_vecMul _ _).symm
      rw [this, vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one]
    have hfirst : ∀ c : Fin (i + t + 1), (c : ℕ) < i + 1 → y c = 0 := by
      intro c hc
      have e : stdSum h (Sum.inl ⟨(c : ℕ), hc⟩) = c := Fin.ext (by rw [stdSum_inl])
      have := hy ⟨(c : ℕ), hc⟩
      rw [e] at this
      exact this
    obtain ⟨a₀, ha₀⟩ : ∃ c, y c ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have h0 : y = 0 := funext hcon
      rw [h0, zero_vecMul] at hyg
      have := congrFun hyg (Fin.last (i + t))
      simp [eLast] at this
    have hblock : i + 1 ≤ (a₀ : ℕ) := by
      by_contra hlt
      exact ha₀ (hfirst a₀ (by omega))
    let σ : Equiv.Perm (Fin (i + t + 1)) := Equiv.swap a₀ (Fin.last (i + t))
    have hσ : ∀ r : Fin (i + t + 1), i + 1 ≤ (r : ℕ) → i + 1 ≤ (σ r : ℕ) := by
      intro r hr
      simp only [σ, Equiv.swap_apply_def]
      split_ifs
      · exact hlast
      · exact hblock
      · exact hr
    let B : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k :=
      ((1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).updateRow a₀ y).submatrix σ id
    have hdet : B.det ≠ 0 := by
      simp only [B]
      rw [Matrix.det_permute, det_updateRow_one]
      refine mul_ne_zero ?_ ha₀
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]
    let b : GL (Fin (i + t + 1)) k := Matrix.GeneralLinearGroup.mkOfDetNeZero B hdet
    have hb : (b : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = B := rfl
    have hbQ : b ∈ parab k (two (stdSum h)) := by
      refine (mem_two_iff h b).2 fun r c hr hc => ?_
      rw [hb]
      simp only [B, submatrix_apply, id]
      by_cases e : σ r = a₀
      · rw [e, updateRow_self]
        exact hfirst c hc
      · rw [updateRow_ne e, one_apply_ne]
        intro e2
        have := hσ r hr
        rw [e2] at this
        omega
    refine ⟨b⁻¹, inv_mem hbQ, b * g, ?_, by simp⟩
    show vecMul (eLast k (i + t)) ((b * g : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = eLast k (i + t)
    have hB : B (Fin.last (i + t)) = y := by
      funext c
      simp [B, σ]
    rw [Units.val_mul, ← vecMul_vecMul, eLast_vecMul, hb, hB]
    exact hyg

end GlobalTheory.CompanionTheory.BZRes.ClosedOrbit

end
