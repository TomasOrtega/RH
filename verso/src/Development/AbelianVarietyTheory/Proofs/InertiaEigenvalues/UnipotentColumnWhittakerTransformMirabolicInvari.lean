import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCoefficientRationalMirabolicMulStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

/- English proof (translation)
Introduce `i k h` and use `hγ i k (by omega)`.
-/
theorem IsMir.succ {E : Type} [Field E] {a m : ℕ} {γ : GL (Fin a) E} (hγ : IsMir m γ) : IsMir (m + 1) γ :=
  fun i k h => hγ i k (by omega)

/- English proof (translation)
Introduce `E _ _ a ψ hψ m f hma hf γ hγ g`. Establish `key` using `GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E a ψ hψ m f hf.cont hf.left γ hγ.succ (eLast a (m + 1)) g`. Unfold `colT`. Rewrite using `[key]`. Use `congr 1`.

Use function extensionality and compare the values at `t`. Set `s0 : UnipotentBlockColumnIndex a (m + 1) (m + 1)` to `⟨(⟨m, by omega⟩, ⟨m + 1, hma⟩), Nat.lt_succ_self m, le_refl _, le_refl _⟩`. Rewrite using `[Finset.sum_eq_single s0]`. Establish `h1 : eLast (E` using `E) a (m + 1) s0 = 1 := by simp [eLast, s0]`. Rewrite using `[h1, one_mul, hγ _ _ (Or.inl (le_refl m))]`.

Establish `ht` using `t.2.1`. Simplify using `only [eLast, Matrix.one_apply]`. Distinguish the cases in `h : (t.1.1 : ℕ) = m`. Rewrite using `[if_pos (Fin.ext h.symm), if_pos (by omega)]`. Rewrite using `[if_neg (fun e => h (congrArg Fin.val e).symm), if_neg (by omega)]`.

Introduce `s _ hs`. Establish `h0 : eLast (E` using `E) a (m + 1) s = 0 := by`. Simplify using `only [eLast]`. Rewrite using `[if_neg]`. Introduce `e`.

Apply `hs` to reduce the goal to its premises. Establish `h2` using `s.2.2`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `Prod.ext (Fin.ext (by simp [s0]; omega)) (Fin.ext (by simp [s0]; omega))`. Rewrite using `[h0, zero_mul]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem colT_isMir_invariant : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ →
    ∀ (m : ℕ) (f : GA E a → ℂ), m + 1 < a → Good ψ (m + 1) f → ∀ γ : GL (Fin a) E, IsMir m γ →
    ∀ g, colT ψ (m + 1) f (ratGL E a γ * g) = colT ψ (m + 1) f g := by
  intro E _ _ a ψ hψ m f hma hf γ hγ g
  have key := GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E a ψ hψ m f hf.cont hf.left γ hγ.succ (eLast a (m + 1)) g
  unfold colT
  rw [key]
  congr 1
  funext t
  let s0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) := ⟨(⟨m, by omega⟩, ⟨m + 1, hma⟩), Nat.lt_succ_self m, le_refl _, le_refl _⟩
  rw [Finset.sum_eq_single s0]
  · have h1 : eLast (E := E) a (m + 1) s0 = 1 := by simp [eLast, s0]
    rw [h1, one_mul, hγ _ _ (Or.inl (le_refl m))]
    have ht := t.2.1
    simp only [eLast, Matrix.one_apply]
    by_cases h : (t.1.1 : ℕ) = m
    · rw [if_pos (Fin.ext h.symm), if_pos (by omega)]
    · rw [if_neg (fun e => h (congrArg Fin.val e).symm), if_neg (by omega)]
  · intro s _ hs
    have h0 : eLast (E := E) a (m + 1) s = 0 := by
      simp only [eLast]
      rw [if_neg]
      intro e
      apply hs
      have h2 := s.2.2
      apply Subtype.ext
      exact Prod.ext (Fin.ext (by simp [s0]; omega)) (Fin.ext (by simp [s0]; omega))
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end GlobalTheory.CuspGeneric
