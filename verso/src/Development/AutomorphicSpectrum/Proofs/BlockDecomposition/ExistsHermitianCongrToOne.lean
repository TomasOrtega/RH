import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardOrthonormalFramesHermitianSpaceStatement

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

/- English proof (translation)
Introduce `E _ τ q ε hR n T hT hdet`. Establish `hinv : ∀ a : E, τ (τ a) = a` using `hR.inv`. Establish `hq : 1 < q` using `hR.one_lt`. Establish `hcard : Nat.card (Fin n → E) = q ^ (2 * n)`. Rewrite using `[Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin, hR.card, ← pow_mul]`.

Establish `hcnt` using `GlobalTheory.T.card_orthonormal_frames_hermitian_space E τ q ε hR n n le_rfl (Fin n → E) (HermSp.ofMatrix hinv T hT hdet) hcard`. Establish `hε : ε = -1 ∨ ε = 1`. Break down `hR.eps with h | h` into its components or cases. Conclude with `Or.inl h.1`. Conclude with `Or.inr h.1`.

Establish `hne : Nat.card {x : Fin n → Fin n → E // ∀ i j : Fin n, (HermSp.ofMatrix hinv T hT hdet).h (x i) (x j) = if i = j then 1 else 0} ≠ 0`. Introduce `h0`. Rewrite `hcnt` using `[h0, Nat.cast_zero, eq_comm, Finset.prod_eq_zero_iff]`. Take `⟨i, -, hi⟩` from `hcnt`. Establish `hk : n - (i : ℕ) ≠ 0` using `Nat.sub_ne_zero_of_lt i.isLt`.

Break down `mul_eq_zero.mp hi with h | h` into its components or cases. Rewrite `h` using `[div_eq_zero_iff]`. Break down `h with h | h` into its components or cases. Establish `h'` using `pow_eq_zero_iff (n := 2 * (n - (i : ℕ))) (by omega) |>.mp h`. Rewrite `h'` using `[Nat.cast_eq_zero]`.

Use linear arithmetic over natural numbers and integers. Rewrite `h` using `[Nat.cast_eq_zero]`. Use linear arithmetic over natural numbers and integers. Rewrite `h` using `[sub_eq_zero]`. Establish `h2` using `congrArg abs h`.

Rewrite `h2` using `[abs_one, abs_pow, abs_div, Nat.abs_cast]`. Establish `key : ∀ {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F] (e : ℤ) (k : ℕ), (e = -1 ∨ e = 1) → k ≠ 0 → (1 : F) ≠ (|(e : F)| / (q : F)) ^ k`. Introduce `F _ _ _ e k he hk' hh`. Establish `hqF : (1 : F) < q` using `by exact_mod_cast hq`. Establish `habs : |(e : F)| = 1`.

Apply the tactic sequence `rcases he with rfl | rfl <;> simp`. Rewrite `hh` using `[habs]`. Establish `hlt : (1 / (q : F)) ^ k < 1` using `pow_lt_one₀ (by positivity) ((div_lt_one (by linarith)).mpr hqF) hk'`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `key ε _ hε hk h2`.

Take `⟨⟨x, hx⟩⟩` from `(Nat.card_ne_zero.mp hne).1`. Establish `hg : cT τ (Matrix.of fun a i => x i a) * T * (Matrix.of fun a i => x i a) = 1`. Use extensionality with `i j`. Rewrite using `[gram_apply hinv T hT hdet]`. Use `show (HermSp.ofMatrix hinv T hT hdet).h (x j) (x i) = (1 : Matrix (Fin n) (Fin n) E) i j`.

Rewrite using `[hx j i, Matrix.one_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg (Ne.symm h), if_neg h]`.

Conclude with `⟨_, Matrix.isUnit_det_of_left_inverse hg, hg⟩`.
-/
theorem exists_congr_one : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε →
    ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), cT τ T = T → IsUnit T.det →
      ∃ g : Matrix (Fin n) (Fin n) E, IsUnit g.det ∧ cT τ g * T * g = 1 := by
  intro E _ τ q ε hR n T hT hdet
  have hinv : ∀ a : E, τ (τ a) = a := hR.inv
  have hq : 1 < q := hR.one_lt
  have hcard : Nat.card (Fin n → E) = q ^ (2 * n) := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin, hR.card, ← pow_mul]
  have hcnt := GlobalTheory.T.card_orthonormal_frames_hermitian_space E τ q ε hR n n le_rfl (Fin n → E) (HermSp.ofMatrix hinv T hT hdet) hcard
  have hε : ε = -1 ∨ ε = 1 := by
    rcases hR.eps with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hne : Nat.card {x : Fin n → Fin n → E // ∀ i j : Fin n,
      (HermSp.ofMatrix hinv T hT hdet).h (x i) (x j) = if i = j then 1 else 0} ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero, eq_comm, Finset.prod_eq_zero_iff] at hcnt
    obtain ⟨i, -, hi⟩ := hcnt
    have hk : n - (i : ℕ) ≠ 0 := Nat.sub_ne_zero_of_lt i.isLt
    rcases mul_eq_zero.mp hi with h | h
    · rw [div_eq_zero_iff] at h
      rcases h with h | h
      · have h' := pow_eq_zero_iff (n := 2 * (n - (i : ℕ))) (by omega) |>.mp h
        rw [Nat.cast_eq_zero] at h'
        omega
      · rw [Nat.cast_eq_zero] at h
        omega
    · rw [sub_eq_zero] at h
      have h2 := congrArg abs h
      rw [abs_one, abs_pow, abs_div, Nat.abs_cast] at h2
      have key : ∀ {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F] (e : ℤ) (k : ℕ),
          (e = -1 ∨ e = 1) → k ≠ 0 → (1 : F) ≠ (|(e : F)| / (q : F)) ^ k := by
        intro F _ _ _ e k he hk' hh
        have hqF : (1 : F) < q := by exact_mod_cast hq
        have habs : |(e : F)| = 1 := by
          rcases he with rfl | rfl <;> simp
        rw [habs] at hh
        have hlt : (1 / (q : F)) ^ k < 1 :=
          pow_lt_one₀ (by positivity) ((div_lt_one (by linarith)).mpr hqF) hk'
        linarith
      exact key ε _ hε hk h2
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_ne_zero.mp hne).1
  have hg : cT τ (Matrix.of fun a i => x i a) * T * (Matrix.of fun a i => x i a) = 1 := by
    ext i j
    rw [gram_apply hinv T hT hdet]
    show (HermSp.ofMatrix hinv T hT hdet).h (x j) (x i) = (1 : Matrix (Fin n) (Fin n) E) i j
    rw [hx j i, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      simp
    · rw [if_neg (Ne.symm h), if_neg h]
  exact ⟨_, Matrix.isUnit_det_of_left_inverse hg, hg⟩

end GlobalTheory.CompanionTheory.UnrDens
