import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.CornerCoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DSigma

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Use `⟨P Y + s • (P Y)ᵀ, Submodule.add_mem _ h1 (Submodule.smul_mem _ s h2), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[transpose_add, transpose_smul, transpose_transpose, smul_add, smul_smul, hs, one_smul, add_comm]`. Introduce `g`. Establish `hA : ∀ k, dTw χ D.r (P Y) k = P (z k)` using `fun k => by`. Rewrite using `[← hPd, ← h, hPP]`.

Establish `hzT : (z g)ᵀ = s • z (D.σ g)`. Rewrite using `[hp, smul_smul, hs, one_smul]`. Establish `hB : s • dTw χ D.r (P Y)ᵀ g = (P (z g)ᵀ)ᵀ`. Rewrite using `[hzT, hPs, ← hA, Det.dSigma D χ (P Y) g hχ, transpose_smul, transpose_transpose]`. Establish `hlin : dTw χ D.r (P Y + s • (P Y)ᵀ) g = dTw χ D.r (P Y) g + s • dTw χ D.r (P Y)ᵀ g`.

Simplify using `only [dTw, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]`. Use `module`. Rewrite using `[hlin, hA, hB, hsum]`.
-/
private theorem shapiro_projection_twisted_cocycle {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (χ : G → F) (s : F)
    (z : G → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F) (hχ : ∀ g, χ (D.σ g) = χ g)
    (hs : s * s = 1) (hp : ∀ g, z (D.σ g) = s • (z g)ᵀ)
    (P : Matrix (Fin n) (Fin n) F → Matrix (Fin n) (Fin n) F)
    (hPP : ∀ Z, P (P Z) = P Z) (hPs : ∀ Z, P (s • Z) = s • P Z)
    (hPd : ∀ g, P (dTw χ D.r Y g) = dTw χ D.r (P Y) g)
    (hsum : ∀ g, P (z g) + (P (z g)ᵀ)ᵀ = z g)
    (h1 : P Y ∈ Od F F n D.a) (h2 : (P Y)ᵀ ∈ Od F F n D.a)
    (h : ∀ g, P (z g) = dTw χ D.r Y g) :
    ∃ Y' ∈ Od F F n D.a, s • Y'ᵀ = Y' ∧ ∀ g, z g = dTw χ D.r Y' g := by
  refine ⟨P Y + s • (P Y)ᵀ, Submodule.add_mem _ h1 (Submodule.smul_mem _ s h2), ?_, ?_⟩
  · rw [transpose_add, transpose_smul, transpose_transpose, smul_add, smul_smul, hs, one_smul,
      add_comm]
  · intro g
    have hA : ∀ k, dTw χ D.r (P Y) k = P (z k) := fun k => by
      rw [← hPd, ← h, hPP]
    have hzT : (z g)ᵀ = s • z (D.σ g) := by
      rw [hp, smul_smul, hs, one_smul]
    have hB : s • dTw χ D.r (P Y)ᵀ g = (P (z g)ᵀ)ᵀ := by
      rw [hzT, hPs, ← hA, Det.dSigma D χ (P Y) g hχ, transpose_smul, transpose_transpose]
    have hlin : dTw χ D.r (P Y + s • (P Y)ᵀ) g = dTw χ D.r (P Y) g + s • dTw χ D.r (P Y)ᵀ g := by
      simp only [dTw, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
      module
    rw [hlin, hA, hB, hsum]

/- English proof (translation)
Introduce `F G _ _ n D χ s z Y hχ hs hz hod hp h`. Take `⟨-, -, hd, hc⟩` from `UpperTheory.V.Pa.Det.cornerCoc D χ Set.univ z hz`. Establish `ht : ∀ Z : Matrix (Fin n) (Fin n) F, (cV' D.a Z)ᵀ = cV D.a Zᵀ` using `fun Z => by`. Use `(hc Zᵀ).2.2.1` as an intermediate fact. Rewrite `this` using `[transpose_transpose]`.

Rewrite using `[← this, transpose_transpose]`. Break down `h with h | h` into its components or cases. Use `shapiro_projection_twisted_cocycle D χ s z Y hχ hs hp (cV D.a) (fun Z => ?_) (fun Z => ?_) (fun g => (hd Y g).1) (fun g => ?_) (hc Y).1 ?_ h` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [cV, Matrix.of_apply]`.

Apply the tactic sequence `split_ifs <;> rfl`. Use extensionality with `i j`. Simplify using `only [cV, Matrix.of_apply, Matrix.smul_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[(hc _).2.2.1, transpose_transpose]`.

Conclude with `(hc _).2.2.2 (hod g)`. Rewrite using `[(hc _).2.2.1]`. Conclude with `(hc _).2.1`. Use `shapiro_projection_twisted_cocycle D χ s z Y hχ hs hp (cV' D.a) (fun Z => ?_) (fun Z => ?_) (fun g => (hd Y g).2) (fun g => ?_) (hc Y).2.1 ?_ h` and prove the remaining obligations. Use extensionality with `i j`.

Simplify using `only [cV', Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> rfl`. Use extensionality with `i j`. Simplify using `only [cV', Matrix.of_apply, Matrix.smul_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[ht, transpose_transpose, add_comm]`. Conclude with `(hc _).2.2.2 (hod g)`. Rewrite using `[ht]`. Conclude with `(hc _).1`.
-/
theorem UpperTheory.V.Pa.Det.shapiro :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (χ : G → F) (s : F) (z : G → Matrix (Fin n) (Fin n) F) (Y : Matrix (Fin n) (Fin n) F), (∀ g, χ (D.σ g) = χ g) → s * s = 1 → TwCoc χ D.r Set.univ z → (∀ g, z g ∈ Od F F n D.a) → (∀ g, z (D.σ g) = s • (z g)ᵀ) → ((∀ g, cV D.a (z g) = dTw χ D.r Y g) ∨ ∀ g, cV' D.a (z g) = dTw χ D.r Y g) → ∃ Y' ∈ Od F F n D.a, s • Y'ᵀ = Y' ∧ ∀ g, z g = dTw χ D.r Y' g := by
  intro F G _ _ n D χ s z Y hχ hs hz hod hp h
  obtain ⟨-, -, hd, hc⟩ := UpperTheory.V.Pa.Det.cornerCoc D χ Set.univ z hz
  have ht : ∀ Z : Matrix (Fin n) (Fin n) F, (cV' D.a Z)ᵀ = cV D.a Zᵀ := fun Z => by
    have := (hc Zᵀ).2.2.1
    rw [transpose_transpose] at this
    rw [← this, transpose_transpose]
  rcases h with h | h
  · refine shapiro_projection_twisted_cocycle D χ s z Y hχ hs hp (cV D.a) (fun Z => ?_) (fun Z => ?_) (fun g => (hd Y g).1)
      (fun g => ?_) (hc Y).1 ?_ h
    · ext i j
      simp only [cV, Matrix.of_apply]
      split_ifs <;> rfl
    · ext i j
      simp only [cV, Matrix.of_apply, Matrix.smul_apply]
      split_ifs <;> simp
    · rw [(hc _).2.2.1, transpose_transpose]
      exact (hc _).2.2.2 (hod g)
    · rw [(hc _).2.2.1]
      exact (hc _).2.1
  · refine shapiro_projection_twisted_cocycle D χ s z Y hχ hs hp (cV' D.a) (fun Z => ?_) (fun Z => ?_) (fun g => (hd Y g).2)
      (fun g => ?_) (hc Y).2.1 ?_ h
    · ext i j
      simp only [cV', Matrix.of_apply]
      split_ifs <;> rfl
    · ext i j
      simp only [cV', Matrix.of_apply, Matrix.smul_apply]
      split_ifs <;> simp
    · rw [ht, transpose_transpose, add_comm]
      exact (hc _).2.2.2 (hod g)
    · rw [ht]
      exact (hc _).1
