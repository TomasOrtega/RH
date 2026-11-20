import Mathlib
open TensorProduct Module

open Matrix

/- English proof (translation)
Introduce `F E _ _ _ _ B _ _ _ _ _ G act n _ _ A hfix Q hQ W hW`. Use `set Q' : Matrix n n B := (Q : Matrix n n B) with hQ'`. Establish `hQQ' : (↑Q⁻¹ : Matrix n n B) * Q' = 1` using `by rw [hQ']; exact_mod_cast Q.inv_mul`. Establish `hQQ : Q' * (↑Q⁻¹ : Matrix n n B) = 1` using `by rw [hQ']; exact_mod_cast Q.mul_inv`. Establish `key : ∀ g (y : n → B), (A g).mulVec (fun i => act g ((Q' *ᵥ y) i)) = Q' *ᵥ (fun i => act g (y i))`.

Introduce `g y`. Establish `h1 : (fun i => act g ((Q' *ᵥ y) i)) = Q'.map (act g) *ᵥ (fun i => act g (y i))`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec _ _ _ _`. Rewrite using `[h1, Matrix.mulVec_mulVec, hQ g]`.

Establish `inj : ∀ u v : n → B, Q' *ᵥ u = Q' *ᵥ v → u = v`. Introduce `u v h`. Establish `h2` using `congrArg (fun w => (↑Q⁻¹ : Matrix n n B) *ᵥ w) h`. Simplify using `only [Matrix.mulVec_mulVec] at h2`. Rewrite `h2` using `[hQQ', Matrix.one_mulVec, Matrix.one_mulVec]`. Then use the resulting hypothesis.

Set `φ : (n → E) →ₗ[F] (n → B)` to `{ toFun := fun c => Q' *ᵥ (fun i => algebraMap E B (c i)) map_add' := by`. Introduce `a b`. Establish `: (fun i => algebraMap E B ((a + b) i)) = (fun i => algebraMap E B (a i)) + (fun i => algebraMap E B (b i))`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Rewrite using `[this, Matrix.mulVec_add]`. Use the proof step `map_smul' := by`. Introduce `r a`. Establish `: (fun i => algebraMap E B ((r • a) i)) = r • (fun i => algebraMap E B (a i))`. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.smul_apply]`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]`. Rewrite using `[this, Matrix.mulVec_smul]`. Use `rfl }`. Establish `hφ : ∀ c, φ c = Q' *ᵥ (fun i => algebraMap E B (c i))` using `fun c => rfl`.

Establish `φinj : Function.Injective φ`. Introduce `a b h`. Rewrite `h` using `[hφ, hφ]`. Establish `h3` using `inj _ _ h`. Use function extensionality and compare the values at `i`.

Conclude with `(algebraMap E B).injective (congrFun h3 i)`. Establish `hWr : W = LinearMap.range φ`. Use extensionality with `x`. Rewrite using `[hW, LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx set y : n → B := (↑Q⁻¹ : Matrix n n B) *ᵥ x with hy`. Establish `hxy : Q' *ᵥ y = x` using `by rw [hy, Matrix.mulVec_mulVec, hQQ, Matrix.one_mulVec]`. Establish `hfixy : ∀ i g, act g (y i) = y i`. Introduce `i g`. Establish `h4` using `hx g`.

Rewrite `h4` using `[← hxy, key]`. Conclude with `congrFun (inj _ _ h4) i`. Use `choose c hc using fun i => (hfix (y i)).1 (hfixy i)`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[hφ, ← hxy]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `hc i`. Introduce and unpack `⟨c, rfl⟩ g`. Rewrite using `[hφ, key]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `((hfix _).2 ⟨c i, rfl⟩) g`. Substitute `hWr` using the available equality. Rewrite using `[LinearMap.finrank_range_of_inj φinj, Module.finrank_pi_fintype]`.

Simplify using `[Finset.sum_const, Finset.card_univ, mul_comm]`.
-/
theorem GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (B : Type) [CommRing B] [Nontrivial B] [Algebra F B] [Algebra E B] [IsScalarTower F E B] (G : Type) (act : G → B →+* B) (n : Type) [Fintype n] [DecidableEq n] (A : G → Matrix n n B), (∀ b : B, (∀ g, act g b = b) ↔ ∃ c : E, algebraMap E B c = b) → ∀ Q : GL n B, (∀ g, A g * (Q : Matrix n n B).map (act g) = Q) → ∀ W : Submodule F (n → B), (∀ x, x ∈ W ↔ ∀ g, (A g).mulVec (fun i => act g (x i)) = x) → finrank F ↥W = finrank F E * Fintype.card n := by
  intro F E _ _ _ _ B _ _ _ _ _ G act n _ _ A hfix Q hQ W hW
  set Q' : Matrix n n B := (Q : Matrix n n B) with hQ'
  have hQQ' : (↑Q⁻¹ : Matrix n n B) * Q' = 1 := by rw [hQ']; exact_mod_cast Q.inv_mul
  have hQQ : Q' * (↑Q⁻¹ : Matrix n n B) = 1 := by rw [hQ']; exact_mod_cast Q.mul_inv
  have key : ∀ g (y : n → B), (A g).mulVec (fun i => act g ((Q' *ᵥ y) i)) = Q' *ᵥ (fun i => act g (y i)) := by
    intro g y
    have h1 : (fun i => act g ((Q' *ᵥ y) i)) = Q'.map (act g) *ᵥ (fun i => act g (y i)) := by
      funext i; exact RingHom.map_mulVec _ _ _ _
    rw [h1, Matrix.mulVec_mulVec, hQ g]
  have inj : ∀ u v : n → B, Q' *ᵥ u = Q' *ᵥ v → u = v := by
    intro u v h
    have h2 := congrArg (fun w => (↑Q⁻¹ : Matrix n n B) *ᵥ w) h
    simp only [Matrix.mulVec_mulVec] at h2
    rwa [hQQ', Matrix.one_mulVec, Matrix.one_mulVec] at h2
  let φ : (n → E) →ₗ[F] (n → B) :=
    { toFun := fun c => Q' *ᵥ (fun i => algebraMap E B (c i))
      map_add' := by
        intro a b
        have : (fun i => algebraMap E B ((a + b) i)) = (fun i => algebraMap E B (a i)) + (fun i => algebraMap E B (b i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_add]
      map_smul' := by
        intro r a
        have : (fun i => algebraMap E B ((r • a) i)) = r • (fun i => algebraMap E B (a i)) := by
          funext i
          simp only [Pi.smul_apply]
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
        rw [this, Matrix.mulVec_smul]
        rfl }
  have hφ : ∀ c, φ c = Q' *ᵥ (fun i => algebraMap E B (c i)) := fun c => rfl
  have φinj : Function.Injective φ := by
    intro a b h
    rw [hφ, hφ] at h
    have h3 := inj _ _ h
    funext i
    exact (algebraMap E B).injective (congrFun h3 i)
  have hWr : W = LinearMap.range φ := by
    ext x
    rw [hW, LinearMap.mem_range]
    constructor
    · intro hx
      set y : n → B := (↑Q⁻¹ : Matrix n n B) *ᵥ x with hy
      have hxy : Q' *ᵥ y = x := by rw [hy, Matrix.mulVec_mulVec, hQQ, Matrix.one_mulVec]
      have hfixy : ∀ i g, act g (y i) = y i := by
        intro i g
        have h4 := hx g
        rw [← hxy, key] at h4
        exact congrFun (inj _ _ h4) i
      choose c hc using fun i => (hfix (y i)).1 (hfixy i)
      refine ⟨c, ?_⟩
      rw [hφ, ← hxy]
      congr 1
      funext i; exact hc i
    · rintro ⟨c, rfl⟩ g
      rw [hφ, key]
      congr 1
      funext i
      exact ((hfix _).2 ⟨c i, rfl⟩) g
  subst hWr
  rw [LinearMap.finrank_range_of_inj φinj, Module.finrank_pi_fintype]
  simp [Finset.sum_const, Finset.card_univ, mul_comm]
