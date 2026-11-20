import Mathlib

namespace GlobalTheory.TraceFormNondegenerate

/- English proof (translation)
Use extensionality with `i j`. Establish `hij` using `h (Matrix.single j i 1)`. Rewrite `hij` using `[Matrix.trace_mul_single]`. Simplify using `using hij`.
-/
theorem eq_zero_of_trace_mul {K : Type} [Field K] {n : ℕ} (X : Matrix (Fin n) (Fin n) K)
    (h : ∀ Y : Matrix (Fin n) (Fin n) K, Matrix.trace (X * Y) = 0) : X = 0 := by
  ext i j
  have hij := h (Matrix.single j i 1)
  rw [Matrix.trace_mul_single] at hij
  simpa using hij

/- English proof (translation)
Take `⟨A, hA⟩ : ∃ A : (Γ →₀ K) →ₗ[K] Matrix (Fin n) (Fin n) K, A = Finsupp.linearCombination K (⇑M)` from `⟨_, rfl⟩`. Take `⟨B, hB⟩ : ∃ B : (Γ →₀ K) →ₗ[K] Matrix (Fin n) (Fin n) K, B = Finsupp.linearCombination K (⇑N)` from `⟨_, rfl⟩`. Establish `hprod : ∀ (f : Γ →₀ K) (h : Γ), Matrix.trace (B f * N h) = Matrix.trace (A f * M h)`. Introduce `f h`. Proceed by induction on `f using Finsupp.induction_linear with`.

Consider the case `zero => simp`. Consider the case `add f g hf hg => simp [add_mul, hf, hg]`. Consider the case `single g a`. Substitute `hA hB` using the available equality. Simplify using `only [Finsupp.linearCombination_single, smul_mul_assoc, Matrix.trace_smul, ← map_mul, htr]`.

Establish `hker : LinearMap.ker A ≤ LinearMap.ker B`. Introduce `f hf`. Rewrite `hf`, the goal using `[LinearMap.mem_ker]`. Apply `eq_zero_of_trace_mul` to reduce the goal to its premises. Introduce `Y`.

Establish `hY : Y ∈ Submodule.span K (Set.range (⇑N))` using `hN ▸ Submodule.mem_top`. Set `ℓ : Matrix (Fin n) (Fin n) K →ₗ[K] K` to `(Matrix.traceLinearMap (Fin n) K K).comp (LinearMap.mulLeft K (B f))`. Establish `hle : Submodule.span K (Set.range (⇑N)) ≤ LinearMap.ker ℓ`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`.

Simplify using `[ℓ, hprod, hf]`. Simplify `hle hY` using `[ℓ]`. Set `φ : LinearMap.range A →ₗ[K] Matrix (Fin n) (Fin n) K` to `((LinearMap.ker A).liftQ B hker).comp A.quotKerEquivRange.symm.toLinearMap`. Establish `hφ : ∀ f, φ ⟨A f, LinearMap.mem_range_self A f⟩ = B f`. Introduce `f`.

Simplify using `[φ]`. Establish `hφtop : LinearMap.range φ = ⊤`. Rewrite using `[eq_top_iff]`. Introduce and unpack `Y -`. Establish `hY : Y ∈ LinearMap.range B`.

Rewrite using `[hB, Finsupp.range_linearCombination, hN]`. Conclude with `Submodule.mem_top`. Take `⟨f, rfl⟩` from `hY`. Conclude with `⟨_, hφ f⟩`. Establish `h1` using `LinearMap.finrank_range_le φ`.

Rewrite `h1` using `[hφtop, finrank_top]`. Establish `h2 : LinearMap.range A = ⊤` using `Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) h1)`. Rewrite `h2` using `[hA, Finsupp.range_linearCombination]`. Then use the resulting hypothesis.
-/
theorem span_eq_top_of_trace_eq {Γ K : Type} [Monoid Γ] [Field K] {n : ℕ}
    (M N : Γ →* Matrix (Fin n) (Fin n) K)
    (htr : ∀ g : Γ, Matrix.trace (M g) = Matrix.trace (N g))
    (hN : Submodule.span K (Set.range (⇑N : Γ → Matrix (Fin n) (Fin n) K)) = ⊤) :
    Submodule.span K (Set.range (⇑M : Γ → Matrix (Fin n) (Fin n) K)) = ⊤ := by
  obtain ⟨A, hA⟩ : ∃ A : (Γ →₀ K) →ₗ[K] Matrix (Fin n) (Fin n) K,
      A = Finsupp.linearCombination K (⇑M) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : (Γ →₀ K) →ₗ[K] Matrix (Fin n) (Fin n) K,
      B = Finsupp.linearCombination K (⇑N) := ⟨_, rfl⟩

  have hprod : ∀ (f : Γ →₀ K) (h : Γ),
      Matrix.trace (B f * N h) = Matrix.trace (A f * M h) := by
    intro f h
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp [add_mul, hf, hg]
    | single g a =>
      subst hA hB
      simp only [Finsupp.linearCombination_single, smul_mul_assoc, Matrix.trace_smul,
        ← map_mul, htr]

  have hker : LinearMap.ker A ≤ LinearMap.ker B := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    apply eq_zero_of_trace_mul
    intro Y
    have hY : Y ∈ Submodule.span K (Set.range (⇑N)) := hN ▸ Submodule.mem_top
    let ℓ : Matrix (Fin n) (Fin n) K →ₗ[K] K :=
      (Matrix.traceLinearMap (Fin n) K K).comp (LinearMap.mulLeft K (B f))
    have hle : Submodule.span K (Set.range (⇑N)) ≤ LinearMap.ker ℓ := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      simp [ℓ, hprod, hf]
    simpa [ℓ] using hle hY

  let φ : LinearMap.range A →ₗ[K] Matrix (Fin n) (Fin n) K :=
    ((LinearMap.ker A).liftQ B hker).comp A.quotKerEquivRange.symm.toLinearMap
  have hφ : ∀ f, φ ⟨A f, LinearMap.mem_range_self A f⟩ = B f := by
    intro f
    simp [φ]
  have hφtop : LinearMap.range φ = ⊤ := by
    rw [eq_top_iff]
    rintro Y -
    have hY : Y ∈ LinearMap.range B := by
      rw [hB, Finsupp.range_linearCombination, hN]
      exact Submodule.mem_top
    obtain ⟨f, rfl⟩ := hY
    exact ⟨_, hφ f⟩
  have h1 := LinearMap.finrank_range_le φ
  rw [hφtop, finrank_top] at h1
  have h2 : LinearMap.range A = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) h1)
  rwa [hA, Finsupp.range_linearCombination] at h2

end GlobalTheory.TraceFormNondegenerate
