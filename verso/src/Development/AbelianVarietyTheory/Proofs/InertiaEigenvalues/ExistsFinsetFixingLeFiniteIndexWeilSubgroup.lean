import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilOpenFin

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h h1 h2 h3 H hH hopen`. Establish `hfix : ∀ (g : G E Ω) (t : Finset Ω), (∀ x ∈ t, g x = x) → ∀ n : ℤ, ∀ x ∈ t, (g ^ n) x = x`. Introduce `g t hg n x hx`. Establish `hm : g ∈ MulAction.stabilizer (G E Ω) x`. Rewrite using `[MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]`.

Conclude with `hg x hx`. Use `(MulAction.mem_stabilizer_iff).mp (Subgroup.zpow_mem _ hm n)` as an intermediate fact. Rewrite `this` using `[AlgEquiv.smul_def]`. Then use the resulting hypothesis. Take `⟨s₁, hs₁⟩` from `h3 (H.comap (ineIncl h)) hopen`. Set `φ : Weil h` to `frob h`.

Take `⟨m, hm0, hm⟩` from `h1 (φ : G E Ω) s₁`. Establish `hN : H.normalCore.index ≠ 0` using `Subgroup.FiniteIndex.index_ne_zero`. Use `set k : ℕ := m * H.normalCore.index with hk`. Establish `hk0 : 0 < k` using `Nat.mul_pos hm0 (Nat.pos_of_ne_zero hN)`. Set `ψ : Weil h` to `φ ^ k`.

Establish `hψH : ψ ∈ H`. Apply `Subgroup.normalCore_le` to reduce the goal to its premises. Use `show φ ^ (m * H.normalCore.index) ∈ H.normalCore`. Rewrite using `[pow_mul]`. Conclude with `Subgroup.pow_index_mem _ _`.

Establish `hψdeg : deg ψ = k` using `by simp [ψ, φ]`. Establish `hψfix : ∀ x ∈ s₁, (ψ : G E Ω) x = x`. Introduce `x hx`. Use `hfix _ s₁ hm (H.normalCore.index : ℤ) x hx` as an intermediate fact. Simplify `this` using `[ψ, φ, hk, pow_mul]`.

Take `⟨ζ, hζ⟩` from `h2 k hk0`. Use `⟨insert ζ s₁, fun τ hτ => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `hζ τ (hτ ζ (Finset.mem_insert_self _ _))`. Set `ρ : Weil h` to `τ * ψ ^ (-i)`. Establish `hρdeg : deg ρ = 0`.

Simplify using `only [ρ, deg_mul, deg_zpow, hψdeg, hi]`. Expand and normalize the polynomial expressions, which then agree. Establish `hρIne : (ρ : G E Ω) ∈ Ine (F` using `E) A := deg_eq_zero_iff.mp hρdeg`. Establish `hρfix : ∀ x ∈ s₁, (ρ : G E Ω) x = x`. Introduce `x hx`.

Establish `e1` using `hfix _ s₁ hψfix (-i) x hx`. Use `show ((τ : G E Ω) * ((ψ ^ (-i) : Weil h) : G E Ω)) x = x`. Rewrite using `[AlgEquiv.mul_apply, Subgroup.coe_zpow, e1]`. Conclude with `hτ x (Finset.mem_insert_of_mem hx)`. Establish `hρM` using `hs₁ ⟨ρ, hρIne⟩ hρfix`.

Establish `hρH : ρ ∈ H`. Establish `: ineIncl h ⟨ρ, hρIne⟩ ∈ H` using `hρM`. Conclude with `this`. Establish `: τ = ρ * ψ ^ i` using `by simp [ρ]`. Rewrite using `[this]`.

Conclude with `H.mul_mem hρH (H.zpow_mem hψH i)`.
-/
theorem exists_finset_fix_le : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ (σ : G E Ω) (s : Finset Ω), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ s, (σ ^ m) x = x) → (∀ k : ℕ, 0 < k → ∃ ζ : Ω, ∀ σ : Weil h, (σ : G E Ω) ζ = ζ → (k : ℤ) ∣ deg σ) → (∀ M : Subgroup (Ine (F := E) A), IsOpen (M : Set (Ine (F := E) A)) → ∃ s : Finset Ω, ∀ σ : Ine (F := E) A, (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ M) → ∀ H : Subgroup (Weil h), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∃ s : Finset Ω, ∀ σ : Weil h, (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ H := by
  intro E Ω _ _ _ _ _ A w h h1 h2 h3 H hH hopen
  classical

  have hfix : ∀ (g : G E Ω) (t : Finset Ω), (∀ x ∈ t, g x = x) → ∀ n : ℤ, ∀ x ∈ t, (g ^ n) x = x := by
    intro g t hg n x hx
    have hm : g ∈ MulAction.stabilizer (G E Ω) x := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]; exact hg x hx
    have := (MulAction.mem_stabilizer_iff).mp (Subgroup.zpow_mem _ hm n)
    rwa [AlgEquiv.smul_def] at this
  obtain ⟨s₁, hs₁⟩ := h3 (H.comap (ineIncl h)) hopen
  let φ : Weil h := frob h
  obtain ⟨m, hm0, hm⟩ := h1 (φ : G E Ω) s₁
  have hN : H.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  set k : ℕ := m * H.normalCore.index with hk
  have hk0 : 0 < k := Nat.mul_pos hm0 (Nat.pos_of_ne_zero hN)
  let ψ : Weil h := φ ^ k
  have hψH : ψ ∈ H := by
    apply Subgroup.normalCore_le
    show φ ^ (m * H.normalCore.index) ∈ H.normalCore
    rw [pow_mul]; exact Subgroup.pow_index_mem _ _
  have hψdeg : deg ψ = k := by simp [ψ, φ]
  have hψfix : ∀ x ∈ s₁, (ψ : G E Ω) x = x := by
    intro x hx
    have := hfix _ s₁ hm (H.normalCore.index : ℤ) x hx
    simpa [ψ, φ, hk, pow_mul] using this
  obtain ⟨ζ, hζ⟩ := h2 k hk0
  refine ⟨insert ζ s₁, fun τ hτ => ?_⟩
  obtain ⟨i, hi⟩ := hζ τ (hτ ζ (Finset.mem_insert_self _ _))
  let ρ : Weil h := τ * ψ ^ (-i)
  have hρdeg : deg ρ = 0 := by
    simp only [ρ, deg_mul, deg_zpow, hψdeg, hi]; ring
  have hρIne : (ρ : G E Ω) ∈ Ine (F := E) A := deg_eq_zero_iff.mp hρdeg
  have hρfix : ∀ x ∈ s₁, (ρ : G E Ω) x = x := by
    intro x hx
    have e1 := hfix _ s₁ hψfix (-i) x hx
    show ((τ : G E Ω) * ((ψ ^ (-i) : Weil h) : G E Ω)) x = x
    rw [AlgEquiv.mul_apply, Subgroup.coe_zpow, e1]
    exact hτ x (Finset.mem_insert_of_mem hx)
  have hρM := hs₁ ⟨ρ, hρIne⟩ hρfix
  have hρH : ρ ∈ H := by
    have : ineIncl h ⟨ρ, hρIne⟩ ∈ H := hρM
    exact this
  have : τ = ρ * ψ ^ i := by simp [ρ]
  rw [this]
  exact H.mul_mem hρH (H.zpow_mem hψH i)

end GlobalTheory.WeilOpenFin
