import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicMulEqZeroIffStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientIntegralHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOverStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSomeLevelOverOfIntegralInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableOfHasSomeLevelOverStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrictStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN.Sat

/- English proof (translation)
Establish `hg : 0 < ((γ : GL (Fin 2) ℝ)).det.val` using `by simp`. Conclude with `hf.comp (UpperHalfPlane.mdifferentiable_smul hg)`.
-/
theorem mdiff_comp_sl (f : ℍ → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (γ : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => f (γ • τ)) := by
  have hg : 0 < ((γ : GL (Fin 2) ℝ)).det.val := by simp
  exact hf.comp (UpperHalfPlane.mdifferentiable_smul hg)

/- English proof (translation)
Introduce `γ hγ`. Establish `c : ∀ x y : ℤ, ((x : ZMod L) = y) → ((x : ZMod K) = y)` using `fun x y h => by`. Use `congrArg (ZMod.castHom hd (ZMod K)) h` as an intermediate fact. Simplify using `using this`. Rewrite `hγ`, the goal using `[CongruenceSubgroup.Gamma_mem]`.

Take `⟨h1, h2, h3, h4⟩` from `hγ`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify `h1)` using `using c _ 1 (by simpa`. Simplify `h2)` using `using c _ 0 (by simpa`. Simplify `h3)` using `using c _ 0 (by simpa`.

Simplify `h4)` using `using c _ 1 (by simpa`.
-/
theorem gamma_le {K L : ℕ} (hd : K ∣ L) : CongruenceSubgroup.Gamma L ≤ CongruenceSubgroup.Gamma K := by
  intro γ hγ
  have c : ∀ x y : ℤ, ((x : ZMod L) = y) → ((x : ZMod K) = y) := fun x y h => by
    have := congrArg (ZMod.castHom hd (ZMod K)) h
    simpa using this
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using c _ 1 (by simpa using h1)
  · simpa using c _ 0 (by simpa using h2)
  · simpa using c _ 0 (by simpa using h3)
  · simpa using c _ 1 (by simpa using h4)

/- English proof (translation)
Rewrite `h` using `[Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range]`. Establish `key : ∀ j : Fin (m + 1), (P j * P (m + 1) ^ (m - j)) * (P (m + 1) * x) ^ (j : ℕ) * y ^ (m + 1 - j) = P (m + 1) ^ m * (P j * x ^ (j : ℕ) * y ^ (m + 1 - j))`. Introduce `j`. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp j.isLt)`. Establish `e1 : m - j = k` using `by omega`.

Establish `e2 : P (m + 1) ^ m = P (m + 1) ^ k * P (m + 1) ^ (j : ℕ)` using `by rw [← pow_add]; congr 1; omega`. Rewrite using `[e1, e2, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum]`. Establish `: (P (m + 1) * x) ^ (m + 1) = P (m + 1) ^ m * (P (m + 1) * x ^ (m + 1) * y ^ (m + 1 - (m + 1)))`.

Simplify using `only [Nat.sub_self, pow_zero, mul_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Take the linear combination `(P (m + 1) ^ m) * h`.
-/
theorem alg (m : ℕ) (P : ℕ → ℂ) (x y : ℂ)
    (h : ∑ i ∈ Finset.range (m + 1 + 1), P i * x ^ i * y ^ (m + 1 - i) = 0) :
    (P (m + 1) * x) ^ (m + 1) +
      ∑ j : Fin (m + 1), (P j * P (m + 1) ^ (m - j)) * (P (m + 1) * x) ^ (j : ℕ) * y ^ (m + 1 - j) = 0 := by
  rw [Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range] at h
  have key : ∀ j : Fin (m + 1), (P j * P (m + 1) ^ (m - j)) * (P (m + 1) * x) ^ (j : ℕ) * y ^ (m + 1 - j) =
      P (m + 1) ^ m * (P j * x ^ (j : ℕ) * y ^ (m + 1 - j)) := by
    intro j
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp j.isLt)
    have e1 : m - j = k := by omega
    have e2 : P (m + 1) ^ m = P (m + 1) ^ k * P (m + 1) ^ (j : ℕ) := by rw [← pow_add]; congr 1; omega
    rw [e1, e2, mul_pow]; ring
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum]
  have : (P (m + 1) * x) ^ (m + 1) = P (m + 1) ^ m * (P (m + 1) * x ^ (m + 1) * y ^ (m + 1 - (m + 1))) := by
    simp only [Nat.sub_self, pow_zero, mul_one]; ring
  rw [this]
  linear_combination (P (m + 1) ^ m) * h

/- English proof (translation)
Introduce `Ω _ _ ε M n a b p hM ha hb hb0 hab hp hpn heq`. Take `⟨-, hiff, -, -, hmem⟩` from `GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict`. Establish `hring` using `GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range`. Establish `inR_mul : ∀ f g : ℍ → ℂ, InR ε.range f → InR ε.range g → InR ε.range (f * g)` using `fun f g hf hg => (hring.1 _).1 (Subring.mul_mem _ ((hring.1 _).2 hf) ((hring.1 _).2 hg))`. Establish `inR_pow : ∀ (f : ℍ → ℂ) (k : ℕ), InR ε.range f → InR ε.range (f ^ k)` using `fun f k hf => (hring.1 _).1 (Subring.pow_mem _ ((hring.1 _).2 hf) k)`.

Establish `hol : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (p i)` using `fun i => GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ (hp i)`. Choose the witnesses or unpack the hypotheses as in `⟨m, rfl⟩ : ∃ m, n = m + 1 := by`. Break down `n with _ | m` into its components or cases. It suffices to derive a contradiction. Apply `hpn` to reduce the goal to its premises.

Use function extensionality and compare the values at `τ`. Use `heq τ` as an intermediate fact. Simplify using `using this`. Conclude with `⟨m, rfl⟩`. Establish `hHs : IsOpen Hs` using `by show IsOpen {z : ℂ | 0 < z.im}; exact isOpen_lt continuous_const Complex.continuous_im`.

Establish `hHc : IsPreconnected Hs`. Apply `Convex.isPreconnected` to reduce the goal to its premises. Use `show Convex ℝ {z : ℂ | 0 < z.im}`. Introduce `x hx y hy s t hs ht hst`. Simplify using `only [Set.mem_setOf_eq, Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hx hy ⊢`.

Break down `hs.eq_or_lt with rfl | hs'` into its components or cases. Simplify using `at hst`. Substitute `hst` using the available equality. Simplify using `using hy`. Use polynomial arithmetic with `[mul_pos hs' hx, mul_nonneg ht hy.le]`.

Establish `dOn : ∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → DifferentiableOn ℂ (up f) Hs` using `fun f hf => (hiff f).1 hf`. Establish `upc : ∀ (f : ℍ → ℂ) (τ : ℍ), up f (τ : ℂ) = f τ` using `fun f τ => by`. Simplify using `only [up, UpperHalfPlane.ofComplex_apply]`. Choose the witnesses or unpack the hypotheses as in `⟨τ0, hτ0⟩ : ∃ τ, b τ ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hb0 (funext hc)`. Take `⟨h', hh'd, hAD, hmon⟩` from `GlobalTheory.T.exists_differentiableOn_quotient_of_integral Hs (m + 1) (fun z => up (p (m + 1)) z * up a z) (up b) (fun j z => up (p j) z * up (p (m + 1)) z ^ (m - j)) hHs hHc ((dOn _ (hol _)).mul (dOn _ ha)) (dOn _ hb) (fun j => (dOn _ (hol _)).mul ((dOn _ (hol _)).pow _)) ⟨τ0, …`. Use `set h : ℍ → ℂ := fun τ => h' τ with hh`. Establish `hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h`.

Rewrite using `[hiff]`. Use `hh'd.congr fun z hz => ?_` and prove the remaining obligations. Use `show h' (UpperHalfPlane.ofComplex z : ℂ) = h' z`. Rewrite using `[UpperHalfPlane.ofComplex_apply_of_im_pos hz]`. Establish `hPA : ∀ τ, p (m + 1) τ * a τ = h τ * b τ` using `fun τ => by`.

Use `hAD τ (hmem τ)` as an intermediate fact. Simplify `this` using `only [upc]`. Take `⟨N, w, hN, hLv, -⟩` from `hp (m + 1)`. Establish `hinv : ∀ γ ∈ CongruenceSubgroup.Gamma (M * N), ∀ τ : ℍ, h (γ • τ) = h τ`. Introduce `γ hγ`.

Establish `hγM` using `gamma_le (Dvd.intro N rfl) hγ`. Establish `hγN` using `gamma_le (Dvd.intro_left M rfl) hγ`. Establish `hprod : ∀ τ, (fun τ => h (γ • τ) - h τ) τ * (fun τ => b τ * b (γ • τ)) τ = 0`. Introduce `τ`. Establish `E1` using `hPA (γ • τ)`.

Establish `E2` using `hPA τ`. Establish `E3` using `hLv γ hγN τ`. Establish `E4` using `hab γ hγM τ`. Simplify using `only`. Take the linear combination `(-(b τ)) * E1 + b (γ • τ) * E2 + (a (γ • τ) * b τ) * E3 + p (m + 1) τ * E4`.

Break down `GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff _ _ ((mdiff_comp_sl h hhol γ).sub hhol) (hb.mul (mdiff_comp_sl b hb γ)) hprod with h0 | h0` into its components or cases. Introduce `τ`. Use `congrFun h0 τ` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`. It suffices to derive a contradiction.

Establish `hbb : ∀ τ, b τ * (fun τ => b (γ • τ)) τ = 0` using `fun τ => congrFun h0 τ`. Break down `GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff _ _ hb (mdiff_comp_sl b hb γ) hbb with h1 | h1` into its components or cases. Conclude with `hb0 h1`. Apply `hτ0` to reduce the goal to its premises. Use `congrFun h1 (γ⁻¹ • τ0)` as an intermediate fact.

Simplify using `using this`. Use `⟨h, ?_, hPA⟩` and prove the remaining obligations. Use `GlobalTheory.T.hasSomeLevelOver_of_integral_invariant Ω ε (M * N) (m + 1) h (fun j τ => p j τ * p (m + 1) τ ^ (m - j)) (Nat.mul_pos hM hN) hhol hinv (fun j => inR_mul _ _ (hp _) (inR_pow _ _ (hp _))) ?_` and prove the remaining obligations. Introduce `τ`. Use `hmon τ (hmem τ)` as an intermediate fact.

Simplify `this` using `only [upc]`.
-/
theorem sat : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (M n : ℕ) (a b : ℍ → ℂ) (p : ℕ → ℍ → ℂ), 0 < M → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b → b ≠ 0 → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, a (γ • τ) * b τ = a τ * b (γ • τ)) → (∀ i, InR ε.range (p i)) → p n ≠ 0 → (∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * a τ ^ i * b τ ^ (n - i) = 0) → ∃ h : ℍ → ℂ, InR ε.range h ∧ ∀ τ, p n τ * a τ = h τ * b τ := by
  intro Ω _ _ ε M n a b p hM ha hb hb0 hab hp hpn heq
  obtain ⟨-, hiff, -, -, hmem⟩ := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  have hring := GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range
  have inR_mul : ∀ f g : ℍ → ℂ, InR ε.range f → InR ε.range g → InR ε.range (f * g) := fun f g hf hg =>
    (hring.1 _).1 (Subring.mul_mem _ ((hring.1 _).2 hf) ((hring.1 _).2 hg))
  have inR_pow : ∀ (f : ℍ → ℂ) (k : ℕ), InR ε.range f → InR ε.range (f ^ k) := fun f k hf =>
    (hring.1 _).1 (Subring.pow_mem _ ((hring.1 _).2 hf) k)
  have hol : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (p i) := fun i => GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ (hp i)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases n with _ | m
    · exfalso; apply hpn; funext τ; have := heq τ; simpa using this
    · exact ⟨m, rfl⟩
  have hHs : IsOpen Hs := by
    show IsOpen {z : ℂ | 0 < z.im}; exact isOpen_lt continuous_const Complex.continuous_im
  have hHc : IsPreconnected Hs := by
    apply Convex.isPreconnected
    show Convex ℝ {z : ℂ | 0 < z.im}
    intro x hx y hy s t hs ht hst
    simp only [Set.mem_setOf_eq, Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] at hx hy ⊢
    rcases hs.eq_or_lt with rfl | hs'
    · simp at hst; subst hst; simpa using hy
    · nlinarith [mul_pos hs' hx, mul_nonneg ht hy.le]
  have dOn : ∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → DifferentiableOn ℂ (up f) Hs := fun f hf => (hiff f).1 hf
  have upc : ∀ (f : ℍ → ℂ) (τ : ℍ), up f (τ : ℂ) = f τ := fun f τ => by
    simp only [up, UpperHalfPlane.ofComplex_apply]
  obtain ⟨τ0, hτ0⟩ : ∃ τ, b τ ≠ 0 := by
    by_contra hc; push_neg at hc; exact hb0 (funext hc)
  obtain ⟨h', hh'd, hAD, hmon⟩ := GlobalTheory.T.exists_differentiableOn_quotient_of_integral Hs (m + 1) (fun z => up (p (m + 1)) z * up a z) (up b)
    (fun j z => up (p j) z * up (p (m + 1)) z ^ (m - j)) hHs hHc
    ((dOn _ (hol _)).mul (dOn _ ha)) (dOn _ hb) (fun j => (dOn _ (hol _)).mul ((dOn _ (hol _)).pow _))
    ⟨τ0, hmem τ0, by rw [upc]; exact hτ0⟩
    (fun z _ => alg m (fun i => p i (UpperHalfPlane.ofComplex z)) (a (UpperHalfPlane.ofComplex z))
      (b (UpperHalfPlane.ofComplex z)) (heq _))
  set h : ℍ → ℂ := fun τ => h' τ with hh
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
    rw [hiff]
    refine hh'd.congr fun z hz => ?_
    show h' (UpperHalfPlane.ofComplex z : ℂ) = h' z
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hPA : ∀ τ, p (m + 1) τ * a τ = h τ * b τ := fun τ => by
    have := hAD τ (hmem τ); simpa only [upc] using this
  obtain ⟨N, w, hN, hLv, -⟩ := hp (m + 1)
  have hinv : ∀ γ ∈ CongruenceSubgroup.Gamma (M * N), ∀ τ : ℍ, h (γ • τ) = h τ := by
    intro γ hγ
    have hγM := gamma_le (Dvd.intro N rfl) hγ
    have hγN := gamma_le (Dvd.intro_left M rfl) hγ
    have hprod : ∀ τ, (fun τ => h (γ • τ) - h τ) τ * (fun τ => b τ * b (γ • τ)) τ = 0 := by
      intro τ
      have E1 := hPA (γ • τ)
      have E2 := hPA τ
      have E3 := hLv γ hγN τ
      have E4 := hab γ hγM τ
      simp only
      linear_combination (-(b τ)) * E1 + b (γ • τ) * E2 + (a (γ • τ) * b τ) * E3 + p (m + 1) τ * E4
    rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff _ _ ((mdiff_comp_sl h hhol γ).sub hhol) (hb.mul (mdiff_comp_sl b hb γ)) hprod with h0 | h0
    · intro τ; have := congrFun h0 τ; simpa [sub_eq_zero] using this
    · exfalso
      have hbb : ∀ τ, b τ * (fun τ => b (γ • τ)) τ = 0 := fun τ => congrFun h0 τ
      rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff _ _ hb (mdiff_comp_sl b hb γ) hbb with h1 | h1
      · exact hb0 h1
      · apply hτ0
        have := congrFun h1 (γ⁻¹ • τ0)
        simpa using this
  refine ⟨h, ?_, hPA⟩
  refine GlobalTheory.T.hasSomeLevelOver_of_integral_invariant Ω ε (M * N) (m + 1) h (fun j τ => p j τ * p (m + 1) τ ^ (m - j)) (Nat.mul_pos hM hN)
    hhol hinv (fun j => inR_mul _ _ (hp _) (inR_pow _ _ (hp _))) ?_
  intro τ
  have := hmon τ (hmem τ)
  simpa only [upc] using this

end GlobalTheory.FN.Sat
