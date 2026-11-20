import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.R0MemNfSpanOfHatHypStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormProductSpanLeftMulClosedStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinusHatsTaylorCoeffLeibnizRuleStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PlusHatsTaylorCoeffLeibnizRuleStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.VecPolyMemSpanValuesStatement

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

/- English proof (translation)
Take `⟨C, hC⟩` from `(Set.toFinite ((fun x : M.Ty P × ℕ => -M.rho P x.1 x.2) '' ((Finset.univ ×ˢ Finset.Icc 1 (P.k - 1) : Finset (M.Ty P × ℕ)) : Set (M.Ty P × ℕ)))).bddAbove`. Use `⟨C + 1, fun t ht ρ => ?_⟩` and prove the remaining obligations. Unfold `M.xC`. Use `Finset.prod_ne_zero_iff.2 fun i hi => ?_` and prove the remaining obligations. Establish `h1 : -M.rho P ρ i ≤ C` using `hC ⟨(ρ, i), Finset.mem_coe.2 (Finset.mem_product.2 ⟨Finset.mem_univ _, hi⟩), rfl⟩`.

Establish `h2 : t + M.rho P ρ i ≠ 0` using `(show 0 < t + M.rho P ρ i by linarith).ne'`. Conclude with `h2` after adjusting the coercions.
-/
theorem hatExp_exists_bound (P : M.Par) :
    ∃ C : ℝ, ∀ t : ℝ, C ≤ t → ∀ ρ : M.Ty P, M.xC P ρ (t : ℂ) ≠ 0 := by
  obtain ⟨C, hC⟩ := (Set.toFinite
    ((fun x : M.Ty P × ℕ => -M.rho P x.1 x.2) ''
      ((Finset.univ ×ˢ Finset.Icc 1 (P.k - 1) : Finset (M.Ty P × ℕ)) : Set (M.Ty P × ℕ)))).bddAbove
  refine ⟨C + 1, fun t ht ρ => ?_⟩
  unfold M.xC
  refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
  have h1 : -M.rho P ρ i ≤ C :=
    hC ⟨(ρ, i), Finset.mem_coe.2 (Finset.mem_product.2 ⟨Finset.mem_univ _, hi⟩), rfl⟩
  have h2 : t + M.rho P ρ i ≠ 0 := (show 0 < t + M.rho P ρ i by linarith).ne'
  exact_mod_cast h2

/- English proof (translation)
Take `⟨C, hC⟩` from `hatExp_exists_bound P`. Use `⟨fun i => C + 1 + (i : ℕ), fun i j h => ?_, fun i ρ => ?_⟩` and prove the remaining obligations. Establish `h' : ((i : ℕ) : ℝ) = (j : ℕ)` using `by simpa using h`. Conclude with `Fin.ext (by exact_mod_cast h')`. Establish `h0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ)` using `Nat.cast_nonneg _`.

Use `⟨hC _ (by linarith) ρ, ?_, ?_⟩` and prove the remaining obligations. Use `hC (C + 1 + (i : ℕ) - 1) (by linarith) ρ` as an intermediate fact. Rewrite `this` using `[Complex.ofReal_sub, Complex.ofReal_one]`. Then use the resulting hypothesis. Use `hC (C + 1 + (i : ℕ) + 1) (by linarith) ρ` as an intermediate fact. Rewrite `this` using `[Complex.ofReal_add _ 1, Complex.ofReal_one]`. Then use the resulting hypothesis.
-/
theorem hatExp_exists_nodes (P : M.Par) (n : ℕ) :
    ∃ y : Fin n → ℝ, Function.Injective y ∧ ∀ i, ∀ ρ : M.Ty P,
      M.xC P ρ (y i : ℂ) ≠ 0 ∧ M.xC P ρ ((y i : ℂ) - 1) ≠ 0 ∧ M.xC P ρ ((y i : ℂ) + 1) ≠ 0 := by
  obtain ⟨C, hC⟩ := hatExp_exists_bound P
  refine ⟨fun i => C + 1 + (i : ℕ), fun i j h => ?_, fun i ρ => ?_⟩
  · have h' : ((i : ℕ) : ℝ) = (j : ℕ) := by simpa using h
    exact Fin.ext (by exact_mod_cast h')
  · have h0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    refine ⟨hC _ (by linarith) ρ, ?_, ?_⟩
    · have := hC (C + 1 + (i : ℕ) - 1) (by linarith) ρ
      rwa [Complex.ofReal_sub, Complex.ofReal_one] at this
    · have := hC (C + 1 + (i : ℕ) + 1) (by linarith) ρ
      rwa [Complex.ofReal_add _ 1, Complex.ofReal_one] at this

/- English proof (translation)
Introduce `P A _ _ _ _ d hd T a hT`. Establish `hle : nfSpan d (basics d) 0 0 1 ≤ nfSpan d T 0 a 1`. Unfold `nfSpan`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨b, hb, H, hH, hHT, rfl⟩`.

Take `⟨h, rfl⟩` from `List.length_eq_one_iff.1 hH`. Establish `h1` using `((GlobalTheory.T.normalFormProductSpan_left_mul_closed P A d hd T).1 0 a 1 h (hT h (hHT h (List.mem_singleton_self h)))).1 b hb`. Simplify `h1` using `[nfSpan]`. Take `⟨y, hy, hreg⟩` from `hatExp_exists_nodes P (P.r + 2)`. Establish `hyc : Function.Injective fun i => (y i : ℂ)` using `fun i j h => hy (Complex.ofReal_injective h)`.

Establish `hyn : Function.Injective fun i => -(y i : ℂ)` using `fun i j h => hyc (neg_injective h)`. Establish `key : ∀ (Z : ℂ → A) (X : ℕ → A) (ν : Fin (P.r + 2) → ℂ), Function.Injective ν → (∀ s : ℂ, Z s = ∑ j ∈ Finset.range (P.r + 2), s ^ j • X j) → (∀ i, Z (ν i) ∈ nfSpan d T 0 a 1) → ∀ s, Z s ∈ nfSpan d T 0 a 1`. Introduce `Z X ν hν hZ hi s`. Use `(Submodule.span_le.2 ?_) ((GlobalTheory.T.mem_span_values_of_vector_polynomial A (P.r + 2) Z X ν hν hZ).2 s)` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `hi i`. Take `⟨Xa, Xr, hXa, hXr, -⟩` from `GlobalTheory.T.plusHats_taylorCoeff_leibniz_rule A P.r d.L 0`. Take `⟨Va, Vr, hVa, hVr, -⟩` from `GlobalTheory.T.minusHats_taylorCoeff_leibniz_rule A P.r d.L 0`. Introduce and unpack `X (((⟨s, rfl⟩ | ⟨s, rfl⟩) | ⟨s, rfl⟩) | ⟨s, rfl⟩)`. Use `key (fun s => d.L.Ahat (0 + s)) Xa _ hyc hXa (fun i => by simpa using hT _ ⟨y i, hreg i, Or.inl rfl⟩) s` as an intermediate fact.

Simplify using `using this`. Use `key (fun s => d.L.R0 (0 + s)) Xr _ hyc hXr (fun i => by simpa using hle (GlobalTheory.T.R0_and_R0v_mem_nfSpan_basics_of_xC_ne_zero P A d hd (y i) (hreg i)).1) s` as an intermediate fact. Simplify using `using this`. Use `key (fun s => d.L.Ahatv (0 - s)) Va _ hyn hVa (fun i => by simpa using hT _ ⟨y i, hreg i, Or.inr (Or.inl rfl)⟩) (-s)` as an intermediate fact. Simplify using `using this`.

Use `key (fun s => d.L.R0v (0 - s)) Vr _ hyn hVr (fun i => by simpa using hle (GlobalTheory.T.R0_and_R0v_mem_nfSpan_basics_of_xC_ne_zero P A d hd (y i) (hreg i)).2) (-s)` as an intermediate fact. Simplify using `using this`.
-/
theorem hats_mem_nfSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (T : Set A) (a : ℕ), (∀ x ∈ basics d, x ∈ nfSpan d T 0 a 1) → ∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1 := by
  intro P A _ _ _ _ d hd T a hT
  have hle : nfSpan d (basics d) 0 0 1 ≤ nfSpan d T 0 a 1 := by
    unfold nfSpan
    refine Submodule.span_le.2 ?_
    rintro x ⟨b, hb, H, hH, hHT, rfl⟩
    obtain ⟨h, rfl⟩ := List.length_eq_one_iff.1 hH
    have h1 := ((GlobalTheory.T.normalFormProductSpan_left_mul_closed P A d hd T).1 0 a 1 h (hT h (hHT h (List.mem_singleton_self h)))).1 b hb
    simpa [nfSpan] using h1
  obtain ⟨y, hy, hreg⟩ := hatExp_exists_nodes P (P.r + 2)
  have hyc : Function.Injective fun i => (y i : ℂ) := fun i j h => hy (Complex.ofReal_injective h)
  have hyn : Function.Injective fun i => -(y i : ℂ) := fun i j h => hyc (neg_injective h)
  have key : ∀ (Z : ℂ → A) (X : ℕ → A) (ν : Fin (P.r + 2) → ℂ), Function.Injective ν →
      (∀ s : ℂ, Z s = ∑ j ∈ Finset.range (P.r + 2), s ^ j • X j) →
      (∀ i, Z (ν i) ∈ nfSpan d T 0 a 1) → ∀ s, Z s ∈ nfSpan d T 0 a 1 := by
    intro Z X ν hν hZ hi s
    refine (Submodule.span_le.2 ?_) ((GlobalTheory.T.mem_span_values_of_vector_polynomial A (P.r + 2) Z X ν hν hZ).2 s)
    rintro _ ⟨i, rfl⟩
    exact hi i
  obtain ⟨Xa, Xr, hXa, hXr, -⟩ := GlobalTheory.T.plusHats_taylorCoeff_leibniz_rule A P.r d.L 0
  obtain ⟨Va, Vr, hVa, hVr, -⟩ := GlobalTheory.T.minusHats_taylorCoeff_leibniz_rule A P.r d.L 0
  rintro X (((⟨s, rfl⟩ | ⟨s, rfl⟩) | ⟨s, rfl⟩) | ⟨s, rfl⟩)
  · have := key (fun s => d.L.Ahat (0 + s)) Xa _ hyc hXa
      (fun i => by simpa using hT _ ⟨y i, hreg i, Or.inl rfl⟩) s
    simpa using this
  · have := key (fun s => d.L.R0 (0 + s)) Xr _ hyc hXr
      (fun i => by simpa using hle (GlobalTheory.T.R0_and_R0v_mem_nfSpan_basics_of_xC_ne_zero P A d hd (y i) (hreg i)).1) s
    simpa using this
  · have := key (fun s => d.L.Ahatv (0 - s)) Va _ hyn hVa
      (fun i => by simpa using hT _ ⟨y i, hreg i, Or.inr (Or.inl rfl)⟩) (-s)
    simpa using this
  · have := key (fun s => d.L.R0v (0 - s)) Vr _ hyn hVr
      (fun i => by simpa using hle (GlobalTheory.T.R0_and_R0v_mem_nfSpan_basics_of_xC_ne_zero P A d hd (y i) (hreg i)).2) (-s)
    simpa using this

end GlobalTheory.HatNF
