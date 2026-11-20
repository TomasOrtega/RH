import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BtOrderIsHopfOrderNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicBoundedPolynomials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDenominatorIntegralPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyPadicBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyBoundedDenominators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeFactorFormGroupBoundedOfTestSupportStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.FinPolysIrr

/- English proof (translation)
Take `⟨-, -, Z, hZ⟩` from `GlobalTheory.LKCx.herm_laws p G w β hβ hR`. Establish `hsim` using `GlobalTheory.LKCx.grp_similitude_herm p G w β y`. Establish `hs0 : (((y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) ≠ 0` using `by exact_mod_cast ((y : G.Cˣ × ℚˣ).2).ne_zero`. Establish `hsig` using `G.sig w`. Use `GlobalTheory.eig_norm_sq_of_similitude G.n (G.gram w) (herm G w β) (toV G w β y : Matrix (Fin G.n) (Fin G.n) ℂ) (G.gram_herm w) Z _ ?_ ?_ hZ hs0 ?_ ?_ μ x hx hμ` and prove the remaining obligations.

Apply the tactic sequence `rcases hsig with h | h <;> omega`. Use `G.n_pos` as an intermediate fact. Apply the tactic sequence `rcases hsig with h | h <;> omega`. Rewrite using `[Complex.ofReal_ratCast]`. Conclude with `hsim`.

Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Take `⟨c, hc⟩` from `hfix`. Conclude with `Or.inr ⟨c, a.1, hc, a.2⟩`. Use `left`.

Establish `h1 : sigPosH (G.gram_herm w) ≠ 1`. Introduce `h1`. Establish `hcard : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} ≤ 1` using `ha.le`. Use `Fintype.card_le_one_iff.1 hcard ⟨w, h1⟩ ⟨v, hv⟩` as an intermediate fact. Conclude with `hw (congrArg Subtype.val this)`.

Break down `hsig with h | h` into its components or cases. Conclude with `absurd h.1 h1`. Conclude with `h.1`.
-/
theorem eig_norm_sq_of_a_one (p : ℕ) [Fact p.Prime] (G : HTGroup p) (ha : G.a = 1) (v : InfinitePlace G.F)
    (hv : sigPosH (G.gram_herm v) = 1) (β : G.Cˣ) (hβ : sh G β = β) (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1)
    (y : grp G β) (a : PosV G v β) (hfix : FixL G v β y a.1) (w : InfinitePlace G.F) (μ : ℂ)
    (x : Fin G.n → ℂ) (hx : x ≠ 0) (hμ : G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) *ᵥ x = μ • x) :
    ‖μ‖ ^ 2 = ((((y : G.Cˣ × ℚˣ).2 : ℚ)) : ℝ) := by
  obtain ⟨-, -, Z, hZ⟩ := GlobalTheory.LKCx.herm_laws p G w β hβ hR
  have hsim := GlobalTheory.LKCx.grp_similitude_herm p G w β y
  have hs0 : (((y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) ≠ 0 := by exact_mod_cast ((y : G.Cˣ × ℚˣ).2).ne_zero
  have hsig := G.sig w
  refine GlobalTheory.eig_norm_sq_of_similitude G.n (G.gram w) (herm G w β) (toV G w β y : Matrix (Fin G.n) (Fin G.n) ℂ)
    (G.gram_herm w) Z _ ?_ ?_ hZ hs0 ?_ ?_ μ x hx hμ
  · rcases hsig with h | h <;> omega
  · have := G.n_pos
    rcases hsig with h | h <;> omega
  · rw [Complex.ofReal_ratCast]; exact hsim
  · by_cases hw : w = v
    · subst hw
      obtain ⟨c, hc⟩ := hfix
      exact Or.inr ⟨c, a.1, hc, a.2⟩
    · left
      have h1 : sigPosH (G.gram_herm w) ≠ 1 := by
        intro h1
        have hcard : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} ≤ 1 := ha.le
        have := Fintype.card_le_one_iff.1 hcard ⟨w, h1⟩ ⟨v, hv⟩
        exact hw (congrArg Subtype.val this)
      rcases hsig with h | h
      · exact absurd h.1 h1
      · exact h.1

/- English proof (translation)
Use `⟨max (√(max S 0)) 1 ^ (G.n ^ 2) * ((G.n ^ 2).choose (G.n ^ 2 / 2) : ℝ), ?_⟩` and prove the remaining obligations. Introduce `y a hfix hS φ k`. Use `set γ : G.C := (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) with hγ`. Establish `hint : IsIntegral G.F γ` using `Algebra.IsIntegral.isIntegral _`. Establish `hdeg : (minpoly G.F γ).natDegree ≤ G.n ^ 2` using `G.rankC ▸ minpoly.natDegree_le γ`.

Establish `hbd : ∀ (w : InfinitePlace G.F) (z : ℂ), (minpoly G.F γ).eval₂ w.embedding z = 0 → ‖z‖ ≤ √(max S 0)`. Introduce `w z hz`. Take `⟨x, hx, hzx⟩` from `GlobalTheory.LKCx.PolyArch.roots_eig_any p G w γ z hz`. Establish `h2` using `eig_norm_sq_of_a_one p G ha v hv β hβ hR y a hfix w z x hx hzx`. Establish `h3 : ‖z‖ ^ 2 ≤ max S 0` using `h2 ▸ le_max_of_le_left hS`.

Simplify using `using Real.abs_le_sqrt h3`. Establish `hroots : ∀ z ∈ ((minpoly G.F γ).map φ).roots, ‖z‖ ≤ √(max S 0)`. Introduce `z hz`. Establish `hr : (minpoly G.F γ).eval₂ φ z = 0`. Use `(Polynomial.mem_roots'.1 hz).2` as an intermediate fact.

Rewrite `this` using `[Polynomial.IsRoot, Polynomial.eval_map]`. Then use the resulting hypothesis. Break down `InfinitePlace.embedding_mk_eq φ with h | h` into its components or cases. Rewrite `hr` using `[← h]`. Conclude with `hbd _ z hr`. Establish `hr' : (minpoly G.F γ).eval₂ (InfinitePlace.mk φ).embedding (starRingEnd ℂ z) = 0`.

Rewrite using `[h]`. Use `congrArg (starRingEnd ℂ) hr` as an intermediate fact. Rewrite `this` using `[map_zero, Polynomial.hom_eval₂]`. Use `this using 2` and compare the differences between its conclusion and the goal. Conclude with `RingHom.ext fun x => rfl`.

Simplify using `using hbd _ _ hr'`. Use `Polynomial.coeff_bdd_of_roots_le φ (minpoly.monic hint) (IsAlgClosed.splits _) hdeg hroots k` as an intermediate fact. Rewrite `this` using `[Polynomial.coeff_map]`. Then use the resulting hypothesis.
-/
theorem minpoly_coeff_bdd_of_a_one (p : ℕ) [Fact p.Prime] (G : HTGroup p) (ha : G.a = 1)
    (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1) (β : G.Cˣ) (hβ : sh G β = β)
    (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) (S : ℝ) : ∃ B : ℝ, ∀ (y : grp G β) (a : PosV G v β),
    FixL G v β y a.1 → (((y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) ≤ S → ∀ (φ : G.F →+* ℂ) (k : ℕ),
    ‖φ ((minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k)‖ ≤ B := by
  refine ⟨max (√(max S 0)) 1 ^ (G.n ^ 2) * ((G.n ^ 2).choose (G.n ^ 2 / 2) : ℝ), ?_⟩
  intro y a hfix hS φ k
  set γ : G.C := (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) with hγ
  have hint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hdeg : (minpoly G.F γ).natDegree ≤ G.n ^ 2 := G.rankC ▸ minpoly.natDegree_le γ
  have hbd : ∀ (w : InfinitePlace G.F) (z : ℂ), (minpoly G.F γ).eval₂ w.embedding z = 0 → ‖z‖ ≤ √(max S 0) := by
    intro w z hz
    obtain ⟨x, hx, hzx⟩ := GlobalTheory.LKCx.PolyArch.roots_eig_any p G w γ z hz
    have h2 := eig_norm_sq_of_a_one p G ha v hv β hβ hR y a hfix w z x hx hzx
    have h3 : ‖z‖ ^ 2 ≤ max S 0 := h2 ▸ le_max_of_le_left hS
    simpa using Real.abs_le_sqrt h3
  have hroots : ∀ z ∈ ((minpoly G.F γ).map φ).roots, ‖z‖ ≤ √(max S 0) := by
    intro z hz
    have hr : (minpoly G.F γ).eval₂ φ z = 0 := by
      have := (Polynomial.mem_roots'.1 hz).2
      rwa [Polynomial.IsRoot, Polynomial.eval_map] at this
    rcases InfinitePlace.embedding_mk_eq φ with h | h
    · rw [← h] at hr; exact hbd _ z hr
    · have hr' : (minpoly G.F γ).eval₂ (InfinitePlace.mk φ).embedding (starRingEnd ℂ z) = 0 := by
        rw [h]
        have := congrArg (starRingEnd ℂ) hr
        rw [map_zero, Polynomial.hom_eval₂] at this
        convert this using 2
        exact RingHom.ext fun x => rfl
      simpa using hbd _ _ hr'
  have := Polynomial.coeff_bdd_of_roots_le φ (minpoly.monic hint) (IsAlgClosed.splits _) hdeg hroots k
  rwa [Polynomial.coeff_map] at this

end GlobalTheory.LKCx.FinPolysIrr

namespace GlobalTheory.LKCx

open GlobalTheory.LKCx.FinPolysIrr in

/- English proof (translation)
Introduce `p _ G ha v hv L f hf K' f' hf' β x t hx hsym hR`. Take `⟨D, hD, hDy⟩` from `GlobalTheory.T.minpoly_bounded_denominators p G L f hf β x t hx`. Take `⟨Bp, hBp⟩` from `GlobalTheory.T.minpoly_padic_bounded p G K' f' hf' β`. Take `⟨m₀, hm₀⟩` from `GlobalTheory.T.bounded_denominator_integral_power G.F p Bp`. Take `⟨S, hS⟩` from `GlobalTheory.T.similitudeFactor_formGroup_bounded_of_test_support p G L f hf K' f' hf' β x t hx`.

Take `⟨B, hB⟩` from `minpoly_coeff_bdd_of_a_one p G ha v hv β hsym hR S`. Establish `hpD : 0 < p ^ m₀ * D` using `Nat.mul_pos (pow_pos (Fact.out : p.Prime).pos _) hD`. Use `(GlobalTheory.T.finite_monic_bounded_polynomials G.F (G.n ^ 2) (p ^ m₀ * D) B hpD).subset ?_` and prove the remaining obligations. Introduce and unpack `P ⟨y, a, rfl, hfix, hne⟩`. Establish `h1 : f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) ≠ 0` using `left_ne_zero_of_mul hne`.

Establish `h2 : f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0` using `right_ne_zero_of_mul hne`. Establish `hint : IsIntegral G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)` using `Algebra.IsIntegral.isIntegral _`. Use `⟨minpoly.monic hint, ?_, fun k => ⟨?_, fun φ => hB y a.2 hfix (hS y a.1.1 a.1.2 h1 h2) φ k⟩⟩` and prove the remaining obligations. Rewrite using `[← G.rankC]`. Conclude with `minpoly.natDegree_le _`.

Use `hm₀ _ D (hDy y a.1.1 h1 k) (fun φ => hBp y a.1.2 h2 φ k)` as an intermediate fact. Use `push_cast`. Simplify `this` using `[mul_assoc]`.
-/
theorem finite_minpoly_fix_a_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → Set.Finite {P : Polynomial G.F | ∃ (y : grp G β) (a : Dat G v β), P = minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0} := by
  intro p _ G ha v hv L f hf K' f' hf' β x t hx hsym hR
  obtain ⟨D, hD, hDy⟩ := GlobalTheory.T.minpoly_bounded_denominators p G L f hf β x t hx
  obtain ⟨Bp, hBp⟩ := GlobalTheory.T.minpoly_padic_bounded p G K' f' hf' β
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.bounded_denominator_integral_power G.F p Bp
  obtain ⟨S, hS⟩ := GlobalTheory.T.similitudeFactor_formGroup_bounded_of_test_support p G L f hf K' f' hf' β x t hx
  obtain ⟨B, hB⟩ := minpoly_coeff_bdd_of_a_one p G ha v hv β hsym hR S
  have hpD : 0 < p ^ m₀ * D := Nat.mul_pos (pow_pos (Fact.out : p.Prime).pos _) hD
  refine (GlobalTheory.T.finite_monic_bounded_polynomials G.F (G.n ^ 2) (p ^ m₀ * D) B hpD).subset ?_
  rintro P ⟨y, a, rfl, hfix, hne⟩
  have h1 : f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) ≠ 0 := left_ne_zero_of_mul hne
  have h2 : f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0 := right_ne_zero_of_mul hne
  have hint : IsIntegral G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := Algebra.IsIntegral.isIntegral _
  refine ⟨minpoly.monic hint, ?_, fun k => ⟨?_, fun φ => hB y a.2 hfix (hS y a.1.1 a.1.2 h1 h2) φ k⟩⟩
  · rw [← G.rankC]; exact minpoly.natDegree_le _
  · have := hm₀ _ D (hDy y a.1.1 h1 k) (fun φ => hBp y a.1.2 h2 φ k)
    push_cast
    simpa [mul_assoc] using this

/- English proof (translation)
The claim follows from `finite_minpoly_fix_a_one`.
-/
example : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → Set.Finite {P : Polynomial G.F | ∃ (y : grp G β) (a : Dat G v β), P = minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0} :=
  finite_minpoly_fix_a_one

end GlobalTheory.LKCx
