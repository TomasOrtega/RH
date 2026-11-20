import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffBoundedTaylorEllipticOfPolesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmLatticeHeisenbergRelationsOneVariableStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallTorsionKilledByPrimePowersStatement

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.ScaledQuot

/- English proof (translation)
Introduce and unpack `⟨u, v, h⟩`. Establish `him` using `congrArg Complex.im h`. Establish `hre` using `congrArg Complex.re h`. Simplify using `[wK] at him hre`. Establish `hv : v = 0`.

Break down `him with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h hd.ne'`. Substitute `hv` using the available equality. Establish `h2 : (2 * u : ℝ) = -1`.

Simplify using `at hre`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : (2 * u : ℤ) = -1` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_inOK_neg_half (d : ℕ) (hd : 0 < d) : ¬ InOK d ((0 : ℂ) - 1 / 2) := by
  rintro ⟨u, v, h⟩
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [wK] at him hre
  have hv : v = 0 := by
    rcases him with h | h
    · exact h
    · exact absurd h hd.ne'
  subst hv
  have h2 : (2 * u : ℝ) = -1 := by
    simp at hre
    linarith
  have h3 : (2 * u : ℤ) = -1 := by exact_mod_cast h2
  omega

/- English proof (translation)
Take `⟨u, v, rfl⟩` from `hl`. Conclude with `⟨s * u, s * v, by push_cast; ring⟩`.
-/
theorem inOK_nat_mul (d s : ℕ) {l : ℂ} (hl : InOK d l) : InOK d ((s : ℂ) * l) := by
  obtain ⟨u, v, rfl⟩ := hl
  exact ⟨s * u, s * v, by push_cast; ring⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨s, 0, by simp⟩`.
-/
theorem inOK_nat (d s : ℕ) : InOK d (s : ℂ) := ⟨s, 0, by simp⟩

/- English proof (translation)
Use `congrFun h z` as an intermediate fact. Rewrite using `[← this]`. Simplify using `[W1, U1, Complex.exp_ne_zero]`.
-/
theorem zero_iff_of_fixed {d : ℕ} {θ : ℂ → ℂ} {x : ℂ} (h : W1 d x θ = θ) (z : ℂ) :
    θ (z + x) = 0 ↔ θ z = 0 := by
  have := congrFun h z
  rw [← this]
  simp [W1, U1, Complex.exp_ne_zero]

/- English proof (translation)
Introduce `d q _ M ω θ hd hd7 hsp hL hch hθ t s hs hsq hst φ`. Take `⟨hdiff, h0, -, hW, hz⟩` from `hθ`. Take `⟨-, -, hUd, -, -, hper, -, -⟩` from `GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd.pos`. Take `⟨-, -, -, -, -, hint, -⟩` from `GlobalTheory.MomOne.okArith d q M.ι hd hd7 hsp`. Take `⟨-, -, -, hsm⟩` from `GlobalTheory.T.smallTorsion_killed_by_prime_powers d q M ω hd hd7 hsp hL hch`.

Establish `hlin : Differentiable ℂ (fun z : ℂ => (s : ℂ) * z)` using `by fun_prop`. Establish `hN : ∀ p, AnalyticAt ℂ (fun z => U1 d t θ ((s : ℂ) * z)) p` using `fun p => ((hUd t θ hdiff).1.comp hlin).analyticAt p`. Establish `hD : ∀ p, AnalyticAt ℂ (fun z => θ ((s : ℂ) * z)) p` using `fun p => (hdiff.comp hlin).analyticAt p`. Establish `han : ∀ p, θ ((s : ℂ) * p) ≠ 0 → AnalyticAt ℂ φ p` using `fun p hp => (hN p).div (hD p) hp`. Establish `hE : Ell M.L φ`.

Use `⟨fun p => (hN p).meromorphicAt.div (hD p).meromorphicAt, ?_⟩` and prove the remaining obligations. Introduce `l hl z`. Establish `hl' : InOK d l` using `(hL l).1 hl`. Establish `hWl` using `hW _ (inOK_nat_mul d s hl')`. Establish `hk : kap1 d ((s : ℂ) * l) t = 1`.

Take `⟨k, hk⟩` from `hint l _ hl' hst`. Establish `e : h1 d ((s : ℂ) * l) t = h1 d l ((s : ℂ) * t)`. Simplify using `only [h1, map_mul, Complex.conj_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[kap1, e, hk]`.

Use `Complex.exp_int_mul_two_pi_mul_I (-k)` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hp` using `hper θ t ((s : ℂ) * l) ((s : ℂ) * z) hWl`. Rewrite `hp` using `[hk, one_mul]`. Use `show U1 d t θ ((s : ℂ) * (z + l)) / θ ((s : ℂ) * (z + l)) = U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z)`. Rewrite using `[mul_add]`. Distinguish the cases in `hz0 : θ ((s : ℂ) * z) = 0`.

Rewrite using `[hz0, (zero_iff_of_fixed hWl _).2 hz0, div_zero, div_zero]`. Establish `hz1 : θ ((s : ℂ) * z + (s : ℂ) * l) ≠ 0` using `fun h => hz0 ((zero_iff_of_fixed hWl _).1 h)`. Rewrite using `[div_eq_div_iff hz1 hz0]`. Conclude with `hp`. Establish `hA0 : AnalyticAt ℂ φ 0` using `han 0 (by rw [mul_zero, h0]; exact one_ne_zero)`.

Establish `hpole : ∀ p r, PrimeTo d q r → ¬ InOK d (r - 1 / 2) → θ ((s : ℂ) * p + r) = 0 → ¬ M.Small p`. Introduce `p r hr hr2 hθ0 hsmall`. Conclude with `hr2 (hsm p s r (inOK_nat d s) (by exact_mod_cast hs.ne') hr (hz _ hθ0) hsmall).2`. Use `⟨hE, hA0, han, hpole, GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles q M _ φ hch hE hA0 ?_⟩` and prove the remaining obligations. Introduce `p hp`.

Establish `hθp : θ ((s : ℂ) * p) = 0`. Assume the negation of the conclusion as `hne`. Conclude with `absurd hp (not_lt.mpr (han p hne).meromorphicOrderAt_nonneg)`. Conclude with `hpole p 0 ⟨1, one_pos, Nat.coprime_one_left q, ⟨0, 0, by simp⟩⟩ (not_inOK_neg_half d hd.pos) (by rw [add_zero]; exact hθp)`.
-/
theorem scaled_quotient_elliptic : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (t : ℂ) (s : ℕ), 0 < s → Nat.Coprime s q → InOK d ((s : ℂ) * t) → let φ : ℂ → ℂ := fun z => U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z); Ell M.L φ ∧ AnalyticAt ℂ φ 0 ∧ (∀ p, θ ((s : ℂ) * p) ≠ 0 → AnalyticAt ℂ φ p) ∧ (∀ p r, PrimeTo d q r → ¬ InOK d (r - 1 / 2) → θ ((s : ℂ) * p + r) = 0 → ¬ M.Small p) ∧ Bdd (hat M.ι (C ω * logS) φ) := by
  intro d q _ M ω θ hd hd7 hsp hL hch hθ t s hs hsq hst φ
  obtain ⟨hdiff, h0, -, hW, hz⟩ := hθ
  obtain ⟨-, -, hUd, -, -, hper, -, -⟩ := GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd.pos
  obtain ⟨-, -, -, -, -, hint, -⟩ := GlobalTheory.MomOne.okArith d q M.ι hd hd7 hsp
  obtain ⟨-, -, -, hsm⟩ := GlobalTheory.T.smallTorsion_killed_by_prime_powers d q M ω hd hd7 hsp hL hch
  have hlin : Differentiable ℂ (fun z : ℂ => (s : ℂ) * z) := by fun_prop
  have hN : ∀ p, AnalyticAt ℂ (fun z => U1 d t θ ((s : ℂ) * z)) p := fun p =>
    ((hUd t θ hdiff).1.comp hlin).analyticAt p
  have hD : ∀ p, AnalyticAt ℂ (fun z => θ ((s : ℂ) * z)) p := fun p =>
    (hdiff.comp hlin).analyticAt p
  have han : ∀ p, θ ((s : ℂ) * p) ≠ 0 → AnalyticAt ℂ φ p := fun p hp =>
    (hN p).div (hD p) hp
  have hE : Ell M.L φ := by
    refine ⟨fun p => (hN p).meromorphicAt.div (hD p).meromorphicAt, ?_⟩
    intro l hl z
    have hl' : InOK d l := (hL l).1 hl
    have hWl := hW _ (inOK_nat_mul d s hl')
    have hk : kap1 d ((s : ℂ) * l) t = 1 := by
      obtain ⟨k, hk⟩ := hint l _ hl' hst
      have e : h1 d ((s : ℂ) * l) t = h1 d l ((s : ℂ) * t) := by
        simp only [h1, map_mul, Complex.conj_natCast]; ring
      rw [kap1, e, hk]
      have := Complex.exp_int_mul_two_pi_mul_I (-k)
      rw [← this]
      congr 1
      push_cast; ring
    have hp := hper θ t ((s : ℂ) * l) ((s : ℂ) * z) hWl
    rw [hk, one_mul] at hp
    show U1 d t θ ((s : ℂ) * (z + l)) / θ ((s : ℂ) * (z + l)) = U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z)
    rw [mul_add]
    by_cases hz0 : θ ((s : ℂ) * z) = 0
    · rw [hz0, (zero_iff_of_fixed hWl _).2 hz0, div_zero, div_zero]
    · have hz1 : θ ((s : ℂ) * z + (s : ℂ) * l) ≠ 0 := fun h => hz0 ((zero_iff_of_fixed hWl _).1 h)
      rw [div_eq_div_iff hz1 hz0]
      exact hp
  have hA0 : AnalyticAt ℂ φ 0 := han 0 (by rw [mul_zero, h0]; exact one_ne_zero)
  have hpole : ∀ p r, PrimeTo d q r → ¬ InOK d (r - 1 / 2) → θ ((s : ℂ) * p + r) = 0 → ¬ M.Small p := by
    intro p r hr hr2 hθ0 hsmall
    exact hr2 (hsm p s r (inOK_nat d s) (by exact_mod_cast hs.ne') hr (hz _ hθ0) hsmall).2
  refine ⟨hE, hA0, han, hpole, GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles q M _ φ hch hE hA0 ?_⟩
  intro p hp
  have hθp : θ ((s : ℂ) * p) = 0 := by
    by_contra hne
    exact absurd hp (not_lt.mpr (han p hne).meromorphicOrderAt_nonneg)
  exact hpole p 0 ⟨1, one_pos, Nat.coprime_one_left q, ⟨0, 0, by simp⟩⟩ (not_inOK_neg_half d hd.pos) (by rw [add_zero]; exact hθp)

end GlobalTheory.MomOne.ScaledQuot
