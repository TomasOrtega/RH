import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedStandardAdelicLatticePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleAtOfIrreducibleTameStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.LatSelfDual

/- English proof (translation)
Unfold `ee`. Rewrite using `[Complex.exp_eq_one_iff]`. Establish `h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0` using `by simp [Real.pi_ne_zero]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn⟩`.

Use `⟨-n, ?_⟩` and prove the remaining obligations. Rewrite `hn` using `[mul_comm (n : ℂ)]`. Establish `h3` using `mul_left_cancel₀ h2 hn`. Establish `h4 : (-t : ℝ) = (n : ℝ)` using `by exact_mod_cast h3`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce and unpack `⟨m, rfl⟩`. Use `⟨-m, ?_⟩` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ee_neg_eq_one_iff (t : ℝ) : ee (-t) = 1 ↔ ∃ m : ℤ, t = m := by
  unfold ee
  rw [Complex.exp_eq_one_iff]
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [mul_comm (n : ℂ)] at hn
    have h3 := mul_left_cancel₀ h2 hn
    have h4 : (-t : ℝ) = (n : ℝ) := by exact_mod_cast h3
    push_cast
    linarith
  · rintro ⟨m, rfl⟩
    refine ⟨-m, ?_⟩
    push_cast
    ring

/- English proof (translation)
Simplify using `only [gamA, ← hψ, Matrix.add_apply, add_mul, Finset.sum_add_distrib]`.
-/
theorem gamA_add_left {D : D7} {ψ : AE D → ℂ} (hψ : ∀ x y, ψ (x + y) = ψ x * ψ y) {N N' : ℕ} (ζ η ξ : XA D N N') :
    gamA ψ (ζ + η) ξ = gamA ψ ζ ξ * gamA ψ η ξ := by
  simp only [gamA, ← hψ, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [gamA, ← hψ, Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]`.
-/
theorem gamA_add_right {D : D7} {ψ : AE D → ℂ} (hψ : ∀ x y, ψ (x + y) = ψ x * ψ y) {N N' : ℕ} (ζ η ξ : XA D N N') :
    gamA ψ ζ (η + ξ) = gamA ψ ζ η * gamA ψ ζ ξ := by
  simp only [gamA, ← hψ, Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Rewrite using `[← hψ]`. Simplify using `only [gamA, Matrix.map_apply, map_sum, map_mul, GlobalTheory.NormSum.PtsMem.sgA_inc]`.
-/
theorem gamA_rat {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {ψ : AE D → ℂ} (hψ : ∀ a, ψ (inc D a) = psi0 D cc δ a)
    {N N' : ℕ} (z y : Matrix (Fin N') (Fin N) D.host.E) :
    gamA ψ (z.map (inc D)) (y.map (inc D)) = psi0 D cc δ (∑ i, ∑ j, z i j * D.host.conj (y i j)) := by
  rw [← hψ]
  simp only [gamA, Matrix.map_apply, map_sum, map_mul, GlobalTheory.NormSum.PtsMem.sgA_inc]

/- English proof (translation)
Take `⟨hadd, -, hrat, -, m₀, hm₀, h₀⟩` from `hψ`. Take `⟨l1, l2, l3, -, ⟨m₁, hm₁, h₁⟩, -⟩` from `GlobalTheory.T.completedStandardAdelicLattice_properties D hG cc δ hC N N'`. Take `⟨w, -, hw⟩` from `GlobalTheory.T.theta_point_additive_form D hG cc δ hC`. Establish `hSD : ∀ n, SD D (stdL D n)` using `fun n => by`. Take `⟨Lt, hL, h1, -⟩` from `GlobalTheory.NormSum.exists_lattice_of_adelic_point D n`.

Conclude with `h1 ▸ (hL 1).2`. Take `⟨-, -, t1, t2, -⟩` from `GlobalTheory.ThetaLine.theta_line D hG cc δ hC N N' (La0 D (tor0 D cc δ) N N') (Or.inr ⟨_, _, hSD N, hSD N', rfl⟩)`. Establish `key : ∀ z y : Matrix (Fin N') (Fin N) D.host.E, gamA ψ (z.map (inc D)) (y.map (inc D)) = 1 ↔ ∃ m : ℤ, (Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ y)).im = m` using `fun z y => by`. Rewrite using `[gamA_rat hrat, ← (hw N N' z y).1, ee_neg_eq_one_iff]`. Establish `hM : 0 < m₀ * m₁ * m₁` using `by positivity`.

Establish `hs : ∀ ζ ∈ latA D cc N N', ∀ η ∈ latA D cc N N', (∑ i, ∑ j, ((m₁ : AE D) * ζ i j) * sgA D ((m₁ : AE D) * η i j)) ∈ OhE D` using `fun ζ hζ η hη => sum_mem fun i _ => sum_mem fun j _ => mul_mem (h₁ _ (hζ i j)) (Formalism.UG.P.csDual_sig_mem _ (h₁ _ (hη i j)))`. Establish `dl : ∀ ζ ∈ latA D cc N N', ∀ η ∈ latA D cc N N', gamA ψ ((m₀ * m₁ * m₁) • ζ) η = 1` using `fun ζ hζ η hη => by`. Rewrite using `[← h₀ _ (hs ζ hζ η hη), gamA]`. Use `congr 1`. Simplify using `only [Finset.mul_sum, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `dr : ∀ ζ ∈ latA D cc N N', ∀ η ∈ latA D cc N N', gamA ψ ζ ((m₀ * m₁ * m₁) • η) = 1` using `fun ζ hζ η hη => by`. Rewrite using `[← h₀ _ (hs ζ hζ η hη), gamA]`.

Use `congr 1`. Simplify using `only [Finset.mul_sum, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `iso : ∀ ζ ∈ latA D cc N N', ∀ η ∈ latA D cc N N', gamA ψ ζ η = 1` using `fun ζ hζ η hη => by`. Take `⟨z, a, ha, hz⟩` from `l3 ζ _ hM`. Take `⟨y, b, hb, hy⟩` from `l3 η _ hM`. Establish `hzm : z.map (inc D) ∈ latA D cc N N'` using `hz ▸ add_mem hζ (nsmul_mem ha _)`. Establish `hym : y.map (inc D) ∈ latA D cc N N'` using `hy ▸ add_mem hη (nsmul_mem hb _)`.

Establish `h` using `(key z y).2 (t1 _ ((l1 z).1 hzm) _ ((l1 y).1 hym))`. Rewrite `h` using `[hz, gamA_add_left hadd, dl a ha _ hym, mul_one, hy, gamA_add_right hadd, dr ζ hζ b hb, mul_one]`. Then use the resulting hypothesis. Use `fun ζ => ⟨iso ζ, fun h => ?_⟩` and prove the remaining obligations. Take `⟨z, a, ha, hz⟩` from `l3 ζ 1 one_pos`. Rewrite `hz` using `[one_smul]`.

Establish `hzm : z.map (inc D) ∈ latA D cc N N'`. Use `(l1 z).2 (t2 _ fun x hx => ?_)` and prove the remaining obligations. Take `⟨y, rfl⟩` from `l2 x hx`. Establish `hym` using `(l1 y).2 hx`. Rewrite using `[← key, hz, gamA_add_left hadd, h _ hym, iso a ha _ hym, mul_one]`.

Establish `: ζ = z.map (inc D) - a` using `by rw [hz, add_sub_cancel_right]`. Rewrite using `[this]`. Conclude with `sub_mem hzm ha`.
-/
theorem latA_selfDual (D : D7) (hG : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hC : Crv D cc δ) (ψ : AE D → ℂ)
    (hψ : IsPsi D cc δ ψ) (N N' : ℕ) : SelfDual (gamA ψ) (latA D cc N N') := by
  obtain ⟨hadd, -, hrat, -, m₀, hm₀, h₀⟩ := hψ
  obtain ⟨l1, l2, l3, -, ⟨m₁, hm₁, h₁⟩, -⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hG cc δ hC N N'
  obtain ⟨w, -, hw⟩ := GlobalTheory.T.theta_point_additive_form D hG cc δ hC
  have hSD : ∀ n, SD D (stdL D n) := fun n => by
    obtain ⟨Lt, hL, h1, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D n
    exact h1 ▸ (hL 1).2
  obtain ⟨-, -, t1, t2, -⟩ := GlobalTheory.ThetaLine.theta_line D hG cc δ hC N N' (La0 D (tor0 D cc δ) N N')
    (Or.inr ⟨_, _, hSD N, hSD N', rfl⟩)
  have key : ∀ z y : Matrix (Fin N') (Fin N) D.host.E, gamA ψ (z.map (inc D)) (y.map (inc D)) = 1 ↔
      ∃ m : ℤ, (Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ y)).im = m := fun z y => by
    rw [gamA_rat hrat, ← (hw N N' z y).1, ee_neg_eq_one_iff]
  have hM : 0 < m₀ * m₁ * m₁ := by positivity
  have hs : ∀ ζ ∈ latA D cc N N', ∀ η ∈ latA D cc N N',
      (∑ i, ∑ j, ((m₁ : AE D) * ζ i j) * sgA D ((m₁ : AE D) * η i j)) ∈ OhE D := fun ζ hζ η hη =>
    sum_mem fun i _ => sum_mem fun j _ => mul_mem (h₁ _ (hζ i j)) (Formalism.UG.P.csDual_sig_mem _ (h₁ _ (hη i j)))
  have dl : ∀ ζ ∈ latA D cc N N', ∀ η ∈ latA D cc N N', gamA ψ ((m₀ * m₁ * m₁) • ζ) η = 1 := fun ζ hζ η hη => by
    rw [← h₀ _ (hs ζ hζ η hη), gamA]
    congr 1
    simp only [Finset.mul_sum, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have dr : ∀ ζ ∈ latA D cc N N', ∀ η ∈ latA D cc N N', gamA ψ ζ ((m₀ * m₁ * m₁) • η) = 1 := fun ζ hζ η hη => by
    rw [← h₀ _ (hs ζ hζ η hη), gamA]
    congr 1
    simp only [Finset.mul_sum, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have iso : ∀ ζ ∈ latA D cc N N', ∀ η ∈ latA D cc N N', gamA ψ ζ η = 1 := fun ζ hζ η hη => by
    obtain ⟨z, a, ha, hz⟩ := l3 ζ _ hM
    obtain ⟨y, b, hb, hy⟩ := l3 η _ hM
    have hzm : z.map (inc D) ∈ latA D cc N N' := hz ▸ add_mem hζ (nsmul_mem ha _)
    have hym : y.map (inc D) ∈ latA D cc N N' := hy ▸ add_mem hη (nsmul_mem hb _)
    have h := (key z y).2 (t1 _ ((l1 z).1 hzm) _ ((l1 y).1 hym))
    rwa [hz, gamA_add_left hadd, dl a ha _ hym, mul_one, hy, gamA_add_right hadd, dr ζ hζ b hb, mul_one] at h
  refine fun ζ => ⟨iso ζ, fun h => ?_⟩
  obtain ⟨z, a, ha, hz⟩ := l3 ζ 1 one_pos
  rw [one_smul] at hz
  have hzm : z.map (inc D) ∈ latA D cc N N' := by
    refine (l1 z).2 (t2 _ fun x hx => ?_)
    obtain ⟨y, rfl⟩ := l2 x hx
    have hym := (l1 y).2 hx
    rw [← key, hz, gamA_add_left hadd, h _ hym, iso a ha _ hym, mul_one]
  have : ζ = z.map (inc D) - a := by rw [hz, add_sub_cancel_right]
  rw [this]
  exact sub_mem hzm ha

end GlobalTheory.FinWeil.LatSelfDual
