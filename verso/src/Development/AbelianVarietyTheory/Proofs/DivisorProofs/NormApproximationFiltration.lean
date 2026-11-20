import Mathlib
import Formalism.SatakeDualWeyl.StatementF
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOneAddPiOMul
import GroundTheory.LocalFields.FilteredSurj
open Polynomial Matrix Formalism.UG

noncomputable section

namespace GlobalTheory.NormEq

/- English proof (translation)
Introduce `L _ _ σ ϖ q h P m hm x hx hxm`. Take `⟨x₀, hx₀, hv⟩` from `h.2.2.2.2.1`. Establish `hve : Valued.v (x₀ - σ x₀) = 1` using `by rw [← Valuation.map_neg, neg_sub]; exact hv`. Establish `he : x₀ - σ x₀ ≠ 0`. Introduce `h0`.

Rewrite `hve` using `[h0, map_zero]`. Conclude with `zero_ne_one hve`. Establish `hcO : x₀ * (x₀ - σ x₀)⁻¹ ∈ intL L`. Express the relevant statement in the definitionally equal form `Valued.v (x₀ * (x₀ - σ x₀)⁻¹) ≤ 1`. Rewrite using `[map_mul, map_inv₀, hve, inv_one, mul_one]`.

Conclude with `hx₀`. Set `cO : intL L` to `⟨_, hcO⟩`. Establish `hcs : cO + sigO σ h.2.1 cO = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `x₀ * (x₀ - σ x₀)⁻¹ + σ (x₀ * (x₀ - σ x₀)⁻¹) = 1`.

Establish `e2 : σ x₀ - x₀ = -(x₀ - σ x₀)` using `by ring`. Rewrite using `[map_mul, map_inv₀, map_sub, h.1, e2, inv_neg]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `set ι := algebraMap (intL L) (GlobalTheory.UTr.Alg P) with hι`.

Use `set πA := ι (piO h) with hπA`. Establish `hconjπ : GlobalTheory.UTr.conj P πA = πA`. Rewrite using `[hπA, GlobalTheory.UTr.conj_algebraMap]`. Use `congr 1`. Conclude with `Subtype.ext h.2.2.1`.

Establish `hconjc : GlobalTheory.UTr.conj P (ι cO) + ι cO = 1`. Use `congrArg ι hcs` as an intermediate fact. Rewrite `this` using `[map_add, map_one]`. Rewrite using `[hι, GlobalTheory.UTr.conj_algebraMap]`. Rewrite using `[← this]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h1 : (x : GlobalTheory.UTr.Alg P) - 1 ∈ Ideal.span {πA ^ m}` using `hxm`. Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.1 h1`. Establish `hxc : GlobalTheory.UTr.conj P (x : GlobalTheory.UTr.Alg P) = x` using `GlobalTheory.UTr.mem_plus.1 hx`. Establish `hca : πA ^ m * GlobalTheory.UTr.conj P a = πA ^ m * a`.

Use `congrArg (GlobalTheory.UTr.conj P) ha` as an intermediate fact. Rewrite `this` using `[map_mul, map_pow, hconjπ, map_sub, map_one, hxc]`. Rewrite using `[mul_comm, this, ← ha, mul_comm]`. Take `⟨k, rfl⟩ : ∃ k, m = k + 1` from `⟨m - 1, by omega⟩`. Establish `hu1 : (1 + πA ^ (k + 1) * (ι cO * a)) - 1 ∈ GlobalTheory.NormEq.piPow h P (k + 1)`.

Rewrite using `[add_sub_cancel_left]`. Conclude with `Ideal.mem_span_singleton'.2 ⟨ι cO * a, mul_comm _ _⟩`. Use `⟨(GlobalTheory.NormEq.isUnit_of_sub_one_mem h P hm hu1).unit, hu1, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(x : GlobalTheory.UTr.Alg P) - (1 + πA ^ (k + 1) * (ι cO * a)) * GlobalTheory.UTr.conj P (1 + πA ^ (k + 1) * (ι cO * a)) ∈ Ideal.span {πA ^ (k + 1 + 1)}`. Establish `e1 : GlobalTheory.UTr.conj P (1 + πA ^ (k + 1) * (ι cO * a)) = 1 + πA ^ (k + 1) * (GlobalTheory.UTr.conj P (ι cO) * GlobalTheory.UTr.conj P a)`.

Rewrite using `[map_add, map_one, map_mul, map_pow, hconjπ, map_mul]`. Rewrite using `[e1, Ideal.mem_span_singleton']`. Use `⟨-(πA ^ k * ι cO * a * GlobalTheory.UTr.conj P (ι cO) * GlobalTheory.UTr.conj P a), ?_⟩` and prove the remaining obligations. Take the linear combination `ha + GlobalTheory.UTr.conj P (ι cO) * hca + πA ^ (k + 1) * a * hconjc`.
-/
theorem exists_norm_lift_step : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)) (m : ℕ), 1 ≤ m → ∀ x : (GlobalTheory.UTr.Alg P)ˣ, x ∈ GlobalTheory.UTr.plus P → x ∈ GlobalTheory.NormEq.filt h P m → ∃ u : (GlobalTheory.UTr.Alg P)ˣ, u ∈ GlobalTheory.NormEq.filt h P m ∧ (x : GlobalTheory.UTr.Alg P) - (u : GlobalTheory.UTr.Alg P) * GlobalTheory.UTr.conj P u ∈ GlobalTheory.NormEq.piPow h P (m + 1) := by
  intro L _ _ σ ϖ q h P m hm x hx hxm
  obtain ⟨x₀, hx₀, hv⟩ := h.2.2.2.2.1
  have hve : Valued.v (x₀ - σ x₀) = 1 := by rw [← Valuation.map_neg, neg_sub]; exact hv
  have he : x₀ - σ x₀ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hve; exact zero_ne_one hve
  have hcO : x₀ * (x₀ - σ x₀)⁻¹ ∈ intL L := by
    change Valued.v (x₀ * (x₀ - σ x₀)⁻¹) ≤ 1
    rw [map_mul, map_inv₀, hve, inv_one, mul_one]; exact hx₀
  let cO : intL L := ⟨_, hcO⟩
  have hcs : cO + sigO σ h.2.1 cO = 1 := by
    apply Subtype.ext
    change x₀ * (x₀ - σ x₀)⁻¹ + σ (x₀ * (x₀ - σ x₀)⁻¹) = 1
    have e2 : σ x₀ - x₀ = -(x₀ - σ x₀) := by ring
    rw [map_mul, map_inv₀, map_sub, h.1, e2, inv_neg]
    field_simp
    ring
  set ι := algebraMap (intL L) (GlobalTheory.UTr.Alg P) with hι
  set πA := ι (piO h) with hπA
  have hconjπ : GlobalTheory.UTr.conj P πA = πA := by
    rw [hπA, GlobalTheory.UTr.conj_algebraMap]; congr 1; exact Subtype.ext h.2.2.1
  have hconjc : GlobalTheory.UTr.conj P (ι cO) + ι cO = 1 := by
    have := congrArg ι hcs
    rw [map_add, map_one] at this
    rw [hι, GlobalTheory.UTr.conj_algebraMap]; rw [← this]; ring
  have h1 : (x : GlobalTheory.UTr.Alg P) - 1 ∈ Ideal.span {πA ^ m} := hxm
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
  have hxc : GlobalTheory.UTr.conj P (x : GlobalTheory.UTr.Alg P) = x := GlobalTheory.UTr.mem_plus.1 hx
  have hca : πA ^ m * GlobalTheory.UTr.conj P a = πA ^ m * a := by
    have := congrArg (GlobalTheory.UTr.conj P) ha
    rw [map_mul, map_pow, hconjπ, map_sub, map_one, hxc] at this
    rw [mul_comm, this, ← ha, mul_comm]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hu1 : (1 + πA ^ (k + 1) * (ι cO * a)) - 1 ∈ GlobalTheory.NormEq.piPow h P (k + 1) := by
    rw [add_sub_cancel_left]; exact Ideal.mem_span_singleton'.2 ⟨ι cO * a, mul_comm _ _⟩
  refine ⟨(GlobalTheory.NormEq.isUnit_of_sub_one_mem h P hm hu1).unit, hu1, ?_⟩
  change (x : GlobalTheory.UTr.Alg P) - (1 + πA ^ (k + 1) * (ι cO * a)) *
    GlobalTheory.UTr.conj P (1 + πA ^ (k + 1) * (ι cO * a)) ∈ Ideal.span {πA ^ (k + 1 + 1)}
  have e1 : GlobalTheory.UTr.conj P (1 + πA ^ (k + 1) * (ι cO * a)) =
      1 + πA ^ (k + 1) * (GlobalTheory.UTr.conj P (ι cO) * GlobalTheory.UTr.conj P a) := by
    rw [map_add, map_one, map_mul, map_pow, hconjπ, map_mul]
  rw [e1, Ideal.mem_span_singleton']
  refine ⟨-(πA ^ k * ι cO * a * GlobalTheory.UTr.conj P (ι cO) * GlobalTheory.UTr.conj P a), ?_⟩
  linear_combination ha + GlobalTheory.UTr.conj P (ι cO) * hca + πA ^ (k + 1) * a * hconjc

end GlobalTheory.NormEq
