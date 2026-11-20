import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelTorsionBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RelTorsionBound

attribute [local instance] MvPolynomial.weightedGradedAlgebra

section Lemmas

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def blockWeight : (Σ k, ι k) → (K → ℕ) := fun p => Pi.single p.1 1

/- English proof (translation)
Use function extensionality and compare the values at `k`. Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single k]`. Simplify using `[blockWeight]`. Introduce `k' _ hk`. Simplify using `[blockWeight, Ne.symm hk]`.

Simplify using the standard rewrite rules.
-/
theorem weight_blockWeight (μ : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blockWeight (ι := ι)) μ = fun k => ∑ i, μ ⟨k, i⟩ := by
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma,
    Finset.sum_eq_single k]
  · simp [blockWeight]
  · intro k' _ hk
    simp [blockWeight, Ne.symm hk]
  · simp

omit [DecidableEq K] in

/- English proof (translation)
Rewrite using `[aeval_monomial, Finsupp.prod_fintype _ _ (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem aeval_monomial_one (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (μ : (Σ k, ι k) →₀ ℕ) :
    aeval y (monomial μ (1 : R)) = ∏ p, y p ^ μ p := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  simp

/- English proof (translation)
Rewrite using `[relSecM, Submodule.span_le]`. Introduce and unpack `_ ⟨μ, hμ, rfl⟩`. Use `⟨monomial (Finsupp.equivFunOnFinite.symm μ) 1, ?_, ?_⟩` and prove the remaining obligations. Use `(mem_weightedHomogeneousSubmodule _ _ _ _).2 (isWeightedHomogeneous_monomial _ _ _ ?_)` and prove the remaining obligations. Rewrite using `[weight_blockWeight]`.

Use function extensionality and compare the values at `k`. Simplify using `using hμ k`. Simplify using `[aeval_monomial_one]`.
-/
theorem relSecM_le_map (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (b : K → ℕ) :
    relSecM R y b ≤ (weightedHomogeneousSubmodule R (blockWeight (ι := ι)) b).map (aeval y).toLinearMap := by
  rw [relSecM, Submodule.span_le]
  rintro _ ⟨μ, hμ, rfl⟩
  refine ⟨monomial (Finsupp.equivFunOnFinite.symm μ) 1, ?_, ?_⟩
  · refine (mem_weightedHomogeneousSubmodule _ _ _ _).2 (isWeightedHomogeneous_monomial _ _ _ ?_)
    rw [weight_blockWeight]
    funext k
    simpa using hμ k
  · simp [aeval_monomial_one]

omit [Fintype K] [DecidableEq K] in

/- English proof (translation)
Establish `hk : ∀ k, ∃ i, N ≤ μ ⟨k, i⟩`. Introduce `k`. Assume the negation of the conclusion as `hn`. Simplify using `only [not_exists, not_le] at hn`. Establish `hle` using `Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (hn i).le`.

Simplify using `only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle`. Conclude with `absurd (h k) (not_lt.2 hle)`. Conclude with `⟨fun k => (hk k).choose, fun k => (hk k).choose_spec⟩`.
-/
theorem exists_chart_le (N : ℕ) (μ : (Σ k, ι k) → ℕ)
    (h : ∀ k, Fintype.card (ι k) * N < ∑ i, μ ⟨k, i⟩) : ∃ c : ∀ k, ι k, ∀ k, N ≤ μ ⟨k, c k⟩ := by
  have hk : ∀ k, ∃ i, N ≤ μ ⟨k, i⟩ := by
    intro k
    by_contra hn
    simp only [not_exists, not_le] at hn
    have hle := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (hn i).le
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
    exact absurd (h k) (not_lt.2 hle)
  exact ⟨fun k => (hk k).choose, fun k => (hk k).choose_spec⟩

omit [Fintype K] [DecidableEq K] in
open Classical in

/- English proof (translation)
Rewrite using `[Finset.sum_ite_eq]`. Simplify using the standard rewrite rules.
-/
theorem sum_chart (c : ∀ k, ι k) (N : ℕ) (k : K) : ∑ i, (if c k = i then N else 0) = N := by
  rw [Finset.sum_ite_eq]
  simp

omit [DecidableEq K] in
open Classical in

/- English proof (translation)
Rewrite using `[Fintype.prod_sigma, ← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_single (c k)]`. Simplify using the standard rewrite rules. Introduce `i _ hi`.

Simplify using `[Ne.symm hi]`. Simplify using the standard rewrite rules.
-/
theorem prod_chart (z : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (N : ℕ) :
    ∏ p : Σ k, ι k, z p ^ (if c p.1 = p.2 then N else 0) = (∏ k, z ⟨k, c k⟩) ^ N := by
  rw [Fintype.prod_sigma, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_eq_single (c k)]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

omit [DecidableEq K] in

/- English proof (translation)
Rewrite using `[← prod_chart]`. Conclude with `monomial_mem_relSecM R y _ fun k => sum_chart c N k`.
-/
theorem chart_pow_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (N : ℕ) :
    (∏ k, y ⟨k, c k⟩) ^ N ∈ relSecM R y (fun _ => N) := by
  classical
  rw [← prod_chart]
  exact monomial_mem_relSecM R y _ fun k => sum_chart c N k

omit [DecidableEq K] in

/- English proof (translation)
Establish `hsplit : ∀ p : Σ k, ι k, μ p = (μ p - if c p.1 = p.2 then N else 0) + if c p.1 = p.2 then N else 0`. Introduce `p`. Use `split_ifs with h`. Establish `hp : N ≤ μ p`. Use `hc p.1` as an intermediate fact.

Rewrite `this` using `[h]`. Conclude with `this`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Use `⟨fun p => μ p - if c p.1 = p.2 then N else 0, fun k => ?_, fun z => ?_⟩` and prove the remaining obligations.

Establish `hs : ∑ i, μ ⟨k, i⟩ = ∑ i, ((μ ⟨k, i⟩ - if c k = i then N else 0) + if c k = i then N else 0)` using `Finset.sum_congr rfl fun i _ => hsplit ⟨k, i⟩`. Rewrite using `[hs, Finset.sum_add_distrib, sum_chart]`. Rewrite using `[← prod_chart z c N, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_add, ← hsplit p]`.
-/
theorem exists_chart_factor (N : ℕ) (μ : (Σ k, ι k) → ℕ) (c : ∀ k, ι k) (hc : ∀ k, N ≤ μ ⟨k, c k⟩) :
    ∃ ν : (Σ k, ι k) → ℕ, (∀ k, ∑ i, ν ⟨k, i⟩ + N = ∑ i, μ ⟨k, i⟩) ∧
      ∀ z : (Σ k, ι k) → Ω, ∏ p, z p ^ μ p = (∏ p, z p ^ ν p) * (∏ k, z ⟨k, c k⟩) ^ N := by
  classical
  have hsplit : ∀ p : Σ k, ι k,
      μ p = (μ p - if c p.1 = p.2 then N else 0) + if c p.1 = p.2 then N else 0 := by
    intro p
    split_ifs with h
    · have hp : N ≤ μ p := by
        have := hc p.1
        rw [h] at this
        exact this
      omega
    · omega
  refine ⟨fun p => μ p - if c p.1 = p.2 then N else 0, fun k => ?_, fun z => ?_⟩
  · have hs : ∑ i, μ ⟨k, i⟩ = ∑ i, ((μ ⟨k, i⟩ - if c k = i then N else 0) + if c k = i then N else 0) :=
      Finset.sum_congr rfl fun i _ => hsplit ⟨k, i⟩
    rw [hs, Finset.sum_add_distrib, sum_chart]
  · rw [← prod_chart z c N, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_add, ← hsplit p]

omit [∀ k, Fintype (ι k)] in
open Classical in

/- English proof (translation)
Establish `h` using `DirectSum.coe_decompose_mul_of_right_mem (𝒜 := weightedHomogeneousSubmodule R (blockWeight (ι := ι))) (a := A) m hG`. Rewrite using `[← decompose'_apply R blockWeight, ← decompose'_apply R blockWeight]`. Conclude with `h`.
-/
theorem comp_mul (R : Type*) [CommRing R] {d : K → ℕ} (m : K → ℕ) {G : MvPolynomial (Σ k, ι k) R}
    (hG : G ∈ weightedHomogeneousSubmodule R (blockWeight (ι := ι)) d) (A : MvPolynomial (Σ k, ι k) R) :
    weightedHomogeneousComponent blockWeight m (A * G) =
      if d ≤ m then weightedHomogeneousComponent blockWeight (m - d) A * G else 0 := by
  have h := DirectSum.coe_decompose_mul_of_right_mem
    (𝒜 := weightedHomogeneousSubmodule R (blockWeight (ι := ι))) (a := A) m hG
  rw [← decompose'_apply R blockWeight, ← decompose'_apply R blockWeight]
  exact h

def KilledAt (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k) (k0 : K) (c : ∀ k, ι k) (d : K → ℕ)
    (N : ℕ) (v : Ω) : Prop :=
  ∃ a : K → ℕ, a + Pi.single k0 1 = d + (fun _ => N) ∧
    ∃ g ∈ relSecM R y a, (∏ k, y ⟨k, c k⟩) ^ N * v = y ⟨k0, c0 k0⟩ * g

/- English proof (translation)
Take `⟨a, ha, g, hg, hgv⟩` from `h`. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le hN`. Use `⟨(fun _ => m) + a, ?_, (∏ k, y ⟨k, c k⟩) ^ m * g, mul_mem_relSecM R y (chart_pow_mem R y c m) hg, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Use `congrFun ha k` as an intermediate fact.

Simplify using `only [Pi.add_apply] at this ⊢`. Use linear arithmetic over natural numbers and integers. Take the linear combination `(∏ k, y ⟨k, c k⟩) ^ m * hgv`.
-/
theorem KilledAt.mono {R : Subalgebra ℤ Ω} {y : (Σ k, ι k) → Ω} {c0 : ∀ k, ι k} {k0 : K} {c : ∀ k, ι k}
    {d : K → ℕ} {N N' : ℕ} {v : Ω} (h : KilledAt R y c0 k0 c d N v) (hN : N ≤ N') :
    KilledAt R y c0 k0 c d N' v := by
  obtain ⟨a, ha, g, hg, hgv⟩ := h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN
  refine ⟨(fun _ => m) + a, ?_, (∏ k, y ⟨k, c k⟩) ^ m * g, mul_mem_relSecM R y (chart_pow_mem R y c m) hg, ?_⟩
  · funext k
    have := congrFun ha k
    simp only [Pi.add_apply] at this ⊢
    omega
  · linear_combination (∏ k, y ⟨k, c k⟩) ^ m * hgv

def TorsionForm (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k) (k0 : K) (d : K → ℕ) (N : ℕ)
    (G : MvPolynomial (Σ k, ι k) R) : Prop :=
  G ∈ weightedHomogeneousSubmodule R (blockWeight (ι := ι)) d ∧
    ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → KilledAt R y c0 k0 c d N (aeval y G)

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, fun c hc => (h.2 c hc).mono hN⟩`.
-/
theorem TorsionForm.mono {R : Subalgebra ℤ Ω} {y : (Σ k, ι k) → Ω} {c0 : ∀ k, ι k} {k0 : K} {d : K → ℕ}
    {N N' : ℕ} {G : MvPolynomial (Σ k, ι k) R} (h : TorsionForm R y c0 k0 d N G) (hN : N ≤ N') :
    TorsionForm R y c0 k0 d N' G :=
  ⟨h.1, fun c hc => (h.2 c hc).mono hN⟩

/- English proof (translation)
Rewrite using `[A.as_sum, Finset.sum_mul, map_sum]`. Use `Submodule.sum_mem _ fun μ hμ => ?_` and prove the remaining obligations. Establish `hwμ : Finsupp.weight blockWeight μ = a` using `hA (mem_support_iff.1 hμ)`. Rewrite `hwμ` using `[weight_blockWeight]`. Take `⟨c, hc⟩` from `exists_chart_le N μ fun k => by rw [congrFun hwμ k]; exact ha k`.

Take `⟨ν, hν, hfac⟩` from `exists_chart_factor (Ω := Ω) N μ c hc`. Establish `hval : aeval y (monomial μ (coeff μ A) * G) = algebraMap R Ω (coeff μ A) * ((∏ p, y p ^ ν p) * ((∏ k, y ⟨k, c k⟩) ^ N * aeval y G))`. Rewrite using `[show monomial μ (coeff μ A) = C (coeff μ A) * monomial μ 1 by rw [C_mul_monomial, mul_one], map_mul, map_mul, aeval_C, aeval_monomial_one, hfac y]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hgood : ∀ k, y ⟨k, c k⟩ ≠ 0`.

Take `⟨a', ha', g, hg, hgv⟩` from `hG.2 c hgood`. Establish `hdeg : (fun k => ∑ i, ν ⟨k, i⟩) + a' = b`. Use function extensionality and compare the values at `k`. Establish `h1` using `hν k`. Establish `h2` using `congrFun hwμ k`.

Establish `h3` using `congrFun ha' k`. Establish `h4` using `congrFun hab k`. Simplify using `only [Pi.add_apply] at h3 h4 ⊢`. Use linear arithmetic over natural numbers and integers. Establish `hmem` using `mul_mem_relSecM R y (monomial_mem_relSecM R y ν fun k => rfl) hg`.

Rewrite `hmem` using `[hdeg]`. Use `⟨coeff μ A • ((∏ p, y p ^ ν p) * g), Submodule.smul_mem _ _ hmem, ?_⟩` and prove the remaining obligations. Rewrite using `[hval, hgv, LinearMap.mulLeft_apply, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [not_forall, not_not] at hgood`.

Take `⟨k, hk⟩` from `hgood`. Establish `hprod : ∏ k, y ⟨k, c k⟩ = 0` using `Finset.prod_eq_zero (Finset.mem_univ k) hk`. Rewrite using `[hval, hprod, zero_pow (by omega), zero_mul, mul_zero, mul_zero]`. Conclude with `Submodule.zero_mem _`.
-/
theorem aeval_mul_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k) (k0 : K) {d a b : K → ℕ}
    {N : ℕ} (hN : 1 ≤ N) {G : MvPolynomial (Σ k, ι k) R} (hG : TorsionForm R y c0 k0 d N G)
    (ha : ∀ k, Fintype.card (ι k) * N < a k) (hab : a + d = b + Pi.single k0 1)
    {A : MvPolynomial (Σ k, ι k) R} (hA : A ∈ weightedHomogeneousSubmodule R (blockWeight (ι := ι)) a) :
    aeval y (A * G) ∈ (relSecM R y b).map (LinearMap.mulLeft R (y ⟨k0, c0 k0⟩)) := by
  rw [A.as_sum, Finset.sum_mul, map_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  have hwμ : Finsupp.weight blockWeight μ = a := hA (mem_support_iff.1 hμ)
  rw [weight_blockWeight] at hwμ
  obtain ⟨c, hc⟩ := exists_chart_le N μ fun k => by rw [congrFun hwμ k]; exact ha k
  obtain ⟨ν, hν, hfac⟩ := exists_chart_factor (Ω := Ω) N μ c hc
  have hval : aeval y (monomial μ (coeff μ A) * G) = algebraMap R Ω (coeff μ A) *
      ((∏ p, y p ^ ν p) * ((∏ k, y ⟨k, c k⟩) ^ N * aeval y G)) := by
    rw [show monomial μ (coeff μ A) = C (coeff μ A) * monomial μ 1 by rw [C_mul_monomial, mul_one],
      map_mul, map_mul, aeval_C, aeval_monomial_one, hfac y]
    ring
  by_cases hgood : ∀ k, y ⟨k, c k⟩ ≠ 0
  · obtain ⟨a', ha', g, hg, hgv⟩ := hG.2 c hgood
    have hdeg : (fun k => ∑ i, ν ⟨k, i⟩) + a' = b := by
      funext k
      have h1 := hν k
      have h2 := congrFun hwμ k
      have h3 := congrFun ha' k
      have h4 := congrFun hab k
      simp only [Pi.add_apply] at h3 h4 ⊢
      omega
    have hmem := mul_mem_relSecM R y (monomial_mem_relSecM R y ν fun k => rfl) hg
    rw [hdeg] at hmem
    refine ⟨coeff μ A • ((∏ p, y p ^ ν p) * g), Submodule.smul_mem _ _ hmem, ?_⟩
    rw [hval, hgv, LinearMap.mulLeft_apply, Algebra.smul_def]
    ring
  · simp only [not_forall, not_not] at hgood
    obtain ⟨k, hk⟩ := hgood
    have hprod : ∏ k, y ⟨k, c k⟩ = 0 := Finset.prod_eq_zero (Finset.mem_univ k) hk
    rw [hval, hprod, zero_pow (by omega), zero_mul, mul_zero, mul_zero]
    exact Submodule.zero_mem _

end Lemmas

/- English proof (translation)
Introduce `K _ _ ι _ Ω _ R hR y c0 hc0 k0`. Use `hR` as an intermediate fact. Set `s : Set (MvPolynomial (Σ k, ι k) R)` to `{G | ∃ d N, TorsionForm R y c0 k0 d N G}`. Take `⟨t, hts, hspan⟩` from `(Submodule.fg_span_iff_fg_span_finset_subset s).1 (IsNoetherian.noetherian (R := MvPolynomial (Σ k, ι k) R) _)`. Establish `hs : ∀ G ∈ s, ∃ d N, TorsionForm R y c0 k0 d N G` using `fun G h => h`.

Use `choose! dG NG hdN using hs`. Use `set N₀ := t.sup NG + 1 with hN₀`. Establish `hT : ∀ G ∈ t, TorsionForm R y c0 k0 (dG G) N₀ G` using `fun G hG => (hdN G (hts hG)).mono (by have := Finset.le_sup (f := NG) hG; omega)`. Use `⟨∑ k, (Fintype.card (ι k) * N₀ + 1) + ∑ G ∈ t, ∑ k, dG G k, fun b hb f hf hyp => ?_⟩` and prove the remaining obligations. Take `⟨F, hF, rfl⟩` from `relSecM_le_map R y _ hf`.

Use `choose! D g hg hgf using hyp`. Establish `hFs : F ∈ s`. Use `⟨b + Pi.single k0 1, Finset.univ.sup D, hF, fun c hc => ?_⟩` and prove the remaining obligations. Use `KilledAt.mono ⟨b + fun _ => D c, ?_, g c, hg c hc, hgf c hc⟩ (Finset.le_sup (Finset.mem_univ c))` and prove the remaining obligations. Use function extensionality and compare the values at `k`.

Simplify using `only [Pi.add_apply]`. Use linear arithmetic over natural numbers and integers. Establish `hFt : F ∈ Submodule.span (MvPolynomial (Σ k, ι k) R) (t : Set (MvPolynomial (Σ k, ι k) R))` using `hspan ▸ Submodule.subset_span hFs`. Take `⟨A, -, hA⟩` from `Submodule.mem_span_finset.1 hFt`. Establish `hFsum : F = ∑ G ∈ t, weightedHomogeneousComponent blockWeight (b + Pi.single k0 1) (A G * G)`.

Establish `h1 : weightedHomogeneousComponent blockWeight (b + Pi.single k0 1) F = F` using `IsWeightedHomogeneous.weightedHomogeneousComponent_same ((mem_weightedHomogeneousSubmodule _ _ _ _).1 hF)`. Rewrite using `[← h1]`. Use `conv_lhs => rw [← hA]`. Rewrite using `[map_sum]`. Simplify using `only [smul_eq_mul]`.

It suffices to establish `h : aeval y F ∈ (relSecM R y b).map (LinearMap.mulLeft R (y ⟨k0, c0 k0⟩)) by`. Take `⟨g', hg', hgx⟩` from `h`. Conclude with `⟨g', hg', by simpa using hgx.symm⟩`. Rewrite using `[hFsum, map_sum]`. Use `Submodule.sum_mem _ fun G hG => ?_` and prove the remaining obligations.

Rewrite using `[comp_mul _ _ (hT G hG).1]`. Use `split_ifs with hle`. Use `aeval_mul_mem R y c0 k0 (by omega) (hT G hG) (fun k => ?_) (tsub_add_cancel_of_le hle) (weightedHomogeneousComponent_mem _ _ _)` and prove the remaining obligations. Establish `h1 : Fintype.card (ι k) * N₀ + 1 ≤ ∑ k, (Fintype.card (ι k) * N₀ + 1)` using `Finset.single_le_sum (f := fun k => Fintype.card (ι k) * N₀ + 1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)`. Establish `h2 : dG G k ≤ ∑ k, dG G k` using `Finset.single_le_sum (f := fun k => dG G k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)`.

Establish `h3 : ∑ k, dG G k ≤ ∑ G ∈ t, ∑ k, dG G k` using `Finset.single_le_sum (f := fun G => ∑ k, dG G k) (fun _ _ => Nat.zero_le _) hG`. Establish `h4` using `hb k`. Establish `h5` using `hle k`. Simplify using `only [Pi.sub_apply, Pi.add_apply] at h5 ⊢`. Use linear arithmetic over natural numbers and integers.

Simplify using the standard rewrite rules.
-/
theorem proof : RelTorsionBound.Statement := by
  intro K _ _ ι _ Ω _ R hR y c0 hc0 k0
  classical
  have := hR
  let s : Set (MvPolynomial (Σ k, ι k) R) := {G | ∃ d N, TorsionForm R y c0 k0 d N G}
  obtain ⟨t, hts, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset s).1 (IsNoetherian.noetherian (R := MvPolynomial (Σ k, ι k) R) _)
  have hs : ∀ G ∈ s, ∃ d N, TorsionForm R y c0 k0 d N G := fun G h => h
  choose! dG NG hdN using hs
  set N₀ := t.sup NG + 1 with hN₀
  have hT : ∀ G ∈ t, TorsionForm R y c0 k0 (dG G) N₀ G := fun G hG =>
    (hdN G (hts hG)).mono (by have := Finset.le_sup (f := NG) hG; omega)
  refine ⟨∑ k, (Fintype.card (ι k) * N₀ + 1) + ∑ G ∈ t, ∑ k, dG G k, fun b hb f hf hyp => ?_⟩
  obtain ⟨F, hF, rfl⟩ := relSecM_le_map R y _ hf
  choose! D g hg hgf using hyp
  have hFs : F ∈ s := by
    refine ⟨b + Pi.single k0 1, Finset.univ.sup D, hF, fun c hc => ?_⟩
    refine KilledAt.mono ⟨b + fun _ => D c, ?_, g c, hg c hc, hgf c hc⟩ (Finset.le_sup (Finset.mem_univ c))
    funext k
    simp only [Pi.add_apply]
    omega
  have hFt : F ∈ Submodule.span (MvPolynomial (Σ k, ι k) R) (t : Set (MvPolynomial (Σ k, ι k) R)) :=
    hspan ▸ Submodule.subset_span hFs
  obtain ⟨A, -, hA⟩ := Submodule.mem_span_finset.1 hFt
  have hFsum : F = ∑ G ∈ t, weightedHomogeneousComponent blockWeight (b + Pi.single k0 1) (A G * G) := by
    have h1 : weightedHomogeneousComponent blockWeight (b + Pi.single k0 1) F = F :=
      IsWeightedHomogeneous.weightedHomogeneousComponent_same ((mem_weightedHomogeneousSubmodule _ _ _ _).1 hF)
    rw [← h1]
    conv_lhs => rw [← hA]
    rw [map_sum]
    simp only [smul_eq_mul]
  suffices h : aeval y F ∈ (relSecM R y b).map (LinearMap.mulLeft R (y ⟨k0, c0 k0⟩)) by
    obtain ⟨g', hg', hgx⟩ := h
    exact ⟨g', hg', by simpa using hgx.symm⟩
  rw [hFsum, map_sum]
  refine Submodule.sum_mem _ fun G hG => ?_
  rw [comp_mul _ _ (hT G hG).1]
  split_ifs with hle
  · refine aeval_mul_mem R y c0 k0 (by omega) (hT G hG) (fun k => ?_) (tsub_add_cancel_of_le hle)
      (weightedHomogeneousComponent_mem _ _ _)
    have h1 : Fintype.card (ι k) * N₀ + 1 ≤ ∑ k, (Fintype.card (ι k) * N₀ + 1) :=
      Finset.single_le_sum (f := fun k => Fintype.card (ι k) * N₀ + 1) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k)
    have h2 : dG G k ≤ ∑ k, dG G k :=
      Finset.single_le_sum (f := fun k => dG G k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have h3 : ∑ k, dG G k ≤ ∑ G ∈ t, ∑ k, dG G k :=
      Finset.single_le_sum (f := fun G => ∑ k, dG G k) (fun _ _ => Nat.zero_le _) hG
    have h4 := hb k
    have h5 := hle k
    simp only [Pi.sub_apply, Pi.add_apply] at h5 ⊢
    omega
  · simp

end RelTorsionBound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
