import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraDefs
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemSpanVariable

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

section SlopeTestRemainingChoices

open MvPowerSeries

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X f hf`.
-/
private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X f hf

/- English proof (translation)
Establish `h1 : ∀ g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)), ((1 : ℕ) : ℕ∞) ≤ g.order`. Introduce `g hg`. Establish `hle : Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) ≤ RingHom.ker (constantCoeff : MvPowerSeries σ O →+* O)`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Simplify using the standard rewrite rules. Use `nat_le_order fun d hd => ?_` and prove the remaining obligations. Establish `hd0 : d = 0`. Rewrite using `[← Finsupp.degree_eq_zero_iff]`. Use linear arithmetic over natural numbers and integers.

Substitute `hd0` using the available equality. Simplify using `using hle hg`. Proceed by induction on `n with`. Consider the case `zero => intro g _`. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Introduce `g hg`. Rewrite `hg` using `[pow_succ]`. Use `Submodule.mul_induction_on hg (fun x hx y hy => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Use `le_trans ?_ le_order_mul` and prove the remaining obligations.

Rewrite using `[Nat.cast_add]`. Conclude with `add_le_add (ih x hx) (h1 y hy)`. Conclude with `le_trans (le_min hx hy) min_order_le_add`.
-/
private theorem order_of_mem_pow {O σ : Type} [CommRing O] (n : ℕ) :
    ∀ g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) ^ n, (n : ℕ∞) ≤ g.order := by
  have h1 : ∀ g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)),
      ((1 : ℕ) : ℕ∞) ≤ g.order := by
    intro g hg
    have hle : Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) ≤
        RingHom.ker (constantCoeff : MvPowerSeries σ O →+* O) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp
    refine nat_le_order fun d hd => ?_
    have hd0 : d = 0 := by
      rw [← Finsupp.degree_eq_zero_iff]
      omega
    subst hd0
    simpa using hle hg
  induction n with
  | zero => intro g _; simp
  | succ n ih =>
    intro g hg
    rw [pow_succ] at hg
    refine Submodule.mul_induction_on hg (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · refine le_trans ?_ le_order_mul
      rw [Nat.cast_add]
      exact add_le_add (ih x hx) (h1 y hy)
    · exact le_trans (le_min hx hy) min_order_le_add

/- English proof (translation)
Establish `hle : I.map (MvPowerSeries.C : O →+* MvPowerSeries σ O) ≤ RingHom.ker (MvPowerSeries.map (σ` using `σ) (Ideal.Quotient.mk I)) := by`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Simplify using `[Ideal.Quotient.eq_zero_iff_mem.2 ha]`. Establish `h` using `congrArg (coeff d) (RingHom.mem_ker.1 (hle hg))`.

Rewrite `h` using `[coeff_map, map_zero]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h`.
-/
private theorem coeff_mem_of_mem_map {O σ : Type} [CommRing O] (I : Ideal O) (g : MvPowerSeries σ O)
    (hg : g ∈ I.map (MvPowerSeries.C : O →+* MvPowerSeries σ O)) (d : σ →₀ ℕ) : coeff d g ∈ I := by
  have hle : I.map (MvPowerSeries.C : O →+* MvPowerSeries σ O) ≤
      RingHom.ker (MvPowerSeries.map (σ := σ) (Ideal.Quotient.mk I)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    simp [Ideal.Quotient.eq_zero_iff_mem.2 ha]
  have h := congrArg (coeff d) (RingHom.mem_ker.1 (hle hg))
  rw [coeff_map, map_zero] at h
  exact Ideal.Quotient.eq_zero_iff_mem.1 h

/- English proof (translation)
Simplify using `only [GlobalTheory.monoVal, Finsupp.prod, X_pow_eq, prod_monomial, Finset.prod_const_one]`. Use `congr 2`. Conclude with `Finsupp.sum_single α`.
-/
private theorem monoVal_X_eq {O σ : Type} [CommRing O] (α : σ →₀ ℕ) :
    GlobalTheory.monoVal (MvPowerSeries.X : σ → MvPowerSeries σ O) α = monomial α 1 := by
  simp only [GlobalTheory.monoVal, Finsupp.prod, X_pow_eq, prod_monomial, Finset.prod_const_one]
  congr 2
  exact Finsupp.sum_single α

/- English proof (translation)
Take `⟨γ, rfl⟩` from `exists_add_of_le h`. Rewrite `hd` using `[map_add]`. Establish `: γ = 0`. Rewrite using `[← Finsupp.degree_eq_zero_iff]`. Use linear arithmetic over natural numbers and integers.

Simplify using `[this]`.
-/
private theorem eq_of_le_of_degree_eq {σ : Type} {α β : σ →₀ ℕ} (h : β ≤ α)
    (hd : β.degree = α.degree) : β = α := by
  obtain ⟨γ, rfl⟩ := exists_add_of_le h
  rw [map_add] at hd
  have : γ = 0 := by
    rw [← Finsupp.degree_eq_zero_iff]
    omega
  simp [this]

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `Λ σ _ _ I a c hc α`. Use `haveI := Fintype.ofFinite σ`. Rewrite `hc`, the goal using `[smul_eq_mul, Ideal.mul_top]`. Take `⟨u, hu, v, hv, huv⟩` from `Submodule.mem_sup.1 hc`. Establish `h0 : MvPowerSeries.coeff α.1 u = 0`.

Use `MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_ (order_of_mem_pow _ u hu))` and prove the remaining obligations. Rewrite using `[α.2]`. Conclude with `Nat.lt_succ_self a` after adjusting the coercions. Establish `h1 : MvPowerSeries.coeff α.1 (u + v) = MvPowerSeries.constantCoeff (c α)`. Rewrite using `[huv, map_sum, Finset.sum_eq_single α]`.

Rewrite using `[monoVal_X_eq, smul_eq_mul, MvPowerSeries.coeff_monomial_mul]`. Simplify using the standard rewrite rules. Introduce `β _ hβ`. Rewrite using `[monoVal_X_eq, smul_eq_mul, MvPowerSeries.coeff_monomial_mul, if_neg]`. Introduce `hle`.

Conclude with `hβ (Subtype.ext (eq_of_le_of_degree_eq hle (β.2.trans α.2.symm)))`. Simplify using the standard rewrite rules. Establish `h2 : MvPowerSeries.constantCoeff (c α) ∈ I`. Rewrite using `[← h1, map_add, h0, zero_add]`. Conclude with `coeff_mem_of_mem_map I v hv _`.

Establish `h3 : c α = (c α - MvPowerSeries.C (MvPowerSeries.constantCoeff (c α))) + MvPowerSeries.C (MvPowerSeries.constantCoeff (c α))` using `by ring`. Rewrite using `[h3]`. Conclude with `Submodule.add_mem_sup (mem_span_X _ (by simp)) (Ideal.mem_map_of_mem _ h2)`.
-/
theorem UpperTheory.V.AlgebraTools.qRegAt_mvPowerSeries :
    ∀ (Λ σ : Type) [CommRing Λ] [Finite σ] (I : Ideal Λ) (a : ℕ),
      QRegAt (MvPowerSeries σ Λ) (MvPowerSeries.X : σ → MvPowerSeries σ Λ) (I.map (MvPowerSeries.C : Λ →+* MvPowerSeries σ Λ)) a := by
  intro Λ σ _ _ I a c hc α
  classical
  haveI := Fintype.ofFinite σ
  rw [smul_eq_mul, Ideal.mul_top] at hc ⊢
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hc
  have h0 : MvPowerSeries.coeff α.1 u = 0 := by
    refine MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_ (order_of_mem_pow _ u hu))
    rw [α.2]
    exact_mod_cast Nat.lt_succ_self a
  have h1 : MvPowerSeries.coeff α.1 (u + v) = MvPowerSeries.constantCoeff (c α) := by
    rw [huv, map_sum, Finset.sum_eq_single α]
    · rw [monoVal_X_eq, smul_eq_mul, MvPowerSeries.coeff_monomial_mul]
      simp
    · intro β _ hβ
      rw [monoVal_X_eq, smul_eq_mul, MvPowerSeries.coeff_monomial_mul, if_neg]
      intro hle
      exact hβ (Subtype.ext (eq_of_le_of_degree_eq hle (β.2.trans α.2.symm)))
    · simp
  have h2 : MvPowerSeries.constantCoeff (c α) ∈ I := by
    rw [← h1, map_add, h0, zero_add]
    exact coeff_mem_of_mem_map I v hv _
  have h3 : c α = (c α - MvPowerSeries.C (MvPowerSeries.constantCoeff (c α))) +
      MvPowerSeries.C (MvPowerSeries.constantCoeff (c α)) := by ring
  rw [h3]
  exact Submodule.add_mem_sup (mem_span_X _ (by simp)) (Ideal.mem_map_of_mem _ h2)
