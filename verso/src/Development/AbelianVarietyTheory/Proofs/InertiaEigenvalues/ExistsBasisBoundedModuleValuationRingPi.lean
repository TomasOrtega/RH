import Mathlib
open IsDedekindDomain NumberField

namespace GlobalTheory

/- English proof (translation)
Take `⟨D, hD, hDM⟩` from `hbd`. Use `set A : ValuationSubring F := p.valuationSubringAtPrime F with hA`. Use `haveI : IsDiscreteValuationRing A := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 F) p.ne_bot _`. Establish `memA : ∀ a : F, a ∈ A ↔ p.valuation F a ≤ 1`. Introduce `a`.

Rewrite using `[hA, HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring, Valuation.mem_valuationSubring_iff]`. Set `M' : Submodule A (Fin d → F)` to `{ carrier := M add_mem' := fun {x y} hx hy => hadd x hx y hy zero_mem' := h0 smul_mem' := fun c x hx => by`. Establish `: c • x = (c : F) • x` using `rfl`. Rewrite using `[this]`. Conclude with `hsmul _ ((memA _).1 c.2) x hx }`.

Set `e : Fin d → Fin d → F` to `fun i => D⁻¹ • Pi.single i 1`. Establish `heF : LinearIndependent F e`. Establish `h1` using `(Pi.basisFun F (Fin d)).linearIndependent.units_smul (fun _ => Units.mk0 D⁻¹ (inv_ne_zero hD))`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`.

Simplify using `[e, Pi.basisFun_apply]`. Establish `heA : LinearIndependent A e` using `(LinearIndependent.iff_fractionRing A F).2 heF`. Establish `hle : M' ≤ Submodule.span A (Set.range e)`. Introduce `x hx`. Establish `hx' : x = ∑ i, (D * x i) • e i`.

Use extensionality with `j`. Simplify using `[e, Finset.sum_apply, Pi.single_apply]`. Rewrite using `[mul_comm D, mul_assoc, mul_inv_cancel₀ hD, mul_one]`. Rewrite using `[hx']`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Establish `hc : D * x i ∈ A` using `(memA _).2 (hDM x hx i)`. Establish `: (D * x i) • e i = (⟨D * x i, hc⟩ : A) • e i` using `rfl`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Take `⟨n, bas⟩` from `Submodule.basisOfPidOfLE hle (Module.Basis.span heA)`.

Use `⟨n, fun k => (bas k : Fin d → F), fun k => (bas k).2, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Use `⟨fun k => (bas.repr ⟨x, hx⟩ k : F), fun k => (memA _).1 (bas.repr ⟨x, hx⟩ k).2, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun y : M' => (y : Fin d → F)) (bas.sum_repr ⟨x, hx⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h`.

Conclude with `h.symm`. Establish `h1 : LinearIndependent A (M'.subtype ∘ bas)` using `bas.linearIndependent.map' M'.subtype (Submodule.ker_subtype M')`. Conclude with `(LinearIndependent.iff_fractionRing A F).1 h1`.
-/
theorem locBasis_of_bounded {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    (d : ℕ) (M : Set (Fin d → F)) (h0 : (0 : Fin d → F) ∈ M)
    (hadd : ∀ x ∈ M, ∀ y ∈ M, x + y ∈ M)
    (hsmul : ∀ a : F, p.valuation F a ≤ 1 → ∀ x ∈ M, a • x ∈ M)
    (hstd : ∀ i, Pi.single i 1 ∈ M)
    (hbd : ∃ D : F, D ≠ 0 ∧ ∀ x ∈ M, ∀ i, p.valuation F (D * x i) ≤ 1) :
    ∃ (m : ℕ) (b : Fin m → Fin d → F), (∀ k, b k ∈ M) ∧
      (∀ x ∈ M, ∃ a : Fin m → F, (∀ k, p.valuation F (a k) ≤ 1) ∧ x = ∑ k, a k • b k) ∧
      LinearIndependent F b := by
  obtain ⟨D, hD, hDM⟩ := hbd
  set A : ValuationSubring F := p.valuationSubringAtPrime F with hA
  haveI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 F) p.ne_bot _
  have memA : ∀ a : F, a ∈ A ↔ p.valuation F a ≤ 1 := by
    intro a
    rw [hA, HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff]
  let M' : Submodule A (Fin d → F) :=
    { carrier := M
      add_mem' := fun {x y} hx hy => hadd x hx y hy
      zero_mem' := h0
      smul_mem' := fun c x hx => by
        have : c • x = (c : F) • x := rfl
        rw [this]
        exact hsmul _ ((memA _).1 c.2) x hx }
  let e : Fin d → Fin d → F := fun i => D⁻¹ • Pi.single i 1
  have heF : LinearIndependent F e := by
    have h1 := (Pi.basisFun F (Fin d)).linearIndependent.units_smul
      (fun _ => Units.mk0 D⁻¹ (inv_ne_zero hD))
    convert h1 using 1
    ext i j
    simp [e, Pi.basisFun_apply]
  have heA : LinearIndependent A e := (LinearIndependent.iff_fractionRing A F).2 heF
  have hle : M' ≤ Submodule.span A (Set.range e) := by
    intro x hx
    have hx' : x = ∑ i, (D * x i) • e i := by
      ext j
      simp [e, Finset.sum_apply, Pi.single_apply]
      rw [mul_comm D, mul_assoc, mul_inv_cancel₀ hD, mul_one]
    rw [hx']
    refine Submodule.sum_mem _ fun i _ => ?_
    have hc : D * x i ∈ A := (memA _).2 (hDM x hx i)
    have : (D * x i) • e i = (⟨D * x i, hc⟩ : A) • e i := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨n, bas⟩ := Submodule.basisOfPidOfLE hle (Module.Basis.span heA)
  refine ⟨n, fun k => (bas k : Fin d → F), fun k => (bas k).2, ?_, ?_⟩
  · intro x hx
    refine ⟨fun k => (bas.repr ⟨x, hx⟩ k : F), fun k => (memA _).1 (bas.repr ⟨x, hx⟩ k).2, ?_⟩
    have h := congrArg (fun y : M' => (y : Fin d → F)) (bas.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  · have h1 : LinearIndependent A (M'.subtype ∘ bas) :=
      bas.linearIndependent.map' M'.subtype (Submodule.ker_subtype M')
    exact (LinearIndependent.iff_fractionRing A F).1 h1

end GlobalTheory
