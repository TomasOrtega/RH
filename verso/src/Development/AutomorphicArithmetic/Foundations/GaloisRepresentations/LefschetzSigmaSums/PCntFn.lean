import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit

open UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Introduce `Γ _ K K' M h hKK' hMn hidx hconj`. Establish `hrep : ∀ (c m : K'), m ∈ M.subgroupOf K' → ∀ y : Γ, (h * ((c * m : K') : Γ) * y ∈ K ↔ h * (c : Γ) * y ∈ K)`. Introduce `c m hm y`. Establish `hm' : (m : Γ) ∈ M` using `Subgroup.mem_subgroupOf.mp hm`. Establish `key : h * ((c * m : K') : Γ) * y = (h * (c : Γ) * m * (h * c)⁻¹) * (h * c * y)`.

Use `push_cast`. Use `group`. Rewrite using `[key]`. Conclude with `Subgroup.mul_mem_cancel_left K (hconj c c.2 m hm')`. Establish `hnz : ∀ y : Γ, cntFn K K' M h y ≠ 0 → ∃ q : K' ⧸ M.subgroupOf K', h * ((Quotient.out q : K') : Γ) * y ∈ K`.

Introduce `y hy`. Unfold `cntFn at hy`. Take `⟨⟨q, hq⟩⟩` from `(Nat.card_ne_zero.mp (Nat.cast_ne_zero.mp hy)).1`. Conclude with `⟨q, hq⟩`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `k hk y`. Prove the components needed by the constructor for the conclusion. Use `haveI : (M.subgroupOf K').Normal := ⟨fun n hn g => by`. Rewrite `hn`, the goal using `[Subgroup.mem_subgroupOf]`. Simplify using `using hMn g g.2 n hn⟩`.

Unfold `cntFn`. Use `congr 1`. Use `Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulRight (((⟨k, hKK' hk⟩ : K') : K' ⧸ M.subgroupOf K'))) ?_)` and prove the remaining obligations. Introduce `q`. Take `⟨m, hm⟩` from `QuotientGroup.mk_out_eq_mul (M.subgroupOf K') (Quotient.out q * ⟨k, hKK' hk⟩)`.

Establish `hq : q * (((⟨k, hKK' hk⟩ : K') : K' ⧸ M.subgroupOf K')) = ((Quotient.out q * ⟨k, hKK' hk⟩ : K') : K' ⧸ M.subgroupOf K')`. Rewrite using `[QuotientGroup.mk_mul, QuotientGroup.out_eq']`. Simplify using `only [Equiv.coe_mulRight]`. Rewrite using `[hq, hm, hrep _ _ m.2]`. Simplify using `only [Subgroup.coe_mul, mul_assoc]`.

Unfold `cntFn`. Simplify using `only [← mul_assoc, Subgroup.mul_mem_cancel_right K hk]`. Introduce `y hy`. Take `⟨q, hq⟩` from `hnz y hy`. Use `⟨(h * ((Quotient.out q : K') : Γ) * y)⁻¹, K.inv_mem hq, _, (Quotient.out q).2, ?_⟩` and prove the remaining obligations.

Use `group`. Use `haveI : (M.subgroupOf K').FiniteIndex := Subgroup.finiteIndex_iff.mpr hidx`. Use `(Set.finite_range (fun q : K' ⧸ M.subgroupOf K' => ((((Quotient.out q : K') : Γ)⁻¹ * h⁻¹ : Γ) : Γ ⧸ K))).subset ?_` and prove the remaining obligations. Introduce `y hy`. Take `⟨q, hq⟩` from `hnz _ hy`.

Use `⟨q, ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [← QuotientGroup.out_eq' y]`. Rewrite using `[QuotientGroup.eq]`. Simplify `hq` using `[mul_assoc]`.
-/
theorem UpperTheory.Gal.LocalSmoothExtension.cntFn_of :
    CntFn := by
  intro Γ _ K K' M h hKK' hMn hidx hconj
  have hrep : ∀ (c m : K'), m ∈ M.subgroupOf K' → ∀ y : Γ,
      (h * ((c * m : K') : Γ) * y ∈ K ↔ h * (c : Γ) * y ∈ K) := by
    intro c m hm y
    have hm' : (m : Γ) ∈ M := Subgroup.mem_subgroupOf.mp hm
    have key : h * ((c * m : K') : Γ) * y = (h * (c : Γ) * m * (h * c)⁻¹) * (h * c * y) := by
      push_cast
      group
    rw [key]
    exact Subgroup.mul_mem_cancel_left K (hconj c c.2 m hm')
  have hnz : ∀ y : Γ, cntFn K K' M h y ≠ 0 →
      ∃ q : K' ⧸ M.subgroupOf K', h * ((Quotient.out q : K') : Γ) * y ∈ K := by
    intro y hy
    unfold cntFn at hy
    obtain ⟨⟨q, hq⟩⟩ := (Nat.card_ne_zero.mp (Nat.cast_ne_zero.mp hy)).1
    exact ⟨q, hq⟩
  refine ⟨?_, ?_, ?_⟩
  · intro k hk y
    constructor
    · haveI : (M.subgroupOf K').Normal := ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        simpa using hMn g g.2 n hn⟩
      unfold cntFn
      congr 1
      refine Nat.card_congr (Equiv.subtypeEquiv
        (Equiv.mulRight (((⟨k, hKK' hk⟩ : K') : K' ⧸ M.subgroupOf K'))) ?_)
      intro q
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (M.subgroupOf K') (Quotient.out q * ⟨k, hKK' hk⟩)
      have hq : q * (((⟨k, hKK' hk⟩ : K') : K' ⧸ M.subgroupOf K')) =
          ((Quotient.out q * ⟨k, hKK' hk⟩ : K') : K' ⧸ M.subgroupOf K') := by
        rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
      simp only [Equiv.coe_mulRight]
      rw [hq, hm, hrep _ _ m.2]
      simp only [Subgroup.coe_mul, mul_assoc]
    · unfold cntFn
      simp only [← mul_assoc, Subgroup.mul_mem_cancel_right K hk]
  · intro y hy
    obtain ⟨q, hq⟩ := hnz y hy
    refine ⟨(h * ((Quotient.out q : K') : Γ) * y)⁻¹, K.inv_mem hq, _, (Quotient.out q).2, ?_⟩
    group
  · haveI : (M.subgroupOf K').FiniteIndex := Subgroup.finiteIndex_iff.mpr hidx
    refine (Set.finite_range (fun q : K' ⧸ M.subgroupOf K' =>
      ((((Quotient.out q : K') : Γ)⁻¹ * h⁻¹ : Γ) : Γ ⧸ K))).subset ?_
    intro y hy
    obtain ⟨q, hq⟩ := hnz _ hy
    refine ⟨q, ?_⟩
    conv_rhs => rw [← QuotientGroup.out_eq' y]
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using hq
