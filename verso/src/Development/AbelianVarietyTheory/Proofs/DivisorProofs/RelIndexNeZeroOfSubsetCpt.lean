import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise

namespace GlobalTheory.LocFinU

/- English proof (translation)
Take `⟨s, hs⟩` from `hΩ.elim_finite_subcover (fun g : Ω => (g : G) • (U : Set G)) (fun g => hU.smul _) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, ⟨1, U.one_mem, mul_one x⟩⟩)`. Establish `hmem : ∀ q : P ⧸ U.subgroupOf P, ∃ i : s, ((Quotient.out q : P) : G) ∈ ((i : Ω) : G) • (U : Set G)`. Introduce `q`. Use `hs (hP (Quotient.out q).2)` as an intermediate fact. Simplify using `only [Set.mem_iUnion] at this`.

Take `⟨i, hi, h⟩` from `this`. Conclude with `⟨⟨i, hi⟩, h⟩`. Use `choose f hf using hmem`. Establish `hinj : Function.Injective f`. Introduce `q q' h`.

Establish `h1` using `hf q`. Establish `h2` using `hf q'`. Rewrite `h1` using `[h]`. Take `⟨u, hu, hu'⟩` from `h1`. Take `⟨u', hu2, hu2'⟩` from `h2`.

Rewrite using `[← Quotient.out_eq q, ← Quotient.out_eq q']`. Express the relevant statement in the definitionally equal form `QuotientGroup.mk _ = QuotientGroup.mk _`. Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv]`. Rewrite using `[← hu', ← hu2']`.

Simplify using `only [smul_eq_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]`. Conclude with `U.mul_mem (U.inv_mem hu) hu2`. Use `haveI : Finite (P ⧸ U.subgroupOf P) := Finite.of_injective f hinj`. Conclude with `Subgroup.index_ne_zero_of_finite`.
-/
theorem relIndex_ne_zero_of_subset_cpt {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U P : Subgroup G) (hU : IsOpen (U : Set G)) (Ω : Set G) (hΩ : IsCompact Ω) (hP : (P : Set G) ⊆ Ω) :
    U.relIndex P ≠ 0 := by
  obtain ⟨s, hs⟩ := hΩ.elim_finite_subcover (fun g : Ω => (g : G) • (U : Set G)) (fun g => hU.smul _)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, ⟨1, U.one_mem, mul_one x⟩⟩)
  have hmem : ∀ q : P ⧸ U.subgroupOf P, ∃ i : s, ((Quotient.out q : P) : G) ∈ ((i : Ω) : G) • (U : Set G) := by
    intro q
    have := hs (hP (Quotient.out q).2)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, h⟩ := this
    exact ⟨⟨i, hi⟩, h⟩
  choose f hf using hmem
  have hinj : Function.Injective f := by
    intro q q' h
    have h1 := hf q
    have h2 := hf q'
    rw [h] at h1
    obtain ⟨u, hu, hu'⟩ := h1
    obtain ⟨u', hu2, hu2'⟩ := h2
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    change QuotientGroup.mk _ = QuotientGroup.mk _
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hu', ← hu2']
    simp only [smul_eq_mul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    exact U.mul_mem (U.inv_mem hu) hu2
  haveI : Finite (P ⧸ U.subgroupOf P) := Finite.of_injective f hinj
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.LocFinU

namespace GlobalTheory.LocFinU

/- English proof (translation)
Unfold `cj`. Use `split_ifs with h`. Conclude with `h.choose_spec.1`. Conclude with `continuous_id`.
-/
theorem continuous_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) : Continuous (cj w) := by
  unfold cj
  split_ifs with h
  · exact h.choose_spec.1
  · exact continuous_id

/- English proof (translation)
Unfold `UL`. Use `split_ifs`. Conclude with `isClosed_univ`. Establish `hc : Continuous fun g : GLw n w => cT (cj w) (g : Matrix (Fin n) (Fin n) _) * 1 * (g : Matrix (Fin n) (Fin n) _)` using `((Units.continuous_val.matrix_map (continuous_cj w)).matrix_transpose.matrix_mul continuous_const).matrix_mul Units.continuous_val`. Conclude with `isClosed_eq hc continuous_const`.
-/
theorem isClosed_UL {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) :
    IsClosed (UL n w : Set (GLw n w)) := by
  unfold UL
  split_ifs
  · exact isClosed_univ
  · have hc : Continuous fun g : GLw n w => cT (cj w) (g : Matrix (Fin n) (Fin n) _) * 1 * (g : Matrix (Fin n) (Fin n) _) :=
      ((Units.continuous_val.matrix_map (continuous_cj w)).matrix_transpose.matrix_mul continuous_const).matrix_mul
        Units.continuous_val
    exact isClosed_eq hc continuous_const

/- English proof (translation)
Rewrite using `[Subtype.isCompact_iff]`. Establish `hK : IsCompact (GlobalTheory.LFun.KGL w n : Set (GLw n w))` using `GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w)`. Establish `: (Subtype.val '' (KL n w : Set (UL n w))) = (GlobalTheory.LFun.KGL w n : Set (GLw n w)) ∩ (UL n w : Set (GLw n w))`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨hx, x.2⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨⟨g, h2⟩, h1, rfl⟩`. Rewrite using `[this]`.

Conclude with `hK.inter_right (isClosed_UL n w)`.
-/
theorem isCompact_KL {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) :
    IsCompact (KL n w : Set (UL n w)) := by
  rw [Subtype.isCompact_iff]
  have hK : IsCompact (GlobalTheory.LFun.KGL w n : Set (GLw n w)) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w)
  have : (Subtype.val '' (KL n w : Set (UL n w))) = (GlobalTheory.LFun.KGL w n : Set (GLw n w)) ∩ (UL n w : Set (GLw n w)) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨g, h2⟩, h1, rfl⟩
  rw [this]
  exact hK.inter_right (isClosed_UL n w)

end GlobalTheory.LocFinU

namespace GlobalTheory.LocFinU

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Subgroup.closure_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `one`. Use `⟨T.one_mem, ?_⟩` and prove the remaining obligations.

Rewrite using `[Subgroup.zpowers_one_eq_bot, Subgroup.coe_bot, closure_singleton]`. Conclude with `isCompact_singleton`. Consider the case `mul x y _ _ hx hy`. Use `⟨T.mul_mem hx.1 hy.1, ?_⟩` and prove the remaining obligations. Establish `hxy : Commute x y` using `hc x hx.1 y hy.1`.

Establish `hcp : IsCompact (closure (Subgroup.zpowers x : Set G) * closure (Subgroup.zpowers y : Set G))` using `hx.2.mul hy.2`. Use `hcp.of_isClosed_subset isClosed_closure (closure_minimal ?_ hcp.isClosed)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨x ^ k, subset_closure ⟨k, rfl⟩, y ^ k, subset_closure ⟨k, rfl⟩, (hxy.mul_zpow k).symm⟩`. Consider the case `inv x _ hx`.

Use `⟨T.inv_mem hx.1, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.zpowers_inv]`. Conclude with `hx.2`.
-/
theorem cptPart_subset_of_comm {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (T : Subgroup G) (hc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) :
    (cptPart T : Set G) ⊆ {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))} := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one =>
    refine ⟨T.one_mem, ?_⟩
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.coe_bot, closure_singleton]
    exact isCompact_singleton
  | mul x y _ _ hx hy =>
    refine ⟨T.mul_mem hx.1 hy.1, ?_⟩
    have hxy : Commute x y := hc x hx.1 y hy.1
    have hcp : IsCompact (closure (Subgroup.zpowers x : Set G) * closure (Subgroup.zpowers y : Set G)) :=
      hx.2.mul hy.2
    refine hcp.of_isClosed_subset isClosed_closure (closure_minimal ?_ hcp.isClosed)
    rintro _ ⟨k, rfl⟩
    exact ⟨x ^ k, subset_closure ⟨k, rfl⟩, y ^ k, subset_closure ⟨k, rfl⟩, (hxy.mul_zpow k).symm⟩
  | inv x _ hx =>
    refine ⟨T.inv_mem hx.1, ?_⟩
    rw [Subgroup.zpowers_inv]
    exact hx.2

end GlobalTheory.LocFinU
