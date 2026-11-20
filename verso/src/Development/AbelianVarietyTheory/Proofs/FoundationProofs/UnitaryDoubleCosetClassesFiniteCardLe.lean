import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetSelfDualClassesRootDiscr
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPointStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

/- English proof (translation)
Introduce `c`. Take `⟨h, k, hh, hk, e⟩` from `DoubleCoset.mk_out_eq_mul H K c.out`. Use `⟨(DoubleCoset.mk H K c.out, QuotientGroup.mk (⟨k⁻¹, K.inv_mem hk⟩ : K)), ?_⟩` and prove the remaining obligations. Take `⟨j, hj⟩` from `QuotientGroup.mk_out_eq_mul (J.subgroupOf K) (⟨k⁻¹, K.inv_mem hk⟩ : K)`. Establish `hjJ : ((j : K) : G) ∈ J` using `Subgroup.mem_subgroupOf.mp j.2`.

Simplify using `only`. Rewrite using `[hj, e]`. Use `conv_rhs => rw [← DoubleCoset.out_eq' H J c]`. Rewrite using `[eq_comm, DoubleCoset.eq]`. Use `⟨h, hh, _, hjJ, ?_⟩` and prove the remaining obligations.

Simplify using `[mul_assoc]`.
-/
theorem doubleCoset_surj_of_le {G : Type*} [Group G] (H K J : Subgroup G) :
    Function.Surjective (fun p : DoubleCoset.Quotient (H : Set G) (K : Set G) × (K ⧸ J.subgroupOf K) =>
      DoubleCoset.mk H J (p.1.out * (p.2.out : G))) := by
  intro c
  obtain ⟨h, k, hh, hk, e⟩ := DoubleCoset.mk_out_eq_mul H K c.out
  refine ⟨(DoubleCoset.mk H K c.out, QuotientGroup.mk (⟨k⁻¹, K.inv_mem hk⟩ : K)), ?_⟩
  obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf K) (⟨k⁻¹, K.inv_mem hk⟩ : K)
  have hjJ : ((j : K) : G) ∈ J := Subgroup.mem_subgroupOf.mp j.2
  simp only
  rw [hj, e]
  conv_rhs => rw [← DoubleCoset.out_eq' H J c]
  rw [eq_comm, DoubleCoset.eq]
  refine ⟨h, hh, _, hjJ, ?_⟩
  simp [mul_assoc]

/- English proof (translation)
Establish `: Finite (K ⧸ J.subgroupOf K)` using `Nat.finite_of_card_ne_zero hJ`. Use `⟨Finite.of_surjective _ (doubleCoset_surj_of_le H K J), ?_⟩` and prove the remaining obligations. Use `Nat.card_le_card_of_surjective _ (doubleCoset_surj_of_le H K J)` as an intermediate fact. Rewrite `this` using `[Nat.card_prod]`. Then use the resulting hypothesis.
-/
theorem doubleCoset_card_le {G : Type*} [Group G] (H K J : Subgroup G)
    [Finite (DoubleCoset.Quotient (H : Set G) (K : Set G))] (hJ : J.relIndex K ≠ 0) :
    Finite (DoubleCoset.Quotient (H : Set G) (J : Set G)) ∧
      Nat.card (DoubleCoset.Quotient (H : Set G) (J : Set G)) ≤
        Nat.card (DoubleCoset.Quotient (H : Set G) (K : Set G)) * J.relIndex K := by
  have : Finite (K ⧸ J.subgroupOf K) := Nat.finite_of_card_ne_zero hJ
  refine ⟨Finite.of_surjective _ (doubleCoset_surj_of_le H K J), ?_⟩
  have := Nat.card_le_card_of_surjective _ (doubleCoset_surj_of_le H K J)
  rwa [Nat.card_prod] at this

/- English proof (translation)
Introduce `D N`. Establish `hcm : IsCMField D.host.E` using `D.host.isCMField_hostE`. Establish `hconj : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x`. Introduce `x`. Apply `D.host.φ₀.injective` to reduce the goal to its premises.

Establish `h1` using `IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x`. Establish `h2` using `D.host.conjE_apply D.host.φ₀ x`. Conclude with `h1.trans h2.symm`. Establish `hfr : Module.finrank ℚ D.host.E = 2 * fF D`. Rewrite using `[D.host.finrank_cmField, fF, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨R, hR, hcov⟩` from `GlobalTheory.exists_finset_selfDual_classes_rootDiscr D.host.E N`. Take `⟨hrat, -, hex, -, -⟩` from `GlobalTheory.NormSum.mem_ratG_intG D N`. Take `⟨Lt, hSD, -, hLt, hmv, -⟩` from `GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N`. Establish `key : ∀ g : GA D N, ∃ L₀ ∈ R, ∃ h ∈ ratG D N, Lt (h⁻¹ * g) = L₀`.

Introduce `g`. Take `⟨h1, h2, h3⟩` from `(hSD g).2`. Take `⟨L₀, hL₀, γ, hγ, hx⟩` from `hcov (Lt g) h1 h2 (by`. Introduce `y`. Rewrite using `[h3 y]`.

Use `forall_congr' fun x => forall_congr' fun _ => ?_` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩`. Establish `hz' : (z : D.host.E) = ∑ i, IsCMField.complexConj D.host.E (x i) * y i` using `hz`. Rewrite using `[← hz']`.

Conclude with `z.isIntegral_coe`. Introduce `hz`. Conclude with `⟨⟨_, hz⟩, rfl⟩)`. Establish `hm : γ.map (IsCMField.complexConj D.host.E) = γ.map D.host.conj`. Use extensionality with `i j`.

Simplify using `only [Matrix.map_apply, hconj]`. Rewrite `hγ` using `[hm]`. Take `⟨h, hh⟩` from `hex γ hγ`. Use `⟨L₀, hL₀, h, (hrat h).2 ⟨γ, hh⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `x`.

Rewrite using `[hmv h (h⁻¹ * g) γ hh x, mul_inv_cancel_left, hx]`. Use `choose L₀ hL₀ h hh hL using key`. Set `f : Cls D N (intG D N) → R` to `fun c => ⟨L₀ c.out, hL₀ _⟩`. Establish `hf : Function.Injective f`. Introduce `c c' e`.

Establish `e' : L₀ c.out = L₀ c'.out` using `congrArg Subtype.val e`. Rewrite `e'` using `[← hL, ← hL, hLt]`. Rewrite using `[← DoubleCoset.out_eq' _ _ c, ← DoubleCoset.out_eq' _ _ c', DoubleCoset.eq]`. Use `⟨h c'.out * (h c.out)⁻¹, Subgroup.mul_mem _ (hh _) (Subgroup.inv_mem _ (hh _)), _, e', ?_⟩` and prove the remaining obligations. Use `group`.

Establish `hfin : Finite (Cls D N (intG D N))` using `Finite.of_injective f hf`. Use `⟨hfin, ?_, fun J _ hJ => doubleCoset_card_le _ _ J hJ⟩` and prove the remaining obligations. Establish `hc : Nat.card (Cls D N (intG D N)) ≤ R.card`. Use `Nat.card_le_card_of_injective f hf` as an intermediate fact. Simplify using `using this`.

Use `le_trans (by exact_mod_cast hc) (hR.trans (le_of_eq ?_))` and prove the remaining obligations. Establish `hrd : |(discr D.host.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ)) = D.host.rdE` using `rfl`. Rewrite using `[hrd, hfr]`. Establish `: 3 * (2 * fF D) * N ^ 2 = 6 * fF D * N ^ 2` using `by ring`. Rewrite using `[this]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cls_finite_card_le : ∀ (D : D7) (N : ℕ), Finite (Cls D N (intG D N)) ∧ (Nat.card (Cls D N (intG D N)) : ℝ) ≤ (12 * (fF D : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2) ^ (6 * fF D * N ^ 2) ∧ ∀ J : Subgroup (GA D N), J ≤ intG D N → J.relIndex (intG D N) ≠ 0 → Finite (Cls D N J) ∧ Nat.card (Cls D N J) ≤ Nat.card (Cls D N (intG D N)) * J.relIndex (intG D N) := by
  intro D N
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  have hconj : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x := by
    intro x
    apply D.host.φ₀.injective
    have h1 := IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x
    have h2 := D.host.conjE_apply D.host.φ₀ x
    exact h1.trans h2.symm
  have hfr : Module.finrank ℚ D.host.E = 2 * fF D := by
    rw [D.host.finrank_cmField, fF, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
    ring
  obtain ⟨R, hR, hcov⟩ := GlobalTheory.exists_finset_selfDual_classes_rootDiscr D.host.E N
  obtain ⟨hrat, -, hex, -, -⟩ := GlobalTheory.NormSum.mem_ratG_intG D N
  obtain ⟨Lt, hSD, -, hLt, hmv, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
  have key : ∀ g : GA D N, ∃ L₀ ∈ R, ∃ h ∈ ratG D N, Lt (h⁻¹ * g) = L₀ := by
    intro g
    obtain ⟨h1, h2, h3⟩ := (hSD g).2
    obtain ⟨L₀, hL₀, γ, hγ, hx⟩ := hcov (Lt g) h1 h2 (by
      intro y
      rw [h3 y]
      refine forall_congr' fun x => forall_congr' fun _ => ?_
      constructor
      · rintro ⟨z, hz⟩
        have hz' : (z : D.host.E) = ∑ i, IsCMField.complexConj D.host.E (x i) * y i := hz
        rw [← hz']
        exact z.isIntegral_coe
      · intro hz
        exact ⟨⟨_, hz⟩, rfl⟩)
    have hm : γ.map (IsCMField.complexConj D.host.E) = γ.map D.host.conj := by
      ext i j
      simp only [Matrix.map_apply, hconj]
    rw [hm] at hγ
    obtain ⟨h, hh⟩ := hex γ hγ
    refine ⟨L₀, hL₀, h, (hrat h).2 ⟨γ, hh⟩, ?_⟩
    ext x
    rw [hmv h (h⁻¹ * g) γ hh x, mul_inv_cancel_left, hx]
  choose L₀ hL₀ h hh hL using key
  let f : Cls D N (intG D N) → R := fun c => ⟨L₀ c.out, hL₀ _⟩
  have hf : Function.Injective f := by
    intro c c' e
    have e' : L₀ c.out = L₀ c'.out := congrArg Subtype.val e
    rw [← hL, ← hL, hLt] at e'
    rw [← DoubleCoset.out_eq' _ _ c, ← DoubleCoset.out_eq' _ _ c', DoubleCoset.eq]
    refine ⟨h c'.out * (h c.out)⁻¹, Subgroup.mul_mem _ (hh _) (Subgroup.inv_mem _ (hh _)), _, e', ?_⟩
    group
  have hfin : Finite (Cls D N (intG D N)) := Finite.of_injective f hf
  refine ⟨hfin, ?_, fun J _ hJ => doubleCoset_card_le _ _ J hJ⟩
  have hc : Nat.card (Cls D N (intG D N)) ≤ R.card := by
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  refine le_trans (by exact_mod_cast hc) (hR.trans (le_of_eq ?_))
  have hrd : |(discr D.host.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ)) = D.host.rdE := rfl
  rw [hrd, hfr]
  have : 3 * (2 * fF D) * N ^ 2 = 6 * fF D * N ^ 2 := by ring
  rw [this]
  congr 1
  push_cast
  ring

end GlobalTheory.NormSum
