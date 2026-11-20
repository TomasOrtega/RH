import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsGenericProjClosureDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsDvrConeDimTrdeg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairBundleTrdeg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensSpan
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace GenericProjClosureDim

variable {R : Type*} [CommRing R] {L : Type*} [Field L] [Algebra R L] {K : Type*} [DecidableEq K]
  {ι : K → Type*}

def tWeight (K : Type*) [DecidableEq K] : K → K → ℕ := fun k => Pi.single k 1

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on' with`. Consider the case `monomial d a`. Establish `h1 : IsWeightedHomogeneous (tWeight K) (pointConeMap R z (monomial d a)) (Finsupp.weight (blockWeight ι) d)`. Rewrite using `[pointConeMap, aeval_monomial, MvPolynomial.algebraMap_apply, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum]`. Use `IsWeightedHomogeneous.C_mul ?_ _` and prove the remaining obligations.

Use `IsWeightedHomogeneous.prod _ _ _ fun p _ => ?_` and prove the remaining obligations. Conclude with `((isWeightedHomogeneous_X (R := L) (tWeight K) p.1).C_mul (z p)).pow (d p)`. Establish `h2 : IsWeightedHomogeneous (blockWeight ι) (monomial d a : MRing ι R) (Finsupp.weight (blockWeight ι) d)` using `isWeightedHomogeneous_monomial _ _ _ rfl`. Distinguish the cases in `h : b = Finsupp.weight (blockWeight ι) d`. Substitute `h` using the available equality.

Rewrite using `[h1.weightedHomogeneousComponent_same, h2.weightedHomogeneousComponent_same]`. Rewrite using `[h1.weightedHomogeneousComponent_ne _ h, h2.weightedHomogeneousComponent_ne _ h, map_zero]`. Consider the case `add f g hf hg => simp only [map_add, hf, hg]`.
-/
theorem coneMap_component (z : (Σ k, ι k) → L) (b : K → ℕ) (f : MRing ι R) :
    weightedHomogeneousComponent (tWeight K) b (pointConeMap R z f) =
      pointConeMap R z (weightedHomogeneousComponent (blockWeight ι) b f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial d a =>
    have h1 : IsWeightedHomogeneous (tWeight K) (pointConeMap R z (monomial d a))
        (Finsupp.weight (blockWeight ι) d) := by
      rw [pointConeMap, aeval_monomial, MvPolynomial.algebraMap_apply, Finsupp.weight_apply, Finsupp.prod,
        Finsupp.sum]
      refine IsWeightedHomogeneous.C_mul ?_ _
      refine IsWeightedHomogeneous.prod _ _ _ fun p _ => ?_
      exact ((isWeightedHomogeneous_X (R := L) (tWeight K) p.1).C_mul (z p)).pow (d p)
    have h2 : IsWeightedHomogeneous (blockWeight ι) (monomial d a : MRing ι R)
        (Finsupp.weight (blockWeight ι) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    by_cases h : b = Finsupp.weight (blockWeight ι) d
    · subst h
      rw [h1.weightedHomogeneousComponent_same, h2.weightedHomogeneousComponent_same]
    · rw [h1.weightedHomogeneousComponent_ne _ h, h2.weightedHomogeneousComponent_ne _ h, map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]

/- English proof (translation)
Use `⟨RingHom.ker_isPrime _, ?_, ?_⟩` and prove the remaining obligations. Introduce `f hf b`. Rewrite `hf`, the goal using `[pointIdeal, RingHom.mem_ker]`. Use `coneMap_component (R := R) z b f` as an intermediate fact. Rewrite `this` using `[hf, map_zero]`.

Conclude with `this.symm`. Introduce `k`. Take `⟨i, hi⟩` from `hz k`. Use `⟨i, ?_⟩` and prove the remaining obligations. Rewrite using `[pointIdeal, RingHom.mem_ker]`.

Express the relevant statement in the definitionally equal form `pointConeMap R z (X ⟨k, i⟩) ≠ 0`. Rewrite using `[pointConeMap, aeval_X]`. Conclude with `mul_ne_zero (by simpa using hi) (X_ne_zero _)`.
-/
theorem isMultiProjPrime_pointIdeal (z : (Σ k, ι k) → L) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    IsMultiProjPrime (pointIdeal R z) := by
  refine ⟨RingHom.ker_isPrime _, ?_, ?_⟩
  · intro f hf b
    rw [pointIdeal, RingHom.mem_ker] at hf ⊢
    have := coneMap_component (R := R) z b f
    rw [hf, map_zero] at this
    exact this.symm
  · intro k
    obtain ⟨i, hi⟩ := hz k
    refine ⟨i, ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    change pointConeMap R z (X ⟨k, i⟩) ≠ 0
    rw [pointConeMap, aeval_X]
    exact mul_ne_zero (by simpa using hi) (X_ne_zero _)

/- English proof (translation)
Use `by_contra! h0`. Establish `hall : ∀ l, ψ l = 0`. Introduce `l`. Use `e.ext fun i => ?_` and prove the remaining obligations. Use `Fintype.linearIndependent_iff.1 ht (fun i => ψ l (e i)) (by rw [← h0 l]; exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm])` as an intermediate fact.

Simplify using `using this i`. Establish `htop : (⊤ : Submodule Ω (Module.Dual Ω E)) = ⊥`. Rewrite using `[← hψ, Submodule.span_eq_bot]`. Introduce and unpack `_ ⟨l, rfl⟩`. Conclude with `hall l`.

Establish `hc : e.coord ⟨0, hN⟩ = 0`. Establish `: e.coord ⟨0, hN⟩ ∈ (⊥ : Submodule Ω (Module.Dual Ω E))` using `htop ▸ Submodule.mem_top`. Simplify using `using this`. Use `congrArg (fun f => f (e ⟨0, hN⟩)) hc` as an intermediate fact. Simplify using `at this`.
-/
theorem exists_ne_zero_of_span {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    {Φ : Type*} [Field Φ] [Algebra Ω Φ] {N P : ℕ} (hN : 0 < N) (e : Module.Basis (Fin N) Ω E)
    {t : Fin N → Φ} (ht : LinearIndependent Ω t) (ψ : Fin P → Module.Dual Ω E)
    (hψ : Submodule.span Ω (Set.range ψ) = ⊤) :
    ∃ l, ∑ i, t i * algebraMap Ω Φ (ψ l (e i)) ≠ 0 := by
  by_contra! h0
  have hall : ∀ l, ψ l = 0 := by
    intro l
    refine e.ext fun i => ?_
    have := Fintype.linearIndependent_iff.1 ht (fun i => ψ l (e i))
      (by rw [← h0 l]; exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm])
    simpa using this i
  have htop : (⊤ : Submodule Ω (Module.Dual Ω E)) = ⊥ := by
    rw [← hψ, Submodule.span_eq_bot]
    rintro _ ⟨l, rfl⟩
    exact hall l
  have hc : e.coord ⟨0, hN⟩ = 0 := by
    have : e.coord ⟨0, hN⟩ ∈ (⊥ : Submodule Ω (Module.Dual Ω E)) := htop ▸ Submodule.mem_top
    simpa using this
  have := congrArg (fun f => f (e ⟨0, hN⟩)) hc
  simp at this

end GenericProjClosureDim

open GenericProjClosureDim in

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht`. Establish `hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0` using `fun k => by`. Take `⟨j, hj⟩` from `hV.multiProj.relevant k`. Use `⟨j, fun h0 => hj ?_⟩` and prove the remaining obligations. Rewrite using `[pointIdeal, RingHom.mem_ker]`.

Simplify using `[pointConeMap, h0]`. Use `choose c hc using hne`. Establish `hyc : segreVec y c ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => hc k`. Establish `hli` using `ht.linearIndependent`. Establish `hz : ∀ o, ∃ i, pairProjCoord y e φ φ' t ⟨o, i⟩ ≠ 0`.

Introduce and unpack `(_ | _ | k)`. Conclude with `exists_ne_zero_of_span hN e hli φ' (TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc)`. Conclude with `exists_ne_zero_of_span hN e hli φ (TwistedDualGensSpan.proof O Ω K ι y N E B a₀ M φ hφ c hyc)`. Conclude with `⟨c k, fun h0 => hc k ((FaithfulSMul.algebraMap_injective Ω Φ) (by simpa [pairProjCoord, projCoord] using h0))⟩`. Establish `hP` using `isMultiProjPrime_pointIdeal (R := O) _ hz`.

Establish `hnt : (pointIdeal O (pairProjCoord y e φ φ' t)).comap (C : O →+* _) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `a ha`. Rewrite `ha` using `[Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, C_eq_zero, IsScalarTower.algebraMap_apply O Ω Φ, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective Ω Φ)]`. Establish `hy : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O)`.

Rewrite using `[Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha, map_zero]`. Rewrite `hy` using `[hV.noTorsion]`. Simplify using `using hy`. Use `⟨hP, hnt, ?_⟩` and prove the remaining obligations. Establish `hdy` using `hDim O K ι (pointIdeal O y) hV.multiProj hV.noTorsion`.

Rewrite `hdy` using `[hV.dim]`. Establish `hty : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = ((d + Fintype.card K : ℕ) : Cardinal)`. Establish `h1 : (((d + Fintype.card K : ℕ) : ℕ∞) + 1) = (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1`. Use `WithBot.coe_injective hdy` as an intermediate fact. Rewrite using `[← this]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `(Cardinal.toENat_eq_natCast.1 (WithTop.add_right_cancel ENat.one_ne_top h1).symm)`. Rewrite using `[hDim _ _ _ _ hP hnt, hTr O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht, hty, ← Nat.cast_add, Cardinal.toENat_nat, Fintype.card_option, Fintype.card_option, show d + (N - 1) + 1 + (Fintype.card K + 1 + 1) = d + Fintype.card K + (N + 1) + 1 by omega]`. Use `norm_cast`.
-/
theorem GenericProjClosureDim.proof (hDim : DvrConeDimTrdeg.Statement) (hTr : PairBundleTrdeg.Statement) :
    GenericProjClosureDim.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht

  have hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0 := fun k => by
    obtain ⟨j, hj⟩ := hV.multiProj.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hli := ht.linearIndependent

  have hz : ∀ o, ∃ i, pairProjCoord y e φ φ' t ⟨o, i⟩ ≠ 0 := by
    rintro (_ | _ | k)
    · exact exists_ne_zero_of_span hN e hli φ'
        (TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc)
    · exact exists_ne_zero_of_span hN e hli φ
        (TwistedDualGensSpan.proof O Ω K ι y N E B a₀ M φ hφ c hyc)
    · exact ⟨c k, fun h0 => hc k ((FaithfulSMul.algebraMap_injective Ω Φ) (by simpa [pairProjCoord, projCoord] using h0))⟩
  have hP := isMultiProjPrime_pointIdeal (R := O) _ hz

  have hnt : (pointIdeal O (pairProjCoord y e φ φ' t)).comap (C : O →+* _) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply,
      C_eq_zero, IsScalarTower.algebraMap_apply O Ω Φ, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective Ω Φ)] at ha
    have hy : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha,
        map_zero]
    rw [hV.noTorsion] at hy
    simpa using hy
  refine ⟨hP, hnt, ?_⟩

  have hdy := hDim O K ι (pointIdeal O y) hV.multiProj hV.noTorsion
  rw [hV.dim] at hdy
  have hty : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = ((d + Fintype.card K : ℕ) : Cardinal) := by
    have h1 : (((d + Fintype.card K : ℕ) : ℕ∞) + 1) =
        (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1 := by
      have := WithBot.coe_injective hdy
      rw [← this]
      push_cast
      ring
    exact (Cardinal.toENat_eq_natCast.1 (WithTop.add_right_cancel ENat.one_ne_top h1).symm)
  rw [hDim _ _ _ _ hP hnt, hTr O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht, hty,
    ← Nat.cast_add, Cardinal.toENat_nat, Fintype.card_option, Fintype.card_option,
    show d + (N - 1) + 1 + (Fintype.card K + 1 + 1) = d + Fintype.card K + (N + 1) + 1 by omega]
  norm_cast

end

end GroundTheory.Heights₂.Heights.NumbersDVR
