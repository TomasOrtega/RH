import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryConjOfSameEllipticCharpolyInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjOfCharpolyLocal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.IntUnitConj

/- English proof (translation)
Introduce `E _ _ _ hU n P hP`. Use `filter_upwards [UnitInert.eventually_separable P hP] with w hsep γ γ' hγK hγ'K hγ hγ'`. Set `O` to `w.adicCompletionIntegers E`. Set `ι` to `algebraMap O (w.adicCompletion E)`. Establish `hι : Function.Injective ι` using `Subtype.val_injective`.

Take `⟨y', hy'⟩ : ∃ y' : GL (Fin n) O, GeneralLinearGroup.map ι y' = γ.1` from `(Subgroup.mem_subgroupOf.1 hγK)`. Take `⟨z', hz'⟩ : ∃ z' : GL (Fin n) O, GeneralLinearGroup.map ι z' = γ'.1` from `(Subgroup.mem_subgroupOf.1 hγ'K)`. Establish `hch : ∀ x : GL (Fin n) O, x.val.charpoly.map ι = (GeneralLinearGroup.map ι x).val.charpoly` using `fun x => (Matrix.charpoly_map _ _).symm`. Establish `e1 : y'.val.charpoly.map ι = atPl w P` using `by rw [hch, hy', hγ]`. Establish `e2 : z'.val.charpoly.map ι = atPl w P` using `by rw [hch, hz', hγ']`.

Establish `e12 : z'.val.charpoly = y'.val.charpoly` using `Polynomial.map_injective ι hι (e2.trans e1.symm)`. It suffices to establish `H : ∃ u : GL (Fin n) O, GeneralLinearGroup.map ι u ∈ UL n w ∧ y'.val * u.val = u.val * z'.val by`. Take `⟨u, hu, hcu⟩` from `H`. Set `g : GLw n w` to `GeneralLinearGroup.map ι u`. Establish `key : γ.1 * g = g * γ'.1`.

Rewrite using `[← hy', ← hz', ← map_mul, ← map_mul]`. Use `congr 1`. Conclude with `Units.ext hcu`. Use `⟨⟨g, hu⟩, Subgroup.mem_subgroupOf.2 ⟨u, rfl⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `γ'.1 = g⁻¹ * γ.1 * g`.

Rewrite using `[mul_assoc, key, inv_mul_cancel_left]`. Distinguish the cases in `hw : IsSplitAt w`. Take `⟨u, hu⟩` from `GlobalTheory.ConjLocal.conj_of_charpoly_local O n y'.val z'.val e12.symm (hsep _ e1)`. Use `⟨u, by rw [UL, if_pos hw]; exact Subgroup.mem_top _, ?_⟩` and prove the remaining obligations. Rewrite using `[hu, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]`.

Take `⟨-, hcc, hv, h4, -⟩` from `GlobalTheory.ConjAtPlace.main E hU w`. Take `⟨ϖ, q, ⟨-, -, -, -, ⟨x₀, hx₀, hx₁⟩, hq2, hcard⟩, -⟩` from `(h4 hw).2.1`. Establish `hcard' : Nat.card (O ⧸ IsLocalRing.maximalIdeal O) = q ^ 2` using `hcard`. Use `haveI := GlobalTheory.HenselSquare.isAdicComplete_integers E w`. Use `haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) := Nat.finite_of_card_ne_zero (by rw [hcard']; positivity)`.

Set `c : O →+* O` to `(cj w).restrict _ _ (ThBasic.cj_mem_integers hU w)`. Establish `hc : ∀ x, c (c x) = x` using `fun x => Subtype.ext (hcc _)`. Establish `hmapc : ∀ M : Matrix (Fin n) (Fin n) O, (cT c M).map ι = cT (cj w) (M.map ι)` using `fun M => by`. Use extensionality with `i j`. Both sides reduce to the same expression.

Establish `hUL : ∀ x : GLw n w, x ∈ UL n w ↔ cT (cj w) x.val * x.val = 1` using `fun x => by`. Rewrite using `[UL, if_neg hw]`. Express the relevant statement in the definitionally equal form `cT (cj w) x.val * 1 * x.val = 1 ↔ _`. Rewrite using `[mul_one]`. Establish `hmv : ∀ x : GL (Fin n) O, (GeneralLinearGroup.map ι x).val = x.val.map ι` using `fun x => by`.

Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hunit : ∀ (x : GL (Fin n) O), GeneralLinearGroup.map ι x ∈ UL n w → cT c x.val * x.val = 1` using `fun x hx => by`. Use `Matrix.map_injective hι ?_` and prove the remaining obligations. Use `show (cT c x.val * x.val).map ι = (1 : Matrix (Fin n) (Fin n) O).map ι`.

Rewrite using `[Matrix.map_mul, hmapc, Matrix.map_one _ (map_zero ι) (map_one ι), ← hmv]`. Conclude with `(hUL _).1 hx`. Take `⟨u, hu, hcu⟩` from `UnitInert.exists_unitary_conj (IsLocalRing.maximalIdeal O) (σ := c) hc (fun x hx => by`. Rewrite `hx`, the goal using `[GlobalTheory.InertUQ.mem_max_iff]`. Conclude with `(hv _).trans_lt hx)`.

Use the proof step `⟨⟨x₀, hx₀⟩, by`. Rewrite using `[← IsLocalRing.notMem_maximalIdeal, GlobalTheory.InertUQ.mem_max_iff]`. Express the relevant statement in the definitionally equal form `¬ Valued.v (x₀ - cj w x₀) < 1`. Rewrite using `[Valuation.map_sub_swap, hx₁]`. Conclude with `lt_irrefl _⟩`.

Use the proof step `(hunit y' (hy' ▸ γ.2)) (hunit z' (hz' ▸ γ'.2)) (hsep _ e1) e12`. Use `⟨u, ?_, hcu⟩` and prove the remaining obligations. Rewrite using `[hUL]`. Use `congrArg (fun M => M.map ι) hu` as an intermediate fact. Simplify using `only [Matrix.map_mul, hmapc, Matrix.map_one _ (map_zero ι) (map_one ι)] at this`.

Conclude with `this`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (P : E[X]), P.Separable →
    ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ y y' : UL n w, y ∈ KL n w → y' ∈ KL n w → y.1.val.charpoly = atPl w P →
      y'.1.val.charpoly = atPl w P → ∃ g ∈ KL n w, y' = g⁻¹ * y * g := by
  intro E _ _ _ hU n P hP
  filter_upwards [UnitInert.eventually_separable P hP] with w hsep γ γ' hγK hγ'K hγ hγ'
  let O := w.adicCompletionIntegers E
  let ι := algebraMap O (w.adicCompletion E)
  have hι : Function.Injective ι := Subtype.val_injective
  obtain ⟨y', hy'⟩ : ∃ y' : GL (Fin n) O, GeneralLinearGroup.map ι y' = γ.1 := (Subgroup.mem_subgroupOf.1 hγK)
  obtain ⟨z', hz'⟩ : ∃ z' : GL (Fin n) O, GeneralLinearGroup.map ι z' = γ'.1 := (Subgroup.mem_subgroupOf.1 hγ'K)
  have hch : ∀ x : GL (Fin n) O, x.val.charpoly.map ι = (GeneralLinearGroup.map ι x).val.charpoly := fun x =>
    (Matrix.charpoly_map _ _).symm
  have e1 : y'.val.charpoly.map ι = atPl w P := by rw [hch, hy', hγ]
  have e2 : z'.val.charpoly.map ι = atPl w P := by rw [hch, hz', hγ']
  have e12 : z'.val.charpoly = y'.val.charpoly := Polynomial.map_injective ι hι (e2.trans e1.symm)
  suffices H : ∃ u : GL (Fin n) O, GeneralLinearGroup.map ι u ∈ UL n w ∧ y'.val * u.val = u.val * z'.val by
    obtain ⟨u, hu, hcu⟩ := H
    let g : GLw n w := GeneralLinearGroup.map ι u
    have key : γ.1 * g = g * γ'.1 := by
      rw [← hy', ← hz', ← map_mul, ← map_mul]
      congr 1
      exact Units.ext hcu
    refine ⟨⟨g, hu⟩, Subgroup.mem_subgroupOf.2 ⟨u, rfl⟩, Subtype.ext ?_⟩
    change γ'.1 = g⁻¹ * γ.1 * g
    rw [mul_assoc, key, inv_mul_cancel_left]
  by_cases hw : IsSplitAt w
  · obtain ⟨u, hu⟩ := GlobalTheory.ConjLocal.conj_of_charpoly_local O n y'.val z'.val e12.symm (hsep _ e1)
    refine ⟨u, by rw [UL, if_pos hw]; exact Subgroup.mem_top _, ?_⟩
    rw [hu, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
  · obtain ⟨-, hcc, hv, h4, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    obtain ⟨ϖ, q, ⟨-, -, -, -, ⟨x₀, hx₀, hx₁⟩, hq2, hcard⟩, -⟩ := (h4 hw).2.1
    have hcard' : Nat.card (O ⧸ IsLocalRing.maximalIdeal O) = q ^ 2 := hcard
    haveI := GlobalTheory.HenselSquare.isAdicComplete_integers E w
    haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) :=
      Nat.finite_of_card_ne_zero (by rw [hcard']; positivity)
    let c : O →+* O := (cj w).restrict _ _ (ThBasic.cj_mem_integers hU w)
    have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hcc _)
    have hmapc : ∀ M : Matrix (Fin n) (Fin n) O, (cT c M).map ι = cT (cj w) (M.map ι) := fun M => by
      ext i j; rfl
    have hUL : ∀ x : GLw n w, x ∈ UL n w ↔ cT (cj w) x.val * x.val = 1 := fun x => by
      rw [UL, if_neg hw]
      change cT (cj w) x.val * 1 * x.val = 1 ↔ _
      rw [mul_one]
    have hmv : ∀ x : GL (Fin n) O, (GeneralLinearGroup.map ι x).val = x.val.map ι := fun x => by
      ext i j; rfl
    have hunit : ∀ (x : GL (Fin n) O), GeneralLinearGroup.map ι x ∈ UL n w → cT c x.val * x.val = 1 := fun x hx => by
      refine Matrix.map_injective hι ?_
      show (cT c x.val * x.val).map ι = (1 : Matrix (Fin n) (Fin n) O).map ι
      rw [Matrix.map_mul, hmapc, Matrix.map_one _ (map_zero ι) (map_one ι), ← hmv]
      exact (hUL _).1 hx
    obtain ⟨u, hu, hcu⟩ := UnitInert.exists_unitary_conj (IsLocalRing.maximalIdeal O) (σ := c) hc
      (fun x hx => by
        rw [GlobalTheory.InertUQ.mem_max_iff] at hx ⊢
        exact (hv _).trans_lt hx)
      ⟨⟨x₀, hx₀⟩, by
        rw [← IsLocalRing.notMem_maximalIdeal, GlobalTheory.InertUQ.mem_max_iff]
        change ¬ Valued.v (x₀ - cj w x₀) < 1
        rw [Valuation.map_sub_swap, hx₁]
        exact lt_irrefl _⟩
      (hunit y' (hy' ▸ γ.2)) (hunit z' (hz' ▸ γ'.2)) (hsep _ e1) e12
    refine ⟨u, ?_, hcu⟩
    rw [hUL]
    have := congrArg (fun M => M.map ι) hu
    simp only [Matrix.map_mul, hmapc, Matrix.map_one _ (map_zero ι) (map_one ι)] at this
    exact this

end GlobalTheory.BCT.IntUnitConj
