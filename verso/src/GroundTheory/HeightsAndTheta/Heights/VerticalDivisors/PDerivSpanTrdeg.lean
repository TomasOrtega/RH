import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsDerivSpanTrdeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

noncomputable section

open scoped IntermediateField.algebraAdjoinAdjoin

/- English proof (translation)
Establish `hE : ∀ x ∈ IntermediateField.adjoin k s, D x = 0`. Introduce `x hx`. Proceed by induction on `hx using IntermediateField.adjoin_induction with`. Consider the case `mem x hx => exact hs x hx`. Consider the case `algebraMap x => exact D.map_algebraMap x`.

Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]`. Consider the case `inv x _ hx => rw [Derivation.leibniz_inv, hx, smul_zero]`. Consider the case `mul x y _ _ hx hy => rw [Derivation.leibniz, hx, hy, smul_zero, smul_zero, add_zero]`. Use extensionality with `α`. Use `set E := IntermediateField.adjoin k s`.

Establish `hsep : IsSeparable E α` using `Algebra.IsSeparable.isSeparable E α`. Use `set g : Polynomial K := (minpoly E α).map (algebraMap E K)`. Establish `h0 : D (g.eval α) = 0`. Rewrite using `[Polynomial.eval_map_algebraMap, minpoly.aeval, map_zero]`. Establish `hc : D.mapCoeffs g = 0`.

Use extensionality with `i`. Simplify using `only [Derivation.mapCoeffs_apply, g, Polynomial.coeff_map]`. Conclude with `(hE _ ((minpoly E α).coeff i).2).trans (by simp)`. Rewrite `h0` using `[Derivation.apply_eval_eq, hc, map_zero, zero_add]`. Establish `hne : g.derivative.eval α ≠ 0`.

Simplify using `only [g]`. Rewrite using `[Polynomial.derivative_map, Polynomial.eval_map_algebraMap]`. Conclude with `hsep.aeval_derivative_ne_zero (minpoly.aeval E α)`. Simplify `h0` using `[hne]`.
-/
theorem DerivSpanTrdeg.derivation_eq_zero_of_isSeparable {k K M : Type*} [Field k] [Field K]
    [Algebra k K] [AddCommGroup M] [Module K M] [Module k M] [IsScalarTower k K M] (s : Set K)
    [Algebra.IsSeparable (IntermediateField.adjoin k s) K] (D : Derivation k K M)
    (hs : ∀ x ∈ s, D x = 0) : D = 0 := by
  have hE : ∀ x ∈ IntermediateField.adjoin k s, D x = 0 := by
    intro x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx => exact hs x hx
    | algebraMap x => exact D.map_algebraMap x
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | inv x _ hx => rw [Derivation.leibniz_inv, hx, smul_zero]
    | mul x y _ _ hx hy => rw [Derivation.leibniz, hx, hy, smul_zero, smul_zero, add_zero]
  ext α
  set E := IntermediateField.adjoin k s
  have hsep : IsSeparable E α := Algebra.IsSeparable.isSeparable E α
  set g : Polynomial K := (minpoly E α).map (algebraMap E K)
  have h0 : D (g.eval α) = 0 := by
    rw [Polynomial.eval_map_algebraMap, minpoly.aeval, map_zero]
  have hc : D.mapCoeffs g = 0 := by
    ext i
    simp only [Derivation.mapCoeffs_apply, g, Polynomial.coeff_map]
    exact (hE _ ((minpoly E α).coeff i).2).trans (by simp)
  rw [Derivation.apply_eval_eq, hc, map_zero, zero_add] at h0
  have hne : g.derivative.eval α ≠ 0 := by
    simp only [g]
    rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval E α)
  simpa [hne] using h0

/- English proof (translation)
Introduce `k L _ _ _ _ ι _ z e he`. Use `set F₀ := IntermediateField.adjoin k (Set.range z)`. Establish `: Algebra.EssFiniteType k F₀`. Rewrite using `[IntermediateField.essFiniteType_iff]`. Conclude with `⟨Finset.univ.image z, by simp [F₀]⟩`.

Take `⟨s, hs, hsep⟩` from `exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F₀`. Establish `htr : Algebra.trdeg k F₀ = Algebra.trdeg k (Algebra.adjoin k (Set.range z))`. Use `trdeg_add_eq k (Algebra.adjoin k (Set.range z)) (A := F₀)` as an intermediate fact. Rewrite `this` using `[trdeg_eq_zero (R := Algebra.adjoin k (Set.range z)) (A := F₀), add_zero]`. Conclude with `this.symm`.

Establish `hcard : s.card ≤ e`. Establish `h1` using `hs.cardinalMk_eq_trdeg`. Rewrite `h1` using `[Cardinal.mk_coe_finset, htr]`. Conclude with `h1 ▸ he` after adjusting the coercions. Set `N : Submodule F₀ Ω[F₀⁄k]` to `Submodule.span F₀ (Set.range fun x : s => KaehlerDifferential.D k F₀ x)`.

Establish `hspan : N = ⊤`. Establish `hD` using `DerivSpanTrdeg.derivation_eq_zero_of_isSeparable (M := Ω[F₀⁄k] ⧸ N) (s : Set F₀) (N.mkQ.compDer (KaehlerDifferential.D k F₀)) (fun x hx => by`. Express the relevant statement in the definitionally equal form `N.mkQ (KaehlerDifferential.D k F₀ x) = 0`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩)`.

Rewrite using `[eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Use `congrArg (fun D => D x) hD` as an intermediate fact. Simplify `this` using `[Submodule.Quotient.mk_eq_zero]`. Establish `hr : Module.finrank F₀ Ω[F₀⁄k] ≤ e`.

Establish `h` using `finrank_range_le_card (R := F₀) (fun x : s => KaehlerDifferential.D k F₀ x)`. Express the relevant statement in the definitionally equal form `Module.finrank F₀ N ≤ _ at h`. Rewrite `h` using `[hspan, finrank_top, Fintype.card_coe]`. Conclude with `h.trans hcard`. Set `ω` to `Module.finBasis F₀ Ω[F₀⁄k]`.

Use `⟨Module.finrank F₀ Ω[F₀⁄k], hr, fun m j => ω.repr (KaehlerDifferential.D k F₀ ⟨z j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩) m, ?_⟩` and prove the remaining obligations. Introduce `D`. Set `D' : Derivation k F₀ L` to `D.compAlgebraMap F₀`. Set `φ` to `(KaehlerDifferential.linearMapEquivDerivation k F₀).symm D'`. Use `⟨fun m => φ (ω m), fun j => ?_⟩` and prove the remaining obligations.

Establish `h1 : D (z j) = φ (KaehlerDifferential.D k F₀ ⟨z j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩)`. Establish `h` using `LinearEquiv.apply_symm_apply (KaehlerDifferential.linearMapEquivDerivation k F₀) D'`. Conclude with `(congrArg (fun D'' : Derivation k F₀ L => D'' ⟨z j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩) h).symm`. Rewrite using `[h1, ← ω.sum_repr (KaehlerDifferential.D k F₀ _), map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, Algebra.smul_def, mul_comm]`. Both sides reduce to the same expression.
-/
theorem DerivSpanTrdeg.proof : DerivSpanTrdeg.Statement := by
  intro k L _ _ _ _ ι _ z e he
  classical
  set F₀ := IntermediateField.adjoin k (Set.range z)
  have : Algebra.EssFiniteType k F₀ := by
    rw [IntermediateField.essFiniteType_iff]
    exact ⟨Finset.univ.image z, by simp [F₀]⟩
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F₀
  have htr : Algebra.trdeg k F₀ = Algebra.trdeg k (Algebra.adjoin k (Set.range z)) := by
    have := trdeg_add_eq k (Algebra.adjoin k (Set.range z)) (A := F₀)
    rw [trdeg_eq_zero (R := Algebra.adjoin k (Set.range z)) (A := F₀), add_zero] at this
    exact this.symm
  have hcard : s.card ≤ e := by
    have h1 := hs.cardinalMk_eq_trdeg
    rw [Cardinal.mk_coe_finset, htr] at h1
    exact_mod_cast h1 ▸ he
  let N : Submodule F₀ Ω[F₀⁄k] :=
    Submodule.span F₀ (Set.range fun x : s => KaehlerDifferential.D k F₀ x)
  have hspan : N = ⊤ := by
    have hD := DerivSpanTrdeg.derivation_eq_zero_of_isSeparable (M := Ω[F₀⁄k] ⧸ N) (s : Set F₀)
      (N.mkQ.compDer (KaehlerDifferential.D k F₀)) (fun x hx => by
        change N.mkQ (KaehlerDifferential.D k F₀ x) = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩)
    rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have := congrArg (fun D => D x) hD
    simpa [Submodule.Quotient.mk_eq_zero] using this
  have hr : Module.finrank F₀ Ω[F₀⁄k] ≤ e := by
    have h := finrank_range_le_card (R := F₀) (fun x : s => KaehlerDifferential.D k F₀ x)
    change Module.finrank F₀ N ≤ _ at h
    rw [hspan, finrank_top, Fintype.card_coe] at h
    exact h.trans hcard
  let ω := Module.finBasis F₀ Ω[F₀⁄k]
  refine ⟨Module.finrank F₀ Ω[F₀⁄k], hr, fun m j =>
    ω.repr (KaehlerDifferential.D k F₀ ⟨z j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩) m, ?_⟩
  intro D
  let D' : Derivation k F₀ L := D.compAlgebraMap F₀
  let φ := (KaehlerDifferential.linearMapEquivDerivation k F₀).symm D'
  refine ⟨fun m => φ (ω m), fun j => ?_⟩
  have h1 : D (z j) =
      φ (KaehlerDifferential.D k F₀ ⟨z j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩) := by
    have h := LinearEquiv.apply_symm_apply (KaehlerDifferential.linearMapEquivDerivation k F₀) D'
    exact (congrArg (fun D'' : Derivation k F₀ L =>
      D'' ⟨z j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩) h).symm
  rw [h1, ← ω.sum_repr (KaehlerDifferential.D k F₀ _), map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, Algebra.smul_def, mul_comm]
  rfl

end

end GroundTheory.Heights₂.Heights.Vertical
