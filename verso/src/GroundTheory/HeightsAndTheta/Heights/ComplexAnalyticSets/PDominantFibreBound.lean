import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDominantFibreBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

/- English proof (translation)
Use `set a : Fin d → MvPolynomial (Fin n) ℂ ⧸ P := fun i => Ideal.Quotient.mk P (linPoly A i) with ha_def`. Establish `hproj : projHom P A = aeval a`. Rewrite using `[projHom, pullback, comp_aeval]`. Both sides reduce to the same expression. Establish `hind : AlgebraicIndependent ℂ a`.

Rewrite using `[algebraicIndependent_iff_injective_aeval, ← hproj]`. Conclude with `hA.injective`. Establish `hint : Algebra.IsIntegral (Algebra.adjoin ℂ (Set.range a)) (MvPolynomial (Fin n) ℂ ⧸ P)`. Prove the components needed by the constructor for the conclusion. Introduce `b`.

Take `⟨f, hfm, hfb⟩` from `hA.finite.to_isIntegral b`. Use `⟨f.map (hind.aevalEquiv : MvPolynomial (Fin d) ℂ →+* Algebra.adjoin ℂ (Set.range a)), hfm.map _, ?_⟩` and prove the remaining obligations. Establish `hcomp : (algebraMap (Algebra.adjoin ℂ (Set.range a)) (MvPolynomial (Fin n) ℂ ⧸ P)).comp (hind.aevalEquiv : MvPolynomial (Fin d) ℂ →+* Algebra.adjoin ℂ (Set.range a)) = (projHom P A).toRingHom`. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `y`.

Rewrite using `[RingHom.comp_apply]`. Express the relevant statement in the definitionally equal form `((hind.aevalEquiv y : Algebra.adjoin ℂ (Set.range a)) : MvPolynomial (Fin n) ℂ ⧸ P) = projHom P A y`. Rewrite using `[hproj]`. Conclude with `hind.algebraMap_aevalEquiv y`. Rewrite using `[Polynomial.eval₂_map, hcomp]`.

Conclude with `hfb`. Establish `: Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range a)) (MvPolynomial (Fin n) ℂ ⧸ P)` using `Algebra.IsIntegral.isAlgebraic`. Conclude with `(Algebra.IsAlgebraic.trdeg_le_cardinalMk (R := ℂ) (s := Set.range a)).trans Cardinal.mk_range_le`.
-/
theorem DominantFibreBound.trdeg_le {n d : ℕ} (P : Ideal (MvPolynomial (Fin n) ℂ)) [P.IsPrime]
    (A : Matrix (Fin d) (Fin n) ℂ) (hA : IsFiniteProjection P A) :
    Algebra.trdeg ℂ (MvPolynomial (Fin n) ℂ ⧸ P) ≤ Cardinal.mk (Fin d) := by
  set a : Fin d → MvPolynomial (Fin n) ℂ ⧸ P := fun i => Ideal.Quotient.mk P (linPoly A i) with ha_def
  have hproj : projHom P A = aeval a := by
    rw [projHom, pullback, comp_aeval]
    rfl
  have hind : AlgebraicIndependent ℂ a := by
    rw [algebraicIndependent_iff_injective_aeval, ← hproj]
    exact hA.injective
  have hint : Algebra.IsIntegral (Algebra.adjoin ℂ (Set.range a)) (MvPolynomial (Fin n) ℂ ⧸ P) := by
    constructor
    intro b
    obtain ⟨f, hfm, hfb⟩ := hA.finite.to_isIntegral b
    refine ⟨f.map (hind.aevalEquiv : MvPolynomial (Fin d) ℂ →+* Algebra.adjoin ℂ (Set.range a)),
      hfm.map _, ?_⟩
    have hcomp : (algebraMap (Algebra.adjoin ℂ (Set.range a)) (MvPolynomial (Fin n) ℂ ⧸ P)).comp
        (hind.aevalEquiv : MvPolynomial (Fin d) ℂ →+* Algebra.adjoin ℂ (Set.range a)) =
        (projHom P A).toRingHom := by
      apply RingHom.ext
      intro y
      rw [RingHom.comp_apply]
      change ((hind.aevalEquiv y : Algebra.adjoin ℂ (Set.range a)) : MvPolynomial (Fin n) ℂ ⧸ P) = projHom P A y
      rw [hproj]
      exact hind.algebraMap_aevalEquiv y
    rw [Polynomial.eval₂_map, hcomp]
    exact hfb
  have : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range a)) (MvPolynomial (Fin n) ℂ ⧸ P) :=
    Algebra.IsIntegral.isAlgebraic
  exact (Algebra.IsAlgebraic.trdeg_le_cardinalMk (R := ℂ) (s := Set.range a)).trans Cardinal.mk_range_le

/- English proof (translation)
Take `⟨A, hA⟩` from `(hG n d P hP hdim).2.1`. Use `set q : Fin d → MvPolynomial (Fin n) ℂ ⧸ P := fun i => Ideal.Quotient.mk P (p i) with hq_def`. Establish `hind : AlgebraicIndependent ℂ q`. Rewrite using `[algebraicIndependent_iff_injective_aeval]`. Rewrite `hinj` using `[comp_aeval]`.

Conclude with `hinj`. Establish `hbasis : IsTranscendenceBasis ℂ q` using `hind.isTranscendenceBasis_of_trdeg_le_of_finite (DominantFibreBound.trdeg_le P A hA)`. Take `⟨f, hf0, hfb⟩` from `hbasis.isAlgebraic.isAlgebraic b`. Use `⟨f.map (hind.aevalEquiv.symm : Algebra.adjoin ℂ (Set.range q) →+* MvPolynomial (Fin d) ℂ), (Polynomial.map_ne_zero_iff hind.aevalEquiv.symm.injective).2 hf0, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.map_map, ← hfb, Polynomial.aeval_def, Polynomial.eval_map]`.

Use `congr 1`. Use extensionality with `y`. Simplify using `[← hind.algebraMap_aevalEquiv]`.
-/
theorem DominantFibreBound.exists_poly (hG : ComplexSets.GenericProjectionFinite.Statement) {n d : ℕ}
    (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) (hP : P.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = (d : ℕ))
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ ℂ P).comp (aeval p)))
    (b : MvPolynomial (Fin n) ℂ ⧸ P) :
    ∃ g : Polynomial (MvPolynomial (Fin d) ℂ), g ≠ 0 ∧
      (g.map (aeval (fun i => Ideal.Quotient.mk P (p i))).toRingHom).eval b = 0 := by
  obtain ⟨A, hA⟩ := (hG n d P hP hdim).2.1
  set q : Fin d → MvPolynomial (Fin n) ℂ ⧸ P := fun i => Ideal.Quotient.mk P (p i) with hq_def
  have hind : AlgebraicIndependent ℂ q := by
    rw [algebraicIndependent_iff_injective_aeval]
    rw [comp_aeval] at hinj
    exact hinj
  have hbasis : IsTranscendenceBasis ℂ q :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite (DominantFibreBound.trdeg_le P A hA)
  obtain ⟨f, hf0, hfb⟩ := hbasis.isAlgebraic.isAlgebraic b
  refine ⟨f.map (hind.aevalEquiv.symm : Algebra.adjoin ℂ (Set.range q) →+* MvPolynomial (Fin d) ℂ),
    (Polynomial.map_ne_zero_iff hind.aevalEquiv.symm.injective).2 hf0, ?_⟩
  rw [Polynomial.map_map, ← hfb, Polynomial.aeval_def, Polynomial.eval_map]
  congr 1
  ext y
  simp [← hind.algebraMap_aevalEquiv]

/- English proof (translation)
Introduce `n d P p hP hdim hinj`. Use `choose g hg0 hgb using fun j : Fin n => DominantFibreBound.exists_poly hG P p hP hdim hinj (Ideal.Quotient.mk P (X j))`. Use `⟨∏ j, (g j).natDegree, ∏ j, (g j).leadingCoeff, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Finset.prod_ne_zero_iff.2 fun j _ => Polynomial.leadingCoeff_ne_zero.2 (hg0 j)`. Introduce `w hw`.

Rewrite `hw` using `[map_prod]`. Establish `hlc : ∀ j, eval w (g j).leadingCoeff ≠ 0` using `fun j => (Finset.prod_ne_zero_iff.1 hw) j (Finset.mem_univ j)`. Establish `hne : ∀ j, (g j).map (eval w) ≠ 0` using `fun j h => by`. Use `Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero (eval w) (hlc j)` as an intermediate fact. Rewrite `this` using `[h, Polynomial.leadingCoeff_zero]`.

Conclude with `hlc j this.symm`. Set `R : Fin n → Finset ℂ` to `fun j => ((g j).map (eval w)).roots.toFinset`. Establish `hsub : {x | x ∈ zeroSet P ∧ ∀ i, eval x (p i) = w i} ⊆ (Fintype.piFinset R : Set (Fin n → ℂ))`. Introduce and unpack `x ⟨hx, hxw⟩`. Rewrite using `[Finset.mem_coe, Fintype.mem_piFinset]`.

Introduce `j`. Set `ψ : MvPolynomial (Fin n) ℂ ⧸ P →+* ℂ` to `Ideal.Quotient.lift P (eval x) hx`. Establish `hψx : ∀ q, ψ (Ideal.Quotient.mk P q) = eval x q` using `fun q => Ideal.Quotient.lift_mk P _ _`. Establish `hψ : ψ.comp (aeval (fun i => Ideal.Quotient.mk P (p i))).toRingHom = eval w`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `c`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, algHom_C]`. Rewrite using `[← Ideal.Quotient.mk_algebraMap, hψx, MvPolynomial.algebraMap_eq, eval_C, eval_C]`. Introduce `i`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]`.

Rewrite using `[hψx, hxw i, eval_X]`. Establish `h0` using `congrArg ψ (hgb j)`. Rewrite `h0` using `[Polynomial.eval_map, Polynomial.hom_eval₂, hψ, map_zero, ← Polynomial.eval_map]`. Establish `hxj : ψ (Ideal.Quotient.mk P (X j)) = x j`. Rewrite using `[hψx, eval_X]`.

Rewrite `h0` using `[hxj]`. Conclude with `Multiset.mem_toFinset.2 ((Polynomial.mem_roots (hne j)).2 h0)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Fintype.card_piFinset]`. Conclude with `Finset.prod_le_prod' fun j _ => (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans Polynomial.natDegree_map_le)` after adjusting the coercions.
-/
theorem DominantFibreBound.proof (hG : ComplexSets.GenericProjectionFinite.Statement) :
    DominantFibreBound.Statement := by
  intro n d P p hP hdim hinj
  choose g hg0 hgb using fun j : Fin n =>
    DominantFibreBound.exists_poly hG P p hP hdim hinj (Ideal.Quotient.mk P (X j))
  refine ⟨∏ j, (g j).natDegree, ∏ j, (g j).leadingCoeff, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun j _ => Polynomial.leadingCoeff_ne_zero.2 (hg0 j)
  intro w hw
  rw [map_prod] at hw
  have hlc : ∀ j, eval w (g j).leadingCoeff ≠ 0 := fun j =>
    (Finset.prod_ne_zero_iff.1 hw) j (Finset.mem_univ j)
  have hne : ∀ j, (g j).map (eval w) ≠ 0 := fun j h => by
    have := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero (eval w) (hlc j)
    rw [h, Polynomial.leadingCoeff_zero] at this
    exact hlc j this.symm
  let R : Fin n → Finset ℂ := fun j => ((g j).map (eval w)).roots.toFinset
  have hsub : {x | x ∈ zeroSet P ∧ ∀ i, eval x (p i) = w i} ⊆
      (Fintype.piFinset R : Set (Fin n → ℂ)) := by
    rintro x ⟨hx, hxw⟩
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro j
    let ψ : MvPolynomial (Fin n) ℂ ⧸ P →+* ℂ := Ideal.Quotient.lift P (eval x) hx
    have hψx : ∀ q, ψ (Ideal.Quotient.mk P q) = eval x q := fun q => Ideal.Quotient.lift_mk P _ _
    have hψ : ψ.comp (aeval (fun i => Ideal.Quotient.mk P (p i))).toRingHom = eval w := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, algHom_C]
        rw [← Ideal.Quotient.mk_algebraMap, hψx, MvPolynomial.algebraMap_eq, eval_C, eval_C]
      · intro i
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
        rw [hψx, hxw i, eval_X]
    have h0 := congrArg ψ (hgb j)
    rw [Polynomial.eval_map, Polynomial.hom_eval₂, hψ, map_zero, ← Polynomial.eval_map] at h0
    have hxj : ψ (Ideal.Quotient.mk P (X j)) = x j := by
      rw [hψx, eval_X]
    rw [hxj] at h0
    exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots (hne j)).2 h0)
  calc _ ≤ (Fintype.piFinset R : Set (Fin n → ℂ)).encard := Set.encard_le_encard hsub
    _ = ((Fintype.piFinset R).card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ _ := by
      rw [Fintype.card_piFinset]
      exact_mod_cast Finset.prod_le_prod' fun j _ => (Multiset.toFinset_card_le _).trans
        ((Polynomial.card_roots' _).trans Polynomial.natDegree_map_le)

end

end GroundTheory.Heights₂.Heights
