import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodEmptyIff
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

noncomputable section

namespace GlobalTheory.RSConj

/- English proof (translation)
Distinguish the cases in `hf : Multipliable f`. Conclude with `hf.map_tprod (starRingEnd ℂ) Complex.continuous_conj`. Establish `hg : ¬ Multipliable fun i => starRingEnd ℂ (f i)`. Introduce `hg`. Apply `hf` to reduce the goal to its premises.

Use `hg.map (starRingEnd ℂ) Complex.continuous_conj` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[tprod_eq_one_of_not_multipliable hf, tprod_eq_one_of_not_multipliable hg, map_one]`.
-/
theorem conj_tprod {β : Type} (f : β → ℂ) :
    starRingEnd ℂ (∏' i, f i) = ∏' i, starRingEnd ℂ (f i) := by
  by_cases hf : Multipliable f
  · exact hf.map_tprod (starRingEnd ℂ) Complex.continuous_conj
  · have hg : ¬ Multipliable fun i => starRingEnd ℂ (f i) := by
      intro hg
      apply hf
      have := hg.map (starRingEnd ℂ) Complex.continuous_conj
      convert this using 1
      funext i
      simp
    rw [tprod_eq_one_of_not_multipliable hf, tprod_eq_one_of_not_multipliable hg, map_one]

/- English proof (translation)
Establish `h : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_cpow (Nat.cast_nonneg q)]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[h, Complex.conj_ofReal]`.
-/
theorem conj_natCast_cpow_neg (q : ℕ) (x : ℝ) :
    starRingEnd ℂ ((q : ℂ) ^ (-(x : ℂ))) = (q : ℂ) ^ (-(x : ℂ)) := by
  have h : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg q)]
    push_cast
    rfl
  rw [h, Complex.conj_ofReal]

/- English proof (translation)
Unfold `locL`. Rewrite using `[map_multiset_prod]`. Simplify using `only [SProd.sprod, Multiset.product, Multiset.map_bind, Multiset.prod_bind, Multiset.map_map, Function.comp_def]`. Rewrite using `[Multiset.prod_map_prod_map]`. Use `congr 1`.

Use `Multiset.map_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `congr 1`. Use `Multiset.map_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [map_inv₀, map_sub, map_one, map_mul, conj_natCast_cpow_neg, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Complex.conj_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_locL (q : ℕ) (A B : Multiset ℂˣ) (x : ℝ) :
    starRingEnd ℂ (locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) =
      locL q B (A.map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) := by
  unfold locL
  rw [map_multiset_prod]
  simp only [SProd.sprod, Multiset.product, Multiset.map_bind, Multiset.prod_bind, Multiset.map_map, Function.comp_def]
  rw [Multiset.prod_map_prod_map]
  congr 1
  refine Multiset.map_congr rfl fun b _ => ?_
  congr 1
  refine Multiset.map_congr rfl fun a _ => ?_
  simp only [map_inv₀, map_sub, map_one, map_mul, conj_natCast_cpow_neg, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Complex.conj_conj]
  ring

/- English proof (translation)
Introduce `E _ _ _ a b σ σ' _ _ T _ _ x _`. Rewrite using `[conj_tprod]`. Use `congr 1`. Use function extensionality and compare the values at `w`. Conclude with `(conj_locL _ _ _ x).symm`.
-/
theorem partial_conj : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b),
    σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' →
    ∀ x : ℝ, 1 < x → ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ (x : ℂ) w.1 =
      starRingEnd ℂ (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1) := by
  intro E _ _ _ a b σ σ' _ _ T _ _ x _
  rw [conj_tprod]
  congr 1
  funext w
  exact (conj_locL _ _ _ x).symm

end GlobalTheory.RSConj
