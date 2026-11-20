import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCotangentBasisInPrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

/- English proof (translation)
Introduce `T _ _ P _`. Set `g : P → maximalIdeal (Localization.AtPrime P)` to `fun x => ⟨algebraMap T _ x, (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P (x : T)).2 x.2⟩`. Set `v : P → CotangentSpace (Localization.AtPrime P)` to `fun x => (maximalIdeal _).toCotangent (g x)`. Establish `hspan : Submodule.span (ResidueField (Localization.AtPrime P)) (Set.range v) = ⊤`. Use `eq_top_iff.2 fun z _ => ?_` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `(maximalIdeal (Localization.AtPrime P)).toCotangent_surjective z`. Take `⟨⟨x, s⟩, hxs⟩` from `IsLocalization.mk'_surjective P.primeCompl (y : Localization.AtPrime P)`. Simplify using `only at hxs`. Establish `hx : x ∈ P` using `(IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime P) P x s).1 (hxs ▸ y.2)`. Establish `hy : y = IsLocalization.mk' (Localization.AtPrime P) (1 : T) s • g ⟨x, hx⟩`.

Use `ext`. Simplify using `only [g, Submodule.coe_smul, smul_eq_mul, ← hxs]`. Rewrite using `[IsLocalization.mk'_eq_mul_mk'_one, mul_comm]`. Rewrite using `[hy, map_smul, ← algebraMap_smul (ResidueField (Localization.AtPrime P))]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩)`.

Take `⟨κ, a, -, hsp, hli⟩` from `exists_linearIndependent' (ResidueField (Localization.AtPrime P)) v`. Establish `: Finite κ` using `hli.finite_of_isNoetherian`. Set `e` to `Finite.equivFin κ`. Set `w` to `(v ∘ a) ∘ e.symm`. Establish `hliw : LinearIndependent (ResidueField (Localization.AtPrime P)) w` using `hli.comp e.symm e.symm.injective`.

Establish `hspw : Submodule.span (ResidueField (Localization.AtPrime P)) (Set.range w) = ⊤`. Rewrite using `[show Set.range w = Set.range (v ∘ a) from e.symm.surjective.range_comp _, hsp, hspan]`. Set `G : Fin (Nat.card κ) → maximalIdeal (Localization.AtPrime P)` to `fun i => g (a (e.symm i))`. Establish `hsum : ∀ c : Fin (Nat.card κ) → Localization.AtPrime P, (maximalIdeal _).toCotangent (∑ i, c i • G i) = ∑ i, residue _ (c i) • w i`. Introduce `c`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, ← ResidueField.algebraMap_eq, algebraMap_smul]`. Both sides reduce to the same expression. Establish `hcoe : ∀ c : Fin (Nat.card κ) → Localization.AtPrime P, ((∑ i, c i • G i : maximalIdeal (Localization.AtPrime P)) : Localization.AtPrime P) = ∑ i, c i * algebraMap T _ (a (e.symm i) : T)`.

Introduce `c`. Simplify using `[G, g]`. Use `⟨Nat.card κ, fun i => (a (e.symm i) : T), fun i => (a (e.symm i)).2, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Establish `hz : (maximalIdeal _).toCotangent ⟨y, hy⟩ ∈ Submodule.span (ResidueField (Localization.AtPrime P)) (Set.range w)`.

Rewrite using `[hspw]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 hz`. Use `choose c' hc' using fun i => residue_surjective (R := Localization.AtPrime P) (c i)`. Establish `hdiff : (maximalIdeal _).toCotangent (⟨y, hy⟩ - ∑ i, c' i • G i) = 0`.

Rewrite using `[map_sub, hsum, ← hc]`. Simplify using `[hc']`. Rewrite `hdiff` using `[Ideal.toCotangent_eq_zero, Submodule.coe_sub, hcoe]`. Rewrite using `[show y = (y - ∑ i, c' i * algebraMap T _ (a (e.symm i) : T)) + ∑ i, c' i * algebraMap T _ (a (e.symm i) : T) by ring]`. Use `add_mem (Ideal.mem_sup_right hdiff) (Ideal.mem_sup_left (Ideal.sum_mem _ fun i _ => ?_))` and prove the remaining obligations.

Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)`. Introduce `c hc i`. Establish `h0 : (maximalIdeal _).toCotangent (∑ i, c i • G i) = 0`. Rewrite using `[Ideal.toCotangent_eq_zero, hcoe]`. Conclude with `hc`.

Rewrite `h0` using `[hsum]`. Conclude with `(residue_eq_zero_iff _).1 (Fintype.linearIndependent_iff.1 hliw _ h0 i)`.
-/
theorem CotangentBasisInPrime.proof : CotangentBasisInPrime.Statement := by
  intro T _ _ P _

  let g : P → maximalIdeal (Localization.AtPrime P) := fun x =>
    ⟨algebraMap T _ x, (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P (x : T)).2 x.2⟩
  let v : P → CotangentSpace (Localization.AtPrime P) := fun x => (maximalIdeal _).toCotangent (g x)
  have hspan : Submodule.span (ResidueField (Localization.AtPrime P)) (Set.range v) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨y, rfl⟩ := (maximalIdeal (Localization.AtPrime P)).toCotangent_surjective z
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.mk'_surjective P.primeCompl (y : Localization.AtPrime P)
    simp only at hxs
    have hx : x ∈ P :=
      (IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime P) P x s).1 (hxs ▸ y.2)
    have hy : y = IsLocalization.mk' (Localization.AtPrime P) (1 : T) s • g ⟨x, hx⟩ := by
      ext
      simp only [g, Submodule.coe_smul, smul_eq_mul, ← hxs]
      rw [IsLocalization.mk'_eq_mul_mk'_one, mul_comm]
    rw [hy, map_smul, ← algebraMap_smul (ResidueField (Localization.AtPrime P))]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩)
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' (ResidueField (Localization.AtPrime P)) v
  have : Finite κ := hli.finite_of_isNoetherian
  let e := Finite.equivFin κ
  let w := (v ∘ a) ∘ e.symm
  have hliw : LinearIndependent (ResidueField (Localization.AtPrime P)) w :=
    hli.comp e.symm e.symm.injective
  have hspw : Submodule.span (ResidueField (Localization.AtPrime P)) (Set.range w) = ⊤ := by
    rw [show Set.range w = Set.range (v ∘ a) from e.symm.surjective.range_comp _, hsp, hspan]
  let G : Fin (Nat.card κ) → maximalIdeal (Localization.AtPrime P) := fun i => g (a (e.symm i))
  have hsum : ∀ c : Fin (Nat.card κ) → Localization.AtPrime P,
      (maximalIdeal _).toCotangent (∑ i, c i • G i) = ∑ i, residue _ (c i) • w i := by
    intro c
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← ResidueField.algebraMap_eq, algebraMap_smul]
    rfl
  have hcoe : ∀ c : Fin (Nat.card κ) → Localization.AtPrime P,
      ((∑ i, c i • G i : maximalIdeal (Localization.AtPrime P)) : Localization.AtPrime P) =
        ∑ i, c i * algebraMap T _ (a (e.symm i) : T) := by
    intro c
    simp [G, g]
  refine ⟨Nat.card κ, fun i => (a (e.symm i) : T), fun i => (a (e.symm i)).2, ?_, ?_⟩
  · intro y hy
    have hz : (maximalIdeal _).toCotangent ⟨y, hy⟩ ∈
        Submodule.span (ResidueField (Localization.AtPrime P)) (Set.range w) := by
      rw [hspw]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hz
    choose c' hc' using fun i => residue_surjective (R := Localization.AtPrime P) (c i)
    have hdiff : (maximalIdeal _).toCotangent (⟨y, hy⟩ - ∑ i, c' i • G i) = 0 := by
      rw [map_sub, hsum, ← hc]
      simp [hc']
    rw [Ideal.toCotangent_eq_zero, Submodule.coe_sub, hcoe] at hdiff
    rw [show y = (y - ∑ i, c' i * algebraMap T _ (a (e.symm i) : T)) +
        ∑ i, c' i * algebraMap T _ (a (e.symm i) : T) by ring]
    refine add_mem (Ideal.mem_sup_right hdiff) (Ideal.mem_sup_left (Ideal.sum_mem _ fun i _ => ?_))
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · intro c hc i
    have h0 : (maximalIdeal _).toCotangent (∑ i, c i • G i) = 0 := by
      rw [Ideal.toCotangent_eq_zero, hcoe]; exact hc
    rw [hsum] at h0
    exact (residue_eq_zero_iff _).1 (Fintype.linearIndependent_iff.1 hliw _ h0 i)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
