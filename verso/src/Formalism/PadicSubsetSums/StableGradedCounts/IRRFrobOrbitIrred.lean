import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Formalism.GaloisIrreducibility (IsOrbit)

/- English proof (translation)
Unfold `FrobOrbitIrred IsOrbit`. Introduce `K L _ _ _ _ _ f hm hirr`. Establish `hf0 : f ≠ 0` using `hm.ne_zero`. Establish `hfL : f.map (algebraMap K L) ≠ 0` using `Polynomial.map_ne_zero hf0`. Establish `hmem : ∀ z : L, z ∈ (f.aroots L).toFinset ↔ aeval z f = 0`.

Introduce `z`. Rewrite using `[Multiset.mem_toFinset, mem_aroots]`. Conclude with `⟨fun h => h.2, fun h => ⟨hf0, h⟩⟩`. Establish `hfrob : ∀ z : L, aeval (z ^ Fintype.card K) f = (aeval z f) ^ Fintype.card K`. Introduce `z`.

Rewrite using `[← expand_aeval, FiniteField.expand_card, map_pow]`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx`, the goal using `[hmem]`. Use `show aeval (x ^ Fintype.card K) f = 0`.

Rewrite using `[hfrob, hx, zero_pow Fintype.card_ne_zero]`. Introduce `x hx y hy`. Rewrite `hx`, `hy` using `[hmem]`. Set `E : IntermediateField K L` to `IntermediateField.adjoin K (f.rootSet L)`. Establish `hxE : x ∈ E` using `IntermediateField.subset_adjoin K _ ((mem_rootSet_of_ne hf0).2 hx)`.

Establish `hyE : y ∈ E` using `IntermediateField.subset_adjoin K _ ((mem_rootSet_of_ne hf0).2 hy)`. Use `haveI hSF : IsSplittingField K E f := IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)`. Use `haveI : Normal K E := Normal.of_isSplittingField f`. Use `haveI : FiniteDimensional K E := IsSplittingField.finiteDimensional E f`. Use `haveI : Finite E := Module.finite_of_finite K`.

Use `haveI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E`. Establish `hmx : minpoly K x = f` using `(minpoly.eq_of_irreducible_of_monic hirr hx hm).symm`. Establish `hmy : minpoly K y = f` using `(minpoly.eq_of_irreducible_of_monic hirr hy hm).symm`. Establish `hxy : minpoly K (⟨y, hyE⟩ : E) = minpoly K (⟨x, hxE⟩ : E)`. Rewrite using `[IntermediateField.minpoly_eq, IntermediateField.minpoly_eq]`.

Use `show minpoly K y = minpoly K x`. Rewrite using `[hmx, hmy]`. Take `⟨σ, hσ⟩` from `(Normal.minpoly_eq_iff_mem_orbit E).1 hxy`. Take `⟨n, hn⟩` from `(FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K E).2 σ`. Establish `key : ∀ (m : ℕ) (w : E), (((FiniteField.frobeniusAlgEquivOfAlgebraic K E ^ m) w : E) : L) = (fun z : L => z ^ Fintype.card K)^[m] (w : L)`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro w`. Both sides reduce to the same expression. Consider the case `succ m ih`.

Introduce `w`. Rewrite using `[pow_succ, AlgEquiv.mul_apply, ih, Function.iterate_succ_apply]`. Use `congr 1`. Apply the tactic sequence `all_goals (try rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic])`. Apply the tactic sequence `all_goals (try simp)`.

Simplify using `only at hσ`. Establish `h2 : ((σ ⟨x, hxE⟩ : E) : L) = y`. Rewrite using `[← AlgEquiv.smul_def, hσ]`. Simplify using `only at hn`. Rewrite `h2` using `[← hn, key]`.

Conclude with `⟨_, h2⟩`. Establish `hsep : f.Separable` using `by first`. Consider the case `exact PerfectField.separable_of_irreducible hirr`. Consider the case `(haveI : PerfectField K := PerfectField.ofFinite`. Conclude with `PerfectField.separable_of_irreducible hirr)`.

Rewrite using `[Multiset.toFinset_card_of_nodup (nodup_roots (hsep.map (f := algebraMap K L)))]`. Use `show Multiset.card (f.map (algebraMap K L)).roots = f.natDegree`. Rewrite using `[IsAlgClosed.card_roots_eq_natDegree, natDegree_map]`.
-/
theorem frobenius_orbit_irreducible : FrobOrbitIrred := by
  unfold FrobOrbitIrred IsOrbit
  intro K L _ _ _ _ _ f hm hirr
  classical
  have hf0 : f ≠ 0 := hm.ne_zero
  have hfL : f.map (algebraMap K L) ≠ 0 := Polynomial.map_ne_zero hf0
  have hmem : ∀ z : L, z ∈ (f.aroots L).toFinset ↔ aeval z f = 0 := by
    intro z
    rw [Multiset.mem_toFinset, mem_aroots]
    exact ⟨fun h => h.2, fun h => ⟨hf0, h⟩⟩
  have hfrob : ∀ z : L, aeval (z ^ Fintype.card K) f = (aeval z f) ^ Fintype.card K := by
    intro z
    rw [← expand_aeval, FiniteField.expand_card, map_pow]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x hx
    rw [hmem] at hx ⊢
    show aeval (x ^ Fintype.card K) f = 0
    rw [hfrob, hx, zero_pow Fintype.card_ne_zero]
  · intro x hx y hy
    rw [hmem] at hx hy
    let E : IntermediateField K L := IntermediateField.adjoin K (f.rootSet L)
    have hxE : x ∈ E := IntermediateField.subset_adjoin K _ ((mem_rootSet_of_ne hf0).2 hx)
    have hyE : y ∈ E := IntermediateField.subset_adjoin K _ ((mem_rootSet_of_ne hf0).2 hy)
    haveI hSF : IsSplittingField K E f :=
      IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
    haveI : Normal K E := Normal.of_isSplittingField f
    haveI : FiniteDimensional K E := IsSplittingField.finiteDimensional E f
    haveI : Finite E := Module.finite_of_finite K
    haveI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    have hmx : minpoly K x = f := (minpoly.eq_of_irreducible_of_monic hirr hx hm).symm
    have hmy : minpoly K y = f := (minpoly.eq_of_irreducible_of_monic hirr hy hm).symm
    have hxy : minpoly K (⟨y, hyE⟩ : E) = minpoly K (⟨x, hxE⟩ : E) := by
      rw [IntermediateField.minpoly_eq, IntermediateField.minpoly_eq]
      show minpoly K y = minpoly K x
      rw [hmx, hmy]
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit E).1 hxy
    obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K E).2 σ
    have key : ∀ (m : ℕ) (w : E), (((FiniteField.frobeniusAlgEquivOfAlgebraic K E ^ m) w : E) : L) =
        (fun z : L => z ^ Fintype.card K)^[m] (w : L) := by
      intro m
      induction m with
      | zero => intro w; rfl
      | succ m ih =>
        intro w
        rw [pow_succ, AlgEquiv.mul_apply, ih, Function.iterate_succ_apply]
        congr 1
        all_goals (try rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic])
        all_goals (try simp)
    simp only at hσ
    have h2 : ((σ ⟨x, hxE⟩ : E) : L) = y := by
      rw [← AlgEquiv.smul_def, hσ]
    simp only at hn
    rw [← hn, key] at h2
    exact ⟨_, h2⟩
  · have hsep : f.Separable := by
      first
      | exact PerfectField.separable_of_irreducible hirr
      | (haveI : PerfectField K := PerfectField.ofFinite
         exact PerfectField.separable_of_irreducible hirr)
    rw [Multiset.toFinset_card_of_nodup (nodup_roots (hsep.map (f := algebraMap K L)))]
    show Multiset.card (f.map (algebraMap K L)).roots = f.natDegree
    rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
