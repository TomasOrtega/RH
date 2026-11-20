import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeBasisAdaptedToSubspaceStatement

namespace GlobalTheory.CompanionTheory.Ar.Crv.SubQuot

open GlobalTheory.CompanionTheory.Ar.Crv

variable {K : Type} [Field K] (C : ACurve K)

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Substitute `ha` using the available equality. Simplify using the standard rewrite rules. Use `(C.fin a ha).subset ?_` and prove the remaining obligations. Introduce `i hi`.

Simplify using `only [Set.mem_setOf_eq] at hi ⊢`. Introduce `h`. Conclude with `hi (le_of_eq h)`.
-/
theorem finite_not_le_one (a : K) : {i | ¬ C.v i a ≤ 1}.Finite := by
  by_cases ha : a = 0
  · subst ha
    simp
  · refine (C.fin a ha).subset ?_
    intro i hi
    simp only [Set.mem_setOf_eq] at hi ⊢
    intro h
    exact hi (le_of_eq h)

/- English proof (translation)
Use `(Set.finite_iUnion fun q : Fin m => Set.finite_iUnion fun r : Fin n => finite_not_le_one C (b'.repr (f (b r)) q)).subset ?_` and prove the remaining obligations. Introduce `i hi`. Simplify using `only [Set.mem_setOf_eq] at hi`. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq]`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Apply `hi` to reduce the goal to its premises. Introduce `x hx q`. Establish `hx' : f x = ∑ r, b.repr x r • f (b r)` using `by conv_lhs => rw [← b.sum_repr x]`. Rewrite using `[map_sum]`.

Simplify using `only [map_smul]`. Rewrite using `[hx', map_sum, Finsupp.finset_sum_apply]`. Use `(C.v i).map_sum_le fun r _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul, (C.v i).map_mul]`. Conclude with `mul_le_one' (hx r) (hcon q r)`.
-/
theorem finite_not_mapsTo {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] {n m : ℕ} (b : Module.Basis (Fin n) K V) (b' : Module.Basis (Fin m) K V')
    (f : V →ₗ[K] V') :
    {i | ¬ ∀ x, (∀ q, C.v i (b.repr x q) ≤ 1) → ∀ q, C.v i (b'.repr (f x) q) ≤ 1}.Finite := by
  classical
  refine (Set.finite_iUnion fun q : Fin m => Set.finite_iUnion fun r : Fin n =>
    finite_not_le_one C (b'.repr (f (b r)) q)).subset ?_
  intro i hi
  simp only [Set.mem_setOf_eq] at hi
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  by_contra hcon
  push_neg at hcon
  apply hi
  intro x hx q
  have hx' : f x = ∑ r, b.repr x r • f (b r) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    simp only [map_smul]
  rw [hx', map_sum, Finsupp.finset_sum_apply]
  refine (C.v i).map_sum_le fun r _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, (C.v i).map_mul]
  exact mul_le_one' (hx r) (hcon q r)

/- English proof (translation)
Introduce `K _ C V _ _ _ L W hL`. Unfold `IsBun at hL ⊢`. Take `⟨hloc, b0, hb0⟩` from `hL`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective W.subtype W.ker_subtype`. Take `⟨s, hs⟩` from `LinearMap.exists_rightInverse_of_surjective W.mkQ W.range_mkQ`.

Use `⟨⟨fun i => ?_, Module.finBasis K W, ?_⟩, ⟨fun i => ?_, Module.finBasis K (V ⧸ W), ?_⟩⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `hloc i`. Take `⟨bW, bQ, b', -, hW, -, -, -⟩` from `GlobalTheory.T.lattice_basis_adapted_to_subspace K C V i _ b (L i) W hb`. Conclude with `⟨bW, hW⟩`. Use `((hb0.union (finite_not_mapsTo C (Module.finBasis K W) b0 W.subtype)).union (finite_not_mapsTo C b0 (Module.finBasis K W) g)).subset ?_` and prove the remaining obligations.

Introduce `i hi`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq] at hi ⊢`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨⟨h1, h2⟩, h3⟩` from `hcon`.

Apply `hi` to reduce the goal to its premises. Unfold `IsLatOf at h1 ⊢`. Introduce `w`. Use `show (w : V) ∈ L i ↔ _`. Rewrite using `[h1]`.

Establish `hgw : g (w : V) = w` using `by simpa using LinearMap.congr_fun hg w`. Prove the components needed by the constructor for the conclusion. Introduce `hw q`. Establish `hq` using `h3 (w : V) hw q`. Rewrite `hq` using `[hgw]`. Then use the resulting hypothesis.

Introduce `hw q`. Conclude with `h2 w hw q`. Take `⟨b, hb⟩` from `hloc i`. Take `⟨bW, bQ, b', -, -, hQ, -, -⟩` from `GlobalTheory.T.lattice_basis_adapted_to_subspace K C V i _ b (L i) W hb`. Conclude with `⟨bQ, hQ⟩`.

Use `((hb0.union (finite_not_mapsTo C b0 (Module.finBasis K (V ⧸ W)) W.mkQ)).union (finite_not_mapsTo C (Module.finBasis K (V ⧸ W)) b0 s)).subset ?_` and prove the remaining obligations. Introduce `i hi`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq] at hi ⊢`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Take `⟨⟨h1, h2⟩, h3⟩` from `hcon`. Apply `hi` to reduce the goal to its premises. Unfold `IsLatOf at h1 ⊢`. Introduce `y`. Use `show y ∈ (L i).map W.mkQ.toAddMonoidHom ↔ _`.

Rewrite using `[AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩ q`. Conclude with `h2 x ((h1 x).1 hx) q`. Introduce `hy`.

Establish `hsy : W.mkQ (s y) = y` using `by simpa using LinearMap.congr_fun hs y`. Conclude with `⟨s y, (h1 (s y)).2 (h3 y hy), hsy⟩`.
-/
theorem isBun_sub_quot : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (W : Submodule K V),
    IsBun C L → IsBun C (sub C L W) ∧ IsBun C (quot C L W) := by
  intro K _ C V _ _ _ L W hL
  unfold IsBun at hL ⊢
  obtain ⟨hloc, b0, hb0⟩ := hL
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective W.subtype W.ker_subtype
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective W.mkQ W.range_mkQ
  refine ⟨⟨fun i => ?_, Module.finBasis K W, ?_⟩, ⟨fun i => ?_, Module.finBasis K (V ⧸ W), ?_⟩⟩
  · obtain ⟨b, hb⟩ := hloc i
    obtain ⟨bW, bQ, b', -, hW, -, -, -⟩ := GlobalTheory.T.lattice_basis_adapted_to_subspace K C V i _ b (L i) W hb
    exact ⟨bW, hW⟩
  · refine ((hb0.union (finite_not_mapsTo C (Module.finBasis K W) b0 W.subtype)).union
      (finite_not_mapsTo C b0 (Module.finBasis K W) g)).subset ?_
    intro i hi
    simp only [Set.mem_union, Set.mem_setOf_eq] at hi ⊢
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    apply hi
    unfold IsLatOf at h1 ⊢
    intro w
    show (w : V) ∈ L i ↔ _
    rw [h1]
    have hgw : g (w : V) = w := by simpa using LinearMap.congr_fun hg w
    constructor
    · intro hw q
      have hq := h3 (w : V) hw q
      rwa [hgw] at hq
    · intro hw q
      exact h2 w hw q
  · obtain ⟨b, hb⟩ := hloc i
    obtain ⟨bW, bQ, b', -, -, hQ, -, -⟩ := GlobalTheory.T.lattice_basis_adapted_to_subspace K C V i _ b (L i) W hb
    exact ⟨bQ, hQ⟩
  · refine ((hb0.union (finite_not_mapsTo C b0 (Module.finBasis K (V ⧸ W)) W.mkQ)).union
      (finite_not_mapsTo C (Module.finBasis K (V ⧸ W)) b0 s)).subset ?_
    intro i hi
    simp only [Set.mem_union, Set.mem_setOf_eq] at hi ⊢
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    apply hi
    unfold IsLatOf at h1 ⊢
    intro y
    show y ∈ (L i).map W.mkQ.toAddMonoidHom ↔ _
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩ q
      exact h2 x ((h1 x).1 hx) q
    · intro hy
      have hsy : W.mkQ (s y) = y := by simpa using LinearMap.congr_fun hs y
      exact ⟨s y, (h1 (s y)).2 (h3 y hy), hsy⟩

end GlobalTheory.CompanionTheory.Ar.Crv.SubQuot
