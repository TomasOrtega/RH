import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement

open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

namespace AdmissibleFiniteSupport

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

end AdmissibleFiniteSupport

open NumberField in
open scoped TensorProduct in
attribute [local instance] _root_.ReciprocityTheory.ChartRestriction.G.T0.resAlg in
/- English proof (translation)
Use `set E := IntermediateField.adjoin k s`. Use `set s' : Set E := Subtype.val ⁻¹' s`. Establish `himg : E.val '' s' = s`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `hy`. Introduce `hz`. Conclude with `⟨⟨z, IntermediateField.subset_adjoin k s hz⟩, hz, rfl⟩`. Establish `hmem : ∀ x : E, x ∈ IntermediateField.adjoin k s'`.

Introduce `x`. Establish `hmap : (IntermediateField.adjoin k s').map E.val = E`. Rewrite using `[IntermediateField.adjoin_map, himg]`. Establish `hx : (x : L) ∈ (IntermediateField.adjoin k s').map E.val`. Rewrite using `[hmap]`.

Conclude with `x.2`. Take `⟨y, hy, hyx⟩` from `hx`. Establish `hyx' : y = x` using `Subtype.ext hyx`. Rewrite using `[← hyx']` and apply the resulting hypothesis. Rewrite using `[← IntermediateField.isAlgebraic_adjoin_iff_top]`.

Conclude with `⟨fun x => isAlgebraic_algebraMap (⟨x, hmem x⟩ : IntermediateField.adjoin k s')⟩`.
-/
private lemma isAlgebraic_adjoin_adjoin_preimage {k L : Type} [Field k] [Field L] [Algebra k L]
    (s : Set L) :
    Algebra.IsAlgebraic (Algebra.adjoin k (Subtype.val ⁻¹' s : Set (IntermediateField.adjoin k s)))
      (IntermediateField.adjoin k s) := by
  set E := IntermediateField.adjoin k s
  set s' : Set E := Subtype.val ⁻¹' s
  have himg : E.val '' s' = s := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hz
      exact ⟨⟨z, IntermediateField.subset_adjoin k s hz⟩, hz, rfl⟩
  have hmem : ∀ x : E, x ∈ IntermediateField.adjoin k s' := by
    intro x
    have hmap : (IntermediateField.adjoin k s').map E.val = E := by
      rw [IntermediateField.adjoin_map, himg]
    have hx : (x : L) ∈ (IntermediateField.adjoin k s').map E.val := by
      rw [hmap]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : y = x := Subtype.ext hyx
    rwa [← hyx']
  rw [← IntermediateField.isAlgebraic_adjoin_iff_top]
  exact ⟨fun x => isAlgebraic_algebraMap (⟨x, hmem x⟩ : IntermediateField.adjoin k s')⟩

open NumberField in
open scoped TensorProduct in
attribute [local instance] _root_.ReciprocityTheory.ChartRestriction.G.T0.resAlg in
/- English proof (translation)
Proceed by induction on `a with`. Consider the case `top => exact absurd h (by simp)`. Consider the case `coe z`. Establish `hz : z < 0` using `by exact_mod_cast h`. Establish `hneg : (-(z : WithTop ℤ)) = ((-z : ℤ) : WithTop ℤ)` using `rfl`.

Rewrite using `[hneg]`. Conclude with `(by omega : (0 : ℤ) ≤ -z)` after adjusting the coercions.
-/
private lemma withTop_int_neg_nonneg_of_neg {a : WithTop ℤ} (h : a < 0) : 0 ≤ -a := by
  induction a with
  | top => exact absurd h (by simp)
  | coe z =>
    have hz : z < 0 := by exact_mod_cast h
    have hneg : (-(z : WithTop ℤ)) = ((-z : ℤ) : WithTop ℤ) := rfl
    rw [hneg]
    exact_mod_cast (by omega : (0 : ℤ) ≤ -z)

open NumberField in
open scoped TensorProduct in
attribute [local instance] _root_.ReciprocityTheory.ChartRestriction.G.T0.resAlg in
/- English proof (translation)
Use `set F := IntermediateField.adjoin K (Set.range x)`. Set `x' : Fin n → F` to `fun i => ⟨x i, IntermediateField.subset_adjoin K _ (Set.mem_range_self i)⟩`. Establish `hx' : AlgebraicIndependent K x'` using `AlgebraicIndependent.of_comp F.val hx`. Establish `hrange : Set.range x' = Subtype.val ⁻¹' Set.range x`. Use extensionality with `z`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`. Conclude with `⟨i, rfl⟩`. Introduce and unpack `⟨i, hi⟩`. Conclude with `⟨i, Subtype.ext hi⟩`.

Establish `hbasis : IsTranscendenceBasis K x'` using `isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.2 ⟨hx', by rw [hrange]; exact isAlgebraic_adjoin_adjoin_preimage _⟩`. Establish `hKF : Algebra.trdeg K F = n` using `by rw [← hbasis.cardinalMk_eq_trdeg]; simp`. Establish `hsum` using `trdeg_add_eq K F (A := Ω)`. Rewrite `hsum` using `[hKF, htr, ← hD]`. Establish `hFΩ : Algebra.trdeg F Ω = 1`.

Establish `hlt : Algebra.trdeg F Ω < Cardinal.aleph0`. Establish `h` using `Cardinal.nat_lt_aleph0 (n + 1)`. Rewrite `h` using `[← hsum]`. Conclude with `lt_of_le_of_lt le_add_self h`. Take `⟨m, hm⟩` from `Cardinal.lt_aleph0.1 hlt`.

Rewrite `hsum`, the goal using `[hm]`. Normalize the coercions in `at hsum ⊢`. Use linear arithmetic over natural numbers and integers. Use `haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective`. Establish `hfgF : (⊤ : IntermediateField F Ω).FG` using `IntermediateField.FG.of_restrictScalars (K := K) (by rw [IntermediateField.restrictScalars_top]; exact hfg)`.

Establish `hnalg : ¬ Algebra.IsAlgebraic F Ω`. Rewrite using `[← trdeg_eq_zero_iff, hFΩ]`. Conclude with `one_ne_zero`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t : Ω, Transcendental F t := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hnalg ⟨fun a => not_not.1 (h a)⟩`. Establish `htinv : Transcendental F t⁻¹` using `fun h => ht (by simpa using h.inv)`. Use `((H2 F Ω t hfgF hFΩ ht g hg).union (H2 F Ω t⁻¹ hfgF hFΩ htinv g hg)).subset ?_` and prove the remaining obligations. Introduce and unpack `v ⟨hdisc, hvg, htriv, hxv, hind⟩`.

Establish `hpoly : ∀ P : MvPolynomial (Fin n) K, MvPolynomial.aeval x P ≠ 0 → v (MvPolynomial.aeval x P) = 0`. Introduce `P hP`. Establish `hP0 : P ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hP`.

Take `⟨c, hc, hcv⟩` from `_root_.ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.exists_val_coeff v x hxv hind P hP0`. Rewrite using `[hcv, htriv c hc]`. Establish `hF : _root_.ReciprocityTheory.ChartRestriction.G.T0.IsTrivOn F v`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.T0.IsTrivOn`. Introduce `a ha`.

Take `⟨P, Q, hPQ⟩` from `(IntermediateField.mem_adjoin_range_iff K x a).1 a.2`. Establish `ha' : (a : Ω) ≠ 0` using `by exact_mod_cast ha`. Rewrite `ha'` using `[hPQ]`. Establish `hQ : MvPolynomial.aeval x Q ≠ 0` using `fun h => ha' (by rw [h, div_zero])`. Establish `hP : MvPolynomial.aeval x P ≠ 0` using `fun h => ha' (by rw [h, zero_div])`.

Use `show v (a : Ω) = 0`. Rewrite using `[hPQ, div_eq_mul_inv, v.map_mul, v.map_inv, hpoly P hP, hpoly Q hQ]`. Simplify using the standard rewrite rules. Distinguish the cases in `hvt : 0 ≤ v t`. Conclude with `Or.inl ⟨hdisc, hF, hvt, hvg⟩`.

Use `right`. Use `⟨hdisc, hF, ?_, hvg⟩` and prove the remaining obligations. Rewrite using `[v.map_inv]`. Use `push_neg at hvt`. Conclude with `withTop_int_neg_nonneg_of_neg hvt`.
-/
private lemma case_two_finite_lemma
    (H2 : ∀ (F Ω : Type) [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (t : Ω), (⊤ : IntermediateField F Ω).FG → Algebra.trdeg F Ω = 1 → Transcendental F t → ∀ g : Ω, g ≠ 0 → {v : AddValuation Ω (WithTop ℤ) | _root_.ReciprocityTheory.ChartRestriction.G.T0.IsNormDiscrete v ∧ _root_.ReciprocityTheory.ChartRestriction.G.T0.IsTrivOn F v ∧ 0 ≤ v t ∧ v g ≠ 0}.Finite)
    {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {n D : ℕ} (hD : n + 1 = D)
    (hfg : (⊤ : IntermediateField K Ω).FG) (htr : Algebra.trdeg K Ω = D) (x : Fin n → Ω)
    (hx : AlgebraicIndependent K x) (g : Ω) (hg : g ≠ 0) :
    {v : AddValuation Ω (WithTop ℤ) | _root_.ReciprocityTheory.ChartRestriction.G.T0.IsNormDiscrete v ∧ v g ≠ 0 ∧
      (∀ a : K, a ≠ 0 → v (algebraMap K Ω a) = 0) ∧ ∃ hxv : ∀ i, x i ∈ _root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v,
        AlgebraicIndependent (IsLocalRing.ResidueField ((_root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v).comap (algebraMap K Ω)))
          fun i => IsLocalRing.residue (_root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v) ⟨x i, hxv i⟩}.Finite := by
  classical
  set F := IntermediateField.adjoin K (Set.range x)
  let x' : Fin n → F := fun i => ⟨x i, IntermediateField.subset_adjoin K _ (Set.mem_range_self i)⟩
  have hx' : AlgebraicIndependent K x' := AlgebraicIndependent.of_comp F.val hx
  have hrange : Set.range x' = Subtype.val ⁻¹' Set.range x := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  have hbasis : IsTranscendenceBasis K x' :=
    isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.2
      ⟨hx', by rw [hrange]; exact isAlgebraic_adjoin_adjoin_preimage _⟩
  have hKF : Algebra.trdeg K F = n := by rw [← hbasis.cardinalMk_eq_trdeg]; simp
  have hsum := trdeg_add_eq K F (A := Ω)
  rw [hKF, htr, ← hD] at hsum
  have hFΩ : Algebra.trdeg F Ω = 1 := by
    have hlt : Algebra.trdeg F Ω < Cardinal.aleph0 := by
      have h := Cardinal.nat_lt_aleph0 (n + 1)
      rw [← hsum] at h
      exact lt_of_le_of_lt le_add_self h
    obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 hlt
    rw [hm] at hsum ⊢
    norm_cast at hsum ⊢
    omega
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have hfgF : (⊤ : IntermediateField F Ω).FG :=
    IntermediateField.FG.of_restrictScalars (K := K) (by rw [IntermediateField.restrictScalars_top]; exact hfg)
  have hnalg : ¬ Algebra.IsAlgebraic F Ω := by
    rw [← trdeg_eq_zero_iff, hFΩ]
    exact one_ne_zero
  obtain ⟨t, ht⟩ : ∃ t : Ω, Transcendental F t := by
    by_contra h
    push_neg at h
    exact hnalg ⟨fun a => not_not.1 (h a)⟩
  have htinv : Transcendental F t⁻¹ := fun h => ht (by simpa using h.inv)
  refine ((H2 F Ω t hfgF hFΩ ht g hg).union (H2 F Ω t⁻¹ hfgF hFΩ htinv g hg)).subset ?_
  rintro v ⟨hdisc, hvg, htriv, hxv, hind⟩
  have hpoly : ∀ P : MvPolynomial (Fin n) K, MvPolynomial.aeval x P ≠ 0 →
      v (MvPolynomial.aeval x P) = 0 := by
    intro P hP
    have hP0 : P ≠ 0 := by
      rintro rfl
      simp at hP
    obtain ⟨c, hc, hcv⟩ := _root_.ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.exists_val_coeff v x hxv hind P hP0
    rw [hcv, htriv c hc]
  have hF : _root_.ReciprocityTheory.ChartRestriction.G.T0.IsTrivOn F v := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.T0.IsTrivOn
    intro a ha
    obtain ⟨P, Q, hPQ⟩ := (IntermediateField.mem_adjoin_range_iff K x a).1 a.2
    have ha' : (a : Ω) ≠ 0 := by exact_mod_cast ha
    rw [hPQ] at ha'
    have hQ : MvPolynomial.aeval x Q ≠ 0 := fun h => ha' (by rw [h, div_zero])
    have hP : MvPolynomial.aeval x P ≠ 0 := fun h => ha' (by rw [h, zero_div])
    show v (a : Ω) = 0
    rw [hPQ, div_eq_mul_inv, v.map_mul, v.map_inv, hpoly P hP, hpoly Q hQ]
    simp
  by_cases hvt : 0 ≤ v t
  · exact Or.inl ⟨hdisc, hF, hvt, hvg⟩
  · right
    refine ⟨hdisc, hF, ?_, hvg⟩
    rw [v.map_inv]
    push_neg at hvt
    exact withTop_int_neg_nonneg_of_neg hvt

open NumberField in
open scoped TensorProduct in
attribute [local instance] _root_.ReciprocityTheory.ChartRestriction.G.T0.resAlg in
/- English proof (translation)
Use `set E := IntermediateField.adjoin k s`. Use `set s' : Set E := Subtype.val ⁻¹' s`. Establish `himg : E.val '' s' = s`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `hy`. Introduce `hz`. Conclude with `⟨⟨z, IntermediateField.subset_adjoin k s hz⟩, hz, rfl⟩`. Establish `hmem : ∀ x : E, x ∈ IntermediateField.adjoin k s'`.

Introduce `x`. Establish `hmap : (IntermediateField.adjoin k s').map E.val = E`. Rewrite using `[IntermediateField.adjoin_map, himg]`. Establish `hx : (x : L) ∈ (IntermediateField.adjoin k s').map E.val`. Rewrite using `[hmap]`.

Conclude with `x.2`. Take `⟨y, hy, hyx⟩` from `hx`. Establish `hyx' : y = x` using `Subtype.ext hyx`. Rewrite using `[← hyx']` and apply the resulting hypothesis. Establish `hE : Algebra.IsAlgebraic (Algebra.adjoin k s') E`.

Rewrite using `[← IntermediateField.isAlgebraic_adjoin_iff_top]`. Conclude with `⟨fun x => isAlgebraic_algebraMap (⟨x, hmem x⟩ : IntermediateField.adjoin k s')⟩`. Take `⟨t, hts, ht⟩` from `exists_isTranscendenceBasis_subset (R := k) s'`. Establish `hcard` using `ht.cardinalMk_eq_trdeg`. Rewrite `hcard` using `[h]`.

Establish `hfin : Finite t` using `Cardinal.lt_aleph0_iff_finite.1 (by rw [hcard]; exact Cardinal.nat_lt_aleph0 D)`. Establish `hnc : Nat.card t = D` using `by simp [Nat.card, hcard]`. Set `e : Fin D ≃ t` to `(finCongr hnc.symm).trans (Finite.equivFin t).symm`. Use `⟨fun i => ((e i : E) : L), fun i => hts (e i).2, ?_⟩` and prove the remaining obligations. Conclude with `(ht.1.comp e e.injective).map' (f := E.val) Subtype.val_injective`.
-/
private lemma exists_algebraicIndependent_fin_of_trdeg_adjoin_eq {k L : Type} [Field k] [Field L] [Algebra k L] (s : Set L) (D : ℕ)
    (h : Algebra.trdeg k (IntermediateField.adjoin k s) = D) :
    ∃ y : Fin D → L, (∀ i, y i ∈ s) ∧ AlgebraicIndependent k y := by
  set E := IntermediateField.adjoin k s
  set s' : Set E := Subtype.val ⁻¹' s
  have himg : E.val '' s' = s := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hz
      exact ⟨⟨z, IntermediateField.subset_adjoin k s hz⟩, hz, rfl⟩
  have hmem : ∀ x : E, x ∈ IntermediateField.adjoin k s' := by
    intro x
    have hmap : (IntermediateField.adjoin k s').map E.val = E := by
      rw [IntermediateField.adjoin_map, himg]
    have hx : (x : L) ∈ (IntermediateField.adjoin k s').map E.val := by
      rw [hmap]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : y = x := Subtype.ext hyx
    rwa [← hyx']
  have hE : Algebra.IsAlgebraic (Algebra.adjoin k s') E := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top]
    exact ⟨fun x => isAlgebraic_algebraMap (⟨x, hmem x⟩ : IntermediateField.adjoin k s')⟩
  obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := k) s'
  have hcard := ht.cardinalMk_eq_trdeg
  rw [h] at hcard
  have hfin : Finite t :=
    Cardinal.lt_aleph0_iff_finite.1 (by rw [hcard]; exact Cardinal.nat_lt_aleph0 D)
  have hnc : Nat.card t = D := by simp [Nat.card, hcard]
  let e : Fin D ≃ t := (finCongr hnc.symm).trans (Finite.equivFin t).symm
  refine ⟨fun i => ((e i : E) : L), fun i => hts (e i).2, ?_⟩
  exact (ht.1.comp e e.injective).map' (f := E.val) Subtype.val_injective

open NumberField in
open scoped TensorProduct in
attribute [local instance] _root_.ReciprocityTheory.ChartRestriction.G.T0.resAlg in
/- English proof (translation)
Unfold `_root_.ReciprocityTheory.ChartRestriction.G.T0.vRing`. Conclude with `Iff.rfl`.
-/
private lemma mem_vRing_iff_nonneg {Ω : Type} [Field Ω] (v : AddValuation Ω (WithTop ℤ)) (x : Ω) :
    x ∈ _root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v ↔ 0 ≤ v x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.T0.vRing
  exact Iff.rfl

open NumberField in
open scoped TensorProduct in
attribute [local instance] _root_.ReciprocityTheory.ChartRestriction.G.T0.resAlg in
/- English proof (translation)
Rewrite using `[← mem_vRing_iff_nonneg]`. Establish `hint : IsIntegral ℤ (algebraMap K Ω a)` using `(a.2.map (IsScalarTower.toAlgHom ℤ K Ω))`. Establish `h2 : IsIntegral (_root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v) (algebraMap K Ω a)` using `hint.tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h2`. Rewrite using `[← hy]`.

Conclude with `y.2`.
-/
private lemma addValuation_algebraMap_ringOfIntegers_nonneg {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (v : AddValuation Ω (WithTop ℤ)) (a : 𝓞 K) : 0 ≤ v (algebraMap K Ω a) := by
  rw [← mem_vRing_iff_nonneg]
  have hint : IsIntegral ℤ (algebraMap K Ω a) := (a.2.map (IsScalarTower.toAlgHom ℤ K Ω))
  have h2 : IsIntegral (_root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v) (algebraMap K Ω a) := hint.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  rw [← hy]
  exact y.2

open NumberField in
open scoped TensorProduct in
attribute [local instance] _root_.ReciprocityTheory.ChartRestriction.G.T0.resAlg in
/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `lt_of_lt_of_le (lt_min (h a (Finset.mem_insert_self a s)) (ih fun m hm => h m (Finset.mem_insert_of_mem hm))) (v.map_add _ _)`.
-/
private lemma addValuation_sum_pos_of_forall_pos {Ω α : Type} [Field Ω] (v : AddValuation Ω (WithTop ℤ)) (g : α → Ω)
    (s : Finset α) (h : ∀ m ∈ s, 0 < v (g m)) : 0 < v (∑ m ∈ s, g m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact lt_of_lt_of_le (lt_min (h a (Finset.mem_insert_self a s))
      (ih fun m hm => h m (Finset.mem_insert_of_mem hm))) (v.map_add _ _)

open NumberField in
open scoped TensorProduct in
attribute [local instance] _root_.ReciprocityTheory.ChartRestriction.G.T0.resAlg in
/- English proof (translation)
Establish `hsum` using `MvPolynomial.eval₂_eq' ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)) x p`. Establish `hmono : ∀ m : Fin D →₀ ℕ, 0 ≤ v (∏ i, x i ^ m i)` using `fun m => by`. Rewrite using `[← mem_vRing_iff_nonneg]`. Conclude with `prod_mem fun i _ => pow_mem (hx i) _`. Use `⟨?_, ⟨fun hpos => ?_, fun hcoeff => ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[hsum, ← mem_vRing_iff_nonneg]`. Use `sum_mem fun m _ => mul_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mem_vRing_iff_nonneg]`. Conclude with `addValuation_algebraMap_ringOfIntegers_nonneg v _`. Rewrite using `[mem_vRing_iff_nonneg]`.

Conclude with `hmono m`. Assume the negation of the conclusion as `hnot push_neg at hnot`. Take `⟨m, hm⟩` from `hnot`. Use `set a := p.coeff m`. Establish `ha0 : v (algebraMap K Ω a) = 0` using `le_antisymm (not_lt.1 fun h => hm ((hla a).1 h)) (addValuation_algebraMap_ringOfIntegers_nonneg v a)`.

Establish `hane : (a : K) ≠ 0`. Introduce `h`. Apply `hm` to reduce the goal to its premises. Establish `: a = 0` using `by exact_mod_cast h`. Rewrite using `[this]`.

Conclude with `zero_mem _`. Use `set P : MvPolynomial (Fin D) K := MvPolynomial.C (a : K)⁻¹ * MvPolynomial.map (algebraMap (𝓞 K) K) p`. Establish `hcoeffP : ∀ β, MvPolynomial.coeff β P = (a : K)⁻¹ * p.coeff β` using `fun β => by`. Simplify using `[P, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]`. Establish `hnn : ∀ β, 0 ≤ v (algebraMap K Ω (MvPolynomial.coeff β P))` using `fun β => by`.

Rewrite using `[hcoeffP, map_mul, v.map_mul, map_inv₀, v.map_inv, ha0, neg_zero, zero_add]`. Conclude with `addValuation_algebraMap_ringOfIntegers_nonneg v _`. Establish `h1 : MvPolynomial.coeff m P = 1` using `by rw [hcoeffP]; exact inv_mul_cancel₀ hane`. Establish `hzero` using `_root_.ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.val_eval_eq_zero v x hx hind P hnn m h1`. Establish `heval : MvPolynomial.eval₂ ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)) x p = algebraMap K Ω a * MvPolynomial.aeval x P`.

Simplify using `only [P, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_map_algebraMap]`. Rewrite using `[← mul_assoc, ← map_mul, mul_inv_cancel₀ hane, map_one, one_mul]`. Both sides reduce to the same expression. Rewrite `hpos` using `[heval, v.map_mul, ha0, hzero, add_zero]`. Conclude with `lt_irrefl _ hpos`.

Rewrite using `[hsum]`. Use `addValuation_sum_pos_of_forall_pos v _ _ fun m _ => ?_` and prove the remaining obligations. Rewrite using `[v.map_mul]`. Conclude with `lt_of_lt_of_le ((hla _).2 (hcoeff m)) (le_add_of_nonneg_right (hmono m))`.
-/
private lemma polynomial_value_over_prime_lemma_4 {K Ω : Type} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] {D : ℕ} (v : AddValuation Ω (WithTop ℤ))
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hla : ∀ a : 𝓞 K, 0 < v (algebraMap K Ω a) ↔ a ∈ la.asIdeal)
    (x : Fin D → Ω) (hx : ∀ i, x i ∈ _root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v)
    (hind : AlgebraicIndependent (IsLocalRing.ResidueField ((_root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v).comap (algebraMap K Ω)))
      fun i => IsLocalRing.residue (_root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v) ⟨x i, hx i⟩)
    (p : MvPolynomial (Fin D) (𝓞 K)) :
    0 ≤ v (MvPolynomial.eval₂ ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)) x p) ∧
      (0 < v (MvPolynomial.eval₂ ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)) x p) ↔
        ∀ m, p.coeff m ∈ la.asIdeal) := by
  have hsum := MvPolynomial.eval₂_eq' ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)) x p
  have hmono : ∀ m : Fin D →₀ ℕ, 0 ≤ v (∏ i, x i ^ m i) := fun m => by
    rw [← mem_vRing_iff_nonneg]
    exact prod_mem fun i _ => pow_mem (hx i) _
  refine ⟨?_, ⟨fun hpos => ?_, fun hcoeff => ?_⟩⟩
  · rw [hsum, ← mem_vRing_iff_nonneg]
    refine sum_mem fun m _ => mul_mem ?_ ?_
    · rw [mem_vRing_iff_nonneg]; exact addValuation_algebraMap_ringOfIntegers_nonneg v _
    · rw [mem_vRing_iff_nonneg]; exact hmono m
  · by_contra hnot
    push_neg at hnot
    obtain ⟨m, hm⟩ := hnot
    set a := p.coeff m
    have ha0 : v (algebraMap K Ω a) = 0 :=
      le_antisymm (not_lt.1 fun h => hm ((hla a).1 h)) (addValuation_algebraMap_ringOfIntegers_nonneg v a)
    have hane : (a : K) ≠ 0 := by
      intro h
      apply hm
      have : a = 0 := by exact_mod_cast h
      rw [this]; exact zero_mem _
    set P : MvPolynomial (Fin D) K :=
      MvPolynomial.C (a : K)⁻¹ * MvPolynomial.map (algebraMap (𝓞 K) K) p
    have hcoeffP : ∀ β, MvPolynomial.coeff β P = (a : K)⁻¹ * p.coeff β := fun β => by
      simp [P, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
    have hnn : ∀ β, 0 ≤ v (algebraMap K Ω (MvPolynomial.coeff β P)) := fun β => by
      rw [hcoeffP, map_mul, v.map_mul, map_inv₀, v.map_inv, ha0, neg_zero, zero_add]
      exact addValuation_algebraMap_ringOfIntegers_nonneg v _
    have h1 : MvPolynomial.coeff m P = 1 := by rw [hcoeffP]; exact inv_mul_cancel₀ hane
    have hzero := _root_.ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.val_eval_eq_zero v x hx hind P hnn m h1
    have heval : MvPolynomial.eval₂ ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)) x p =
        algebraMap K Ω a * MvPolynomial.aeval x P := by
      simp only [P, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_map_algebraMap]
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hane, map_one, one_mul]
      rfl
    rw [heval, v.map_mul, ha0, hzero, add_zero] at hpos
    exact lt_irrefl _ hpos
  · rw [hsum]
    refine addValuation_sum_pos_of_forall_pos v _ _ fun m _ => ?_
    rw [v.map_mul]
    exact lt_of_lt_of_le ((hla _).2 (hcoeff m)) (le_add_of_nonneg_right (hmono m))

open NumberField in
open scoped TensorProduct in
attribute [local instance] _root_.ReciprocityTheory.ChartRestriction.G.T0.resAlg in

/- English proof (translation)
Introduce `H1 H2 K _ _ ι _ Ω _ _ WT _ A _ _ _ _ 𝒜 d c hD hfg htr hrk hwL hjc hT`. Establish `hfin : ∀ g : Ω c, g ≠ 0 → {v | d.admitted c v ∧ v g ≠ 0}.Finite`. Introduce `g hg`. Use `set r : Fin (d.N + 1) → Fin (d.N + 1) → Ω c := fun j j0 => _root_.ReciprocityTheory.ChartRestriction.G.T0.ratio (d.w j c) (d.w j0 c)`. Establish `hfin1` using `Set.finite_iUnion fun j0 : Fin (d.N + 1) => Set.finite_iUnion fun σ : Fin d.D → Fin (d.N + 1) => H1 K (Ω c) d.D (fun i => r (σ i) j0) hfg htr g hg`.

Establish `hfin2` using `Set.finite_iUnion fun p : {p : Fin (d.N + 1) × (Fin (d.D - 1) → Fin (d.N + 1)) // AlgebraicIndependent K fun i => r (p.2 i) p.1} => case_two_finite_lemma H2 (Nat.sub_add_cancel hD) hfg htr _ p.2 g hg`. Use `(hfin1.union hfin2).subset ?_` and prove the remaining obligations. Introduce and unpack `v ⟨hv, hvg⟩`. Establish `hv'` using `hv`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.T0.Data.admitted at hv'`.

Take `⟨hdisc, ⟨la, hla, hres⟩ | ⟨htriv, hres⟩⟩` from `hv'`. Use `left`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.T0.Data.ResCond at hres`. Take `⟨-, j0, -, hint, htd⟩` from `hres`. Take `⟨y, hy, hind⟩` from `exists_algebraicIndependent_fin_of_trdeg_adjoin_eq _ _ htd`.

Use `choose σ hσ hyσ using hy`. Use `Set.mem_iUnion.2 ⟨j0, Set.mem_iUnion.2 ⟨σ, hdisc, hvg, la, ?_⟩⟩` and prove the remaining obligations. Establish `hx : ∀ i, r (σ i) j0 ∈ _root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v` using `fun i => (mem_vRing_iff_nonneg v _).2 (hint (σ i))`. Establish `hind' : AlgebraicIndependent (IsLocalRing.ResidueField ((_root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v).comap (algebraMap K (Ω c)))) fun i => IsLocalRing.residue (_root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v) ⟨r (σ i) j0, hx i⟩`. Establish `hfun : (fun i => IsLocalRing.residue (_root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v) ⟨r (σ i) j0, hx i⟩) = y`.

Use function extensionality and compare the values at `fun i => by rw [hyσ i]`. Rewrite using `[hfun]`. Conclude with `hind`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.T0.IsOver at hla`. Conclude with `polynomial_value_over_prime_lemma_4 v la hla _ hx hind'`.

Use `right`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.T0.Data.ResCond at hres`. Take `⟨-, j0, -, hint, htd⟩` from `hres`. Take `⟨y, hy, hind⟩` from `exists_algebraicIndependent_fin_of_trdeg_adjoin_eq _ _ htd`. Use `choose σ hσ hyσ using hy`.

Establish `hx : ∀ i, r (σ i) j0 ∈ _root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v` using `fun i => (mem_vRing_iff_nonneg v _).2 (hint (σ i))`. Establish `hind' : AlgebraicIndependent (IsLocalRing.ResidueField ((_root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v).comap (algebraMap K (Ω c)))) fun i => IsLocalRing.residue (_root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v) ⟨r (σ i) j0, hx i⟩`. Establish `hfun : (fun i => IsLocalRing.residue (_root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v) ⟨r (σ i) j0, hx i⟩) = y`. Use function extensionality and compare the values at `fun i => by rw [hyσ i]`. Rewrite using `[hfun]`.

Conclude with `hind`. Establish `hxK : AlgebraicIndependent K fun i => r (σ i) j0` using `_root_.ReciprocityTheory.MultiplicativeHeights.algebraicIndependent_of_residue_lift (_root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v) (fun i => ⟨r (σ i) j0, hx i⟩) hind'`. Use `Set.mem_iUnion.2 ⟨⟨(j0, σ), hxK⟩, hdisc, hvg, ?_, hx, hind'⟩` and prove the remaining obligations. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.T0.IsTrivOn at htriv`. Conclude with `htriv`.

Use `⟨hfin, fun G e S he he0 hscale hzero f hf hf0 => ?_⟩` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨a, rfl⟩ : ∃ a : Ω c, a • e = f := by`. Take `⟨a, ha⟩` from `(finrank_eq_one_iff_of_nonzero' (⟨e, he⟩ : 𝒜 c G) (by simpa using he0)).1 (hrk G) ⟨f, hf⟩`. Conclude with `⟨a, congrArg Subtype.val ha⟩`. Establish `ha : a ≠ 0` using `by rintro rfl; simp at hf0`.

Establish `hneg : ∀ s, {v | d.admitted c v ∧ v s < 0}.Finite` using `fun s => by`. Distinguish the cases in `hs : s = 0`. Simplify using `[hs]`. Conclude with `(hfin s hs).subset fun v hv => ⟨hv.1, hv.2.ne⟩`. Use `((hfin a ha).union (S.finite_toSet.biUnion fun s _ => hneg s)).subset ?_` and prove the remaining obligations.

Introduce and unpack `v ⟨hv, hord⟩`. Distinguish the cases in `hva : v a = 0`. Use `right`. Assume the negation of the conclusion as `hS`. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe, not_exists, not_and, not_lt] at hS`.

Establish `h1` using `hscale v hv a ha`. Rewrite `h1` using `[hva, zero_add, hzero v hv fun s hs => hS s hs hv]`. Conclude with `hord (by exact_mod_cast h1)`. Conclude with `Or.inl ⟨hv, hva⟩`.
-/
theorem _root_.GlobalTheory.finite_support_admissible :
    (∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (D : ℕ) (x : Fin D → Ω), (⊤ : IntermediateField K Ω).FG → Algebra.trdeg K Ω = D → ∀ g : Ω, g ≠ 0 → {v : AddValuation Ω (WithTop ℤ) | _root_.ReciprocityTheory.ChartRestriction.G.T0.IsNormDiscrete v ∧ v g ≠ 0 ∧ ∃ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ∀ p : MvPolynomial (Fin D) (𝓞 K), 0 ≤ v (MvPolynomial.eval₂ ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)) x p) ∧ (0 < v (MvPolynomial.eval₂ ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)) x p) ↔ ∀ m, p.coeff m ∈ la.asIdeal)}.Finite) → (∀ (F Ω : Type) [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (t : Ω), (⊤ : IntermediateField F Ω).FG → Algebra.trdeg F Ω = 1 → Transcendental F t → ∀ g : Ω, g ≠ 0 → {v : AddValuation Ω (WithTop ℤ) | _root_.ReciprocityTheory.ChartRestriction.G.T0.IsNormDiscrete v ∧ _root_.ReciprocityTheory.ChartRestriction.G.T0.IsTrivOn F v ∧ 0 ≤ v t ∧ v g ≠ 0}.Finite) → ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] (WT : Type) [AddCommGroup WT] (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : _root_.ReciprocityTheory.ChartRestriction.G.T0.Data K ι Ω WT A), ∀ c : ι, 1 ≤ d.D → (⊤ : IntermediateField K (Ω c)).FG → Algebra.trdeg K (Ω c) = d.D → (∀ G, Module.finrank (Ω c) (𝒜 c G) = 1) → (∀ j, d.w j c ∈ 𝒜 c d.wL) → d.w (d.jc c) c ≠ 0 → _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD d c → (∀ g : Ω c, g ≠ 0 → {v | d.admitted c v ∧ v g ≠ 0}.Finite) ∧ ∀ (G : WT) (e : A c) (S : Finset (Ω c)), e ∈ 𝒜 c G → e ≠ 0 → (∀ v, d.admitted c v → ∀ a : Ω c, a ≠ 0 → ((d.ord c v G (a • e) : ℤ) : WithTop ℤ) = v a + (d.ord c v G e : WithTop ℤ)) → (∀ v, d.admitted c v → (∀ s ∈ S, 0 ≤ v s) → d.ord c v G e = 0) → ∀ f ∈ 𝒜 c G, f ≠ 0 → {v | d.admitted c v ∧ d.ord c v G f ≠ 0}.Finite := by
  intro H1 H2 K _ _ ι _ Ω _ _ WT _ A _ _ _ _ 𝒜 d c hD hfg htr hrk hwL hjc hT
  have hfin : ∀ g : Ω c, g ≠ 0 → {v | d.admitted c v ∧ v g ≠ 0}.Finite := by
    intro g hg
    set r : Fin (d.N + 1) → Fin (d.N + 1) → Ω c := fun j j0 => _root_.ReciprocityTheory.ChartRestriction.G.T0.ratio (d.w j c) (d.w j0 c)
    have hfin1 := Set.finite_iUnion fun j0 : Fin (d.N + 1) => Set.finite_iUnion
      fun σ : Fin d.D → Fin (d.N + 1) => H1 K (Ω c) d.D (fun i => r (σ i) j0) hfg htr g hg
    have hfin2 := Set.finite_iUnion fun p : {p : Fin (d.N + 1) × (Fin (d.D - 1) → Fin (d.N + 1)) //
        AlgebraicIndependent K fun i => r (p.2 i) p.1} =>
      case_two_finite_lemma H2 (Nat.sub_add_cancel hD) hfg htr _ p.2 g hg
    refine (hfin1.union hfin2).subset ?_
    rintro v ⟨hv, hvg⟩
    have hv' := hv
    unfold _root_.ReciprocityTheory.ChartRestriction.G.T0.Data.admitted at hv'
    obtain ⟨hdisc, ⟨la, hla, hres⟩ | ⟨htriv, hres⟩⟩ := hv'
    · left
      unfold _root_.ReciprocityTheory.ChartRestriction.G.T0.Data.ResCond at hres
      obtain ⟨-, j0, -, hint, htd⟩ := hres
      obtain ⟨y, hy, hind⟩ := exists_algebraicIndependent_fin_of_trdeg_adjoin_eq _ _ htd
      choose σ hσ hyσ using hy
      refine Set.mem_iUnion.2 ⟨j0, Set.mem_iUnion.2 ⟨σ, hdisc, hvg, la, ?_⟩⟩
      have hx : ∀ i, r (σ i) j0 ∈ _root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v := fun i => (mem_vRing_iff_nonneg v _).2 (hint (σ i))
      have hind' : AlgebraicIndependent (IsLocalRing.ResidueField ((_root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v).comap (algebraMap K (Ω c))))
          fun i => IsLocalRing.residue (_root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v) ⟨r (σ i) j0, hx i⟩ := by
        have hfun : (fun i => IsLocalRing.residue (_root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v) ⟨r (σ i) j0, hx i⟩) = y :=
          funext fun i => by rw [hyσ i]
        rw [hfun]
        exact hind
      unfold _root_.ReciprocityTheory.ChartRestriction.G.T0.IsOver at hla
      exact polynomial_value_over_prime_lemma_4 v la hla _ hx hind'
    · right
      unfold _root_.ReciprocityTheory.ChartRestriction.G.T0.Data.ResCond at hres
      obtain ⟨-, j0, -, hint, htd⟩ := hres
      obtain ⟨y, hy, hind⟩ := exists_algebraicIndependent_fin_of_trdeg_adjoin_eq _ _ htd
      choose σ hσ hyσ using hy
      have hx : ∀ i, r (σ i) j0 ∈ _root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v := fun i => (mem_vRing_iff_nonneg v _).2 (hint (σ i))
      have hind' : AlgebraicIndependent (IsLocalRing.ResidueField ((_root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v).comap (algebraMap K (Ω c))))
          fun i => IsLocalRing.residue (_root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v) ⟨r (σ i) j0, hx i⟩ := by
        have hfun : (fun i => IsLocalRing.residue (_root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v) ⟨r (σ i) j0, hx i⟩) = y :=
          funext fun i => by rw [hyσ i]
        rw [hfun]
        exact hind
      have hxK : AlgebraicIndependent K fun i => r (σ i) j0 :=
        _root_.ReciprocityTheory.MultiplicativeHeights.algebraicIndependent_of_residue_lift (_root_.ReciprocityTheory.ChartRestriction.G.T0.vRing v) (fun i => ⟨r (σ i) j0, hx i⟩) hind'
      refine Set.mem_iUnion.2 ⟨⟨(j0, σ), hxK⟩, hdisc, hvg, ?_, hx, hind'⟩
      unfold _root_.ReciprocityTheory.ChartRestriction.G.T0.IsTrivOn at htriv
      exact htriv
  refine ⟨hfin, fun G e S he he0 hscale hzero f hf hf0 => ?_⟩
  obtain ⟨a, rfl⟩ : ∃ a : Ω c, a • e = f := by
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨e, he⟩ : 𝒜 c G)
      (by simpa using he0)).1 (hrk G) ⟨f, hf⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  have ha : a ≠ 0 := by rintro rfl; simp at hf0
  have hneg : ∀ s, {v | d.admitted c v ∧ v s < 0}.Finite := fun s => by
    by_cases hs : s = 0
    · simp [hs]
    · exact (hfin s hs).subset fun v hv => ⟨hv.1, hv.2.ne⟩
  refine ((hfin a ha).union (S.finite_toSet.biUnion fun s _ => hneg s)).subset ?_
  rintro v ⟨hv, hord⟩
  by_cases hva : v a = 0
  · right
    by_contra hS
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe, not_exists, not_and, not_lt] at hS
    have h1 := hscale v hv a ha
    rw [hva, zero_add, hzero v hv fun s hs => hS s hs hv] at h1
    exact hord (by exact_mod_cast h1)
  · exact Or.inl ⟨hv, hva⟩

end GlobalTheory
