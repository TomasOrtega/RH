import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

open TopologicalSpace

variable {m n : ℕ}

/- English proof (translation)
Use `haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK`. Establish `hc : Continuous (fun q : ((Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m)) × K => linProj q.1.1 (q.2 : EuclideanSpace ℂ (Fin n)))`. Unfold `linProj`. Use `fun_prop`. Establish `hC : IsClosed {q : ((Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m)) × K | linProj q.1.1 (q.2 : EuclideanSpace ℂ (Fin n)) = q.1.2}` using `isClosed_eq hc (continuous_snd.comp continuous_fst)`.

Establish `h2` using `isClosedMap_fst_of_compactSpace _ hC`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `p`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, h⟩`.

Conclude with `⟨(p, ⟨y, hy⟩), h, rfl⟩`. Introduce and unpack `⟨⟨p', y⟩, h, rfl⟩`. Conclude with `⟨y, y.2, h⟩`.
-/
theorem isClosed_linProj_meets_compact {K : Set (EuclideanSpace ℂ (Fin n))} (hK : IsCompact K) :
    IsClosed {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) | ∃ y ∈ K, linProj p.1 y = p.2} := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun q : ((Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m)) × K =>
      linProj q.1.1 (q.2 : EuclideanSpace ℂ (Fin n))) := by
    unfold linProj
    fun_prop
  have hC : IsClosed {q : ((Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m)) × K |
      linProj q.1.1 (q.2 : EuclideanSpace ℂ (Fin n)) = q.1.2} :=
    isClosed_eq hc (continuous_snd.comp continuous_fst)
  have h2 := isClosedMap_fst_of_compactSpace _ hC
  convert h2 using 1
  ext p
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨(p, ⟨y, hy⟩), h, rfl⟩
  · rintro ⟨⟨p', y⟩, h, rfl⟩
    exact ⟨y, y.2, h⟩

/- English proof (translation)
Use `haveI : LocallyCompactSpace U := hU.locallyCompactSpace`. Conclude with `isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance`.
-/
theorem isSigmaCompact_of_isOpen_euclidean {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U) :
    IsSigmaCompact U := by
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance

/- English proof (translation)
Take `⟨K, hK, hKS⟩` from `hS`. Take `⟨L, hL, hLU⟩` from `isSigmaCompact_of_isOpen_euclidean hU`. Establish `hEq : {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) | ∃ y ∈ S ∩ U, linProj p.1 y = p.2} = ⋃ k, ⋃ l, {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) | ∃ y ∈ K k ∩ L l, linProj p.1 y = p.2}`. Use extensionality with `p`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_iUnion]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨hyS, hyU⟩, h⟩`. Rewrite `hyS` using `[← hKS, Set.mem_iUnion]`. Rewrite `hyU` using `[← hLU, Set.mem_iUnion]`. Take `⟨k, hk⟩` from `hyS`.

Take `⟨l, hl⟩` from `hyU`. Conclude with `⟨k, l, y, ⟨hk, hl⟩, h⟩`. Introduce and unpack `⟨k, l, y, ⟨hk, hl⟩, h⟩`. Use `⟨y, ⟨?_, ?_⟩, h⟩` and prove the remaining obligations. Rewrite using `[← hKS]`.

Conclude with `Set.mem_iUnion.mpr ⟨k, hk⟩`. Rewrite using `[← hLU]`. Conclude with `Set.mem_iUnion.mpr ⟨l, hl⟩`. Rewrite using `[hEq]`. Conclude with `MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun l => (isClosed_linProj_meets_compact ((hK k).inter (hL l))).measurableSet`.
-/
theorem measurableSet_linProj_meets {S U : Set (EuclideanSpace ℂ (Fin n))} (hS : IsSigmaCompact S)
    (hU : IsOpen U) :
    MeasurableSet {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
      ∃ y ∈ S ∩ U, linProj p.1 y = p.2} := by
  obtain ⟨K, hK, hKS⟩ := hS
  obtain ⟨L, hL, hLU⟩ := isSigmaCompact_of_isOpen_euclidean hU
  have hEq : {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) | ∃ y ∈ S ∩ U, linProj p.1 y = p.2} =
      ⋃ k, ⋃ l, {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
        ∃ y ∈ K k ∩ L l, linProj p.1 y = p.2} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨y, ⟨hyS, hyU⟩, h⟩
      rw [← hKS, Set.mem_iUnion] at hyS
      rw [← hLU, Set.mem_iUnion] at hyU
      obtain ⟨k, hk⟩ := hyS
      obtain ⟨l, hl⟩ := hyU
      exact ⟨k, l, y, ⟨hk, hl⟩, h⟩
    · rintro ⟨k, l, y, ⟨hk, hl⟩, h⟩
      refine ⟨y, ⟨?_, ?_⟩, h⟩
      · rw [← hKS]; exact Set.mem_iUnion.mpr ⟨k, hk⟩
      · rw [← hLU]; exact Set.mem_iUnion.mpr ⟨l, hl⟩
  rw [hEq]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun l =>
    (isClosed_linProj_meets_compact ((hK k).inter (hL l))).measurableSet

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hN`. Take `⟨t, htS, htN⟩` from `Set.exists_subset_encard_eq hN`. Establish `htf : t.Finite` using `Set.finite_of_encard_eq_coe htN`. Establish `hcard : htf.toFinset.card = N`.

Use `htf.encard_eq_coe_toFinset_card` as an intermediate fact. Rewrite `this` using `[htN]`. Conclude with `this.symm` after adjusting the coercions. Set `e : Fin N ≃ {x // x ∈ htf.toFinset}` to `(htf.toFinset.equivFinOfCardEq hcard).symm`. Set `g : Fin N → EuclideanSpace ℂ (Fin n)` to `fun i => (e i : EuclideanSpace ℂ (Fin n))`.

Establish `hg_mem : ∀ i, g i ∈ t` using `fun i => htf.mem_toFinset.mp (e i).2`. Establish `hg_inj : Function.Injective g`. Introduce `i j hij`. Conclude with `e.injective (Subtype.ext hij)`. Take `⟨V, hV, hVd⟩` from `(Set.finite_range g).t2_separation`.

Establish `hB : ∀ i, ∃ v ∈ countableBasis (EuclideanSpace ℂ (Fin n)), g i ∈ v ∧ v ⊆ V (g i)` using `fun i => (isBasis_countableBasis (EuclideanSpace ℂ (Fin n))).exists_subset_of_mem_open (hV (g i)).1 (hV (g i)).2`. Use `choose v hvB hgv hvV using hB`. Use `⟨fun i => ⟨v i, hvB i⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Establish `hne : g i ≠ g j` using `fun h => hij (hg_inj h)`.

Conclude with `(hVd (Set.mem_range_self i) (Set.mem_range_self j) hne).mono (hvV i) (hvV j)`. Introduce `i`. Use `htS (hg_mem i)` as an intermediate fact. Conclude with `⟨g i, ⟨this.1, hgv i⟩, this.2⟩`. Introduce and unpack `⟨f, hfd, hf⟩ choose y hy hyw using hf`.

Establish `hinj : Function.Injective y`. Introduce `i j hij`. Assume the negation of the conclusion as `hne`. Establish `hd` using `hfd i j hne`. Conclude with `Set.disjoint_left.mp hd (hy i).2 (hij ▸ (hy j).2)`.

Establish `hsub : Set.range y ⊆ ptsOver S π w`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨(hy i).1, hyw i⟩`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Set.image_univ, hinj.encard_image, Set.encard_univ]`.

Simplify using the standard rewrite rules. Use `_ ≤ (ptsOver S π w).encard := Set.encard_le_encard hsub`.
-/
theorem natCast_le_encard_ptsOver_iff (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin m → Fin n → ℂ)
    (w : EuclideanSpace ℂ (Fin m)) (N : ℕ) :
    (N : ℕ∞) ≤ (ptsOver S π w).encard ↔
      ∃ f : Fin N → countableBasis (EuclideanSpace ℂ (Fin n)),
        (∀ i j, i ≠ j → Disjoint (f i : Set (EuclideanSpace ℂ (Fin n))) (f j)) ∧
        ∀ i, ∃ y ∈ S ∩ (f i : Set (EuclideanSpace ℂ (Fin n))), linProj π y = w := by
  constructor
  · intro hN
    obtain ⟨t, htS, htN⟩ := Set.exists_subset_encard_eq hN
    have htf : t.Finite := Set.finite_of_encard_eq_coe htN
    have hcard : htf.toFinset.card = N := by
      have := htf.encard_eq_coe_toFinset_card
      rw [htN] at this
      exact_mod_cast this.symm
    let e : Fin N ≃ {x // x ∈ htf.toFinset} := (htf.toFinset.equivFinOfCardEq hcard).symm
    let g : Fin N → EuclideanSpace ℂ (Fin n) := fun i => (e i : EuclideanSpace ℂ (Fin n))
    have hg_mem : ∀ i, g i ∈ t := fun i => htf.mem_toFinset.mp (e i).2
    have hg_inj : Function.Injective g := by
      intro i j hij
      exact e.injective (Subtype.ext hij)
    obtain ⟨V, hV, hVd⟩ := (Set.finite_range g).t2_separation
    have hB : ∀ i, ∃ v ∈ countableBasis (EuclideanSpace ℂ (Fin n)), g i ∈ v ∧ v ⊆ V (g i) := fun i =>
      (isBasis_countableBasis (EuclideanSpace ℂ (Fin n))).exists_subset_of_mem_open (hV (g i)).1 (hV (g i)).2
    choose v hvB hgv hvV using hB
    refine ⟨fun i => ⟨v i, hvB i⟩, ?_, ?_⟩
    · intro i j hij
      have hne : g i ≠ g j := fun h => hij (hg_inj h)
      exact (hVd (Set.mem_range_self i) (Set.mem_range_self j) hne).mono (hvV i) (hvV j)
    · intro i
      have := htS (hg_mem i)
      exact ⟨g i, ⟨this.1, hgv i⟩, this.2⟩
  · rintro ⟨f, hfd, hf⟩
    choose y hy hyw using hf
    have hinj : Function.Injective y := by
      intro i j hij
      by_contra hne
      have hd := hfd i j hne
      exact Set.disjoint_left.mp hd (hy i).2 (hij ▸ (hy j).2)
    have hsub : Set.range y ⊆ ptsOver S π w := by
      rintro _ ⟨i, rfl⟩
      exact ⟨(hy i).1, hyw i⟩
    calc (N : ℕ∞) = (Set.range y).encard := by
          rw [← Set.image_univ, hinj.encard_image, Set.encard_univ]; simp
      _ ≤ (ptsOver S π w).encard := Set.encard_le_encard hsub

/- English proof (translation)
Use `haveI : Countable (countableBasis (EuclideanSpace ℂ (Fin n))) := (countable_countableBasis (EuclideanSpace ℂ (Fin n))).to_subtype`. Establish `hEq : {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) | (N : ℕ∞) ≤ (ptsOver S p.1 p.2).encard} = ⋃ f : Fin N → countableBasis (EuclideanSpace ℂ (Fin n)), ({_p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) | ∀ i j, i ≠ j → Disjoint (f i : Set (EuclideanSpace ℂ (Fin n))) (f …`. Use extensionality with `p`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter]`. Conclude with `natCast_le_encard_ptsOver_iff S p.1 p.2 N`.

Rewrite using `[hEq]`. Conclude with `MeasurableSet.iUnion fun f => (MeasurableSet.const _).inter (MeasurableSet.iInter fun i => measurableSet_linProj_meets hS (isOpen_of_mem_countableBasis (f i).2))`.
-/
theorem measurableSet_natCast_le_encard_ptsOver {S : Set (EuclideanSpace ℂ (Fin n))}
    (hS : IsSigmaCompact S) (N : ℕ) :
    MeasurableSet {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
      (N : ℕ∞) ≤ (ptsOver S p.1 p.2).encard} := by
  haveI : Countable (countableBasis (EuclideanSpace ℂ (Fin n))) :=
    (countable_countableBasis (EuclideanSpace ℂ (Fin n))).to_subtype
  have hEq : {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
      (N : ℕ∞) ≤ (ptsOver S p.1 p.2).encard} =
      ⋃ f : Fin N → countableBasis (EuclideanSpace ℂ (Fin n)),
        ({_p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
          ∀ i j, i ≠ j → Disjoint (f i : Set (EuclideanSpace ℂ (Fin n))) (f j)} ∩
        ⋂ i, {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
          ∃ y ∈ S ∩ (f i : Set (EuclideanSpace ℂ (Fin n))), linProj p.1 y = p.2}) := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter]
    exact natCast_le_encard_ptsOver_iff S p.1 p.2 N
  rw [hEq]
  exact MeasurableSet.iUnion fun f => (MeasurableSet.const _).inter
    (MeasurableSet.iInter fun i => measurableSet_linProj_meets hS (isOpen_of_mem_countableBasis (f i).2))

/- English proof (translation)
Introduce `n m S hS`. Establish `h : (fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) => cntOver S p.1 p.2) = fun p => ⨆ N : ℕ, {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) | (N : ℕ∞) ≤ (ptsOver S p.1 p.2).encard}.indicator (fun _ => (N : ℝ≥0∞)) p`. Use function extensionality and compare the values at `p`. Simplify using `only [cntOver, Set.indicator_apply, Set.mem_setOf_eq]`. Generalize the expression as in `(ptsOver S p.1 p.2).encard = e`.

Proceed by induction on `e using ENat.recTopCoe with`. Consider the case `top => simp [ENNReal.iSup_natCast]`. Consider the case `coe k`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `le_iSup_of_le k (by simp)`.

Use `iSup_le fun N => ?_ split_ifs with hN` and prove the remaining obligations. Establish `: N ≤ k` using `by exact_mod_cast hN`. Simplify using `using this`. Conclude with `zero_le`. Rewrite using `[h]`.

Conclude with `Measurable.iSup fun N => measurable_const.indicator (measurableSet_natCast_le_encard_ptsOver hS N)`.
-/
theorem measurable_cntOver : ∀ (n m : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsSigmaCompact S →
    Measurable (fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) => cntOver S p.1 p.2) := by
  intro n m S hS
  have h : (fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) => cntOver S p.1 p.2) =
      fun p => ⨆ N : ℕ, {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
        (N : ℕ∞) ≤ (ptsOver S p.1 p.2).encard}.indicator (fun _ => (N : ℝ≥0∞)) p := by
    funext p
    simp only [cntOver, Set.indicator_apply, Set.mem_setOf_eq]
    generalize (ptsOver S p.1 p.2).encard = e
    induction e using ENat.recTopCoe with
    | top => simp [ENNReal.iSup_natCast]
    | coe k =>
      apply le_antisymm
      · exact le_iSup_of_le k (by simp)
      · refine iSup_le fun N => ?_
        split_ifs with hN
        · have : N ≤ k := by exact_mod_cast hN
          simpa using this
        · exact zero_le
  rw [h]
  exact Measurable.iSup fun N => measurable_const.indicator (measurableSet_natCast_le_encard_ptsOver hS N)

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
