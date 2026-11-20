import Formalism.SuccessiveMinima.DefsMink

open MeasureTheory Module Metric Set
open scoped Pointwise

noncomputable section

namespace Formalism.FN.SuccessiveMinima

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- English proof (translation)
Establish `hK : K ∈ nhds (0 : E)` using `mem_interior_iff_mem_nhds.mp hK0`. Establish `hKabs : Absorbent ℝ K` using `absorbent_nhds_zero hK`. Break down `ht.eq_or_lt with rfl | htpos` into its components or cases. Establish `hne : K.Nonempty` using `⟨0, interior_subset hK0⟩`. Rewrite using `[Set.zero_smul_set hne, Set.mem_zero]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Simplify using the standard rewrite rules. Introduce `hg`. Assume the negation of the conclusion as `hu`.

Use `(gauge_pos hKabs ((NormedSpace.isVonNBounded_iff ℝ).mpr hKc.isBounded)).mpr hu` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : t⁻¹ • u ∈ K ↔ gauge K (t⁻¹ • u) ≤ 1`. Rewrite using `[gauge_le_one_iff_mem_closure hKv hK, hKc.isClosed.closure_eq]`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem₀ htpos.ne', h1, gauge_smul_of_nonneg (inv_nonneg.mpr htpos.le), smul_eq_mul, inv_mul_le_iff₀ htpos, mul_one]`.
-/
theorem mem_smul_iff_gauge {K : Set E} (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hK0 : (0 : E) ∈ interior K) {t : ℝ} (ht : 0 ≤ t) (u : E) :
    u ∈ t • K ↔ gauge K u ≤ t := by
  have hK : K ∈ nhds (0 : E) := mem_interior_iff_mem_nhds.mp hK0
  have hKabs : Absorbent ℝ K := absorbent_nhds_zero hK
  rcases ht.eq_or_lt with rfl | htpos
  ·
    have hne : K.Nonempty := ⟨0, interior_subset hK0⟩
    rw [Set.zero_smul_set hne, Set.mem_zero]
    constructor
    · rintro rfl
      simp
    · intro hg
      by_contra hu
      have := (gauge_pos hKabs ((NormedSpace.isVonNBounded_iff ℝ).mpr hKc.isBounded)).mpr hu
      linarith
  · have h1 : t⁻¹ • u ∈ K ↔ gauge K (t⁻¹ • u) ≤ 1 := by
      rw [gauge_le_one_iff_mem_closure hKv hK, hKc.isClosed.closure_eq]
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ htpos.ne', h1,
      gauge_smul_of_nonneg (inv_nonneg.mpr htpos.le), smul_eq_mul, inv_mul_le_iff₀ htpos, mul_one]

/- English proof (translation)
Use `haveI : ProperSpace E := FiniteDimensional.proper_real E`. Establish `hcl : IsClosed (L : Set E)` using `L.toAddSubgroup.isClosed_of_discrete`. Establish `hd : IsDiscrete (L : Set E)` using `by first`. Consider the case `exact ⟨‹DiscreteTopology L›⟩`. Consider the case `exact isDiscrete_iff_discreteTopology.mpr ‹DiscreteTopology L›`.

Rewrite using `[Set.inter_comm]`. Conclude with `Metric.finite_isBounded_inter_isClosed hd hs hcl`.
-/
theorem finite_lat_inter (L : Submodule ℤ E) [DiscreteTopology L] {s : Set E}
    (hs : Bornology.IsBounded s) : ((L : Set E) ∩ s).Finite := by
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  have hcl : IsClosed (L : Set E) := L.toAddSubgroup.isClosed_of_discrete
  have hd : IsDiscrete (L : Set E) := by
    first
      | exact ⟨‹DiscreteTopology L›⟩
      | exact isDiscrete_iff_discreteTopology.mpr ‹DiscreteTopology L›
  rw [Set.inter_comm]
  exact Metric.finite_isBounded_inter_isClosed hd hs hcl

/- English proof (translation)
Take `⟨m, hmS, hmin⟩` from `Set.exists_min_image (insert T (f '' B)) id ((hB.image f).insert T) ⟨T, Set.mem_insert _ _⟩`. Use `⟨m, ?_, hmin T (Set.mem_insert _ _), fun u hu => hmin (f u) (Set.mem_insert_of_mem _ ⟨u, hu, rfl⟩)⟩` and prove the remaining obligations. Break down `hmS with rfl | ⟨u, hu, rfl⟩` into its components or cases. Conclude with `hcT`. Conclude with `h u hu`.
-/
theorem exists_gap {α : Type*} (f : α → ℝ) {B : Set α} (hB : B.Finite) {c T : ℝ} (hcT : c < T)
    (h : ∀ u ∈ B, c < f u) : ∃ m, c < m ∧ m ≤ T ∧ ∀ u ∈ B, m ≤ f u := by
  obtain ⟨m, hmS, hmin⟩ := Set.exists_min_image (insert T (f '' B)) id
    ((hB.image f).insert T) ⟨T, Set.mem_insert _ _⟩
  refine ⟨m, ?_, hmin T (Set.mem_insert _ _), fun u hu => hmin (f u) (Set.mem_insert_of_mem _ ⟨u, hu, rfl⟩)⟩
  rcases hmS with rfl | ⟨u, hu, rfl⟩
  · exact hcT
  · exact h u hu

variable (L : Submodule ℤ E) [DiscreteTopology L] {K : Set E}

/- English proof (translation)
Use `set S : Set ℝ := {t : ℝ | 0 ≤ t ∧ i ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ t • K))} with hS`. Establish `hSne : S.Nonempty` using `⟨T, hT⟩`. Establish `hSbdd : BddBelow S` using `⟨0, fun t ht => ht.1⟩`. Establish `hs0 : 0 ≤ sInf S` using `le_csInf hSne fun t ht => ht.1`. Establish `hsT : sInf S ≤ T` using `csInf_le hSbdd hT`.

Use `show 0 ≤ sInf S ∧ i ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ sInf S • K))`. Use `⟨hs0, ?_⟩` and prove the remaining obligations. Break down `hsT.eq_or_lt with hsT | hsT` into its components or cases. Rewrite using `[hsT]`. Conclude with `hT.2`.

Use `set B : Set E := {u | u ∈ (L : Set E) ∩ T • K ∧ sInf S < gauge K u} with hB`. Establish `hBfin : B.Finite` using `(finite_lat_inter L ((hKc.smul T).isBounded)).subset fun u hu => hu.1`. Take `⟨m, hsm, hmT, hmB⟩` from `exists_gap (gauge K) hBfin hsT fun u hu => hu.2`. Take `⟨t, htS, htm⟩` from `exists_lt_of_csInf_lt hSne hsm`. Establish `hst : sInf S ≤ t` using `csInf_le hSbdd htS`.

Use `htS.2.trans (Submodule.finrank_mono (Submodule.span_mono ?_))` and prove the remaining obligations. Introduce and unpack `u ⟨huL, hut⟩`. Establish `hgt : gauge K u ≤ t` using `(mem_smul_iff_gauge hKc hKv hK0 htS.1 u).mp hut`. Use `⟨huL, (mem_smul_iff_gauge hKc hKv hK0 hs0 u).mpr ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`.

Use `push_neg at hlt`. Establish `huT : u ∈ T • K` using `(mem_smul_iff_gauge hKc hKv hK0 (hs0.trans hsT.le) u).mpr (by linarith)`. Use `hmB u ⟨⟨huL, huT⟩, hlt⟩` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem succMin_mem (hKc : IsCompact K) (hKv : Convex ℝ K) (hK0 : (0 : E) ∈ interior K)
    {i : ℕ} {T : ℝ}
    (hT : 0 ≤ T ∧ i ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ T • K))) :
    0 ≤ succMin L K i ∧ i ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ succMin L K i • K)) := by
  classical
  set S : Set ℝ := {t : ℝ | 0 ≤ t ∧ i ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ t • K))}
    with hS
  have hSne : S.Nonempty := ⟨T, hT⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1⟩
  have hs0 : 0 ≤ sInf S := le_csInf hSne fun t ht => ht.1
  have hsT : sInf S ≤ T := csInf_le hSbdd hT
  show 0 ≤ sInf S ∧ i ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ sInf S • K))
  refine ⟨hs0, ?_⟩
  rcases hsT.eq_or_lt with hsT | hsT
  · rw [hsT]; exact hT.2

  set B : Set E := {u | u ∈ (L : Set E) ∩ T • K ∧ sInf S < gauge K u} with hB
  have hBfin : B.Finite :=
    (finite_lat_inter L ((hKc.smul T).isBounded)).subset fun u hu => hu.1
  obtain ⟨m, hsm, hmT, hmB⟩ := exists_gap (gauge K) hBfin hsT fun u hu => hu.2
  obtain ⟨t, htS, htm⟩ := exists_lt_of_csInf_lt hSne hsm
  have hst : sInf S ≤ t := csInf_le hSbdd htS
  refine htS.2.trans (Submodule.finrank_mono (Submodule.span_mono ?_))
  rintro u ⟨huL, hut⟩
  have hgt : gauge K u ≤ t := (mem_smul_iff_gauge hKc hKv hK0 htS.1 u).mp hut
  refine ⟨huL, (mem_smul_iff_gauge hKc hKv hK0 hs0 u).mpr ?_⟩
  by_contra hlt
  push_neg at hlt
  have huT : u ∈ T • K :=
    (mem_smul_iff_gauge hKc hKv hK0 (hs0.trans hsT.le) u).mpr (by linarith)
  have := hmB u ⟨⟨huL, huT⟩, hlt⟩
  linarith

/- English proof (translation)
Establish `hK : K ∈ nhds (0 : E)` using `mem_interior_iff_mem_nhds.mp hK0`. Establish `hKabs : Absorbent ℝ K` using `absorbent_nhds_zero hK`. Use `set B : Set E := {u | u ∈ (L : Set E) ∩ K ∧ u ≠ 0} with hB`. Establish `hBfin : B.Finite` using `(finite_lat_inter L hKc.isBounded).subset fun u hu => hu.1`. Take `⟨m, hm0, hm1, hmB⟩` from `exists_gap (gauge K) hBfin zero_lt_one fun u hu => (gauge_pos hKabs ((NormedSpace.isVonNBounded_iff ℝ).mpr hKc.isBounded)).mpr hu.2`.

Use `⟨m, hm0, fun t ht htm => Submodule.span_eq_bot.mpr ?_⟩` and prove the remaining obligations. Introduce and unpack `u ⟨huL, hut⟩`. Establish `hgt : gauge K u ≤ t` using `(mem_smul_iff_gauge hKc hKv hK0 ht u).mp hut`. Assume the negation of the conclusion as `hu`. Establish `huK : u ∈ K`.

Use `(mem_smul_iff_gauge hKc hKv hK0 zero_le_one u).mpr (by linarith)` as an intermediate fact. Rewrite `this` using `[one_smul]`. Then use the resulting hypothesis. Use `hmB u ⟨⟨huL, huK⟩, hu⟩` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_pos_bot (hKc : IsCompact K) (hKv : Convex ℝ K) (hK0 : (0 : E) ∈ interior K) :
    ∃ m : ℝ, 0 < m ∧ ∀ t, 0 ≤ t → t < m →
      Submodule.span ℝ ((L : Set E) ∩ t • K) = ⊥ := by
  have hK : K ∈ nhds (0 : E) := mem_interior_iff_mem_nhds.mp hK0
  have hKabs : Absorbent ℝ K := absorbent_nhds_zero hK
  set B : Set E := {u | u ∈ (L : Set E) ∩ K ∧ u ≠ 0} with hB
  have hBfin : B.Finite := (finite_lat_inter L hKc.isBounded).subset fun u hu => hu.1
  obtain ⟨m, hm0, hm1, hmB⟩ := exists_gap (gauge K) hBfin zero_lt_one
    fun u hu => (gauge_pos hKabs ((NormedSpace.isVonNBounded_iff ℝ).mpr hKc.isBounded)).mpr hu.2
  refine ⟨m, hm0, fun t ht htm => Submodule.span_eq_bot.mpr ?_⟩
  rintro u ⟨huL, hut⟩
  have hgt : gauge K u ≤ t := (mem_smul_iff_gauge hKc hKv hK0 ht u).mp hut
  by_contra hu
  have huK : u ∈ K := by
    have := (mem_smul_iff_gauge hKc hKv hK0 zero_le_one u).mpr (by linarith)
    rwa [one_smul] at this
  have := hmB u ⟨⟨huL, huK⟩, hu⟩
  linarith

/- English proof (translation)
Take `⟨b, hbL, hbspan, hbli⟩` from `exists_linearIndependent ℝ (L : Set E)`. Establish `hbfin : b.Finite` using `hbli.setFinite`. Take `⟨M, hM⟩` from `(hbfin.image (gauge K)).bddAbove`. Use `⟨max M 0, le_max_right _ _, eq_top_iff.mpr ?_⟩` and prove the remaining obligations. Establish `hLtop : Submodule.span ℝ (L : Set E) = ⊤` using `IsZLattice.span_top`.

Rewrite using `[← hLtop, ← hbspan]`. Use `Submodule.span_mono fun x hx => ⟨hbL hx, ?_⟩` and prove the remaining obligations. Use `(mem_smul_iff_gauge hKc hKv hK0 (le_max_right _ _) x).mpr ?_` and prove the remaining obligations. Conclude with `(hM ⟨x, hx, rfl⟩).trans (le_max_left _ _)`.
-/
theorem exists_span_top [IsZLattice ℝ L] (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hK0 : (0 : E) ∈ interior K) :
    ∃ T : ℝ, 0 ≤ T ∧ Submodule.span ℝ ((L : Set E) ∩ T • K) = ⊤ := by

  obtain ⟨b, hbL, hbspan, hbli⟩ := exists_linearIndependent ℝ (L : Set E)
  have hbfin : b.Finite := hbli.setFinite
  obtain ⟨M, hM⟩ := (hbfin.image (gauge K)).bddAbove
  refine ⟨max M 0, le_max_right _ _, eq_top_iff.mpr ?_⟩
  have hLtop : Submodule.span ℝ (L : Set E) = ⊤ := IsZLattice.span_top
  rw [← hLtop, ← hbspan]
  refine Submodule.span_mono fun x hx => ⟨hbL hx, ?_⟩
  refine (mem_smul_iff_gauge hKc hKv hK0 (le_max_right _ _) x).mpr ?_
  exact (hM ⟨x, hx, rfl⟩).trans (le_max_left _ _)

end Formalism.FN.SuccessiveMinima

open Formalism.FN.SuccessiveMinima in
/- English proof (translation)
Introduce `E _ _ _ L _ _ K hKc hKv _ hK0`. Establish `hmemK : ∀ {t : ℝ}, 0 ≤ t → ∀ u, u ∈ t • K ↔ gauge K u ≤ t` using `fun ht u => mem_smul_iff_gauge hKc hKv hK0 ht u`. Take `⟨T, hT0, hTtop⟩` from `exists_span_top L hKc hKv hK0`. Establish `hTfin : finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ T • K)) = finrank ℝ E`. Rewrite using `[hTtop, finrank_top]`.

Establish `hmem : ∀ j, j ≤ finrank ℝ E → 0 ≤ succMin L K j ∧ j ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ succMin L K j • K))` using `fun j hj => succMin_mem L hKc hKv hK0 ⟨hT0, by rw [hTfin]; exact hj⟩`. Establish `hsub : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → (L : Set E) ∩ s • K ⊆ (L : Set E) ∩ t • K` using `fun hs hst u hu => ⟨hu.1, (hmemK (hs.trans hst) u).mpr (((hmemK hs u).mp hu.2).trans hst)⟩`. Establish `hle : ∀ {j : ℕ} {t : ℝ}, 0 ≤ t → j ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ t • K)) → succMin L K j ≤ t` using `fun ht h => csInf_le ⟨0, fun x hx => hx.1⟩ ⟨ht, h⟩`. Take `⟨m, hm0, hmbot⟩` from `exists_pos_bot L hKc hKv hK0`. Establish `hpos : ∀ j, 1 ≤ j → j ≤ finrank ℝ E → 0 < succMin L K j`.

Introduce `j hj1 hjn`. Take `⟨h0, hj⟩` from `hmem j hjn`. Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`. Rewrite `hj` using `[hmbot _ h0 (lt_of_le_of_lt hneg hm0), finrank_bot]`.

Use linear arithmetic over natural numbers and integers. Establish `build : ∀ k, k ≤ finrank ℝ E → ∃ w : Fin k → E, LinearIndependent ℝ w ∧ ∀ j : Fin k, w j ∈ L ∧ w j ∈ succMin L K ((j : ℕ) + 1) • K`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _`.

Conclude with `⟨Fin.elim0, linearIndependent_empty_type, fun j => j.elim0⟩`. Consider the case `succ k ih`. Introduce `hk`. Take `⟨w, hw, hwm⟩` from `ih (Nat.le_of_succ_le hk)`. Take `⟨_, hdim⟩` from `hmem (k + 1) hk`.

Establish `hex : ∃ x ∈ (L : Set E) ∩ succMin L K (k + 1) • K, x ∉ Submodule.span ℝ (Set.range w)`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Establish `h1` using `Submodule.finrank_mono (Submodule.span_le.mpr hno)`. Rewrite `h1` using `[finrank_span_eq_card hw, Fintype.card_fin]`.

Use linear arithmetic over natural numbers and integers. Take `⟨x, ⟨hxL, hxK⟩, hxw⟩` from `hex`. Use `⟨Fin.snoc w x, linearIndependent_fin_snoc.mpr ⟨hw, hxw⟩, fun j => ?_⟩` and prove the remaining obligations. Use `Fin.lastCases ?_ (fun i => ?_) j` and prove the remaining obligations. Simplify using `only [Fin.snoc_last, Fin.val_last]`.

Conclude with `⟨hxL, hxK⟩`. Simplify using `only [Fin.snoc_castSucc, Fin.coe_castSucc]`. Conclude with `hwm i`. Take `⟨v, hv, hvm⟩` from `build (finrank ℝ E) le_rfl`. Use `⟨v, hv, fun i => (hvm i).1, fun i => (hvm i).2, fun i => hpos _ (by omega) (Nat.succ_le_of_lt i.isLt), ?_, ?_⟩` and prove the remaining obligations.

Introduce `i j hij`. Establish `hij' : (i : ℕ) ≤ j` using `hij`. Take `⟨h0, hj⟩` from `hmem ((j : ℕ) + 1) (Nat.succ_le_of_lt j.isLt)`. Conclude with `hle h0 (le_trans (by omega) hj)`. Introduce `i u huL huint`.

Establish `hlam : 0 < succMin L K ((i : ℕ) + 1)` using `hpos _ (by omega) (Nat.succ_le_of_lt i.isLt)`. Establish `hg : gauge K u < succMin L K ((i : ℕ) + 1)`. Take `⟨y, hy, rfl⟩` from `Set.mem_smul_set.mp huint`. Rewrite using `[gauge_smul_of_nonneg hlam.le, smul_eq_mul]`. Conclude with `mul_lt_of_lt_one_right hlam (interior_subset_gauge_lt_one K hy)`.

Establish `hg0 : 0 ≤ gauge K u` using `gauge_nonneg u`. Use `set W := Submodule.span ℝ ((L : Set E) ∩ gauge K u • K) with hW`. Establish `huW : u ∈ W` using `Submodule.subset_span ⟨huL, (hmemK hg0 u).mpr le_rfl⟩`. Establish `hdn : finrank ℝ W ≤ finrank ℝ E` using `Submodule.finrank_le W`. Establish `hdi : finrank ℝ W ≤ (i : ℕ)`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Use `hle hg0 (show (i : ℕ) + 1 ≤ finrank ℝ W by omega)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdW : succMin L K (finrank ℝ W) ≤ gauge K u` using `hle hg0 le_rfl`.

Establish `hvW : ∀ k : Fin (finrank ℝ E), (k : ℕ) < finrank ℝ W → v k ∈ W`. Introduce `k hk`. Take `⟨hd0, hd⟩` from `hmem (finrank ℝ W) hdn`. Establish `hk1 : succMin L K ((k : ℕ) + 1) ≤ gauge K u` using `(hle hd0 (le_trans (by omega) hd)).trans hdW`. Conclude with `Submodule.subset_span (hsub (hmem _ (Nat.succ_le_of_lt k.isLt)).1 hk1 ⟨(hvm k).1, (hvm k).2⟩)`.

Establish `himg : v '' {k | (k : ℕ) < finrank ℝ W} = Set.range (fun j : Fin (finrank ℝ W) => v (Fin.castLE hdn j))`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`. Conclude with `⟨⟨k, hk⟩, congrArg v (Fin.ext rfl)⟩`.

Introduce and unpack `⟨j, rfl⟩`. Conclude with `⟨Fin.castLE hdn j, by simp, rfl⟩`. Establish `hUW : Submodule.span ℝ (v '' {k | (k : ℕ) < finrank ℝ W}) = W`. Use `Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr ?_) ?_` and prove the remaining obligations. Introduce and unpack `x ⟨k, hk, rfl⟩`.

Conclude with `hvW k hk`. Rewrite using `[himg]`. Conclude with `(finrank_span_eq_card (hv.comp _ (Fin.castLE_injective hdn))).trans (Fintype.card_fin _)`. Rewrite `huW` using `[← hUW]`. Use `Submodule.span_mono (Set.image_mono fun k hk => ?_) huW` and prove the remaining obligations.

Use `show k < i`. Conclude with `Fin.lt_iff_val_lt_val.mpr (lt_of_lt_of_le hk hdi)`.
-/
theorem Formalism.FN.existsSuccessiveMinimaVectors : Formalism.FN.SuccMinFacts := by
  classical
  intro E _ _ _ L _ _ K hKc hKv _ hK0
  have hmemK : ∀ {t : ℝ}, 0 ≤ t → ∀ u, u ∈ t • K ↔ gauge K u ≤ t :=
    fun ht u => mem_smul_iff_gauge hKc hKv hK0 ht u
  obtain ⟨T, hT0, hTtop⟩ := exists_span_top L hKc hKv hK0
  have hTfin : finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ T • K)) = finrank ℝ E := by
    rw [hTtop, finrank_top]
  have hmem : ∀ j, j ≤ finrank ℝ E → 0 ≤ succMin L K j ∧
      j ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ succMin L K j • K)) :=
    fun j hj => succMin_mem L hKc hKv hK0 ⟨hT0, by rw [hTfin]; exact hj⟩
  have hsub : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → (L : Set E) ∩ s • K ⊆ (L : Set E) ∩ t • K :=
    fun hs hst u hu => ⟨hu.1, (hmemK (hs.trans hst) u).mpr (((hmemK hs u).mp hu.2).trans hst)⟩
  have hle : ∀ {j : ℕ} {t : ℝ}, 0 ≤ t →
      j ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ t • K)) → succMin L K j ≤ t :=
    fun ht h => csInf_le ⟨0, fun x hx => hx.1⟩ ⟨ht, h⟩
  obtain ⟨m, hm0, hmbot⟩ := exists_pos_bot L hKc hKv hK0
  have hpos : ∀ j, 1 ≤ j → j ≤ finrank ℝ E → 0 < succMin L K j := by
    intro j hj1 hjn
    obtain ⟨h0, hj⟩ := hmem j hjn
    by_contra hneg
    push_neg at hneg
    rw [hmbot _ h0 (lt_of_le_of_lt hneg hm0), finrank_bot] at hj
    omega

  have build : ∀ k, k ≤ finrank ℝ E → ∃ w : Fin k → E, LinearIndependent ℝ w ∧
      ∀ j : Fin k, w j ∈ L ∧ w j ∈ succMin L K ((j : ℕ) + 1) • K := by
    intro k
    induction k with
    | zero => intro _; exact ⟨Fin.elim0, linearIndependent_empty_type, fun j => j.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨w, hw, hwm⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨_, hdim⟩ := hmem (k + 1) hk
      have hex : ∃ x ∈ (L : Set E) ∩ succMin L K (k + 1) • K,
          x ∉ Submodule.span ℝ (Set.range w) := by
        by_contra hno
        push_neg at hno
        have h1 := Submodule.finrank_mono (Submodule.span_le.mpr hno)
        rw [finrank_span_eq_card hw, Fintype.card_fin] at h1
        omega
      obtain ⟨x, ⟨hxL, hxK⟩, hxw⟩ := hex
      refine ⟨Fin.snoc w x, linearIndependent_fin_snoc.mpr ⟨hw, hxw⟩, fun j => ?_⟩
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.snoc_last, Fin.val_last]
        exact ⟨hxL, hxK⟩
      · simp only [Fin.snoc_castSucc, Fin.coe_castSucc]
        exact hwm i
  obtain ⟨v, hv, hvm⟩ := build (finrank ℝ E) le_rfl
  refine ⟨v, hv, fun i => (hvm i).1, fun i => (hvm i).2,
    fun i => hpos _ (by omega) (Nat.succ_le_of_lt i.isLt), ?_, ?_⟩
  · intro i j hij
    have hij' : (i : ℕ) ≤ j := hij
    obtain ⟨h0, hj⟩ := hmem ((j : ℕ) + 1) (Nat.succ_le_of_lt j.isLt)
    exact hle h0 (le_trans (by omega) hj)
  · intro i u huL huint
    have hlam : 0 < succMin L K ((i : ℕ) + 1) := hpos _ (by omega) (Nat.succ_le_of_lt i.isLt)

    have hg : gauge K u < succMin L K ((i : ℕ) + 1) := by
      obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp huint
      rw [gauge_smul_of_nonneg hlam.le, smul_eq_mul]
      exact mul_lt_of_lt_one_right hlam (interior_subset_gauge_lt_one K hy)
    have hg0 : 0 ≤ gauge K u := gauge_nonneg u
    set W := Submodule.span ℝ ((L : Set E) ∩ gauge K u • K) with hW
    have huW : u ∈ W := Submodule.subset_span ⟨huL, (hmemK hg0 u).mpr le_rfl⟩
    have hdn : finrank ℝ W ≤ finrank ℝ E := Submodule.finrank_le W
    have hdi : finrank ℝ W ≤ (i : ℕ) := by
      by_contra hcon
      push_neg at hcon
      have := hle hg0 (show (i : ℕ) + 1 ≤ finrank ℝ W by omega)
      linarith

    have hdW : succMin L K (finrank ℝ W) ≤ gauge K u := hle hg0 le_rfl
    have hvW : ∀ k : Fin (finrank ℝ E), (k : ℕ) < finrank ℝ W → v k ∈ W := by
      intro k hk
      obtain ⟨hd0, hd⟩ := hmem (finrank ℝ W) hdn
      have hk1 : succMin L K ((k : ℕ) + 1) ≤ gauge K u :=
        (hle hd0 (le_trans (by omega) hd)).trans hdW
      exact Submodule.subset_span
        (hsub (hmem _ (Nat.succ_le_of_lt k.isLt)).1 hk1 ⟨(hvm k).1, (hvm k).2⟩)
    have himg : v '' {k | (k : ℕ) < finrank ℝ W} =
        Set.range (fun j : Fin (finrank ℝ W) => v (Fin.castLE hdn j)) := by
      ext x
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact ⟨⟨k, hk⟩, congrArg v (Fin.ext rfl)⟩
      · rintro ⟨j, rfl⟩
        exact ⟨Fin.castLE hdn j, by simp, rfl⟩
    have hUW : Submodule.span ℝ (v '' {k | (k : ℕ) < finrank ℝ W}) = W := by
      refine Submodule.eq_of_le_of_finrank_eq
        (Submodule.span_le.mpr ?_) ?_
      · rintro x ⟨k, hk, rfl⟩
        exact hvW k hk
      · rw [himg]
        exact (finrank_span_eq_card (hv.comp _ (Fin.castLE_injective hdn))).trans
          (Fintype.card_fin _)
    rw [← hUW] at huW
    refine Submodule.span_mono (Set.image_mono fun k hk => ?_) huW
    show k < i
    exact Fin.lt_iff_val_lt_val.mpr (lt_of_lt_of_le hk hdi)
