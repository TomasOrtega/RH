import Mathlib

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

open Subgroup

variable {G : Type*} [Group G]

/- English proof (translation)
Establish `h1 : MulAction.stabilizer (MulAction.stabilizer G y) t = (MulAction.stabilizer G t).subgroupOf (MulAction.stabilizer G y)`. Use extensionality with `g`. Simplify using `[Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.smul_def]`. Establish `h2 : MulAction.orbit (MulAction.stabilizer G y) t = {x : X | ∃ g : G, g • y = y ∧ g • t = x}`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩`. Conclude with `⟨g, g.2, rfl⟩`. Introduce and unpack `⟨g, hg, rfl⟩`. Conclude with `⟨⟨g, hg⟩, rfl⟩`.

Rewrite using `[Subgroup.relIndex, ← h1, MulAction.index_stabilizer, h2]`.
-/
private theorem ncard_orbit_in_stabilizer_eq_relIndex {X Y : Type*} [MulAction G X] [MulAction G Y] (t : X) (y : Y) :
    {x : X | ∃ g : G, g • y = y ∧ g • t = x}.ncard =
      (MulAction.stabilizer G t).relIndex (MulAction.stabilizer G y) := by
  have h1 : MulAction.stabilizer (MulAction.stabilizer G y) t =
      (MulAction.stabilizer G t).subgroupOf (MulAction.stabilizer G y) := by
    ext g
    simp [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  have h2 : MulAction.orbit (MulAction.stabilizer G y) t = {x : X | ∃ g : G, g • y = y ∧ g • t = x} := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  rw [Subgroup.relIndex, ← h1, MulAction.index_stabilizer, h2]

/- English proof (translation)
Establish `hS` using `ncard_orbit_in_stabilizer_eq_relIndex (G := G) ((1 : G) : G ⧸ C) ((1 : G) : G ⧸ S)`. Establish `hH` using `ncard_orbit_in_stabilizer_eq_relIndex (G := G) ((1 : G) : G ⧸ C) ((1 : G) : G ⧸ H')`. Rewrite `hS`, `hH` using `[MulAction.stabilizer_quotient, MulAction.stabilizer_quotient]`. Rewrite using `[← hS, ← hH]`. Establish `hmem : ∀ (K : Subgroup G) (g : G), g • ((1 : G) : G ⧸ K) = ((1 : G) : G ⧸ K) ↔ g ∈ K` using `fun K g => by rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]`.

Use `congr 1`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, hmem]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, rfl⟩`.

Take `⟨t, ht, htg⟩` from `h2 g hg`. Use `⟨t⁻¹, H'.inv_mem ht, ?_⟩` and prove the remaining obligations. Rewrite using `[MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, QuotientGroup.eq]`. Simplify using `using htg`. Introduce and unpack `⟨g, hg, rfl⟩`.

Conclude with `⟨g, h1 hg, rfl⟩`.
-/
theorem relIndex_eq_of_cover (S C H' : Subgroup G) (h1 : H' ≤ S)
    (h2 : ∀ s ∈ S, ∃ t ∈ H', t * s ∈ C) : C.relIndex S = C.relIndex H' := by
  have hS := ncard_orbit_in_stabilizer_eq_relIndex (G := G) ((1 : G) : G ⧸ C) ((1 : G) : G ⧸ S)
  have hH := ncard_orbit_in_stabilizer_eq_relIndex (G := G) ((1 : G) : G ⧸ C) ((1 : G) : G ⧸ H')
  rw [MulAction.stabilizer_quotient, MulAction.stabilizer_quotient] at hS hH
  rw [← hS, ← hH]
  have hmem : ∀ (K : Subgroup G) (g : G), g • ((1 : G) : G ⧸ K) = ((1 : G) : G ⧸ K) ↔ g ∈ K :=
    fun K g => by rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, hmem]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨t, ht, htg⟩ := h2 g hg
    refine ⟨t⁻¹, H'.inv_mem ht, ?_⟩
    rw [MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, QuotientGroup.eq]
    simpa using htg
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, h1 hg, rfl⟩

/- English proof (translation)
Rewrite using `[← relIndex_eq_of_cover S C H' h1 h2, ← inf_relIndex_right C S, ← inf_relIndex_right S C, mul_comm, relIndex_mul_relIndex _ _ _ inf_le_right hS, mul_comm, relIndex_mul_relIndex _ _ _ inf_le_right hC, inf_comm]`.
-/
theorem index_tube (H S C H' : Subgroup G) (hS : S ≤ H) (hC : C ≤ H) (h1 : H' ≤ S)
    (h2 : ∀ s ∈ S, ∃ t ∈ H', t * s ∈ C) :
    S.relIndex H * C.relIndex H' = C.relIndex H * S.relIndex C := by
  rw [← relIndex_eq_of_cover S C H' h1 h2, ← inf_relIndex_right C S, ← inf_relIndex_right S C, mul_comm,
    relIndex_mul_relIndex _ _ _ inf_le_right hS, mul_comm, relIndex_mul_relIndex _ _ _ inf_le_right hC, inf_comm]

/- English proof (translation)
Establish `hBA' : B.relIndex A ≠ 0` using `relIndex_ne_zero_trans hCB hAC`. Establish `hAC' : A.relIndex C ≠ 0` using `relIndex_ne_zero_trans hBA hCB`. Establish `orbitMap_conj_smul_one` using `relIndex_inf_mul_relIndex C B A`. Establish `orbitMap_conj_smul_two` using `relIndex_inf_mul_relIndex B C A`. Establish `eB1` using `relIndex_inf_mul_relIndex A C B`.

Establish `eB2` using `relIndex_inf_mul_relIndex C A B`. Establish `eC1` using `relIndex_inf_mul_relIndex B A C`. Establish `eC2` using `relIndex_inf_mul_relIndex A B C`. Establish `EA : C.relIndex (A ⊓ B) * B.relIndex A = B.relIndex (A ⊓ C) * C.relIndex A`. Rewrite using `[inf_comm A B, inf_comm A C, orbitMap_conj_smul_one, orbitMap_conj_smul_two, inf_comm]`.

Establish `EB : A.relIndex (B ⊓ C) * C.relIndex B = C.relIndex (A ⊓ B) * A.relIndex B`. Rewrite using `[inf_comm B C, eB1, eB2, inf_comm]`. Establish `EC : B.relIndex (A ⊓ C) * A.relIndex C = A.relIndex (B ⊓ C) * B.relIndex C`. Rewrite using `[eC1, eC2, inf_comm]`. Establish `hu : C.relIndex (A ⊓ B) ≠ 0`.

Rewrite using `[inf_comm]`. Conclude with `left_ne_zero_of_mul (by rw [orbitMap_conj_smul_one]; exact relIndex_inf_ne_zero hAC hBA')`. Establish `hv : B.relIndex (A ⊓ C) ≠ 0` using `left_ne_zero_of_mul (by rw [eC1]; exact relIndex_inf_ne_zero hCB hAC')`. Establish `hw : A.relIndex (B ⊓ C) ≠ 0` using `left_ne_zero_of_mul (by rw [eC2]; exact relIndex_inf_ne_zero hAC' hCB)`. Apply `Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero hu hv) hw))` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem relIndex_cocycle (A B C : Subgroup G) (hAC : C.relIndex A ≠ 0) (hBA : A.relIndex B ≠ 0)
    (hCB : B.relIndex C ≠ 0) :
    B.relIndex A * C.relIndex B * A.relIndex C = A.relIndex B * B.relIndex C * C.relIndex A := by
  have hBA' : B.relIndex A ≠ 0 := relIndex_ne_zero_trans hCB hAC
  have hAC' : A.relIndex C ≠ 0 := relIndex_ne_zero_trans hBA hCB
  have orbitMap_conj_smul_one := relIndex_inf_mul_relIndex C B A
  have orbitMap_conj_smul_two := relIndex_inf_mul_relIndex B C A
  have eB1 := relIndex_inf_mul_relIndex A C B
  have eB2 := relIndex_inf_mul_relIndex C A B
  have eC1 := relIndex_inf_mul_relIndex B A C
  have eC2 := relIndex_inf_mul_relIndex A B C
  have EA : C.relIndex (A ⊓ B) * B.relIndex A = B.relIndex (A ⊓ C) * C.relIndex A := by
    rw [inf_comm A B, inf_comm A C, orbitMap_conj_smul_one, orbitMap_conj_smul_two, inf_comm]
  have EB : A.relIndex (B ⊓ C) * C.relIndex B = C.relIndex (A ⊓ B) * A.relIndex B := by
    rw [inf_comm B C, eB1, eB2, inf_comm]
  have EC : B.relIndex (A ⊓ C) * A.relIndex C = A.relIndex (B ⊓ C) * B.relIndex C := by
    rw [eC1, eC2, inf_comm]
  have hu : C.relIndex (A ⊓ B) ≠ 0 := by
    rw [inf_comm]
    exact left_ne_zero_of_mul (by rw [orbitMap_conj_smul_one]; exact relIndex_inf_ne_zero hAC hBA')
  have hv : B.relIndex (A ⊓ C) ≠ 0 :=
    left_ne_zero_of_mul (by rw [eC1]; exact relIndex_inf_ne_zero hCB hAC')
  have hw : A.relIndex (B ⊓ C) ≠ 0 :=
    left_ne_zero_of_mul (by rw [eC2]; exact relIndex_inf_ne_zero hAC' hCB)
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero hu hv) hw))
  calc C.relIndex (A ⊓ B) * B.relIndex (A ⊓ C) * A.relIndex (B ⊓ C) *
        (B.relIndex A * C.relIndex B * A.relIndex C)
      = (C.relIndex (A ⊓ B) * B.relIndex A) * (A.relIndex (B ⊓ C) * C.relIndex B) *
          (B.relIndex (A ⊓ C) * A.relIndex C) := by ring
    _ = (B.relIndex (A ⊓ C) * C.relIndex A) * (C.relIndex (A ⊓ B) * A.relIndex B) *
          (A.relIndex (B ⊓ C) * B.relIndex C) := by rw [EA, EB, EC]
    _ = _ := by ring

/- English proof (translation)
Use `revert hf hd`. Use `Finset.induction_on s (by simp) ?_` and prove the remaining obligations. Introduce `a s ha ih hf hd`. Establish `hfa : (f a).Finite` using `hf a (Finset.mem_insert_self a s)`. Establish `hfs : (⋃ i ∈ s, f i).Finite` using `Set.Finite.biUnion s.finite_toSet fun i hi => hf i (Finset.mem_insert_of_mem hi)`.

Establish `hdisj : Disjoint (f a) (⋃ i ∈ s, f i)`. Rewrite using `[Set.disjoint_iUnion₂_right]`. Introduce `i hi`. Conclude with `hd (by simp) (by simp [hi]) (fun h => ha (h ▸ hi))`. Rewrite using `[Finset.set_biUnion_insert, Finset.sum_insert ha, Set.ncard_union_eq hdisj hfa hfs, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (hd.subset (Finset.coe_subset.2 (Finset.subset_insert a s)))]`.
-/
theorem ncard_biUnion_finset {ι X : Type*} (s : Finset ι) (f : ι → Set X)
    (hf : ∀ i ∈ s, (f i).Finite) (hd : (s : Set ι).PairwiseDisjoint f) :
    (⋃ i ∈ s, f i).ncard = ∑ i ∈ s, (f i).ncard := by
  classical
  revert hf hd
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih hf hd
  have hfa : (f a).Finite := hf a (Finset.mem_insert_self a s)
  have hfs : (⋃ i ∈ s, f i).Finite :=
    Set.Finite.biUnion s.finite_toSet fun i hi => hf i (Finset.mem_insert_of_mem hi)
  have hdisj : Disjoint (f a) (⋃ i ∈ s, f i) := by
    rw [Set.disjoint_iUnion₂_right]
    intro i hi
    exact hd (by simp) (by simp [hi]) (fun h => ha (h ▸ hi))
  rw [Finset.set_biUnion_insert, Finset.sum_insert ha, Set.ncard_union_eq hdisj hfa hfs,
    ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (hd.subset (Finset.coe_subset.2 (Finset.subset_insert a s)))]

/- English proof (translation)
Conclude with `ncard_orbit_in_stabilizer_eq_relIndex t y`.
-/
theorem ncard_orb {X Y : Type*} [MulAction G X] [MulAction G Y] (t : X) (y : Y) :
    {x : X | ∃ g : G, g • y = y ∧ g • t = x}.ncard =
      (MulAction.stabilizer G t).relIndex (MulAction.stabilizer G y) := by
  exact ncard_orbit_in_stabilizer_eq_relIndex t y

/- English proof (translation)
Establish `hcard : ∀ y ∈ sY, (Nat.card {x // x ∈ A ∧ π x = y} : ℝ) = ∑ t ∈ sX.filter (fun t => π t = y), ((MulAction.stabilizer G t).relIndex (MulAction.stabilizer G (π t)) : ℝ)`. Introduce `y hy`. Establish `hfib : {x | x ∈ A ∧ π x = y} = ⋃ t ∈ sX.filter (fun t => π t = y), {x : X | ∃ g : G, g • y = y ∧ g • t = x}`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, exists_prop]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hxA, hxy⟩`. Take `⟨t, ⟨ht, g, hgt⟩, -⟩` from `hX x hxA`. Establish `h1 : π t = y` using `hY (π t) (hsX t ht).2 y hy ⟨g, by rw [← hπ, hgt, hxy]⟩`. Use `⟨t, ⟨ht, h1⟩, g, ?_, hgt⟩` and prove the remaining obligations.

Rewrite using `[← h1, ← hπ, hgt, hxy, h1]`. Introduce and unpack `⟨t, ⟨ht, h1⟩, g, hg, rfl⟩`. Use `⟨hA g t (hsX t ht).1, ?_⟩` and prove the remaining obligations. Rewrite using `[hπ, h1, hg]`. Establish `hfin' : ∀ t ∈ sX.filter (fun t => π t = y), {x : X | ∃ g : G, g • y = y ∧ g • t = x}.Finite`.

Introduce `t ht`. Rewrite `ht` using `[Finset.mem_filter]`. Apply `Set.finite_of_ncard_ne_zero` to reduce the goal to its premises. Rewrite using `[ncard_orb, ← ht.2]`. Conclude with `hfin t ht.1`.

Establish `hdisj : (↑(sX.filter (fun t => π t = y)) : Set X).PairwiseDisjoint (fun t => {x : X | ∃ g : G, g • y = y ∧ g • t = x})`. Introduce `t ht t' ht' hne`. Use `Set.disjoint_left.2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨g, -, rfl⟩ ⟨g', -, hg'⟩`. Rewrite `ht`, `ht'` using `[Finset.mem_coe, Finset.mem_filter]`.

Take `⟨t0, -, huniq⟩` from `hX (g • t) (hA g t (hsX t ht.1).1)`. Conclude with `hne ((huniq t ⟨ht.1, g, rfl⟩).trans (huniq t' ⟨ht'.1, g', hg'⟩).symm)`. Apply the tactic sequence `have hnc : Nat.card {x // x ∈ A ∧ π x = y} = ({x | x ∈ A ∧ π x = y} : Set X).ncard := by first | exact Nat.card_coe_set_eq _ | exact (Set.ncard_def _).symm`. Rewrite using `[hnc, hfib, ncard_biUnion_finset _ _ hfin' hdisj]`. Use `push_cast`.

Use `Finset.sum_congr rfl fun t ht => ?_` and prove the remaining obligations. Rewrite `ht` using `[Finset.mem_filter]`. Rewrite using `[ncard_orb, ht.2]`. Use `symm`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations. Rewrite using `[hcard y hy, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun t ht => ?_` and prove the remaining obligations. Rewrite using `[(Finset.mem_filter.1 ht).2]`. Use `_ = _ := Finset.sum_fiberwise_of_maps_to (fun t ht => (hsX t ht).2) _`.
-/
theorem sum_relIndex_fibre {X Y : Type*} [MulAction G X] [MulAction G Y] (π : X → Y)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x) (A : Set X) (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A)
    (sX : Finset X) (sY : Finset Y) (hsX : ∀ x ∈ sX, x ∈ A ∧ π x ∈ sY)
    (hX : ∀ x ∈ A, ∃! t, t ∈ sX ∧ ∃ g : G, g • t = x)
    (hY : ∀ y ∈ sY, ∀ y' ∈ sY, (∃ g : G, g • y = y') → y = y')
    (hfin : ∀ x ∈ sX, (MulAction.stabilizer G x).relIndex (MulAction.stabilizer G (π x)) ≠ 0)
    (w : Y → ℝ) :
    ∑ x ∈ sX, ((MulAction.stabilizer G x).relIndex (MulAction.stabilizer G (π x)) : ℝ) * w (π x) =
      ∑ y ∈ sY, (Nat.card {x // x ∈ A ∧ π x = y} : ℝ) * w y := by
  classical
  have hcard : ∀ y ∈ sY, (Nat.card {x // x ∈ A ∧ π x = y} : ℝ) =
      ∑ t ∈ sX.filter (fun t => π t = y),
        ((MulAction.stabilizer G t).relIndex (MulAction.stabilizer G (π t)) : ℝ) := by
    intro y hy
    have hfib : {x | x ∈ A ∧ π x = y} =
        ⋃ t ∈ sX.filter (fun t => π t = y), {x : X | ∃ g : G, g • y = y ∧ g • t = x} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, exists_prop]
      constructor
      · rintro ⟨hxA, hxy⟩
        obtain ⟨t, ⟨ht, g, hgt⟩, -⟩ := hX x hxA
        have h1 : π t = y := hY (π t) (hsX t ht).2 y hy ⟨g, by rw [← hπ, hgt, hxy]⟩
        refine ⟨t, ⟨ht, h1⟩, g, ?_, hgt⟩
        rw [← h1, ← hπ, hgt, hxy, h1]
      · rintro ⟨t, ⟨ht, h1⟩, g, hg, rfl⟩
        refine ⟨hA g t (hsX t ht).1, ?_⟩
        rw [hπ, h1, hg]
    have hfin' : ∀ t ∈ sX.filter (fun t => π t = y), {x : X | ∃ g : G, g • y = y ∧ g • t = x}.Finite := by
      intro t ht
      rw [Finset.mem_filter] at ht
      apply Set.finite_of_ncard_ne_zero
      rw [ncard_orb, ← ht.2]
      exact hfin t ht.1
    have hdisj : (↑(sX.filter (fun t => π t = y)) : Set X).PairwiseDisjoint
        (fun t => {x : X | ∃ g : G, g • y = y ∧ g • t = x}) := by
      intro t ht t' ht' hne
      refine Set.disjoint_left.2 ?_
      rintro x ⟨g, -, rfl⟩ ⟨g', -, hg'⟩
      rw [Finset.mem_coe, Finset.mem_filter] at ht ht'
      obtain ⟨t0, -, huniq⟩ := hX (g • t) (hA g t (hsX t ht.1).1)
      exact hne ((huniq t ⟨ht.1, g, rfl⟩).trans (huniq t' ⟨ht'.1, g', hg'⟩).symm)
    have hnc : Nat.card {x // x ∈ A ∧ π x = y} = ({x | x ∈ A ∧ π x = y} : Set X).ncard :=
      by first | exact Nat.card_coe_set_eq _ | exact (Set.ncard_def _).symm
    rw [hnc, hfib, ncard_biUnion_finset _ _ hfin' hdisj]
    push_cast
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_filter] at ht
    rw [ncard_orb, ht.2]
  symm
  calc ∑ y ∈ sY, (Nat.card {x // x ∈ A ∧ π x = y} : ℝ) * w y
      = ∑ y ∈ sY, ∑ t ∈ sX.filter (fun t => π t = y),
          ((MulAction.stabilizer G t).relIndex (MulAction.stabilizer G (π t)) : ℝ) * w (π t) := by
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [hcard y hy, Finset.sum_mul]
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [(Finset.mem_filter.1 ht).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun t ht => (hsX t ht).2) _

end Formalism.HermitianLattices.Ext.L3.LIOrb
