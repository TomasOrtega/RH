import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.OpenSlices.LatticeIndices.ValuationPiNeZero

noncomputable section

open Matrix GroundTheory.Automorphic ValuativeRel

namespace PositivityTheory.RgUd.T.Desc.SLT.Bi

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.T.Desc.SLT

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Take `⟨hxB, hxv⟩` from `hx`. Use `⟨fun a ha => ?_, fun r s => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_add, add_mul, mul_one, one_mul, hxB a ha]`. Establish `hpi : valuation k (pi k) ^ j ≤ 1` using `pow_le_one' (GLnLocal.valuation_uniformizer_lt_one k).le j`. Rewrite using `[pow_zero, Matrix.add_apply]`.

Use `(Valuation.map_add _ _ _).trans (max_le ?_ ((hxv r s).trans hpi))` and prove the remaining obligations. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Rewrite using `[map_one]`. Rewrite using `[map_zero]`.

Conclude with `zero_le'`.
-/
theorem one_add_mem_zero_lattice (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {j : ℕ} {x : Matrix (Fin n) (Fin n) k}
    (hx : x ∈ Lat Z j) : 1 + x ∈ Lat Z 0 := by
  obtain ⟨hxB, hxv⟩ := hx
  refine ⟨fun a ha => ?_, fun r s => ?_⟩
  · rw [mul_add, add_mul, mul_one, one_mul, hxB a ha]
  · have hpi : valuation k (pi k) ^ j ≤ 1 := pow_le_one' (GLnLocal.valuation_uniformizer_lt_one k).le j
    rw [pow_zero, Matrix.add_apply]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ((hxv r s).trans hpi))
    rw [Matrix.one_apply]
    split_ifs
    · rw [map_one]
    · rw [map_zero]
      exact zero_le'

/- English proof (translation)
Establish `hpi1 : valuation k (pi k) ^ m ≤ 1` using `pow_le_one' (GLnLocal.valuation_uniformizer_lt_one k).le m`. Establish `hpim : valuation k (pi k) ^ m ≤ valuation k (pi k) ^ 1` using `pow_le_pow_right_of_le_one' (GLnLocal.valuation_uniformizer_lt_one k).le hm`. Set `B : Matrix (Fin n) (Fin n) 𝒪[k]` to `fun i j => ⟨a i j, (ha i j).trans hpi1⟩`. Establish `hBm : ∀ i j, B i j ∈ IsLocalRing.maximalIdeal 𝒪[k]`. Introduce `i j`.

Use `(GLnLocal.mem_maximalIdeal_pow_iff k (m := 1) (y := B i j)).2 ((ha i j).trans hpim)` as an intermediate fact. Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis. Establish `hone : ∀ i j, (((1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j : 𝒪[k]) : k) = (1 : Matrix (Fin n) (Fin n) k) i j`. Introduce `i j`. Rewrite using `[Matrix.one_apply, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hdet : IsUnit (1 + B).det`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, map_add, map_one]`. Establish `h0 : (IsLocalRing.residue 𝒪[k]).mapMatrix B = 0`. Use extensionality with `i j`.

Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply]`. Conclude with `(IsLocalRing.residue_eq_zero_iff _).2 (hBm i j)`. Rewrite using `[h0, add_zero, Matrix.det_one]`. Conclude with `one_ne_zero`. Establish `hcoe : ∀ i j, ((((1 + B) i j : 𝒪[k])) : k) = (1 + a) i j`.

Introduce `i j`. Rewrite using `[Matrix.add_apply, Subring.coe_add, hone, Matrix.add_apply]`. Set `U : GL (Fin n) 𝒪[k]` to `Matrix.nonsingInvUnit (1 + B) hdet`. Use `⟨GLnLocal.integralGLHom k n U, ⟨U, ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Use `(GLnLocal.mem_ker_reduction_iff k n).2 fun i j => ?_` and prove the remaining obligations.

Establish `: ((U : Matrix (Fin n) (Fin n) 𝒪[k]) i j : k) = (1 + a) i j` using `hcoe i j`. Rewrite using `[this, Matrix.add_apply, add_sub_cancel_left]`. Conclude with `ha i j`. Use extensionality with `i j`. Rewrite using `[GLnLocal.integralGLHom_apply]`.

Conclude with `hcoe i j`.
-/
theorem exists_unit {m : ℕ} (hm : 1 ≤ m) {a : Matrix (Fin n) (Fin n) k}
    (ha : ∀ i j, valuation k (a i j) ≤ valuation k (pi k) ^ m) :
    ∃ h ∈ GLnLocal.congruenceSubgroup k n m, h.val = 1 + a := by
  have hpi1 : valuation k (pi k) ^ m ≤ 1 :=
    pow_le_one' (GLnLocal.valuation_uniformizer_lt_one k).le m
  have hpim : valuation k (pi k) ^ m ≤ valuation k (pi k) ^ 1 :=
    pow_le_pow_right_of_le_one' (GLnLocal.valuation_uniformizer_lt_one k).le hm
  let B : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨a i j, (ha i j).trans hpi1⟩
  have hBm : ∀ i j, B i j ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    intro i j
    have := (GLnLocal.mem_maximalIdeal_pow_iff k (m := 1) (y := B i j)).2 ((ha i j).trans hpim)
    rwa [pow_one] at this
  have hone : ∀ i j, (((1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j : 𝒪[k]) : k) = (1 : Matrix (Fin n) (Fin n) k) i j := by
    intro i j
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : IsUnit (1 + B).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, map_add, map_one]
    have h0 : (IsLocalRing.residue 𝒪[k]).mapMatrix B = 0 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply]
      exact (IsLocalRing.residue_eq_zero_iff _).2 (hBm i j)
    rw [h0, add_zero, Matrix.det_one]
    exact one_ne_zero
  have hcoe : ∀ i j, ((((1 + B) i j : 𝒪[k])) : k) = (1 + a) i j := by
    intro i j
    rw [Matrix.add_apply, Subring.coe_add, hone, Matrix.add_apply]
  let U : GL (Fin n) 𝒪[k] := Matrix.nonsingInvUnit (1 + B) hdet
  refine ⟨GLnLocal.integralGLHom k n U, ⟨U, ?_, rfl⟩, ?_⟩
  · refine (GLnLocal.mem_ker_reduction_iff k n).2 fun i j => ?_
    have : ((U : Matrix (Fin n) (Fin n) 𝒪[k]) i j : k) = (1 + a) i j := hcoe i j
    rw [this, Matrix.add_apply, add_sub_cancel_left]
    exact ha i j
  · ext i j
    rw [GLnLocal.integralGLHom_apply]
    exact hcoe i j

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hG, hC⟩`. Establish `hG' : h ∈ Gz Z` using `hG`. Establish `hC' : h ∈ GLnLocal.congruenceSubgroup k n m` using `hC`. Rewrite `hC'` using `[GLnLocal.mem_congruenceSubgroup_iff]`.

Use `⟨fun a ha => ?_, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_sub, sub_mul, mul_one, one_mul, hG' a ha]`. Rewrite using `[Matrix.sub_apply]`. Conclude with `hC'.2 i j`. Introduce `hx`.

Take `⟨h', hh', hv⟩` from `exists_unit hm hx.2`. Establish `heq : h' = h` using `Units.ext (by rw [hv]; abel)`. Establish `hG : h ∈ Gz Z`. Introduce `a ha`. Use `hx.1 a ha` as an intermediate fact.

Rewrite `this` using `[mul_sub, sub_mul, mul_one, one_mul]`. Conclude with `sub_left_inj.mp this`. Conclude with `⟨hG, heq ▸ hh'⟩`.
-/
theorem mem_Lc_iff (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {m : ℕ} (hm : 1 ≤ m) (h : GL (Fin n) k) :
    h ∈ Lc Z m ↔ h.val - 1 ∈ Lat Z m := by
  constructor
  · rintro ⟨hG, hC⟩
    have hG' : h ∈ Gz Z := hG
    have hC' : h ∈ GLnLocal.congruenceSubgroup k n m := hC
    rw [GLnLocal.mem_congruenceSubgroup_iff] at hC'
    refine ⟨fun a ha => ?_, fun i j => ?_⟩
    · rw [mul_sub, sub_mul, mul_one, one_mul, hG' a ha]
    · rw [Matrix.sub_apply]
      exact hC'.2 i j
  · intro hx
    obtain ⟨h', hh', hv⟩ := exists_unit hm hx.2
    have heq : h' = h := Units.ext (by rw [hv]; abel)
    have hG : h ∈ Gz Z := by
      intro a ha
      have := hx.1 a ha
      rw [mul_sub, sub_mul, mul_one, one_mul] at this
      exact sub_left_inj.mp this
    exact ⟨hG, heq ▸ hh'⟩

/- English proof (translation)
Take `⟨h, -, e⟩` from `exists_unit hm ha.2`. Use `⟨h, (mem_Lc_iff Z hm h).mpr ?_, e⟩` and prove the remaining obligations. Rewrite using `[e, add_sub_cancel_left]`. Conclude with `ha`.
-/
theorem exists_Lc (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {m : ℕ} (hm : 1 ≤ m)
    {a : Matrix (Fin n) (Fin n) k} (ha : a ∈ Lat Z m) : ∃ h ∈ Lc Z m, h.val = 1 + a := by
  obtain ⟨h, -, e⟩ := exists_unit hm ha.2
  refine ⟨h, (mem_Lc_iff Z hm h).mpr ?_, e⟩
  rw [e, add_sub_cancel_left]; exact ha

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Set `e : H ≃ A` to `{ toFun := fun x => ⟨(x : GL (Fin n) k).val - 1, h1 x x.2⟩ invFun := fun a => ⟨(h2 a a.2).choose, (h2 a a.2).choose_spec.1⟩ left_inv := fun x => by`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[(h2 _ (h1 x x.2)).choose_spec.2]`. Normalize the expressions using the abelian group laws.

Use `right_inv := fun a => by`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(h2 a a.2).choose.val - 1 = a`. Rewrite using `[(h2 a a.2).choose_spec.2]`. Use `abel }`.

Establish `key : ∀ x y : H, x⁻¹ * y ∈ K.subgroupOf H ↔ -(e x) + e y ∈ N.addSubgroupOf A`. Introduce `x y`. Rewrite using `[Subgroup.mem_subgroupOf, AddSubgroup.mem_addSubgroupOf, h4]`. Establish `hx : (x : GL (Fin n) k) ∈ H` using `x.2`. Establish `hinv : (x : GL (Fin n) k)⁻¹ ∈ H` using `H.inv_mem x.2`.

Express the relevant statement in the definitionally equal form `((x : GL (Fin n) k)⁻¹ * (y : GL (Fin n) k)).val - 1 ∈ N ↔ -((x : GL (Fin n) k).val - 1) + ((y : GL (Fin n) k).val - 1) ∈ N`. Establish `h6 : -((x : GL (Fin n) k).val - 1) + ((y : GL (Fin n) k).val - 1) = (y : GL (Fin n) k).val - (x : GL (Fin n) k).val` using `by abel`. Establish `h5 : ((x : GL (Fin n) k)⁻¹ * (y : GL (Fin n) k)).val - 1 = ((x : GL (Fin n) k)⁻¹).val * ((y : GL (Fin n) k).val - (x : GL (Fin n) k).val)`. Rewrite using `[Units.val_mul, mul_sub, Units.inv_mul]`. Rewrite using `[h5, h6]`.

Prove the components needed by the constructor for the conclusion. Introduce `hN`. Use `h3 _ hx _ hN` as an intermediate fact. Rewrite `this` using `[← mul_assoc, Units.mul_inv, one_mul]`. Then use the resulting hypothesis. Introduce `hN`.

Conclude with `h3 _ hinv _ hN`. Express the relevant statement in the definitionally equal form `Nat.card (H ⧸ K.subgroupOf H) = Nat.card (A ⧸ N.addSubgroupOf A)`. Conclude with `Nat.card_congr (Quotient.congr e fun x y => by`. Rewrite using `[QuotientGroup.leftRel_apply, QuotientAddGroup.leftRel_apply]`. Conclude with `key x y)`.
-/
theorem relIndex_eq_of_coset (H K : Subgroup (GL (Fin n) k)) (A N : AddSubgroup (Matrix (Fin n) (Fin n) k))
    (h1 : ∀ h ∈ H, h.val - 1 ∈ A) (h2 : ∀ a ∈ A, ∃ h ∈ H, h.val = 1 + a)
    (h3 : ∀ h ∈ H, ∀ x ∈ N, h.val * x ∈ N) (h4 : ∀ h, h ∈ K ↔ h.val - 1 ∈ N) :
    K.relIndex H = N.relIndex A := by
  let e : H ≃ A :=
    { toFun := fun x => ⟨(x : GL (Fin n) k).val - 1, h1 x x.2⟩
      invFun := fun a => ⟨(h2 a a.2).choose, (h2 a a.2).choose_spec.1⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply Units.ext
        rw [(h2 _ (h1 x x.2)).choose_spec.2]
        abel
      right_inv := fun a => by
        apply Subtype.ext
        change (h2 a a.2).choose.val - 1 = a
        rw [(h2 a a.2).choose_spec.2]
        abel }
  have key : ∀ x y : H, x⁻¹ * y ∈ K.subgroupOf H ↔ -(e x) + e y ∈ N.addSubgroupOf A := by
    intro x y
    rw [Subgroup.mem_subgroupOf, AddSubgroup.mem_addSubgroupOf, h4]
    have hx : (x : GL (Fin n) k) ∈ H := x.2
    have hinv : (x : GL (Fin n) k)⁻¹ ∈ H := H.inv_mem x.2
    change ((x : GL (Fin n) k)⁻¹ * (y : GL (Fin n) k)).val - 1 ∈ N ↔
      -((x : GL (Fin n) k).val - 1) + ((y : GL (Fin n) k).val - 1) ∈ N
    have h6 : -((x : GL (Fin n) k).val - 1) + ((y : GL (Fin n) k).val - 1) =
        (y : GL (Fin n) k).val - (x : GL (Fin n) k).val := by abel
    have h5 : ((x : GL (Fin n) k)⁻¹ * (y : GL (Fin n) k)).val - 1 =
        ((x : GL (Fin n) k)⁻¹).val * ((y : GL (Fin n) k).val - (x : GL (Fin n) k).val) := by
      rw [Units.val_mul, mul_sub, Units.inv_mul]
    rw [h5, h6]
    constructor
    · intro hN
      have := h3 _ hx _ hN
      rwa [← mul_assoc, Units.mul_inv, one_mul] at this
    · intro hN
      exact h3 _ hinv _ hN
  change Nat.card (H ⧸ K.subgroupOf H) = Nat.card (A ⧸ N.addSubgroupOf A)
  exact Nat.card_congr (Quotient.congr e fun x y => by
    rw [QuotientGroup.leftRel_apply, QuotientAddGroup.leftRel_apply]
    exact key x y)

/- English proof (translation)
Use `⟨fun a ha => ?_, fun r s => ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, hy.1 a ha, mul_assoc, hx.1 a ha, mul_assoc]`. Rewrite using `[Matrix.mul_apply]`. Use `Valuation.map_sum_le _ fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Combine the equalities or inequalities in the displayed calculation.
-/
private theorem mul_mem_Lat_of_mem_Lat_zero (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {j : ℕ}
    {y x : Matrix (Fin n) (Fin n) k} (hy : y ∈ Lat Z 0) (hx : x ∈ Lat Z j) : y * x ∈ Lat Z j := by
  refine ⟨fun a ha => ?_, fun r s => ?_⟩
  · rw [← mul_assoc, hy.1 a ha, mul_assoc, hx.1 a ha, mul_assoc]
  · rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    calc _ ≤ 1 * valuation k (pi k) ^ j :=
          mul_le_mul' ((hy.2 r l).trans_eq (pow_zero _)) (hx.2 l s)
      _ = _ := one_mul _

/- English proof (translation)
Apply `relIndex_eq_of_coset` to reduce the goal to its premises. Introduce `h hh`. Conclude with `(mem_Lc_iff Z hm h).1 hh`. Introduce `a ha`. Conclude with `exists_Lc Z hm ha`.

Introduce `h hh x hx`. Use `one_add_mem_zero_lattice Z ((mem_Lc_iff Z hm h).1 hh)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Conclude with `mul_mem_Lat_of_mem_Lat_zero Z this hx`. Introduce `h`.

Conclude with `mem_Lc_iff Z (hm.trans hmm) h`.
-/
theorem relIndex_Lc (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {m m' : ℕ} (hm : 1 ≤ m) (hmm : m ≤ m') :
    (Lc Z m').relIndex (Lc Z m) = (Lat Z m').relIndex (Lat Z m) := by
  apply relIndex_eq_of_coset
  · intro h hh
    exact (mem_Lc_iff Z hm h).1 hh
  · intro a ha
    exact exists_Lc Z hm ha
  · intro h hh x hx
    have := one_add_mem_zero_lattice Z ((mem_Lc_iff Z hm h).1 hh)
    rw [add_sub_cancel] at this
    exact mul_mem_Lat_of_mem_Lat_zero Z this hx
  · intro h
    exact mem_Lc_iff Z (hm.trans hmm) h

/- English proof (translation)
Apply `relIndex_eq_of_coset` to reduce the goal to its premises. Introduce `h hh`. Take `⟨h0, hh0, rfl⟩` from `Subgroup.mem_map.1 hh`. Use `AddSubgroup.mem_map.2 ⟨h0.val - 1, (mem_Lc_iff Z hm h0).1 hh0, ?_⟩` and prove the remaining obligations. Rewrite using `[conjA_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.mul_inv]`.

Introduce `a ha`. Take `⟨a0, ha0, rfl⟩` from `AddSubgroup.mem_map.1 ha`. Take `⟨h0, hh0, hv⟩` from `exists_Lc Z hm ha0`. Use `⟨g * h0 * g⁻¹, Subgroup.mem_map.2 ⟨h0, hh0, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[conjA_apply, Units.val_mul, Units.val_mul, hv, mul_add, add_mul, mul_one, Units.mul_inv]`.

Introduce `h hh x hx`. Take `⟨h0, hh0, rfl⟩` from `Subgroup.mem_map.1 hh`. Establish `hd : h0.val - 1 ∈ Lat Z ((m - c) + c)`. Rewrite using `[Nat.sub_add_cancel hcm]`. Conclude with `(mem_Lc_iff Z hm h0).1 hh0`.

Establish `hy` using `one_add_mem_zero_lattice Z (hc _ _ hd).1`. Establish `he : 1 + conjA g (h0.val - 1) = ((MulAut.conj g).toMonoidHom h0).val`. Rewrite using `[conjA_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.mul_inv]`. Normalize the expressions using the abelian group laws. Rewrite `hy` using `[he]`.

Conclude with `mul_mem_Lat_of_mem_Lat_zero Z hy hx`. Introduce `h`. Conclude with `mem_Lc_iff Z (hm.trans hmm) h`.
-/
theorem relIndex_Lc_conj (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (g : GL (Fin n) k) (hg : g ∈ Gz Z)
    (c : ℕ) (hc : ∀ j : ℕ, ∀ x ∈ Lat Z (j + c), conjA g x ∈ Lat Z j ∧ conjA g⁻¹ x ∈ Lat Z j)
    {m m' : ℕ} (hm : 1 ≤ m) (hcm : c ≤ m) (hmm : m ≤ m') :
    (Lc Z m').relIndex ((Lc Z m).map (MulAut.conj g).toMonoidHom) =
      (Lat Z m').relIndex ((Lat Z m).map (conjA g)) := by
  apply relIndex_eq_of_coset
  · intro h hh
    obtain ⟨h0, hh0, rfl⟩ := Subgroup.mem_map.1 hh
    refine AddSubgroup.mem_map.2 ⟨h0.val - 1, (mem_Lc_iff Z hm h0).1 hh0, ?_⟩
    rw [conjA_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul, Units.val_mul,
      mul_sub, sub_mul, mul_one, Units.mul_inv]
  · intro a ha
    obtain ⟨a0, ha0, rfl⟩ := AddSubgroup.mem_map.1 ha
    obtain ⟨h0, hh0, hv⟩ := exists_Lc Z hm ha0
    refine ⟨g * h0 * g⁻¹, Subgroup.mem_map.2 ⟨h0, hh0, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩, ?_⟩
    rw [conjA_apply, Units.val_mul, Units.val_mul, hv, mul_add, add_mul, mul_one, Units.mul_inv]
  · intro h hh x hx
    obtain ⟨h0, hh0, rfl⟩ := Subgroup.mem_map.1 hh
    have hd : h0.val - 1 ∈ Lat Z ((m - c) + c) := by
      rw [Nat.sub_add_cancel hcm]
      exact (mem_Lc_iff Z hm h0).1 hh0
    have hy := one_add_mem_zero_lattice Z (hc _ _ hd).1
    have he : 1 + conjA g (h0.val - 1) = ((MulAut.conj g).toMonoidHom h0).val := by
      rw [conjA_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul, Units.val_mul,
        mul_sub, sub_mul, mul_one, Units.mul_inv]
      abel
    rw [he] at hy
    exact mul_mem_Lat_of_mem_Lat_zero Z hy hx
  · intro h
    exact mem_Lc_iff Z (hm.trans hmm) h

/- English proof (translation)
Introduce `h hh`. Establish `hm' : 1 ≤ m'` using `by omega`. Establish `hx` using `(mem_Lc_iff Z hm' h).1 hh`. Use `⟨(mem_Lc_iff Z hm h).2 (Lat_anti Z (by omega) hx), ?_⟩` and prove the remaining obligations. Establish `hx' : h.val - 1 ∈ Lat Z (m + c)` using `Lat_anti Z hmm hx`.

Establish `h0 : g⁻¹ * h * g ∈ Lc Z m`. Use `(mem_Lc_iff Z hm _).2 ?_` and prove the remaining obligations. Use `(hc m _ hx').2` as an intermediate fact. Rewrite `this` using `[conjA_apply, inv_inv]`. Use `this using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.inv_mul]`. Use `Subgroup.mem_map.2 ⟨_, h0, ?_⟩` and prove the remaining obligations. Rewrite using `[MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Use `group`.
-/
theorem Lc_le (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (g : GL (Fin n) k) (hg : g ∈ Gz Z)
    (c : ℕ) (hc : ∀ j : ℕ, ∀ x ∈ Lat Z (j + c), conjA g x ∈ Lat Z j ∧ conjA g⁻¹ x ∈ Lat Z j)
    {m m' : ℕ} (hm : 1 ≤ m) (hmm : m + c ≤ m') :
    Lc Z m' ≤ Lc Z m ⊓ (Lc Z m).map (MulAut.conj g).toMonoidHom := by
  intro h hh
  have hm' : 1 ≤ m' := by omega
  have hx := (mem_Lc_iff Z hm' h).1 hh
  refine ⟨(mem_Lc_iff Z hm h).2 (Lat_anti Z (by omega) hx), ?_⟩
  have hx' : h.val - 1 ∈ Lat Z (m + c) := Lat_anti Z hmm hx
  have h0 : g⁻¹ * h * g ∈ Lc Z m := by
    refine (mem_Lc_iff Z hm _).2 ?_
    have := (hc m _ hx').2
    rw [conjA_apply, inv_inv] at this
    convert this using 1
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.inv_mul]
  refine Subgroup.mem_map.2 ⟨_, h0, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end PositivityTheory.RgUd.T.Desc.SLT.Bi
