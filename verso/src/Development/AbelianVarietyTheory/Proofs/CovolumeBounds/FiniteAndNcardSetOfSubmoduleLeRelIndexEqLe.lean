import Mathlib

open Module

namespace GlobalTheory

section Subgroups

variable {M : Type*} [AddCommGroup M]

/- English proof (translation)
Use `haveI : Fact p.Prime := ⟨hp⟩`. Establish `e : (M ⧸ H) ≃+ ZMod p` using `addEquivOfPrimeCardEq (p := p) hH (Nat.card_zmod p)`. Use `⟨(e.toAddMonoidHom.comp (QuotientAddGroup.mk' H)).toIntLinearMap, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Simplify using `[AddMonoidHom.mem_ker]`.
-/
theorem exists_ker_eq_of_index_prime {p : ℕ} (hp : p.Prime) (H : AddSubgroup M)
    (hH : H.index = p) : ∃ f : M →ₗ[ℤ] ZMod p, f.toAddMonoidHom.ker = H := by
  haveI : Fact p.Prime := ⟨hp⟩
  have e : (M ⧸ H) ≃+ ZMod p := addEquivOfPrimeCardEq (p := p) hH (Nat.card_zmod p)
  refine ⟨(e.toAddMonoidHom.comp (QuotientAddGroup.mk' H)).toIntLinearMap, ?_⟩
  ext x
  simp [AddMonoidHom.mem_ker]

/- English proof (translation)
Use `haveI : NeZero p := ⟨hp.ne_zero⟩`. Set `b` to `Module.finBasis ℤ M`. Set `φ : (Fin (finrank ℤ M) → ZMod p) → AddSubgroup M` to `fun w => (b.constr ℤ w).toAddMonoidHom.ker`. Establish `hsub : {H : AddSubgroup M | H.index = p} ⊆ φ '' Set.univ`. Introduce `H hH`.

Take `⟨f, hf⟩` from `exists_ker_eq_of_index_prime hp H hH`. Use `⟨(b.constr ℤ).symm f, Set.mem_univ _, ?_⟩` and prove the remaining obligations. Simplify using `only [φ, LinearEquiv.apply_symm_apply]`. Conclude with `hf`. Use `(Set.encard_le_encard hsub).trans ((Set.encard_image_le _ _).trans ?_)` and prove the remaining obligations.

Rewrite using `[Set.encard_univ, ENat.card_eq_coe_fintype_card]`. Simplify using the standard rewrite rules.
-/
theorem encard_setOf_index_prime_le [Module.Free ℤ M] [Module.Finite ℤ M] {p : ℕ}
    (hp : p.Prime) :
    {H : AddSubgroup M | H.index = p}.encard ≤ ((p ^ finrank ℤ M : ℕ) : ℕ∞) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let b := Module.finBasis ℤ M
  let φ : (Fin (finrank ℤ M) → ZMod p) → AddSubgroup M :=
    fun w => (b.constr ℤ w).toAddMonoidHom.ker
  have hsub : {H : AddSubgroup M | H.index = p} ⊆ φ '' Set.univ := by
    intro H hH
    obtain ⟨f, hf⟩ := exists_ker_eq_of_index_prime hp H hH
    refine ⟨(b.constr ℤ).symm f, Set.mem_univ _, ?_⟩
    simp only [φ, LinearEquiv.apply_symm_apply]
    exact hf
  refine (Set.encard_le_encard hsub).trans ((Set.encard_image_le _ _).trans ?_)
  rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]
  simp

/- English proof (translation)
Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `haveI : H.FiniteIndex := ⟨h0⟩`. Take `⟨x, hx⟩` from `exists_prime_addOrderOf_dvd_card' (G := M ⧸ H) p hd`. Use `⟨(AddSubgroup.zmultiples x).comap (QuotientAddGroup.mk' H), ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`.

Simplify using `only [AddSubgroup.mem_comap, QuotientAddGroup.mk'_apply]`. Rewrite using `[(QuotientAddGroup.eq_zero_iff y).2 hy]`. Conclude with `zero_mem _`. Establish `h1 : H = (⊥ : AddSubgroup (M ⧸ H)).comap (QuotientAddGroup.mk' H)`. Use extensionality with `y`.

Simplify using the standard rewrite rules. Establish `h2` using `AddSubgroup.relIndex_comap (⊥ : AddSubgroup (M ⧸ H)) (QuotientAddGroup.mk' H) ((AddSubgroup.zmultiples x).comap (QuotientAddGroup.mk' H))`. Rewrite `h2` using `[← h1, AddSubgroup.map_comap_eq_self_of_surjective (QuotientAddGroup.mk'_surjective H), AddSubgroup.relIndex_bot_left, Nat.card_zmultiples, hx]`. Conclude with `h2`.
-/
theorem exists_le_relIndex_eq_prime {p : ℕ} (hp : p.Prime) (H : AddSubgroup M)
    (h0 : H.index ≠ 0) (hd : p ∣ H.index) :
    ∃ K : AddSubgroup M, H ≤ K ∧ H.relIndex K = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : H.FiniteIndex := ⟨h0⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := M ⧸ H) p hd
  refine ⟨(AddSubgroup.zmultiples x).comap (QuotientAddGroup.mk' H), ?_, ?_⟩
  · intro y hy
    simp only [AddSubgroup.mem_comap, QuotientAddGroup.mk'_apply]
    rw [(QuotientAddGroup.eq_zero_iff y).2 hy]
    exact zero_mem _
  · have h1 : H = (⊥ : AddSubgroup (M ⧸ H)).comap (QuotientAddGroup.mk' H) := by
      ext y; simp
    have h2 := AddSubgroup.relIndex_comap (⊥ : AddSubgroup (M ⧸ H)) (QuotientAddGroup.mk' H)
      ((AddSubgroup.zmultiples x).comap (QuotientAddGroup.mk' H))
    rw [← h1, AddSubgroup.map_comap_eq_self_of_surjective (QuotientAddGroup.mk'_surjective H),
      AddSubgroup.relIndex_bot_left, Nat.card_zmultiples, hx] at h2
    exact h2

/- English proof (translation)
Establish `hfin : s.Finite` using `Set.finite_of_encard_le_coe hs`. Establish `key : (⋃ i ∈ s, t i).encard ≤ s.encard * b` using `by clear hs`. Proceed by induction on `s, hfin using Set.Finite.induction_on with`. Consider the case `empty => simp`. Consider the case `@insert i s hi _ ih`.

Rewrite using `[Set.biUnion_insert, Set.encard_insert_of_notMem hi, add_mul, one_mul, add_comm]`. Conclude with `(Set.encard_union_le _ _).trans (add_le_add (ht i (Set.mem_insert _ _)) (ih fun j hj => ht j (Set.mem_insert_of_mem _ hj)))`. Use `key.trans ?_` and prove the remaining obligations. Use `push_cast`. Use `gcongr`.
-/
theorem encard_biUnion_le_mul {α β : Type*} (s : Set α) (t : α → Set β) (a b : ℕ)
    (hs : s.encard ≤ a) (ht : ∀ i ∈ s, (t i).encard ≤ b) :
    (⋃ i ∈ s, t i).encard ≤ ((a * b : ℕ) : ℕ∞) := by
  have hfin : s.Finite := Set.finite_of_encard_le_coe hs
  have key : (⋃ i ∈ s, t i).encard ≤ s.encard * b := by
    clear hs
    induction s, hfin using Set.Finite.induction_on with
    | empty => simp
    | @insert i s hi _ ih =>
      rw [Set.biUnion_insert, Set.encard_insert_of_notMem hi, add_mul, one_mul, add_comm]
      exact (Set.encard_union_le _ _).trans (add_le_add (ht i (Set.mem_insert _ _))
        (ih fun j hj => ht j (Set.mem_insert_of_mem _ hj)))
  refine key.trans ?_
  push_cast
  gcongr

/- English proof (translation)
Use extensionality with `H`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨H.addSubgroupOf K, h2, by simp [AddSubgroup.addSubgroupOf_map_subtype, h1]⟩`. Introduce and unpack `⟨H', h, rfl⟩`.

Use `⟨AddSubgroup.map_subtype_le _, ?_⟩` and prove the remaining obligations. Rewrite using `[AddSubgroup.relIndex, AddSubgroup.addSubgroupOf, AddSubgroup.comap_map_eq_self_of_injective K.subtype_injective]`. Conclude with `h`.
-/
theorem setOf_le_relIndex_eq_image (K : AddSubgroup M) (m : ℕ) :
    {H : AddSubgroup M | H ≤ K ∧ H.relIndex K = m} =
      (fun H' : AddSubgroup K => H'.map K.subtype) '' {H' | H'.index = m} := by
  ext H
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨H.addSubgroupOf K, h2, by simp [AddSubgroup.addSubgroupOf_map_subtype, h1]⟩
  · rintro ⟨H', h, rfl⟩
    refine ⟨AddSubgroup.map_subtype_le _, ?_⟩
    rw [AddSubgroup.relIndex, AddSubgroup.addSubgroupOf,
      AddSubgroup.comap_map_eq_self_of_injective K.subtype_injective]
    exact h

/- English proof (translation)
Proceed by induction on `m using induction_on_primes with`. Consider the case `zero => exact absurd rfl hm`. Consider the case `one`. Establish `: {H : AddSubgroup M | H.index = 1} = {⊤}` using `by ext H; simp`. Simplify using `[this]`.

Consider the case `prime_mul p a hp ih`. Establish `ha : a ≠ 0` using `fun h => hm (by simp [h])`. Establish `hsub : {H : AddSubgroup M | H.index = p * a} ⊆ ⋃ K ∈ {K : AddSubgroup M | K.index = a}, {H | H ≤ K ∧ H.relIndex K = p}`. Introduce `H hH`. Establish `hH' : H.index = p * a` using `hH`.

Take `⟨K, hK, hr⟩` from `exists_le_relIndex_eq_prime hp H (hH' ▸ hm) (hH' ▸ dvd_mul_right _ _)`. Use `AddSubgroup.relIndex_mul_index hK` as an intermediate fact. Rewrite `this` using `[hr, hH']`. Conclude with `Set.mem_biUnion (x := K) (Nat.eq_of_mul_eq_mul_left hp.pos this) ⟨hK, hr⟩`. Use `(Set.encard_le_encard hsub).trans ((encard_biUnion_le_mul _ _ _ (p ^ finrank ℤ M) (ih ha) ?_).trans ?_)` and prove the remaining obligations.

Introduce `K _`. Rewrite using `[setOf_le_relIndex_eq_image]`. Use `(Set.encard_image_le _ _).trans ?_` and prove the remaining obligations. Use `haveI : Module.Finite ℤ K := inferInstanceAs (Module.Finite ℤ K.toIntSubmodule)`. Use `haveI : Module.Free ℤ K := inferInstanceAs (Module.Free ℤ K.toIntSubmodule)`.

Use `(encard_setOf_index_prime_le hp).trans ?_` and prove the remaining obligations. Establish `: finrank ℤ K ≤ finrank ℤ M` using `Submodule.finrank_le K.toIntSubmodule`. Conclude with `Nat.pow_le_pow_right hp.pos this` after adjusting the coercions. Rewrite using `[mul_pow, mul_comm]`.
-/
theorem encard_setOf_index_eq_le [Module.Free ℤ M] [Module.Finite ℤ M] {m : ℕ} (hm : m ≠ 0) :
    {H : AddSubgroup M | H.index = m}.encard ≤ ((m ^ finrank ℤ M : ℕ) : ℕ∞) := by
  induction m using induction_on_primes with
  | zero => exact absurd rfl hm
  | one =>
    have : {H : AddSubgroup M | H.index = 1} = {⊤} := by ext H; simp
    simp [this]
  | prime_mul p a hp ih =>
    have ha : a ≠ 0 := fun h => hm (by simp [h])
    have hsub : {H : AddSubgroup M | H.index = p * a} ⊆
        ⋃ K ∈ {K : AddSubgroup M | K.index = a}, {H | H ≤ K ∧ H.relIndex K = p} := by
      intro H hH
      have hH' : H.index = p * a := hH
      obtain ⟨K, hK, hr⟩ := exists_le_relIndex_eq_prime hp H (hH' ▸ hm) (hH' ▸ dvd_mul_right _ _)
      have := AddSubgroup.relIndex_mul_index hK
      rw [hr, hH'] at this
      exact Set.mem_biUnion (x := K) (Nat.eq_of_mul_eq_mul_left hp.pos this) ⟨hK, hr⟩
    refine (Set.encard_le_encard hsub).trans
      ((encard_biUnion_le_mul _ _ _ (p ^ finrank ℤ M) (ih ha) ?_).trans ?_)
    · intro K _
      rw [setOf_le_relIndex_eq_image]
      refine (Set.encard_image_le _ _).trans ?_
      haveI : Module.Finite ℤ K := inferInstanceAs (Module.Finite ℤ K.toIntSubmodule)
      haveI : Module.Free ℤ K := inferInstanceAs (Module.Free ℤ K.toIntSubmodule)
      refine (encard_setOf_index_prime_le hp).trans ?_
      have : finrank ℤ K ≤ finrank ℤ M := Submodule.finrank_le K.toIntSubmodule
      exact_mod_cast Nat.pow_le_pow_right hp.pos this
    · rw [mul_pow, mul_comm]

/- English proof (translation)
The claim follows from `Set.finite_of_encard_le_coe (encard_setOf_index_eq_le hm)`.
-/
theorem finite_setOf_index_eq [Module.Free ℤ M] [Module.Finite ℤ M] {m : ℕ} (hm : m ≠ 0) :
    {H : AddSubgroup M | H.index = m}.Finite :=
  Set.finite_of_encard_le_coe (encard_setOf_index_eq_le hm)

/- English proof (translation)
Establish `h` using `encard_setOf_index_eq_le (M := M) hm`. Rewrite `h` using `[← (finite_setOf_index_eq (M := M) hm).cast_ncard_eq]`. Conclude with `h` after adjusting the coercions.
-/
theorem ncard_setOf_index_eq_le [Module.Free ℤ M] [Module.Finite ℤ M] {m : ℕ} (hm : m ≠ 0) :
    {H : AddSubgroup M | H.index = m}.ncard ≤ m ^ finrank ℤ M := by
  have h := encard_setOf_index_eq_le (M := M) hm
  rw [← (finite_setOf_index_eq (M := M) hm).cast_ncard_eq] at h
  exact_mod_cast h

/- English proof (translation)
Use `⟨finite_setOf_index_eq hm, ?_⟩` and prove the remaining obligations. Simplify using `using ncard_setOf_index_eq_le (M := Fin ρ → ℤ) hm`.
-/
theorem finite_and_ncard_setOf_index_pi_le (ρ : ℕ) {m : ℕ} (hm : m ≠ 0) :
    {H : AddSubgroup (Fin ρ → ℤ) | H.index = m}.Finite ∧
      {H : AddSubgroup (Fin ρ → ℤ) | H.index = m}.ncard ≤ m ^ ρ := by
  refine ⟨finite_setOf_index_eq hm, ?_⟩
  simpa using ncard_setOf_index_eq_le (M := Fin ρ → ℤ) hm

/- English proof (translation)
Rewrite using `[setOf_le_relIndex_eq_image]`. Conclude with `(Set.encard_image_le _ _).trans (encard_setOf_index_eq_le hm)`.
-/
theorem encard_setOf_le_relIndex_eq_le (K : AddSubgroup M) [Module.Free ℤ K] [Module.Finite ℤ K]
    {m : ℕ} (hm : m ≠ 0) :
    {H : AddSubgroup M | H ≤ K ∧ H.relIndex K = m}.encard ≤ ((m ^ finrank ℤ K : ℕ) : ℕ∞) := by
  rw [setOf_le_relIndex_eq_image]
  exact (Set.encard_image_le _ _).trans (encard_setOf_index_eq_le hm)

/- English proof (translation)
Use `haveI : Module.Free ℤ L.toAddSubgroup := inferInstanceAs (Module.Free ℤ L)`. Use `haveI : Module.Finite ℤ L.toAddSubgroup := inferInstanceAs (Module.Finite ℤ L)`. Use `le_trans ?_ (encard_setOf_le_relIndex_eq_le L.toAddSubgroup hm)` and prove the remaining obligations. Use `Set.encard_le_encard_of_injOn (f := Submodule.toAddSubgroup) ?_ Submodule.toAddSubgroup_injective.injOn` and prove the remaining obligations. Introduce and unpack `H ⟨h1, h2⟩`.

Conclude with `⟨h1, h2⟩`.
-/
theorem encard_setOf_submodule_le_relIndex_eq_le {R : Type*} [Ring R] [Module R M]
    (L : Submodule R M) [Module.Free ℤ L] [Module.Finite ℤ L] {m : ℕ} (hm : m ≠ 0) :
    {H : Submodule R M | H ≤ L ∧ H.toAddSubgroup.relIndex L.toAddSubgroup = m}.encard ≤
      ((m ^ finrank ℤ L : ℕ) : ℕ∞) := by
  haveI : Module.Free ℤ L.toAddSubgroup := inferInstanceAs (Module.Free ℤ L)
  haveI : Module.Finite ℤ L.toAddSubgroup := inferInstanceAs (Module.Finite ℤ L)
  refine le_trans ?_ (encard_setOf_le_relIndex_eq_le L.toAddSubgroup hm)
  refine Set.encard_le_encard_of_injOn (f := Submodule.toAddSubgroup) ?_
    Submodule.toAddSubgroup_injective.injOn
  rintro H ⟨h1, h2⟩
  exact ⟨h1, h2⟩

/- English proof (translation)
Establish `h` using `encard_setOf_submodule_le_relIndex_eq_le L hm`. Establish `hf` using `Set.finite_of_encard_le_coe h`. Use `⟨hf, ?_⟩` and prove the remaining obligations. Rewrite `h` using `[← hf.cast_ncard_eq]`. Conclude with `h` after adjusting the coercions.
-/
theorem finite_and_ncard_setOf_submodule_le_relIndex_eq_le {R : Type*} [Ring R] [Module R M]
    (L : Submodule R M) [Module.Free ℤ L] [Module.Finite ℤ L] {m : ℕ} (hm : m ≠ 0) :
    {H : Submodule R M | H ≤ L ∧ H.toAddSubgroup.relIndex L.toAddSubgroup = m}.Finite ∧
    {H : Submodule R M | H ≤ L ∧ H.toAddSubgroup.relIndex L.toAddSubgroup = m}.ncard ≤
      m ^ finrank ℤ L := by
  have h := encard_setOf_submodule_le_relIndex_eq_le L hm
  have hf := Set.finite_of_encard_le_coe h
  refine ⟨hf, ?_⟩
  rw [← hf.cast_ncard_eq] at h
  exact_mod_cast h

end Subgroups

section DeterminedMaps

open MeasureTheory Metric

/- English proof (translation)
Use `borelize V`. Set `μ : Measure V` to `Measure.addHaar`. Establish `hδ : 0 < d / 2` using `by positivity`. Establish `hρ : 0 < R + d / 2` using `by positivity`. Establish `D : Set.Pairwise (s : Set ι) (Function.onFun Disjoint fun i => ball (f i) (d / 2))`.

Introduce `i hi j hj hij`. Apply `ball_disjoint_ball` to reduce the goal to its premises. Rewrite using `[dist_eq_norm, add_halves]`. Conclude with `h i hi j hj hij`. Establish `hsub : (⋃ i ∈ s, ball (f i) (d / 2)) ⊆ ball (0 : V) (R + d / 2)`.

Use `Set.iUnion₂_subset fun i hi => ball_subset_ball' ?_` and prove the remaining obligations. Rewrite using `[dist_zero_right]`. Combine the linear relations using `[hs i hi]`. Establish `I : (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ V) * μ (ball 0 1) ≤ ENNReal.ofReal ((R + d / 2) ^ finrank ℝ V) * μ (ball 0 1)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[measure_biUnion_finset D fun c _ => measurableSet_ball]`. Simplify using `only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]`. Use `_ ≤ μ (ball (0 : V) (R + d / 2)) := measure_mono hsub`. Use `_ = _ := by simp only [μ.addHaar_ball_of_pos _ hρ]`. Establish `J` using `(ENNReal.mul_le_mul_iff_left (measure_ball_pos μ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 I`.

Establish `K` using `ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) J`. Rewrite `K` using `[ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_natCast]`. Establish `e : 1 + 2 * R / d = (R + d / 2) / (d / 2)` using `by field_simp; ring`. Rewrite using `[e, div_pow, le_div_iff₀ (by positivity)]`. Conclude with `K`.
-/
theorem card_le_of_family_separated {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (s : Finset ι) (f : ι → V) {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R)
    (hs : ∀ i ∈ s, ‖f i‖ ≤ R) (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → d ≤ ‖f i - f j‖) :
    (s.card : ℝ) ≤ (1 + 2 * R / d) ^ finrank ℝ V := by
  borelize V
  let μ : Measure V := Measure.addHaar
  have hδ : 0 < d / 2 := by positivity
  have hρ : 0 < R + d / 2 := by positivity
  have D : Set.Pairwise (s : Set ι) (Function.onFun Disjoint fun i => ball (f i) (d / 2)) := by
    intro i hi j hj hij
    apply ball_disjoint_ball
    rw [dist_eq_norm, add_halves]
    exact h i hi j hj hij
  have hsub : (⋃ i ∈ s, ball (f i) (d / 2)) ⊆ ball (0 : V) (R + d / 2) := by
    refine Set.iUnion₂_subset fun i hi => ball_subset_ball' ?_
    rw [dist_zero_right]
    linarith [hs i hi]
  have I : (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ V) * μ (ball 0 1) ≤
      ENNReal.ofReal ((R + d / 2) ^ finrank ℝ V) * μ (ball 0 1) :=
    calc (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ V) * μ (ball 0 1)
        = μ (⋃ i ∈ s, ball (f i) (d / 2)) := by
          rw [measure_biUnion_finset D fun c _ => measurableSet_ball]
          simp only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : V) (R + d / 2)) := measure_mono hsub
      _ = _ := by simp only [μ.addHaar_ball_of_pos _ hρ]
  have J := (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ _ zero_lt_one).ne'
    measure_ball_lt_top.ne).1 I
  have K := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) J
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_natCast] at K
  have e : 1 + 2 * R / d = (R + d / 2) / (d / 2) := by field_simp; ring
  rw [e, div_pow, le_div_iff₀ (by positivity)]
  exact K

/- English proof (translation)
Establish `hf : S.Finite`. Assume the negation of the conclusion as `hinf`. Take `⟨s, hs, hc⟩` from `Set.Infinite.exists_subset_card_eq hinf (⌊B⌋₊ + 1)`. Establish `h1` using `h s hs`. Rewrite `h1` using `[hc]`.

Establish `h2` using `Nat.lt_floor_add_one B`. Move the coercions through the operations in `at h1`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨hf, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.ncard_eq_toFinset_card S hf]`.

Conclude with `h _ (by simp)`.
-/
theorem finite_and_ncard_le_of_forall_finset {α : Type*} (S : Set α) (B : ℝ)
    (h : ∀ s : Finset α, (s : Set α) ⊆ S → (s.card : ℝ) ≤ B) :
    S.Finite ∧ (S.ncard : ℝ) ≤ B := by
  have hf : S.Finite := by
    by_contra hinf
    obtain ⟨s, hs, hc⟩ := Set.Infinite.exists_subset_card_eq hinf (⌊B⌋₊ + 1)
    have h1 := h s hs
    rw [hc] at h1
    have h2 := Nat.lt_floor_add_one B
    push_cast at h1
    linarith
  refine ⟨hf, ?_⟩
  rw [Set.ncard_eq_toFinset_card S hf]
  exact h _ (by simp)

/- English proof (translation)
Establish `h1` using `Submodule.finrank_quotient_add_finrank (Submodule.span ℤ (Set.range v))`. Rewrite `h1` using `[finrank_span_eq_card hv, Fintype.card_fin, hn]`. Establish `h2 : finrank ℤ (A ⧸ Submodule.span ℤ (Set.range v)) = 0` using `by omega`. Take `⟨k, hk, hx⟩` from `(Module.finrank_eq_zero_iff.1 h2) (Submodule.Quotient.mk x)`. Conclude with `⟨k, hk, by rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx⟩`.
-/
theorem exists_zsmul_mem_span_of_linearIndependent {A : Type*} [AddCommGroup A]
    [Module.Finite ℤ A] {n : ℕ} (hn : finrank ℤ A = n) {v : Fin n → A}
    (hv : LinearIndependent ℤ v) (x : A) :
    ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ Submodule.span ℤ (Set.range v) := by
  have h1 := Submodule.finrank_quotient_add_finrank (Submodule.span ℤ (Set.range v))
  rw [finrank_span_eq_card hv, Fintype.card_fin, hn] at h1
  have h2 : finrank ℤ (A ⧸ Submodule.span ℤ (Set.range v)) = 0 := by omega
  obtain ⟨k, hk, hx⟩ := (Module.finrank_eq_zero_iff.1 h2) (Submodule.Quotient.mk x)
  exact ⟨k, hk, by rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx⟩

/- English proof (translation)
Use extensionality with `x`. Take `⟨k, hk, hx⟩` from `exists_zsmul_mem_span_of_linearIndependent hn hv x`. Establish `h1 : f (k • x) = g (k • x)` using `LinearMap.eqOn_span' (by rintro _ ⟨i, rfl⟩; exact h i) hx`. Rewrite `h1` using `[map_smul, map_smul]`. Conclude with `smul_right_injective B hk h1`.
-/
theorem linearMap_ext_of_linearIndependent {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module.Finite ℤ A] [Module.IsTorsionFree ℤ B] {n : ℕ} (hn : finrank ℤ A = n) {v : Fin n → A}
    (hv : LinearIndependent ℤ v) {f g : A →ₗ[ℤ] B} (h : ∀ i, f (v i) = g (v i)) : f = g := by
  ext x
  obtain ⟨k, hk, hx⟩ := exists_zsmul_mem_span_of_linearIndependent hn hv x
  have h1 : f (k • x) = g (k • x) :=
    LinearMap.eqOn_span' (by rintro _ ⟨i, rfl⟩; exact h i) hx
  rw [map_smul, map_smul] at h1
  exact smul_right_injective B hk h1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- English proof (translation)
Set `W : Submodule ℝ E` to `Submodule.span ℝ (Set.range fun i => (v i : E))`. Use `haveI : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)`. Establish `hW : finrank ℝ W ≤ n`. Conclude with `(finrank_range_le_card (R := ℝ) (fun i => (v i : E))).trans (Fintype.card_fin n).le`. Establish `hmem : ∀ x : L, (x : E) ∈ W`.

Introduce `x`. Take `⟨k, hk, hx⟩` from `exists_zsmul_mem_span_of_linearIndependent hn hv x`. Establish `h1 : Submodule.span ℤ (Set.range v) ≤ (W.restrictScalars ℤ).comap L.subtype`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Establish `h2 : (k : ℝ) • (x : E) ∈ W`. Rewrite using `[Int.cast_smul_eq_zsmul]`. Conclude with `h1 hx`. Conclude with `(W.smul_mem_iff (by exact_mod_cast hk)).1 h2`.

Use `finite_and_ncard_le_of_forall_finset _ _ fun s hs => ?_` and prove the remaining obligations. Use `(card_le_of_family_separated s (fun x : L => (⟨x, hmem x⟩ : W)) hd hR (fun i hi => hs hi) (fun i _ j _ hij => ?_)).trans ?_` and prove the remaining obligations. Conclude with `hL _ (L.sub_mem i.2 j.2) (sub_ne_zero.2 fun h => hij (Subtype.ext h))`. Conclude with `pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) hW`.
-/
theorem finite_and_ncard_setOf_norm_le_of_rank (L : Submodule ℤ E) [Module.Finite ℤ L] {n : ℕ}
    (hn : finrank ℤ L = n) {v : Fin n → L} (hv : LinearIndependent ℤ v) {d R : ℝ} (hd : 0 < d)
    (hR : 0 ≤ R) (hL : ∀ x ∈ L, x ≠ 0 → d ≤ ‖x‖) :
    {x : L | ‖(x : E)‖ ≤ R}.Finite ∧
      (({x : L | ‖(x : E)‖ ≤ R}.ncard : ℕ) : ℝ) ≤ (1 + 2 * R / d) ^ n := by
  let W : Submodule ℝ E := Submodule.span ℝ (Set.range fun i => (v i : E))
  haveI : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have hW : finrank ℝ W ≤ n := by
    exact (finrank_range_le_card (R := ℝ) (fun i => (v i : E))).trans (Fintype.card_fin n).le
  have hmem : ∀ x : L, (x : E) ∈ W := by
    intro x
    obtain ⟨k, hk, hx⟩ := exists_zsmul_mem_span_of_linearIndependent hn hv x
    have h1 : Submodule.span ℤ (Set.range v) ≤ (W.restrictScalars ℤ).comap L.subtype := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    have h2 : (k : ℝ) • (x : E) ∈ W := by
      rw [Int.cast_smul_eq_zsmul]
      exact h1 hx
    exact (W.smul_mem_iff (by exact_mod_cast hk)).1 h2
  refine finite_and_ncard_le_of_forall_finset _ _ fun s hs => ?_
  refine (card_le_of_family_separated s (fun x : L => (⟨x, hmem x⟩ : W)) hd hR
    (fun i hi => hs hi) (fun i _ j _ hij => ?_)).trans ?_
  · exact hL _ (L.sub_mem i.2 j.2) (sub_ne_zero.2 fun h => hij (Subtype.ext h))
  · exact pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) hW

/- English proof (translation)
Use `haveI : IsAddTorsionFree E := IsAddTorsionFree.of_isTorsionFree ℝ E`. Take `⟨hf, hc⟩` from `finite_and_ncard_setOf_norm_le_of_rank L hn hv hd hR hL`. Rewrite `hc` using `[Set.ncard_eq_toFinset_card _ hf]`. Use `finite_and_ncard_le_of_forall_finset _ _ fun s hs => ?_` and prove the remaining obligations. Establish `h1 : s.card ≤ (Fintype.piFinset fun _ : Fin n => hf.toFinset).card`.

Use `Finset.card_le_card_of_injOn (fun g i => φ g (v i)) (fun g hg => ?_) (fun g hg g' hg' h => hφ (hs hg) (hs hg') ?_)` and prove the remaining obligations. Simplify using `only [Finset.mem_coe, Fintype.mem_piFinset, Set.Finite.mem_toFinset]`. Conclude with `fun i => hG g (hs hg) i`. Conclude with `linearMap_ext_of_linearIndependent hn hv fun i => congrFun h i`. Rewrite `h1` using `[Fintype.card_piFinset_const]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem finite_and_ncard_le_of_norm_apply_le (L : Submodule ℤ E) [Module.Finite ℤ L] {n : ℕ}
    (hn : finrank ℤ L = n) {v : Fin n → L} (hv : LinearIndependent ℤ v) {d R : ℝ} (hd : 0 < d)
    (hR : 0 ≤ R) (hL : ∀ x ∈ L, x ≠ 0 → d ≤ ‖x‖) {Γ : Type*} (G : Set Γ)
    (φ : Γ → L →ₗ[ℤ] L) (hφ : Set.InjOn φ G) (hG : ∀ g ∈ G, ∀ i, ‖(φ g (v i) : E)‖ ≤ R) :
    G.Finite ∧ (G.ncard : ℝ) ≤ (1 + 2 * R / d) ^ (n ^ 2) := by
  classical
  haveI : IsAddTorsionFree E := IsAddTorsionFree.of_isTorsionFree ℝ E
  obtain ⟨hf, hc⟩ := finite_and_ncard_setOf_norm_le_of_rank L hn hv hd hR hL
  rw [Set.ncard_eq_toFinset_card _ hf] at hc
  refine finite_and_ncard_le_of_forall_finset _ _ fun s hs => ?_
  have h1 : s.card ≤ (Fintype.piFinset fun _ : Fin n => hf.toFinset).card := by
    refine Finset.card_le_card_of_injOn (fun g i => φ g (v i)) (fun g hg => ?_)
      (fun g hg g' hg' h => hφ (hs hg) (hs hg') ?_)
    · simp only [Finset.mem_coe, Fintype.mem_piFinset, Set.Finite.mem_toFinset]
      exact fun i => hG g (hs hg) i
    · exact linearMap_ext_of_linearIndependent hn hv fun i => congrFun h i
  rw [Fintype.card_piFinset_const] at h1
  calc (s.card : ℝ) ≤ (hf.toFinset.card : ℝ) ^ n := by exact_mod_cast h1
    _ ≤ ((1 + 2 * R / d) ^ n) ^ n := by gcongr
    _ = _ := by rw [← pow_mul, sq]

/- English proof (translation)
Establish `h` using `finite_and_ncard_le_of_norm_apply_le L hn hv h1 (R := c * max lamN 0) (by positivity) hL G φ hφ fun g hg i => (hG g hg _).trans (mul_le_mul_of_nonneg_left ((hvN i).trans (le_max_left _ _)) hc)`. Break down `Nat.eq_zero_or_pos n with rfl | hn0` into its components or cases. Simplify using `using h`. Rewrite `h` using `[max_eq_left ((norm_nonneg _).trans (hvN ⟨0, hn0⟩)), ← mul_assoc]`. Then use the resulting hypothesis.
-/
theorem finite_and_ncard_le_of_norm_map_le (L : Submodule ℤ E) [Module.Finite ℤ L] {n : ℕ}
    (hn : finrank ℤ L = n) {v : Fin n → L} (hv : LinearIndependent ℤ v) {lam1 lamN c : ℝ}
    (h1 : 0 < lam1) (hc : 0 ≤ c) (hL : ∀ x ∈ L, x ≠ 0 → lam1 ≤ ‖x‖)
    (hvN : ∀ i, ‖(v i : E)‖ ≤ lamN) {Γ : Type*} (G : Set Γ)
    (φ : Γ → L →ₗ[ℤ] L) (hφ : Set.InjOn φ G)
    (hG : ∀ g ∈ G, ∀ x : L, ‖(φ g x : E)‖ ≤ c * ‖(x : E)‖) :
    G.Finite ∧ (G.ncard : ℝ) ≤ (1 + 2 * c * lamN / lam1) ^ (n ^ 2) := by
  have h := finite_and_ncard_le_of_norm_apply_le L hn hv h1
    (R := c * max lamN 0) (by positivity) hL G φ hφ fun g hg i =>
      (hG g hg _).trans (mul_le_mul_of_nonneg_left ((hvN i).trans (le_max_left _ _)) hc)
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simpa using h
  · rwa [max_eq_left ((norm_nonneg _).trans (hvN ⟨0, hn0⟩)), ← mul_assoc] at h

/- English proof (translation)
The claim follows from `finite_and_ncard_le_of_norm_map_le L hn hv h1 hc hL hvN G LinearEquiv.toLinearMap LinearEquiv.toLinearMap_injective.injOn hG`.
-/
theorem finite_and_ncard_linearEquiv_le (L : Submodule ℤ E) [Module.Finite ℤ L] {n : ℕ}
    (hn : finrank ℤ L = n) {v : Fin n → L} (hv : LinearIndependent ℤ v) {lam1 lamN c : ℝ}
    (h1 : 0 < lam1) (hc : 0 ≤ c) (hL : ∀ x ∈ L, x ≠ 0 → lam1 ≤ ‖x‖)
    (hvN : ∀ i, ‖(v i : E)‖ ≤ lamN) (G : Set (L ≃ₗ[ℤ] L))
    (hG : ∀ g ∈ G, ∀ x : L, ‖(g x : E)‖ ≤ c * ‖(x : E)‖) :
    G.Finite ∧ (G.ncard : ℝ) ≤ (1 + 2 * c * lamN / lam1) ^ (n ^ 2) :=
  finite_and_ncard_le_of_norm_map_le L hn hv h1 hc hL hvN G LinearEquiv.toLinearMap
    LinearEquiv.toLinearMap_injective.injOn hG

/- English proof (translation)
The claim follows from `LinearIndependent.of_comp L.subtype (hv.restrict_scalars' ℤ)`.
-/
theorem linearIndependent_int_of_real (L : Submodule ℤ E) {ι : Type*} {v : ι → L}
    (hv : LinearIndependent ℝ fun i => (v i : E)) : LinearIndependent ℤ v :=
  LinearIndependent.of_comp L.subtype (hv.restrict_scalars' ℤ)

/- English proof (translation)
The claim follows from `finite_and_ncard_le_of_norm_map_le L ((ZLattice.rank ℝ L).trans hn) (linearIndependent_int_of_real L hv) h1 hc hL hvN G φ hφ hG`.
-/
theorem ZLattice_finite_and_ncard_le_of_norm_map_le [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] {n : ℕ} (hn : finrank ℝ E = n) {v : Fin n → L}
    (hv : LinearIndependent ℝ fun i => (v i : E)) {lam1 lamN c : ℝ}
    (h1 : 0 < lam1) (hc : 0 ≤ c) (hL : ∀ x ∈ L, x ≠ 0 → lam1 ≤ ‖x‖)
    (hvN : ∀ i, ‖(v i : E)‖ ≤ lamN) {Γ : Type*} (G : Set Γ)
    (φ : Γ → L →ₗ[ℤ] L) (hφ : Set.InjOn φ G)
    (hG : ∀ g ∈ G, ∀ x : L, ‖(φ g x : E)‖ ≤ c * ‖(x : E)‖) :
    G.Finite ∧ (G.ncard : ℝ) ≤ (1 + 2 * c * lamN / lam1) ^ (n ^ 2) :=
  finite_and_ncard_le_of_norm_map_le L ((ZLattice.rank ℝ L).trans hn)
    (linearIndependent_int_of_real L hv) h1 hc hL hvN G φ hφ hG

/- English proof (translation)
Set `ψ : G → L →ₗ[ℤ] L` to `fun g => ((φ g).restrictScalars ℤ).restrict (hφL g g.2)`. Establish `hψ : Set.InjOn ψ Set.univ`. Introduce `g _ g' _ h`. Use `Subtype.ext (hφ g.2 g'.2 ?_)` and prove the remaining obligations. Use `LinearMap.ext_on (IsZLattice.span_top (K := ℝ) (L := L)) fun x hx => ?_` and prove the remaining obligations.

Conclude with `congrArg Subtype.val (LinearMap.congr_fun h ⟨x, hx⟩)`. Take `⟨hf, hc⟩` from `ZLattice_finite_and_ncard_le_of_norm_map_le L hn (v := fun i => ⟨v i, hvL i⟩) hv h1 hc hL hvN Set.univ ψ hψ fun g _ x => hG g g.2 x x.2`. Rewrite `hc` using `[Set.ncard_univ, Nat.card_coe_set_eq]`. Conclude with `⟨Set.finite_coe_iff.1 (Set.finite_univ_iff.1 hf), hc⟩`.
-/
theorem ZLattice_finite_and_ncard_le_of_mapsTo [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] {n : ℕ} (hn : finrank ℝ E = n) {v : Fin n → E}
    (hvL : ∀ i, v i ∈ L) (hv : LinearIndependent ℝ v) {lam1 lamN c : ℝ}
    (h1 : 0 < lam1) (hc : 0 ≤ c) (hL : ∀ x ∈ L, x ≠ 0 → lam1 ≤ ‖x‖)
    (hvN : ∀ i, ‖v i‖ ≤ lamN) {Γ : Type*} (G : Set Γ)
    (φ : Γ → E →ₗ[ℝ] E) (hφ : Set.InjOn φ G) (hφL : ∀ g ∈ G, ∀ x ∈ L, φ g x ∈ L)
    (hG : ∀ g ∈ G, ∀ x ∈ L, ‖φ g x‖ ≤ c * ‖x‖) :
    G.Finite ∧ (G.ncard : ℝ) ≤ (1 + 2 * c * lamN / lam1) ^ (n ^ 2) := by
  let ψ : G → L →ₗ[ℤ] L := fun g => ((φ g).restrictScalars ℤ).restrict (hφL g g.2)
  have hψ : Set.InjOn ψ Set.univ := by
    intro g _ g' _ h
    refine Subtype.ext (hφ g.2 g'.2 ?_)
    refine LinearMap.ext_on (IsZLattice.span_top (K := ℝ) (L := L)) fun x hx => ?_
    exact congrArg Subtype.val (LinearMap.congr_fun h ⟨x, hx⟩)
  obtain ⟨hf, hc⟩ := ZLattice_finite_and_ncard_le_of_norm_map_le L hn
    (v := fun i => ⟨v i, hvL i⟩) hv h1 hc hL hvN Set.univ ψ hψ
    fun g _ x => hG g g.2 x x.2
  rw [Set.ncard_univ, Nat.card_coe_set_eq] at hc
  exact ⟨Set.finite_coe_iff.1 (Set.finite_univ_iff.1 hf), hc⟩

end DeterminedMaps

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun ρ _ hm => finite_and_ncard_setOf_index_pi_le ρ (by omega), fun _ _ _ _ L _ _ _ hn _ _ _ h1 hc hL _ hv hvN G hG => finite_and_ncard_linearEquiv_le L hn hv h1 (zero_le_one.trans hc) hL hvN G hG⟩`.
-/
theorem card_subgroups_le_and_card_automorphisms_le :
    (∀ ρ m : ℕ, 1 ≤ m → {H : AddSubgroup (Fin ρ → ℤ) | H.index = m}.Finite ∧
      {H : AddSubgroup (Fin ρ → ℤ) | H.index = m}.ncard ≤ m ^ ρ) ∧
    (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (n : ℕ), finrank ℤ L = n →
      ∀ (lam1 lamN c : ℝ), 0 < lam1 → 1 ≤ c → (∀ x ∈ L, x ≠ 0 → lam1 ≤ ‖x‖) →
      ∀ v : Fin n → L, LinearIndependent ℤ v → (∀ i, ‖(v i : E)‖ ≤ lamN) →
      ∀ G : Set (L ≃ₗ[ℤ] L), (∀ g ∈ G, ∀ x : L, ‖(g x : E)‖ ≤ c * ‖(x : E)‖) →
      G.Finite ∧ (G.ncard : ℝ) ≤ (1 + 2 * c * lamN / lam1) ^ (n ^ 2)) :=
  ⟨fun ρ _ hm => finite_and_ncard_setOf_index_pi_le ρ (by omega),
    fun _ _ _ _ L _ _ _ hn _ _ _ h1 hc hL _ hv hvN G hG =>
      finite_and_ncard_linearEquiv_le L hn hv h1 (zero_le_one.trans hc) hL hvN G hG⟩

end GlobalTheory
