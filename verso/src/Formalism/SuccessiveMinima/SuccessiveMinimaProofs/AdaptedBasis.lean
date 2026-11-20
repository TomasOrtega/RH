import Formalism.SuccessiveMinima.DefsMink

open Module Submodule

noncomputable section

namespace Formalism.FN.AdaptedBasisExistence

/- English proof (translation)
Use `haveI : ProperSpace E := FiniteDimensional.proper_real E`. Establish `hKL : span ℤ (Set.range B) ≤ L`. Rewrite using `[span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hB i`.

Establish `hdisc : IsDiscrete (L : Set E)` using `IsDiscrete.mk (inferInstance : DiscreteTopology L)`. Use `haveI : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)`. Establish `hclosed : IsClosed (L : Set E)` using `AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)`. Establish `hfin : (ZSpan.fundamentalDomain B ∩ (L : Set E)).Finite` using `Metric.finite_isBounded_inter_isClosed hdisc (ZSpan.fundamentalDomain_isBounded B) hclosed`. Take `⟨S, hS⟩ : ∃ S : Finset E, ∀ y, y ∈ S ↔ y ∈ ZSpan.fundamentalDomain B ∩ (L : Set E)` from `⟨hfin.toFinset, fun y => hfin.mem_toFinset⟩`.

Use `⟨S.card.factorial, Nat.factorial_pos _, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ k : ℕ, ZSpan.fract B (k • x) ∈ S`. Introduce `k`. Rewrite using `[hS]`. Use `⟨ZSpan.fract_mem_fundamentalDomain B _, ?_⟩` and prove the remaining obligations.

Rewrite using `[ZSpan.fract_apply]`. Conclude with `L.sub_mem (nsmul_mem hx k) (hKL (ZSpan.floor B (k • x)).2)`. Take `⟨a, b, hab, heq⟩` from `Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (S.card + 1) => (⟨ZSpan.fract B ((k : ℕ) • x), hmem k⟩ : S)) (by simp)`. Establish `heq' : ZSpan.fract B ((a : ℕ) • x) = ZSpan.fract B ((b : ℕ) • x)` using `congrArg Subtype.val heq`. Rewrite `heq'` using `[ZSpan.fract_eq_fract]`.

Establish `hab' : (a : ℕ) ≠ (b : ℕ)` using `fun h => hab (Fin.ext h)`. Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Establish `key : ∃ k : ℕ, 0 < k ∧ k ≤ S.card ∧ k • x ∈ span ℤ (Set.range B)`. Break down `lt_or_gt_of_ne hab' with h | h` into its components or cases.

Take `⟨c, hc⟩` from `Nat.exists_eq_add_of_lt h`. Use `⟨c + 1, Nat.succ_pos _, by omega, ?_⟩` and prove the remaining obligations. Establish `e : -((a : ℕ) • x) + (b : ℕ) • x = (c + 1) • x`. Rewrite using `[hc, add_assoc, add_nsmul]`. Normalize the expressions using the abelian group laws.

Rewrite using `[← e]`. Conclude with `heq'`. Take `⟨c, hc⟩` from `Nat.exists_eq_add_of_lt h`. Use `⟨c + 1, Nat.succ_pos _, by omega, ?_⟩` and prove the remaining obligations. Establish `e : -(-((a : ℕ) • x) + (b : ℕ) • x) = (c + 1) • x`.

Rewrite using `[hc, add_assoc, add_nsmul]`. Normalize the expressions using the abelian group laws. Rewrite using `[← e]`. Conclude with `neg_mem heq'`. Take `⟨k, hk0, hkS, hkx⟩` from `key`.

Take `⟨d, hd⟩` from `Nat.dvd_factorial hk0 hkS`. Rewrite using `[hd, mul_comm, ← smul_smul]`. Conclude with `nsmul_mem hkx d`.
-/
theorem exists_nsmul_mem_span {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {ι : Type} [Fintype ι]
    (B : Basis ι ℝ E) (hB : ∀ i, B i ∈ L) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, N • x ∈ span ℤ (Set.range B) := by
  classical
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  have hKL : span ℤ (Set.range B) ≤ L := by
    rw [span_le]
    rintro _ ⟨i, rfl⟩
    exact hB i
  have hdisc : IsDiscrete (L : Set E) := IsDiscrete.mk (inferInstance : DiscreteTopology L)
  haveI : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  have hclosed : IsClosed (L : Set E) := AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)
  have hfin : (ZSpan.fundamentalDomain B ∩ (L : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed hdisc (ZSpan.fundamentalDomain_isBounded B) hclosed
  obtain ⟨S, hS⟩ : ∃ S : Finset E, ∀ y, y ∈ S ↔ y ∈ ZSpan.fundamentalDomain B ∩ (L : Set E) :=
    ⟨hfin.toFinset, fun y => hfin.mem_toFinset⟩
  refine ⟨S.card.factorial, Nat.factorial_pos _, fun x hx => ?_⟩
  have hmem : ∀ k : ℕ, ZSpan.fract B (k • x) ∈ S := by
    intro k
    rw [hS]
    refine ⟨ZSpan.fract_mem_fundamentalDomain B _, ?_⟩
    rw [ZSpan.fract_apply]
    exact L.sub_mem (nsmul_mem hx k) (hKL (ZSpan.floor B (k • x)).2)
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (S.card + 1) => (⟨ZSpan.fract B ((k : ℕ) • x), hmem k⟩ : S)) (by simp)
  have heq' : ZSpan.fract B ((a : ℕ) • x) = ZSpan.fract B ((b : ℕ) • x) :=
    congrArg Subtype.val heq
  rw [ZSpan.fract_eq_fract] at heq'
  have hab' : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Fin.ext h)
  have ha := a.isLt
  have hb := b.isLt
  have key : ∃ k : ℕ, 0 < k ∧ k ≤ S.card ∧ k • x ∈ span ℤ (Set.range B) := by
    rcases lt_or_gt_of_ne hab' with h | h
    · obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_lt h
      refine ⟨c + 1, Nat.succ_pos _, by omega, ?_⟩
      have e : -((a : ℕ) • x) + (b : ℕ) • x = (c + 1) • x := by
        rw [hc, add_assoc, add_nsmul]
        abel
      rw [← e]
      exact heq'
    · obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_lt h
      refine ⟨c + 1, Nat.succ_pos _, by omega, ?_⟩
      have e : -(-((a : ℕ) • x) + (b : ℕ) • x) = (c + 1) • x := by
        rw [hc, add_assoc, add_nsmul]
        abel
      rw [← e]
      exact neg_mem heq'
  obtain ⟨k, hk0, hkS, hkx⟩ := key
  obtain ⟨d, hd⟩ := Nat.dvd_factorial hk0 hkS
  rw [hd, mul_comm, ← smul_smul]
  exact nsmul_mem hkx d

end Formalism.FN.AdaptedBasisExistence

namespace Formalism.FN.AdaptedBasisExistence

set_option maxHeartbeats 800000 in

/- English proof (translation)
Use `delta Formalism.FN.AdaptedBasis`. Introduce `E _ _ _ L _ _ v hv hvL`. Establish `hsp0 : ⊤ ≤ span ℝ (Set.range v)` using `(hv.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _)).ge`. Set `B : Basis (Fin (finrank ℝ E)) ℝ E` to `Basis.mk hv hsp0`. Establish `hBv : ∀ i, B i = v i` using `fun i => congrFun (Basis.coe_mk hv hsp0) i`.

Take `⟨N, hN, hNL⟩` from `exists_nsmul_mem_span L B (fun i => by rw [hBv]; exact hvL i)`. Establish `hN' : (N : ℝ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hint : ∀ x ∈ L, ∀ k, ∃ z : ℤ, (N : ℝ) * B.repr x k = z`. Introduce `x hx k`. Take `⟨z, hz⟩` from `(Basis.mem_span_iff_repr_mem ℤ B (N • x)).mp (hNL x hx) k`.

Establish `hz' : (z : ℝ) = (N : ℝ) * B.repr x k` using `by simpa using hz`. Conclude with `⟨z, hz'.symm⟩`. Establish `hP : ∀ j : Fin (finrank ℝ E), ∃ m : ℕ, 0 < m ∧ ∃ x, (x ∈ L ∧ ∀ k, j < k → B.repr x k = 0) ∧ (N : ℝ) * B.repr x j = m`. Introduce `j`. Use `⟨N, hN, v j, ⟨hvL j, fun k hk => ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hBv, B.repr_self, Finsupp.single_apply, if_neg (ne_of_lt hk)]`. Rewrite using `[← hBv, B.repr_self, Finsupp.single_apply, if_pos rfl, mul_one]`. Establish `hm` using `fun j => Nat.find_spec (hP j)`. Establish `hmin` using `fun j (r : ℕ) (hr : r < Nat.find (hP j)) => Nat.find_min (hP j) hr`. Use `choose b hbG hbj using fun j => (hm j).2`.

Establish `hdiv : ∀ j x, (x ∈ L ∧ ∀ k, j < k → B.repr x k = 0) → ∃ q : ℤ, B.repr x j = q * B.repr (b j) j`. Introduce `j x hx`. Take `⟨z, hz⟩` from `hint x hx.1 j`. Establish `hmpos : 0 < (Nat.find (hP j) : ℤ)` using `by exact_mod_cast (hm j).1`. Establish `hr0 : 0 ≤ z % (Nat.find (hP j) : ℤ)` using `Int.emod_nonneg _ hmpos.ne'`.

Establish `hrlt : z % (Nat.find (hP j) : ℤ) < Nat.find (hP j)` using `Int.emod_lt_of_pos _ hmpos`. Establish `hcast : ((z % (Nat.find (hP j) : ℤ) : ℤ) : ℝ) = (z : ℝ) - ((z / (Nat.find (hP j) : ℤ) : ℤ) : ℝ) * (Nat.find (hP j) : ℝ)`. Establish `h` using `congrArg (fun t : ℤ => (t : ℝ)) (Int.ediv_mul_add_emod z (Nat.find (hP j) : ℤ))`. Move the coercions through the operations in `at h`. Combine the linear equalities and inequalities to obtain the conclusion.

Distinguish the cases in `hr : z % (Nat.find (hP j) : ℤ) = 0`. Use `⟨z / (Nat.find (hP j) : ℤ), ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ hN'` to reduce the goal to its premises. Rewrite using `[hz, mul_left_comm, hbj]`. Rewrite `hcast` using `[hr]`.

Move the coercions through the operations in `at hcast`. Combine the linear equalities and inequalities to obtain the conclusion. It suffices to derive a contradiction. Establish `hrpos : 0 < z % (Nat.find (hP j) : ℤ)` using `lt_of_le_of_ne hr0 (Ne.symm hr)`. Establish `e : ∀ k, B.repr (x - (z / (Nat.find (hP j) : ℤ)) • b j) k = B.repr x k - ((z / (Nat.find (hP j) : ℤ) : ℤ) : ℝ) * B.repr (b j) k`.

Introduce `k`. Simplify using the standard rewrite rules. Use `hmin j (z % (Nat.find (hP j) : ℤ)).toNat (by omega) ⟨by omega, x - (z / (Nat.find (hP j) : ℤ)) • b j, ⟨L.sub_mem hx.1 (L.smul_mem _ (hbG j).1), fun k hk => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[e, hx.2 k hk, (hbG j).2 k hk, mul_zero, sub_zero]`. Rewrite using `[e, mul_sub, mul_left_comm, hbj, hz]`.

Establish `h2 : (((z % (Nat.find (hP j) : ℤ)).toNat : ℕ) : ℝ) = ((z % (Nat.find (hP j) : ℤ) : ℤ) : ℝ)`. Conclude with `Int.toNat_of_nonneg hr0` after adjusting the coercions. Rewrite using `[h2, hcast]`. Establish `hspan : ∀ r : ℕ, ∀ x ∈ L, (∀ k : Fin (finrank ℝ E), r ≤ k.val → B.repr x k = 0) → x ∈ span ℤ (b '' {k | k.val < r})`. Introduce `r`.

Proceed by induction on `r with`. Consider the case `zero`. Introduce `x _ h0`. Establish `hx0 : x = 0` using `B.repr.injective (by ext k; simp [h0 k (Nat.zero_le _)])`. Rewrite using `[hx0]`.

Conclude with `zero_mem _`. Consider the case `succ r ih`. Introduce `x hx h`. Distinguish the cases in `hr : r < finrank ℝ E`. Take `⟨q, hq⟩` from `hdiv ⟨r, hr⟩ x ⟨hx, fun k hk => h k (by rw [Fin.lt_def] at hk; exact hk)⟩`.

Establish `e : ∀ k, B.repr (x - q • b ⟨r, hr⟩) k = B.repr x k - (q : ℝ) * B.repr (b ⟨r, hr⟩) k`. Introduce `k`. Simplify using the standard rewrite rules. Establish `hy : x - q • b ⟨r, hr⟩ ∈ span ℤ (b '' {k | k.val < r})`. Use `ih _ (L.sub_mem hx (L.smul_mem q (hbG _).1)) fun k hk => ?_` and prove the remaining obligations.

Rewrite using `[e]`. Break down `Nat.lt_or_ge r k.val with hk' | hk'` into its components or cases. Rewrite using `[h k hk', (hbG _).2 k (by rw [Fin.lt_def]; exact hk'), mul_zero, sub_zero]`. Establish `hkr : k = ⟨r, hr⟩` using `Fin.ext (show k.val = r by omega)`. Rewrite using `[hkr, hq, sub_self]`.

Establish `hb_mem : b ⟨r, hr⟩ ∈ span ℤ (b '' {k | k.val < r + 1})` using `subset_span ⟨⟨r, hr⟩, by simp, rfl⟩`. Establish `hmono : span ℤ (b '' {k | k.val < r}) ≤ span ℤ (b '' {k | k.val < r + 1})` using `span_mono (Set.image_mono fun k (hk : k.val < r) => show k.val < r + 1 by omega)`. Establish `hsum` using `add_mem (hmono hy) (smul_mem _ q hb_mem)`. Rewrite `hsum` using `[sub_add_cancel]`. Then use the resulting hypothesis. Establish `hmono : span ℤ (b '' {k | k.val < r}) ≤ span ℤ (b '' {k | k.val < r + 1})` using `span_mono (Set.image_mono fun k (hk : k.val < r) => show k.val < r + 1 by omega)`.

Conclude with `hmono (ih x hx fun k hk => absurd k.isLt (by omega))`. Establish `hbL : ∀ j, b j ∈ L` using `fun j => (hbG j).1`. Establish `hall : ∀ x ∈ L, x ∈ span ℤ (Set.range b)` using `fun x hx => span_mono (Set.image_subset_range _ _) (hspan (finrank ℝ E) x hx fun k hk => absurd k.isLt (by omega))`. Set `b' : Fin (finrank ℝ E) → L` to `fun j => ⟨b j, hbL j⟩`. Establish `hsp : ⊤ ≤ span ℤ (Set.range b')`.

Introduce and unpack `x -`. Establish `h2` using `hall x x.2`. Establish `h3 : Set.range b = L.subtype '' Set.range b'`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression.

Rewrite `h2` using `[h3, ← Submodule.map_span, Submodule.mem_map]`. Take `⟨y, hy, hyx⟩` from `h2`. Rewrite using `[← Subtype.ext hyx]` and apply the resulting hypothesis. Establish `hliR : LinearIndependent ℝ b`. Use `linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (Fintype.card_fin _)` and prove the remaining obligations.

Use `le_trans hsp0 (span_le.mpr ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `span_le_restrictScalars ℤ ℝ _ (hall _ (hvL i))`. Establish `hliZ : LinearIndependent ℤ b'` using `LinearIndependent.of_comp L.subtype (hliR.restrict_scalars' ℤ)`. Use `⟨Basis.mk hliZ hsp, fun j => ?_⟩` and prove the remaining obligations.

Simplify using `only [Basis.coe_mk]`. Express the relevant statement in the definitionally equal form `span ℝ (b '' {k | k ≤ j}) = span ℝ (v '' {k | k ≤ j})`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[span_le]`. Introduce and unpack `_ ⟨k, hk, rfl⟩`.

Rewrite `hk` using `[Set.mem_setOf_eq]`. Establish `hvB : v '' {k | k ≤ j} = B '' {k | k ≤ j}` using `Set.image_congr fun i _ => (hBv i).symm`. Rewrite using `[SetLike.mem_coe, hvB, B.mem_span_image]`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_coe, Finsupp.mem_support_iff]`.

Assume the negation of the conclusion as `hij`. Rewrite `hij` using `[Set.mem_setOf_eq, not_le]`. Conclude with `hi ((hbG k).2 i (lt_of_le_of_lt hk hij))`. Rewrite using `[span_le]`. Introduce and unpack `_ ⟨i, hi, rfl⟩`.

Rewrite `hi` using `[Set.mem_setOf_eq]`. Establish `hvi` using `hspan (j.val + 1) (v i) (hvL i) fun k hk => by`. Rewrite using `[← hBv, B.repr_self, Finsupp.single_apply, if_neg]`. Introduce `hik`. Rewrite `hi` using `[hik, Fin.le_def]`.

Use linear arithmetic over natural numbers and integers. Establish `hsub : {k : Fin (finrank ℝ E) | k.val < j.val + 1} ⊆ {k | k ≤ j}`. Introduce `k hk`. Simplify using `only [Set.mem_setOf_eq] at hk ⊢`. Rewrite using `[Fin.le_def]`.

Use linear arithmetic over natural numbers and integers. Conclude with `span_le_restrictScalars ℤ ℝ _ (span_mono (Set.image_mono hsub) hvi)`.
-/
theorem adapted_basis_exists : AdaptedBasis := by
  delta Formalism.FN.AdaptedBasis
  intro E _ _ _ L _ _ v hv hvL
  classical
  have hsp0 : ⊤ ≤ span ℝ (Set.range v) :=
    (hv.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _)).ge
  let B : Basis (Fin (finrank ℝ E)) ℝ E := Basis.mk hv hsp0
  have hBv : ∀ i, B i = v i := fun i => congrFun (Basis.coe_mk hv hsp0) i
  obtain ⟨N, hN, hNL⟩ := exists_nsmul_mem_span L B (fun i => by rw [hBv]; exact hvL i)
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hint : ∀ x ∈ L, ∀ k, ∃ z : ℤ, (N : ℝ) * B.repr x k = z := by
    intro x hx k
    obtain ⟨z, hz⟩ := (Basis.mem_span_iff_repr_mem ℤ B (N • x)).mp (hNL x hx) k
    have hz' : (z : ℝ) = (N : ℝ) * B.repr x k := by simpa using hz
    exact ⟨z, hz'.symm⟩
  have hP : ∀ j : Fin (finrank ℝ E), ∃ m : ℕ, 0 < m ∧ ∃ x, (x ∈ L ∧ ∀ k, j < k → B.repr x k = 0) ∧
      (N : ℝ) * B.repr x j = m := by
    intro j
    refine ⟨N, hN, v j, ⟨hvL j, fun k hk => ?_⟩, ?_⟩
    · rw [← hBv, B.repr_self, Finsupp.single_apply, if_neg (ne_of_lt hk)]
    · rw [← hBv, B.repr_self, Finsupp.single_apply, if_pos rfl, mul_one]
  have hm := fun j => Nat.find_spec (hP j)
  have hmin := fun j (r : ℕ) (hr : r < Nat.find (hP j)) => Nat.find_min (hP j) hr
  choose b hbG hbj using fun j => (hm j).2
  have hdiv : ∀ j x, (x ∈ L ∧ ∀ k, j < k → B.repr x k = 0) →
      ∃ q : ℤ, B.repr x j = q * B.repr (b j) j := by
    intro j x hx
    obtain ⟨z, hz⟩ := hint x hx.1 j
    have hmpos : 0 < (Nat.find (hP j) : ℤ) := by exact_mod_cast (hm j).1
    have hr0 : 0 ≤ z % (Nat.find (hP j) : ℤ) := Int.emod_nonneg _ hmpos.ne'
    have hrlt : z % (Nat.find (hP j) : ℤ) < Nat.find (hP j) := Int.emod_lt_of_pos _ hmpos
    have hcast : ((z % (Nat.find (hP j) : ℤ) : ℤ) : ℝ) =
        (z : ℝ) - ((z / (Nat.find (hP j) : ℤ) : ℤ) : ℝ) * (Nat.find (hP j) : ℝ) := by
      have h := congrArg (fun t : ℤ => (t : ℝ)) (Int.ediv_mul_add_emod z (Nat.find (hP j) : ℤ))
      push_cast at h
      linarith
    by_cases hr : z % (Nat.find (hP j) : ℤ) = 0
    · refine ⟨z / (Nat.find (hP j) : ℤ), ?_⟩
      apply mul_left_cancel₀ hN'
      rw [hz, mul_left_comm, hbj]
      rw [hr] at hcast
      push_cast at hcast
      linarith
    · exfalso
      have hrpos : 0 < z % (Nat.find (hP j) : ℤ) := lt_of_le_of_ne hr0 (Ne.symm hr)
      have e : ∀ k, B.repr (x - (z / (Nat.find (hP j) : ℤ)) • b j) k =
          B.repr x k - ((z / (Nat.find (hP j) : ℤ) : ℤ) : ℝ) * B.repr (b j) k := by
        intro k
        simp
      refine hmin j (z % (Nat.find (hP j) : ℤ)).toNat (by omega)
        ⟨by omega, x - (z / (Nat.find (hP j) : ℤ)) • b j,
          ⟨L.sub_mem hx.1 (L.smul_mem _ (hbG j).1), fun k hk => ?_⟩, ?_⟩
      · rw [e, hx.2 k hk, (hbG j).2 k hk, mul_zero, sub_zero]
      · rw [e, mul_sub, mul_left_comm, hbj, hz]
        have h2 : (((z % (Nat.find (hP j) : ℤ)).toNat : ℕ) : ℝ) =
            ((z % (Nat.find (hP j) : ℤ) : ℤ) : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hr0
        rw [h2, hcast]
  have hspan : ∀ r : ℕ, ∀ x ∈ L, (∀ k : Fin (finrank ℝ E), r ≤ k.val → B.repr x k = 0) →
      x ∈ span ℤ (b '' {k | k.val < r}) := by
    intro r
    induction r with
    | zero =>
      intro x _ h0
      have hx0 : x = 0 := B.repr.injective (by ext k; simp [h0 k (Nat.zero_le _)])
      rw [hx0]
      exact zero_mem _
    | succ r ih =>
      intro x hx h
      by_cases hr : r < finrank ℝ E
      · obtain ⟨q, hq⟩ := hdiv ⟨r, hr⟩ x ⟨hx, fun k hk => h k (by rw [Fin.lt_def] at hk; exact hk)⟩
        have e : ∀ k, B.repr (x - q • b ⟨r, hr⟩) k = B.repr x k - (q : ℝ) * B.repr (b ⟨r, hr⟩) k := by
          intro k
          simp
        have hy : x - q • b ⟨r, hr⟩ ∈ span ℤ (b '' {k | k.val < r}) := by
          refine ih _ (L.sub_mem hx (L.smul_mem q (hbG _).1)) fun k hk => ?_
          rw [e]
          rcases Nat.lt_or_ge r k.val with hk' | hk'
          · rw [h k hk', (hbG _).2 k (by rw [Fin.lt_def]; exact hk'), mul_zero, sub_zero]
          · have hkr : k = ⟨r, hr⟩ := Fin.ext (show k.val = r by omega)
            rw [hkr, hq, sub_self]
        have hb_mem : b ⟨r, hr⟩ ∈ span ℤ (b '' {k | k.val < r + 1}) :=
          subset_span ⟨⟨r, hr⟩, by simp, rfl⟩
        have hmono : span ℤ (b '' {k | k.val < r}) ≤ span ℤ (b '' {k | k.val < r + 1}) :=
          span_mono (Set.image_mono fun k (hk : k.val < r) => show k.val < r + 1 by omega)
        have hsum := add_mem (hmono hy) (smul_mem _ q hb_mem)
        rwa [sub_add_cancel] at hsum
      · have hmono : span ℤ (b '' {k | k.val < r}) ≤ span ℤ (b '' {k | k.val < r + 1}) :=
          span_mono (Set.image_mono fun k (hk : k.val < r) => show k.val < r + 1 by omega)
        exact hmono (ih x hx fun k hk => absurd k.isLt (by omega))
  have hbL : ∀ j, b j ∈ L := fun j => (hbG j).1
  have hall : ∀ x ∈ L, x ∈ span ℤ (Set.range b) := fun x hx =>
    span_mono (Set.image_subset_range _ _)
      (hspan (finrank ℝ E) x hx fun k hk => absurd k.isLt (by omega))
  let b' : Fin (finrank ℝ E) → L := fun j => ⟨b j, hbL j⟩
  have hsp : ⊤ ≤ span ℤ (Set.range b') := by
    rintro x -
    have h2 := hall x x.2
    have h3 : Set.range b = L.subtype '' Set.range b' := by
      rw [← Set.range_comp]
      rfl
    rw [h3, ← Submodule.map_span, Submodule.mem_map] at h2
    obtain ⟨y, hy, hyx⟩ := h2
    rwa [← Subtype.ext hyx]
  have hliR : LinearIndependent ℝ b := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (Fintype.card_fin _)
    refine le_trans hsp0 (span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩
    exact span_le_restrictScalars ℤ ℝ _ (hall _ (hvL i))
  have hliZ : LinearIndependent ℤ b' :=
    LinearIndependent.of_comp L.subtype (hliR.restrict_scalars' ℤ)
  refine ⟨Basis.mk hliZ hsp, fun j => ?_⟩
  simp only [Basis.coe_mk]
  change span ℝ (b '' {k | k ≤ j}) = span ℝ (v '' {k | k ≤ j})
  apply le_antisymm
  · rw [span_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [Set.mem_setOf_eq] at hk
    have hvB : v '' {k | k ≤ j} = B '' {k | k ≤ j} := Set.image_congr fun i _ => (hBv i).symm
    rw [SetLike.mem_coe, hvB, B.mem_span_image]
    intro i hi
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hi
    by_contra hij
    rw [Set.mem_setOf_eq, not_le] at hij
    exact hi ((hbG k).2 i (lt_of_le_of_lt hk hij))
  · rw [span_le]
    rintro _ ⟨i, hi, rfl⟩
    rw [Set.mem_setOf_eq] at hi
    have hvi := hspan (j.val + 1) (v i) (hvL i) fun k hk => by
      rw [← hBv, B.repr_self, Finsupp.single_apply, if_neg]
      intro hik
      rw [hik, Fin.le_def] at hi
      omega
    have hsub : {k : Fin (finrank ℝ E) | k.val < j.val + 1} ⊆ {k | k ≤ j} := by
      intro k hk
      simp only [Set.mem_setOf_eq] at hk ⊢
      rw [Fin.le_def]
      omega
    exact span_le_restrictScalars ℤ ℝ _ (span_mono (Set.image_mono hsub) hvi)

end Formalism.FN.AdaptedBasisExistence

/- English proof (translation)
The claim follows from `Formalism.FN.AdaptedBasisExistence.adapted_basis_exists`.
-/
theorem Formalism.FN.existsAdaptedBasis : Formalism.FN.AdaptedBasis := Formalism.FN.AdaptedBasisExistence.adapted_basis_exists
