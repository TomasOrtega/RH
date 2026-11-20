import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.InvariantSubmoduleEqSpanEigenbasisOfSeparable
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.CardDvdOfPartitionEqualSize

open IsLocalRing Polynomial Matrix UpperTheory.V

/- English proof (translation)
Introduce `K G _ _ _ n r hirr N hN hu hnot`. Take `⟨u, huN, hsep⟩` from `hu`. Establish `hconj : ∀ g h : G, h ∈ N → g⁻¹ * h * g ∈ N`. Introduce `g h hh`. Establish `hc : h⁻¹ * g⁻¹ * h⁻¹⁻¹ * g⁻¹⁻¹ ∈ N` using `hN (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))`.

Establish `e : g⁻¹ * h * g = h * (h⁻¹ * g⁻¹ * h⁻¹⁻¹ * g⁻¹⁻¹)` using `by group`. Rewrite using `[e]`. Conclude with `N.mul_mem hh hc`. Establish `hr1 : ∀ g : G, r g * r g⁻¹ = 1`. Introduce `g`.

Rewrite using `[← map_mul, mul_inv_cancel, map_one]`. Establish `hr2 : ∀ g : G, r g⁻¹ * r g = 1`. Introduce `g`. Rewrite using `[← map_mul, inv_mul_cancel, map_one]`. Set `Inv : Submodule K (Fin n → K) → Prop` to `fun X => ∀ g ∈ N, ∀ v ∈ X, r g *ᵥ v ∈ X`.

Set `tr : G → Submodule K (Fin n → K) → Submodule K (Fin n → K)` to `fun g X => X.map (Matrix.toLin' (r g))`. Establish `mem_tr : ∀ g X v, v ∈ tr g X ↔ r g⁻¹ *ᵥ v ∈ X`. Introduce `g X v`. Prove the components needed by the constructor for the conclusion. Introduce `hv`.

Take `⟨x, hx, rfl⟩` from `Submodule.mem_map.1 hv`. Simplify using `only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec]`. Conclude with `hx`. Introduce `hv`. Use `Submodule.mem_map.2 ⟨_, hv, ?_⟩` and prove the remaining obligations.

Simplify using `only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hr1, Matrix.one_mulVec]`. Establish `tr_inv : ∀ g X, Inv X → Inv (tr g X)`. Introduce `g X hX h hh v hv`. Rewrite `hv`, the goal using `[mem_tr]`. Establish `e : r g⁻¹ *ᵥ (r h *ᵥ v) = r (g⁻¹ * h * g) *ᵥ (r g⁻¹ *ᵥ v)`.

Simplify using `only [Matrix.mulVec_mulVec, map_mul, mul_assoc, hr1, mul_one]`. Rewrite using `[e]`. Conclude with `hX _ (hconj g h hh) _ hv`. Establish `htr_mul : ∀ g h X, tr (g * h) X = tr g (tr h X)`. Introduce `g h X`.

Use extensionality with `v`. Rewrite using `[mem_tr, mem_tr, mem_tr, _root_.mul_inv_rev, map_mul, ← Matrix.mulVec_mulVec]`. Establish `htr_one : ∀ X, tr 1 X = X`. Introduce `X`. Use extensionality with `v`.

Rewrite using `[mem_tr, inv_one, map_one, Matrix.one_mulVec]`. Take `⟨b, hb⟩` from `Ws.invariant_submodule_eq_span_eigenbasis_of_separable K n (r u) hsep`. Establish `hspan : ∀ X, Inv X → X = Submodule.span K (b '' {i | b i ∈ X})` using `fun X hX => hb X (hX u huN)`. Establish `hrank : ∀ X, Inv X → Module.finrank K X = {i | b i ∈ X}.ncard`. Introduce `X hX`.

Establish `e` using `hspan X hX`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← e]`. Use `_ = {i | b i ∈ X}.ncard := by`. Establish `hli` using `b.linearIndependent.comp (Subtype.val : {i // i ∈ {i | b i ∈ X}} → Fin n) Subtype.val_injective`.

Rewrite using `[Set.image_eq_range]`. Rewrite using `[finrank_span_eq_card (R := K) (b := fun x : {i // i ∈ {i | b i ∈ X}} => b x) hli, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]`. Choose the witnesses or unpack the hypotheses as in `⟨W0, hW0i, hW0b, hW0t⟩ : ∃ W, Inv W ∧ W ≠ ⊥ ∧ W ≠ ⊤ := by`. Unfold `U3.MatIrr at hnot`. Use `push_neg at hnot`.

Conclude with `hnot`. Establish `hex : ∃ k, ∃ X, Inv X ∧ X ≠ ⊥ ∧ Module.finrank K X = k` using `⟨_, W0, hW0i, hW0b, rfl⟩`. Take `⟨W, hWi, hWb, hWk⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ X, Inv X → X ≠ ⊥ → Module.finrank K W ≤ Module.finrank K X`. Introduce `X hX hXb`.

Rewrite using `[hWk]`. Conclude with `Nat.find_min' hex ⟨X, hX, hXb, rfl⟩`. Establish `hWt : W ≠ ⊤`. Introduce `h`. Establish `h1` using `hmin W0 hW0i hW0b`.

Establish `h2` using `Submodule.finrank_lt hW0t`. Rewrite `h1` using `[h, finrank_top]`. Use linear arithmetic over natural numbers and integers. Establish `tr_ne : ∀ g X, X ≠ ⊥ → tr g X ≠ ⊥`. Introduce `g X hX h`.

Apply `hX` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `v hv`. Establish `hm : r g *ᵥ v ∈ tr g X`. Rewrite using `[mem_tr, Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec]`.

Conclude with `hv`. Rewrite `hm` using `[h, Submodule.mem_bot]`. Establish `e` using `congrArg (fun w => r g⁻¹ *ᵥ w) hm`. Simplify using `only [Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec, Matrix.mulVec_zero] at e`. Rewrite using `[e]`.

Conclude with `Submodule.zero_mem _`. Establish `trW_rank : ∀ g, Module.finrank K (tr g W) = Module.finrank K W` using `fun g => le_antisymm (Submodule.finrank_map_le _ _) (hmin _ (tr_inv g W hWi) (tr_ne g W hWb))`. Establish `key : ∀ g, (∀ v ∈ W, r g *ᵥ v ∈ W) → tr g W = W`. Introduce `g hg`. Apply `Submodule.eq_of_le_of_finrank_le` to reduce the goal to its premises.

Introduce `v hv`. Rewrite `hv` using `[mem_tr]`. Establish `e : v = r g *ᵥ (r g⁻¹ *ᵥ v)`. Rewrite using `[Matrix.mulVec_mulVec, hr1, Matrix.one_mulVec]`. Rewrite using `[e]`.

Conclude with `hg _ hv`. Rewrite using `[trW_rank]`. Set `S : Subgroup G` to `{ carrier := {g | tr g W = W} mul_mem' := by`. Introduce `a c ha hc`. Simplify using `only [Set.mem_setOf_eq] at ha hc ⊢`.

Rewrite using `[htr_mul, hc, ha]`. Use the proof step `one_mem' := htr_one W`. Use the proof step `inv_mem' := by`. Introduce `a ha`. Simplify using `only [Set.mem_setOf_eq] at ha ⊢`.

Use `conv_lhs => rw [← ha]`. Rewrite using `[← htr_mul, inv_mul_cancel, htr_one] }`. Establish `hS : ∀ g, g ∈ S ↔ ∀ v ∈ W, r g *ᵥ v ∈ W`. Introduce `g`. Prove the components needed by the constructor for the conclusion.

Introduce `hg v hv`. Establish `hm : r g *ᵥ v ∈ tr g W`. Rewrite using `[mem_tr, Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec]`. Conclude with `hv`. Establish `hg' : tr g W = W` using `hg`.

Rewrite `hm` using `[hg']`. Conclude with `hm`. Conclude with `key g`. Use `⟨W, S, hWb, hWt, fun g hg => (hS g).2 (hWi g hg), hS, ?_⟩` and prove the remaining obligations. Establish `huniq : ∀ g1 g2 i, b i ∈ tr g1 W → b i ∈ tr g2 W → tr g1 W = tr g2 W`.

Introduce `g1 g2 i h1 h2`. Establish `hI : Inv (tr g1 W ⊓ tr g2 W)` using `fun h hh v hv => ⟨tr_inv g1 W hWi h hh v hv.1, tr_inv g2 W hWi h hh v hv.2⟩`. Establish `hne : tr g1 W ⊓ tr g2 W ≠ ⊥`. Introduce `h`. Establish `hm : b i ∈ tr g1 W ⊓ tr g2 W` using `⟨h1, h2⟩`.

Rewrite `hm` using `[h, Submodule.mem_bot]`. Conclude with `b.ne_zero i hm`. Establish `hm` using `hmin _ hI hne`. Establish `e1 : tr g1 W ⊓ tr g2 W = tr g1 W` using `Submodule.eq_of_le_of_finrank_le inf_le_left (by rw [trW_rank]; exact hm)`. Establish `e2 : tr g1 W ⊓ tr g2 W = tr g2 W` using `Submodule.eq_of_le_of_finrank_le inf_le_right (by rw [trW_rank]; exact hm)`.

Conclude with `e1.symm.trans e2`. Establish `hcover : ∀ i, ∃ g, b i ∈ tr g W`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Take `⟨i, hi⟩` from `hc`.

Establish `hUi : ∀ g ∈ (⊤ : Subgroup G), ∀ v ∈ ⨆ h, tr h W, r g *ᵥ v ∈ ⨆ h, tr h W`. Introduce `g _ v hv`. Use `Submodule.iSup_induction (fun h => tr h W) (motive := fun v => r g *ᵥ v ∈ ⨆ h, tr h W) hv ?_ ?_ ?_` and prove the remaining obligations. Introduce `h x hx`. Use `Submodule.mem_iSup_of_mem (g * h) ?_` and prove the remaining obligations.

Rewrite using `[htr_mul, mem_tr, Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec]`. Conclude with `hx`. Use `show r g *ᵥ 0 ∈ ⨆ h, tr h W`. Rewrite using `[Matrix.mulVec_zero]`. Conclude with `Submodule.zero_mem _`.

Introduce `x y hx hy show r g *ᵥ (x + y) ∈ ⨆ h, tr h W`. Rewrite using `[Matrix.mulVec_add]`. Conclude with `add_mem hx hy`. Establish `hU` using `hirr _ hUi`. Establish `hUb : (⨆ h, tr h W) ≠ ⊥`.

Introduce `h`. Apply `hWb` to reduce the goal to its premises. Rewrite using `[eq_bot_iff, ← h]`. Use `le_iSup (fun h => tr h W) 1` as an intermediate fact. Rewrite `this` using `[htr_one]`.

Conclude with `this`. Establish `hUt` using `hU.resolve_left hUb`. Establish `hbi : b i ∈ ⨆ h, tr h W`. Rewrite using `[hUt]`. Conclude with `Submodule.mem_top`.

Establish `hz : ∀ v ∈ ⨆ h, tr h W, b.repr v i = 0`. Introduce `v hv`. Use `Submodule.iSup_induction (fun h => tr h W) (motive := fun v => b.repr v i = 0) hv ?_ ?_ ?_` and prove the remaining obligations. Introduce `g x hx`. Establish `hx' : x ∈ tr g W` using `hx`.

Rewrite `hx'` using `[hspan _ (tr_inv g W hWi), Module.Basis.mem_span_image]`. Assume the negation of the conclusion as `h0`. Conclude with `hi g (hx' (Finsupp.mem_support_iff.2 h0))`. Simplify using the standard rewrite rules. Introduce `x y hx hy`.

Simplify using `only [map_add, Finsupp.add_apply]`. Rewrite using `[hx, hy, add_zero]`. Use `hz _ hbi` as an intermediate fact. Simplify using `at this`. Set `T : G ⧸ S → Set (Fin n)` to `fun q => {i | b i ∈ tr q.out W}`.

Establish `hT1 : ∀ q, (T q).ncard = Module.finrank K W`. Introduce `q`. Rewrite using `[← trW_rank q.out, hrank _ (tr_inv _ W hWi)]`. Establish `hT2 : ∀ i, ∃! q, i ∈ T q`. Introduce `i`.

Take `⟨g, hg⟩` from `hcover i`. Use `⟨(g : G ⧸ S), ?_, ?_⟩` and prove the remaining obligations. Use `show b i ∈ tr (g : G ⧸ S).out W`. Take `⟨a, ha⟩ : ∃ a, a = (g : G ⧸ S).out` from `⟨_, rfl⟩`. Rewrite using `[← ha]`.

Establish `hm : a⁻¹ * g ∈ S`. Rewrite using `[ha]`. Conclude with `QuotientGroup.eq.mp (QuotientGroup.out_eq' (g : G ⧸ S))`. Establish `hm' : tr (a⁻¹ * g) W = W` using `hm`. Establish `e : tr (a * (a⁻¹ * g)) W = tr a W`.

Rewrite using `[htr_mul, hm']`. Rewrite `e` using `[mul_inv_cancel_left]`. Rewrite using `[← e]`. Conclude with `hg`. Introduce `q hq`.

Establish `e` using `huniq _ _ i hq hg`. Establish `hm : q.out⁻¹ * g ∈ S` using `by show tr _ W = W`. Rewrite using `[htr_mul, ← e, ← htr_mul, inv_mul_cancel, htr_one]`. Conclude with `(QuotientGroup.out_eq' q).symm.trans (QuotientGroup.eq.mpr hm)`. Establish `hc` using `Ws.card_dvd_of_partition_equal_size (Fin n) (G ⧸ S) T (Module.finrank K W) hT1 hT2`.

Establish `hn : Nat.card (Fin n) = n` using `Nat.card_eq_fintype_card.trans (Fintype.card_fin n)`. Rewrite `hc` using `[hn]`. Conclude with `hc`.
-/
theorem UpperTheory.V.Ws.exists_stabilizer_index_dvd_of_not_irreducible_restriction :
    ∀ (K G : Type) [Field K] [IsAlgClosed K] [Group G] (n : ℕ) (r : G →* Matrix (Fin n) (Fin n) K), U3.MatIrr ⊤ r →
      ∀ N : Subgroup G, commutator G ≤ N → (∃ u ∈ N, (r u).charpoly.Separable) → ¬ U3.MatIrr N r →
      ∃ (W : Submodule K (Fin n → K)) (S : Subgroup G), W ≠ ⊥ ∧ W ≠ ⊤ ∧ N ≤ S ∧ (∀ g, g ∈ S ↔ ∀ v ∈ W, r g *ᵥ v ∈ W) ∧
        S.index ∣ n := by
  intro K G _ _ _ n r hirr N hN hu hnot
  classical
  obtain ⟨u, huN, hsep⟩ := hu
  have hconj : ∀ g h : G, h ∈ N → g⁻¹ * h * g ∈ N := by
    intro g h hh
    have hc : h⁻¹ * g⁻¹ * h⁻¹⁻¹ * g⁻¹⁻¹ ∈ N :=
      hN (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have e : g⁻¹ * h * g = h * (h⁻¹ * g⁻¹ * h⁻¹⁻¹ * g⁻¹⁻¹) := by
      group
    rw [e]
    exact N.mul_mem hh hc
  have hr1 : ∀ g : G, r g * r g⁻¹ = 1 := by
    intro g
    rw [← map_mul, mul_inv_cancel, map_one]
  have hr2 : ∀ g : G, r g⁻¹ * r g = 1 := by
    intro g
    rw [← map_mul, inv_mul_cancel, map_one]
  let Inv : Submodule K (Fin n → K) → Prop := fun X => ∀ g ∈ N, ∀ v ∈ X, r g *ᵥ v ∈ X
  let tr : G → Submodule K (Fin n → K) → Submodule K (Fin n → K) :=
    fun g X => X.map (Matrix.toLin' (r g))
  have mem_tr : ∀ g X v, v ∈ tr g X ↔ r g⁻¹ *ᵥ v ∈ X := by
    intro g X v
    constructor
    · intro hv
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hv
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec]
      exact hx
    · intro hv
      refine Submodule.mem_map.2 ⟨_, hv, ?_⟩
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hr1, Matrix.one_mulVec]
  have tr_inv : ∀ g X, Inv X → Inv (tr g X) := by
    intro g X hX h hh v hv
    rw [mem_tr] at hv ⊢
    have e : r g⁻¹ *ᵥ (r h *ᵥ v) = r (g⁻¹ * h * g) *ᵥ (r g⁻¹ *ᵥ v) := by
      simp only [Matrix.mulVec_mulVec, map_mul, mul_assoc, hr1, mul_one]
    rw [e]
    exact hX _ (hconj g h hh) _ hv
  have htr_mul : ∀ g h X, tr (g * h) X = tr g (tr h X) := by
    intro g h X
    ext v
    rw [mem_tr, mem_tr, mem_tr, _root_.mul_inv_rev, map_mul, ← Matrix.mulVec_mulVec]
  have htr_one : ∀ X, tr 1 X = X := by
    intro X
    ext v
    rw [mem_tr, inv_one, map_one, Matrix.one_mulVec]
  obtain ⟨b, hb⟩ := Ws.invariant_submodule_eq_span_eigenbasis_of_separable K n (r u) hsep
  have hspan : ∀ X, Inv X → X = Submodule.span K (b '' {i | b i ∈ X}) :=
    fun X hX => hb X (hX u huN)
  have hrank : ∀ X, Inv X → Module.finrank K X = {i | b i ∈ X}.ncard := by
    intro X hX
    have e := hspan X hX
    calc Module.finrank K X = Module.finrank K (Submodule.span K (b '' {i | b i ∈ X})) := by
          rw [← e]
      _ = {i | b i ∈ X}.ncard := by
          have hli := b.linearIndependent.comp
            (Subtype.val : {i // i ∈ {i | b i ∈ X}} → Fin n) Subtype.val_injective
          rw [Set.image_eq_range]
          rw [finrank_span_eq_card (R := K) (b := fun x : {i // i ∈ {i | b i ∈ X}} => b x) hli,
            ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  obtain ⟨W0, hW0i, hW0b, hW0t⟩ : ∃ W, Inv W ∧ W ≠ ⊥ ∧ W ≠ ⊤ := by
    unfold U3.MatIrr at hnot
    push_neg at hnot
    exact hnot
  have hex : ∃ k, ∃ X, Inv X ∧ X ≠ ⊥ ∧ Module.finrank K X = k := ⟨_, W0, hW0i, hW0b, rfl⟩
  obtain ⟨W, hWi, hWb, hWk⟩ := Nat.find_spec hex
  have hmin : ∀ X, Inv X → X ≠ ⊥ → Module.finrank K W ≤ Module.finrank K X := by
    intro X hX hXb
    rw [hWk]
    exact Nat.find_min' hex ⟨X, hX, hXb, rfl⟩
  have hWt : W ≠ ⊤ := by
    intro h
    have h1 := hmin W0 hW0i hW0b
    have h2 := Submodule.finrank_lt hW0t
    rw [h, finrank_top] at h1
    omega
  have tr_ne : ∀ g X, X ≠ ⊥ → tr g X ≠ ⊥ := by
    intro g X hX h
    apply hX
    rw [eq_bot_iff]
    intro v hv
    have hm : r g *ᵥ v ∈ tr g X := by
      rw [mem_tr, Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec]
      exact hv
    rw [h, Submodule.mem_bot] at hm
    have e := congrArg (fun w => r g⁻¹ *ᵥ w) hm
    simp only [Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec, Matrix.mulVec_zero] at e
    rw [e]
    exact Submodule.zero_mem _
  have trW_rank : ∀ g, Module.finrank K (tr g W) = Module.finrank K W := fun g =>
    le_antisymm (Submodule.finrank_map_le _ _) (hmin _ (tr_inv g W hWi) (tr_ne g W hWb))
  have key : ∀ g, (∀ v ∈ W, r g *ᵥ v ∈ W) → tr g W = W := by
    intro g hg
    apply Submodule.eq_of_le_of_finrank_le
    · intro v hv
      rw [mem_tr] at hv
      have e : v = r g *ᵥ (r g⁻¹ *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, hr1, Matrix.one_mulVec]
      rw [e]
      exact hg _ hv
    · rw [trW_rank]
  let S : Subgroup G :=
    { carrier := {g | tr g W = W}
      mul_mem' := by
        intro a c ha hc
        simp only [Set.mem_setOf_eq] at ha hc ⊢
        rw [htr_mul, hc, ha]
      one_mem' := htr_one W
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← htr_mul, inv_mul_cancel, htr_one] }
  have hS : ∀ g, g ∈ S ↔ ∀ v ∈ W, r g *ᵥ v ∈ W := by
    intro g
    constructor
    · intro hg v hv
      have hm : r g *ᵥ v ∈ tr g W := by
        rw [mem_tr, Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec]
        exact hv
      have hg' : tr g W = W := hg
      rw [hg'] at hm
      exact hm
    · exact key g
  refine ⟨W, S, hWb, hWt, fun g hg => (hS g).2 (hWi g hg), hS, ?_⟩
  have huniq : ∀ g1 g2 i, b i ∈ tr g1 W → b i ∈ tr g2 W → tr g1 W = tr g2 W := by
    intro g1 g2 i h1 h2
    have hI : Inv (tr g1 W ⊓ tr g2 W) := fun h hh v hv =>
      ⟨tr_inv g1 W hWi h hh v hv.1, tr_inv g2 W hWi h hh v hv.2⟩
    have hne : tr g1 W ⊓ tr g2 W ≠ ⊥ := by
      intro h
      have hm : b i ∈ tr g1 W ⊓ tr g2 W := ⟨h1, h2⟩
      rw [h, Submodule.mem_bot] at hm
      exact b.ne_zero i hm
    have hm := hmin _ hI hne
    have e1 : tr g1 W ⊓ tr g2 W = tr g1 W :=
      Submodule.eq_of_le_of_finrank_le inf_le_left (by rw [trW_rank]; exact hm)
    have e2 : tr g1 W ⊓ tr g2 W = tr g2 W :=
      Submodule.eq_of_le_of_finrank_le inf_le_right (by rw [trW_rank]; exact hm)
    exact e1.symm.trans e2
  have hcover : ∀ i, ∃ g, b i ∈ tr g W := by
    by_contra hc
    push_neg at hc
    obtain ⟨i, hi⟩ := hc
    have hUi : ∀ g ∈ (⊤ : Subgroup G), ∀ v ∈ ⨆ h, tr h W, r g *ᵥ v ∈ ⨆ h, tr h W := by
      intro g _ v hv
      refine Submodule.iSup_induction (fun h => tr h W)
        (motive := fun v => r g *ᵥ v ∈ ⨆ h, tr h W) hv ?_ ?_ ?_
      · intro h x hx
        refine Submodule.mem_iSup_of_mem (g * h) ?_
        rw [htr_mul, mem_tr, Matrix.mulVec_mulVec, hr2, Matrix.one_mulVec]
        exact hx
      · show r g *ᵥ 0 ∈ ⨆ h, tr h W
        rw [Matrix.mulVec_zero]
        exact Submodule.zero_mem _
      · intro x y hx hy
        show r g *ᵥ (x + y) ∈ ⨆ h, tr h W
        rw [Matrix.mulVec_add]
        exact add_mem hx hy
    have hU := hirr _ hUi
    have hUb : (⨆ h, tr h W) ≠ ⊥ := by
      intro h
      apply hWb
      rw [eq_bot_iff, ← h]
      have := le_iSup (fun h => tr h W) 1
      rw [htr_one] at this
      exact this
    have hUt := hU.resolve_left hUb
    have hbi : b i ∈ ⨆ h, tr h W := by
      rw [hUt]
      exact Submodule.mem_top
    have hz : ∀ v ∈ ⨆ h, tr h W, b.repr v i = 0 := by
      intro v hv
      refine Submodule.iSup_induction (fun h => tr h W)
        (motive := fun v => b.repr v i = 0) hv ?_ ?_ ?_
      · intro g x hx
        have hx' : x ∈ tr g W := hx
        rw [hspan _ (tr_inv g W hWi), Module.Basis.mem_span_image] at hx'
        by_contra h0
        exact hi g (hx' (Finsupp.mem_support_iff.2 h0))
      · simp
      · intro x y hx hy
        simp only [map_add, Finsupp.add_apply]
        rw [hx, hy, add_zero]
    have := hz _ hbi
    simp at this
  let T : G ⧸ S → Set (Fin n) := fun q => {i | b i ∈ tr q.out W}
  have hT1 : ∀ q, (T q).ncard = Module.finrank K W := by
    intro q
    rw [← trW_rank q.out, hrank _ (tr_inv _ W hWi)]
  have hT2 : ∀ i, ∃! q, i ∈ T q := by
    intro i
    obtain ⟨g, hg⟩ := hcover i
    refine ⟨(g : G ⧸ S), ?_, ?_⟩
    · show b i ∈ tr (g : G ⧸ S).out W
      obtain ⟨a, ha⟩ : ∃ a, a = (g : G ⧸ S).out := ⟨_, rfl⟩
      rw [← ha]
      have hm : a⁻¹ * g ∈ S := by
        rw [ha]
        exact QuotientGroup.eq.mp (QuotientGroup.out_eq' (g : G ⧸ S))
      have hm' : tr (a⁻¹ * g) W = W := hm
      have e : tr (a * (a⁻¹ * g)) W = tr a W := by
        rw [htr_mul, hm']
      rw [mul_inv_cancel_left] at e
      rw [← e]
      exact hg
    · intro q hq
      have e := huniq _ _ i hq hg
      have hm : q.out⁻¹ * g ∈ S := by
        show tr _ W = W
        rw [htr_mul, ← e, ← htr_mul, inv_mul_cancel, htr_one]
      exact (QuotientGroup.out_eq' q).symm.trans (QuotientGroup.eq.mpr hm)
  have hc := Ws.card_dvd_of_partition_equal_size (Fin n) (G ⧸ S) T (Module.finrank K W) hT1 hT2
  have hn : Nat.card (Fin n) = n := Nat.card_eq_fintype_card.trans (Fintype.card_fin n)
  rw [hn] at hc
  exact hc
