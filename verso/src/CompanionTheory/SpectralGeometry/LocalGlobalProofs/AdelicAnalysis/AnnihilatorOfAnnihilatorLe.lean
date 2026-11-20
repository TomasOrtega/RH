import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.CofinalDual

/- English proof (translation)
Use `haveI := Fintype.ofFinite B`. Establish `hne : ∀ x y, b x y ≠ 0` using `fun x y h => by`. Use `hn x y` as an intermediate fact. Simplify using `[h] at this`. Establish `h0 : ∀ x, b x 0 = 1` using `fun x => by`.

Use `hr x 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `(mul_eq_left₀ (hne x 0)).1 this.symm`. Set `f : A → AddChar B ℂ` to `fun x => { toFun := b x, map_zero_eq_one' := h0 x, map_add_eq_mul' := hr x }`. Establish `hf : Function.Injective f`.

Introduce `x x' h`. Establish `e : ∀ y, b x y = b x' y` using `fun y => congrArg (fun ψ : AddChar B ℂ => ψ y) h`. Establish `: x - x' = 0` using `hk _ fun y => by`. Establish `h1` using `hl (x - x') x' y`. Rewrite `h1` using `[sub_add_cancel, e y]`.

Conclude with `(mul_eq_right₀ (hne x' y)).1 h1.symm`. Conclude with `sub_eq_zero.1 this`. Establish `e : Nat.card (AddChar B ℂ) = Nat.card B`. Rewrite using `[Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]`. Conclude with `e ▸ Nat.card_le_card_of_injective f hf`.
-/
theorem card_le_of_pairing {A B : Type} [AddCommGroup A] [AddCommGroup B] [Finite A] [Finite B]
    (b : A → B → ℂ) (hn : ∀ x y, ‖b x y‖ = 1)
    (hl : ∀ x x' y, b (x + x') y = b x y * b x' y)
    (hr : ∀ x y y', b x (y + y') = b x y * b x y')
    (hk : ∀ x, (∀ y, b x y = 1) → x = 0) : Nat.card A ≤ Nat.card B := by
  classical
  haveI := Fintype.ofFinite B
  have hne : ∀ x y, b x y ≠ 0 := fun x y h => by
    have := hn x y
    simp [h] at this
  have h0 : ∀ x, b x 0 = 1 := fun x => by
    have := hr x 0 0
    rw [add_zero] at this
    exact (mul_eq_left₀ (hne x 0)).1 this.symm
  let f : A → AddChar B ℂ := fun x =>
    { toFun := b x, map_zero_eq_one' := h0 x, map_add_eq_mul' := hr x }
  have hf : Function.Injective f := by
    intro x x' h
    have e : ∀ y, b x y = b x' y := fun y => congrArg (fun ψ : AddChar B ℂ => ψ y) h
    have : x - x' = 0 := hk _ fun y => by
      have h1 := hl (x - x') x' y
      rw [sub_add_cancel, e y] at h1
      exact (mul_eq_right₀ (hne x' y)).1 h1.symm
    exact sub_eq_zero.1 this
  have e : Nat.card (AddChar B ℂ) = Nat.card B := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  exact e ▸ Nat.card_le_card_of_injective f hf

/- English proof (translation)
Establish `hx : ∀ (x x' : X) (y : Y), (x : X ⧸ N) = x' → c x y = c x' y`. Introduce `x x' y h`. Establish `hm : -x + x' ∈ N` using `QuotientAddGroup.eq.1 h`. Use `hl x (-x + x') y` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_left, (hN _).1 hm y, mul_one]`.

Conclude with `this.symm`. Establish `hy : ∀ (x : X) (y y' : Y), (y : Y ⧸ M) = y' → c x y = c x y'`. Introduce `x y y' h`. Establish `hm : -y + y' ∈ M` using `QuotientAddGroup.eq.1 h`. Use `hr x y (-y + y')` as an intermediate fact.

Rewrite `this` using `[add_neg_cancel_left, (hM _).1 hm x, mul_one]`. Conclude with `this.symm`. Set `b : X ⧸ N → Y ⧸ M → ℂ` to `fun p q => c (Quotient.out p) (Quotient.out q)`. Establish `hb : ∀ (x : X) (y : Y), b (x : X ⧸ N) (y : Y ⧸ M) = c x y` using `fun x y => by`. Express the relevant statement in the definitionally equal form `c (Quotient.out (x : X ⧸ N)) (Quotient.out (y : Y ⧸ M)) = c x y`.

Rewrite using `[hx _ x _ (QuotientAddGroup.out_eq' _), hy _ _ y (QuotientAddGroup.out_eq' _)]`. Establish `bn : ∀ p q, ‖b p q‖ = 1` using `fun p q => hn _ _`. Establish `bl : ∀ p p' q, b (p + p') q = b p q * b p' q`. Introduce `p p' q`. Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective p`.

Take `⟨x', rfl⟩` from `QuotientAddGroup.mk_surjective p'`. Take `⟨y, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Rewrite using `[← QuotientAddGroup.mk_add, hb, hb, hb, hl]`. Establish `br : ∀ p q q', b p (q + q') = b p q * b p q'`. Introduce `p q q'`.

Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective p`. Take `⟨y, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Take `⟨y', rfl⟩` from `QuotientAddGroup.mk_surjective q'`. Rewrite using `[← QuotientAddGroup.mk_add, hb, hb, hb, hr]`. Establish `k1 : ∀ p, (∀ q, b p q = 1) → p = 0`.

Introduce `p h`. Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective p`. Conclude with `(QuotientAddGroup.eq_zero_iff x).2 ((hN x).2 fun y => by rw [← hb, h])`. Establish `k2 : ∀ q, (∀ p, b p q = 1) → q = 0`. Introduce `q h`.

Take `⟨y, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Conclude with `(QuotientAddGroup.eq_zero_iff y).2 ((hM y).2 fun x => by rw [← hb, h])`. Conclude with `le_antisymm (card_le_of_pairing b bn bl br k1) (card_le_of_pairing (fun q p => b p q) (fun q p => bn p q) (fun q q' p => br p q q') (fun q p p' => bl p p' q) k2)`.
-/
theorem index_eq_of_pairing {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (c : X → Y → ℂ)
    (hn : ∀ x y, ‖c x y‖ = 1)
    (hl : ∀ x x' y, c (x + x') y = c x y * c x' y)
    (hr : ∀ x y y', c x (y + y') = c x y * c x y')
    (N : AddSubgroup X) (M : AddSubgroup Y)
    (hN : ∀ x, x ∈ N ↔ ∀ y, c x y = 1) (hM : ∀ y, y ∈ M ↔ ∀ x, c x y = 1)
    [N.FiniteIndex] [M.FiniteIndex] : N.index = M.index := by
  have hx : ∀ (x x' : X) (y : Y), (x : X ⧸ N) = x' → c x y = c x' y := by
    intro x x' y h
    have hm : -x + x' ∈ N := QuotientAddGroup.eq.1 h
    have := hl x (-x + x') y
    rw [add_neg_cancel_left, (hN _).1 hm y, mul_one] at this
    exact this.symm
  have hy : ∀ (x : X) (y y' : Y), (y : Y ⧸ M) = y' → c x y = c x y' := by
    intro x y y' h
    have hm : -y + y' ∈ M := QuotientAddGroup.eq.1 h
    have := hr x y (-y + y')
    rw [add_neg_cancel_left, (hM _).1 hm x, mul_one] at this
    exact this.symm
  let b : X ⧸ N → Y ⧸ M → ℂ := fun p q => c (Quotient.out p) (Quotient.out q)
  have hb : ∀ (x : X) (y : Y), b (x : X ⧸ N) (y : Y ⧸ M) = c x y := fun x y => by
    change c (Quotient.out (x : X ⧸ N)) (Quotient.out (y : Y ⧸ M)) = c x y
    rw [hx _ x _ (QuotientAddGroup.out_eq' _), hy _ _ y (QuotientAddGroup.out_eq' _)]
  have bn : ∀ p q, ‖b p q‖ = 1 := fun p q => hn _ _
  have bl : ∀ p p' q, b (p + p') q = b p q * b p' q := by
    intro p p' q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
    obtain ⟨x', rfl⟩ := QuotientAddGroup.mk_surjective p'
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [← QuotientAddGroup.mk_add, hb, hb, hb, hl]
  have br : ∀ p q q', b p (q + q') = b p q * b p q' := by
    intro p q q'
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨y', rfl⟩ := QuotientAddGroup.mk_surjective q'
    rw [← QuotientAddGroup.mk_add, hb, hb, hb, hr]
  have k1 : ∀ p, (∀ q, b p q = 1) → p = 0 := by
    intro p h
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
    exact (QuotientAddGroup.eq_zero_iff x).2 ((hN x).2 fun y => by rw [← hb, h])
  have k2 : ∀ q, (∀ p, b p q = 1) → q = 0 := by
    intro q h
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact (QuotientAddGroup.eq_zero_iff y).2 ((hM y).2 fun x => by rw [← hb, h])
  exact le_antisymm (card_le_of_pairing b bn bl br k1)
    (card_le_of_pairing (fun q p => b p q) (fun q p => bn p q) (fun q q' p => br p q q')
      (fun q p p' => bl p p' q) k2)

/- English proof (translation)
Use `haveI : CompactSpace T := isCompact_iff_compactSpace.1 hT`. Establish `ho : IsOpen ((S.addSubgroupOf T : AddSubgroup T) : Set T)` using `hS.preimage continuous_subtype_val`. Use `haveI := AddSubgroup.quotient_finite_of_isOpen _ ho`. Establish `: (S.addSubgroupOf T).FiniteIndex` using `AddSubgroup.finiteIndex_of_finite_quotient`. Conclude with `this.index_ne_zero`.
-/
theorem relIndex_ne_zero_of_isOpen {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] (S T : AddSubgroup V) (hS : IsOpen (S : Set V))
    (hT : IsCompact (T : Set V)) : S.relIndex T ≠ 0 := by
  haveI : CompactSpace T := isCompact_iff_compactSpace.1 hT
  have ho : IsOpen ((S.addSubgroupOf T : AddSubgroup T) : Set T) :=
    hS.preimage continuous_subtype_val
  haveI := AddSubgroup.quotient_finite_of_isOpen _ ho
  have : (S.addSubgroupOf T).FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  exact this.index_ne_zero

/- English proof (translation)
Use `haveI : (S.addSubgroupOf T).FiniteIndex := ⟨hf⟩`. Use `haveI := Fintype.ofFinite (T ⧸ S.addSubgroupOf T)`. Set `o : T ⧸ S.addSubgroupOf T → T` to `fun q => Quotient.out q`. Establish `ho : ∀ q, ((o q : T) : T ⧸ S.addSubgroupOf T) = q` using `fun q => QuotientAddGroup.out_eq' q`. Set `C : T ⧸ S.addSubgroupOf T → Set V` to `fun q => (fun v => (-(o q : V)) + v) ⁻¹' (S : Set V)`.

Establish `hU : (T : Set V) = ⋃ q, C q`. Use extensionality with `v`. Simplify using `only [Set.mem_iUnion, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `hv`.

Use `⟨((⟨v, hv⟩ : T) : T ⧸ S.addSubgroupOf T), ?_⟩` and prove the remaining obligations. Establish `h` using `QuotientAddGroup.eq.1 (ho ((⟨v, hv⟩ : T) : T ⧸ S.addSubgroupOf T))`. Conclude with `AddSubgroup.mem_addSubgroupOf.1 h`. Introduce and unpack `⟨q, hq⟩`. Establish `h1 : -(o q : V) + v ∈ T` using `hST hq`.

Use `T.add_mem (o q).2 h1` as an intermediate fact. Simplify using `using this`. Establish `hd : Pairwise (Function.onFun Disjoint C)`. Introduce `q q' hne`. Use `Set.disjoint_left.2 fun v hv hv' => hne ?_` and prove the remaining obligations.

Establish `h1 : -(o q : V) + v ∈ S` using `hv`. Establish `h2 : -(o q' : V) + v ∈ S` using `hv'`. Establish `h3 : -(o q : V) + (o q' : V) ∈ S`. Use `S.sub_mem h1 h2` as an intermediate fact. Establish `e : -(o q : V) + v - (-(o q' : V) + v) = -(o q : V) + (o q' : V)` using `by abel`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `h4 : ((o q : T) : T ⧸ S.addSubgroupOf T) = (o q' : T)` using `QuotientAddGroup.eq.2 (AddSubgroup.mem_addSubgroupOf.2 (by simpa using h3))`. Rewrite `h4` using `[ho, ho]`. Conclude with `h4`. Establish `hm : ∀ q, MeasurableSet (C q)` using `fun q => (hS.preimage (continuous_const.add continuous_id)).measurableSet`.

Establish `hc : ∀ q, μ (C q) = μ S` using `fun q => measure_preimage_add μ _ _`. Rewrite using `[hU, measure_iUnion hd hm, tsum_fintype]`. Simplify using `only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Use `congr 2`. Rewrite using `[AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]`.
-/
theorem measure_eq_relIndex_mul {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddLeftInvariant] (S T : AddSubgroup V) (hST : S ≤ T) (hS : IsOpen (S : Set V))
    (hf : S.relIndex T ≠ 0) : μ T = S.relIndex T * μ S := by
  classical
  haveI : (S.addSubgroupOf T).FiniteIndex := ⟨hf⟩
  haveI := Fintype.ofFinite (T ⧸ S.addSubgroupOf T)
  let o : T ⧸ S.addSubgroupOf T → T := fun q => Quotient.out q
  have ho : ∀ q, ((o q : T) : T ⧸ S.addSubgroupOf T) = q := fun q => QuotientAddGroup.out_eq' q
  let C : T ⧸ S.addSubgroupOf T → Set V := fun q => (fun v => (-(o q : V)) + v) ⁻¹' (S : Set V)
  have hU : (T : Set V) = ⋃ q, C q := by
    ext v
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hv
      refine ⟨((⟨v, hv⟩ : T) : T ⧸ S.addSubgroupOf T), ?_⟩
      have h := QuotientAddGroup.eq.1 (ho ((⟨v, hv⟩ : T) : T ⧸ S.addSubgroupOf T))
      exact AddSubgroup.mem_addSubgroupOf.1 h
    · rintro ⟨q, hq⟩
      have h1 : -(o q : V) + v ∈ T := hST hq
      have := T.add_mem (o q).2 h1
      simpa using this
  have hd : Pairwise (Function.onFun Disjoint C) := by
    intro q q' hne
    refine Set.disjoint_left.2 fun v hv hv' => hne ?_
    have h1 : -(o q : V) + v ∈ S := hv
    have h2 : -(o q' : V) + v ∈ S := hv'
    have h3 : -(o q : V) + (o q' : V) ∈ S := by
      have := S.sub_mem h1 h2
      have e : -(o q : V) + v - (-(o q' : V) + v) = -(o q : V) + (o q' : V) := by abel
      rwa [e] at this
    have h4 : ((o q : T) : T ⧸ S.addSubgroupOf T) = (o q' : T) :=
      QuotientAddGroup.eq.2 (AddSubgroup.mem_addSubgroupOf.2 (by simpa using h3))
    rw [ho, ho] at h4
    exact h4
  have hm : ∀ q, MeasurableSet (C q) := fun q =>
    (hS.preimage (continuous_const.add continuous_id)).measurableSet
  have hc : ∀ q, μ (C q) = μ S := fun q => measure_preimage_add μ _ _
  rw [hU, measure_iUnion hd hm, tsum_fintype]
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 2
  rw [AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]

def perpSub {V : Type} [AddCommGroup V] (χ : V → V → ℂ) (hs : ∀ x y, χ x y = χ y x)
    (hn : ∀ x y, ‖χ x y‖ = 1) (ha : ∀ x x' y, χ (x + x') y = χ x y * χ x' y)
    (L : AddSubgroup V) : AddSubgroup V where
  carrier := perp χ L
  add_mem' := by
    intro y y' hy hy' x hx
    rw [hs, ha, hs y, hs y', hy x hx, hy' x hx, one_mul]
  zero_mem' := by
    intro x _
    have hne : χ 0 x ≠ 0 := fun h => by
      have := hn 0 x
      simp [h] at this
    have := ha 0 0 x
    rw [add_zero] at this
    rw [hs]
    exact (mul_eq_left₀ hne).1 this.symm
  neg_mem' := by
    intro y hy x hx
    have hne : χ 0 x ≠ 0 := fun h => by
      have := hn 0 x
      simp [h] at this
    have h0 : χ 0 x = 1 := by
      have := ha 0 0 x
      rw [add_zero] at this
      exact (mul_eq_left₀ hne).1 this.symm
    have := ha y (-y) x
    rw [add_neg_cancel, h0, hs y x, hy x hx, one_mul] at this
    rw [hs]
    exact this.symm

/- English proof (translation)
Use `haveI : (X₀.addSubgroupOf X).FiniteIndex := ⟨fX⟩`. Use `haveI : (Y₀.addSubgroupOf Y).FiniteIndex := ⟨fY⟩`. Use `index_eq_of_pairing (fun (x : X) (y : Y) => χ x y) (fun x y => hn _ _) (fun x x' y => ha _ _ _) (fun x y y' => by` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `χ x ((y : V) + y') = _`. Rewrite using `[hs, ha, hs y, hs y']) _ _ ?_ ?_`.

Introduce `x`. Rewrite using `[AddSubgroup.mem_addSubgroupOf, hX x x.2]`. Conclude with `⟨fun h y => h y y.2, fun h y hy => h ⟨y, hy⟩⟩`. Introduce `y`. Rewrite using `[AddSubgroup.mem_addSubgroupOf, hY y y.2]`.

Conclude with `⟨fun h x => h x x.2, fun h x hx => h ⟨x, hx⟩⟩`.
-/
theorem relIndex_eq_of_pairing {V : Type} [AddCommGroup V] (χ : V → V → ℂ)
    (hs : ∀ x y, χ x y = χ y x) (hn : ∀ x y, ‖χ x y‖ = 1)
    (ha : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (X₀ X Y₀ Y : AddSubgroup V)
    (hX : ∀ x ∈ X, (x ∈ X₀ ↔ ∀ y ∈ Y, χ x y = 1))
    (hY : ∀ y ∈ Y, (y ∈ Y₀ ↔ ∀ x ∈ X, χ x y = 1))
    (fX : X₀.relIndex X ≠ 0) (fY : Y₀.relIndex Y ≠ 0) : X₀.relIndex X = Y₀.relIndex Y := by
  haveI : (X₀.addSubgroupOf X).FiniteIndex := ⟨fX⟩
  haveI : (Y₀.addSubgroupOf Y).FiniteIndex := ⟨fY⟩
  refine index_eq_of_pairing (fun (x : X) (y : Y) => χ x y) (fun x y => hn _ _)
    (fun x x' y => ha _ _ _)
    (fun x y y' => by
      change χ x ((y : V) + y') = _
      rw [hs, ha, hs y, hs y']) _ _ ?_ ?_
  · intro x
    rw [AddSubgroup.mem_addSubgroupOf, hX x x.2]
    exact ⟨fun h y => h y y.2, fun h y hy => h ⟨y, hy⟩⟩
  · intro y
    rw [AddSubgroup.mem_addSubgroupOf, hY y y.2]
    exact ⟨fun h x => h x x.2, fun h x hx => h ⟨x, hx⟩⟩

/- English proof (translation)
Introduce `V _ _ _ _ _ χ μ hμ hs hn ha L₁ L L₂ h1 h2 oL₁ cL₂ cP₁ oP₂ dd₁ dd₂ _ m₂`. Set `Q : AddSubgroup V → AddSubgroup V` to `perpSub χ hs hn ha`. Establish `hQ : ∀ (A : AddSubgroup V) (y : V), y ∈ Q A ↔ ∀ x ∈ A, χ x y = 1` using `fun _ _ => Iff.rfl`. Establish `hQc : ∀ A : AddSubgroup V, (Q A : Set V) = perp χ A` using `fun _ => rfl`. Establish `anti : ∀ A B : AddSubgroup V, A ≤ B → Q B ≤ Q A` using `fun A B h y hy x hx => hy x (h hx)`.

Establish `hself : ∀ A : AddSubgroup V, A ≤ Q (Q A)` using `fun A x hx y hy => by`. Rewrite using `[hs]`. Conclude with `hy x hx`. Establish `placeRankTwoOne : Q L₂ ≤ Q L₁` using `anti _ _ (h1.trans h2)`. Establish `P2 : Q L₂ ≤ Q L` using `anti _ _ h2`.

Establish `P1 : Q L ≤ Q L₁` using `anti _ _ h1`. Establish `LM : L ≤ Q (Q L)` using `hself L`. Establish `ML : Q (Q L) ≤ L₂` using `fun z hz => dd₂ (anti _ _ P2 hz)`. Establish `n0 : L₁.relIndex L₂ ≠ 0` using `relIndex_ne_zero_of_isOpen _ _ oL₁ cL₂`. Establish `p0 : (Q L₂).relIndex (Q L₁) ≠ 0` using `relIndex_ne_zero_of_isOpen _ _ oP₂ cP₁`.

Establish `ea` using `AddSubgroup.relIndex_mul_relIndex L₁ L L₂ h1 h2`. Establish `ep` using `AddSubgroup.relIndex_mul_relIndex (Q L₂) (Q L) (Q L₁) P2 P1`. Establish `ek` using `AddSubgroup.relIndex_mul_relIndex L (Q (Q L)) L₂ LM ML`. Establish `a0 : L₁.relIndex L ≠ 0` using `fun h => n0 (by rw [← ea, h, zero_mul])`. Establish `a'0 : L.relIndex L₂ ≠ 0` using `fun h => n0 (by rw [← ea, h, mul_zero])`.

Establish `q0 : (Q L₂).relIndex (Q L) ≠ 0` using `fun h => p0 (by rw [← ep, h, zero_mul])`. Establish `q'0 : (Q L).relIndex (Q L₁) ≠ 0` using `fun h => p0 (by rw [← ep, h, mul_zero])`. Establish `m0 : (Q (Q L)).relIndex L₂ ≠ 0` using `fun h => a'0 (by rw [← ek, h, mul_zero])`. Establish `kerL₁ : ∀ x, x ∈ L₁ ↔ ∀ y ∈ Q L₁, χ x y = 1` using `fun x => ⟨fun hx y hy => hy x hx, fun h => dd₁ fun y hy => by`. Rewrite using `[hs]`.

Conclude with `h y hy⟩`. Establish `e1 : L₁.relIndex L = (Q L).relIndex (Q L₁)` using `relIndex_eq_of_pairing χ hs hn ha L₁ L (Q L) (Q L₁) (fun x _ => kerL₁ x) (fun y _ => hQ L y) a0 q'0`. Establish `e2 : (Q (Q L)).relIndex L₂ = (Q L₂).relIndex (Q L)` using `relIndex_eq_of_pairing χ hs hn ha (Q (Q L)) L₂ (Q L₂) (Q L) (fun x _ => by`. Rewrite using `[hQ]`. Conclude with `forall₂_congr fun y _ => by rw [hs])`.

Use the proof step `(fun y _ => hQ L₂ y) m0 q0`. Establish `e3 : L₁.relIndex L₂ = (Q L₂).relIndex (Q L₁)` using `relIndex_eq_of_pairing χ hs hn ha L₁ L₂ (Q L₂) (Q L₁) (fun x _ => kerL₁ x) (fun y _ => hQ L₂ y) n0 p0`. Establish `e4 : L.relIndex L₂ = (Q L₂).relIndex (Q L)`. Establish `: L₁.relIndex L * L.relIndex L₂ = L₁.relIndex L * (Q L₂).relIndex (Q L)`. Rewrite using `[ea, e3, ← ep, e1, mul_comm]`.

Conclude with `Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero a0) this`. Establish `hk : L.relIndex (Q (Q L)) = 1`. Establish `: L.relIndex (Q (Q L)) * (Q (Q L)).relIndex L₂ = 1 * (Q (Q L)).relIndex L₂`. Rewrite using `[ek, one_mul, e2, e4]`. Conclude with `Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero m0) this`.

Establish `MLe : Q (Q L) ≤ L` using `AddSubgroup.relIndex_eq_one.1 hk`. Establish `oP : IsOpen (Q L : Set V)` using `AddSubgroup.isOpen_mono P2 oP₂`. Use `⟨?_, oP, MLe, ?_⟩` and prove the remaining obligations. Conclude with `cP₁.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ oP) P1`. Express the relevant statement in the definitionally equal form `μ L * μ (Q L) = 1`.

Express the relevant statement in the definitionally equal form `μ L₂ * μ (Q L₂) = 1 at m₂`. Rewrite using `[measure_eq_relIndex_mul μ L₁ L h1 oL₁ a0, measure_eq_relIndex_mul μ (Q L₂) (Q L) P2 oP₂ q0, ← m₂, measure_eq_relIndex_mul μ L₁ L₂ (h1.trans h2) oL₁ n0, ← ea, e4]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem selfDual_of_between : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (χ : V → V → ℂ) (μ : Measure V), μ.IsAddHaarMeasure → (∀ x y, χ x y = χ y x) → (∀ x y, ‖χ x y‖ = 1) → (∀ x x' y, χ (x + x') y = χ x y * χ x' y) → ∀ L₁ L L₂ : AddSubgroup V, L₁ ≤ L → L ≤ L₂ → IsOpen (L₁ : Set V) → IsCompact (L₂ : Set V) → IsCompact (perp χ L₁) → IsOpen (perp χ L₂) → perp χ (perp χ L₁) ⊆ L₁ → perp χ (perp χ L₂) ⊆ L₂ → μ L₁ * μ (perp χ L₁) = 1 → μ L₂ * μ (perp χ L₂) = 1 → IsCompact (perp χ L) ∧ IsOpen (perp χ L) ∧ perp χ (perp χ L) ⊆ L ∧ μ L * μ (perp χ L) = 1 := by
  intro V _ _ _ _ _ χ μ hμ hs hn ha L₁ L L₂ h1 h2 oL₁ cL₂ cP₁ oP₂ dd₁ dd₂ _ m₂
  let Q : AddSubgroup V → AddSubgroup V := perpSub χ hs hn ha
  have hQ : ∀ (A : AddSubgroup V) (y : V), y ∈ Q A ↔ ∀ x ∈ A, χ x y = 1 := fun _ _ => Iff.rfl
  have hQc : ∀ A : AddSubgroup V, (Q A : Set V) = perp χ A := fun _ => rfl
  have anti : ∀ A B : AddSubgroup V, A ≤ B → Q B ≤ Q A :=
    fun A B h y hy x hx => hy x (h hx)
  have hself : ∀ A : AddSubgroup V, A ≤ Q (Q A) := fun A x hx y hy => by
    rw [hs]
    exact hy x hx
  have placeRankTwoOne : Q L₂ ≤ Q L₁ := anti _ _ (h1.trans h2)
  have P2 : Q L₂ ≤ Q L := anti _ _ h2
  have P1 : Q L ≤ Q L₁ := anti _ _ h1
  have LM : L ≤ Q (Q L) := hself L
  have ML : Q (Q L) ≤ L₂ := fun z hz => dd₂ (anti _ _ P2 hz)
  have n0 : L₁.relIndex L₂ ≠ 0 := relIndex_ne_zero_of_isOpen _ _ oL₁ cL₂
  have p0 : (Q L₂).relIndex (Q L₁) ≠ 0 := relIndex_ne_zero_of_isOpen _ _ oP₂ cP₁
  have ea := AddSubgroup.relIndex_mul_relIndex L₁ L L₂ h1 h2
  have ep := AddSubgroup.relIndex_mul_relIndex (Q L₂) (Q L) (Q L₁) P2 P1
  have ek := AddSubgroup.relIndex_mul_relIndex L (Q (Q L)) L₂ LM ML
  have a0 : L₁.relIndex L ≠ 0 := fun h => n0 (by rw [← ea, h, zero_mul])
  have a'0 : L.relIndex L₂ ≠ 0 := fun h => n0 (by rw [← ea, h, mul_zero])
  have q0 : (Q L₂).relIndex (Q L) ≠ 0 := fun h => p0 (by rw [← ep, h, zero_mul])
  have q'0 : (Q L).relIndex (Q L₁) ≠ 0 := fun h => p0 (by rw [← ep, h, mul_zero])
  have m0 : (Q (Q L)).relIndex L₂ ≠ 0 := fun h => a'0 (by rw [← ek, h, mul_zero])
  have kerL₁ : ∀ x, x ∈ L₁ ↔ ∀ y ∈ Q L₁, χ x y = 1 := fun x =>
    ⟨fun hx y hy => hy x hx, fun h => dd₁ fun y hy => by
      rw [hs]
      exact h y hy⟩
  have e1 : L₁.relIndex L = (Q L).relIndex (Q L₁) :=
    relIndex_eq_of_pairing χ hs hn ha L₁ L (Q L) (Q L₁) (fun x _ => kerL₁ x)
      (fun y _ => hQ L y) a0 q'0
  have e2 : (Q (Q L)).relIndex L₂ = (Q L₂).relIndex (Q L) :=
    relIndex_eq_of_pairing χ hs hn ha (Q (Q L)) L₂ (Q L₂) (Q L)
      (fun x _ => by
        rw [hQ]
        exact forall₂_congr fun y _ => by rw [hs])
      (fun y _ => hQ L₂ y) m0 q0
  have e3 : L₁.relIndex L₂ = (Q L₂).relIndex (Q L₁) :=
    relIndex_eq_of_pairing χ hs hn ha L₁ L₂ (Q L₂) (Q L₁) (fun x _ => kerL₁ x)
      (fun y _ => hQ L₂ y) n0 p0
  have e4 : L.relIndex L₂ = (Q L₂).relIndex (Q L) := by
    have : L₁.relIndex L * L.relIndex L₂ = L₁.relIndex L * (Q L₂).relIndex (Q L) := by
      rw [ea, e3, ← ep, e1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero a0) this
  have hk : L.relIndex (Q (Q L)) = 1 := by
    have : L.relIndex (Q (Q L)) * (Q (Q L)).relIndex L₂ = 1 * (Q (Q L)).relIndex L₂ := by
      rw [ek, one_mul, e2, e4]
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero m0) this
  have MLe : Q (Q L) ≤ L := AddSubgroup.relIndex_eq_one.1 hk
  have oP : IsOpen (Q L : Set V) := AddSubgroup.isOpen_mono P2 oP₂
  refine ⟨?_, oP, MLe, ?_⟩
  · exact cP₁.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ oP) P1
  · change μ L * μ (Q L) = 1
    change μ L₂ * μ (Q L₂) = 1 at m₂
    rw [measure_eq_relIndex_mul μ L₁ L h1 oL₁ a0, measure_eq_relIndex_mul μ (Q L₂) (Q L) P2 oP₂ q0,
      ← m₂, measure_eq_relIndex_mul μ L₁ L₂ (h1.trans h2) oL₁ n0, ← ea, e4]
    push_cast
    ring

end GlobalTheory.CompanionTheory.SW.CofinalDual
