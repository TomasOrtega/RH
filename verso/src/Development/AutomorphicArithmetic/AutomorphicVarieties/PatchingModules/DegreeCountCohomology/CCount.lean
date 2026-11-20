import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Rewrite using `[← AddSubgroup.index_ker, AddSubgroup.card_mul_index]`.
-/
private theorem card_ker_mul_card_range_eq_card {G H : Type} [AddGroup G] [AddGroup H] (f : G →+ H) :
    Nat.card f.ker * Nat.card f.range = Nat.card G := by
  rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]

/- English proof (translation)
Introduce `R Γ M _ _ _ _ _ ρ c hc h2`. Set `f : M →+ (Γ → M)` to `{ toFun := fun m g => ρ g m - m map_zero' := by ext g; simp map_add' := by intro a b; ext g; simp; abel }`. Establish `hf : ∀ m g, f m g = ρ g m - m` using `fun _ _ => rfl`. Establish `hBl : ∀ z, z ∈ Bl ρ ↔ z ∈ f.range`. Introduce `z`.

Simplify using `only [Bl, LinearMap.mem_range, AddMonoidHom.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, rfl⟩`. Conclude with `⟨m, by ext g; simp [hf]⟩`. Introduce and unpack `⟨m, rfl⟩`.

Conclude with `⟨m, by ext g; simp [hf]⟩`. Establish `hker : ∀ m, m ∈ f.ker ↔ m ∈ ρ.invariants`. Introduce `m`. Rewrite using `[AddMonoidHom.mem_ker, Representation.mem_invariants]`. Prove the components needed by the constructor for the conclusion.

Introduce `h g`. Use `congrFun h g` as an intermediate fact. Rewrite `this` using `[hf]`. Simplify `this` using `[sub_eq_zero]`. Introduce `h`.

Use extensionality with `g`. Simplify using `[hf, h g]`. Establish `cardBl : Nat.card (Bl ρ) = Nat.card f.range` using `Nat.card_congr (Equiv.subtypeEquivRight hBl)`. Establish `cardInv : Nat.card ρ.invariants = Nat.card f.ker` using `Nat.card_congr (Equiv.subtypeEquivRight (fun m => (hker m).symm))`. Set `d : M →+ M` to `{ toFun := fun m => ρ c m - m map_zero' := by simp map_add' := by intro a b; simp; abel }`.

Establish `hd : ∀ m, d m = ρ c m - m` using `fun _ => rfl`. Establish `cardFix : Nat.card {m : M // ρ c m = m} = Nat.card d.ker` using `Nat.card_congr (Equiv.subtypeEquivRight (fun m => by`. Rewrite using `[AddMonoidHom.mem_ker, hd, sub_eq_zero]))`. Establish `hdM : Nat.card d.range * Nat.card {m : M // ρ c m = m} = Nat.card M`. Rewrite using `[cardFix, mul_comm]`.

Conclude with `card_ker_mul_card_range_eq_card d`. Set `Mc : AddSubgroup M` to `{ carrier := {m | ρ c m = m} add_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq] at *`. Rewrite using `[map_add, ha, hb]`.

Use the proof step `zero_mem' := by simp`. Use the proof step `neg_mem' := by`. Introduce `a ha`. Simplify using `only [Set.mem_setOf_eq] at *`. Rewrite using `[map_neg, ha] }`.

Establish `cardMc : Nat.card {m : M // ρ c m = m} = Nat.card Mc` using `Nat.card_congr (Equiv.subtypeEquivRight (fun m => Iff.rfl))`. Set `f' : Mc →+ (Γ → M)` to `f.comp Mc.subtype`. Establish `hf' : ∀ x, f' x = f x.1` using `fun _ => rfl`. Establish `cardKer' : Nat.card f'.ker = Nat.card ρ.invariants`. Rewrite using `[cardInv]`.

Conclude with `Nat.card_congr { toFun := fun x => ⟨x.1.1, by`. Use `AddMonoidHom.mem_ker.1 x.2` as an intermediate fact. Rewrite `this` using `[hf']`. Conclude with `AddMonoidHom.mem_ker.2 this⟩`. Use `invFun := fun v => ⟨⟨v.1, ((hker _).1 v.2 |> (Representation.mem_invariants ρ _).1) c⟩, by`.

Apply `AddMonoidHom.mem_ker.2` to reduce the goal to its premises. Rewrite using `[hf']`. Conclude with `AddMonoidHom.mem_ker.1 v.2⟩`. Use `left_inv := fun _ => rfl`. Use `right_inv := fun _ => rfl }`.

Establish `hRange' : ∀ z, z ∈ f'.range ↔ z ∈ {z | z ∈ Bl ρ ∧ z c = 0}`. Introduce `z`. Simplify using `only [Set.mem_setOf_eq, AddMonoidHom.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`.

Use `⟨(hBl _).2 ⟨x.1, (hf' x).symm⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hf', hf, sub_eq_zero]`. Conclude with `x.2`. Introduce and unpack `⟨hz, hzc⟩`. Take `⟨m, rfl⟩` from `(hBl z).1 hz`.

Rewrite `hzc` using `[hf, sub_eq_zero]`. Conclude with `⟨⟨m, hzc⟩, rfl⟩`. Establish `cardR' : Nat.card f'.range = {z | z ∈ Bl ρ ∧ z c = 0}.ncard`. Rewrite using `[← Nat.card_coe_set_eq]`. Conclude with `Nat.card_congr (Equiv.subtypeEquivRight hRange')`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `Z _ hle hcoc`. Set `ev : Z →+ M` to `{ toFun := fun z => z.1 c map_zero' := rfl map_add' := fun _ _ => rfl }`. Establish `hev : ∀ z, ev z = z.1 c` using `fun _ => rfl`. Establish `kerEv : Nat.card ev.ker = {z | z ∈ Z ∧ z c = 0}.ncard`.

Rewrite using `[← Nat.card_coe_set_eq]`. Conclude with `Nat.card_congr { toFun := fun x => ⟨x.1.1, x.1.2, by`. Use `AddMonoidHom.mem_ker.1 x.2` as an intermediate fact. Rewrite using `[hev] at this⟩` and apply the resulting hypothesis. Use `invFun := fun y => ⟨⟨y.1, y.2.1⟩, AddMonoidHom.mem_ker.2 (by rw [hev]; exact y.2.2)⟩`.

Use `left_inv := fun _ => rfl`. Use `right_inv := fun _ => rfl }`. Establish `rangeEv : ∀ x, x ∈ ev.range ↔ x ∈ d.range`. Introduce `x`. Simplify using `only [AddMonoidHom.mem_range]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨z, hz⟩, rfl⟩`. Rewrite using `[hev]`. Establish `h1` using `hcoc z hz 1 1`. Simplify using `only [mul_one, map_one, Module.End.one_apply] at h1`.

Establish `hz1 : z 1 = 0`. Establish `: z 1 + z 1 = z 1 + 0` using `by rw [add_zero]; exact h1.symm`. Conclude with `add_left_cancel this`. Establish `h2c` using `hcoc z hz c c`. Rewrite `h2c` using `[hc, hz1]`.

Take `⟨u, hu⟩` from `h2`. Use `⟨-((↑u⁻¹ : R) • z c), ?_⟩` and prove the remaining obligations. Rewrite using `[hd, map_neg, map_smul]`. Establish `hneg : ρ c (z c) = -z c`. Rewrite using `[eq_neg_iff_add_eq_zero, add_comm]`.

Conclude with `h2c.symm`. Rewrite using `[hneg, smul_neg, neg_neg, sub_neg_eq_add, ← add_smul]`. Establish `: (↑u⁻¹ : R) + ↑u⁻¹ = 1`. Rewrite using `[← Units.inv_mul u, hu]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, one_smul]`. Introduce and unpack `⟨m, rfl⟩`. Establish `hmem : f m ∈ Z` using `hle ((Submodule.mem_toAddSubgroup _).2 ((hBl _).2 ⟨m, rfl⟩))`. Use `⟨⟨f m, hmem⟩, ?_⟩` and prove the remaining obligations. Use `show f m c = d m`.

Rewrite using `[hf, hd]`. Establish `cardRangeEv : Nat.card ev.range = Nat.card d.range` using `Nat.card_congr (Equiv.subtypeEquivRight rangeEv)`. Rewrite using `[← kerEv, ← card_ker_mul_card_range_eq_card ev, cardRangeEv, mul_assoc, hdM]`. Rewrite using `[cardBl, cardInv, mul_comm]`. Conclude with `card_ker_mul_card_range_eq_card f`.

Rewrite using `[← cardR', ← cardKer', cardMc, mul_comm]`. Conclude with `card_ker_mul_card_range_eq_card f'`.
-/
theorem UpperTheory.V.Pa.cCount :
    ∀ (R Γ M : Type) [CommRing R] [Group Γ] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R Γ M) (c : Γ), c * c = 1 → IsUnit (2 : R) → (∀ Z : AddSubgroup (Γ → M), Finite Z → (Bl ρ).toAddSubgroup ≤ Z → (∀ z ∈ Z, ∀ g h, z (g * h) = z g + ρ g (z h)) → Nat.card Z * Nat.card {m : M // ρ c m = m} = {z | z ∈ Z ∧ z c = 0}.ncard * Nat.card M) ∧ Nat.card (Bl ρ) * Nat.card ρ.invariants = Nat.card M ∧ {z | z ∈ Bl ρ ∧ z c = 0}.ncard * Nat.card ρ.invariants = Nat.card {m : M // ρ c m = m} := by
  intro R Γ M _ _ _ _ _ ρ c hc h2
  let f : M →+ (Γ → M) :=
    { toFun := fun m g => ρ g m - m
      map_zero' := by ext g; simp
      map_add' := by intro a b; ext g; simp; abel }
  have hf : ∀ m g, f m g = ρ g m - m := fun _ _ => rfl
  have hBl : ∀ z, z ∈ Bl ρ ↔ z ∈ f.range := by
    intro z
    simp only [Bl, LinearMap.mem_range, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨m, by ext g; simp [hf]⟩
    · rintro ⟨m, rfl⟩
      exact ⟨m, by ext g; simp [hf]⟩
  have hker : ∀ m, m ∈ f.ker ↔ m ∈ ρ.invariants := by
    intro m
    rw [AddMonoidHom.mem_ker, Representation.mem_invariants]
    constructor
    · intro h g
      have := congrFun h g
      rw [hf] at this
      simpa [sub_eq_zero] using this
    · intro h
      ext g
      simp [hf, h g]
  have cardBl : Nat.card (Bl ρ) = Nat.card f.range :=
    Nat.card_congr (Equiv.subtypeEquivRight hBl)
  have cardInv : Nat.card ρ.invariants = Nat.card f.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun m => (hker m).symm))
  let d : M →+ M :=
    { toFun := fun m => ρ c m - m
      map_zero' := by simp
      map_add' := by intro a b; simp; abel }
  have hd : ∀ m, d m = ρ c m - m := fun _ => rfl
  have cardFix : Nat.card {m : M // ρ c m = m} = Nat.card d.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun m => by
      rw [AddMonoidHom.mem_ker, hd, sub_eq_zero]))
  have hdM : Nat.card d.range * Nat.card {m : M // ρ c m = m} = Nat.card M := by
    rw [cardFix, mul_comm]
    exact card_ker_mul_card_range_eq_card d
  let Mc : AddSubgroup M :=
    { carrier := {m | ρ c m = m}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        rw [map_add, ha, hb]
      zero_mem' := by simp
      neg_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        rw [map_neg, ha] }
  have cardMc : Nat.card {m : M // ρ c m = m} = Nat.card Mc :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun m => Iff.rfl))
  let f' : Mc →+ (Γ → M) := f.comp Mc.subtype
  have hf' : ∀ x, f' x = f x.1 := fun _ => rfl
  have cardKer' : Nat.card f'.ker = Nat.card ρ.invariants := by
    rw [cardInv]
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, by
          have := AddMonoidHom.mem_ker.1 x.2
          rw [hf'] at this
          exact AddMonoidHom.mem_ker.2 this⟩
        invFun := fun v => ⟨⟨v.1, ((hker _).1 v.2 |> (Representation.mem_invariants ρ _).1) c⟩, by
          apply AddMonoidHom.mem_ker.2
          rw [hf']
          exact AddMonoidHom.mem_ker.1 v.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hRange' : ∀ z, z ∈ f'.range ↔ z ∈ {z | z ∈ Bl ρ ∧ z c = 0} := by
    intro z
    simp only [Set.mem_setOf_eq, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(hBl _).2 ⟨x.1, (hf' x).symm⟩, ?_⟩
      rw [hf', hf, sub_eq_zero]
      exact x.2
    · rintro ⟨hz, hzc⟩
      obtain ⟨m, rfl⟩ := (hBl z).1 hz
      rw [hf, sub_eq_zero] at hzc
      exact ⟨⟨m, hzc⟩, rfl⟩
  have cardR' : Nat.card f'.range = {z | z ∈ Bl ρ ∧ z c = 0}.ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight hRange')
  refine ⟨?_, ?_, ?_⟩
  · intro Z _ hle hcoc
    let ev : Z →+ M :=
      { toFun := fun z => z.1 c
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hev : ∀ z, ev z = z.1 c := fun _ => rfl
    have kerEv : Nat.card ev.ker = {z | z ∈ Z ∧ z c = 0}.ncard := by
      rw [← Nat.card_coe_set_eq]
      exact Nat.card_congr
        { toFun := fun x => ⟨x.1.1, x.1.2, by
            have := AddMonoidHom.mem_ker.1 x.2
            rwa [hev] at this⟩
          invFun := fun y => ⟨⟨y.1, y.2.1⟩, AddMonoidHom.mem_ker.2 (by rw [hev]; exact y.2.2)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have rangeEv : ∀ x, x ∈ ev.range ↔ x ∈ d.range := by
      intro x
      simp only [AddMonoidHom.mem_range]
      constructor
      · rintro ⟨⟨z, hz⟩, rfl⟩
        rw [hev]
        have h1 := hcoc z hz 1 1
        simp only [mul_one, map_one, Module.End.one_apply] at h1
        have hz1 : z 1 = 0 := by
          have : z 1 + z 1 = z 1 + 0 := by rw [add_zero]; exact h1.symm
          exact add_left_cancel this
        have h2c := hcoc z hz c c
        rw [hc, hz1] at h2c
        obtain ⟨u, hu⟩ := h2
        refine ⟨-((↑u⁻¹ : R) • z c), ?_⟩
        rw [hd, map_neg, map_smul]
        have hneg : ρ c (z c) = -z c := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact h2c.symm
        rw [hneg, smul_neg, neg_neg, sub_neg_eq_add, ← add_smul]
        have : (↑u⁻¹ : R) + ↑u⁻¹ = 1 := by
          rw [← Units.inv_mul u, hu]
          ring
        rw [this, one_smul]
      · rintro ⟨m, rfl⟩
        have hmem : f m ∈ Z := hle ((Submodule.mem_toAddSubgroup _).2 ((hBl _).2 ⟨m, rfl⟩))
        refine ⟨⟨f m, hmem⟩, ?_⟩
        show f m c = d m
        rw [hf, hd]
    have cardRangeEv : Nat.card ev.range = Nat.card d.range :=
      Nat.card_congr (Equiv.subtypeEquivRight rangeEv)
    rw [← kerEv, ← card_ker_mul_card_range_eq_card ev, cardRangeEv, mul_assoc, hdM]
  · rw [cardBl, cardInv, mul_comm]
    exact card_ker_mul_card_range_eq_card f
  · rw [← cardR', ← cardKer', cardMc, mul_comm]
    exact card_ker_mul_card_range_eq_card f'
