import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

open UpperTheory.V.FW

/- English proof (translation)
Introduce `C _ _ J hJ`. Establish `hcard : ∀ {G H : Type} [Group G] [Group H] (f : G →* H), Nat.card G = Nat.card f.ker * Nat.card f.range`. Introduce `G H _ _ f`. Rewrite using `[← f.ker.card_mul_index, Subgroup.index_ker]`. Use `set T := torK C 2 with hT`.

Use `set D := difR J with hD`. Use `set K := minK J with hK`. Establish `memT : ∀ x : C, x ∈ T ↔ x ^ 2 = 1` using `fun x => by simp [hT, torK]`. Establish `memK : ∀ x : C, x ∈ K ↔ J x * x = 1` using `fun x => by simp [hK, minK]`. Establish `memD : ∀ x : C, x ∈ D ↔ ∃ y, y / J y = x` using `fun x => by simp [hD, difR]`.

Establish `hDK : D ≤ K`. Introduce `x hx`. Take `⟨y, rfl⟩` from `(memD x).1 hx`. Rewrite using `[memK, map_div, hJ, div_mul_div_comm, mul_comm (J y) y, div_self']`. Establish `h1 : (powR C 2).index = Nat.card T`.

Establish `e1` using `hcard (powMonoidHom 2 : C →* C)`. Establish `e2` using `(powR C 2).card_mul_index`. Establish `hpos : 0 < Nat.card (powR C 2)` using `Nat.card_pos`. Establish `e3 : Nat.card (powR C 2) * (powR C 2).index = Nat.card (powR C 2) * Nat.card T`. Rewrite using `[e2, mul_comm]`.

Conclude with `e1`. Conclude with `Nat.eq_of_mul_eq_mul_left hpos e3`. Set `g : T →* C` to `(MonoidHom.id C / J).comp T.subtype`. Establish `e4` using `hcard g`. Establish `r1 : Nat.card g.range ≤ Nat.card (D ⊓ T : Subgroup C)`.

Apply `Subgroup.card_le_of_le` to reduce the goal to its premises. Introduce and unpack `_ ⟨t, rfl⟩`. Establish `gt : g t = t.1 / J t.1` using `rfl`. Rewrite using `[gt, Subgroup.mem_inf]`. Use `⟨(memD _).2 ⟨t.1, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[memT, div_pow, ← map_pow, (memT _).1 t.2, map_one, div_one]`. Establish `r2 : Nat.card g.ker ≤ Nat.card (K ⊓ T : Subgroup C)`. Establish `hm : ∀ x : g.ker, (x.1.1 : C) ∈ K ⊓ T`. Introduce `x`. Establish `hx : g x.1 = 1` using `MonoidHom.mem_ker.1 x.2`.

Establish `hT' : x.1.1 ^ 2 = 1` using `(memT _).1 x.1.2`. Establish `hd : x.1.1 / J x.1.1 = 1` using `hx`. Establish `hJx : J x.1.1 = x.1.1` using `(div_eq_one.1 hd).symm`. Use `Subgroup.mem_inf.2 ⟨(memK _).2 ?_, x.1.2⟩` and prove the remaining obligations. Rewrite using `[hJx, ← pow_two, hT']`.

Use `Nat.card_le_card_of_injective (fun x => (⟨x.1.1, hm x⟩ : (K ⊓ T : Subgroup C))) ?_` and prove the remaining obligations. Introduce `a b hab`. Establish `hab'` using `congrArg Subtype.val hab`. Simplify using `only at hab'`. Conclude with `Subtype.ext (Subtype.ext hab')`.

Set `incl : (K ⊓ T : Subgroup C) →* K` to `Subgroup.inclusion inf_le_left`. Set `h : (K ⊓ T : Subgroup C) →* K ⧸ D.subgroupOf K` to `(QuotientGroup.mk' (D.subgroupOf K)).comp incl`. Establish `e5` using `hcard h`. Establish `r3 : Nat.card h.range ≤ D.relIndex K` using `le_of_le_of_eq (Subgroup.card_le_card_group _) rfl`. Establish `r4 : Nat.card h.ker ≤ Nat.card (D ⊓ T : Subgroup C)`.

Establish `hm : ∀ x : h.ker, (x.1.1 : C) ∈ D ⊓ T`. Introduce `x`. Establish `hx : h x.1 = 1` using `MonoidHom.mem_ker.1 x.2`. Establish `hx2 : incl x.1 ∈ D.subgroupOf K` using `(QuotientGroup.eq_one_iff _).1 hx`. Use `Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hx2, (Subgroup.mem_inf.1 x.1.2).2⟩` and prove the remaining obligations.

Use `Nat.card_le_card_of_injective (fun x => (⟨x.1.1, hm x⟩ : (D ⊓ T : Subgroup C))) ?_` and prove the remaining obligations. Introduce `a b hab`. Establish `hab'` using `congrArg Subtype.val hab`. Simplify using `only at hab'`. Conclude with `Subtype.ext (Subtype.ext hab')`.

Rewrite using `[h1]`. Use `set r := D.relIndex K`. Use `set d := Nat.card (D ⊓ T : Subgroup C)`. Establish `s1 : Nat.card T ≤ (r * d) * d`. Rewrite using `[e4]`.

Apply `Nat.mul_le_mul _ r1` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `s2 : (r * d) * d ≤ (r * d) ^ 2`. Break down `Nat.eq_zero_or_pos r with hr | hr` into its components or cases. Simplify using `[hr]`.

Rewrite using `[pow_two]`. Conclude with `Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left d hr)`. Conclude with `s1.trans s2`.
-/
theorem UpperTheory.V.FW.pTwo :
    ∀ (C : Type) [CommGroup C] [Finite C] (J : C →* C), (∀ x, J (J x) = x) → (powR C 2).index ≤ ((difR J).relIndex (minK J) * Nat.card (difR J ⊓ torK C 2 : Subgroup C)) ^ 2 := by
  intro C _ _ J hJ
  classical
  have hcard : ∀ {G H : Type} [Group G] [Group H] (f : G →* H),
      Nat.card G = Nat.card f.ker * Nat.card f.range := by
    intro G H _ _ f
    rw [← f.ker.card_mul_index, Subgroup.index_ker]
  set T := torK C 2 with hT
  set D := difR J with hD
  set K := minK J with hK
  have memT : ∀ x : C, x ∈ T ↔ x ^ 2 = 1 := fun x => by simp [hT, torK]
  have memK : ∀ x : C, x ∈ K ↔ J x * x = 1 := fun x => by simp [hK, minK]
  have memD : ∀ x : C, x ∈ D ↔ ∃ y, y / J y = x := fun x => by simp [hD, difR]
  have hDK : D ≤ K := by
    intro x hx
    obtain ⟨y, rfl⟩ := (memD x).1 hx
    rw [memK, map_div, hJ, div_mul_div_comm, mul_comm (J y) y, div_self']
  have h1 : (powR C 2).index = Nat.card T := by
    have e1 := hcard (powMonoidHom 2 : C →* C)
    have e2 := (powR C 2).card_mul_index
    have hpos : 0 < Nat.card (powR C 2) := Nat.card_pos
    have e3 : Nat.card (powR C 2) * (powR C 2).index = Nat.card (powR C 2) * Nat.card T := by
      rw [e2, mul_comm]
      exact e1
    exact Nat.eq_of_mul_eq_mul_left hpos e3
  let g : T →* C := (MonoidHom.id C / J).comp T.subtype
  have e4 := hcard g
  have r1 : Nat.card g.range ≤ Nat.card (D ⊓ T : Subgroup C) := by
    apply Subgroup.card_le_of_le
    rintro _ ⟨t, rfl⟩
    have gt : g t = t.1 / J t.1 := rfl
    rw [gt, Subgroup.mem_inf]
    refine ⟨(memD _).2 ⟨t.1, rfl⟩, ?_⟩
    rw [memT, div_pow, ← map_pow, (memT _).1 t.2, map_one, div_one]
  have r2 : Nat.card g.ker ≤ Nat.card (K ⊓ T : Subgroup C) := by
    have hm : ∀ x : g.ker, (x.1.1 : C) ∈ K ⊓ T := by
      intro x
      have hx : g x.1 = 1 := MonoidHom.mem_ker.1 x.2
      have hT' : x.1.1 ^ 2 = 1 := (memT _).1 x.1.2
      have hd : x.1.1 / J x.1.1 = 1 := hx
      have hJx : J x.1.1 = x.1.1 := (div_eq_one.1 hd).symm
      refine Subgroup.mem_inf.2 ⟨(memK _).2 ?_, x.1.2⟩
      rw [hJx, ← pow_two, hT']
    refine Nat.card_le_card_of_injective (fun x => (⟨x.1.1, hm x⟩ : (K ⊓ T : Subgroup C))) ?_
    intro a b hab
    have hab' := congrArg Subtype.val hab
    simp only at hab'
    exact Subtype.ext (Subtype.ext hab')
  let incl : (K ⊓ T : Subgroup C) →* K := Subgroup.inclusion inf_le_left
  let h : (K ⊓ T : Subgroup C) →* K ⧸ D.subgroupOf K := (QuotientGroup.mk' (D.subgroupOf K)).comp incl
  have e5 := hcard h
  have r3 : Nat.card h.range ≤ D.relIndex K :=
    le_of_le_of_eq (Subgroup.card_le_card_group _) rfl
  have r4 : Nat.card h.ker ≤ Nat.card (D ⊓ T : Subgroup C) := by
    have hm : ∀ x : h.ker, (x.1.1 : C) ∈ D ⊓ T := by
      intro x
      have hx : h x.1 = 1 := MonoidHom.mem_ker.1 x.2
      have hx2 : incl x.1 ∈ D.subgroupOf K := (QuotientGroup.eq_one_iff _).1 hx
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hx2, (Subgroup.mem_inf.1 x.1.2).2⟩
    refine Nat.card_le_card_of_injective (fun x => (⟨x.1.1, hm x⟩ : (D ⊓ T : Subgroup C))) ?_
    intro a b hab
    have hab' := congrArg Subtype.val hab
    simp only at hab'
    exact Subtype.ext (Subtype.ext hab')
  rw [h1]
  set r := D.relIndex K
  set d := Nat.card (D ⊓ T : Subgroup C)
  have s1 : Nat.card T ≤ (r * d) * d := by
    rw [e4]
    apply Nat.mul_le_mul _ r1
    calc Nat.card g.ker ≤ Nat.card (K ⊓ T : Subgroup C) := r2
      _ = Nat.card h.ker * Nat.card h.range := e5
      _ ≤ d * r := Nat.mul_le_mul r4 r3
      _ = r * d := mul_comm _ _
  have s2 : (r * d) * d ≤ (r * d) ^ 2 := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · simp [hr]
    · rw [pow_two]
      exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left d hr)
  exact s1.trans s2
