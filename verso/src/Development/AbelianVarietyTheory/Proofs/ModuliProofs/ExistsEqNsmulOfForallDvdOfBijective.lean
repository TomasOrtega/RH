import Mathlib

namespace GlobalTheory

/- English proof (translation)
Set `g : La →ₗ[ℤ] ℤ` to `{ toFun := fun x => EF c x / N map_add' := fun x y => by`. Simplify using `only [map_add]`. Conclude with `Int.add_ediv_of_dvd_left (hc x)`. Use the proof step `map_smul' := fun r x => by`. Simplify using `only [map_smul, smul_eq_mul, RingHom.id_apply]`.

Conclude with `Int.mul_ediv_assoc r (hc x) }`. Take `⟨b, hb⟩` from `hEF.2 g`. Use `⟨b, hEF.1 ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Establish `h1 : EF b x = EF c x / N` using `by rw [hb]; rfl`.

Rewrite using `[map_nsmul, LinearMap.smul_apply, h1, nsmul_eq_mul]`. Conclude with `(Int.mul_ediv_cancel' (hc x)).symm`.
-/
theorem exists_eq_nsmul_of_forall_dvd_of_bijective {La : Type} [AddCommGroup La]
    (EF : LinearMap.BilinForm ℤ La) (hEF : Function.Bijective EF) (N : ℕ) (hN : 0 < N) (c : La)
    (hc : ∀ x, (N : ℤ) ∣ EF c x) : ∃ b, c = N • b := by
  let g : La →ₗ[ℤ] ℤ :=
    { toFun := fun x => EF c x / N
      map_add' := fun x y => by
        simp only [map_add]
        exact Int.add_ediv_of_dvd_left (hc x)
      map_smul' := fun r x => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc r (hc x) }
  obtain ⟨b, hb⟩ := hEF.2 g
  refine ⟨b, hEF.1 ?_⟩
  ext x
  have h1 : EF b x = EF c x / N := by rw [hb]; rfl
  rw [map_nsmul, LinearMap.smul_apply, h1, nsmul_eq_mul]
  exact (Int.mul_ediv_cancel' (hc x)).symm

/- English proof (translation)
Establish `: Fintype Q` using `Fintype.ofFinite Q`. Use `set V : AddSubgroup Q := ⨅ t ∈ U, (B t).ker with hV`. Establish `hmemV : ∀ x, x ∈ V ↔ ∀ t ∈ U, B t x = 0`. Introduce `x`. Simplify using `[hV, AddSubgroup.mem_iInf, AddMonoidHom.mem_ker]`.

Set `e : AddChar (ZMod N) ℂ` to `ZMod.stdAddChar`. Establish `he : ∀ z, e z = 1 → z = 0`. Introduce `z h`. Apply `ZMod.injective_stdAddChar` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `e z = e 0`.

Rewrite using `[h, AddChar.map_zero_eq_one]`. Establish `hrow : ∀ t : U, ∑ x : Q, e (B t x) = if t = 0 then (Fintype.card Q : ℂ) else 0`. Introduce `t`. Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg ht]`. Establish `hne : e.compAddMonoidHom (B t) ≠ 0`. Introduce `h`. Apply `ht` to reduce the goal to its premises.

Establish `h0 : (t : Q) = 0`. Apply `hL` to reduce the goal to its premises. Introduce `x`. Apply `he` to reduce the goal to its premises. Use `DFunLike.congr_fun h x` as an intermediate fact.

Simplify using `using this`. Conclude with `Subtype.ext h0`. Conclude with `AddChar.sum_eq_zero_iff_ne_zero.mpr hne`. Establish `hcol : ∀ x : Q, ∑ t : U, e (B t x) = if x ∈ V then (Fintype.card U : ℂ) else 0`. Introduce `x`.

Distinguish the cases in `hx : x ∈ V`. Rewrite using `[if_pos hx]`. Establish `: ∀ t : U, e (B t x) = 1`. Introduce `t`. Rewrite using `[(hmemV x).mp hx t t.2, AddChar.map_zero_eq_one]`.

Simplify using `[this]`. Rewrite using `[if_neg hx]`. Establish `hne : e.compAddMonoidHom ((B.flip x).comp U.subtype) ≠ 0`. Introduce `h`. Apply `hx` to reduce the goal to its premises.

Rewrite using `[hmemV]`. Introduce `t ht`. Apply `he` to reduce the goal to its premises. Use `DFunLike.congr_fun h ⟨t, ht⟩` as an intermediate fact. Simplify using `using this`.

Use `AddChar.sum_eq_zero_iff_ne_zero.mpr hne` as an intermediate fact. Simplify using `using this`. Establish `hA : ∑ t : U, ∑ x : Q, e (B t x) = (Fintype.card Q : ℂ)`. Rewrite using `[Fintype.sum_eq_single 0 (fun t ht => by rw [hrow t, if_neg ht])]`. Rewrite using `[hrow 0, if_pos rfl]`.

Establish `hB : ∑ t : U, ∑ x : Q, e (B t x) = (Fintype.card V : ℂ) * (Fintype.card U : ℂ)`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[hcol]`. Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]`. Use `congr 1`.

Rewrite using `[Fintype.card_subtype]`. Establish `hC : (Fintype.card U : ℂ) * (Fintype.card V : ℂ) = (Fintype.card Q : ℂ)`. Rewrite using `[← hA, hB, mul_comm]`. Rewrite using `[Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]`. Conclude with `hC` after adjusting the coercions.
-/
private theorem card_mul_card_orthogonal_eq_card_of_nondegenerate {Q : Type} [AddCommGroup Q] [Finite Q] (N : ℕ)
    [NeZero N] (B : Q →+ Q →+ ZMod N) (hL : ∀ y, (∀ x, B y x = 0) → y = 0)
    (U : AddSubgroup Q) :
    Nat.card U * Nat.card (⨅ t ∈ U, (B t).ker : AddSubgroup Q) = Nat.card Q := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  set V : AddSubgroup Q := ⨅ t ∈ U, (B t).ker with hV
  have hmemV : ∀ x, x ∈ V ↔ ∀ t ∈ U, B t x = 0 := by
    intro x; simp [hV, AddSubgroup.mem_iInf, AddMonoidHom.mem_ker]
  let e : AddChar (ZMod N) ℂ := ZMod.stdAddChar
  have he : ∀ z, e z = 1 → z = 0 := by
    intro z h
    apply ZMod.injective_stdAddChar
    change e z = e 0
    rw [h, AddChar.map_zero_eq_one]
  have hrow : ∀ t : U, ∑ x : Q, e (B t x) = if t = 0 then (Fintype.card Q : ℂ) else 0 := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simp
    · rw [if_neg ht]
      have hne : e.compAddMonoidHom (B t) ≠ 0 := by
        intro h
        apply ht
        have h0 : (t : Q) = 0 := by
          apply hL
          intro x
          apply he
          have := DFunLike.congr_fun h x
          simpa using this
        exact Subtype.ext h0
      exact AddChar.sum_eq_zero_iff_ne_zero.mpr hne
  have hcol : ∀ x : Q, ∑ t : U, e (B t x) = if x ∈ V then (Fintype.card U : ℂ) else 0 := by
    intro x
    by_cases hx : x ∈ V
    · rw [if_pos hx]
      have : ∀ t : U, e (B t x) = 1 := by
        intro t
        rw [(hmemV x).mp hx t t.2, AddChar.map_zero_eq_one]
      simp [this]
    · rw [if_neg hx]
      have hne : e.compAddMonoidHom ((B.flip x).comp U.subtype) ≠ 0 := by
        intro h
        apply hx
        rw [hmemV]
        intro t ht
        apply he
        have := DFunLike.congr_fun h ⟨t, ht⟩
        simpa using this
      have := AddChar.sum_eq_zero_iff_ne_zero.mpr hne
      simpa using this
  have hA : ∑ t : U, ∑ x : Q, e (B t x) = (Fintype.card Q : ℂ) := by
    rw [Fintype.sum_eq_single 0 (fun t ht => by rw [hrow t, if_neg ht])]
    rw [hrow 0, if_pos rfl]
  have hB : ∑ t : U, ∑ x : Q, e (B t x) = (Fintype.card V : ℂ) * (Fintype.card U : ℂ) := by
    rw [Finset.sum_comm]
    simp_rw [hcol]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [Fintype.card_subtype]
  have hC : (Fintype.card U : ℂ) * (Fintype.card V : ℂ) = (Fintype.card Q : ℂ) := by
    rw [← hA, hB, mul_comm]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact_mod_cast hC

/- English proof (translation)
Establish `hz : ∀ a a', (N : ℤ) ∣ E a a' → B (π a) (π a') = 0` using `fun a a' h => by`. Rewrite using `[← hE]`. Conclude with `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h`. Use `set S : Set Q := {q | ∃ a p, R a p ∧ π a = q} with hSdef`. Use `set ST : Set Q := {q | ∃ a p, R a p ∧ p ∈ T ∧ π a = q} with hSTdef`.

Use `set U : AddSubgroup Q := AddSubgroup.closure ST with hUdef`. Use `set V : AddSubgroup Q := ⨅ t ∈ U, (B t).ker with hVdef`. Use `set W : AddSubgroup Q := ⨅ x ∈ V, (B.flip x).ker with hWdef`. Establish `hmemV : ∀ x, x ∈ V ↔ ∀ t ∈ U, B t x = 0`. Introduce `x`.

Simplify using `[hVdef, AddSubgroup.mem_iInf]`. Establish `hmemW : ∀ y, y ∈ W ↔ ∀ x ∈ V, B y x = 0`. Introduce `y`. Simplify using `[hWdef, AddSubgroup.mem_iInf]`. Establish `h1 : Nat.card U * Nat.card V = Nat.card Q` using `card_mul_card_orthogonal_eq_card_of_nondegenerate N B hL U`.

Establish `h2 : Nat.card V * Nat.card W = Nat.card Q` using `card_mul_card_orthogonal_eq_card_of_nondegenerate N B.flip (fun x hx => hR x (fun y => by simpa using hx y)) V`. Establish `hSV : S ⊆ (V : Set Q)`. Introduce and unpack `q ⟨a', p', hr, rfl⟩`. Rewrite using `[SetLike.mem_coe, hmemV]`. Introduce `t ht`.

Establish `hle : U ≤ (B.flip (π a')).ker`. Rewrite using `[hUdef, AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨a0, p0, h0, hp0, rfl⟩`. Simplify using `only [SetLike.mem_coe, AddMonoidHom.mem_ker, AddMonoidHom.flip_apply]`. Conclude with `hz _ _ (horth a0 p0 a' p' h0 hp0 hr)`.

Simplify using `using hle ht`. Establish `hSTU : ST ⊆ (U : Set Q)` using `AddSubgroup.subset_closure`. Establish `hUW : U ≤ W`. Introduce `t ht`. Rewrite using `[hmemW]`.

Introduce `x hx`. Conclude with `(hmemV x).mp hx t ht`. Establish `hPS : Nat.card P ≤ Nat.card S`. Use `Nat.card_le_card_of_injective (fun p => ⟨π (hRsurj p).choose, (hRsurj p).choose, p, (hRsurj p).choose_spec, rfl⟩) ?_` and prove the remaining obligations. Introduce `p p' h`.

Establish `h' : π (hRsurj p).choose = π (hRsurj p').choose` using `congrArg Subtype.val h`. Take `⟨c, hc⟩` from `hπeq _ _ h'`. Use `hRinv _ c p (hRsurj p).choose_spec` as an intermediate fact. Rewrite `this` using `[← hc]`. Conclude with `hRfun _ _ _ this (hRsurj p').choose_spec`.

Establish `hTST : Nat.card T ≤ Nat.card ST`. Use `Nat.card_le_card_of_injective (fun p : T => ⟨π (hRsurj p).choose, (hRsurj p).choose, p, (hRsurj p).choose_spec, p.2, rfl⟩) ?_` and prove the remaining obligations. Introduce `p p' h`. Establish `h' : π (hRsurj p).choose = π (hRsurj p').choose` using `congrArg Subtype.val h`. Take `⟨c, hc⟩` from `hπeq _ _ h'`.

Use `hRinv _ c p (hRsurj p).choose_spec` as an intermediate fact. Rewrite `this` using `[← hc]`. Conclude with `Subtype.ext (hRfun _ _ _ this (hRsurj p').choose_spec)`. Establish `hSVc : Nat.card S ≤ Nat.card V` using `Nat.card_mono (Set.toFinite _) hSV`. Establish `hSTUc : Nat.card ST ≤ Nat.card U` using `Nat.card_mono (Set.toFinite _) hSTU`.

Establish `hUpos : 0 < Nat.card U` using `Nat.card_pos`. Establish `hVpos : 0 < Nat.card V` using `Nat.card_pos`. Establish `hQpos : 0 < Nat.card Q` using `Nat.card_pos`. Establish `hPT : Nat.card P * Nat.card T ≤ Nat.card S * Nat.card ST` using `Nat.mul_le_mul hPS hTST`. Establish `hTpos : 0 < Nat.card T`.

Break down `Nat.eq_zero_or_pos (Nat.card T) with h | h` into its components or cases. Rewrite `hcard` using `[h, mul_zero]`. Use linear arithmetic over natural numbers and integers. Conclude with `h`. Establish `hSTpos : 0 < Nat.card ST` using `lt_of_lt_of_le hTpos hTST`.

Establish `hSeq : Nat.card S = Nat.card V`. Assume the negation of the conclusion as `hne`. Establish `hlt : Nat.card S < Nat.card V` using `lt_of_le_of_ne hSVc hne`. Establish `h3 : Nat.card S * Nat.card ST < Nat.card V * Nat.card U` using `lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt hSTpos) (Nat.mul_le_mul_left _ hSTUc)`. Rewrite `h3` using `[mul_comm (Nat.card V)]`.

Use linear arithmetic over natural numbers and integers. Establish `hSpos : 0 < Nat.card S` using `by rw [hSeq]; exact hVpos`. Establish `hSTeq : Nat.card ST = Nat.card U`. Assume the negation of the conclusion as `hne`. Establish `hlt : Nat.card ST < Nat.card U` using `lt_of_le_of_ne hSTUc hne`.

Establish `h3 : Nat.card S * Nat.card ST < Nat.card V * Nat.card U`. Rewrite using `[hSeq]`. Conclude with `Nat.mul_lt_mul_of_pos_left hlt hVpos`. Rewrite `h3` using `[mul_comm (Nat.card V)]`. Use linear arithmetic over natural numbers and integers.

Establish `hSVset : S = (V : Set Q)`. Apply `Set.eq_of_subset_of_ncard_le hSV` to reduce the goal to its premises. Rewrite using `[← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]`. Conclude with `hSeq.symm.le`. Establish `hSTUset : ST = (U : Set Q)`.

Apply `Set.eq_of_subset_of_ncard_le hSTU` to reduce the goal to its premises. Rewrite using `[← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]`. Conclude with `hSTeq.symm.le`. Establish `hWU : Nat.card W ≤ Nat.card U`. Establish `: Nat.card V * Nat.card W = Nat.card V * Nat.card U` using `by rw [h2, ← h1, mul_comm]`.

Conclude with `(Nat.eq_of_mul_eq_mul_left hVpos this).le`. Establish `hUWeq : U = W` using `AddSubgroup.eq_of_le_of_card_ge hUW hWU`. Establish `haW : π a ∈ W`. Rewrite using `[hmemW]`. Introduce `x hx`.

Establish `hxS : x ∈ S` using `by rw [hSVset]; exact hx`. Take `⟨a', p', hr, rfl⟩` from `hxS`. Conclude with `hz _ _ (ha a' p' hr)`. Establish `haST : π a ∈ ST`. Rewrite using `[hSTUset, SetLike.mem_coe, hUWeq]`.

Conclude with `haW`. Take `⟨a0, p0, h0, _, he⟩` from `haST`. Take `⟨c, hc⟩` from `hπeq _ _ he`. Conclude with `⟨p0, hc ▸ hRinv a0 c p0 h0⟩`.
-/
private theorem exists_rel_of_dvd_pairing_of_card_mul_eq {La Q P : Type} [AddCommGroup La] [AddCommGroup Q]
    [Finite Q] (N : ℕ) [NeZero N] (π : La →+ Q) (B : Q →+ Q →+ ZMod N)
    (hπeq : ∀ a a', π a = π a' → ∃ c, a' = a + N • c)
    (hL : ∀ y, (∀ x, B y x = 0) → y = 0) (hR : ∀ x, (∀ y, B y x = 0) → x = 0)
    (E : La → La → ℤ) (hE : ∀ a a', ((E a a' : ℤ) : ZMod N) = B (π a) (π a'))
    (T : Set P) (R : La → P → Prop) (hRinv : ∀ a b p, R a p → R (a + N • b) p)
    (hRfun : ∀ a p p', R a p → R a p' → p = p') (hRsurj : ∀ p, ∃ a, R a p)
    (hcard : Nat.card P * Nat.card T = Nat.card Q)
    (horth : ∀ a p a' p', R a p → p ∈ T → R a' p' → (N : ℤ) ∣ E a a')
    (a : La) (ha : ∀ a' p', R a' p' → (N : ℤ) ∣ E a a') : ∃ p, R a p := by
  classical
  have hz : ∀ a a', (N : ℤ) ∣ E a a' → B (π a) (π a') = 0 := fun a a' h => by
    rw [← hE]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
  set S : Set Q := {q | ∃ a p, R a p ∧ π a = q} with hSdef
  set ST : Set Q := {q | ∃ a p, R a p ∧ p ∈ T ∧ π a = q} with hSTdef
  set U : AddSubgroup Q := AddSubgroup.closure ST with hUdef
  set V : AddSubgroup Q := ⨅ t ∈ U, (B t).ker with hVdef
  set W : AddSubgroup Q := ⨅ x ∈ V, (B.flip x).ker with hWdef
  have hmemV : ∀ x, x ∈ V ↔ ∀ t ∈ U, B t x = 0 := by
    intro x; simp [hVdef, AddSubgroup.mem_iInf]
  have hmemW : ∀ y, y ∈ W ↔ ∀ x ∈ V, B y x = 0 := by
    intro y; simp [hWdef, AddSubgroup.mem_iInf]
  have h1 : Nat.card U * Nat.card V = Nat.card Q := card_mul_card_orthogonal_eq_card_of_nondegenerate N B hL U
  have h2 : Nat.card V * Nat.card W = Nat.card Q :=
    card_mul_card_orthogonal_eq_card_of_nondegenerate N B.flip (fun x hx => hR x (fun y => by simpa using hx y)) V
  have hSV : S ⊆ (V : Set Q) := by
    rintro q ⟨a', p', hr, rfl⟩
    rw [SetLike.mem_coe, hmemV]
    intro t ht
    have hle : U ≤ (B.flip (π a')).ker := by
      rw [hUdef, AddSubgroup.closure_le]
      rintro _ ⟨a0, p0, h0, hp0, rfl⟩
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, AddMonoidHom.flip_apply]
      exact hz _ _ (horth a0 p0 a' p' h0 hp0 hr)
    simpa using hle ht
  have hSTU : ST ⊆ (U : Set Q) := AddSubgroup.subset_closure
  have hUW : U ≤ W := by
    intro t ht
    rw [hmemW]
    intro x hx
    exact (hmemV x).mp hx t ht
  have hPS : Nat.card P ≤ Nat.card S := by
    refine Nat.card_le_card_of_injective
      (fun p => ⟨π (hRsurj p).choose, (hRsurj p).choose, p, (hRsurj p).choose_spec, rfl⟩) ?_
    intro p p' h
    have h' : π (hRsurj p).choose = π (hRsurj p').choose := congrArg Subtype.val h
    obtain ⟨c, hc⟩ := hπeq _ _ h'
    have := hRinv _ c p (hRsurj p).choose_spec
    rw [← hc] at this
    exact hRfun _ _ _ this (hRsurj p').choose_spec
  have hTST : Nat.card T ≤ Nat.card ST := by
    refine Nat.card_le_card_of_injective
      (fun p : T => ⟨π (hRsurj p).choose, (hRsurj p).choose, p, (hRsurj p).choose_spec, p.2, rfl⟩) ?_
    intro p p' h
    have h' : π (hRsurj p).choose = π (hRsurj p').choose := congrArg Subtype.val h
    obtain ⟨c, hc⟩ := hπeq _ _ h'
    have := hRinv _ c p (hRsurj p).choose_spec
    rw [← hc] at this
    exact Subtype.ext (hRfun _ _ _ this (hRsurj p').choose_spec)
  have hSVc : Nat.card S ≤ Nat.card V := Nat.card_mono (Set.toFinite _) hSV
  have hSTUc : Nat.card ST ≤ Nat.card U := Nat.card_mono (Set.toFinite _) hSTU
  have hUpos : 0 < Nat.card U := Nat.card_pos
  have hVpos : 0 < Nat.card V := Nat.card_pos
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hPT : Nat.card P * Nat.card T ≤ Nat.card S * Nat.card ST := Nat.mul_le_mul hPS hTST
  have hTpos : 0 < Nat.card T := by
    rcases Nat.eq_zero_or_pos (Nat.card T) with h | h
    · rw [h, mul_zero] at hcard; omega
    · exact h
  have hSTpos : 0 < Nat.card ST := lt_of_lt_of_le hTpos hTST
  have hSeq : Nat.card S = Nat.card V := by
    by_contra hne
    have hlt : Nat.card S < Nat.card V := lt_of_le_of_ne hSVc hne
    have h3 : Nat.card S * Nat.card ST < Nat.card V * Nat.card U :=
      lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt hSTpos) (Nat.mul_le_mul_left _ hSTUc)
    rw [mul_comm (Nat.card V)] at h3
    omega
  have hSpos : 0 < Nat.card S := by rw [hSeq]; exact hVpos
  have hSTeq : Nat.card ST = Nat.card U := by
    by_contra hne
    have hlt : Nat.card ST < Nat.card U := lt_of_le_of_ne hSTUc hne
    have h3 : Nat.card S * Nat.card ST < Nat.card V * Nat.card U := by
      rw [hSeq]; exact Nat.mul_lt_mul_of_pos_left hlt hVpos
    rw [mul_comm (Nat.card V)] at h3
    omega
  have hSVset : S = (V : Set Q) := by
    apply Set.eq_of_subset_of_ncard_le hSV
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact hSeq.symm.le
  have hSTUset : ST = (U : Set Q) := by
    apply Set.eq_of_subset_of_ncard_le hSTU
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact hSTeq.symm.le
  have hWU : Nat.card W ≤ Nat.card U := by
    have : Nat.card V * Nat.card W = Nat.card V * Nat.card U := by rw [h2, ← h1, mul_comm]
    exact (Nat.eq_of_mul_eq_mul_left hVpos this).le
  have hUWeq : U = W := AddSubgroup.eq_of_le_of_card_ge hUW hWU
  have haW : π a ∈ W := by
    rw [hmemW]
    intro x hx
    have hxS : x ∈ S := by rw [hSVset]; exact hx
    obtain ⟨a', p', hr, rfl⟩ := hxS
    exact hz _ _ (ha a' p' hr)
  have haST : π a ∈ ST := by
    rw [hSTUset, SetLike.mem_coe, hUWeq]
    exact haW
  obtain ⟨a0, p0, h0, _, he⟩ := haST
  obtain ⟨c, hc⟩ := hπeq _ _ he
  exact ⟨p0, hc ▸ hRinv a0 c p0 h0⟩

/- English proof (translation)
Introduce `La _ _ _ EF hEF N hN P T R hRinv hRfun hRsurj hcard horth a ha`. Establish `: NeZero N` using `⟨hN.ne'⟩`. Set `b` to `Module.Free.chooseBasis ℤ La`. Set `M : Matrix (Module.Free.ChooseBasisIndex ℤ La) (Module.Free.ChooseBasisIndex ℤ La) (ZMod N)` to `fun i j => ((EF (b i) (b j) : ℤ) : ZMod N)`. Set `π : La →+ (Module.Free.ChooseBasisIndex ℤ La → ZMod N)` to `{ toFun := fun a i => ((b.repr a i : ℤ) : ZMod N) map_zero' := by ext i; simp map_add' := by intro x y; ext i; simp }`.

Set `B : (Module.Free.ChooseBasisIndex ℤ La → ZMod N) →+ (Module.Free.ChooseBasisIndex ℤ La → ZMod N) →+ ZMod N` to `AddMonoidHom.mk' (fun y => AddMonoidHom.mk' (fun x => dotProduct (Matrix.vecMul y M) x) (fun x x' => dotProduct_add _ _ _)) (fun y y' => by ext x; simp [Matrix.add_vecMul, add_dotProduct])`. Establish `hBapp : ∀ y x, B y x = dotProduct (Matrix.vecMul y M) x` using `fun _ _ => rfl`. Establish `hπapp : ∀ a i, π a i = ((b.repr a i : ℤ) : ZMod N)` using `fun _ _ => rfl`. Establish `hE : ∀ a a', ((EF a a' : ℤ) : ZMod N) = B (π a) (π a')`. Introduce `a a'`.

Establish `hZ : EF a a' = ∑ i, ∑ j, b.repr a i * EF (b i) (b j) * b.repr a' j`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[b.sum_repr, b.sum_repr]`. Use `_ = _ := by`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hZ, hBapp]`. Simplify using `only [Matrix.vecMul, dotProduct, hπapp, M, Int.cast_sum, Int.cast_mul, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Establish `hπN : ∀ c, π ((N : ℕ) • c) = 0`. Introduce `c`. Use extensionality with `i`. Simplify using `[hπapp]`.

Establish `hdiv : ∀ a, (∀ y, B (π a) y = 0) → ∃ c, a = N • c`. Introduce `a h`. Apply `exists_eq_nsmul_of_forall_dvd_of_bijective EF hEF N hN a` to reduce the goal to its premises. Introduce `x`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd, hE]`.

Conclude with `h _`. Establish `hsurj : ∀ y, ∃ a, π a = y`. Introduce `y`. Use `⟨b.equivFun.symm (fun i => ((y i).val : ℤ)), ?_⟩` and prove the remaining obligations. Use extensionality with `i`.

Rewrite using `[hπapp, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`. Simplify using the standard rewrite rules. Establish `hL : ∀ y, (∀ x, B y x = 0) → y = 0`. Introduce `y hy`. Take `⟨a, rfl⟩` from `hsurj y`.

Take `⟨c, rfl⟩` from `hdiv a (fun x => hy x)`. Conclude with `hπN c`. Establish `hπeq : ∀ a a', π a = π a' → ∃ c, a' = a + N • c`. Introduce `a a' h`. Take `⟨c, hc⟩` from `hdiv (a' - a) (fun y => by rw [map_sub, h, sub_self, map_zero]; rfl)`.

Conclude with `⟨c, by rw [← hc]; abel⟩`. Establish `hinj : Function.Injective (fun y => Matrix.vecMul y M)`. Introduce `y y' h`. Establish `h' : ∀ x, B (y - y') x = 0`. Introduce `x`.

Rewrite using `[hBapp, Matrix.sub_vecMul]`. Simplify using `only at h`. Rewrite using `[h, sub_self, zero_dotProduct]`. Conclude with `sub_eq_zero.mp (hL _ h')`. Establish `hsv : Function.Surjective (fun y => Matrix.vecMul y M)` using `Finite.injective_iff_surjective.mp hinj`.

Establish `hR : ∀ x, (∀ y, B y x = 0) → x = 0`. Introduce `x hx`. Use extensionality with `i`. Take `⟨y, hy⟩` from `hsv (Pi.single i 1)`. Use `hx y` as an intermediate fact.

Rewrite `this` using `[hBapp]`. Simplify using `only at hy`. Rewrite `this` using `[hy, single_dotProduct, one_mul]`. Simplify using `using this`. Establish `hQ : Nat.card (Module.Free.ChooseBasisIndex ℤ La → ZMod N) = N ^ Module.finrank ℤ La`.

Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Module.finrank_eq_card_chooseBasisIndex]`. Conclude with `exists_rel_of_dvd_pairing_of_card_mul_eq N π B hπeq hL hR (fun a a' => EF a a') hE T R hRinv hRfun hRsurj (hcard.trans hQ.symm) horth a ha`.
-/
theorem exists_rel_of_forall_dvd_of_card_mul :
    ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La), Function.Bijective EF → ∀ (N : ℕ), 0 < N → ∀ (P : Type) (T : Set P) (R : La → P → Prop), (∀ a b p, R a p → R (a + N • b) p) → (∀ a p p', R a p → R a p' → p = p') → (∀ p, ∃ a, R a p) → Nat.card P * Nat.card T = N ^ Module.finrank ℤ La → (∀ a p a' p', R a p → p ∈ T → R a' p' → (N : ℤ) ∣ EF a a') → ∀ a, (∀ a' p', R a' p' → (N : ℤ) ∣ EF a a') → ∃ p, R a p := by
  intro La _ _ _ EF hEF N hN P T R hRinv hRfun hRsurj hcard horth a ha
  classical
  have : NeZero N := ⟨hN.ne'⟩
  let b := Module.Free.chooseBasis ℤ La
  let M : Matrix (Module.Free.ChooseBasisIndex ℤ La) (Module.Free.ChooseBasisIndex ℤ La) (ZMod N) :=
    fun i j => ((EF (b i) (b j) : ℤ) : ZMod N)
  let π : La →+ (Module.Free.ChooseBasisIndex ℤ La → ZMod N) :=
    { toFun := fun a i => ((b.repr a i : ℤ) : ZMod N)
      map_zero' := by ext i; simp
      map_add' := by intro x y; ext i; simp }
  let B : (Module.Free.ChooseBasisIndex ℤ La → ZMod N) →+
      (Module.Free.ChooseBasisIndex ℤ La → ZMod N) →+ ZMod N :=
    AddMonoidHom.mk' (fun y => AddMonoidHom.mk' (fun x => dotProduct (Matrix.vecMul y M) x)
      (fun x x' => dotProduct_add _ _ _))
      (fun y y' => by ext x; simp [Matrix.add_vecMul, add_dotProduct])
  have hBapp : ∀ y x, B y x = dotProduct (Matrix.vecMul y M) x := fun _ _ => rfl
  have hπapp : ∀ a i, π a i = ((b.repr a i : ℤ) : ZMod N) := fun _ _ => rfl
  have hE : ∀ a a', ((EF a a' : ℤ) : ZMod N) = B (π a) (π a') := by
    intro a a'
    have hZ : EF a a' = ∑ i, ∑ j, b.repr a i * EF (b i) (b j) * b.repr a' j := by
      calc EF a a' = EF (∑ i, b.repr a i • b i) (∑ j, b.repr a' j • b j) := by
            rw [b.sum_repr, b.sum_repr]
        _ = _ := by
            simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
              Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
            ring
    rw [hZ, hBapp]
    simp only [Matrix.vecMul, dotProduct, hπapp, M, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hπN : ∀ c, π ((N : ℕ) • c) = 0 := by
    intro c; ext i; simp [hπapp]
  have hdiv : ∀ a, (∀ y, B (π a) y = 0) → ∃ c, a = N • c := by
    intro a h
    apply exists_eq_nsmul_of_forall_dvd_of_bijective EF hEF N hN a
    intro x
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hE]
    exact h _
  have hsurj : ∀ y, ∃ a, π a = y := by
    intro y
    refine ⟨b.equivFun.symm (fun i => ((y i).val : ℤ)), ?_⟩
    ext i
    rw [hπapp, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    simp
  have hL : ∀ y, (∀ x, B y x = 0) → y = 0 := by
    intro y hy
    obtain ⟨a, rfl⟩ := hsurj y
    obtain ⟨c, rfl⟩ := hdiv a (fun x => hy x)
    exact hπN c
  have hπeq : ∀ a a', π a = π a' → ∃ c, a' = a + N • c := by
    intro a a' h
    obtain ⟨c, hc⟩ := hdiv (a' - a) (fun y => by rw [map_sub, h, sub_self, map_zero]; rfl)
    exact ⟨c, by rw [← hc]; abel⟩
  have hinj : Function.Injective (fun y => Matrix.vecMul y M) := by
    intro y y' h
    have h' : ∀ x, B (y - y') x = 0 := by
      intro x
      rw [hBapp, Matrix.sub_vecMul]
      simp only at h
      rw [h, sub_self, zero_dotProduct]
    exact sub_eq_zero.mp (hL _ h')
  have hsv : Function.Surjective (fun y => Matrix.vecMul y M) := Finite.injective_iff_surjective.mp hinj
  have hR : ∀ x, (∀ y, B y x = 0) → x = 0 := by
    intro x hx
    ext i
    obtain ⟨y, hy⟩ := hsv (Pi.single i 1)
    have := hx y
    rw [hBapp] at this
    simp only at hy
    rw [hy, single_dotProduct, one_mul] at this
    simpa using this
  have hQ : Nat.card (Module.Free.ChooseBasisIndex ℤ La → ZMod N) = N ^ Module.finrank ℤ La := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
      Module.finrank_eq_card_chooseBasisIndex]
  exact exists_rel_of_dvd_pairing_of_card_mul_eq N π B hπeq hL hR (fun a a' => EF a a') hE T R hRinv hRfun hRsurj
    (hcard.trans hQ.symm) horth a ha

end GlobalTheory
