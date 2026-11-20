import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

/- English proof (translation)
Establish `h1 : D.gI v = (D.a : ℤ) • v`. Establish `h` using `hv`. Simplify using `only [Dat.delI, LinearMap.sub_apply, sub_eq_zero] at h`. Rewrite using `[h]`. Simplify using the standard rewrite rules.

Establish `hp : ∀ k : ℕ, (D.gI ^ k) v = ((D.a : ℤ) ^ k) • v`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Rewrite using `[pow_succ, Module.End.mul_apply, h1, map_zsmul, ih, smul_smul, pow_succ, mul_comm]`. Establish `hn` using `hp D.n`. Rewrite `hn` using `[D.gI_pow]`. Express the relevant statement in the definitionally equal form `v = _ at hn`. Apply `D.tf ((D.a : ℤ) ^ D.n - 1) v` to reduce the goal to its premises.

Establish `h2 : (1 : ℤ) < (D.a : ℤ) ^ D.n` using `one_lt_pow₀ (by have := D.two_le; omega) D.n_pos.ne'`. Use linear arithmetic over natural numbers and integers. Rewrite using `[sub_smul, one_smul, ← hn, sub_self]`.
-/
private theorem selInj_delI_inj {Y I : Type} [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I)
    (v : I) (hv : D.delI v = 0) : v = 0 := by
  have h1 : D.gI v = (D.a : ℤ) • v := by
    have h := hv
    simp only [Dat.delI, LinearMap.sub_apply, sub_eq_zero] at h
    rw [h]
    simp
  have hp : ∀ k : ℕ, (D.gI ^ k) v = ((D.a : ℤ) ^ k) • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, h1, map_zsmul, ih, smul_smul, pow_succ, mul_comm]
  have hn := hp D.n
  rw [D.gI_pow] at hn
  change v = _ at hn
  apply D.tf ((D.a : ℤ) ^ D.n - 1) v
  · have h2 : (1 : ℤ) < (D.a : ℤ) ^ D.n := one_lt_pow₀ (by have := D.two_le; omega) D.n_pos.ne'
    omega
  · rw [sub_smul, one_smul, ← hn, sub_self]

/- English proof (translation)
Rewrite using `[Submodule.mem_torsion_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨m, hm⟩, h⟩`. Conclude with `⟨m, nonZeroDivisors.ne_zero hm, h⟩`. Introduce and unpack `⟨m, hm, h⟩`.

Conclude with `⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩, h⟩`.
-/
private theorem selInj_tors_iff {Y : Type} [AddCommGroup Y] (t : Y) :
    t ∈ Submodule.torsion ℤ Y ↔ ∃ m : ℤ, m ≠ 0 ∧ m • t = 0 := by
  rw [Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨⟨m, hm⟩, h⟩
    exact ⟨m, nonZeroDivisors.ne_zero hm, h⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩, h⟩

/- English proof (translation)
Simplify using `only [Ct.mt, Submodule.mem_sup, LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨z, rfl⟩, t, ht, h⟩`. Conclude with `⟨z, t, ht, by simpa using h⟩`. Introduce and unpack `⟨z, t, ht, h⟩`.

Conclude with `⟨_, ⟨z, rfl⟩, t, ht, by simpa using h⟩`.
-/
private theorem selInj_mem_mt {Y : Type} [AddCommGroup Y] (l : ℕ) (x : Y) :
    x ∈ mt Y l ↔ ∃ z : Y, ∃ t ∈ Submodule.torsion ℤ Y, (l : ℤ) • z + t = x := by
  simp only [Ct.mt, Submodule.mem_sup, LinearMap.mem_range]
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, t, ht, h⟩
    exact ⟨z, t, ht, by simpa using h⟩
  · rintro ⟨z, t, ht, h⟩
    exact ⟨_, ⟨z, rfl⟩, t, ht, by simpa using h⟩

/- English proof (translation)
Introduce `Y I _ _ D l hl hl0 hfin`. Establish `hdel_apply : ∀ y, D.del y = D.g y - (D.a : ℤ) • y`. Introduce `y`. Simplify using `[Dat.del]`. Establish `hdelI_apply : ∀ v, D.delI v = D.gI v - (D.a : ℤ) • v`.

Introduce `v`. Simplify using `[Dat.delI]`. Establish `htor : ∀ {y : Y} (m : ℤ), m ≠ 0 → m • y ∈ Submodule.torsion ℤ Y → y ∈ Submodule.torsion ℤ Y`. Introduce `y m hm h`. Take `⟨m', hm', h'⟩` from `(selInj_tors_iff _).1 h`.

Conclude with `(selInj_tors_iff y).2 ⟨m' * m, mul_ne_zero hm' hm, by rw [mul_smul, h']⟩`. Establish `hdt : ∀ t ∈ Submodule.torsion ℤ Y, D.d t = 0`. Introduce `t ht`. Take `⟨m, hm, h⟩` from `(selInj_tors_iff t).1 ht`. Conclude with `D.tf m _ hm (by rw [← map_zsmul, h, map_zero])`.

Establish `hdd : ∀ y, D.d (D.del y) = D.delI (D.d y)`. Introduce `y`. Rewrite using `[hdel_apply, hdelI_apply, map_sub, map_zsmul, D.comm]`. Establish `hdelt : ∀ t ∈ Submodule.torsion ℤ Y, D.del t ∈ Submodule.torsion ℤ Y`. Introduce `t ht`.

Take `⟨m, hm, h⟩` from `(selInj_tors_iff t).1 ht`. Conclude with `(selInj_tors_iff _).2 ⟨m, hm, by rw [← map_zsmul, h, map_zero]⟩`. Establish `key : ∀ w : {w : D.W // (l : ℤ) • w = 0}, ∃ u : D.U, Submodule.Quotient.mk u = w.1 ∧ ∃ y : Y, ∃ t ∈ Submodule.torsion ℤ Y, (l : ℤ) • (u : Y) = D.del y + t`. Introduce and unpack `⟨w, hw⟩`. Take `⟨u, rfl⟩` from `Submodule.Quotient.mk_surjective _ w`.

Use `⟨u, rfl, ?_⟩` and prove the remaining obligations. Rewrite `hw` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Establish `hw' : (l : ℤ) • (u : Y) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y` using `hw`. Take `⟨a', ⟨y, rfl⟩, t, ht, h⟩` from `Submodule.mem_sup.1 hw'`. Conclude with `⟨y, t, ht, h.symm⟩`.

Use `choose u hu y t ht hyt using key`. Establish `hsel : ∀ w, (Submodule.Quotient.mk (y w) : Y ⧸ Ct.mt Y l) ∈ D.SelInv l`. Introduce `w`. Take `⟨c, hc⟩` from `hl`. Use `⟨y w, rfl, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[selInj_mem_mt]`. Use `⟨(u w : Y) + c • y w, -t w, neg_mem (ht w), ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, hyt w, hdel_apply, smul_smul, ← hc, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws. Take `⟨i, hi⟩` from `(u w).2`.

Use `⟨i, ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg D.d (hyt w)`. Rewrite `e` using `[map_zsmul, map_add, hdt _ (ht w), add_zero, hdd, ← hi]`. Rewrite using `[← sub_eq_zero]`. Apply `selInj_delI_inj D` to reduce the goal to its premises.

Rewrite using `[map_sub, map_zsmul, ← e, sub_self]`. Set `f : {w : D.W // (l : ℤ) • w = 0} → D.SelInv l` to `fun w => ⟨_, hsel w⟩`. Apply `Nat.card_le_card_of_injective f` to reduce the goal to its premises. Introduce `w w' hww`. Establish `hq : (Submodule.Quotient.mk (y w) : Y ⧸ Ct.mt Y l) = Submodule.Quotient.mk (y w')` using `congrArg Subtype.val hww`.

Rewrite `hq` using `[Submodule.Quotient.eq, selInj_mem_mt]`. Take `⟨z, t0, ht0, hz⟩` from `hq`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hu w, ← hu w', Submodule.Quotient.eq]`. Use `show ((u w : Y) - (u w' : Y)) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y`.

Establish `e2 : D.del (y w) - D.del (y w') = (l : ℤ) • D.del z + D.del t0`. Rewrite using `[← map_sub, ← hz, map_add, map_zsmul]`. Establish `hs : (u w : Y) - u w' - D.del z ∈ Submodule.torsion ℤ Y`. Use `htor (l : ℤ) (by exact_mod_cast hl0.ne') ?_` and prove the remaining obligations. Establish `e : (l : ℤ) • ((u w : Y) - u w' - D.del z) = D.del t0 + (t w - t w')`.

Rewrite using `[smul_sub, smul_sub, hyt w, hyt w', show D.del (y w) = (l : ℤ) • D.del z + D.del t0 + D.del (y w') by rw [← e2]; abel]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `add_mem (hdelt t0 ht0) (sub_mem (ht w) (ht w'))`. Rewrite using `[show (u w : Y) - u w' = D.del z + ((u w : Y) - u w' - D.del z) by abel]`.

Conclude with `Submodule.add_mem_sup (LinearMap.mem_range_self _ _) hs`.
-/
theorem UpperTheory.V.ZK.Ct.selInj :
    ∀ (Y I : Type) [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I), ∀ l : ℕ, (l : ℤ) ∣ (D.a : ℤ) - 1 → 0 < l → Finite (D.SelInv l) → Nat.card {w : D.W // (l : ℤ) • w = 0} ≤ Nat.card (D.SelInv l) := by
  intro Y I _ _ D l hl hl0 hfin
  have hdel_apply : ∀ y, D.del y = D.g y - (D.a : ℤ) • y := by
    intro y
    simp [Dat.del]
  have hdelI_apply : ∀ v, D.delI v = D.gI v - (D.a : ℤ) • v := by
    intro v
    simp [Dat.delI]
  have htor : ∀ {y : Y} (m : ℤ), m ≠ 0 → m • y ∈ Submodule.torsion ℤ Y → y ∈ Submodule.torsion ℤ Y := by
    intro y m hm h
    obtain ⟨m', hm', h'⟩ := (selInj_tors_iff _).1 h
    exact (selInj_tors_iff y).2 ⟨m' * m, mul_ne_zero hm' hm, by rw [mul_smul, h']⟩
  have hdt : ∀ t ∈ Submodule.torsion ℤ Y, D.d t = 0 := by
    intro t ht
    obtain ⟨m, hm, h⟩ := (selInj_tors_iff t).1 ht
    exact D.tf m _ hm (by rw [← map_zsmul, h, map_zero])
  have hdd : ∀ y, D.d (D.del y) = D.delI (D.d y) := by
    intro y
    rw [hdel_apply, hdelI_apply, map_sub, map_zsmul, D.comm]
  have hdelt : ∀ t ∈ Submodule.torsion ℤ Y, D.del t ∈ Submodule.torsion ℤ Y := by
    intro t ht
    obtain ⟨m, hm, h⟩ := (selInj_tors_iff t).1 ht
    exact (selInj_tors_iff _).2 ⟨m, hm, by rw [← map_zsmul, h, map_zero]⟩
  have key : ∀ w : {w : D.W // (l : ℤ) • w = 0}, ∃ u : D.U, Submodule.Quotient.mk u = w.1 ∧
      ∃ y : Y, ∃ t ∈ Submodule.torsion ℤ Y, (l : ℤ) • (u : Y) = D.del y + t := by
    rintro ⟨w, hw⟩
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    refine ⟨u, rfl, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hw
    have hw' : (l : ℤ) • (u : Y) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y := hw
    obtain ⟨a', ⟨y, rfl⟩, t, ht, h⟩ := Submodule.mem_sup.1 hw'
    exact ⟨y, t, ht, h.symm⟩
  choose u hu y t ht hyt using key
  have hsel : ∀ w, (Submodule.Quotient.mk (y w) : Y ⧸ Ct.mt Y l) ∈ D.SelInv l := by
    intro w
    obtain ⟨c, hc⟩ := hl
    refine ⟨y w, rfl, ?_, ?_⟩
    · rw [selInj_mem_mt]
      refine ⟨(u w : Y) + c • y w, -t w, neg_mem (ht w), ?_⟩
      rw [smul_add, hyt w, hdel_apply, smul_smul, ← hc, sub_smul, one_smul]
      abel
    · obtain ⟨i, hi⟩ := (u w).2
      refine ⟨i, ?_⟩
      have e := congrArg D.d (hyt w)
      rw [map_zsmul, map_add, hdt _ (ht w), add_zero, hdd, ← hi] at e
      rw [← sub_eq_zero]
      apply selInj_delI_inj D
      rw [map_sub, map_zsmul, ← e, sub_self]
  let f : {w : D.W // (l : ℤ) • w = 0} → D.SelInv l := fun w => ⟨_, hsel w⟩
  apply Nat.card_le_card_of_injective f
  intro w w' hww
  have hq : (Submodule.Quotient.mk (y w) : Y ⧸ Ct.mt Y l) = Submodule.Quotient.mk (y w') :=
    congrArg Subtype.val hww
  rw [Submodule.Quotient.eq, selInj_mem_mt] at hq
  obtain ⟨z, t0, ht0, hz⟩ := hq
  apply Subtype.ext
  rw [← hu w, ← hu w', Submodule.Quotient.eq]
  show ((u w : Y) - (u w' : Y)) ∈ LinearMap.range D.del ⊔ Submodule.torsion ℤ Y
  have e2 : D.del (y w) - D.del (y w') = (l : ℤ) • D.del z + D.del t0 := by
    rw [← map_sub, ← hz, map_add, map_zsmul]
  have hs : (u w : Y) - u w' - D.del z ∈ Submodule.torsion ℤ Y := by
    refine htor (l : ℤ) (by exact_mod_cast hl0.ne') ?_
    have e : (l : ℤ) • ((u w : Y) - u w' - D.del z) = D.del t0 + (t w - t w') := by
      rw [smul_sub, smul_sub, hyt w, hyt w',
        show D.del (y w) = (l : ℤ) • D.del z + D.del t0 + D.del (y w') by rw [← e2]; abel]
      abel
    rw [e]
    exact add_mem (hdelt t0 ht0) (sub_mem (ht w) (ht w'))
  rw [show (u w : Y) - u w' = D.del z + ((u w : Y) - u w' - D.del z) by abel]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) hs
