import Formalism.HyperbolicPlaceProducts.Statement
import Mathlib

namespace Formalism.SLP.P

open AddSubgroup

/- English proof (translation)
Establish `hker : (AddMonoidHom.snd ℤ A).ker = (AddMonoidHom.inl ℤ A).range`. Use extensionality with `⟨x, y⟩`. Rewrite using `[AddMonoidHom.mem_ker, AddMonoidHom.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `⟨x, ?_⟩` and prove the remaining obligations. Simplify using `at h`. Simplify using `[h]`. Introduce and unpack `⟨z, hz⟩`. Simplify using `[← hz]`.

Establish `hr : (AddMonoidHom.snd ℤ A).range = ⊤` using `AddMonoidHom.range_eq_top.mpr (fun y => ⟨(0, y), rfl⟩)`. Rewrite using `[index_map, hr, index_top, mul_one, index_comap, ← hker, ← relIndex_sup_left (K := H) (H := (AddMonoidHom.snd ℤ A).ker), relIndex_mul_index le_sup_left]`.
-/
lemma index_prod_eq {A : Type*} [AddCommGroup A] (H : AddSubgroup (ℤ × A)) :
    H.index = (H.comap (AddMonoidHom.inl ℤ A)).index *
      (H.map (AddMonoidHom.snd ℤ A)).index := by
  have hker : (AddMonoidHom.snd ℤ A).ker = (AddMonoidHom.inl ℤ A).range := by
    ext ⟨x, y⟩
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    constructor
    · intro h
      refine ⟨x, ?_⟩
      simp at h
      simp [h]
    · rintro ⟨z, hz⟩
      simp [← hz]
  have hr : (AddMonoidHom.snd ℤ A).range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr (fun y => ⟨(0, y), rfl⟩)
  rw [index_map, hr, index_top, mul_one, index_comap, ← hker,
    ← relIndex_sup_left (K := H) (H := (AddMonoidHom.snd ℤ A).ker),
    relIndex_mul_index le_sup_left]

/- English proof (translation)
Take `⟨a, rfl⟩` from `Int.subgroup_cyclic D`. Rewrite using `[← zmultiples_eq_closure, Int.index_zmultiples, Int.zmultiples_natAbs]`.
-/
lemma eq_zmultiples_index (D : AddSubgroup ℤ) : D = zmultiples (D.index : ℤ) := by
  obtain ⟨a, rfl⟩ := Int.subgroup_cyclic D
  rw [← zmultiples_eq_closure, Int.index_zmultiples, Int.zmultiples_natAbs]

/- English proof (translation)
Introduce `h hh`. Establish `hle : H₁.map (AddMonoidHom.snd ℤ A) ≤ (H₁ ⊓ H₂).map (AddMonoidHom.snd ℤ A)`. Rewrite using `[← hv, closure_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Take `⟨x, hx⟩` from `hlift i`.

Conclude with `⟨(x, v i), hx, rfl⟩`. Take `⟨t, ht, hts⟩` from `hle ⟨h, hh, rfl⟩`. Establish `hts' : t.2 = h.2` using `hts`. Establish `h1 : (h.1 - t.1, (0 : A)) ∈ H₁`. Establish `hm : h - t ∈ H₁` using `H₁.sub_mem hh ht.1`.

Establish `he : h - t = (h.1 - t.1, (0 : A))`. Use `ext`. Both sides reduce to the same expression. Simplify using `[hts']`. Rewrite `hm` using `[he]`. Then use the resulting hypothesis.

Establish `h2 : (h.1 - t.1, (0 : A)) ∈ H₂` using `hk h1`. Establish `he : h = (h.1 - t.1, (0 : A)) + t`. Use `ext`. Simplify using the standard rewrite rules. Simplify using `[hts']`.

Rewrite using `[he]`. Conclude with `H₂.add_mem h2 ht.2`.
-/
lemma le_of_lifts {A : Type*} [AddCommGroup A] {H₁ H₂ : AddSubgroup (ℤ × A)} {ι : Type*}
    (v : ι → A) (hv : AddSubgroup.closure (Set.range v) = H₁.map (AddMonoidHom.snd ℤ A))
    (hk : H₁.comap (AddMonoidHom.inl ℤ A) ≤ H₂.comap (AddMonoidHom.inl ℤ A))
    (hlift : ∀ i, ∃ x : ℤ, (x, v i) ∈ H₁ ⊓ H₂) : H₁ ≤ H₂ := by
  intro h hh
  have hle : H₁.map (AddMonoidHom.snd ℤ A) ≤ (H₁ ⊓ H₂).map (AddMonoidHom.snd ℤ A) := by
    rw [← hv, closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨x, hx⟩ := hlift i
    exact ⟨(x, v i), hx, rfl⟩
  obtain ⟨t, ht, hts⟩ := hle ⟨h, hh, rfl⟩
  have hts' : t.2 = h.2 := hts
  have h1 : (h.1 - t.1, (0 : A)) ∈ H₁ := by
    have hm : h - t ∈ H₁ := H₁.sub_mem hh ht.1
    have he : h - t = (h.1 - t.1, (0 : A)) := by
      ext
      · rfl
      · simp [hts']
    rwa [he] at hm
  have h2 : (h.1 - t.1, (0 : A)) ∈ H₂ := hk h1
  have he : h = (h.1 - t.1, (0 : A)) + t := by
    ext
    · simp
    · simp [hts']
  rw [he]
  exact H₂.add_mem h2 ht.2

/- English proof (translation)
Introduce `j hj`. Use `choose V hV using hgen`. Use `set S := {H : AddSubgroup (ℤ × A) | H.index = j} with hS`. Set `dd : AddSubgroup (ℤ × A) → ℕ` to `fun H => (H.comap (AddMonoidHom.inl ℤ A)).index`. Set `cc : AddSubgroup (ℤ × A) → Fin n → ℤ` to `fun H i => if h : ∃ x : ℤ, (x, V (H.map (AddMonoidHom.snd ℤ A)) i) ∈ H then h.choose % (dd H : ℤ) else 0`.

Set `F : AddSubgroup (ℤ × A) → ℕ × AddSubgroup A × (Fin n → ℤ)` to `fun H => (dd H, H.map (AddMonoidHom.snd ℤ A), cc H)`. Set `cube : ℕ → Finset (Fin n → ℤ)` to `fun d => Fintype.piFinset fun _ => Finset.Ico (0 : ℤ) d`. Set `T : Set (ℕ × AddSubgroup A × (Fin n → ℤ))` to `⋃ d ∈ j.divisors, ({d} : Set ℕ) ×ˢ ({H : AddSubgroup A | H.index = j / d} ×ˢ (cube d : Set (Fin n → ℤ)))`. Establish `hpos : ∀ H ∈ S, 0 < dd H ∧ H.index = dd H * (H.map (AddMonoidHom.snd ℤ A)).index`. Introduce `H hH`.

Establish `hp` using `index_prod_eq H`. Use `⟨Nat.pos_of_ne_zero fun h0 => ?_, hp⟩` and prove the remaining obligations. Establish `: H.index = j` using `hH`. Simplify using `only [dd] at h0`. Rewrite `hp` using `[h0, zero_mul]`.

Use linear arithmetic over natural numbers and integers. Establish `hmaps : ∀ H ∈ S, F H ∈ T`. Introduce `H hH`. Take `⟨hd, hp⟩` from `hpos H hH`. Establish `hHj : H.index = j` using `hH`.

Simplify using `only [T, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]`. Use `⟨dd H, Nat.mem_divisors.mpr ⟨⟨_, hHj ▸ hp⟩, by omega⟩, rfl, ?_, ?_⟩` and prove the remaining obligations. Use `show (H.map (AddMonoidHom.snd ℤ A)).index = j / dd H`. Rewrite using `[← hHj, hp, Nat.mul_div_cancel_left _ hd]`. Simplify using `only [cube]`.

Rewrite using `[Finset.mem_coe, Fintype.mem_piFinset]`. Introduce `i`. Simplify using `only [F, cc, Finset.mem_Ico]`. Establish `hd' : (0 : ℤ) < (dd H : ℤ)` using `by exact_mod_cast hd`. Use `split_ifs`.

Conclude with `⟨Int.emod_nonneg _ hd'.ne', Int.emod_lt_of_pos _ hd'⟩`. Conclude with `⟨le_rfl, hd'⟩`. Establish `hinj : Set.InjOn F S`. Introduce `H₁ hH₁ H₂ hH₂ hF`. Simplify using `only [F, Prod.mk.injEq] at hF`.

Take `⟨hd, hm, hc⟩` from `hF`. Establish `hD₁` using `eq_zmultiples_index (H₁.comap (AddMonoidHom.inl ℤ A))`. Establish `hD₂` using `eq_zmultiples_index (H₂.comap (AddMonoidHom.inl ℤ A))`. Establish `hDD : H₁.comap (AddMonoidHom.inl ℤ A) = H₂.comap (AddMonoidHom.inl ℤ A)`. Rewrite using `[hD₁, hD₂]`.

Conclude with `congrArg (fun d : ℕ => zmultiples (d : ℤ)) hd`. Use `set v := V (H₁.map (AddMonoidHom.snd ℤ A)) with hvdef`. Establish `hlift : ∀ i, ∃ x : ℤ, (x, v i) ∈ H₁ ⊓ H₂`. Introduce `i`. Establish `hvi : v i ∈ H₁.map (AddMonoidHom.snd ℤ A)`.

Rewrite using `[← hV (H₁.map (AddMonoidHom.snd ℤ A))]`. Conclude with `subset_closure ⟨i, rfl⟩`. Establish `hex₁ : ∃ x : ℤ, (x, V (H₁.map (AddMonoidHom.snd ℤ A)) i) ∈ H₁`. Take `⟨p, hp, hps⟩` from `hvi`. Conclude with `⟨p.1, by rw [← hvdef, ← hps]; exact hp⟩`.

Establish `hex₂ : ∃ x : ℤ, (x, V (H₂.map (AddMonoidHom.snd ℤ A)) i) ∈ H₂`. Rewrite `hvi` using `[hm]`. Take `⟨p, hp, hps⟩` from `hvi`. Conclude with `⟨p.1, by rw [← hm, ← hvdef, ← hps]; exact hp⟩`. Establish `hci` using `congrFun hc i`.

Simplify using `only [cc, dif_pos hex₁, dif_pos hex₂] at hci`. Establish `hs₁` using `hex₁.choose_spec`. Establish `hkey : ∀ x : ℤ, (x, V (H₂.map (AddMonoidHom.snd ℤ A)) i) ∈ H₂ → (x, v i) ∈ H₂` using `fun x hx => by rw [hvdef, hm]; exact hx`. Establish `hs₂` using `hkey _ hex₂.choose_spec`. Use `⟨hex₁.choose, hs₁, ?_⟩` and prove the remaining obligations.

Establish `hmod : (dd H₂ : ℤ) ∣ hex₂.choose - hex₁.choose`. Rewrite `hci` using `[hd]`. Conclude with `Int.ModEq.dvd hci`. Establish `hz : hex₂.choose - hex₁.choose ∈ H₂.comap (AddMonoidHom.inl ℤ A)`. Rewrite using `[hD₂]`.

Conclude with `Int.mem_zmultiples_iff.mpr hmod`. Establish `hz' : (hex₂.choose - hex₁.choose, (0 : A)) ∈ H₂` using `hz`. Establish `he : (hex₁.choose, v i) = (hex₂.choose, v i) - (hex₂.choose - hex₁.choose, (0 : A))`. Use `ext`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Rewrite using `[he]`. Conclude with `H₂.sub_mem hs₂ hz'`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `le_of_lifts v (hV _) hDD.le hlift`.

Use `le_of_lifts v (by rw [← hm]; exact hV _) hDD.ge fun i => ?_` and prove the remaining obligations. Take `⟨x, hx⟩` from `hlift i`. Conclude with `⟨x, by rwa [inf_comm]⟩`. Establish `hTfin : T.Finite`. Use `Set.Finite.biUnion (Finset.finite_toSet _) fun d hd => ?_` and prove the remaining obligations.

Use `(Set.finite_singleton d).prod ((ih _ ?_).1.prod (Finset.finite_toSet _))` and prove the remaining obligations. Conclude with `Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)`. Use `⟨Set.Finite.of_finite_image (hTfin.subset ?_) hinj, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨H, hH, rfl⟩`. Conclude with `hmaps H hH`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[Set.ncard_prod, Set.ncard_prod, Set.ncard_singleton, one_mul, Set.ncard_coe_finset]`. Simplify using `[cube, Fintype.card_piFinset, Int.card_Ico]`. Use `_ ≤ ∑ d ∈ j.divisors, (j / d) ^ n * d ^ n := by`.

Use `Finset.sum_le_sum fun d hd => Nat.mul_le_mul_right _ (ih _ ?_).2` and prove the remaining obligations. Conclude with `Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)`. Use `_ = ∑ _d ∈ j.divisors, j ^ n := by`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Rewrite using `[← mul_pow, Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]`.

Use `_ = j.divisors.card * j ^ n := by rw [Finset.sum_const, smul_eq_mul]`. Use `_ ≤ j * j ^ n := Nat.mul_le_mul_right _ (Nat.card_divisors_le_self j)`. Use `_ = j ^ (n + 1) := by ring`.
-/
theorem step {A : Type*} [AddCommGroup A] (n : ℕ)
    (hgen : ∀ K : AddSubgroup A, ∃ v : Fin n → A, AddSubgroup.closure (Set.range v) = K)
    (ih : ∀ j : ℕ, 1 ≤ j → {H : AddSubgroup A | H.index = j}.Finite ∧
      {H : AddSubgroup A | H.index = j}.ncard ≤ j ^ n) :
    ∀ j : ℕ, 1 ≤ j → {H : AddSubgroup (ℤ × A) | H.index = j}.Finite ∧
      {H : AddSubgroup (ℤ × A) | H.index = j}.ncard ≤ j ^ (n + 1) := by
  intro j hj
  choose V hV using hgen
  classical
  set S := {H : AddSubgroup (ℤ × A) | H.index = j} with hS
  let dd : AddSubgroup (ℤ × A) → ℕ := fun H => (H.comap (AddMonoidHom.inl ℤ A)).index
  let cc : AddSubgroup (ℤ × A) → Fin n → ℤ := fun H i =>
    if h : ∃ x : ℤ, (x, V (H.map (AddMonoidHom.snd ℤ A)) i) ∈ H then h.choose % (dd H : ℤ)
    else 0
  let F : AddSubgroup (ℤ × A) → ℕ × AddSubgroup A × (Fin n → ℤ) :=
    fun H => (dd H, H.map (AddMonoidHom.snd ℤ A), cc H)
  let cube : ℕ → Finset (Fin n → ℤ) := fun d => Fintype.piFinset fun _ => Finset.Ico (0 : ℤ) d
  let T : Set (ℕ × AddSubgroup A × (Fin n → ℤ)) :=
    ⋃ d ∈ j.divisors, ({d} : Set ℕ) ×ˢ ({H : AddSubgroup A | H.index = j / d} ×ˢ
      (cube d : Set (Fin n → ℤ)))
  have hpos : ∀ H ∈ S, 0 < dd H ∧ H.index = dd H * (H.map (AddMonoidHom.snd ℤ A)).index := by
    intro H hH
    have hp := index_prod_eq H
    refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, hp⟩
    have : H.index = j := hH
    simp only [dd] at h0
    rw [h0, zero_mul] at hp
    omega
  have hmaps : ∀ H ∈ S, F H ∈ T := by
    intro H hH
    obtain ⟨hd, hp⟩ := hpos H hH
    have hHj : H.index = j := hH
    simp only [T, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
    refine ⟨dd H, Nat.mem_divisors.mpr ⟨⟨_, hHj ▸ hp⟩, by omega⟩, rfl, ?_, ?_⟩
    · show (H.map (AddMonoidHom.snd ℤ A)).index = j / dd H
      rw [← hHj, hp, Nat.mul_div_cancel_left _ hd]
    · simp only [cube]
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      intro i
      simp only [F, cc, Finset.mem_Ico]
      have hd' : (0 : ℤ) < (dd H : ℤ) := by exact_mod_cast hd
      split_ifs
      · exact ⟨Int.emod_nonneg _ hd'.ne', Int.emod_lt_of_pos _ hd'⟩
      · exact ⟨le_rfl, hd'⟩
  have hinj : Set.InjOn F S := by
    intro H₁ hH₁ H₂ hH₂ hF
    simp only [F, Prod.mk.injEq] at hF
    obtain ⟨hd, hm, hc⟩ := hF
    have hD₁ := eq_zmultiples_index (H₁.comap (AddMonoidHom.inl ℤ A))
    have hD₂ := eq_zmultiples_index (H₂.comap (AddMonoidHom.inl ℤ A))
    have hDD : H₁.comap (AddMonoidHom.inl ℤ A) = H₂.comap (AddMonoidHom.inl ℤ A) := by
      rw [hD₁, hD₂]
      exact congrArg (fun d : ℕ => zmultiples (d : ℤ)) hd
    set v := V (H₁.map (AddMonoidHom.snd ℤ A)) with hvdef
    have hlift : ∀ i, ∃ x : ℤ, (x, v i) ∈ H₁ ⊓ H₂ := by
      intro i
      have hvi : v i ∈ H₁.map (AddMonoidHom.snd ℤ A) := by
        rw [← hV (H₁.map (AddMonoidHom.snd ℤ A))]
        exact subset_closure ⟨i, rfl⟩
      have hex₁ : ∃ x : ℤ, (x, V (H₁.map (AddMonoidHom.snd ℤ A)) i) ∈ H₁ := by
        obtain ⟨p, hp, hps⟩ := hvi
        exact ⟨p.1, by rw [← hvdef, ← hps]; exact hp⟩
      have hex₂ : ∃ x : ℤ, (x, V (H₂.map (AddMonoidHom.snd ℤ A)) i) ∈ H₂ := by
        rw [hm] at hvi
        obtain ⟨p, hp, hps⟩ := hvi
        exact ⟨p.1, by rw [← hm, ← hvdef, ← hps]; exact hp⟩
      have hci := congrFun hc i
      simp only [cc, dif_pos hex₁, dif_pos hex₂] at hci
      have hs₁ := hex₁.choose_spec
      have hkey : ∀ x : ℤ, (x, V (H₂.map (AddMonoidHom.snd ℤ A)) i) ∈ H₂ → (x, v i) ∈ H₂ :=
        fun x hx => by rw [hvdef, hm]; exact hx
      have hs₂ := hkey _ hex₂.choose_spec
      refine ⟨hex₁.choose, hs₁, ?_⟩
      have hmod : (dd H₂ : ℤ) ∣ hex₂.choose - hex₁.choose := by
        rw [hd] at hci
        exact Int.ModEq.dvd hci
      have hz : hex₂.choose - hex₁.choose ∈ H₂.comap (AddMonoidHom.inl ℤ A) := by
        rw [hD₂]
        exact Int.mem_zmultiples_iff.mpr hmod
      have hz' : (hex₂.choose - hex₁.choose, (0 : A)) ∈ H₂ := hz
      have he : (hex₁.choose, v i) =
          (hex₂.choose, v i) - (hex₂.choose - hex₁.choose, (0 : A)) := by
        ext
        · simp
        · simp
      rw [he]
      exact H₂.sub_mem hs₂ hz'
    apply le_antisymm
    · exact le_of_lifts v (hV _) hDD.le hlift
    · refine le_of_lifts v (by rw [← hm]; exact hV _) hDD.ge fun i => ?_
      obtain ⟨x, hx⟩ := hlift i
      exact ⟨x, by rwa [inf_comm]⟩
  have hTfin : T.Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun d hd => ?_
    refine (Set.finite_singleton d).prod ((ih _ ?_).1.prod (Finset.finite_toSet _))
    exact Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)
  refine ⟨Set.Finite.of_finite_image (hTfin.subset ?_) hinj, ?_⟩
  · rintro _ ⟨H, hH, rfl⟩
    exact hmaps H hH
  calc S.ncard ≤ T.ncard := Set.ncard_le_ncard_of_injOn F hmaps hinj hTfin
    _ ≤ ∑ d ∈ j.divisors, (({d} : Set ℕ) ×ˢ ({H : AddSubgroup A | H.index = j / d} ×ˢ
          (cube d : Set (Fin n → ℤ)))).ncard := Finset.set_ncard_biUnion_le _ _
    _ = ∑ d ∈ j.divisors, {H : AddSubgroup A | H.index = j / d}.ncard * d ^ n := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Set.ncard_prod, Set.ncard_prod, Set.ncard_singleton, one_mul, Set.ncard_coe_finset]
        simp [cube, Fintype.card_piFinset, Int.card_Ico]
    _ ≤ ∑ d ∈ j.divisors, (j / d) ^ n * d ^ n := by
        refine Finset.sum_le_sum fun d hd => Nat.mul_le_mul_right _ (ih _ ?_).2
        exact Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)
    _ = ∑ _d ∈ j.divisors, j ^ n := by
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [← mul_pow, Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]
    _ = j.divisors.card * j ^ n := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ j * j ^ n := Nat.mul_le_mul_right _ (Nat.card_divisors_le_self j)
    _ = j ^ (n + 1) := by ring

/- English proof (translation)
Introduce `j hj`. Take `⟨hfin, hcard⟩` from `h j hj`. Set `f : AddSubgroup G → AddSubgroup G'` to `fun H => H.comap e.symm.toAddMonoidHom`. Establish `hmaps : ∀ H ∈ {H : AddSubgroup G | H.index = j}, f H ∈ {H : AddSubgroup G' | H.index = j}`. Introduce `H hH`.

Use `show (H.comap e.symm.toAddMonoidHom).index = j`. Rewrite using `[index_comap_of_surjective _ e.symm.surjective]`. Conclude with `hH`. Establish `hinj : Set.InjOn f {H : AddSubgroup G | H.index = j}` using `(comap_injective e.symm.surjective).injOn`. Use `⟨Set.Finite.of_finite_image (hfin.subset ?_) hinj, ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨H, hH, rfl⟩`. Conclude with `hmaps H hH`. Conclude with `(Set.ncard_le_ncard_of_injOn f hmaps hinj hfin).trans hcard`.
-/
theorem transfer {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (e : G ≃+ G') (n : ℕ)
    (h : ∀ j : ℕ, 1 ≤ j → {H : AddSubgroup G' | H.index = j}.Finite ∧
      {H : AddSubgroup G' | H.index = j}.ncard ≤ j ^ n) :
    ∀ j : ℕ, 1 ≤ j → {H : AddSubgroup G | H.index = j}.Finite ∧
      {H : AddSubgroup G | H.index = j}.ncard ≤ j ^ n := by
  intro j hj
  obtain ⟨hfin, hcard⟩ := h j hj
  let f : AddSubgroup G → AddSubgroup G' := fun H => H.comap e.symm.toAddMonoidHom
  have hmaps : ∀ H ∈ {H : AddSubgroup G | H.index = j},
      f H ∈ {H : AddSubgroup G' | H.index = j} := by
    intro H hH
    show (H.comap e.symm.toAddMonoidHom).index = j
    rw [index_comap_of_surjective _ e.symm.surjective]
    exact hH
  have hinj : Set.InjOn f {H : AddSubgroup G | H.index = j} :=
    (comap_injective e.symm.surjective).injOn
  refine ⟨Set.Finite.of_finite_image (hfin.subset ?_) hinj, ?_⟩
  · rintro _ ⟨H, hH, rfl⟩
    exact hmaps H hH
  exact (Set.ncard_le_ncard_of_injOn f hmaps hinj hfin).trans hcard

def consEquiv (n : ℕ) : (Fin (n + 1) → ℤ) ≃+ ℤ × (Fin n → ℤ) where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by simp
  map_add' f g := rfl

/- English proof (translation)
Take `⟨k, b⟩` from `Submodule.basisOfPid (Pi.basisFun ℤ (Fin n)) K.toIntSubmodule`. Establish `hk : k ≤ n`. Establish `h1` using `Submodule.finrank_le K.toIntSubmodule`. Rewrite `h1` using `[Module.finrank_eq_card_basis b, Fintype.card_fin, Module.finrank_fin_fun]`. Then use the resulting hypothesis. Use `⟨fun i => if h : i.val < k then (b ⟨i, h⟩ : Fin n → ℤ) else 0, ?_⟩` and prove the remaining obligations.

Apply `AddSubgroup.toIntSubmodule.injective` to reduce the goal to its premises. Rewrite using `[AddSubgroup.toIntSubmodule_closure]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Simplify using `only`. Use `split_ifs`. Conclude with `(b _).2`. Conclude with `Submodule.zero_mem _`. Introduce `x hx`.

Establish `h2 : x ∈ (Submodule.span ℤ (Set.range b)).map K.toIntSubmodule.subtype` using `⟨⟨x, hx⟩, by rw [b.span_eq]; trivial, rfl⟩`. Rewrite `h2` using `[Submodule.map_span]`. Use `Submodule.span_mono ?_ h2` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨m, rfl⟩, rfl⟩`. Use `⟨⟨m, lt_of_lt_of_le m.2 hk⟩, ?_⟩` and prove the remaining obligations.

Simplify using `[m.2]`.
-/
lemma gen_pi (n : ℕ) (K : AddSubgroup (Fin n → ℤ)) :
    ∃ v : Fin n → (Fin n → ℤ), AddSubgroup.closure (Set.range v) = K := by
  obtain ⟨k, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin n)) K.toIntSubmodule
  have hk : k ≤ n := by
    have h1 := Submodule.finrank_le K.toIntSubmodule
    rwa [Module.finrank_eq_card_basis b, Fintype.card_fin, Module.finrank_fin_fun] at h1
  refine ⟨fun i => if h : i.val < k then (b ⟨i, h⟩ : Fin n → ℤ) else 0, ?_⟩
  apply AddSubgroup.toIntSubmodule.injective
  rw [AddSubgroup.toIntSubmodule_closure]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    dsimp only
    split_ifs
    · exact (b _).2
    · exact Submodule.zero_mem _
  · intro x hx
    have h2 : x ∈ (Submodule.span ℤ (Set.range b)).map K.toIntSubmodule.subtype :=
      ⟨⟨x, hx⟩, by rw [b.span_eq]; trivial, rfl⟩
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    refine ⟨⟨m, lt_of_lt_of_le m.2 hk⟩, ?_⟩
    simp [m.2]

/- English proof (translation)
Introduce `j _`. Establish `htop : ∀ H : AddSubgroup (Fin 0 → ℤ), H = ⊤` using `fun H => eq_top_iff.mpr fun x _ => by rw [Subsingleton.elim x 0]; exact H.zero_mem`. Establish `hsub : {H : AddSubgroup (Fin 0 → ℤ) | H.index = j} ⊆ {⊤}` using `fun H _ => htop H`. Use `⟨(Set.finite_singleton _).subset hsub, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero]`.

Conclude with `(Set.ncard_le_ncard hsub (Set.finite_singleton _)).trans (Set.ncard_singleton _).le`.
-/
lemma base : ∀ j : ℕ, 1 ≤ j → {H : AddSubgroup (Fin 0 → ℤ) | H.index = j}.Finite ∧
    {H : AddSubgroup (Fin 0 → ℤ) | H.index = j}.ncard ≤ j ^ 0 := by
  intro j _
  have htop : ∀ H : AddSubgroup (Fin 0 → ℤ), H = ⊤ := fun H =>
    eq_top_iff.mpr fun x _ => by rw [Subsingleton.elim x 0]; exact H.zero_mem
  have hsub : {H : AddSubgroup (Fin 0 → ℤ) | H.index = j} ⊆ {⊤} := fun H _ => htop H
  refine ⟨(Set.finite_singleton _).subset hsub, ?_⟩
  rw [pow_zero]
  exact (Set.ncard_le_ncard hsub (Set.finite_singleton _)).trans (Set.ncard_singleton _).le

end Formalism.SLP.P
