import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace GlobalTheory.SmGL.Segment

open GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ρ : IrrGL k} {hρ : ρ.IsCusp} {c d c' d' : ℤ} {h : c ≤ d} {h' : c' ≤ d'} {Δ Δ' : Segment k}

/- English proof (translation)
The claim follows from `mem_carrier.2 ⟨0, Δ.len_pos, by simp⟩`.
-/
theorem first_mem_carrier (Δ : Segment k) : Δ.first ∈ Δ.carrier := mem_carrier.2 ⟨0, Δ.len_pos, by simp⟩

/- English proof (translation)
Simplify using `only [mem_icc, IrrGL.nu_intCast_inj hρ.1]`. Conclude with `⟨fun ⟨_, h1, h2, e⟩ => e ▸ ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨a, h1, h2, rfl⟩⟩`.
-/
theorem nu_mem_icc {a : ℤ} : ρ.nu a ∈ (icc ρ hρ c d h).carrier ↔ c ≤ a ∧ a ≤ d := by
  simp only [mem_icc, IrrGL.nu_intCast_inj hρ.1]
  exact ⟨fun ⟨_, h1, h2, e⟩ => e ▸ ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨a, h1, h2, rfl⟩⟩

/- English proof (translation)
The claim follows from `ext_first e (by simp only [icc, len_ofFirst]; omega)`.
-/
theorem eq_icc_of_first_eq (hρ : ρ.IsCusp) (e : Δ.first = ρ.nu c) :
    Δ = icc ρ hρ c (c + Δ.len - 1) (Int.le_sub_one_of_lt (lt_add_of_pos_right c (Nat.cast_pos.2 Δ.len_pos))) :=
  ext_first e (by simp only [icc, len_ofFirst]; omega)

/- English proof (translation)
Take `⟨b, -, hb⟩` from `mem_carrier.1 ha`. Use `⟨a - b, _, _, eq_icc_of_first_eq hρ ?_⟩` and prove the remaining obligations. Use `congrArg (fun x => IrrGL.nu x (-(b : ℂ))) hb` as an intermediate fact. Simplify `this` using `[sub_eq_add_neg]`.
-/
theorem exists_eq_icc_of_mem (hρ : ρ.IsCusp) {a : ℤ} (ha : ρ.nu a ∈ Δ.carrier) :
    ∃ (c d : ℤ) (h : c ≤ d), Δ = icc ρ hρ c d h := by
  obtain ⟨b, -, hb⟩ := mem_carrier.1 ha
  refine ⟨a - b, _, _, eq_icc_of_first_eq hρ ?_⟩
  have := congrArg (fun x => IrrGL.nu x (-(b : ℂ))) hb
  simpa [sub_eq_add_neg] using this

/- English proof (translation)
Use `⟨fun H => ⟨(nu_mem_icc.1 (H (nu_mem_icc.2 ⟨le_rfl, h⟩))).1, (nu_mem_icc.1 (H (nu_mem_icc.2 ⟨h, le_rfl⟩))).2⟩, fun ⟨h1, h2⟩ x hx => ?_⟩` and prove the remaining obligations. Take `⟨a, h3, h4, rfl⟩` from `mem_icc.1 hx`. Conclude with `nu_mem_icc.2 ⟨h1.trans h3, h4.trans h2⟩`.
-/
theorem icc_subset_icc : (icc ρ hρ c d h).carrier ⊆ (icc ρ hρ c' d' h').carrier ↔ c' ≤ c ∧ d ≤ d' := by
  refine ⟨fun H => ⟨(nu_mem_icc.1 (H (nu_mem_icc.2 ⟨le_rfl, h⟩))).1, (nu_mem_icc.1 (H (nu_mem_icc.2 ⟨h, le_rfl⟩))).2⟩,
    fun ⟨h1, h2⟩ x hx => ?_⟩
  obtain ⟨a, h3, h4, rfl⟩ := mem_icc.1 hx
  exact nu_mem_icc.2 ⟨h1.trans h3, h4.trans h2⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨Γ, hΓ⟩`. Take `⟨e, f, hef, rfl⟩` from `exists_eq_icc_of_mem (Δ := Γ) hρ (a := c) (by rw [hΓ]; exact Or.inl (nu_mem_icc.2 ⟨le_rfl, h⟩))`. Establish `key : ∀ a : ℤ, (e ≤ a ∧ a ≤ f) ↔ (c ≤ a ∧ a ≤ d) ∨ (c' ≤ a ∧ a ≤ d')` using `fun a => by`. Simplify `Set.ext_iff.1 hΓ (ρ.nu a)` using `only [Set.mem_union, nu_mem_icc]`.

Use `key c` as an intermediate fact. Use `key d'` as an intermediate fact. Use `key c'` as an intermediate fact. Use `key d` as an intermediate fact. Use `key (d + 1)` as an intermediate fact.

Use `key (d' + 1)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨h1, h2⟩`. Use `⟨icc ρ hρ (min c c') (max d d') (by omega), Set.ext fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_union, mem_icc]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, h3, h4, rfl⟩`. Distinguish the cases in `ha : c ≤ a ∧ a ≤ d`. Conclude with `Or.inl ⟨a, ha.1, ha.2, rfl⟩`. Conclude with `Or.inr ⟨a, by omega, by omega, rfl⟩`.

Apply the tactic sequence `rintro (⟨a, h3, h4, rfl⟩ | ⟨a, h3, h4, rfl⟩) <;> exact ⟨a, by omega, by omega, rfl⟩`.
-/
theorem exists_carrier_eq_union_icc :
    (∃ Γ : Segment k, Γ.carrier = (icc ρ hρ c d h).carrier ∪ (icc ρ hρ c' d' h').carrier) ↔
      c' ≤ d + 1 ∧ c ≤ d' + 1 := by
  constructor
  · rintro ⟨Γ, hΓ⟩
    obtain ⟨e, f, hef, rfl⟩ := exists_eq_icc_of_mem (Δ := Γ) hρ (a := c)
      (by rw [hΓ]; exact Or.inl (nu_mem_icc.2 ⟨le_rfl, h⟩))
    have key : ∀ a : ℤ, (e ≤ a ∧ a ≤ f) ↔ (c ≤ a ∧ a ≤ d) ∨ (c' ≤ a ∧ a ≤ d') := fun a => by
      simpa only [Set.mem_union, nu_mem_icc] using Set.ext_iff.1 hΓ (ρ.nu a)
    have := key c; have := key d'; have := key c'; have := key d; have := key (d + 1); have := key (d' + 1)
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨icc ρ hρ (min c c') (max d d') (by omega), Set.ext fun x => ?_⟩
    simp only [Set.mem_union, mem_icc]
    constructor
    · rintro ⟨a, h3, h4, rfl⟩
      by_cases ha : c ≤ a ∧ a ≤ d
      · exact Or.inl ⟨a, ha.1, ha.2, rfl⟩
      · exact Or.inr ⟨a, by omega, by omega, rfl⟩
    · rintro (⟨a, h3, h4, rfl⟩ | ⟨a, h3, h4, rfl⟩) <;> exact ⟨a, by omega, by omega, rfl⟩

/- English proof (translation)
Rewrite using `[Linked, exists_carrier_eq_union_icc, icc_subset_icc, icc_subset_icc]`. Use linear arithmetic over natural numbers and integers.
-/
theorem linked_icc : (icc ρ hρ c d h).Linked (icc ρ hρ c' d' h') ↔
    (c < c' ∧ c' ≤ d + 1 ∧ d < d') ∨ (c' < c ∧ c ≤ d' + 1 ∧ d' < d) := by
  rw [Linked, exists_carrier_eq_union_icc, icc_subset_icc, icc_subset_icc]
  omega

/- English proof (translation)
Establish `key : (∃ j : ℕ, 0 < j ∧ (icc ρ hρ c' d' h').first = (icc ρ hρ c d h).first.nu j) ↔ c < c'`. Establish `e : ∀ j : ℕ, (icc ρ hρ c' d' h').first = (icc ρ hρ c d h).first.nu j ↔ c' = c + j` using `fun j => by`. Rewrite using `[← IrrGL.nu_intCast_inj hρ.1]`. Simplify using `[icc]`. Simplify using `only [e]`.

Conclude with `⟨fun ⟨j, h1, h2⟩ => by omega, fun H => ⟨(c' - c).toNat, by omega, by omega⟩⟩`. Rewrite using `[Precedes, linked_icc, key]`. Use linear arithmetic over natural numbers and integers.
-/
theorem precedes_icc : (icc ρ hρ c d h).Precedes (icc ρ hρ c' d' h') ↔ c < c' ∧ c' ≤ d + 1 ∧ d < d' := by
  have key : (∃ j : ℕ, 0 < j ∧ (icc ρ hρ c' d' h').first = (icc ρ hρ c d h).first.nu j) ↔ c < c' := by
    have e : ∀ j : ℕ, (icc ρ hρ c' d' h').first = (icc ρ hρ c d h).first.nu j ↔ c' = c + j := fun j => by
      rw [← IrrGL.nu_intCast_inj hρ.1]
      simp [icc]
    simp only [e]
    exact ⟨fun ⟨j, h1, h2⟩ => by omega, fun H => ⟨(c' - c).toNat, by omega, by omega⟩⟩
  rw [Precedes, linked_icc, key]
  omega

/- English proof (translation)
Take `⟨⟨Γ, hΓ⟩, -⟩` from `H`. Establish `key : ∀ D : Segment k, D.carrier ⊆ Γ.carrier → ∃ (c d : ℤ) (h : c ≤ d), D = icc Γ.first Γ.isCusp_first c d h` using `fun D hD => by`. Take `⟨a, -, ha⟩` from `mem_carrier.1 (hD D.first_mem_carrier)`. Conclude with `⟨a, _, _, eq_icc_of_first_eq _ (by simpa using ha.symm)⟩`. Take `⟨c, d, h, e⟩` from `key Δ (hΓ ▸ Set.subset_union_left)`.

Take `⟨c', d', h', e'⟩` from `key Δ' (hΓ ▸ Set.subset_union_right)`. Conclude with `⟨_, _, c, d, c', d', h, h', e, e'⟩`.
-/
theorem Linked.exists_eq_icc (H : Linked Δ Δ') : ∃ (ρ : IrrGL k) (hρ : ρ.IsCusp) (c d c' d' : ℤ) (h : c ≤ d) (h' : c' ≤ d'),
    Δ = icc ρ hρ c d h ∧ Δ' = icc ρ hρ c' d' h' := by
  obtain ⟨⟨Γ, hΓ⟩, -⟩ := H
  have key : ∀ D : Segment k, D.carrier ⊆ Γ.carrier → ∃ (c d : ℤ) (h : c ≤ d), D = icc Γ.first Γ.isCusp_first c d h :=
    fun D hD => by
      obtain ⟨a, -, ha⟩ := mem_carrier.1 (hD D.first_mem_carrier)
      exact ⟨a, _, _, eq_icc_of_first_eq _ (by simpa using ha.symm)⟩
  obtain ⟨c, d, h, e⟩ := key Δ (hΓ ▸ Set.subset_union_left)
  obtain ⟨c', d', h', e'⟩ := key Δ' (hΓ ▸ Set.subset_union_right)
  exact ⟨_, _, c, d, c', d', h, h', e, e'⟩

/- English proof (translation)
Use `⟨fun H => ?_, fun H => H.elim (·.1) (·.1.symm)⟩` and prove the remaining obligations. Take `⟨ρ, hρ, c, d, c', d', h, h', rfl, rfl⟩` from `H.exists_eq_icc`. Simplify `linked_icc.1 H` using `only [precedes_icc]`.
-/
theorem linked_iff_precedes : Linked Δ Δ' ↔ Precedes Δ Δ' ∨ Precedes Δ' Δ := by
  refine ⟨fun H => ?_, fun H => H.elim (·.1) (·.1.symm)⟩
  obtain ⟨ρ, hρ, c, d, c', d', h, h', rfl, rfl⟩ := H.exists_eq_icc
  simpa only [precedes_icc] using linked_icc.1 H

/- English proof (translation)
Establish `key : ∀ j : ℕ, Δ'.first = Δ.first.nu j → (Precedes Δ Δ' ↔ 0 < j ∧ j ≤ Δ.len ∧ Δ.len < j + Δ'.len)` using `fun j e => by`. Establish `e1` using `eq_icc_of_first_eq (Δ := Δ) (c := 0) Δ.isCusp_first (by simp)`. Establish `e2` using `eq_icc_of_first_eq (Δ := Δ') (c := j) Δ.isCusp_first (by simpa using e)`. Use `(iff_of_eq (congrArg₂ Precedes e1 e2)).trans (precedes_icc.trans ?_)` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers.

Use `⟨fun H => ?_, fun ⟨j, h1, h2, h3, e⟩ => (key j e).2 ⟨h1, h2, h3⟩⟩` and prove the remaining obligations. Take `⟨j, -, e⟩` from `H.2`. Take `⟨h1, h2, h3⟩` from `(key j e).1 H`. Conclude with `⟨j, h1, h2, h3, e⟩`.
-/
theorem precedes_iff : Precedes Δ Δ' ↔
    ∃ j : ℕ, 0 < j ∧ j ≤ Δ.len ∧ Δ.len < j + Δ'.len ∧ Δ'.first = Δ.first.nu j := by
  have key : ∀ j : ℕ, Δ'.first = Δ.first.nu j → (Precedes Δ Δ' ↔ 0 < j ∧ j ≤ Δ.len ∧ Δ.len < j + Δ'.len) := fun j e => by
    have e1 := eq_icc_of_first_eq (Δ := Δ) (c := 0) Δ.isCusp_first (by simp)
    have e2 := eq_icc_of_first_eq (Δ := Δ') (c := j) Δ.isCusp_first (by simpa using e)
    refine (iff_of_eq (congrArg₂ Precedes e1 e2)).trans (precedes_icc.trans ?_)
    omega
  refine ⟨fun H => ?_, fun ⟨j, h1, h2, h3, e⟩ => (key j e).2 ⟨h1, h2, h3⟩⟩
  obtain ⟨j, -, e⟩ := H.2
  obtain ⟨h1, h2, h3⟩ := (key j e).1 H
  exact ⟨j, h1, h2, h3, e⟩

/- English proof (translation)
Proceed by induction on `H with`. Consider the case `single H => exact H.2`. Consider the case `tail _ H ih`. Take `⟨i, hi, e⟩` from `ih`. Take `⟨j, -, e'⟩` from `H.2`.

Conclude with `⟨i + j, by omega, by rw [e', e, IrrGL.nu_nu, Nat.cast_add]⟩`.
-/
theorem exists_first_eq_of_transGen (H : Relation.TransGen Precedes Δ Δ') :
    ∃ j : ℕ, 0 < j ∧ Δ'.first = Δ.first.nu j := by
  induction H with
  | single H => exact H.2
  | tail _ H ih =>
    obtain ⟨i, hi, e⟩ := ih
    obtain ⟨j, -, e'⟩ := H.2
    exact ⟨i + j, by omega, by rw [e', e, IrrGL.nu_nu, Nat.cast_add]⟩

/- English proof (translation)
Introduce `H` and use `by obtain ⟨j, hj, e⟩ := exists_first_eq_of_transGen H exact hj.ne ((IrrGL.nu_natCast_inj Δ.isCusp_first.1).1 (by simpa using e))`.
-/
theorem not_transGen_precedes_self (Δ : Segment k) : ¬ Relation.TransGen Precedes Δ Δ := fun H => by
  obtain ⟨j, hj, e⟩ := exists_first_eq_of_transGen H
  exact hj.ne ((IrrGL.nu_natCast_inj Δ.isCusp_first.1).1 (by simpa using e))

/- English proof (translation)
Introduce `H'` and use `not_transGen_precedes_self Δ ((Relation.TransGen.single H).tail H')`.
-/
theorem Precedes.asymm (H : Precedes Δ Δ') : ¬ Precedes Δ' Δ := fun H' =>
  not_transGen_precedes_self Δ ((Relation.TransGen.single H).tail H')

/- English proof (translation)
Take `⟨-, j, hj, e⟩` from `H`. Establish `e' : Δ.first.nu y = Δ.first.nu ((x + j : ℝ) : ℂ)`. Use `push_cast`. Conclude with `e.trans (Δ.first.nu_nu x j)`. Establish `: (0 : ℝ) < j` using `Nat.cast_pos.2 hj`.

Rewrite using `[(IrrGL.nu_ofReal_inj Δ.isCusp_first.1).1 e']`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lt_of_precedes_nu {x y : ℝ} (H : (Δ.nu x).Precedes (Δ.nu y)) : x < y := by
  obtain ⟨-, j, hj, e⟩ := H
  have e' : Δ.first.nu y = Δ.first.nu ((x + j : ℝ) : ℂ) := by
    push_cast
    exact e.trans (Δ.first.nu_nu x j)
  have : (0 : ℝ) < j := Nat.cast_pos.2 hj
  rw [(IrrGL.nu_ofReal_inj Δ.isCusp_first.1).1 e']
  linarith

/- English proof (translation)
Introduce `H` and use `hxy.asymm (lt_of_precedes_nu H)`.
-/
theorem not_precedes_nu (Δ : Segment k) {x y : ℝ} (hxy : y < x) : ¬ (Δ.nu x).Precedes (Δ.nu y) := fun H =>
  hxy.asymm (lt_of_precedes_nu H)

/- English proof (translation)
The claim follows from `Function.LeftInverse.injective (g := fun x => x.tw χ⁻¹ hχ.inv) fun x => x.tw_tw_inv χ hχ`.
-/
theorem tw_injective (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Function.Injective fun Δ : Segment k => Δ.tw χ hχ :=
  Function.LeftInverse.injective (g := fun x => x.tw χ⁻¹ hχ.inv) fun x => x.tw_tw_inv χ hχ

end GlobalTheory.SmGL.Segment

namespace GlobalTheory.LocGL

/- English proof (translation)
Set `p : α → α → Prop` to `fun a b => Relation.ReflTransGen r b a`. Use `haveI : IsPartialOrder α p := { refl := fun _ => .refl trans := fun _ _ _ h h' => h'.trans h antisymm := fun a b h h' => by`. Break down `Relation.reflTransGen_iff_eq_or_transGen.1 h with e | h` into its components or cases. Conclude with `e`. Conclude with `absurd (h.trans_left h') (hr _) }`.

Take `⟨s, hs, hps⟩` from `extend_partialOrder p`. Use `⟨m.sort s, m.sort_eq s, (m.pairwise_sort s).imp fun {a b} hab h => ?_⟩` and prove the remaining obligations. Take `rfl : a = b` from `antisymm hab (hps _ _ (.single h))`. Conclude with `hr a (.single h)`.
-/
theorem exists_list_pairwise_not_rel {α : Type*} {r : α → α → Prop} (hr : ∀ a, ¬ Relation.TransGen r a a)
    (m : Multiset α) : ∃ l : List α, (l : Multiset α) = m ∧ l.Pairwise fun a b => ¬ r a b := by
  classical
  let p : α → α → Prop := fun a b => Relation.ReflTransGen r b a
  haveI : IsPartialOrder α p :=
    { refl := fun _ => .refl
      trans := fun _ _ _ h h' => h'.trans h
      antisymm := fun a b h h' => by
        rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with e | h
        · exact e
        · exact absurd (h.trans_left h') (hr _) }
  obtain ⟨s, hs, hps⟩ := extend_partialOrder p
  refine ⟨m.sort s, m.sort_eq s, (m.pairwise_sort s).imp fun {a b} hab h => ?_⟩
  obtain rfl : a = b := antisymm hab (hps _ _ (.single h))
  exact hr a (.single h)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨l, rfl, hl⟩` from `exists_list_pairwise_not_rel Segment.not_transGen_precedes_self 𝔪`. Conclude with `⟨l.get, (Fin.univ_val_map l.get).trans (congrArg _ (List.ofFn_get l)), List.pairwise_iff_get.1 hl⟩`.
-/
theorem exists_isOrderedForm (𝔪 : Multiset (Segment k)) :
    ∃ Δ : Fin 𝔪.card → Segment k, IsOrderedForm Δ 𝔪 := by
  obtain ⟨l, rfl, hl⟩ := exists_list_pairwise_not_rel Segment.not_transGen_precedes_self 𝔪
  exact ⟨l.get, (Fin.univ_val_map l.get).trans (congrArg _ (List.ofFn_get l)), List.pairwise_iff_get.1 hl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun H => by simpa only [Multiset.map_map, Function.comp_def, Segment.tw_tw_inv, Multiset.map_id'] using H.tw χ⁻¹ hχ.inv, fun H => H.tw χ hχ⟩`.
-/
theorem isOrderedForm_tw_iff {h : ℕ} {Δ : Fin h → Segment k} {𝔪 : Multiset (Segment k)} (χ : kˣ →* ℂˣ)
    (hχ : IsSmoothChar χ) : IsOrderedForm (fun i => (Δ i).tw χ hχ) (𝔪.map (·.tw χ hχ)) ↔ IsOrderedForm Δ 𝔪 :=
  ⟨fun H => by simpa only [Multiset.map_map, Function.comp_def, Segment.tw_tw_inv, Multiset.map_id'] using H.tw χ⁻¹ hχ.inv,
    fun H => H.tw χ hχ⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨fun _ _ => Segment.Precedes.asymm, Segment.not_transGen_precedes_self, exists_isOrderedForm⟩, ⟨fun _ _ _ _ _ _ _ _ => Segment.precedes_icc, fun _ _ => Segment.linked_iff_precedes⟩, fun χ hχ => ⟨fun _ _ => Segment.linked_tw_iff χ hχ, fun _ _ => Segment.precedes_tw_iff χ hχ, fun …`.
-/
theorem precedes_and_orderedForms (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] :
    ((∀ Δ Δ' : Segment k, Δ.Precedes Δ' → ¬ Δ'.Precedes Δ) ∧
      (∀ Δ : Segment k, ¬ Relation.TransGen Segment.Precedes Δ Δ) ∧
      ∀ 𝔪 : Multiset (Segment k), ∃ Δ : Fin 𝔪.card → Segment k, IsOrderedForm Δ 𝔪) ∧
    ((∀ (ρ : IrrGL k) (hρ : ρ.IsCusp) (c d c' d' : ℤ) (h : c ≤ d) (h' : c' ≤ d'),
        (Segment.icc ρ hρ c d h).Precedes (Segment.icc ρ hρ c' d' h') ↔ c < c' ∧ c' ≤ d + 1 ∧ d < d') ∧
      ∀ Δ Δ' : Segment k, Δ.Linked Δ' ↔ Δ.Precedes Δ' ∨ Δ'.Precedes Δ) ∧
    (∀ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ),
      (∀ Δ Δ' : Segment k, (Δ.tw χ hχ).Linked (Δ'.tw χ hχ) ↔ Δ.Linked Δ') ∧
      (∀ Δ Δ' : Segment k, (Δ.tw χ hχ).Precedes (Δ'.tw χ hχ) ↔ Δ.Precedes Δ') ∧
      ∀ (h : ℕ) (Δ : Fin h → Segment k) (𝔪 : Multiset (Segment k)),
        IsOrderedForm (fun i => (Δ i).tw χ hχ) (𝔪.map (·.tw χ hχ)) ↔ IsOrderedForm Δ 𝔪) ∧
    ∀ (Δ : Segment k) (x y : ℝ), y < x → ¬ (Δ.nu x).Precedes (Δ.nu y) :=
  ⟨⟨fun _ _ => Segment.Precedes.asymm, Segment.not_transGen_precedes_self, exists_isOrderedForm⟩,
    ⟨fun _ _ _ _ _ _ _ _ => Segment.precedes_icc, fun _ _ => Segment.linked_iff_precedes⟩,
    fun χ hχ => ⟨fun _ _ => Segment.linked_tw_iff χ hχ, fun _ _ => Segment.precedes_tw_iff χ hχ,
      fun _ _ _ => isOrderedForm_tw_iff χ hχ⟩,
    fun Δ _ _ h => Δ.not_precedes_nu h⟩

end GlobalTheory.LocGL
