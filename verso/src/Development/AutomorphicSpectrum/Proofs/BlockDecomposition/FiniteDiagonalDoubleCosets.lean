import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.OrbitCount

/- English proof (translation)
Establish `hT : (g ⁻¹' (S : Set D)).Finite` using `Set.Finite.preimage' S.finite_toSet hfin`. Establish `hsupp : Function.support (fun p => f (g p)) ⊆ (hT.toFinset : Set P)`. Introduce `p hp`. Simplify using `using hS _ hp`. Rewrite using `[finsum_eq_sum_of_support_subset _ hsupp]`.

Establish `hmaps : ∀ p ∈ hT.toFinset, g p ∈ S`. Introduce `p hp`. Simplify using `using hp`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to hmaps]`. Use `Finset.sum_congr rfl fun Q hQ => ?_` and prove the remaining obligations.

Establish `hfil : hT.toFinset.filter (fun p => g p = Q) = (hfin Q hQ).toFinset`. Use extensionality with `p`. Simplify using `only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.2`.

Introduce `h`. Conclude with `⟨h ▸ hQ, h⟩`. Rewrite using `[hfil, Finset.sum_congr rfl (g := fun _ => f Q)]`. Rewrite using `[Finset.sum_const, nsmul_eq_mul, Nat.card_eq_card_finite_toFinset (hfin Q hQ)]`. Introduce `p hp`.

Establish `: g p = Q` using `by simpa using hp`. Rewrite using `[this]`.
-/
theorem finsum_comp_eq {P D : Type} (g : P → D) (f : D → ℂ) (S : Finset D)
    (hS : ∀ Q, f Q ≠ 0 → Q ∈ S) (hfin : ∀ Q ∈ S, (g ⁻¹' {Q}).Finite) :
    ∑ᶠ p, f (g p) = ∑ Q ∈ S, (Nat.card (g ⁻¹' {Q}) : ℂ) * f Q := by
  have hT : (g ⁻¹' (S : Set D)).Finite := Set.Finite.preimage' S.finite_toSet hfin
  have hsupp : Function.support (fun p => f (g p)) ⊆ (hT.toFinset : Set P) := by
    intro p hp
    simpa using hS _ hp
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hmaps : ∀ p ∈ hT.toFinset, g p ∈ S := by
    intro p hp
    simpa using hp
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  have hfil : hT.toFinset.filter (fun p => g p = Q) = (hfin Q hQ).toFinset := by
    ext p
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff,
      Finset.mem_coe]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ hQ, h⟩
  rw [hfil, Finset.sum_congr rfl (g := fun _ => f Q)]
  · rw [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_card_finite_toFinset (hfin Q hQ)]
  · intro p hp
    have : g p = Q := by simpa using hp
    rw [this]

/- English proof (translation)
Establish `hS : ∀ Q, f Q ≠ 0 → Q ∈ hf.toFinset` using `fun Q h => by simpa using h`. Establish `hempty : ∀ q Q, π Q ≠ q → Ψ q ⁻¹' {Q} = ∅`. Introduce `q Q hne`. Use extensionality with `p`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]`.

Introduce `h`. Conclude with `hne (h ▸ hπ q p)`. Establish `hinner : ∀ q, c q * ∑ᶠ p, f (Ψ q p) = ∑ Q ∈ hf.toFinset, if π Q = q then (c (π Q) * (Nat.card (Ψ (π Q) ⁻¹' {Q}) : ℂ)) * f Q else 0`. Introduce `q`. Rewrite using `[finsum_comp_eq (Ψ q) f hf.toFinset hS, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun Q _ => ?_` and prove the remaining obligations. Distinguish the cases in `hq : π Q = q`. Substitute `hq` using the available equality. Rewrite using `[if_pos rfl, mul_assoc]`. Rewrite using `[if_neg hq, hempty q Q hq]`.

Simplify using the standard rewrite rules. Introduce `Q hQ`. Distinguish the cases in `hq : π Q = q`. Substitute `hq` using the available equality. Conclude with `hfib Q (by simpa using hQ)`.

Rewrite using `[hempty q Q hq]`. Conclude with `Set.finite_empty`. Establish `hsupp : Function.support (fun q => c q * ∑ᶠ p, f (Ψ q p)) ⊆ ((hf.toFinset.image π : Finset D₁) : Set D₁)`. Introduce `q hq`. Assume the negation of the conclusion as `hnot`.

Apply `hq` to reduce the goal to its premises. Use `show c q * ∑ᶠ p, f (Ψ q p) = 0`. Rewrite using `[hinner q]`. Use `Finset.sum_eq_zero fun Q hQ => ?_` and prove the remaining obligations. Rewrite using `[if_neg]`.

Introduce `h`. Conclude with `hnot (by simpa using ⟨Q, by simpa using hQ, h⟩)`. Establish `hsuppL : Function.support (fun Q => (c (π Q) * (Nat.card (Ψ (π Q) ⁻¹' {Q}) : ℂ)) * f Q) ⊆ (hf.toFinset : Set D)`. Introduce `Q hQ`. Establish `: f Q ≠ 0` using `fun h => hQ (by simp [h])`.

Simplify using `using this`. Rewrite using `[finsum_eq_sum_of_support_subset _ hsupp, finsum_eq_sum_of_support_subset _ hsuppL]`. Repeatedly rewrite using `[hinner]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun Q hQ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_ite_eq]`. Rewrite using `[if_pos (Finset.mem_image_of_mem π hQ)]`.
-/
theorem abstract_sum {D D₁ P : Type} (π : D → D₁) (Ψ : D₁ → P → D)
    (hπ : ∀ q p, π (Ψ q p) = q) (f : D → ℂ) (hf : (Function.support f).Finite) (c : D₁ → ℂ)
    (hfib : ∀ Q, f Q ≠ 0 → (Ψ (π Q) ⁻¹' {Q}).Finite) :
    ∑ᶠ Q, (c (π Q) * (Nat.card (Ψ (π Q) ⁻¹' {Q}) : ℂ)) * f Q =
      ∑ᶠ q, c q * ∑ᶠ p, f (Ψ q p) := by
  have hS : ∀ Q, f Q ≠ 0 → Q ∈ hf.toFinset := fun Q h => by simpa using h
  have hempty : ∀ q Q, π Q ≠ q → Ψ q ⁻¹' {Q} = ∅ := by
    intro q Q hne
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    intro h
    exact hne (h ▸ hπ q p)
  have hinner : ∀ q, c q * ∑ᶠ p, f (Ψ q p) = ∑ Q ∈ hf.toFinset,
      if π Q = q then (c (π Q) * (Nat.card (Ψ (π Q) ⁻¹' {Q}) : ℂ)) * f Q else 0 := by
    intro q
    rw [finsum_comp_eq (Ψ q) f hf.toFinset hS, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun Q _ => ?_
      by_cases hq : π Q = q
      · subst hq
        rw [if_pos rfl, mul_assoc]
      · rw [if_neg hq, hempty q Q hq]
        simp
    · intro Q hQ
      by_cases hq : π Q = q
      · subst hq
        exact hfib Q (by simpa using hQ)
      · rw [hempty q Q hq]
        exact Set.finite_empty
  have hsupp : Function.support (fun q => c q * ∑ᶠ p, f (Ψ q p)) ⊆
      ((hf.toFinset.image π : Finset D₁) : Set D₁) := by
    intro q hq
    by_contra hnot
    apply hq
    show c q * ∑ᶠ p, f (Ψ q p) = 0
    rw [hinner q]
    refine Finset.sum_eq_zero fun Q hQ => ?_
    rw [if_neg]
    intro h
    exact hnot (by simpa using ⟨Q, by simpa using hQ, h⟩)
  have hsuppL : Function.support
      (fun Q => (c (π Q) * (Nat.card (Ψ (π Q) ⁻¹' {Q}) : ℂ)) * f Q) ⊆ (hf.toFinset : Set D) := by
    intro Q hQ
    have : f Q ≠ 0 := fun h => hQ (by simp [h])
    simpa using this
  rw [finsum_eq_sum_of_support_subset _ hsupp, finsum_eq_sum_of_support_subset _ hsuppL]
  simp_rw [hinner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_image_of_mem π hQ)]

variable {H : Type} [Group H]

abbrev cj {G : Type} [Group G] (L : Subgroup G) (x : G) : Subgroup G :=
  L.map (MulAut.conj x).toMonoidHom

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨l, hl, rfl⟩`. Establish `: x⁻¹ * (MulAut.conj x).toMonoidHom l * x = l`. Simplify using `[MulAut.conj_apply, mul_assoc]`. Rewrite using `[this]`.

Conclude with `hl`. Introduce `h`. Conclude with `⟨_, h, by simp [MulAut.conj_apply, mul_assoc]⟩`.
-/
theorem mem_cj {G : Type} [Group G] {L : Subgroup G} {x g : G} :
    g ∈ cj L x ↔ x⁻¹ * g * x ∈ L := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    have : x⁻¹ * (MulAut.conj x).toMonoidHom l * x = l := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [this]
    exact hl
  · intro h
    exact ⟨_, h, by simp [MulAut.conj_apply, mul_assoc]⟩

abbrev dg : H →* H × H := (MonoidHom.id H).prod (MonoidHom.id H)

/- English proof (translation)
Introduce `_ _ h` and use `congrArg Prod.fst h`.
-/
theorem dg_injective : Function.Injective (dg (H := H)) := fun _ _ h => congrArg Prod.fst h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, rfl⟩`. Conclude with `⟨rfl, ht⟩`. Introduce and unpack `⟨e, h⟩`. Conclude with `⟨g.1, h, Prod.ext rfl e⟩`.
-/
theorem mem_map_dg {Z : Subgroup H} {g : H × H} : g ∈ Z.map dg ↔ g.1 = g.2 ∧ g.1 ∈ Z := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨rfl, ht⟩
  · rintro ⟨e, h⟩
    exact ⟨g.1, h, Prod.ext rfl e⟩

/- English proof (translation)
Use extensionality with `g`. Establish `hc : g ∈ M.map (MulAut.conj y).toMonoidHom ↔ y.1⁻¹ * g.1 * y.1 ∈ L ∧ y.2⁻¹ * g.2 * y.2 ∈ L`. Use `mem_cj (L := M) (x := y) (g := g)` as an intermediate fact. Rewrite using `[this, hM]`. Both sides reduce to the same expression.

Rewrite using `[Subgroup.mem_inf, hc, hΔ, mem_map_dg, Subgroup.mem_inf, Subgroup.mem_inf, mem_cj, mem_cj]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨e, hz⟩, h1, h2⟩`. Conclude with `⟨e, ⟨hz, h1⟩, e ▸ h2⟩`. Introduce and unpack `⟨e, ⟨hz, h1⟩, h2⟩`.

Conclude with `⟨⟨e, hz⟩, h1, e ▸ h2⟩`.
-/
theorem inf_diag {Z L : Subgroup H} {Δ M : Subgroup (H × H)}
    (hΔ : ∀ g, g ∈ Δ ↔ g.1 = g.2 ∧ g.1 ∈ Z) (hM : ∀ g, g ∈ M ↔ g.1 ∈ L ∧ g.2 ∈ L) (y : H × H) :
    Δ ⊓ M.map (MulAut.conj y).toMonoidHom = ((Z ⊓ cj L y.1) ⊓ cj L y.2).map dg := by
  ext g
  have hc : g ∈ M.map (MulAut.conj y).toMonoidHom ↔
      y.1⁻¹ * g.1 * y.1 ∈ L ∧ y.2⁻¹ * g.2 * y.2 ∈ L := by
    have := mem_cj (L := M) (x := y) (g := g)
    rw [this, hM]
    rfl
  rw [Subgroup.mem_inf, hc, hΔ, mem_map_dg, Subgroup.mem_inf, Subgroup.mem_inf, mem_cj, mem_cj]
  constructor
  · rintro ⟨⟨e, hz⟩, h1, h2⟩
    exact ⟨e, ⟨hz, h1⟩, e ▸ h2⟩
  · rintro ⟨e, ⟨hz, h1⟩, h2⟩
    exact ⟨⟨e, hz⟩, h1, e ▸ h2⟩

noncomputable def wt (Z L C : Subgroup H) (y : H × H) : ℕ :=
  ((Z ⊓ cj L y.1) ⊓ cj L y.2).relIndex C

/- English proof (translation)
Rewrite using `[inf_diag hΔ hM, Subgroup.relIndex_map_map_of_injective _ _ dg_injective, wt]`.
-/
theorem relIndex_diag {Z L : Subgroup H} {Δ M : Subgroup (H × H)}
    (hΔ : ∀ g, g ∈ Δ ↔ g.1 = g.2 ∧ g.1 ∈ Z) (hM : ∀ g, g ∈ M ↔ g.1 ∈ L ∧ g.2 ∈ L)
    (C : Subgroup H) (y : H × H) :
    (Δ ⊓ M.map (MulAut.conj y).toMonoidHom).relIndex (C.map dg) = wt Z L C y := by
  rw [inf_diag hΔ hM, Subgroup.relIndex_map_map_of_injective _ _ dg_injective, wt]

/- English proof (translation)
Use extensionality with `g`. Rewrite using `[mem_cj, mem_cj]`. Establish `e : (x * l)⁻¹ * g * (x * l) = l⁻¹ * (x⁻¹ * g * x) * l` using `by group`. Rewrite using `[e]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `L.mul_mem (L.mul_mem hl h) (L.inv_mem hl)` as an intermediate fact. Establish `e2 : l * (l⁻¹ * (x⁻¹ * g * x) * l) * l⁻¹ = x⁻¹ * g * x` using `by group`. Rewrite `this` using `[e2]`. Then use the resulting hypothesis. Introduce `h`.

Conclude with `L.mul_mem (L.mul_mem (L.inv_mem hl) h) hl`.
-/
theorem cj_mul_right {L : Subgroup H} {l : H} (hl : l ∈ L) (x : H) : cj L (x * l) = cj L x := by
  ext g
  rw [mem_cj, mem_cj]
  have e : (x * l)⁻¹ * g * (x * l) = l⁻¹ * (x⁻¹ * g * x) * l := by group
  rw [e]
  constructor
  · intro h
    have := L.mul_mem (L.mul_mem hl h) (L.inv_mem hl)
    have e2 : l * (l⁻¹ * (x⁻¹ * g * x) * l) * l⁻¹ = x⁻¹ * g * x := by group
    rwa [e2] at this
  · intro h
    exact L.mul_mem (L.mul_mem (L.inv_mem hl) h) hl

/- English proof (translation)
Use extensionality with `g`. Rewrite using `[mem_cj, mem_cj, mem_cj]`. Establish `e : (t * x)⁻¹ * g * (t * x) = x⁻¹ * (t⁻¹ * g * t) * x` using `by group`. Rewrite using `[e]`.
-/
theorem cj_mul_left (L : Subgroup H) (t x : H) : cj L (t * x) = cj (cj L x) t := by
  ext g
  rw [mem_cj, mem_cj, mem_cj]
  have e : (t * x)⁻¹ * g * (t * x) = x⁻¹ * (t⁻¹ * g * t) * x := by group
  rw [e]

/- English proof (translation)
Use extensionality with `g`. Rewrite using `[mem_cj]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `h1 _ h` as an intermediate fact.

Establish `e : t * (t⁻¹ * g * t) * t⁻¹ = g` using `by group`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Conclude with `h2 g`.
-/
theorem cj_eq_self {K : Subgroup H} {t : H} (h1 : ∀ c ∈ K, t * c * t⁻¹ ∈ K)
    (h2 : ∀ c ∈ K, t⁻¹ * c * t ∈ K) : cj K t = K := by
  ext g
  rw [mem_cj]
  constructor
  · intro h
    have := h1 _ h
    have e : t * (t⁻¹ * g * t) * t⁻¹ = g := by group
    rwa [e] at this
  · exact h2 g

/- English proof (translation)
The claim follows from `(MulAut.conj t).injective`.
-/
theorem conj_injective (t : H) : Function.Injective (MulAut.conj t).toMonoidHom :=
  (MulAut.conj t).injective

/- English proof (translation)
Establish `hZ : cj Z t = Z` using `cj_eq_self (fun c hc => Z.mul_mem (Z.mul_mem ht hc) (Z.inv_mem ht)) (fun c hc => Z.mul_mem (Z.mul_mem (Z.inv_mem ht) hc) ht)`. Establish `hCt : cj C t = C` using `cj_eq_self (hC t ht) (fun c hc => by`. Use `hC t⁻¹ (Z.inv_mem ht) c hc` as an intermediate fact. Rewrite using `[inv_inv] at this)` and apply the resulting hypothesis. Simplify using `only [wt]`.

Rewrite using `[cj_mul_right hl, cj_mul_right hl', cj_mul_left, cj_mul_left]`. Establish `e : (Z ⊓ cj (cj L x) t) ⊓ cj (cj L h) t = cj ((Z ⊓ cj L x) ⊓ cj L h) t`. Unfold `cj`. Rewrite using `[Subgroup.map_inf _ _ _ (conj_injective t), Subgroup.map_inf _ _ _ (conj_injective t)]`. Conclude with `congrArg (· ⊓ _) (congrArg (· ⊓ _) hZ.symm)`.

Rewrite using `[e]`. Use `conv_lhs => rw [← hCt]`. Conclude with `Subgroup.relIndex_map_map_of_injective _ _ (conj_injective t)`.
-/
theorem wt_invariant {Z L C : Subgroup H} (hC : ∀ t ∈ Z, ∀ c ∈ C, t * c * t⁻¹ ∈ C)
    {t l l' : H} (ht : t ∈ Z) (hl : l ∈ L) (hl' : l' ∈ L) (x h : H) :
    wt Z L C (t * x * l, t * h * l') = wt Z L C (x, h) := by
  have hZ : cj Z t = Z := cj_eq_self (fun c hc => Z.mul_mem (Z.mul_mem ht hc) (Z.inv_mem ht))
    (fun c hc => Z.mul_mem (Z.mul_mem (Z.inv_mem ht) hc) ht)
  have hCt : cj C t = C := cj_eq_self (hC t ht) (fun c hc => by
    have := hC t⁻¹ (Z.inv_mem ht) c hc
    rwa [inv_inv] at this)
  simp only [wt]
  rw [cj_mul_right hl, cj_mul_right hl', cj_mul_left, cj_mul_left]
  have e : (Z ⊓ cj (cj L x) t) ⊓ cj (cj L h) t = cj ((Z ⊓ cj L x) ⊓ cj L h) t := by
    unfold cj
    rw [Subgroup.map_inf _ _ _ (conj_injective t), Subgroup.map_inf _ _ _ (conj_injective t)]
    exact congrArg (· ⊓ _) (congrArg (· ⊓ _) hZ.symm)
  rw [e]
  conv_lhs => rw [← hCt]
  exact Subgroup.relIndex_map_map_of_injective _ _ (conj_injective t)

section Classes

variable {Z L : Subgroup H} {Δ M : Subgroup (H × H)}

/- English proof (translation)
Rewrite using `[DoubleCoset.eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨d, hd, m, hm, e⟩`. Take `⟨e1, hz⟩` from `(hΔ d).1 hd`. Take `⟨m1, m2⟩` from `(hM m).1 hm`.

Use `⟨d.1, hz, m.1, m1, m.2, m2, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Both sides reduce to the same expression. Rewrite using `[e, e1]`. Both sides reduce to the same expression.

Introduce and unpack `⟨t, ht, l, hl, l', hl', e1, e2⟩`. Conclude with `⟨(t, t), (hΔ _).2 ⟨rfl, ht⟩, (l, l'), (hM _).2 ⟨hl, hl'⟩, Prod.ext e1 e2⟩`.
-/
theorem mk_eq_iff (hΔ : ∀ g, g ∈ Δ ↔ g.1 = g.2 ∧ g.1 ∈ Z) (hM : ∀ g, g ∈ M ↔ g.1 ∈ L ∧ g.2 ∈ L)
    (y y' : H × H) :
    DoubleCoset.mk Δ M y = DoubleCoset.mk Δ M y' ↔
      ∃ t ∈ Z, ∃ l ∈ L, ∃ l' ∈ L, y'.1 = t * y.1 * l ∧ y'.2 = t * y.2 * l' := by
  rw [DoubleCoset.eq]
  constructor
  · rintro ⟨d, hd, m, hm, e⟩
    obtain ⟨e1, hz⟩ := (hΔ d).1 hd
    obtain ⟨m1, m2⟩ := (hM m).1 hm
    refine ⟨d.1, hz, m.1, m1, m.2, m2, ?_, ?_⟩
    · rw [e]
      rfl
    · rw [e, e1]
      rfl
  · rintro ⟨t, ht, l, hl, l', hl', e1, e2⟩
    exact ⟨(t, t), (hΔ _).2 ⟨rfl, ht⟩, (l, l'), (hM _).2 ⟨hl, hl'⟩, Prod.ext e1 e2⟩

/- English proof (translation)
Take `⟨t, ht, l, hl, l', hl', e1, e2⟩` from `(mk_eq_iff hΔ hM y (Quotient.out (DoubleCoset.mk Δ M y))).1 (DoubleCoset.out_eq' Δ M (DoubleCoset.mk Δ M y)).symm`. Establish `e : Quotient.out (DoubleCoset.mk Δ M y) = (t * y.1 * l, t * y.2 * l')` using `Prod.ext e1 e2`. Rewrite using `[e]`. Conclude with `hG t ht l hl l' hl' y.1 y.2`.
-/
theorem out_invariant {α : Type} (hΔ : ∀ g, g ∈ Δ ↔ g.1 = g.2 ∧ g.1 ∈ Z)
    (hM : ∀ g, g ∈ M ↔ g.1 ∈ L ∧ g.2 ∈ L) (G : H × H → α)
    (hG : ∀ t ∈ Z, ∀ l ∈ L, ∀ l' ∈ L, ∀ x h, G (t * x * l, t * h * l') = G (x, h)) (y : H × H) :
    G (Quotient.out (DoubleCoset.mk Δ M y)) = G y := by
  obtain ⟨t, ht, l, hl, l', hl', e1, e2⟩ :=
    (mk_eq_iff hΔ hM y (Quotient.out (DoubleCoset.mk Δ M y))).1
      (DoubleCoset.out_eq' Δ M (DoubleCoset.mk Δ M y)).symm
  have e : Quotient.out (DoubleCoset.mk Δ M y) = (t * y.1 * l, t * y.2 * l') := Prod.ext e1 e2
  rw [e]
  exact hG t ht l hl l' hl' y.1 y.2

variable (Z L Δ M) in

noncomputable def proj (Q : DoubleCoset.Quotient (Δ : Set (H × H)) (M : Set (H × H))) :
    DoubleCoset.Quotient (Z : Set H) (L : Set H) :=
  DoubleCoset.mk Z L (Quotient.out Q).1

variable (Z L Δ M) in

noncomputable def lift (q : DoubleCoset.Quotient (Z : Set H) (L : Set H)) (p : H ⧸ L) :
    DoubleCoset.Quotient (Δ : Set (H × H)) (M : Set (H × H)) :=
  DoubleCoset.mk Δ M (Quotient.out q, p.out)

/- English proof (translation)
Take `⟨t, ht, l, hl, l', hl', e1, -⟩` from `(mk_eq_iff hΔ hM (Quotient.out (DoubleCoset.mk Δ M y)) y).1 (DoubleCoset.out_eq' Δ M (DoubleCoset.mk Δ M y))`. Rewrite using `[proj, DoubleCoset.eq]`. Conclude with `⟨t, ht, l, hl, e1⟩`.
-/
theorem proj_mk (hΔ : ∀ g, g ∈ Δ ↔ g.1 = g.2 ∧ g.1 ∈ Z) (hM : ∀ g, g ∈ M ↔ g.1 ∈ L ∧ g.2 ∈ L)
    (y : H × H) : proj Z L Δ M (DoubleCoset.mk Δ M y) = DoubleCoset.mk Z L y.1 := by
  obtain ⟨t, ht, l, hl, l', hl', e1, -⟩ :=
    (mk_eq_iff hΔ hM (Quotient.out (DoubleCoset.mk Δ M y)) y).1
      (DoubleCoset.out_eq' Δ M (DoubleCoset.mk Δ M y))
  rw [proj, DoubleCoset.eq]
  exact ⟨t, ht, l, hl, e1⟩

/- English proof (translation)
Rewrite using `[lift, proj_mk hΔ hM]`. Conclude with `DoubleCoset.out_eq' Z L q`.
-/
theorem proj_lift (hΔ : ∀ g, g ∈ Δ ↔ g.1 = g.2 ∧ g.1 ∈ Z) (hM : ∀ g, g ∈ M ↔ g.1 ∈ L ∧ g.2 ∈ L)
    (q : DoubleCoset.Quotient (Z : Set H) (L : Set H)) (p : H ⧸ L) :
    proj Z L Δ M (lift Z L Δ M q p) = q := by
  rw [lift, proj_mk hΔ hM]
  exact DoubleCoset.out_eq' Z L q

/- English proof (translation)
Take `⟨t, ht, l, hl, e⟩` from `(DoubleCoset.eq Z L (Quotient.out (proj Z L Δ M Q)) (Quotient.out Q).1).1 (DoubleCoset.out_eq' Z L (proj Z L Δ M Q))`. Use `⟨t⁻¹ * (Quotient.out Q).2, Eq.trans ?_ (DoubleCoset.out_eq' Δ M Q)⟩` and prove the remaining obligations. Rewrite using `[mk_eq_iff hΔ hM]`. Conclude with `⟨t, ht, l, hl, 1, L.one_mem, e, by simp⟩`.
-/
theorem exists_rep (hΔ : ∀ g, g ∈ Δ ↔ g.1 = g.2 ∧ g.1 ∈ Z) (hM : ∀ g, g ∈ M ↔ g.1 ∈ L ∧ g.2 ∈ L)
    (Q : DoubleCoset.Quotient (Δ : Set (H × H)) (M : Set (H × H))) :
    ∃ h : H, DoubleCoset.mk Δ M (Quotient.out (proj Z L Δ M Q), h) = Q := by
  obtain ⟨t, ht, l, hl, e⟩ := (DoubleCoset.eq Z L (Quotient.out (proj Z L Δ M Q))
    (Quotient.out Q).1).1 (DoubleCoset.out_eq' Z L (proj Z L Δ M Q))
  refine ⟨t⁻¹ * (Quotient.out Q).2, Eq.trans ?_ (DoubleCoset.out_eq' Δ M Q)⟩
  rw [mk_eq_iff hΔ hM]
  exact ⟨t, ht, l, hl, 1, L.one_mem, e, by simp⟩

/- English proof (translation)
Use extensionality with `p`. Simplify using `only [Set.mem_ofPred_eq, MulAction.mem_orbit_iff]`. Rewrite using `[mk_eq_iff hΔ hM]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, l, hl, l', hl', e1, e2⟩`.

Establish `e1' : x = t * x * l` using `e1`. Establish `e2' : h = t * p.out * l'` using `e2`. Establish `hb : t⁻¹ ∈ cj L x`. Rewrite using `[mem_cj]`. Establish `: x⁻¹ * t⁻¹ * x = l`.

Establish `: t⁻¹ * x = x * l`. Rewrite using `[inv_mul_eq_iff_eq_mul, ← mul_assoc]`. Conclude with `e1'`. Rewrite using `[mul_assoc, this]`. Use `group`.

Rewrite using `[this]`. Conclude with `hl`. Use `⟨⟨t⁻¹, Subgroup.mem_inf.2 ⟨Z.inv_mem ht, hb⟩⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(QuotientGroup.mk (t⁻¹ * h) : H ⧸ L) = p`. Establish `hq : (QuotientGroup.mk (t⁻¹ * h) : H ⧸ L) = QuotientGroup.mk p.out`.

Rewrite using `[QuotientGroup.eq]`. Establish `: (t⁻¹ * h)⁻¹ * p.out = l'⁻¹`. Rewrite using `[e2']`. Use `group`. Rewrite using `[this]`.

Conclude with `L.inv_mem hl'`. Rewrite using `[hq, QuotientGroup.out_eq']`. Introduce and unpack `⟨⟨b, hb⟩, e⟩`. Take `⟨hbZ, hbL⟩` from `Subgroup.mem_inf.1 hb`. Establish `e' : (QuotientGroup.mk (b * h) : H ⧸ L) = p` using `e`.

Establish `hq : (QuotientGroup.mk (b * h) : H ⧸ L) = QuotientGroup.mk p.out`. Rewrite using `[e', QuotientGroup.out_eq']`. Rewrite `hq` using `[QuotientGroup.eq]`. Rewrite `hbL` using `[mem_cj]`. Establish `hl2 : p.out⁻¹ * (b * h) ∈ L`.

Use `L.inv_mem hq` as an intermediate fact. Establish `e3 : ((b * h)⁻¹ * p.out)⁻¹ = p.out⁻¹ * (b * h)` using `by group`. Rewrite `this` using `[e3]`. Then use the resulting hypothesis. Use `⟨b⁻¹, Z.inv_mem hbZ, x⁻¹ * b * x, hbL, p.out⁻¹ * (b * h), hl2, ?_, ?_⟩` and prove the remaining obligations. Use `show x = b⁻¹ * x * (x⁻¹ * b * x) group`.

Use `show h = b⁻¹ * p.out * (p.out⁻¹ * (b * h)) group`.
-/
theorem fiber_eq_orbit (hΔ : ∀ g, g ∈ Δ ↔ g.1 = g.2 ∧ g.1 ∈ Z)
    (hM : ∀ g, g ∈ M ↔ g.1 ∈ L ∧ g.2 ∈ L) (x h : H) :
    {p : H ⧸ L | DoubleCoset.mk Δ M (x, p.out) = DoubleCoset.mk Δ M (x, h)} =
      MulAction.orbit (Z ⊓ cj L x : Subgroup H) (QuotientGroup.mk h : H ⧸ L) := by
  ext p
  simp only [Set.mem_ofPred_eq, MulAction.mem_orbit_iff]
  rw [mk_eq_iff hΔ hM]
  constructor
  · rintro ⟨t, ht, l, hl, l', hl', e1, e2⟩
    have e1' : x = t * x * l := e1
    have e2' : h = t * p.out * l' := e2
    have hb : t⁻¹ ∈ cj L x := by
      rw [mem_cj]
      have : x⁻¹ * t⁻¹ * x = l := by
        have : t⁻¹ * x = x * l := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc]
          exact e1'
        rw [mul_assoc, this]
        group
      rw [this]
      exact hl
    refine ⟨⟨t⁻¹, Subgroup.mem_inf.2 ⟨Z.inv_mem ht, hb⟩⟩, ?_⟩
    change (QuotientGroup.mk (t⁻¹ * h) : H ⧸ L) = p
    have hq : (QuotientGroup.mk (t⁻¹ * h) : H ⧸ L) = QuotientGroup.mk p.out := by
      rw [QuotientGroup.eq]
      have : (t⁻¹ * h)⁻¹ * p.out = l'⁻¹ := by
        rw [e2']
        group
      rw [this]
      exact L.inv_mem hl'
    rw [hq, QuotientGroup.out_eq']
  · rintro ⟨⟨b, hb⟩, e⟩
    obtain ⟨hbZ, hbL⟩ := Subgroup.mem_inf.1 hb
    have e' : (QuotientGroup.mk (b * h) : H ⧸ L) = p := e
    have hq : (QuotientGroup.mk (b * h) : H ⧸ L) = QuotientGroup.mk p.out := by
      rw [e', QuotientGroup.out_eq']
    rw [QuotientGroup.eq] at hq
    rw [mem_cj] at hbL
    have hl2 : p.out⁻¹ * (b * h) ∈ L := by
      have := L.inv_mem hq
      have e3 : ((b * h)⁻¹ * p.out)⁻¹ = p.out⁻¹ * (b * h) := by group
      rwa [e3] at this
    refine ⟨b⁻¹, Z.inv_mem hbZ, x⁻¹ * b * x, hbL, p.out⁻¹ * (b * h), hl2, ?_, ?_⟩
    · show x = b⁻¹ * x * (x⁻¹ * b * x)
      group
    · show h = b⁻¹ * p.out * (p.out⁻¹ * (b * h))
      group

/- English proof (translation)
Rewrite using `[← MulAction.index_stabilizer, Subgroup.relIndex]`. Use `congr 1`. Use extensionality with `b`. Rewrite using `[MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_cj]`. Express the relevant statement in the definitionally equal form `(QuotientGroup.mk ((b : H) * h) : H ⧸ L) = QuotientGroup.mk h ↔ _`.

Rewrite using `[eq_comm, QuotientGroup.eq]`. Establish `e : h⁻¹ * ((b : H) * h) = h⁻¹ * b * h` using `by group`. Rewrite using `[e]`. Conclude with `⟨fun hh => ⟨b.2, hh⟩, fun hh => hh.2⟩`.
-/
theorem ncard_orbit (L B : Subgroup H) (h : H) :
    (MulAction.orbit B (QuotientGroup.mk h : H ⧸ L)).ncard = (B ⊓ cj L h).relIndex B := by
  rw [← MulAction.index_stabilizer, Subgroup.relIndex]
  congr 1
  ext b
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_cj]
  change (QuotientGroup.mk ((b : H) * h) : H ⧸ L) = QuotientGroup.mk h ↔ _
  rw [eq_comm, QuotientGroup.eq]
  have e : h⁻¹ * ((b : H) * h) = h⁻¹ * b * h := by group
  rw [e]
  exact ⟨fun hh => ⟨b.2, hh⟩, fun hh => hh.2⟩

/- English proof (translation)
Take `⟨h, hh⟩` from `exists_rep (Z := Z) (L := L) hΔ hM Q`. Establish `hw` using `out_invariant hΔ hM (wt Z L C) (fun t ht l hl l' hl' x h => wt_invariant h2 ht hl hl' x h) (Quotient.out (proj Z L Δ M Q), h)`. Rewrite `hw` using `[hh]`. Establish `hset : lift Z L Δ M (proj Z L Δ M Q) ⁻¹' {Q} = MulAction.orbit (Z ⊓ cj L (Quotient.out (proj Z L Δ M Q)) : Subgroup H) (QuotientGroup.mk h : H ⧸ L)`. Rewrite using `[← fiber_eq_orbit hΔ hM, hh]`.

Both sides reduce to the same expression. Establish `hmul` using `Subgroup.relIndex_mul_relIndex ((Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) ⊓ cj L h) (Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) C inf_le_left (h1 (Quotient.out (proj Z L Δ M Q))).1`. Establish `hA : ((Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) ⊓ cj L h).relIndex C ≠ 0`. Use `Subgroup.relIndex_inf_ne_zero (h1 (Quotient.out (proj Z L Δ M Q))).2 (h1 h).2` as an intermediate fact. Establish `e : (Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) ⊓ (Z ⊓ cj L h) = (Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) ⊓ cj L h` using `le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_right)) (le_inf inf_le_left (le_inf (inf_le_left.trans inf_le_left) inf_le_right))`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `hB : ((Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) ⊓ cj L h).relIndex (Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) ≠ 0`. Introduce `h0`. Rewrite `hmul` using `[h0, zero_mul]`. Conclude with `hA hmul.symm`.

Establish `hcard` using `ncard_orbit L (Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hset]`. Conclude with `Set.finite_of_ncard_ne_zero (hcard ▸ hB)`. Rewrite using `[hset, Nat.card_coe_set_eq, hcard, hw] show ((Z ⊓ cj L _) ⊓ cj L h).relIndex C = _`.

Rewrite using `[← hmul, mul_comm]`.
-/
theorem weight_fiber {C : Subgroup H} (hΔ : ∀ g, g ∈ Δ ↔ g.1 = g.2 ∧ g.1 ∈ Z)
    (hM : ∀ g, g ∈ M ↔ g.1 ∈ L ∧ g.2 ∈ L)
    (h1 : ∀ x : H, Z ⊓ cj L x ≤ C ∧ (Z ⊓ cj L x).relIndex C ≠ 0)
    (h2 : ∀ t ∈ Z, ∀ c ∈ C, t * c * t⁻¹ ∈ C)
    (Q : DoubleCoset.Quotient (Δ : Set (H × H)) (M : Set (H × H))) :
    (lift Z L Δ M (proj Z L Δ M Q) ⁻¹' {Q}).Finite ∧
      wt Z L C (Quotient.out Q) = (Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))).relIndex C *
        Nat.card (lift Z L Δ M (proj Z L Δ M Q) ⁻¹' {Q}) := by
  obtain ⟨h, hh⟩ := exists_rep (Z := Z) (L := L) hΔ hM Q
  have hw := out_invariant hΔ hM (wt Z L C)
    (fun t ht l hl l' hl' x h => wt_invariant h2 ht hl hl' x h) (Quotient.out (proj Z L Δ M Q), h)
  rw [hh] at hw
  have hset : lift Z L Δ M (proj Z L Δ M Q) ⁻¹' {Q} =
      MulAction.orbit (Z ⊓ cj L (Quotient.out (proj Z L Δ M Q)) : Subgroup H)
        (QuotientGroup.mk h : H ⧸ L) := by
    rw [← fiber_eq_orbit hΔ hM, hh]
    rfl
  have hmul := Subgroup.relIndex_mul_relIndex
    ((Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) ⊓ cj L h)
    (Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) C inf_le_left
    (h1 (Quotient.out (proj Z L Δ M Q))).1
  have hA : ((Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) ⊓ cj L h).relIndex C ≠ 0 := by
    have := Subgroup.relIndex_inf_ne_zero (h1 (Quotient.out (proj Z L Δ M Q))).2 (h1 h).2
    have e : (Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) ⊓ (Z ⊓ cj L h) =
        (Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) ⊓ cj L h :=
      le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_right))
        (le_inf inf_le_left (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
    rwa [e] at this
  have hB : ((Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) ⊓ cj L h).relIndex
      (Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact hA hmul.symm
  have hcard := ncard_orbit L (Z ⊓ cj L (Quotient.out (proj Z L Δ M Q))) h
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact Set.finite_of_ncard_ne_zero (hcard ▸ hB)
  · rw [hset, Nat.card_coe_set_eq, hcard, hw]
    show ((Z ⊓ cj L _) ⊓ cj L h).relIndex C = _
    rw [← hmul, mul_comm]

end Classes

/- English proof (translation)
Establish `hF : ∀ t ∈ Z, ∀ l ∈ L, ∀ l' ∈ L, ∀ x h, F (t * x * l, t * h * l') = F (x, h)`. Introduce `t ht l hl l' hl' x h`. Rewrite using `[h4 l hl l' hl', h3 t ht]`. Establish `hw` using `weight_fiber (C := C) hΔ hM h1 h2`. Establish `key` using `abstract_sum (proj Z L Δ M) (lift Z L Δ M) (proj_lift hΔ hM) (fun Q => F (Quotient.out Q)) hfin (fun q => (((Z ⊓ L.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ)) (fun Q _ => (hw Q).1)`.

Establish `hR : ∀ q : DoubleCoset.Quotient (Z : Set H) (L : Set H), (∑ᶠ p : H ⧸ L, F (Quotient.out (lift Z L Δ M q p))) = ∑ᶠ p : H ⧸ L, F (Quotient.out q, p.out)` using `fun q => finsum_congr fun p => out_invariant hΔ hM F hF _`. Simplify using `only [hR] at key`. Rewrite using `[← key]`. Use `finsum_congr fun Q => ?_` and prove the remaining obligations. Establish `e` using `relIndex_diag hΔ hM C (Quotient.out Q)`.

Rewrite using `[e, (hw Q).2]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem orbit_count_gen (Z L C : Subgroup H) (Δ M : Subgroup (H × H))
    (hΔ : ∀ g, g ∈ Δ ↔ g.1 = g.2 ∧ g.1 ∈ Z) (hM : ∀ g, g ∈ M ↔ g.1 ∈ L ∧ g.2 ∈ L)
    (F : H × H → ℂ)
    (h1 : ∀ x : H, Z ⊓ L.map (MulAut.conj x).toMonoidHom ≤ C ∧
      (Z ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0)
    (h2 : ∀ t ∈ Z, ∀ c ∈ C, t * c * t⁻¹ ∈ C)
    (h3 : ∀ t ∈ Z, ∀ x h, F (t * x, t * h) = F (x, h))
    (h4 : ∀ l ∈ L, ∀ l' ∈ L, ∀ x h, F (x * l, h * l') = F (x, h))
    (hfin : {Q : DoubleCoset.Quotient (Δ : Set (H × H)) (M : Set (H × H)) |
      F (Quotient.out Q) ≠ 0}.Finite) :
    ∑ᶠ Q : DoubleCoset.Quotient (Δ : Set (H × H)) (M : Set (H × H)),
        (((Δ ⊓ M.map (MulAut.conj (Quotient.out Q)).toMonoidHom).relIndex
          (C.map ((MonoidHom.id H).prod (MonoidHom.id H))) : ℕ) : ℂ) * F (Quotient.out Q) =
      ∑ᶠ q : DoubleCoset.Quotient (Z : Set H) (L : Set H),
        (((Z ⊓ L.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ) *
          ∑ᶠ p : H ⧸ L, F (Quotient.out q, p.out) := by
  have hF : ∀ t ∈ Z, ∀ l ∈ L, ∀ l' ∈ L, ∀ x h, F (t * x * l, t * h * l') = F (x, h) := by
    intro t ht l hl l' hl' x h
    rw [h4 l hl l' hl', h3 t ht]
  have hw := weight_fiber (C := C) hΔ hM h1 h2
  have key := abstract_sum (proj Z L Δ M) (lift Z L Δ M) (proj_lift hΔ hM)
    (fun Q => F (Quotient.out Q)) hfin
    (fun q => (((Z ⊓ L.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ))
    (fun Q _ => (hw Q).1)
  have hR : ∀ q : DoubleCoset.Quotient (Z : Set H) (L : Set H),
      (∑ᶠ p : H ⧸ L, F (Quotient.out (lift Z L Δ M q p))) =
        ∑ᶠ p : H ⧸ L, F (Quotient.out q, p.out) := fun q =>
    finsum_congr fun p => out_invariant hΔ hM F hF _
  simp only [hR] at key
  rw [← key]
  refine finsum_congr fun Q => ?_
  have e := relIndex_diag hΔ hM C (Quotient.out Q)
  rw [e, (hw Q).2]
  push_cast
  rfl

/- English proof (translation)
Introduce `H _ Z L C F h1 h2 h3 h4 hfin`. Conclude with `orbit_count_gen Z L C _ _ (fun g => mem_map_dg) (fun g => Subgroup.mem_prod) F h1 h2 h3 h4 hfin`.
-/
theorem orbit_count : ∀ (H : Type) [Group H] (Z L C : Subgroup H) (F : H × H → ℂ),
  (∀ x : H, Z ⊓ L.map (MulAut.conj x).toMonoidHom ≤ C ∧ (Z ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0) →
  (∀ t ∈ Z, ∀ c ∈ C, t * c * t⁻¹ ∈ C) →
  (∀ t ∈ Z, ∀ x h, F (t * x, t * h) = F (x, h)) →
  (∀ l ∈ L, ∀ l' ∈ L, ∀ x h, F (x * l, h * l') = F (x, h)) →
  {Q : DoubleCoset.Quotient ((Z.map ((MonoidHom.id H).prod (MonoidHom.id H)) : Subgroup (H × H)) : Set (H × H)) ((L.prod L : Subgroup (H × H)) : Set (H × H)) | F (Quotient.out Q) ≠ 0}.Finite →
  ∑ᶠ Q : DoubleCoset.Quotient ((Z.map ((MonoidHom.id H).prod (MonoidHom.id H)) : Subgroup (H × H)) : Set (H × H)) ((L.prod L : Subgroup (H × H)) : Set (H × H)),
      (((Z.map ((MonoidHom.id H).prod (MonoidHom.id H)) ⊓ (L.prod L).map (MulAut.conj (Quotient.out Q)).toMonoidHom).relIndex (C.map ((MonoidHom.id H).prod (MonoidHom.id H))) : ℕ) : ℂ) * F (Quotient.out Q) =
    ∑ᶠ q : DoubleCoset.Quotient (Z : Set H) (L : Set H),
      (((Z ⊓ L.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ) * ∑ᶠ p : H ⧸ L, F (Quotient.out q, p.out) := by
  intro H _ Z L C F h1 h2 h3 h4 hfin
  exact orbit_count_gen Z L C _ _
    (fun g => mem_map_dg) (fun g => Subgroup.mem_prod) F h1 h2 h3 h4 hfin

end GlobalTheory.CompanionTheory.OrbitCount
