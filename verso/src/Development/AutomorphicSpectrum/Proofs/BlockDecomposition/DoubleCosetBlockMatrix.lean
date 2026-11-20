import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemma
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.GeoCell

open GroundTheory.Automorphic.Parabolic

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hxy`. Assume the negation of the conclusion as `hne`. Break down `lt_or_gt_of_ne hne with h1 | h1` into its components or cases. Use `(h _ _).2 h1` as an intermediate fact.

Rewrite `this` using `[hxy]`. Conclude with `lt_irrefl _ this`. Use `(h _ _).2 h1` as an intermediate fact. Rewrite `this` using `[hxy]`. Conclude with `lt_irrefl _ this`.

Introduce `hxy`. Assume the negation of the conclusion as `hne`. Break down `lt_or_gt_of_ne hne with h1 | h1` into its components or cases. Use `(h _ _).1 h1` as an intermediate fact. Rewrite `this` using `[hxy]`.

Conclude with `lt_irrefl _ this`. Use `(h _ _).1 h1` as an intermediate fact. Rewrite `this` using `[hxy]`. Conclude with `lt_irrefl _ this`.
-/
theorem eq_iff_of_lt_iff {C A B : Type} [LinearOrder A] [LinearOrder B] (f : C → A) (g : C → B)
    (h : ∀ x y, f x < f y ↔ g x < g y) (x y : C) : f x = f y ↔ g x = g y := by
  constructor
  · intro hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have := (h _ _).2 h1
      rw [hxy] at this
      exact lt_irrefl _ this
    · have := (h _ _).2 h1
      rw [hxy] at this
      exact lt_irrefl _ this
  · intro hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have := (h _ _).1 h1
      rw [hxy] at this
      exact lt_irrefl _ this
    · have := (h _ _).1 h1
      rw [hxy] at this
      exact lt_irrefl _ this

/- English proof (translation)
Establish `h1 : ∀ a b, (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (w j)).card = (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (w' j)).card`. Introduce `a b`. Consider the cases of `b with`. Consider the case `zero => simpa using h a 0`. Consider the case `succ b`.

Establish `key : ∀ u : Equiv.Perm (Fin n), (Finset.univ.filter fun j => γ j ≤ b + 1 ∧ a ≤ β (u j)).card = (Finset.univ.filter fun j => γ j = b + 1 ∧ a ≤ β (u j)).card + (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (u j)).card`. Introduce `u`. Rewrite using `[← Finset.card_union_of_disjoint]`. Use `congr 1`. Use extensionality with `j`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.disjoint_filter]`. Introduce `j _ h1 h2`. Use linear arithmetic over natural numbers and integers.

Use `h a (b + 1)` as an intermediate fact. Rewrite `this` using `[key w, key w', h a b]`. Use linear arithmetic over natural numbers and integers. Establish `key : ∀ u : Equiv.Perm (Fin n), (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (u j)).card = (Finset.univ.filter fun j => γ j = b ∧ β (u j) = a).card + (Finset.univ.filter fun j => γ j = b ∧ a + 1 ≤ β (u j)).card`. Introduce `u`.

Rewrite using `[← Finset.card_union_of_disjoint]`. Use `congr 1`. Use extensionality with `j`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Finset.disjoint_filter]`. Introduce `j _ h1 h2`. Use linear arithmetic over natural numbers and integers. Use `h1 a b` as an intermediate fact. Rewrite `this` using `[key w, key w', h1 (a + 1) b]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem card_cell_of_card_corner {n : ℕ} {β γ : Fin n → ℕ} {w w' : Equiv.Perm (Fin n)}
    (h : ∀ a b, (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w j)).card =
      (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w' j)).card) (a b : ℕ) :
    (Finset.univ.filter fun j => γ j = b ∧ β (w j) = a).card =
      (Finset.univ.filter fun j => γ j = b ∧ β (w' j) = a).card := by
  classical
  have h1 : ∀ a b, (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (w j)).card =
      (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (w' j)).card := by
    intro a b
    cases b with
    | zero => simpa using h a 0
    | succ b =>
      have key : ∀ u : Equiv.Perm (Fin n),
          (Finset.univ.filter fun j => γ j ≤ b + 1 ∧ a ≤ β (u j)).card =
            (Finset.univ.filter fun j => γ j = b + 1 ∧ a ≤ β (u j)).card +
              (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (u j)).card := by
        intro u
        rw [← Finset.card_union_of_disjoint]
        · congr 1
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
          omega
        · rw [Finset.disjoint_filter]
          intro j _ h1 h2
          omega
      have := h a (b + 1)
      rw [key w, key w', h a b] at this
      omega
  have key : ∀ u : Equiv.Perm (Fin n),
      (Finset.univ.filter fun j => γ j = b ∧ a ≤ β (u j)).card =
        (Finset.univ.filter fun j => γ j = b ∧ β (u j) = a).card +
          (Finset.univ.filter fun j => γ j = b ∧ a + 1 ≤ β (u j)).card := by
    intro u
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      omega
    · rw [Finset.disjoint_filter]
      intro j _ h1 h2
      omega
  have := h1 a b
  rw [key w, key w', h1 (a + 1) b] at this
  omega

/- English proof (translation)
Introduce `k _ _ _ _ α _ _ N m _ _ β' _ _ m' _ _ e β hβ e' γ hγ w w'`. Establish `hβe` using `eq_iff_of_lt_iff β (blk e) hβ`. Establish `hγe` using `eq_iff_of_lt_iff γ (blk e') hγ`. Establish `reidx : ∀ (u : Equiv.Perm (Fin N)) (i : α) (j : β'), (Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (u.symm x) = j).card = (Finset.univ.filter fun y : Fin N => blk e (u y) = i ∧ blk e' y = j).card`. Introduce `u i j`.

Apply `Finset.card_equiv u.symm` to reduce the goal to its premises. Introduce `x`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Introduce `hmem i j`.

Establish `hc : ∀ a b, (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w j)).card = (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w' j)).card`. Introduce `a b`. Rewrite using `[← cellRank_permGL (F := k), ← cellRank_permGL (F := k)]`. Conclude with `(cellRank_of_mem_doubleCoset hmem a b).symm`. Rewrite using `[reidx, reidx]`.

Distinguish the cases in `hi : ∃ x0, blk e x0 = i`. Distinguish the cases in `hj : ∃ y0, blk e' y0 = j`. Take `⟨x0, rfl⟩` from `hi`. Take `⟨y0, rfl⟩` from `hj`. Establish `conv : ∀ u : Equiv.Perm (Fin N), (Finset.univ.filter fun y : Fin N => blk e (u y) = blk e x0 ∧ blk e' y = blk e' y0) = Finset.univ.filter fun y => γ y = γ y0 ∧ β (u y) = β x0`.

Introduce `u`. Use extensionality with `y`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, hβe, hγe]`. The claim follows by propositional logic. Rewrite using `[conv, conv]`.

Conclude with `card_cell_of_card_corner hc _ _`. Establish `hz : ∀ u : Equiv.Perm (Fin N), (Finset.univ.filter fun y : Fin N => blk e (u y) = i ∧ blk e' y = j) = ∅`. Introduce `u`. Use extensionality with `y`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]`.

Conclude with `fun h => hj ⟨y, h.2⟩`. Rewrite using `[hz, hz]`. Establish `hz : ∀ u : Equiv.Perm (Fin N), (Finset.univ.filter fun y : Fin N => blk e (u y) = i ∧ blk e' y = j) = ∅`. Introduce `u`. Use extensionality with `y`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]`. Conclude with `fun h => hi ⟨u y, h.1⟩`. Rewrite using `[hz, hz]`. Introduce `h`. Establish `hcard : ∀ c : α × β', Fintype.card {y : Fin N // (blk e (w y), blk e' y) = c} = Fintype.card {y : Fin N // (blk e (w' y), blk e' y) = c}`.

Introduce `c`. Rewrite using `[Fintype.card_subtype, Fintype.card_subtype]`. Establish `conv : ∀ u : Equiv.Perm (Fin N), (Finset.univ.filter fun y : Fin N => (blk e (u y), blk e' y) = c) = Finset.univ.filter fun y => blk e (u y) = c.1 ∧ blk e' y = c.2`. Introduce `u`. Use extensionality with `y`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]`. Rewrite using `[conv, conv, ← reidx, ← reidx]`. Conclude with `h c.1 c.2`. Set `v : Fin N ≃ Fin N` to `Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hcard c)`. Establish `hv : ∀ j, (blk e (w' (v j)), blk e' (v j)) = (blk e (w j), blk e' j)` using `fun j => Equiv.ofFiberEquiv_map (fun c => Fintype.equivOfCardEq (hcard c)) j`.

Establish `hvβ : ∀ j, β (w' (v j)) = β (w j)` using `fun j => (hβe _ _).2 (Prod.ext_iff.1 (hv j)).1`. Establish `hvγ : ∀ j, γ (v j) = γ j` using `fun j => (hγe _ _).2 (Prod.ext_iff.1 (hv j)).2`. Set `u : Equiv.Perm (Fin N)` to `w' * v * w⁻¹`. Establish `hu : ∀ x, β (u x) = β x`. Introduce `x`.

Simplify using `only [u, Equiv.Perm.mul_apply]`. Rewrite using `[hvβ]`. Simplify using the standard rewrite rules. Establish `hv' : ∀ x, γ ((v⁻¹ : Equiv.Perm (Fin N)) x) = γ x`. Introduce `x`.

Use `hvγ ((v⁻¹ : Equiv.Perm (Fin N)) x)` as an intermediate fact. Establish `h' : v ((v⁻¹ : Equiv.Perm (Fin N)) x) = x` using `Equiv.apply_symm_apply v x`. Rewrite `this` using `[h']`. Conclude with `this.symm`. Use `DoubleCoset.mem_doubleCoset.2 ⟨permGL k u, permGL_mem_blockUpper hu, permGL k v⁻¹, permGL_mem_blockUpper hv', ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_mul, ← map_mul]`. Use `congr 1`. Simplify using `only [u]`. Use `group`.
-/
theorem permGL_mem_doubleCoset_iff_card : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ), (∀ x y, γ x < γ y ↔ blk e' x < blk e' y) → ∀ (w w' : Equiv.Perm (Fin N)), permGL k w' ∈ doubleCoset (permGL k w) (blockUpper k N β : Set (GL (Fin N) k)) (blockUpper k N γ) ↔ ∀ i j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w'.symm x) = j).card) := by
  intro k _ _ _ _ α _ _ N m _ _ β' _ _ m' _ _ e β hβ e' γ hγ w w'
  classical
  have hβe := eq_iff_of_lt_iff β (blk e) hβ
  have hγe := eq_iff_of_lt_iff γ (blk e') hγ
  have reidx : ∀ (u : Equiv.Perm (Fin N)) (i : α) (j : β'),
      (Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (u.symm x) = j).card =
        (Finset.univ.filter fun y : Fin N => blk e (u y) = i ∧ blk e' y = j).card := by
    intro u i j
    apply Finset.card_equiv u.symm
    intro x
    simp
  constructor
  · intro hmem i j
    have hc : ∀ a b, (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w j)).card =
        (Finset.univ.filter fun j => γ j ≤ b ∧ a ≤ β (w' j)).card := by
      intro a b
      rw [← cellRank_permGL (F := k), ← cellRank_permGL (F := k)]
      exact (cellRank_of_mem_doubleCoset hmem a b).symm
    rw [reidx, reidx]
    by_cases hi : ∃ x0, blk e x0 = i
    · by_cases hj : ∃ y0, blk e' y0 = j
      · obtain ⟨x0, rfl⟩ := hi
        obtain ⟨y0, rfl⟩ := hj
        have conv : ∀ u : Equiv.Perm (Fin N),
            (Finset.univ.filter fun y : Fin N => blk e (u y) = blk e x0 ∧ blk e' y = blk e' y0) =
              Finset.univ.filter fun y => γ y = γ y0 ∧ β (u y) = β x0 := by
          intro u
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hβe, hγe]
          tauto
        rw [conv, conv]
        exact card_cell_of_card_corner hc _ _
      · have hz : ∀ u : Equiv.Perm (Fin N),
            (Finset.univ.filter fun y : Fin N => blk e (u y) = i ∧ blk e' y = j) = ∅ := by
          intro u
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          exact fun h => hj ⟨y, h.2⟩
        rw [hz, hz]
    · have hz : ∀ u : Equiv.Perm (Fin N),
          (Finset.univ.filter fun y : Fin N => blk e (u y) = i ∧ blk e' y = j) = ∅ := by
        intro u
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        exact fun h => hi ⟨u y, h.1⟩
      rw [hz, hz]
  · intro h
    have hcard : ∀ c : α × β', Fintype.card {y : Fin N // (blk e (w y), blk e' y) = c} =
        Fintype.card {y : Fin N // (blk e (w' y), blk e' y) = c} := by
      intro c
      rw [Fintype.card_subtype, Fintype.card_subtype]
      have conv : ∀ u : Equiv.Perm (Fin N),
          (Finset.univ.filter fun y : Fin N => (blk e (u y), blk e' y) = c) =
            Finset.univ.filter fun y => blk e (u y) = c.1 ∧ blk e' y = c.2 := by
        intro u
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
      rw [conv, conv, ← reidx, ← reidx]
      exact h c.1 c.2
    let v : Fin N ≃ Fin N := Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hcard c)
    have hv : ∀ j, (blk e (w' (v j)), blk e' (v j)) = (blk e (w j), blk e' j) := fun j =>
      Equiv.ofFiberEquiv_map (fun c => Fintype.equivOfCardEq (hcard c)) j
    have hvβ : ∀ j, β (w' (v j)) = β (w j) := fun j => (hβe _ _).2 (Prod.ext_iff.1 (hv j)).1
    have hvγ : ∀ j, γ (v j) = γ j := fun j => (hγe _ _).2 (Prod.ext_iff.1 (hv j)).2
    let u : Equiv.Perm (Fin N) := w' * v * w⁻¹
    have hu : ∀ x, β (u x) = β x := by
      intro x
      simp only [u, Equiv.Perm.mul_apply]
      rw [hvβ]
      simp
    have hv' : ∀ x, γ ((v⁻¹ : Equiv.Perm (Fin N)) x) = γ x := by
      intro x
      have := hvγ ((v⁻¹ : Equiv.Perm (Fin N)) x)
      have h' : v ((v⁻¹ : Equiv.Perm (Fin N)) x) = x := Equiv.apply_symm_apply v x
      rw [h'] at this
      exact this.symm
    refine DoubleCoset.mem_doubleCoset.2 ⟨permGL k u, permGL_mem_blockUpper hu, permGL k v⁻¹,
      permGL_mem_blockUpper hv', ?_⟩
    rw [← map_mul, ← map_mul]
    congr 1
    simp only [u]
    group

end GlobalTheory.CompanionTheory.GeoCell
