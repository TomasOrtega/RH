import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis

open UpperTheory.Gal UpperTheory.Gal.Int.Geo

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Use `⟨∅, fun _ => 0, linearIndepOn_empty k id, by simp, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Take `rfl : i = 0` from `Nat.le_zero.mp hi`.

Simplify using `[h0]`. Consider the case `succ n ih`. Take `⟨s, lev, hs, hlev, hspan⟩` from `ih`. Establish `hsW : s ⊆ (W (n + 1) : Set V)`. Introduce `x hx`.

Establish `hx' : x ∈ W n`. Rewrite using `[← hspan n le_rfl]`. Conclude with `Submodule.subset_span ⟨hx, hlev x hx⟩`. Conclude with `hW (Nat.le_succ n) hx'`. Take `⟨b, hbt, hsb, htb, hb⟩` from `exists_linearIndepOn_id_extension hs hsW`.

Use `⟨b, fun x => if x ∈ s then lev x else n, hb, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Distinguish the cases in `h : x ∈ s`. Simplify using `only [h, if_true]`. Conclude with `Nat.lt_succ_of_lt (hlev x h)`.

Simplify using `[h]`. Introduce `i hi`. Break down `Nat.lt_or_ge i (n + 1) with hi' | hi'` into its components or cases. Establish `hset : {x | x ∈ b ∧ (if x ∈ s then lev x else n) < i} = {x | x ∈ s ∧ lev x < i}`. Use extensionality with `x`.

Distinguish the cases in `h : x ∈ s`. Simplify using `[h, hsb h]`. Simplify using `only [Set.mem_setOf_eq, h, if_false, false_and, iff_false]`. Introduce and unpack `⟨-, h'⟩`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hset]`. Conclude with `hspan i (Nat.lt_succ_iff.mp hi')`. Establish `hi2 : i = n + 1` using `le_antisymm hi hi'`. Substitute `hi2` using the available equality. Establish `hset : {x | x ∈ b ∧ (if x ∈ s then lev x else n) < n + 1} = b`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.1`. Introduce `hx`. Use `⟨hx, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `h : x ∈ s`. Simplify using `only [h, if_true]`. Conclude with `Nat.lt_succ_of_lt (hlev x h)`. Simplify using `[h]`. Rewrite using `[hset]`.

Apply `le_antisymm` to reduce the goal to its premises. Conclude with `Submodule.span_le.mpr hbt`. Introduce `y hy`. Conclude with `htb hy`.
-/
private theorem exists_linearIndep_levels_span_eq_of_monotone {k : Type} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    (W : ℕ → Submodule k V) (hW : Monotone W) (h0 : W 0 = ⊥) (n : ℕ) :
    ∃ (s : Set V) (lev : V → ℕ), LinearIndepOn k id s ∧ (∀ x ∈ s, lev x < n) ∧
      ∀ i ≤ n, Submodule.span k {x | x ∈ s ∧ lev x < i} = W i := by
  induction n with
  | zero =>
    refine ⟨∅, fun _ => 0, linearIndepOn_empty k id, by simp, ?_⟩
    intro i hi
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    simp [h0]
  | succ n ih =>
    obtain ⟨s, lev, hs, hlev, hspan⟩ := ih
    have hsW : s ⊆ (W (n + 1) : Set V) := by
      intro x hx
      have hx' : x ∈ W n := by
        rw [← hspan n le_rfl]
        exact Submodule.subset_span ⟨hx, hlev x hx⟩
      exact hW (Nat.le_succ n) hx'
    obtain ⟨b, hbt, hsb, htb, hb⟩ := exists_linearIndepOn_id_extension hs hsW
    classical
    refine ⟨b, fun x => if x ∈ s then lev x else n, hb, ?_, ?_⟩
    · intro x hx
      by_cases h : x ∈ s
      · simp only [h, if_true]
        exact Nat.lt_succ_of_lt (hlev x h)
      · simp [h]
    · intro i hi
      rcases Nat.lt_or_ge i (n + 1) with hi' | hi'
      · have hset : {x | x ∈ b ∧ (if x ∈ s then lev x else n) < i} = {x | x ∈ s ∧ lev x < i} := by
          ext x
          by_cases h : x ∈ s
          · simp [h, hsb h]
          · simp only [Set.mem_setOf_eq, h, if_false, false_and, iff_false]
            rintro ⟨-, h'⟩
            omega
        rw [hset]
        exact hspan i (Nat.lt_succ_iff.mp hi')
      · have hi2 : i = n + 1 := le_antisymm hi hi'
        subst hi2
        have hset : {x | x ∈ b ∧ (if x ∈ s then lev x else n) < n + 1} = b := by
          ext x
          constructor
          · exact fun h => h.1
          · intro hx
            refine ⟨hx, ?_⟩
            by_cases h : x ∈ s
            · simp only [h, if_true]
              exact Nat.lt_succ_of_lt (hlev x h)
            · simp [h]
        rw [hset]
        apply le_antisymm
        · exact Submodule.span_le.mpr hbt
        · intro y hy
          exact htb hy

/- English proof (translation)
Introduce `k _ d m W hW h0 hm`. Take `⟨s, lev, hs, hlev, hspan⟩` from `exists_linearIndep_levels_span_eq_of_monotone W hW h0 m`. Establish `hall : ∀ i, Submodule.span k {x | x ∈ s ∧ lev x < i} = W i`. Introduce `i`. Break down `le_or_gt i m with h | h` into its components or cases.

Conclude with `hspan i h`. Establish `e1 : {x | x ∈ s ∧ lev x < i} = {x | x ∈ s ∧ lev x < m}`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, -⟩`.

Conclude with `⟨hx, hlev x hx⟩`. Introduce and unpack `⟨hx, h'⟩`. Conclude with `⟨hx, by omega⟩`. Establish `hle` using `hW h.le`. Rewrite `hle` using `[hm]`.

Rewrite using `[e1, hspan m le_rfl, hm]`. Conclude with `(top_le_iff.mp hle).symm`. Establish `hsall : Submodule.span k s = ⊤`. Establish `e1 : {x | x ∈ s ∧ lev x < m} = s`. Use extensionality with `x`.

Conclude with `⟨fun h => h.1, fun h => ⟨h, hlev x h⟩⟩`. Rewrite using `[← e1, hspan m le_rfl, hm]`. Set `b0 : Module.Basis s k (Fin d → k)` to `Module.Basis.mk (v := ((↑) : s → Fin d → k)) hs (by rw [Subtype.range_coe]; exact hsall.ge)`. Set `e : s ≃ Fin d` to `b0.indexEquiv (Pi.basisFun k (Fin d))`. Set `b : Module.Basis (Fin d) k (Fin d → k)` to `b0.reindex e`.

Establish `hb : ∀ j, b j = (e.symm j : Fin d → k)`. Introduce `j`. Simplify using `only [b, Module.Basis.reindex_apply]`. Conclude with `Module.Basis.mk_apply _ _ _`. Set `L` to `b.equivFun.symm`.

Set `P : GL (Fin d) k` to `⟨LinearMap.toMatrix' (L : (Fin d → k) →ₗ[k] (Fin d → k)), LinearMap.toMatrix' (L.symm : (Fin d → k) →ₗ[k] (Fin d → k)), by rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id], by rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix' …`. Use `⟨P, fun j => lev (e.symm j), ?_⟩` and prove the remaining obligations. Introduce `i v`. Establish `hPv : (↑P : Matrix (Fin d) (Fin d) k).mulVec v = L v` using `LinearMap.toMatrix'_mulVec _ v`. Rewrite using `[hPv, ← hall i]`.

Establish `himg : (⇑b '' {j | lev (e.symm j) < i}) = {x | x ∈ s ∧ lev x < i}`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨j, hj, rfl⟩`. Rewrite using `[hb]`.

Conclude with `⟨(e.symm j).2, hj⟩`. Introduce and unpack `⟨hx, hl⟩`. Use `⟨e ⟨x, hx⟩, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using hl`. Rewrite using `[hb]`.

Simplify using the standard rewrite rules. Rewrite using `[← himg, Module.Basis.mem_span_image]`. Establish `hrep : ⇑(b.repr (L v)) = v`. Rewrite using `[← Module.Basis.equivFun_apply]`. Conclude with `b.equivFun.apply_symm_apply v`.

Prove the components needed by the constructor for the conclusion. Introduce `hv j hj`. Express the relevant statement in the definitionally equal form `∀ j, i ≤ lev (e.symm j) → v j = 0 at hv`. Rewrite `hj` using `[Finset.mem_coe, Finsupp.mem_support_iff, hrep]`. Use `show lev (e.symm j) < i`.

Assume the negation of the conclusion as `hlt`. Conclude with `hj (hv j (not_lt.mp hlt))`. Introduce `hsub`. Express the relevant statement in the definitionally equal form `∀ j, i ≤ lev (e.symm j) → v j = 0`. Introduce `j hj`.

Assume the negation of the conclusion as `hne`. Establish `hmem : j ∈ ((b.repr (L v)).support : Set (Fin d))`. Rewrite using `[Finset.mem_coe, Finsupp.mem_support_iff, hrep]`. Conclude with `hne`. Establish `h2` using `hsub hmem`.

Simplify using `only [Set.mem_setOf_eq] at h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.Gal.Int.Geo.flagBasis_of :
    FlagBasis := by
  intro k _ d m W hW h0 hm
  obtain ⟨s, lev, hs, hlev, hspan⟩ := exists_linearIndep_levels_span_eq_of_monotone W hW h0 m
  have hall : ∀ i, Submodule.span k {x | x ∈ s ∧ lev x < i} = W i := by
    intro i
    rcases le_or_gt i m with h | h
    · exact hspan i h
    · have e1 : {x | x ∈ s ∧ lev x < i} = {x | x ∈ s ∧ lev x < m} := by
        ext x
        constructor
        · rintro ⟨hx, -⟩
          exact ⟨hx, hlev x hx⟩
        · rintro ⟨hx, h'⟩
          exact ⟨hx, by omega⟩
      have hle := hW h.le
      rw [hm] at hle
      rw [e1, hspan m le_rfl, hm]
      exact (top_le_iff.mp hle).symm
  have hsall : Submodule.span k s = ⊤ := by
    have e1 : {x | x ∈ s ∧ lev x < m} = s := by
      ext x
      exact ⟨fun h => h.1, fun h => ⟨h, hlev x h⟩⟩
    rw [← e1, hspan m le_rfl, hm]
  let b0 : Module.Basis s k (Fin d → k) :=
    Module.Basis.mk (v := ((↑) : s → Fin d → k)) hs (by rw [Subtype.range_coe]; exact hsall.ge)
  let e : s ≃ Fin d := b0.indexEquiv (Pi.basisFun k (Fin d))
  let b : Module.Basis (Fin d) k (Fin d → k) := b0.reindex e
  have hb : ∀ j, b j = (e.symm j : Fin d → k) := by
    intro j
    simp only [b, Module.Basis.reindex_apply]
    exact Module.Basis.mk_apply _ _ _
  let L := b.equivFun.symm
  let P : GL (Fin d) k :=
    ⟨LinearMap.toMatrix' (L : (Fin d → k) →ₗ[k] (Fin d → k)),
      LinearMap.toMatrix' (L.symm : (Fin d → k) →ₗ[k] (Fin d → k)),
      by rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id],
      by rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]⟩
  refine ⟨P, fun j => lev (e.symm j), ?_⟩
  intro i v
  have hPv : (↑P : Matrix (Fin d) (Fin d) k).mulVec v = L v := LinearMap.toMatrix'_mulVec _ v
  rw [hPv, ← hall i]
  have himg : (⇑b '' {j | lev (e.symm j) < i}) = {x | x ∈ s ∧ lev x < i} := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [hb]
      exact ⟨(e.symm j).2, hj⟩
    · rintro ⟨hx, hl⟩
      refine ⟨e ⟨x, hx⟩, ?_, ?_⟩
      · simpa using hl
      · rw [hb]
        simp
  rw [← himg, Module.Basis.mem_span_image]
  have hrep : ⇑(b.repr (L v)) = v := by
    rw [← Module.Basis.equivFun_apply]
    exact b.equivFun.apply_symm_apply v
  constructor
  · intro hv j hj
    change ∀ j, i ≤ lev (e.symm j) → v j = 0 at hv
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hrep] at hj
    show lev (e.symm j) < i
    by_contra hlt
    exact hj (hv j (not_lt.mp hlt))
  · intro hsub
    change ∀ j, i ≤ lev (e.symm j) → v j = 0
    intro j hj
    by_contra hne
    have hmem : j ∈ ((b.repr (L v)).support : Set (Fin d)) := by
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hrep]
      exact hne
    have h2 := hsub hmem
    simp only [Set.mem_setOf_eq] at h2
    omega
