import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.Sublevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.VertFinite

open Set UpperTheory.V.ConeExtensionAcyclic

/- English proof (translation)
Introduce `E Y _ _ _ q T hg s hs hsT`. Take `⟨h0, hh0⟩` from `hg.nonempty`. Set `K : Set E` to `⋃ x ∈ s, {h | h ∈ poly q ∧ x h ≤ x h0}`. Establish `hK : IsCompact K` using `hs.isCompact_biUnion fun x hx => sublevel hg x (hsT hx) (x h0)`. Establish `hKp : K ⊆ poly q`.

Introduce `h hh`. Simplify using `only [K, Set.mem_iUnion] at hh`. Take `⟨x, _, hp, _⟩` from `hh`. Conclude with `hp`. Use `((vert_finite hg.locFin K hK hKp).preimage Subtype.val_injective.injOn).subset ?_` and prove the remaining obligations.

Introduce and unpack `v ⟨z, hzs, hzv⟩`. Use `⟨?_, v.2⟩` and prove the remaining obligations. Simplify using `only [K, Set.mem_iUnion]`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`.

Establish `hconv : Convex ℝ {f : E →L[ℝ] ℝ | 0 < f (v.1 - h0)}`. Use `convex_halfSpace_gt ?_ 0` and prove the remaining obligations. Conclude with `⟨fun f g => rfl, fun c f => rfl⟩`. Establish `hsub : s ⊆ {f : E →L[ℝ] ℝ | 0 < f (v.1 - h0)}`. Introduce `x hx`.

Establish `hlt : x h0 < x v.1`. Assume the negation of the conclusion as `hle`. Conclude with `hno x hx ⟨v.2.1, not_lt.mp hle⟩`. Simplify using `only [Set.mem_setOf_eq, map_sub]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hz` using `convexHull_min hsub hconv hzs`. Establish `hz2` using `hzv h0 hh0`. Simplify using `only [Set.mem_setOf_eq, map_sub] at hz`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.V.ConeExtensionAcyclic.cone_finite :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {q : Y → E →L[ℝ] ℝ} {T : Set E}, Good q T → ∀ s : Set (E →L[ℝ] ℝ), s.Finite → s ⊆ posDual T → {v : Vert q | (convexHull ℝ s ∩ normalCone q v.1).Nonempty}.Finite := by
  intro E Y _ _ _ q T hg s hs hsT
  obtain ⟨h0, hh0⟩ := hg.nonempty
  let K : Set E := ⋃ x ∈ s, {h | h ∈ poly q ∧ x h ≤ x h0}
  have hK : IsCompact K := hs.isCompact_biUnion fun x hx => sublevel hg x (hsT hx) (x h0)
  have hKp : K ⊆ poly q := by
    intro h hh
    simp only [K, Set.mem_iUnion] at hh
    obtain ⟨x, _, hp, _⟩ := hh
    exact hp
  refine ((vert_finite hg.locFin K hK hKp).preimage Subtype.val_injective.injOn).subset ?_
  rintro v ⟨z, hzs, hzv⟩
  refine ⟨?_, v.2⟩
  simp only [K, Set.mem_iUnion]
  by_contra hno
  push_neg at hno
  have hconv : Convex ℝ {f : E →L[ℝ] ℝ | 0 < f (v.1 - h0)} := by
    refine convex_halfSpace_gt ?_ 0
    exact ⟨fun f g => rfl, fun c f => rfl⟩
  have hsub : s ⊆ {f : E →L[ℝ] ℝ | 0 < f (v.1 - h0)} := by
    intro x hx
    have hlt : x h0 < x v.1 := by
      by_contra hle
      exact hno x hx ⟨v.2.1, not_lt.mp hle⟩
    simp only [Set.mem_setOf_eq, map_sub]
    linarith
  have hz := convexHull_min hsub hconv hzs
  have hz2 := hzv h0 hh0
  simp only [Set.mem_setOf_eq, map_sub] at hz
  linarith
