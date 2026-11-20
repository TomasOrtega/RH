import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.DPFil

/- English proof (translation)
Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨l, hl, hr, rfl⟩`. Proceed by induction on `l with`. Consider the case `nil => simp at hr`. Consider the case `cons q t ih`.

Establish `hq : q.2 ∈ J` using `hl q (by simp)`. Rewrite using `[List.map_cons, List.prod_cons]`. Distinguish the cases in `h0 : q.1 = 0`. Use `J.mul_mem_left _ (ih (fun q' h' => hl q' (List.mem_cons_of_mem _ h')) ?_)` and prove the remaining obligations. Simplify `hr` using `[h0]`.

Conclude with `J.mul_mem_right _ (δ.dpow_mem h0 hq)`.
-/
theorem dividedPowerFiltration_one_le {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) : pdP δ 1 ≤ J := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, hl, hr, rfl⟩
  induction l with
  | nil => simp at hr
  | cons q t ih =>
    have hq : q.2 ∈ J := hl q (by simp)
    rw [List.map_cons, List.prod_cons]
    by_cases h0 : q.1 = 0
    · refine J.mul_mem_left _ (ih (fun q' h' => hl q' (List.mem_cons_of_mem _ h')) ?_)
      simpa [h0] using hr
    · exact J.mul_mem_right _ (δ.dpow_mem h0 hq)

/- English proof (translation)
Unfold `pdP`. Rewrite using `[Ideal.span_mul_span']`. Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨l, hl, hr, rfl⟩, _, ⟨l', hl', hr', rfl⟩, rfl⟩`. Use `Ideal.subset_span ⟨l ++ l', ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `q hq`. Break down `List.mem_append.1 hq with h | h` into its components or cases. Conclude with `hl q h`. Conclude with `hl' q h`. Simplify using `using Nat.add_le_add hr hr'`.

Simplify using the standard rewrite rules.
-/
theorem dividedPowerFiltration_mul_le {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (r r' : ℕ) :
    pdP δ r * pdP δ r' ≤ pdP δ (r + r') := by
  unfold pdP
  rw [Ideal.span_mul_span']
  refine Ideal.span_le.2 ?_
  rintro _ ⟨_, ⟨l, hl, hr, rfl⟩, _, ⟨l', hl', hr', rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨l ++ l', ?_, ?_, ?_⟩
  · intro q hq
    rcases List.mem_append.1 hq with h | h
    · exact hl q h
    · exact hl' q h
  · simpa using Nat.add_le_add hr hr'
  · simp

/- English proof (translation)
The claim follows from `Ideal.subset_span ⟨[(k, x)], by simpa using hx, by simp, by simp⟩`.
-/
theorem dpow_mem_pdP {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (k : ℕ) {x : B} (hx : x ∈ J) :
    δ.dpow k x ∈ pdP δ k :=
  Ideal.subset_span ⟨[(k, x)], by simpa using hx, by simp, by simp⟩

/- English proof (translation)
Introduce `b L Q`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `r hr T`. Express the relevant statement in the definitionally equal form `T.obj.pdPow r.toNat = ⊤`. Rewrite using `[Int.toNat_of_nonpos hr]`.

Conclude with `T.obj.pdPow_zero`. Introduce `T`. Express the relevant statement in the definitionally equal form `T.obj.pdPow (1 : ℤ).toNat = T.obj.J`. Conclude with `le_antisymm (dividedPowerFiltration_one_le T.obj.δ) T.obj.J_le_pdPow_one`. Introduce `r r' h T`.

Conclude with `T.obj.pdPow_anti (Int.toNat_le_toNat h)`. Introduce `r r' T x y hx hy`. Establish `hx' : (show T.obj.B from x) ∈ pdP T.obj.δ r`. Establish `: (show T.obj.B from x) ∈ T.obj.pdPow ((r : ℤ).toNat)` using `hx`. Rewrite `this` using `[Int.toNat_natCast]`.

Conclude with `this`. Establish `hy' : (show T.obj.B from y) ∈ pdP T.obj.δ r'`. Establish `: (show T.obj.B from y) ∈ T.obj.pdPow ((r' : ℤ).toNat)` using `hy`. Rewrite `this` using `[Int.toNat_natCast]`. Conclude with `this`.

Establish `h` using `dividedPowerFiltration_mul_le T.obj.δ r r' (Ideal.mul_mem_mul hx' hy')`. Express the relevant statement in the definitionally equal form `_ ∈ T.obj.pdPow (((r + r' : ℕ) : ℤ).toNat)`. Rewrite using `[Int.toNat_natCast]`. Conclude with `h`. Introduce `k T x hx`.

Express the relevant statement in the definitionally equal form `_ ∈ T.obj.pdPow ((k : ℤ).toNat)`. Rewrite using `[Int.toNat_natCast]`. Conclude with `dpow_mem_pdP T.obj.δ k hx`.
-/
theorem isFil_sFil : ∀ {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)), IsFil (sP Q) (sFil Q) := by
  intro b L Q
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hr T
    change T.obj.pdPow r.toNat = ⊤
    rw [Int.toNat_of_nonpos hr]
    exact T.obj.pdPow_zero
  · intro T
    change T.obj.pdPow (1 : ℤ).toNat = T.obj.J
    exact le_antisymm (dividedPowerFiltration_one_le T.obj.δ) T.obj.J_le_pdPow_one
  · intro r r' h T
    exact T.obj.pdPow_anti (Int.toNat_le_toNat h)
  · intro r r' T x y hx hy
    have hx' : (show T.obj.B from x) ∈ pdP T.obj.δ r := by
      have : (show T.obj.B from x) ∈ T.obj.pdPow ((r : ℤ).toNat) := hx
      rw [Int.toNat_natCast] at this
      exact this
    have hy' : (show T.obj.B from y) ∈ pdP T.obj.δ r' := by
      have : (show T.obj.B from y) ∈ T.obj.pdPow ((r' : ℤ).toNat) := hy
      rw [Int.toNat_natCast] at this
      exact this
    have h := dividedPowerFiltration_mul_le T.obj.δ r r' (Ideal.mul_mem_mul hx' hy')
    change _ ∈ T.obj.pdPow (((r + r' : ℕ) : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact h
  · intro k T x hx
    change _ ∈ T.obj.pdPow ((k : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact dpow_mem_pdP T.obj.δ k hx

end GlobalTheory.CompanionTheory.DPFil
