import ReciprocityTheory.SemistableReduction.SemiDegR

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

/- English proof (translation)
Take `⟨a, rfl⟩` from `hx`. Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a + b, by push_cast; rfl⟩`.
-/
theorem isIntegralElt_add {K : Type} [Field K] [NumberField K] {x y : K} (hx : IsIntegralElt x)
    (hy : IsIntegralElt y) : IsIntegralElt (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by push_cast; rfl⟩

/- English proof (translation)
Take `⟨z, rfl⟩` from `hx`. Conclude with `⟨RingOfIntegers.mapRingHom S.c z, rfl⟩`.
-/
theorem isIntegralElt_c {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) {x : K}
    (hx : IsIntegralElt x) : IsIntegralElt (S.c x) := by
  obtain ⟨z, rfl⟩ := hx
  exact ⟨RingOfIntegers.mapRingHom S.c z, rfl⟩

/- English proof (translation)
Establish `hs : Function.Surjective S.c` using `fun x => ⟨S.c x, S.c_invol x⟩`. Set `e : K ≃+* K` to `RingEquiv.ofBijective S.c ⟨S.c.injective, hs⟩`. Set `e' : K ≃ₐ[ℚ] K` to `AlgEquiv.ofRingEquiv (f := e) (fun q => by simp [e])`. Conclude with `Algebra.norm_eq_of_algEquiv e' z`.
-/
theorem norm_c {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (z : K) :
    Algebra.norm ℚ (S.c z) = Algebra.norm ℚ z := by
  have hs : Function.Surjective S.c := fun x => ⟨S.c x, S.c_invol x⟩
  let e : K ≃+* K := RingEquiv.ofBijective S.c ⟨S.c.injective, hs⟩
  let e' : K ≃ₐ[ℚ] K := AlgEquiv.ofRingEquiv (f := e) (fun q => by simp [e])
  exact Algebra.norm_eq_of_algEquiv e' z

def projLt (K : Type) [Field K] [NumberField K] (r e : ℕ) : (Fin r → K) →ₗ[𝓞 K] (Fin r → K) where
  toFun x i := if (i : ℕ) < e then x i else 0
  map_add' x y := by
    funext i
    by_cases h : (i : ℕ) < e <;> simp [h]
  map_smul' a x := by
    funext i
    by_cases h : (i : ℕ) < e <;> simp [h]

/- English proof (translation)
Unfold `spanIdx`. Establish `hspan : Submodule.span (𝓞 K) (Set.range ![x0, y]) = Submodule.span (𝓞 K) {x0} ⊔ Submodule.span (𝓞 K) {y}`. Rewrite using `[Matrix.range_cons_cons_empty, Submodule.span_insert]`. Establish `h1 : Set.range ![x0] = {x0}` using `Matrix.range_cons_empty _ _`. Establish `h2 : Set.range ![y] = {y}` using `Matrix.range_cons_empty _ _`.

Rewrite using `[hspan, h1, h2, Submodule.sup_toAddSubgroup, Submodule.sup_toAddSubgroup]`. Use `set X0 := (Submodule.span (𝓞 K) {x0}).toAddSubgroup`. Use `set Y := (Submodule.span (𝓞 K) {y}).toAddSubgroup`. Establish `hX0 : X0 ≤ Gj.toAddSubgroup` using `by show Submodule.span (𝓞 K) {x0} ≤ Gj`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`.

Conclude with `hx0`. Establish `hY : Y ≤ Gp.toAddSubgroup` using `by show Submodule.span (𝓞 K) {y} ≤ Gp`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Conclude with `hy`. Establish `key` using `AddSubgroup.relIndex_mul_relIndex _ _ _ (sup_le_sup_left hY X0) (sup_le_sup_right hX0 Gp.toAddSubgroup)`.

Rewrite using `[← key, mul_comm (X0.relIndex _)]`. Use `congr 1`. Use `relIndex_sup_proj (projGe K r p).toAddMonoidHom X0 Y Gp.toAddSubgroup hY ?_ ?_` and prove the remaining obligations. Introduce `a ha`. Take `⟨t, rfl⟩` from `Submodule.mem_span_singleton.1 ha`.

Use `show projGe K r p (t • x0) = 0`. Rewrite using `[map_smul]`. Establish `: projGe K r p x0 = 0`. Use function extensionality and compare the values at `i`. Use `show (if (p : ℕ) ≤ i then x0 i else 0) = 0`.

Use `split_ifs with h`. Conclude with `hj x0 hx0 i (fun hi => by rw [hi] at h; omega)`. Both sides reduce to the same expression. Rewrite using `[this, smul_zero]`. Introduce `x hx show projGe K r p x = x`.

Use function extensionality and compare the values at `i`. Use `show (if (p : ℕ) ≤ i then x i else 0) = x i`. Use `split_ifs with h`. Both sides reduce to the same expression. Conclude with `(hp x hx i (fun hi => by rw [hi] at h; omega)).symm`.

Rewrite using `[sup_comm X0, sup_comm Gj.toAddSubgroup]`. Use `relIndex_sup_proj (projLt K r p).toAddMonoidHom Gp.toAddSubgroup X0 Gj.toAddSubgroup hX0 ?_ ?_` and prove the remaining obligations. Introduce `x hx show projLt K r p x = 0`. Use function extensionality and compare the values at `i`. Use `show (if (i : ℕ) < p then x i else 0) = 0`.

Use `split_ifs with h`. Conclude with `hp x hx i (fun hi => by rw [hi] at h; omega)`. Both sides reduce to the same expression. Introduce `x hx show projLt K r p x = x`. Use function extensionality and compare the values at `i`.

Use `show (if (i : ℕ) < p then x i else 0) = x i`. Use `split_ifs with h`. Both sides reduce to the same expression. Conclude with `(hj x hx i (fun hi => by rw [hi] at h; omega)).symm`.
-/
theorem spanIdx_pair {K : Type} [Field K] [NumberField K] {r : ℕ} (j p : Fin r)
    (hjp : (j : ℕ) < p) (Gj Gp : Submodule (𝓞 K) (Fin r → K)) (hj : ∀ x ∈ Gj, IsAt j x)
    (hp : ∀ x ∈ Gp, IsAt p x) (x0 y : Fin r → K) (hx0 : x0 ∈ Gj) (hy : y ∈ Gp) :
    spanIdx (Gj ⊔ Gp) ![x0, y] = spanIdx Gj ![x0] * spanIdx Gp ![y] := by
  unfold spanIdx
  have hspan : Submodule.span (𝓞 K) (Set.range ![x0, y]) =
      Submodule.span (𝓞 K) {x0} ⊔ Submodule.span (𝓞 K) {y} := by
    rw [Matrix.range_cons_cons_empty, Submodule.span_insert]
  have h1 : Set.range ![x0] = {x0} := Matrix.range_cons_empty _ _
  have h2 : Set.range ![y] = {y} := Matrix.range_cons_empty _ _
  rw [hspan, h1, h2, Submodule.sup_toAddSubgroup, Submodule.sup_toAddSubgroup]
  set X0 := (Submodule.span (𝓞 K) {x0}).toAddSubgroup
  set Y := (Submodule.span (𝓞 K) {y}).toAddSubgroup
  have hX0 : X0 ≤ Gj.toAddSubgroup := by
    show Submodule.span (𝓞 K) {x0} ≤ Gj
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hx0
  have hY : Y ≤ Gp.toAddSubgroup := by
    show Submodule.span (𝓞 K) {y} ≤ Gp
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hy
  have key := AddSubgroup.relIndex_mul_relIndex _ _ _ (sup_le_sup_left hY X0)
    (sup_le_sup_right hX0 Gp.toAddSubgroup)
  rw [← key, mul_comm (X0.relIndex _)]
  congr 1
  · refine relIndex_sup_proj (projGe K r p).toAddMonoidHom X0 Y Gp.toAddSubgroup hY ?_ ?_
    · intro a ha
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 ha
      show projGe K r p (t • x0) = 0
      rw [map_smul]
      have : projGe K r p x0 = 0 := by
        funext i
        show (if (p : ℕ) ≤ i then x0 i else 0) = 0
        split_ifs with h
        · exact hj x0 hx0 i (fun hi => by rw [hi] at h; omega)
        · rfl
      rw [this, smul_zero]
    · intro x hx
      show projGe K r p x = x
      funext i
      show (if (p : ℕ) ≤ i then x i else 0) = x i
      split_ifs with h
      · rfl
      · exact (hp x hx i (fun hi => by rw [hi] at h; omega)).symm
  · rw [sup_comm X0, sup_comm Gj.toAddSubgroup]
    refine relIndex_sup_proj (projLt K r p).toAddMonoidHom Gp.toAddSubgroup X0 Gj.toAddSubgroup
      hX0 ?_ ?_
    · intro x hx
      show projLt K r p x = 0
      funext i
      show (if (i : ℕ) < p then x i else 0) = 0
      split_ifs with h
      · exact hp x hx i (fun hi => by rw [hi] at h; omega)
      · rfl
    · intro x hx
      show projLt K r p x = x
      funext i
      show (if (i : ℕ) < p then x i else 0) = x i
      split_ifs with h
      · rfl
      · exact (hj x hx i (fun hi => by rw [hi] at h; omega)).symm

end ReciprocityTheory.MultiplicativeHeights.SemiPt
