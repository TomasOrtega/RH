import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PromodularityCaseThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedTanFlow

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Cu

namespace UpperTheory.V.Cu.ReductionTangentLimit

def xMA (k : Type) [Field k] : M4 k := Matrix.single 1 0 1 - Matrix.single 3 2 1

def cA {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k) (b : Φ.ι → k) :
    PD Φ.ι Γ k :=
  ⟨(Φ.split a).r, fun v => 1 + b v • xMA k⟩

/- English proof (translation)
Use `hx.2.2.2.2.2.1 g i j h1 h2` as an intermediate fact. Rewrite `this` using `[hc, Matrix.mul_apply]`. Simplify using `only [Fr.split_r_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this`. Conclude with `(mul_eq_zero.1 this).resolve_right ((Φ.χ j g).isUnit.map a).ne_zero`.
-/
theorem zeroA {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {k : Type} [Field k]
    {a : O →+* k} {S : Finset (ℤ × ℤ)} {c : PD Φ.ι Γ k} (hc : c.r = (Φ.split a).r) {x} (hx : x ∈ Φ.Tan S c) (i j : Fin 4)
    (h1 : i ≠ j) (h2 : wt i j ∉ S) (g : Γ) : x.1 g i j = 0 := by
  have := hx.2.2.2.2.2.1 g i j h1 h2
  rw [hc, Matrix.mul_apply] at this
  simp only [Fr.split_r_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  exact (mul_eq_zero.1 this).resolve_right ((Φ.χ j g).isUnit.map a).ne_zero

/- English proof (translation)
Establish `z : ∀ i j, i ≠ j → m i ≤ m j → c.r g i j = 0` using `fun i j h1 h2 => hS g i j h1 fun h3 => absurd (hm i j h1 h3) (by omega)`. Use `⟨fun i j hij => z i j (by rintro rfl; omega) (by omega), ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Rewrite using `[cmp_apply, Fr.split_r_apply]`. Distinguish the cases in `h1 : i = j`.

Substitute `h1` using the available equality. Simplify using `[h.diag]`. Rewrite using `[if_neg h1] split_ifs with h2`. Conclude with `(z i j h1 (by omega)).symm`. Both sides reduce to the same expression.
-/
theorem limRA {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {k : Type} [Field k] {a : O →+* k} {c : PD Φ.ι Γ k}
    (h : Φ.Res a c) {S : Finset (ℤ × ℤ)} (hS : Supp S c.r) {m : Fin 4 → ℤ}
    (hm : ∀ i j, i ≠ j → wt i j ∈ S → m j < m i) (g : Γ) : Lim m (c.r g) ((Φ.split a).r g) := by
  have z : ∀ i j, i ≠ j → m i ≤ m j → c.r g i j = 0 := fun i j h1 h2 =>
    hS g i j h1 fun h3 => absurd (hm i j h1 h3) (by omega)
  refine ⟨fun i j hij => z i j (by rintro rfl; omega) (by omega), ?_⟩
  ext i j
  rw [cmp_apply, Fr.split_r_apply]
  by_cases h1 : i = j
  · subst h1; simp [h.diag]
  · rw [if_neg h1]
    split_ifs with h2
    · exact (z i j h1 (by omega)).symm
    · rfl

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Establish `h32 : n 3 2 = -n 1 0`. Use `congrFun (congrFun h1 1) 0` as an intermediate fact. Simplify using `[Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, h2, h3 0 1 (by decide), h3 0 2 (by decide), h3 0 3 (by decide), h3 1 2 (by decide), h3 1 3 (by decide), h3 2 3 (by decide)] at this`. Take the linear combination `this`.

Use `⟨fun i j hij => ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> first | exact h3 _ _ (by decide) | (simp at hij)`. Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;>`. Simplify using `[cmp_apply, xMA, Matrix.one_apply, Matrix.single_apply, h2, h32, h3 0 1 (by decide), h3 2 3 (by decide)]`.
-/
theorem limA {k : Type} [Field k] {n : M4 k} (h : IsLow n) : Lim ![0, 0, 1, 1] n (1 + n 1 0 • xMA k) := by
  obtain ⟨h1, h2, h3⟩ := h
  have h32 : n 3 2 = -n 1 0 := by
    have := congrFun (congrFun h1 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, h2, h3 0 1 (by decide), h3 0 2 (by decide),
      h3 0 3 (by decide), h3 1 2 (by decide), h3 1 3 (by decide), h3 2 3 (by decide)] at this
    linear_combination this
  refine ⟨fun i j hij => ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> first | exact h3 _ _ (by decide) | (simp at hij)
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cmp_apply, xMA, Matrix.one_apply, Matrix.single_apply, h2, h32, h3 0 1 (by decide), h3 2 3 (by decide)]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, xMA, Matrix.one_apply, Matrix.single_apply]`.
-/
theorem gsp_A {k : Type} [Field k] (b : k) : IsGSp 1 (1 + b • xMA k) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, xMA, Matrix.one_apply, Matrix.single_apply]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hp.low v`. Establish `h1' : c.n v * adj (c.n v) = 1` using `mul_eq_one_comm.1 (by simpa [IsGSp] using h1)`. Establish `e : c.r s * c.n v = c.n v * (adj (c.n v) * c.r s * c.n v)`. Rewrite using `[← mul_assoc, ← mul_assoc, h1', one_mul]`. Establish `u` using `hp.flag v s hs`.

Establish `e2` using `congrFun (congrFun e 1) 0`. Establish `hc : (adj (c.n v) * c.r s * c.n v) 0 0 = a (Φ.χ 0 s)` using `h.char v s hs 0`. Rewrite `e2` using `[Matrix.mul_apply, Matrix.mul_apply (M := c.n v), Fin.sum_univ_four, Fin.sum_univ_four, u 1 0 (by decide), u 2 0 (by decide), u 3 0 (by decide), hc, h.diag, hA.1 s 1 0 (by decide) (by decide), hA.1 s 1 2 (by decide) (by decide), hA.1 s 1 3 (by decide) (by decide)]`. Conclude with `mul_left_cancel₀ (hA.2 v) (by linear_combination -e2)`.
-/
theorem characters_agree_at_local_of_typeA {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {k : Type} [Field k] {a : O →+* k} {c : PD Φ.ι Γ k}
    (hp : Φ.IsPair a c) (h : Φ.Res a c) (hA : InA c) (v : Φ.ι) (s : Γ) (hs : s ∈ Φ.Gv v) :
    a (Φ.χ 0 s) = a (Φ.χ 1 s) := by
  obtain ⟨h1, h2, h3⟩ := hp.low v
  have h1' : c.n v * adj (c.n v) = 1 := mul_eq_one_comm.1 (by simpa [IsGSp] using h1)
  have e : c.r s * c.n v = c.n v * (adj (c.n v) * c.r s * c.n v) := by
    rw [← mul_assoc, ← mul_assoc, h1', one_mul]
  have u := hp.flag v s hs
  have e2 := congrFun (congrFun e 1) 0
  have hc : (adj (c.n v) * c.r s * c.n v) 0 0 = a (Φ.χ 0 s) := h.char v s hs 0
  rw [Matrix.mul_apply, Matrix.mul_apply (M := c.n v), Fin.sum_univ_four, Fin.sum_univ_four, u 1 0 (by decide),
    u 2 0 (by decide), u 3 0 (by decide), hc, h.diag, hA.1 s 1 0 (by decide) (by decide),
    hA.1 s 1 2 (by decide) (by decide), hA.1 s 1 3 (by decide) (by decide)] at e2
  exact mul_left_cancel₀ (hA.2 v) (by linear_combination -e2)

/- English proof (translation)
Establish `e : Units.map (a : O →* k) (Φ.χ i s * (Φ.χ j s)⁻¹) = 1`. Rewrite using `[map_mul, map_inv, mul_inv_eq_one]`. Conclude with `Units.ext h`. Establish `e2 : ∀ u : Oˣ, a u = (Units.map (a : O →* k) u : kˣ)` using `fun _ => rfl`. Rewrite using `[hok.rt_wt, e2, e, Units.val_one]`.
-/
theorem rt_oneA {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {k : Type} [Field k] {a : O →+* k} (hok : Φ.Ok a)
    {i j : Fin 4} {s : Γ} (h : a (Φ.χ i s) = a (Φ.χ j s)) : a (Φ.rt (wt i j) s) = 1 := by
  have e : Units.map (a : O →* k) (Φ.χ i s * (Φ.χ j s)⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one]
    exact Units.ext h
  have e2 : ∀ u : Oˣ, a u = (Units.map (a : O →* k) u : kˣ) := fun _ => rfl
  rw [hok.rt_wt, e2, e, Units.val_one]

/- English proof (translation)
Establish `h10` using `h 1 0 (by decide)`. Establish `h21` using `h 2 1 (by decide)`. Establish `h20` using `h 2 0 (by decide)`. Establish `h31` using `h 3 1 (by decide)`. Establish `h30` using `h 3 0 (by decide)`.

Simplify using `[Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, xMA, Matrix.one_apply, Matrix.single_apply] at h10 h21 h20 h31 h30`. Establish `e20 : Z 2 0 = 0` using `by linear_combination h20 - b * h21`. Use `⟨by linear_combination h10, h21, by linear_combination h30 - b * e20 - b * h31⟩` and prove the remaining obligations.
-/
theorem rel_A {k : Type} [Field k] (b : k) (Z : M4 k) (h : IsUp (adj (1 + b • xMA k) * Z * (1 + b • xMA k))) :
    Z 1 0 = b ^ 2 * Z 0 1 + b * (Z 0 0 - Z 1 1) ∧ Z 2 1 = 0 ∧ Z 3 0 = 0 := by
  have h10 := h 1 0 (by decide)
  have h21 := h 2 1 (by decide)
  have h20 := h 2 0 (by decide)
  have h31 := h 3 1 (by decide)
  have h30 := h 3 0 (by decide)
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, xMA, Matrix.one_apply, Matrix.single_apply]
    at h10 h21 h20 h31 h30
  have e20 : Z 2 0 = 0 := by linear_combination h20 - b * h21
  refine ⟨by linear_combination h10, h21, by linear_combination h30 - b * e20 - b * h31⟩

set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option maxRecDepth 20000 in
/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem keyA : ∀ S ∈ redTypes, (-wPs ∈ S ∨ (-wBe ∈ S ∧ -wTh ∈ S ∧ S ≠ yY)) → ∃ i₀ j₀ : Fin 4, wt i₀ j₀ ∈ oddRoots ∧
    (i₀ = 0 ∧ j₀ = 3 ∨ wt 0 3 ∉ S) ∧ (i₀ = 1 ∧ j₀ = 2 ∨ wt 1 2 ∉ S) ∧
    ((i₀ = 0 ∧ j₀ = 1 ∨ wt 0 1 ∉ S) ∨ (i₀ = 1 ∧ j₀ = 0 ∨ wt 1 0 ∉ S)) := by
  decide

/- English proof (translation)
Take `⟨i₀, j₀, h1, hθ, hβ, hα⟩` from `keyA S hS h`. Use `⟨i₀, j₀, h1, fun x hx h0 h00 h11 => ?_⟩` and prove the remaining obligations. Establish `ent : ∀ v (s : Γ) (i j : Fin 4), (x.1 s + (Φ.split a).r s * x.2 v * (Φ.split a).r s⁻¹ - x.2 v) i j = x.1 s i j + a (Φ.rt (wt i j) s) * x.2 v i j - x.2 v i j` using `fun v s i j => by`. Rewrite using `[Matrix.sub_apply, Matrix.add_apply, hok.conj_split]`. Establish `rel : ∀ v, ∀ s ∈ Φ.Gv v, x.1 s 1 0 = b v ^ 2 * x.1 s 0 1 ∧ x.1 s 2 1 = x.2 v 2 1 - a (Φ.rt (wt 2 1) s) * x.2 v 2 1 ∧ x.1 s 3 0 = x.2 v 3 0 - a (Φ.rt (wt 3 0) s) * x.2 v 3 0`.

Introduce `v s hs`. Use `rel_A (b v) (x.1 s + (Φ.split a).r s * x.2 v * (Φ.split a).r s⁻¹ - x.2 v) (hx.2.2.2.2.2.2.2 v s hs)` as an intermediate fact. Simplify using `only [ent] at this`. Establish `e00 : a (Φ.rt (wt 0 0) s) = 1` using `rt_oneA hok rfl`. Establish `e11 : a (Φ.rt (wt 1 1) s) = 1` using `rt_oneA hok rfl`.

Establish `e01 : a (Φ.rt (wt 0 1) s) = 1` using `rt_oneA hok (hχ v s hs)`. Establish `e10 : a (Φ.rt (wt 1 0) s) = 1` using `rt_oneA hok (hχ v s hs).symm`. Rewrite `this` using `[e00, e11, e01, e10, h00 s, h11 s]`. Conclude with `⟨by linear_combination this.1, by linear_combination this.2.1, by linear_combination this.2.2⟩`. Establish `z1 : ∀ {i j : Fin 4}, i ≠ j → wt i j ∉ S → ∀ g, x.1 g i j = 0` using `fun h1 h2 g => zeroA (c := cA Φ a b) rfl hx _ _ h1 h2 g`.

Establish `g03 : ∀ g, x.1 g 0 3 = 0`. Break down `hθ with ⟨rfl, rfl⟩ | hθ` into its components or cases. Conclude with `h0`. Conclude with `z1 (by decide) hθ`. Establish `g12 : ∀ g, x.1 g 1 2 = 0`.

Break down `hβ with ⟨rfl, rfl⟩ | hβ` into its components or cases. Conclude with `h0`. Conclude with `z1 (by decide) hβ`. Establish `gα : ∀ v, ∀ s ∈ Φ.Gv v, x.1 s 0 1 = 0 ∧ x.1 s 1 0 = 0`. Introduce `v s hs`.

Establish `e` using `(rel v s hs).1`. Establish `sq : b v ^ 2 ≠ 0` using `pow_ne_zero 2 (hb v)`. Break down `hα with (⟨rfl, rfl⟩ | hα) | (⟨rfl, rfl⟩ | hα)` into its components or cases. Establish `e'` using `h0 s`. Rewrite `e` using `[e', mul_zero]`.

Conclude with `⟨e', e⟩`. Establish `e'` using `z1 (by decide) hα s`. Rewrite `e` using `[e', mul_zero]`. Conclude with `⟨e', e⟩`. Establish `e'` using `h0 s`.

Rewrite `e` using `[e']`. Conclude with `⟨(mul_eq_zero.1 e.symm).resolve_left sq, e'⟩`. Establish `e'` using `z1 (by decide) hα s`. Rewrite `e` using `[e']`. Conclude with `⟨(mul_eq_zero.1 e.symm).resolve_left sq, e'⟩`.

Establish `pos : ∀ i j : Fin 4, i ≤ j.rev → wt i j ∈ oddRoots → (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 0) ∨ (i = 3 ∧ j = 0)` using `by decide`. Introduce `i j h4 h5`. Break down `pos i j h4 h5 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` into its components or cases. Conclude with `⟨0, fun v s hs => by simp [(gα v s hs).1]⟩`. Conclude with `⟨0, fun v s _ => by simp [g03 s]⟩`.

Conclude with `⟨fun v => x.2 v 2 1, fun v s hs => (rel v s hs).2.1⟩`. Conclude with `⟨0, fun v s _ => by simp [g12 s]⟩`. Conclude with `⟨0, fun v s hs => by simp [(gα v s hs).2]⟩`. Conclude with `⟨fun v => x.2 v 3 0, fun v s hs => (rel v s hs).2.2⟩`.
-/
theorem oneOddA {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k]
    (a : O →+* k) (hok : Φ.Ok a) (b : Φ.ι → k) (hb : ∀ v, b v ≠ 0)
    (hχ : ∀ v, ∀ s ∈ Φ.Gv v, a (Φ.χ 0 s) = a (Φ.χ 1 s)) (S : Finset (ℤ × ℤ)) (hS : S ∈ redTypes)
    (h : -wPs ∈ S ∨ (-wBe ∈ S ∧ -wTh ∈ S ∧ S ≠ yY)) :
    ∃ i₀ j₀ : Fin 4, wt i₀ j₀ ∈ oddRoots ∧ ∀ x ∈ Φ.Tan S (cA Φ a b), (∀ g, x.1 g i₀ j₀ = 0) →
      (∀ g, x.1 g 0 0 = 0) → (∀ g, x.1 g 1 1 = 0) → ∀ i j : Fin 4, i ≤ j.rev → wt i j ∈ oddRoots →
        ∃ n, Φ.LocTriv a (wt i j) (fun g => x.1 g i j) n := by
  obtain ⟨i₀, j₀, h1, hθ, hβ, hα⟩ := keyA S hS h
  refine ⟨i₀, j₀, h1, fun x hx h0 h00 h11 => ?_⟩
  have ent : ∀ v (s : Γ) (i j : Fin 4), (x.1 s + (Φ.split a).r s * x.2 v * (Φ.split a).r s⁻¹ - x.2 v) i j =
      x.1 s i j + a (Φ.rt (wt i j) s) * x.2 v i j - x.2 v i j := fun v s i j => by
    rw [Matrix.sub_apply, Matrix.add_apply, hok.conj_split]
  have rel : ∀ v, ∀ s ∈ Φ.Gv v, x.1 s 1 0 = b v ^ 2 * x.1 s 0 1 ∧
      x.1 s 2 1 = x.2 v 2 1 - a (Φ.rt (wt 2 1) s) * x.2 v 2 1 ∧
      x.1 s 3 0 = x.2 v 3 0 - a (Φ.rt (wt 3 0) s) * x.2 v 3 0 := by
    intro v s hs
    have := rel_A (b v) (x.1 s + (Φ.split a).r s * x.2 v * (Φ.split a).r s⁻¹ - x.2 v) (hx.2.2.2.2.2.2.2 v s hs)
    simp only [ent] at this
    have e00 : a (Φ.rt (wt 0 0) s) = 1 := rt_oneA hok rfl
    have e11 : a (Φ.rt (wt 1 1) s) = 1 := rt_oneA hok rfl
    have e01 : a (Φ.rt (wt 0 1) s) = 1 := rt_oneA hok (hχ v s hs)
    have e10 : a (Φ.rt (wt 1 0) s) = 1 := rt_oneA hok (hχ v s hs).symm
    rw [e00, e11, e01, e10, h00 s, h11 s] at this
    exact ⟨by linear_combination this.1, by linear_combination this.2.1, by linear_combination this.2.2⟩
  have z1 : ∀ {i j : Fin 4}, i ≠ j → wt i j ∉ S → ∀ g, x.1 g i j = 0 := fun h1 h2 g =>
    zeroA (c := cA Φ a b) rfl hx _ _ h1 h2 g
  have g03 : ∀ g, x.1 g 0 3 = 0 := by
    rcases hθ with ⟨rfl, rfl⟩ | hθ
    · exact h0
    · exact z1 (by decide) hθ
  have g12 : ∀ g, x.1 g 1 2 = 0 := by
    rcases hβ with ⟨rfl, rfl⟩ | hβ
    · exact h0
    · exact z1 (by decide) hβ
  have gα : ∀ v, ∀ s ∈ Φ.Gv v, x.1 s 0 1 = 0 ∧ x.1 s 1 0 = 0 := by
    intro v s hs
    have e := (rel v s hs).1
    have sq : b v ^ 2 ≠ 0 := pow_ne_zero 2 (hb v)
    rcases hα with (⟨rfl, rfl⟩ | hα) | (⟨rfl, rfl⟩ | hα)
    · have e' := h0 s
      rw [e', mul_zero] at e
      exact ⟨e', e⟩
    · have e' := z1 (by decide) hα s
      rw [e', mul_zero] at e
      exact ⟨e', e⟩
    · have e' := h0 s
      rw [e'] at e
      exact ⟨(mul_eq_zero.1 e.symm).resolve_left sq, e'⟩
    · have e' := z1 (by decide) hα s
      rw [e'] at e
      exact ⟨(mul_eq_zero.1 e.symm).resolve_left sq, e'⟩
  have pos : ∀ i j : Fin 4, i ≤ j.rev → wt i j ∈ oddRoots → (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 1) ∨
      (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 0) ∨ (i = 3 ∧ j = 0) := by decide
  intro i j h4 h5
  rcases pos i j h4 h5 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨0, fun v s hs => by simp [(gα v s hs).1]⟩
  · exact ⟨0, fun v s _ => by simp [g03 s]⟩
  · exact ⟨fun v => x.2 v 2 1, fun v s hs => (rel v s hs).2.1⟩
  · exact ⟨0, fun v s _ => by simp [g12 s]⟩
  · exact ⟨0, fun v s hs => by simp [(gα v s hs).2]⟩
  · exact ⟨fun v => x.2 v 3 0, fun v s hs => (rel v s hs).2.2⟩

/- English proof (translation)
Take `⟨i₀, j₀, h0, H⟩` from `H`. Establish `ent : ∀ x ∈ Φ.Tan S c, ∀ i j, (fun g => x.1 g i j) ∈ Φ.Zgl a (wt i j)`. Introduce `x hx i j`. Use `⟨hx.1.comp (fun Z : M4 k => Z i j), fun g h => ?_, fun g hg => ?_, fun hw => ?_⟩` and prove the remaining obligations. Use `show x.1 (g * h) i j = _`.

Rewrite using `[hx.2.2.1, Matrix.add_apply, hc, hok.conj_split]`. Use `show x.1 g i j = 0`. Rewrite using `[hx.2.2.2.1 g hg]`. Both sides reduce to the same expression. Conclude with `hx.2.2.2.2.1 fun e => hw ((wt_eq_zero i j).2 e)`.

Set `E : Fin 4 → Fin 4 → (Φ.TanS S c →ₗ[k] (Γ → k))` to `fun i j => { toFun := fun x g => x.1.1 g i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Set `E3 : Φ.TanS S c →ₗ[k] Φ.Zgl a (wt i₀ j₀) × Φ.Zgl a (wt 0 0) × Φ.Zgl a (wt 1 1)` to `{ toFun := fun x => (⟨fun g => x.1.1 g i₀ j₀, ent _ x.2 _ _⟩, ⟨fun g => x.1.1 g 0 0, ent _ x.2 _ _⟩, ⟨fun g => x.1.1 g 1 1, ent _ x.2 _ _⟩) map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `kz : ∀ x : LinearMap.ker E3, (∀ g, x.1.1.1 g i₀ j₀ = 0) ∧ (∀ g, x.1.1.1 g 0 0 = 0) ∧ (∀ g, x.1.1.1 g 1 1 = 0)`. Introduce `x`. Establish `h` using `LinearMap.mem_ker.1 x.2`.

Conclude with `⟨fun g => congrArg (fun p => (p.1 : Γ → k) g) h, fun g => congrArg (fun p => (p.2.1 : Γ → k) g) h, fun g => congrArg (fun p => (p.2.2 : Γ → k) g) h⟩`. Set `P` to `{p : Fin 4 × Fin 4 // p.1 ≤ p.2.rev}`. Set `Q` to `{p : Fin 4 × Fin 4 // p.2 < p.1}`. Set `M : P → Submodule k (Γ → k)` to `fun p => if wt p.1.1 p.1.2 ∈ oddRoots then Φ.Str a (wt p.1.1 p.1.2) else Φ.Zgl a (wt p.1.1 p.1.2)`. Establish `hM : ∀ p, Module.rank k (M p) ≤ C`.

Introduce `p`. Distinguish the cases in `h : wt p.1.1 p.1.2 ∈ oddRoots`. Rewrite using `[show M p = _ from if_pos h]`. Conclude with `hb.str _ (Finset.mem_union_left _ h)`. Rewrite using `[show M p = _ from if_neg h]`.

Establish `: ∀ i j, wt i j ∉ oddRoots → wt i j ∈ [0, wPs, -wPs]` using `by decide`. Conclude with `hb.even _ (this _ _ h)`. Establish `mem : ∀ (x : LinearMap.ker E3) (p : P), E p.1.1 p.1.2 x.1 ∈ M p`. Introduce `x p`. Distinguish the cases in `h : wt p.1.1 p.1.2 ∈ oddRoots`.

Rewrite using `[show M p = _ from if_pos h]`. Conclude with `⟨ent _ x.1.2 _ _, H _ x.1.2 (kz x).1 (kz x).2.1 (kz x).2.2 _ _ p.2 h⟩`. Rewrite using `[show M p = _ from if_neg h]`. Conclude with `ent _ x.1.2 _ _`. Set `F : LinearMap.ker E3 →ₗ[k] (∀ p : P, M p) × (Φ.ι × Q → k)` to `{ toFun := fun x => (fun p => ⟨_, mem x p⟩, fun z => (adj (c.n z.1) * x.1.1.2 z.1 * c.n z.1) z.2.1.1 z.2.1.2) map_add' := fun x y => Prod.ext rfl (funext fun z => by simp [mul_add, add_mul]) map_smul' := fun t x => Prod.ext rfl (funext fun z => by simp) }`.

Establish `hF : Function.Injective F`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `hx1 : ∀ g i j, i ≤ j.rev → x.1.1.1 g i j = 0` using `fun g i j h => congrFun (congrArg Subtype.val (congrFun (congrArg Prod.fst hx) ⟨(i, j), h⟩)) g`. Establish `hx2 : ∀ v i j, j < i → (adj (c.n v) * x.1.1.2 v * c.n v) i j = 0` using `fun v i j h => congrFun (congrArg Prod.snd hx) (v, ⟨(i, j), h⟩)`.

Use `Subtype.ext (Subtype.ext (Prod.ext (funext fun g => ?_) (funext fun v => ?_)))` and prove the remaining obligations. Use extensionality with `i j`. Distinguish the cases in `h : i ≤ j.rev`. Conclude with `hx1 g i j h`. Use `congrFun (congrFun (show adj (x.1.1.1 g) = -x.1.1.1 g from x.1.2.2.1 g) i) j` as an intermediate fact.

Establish `h' : ∀ i j : Fin 4, ¬ i ≤ j.rev → j.rev ≤ i.rev.rev` using `by decide`. Rewrite `this` using `[adj_apply, hx1 g _ _ (h' i j h), smul_zero, Matrix.neg_apply]`. Conclude with `neg_eq_zero.1 this.symm`. Establish `h1 : adj (c.n v) * c.n v = 1` using `by simpa [IsGSp] using hn v`. Establish `h2` using `mul_eq_one_comm.1 h1`.

Establish `h3 : adj (c.n v) * x.1.1.2 v * c.n v = 0`. Use extensionality with `i j`. Break down `le_or_gt i j with h | h` into its components or cases. Use `exacts [(x.1.2.2.2.2.2.2.2.1 v).2 i j h, hx2 v i j h]`. Combine the equalities or inequalities in the displayed calculation.

Establish `r1 : Module.rank k (LinearMap.range E3) ≤ (d + C) + (C + C)`. Use `(Submodule.rank_le _).trans ?_` and prove the remaining obligations. Rewrite using `[rank_prod', rank_prod']`. Conclude with `add_le_add (hb.odd _ h0) (add_le_add (hb.even _ (by decide)) (hb.even _ (by decide)))`. Establish `r2 : Module.rank k (∀ p : P, M p) ≤ 10 * C`.

Rewrite using `[rank_pi]`. Use `le_trans (Cardinal.sum_le_sum _ _ hM) ?_` and prove the remaining obligations. Rewrite using `[Cardinal.sum_const', Cardinal.mk_fintype, show Fintype.card P = 10 by decide]`. Simplify using the standard rewrite rules. Establish `r3 : Module.rank k (Φ.ι × Q → k) ≤ 6 * C` using `by haveI := Fintype.ofFinite Φ.ι`.

Rewrite using `[rank_fun', Fintype.card_prod, show Fintype.card Q = 6 by decide, ← Nat.card_eq_fintype_card]`. Use `hb.card` as an intermediate fact. Conclude with `(by omega : Nat.card Φ.ι * 6 ≤ 6 * C)` after adjusting the coercions. Establish `r4` using `LinearMap.rank_le_of_injective F hF`. Rewrite `r4` using `[rank_prod']`.

Rewrite using `[← LinearMap.rank_range_add_rank_ker E3]`. Use `le_trans (add_le_add r1 (r4.trans (add_le_add r2 r3))) ?_` and prove the remaining obligations. Conclude with `(by omega : d + C + (C + C) + (10 * C + 6 * C) ≤ d + 20 * C)` after adjusting the coercions.
-/
theorem rank_A {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k]
    (a : O →+* k) (hok : Φ.Ok a) (d C : ℕ) (hb : Φ.Bounds a d C) (S : Finset (ℤ × ℤ)) (c : PD Φ.ι Γ k)
    (hc : c.r = (Φ.split a).r) (hn : ∀ v, IsGSp 1 (c.n v))
    (H : ∃ i₀ j₀ : Fin 4, wt i₀ j₀ ∈ oddRoots ∧ ∀ x ∈ Φ.Tan S c, (∀ g, x.1 g i₀ j₀ = 0) →
      (∀ g, x.1 g 0 0 = 0) → (∀ g, x.1 g 1 1 = 0) → ∀ i j : Fin 4, i ≤ j.rev → wt i j ∈ oddRoots →
        ∃ n, Φ.LocTriv a (wt i j) (fun g => x.1 g i j) n) :
    Module.rank k (Φ.TanS S c) ≤ d + 20 * C := by
  obtain ⟨i₀, j₀, h0, H⟩ := H
  have ent : ∀ x ∈ Φ.Tan S c, ∀ i j, (fun g => x.1 g i j) ∈ Φ.Zgl a (wt i j) := by
    intro x hx i j
    refine ⟨hx.1.comp (fun Z : M4 k => Z i j), fun g h => ?_, fun g hg => ?_, fun hw => ?_⟩
    · show x.1 (g * h) i j = _
      rw [hx.2.2.1, Matrix.add_apply, hc, hok.conj_split]
    · show x.1 g i j = 0
      rw [hx.2.2.2.1 g hg]; rfl
    · exact hx.2.2.2.2.1 fun e => hw ((wt_eq_zero i j).2 e)
  let E : Fin 4 → Fin 4 → (Φ.TanS S c →ₗ[k] (Γ → k)) := fun i j =>
    { toFun := fun x g => x.1.1 g i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let E3 : Φ.TanS S c →ₗ[k] Φ.Zgl a (wt i₀ j₀) × Φ.Zgl a (wt 0 0) × Φ.Zgl a (wt 1 1) :=
    { toFun := fun x => (⟨fun g => x.1.1 g i₀ j₀, ent _ x.2 _ _⟩, ⟨fun g => x.1.1 g 0 0, ent _ x.2 _ _⟩,
        ⟨fun g => x.1.1 g 1 1, ent _ x.2 _ _⟩)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have kz : ∀ x : LinearMap.ker E3, (∀ g, x.1.1.1 g i₀ j₀ = 0) ∧ (∀ g, x.1.1.1 g 0 0 = 0) ∧
      (∀ g, x.1.1.1 g 1 1 = 0) := by
    intro x
    have h := LinearMap.mem_ker.1 x.2
    exact ⟨fun g => congrArg (fun p => (p.1 : Γ → k) g) h, fun g => congrArg (fun p => (p.2.1 : Γ → k) g) h,
      fun g => congrArg (fun p => (p.2.2 : Γ → k) g) h⟩
  let P := {p : Fin 4 × Fin 4 // p.1 ≤ p.2.rev}
  let Q := {p : Fin 4 × Fin 4 // p.2 < p.1}
  let M : P → Submodule k (Γ → k) := fun p =>
    if wt p.1.1 p.1.2 ∈ oddRoots then Φ.Str a (wt p.1.1 p.1.2) else Φ.Zgl a (wt p.1.1 p.1.2)
  have hM : ∀ p, Module.rank k (M p) ≤ C := by
    intro p
    by_cases h : wt p.1.1 p.1.2 ∈ oddRoots
    · rw [show M p = _ from if_pos h]
      exact hb.str _ (Finset.mem_union_left _ h)
    · rw [show M p = _ from if_neg h]
      have : ∀ i j, wt i j ∉ oddRoots → wt i j ∈ [0, wPs, -wPs] := by decide
      exact hb.even _ (this _ _ h)
  have mem : ∀ (x : LinearMap.ker E3) (p : P), E p.1.1 p.1.2 x.1 ∈ M p := by
    intro x p
    by_cases h : wt p.1.1 p.1.2 ∈ oddRoots
    · rw [show M p = _ from if_pos h]
      exact ⟨ent _ x.1.2 _ _, H _ x.1.2 (kz x).1 (kz x).2.1 (kz x).2.2 _ _ p.2 h⟩
    · rw [show M p = _ from if_neg h]
      exact ent _ x.1.2 _ _
  let F : LinearMap.ker E3 →ₗ[k] (∀ p : P, M p) × (Φ.ι × Q → k) :=
    { toFun := fun x => (fun p => ⟨_, mem x p⟩, fun z => (adj (c.n z.1) * x.1.1.2 z.1 * c.n z.1) z.2.1.1 z.2.1.2)
      map_add' := fun x y => Prod.ext rfl (funext fun z => by simp [mul_add, add_mul])
      map_smul' := fun t x => Prod.ext rfl (funext fun z => by simp) }
  have hF : Function.Injective F := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hx1 : ∀ g i j, i ≤ j.rev → x.1.1.1 g i j = 0 := fun g i j h =>
      congrFun (congrArg Subtype.val (congrFun (congrArg Prod.fst hx) ⟨(i, j), h⟩)) g
    have hx2 : ∀ v i j, j < i → (adj (c.n v) * x.1.1.2 v * c.n v) i j = 0 := fun v i j h =>
      congrFun (congrArg Prod.snd hx) (v, ⟨(i, j), h⟩)
    refine Subtype.ext (Subtype.ext (Prod.ext (funext fun g => ?_) (funext fun v => ?_)))
    · ext i j
      by_cases h : i ≤ j.rev
      · exact hx1 g i j h
      · have := congrFun (congrFun (show adj (x.1.1.1 g) = -x.1.1.1 g from x.1.2.2.1 g) i) j
        have h' : ∀ i j : Fin 4, ¬ i ≤ j.rev → j.rev ≤ i.rev.rev := by decide
        rw [adj_apply, hx1 g _ _ (h' i j h), smul_zero, Matrix.neg_apply] at this
        exact neg_eq_zero.1 this.symm
    · have h1 : adj (c.n v) * c.n v = 1 := by simpa [IsGSp] using hn v
      have h2 := mul_eq_one_comm.1 h1
      have h3 : adj (c.n v) * x.1.1.2 v * c.n v = 0 := by
        ext i j
        rcases le_or_gt i j with h | h
        exacts [(x.1.2.2.2.2.2.2.2.1 v).2 i j h, hx2 v i j h]
      calc x.1.1.2 v = (c.n v * adj (c.n v)) * x.1.1.2 v * (c.n v * adj (c.n v)) := by rw [h2, one_mul, mul_one]
        _ = c.n v * (adj (c.n v) * x.1.1.2 v * c.n v) * adj (c.n v) := by simp only [mul_assoc]
        _ = 0 := by rw [h3, mul_zero, zero_mul]
  have r1 : Module.rank k (LinearMap.range E3) ≤ (d + C) + (C + C) := by
    refine (Submodule.rank_le _).trans ?_
    rw [rank_prod', rank_prod']
    exact add_le_add (hb.odd _ h0) (add_le_add (hb.even _ (by decide)) (hb.even _ (by decide)))
  have r2 : Module.rank k (∀ p : P, M p) ≤ 10 * C := by
    rw [rank_pi]
    refine le_trans (Cardinal.sum_le_sum _ _ hM) ?_
    rw [Cardinal.sum_const', Cardinal.mk_fintype, show Fintype.card P = 10 by decide]
    simp
  have r3 : Module.rank k (Φ.ι × Q → k) ≤ 6 * C := by
    haveI := Fintype.ofFinite Φ.ι
    rw [rank_fun', Fintype.card_prod, show Fintype.card Q = 6 by decide, ← Nat.card_eq_fintype_card]
    have := hb.card
    exact_mod_cast (by omega : Nat.card Φ.ι * 6 ≤ 6 * C)
  have r4 := LinearMap.rank_le_of_injective F hF
  rw [rank_prod'] at r4
  rw [← LinearMap.rank_range_add_rank_ker E3]
  refine le_trans (add_le_add r1 (r4.trans (add_le_add r2 r3))) ?_
  exact_mod_cast (by omega : d + C + (C + C) + (10 * C + 6 * C) ≤ d + 20 * C)

end UpperTheory.V.Cu.ReductionTangentLimit

/- English proof (translation)
Introduce `O Γ _ _ _ _ _ _ Φ k _ a hok d C hb c hc hA S hS h hs`. Establish `hm : ∀ i j, i ≠ j → wt i j ∈ aA → (![0, 0, 1, 1] : Fin 4 → ℤ) j < ![0, 0, 1, 1] i` using `by decide`. Rewrite using `[Fr.span_Tan]`. Conclude with `le_trans (tan_flow Φ S c (ReductionTangentLimit.cA Φ a fun v => c.n v 1 0) ![0, 0, 1, 1] (by unfold Symp; decide) (ReductionTangentLimit.limRA hc.res hA.1 hm) fun v => ReductionTangentLimit.limA (hc.pair.low v)) (ReductionTangentLimit.rank_A Φ a hok d C hb S (ReductionTangentLimi …`.
-/
theorem UpperTheory.V.Cu.redTanA : RedTanA := by
  intro O Γ _ _ _ _ _ _ Φ k _ a hok d C hb c hc hA S hS h hs
  have hm : ∀ i j, i ≠ j → wt i j ∈ aA → (![0, 0, 1, 1] : Fin 4 → ℤ) j < ![0, 0, 1, 1] i := by decide
  rw [Fr.span_Tan]
  exact le_trans
    (tan_flow Φ S c (ReductionTangentLimit.cA Φ a fun v => c.n v 1 0) ![0, 0, 1, 1] (by unfold Symp; decide)
      (ReductionTangentLimit.limRA hc.res hA.1 hm) fun v => ReductionTangentLimit.limA (hc.pair.low v))
    (ReductionTangentLimit.rank_A Φ a hok d C hb S (ReductionTangentLimit.cA Φ a fun v => c.n v 1 0) rfl
      (fun v => ReductionTangentLimit.gsp_A (c.n v 1 0))
      (ReductionTangentLimit.oneOddA Φ a hok (fun v => c.n v 1 0) hA.2 (ReductionTangentLimit.characters_agree_at_local_of_typeA hc.pair hc.res hA) S hS h))
