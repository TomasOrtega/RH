import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SectionRingIso

open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

variable {X X' Y Z : Scheme.{0}}

/- English proof (translation)
Rewrite using `[← gs_pull r q z W h, gs_eq q (r z) W h, gs_eq r z (q ⁻¹ᵁ W) h]`. Conclude with `Scheme.Hom.germ_stalkMap_apply r (q ⁻¹ᵁ W) z h _`.
-/
theorem stalkMap_gs (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (W : X.Opens) (h : q (r z) ∈ W) (a : Γ(X, W)) :
    (r.stalkMap z).hom (gs q (r z) W a) = gs (r ≫ q) z W a := by
  rw [← gs_pull r q z W h, gs_eq q (r z) W h, gs_eq r z (q ⁻¹ᵁ W) h]
  exact Scheme.Hom.germ_stalkMap_apply r (q ⁻¹ᵁ W) z h _

abbrev ch (L : LB Y) (j : Fin 1 → L.ι) : Y.Opens := LB.wchart L (fun _ : Fin 1 => 𝟙 Y) j

/- English proof (translation)
Unfold `ch LB.wchart`. Simplify using `[Fin.forall_fin_one]`.
-/
theorem mem_ch {L : LB Y} {j : Fin 1 → L.ι} {y : Y} : y ∈ ch L j ↔ y ∈ L.U (j 0) := by
  unfold ch LB.wchart
  simp [Fin.forall_fin_one]

abbrev vl {L : LB Y} {n : ℕ} (s : H0 L n) (r : Z ⟶ Y) (z : Z) (j : Fin 1 → L.ι) : Z.presheaf.stalk z :=
  gs r z (ch L j) (s.f j)

/- English proof (translation)
Establish `e` using `sec_trans s r z (mem_ch.2 hj) (mem_ch.2 hj')`. Simplify using `only [trF, Fin.prod_univ_one, Category.comp_id, zpow_natCast, Units.val_pow_eq_pow_val] at e`. Conclude with `e`.
-/
theorem vl_trans {L : LB Y} {n : ℕ} (s : H0 L n) (r : Z ⟶ Y) (z : Z) {j j' : Fin 1 → L.ι}
    (hj : r z ∈ L.U (j 0)) (hj' : r z ∈ L.U (j' 0)) :
    vl s r z j = (gm r z _ (L.g (j 0) (j' 0))).val ^ n * vl s r z j' := by
  have e := sec_trans s r z (mem_ch.2 hj) (mem_ch.2 hj')
  simp only [trF, Fin.prod_univ_one, Category.comp_id, zpow_natCast, Units.val_pow_eq_pow_val] at e
  exact e

/- English proof (translation)
Use `⟨(LB.Sec.mk (fun j => (show Γ(Y, ch L j) from a.f j) * (show Γ(Y, ch L j) from b.f j)) (fun i j => ?_) : LB.Sec (L.LinComb (fun _ : Fin 1 => 𝟙 Y) (fun _ => ((n + m : ℕ) : ℤ)))), fun j => rfl⟩` and prove the remaining obligations. Establish `ea` using `a.compat i j`. Establish `eb` using `b.compat i j`. Use `(map_mul _ _ _).trans ?_` and prove the remaining obligations. Use `erw [ea, eb, map_mul]`.

Simplify using `only [LB.LinComb, Nat.cast_add, zpow_add, Finset.prod_mul_distrib, Units.val_mul]`. Conclude with `mul_mul_mul_comm _ _ _ _`.
-/
theorem exists_mul {L : LB Y} {n m : ℕ} (a : H0 L n) (b : H0 L m) : ∃ d : H0 L (n + m), ∀ j : Fin 1 → L.ι,
    (show Γ(Y, ch L j) from d.f j) = (show Γ(Y, ch L j) from a.f j) * (show Γ(Y, ch L j) from b.f j) := by
  refine ⟨(LB.Sec.mk (fun j => (show Γ(Y, ch L j) from a.f j) * (show Γ(Y, ch L j) from b.f j)) (fun i j => ?_) :
    LB.Sec (L.LinComb (fun _ : Fin 1 => 𝟙 Y) (fun _ => ((n + m : ℕ) : ℤ)))), fun j => rfl⟩
  have ea := a.compat i j
  have eb := b.compat i j
  refine (map_mul _ _ _).trans ?_
  erw [ea, eb, map_mul]
  simp only [LB.LinComb, Nat.cast_add, zpow_add, Finset.prod_mul_distrib, Units.val_mul]
  exact mul_mul_mul_comm _ _ _ _

/- English proof (translation)
Establish `hjc : r z ∈ ch L j` using `mem_ch.2 hj`. Establish `key : vl s r z j = (r.stalkMap z).hom (vl s (𝟙 Y) (r z) j)`. Establish `e` using `stalkMap_gs r (𝟙 Y) z (ch L j) hjc (s.f j)`. Use `erw [Category.comp_id] at e`. Conclude with `e.symm`.

Rewrite using `[mem_nonzeroLocus, key, isUnit_map_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, hu⟩`. Establish `e` using `vl_trans s (𝟙 Y) (r z) (mem_ch.1 hk) hj`. Establish `hu' : IsUnit (vl s (𝟙 Y) (r z) k)` using `hu`.

Rewrite `hu'` using `[e]`. Conclude with `(IsUnit.mul_iff.1 hu').2`. Introduce `hu`. Conclude with `⟨j, hjc, hu⟩`.
-/
theorem mem_iff_isUnit {L : LB Y} {n : ℕ} (s : H0 L n) (r : Z ⟶ Y) (z : Z) {j : Fin 1 → L.ι}
    (hj : r z ∈ L.U (j 0)) : r z ∈ nonzeroLocus s ↔ IsUnit (vl s r z j) := by
  have hjc : r z ∈ ch L j := mem_ch.2 hj
  have key : vl s r z j = (r.stalkMap z).hom (vl s (𝟙 Y) (r z) j) := by
    have e := stalkMap_gs r (𝟙 Y) z (ch L j) hjc (s.f j)
    erw [Category.comp_id] at e
    exact e.symm
  rw [mem_nonzeroLocus, key, isUnit_map_iff]
  constructor
  · rintro ⟨k, hk, hu⟩
    have e := vl_trans s (𝟙 Y) (r z) (mem_ch.1 hk) hj
    have hu' : IsUnit (vl s (𝟙 Y) (r z) k) := hu
    rw [e] at hu'
    exact (IsUnit.mul_iff.1 hu').2
  · intro hu
    exact ⟨j, hjc, hu⟩

/- English proof (translation)
Take `⟨hN, e, rfl, rfl⟩` from `h`. Take `⟨hM, e', rfl, rfl⟩` from `h'`. Take `⟨d, hd1, hd2⟩` from `hm N M hN hM e e'`. Conclude with `⟨_, d, hd1, hd2⟩`.
-/
private theorem exists_add_index_of_mul_closed {T : Type} [CommRing T] {S : ℕ → Type} (A B : ∀ n : ℕ, 1 ≤ n → S n → T)
    (hm : ∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : S n) (b : S m), ∃ d : S (n + m),
      A (n + m) (hn.trans (Nat.le_add_right n m)) d = A n hn a * A m hm b ∧
      B (n + m) (hn.trans (Nat.le_add_right n m)) d = B n hn a * B m hm b) {N M : ℕ} {x y x' y' : T}
    (h : ∃ (hN : 1 ≤ N) (e : S N), A N hN e = x ∧ B N hN e = y)
    (h' : ∃ (hM : 1 ≤ M) (e : S M), A M hM e = x' ∧ B M hM e = y') :
    ∃ (hNM : 1 ≤ N + M) (e : S (N + M)), A (N + M) hNM e = x * x' ∧ B (N + M) hNM e = y * y' := by
  obtain ⟨hN, e, rfl, rfl⟩ := h
  obtain ⟨hM, e', rfl, rfl⟩ := h'
  obtain ⟨d, hd1, hd2⟩ := hm N M hN hM e e'
  exact ⟨_, d, hd1, hd2⟩

/- English proof (translation)
Proceed by induction on `p, hp using Nat.le_induction with`. Consider the case `base => rw [Nat.mul_one]`. Simplify `h` using `only [pow_one]`. Consider the case `succ p hp ih`. Rewrite using `[Nat.mul_succ, pow_succ, pow_succ]`.

Conclude with `exists_add_index_of_mul_closed A B hm ih h`.
-/
private theorem exists_mul_index_pow_of_mul_closed {T : Type} [CommRing T] {S : ℕ → Type} (A B : ∀ n : ℕ, 1 ≤ n → S n → T)
    (hm : ∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : S n) (b : S m), ∃ d : S (n + m),
      A (n + m) (hn.trans (Nat.le_add_right n m)) d = A n hn a * A m hm b ∧
      B (n + m) (hn.trans (Nat.le_add_right n m)) d = B n hn a * B m hm b) {N : ℕ} {x y : T}
    (h : ∃ (hN : 1 ≤ N) (e : S N), A N hN e = x ∧ B N hN e = y) (p : ℕ) (hp : 1 ≤ p) :
    ∃ (h1 : 1 ≤ N * p) (e : S (N * p)), A (N * p) h1 e = x ^ p ∧ B (N * p) h1 e = y ^ p := by
  induction p, hp using Nat.le_induction with
  | base => rw [Nat.mul_one]; simpa only [pow_one] using h
  | succ p hp ih =>
    rw [Nat.mul_succ, pow_succ, pow_succ]
    exact exists_add_index_of_mul_closed A B hm ih h

/- English proof (translation)
Establish `Ra : ∃ (h1 : 1 ≤ n) (e : S n), A n h1 e = A n hn a ∧ B n h1 e = B n hn a` using `⟨hn, a, rfl, rfl⟩`. Establish `Rb : ∃ (h1 : 1 ≤ n + 1) (e : S (n + 1)), A (n + 1) h1 e = A (n + 1) (Nat.le_add_left 1 n) b ∧ B (n + 1) h1 e = B (n + 1) (Nat.le_add_left 1 n) b` using `⟨_, b, rfl, rfl⟩`. Generalize the expression as in `A n hn a = x at Ra ua ⊢`. Generalize the expression as in `B n hn a = y at Ra ⊢`. Generalize the expression as in `A (n + 1) (Nat.le_add_left 1 n) b = x' at Rb ⊢`.

Generalize the expression as in `B (n + 1) (Nat.le_add_left 1 n) b = y' at Rb ub ⊢`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Take `⟨h1, e, hx, hy⟩` from `Ra`. Take `⟨h1', e', hx', hy'⟩` from `Rb`.

Rewrite using `[← hx, ← hy, ← hx', ← hy', H n h1 e, H (n + 1) h1' e']`. Expand and normalize the polynomial expressions, which then agree. Introduce `H k hk s`. Establish `P1` using `exists_mul_index_pow_of_mul_closed A B hm Ra (n + 1) (by omega)`. Establish `P2` using `exists_mul_index_pow_of_mul_closed A B hm Rb n hn`.

Rewrite `P2` using `[Nat.mul_comm (n + 1) n]`. Take `⟨h1, e1, hA1, hB1⟩` from `P1`. Take `⟨h2, e2, hA2, hB2⟩` from `P2`. Establish `C` using `hc _ h1 e1 e2 (by rw [hB2]; exact ub.pow n)`. Rewrite `C` using `[hA1, hB1, hA2, hB2]`.

Establish `hn0 : n ≠ 0` using `by omega`. Establish `uy : IsUnit y`. Establish `: IsUnit (x' ^ n * y ^ (n + 1))` using `C ▸ (ua.pow _).mul (ub.pow _)`. Conclude with `(isUnit_pow_iff (Nat.succ_ne_zero n)).1 (IsUnit.mul_iff.1 this).2`. Establish `hA : x = u ^ n * y`.

Apply `((ua.mul ub).pow n).mul_left_cancel` to reduce the goal to its premises. Establish `H' : (u * (x * y')) ^ n = (x' * y) ^ n` using `by rw [H]`. Take the linear combination `C - y * H'`. Establish `hB : x' = u ^ (n + 1) * y'`. Apply `uy.mul_left_cancel` to reduce the goal to its premises.

Take the linear combination `(-1 : T) * H + u * y' * hA`. Establish `hu : IsUnit u`. Establish `: IsUnit (u ^ n * y)` using `hA ▸ ua`. Conclude with `(isUnit_pow_iff hn0).1 (IsUnit.mul_iff.1 this).1`. Establish `Rs : ∃ (h1 : 1 ≤ k) (e : S k), A k h1 e = A k hk s ∧ B k h1 e = B k hk s` using `⟨hk, s, rfl, rfl⟩`.

Establish `P3` using `exists_add_index_of_mul_closed A B hm Rs (exists_mul_index_pow_of_mul_closed A B hm Ra k hk)`. Establish `P4` using `exists_mul_index_pow_of_mul_closed A B hm Rb k hk`. Rewrite `P3` using `[show k + n * k = (n + 1) * k by ring]`. Take `⟨h3, e3, hA3, hB3⟩` from `P3`. Take `⟨h4, e4, hA4, hB4⟩` from `P4`.

Establish `C2` using `hc _ h3 e3 e4 (by rw [hB4]; exact ub.pow k)`. Rewrite `C2` using `[hA3, hB3, hA4, hB4, hA, hB]`. Apply `(((hu.pow (n * k)).mul (uy.pow k)).mul (ub.pow k)).mul_left_cancel` to reduce the goal to its premises. Take the linear combination `C2`.
-/
theorem alg_iff {T : Type} [CommRing T] {S : ℕ → Type} (A B : ∀ n : ℕ, 1 ≤ n → S n → T)
    (hm : ∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : S n) (b : S m), ∃ d : S (n + m),
      A (n + m) (hn.trans (Nat.le_add_right n m)) d = A n hn a * A m hm b ∧
      B (n + m) (hn.trans (Nat.le_add_right n m)) d = B n hn a * B m hm b)
    (hc : ∀ (n : ℕ) (hn : 1 ≤ n) (a b : S n), IsUnit (B n hn b) → A n hn a * B n hn b = A n hn b * B n hn a)
    {n : ℕ} (hn : 1 ≤ n) (a : S n) (b : S (n + 1)) (ua : IsUnit (A n hn a))
    (ub : IsUnit (B (n + 1) (Nat.le_add_left 1 n) b)) (u : T) :
    (∀ (k : ℕ) (hk : 1 ≤ k) (s : S k), A k hk s = u ^ k * B k hk s) ↔
      u * (A n hn a * B (n + 1) (Nat.le_add_left 1 n) b) = A (n + 1) (Nat.le_add_left 1 n) b * B n hn a := by
  have Ra : ∃ (h1 : 1 ≤ n) (e : S n), A n h1 e = A n hn a ∧ B n h1 e = B n hn a := ⟨hn, a, rfl, rfl⟩
  have Rb : ∃ (h1 : 1 ≤ n + 1) (e : S (n + 1)), A (n + 1) h1 e = A (n + 1) (Nat.le_add_left 1 n) b ∧
      B (n + 1) h1 e = B (n + 1) (Nat.le_add_left 1 n) b := ⟨_, b, rfl, rfl⟩
  generalize A n hn a = x at Ra ua ⊢
  generalize B n hn a = y at Ra ⊢
  generalize A (n + 1) (Nat.le_add_left 1 n) b = x' at Rb ⊢
  generalize B (n + 1) (Nat.le_add_left 1 n) b = y' at Rb ub ⊢
  constructor
  · intro H
    obtain ⟨h1, e, hx, hy⟩ := Ra
    obtain ⟨h1', e', hx', hy'⟩ := Rb
    rw [← hx, ← hy, ← hx', ← hy', H n h1 e, H (n + 1) h1' e']
    ring
  · intro H k hk s

    have P1 := exists_mul_index_pow_of_mul_closed A B hm Ra (n + 1) (by omega)
    have P2 := exists_mul_index_pow_of_mul_closed A B hm Rb n hn
    rw [Nat.mul_comm (n + 1) n] at P2
    obtain ⟨h1, e1, hA1, hB1⟩ := P1
    obtain ⟨h2, e2, hA2, hB2⟩ := P2
    have C := hc _ h1 e1 e2 (by rw [hB2]; exact ub.pow n)
    rw [hA1, hB1, hA2, hB2] at C
    have hn0 : n ≠ 0 := by omega
    have uy : IsUnit y := by
      have : IsUnit (x' ^ n * y ^ (n + 1)) := C ▸ (ua.pow _).mul (ub.pow _)
      exact (isUnit_pow_iff (Nat.succ_ne_zero n)).1 (IsUnit.mul_iff.1 this).2
    have hA : x = u ^ n * y := by
      apply ((ua.mul ub).pow n).mul_left_cancel
      have H' : (u * (x * y')) ^ n = (x' * y) ^ n := by rw [H]
      linear_combination C - y * H'
    have hB : x' = u ^ (n + 1) * y' := by
      apply uy.mul_left_cancel
      linear_combination (-1 : T) * H + u * y' * hA
    have hu : IsUnit u := by
      have : IsUnit (u ^ n * y) := hA ▸ ua
      exact (isUnit_pow_iff hn0).1 (IsUnit.mul_iff.1 this).1
    have Rs : ∃ (h1 : 1 ≤ k) (e : S k), A k h1 e = A k hk s ∧ B k h1 e = B k hk s := ⟨hk, s, rfl, rfl⟩
    have P3 := exists_add_index_of_mul_closed A B hm Rs (exists_mul_index_pow_of_mul_closed A B hm Ra k hk)
    have P4 := exists_mul_index_pow_of_mul_closed A B hm Rb k hk
    rw [show k + n * k = (n + 1) * k by ring] at P3
    obtain ⟨h3, e3, hA3, hB3⟩ := P3
    obtain ⟨h4, e4, hA4, hB4⟩ := P4
    have C2 := hc _ h3 e3 e4 (by rw [hB4]; exact ub.pow k)
    rw [hA3, hB3, hA4, hB4, hA, hB] at C2
    apply (((hu.pow (n * k)).mul (uy.pow k)).mul (ub.pow k)).mul_left_cancel
    linear_combination C2

/- English proof (translation)
Set `F : Γ(X', W)` to `(X'.presheaf.map (homOfLE h₁).op).hom ((Φ.app (ch L j)).hom (t.f j)) * (X'.presheaf.map (homOfLE h₂).op).hom (s.f k)`. Establish `hg : ∀ x (hx : x ∈ W), gs (𝟙 X') x W F = vl t (𝟙 X' ≫ Φ) x j * vl s (𝟙 X') x k`. Introduce `x hx`. Rewrite using `[gs_mul _ x _ hx, gs_res _ x h₁ hx]`. Use `erw [gs_res _ x h₂ hx]`.

Use `erw [gs_pull (𝟙 X') Φ x _ (h₁ hx)]`. Establish `hF : IsUnit F`. Use `RingedSpace.isUnit_of_isUnit_germ X'.toRingedSpace W F fun x hx => ?_` and prove the remaining obligations. Establish `e` using `gs_eq (𝟙 X') x W hx F`. Establish `h0` using `hu x hx`.

Rewrite `h0` using `[← hg x hx, e]`. Conclude with `h0`. Use `⟨hF.unit, fun Z r z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[← gs_unit r z W hz, IsUnit.unit_spec]`. Establish `e1` using `stalkMap_gs r (𝟙 X') z W hz F`.

Rewrite `e1` using `[Category.comp_id]`. Rewrite using `[← e1, hg (r z) hz, map_mul]`. Establish `e2` using `stalkMap_gs r (𝟙 X' ≫ Φ) z (ch L j) (h₁ hz) (t.f j)`. Establish `e3` using `stalkMap_gs r (𝟙 X') z (ch L' k) (h₂ hz) (s.f k)`. Rewrite `e2` using `[Category.id_comp]`.

Rewrite `e3` using `[Category.comp_id]`. Use `erw [e2, e3]`.
-/
theorem exists_loc {L : LB X} {L' : LB X'} (Φ : X' ⟶ X) {n m : ℕ} (t : H0 L m) (s : H0 L' n) (j : Fin 1 → L.ι)
    (k : Fin 1 → L'.ι) (W : X'.Opens) (h₁ : W ≤ Φ ⁻¹ᵁ ch L j) (h₂ : W ≤ ch L' k)
    (hu : ∀ x ∈ W, IsUnit (vl t (𝟙 X' ≫ Φ) x j * vl s (𝟙 X') x k)) :
    ∃ f : Γ(X', W)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z), r z ∈ W →
      (gm r z W f).val = vl t (r ≫ Φ) z j * vl s r z k := by
  let F : Γ(X', W) := (X'.presheaf.map (homOfLE h₁).op).hom ((Φ.app (ch L j)).hom (t.f j)) *
    (X'.presheaf.map (homOfLE h₂).op).hom (s.f k)
  have hg : ∀ x (hx : x ∈ W), gs (𝟙 X') x W F = vl t (𝟙 X' ≫ Φ) x j * vl s (𝟙 X') x k := by
    intro x hx
    rw [gs_mul _ x _ hx, gs_res _ x h₁ hx]
    erw [gs_res _ x h₂ hx]
    erw [gs_pull (𝟙 X') Φ x _ (h₁ hx)]
  have hF : IsUnit F := by
    refine RingedSpace.isUnit_of_isUnit_germ X'.toRingedSpace W F fun x hx => ?_
    have e := gs_eq (𝟙 X') x W hx F
    have h0 := hu x hx
    rw [← hg x hx, e] at h0
    exact h0
  refine ⟨hF.unit, fun Z r z hz => ?_⟩
  rw [← gs_unit r z W hz, IsUnit.unit_spec]
  have e1 := stalkMap_gs r (𝟙 X') z W hz F
  rw [Category.comp_id] at e1
  rw [← e1, hg (r z) hz, map_mul]
  have e2 := stalkMap_gs r (𝟙 X' ≫ Φ) z (ch L j) (h₁ hz) (t.f j)
  have e3 := stalkMap_gs r (𝟙 X') z (ch L' k) (h₂ hz) (s.f k)
  rw [Category.id_comp] at e2
  rw [Category.comp_id] at e3
  erw [e2, e3]

/- English proof (translation)
Establish `hJc : Φ x ∈ ch L J` using `mem_ch.2 hJ`. Establish `hKc : x ∈ ch L' K` using `mem_ch.2 hK`. Use `alg_iff (fun k hk s => vl (θ k hk s) Φ x J) (fun k hk s => vl s (𝟙 X') x K) ?_ ?_ hn a b ?_ ?_ u` and prove the remaining obligations. Introduce `n m hn hm a b`. Take `⟨d, hd⟩` from `exists_mul a b`.

Use `⟨d, ?_, ?_⟩` and prove the remaining obligations. Establish `e` using `hmul n m hn hm a b d hd J dsimp only at e`. Simplify using `only [vl]`. Use `erw [e, gs_mul _ x _ hJc]`. Establish `e` using `hd K dsimp only at e`.

Simplify using `only [vl]`. Use `erw [e, gs_mul _ x _ hKc]`. Introduce `n hn a b hu`. Conclude with `hc n hn a b x J K ((mem_iff_isUnit b (𝟙 X') x hK).2 hu) hJ hK`. Establish `h1 : x ∈ Φ ⁻¹ᵁ nonzeroLocus (θ n hn a)` using `by rw [hD]; exact ha`.

Conclude with `(mem_iff_isUnit (θ n hn a) Φ x hJ).1 h1`. Conclude with `(mem_iff_isUnit b (𝟙 X') x hK).1 hb`.
-/
private theorem core_lemma {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} (θ : ∀ n : ℕ, 1 ≤ n → H0 L' n → H0 L n)
    (hmul : ∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : H0 L' n) (b : H0 L' m) (d : H0 L' (n + m)),
      (∀ j : Fin 1 → L'.ι, (show Γ(X', ch L' j) from d.f j) =
        (show Γ(X', ch L' j) from a.f j) * (show Γ(X', ch L' j) from b.f j)) →
      ∀ j : Fin 1 → L.ι, (show Γ(X, ch L j) from (θ (n + m) (hn.trans (Nat.le_add_right n m)) d).f j) =
        (show Γ(X, ch L j) from (θ n hn a).f j) * (show Γ(X, ch L j) from (θ m hm b).f j))
    (Φ : X' ⟶ X) (hD : ∀ (n : ℕ) (hn : 1 ≤ n) (b : H0 L' n), Φ ⁻¹ᵁ nonzeroLocus (θ n hn b) = nonzeroLocus b)
    (hc : ∀ (n : ℕ) (hn : 1 ≤ n) (a b : H0 L' n) (x : X') (j : Fin 1 → L.ι) (k : Fin 1 → L'.ι),
      x ∈ nonzeroLocus b → Φ x ∈ L.U (j 0) → x ∈ L'.U (k 0) →
      vl (θ n hn a) Φ x j * vl b (𝟙 X') x k = vl (θ n hn b) Φ x j * vl a (𝟙 X') x k) (x : X') (J : Fin 1 → L.ι) (K : Fin 1 → L'.ι)
    (hJ : Φ x ∈ L.U (J 0)) (hK : x ∈ L'.U (K 0)) {n : ℕ} (hn : 1 ≤ n) (a : H0 L' n) (b : H0 L' (n + 1))
    (ha : x ∈ nonzeroLocus a) (hb : x ∈ nonzeroLocus b) (u : X'.presheaf.stalk x) :
    (∀ (k : ℕ) (hk : 1 ≤ k) (s : H0 L' k), vl (θ k hk s) Φ x J = u ^ k * vl s (𝟙 X') x K) ↔
      u * (vl (θ n hn a) Φ x J * vl b (𝟙 X') x K) =
        vl (θ (n + 1) (Nat.le_add_left 1 n) b) Φ x J * vl a (𝟙 X') x K := by
  have hJc : Φ x ∈ ch L J := mem_ch.2 hJ
  have hKc : x ∈ ch L' K := mem_ch.2 hK
  refine alg_iff (fun k hk s => vl (θ k hk s) Φ x J) (fun k hk s => vl s (𝟙 X') x K) ?_ ?_ hn a b ?_ ?_ u
  · intro n m hn hm a b
    obtain ⟨d, hd⟩ := exists_mul a b
    refine ⟨d, ?_, ?_⟩
    · have e := hmul n m hn hm a b d hd J
      dsimp only at e
      simp only [vl]
      erw [e, gs_mul _ x _ hJc]
    · have e := hd K
      dsimp only at e
      simp only [vl]
      erw [e, gs_mul _ x _ hKc]
  · intro n hn a b hu
    exact hc n hn a b x J K ((mem_iff_isUnit b (𝟙 X') x hK).2 hu) hJ hK
  · have h1 : x ∈ Φ ⁻¹ᵁ nonzeroLocus (θ n hn a) := by rw [hD]; exact ha
    exact (mem_iff_isUnit (θ n hn a) Φ x hJ).1 h1
  · exact (mem_iff_isUnit b (𝟙 X') x hK).1 hb

/- English proof (translation)
Set `J : ((L.pull Φ).div L').ι → Fin 1 → L.ι` to `fun p _ => p.1 PUnit.unit`. Set `K : ((L.pull Φ).div L').ι → Fin 1 → L'.ι` to `fun p _ => p.2`. Establish `hJ : ∀ p, ∀ x ∈ ((L.pull Φ).div L').U p, Φ x ∈ L.U (J p 0)`. Introduce `p x hx`. Establish `h1 : x ∈ L.wchart (fun _ : PUnit => Φ) p.1` using `hx.1`.

Unfold `LB.wchart at h1`. Simplify using `only [TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage] at h1`. Conclude with `h1 PUnit.unit`. Establish `hK : ∀ p, ∀ x ∈ ((L.pull Φ).div L').U p, x ∈ L'.U (K p 0)` using `fun p x hx => hx.2`. Establish `unitT : ∀ p {m : ℕ} (hm : 1 ≤ m) (s : H0 L' m) (y : X'), y ∈ ((L.pull Φ).div L').U p → y ∈ nonzeroLocus s → IsUnit (vl (θ m hm s) Φ y (J p))`.

Introduce `p m hm s y hy hs`. Establish `h1 : y ∈ Φ ⁻¹ᵁ nonzeroLocus (θ m hm s)` using `by rw [hD]; exact hs`. Conclude with `(mem_iff_isUnit (θ m hm s) Φ y (hJ p y hy)).1 h1`. Establish `unitS : ∀ p {m : ℕ} (s : H0 L' m) (y : X'), y ∈ ((L.pull Φ).div L').U p → y ∈ nonzeroLocus s → IsUnit (vl s (𝟙 X') y (K p))` using `fun p m s y hy hs => (mem_iff_isUnit s (𝟙 X') y (hK p y hy)).1 hs`. Establish `uniq : ∀ p y (hy : y ∈ ((L.pull Φ).div L').U p) (u u' : X'.presheaf.stalk y), (∀ (k : ℕ) (hk : 1 ≤ k) (s : H0 L' k), vl (θ k hk s) Φ y (J p) = u ^ k * vl s (𝟙 X') y (K p)) → (∀ (k : ℕ) (hk : 1 ≤ k) (s : H0 L' k), vl (θ k hk s) Φ y (J p) = u' ^ k * vl s (𝟙 X') y (K p)) → u = u'`.

Introduce `p y hy u u' h h'`. Take `⟨n, hn, a, b, ha, hb⟩` from `hcov y`. Establish `c` using `(core_lemma θ hmul Φ hD hc y (J p) (K p) (hJ p y hy) (hK p y hy) hn a b ha hb u).1 h`. Establish `c'` using `(core_lemma θ hmul Φ hD hc y (J p) (K p) (hJ p y hy) (hK p y hy) hn a b ha hb u').1 h'`. Conclude with `((unitT p hn a y hy ha).mul (unitS p b y hy hb)).mul_right_cancel (c.trans c'.symm)`.

Establish `hsec : ∀ p : ((L.pull Φ).div L').ι, ∃ f : (Γ(X', ((L.pull Φ).div L').U p))ˣ, ∀ x (hx : x ∈ ((L.pull Φ).div L').U p) (k : ℕ) (hk : 1 ≤ k) (s : H0 L' k), vl (θ k hk s) Φ x (J p) = (gs (𝟙 X') x _ f.val) ^ k * vl s (𝟙 X') x (K p)`. Introduce `p`. Use `choose N hN A B hA hB using hcov`. Set `V : X'.Opens` to `((L.pull Φ).div L').U p`. Set `Uo : V → X'.Opens` to `fun x => V ⊓ nonzeroLocus (A x) ⊓ nonzeroLocus (B x)`.

Establish `hUo : ∀ x : V, (x : X') ∈ Uo x` using `fun x => ⟨⟨x.2, hA x⟩, hB x⟩`. Establish `eloc : ∀ x : V, ∃ e : (Γ(X', Uo x))ˣ, ∀ y (hy : y ∈ Uo x), (gm (𝟙 X') y (Uo x) e).val * (vl (θ _ (hN x) (A x)) Φ y (J p) * vl (B x) (𝟙 X') y (K p)) = vl (θ _ (Nat.le_add_left 1 (N x)) (B x)) Φ y (J p) * vl (A x) (𝟙 X') y (K p)`. Introduce `x`. Establish `l1 : Uo x ≤ Φ ⁻¹ᵁ ch L (J p)` using `fun y hy => mem_ch.2 (hJ p y hy.1.1)`. Establish `l2 : Uo x ≤ ch L' (K p)` using `fun y hy => mem_ch.2 (hK p y hy.1.1)`.

Take `⟨f1, hf1⟩` from `exists_loc Φ (θ _ (hN x) (A x)) (B x) (J p) (K p) (Uo x) l1 l2 (fun y hy => by`. Rewrite using `[Category.id_comp]`. Conclude with `(unitT p (hN x) (A x) y hy.1.1 hy.1.2).mul (unitS p (B x) y hy.1.1 hy.2))`. Take `⟨f2, hf2⟩` from `exists_loc Φ (θ _ (Nat.le_add_left 1 (N x)) (B x)) (A x) (J p) (K p) (Uo x) l1 l2 (fun y hy => by`. Rewrite using `[Category.id_comp]`.

Conclude with `(unitT p _ (B x) y hy.1.1 hy.2).mul (unitS p (A x) y hy.1.1 hy.1.2))`. Use `⟨f2 * f1⁻¹, fun y hy => ?_⟩` and prove the remaining obligations. Establish `g1` using `hf1 X' (𝟙 X') y hy`. Establish `g2` using `hf2 X' (𝟙 X') y hy`. Rewrite `g1`, `g2` using `[Category.id_comp]`.

Rewrite using `[map_mul, map_inv, Units.val_mul, ← g1, ← g2, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]`. Use `choose e he using eloc`. Establish `uprop : ∀ (x : V) y (hy : y ∈ Uo x) (k : ℕ) (hk : 1 ≤ k) (s : H0 L' k), vl (θ k hk s) Φ y (J p) = (gm (𝟙 X') y (Uo x) (e x)).val ^ k * vl s (𝟙 X') y (K p)` using `fun x y hy => (core_lemma θ hmul Φ hD hc y (J p) (K p) (hJ p y hy.1.1) (hK p y hy.1.1) (hN x) (A x) (B x) hy.1.2 hy.2 _).2 (he x y hy)`. Establish `compat : TopCat.Presheaf.IsCompatible X'.sheaf.1 Uo (fun x => (e x).val)`. Introduce `x x'`.

Apply `fn_ext` to reduce the goal to its premises. Introduce `y hy`. Use `erw [gs_res (𝟙 X') y inf_le_left hy, gs_res (𝟙 X') y inf_le_right hy, gs_unit _ y _ hy.1, gs_unit _ y _ hy.2]`. Conclude with `uniq p y hy.1.1.1 _ _ (uprop x y hy.1) (uprop x' y hy.2)`. Take `⟨G, hG, -⟩` from `X'.sheaf.existsUnique_gluing' Uo V (fun x => homOfLE (fun y hy => hy.1.1)) (fun y hy => (Opens.mem_iSup).2 ⟨⟨y, hy⟩, hUo ⟨y, hy⟩⟩) (fun x => (e x).val) compat`.

Establish `gG : ∀ y (hy : y ∈ V), gs (𝟙 X') y V G = (gm (𝟙 X') y (Uo ⟨y, hy⟩) (e ⟨y, hy⟩)).val`. Introduce `y hy`. Use `(gs_res (𝟙 X') y (show Uo ⟨y, hy⟩ ≤ V from fun z hz => hz.1.1) (hUo ⟨y, hy⟩) G).symm.trans ?_` and prove the remaining obligations. Use `erw [hG ⟨y, hy⟩]`. Conclude with `gs_unit _ _ _ (hUo _) _`.

Establish `hGu : IsUnit G`. Use `RingedSpace.isUnit_of_isUnit_germ X'.toRingedSpace V G fun y hy => ?_` and prove the remaining obligations. Establish `h0 : IsUnit (gs (𝟙 X') y V G)` using `by rw [gG y hy]; exact Units.isUnit _`. Use `erw [gs_eq (𝟙 X') y V hy] at h0`. Conclude with `h0`.

Use `⟨hGu.unit, fun y hy k hk s => ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec, gG y hy]`. Conclude with `uprop ⟨y, hy⟩ y (hUo _) k hk s`. Use `choose f hf using hsec`. Use `⟨⟨f⟩, ?_, ?_⟩` and prove the remaining obligations.

Introduce `p q clear hmul hD hc hcov unitT unitS`. Apply `Units.ext` to reduce the goal to its premises. Apply `fn_ext` to reduce the goal to its premises. Introduce `y hy`. Establish `hp : y ∈ ((L.pull Φ).div L').U p` using `hy.1`.

Establish `hq : y ∈ ((L.pull Φ).div L').U q` using `hy.2`. Establish `hpJ` using `hJ p y hp`. Establish `hqJ` using `hJ q y hq`. Establish `hpK` using `hK p y hp`. Establish `hqK` using `hK q y hq`.

Rewrite using `[Units.val_mul, gs_mul _ y _ hy]`. Use `erw [gs_res (𝟙 X') y inf_le_left hy, gs_res (𝟙 X') y inf_le_right hy]`. Establish `hW : gs (𝟙 X') y _ (((L.pull Φ).div L').g p q).val = (gm Φ y _ (L.g (J p 0) (J q 0))).val * ((gm (𝟙 X') y _ (L'.g (K p 0) (K q 0)))⁻¹).val`. Unfold `LB.div`. Simplify using `only`.

Rewrite using `[Units.val_mul, gs_mul _ y _ hy, ← map_inv]`. Use `erw [gs_res (𝟙 X') y _ hy, gs_res (𝟙 X') y _ hy, gs_unit _ y _ (⟨hp.1, hq.1⟩ : y ∈ (L.pull Φ).U p.1 ⊓ (L.pull Φ).U q.1), gs_unit _ y _ (⟨hp.2, hq.2⟩ : y ∈ L'.U p.2 ⊓ L'.U q.2), gm_linComb L (fun _ : PUnit => Φ) (fun _ => 1) (𝟙 X') y p.1 q.1 hp.1 hq.1, map_inv]`. Simplify using `only [Finset.univ_unique, Finset.prod_singleton, zpow_one, Category.id_comp]`. Both sides reduce to the same expression. Rewrite using `[hW]`.

Apply `uniq p y hp _ _ (hf p y hp)` to reduce the goal to its premises. Introduce `m hm s`. Establish `t1` using `vl_trans (θ m hm s) Φ y (j := J p) (j' := J q) hpJ hqJ`. Establish `t2` using `vl_trans s (𝟙 X') y (j := K p) (j' := K q) hpK hqK`. Rewrite using `[t1, hf q y hq m hm s, t2]`.

Establish `hH : ((gm (𝟙 X') y _ (L'.g (K p 0) (K q 0)))⁻¹).val ^ m * (gm (𝟙 X') y _ (L'.g (K p 0) (K q 0))).val ^ m = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, inv_mul_cancel, one_pow, Units.val_one]`. Take the linear combination `(-((gm Φ y _ (L.g (J p 0) (J q 0))).val ^ m * (gs (𝟙 X') y _ (f q).val) ^ m * vl s (𝟙 X') y (K q))) * hH`. Introduce `Z r z j k hj hk n hn a`. Establish `hx : r z ∈ ((L.pull Φ).div L').U ((fun _ => j), k)`.

Use `⟨?_, hk⟩` and prove the remaining obligations. Use `show r z ∈ L.wchart (fun _ : PUnit => Φ) (fun _ => j)`. Unfold `LB.wchart`. Simplify using `using hj`. Establish `e` using `congrArg (r.stalkMap z).hom (hf ((fun _ => j), k) (r z) hx n hn a)`.

Rewrite `e` using `[map_mul, map_pow]`. Establish `e1` using `stalkMap_gs r Φ z (ch L (fun _ => j)) (mem_ch.2 hj) ((θ n hn a).f (fun _ => j))`. Establish `e2` using `stalkMap_gs r (𝟙 X') z _ hx (f ((fun _ => j), k)).val`. Establish `e3` using `stalkMap_gs r (𝟙 X') z (ch L' (fun _ => k)) (mem_ch.2 hk) (a.f (fun _ => k))`. Rewrite `e2`, `e3` using `[Category.comp_id]`.

Use `erw [e1, e2, e3] at e`. Rewrite `e` using `[gs_unit r z _ hx]`. Conclude with `e`.
-/
theorem core {L : LB X} {L' : LB X'} (θ : ∀ n : ℕ, 1 ≤ n → H0 L' n → H0 L n)
    (hmul : ∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : H0 L' n) (b : H0 L' m) (d : H0 L' (n + m)),
      (∀ j : Fin 1 → L'.ι, (show Γ(X', ch L' j) from d.f j) =
        (show Γ(X', ch L' j) from a.f j) * (show Γ(X', ch L' j) from b.f j)) →
      ∀ j : Fin 1 → L.ι, (show Γ(X, ch L j) from (θ (n + m) (hn.trans (Nat.le_add_right n m)) d).f j) =
        (show Γ(X, ch L j) from (θ n hn a).f j) * (show Γ(X, ch L j) from (θ m hm b).f j))
    (Φ : X' ⟶ X) (hD : ∀ (n : ℕ) (hn : 1 ≤ n) (b : H0 L' n), Φ ⁻¹ᵁ nonzeroLocus (θ n hn b) = nonzeroLocus b)
    (hc : ∀ (n : ℕ) (hn : 1 ≤ n) (a b : H0 L' n) (x : X') (j : Fin 1 → L.ι) (k : Fin 1 → L'.ι),
      x ∈ nonzeroLocus b → Φ x ∈ L.U (j 0) → x ∈ L'.U (k 0) →
      vl (θ n hn a) Φ x j * vl b (𝟙 X') x k = vl (θ n hn b) Φ x j * vl a (𝟙 X') x k)
    (hcov : ∀ x : X', ∃ (n : ℕ) (_ : 1 ≤ n) (a : H0 L' n) (b : H0 L' (n + 1)),
      x ∈ nonzeroLocus a ∧ x ∈ nonzeroLocus b) :
    ∃ w : LB.Iso L' (L.pull Φ), w.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι),
      Φ (r z) ∈ L.U j → r z ∈ L'.U k → ∀ (n : ℕ) (hn : 1 ≤ n) (a : H0 L' n),
      vl (θ n hn a) (r ≫ Φ) z (fun _ => j) = (gw w r z j k).val ^ n * vl a r z (fun _ => k) := by
  classical

  let J : ((L.pull Φ).div L').ι → Fin 1 → L.ι := fun p _ => p.1 PUnit.unit
  let K : ((L.pull Φ).div L').ι → Fin 1 → L'.ι := fun p _ => p.2
  have hJ : ∀ p, ∀ x ∈ ((L.pull Φ).div L').U p, Φ x ∈ L.U (J p 0) := by
    intro p x hx
    have h1 : x ∈ L.wchart (fun _ : PUnit => Φ) p.1 := hx.1
    unfold LB.wchart at h1
    simp only [TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage] at h1
    exact h1 PUnit.unit
  have hK : ∀ p, ∀ x ∈ ((L.pull Φ).div L').U p, x ∈ L'.U (K p 0) := fun p x hx => hx.2
  have unitT : ∀ p {m : ℕ} (hm : 1 ≤ m) (s : H0 L' m) (y : X'), y ∈ ((L.pull Φ).div L').U p →
      y ∈ nonzeroLocus s → IsUnit (vl (θ m hm s) Φ y (J p)) := by
    intro p m hm s y hy hs
    have h1 : y ∈ Φ ⁻¹ᵁ nonzeroLocus (θ m hm s) := by rw [hD]; exact hs
    exact (mem_iff_isUnit (θ m hm s) Φ y (hJ p y hy)).1 h1
  have unitS : ∀ p {m : ℕ} (s : H0 L' m) (y : X'), y ∈ ((L.pull Φ).div L').U p →
      y ∈ nonzeroLocus s → IsUnit (vl s (𝟙 X') y (K p)) :=
    fun p m s y hy hs => (mem_iff_isUnit s (𝟙 X') y (hK p y hy)).1 hs

  have uniq : ∀ p y (hy : y ∈ ((L.pull Φ).div L').U p) (u u' : X'.presheaf.stalk y),
      (∀ (k : ℕ) (hk : 1 ≤ k) (s : H0 L' k), vl (θ k hk s) Φ y (J p) = u ^ k * vl s (𝟙 X') y (K p)) →
      (∀ (k : ℕ) (hk : 1 ≤ k) (s : H0 L' k), vl (θ k hk s) Φ y (J p) = u' ^ k * vl s (𝟙 X') y (K p)) →
      u = u' := by
    intro p y hy u u' h h'
    obtain ⟨n, hn, a, b, ha, hb⟩ := hcov y
    have c := (core_lemma θ hmul Φ hD hc y (J p) (K p) (hJ p y hy) (hK p y hy) hn a b ha hb u).1 h
    have c' := (core_lemma θ hmul Φ hD hc y (J p) (K p) (hJ p y hy) (hK p y hy) hn a b ha hb u').1 h'
    exact ((unitT p hn a y hy ha).mul (unitS p b y hy hb)).mul_right_cancel (c.trans c'.symm)
  have hsec : ∀ p : ((L.pull Φ).div L').ι, ∃ f : (Γ(X', ((L.pull Φ).div L').U p))ˣ,
      ∀ x (hx : x ∈ ((L.pull Φ).div L').U p) (k : ℕ) (hk : 1 ≤ k) (s : H0 L' k),
        vl (θ k hk s) Φ x (J p) = (gs (𝟙 X') x _ f.val) ^ k * vl s (𝟙 X') x (K p) := by
    intro p
    choose N hN A B hA hB using hcov
    let V : X'.Opens := ((L.pull Φ).div L').U p
    let Uo : V → X'.Opens := fun x => V ⊓ nonzeroLocus (A x) ⊓ nonzeroLocus (B x)
    have hUo : ∀ x : V, (x : X') ∈ Uo x := fun x => ⟨⟨x.2, hA x⟩, hB x⟩
    have eloc : ∀ x : V, ∃ e : (Γ(X', Uo x))ˣ, ∀ y (hy : y ∈ Uo x),
        (gm (𝟙 X') y (Uo x) e).val * (vl (θ _ (hN x) (A x)) Φ y (J p) * vl (B x) (𝟙 X') y (K p)) =
          vl (θ _ (Nat.le_add_left 1 (N x)) (B x)) Φ y (J p) * vl (A x) (𝟙 X') y (K p) := by
      intro x
      have l1 : Uo x ≤ Φ ⁻¹ᵁ ch L (J p) := fun y hy => mem_ch.2 (hJ p y hy.1.1)
      have l2 : Uo x ≤ ch L' (K p) := fun y hy => mem_ch.2 (hK p y hy.1.1)
      obtain ⟨f1, hf1⟩ := exists_loc Φ (θ _ (hN x) (A x)) (B x) (J p) (K p) (Uo x) l1 l2 (fun y hy => by
        rw [Category.id_comp]
        exact (unitT p (hN x) (A x) y hy.1.1 hy.1.2).mul (unitS p (B x) y hy.1.1 hy.2))
      obtain ⟨f2, hf2⟩ := exists_loc Φ (θ _ (Nat.le_add_left 1 (N x)) (B x)) (A x) (J p) (K p) (Uo x) l1 l2
        (fun y hy => by
          rw [Category.id_comp]
          exact (unitT p _ (B x) y hy.1.1 hy.2).mul (unitS p (A x) y hy.1.1 hy.1.2))
      refine ⟨f2 * f1⁻¹, fun y hy => ?_⟩
      have g1 := hf1 X' (𝟙 X') y hy
      have g2 := hf2 X' (𝟙 X') y hy
      rw [Category.id_comp] at g1 g2
      rw [map_mul, map_inv, Units.val_mul, ← g1, ← g2, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
    choose e he using eloc
    have uprop : ∀ (x : V) y (hy : y ∈ Uo x) (k : ℕ) (hk : 1 ≤ k) (s : H0 L' k),
        vl (θ k hk s) Φ y (J p) = (gm (𝟙 X') y (Uo x) (e x)).val ^ k * vl s (𝟙 X') y (K p) :=
      fun x y hy => (core_lemma θ hmul Φ hD hc y (J p) (K p) (hJ p y hy.1.1) (hK p y hy.1.1) (hN x) (A x) (B x)
        hy.1.2 hy.2 _).2 (he x y hy)
    have compat : TopCat.Presheaf.IsCompatible X'.sheaf.1 Uo (fun x => (e x).val) := by
      intro x x'
      apply fn_ext
      intro y hy
      erw [gs_res (𝟙 X') y inf_le_left hy, gs_res (𝟙 X') y inf_le_right hy, gs_unit _ y _ hy.1, gs_unit _ y _ hy.2]
      exact uniq p y hy.1.1.1 _ _ (uprop x y hy.1) (uprop x' y hy.2)
    obtain ⟨G, hG, -⟩ := X'.sheaf.existsUnique_gluing' Uo V (fun x => homOfLE (fun y hy => hy.1.1))
      (fun y hy => (Opens.mem_iSup).2 ⟨⟨y, hy⟩, hUo ⟨y, hy⟩⟩) (fun x => (e x).val) compat
    have gG : ∀ y (hy : y ∈ V), gs (𝟙 X') y V G = (gm (𝟙 X') y (Uo ⟨y, hy⟩) (e ⟨y, hy⟩)).val := by
      intro y hy
      refine (gs_res (𝟙 X') y (show Uo ⟨y, hy⟩ ≤ V from fun z hz => hz.1.1) (hUo ⟨y, hy⟩) G).symm.trans ?_
      erw [hG ⟨y, hy⟩]
      exact gs_unit _ _ _ (hUo _) _
    have hGu : IsUnit G := by
      refine RingedSpace.isUnit_of_isUnit_germ X'.toRingedSpace V G fun y hy => ?_
      have h0 : IsUnit (gs (𝟙 X') y V G) := by rw [gG y hy]; exact Units.isUnit _
      erw [gs_eq (𝟙 X') y V hy] at h0
      exact h0
    refine ⟨hGu.unit, fun y hy k hk s => ?_⟩
    rw [IsUnit.unit_spec, gG y hy]
    exact uprop ⟨y, hy⟩ y (hUo _) k hk s
  choose f hf using hsec
  refine ⟨⟨f⟩, ?_, ?_⟩
  · intro p q
    clear hmul hD hc hcov unitT unitS
    apply Units.ext
    apply fn_ext
    intro y hy
    have hp : y ∈ ((L.pull Φ).div L').U p := hy.1
    have hq : y ∈ ((L.pull Φ).div L').U q := hy.2
    have hpJ := hJ p y hp
    have hqJ := hJ q y hq
    have hpK := hK p y hp
    have hqK := hK q y hq
    rw [Units.val_mul, gs_mul _ y _ hy]
    erw [gs_res (𝟙 X') y inf_le_left hy, gs_res (𝟙 X') y inf_le_right hy]
    have hW : gs (𝟙 X') y _ (((L.pull Φ).div L').g p q).val =
        (gm Φ y _ (L.g (J p 0) (J q 0))).val * ((gm (𝟙 X') y _ (L'.g (K p 0) (K q 0)))⁻¹).val := by
      unfold LB.div
      dsimp only
      rw [Units.val_mul, gs_mul _ y _ hy, ← map_inv]
      erw [gs_res (𝟙 X') y _ hy, gs_res (𝟙 X') y _ hy, gs_unit _ y _ (⟨hp.1, hq.1⟩ : y ∈ (L.pull Φ).U p.1 ⊓ (L.pull Φ).U q.1),
        gs_unit _ y _ (⟨hp.2, hq.2⟩ : y ∈ L'.U p.2 ⊓ L'.U q.2),
        gm_linComb L (fun _ : PUnit => Φ) (fun _ => 1) (𝟙 X') y p.1 q.1 hp.1 hq.1, map_inv]
      simp only [Finset.univ_unique, Finset.prod_singleton, zpow_one, Category.id_comp]
      rfl
    rw [hW]
    apply uniq p y hp _ _ (hf p y hp)
    intro m hm s
    have t1 := vl_trans (θ m hm s) Φ y (j := J p) (j' := J q) hpJ hqJ
    have t2 := vl_trans s (𝟙 X') y (j := K p) (j' := K q) hpK hqK
    rw [t1, hf q y hq m hm s, t2]
    have hH : ((gm (𝟙 X') y _ (L'.g (K p 0) (K q 0)))⁻¹).val ^ m * (gm (𝟙 X') y _ (L'.g (K p 0) (K q 0))).val ^ m = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, inv_mul_cancel,
        one_pow, Units.val_one]
    linear_combination (-((gm Φ y _ (L.g (J p 0) (J q 0))).val ^ m * (gs (𝟙 X') y _ (f q).val) ^ m *
      vl s (𝟙 X') y (K q))) * hH
  · intro Z r z j k hj hk n hn a
    have hx : r z ∈ ((L.pull Φ).div L').U ((fun _ => j), k) := by
      refine ⟨?_, hk⟩
      show r z ∈ L.wchart (fun _ : PUnit => Φ) (fun _ => j)
      unfold LB.wchart
      simpa using hj
    have e := congrArg (r.stalkMap z).hom (hf ((fun _ => j), k) (r z) hx n hn a)
    rw [map_mul, map_pow] at e
    have e1 := stalkMap_gs r Φ z (ch L (fun _ => j)) (mem_ch.2 hj) ((θ n hn a).f (fun _ => j))
    have e2 := stalkMap_gs r (𝟙 X') z _ hx (f ((fun _ => j), k)).val
    have e3 := stalkMap_gs r (𝟙 X') z (ch L' (fun _ => k)) (mem_ch.2 hk) (a.f (fun _ => k))
    rw [Category.comp_id] at e2 e3
    erw [e1, e2, e3] at e
    rw [gs_unit r z _ hx] at e
    exact e

end GlobalTheory.SectionRingIso

/- English proof (translation)
Introduce `R _ X X' _ _ _ _ L L' _ _ θ _ hmul Φ hpair hcov`. Take `⟨w, hw, hval⟩` from `GlobalTheory.SectionRingIso.core (fun n hn => θ n hn) hmul Φ (fun n hn b => (hpair n hn b b).1) (fun n hn a b x j k hx hj hk => (hpair n hn a b).2 x j k hx hj hk) hcov`. Use `⟨w, hw, fun n hn a Z r z p q hp hq => ?_⟩` and prove the remaining obligations. Take `⟨p0, rfl⟩ : ∃ p0, p = fun _ => p0` from `⟨p 0, funext fun κ => by rw [Fin.fin_one_eq_zero κ]⟩`. Take `⟨q0, rfl⟩ : ∃ q0, q = fun _ => q0` from `⟨q 0, funext fun κ => by rw [Fin.fin_one_eq_zero κ]⟩`.

Establish `e` using `hval Z r z p0 q0 (hp 0) (hq 0) n hn a`. Simplify using `only [Fin.prod_univ_one, Category.comp_id, zpow_natCast, Units.val_pow_eq_pow_val]`. Conclude with `e`.
-/
theorem GlobalTheory.exists_iso_of_sectionRing : ∀ (R : Type) [CommRing R] (X X' : Over (Spec (CommRingCat.of R))) [CompactSpace X.left] [QuasiSeparatedSpace X.left] [CompactSpace X'.left] [QuasiSeparatedSpace X'.left] (L : LB X.left) (L' : LB X'.left), L.IsLB → L'.IsLB → ∀ θ : ∀ n : ℕ, 1 ≤ n → (H0 L' n ≃ H0 L n), (∀ (n : ℕ) (hn : 1 ≤ n) (c : R) (a b d : H0 L' n), (∀ j, d.f j = a.f j + resTop _ (scal X'.hom c) * b.f j) → ∀ j, (θ n hn d).f j = (θ n hn a).f j + resTop _ (scal X.hom c) * (θ n hn b).f j) → (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : H0 L' n) (b : H0 L' m) (d : H0 L' (n + m)), (∀ j : Fin 1 → L'.ι, (show Γ(X'.left, LB.wchart L' (fun _ : Fin 1 => 𝟙 X'.left) j) from d.f j) = (show Γ(X'.left, LB.wchart L' (fun _ : Fin 1 => 𝟙 X'.left) j) from a.f j) * (show Γ(X'.left, LB.wchart L' (fun _ : Fin 1 => 𝟙 X'.left) j) from b.f j)) → ∀ j : Fin 1 → L.ι, (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ (n + m) (hn.trans (Nat.le_add_right n m)) d).f j) = (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ n hn a).f j) * (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ m hm b).f j)) → ∀ Φ : X'.left ⟶ X.left, (∀ (n : ℕ) (hn : 1 ≤ n) (a b : H0 L' n), Φ ⁻¹ᵁ nonzeroLocus (θ n hn b) = nonzeroLocus b ∧ ∀ (x : X'.left) (j : Fin 1 → L.ι) (j' : Fin 1 → L'.ι), x ∈ nonzeroLocus b → Φ x ∈ L.U (j 0) → x ∈ L'.U (j' 0) → Geo.Tor.gs Φ x _ ((θ n hn a).f j) * Geo.Tor.gs (𝟙 X'.left) x _ (b.f j') = Geo.Tor.gs Φ x _ ((θ n hn b).f j) * Geo.Tor.gs (𝟙 X'.left) x _ (a.f j')) → (∀ x : X'.left, ∃ (n : ℕ) (_ : 1 ≤ n) (a : H0 L' n) (b : H0 L' (n + 1)), x ∈ nonzeroLocus a ∧ x ∈ nonzeroLocus b) → ∃ w : LB.Iso L' (L.pull Φ), w.IsGen ∧ ∀ (n : ℕ) (hn : 1 ≤ n) (a : H0 L' n), (∀ (Z : Scheme.{0}) (r : Z ⟶ X'.left) (z : Z) (p : Fin 1 → L.ι) (q : Fin 1 → L'.ι), (∀ κ, (Φ) ((fun _ : Fin 1 => 𝟙 X'.left) κ (r z)) ∈ L.U (p κ)) → (∀ κ, (fun _ : Fin 1 => 𝟙 X'.left) κ (r z) ∈ L'.U (q κ)) → Geo.Tor.gs (r ≫ Φ) z (LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) p) ((θ n hn a).f p) = (∏ κ, Geo.Tor.gw w (r ≫ (fun _ : Fin 1 => 𝟙 X'.left) κ) z (p κ) (q κ) ^ (fun _ : Fin 1 => (n : ℤ)) κ).val * Geo.Tor.gs r z (LB.wchart L' (fun _ : Fin 1 => 𝟙 X'.left) q) ((a).f q)) := by
  intro R _ X X' _ _ _ _ L L' _ _ θ _ hmul Φ hpair hcov
  obtain ⟨w, hw, hval⟩ := GlobalTheory.SectionRingIso.core (fun n hn => θ n hn) hmul Φ
    (fun n hn b => (hpair n hn b b).1) (fun n hn a b x j k hx hj hk => (hpair n hn a b).2 x j k hx hj hk) hcov
  refine ⟨w, hw, fun n hn a Z r z p q hp hq => ?_⟩
  obtain ⟨p0, rfl⟩ : ∃ p0, p = fun _ => p0 := ⟨p 0, funext fun κ => by rw [Fin.fin_one_eq_zero κ]⟩
  obtain ⟨q0, rfl⟩ : ∃ q0, q = fun _ => q0 := ⟨q 0, funext fun κ => by rw [Fin.fin_one_eq_zero κ]⟩
  have e := hval Z r z p0 q0 (hp 0) (hq 0) n hn a
  simp only [Fin.prod_univ_one, Category.comp_id, zpow_natCast, Units.val_pow_eq_pow_val]
  exact e
