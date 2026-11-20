import Mathlib

namespace GlobalTheory.UnipotentBorder

open Matrix

variable {O : Type} [CommRing O]

def IsUU {m : ℕ} (U : Matrix (Fin m) (Fin m) O) : Prop :=
  ∀ i j, (j < i → U i j = 0) ∧ (i = j → U i j = 1)

def IsLU {m : ℕ} (L : Matrix (Fin m) (Fin m) O) : Prop :=
  ∀ i j, (i < j → L i j = 0) ∧ (i = j → L i j = 1)

/- English proof (translation)
Rewrite using `[mul_apply]`. Simplify using `only [mul_diagonal]`.
-/
theorem udl_apply {m : ℕ} (U L : Matrix (Fin m) (Fin m) O) (d : Fin m → O) (i j : Fin m) :
    (U * diagonal d * L) i j = ∑ k, U i k * d k * L k j := by
  rw [mul_apply]
  simp only [mul_diagonal]

/- English proof (translation)
Simplify using `only [udl_apply]`. Rewrite using `[Finset.sum_eq_single (Fin.last n)]`. Rewrite using `[(hU _ _).2 rfl, one_mul]`. Introduce `k _ hk`. Rewrite using `[(hU (Fin.last n) k).1 (lt_of_le_of_ne (Fin.le_last k) hk), zero_mul, zero_mul]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem last_row {n : ℕ} {U L : Matrix (Fin (n+1)) (Fin (n+1)) O} (hU : IsUU U)
    (D : Fin (n+1) → Oˣ) (j : Fin (n+1)) :
    (U * diagonal (fun k => (D k : O)) * L) (Fin.last n) j
      = (D (Fin.last n) : O) * L (Fin.last n) j := by
  simp only [udl_apply]
  rw [Finset.sum_eq_single (Fin.last n)]
  · rw [(hU _ _).2 rfl, one_mul]
  · intro k _ hk
    rw [(hU (Fin.last n) k).1 (lt_of_le_of_ne (Fin.le_last k) hk), zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Simplify using `only [udl_apply]`. Rewrite using `[Finset.sum_eq_single (Fin.last n)]`. Rewrite using `[(hL _ _).2 rfl, mul_one]`. Introduce `k _ hk`. Rewrite using `[(hL k (Fin.last n)).1 (lt_of_le_of_ne (Fin.le_last k) hk), mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem last_col {n : ℕ} {U L : Matrix (Fin (n+1)) (Fin (n+1)) O} (hL : IsLU L)
    (D : Fin (n+1) → Oˣ) (i : Fin (n+1)) :
    (U * diagonal (fun k => (D k : O)) * L) i (Fin.last n)
      = U i (Fin.last n) * (D (Fin.last n) : O) := by
  simp only [udl_apply]
  rw [Finset.sum_eq_single (Fin.last n)]
  · rw [(hL _ _).2 rfl, mul_one]
  · intro k _ hk
    rw [(hL k (Fin.last n)).1 (lt_of_le_of_ne (Fin.le_last k) hk), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Simplify using `only [udl_apply, Fin.sum_univ_castSucc, submatrix_apply]`.
-/
theorem top_block {n : ℕ} (U L : Matrix (Fin (n+1)) (Fin (n+1)) O)
    (D : Fin (n+1) → Oˣ) (i j : Fin n) :
    (U * diagonal (fun k => (D k : O)) * L) i.castSucc j.castSucc =
      (U.submatrix Fin.castSucc Fin.castSucc * diagonal (fun k : Fin n => (D k.castSucc : O)) *
        L.submatrix Fin.castSucc Fin.castSucc) i j
      + U i.castSucc (Fin.last n) * (D (Fin.last n) : O) * L (Fin.last n) j.castSucc := by
  simp only [udl_apply, Fin.sum_univ_castSucc, submatrix_apply]

/- English proof (translation)
The claim follows from `fun _ _ ↦ ⟨fun h ↦ (hU _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h), fun h ↦ (hU _ _).2 (congrArg _ h)⟩`.
-/
theorem IsUU.top {n : ℕ} {U : Matrix (Fin (n+1)) (Fin (n+1)) O} (hU : IsUU U) :
    IsUU (U.submatrix Fin.castSucc Fin.castSucc) := fun _ _ ↦
  ⟨fun h ↦ (hU _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h), fun h ↦ (hU _ _).2 (congrArg _ h)⟩

/- English proof (translation)
The claim follows from `fun _ _ ↦ ⟨fun h ↦ (hL _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h), fun h ↦ (hL _ _).2 (congrArg _ h)⟩`.
-/
theorem IsLU.top {n : ℕ} {L : Matrix (Fin (n+1)) (Fin (n+1)) O} (hL : IsLU L) :
    IsLU (L.submatrix Fin.castSucc Fin.castSucc) := fun _ _ ↦
  ⟨fun h ↦ (hL _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h), fun h ↦ (hL _ _).2 (congrArg _ h)⟩

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `U U' L L' D D' _ _ _ _ _`. Conclude with `⟨Matrix.ext fun i _ ↦ i.elim0, funext fun i ↦ i.elim0, Matrix.ext fun i _ ↦ i.elim0⟩`.

Consider the case `succ n ih`. Introduce `U U' L L' D D' hU hU' hL hL' h`. Establish `hrow : ∀ j, (D (Fin.last n) : O) * L (Fin.last n) j = (D' (Fin.last n) : O) * L' (Fin.last n) j` using `fun j ↦ (last_row hU D (L := L) j).symm.trans ((congrFun (congrFun h _) j).trans (last_row hU' D' (L := L') j))`. Establish `hcol : ∀ i, U i (Fin.last n) * (D (Fin.last n) : O) = U' i (Fin.last n) * (D' (Fin.last n) : O)` using `fun i ↦ (last_col hL D (U := U) i).symm.trans ((congrFun (congrFun h i) _).trans (last_col hL' D' (U := U') i))`. Establish `hDl : D (Fin.last n) = D' (Fin.last n)`.

Establish `e` using `hrow (Fin.last n)`. Rewrite `e` using `[(hL _ _).2 rfl, (hL' _ _).2 rfl, mul_one, mul_one]`. Conclude with `Units.ext e`. Establish `hLl : ∀ j, L (Fin.last n) j = L' (Fin.last n) j` using `fun j ↦ by`. Establish `e` using `hrow j`.

Rewrite `e` using `[hDl]`. Conclude with `(Units.mul_right_inj (D' (Fin.last n))).1 e`. Establish `hUl : ∀ i, U i (Fin.last n) = U' i (Fin.last n)` using `fun i ↦ by`. Establish `e` using `hcol i`. Rewrite `e` using `[hDl]`.

Conclude with `(Units.mul_left_inj (D' (Fin.last n))).1 e`. Establish `htop : U.submatrix Fin.castSucc Fin.castSucc * diagonal (fun k : Fin n ↦ ((D ∘ Fin.castSucc) k : O)) * L.submatrix Fin.castSucc Fin.castSucc = U'.submatrix Fin.castSucc Fin.castSucc * diagonal (fun k : Fin n ↦ ((D' ∘ Fin.castSucc) k : O)) * L'.submatrix Fin.castSucc Fin.castSucc`. Use extensionality with `i j`. Establish `e1` using `top_block U L D i j`. Establish `e2` using `top_block U' L' D' i j`.

Rewrite `e1` using `[h, e2, hUl, hDl, hLl]`. Conclude with `(add_right_cancel e1).symm`. Take `⟨hU0, hD0, hL0⟩` from `ih _ _ _ _ (D ∘ Fin.castSucc) (D' ∘ Fin.castSucc) hU.top hU'.top hL.top hL'.top htop`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Break down `Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl` into its components or cases. Break down `Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl` into its components or cases. Conclude with `congrFun (congrFun hU0 i) j`. Conclude with `hUl _`. Break down `Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl` into its components or cases.

Rewrite using `[(hU _ _).1 (Fin.castSucc_lt_last j), (hU' _ _).1 (Fin.castSucc_lt_last j)]`. Rewrite using `[(hU _ _).2 rfl, (hU' _ _).2 rfl]`. Use function extensionality and compare the values at `k`. Break down `Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl` into its components or cases. Conclude with `congrFun hD0 k`.

Conclude with `hDl`. Use extensionality with `i j`. Break down `Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl` into its components or cases. Break down `Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl` into its components or cases. Conclude with `congrFun (congrFun hL0 i) j`.

Rewrite using `[(hL _ _).1 (Fin.castSucc_lt_last i), (hL' _ _).1 (Fin.castSucc_lt_last i)]`. Conclude with `hLl j`.
-/
theorem udl_unique : ∀ (n : ℕ) (U U' L L' : Matrix (Fin n) (Fin n) O) (D D' : Fin n → Oˣ),
    IsUU U → IsUU U' → IsLU L → IsLU L' →
    U * diagonal (fun i => (D i : O)) * L = U' * diagonal (fun i => (D' i : O)) * L' →
    U = U' ∧ D = D' ∧ L = L' := by
  intro n
  induction n with
  | zero =>
    intro U U' L L' D D' _ _ _ _ _
    exact ⟨Matrix.ext fun i _ ↦ i.elim0, funext fun i ↦ i.elim0, Matrix.ext fun i _ ↦ i.elim0⟩
  | succ n ih =>
    intro U U' L L' D D' hU hU' hL hL' h

    have hrow : ∀ j, (D (Fin.last n) : O) * L (Fin.last n) j = (D' (Fin.last n) : O) * L' (Fin.last n) j :=
      fun j ↦ (last_row hU D (L := L) j).symm.trans
        ((congrFun (congrFun h _) j).trans (last_row hU' D' (L := L') j))
    have hcol : ∀ i, U i (Fin.last n) * (D (Fin.last n) : O) = U' i (Fin.last n) * (D' (Fin.last n) : O) :=
      fun i ↦ (last_col hL D (U := U) i).symm.trans
        ((congrFun (congrFun h i) _).trans (last_col hL' D' (U := U') i))
    have hDl : D (Fin.last n) = D' (Fin.last n) := by
      have e := hrow (Fin.last n)
      rw [(hL _ _).2 rfl, (hL' _ _).2 rfl, mul_one, mul_one] at e
      exact Units.ext e
    have hLl : ∀ j, L (Fin.last n) j = L' (Fin.last n) j := fun j ↦ by
      have e := hrow j
      rw [hDl] at e
      exact (Units.mul_right_inj (D' (Fin.last n))).1 e
    have hUl : ∀ i, U i (Fin.last n) = U' i (Fin.last n) := fun i ↦ by
      have e := hcol i
      rw [hDl] at e
      exact (Units.mul_left_inj (D' (Fin.last n))).1 e

    have htop : U.submatrix Fin.castSucc Fin.castSucc * diagonal (fun k : Fin n ↦ ((D ∘ Fin.castSucc) k : O)) *
        L.submatrix Fin.castSucc Fin.castSucc =
        U'.submatrix Fin.castSucc Fin.castSucc * diagonal (fun k : Fin n ↦ ((D' ∘ Fin.castSucc) k : O)) *
        L'.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      have e1 := top_block U L D i j
      have e2 := top_block U' L' D' i j
      rw [h, e2, hUl, hDl, hLl] at e1
      exact (add_right_cancel e1).symm
    obtain ⟨hU0, hD0, hL0⟩ := ih _ _ _ _ (D ∘ Fin.castSucc) (D' ∘ Fin.castSucc)
      hU.top hU'.top hL.top hL'.top htop
    refine ⟨?_, ?_, ?_⟩
    · ext i j
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · exact congrFun (congrFun hU0 i) j
        · exact hUl _
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · rw [(hU _ _).1 (Fin.castSucc_lt_last j), (hU' _ _).1 (Fin.castSucc_lt_last j)]
        · rw [(hU _ _).2 rfl, (hU' _ _).2 rfl]
    · funext k
      rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
      · exact congrFun hD0 k
      · exact hDl
    · ext i j
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · exact congrFun (congrFun hL0 i) j
        · rw [(hL _ _).1 (Fin.castSucc_lt_last i), (hL' _ _).1 (Fin.castSucc_lt_last i)]
      · exact hLl j

def border {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (col row : Fin n → O) (x : O) :
    Matrix (Fin (n+1)) (Fin (n+1)) O := fun i j =>
  Fin.lastCases (motive := fun _ => O) (Fin.lastCases (motive := fun _ => O) x row j)
    (fun i' => Fin.lastCases (motive := fun _ => O) (col i') (A i') j) i

section
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (col row : Fin n → O) (x : O)
omit [CommRing O]

/- English proof (translation)
Simplify using `[border]`.
-/
theorem border_ll : border A col row x (Fin.last n) (Fin.last n) = x := by simp [border]
/- English proof (translation)
Simplify using `[border]`.
-/
theorem border_lc (j : Fin n) : border A col row x (Fin.last n) j.castSucc = row j := by simp [border]
/- English proof (translation)
Simplify using `[border]`.
-/
theorem border_cl (i : Fin n) : border A col row x i.castSucc (Fin.last n) = col i := by simp [border]
/- English proof (translation)
Simplify using `[border]`.
-/
theorem border_cc (i j : Fin n) : border A col row x i.castSucc j.castSucc = A i j := by simp [border]
/- English proof (translation)
The claim follows from `Matrix.ext fun i j ↦ border_cc A col row x i j`.
-/
theorem border_top : (border A col row x).submatrix Fin.castSucc Fin.castSucc = A :=
  Matrix.ext fun i j ↦ border_cc A col row x i j
end

/- English proof (translation)
Establish `hm : z * y ∈ IsLocalRing.maximalIdeal O`. Take `⟨t, rfl⟩` from `hy`. Conclude with `Ideal.mul_mem_left _ z (Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hβ)))`. Assume the negation of the conclusion as `h`. Establish `h2 : a - z * y ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 h)`.

Establish `h3 : a ∈ IsLocalRing.maximalIdeal O` using `by simpa using Ideal.add_mem _ h2 hm`. Conclude with `mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 h3) ha`.
-/
theorem unit_sub [IsLocalRing O] {β : O} (hβ : ¬IsUnit β) {a y : O} (ha : IsUnit a)
    (hy : β ∣ y) (z : O) : IsUnit (a - z * y) := by
  have hm : z * y ∈ IsLocalRing.maximalIdeal O := by
    obtain ⟨t, rfl⟩ := hy
    exact Ideal.mul_mem_left _ z
      (Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hβ)))
  by_contra h
  have h2 : a - z * y ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 h)
  have h3 : a ∈ IsLocalRing.maximalIdeal O := by simpa using Ideal.add_mem _ h2 hm
  exact mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 h3) ha

/- English proof (translation)
Establish `hres : ∀ x : O, IsLocalRing.residue O x = 0 ↔ ¬IsUnit x` using `fun x ↦ by`. Rewrite using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Establish `htri : (g.map (IsLocalRing.residue O)).BlockTriangular id`. Introduce `a b hab`. Simplify using `only [map_apply]`.

Take `⟨t, ht⟩` from `hlow a b hab`. Rewrite using `[hres, ht]`. Conclude with `fun hu ↦ hβ (isUnit_of_mul_isUnit_left hu)`. Establish `hmap : IsLocalRing.residue O g.det = (g.map (IsLocalRing.residue O)).det` using `RingHom.map_det _ _`. Establish `hdet : (g.map (IsLocalRing.residue O)).det ≠ 0`.

Rewrite using `[← hmap]`. Conclude with `(hg.map _).ne_zero`. Rewrite `hdet` using `[det_of_upperTriangular htri, Finset.prod_ne_zero_iff]`. Establish `hi` using `hdet i (Finset.mem_univ _)`. Simplify using `only [map_apply] at hi`.

Assume the negation of the conclusion as `hu`. Conclude with `hi ((hres _).2 hu)`.
-/
theorem diag_unit [IsLocalRing O] {β : O} (hβ : ¬IsUnit β) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) O) (hg : IsUnit g.det) (hlow : ∀ i j, j < i → β ∣ g i j)
    (i : Fin n) : IsUnit (g i i) := by

  have hres : ∀ x : O, IsLocalRing.residue O x = 0 ↔ ¬IsUnit x := fun x ↦ by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have htri : (g.map (IsLocalRing.residue O)).BlockTriangular id := by
    intro a b hab
    simp only [map_apply]
    obtain ⟨t, ht⟩ := hlow a b hab
    rw [hres, ht]
    exact fun hu ↦ hβ (isUnit_of_mul_isUnit_left hu)
  have hmap : IsLocalRing.residue O g.det = (g.map (IsLocalRing.residue O)).det :=
    RingHom.map_det _ _
  have hdet : (g.map (IsLocalRing.residue O)).det ≠ 0 := by
    rw [← hmap]
    exact (hg.map _).ne_zero
  rw [det_of_upperTriangular htri, Finset.prod_ne_zero_iff] at hdet
  have hi := hdet i (Finset.mem_univ _)
  simp only [map_apply] at hi
  by_contra hu
  exact hi ((hres _).2 hu)

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `g _ _`. Conclude with `⟨0, fun i ↦ i.elim0, 0, fun i ↦ i.elim0, fun i ↦ i.elim0, Matrix.ext fun i _ ↦ i.elim0⟩`.

Consider the case `succ n ih`. Introduce `g hg hd`. Take `⟨u, hu⟩` from `hd (Fin.last n)`. Establish `hui : (↑u⁻¹ : O) * ↑u = 1` using `Units.inv_mul u`. Set `g' : Matrix (Fin n) (Fin n) O` to `fun i j ↦ g i.castSucc j.castSucc - (g i.castSucc (Fin.last n) * ↑u⁻¹) * g (Fin.last n) j.castSucc`.

Establish `hg' : ∀ i j, (i < j → α ∣ g' i j) ∧ (j < i → β ∣ g' i j)`. Introduce `i j`. Use `⟨fun h ↦ ?_, fun h ↦ ?_⟩` and prove the remaining obligations. Conclude with `dvd_sub ((hg _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h)) (Dvd.dvd.mul_right (Dvd.dvd.mul_right ((hg _ _).1 (Fin.castSucc_lt_last i)) _) _)`. Conclude with `dvd_sub ((hg _ _).2 (Fin.castSucc_lt_castSucc_iff.2 h)) (Dvd.dvd.mul_left ((hg _ _).2 (Fin.castSucc_lt_last j)) _)`.

Establish `hd' : ∀ i, IsUnit (g' i i)` using `fun i ↦ unit_sub hβ (hd i.castSucc) ((hg _ _).2 (Fin.castSucc_lt_last i)) _`. Take `⟨U0, D0, L0, hU0, hL0, hg0⟩` from `ih g' hg' hd'`. Set `U` to `border U0 (fun i ↦ g i.castSucc (Fin.last n) * ↑u⁻¹) 0 1`. Set `L` to `border L0 0 (fun j ↦ ↑u⁻¹ * g (Fin.last n) j.castSucc) 1`. Set `D : Fin (n + 1) → Oˣ` to `Fin.lastCases u D0`.

Establish `hU : ∀ i j, (j < i → U i j = 0) ∧ (i = j → U i j = 1) ∧ (i < j → α ∣ U i j)`. Introduce `i j`. Break down `Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl` into its components or cases. Break down `Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl` into its components or cases. Simplify using `only [U, border_cc, Fin.castSucc_lt_castSucc_iff, Fin.castSucc_inj]`.

Conclude with `hU0 i j`. Simplify using `only [U, border_cl]`. Conclude with `⟨fun h ↦ absurd h (not_lt.2 (Fin.castSucc_lt_last i).le), fun h ↦ absurd h (Fin.castSucc_lt_last i).ne, fun _ ↦ Dvd.dvd.mul_right ((hg _ _).1 (Fin.castSucc_lt_last i)) _⟩`. Break down `Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl` into its components or cases. Simplify using `only [U, border_lc, Pi.zero_apply]`.

Conclude with `⟨fun _ ↦ trivial, fun h ↦ absurd h (Fin.castSucc_lt_last j).ne', fun h ↦ absurd h (not_lt.2 (Fin.castSucc_lt_last j).le)⟩`. Simplify using `[U, border_ll]`. Establish `hL : ∀ i j, (i < j → L i j = 0) ∧ (i = j → L i j = 1) ∧ (j < i → β ∣ L i j)`. Introduce `i j`. Break down `Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl` into its components or cases.

Break down `Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl` into its components or cases. Simplify using `only [L, border_cc, Fin.castSucc_lt_castSucc_iff, Fin.castSucc_inj]`. Conclude with `hL0 i j`. Simplify using `only [L, border_cl, Pi.zero_apply]`. Conclude with `⟨fun _ ↦ trivial, fun h ↦ absurd h (Fin.castSucc_lt_last i).ne, fun h ↦ absurd h (not_lt.2 (Fin.castSucc_lt_last i).le)⟩`.

Break down `Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl` into its components or cases. Simplify using `only [L, border_lc]`. Conclude with `⟨fun h ↦ absurd h (not_lt.2 (Fin.castSucc_lt_last j).le), fun h ↦ absurd h (Fin.castSucc_lt_last j).ne', fun _ ↦ Dvd.dvd.mul_left ((hg _ _).2 (Fin.castSucc_lt_last j)) _⟩`. Simplify using `[L, border_ll]`. Establish `hUU : IsUU U` using `fun i j ↦ ⟨(hU i j).1, (hU i j).2.1⟩`.

Establish `hLU : IsLU L` using `fun i j ↦ ⟨(hL i j).1, (hL i j).2.1⟩`. Use `⟨U, D, L, hU, hL, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Break down `Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl` into its components or cases. Break down `Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl` into its components or cases.

Rewrite using `[top_block]`. Simplify using `only [U, L, D, border_top, Fin.lastCases_castSucc, Fin.lastCases_last, border_cl, border_lc]`. Rewrite using `[← hg0]`. Simplify using `only [g']`. Take the linear combination `(-(g i.castSucc (Fin.last n) * ↑u⁻¹ * g (Fin.last n) j.castSucc)) * hui`.

Rewrite using `[last_col hLU]`. Simplify using `only [U, D, border_cl, Fin.lastCases_last]`. Take the linear combination `(-(g i.castSucc (Fin.last n))) * hui`. Rewrite using `[last_row hUU]`. Break down `Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl` into its components or cases.

Simplify using `only [L, D, border_lc, Fin.lastCases_last]`. Rewrite using `[← mul_assoc, Units.mul_inv, one_mul]`. Simplify using `only [L, D, border_ll, Fin.lastCases_last, mul_one]`. Conclude with `hu.symm`.
-/
theorem udl_exists [IsLocalRing O] {α β : O} (hβ : ¬IsUnit β) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O),
    (∀ i j, (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)) → (∀ i, IsUnit (g i i)) →
    ∃ (U : Matrix (Fin n) (Fin n) O) (D : Fin n → Oˣ) (L : Matrix (Fin n) (Fin n) O),
      (∀ i j, (j < i → U i j = 0) ∧ (i = j → U i j = 1) ∧ (i < j → α ∣ U i j)) ∧
      (∀ i j, (i < j → L i j = 0) ∧ (i = j → L i j = 1) ∧ (j < i → β ∣ L i j)) ∧
      g = U * diagonal (fun i => (D i : O)) * L := by
  intro n
  induction n with
  | zero =>
    intro g _ _
    exact ⟨0, fun i ↦ i.elim0, 0, fun i ↦ i.elim0, fun i ↦ i.elim0, Matrix.ext fun i _ ↦ i.elim0⟩
  | succ n ih =>
    intro g hg hd
    obtain ⟨u, hu⟩ := hd (Fin.last n)
    have hui : (↑u⁻¹ : O) * ↑u = 1 := Units.inv_mul u

    let g' : Matrix (Fin n) (Fin n) O := fun i j ↦
      g i.castSucc j.castSucc - (g i.castSucc (Fin.last n) * ↑u⁻¹) * g (Fin.last n) j.castSucc
    have hg' : ∀ i j, (i < j → α ∣ g' i j) ∧ (j < i → β ∣ g' i j) := by
      intro i j
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · exact dvd_sub ((hg _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h))
          (Dvd.dvd.mul_right (Dvd.dvd.mul_right ((hg _ _).1 (Fin.castSucc_lt_last i)) _) _)
      · exact dvd_sub ((hg _ _).2 (Fin.castSucc_lt_castSucc_iff.2 h))
          (Dvd.dvd.mul_left ((hg _ _).2 (Fin.castSucc_lt_last j)) _)
    have hd' : ∀ i, IsUnit (g' i i) := fun i ↦
      unit_sub hβ (hd i.castSucc) ((hg _ _).2 (Fin.castSucc_lt_last i)) _
    obtain ⟨U0, D0, L0, hU0, hL0, hg0⟩ := ih g' hg' hd'
    let U := border U0 (fun i ↦ g i.castSucc (Fin.last n) * ↑u⁻¹) 0 1
    let L := border L0 0 (fun j ↦ ↑u⁻¹ * g (Fin.last n) j.castSucc) 1
    let D : Fin (n + 1) → Oˣ := Fin.lastCases u D0
    have hU : ∀ i j, (j < i → U i j = 0) ∧ (i = j → U i j = 1) ∧ (i < j → α ∣ U i j) := by
      intro i j
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · simp only [U, border_cc, Fin.castSucc_lt_castSucc_iff, Fin.castSucc_inj]
          exact hU0 i j
        · simp only [U, border_cl]
          exact ⟨fun h ↦ absurd h (not_lt.2 (Fin.castSucc_lt_last i).le),
            fun h ↦ absurd h (Fin.castSucc_lt_last i).ne,
            fun _ ↦ Dvd.dvd.mul_right ((hg _ _).1 (Fin.castSucc_lt_last i)) _⟩
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · simp only [U, border_lc, Pi.zero_apply]
          exact ⟨fun _ ↦ trivial, fun h ↦ absurd h (Fin.castSucc_lt_last j).ne',
            fun h ↦ absurd h (not_lt.2 (Fin.castSucc_lt_last j).le)⟩
        · simp [U, border_ll]
    have hL : ∀ i j, (i < j → L i j = 0) ∧ (i = j → L i j = 1) ∧ (j < i → β ∣ L i j) := by
      intro i j
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · simp only [L, border_cc, Fin.castSucc_lt_castSucc_iff, Fin.castSucc_inj]
          exact hL0 i j
        · simp only [L, border_cl, Pi.zero_apply]
          exact ⟨fun _ ↦ trivial, fun h ↦ absurd h (Fin.castSucc_lt_last i).ne,
            fun h ↦ absurd h (not_lt.2 (Fin.castSucc_lt_last i).le)⟩
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
        · simp only [L, border_lc]
          exact ⟨fun h ↦ absurd h (not_lt.2 (Fin.castSucc_lt_last j).le),
            fun h ↦ absurd h (Fin.castSucc_lt_last j).ne',
            fun _ ↦ Dvd.dvd.mul_left ((hg _ _).2 (Fin.castSucc_lt_last j)) _⟩
        · simp [L, border_ll]
    have hUU : IsUU U := fun i j ↦ ⟨(hU i j).1, (hU i j).2.1⟩
    have hLU : IsLU L := fun i j ↦ ⟨(hL i j).1, (hL i j).2.1⟩
    refine ⟨U, D, L, hU, hL, ?_⟩
    ext i j
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · rw [top_block]
        simp only [U, L, D, border_top, Fin.lastCases_castSucc, Fin.lastCases_last, border_cl, border_lc]
        rw [← hg0]
        simp only [g']
        linear_combination (-(g i.castSucc (Fin.last n) * ↑u⁻¹ * g (Fin.last n) j.castSucc)) * hui
      · rw [last_col hLU]
        simp only [U, D, border_cl, Fin.lastCases_last]
        linear_combination (-(g i.castSucc (Fin.last n))) * hui
    · rw [last_row hUU]
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · simp only [L, D, border_lc, Fin.lastCases_last]
        rw [← mul_assoc, Units.mul_inv, one_mul]
      · simp only [L, D, border_ll, Fin.lastCases_last, mul_one]
        exact hu.symm

/- English proof (translation)
Simplify using `only`. Introduce `O _ n _ α β hβ g hg`. Take `⟨U, D, L, hU, hL, hgeq⟩` from `udl_exists hβ n (↑g : Matrix (Fin n) (Fin n) O) hg (fun i ↦ diag_unit hβ (↑g : Matrix (Fin n) (Fin n) O) (Matrix.isUnits_det_units g) (fun i j h ↦ (hg i j).2 h) i)`. Use `⟨(U, D, L), ⟨hU, hL, hgeq⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨U', D', L'⟩ ⟨hU', hL', hg'⟩`.

Take `⟨h1, h2, h3⟩` from `udl_unique n U' U L' L D' D (fun i j ↦ ⟨(hU' i j).1, (hU' i j).2.1⟩) (fun i j ↦ ⟨(hU i j).1, (hU i j).2.1⟩) (fun i j ↦ ⟨(hL' i j).1, (hL' i j).2.1⟩) (fun i j ↦ ⟨(hL i j).1, (hL i j).2.1⟩) (hg'.symm.trans hgeq)`. Rewrite using `[h1, h2, h3]`.
-/
theorem iwahori_factorisation : (let d1 : {O : Type} → [CommRing O] → {n : ℕ} → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (β : O) (l : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (i < j → l i j = (0 : O)) ∧ (i = j → l i j = (1 : O)) ∧ (j < i → β ∣ l i j)); let d2 : {O : Type} → [CommRing O] → {n : ℕ} → O → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (α β : O) (g : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)); let d3 : {O : Type} → [CommRing O] → {n : ℕ} → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (α : O) (u : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (j < i → u i j = (0 : O)) ∧ (i = j → u i j = (1 : O)) ∧ (i < j → α ∣ u i j)); ∀ {O : Type} [inst : CommRing O] {n : ℕ} [IsLocalRing O] {α β : O}, ¬IsUnit β → ∀ (g : GL (Fin n) O), d2 α β (↑g : Matrix (Fin n) (Fin n) O) → ∃! p : Matrix (Fin n) (Fin n) O × (Fin n → Oˣ) × Matrix (Fin n) (Fin n) O, d3 α (Prod.fst p) ∧ d1 β (Prod.snd (Prod.snd p)) ∧ (↑g : Matrix (Fin n) (Fin n) O) = (Prod.fst p * Matrix.diagonal fun (i : Fin n) ↦ (↑(Prod.fst (Prod.snd p) i) : O)) * Prod.snd (Prod.snd p)) := by
  dsimp only
  intro O _ n _ α β hβ g hg
  obtain ⟨U, D, L, hU, hL, hgeq⟩ := udl_exists hβ n (↑g : Matrix (Fin n) (Fin n) O) hg
    (fun i ↦ diag_unit hβ (↑g : Matrix (Fin n) (Fin n) O) (Matrix.isUnits_det_units g)
      (fun i j h ↦ (hg i j).2 h) i)
  refine ⟨(U, D, L), ⟨hU, hL, hgeq⟩, ?_⟩
  rintro ⟨U', D', L'⟩ ⟨hU', hL', hg'⟩
  obtain ⟨h1, h2, h3⟩ := udl_unique n U' U L' L D' D
    (fun i j ↦ ⟨(hU' i j).1, (hU' i j).2.1⟩) (fun i j ↦ ⟨(hU i j).1, (hU i j).2.1⟩)
    (fun i j ↦ ⟨(hL' i j).1, (hL' i j).2.1⟩) (fun i j ↦ ⟨(hL i j).1, (hL i j).2.1⟩)
    (hg'.symm.trans hgeq)
  rw [h1, h2, h3]

end GlobalTheory.UnipotentBorder
