import Formalism.DoubleCosetMeasures.Statement

set_option maxHeartbeats 400000

noncomputable section

open Matrix

namespace Formalism.DoubleCosetMeasures.P

open Formalism.DoubleCosetMeasures

/- English proof (translation)
Introduce `K _ n x y`. Conclude with `⟨fun hx hy => isLowUni_mul K hx hy, fun hx hy => isUpUni_mul K hx hy, fun hx => ⟨isLowUni_inv K hx, isLowUni_det K hx⟩, fun hx => ⟨isUpUni_inv K hx, isUpUni_det K hx⟩⟩`.
-/
theorem uniGroup : Formalism.DoubleCosetMeasures.UniGroup := by
  intro K _ n x y
  exact ⟨fun hx hy => isLowUni_mul K hx hy, fun hx hy => isUpUni_mul K hx hy,
    fun hx => ⟨isLowUni_inv K hx, isLowUni_det K hx⟩,
    fun hx => ⟨isUpUni_inv K hx, isUpUni_det K hx⟩⟩

section Simple

variable {K : Type} [CommRing K] {n : ℕ}

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Fintype.sum_eq_add j ⟨j.val + 1, h⟩ (by intro e; simp [Fin.ext_iff] at e)]`. Rewrite using `[hy.2 j, hx.2 _]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `k ⟨hk1, hk2⟩`. Break down `lt_or_gt_of_ne hk1 with hlt | hgt` into its components or cases.

Establish `: y k j = 0` using `hy.1 (by simpa using hlt)`. Simplify using `[this]`. Establish `hlt : (⟨j.val + 1, h⟩ : Fin n) < k`. Rewrite `hgt`, the goal using `[Fin.lt_def]`. Establish `: k.val ≠ j.val + 1` using `fun e => hk2 (Fin.ext e)`.

Simplify using `only`. Use linear arithmetic over natural numbers and integers. Establish `: x ⟨j.val + 1, h⟩ k = 0` using `hx.1 (by simpa using hlt)`. Simplify using `[this]`.
-/
theorem low_simple_entry {x y : Matrix (Fin n) (Fin n) K} (hx : IsLowUni x) (hy : IsLowUni y)
    (j : Fin n) (h : j.val + 1 < n) :
    (x * y) ⟨j.val + 1, h⟩ j = x ⟨j.val + 1, h⟩ j + y ⟨j.val + 1, h⟩ j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_add j ⟨j.val + 1, h⟩
    (by intro e; simp [Fin.ext_iff] at e)]
  · rw [hy.2 j, hx.2 _]; ring
  · rintro k ⟨hk1, hk2⟩
    rcases lt_or_gt_of_ne hk1 with hlt | hgt
    · have : y k j = 0 := hy.1 (by simpa using hlt)
      simp [this]
    · have hlt : (⟨j.val + 1, h⟩ : Fin n) < k := by
        rw [Fin.lt_def] at hgt ⊢
        have : k.val ≠ j.val + 1 := fun e => hk2 (Fin.ext e)
        simp only
        omega
      have : x ⟨j.val + 1, h⟩ k = 0 := hx.1 (by simpa using hlt)
      simp [this]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Fintype.sum_eq_add j ⟨j.val + 1, h⟩ (by intro e; simp [Fin.ext_iff] at e)]`. Rewrite using `[hx.2 j, hy.2 _]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `k ⟨hk1, hk2⟩`. Break down `lt_or_gt_of_ne hk1 with hlt | hgt` into its components or cases.

Establish `: x j k = 0` using `hx.1 (by simpa using hlt)`. Simplify using `[this]`. Establish `hlt : (⟨j.val + 1, h⟩ : Fin n) < k`. Rewrite `hgt`, the goal using `[Fin.lt_def]`. Establish `: k.val ≠ j.val + 1` using `fun e => hk2 (Fin.ext e)`.

Simplify using `only`. Use linear arithmetic over natural numbers and integers. Establish `: y k ⟨j.val + 1, h⟩ = 0` using `hy.1 (by simpa using hlt)`. Simplify using `[this]`.
-/
theorem up_simple_entry {x y : Matrix (Fin n) (Fin n) K} (hx : IsUpUni x) (hy : IsUpUni y)
    (j : Fin n) (h : j.val + 1 < n) :
    (x * y) j ⟨j.val + 1, h⟩ = x j ⟨j.val + 1, h⟩ + y j ⟨j.val + 1, h⟩ := by
  rw [Matrix.mul_apply, Fintype.sum_eq_add j ⟨j.val + 1, h⟩
    (by intro e; simp [Fin.ext_iff] at e)]
  · rw [hx.2 j, hy.2 _]; ring
  · rintro k ⟨hk1, hk2⟩
    rcases lt_or_gt_of_ne hk1 with hlt | hgt
    · have : x j k = 0 := hx.1 (by simpa using hlt)
      simp [this]
    · have hlt : (⟨j.val + 1, h⟩ : Fin n) < k := by
        rw [Fin.lt_def] at hgt ⊢
        have : k.val ≠ j.val + 1 := fun e => hk2 (Fin.ext e)
        simp only
        omega
      have : y k ⟨j.val + 1, h⟩ = 0 := hy.1 (by simpa using hlt)
      simp [this]

end Simple

/- English proof (translation)
Introduce `K _ n x y`. Prove the components needed by the constructor for the conclusion. Introduce `hx hy`. Unfold `sLow`. Rewrite using `[← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : j.val + 1 < n`. Simplify using `only [dif_pos h]`. Apply the tactic sequence `exact low_simple_entry hx hy j h`. Simplify using `[dif_neg h]`.

Introduce `hx hy`. Unfold `sUp`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : j.val + 1 < n`.

Simplify using `only [dif_pos h]`. Apply the tactic sequence `exact up_simple_entry hx hy j h`. Simplify using `[dif_neg h]`.
-/
theorem simpleAdd : Formalism.DoubleCosetMeasures.SimpleAdd := by
  intro K _ n x y
  constructor
  · intro hx hy
    unfold sLow
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j.val + 1 < n
    · simp only [dif_pos h]; exact low_simple_entry hx hy j h
    · simp [dif_neg h]
  · intro hx hy
    unfold sUp
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j.val + 1 < n
    · simp only [dif_pos h]; exact up_simple_entry hx hy j h
    · simp [dif_neg h]

section Int

variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}

/- English proof (translation)
Introduce `a b`. Rewrite using `[Matrix.mul_apply]`. Conclude with `R.sum_mem fun k _ => R.mul_mem (hA a k) (hB k b)`.
-/
theorem isInt_mul {A B : Matrix (Fin n) (Fin n) K} (hA : IsInt R A) (hB : IsInt R B) :
    IsInt R (A * B) := by
  intro a b
  rw [Matrix.mul_apply]
  exact R.sum_mem fun k _ => R.mul_mem (hA a k) (hB k b)

/- English proof (translation)
Set `A' : Matrix (Fin n) (Fin n) R` to `fun a b => ⟨A a b, hA a b⟩`. Establish `hmap : R.subtype.mapMatrix A' = A` using `by ext a b; rfl`. Introduce `a b`. Rewrite using `[← hmap, ← RingHom.map_adjugate]`. Conclude with `(A'.adjugate a b).2`.
-/
theorem isInt_adjugate {A : Matrix (Fin n) (Fin n) K} (hA : IsInt R A) :
    IsInt R A.adjugate := by
  let A' : Matrix (Fin n) (Fin n) R := fun a b => ⟨A a b, hA a b⟩
  have hmap : R.subtype.mapMatrix A' = A := by ext a b; rfl
  intro a b
  rw [← hmap, ← RingHom.map_adjugate]
  exact (A'.adjugate a b).2

/- English proof (translation)
Rewrite using `[Matrix.inv_def, hd, Ring.inverse_one, one_smul]`. Conclude with `isInt_adjugate R hA`.
-/
theorem isInt_inv {A : Matrix (Fin n) (Fin n) K} (hA : IsInt R A) (hd : A.det = 1) :
    IsInt R A⁻¹ := by
  rw [Matrix.inv_def, hd, Ring.inverse_one, one_smul]
  exact isInt_adjugate R hA

end Int

/- English proof (translation)
Introduce `K _ R n a b Z ha hb haR hbR`. Establish `hda : IsUnit a.det` using `by simp [isLowUni_det K ha]`. Establish `hdb : IsUnit b.det` using `by simp [isUpUni_det K hb]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `hZ : Z = a⁻¹ * (a * Z * b) * b⁻¹`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv b hdb, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul a hda, Matrix.one_mul]`. Rewrite using `[hZ]`. Conclude with `isInt_mul R (isInt_mul R (isInt_inv R haR (isLowUni_det K ha)) h) (isInt_inv R hbR (isUpUni_det K hb))`. Introduce `h`.

Conclude with `isInt_mul R (isInt_mul R haR h) hbR`.
-/
theorem intInv : Formalism.DoubleCosetMeasures.IntInv := by
  intro K _ R n a b Z ha hb haR hbR
  have hda : IsUnit a.det := by simp [isLowUni_det K ha]
  have hdb : IsUnit b.det := by simp [isUpUni_det K hb]
  constructor
  · intro h
    have hZ : Z = a⁻¹ * (a * Z * b) * b⁻¹ := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv b hdb, Matrix.mul_one,
        ← Matrix.mul_assoc, Matrix.nonsing_inv_mul a hda, Matrix.one_mul]
    rw [hZ]
    exact isInt_mul R (isInt_mul R (isInt_inv R haR (isLowUni_det K ha)) h)
      (isInt_inv R hbR (isUpUni_det K hb))
  · intro h
    exact isInt_mul R (isInt_mul R haR h) hbR

section Lat

variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}

/- English proof (translation)
Unfold `latOf`. Simplify using `only [Submodule.mem_map, Submodule.mem_top, true_and]`. Both sides reduce to the same expression.
-/
theorem mem_latOf (g : GL (Fin n) K) (w : Fin n → K) :
    w ∈ latOf R g ↔ ∃ v : Fin n → R, (g : Matrix (Fin n) (Fin n) K) *ᵥ (fun j => (v j : K)) = w := by
  unfold latOf
  simp only [Submodule.mem_map, Submodule.mem_top, true_and]
  rfl

/- English proof (translation)
Introduce `w hw`. Take `⟨v, rfl⟩` from `(mem_latOf R h w).1 hw`. Rewrite using `[mem_latOf]`. Use `set M : Matrix (Fin n) (Fin n) K := ((g⁻¹ * h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hMdef`. Use `⟨fun i => ⟨(M *ᵥ (fun j => (v j : K))) i, ?_⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `R.sum_mem fun k _ => R.mul_mem (hM i k) (v k).2`. Establish `hgM : (g : Matrix (Fin n) (Fin n) K) * M = h`. Rewrite using `[hMdef, Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`. Express the relevant statement in the definitionally equal form `(g : Matrix (Fin n) (Fin n) K) *ᵥ (M *ᵥ (fun j => (v j : K))) = _`.

Rewrite using `[Matrix.mulVec_mulVec, hgM]`.
-/
theorem latOf_le (g h : GL (Fin n) K)
    (hM : IsInt R (((g⁻¹ * h : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)) :
    latOf R h ≤ latOf R g := by
  intro w hw
  obtain ⟨v, rfl⟩ := (mem_latOf R h w).1 hw
  rw [mem_latOf]
  set M : Matrix (Fin n) (Fin n) K := ((g⁻¹ * h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hMdef
  refine ⟨fun i => ⟨(M *ᵥ (fun j => (v j : K))) i, ?_⟩, ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact R.sum_mem fun k _ => R.mul_mem (hM i k) (v k).2
  · have hgM : (g : Matrix (Fin n) (Fin n) K) * M = h := by
      rw [hMdef, Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.one_mul]
    change (g : Matrix (Fin n) (Fin n) K) *ᵥ (M *ᵥ (fun j => (v j : K))) = _
    rw [Matrix.mulVec_mulVec, hgM]

/- English proof (translation)
Introduce `i j`. Establish `hmem : (h : Matrix (Fin n) (Fin n) K) *ᵥ (fun k => ((Pi.single j (1 : R) : Fin n → R) k : K)) ∈ latOf R h` using `(mem_latOf R h _).2 ⟨_, rfl⟩`. Take `⟨v, hv⟩` from `(mem_latOf R g _).1 (hle hmem)`. Establish `hcoe : (fun k => ((Pi.single j (1 : R) : Fin n → R) k : K)) = Pi.single j (1 : K)`. Use extensionality with `k`.

Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hk]`. Rewrite `hv` using `[hcoe]`.

Establish `key : (((g⁻¹ * h : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single j (1 : K) = fun k => (v k : K)`. Rewrite using `[Units.val_mul, ← Matrix.mulVec_mulVec, ← hv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Use `congrFun key i` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_single_one]`. Simplify using `only [Matrix.col_apply] at this`.

Rewrite using `[this]`. Conclude with `(v i).2`.
-/
theorem isInt_of_latOf_le (g h : GL (Fin n) K) (hle : latOf R h ≤ latOf R g) :
    IsInt R (((g⁻¹ * h : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) := by
  intro i j
  have hmem : (h : Matrix (Fin n) (Fin n) K) *ᵥ (fun k => ((Pi.single j (1 : R) : Fin n → R) k : K))
      ∈ latOf R h := (mem_latOf R h _).2 ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := (mem_latOf R g _).1 (hle hmem)
  have hcoe : (fun k => ((Pi.single j (1 : R) : Fin n → R) k : K)) = Pi.single j (1 : K) := by
    ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  rw [hcoe] at hv
  have key : (((g⁻¹ * h : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single j (1 : K) =
      fun k => (v k : K) := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hv, Matrix.mulVec_mulVec, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have := congrFun key i
  rw [Matrix.mulVec_single_one] at this
  simp only [Matrix.col_apply] at this
  rw [this]
  exact (v i).2

end Lat

/- English proof (translation)
Introduce `K _ R n g h`. Prove the components needed by the constructor for the conclusion. Introduce `e`. Conclude with `⟨isInt_of_latOf_le R g h (le_of_eq e.symm), isInt_of_latOf_le R h g (le_of_eq e)⟩`. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `le_antisymm (latOf_le R h g h2) (latOf_le R g h h1)`.
-/
theorem latticeCoset : Formalism.DoubleCosetMeasures.LatticeCoset := by
  intro K _ R n g h
  constructor
  · intro e
    exact ⟨isInt_of_latOf_le R g h (le_of_eq e.symm), isInt_of_latOf_le R h g (le_of_eq e)⟩
  · rintro ⟨h1, h2⟩
    exact le_antisymm (latOf_le R h g h2) (latOf_le R g h h1)

end Formalism.DoubleCosetMeasures.P
