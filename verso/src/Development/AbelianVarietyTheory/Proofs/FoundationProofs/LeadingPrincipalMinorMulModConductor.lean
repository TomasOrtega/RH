import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType Matrix

namespace GlobalTheory.PsType.MinorMul

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `u hu hle` and use `hx u hu (hle.trans h)`.
-/
theorem triv_of_val_le {χ : kˣ →* ℂˣ} {x y : k} (h : valuation k y ≤ valuation k x) (hx : Triv χ x) : Triv χ y :=
  fun u hu hle => hx u hu (hle.trans h)

/- English proof (translation)
Introduce `u _ hle`. Rewrite `hle` using `[map_zero, le_zero_iff, map_eq_zero, sub_eq_zero]`. Establish `: u = 1` using `Units.ext hle`. Simplify using `[this]`.
-/
theorem triv_zero (χ : kˣ →* ℂˣ) : Triv χ (0 : k) := by
  intro u _ hle
  rw [map_zero, le_zero_iff, map_eq_zero, sub_eq_zero] at hle
  have : u = 1 := Units.ext hle
  simp [this]

def trivIdeal (χ : kˣ →* ℂˣ) : Ideal 𝒪[k] where
  carrier := {x | Triv χ (x : k)}
  zero_mem' := triv_zero χ
  add_mem' {x y} hx hy := by
    show Triv χ ((x : k) + y)
    rcases le_max_iff.1 (Valuation.map_add (valuation k) (x : k) y) with h | h
    · exact triv_of_val_le h hx
    · exact triv_of_val_le h hy
  smul_mem' c x hx := by
    show Triv χ ((c : k) * x)
    refine triv_of_val_le ?_ hx
    rw [map_mul]
    exact mul_le_of_le_one_left' ((Valuation.mem_integer_iff _ _).1 c.2)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_trivIdeal {χ : kˣ →* ℂˣ} {x : 𝒪[k]} : x ∈ trivIdeal χ ↔ Triv χ (x : k) := Iff.rfl

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Take `⟨y, hy⟩` from `hx.exists_right_inv`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Establish `h1 : x * y - 1 ∈ I`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hy, map_one, sub_self]`.

Establish `hm : x * y ∈ IsLocalRing.maximalIdeal R` using `Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal x).2 hn)`. Establish `h2` using `(IsLocalRing.le_maximalIdeal hI) h1`. Establish `: (1 : R) ∈ IsLocalRing.maximalIdeal R`. Use `Ideal.sub_mem _ hm h2` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis.

Conclude with `(IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)`.
-/
theorem isUnit_of_isUnit_mk {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R} (hI : I ≠ ⊤) {x : R}
    (hx : IsUnit (Ideal.Quotient.mk I x)) : IsUnit x := by
  by_contra hn
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h1 : x * y - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hy, map_one, sub_self]
  have hm : x * y ∈ IsLocalRing.maximalIdeal R :=
    Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal x).2 hn)
  have h2 := (IsLocalRing.le_maximalIdeal hI) h1
  have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem _ hm h2
    rwa [sub_sub_cancel] at this
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)

/- English proof (translation)
Establish `h0 : (M.toBlock p fun i => ¬ p i) = 0`. Use extensionality with `i j`. Conclude with `h i i.2 j j.2`. Unfold `toSquareBlockProp`. Rewrite using `[toBlock_mul_eq_add p p p M N, h0, Matrix.zero_mul, add_zero]`.
-/
theorem toSquareBlockProp_mul {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (M N : Matrix ι ι R) (h : ∀ i, p i → ∀ j, ¬ p j → M i j = 0) :
    (M * N).toSquareBlockProp p = M.toSquareBlockProp p * N.toSquareBlockProp p := by
  have h0 : (M.toBlock p fun i => ¬ p i) = 0 := by
    ext i j; exact h i i.2 j j.2
  unfold toSquareBlockProp
  rw [toBlock_mul_eq_add p p p M N, h0, Matrix.zero_mul, add_zero]

/- English proof (translation)
Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem minor_map {n : ℕ} (u : GL (Fin n) 𝒪[k]) (m : Fin n) :
    minor (GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) m =
      algebraMap 𝒪[k] k ((u.val.toSquareBlockProp fun i => i ≤ m).det) := by
  rw [RingHom.map_det]; rfl

end GlobalTheory.PsType.MinorMul

open GlobalTheory.PsType.MinorMul in
/- English proof (translation)
Introduce `k _ _ _ _ n ψ hψ m hm`. Use `set χ := ψ m / nxt ψ m with hχ`. Use `set I := trivIdeal χ with hIdef`. Establish `hI : I ≠ ⊤`. Introduce `h`.

Establish `: (1 : 𝒪[k]) ∈ I` using `h ▸ Submodule.mem_top`. Conclude with `hm (by have h2 := (mem_trivIdeal (χ := χ) (x := 1)).1 this; simpa using h2)`. Establish `hent : ∀ a ∈ grp ψ, ∀ i j : Fin n, i ≤ m → ¬ j ≤ m → Triv χ (a.val i j)`. Introduce `a ha i j hi hj`. Establish `hj' : m < j` using `not_le.1 hj`.

Establish `hlt : (m : ℕ) + 1 < n` using `lt_of_le_of_lt (Nat.succ_le_of_lt (Fin.lt_def.1 hj')) j.2`. Establish `hnx : nxt ψ m = ψ ⟨(m : ℕ) + 1, hlt⟩` using `dif_pos hlt`. Establish `h1` using `ha.2 i j (lt_of_le_of_lt hi hj')`. Rewrite using `[hχ, hnx]`. Conclude with `hψ i m ⟨(m : ℕ) + 1, hlt⟩ j hi (Fin.le_def.2 (Nat.le_succ _)) (Fin.le_def.2 (Nat.succ_le_of_lt (Fin.lt_def.1 hj'))) _ h1`.

Establish `hzero : ∀ u : GL (Fin n) 𝒪[k], GeneralLinearGroup.map (algebraMap 𝒪[k] k) u ∈ grp ψ → ∀ i, i ≤ m → ∀ j, ¬ j ≤ m → (Ideal.Quotient.mk I).mapMatrix u.val i j = 0`. Introduce `u hu i hi j hj`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (hent _ hu i j hi hj)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `a ha`.

Take `⟨u, rfl⟩` from `ha.1`. Rewrite using `[minor_map]`. Use `(Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.1 ?_` and prove the remaining obligations. Use `isUnit_of_isUnit_mk hI ?_` and prove the remaining obligations. Establish `hdet : IsUnit ((Ideal.Quotient.mk I).mapMatrix u.val).det`.

Rewrite using `[← RingHom.map_det]`. Conclude with `(Matrix.isUnits_det_units u).map _`. Rewrite `hdet` using `[twoBlockTriangular_det' _ (fun i => i ≤ m) (hzero u ha)]`. Use `isUnit_of_mul_isUnit_left hdet` as an intermediate fact. Rewrite `this` using `[show (((Ideal.Quotient.mk I).mapMatrix u.val).toSquareBlockProp fun i => i ≤ m) = (Ideal.Quotient.mk I).mapMatrix (u.val.toSquareBlockProp fun i => i ≤ m) from rfl, ← RingHom.map_det]`. Then use the resulting hypothesis.

Introduce `a ha b hb`. Take `⟨u, rfl⟩` from `ha.1`. Take `⟨w, rfl⟩` from `hb.1`. Rewrite using `[← map_mul, minor_map, minor_map, minor_map, ← map_mul, ← map_sub]`. It suffices to establish `hs : (((u * w).val.toSquareBlockProp fun i => i ≤ m).det - (u.val.toSquareBlockProp fun i => i ≤ m).det * (w.val.toSquareBlockProp fun i => i ≤ m).det) ∈ I from hs`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, RingHom.map_det, RingHom.map_det, RingHom.map_det, sub_eq_zero, ← det_mul]`. Use `congr 1`. Rewrite using `[Units.val_mul]`. Use `show ((Ideal.Quotient.mk I).mapMatrix (u.val * w.val)).toSquareBlockProp (fun i => i ≤ m) = _`. Rewrite using `[map_mul, toSquareBlockProp_mul _ _ _ (hzero u ha)]`.

Both sides reduce to the same expression.
-/
theorem GlobalTheory.PsType.minor_mul_mod : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ m : Fin n, ¬ Triv (ψ m / nxt ψ m) 1 → (∀ a ∈ grp ψ, valuation k (minor a m) = 1) ∧ ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, Triv (ψ m / nxt ψ m) (minor (a * b) m - minor a m * minor b m) := by
  intro k _ _ _ _ n ψ hψ m hm
  set χ := ψ m / nxt ψ m with hχ
  set I := trivIdeal χ with hIdef
  have hI : I ≠ ⊤ := by
    intro h
    have : (1 : 𝒪[k]) ∈ I := h ▸ Submodule.mem_top
    exact hm (by have h2 := (mem_trivIdeal (χ := χ) (x := 1)).1 this; simpa using h2)

  have hent : ∀ a ∈ grp ψ, ∀ i j : Fin n, i ≤ m → ¬ j ≤ m → Triv χ (a.val i j) := by
    intro a ha i j hi hj
    have hj' : m < j := not_le.1 hj
    have hlt : (m : ℕ) + 1 < n := lt_of_le_of_lt (Nat.succ_le_of_lt (Fin.lt_def.1 hj')) j.2
    have hnx : nxt ψ m = ψ ⟨(m : ℕ) + 1, hlt⟩ := dif_pos hlt
    have h1 := ha.2 i j (lt_of_le_of_lt hi hj')
    rw [hχ, hnx]
    exact hψ i m ⟨(m : ℕ) + 1, hlt⟩ j hi (Fin.le_def.2 (Nat.le_succ _))
      (Fin.le_def.2 (Nat.succ_le_of_lt (Fin.lt_def.1 hj'))) _ h1

  have hzero : ∀ u : GL (Fin n) 𝒪[k], GeneralLinearGroup.map (algebraMap 𝒪[k] k) u ∈ grp ψ →
      ∀ i, i ≤ m → ∀ j, ¬ j ≤ m → (Ideal.Quotient.mk I).mapMatrix u.val i j = 0 := by
    intro u hu i hi j hj
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hent _ hu i j hi hj)
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨u, rfl⟩ := ha.1
    rw [minor_map]
    refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.1 ?_
    refine isUnit_of_isUnit_mk hI ?_
    have hdet : IsUnit ((Ideal.Quotient.mk I).mapMatrix u.val).det := by
      rw [← RingHom.map_det]
      exact (Matrix.isUnits_det_units u).map _
    rw [twoBlockTriangular_det' _ (fun i => i ≤ m) (hzero u ha)] at hdet
    have := isUnit_of_mul_isUnit_left hdet
    rwa [show (((Ideal.Quotient.mk I).mapMatrix u.val).toSquareBlockProp fun i => i ≤ m) =
      (Ideal.Quotient.mk I).mapMatrix (u.val.toSquareBlockProp fun i => i ≤ m) from rfl, ← RingHom.map_det] at this
  · intro a ha b hb
    obtain ⟨u, rfl⟩ := ha.1
    obtain ⟨w, rfl⟩ := hb.1
    rw [← map_mul, minor_map, minor_map, minor_map, ← map_mul, ← map_sub]
    suffices hs : (((u * w).val.toSquareBlockProp fun i => i ≤ m).det -
        (u.val.toSquareBlockProp fun i => i ≤ m).det * (w.val.toSquareBlockProp fun i => i ≤ m).det) ∈ I from hs
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, RingHom.map_det, RingHom.map_det, RingHom.map_det, sub_eq_zero,
      ← det_mul]
    congr 1
    rw [Units.val_mul]
    show ((Ideal.Quotient.mk I).mapMatrix (u.val * w.val)).toSquareBlockProp (fun i => i ≤ m) = _
    rw [map_mul, toSquareBlockProp_mul _ _ _ (hzero u ha)]
    rfl
