import Development.WeilBound.CoreStatements.HodgeTatePoints.RaCpaf
import ReciprocityTheory.DualLattices.CotangentSurjective
import ReciprocityTheory.DualLattices.SumValCoord
import ReciprocityTheory.DualLattices.ProdDvdOfIso
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes

noncomputable section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Ra

section Count

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

/- English proof (translation)
Establish `h : (fun x => (B' * V.map (algebraMap R C)) x j) = ∑ α, V α j • (fun x => B' x α)`. Use extensionality with `x`. Simplify using `[Matrix.mul_apply, Finset.sum_apply, Algebra.smul_def, mul_comm]`. Rewrite using `[h]`. Conclude with `Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)`.
-/
lemma monomialCount_col_mem_span {X : Type} [Fintype X] (B' : Matrix X X C) (V : Matrix X X R)
    (j : X) :
    (fun x => (B' * V.map (algebraMap R C)) x j) ∈
      Submodule.span R (Set.range fun α x => B' x α) := by
  have h : (fun x => (B' * V.map (algebraMap R C)) x j) = ∑ α, V α j • (fun x => B' x α) := by
    ext x
    simp [Matrix.mul_apply, Finset.sum_apply, Algebra.smul_def, mul_comm]
  rw [h]
  exact Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

/- English proof (translation)
Use `choose c hc using fun α => (Submodule.mem_span_range_iff_exists_fun R).1 (h α)`. Use `⟨fun i α => c α i, ?_⟩` and prove the remaining obligations. Use extensionality with `x α`. Use `congrFun (hc α) x` as an intermediate fact. Rewrite `this` using `[Finset.sum_apply]`.

Simplify using `only [Pi.smul_apply, Algebra.smul_def] at this`. Rewrite using `[← this, Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`.
-/
lemma monomialCount_exists_factor {X : Type} [Fintype X] (B B' : Matrix X X C)
    (h : ∀ α, (fun x => B' x α) ∈ Submodule.span R (Set.range fun j x => B x j)) :
    ∃ W : Matrix X X R, B' = B * W.map (algebraMap R C) := by
  choose c hc using fun α => (Submodule.mem_span_range_iff_exists_fun R).1 (h α)
  refine ⟨fun i α => c α i, ?_⟩
  ext x α
  have := congrFun (hc α) x
  rw [Finset.sum_apply] at this
  simp only [Pi.smul_apply, Algebra.smul_def] at this
  rw [← this, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/- English proof (translation)
Establish `hpow : ∀ j k, f j ^ k ∈ A.carrier`. Introduce `j k`. Proceed by induction on `k with`. Consider the case `zero => simpa using A.one_mem`. Consider the case `succ k ih => rw [pow_succ]`.

Conclude with `A.mul_mem _ _ ih (hf j)`. Establish `: (fun y => ∏ j, f j y ^ n j) = ∏ j, f j ^ n j`. Use extensionality with `y`. Simplify using `[Finset.prod_apply]`. Rewrite using `[this]`.

Conclude with `Finset.prod_induction _ (· ∈ A.carrier) (fun a b ha hb => A.mul_mem a b ha hb) A.one_mem (fun j _ => hpow j (n j))`.
-/
lemma monomialCount_prod_pow_mem {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (A : HopfOrder (C := C) R N) {ι : Type} [Fintype ι] (f : ι → N → C)
    (hf : ∀ j, f j ∈ A.carrier) (n : ι → ℕ) : (fun y => ∏ j, f j y ^ n j) ∈ A.carrier := by
  have hpow : ∀ j k, f j ^ k ∈ A.carrier := by
    intro j k
    induction k with
    | zero => simpa using A.one_mem
    | succ k ih => rw [pow_succ]; exact A.mul_mem _ _ ih (hf j)
  have : (fun y => ∏ j, f j y ^ n j) = ∏ j, f j ^ n j := by
    ext y; simp [Finset.prod_apply]
  rw [this]
  exact Finset.prod_induction _ (· ∈ A.carrier) (fun a b ha hb => A.mul_mem a b ha hb)
    A.one_mem (fun j _ => hpow j (n j))

end Count

/- English proof (translation)
Break down `isEmpty_or_nonempty ι with hι | hι` into its components or cases. Simplify using the standard rewrite rules. Establish `hpos : 0 < Fintype.card ι` using `Fintype.card_pos`. Establish `h2 : p * (p - 1) / 2 * 2 = p * (p - 1)` using `Nat.div_mul_cancel (Nat.even_mul_pred_self p).two_dvd`. Establish `h3 : p ^ (Fintype.card ι - 1) * p = p ^ Fintype.card ι`.

Rewrite using `[← pow_succ, Nat.sub_add_cancel hpos]`. Establish `hcard : Fintype.card (ι → ZMod p) = p ^ Fintype.card ι`. Simplify using `[ZMod.card]`. Rewrite using `[Finset.prod_pow, ← pow_mul, hcard]`. Use `congr 1`.

Combine the equalities or inequalities in the displayed calculation.
-/
lemma monomialCount_exponent (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : ι → NNReal) :
    (∏ j, a j) ^ (Fintype.card (ι → ZMod p) * (p - 1)) =
      (∏ j, a j ^ (p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2))) ^ 2 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have hpos : 0 < Fintype.card ι := Fintype.card_pos
  have h2 : p * (p - 1) / 2 * 2 = p * (p - 1) :=
    Nat.div_mul_cancel (Nat.even_mul_pred_self p).two_dvd
  have h3 : p ^ (Fintype.card ι - 1) * p = p ^ Fintype.card ι := by
    rw [← pow_succ, Nat.sub_add_cancel hpos]
  have hcard : Fintype.card (ι → ZMod p) = p ^ Fintype.card ι := by
    simp [ZMod.card]
  rw [Finset.prod_pow, ← pow_mul, hcard]
  congr 1
  calc p ^ Fintype.card ι * (p - 1) = p ^ (Fintype.card ι - 1) * p * (p - 1) := by rw [h3]
    _ = p ^ (Fintype.card ι - 1) * (p * (p - 1)) := by ring
    _ = p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2 * 2) := by rw [h2]
    _ = p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2) * 2 := by ring

/- English proof (translation)
Introduce `p _ C _ _ _ v R _ _ hv hp1 ι _ _ AA cA cN hA hN`. Take `⟨Λ, ε, hΛ, hspan, hε, hlen⟩` from `hsmith p C v R hv hp1 ι AA`. Establish `hcA : cA = ∏ j, v (algebraMap R C (ε j))` using `hasLen_unique hv hA hlen`. Establish `hl` using `fun j => lifts p C v R hv hp1 ι AA (Λ j) (ε j) (by rw [hspan]; exact Submodule.subset_span ⟨j, rfl⟩) (hε j)`. Use `choose u hu_mem hu_int hu_cong using hl`.

Set `B' : Matrix (ι → ZMod p) (ι → ZMod p) C` to `Matrix.of fun (x α : ι → ZMod p) => ∏ j, (algebraMap R C (ε j) * u j x) ^ (α j).val`. Establish `hB'v : v B'.det = ∏ j, v (algebraMap R C (ε j)) ^ (p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2))` using `(u5 p C v R hv hp1 ι Λ u hΛ hu_int hu_cong).2 fun j => algebraMap R C (ε j)`. Establish `hsq : cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) = v B'.det ^ 2`. Rewrite using `[hcA, hB'v]`. Conclude with `monomialCount_exponent p _`.

Establish `hp0 : v (p : C) ≠ 0` using `(Valuation.ne_zero_iff v).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)`. Establish `hε0 : ∀ j, v (algebraMap R C (ε j)) ≠ 0`. Introduce `j h0`. Establish `hpp : p - 1 ≠ 0` using `by have := (Fact.out : p.Prime).two_le; omega`. Use `hε j` as an intermediate fact.

Rewrite `this` using `[h0, zero_pow hpp]`. Conclude with `hp0 (le_antisymm this zero_le)`. Establish `hB'0 : v B'.det ≠ 0`. Rewrite using `[hB'v]`. Conclude with `Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (hε0 j)`.

Establish `hmem : ∀ α : ι → ZMod p, (fun x => B' x α) ∈ AA.carrier`. Introduce `α`. Conclude with `monomialCount_prod_pow_mem AA (fun j y => algebraMap R C (ε j) * u j y) (fun j => (Submodule.mem_inf.1 (hu_mem j)).1) (fun j => (α j).val)`. Take `⟨B, hAA, hBc⟩` from `hN`. Take `⟨W, hW⟩` from `monomialCount_exists_factor (R := R) B B' (fun α => hAA ▸ hmem α)`.

Establish `hdet : v B'.det = cN * v (algebraMap R C W.det)`. Rewrite using `[hW, Matrix.det_mul, map_mul, RingHom.map_det, hBc]`. Both sides reduce to the same expression. Establish `hw1 : v (algebraMap R C W.det) ≤ 1` using `hv.map_le_one W.det`. Establish `hle : v B'.det ≤ cN`.

Rewrite using `[hdet]`. Conclude with `mul_le_of_le_one_right zero_le hw1`. Use `⟨by rw [hsq]; exact pow_le_pow_left₀ zero_le hle 2, fun heq => ?_⟩` and prove the remaining obligations. Establish `hBeq : v B'.det = cN`. Rewrite `heq` using `[hsq]`.

Conclude with `(pow_left_inj₀ zero_le zero_le two_ne_zero).1 heq`. Establish `hcN0 : cN ≠ 0` using `hBeq ▸ hB'0`. Establish `hw : v (algebraMap R C W.det) = 1`. Establish `h : cN * v (algebraMap R C W.det) = cN * 1` using `by rw [← hdet, hBeq, mul_one]`. Conclude with `mul_left_cancel₀ hcN0 h`.

Establish `hWu : IsUnit W.det` using `hv.isUnit_of_one (isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at hw) hw`. Establish `hBeq' : B' * (W⁻¹).map (algebraMap R C) = B`. Rewrite using `[hW, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hWu, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]`. Use `⟨fun j y => algebraMap R C (ε j) * u j y, hu_mem, ?_⟩` and prove the remaining obligations. Establish `hspan' : Submodule.span R (Set.range fun (α : ι → ZMod p) (y : ι → ZMod p) => ∏ j, (algebraMap R C (ε j) * u j y) ^ (α j).val) = Submodule.span R (Set.range fun α x => B' x α)` using `rfl`.

Rewrite using `[hspan']`. Use `le_antisymm ?_ (Submodule.span_le.2 ?_)` and prove the remaining obligations. Rewrite using `[hAA]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`.

Use `monomialCount_col_mem_span (R := R) B' (W⁻¹) j` as an intermediate fact. Rewrite `this` using `[hBeq']`. Then use the resulting hypothesis. Introduce and unpack `_ ⟨α, rfl⟩`. Conclude with `hmem α`.
-/
theorem cnt_coord_of (hsmith : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∃ (Λ : Matrix ι ι R) (ε : ι → R), IsUnit Λ.det ∧ afLat p AA.carrier = Submodule.span R (Set.range fun j => ε j • Λ j) ∧ (∀ j, v (p : C) ≤ v (algebraMap R C (ε j)) ^ (p - 1)) ∧ HasLen v R (AFQuot p AA.carrier) (∏ j, v (algebraMap R C (ε j)))) :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) = cN ^ 2 → ∃ x : ι → (ι → ZMod p) → C, (∀ j, x j ∈ afFun p AA.carrier) ∧ AA.carrier = Submodule.span R (Set.range fun (α : ι → ZMod p) (y : ι → ZMod p) => ∏ j, x j y ^ (α j).val)) := by
  intro p _ C _ _ _ v R _ _ hv hp1 ι _ _ AA cA cN hA hN
  obtain ⟨Λ, ε, hΛ, hspan, hε, hlen⟩ := hsmith p C v R hv hp1 ι AA
  have hcA : cA = ∏ j, v (algebraMap R C (ε j)) := hasLen_unique hv hA hlen
  have hl := fun j => lifts p C v R hv hp1 ι AA (Λ j) (ε j)
    (by rw [hspan]; exact Submodule.subset_span ⟨j, rfl⟩) (hε j)
  choose u hu_mem hu_int hu_cong using hl

  let B' : Matrix (ι → ZMod p) (ι → ZMod p) C := Matrix.of fun (x α : ι → ZMod p) =>
    ∏ j, (algebraMap R C (ε j) * u j x) ^ (α j).val
  have hB'v : v B'.det = ∏ j, v (algebraMap R C (ε j)) ^
      (p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2)) :=
    (u5 p C v R hv hp1 ι Λ u hΛ hu_int hu_cong).2 fun j => algebraMap R C (ε j)
  have hsq : cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) = v B'.det ^ 2 := by
    rw [hcA, hB'v]
    exact monomialCount_exponent p _

  have hp0 : v (p : C) ≠ 0 :=
    (Valuation.ne_zero_iff v).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hε0 : ∀ j, v (algebraMap R C (ε j)) ≠ 0 := by
    intro j h0
    have hpp : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
    have := hε j
    rw [h0, zero_pow hpp] at this
    exact hp0 (le_antisymm this zero_le)
  have hB'0 : v B'.det ≠ 0 := by
    rw [hB'v]
    exact Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (hε0 j)

  have hmem : ∀ α : ι → ZMod p, (fun x => B' x α) ∈ AA.carrier := by
    intro α
    exact monomialCount_prod_pow_mem AA (fun j y => algebraMap R C (ε j) * u j y)
      (fun j => (Submodule.mem_inf.1 (hu_mem j)).1) (fun j => (α j).val)
  obtain ⟨B, hAA, hBc⟩ := hN
  obtain ⟨W, hW⟩ := monomialCount_exists_factor (R := R) B B' (fun α => hAA ▸ hmem α)
  have hdet : v B'.det = cN * v (algebraMap R C W.det) := by
    rw [hW, Matrix.det_mul, map_mul, RingHom.map_det, hBc]; rfl
  have hw1 : v (algebraMap R C W.det) ≤ 1 := hv.map_le_one W.det
  have hle : v B'.det ≤ cN := by
    rw [hdet]; exact mul_le_of_le_one_right zero_le hw1
  refine ⟨by rw [hsq]; exact pow_le_pow_left₀ zero_le hle 2, fun heq => ?_⟩
  have hBeq : v B'.det = cN := by
    rw [hsq] at heq
    exact (pow_left_inj₀ zero_le zero_le two_ne_zero).1 heq
  have hcN0 : cN ≠ 0 := hBeq ▸ hB'0
  have hw : v (algebraMap R C W.det) = 1 := by
    have h : cN * v (algebraMap R C W.det) = cN * 1 := by rw [← hdet, hBeq, mul_one]
    exact mul_left_cancel₀ hcN0 h
  have hWu : IsUnit W.det :=
    hv.isUnit_of_one (isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at hw) hw
  have hBeq' : B' * (W⁻¹).map (algebraMap R C) = B := by
    rw [hW, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hWu,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  refine ⟨fun j y => algebraMap R C (ε j) * u j y, hu_mem, ?_⟩
  have hspan' : Submodule.span R (Set.range fun (α : ι → ZMod p) (y : ι → ZMod p) =>
      ∏ j, (algebraMap R C (ε j) * u j y) ^ (α j).val) =
      Submodule.span R (Set.range fun α x => B' x α) := rfl
  rw [hspan']
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rw [hAA]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    have := monomialCount_col_mem_span (R := R) B' (W⁻¹) j
    rwa [hBeq'] at this
  · rintro _ ⟨α, rfl⟩
    exact hmem α

end PositivityTheory.HtPt.Ra
