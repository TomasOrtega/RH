import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.SegmentBlockOfMonomial

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.Joints.StandardMonomialSpace

/- English proof (translation)
Simplify using `only [YCond, chWt, chStable, h]`.
-/
theorem ycond_congr {K : Type} [CommRing K] {N r : ℕ} [NeZero r] {LL LL' : ChainLetters N} (h : LL.vec = LL'.vec) (j : ℕ)
    (M : WithTop ℤ) : YCond K (r := r) LL j M = YCond K (r := r) LL' j M := by
  simp only [YCond, chWt, chStable, h]

section E

variable {s r : ℕ}

/- English proof (translation)
Simplify using `only [chW, chE, ne_eq, Fin.mk.injEq]`. Use linear arithmetic over natural numbers and integers.
-/
theorem chW_ne_chE (i i' : Fin s) : chW i ≠ chE i' := by
  simp only [chW, chE, ne_eq, Fin.mk.injEq]
  omega

/- English proof (translation)
Simplify using `only [chW, chU, ne_eq, Fin.mk.injEq]`. Use `i.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem chW_ne_chU (i : Fin s) : chW i ≠ chU s := by
  simp only [chW, chU, ne_eq, Fin.mk.injEq]
  have := i.2
  omega

/- English proof (translation)
Simplify using `only [chE, chU, ne_eq, Fin.mk.injEq]`. Use `i.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem chE_ne_chU (i : Fin s) : chE i ≠ chU s := by
  simp only [chE, chU, ne_eq, Fin.mk.injEq]
  have := i.2
  omega

/- English proof (translation)
Simplify using `only [chW, Fin.mk.injEq] at h`. Conclude with `Fin.ext (by omega)`.
-/
theorem chW_inj {i i' : Fin s} (h : chW i = chW i') : i = i' := by
  simp only [chW, Fin.mk.injEq] at h
  exact Fin.ext (by omega)

/- English proof (translation)
Simplify using `only [chE, Fin.mk.injEq] at h`. Conclude with `Fin.ext (by omega)`.
-/
theorem chE_inj {i i' : Fin s} (h : chE i = chE i') : i = i' := by
  simp only [chE, Fin.mk.injEq] at h
  exact Fin.ext (by omega)

def eCh (a0 : Fin (2 * s + 1)) : Fin (2 * s + 1) → ℕ := fun a => if a = a0 then 1 else 0

def dEps (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) : Fin (2 * s + 1) → ℕ :=
  (∑ i, ∑ c, (ez i c • eCh (chW i) + ey i c • eCh (chE i))) + ∑ c, ax c • eCh (chU s)

/- English proof (translation)
Unfold `mEps dEps`. Use `hom_Pol_mul K (pol_prod' _ _ _ fun i _ => pol_prod' _ _ _ fun c _ => ?_) (pol_prod' _ _ _ fun c _ => ?_)` and prove the remaining obligations. Conclude with `hom_Pol_mul K (pol_pow' (pol_X' (chW i) c) _) (pol_pow' (pol_X' (chE i) c) _)`. Conclude with `pol_pow' (pol_X' (chU s) c) _`.
-/
theorem mEps_pol (K : Type) [CommRing K] [Nontrivial K] (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) :
    mEps K ez ey ax ∈ Pol K r (dEps ez ey ax) := by
  classical
  unfold mEps dEps
  refine hom_Pol_mul K (pol_prod' _ _ _ fun i _ => pol_prod' _ _ _ fun c _ => ?_) (pol_prod' _ _ _ fun c _ => ?_)
  · exact hom_Pol_mul K (pol_pow' (pol_X' (chW i) c) _) (pol_pow' (pol_X' (chE i) c) _)
  · exact pol_pow' (pol_X' (chU s) c) _

/- English proof (translation)
Establish `hWW : ∀ c, chW i = chW c ↔ i = c` using `fun c => ⟨chW_inj, fun h => h ▸ rfl⟩`. Simplify using `only [dEps, eCh, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hWW, chW_ne_chE i, chW_ne_chU i, if_false, mul_zero, add_zero, Finset.sum_const_zero, mul_ite, mul_one]`. Rewrite using `[Finset.sum_eq_single i (fun b _ hb => Finset.sum_eq_zero fun c _ => if_neg (fun h => hb h.symm)) (fun h => absurd (Finset.mem_univ i) h)]`. Simplify using the standard rewrite rules.
-/
theorem dEps_chW_eq_sum (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) (i : Fin s) : dEps ez ey ax (chW i) = ∑ c, ez i c := by
  have hWW : ∀ c, chW i = chW c ↔ i = c := fun c => ⟨chW_inj, fun h => h ▸ rfl⟩
  simp only [dEps, eCh, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hWW, chW_ne_chE i,
    chW_ne_chU i, if_false, mul_zero, add_zero, Finset.sum_const_zero, mul_ite, mul_one]
  rw [Finset.sum_eq_single i (fun b _ hb => Finset.sum_eq_zero fun c _ => if_neg (fun h => hb h.symm))
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

/- English proof (translation)
Establish `hEE : ∀ c, chE i = chE c ↔ i = c` using `fun c => ⟨chE_inj, fun h => h ▸ rfl⟩`. Establish `hEW : ∀ c, chE i = chW c ↔ False` using `fun c => ⟨fun h => chW_ne_chE c i h.symm, False.elim⟩`. Simplify using `only [dEps, eCh, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hEE, hEW, chE_ne_chU i, if_false, mul_zero, add_zero, zero_add, Finset.sum_const_zero, mul_ite, mul_one]`. Rewrite using `[Finset.sum_eq_single i (fun b _ hb => Finset.sum_eq_zero fun c _ => if_neg (fun h => hb h.symm)) (fun h => absurd (Finset.mem_univ i) h)]`. Simplify using the standard rewrite rules.
-/
theorem dEps_E (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) (i : Fin s) : dEps ez ey ax (chE i) = ∑ c, ey i c := by
  have hEE : ∀ c, chE i = chE c ↔ i = c := fun c => ⟨chE_inj, fun h => h ▸ rfl⟩
  have hEW : ∀ c, chE i = chW c ↔ False := fun c => ⟨fun h => chW_ne_chE c i h.symm, False.elim⟩
  simp only [dEps, eCh, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hEE, hEW,
    chE_ne_chU i, if_false, mul_zero, add_zero, zero_add, Finset.sum_const_zero, mul_ite, mul_one]
  rw [Finset.sum_eq_single i (fun b _ hb => Finset.sum_eq_zero fun c _ => if_neg (fun h => hb h.symm))
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

/- English proof (translation)
Establish `hUW : ∀ c, chU s = chW c ↔ False` using `fun c => ⟨fun h => chW_ne_chU c h.symm, False.elim⟩`. Establish `hUE : ∀ c, chU s = chE c ↔ False` using `fun c => ⟨fun h => chE_ne_chU c h.symm, False.elim⟩`. Simplify using `[dEps, eCh, hUW, hUE]`.
-/
theorem dEps_U (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) : dEps ez ey ax (chU s) = ∑ c, ax c := by
  have hUW : ∀ c, chU s = chW c ↔ False := fun c => ⟨fun h => chW_ne_chU c h.symm, False.elim⟩
  have hUE : ∀ c, chU s = chE c ↔ False := fun c => ⟨fun h => chE_ne_chU c h.symm, False.elim⟩
  simp [dEps, eCh, hUW, hUE]

/- English proof (translation)
Assemble the required witnesses or components as `⟨mEps O ez ey ax, by simp [mEps]⟩`.
-/
theorem mEps_int {O : Type} [CommRing O] [IsDomain O] (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) :
    mEps (KK O) ez ey ax ∈ IntPol O (Fin (2 * s + 1) × Fin r) :=
  ⟨mEps O ez ey ax, by simp [mEps]⟩

variable {K : Type} [Field K] [CharZero K] [NeZero r]

/- English proof (translation)
Unfold `mEps`. Rewrite using `[WithTop.coe_add]`. Use `ycond_mul LL J _ _ (ycond_prod LL J _ _ _ fun i _ => ?_) ?_` and prove the remaining obligations. Establish `h1` using `ycond_prod (K := K) LL J Finset.univ (fun c : Fin r => (ez i c : ℤ) * (vWt LL J (chW i) : ℤ)) (fun c => X (chW i, c) ^ ez i c * X (chE i, c) ^ ey i c) (fun c _ => by`. Establish `a1` using `ycond_pow LL J _ (ycond_X (K := K) LL J (chW i) c) (ez i c)`.

Establish `a2` using `ycond_pow LL J _ (ycond_X (K := K) LL J (chE i) c) (ey i c)`. Establish `hv : vWt LL J (chE i) = 0` using `by unfold vWt; rw [if_neg]; rw [hE i]; simp`. Rewrite `a2` using `[hv]`. Use `ycond_mul LL J _ _ a1 a2` as an intermediate fact. Rewrite `this` using `[← WithTop.coe_add]`.

Simplify using `using this)`. Rewrite `h1` using `[← Finset.sum_mul]`. Rewrite using `[Nat.cast_sum]`. Conclude with `h1`. Establish `h1` using `ycond_prod (K := K) LL J Finset.univ (fun c : Fin r => (ax c : ℤ) * (vWt LL J (chU s) : ℤ)) (fun c => X (chU s, c) ^ ax c) (fun c _ => ycond_pow LL J _ (ycond_X (K := K) LL J (chU s) c) (ax c))`.

Rewrite `h1` using `[← Finset.sum_mul]`. Rewrite using `[Nat.cast_sum]`. Conclude with `h1`.
-/
theorem ycond_mEps (LL : ChainLetters (2 * s + 1)) (J : ℕ) (hE : ∀ i : Fin s, LL.vec (chE i) = false)
    (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) :
    mEps K ez ey ax ∈ YCond K (r := r) LL J
      (((∑ i, ((∑ c, ez i c : ℕ) : ℤ) * (vWt LL J (chW i) : ℤ)) + ((∑ c, ax c : ℕ) : ℤ) * (vWt LL J (chU s) : ℤ) : ℤ) : WithTop ℤ) := by
  classical
  unfold mEps
  rw [WithTop.coe_add]
  refine ycond_mul LL J _ _ (ycond_prod LL J _ _ _ fun i _ => ?_) ?_
  · have h1 := ycond_prod (K := K) LL J Finset.univ (fun c : Fin r => (ez i c : ℤ) * (vWt LL J (chW i) : ℤ))
      (fun c => X (chW i, c) ^ ez i c * X (chE i, c) ^ ey i c) (fun c _ => by
        have a1 := ycond_pow LL J _ (ycond_X (K := K) LL J (chW i) c) (ez i c)
        have a2 := ycond_pow LL J _ (ycond_X (K := K) LL J (chE i) c) (ey i c)
        have hv : vWt LL J (chE i) = 0 := by unfold vWt; rw [if_neg]; rw [hE i]; simp
        rw [hv] at a2
        have := ycond_mul LL J _ _ a1 a2
        rw [← WithTop.coe_add] at this
        simpa using this)
    rw [← Finset.sum_mul] at h1
    rw [Nat.cast_sum]
    exact h1
  · have h1 := ycond_prod (K := K) LL J Finset.univ (fun c : Fin r => (ax c : ℤ) * (vWt LL J (chU s) : ℤ))
      (fun c => X (chU s, c) ^ ax c) (fun c _ => ycond_pow LL J _ (ycond_X (K := K) LL J (chU s) c) (ax c))
    rw [← Finset.sum_mul] at h1
    rw [Nat.cast_sum]
    exact h1

/- English proof (translation)
The claim follows from `ycond_prod LL J _ _ _ fun l _ => ycond_pow LL J _ (ycond_pair LL J _ _ (hW _) (hE _)) (k l)`.
-/
theorem ycond_pairs (S : SegData s) (LL : ChainLetters (2 * s + 1)) (J : ℕ) (hW : ∀ i : Fin s, LL.vec (chW i) = true)
    (hE : ∀ i : Fin s, LL.vec (chE i) = false) (k : Fin S.t → ℕ) :
    ∏ l, pairU K r S l ^ k l ∈ YCond K (r := r) LL J
      ((∑ l, (k l : ℤ) * (pWt J (chW (uTop S l)) (chE (uTop S l)) : ℤ) : ℤ) : WithTop ℤ) :=
  ycond_prod LL J _ _ _ fun l _ => ycond_pow LL J _ (ycond_pair LL J _ _ (hW _) (hE _)) (k l)

/- English proof (translation)
Establish `hu : ∀ l : Fin S.t, ((uTop S l : Fin s) : ℕ) = S.sigma + l` using `fun l => rfl`. Establish `hlt : ∀ l : Fin S.t, S.sigma + (l : ℕ) < s` using `fun l => by rw [← hu]; exact (uTop S l).2`. Distinguish the cases in `hJ : ∃ l : Fin S.t, J = 2 * (S.sigma + (l : ℕ)) + 1`. Take `⟨l0, hl0⟩` from `hJ`. Establish `hsum : ∑ l, pWt J (chW (uTop S l)) (chE (uTop S l)) = 1`.

Rewrite using `[Finset.sum_eq_single l0]`. Simplify using `only [pWt, chW, chE, hu]`. Rewrite using `[if_pos]`. Apply the tactic sequence `constructor <;> omega`. Introduce `l _ hl`.

Simplify using `only [pWt, chW, chE, hu]`. Rewrite using `[if_neg]`. Introduce and unpack `⟨h1, h2⟩`. Apply `hl` to reduce the goal to its premises. Conclude with `Fin.ext (by omega)`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ l0) h`. Establish `hv : vWt LL J (chU s) = 0`. Simplify using `only [vWt, chU]`. Use `hlt l0` as an intermediate fact.

Apply `ite_eq_right_iff.mpr` to reduce the goal to its premises. Introduce `h`. Conclude with `absurd h.2 (by omega)`. Use linear arithmetic over natural numbers and integers. Establish `hsum : ∑ l, pWt J (chW (uTop S l)) (chE (uTop S l)) = 0`.

Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Simplify using `only [pWt, chW, chE, hu]`. Rewrite using `[if_neg]`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `hJ ⟨l, by omega⟩`.

Establish `hv : vWt LL J (chU s) ≤ 1`. Unfold `vWt`. Apply the tactic sequence `split_ifs <;> omega`. Use linear arithmetic over natural numbers and integers.
-/
theorem pWt_sum_le (S : SegData s) (LL : ChainLetters (2 * s + 1)) (J : ℕ) :
    (∑ l : Fin S.t, pWt J (chW (uTop S l)) (chE (uTop S l))) + vWt LL J (chU s) ≤ 1 := by
  have hu : ∀ l : Fin S.t, ((uTop S l : Fin s) : ℕ) = S.sigma + l := fun l => rfl
  have hlt : ∀ l : Fin S.t, S.sigma + (l : ℕ) < s := fun l => by rw [← hu]; exact (uTop S l).2
  by_cases hJ : ∃ l : Fin S.t, J = 2 * (S.sigma + (l : ℕ)) + 1
  · obtain ⟨l0, hl0⟩ := hJ
    have hsum : ∑ l, pWt J (chW (uTop S l)) (chE (uTop S l)) = 1 := by
      rw [Finset.sum_eq_single l0]
      · simp only [pWt, chW, chE, hu]
        rw [if_pos]
        constructor <;> omega
      · intro l _ hl
        simp only [pWt, chW, chE, hu]
        rw [if_neg]
        rintro ⟨h1, h2⟩
        apply hl
        exact Fin.ext (by omega)
      · intro h
        exact absurd (Finset.mem_univ l0) h
    have hv : vWt LL J (chU s) = 0 := by
      simp only [vWt, chU]
      have := hlt l0
      apply ite_eq_right_iff.mpr
      intro h
      exact absurd h.2 (by omega)
    omega
  · have hsum : ∑ l, pWt J (chW (uTop S l)) (chE (uTop S l)) = 0 := by
      refine Finset.sum_eq_zero fun l _ => ?_
      simp only [pWt, chW, chE, hu]
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hJ ⟨l, by omega⟩
    have hv : vWt LL J (chU s) ≤ 1 := by
      unfold vWt
      split_ifs <;> omega
    omega

/- English proof (translation)
Establish `hv : ∀ a, (vWt LL J a : ℤ) ≤ 1` using `fun a => by`. Unfold `vWt`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hA : (∑ i, ((∑ c, ez i c : ℕ) : ℤ) * (vWt LL J (chW i) : ℤ)) ≤ (s : ℤ) * Qe`. Combine the equalities or inequalities in the displayed calculation.

Establish `e1 : ((∑ c, ez i c : ℕ) : ℤ) ≤ Qe` using `by exact_mod_cast h1 i`. Establish `e2` using `hv (chW i)`. Establish `e3 : (0 : ℤ) ≤ ((∑ c, ez i c : ℕ) : ℤ)` using `Nat.cast_nonneg _`. Establish `e4 : (0 : ℤ) ≤ (vWt LL J (chW i) : ℤ)` using `Nat.cast_nonneg _`. Use the polynomial consequences of the given equalities and inequalities.

Use `_ = (s : ℤ) * Qe := by simp`. Establish `hpw` using `pWt_sum_le S LL J`. Establish `e3 : ((∑ l, pWt J (chW (uTop S l)) (chE (uTop S l)) : ℕ) : ℤ) + (vWt LL J (chU s) : ℤ) ≤ 1`. Conclude with `hpw` after adjusting the coercions. Move the coercions through the operations in `at e3`.

Establish `eB : ((∑ c, ax c : ℕ) : ℤ) * (vWt LL J (chU s) : ℤ) ≤ (Qe : ℤ) * (vWt LL J (chU s) : ℤ)` using `mul_le_mul_of_nonneg_right (by exact_mod_cast h2) (Nat.cast_nonneg _)`. Establish `eC : ∑ l, (k l : ℤ) * (pWt J (chW (uTop S l)) (chE (uTop S l)) : ℤ) ≤ ∑ l, (Qe : ℤ) * (pWt J (chW (uTop S l)) (chE (uTop S l)) : ℤ)` using `Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (by exact_mod_cast h3 l) (Nat.cast_nonneg _)`. Rewrite `eC` using `[← Finset.mul_sum]`. Establish `eQ` using `mul_le_mul_of_nonneg_left e3 (Nat.cast_nonneg Qe : (0 : ℤ) ≤ Qe)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem rowInc_le (S : SegData s) (LL : ChainLetters (2 * s + 1)) (J : ℕ) (ez : Fin s → Fin r → ℕ) (ax : Fin r → ℕ)
    (k : Fin S.t → ℕ) (Qe : ℕ) (h1 : ∀ i, ∑ c, ez i c ≤ Qe) (h2 : ∑ c, ax c ≤ Qe) (h3 : ∀ l, k l ≤ Qe) :
    ((∑ i, ((∑ c, ez i c : ℕ) : ℤ) * (vWt LL J (chW i) : ℤ)) + ((∑ c, ax c : ℕ) : ℤ) * (vWt LL J (chU s) : ℤ)) +
      ∑ l, (k l : ℤ) * (pWt J (chW (uTop S l)) (chE (uTop S l)) : ℤ) ≤ ((s : ℤ) + 1) * Qe := by
  have hv : ∀ a, (vWt LL J a : ℤ) ≤ 1 := fun a => by
    unfold vWt
    split_ifs <;> simp
  have hA : (∑ i, ((∑ c, ez i c : ℕ) : ℤ) * (vWt LL J (chW i) : ℤ)) ≤ (s : ℤ) * Qe := by
    calc (∑ i, ((∑ c, ez i c : ℕ) : ℤ) * (vWt LL J (chW i) : ℤ)) ≤ ∑ _i : Fin s, (Qe : ℤ) :=
          Finset.sum_le_sum fun i _ => by
            have e1 : ((∑ c, ez i c : ℕ) : ℤ) ≤ Qe := by exact_mod_cast h1 i
            have e2 := hv (chW i)
            have e3 : (0 : ℤ) ≤ ((∑ c, ez i c : ℕ) : ℤ) := Nat.cast_nonneg _
            have e4 : (0 : ℤ) ≤ (vWt LL J (chW i) : ℤ) := Nat.cast_nonneg _
            nlinarith
      _ = (s : ℤ) * Qe := by simp
  have hpw := pWt_sum_le S LL J
  have e3 : ((∑ l, pWt J (chW (uTop S l)) (chE (uTop S l)) : ℕ) : ℤ) + (vWt LL J (chU s) : ℤ) ≤ 1 := by
    exact_mod_cast hpw
  push_cast at e3
  have eB : ((∑ c, ax c : ℕ) : ℤ) * (vWt LL J (chU s) : ℤ) ≤ (Qe : ℤ) * (vWt LL J (chU s) : ℤ) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast h2) (Nat.cast_nonneg _)
  have eC : ∑ l, (k l : ℤ) * (pWt J (chW (uTop S l)) (chE (uTop S l)) : ℤ) ≤
      ∑ l, (Qe : ℤ) * (pWt J (chW (uTop S l)) (chE (uTop S l)) : ℤ) :=
    Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (by exact_mod_cast h3 l) (Nat.cast_nonneg _)
  rw [← Finset.mul_sum] at eC
  have eQ := mul_le_mul_of_nonneg_left e3 (Nat.cast_nonneg Qe : (0 : ℤ) ≤ Qe)
  nlinarith

end E

def capIdx {s : ℕ} (S : SegData s) (k : Fin (S.t + 1)) : ℕ := if h : (k : ℕ) < S.t then (uTop S ⟨k, h⟩ : ℕ) else s

/- English proof (translation)
Use `show (segmentCapacities p S b k).map (fun x : ℤ => ⌊(x : ℝ) - mu⌋) = _`. Unfold `segmentCapacities capIdx`. Apply the tactic sequence `split_ifs with h <;> rfl`.
-/
theorem thr_eq {s r : ℕ} (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (mu : ℝ) (b : SegBlock s r) (k : Fin (S.t + 1)) :
    (blockData p S aTop aPlus mu b).T.thr k = ((⌊((cap p S b (capIdx S k) : ℤ) : ℝ) - mu⌋ : ℤ) : WithTop ℤ) := by
  show (segmentCapacities p S b k).map (fun x : ℤ => ⌊(x : ℝ) - mu⌋) = _
  unfold segmentCapacities capIdx
  split_ifs with h <;> rfl

end Formalism.MainNotions.ColumnSystems.Pf
