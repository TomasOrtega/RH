import Mathlib
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Formalism.LocalToGlobal.Columns.RowForms

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions

section PosX

variable (R : Ranks)

def posXn (i : ℕ) : ℕ :=
  if i < R.k - 1 then i
  else if i < R.r then R.k - 1 + (i - (R.k - 1)) * (R.t + 1)
  else R.k - 1 + ((i - R.r) / R.t) * (R.t + 1) + ((i - R.r) % R.t + 1)

def invXn (y : ℕ) : ℕ :=
  if y < R.k - 1 then y
  else if (y - (R.k - 1)) % (R.t + 1) = 0 then R.k - 1 + (y - (R.k - 1)) / (R.t + 1)
  else R.r + ((y - (R.k - 1)) / (R.t + 1)) * R.t + ((y - (R.k - 1)) % (R.t + 1) - 1)

/- English proof (translation)
Use `R.rank_add_five_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem nz_t_pos : 0 < R.t := by
  have := R.rank_add_five_le
  omega

/- English proof (translation)
Use `R.m_add_three_le_k` as an intermediate fact. Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers.
-/
theorem nz_r_eq : R.r = R.k - 1 + R.m := by
  have := R.m_add_three_le_k
  unfold Ranks.r
  omega

/- English proof (translation)
Use `R.m_add_three_le_k` as an intermediate fact. Unfold `Ranks.N`. Use linear arithmetic over natural numbers and integers.
-/
theorem nz_rankX : R.N R.m - 1 = R.k - 1 + R.m * (R.t + 1) := by
  have := R.m_add_three_le_k
  unfold Ranks.N
  omega

/- English proof (translation)
Use `nz_r_eq R` as an intermediate fact. Unfold `posXn`. Rewrite using `[if_neg (by omega), if_neg (by omega)]`.
-/
theorem nz_posXn_hi {i : ℕ} (h : R.r ≤ i) :
    posXn R i = R.k - 1 + ((i - R.r) / R.t) * (R.t + 1) + ((i - R.r) % R.t + 1) := by
  have := nz_r_eq R
  unfold posXn
  rw [if_neg (by omega), if_neg (by omega)]

/- English proof (translation)
Establish `hr` using `nz_r_eq R`. Establish `ht` using `nz_t_pos R`. Distinguish the cases in `h1 : i < R.k - 1`. Unfold `posXn invXn`. Rewrite using `[if_pos h1, if_pos h1]`.

Distinguish the cases in `h2 : i < R.r`. Establish `e0 : posXn R i = R.k - 1 + (i - (R.k - 1)) * (R.t + 1)`. Unfold `posXn`. Rewrite using `[if_neg h1, if_pos h2]`. Take `⟨d1, d2⟩` from `divmod (R.t + 1) (i - (R.k - 1)) 0 (by omega)`.

Establish `e1 : R.k - 1 + (i - (R.k - 1)) * (R.t + 1) - (R.k - 1) = (i - (R.k - 1)) * (R.t + 1) + 0` using `by omega`. Unfold `invXn`. Rewrite using `[e0, if_neg (by omega), e1, d1, d2, if_pos rfl]`. Use linear arithmetic over natural numbers and integers. Establish `hm : (i - R.r) % R.t < R.t` using `Nat.mod_lt _ ht`.

Take `⟨d1, d2⟩` from `divmod (R.t + 1) ((i - R.r) / R.t) ((i - R.r) % R.t + 1) (by omega)`. Establish `e1 : R.k - 1 + ((i - R.r) / R.t) * (R.t + 1) + ((i - R.r) % R.t + 1) - (R.k - 1) = ((i - R.r) / R.t) * (R.t + 1) + ((i - R.r) % R.t + 1)` using `by omega`. Establish `e2` using `Nat.div_add_mod (i - R.r) R.t`. Rewrite `e2` using `[Nat.mul_comm]`. Unfold `invXn`.

Rewrite using `[nz_posXn_hi R (Nat.not_lt.mp h2), if_neg (by omega), e1, d1, d2, if_neg (by omega)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem nz_invXn_posXn (i : ℕ) : invXn R (posXn R i) = i := by
  have hr := nz_r_eq R
  have ht := nz_t_pos R
  by_cases h1 : i < R.k - 1
  · unfold posXn invXn
    rw [if_pos h1, if_pos h1]
  by_cases h2 : i < R.r
  · have e0 : posXn R i = R.k - 1 + (i - (R.k - 1)) * (R.t + 1) := by
      unfold posXn
      rw [if_neg h1, if_pos h2]
    obtain ⟨d1, d2⟩ := divmod (R.t + 1) (i - (R.k - 1)) 0 (by omega)
    have e1 : R.k - 1 + (i - (R.k - 1)) * (R.t + 1) - (R.k - 1) = (i - (R.k - 1)) * (R.t + 1) + 0 := by omega
    unfold invXn
    rw [e0, if_neg (by omega), e1, d1, d2, if_pos rfl]
    omega
  · have hm : (i - R.r) % R.t < R.t := Nat.mod_lt _ ht
    obtain ⟨d1, d2⟩ := divmod (R.t + 1) ((i - R.r) / R.t) ((i - R.r) % R.t + 1) (by omega)
    have e1 : R.k - 1 + ((i - R.r) / R.t) * (R.t + 1) + ((i - R.r) % R.t + 1) - (R.k - 1) =
        ((i - R.r) / R.t) * (R.t + 1) + ((i - R.r) % R.t + 1) := by omega
    have e2 := Nat.div_add_mod (i - R.r) R.t
    rw [Nat.mul_comm] at e2
    unfold invXn
    rw [nz_posXn_hi R (Nat.not_lt.mp h2), if_neg (by omega), e1, d1, d2, if_neg (by omega)]
    omega

/- English proof (translation)
Establish `hr` using `nz_r_eq R`. Establish `ht` using `nz_t_pos R`. Establish `hn` using `nz_rankX R`. Establish `hn'` using `rank_X'_eq R`. Distinguish the cases in `h1 : i < R.k - 1`.

Unfold `posXn`. Rewrite using `[if_pos h1]`. Conclude with `h`. Distinguish the cases in `h2 : i < R.r`. Establish `h3 : (i - (R.k - 1) + 1) * (R.t + 1) ≤ R.m * (R.t + 1)` using `Nat.mul_le_mul_right _ (by omega)`.

Rewrite `h3` using `[Nat.add_mul, Nat.one_mul]`. Unfold `posXn`. Rewrite using `[if_neg h1, if_pos h2]`. Use linear arithmetic over natural numbers and integers. Establish `hm : (i - R.r) % R.t < R.t` using `Nat.mod_lt _ ht`.

Establish `hd : (i - R.r) / R.t < R.m` using `Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)`. Establish `h3 : ((i - R.r) / R.t + 1) * (R.t + 1) ≤ R.m * (R.t + 1)` using `Nat.mul_le_mul_right _ hd`. Rewrite `h3` using `[Nat.add_mul, Nat.one_mul]`. Rewrite using `[nz_posXn_hi R (Nat.not_lt.mp h2)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem nz_posXn_lt {i : ℕ} (h : i < R.N R.m - 1) : posXn R i < R.N R.m - 1 := by
  have hr := nz_r_eq R
  have ht := nz_t_pos R
  have hn := nz_rankX R
  have hn' := rank_X'_eq R
  by_cases h1 : i < R.k - 1
  · unfold posXn
    rw [if_pos h1]
    exact h
  by_cases h2 : i < R.r
  · have h3 : (i - (R.k - 1) + 1) * (R.t + 1) ≤ R.m * (R.t + 1) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h3
    unfold posXn
    rw [if_neg h1, if_pos h2]
    omega
  · have hm : (i - R.r) % R.t < R.t := Nat.mod_lt _ ht
    have hd : (i - R.r) / R.t < R.m := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    have h3 : ((i - R.r) / R.t + 1) * (R.t + 1) ≤ R.m * (R.t + 1) := Nat.mul_le_mul_right _ hd
    rw [Nat.add_mul, Nat.one_mul] at h3
    rw [nz_posXn_hi R (Nat.not_lt.mp h2)]
    omega

def posXf (i : Fin (R.N R.m - 1)) : Fin (R.N R.m - 1) := ⟨posXn R i.1, nz_posXn_lt R i.2⟩

/- English proof (translation)
Introduce `a b h`. Establish `h1 : posXn R a.1 = posXn R b.1` using `congrArg Fin.val h`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[← nz_invXn_posXn R a.1, ← nz_invXn_posXn R b.1, h1]`.
-/
theorem nz_posXf_inj : Function.Injective (posXf R) := by
  intro a b h
  have h1 : posXn R a.1 = posXn R b.1 := congrArg Fin.val h
  apply Fin.ext
  rw [← nz_invXn_posXn R a.1, ← nz_invXn_posXn R b.1, h1]

def posX : Equiv.Perm (Fin (R.N R.m - 1)) :=
  Equiv.ofBijective (posXf R) (Finite.injective_iff_bijective.mp (nz_posXf_inj R))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem nz_posX_val (i : Fin (R.N R.m - 1)) : (posX R i).1 = posXn R i.1 := rfl

/- English proof (translation)
Establish `hn'` using `rank_X'_eq R`. Rewrite using `[coarse_of_le h1, blkIdx_replicate (nz_t_pos R) R.m (a - R.r) (by omega)]`.
-/
theorem nz_coarseX {a : ℕ} (h1 : R.r ≤ a) (h2 : a < R.N R.m - 1) :
    coarse R.r (List.replicate R.m R.t) a = (a - R.r) / R.t + 1 := by
  have hn' := rank_X'_eq R
  rw [coarse_of_le h1, blkIdx_replicate (nz_t_pos R) R.m (a - R.r) (by omega)]

def sX (B : ℕ) : ℚ := ((R.t : ℚ) - 1) / 2 - (((R.N R.m - 1 : ℕ) : ℚ) - 1) / 2 + (R.k : ℚ) + (B : ℚ) * ((R.t : ℚ) + 1)

/- English proof (translation)
Take `⟨a, ha⟩` from `R.k_even`. Take `⟨c, hc⟩` from `R.t_odd`. Establish `hk` using `R.m_add_three_le_k`. Establish `hn : ((R.N R.m - 1 : ℕ) : ℚ) = (R.k : ℚ) + (R.m : ℚ) * ((R.t : ℚ) + 1) - 1`. Establish `: R.N R.m - 1 + 1 = R.k + R.m * (R.t + 1)`.

Unfold `Ranks.N`. Use linear arithmetic over natural numbers and integers. Establish `h2 : ((R.N R.m - 1 + 1 : ℕ) : ℚ) = ((R.k + R.m * (R.t + 1) : ℕ) : ℚ)` using `by rw [this]`. Move the coercions through the operations in `at h2`. Combine the linear equalities and inequalities to obtain the conclusion.

Unfold `sX`. Rewrite using `[hn, ha, hc]`. Conclude with `⟨(c : ℤ) - ((a : ℤ) + (R.m : ℤ) * ((c : ℤ) + 1) - 1) + ((a : ℤ) + a) + (B : ℤ) * (2 * (c : ℤ) + 1 + 1), by push_cast; ring⟩`.
-/
theorem nz_sX_int (B : ℕ) : ∃ z : ℤ, sX R B = z := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨c, hc⟩ := R.t_odd
  have hk := R.m_add_three_le_k
  have hn : ((R.N R.m - 1 : ℕ) : ℚ) = (R.k : ℚ) + (R.m : ℚ) * ((R.t : ℚ) + 1) - 1 := by
    have : R.N R.m - 1 + 1 = R.k + R.m * (R.t + 1) := by
      unfold Ranks.N
      omega
    have h2 : ((R.N R.m - 1 + 1 : ℕ) : ℚ) = ((R.k + R.m * (R.t + 1) : ℕ) : ℚ) := by rw [this]
    push_cast at h2
    linarith
  unfold sX
  rw [hn, ha, hc]
  exact ⟨(c : ℤ) - ((a : ℤ) + (R.m : ℤ) * ((c : ℤ) + 1) - 1) + ((a : ℤ) + a) + (B : ℤ) * (2 * (c : ℤ) + 1 + 1), by push_cast; ring⟩

variable {R}

/- English proof (translation)
Establish `ht` using `nz_t_pos R`. Establish `hk` using `R.m_add_three_le_k`. Establish `hm : (a.1 - R.r) % R.t < R.t` using `Nat.mod_lt _ ht`. Rewrite using `[RowPar.sgTrue_eq P (posX R a), nz_posX_val, nz_posXn_hi R h, RowPar.sgHC_e _ ((a.1 - R.r) / R.t) ((a.1 - R.r) % R.t + 1) (by omega) (by omega)]`. Unfold `rhoVec sX`.

Rewrite using `[nz_posX_val, nz_posXn_hi R h]`. Establish `hk1 : ((R.k - 1 : ℕ) : ℚ) = (R.k : ℚ) - 1`. Rewrite using `[Nat.cast_sub (by omega)]`. Simplify using the standard rewrite rules. Use `push_cast`.

Rewrite using `[hk1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem RowPar.nz_sgTrue_pos (P : HCParam R) (a : Fin (R.N R.m - 1)) (h : R.r ≤ a.1) :
    (((RowPar.of P).sgTrue).w (posX R a) : ℚ) = -(RowPar.of P).eAt ((a.1 - R.r) / R.t) + sX R ((a.1 - R.r) / R.t) := by
  have ht := nz_t_pos R
  have hk := R.m_add_three_le_k
  have hm : (a.1 - R.r) % R.t < R.t := Nat.mod_lt _ ht
  rw [RowPar.sgTrue_eq P (posX R a), nz_posX_val, nz_posXn_hi R h,
    RowPar.sgHC_e _ ((a.1 - R.r) / R.t) ((a.1 - R.r) % R.t + 1) (by omega) (by omega)]
  unfold rhoVec sX
  rw [nz_posX_val, nz_posXn_hi R h]
  have hk1 : ((R.k - 1 : ℕ) : ℚ) = (R.k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  push_cast
  rw [hk1]
  ring

end PosX

section WtsX

variable {X : Fields} {Word : Type} {R : Ranks} {W : Wts X Word R}

/- English proof (translation)
Take `⟨P, hP⟩` from `hW.row_ok τ`. Unfold `Wts.sgTrue`. Rewrite using `[← hP]`. Conclude with `RowPar.nz_sgTrue_pos P a h`.
-/
theorem nz_sg_val (hW : W.Ok) (τ : X.Tau) (a : Fin (R.N R.m - 1)) (h : R.r ≤ a.1) :
    ((W.sgTrue τ).w (posX R a) : ℚ) = -(W.row τ).eAt ((a.1 - R.r) / R.t) + sX R ((a.1 - R.r) / R.t) := by
  obtain ⟨P, hP⟩ := hW.row_ok τ
  unfold Wts.sgTrue
  rw [← hP]
  exact RowPar.nz_sgTrue_pos P a h

/- English proof (translation)
Rewrite `hab` using `[nz_coarseX R ha a.2, nz_coarseX R hb b.2]`. Establish `h1 : (a.1 - R.r) / R.t = (b.1 - R.r) / R.t` using `by omega`. Establish `h2 : ((W.sgTrue τ).w (posX R a) : ℚ) = ((W.sgTrue τ).w (posX R b) : ℚ)`. Rewrite using `[nz_sg_val hW τ a ha, nz_sg_val hW τ b hb, h1]`. Conclude with `h2` after adjusting the coercions.
-/
theorem nz_sg_const (hW : W.Ok) (τ : X.Tau) (a b : Fin (R.N R.m - 1)) (ha : R.r ≤ a.1) (hb : R.r ≤ b.1)
    (hab : coarse R.r (List.replicate R.m R.t) a.1 = coarse R.r (List.replicate R.m R.t) b.1) :
    (W.sgTrue τ).w (posX R a) = (W.sgTrue τ).w (posX R b) := by
  rw [nz_coarseX R ha a.2, nz_coarseX R hb b.2] at hab
  have h1 : (a.1 - R.r) / R.t = (b.1 - R.r) / R.t := by omega
  have h2 : ((W.sgTrue τ).w (posX R a) : ℚ) = ((W.sgTrue τ).w (posX R b) : ℚ) := by
    rw [nz_sg_val hW τ a ha, nz_sg_val hW τ b hb, h1]
  exact_mod_cast h2

/- English proof (translation)
Establish `hn'` using `rank_X'_eq R`. Establish `hB : (a.1 - R.r) / R.t < R.m` using `Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; have := a.2; omega)`. Take `⟨z, hz⟩` from `he ⟨(a.1 - R.r) / R.t, hB⟩`. Take `⟨y, hy⟩` from `nz_sX_int R ((a.1 - R.r) / R.t)`. Take `⟨c, hc⟩` from `hf`.

Establish `h1 : ((∑ τ, (W.sgTrue τ).w (posX R a) : ℤ) : ℚ) = ((2 * (-z + (c : ℤ) * y) : ℤ) : ℚ)`. Use `push_cast`. Rewrite using `[Finset.sum_congr rfl fun τ _ => nz_sg_val hW τ a ha, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ]`. Establish `h2 : ∑ τ, (W.row τ).eAt ((a.1 - R.r) / R.t) = 2 * (z : ℚ)`. Rewrite using `[← hz]`.

Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Unfold `RowPar.eAt`. Rewrite using `[dif_pos hB]`. Establish `h3 : Fintype.card X.Tau = c + c` using `hc`. Rewrite using `[h2, h3, hy, nsmul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h4 : ∑ τ, (W.sgTrue τ).w (posX R a) = 2 * (-z + (c : ℤ) * y)` using `by exact_mod_cast h1`. Rewrite using `[h4]`. Conclude with `even_two_mul _`.
-/
theorem nz_sg_even (hW : W.Ok) (hf : Even X.f) (he : ∀ j : Fin R.m, ∃ z : ℤ, ∑ τ, (W.row τ).e j = 2 * (z : ℚ))
    (a : Fin (R.N R.m - 1)) (ha : R.r ≤ a.1) : Even (∑ τ, (W.sgTrue τ).w (posX R a)) := by
  have hn' := rank_X'_eq R
  have hB : (a.1 - R.r) / R.t < R.m := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; have := a.2; omega)
  obtain ⟨z, hz⟩ := he ⟨(a.1 - R.r) / R.t, hB⟩
  obtain ⟨y, hy⟩ := nz_sX_int R ((a.1 - R.r) / R.t)
  obtain ⟨c, hc⟩ := hf
  have h1 : ((∑ τ, (W.sgTrue τ).w (posX R a) : ℤ) : ℚ) = ((2 * (-z + (c : ℤ) * y) : ℤ) : ℚ) := by
    push_cast
    rw [Finset.sum_congr rfl fun τ _ => nz_sg_val hW τ a ha, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_const, Finset.card_univ]
    have h2 : ∑ τ, (W.row τ).eAt ((a.1 - R.r) / R.t) = 2 * (z : ℚ) := by
      rw [← hz]
      refine Finset.sum_congr rfl fun τ _ => ?_
      unfold RowPar.eAt
      rw [dif_pos hB]
    have h3 : Fintype.card X.Tau = c + c := hc
    rw [h2, h3, hy, nsmul_eq_mul]
    push_cast
    ring
  have h4 : ∑ τ, (W.sgTrue τ).w (posX R a) = 2 * (-z + (c : ℤ) * y) := by exact_mod_cast h1
  rw [h4]
  exact even_two_mul _

end WtsX

section PosV

variable (R : Ranks) (j : ℕ)

def pV : ℕ := min (RowPar.pOf R j) R.r

def posVn (i : ℕ) : ℕ :=
  if i < pV R j then i else if i < R.r then i + R.t else i - R.r + pV R j

/- English proof (translation)
The claim follows from `min_le_right _ _`.
-/
theorem nz_pV_le : pV R j ≤ R.r := min_le_right _ _

/- English proof (translation)
Establish `h1` using `nz_pV_le R j`. Unfold `Ranks.nV at h ⊢`. Unfold `posVn`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem nz_posVn_lt {i : ℕ} (h : i < R.nV) : posVn R j i < R.nV := by
  have h1 := nz_pV_le R j
  unfold Ranks.nV at h ⊢
  unfold posVn
  split_ifs <;> omega

def posVf (i : Fin R.nV) : Fin R.nV := ⟨posVn R j i.1, nz_posVn_lt R j i.2⟩

/- English proof (translation)
Introduce `a b h`. Establish `h1 : posVn R j a.1 = posVn R j b.1` using `congrArg Fin.val h`. Establish `h2` using `nz_pV_le R j`. Establish `ha` using `a.2`. Establish `hb` using `b.2`.

Unfold `Ranks.nV at ha hb`. Apply `Fin.ext` to reduce the goal to its premises. Unfold `posVn at h1`. Apply the tactic sequence `split_ifs at h1 <;> omega`.
-/
theorem nz_posVf_inj : Function.Injective (posVf R j) := by
  intro a b h
  have h1 : posVn R j a.1 = posVn R j b.1 := congrArg Fin.val h
  have h2 := nz_pV_le R j
  have ha := a.2
  have hb := b.2
  unfold Ranks.nV at ha hb
  apply Fin.ext
  unfold posVn at h1
  split_ifs at h1 <;> omega

def posV : Equiv.Perm (Fin R.nV) :=
  Equiv.ofBijective (posVf R j) (Finite.injective_iff_bijective.mp (nz_posVf_inj R j))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem nz_posV_val (i : Fin R.nV) : (posV R j i).1 = posVn R j i.1 := rfl

variable {R j}

/- English proof (translation)
Use `R.m_add_three_le_k` as an intermediate fact. Unfold `pV RowPar.pOf Ranks.r`. Use linear arithmetic over natural numbers and integers.
-/
theorem nz_pV_eq (h2 : j ≤ R.m) : pV R j = RowPar.pOf R j := by
  have := R.m_add_three_le_k
  unfold pV RowPar.pOf Ranks.r
  omega

def sV (R : Ranks) (j : ℕ) : ℚ := ((R.k : ℚ) - (R.m : ℚ)) / 2 + (j : ℚ) - 1

/- English proof (translation)
Take `⟨a, ha⟩` from `R.k_even`. Take `⟨b, hb⟩` from `R.m_even`. Unfold `sV`. Rewrite using `[ha, hb]`. Conclude with `⟨(a : ℤ) - b + j - 1, by push_cast; ring⟩`.
-/
theorem nz_sV_int (R : Ranks) (j : ℕ) : ∃ z : ℤ, sV R j = z := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  unfold sV
  rw [ha, hb]
  exact ⟨(a : ℤ) - b + j - 1, by push_cast; ring⟩

/- English proof (translation)
Establish `hp` using `nz_pV_eq h2`. Establish `hle` using `nz_pV_le R j`. Establish `ha` using `a.2`. Unfold `Ranks.nV at ha`. Establish `e : (posV R j a).1 = a.1 - R.r + RowPar.pOf R j`.

Rewrite using `[nz_posV_val]`. Unfold `posVn`. Rewrite using `[if_neg (by omega), if_neg (by omega), hp]`. Unfold `RowPar.lamVQ`. Rewrite using `[e, if_neg (by omega), if_pos (by omega)]`.

Unfold `RowPar.dV sV`. Rewrite using `[RowPar.cast_pOf h1, RowPar.cast_qOf h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem RowPar.nz_lamVQ_pos (S : RowPar R) (h1 : 1 ≤ j) (h2 : j ≤ R.m) (a : Fin R.nV) (h : R.r ≤ a.1) :
    S.lamVQ j (posV R j a) = -S.eAt (j - 1) + sV R j := by
  have hp := nz_pV_eq h2
  have hle := nz_pV_le R j
  have ha := a.2
  unfold Ranks.nV at ha
  have e : (posV R j a).1 = a.1 - R.r + RowPar.pOf R j := by
    rw [nz_posV_val]
    unfold posVn
    rw [if_neg (by omega), if_neg (by omega), hp]
  unfold RowPar.lamVQ
  rw [e, if_neg (by omega), if_pos (by omega)]
  unfold RowPar.dV sV
  rw [RowPar.cast_pOf h1, RowPar.cast_qOf h2]
  ring

end PosV

section WtsV

variable {X : Fields} {Word : Type} {R : Ranks} {W : Wts X Word R} {j : ℕ}

/- English proof (translation)
Rewrite using `[Wts.lamV_eq hW h1 h2 τ (posV R j a)]`. Conclude with `RowPar.nz_lamVQ_pos _ h1 h2 a h`.
-/
theorem nz_lamV_val (hW : W.Ok) (h1 : 1 ≤ j) (h2 : j ≤ R.m) (τ : X.Tau) (a : Fin R.nV) (h : R.r ≤ a.1) :
    ((W.lamV j τ).w (posV R j a) : ℚ) = -(W.row τ).eAt (j - 1) + sV R j := by
  rw [Wts.lamV_eq hW h1 h2 τ (posV R j a)]
  exact RowPar.nz_lamVQ_pos _ h1 h2 a h

/- English proof (translation)
Establish `h3 : ((W.lamV j τ).w (posV R j a) : ℚ) = ((W.lamV j τ).w (posV R j b) : ℚ)`. Rewrite using `[nz_lamV_val hW h1 h2 τ a ha, nz_lamV_val hW h1 h2 τ b hb]`. Conclude with `h3` after adjusting the coercions.
-/
theorem nz_lamV_const (hW : W.Ok) (h1 : 1 ≤ j) (h2 : j ≤ R.m) (τ : X.Tau) (a b : Fin R.nV) (ha : R.r ≤ a.1)
    (hb : R.r ≤ b.1) : (W.lamV j τ).w (posV R j a) = (W.lamV j τ).w (posV R j b) := by
  have h3 : ((W.lamV j τ).w (posV R j a) : ℚ) = ((W.lamV j τ).w (posV R j b) : ℚ) := by
    rw [nz_lamV_val hW h1 h2 τ a ha, nz_lamV_val hW h1 h2 τ b hb]
  exact_mod_cast h3

/- English proof (translation)
Establish `hB : j - 1 < R.m` using `by omega`. Take `⟨z, hz⟩` from `he ⟨j - 1, hB⟩`. Take `⟨y, hy⟩` from `nz_sV_int R j`. Take `⟨c, hc⟩` from `hf`. Establish `h3 : ((∑ τ, (W.lamV j τ).w (posV R j a) : ℤ) : ℚ) = ((2 * (-z + (c : ℤ) * y) : ℤ) : ℚ)`.

Use `push_cast`. Rewrite using `[Finset.sum_congr rfl fun τ _ => nz_lamV_val hW h1 h2 τ a ha, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ]`. Establish `h4 : ∑ τ, (W.row τ).eAt (j - 1) = 2 * (z : ℚ)`. Rewrite using `[← hz]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Unfold `RowPar.eAt`. Rewrite using `[dif_pos hB]`. Establish `h5 : Fintype.card X.Tau = c + c` using `hc`. Rewrite using `[h4, h5, hy, nsmul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `h6 : ∑ τ, (W.lamV j τ).w (posV R j a) = 2 * (-z + (c : ℤ) * y)` using `by exact_mod_cast h3`. Rewrite using `[h6]`. Conclude with `even_two_mul _`.
-/
theorem nz_lamV_even (hW : W.Ok) (hf : Even X.f) (he : ∀ j : Fin R.m, ∃ z : ℤ, ∑ τ, (W.row τ).e j = 2 * (z : ℚ))
    (h1 : 1 ≤ j) (h2 : j ≤ R.m) (a : Fin R.nV) (ha : R.r ≤ a.1) : Even (∑ τ, (W.lamV j τ).w (posV R j a)) := by
  have hB : j - 1 < R.m := by omega
  obtain ⟨z, hz⟩ := he ⟨j - 1, hB⟩
  obtain ⟨y, hy⟩ := nz_sV_int R j
  obtain ⟨c, hc⟩ := hf
  have h3 : ((∑ τ, (W.lamV j τ).w (posV R j a) : ℤ) : ℚ) = ((2 * (-z + (c : ℤ) * y) : ℤ) : ℚ) := by
    push_cast
    rw [Finset.sum_congr rfl fun τ _ => nz_lamV_val hW h1 h2 τ a ha, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_const, Finset.card_univ]
    have h4 : ∑ τ, (W.row τ).eAt (j - 1) = 2 * (z : ℚ) := by
      rw [← hz]
      refine Finset.sum_congr rfl fun τ _ => ?_
      unfold RowPar.eAt
      rw [dif_pos hB]
    have h5 : Fintype.card X.Tau = c + c := hc
    rw [h4, h5, hy, nsmul_eq_mul]
    push_cast
    ring
  have h6 : ∑ τ, (W.lamV j τ).w (posV R j a) = 2 * (-z + (c : ℤ) * y) := by exact_mod_cast h3
  rw [h6]
  exact even_two_mul _

end WtsV

end Formalism.L2.Col
