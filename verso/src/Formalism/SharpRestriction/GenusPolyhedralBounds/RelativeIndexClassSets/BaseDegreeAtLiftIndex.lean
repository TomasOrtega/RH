import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.SubsingletonQuotientOfIdealEqTop

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem even_sub_of {a b : ℕ} (ha : Even a) (hb : Even b) : Even (a - b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x - y, by omega⟩

def sA (p l g : ℕ) : ℝ := ∑ i : Fin p, ((l + (p - 1 - i.1) * g : ℕ) : ℝ)

/- English proof (translation)
Replace the relevant objects with their definitions. Chain the equalities or inequalities of the calculation. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sA_le (p l g : ℕ) : sA p l g ≤ p * ((l : ℝ) + p * g) := by
  unfold sA
  calc ∑ i : Fin p, (((l + (p - 1 - i.1) * g : ℕ)) : ℝ)
      ≤ ∑ _i : Fin p, ((l : ℝ) + p * g) := by
        apply Finset.sum_le_sum
        intro i _
        have h1 : (p - 1 - i.1) * g ≤ p * g := Nat.mul_le_mul_right g (by omega)
        have h2 : l + (p - 1 - i.1) * g ≤ l + p * g := by omega
        exact_mod_cast h2
    _ = p * ((l : ℝ) + p * g) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/- English proof (translation)
Replace the relevant objects with their definitions. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem sA_ge (p l g : ℕ) : (p : ℝ) * l ≤ sA p l g := by
  unfold sA
  calc (p : ℝ) * l = ∑ _i : Fin p, (l : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ i : Fin p, (((l + (p - 1 - i.1) * g : ℕ)) : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact_mod_cast Nat.le_add_right l _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sA_nonneg (p l g : ℕ) : 0 ≤ sA p l g := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem sA_lin {p l1 g1 l2 g2 : ℕ} {a1 a2 e : ℝ}
    (h : ∀ c : ℕ, c < p → a1 * ((l1 + c * g1 : ℕ) : ℝ) ≤ a2 * ((l2 + c * g2 : ℕ) : ℝ) + e) :
    a1 * sA p l1 g1 ≤ a2 * sA p l2 g2 + p * e := by
  unfold sA
  rw [Finset.mul_sum, Finset.mul_sum]
  have h2 : ∑ i : Fin p, (a2 * ((l2 + (p - 1 - i.1) * g2 : ℕ) : ℝ) + e) =
      ∑ i : Fin p, a2 * ((l2 + (p - 1 - i.1) * g2 : ℕ) : ℝ) + p * e := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← h2]
  exact Finset.sum_le_sum (fun i _ => h _ (by have := i.isLt; omega))

def apW (D : D7) (j l g n : ℕ) (hn : Even n) : WeightFamilies.Wt D j where
  aP _ i := l + ((D.R.sigW j).1 - 1 - i.1) * g
  aM _ _ := 0
  aPlus_antitone _ a b h := by
    have h' : a.1 ≤ b.1 := h
    exact Nat.add_le_add_left (Nat.mul_le_mul_right g (by omega)) l
  aM_anti _ _ _ _ := le_rfl
  n := n
  n_even := hn

variable {D : D7}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem apW_aP (j l g n : ℕ) (hn : Even n) (τ : D.what₂.Tau) (i : Fin (D.R.sigW j).1) :
    (apW D j l g n hn).aP τ i = l + ((D.R.sigW j).1 - 1 - i.1) * g := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem apW_aM (j l g n : ℕ) (hn : Even n) (τ : D.what₂.Tau) (i : Fin (D.R.sigW j).2) :
    (apW D j l g n hn).aM τ i = 0 := rfl

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem gapZ_apW (j l g n : ℕ) (hn : Even n) (τ : D.what₂.Tau) (i : Fin (D.R.sigW j).1) :
    gapZ ((apW D j l g n hn).aP τ) i = if i.1 + 1 < (D.R.sigW j).1 then (g : ℤ) else l := by
  have hi := i.isLt
  unfold gapZ
  split_ifs with h
  · simp only [apW_aP, Fin.val_mk]
    have e1 : (D.R.sigW j).1 - 1 - i.1 = ((D.R.sigW j).1 - 1 - (i.1 + 1)) + 1 := by omega
    rw [e1]
    push_cast
    ring
  · simp only [apW_aP]
    have e1 : (D.R.sigW j).1 - 1 - i.1 = 0 := by omega
    rw [e1]
    simp

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.
-/
theorem sum_apW (j l g n : ℕ) (hn : Even n) :
    (∑ τ, ((∑ i, ((apW D j l g n hn).aP τ i : ℝ)) + ∑ i, ((apW D j l g n hn).aM τ i : ℝ))) =
      D.R.f * sA (D.R.sigW j).1 l g := by
  have hin : ∀ τ : D.what₂.Tau, (∑ i, ((apW D j l g n hn).aP τ i : ℝ)) + ∑ i, ((apW D j l g n hn).aM τ i : ℝ) =
      sA (D.R.sigW j).1 l g := by
    intro τ
    simp only [apW_aM, Nat.cast_zero, Finset.sum_const_zero, add_zero]
    rfl
  rw [Finset.sum_congr rfl (fun τ _ => hin τ), Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Move the embeddings inside the algebraic operations. A detailed English derivation is pending.
-/
theorem DF_le_size {j : ℕ} (w : WeightFamilies.Wt D j) : (DF w : ℝ) ≤ w.size := by
  have key : ∀ (a b : ℝ), 0 ≤ b → a ≤ a + b + 1 := fun a b hb => by linarith
  unfold DF degP WeightFamilies.Wt.size
  push_cast
  exact key _ _ (by positivity)

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem finM_elim (i : Fin (D.R.sigW D.R.m).2) : False := by
  have h := i.isLt
  simp [Ranks.sigW] at h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sigW_m_fst (D : D7) : (D.R.sigW D.R.m).1 = D.R.r := rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sigW_m_snd (D : D7) : (D.R.sigW D.R.m).2 = 0 := by
  simp [Ranks.sigW]

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem r_pos (D : D7) : 0 < D.R.r := by
  unfold Ranks.r
  have := D.R.two_le_m
  omega

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem f_pos (D : D7) : 0 < D.R.f := by
  unfold Ranks.f Ranks.n
  have := D.R.m_le_f
  have := D.R.two_le_m
  omega

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem dimY_m (D : D7) : WeightFamilies.dimY D D.R.m = D.R.f * D.R.r.choose 2 := by
  rw [Nat.choose_two_right]
  simp [WeightFamilies.dimY, Ranks.sigW, Ranks.r]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem baseDegree_at_lift_index (D : D7) : n0 D D.R.m = D.R.r + 2 * g0 D := by
  simp [n0, Ranks.sigW]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions.
-/
theorem size_apW_m (l g n : ℕ) (hn : Even n) :
    (apW D D.R.m l g n hn).size = D.R.f * sA D.R.r l g + (D.R.f : ℝ) * D.R.r * n + 1 := by
  unfold WeightFamilies.Wt.size
  rw [sum_apW, sigW_m_fst, sigW_m_snd]
  have hn' : (apW D D.R.m l g n hn).n = n := rfl
  rw [hn']
  norm_num

/- English proof (translation)
Replace the relevant objects with their definitions. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem DF_apW_m (l g n : ℕ) (hn : Even n) : (DF (apW D D.R.m l g n hn) : ℝ) = D.R.f * sA D.R.r l g := by
  unfold DF degP
  push_cast
  rw [sum_apW]
  rfl

abbrev Dm (D : D7) : ℕ := WeightFamilies.dimY D D.R.m

structure RunN (D : D7) where
  T : ℕ
  nW : ℕ
  nP : ℕ
  Q0 : ℕ
  T_pos : 0 < T
  nW_even : Even nW
  even_nP₂ : Even nP
  split : D.R.nV = nP + T * nW
  nP_le_nW : nP ≤ nW
  hQ0 : (WeightFamilies.dimY D D.R.m + 2) * nW + 2 * D.R.r ≤ 2 * Q0

namespace RunN

variable (X : RunN D)

def Tq : ℕ := Tp D D.R.m X.T

def Q : ℕ := X.Tq + 2 * D.R.r

def kl : ℕ := (Dm D + 2) * X.nW + 2 * D.R.r + X.Tq * X.Q0

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem nV_even (X : RunN D) : Even D.R.nV := by
  rw [X.split]
  exact X.even_nP₂.add (X.nW_even.mul_left _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Tq_eq : X.Tq = X.T + Dm D + 2 := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers.
-/
theorem two_le_Tq : 2 ≤ X.Tq := by
  rw [X.Tq_eq]
  omega

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem two_le_Q : 2 ≤ X.Q := by
  unfold Q
  have := X.two_le_Tq
  omega

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem two_le_TqQ : 2 ≤ X.Tq * X.Q := by
  have h1 := X.two_le_Tq
  have h2 := X.two_le_Q
  nlinarith

/- English proof (translation)
Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem two_le_DQ : 2 ≤ (Dm D + 2) * X.Q := by
  have h2 := X.two_le_Q
  nlinarith

def ka : WeightFamilies.Wt D D.R.m := apW D D.R.m X.kl (X.Tq * X.Q - 2) D.R.nV X.nV_even

def wL : WeightFamilies.Wt D D.R.m := apW D D.R.m X.Q0 X.Q X.nW X.nW_even

def wF : WeightFamilies.Wt D D.R.m :=
  apW D D.R.m ((Dm D + 2) * X.nW + 2 * D.R.r + (Dm D + 2) * X.Q0) ((Dm D + 2) * X.Q - 2) X.nP X.even_nP₂

def w2 : WeightFamilies.Wt D D.R.m :=
  apW D D.R.m (2 * X.Q0 - ((Dm D + 2) * X.nW + 2 * D.R.r)) (2 * X.Q + 2) ((Dm D + 4) * X.nW - X.nP)
    (even_sub_of (X.nW_even.mul_left _) X.even_nP₂)

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Use linear arithmetic over natural numbers and integers.
-/
theorem Tq_posZ : (0 : ℤ) < (Tp D D.R.m X.T : ℤ) := by
  have := X.two_le_Tq
  unfold Tq at this
  omega

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Replace the relevant objects with their definitions. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isL : IsL D X.ka X.wL X.T X.nW := by
  refine ⟨rfl, fun τ i => ?_, fun τ i => (finM_elim i).elim⟩
  have hT : (0 : ℤ) < (X.Tq : ℤ) := X.Tq_posZ
  unfold RunN.wL
  rw [gapZ_apW]
  split_ifs with h
  · unfold RunN.ka
    rw [gapZ_apW, if_pos h]
    have e1 := X.two_le_TqQ
    have e : ((X.Tq * X.Q - 2 : ℕ) : ℤ) + 2 = (X.Tq : ℤ) * X.Q := by
      rw [Nat.cast_sub e1]
      push_cast
      ring
    rw [e]
    exact (Int.mul_fdiv_cancel_left _ hT.ne').symm
  · have hl : i.1 + 1 = (D.R.sigW D.R.m).1 := by
      have := i.isLt
      omega
    have hk : X.ka.aP τ i = X.kl := by
      unfold RunN.ka
      have e0 : (D.R.sigW D.R.m).1 - 1 - i.1 = 0 := by omega
      rw [apW_aP, e0, zero_mul, add_zero]
    rw [hk]
    have e : (X.kl : ℤ) - ((WeightFamilies.dimY D D.R.m : ℤ) + 2) * X.nW - 2 * D.R.r = (X.Tq : ℤ) * X.Q0 := by
      unfold RunN.kl Dm
      push_cast
      ring
    rw [e]
    exact (Int.mul_fdiv_cancel_left _ hT.ne').symm

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Replace the relevant objects with their definitions. Move the embeddings inside the algebraic operations.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isF : IsF' X.ka X.wL X.wF X.T X.nP := by
  refine ⟨rfl, fun τ i => ?_, fun τ i => (finM_elim i).elim⟩
  simp only [RunN.wF, RunN.ka, RunN.wL, apW_aP]
  have e1 := X.two_le_TqQ
  have e2 := X.two_le_DQ
  have hT : (X.Tq : ℤ) = X.T + Dm D + 2 := by
    rw [X.Tq_eq]
    push_cast
    ring
  unfold RunN.kl
  push_cast [Nat.cast_sub e1, Nat.cast_sub e2]
  rw [hT]
  ring

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Replace the chosen expression with an arbitrary variable. Use linear arithmetic over natural numbers and integers.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem run_isSecondWeight : IsG2 X.wL X.wF X.w2 := by
  refine ⟨?_, fun τ i => ?_, fun τ i => (finM_elim i).elim⟩
  · show ((Dm D + 4) * X.nW - X.nP) + X.nP = (Dm D + 4) * X.nW
    have h1 := X.nP_le_nW
    have h2 : X.nW ≤ (Dm D + 4) * X.nW := by nlinarith
    generalize (Dm D + 4) * X.nW = M at *
    omega
  · simp only [RunN.w2, RunN.wF, RunN.wL, apW_aP]
    have h1 : (Dm D + 2) * X.nW + 2 * D.R.r ≤ 2 * X.Q0 := X.hQ0
    have h2 := X.two_le_DQ
    zify [h1, h2]
    simp only [Dm]
    ring

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Replace the chosen expression with an arbitrary variable. Use linear arithmetic over natural numbers and integers.
-/
theorem gapP (τ : D.what₂.Tau) (i : Fin (D.R.sigW D.R.m).1) (h : i.1 + 1 < (D.R.sigW D.R.m).1) :
    ((Tp D D.R.m X.T * (Tp D D.R.m X.T + 2 * D.R.r) : ℕ) : ℤ) ≤ gapZ (X.ka.aP τ) i + 2 := by
  unfold RunN.ka
  rw [gapZ_apW, if_pos h]
  have h2 := X.two_le_TqQ
  have e : Tp D D.R.m X.T * (Tp D D.R.m X.T + 2 * D.R.r) = X.Tq * X.Q := rfl
  rw [e]
  generalize X.Tq * X.Q = N at h2 ⊢
  omega

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gapM (τ : D.what₂.Tau) (i : Fin (D.R.sigW D.R.m).2) (_h : i.1 + 1 < (D.R.sigW D.R.m).2) :
    ((Tp D D.R.m X.T * (Tp D D.R.m X.T + 2 * D.R.r) : ℕ) : ℤ) ≤ gapZ (X.ka.aM τ) i + 2 := (finM_elim i).elim

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem ka_last (τ : D.what₂.Tau) (i : Fin (D.R.sigW D.R.m).1) (h : i.1 + 1 = (D.R.sigW D.R.m).1) :
    X.ka.aP τ i = X.kl := by
  unfold RunN.ka
  have e : (D.R.sigW D.R.m).1 - 1 - i.1 = 0 := by omega
  rw [apW_aP, e, zero_mul, add_zero]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lastM (c : ℝ) (τ : D.what₂.Tau) (i : Fin (D.R.sigW D.R.m).2) (_h : i.1 + 1 = (D.R.sigW D.R.m).2) :
    c ≤ (X.ka.aM τ i : ℝ) := (finM_elim i).elim

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem ncAt_ka (τ : D.what₂.Tau) : ncAt X.ka τ = (X.kl : ℤ) + D.R.t + 1 := by
  have h0 : 0 < (D.R.sigW D.R.m).1 := by
    rw [sigW_m_fst]
    exact r_pos D
  have h1 : ¬ 0 < (D.R.sigW D.R.m).2 := by
    rw [sigW_m_snd]
    omega
  have hn : X.ka.n = D.R.nV := rfl
  unfold ncAt
  rw [dif_pos h0, dif_neg h1,
    X.ka_last τ ⟨(D.R.sigW D.R.m).1 - 1, by omega⟩ (by show (D.R.sigW D.R.m).1 - 1 + 1 = _; omega),
    hn, sigW_m_fst, sigW_m_snd]
  unfold Ranks.nV
  push_cast
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Tq_cast : (X.Tq : ℝ) = (X.T : ℝ) + Dm D + 2 := by
  rw [X.Tq_eq]
  push_cast
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Q_cast : (X.Q : ℝ) = (X.Tq : ℝ) + 2 * D.R.r := by
  unfold Q
  push_cast
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kl_cast : (X.kl : ℝ) = ((Dm D : ℝ) + 2) * X.nW + 2 * D.R.r + (X.Tq : ℝ) * X.Q0 := by
  unfold kl
  push_cast
  ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ka_n : X.ka.n = D.R.nV := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem wL_n : X.wL.n = X.nW := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem wF_n : X.wF.n = X.nP := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gk_cast : ((X.Tq * X.Q - 2 : ℕ) : ℝ) = (X.Tq : ℝ) * X.Q - 2 := by
  rw [Nat.cast_sub X.two_le_TqQ]
  push_cast
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gF_cast : (((Dm D + 2) * X.Q - 2 : ℕ) : ℝ) = ((Dm D : ℝ) + 2) * X.Q - 2 := by
  rw [Nat.cast_sub X.two_le_DQ]
  push_cast
  ring

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DQ_cast_ge : (2 : ℝ) ≤ ((Dm D : ℝ) + 2) * X.Q := by
  exact_mod_cast X.two_le_DQ

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ka_size : X.ka.size = D.R.f * sA D.R.r X.kl (X.Tq * X.Q - 2) + (D.R.f : ℝ) * D.R.r * D.R.nV + 1 := size_apW_m _ _ _ _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wL_size : X.wL.size = D.R.f * sA D.R.r X.Q0 X.Q + (D.R.f : ℝ) * D.R.r * X.nW + 1 := size_apW_m _ _ _ _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wF_size : X.wF.size = D.R.f * sA D.R.r ((Dm D + 2) * X.nW + 2 * D.R.r + (Dm D + 2) * X.Q0) ((Dm D + 2) * X.Q - 2) +
    (D.R.f : ℝ) * D.R.r * X.nP + 1 := size_apW_m _ _ _ _

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ka_size_le : X.ka.size ≤
    (D.R.f : ℝ) * D.R.r * ((X.kl : ℝ) + D.R.r * ((X.Tq : ℝ) * X.Q)) + (D.R.f : ℝ) * D.R.r * D.R.nV + 1 := by
  rw [X.ka_size]
  have h1 := sA_le D.R.r X.kl (X.Tq * X.Q - 2)
  have hg : ((X.Tq * X.Q - 2 : ℕ) : ℝ) ≤ (X.Tq : ℝ) * X.Q := by rw [X.gk_cast]; linarith
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hr : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have h4 : (D.R.r : ℝ) * (D.R.r * ((X.Tq * X.Q - 2 : ℕ) : ℝ)) ≤ D.R.r * (D.R.r * ((X.Tq : ℝ) * X.Q)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg hr) hr
  have h2 : sA D.R.r X.kl (X.Tq * X.Q - 2) ≤ D.R.r * ((X.kl : ℝ) + D.R.r * ((X.Tq : ℝ) * X.Q)) := by
    linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hf
  linarith

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ka_size_ge : (X.kl : ℝ) ≤ X.ka.size := by
  rw [X.ka_size]
  have h1 := sA_ge D.R.r X.kl (X.Tq * X.Q - 2)
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast Nat.succ_le_of_lt (f_pos D)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast Nat.succ_le_of_lt (r_pos D)
  have hk : (0 : ℝ) ≤ X.kl := Nat.cast_nonneg _
  have a1 : (1 : ℝ) * X.kl ≤ D.R.r * X.kl := mul_le_mul_of_nonneg_right hr hk
  have a2 : (1 : ℝ) * sA D.R.r X.kl (X.Tq * X.Q - 2) ≤ D.R.f * sA D.R.r X.kl (X.Tq * X.Q - 2) :=
    mul_le_mul_of_nonneg_right hf (sA_nonneg _ _ _)
  have a3 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * D.R.nV := by positivity
  linarith

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem wL_size_le : X.wL.size ≤
    (D.R.f : ℝ) * D.R.r * ((X.Q0 : ℝ) + D.R.r * X.Q) + (D.R.f : ℝ) * D.R.r * X.nW + 1 := by
  rw [X.wL_size]
  have h1 := sA_le D.R.r X.Q0 X.Q
  have h3 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg D.R.f : (0 : ℝ) ≤ D.R.f)
  linarith

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem DF_wL_le : (DF X.wL : ℝ) ≤ (D.R.f : ℝ) * D.R.r * ((X.Q0 : ℝ) + D.R.r * X.Q) := by
  have h := DF_apW_m (D := D) X.Q0 X.Q X.nW X.nW_even
  have h1 := sA_le D.R.r X.Q0 X.Q
  have h3 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg D.R.f : (0 : ℝ) ≤ D.R.f)
  unfold RunN.wL
  rw [h]
  linarith

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem T_wL_le : (X.T : ℝ) * X.wL.size ≤ X.ka.size + X.T := by
  rw [X.ka_size, X.wL_size]
  have hlin : (X.T : ℝ) * sA D.R.r X.Q0 X.Q ≤ 1 * sA D.R.r X.kl (X.Tq * X.Q - 2) + D.R.r * 0 := by
    apply sA_lin
    intro c _
    simp only [Nat.cast_add, Nat.cast_mul]
    rw [X.gk_cast, X.kl_cast, X.Tq_cast]
    have hDQ := X.DQ_cast_ge
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    have h1 : (0 : ℝ) ≤ (c : ℝ) * (((Dm D : ℝ) + 2) * X.Q - 2) := mul_nonneg hc (by linarith)
    have h2 : (0 : ℝ) ≤ ((Dm D : ℝ) + 2) * X.nW := by positivity
    have h3 : (0 : ℝ) ≤ ((Dm D : ℝ) + 2) * X.Q0 := by positivity
    have h4 : (0 : ℝ) ≤ (D.R.r : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hnV : (D.R.nV : ℝ) = X.nP + X.T * X.nW := by exact_mod_cast X.split
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have k1 := mul_le_mul_of_nonneg_left hlin hf
  have k2 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * X.nP := by positivity
  rw [hnV]
  nlinarith

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem wF_size_le : X.wF.size ≤
    ((Dm D : ℝ) + 2) * X.wL.size + 2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 + (D.R.f : ℝ) * D.R.r * X.nP + 1 := by
  rw [X.wF_size, X.wL_size]
  have hlin : 1 * sA D.R.r ((Dm D + 2) * X.nW + 2 * D.R.r + (Dm D + 2) * X.Q0) ((Dm D + 2) * X.Q - 2) ≤
      ((Dm D : ℝ) + 2) * sA D.R.r X.Q0 X.Q + D.R.r * (((Dm D : ℝ) + 2) * X.nW + 2 * D.R.r) := by
    apply sA_lin
    intro c _
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [X.gF_cast]
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    nlinarith
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have k1 := mul_le_mul_of_nonneg_left hlin hf
  have k2 : (0 : ℝ) ≤ (Dm D : ℝ) + 2 := by positivity
  nlinarith

end RunN

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

end
