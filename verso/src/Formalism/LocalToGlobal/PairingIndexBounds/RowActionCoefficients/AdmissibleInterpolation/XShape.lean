import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.NumericalIdentityScalar
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.EvalIdFrameRowAct

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

namespace FrameShapeLemmas

/- English proof (translation)
Substitute `hm` using the available equality. Establish `h1` using `hlam t`. Establish `h2` using `hlam (Fin.last m₀)`. Establish `h3 : lam (Fin.last m₀) ≤ lam t` using `hanti (Fin.le_last t)`. Establish `h4` using `hnn (t.val + 1)`.

Establish `h5` using `hnn (m₀ + 1)`. Rewrite `h2` using `[Fin.val_last]`. Unfold `nuOf`. Rewrite using `[Fin.cast_eq_self]`. Use linear arithmetic over natural numbers and integers.
-/
theorem shape_even (m₀ n : ℕ) (hm : m₀ + 1 = n) (lam : Fin (m₀ + 1) → ℤ) (hanti : Antitone lam) (ν : ℕ → ℤ) (w : ℤ)
    (hlam : ∀ i : Fin (m₀ + 1), ν (i.val + 1) = lam i + w) (hnn : ∀ i, 0 ≤ ν i) (t : Fin n) :
    nuOf lam (Fin.cast hm.symm t) = (ν (t.val + 1)).toNat - (ν n).toNat := by
  subst hm
  have h1 := hlam t
  have h2 := hlam (Fin.last m₀)
  have h3 : lam (Fin.last m₀) ≤ lam t := hanti (Fin.le_last t)
  have h4 := hnn (t.val + 1)
  have h5 := hnn (m₀ + 1)
  rw [Fin.val_last] at h2
  unfold nuOf
  rw [Fin.cast_eq_self]
  omega

/- English proof (translation)
Substitute `hm` using the available equality. Establish `h1` using `hlam t.rev`. Establish `h2` using `hlam 0`. Establish `h3 : lam t.rev ≤ lam 0` using `hanti (Fin.zero_le _)`. Establish `h4` using `hnn (t.rev.val + 1)`.

Establish `h5` using `hnn 1`. Rewrite `h2` using `[Fin.val_zero, zero_add]`. Unfold `nuOf`. Rewrite using `[Fin.cast_eq_self]`. Use `beta_reduce`.

Rewrite using `[Fin.rev_last]`. Use linear arithmetic over natural numbers and integers.
-/
theorem shape_odd (m₀ n : ℕ) (hm : m₀ + 1 = n) (lam : Fin (m₀ + 1) → ℤ) (hanti : Antitone lam) (ν : ℕ → ℤ) (w : ℤ)
    (hlam : ∀ i : Fin (m₀ + 1), ν (i.val + 1) = lam i + w) (hnn : ∀ i, 0 ≤ ν i) (t : Fin n) :
    nuOf (fun i => -lam i.rev) (Fin.cast hm.symm t) = (ν 1).toNat - (ν (t.rev.val + 1)).toNat := by
  subst hm
  have h1 := hlam t.rev
  have h2 := hlam 0
  have h3 : lam t.rev ≤ lam 0 := hanti (Fin.zero_le _)
  have h4 := hnn (t.rev.val + 1)
  have h5 := hnn 1
  rw [Fin.val_zero, zero_add] at h2
  unfold nuOf
  rw [Fin.cast_eq_self]
  beta_reduce
  rw [Fin.rev_last]
  omega

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

/- English proof (translation)
Unfold `liftWt`. Use `split_ifs with h`. Conclude with `nuv_low X l v s i.val h`. Use `nuv_high X l v s i.val h ?_` and prove the remaining obligations. Use `i.isLt` as an intermediate fact.

Establish `h2 : (j + 1) * (X.Fl.t + 1) ≤ (l + 1) * (X.Fl.t + 1)` using `Nat.mul_le_mul_right _ hl`. Unfold `NN`. Use `show i.val + 1 ≤ X.G.P.m + 1 + (l + 1) * (X.Fl.t + 1)`. Use linear arithmetic over natural numbers and integers.
-/
theorem hlamS (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (l : ℕ) (hl : j + 1 ≤ l + 1) (i : Fin (X.G.P.m + (j + 1) * (X.Fl.t + 1) + 1)) :
    X.nuv v (l + 1) s (i.val + 1) =
      liftWt X.Fl.t X.G.P.m (X.G.P.lam0 v s) (fun i => X.Fl.w v i s) (j + 1) i + X.Fl.w v (l + 1) s := by
  unfold liftWt
  split_ifs with h
  · exact nuv_low X l v s i.val h
  · refine nuv_high X l v s i.val h ?_
    have := i.isLt
    have h2 : (j + 1) * (X.Fl.t + 1) ≤ (l + 1) * (X.Fl.t + 1) := Nat.mul_le_mul_right _ hl
    unfold NN
    show i.val + 1 ≤ X.G.P.m + 1 + (l + 1) * (X.Fl.t + 1)
    omega

/- English proof (translation)
Rewrite using `[Nat.not_even_iff]`. Conclude with `h`.
-/
theorem not_even_of_odd {n' : ℕ} {s : Fin n'} (h : IsOddPos s) : ¬ Even s.val := by
  rw [Nat.not_even_iff]; exact h

/- English proof (translation)
The claim follows from `Nat.even_iff.2 (by unfold IsOddPos at h; omega)`.
-/
theorem even_of_not_odd {n' : ℕ} {s : Fin n'} (h : ¬ IsOddPos s) : Even s.val :=
  Nat.even_iff.2 (by unfold IsOddPos at h; omega)

/- English proof (translation)
Use function extensionality and compare the values at `t`. Unfold `nuS muX cX eX`. Consider the cases of `j with`. Consider the case `zero => show nuOf (lamAt (X.G.P.lam0 b.1) b.2) (Fin.cast (rankJ X 0).symm t) = _`. Unfold `lamAt`.

Use `split_ifs with h1 h2 h2`. Conclude with `absurd h1 (not_even_of_odd h2)`. Conclude with `shape_even _ _ (rankJ X 0) _ (X.G.P.dom b.1 b.2) (X.nuv b.1 1 b.2) _ (fun i => nuv_low X 0 b.1 b.2 i.val i.isLt) (nuv_nonneg X b.1 0 b.2) t`. Conclude with `shape_odd _ _ (rankJ X 0) _ (X.G.P.dom b.1 b.2) (X.nuv b.1 1 b.2) _ (fun i => nuv_low X 0 b.1 b.2 i.val i.isLt) (nuv_nonneg X b.1 0 b.2) t`. Conclude with `absurd (even_of_not_odd h2) h1`.

Consider the case `succ j => show nuOf (lamAt ((X.Fl.Pj (j + 1)).lam0 b.1) b.2) (Fin.cast (rankJ X (j + 1)).symm t) = _`. Unfold `lamAt`. Use `split_ifs with h1 h2 h2`. Conclude with `absurd h1 (not_even_of_odd h2)`. Conclude with `shape_even _ _ (rankJ X (j + 1)) _ (X.Fl.domJ (j + 1) b.1 b.2) (X.nuv b.1 (j + 1 + 1) b.2) _ (hlamS X j b.1 b.2 (j + 1) (by omega)) (nuv_nonneg X b.1 (j + 1) b.2) t`.

Conclude with `shape_odd _ _ (rankJ X (j + 1)) _ (X.Fl.domJ (j + 1) b.1 b.2) (X.nuv b.1 (j + 1 + 1) b.2) _ (hlamS X j b.1 b.2 (j + 1) (by omega)) (nuv_nonneg X b.1 (j + 1) b.2) t`. Conclude with `absurd (even_of_not_odd h2) h1`.
-/
theorem c1 (j : ℕ) (b : BX X) : nuM X j b = nuS X j b := by
  funext t
  unfold nuS muX cX eX
  cases j with
  | zero =>
    show nuOf (lamAt (X.G.P.lam0 b.1) b.2) (Fin.cast (rankJ X 0).symm t) = _
    unfold lamAt
    split_ifs with h1 h2 h2
    · exact absurd h1 (not_even_of_odd h2)
    · exact shape_even _ _ (rankJ X 0) _ (X.G.P.dom b.1 b.2) (X.nuv b.1 1 b.2) _ (fun i => nuv_low X 0 b.1 b.2 i.val i.isLt)
        (nuv_nonneg X b.1 0 b.2) t
    · exact shape_odd _ _ (rankJ X 0) _ (X.G.P.dom b.1 b.2) (X.nuv b.1 1 b.2) _ (fun i => nuv_low X 0 b.1 b.2 i.val i.isLt)
        (nuv_nonneg X b.1 0 b.2) t
    · exact absurd (even_of_not_odd h2) h1
  | succ j =>
    show nuOf (lamAt ((X.Fl.Pj (j + 1)).lam0 b.1) b.2) (Fin.cast (rankJ X (j + 1)).symm t) = _
    unfold lamAt
    split_ifs with h1 h2 h2
    · exact absurd h1 (not_even_of_odd h2)
    · exact shape_even _ _ (rankJ X (j + 1)) _ (X.Fl.domJ (j + 1) b.1 b.2) (X.nuv b.1 (j + 1 + 1) b.2) _
        (hlamS X j b.1 b.2 (j + 1) (by omega)) (nuv_nonneg X b.1 (j + 1) b.2) t
    · exact shape_odd _ _ (rankJ X (j + 1)) _ (X.Fl.domJ (j + 1) b.1 b.2) (X.nuv b.1 (j + 1 + 1) b.2) _
        (hlamS X j b.1 b.2 (j + 1) (by omega)) (nuv_nonneg X b.1 (j + 1) b.2) t
    · exact absurd (even_of_not_odd h2) h1

/- English proof (translation)
Apply `nuv_zero X v j s` to reduce the goal to its premises. Unfold `NN`. Establish `: j * (X.t + 1) < (j + 1) * (X.t + 1)` using `by nlinarith`. Use linear arithmetic over natural numbers and integers.
-/
theorem nuv_top (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) : X.nuv v (j + 1) s (NN X.G.P.m X.t (j + 1)) = 0 := by
  apply nuv_zero X v j s
  unfold NN
  have : j * (X.t + 1) < (j + 1) * (X.t + 1) := by nlinarith
  omega

/- English proof (translation)
Use function extensionality and compare the values at `t`. Unfold `nuT muX cX`. Use `show nuOf (lamAt ((X.Fl.Pj (j + 1)).lam0 b.1) b.2) (Fin.cast (rankJ X (j + 1)).symm t) = _`. Unfold `lamAt`. Use `split_ifs with h1 h2 h2`.

Conclude with `absurd h1 (not_even_of_odd h2)`. Use `shape_even _ _ (rankJ X (j + 1)) _ (X.Fl.domJ (j + 1) b.1 b.2) (X.nuv b.1 (j + 1) b.2) _ (hlamS X j b.1 b.2 j le_rfl) (nuv_nonneg X b.1 j b.2) t` as an intermediate fact. Rewrite `this` using `[nuv_top X j b.1 b.2]`. Use `this.trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.

Conclude with `shape_odd _ _ (rankJ X (j + 1)) _ (X.Fl.domJ (j + 1) b.1 b.2) (X.nuv b.1 (j + 1) b.2) _ (hlamS X j b.1 b.2 j le_rfl) (nuv_nonneg X b.1 j b.2) t`. Conclude with `absurd (even_of_not_odd h2) h1`.
-/
theorem c2 (j : ℕ) (b : BX X) : nuM X (j + 1) b = nuT X j b := by
  funext t
  unfold nuT muX cX
  show nuOf (lamAt ((X.Fl.Pj (j + 1)).lam0 b.1) b.2) (Fin.cast (rankJ X (j + 1)).symm t) = _
  unfold lamAt
  split_ifs with h1 h2 h2
  · exact absurd h1 (not_even_of_odd h2)
  · have := shape_even _ _ (rankJ X (j + 1)) _ (X.Fl.domJ (j + 1) b.1 b.2) (X.nuv b.1 (j + 1) b.2) _
      (hlamS X j b.1 b.2 j le_rfl) (nuv_nonneg X b.1 j b.2) t
    rw [nuv_top X j b.1 b.2] at this
    refine this.trans ?_
    simp
  · exact shape_odd _ _ (rankJ X (j + 1)) _ (X.Fl.domJ (j + 1) b.1 b.2) (X.nuv b.1 (j + 1) b.2) _
      (hlamS X j b.1 b.2 j le_rfl) (nuv_nonneg X b.1 j b.2) t
  · exact absurd (even_of_not_odd h2) h1

/- English proof (translation)
Distinguish the cases in `hc : c < X.G.P.m + (j + 1) * (X.Fl.t + 1) + 1`. Rewrite using `[hlamS X j v s j le_rfl ⟨c, hc⟩, hlamS X j v s j le_rfl ⟨a, lt_of_le_of_lt h hc⟩]`. Use `X.Fl.domJ (j + 1) v s (show (⟨a, lt_of_le_of_lt h hc⟩ : Fin _) ≤ ⟨c, hc⟩ from h)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[nuv_zero X v j s (c + 1) (by`.

Establish `h1 : NN X.G.P.m X.t j ≤ NN X.G.P.m X.t (j + 1)` using `NN_le X j`. Establish `h2 : NN X.G.P.m X.t (j + 1) = X.G.P.m + 1 + (j + 1) * (X.Fl.t + 1)` using `rfl`. Use the proof step `omega)]`. Conclude with `nuv_nonneg X v j s _`.
-/
theorem nuv_anti (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) {a c : ℕ} (h : a ≤ c) :
    X.nuv v (j + 1) s (c + 1) ≤ X.nuv v (j + 1) s (a + 1) := by
  by_cases hc : c < X.G.P.m + (j + 1) * (X.Fl.t + 1) + 1
  · rw [hlamS X j v s j le_rfl ⟨c, hc⟩, hlamS X j v s j le_rfl ⟨a, lt_of_le_of_lt h hc⟩]
    have := X.Fl.domJ (j + 1) v s (show (⟨a, lt_of_le_of_lt h hc⟩ : Fin _) ≤ ⟨c, hc⟩ from h)
    linarith
  · rw [nuv_zero X v j s (c + 1) (by
      have h1 : NN X.G.P.m X.t j ≤ NN X.G.P.m X.t (j + 1) := NN_le X j
      have h2 : NN X.G.P.m X.t (j + 1) = X.G.P.m + 1 + (j + 1) * (X.Fl.t + 1) := rfl
      omega)]
    exact nuv_nonneg X v j s _

/- English proof (translation)
Introduce `a c hac`. Unfold `muX`. Conclude with `Int.toNat_le_toNat (nuv_anti X j b.1 b.2 hac)`.
-/
theorem c3 (j n : ℕ) (b : BX X) : Antitone (muX X j n b) := by
  intro a c hac
  unfold muX
  exact Int.toNat_le_toNat (nuv_anti X j b.1 b.2 hac)

/- English proof (translation)
Unfold `muX cX`. Conclude with `Int.toNat_le_toNat (nuv_le_first X b.1 j b.2 _)`.
-/
theorem c4 (j n : ℕ) (b : BX X) (t : Fin n) : muX X j n b t ≤ cX X j b := by
  unfold muX cX
  exact Int.toNat_le_toNat (nuv_le_first X b.1 j b.2 _)

/- English proof (translation)
Unfold `colH muX Sys.colHt`. Rewrite using `[BidetPairing.card_fin_filter n fun t => k < (X.nuv b.1 (j + 1) b.2 (t + 1)).toNat]`. Use `Finset.card_bij (fun t _ => t + 1) ?_ ?_ ?_` and prove the remaining obligations. Introduce `t ht`. Rewrite `ht` using `[Finset.mem_filter, Finset.mem_range]`.

Rewrite using `[Finset.mem_filter, Finset.mem_Icc]`. Conclude with `⟨⟨by omega, by omega⟩, Int.lt_toNat.1 ht.2⟩`. Introduce `a _ c _ h`. Use linear arithmetic over natural numbers and integers. Introduce `i hi`.

Rewrite `hi` using `[Finset.mem_filter, Finset.mem_Icc]`. Establish `hin : i ≤ n`. Assume the negation of the conclusion as `hc`. Use `nuv_zero X b.1 j b.2 i (by omega)` as an intermediate fact. Rewrite `hi` using `[this]`.

Use `hi.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `⟨i - 1, ?_, by omega⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_filter, Finset.mem_range]`. Use `⟨by omega, ?_⟩` and prove the remaining obligations.

Rewrite using `[show i - 1 + 1 = i by omega]`. Conclude with `Int.lt_toNat.2 hi.2`.
-/
theorem c56 (j n : ℕ) (h1 : NN X.G.P.m X.t j ≤ n) (h2 : n ≤ NN X.G.P.m X.t (j + 1)) (b : BX X) (k : ℕ) :
    colH (muX X j n b) k = X.colHt b.1 (j + 1) b.2 k := by
  unfold colH muX Sys.colHt
  rw [BidetPairing.card_fin_filter n fun t => k < (X.nuv b.1 (j + 1) b.2 (t + 1)).toNat]
  refine Finset.card_bij (fun t _ => t + 1) ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_filter, Finset.mem_range] at ht
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, Int.lt_toNat.1 ht.2⟩
  · intro a _ c _ h
    omega
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_Icc] at hi
    have hin : i ≤ n := by
      by_contra hc
      have := nuv_zero X b.1 j b.2 i (by omega)
      rw [this] at hi
      have := hi.2
      omega
    refine ⟨i - 1, ?_, by omega⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [show i - 1 + 1 = i by omega]
    exact Int.lt_toNat.2 hi.2

/- English proof (translation)
Unfold `NN`. Use linear arithmetic over natural numbers and integers.
-/
theorem NJ_pos (j : ℕ) : 0 < NN X.G.P.m X.t j := by unfold NN; omega

/- English proof (translation)
Unfold `eX muX`. Establish `h` using `nuv_anti X j b.1 b.2 (show t.val ≤ NJ X j - 1 by have := t.isLt; omega)`. Establish `hN : NJ X j - 1 + 1 = NJ X j` using `Nat.sub_add_cancel (NJ_pos X j)`. Rewrite `h` using `[hN]`. Conclude with `Int.toNat_le_toNat h`.
-/
theorem c7 (j : ℕ) (b : BX X) (t : Fin (NJ X j)) : eX X j b ≤ muX X j (NJ X j) b t := by
  unfold eX muX
  have h := nuv_anti X j b.1 b.2 (show t.val ≤ NJ X j - 1 by have := t.isLt; omega)
  have hN : NJ X j - 1 + 1 = NJ X j := Nat.sub_add_cancel (NJ_pos X j)
  rw [hN] at h
  exact Int.toNat_le_toNat h

/- English proof (translation)
Unfold `eX muX`. Rewrite using `[ht]`.
-/
theorem c8 (j : ℕ) (b : BX X) (t : Fin (NJ X j)) (ht : t.val + 1 = NJ X j) : muX X j (NJ X j) b t = eX X j b := by
  unfold eX muX
  rw [ht]

/- English proof (translation)
Establish `h1` using `numO X j v s h`. Establish `h2 : cMu X j v s = X.G.P.lam0 v s ⟨0, by omega⟩ + X.Fl.w v (j + 1) s` using `nuv_low X j v s 0 (by omega)`. Establish `h3 : X.w v (j + 1) s = X.Fl.w v (j + 1) s` using `rfl`. Establish `h4 : (⟨0, by omega⟩ : Fin (X.G.P.m + 1)) = 0` using `rfl`. Rewrite `h2` using `[h4]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eJ_odd (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (h : IsOddPos s) : eJ X j v s = -X.G.P.lam0 v s 0 := by
  have h1 := numO X j v s h
  have h2 : cMu X j v s = X.G.P.lam0 v s ⟨0, by omega⟩ + X.Fl.w v (j + 1) s := nuv_low X j v s 0 (by omega)
  have h3 : X.w v (j + 1) s = X.Fl.w v (j + 1) s := rfl
  have h4 : (⟨0, by omega⟩ : Fin (X.G.P.m + 1)) = 0 := rfl
  rw [h4] at h2
  linarith

/- English proof (translation)
Take `⟨h1, h2⟩` from `numE X j b.1 b.2 h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `eX`. Rewrite using `[Int.toNat_of_nonneg h1, h2]`. Establish `h3` using `hlamS X j b.1 b.2 j le_rfl (Fin.last _)`.

Establish `h4 : X.nuv b.1 (j + 1) b.2 ((Fin.last (X.G.P.m + (j + 1) * (X.Fl.t + 1))).val + 1) = 0`. Use `nuv_top X j b.1 b.2` as an intermediate fact. Rewrite using `[Fin.val_last]`. Establish `e : X.G.P.m + (j + 1) * (X.Fl.t + 1) + 1 = NN X.G.P.m X.t (j + 1)` using `by show _ = X.G.P.m + 1 + (j + 1) * (X.Fl.t + 1)`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[e]`. Conclude with `this`. Rewrite `h3` using `[h4]`. Establish `h5 : eJ X (j + 1) b.1 b.2 = liftWt X.Fl.t X.G.P.m (X.G.P.lam0 b.1 b.2) (fun i => X.Fl.w b.1 i b.2) (j + 1) (Fin.last _)` using `by show lamAt _ b.2 _ = _`. Unfold `lamAt`.

Rewrite using `[if_pos (even_of_not_odd h)]`. Both sides reduce to the same expression. Rewrite using `[h5]`. Establish `h6 : X.w b.1 (j + 1) b.2 = X.Fl.w b.1 (j + 1) b.2` using `rfl`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem c9 (j : ℕ) (b : BX X) (h : ¬ IsOddPos b.2) :
    (eX X j b : ℤ) = eJ X j b.1 b.2 + X.w b.1 (j + 1) b.2 ∧ eJ X (j + 1) b.1 b.2 = -X.w b.1 (j + 1) b.2 := by
  obtain ⟨h1, h2⟩ := numE X j b.1 b.2 h
  refine ⟨?_, ?_⟩
  · unfold eX
    rw [Int.toNat_of_nonneg h1, h2]
  · have h3 := hlamS X j b.1 b.2 j le_rfl (Fin.last _)
    have h4 : X.nuv b.1 (j + 1) b.2 ((Fin.last (X.G.P.m + (j + 1) * (X.Fl.t + 1))).val + 1) = 0 := by
      have := nuv_top X j b.1 b.2
      rw [Fin.val_last]
      have e : X.G.P.m + (j + 1) * (X.Fl.t + 1) + 1 = NN X.G.P.m X.t (j + 1) := by
        show _ = X.G.P.m + 1 + (j + 1) * (X.Fl.t + 1)
        omega
      rw [e]; exact this
    rw [h4] at h3
    have h5 : eJ X (j + 1) b.1 b.2 =
        liftWt X.Fl.t X.G.P.m (X.G.P.lam0 b.1 b.2) (fun i => X.Fl.w b.1 i b.2) (j + 1) (Fin.last _) := by
      show lamAt _ b.2 _ = _
      unfold lamAt
      rw [if_pos (even_of_not_odd h)]
      rfl
    rw [h5]
    have h6 : X.w b.1 (j + 1) b.2 = X.Fl.w b.1 (j + 1) b.2 := rfl
    linarith

/- English proof (translation)
Use `⟨?_, by rw [eJ_odd X (j + 1) b.1 b.2 h, eJ_odd X j b.1 b.2 h]⟩` and prove the remaining obligations. Establish `h1` using `numO X j b.1 b.2 h`. Rewrite using `[← h1]`. Conclude with `cMu_toNat X b.1 j b.2`.
-/
theorem c10 (j : ℕ) (b : BX X) (h : IsOddPos b.2) :
    (cX X j b : ℤ) = X.w b.1 (j + 1) b.2 - eJ X j b.1 b.2 ∧ eJ X (j + 1) b.1 b.2 = eJ X j b.1 b.2 := by
  refine ⟨?_, by rw [eJ_odd X (j + 1) b.1 b.2 h, eJ_odd X j b.1 b.2 h]⟩
  have h1 := numO X j b.1 b.2 h
  rw [← h1]
  exact cMu_toNat X b.1 j b.2

end FrameShapeLemmas

open FrameShapeLemmas in
/- English proof (translation)
Introduce `p _ X j b`. Conclude with `⟨c1 X j b, c2 X j b, fun n => c3 X j n b, fun n t => c4 X j n b t, c56 X j _ le_rfl (NN_le X j) b, c56 X j _ (NN_le X j) le_rfl b, c7 X j b, c8 X j b, c9 X j b, c10 X j b⟩`.
-/
theorem frame_shape_identity_holds : XShape := by
  intro p _ X j b
  exact ⟨c1 X j b, c2 X j b, fun n => c3 X j n b, fun n t => c4 X j n b t, c56 X j _ le_rfl (NN_le X j) b,
    c56 X j _ (NN_le X j) le_rfl b, c7 X j b, c8 X j b, c9 X j b, c10 X j b⟩

end Formalism.L2.PairingIndexBounds.Ent
