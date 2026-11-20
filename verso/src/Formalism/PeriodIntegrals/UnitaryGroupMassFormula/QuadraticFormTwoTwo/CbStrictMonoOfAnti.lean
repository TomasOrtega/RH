import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.InLieW

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `i j hi hij hj`. Proceed by induction on `j with`. Consider the case `zero => omega`. Consider the case `succ j ih`. Distinguish the cases in `h : i < j`.

Conclude with `lt_trans (ha j (by omega) hj) (ih h (by omega))`. Establish `e : i = j` using `by omega`. Rewrite using `[e]`. Conclude with `ha j (by omega) hj`.
-/
theorem cb_anti_of_succ {n : ℕ} {a : ℕ → ℝ} (ha : ∀ i, 1 ≤ i → i + 1 ≤ n → a (i + 1) < a i) :
    ∀ i j, 1 ≤ i → i < j → j ≤ n → a j < a i := by
  intro i j hi hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases h : i < j
    · exact lt_trans (ha j (by omega) hj) (ih h (by omega))
    · have e : i = j := by omega
      rw [e]
      exact ha j (by omega) hj

/- English proof (translation)
Introduce `i hi`. Establish `h0` using `h (-(a i : ℂ))`. Establish `hl : ∏ l ∈ Icc 1 n, (-(a i : ℂ) + (a l : ℂ)) = 0` using `Finset.prod_eq_zero hi (by ring)`. Rewrite `h0` using `[hl]`. Take `⟨j, hj, hz⟩` from `Finset.prod_eq_zero_iff.mp h0.symm`.

Use `⟨j, hj, ?_⟩` and prove the remaining obligations. Establish `e : ((b j : ℝ) : ℂ) = (a i : ℂ)` using `by linear_combination hz`. Conclude with `e.symm` after adjusting the coercions.
-/
theorem cb_mem_of_prod_eq {n : ℕ} {a b : ℕ → ℝ}
    (h : ∀ Y : ℂ, ∏ i ∈ Icc 1 n, (Y + (a i : ℂ)) = ∏ i ∈ Icc 1 n, (Y + (b i : ℂ))) :
    ∀ i ∈ Icc 1 n, ∃ j ∈ Icc 1 n, a i = b j := by
  intro i hi
  have h0 := h (-(a i : ℂ))
  have hl : ∏ l ∈ Icc 1 n, (-(a i : ℂ) + (a l : ℂ)) = 0 := Finset.prod_eq_zero hi (by ring)
  rw [hl] at h0
  obtain ⟨j, hj, hz⟩ := Finset.prod_eq_zero_iff.mp h0.symm
  refine ⟨j, hj, ?_⟩
  have e : ((b j : ℝ) : ℂ) = (a i : ℂ) := by linear_combination hz
  exact_mod_cast e.symm

/- English proof (translation)
Introduce and unpack `x ⟨j, rfl⟩`. Take `⟨l, hl, hab⟩` from `hm (j.val + 1) (Finset.mem_Icc.mpr ⟨by omega, by have := j.isLt; omega⟩)`. Establish `hl1` using `(Finset.mem_Icc.mp hl).1`. Establish `hl2` using `(Finset.mem_Icc.mp hl).2`. Use `⟨⟨l - 1, by omega⟩, ?_⟩` and prove the remaining obligations.

Use `show -b (l - 1 + 1) = -a (j.val + 1)`. Rewrite using `[hab, Nat.sub_add_cancel hl1]`.
-/
theorem cb_range_sub_of_mem {n : ℕ} {a b : ℕ → ℝ} (hm : ∀ i ∈ Icc 1 n, ∃ j ∈ Icc 1 n, a i = b j) :
    Set.range (fun j : Fin n => -a (j.1 + 1)) ⊆ Set.range (fun j : Fin n => -b (j.1 + 1)) := by
  rintro x ⟨j, rfl⟩
  obtain ⟨l, hl, hab⟩ := hm (j.val + 1) (Finset.mem_Icc.mpr ⟨by omega, by have := j.isLt; omega⟩)
  have hl1 := (Finset.mem_Icc.mp hl).1
  have hl2 := (Finset.mem_Icc.mp hl).2
  refine ⟨⟨l - 1, by omega⟩, ?_⟩
  show -b (l - 1 + 1) = -a (j.val + 1)
  rw [hab, Nat.sub_add_cancel hl1]

/- English proof (translation)
Introduce `i j hij`. Establish `h' : i.val < j.val` using `hij`. Establish `hjn` using `j.isLt`. Use `cb_anti_of_succ ha (i.val + 1) (j.val + 1) (by omega) (by omega) (by omega)` as an intermediate fact. Use `show -a (i.val + 1) < -a (j.val + 1)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cb_strictMono_of_anti {n : ℕ} {a : ℕ → ℝ} (ha : ∀ i, 1 ≤ i → i + 1 ≤ n → a (i + 1) < a i) :
    StrictMono (fun j : Fin n => -a (j.1 + 1)) := by
  intro i j hij
  have h' : i.val < j.val := hij
  have hjn := j.isLt
  have := cb_anti_of_succ ha (i.val + 1) (j.val + 1) (by omega) (by omega) (by omega)
  show -a (i.val + 1) < -a (j.val + 1)
  linarith

/- English proof (translation)
Establish `hr : Set.range (fun j : Fin n => -a (j.1 + 1)) = Set.range (fun j : Fin n => -b (j.1 + 1))` using `Set.Subset.antisymm (cb_range_sub_of_mem (cb_mem_of_prod_eq h)) (cb_range_sub_of_mem (cb_mem_of_prod_eq (fun Y => (h Y).symm)))`. Establish `hf` using `((cb_strictMono_of_anti ha).range_inj (cb_strictMono_of_anti hb)).mp hr`. Introduce `i hi`. Establish `h1` using `(Finset.mem_Icc.mp hi).1`. Establish `h1'` using `(Finset.mem_Icc.mp hi).2`.

Establish `h2 : -a (i - 1 + 1) = -b (i - 1 + 1)` using `congrFun hf ⟨i - 1, by omega⟩`. Rewrite `h2` using `[Nat.sub_add_cancel h1]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cb_eq_of_prod_eq {n : ℕ} {a b : ℕ → ℝ}
    (ha : ∀ i, 1 ≤ i → i + 1 ≤ n → a (i + 1) < a i) (hb : ∀ i, 1 ≤ i → i + 1 ≤ n → b (i + 1) < b i)
    (h : ∀ Y : ℂ, ∏ i ∈ Icc 1 n, (Y + (a i : ℂ)) = ∏ i ∈ Icc 1 n, (Y + (b i : ℂ))) :
    ∀ i ∈ Icc 1 n, a i = b i := by
  have hr : Set.range (fun j : Fin n => -a (j.1 + 1)) = Set.range (fun j : Fin n => -b (j.1 + 1)) :=
    Set.Subset.antisymm (cb_range_sub_of_mem (cb_mem_of_prod_eq h))
      (cb_range_sub_of_mem (cb_mem_of_prod_eq (fun Y => (h Y).symm)))
  have hf := ((cb_strictMono_of_anti ha).range_inj (cb_strictMono_of_anti hb)).mp hr
  intro i hi
  have h1 := (Finset.mem_Icc.mp hi).1
  have h1' := (Finset.mem_Icc.mp hi).2
  have h2 : -a (i - 1 + 1) = -b (i - 1 + 1) := congrFun hf ⟨i - 1, by omega⟩
  rw [Nat.sub_add_cancel h1] at h2
  linarith

/- English proof (translation)
Unfold `M.rho`. Rewrite using `[dif_pos ⟨by omega, by have := j.isLt; omega⟩]`. Use `first`. Consider the case `rfl`. Consider the case `simp`.
-/
theorem cb_rho_eq' (Q : M.Par) (π : M.Ty Q) (j : Fin (Q.k - 1)) :
    M.rho Q π (j.1 + 1) = Q.lo (j.1 + 1) + (((π j : Fin _) : ℕ) : ℝ) := by
  unfold M.rho
  rw [dif_pos ⟨by omega, by have := j.isLt; omega⟩]
  first
    | rfl
    | simp

/- English proof (translation)
Conclude with `⟨⟨i - 1, by omega⟩, by show i = i - 1 + 1; omega⟩`.
-/
theorem cb_ofIcc {n i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ n) : ∃ j : Fin n, i = j.1 + 1 := by
  exact ⟨⟨i - 1, by omega⟩, by show i = i - 1 + 1; omega⟩

/- English proof (translation)
Rewrite using `[cb_rho_eq' Q π j]`. Establish `hj` using `j.2`. Establish `hw : ((π j : Fin _) : ℕ) ≤ Q.wid (j.1 + 1)` using `by have := (π j).2; omega`. Establish `hg'` using `hg (j.1 + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)`. Establish `hf : ((Q.wid (j.1 + 1) : ℕ) : ℝ) ≤ Q.hi (j.1 + 1) - Q.lo (j.1 + 1)` using `Nat.floor_le (sub_nonneg.mpr hg')`.

Establish `hw' : (((π j : Fin _) : ℕ) : ℝ) ≤ (Q.wid (j.1 + 1) : ℝ)` using `by exact_mod_cast hw`. Establish `h0 : (0 : ℝ) ≤ (((π j : Fin _) : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem cb_rho_bounds (Q : M.Par) (hg : ∀ i ∈ Icc 1 (Q.k - 1), Q.lo i ≤ Q.hi i) (π : M.Ty Q)
    (j : Fin (Q.k - 1)) : Q.lo (j.1 + 1) ≤ M.rho Q π (j.1 + 1) ∧ M.rho Q π (j.1 + 1) ≤ Q.hi (j.1 + 1) := by
  rw [cb_rho_eq' Q π j]
  have hj := j.2
  have hw : ((π j : Fin _) : ℕ) ≤ Q.wid (j.1 + 1) := by have := (π j).2; omega
  have hg' := hg (j.1 + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hf : ((Q.wid (j.1 + 1) : ℕ) : ℝ) ≤ Q.hi (j.1 + 1) - Q.lo (j.1 + 1) :=
    Nat.floor_le (sub_nonneg.mpr hg')
  have hw' : (((π j : Fin _) : ℕ) : ℝ) ≤ (Q.wid (j.1 + 1) : ℝ) := by exact_mod_cast hw
  have h0 : (0 : ℝ) ≤ (((π j : Fin _) : ℕ) : ℝ) := Nat.cast_nonneg _
  constructor <;> linarith

/- English proof (translation)
Introduce `i h1 h2`. Take `⟨j, rfl⟩` from `cb_ofIcc (n := Q.k - 1) h1 (by omega)`. Establish `b1` using `(cb_rho_bounds Q hg π ⟨j.1 + 1, by omega⟩).2`. Establish `b0` using `(cb_rho_bounds Q hg π j).1`. Establish `hm` using `min_le_max (a := Q.u (j.1 + 1 + 1)) (b := Q.u' (j.1 + 1 + 1))`.

Establish `e1 : Q.hi (j.1 + 1 + 1) = min (Q.u (j.1 + 1 + 1)) (Q.u' (j.1 + 1 + 1)) - 1 / 2` using `rfl`. Establish `e2 : Q.lo (j.1 + 1) = max (Q.u (j.1 + 1 + 1)) (Q.u' (j.1 + 1 + 1)) + 1 / 2` using `rfl`. Simplify using `only at b1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cb_rho_anti (Q : M.Par) (hg : ∀ i ∈ Icc 1 (Q.k - 1), Q.lo i ≤ Q.hi i) (π : M.Ty Q) :
    ∀ i, 1 ≤ i → i + 1 ≤ Q.k - 1 → M.rho Q π (i + 1) < M.rho Q π i := by
  intro i h1 h2
  obtain ⟨j, rfl⟩ := cb_ofIcc (n := Q.k - 1) h1 (by omega)
  have b1 := (cb_rho_bounds Q hg π ⟨j.1 + 1, by omega⟩).2
  have b0 := (cb_rho_bounds Q hg π j).1
  have hm := min_le_max (a := Q.u (j.1 + 1 + 1)) (b := Q.u' (j.1 + 1 + 1))
  have e1 : Q.hi (j.1 + 1 + 1) = min (Q.u (j.1 + 1 + 1)) (Q.u' (j.1 + 1 + 1)) - 1 / 2 := rfl
  have e2 : Q.lo (j.1 + 1) = max (Q.u (j.1 + 1 + 1)) (Q.u' (j.1 + 1 + 1)) + 1 / 2 := rfl
  simp only at b1
  linarith

/- English proof (translation)
Use function extensionality and compare the values at `j`. Apply `Fin.ext` to reduce the goal to its premises. Establish `e` using `h j`. Rewrite `e` using `[cb_rho_eq' Q π j, cb_rho_eq' Q π' j]`. Conclude with `add_left_cancel e` after adjusting the coercions.
-/
theorem cb_ty_ext (Q : M.Par) {π π' : M.Ty Q}
    (h : ∀ j : Fin (Q.k - 1), M.rho Q π (j.1 + 1) = M.rho Q π' (j.1 + 1)) : π = π' := by
  funext j
  apply Fin.ext
  have e := h j
  rw [cb_rho_eq' Q π j, cb_rho_eq' Q π' j] at e
  exact_mod_cast add_left_cancel e

/- English proof (translation)
Use `⟨fun j => ⟨⌊v (j.1 + 1) - Q.lo (j.1 + 1)⌋₊, ?_⟩, ?_⟩` and prove the remaining obligations. Take `⟨h1, h2, -⟩` from `hv j`. Establish `: ⌊v (j.1 + 1) - Q.lo (j.1 + 1)⌋₊ ≤ Q.wid (j.1 + 1)`. Unfold `M.Par.wid`. Conclude with `Nat.floor_le_floor (by linarith)`.

Use linear arithmetic over natural numbers and integers. Introduce `j`. Rewrite using `[cb_rho_eq' Q _ j]`. Take `⟨h1, -, n, hn⟩` from `hv j`. Establish `hn0 : (0 : ℝ) ≤ (n : ℝ)` using `hn ▸ sub_nonneg.mpr h1`.

Establish `hn0' : (0 : ℤ) ≤ n` using `by exact_mod_cast hn0`. Use `lift n to ℕ using hn0'`. Rewrite `hn` using `[Int.cast_natCast]`. Use `show Q.lo (j.1 + 1) + ((⌊v (j.1 + 1) - Q.lo (j.1 + 1)⌋₊ : ℕ) : ℝ) = v (j.1 + 1)`. Rewrite using `[hn, Nat.floor_natCast]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cb_exists_ty (Q : M.Par) (v : ℕ → ℝ)
    (hv : ∀ j : Fin (Q.k - 1), Q.lo (j.1 + 1) ≤ v (j.1 + 1) ∧ v (j.1 + 1) ≤ Q.hi (j.1 + 1) ∧
      ∃ n : ℤ, v (j.1 + 1) - Q.lo (j.1 + 1) = n) :
    ∃ τ : M.Ty Q, ∀ j : Fin (Q.k - 1), M.rho Q τ (j.1 + 1) = v (j.1 + 1) := by
  refine ⟨fun j => ⟨⌊v (j.1 + 1) - Q.lo (j.1 + 1)⌋₊, ?_⟩, ?_⟩
  · obtain ⟨h1, h2, -⟩ := hv j
    have : ⌊v (j.1 + 1) - Q.lo (j.1 + 1)⌋₊ ≤ Q.wid (j.1 + 1) := by
      unfold M.Par.wid
      exact Nat.floor_le_floor (by linarith)
    omega
  · intro j
    rw [cb_rho_eq' Q _ j]
    obtain ⟨h1, -, n, hn⟩ := hv j
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := hn ▸ sub_nonneg.mpr h1
    have hn0' : (0 : ℤ) ≤ n := by exact_mod_cast hn0
    lift n to ℕ using hn0'
    rw [Int.cast_natCast] at hn
    show Q.lo (j.1 + 1) + ((⌊v (j.1 + 1) - Q.lo (j.1 + 1)⌋₊ : ℕ) : ℝ) = v (j.1 + 1)
    rw [hn, Nat.floor_natCast]
    linarith

/- English proof (translation)
Unfold `M.Par.lo`. Apply the tactic sequence `rcases max_choice (Q.u (i + 1)) (Q.u' (i + 1)) with h | h <;> rw [h]`. Take `⟨n, hn⟩` from `hu`. Conclude with `⟨n, by linarith⟩`. Take `⟨n, hn⟩` from `hu'`.

Conclude with `⟨n, by linarith⟩`.
-/
theorem cb_lo_int (Q : M.Par) (c : ℝ) (i : ℕ) (hu : ∃ n : ℤ, Q.u (i + 1) - c = n)
    (hu' : ∃ n : ℤ, Q.u' (i + 1) - c = n) : ∃ n : ℤ, Q.lo i - (c + 1 / 2) = n := by
  unfold M.Par.lo
  rcases max_choice (Q.u (i + 1)) (Q.u' (i + 1)) with h | h <;> rw [h]
  · obtain ⟨n, hn⟩ := hu
    exact ⟨n, by linarith⟩
  · obtain ⟨n, hn⟩ := hu'
    exact ⟨n, by linarith⟩

/- English proof (translation)
Rewrite using `[cb_rho_eq' Q τ j]`. Take `⟨n, hn⟩` from `h`. Conclude with `⟨n + ((τ j : Fin _) : ℕ), by push_cast; linarith⟩`.
-/
theorem cb_rho_int (Q : M.Par) (c : ℝ) (τ : M.Ty Q) (j : Fin (Q.k - 1))
    (h : ∃ n : ℤ, Q.lo (j.1 + 1) - c = n) : ∃ n : ℤ, M.rho Q τ (j.1 + 1) - c = n := by
  rw [cb_rho_eq' Q τ j]
  obtain ⟨n, hn⟩ := h
  exact ⟨n + ((τ j : Fin _) : ℕ), by push_cast; linarith⟩

/- English proof (translation)
Take `⟨m, hm⟩` from `hx`. Take `⟨l, hl⟩` from `hy`. Conclude with `⟨m - l, by push_cast; linarith⟩`.
-/
theorem cb_int_sub {x y c : ℝ} (hx : ∃ n : ℤ, x - c = n) (hy : ∃ n : ℤ, y - c = n) :
    ∃ n : ℤ, x - y = n := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨l, hl⟩ := hy
  exact ⟨m - l, by push_cast; linarith⟩

/- English proof (translation)
Establish `h1 : (1 : ℕ) ∈ Icc 1 P.k` using `Finset.mem_Icc.mpr ⟨le_rfl, hP.k_pos⟩`. Take `⟨b, hb⟩` from `hP.int_u' 1 h1`. Use `⟨hP.k_pos, hP.T_pos, hP.T'_pos, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Take `⟨a, ha⟩` from `hP.int_u' i hi`.

Conclude with `⟨a - b, by show P.u' i - P.u' 1 = _; push_cast; linarith⟩`. Introduce `i hi`. Take `⟨a, ha⟩` from `hP.int_u' i hi`. Conclude with `⟨a - b, by show P.u' i - P.u' 1 = _; push_cast; linarith⟩`. Introduce `i hi`.

Establish `g` using `hP.gap i hi`. Use `show max (P.u' (i + 1)) (P.u' (i + 1)) + 1 / 2 ≤ min (P.u' i) (P.u' i) - 1 / 2`. Establish `e1 : P.lo i = max (P.u (i + 1)) (P.u' (i + 1)) + 1 / 2` using `rfl`. Establish `e2 : P.hi i = min (P.u i) (P.u' i) - 1 / 2` using `rfl`. Rewrite using `[max_self, min_self]`.

Use `le_max_right (P.u (i + 1)) (P.u' (i + 1))` as an intermediate fact. Use `min_le_right (P.u i) (P.u' i)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Pp_OK {P : M.Par} (hP : P.OK) : (Pp P).OK := by
  have h1 : (1 : ℕ) ∈ Icc 1 P.k := Finset.mem_Icc.mpr ⟨le_rfl, hP.k_pos⟩
  obtain ⟨b, hb⟩ := hP.int_u' 1 h1
  refine ⟨hP.k_pos, hP.T_pos, hP.T'_pos, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨a, ha⟩ := hP.int_u' i hi
    exact ⟨a - b, by show P.u' i - P.u' 1 = _; push_cast; linarith⟩
  · intro i hi
    obtain ⟨a, ha⟩ := hP.int_u' i hi
    exact ⟨a - b, by show P.u' i - P.u' 1 = _; push_cast; linarith⟩
  · intro i hi
    have g := hP.gap i hi
    show max (P.u' (i + 1)) (P.u' (i + 1)) + 1 / 2 ≤ min (P.u' i) (P.u' i) - 1 / 2
    have e1 : P.lo i = max (P.u (i + 1)) (P.u' (i + 1)) + 1 / 2 := rfl
    have e2 : P.hi i = min (P.u i) (P.u' i) - 1 / 2 := rfl
    rw [max_self, min_self]
    have := le_max_right (P.u (i + 1)) (P.u' (i + 1))
    have := min_le_right (P.u i) (P.u' i)
    linarith

/- English proof (translation)
Use `⟨hP.k_pos, hP.T_pos, hP.T'_pos, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hP.int_u`. Conclude with `hP.int_u`. Introduce `i hi`. Establish `g` using `hP.gap i hi`.

Use `show max (P.u (i + 1)) (P.u (i + 1)) + 1 / 2 ≤ min (P.u i) (P.u i) - 1 / 2`. Establish `e1 : P.lo i = max (P.u (i + 1)) (P.u' (i + 1)) + 1 / 2` using `rfl`. Establish `e2 : P.hi i = min (P.u i) (P.u' i) - 1 / 2` using `rfl`. Rewrite using `[max_self, min_self]`. Use `le_max_left (P.u (i + 1)) (P.u' (i + 1))` as an intermediate fact.

Use `min_le_left (P.u i) (P.u' i)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Pq_OK {P : M.Par} (hP : P.OK) : (Pq P).OK := by
  refine ⟨hP.k_pos, hP.T_pos, hP.T'_pos, ?_, ?_, ?_⟩
  · exact hP.int_u
  · exact hP.int_u
  · intro i hi
    have g := hP.gap i hi
    show max (P.u (i + 1)) (P.u (i + 1)) + 1 / 2 ≤ min (P.u i) (P.u i) - 1 / 2
    have e1 : P.lo i = max (P.u (i + 1)) (P.u' (i + 1)) + 1 / 2 := rfl
    have e2 : P.hi i = min (P.u i) (P.u' i) - 1 / 2 := rfl
    rw [max_self, min_self]
    have := le_max_left (P.u (i + 1)) (P.u' (i + 1))
    have := min_le_left (P.u i) (P.u' i)
    linarith

/- English proof (translation)
Express the relevant statement in the definitionally equal form `max (P.u' (i + 1)) (P.u' (i + 1)) + 1 / 2 ≤ x at h1`. Express the relevant statement in the definitionally equal form `max (P.u (i + 1)) (P.u (i + 1)) + 1 / 2 ≤ x at h2`. Rewrite `h1`, `h2` using `[max_self]`. Use `show max (P.u (i + 1)) (P.u' (i + 1)) + 1 / 2 ≤ x`. Use `max_le (show P.u (i + 1) ≤ x - 1 / 2 by linarith) (show P.u' (i + 1) ≤ x - 1 / 2 by linarith)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cb_lo_le_of (P : M.Par) (i : ℕ) (x : ℝ) (h1 : (Pp P).lo i ≤ x) (h2 : (Pq P).lo i ≤ x) :
    P.lo i ≤ x := by
  change max (P.u' (i + 1)) (P.u' (i + 1)) + 1 / 2 ≤ x at h1
  change max (P.u (i + 1)) (P.u (i + 1)) + 1 / 2 ≤ x at h2
  rw [max_self] at h1 h2
  show max (P.u (i + 1)) (P.u' (i + 1)) + 1 / 2 ≤ x
  have := max_le (show P.u (i + 1) ≤ x - 1 / 2 by linarith) (show P.u' (i + 1) ≤ x - 1 / 2 by linarith)
  linarith

/- English proof (translation)
Express the relevant statement in the definitionally equal form `x ≤ min (P.u' i) (P.u' i) - 1 / 2 at h1`. Express the relevant statement in the definitionally equal form `x ≤ min (P.u i) (P.u i) - 1 / 2 at h2`. Rewrite `h1`, `h2` using `[min_self]`. Use `show x ≤ min (P.u i) (P.u' i) - 1 / 2`. Use `le_min (show x + 1 / 2 ≤ P.u i by linarith) (show x + 1 / 2 ≤ P.u' i by linarith)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cb_le_hi_of (P : M.Par) (i : ℕ) (x : ℝ) (h1 : x ≤ (Pp P).hi i) (h2 : x ≤ (Pq P).hi i) :
    x ≤ P.hi i := by
  change x ≤ min (P.u' i) (P.u' i) - 1 / 2 at h1
  change x ≤ min (P.u i) (P.u i) - 1 / 2 at h2
  rw [min_self] at h1 h2
  show x ≤ min (P.u i) (P.u' i) - 1 / 2
  have := le_min (show x + 1 / 2 ≤ P.u i by linarith) (show x + 1 / 2 ≤ P.u' i by linarith)
  linarith

/- English proof (translation)
Use `show max (P.u' (i + 1)) (P.u' (i + 1)) + 1 / 2 ≤ max (P.u (i + 1)) (P.u' (i + 1)) + 1 / 2`. Rewrite using `[max_self]`. Combine the linear relations using `[le_max_right (P.u (i + 1)) (P.u' (i + 1))]`.
-/
theorem cb_lo_Pp_le (P : M.Par) (i : ℕ) : (Pp P).lo i ≤ P.lo i := by
  show max (P.u' (i + 1)) (P.u' (i + 1)) + 1 / 2 ≤ max (P.u (i + 1)) (P.u' (i + 1)) + 1 / 2
  rw [max_self]
  linarith [le_max_right (P.u (i + 1)) (P.u' (i + 1))]

/- English proof (translation)
Use `show min (P.u i) (P.u' i) - 1 / 2 ≤ min (P.u' i) (P.u' i) - 1 / 2`. Rewrite using `[min_self]`. Combine the linear relations using `[min_le_right (P.u i) (P.u' i)]`.
-/
theorem cb_hi_le_Pp (P : M.Par) (i : ℕ) : P.hi i ≤ (Pp P).hi i := by
  show min (P.u i) (P.u' i) - 1 / 2 ≤ min (P.u' i) (P.u' i) - 1 / 2
  rw [min_self]
  linarith [min_le_right (P.u i) (P.u' i)]

/- English proof (translation)
Establish `gP : ∀ i ∈ Icc 1 (P.k - 1), P.lo i ≤ P.hi i` using `hP.gap`. Establish `gPp : ∀ i ∈ Icc 1 ((Pp P).k - 1), (Pp P).lo i ≤ (Pp P).hi i` using `(Pp_OK hP).gap`. Establish `gPq : ∀ i ∈ Icc 1 ((Pq P).k - 1), (Pq P).lo i ≤ (Pq P).hi i` using `(Pq_OK hP).gap`. Establish `hu : ∀ j : Fin (P.k - 1), ∃ n : ℤ, P.u (j.1 + 1 + 1) - P.u 1 = n` using `fun j => hP.int_u _ (Finset.mem_Icc.mpr ⟨by omega, by have := j.2; omega⟩)`. Establish `hu' : ∀ j : Fin (P.k - 1), ∃ n : ℤ, P.u' (j.1 + 1 + 1) - P.u 1 = n` using `fun j => hP.int_u' _ (Finset.mem_Icc.mpr ⟨by omega, by have := j.2; omega⟩)`.

Establish `zP : ∀ j : Fin (P.k - 1), ∃ n : ℤ, P.lo (j.1 + 1) - (P.u 1 + 1 / 2) = n` using `fun j => cb_lo_int P _ _ (hu j) (hu' j)`. Establish `zPp : ∀ j : Fin (P.k - 1), ∃ n : ℤ, (Pp P).lo (j.1 + 1) - (P.u 1 + 1 / 2) = n` using `fun j => cb_lo_int (Pp P) _ _ (hu' j) (hu' j)`. Establish `hf : ∀ ρ : M.Ty P, ∃ σ : M.Ty (Pp P), ∀ j : Fin (P.k - 1), M.rho (Pp P) σ (j.1 + 1) = M.rho P ρ (j.1 + 1)`. Introduce `ρ`. Use `cb_exists_ty (Pp P) (fun i => M.rho P ρ i) (fun j => ⟨?_, ?_, ?_⟩)` and prove the remaining obligations.

Conclude with `(cb_lo_Pp_le P _).trans (cb_rho_bounds P gP ρ j).1`. Conclude with `(cb_rho_bounds P gP ρ j).2.trans (cb_hi_le_Pp P _)`. Conclude with `cb_int_sub (cb_rho_int P _ ρ j (zP j)) (zPp j)`. Use `choose f hf using hf`. Use `⟨f, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `ρ ρ' h`. Apply `cb_ty_ext P` to reduce the goal to its premises. Introduce `j`. Rewrite using `[← hf ρ j, ← hf ρ' j, h]`. Introduce `ρ Y`.

Unfold `M.xC`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_Icc]`. Take `⟨j, rfl⟩` from `cb_ofIcc (n := P.k - 1) hi.1 hi.2`.

Rewrite using `[hf ρ j]`. Introduce `σ τ hx`. Establish `hst : ∀ i ∈ Icc 1 (P.k - 1), M.rho (Pp P) σ i = M.rho (Pq P) τ i` using `cb_eq_of_prod_eq (n := P.k - 1) (cb_rho_anti (Pp P) gPp σ) (cb_rho_anti (Pq P) gPq τ) (fun Y => hx Y)`. Take `⟨ρ, hρ⟩` from `cb_exists_ty P (fun i => M.rho (Pp P) σ i) (fun j => by`. Establish `e` using `hst (j.1 + 1) (Finset.mem_Icc.mpr ⟨by omega, by have := j.2; omega⟩)`.

Establish `bσ` using `cb_rho_bounds (Pp P) gPp σ j`. Establish `bτ` using `cb_rho_bounds (Pq P) gPq τ j`. Rewrite `bτ` using `[← e]`. Use `⟨cb_lo_le_of P _ _ bσ.1 bτ.1, cb_le_hi_of P _ _ bσ.2 bτ.2, ?_⟩` and prove the remaining obligations. Conclude with `cb_int_sub (cb_rho_int (Pp P) _ σ j (zPp j)) (zP j))`.

Use `⟨ρ, cb_ty_ext (Pp P) (fun j => ?_)⟩` and prove the remaining obligations. Rewrite using `[hf ρ j, hρ j]`.
-/
theorem comb_match {P : M.Par} (hP : P.OK) :
    ∃ f : M.Ty P → M.Ty (Pp P), Function.Injective f ∧ (∀ (ρ : M.Ty P) (Y : ℂ), M.xC (Pp P) (f ρ) Y = M.xC P ρ Y) ∧
      ∀ (σ : M.Ty (Pp P)) (ρ : M.Ty (Pq P)), (∀ Y : ℂ, M.xC (Pp P) σ Y = M.xC (Pq P) ρ Y) → σ ∈ Set.range f := by
  have gP : ∀ i ∈ Icc 1 (P.k - 1), P.lo i ≤ P.hi i := hP.gap
  have gPp : ∀ i ∈ Icc 1 ((Pp P).k - 1), (Pp P).lo i ≤ (Pp P).hi i := (Pp_OK hP).gap
  have gPq : ∀ i ∈ Icc 1 ((Pq P).k - 1), (Pq P).lo i ≤ (Pq P).hi i := (Pq_OK hP).gap
  have hu : ∀ j : Fin (P.k - 1), ∃ n : ℤ, P.u (j.1 + 1 + 1) - P.u 1 = n := fun j =>
    hP.int_u _ (Finset.mem_Icc.mpr ⟨by omega, by have := j.2; omega⟩)
  have hu' : ∀ j : Fin (P.k - 1), ∃ n : ℤ, P.u' (j.1 + 1 + 1) - P.u 1 = n := fun j =>
    hP.int_u' _ (Finset.mem_Icc.mpr ⟨by omega, by have := j.2; omega⟩)
  have zP : ∀ j : Fin (P.k - 1), ∃ n : ℤ, P.lo (j.1 + 1) - (P.u 1 + 1 / 2) = n := fun j =>
    cb_lo_int P _ _ (hu j) (hu' j)
  have zPp : ∀ j : Fin (P.k - 1), ∃ n : ℤ, (Pp P).lo (j.1 + 1) - (P.u 1 + 1 / 2) = n := fun j =>
    cb_lo_int (Pp P) _ _ (hu' j) (hu' j)
  have hf : ∀ ρ : M.Ty P, ∃ σ : M.Ty (Pp P),
      ∀ j : Fin (P.k - 1), M.rho (Pp P) σ (j.1 + 1) = M.rho P ρ (j.1 + 1) := by
    intro ρ
    refine cb_exists_ty (Pp P) (fun i => M.rho P ρ i) (fun j => ⟨?_, ?_, ?_⟩)
    · exact (cb_lo_Pp_le P _).trans (cb_rho_bounds P gP ρ j).1
    · exact (cb_rho_bounds P gP ρ j).2.trans (cb_hi_le_Pp P _)
    · exact cb_int_sub (cb_rho_int P _ ρ j (zP j)) (zPp j)
  choose f hf using hf
  refine ⟨f, ?_, ?_, ?_⟩
  · intro ρ ρ' h
    apply cb_ty_ext P
    intro j
    rw [← hf ρ j, ← hf ρ' j, h]
  · intro ρ Y
    unfold M.xC
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    obtain ⟨j, rfl⟩ := cb_ofIcc (n := P.k - 1) hi.1 hi.2
    rw [hf ρ j]
  · intro σ τ hx
    have hst : ∀ i ∈ Icc 1 (P.k - 1), M.rho (Pp P) σ i = M.rho (Pq P) τ i :=
      cb_eq_of_prod_eq (n := P.k - 1) (cb_rho_anti (Pp P) gPp σ) (cb_rho_anti (Pq P) gPq τ) (fun Y => hx Y)
    obtain ⟨ρ, hρ⟩ := cb_exists_ty P (fun i => M.rho (Pp P) σ i) (fun j => by
      have e := hst (j.1 + 1) (Finset.mem_Icc.mpr ⟨by omega, by have := j.2; omega⟩)
      have bσ := cb_rho_bounds (Pp P) gPp σ j
      have bτ := cb_rho_bounds (Pq P) gPq τ j
      rw [← e] at bτ
      refine ⟨cb_lo_le_of P _ _ bσ.1 bτ.1, cb_le_hi_of P _ _ bσ.2 bτ.2, ?_⟩
      exact cb_int_sub (cb_rho_int (Pp P) _ σ j (zPp j)) (zP j))
    refine ⟨ρ, cb_ty_ext (Pp P) (fun j => ?_)⟩
    rw [hf ρ j, hρ j]

def cb_xPoly (Q : M.Par) (σ : M.Ty Q) : Polynomial ℂ :=
  ∏ i ∈ Icc 1 (Q.k - 1), (Polynomial.X + Polynomial.C ((M.rho Q σ i : ℝ) : ℂ))

/- English proof (translation)
Unfold `cb_xPoly M.xC`. Simplify using `only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]`.
-/
theorem cb_eval_xPoly (Q : M.Par) (σ : M.Ty Q) (Y : ℂ) : (cb_xPoly Q σ).eval Y = M.xC Q σ Y := by
  unfold cb_xPoly M.xC
  simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

/- English proof (translation)
Establish `gPp : ∀ i ∈ Icc 1 ((Pp P).k - 1), (Pp P).lo i ≤ (Pp P).hi i` using `(Pp_OK hP).gap`. Establish `hne : ∀ σ σ' : M.Ty (Pp P), σ ≠ σ' → cb_xPoly (Pp P) σ - cb_xPoly (Pp P) σ' ≠ 0`. Introduce `σ σ' hss h0`. Apply `hss` to reduce the goal to its premises. Establish `hx : ∀ Y, M.xC (Pp P) σ Y = M.xC (Pp P) σ' Y`.

Introduce `Y`. Rewrite using `[← cb_eval_xPoly, ← cb_eval_xPoly, sub_eq_zero.mp h0]`. Establish `e` using `cb_eq_of_prod_eq (n := (Pp P).k - 1) (cb_rho_anti _ gPp σ) (cb_rho_anti _ gPp σ') hx`. Conclude with `cb_ty_ext _ (fun j => e _ (Finset.mem_Icc.mpr ⟨by omega, by have := j.2; omega⟩))`. Take `⟨Y₀, hY⟩` from `Infinite.exists_notMem_finset ((Finset.univ : Finset (M.Ty (Pp P) × M.Ty (Pp P))).biUnion (fun p => if p.1 = p.2 then ∅ else (cb_xPoly (Pp P) p.1 - cb_xPoly (Pp P) p.2).roots.toFinset))`.

Use `⟨Y₀, fun σ σ' h => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hss`. Apply `hY` to reduce the goal to its premises. Simplify using `only [Finset.mem_biUnion, Finset.mem_univ, true_and]`. Use `⟨(σ, σ'), ?_⟩` and prove the remaining obligations.

Rewrite using `[if_neg hss, Multiset.mem_toFinset, Polynomial.mem_roots (hne σ σ' hss), Polynomial.IsRoot.def, Polynomial.eval_sub, cb_eval_xPoly, cb_eval_xPoly, sub_eq_zero]`. Conclude with `h`.
-/
theorem exists_sep {P : M.Par} (hP : P.OK) :
    ∃ Y₀ : ℂ, Function.Injective (fun σ : M.Ty (Pp P) => M.xC (Pp P) σ Y₀) := by
  classical
  have gPp : ∀ i ∈ Icc 1 ((Pp P).k - 1), (Pp P).lo i ≤ (Pp P).hi i := (Pp_OK hP).gap
  have hne : ∀ σ σ' : M.Ty (Pp P), σ ≠ σ' → cb_xPoly (Pp P) σ - cb_xPoly (Pp P) σ' ≠ 0 := by
    intro σ σ' hss h0
    apply hss
    have hx : ∀ Y, M.xC (Pp P) σ Y = M.xC (Pp P) σ' Y := by
      intro Y
      rw [← cb_eval_xPoly, ← cb_eval_xPoly, sub_eq_zero.mp h0]
    have e := cb_eq_of_prod_eq (n := (Pp P).k - 1) (cb_rho_anti _ gPp σ) (cb_rho_anti _ gPp σ') hx
    exact cb_ty_ext _ (fun j => e _ (Finset.mem_Icc.mpr ⟨by omega, by have := j.2; omega⟩))
  obtain ⟨Y₀, hY⟩ := Infinite.exists_notMem_finset
    ((Finset.univ : Finset (M.Ty (Pp P) × M.Ty (Pp P))).biUnion
      (fun p => if p.1 = p.2 then ∅ else (cb_xPoly (Pp P) p.1 - cb_xPoly (Pp P) p.2).roots.toFinset))
  refine ⟨Y₀, fun σ σ' h => ?_⟩
  by_contra hss
  apply hY
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  refine ⟨(σ, σ'), ?_⟩
  rw [if_neg hss, Multiset.mem_toFinset, Polynomial.mem_roots (hne σ σ' hss), Polynomial.IsRoot.def,
    Polynomial.eval_sub, cb_eval_xPoly, cb_eval_xPoly, sub_eq_zero]
  exact h

end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
