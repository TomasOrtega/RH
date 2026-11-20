import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm

noncomputable section

namespace GlobalTheory.PMonE

open Finset

section Prep

variable {F : Type} [NormedField F] {m : Type} [Fintype m]

def PrepBd (c : ℝ) (X : Matrix m m F) : Prop := ∀ i j, ‖X i j‖ ≤ c

noncomputable def prepV (q : ℕ) (M : ℕ → Matrix m m F) (A : Matrix m m F) (k : ℕ) : ℕ → Matrix m m F :=
  Nat.rec (motive := fun _ => ℕ → Matrix m m F) (fun _ => 0)
    (fun _ V n => M (n + 1) + V (n + 1) * A.map (fun a => a ^ q ^ (n + 1))) k

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem prepV_zero (q : ℕ) (M : ℕ → Matrix m m F) (A : Matrix m m F) (n : ℕ) : prepV q M A 0 n = 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem prepV_succ (q : ℕ) (M : ℕ → Matrix m m F) (A : Matrix m m F) (k n : ℕ) :
    prepV q M A (k + 1) n = M (n + 1) + prepV q M A k (n + 1) * A.map (fun a => a ^ q ^ (n + 1)) := rfl

variable [IsUltrametricDist F]

omit [Fintype m] in
/- English proof (translation)
Introduce `i j` and use `(IsUltrametricDist.norm_add_le_max (X i j) (Y i j)).trans (max_le (hX i j) (hY i j))`.
-/
theorem PrepBd.add {c : ℝ} {X Y : Matrix m m F} (hX : PrepBd c X) (hY : PrepBd c Y) : PrepBd c (X + Y) :=
  fun i j => (IsUltrametricDist.norm_add_le_max (X i j) (Y i j)).trans (max_le (hX i j) (hY i j))

omit [Fintype m] [IsUltrametricDist F] in
/- English proof (translation)
Introduce `i j` and use `by simpa using hX i j`.
-/
theorem PrepBd.neg {c : ℝ} {X : Matrix m m F} (hX : PrepBd c X) : PrepBd c (-X) :=
  fun i j => by simpa using hX i j

omit [Fintype m] [IsUltrametricDist F] in
/- English proof (translation)
Introduce `i j` and use `(hX i j).trans h`.
-/
theorem PrepBd.mono {c d : ℝ} {X : Matrix m m F} (hX : PrepBd c X) (h : c ≤ d) : PrepBd d X :=
  fun i j => (hX i j).trans h

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hc hd) fun k _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (hX i k) (hY k j) (norm_nonneg _) hc`.
-/
theorem PrepBd.mul {c d : ℝ} {X Y : Matrix m m F} (hc : 0 ≤ c) (hd : 0 ≤ d) (hX : PrepBd c X) (hY : PrepBd d Y) :
    PrepBd (c * d) (X * Y) := by
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hc hd) fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hX i k) (hY k j) (norm_nonneg _) hc

omit [Fintype m] [IsUltrametricDist F] in
/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.map_apply, norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) (hX i j)`.
-/
theorem PrepBd.map_pow {X : Matrix m m F} (hX : PrepBd 1 X) (N : ℕ) : PrepBd 1 (X.map (fun a => a ^ N)) := by
  intro i j
  rw [Matrix.map_apply, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (hX i j)

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro n _ _ i j`. Simplify `hδ` using `[prepV_zero]`. Consider the case `succ k ih`.

Introduce `n hn hk`. Rewrite using `[prepV_succ]`. Use `(hM _ (by omega) (by omega)).add ?_` and prove the remaining obligations. Simplify using `using PrepBd.mul hδ zero_le_one (ih (n + 1) (by omega) (by omega)) (hA.map_pow _)`.
-/
theorem prepV_bd {q D : ℕ} {M : ℕ → Matrix m m F} {δ : ℝ} (hδ : 0 ≤ δ)
    (hM : ∀ n, 2 ≤ n → n ≤ D → PrepBd δ (M n)) {A : Matrix m m F} (hA : PrepBd 1 A) :
    ∀ k n, 1 ≤ n → n + k ≤ D → PrepBd δ (prepV q M A k n) := by
  intro k
  induction k with
  | zero => intro n _ _ i j; simpa [prepV_zero] using hδ
  | succ k ih =>
    intro n hn hk
    rw [prepV_succ]
    refine (hM _ (by omega) (by omega)).add ?_
    simpa using PrepBd.mul hδ zero_le_one (ih (n + 1) (by omega) (by omega)) (hA.map_pow _)

omit [Fintype m] in
/- English proof (translation)
Introduce `i j`. Establish `h1 : ‖A i j - B i j‖ ≤ 1`. Use `(hA.add hB.neg) i j` as an intermediate fact. Simplify `this` using `[sub_eq_add_neg]`. Establish `h2 : ‖A i j - B i j‖ ≤ ε` using `h i j`.

Rewrite using `[Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, ← pow_mul, ← sub_pow_char_pow, norm_pow]`. Conclude with `(pow_le_of_le_one (norm_nonneg _) h1 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).trans h2`.
-/
theorem PrepBd.map_pow_sub (p : ℕ) [Fact p.Prime] [CharP F p] (e n : ℕ) {A B : Matrix m m F} {ε : ℝ}
    (hA : PrepBd 1 A) (hB : PrepBd 1 B) (h : PrepBd ε (A - B)) :
    PrepBd ε (A.map (fun a => a ^ (p ^ e) ^ n) - B.map (fun a => a ^ (p ^ e) ^ n)) := by
  intro i j
  have h1 : ‖A i j - B i j‖ ≤ 1 := by
    have := (hA.add hB.neg) i j
    simpa [sub_eq_add_neg] using this
  have h2 : ‖A i j - B i j‖ ≤ ε := h i j
  rw [Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, ← pow_mul, ← sub_pow_char_pow, norm_pow]
  exact (pow_le_of_le_one (norm_nonneg _) h1 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).trans h2

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro n _ _ i j`. Simplify `mul_nonneg hδ hε` using `[prepV_zero]`. Consider the case `succ k ih`.

Introduce `n hn hk`. Rewrite using `[prepV_succ, prepV_succ]`. Establish `e1 : M (n + 1) + prepV (p ^ e) M A k (n + 1) * A.map (fun a => a ^ (p ^ e) ^ (n + 1)) - (M (n + 1) + prepV (p ^ e) M B k (n + 1) * B.map (fun a => a ^ (p ^ e) ^ (n + 1))) = (prepV (p ^ e) M A k (n + 1) - prepV (p ^ e) M B k (n + 1)) * A.map (fun a => a ^ (p ^ e) ^ (n + 1)) + prep …`. Rewrite using `[Matrix.sub_mul, Matrix.mul_sub]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e1]`. Use `PrepBd.add ?_ ?_` and prove the remaining obligations. Simplify using `using PrepBd.mul (mul_nonneg hδ hε) zero_le_one (ih (n + 1) (by omega) (by omega)) (hA.map_pow _)`. Conclude with `PrepBd.mul hδ hε (prepV_bd hδ hM hB k (n + 1) (by omega) (by omega)) (PrepBd.map_pow_sub p e _ hA hB h)`.
-/
theorem prepV_sub_bd (p : ℕ) [Fact p.Prime] [CharP F p] {e D : ℕ} {M : ℕ → Matrix m m F} {δ ε : ℝ} (hδ : 0 ≤ δ)
    (hε : 0 ≤ ε) (hM : ∀ n, 2 ≤ n → n ≤ D → PrepBd δ (M n)) {A B : Matrix m m F} (hA : PrepBd 1 A)
    (hB : PrepBd 1 B) (h : PrepBd ε (A - B)) :
    ∀ k n, 1 ≤ n → n + k ≤ D → PrepBd (δ * ε) (prepV (p ^ e) M A k n - prepV (p ^ e) M B k n) := by
  intro k
  induction k with
  | zero => intro n _ _ i j; simpa [prepV_zero] using mul_nonneg hδ hε
  | succ k ih =>
    intro n hn hk
    rw [prepV_succ, prepV_succ]
    have e1 : M (n + 1) + prepV (p ^ e) M A k (n + 1) * A.map (fun a => a ^ (p ^ e) ^ (n + 1)) -
        (M (n + 1) + prepV (p ^ e) M B k (n + 1) * B.map (fun a => a ^ (p ^ e) ^ (n + 1))) =
        (prepV (p ^ e) M A k (n + 1) - prepV (p ^ e) M B k (n + 1)) * A.map (fun a => a ^ (p ^ e) ^ (n + 1)) +
        prepV (p ^ e) M B k (n + 1) *
          (A.map (fun a => a ^ (p ^ e) ^ (n + 1)) - B.map (fun a => a ^ (p ^ e) ^ (n + 1))) := by
      rw [Matrix.sub_mul, Matrix.mul_sub]; abel
    rw [e1]
    refine PrepBd.add ?_ ?_
    · simpa using PrepBd.mul (mul_nonneg hδ hε) zero_le_one (ih (n + 1) (by omega) (by omega)) (hA.map_pow _)
    · exact PrepBd.mul hδ hε (prepV_bd hδ hM hB k (n + 1) (by omega) (by omega))
        (PrepBd.map_pow_sub p e _ hA hB h)

/- English proof (translation)
Set `s : Set (m → m → F)` to `{A | ∀ i j, ‖A i j‖ ≤ 1}`. Set `f : (m → m → F) → (m → m → F)` to `fun A => fun i j => (-M0 - W (Matrix.of A) * (Matrix.of A)) i j`. Establish `hs : IsClosed s`. Simplify using `only [s, Set.ofPred_forall]`. Conclude with `isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const`.

Establish `hf : Set.MapsTo f s s`. Introduce `A hA`. Establish `hA' : PrepBd 1 (Matrix.of A)` using `hA`. Establish `: PrepBd 1 (-M0 - W (Matrix.of A) * (Matrix.of A))`. Rewrite using `[sub_eq_add_neg]`.

Use `h0.neg.add (PrepBd.neg ?_)` and prove the remaining obligations. Conclude with `(PrepBd.mul hδ zero_le_one (hW _ hA') hA').mono (by simpa using hδ1.le)`. Conclude with `this`. Establish `hc : ContractingWith ⟨δ, hδ⟩ (hf.restrict f s s)`. Use `⟨hδ1, LipschitzWith.of_dist_le_mul fun A B => ?_⟩` and prove the remaining obligations.

Establish `hA' : PrepBd 1 (Matrix.of A.1)` using `A.2`. Establish `hB' : PrepBd 1 (Matrix.of B.1)` using `B.2`. Establish `hε : 0 ≤ dist A B` using `dist_nonneg`. Establish `hAB : PrepBd (dist A B) (Matrix.of A.1 - Matrix.of B.1)`. Introduce `i j`.

Rewrite using `[Matrix.sub_apply, Matrix.of_apply, Matrix.of_apply, ← dist_eq_norm, Subtype.dist_eq]`. Conclude with `(dist_le_pi_dist _ _ j).trans (dist_le_pi_dist A.1 B.1 i)`. Establish `key : PrepBd (δ * dist A B) ((-M0 - W (Matrix.of A.1) * (Matrix.of A.1)) - (-M0 - W (Matrix.of B.1) * (Matrix.of B.1)))`. Establish `e1 : (-M0 - W (Matrix.of A.1) * (Matrix.of A.1)) - (-M0 - W (Matrix.of B.1) * (Matrix.of B.1)) = -((W (Matrix.of A.1) - W (Matrix.of B.1)) * (Matrix.of A.1) + W (Matrix.of B.1) * (Matrix.of A.1 - Matrix.of B.1))`. Rewrite using `[Matrix.sub_mul, Matrix.mul_sub]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e1]`. Use `PrepBd.neg (PrepBd.add ?_ ?_)` and prove the remaining obligations. Simplify using `using PrepBd.mul (mul_nonneg hδ hε) zero_le_one (hW2 _ _ _ hε hA' hB' hAB) hA'`. Conclude with `PrepBd.mul hδ hε (hW _ hB') hAB`.

Express the relevant statement in the definitionally equal form `dist (f A.1) (f B.1) ≤ δ * dist A B`. Use `(dist_pi_le_iff (mul_nonneg hδ hε)).2 fun i => (dist_pi_le_iff (mul_nonneg hδ hε)).2 fun j => ?_` and prove the remaining obligations. Rewrite using `[dist_eq_norm]`. Conclude with `key i j`. Take `⟨y, hy, hfix, -⟩` from `hc.exists_fixedPoint' hs.isComplete hf (x := 0) (by intro i j; simp) (edist_ne_top _ _)`.

Use `⟨Matrix.of y, hy, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Conclude with `(congrFun (congrFun hfix i) j).symm`.
-/
theorem prep_fixed [CompleteSpace F] {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1) (M0 : Matrix m m F) (h0 : PrepBd 1 M0)
    (W : Matrix m m F → Matrix m m F) (hW : ∀ A, PrepBd 1 A → PrepBd δ (W A))
    (hW2 : ∀ A B ε, 0 ≤ ε → PrepBd 1 A → PrepBd 1 B → PrepBd ε (A - B) → PrepBd (δ * ε) (W A - W B)) :
    ∃ A, PrepBd 1 A ∧ A = -M0 - W A * A := by
  let s : Set (m → m → F) := {A | ∀ i j, ‖A i j‖ ≤ 1}
  let f : (m → m → F) → (m → m → F) := fun A => fun i j => (-M0 - W (Matrix.of A) * (Matrix.of A)) i j
  have hs : IsClosed s := by
    simp only [s, Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const
  have hf : Set.MapsTo f s s := by
    intro A hA
    have hA' : PrepBd 1 (Matrix.of A) := hA
    have : PrepBd 1 (-M0 - W (Matrix.of A) * (Matrix.of A)) := by
      rw [sub_eq_add_neg]
      refine h0.neg.add (PrepBd.neg ?_)
      exact (PrepBd.mul hδ zero_le_one (hW _ hA') hA').mono (by simpa using hδ1.le)
    exact this
  have hc : ContractingWith ⟨δ, hδ⟩ (hf.restrict f s s) := by
    refine ⟨hδ1, LipschitzWith.of_dist_le_mul fun A B => ?_⟩
    have hA' : PrepBd 1 (Matrix.of A.1) := A.2
    have hB' : PrepBd 1 (Matrix.of B.1) := B.2
    have hε : 0 ≤ dist A B := dist_nonneg
    have hAB : PrepBd (dist A B) (Matrix.of A.1 - Matrix.of B.1) := by
      intro i j
      rw [Matrix.sub_apply, Matrix.of_apply, Matrix.of_apply, ← dist_eq_norm, Subtype.dist_eq]
      exact (dist_le_pi_dist _ _ j).trans (dist_le_pi_dist A.1 B.1 i)
    have key : PrepBd (δ * dist A B) ((-M0 - W (Matrix.of A.1) * (Matrix.of A.1)) -
        (-M0 - W (Matrix.of B.1) * (Matrix.of B.1))) := by
      have e1 : (-M0 - W (Matrix.of A.1) * (Matrix.of A.1)) - (-M0 - W (Matrix.of B.1) * (Matrix.of B.1)) =
          -((W (Matrix.of A.1) - W (Matrix.of B.1)) * (Matrix.of A.1) +
            W (Matrix.of B.1) * (Matrix.of A.1 - Matrix.of B.1)) := by
        rw [Matrix.sub_mul, Matrix.mul_sub]; abel
      rw [e1]
      refine PrepBd.neg (PrepBd.add ?_ ?_)
      · simpa using PrepBd.mul (mul_nonneg hδ hε) zero_le_one (hW2 _ _ _ hε hA' hB' hAB) hA'
      · exact PrepBd.mul hδ hε (hW _ hB') hAB
    change dist (f A.1) (f B.1) ≤ δ * dist A B
    refine (dist_pi_le_iff (mul_nonneg hδ hε)).2 fun i => (dist_pi_le_iff (mul_nonneg hδ hε)).2 fun j => ?_
    rw [dist_eq_norm]
    exact key i j
  obtain ⟨y, hy, hfix, -⟩ := hc.exists_fixedPoint' hs.isComplete hf (x := 0) (by intro i j; simp) (edist_ne_top _ _)
  refine ⟨Matrix.of y, hy, ?_⟩
  ext i j
  exact (congrFun (congrFun hfix i) j).symm

omit [IsUltrametricDist F] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `hq : (p ^ e) ^ n = p ^ (e * n)` using `(pow_mul p e n).symm`. Simplify using `only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]`. Rewrite using `[pow_succ' (p ^ e) n, pow_mul (x i), hq, sub_pow_char_pow, sum_pow_char_pow]`. Simplify using `only [mul_pow]`.
-/
theorem prep_pow_sub_mulVec (p : ℕ) [Fact p.Prime] [CharP F p] (e n : ℕ) (A : Matrix m m F) (x : m → F) :
    (fun i => (x i ^ p ^ e - A.mulVec x i) ^ (p ^ e) ^ n) =
      (fun i => x i ^ (p ^ e) ^ (n + 1)) - (A.map (fun a => a ^ (p ^ e) ^ n)).mulVec (fun i => x i ^ (p ^ e) ^ n) := by
  funext i
  have hq : (p ^ e) ^ n = p ^ (e * n) := (pow_mul p e n).symm
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [pow_succ' (p ^ e) n, pow_mul (x i), hq, sub_pow_char_pow, sum_pow_char_pow]
  simp only [mul_pow]

omit [IsUltrametricDist F] in
/- English proof (translation)
Unfold `gsum`. Simplify using `only [prep_pow_sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, sum_sub_distrib]`. Rewrite using `[sum_range_succ', sum_range_succ, sum_range_succ', hD, h0]`. Establish `: ∑ n ∈ range D, (U n).mulVec (fun i => x i ^ (p ^ e) ^ (n + 1)) = ∑ n ∈ range D, (M (n + 1)).mulVec (fun i => x i ^ (p ^ e) ^ (n + 1)) + ∑ n ∈ range D, (U (n + 1) * A.map (fun a => a ^ (p ^ e) ^ (n + 1))).mulVec (fun i => x i ^ (p ^ e) ^ (n + 1))`. Rewrite using `[← sum_add_distrib]`.

Use `sum_congr rfl fun n hn => ?_` and prove the remaining obligations. Rewrite using `[← Matrix.add_mulVec, ← hU n (mem_range.1 hn)]`. Rewrite using `[this]`. Establish `hA : A.map (fun a => a ^ (p ^ e) ^ 0) = A` using `by ext i j; simp`. Rewrite using `[hA, Matrix.neg_mulVec, Matrix.zero_mulVec]`.

Normalize the expressions using the abelian group laws.
-/
theorem prep_identity (p : ℕ) [Fact p.Prime] [CharP F p] (e D : ℕ) (M U : ℕ → Matrix m m F) (A : Matrix m m F)
    (hD : U D = 0) (hU : ∀ n, n < D → U n = M (n + 1) + U (n + 1) * A.map (fun a => a ^ (p ^ e) ^ (n + 1)))
    (h0 : M 0 = -(U 0 * A)) (x : m → F) :
    gsum (p ^ e) D M x = gsum (p ^ e) D U (fun i => x i ^ p ^ e - A.mulVec x i) := by
  unfold gsum
  simp only [prep_pow_sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, sum_sub_distrib]
  rw [sum_range_succ', sum_range_succ, sum_range_succ', hD, h0]
  have : ∑ n ∈ range D, (U n).mulVec (fun i => x i ^ (p ^ e) ^ (n + 1)) =
      ∑ n ∈ range D, (M (n + 1)).mulVec (fun i => x i ^ (p ^ e) ^ (n + 1)) +
      ∑ n ∈ range D, (U (n + 1) * A.map (fun a => a ^ (p ^ e) ^ (n + 1))).mulVec
        (fun i => x i ^ (p ^ e) ^ (n + 1)) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    rw [← Matrix.add_mulVec, ← hU n (mem_range.1 hn)]
  rw [this]
  have hA : A.map (fun a => a ^ (p ^ e) ^ 0) = A := by ext i j; simp
  rw [hA, Matrix.neg_mulVec, Matrix.zero_mulVec]
  abel

end Prep

/- English proof (translation)
Introduce `F _ _ _ p _ _ m _ _ e D _ hD M hM`. Choose the witnesses or unpack the hypotheses as in `⟨δ, hδ, hδ1, hMδ⟩ : ∃ δ : ℝ, 0 ≤ δ ∧ δ < 1 ∧ ∀ n, 2 ≤ n → n ≤ D → PrepBd δ (M n) := by`. Set `S : Finset (ℕ × m × m)` to `Icc 2 D ×ˢ univ`. Use `⟨((S.sup fun t => ‖M t.1 t.2.1 t.2.2‖₊ : NNReal) : ℝ), NNReal.coe_nonneg _, ?_, ?_⟩` and prove the remaining obligations. Establish `: (S.sup fun t => ‖M t.1 t.2.1 t.2.2‖₊) < 1`.

Rewrite using `[Finset.sup_lt_iff (by simp)]`. Introduce `t ht`. Establish `h2 : 2 ≤ t.1` using `(mem_Icc.1 (mem_product.1 ht).1).1`. Conclude with `hM.small t.1 (by omega) t.2.1 t.2.2` after adjusting the coercions. Conclude with `this` after adjusting the coercions.

Introduce `n h2 hn i j`. Establish `: ‖M n i j‖₊ ≤ S.sup fun t => ‖M t.1 t.2.1 t.2.2‖₊` using `Finset.le_sup (f := fun t : ℕ × m × m => ‖M t.1 t.2.1 t.2.2‖₊) (b := (n, i, j)) (mem_product.2 ⟨mem_Icc.2 ⟨h2, hn⟩, mem_univ _⟩)`. Conclude with `this` after adjusting the coercions. Take `⟨k, rfl⟩ : ∃ k, D = k + 1` from `⟨D - 1, by omega⟩`. Establish `hW : ∀ A : Matrix m m F, PrepBd 1 A → PrepBd δ (prepV (p ^ e) M A k 1 * A.map (fun a => a ^ (p ^ e) ^ 1))` using `fun A hA => by`.

Use `PrepBd.mul hδ zero_le_one (prepV_bd (q := p ^ e) hδ hMδ hA k 1 le_rfl (by omega)) (hA.map_pow ((p ^ e) ^ 1))` as an intermediate fact. Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis. Take `⟨A, hA, hfix⟩` from `prep_fixed hδ hδ1 (M 0) (hM.int 0) (fun A => prepV (p ^ e) M A k 1 * A.map (fun a => a ^ (p ^ e) ^ 1)) hW (by`. Introduce `A B ε hε hA hB h`. Establish `e1 : prepV (p ^ e) M A k 1 * A.map (fun a => a ^ (p ^ e) ^ 1) - prepV (p ^ e) M B k 1 * B.map (fun a => a ^ (p ^ e) ^ 1) = (prepV (p ^ e) M A k 1 - prepV (p ^ e) M B k 1) * A.map (fun a => a ^ (p ^ e) ^ 1) + prepV (p ^ e) M B k 1 * (A.map (fun a => a ^ (p ^ e) ^ 1) - B.map (fun a …`.

Rewrite using `[Matrix.sub_mul, Matrix.mul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[e1]`. Use `PrepBd.add ?_ ?_` and prove the remaining obligations. Use `PrepBd.mul (mul_nonneg hδ hε) zero_le_one (prepV_sub_bd p (e := e) hδ hε hMδ hA hB h k 1 le_rfl (by omega)) (hA.map_pow ((p ^ e) ^ 1))` as an intermediate fact.

Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis. Conclude with `PrepBd.mul hδ hε (prepV_bd hδ hMδ hB k 1 le_rfl (by omega)) (PrepBd.map_pow_sub p e _ hA hB h))`. Establish `hU0 : prepV (p ^ e) M A (k + 1 - 0) 0 = 1 + prepV (p ^ e) M A k 1 * A.map (fun a => a ^ (p ^ e) ^ 1)`. Rewrite using `[Nat.sub_zero, prepV_succ, zero_add, hM.top]`. Establish `h0 : M 0 = -(prepV (p ^ e) M A (k + 1 - 0) 0 * A)`.

Rewrite using `[hU0, Matrix.add_mul, Matrix.one_mul]`. Use `eq_sub_iff_add_eq.1 hfix` as an intermediate fact. Rewrite using `[this, neg_neg]`. Use `⟨A, fun n => prepV (p ^ e) M A (k + 1 - n) n, hA, ?_, ?_, h0, ?_⟩` and prove the remaining obligations. Introduce `i j beta_reduce`.

Rewrite using `[hU0, add_sub_cancel_left]`. Conclude with `(hW A hA i j).trans_lt hδ1`. Introduce `n hn i j beta_reduce`. Distinguish the cases in `h : n ≤ k + 1`. Conclude with `(prepV_bd hδ hMδ hA _ n hn (by omega) i j).trans_lt hδ1`.

Establish `: k + 1 - n = 0` using `by omega`. Simplify using `[this, prepV_zero]`. Use `prep_identity p e (k + 1) M _ A (by simp [prepV_zero]) (fun n hn => ?_) h0` and prove the remaining obligations. Establish `: k + 1 - n = (k + 1 - (n + 1)) + 1` using `by omega`. Use `beta_reduce`.

Rewrite using `[this, prepV_succ]`.
-/
theorem preparation : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] (p : ℕ)
    [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ), 0 < e → 1 ≤ D →
    ∀ M : ℕ → Matrix m m F, Normal 1 M → ∃ (A : Matrix m m F) (U : ℕ → Matrix m m F), (∀ i j, ‖A i j‖ ≤ 1) ∧
      (∀ i j, ‖(U 0 - 1) i j‖ < 1) ∧ (∀ n, 1 ≤ n → ∀ i j, ‖U n i j‖ < 1) ∧ M 0 = -(U 0 * A) ∧
      ∀ x : m → F, gsum (p ^ e) D M x = gsum (p ^ e) D U (fun i => x i ^ p ^ e - A.mulVec x i) := by
  intro F _ _ _ p _ _ m _ _ e D _ hD M hM
  obtain ⟨δ, hδ, hδ1, hMδ⟩ : ∃ δ : ℝ, 0 ≤ δ ∧ δ < 1 ∧ ∀ n, 2 ≤ n → n ≤ D → PrepBd δ (M n) := by
    let S : Finset (ℕ × m × m) := Icc 2 D ×ˢ univ
    refine ⟨((S.sup fun t => ‖M t.1 t.2.1 t.2.2‖₊ : NNReal) : ℝ), NNReal.coe_nonneg _, ?_, ?_⟩
    · have : (S.sup fun t => ‖M t.1 t.2.1 t.2.2‖₊) < 1 := by
        rw [Finset.sup_lt_iff (by simp)]
        intro t ht
        have h2 : 2 ≤ t.1 := (mem_Icc.1 (mem_product.1 ht).1).1
        exact_mod_cast hM.small t.1 (by omega) t.2.1 t.2.2
      exact_mod_cast this
    · intro n h2 hn i j
      have : ‖M n i j‖₊ ≤ S.sup fun t => ‖M t.1 t.2.1 t.2.2‖₊ :=
        Finset.le_sup (f := fun t : ℕ × m × m => ‖M t.1 t.2.1 t.2.2‖₊) (b := (n, i, j))
          (mem_product.2 ⟨mem_Icc.2 ⟨h2, hn⟩, mem_univ _⟩)
      exact_mod_cast this
  obtain ⟨k, rfl⟩ : ∃ k, D = k + 1 := ⟨D - 1, by omega⟩
  have hW : ∀ A : Matrix m m F, PrepBd 1 A →
      PrepBd δ (prepV (p ^ e) M A k 1 * A.map (fun a => a ^ (p ^ e) ^ 1)) := fun A hA => by
    have := PrepBd.mul hδ zero_le_one (prepV_bd (q := p ^ e) hδ hMδ hA k 1 le_rfl (by omega))
      (hA.map_pow ((p ^ e) ^ 1))
    rwa [mul_one] at this
  obtain ⟨A, hA, hfix⟩ := prep_fixed hδ hδ1 (M 0) (hM.int 0)
    (fun A => prepV (p ^ e) M A k 1 * A.map (fun a => a ^ (p ^ e) ^ 1)) hW (by
      intro A B ε hε hA hB h
      have e1 : prepV (p ^ e) M A k 1 * A.map (fun a => a ^ (p ^ e) ^ 1) -
          prepV (p ^ e) M B k 1 * B.map (fun a => a ^ (p ^ e) ^ 1) =
          (prepV (p ^ e) M A k 1 - prepV (p ^ e) M B k 1) * A.map (fun a => a ^ (p ^ e) ^ 1) +
          prepV (p ^ e) M B k 1 * (A.map (fun a => a ^ (p ^ e) ^ 1) - B.map (fun a => a ^ (p ^ e) ^ 1)) := by
        rw [Matrix.sub_mul, Matrix.mul_sub]; abel
      rw [e1]
      refine PrepBd.add ?_ ?_
      · have := PrepBd.mul (mul_nonneg hδ hε) zero_le_one
          (prepV_sub_bd p (e := e) hδ hε hMδ hA hB h k 1 le_rfl (by omega)) (hA.map_pow ((p ^ e) ^ 1))
        rwa [mul_one] at this
      · exact PrepBd.mul hδ hε (prepV_bd hδ hMδ hB k 1 le_rfl (by omega)) (PrepBd.map_pow_sub p e _ hA hB h))
  have hU0 : prepV (p ^ e) M A (k + 1 - 0) 0 = 1 + prepV (p ^ e) M A k 1 * A.map (fun a => a ^ (p ^ e) ^ 1) := by
    rw [Nat.sub_zero, prepV_succ, zero_add, hM.top]
  have h0 : M 0 = -(prepV (p ^ e) M A (k + 1 - 0) 0 * A) := by
    rw [hU0, Matrix.add_mul, Matrix.one_mul]
    have := eq_sub_iff_add_eq.1 hfix
    rw [this, neg_neg]
  refine ⟨A, fun n => prepV (p ^ e) M A (k + 1 - n) n, hA, ?_, ?_, h0, ?_⟩
  · intro i j
    beta_reduce
    rw [hU0, add_sub_cancel_left]
    exact (hW A hA i j).trans_lt hδ1
  · intro n hn i j
    beta_reduce
    by_cases h : n ≤ k + 1
    · exact (prepV_bd hδ hMδ hA _ n hn (by omega) i j).trans_lt hδ1
    · have : k + 1 - n = 0 := by omega
      simp [this, prepV_zero]
  · refine prep_identity p e (k + 1) M _ A (by simp [prepV_zero]) (fun n hn => ?_) h0
    have : k + 1 - n = (k + 1 - (n + 1)) + 1 := by omega
    beta_reduce
    rw [this, prepV_succ]

end GlobalTheory.PMonE

end
