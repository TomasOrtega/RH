import Formalism.LocalToGlobal.CMDeterminantIdeals.CmNumbersLink

noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder

def IndexFormula : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (M : Submodule (𝓞 K) (Fin m → K)) (b : Fin m → Fin m → K),
    M.FG → Submodule.span K (M : Set (Fin m → K)) = ⊤ → LinearIndependent K b → (∀ i, b i ∈ M) →
    ((FractionalIdeal.absNorm (MLat.mk (Submodule.span (𝓞 K) (Set.range b)) (fun _ => 0) : MLat K m).detIdeal : ℚ) : ℝ) =
      ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex M.toAddSubgroup : ℝ) *
        ((FractionalIdeal.absNorm (MLat.mk M (fun _ => 0) : MLat K m).detIdeal : ℚ) : ℝ)

/- English proof (translation)
Introduce `hIF K _ _ m L b hL hb`. Use `set M0 := Submodule.span (𝓞 K) (Set.range b) with hM0`. Set `L0 : MLat K m` to `⟨M0, L.H⟩`. Establish `hspan : Submodule.span K (Set.range b) = ⊤`. Break down `isEmpty_or_nonempty (Fin m) with hm | hm` into its components or cases.

Conclude with `eq_top_iff.2 fun x _ => by rw [Subsingleton.elim x 0]; exact zero_mem _`. Conclude with `hb.2.1.span_eq_top_of_card_eq_finrank (by simp)`. Establish `hL0 : L0.Good`. Use `⟨Submodule.fg_span (Set.finite_range b), ?_, hL.2.2⟩` and prove the remaining obligations. Use `show Submodule.span K ((M0 : Set (Fin m → K))) = ⊤`.

Rewrite using `[hM0, Submodule.span_span_of_tower]`. Conclude with `hspan`. Establish `hfree` using `detLineFree K m L0 b hL0 rfl`. Establish `hI` using `hIF K m L.M b hL.1 hL.2.1 hb.2.1 hb.1`. Establish `e0 : (MLat.mk M0 (fun _ => 0) : MLat K m).detIdeal = L0.detIdeal` using `rfl`.

Establish `e1 : (MLat.mk L.M (fun _ => 0) : MLat K m).detIdeal = L.detIdeal` using `rfl`. Rewrite `hI` using `[e0, e1]`. Establish `hpos0 : (0 : ℝ) < ((FractionalIdeal.absNorm L0.detIdeal : ℚ) : ℝ)`. Conclude with `A2.absNorm_pos' (A2.detIdeal_ne_zero L0 hL0)` after adjusting the coercions. Establish `hpos : (0 : ℝ) < ((FractionalIdeal.absNorm L.detIdeal : ℚ) : ℝ)`.

Conclude with `A2.absNorm_pos' (A2.detIdeal_ne_zero L hL)` after adjusting the coercions. Establish `hrel : (0 : ℝ) < (M0.toAddSubgroup.relIndex L.M.toAddSubgroup : ℝ)`. Break down `(Nat.cast_nonneg (α := ℝ) (M0.toAddSubgroup.relIndex L.M.toAddSubgroup)).lt_or_eq with h | h` into its components or cases. Conclude with `h`. Rewrite `hI` using `[← h, zero_mul]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hfree`, the goal using `[A2.deg_detLine]`. Establish `hlog : Real.log ((FractionalIdeal.absNorm L0.detIdeal : ℚ) : ℝ) = Real.log (M0.toAddSubgroup.relIndex L.M.toAddSubgroup : ℝ) + Real.log ((FractionalIdeal.absNorm L.detIdeal : ℚ) : ℝ)`. Rewrite using `[hI, Real.log_mul hrel.ne' hpos.ne']`. Establish `hH : L0.H = L.H` using `rfl`.

Rewrite `hfree` using `[hH]`. Unfold `ReciprocityTheory.MultiplicativeHeights.latDeg`. Rewrite using `[← hM0]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem DetLatDeg_of : IndexFormula → DetLatDeg := by
  intro hIF K _ _ m L b hL hb
  set M0 := Submodule.span (𝓞 K) (Set.range b) with hM0
  let L0 : MLat K m := ⟨M0, L.H⟩
  have hspan : Submodule.span K (Set.range b) = ⊤ := by
    rcases isEmpty_or_nonempty (Fin m) with hm | hm
    · exact eq_top_iff.2 fun x _ => by rw [Subsingleton.elim x 0]; exact zero_mem _
    · exact hb.2.1.span_eq_top_of_card_eq_finrank (by simp)
  have hL0 : L0.Good := by
    refine ⟨Submodule.fg_span (Set.finite_range b), ?_, hL.2.2⟩
    show Submodule.span K ((M0 : Set (Fin m → K))) = ⊤
    rw [hM0, Submodule.span_span_of_tower]
    exact hspan
  have hfree := detLineFree K m L0 b hL0 rfl
  have hI := hIF K m L.M b hL.1 hL.2.1 hb.2.1 hb.1
  have e0 : (MLat.mk M0 (fun _ => 0) : MLat K m).detIdeal = L0.detIdeal := rfl
  have e1 : (MLat.mk L.M (fun _ => 0) : MLat K m).detIdeal = L.detIdeal := rfl
  rw [e0, e1] at hI
  have hpos0 : (0 : ℝ) < ((FractionalIdeal.absNorm L0.detIdeal : ℚ) : ℝ) := by
    exact_mod_cast A2.absNorm_pos' (A2.detIdeal_ne_zero L0 hL0)
  have hpos : (0 : ℝ) < ((FractionalIdeal.absNorm L.detIdeal : ℚ) : ℝ) := by
    exact_mod_cast A2.absNorm_pos' (A2.detIdeal_ne_zero L hL)
  have hrel : (0 : ℝ) < (M0.toAddSubgroup.relIndex L.M.toAddSubgroup : ℝ) := by
    rcases (Nat.cast_nonneg (α := ℝ) (M0.toAddSubgroup.relIndex L.M.toAddSubgroup)).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hI; linarith
  rw [A2.deg_detLine] at hfree ⊢
  have hlog : Real.log ((FractionalIdeal.absNorm L0.detIdeal : ℚ) : ℝ) =
      Real.log (M0.toAddSubgroup.relIndex L.M.toAddSubgroup : ℝ) + Real.log ((FractionalIdeal.absNorm L.detIdeal : ℚ) : ℝ) := by
    rw [hI, Real.log_mul hrel.ne' hpos.ne']
  have hH : L0.H = L.H := rfl
  rw [hH] at hfree
  unfold ReciprocityTheory.MultiplicativeHeights.latDeg
  rw [← hM0]
  linarith

namespace Dx

variable {K : Type} [Field K] [NumberField K]

def dS {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K) K :=
  Submodule.span (𝓞 K) {d | ∃ x : Fin n → Fin n → K, (∀ i, x i ∈ M) ∧ d = (Matrix.of x).det}

def lastL (K : Type) [Field K] [NumberField K] (n : ℕ) : (Fin (n+1) → K) →ₗ[𝓞 K] K :=
  LinearMap.proj (Fin.last n)

def snocL (K : Type) [Field K] [NumberField K] (n : ℕ) : (Fin n → K) →ₗ[𝓞 K] (Fin (n+1) → K) where
  toFun w := Fin.snoc (α := fun _ => K) w 0
  map_add' u v := by
    ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' c u := by
    ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/- English proof (translation)
Simplify using `[snocL]`.
-/
@[simp] theorem snocL_castSucc {n : ℕ} (w : Fin n → K) (j : Fin n) : snocL K n w (Fin.castSucc j) = w j := by
  simp [snocL]

/- English proof (translation)
Simplify using `[snocL]`.
-/
@[simp] theorem snocL_last {n : ℕ} (w : Fin n → K) : snocL K n w (Fin.last n) = 0 := by
  simp [snocL]

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem lastL_apply {n : ℕ} (v : Fin (n+1) → K) : lastL K n v = v (Fin.last n) := rfl

/- English proof (translation)
Rewrite using `[Submodule.mul_le]`. Introduce `p hp q hq`. Take `⟨v, hv, rfl⟩` from `hq`. Proceed by induction on `hp using Submodule.span_induction with`. Consider the case `mem d hd`.

Take `⟨y, hy, rfl⟩` from `hd`. Apply `Submodule.subset_span` to reduce the goal to its premises. Set `X : Fin (n+1) → Fin (n+1) → K` to `Fin.snoc (α := fun _ => Fin (n+1) → K) (fun i => snocL K n (y i)) v`. Use `⟨X, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`.

Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify `hv` using `[X]`. Simplify `hy j` using `[X]`. Establish `hsub : (Matrix.of X).submatrix (Fin.last n).succAbove (Fin.last n).succAbove = Matrix.of y`. Use extensionality with `i j`.

Simplify using `[X, Fin.succAbove_last]`. Rewrite using `[Matrix.det_succ_column _ (Fin.last n), Fin.sum_univ_castSucc, hsub]`. Establish `h0 : ∀ i : Fin n, Matrix.of X (Fin.castSucc i) (Fin.last n) = 0` using `fun i => by simp [X]`. Simplify using `only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]`. Establish `hl : Matrix.of X (Fin.last n) (Fin.last n) = v (Fin.last n)` using `by simp [X]`.

Rewrite using `[hl, Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, lastL_apply, mul_comm]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [add_mul]`. Conclude with `add_mem hx hy`. Consider the case `smul r x _ hx => rw [smul_mul_assoc]`.

Conclude with `Submodule.smul_mem _ r hx`.
-/
theorem dS_mul_le {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) :
    dS (M.comap (snocL K n)) * M.map (lastL K n) ≤ dS M := by
  rw [Submodule.mul_le]
  intro p hp q hq
  obtain ⟨v, hv, rfl⟩ := hq
  induction hp using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨y, hy, rfl⟩ := hd
    apply Submodule.subset_span
    let X : Fin (n+1) → Fin (n+1) → K := Fin.snoc (α := fun _ => Fin (n+1) → K) (fun i => snocL K n (y i)) v
    refine ⟨X, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [X] using hv
      · simpa [X] using hy j
    · have hsub : (Matrix.of X).submatrix (Fin.last n).succAbove (Fin.last n).succAbove = Matrix.of y := by
        ext i j; simp [X, Fin.succAbove_last]
      rw [Matrix.det_succ_column _ (Fin.last n), Fin.sum_univ_castSucc, hsub]
      have h0 : ∀ i : Fin n, Matrix.of X (Fin.castSucc i) (Fin.last n) = 0 := fun i => by simp [X]
      simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
      have hl : Matrix.of X (Fin.last n) (Fin.last n) = v (Fin.last n) := by simp [X]
      rw [hl, Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, lastL_apply, mul_comm]
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

/- English proof (translation)
Rewrite using `[dS, Submodule.span_le]`. Introduce and unpack `d ⟨x, hx, rfl⟩`. Use `set E : Matrix (Fin (n+1)) (Fin (n+1)) K := 1 + Matrix.replicateCol Unit (-(Pi.single (Fin.last n) (1 : K) : Fin (n+1) → K)) * Matrix.replicateRow Unit (z - (Pi.single (Fin.last n) (1 : K) : Fin (n+1) → K)) with hE`. Establish `hEdet : E.det = 1`. Rewrite using `[hE, Matrix.det_one_add_replicateCol_mul_replicateRow]`.

Simplify using `[dotProduct, Pi.single_apply, hz1]`. Establish `hY : ∀ i k, (Matrix.of x * E) i k = if k = Fin.last n then x i (Fin.last n) else x i k - x i (Fin.last n) * z k`. Introduce `i k`. Simplify using `[hE, Matrix.mul_apply, Pi.single_apply]`. Rewrite using `[Finset.sum_congr rfl (fun j _ => mul_add _ _ _), Finset.sum_add_distrib]`.

Simplify using `only [Matrix.one_apply, mul_ite, mul_one, mul_zero, mul_neg, Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Use `split_ifs with hk`. Substitute `hk` using the available equality. Simplify using `[hz1]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hdet : (Matrix.of x).det = (Matrix.of x * E).det` using `by rw [Matrix.det_mul, hEdet, mul_one]`. Rewrite using `[SetLike.mem_coe, hdet, Matrix.det_succ_column _ (Fin.last n)]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `hxl : x i (Fin.last n) ∈ M.map (lastL K n)` using `⟨x i, hx i, rfl⟩`. Set `u : Fin (n+1) → Fin (n+1) → K` to `fun l => x l - x l (Fin.last n) • z`.

Establish `hu : ∀ l, (fun k : Fin n => u l (Fin.castSucc k)) ∈ M.comap (snocL K n)`. Introduce `l`. Use `show snocL K n _ ∈ M`. Establish `: snocL K n (fun k : Fin n => u l (Fin.castSucc k)) = u l`. Apply the tactic sequence `ext k; refine Fin.lastCases ?_ (fun j => ?_) k <;> simp [u, hz1]`.

Rewrite using `[this]`. Conclude with `M.sub_mem (hx l) (hz _ ⟨x l, hx l, rfl⟩)`. Establish `hmin : ((Matrix.of x * E).submatrix i.succAbove (Fin.last n).succAbove).det ∈ dS (M.comap (snocL K n))`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨fun j k => u (i.succAbove j) (Fin.castSucc k), fun j => hu _, ?_⟩` and prove the remaining obligations.

Use `congr 1`. Use extensionality with `j k`. Simplify using `[hY, Fin.succAbove_last, u, (Fin.castSucc_lt_last k).ne]`. Rewrite using `[hY, if_pos rfl]`. Break down `neg_one_pow_eq_or K ((i : ℕ) + (Fin.last n : ℕ)) with h | h` into its components or cases.

Use `Submodule.mul_mem_mul hmin hxl using 1` and compare the differences between its conclusion and the goal. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Use `Submodule.neg_mem _ (Submodule.mul_mem_mul hmin hxl) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[h]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dS_le_mul {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) (z : Fin (n+1) → K) (hz1 : z (Fin.last n) = 1)
    (hz : ∀ q ∈ M.map (lastL K n), q • z ∈ M) :
    dS M ≤ dS (M.comap (snocL K n)) * M.map (lastL K n) := by
  rw [dS, Submodule.span_le]
  rintro d ⟨x, hx, rfl⟩
  set E : Matrix (Fin (n+1)) (Fin (n+1)) K := 1 + Matrix.replicateCol Unit (-(Pi.single (Fin.last n) (1 : K) : Fin (n+1) → K)) *
    Matrix.replicateRow Unit (z - (Pi.single (Fin.last n) (1 : K) : Fin (n+1) → K)) with hE
  have hEdet : E.det = 1 := by
    rw [hE, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp [dotProduct, Pi.single_apply, hz1]
  have hY : ∀ i k, (Matrix.of x * E) i k =
      if k = Fin.last n then x i (Fin.last n) else x i k - x i (Fin.last n) * z k := by
    intro i k
    simp [hE, Matrix.mul_apply, Pi.single_apply]
    rw [Finset.sum_congr rfl (fun j _ => mul_add _ _ _), Finset.sum_add_distrib]
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, mul_neg, Finset.sum_neg_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    split_ifs with hk
    · subst hk; simp [hz1]
    · ring
  have hdet : (Matrix.of x).det = (Matrix.of x * E).det := by rw [Matrix.det_mul, hEdet, mul_one]
  rw [SetLike.mem_coe, hdet, Matrix.det_succ_column _ (Fin.last n)]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hxl : x i (Fin.last n) ∈ M.map (lastL K n) := ⟨x i, hx i, rfl⟩
  let u : Fin (n+1) → Fin (n+1) → K := fun l => x l - x l (Fin.last n) • z
  have hu : ∀ l, (fun k : Fin n => u l (Fin.castSucc k)) ∈ M.comap (snocL K n) := by
    intro l
    show snocL K n _ ∈ M
    have : snocL K n (fun k : Fin n => u l (Fin.castSucc k)) = u l := by
      ext k; refine Fin.lastCases ?_ (fun j => ?_) k <;> simp [u, hz1]
    rw [this]
    exact M.sub_mem (hx l) (hz _ ⟨x l, hx l, rfl⟩)
  have hmin : ((Matrix.of x * E).submatrix i.succAbove (Fin.last n).succAbove).det ∈ dS (M.comap (snocL K n)) := by
    apply Submodule.subset_span
    refine ⟨fun j k => u (i.succAbove j) (Fin.castSucc k), fun j => hu _, ?_⟩
    congr 1; ext j k
    simp [hY, Fin.succAbove_last, u, (Fin.castSucc_lt_last k).ne]
  rw [hY, if_pos rfl]
  rcases neg_one_pow_eq_or K ((i : ℕ) + (Fin.last n : ℕ)) with h | h
  · convert Submodule.mul_mem_mul hmin hxl using 1; rw [h]; ring
  · convert Submodule.neg_mem _ (Submodule.mul_mem_mul hmin hxl) using 1; rw [h]; ring

/- English proof (translation)
Use `set Z := f.ker`. Establish `hmod : (A' ⊔ Z) ⊓ A = A' ⊔ (A ⊓ Z)`. Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_inf, AddSubgroup.mem_sup]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨y, hy, z, hz, rfl⟩, hx⟩`. Conclude with `⟨y, hy, z, ⟨by simpa using A.sub_mem hx (hA hy), hz⟩, rfl⟩`. Introduce and unpack `⟨y, hy, z, ⟨hzA, hz⟩, rfl⟩`. Conclude with `⟨⟨y, hy, z, hz, rfl⟩, A.add_mem (hA hy) hzA⟩`. Establish `h1 : A'.relIndex (A' ⊔ (A ⊓ Z)) = (A' ⊓ Z).relIndex (A ⊓ Z)`.

Rewrite using `[sup_comm, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right A' (A ⊓ Z), ← AddSubgroup.inf_relIndex_right (A' ⊓ Z) (A ⊓ Z)]`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_inf]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h, h2, h3⟩`. Conclude with `⟨⟨h, h3⟩, h2, h3⟩`. Introduce and unpack `⟨⟨h, h3⟩, h2, _⟩`. Conclude with `⟨h, h2, h3⟩`. Establish `h2 : (A' ⊔ (A ⊓ Z)).relIndex A = (A'.map f).relIndex (A.map f)`.

Rewrite using `[AddSubgroup.relIndex_map_map]`. Establish `e : A ⊔ f.ker = A ⊔ (A' ⊔ f.ker)`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `sup_le le_sup_left (le_trans le_sup_right le_sup_right)`. Conclude with `sup_le le_sup_left (sup_le (le_trans hA le_sup_left) le_sup_right)`.

Rewrite using `[e, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right (A' ⊔ f.ker) A]`. Use `show _ = ((A' ⊔ Z) ⊓ A).relIndex A`. Rewrite using `[hmod]`. Rewrite using `[← AddSubgroup.relIndex_mul_relIndex A' (A' ⊔ (A ⊓ Z)) A le_sup_left (sup_le hA inf_le_left), h1, h2]`.
-/
theorem idx {G H : Type*} [AddCommGroup G] [AddCommGroup H] (A' A : AddSubgroup G) (hA : A' ≤ A) (f : G →+ H) :
    A'.relIndex A = (A' ⊓ f.ker).relIndex (A ⊓ f.ker) * (A'.map f).relIndex (A.map f) := by
  set Z := f.ker
  have hmod : (A' ⊔ Z) ⊓ A = A' ⊔ (A ⊓ Z) := by
    ext x
    simp only [AddSubgroup.mem_inf, AddSubgroup.mem_sup]
    constructor
    · rintro ⟨⟨y, hy, z, hz, rfl⟩, hx⟩
      exact ⟨y, hy, z, ⟨by simpa using A.sub_mem hx (hA hy), hz⟩, rfl⟩
    · rintro ⟨y, hy, z, ⟨hzA, hz⟩, rfl⟩
      exact ⟨⟨y, hy, z, hz, rfl⟩, A.add_mem (hA hy) hzA⟩
  have h1 : A'.relIndex (A' ⊔ (A ⊓ Z)) = (A' ⊓ Z).relIndex (A ⊓ Z) := by
    rw [sup_comm, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right A' (A ⊓ Z),
      ← AddSubgroup.inf_relIndex_right (A' ⊓ Z) (A ⊓ Z)]
    congr 1
    ext x; simp only [AddSubgroup.mem_inf]
    constructor
    · rintro ⟨h, h2, h3⟩; exact ⟨⟨h, h3⟩, h2, h3⟩
    · rintro ⟨⟨h, h3⟩, h2, _⟩; exact ⟨h, h2, h3⟩
  have h2 : (A' ⊔ (A ⊓ Z)).relIndex A = (A'.map f).relIndex (A.map f) := by
    rw [AddSubgroup.relIndex_map_map]
    have e : A ⊔ f.ker = A ⊔ (A' ⊔ f.ker) := by
      apply le_antisymm
      · exact sup_le le_sup_left (le_trans le_sup_right le_sup_right)
      · exact sup_le le_sup_left (sup_le (le_trans hA le_sup_left) le_sup_right)
    rw [e, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right (A' ⊔ f.ker) A]
    show _ = ((A' ⊔ Z) ⊓ A).relIndex A
    rw [hmod]
  rw [← AddSubgroup.relIndex_mul_relIndex A' (A' ⊔ (A ⊓ Z)) A le_sup_left (sup_le hA inf_le_left), h1, h2]

/- English proof (translation)
Establish `hJ : J ≠ 0` using `by rintro rfl; exact hJ' (FractionalIdeal.le_zero_iff.1 hle)`. Establish `hX : J' * J⁻¹ ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Take `⟨X, hX'⟩` from `FractionalIdeal.le_one_iff_exists_coeIdeal.1 hX`. Establish `hdec : J' = J * (X : FractionalIdeal (𝓞 K)⁰ K)`.

Rewrite using `[hX', mul_comm J', ← mul_assoc, mul_inv_cancel₀ hJ, one_mul]`. Take `⟨c, P, hc, hP⟩` from `FractionalIdeal.exists_eq_spanSingleton_mul J`. Set `φ : 𝓞 K →+ K` to `(AddMonoidHom.mulLeft ((algebraMap (𝓞 K) K c)⁻¹)).comp (algebraMap (𝓞 K) K).toAddMonoidHom`. Establish `hc' : (algebraMap (𝓞 K) K c)⁻¹ ≠ 0` using `inv_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hc)`. Establish `hφ : Function.Injective φ`.

Introduce `r s h`. Establish `h' : (algebraMap (𝓞 K) K c)⁻¹ * algebraMap (𝓞 K) K r = (algebraMap (𝓞 K) K c)⁻¹ * algebraMap (𝓞 K) K s` using `h`. Conclude with `IsFractionRing.injective (𝓞 K) K (mul_left_cancel₀ hc' h')`. Establish `hmap : ∀ Q : Ideal (𝓞 K), ((FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K c)⁻¹ * (Q : FractionalIdeal (𝓞 K)⁰ K) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).toAddSubgroup = Q.toAddSubgroup.map φ`. Introduce `Q`.

Use extensionality with `x`. Simplify using `only [Submodule.mem_toAddSubgroup, FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton, Submodule.mem_span_singleton_mul, AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Take `⟨r, hr, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hz`.

Conclude with `⟨r, hr, rfl⟩`. Introduce and unpack `⟨r, hr, rfl⟩`. Conclude with `⟨algebraMap (𝓞 K) K r, (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩, rfl⟩`. Establish `hJ'P : J' = FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K c)⁻¹ * ((P * X : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)`. Rewrite using `[hdec, hP, FractionalIdeal.coeIdeal_mul, mul_assoc]`.

Establish `hrel : (J' : Submodule (𝓞 K) K).toAddSubgroup.relIndex (J : Submodule (𝓞 K) K).toAddSubgroup = (P * X).toAddSubgroup.relIndex P.toAddSubgroup`. Rewrite using `[hJ'P, hmap, hP, hmap, AddSubgroup.relIndex_map_map_of_injective _ _ hφ]`. Establish `hPX : P * X ≤ P` using `by simpa [mul_comm] using (Ideal.mul_le_right : X * P ≤ P)`. Establish `htow` using `AddSubgroup.relIndex_mul_relIndex (P * X).toAddSubgroup P.toAddSubgroup ⊤ hPX le_top`. Rewrite `htow` using `[AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_top_right]`.

Establish `hn : ∀ Q : Ideal (𝓞 K), Ideal.absNorm Q = Q.toAddSubgroup.index` using `fun Q => by`. Rewrite using `[Ideal.absNorm_apply]`. Both sides reduce to the same expression. Establish `hmul : Ideal.absNorm (P * X) = Ideal.absNorm P * Ideal.absNorm X` using `map_mul _ _ _`. Rewrite `hmul` using `[hn, hn, hn]`.

Establish `hP0 : P.toAddSubgroup.index ≠ 0`. Rewrite using `[← hn]`. Introduce `h`. Apply `hJ` to reduce the goal to its premises. Rewrite using `[hP, Ideal.absNorm_eq_zero_iff.1 h, FractionalIdeal.coeIdeal_bot, mul_zero]`.

Establish `hidx : (P * X).toAddSubgroup.relIndex P.toAddSubgroup = Ideal.absNorm X`. Rewrite using `[hn X]`. Apply `Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hP0)` to reduce the goal to its premises. Rewrite using `[htow, hmul, mul_comm]`. Rewrite using `[hrel, hidx, hdec, map_mul, FractionalIdeal.coeIdeal_absNorm, mul_comm]`.
-/
theorem absNorm_eq_relIndex_mul (J J' : FractionalIdeal (𝓞 K)⁰ K) (hJ' : J' ≠ 0) (hle : J' ≤ J) :
    FractionalIdeal.absNorm J' = ((J' : Submodule (𝓞 K) K).toAddSubgroup.relIndex
      (J : Submodule (𝓞 K) K).toAddSubgroup : ℚ) * FractionalIdeal.absNorm J := by
  have hJ : J ≠ 0 := by rintro rfl; exact hJ' (FractionalIdeal.le_zero_iff.1 hle)
  have hX : J' * J⁻¹ ≤ 1 := by
    calc J' * J⁻¹ ≤ J * J⁻¹ := mul_le_mul' hle le_rfl
      _ = 1 := mul_inv_cancel₀ hJ
  obtain ⟨X, hX'⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hX
  have hdec : J' = J * (X : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hX', mul_comm J', ← mul_assoc, mul_inv_cancel₀ hJ, one_mul]
  obtain ⟨c, P, hc, hP⟩ := FractionalIdeal.exists_eq_spanSingleton_mul J
  let φ : 𝓞 K →+ K := (AddMonoidHom.mulLeft ((algebraMap (𝓞 K) K c)⁻¹)).comp (algebraMap (𝓞 K) K).toAddMonoidHom
  have hc' : (algebraMap (𝓞 K) K c)⁻¹ ≠ 0 :=
    inv_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hc)
  have hφ : Function.Injective φ := by
    intro r s h
    have h' : (algebraMap (𝓞 K) K c)⁻¹ * algebraMap (𝓞 K) K r = (algebraMap (𝓞 K) K c)⁻¹ * algebraMap (𝓞 K) K s := h
    exact IsFractionRing.injective (𝓞 K) K (mul_left_cancel₀ hc' h')
  have hmap : ∀ Q : Ideal (𝓞 K), ((FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K c)⁻¹ *
      (Q : FractionalIdeal (𝓞 K)⁰ K) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).toAddSubgroup =
      Q.toAddSubgroup.map φ := by
    intro Q
    ext x
    simp only [Submodule.mem_toAddSubgroup, FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton,
      Submodule.mem_span_singleton_mul, AddSubgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
      exact ⟨r, hr, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨algebraMap (𝓞 K) K r, (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩, rfl⟩
  have hJ'P : J' = FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K c)⁻¹ *
      ((P * X : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hdec, hP, FractionalIdeal.coeIdeal_mul, mul_assoc]
  have hrel : (J' : Submodule (𝓞 K) K).toAddSubgroup.relIndex (J : Submodule (𝓞 K) K).toAddSubgroup =
      (P * X).toAddSubgroup.relIndex P.toAddSubgroup := by
    rw [hJ'P, hmap, hP, hmap, AddSubgroup.relIndex_map_map_of_injective _ _ hφ]
  have hPX : P * X ≤ P := by simpa [mul_comm] using (Ideal.mul_le_right : X * P ≤ P)
  have htow := AddSubgroup.relIndex_mul_relIndex (P * X).toAddSubgroup P.toAddSubgroup ⊤ hPX le_top
  rw [AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_top_right] at htow
  have hn : ∀ Q : Ideal (𝓞 K), Ideal.absNorm Q = Q.toAddSubgroup.index := fun Q => by
    rw [Ideal.absNorm_apply]; rfl
  have hmul : Ideal.absNorm (P * X) = Ideal.absNorm P * Ideal.absNorm X := map_mul _ _ _
  rw [hn, hn, hn] at hmul
  have hP0 : P.toAddSubgroup.index ≠ 0 := by
    rw [← hn]
    intro h
    apply hJ
    rw [hP, Ideal.absNorm_eq_zero_iff.1 h, FractionalIdeal.coeIdeal_bot, mul_zero]
  have hidx : (P * X).toAddSubgroup.relIndex P.toAddSubgroup = Ideal.absNorm X := by
    rw [hn X]
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hP0)
    rw [htow, hmul, mul_comm]
  rw [hrel, hidx, hdec, map_mul, FractionalIdeal.coeIdeal_absNorm, mul_comm]

def Sand {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) : Prop :=
  (∃ a : 𝓞 K, a ≠ 0 ∧ ∀ i, (Pi.single i (algebraMap (𝓞 K) K a) : Fin n → K) ∈ M) ∧
    ∃ b ∈ (𝓞 K)⁰, ∀ x ∈ M, ∀ i, IsLocalization.IsInteger (𝓞 K) (b • x i)

def fiD {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) : FractionalIdeal (𝓞 K)⁰ K :=
  (MLat.mk M (fun _ => 0) : MLat K n).detIdeal

/- English proof (translation)
Take `⟨a, ha, hint⟩` from `hM.2`. Use `⟨a ^ n, pow_mem ha n, fun b hb => ?_⟩` and prove the remaining obligations. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem d hd`. Take `⟨x, hx, rfl⟩` from `hd`.

Establish `: (a ^ n) • (Matrix.of x).det = (Matrix.of fun i j => a • x i j).det`. Rewrite using `[show (Matrix.of fun i j => a • x i j) = (algebraMap (𝓞 K) K a) • Matrix.of x by`. Use extensionality with `i j`. Simplify using `[Algebra.smul_def]]`. Rewrite using `[Matrix.det_smul, Fintype.card_fin, Algebra.smul_def, map_pow]`.

Rewrite using `[this]`. Conclude with `A2.isInteger_det _ fun i j => hint _ (hx i) j`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `IsLocalization.isInteger_add hx hy`.

Consider the case `smul r x _ hx => rw [smul_comm]`. Conclude with `IsLocalization.isInteger_smul hx`.
-/
theorem dS_isFractional {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) (hM : Sand M) : IsFractional (𝓞 K)⁰ (dS M) := by
  obtain ⟨a, ha, hint⟩ := hM.2
  refine ⟨a ^ n, pow_mem ha n, fun b hb => ?_⟩
  induction hb using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨x, hx, rfl⟩ := hd
    have : (a ^ n) • (Matrix.of x).det = (Matrix.of fun i j => a • x i j).det := by
      rw [show (Matrix.of fun i j => a • x i j) = (algebraMap (𝓞 K) K a) • Matrix.of x by
        ext i j; simp [Algebra.smul_def]]
      rw [Matrix.det_smul, Fintype.card_fin, Algebra.smul_def, map_pow]
    rw [this]
    exact A2.isInteger_det _ fun i j => hint _ (hx i) j
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy => rw [smul_add]; exact IsLocalization.isInteger_add hx hy
  | smul r x _ hx => rw [smul_comm]; exact IsLocalization.isInteger_smul hx

/- English proof (translation)
The claim follows from `A2.detIdeal_coe _ (dS_isFractional M hM)`.
-/
theorem coe_fiD {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) (hM : Sand M) : (fiD M : Submodule (𝓞 K) K) = dS M :=
  A2.detIdeal_coe _ (dS_isFractional M hM)

/- English proof (translation)
Take `⟨a, ha, hs⟩` from `hM.1`. Introduce `h0`. Establish `hmem : (Matrix.of fun i => (Pi.single i (algebraMap (𝓞 K) K a) : Fin n → K)).det ∈ (fiD M : Submodule (𝓞 K) K)`. Rewrite using `[coe_fiD M hM]`. Conclude with `Submodule.subset_span ⟨_, hs, rfl⟩`.

Rewrite `hmem` using `[h0]`. Establish `hdiag : (Matrix.of fun i => (Pi.single i (algebraMap (𝓞 K) K a) : Fin n → K)) = Matrix.diagonal fun _ => algebraMap (𝓞 K) K a`. Use extensionality with `i j`. Simplify using `[Pi.single_apply, Matrix.diagonal_apply, eq_comm]`. Rewrite `hmem` using `[hdiag, Matrix.det_diagonal, Finset.prod_const]`.

Use `(FractionalIdeal.mem_zero_iff _).1 hmem` as an intermediate fact. Conclude with `pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 ha) this`.
-/
theorem fiD_ne_zero {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) (hM : Sand M) : fiD M ≠ 0 := by
  obtain ⟨a, ha, hs⟩ := hM.1
  intro h0
  have hmem : (Matrix.of fun i => (Pi.single i (algebraMap (𝓞 K) K a) : Fin n → K)).det ∈ (fiD M : Submodule (𝓞 K) K) := by
    rw [coe_fiD M hM]; exact Submodule.subset_span ⟨_, hs, rfl⟩
  rw [h0] at hmem
  have hdiag : (Matrix.of fun i => (Pi.single i (algebraMap (𝓞 K) K a) : Fin n → K)) =
      Matrix.diagonal fun _ => algebraMap (𝓞 K) K a := by
    ext i j; simp [Pi.single_apply, Matrix.diagonal_apply, eq_comm]
  rw [hdiag, Matrix.det_diagonal, Finset.prod_const] at hmem
  have := (FractionalIdeal.mem_zero_iff _).1 hmem
  exact pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 ha) this

/- English proof (translation)
Take `⟨⟨a, ha, hs⟩, ⟨b, hb, hint⟩⟩` from `hM`. Use `⟨⟨a, ha, fun i => ?_⟩, ⟨b, hb, fun x hx i => ?_⟩⟩` and prove the remaining obligations. Use `show snocL K n _ ∈ M`. Establish `: snocL K n (Pi.single i (algebraMap (𝓞 K) K a)) = Pi.single (Fin.castSucc i) (algebraMap (𝓞 K) K a)`. Use extensionality with `k`.

Use `Fin.lastCases ?_ (fun j => ?_) k` and prove the remaining obligations. Simplify using `[(Fin.castSucc_lt_last i).ne']`. Simplify using `[Pi.single_apply, Fin.castSucc_inj]`. Rewrite using `[this]`. Conclude with `hs _`.

Use `hint _ hx (Fin.castSucc i)` as an intermediate fact. Simplify using `using this`.
-/
theorem sand_comap {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) (hM : Sand M) : Sand (M.comap (snocL K n)) := by
  obtain ⟨⟨a, ha, hs⟩, ⟨b, hb, hint⟩⟩ := hM
  refine ⟨⟨a, ha, fun i => ?_⟩, ⟨b, hb, fun x hx i => ?_⟩⟩
  · show snocL K n _ ∈ M
    have : snocL K n (Pi.single i (algebraMap (𝓞 K) K a)) = Pi.single (Fin.castSucc i) (algebraMap (𝓞 K) K a) := by
      ext k; refine Fin.lastCases ?_ (fun j => ?_) k
      · simp [(Fin.castSucc_lt_last i).ne']
      · simp [Pi.single_apply, Fin.castSucc_inj]
    rw [this]; exact hs _
  · have := hint _ hx (Fin.castSucc i)
    simpa using this

/- English proof (translation)
Take `⟨b, hb, hint⟩` from `hM.2`. Use `⟨b, hb, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨v, hv, rfl⟩` from `hy`. Conclude with `hint v hv _`.
-/
theorem frac_map {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) (hM : Sand M) :
    IsFractional (𝓞 K)⁰ (M.map (lastL K n)) := by
  obtain ⟨b, hb, hint⟩ := hM.2
  refine ⟨b, hb, fun y hy => ?_⟩
  obtain ⟨v, hv, rfl⟩ := hy
  exact hint v hv _

def imI {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) (hM : Sand M) : FractionalIdeal (𝓞 K)⁰ K :=
  ⟨M.map (lastL K n), frac_map M hM⟩

/- English proof (translation)
Take `⟨a, ha, hs⟩` from `hM.1`. Introduce `h0`. Establish `hmem : algebraMap (𝓞 K) K a ∈ (imI M hM : Submodule (𝓞 K) K)` using `⟨_, hs (Fin.last n), by simp⟩`. Rewrite `hmem` using `[h0]`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 ha ((FractionalIdeal.mem_zero_iff _).1 hmem)`.
-/
theorem imI_ne_zero {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) (hM : Sand M) : imI M hM ≠ 0 := by
  obtain ⟨a, ha, hs⟩ := hM.1
  intro h0
  have hmem : algebraMap (𝓞 K) K a ∈ (imI M hM : Submodule (𝓞 K) K) :=
    ⟨_, hs (Fin.last n), by simp⟩
  rw [h0] at hmem
  exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 ha ((FractionalIdeal.mem_zero_iff _).1 hmem)

/- English proof (translation)
Use `set I := imI M hM`. Establish `hI : I * I⁻¹ = 1` using `mul_inv_cancel₀ (imI_ne_zero M hM)`. Set `T : Submodule (𝓞 K) K` to `{ carrier := {t | ∃ z : Fin (n+1) → K, z (Fin.last n) = t ∧ ∀ q ∈ M.map (lastL K n), q • z ∈ M} add_mem' := by`. Introduce and unpack `s t ⟨z, hz, hzM⟩ ⟨w, hw, hwM⟩`. Conclude with `⟨z + w, by simp [hz, hw], fun q hq => by rw [smul_add]; exact M.add_mem (hzM q hq) (hwM q hq)⟩`.

Use the proof step `zero_mem' := ⟨0, by simp, fun q _ => by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c t ⟨z, hz, hzM⟩`. Use `⟨c • z, by simp [hz], fun q hq => ?_⟩` and prove the remaining obligations. Rewrite using `[smul_comm]`.

Conclude with `M.smul_mem c (hzM q hq) }`. Establish `hle : ((I * I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≤ T`. Rewrite using `[FractionalIdeal.coe_mul, Submodule.mul_le]`. Introduce `p hp c hc`. Take `⟨y, hy, rfl⟩` from `hp`.

Use `⟨c • y, by simp [mul_comm], fun q hq => ?_⟩` and prove the remaining obligations. Establish `hqc : q * c ∈ I * I⁻¹` using `FractionalIdeal.mul_mem_mul hq hc`. Rewrite `hqc` using `[hI]`. Take `⟨r, hr⟩` from `(FractionalIdeal.mem_one_iff _).1 hqc`. Rewrite using `[smul_smul, ← hr, algebraMap_smul]`.

Conclude with `M.smul_mem r hy`. Establish `h1 : (1 : K) ∈ ((I * I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)`. Rewrite using `[hI]`. Conclude with `(FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩`. Take `⟨z, hz, hzM⟩` from `hle h1`.

Conclude with `⟨z, hz, hzM⟩`.
-/
theorem exists_unit_one_add_generator {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) (hM : Sand M) :
    ∃ z : Fin (n+1) → K, z (Fin.last n) = 1 ∧ ∀ q ∈ M.map (lastL K n), q • z ∈ M := by
  set I := imI M hM
  have hI : I * I⁻¹ = 1 := mul_inv_cancel₀ (imI_ne_zero M hM)
  let T : Submodule (𝓞 K) K :=
    { carrier := {t | ∃ z : Fin (n+1) → K, z (Fin.last n) = t ∧ ∀ q ∈ M.map (lastL K n), q • z ∈ M}
      add_mem' := by
        rintro s t ⟨z, hz, hzM⟩ ⟨w, hw, hwM⟩
        exact ⟨z + w, by simp [hz, hw], fun q hq => by rw [smul_add]; exact M.add_mem (hzM q hq) (hwM q hq)⟩
      zero_mem' := ⟨0, by simp, fun q _ => by simp⟩
      smul_mem' := by
        rintro c t ⟨z, hz, hzM⟩
        refine ⟨c • z, by simp [hz], fun q hq => ?_⟩
        rw [smul_comm]; exact M.smul_mem c (hzM q hq) }
  have hle : ((I * I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≤ T := by
    rw [FractionalIdeal.coe_mul, Submodule.mul_le]
    intro p hp c hc
    obtain ⟨y, hy, rfl⟩ := hp
    refine ⟨c • y, by simp [mul_comm], fun q hq => ?_⟩
    have hqc : q * c ∈ I * I⁻¹ := FractionalIdeal.mul_mem_mul hq hc
    rw [hI] at hqc
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hqc
    rw [smul_smul, ← hr, algebraMap_smul]
    exact M.smul_mem r hy
  have h1 : (1 : K) ∈ ((I * I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
    rw [hI]; exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  obtain ⟨z, hz, hzM⟩ := hle h1
  exact ⟨z, hz, hzM⟩

/- English proof (translation)
Apply `FractionalIdeal.coeToSubmodule_injective` to reduce the goal to its premises. Use `show (fiD M : Submodule (𝓞 K) K) = ((fiD (M.comap (snocL K n)) * imI M hM : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)`. Rewrite using `[FractionalIdeal.coe_mul, coe_fiD M hM, coe_fiD _ (sand_comap M hM)]`. Use `show dS M = dS (M.comap (snocL K n)) * M.map (lastL K n)`. Take `⟨z, hz1, hz⟩` from `exists_unit_one_add_generator M hM`.

Conclude with `le_antisymm (dS_le_mul M z hz1 hz) (dS_mul_le M)`.
-/
theorem fiD_succ {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) (hM : Sand M) :
    fiD M = fiD (M.comap (snocL K n)) * imI M hM := by
  apply FractionalIdeal.coeToSubmodule_injective
  show (fiD M : Submodule (𝓞 K) K) = ((fiD (M.comap (snocL K n)) * imI M hM : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
  rw [FractionalIdeal.coe_mul, coe_fiD M hM, coe_fiD _ (sand_comap M hM)]
  show dS M = dS (M.comap (snocL K n)) * M.map (lastL K n)
  obtain ⟨z, hz1, hz⟩ := exists_unit_one_add_generator M hM
  exact le_antisymm (dS_le_mul M z hz1 hz) (dS_mul_le M)

/- English proof (translation)
Rewrite using `[idx M'.toAddSubgroup M.toAddSubgroup h (lastL K n).toAddMonoidHom, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]`. Use `congr 1`. Establish `hinj : Function.Injective (snocL K n).toAddMonoidHom`. Introduce `u v huv`. Use extensionality with `j`.

Use `congrFun huv (Fin.castSucc j)` as an intermediate fact. Simplify using `using this`. Establish `hm : ∀ N : Submodule (𝓞 K) (Fin (n+1) → K), (N.comap (snocL K n)).toAddSubgroup.map (snocL K n).toAddMonoidHom = N.toAddSubgroup ⊓ (lastL K n).toAddMonoidHom.ker`. Introduce `N`. Use extensionality with `x`.

Simplify using `only [AddSubgroup.mem_map, AddSubgroup.mem_inf, AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Submodule.mem_comap, LinearMap.toAddMonoidHom_coe, lastL_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩; exact ⟨hw, by simp⟩`. Introduce and unpack `⟨hx, h0⟩`. Apply the tactic sequence `refine ⟨Fin.init x, ?_, ?_⟩ <;>`.

Establish `e : snocL K n (Fin.init x) = x`. Use extensionality with `k`. Use `Fin.lastCases ?_ (fun j => ?_) k` and prove the remaining obligations. Simplify using `[h0]`. Simplify using `[Fin.init]`.

Rewrite using `[e]`. Apply the tactic sequence `try exact hx`. Rewrite using `[← hm, ← hm, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]`.
-/
theorem relIndex_succ {n : ℕ} (M' M : Submodule (𝓞 K) (Fin (n+1) → K)) (h : M' ≤ M) :
    M'.toAddSubgroup.relIndex M.toAddSubgroup =
      (M'.comap (snocL K n)).toAddSubgroup.relIndex (M.comap (snocL K n)).toAddSubgroup *
        (M'.map (lastL K n)).toAddSubgroup.relIndex (M.map (lastL K n)).toAddSubgroup := by
  rw [idx M'.toAddSubgroup M.toAddSubgroup h (lastL K n).toAddMonoidHom, Submodule.map_toAddSubgroup,
    Submodule.map_toAddSubgroup]
  congr 1
  have hinj : Function.Injective (snocL K n).toAddMonoidHom := by
    intro u v huv
    ext j
    have := congrFun huv (Fin.castSucc j)
    simpa using this
  have hm : ∀ N : Submodule (𝓞 K) (Fin (n+1) → K),
      (N.comap (snocL K n)).toAddSubgroup.map (snocL K n).toAddMonoidHom = N.toAddSubgroup ⊓ (lastL K n).toAddMonoidHom.ker := by
    intro N
    ext x
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_inf, AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup,
      Submodule.mem_comap, LinearMap.toAddMonoidHom_coe, lastL_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact ⟨hw, by simp⟩
    · rintro ⟨hx, h0⟩
      refine ⟨Fin.init x, ?_, ?_⟩ <;>
      · have e : snocL K n (Fin.init x) = x := by
          ext k; refine Fin.lastCases ?_ (fun j => ?_) k
          · simp [h0]
          · simp [Fin.init]
        rw [e]; try exact hx
  rw [← hm, ← hm, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `M' M h _ _`. Establish `e : M' = M` using `le_antisymm h fun x _ => by rw [Subsingleton.elim x 0]; exact zero_mem _`.

Substitute `e` using the available equality. Simplify using `[AddSubgroup.relIndex_self]`. Consider the case `succ n ih`. Introduce `M' M h hM' hM`. Rewrite using `[fiD_succ M' hM', fiD_succ M hM, map_mul, map_mul, relIndex_succ M' M h, ih _ _ (Submodule.comap_mono h) (sand_comap M' hM') (sand_comap M hM), absNorm_eq_relIndex_mul (imI M hM) (imI M' hM') (imI_ne_zero M' hM') (Submodule.map_mono h)]`.

Use `push_cast`. Use `show _ = _ * _ * (FractionalIdeal.absNorm (fiD (M.comap (snocL K n))) * FractionalIdeal.absNorm (imI M hM))`. Simplify using `only [imI, FractionalIdeal.coe_mk]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main_formula : ∀ (n : ℕ) (M' M : Submodule (𝓞 K) (Fin n → K)), M' ≤ M → Sand M' → Sand M →
    FractionalIdeal.absNorm (fiD M') = (M'.toAddSubgroup.relIndex M.toAddSubgroup : ℚ) * FractionalIdeal.absNorm (fiD M) := by
  intro n
  induction n with
  | zero =>
    intro M' M h _ _
    have e : M' = M := le_antisymm h fun x _ => by rw [Subsingleton.elim x 0]; exact zero_mem _
    subst e
    simp [AddSubgroup.relIndex_self]
  | succ n ih =>
    intro M' M h hM' hM
    rw [fiD_succ M' hM', fiD_succ M hM, map_mul, map_mul, relIndex_succ M' M h,
      ih _ _ (Submodule.comap_mono h) (sand_comap M' hM') (sand_comap M hM),
      absNorm_eq_relIndex_mul (imI M hM) (imI M' hM') (imI_ne_zero M' hM') (Submodule.map_mono h)]
    push_cast
    show _ = _ * _ * (FractionalIdeal.absNorm (fiD (M.comap (snocL K n))) * FractionalIdeal.absNorm (imI M hM))
    simp only [imI, FractionalIdeal.coe_mk]
    ring

end Dx

end Formalism.L2.LamCM
