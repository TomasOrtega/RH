import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EuOfDifferentiableAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionAtOne

noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.Fhw

variable {n : ℕ}

/- English proof (translation)
Introduce `a b hab`. Establish `hm` using `h.1 hab`. Establish `h1` using `hl hab`. Establish `c1 : ((univ.filter fun c => lev b < lev c).card : ℤ) ≤ ((univ.filter fun c => lev a < lev c).card : ℤ)`. Conclude with `Finset.card_le_card fun c hc => by` after adjusting the coercions.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢`. Use linear arithmetic over natural numbers and integers. Establish `c2 : ((univ.filter fun c => lev c < lev a).card : ℤ) ≤ ((univ.filter fun c => lev c < lev b).card : ℤ)`. Conclude with `Finset.card_le_card fun c hc => by` after adjusting the coercions. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [muZ]`. Use linear arithmetic over natural numbers and integers.
-/
theorem muZ_antitone {lam : Fin n → ℤ} (hl : Antitone lam) {lev : Fin n → ℕ} (h : IsLev lam lev) :
    Antitone (muZ lam lev) := by
  intro a b hab
  have hm := h.1 hab
  have h1 := hl hab
  have c1 : ((univ.filter fun c => lev b < lev c).card : ℤ) ≤ ((univ.filter fun c => lev a < lev c).card : ℤ) := by
    exact_mod_cast Finset.card_le_card fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      omega
  have c2 : ((univ.filter fun c => lev c < lev a).card : ℤ) ≤ ((univ.filter fun c => lev c < lev b).card : ℤ) := by
    exact_mod_cast Finset.card_le_card fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      omega
  simp only [muZ]
  omega

/- English proof (translation)
Establish `: v ⟨j + 1, hj⟩ ≤ v j` using `hv (show j ≤ ⟨j + 1, hj⟩ by rw [Fin.le_def]; simp)`. Simplify using `only [dif, hj, dite_true]`. Use linear arithmetic over natural numbers and integers.
-/
theorem dif_nonneg {v : Fin n → ℤ} (hv : Antitone v) (j : Fin n) (hj : (j : ℕ) + 1 < n) : 0 ≤ dif v j := by
  have : v ⟨j + 1, hj⟩ ≤ v j := hv (show j ≤ ⟨j + 1, hj⟩ by rw [Fin.le_def]; simp)
  simp only [dif, hj, dite_true]
  omega

/- English proof (translation)
Proceed by induction on `N, h using Nat.le_induction with`. Consider the case `base`. Rewrite using `[sub_self]`. Conclude with `Finset.sum_eq_zero fun i hi => if_neg (by simpa using Finset.mem_range.1 hi)`. Consider the case `succ N hN ih`.

Rewrite using `[Finset.sum_range_succ, ih, if_pos hN]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_range_ite (w : ℕ → ℤ) (a : ℕ) (N : ℕ) (h : a ≤ N) :
    ∑ i ∈ range N, (if a ≤ i then w i - w (i + 1) else 0) = w a - w N := by
  induction N, h using Nat.le_induction with
  | base =>
    rw [sub_self]
    exact Finset.sum_eq_zero fun i hi => if_neg (by simpa using Finset.mem_range.1 hi)
  | succ N hN ih =>
    rw [Finset.sum_range_succ, ih, if_pos hN]
    ring

/- English proof (translation)
Use `set w : ℕ → ℤ := fun i => if h : i < n then v ⟨i, h⟩ else 0 with hw`. Establish `e : ∀ j : Fin n, (if a ≤ j then dif v j else 0) = (fun i : ℕ => if (a : ℕ) ≤ i then w i - w (i + 1) else 0) j`. Introduce `j`. Establish `: dif v j = w j - w (j + 1)` using `by simp [dif, hw]`. Simplify using `only [Fin.le_def, this]`.

Rewrite using `[Finset.sum_congr rfl fun j _ => e j, Fin.sum_univ_eq_sum_range (fun i : ℕ => if (a : ℕ) ≤ i then w i - w (i + 1) else 0) n, sum_range_ite w a n a.isLt.le]`. Simplify using `[hw]`.
-/
theorem sum_dif (v : Fin n → ℤ) (a : Fin n) : ∑ j, (if a ≤ j then dif v j else 0) = v a := by
  set w : ℕ → ℤ := fun i => if h : i < n then v ⟨i, h⟩ else 0 with hw
  have e : ∀ j : Fin n, (if a ≤ j then dif v j else 0) =
      (fun i : ℕ => if (a : ℕ) ≤ i then w i - w (i + 1) else 0) j := by
    intro j
    have : dif v j = w j - w (j + 1) := by simp [dif, hw]
    simp only [Fin.le_def, this]
  rw [Finset.sum_congr rfl fun j _ => e j, Fin.sum_univ_eq_sum_range
    (fun i : ℕ => if (a : ℕ) ≤ i then w i - w (i + 1) else 0) n, sum_range_ite w a n a.isLt.le]
  simp [hw]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ hu, ih]`.
-/
theorem zpow_sum {u : ℂ} (hu : u ≠ 0) {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    u ^ (∑ i ∈ s, f i) = ∏ i ∈ s, u ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ hu, ih]

open scoped ComplexOrder in
/- English proof (translation)
Establish `hu : IsUnit g` using `(Matrix.isUnit_iff_isUnit_det g).2 (isUnit_iff_ne_zero.2 hg)`. Establish `key : ∀ v : Fin (j + 1) → ℂ, Function.extend (ini j) v 0 ᵥ* g = v ᵥ* g.submatrix (ini j) id`. Introduce `v`. Use function extensionality and compare the values at `c`. Simplify using `only [Matrix.vecMul, dotProduct, submatrix_apply, id]`.

Use `symm`. Use `Finset.sum_of_injOn (ini j) (ini_injective j).injOn (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ ?_` and prove the remaining obligations. Introduce `i _ hi`. Rewrite using `[Function.extend_apply', Pi.zero_apply, zero_mul]`. Introduce and unpack `⟨r, rfl⟩`.

Conclude with `hi ⟨r, by simp, rfl⟩`. Introduce `i _`. Rewrite using `[(ini_injective j).extend_apply]`. Establish `inj : Function.Injective fun v : Fin (j + 1) → ℂ => v ᵥ* g.submatrix (ini j) id`. Introduce `v w h`.

Simplify using `only [← key] at h`. Use `Matrix.vecMul_injective_of_isUnit hu h` as an intermediate fact. Use function extensionality and compare the values at `r`. Establish `h2` using `congrFun this (ini j r)`. Rewrite `h2` using `[(ini_injective j).extend_apply, (ini_injective j).extend_apply]`. Then use the resulting hypothesis.

Conclude with `(PosDef.mul_conjTranspose_self _ inj).det_pos.ne'`.
-/
theorem gm_ne {g : Mat n} (hg : g ∈ GLs n) (j : Fin n) : gm j g ≠ 0 := by
  have hu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 (isUnit_iff_ne_zero.2 hg)
  have key : ∀ v : Fin (j + 1) → ℂ, Function.extend (ini j) v 0 ᵥ* g = v ᵥ* g.submatrix (ini j) id := by
    intro v
    funext c
    simp only [Matrix.vecMul, dotProduct, submatrix_apply, id]
    symm
    refine Finset.sum_of_injOn (ini j) (ini_injective j).injOn (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ ?_
    · intro i _ hi
      rw [Function.extend_apply', Pi.zero_apply, zero_mul]
      rintro ⟨r, rfl⟩
      exact hi ⟨r, by simp, rfl⟩
    · intro i _
      rw [(ini_injective j).extend_apply]
  have inj : Function.Injective fun v : Fin (j + 1) → ℂ => v ᵥ* g.submatrix (ini j) id := by
    intro v w h
    simp only [← key] at h
    have := Matrix.vecMul_injective_of_isUnit hu h
    funext r
    have h2 := congrFun this (ini j r)
    rwa [(ini_injective j).extend_apply, (ini_injective j).extend_apply] at h2
  exact (PosDef.mul_conjTranspose_self _ inj).det_pos.ne'

/- English proof (translation)
Proceed by induction on `u using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih`. Simplify using `only [Finset.prod_insert hi]`. Conclude with `(h i (Finset.mem_insert_self _ _)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))`.
-/
theorem diffAt_prod {𝕜 E ι : Type} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (u : Finset ι) (f : ι → E → ℂ) {x : E} (h : ∀ i ∈ u, DifferentiableAt 𝕜 (f i) x) :
    DifferentiableAt 𝕜 (fun y => ∏ i ∈ u, f i y) x := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Conclude with `DifferentiableAt.fun_sum fun σ _ => (diffAt_prod _ _ fun i _ => h _ _).const_mul _`.
-/
theorem diffAt_det {𝕜 E : Type} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {m : ℕ} (M : E → Matrix (Fin m) (Fin m) ℂ) {x : E}
    (h : ∀ i j, DifferentiableAt 𝕜 (fun y => M y i j) x) : DifferentiableAt 𝕜 (fun y => (M y).det) x := by
  simp only [Matrix.det_apply']
  exact DifferentiableAt.fun_sum fun σ _ =>
    (diffAt_prod _ _ fun i _ => h _ _).const_mul _

/- English proof (translation)
Establish `h : Differentiable 𝕜 (fun y : Mat n => y)` using `differentiable_id`. Conclude with `(differentiable_pi.1 (differentiable_pi.1 h i) j) x`.
-/
theorem entry_diff {𝕜 : Type} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] (i j : Fin n) (x : Mat n) :
    DifferentiableAt 𝕜 (fun y : Mat n => y i j) x := by
  have h : Differentiable 𝕜 (fun y : Mat n => y) := differentiable_id
  exact (differentiable_pi.1 (differentiable_pi.1 h i) j) x

/- English proof (translation)
The claim follows from `diffAt_det (fun y : Mat n => y.submatrix (ini j) (ini j)) fun r c => entry_diff _ _ x`.
-/
theorem lm_diff (j : Fin n) (x : Mat n) : DifferentiableAt ℂ (lm j) x :=
  diffAt_det (fun y : Mat n => y.submatrix (ini j) (ini j)) fun r c => entry_diff _ _ x

/- English proof (translation)
Use `diffAt_det (fun y : Mat n => y.submatrix (ini j) id * (y.submatrix (ini j) id)ᴴ) fun r c => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply, submatrix_apply, conjTranspose_apply, id]`. Use `DifferentiableAt.fun_sum fun k _ => (entry_diff _ _ x).mul ?_` and prove the remaining obligations. Conclude with `(Complex.conjCLE.differentiableAt).comp x (entry_diff (𝕜 := ℝ) _ _ x)`.
-/
theorem gm_diff (j : Fin n) (x : Mat n) : DifferentiableAt ℝ (gm j) x := by
  refine diffAt_det (fun y : Mat n => y.submatrix (ini j) id * (y.submatrix (ini j) id)ᴴ) fun r c => ?_
  simp only [Matrix.mul_apply, submatrix_apply, conjTranspose_apply, id]
  refine DifferentiableAt.fun_sum fun k _ => (entry_diff _ _ x).mul ?_
  exact (Complex.conjCLE.differentiableAt).comp x (entry_diff (𝕜 := ℝ) _ _ x)

/- English proof (translation)
Establish `hb : Function.Bijective (ini j)` using `(Fintype.bijective_iff_injective_and_card _).2 ⟨ini_injective j, by simp; omega⟩`. Establish `: lm j g = g.det` using `Matrix.det_submatrix_equiv_self (Equiv.ofBijective _ hb) g`. Rewrite using `[this]`. Conclude with `hg`.
-/
theorem lm_last_ne {g : Mat n} (hg : g ∈ GLs n) (j : Fin n) (hj : ¬ (j : ℕ) + 1 < n) : lm j g ≠ 0 := by
  have hb : Function.Bijective (ini j) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨ini_injective j, by simp; omega⟩
  have : lm j g = g.det := Matrix.det_submatrix_equiv_self (Equiv.ofBijective _ hb) g
  rw [this]
  exact hg

/- English proof (translation)
Distinguish the cases in `h : c = b`. Substitute `h` using the available equality. Simplify using `[Matrix.mul_single_apply_same]`. Simplify using `[h, Matrix.mul_single_apply_of_ne _ _ _ _ _ h]`.
-/
theorem line_apply (g : Mat n) (a b : Fin n) (t : ℂ) (r c : Fin n) :
    (g + t • (g * Matrix.single a b (1 : ℂ))) r c = g r c + if c = b then t * g r a else 0 := by
  by_cases h : c = b
  · subst h
    simp [Matrix.mul_single_apply_same]
  · simp [h, Matrix.mul_single_apply_of_ne _ _ _ _ _ h]

/- English proof (translation)
Distinguish the cases in `hb : b ≤ j`. Establish `hb' : (b : ℕ) < j + 1` using `by have := Fin.le_def.1 hb; omega`. Establish `ha' : (a : ℕ) < j + 1` using `by have := Fin.lt_def.1 hab; omega`. Use `set b' : Fin (j + 1) := ⟨b, hb'⟩`. Use `set a' : Fin (j + 1) := ⟨a, ha'⟩`.

Establish `hib : ini j b' = b` using `Fin.ext rfl`. Establish `hia : ini j a' = a` using `Fin.ext rfl`. Establish `hne : b' ≠ a'` using `fun h => by`. Establish `h'` using `congrArg (fun z : Fin (j + 1) => (z : ℕ)) h`. Conclude with `hab.ne' (Fin.ext h')`.

Establish `e : (g + t • (g * Matrix.single a b (1 : ℂ))).submatrix (ini j) (ini j) = (g.submatrix (ini j) (ini j)).updateCol b' fun k => g.submatrix (ini j) (ini j) k b' + t • g.submatrix (ini j) (ini j) k a'`. Use extensionality with `r c`. Rewrite using `[submatrix_apply, line_apply]`. Distinguish the cases in `hc : c = b'`. Substitute `hc` using the available equality.

Simplify using `[hib, hia, Matrix.updateCol_self]`. Establish `: ini j c ≠ b` using `fun h => hc ((ini_injective j) (h.trans hib.symm))`. Simplify using `[this, Matrix.updateCol_ne hc]`. Unfold `lm`. Rewrite using `[e, det_updateCol_add_smul_self _ hne]`.

Establish `e : (g + t • (g * Matrix.single a b (1 : ℂ))).submatrix (ini j) (ini j) = g.submatrix (ini j) (ini j)`. Use extensionality with `r c`. Rewrite using `[submatrix_apply, line_apply]`. Establish `: ini j c ≠ b`. Introduce `h`.

Apply `hb` to reduce the goal to its premises. Rewrite using `[← h, Fin.le_def]`. Use `c.isLt` as an intermediate fact. Simplify using `only [ini, Fin.val_castLE]`. Use linear arithmetic over natural numbers and integers.

Simplify using `[this]`. Unfold `lm`. Rewrite using `[e]`.
-/
theorem lm_line_lt (g : Mat n) {a b : Fin n} (hab : a < b) (t : ℂ) (j : Fin n) :
    lm j (g + t • (g * Matrix.single a b (1 : ℂ))) = lm j g := by
  by_cases hb : b ≤ j
  · have hb' : (b : ℕ) < j + 1 := by have := Fin.le_def.1 hb; omega
    have ha' : (a : ℕ) < j + 1 := by have := Fin.lt_def.1 hab; omega
    set b' : Fin (j + 1) := ⟨b, hb'⟩
    set a' : Fin (j + 1) := ⟨a, ha'⟩
    have hib : ini j b' = b := Fin.ext rfl
    have hia : ini j a' = a := Fin.ext rfl
    have hne : b' ≠ a' := fun h => by
      have h' := congrArg (fun z : Fin (j + 1) => (z : ℕ)) h
      exact hab.ne' (Fin.ext h')
    have e : (g + t • (g * Matrix.single a b (1 : ℂ))).submatrix (ini j) (ini j) =
        (g.submatrix (ini j) (ini j)).updateCol b' fun k =>
          g.submatrix (ini j) (ini j) k b' + t • g.submatrix (ini j) (ini j) k a' := by
      ext r c
      rw [submatrix_apply, line_apply]
      by_cases hc : c = b'
      · subst hc
        simp [hib, hia, Matrix.updateCol_self]
      · have : ini j c ≠ b := fun h => hc ((ini_injective j) (h.trans hib.symm))
        simp [this, Matrix.updateCol_ne hc]
    unfold lm
    rw [e, det_updateCol_add_smul_self _ hne]
  · have e : (g + t • (g * Matrix.single a b (1 : ℂ))).submatrix (ini j) (ini j) =
        g.submatrix (ini j) (ini j) := by
      ext r c
      rw [submatrix_apply, line_apply]
      have : ini j c ≠ b := by
        intro h
        apply hb
        rw [← h, Fin.le_def]
        have := c.isLt
        simp only [ini, Fin.val_castLE]
        omega
      simp [this]
    unfold lm
    rw [e]

/- English proof (translation)
Distinguish the cases in `hb : a ≤ j`. Establish `hb' : (a : ℕ) < j + 1` using `by have := Fin.le_def.1 hb; omega set a' : Fin (j + 1) := ⟨a, hb'⟩`. Establish `hia : ini j a' = a` using `Fin.ext rfl`. Establish `e : (g + t • (g * Matrix.single a a (1 : ℂ))).submatrix (ini j) (ini j) = (g.submatrix (ini j) (ini j)).updateCol a' ((1 + t) • fun k => g.submatrix (ini j) (ini j) k a')`. Use extensionality with `r c`.

Rewrite using `[submatrix_apply, line_apply]`. Distinguish the cases in `hc : c = a'`. Substitute `hc` using the available equality. Simplify using `[hia, Matrix.updateCol_self]`. Expand and normalize the polynomial expressions, which then agree.

Establish `: ini j c ≠ a` using `fun h => hc ((ini_injective j) (h.trans hia.symm))`. Simplify using `[this, Matrix.updateCol_ne hc]`. Unfold `lm`. Rewrite using `[e, det_updateCol_smul, if_pos hb]`. Use `congr 2`.

Use extensionality with `r c`. Distinguish the cases in `hc : c = a'`. Substitute `hc` using the available equality. Simplify using `[Matrix.updateCol_self]`. Simplify using `[Matrix.updateCol_ne hc]`.

Establish `e : (g + t • (g * Matrix.single a a (1 : ℂ))).submatrix (ini j) (ini j) = g.submatrix (ini j) (ini j)`. Use extensionality with `r c`. Rewrite using `[submatrix_apply, line_apply]`. Establish `: ini j c ≠ a`. Introduce `h`.

Apply `hb` to reduce the goal to its premises. Rewrite using `[← h, Fin.le_def]`. Use `c.isLt` as an intermediate fact. Simplify using `only [ini, Fin.val_castLE]`. Use linear arithmetic over natural numbers and integers.

Simplify using `[this]`. Unfold `lm`. Rewrite using `[e, if_neg hb, one_mul]`.
-/
theorem lm_line_eq (g : Mat n) (a : Fin n) (t : ℂ) (j : Fin n) :
    lm j (g + t • (g * Matrix.single a a (1 : ℂ))) = (if a ≤ j then (1 + t) else 1) * lm j g := by
  by_cases hb : a ≤ j
  · have hb' : (a : ℕ) < j + 1 := by have := Fin.le_def.1 hb; omega
    set a' : Fin (j + 1) := ⟨a, hb'⟩
    have hia : ini j a' = a := Fin.ext rfl
    have e : (g + t • (g * Matrix.single a a (1 : ℂ))).submatrix (ini j) (ini j) =
        (g.submatrix (ini j) (ini j)).updateCol a' ((1 + t) • fun k => g.submatrix (ini j) (ini j) k a') := by
      ext r c
      rw [submatrix_apply, line_apply]
      by_cases hc : c = a'
      · subst hc
        simp [hia, Matrix.updateCol_self]
        ring
      · have : ini j c ≠ a := fun h => hc ((ini_injective j) (h.trans hia.symm))
        simp [this, Matrix.updateCol_ne hc]
    unfold lm
    rw [e, det_updateCol_smul, if_pos hb]
    congr 2
    ext r c
    by_cases hc : c = a'
    · subst hc
      simp [Matrix.updateCol_self]
    · simp [Matrix.updateCol_ne hc]
  · have e : (g + t • (g * Matrix.single a a (1 : ℂ))).submatrix (ini j) (ini j) =
        g.submatrix (ini j) (ini j) := by
      ext r c
      rw [submatrix_apply, line_apply]
      have : ini j c ≠ a := by
        intro h
        apply hb
        rw [← h, Fin.le_def]
        have := c.isLt
        simp only [ini, Fin.val_castLE]
        omega
      simp [this]
    unfold lm
    rw [e, if_neg hb, one_mul]

def Pf (d : Fin n → ℤ) (x : Mat n) : ℂ := ∏ j, lm j x ^ d j

def Qf (y : Fin n → ℤ) (x : Mat n) : ℂ := ∏ j, gm j x ^ y j

/- English proof (translation)
Use `diffAt_prod _ _ fun j _ => (lm_diff j g).zpow ?_` and prove the remaining obligations. Distinguish the cases in `hj : (j : ℕ) + 1 < n`. Conclude with `Or.inr (hd j hj)`. Conclude with `Or.inl (lm_last_ne hg j hj)`.
-/
theorem Pf_diff {d : Fin n → ℤ} (hd : ∀ j : Fin n, (j : ℕ) + 1 < n → 0 ≤ d j) {g : Mat n} (hg : g ∈ GLs n) :
    DifferentiableAt ℂ (Pf d) g := by
  refine diffAt_prod _ _ fun j _ => (lm_diff j g).zpow ?_
  by_cases hj : (j : ℕ) + 1 < n
  · exact Or.inr (hd j hj)
  · exact Or.inl (lm_last_ne hg j hj)

/- English proof (translation)
Use `diffAt_prod _ _ fun j _ => ?_` and prove the remaining obligations. Conclude with `((differentiableAt_zpow (m := y j)).2 (Or.inl (gm_ne hg j))).restrictScalars ℝ |>.comp g (gm_diff j g)`.
-/
theorem Qf_diff (y : Fin n → ℤ) {g : Mat n} (hg : g ∈ GLs n) : DifferentiableAt ℝ (Qf y) g := by
  refine diffAt_prod _ _ fun j _ => ?_
  exact ((differentiableAt_zpow (m := y j)).2 (Or.inl (gm_ne hg j))).restrictScalars ℝ |>.comp g (gm_diff j g)

/- English proof (translation)
Use `set A := g.submatrix (ini j) id`. Use `set M₀ := A * Aᴴ`. Use `set N := A * (X * X) * Aᴴ`. Establish `e : ∀ t : ℝ, gm j (g + t • (g * X)) = (M₀ - ((t ^ 2 : ℝ) : ℂ) • N).det`. Introduce `t`.

Establish `h0 : g + t • (g * X) = g * (1 + (t : ℂ) • X)`. Rewrite using `[Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]`. Use `congr 1`. Establish `h1 : (g + t • (g * X)).submatrix (ini j) id = A * (1 + (t : ℂ) • X)`. Rewrite using `[h0, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_id_id]`.

Establish `h2 : (1 + (t : ℂ) • X)ᴴ = 1 - (t : ℂ) • X`. Rewrite using `[conjTranspose_add, conjTranspose_one, conjTranspose_smul, hX]`. Simplify using `[sub_eq_add_neg]`. Unfold `gm`. Rewrite using `[h1, conjTranspose_mul, h2]`.

Use `congr 1`. Simplify using `only [M₀, N, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (1 + (t : ℂ) • X)]`. Establish `h3 : (1 + (t : ℂ) • X) * (1 - (t : ℂ) • X) = 1 - ((t ^ 2 : ℝ) : ℂ) • (X * X)`. Establish `h4 : ∀ T : Mat n, (1 + T) * (1 - T) = 1 - T * T` using `fun T => by noncomm_ring`.

Rewrite using `[h4, Matrix.smul_mul, Matrix.mul_smul, smul_smul]`. Use `push_cast`. Rewrite using `[pow_two]`. Rewrite using `[h3, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]`. Establish `hψ : DifferentiableAt ℝ (fun s : ℝ => (M₀ - (s : ℂ) • N).det) 0`.

Use `diffAt_det (fun s : ℝ => M₀ - (s : ℂ) • N) fun r c => ?_` and prove the remaining obligations. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]`. Use `fun_prop`. Establish `h2 : HasDerivAt (fun t : ℝ => t ^ 2) 0 0` using `by simpa using hasDerivAt_pow 2 (0 : ℝ)`. Establish `hψ' : HasDerivAt (fun s : ℝ => (M₀ - (s : ℂ) • N).det) (deriv (fun s : ℝ => (M₀ - (s : ℂ) • N).det) 0) ((fun t : ℝ => t ^ 2) 0)`.

Simplify using `using hψ.hasDerivAt`. Establish `h3 : HasDerivAt ((fun s : ℝ => (M₀ - (s : ℂ) • N).det) ∘ fun t : ℝ => t ^ 2) ((0 : ℝ) • deriv (fun s : ℝ => (M₀ - (s : ℂ) • N).det) 0) 0` using `HasDerivAt.scomp (h := fun t : ℝ => t ^ 2) (0 : ℝ) hψ' h2`. Rewrite `h3` using `[zero_smul]`. Conclude with `h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => e t)`.
-/
theorem gm_skew (g : Mat n) {X : Mat n} (hX : Xᴴ = -X) (j : Fin n) :
    HasDerivAt (fun t : ℝ => gm j (g + t • (g * X))) 0 0 := by
  set A := g.submatrix (ini j) id
  set M₀ := A * Aᴴ
  set N := A * (X * X) * Aᴴ
  have e : ∀ t : ℝ, gm j (g + t • (g * X)) = (M₀ - ((t ^ 2 : ℝ) : ℂ) • N).det := by
    intro t
    have h0 : g + t • (g * X) = g * (1 + (t : ℂ) • X) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
      congr 1
    have h1 : (g + t • (g * X)).submatrix (ini j) id = A * (1 + (t : ℂ) • X) := by
      rw [h0, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_id_id]
    have h2 : (1 + (t : ℂ) • X)ᴴ = 1 - (t : ℂ) • X := by
      rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul, hX]
      simp [sub_eq_add_neg]
    unfold gm
    rw [h1, conjTranspose_mul, h2]
    congr 1
    simp only [M₀, N, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (1 + (t : ℂ) • X)]
    have h3 : (1 + (t : ℂ) • X) * (1 - (t : ℂ) • X) = 1 - ((t ^ 2 : ℝ) : ℂ) • (X * X) := by
      have h4 : ∀ T : Mat n, (1 + T) * (1 - T) = 1 - T * T := fun T => by noncomm_ring
      rw [h4, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      push_cast
      rw [pow_two]
    rw [h3, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have hψ : DifferentiableAt ℝ (fun s : ℝ => (M₀ - (s : ℂ) • N).det) 0 := by
    refine diffAt_det (fun s : ℝ => M₀ - (s : ℂ) • N) fun r c => ?_
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by simpa using hasDerivAt_pow 2 (0 : ℝ)
  have hψ' : HasDerivAt (fun s : ℝ => (M₀ - (s : ℂ) • N).det) (deriv (fun s : ℝ => (M₀ - (s : ℂ) • N).det) 0)
      ((fun t : ℝ => t ^ 2) 0) := by
    simpa using hψ.hasDerivAt
  have h3 : HasDerivAt ((fun s : ℝ => (M₀ - (s : ℂ) • N).det) ∘ fun t : ℝ => t ^ 2)
      ((0 : ℝ) • deriv (fun s : ℝ => (M₀ - (s : ℂ) • N).det) 0) 0 :=
    HasDerivAt.scomp (h := fun t : ℝ => t ^ 2) (0 : ℝ) hψ' h2
  rw [zero_smul] at h3
  exact h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => e t)

/- English proof (translation)
Establish `h1 : HasDerivAt (fun t : ℝ => Qf y (g + t • (g * X))) (fderiv ℝ (Qf y) g (g * X)) 0` using `(Qf_diff y hg).hasFDerivAt.hasLineDerivAt (g * X)`. Establish `h2 : ∀ j ∈ (univ : Finset (Fin n)), HasDerivAt (fun t : ℝ => gm j (g + t • (g * X)) ^ y j) 0 0`. Introduce `j _`. Establish `h0` using `gm_skew g hX j`. Establish `hz : HasDerivAt (fun z : ℂ => z ^ y j) ((y j : ℂ) * gm j g ^ (y j - 1)) ((fun t : ℝ => gm j (g + t • (g * X))) 0)`.

Simplify using `using hasDerivAt_zpow (y j) (gm j g) (Or.inl (gm_ne hg j))`. Establish `h5 : HasDerivAt ((fun z : ℂ => z ^ y j) ∘ fun t : ℝ => gm j (g + t • (g * X))) 0 0`. Simplify using `using hz.scomp (0 : ℝ) h0`. Conclude with `h5`. Establish `h3` using `HasDerivAt.finset_prod h2`.

Simplify using `only [smul_zero, Finset.sum_const_zero] at h3`. Establish `e : (fun t : ℝ => Qf y (g + t • (g * X))) = ∏ j, fun t : ℝ => gm j (g + t • (g * X)) ^ y j`. Use function extensionality and compare the values at `t`. Simplify using `[Qf, Finset.prod_apply]`. Rewrite `h1` using `[e]`.

Conclude with `h1.unique h3`.
-/
theorem Qf_skew (y : Fin n → ℤ) {g : Mat n} (hg : g ∈ GLs n) {X : Mat n} (hX : Xᴴ = -X) :
    fderiv ℝ (Qf y) g (g * X) = 0 := by
  have h1 : HasDerivAt (fun t : ℝ => Qf y (g + t • (g * X))) (fderiv ℝ (Qf y) g (g * X)) 0 :=
    (Qf_diff y hg).hasFDerivAt.hasLineDerivAt (g * X)
  have h2 : ∀ j ∈ (univ : Finset (Fin n)), HasDerivAt (fun t : ℝ => gm j (g + t • (g * X)) ^ y j) 0 0 := by
    intro j _
    have h0 := gm_skew g hX j
    have hz : HasDerivAt (fun z : ℂ => z ^ y j) ((y j : ℂ) * gm j g ^ (y j - 1))
        ((fun t : ℝ => gm j (g + t • (g * X))) 0) := by
      simpa using hasDerivAt_zpow (y j) (gm j g) (Or.inl (gm_ne hg j))
    have h5 : HasDerivAt ((fun z : ℂ => z ^ y j) ∘ fun t : ℝ => gm j (g + t • (g * X))) 0 0 := by
      simpa using hz.scomp (0 : ℝ) h0
    exact h5
  have h3 := HasDerivAt.finset_prod h2
  simp only [smul_zero, Finset.sum_const_zero] at h3
  have e : (fun t : ℝ => Qf y (g + t • (g * X))) = ∏ j, fun t : ℝ => gm j (g + t • (g * X)) ^ y j := by
    funext t
    simp [Qf, Finset.prod_apply]
  rw [e] at h1
  exact h1.unique h3

/- English proof (translation)
Establish `h1 : HasDerivAt (fun t : ℂ => Pf d (g + t • (g * Matrix.single a b 1))) (fderiv ℂ (Pf d) g (g * Matrix.single a b 1)) 0` using `(Pf_diff hd hg).hasFDerivAt.hasLineDerivAt (g * Matrix.single a b 1)`. Use `h1.unique ?_` and prove the remaining obligations. Establish `: (fun t : ℂ => Pf d (g + t • (g * Matrix.single a b 1))) = fun _ => Pf d g`. Use function extensionality and compare the values at `t`. Simplify using `only [Pf, lm_line_lt g hab]`.

Rewrite using `[this]`. Conclude with `hasDerivAt_const _ _`.
-/
theorem Pf_lt {d : Fin n → ℤ} (hd : ∀ j : Fin n, (j : ℕ) + 1 < n → 0 ≤ d j) {g : Mat n} (hg : g ∈ GLs n)
    {a b : Fin n} (hab : a < b) : fderiv ℂ (Pf d) g (g * Matrix.single a b 1) = 0 := by
  have h1 : HasDerivAt (fun t : ℂ => Pf d (g + t • (g * Matrix.single a b 1)))
      (fderiv ℂ (Pf d) g (g * Matrix.single a b 1)) 0 :=
    (Pf_diff hd hg).hasFDerivAt.hasLineDerivAt (g * Matrix.single a b 1)
  refine h1.unique ?_
  have : (fun t : ℂ => Pf d (g + t • (g * Matrix.single a b 1))) = fun _ => Pf d g := by
    funext t
    simp only [Pf, lm_line_lt g hab]
  rw [this]
  exact hasDerivAt_const _ _

/- English proof (translation)
Establish `h1 : HasDerivAt (fun t : ℂ => Pf d (g + t • (g * Matrix.single a a 1))) (fderiv ℂ (Pf d) g (g * Matrix.single a a 1)) 0` using `(Pf_diff hd hg).hasFDerivAt.hasLineDerivAt (g * Matrix.single a a 1)`. Use `set m : ℤ := ∑ j, (if a ≤ j then d j else 0)`. Establish `h2 : HasDerivAt (fun t : ℂ => (1 + t) ^ m) (m : ℂ) 0`. Use `(hasDerivAt_zpow m (1 + 0 : ℂ) (Or.inl (by simp))).comp_const_add (1 : ℂ) 0` as an intermediate fact. Simplify using `using this`.

Establish `h3` using `h2.mul_const (Pf d g)`. Use `h1.unique (h3.congr_of_eventuallyEq ?_)` and prove the remaining obligations. Establish `hne : ∀ᶠ t : ℂ in nhds 0, 1 + t ≠ 0` using `(continuous_const.add continuous_id).continuousAt.eventually_ne (by simp)`. Use `filter_upwards [hne] with t ht`. Simplify using `only [Pf, lm_line_eq, m, zpow_sum ht, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_zpow]`. Apply the tactic sequence `by_cases h : a ≤ j <;> simp [h]`.
-/
theorem Pf_eq {d : Fin n → ℤ} (hd : ∀ j : Fin n, (j : ℕ) + 1 < n → 0 ≤ d j) {g : Mat n} (hg : g ∈ GLs n)
    (a : Fin n) : fderiv ℂ (Pf d) g (g * Matrix.single a a 1) =
      ((∑ j, (if a ≤ j then d j else 0) : ℤ) : ℂ) * Pf d g := by
  have h1 : HasDerivAt (fun t : ℂ => Pf d (g + t • (g * Matrix.single a a 1)))
      (fderiv ℂ (Pf d) g (g * Matrix.single a a 1)) 0 :=
    (Pf_diff hd hg).hasFDerivAt.hasLineDerivAt (g * Matrix.single a a 1)
  set m : ℤ := ∑ j, (if a ≤ j then d j else 0)
  have h2 : HasDerivAt (fun t : ℂ => (1 + t) ^ m) (m : ℂ) 0 := by
    have := (hasDerivAt_zpow m (1 + 0 : ℂ) (Or.inl (by simp))).comp_const_add (1 : ℂ) 0
    simpa using this
  have h3 := h2.mul_const (Pf d g)
  refine h1.unique (h3.congr_of_eventuallyEq ?_)
  have hne : ∀ᶠ t : ℂ in nhds 0, 1 + t ≠ 0 :=
    (continuous_const.add continuous_id).continuousAt.eventually_ne (by simp)
  filter_upwards [hne] with t ht
  simp only [Pf, lm_line_eq, m, zpow_sum ht, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [mul_zpow]
  by_cases h : a ≤ j <;> simp [h]

/- English proof (translation)
Establish `h : fderiv ℝ (fun x => P x * Q x) g = P g • fderiv ℝ Q g + Q g • fderiv ℝ P g` using `fderiv_fun_mul hP hQ`. Simplify using `only [Eu, Rd, Pi.smul_apply, Pi.add_apply, h, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Eu_mul {P Q : Mat n → ℂ} {g : Mat n} (hP : DifferentiableAt ℝ P g) (hQ : DifferentiableAt ℝ Q g)
    (s : Bool) (a b : Fin n) :
    Eu s a b (fun x => P x * Q x) g = Eu s a b P g * Q g + P g * Eu s a b Q g := by
  have h : fderiv ℝ (fun x => P x * Q x) g = P g • fderiv ℝ Q g + Q g • fderiv ℝ P g := fderiv_fun_mul hP hQ
  simp only [Eu, Rd, Pi.smul_apply, Pi.add_apply, h, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Establish `s1 : (Matrix.single a b (1 : ℂ) - Matrix.single b a 1)ᴴ = -(Matrix.single a b (1 : ℂ) - Matrix.single b a 1)`. Simplify using `[conjTranspose_sub, Matrix.conjTranspose_single]`. Establish `s2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ = -(Matrix.single a b Complex.I + Matrix.single b a Complex.I)`. Simplify using `[conjTranspose_add, Matrix.conjTranspose_single, Matrix.single_neg]`. Establish `h1` using `Qf_skew y hg s1`.

Establish `h2` using `Qf_skew y hg s2`. Rewrite `h1` using `[Matrix.mul_sub, map_sub]`. Rewrite `h2` using `[Matrix.mul_add, map_add]`. Simplify using `only [Eu, Rd, Pi.smul_apply, Pi.add_apply, smul_eq_mul, if_true, Bool.false_eq_true, if_false]`. Take the linear combination `(1 / 2 : ℂ) * h1 - (Complex.I / 2) * h2`.
-/
theorem Qf_kill (y : Fin n → ℤ) {g : Mat n} (hg : g ∈ GLs n) (a b : Fin n) :
    Eu true a b (Qf y) g - Eu false b a (Qf y) g = 0 := by
  have s1 : (Matrix.single a b (1 : ℂ) - Matrix.single b a 1)ᴴ = -(Matrix.single a b (1 : ℂ) - Matrix.single b a 1) := by
    simp [conjTranspose_sub, Matrix.conjTranspose_single]
  have s2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ =
      -(Matrix.single a b Complex.I + Matrix.single b a Complex.I) := by
    simp [conjTranspose_add, Matrix.conjTranspose_single, Matrix.single_neg]
  have h1 := Qf_skew y hg s1
  have h2 := Qf_skew y hg s2
  rw [Matrix.mul_sub, map_sub] at h1
  rw [Matrix.mul_add, map_add] at h2
  simp only [Eu, Rd, Pi.smul_apply, Pi.add_apply, smul_eq_mul, if_true, Bool.false_eq_true, if_false]
  linear_combination (1 / 2 : ℂ) * h1 - (Complex.I / 2) * h2

/- English proof (translation)
Establish `: Kf a b h = e1 DR a b h - f1 DR b a h`. Simplify using `[Kf, GlobalTheory.CompanionTheory.GLK.e2, sub_eq_add_neg]`. Rewrite using `[this, Submodule.coe_sub, Pi.sub_apply, orderedCechToCatCochainsOne_apply_valueAtSubset _ _ _ hg, liftOneFormsToCompatible_apply _ _ _ hg]`.
-/
theorem Kf_apply (a b : Fin n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    (Kf a b h).1 g = Eu true a b h.1 g - Eu false b a h.1 g := by
  have : Kf a b h = e1 DR a b h - f1 DR b a h := by
    simp [Kf, GlobalTheory.CompanionTheory.GLK.e2, sub_eq_add_neg]
  rw [this, Submodule.coe_sub, Pi.sub_apply, orderedCechToCatCochainsOne_apply_valueAtSubset _ _ _ hg, liftOneFormsToCompatible_apply _ _ _ hg]

/- English proof (translation)
Establish `hc` using `Pf_diff hd hg`. Establish `hP` using `hc.restrictScalars ℝ`. Establish `hQ` using `Qf_diff y hg`. Establish `e : F.1 =ᶠ[nhds g] fun x => Pf d x * Qf y x` using `by filter_upwards [GlobalTheory.CompanionTheory.RmHol.isOpen_GLs.mem_nhds hg] with x hx using hF x hx`. Establish `hk` using `Qf_kill y hg a b`.

Establish `h1` using `GlobalTheory.CompanionTheory.RmHol.GelCoef.Eu_of_differentiableAt hc a b`. Establish `h2` using `GlobalTheory.CompanionTheory.RmHol.GelCoef.Eu_of_differentiableAt hc b a`. Rewrite using `[Kf_apply _ _ _ hg, GlobalTheory.CompanionTheory.RmHol.GelCoef.Eu_congr_germ e, GlobalTheory.CompanionTheory.RmHol.GelCoef.Eu_congr_germ e, Eu_mul hP hQ, Eu_mul hP hQ, h1.1, h2.2]`. Take the linear combination `Pf d g * hk`.
-/
theorem Kf_fRaw {d y : Fin n → ℤ} (hd : ∀ j : Fin n, (j : ℕ) + 1 < n → 0 ≤ d j) (F : SmF n)
    (hF : ∀ x ∈ GLs n, F.1 x = Pf d x * Qf y x) (a b : Fin n) {g : Mat n} (hg : g ∈ GLs n) :
    (Kf a b F).1 g = fderiv ℂ (Pf d) g (g * Matrix.single a b 1) * Qf y g := by
  have hc := Pf_diff hd hg
  have hP := hc.restrictScalars ℝ
  have hQ := Qf_diff y hg
  have e : F.1 =ᶠ[nhds g] fun x => Pf d x * Qf y x := by
    filter_upwards [GlobalTheory.CompanionTheory.RmHol.isOpen_GLs.mem_nhds hg] with x hx using hF x hx
  have hk := Qf_kill y hg a b
  have h1 := GlobalTheory.CompanionTheory.RmHol.GelCoef.Eu_of_differentiableAt hc a b
  have h2 := GlobalTheory.CompanionTheory.RmHol.GelCoef.Eu_of_differentiableAt hc b a
  rw [Kf_apply _ _ _ hg, GlobalTheory.CompanionTheory.RmHol.GelCoef.Eu_congr_germ e, GlobalTheory.CompanionTheory.RmHol.GelCoef.Eu_congr_germ e,
    Eu_mul hP hQ, Eu_mul hP hQ, h1.1, h2.2]
  linear_combination Pf d g * hk

end GlobalTheory.CompanionTheory.ModelS.Fhw

open GlobalTheory.CompanionTheory.ModelS.Fhw in

/- English proof (translation)
Establish `hd : ∀ j : Fin n, (j : ℕ) + 1 < n → 0 ≤ GlobalTheory.CompanionTheory.ModelS.dif (GlobalTheory.CompanionTheory.ModelS.muZ lam lev) j` using `fun j hj => dif_nonneg (muZ_antitone hl hv) j hj`. Establish `hP : ∀ x ∈ GLs n, F.1 x = Pf (GlobalTheory.CompanionTheory.ModelS.dif (GlobalTheory.CompanionTheory.ModelS.muZ lam lev)) x * Qf (GlobalTheory.CompanionTheory.ModelS.dif (GlobalTheory.CompanionTheory.ModelS.yZ lam lev)) x`. Introduce `x hx`. Rewrite using `[hF, GlobalTheory.CompanionTheory.ModelS.fRaw, Set.indicator_of_mem hx, Finset.prod_mul_distrib]`. Both sides reduce to the same expression.

Use `⟨fun a b hab => ?_, fun a => ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Distinguish the cases in `hg : g ∈ GLs n`. Rewrite using `[Kf_fRaw hd F hP a b hg, Pf_lt hd hg hab, zero_mul]`.

Both sides reduce to the same expression. Conclude with `(GlobalTheory.CompanionTheory.ModelS.Kf a b F).2.2 g hg`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Distinguish the cases in `hg : g ∈ GLs n`.

Rewrite using `[Kf_fRaw hd F hP a a hg, Pf_eq hd hg a, Submodule.coe_smul, Pi.smul_apply, hP g hg, smul_eq_mul, sum_dif]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[(GlobalTheory.CompanionTheory.ModelS.Kf a a F).2.2 g hg, Submodule.coe_smul, Pi.smul_apply, F.2.2 g hg, smul_zero]`.
-/
theorem GlobalTheory.CompanionTheory.ModelS.f_highest (n : ℕ) (lam : Fin n → ℤ) (hl : Antitone lam) (lev : Fin n → ℕ) (hv : IsLev lam lev)
    (F : GlobalTheory.CompanionTheory.ModelS.SmF n) (hF : F.1 = GlobalTheory.CompanionTheory.ModelS.fRaw lam lev) :
    (∀ a b : Fin n, a < b → GlobalTheory.CompanionTheory.ModelS.Kf a b F = 0) ∧
      ∀ a : Fin n, GlobalTheory.CompanionTheory.ModelS.Kf a a F = (GlobalTheory.CompanionTheory.ModelS.muZ lam lev a : ℂ) • F := by
  have hd : ∀ j : Fin n, (j : ℕ) + 1 < n → 0 ≤ GlobalTheory.CompanionTheory.ModelS.dif (GlobalTheory.CompanionTheory.ModelS.muZ lam lev) j :=
    fun j hj => dif_nonneg (muZ_antitone hl hv) j hj
  have hP : ∀ x ∈ GLs n, F.1 x = Pf (GlobalTheory.CompanionTheory.ModelS.dif (GlobalTheory.CompanionTheory.ModelS.muZ lam lev)) x *
      Qf (GlobalTheory.CompanionTheory.ModelS.dif (GlobalTheory.CompanionTheory.ModelS.yZ lam lev)) x := by
    intro x hx
    rw [hF, GlobalTheory.CompanionTheory.ModelS.fRaw, Set.indicator_of_mem hx, Finset.prod_mul_distrib]
    rfl
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · rw [Kf_fRaw hd F hP a b hg, Pf_lt hd hg hab, zero_mul]
      rfl
    · exact (GlobalTheory.CompanionTheory.ModelS.Kf a b F).2.2 g hg
  · apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · rw [Kf_fRaw hd F hP a a hg, Pf_eq hd hg a, Submodule.coe_smul, Pi.smul_apply, hP g hg, smul_eq_mul,
        sum_dif]
      ring
    · rw [(GlobalTheory.CompanionTheory.ModelS.Kf a a F).2.2 g hg, Submodule.coe_smul, Pi.smul_apply, F.2.2 g hg, smul_zero]
