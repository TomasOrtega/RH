import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

namespace GlobalTheory.CompanionTheory.Ar.PB.BigCellLU

variable {N : ℕ}

abbrev square_block_restriction (G : Matrix (Fin N) (Fin N) ℂ) (T : Finset (Fin N)) : Matrix {x // x ∈ T} {x // x ∈ T} ℂ :=
  G.submatrix Subtype.val Subtype.val

/- English proof (translation)
Unfold `minorIJ`. Rewrite using `[dif_pos rfl, ← Matrix.det_submatrix_equiv_self (T.orderIsoOfFin rfl).toEquiv (square_block_restriction G T)]`. Use `congr 1`.
-/
theorem minorIJ_self (G : Matrix (Fin N) (Fin N) ℂ) (T : Finset (Fin N)) :
    minorIJ G T T = (square_block_restriction G T).det := by
  unfold minorIJ
  rw [dif_pos rfl, ← Matrix.det_submatrix_equiv_self (T.orderIsoOfFin rfl).toEquiv (square_block_restriction G T)]
  congr 1

/- English proof (translation)
Establish `hB : G⁻¹ * G = 1` using `Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hd)`. Establish `hprod : square_block_restriction G⁻¹ T * square_block_restriction G T = 1`. Use extensionality with `x y`. Establish `h1 : (G⁻¹ * G) x.1 y.1 = (1 : Matrix (Fin N) (Fin N) ℂ) x.1 y.1` using `by rw [hB]`. Rewrite `h1` using `[Matrix.mul_apply, ← Finset.sum_subset (Finset.subset_univ T) (f := fun c => G⁻¹ x.1 c * G c y.1) (fun c _ hc => by rw [h x.1 x.2 c hc, zero_mul]), ← Finset.sum_coe_sort T, Matrix.one_apply]`.

Establish `h3 : (square_block_restriction G⁻¹ T * square_block_restriction G T) x y = ∑ i : {x // x ∈ T}, G⁻¹ x.1 i.1 * G i.1 y.1` using `rfl`. Rewrite using `[h3, h1, Matrix.one_apply]`. Distinguish the cases in `hxy : x = y`. Rewrite using `[if_pos hxy, if_pos (congrArg Subtype.val hxy)]`. Rewrite using `[if_neg hxy, if_neg (fun h => hxy (Subtype.ext h))]`.

Introduce `h0`. Establish `h2` using `congrArg Matrix.det hprod`. Rewrite `h2` using `[Matrix.det_mul, h0, mul_zero, Matrix.det_one]`. Conclude with `zero_ne_one h2`.
-/
theorem det_squareBlockRestriction_ne_zero (G : Matrix (Fin N) (Fin N) ℂ) (hd : G.det ≠ 0) (T : Finset (Fin N))
    (h : ∀ x ∈ T, ∀ c, c ∉ T → G⁻¹ x c = 0) : (square_block_restriction G T).det ≠ 0 := by
  have hB : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hd)
  have hprod : square_block_restriction G⁻¹ T * square_block_restriction G T = 1 := by
    ext x y
    have h1 : (G⁻¹ * G) x.1 y.1 = (1 : Matrix (Fin N) (Fin N) ℂ) x.1 y.1 := by rw [hB]
    rw [Matrix.mul_apply, ← Finset.sum_subset (Finset.subset_univ T)
      (f := fun c => G⁻¹ x.1 c * G c y.1) (fun c _ hc => by rw [h x.1 x.2 c hc, zero_mul]),
      ← Finset.sum_coe_sort T, Matrix.one_apply] at h1
    have h3 : (square_block_restriction G⁻¹ T * square_block_restriction G T) x y = ∑ i : {x // x ∈ T}, G⁻¹ x.1 i.1 * G i.1 y.1 := rfl
    rw [h3, h1, Matrix.one_apply]
    by_cases hxy : x = y
    · rw [if_pos hxy, if_pos (congrArg Subtype.val hxy)]
    · rw [if_neg hxy, if_neg (fun h => hxy (Subtype.ext h))]
  intro h0
  have h2 := congrArg Matrix.det hprod
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at h2
  exact zero_ne_one h2

/- English proof (translation)
Establish `hex : ∀ b, ∃ n, ∃ T ∈ F, b ∈ T ∧ T.card = n` using `fun b => by`. Take `⟨T, hT, hb⟩` from `hcov b`. Conclude with `⟨T.card, T, hT, hb, rfl⟩`. Establish `hmin : ∀ b, ∃ T ∈ F, b ∈ T ∧ ∀ T' ∈ F, b ∈ T' → T ⊆ T'`. Introduce `b`.

Take `⟨T, hTF, hbT, hcard⟩` from `Nat.find_spec (hex b)`. Use `⟨T, hTF, hbT, fun T' hT'F hbT' => ?_⟩` and prove the remaining obligations. Break down `hnest T hTF T' hT'F b hbT hbT' with h1 | h1` into its components or cases. Conclude with `h1`. Establish `hle : T.card ≤ T'.card`.

Rewrite using `[hcard]`. Conclude with `Nat.find_min' (hex b) ⟨T', hT'F, hbT', rfl⟩`. Conclude with `le_of_eq (Finset.eq_of_subset_of_card_le h1 hle).symm`. Use `choose Tb hTbF hbTb hTbmin using hmin`. Use `⟨Matrix.of fun x b => if hx : x ∈ Tb b then (square_block_restriction G (Tb b))⁻¹ ⟨x, hx⟩ ⟨b, hbTb b⟩ else 0, ?_, ?_⟩` and prove the remaining obligations.

Introduce `T hT c hc x hx`. Establish `hx' : x ∉ Tb c` using `fun h' => hx (hTbmin c T hT hc h')`. Simplify using `only [Matrix.of_apply, dif_neg hx']`. Introduce `a b hab`. Establish `ha : a ∈ Tb b` using `hab (Tb b) (hTbF b) (hbTb b)`.

Establish `hM : square_block_restriction G (Tb b) * (square_block_restriction G (Tb b))⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hinv _ (hTbF b)))`. Establish `h1` using `congrFun (congrFun hM ⟨a, ha⟩) ⟨b, hbTb b⟩`. Rewrite `h1` using `[Matrix.mul_apply, Matrix.one_apply]`. Establish `h2 : ∀ x : {x // x ∈ Tb b}, G a x.1 * (if hx : x.1 ∈ Tb b then (square_block_restriction G (Tb b))⁻¹ ⟨x.1, hx⟩ ⟨b, hbTb b⟩ else 0) = square_block_restriction G (Tb b) ⟨a, ha⟩ x * (square_block_restriction G (Tb b))⁻¹ x ⟨b, hbTb b⟩`. Introduce `x`.

Rewrite using `[dif_pos x.2]`. Both sides reduce to the same expression. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[← Finset.sum_subset (Finset.subset_univ (Tb b)) (f := fun x => G a x * (if hx : x ∈ Tb b then (square_block_restriction G (Tb b))⁻¹ ⟨x, hx⟩ ⟨b, hbTb b⟩ else 0)) (fun x _ hx => by simp only [dif_neg hx, mul_zero]), ← Finset.sum_coe_sort (Tb b), Finset.sum_congr rfl (fun x _ => h2 …`.

Simplify using `only [Subtype.mk.injEq]`.
-/
theorem exists_cols (G : Matrix (Fin N) (Fin N) ℂ) (F : Set (Finset (Fin N))) (hcov : ∀ b, ∃ T ∈ F, b ∈ T)
    (hnest : ∀ T ∈ F, ∀ T' ∈ F, ∀ b, b ∈ T → b ∈ T' → T ⊆ T' ∨ T' ⊆ T)
    (hinv : ∀ T ∈ F, (square_block_restriction G T).det ≠ 0) :
    ∃ W : Matrix (Fin N) (Fin N) ℂ, (∀ T ∈ F, ∀ c ∈ T, ∀ x, x ∉ T → W x c = 0) ∧
      ∀ a b, (∀ T ∈ F, b ∈ T → a ∈ T) → (G * W) a b = if a = b then 1 else 0 := by
  have hex : ∀ b, ∃ n, ∃ T ∈ F, b ∈ T ∧ T.card = n := fun b => by
    obtain ⟨T, hT, hb⟩ := hcov b
    exact ⟨T.card, T, hT, hb, rfl⟩
  have hmin : ∀ b, ∃ T ∈ F, b ∈ T ∧ ∀ T' ∈ F, b ∈ T' → T ⊆ T' := by
    intro b
    obtain ⟨T, hTF, hbT, hcard⟩ := Nat.find_spec (hex b)
    refine ⟨T, hTF, hbT, fun T' hT'F hbT' => ?_⟩
    rcases hnest T hTF T' hT'F b hbT hbT' with h1 | h1
    · exact h1
    · have hle : T.card ≤ T'.card := by
        rw [hcard]
        exact Nat.find_min' (hex b) ⟨T', hT'F, hbT', rfl⟩
      exact le_of_eq (Finset.eq_of_subset_of_card_le h1 hle).symm
  choose Tb hTbF hbTb hTbmin using hmin
  refine ⟨Matrix.of fun x b => if hx : x ∈ Tb b then (square_block_restriction G (Tb b))⁻¹ ⟨x, hx⟩ ⟨b, hbTb b⟩ else 0, ?_, ?_⟩
  · intro T hT c hc x hx
    have hx' : x ∉ Tb c := fun h' => hx (hTbmin c T hT hc h')
    simp only [Matrix.of_apply, dif_neg hx']
  · intro a b hab
    have ha : a ∈ Tb b := hab (Tb b) (hTbF b) (hbTb b)
    have hM : square_block_restriction G (Tb b) * (square_block_restriction G (Tb b))⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hinv _ (hTbF b)))
    have h1 := congrFun (congrFun hM ⟨a, ha⟩) ⟨b, hbTb b⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    have h2 : ∀ x : {x // x ∈ Tb b}, G a x.1 * (if hx : x.1 ∈ Tb b then (square_block_restriction G (Tb b))⁻¹ ⟨x.1, hx⟩ ⟨b, hbTb b⟩ else 0) =
        square_block_restriction G (Tb b) ⟨a, ha⟩ x * (square_block_restriction G (Tb b))⁻¹ x ⟨b, hbTb b⟩ := by
      intro x
      rw [dif_pos x.2]
      rfl
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [← Finset.sum_subset (Finset.subset_univ (Tb b))
      (f := fun x => G a x * (if hx : x ∈ Tb b then (square_block_restriction G (Tb b))⁻¹ ⟨x, hx⟩ ⟨b, hbTb b⟩ else 0))
      (fun x _ hx => by simp only [dif_neg hx, mul_zero]),
      ← Finset.sum_coe_sort (Tb b), Finset.sum_congr rfl (fun x _ => h2 x), h1]
    simp only [Subtype.mk.injEq]

def IsSeg (N j : ℕ) (T : Finset (Fin N)) : Prop :=
  (∃ m, m ≤ N - j ∧ T = Finset.univ.filter fun a : Fin N => (a : ℕ) < m) ∨
    ∃ m, T = Finset.univ.filter fun a : Fin N => N - j ≤ (a : ℕ) ∧ (a : ℕ) < m

/- English proof (translation)
Conclude with `Or.inl ⟨N - j, le_refl _, rfl⟩`.
-/
theorem isSeg_omIdx (N j : ℕ) : IsSeg N j (omIdx N j) := by
  exact Or.inl ⟨N - j, le_refl _, rfl⟩

/- English proof (translation)
The claim follows from `Or.inr ⟨N, by ext a; simp [wIdx]⟩`.
-/
theorem isSeg_wIdx (N j : ℕ) : IsSeg N j (wIdx N j) :=
  Or.inr ⟨N, by ext a; simp [wIdx]⟩

/- English proof (translation)
Establish `hi` using `i.isLt`. Unfold `IsSeg stepCols`. Distinguish the cases in `h : (i : ℕ) + 1 ≤ j`. Use `right`. Conclude with `⟨N - j + ((i : ℕ) + 1), by ext a; simp [h]⟩`.

Use `left`. Conclude with `⟨(i : ℕ) + 1 - j, by omega, by ext a; simp [h]⟩`.
-/
theorem isSeg_stepCols (N j : ℕ) (i : Fin N) : IsSeg N j (stepCols N j i) := by
  have hi := i.isLt
  unfold IsSeg stepCols
  by_cases h : (i : ℕ) + 1 ≤ j
  · right
    exact ⟨N - j + ((i : ℕ) + 1), by ext a; simp [h]⟩
  · left
    exact ⟨(i : ℕ) + 1 - j, by omega, by ext a; simp [h]⟩

/- English proof (translation)
Apply the tactic sequence `rcases h with ⟨m, hm, rfl⟩ | ⟨m, rfl⟩ <;> rcases h' with ⟨m', hm', rfl⟩ | ⟨m', rfl⟩ <;>`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hb hb'`. Apply the tactic sequence `all_goals first`. Consider the case `(exfalso; omega)`. Consider the case `(rcases le_total m m' with hmm | hmm`.

Use `left`. Introduce `a ha`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢`. Use linear arithmetic over natural numbers and integers. Use `right`.

Introduce `a ha`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢`. Use the proof step `omega)`.
-/
theorem IsSeg.nested {N j : ℕ} {T T' : Finset (Fin N)} (h : IsSeg N j T) (h' : IsSeg N j T') {b : Fin N}
    (hb : b ∈ T) (hb' : b ∈ T') : T ⊆ T' ∨ T' ⊆ T := by
  rcases h with ⟨m, hm, rfl⟩ | ⟨m, rfl⟩ <;> rcases h' with ⟨m', hm', rfl⟩ | ⟨m', rfl⟩ <;>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb hb'
  all_goals first
    | (exfalso; omega)
    | (rcases le_total m m' with hmm | hmm
       · left
         intro a ha
         simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
         omega
       · right
         intro a ha
         simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
         omega)

/- English proof (translation)
Establish `hab' : (a : ℕ) < b` using `hab`. Apply the tactic sequence `rcases h with ⟨m, hm, rfl⟩ | ⟨m, rfl⟩ <;>`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢`. Use linear arithmetic over natural numbers and integers. Establish `h1 : ¬ ((b : ℕ) < N - j)` using `by omega`.

Establish `h2 : ¬ ((a : ℕ) < N - j)` using `fun h => h1 (hs.mp h)`. Use linear arithmetic over natural numbers and integers.
-/
theorem IsSeg.down {N j : ℕ} {T : Finset (Fin N)} (h : IsSeg N j T) {a b : Fin N} (hb : b ∈ T) (hab : a < b)
    (hs : (a : ℕ) < N - j ↔ (b : ℕ) < N - j) : a ∈ T := by
  have hab' : (a : ℕ) < b := hab
  rcases h with ⟨m, hm, rfl⟩ | ⟨m, rfl⟩ <;>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
  · omega
  · have h1 : ¬ ((b : ℕ) < N - j) := by omega
    have h2 : ¬ ((a : ℕ) < N - j) := fun h => h1 (hs.mp h)
    omega

/- English proof (translation)
Introduce `N j kp G hjN hbd hdet hstep`. Establish `hGG : G * G⁻¹ = 1` using `Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hdet)`. Establish `hGinv : ∀ x c : Fin N, ¬ ((x : ℕ) < N - j ↔ (c : ℕ) < N - j) → G⁻¹ x c = 0` using `by set E : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun x c => if ((x : ℕ) < N - j ↔ (c : ℕ) < N - j) then G⁻¹ x c else 0) with hEdef`. Establish `hE : G * E = 1`. Use extensionality with `a c`.

Distinguish the cases in `hac : ((a : ℕ) < N - j ↔ (c : ℕ) < N - j)`. Rewrite using `[← hGG, Matrix.mul_apply, Matrix.mul_apply]`. Use `Finset.sum_congr rfl (fun x _ => ?_)` and prove the remaining obligations. Rewrite using `[hEdef, Matrix.of_apply]`. Distinguish the cases in `hxc : ((x : ℕ) < N - j ↔ (c : ℕ) < N - j)`.

Rewrite using `[if_pos hxc]`. Rewrite using `[if_neg hxc, hbd a x (fun hax => hxc (hax.symm.trans hac)), zero_mul, zero_mul]`. Establish `hne : a ≠ c` using `fun h => hac (by rw [h])`. Rewrite using `[Matrix.one_apply_ne hne, Matrix.mul_apply]`. Use `Finset.sum_eq_zero (fun x _ => ?_)` and prove the remaining obligations.

Rewrite using `[hEdef, Matrix.of_apply]`. Distinguish the cases in `hxc : ((x : ℕ) < N - j ↔ (c : ℕ) < N - j)`. Rewrite using `[hbd a x (fun hax => hac (hax.trans hxc)), zero_mul]`. Rewrite using `[if_neg hxc, mul_zero]`. Establish `hEinv : G⁻¹ = E` using `Matrix.inv_eq_right_inv hE`.

Introduce `x c hxc`. Rewrite using `[hEinv, hEdef, Matrix.of_apply, if_neg hxc]`. Establish `hom : (square_block_restriction G (omIdx N j)).det ≠ 0` using `det_squareBlockRestriction_ne_zero G hdet _ (fun x hx c hc => hGinv x c (fun h => by`. Simplify using `only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hx hc`. Conclude with `hc (h.mp hx)))`.

Establish `hw : (square_block_restriction G (wIdx N j)).det ≠ 0` using `det_squareBlockRestriction_ne_zero G hdet _ (fun x hx c hc => hGinv x c (fun h => by`. Simplify using `only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hx hc`. Conclude with `(not_lt.mpr hx) (h.mpr (not_le.mp hc))))`. Set `F : Set (Finset (Fin N))` to `{T | (∃ i, kp i ∧ IsProperStep N j i ∧ T = stepCols N j i) ∨ T = omIdx N j ∨ T = wIdx N j}`. Establish `hseg : ∀ T ∈ F, IsSeg N j T`.

Introduce and unpack `T (⟨i, -, -, rfl⟩ | rfl | rfl)`. Conclude with `isSeg_stepCols N j i`. Conclude with `isSeg_omIdx N j`. Conclude with `isSeg_wIdx N j`. Establish `hcov : ∀ b, ∃ T ∈ F, b ∈ T`.

Introduce `b`. Distinguish the cases in `hb : (b : ℕ) < N - j`. Conclude with `⟨omIdx N j, Or.inr (Or.inl rfl), by`. Simplify using `only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `hb⟩`.

Conclude with `⟨wIdx N j, Or.inr (Or.inr rfl), by`. Simplify using `only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `not_lt.mp hb⟩`. Establish `hinv : ∀ T ∈ F, (square_block_restriction G T).det ≠ 0`. Introduce and unpack `T (⟨i, hki, hpi, rfl⟩ | rfl | rfl)`.

Rewrite using `[← minorIJ_self]`. Conclude with `hstep i hki hpi`. Conclude with `hom`. Conclude with `hw`. Take `⟨W, hWsupp, hGW⟩` from `exists_cols G F hcov (fun T hT T' hT' b hb hb' => (hseg T hT).nested (hseg T' hT') hb hb') hinv`.

Establish `hWblk : IsBlockDiag j W`. Introduce `x c hxc`. Distinguish the cases in `hc : (c : ℕ) < N - j`. Use `hWsupp (omIdx N j) (Or.inr (Or.inl rfl)) c ?_ x ?_` and prove the remaining obligations. Simplify using `only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]`.

Conclude with `hc`. Simplify using `only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]`. Introduce `hx`. Conclude with `hxc (iff_of_true hx hc)`. Use `hWsupp (wIdx N j) (Or.inr (Or.inr rfl)) c ?_ x ?_` and prove the remaining obligations.

Simplify using `only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `not_lt.mp hc`. Simplify using `only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]`. Introduce `hx`. Conclude with `hxc (iff_of_false (not_lt.mpr hx) hc)`.

Establish `hLblk : IsBlockDiag j (G * W)`. Introduce `a b hab`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero (fun x _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hxb : ((x : ℕ) < N - j ↔ (b : ℕ) < N - j)`.

Rewrite using `[hbd a x (fun hax => hab (hax.trans hxb)), zero_mul]`. Rewrite using `[hWblk x b hxb, mul_zero]`. Use `⟨G * W, W, hLblk, ⟨fun a => ?_, fun a b hab => ?_⟩, ?_, hWblk, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[hGW a a (fun T _ h => h), if_pos rfl]`. Distinguish the cases in `hs : ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)`.

Rewrite using `[hGW a b (fun T hT hb => (hseg T hT).down hb hab hs), if_neg (ne_of_lt hab)]`. Conclude with `hLblk a b hs`. Introduce `a b hba hs hno`. Use `(hGW a b ?_).trans (if_neg (ne_of_gt hba))` and prove the remaining obligations. Introduce and unpack `T (⟨i, hki, hpi, rfl⟩ | rfl | rfl) hb`.

Assume the negation of the conclusion as `ha`. Conclude with `hno ⟨i, hki, hpi, hb, ha⟩`. Simplify using `only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢`. Conclude with `hs.mpr hb`. Simplify using `only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢`.

Conclude with `not_lt.mp (fun h => (not_lt.mpr hb) (hs.mp h))`. Introduce `i hki hpi c hc x hx`. Conclude with `hWsupp _ (Or.inl ⟨i, hki, hpi, rfl⟩) c hc x hx`.
-/
theorem exists_lu : ∀ (N j : ℕ) (kp : Fin N → Prop) (G : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j G → G.det ≠ 0 → (∀ i, kp i → IsProperStep N j i → minorIJ G (stepCols N j i) (stepCols N j i) ≠ 0) → ∃ L W : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j L ∧ IsLowerUni L ∧ (∀ a b : Fin N, b < a → ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) → (¬ ∃ i, kp i ∧ IsProperStep N j i ∧ b ∈ stepCols N j i ∧ a ∉ stepCols N j i) → L a b = 0) ∧ IsBlockDiag j W ∧ (∀ i, kp i → IsProperStep N j i → ∀ c ∈ stepCols N j i, ∀ x, x ∉ stepCols N j i → W x c = 0) ∧ G * W = L := by
  intro N j kp G hjN hbd hdet hstep
  have hGG : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hdet)
  have hGinv : ∀ x c : Fin N, ¬ ((x : ℕ) < N - j ↔ (c : ℕ) < N - j) → G⁻¹ x c = 0 := by
    set E : Matrix (Fin N) (Fin N) ℂ :=
      Matrix.of (fun x c => if ((x : ℕ) < N - j ↔ (c : ℕ) < N - j) then G⁻¹ x c else 0) with hEdef
    have hE : G * E = 1 := by
      ext a c
      by_cases hac : ((a : ℕ) < N - j ↔ (c : ℕ) < N - j)
      · rw [← hGG, Matrix.mul_apply, Matrix.mul_apply]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [hEdef, Matrix.of_apply]
        by_cases hxc : ((x : ℕ) < N - j ↔ (c : ℕ) < N - j)
        · rw [if_pos hxc]
        · rw [if_neg hxc, hbd a x (fun hax => hxc (hax.symm.trans hac)), zero_mul, zero_mul]
      · have hne : a ≠ c := fun h => hac (by rw [h])
        rw [Matrix.one_apply_ne hne, Matrix.mul_apply]
        refine Finset.sum_eq_zero (fun x _ => ?_)
        rw [hEdef, Matrix.of_apply]
        by_cases hxc : ((x : ℕ) < N - j ↔ (c : ℕ) < N - j)
        · rw [hbd a x (fun hax => hac (hax.trans hxc)), zero_mul]
        · rw [if_neg hxc, mul_zero]
    have hEinv : G⁻¹ = E := Matrix.inv_eq_right_inv hE
    intro x c hxc
    rw [hEinv, hEdef, Matrix.of_apply, if_neg hxc]
  have hom : (square_block_restriction G (omIdx N j)).det ≠ 0 := det_squareBlockRestriction_ne_zero G hdet _ (fun x hx c hc => hGinv x c (fun h => by
    simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hx hc
    exact hc (h.mp hx)))
  have hw : (square_block_restriction G (wIdx N j)).det ≠ 0 := det_squareBlockRestriction_ne_zero G hdet _ (fun x hx c hc => hGinv x c (fun h => by
    simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hx hc
    exact (not_lt.mpr hx) (h.mpr (not_le.mp hc))))
  let F : Set (Finset (Fin N)) := {T | (∃ i, kp i ∧ IsProperStep N j i ∧ T = stepCols N j i) ∨
    T = omIdx N j ∨ T = wIdx N j}
  have hseg : ∀ T ∈ F, IsSeg N j T := by
    rintro T (⟨i, -, -, rfl⟩ | rfl | rfl)
    · exact isSeg_stepCols N j i
    · exact isSeg_omIdx N j
    · exact isSeg_wIdx N j
  have hcov : ∀ b, ∃ T ∈ F, b ∈ T := by
    intro b
    by_cases hb : (b : ℕ) < N - j
    · exact ⟨omIdx N j, Or.inr (Or.inl rfl), by
        simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]; exact hb⟩
    · exact ⟨wIdx N j, Or.inr (Or.inr rfl), by
        simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]; exact not_lt.mp hb⟩
  have hinv : ∀ T ∈ F, (square_block_restriction G T).det ≠ 0 := by
    rintro T (⟨i, hki, hpi, rfl⟩ | rfl | rfl)
    · rw [← minorIJ_self]
      exact hstep i hki hpi
    · exact hom
    · exact hw
  obtain ⟨W, hWsupp, hGW⟩ := exists_cols G F hcov
    (fun T hT T' hT' b hb hb' => (hseg T hT).nested (hseg T' hT') hb hb') hinv
  have hWblk : IsBlockDiag j W := by
    intro x c hxc
    by_cases hc : (c : ℕ) < N - j
    · refine hWsupp (omIdx N j) (Or.inr (Or.inl rfl)) c ?_ x ?_
      · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]; exact hc
      · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]
        intro hx
        exact hxc (iff_of_true hx hc)
    · refine hWsupp (wIdx N j) (Or.inr (Or.inr rfl)) c ?_ x ?_
      · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]; exact not_lt.mp hc
      · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
        intro hx
        exact hxc (iff_of_false (not_lt.mpr hx) hc)
  have hLblk : IsBlockDiag j (G * W) := by
    intro a b hab
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    by_cases hxb : ((x : ℕ) < N - j ↔ (b : ℕ) < N - j)
    · rw [hbd a x (fun hax => hab (hax.trans hxb)), zero_mul]
    · rw [hWblk x b hxb, mul_zero]
  refine ⟨G * W, W, hLblk, ⟨fun a => ?_, fun a b hab => ?_⟩, ?_, hWblk, ?_, rfl⟩
  · rw [hGW a a (fun T _ h => h), if_pos rfl]
  · by_cases hs : ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
    · rw [hGW a b (fun T hT hb => (hseg T hT).down hb hab hs), if_neg (ne_of_lt hab)]
    · exact hLblk a b hs
  · intro a b hba hs hno
    refine (hGW a b ?_).trans (if_neg (ne_of_gt hba))
    rintro T (⟨i, hki, hpi, rfl⟩ | rfl | rfl) hb
    · by_contra ha
      exact hno ⟨i, hki, hpi, hb, ha⟩
    · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact hs.mpr hb
    · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact not_lt.mp (fun h => (not_lt.mpr hb) (hs.mp h))
  · intro i hki hpi c hc x hx
    exact hWsupp _ (Or.inl ⟨i, hki, hpi, rfl⟩) c hc x hx

end GlobalTheory.CompanionTheory.Ar.PB.BigCellLU
