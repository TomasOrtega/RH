import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ShearMp
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RootHaarLoc

noncomputable section

open MeasureTheory Matrix

namespace Formalism.L2.SG.lowerTriangularModel

variable {m : ℕ} (w : Equiv.Perm (Fin m))

local notation "L" => Formalism.FourierDecayAlt.P.Dx2.Rad.low w

def ht (q : Formalism.FourierDecayAlt.C2.Lstidx w) : ℕ := q.1.1.val - q.1.2.val

/- English proof (translation)
Rewrite using `[Formalism.FourierDecayAlt.P.Dx2.Rad.low_apply, Matrix.one_apply_ne (ne_of_lt h), zero_add, dif_neg]`. Introduce and unpack `⟨h1, -⟩`. Conclude with `absurd (lt_trans h1 h) (lt_irrefl _)`.
-/
theorem low_upper (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) (i j : Fin m) (h : i < j) : L y i j = 0 := by
  rw [Formalism.FourierDecayAlt.P.Dx2.Rad.low_apply, Matrix.one_apply_ne (ne_of_lt h), zero_add, dif_neg]
  rintro ⟨h1, -⟩
  exact absurd (lt_trans h1 h) (lt_irrefl _)

/- English proof (translation)
Rewrite using `[Formalism.FourierDecayAlt.P.Dx2.Rad.low_apply, Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1), add_zero]`.
-/
theorem low_diag (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) (i : Fin m) : L y i i = 1 := by
  rw [Formalism.FourierDecayAlt.P.Dx2.Rad.low_apply, Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1), add_zero]

/- English proof (translation)
Introduce `i j hij`. Conclude with `low_upper w y i j hij`.
-/
theorem low_bt (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) : (L y).BlockTriangular OrderDual.toDual := by
  intro i j hij
  exact low_upper w y i j hij

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular _ (low_bt w y)]`. Conclude with `Finset.prod_eq_one fun i _ => low_diag w y i`.
-/
theorem low_det (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) : (L y).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (low_bt w y)]
  exact Finset.prod_eq_one fun i _ => low_diag w y i

abbrev M (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) : Matrix (Fin m) (Fin m) ℂ := (L y)⁻¹

/- English proof (translation)
Rewrite using `[low_det]`. Conclude with `isUnit_one`.
-/
theorem isUnit_low (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) : IsUnit (L y).det := by rw [low_det]; exact isUnit_one

/- English proof (translation)
Use `haveI := Matrix.invertibleOfIsUnitDet (L y) (isUnit_low w y)`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular (low_bt w y) h`.
-/
theorem M_upper (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) (i j : Fin m) (h : i < j) : M w y i j = 0 := by
  haveI := Matrix.invertibleOfIsUnitDet (L y) (isUnit_low w y)
  exact Matrix.blockTriangular_inv_of_blockTriangular (low_bt w y) h

/- English proof (translation)
The claim follows from `Matrix.mul_nonsing_inv _ (isUnit_low w y)`.
-/
theorem mul_M (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) : L y * M w y = 1 := Matrix.mul_nonsing_inv _ (isUnit_low w y)

/- English proof (translation)
Rewrite using `[Finset.sum_filter]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Both sides reduce to the same expression. Break down `not_and_or.1 h with h1 | h1` into its components or cases.

Rewrite using `[M_upper w y c j (not_le.1 h1), mul_zero]`. Rewrite using `[low_upper w y i c (not_le.1 h1), zero_mul]`.
-/
theorem sum_split (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) (i j : Fin m) :
    ∑ c, L y i c * M w y c j = ∑ c ∈ Finset.univ.filter (fun c => j ≤ c ∧ c ≤ i), L y i c * M w y c j := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with h
  · rfl
  · rcases not_and_or.1 h with h1 | h1
    · rw [M_upper w y c j (not_le.1 h1), mul_zero]
    · rw [low_upper w y i c (not_le.1 h1), zero_mul]

/- English proof (translation)
Establish `h` using `congrFun (congrFun (mul_M w y) i) i`. Rewrite `h` using `[Matrix.mul_apply, sum_split, Matrix.one_apply_eq]`. Establish `e : Finset.univ.filter (fun c => i ≤ c ∧ c ≤ i) = {i}`. Use extensionality with `c`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]`.

Conclude with `⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩`. Rewrite `h` using `[e, Finset.sum_singleton, low_diag, one_mul]`. Conclude with `h`.
-/
theorem M_diag (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) (i : Fin m) : M w y i i = 1 := by
  have h := congrFun (congrFun (mul_M w y) i) i
  rw [Matrix.mul_apply, sum_split, Matrix.one_apply_eq] at h
  have e : Finset.univ.filter (fun c => i ≤ c ∧ c ≤ i) = {i} := by
    ext c; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩
  rw [e, Finset.sum_singleton, low_diag, one_mul] at h
  exact h

/- English proof (translation)
Establish `h` using `congrFun (congrFun (mul_M w y) i) j`. Rewrite `h` using `[Matrix.mul_apply, sum_split, Matrix.one_apply_ne (ne_of_gt hji)]`. Establish `e : Finset.univ.filter (fun c => j ≤ c ∧ c ≤ i) = insert i (insert j (Finset.univ.filter (fun c => j < c ∧ c < i)))`. Use extensionality with `c`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Break down `h2.lt_or_eq with h2 | h2` into its components or cases. Break down `h1.lt_or_eq with h1 | h1` into its components or cases. Conclude with `Or.inr (Or.inr ⟨h1, h2⟩)`.

Conclude with `Or.inr (Or.inl h1.symm)`. Conclude with `Or.inl h2`. Introduce and unpack `(h | h | h)`. Conclude with `⟨h ▸ hji.le, h ▸ le_rfl⟩`. Conclude with `⟨h ▸ le_rfl, h ▸ hji.le⟩`.

Conclude with `⟨h.1.le, h.2.le⟩`. Establish `hi : i ∉ insert j (Finset.univ.filter (fun c => j < c ∧ c < i))`. Simplify using `only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, not_or]`. Conclude with `⟨ne_of_gt hji, fun h => lt_irrefl _ h.2⟩`. Establish `hj : j ∉ Finset.univ.filter (fun c => j < c ∧ c < i)`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `fun h => lt_irrefl _ h.1`. Rewrite `h` using `[e, Finset.sum_insert hi, Finset.sum_insert hj, low_diag, one_mul, M_diag, mul_one]`. Take the linear combination `h`.
-/
theorem M_rec (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) (i j : Fin m) (hji : j < i) :
    M w y i j + L y i j = -∑ c ∈ Finset.univ.filter (fun c => j < c ∧ c < i), L y i c * M w y c j := by
  have h := congrFun (congrFun (mul_M w y) i) j
  rw [Matrix.mul_apply, sum_split, Matrix.one_apply_ne (ne_of_gt hji)] at h
  have e : Finset.univ.filter (fun c => j ≤ c ∧ c ≤ i) =
      insert i (insert j (Finset.univ.filter (fun c => j < c ∧ c < i))) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h2.lt_or_eq with h2 | h2
      · rcases h1.lt_or_eq with h1 | h1
        · exact Or.inr (Or.inr ⟨h1, h2⟩)
        · exact Or.inr (Or.inl h1.symm)
      · exact Or.inl h2
    · rintro (h | h | h)
      · exact ⟨h ▸ hji.le, h ▸ le_rfl⟩
      · exact ⟨h ▸ le_rfl, h ▸ hji.le⟩
      · exact ⟨h.1.le, h.2.le⟩
  have hi : i ∉ insert j (Finset.univ.filter (fun c => j < c ∧ c < i)) := by
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, not_or]
    exact ⟨ne_of_gt hji, fun h => lt_irrefl _ h.2⟩
  have hj : j ∉ Finset.univ.filter (fun c => j < c ∧ c < i) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun h => lt_irrefl _ h.1
  rw [e, Finset.sum_insert hi, Finset.sum_insert hj, low_diag, one_mul, M_diag, mul_one] at h
  linear_combination h

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `y y' hy i j hij`. Break down `lt_trichotomy i j with h | h | h` into its components or cases. Rewrite using `[M_upper w y i j h, M_upper w y' i j h]`.

Substitute `h` using the available equality. Rewrite using `[M_diag, M_diag]`. Establish `hL : ∀ a b : Fin m, a.val - b.val ≤ n → L y a b = L y' a b`. Introduce `a b hab`. Rewrite using `[Formalism.FourierDecayAlt.P.Dx2.Rad.low_apply, Formalism.FourierDecayAlt.P.Dx2.Rad.low_apply]`.

Use `congr 1`. Use `split_ifs with hq`. Conclude with `hy _ hab`. Both sides reduce to the same expression. Establish `e1` using `M_rec w y i j h`.

Establish `e2` using `M_rec w y' i j h`. Establish `hsum : ∑ c ∈ Finset.univ.filter (fun c => j < c ∧ c < i), L y i c * M w y c j = ∑ c ∈ Finset.univ.filter (fun c => j < c ∧ c < i), L y' i c * M w y' c j`. Use `Finset.sum_congr rfl fun c hc => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hc`. Establish `hc1` using `Fin.lt_def.1 hc.1`.

Establish `hc2` using `Fin.lt_def.1 hc.2`. Rewrite using `[hL i c (by omega)]`. Use `congr 1`. Conclude with `ih (c.val - j.val) (by omega) y y' (fun q hq => hy q (by omega)) c j le_rfl`. Use `hL i j hij` as an intermediate fact.

Take the linear combination `e1 - e2 - this - hsum`.
-/
theorem M_dep (n : ℕ) : ∀ (y y' : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ), (∀ q, ht w q ≤ n → y q = y' q) →
    ∀ i j : Fin m, i.val - j.val ≤ n → M w y i j = M w y' i j := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y y' hy i j hij
  rcases lt_trichotomy i j with h | h | h
  · rw [M_upper w y i j h, M_upper w y' i j h]
  · subst h; rw [M_diag, M_diag]
  · have hL : ∀ a b : Fin m, a.val - b.val ≤ n → L y a b = L y' a b := by
      intro a b hab
      rw [Formalism.FourierDecayAlt.P.Dx2.Rad.low_apply, Formalism.FourierDecayAlt.P.Dx2.Rad.low_apply]
      congr 1
      split_ifs with hq
      · exact hy _ hab
      · rfl
    have e1 := M_rec w y i j h
    have e2 := M_rec w y' i j h
    have hsum : ∑ c ∈ Finset.univ.filter (fun c => j < c ∧ c < i), L y i c * M w y c j =
        ∑ c ∈ Finset.univ.filter (fun c => j < c ∧ c < i), L y' i c * M w y' c j := by
      refine Finset.sum_congr rfl fun c hc => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      have hc1 := Fin.lt_def.1 hc.1
      have hc2 := Fin.lt_def.1 hc.2
      rw [hL i c (by omega)]
      congr 1
      exact ih (c.val - j.val) (by omega) y y' (fun q hq => hy q (by omega)) c j le_rfl
    have := hL i j hij
    linear_combination e1 - e2 - this - hsum

def linv (y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ := fun q => M w y q.1.1 q.1.2

/- English proof (translation)
Establish `e : (fun y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ => L y) = fun y => Matrix.of fun i j => (1 : Matrix (Fin m) (Fin m) ℂ) i j + if h : j < i ∧ w.symm i < w.symm j then y ⟨(i, j), h⟩ else 0`. Use function extensionality and compare the values at `y`. Use extensionality with `i j`. Conclude with `Formalism.FourierDecayAlt.P.Dx2.Rad.low_apply w y i j`. Rewrite using `[e]`.

Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.of_apply]`. Use `split_ifs`. Conclude with `continuous_const.add (continuous_apply _)`. Conclude with `continuous_const`.
-/
theorem low_cont : Continuous (fun y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ => L y) := by
  have e : (fun y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ => L y) = fun y => Matrix.of fun i j =>
      (1 : Matrix (Fin m) (Fin m) ℂ) i j + if h : j < i ∧ w.symm i < w.symm j then y ⟨(i, j), h⟩ else 0 := by
    funext y; ext i j; exact Formalism.FourierDecayAlt.P.Dx2.Rad.low_apply w y i j
  rw [e]
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.of_apply]
  split_ifs
  · exact continuous_const.add (continuous_apply _)
  · exact continuous_const

/- English proof (translation)
Establish `e : (fun y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ => M w y) = fun y => (L y).adjugate`. Use function extensionality and compare the values at `y`. Use `show (L y)⁻¹ = _`. Rewrite using `[Matrix.inv_def, low_det, Ring.inverse_one, one_smul]`. Rewrite using `[e]`.

Conclude with `(low_cont w).matrix_adjugate`.
-/
theorem M_cont : Continuous (fun y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ => M w y) := by
  have e : (fun y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ => M w y) = fun y => (L y).adjugate := by
    funext y
    show (L y)⁻¹ = _
    rw [Matrix.inv_def, low_det, Ring.inverse_one, one_smul]
  rw [e]
  exact (low_cont w).matrix_adjugate

/- English proof (translation)
Use `set τ : ∀ q : Formalism.FourierDecayAlt.C2.Lstidx w, (Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) → ℂ := fun q y => -(M w y q.1.1 q.1.2 + y q) with hτ`. Establish `hmeas : ∀ q, Measurable (τ q)` using `fun q => by`. Use `Measurable.neg (Measurable.add ?_ (measurable_pi_apply q))` and prove the remaining obligations. Conclude with `((continuous_apply q.1.2).comp ((continuous_apply q.1.1).comp (M_cont w))).measurable`. Establish `hdep : ∀ q (x x' : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ), (∀ q', ht w q' < ht w q → x q' = x' q') → τ q x = τ q x'`.

Introduce `q x x' hx`. Establish `hq` using `q.2.1`. Establish `hq'` using `Fin.lt_def.1 hq`. Simplify using `only [hτ]`. Use `congr 1`.

Establish `e1` using `M_rec w x q.1.1 q.1.2 hq`. Establish `e2` using `M_rec w x' q.1.1 q.1.2 hq`. Establish `hLq : ∀ y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ, L y q.1.1 q.1.2 = y q` using `fun y => by`. Rewrite using `[Formalism.FourierDecayAlt.P.Dx2.Rad.low_coord]`. Rewrite `e1`, `e2` using `[hLq]`.

Rewrite using `[e1, e2]`. Use `congr 1`. Use `Finset.sum_congr rfl fun c hc => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hc`. Establish `hc1` using `Fin.lt_def.1 hc.1`.

Establish `hc2` using `Fin.lt_def.1 hc.2`. Establish `hL : L x q.1.1 c = L x' q.1.1 c`. Rewrite using `[Formalism.FourierDecayAlt.P.Dx2.Rad.low_apply, Formalism.FourierDecayAlt.P.Dx2.Rad.low_apply]`. Use `congr 1`. Use `split_ifs with h`.

Conclude with `hx _ (by simp only [ht]; omega)`. Both sides reduce to the same expression. Rewrite using `[hL]`. Use `congr 1`. Conclude with `M_dep w (c.val - q.1.2.val) x x' (fun q' hq'' => hx q' (by simp only [ht] at hq'' ⊢; omega)) c q.1.2 le_rfl`.

Establish `hS` using `Formalism.L2.SG.NGCut.SplitEmbedding.shear_mp _ (Formalism.FourierDecayAlt.C2.Lstidx w) rfl (fun _ => ℂ) (fun _ => volume) (ht w) τ hmeas hdep`. Establish `hN` using `Measure.measurePreserving_neg (volume : Measure (Formalism.FourierDecayAlt.C2.Lstidx w → ℂ))`. Establish `e : linv w = Neg.neg ∘ (fun g p => g p + τ p g)`. Use function extensionality and compare the values at `y q`. Simplify using `only [Function.comp_apply, Pi.neg_apply, hτ, linv]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hN.comp hS`.
-/
theorem linv_mp : MeasurePreserving (linv w) volume volume := by
  set τ : ∀ q : Formalism.FourierDecayAlt.C2.Lstidx w, (Formalism.FourierDecayAlt.C2.Lstidx w → ℂ) → ℂ := fun q y => -(M w y q.1.1 q.1.2 + y q) with hτ
  have hmeas : ∀ q, Measurable (τ q) := fun q => by
    refine Measurable.neg (Measurable.add ?_ (measurable_pi_apply q))
    exact ((continuous_apply q.1.2).comp ((continuous_apply q.1.1).comp (M_cont w))).measurable
  have hdep : ∀ q (x x' : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ), (∀ q', ht w q' < ht w q → x q' = x' q') → τ q x = τ q x' := by
    intro q x x' hx
    have hq := q.2.1
    have hq' := Fin.lt_def.1 hq
    simp only [hτ]
    congr 1
    have e1 := M_rec w x q.1.1 q.1.2 hq
    have e2 := M_rec w x' q.1.1 q.1.2 hq
    have hLq : ∀ y : Formalism.FourierDecayAlt.C2.Lstidx w → ℂ, L y q.1.1 q.1.2 = y q := fun y => by
      rw [Formalism.FourierDecayAlt.P.Dx2.Rad.low_coord]
    rw [hLq] at e1 e2
    rw [e1, e2]
    congr 1
    refine Finset.sum_congr rfl fun c hc => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    have hc1 := Fin.lt_def.1 hc.1
    have hc2 := Fin.lt_def.1 hc.2
    have hL : L x q.1.1 c = L x' q.1.1 c := by
      rw [Formalism.FourierDecayAlt.P.Dx2.Rad.low_apply, Formalism.FourierDecayAlt.P.Dx2.Rad.low_apply]
      congr 1
      split_ifs with h
      · exact hx _ (by simp only [ht]; omega)
      · rfl
    rw [hL]
    congr 1
    exact M_dep w (c.val - q.1.2.val) x x' (fun q' hq'' => hx q' (by simp only [ht] at hq'' ⊢; omega)) c q.1.2 le_rfl
  have hS := Formalism.L2.SG.NGCut.SplitEmbedding.shear_mp _ (Formalism.FourierDecayAlt.C2.Lstidx w) rfl (fun _ => ℂ) (fun _ => volume) (ht w) τ hmeas hdep
  have hN := Measure.measurePreserving_neg (volume : Measure (Formalism.FourierDecayAlt.C2.Lstidx w → ℂ))
  have e : linv w = Neg.neg ∘ (fun g p => g p + τ p g) := by
    funext y q
    simp only [Function.comp_apply, Pi.neg_apply, hτ, linv]
    ring
  rw [e]
  exact hN.comp hS

end Formalism.L2.SG.lowerTriangularModel

end
