import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfLatSk

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Introduce `h`. Apply `shapeNZ.1 1` to reduce the goal to its premises. Unfold `ddPow`. Rewrite using `[h]`. Simplify using the standard rewrite rules.
-/
theorem ddS_ne : ddS D ≠ 0 := by
  intro h
  apply shapeNZ.1 1
  unfold ddPow; rw [h]; simp

/- English proof (translation)
Unfold `ddPow`. Rewrite using `[← zpow_add₀ ddS_ne]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ddPow_mul (i j : ℕ) : ddPow D i * ddPow D j = ddPow D (i + j) := by
  unfold ddPow
  rw [← zpow_add₀ ddS_ne]
  congr 1; push_cast; ring

/- English proof (translation)
Rewrite using `[← ddPow_mul]`. Conclude with `FractionalIdeal.mul_mem_mul hx hy`.
-/
theorem mem_ddPow_mul {i j : ℕ} {x y : D.host.E} (hx : x ∈ ddPow D i) (hy : y ∈ ddPow D j) :
    x * y ∈ ddPow D (i + j) := by
  rw [← ddPow_mul]; exact FractionalIdeal.mul_mem_mul hx hy

/- English proof (translation)
Use `FractionalIdeal.mul_mem_mul hx hy` as an intermediate fact. Unfold `qdPow at this ⊢`. Rewrite `this` using `[mul_assoc, ddPow_mul]`. Then use the resulting hypothesis.
-/
theorem mem_qdPow_mul {i j : ℕ} {x y : D.host.E} (hx : x ∈ qdPow D i) (hy : y ∈ ddPow D j) :
    x * y ∈ qdPow D (i + j) := by
  have := FractionalIdeal.mul_mem_mul hx hy
  unfold qdPow at this ⊢
  rwa [mul_assoc, ddPow_mul] at this

/- English proof (translation)
Rewrite using `[mul_comm, add_comm]`. Conclude with `mem_qdPow_mul hy hx`.
-/
theorem mem_ddPow_mul_qd {i j : ℕ} {x y : D.host.E} (hx : x ∈ ddPow D i) (hy : y ∈ qdPow D j) :
    x * y ∈ qdPow D (i + j) := by
  rw [mul_comm, add_comm]; exact mem_qdPow_mul hy hx

/- English proof (translation)
Unfold `ddPow`. Simplify using `only [CharP.cast_eq_zero, neg_zero, zpow_zero]`. Conclude with `(FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩`.
-/
theorem one_mem_ddPow0 : (1 : D.host.E) ∈ ddPow D 0 := by
  unfold ddPow; simp only [CharP.cast_eq_zero, neg_zero, zpow_zero]
  exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩

/- English proof (translation)
Rewrite `hx` using `[qdPow_mem_iff]`. Establish `h2 : ((gS D : ℕ) : D.host.E) ∈ ddPow D 0`. Unfold `ddPow`. Simplify using `only [CharP.cast_eq_zero, neg_zero, zpow_zero]`. Conclude with `(FractionalIdeal.mem_one_iff _).2 ⟨(gS D : ℕ), map_natCast _ _⟩`.

Use `mem_ddPow_mul h2 hx` as an intermediate fact. Rewrite `this` using `[zero_add, mul_div_cancel₀ _ gS_ne]`. Then use the resulting hypothesis.
-/
theorem qd_le_dd (h : ℕ) {x : D.host.E} (hx : x ∈ qdPow D h) : x ∈ ddPow D h := by
  rw [qdPow_mem_iff] at hx
  have h2 : ((gS D : ℕ) : D.host.E) ∈ ddPow D 0 := by
    unfold ddPow; simp only [CharP.cast_eq_zero, neg_zero, zpow_zero]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨(gS D : ℕ), map_natCast _ _⟩
  have := mem_ddPow_mul h2 hx
  rwa [zero_add, mul_div_cancel₀ _ gS_ne] at this

def GrD (M : MatR D) : Prop := ∀ a c : Fin (D.R.rS + 1), a ≤ c → M a c ∈ ddPow D (c.val - a.val)

/- English proof (translation)
Establish `hXi` using `upU_inv hX`. Establish `hd : IsUnit X.det` using `by rw [upU_det hX]; exact isUnit_one`. Establish `key : ∀ n : ℕ, ∀ a c : Fin (D.R.rS + 1), a ≤ c → c.val - a.val = n → X⁻¹ a c ∈ ddPow D n`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`.

Consider the case `_ n ih`. Introduce `a c hac hn`. Break down `eq_or_lt_of_le hac with h | h` into its components or cases. Substitute `h` using the available equality. Rewrite using `[(hXi a a).2 rfl]`.

Simplify using `only [Nat.sub_self] at hn`. Substitute `hn` using the available equality. Conclude with `one_mem_ddPow0`. Establish `h1` using `congrFun (congrFun (Matrix.mul_nonsing_inv X hd) a) c`. Rewrite `h1` using `[Matrix.mul_apply, Matrix.one_apply_ne (ne_of_lt h), ← Finset.add_sum_erase _ _ (Finset.mem_univ a), (hX a a).2 rfl, one_mul]`.

Establish `h2 : X⁻¹ a c = -∑ i ∈ Finset.univ.erase a, X a i * X⁻¹ i c`. Rewrite using `[eq_neg_iff_add_eq_zero]`. Conclude with `h1`. Rewrite using `[h2]`. Use `(ddPow D n : Submodule (𝓞 D.host.E) D.host.E).neg_mem (Submodule.sum_mem _ fun i hi => ?_)` and prove the remaining obligations.

Establish `hia : i ≠ a` using `Finset.ne_of_mem_erase hi`. Distinguish the cases in `hai : a < i`. Distinguish the cases in `hic : i ≤ c`. Establish `hlt : c.val - i.val < n` using `by have : a.val < i.val := hai; omega`. Establish `e : n = (i.val - a.val) + (c.val - i.val)` using `by have : a.val < i.val := hai; omega`.

Rewrite using `[e]`. Conclude with `mem_ddPow_mul (hG a i (le_of_lt hai)) (ih _ hlt i c hic rfl)`. Rewrite using `[(hXi i c).1 (lt_of_not_ge hic), mul_zero]`. Conclude with `FractionalIdeal.zero_mem _`. Rewrite using `[(hX a i).1 (lt_of_le_of_ne (not_lt.1 hai) hia), zero_mul]`.

Conclude with `FractionalIdeal.zero_mem _`. Introduce `a c hac`. Conclude with `key _ a c hac rfl`.
-/
theorem grD_inv {X : MatR D} (hX : UpU X) (hG : GrD X) : GrD X⁻¹ := by
  have hXi := upU_inv hX
  have hd : IsUnit X.det := by rw [upU_det hX]; exact isUnit_one
  have key : ∀ n : ℕ, ∀ a c : Fin (D.R.rS + 1), a ≤ c → c.val - a.val = n → X⁻¹ a c ∈ ddPow D n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a c hac hn
      rcases eq_or_lt_of_le hac with h | h
      · subst h; rw [(hXi a a).2 rfl]; simp only [Nat.sub_self] at hn; subst hn; exact one_mem_ddPow0
      ·
        have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv X hd) a) c
        rw [Matrix.mul_apply, Matrix.one_apply_ne (ne_of_lt h), ← Finset.add_sum_erase _ _ (Finset.mem_univ a),
          (hX a a).2 rfl, one_mul] at h1
        have h2 : X⁻¹ a c = -∑ i ∈ Finset.univ.erase a, X a i * X⁻¹ i c := by
          rw [eq_neg_iff_add_eq_zero]; exact h1
        rw [h2]
        refine (ddPow D n : Submodule (𝓞 D.host.E) D.host.E).neg_mem (Submodule.sum_mem _ fun i hi => ?_)
        have hia : i ≠ a := Finset.ne_of_mem_erase hi
        by_cases hai : a < i
        · by_cases hic : i ≤ c
          · have hlt : c.val - i.val < n := by have : a.val < i.val := hai; omega
            have e : n = (i.val - a.val) + (c.val - i.val) := by have : a.val < i.val := hai; omega
            rw [e]
            exact mem_ddPow_mul (hG a i (le_of_lt hai)) (ih _ hlt i c hic rfl)
          · rw [(hXi i c).1 (lt_of_not_ge hic), mul_zero]; exact FractionalIdeal.zero_mem _
        · rw [(hX a i).1 (lt_of_le_of_ne (not_lt.1 hai) hia), zero_mul]; exact FractionalIdeal.zero_mem _
  intro a c hac
  exact key _ a c hac rfl

/- English proof (translation)
Establish `hd : IsUnit X.det` using `by rw [upU_det hX]; exact isUnit_one`. Establish `hd' : IsUnit X'.det` using `by rw [upU_det hX']; exact isUnit_one`. Establish `hXi` using `upU_inv hX`. Establish `hXi'` using `upU_inv hX'`. Establish `hm : X⁻¹ - X'⁻¹ = X⁻¹ * (X' - X) * X'⁻¹`.

Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd', Matrix.mul_one]`. Establish `e` using `congrFun (congrFun hm a) c`. Rewrite `e` using `[Matrix.sub_apply]`. Rewrite using `[e, Matrix.mul_apply, Finset.sum_eq_single c]`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single a]`.

Rewrite using `[(hXi a a).2 rfl, (hXi' c c).2 rfl, one_mul, mul_one, Matrix.sub_apply]`. Introduce `i _ hia`. Distinguish the cases in `hai : a < i`. Rewrite using `[Matrix.sub_apply]`. Distinguish the cases in `hic : i < c`.

Rewrite using `[hag i c hic (by have : a.val < i.val := hai; have : i.val < c.val := hic; omega), sub_self, mul_zero]`. Break down `eq_or_lt_of_le (not_lt.1 hic) with h | h` into its components or cases. Rewrite using `[h, (hX' i i).2 rfl, (hX i i).2 rfl, sub_self, mul_zero]`. Rewrite using `[(hX' i c).1 h, (hX i c).1 h, sub_self, mul_zero]`. Rewrite using `[(hXi a i).1 (lt_of_le_of_ne (not_lt.1 hai) hia), zero_mul]`.

Simplify using the standard rewrite rules. Introduce `j _ hjc`. Distinguish the cases in `hjc' : j < c`. Rewrite using `[Matrix.mul_apply]`. Use `mul_eq_zero_of_left (Finset.sum_eq_zero fun i _ => ?_) _` and prove the remaining obligations.

Distinguish the cases in `hai : a ≤ i`. Rewrite using `[Matrix.sub_apply]`. Distinguish the cases in `hij : i < j`. Rewrite using `[hag i j hij (by have : a.val ≤ i.val := hai; have : j.val < c.val := hjc'; omega), sub_self, mul_zero]`. Break down `eq_or_lt_of_le (not_lt.1 hij) with h | h` into its components or cases.

Rewrite using `[h, (hX' i i).2 rfl, (hX i i).2 rfl, sub_self, mul_zero]`. Rewrite using `[(hX' i j).1 h, (hX i j).1 h, sub_self, mul_zero]`. Rewrite using `[(hXi a i).1 (lt_of_not_ge hai), zero_mul]`. Rewrite using `[(hXi' j c).1 (lt_of_le_of_ne (not_lt.1 hjc') (Ne.symm hjc)), mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem inv_diff {X X' : MatR D} (hX : UpU X) (hX' : UpU X') {a c : Fin (D.R.rS + 1)} (hac : a < c)
    (hag : ∀ i j : Fin (D.R.rS + 1), i < j → j.val - i.val < c.val - a.val → X i j = X' i j) :
    X⁻¹ a c - X'⁻¹ a c = X' a c - X a c := by
  have hd : IsUnit X.det := by rw [upU_det hX]; exact isUnit_one
  have hd' : IsUnit X'.det := by rw [upU_det hX']; exact isUnit_one
  have hXi := upU_inv hX
  have hXi' := upU_inv hX'
  have hm : X⁻¹ - X'⁻¹ = X⁻¹ * (X' - X) * X'⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hd', Matrix.mul_one]
  have e := congrFun (congrFun hm a) c
  rw [Matrix.sub_apply] at e
  rw [e, Matrix.mul_apply, Finset.sum_eq_single c]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [(hXi a a).2 rfl, (hXi' c c).2 rfl, one_mul, mul_one, Matrix.sub_apply]
    · intro i _ hia
      by_cases hai : a < i
      · rw [Matrix.sub_apply]
        by_cases hic : i < c
        · rw [hag i c hic (by have : a.val < i.val := hai; have : i.val < c.val := hic; omega), sub_self, mul_zero]
        · rcases eq_or_lt_of_le (not_lt.1 hic) with h | h
          · rw [h, (hX' i i).2 rfl, (hX i i).2 rfl, sub_self, mul_zero]
          · rw [(hX' i c).1 h, (hX i c).1 h, sub_self, mul_zero]
      · rw [(hXi a i).1 (lt_of_le_of_ne (not_lt.1 hai) hia), zero_mul]
    · simp
  · intro j _ hjc
    by_cases hjc' : j < c
    · rw [Matrix.mul_apply]
      refine mul_eq_zero_of_left (Finset.sum_eq_zero fun i _ => ?_) _
      by_cases hai : a ≤ i
      · rw [Matrix.sub_apply]
        by_cases hij : i < j
        · rw [hag i j hij (by have : a.val ≤ i.val := hai; have : j.val < c.val := hjc'; omega), sub_self, mul_zero]
        · rcases eq_or_lt_of_le (not_lt.1 hij) with h | h
          · rw [h, (hX' i i).2 rfl, (hX i i).2 rfl, sub_self, mul_zero]
          · rw [(hX' i j).1 h, (hX i j).1 h, sub_self, mul_zero]
      · rw [(hXi a i).1 (lt_of_not_ge hai), zero_mul]
    · rw [(hXi' j c).1 (lt_of_le_of_ne (not_lt.1 hjc') (Ne.symm hjc)), mul_zero]
  · simp

variable (w : Point D.host.E (D.R.rS + 1))

/- English proof (translation)
Introduce `a c`. Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Simplify using `only [Xmat, ne_of_gt h, if_false]`. Rewrite using `[dif_neg (fun h' => absurd h'.1 (not_lt.2 (le_of_lt h)))]`. Simplify using `[Xmat, h]`.
-/
theorem Xmat_upU (y : FreeE w → D.host.E) : UpU (Xmat w y) := by
  intro a c
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [Xmat, ne_of_gt h, if_false]
    rw [dif_neg (fun h' => absurd h'.1 (not_lt.2 (le_of_lt h)))]
  · simp [Xmat, h]

/- English proof (translation)
Introduce `a c hne`. Establish `hac : a ≠ c` using `fun e => hne (by rw [e])`. Simplify using `only [Xmat, hac, if_false]`. Rewrite using `[dif_neg (fun h' => hne h'.2)]`.
-/
theorem Xmat_blk (y : FreeE w → D.host.E) : IsBlockDiagonalMatrix w (Xmat w y) := by
  intro a c hne
  have hac : a ≠ c := fun e => hne (by rw [e])
  simp only [Xmat, hac, if_false]
  rw [dif_neg (fun h' => hne h'.2)]

/- English proof (translation)
Establish `hne : q.1.1 ≠ q.1.2` using `ne_of_lt q.2.1`. Simplify using `only [Xmat, hne, if_false]`. Rewrite using `[dif_pos q.2]`. Both sides reduce to the same expression.
-/
theorem Xmat_q (y : FreeE w → D.host.E) (q : FreeE w) : Xmat w y q.1.1 q.1.2 = y q := by
  have hne : q.1.1 ≠ q.1.2 := ne_of_lt q.2.1
  simp only [Xmat, hne, if_false]
  rw [dif_pos q.2]
  rfl

/- English proof (translation)
Introduce `a c hac`. Break down `eq_or_lt_of_le hac with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using `only [Xmat, if_true, Nat.sub_self]`. Conclude with `one_mem_ddPow0`.

Distinguish the cases in `hb : blkOf w.1 a.val = blkOf w.1 c.val`. Use `Xmat_q w y ⟨(a, c), h, hb⟩` as an intermediate fact. Simplify using `only at this`. Rewrite using `[this]`. Conclude with `hy ⟨(a, c), h, hb⟩`.

Rewrite using `[Xmat_blk w y a c hb]`. Conclude with `FractionalIdeal.zero_mem _`.
-/
theorem Xmat_grD (y : FreeE w → D.host.E) (hy : ∀ q, y q ∈ ddPow D (hgt w q)) : GrD (Xmat w y) := by
  intro a c hac
  rcases eq_or_lt_of_le hac with h | h
  · subst h; simp only [Xmat, if_true, Nat.sub_self]; exact one_mem_ddPow0
  · by_cases hb : blkOf w.1 a.val = blkOf w.1 c.val
    · have := Xmat_q w y ⟨(a, c), h, hb⟩
      simp only at this; rw [this]; exact hy ⟨(a, c), h, hb⟩
    · rw [Xmat_blk w y a c hb]; exact FractionalIdeal.zero_mem _

end Formalism.L2.SG.Pf.StabIntLat
