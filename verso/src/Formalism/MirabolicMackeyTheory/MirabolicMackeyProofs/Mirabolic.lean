import Mathlib
import Formalism.MirabolicMackeyTheory.StatementL

open Matrix

namespace Formalism.EigenvalueLevelCeiling

variable {k : Type} [Field k] {n : ℕ}

/- English proof (translation)
Establish `hdet : M.det = 1`. Rewrite using `[Matrix.det_of_upperTriangular (by intro i j hij; exact hM.2 i j hij)]`. Simplify using `[hM.1]`. Conclude with `⟨Matrix.nonsingInvUnit M (by rw [hdet]; exact isUnit_one), rfl⟩`.
-/
theorem exists_gl_of_isUniU (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hM : IsUniU M) :
    ∃ g : GL (Fin (n + 1)) k, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = M := by
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_upperTriangular (by intro i j hij; exact hM.2 i j hij)]
    simp [hM.1]
  exact ⟨Matrix.nonsingInvUnit M (by rw [hdet]; exact isUnit_one), rfl⟩

def pairU (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  1 + t • vecMulVec (fun a => h a l.castSucc) (Pi.single s.succ 1)

def pairV (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  1 + t • vecMulVec (Pi.single l.castSucc 1) (fun b => h s.succ b)

/- English proof (translation)
Simplify using `[pairU, Matrix.vecMulVec_apply, Pi.single_apply]`.
-/
theorem pairU_apply (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) (a b) :
    pairU h s l t a b = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b +
      t * (h a l.castSucc * if b = s.succ then 1 else 0) := by
  simp [pairU, Matrix.vecMulVec_apply, Pi.single_apply]

/- English proof (translation)
Simplify using `[pairV, Matrix.vecMulVec_apply, Pi.single_apply]`.
-/
theorem pairV_apply (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) (a b) :
    pairV h s l t a b = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b +
      t * ((if a = l.castSucc then 1 else 0) * h s.succ b) := by
  simp [pairV, Matrix.vecMulVec_apply, Pi.single_apply]

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.mul_apply, Matrix.mul_apply]`. Simplify using `only [pairU_apply, pairV_apply, add_mul, mul_add, Finset.sum_add_distrib]`. Establish `e1 : ∑ c, (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a c * h c b = h a b`. Simplify using `[Matrix.one_apply]`.

Establish `e2 : ∑ c, h a c * (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) c b = h a b`. Simplify using `[Matrix.one_apply]`. Rewrite using `[e1, e2]`. Simplify using `[mul_ite, ite_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pair_comm (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) :
    pairU h s l t * h = h * pairV h s l t := by
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [pairU_apply, pairV_apply, add_mul, mul_add, Finset.sum_add_distrib]
  have e1 : ∑ c, (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a c * h c b = h a b := by
    simp [Matrix.one_apply]
  have e2 : ∑ c, h a c * (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) c b = h a b := by
    simp [Matrix.one_apply]
  rw [e1, e2]
  simp [mul_ite, ite_mul]
  ring

/- English proof (translation)
Establish `hls : l.castSucc < s.succ` using `lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.2 hl) ((Fin.castSucc_lt_succ : s.castSucc < s.succ))`. Establish `hsl : h s.succ l.castSucc = 0` using `hg s.succ ((Fin.castSucc_lt_succ : s.castSucc < s.succ)) l.castSucc hls`. Use `⟨fun i => ?_, fun i j hji => ?_⟩` and prove the remaining obligations. Rewrite using `[pairU_apply, Matrix.one_apply_eq]`. Distinguish the cases in `hi : i = s.succ`.

Substitute `hi` using the available equality. Rewrite using `[hsl]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hi]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[pairU_apply, Matrix.one_apply_ne hji.ne']`. Distinguish the cases in `hj : j = s.succ`. Substitute `hj` using the available equality. Rewrite using `[hg i (lt_trans ((Fin.castSucc_lt_succ : s.castSucc < s.succ)) hji) l.castSucc (lt_trans hls hji)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_neg hj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pairU_isUniU (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (hl : l ≤ s)
    (hg : ∀ j, s.castSucc < j → ∀ b, b < j → h j b = 0) (t : k) : IsUniU (pairU h s l t) := by
  have hls : l.castSucc < s.succ :=
    lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.2 hl) ((Fin.castSucc_lt_succ : s.castSucc < s.succ))
  have hsl : h s.succ l.castSucc = 0 := hg s.succ ((Fin.castSucc_lt_succ : s.castSucc < s.succ)) l.castSucc hls
  refine ⟨fun i => ?_, fun i j hji => ?_⟩
  · rw [pairU_apply, Matrix.one_apply_eq]
    by_cases hi : i = s.succ
    · subst hi
      rw [hsl]
      ring
    · rw [if_neg hi]
      ring
  · rw [pairU_apply, Matrix.one_apply_ne hji.ne']
    by_cases hj : j = s.succ
    · subst hj
      rw [hg i (lt_trans ((Fin.castSucc_lt_succ : s.castSucc < s.succ)) hji) l.castSucc (lt_trans hls hji)]
      ring
    · rw [if_neg hj]
      ring

/- English proof (translation)
Establish `hls : l.castSucc < s.succ` using `lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.2 hl) ((Fin.castSucc_lt_succ : s.castSucc < s.succ))`. Establish `hsl : h s.succ l.castSucc = 0` using `hg s.succ ((Fin.castSucc_lt_succ : s.castSucc < s.succ)) l.castSucc hls`. Use `⟨fun i => ?_, fun i j hji => ?_⟩` and prove the remaining obligations. Rewrite using `[pairV_apply, Matrix.one_apply_eq]`. Distinguish the cases in `hi : i = l.castSucc`.

Substitute `hi` using the available equality. Rewrite using `[hsl]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hi]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[pairV_apply, Matrix.one_apply_ne hji.ne']`. Distinguish the cases in `hi : i = l.castSucc`. Substitute `hi` using the available equality. Rewrite using `[hg s.succ ((Fin.castSucc_lt_succ : s.castSucc < s.succ)) j (lt_trans hji hls)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_neg hi]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pairV_isUniU (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (hl : l ≤ s)
    (hg : ∀ j, s.castSucc < j → ∀ b, b < j → h j b = 0) (t : k) : IsUniU (pairV h s l t) := by
  have hls : l.castSucc < s.succ :=
    lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.2 hl) ((Fin.castSucc_lt_succ : s.castSucc < s.succ))
  have hsl : h s.succ l.castSucc = 0 := hg s.succ ((Fin.castSucc_lt_succ : s.castSucc < s.succ)) l.castSucc hls
  refine ⟨fun i => ?_, fun i j hji => ?_⟩
  · rw [pairV_apply, Matrix.one_apply_eq]
    by_cases hi : i = l.castSucc
    · subst hi
      rw [hsl]
      ring
    · rw [if_neg hi]
      ring
  · rw [pairV_apply, Matrix.one_apply_ne hji.ne']
    by_cases hi : i = l.castSucc
    · subst hi
      rw [hg s.succ ((Fin.castSucc_lt_succ : s.castSucc < s.succ)) j (lt_trans hji hls)]
      ring
    · rw [if_neg hi]
      ring

/- English proof (translation)
The claim follows from `Matrix.one_apply_ne ((Fin.castSucc_lt_succ : a.castSucc < a.succ)).ne`.
-/
theorem one_castSucc_succ (a : Fin n) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a.castSucc a.succ = 0 :=
  Matrix.one_apply_ne ((Fin.castSucc_lt_succ : a.castSucc < a.succ)).ne

/- English proof (translation)
Simplify using `[supd, pairU_apply, one_castSucc_succ, Fin.succ_inj]`.
-/
theorem supd_pairU (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) :
    supd (pairU h s l t) = t * h s.castSucc l.castSucc := by
  simp [supd, pairU_apply, one_castSucc_succ, Fin.succ_inj]

/- English proof (translation)
Simplify using `[supd, pairV_apply, one_castSucc_succ, Fin.castSucc_inj]`.
-/
theorem supd_pairV (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) :
    supd (pairV h s l t) = t * h s.succ l.succ := by
  simp [supd, pairV_apply, one_castSucc_succ, Fin.castSucc_inj]

/- English proof (translation)
Establish `hlast : h (Fin.last n) (Fin.last n) = 1 ∧ ∀ b, b < Fin.last n → h (Fin.last n) b = 0` using `⟨by rw [hm]; simp, fun b hb => by rw [hm, if_neg hb.ne]⟩`. Establish `hex : ∃ j, ¬ (h j j = 1 ∧ ∀ b, b < j → h j b = 0)`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Conclude with `hu ⟨fun i => (hno i).1, fun i j hji => (hno i).2 j hji⟩`.

Take `⟨j1, hj1⟩` from `hex`. Set `S` to `Finset.univ.filter fun j => ¬ (h j j = 1 ∧ ∀ b, b < j → h j b = 0)`. Establish `hSne : S.Nonempty` using `⟨j1, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj1⟩⟩`. Use `set j0 := S.max' hSne with hj0def`. Establish `hj0 : ¬ (h j0 j0 = 1 ∧ ∀ b, b < j0 → h j0 b = 0)` using `(Finset.mem_filter.1 (S.max'_mem hSne)).2`.

Establish `hgood : ∀ j, j0 < j → h j j = 1 ∧ ∀ b, b < j → h j b = 0`. Introduce `j hj`. Assume the negation of the conclusion as `hb`. Conclude with `absurd (S.le_max' j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩)) (not_le.2 hj)`. Establish `hne : j0 ≠ Fin.last n` using `fun he => hj0 (he ▸ hlast)`.

Use `set s := j0.castPred hne with hsdef`. Establish `hs : s.castSucc = j0` using `Fin.castSucc_castPred j0 hne`. Establish `hgood' : ∀ j, s.castSucc < j → h j j = 1 ∧ ∀ b, b < j → h j b = 0`. Rewrite using `[hs]`. Conclude with `hgood`.

Distinguish the cases in `hd : h j0 j0 = 1`. Establish `hb : ∃ b, b < j0 ∧ h j0 b ≠ 0`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Conclude with `hj0 ⟨hd, hno⟩`.

Take `⟨b, hb0, hbne⟩` from `hb`. Establish `hbl : b ≠ Fin.last n` using `(lt_of_lt_of_le hb0 (Fin.le_last _)).ne`. Use `⟨s, b.castPred hbl, ?_, hgood', ?_⟩` and prove the remaining obligations. Rewrite using `[← Fin.castSucc_le_castSucc_iff, Fin.castSucc_castPred, hs]`. Conclude with `hb0.le`.

Establish `hlt : b.castPred hbl ≠ s`. Introduce `he`. Use `congrArg Fin.castSucc he` as an intermediate fact. Rewrite `this` using `[Fin.castSucc_castPred, hs]`. Conclude with `hb0.ne this`.

Rewrite using `[if_neg hlt]`. Simplify `hbne` using `[Fin.castSucc_castPred, hs]`. Use `⟨s, s, le_rfl, hgood', ?_⟩` and prove the remaining obligations. Rewrite using `[if_pos rfl]`. Simplify `hd` using `[hs]`.
-/
theorem exists_bad (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hm : IsMirab h) (hu : ¬ IsUniU h) :
    ∃ s l : Fin n, l ≤ s ∧ (∀ j, s.castSucc < j → h j j = 1 ∧ ∀ b, b < j → h j b = 0) ∧
      h s.castSucc l.castSucc ≠ if l = s then 1 else 0 := by
  classical
  have hlast : h (Fin.last n) (Fin.last n) = 1 ∧ ∀ b, b < Fin.last n → h (Fin.last n) b = 0 :=
    ⟨by rw [hm]; simp, fun b hb => by rw [hm, if_neg hb.ne]⟩
  have hex : ∃ j, ¬ (h j j = 1 ∧ ∀ b, b < j → h j b = 0) := by
    by_contra hno
    push_neg at hno
    exact hu ⟨fun i => (hno i).1, fun i j hji => (hno i).2 j hji⟩
  obtain ⟨j1, hj1⟩ := hex
  let S := Finset.univ.filter fun j => ¬ (h j j = 1 ∧ ∀ b, b < j → h j b = 0)
  have hSne : S.Nonempty := ⟨j1, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj1⟩⟩
  set j0 := S.max' hSne with hj0def
  have hj0 : ¬ (h j0 j0 = 1 ∧ ∀ b, b < j0 → h j0 b = 0) := (Finset.mem_filter.1 (S.max'_mem hSne)).2
  have hgood : ∀ j, j0 < j → h j j = 1 ∧ ∀ b, b < j → h j b = 0 := by
    intro j hj
    by_contra hb
    exact absurd (S.le_max' j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩)) (not_le.2 hj)
  have hne : j0 ≠ Fin.last n := fun he => hj0 (he ▸ hlast)
  set s := j0.castPred hne with hsdef
  have hs : s.castSucc = j0 := Fin.castSucc_castPred j0 hne
  have hgood' : ∀ j, s.castSucc < j → h j j = 1 ∧ ∀ b, b < j → h j b = 0 := by
    rw [hs]
    exact hgood
  by_cases hd : h j0 j0 = 1
  · have hb : ∃ b, b < j0 ∧ h j0 b ≠ 0 := by
      by_contra hno
      push_neg at hno
      exact hj0 ⟨hd, hno⟩
    obtain ⟨b, hb0, hbne⟩ := hb
    have hbl : b ≠ Fin.last n := (lt_of_lt_of_le hb0 (Fin.le_last _)).ne
    refine ⟨s, b.castPred hbl, ?_, hgood', ?_⟩
    · rw [← Fin.castSucc_le_castSucc_iff, Fin.castSucc_castPred, hs]
      exact hb0.le
    · have hlt : b.castPred hbl ≠ s := by
        intro he
        have := congrArg Fin.castSucc he
        rw [Fin.castSucc_castPred, hs] at this
        exact hb0.ne this
      rw [if_neg hlt]
      simpa [Fin.castSucc_castPred, hs] using hbne
  · refine ⟨s, s, le_rfl, hgood', ?_⟩
    rw [if_pos rfl]
    simpa [hs] using hd

/- English proof (translation)
Introduce `k A _ _ _ n ψ hψ h hm hu`. Take `⟨s, l, hl, hgood, hbad⟩` from `exists_bad (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) hm hu`. Establish `hg : ∀ j, s.castSucc < j → ∀ b, b < j → (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) j b = 0` using `fun j hj b hb => (hgood j hj).2 b hb`. Establish `hrow : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s.succ l.succ = if l = s then 1 else 0`. Distinguish the cases in `hls : l = s`.

Substitute `hls` using the available equality. Rewrite using `[if_pos rfl]`. Conclude with `(hgood _ (Fin.castSucc_lt_succ : l.castSucc < l.succ)).1`. Rewrite using `[if_neg hls]`. Conclude with `(hgood _ (Fin.castSucc_lt_succ : s.castSucc < s.succ)).2 _ (Fin.succ_lt_succ_iff.2 (lt_of_le_of_ne hl hls))`.

Take `⟨c, hc⟩ : ∃ c : k, c = (if l = s then 1 else 0) - (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s.castSucc l.castSucc` from `⟨_, rfl⟩`. Establish `hc0 : c ≠ 0`. Rewrite using `[hc]`. Conclude with `sub_ne_zero.2 (Ne.symm hbad)`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, ψ x ≠ 1 := by`.

Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Conclude with `hψ (AddChar.ext ψ 1 fun y => by rw [hno y, AddChar.one_apply])`. Take `⟨t, ht⟩ : ∃ t : k, t = x / c` from `⟨_, rfl⟩`. Establish `htc : t * c = x` using `by rw [ht]; field_simp`.

Take `⟨g, hgM⟩` from `exists_gl_of_isUniU _ (pairU_isUniU (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s l hl hg t)`. Establish `hconj : ((h⁻¹ * g * h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = pairV (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s l t`. Rewrite using `[Units.val_mul, Units.val_mul, hgM, mul_assoc, pair_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]`. Use `⟨g, by rw [hgM]; exact pairU_isUniU _ s l hl hg t, by rw [hconj]; exact pairV_isUniU _ s l hl hg t, ?_⟩` and prove the remaining obligations. Rewrite using `[hconj, hgM, supd_pairV, supd_pairU, hrow]`.

Introduce `heq`. Apply `hx` to reduce the goal to its premises. Establish `e : t * (if l = s then (1 : k) else 0) = t * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s.castSucc l.castSucc + x`. Take the linear combination `htc - t * hc`. Rewrite `heq` using `[e, AddChar.map_add_eq_mul]`.

Take `⟨v, hv⟩ : IsUnit (ψ (t * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s.castSucc l.castSucc))` from `IsUnit.of_mul_eq_one (ψ (-(t * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s.castSucc l.castSucc))) (by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one])`. Rewrite `heq` using `[← hv]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mirabolic_mackey_pair : MirabolicMackey := by
  intro k A _ _ _ n ψ hψ h hm hu
  obtain ⟨s, l, hl, hgood, hbad⟩ := exists_bad (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) hm hu
  have hg : ∀ j, s.castSucc < j → ∀ b, b < j → (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) j b = 0 :=
    fun j hj b hb => (hgood j hj).2 b hb
  have hrow : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s.succ l.succ = if l = s then 1 else 0 := by
    by_cases hls : l = s
    · subst hls
      rw [if_pos rfl]
      exact (hgood _ (Fin.castSucc_lt_succ : l.castSucc < l.succ)).1
    · rw [if_neg hls]
      exact (hgood _ (Fin.castSucc_lt_succ : s.castSucc < s.succ)).2 _
        (Fin.succ_lt_succ_iff.2 (lt_of_le_of_ne hl hls))
  obtain ⟨c, hc⟩ : ∃ c : k,
      c = (if l = s then 1 else 0) - (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s.castSucc l.castSucc :=
    ⟨_, rfl⟩
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact sub_ne_zero.2 (Ne.symm hbad)
  obtain ⟨x, hx⟩ : ∃ x, ψ x ≠ 1 := by
    by_contra hno
    push_neg at hno
    exact hψ (AddChar.ext ψ 1 fun y => by rw [hno y, AddChar.one_apply])
  obtain ⟨t, ht⟩ : ∃ t : k, t = x / c := ⟨_, rfl⟩
  have htc : t * c = x := by rw [ht]; field_simp
  obtain ⟨g, hgM⟩ := exists_gl_of_isUniU _ (pairU_isUniU (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s l hl hg t)
  have hconj : ((h⁻¹ * g * h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      pairV (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s l t := by
    rw [Units.val_mul, Units.val_mul, hgM, mul_assoc, pair_comm, ← mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, one_mul]
  refine ⟨g, by rw [hgM]; exact pairU_isUniU _ s l hl hg t, by rw [hconj]; exact pairV_isUniU _ s l hl hg t, ?_⟩
  rw [hconj, hgM, supd_pairV, supd_pairU, hrow]
  intro heq
  apply hx
  have e : t * (if l = s then (1 : k) else 0) =
      t * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s.castSucc l.castSucc + x := by
    linear_combination htc - t * hc
  rw [e, AddChar.map_add_eq_mul] at heq
  obtain ⟨v, hv⟩ : IsUnit (ψ (t * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s.castSucc l.castSucc)) :=
    IsUnit.of_mul_eq_one (ψ (-(t * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s.castSucc l.castSucc)))
      (by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one])
  rw [← hv] at heq
  calc ψ x = ↑v⁻¹ * (↑v * ψ x) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = ↑v⁻¹ * ↑v := by rw [heq]
    _ = 1 := Units.inv_mul v

/- English proof (translation)
Simplify using `[supd, one_castSucc_succ]`.
-/
theorem supd_one : supd (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = 0 := by
  simp [supd, one_castSucc_succ]

/- English proof (translation)
Unfold `supd`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Fintype.sum_eq_add i.castSucc i.succ ((Fin.castSucc_lt_succ : i.castSucc < i.succ)).ne]`. Rewrite using `[hu.1, hu'.1]`.

Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `c ⟨hc1, hc2⟩`. Break down `lt_or_gt_of_ne hc1 with h1 | h1` into its components or cases. Rewrite using `[hu.2 _ _ h1, zero_mul]`. Establish `h2 : (c : ℕ) ≠ (i : ℕ) + 1` using `fun h3 => hc2 (Fin.ext (by simp [h3]))`.

Establish `h4 : i.succ < c`. Rewrite `h1`, the goal using `[Fin.lt_iff_val_lt_val]`. Simplify using `only [Fin.coe_castSucc, Fin.val_succ] at h1 ⊢`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hu'.2 _ _ h4, mul_zero]`.
-/
theorem supd_mul (u u' : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hu : IsUniU u) (hu' : IsUniU u') :
    supd (u * u') = supd u + supd u' := by
  unfold supd
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply, Fintype.sum_eq_add i.castSucc i.succ ((Fin.castSucc_lt_succ : i.castSucc < i.succ)).ne]
  · rw [hu.1, hu'.1]
    ring
  · rintro c ⟨hc1, hc2⟩
    rcases lt_or_gt_of_ne hc1 with h1 | h1
    · rw [hu.2 _ _ h1, zero_mul]
    · have h2 : (c : ℕ) ≠ (i : ℕ) + 1 := fun h3 => hc2 (Fin.ext (by simp [h3]))
      have h4 : i.succ < c := by
        rw [Fin.lt_iff_val_lt_val] at h1 ⊢
        simp only [Fin.coe_castSucc, Fin.val_succ] at h1 ⊢
        omega
      rw [hu'.2 _ _ h4, mul_zero]

/- English proof (translation)
Introduce `j`. Distinguish the cases in `hj : j = Fin.last n`. Substitute `hj` using the available equality. Rewrite using `[if_pos rfl]`. Conclude with `hu.1 _`.

Rewrite using `[if_neg hj]`. Conclude with `hu.2 _ _ (Fin.lt_last_iff_ne_last.2 hj)`.
-/
theorem isMirab_of_isUniU (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hu : IsUniU u) : IsMirab u := by
  intro j
  by_cases hj : j = Fin.last n
  · subst hj
    rw [if_pos rfl]
    exact hu.1 _
  · rw [if_neg hj]
    exact hu.2 _ _ (Fin.lt_last_iff_ne_last.2 hj)

/- English proof (translation)
Introduce `k A _ _ _ n ψ hψ P U hP hU`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `show ψ (supd ((1 : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) = 1`. Rewrite using `[Units.val_one, supd_one, AddChar.map_zero_eq_one]`. Introduce `u hu u' hu' show ψ (supd (((u * u' : P) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) = ψ (supd ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) * ψ (supd ((u' : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k))`.

Rewrite using `[Subgroup.coe_mul, Units.val_mul, supd_mul _ _ ((hU u).1 hu) ((hU u').1 hu'), AddChar.map_add_eq_mul]`. Introduce `h hh`. Establish `hm : IsMirab ((h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)` using `(hP h).1 h.2`. Establish `hnu : ¬ IsUniU ((h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)` using `fun hu => hh ((hU h).2 hu)`. Take `⟨u, hu1, hu2, hne⟩` from `mirabolic_mackey_pair k A n ψ hψ (h : GL (Fin (n + 1)) k) hm hnu`.

Establish `huP : u ∈ P` using `(hP u).2 (isMirab_of_isUniU _ hu1)`. Use `⟨⟨u, huP⟩, (hU _).2 hu1, (hU _).2 ?_, ?_⟩` and prove the remaining obligations. Simplify using `using hu2`. Simplify using `using hne`.
-/
theorem mirabolic_is_mackey : MirabolicIsMackey := by
  intro k A _ _ _ n ψ hψ P U hP hU
  refine ⟨?_, ?_, ?_⟩
  · show ψ (supd ((1 : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) = 1
    rw [Units.val_one, supd_one, AddChar.map_zero_eq_one]
  · intro u hu u' hu'
    show ψ (supd (((u * u' : P) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) =
      ψ (supd ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) *
        ψ (supd ((u' : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
    rw [Subgroup.coe_mul, Units.val_mul, supd_mul _ _ ((hU u).1 hu) ((hU u').1 hu'),
      AddChar.map_add_eq_mul]
  · intro h hh
    have hm : IsMirab ((h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := (hP h).1 h.2
    have hnu : ¬ IsUniU ((h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
      fun hu => hh ((hU h).2 hu)
    obtain ⟨u, hu1, hu2, hne⟩ := mirabolic_mackey_pair k A n ψ hψ (h : GL (Fin (n + 1)) k) hm hnu
    have huP : u ∈ P := (hP u).2 (isMirab_of_isUniU _ hu1)
    refine ⟨⟨u, huP⟩, (hU _).2 hu1, (hU _).2 ?_, ?_⟩
    · simpa using hu2
    · simpa using hne

end Formalism.EigenvalueLevelCeiling
