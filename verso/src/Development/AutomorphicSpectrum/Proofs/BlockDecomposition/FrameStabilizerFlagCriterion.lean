import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabUpTo
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.CFin.Tri

/- English proof (translation)
Unfold `cnt`. Conclude with `Finset.card_filter_le _ _` after adjusting the coercions.
-/
theorem cnt_le {r : ℕ} (S : Finset (Fin r)) (i : Fin r) : cnt S i ≤ S.card := by
  unfold cnt
  exact_mod_cast Finset.card_filter_le _ _

/- English proof (translation)
Establish `hne : (S.filter (i ≤ ·)).Nonempty`. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff]`. Establish `: S.filter (· < i) = S` using `Finset.filter_true_of_mem fun x hx => not_le.mp (hn hx)`. Simplify using `[cnt, this] at h`.

Use `⟨(S.filter (i ≤ ·)).min' hne, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Finset.mem_filter.mp (Finset.min'_mem _ hne)).1`. Conclude with `(Finset.mem_filter.mp (Finset.min'_mem _ hne)).2`. Introduce `j' hj' hij'`. Conclude with `Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hj', hij'⟩)`.
-/
theorem exists_least {r : ℕ} {S : Finset (Fin r)} {i : Fin r} (h : cnt S i < S.card) :
    ∃ j ∈ S, i ≤ j ∧ ∀ j' ∈ S, i ≤ j' → j ≤ j' := by
  have hne : (S.filter (i ≤ ·)).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hn
    have : S.filter (· < i) = S := Finset.filter_true_of_mem fun x hx => not_le.mp (hn hx)
    simp [cnt, this] at h
  refine ⟨(S.filter (i ≤ ·)).min' hne, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).1
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
  · intro j' hj' hij'
    exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hj', hij'⟩)

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Use `push_neg at hn`. Establish `hsub : S.filter (· < k) ⊆ S.filter (· < i)`. Introduce `t ht`. Take `⟨htS, htk⟩` from `Finset.mem_filter.mp ht`.

Use `Finset.mem_filter.mpr ⟨htS, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hti`. Conclude with `absurd htk (not_lt.mpr (hn t htS (not_lt.mp hti)))`. Use `Finset.card_le_card hsub` as an intermediate fact. Unfold `cnt at h`.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_between {r : ℕ} {S : Finset (Fin r)} {i k : Fin r} (h : cnt S i < cnt S k) :
    ∃ t ∈ S, i ≤ t ∧ t < k := by
  by_contra hn
  push_neg at hn
  have hsub : S.filter (· < k) ⊆ S.filter (· < i) := by
    intro t ht
    obtain ⟨htS, htk⟩ := Finset.mem_filter.mp ht
    refine Finset.mem_filter.mpr ⟨htS, ?_⟩
    by_contra hti
    exact absurd htk (not_lt.mpr (hn t htS (not_lt.mp hti)))
  have := Finset.card_le_card hsub
  unfold cnt at h
  omega

/- English proof (translation)
Introduce `u v huv hv`. Use `letI : Invertible M := ⟨M', mul_eq_one_comm.mp h, h⟩`. Establish `hinv : M⁻¹ = M'` using `Matrix.inv_eq_right_inv h`. Establish `hb : M.BlockTriangular (fun w => if lv w ≤ lv v then (0 : ℤ) else 1)`. Introduce `a b hab`.

Distinguish the cases in `hb' : lv b ≤ lv v`. Distinguish the cases in `ha' : lv a ≤ lv v`. Simplify using `[hb', ha'] at hab`. Conclude with `hM a b (by omega) (by omega)`. Apply the tactic sequence `by_cases ha' : lv a ≤ lv v <;> simp [hb', ha'] at hab`.

Use `Matrix.blockTriangular_inv_of_blockTriangular hb` as an intermediate fact. Rewrite `this` using `[hinv]`. Apply `this` to reduce the goal to its premises. Establish `h1 : ¬ lv u ≤ lv v` using `by omega`. Simplify using `[h1]`.
-/
theorem inv_neg_tri {ι : Type} [Fintype ι] [DecidableEq ι] {L : Type} [Field L] (lv : ι → ℤ)
    {M M' : Matrix ι ι L} (h : M * M' = 1)
    (hM : ∀ u v, lv v < lv u → lv v < 0 → M u v = 0) :
    ∀ u v, lv v < lv u → lv v < 0 → M' u v = 0 := by
  intro u v huv hv
  letI : Invertible M := ⟨M', mul_eq_one_comm.mp h, h⟩
  have hinv : M⁻¹ = M' := Matrix.inv_eq_right_inv h
  have hb : M.BlockTriangular (fun w => if lv w ≤ lv v then (0 : ℤ) else 1) := by
    intro a b hab
    by_cases hb' : lv b ≤ lv v
    · by_cases ha' : lv a ≤ lv v
      · simp [hb', ha'] at hab
      · exact hM a b (by omega) (by omega)
    · by_cases ha' : lv a ≤ lv v <;> simp [hb', ha'] at hab
  have := Matrix.blockTriangular_inv_of_blockTriangular hb
  rw [hinv] at this
  apply this
  have h1 : ¬ lv u ≤ lv v := by omega
  simp [h1]

/- English proof (translation)
Break down `v with i | k | i` into its components or cases. Establish `hi : cnt S i < S.card` using `by simpa [lev] using hv`. Take `⟨j, hjS, hij, hmin⟩` from `exists_least hi`. Take `⟨b, hb, hbz⟩` from `hst j hjS i hij`. Establish `hc : X *ᵥ b = frm X Z Y *ᵥ (Sum.elim b (fun _ => 0))`.

Use extensionality with `a`. Simplify using `[frm, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]`. Establish `hcol : (fun w => (Qi * g * frm X Z Y) w (Sum.inl i)) = Sum.elim b (fun _ => 0)`. Establish `e1 : (fun w => (Qi * g * frm X Z Y) w (Sum.inl i)) = Qi *ᵥ (g *ᵥ (fun a => X a i))`. Use extensionality with `w`.

Rewrite using `[Matrix.mul_assoc]`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, frm]`. Rewrite using `[e1, hb, hc, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]`. Establish `hval : (Qi * g * frm X Z Y) u (Sum.inl i) = Sum.elim b (fun _ => 0) u` using `congrFun hcol u`. Rewrite using `[hval]`.

Break down `u with k | w` into its components or cases. Simplify using `only [Sum.elim_inl]`. Establish `hc' : cnt S i < cnt S k` using `by simpa [lev] using huv`. Take `⟨t, htS, hit, htk⟩` from `exists_between hc'`. Conclude with `hbz k (lt_of_le_of_lt (hmin t htS hit) htk)`.

Simplify using the standard rewrite rules. Simplify using `[lev] at hv`. Use `cnt_le S i` as an intermediate fact. Simplify using `only [lev] at hv`. Use linear arithmetic over natural numbers and integers.
-/
theorem col_zero {L : Type} [Field L] {n r m : ℕ} (X Y : Matrix (Fin n) (Fin r) L)
    (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L)
    (hQ : Qi * frm X Z Y = 1) (S : Finset (Fin r)) (g : Matrix (Fin n) (Fin n) L)
    (hst : ∀ j ∈ S, StabUpTo X g j) (u v : Idx r m)
    (huv : lev m S v < lev m S u) (hv : lev m S v < 0) : (Qi * g * frm X Z Y) u v = 0 := by
  rcases v with i | k | i
  · have hi : cnt S i < S.card := by simpa [lev] using hv
    obtain ⟨j, hjS, hij, hmin⟩ := exists_least hi
    obtain ⟨b, hb, hbz⟩ := hst j hjS i hij
    have hc : X *ᵥ b = frm X Z Y *ᵥ (Sum.elim b (fun _ => 0)) := by
      ext a
      simp [frm, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    have hcol : (fun w => (Qi * g * frm X Z Y) w (Sum.inl i)) = Sum.elim b (fun _ => 0) := by
      have e1 : (fun w => (Qi * g * frm X Z Y) w (Sum.inl i))
          = Qi *ᵥ (g *ᵥ (fun a => X a i)) := by
        ext w
        rw [Matrix.mul_assoc]
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, frm]
      rw [e1, hb, hc, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]
    have hval : (Qi * g * frm X Z Y) u (Sum.inl i) = Sum.elim b (fun _ => 0) u := congrFun hcol u
    rw [hval]
    rcases u with k | w
    · simp only [Sum.elim_inl]
      have hc' : cnt S i < cnt S k := by simpa [lev] using huv
      obtain ⟨t, htS, hit, htk⟩ := exists_between hc'
      exact hbz k (lt_of_le_of_lt (hmin t htS hit) htk)
    · simp
  · simp [lev] at hv
  · have := cnt_le S i
    simp only [lev] at hv
    omega

/- English proof (translation)
Simplify using `[cT, Matrix.transpose_mul, Matrix.map_mul]`.
-/
theorem cT_mul' {L : Type} [Field L] (s : L →+* L) {a b c : Type} [Fintype b]
    (A : Matrix a b L) (B : Matrix b c L) : cT s (A * B) = cT s B * cT s A := by
  simp [cT, Matrix.transpose_mul, Matrix.map_mul]

/- English proof (translation)
Simplify using `[cT]`.
-/
theorem cT_one' {L : Type} [Field L] (s : L →+* L) {a : Type} [DecidableEq a] :
    cT s (1 : Matrix a a L) = 1 := by
  simp [cT]

/- English proof (translation)
Take `⟨gi, h1⟩` from `hg.exists_right_inv`. Establish `hrow0 : cT s X * J * frm X Z Y = Matrix.fromCols (0 : Matrix (Fin r) (Fin r) L) (Matrix.fromCols (0 : Matrix (Fin r) (Fin m) L) (1 : Matrix (Fin r) (Fin r) L))`. Rewrite using `[frm, Matrix.mul_fromCols, Matrix.mul_fromCols, hXX, hXZ, hXY]`. Use `set Q := frm X Z Y with hQdef`. Use `set M := Qi * g * Q with hMdef`.

Use `set M' := Qi * gi * Q with hM'def`. Establish `hMM' : M * M' = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `A1 : ∀ u v, lev m S v < lev m S u → lev m S v < 0 → M u v = 0` using `fun u v huv hv => col_zero X Y Z Qi hQ S g hst u v huv hv`. Establish `A2` using `inv_neg_tri (lev m S) hMM' A1`.

Use `set H := cT s Q * J * Q with hHdef`. Establish `hgJ : cT s gi * J = J * g`. Establish `e : cT s gi * cT s g = 1`. Rewrite using `[← cT_mul', h1, cT_one']`. Combine the equalities or inequalities in the displayed calculation.

Establish `hHM : H * M = cT s M' * H`. Establish `e : cT s Qi * cT s Q = 1` using `by rw [← cT_mul', hQ', cT_one']`. Combine the equalities or inequalities in the displayed calculation. Establish `hrow : ∀ l w, H (Sum.inl l) w = (Matrix.fromCols (0 : Matrix (Fin r) (Fin r) L) (Matrix.fromCols (0 : Matrix (Fin r) (Fin m) L) (1 : Matrix (Fin r) (Fin r) L))) l w`. Introduce `l w`.

Rewrite using `[← hrow0]`. Simplify using `only [hHdef, hQdef, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, frm, Matrix.fromCols_apply_inl]`. Establish `lx : ∀ i, lev m S (Sum.inl i) = cnt S i - S.card` using `fun _ => rfl`. Establish `lz : ∀ k, lev m S (Sum.inr (Sum.inl k)) = 0` using `fun _ => rfl`. Establish `ly : ∀ i, lev m S (Sum.inr (Sum.inr i)) = S.card - cnt S i` using `fun _ => rfl`.

Introduce `u v huv`. Distinguish the cases in `hv : lev m S v < 0`. Conclude with `A1 u v huv hv`. Use `push_neg at hv`. Break down `u with i | k | l` into its components or cases.

Use `cnt_le S i` as an intermediate fact. Rewrite `huv` using `[lx]`. Use linear arithmetic over natural numbers and integers. Rewrite `huv` using `[lz]`. Use linear arithmetic over natural numbers and integers.

Establish `hl0 : lev m S (Sum.inl l) < 0`. Use `cnt_le S l` as an intermediate fact. Rewrite `huv` using `[ly]`. Rewrite using `[lx]`. Use linear arithmetic over natural numbers and integers.

Establish `hlv : lev m S v < - lev m S (Sum.inl l)` using `by rw [ly] at huv; rw [lx]; omega`. Establish `e1 : M (Sum.inr (Sum.inr l)) v = (H * M) (Sum.inl l) v`. Simplify using `[Matrix.mul_apply, Fintype.sum_sum_type, hrow, Matrix.one_apply]`. Rewrite using `[e1, hHM, Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun w _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hw : lev m S (Sum.inl l) < lev m S w`. Establish `: M' w (Sum.inl l) = 0` using `A2 w _ hw hl0`. Simplify using `[cT, this]`. Use `push_neg at hw`. Break down `w with l' | k | l'` into its components or cases.

Break down `v with a | b | c` into its components or cases. Simplify using `[hrow]`. Simplify using `[hrow]`. Distinguish the cases in `hc : l' = c`. Substitute `hc` using the available equality.

Use `cnt_le S l'` as an intermediate fact. Simplify using `only [lx, ly] at hw hlv`. Use linear arithmetic over natural numbers and integers. Simplify using `[hrow, Matrix.one_apply, hc]`. Rewrite `hw` using `[lz]`.

Use linear arithmetic over natural numbers and integers. Use `cnt_le S l'` as an intermediate fact. Rewrite `hw` using `[ly]`. Use linear arithmetic over natural numbers and integers.
-/
theorem block_tri (L : Type) [Field L] (s : L →+* L) (n r m : ℕ)
    (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L)
    (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L)
    (hXX : cT s X * J * X = 0) (hXY : cT s X * J * Y = 1) (hXZ : cT s X * J * Z = 0)
    (hQ : Qi * frm X Z Y = 1) (hQ' : frm X Z Y * Qi = 1) (S : Finset (Fin r))
    (g : Matrix (Fin n) (Fin n) L) (hg : IsUnit g) (hJ : cT s g * J * g = J)
    (hst : ∀ j ∈ S, StabUpTo X g j) :
    (Qi * g * frm X Z Y).BlockTriangular (lev m S) := by
  obtain ⟨gi, h1⟩ := hg.exists_right_inv
  have hrow0 : cT s X * J * frm X Z Y = Matrix.fromCols (0 : Matrix (Fin r) (Fin r) L)
        (Matrix.fromCols (0 : Matrix (Fin r) (Fin m) L) (1 : Matrix (Fin r) (Fin r) L)) := by
    rw [frm, Matrix.mul_fromCols, Matrix.mul_fromCols, hXX, hXZ, hXY]
  set Q := frm X Z Y with hQdef
  set M := Qi * g * Q with hMdef
  set M' := Qi * gi * Q with hM'def
  have hMM' : M * M' = 1 := by
    calc M * M' = Qi * g * (Q * Qi) * gi * Q := by simp only [hMdef, hM'def, Matrix.mul_assoc]
      _ = Qi * (g * gi) * Q := by rw [hQ']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, hQ]
  have A1 : ∀ u v, lev m S v < lev m S u → lev m S v < 0 → M u v = 0 :=
    fun u v huv hv => col_zero X Y Z Qi hQ S g hst u v huv hv
  have A2 := inv_neg_tri (lev m S) hMM' A1
  set H := cT s Q * J * Q with hHdef
  have hgJ : cT s gi * J = J * g := by
    have e : cT s gi * cT s g = 1 := by
      rw [← cT_mul', h1, cT_one']
    calc cT s gi * J = cT s gi * (cT s g * J * g) := by rw [hJ]
      _ = (cT s gi * cT s g) * J * g := by simp only [Matrix.mul_assoc]
      _ = J * g := by rw [e, Matrix.one_mul]
  have hHM : H * M = cT s M' * H := by
    have e : cT s Qi * cT s Q = 1 := by rw [← cT_mul', hQ', cT_one']
    calc H * M = cT s Q * J * (Q * Qi) * g * Q := by simp only [hHdef, hMdef, Matrix.mul_assoc]
      _ = cT s Q * (J * g) * Q := by rw [hQ']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = cT s Q * (cT s gi * J) * Q := by rw [hgJ]
      _ = cT s Q * cT s gi * (cT s Qi * cT s Q) * J * Q := by rw [e]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = cT s M' * H := by simp only [hM'def, hHdef, cT_mul', Matrix.mul_assoc]
  have hrow : ∀ l w, H (Sum.inl l) w = (Matrix.fromCols (0 : Matrix (Fin r) (Fin r) L)
      (Matrix.fromCols (0 : Matrix (Fin r) (Fin m) L) (1 : Matrix (Fin r) (Fin r) L))) l w := by
    intro l w
    rw [← hrow0]
    simp only [hHdef, hQdef, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, frm,
      Matrix.fromCols_apply_inl]
  have lx : ∀ i, lev m S (Sum.inl i) = cnt S i - S.card := fun _ => rfl
  have lz : ∀ k, lev m S (Sum.inr (Sum.inl k)) = 0 := fun _ => rfl
  have ly : ∀ i, lev m S (Sum.inr (Sum.inr i)) = S.card - cnt S i := fun _ => rfl
  intro u v huv
  by_cases hv : lev m S v < 0
  · exact A1 u v huv hv
  push_neg at hv
  rcases u with i | k | l
  · have := cnt_le S i
    rw [lx] at huv
    omega
  · rw [lz] at huv
    omega
  have hl0 : lev m S (Sum.inl l) < 0 := by
    have := cnt_le S l
    rw [ly] at huv; rw [lx]; omega
  have hlv : lev m S v < - lev m S (Sum.inl l) := by rw [ly] at huv; rw [lx]; omega
  have e1 : M (Sum.inr (Sum.inr l)) v = (H * M) (Sum.inl l) v := by
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hrow, Matrix.one_apply]
  rw [e1, hHM, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun w _ => ?_
  by_cases hw : lev m S (Sum.inl l) < lev m S w
  · have : M' w (Sum.inl l) = 0 := A2 w _ hw hl0
    simp [cT, this]
  push_neg at hw
  rcases w with l' | k | l'
  · rcases v with a | b | c
    · simp [hrow]
    · simp [hrow]
    · by_cases hc : l' = c
      · subst hc
        have := cnt_le S l'
        simp only [lx, ly] at hw hlv
        omega
      · simp [hrow, Matrix.one_apply, hc]
  · rw [lz] at hw
    omega
  · have := cnt_le S l'
    rw [ly] at hw
    omega

/- English proof (translation)
Introduce `L _ s _ n r m J X Y Z Qi _ hXX _ hXY hXZ _ hQ hQ' S g hg hJ hst`. Conclude with `block_tri L s n r m J X Y Z Qi hXX hXY hXZ hQ hQ' S g hg hJ hst`.
-/
theorem witt_blockTriangular : ∀ (L : Type) [Field L] (s : L →+* L), (∀ x, s (s x) = x) → ∀ (n r m : ℕ) (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L) (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L), cT s J = J → cT s X * J * X = 0 → cT s Y * J * Y = 0 → cT s X * J * Y = 1 → cT s X * J * Z = 0 → cT s Y * J * Z = 0 → Qi * frm X Z Y = 1 → frm X Z Y * Qi = 1 → ∀ (S : Finset (Fin r)) (g : Matrix (Fin n) (Fin n) L), IsUnit g → cT s g * J * g = J → (∀ j ∈ S, StabUpTo X g j) → (Qi * g * frm X Z Y).BlockTriangular (lev m S) := by
  intro L _ s _ n r m J X Y Z Qi _ hXX _ hXY hXZ _ hQ hQ' S g hg hJ hst
  exact block_tri L s n r m J X Y Z Qi hXX hXY hXZ hQ hQ' S g hg hJ hst

end GlobalTheory.CompanionTheory.CFin.Tri
