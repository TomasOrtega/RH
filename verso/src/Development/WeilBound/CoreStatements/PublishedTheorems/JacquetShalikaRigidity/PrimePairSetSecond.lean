import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace primeSetTwoBounds

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

/- English proof (translation)
Rewrite using `[blkU, posU_val, Matrix.add_apply, posM, Matrix.sum_apply]`. Simplify using `only [Matrix.single_apply]`.
-/
theorem blkU_val_apply {R : Type} [CommRing R] {r m : ℕ} (x : UnipotentBlockColumnIndex k r m → R) (i c : Fin k) :
    (blkU x : GL (Fin k) R).val i c = (1 : Matrix (Fin k) (Fin k) R) i c +
      ∑ t : UnipotentBlockColumnIndex k r m, if t.1.1 = i ∧ t.1.2 = c then x t else 0 := by
  rw [blkU, posU_val, Matrix.add_apply, posM, Matrix.sum_apply]
  simp only [Matrix.single_apply]

/- English proof (translation)
Rewrite using `[blkU_val_apply, Finset.sum_eq_zero, add_zero]`. Introduce `t _`. Rewrite using `[if_neg]`. Introduce and unpack `⟨e1, e2⟩`. Use `t.2` as an intermediate fact.

Substitute `e1 e2` using the available equality. Use linear arithmetic over natural numbers and integers.
-/
theorem blkU_val_of_not_lt {R : Type} [CommRing R] {r m : ℕ} (x : UnipotentBlockColumnIndex k r m → R) (i c : Fin k)
    (h : ¬ (i : ℕ) < c) : (blkU x : GL (Fin k) R).val i c = (1 : Matrix (Fin k) (Fin k) R) i c := by
  rw [blkU_val_apply, Finset.sum_eq_zero, add_zero]
  intro t _
  rw [if_neg]
  rintro ⟨e1, e2⟩
  have := t.2
  subst e1 e2
  omega

/- English proof (translation)
Use `⟨fun i c hc => ?_, fun i => ?_, fun i c hc => absurd hc (Nat.not_lt_zero _)⟩` and prove the remaining obligations. Rewrite using `[blkU_val_of_not_lt _ _ _ (by omega), Matrix.one_apply_ne]`. Introduce and unpack `rfl`. Conclude with `lt_irrefl _ hc`. Rewrite using `[blkU_val_of_not_lt _ _ _ (lt_irrefl _), Matrix.one_apply_eq]`.
-/
theorem blkU_unipotent_zero {r m : ℕ} (x : UnipotentBlockColumnIndex k r m → Ad E) : UU 0 (blkU x : GA E k) := by
  refine ⟨fun i c hc => ?_, fun i => ?_, fun i c hc => absurd hc (Nat.not_lt_zero _)⟩
  · rw [blkU_val_of_not_lt _ _ _ (by omega), Matrix.one_apply_ne]
    rintro rfl; exact lt_irrefl _ hc
  · rw [blkU_val_of_not_lt _ _ _ (lt_irrefl _), Matrix.one_apply_eq]

/- English proof (translation)
Break down `lt_trichotomy (l : ℕ) i with h | h | h` into its components or cases. Rewrite using `[hu.1 i l h, Matrix.one_apply_ne]`. Introduce and unpack `rfl`. Conclude with `lt_irrefl _ h`. Establish `: l = i` using `Fin.ext h`.

Substitute `this` using the available equality. Rewrite using `[hu.2.1, Matrix.one_apply_eq]`. Use `l.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem unipotent_last_row_identity {u : GA E k} (hu : UU 0 u) (i l : Fin k) (hi : (i : ℕ) + 1 = k) :
    u.val i l = (1 : Matrix (Fin k) (Fin k) (Ad E)) i l := by
  rcases lt_trichotomy (l : ℕ) i with h | h | h
  · rw [hu.1 i l h, Matrix.one_apply_ne]; rintro rfl; exact lt_irrefl _ h
  · have : l = i := Fin.ext h
    subst this; rw [hu.2.1, Matrix.one_apply_eq]
  · have := l.2; omega

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Simplify using `only [h]`. Rewrite using `[← Matrix.mul_apply, Matrix.one_mul]`.
-/
theorem mul_row {R : Type} [CommRing R] (M N : Matrix (Fin k) (Fin k) R) (i : Fin k)
    (h : ∀ l, M i l = (1 : Matrix (Fin k) (Fin k) R) i l) (c : Fin k) : (M * N) i c = N i c := by
  rw [Matrix.mul_apply]
  simp only [h]
  rw [← Matrix.mul_apply, Matrix.one_mul]

/- English proof (translation)
Use function extensionality and compare the values at `c`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `split_ifs with hi`. Rewrite using `[Units.val_mul, mul_row _ _ i (fun l => unipotent_last_row_identity hu i l hi)]`. Both sides reduce to the same expression.
-/
theorem lastRow_unipotent_mul (u g : GA E k) (hu : UU 0 u) : lastRow (u * g) = lastRow g := by
  funext c
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [Units.val_mul, mul_row _ _ i (fun l => unipotent_last_row_identity hu i l hi)]
  · rfl

/- English proof (translation)
Use function extensionality and compare the values at `c`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `split_ifs with hi`. Rewrite using `[Units.val_mul]`. Use `mul_row _ _ i (fun l => ?_) c` and prove the remaining obligations.

Establish `e` using `hγ i l (Or.inl (by omega))`. Express the relevant statement in the definitionally equal form `algebraMap E (Ad E) (γ.val i l) = _`. Rewrite using `[e, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Both sides reduce to the same expression.
-/
theorem lastRow_mir (γ : GL (Fin k) E) (g : GA E k) (hγ : IsMir (k - 1) γ) :
    lastRow (ratGL E k γ * g) = lastRow g := by
  funext c
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [Units.val_mul]
    refine mul_row _ _ i (fun l => ?_) c
    have e := hγ i l (Or.inl (by omega))
    change algebraMap E (Ad E) (γ.val i l) = _
    rw [e, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · rfl

/- English proof (translation)
Use `continuous_pi fun c => continuous_finsetSum _ fun i _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `(Units.continuous_val (M := Matrix (Fin k) (Fin k) (Ad E))).matrix_elem i c`. Conclude with `continuous_const`.
-/
theorem continuous_lastRow : Continuous (lastRow : GA E k → Fin k → Ad E) := by
  refine continuous_pi fun c => continuous_finsetSum _ fun i _ => ?_
  split_ifs
  · exact (Units.continuous_val (M := Matrix (Fin k) (Fin k) (Ad E))).matrix_elem i c
  · exact continuous_const

variable {ψ : AddChar (Ad E) ℂ}

/- English proof (translation)
Rewrite using `[blkU, posU_val, mul_add, mul_one, Matrix.add_apply, posM, Matrix.mul_sum, Matrix.sum_apply]`. Use `congr 1`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.single_apply]`.

Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single t.1.1]`. Simplify using `[h]`. Introduce `b _ hb`. Simplify using `[Ne.symm hb]`.

Simplify using the standard rewrite rules. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Simplify using `[h]`.
-/
theorem mul_blkU_apply {R : Type} [CommRing R] {j : ℕ} (M : Matrix (Fin k) (Fin k) R) (x : UnipotentBlockColumnIndex k j j → R)
    (i c : Fin k) : (M * (blkU x : GL (Fin k) R).val) i c =
      M i c + ∑ t : UnipotentBlockColumnIndex k j j, if t.1.2 = c then M i t.1.1 * x t else 0 := by
  rw [blkU, posU_val, mul_add, mul_one, Matrix.add_apply, posM, Matrix.mul_sum, Matrix.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.mul_apply]
  simp only [Matrix.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single t.1.1]
    · simp [h]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · refine Finset.sum_eq_zero fun l _ => ?_
    simp [h]

def cut (j : ℕ) (u : GA E k) : GA E k := u * blkU (r := j) (m := j) fun t => -u.val t.1.1 t.1.2

/- English proof (translation)
Rewrite using `[cut, Units.val_mul, mul_blkU_apply]`. Establish `hs : ∀ t : UnipotentBlockColumnIndex k j j, (if t.1.2 = c then u.val i t.1.1 * -u.val t.1.1 t.1.2 else 0) = if t.1.2 = c ∧ t.1.1 = i then -u.val i c else 0`. Introduce `t`. Rewrite using `[hu.2.2 i t.1.1 t.2.1, Matrix.one_apply]`. Apply the tactic sequence `by_cases h1 : t.1.2 = c <;> by_cases h2 : t.1.1 = i`.

Substitute `h1 h2` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h1, h2, Ne.symm h2]`. Simplify using `[h1]`. Simplify using `[h1]`.

Simplify using `only [hs]`. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single (⟨(i, c), h.1, h.2.ge, h.2.le⟩ : UnipotentBlockColumnIndex k j j)]`. Simplify using the standard rewrite rules. Introduce `t _ ht`.

Rewrite using `[if_neg]`. Introduce and unpack `⟨e1, e2⟩`. Conclude with `ht (Subtype.ext (Prod.ext e2 e1))`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_eq_zero, add_zero]`.

Introduce `t _`. Rewrite using `[if_neg]`. Introduce and unpack `⟨e1, e2⟩`. Use `t.2` as an intermediate fact. Substitute `e1 e2` using the available equality.

Conclude with `h ⟨this.1, by omega⟩`.
-/
theorem cut_apply {j : ℕ} {u : GA E k} (hu : UU j u) (i c : Fin k) :
    (cut j u).val i c = if (i : ℕ) < j ∧ (c : ℕ) = j then 0 else u.val i c := by
  rw [cut, Units.val_mul, mul_blkU_apply]
  have hs : ∀ t : UnipotentBlockColumnIndex k j j, (if t.1.2 = c then u.val i t.1.1 * -u.val t.1.1 t.1.2 else 0) =
      if t.1.2 = c ∧ t.1.1 = i then -u.val i c else 0 := by
    intro t
    rw [hu.2.2 i t.1.1 t.2.1, Matrix.one_apply]
    by_cases h1 : t.1.2 = c <;> by_cases h2 : t.1.1 = i
    · subst h1 h2; simp
    · simp [h1, h2, Ne.symm h2]
    · simp [h1]
    · simp [h1]
  simp only [hs]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨(i, c), h.1, h.2.ge, h.2.le⟩ : UnipotentBlockColumnIndex k j j)]
    · simp
    · intro t _ ht
      rw [if_neg]
      rintro ⟨e1, e2⟩
      exact ht (Subtype.ext (Prod.ext e2 e1))
    · simp
  · rw [Finset.sum_eq_zero, add_zero]
    intro t _
    rw [if_neg]
    rintro ⟨e1, e2⟩
    have := t.2
    subst e1 e2
    exact h ⟨this.1, by omega⟩

/- English proof (translation)
Use `⟨fun i c hc => ?_, fun i => ?_, fun i c hc => ?_⟩` and prove the remaining obligations. Rewrite using `[cut_apply hu]`. Use `split_ifs`. Both sides reduce to the same expression. Conclude with `hu.1 i c hc`.

Rewrite using `[cut_apply hu, if_neg (by omega)]; exact hu.2.1 i`. Rewrite using `[cut_apply hu] split_ifs with h`. Rewrite using `[Matrix.one_apply_ne]`. Introduce `e`. Substitute `e` using the available equality.

Use linear arithmetic over natural numbers and integers. Break down `Nat.lt_or_ge (c : ℕ) j with h' | h'` into its components or cases. Conclude with `hu.2.2 i c h'`. Establish `hc' : (c : ℕ) = j` using `by omega`. Break down `lt_trichotomy (i : ℕ) c with h2 | h2 | h2` into its components or cases.

Conclude with `absurd ⟨by omega, hc'⟩ h`. Establish `: i = c` using `Fin.ext h2`. Substitute `this` using the available equality. Rewrite using `[hu.2.1, Matrix.one_apply_eq]`. Rewrite using `[hu.1 i c h2, Matrix.one_apply_ne]`.

Introduce `e`. Substitute `e` using the available equality. Use linear arithmetic over natural numbers and integers.
-/
theorem uu_cut {j : ℕ} {u : GA E k} (hu : UU j u) : UU (j + 1) (cut j u) := by
  refine ⟨fun i c hc => ?_, fun i => ?_, fun i c hc => ?_⟩
  · rw [cut_apply hu]; split_ifs
    · rfl
    · exact hu.1 i c hc
  · rw [cut_apply hu, if_neg (by omega)]; exact hu.2.1 i
  · rw [cut_apply hu]
    split_ifs with h
    · rw [Matrix.one_apply_ne]; intro e; subst e; omega
    · rcases Nat.lt_or_ge (c : ℕ) j with h' | h'
      · exact hu.2.2 i c h'
      · have hc' : (c : ℕ) = j := by omega
        rcases lt_trichotomy (i : ℕ) c with h2 | h2 | h2
        · exact absurd ⟨by omega, hc'⟩ h
        · have : i = c := Fin.ext h2
          subst this; rw [hu.2.1, Matrix.one_apply_eq]
        · rw [hu.1 i c h2, Matrix.one_apply_ne]; intro e; subst e; omega

/- English proof (translation)
Rewrite using `[cut, mul_assoc]`. Express the relevant statement in the definitionally equal form `u = u * (posU _ _ * posU _ _)`. Establish `e : ((fun t : UnipotentBlockColumnIndex k j j => -u.val t.1.1 t.1.2) + fun t => u.val t.1.1 t.1.2) = 0`. Use function extensionality and compare the values at `t`. Simplify using the standard rewrite rules.

Rewrite using `[← posU_add, e, posU_zero, mul_one]`.
-/
theorem cut_mul {j : ℕ} (u : GA E k) : u = cut j u * blkU (r := j) (m := j) fun t => u.val t.1.1 t.1.2 := by
  rw [cut, mul_assoc]
  change u = u * (posU _ _ * posU _ _)
  have e : ((fun t : UnipotentBlockColumnIndex k j j => -u.val t.1.1 t.1.2) + fun t => u.val t.1.1 t.1.2) = 0 := by
    funext t; simp
  rw [← posU_add, e, posU_zero, mul_one]

def sd (n : GA E k) : Ad E := ∑ p : Fin k × Fin k with (p.2 : ℕ) = p.1 + 1, n.val p.1 p.2

/- English proof (translation)
Establish `hA : sd u = sd (cut j u) + ∑ p : Fin k × Fin k with (p.2 : ℕ) = p.1 + 1, if (p.1 : ℕ) < j ∧ (p.2 : ℕ) = j then u.val p.1 p.2 else 0`. Rewrite using `[sd, sd, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[cut_apply hu]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[hA]`. Use `congr 1`. Set `i0 : Fin k` to `⟨j - 1, by omega⟩`. Set `c0 : Fin k` to `⟨j, hjk⟩`. Rewrite using `[Finset.sum_eq_single (i0, c0), dot, Finset.sum_eq_single (⟨(i0, c0), by simp [i0]; omega, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex k j j)]`.

Simplify using `[eLast, i0, c0]`. Rewrite using `[if_pos (by omega), if_pos (by omega)]`. Introduce `t _ ht`. Simplify using `only [eLast]`. Rewrite using `[if_neg, map_zero, zero_mul]`.

Introduce `e`. Apply `ht` to reduce the goal to its premises. Use `t.2` as an intermediate fact. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises.

Apply `Fin.ext` to reduce the goal to its premises. Simplify using `[i0]`. Use linear arithmetic over natural numbers and integers. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `[c0]`.

Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Introduce `p hp hne`. Rewrite using `[if_neg]`. Introduce and unpack `⟨h1, h2⟩`.

Simplify using `only [Finset.mem_filter] at hp`. Apply `hne` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `[i0]`.

Use linear arithmetic over natural numbers and integers. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `[c0]`. Use linear arithmetic over natural numbers and integers. Introduce `h`.

It suffices to derive a contradiction. Apply `h` to reduce the goal to its premises. Simplify using `[i0, c0]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sd_cut {j : ℕ} (hj1 : 1 ≤ j) (hjk : j < k) {u : GA E k} (hu : UU j u) :
    sd u = sd (cut j u) + dot (eLast k j) (fun t : UnipotentBlockColumnIndex k j j => u.val t.1.1 t.1.2) := by
  have hA : sd u = sd (cut j u) + ∑ p : Fin k × Fin k with (p.2 : ℕ) = p.1 + 1,
      if (p.1 : ℕ) < j ∧ (p.2 : ℕ) = j then u.val p.1 p.2 else 0 := by
    rw [sd, sd, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [cut_apply hu]
    split_ifs <;> simp
  rw [hA]
  congr 1
  let i0 : Fin k := ⟨j - 1, by omega⟩
  let c0 : Fin k := ⟨j, hjk⟩
  rw [Finset.sum_eq_single (i0, c0), dot, Finset.sum_eq_single (⟨(i0, c0), by simp [i0]; omega, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex k j j)]
  · simp [eLast, i0, c0]
    rw [if_pos (by omega), if_pos (by omega)]
  · intro t _ ht
    simp only [eLast]
    rw [if_neg, map_zero, zero_mul]
    intro e
    apply ht
    have := t.2
    apply Subtype.ext; apply Prod.ext
    · apply Fin.ext; simp [i0]; omega
    · apply Fin.ext; simp [c0]; omega
  · simp
  · intro p hp hne
    rw [if_neg]
    rintro ⟨h1, h2⟩
    simp only [Finset.mem_filter] at hp
    apply hne
    apply Prod.ext
    · apply Fin.ext; simp [i0]; omega
    · apply Fin.ext; simp [c0]; omega
  · intro h; exfalso; apply h; simp [i0, c0]; omega

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem psN_eq (u : GA E k) : psN ψ u = ψ (sd u) := rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i c`. Conclude with `hu.2.2 i c (by omega)`.
-/
theorem uu_one {j : ℕ} (hj : k ≤ j) {u : GA E k} (hu : UU j u) : u = 1 := by
  apply Units.ext
  ext i c
  exact hu.2.2 i c (by omega)

/- English proof (translation)
Establish `base : ∀ u : GA E k, u = 1 → ∀ g, f (u * g) = psN ψ u * f g`. Introduce and unpack `u rfl g`. Establish `: psN ψ (1 : GA E k) = 1`. Unfold `psN`. Rewrite using `[Finset.sum_eq_zero, AddChar.map_zero_eq_one]`.

Introduce `p hp`. Simplify using `only [Finset.mem_filter] at hp`. Rewrite using `[Units.val_one, Matrix.one_apply_ne]`. Introduce `e`. Rewrite `hp` using `[e]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[this, one_mul, one_mul]`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro j hj _ u hu g; exact base u (uu_one (by omega) hu) g`.

Consider the case `succ n ih`. Introduce `j hj hmj u hu g`. Break down `Nat.lt_or_ge j k with hjk | hjk` into its components or cases. Use `conv_lhs => rw [cut_mul (j := j) u, mul_assoc]`. Rewrite using `[ih (j + 1) (by omega) (by omega) _ (uu_cut hu), hf.law j (by omega), psN_eq, psN_eq, sd_cut (by omega) hjk hu, AddChar.map_add_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `base u (uu_one hjk hu) g`.
-/
theorem pre_law {m : ℕ} {f : GA E k → ℂ} (hf : Pre ψ m f) :
    ∀ n j, k ≤ j + n → m + 1 ≤ j → ∀ u, UU j u → ∀ g, f (u * g) = psN ψ u * f g := by
  have base : ∀ u : GA E k, u = 1 → ∀ g, f (u * g) = psN ψ u * f g := by
    rintro u rfl g
    have : psN ψ (1 : GA E k) = 1 := by
      unfold psN
      rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one]
      intro p hp
      simp only [Finset.mem_filter] at hp
      rw [Units.val_one, Matrix.one_apply_ne]
      intro e; rw [e] at hp; omega
    rw [this, one_mul, one_mul]
  intro n
  induction n with
  | zero => intro j hj _ u hu g; exact base u (uu_one (by omega) hu) g
  | succ n ih =>
    intro j hj hmj u hu g
    rcases Nat.lt_or_ge j k with hjk | hjk
    · conv_lhs => rw [cut_mul (j := j) u, mul_assoc]
      rw [ih (j + 1) (by omega) (by omega) _ (uu_cut hu), hf.law j (by omega), psN_eq, psN_eq,
        sd_cut (by omega) hjk hu, AddChar.map_add_eq_mul]
      ring
    · exact base u (uu_one hjk hu) g

/- English proof (translation)
Use function extensionality and compare the values at `g`. Unfold `colT coefF`. Rewrite using `[← avg_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Simplify using `only`. Rewrite using `[hχ _ (blkU_unipotent_zero x)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem colT_mul {χ f : GA E k → ℂ} (hχ : ∀ u, UU 0 u → ∀ g, χ (u * g) = χ g) (j : ℕ) :
    colT ψ j (fun g => χ g * f g) = fun g => χ g * colT ψ j f g := by
  funext g
  unfold colT coefF
  rw [← avg_const_mul]
  congr 1
  funext x
  dsimp only
  rw [hχ _ (blkU_unipotent_zero x)]
  ring

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro f`. Both sides reduce to the same expression. Consider the case `succ m ih => intro f`. Rewrite using `[whit_succ, whit_succ, colT_mul hχ, ih]`.
-/
theorem whit_mul {χ : GA E k → ℂ} (hχ : ∀ u, UU 0 u → ∀ g, χ (u * g) = χ g) (m : ℕ) :
    ∀ f : GA E k → ℂ, whit ψ m (fun g => χ g * f g) = fun g => χ g * whit ψ m f g := by
  induction m with
  | zero => intro f; rfl
  | succ m ih => intro f; rw [whit_succ, whit_succ, colT_mul hχ, ih]

/- English proof (translation)
Introduce `g hg`. Unfold `colT coefF`. Establish `e : (fun x : UnipotentBlockColumnIndex k j j → Ad E => ψ (-dot (eLast k j) x) * f (blkU x * g)) = fun x => (0 : ℂ) * ψ (-dot (eLast k j) x)`. Use function extensionality and compare the values at `x`. Rewrite using `[hZ _ (by rwa [lastRow_unipotent_mul _ _ (blkU_unipotent_zero x)]), mul_zero, zero_mul]`.

Rewrite using `[e, avg_const_mul, zero_mul]`.
-/
theorem colT_supp {C : Set (Fin k → Ad E)} {f : GA E k → ℂ} (hZ : ∀ g, lastRow g ∉ C → f g = 0) (j : ℕ) :
    ∀ g, lastRow g ∉ C → colT ψ j f g = 0 := by
  intro g hg
  unfold colT coefF
  have e : (fun x : UnipotentBlockColumnIndex k j j → Ad E => ψ (-dot (eLast k j) x) * f (blkU x * g)) =
      fun x => (0 : ℂ) * ψ (-dot (eLast k j) x) := by
    funext x
    rw [hZ _ (by rwa [lastRow_unipotent_mul _ _ (blkU_unipotent_zero x)]), mul_zero, zero_mul]
  rw [e, avg_const_mul, zero_mul]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro f hf`. Conclude with `hf`. Consider the case `succ m ih => intro f hf`. Rewrite using `[whit_succ]`.

Conclude with `ih _ (colT_supp hf (m + 1))`.
-/
theorem whit_supp {C : Set (Fin k → Ad E)} (m : ℕ) :
    ∀ f : GA E k → ℂ, (∀ g, lastRow g ∉ C → f g = 0) → ∀ g, lastRow g ∉ C → whit ψ m f g = 0 := by
  induction m with
  | zero => intro f hf; exact hf
  | succ m ih => intro f hf; rw [whit_succ]; exact ih _ (colT_supp hf (m + 1))

end primeSetTwoBounds

open primeSetTwoBounds in
/- English proof (translation)
Introduce `h1 E _ _ _ k ψ hψ`. Establish `wpre : ∀ m, m < k → ∀ f : GA E k → ℂ, Pre ψ m f → Pre ψ 0 (whit ψ m f)`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro _ f hf`.

Conclude with `hf`. Consider the case `succ m ih`. Introduce `hm f hf`. Rewrite using `[whit_succ]`. Use `(h1 E k ψ hψ (m + 1) (by omega) hm f hf).1` as an intermediate fact.

Rewrite `this` using `[Nat.add_sub_cancel]`. Conclude with `ih (by omega) _ this`. Use `⟨fun m f hf u hu g => pre_law hf (k - (m + 1)) (m + 1) (by omega) le_rfl u hu g, fun u => hψ.norm _, fun u hu => ⟨hu.1, hu.2.1, fun i c hc => ?_⟩, wpre, fun m _ f χ hf hχc hχ hχm => ⟨?_, whit_mul hχ m f, fun hg => ?_⟩, fun m f hf => ⟨hf.cont, hf.left, hf.law⟩, fun u g hu => lastR …` and prove the remaining obligations. Distinguish the cases in `h : i = c`. Substitute `h` using the available equality.

Rewrite using `[hu.2.1, Matrix.one_apply_eq]`. Rewrite using `[hu.1 i c (by have : (i : ℕ) ≠ c := fun e => h (Fin.ext e); omega), Matrix.one_apply_ne h]`. Use `⟨hχc.mul hf.cont, fun γ hγ g => ?_, fun j hj y g => ?_⟩` and prove the remaining obligations. Rewrite using `[hχm γ hγ, hf.left γ hγ]`. Rewrite using `[hχ _ (blkU_unipotent_zero y), hf.law j hj]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨hχc.mul hg.cont, fun γ hγ g => ?_, fun j hj y g => ?_, fun r hr hrm g => ?_⟩` and prove the remaining obligations. Rewrite using `[hχm γ hγ, hg.left γ hγ]`. Rewrite using `[hχ _ (blkU_unipotent_zero y), hg.law j hj]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e : (fun x : UnipotentBlockColumnIndex k r m → Ad E => (fun g => χ g * f g) (blkU x * g)) = fun x => χ g * f (blkU x * g)`. Use function extensionality and compare the values at `x`. Simplify using `only`. Rewrite using `[hχ _ (blkU_unipotent_zero x)]`. Rewrite using `[e, avg_const_mul, hg.van r hr hrm g, mul_zero]`.

Assume the negation of the conclusion as `hn`. Conclude with `hg (whit_supp m f (fun g' hg' => by by_contra h'; exact hg' (hC g' h')) g hn)`.
-/
theorem p2_of : P1 → P2 := by
  intro h1 E _ _ _ k ψ hψ
  have wpre : ∀ m, m < k → ∀ f : GA E k → ℂ, Pre ψ m f → Pre ψ 0 (whit ψ m f) := by
    intro m
    induction m with
    | zero => intro _ f hf; exact hf
    | succ m ih =>
      intro hm f hf
      rw [whit_succ]
      have := (h1 E k ψ hψ (m + 1) (by omega) hm f hf).1
      rw [Nat.add_sub_cancel] at this
      exact ih (by omega) _ this
  refine ⟨fun m f hf u hu g => pre_law hf (k - (m + 1)) (m + 1) (by omega) le_rfl u hu g,
    fun u => hψ.norm _, fun u hu => ⟨hu.1, hu.2.1, fun i c hc => ?_⟩, wpre,
    fun m _ f χ hf hχc hχ hχm => ⟨?_, whit_mul hχ m f, fun hg => ?_⟩, fun m f hf => ⟨hf.cont, hf.left, hf.law⟩,
    fun u g hu => lastRow_unipotent_mul u g hu, fun γ g hγ => lastRow_mir γ g hγ, continuous_lastRow,
    fun m _ f C hC g hg => ?_⟩
  · by_cases h : i = c
    · subst h; rw [hu.2.1, Matrix.one_apply_eq]
    · rw [hu.1 i c (by have : (i : ℕ) ≠ c := fun e => h (Fin.ext e); omega), Matrix.one_apply_ne h]
  · refine ⟨hχc.mul hf.cont, fun γ hγ g => ?_, fun j hj y g => ?_⟩
    · rw [hχm γ hγ, hf.left γ hγ]
    · rw [hχ _ (blkU_unipotent_zero y), hf.law j hj]; ring
  · refine ⟨hχc.mul hg.cont, fun γ hγ g => ?_, fun j hj y g => ?_, fun r hr hrm g => ?_⟩
    · rw [hχm γ hγ, hg.left γ hγ]
    · rw [hχ _ (blkU_unipotent_zero y), hg.law j hj]; ring
    · have e : (fun x : UnipotentBlockColumnIndex k r m → Ad E => (fun g => χ g * f g) (blkU x * g)) =
          fun x => χ g * f (blkU x * g) := by
        funext x; dsimp only; rw [hχ _ (blkU_unipotent_zero x)]
      rw [e, avg_const_mul, hg.van r hr hrm g, mul_zero]
  · by_contra hn
    exact hg (whit_supp m f (fun g' hg' => by by_contra h'; exact hg' (hC g' h')) g hn)

end PositivityTheory.AdelicQuotientData

end
