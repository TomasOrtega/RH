import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnramifiedDegreeOneOfNcardPlacesOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolRatioProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsChoiceOfIdem

open Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab NumberField IsDedekindDomain Matrix Formalism.UG MeasureTheory
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.RowIndex

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact h1 x hx`. Consider the case `zero => intro i _`.

Both sides reduce to the same expression. Consider the case `add x y _ _ hx hy => intro i hi`. Simplify using `[hx i hi, hy i hi]`. Consider the case `smul a x _ hx => intro i hi`. Simplify using `[hx i hi]`.

Introduce `hv`. Establish `hsum : v = ∑ i, v i • Pi.single i (1 : R)`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[hsum]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : T i`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (h2 i hi))`. Simplify using `[hv i hi]`.
-/
theorem mem_span_supp {R : Type} [CommRing R] {N : ℕ} (U : Set (Fin N → R)) (T : Fin N → Prop)
    (h1 : ∀ u ∈ U, ∀ i, ¬ T i → u i = 0) (h2 : ∀ i, T i → Pi.single i 1 ∈ U) (v : Fin N → R) :
    v ∈ Submodule.span R U ↔ ∀ i, ¬ T i → v i = 0 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact h1 x hx
    | zero => intro i _; rfl
    | add x y _ _ hx hy => intro i hi; simp [hx i hi, hy i hi]
    | smul a x _ hx => intro i hi; simp [hx i hi]
  · intro hv
    have hsum : v = ∑ i, v i • Pi.single i (1 : R) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : T i
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (h2 i hi))
    · simp [hv i hi]

/- English proof (translation)
Establish `key : ∀ i : Fin N, Formalism.MainNotions.StandardLattice.blk s k i.1 = s ↔ (s ≤ i.1 ∧ i.1 ≤ s + k)`. Introduce `i`. Unfold `Formalism.MainNotions.StandardLattice.blk`. Apply the tactic sequence `split_ifs <;> omega`. Establish `mono : ∀ i j : Fin N, i ≤ j → Formalism.MainNotions.StandardLattice.blk s k i.1 ≤ Formalism.MainNotions.StandardLattice.blk s k j.1`.

Introduce `i j h`. Establish `h' : i.1 ≤ j.1` using `h`. Unfold `Formalism.MainNotions.StandardLattice.blk`. Apply the tactic sequence `split_ifs <;> omega`. Establish `hL : Formalism.MainNotions.StandardLattice.IsRowLev k s A ↔ ((∀ i j : Fin N, j < i → A i j = 0) ∧ (∀ i, A i i = 1) ∧ ∀ i j : Fin N, j.1 = s + k → s ≤ i.1 → i.1 < s + k → A i j = 0)`.

Unfold `Formalism.MainNotions.StandardLattice.IsRowLev`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨ha, hb, hc, hd⟩`. Use `⟨fun i j hij => ?_, hb, fun i j hj h1 h2 => ?_⟩` and prove the remaining obligations. Break down `lt_or_eq_of_le (mono j i hij.le) with h | h` into its components or cases.

Conclude with `ha i j h`. Conclude with `hc i j h.symm hij`. Conclude with `hd i j hj (fun e => by subst e; omega) ((key i).2 ⟨h1, by omega⟩)`. Introduce and unpack `⟨hl, hb, hd⟩`. Use `⟨fun i j h => hl i j ?_, hb, fun i j _ h => hl i j h, fun i j hj hij hi => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hc push Not at hc`. Conclude with `absurd (mono i j hc) (not_le.2 h)`. Establish `h5` using `(key i).1 hi`. Establish `hne : i.1 ≠ j.1` using `fun e => hij (Fin.ext e)`. Conclude with `hd i j hj h5.1 (by omega)`.

Rewrite using `[hL]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hl, hd1, hd⟩`. Establish `hBr` using `rows_unitri B A h' 0 (fun i _ => ⟨hd1 i, fun j hj => hl i j hj⟩)`. Use `⟨fun j _ i hij => ?_, fun j hj i hi => ?_, fun i _ j hij => ?_⟩` and prove the remaining obligations.

Break down `eq_or_lt_of_le (not_lt.1 hij) with e | e` into its components or cases. Substitute `e` using the available equality. Simplify using `[hd1]`. Rewrite using `[Matrix.sub_apply, Matrix.one_apply_ne e.ne', hl i j e, sub_zero]`. Distinguish the cases in `e : i = j`.

Substitute `e` using the available equality. Simplify using `[hd1]`. Rewrite using `[Matrix.sub_apply, Matrix.one_apply_ne e, sub_zero]`. Break down `lt_or_gt_of_ne (Fin.val_ne_of_ne e) with h1 | h1` into its components or cases. Conclude with `hd i j hj (by omega) (by omega)`.

Conclude with `hl i j h1`. Break down `eq_or_lt_of_le (not_lt.1 hij) with e | e` into its components or cases. Substitute `e` using the available equality. Simplify using `[(hBr j (Nat.zero_le _)).1]`. Rewrite using `[Matrix.sub_apply, Matrix.one_apply_ne e.ne', (hBr i (Nat.zero_le _)).2 j e, sub_zero]`.

Introduce and unpack `⟨h1, h2, h3⟩`. Establish `hB : ∀ i : Fin N, s + k ≤ i.1 → B i i = 1 ∧ ∀ j, j < i → B i j = 0`. Introduce `i hi`. Use `⟨?_, fun j hj => ?_⟩` and prove the remaining obligations. Establish `h5` using `h3 i hi i (lt_irrefl _)`.

Rewrite `h5` using `[Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero]`. Then use the resulting hypothesis. Establish `h5` using `h3 i hi j (not_lt.2 hj.le)`. Rewrite `h5` using `[Matrix.sub_apply, Matrix.one_apply_ne hj.ne', sub_zero]`. Then use the resulting hypothesis. Establish `hA` using `rows_unitri A B h (s + k) hB`. Establish `c1 : ∀ j : Fin N, j.1 < s + k → A j j = 1` using `fun j hj => by`.

Establish `h5` using `h1 j hj j (lt_irrefl _)`. Rewrite `h5` using `[Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero]`. Then use the resulting hypothesis. Establish `c2 : ∀ i j : Fin N, j.1 < s + k → j < i → A i j = 0` using `fun i j hj hji => by`. Establish `h5` using `h1 j hj i (not_lt.2 hji.le)`. Rewrite `h5` using `[Matrix.sub_apply, Matrix.one_apply_ne hji.ne', sub_zero]`. Then use the resulting hypothesis.

Use `⟨fun i j hji => ?_, fun i => ?_, fun i j hj hs hi => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hj : j.1 < s + k`. Conclude with `c2 i j hj hji`. Establish `h6 : j.1 < i.1` using `hji`. Conclude with `(hA i (by omega)).2 j hji`.

Distinguish the cases in `hi : i.1 < s + k`. Conclude with `c1 i hi`. Conclude with `(hA i (by omega)).1`. Establish `h5` using `h2 j hj i (by omega)`. Establish `hne : i ≠ j` using `fun e => by subst e; omega`.

Rewrite `h5` using `[Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]`. Then use the resulting hypothesis.
-/
theorem isRowLev_iff {R : Type} [CommRing R] {N k s : ℕ} (A B : Matrix (Fin N) (Fin N) R) (h : B * A = 1)
    (h' : A * B = 1) :
    Formalism.MainNotions.StandardLattice.IsRowLev k s A ↔
      (∀ j : Fin N, j.1 < s + k → ∀ i, ¬ i < j → (A - 1) i j = 0) ∧
      (∀ j : Fin N, j.1 = s + k → ∀ i : Fin N, ¬ i.1 < s → (A - 1) i j = 0) ∧
      (∀ i : Fin N, s + k ≤ i.1 → ∀ j, ¬ i < j → (B - 1) i j = 0) := by
  have key : ∀ i : Fin N, Formalism.MainNotions.StandardLattice.blk s k i.1 = s ↔ (s ≤ i.1 ∧ i.1 ≤ s + k) := by
    intro i
    unfold Formalism.MainNotions.StandardLattice.blk
    split_ifs <;> omega
  have mono : ∀ i j : Fin N, i ≤ j → Formalism.MainNotions.StandardLattice.blk s k i.1 ≤ Formalism.MainNotions.StandardLattice.blk s k j.1 := by
    intro i j h
    have h' : i.1 ≤ j.1 := h
    unfold Formalism.MainNotions.StandardLattice.blk
    split_ifs <;> omega
  have hL : Formalism.MainNotions.StandardLattice.IsRowLev k s A ↔
      ((∀ i j : Fin N, j < i → A i j = 0) ∧ (∀ i, A i i = 1) ∧
        ∀ i j : Fin N, j.1 = s + k → s ≤ i.1 → i.1 < s + k → A i j = 0) := by
    unfold Formalism.MainNotions.StandardLattice.IsRowLev
    constructor
    · rintro ⟨ha, hb, hc, hd⟩
      refine ⟨fun i j hij => ?_, hb, fun i j hj h1 h2 => ?_⟩
      · rcases lt_or_eq_of_le (mono j i hij.le) with h | h
        · exact ha i j h
        · exact hc i j h.symm hij
      · exact hd i j hj (fun e => by subst e; omega) ((key i).2 ⟨h1, by omega⟩)
    · rintro ⟨hl, hb, hd⟩
      refine ⟨fun i j h => hl i j ?_, hb, fun i j _ h => hl i j h, fun i j hj hij hi => ?_⟩
      · by_contra hc
        push Not at hc
        exact absurd (mono i j hc) (not_le.2 h)
      · have h5 := (key i).1 hi
        have hne : i.1 ≠ j.1 := fun e => hij (Fin.ext e)
        exact hd i j hj h5.1 (by omega)
  rw [hL]
  constructor
  · rintro ⟨hl, hd1, hd⟩
    have hBr := rows_unitri B A h' 0 (fun i _ => ⟨hd1 i, fun j hj => hl i j hj⟩)
    refine ⟨fun j _ i hij => ?_, fun j hj i hi => ?_, fun i _ j hij => ?_⟩
    · rcases eq_or_lt_of_le (not_lt.1 hij) with e | e
      · subst e; simp [hd1]
      · rw [Matrix.sub_apply, Matrix.one_apply_ne e.ne', hl i j e, sub_zero]
    · by_cases e : i = j
      · subst e; simp [hd1]
      · rw [Matrix.sub_apply, Matrix.one_apply_ne e, sub_zero]
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne e) with h1 | h1
        · exact hd i j hj (by omega) (by omega)
        · exact hl i j h1
    · rcases eq_or_lt_of_le (not_lt.1 hij) with e | e
      · subst e; simp [(hBr j (Nat.zero_le _)).1]
      · rw [Matrix.sub_apply, Matrix.one_apply_ne e.ne', (hBr i (Nat.zero_le _)).2 j e, sub_zero]
  · rintro ⟨h1, h2, h3⟩
    have hB : ∀ i : Fin N, s + k ≤ i.1 → B i i = 1 ∧ ∀ j, j < i → B i j = 0 := by
      intro i hi
      refine ⟨?_, fun j hj => ?_⟩
      · have h5 := h3 i hi i (lt_irrefl _)
        rwa [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at h5
      · have h5 := h3 i hi j (not_lt.2 hj.le)
        rwa [Matrix.sub_apply, Matrix.one_apply_ne hj.ne', sub_zero] at h5
    have hA := rows_unitri A B h (s + k) hB
    have c1 : ∀ j : Fin N, j.1 < s + k → A j j = 1 := fun j hj => by
      have h5 := h1 j hj j (lt_irrefl _)
      rwa [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at h5
    have c2 : ∀ i j : Fin N, j.1 < s + k → j < i → A i j = 0 := fun i j hj hji => by
      have h5 := h1 j hj i (not_lt.2 hji.le)
      rwa [Matrix.sub_apply, Matrix.one_apply_ne hji.ne', sub_zero] at h5
    refine ⟨fun i j hji => ?_, fun i => ?_, fun i j hj hs hi => ?_⟩
    · by_cases hj : j.1 < s + k
      · exact c2 i j hj hji
      · have h6 : j.1 < i.1 := hji
        exact (hA i (by omega)).2 j hji
    · by_cases hi : i.1 < s + k
      · exact c1 i hi
      · exact (hA i (by omega)).1
    · have h5 := h2 j hj i (by omega)
      have hne : i ≠ j := fun e => by subst e; omega
      rwa [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at h5

variable {I : AutInst}

/- English proof (translation)
Establish `hm : 1 ≤ g 0 * g 1` using `Nat.mul_pos (hC.1 0).pos (hC.1 1).pos`. Establish `hgk : ∀ (q : Fin 2) (u : HeightOneSpectrum (𝓞 I.E)), ((g q : ℕ) : 𝓞 I.E) ∈ u.asIdeal → ((g 0 * g 1 : ℕ) : 𝓞 I.E) ∈ u.asIdeal`. Introduce `q u hu`. Rewrite using `[Nat.cast_mul]`. Use `fin_cases q`.

Conclude with `u.asIdeal.mul_mem_right _ hu`. Conclude with `u.asIdeal.mul_mem_left _ hu`. Establish `hconjg : ∀ q v, ((g q : ℕ) : 𝓞 I.E) ∈ (w' q v).asIdeal` using `fun q v => (hw' q v (g q) (g q) (by simp)).1 ((hC.2.2.2.1 q v).1)`. Rewrite using `[mem_mod_iff hm (IsChoice.isRadical_mul hC) (Submodule.span _ S) y]`. Prove the components needed by the constructor for the conclusion.

Introduce `h q v`. Conclude with `⟨(mem_span_iff (fr q v) S y).1 (h _ (hgk q _ (hC.2.2.2.1 q v).1)), (mem_span_iff (fr' q v) S y).1 (h _ (hgk q _ (hconjg q v)))⟩`. Introduce `h u hu`. Rewrite `hu` using `[Nat.cast_mul]`. Establish `hq : ∃ q : Fin 2, ((g q : ℕ) : 𝓞 I.E) ∈ u.asIdeal`.

Break down `u.isPrime.mem_or_mem hu with h0 | h1` into its components or cases. Conclude with `⟨0, h0⟩`. Conclude with `⟨1, h1⟩`. Take `⟨q, hq⟩` from `hq`. Take `⟨v, hv | hv⟩` from `hC.2.2.2.2.2.2 q u hq`.

Substitute `hv` using the available equality. Conclude with `(mem_span_iff (fr q v) S y).2 (h q v).1`. Establish `e : u = w' q v` using `(extId_mul_sup_natCast_conj I).2.2.2.2.2.1 _ _ _ hv (hw' q v)`. Substitute `e` using the available equality. Conclude with `(mem_span_iff (fr' q v) S y).2 (h q v).2`.
-/
theorem cong_iff {N : ℕ} {g : Fin 2 → ℕ} {Pl : Fin 2 → Type} {w w' : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)}
    (hC : IsChoice I g Pl w) (hw' : ∀ k v, IsConj I (w k v) (w' k v))
    (fr : ∀ k v, PlFrame I N (g k) (w k v)) (fr' : ∀ k v, PlFrame I N (g k) (w' k v)) (S : Set I.Lf) (y : I.Lf) :
    (∃ s ∈ Submodule.span (IntAf I.F I.E) S, ∃ z ∈ I.Lf,
        y.1 = s.1 + ((g 0 * g 1 : ℕ) : I.E ⊗[I.F] Af I.F) • z) ↔
      ∀ k v, (fr k v).c y ∈ Submodule.span (ZMod (g k)) ((fr k v).c '' S) ∧
        (fr' k v).c y ∈ Submodule.span (ZMod (g k)) ((fr' k v).c '' S) := by
  have hm : 1 ≤ g 0 * g 1 := Nat.mul_pos (hC.1 0).pos (hC.1 1).pos
  have hgk : ∀ (q : Fin 2) (u : HeightOneSpectrum (𝓞 I.E)), ((g q : ℕ) : 𝓞 I.E) ∈ u.asIdeal →
      ((g 0 * g 1 : ℕ) : 𝓞 I.E) ∈ u.asIdeal := by
    intro q u hu
    rw [Nat.cast_mul]
    fin_cases q
    · exact u.asIdeal.mul_mem_right _ hu
    · exact u.asIdeal.mul_mem_left _ hu
  have hconjg : ∀ q v, ((g q : ℕ) : 𝓞 I.E) ∈ (w' q v).asIdeal := fun q v =>
    (hw' q v (g q) (g q) (by simp)).1 ((hC.2.2.2.1 q v).1)
  rw [mem_mod_iff hm (IsChoice.isRadical_mul hC) (Submodule.span _ S) y]
  constructor
  · intro h q v
    exact ⟨(mem_span_iff (fr q v) S y).1 (h _ (hgk q _ (hC.2.2.2.1 q v).1)),
      (mem_span_iff (fr' q v) S y).1 (h _ (hgk q _ (hconjg q v)))⟩
  · intro h u hu
    rw [Nat.cast_mul] at hu
    have hq : ∃ q : Fin 2, ((g q : ℕ) : 𝓞 I.E) ∈ u.asIdeal := by
      rcases u.isPrime.mem_or_mem hu with h0 | h1
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
    obtain ⟨q, hq⟩ := hq
    obtain ⟨v, hv | hv⟩ := hC.2.2.2.2.2.2 q u hq
    · subst hv
      exact (mem_span_iff (fr q v) S y).2 (h q v).1
    · have e : u = w' q v := (extId_mul_sup_natCast_conj I).2.2.2.2.2.1 _ _ _ hv (hw' q v)
      subst e
      exact (mem_span_iff (fr' q v) S y).2 (h q v).2

/- English proof (translation)
Take `⟨r, hr⟩` from `exists_reduction (F := I.F) (E := I.E) p hp w hw`. Establish `hker` using `ker_eq_extId hp.ne_zero r hr`. Establish `hdual : ∀ i j, r (hI (b' i) (b j)) = if i = j then 1 else 0`. Introduce `i j`. Establish `h` using `hb i j`.

Rewrite `h` using `[← hker, RingHom.mem_ker, map_sub, sub_eq_zero]`. Rewrite using `[h]`. Apply the tactic sequence `split_ifs <;> simp`. Take `⟨fr, hfr, hfc⟩` from `exists_frame_of_dual hn hp hw r hr b b' hdual`. Establish `hr'` using `conj_reduction hc r hr`.

Establish `hdual' : ∀ i j, (r.comp (sigI I)) (hI (b i) (b' j)) = if i = j then 1 else 0`. Introduce `i j`. Rewrite using `[RingHom.comp_apply, sigI_hI, hdual j i]`. Distinguish the cases in `e : i = j`. Substitute `e` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[e, Ne.symm e]`. Take `⟨fr', hfr', hfc'⟩` from `exists_frame_of_dual hn hp hw' (r.comp (sigI I)) hr' b' b hdual'`. Establish `hb1 : ∀ j, fr.c (b j) = Pi.single j 1`. Introduce `j`.

Use function extensionality and compare the values at `i`. Rewrite using `[hfc, hdual]`. Simplify using `[Pi.single_apply]`. Use `⟨fr, fr', hb1, fun j => ?_, fun a => ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Rewrite using `[hfc', hdual']`. Simplify using `[Pi.single_apply]`. Rewrite using `[hfr', hfr]`. Both sides reduce to the same expression. Introduce `x hx M hM i j`.

Use `⟨(entry_eq fr b hb1 hx hM i j).symm, ?_⟩` and prove the remaining obligations. Establish `hxi : x⁻¹ ∈ I.Kset` using `(Ksub I).inv_mem hx`. Take `⟨M2, hM2⟩` from `fr.exists_actsAs hxi`. Establish `hmul : fr.ActsAs (x * x⁻¹) (M.1 * M2)` using `PlFrame.ActsAs.mul fr hxi hM hM2`. Rewrite `hmul` using `[mul_inv_cancel]`.

Establish `h1 : M.1 * M2 = 1` using `PlFrame.ActsAs.unique fr (Ksub I).one_mem hmul fr.actsAs_one`. Establish `h2 : (M⁻¹).1 = M2`. Combine the equalities or inequalities in the displayed calculation. Establish `e2` using `entry_eq fr b hb1 hxi hM2 j i`. Rewrite using `[hfc', RingHom.comp_apply, sigI_hI, hI_latEnd, ← hfc, ← e2, h2]`.
-/
theorem exists_frames {N p : ℕ} {w w' : HeightOneSpectrum (𝓞 I.E)} (hn : I.n = N) (hp : p.Prime)
    (hw : Ideal.absNorm w.asIdeal = p) (hw' : Ideal.absNorm w'.asIdeal = p) (hc : IsConj I w w')
    (b b' : Fin N → I.Lf) (hb : ∀ i j, hI (b' i) (b j) - (if i = j then 1 else 0) ∈ extId I w.asIdeal) :
    ∃ (fr : PlFrame I N p w) (fr' : PlFrame I N p w'), (∀ j, fr.c (b j) = Pi.single j 1) ∧
      (∀ j, fr'.c (b' j) = Pi.single j 1) ∧ (∀ a, fr'.r a = fr.r (sigI I a)) ∧
      ∀ (x : I.Gf) (hx : x ∈ I.Kset) (M : GL (Fin N) (ZMod p)), fr.ActsAs x M →
        ∀ i j, fr.c (latEnd hx (b j)) i = M.1 i j ∧ fr'.c (latEnd hx (b' j)) i = (M⁻¹).1 j i := by
  obtain ⟨r, hr⟩ := exists_reduction (F := I.F) (E := I.E) p hp w hw
  have hker := ker_eq_extId hp.ne_zero r hr
  have hdual : ∀ i j, r (hI (b' i) (b j)) = if i = j then 1 else 0 := by
    intro i j
    have h := hb i j
    rw [← hker, RingHom.mem_ker, map_sub, sub_eq_zero] at h
    rw [h]
    split_ifs <;> simp
  obtain ⟨fr, hfr, hfc⟩ := exists_frame_of_dual hn hp hw r hr b b' hdual
  have hr' := conj_reduction hc r hr
  have hdual' : ∀ i j, (r.comp (sigI I)) (hI (b i) (b' j)) = if i = j then 1 else 0 := by
    intro i j
    rw [RingHom.comp_apply, sigI_hI, hdual j i]
    by_cases e : i = j
    · subst e; simp
    · simp [e, Ne.symm e]
  obtain ⟨fr', hfr', hfc'⟩ := exists_frame_of_dual hn hp hw' (r.comp (sigI I)) hr' b' b hdual'
  have hb1 : ∀ j, fr.c (b j) = Pi.single j 1 := by
    intro j
    funext i
    rw [hfc, hdual]
    simp [Pi.single_apply]
  refine ⟨fr, fr', hb1, fun j => ?_, fun a => ?_, ?_⟩
  · funext i
    rw [hfc', hdual']
    simp [Pi.single_apply]
  · rw [hfr', hfr]
    rfl
  · intro x hx M hM i j
    refine ⟨(entry_eq fr b hb1 hx hM i j).symm, ?_⟩
    have hxi : x⁻¹ ∈ I.Kset := (Ksub I).inv_mem hx
    obtain ⟨M2, hM2⟩ := fr.exists_actsAs hxi
    have hmul : fr.ActsAs (x * x⁻¹) (M.1 * M2) := PlFrame.ActsAs.mul fr hxi hM hM2
    rw [mul_inv_cancel] at hmul
    have h1 : M.1 * M2 = 1 := PlFrame.ActsAs.unique fr (Ksub I).one_mem hmul fr.actsAs_one
    have h2 : (M⁻¹).1 = M2 := by
      calc (M⁻¹).1 = (M⁻¹).1 * (M.1 * M2) := by rw [h1, mul_one]
        _ = M2 := by rw [← mul_assoc, Units.inv_mul, one_mul]
    have e2 := entry_eq fr b hb1 hxi hM2 j i
    rw [hfc', RingHom.comp_apply, sigI_hI, hI_latEnd, ← hfc, ← e2, h2]

/- English proof (translation)
Establish `hfr : Module.finrank ℚ E = Module.finrank ℚ E'` using `ι.toRatAlgEquiv.toLinearEquiv.finrank_eq`. Use `set n := Module.finrank ℚ E' with hn`. Use `set S := {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal} with hS`. Set `φ : 𝓞 E ≃+* 𝓞 E'` to `NumberField.RingOfIntegers.mapRingEquiv ι`. Establish `hcount : S.ncard = n`.

Rewrite using `[← h]`. Use `Set.ncard_congr (fun v _ => HeightOneSpectrum.equivOfRingEquiv φ v) ?_ ?_ ?_` and prove the remaining obligations. Introduce `v hv show (φ.symm : 𝓞 E' →+* 𝓞 E) ((p : ℕ) : 𝓞 E') ∈ v.asIdeal`. Rewrite using `[map_natCast]`. Conclude with `hv`.

Introduce `a c _ _ e`. Conclude with `(HeightOneSpectrum.equivOfRingEquiv φ).injective e`. Introduce `v' hv'`. Use `⟨(HeightOneSpectrum.equivOfRingEquiv φ).symm v', ?_, (HeightOneSpectrum.equivOfRingEquiv φ).apply_symm_apply v'⟩` and prove the remaining obligations. Use `show (φ : 𝓞 E →+* 𝓞 E') ((p : ℕ) : 𝓞 E) ∈ v'.asIdeal`.

Rewrite using `[map_natCast]`. Conclude with `hv'`. Establish `hnpos : 0 < n` using `Module.finrank_pos`. Establish `hfin : S.Finite` using `Set.finite_of_ncard_pos (by omega)`. Use `set T := hfin.toFinset with hT`.

Establish `hTc : T.card = n` using `by rw [hT, ← Set.ncard_eq_toFinset_card S hfin, hcount]`. Establish `hmemT : ∀ v, v ∈ T ↔ ((p : ℕ) : 𝓞 E) ∈ v.asIdeal` using `fun v => by simp [hT, hS]`. Establish `hnorm : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 E)}) = p ^ n`. Rewrite using `[Ideal.absNorm_span_singleton]`. Establish `e : ((p : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ)` using `by simp`.

Rewrite using `[e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, hfr]`. Simplify using the standard rewrite rules. Establish `hdv : ∀ v ∈ T, Ideal.absNorm v.asIdeal ∣ p ^ n`. Introduce `v hv`. Rewrite using `[← hnorm]`.

Conclude with `Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 ((hmemT v).1 hv))`. Use `choose! j hj using fun v (hv : v ∈ T) => (Nat.dvd_prime_pow hp).1 (hdv v hv)`. Establish `hj1 : ∀ v ∈ T, 1 ≤ j v`. Introduce `v hv`. Assume the negation of the conclusion as `h0`.

Establish `h00 : j v = 0` using `by omega`. Establish `h1 : Ideal.absNorm v.asIdeal = 1` using `by rw [(hj v hv).2, h00, pow_zero]`. Conclude with `v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h1)`. Establish `hcop : (T : Set (HeightOneSpectrum (𝓞 E))).Pairwise (Function.onFun IsCoprime (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal))`. Introduce `v _ w _ hvw`.

Use `show IsCoprime v.asIdeal w.asIdeal`. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Conclude with `Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal (fun e => hvw (HeightOneSpectrum.ext e))`. Establish `hJ : ∏ v ∈ T, v.asIdeal = ⨅ v ∈ T, v.asIdeal` using `Ideal.prod_eq_iInf_of_pairwise_isCoprime hcop`. Establish `hle : Ideal.span {((p : ℕ) : 𝓞 E)} ≤ ∏ v ∈ T, v.asIdeal`.

Rewrite using `[hJ]`. Use `le_iInf₂ fun v hv => ?_` and prove the remaining obligations. Conclude with `(Ideal.span_singleton_le_iff_mem _).2 ((hmemT v).1 hv)`. Establish `hJn : Ideal.absNorm (∏ v ∈ T, v.asIdeal) = p ^ (∑ v ∈ T, j v)`. Rewrite using `[map_prod, Finset.prod_congr rfl (fun v hv => (hj v hv).2), Finset.prod_pow_eq_pow_sum]`.

Establish `hsum_le : ∑ v ∈ T, j v ≤ n`. Establish `h5` using `Ideal.absNorm_dvd_absNorm_of_le hle`. Rewrite `h5` using `[hnorm, hJn]`. Conclude with `(Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h5`. Establish `hsum_ge : n ≤ ∑ v ∈ T, j v`.

Rewrite using `[← hTc, Finset.card_eq_sum_ones]`. Conclude with `Finset.sum_le_sum hj1`. Establish `hall : ∀ v ∈ T, j v = 1`. Establish `h5` using `(Finset.sum_eq_sum_iff_of_le hj1).1 (by rw [← Finset.card_eq_sum_ones, hTc]; omega)`. Conclude with `fun v hv => (h5 v hv).symm`.

Establish `heq : Ideal.span {((p : ℕ) : 𝓞 E)} = ∏ v ∈ T, v.asIdeal`. Take `⟨K, hK⟩` from `Ideal.dvd_iff_le.2 hle`. Establish `h1 : Ideal.absNorm K = 1`. Establish `h5` using `congrArg Ideal.absNorm hK`. Rewrite `h5` using `[map_mul, hnorm, hJn, show ∑ v ∈ T, j v = n by omega]`.

Establish `hp0 : 0 < p ^ n` using `pow_pos hp.pos _`. Conclude with `Nat.eq_of_mul_eq_mul_left hp0 (by rw [mul_one]; exact h5.symm)`. Rewrite using `[hK, Ideal.absNorm_eq_one_iff.1 h1, Ideal.mul_top]`. Use `⟨hcount, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[heq, hJ]`.

Conclude with `Ideal.isRadical_iInf _ fun v => Ideal.isRadical_iInf _ fun _ => v.isPrime.isRadical`. Introduce `v hv`. Rewrite using `[(hj v ((hmemT v).2 hv)).2, hall v ((hmemT v).2 hv), pow_one]`.
-/
theorem split_facts {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (ι : E ≃+* E') {p : ℕ}
    (hp : p.Prime) (h : (Formalism.BasicNotions.placesOver E' p).ncard = Module.finrank ℚ E') :
    {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E' ∧
    (Ideal.span {((p : ℕ) : 𝓞 E)}).IsRadical ∧
    ∀ v : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ v.asIdeal → Ideal.absNorm v.asIdeal = p := by
  classical
  have hfr : Module.finrank ℚ E = Module.finrank ℚ E' := ι.toRatAlgEquiv.toLinearEquiv.finrank_eq
  set n := Module.finrank ℚ E' with hn
  set S := {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal} with hS
  let φ : 𝓞 E ≃+* 𝓞 E' := NumberField.RingOfIntegers.mapRingEquiv ι
  have hcount : S.ncard = n := by
    rw [← h]
    refine Set.ncard_congr (fun v _ => HeightOneSpectrum.equivOfRingEquiv φ v) ?_ ?_ ?_
    · intro v hv
      show (φ.symm : 𝓞 E' →+* 𝓞 E) ((p : ℕ) : 𝓞 E') ∈ v.asIdeal
      rw [map_natCast]
      exact hv
    · intro a c _ _ e
      exact (HeightOneSpectrum.equivOfRingEquiv φ).injective e
    · intro v' hv'
      refine ⟨(HeightOneSpectrum.equivOfRingEquiv φ).symm v', ?_,
        (HeightOneSpectrum.equivOfRingEquiv φ).apply_symm_apply v'⟩
      show (φ : 𝓞 E →+* 𝓞 E') ((p : ℕ) : 𝓞 E) ∈ v'.asIdeal
      rw [map_natCast]
      exact hv'
  have hnpos : 0 < n := Module.finrank_pos
  have hfin : S.Finite := Set.finite_of_ncard_pos (by omega)
  set T := hfin.toFinset with hT
  have hTc : T.card = n := by rw [hT, ← Set.ncard_eq_toFinset_card S hfin, hcount]
  have hmemT : ∀ v, v ∈ T ↔ ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := fun v => by simp [hT, hS]
  have hnorm : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 E)}) = p ^ n := by
    rw [Ideal.absNorm_span_singleton]
    have e : ((p : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) := by simp
    rw [e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, hfr]
    simp
  have hdv : ∀ v ∈ T, Ideal.absNorm v.asIdeal ∣ p ^ n := by
    intro v hv
    rw [← hnorm]
    exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 ((hmemT v).1 hv))
  choose! j hj using fun v (hv : v ∈ T) => (Nat.dvd_prime_pow hp).1 (hdv v hv)
  have hj1 : ∀ v ∈ T, 1 ≤ j v := by
    intro v hv
    by_contra h0
    have h00 : j v = 0 := by omega
    have h1 : Ideal.absNorm v.asIdeal = 1 := by rw [(hj v hv).2, h00, pow_zero]
    exact v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h1)
  have hcop : (T : Set (HeightOneSpectrum (𝓞 E))).Pairwise
      (Function.onFun IsCoprime (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal)) := by
    intro v _ w _ hvw
    show IsCoprime v.asIdeal w.asIdeal
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal
      (fun e => hvw (HeightOneSpectrum.ext e))
  have hJ : ∏ v ∈ T, v.asIdeal = ⨅ v ∈ T, v.asIdeal := Ideal.prod_eq_iInf_of_pairwise_isCoprime hcop
  have hle : Ideal.span {((p : ℕ) : 𝓞 E)} ≤ ∏ v ∈ T, v.asIdeal := by
    rw [hJ]
    refine le_iInf₂ fun v hv => ?_
    exact (Ideal.span_singleton_le_iff_mem _).2 ((hmemT v).1 hv)
  have hJn : Ideal.absNorm (∏ v ∈ T, v.asIdeal) = p ^ (∑ v ∈ T, j v) := by
    rw [map_prod, Finset.prod_congr rfl (fun v hv => (hj v hv).2), Finset.prod_pow_eq_pow_sum]
  have hsum_le : ∑ v ∈ T, j v ≤ n := by
    have h5 := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [hnorm, hJn] at h5
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h5
  have hsum_ge : n ≤ ∑ v ∈ T, j v := by
    rw [← hTc, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum hj1
  have hall : ∀ v ∈ T, j v = 1 := by
    have h5 := (Finset.sum_eq_sum_iff_of_le hj1).1 (by rw [← Finset.card_eq_sum_ones, hTc]; omega)
    exact fun v hv => (h5 v hv).symm
  have heq : Ideal.span {((p : ℕ) : 𝓞 E)} = ∏ v ∈ T, v.asIdeal := by
    obtain ⟨K, hK⟩ := Ideal.dvd_iff_le.2 hle
    have h1 : Ideal.absNorm K = 1 := by
      have h5 := congrArg Ideal.absNorm hK
      rw [map_mul, hnorm, hJn, show ∑ v ∈ T, j v = n by omega] at h5
      have hp0 : 0 < p ^ n := pow_pos hp.pos _
      exact Nat.eq_of_mul_eq_mul_left hp0 (by rw [mul_one]; exact h5.symm)
    rw [hK, Ideal.absNorm_eq_one_iff.1 h1, Ideal.mul_top]
  refine ⟨hcount, ?_, ?_⟩
  · rw [heq, hJ]
    exact Ideal.isRadical_iInf _ fun v => Ideal.isRadical_iInf _ fun _ => v.isPrime.isRadical
  · intro v hv
    rw [(hj v ((hmemT v).2 hv)).2, hall v ((hmemT v).2 hv), pow_one]

/- English proof (translation)
Establish `hMi : (M⁻¹).1 * M.1 = 1` using `M.inv_mul`. Establish `hMi' : M.1 * (M⁻¹).1 = 1` using `M.mul_inv`. Rewrite using `[isRowLev_iff M.1 (M⁻¹).1 hMi hMi']`. Establish `hA : ∀ j i, c (T (b j) - b j) i = (M.1 - 1) i j`. Introduce `j i`.

Rewrite using `[map_sub, Pi.sub_apply, (hM i j).1, hb, Matrix.sub_apply, Pi.single_apply, Matrix.one_apply]`. Establish `hB : ∀ m l, c' (T (b' m) - b' m) l = ((M⁻¹).1 - 1) m l`. Introduce `m l`. Rewrite using `[map_sub, Pi.sub_apply, (hM l m).2, hb', Matrix.sub_apply, Pi.single_apply, Matrix.one_apply]`. Distinguish the cases in `e : l = m`.

Substitute `e` using the available equality. Simplify using the standard rewrite rules. Simplify using `[e, Ne.symm e]`. Establish `hz : ∀ j : Fin N, s ≤ j.1 → j.1 < s + k → c' (T (b j) - b j) = 0`. Introduce `j hj1 hj2`.

Rewrite using `[← h3 j hj1 hj2, map_smul, ← smul_sub, map_smulₛₗ, hε, zero_smul]`. Establish `spanC : ∀ (P : Fin N → Prop) (v : Fin N → ZMod p), v ∈ Submodule.span (ZMod p) (c '' (b '' {i | P i})) ↔ ∀ i, ¬ P i → v i = 0`. Introduce `P v`. Use `mem_span_supp _ P ?_ ?_ v` and prove the remaining obligations. Introduce and unpack `u ⟨_, ⟨i0, hi0, rfl⟩, rfl⟩ i hi`.

Rewrite using `[hb, Pi.single_apply, if_neg]`. Introduce and unpack `rfl`. Conclude with `hi hi0`. Introduce `i hi`. Conclude with `⟨b i, ⟨i, hi, rfl⟩, hb i⟩`.

Establish `spanC' : ∀ (P : Fin N → Prop) (v : Fin N → ZMod p), (∀ i, P i → i.1 < s) → (v ∈ Submodule.span (ZMod p) (c' '' (b '' {i | P i})) ↔ ∀ l : Fin N, ¬ P l.rev → v l = 0)`. Introduce `P v hP`. Use `mem_span_supp _ (fun l => P l.rev) ?_ ?_ v` and prove the remaining obligations. Introduce and unpack `u ⟨_, ⟨i0, hi0, rfl⟩, rfl⟩ l hl`. Rewrite using `[h1 i0 (hP i0 hi0), hb', Pi.single_apply, if_neg]`.

Introduce `e`. Apply `hl` to reduce the goal to its premises. Use `show P l.rev`. Rewrite using `[e, Fin.rev_rev]`. Conclude with `hi0`.

Introduce `l hl`. Use `⟨b l.rev, ⟨l.rev, hl, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[h1 _ (hP _ hl), hb', Fin.rev_rev]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hP, hQ⟩`.

Use `⟨fun j hj i hi => ?_, fun j hj i hi => ?_, fun i hi l hl => ?_⟩` and prove the remaining obligations. Rewrite using `[← hA]`. Conclude with `(spanC (· < j) _).1 (hP j hj).1 i hi`. Rewrite using `[← hA]`. Conclude with `(spanC (fun i => i.1 < s) _).1 (hQ j hj).1 i hi`.

Establish `hl' : l.1 ≤ i.1` using `not_lt.1 hl`. Establish `hlr` using `Fin.val_rev l`. Establish `hir` using `Fin.val_rev i`. Establish `hi2` using `i.2`. Establish `hl2` using `l.2`.

Distinguish the cases in `hi' : i.1 = s + k`. Establish `e : T (b i) - b i = -(T (b' i) - b' i)`. Rewrite using `[h2 i hi', map_neg]`. Normalize the expressions using the abelian group laws. Establish `h5` using `(hQ i hi').2`.

Rewrite `h5` using `[e, map_neg, Submodule.neg_mem_iff]`. Rewrite using `[← hB]`. Use `(spanC' (fun i => i.1 < s) _ (fun _ h => h)).1 h5 l ?_` and prove the remaining obligations. Use `show ¬ l.rev.1 < s`. Use linear arithmetic over natural numbers and integers.

Establish `hj : i.rev.1 < s` using `by omega`. Establish `h5` using `(hP i.rev (by omega)).2`. Establish `e : T (b i.rev) - b i.rev = T (b' i) - b' i`. Rewrite using `[h1 _ hj, Fin.rev_rev]`. Rewrite `h5` using `[e]`.

Rewrite using `[← hB]`. Use `(spanC' (· < i.rev) _ (fun _ h => lt_trans (show _ < i.rev.1 from h) hj)).1 h5 l ?_` and prove the remaining obligations. Use `show ¬ l.rev.1 < i.rev.1`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨r1, r2, r3⟩`.

Use `⟨fun j hj => ⟨?_, ?_⟩, fun j hj => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `(spanC (· < j) _).2 fun i hi => by rw [hA]; exact r1 j hj i hi`. Distinguish the cases in `hjs : j.1 < s`. Establish `e : T (b j) - b j = T (b' j.rev) - b' j.rev` using `by rw [h1 j hjs]`. Rewrite using `[e]`.

Use `(spanC' (· < j) _ (fun _ h => lt_trans (show _ < j.1 from h) hjs)).2 fun l hl => ?_` and prove the remaining obligations. Rewrite using `[hB]`. Establish `hjr` using `Fin.val_rev j`. Establish `hlr` using `Fin.val_rev l`. Establish `hj2` using `j.2`.

Establish `hl2` using `l.2`. Use `r3 j.rev (by omega) l ?_` and prove the remaining obligations. Introduce `hlt`. Apply `hl` to reduce the goal to its premises. Use `show l.rev.1 < j.1`.

Establish `h6 : j.rev.1 < l.1` using `hlt`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hz j (not_lt.1 hjs) hj]`. Conclude with `zero_mem _`. Conclude with `(spanC (fun i => i.1 < s) _).2 fun i hi => by rw [hA]; exact r2 j hj i hi`.

Establish `e : T (b j) - b j = -(T (b' j) - b' j)`. Rewrite using `[h2 j hj, map_neg]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, map_neg, Submodule.neg_mem_iff]`. Use `(spanC' (fun i => i.1 < s) _ (fun _ h => h)).2 fun l hl => ?_` and prove the remaining obligations.

Rewrite using `[hB]`. Use `r3 j (le_of_eq hj.symm) l ?_` and prove the remaining obligations. Introduce `hlt`. Apply `hl` to reduce the goal to its premises. Use `show l.rev.1 < s`.

Establish `hlr` using `Fin.val_rev l`. Establish `hl2` using `l.2`. Establish `h6 : j.1 < l.1` using `hlt`. Use linear arithmetic over natural numbers and integers.
-/
theorem local_iff {N p k s : ℕ} (hN : N = s + k + 1 + s) {R L : Type} [CommRing R] [AddCommGroup L] [Module R L]
    {r r' : R →+* ZMod p} (c : L →ₛₗ[r] (Fin N → ZMod p)) (c' : L →ₛₗ[r'] (Fin N → ZMod p)) (b b' : Fin N → L)
    (hb : ∀ j, c (b j) = Pi.single j 1) (hb' : ∀ j, c' (b' j) = Pi.single j 1)
    (h1 : ∀ j : Fin N, j.1 < s → b j = b' j.rev) (h2 : ∀ j : Fin N, j.1 = s + k → b j = - b' j)
    (ε : R) (hε : r' ε = 0) (h3 : ∀ j : Fin N, s ≤ j.1 → j.1 < s + k → ε • b j = b j)
    (T : L →ₗ[R] L) (M : GL (Fin N) (ZMod p))
    (hM : ∀ i j, c (T (b j)) i = M.1 i j ∧ c' (T (b' j)) i = (M⁻¹).1 j i) :
    ((∀ j : Fin N, j.1 < s + k →
        c (T (b j) - b j) ∈ Submodule.span (ZMod p) (c '' (b '' {i | i < j})) ∧
        c' (T (b j) - b j) ∈ Submodule.span (ZMod p) (c' '' (b '' {i | i < j}))) ∧
      ∀ j : Fin N, j.1 = s + k →
        c (T (b j) - b j) ∈ Submodule.span (ZMod p) (c '' (b '' {i | i.1 < s})) ∧
        c' (T (b j) - b j) ∈ Submodule.span (ZMod p) (c' '' (b '' {i | i.1 < s}))) ↔
      Formalism.MainNotions.StandardLattice.IsRowLev k s M.1 := by
  have hMi : (M⁻¹).1 * M.1 = 1 := M.inv_mul
  have hMi' : M.1 * (M⁻¹).1 = 1 := M.mul_inv
  rw [isRowLev_iff M.1 (M⁻¹).1 hMi hMi']
  have hA : ∀ j i, c (T (b j) - b j) i = (M.1 - 1) i j := by
    intro j i
    rw [map_sub, Pi.sub_apply, (hM i j).1, hb, Matrix.sub_apply, Pi.single_apply, Matrix.one_apply]
  have hB : ∀ m l, c' (T (b' m) - b' m) l = ((M⁻¹).1 - 1) m l := by
    intro m l
    rw [map_sub, Pi.sub_apply, (hM l m).2, hb', Matrix.sub_apply, Pi.single_apply, Matrix.one_apply]
    by_cases e : l = m
    · subst e; simp
    · simp [e, Ne.symm e]
  have hz : ∀ j : Fin N, s ≤ j.1 → j.1 < s + k → c' (T (b j) - b j) = 0 := by
    intro j hj1 hj2
    rw [← h3 j hj1 hj2, map_smul, ← smul_sub, map_smulₛₗ, hε, zero_smul]
  have spanC : ∀ (P : Fin N → Prop) (v : Fin N → ZMod p),
      v ∈ Submodule.span (ZMod p) (c '' (b '' {i | P i})) ↔ ∀ i, ¬ P i → v i = 0 := by
    intro P v
    refine mem_span_supp _ P ?_ ?_ v
    · rintro u ⟨_, ⟨i0, hi0, rfl⟩, rfl⟩ i hi
      rw [hb, Pi.single_apply, if_neg]
      rintro rfl
      exact hi hi0
    · intro i hi
      exact ⟨b i, ⟨i, hi, rfl⟩, hb i⟩
  have spanC' : ∀ (P : Fin N → Prop) (v : Fin N → ZMod p), (∀ i, P i → i.1 < s) →
      (v ∈ Submodule.span (ZMod p) (c' '' (b '' {i | P i})) ↔ ∀ l : Fin N, ¬ P l.rev → v l = 0) := by
    intro P v hP
    refine mem_span_supp _ (fun l => P l.rev) ?_ ?_ v
    · rintro u ⟨_, ⟨i0, hi0, rfl⟩, rfl⟩ l hl
      rw [h1 i0 (hP i0 hi0), hb', Pi.single_apply, if_neg]
      intro e
      apply hl
      show P l.rev
      rw [e, Fin.rev_rev]
      exact hi0
    · intro l hl
      refine ⟨b l.rev, ⟨l.rev, hl, rfl⟩, ?_⟩
      rw [h1 _ (hP _ hl), hb', Fin.rev_rev]
  constructor
  · rintro ⟨hP, hQ⟩
    refine ⟨fun j hj i hi => ?_, fun j hj i hi => ?_, fun i hi l hl => ?_⟩
    · rw [← hA]
      exact (spanC (· < j) _).1 (hP j hj).1 i hi
    · rw [← hA]
      exact (spanC (fun i => i.1 < s) _).1 (hQ j hj).1 i hi
    · have hl' : l.1 ≤ i.1 := not_lt.1 hl
      have hlr := Fin.val_rev l
      have hir := Fin.val_rev i
      have hi2 := i.2
      have hl2 := l.2
      by_cases hi' : i.1 = s + k
      · have e : T (b i) - b i = -(T (b' i) - b' i) := by
          rw [h2 i hi', map_neg]
          abel
        have h5 := (hQ i hi').2
        rw [e, map_neg, Submodule.neg_mem_iff] at h5
        rw [← hB]
        refine (spanC' (fun i => i.1 < s) _ (fun _ h => h)).1 h5 l ?_
        show ¬ l.rev.1 < s
        omega
      · have hj : i.rev.1 < s := by omega
        have h5 := (hP i.rev (by omega)).2
        have e : T (b i.rev) - b i.rev = T (b' i) - b' i := by
          rw [h1 _ hj, Fin.rev_rev]
        rw [e] at h5
        rw [← hB]
        refine (spanC' (· < i.rev) _ (fun _ h => lt_trans (show _ < i.rev.1 from h) hj)).1 h5 l ?_
        show ¬ l.rev.1 < i.rev.1
        omega
  · rintro ⟨r1, r2, r3⟩
    refine ⟨fun j hj => ⟨?_, ?_⟩, fun j hj => ⟨?_, ?_⟩⟩
    · exact (spanC (· < j) _).2 fun i hi => by rw [hA]; exact r1 j hj i hi
    · by_cases hjs : j.1 < s
      · have e : T (b j) - b j = T (b' j.rev) - b' j.rev := by rw [h1 j hjs]
        rw [e]
        refine (spanC' (· < j) _ (fun _ h => lt_trans (show _ < j.1 from h) hjs)).2 fun l hl => ?_
        rw [hB]
        have hjr := Fin.val_rev j
        have hlr := Fin.val_rev l
        have hj2 := j.2
        have hl2 := l.2
        refine r3 j.rev (by omega) l ?_
        intro hlt
        apply hl
        show l.rev.1 < j.1
        have h6 : j.rev.1 < l.1 := hlt
        omega
      · rw [hz j (not_lt.1 hjs) hj]
        exact zero_mem _
    · exact (spanC (fun i => i.1 < s) _).2 fun i hi => by rw [hA]; exact r2 j hj i hi
    · have e : T (b j) - b j = -(T (b' j) - b' j) := by
        rw [h2 j hj, map_neg]
        abel
      rw [e, map_neg, Submodule.neg_mem_iff]
      refine (spanC' (fun i => i.1 < s) _ (fun _ h => h)).2 fun l hl => ?_
      rw [hB]
      refine r3 j (le_of_eq hj.symm) l ?_
      intro hlt
      apply hl
      show l.rev.1 < s
      have hlr := Fin.val_rev l
      have hl2 := l.2
      have h6 : j.1 < l.1 := hlt
      omega

/- English proof (translation)
Take `⟨w, hC, hw1⟩` from `exists_choice_of_idem g hg hne hrad hsp hf hcard ε e1 e2 e3`. Establish `hex : ∀ (q : Fin 2) (v : Fin f), ∃ u, IsConj I (w q v) u` using `fun q v => (extId_mul_sup_natCast_conj I).2.2.2.1 (w q v)`. Use `choose w' hw' using hex`. Establish `hgw : ∀ q v, ((g q : ℕ) : 𝓞 I.E) ∈ (w q v).asIdeal` using `fun q v => (hC.2.2.2.1 q v).1`. Establish `hgw' : ∀ q v, ((g q : ℕ) : 𝓞 I.E) ∈ (w' q v).asIdeal` using `fun q v => (hw' q v (g q) (g q) (by simp)).1 (hgw q v)`.

Establish `hfr : ∀ (q : Fin 2) (v : Fin f), ∃ (fr : PlFrame I N (g q) (w q v)) (fr' : PlFrame I N (g q) (w' q v)), (∀ j, fr.c (b j) = Pi.single j 1) ∧ (∀ j, fr'.c (b' j) = Pi.single j 1) ∧ (∀ a, fr'.r a = fr.r (sigI I a)) ∧ ∀ (x : I.Gf) (hx : x ∈ I.Kset) (M : GL (Fin N) (ZMod (g q))), fr.Ac …` using `fun q v => exists_frames hn (hg q) (hsp q _ (hgw q v)) (hsp q _ (hgw' q v)) (hw' q v) b b' (hb q _ (hgw q v) (hw1 q v))`. Use `choose fr fr' hfb hfb' hfr' hact using hfr`. Establish `hε : ∀ q v, (fr' q v).r ε = 0`. Introduce `q v`. Establish `h0 : (fr q v).r (1 - ε) = 0`.

Rewrite using `[← RingHom.mem_ker, PlFrame.ker_r]`. Conclude with `hw1 q v`. Rewrite `h0` using `[map_sub, map_one, sub_eq_zero]`. Rewrite using `[hfr' q v, ← one_mul ((fr q v).r (sigI I ε)), h0, ← map_mul, e2, map_zero]`. Take `⟨ρ, hρ⟩` from `exists_red_actsBy I N g (fun _ => Fin f) w fr hn hC`.

Establish `hm : 1 ≤ g 0 * g 1` using `Nat.mul_pos (hg 0).pos (hg 1).pos`. Establish `loc : ∀ (q : Fin 2) (v : Fin f) (x : I.Gf) (hx : x ∈ I.Kset), (((∀ j : Fin N, j.1 < s + k → (fr q v).c (latEnd hx (b j) - b j) ∈ Submodule.span (ZMod (g q)) ((fr q v).c '' (b '' {i | i < j})) ∧ (fr' q v).c (latEnd hx (b j) - b j) ∈ Submodule.span (ZMod (g q)) ((fr' q v).c '' (b ' …` using `fun q v x hx => local_iff hN (fr q v).c (fr' q v).c b b' (hfb q v) (hfb' q v) h1 h2 ε (hε q v) h3 (latEnd hx) (ρ.toFun x ⟨q, v⟩) (hact q v x hx _ (fun y h => hρ x hx q v y h))`. Use `vol_ratio_prod (fun _ => Fintype.card_fin f) ρ μf hm (fun _ => Formalism.MainNotions.StandardLattice.IsRowLev k s) K₂ ?_` and prove the remaining obligations. Introduce `x`. Rewrite using `[hK x]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, hA, hB⟩`. Use `⟨hx, fun q v => (loc q v x hx).1 ⟨fun j hj => ?_, fun j hj => ?_⟩⟩` and prove the remaining obligations. Conclude with `(cong_iff hC hw' fr fr' _ _).1 (hA j hj) q v`. Conclude with `(cong_iff hC hw' fr fr' _ _).1 (hB j hj) q v`.

Introduce and unpack `⟨hx, hP⟩`. Use `⟨hx, fun j hj => ?_, fun j hj => ?_⟩` and prove the remaining obligations. Conclude with `(cong_iff hC hw' fr fr' _ _).2 fun q v => ((loc q v x hx).2 (hP q v)).1 j hj`. Conclude with `(cong_iff hC hw' fr fr' _ _).2 fun q v => ((loc q v x hx).2 (hP q v)).2 j hj`.
-/
theorem vol_ratio_rows {N f k s : ℕ} (hN : N = s + k + 1 + s) (hn : I.n = N) (g : Fin 2 → ℕ)
    (hg : ∀ i, (g i).Prime) (hne : g 0 ≠ g 1) (hrad : ∀ i, (Ideal.span {((g i : ℕ) : 𝓞 I.E)}).IsRadical)
    (hsp : ∀ i (v : HeightOneSpectrum (𝓞 I.E)), ((g i : ℕ) : 𝓞 I.E) ∈ v.asIdeal → Ideal.absNorm v.asIdeal = g i)
    (hf : 0 < f) (hcard : ∀ i, {v : HeightOneSpectrum (𝓞 I.E) | ((g i : ℕ) : 𝓞 I.E) ∈ v.asIdeal}.ncard = 2 * f)
    (ε : IntAf I.F I.E) (e1 : ε * ε = ε) (e2 : ε * sigI I ε = 0)
    (e3 : ∀ i (v : HeightOneSpectrum (𝓞 I.E)), ((g i : ℕ) : 𝓞 I.E) ∈ v.asIdeal → 1 - ε - sigI I ε ∈ extId I v.asIdeal)
    (b b' : Fin N → I.Lf)
    (hb : ∀ l (v : HeightOneSpectrum (𝓞 I.E)), ((g l : ℕ) : 𝓞 I.E) ∈ v.asIdeal → 1 - ε ∈ extId I v.asIdeal →
      ∀ i j, hI (b' i) (b j) - (if i = j then 1 else 0) ∈ extId I v.asIdeal)
    (h1 : ∀ j : Fin N, j.1 < s → b j = b' j.rev) (h2 : ∀ j : Fin N, j.1 = s + k → b j = - b' j)
    (h3 : ∀ j : Fin N, s ≤ j.1 → j.1 < s + k → ε • b j = b j)
    (μf : Measure I.Gf) [μf.IsHaarMeasure] (K₂ : Set I.Gf)
    (hK : ∀ x, x ∈ K₂ ↔ ∃ hx : x ∈ I.Kset,
      (∀ j : Fin N, j.1 < s + k → ∃ t ∈ Submodule.span (IntAf I.F I.E) (b '' {i | i < j}), ∃ z ∈ I.Lf,
        (latEnd hx (b j) - b j).1 = t.1 + ((g 0 * g 1 : ℕ) : I.E ⊗[I.F] Af I.F) • z) ∧
      ∀ j : Fin N, j.1 = s + k → ∃ t ∈ Submodule.span (IntAf I.F I.E) (b '' {i | i.1 < s}), ∃ z ∈ I.Lf,
        (latEnd hx (b j) - b j).1 = t.1 + ((g 0 * g 1 : ℕ) : I.E ⊗[I.F] Af I.F) • z) :
    (μf I.Kset).toReal / (μf K₂).toReal =
      Formalism.MainNotions.StandardLattice.idxLoc (ZMod (g 0)) N (Formalism.MainNotions.StandardLattice.IsRowLev k s) ^ f *
        Formalism.MainNotions.StandardLattice.idxLoc (ZMod (g 1)) N (Formalism.MainNotions.StandardLattice.IsRowLev k s) ^ f := by
  obtain ⟨w, hC, hw1⟩ := exists_choice_of_idem g hg hne hrad hsp hf hcard ε e1 e2 e3
  have hex : ∀ (q : Fin 2) (v : Fin f), ∃ u, IsConj I (w q v) u := fun q v =>
    (extId_mul_sup_natCast_conj I).2.2.2.1 (w q v)
  choose w' hw' using hex
  have hgw : ∀ q v, ((g q : ℕ) : 𝓞 I.E) ∈ (w q v).asIdeal := fun q v => (hC.2.2.2.1 q v).1
  have hgw' : ∀ q v, ((g q : ℕ) : 𝓞 I.E) ∈ (w' q v).asIdeal := fun q v =>
    (hw' q v (g q) (g q) (by simp)).1 (hgw q v)
  have hfr : ∀ (q : Fin 2) (v : Fin f), ∃ (fr : PlFrame I N (g q) (w q v)) (fr' : PlFrame I N (g q) (w' q v)),
      (∀ j, fr.c (b j) = Pi.single j 1) ∧ (∀ j, fr'.c (b' j) = Pi.single j 1) ∧
      (∀ a, fr'.r a = fr.r (sigI I a)) ∧
      ∀ (x : I.Gf) (hx : x ∈ I.Kset) (M : GL (Fin N) (ZMod (g q))), fr.ActsAs x M →
        ∀ i j, fr.c (latEnd hx (b j)) i = M.1 i j ∧ fr'.c (latEnd hx (b' j)) i = (M⁻¹).1 j i :=
    fun q v => exists_frames hn (hg q) (hsp q _ (hgw q v)) (hsp q _ (hgw' q v)) (hw' q v) b b'
      (hb q _ (hgw q v) (hw1 q v))
  choose fr fr' hfb hfb' hfr' hact using hfr
  have hε : ∀ q v, (fr' q v).r ε = 0 := by
    intro q v
    have h0 : (fr q v).r (1 - ε) = 0 := by
      rw [← RingHom.mem_ker, PlFrame.ker_r]
      exact hw1 q v
    rw [map_sub, map_one, sub_eq_zero] at h0
    rw [hfr' q v, ← one_mul ((fr q v).r (sigI I ε)), h0, ← map_mul, e2, map_zero]
  obtain ⟨ρ, hρ⟩ := exists_red_actsBy I N g (fun _ => Fin f) w fr hn hC
  have hm : 1 ≤ g 0 * g 1 := Nat.mul_pos (hg 0).pos (hg 1).pos
  have loc : ∀ (q : Fin 2) (v : Fin f) (x : I.Gf) (hx : x ∈ I.Kset),
      (((∀ j : Fin N, j.1 < s + k →
        (fr q v).c (latEnd hx (b j) - b j) ∈ Submodule.span (ZMod (g q)) ((fr q v).c '' (b '' {i | i < j})) ∧
        (fr' q v).c (latEnd hx (b j) - b j) ∈ Submodule.span (ZMod (g q)) ((fr' q v).c '' (b '' {i | i < j}))) ∧
      ∀ j : Fin N, j.1 = s + k →
        (fr q v).c (latEnd hx (b j) - b j) ∈ Submodule.span (ZMod (g q)) ((fr q v).c '' (b '' {i | i.1 < s})) ∧
        (fr' q v).c (latEnd hx (b j) - b j) ∈ Submodule.span (ZMod (g q)) ((fr' q v).c '' (b '' {i | i.1 < s}))) ↔
      Formalism.MainNotions.StandardLattice.IsRowLev k s (ρ.toFun x ⟨q, v⟩ : GL (Fin N) (ZMod (g q))).1) := fun q v x hx =>
    local_iff hN (fr q v).c (fr' q v).c b b' (hfb q v) (hfb' q v) h1 h2 ε (hε q v) h3 (latEnd hx)
      (ρ.toFun x ⟨q, v⟩) (hact q v x hx _ (fun y h => hρ x hx q v y h))
  refine vol_ratio_prod (fun _ => Fintype.card_fin f) ρ μf hm (fun _ => Formalism.MainNotions.StandardLattice.IsRowLev k s) K₂ ?_
  intro x
  rw [hK x]
  constructor
  · rintro ⟨hx, hA, hB⟩
    refine ⟨hx, fun q v => (loc q v x hx).1 ⟨fun j hj => ?_, fun j hj => ?_⟩⟩
    · exact (cong_iff hC hw' fr fr' _ _).1 (hA j hj) q v
    · exact (cong_iff hC hw' fr fr' _ _).1 (hB j hj) q v
  · rintro ⟨hx, hP⟩
    refine ⟨hx, fun j hj => ?_, fun j hj => ?_⟩
    · exact (cong_iff hC hw' fr fr' _ _).2 fun q v => ((loc q v x hx).2 (hP q v)).1 j hj
    · exact (cong_iff hC hw' fr fr' _ _).2 fun q v => ((loc q v x hx).2 (hP q v)).2 j hj

end GlobalTheory.RowIndex
