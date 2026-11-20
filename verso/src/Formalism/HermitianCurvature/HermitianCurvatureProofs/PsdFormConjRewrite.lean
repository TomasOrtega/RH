import Formalism.HermitianCurvature.StatementJ

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate nonZeroDivisors

namespace Formalism.FourierDecayAlt.P.Jx1

/- English proof (translation)
Unfold `TB.PSDOn at h`. Rewrite `h` using `[Matrix.posSemidef_iff_dotProduct_mulVec]`. Take `⟨hH, hN⟩` from `h`. Use `⟨fun x hx y hy => ?_, fun a => ?_⟩` and prove the remaining obligations. Establish `e` using `hH.apply ⟨y, hy⟩ ⟨x, hx⟩`.

Simplify using `only [Matrix.of_apply] at e`. Use `show k x y = conj (k y x)`. Rewrite using `[← e]`. Simplify using the standard rewrite rules. Establish `hb` using `(Complex.le_def.mp (hN (fun i => conj (a i)))).1`.

Simplify using `only [Complex.zero_re] at hb`. Use `le_of_le_of_eq hb ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[Finset.sum_comm, ← Finset.sum_coe_sort F]`. Simplify using `only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_coe_sort F]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Complex.star_def, Complex.conj_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conv {α : Type} (F : Finset α) (k : α → α → ℂ) (h : TB.PSDOn F k) :
    TA.PSDOn F (fun x y => k y x) := by
  unfold TB.PSDOn at h
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at h
  obtain ⟨hH, hN⟩ := h
  refine ⟨fun x hx y hy => ?_, fun a => ?_⟩
  · have e := hH.apply ⟨y, hy⟩ ⟨x, hx⟩
    simp only [Matrix.of_apply] at e
    show k x y = conj (k y x)
    rw [← e]
    simp
  · have hb := (Complex.le_def.mp (hN (fun i => conj (a i)))).1
    simp only [Complex.zero_re] at hb
    refine le_of_le_of_eq hb ?_
    congr 1
    rw [Finset.sum_comm, ← Finset.sum_coe_sort F]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_coe_sort F]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Complex.star_def, Complex.conj_conj]
    ring

/- English proof (translation)
Unfold `AxiomsAgree`. Introduce `E W _ _ D hK hA2 hA13`. Unfold `TB.Data.KernelPSD at hK`. Unfold `TB.Data.KernelSupport at hA2`. Unfold `TB.Data.ThetaDomination at hA13`.

Establish `hlv : ∀ j (h : TB.Pt E), TA.IsPt j h → TB.level h = j`. Introduce `j h hh`. Use `first`. Consider the case `exact hh.1`. Consider the case `(have h0 := hh.1`.

Simplify `h0)` using `[TA.lvl, TB.level]`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `TA.AxK`. Conclude with `⟨D.K0, fun i _ P _ => conv P (D.Kr i) (hK.1 i P)⟩`. Unfold `TA.KernelSupport`.

Introduce `i s hs hsi hir h h' t t' hh hh' ht ht' hor`. Use `show D.Kr i (TA.ext h' s t') (TA.ext h s t) = 0`. Assume the negation of the conclusion as `hne`. Distinguish the cases in `htt : t' = t`. Substitute `htt` using the available equality.

Break down `hor with h1 | h1` into its components or cases. Conclude with `h1 (by simp)`. Conclude with `h1.2.2 rfl`. Take `⟨h1, h2⟩` from `hA2 i s hs hsi hir h' h t' t (hlv _ _ hh') (hlv _ _ hh) ht' ht htt hne`. Break down `hor with h3 | h3` into its components or cases.

Apply `h3 show 1 / t - 1 / t' ∈ D.Lap (i - s + 1) s` to reduce the goal to its premises. Establish `h4` using `neg_mem h2`. Simplify `h4` using `[one_div, neg_sub]`. Conclude with `h1 ⟨h3.1, h3.2.1⟩`. Unfold `TA.ThetaDomination`.

Introduce `i s hs hsi hir`. Take `⟨-, hC, hL, hS⟩` from `hA13 i s hs hsi hir`. Use `⟨fun t Hd _ => conv Hd _ (hK.2 i s t Hd), fun t l hl => ?_, fun t Hd ht hHd => ?_, fun R Hd hR hHd => ?_⟩` and prove the remaining obligations. Use `show (fun h h' => D.Th i s (t + l) h' h) = (fun h h' => D.Th i s t h' h)`. Establish `hl' : t + l - t ∈ D.La (i - s + 1) s`.

Rewrite using `[add_sub_cancel_left]`. Conclude with `hl`. Rewrite using `[hL (t + l) t hl']`. Conclude with `conv Hd _ (hC t ht Hd fun h hh => hlv _ _ (hHd h hh))`. Establish `h5` using `conv Hd _ (hS R hR Hd fun h hh => hlv _ _ (hHd h hh))`.

Establish `e : ((1 + D.e i : ℝ) : ℂ) = 1 + (D.e i : ℂ)` using `by push_cast; ring`. Use `show TA.PSDOn Hd (fun h h' => ((1 + D.e i : ℝ) : ℂ) * D.Kr (i - s) h' h - ∑ t ∈ R, D.Th i s t h' h)`. Rewrite using `[e]`. Conclude with `h5`. Unfold `TA.AxE`.

Introduce `i hi hir`. Conclude with `(hA13 i 1 le_rfl hi hir).1`.
-/
theorem t_AxiomsAgree : AxiomsAgree := by
  unfold AxiomsAgree
  intro E W _ _ D hK hA2 hA13
  unfold TB.Data.KernelPSD at hK
  unfold TB.Data.KernelSupport at hA2
  unfold TB.Data.ThetaDomination at hA13
  have hlv : ∀ j (h : TB.Pt E), TA.IsPt j h → TB.level h = j := by
    intro j h hh
    first
    | exact hh.1
    | (have h0 := hh.1
       simpa [TA.lvl, TB.level] using h0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold TA.AxK
    exact ⟨D.K0, fun i _ P _ => conv P (D.Kr i) (hK.1 i P)⟩
  · unfold TA.KernelSupport
    intro i s hs hsi hir h h' t t' hh hh' ht ht' hor
    show D.Kr i (TA.ext h' s t') (TA.ext h s t) = 0
    by_contra hne
    by_cases htt : t' = t
    · subst htt
      rcases hor with h1 | h1
      · exact h1 (by simp)
      · exact h1.2.2 rfl
    · obtain ⟨h1, h2⟩ := hA2 i s hs hsi hir h' h t' t (hlv _ _ hh') (hlv _ _ hh) ht' ht htt hne
      rcases hor with h3 | h3
      · apply h3
        show 1 / t - 1 / t' ∈ D.Lap (i - s + 1) s
        have h4 := neg_mem h2
        simpa [one_div, neg_sub] using h4
      · exact h1 ⟨h3.1, h3.2.1⟩
  · unfold TA.ThetaDomination
    intro i s hs hsi hir
    obtain ⟨-, hC, hL, hS⟩ := hA13 i s hs hsi hir
    refine ⟨fun t Hd _ => conv Hd _ (hK.2 i s t Hd), fun t l hl => ?_, fun t Hd ht hHd => ?_,
      fun R Hd hR hHd => ?_⟩
    · show (fun h h' => D.Th i s (t + l) h' h) = (fun h h' => D.Th i s t h' h)
      have hl' : t + l - t ∈ D.La (i - s + 1) s := by
        rw [add_sub_cancel_left]
        exact hl
      rw [hL (t + l) t hl']
    · exact conv Hd _ (hC t ht Hd fun h hh => hlv _ _ (hHd h hh))
    · have h5 := conv Hd _ (hS R hR Hd fun h hh => hlv _ _ (hHd h hh))
      have e : ((1 + D.e i : ℝ) : ℂ) = 1 + (D.e i : ℂ) := by push_cast; ring
      show TA.PSDOn Hd (fun h h' => ((1 + D.e i : ℝ) : ℂ) * D.Kr (i - s) h' h - ∑ t ∈ R, D.Th i s t h' h)
      rw [e]
      exact h5
  · unfold TA.AxE
    intro i hi hir
    exact (hA13 i 1 le_rfl hi hir).1

/- English proof (translation)
Establish `h : conj (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y) = ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y`. Simplify using `only [map_sum, map_mul, Complex.conj_conj]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_` and prove the remaining obligations. Rewrite using `[← hh v hv u hu]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `Complex.conj_eq_iff_im.mp h`.
-/
private theorem im_quadratic_form_eq_zero_of_hermitian {α : Type} (F : Finset α) (k : α → α → ℂ)
    (hh : ∀ x ∈ F, ∀ y ∈ F, k y x = conj (k x y)) (a : α → ℂ) :
    (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y).im = 0 := by
  have h : conj (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y) =
      ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y := by
    simp only [map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_
    rw [← hh v hv u hu]
    ring
  exact Complex.conj_eq_iff_im.mp h

/- English proof (translation)
Unfold `TB.PSDOn`. Rewrite using `[Matrix.posSemidef_iff_dotProduct_mulVec]`. Use `⟨?_, fun x => ?_⟩` and prove the remaining obligations. Use `Matrix.IsHermitian.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.of_apply]`.

Rewrite using `[h.1 i i.2 j j.2]`. Simplify using the standard rewrite rules. Use `set a : α → ℂ := fun u => if hu : u ∈ F then x ⟨u, hu⟩ else 0 with ha`. Establish `hQ : star x ⬝ᵥ (Matrix.of fun u v : F => k u v).mulVec x = ∑ u ∈ F, ∑ v ∈ F, conj (a u) * k u v * a v`. Rewrite using `[← Finset.sum_coe_sort F]`.

Simplify using `only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_coe_sort F]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[ha, Complex.star_def, mul_assoc]`.

Rewrite using `[hQ, Complex.le_def]`. Simplify using `only [Complex.zero_re, Complex.zero_im]`. Conclude with `⟨h.2 a, (im_quadratic_form_eq_zero_of_hermitian F k h.1 a).symm⟩`.
-/
private theorem tb_psdOn_of_ta_psdOn {α : Type} (F : Finset α) (k : α → α → ℂ) (h : TA.PSDOn F k) :
    TB.PSDOn F k := by
  classical
  unfold TB.PSDOn
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.of_apply]
    rw [h.1 i i.2 j j.2]
    simp
  · set a : α → ℂ := fun u => if hu : u ∈ F then x ⟨u, hu⟩ else 0 with ha
    have hQ : star x ⬝ᵥ (Matrix.of fun u v : F => k u v).mulVec x =
        ∑ u ∈ F, ∑ v ∈ F, conj (a u) * k u v * a v := by
      rw [← Finset.sum_coe_sort F]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_coe_sort F]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [ha, Complex.star_def, mul_assoc]
    rw [hQ, Complex.le_def]
    simp only [Complex.zero_re, Complex.zero_im]
    exact ⟨h.2 a, (im_quadratic_form_eq_zero_of_hermitian F k h.1 a).symm⟩

/- English proof (translation)
Unfold `PSDTranspose`. Introduce `α F k h`. Conclude with `tb_psdOn_of_ta_psdOn F _ (conv F k h)`.
-/
theorem t_PSDTranspose : PSDTranspose := by
  unfold PSDTranspose
  intro α F k h
  exact tb_psdOn_of_ta_psdOn F _ (conv F k h)

section Tower
variable {E : Type} [Field E]

def Cnd (Sg : ℕ → ℕ → Finset E) (p : TB.Pt E) : Prop :=
  ∀ k (hk : k < p.length), 1 ≤ (p[k]'hk).1 ∧ (p[k]'hk).2 ∈ Sg (TB.blockStart p k) (p[k]'hk).1

/- English proof (translation)
Use `first`. Consider the case `(simp only [TB.blockStart, List.take_append_of_le_length hk.le]; done)`. Consider the case `(simp [TB.blockStart, List.take_append, hk.le]; done)`. Consider the case `simp [TB.blockStart, List.take_append_eq_append_take, Nat.sub_eq_zero_of_le hk.le]`.
-/
theorem bs_left (h : TB.Pt E) (s : ℕ) (t : E) (k : ℕ) (hk : k < h.length) :
    TB.blockStart (h ++ [(s, t)]) k = TB.blockStart h k := by
  first
  | (simp only [TB.blockStart, List.take_append_of_le_length hk.le]; done)
  | (simp [TB.blockStart, List.take_append, hk.le]; done)
  | simp [TB.blockStart, List.take_append_eq_append_take, Nat.sub_eq_zero_of_le hk.le]

/- English proof (translation)
Use `first`. Consider the case `(simp [TB.blockStart, TB.level]; done)`. Consider the case `(simp [TB.blockStart, TB.level, List.take_left']; done)`. Consider the case `simp [TB.blockStart, TB.level, List.take_append_eq_append_take]`.
-/
theorem bs_last (h : TB.Pt E) (s : ℕ) (t : E) :
    TB.blockStart (h ++ [(s, t)]) h.length = TB.level h + 1 := by
  first
  | (simp [TB.blockStart, TB.level]; done)
  | (simp [TB.blockStart, TB.level, List.take_left']; done)
  | simp [TB.blockStart, TB.level, List.take_append_eq_append_take]

/- English proof (translation)
Unfold `Cnd`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Use `⟨fun k hk => ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `H1` using `H k (by simp; omega)`.

Simplify using `only [List.getElem_append_left hk, bs_left h s t k hk] at H1`. Conclude with `H1`. Establish `H1` using `H h.length (by simp)`. Simplify using `only [List.getElem_append_right (le_refl _), Nat.sub_self] at H1`. Simplify using `using H1.1`.

Establish `H1` using `H h.length (by simp)`. Simplify using `only [List.getElem_append_right (le_refl _), Nat.sub_self, bs_last] at H1`. Simplify using `using H1.2`. Introduce and unpack `⟨H, h1, h2⟩ k hk`. Establish `hk' : k < h.length + 1` using `by simpa using hk`.

Break down `Nat.lt_or_ge k h.length with hlt | hge` into its components or cases. Simplify using `only [List.getElem_append_left hlt, bs_left h s t k hlt]`. Conclude with `H k hlt`. Establish `hkl : k = h.length` using `by omega`. Substitute `hkl` using the available equality.

Simplify using `only [List.getElem_append_right (le_refl _), Nat.sub_self, bs_last]`. Simplify using `using ⟨h1, h2⟩`.
-/
theorem cnd_append (Sg : ℕ → ℕ → Finset E) (h : TB.Pt E) (s : ℕ) (t : E) :
    Cnd Sg (h ++ [(s, t)]) ↔ Cnd Sg h ∧ 1 ≤ s ∧ t ∈ Sg (TB.level h + 1) s := by
  unfold Cnd
  constructor
  · intro H
    refine ⟨fun k hk => ?_, ?_, ?_⟩
    · have H1 := H k (by simp; omega)
      simp only [List.getElem_append_left hk, bs_left h s t k hk] at H1
      exact H1
    · have H1 := H h.length (by simp)
      simp only [List.getElem_append_right (le_refl _), Nat.sub_self] at H1
      simpa using H1.1
    · have H1 := H h.length (by simp)
      simp only [List.getElem_append_right (le_refl _), Nat.sub_self, bs_last] at H1
      simpa using H1.2
  · rintro ⟨H, h1, h2⟩ k hk
    have hk' : k < h.length + 1 := by simpa using hk
    rcases Nat.lt_or_ge k h.length with hlt | hge
    · simp only [List.getElem_append_left hlt, bs_left h s t k hlt]
      exact H k hlt
    · have hkl : k = h.length := by omega
      subst hkl
      simp only [List.getElem_append_right (le_refl _), Nat.sub_self, bs_last]
      simpa using ⟨h1, h2⟩

/- English proof (translation)
Simplify using `[TB.level]`.
-/
theorem level_append (h : TB.Pt E) (s : ℕ) (t : E) : TB.level (h ++ [(s, t)]) = TB.level h + s := by
  simp [TB.level]

/- English proof (translation)
It suffices to establish `HH : ∀ n (p : TB.Pt E), p ∈ TA.PT (fun j s => Sg (j - s + 1) s) n ↔ TB.level p = n ∧ Cnd Sg p from fun n => HH n p`. Introduce `n`. Use `Nat.strong_induction_on n (fun n ih => ?_)` and prove the remaining obligations. Introduce `p`. Consider the cases of `n with`.

Consider the case `zero`. Rewrite using `[TA.PT]`. Simplify using `only [Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`.

Conclude with `⟨rfl, fun k hk => absurd hk (by simp)⟩`. Introduce and unpack `⟨hl, hc⟩`. Take `rfl | ⟨h, ⟨s, t⟩, hp⟩` from `List.eq_nil_or_concat p`. Both sides reduce to the same expression. Apply the tactic sequence `exfalso try rw [List.concat_eq_append] at hp`.

Substitute `hp` using the available equality. Take `⟨-, hs, -⟩` from `(cnd_append Sg h s t).mp hc`. Rewrite `hl` using `[level_append]`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n`.

Rewrite using `[TA.PT]`. Simplify using `only [Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists, Finset.mem_range, Finset.mem_image, TA.ext]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm, h, hh, t, ht, rfl⟩`. Take `⟨hl, hc⟩` from `(ih m hm h).mp hh`.

Establish `e : n + 1 - (n + 1 - m) + 1 = m + 1` using `by omega`. Rewrite `ht` using `[e]`. Use `⟨?_, (cnd_append Sg h _ t).mpr ⟨hc, by omega, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[level_append, hl]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hl]`. Conclude with `ht`. Introduce and unpack `⟨hl, hc⟩`. Take `rfl | ⟨h, ⟨s, t⟩, hp⟩` from `List.eq_nil_or_concat p`. Simplify using `[TB.level] at hl`.

Apply the tactic sequence `try rw [List.concat_eq_append] at hp`. Substitute `hp` using the available equality. Take `⟨hc', hs, ht⟩` from `(cnd_append Sg h s t).mp hc`. Rewrite `hl` using `[level_append]`. Establish `hm : TB.level h < n + 1` using `by omega`.

Establish `e1 : n + 1 - TB.level h = s` using `by omega`. Establish `e2 : n + 1 - s + 1 = TB.level h + 1` using `by omega`. Use `⟨TB.level h, hm, h, (ih _ hm h).mpr ⟨rfl, hc'⟩, t, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e1, e2]`. Conclude with `ht`.

Rewrite using `[e1]`.
-/
theorem pt_iff [DecidableEq E] (Sg : ℕ → ℕ → Finset E) (p : TB.Pt E) :
    ∀ n, p ∈ TA.PT (fun j s => Sg (j - s + 1) s) n ↔ TB.level p = n ∧ Cnd Sg p := by
  suffices HH : ∀ n (p : TB.Pt E), p ∈ TA.PT (fun j s => Sg (j - s + 1) s) n ↔ TB.level p = n ∧ Cnd Sg p from
    fun n => HH n p
  intro n
  refine Nat.strong_induction_on n (fun n ih => ?_)
  intro p
  cases n with
  | zero =>
    rw [TA.PT]
    simp only [Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨rfl, fun k hk => absurd hk (by simp)⟩
    · rintro ⟨hl, hc⟩
      obtain rfl | ⟨h, ⟨s, t⟩, hp⟩ := List.eq_nil_or_concat p
      · rfl
      · exfalso
        try rw [List.concat_eq_append] at hp
        subst hp
        obtain ⟨-, hs, -⟩ := (cnd_append Sg h s t).mp hc
        rw [level_append] at hl
        omega
  | succ n =>
    rw [TA.PT]
    simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists, Finset.mem_range,
      Finset.mem_image, TA.ext]
    constructor
    · rintro ⟨m, hm, h, hh, t, ht, rfl⟩
      obtain ⟨hl, hc⟩ := (ih m hm h).mp hh
      have e : n + 1 - (n + 1 - m) + 1 = m + 1 := by omega
      rw [e] at ht
      refine ⟨?_, (cnd_append Sg h _ t).mpr ⟨hc, by omega, ?_⟩⟩
      · rw [level_append, hl]
        omega
      · rw [hl]
        exact ht
    · rintro ⟨hl, hc⟩
      obtain rfl | ⟨h, ⟨s, t⟩, hp⟩ := List.eq_nil_or_concat p
      · simp [TB.level] at hl
      · try rw [List.concat_eq_append] at hp
        subst hp
        obtain ⟨hc', hs, ht⟩ := (cnd_append Sg h s t).mp hc
        rw [level_append] at hl
        have hm : TB.level h < n + 1 := by omega
        have e1 : n + 1 - TB.level h = s := by omega
        have e2 : n + 1 - s + 1 = TB.level h + 1 := by omega
        refine ⟨TB.level h, hm, h, (ih _ hm h).mpr ⟨rfl, hc'⟩, t, ?_, ?_⟩
        · rw [e1, e2]
          exact ht
        · rw [e1]

/- English proof (translation)
Unfold `TowersAgree`. Introduce `E _ _ T i`. Use extensionality with `p`. Rewrite using `[pt_iff T.Sg p i]`. Conclude with `T.isTower i p`.
-/
theorem t_TowersAgree : TowersAgree := by
  unfold TowersAgree
  intro E _ _ T i
  ext p
  rw [pt_iff T.Sg p i]
  exact T.isTower i p

end Tower

/- English proof (translation)
Unfold `FormsAgree`. Introduce `E W _ _ D H _ _ Φ T ε i w hw hg`. Unfold `TB.Data.Q TB.Data.Sf TA.Slev TA.gram`. Rewrite using `[t_TowersAgree E T i]`. Use `set X := TA.PT (fun j s => T.Sg (j - s + 1) s) i with hX`.

Establish `hS : (∑ p ∈ X, ∑ q ∈ X, D.Kr i p q * D.gram ε i w p q) = (D.wt w : ℂ) * ∑ p ∈ X, ∑ p' ∈ X, (toTA D).K i p p' * inner ℂ (Φ w p) (Φ w p')`. Rewrite using `[Finset.mul_sum, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Rewrite using `[hg]`. Simplify using `only [toTA]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hS, Complex.re_ofReal_mul]`. Use `first`.

Consider the case `exact mul_div_cancel_left₀ _ hw`. Consider the case `field_simp`.
-/
theorem t_FormsAgree : FormsAgree := by
  unfold FormsAgree
  intro E W _ _ D H _ _ Φ T ε i w hw hg
  unfold TB.Data.Q TB.Data.Sf TA.Slev TA.gram
  rw [t_TowersAgree E T i]
  set X := TA.PT (fun j s => T.Sg (j - s + 1) s) i with hX
  have hS : (∑ p ∈ X, ∑ q ∈ X, D.Kr i p q * D.gram ε i w p q) =
      (D.wt w : ℂ) * ∑ p ∈ X, ∑ p' ∈ X, (toTA D).K i p p' * inner ℂ (Φ w p) (Φ w p') := by
    rw [Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hg]
    simp only [toTA]
    ring
  rw [hS, Complex.re_ofReal_mul]
  first
  | exact mul_div_cancel_left₀ _ hw
  | field_simp

section Agree
variable {α : Type}

/- English proof (translation)
Establish `h : conj (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y) = ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y`. Simplify using `only [map_sum, map_mul, Complex.conj_conj]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_` and prove the remaining obligations. Rewrite using `[← hh v hv u hu]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `Complex.conj_eq_iff_im.mp h`.
-/
theorem q_im (F : Finset α) (k : α → α → ℂ) (hh : ∀ x ∈ F, ∀ y ∈ F, k y x = conj (k x y)) (a : α → ℂ) :
    (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y).im = 0 := by
  have h : conj (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y) =
      ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y := by
    simp only [map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_
    rw [← hh v hv u hu]
    ring
  exact Complex.conj_eq_iff_im.mp h

/- English proof (translation)
Conclude with `tb_psdOn_of_ta_psdOn F k h`.
-/
theorem ta_to_tb (F : Finset α) (k : α → α → ℂ) (h : TA.PSDOn F k) : TB.PSDOn F k := by
  exact tb_psdOn_of_ta_psdOn F k h

/- English proof (translation)
Use `Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Simplify using `only [Complex.conj_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psd_form_conj_rewrite (F : Finset α) (k : α → α → ℂ) (a : α → ℂ) :
    (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y) =
      ∑ x ∈ F, ∑ y ∈ F, conj ((fun z => conj (a z)) x) * k x y * (fun z => conj (a z)) y := by
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [Complex.conj_conj]
  ring

/- English proof (translation)
Introduce `x hx y hy`. Use `set B : (α → ℂ) → (α → ℂ) → ℂ := fun a b => ∑ u ∈ F, ∑ v ∈ F, a u * conj (b v) * k u v with hB`. Establish `hS : ∀ a, (B a a).im = 0` using `fun a => (h a).1`. Establish `hexp : ∀ a b, B (a + b) (a + b) = B a a + B b b + (B a b + B b a)`. Introduce `a b`.

Simplify using `only [hB, Pi.add_apply, map_add, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hpol : ∀ a b, (B a b + B b a).im = 0`. Introduce `a b`.

Establish `h0` using `hS (a + b)`. Rewrite `h0` using `[hexp, Complex.add_im, Complex.add_im, hS a, hS b]`. Simplify using `using h0`. Establish `hsc1 : ∀ (c : ℂ) a b, B (c • a) b = c * B a b`. Introduce `c a b`.

Simplify using `only [hB, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hsc2 : ∀ (c : ℂ) a b, B a (c • b) = conj c * B a b`. Introduce `c a b`.

Simplify using `only [hB, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hBe : ∀ p q, p ∈ F → q ∈ F → B (fun u => if u = p then 1 else 0) (fun u => if u = q then 1 else 0) = k p q`. Introduce `p q hp hq`.

Simplify using `[hB, apply_ite (starRingEnd ℂ), ite_mul, hp, hq]`. Establish `h1` using `hpol (fun u => if u = x then 1 else 0) (fun u => if u = y then 1 else 0)`. Establish `h2` using `hpol (fun u => if u = x then 1 else 0) (Complex.I • fun u => if u = y then 1 else 0)`. Rewrite `h2` using `[hsc2, hsc1]`. Rewrite `h1`, `h2` using `[hBe x y hx hy, hBe y x hy hx]`.

Apply the tactic sequence `apply Complex.ext <;> simp [Complex.mul_im] at h1 h2 ⊢ <;> linarith`.
-/
theorem psd_kernel_hermitian (F : Finset α) (k : α → α → ℂ) (h : A5.IsPSD F k) :
    ∀ x ∈ F, ∀ y ∈ F, k y x = conj (k x y) := by
  classical
  intro x hx y hy
  set B : (α → ℂ) → (α → ℂ) → ℂ := fun a b => ∑ u ∈ F, ∑ v ∈ F, a u * conj (b v) * k u v with hB
  have hS : ∀ a, (B a a).im = 0 := fun a => (h a).1
  have hexp : ∀ a b, B (a + b) (a + b) = B a a + B b b + (B a b + B b a) := by
    intro a b
    simp only [hB, Pi.add_apply, map_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  have hpol : ∀ a b, (B a b + B b a).im = 0 := by
    intro a b
    have h0 := hS (a + b)
    rw [hexp, Complex.add_im, Complex.add_im, hS a, hS b] at h0
    simpa using h0
  have hsc1 : ∀ (c : ℂ) a b, B (c • a) b = c * B a b := by
    intro c a b
    simp only [hB, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  have hsc2 : ∀ (c : ℂ) a b, B a (c • b) = conj c * B a b := by
    intro c a b
    simp only [hB, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  have hBe : ∀ p q, p ∈ F → q ∈ F →
      B (fun u => if u = p then 1 else 0) (fun u => if u = q then 1 else 0) = k p q := by
    intro p q hp hq
    simp [hB, apply_ite (starRingEnd ℂ), ite_mul, hp, hq]
  have h1 := hpol (fun u => if u = x then 1 else 0) (fun u => if u = y then 1 else 0)
  have h2 := hpol (fun u => if u = x then 1 else 0) (Complex.I • fun u => if u = y then 1 else 0)
  rw [hsc2, hsc1] at h2
  rw [hBe x y hx hy, hBe y x hy hx] at h1 h2
  apply Complex.ext <;> simp [Complex.mul_im] at h1 h2 ⊢ <;> linarith

/- English proof (translation)
Unfold `PSDAgree`. Introduce `α F k`. Use `⟨⟨fun h => conv F _ (t_PSDTranspose α F k h), ta_to_tb F k⟩, ⟨fun h => ⟨psd_kernel_hermitian F k h, fun a => ?_⟩, fun h => ?_⟩⟩` and prove the remaining obligations. Establish `h2` using `(h (fun z => conj (a z))).2`. Use `le_of_le_of_eq h2 ?_` and prove the remaining obligations.

Use `congr 1`. Use `Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Simplify using `only [Complex.conj_conj]`. Expand and normalize the polynomial expressions, which then agree. Introduce `a`.

Rewrite using `[psd_form_conj_rewrite F k a]`. Conclude with `⟨q_im F k h.1 _, h.2 _⟩`.
-/
theorem t_PSDAgree : PSDAgree := by
  unfold PSDAgree
  intro α F k
  refine ⟨⟨fun h => conv F _ (t_PSDTranspose α F k h), ta_to_tb F k⟩, ⟨fun h => ⟨psd_kernel_hermitian F k h, fun a => ?_⟩, fun h => ?_⟩⟩
  · have h2 := (h (fun z => conj (a z))).2
    refine le_of_le_of_eq h2 ?_
    congr 1
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [Complex.conj_conj]
    ring
  · intro a
    rw [psd_form_conj_rewrite F k a]
    exact ⟨q_im F k h.1 _, h.2 _⟩

end Agree

/- English proof (translation)
Unfold `MajIsProf`. Introduce `E W _ _ D e hP ρ l`. Unfold `TB.Data.maj prof`. Use `Fintype.prod_equiv e _ _ (fun v => ?_)` and prove the remaining obligations. Simplify using `only [hP v l, Equiv.symm_apply_apply]`.
-/
theorem t_MajIsProf : MajIsProf := by
  unfold MajIsProf
  intro E W _ _ D e hP ρ l
  unfold TB.Data.maj prof
  refine Fintype.prod_equiv e _ _ (fun v => ?_)
  simp only [hP v l, Equiv.symm_apply_apply]

/- English proof (translation)
Unfold `BoxSumLattice`. Introduce `hB`. Unfold `Formalism.SA.C.BoxSum at hB`. Take `⟨C₀, hC₀⟩` from `hB`. Use `⟨max 1 |C₀|, le_max_left _ _, ?_⟩` and prove the remaining obligations.

Introduce `E _ _ _ aa L x K Θ a haa hL hx hK ha hΘ hprod`. Establish `hΘpos : 0 < Θ` using `by linarith`. Establish `hapos : 0 < a` using `by linarith`. Establish `hd0 : 0 < Fintype.card (InfinitePlace E)` using `Fintype.card_pos`. Establish `wnn : ∀ (w : InfinitePlace E) (l : E), 0 ≤ w l`.

Introduce `w l`. Use `first`. Consider the case `positivity`. Consider the case `exact w.nonneg l`. Consider the case `exact apply_nonneg w l`.

Establish `hNq : (0 : ℝ) < (FractionalIdeal.absNorm aa : ℝ)` using `by first`. Consider the case `(have h1 : FractionalIdeal.absNorm aa ≠ 0 := by`. Simplify `haa` using `[FractionalIdeal.absNorm_eq_zero_iff]`. Establish `h2 : (0 : ℚ) ≤ FractionalIdeal.absNorm aa` using `FractionalIdeal.absNorm_nonneg aa`. Conclude with `lt_of_le_of_ne h2 (Ne.symm h1))` after adjusting the coercions.

Consider the case `exact_mod_cast FractionalIdeal.absNorm_pos_iff.mpr haa`. Establish `hNpos : 0 < √(FractionalIdeal.absNorm aa : ℝ)` using `Real.sqrt_pos.mpr hNq`. Use `set T : ℝ := (a / Θ) ^ Fintype.card (InfinitePlace E) * √(FractionalIdeal.absNorm aa : ℝ) with hT`. Establish `hTpos : 0 < T` using `mul_pos (pow_pos (div_pos hapos hΘpos) _) hNpos`. Choose the witnesses or unpack the hypotheses as in `⟨y, hxy, hy0, hyT⟩ : ∃ y : InfinitePlace E → ℝ, (∀ w, x w ≤ y w) ∧ (∀ w, 0 < y w) ∧ ∏ w, y w ≤ T := by`.

Distinguish the cases in `hpos : ∀ w, 0 < x w`. Conclude with `⟨x, fun _ => le_rfl, hpos, hprod⟩`. Use `push_neg at hpos`. Take `⟨w₀, hw₀⟩` from `hpos`. Establish `hxw0 : x w₀ = 0` using `le_antisymm hw₀ (hx w₀)`.

Use `set M : ℝ := 1 + ∑ w, x w with hM`. Establish `hsum0 : 0 ≤ ∑ w, x w` using `Finset.sum_nonneg fun w _ => hx w`. Establish `hM1 : 1 ≤ M` using `by linarith`. Establish `hMpos : 0 < M` using `by linarith`. Use `set ε : ℝ := min 1 (T / M ^ Fintype.card (InfinitePlace E)) with hε`.

Establish `hεpos : 0 < ε` using `lt_min one_pos (div_pos hTpos (pow_pos hMpos _))`. Use `⟨fun w => max (x w) ε, fun w => le_max_left _ _, fun w => lt_of_lt_of_le hεpos (le_max_right _ _), ?_⟩` and prove the remaining obligations. Establish `hcomp : ∏ w ∈ ({w₀}ᶜ : Finset (InfinitePlace E)), max (x w) ε ≤ M ^ Fintype.card (InfinitePlace E)`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.prod_le_prod (fun w _ => le_trans hεpos.le (le_max_right _ _))` to reduce the goal to its premises.

Introduce `w _`. Apply `max_le` to reduce the goal to its premises. Establish `h3 : x w ≤ ∑ v, x v` using `Finset.single_le_sum (fun v _ => hx v) (Finset.mem_univ w)`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `le_trans (min_le_left _ _) hM1`.

Use `_ = M ^ ({w₀}ᶜ : Finset (InfinitePlace E)).card := Finset.prod_const M`. Use `_ ≤ M ^ Fintype.card (InfinitePlace E) := pow_le_pow_right₀ hM1 (Finset.card_le_univ _)`. Use `show ∏ w, max (x w) ε ≤ T`. Rewrite using `[Fintype.prod_eq_mul_prod_compl w₀, hxw0, max_eq_right hεpos.le]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hPpos : 0 < ∏ w, y w` using `Finset.prod_pos fun w _ => hy0 w`. Establish `hQpos : 0 < √(FractionalIdeal.absNorm aa : ℝ) / ∏ w, y w` using `div_pos hNpos hPpos`. Use `set Θ' : ℝ := (√(FractionalIdeal.absNorm aa : ℝ) / ∏ w, y w) ^ ((1 : ℝ) / Fintype.card (InfinitePlace E)) with hΘ'`. Establish `hΘ'nn : 0 ≤ Θ'` using `Real.rpow_nonneg hQpos.le _`. Establish `hΘ'd : Θ' ^ Fintype.card (InfinitePlace E) = √(FractionalIdeal.absNorm aa : ℝ) / ∏ w, y w`.

Rewrite using `[hΘ', ← Real.rpow_natCast, ← Real.rpow_mul hQpos.le]`. Establish `hdr : ((1 : ℝ) / Fintype.card (InfinitePlace E)) * (Fintype.card (InfinitePlace E) : ℝ) = 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hdr, Real.rpow_one]`. Establish `hΘ'ge : Θ / a ≤ Θ'`.

Establish `h1 : (Θ / a) ^ Fintype.card (InfinitePlace E) ≤ Θ' ^ Fintype.card (InfinitePlace E)`. Rewrite using `[hΘ'd, le_div_iff₀ hPpos]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hT, ← mul_assoc, ← mul_pow]`. Establish `hone : Θ / a * (a / Θ) = 1` using `by field_simp`.

Rewrite using `[hone, one_pow, one_mul]`. Use `first`. Consider the case `exact le_of_pow_le_pow_left₀ hd0.ne' hΘ'nn h1`. Consider the case `exact (pow_le_pow_iff_left₀ (div_pos hΘpos hapos).le hΘ'nn hd0.ne').mp h1`. Establish `hΘ'2 : 2 < Θ'` using `lt_of_lt_of_le (by rw [lt_div_iff₀ hapos]; linarith) hΘ'ge`.

Establish `hK3 : (3 : ℝ) ≤ (K : ℝ)` using `by exact_mod_cast hK`. Establish `hbox` using `hC₀ E aa haa y Θ' (K : ℝ) hy0 hΘ'2 hK3 hΘ'd`. Unfold `TA.LatSum`. Prove the components needed by the constructor for the conclusion. Introduce `l`.

Unfold `prof`. Conclude with `Finset.prod_nonneg fun w _ => le_min zero_le_one (pow_nonneg (div_nonneg (hx w) (wnn w l)) _)`. Introduce `S hS`. Establish `hS' : ∀ l ∈ S, l ∈ aa ∧ l ≠ 0` using `fun l hl => ⟨hL l (hS l hl).1, (hS l hl).2⟩`. Establish `h1` using `hbox S hS'`.

Establish `hs : 0 < (K : ℝ) - 5 / 2` using `by linarith`. Establish `ht0 : 0 ≤ Θ' ^ (-((K : ℝ) - 5 / 2))` using `Real.rpow_nonneg hΘ'nn _`. Establish `htle : Θ' ^ (-((K : ℝ) - 5 / 2)) ≤ a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))`. Establish `hta : 0 < Θ / a` using `div_pos hΘpos hapos`. Rewrite using `[Real.rpow_neg hΘ'nn, Real.rpow_neg hΘpos.le]`.

Establish `h2 : (Θ / a) ^ ((K : ℝ) - 5 / 2) ≤ Θ' ^ ((K : ℝ) - 5 / 2)` using `Real.rpow_le_rpow hta.le hΘ'ge hs.le`. Establish `h3 : (Θ' ^ ((K : ℝ) - 5 / 2))⁻¹ ≤ ((Θ / a) ^ ((K : ℝ) - 5 / 2))⁻¹` using `inv_anti₀ (Real.rpow_pos_of_pos hta _) h2`. Use `le_trans h3 (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Real.div_rpow hΘpos.le hapos.le, inv_div, div_eq_mul_inv]`. Combine the equalities or inequalities in the displayed calculation.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `l _`. Unfold `prof`. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `w _`.

Conclude with `le_min zero_le_one (pow_nonneg (div_nonneg (hx w) (wnn w l)) _)`. Introduce `w _`. Rewrite using `[Real.rpow_natCast]`. Apply `min_le_min_left` to reduce the goal to its premises. Conclude with `pow_le_pow_left₀ (div_nonneg (hx w) (wnn w l)) (div_le_div_of_nonneg_right (hxy w) (wnn w l)) _`.

Use `_ ≤ (C₀ * Θ' ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E) := h1`. Use `_ ≤ (|C₀| * Θ' ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E) := by`. Establish `e : (|C₀| * Θ' ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E) = |(C₀ * Θ' ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E)|`. Rewrite using `[abs_pow, abs_mul, abs_of_nonneg ht0]`. Rewrite using `[e]`.

Conclude with `le_abs_self _`. Use `_ ≤ (max 1 |C₀| * a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E) := by`. Apply `pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) ht0)` to reduce the goal to its premises. Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul (le_max_right _ _) htle ht0 (le_trans zero_le_one (le_max_left _ _))`.
-/
theorem t_BoxSumLattice : BoxSumLattice := by
  classical
  unfold BoxSumLattice
  intro hB
  unfold Formalism.SA.C.BoxSum at hB
  obtain ⟨C₀, hC₀⟩ := hB
  refine ⟨max 1 |C₀|, le_max_left _ _, ?_⟩
  intro E _ _ _ aa L x K Θ a haa hL hx hK ha hΘ hprod
  have hΘpos : 0 < Θ := by linarith
  have hapos : 0 < a := by linarith
  have hd0 : 0 < Fintype.card (InfinitePlace E) := Fintype.card_pos
  have wnn : ∀ (w : InfinitePlace E) (l : E), 0 ≤ w l := by
    intro w l
    first
    | positivity
    | exact w.nonneg l
    | exact apply_nonneg w l
  have hNq : (0 : ℝ) < (FractionalIdeal.absNorm aa : ℝ) := by
    first
    | (have h1 : FractionalIdeal.absNorm aa ≠ 0 := by
         simpa [FractionalIdeal.absNorm_eq_zero_iff] using haa
       have h2 : (0 : ℚ) ≤ FractionalIdeal.absNorm aa := FractionalIdeal.absNorm_nonneg aa
       exact_mod_cast lt_of_le_of_ne h2 (Ne.symm h1))
    | exact_mod_cast FractionalIdeal.absNorm_pos_iff.mpr haa
  have hNpos : 0 < √(FractionalIdeal.absNorm aa : ℝ) := Real.sqrt_pos.mpr hNq
  set T : ℝ := (a / Θ) ^ Fintype.card (InfinitePlace E) * √(FractionalIdeal.absNorm aa : ℝ) with hT
  have hTpos : 0 < T := mul_pos (pow_pos (div_pos hapos hΘpos) _) hNpos
  obtain ⟨y, hxy, hy0, hyT⟩ : ∃ y : InfinitePlace E → ℝ, (∀ w, x w ≤ y w) ∧ (∀ w, 0 < y w) ∧
      ∏ w, y w ≤ T := by
    by_cases hpos : ∀ w, 0 < x w
    · exact ⟨x, fun _ => le_rfl, hpos, hprod⟩
    · push_neg at hpos
      obtain ⟨w₀, hw₀⟩ := hpos
      have hxw0 : x w₀ = 0 := le_antisymm hw₀ (hx w₀)
      set M : ℝ := 1 + ∑ w, x w with hM
      have hsum0 : 0 ≤ ∑ w, x w := Finset.sum_nonneg fun w _ => hx w
      have hM1 : 1 ≤ M := by linarith
      have hMpos : 0 < M := by linarith
      set ε : ℝ := min 1 (T / M ^ Fintype.card (InfinitePlace E)) with hε
      have hεpos : 0 < ε := lt_min one_pos (div_pos hTpos (pow_pos hMpos _))
      refine ⟨fun w => max (x w) ε, fun w => le_max_left _ _,
        fun w => lt_of_lt_of_le hεpos (le_max_right _ _), ?_⟩
      have hcomp : ∏ w ∈ ({w₀}ᶜ : Finset (InfinitePlace E)), max (x w) ε ≤
          M ^ Fintype.card (InfinitePlace E) := by
        calc ∏ w ∈ ({w₀}ᶜ : Finset (InfinitePlace E)), max (x w) ε
            ≤ ∏ w ∈ ({w₀}ᶜ : Finset (InfinitePlace E)), M := by
              apply Finset.prod_le_prod (fun w _ => le_trans hεpos.le (le_max_right _ _))
              intro w _
              apply max_le
              · have h3 : x w ≤ ∑ v, x v := Finset.single_le_sum (fun v _ => hx v) (Finset.mem_univ w)
                linarith
              · exact le_trans (min_le_left _ _) hM1
          _ = M ^ ({w₀}ᶜ : Finset (InfinitePlace E)).card := Finset.prod_const M
          _ ≤ M ^ Fintype.card (InfinitePlace E) := pow_le_pow_right₀ hM1 (Finset.card_le_univ _)
      show ∏ w, max (x w) ε ≤ T
      rw [Fintype.prod_eq_mul_prod_compl w₀, hxw0, max_eq_right hεpos.le]
      calc ε * ∏ w ∈ ({w₀}ᶜ : Finset (InfinitePlace E)), max (x w) ε
          ≤ ε * M ^ Fintype.card (InfinitePlace E) := mul_le_mul_of_nonneg_left hcomp hεpos.le
        _ ≤ (T / M ^ Fintype.card (InfinitePlace E)) * M ^ Fintype.card (InfinitePlace E) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_pos hMpos _).le
        _ = T := div_mul_cancel₀ T (pow_pos hMpos _).ne'
  have hPpos : 0 < ∏ w, y w := Finset.prod_pos fun w _ => hy0 w
  have hQpos : 0 < √(FractionalIdeal.absNorm aa : ℝ) / ∏ w, y w := div_pos hNpos hPpos
  set Θ' : ℝ := (√(FractionalIdeal.absNorm aa : ℝ) / ∏ w, y w) ^ ((1 : ℝ) / Fintype.card (InfinitePlace E))
    with hΘ'
  have hΘ'nn : 0 ≤ Θ' := Real.rpow_nonneg hQpos.le _
  have hΘ'd : Θ' ^ Fintype.card (InfinitePlace E) = √(FractionalIdeal.absNorm aa : ℝ) / ∏ w, y w := by
    rw [hΘ', ← Real.rpow_natCast, ← Real.rpow_mul hQpos.le]
    have hdr : ((1 : ℝ) / Fintype.card (InfinitePlace E)) * (Fintype.card (InfinitePlace E) : ℝ) = 1 := by
      field_simp
    rw [hdr, Real.rpow_one]
  have hΘ'ge : Θ / a ≤ Θ' := by
    have h1 : (Θ / a) ^ Fintype.card (InfinitePlace E) ≤ Θ' ^ Fintype.card (InfinitePlace E) := by
      rw [hΘ'd, le_div_iff₀ hPpos]
      calc (Θ / a) ^ Fintype.card (InfinitePlace E) * ∏ w, y w
          ≤ (Θ / a) ^ Fintype.card (InfinitePlace E) * T :=
            mul_le_mul_of_nonneg_left hyT (pow_pos (div_pos hΘpos hapos) _).le
        _ = √(FractionalIdeal.absNorm aa : ℝ) := by
            rw [hT, ← mul_assoc, ← mul_pow]
            have hone : Θ / a * (a / Θ) = 1 := by field_simp
            rw [hone, one_pow, one_mul]
    first
    | exact le_of_pow_le_pow_left₀ hd0.ne' hΘ'nn h1
    | exact (pow_le_pow_iff_left₀ (div_pos hΘpos hapos).le hΘ'nn hd0.ne').mp h1
  have hΘ'2 : 2 < Θ' := lt_of_lt_of_le (by rw [lt_div_iff₀ hapos]; linarith) hΘ'ge
  have hK3 : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hbox := hC₀ E aa haa y Θ' (K : ℝ) hy0 hΘ'2 hK3 hΘ'd
  unfold TA.LatSum
  constructor
  · intro l
    unfold prof
    exact Finset.prod_nonneg fun w _ => le_min zero_le_one (pow_nonneg (div_nonneg (hx w) (wnn w l)) _)
  · intro S hS
    have hS' : ∀ l ∈ S, l ∈ aa ∧ l ≠ 0 := fun l hl => ⟨hL l (hS l hl).1, (hS l hl).2⟩
    have h1 := hbox S hS'
    have hs : 0 < (K : ℝ) - 5 / 2 := by linarith
    have ht0 : 0 ≤ Θ' ^ (-((K : ℝ) - 5 / 2)) := Real.rpow_nonneg hΘ'nn _
    have htle : Θ' ^ (-((K : ℝ) - 5 / 2)) ≤ a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)) := by
      have hta : 0 < Θ / a := div_pos hΘpos hapos
      rw [Real.rpow_neg hΘ'nn, Real.rpow_neg hΘpos.le]
      have h2 : (Θ / a) ^ ((K : ℝ) - 5 / 2) ≤ Θ' ^ ((K : ℝ) - 5 / 2) :=
        Real.rpow_le_rpow hta.le hΘ'ge hs.le
      have h3 : (Θ' ^ ((K : ℝ) - 5 / 2))⁻¹ ≤ ((Θ / a) ^ ((K : ℝ) - 5 / 2))⁻¹ :=
        inv_anti₀ (Real.rpow_pos_of_pos hta _) h2
      refine le_trans h3 (le_of_eq ?_)
      rw [Real.div_rpow hΘpos.le hapos.le, inv_div, div_eq_mul_inv]
    calc ∑ l ∈ S, prof x K l ≤ ∑ l ∈ S, ∏ w, min 1 ((y w / w l) ^ (K : ℝ)) := by
          apply Finset.sum_le_sum
          intro l _
          unfold prof
          apply Finset.prod_le_prod
          · intro w _
            exact le_min zero_le_one (pow_nonneg (div_nonneg (hx w) (wnn w l)) _)
          · intro w _
            rw [Real.rpow_natCast]
            apply min_le_min_left
            exact pow_le_pow_left₀ (div_nonneg (hx w) (wnn w l)) (div_le_div_of_nonneg_right (hxy w) (wnn w l)) _
      _ ≤ (C₀ * Θ' ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E) := h1
      _ ≤ (|C₀| * Θ' ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E) := by
          have e : (|C₀| * Θ' ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E) =
              |(C₀ * Θ' ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E)| := by
            rw [abs_pow, abs_mul, abs_of_nonneg ht0]
          rw [e]
          exact le_abs_self _
      _ ≤ (max 1 |C₀| * a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E) := by
          apply pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) ht0)
          rw [mul_assoc]
          exact mul_le_mul (le_max_right _ _) htle ht0 (le_trans zero_le_one (le_max_left _ _))

end Formalism.FourierDecayAlt.P.Jx1

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `Jx1.t_PSDAgree`.
-/
theorem psd_agree : Formalism.FourierDecayAlt.J.PSDAgree := Jx1.t_PSDAgree

/- English proof (translation)
The claim follows from `Jx1.t_PSDTranspose`.
-/
theorem psd_transpose : Formalism.FourierDecayAlt.J.PSDTranspose := Jx1.t_PSDTranspose

/- English proof (translation)
The claim follows from `Jx1.t_AxiomsAgree`.
-/
theorem axioms_agree : Formalism.FourierDecayAlt.J.AxiomsAgree := Jx1.t_AxiomsAgree

/- English proof (translation)
The claim follows from `Jx1.t_TowersAgree`.
-/
theorem towers_agree : Formalism.FourierDecayAlt.J.TowersAgree := Jx1.t_TowersAgree

/- English proof (translation)
The claim follows from `Jx1.t_FormsAgree`.
-/
theorem forms_agree : Formalism.FourierDecayAlt.J.FormsAgree := Jx1.t_FormsAgree

/- English proof (translation)
The claim follows from `Jx1.t_BoxSumLattice`.
-/
theorem box_sum_lattice : Formalism.FourierDecayAlt.J.BoxSumLattice := Jx1.t_BoxSumLattice

/- English proof (translation)
The claim follows from `Jx1.t_MajIsProf`.
-/
theorem majorant_is_profinite : Formalism.FourierDecayAlt.J.MajIsProf := Jx1.t_MajIsProf

end Formalism.FourierDecayAlt.P
