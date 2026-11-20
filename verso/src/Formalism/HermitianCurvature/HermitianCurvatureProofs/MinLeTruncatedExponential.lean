import Formalism.HermitianCurvature.StatementTBB
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IntegrableOnIoiTruncatedPowerMoment
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorSumCounterexample

namespace Formalism.FourierDecayAlt.P.TBBx1

open Finset Filter Topology MeasureTheory Real
open Formalism.FourierDecayAlt.TBB
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

section words

variable {P : M.Par} {l0 : ℕ} {Y : Finset ℝ} {N : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨hw.1, hl, [], by simp, by simp, by simp⟩`.
-/
lemma isExt_self {m : ℕ} {w : List C.Letter} (hw : AdmW P l0 Y w) (hl : w.length ≤ N) :
    IsExt P l0 Y N m w w :=
  ⟨hw.1, hl, [], by simp, by simp, by simp⟩

/- English proof (translation)
Take `⟨hc, -, L, rfl, -, hL⟩` from `h`. Use `⟨hc, fun l hl => ?_⟩` and prove the remaining obligations. Break down `List.mem_append.1 hl with hl | hl` into its components or cases. Conclude with `hL l hl`. Conclude with `hw.2 l hl`.
-/
lemma admissible_word_of_extension {m : ℕ} {w w' : List C.Letter} (hw : AdmW P l0 Y w) (h : IsExt P l0 Y N m w w') :
    AdmW P l0 Y w' := by
  obtain ⟨hc, -, L, rfl, -, hL⟩ := h
  refine ⟨hc, fun l hl => ?_⟩
  rcases List.mem_append.1 hl with hl | hl
  · exact hL l hl
  · exact hw.2 l hl

/- English proof (translation)
Take `⟨-, -, L, rfl, hL, -⟩` from `h`. Simplify using `only [List.length_append]`. Use linear arithmetic over natural numbers and integers.
-/
lemma isExt_len {m : ℕ} {w w' : List C.Letter} (h : IsExt P l0 Y N m w w') : w'.length ≤ w.length + m := by
  obtain ⟨-, -, L, rfl, hL, -⟩ := h
  simp only [List.length_append]
  omega

/- English proof (translation)
The claim follows from `h.2.1`.
-/
lemma isExt_lenN {m : ℕ} {w w' : List C.Letter} (h : IsExt P l0 Y N m w w') : w'.length ≤ N := h.2.1

/- English proof (translation)
Take `⟨-, -, L1, rfl, hL1, hY1⟩` from `h1`. Take `⟨hc, hN, L2, rfl, hL2, hY2⟩` from `h2`. Use `⟨hc, hN, L2 ++ L1, by simp, by simp only [List.length_append]; omega, fun l hl => ?_⟩` and prove the remaining obligations. Break down `List.mem_append.1 hl with hl | hl` into its components or cases. Conclude with `hY2 l hl`.

Conclude with `hY1 l hl`.
-/
lemma isExt_trans {m₁ m₂ : ℕ} {w w' w'' : List C.Letter} (h1 : IsExt P l0 Y N m₁ w w')
    (h2 : IsExt P l0 Y N m₂ w' w'') : IsExt P l0 Y N (m₁ + m₂) w w'' := by
  obtain ⟨-, -, L1, rfl, hL1, hY1⟩ := h1
  obtain ⟨hc, hN, L2, rfl, hL2, hY2⟩ := h2
  refine ⟨hc, hN, L2 ++ L1, by simp, by simp only [List.length_append]; omega, fun l hl => ?_⟩
  rcases List.mem_append.1 hl with hl | hl
  · exact hY2 l hl
  · exact hY1 l hl

/- English proof (translation)
Take `⟨hc, hN, L, hL, hLm, hY⟩` from `h`. Conclude with `⟨hc, hN, L, hL, hLm.trans hm, hY⟩`.
-/
lemma isExt_mono {m m' : ℕ} {w w' : List C.Letter} (h : IsExt P l0 Y N m w w') (hm : m ≤ m') :
    IsExt P l0 Y N m' w w' := by
  obtain ⟨hc, hN, L, hL, hLm, hY⟩ := h
  exact ⟨hc, hN, L, hL, hLm.trans hm, hY⟩

/- English proof (translation)
Set `A : Finset C.Letter` to `Y.image (fun y => (true, y)) ∪ Y.image (fun y => (false, y + 1))`. Establish `hfin : {L : List A | L.length ≤ m}.Finite` using `List.finite_length_le A m`. Use `(hfin.image (fun L => L.map Subtype.val ++ w)).subset ?_` and prove the remaining obligations. Introduce and unpack `w' ⟨-, -, L, rfl, hLm, hY⟩`. Establish `hA : ∀ l ∈ L, l ∈ A`.

Introduce `l hl`. Take `⟨y, hy, h | h⟩` from `hY l hl`. Conclude with `Finset.mem_union_left _ (Finset.mem_image.2 ⟨y, hy, h.symm⟩)`. Conclude with `Finset.mem_union_right _ (Finset.mem_image.2 ⟨y, hy, h.symm⟩)`. Use `⟨L.attach.map (fun x => ⟨x.1, hA x.1 x.2⟩), by simpa using hLm, ?_⟩` and prove the remaining obligations.

Use `show List.map Subtype.val (List.map _ L.attach) ++ w = L ++ w`. Rewrite using `[List.map_map]`. Use `congr 1`. Conclude with `List.attach_map_subtype_val L`.
-/
lemma isExt_finite (m : ℕ) (w : List C.Letter) : {w' | IsExt P l0 Y N m w w'}.Finite := by
  let A : Finset C.Letter := Y.image (fun y => (true, y)) ∪ Y.image (fun y => (false, y + 1))
  have hfin : {L : List A | L.length ≤ m}.Finite := List.finite_length_le A m
  refine (hfin.image (fun L => L.map Subtype.val ++ w)).subset ?_
  rintro w' ⟨-, -, L, rfl, hLm, hY⟩
  have hA : ∀ l ∈ L, l ∈ A := by
    intro l hl
    obtain ⟨y, hy, h | h⟩ := hY l hl
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨y, hy, h.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨y, hy, h.symm⟩)
  refine ⟨L.attach.map (fun x => ⟨x.1, hA x.1 x.2⟩), by simpa using hLm, ?_⟩
  show List.map Subtype.val (List.map _ L.attach) ++ w = L ++ w
  rw [List.map_map]
  congr 1
  exact List.attach_map_subtype_val L

/- English proof (translation)
Take `⟨a, ha, hmax⟩` from `Set.exists_max_image _ f (isExt_finite m w) ⟨w, hw⟩`. Conclude with `⟨a, ha, fun b hb => hmax b hb⟩`.
-/
lemma exists_max_ext (m : ℕ) (w : List C.Letter) (f : List C.Letter → ℝ) (hw : IsExt P l0 Y N m w w) :
    ∃ w', IsExt P l0 Y N m w w' ∧ ∀ w'', IsExt P l0 Y N m w w'' → f w'' ≤ f w' := by
  obtain ⟨a, ha, hmax⟩ := Set.exists_max_image _ f (isExt_finite m w) ⟨w, hw⟩
  exact ⟨a, ha, fun b hb => hmax b hb⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨fun a => (Nat.not_lt_zero _ a.2).elim, fun a => (Nat.not_lt_zero _ a.2).elim⟩, by simp⟩`.
-/
lemma admissible_word_nil : AdmW P l0 Y [] :=
  ⟨⟨fun a => (Nat.not_lt_zero _ a.2).elim, fun a => (Nat.not_lt_zero _ a.2).elim⟩, by simp⟩

end words

/- English proof (translation)
Unfold `mn`. Use `split_ifs`. Evaluate the numerical expressions. Conclude with `le_min zero_le_one (pow_nonneg (div_nonneg hΛ hx) _)`.
-/
lemma mn_nonneg {Λ : ℝ} (hΛ : 0 ≤ Λ) (K : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ mn Λ K x := by
  unfold mn
  split_ifs
  · norm_num
  · exact le_min zero_le_one (pow_nonneg (div_nonneg hΛ hx) _)

/- English proof (translation)
Unfold `mn Formalism.HermitianLatticeCounting.ExpansionTerms.TruncationCutoff`. Use `split_ifs with h0`. Conclude with `le_rfl`. Rewrite using `[show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]`. Establish `ha : 0 ≤ Λ / t` using `div_nonneg hΛ ht`.

Establish `hab : Λ / t ≤ x / t` using `div_le_div_of_nonneg_right hΛx ht`. Combine the equalities or inequalities in the displayed calculation. Break down `le_or_gt (Λ / t) 1 with h1 | h1` into its components or cases. Conclude with `min_le_min le_rfl (pow_le_pow_of_le_one ha h1 hK)`. Rewrite using `[min_eq_left (one_le_pow₀ h1.le), min_eq_left (one_le_pow₀ h1.le)]`.

Use `_ ≤ min 1 ((x / t) ^ 3) := min_le_min le_rfl (pow_le_pow_left₀ ha hab 3)`.
-/
lemma min_le_truncated_exponential {Λ x : ℝ} (hΛ : 0 ≤ Λ) (hΛx : Λ ≤ x) {K : ℕ} (hK : 3 ≤ K) {t : ℝ} (ht : 0 ≤ t) :
    mn Λ K t ≤ Formalism.HermitianLatticeCounting.ExpansionTerms.TruncationCutoff 3 x t := by
  unfold mn Formalism.HermitianLatticeCounting.ExpansionTerms.TruncationCutoff
  split_ifs with h0
  · exact le_rfl
  · rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have ha : 0 ≤ Λ / t := div_nonneg hΛ ht
    have hab : Λ / t ≤ x / t := div_le_div_of_nonneg_right hΛx ht
    calc min 1 ((Λ / t) ^ K) ≤ min 1 ((Λ / t) ^ 3) := by
          rcases le_or_gt (Λ / t) 1 with h1 | h1
          · exact min_le_min le_rfl (pow_le_pow_of_le_one ha h1 hK)
          · rw [min_eq_left (one_le_pow₀ h1.le), min_eq_left (one_le_pow₀ h1.le)]
      _ ≤ min 1 ((x / t) ^ 3) := min_le_min le_rfl (pow_le_pow_left₀ ha hab 3)

/- English proof (translation)
Unfold `Formalism.HermitianLatticeCounting.ExpansionTerms.TruncationCutoff`. Use `split_ifs`. Evaluate the numerical expressions. Conclude with `le_min zero_le_one (Real.rpow_nonneg (div_nonneg hx ht) _)`.
-/
lemma truncated_exponential_nonneg (x t : ℝ) (hx : 0 ≤ x) (ht : 0 ≤ t) : 0 ≤ Formalism.HermitianLatticeCounting.ExpansionTerms.TruncationCutoff 3 x t := by
  unfold Formalism.HermitianLatticeCounting.ExpansionTerms.TruncationCutoff
  split_ifs
  · norm_num
  · exact le_min zero_le_one (Real.rpow_nonneg (div_nonneg hx ht) _)

/- English proof (translation)
Unfold `P5.fsv`. Use `congr 1`. Apply the tactic sequence `apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring`.
-/
lemma fsv_eq (s c : ℂ) : P5.fsv s c = Complex.exp (2 * Complex.I * ((s * c).im : ℂ)) := by
  unfold P5.fsv
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/- English proof (translation)
Simplify using `[ae_iff]`.
-/
lemma ae_ne_zero : ∀ᵐ c : ℂ ∂volume, c ≠ 0 := by
  simp [ae_iff]

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P p nn F Y Λ K N hK hΛ hI2 hI3 j hj h hh w hw hlen c hc`. Take `⟨φ, hφc, hφi, hφe⟩` from `hI2 j hj h hh w hw (by omega)`. Establish `hself : IsExt P p.l0 Y N K w w` using `isExt_self hw (by omega)`. Take `⟨wm, hwm, hmax⟩` from `exists_max_ext K w (fun w' => Ew p nn F j w' h) hself`. Use `set M := Ew p nn F j wm h with hMdef`.

Establish `hint : ∀ s : ℂ, ∫ c, Complex.exp (2 * Complex.I * ((s * c).im : ℂ)) * φ c = ∫ c, P5.fsv s c * NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])`. Introduce `s`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_ne_zero] with c hc`. Rewrite using `[fsv_eq, hφe c hc]`.

Establish `hbd : ∀ s : ℂ, ‖∫ c, P5.fsv s c * NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])‖ ≤ mn Λ K ‖s‖ * M`. Introduce `s`. Take `⟨w', hw', hb⟩` from `hI3 j hj h hh w hw hlen s`. Conclude with `hb.trans (mul_le_mul_of_nonneg_left (hmax w' hw') (mn_nonneg hΛ K (norm_nonneg _)))`. Establish `hM : 0 ≤ M`.

Establish `h0` using `hbd 0`. Simplify using `only [norm_zero, mn, if_true, one_mul] at h0`. Conclude with `(norm_nonneg _).trans h0`. Establish `key : ∀ x : ℝ, 0 < x → Λ ≤ x → ‖φ c‖ ≤ 3 / π * x ^ 2 * M`. Introduce `x hx hΛx`.

Use `Formalism.HermitianLatticeCounting.P.sup_bound_of_truncated_integral φ x M hφc hφi hx (fun s => ?_) c` and prove the remaining obligations. Rewrite using `[hint s, mul_comm M]`. Conclude with `(hbd s).trans (mul_le_mul_of_nonneg_right (min_le_truncated_exponential hΛ hΛx hK (norm_nonneg _)) hM)`. Establish `hre : Ew p nn F (j + 1) w (h ++ [(1, c)]) ≤ ‖φ c‖` using `by show (NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])).re ≤ _`. Rewrite using `[← hφe c hc]`.

Conclude with `Complex.re_le_norm _`. Use `⟨wm, hwm, hre.trans ?_⟩` and prove the remaining obligations. Break down `hΛ.lt_or_eq with hpos | h0` into its components or cases. Conclude with `key Λ hpos le_rfl`. Rewrite using `[← h0]`.

Establish `ht : Tendsto (fun x : ℝ => 3 / π * x ^ 2 * M) (𝓝[>] 0) (𝓝 (3 / π * 0 ^ 2 * M))` using `((by fun_prop : Continuous fun x : ℝ => 3 / π * x ^ 2 * M).tendsto 0).mono_left nhdsWithin_le_nhds`. Use `ge_of_tendsto ht ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with x hx`. Conclude with `key x hx (h0 ▸ le_of_lt hx)`.
-/
theorem stepOne : StepOne := by
  intro Wp Wq _ _ _ _ _ _ P p nn F Y Λ K N hK hΛ hI2 hI3 j hj h hh w hw hlen c hc
  obtain ⟨φ, hφc, hφi, hφe⟩ := hI2 j hj h hh w hw (by omega)
  have hself : IsExt P p.l0 Y N K w w := isExt_self hw (by omega)
  obtain ⟨wm, hwm, hmax⟩ := exists_max_ext K w (fun w' => Ew p nn F j w' h) hself
  set M := Ew p nn F j wm h with hMdef
  have hint : ∀ s : ℂ, ∫ c, Complex.exp (2 * Complex.I * ((s * c).im : ℂ)) * φ c
      = ∫ c, P5.fsv s c * NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)]) := by
    intro s
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero] with c hc
    rw [fsv_eq, hφe c hc]
  have hbd : ∀ s : ℂ, ‖∫ c, P5.fsv s c * NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])‖ ≤
      mn Λ K ‖s‖ * M := by
    intro s
    obtain ⟨w', hw', hb⟩ := hI3 j hj h hh w hw hlen s
    exact hb.trans (mul_le_mul_of_nonneg_left (hmax w' hw') (mn_nonneg hΛ K (norm_nonneg _)))
  have hM : 0 ≤ M := by
    have h0 := hbd 0
    simp only [norm_zero, mn, if_true, one_mul] at h0
    exact (norm_nonneg _).trans h0
  have key : ∀ x : ℝ, 0 < x → Λ ≤ x → ‖φ c‖ ≤ 3 / π * x ^ 2 * M := by
    intro x hx hΛx
    refine Formalism.HermitianLatticeCounting.P.sup_bound_of_truncated_integral φ x M hφc hφi hx (fun s => ?_) c
    rw [hint s, mul_comm M]
    exact (hbd s).trans (mul_le_mul_of_nonneg_right (min_le_truncated_exponential hΛ hΛx hK (norm_nonneg _)) hM)
  have hre : Ew p nn F (j + 1) w (h ++ [(1, c)]) ≤ ‖φ c‖ := by
    show (NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])).re ≤ _
    rw [← hφe c hc]
    exact Complex.re_le_norm _
  refine ⟨wm, hwm, hre.trans ?_⟩
  rcases hΛ.lt_or_eq with hpos | h0
  · exact key Λ hpos le_rfl
  · rw [← h0]
    have ht : Tendsto (fun x : ℝ => 3 / π * x ^ 2 * M) (𝓝[>] 0) (𝓝 (3 / π * 0 ^ 2 * M)) :=
      ((by fun_prop : Continuous fun x : ℝ => 3 / π * x ^ 2 * M).tendsto 0).mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact key x hx (h0 ▸ le_of_lt hx)

/- English proof (translation)
Rewrite using `[show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num`.
-/
lemma gauss_const : (4 * (3 / 2 : ℝ) ^ (3 : ℝ) * (3 / (3 - 2))) = 40.5 := by
  rw [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

/- English proof (translation)
Use `⟨40.5 / π, by positivity, ?_⟩` and prove the remaining obligations. Introduce `Wp Wq _ _ _ _ _ _ P p nn F Y Λ K N hK hΛ hPos hI4 hI5 b s hb hs hbs h hh w hw hlen Mb hMb z hz`. Establish `hΛ0 : 0 < Λ` using `by linarith`. Establish `hMb0 : 0 ≤ Mb` using `(hPos _ w _ hw (by omega)).trans (hMb w (isExt_self hw (by omega)) 1 one_ne_zero)`. Use `set ω₁ : ℂ := ((π / Λ : ℝ) : ℂ) with hω₁`.

Use `set ω₂ : ℂ := ((π / Λ : ℝ) : ℂ) * Complex.I with hω₂`. Establish `him : (conj ω₁ * ω₂).im = (π / Λ) ^ 2`. Simplify using `[hω₁, hω₂, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree. Establish `hne : (conj ω₁ * ω₂).im ≠ 0` using `by rw [him]; positivity`.

Establish `hbdd : ∀ w', IsExt P p.l0 Y N K w w' → BddAbove (Set.range fun t : {t : ℂ // t ≠ 0} => Ew p nn F (b + s - 2) w' (h ++ [(s - 1, t.1)]))` using `fun w' hw' => ⟨Mb, by rintro _ ⟨t, rfl⟩; exact hMb w' hw' t.1 t.2⟩`. Take `⟨k, hk1, hk2⟩` from `hI5 b s hb hs hbs h hh w hw hlen hbdd ω₁ ω₂ z hne`. Establish `hkσ : ∀ σ, InDual ω₁ ω₂ σ → (‖k σ‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (mn Λ K ‖σ‖ * Mb)`. Introduce `σ hσ`. Use `(hk2 σ hσ).trans (limsup_le_of_le (by isBoundedDefault) ?_)` and prove the remaining obligations.

Establish `ev1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ≠ 0` using `self_mem_nhdsWithin`. Establish `ev2 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t⁻¹ + σ ≠ 0`. Distinguish the cases in `hσ0 : σ = 0`. Use `filter_upwards [ev1] with t ht`. Simplify `ht` using `[hσ0]`.

Establish `hn : ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ (-σ)⁻¹` using `eventually_ne_nhds (by simpa using hσ0) filter_upwards [nhdsWithin_le_nhds hn] with t ht`. Introduce `h0`. Apply `ht` to reduce the goal to its premises. Rewrite using `[← eq_neg_iff_add_eq_zero.2 h0, inv_inv]`. Use `filter_upwards [ev1, ev2] with t ht ht'`.

Establish `ht'' : (t⁻¹ + σ)⁻¹ ≠ 0` using `inv_ne_zero ht'`. Take `⟨w₁, w₂, hw₁, hw₂, hN⟩` from `hI4 b (s - 1) hb (by omega) (by omega) h hh w hw hlen t _ ht ht''`. Rewrite `hN` using `[show b + (s - 1) - 1 = b + s - 2 by omega]`. Establish `hdiff : ‖t⁻¹ - ((t⁻¹ + σ)⁻¹)⁻¹‖ = ‖σ‖`. Rewrite using `[inv_inv, sub_add_cancel_left, norm_neg]`.

Rewrite `hN` using `[hdiff]`. Establish `hE1` using `hMb w₁ hw₁ t ht`. Establish `hE2` using `hMb w₂ hw₂ _ ht''`. Establish `hmn` using `mn_nonneg hΛ0.le K (norm_nonneg σ)`. Establish `hle : ‖NP p nn F (b + s - 2) w (h ++ [(s - 1, t)]) (h ++ [(s - 1, (t⁻¹ + σ)⁻¹)])‖ ≤ mn Λ K ‖σ‖ * Mb` using `hN.trans (mul_le_mul_of_nonneg_left (by linarith) hmn)`.

Rewrite using `[← ENNReal.ofReal_coe_nnreal, coe_nnnorm]`. Conclude with `ENNReal.ofReal_le_ofReal hle`. Establish `hdual : ∀ σ, InDual ω₁ ω₂ σ → σ ∈ Set.range (fun a : GaussianInt => (Λ : ℂ) * GaussianInt.toComplex a)`. Introduce `σ hσ`. Establish `h1` using `hσ 1 0`.

Establish `h2` using `hσ 0 1`. Simplify using `only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, add_zero, zero_add] at h1 h2`. Rewrite `h1`, `h2` using `[fsv_eq, Complex.exp_eq_one_iff]`. Take `⟨n1, hn1⟩` from `h1`. Take `⟨n2, hn2⟩` from `h2`.

Establish `e1` using `congrArg Complex.im hn1`. Establish `e2` using `congrArg Complex.im hn2`. Simplify using `[hω₁, hω₂, Complex.mul_im, Complex.mul_re] at e1 e2`. Use `⟨⟨n2, n1⟩, ?_⟩` and prove the remaining obligations. Use `show (Λ : ℂ) * GaussianInt.toComplex ⟨n2, n1⟩ = σ`.

Rewrite using `[GaussianInt.toComplex_def']`. Establish `hπ` using `Real.pi_pos`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Clear denominators, using `at e2` for the nonvanishing conditions.

Use the polynomial consequences of the given equalities and inequalities. Simplify using the standard rewrite rules. Clear denominators, using `at e1` for the nonvanishing conditions. Use the polynomial consequences of the given equalities and inequalities. Establish `hinj : Function.Injective (fun a : GaussianInt => (Λ : ℂ) * GaussianInt.toComplex a)`.

Introduce `a a' haa`. Establish `: GaussianInt.toComplex a = GaussianInt.toComplex a'` using `mul_left_cancel₀ (by exact_mod_cast hΛ0.ne') haa`. Conclude with `GaussianInt.toComplex_injective this`. Set `g : ℂ → ℝ≥0∞` to `fun σ => ENNReal.ofReal (Formalism.HermitianLatticeCounting.ExpansionTerms.TruncationCutoff 3 Λ ‖σ‖)`. Establish `hG : ∑' a : GaussianInt, g ((Λ : ℂ) * GaussianInt.toComplex a) ≤ ENNReal.ofReal 40.5`.

Rewrite using `[ENNReal.tsum_eq_iSup_sum]`. Use `iSup_le fun S => ?_` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_sum_of_nonneg (fun a _ => truncated_exponential_nonneg _ _ hΛ0.le (norm_nonneg _))]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Use `Formalism.HermitianLatticeCounting.P.gaussian_lattice_cutoff_sum 3 Λ (by norm_num) hΛ0 S` as an intermediate fact.

Rewrite `this` using `[gauss_const]`. Then use the resulting hypothesis. Establish `hsum : ∑' σ : {σ : ℂ // InDual ω₁ ω₂ σ}, (‖k σ.1‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal Mb * ENNReal.ofReal 40.5`. Combine the equalities or inequalities in the displayed calculation. Use `ENNReal.tsum_le_tsum fun σ => (hkσ σ.1 σ.2).trans ?_` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_mul hMb0, mul_comm Mb]`.

Use `ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hMb0)` and prove the remaining obligations. Conclude with `min_le_truncated_exponential hΛ0.le le_rfl hK (norm_nonneg _)`. Use `_ = ENNReal.ofReal Mb * ∑' σ : {σ : ℂ // InDual ω₁ ω₂ σ}, g σ.1 := ENNReal.tsum_mul_left`. Use `_ ≤ ENNReal.ofReal Mb * ∑' σ : Set.range (fun a : GaussianInt => (Λ : ℂ) * GaussianInt.toComplex a), g σ.1 := by gcongr`. Conclude with `ENNReal.tsum_mono_subtype g (fun σ hσ => hdual σ hσ)`.

Use `_ = ENNReal.ofReal Mb * ∑' a : GaussianInt, g ((Λ : ℂ) * GaussianInt.toComplex a) := by`. Rewrite using `[tsum_range g hinj]`. Use `_ ≤ ENNReal.ofReal Mb * ENNReal.ofReal 40.5 := by gcongr`. Establish `hterm : ENNReal.ofReal (Ew p nn F (b + s - 1) w (h ++ [(s, z)])) ≤ ∑' ab : ℤ × ℤ, ENNReal.ofReal (Ew p nn F (b + s - 1) w (h ++ [(s, z + (ab.1 : ℂ) * ω₁ + (ab.2 : ℂ) * ω₂)]))`. Use `le_of_eq_of_le ?_ (ENNReal.le_tsum ((0 : ℤ), (0 : ℤ)))` and prove the remaining obligations.

Simplify using the standard rewrite rules. Establish `hv : |(conj ω₁ * ω₂).im| / π = π / Λ ^ 2`. Rewrite using `[him, abs_of_nonneg (by positivity)]`. Clear the denominators using the available nonvanishing facts. Establish `hmain : ENNReal.ofReal (π / Λ ^ 2 * Ew p nn F (b + s - 1) w (h ++ [(s, z)])) ≤ ENNReal.ofReal (Mb * 40.5)`.

Rewrite using `[ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hMb0, ← hv]`. Establish `hm : ENNReal.ofReal (|(conj ω₁ * ω₂).im| / π) * ENNReal.ofReal (Ew p nn F (b + s - 1) w (h ++ [(s, z)])) ≤ ENNReal.ofReal (|(conj ω₁ * ω₂).im| / π) * ∑' ab : ℤ × ℤ, ENNReal.ofReal (Ew p nn F (b + s - 1) w (h ++ [(s, z + (ab.1 : ℂ) * ω₁ + (ab.2 : ℂ) * ω₂)]))` using `by gcongr`. Conclude with `hm.trans (hk1.trans hsum)`. Establish `hfin` using `(ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hmain`. Establish `hπ` using `Real.pi_pos`.

Establish `hΛ2 : 0 < Λ ^ 2` using `by positivity`. Rewrite `hfin` using `[div_mul_eq_mul_div, div_le_iff₀ hΛ2]`. Rewrite using `[div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hπ]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem stepUp : StepUp := by
  refine ⟨40.5 / π, by positivity, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p nn F Y Λ K N hK hΛ hPos hI4 hI5 b s hb hs hbs h hh w hw hlen Mb hMb z hz
  have hΛ0 : 0 < Λ := by linarith
  have hMb0 : 0 ≤ Mb :=
    (hPos _ w _ hw (by omega)).trans (hMb w (isExt_self hw (by omega)) 1 one_ne_zero)
  set ω₁ : ℂ := ((π / Λ : ℝ) : ℂ) with hω₁
  set ω₂ : ℂ := ((π / Λ : ℝ) : ℂ) * Complex.I with hω₂
  have him : (conj ω₁ * ω₂).im = (π / Λ) ^ 2 := by
    simp [hω₁, hω₂, Complex.conj_ofReal]
    ring
  have hne : (conj ω₁ * ω₂).im ≠ 0 := by rw [him]; positivity
  have hbdd : ∀ w', IsExt P p.l0 Y N K w w' →
      BddAbove (Set.range fun t : {t : ℂ // t ≠ 0} => Ew p nn F (b + s - 2) w' (h ++ [(s - 1, t.1)])) :=
    fun w' hw' => ⟨Mb, by rintro _ ⟨t, rfl⟩; exact hMb w' hw' t.1 t.2⟩
  obtain ⟨k, hk1, hk2⟩ := hI5 b s hb hs hbs h hh w hw hlen hbdd ω₁ ω₂ z hne
  have hkσ : ∀ σ, InDual ω₁ ω₂ σ → (‖k σ‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (mn Λ K ‖σ‖ * Mb) := by
    intro σ hσ
    refine (hk2 σ hσ).trans (limsup_le_of_le (by isBoundedDefault) ?_)
    have ev1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ≠ 0 := self_mem_nhdsWithin
    have ev2 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t⁻¹ + σ ≠ 0 := by
      by_cases hσ0 : σ = 0
      · filter_upwards [ev1] with t ht
        simpa [hσ0] using ht
      · have hn : ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ (-σ)⁻¹ :=
          eventually_ne_nhds (by simpa using hσ0)
        filter_upwards [nhdsWithin_le_nhds hn] with t ht
        intro h0
        apply ht
        rw [← eq_neg_iff_add_eq_zero.2 h0, inv_inv]
    filter_upwards [ev1, ev2] with t ht ht'
    have ht'' : (t⁻¹ + σ)⁻¹ ≠ 0 := inv_ne_zero ht'
    obtain ⟨w₁, w₂, hw₁, hw₂, hN⟩ := hI4 b (s - 1) hb (by omega) (by omega) h hh w hw hlen t _ ht ht''
    rw [show b + (s - 1) - 1 = b + s - 2 by omega] at hN
    have hdiff : ‖t⁻¹ - ((t⁻¹ + σ)⁻¹)⁻¹‖ = ‖σ‖ := by
      rw [inv_inv, sub_add_cancel_left, norm_neg]
    rw [hdiff] at hN
    have hE1 := hMb w₁ hw₁ t ht
    have hE2 := hMb w₂ hw₂ _ ht''
    have hmn := mn_nonneg hΛ0.le K (norm_nonneg σ)
    have hle : ‖NP p nn F (b + s - 2) w (h ++ [(s - 1, t)]) (h ++ [(s - 1, (t⁻¹ + σ)⁻¹)])‖ ≤
        mn Λ K ‖σ‖ * Mb := hN.trans (mul_le_mul_of_nonneg_left (by linarith) hmn)
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    exact ENNReal.ofReal_le_ofReal hle
  have hdual : ∀ σ, InDual ω₁ ω₂ σ → σ ∈ Set.range (fun a : GaussianInt => (Λ : ℂ) * GaussianInt.toComplex a) := by
    intro σ hσ
    have h1 := hσ 1 0
    have h2 := hσ 0 1
    simp only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, add_zero, zero_add] at h1 h2
    rw [fsv_eq, Complex.exp_eq_one_iff] at h1 h2
    obtain ⟨n1, hn1⟩ := h1
    obtain ⟨n2, hn2⟩ := h2
    have e1 := congrArg Complex.im hn1
    have e2 := congrArg Complex.im hn2
    simp [hω₁, hω₂, Complex.mul_im, Complex.mul_re] at e1 e2
    refine ⟨⟨n2, n1⟩, ?_⟩
    show (Λ : ℂ) * GaussianInt.toComplex ⟨n2, n1⟩ = σ
    rw [GaussianInt.toComplex_def']
    have hπ := Real.pi_pos
    apply Complex.ext
    · simp
      field_simp at e2
      nlinarith
    · simp
      field_simp at e1
      nlinarith
  have hinj : Function.Injective (fun a : GaussianInt => (Λ : ℂ) * GaussianInt.toComplex a) := by
    intro a a' haa
    have : GaussianInt.toComplex a = GaussianInt.toComplex a' :=
      mul_left_cancel₀ (by exact_mod_cast hΛ0.ne') haa
    exact GaussianInt.toComplex_injective this
  let g : ℂ → ℝ≥0∞ := fun σ => ENNReal.ofReal (Formalism.HermitianLatticeCounting.ExpansionTerms.TruncationCutoff 3 Λ ‖σ‖)
  have hG : ∑' a : GaussianInt, g ((Λ : ℂ) * GaussianInt.toComplex a) ≤ ENNReal.ofReal 40.5 := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun S => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => truncated_exponential_nonneg _ _ hΛ0.le (norm_nonneg _))]
    refine ENNReal.ofReal_le_ofReal ?_
    have := Formalism.HermitianLatticeCounting.P.gaussian_lattice_cutoff_sum 3 Λ (by norm_num) hΛ0 S
    rwa [gauss_const] at this
  have hsum : ∑' σ : {σ : ℂ // InDual ω₁ ω₂ σ}, (‖k σ.1‖₊ : ℝ≥0∞) ≤
      ENNReal.ofReal Mb * ENNReal.ofReal 40.5 := by
    calc ∑' σ : {σ : ℂ // InDual ω₁ ω₂ σ}, (‖k σ.1‖₊ : ℝ≥0∞)
        ≤ ∑' σ : {σ : ℂ // InDual ω₁ ω₂ σ}, ENNReal.ofReal Mb * g σ.1 := by
          refine ENNReal.tsum_le_tsum fun σ => (hkσ σ.1 σ.2).trans ?_
          rw [← ENNReal.ofReal_mul hMb0, mul_comm Mb]
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hMb0)
          exact min_le_truncated_exponential hΛ0.le le_rfl hK (norm_nonneg _)
      _ = ENNReal.ofReal Mb * ∑' σ : {σ : ℂ // InDual ω₁ ω₂ σ}, g σ.1 := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal Mb *
            ∑' σ : Set.range (fun a : GaussianInt => (Λ : ℂ) * GaussianInt.toComplex a), g σ.1 := by
          gcongr
          exact ENNReal.tsum_mono_subtype g (fun σ hσ => hdual σ hσ)
      _ = ENNReal.ofReal Mb * ∑' a : GaussianInt, g ((Λ : ℂ) * GaussianInt.toComplex a) := by
          rw [tsum_range g hinj]
      _ ≤ ENNReal.ofReal Mb * ENNReal.ofReal 40.5 := by gcongr
  have hterm : ENNReal.ofReal (Ew p nn F (b + s - 1) w (h ++ [(s, z)])) ≤
      ∑' ab : ℤ × ℤ, ENNReal.ofReal
        (Ew p nn F (b + s - 1) w (h ++ [(s, z + (ab.1 : ℂ) * ω₁ + (ab.2 : ℂ) * ω₂)])) := by
    refine le_of_eq_of_le ?_ (ENNReal.le_tsum ((0 : ℤ), (0 : ℤ)))
    simp
  have hv : |(conj ω₁ * ω₂).im| / π = π / Λ ^ 2 := by
    rw [him, abs_of_nonneg (by positivity)]
    field_simp
  have hmain : ENNReal.ofReal (π / Λ ^ 2 * Ew p nn F (b + s - 1) w (h ++ [(s, z)])) ≤
      ENNReal.ofReal (Mb * 40.5) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hMb0, ← hv]
    have hm : ENNReal.ofReal (|(conj ω₁ * ω₂).im| / π) * ENNReal.ofReal (Ew p nn F (b + s - 1) w (h ++ [(s, z)])) ≤
        ENNReal.ofReal (|(conj ω₁ * ω₂).im| / π) * ∑' ab : ℤ × ℤ, ENNReal.ofReal
          (Ew p nn F (b + s - 1) w (h ++ [(s, z + (ab.1 : ℂ) * ω₁ + (ab.2 : ℂ) * ω₂)])) := by gcongr
    exact hm.trans (hk1.trans hsum)
  have hfin := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hmain
  have hπ := Real.pi_pos
  have hΛ2 : 0 < Λ ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hΛ2] at hfin
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hπ]
  nlinarith

/- English proof (translation)
Introduce `h1 hU`. Take `⟨Cu, hCu, hup⟩` from `hU`. Use `⟨max (3 / π) Cu, lt_max_of_lt_right hCu, ?_⟩` and prove the remaining obligations. Introduce `Wp Wq _ _ _ _ _ _ P p nn F Y Λ K N hK hΛ hPos hI2 hI3 hI4 hI5`. Establish `hC2 : 0 ≤ max (3 / π) Cu` using `le_max_of_le_right hCu.le`.

Establish `hCL : 0 ≤ max (3 / π) Cu * Λ ^ 2` using `by positivity`. Introduce `b s hb hs`. Proceed by induction on `s, hs using Nat.le_induction with`. Consider the case `base`. Introduce `hbs h hh w hw hlen t ht`.

Rewrite `hlen` using `[one_mul]`. Take `⟨w', hw', hE⟩` from `h1 Wp Wq P p nn F Y Λ K N hK (by linarith) hI2 hI3 (b - 1) (by omega) h hh w hw hlen t ht`. Rewrite `hE` using `[show b - 1 + 1 = b + 1 - 1 by omega]`. Use `⟨w', by rwa [one_mul], hE.trans ?_⟩` and prove the remaining obligations. Establish `hE0 : 0 ≤ Ew p nn F (b - 1) w' h` using `hPos _ _ _ (admissible_word_of_extension hw hw') (isExt_lenN hw')`.

Rewrite using `[pow_one]`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)) hE0`. Consider the case `succ s hs ih`. Introduce `hbs h hh w hw hlen t ht`. Establish `hlen' : w.length + K + s * K ≤ N` using `by rw [Nat.succ_mul] at hlen; omega`.

Establish `hself : IsExt P p.l0 Y N ((s + 1) * K) w w` using `isExt_self hw (by omega)`. Take `⟨wm, hwm, hmax⟩` from `exists_max_ext ((s + 1) * K) w (fun w' => Ew p nn F (b - 1) w' h) hself`. Establish `hE0 : 0 ≤ Ew p nn F (b - 1) wm h` using `hPos _ _ _ (admissible_word_of_extension hw hwm) (isExt_lenN hwm)`. Use `set Mb := (max (3 / π) Cu * Λ ^ 2) ^ s * Ew p nn F (b - 1) wm h with hMbdef`. Establish `hMb : ∀ w', IsExt P p.l0 Y N K w w' → ∀ t : ℂ, t ≠ 0 → Ew p nn F (b + (s + 1) - 2) w' (h ++ [(s + 1 - 1, t)]) ≤ Mb`.

Introduce `w' hw' t ht`. Rewrite using `[show b + (s + 1) - 2 = b + s - 1 by omega, show s + 1 - 1 = s by omega]`. Establish `hl' : w'.length + s * K ≤ N` using `by have := isExt_len hw'; omega`. Take `⟨w'', hw'', hE⟩` from `ih (by omega) h hh w' (admissible_word_of_extension hw hw') hl' t ht`. Use `hE.trans (mul_le_mul_of_nonneg_left (hmax w'' ?_) (pow_nonneg hCL _))` and prove the remaining obligations.

Use `isExt_mono (isExt_trans hw' hw'') ?_` and prove the remaining obligations. Rewrite using `[Nat.succ_mul]`. Use linear arithmetic over natural numbers and integers. Establish `hup'` using `hup Wp Wq P p nn F Y Λ K N hK hΛ hPos hI4 hI5 b (s + 1) hb (by omega) hbs h hh w hw (by omega) Mb hMb t ht`. Use `⟨wm, hwm, hup'.trans ?_⟩` and prove the remaining obligations.

Rewrite using `[hMbdef, pow_succ]`. Establish `hX : 0 ≤ (max (3 / π) Cu * Λ ^ 2) ^ s * Ew p nn F (b - 1) wm h` using `mul_nonneg (pow_nonneg hCL _) hE0`. Establish `hc : Cu * Λ ^ 2 ≤ max (3 / π) Cu * Λ ^ 2` using `mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lemmaSOfSteps : LemmaSOfSteps := by
  intro h1 hU
  obtain ⟨Cu, hCu, hup⟩ := hU
  refine ⟨max (3 / π) Cu, lt_max_of_lt_right hCu, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p nn F Y Λ K N hK hΛ hPos hI2 hI3 hI4 hI5
  have hC2 : 0 ≤ max (3 / π) Cu := le_max_of_le_right hCu.le
  have hCL : 0 ≤ max (3 / π) Cu * Λ ^ 2 := by positivity
  intro b s hb hs
  induction s, hs using Nat.le_induction with
  | base =>
    intro hbs h hh w hw hlen t ht
    rw [one_mul] at hlen
    obtain ⟨w', hw', hE⟩ := h1 Wp Wq P p nn F Y Λ K N hK (by linarith) hI2 hI3 (b - 1) (by omega) h hh w hw
      hlen t ht
    rw [show b - 1 + 1 = b + 1 - 1 by omega] at hE
    refine ⟨w', by rwa [one_mul], hE.trans ?_⟩
    have hE0 : 0 ≤ Ew p nn F (b - 1) w' h := hPos _ _ _ (admissible_word_of_extension hw hw') (isExt_lenN hw')
    rw [pow_one]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)) hE0
  | succ s hs ih =>
    intro hbs h hh w hw hlen t ht
    have hlen' : w.length + K + s * K ≤ N := by rw [Nat.succ_mul] at hlen; omega
    have hself : IsExt P p.l0 Y N ((s + 1) * K) w w := isExt_self hw (by omega)
    obtain ⟨wm, hwm, hmax⟩ := exists_max_ext ((s + 1) * K) w (fun w' => Ew p nn F (b - 1) w' h) hself
    have hE0 : 0 ≤ Ew p nn F (b - 1) wm h := hPos _ _ _ (admissible_word_of_extension hw hwm) (isExt_lenN hwm)
    set Mb := (max (3 / π) Cu * Λ ^ 2) ^ s * Ew p nn F (b - 1) wm h with hMbdef
    have hMb : ∀ w', IsExt P p.l0 Y N K w w' → ∀ t : ℂ, t ≠ 0 →
        Ew p nn F (b + (s + 1) - 2) w' (h ++ [(s + 1 - 1, t)]) ≤ Mb := by
      intro w' hw' t ht
      rw [show b + (s + 1) - 2 = b + s - 1 by omega, show s + 1 - 1 = s by omega]
      have hl' : w'.length + s * K ≤ N := by have := isExt_len hw'; omega
      obtain ⟨w'', hw'', hE⟩ := ih (by omega) h hh w' (admissible_word_of_extension hw hw') hl' t ht
      refine hE.trans (mul_le_mul_of_nonneg_left (hmax w'' ?_) (pow_nonneg hCL _))
      refine isExt_mono (isExt_trans hw' hw'') ?_
      rw [Nat.succ_mul]; omega
    have hup' := hup Wp Wq P p nn F Y Λ K N hK hΛ hPos hI4 hI5 b (s + 1) hb (by omega) hbs h hh w hw
      (by omega) Mb hMb t ht
    refine ⟨wm, hwm, hup'.trans ?_⟩
    rw [hMbdef, pow_succ]
    have hX : 0 ≤ (max (3 / π) Cu * Λ ^ 2) ^ s * Ew p nn F (b - 1) wm h := mul_nonneg (pow_nonneg hCL _) hE0
    have hc : Cu * Λ ^ 2 ≤ max (3 / π) Cu * Λ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
    calc Cu * Λ ^ 2 * ((max (3 / π) Cu * Λ ^ 2) ^ s * Ew p nn F (b - 1) wm h)
        ≤ max (3 / π) Cu * Λ ^ 2 * ((max (3 / π) Cu * Λ ^ 2) ^ s * Ew p nn F (b - 1) wm h) :=
          mul_le_mul_of_nonneg_right hc hX
      _ = (max (3 / π) Cu * Λ ^ 2) ^ s * (max (3 / π) Cu * Λ ^ 2) * Ew p nn F (b - 1) wm h := by ring

/- English proof (translation)
Establish `hCL : 0 ≤ C₂ * Λ ^ 2` using `by positivity`. Introduce `γ`. Proceed by induction on `γ using List.reverseRecOn with`. Consider the case `nil`. Introduce `j hj _ w hw hl`.

Establish `hj0 : j = 0` using `by simpa [D.IsLocPt, D.ptSize] using hj.2.symm`. Substitute `hj0` using the available equality. Conclude with `⟨w, isExt_self hw (by omega), by simp⟩`. Consider the case `append_singleton h x ih`. Introduce `j hj hjr w hw hl`.

Take `⟨s, t⟩` from `x`. Take `⟨hblk, hsz⟩` from `hj`. Establish `hsz' : D.ptSize h + s = j` using `by simpa [D.ptSize] using hsz`. Establish `hst` using `hblk (s, t) (by simp)`. Establish `hh : D.IsLocPt h (D.ptSize h)` using `⟨fun bl hbl => hblk bl (by simp [hbl]), rfl⟩`.

Use `set i := D.ptSize h with hi`. Establish `hlS : w.length + s * K ≤ N`. Establish `: s * K ≤ j * K` using `Nat.mul_le_mul_right K (by omega)`. Use linear arithmetic over natural numbers and integers. Take `⟨w₁, hw₁, hE₁⟩` from `hL (i + 1) s (by omega) hst.1 (by omega) h (by simpa using hh) w hw hlS t hst.2`.

Rewrite `hE₁` using `[show i + 1 + s - 1 = j by omega, show i + 1 - 1 = i by omega]`. Establish `hl₁ : w₁.length + i * K ≤ N`. Establish `h1` using `isExt_len hw₁`. Establish `: j * K = i * K + s * K` using `by rw [← hsz', Nat.add_mul]`. Use linear arithmetic over natural numbers and integers.

Take `⟨w₂, hw₂, hE₂⟩` from `ih i hh (by omega) w₁ (admissible_word_of_extension hw hw₁) hl₁`. Use `⟨w₂, ?_, hE₁.trans ?_⟩` and prove the remaining obligations. Use `isExt_mono (isExt_trans hw₁ hw₂) (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[← hsz', Nat.add_mul, add_comm]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem corollary_s_induction {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ) (C₂ : ℝ) (hC : 0 ≤ C₂)
    (hL : LemmaS p nn F Y Λ K N C₂) :
    ∀ γ : C.LPt, ∀ j, D.IsLocPt γ j → j ≤ P.r + 1 → ∀ w, AdmW P p.l0 Y w → w.length + j * K ≤ N →
      ∃ w', IsExt P p.l0 Y N (j * K) w w' ∧ Ew p nn F j w γ ≤ (C₂ * Λ ^ 2) ^ j * Ew p nn F 0 w' [] := by
  have hCL : 0 ≤ C₂ * Λ ^ 2 := by positivity
  intro γ
  induction γ using List.reverseRecOn with
  | nil =>
    intro j hj _ w hw hl
    have hj0 : j = 0 := by simpa [D.IsLocPt, D.ptSize] using hj.2.symm
    subst hj0
    exact ⟨w, isExt_self hw (by omega), by simp⟩
  | append_singleton h x ih =>
    intro j hj hjr w hw hl
    obtain ⟨s, t⟩ := x
    obtain ⟨hblk, hsz⟩ := hj
    have hsz' : D.ptSize h + s = j := by simpa [D.ptSize] using hsz
    have hst := hblk (s, t) (by simp)
    have hh : D.IsLocPt h (D.ptSize h) := ⟨fun bl hbl => hblk bl (by simp [hbl]), rfl⟩
    set i := D.ptSize h with hi
    have hlS : w.length + s * K ≤ N := by
      have : s * K ≤ j * K := Nat.mul_le_mul_right K (by omega)
      omega
    obtain ⟨w₁, hw₁, hE₁⟩ := hL (i + 1) s (by omega) hst.1 (by omega) h (by simpa using hh) w hw hlS t hst.2
    rw [show i + 1 + s - 1 = j by omega, show i + 1 - 1 = i by omega] at hE₁
    have hl₁ : w₁.length + i * K ≤ N := by
      have h1 := isExt_len hw₁
      have : j * K = i * K + s * K := by rw [← hsz', Nat.add_mul]
      omega
    obtain ⟨w₂, hw₂, hE₂⟩ := ih i hh (by omega) w₁ (admissible_word_of_extension hw hw₁) hl₁
    refine ⟨w₂, ?_, hE₁.trans ?_⟩
    · refine isExt_mono (isExt_trans hw₁ hw₂) (le_of_eq ?_)
      rw [← hsz', Nat.add_mul, add_comm]
    · calc (C₂ * Λ ^ 2) ^ s * Ew p nn F i w₁ h
          ≤ (C₂ * Λ ^ 2) ^ s * ((C₂ * Λ ^ 2) ^ i * Ew p nn F 0 w₂ []) :=
            mul_le_mul_of_nonneg_left hE₂ (pow_nonneg hCL _)
        _ = (C₂ * Λ ^ 2) ^ j * Ew p nn F 0 w₂ [] := by rw [← hsz', pow_add]; ring

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P p nn F Y Λ K N C₂ hN hC _ hL γ hγ`. Conclude with `corollary_s_induction p nn F Y Λ K N C₂ hC hL γ (P.r + 1) hγ le_rfl [] admissible_word_nil (by simpa using hN)`.
-/
theorem corSOfLemmaS : CorSOfLemmaS := by
  intro Wp Wq _ _ _ _ _ _ P p nn F Y Λ K N C₂ hN hC _ hL γ hγ
  exact corollary_s_induction p nn F Y Λ K N C₂ hC hL γ (P.r + 1) hγ le_rfl [] admissible_word_nil (by simpa using hN)

end

end Formalism.FourierDecayAlt.P.TBBx1

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.TBBx1.stepOne`.
-/
theorem Formalism.FourierDecayAlt.P.lemma_s_induction_base : Formalism.FourierDecayAlt.TBB.StepOne := Formalism.FourierDecayAlt.P.TBBx1.stepOne
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.TBBx1.stepUp`.
-/
theorem Formalism.FourierDecayAlt.P.lemma_s_induction_up : Formalism.FourierDecayAlt.TBB.StepUp := Formalism.FourierDecayAlt.P.TBBx1.stepUp
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.TBBx1.lemmaSOfSteps`.
-/
theorem Formalism.FourierDecayAlt.P.lemma_s_of_parts : Formalism.FourierDecayAlt.TBB.LemmaSOfSteps := Formalism.FourierDecayAlt.P.TBBx1.lemmaSOfSteps
/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.TBBx1.corSOfLemmaS`.
-/
theorem Formalism.FourierDecayAlt.P.corSOfLemmaS_statement : Formalism.FourierDecayAlt.TBB.CorSOfLemmaS := Formalism.FourierDecayAlt.P.TBBx1.corSOfLemmaS
