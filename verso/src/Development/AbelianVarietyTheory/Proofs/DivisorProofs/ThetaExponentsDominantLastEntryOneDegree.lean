import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H}

/- English proof (translation)
Establish `hE : (H.rt : E) ^ 2 = -(H.d : E)`. Use `congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq` as an intermediate fact. Simplify using `using this`. Establish `hsq : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2`. Rewrite using `[H.sqrt_neg_disc_sq, ← map_pow, hE]`.

Simplify using the standard rewrite rules. Establish `hneg : τ (H.rt : E) = -H.rt0` using `(sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left h`. Establish `hre : H.rt0.re = 0`. Establish `h2` using `H.sqrt_neg_disc_sq`. Establish `hr` using `congrArg Complex.re h2`.

Establish `hi` using `congrArg Complex.im h2`. Simplify using `only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im] at hr hi`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Assume the negation of the conclusion as `hne`. Establish `him : H.rt0.im = 0`.

Establish `: H.rt0.re * H.rt0.im = 0` using `by linarith`. Conclude with `(mul_eq_zero.1 this).resolve_left hne`. Rewrite `hr` using `[him]`. Use polynomial arithmetic with `[mul_self_nonneg H.rt0.re]`. Use `show (starRingEnd ℂ) (τ (H.rt : E)) = H.rt0`.

Rewrite using `[hneg]`. Apply the tactic sequence `apply Complex.ext <;> simp [hre]`.
-/
theorem conjEmb_rt_of_not {τ : E →+* ℂ} (h : ¬ τ (H.rt : E) = H.rt0) :
    conjEmb τ (H.rt : E) = H.rt0 := by
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
    simpa using this
  have hsq : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow, hE]; simp
  have hneg : τ (H.rt : E) = -H.rt0 := (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left h
  have hre : H.rt0.re = 0 := by
    have h2 := H.sqrt_neg_disc_sq
    have hr := congrArg Complex.re h2
    have hi := congrArg Complex.im h2
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im] at hr hi
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    by_contra hne
    have him : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [him] at hr
    nlinarith [mul_self_nonneg H.rt0.re]
  show (starRingEnd ℂ) (τ (H.rt : E)) = H.rt0
  rw [hneg]
  apply Complex.ext <;> simp [hre]

/- English proof (translation)
Distinguish the cases in `h : σ (H.rt : E) = H.rt0`. Conclude with `Or.inl ⟨⟨σ, h⟩, rfl⟩`. Conclude with `Or.inr ⟨⟨conjEmb σ, conjEmb_rt_of_not h⟩, (GlobalTheory.AllWt.conjEmb_conjEmb σ).symm⟩`.
-/
theorem psi_or_conj (σ : E →+* ℂ) : (∃ τ : Psi H, σ = τ.1) ∨ ∃ τ : Psi H, σ = conjEmb τ.1 := by
  by_cases h : σ (H.rt : E) = H.rt0
  · exact Or.inl ⟨⟨σ, h⟩, rfl⟩
  · exact Or.inr ⟨⟨conjEmb σ, conjEmb_rt_of_not h⟩, (GlobalTheory.AllWt.conjEmb_conjEmb σ).symm⟩

/- English proof (translation)
Establish `: 0 < Fintype.card (E →+* ℂ)`. Rewrite using `[NumberField.Embeddings.card]`. Conclude with `Module.finrank_pos`. Take `⟨σ⟩` from `Fintype.card_pos_iff.1 this`. Apply the tactic sequence `rcases psi_or_conj (H := H) σ with ⟨τ, -⟩ | ⟨τ, -⟩ <;> exact ⟨τ⟩`.
-/
theorem psi_nonempty : Nonempty (Psi H) := by
  have : 0 < Fintype.card (E →+* ℂ) := by
    rw [NumberField.Embeddings.card]; exact Module.finrank_pos
  obtain ⟨σ⟩ := Fintype.card_pos_iff.1 this
  rcases psi_or_conj (H := H) σ with ⟨τ, -⟩ | ⟨τ, -⟩ <;> exact ⟨τ⟩

/- English proof (translation)
Use `set P := (Finset.univ : Finset (E →+* ℂ)).filter (fun τ => τ (H.rt : E) = H.rt0) with hP`. Use `set Q := (Finset.univ : Finset (E →+* ℂ)).filter (fun τ => ¬ τ (H.rt : E) = H.rt0) with hQ`. Establish `hcard : Q.card = P.card`. Use `Finset.card_nbij' conjEmb conjEmb ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a ha`.

Simplify using `only [hQ, hP, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢`. Conclude with `conjEmb_rt_of_not ha`. Introduce `a ha`. Simplify using `only [hQ, hP, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢`. Conclude with `GlobalTheory.AllWt.conj_not_mem ⟨a, ha⟩`.

Introduce `a _`. Conclude with `GlobalTheory.AllWt.conjEmb_conjEmb a`. Introduce `a _`. Conclude with `GlobalTheory.AllWt.conjEmb_conjEmb a`. Establish `htot : P.card + Q.card = Module.finrank ℚ E`.

Rewrite using `[← NumberField.Embeddings.card E ℂ, ← Finset.card_univ]`. Conclude with `Finset.card_filter_add_card_filter_not _`. Establish `hsum : ∑ τ : E →+* ℂ, Dw.mult τ = P.card * Dw.p + Q.card * Dw.q`. Simplify using `only [Datum.mult]`. Rewrite using `[Finset.sum_ite]`.

Simplify using `[Finset.sum_const, hP, hQ]`. Rewrite using `[hsum, hcard, ← htot, hcard, ← two_mul, Nat.mul_div_cancel_left _ (by norm_num)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_mult : ∑ τ : E →+* ℂ, Dw.mult τ = (Module.finrank ℚ E / 2) * (Dw.p + Dw.q) := by
  classical
  set P := (Finset.univ : Finset (E →+* ℂ)).filter (fun τ => τ (H.rt : E) = H.rt0) with hP
  set Q := (Finset.univ : Finset (E →+* ℂ)).filter (fun τ => ¬ τ (H.rt : E) = H.rt0) with hQ
  have hcard : Q.card = P.card := by
    refine Finset.card_nbij' conjEmb conjEmb ?_ ?_ ?_ ?_
    · intro a ha
      simp only [hQ, hP, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
      exact conjEmb_rt_of_not ha
    · intro a ha
      simp only [hQ, hP, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
      exact GlobalTheory.AllWt.conj_not_mem ⟨a, ha⟩
    · intro a _; exact GlobalTheory.AllWt.conjEmb_conjEmb a
    · intro a _; exact GlobalTheory.AllWt.conjEmb_conjEmb a
  have htot : P.card + Q.card = Module.finrank ℚ E := by
    rw [← NumberField.Embeddings.card E ℂ, ← Finset.card_univ]
    exact Finset.card_filter_add_card_filter_not _
  have hsum : ∑ τ : E →+* ℂ, Dw.mult τ = P.card * Dw.p + Q.card * Dw.q := by
    simp only [Datum.mult]
    rw [Finset.sum_ite]
    simp [Finset.sum_const, hP, hQ]
  rw [hsum, hcard, ← htot, hcard, ← two_mul, Nat.mul_div_cancel_left _ (by norm_num)]
  ring

variable (Dw) in

abbrev thExpZ (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) : (E →+* ℂ) × ℕ → ℤ :=
  (GlobalTheory.AllWt.wtOf Dw (u + GlobalTheory.FlatLine.parWt Dw (shift Dw u n)) ((n / 2 : ℕ) : ℤ)).1

/- English proof (translation)
Rewrite using `[thExpZ, GlobalTheory.AllWt.wtOf_big _ _ τ i hi]`. Simplify using `only [Pi.add_apply, GlobalTheory.FlatLine.parWt, shift, dif_pos (show 0 < Dw.p by omega)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thExpZ_big (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (τ : Psi H) (i : ℕ) (hi : i < Dw.p) :
    thExpZ Dw u n (τ.1, i) = u τ ⟨i, by omega⟩ + 1 - u τ ⟨Dw.p - 1, by omega⟩ := by
  rw [thExpZ, GlobalTheory.AllWt.wtOf_big _ _ τ i hi]
  simp only [Pi.add_apply, GlobalTheory.FlatLine.parWt, shift, dif_pos (show 0 < Dw.p by omega)]
  ring

/- English proof (translation)
Simplify using `only [thExpZ, GlobalTheory.AllWt.wtOf, dif_pos τ.2, dif_neg (not_lt.2 hi)]`.
-/
theorem thExpZ_big_ge (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (τ : Psi H) (i : ℕ) (hi : Dw.p ≤ i) :
    thExpZ Dw u n (τ.1, i) = 0 := by
  simp only [thExpZ, GlobalTheory.AllWt.wtOf, dif_pos τ.2, dif_neg (not_lt.2 hi)]

/- English proof (translation)
Rewrite using `[thExpZ, GlobalTheory.AllWt.wtOf_small _ _ τ i hi]`. Simplify using `only [Pi.add_apply, GlobalTheory.FlatLine.parWt, shift, dif_pos hp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thExpZ_small (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (hp : 0 < Dw.p) (τ : Psi H) (i : ℕ) (hi : i < Dw.q) :
    thExpZ Dw u n (conjEmb τ.1, i) =
      u τ ⟨Dw.p - 1, by omega⟩ - u τ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ - 2 * ((n / 2 : ℕ) : ℤ) - 1 := by
  rw [thExpZ, GlobalTheory.AllWt.wtOf_small _ _ τ i hi]
  simp only [Pi.add_apply, GlobalTheory.FlatLine.parWt, shift, dif_pos hp]
  ring

/- English proof (translation)
Establish `h' : conjEmb (conjEmb τ.1) (H.rt : E) = H.rt0`. Rewrite using `[GlobalTheory.AllWt.conjEmb_conjEmb]`. Conclude with `τ.2`. Simplify using `only [thExpZ, GlobalTheory.AllWt.wtOf, dif_neg (GlobalTheory.AllWt.conj_not_mem τ), dif_pos h', dif_neg (not_lt.2 hi)]`.
-/
theorem thExpZ_small_ge (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (τ : Psi H) (i : ℕ) (hi : Dw.q ≤ i) :
    thExpZ Dw u n (conjEmb τ.1, i) = 0 := by
  have h' : conjEmb (conjEmb τ.1) (H.rt : E) = H.rt0 := by
    rw [GlobalTheory.AllWt.conjEmb_conjEmb]; exact τ.2
  simp only [thExpZ, GlobalTheory.AllWt.wtOf, dif_neg (GlobalTheory.AllWt.conj_not_mem τ), dif_pos h', dif_neg (not_lt.2 hi)]

/- English proof (translation)
Establish `hp0 : 0 < Dw.p` using `hp`. Take `⟨τ0⟩` from `psi_nonempty (H := H)`. Establish `hb0 : 0 ≤ b` using `(abs_nonneg _).trans (hb τ0 ⟨0, by omega⟩)`. Establish `hup : ∀ τ i, (u τ i : ℝ) ≤ b` using `fun τ i => (le_abs_self _).trans (hb τ i)`. Establish `hlo : ∀ τ i, -b ≤ (u τ i : ℝ)` using `fun τ i => by`.

Use `neg_abs_le (u τ i : ℝ)` as an intermediate fact. Combine the linear relations using `[hb τ i]`. Establish `hm : 2 * ((n / 2 : ℕ) : ℤ) = n` using `by obtain ⟨k, rfl⟩ := hn; omega`. Establish `F1 : ∀ x, 0 ≤ thExpZ Dw u n x`. Introduce and unpack `⟨σ, i⟩`.

Break down `psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩` into its components or cases. Distinguish the cases in `hi : i < Dw.p`. Rewrite using `[thExpZ_big u n τ i hi]`. Use `hu τ (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p - 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[thExpZ_big_ge u n τ i (by omega)]`. Distinguish the cases in `hi : i < Dw.q`. Rewrite using `[thExpZ_small u n hp0 τ i hi]`. Establish `h1` using `hu τ (show (⟨Dw.p, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from Fin.mk_le_mk.2 (by omega))`. Establish `h2` using `hgap τ ⟨Dw.p - 1, by omega⟩ ⟨Dw.p, by omega⟩ (by simp; omega) rfl`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[thExpZ_small_ge u n τ i (by omega)]`. Establish `F2 : ∀ x, (thExpZ Dw u n x : ℝ) ≤ 2 * b + 1`. Introduce and unpack `⟨σ, i⟩`. Break down `psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩` into its components or cases.

Distinguish the cases in `hi : i < Dw.p`. Rewrite using `[thExpZ_big u n τ i hi]`. Use `push_cast`. Combine the linear relations using `[hup τ ⟨i, by omega⟩, hlo τ ⟨Dw.p - 1, by omega⟩]`. Rewrite using `[thExpZ_big_ge u n τ i (by omega)]; push_cast; linarith`.

Distinguish the cases in `hi : i < Dw.q`. Rewrite using `[thExpZ_small u n hp0 τ i hi, hm]`. Use `push_cast`. Establish `: (0 : ℝ) ≤ (n : ℝ)` using `Nat.cast_nonneg _`. Combine the linear relations using `[hup τ ⟨Dw.p - 1, by omega⟩, hlo τ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩]`.

Rewrite using `[thExpZ_small_ge u n τ i (by omega)]; push_cast; linarith`. Establish `F3 : ∀ σ i, thExpZ Dw u n (σ, i + 1) ≤ thExpZ Dw u n (σ, i)`. Introduce `σ i`. Break down `psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩` into its components or cases. Distinguish the cases in `hi : i + 1 < Dw.p`.

Rewrite using `[thExpZ_big u n τ _ hi, thExpZ_big u n τ i (by omega)]`. Use `hu τ (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨i + 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[thExpZ_big_ge u n τ (i + 1) (by omega)]; exact F1 _`. Distinguish the cases in `hi : i + 1 < Dw.q`.

Rewrite using `[thExpZ_small u n hp0 τ _ hi, thExpZ_small u n hp0 τ i (by omega)]`. Use `hu τ (show (⟨Dw.p + (Dw.q - 1 - (i + 1)), by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from Fin.mk_le_mk.2 (by omega))` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[thExpZ_small_ge u n τ (i + 1) (by omega)]; exact F1 _`. Establish `hcast : ∀ x, (thA Dw u n x : ℝ) = (thExpZ Dw u n x : ℝ)` using `fun x => by`.

Establish `h` using `Int.toNat_of_nonneg (F1 x)`. Use `show (((thExpZ Dw u n x).toNat : ℕ) : ℝ) = _`. Rewrite using `[← h]`. Use `norm_cast`. Establish `hbound : ∀ x, (thA Dw u n x : ℝ) ≤ 2 * b + 1` using `fun x => (hcast x).trans_le (F2 x)`.

Use `⟨⟨fun σ => antitone_nat_of_succ_le fun i => Int.toNat_le_toNat (F3 σ i), hn⟩, ?_, ?_, hbound, ?_⟩` and prove the remaining obligations. Use `Prod.ext (funext fun x => ?_) ?_` and prove the remaining obligations. Conclude with `Int.toNat_of_nonneg (F1 x)`. Use `show (n : ℤ) = 2 * ((n / 2 : ℕ) : ℤ)`. Use linear arithmetic over natural numbers and integers.

Introduce `σ hσ _`. Establish `hmul : Dw.mult σ = Dw.p` using `if_pos hσ`. Rewrite using `[hmul]`. Establish `h1 : thExpZ Dw u n (σ, Dw.p - 1) = 1` using `(thExpZ_big u n ⟨σ, hσ⟩ (Dw.p - 1) (by omega)).trans (by ring)`. Use `show 0 < (thExpZ Dw u n (σ, Dw.p - 1)).toNat`.

Rewrite using `[h1]`. Evaluate the decidable proposition. Establish `hDF : (Formalism.L2.Pj.DF Dw (thA Dw u n) : ℝ) ≤ ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (2 * b + 1)`. Unfold `Formalism.L2.Pj.DF`. Use `push_cast`.

Use `Finset.sum_le_sum fun τ _ => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite `hDF` using `[← Finset.sum_mul]`. Establish `hs : (∑ τ : E →+* ℂ, (Dw.mult τ : ℝ)) = ((Module.finrank ℚ E / 2 : ℕ) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ)`. Rewrite using `[← Nat.cast_sum, sum_mult, Nat.cast_mul]`.

Rewrite `hDF` using `[hs]`. Conclude with `hDF`.
-/
theorem thA_dominant_lastPos_degree (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (b : ℝ) (hp : 1 ≤ Dw.p)
    (hn : Even n) (hu : ∀ τ, Antitone (u τ))
    (hgap : ∀ τ (i j : Fin (Dw.p + Dw.q)), (i : ℕ) + 1 = Dw.p → (j : ℕ) = Dw.p → (n : ℤ) + 1 ≤ u τ i - u τ j)
    (hb : ∀ τ i, |(u τ i : ℝ)| ≤ b) :
    Formalism.L2.Pj.Dom (thA Dw u n) n ∧
      Formalism.L2.Pj.wtZ (thA Dw u n) n =
        GlobalTheory.AllWt.wtOf Dw (u + GlobalTheory.FlatLine.parWt Dw (shift Dw u n)) ((n / 2 : ℕ) : ℤ) ∧
      Formalism.L2.Pj.LastPos Dw (thA Dw u n) ∧ (∀ x, (thA Dw u n x : ℝ) ≤ 2 * b + 1) ∧
      (Formalism.L2.Pj.DF Dw (thA Dw u n) : ℝ) ≤ (Module.finrank ℚ E / 2 : ℕ) * (Dw.p + Dw.q : ℕ) * (2 * b + 1) := by
  have hp0 : 0 < Dw.p := hp
  obtain ⟨τ0⟩ := psi_nonempty (H := H)
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hb τ0 ⟨0, by omega⟩)
  have hup : ∀ τ i, (u τ i : ℝ) ≤ b := fun τ i => (le_abs_self _).trans (hb τ i)
  have hlo : ∀ τ i, -b ≤ (u τ i : ℝ) := fun τ i => by
    have := neg_abs_le (u τ i : ℝ); linarith [hb τ i]
  have hm : 2 * ((n / 2 : ℕ) : ℤ) = n := by obtain ⟨k, rfl⟩ := hn; omega

  have F1 : ∀ x, 0 ≤ thExpZ Dw u n x := by
    rintro ⟨σ, i⟩
    rcases psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · by_cases hi : i < Dw.p
      · rw [thExpZ_big u n τ i hi]
        have := hu τ (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p - 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))
        omega
      · rw [thExpZ_big_ge u n τ i (by omega)]
    · by_cases hi : i < Dw.q
      · rw [thExpZ_small u n hp0 τ i hi]
        have h1 := hu τ (show (⟨Dw.p, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from
          Fin.mk_le_mk.2 (by omega))
        have h2 := hgap τ ⟨Dw.p - 1, by omega⟩ ⟨Dw.p, by omega⟩ (by simp; omega) rfl
        omega
      · rw [thExpZ_small_ge u n τ i (by omega)]

  have F2 : ∀ x, (thExpZ Dw u n x : ℝ) ≤ 2 * b + 1 := by
    rintro ⟨σ, i⟩
    rcases psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · by_cases hi : i < Dw.p
      · rw [thExpZ_big u n τ i hi]; push_cast
        linarith [hup τ ⟨i, by omega⟩, hlo τ ⟨Dw.p - 1, by omega⟩]
      · rw [thExpZ_big_ge u n τ i (by omega)]; push_cast; linarith
    · by_cases hi : i < Dw.q
      · rw [thExpZ_small u n hp0 τ i hi, hm]; push_cast
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        linarith [hup τ ⟨Dw.p - 1, by omega⟩, hlo τ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩]
      · rw [thExpZ_small_ge u n τ i (by omega)]; push_cast; linarith

  have F3 : ∀ σ i, thExpZ Dw u n (σ, i + 1) ≤ thExpZ Dw u n (σ, i) := by
    intro σ i
    rcases psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · by_cases hi : i + 1 < Dw.p
      · rw [thExpZ_big u n τ _ hi, thExpZ_big u n τ i (by omega)]
        have := hu τ (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨i + 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))
        omega
      · rw [thExpZ_big_ge u n τ (i + 1) (by omega)]; exact F1 _
    · by_cases hi : i + 1 < Dw.q
      · rw [thExpZ_small u n hp0 τ _ hi, thExpZ_small u n hp0 τ i (by omega)]
        have := hu τ (show (⟨Dw.p + (Dw.q - 1 - (i + 1)), by omega⟩ : Fin (Dw.p + Dw.q)) ≤
          ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from Fin.mk_le_mk.2 (by omega))
        omega
      · rw [thExpZ_small_ge u n τ (i + 1) (by omega)]; exact F1 _
  have hcast : ∀ x, (thA Dw u n x : ℝ) = (thExpZ Dw u n x : ℝ) := fun x => by
    have h := Int.toNat_of_nonneg (F1 x)
    show (((thExpZ Dw u n x).toNat : ℕ) : ℝ) = _
    rw [← h]; norm_cast
  have hbound : ∀ x, (thA Dw u n x : ℝ) ≤ 2 * b + 1 := fun x => (hcast x).trans_le (F2 x)
  refine ⟨⟨fun σ => antitone_nat_of_succ_le fun i => Int.toNat_le_toNat (F3 σ i), hn⟩, ?_, ?_, hbound, ?_⟩
  · refine Prod.ext (funext fun x => ?_) ?_
    · exact Int.toNat_of_nonneg (F1 x)
    · show (n : ℤ) = 2 * ((n / 2 : ℕ) : ℤ)
      omega
  · intro σ hσ _
    have hmul : Dw.mult σ = Dw.p := if_pos hσ
    rw [hmul]
    have h1 : thExpZ Dw u n (σ, Dw.p - 1) = 1 :=
      (thExpZ_big u n ⟨σ, hσ⟩ (Dw.p - 1) (by omega)).trans (by ring)
    show 0 < (thExpZ Dw u n (σ, Dw.p - 1)).toNat
    rw [h1]; decide
  · have hDF : (Formalism.L2.Pj.DF Dw (thA Dw u n) : ℝ) ≤ ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (2 * b + 1) := by
      unfold Formalism.L2.Pj.DF; push_cast
      refine Finset.sum_le_sum fun τ _ => ?_
      calc ∑ i : Fin (Dw.mult τ), (thA Dw u n (τ, i) : ℝ) ≤ ∑ _i : Fin (Dw.mult τ), (2 * b + 1) :=
            Finset.sum_le_sum fun i _ => hbound (τ, i)
        _ = _ := by simp [mul_add]
    rw [← Finset.sum_mul] at hDF
    have hs : (∑ τ : E →+* ℂ, (Dw.mult τ : ℝ)) =
        ((Module.finrank ℚ E / 2 : ℕ) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) := by
      rw [← Nat.cast_sum, sum_mult, Nat.cast_mul]
    rw [hs] at hDF
    exact hDF

end GlobalTheory.RefSum

/- English proof (translation)
The claim follows from `GlobalTheory.RefSum.thA_dominant_lastPos_degree`.
-/
example : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (u : Weight Dw) (n : ℕ) (b : ℝ), 1 ≤ Dw.p → Even n → (∀ τ, Antitone (u τ)) → (∀ τ (i j : Fin (Dw.p + Dw.q)), (i : ℕ) + 1 = Dw.p → (j : ℕ) = Dw.p → (n : ℤ) + 1 ≤ u τ i - u τ j) → (∀ τ i, |(u τ i : ℝ)| ≤ b) → Dom (thA Dw u n) n ∧ wtZ (thA Dw u n) n = wtOf Dw (u + parWt Dw (shift Dw u n)) ((n / 2 : ℕ) : ℤ) ∧ LastPos Dw (thA Dw u n) ∧ (∀ x, (thA Dw u n x : ℝ) ≤ 2 * b + 1) ∧ (DF Dw (thA Dw u n) : ℝ) ≤ (Module.finrank ℚ E / 2 : ℕ) * (Dw.p + Dw.q : ℕ) * (2 * b + 1) := GlobalTheory.RefSum.thA_dominant_lastPos_degree
