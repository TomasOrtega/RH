import Formalism.HermitianCurvature.StatementJ

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J

namespace Formalism.FourierDecayAlt.P.Jx7

section frames
/- English proof (translation)
Introduce `r i s C rd g N I A TT hi hs hrd hg`. Take `⟨j, rfl⟩ : ∃ j, i = j + 1` from `⟨i - 1, by omega⟩`. Take `⟨t, rfl⟩ : ∃ t, s = t + 1` from `⟨s - 1, by omega⟩`. Establish `hpi : (0 : ℝ) < 2 * Real.pi` using `by positivity`. Establish `e1 : 2 * r + 2 - 1 = 2 * r + 1` using `by omega`.

Establish `e2 : 2 * (j + 1 - 1) + (t + 1) - 1 = 2 * j + t` using `by omega`. Establish `e3 : 2 * (j + 1) - 1 = 2 * j + 1` using `by omega`. Establish `e4 : 2 * (j + 1) - 2 = 2 * j` using `by omega`. Establish `e5 : 2 * (j + 1 - 1) = 2 * j` using `by omega`. Prove the components needed by the constructor for the conclusion.

Unfold `Sz.lamThreshold Sz.lamHat S6.nuBlock`. Rewrite using `[e1, e2]`. Establish `hz : rd ^ ((2 * (r : ℤ) + 3 - 2 * ((j + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ)) + 1) = rd ^ (2 * r + 1) / rd ^ (2 * j + t)`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hrd.ne']`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hz]`. Establish `hb : C * (2 * Real.pi / g) * N / I = C * (2 * Real.pi / rd) * N / (g * I) * rd`. Distinguish the cases in `hI : I = 0`.

Simplify using `[hI]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hb, mul_pow]`. Generalize the expression as in `(C * (2 * Real.pi / rd) * N / (g * I)) ^ (2 * j + t) = Z`. Simplify using `only [div_pow]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Unfold `Sz.lamPrimeSq Sz.lamPrimeHat S6.nuBlock`. Rewrite using `[e1, e3, e4, e5]`. Establish `hz : rd ^ (2 * (r : ℤ) + 3 - 2 * ((j + 1 : ℕ) : ℤ) - ((r : ℤ) + 2 - ((j + 1 : ℕ) : ℤ))) = rd ^ r / rd ^ j`.

Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hrd.ne']`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hz]`.

Establish `hbpos : 0 ≤ g * (rd ^ r / rd ^ j)` using `by positivity`. Rewrite using `[← Real.sqrt_sq hbpos, ← Real.sqrt_mul' _ (sq_nonneg _)]`. Use `congr 1`. Establish `hb : C * (2 * Real.pi / rd) * N / I = C * N / I * (2 * Real.pi / rd)` using `by ring`. Rewrite using `[hb, mul_pow (C * N / I)]`.

Generalize the expression as in `(C * N / I) ^ (2 * j) = Z`. Generalize the expression as in `(√TT)⁻¹ = S`. Simplify using `only [div_pow, mul_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem t_FrameProducts : FrameProducts := by
  intro r i s C rd g N I A TT hi hs hrd hg
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have e1 : 2 * r + 2 - 1 = 2 * r + 1 := by omega
  have e2 : 2 * (j + 1 - 1) + (t + 1) - 1 = 2 * j + t := by omega
  have e3 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  have e4 : 2 * (j + 1) - 2 = 2 * j := by omega
  have e5 : 2 * (j + 1 - 1) = 2 * j := by omega
  constructor
  · unfold Sz.lamThreshold Sz.lamHat S6.nuBlock
    rw [e1, e2]
    have hz : rd ^ ((2 * (r : ℤ) + 3 - 2 * ((j + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ)) + 1) =
        rd ^ (2 * r + 1) / rd ^ (2 * j + t) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hrd.ne']
      congr 1; push_cast; ring
    rw [hz]
    have hb : C * (2 * Real.pi / g) * N / I = C * (2 * Real.pi / rd) * N / (g * I) * rd := by
      by_cases hI : I = 0
      · simp [hI]
      · field_simp
    rw [hb, mul_pow]
    generalize (C * (2 * Real.pi / rd) * N / (g * I)) ^ (2 * j + t) = Z
    simp only [div_pow]
    field_simp
    ring
  · unfold Sz.lamPrimeSq Sz.lamPrimeHat S6.nuBlock
    rw [e1, e3, e4, e5]
    have hz : rd ^ (2 * (r : ℤ) + 3 - 2 * ((j + 1 : ℕ) : ℤ) - ((r : ℤ) + 2 - ((j + 1 : ℕ) : ℤ))) =
        rd ^ r / rd ^ j := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hrd.ne']
      congr 1; push_cast; ring
    rw [hz]
    have hbpos : 0 ≤ g * (rd ^ r / rd ^ j) := by positivity
    rw [← Real.sqrt_sq hbpos, ← Real.sqrt_mul' _ (sq_nonneg _)]
    congr 1
    have hb : C * (2 * Real.pi / rd) * N / I = C * N / I * (2 * Real.pi / rd) := by ring
    rw [hb, mul_pow (C * N / I)]
    generalize (C * N / I) ^ (2 * j) = Z
    generalize (√TT)⁻¹ = S
    simp only [div_pow, mul_pow]
    field_simp
    ring

end frames

section sizes
open scoped nonZeroDivisors
/- English proof (translation)
Unfold `S6.rd`. Apply `Real.rpow_pos_of_pos` to reduce the goal to its premises. Establish `: (0 : ℤ) < |discr E|` using `abs_pos.2 (discr_ne_zero E)`. Conclude with `this` after adjusting the coercions.
-/
lemma rd_pos (E : Type) [Field E] [NumberField E] [IsCMField E] : 0 < S6.rd E := by
  unfold S6.rd
  apply Real.rpow_pos_of_pos
  have : (0 : ℤ) < |discr E| := abs_pos.2 (discr_ne_zero E)
  exact_mod_cast this

/- English proof (translation)
Introduce `h`. Establish `h1` using `hN E g k ν hg`. Rewrite `h1` using `[h]`. Establish `hpos : 0 < ((g : ℝ) ^ k * S6.rd E ^ ν) ^ S6.deg E`. Use `rd_pos E` as an intermediate fact.

Establish `hg' : (0 : ℝ) < g` using `by exact_mod_cast hg`. Check the signs of the components of the expression. Simplify using `at h1`. Rewrite `hpos` using `[← h1]`. Conclude with `lt_irrefl _ hpos`.
-/
lemma idl_ne_zero (hN : S6.NormIdl) (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (k ν : ℤ)
    (hg : 0 < g) : S6.idl E g k ν ≠ 0 := by
  intro h
  have h1 := hN E g k ν hg
  rw [h] at h1
  have hpos : 0 < ((g : ℝ) ^ k * S6.rd E ^ ν) ^ S6.deg E := by
    have := rd_pos E
    have hg' : (0 : ℝ) < g := by exact_mod_cast hg
    positivity
  simp at h1
  rw [← h1] at hpos
  exact lt_irrefl _ hpos

/- English proof (translation)
Rewrite using `[hN E g (-1) (-μ) hg, ← inv_pow]`. Use `congr 1`. Rewrite using `[zpow_neg, zpow_neg, zpow_one, mul_inv]`.
-/
lemma sqrt_idl (hN : S6.NormIdl) (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (μ : ℤ)
    (hg : 0 < g) : √(FractionalIdeal.absNorm (S6.idl E g (-1) (-μ)) : ℝ) =
      (((g : ℝ) * S6.rd E ^ μ) ^ S6.deg E)⁻¹ := by
  rw [hN E g (-1) (-μ) hg, ← inv_pow]
  congr 1
  rw [zpow_neg, zpow_neg, zpow_one, mul_inv]

/- English proof (translation)
Introduce `hL hI hN E _ _ _ hU g r b s hg`. Take `⟨-, -, -, -, f5, -, -, -, -, -, -, -⟩` from `hL E hU g (S6.nuBlock r b 1) 1 hg`. Take `⟨-, -, -, -, k5, -, k7, -, -, -, -, -⟩` from `hL E hU g (S6.nuBlock r b s) s hg`. Use `⟨fun l hl => f5 hl, fun l hl => k5 hl, fun l hl => k7 hl, idl_ne_zero hN E g _ _ hg, idl_ne_zero hN E g _ _ hg, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `(hI E g r b ((s + 1 : ℕ) : ℤ)).1` as an intermediate fact.

Rewrite using `[this]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Unfold `S6.dualIdl`.

Rewrite using `[sqrt_idl hN E g _ hg]`. Use `congr 4`. Unfold `S6.nuBlock`. Expand and normalize the polynomial expressions, which then agree. Unfold `S6.liftIdl`.

Rewrite using `[sqrt_idl hN E g _ hg]`. Use `congr 4`.
-/
theorem t_BlockLattices : BlockLattices := by
  intro hL hI hN E _ _ _ hU g r b s hg
  obtain ⟨-, -, -, -, f5, -, -, -, -, -, -, -⟩ := hL E hU g (S6.nuBlock r b 1) 1 hg
  obtain ⟨-, -, -, -, k5, -, k7, -, -, -, -, -⟩ := hL E hU g (S6.nuBlock r b s) s hg
  refine ⟨fun l hl => f5 hl, fun l hl => k5 hl, fun l hl => k7 hl, idl_ne_zero hN E g _ _ hg,
    idl_ne_zero hN E g _ _ hg, ?_, ?_, ?_⟩
  · have := (hI E g r b ((s + 1 : ℕ) : ℤ)).1
    rw [this]; congr 2; push_cast; ring
  · unfold S6.dualIdl
    rw [sqrt_idl hN E g _ hg]
    congr 4; unfold S6.nuBlock; ring
  · unfold S6.liftIdl
    rw [sqrt_idl hN E g _ hg]
    congr 4

section Gl
variable {ι : Type} [Fintype ι] (G : Sz.Glob ι) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ)

/- English proof (translation)
Unfold `Sz.Glob.supI`. Apply `Real.sSup_nonneg` to reduce the goal to its premises. Introduce and unpack `x ⟨Y, -, rfl⟩`. Use `show 0 ≤ G.g ^ G.m * (G.place w).be G.ka de de' T T' Y`. Unfold `Sz.Cfg.be Sz.Cfg.core`.

Check the signs of the components of the expression.
-/
lemma supI_nonneg (hg : 0 ≤ G.g) (hka : 0 ≤ G.ka) (w : ι) : 0 ≤ G.supI de de' T T' l w := by
  unfold Sz.Glob.supI
  apply Real.sSup_nonneg
  rintro x ⟨Y, -, rfl⟩
  show 0 ≤ G.g ^ G.m * (G.place w).be G.ka de de' T T' Y
  unfold Sz.Cfg.be Sz.Cfg.core
  positivity

/- English proof (translation)
Unfold `Sz.Glob.cutSupLong`. Apply `Real.sSup_nonneg` to reduce the goal to its premises. Introduce and unpack `x ⟨Y, -, rfl⟩`. Use `show 0 ≤ G.g ^ G.m * (G.place w).be G.ka de de' T T' Y`. Unfold `Sz.Cfg.be Sz.Cfg.core`.

Check the signs of the components of the expression.
-/
lemma supremum_first_nonneg (hg : 0 ≤ G.g) (hka : 0 ≤ G.ka) (w : ι) : 0 ≤ G.cutSupLong de de' T T' l w := by
  unfold Sz.Glob.cutSupLong
  apply Real.sSup_nonneg
  rintro x ⟨Y, -, rfl⟩
  show 0 ≤ G.g ^ G.m * (G.place w).be G.ka de de' T T' Y
  unfold Sz.Cfg.be Sz.Cfg.core
  positivity

noncomputable def sp (p : Prop) [Decidable p] (w : ι) : ℝ :=
  if p then G.cutSupLong de de' T T' l w else G.supI de de' T T' l w

/- English proof (translation)
Unfold `sp`. Use `split_ifs`. Conclude with `supremum_first_nonneg G de de' T T' l hg hka w`. Conclude with `supI_nonneg G de de' T T' l hg hka w`.
-/
lemma sp_nonneg (hg : 0 ≤ G.g) (hka : 0 ≤ G.ka) (p : Prop) [Decidable p] (w : ι) :
    0 ≤ sp G de de' T T' l p w := by
  unfold sp; split_ifs
  · exact supremum_first_nonneg G de de' T T' l hg hka w
  · exact supI_nonneg G de de' T T' l hg hka w

/- English proof (translation)
Unfold `supA sp`. Simplify using `only [decide_eq_true_eq]`. Clear the denominators using the available nonvanishing facts.
-/
lemma supA_mul (hg : 0 < G.g) (hka : 0 < G.ka) (p : Prop) [Decidable p] (w : ι) :
    G.g ^ G.m * ((G.ka ^ (G.m - 1))⁻¹ * supA G de de' T T' l (decide p) w) = sp G de de' T T' l p w := by
  unfold supA sp
  simp only [decide_eq_true_eq]
  field_simp

/- English proof (translation)
Establish `h` using `sp_nonneg G de de' T T' l hg.le hka.le p w`. Rewrite `h` using `[← supA_mul G de de' T T' l hg hka p w]`. Establish `hc : 0 < G.g ^ G.m * (G.ka ^ (G.m - 1))⁻¹` using `by positivity`. Rewrite `h` using `[← mul_assoc]`. Conclude with `nonneg_of_mul_nonneg_right h hc`.
-/
lemma supA_nonneg (hg : 0 < G.g) (hka : 0 < G.ka) (p : Prop) [Decidable p] (w : ι) :
    0 ≤ supA G de de' T T' l (decide p) w := by
  have h := sp_nonneg G de de' T T' l hg.le hka.le p w
  rw [← supA_mul G de de' T T' l hg hka p w] at h
  have hc : 0 < G.g ^ G.m * (G.ka ^ (G.m - 1))⁻¹ := by positivity
  rw [← mul_assoc] at h
  exact nonneg_of_mul_nonneg_right h hc

/- English proof (translation)
Unfold `Sz.Glob.N`. Check the signs of the components of the expression.
-/
lemma N_nonneg : 0 ≤ G.N := by unfold Sz.Glob.N; positivity

/- English proof (translation)
Unfold `thrS Sz.lamThreshold`. Establish `h1` using `supA_nonneg G de de' T T' l hg hka (b = 1 ∧ s = 1) w`. Establish `h2` using `N_nonneg G`. Use `Real.pi_pos` as an intermediate fact. Check the signs of the components of the expression.
-/
lemma thrS_nonneg (hg : 0 < G.g) (hka : 0 < G.ka) (hC : 0 ≤ C) (hI : 0 < G.lenI) (b s : ℕ) (w : ι) :
    0 ≤ thrS G C de de' T T' l b s w := by
  unfold thrS Sz.lamThreshold
  have h1 := supA_nonneg G de de' T T' l hg hka (b = 1 ∧ s = 1) w
  have h2 := N_nonneg G
  have := Real.pi_pos
  positivity

/- English proof (translation)
Unfold `Sz.lamHat`. Establish `h2` using `N_nonneg G`. Check the signs of the components of the expression.
-/
lemma lamHat_nonneg (hg : 0 < G.g) (hka : 0 < G.ka) (hC : 0 ≤ C) (hI : 0 < G.lenI) (b s : ℕ) (x : ℝ)
    (hx : 0 ≤ x) : 0 ≤ Sz.lamHat b s C G.ka G.N G.lenI G.g x := by
  unfold Sz.lamHat
  have h2 := N_nonneg G
  positivity

/- English proof (translation)
Use `⟨b, hb, by omega, ?_⟩` and prove the remaining obligations. Break down `Nat.eq_or_lt_of_le hs with h1 | h1` into its components or cases. Substitute `h1` using the available equality. Break down `Nat.eq_or_lt_of_le hb with h2 | h2` into its components or cases. Substitute `h2 left` using the available equality.

Use `⟨rfl, Finset.prod_congr rfl fun w _ => ?_⟩` and prove the remaining obligations. Rewrite using `[(hX 0 1 C G.ka G.N G.lenI 0 G.g _).2]`. Simplify using `[sp]`. Use `right`. Use `left`.

Use `⟨h2, Finset.prod_congr rfl fun w _ => ?_⟩` and prove the remaining obligations. Rewrite using `[(hX 0 b C G.ka G.N G.lenI 0 G.g _).2]`. Establish `: b ≠ 1` using `by omega`. Simplify using `[sp, this]`. Use `right`.

Use `right`. Use `left`. Use `⟨s, h1, by omega, Finset.prod_congr rfl fun w _ => ?_⟩` and prove the remaining obligations. Establish `: s ≠ 1` using `by omega`. Simplify using `[sp, this]`.
-/
lemma memS (hX : XIsLamOne) (b s : ℕ) (hb : 1 ≤ b) (hs : 1 ≤ s) (hbs : b + s ≤ G.r + 2) :
    (∏ w, Sz.lamHat b s C G.ka G.N G.lenI G.g (sp G de de' T T' l (b = 1 ∧ s = 1) w)) ∈
      G.thrSet C de de' T T' l := by
  refine ⟨b, hb, by omega, ?_⟩
  rcases Nat.eq_or_lt_of_le hs with h1 | h1
  · subst h1
    rcases Nat.eq_or_lt_of_le hb with h2 | h2
    · subst h2
      left
      refine ⟨rfl, Finset.prod_congr rfl fun w _ => ?_⟩
      rw [(hX 0 1 C G.ka G.N G.lenI 0 G.g _).2]; simp [sp]
    · right; left
      refine ⟨h2, Finset.prod_congr rfl fun w _ => ?_⟩
      rw [(hX 0 b C G.ka G.N G.lenI 0 G.g _).2]
      have : b ≠ 1 := by omega
      simp [sp, this]
  · right; right; left
    refine ⟨s, h1, by omega, Finset.prod_congr rfl fun w _ => ?_⟩
    have : s ≠ 1 := by omega
    simp [sp, this]

/- English proof (translation)
Assemble the required witnesses or components as `⟨b, hb, hbs, Or.inr (Or.inr (Or.inr rfl))⟩`.
-/
lemma memP (b : ℕ) (hb : 1 ≤ b) (hbs : b ≤ G.r + 1) :
    (∏ w, Sz.lamPrimeHat b C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T')) ∈
      G.thrSet C de de' T T' l :=
  ⟨b, hb, hbs, Or.inr (Or.inr (Or.inr rfl))⟩

end Gl

/- English proof (translation)
Introduce `hL hI hN hDeg hFP hX E W _ _ _ D e G C de de' T T' l Θ hU hInst hg1 hg2 hC hlen hΘ hGr`. Take `⟨hr, hK, hPl, hv, hLa, hLap, hLad, hszD, hszL, hvol⟩` from `hInst`. Establish `hgN : 0 < G.g1 * G.g2` using `Nat.mul_pos hg1 hg2`. Establish `hGg : G.g = ((G.g1 * G.g2 : ℕ) : ℝ)` using `by unfold Sz.Glob.g; push_cast; ring`. Establish `hgpos : 0 < G.g` using `by rw [hGg]; exact_mod_cast hgN`.

Establish `hrd` using `rd_pos E`. Establish `hka : G.ka = 2 * Real.pi / S6.rd E`. Unfold `Sz.Glob.ka`. Rewrite using `[hv]`. Clear the denominators using the available nonvanishing facts.

Establish `hkapos : 0 < G.ka` using `by rw [hka]; have := Real.pi_pos; positivity`. Establish `hcard : Fintype.card (InfinitePlace E) = S6.deg E` using `(hDeg E).2.1`. Establish `hf : D.f = Fintype.card (InfinitePlace E)` using `by simpa using Fintype.card_congr e`. Establish `hGf : G.f = Fintype.card (InfinitePlace E)` using `rfl`. Establish `hM : ∀ x ∈ G.thrSet C de de' T T' l, x ≤ (Θ ^ G.f)⁻¹` using `fun x hx => hGr.2 hx`.

Establish `BL` using `fun b s => t_BlockLattices hL hI hN E hU (G.g1 * G.g2) G.r b s hgN`. Establish `key : ∀ b s : ℕ, 1 ≤ b → 1 ≤ s → ∀ w, thrS G C de de' T T' l b s w * (G.g * S6.rd E ^ (S6.nuBlock G.r b s + 1)) = Sz.lamHat b s C G.ka G.N G.lenI G.g (sp G de de' T T' l (b = 1 ∧ s = 1) w)`. Introduce `b s hb hs w`. Use `(hFP G.r b s C (S6.rd E) G.g G.N G.lenI (supA G de de' T T' l (decide (b = 1 ∧ s = 1)) w) 0 hb hs hrd hgpos).1` as an intermediate fact. Unfold `thrS`.

Rewrite using `[show G.m = 2 * G.r + 2 from rfl, this, ← hka]`. Use `congr 1`. Conclude with `supA_mul G de de' T T' l hgpos hkapos _ w`. Establish `keyP : ∀ b : ℕ, 1 ≤ b → ∀ w, thrP G C de de' T T' l b w * (G.g * S6.rd E ^ (S6.nuBlock G.r b ((G.r : ℤ) + 2 - b))) = Sz.lamPrimeHat b C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T')`. Introduce `b hb w`.

Use `(hFP G.r b 1 C (S6.rd E) G.g G.N G.lenI (supA G de de' T T' l false w) (T * T') hb le_rfl hrd hgpos).2` as an intermediate fact. Unfold `thrP`. Rewrite using `[show G.m = 2 * G.r + 2 from rfl, this, ← hka]`. Use `congr 1`. Conclude with `supA_mul G de de' T T' l hgpos hkapos False w`.

Establish `prodkey : ∀ b s : ℕ, 1 ≤ b → 1 ≤ s → ∏ w, thrS G C de de' T T' l b s w = (∏ w, Sz.lamHat b s C G.ka G.N G.lenI G.g (sp G de de' T T' l (b = 1 ∧ s = 1) w)) * √(FractionalIdeal.absNorm (S6.dualIdl E (G.g1 * G.g2) (S6.nuBlock G.r b s)) : ℝ)`. Introduce `b s hb hs`. Establish `hc : 0 < G.g * S6.rd E ^ (S6.nuBlock G.r b s + 1)` using `by positivity`. Unfold `S6.dualIdl`. Rewrite using `[sqrt_idl hN E _ _ hgN, ← hGg, ← hcard, ← Finset.card_univ, ← Finset.prod_const, ← div_eq_mul_inv, ← Finset.prod_div_distrib]`.

Conclude with `Finset.prod_congr rfl fun w _ => eq_div_of_mul_eq hc.ne' (key b s hb hs w)`. Establish `Ppos : ∀ b s : ℕ, 0 ≤ ∏ w, Sz.lamHat b s C G.ka G.N G.lenI G.g (sp G de de' T T' l (b = 1 ∧ s = 1) w)` using `fun b s => Finset.prod_nonneg fun w _ => lamHat_nonneg G C hgpos hkapos hC hlen b s _ (sp_nonneg G de de' T T' l hgpos.le hkapos.le _ w)`. Establish `Ple : ∀ b s : ℕ, 1 ≤ b → 1 ≤ s → b + s ≤ G.r + 2 → ∏ w, Sz.lamHat b s C G.ka G.N G.lenI G.g (sp G de de' T T' l (b = 1 ∧ s = 1) w) ≤ (Θ ^ G.f)⁻¹` using `fun b s hb hs hbs => hM _ (memS G C de de' T T' l hX b s hb hs hbs)`. Establish `Npos : ∀ ν : ℤ, 0 < √(FractionalIdeal.absNorm (S6.dualIdl E (G.g1 * G.g2) ν) : ℝ)`. Introduce `ν`.

Unfold `S6.dualIdl`. Rewrite using `[sqrt_idl hN E _ _ hgN]`. Establish `: (0 : ℝ) < ((G.g1 * G.g2 : ℕ) : ℝ)` using `by exact_mod_cast hgN`. Check the signs of the components of the expression. Use `⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `b s`. Rewrite using `[hvol]`. Apply `div_nonneg (sq_nonneg _)` to reduce the goal to its premises. Conclude with `FractionalIdeal.absNorm_nonneg _` after adjusting the coercions. Introduce `b s hb hs hbs`.

Rewrite `hbs` using `[hr]`. Rewrite using `[hvol, prodkey b s hb hs, mul_pow, Real.sq_sqrt (Real.sqrt_pos.1 (Npos _)).le, mul_div_assoc, div_self (Real.sqrt_pos.1 (Npos _)).ne', mul_one, hf, ← hGf]`. Conclude with `pow_le_pow_left₀ (Ppos b s) (Ple b s hb hs hbs) 2`. Introduce `i hi1 hi2`. Rewrite `hi2` using `[hr]`.

Use `⟨(BL i 1).2.2.2.1, ?_, fun v => ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[hLad]`. Conclude with `(BL i 1).1 x hx`. Rewrite using `[hszD]`.

Conclude with `thrS_nonneg G C de de' T T' l hgpos hkapos hC hlen _ _ _`. Establish `h1 : ∏ v, D.szD i v = ∏ w, thrS G C de de' T T' l i 1 w`. Rewrite using `[← Equiv.prod_comp e]`. Conclude with `Finset.prod_congr rfl fun v _ => hszD i v`. Rewrite using `[h1]`.

Establish `h2` using `prodkey i 1 hi1 le_rfl`. Rewrite `h2` using `[Nat.cast_one]`. Use `beta_reduce`. Rewrite using `[h2, one_div, inv_pow, hf, ← hGf]`. Conclude with `mul_le_mul_of_nonneg_right (Ple i 1 hi1 le_rfl (by omega)) (Real.sqrt_nonneg _)`.

Introduce `b s hb hs hbs hne`. Rewrite `hbs`, `hne` using `[hr]`. Use `⟨(BL b s).2.2.2.2.1, ?_, fun v => ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[hLap]`.

Conclude with `(BL b s).2.2.1 x hx`. Rewrite using `[hszL]`. Use `split_ifs`. Conclude with `thrS_nonneg G C de de' T T' l hgpos hkapos hC hlen _ _ _`. Unfold `thrP`.

Check the signs of the components of the expression. Establish `h2Θ : (Θ ^ G.f)⁻¹ ≤ (2 / Θ) ^ D.f`. Rewrite using `[hf, ← hGf, div_pow, div_eq_mul_inv]`. Establish `: (1 : ℝ) ≤ 2 ^ G.f` using `one_le_pow₀ (by norm_num)`. Establish `h0 : 0 ≤ (Θ ^ G.f)⁻¹` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Distinguish the cases in `hc : b + s ≤ G.r + 1`. Establish `h1 : ∏ v, D.szL b s v = ∏ w, thrS G C de de' T T' l b (s + 1) w`. Rewrite using `[← Equiv.prod_comp e]`. Conclude with `Finset.prod_congr rfl fun v _ => by rw [hszL, if_pos hc]`.

Use `beta_reduce`. Rewrite using `[h1, prodkey b (s + 1) hb (by omega), (BL b s).2.2.2.2.2.1]`. Conclude with `mul_le_mul_of_nonneg_right ((Ple b (s + 1) hb (by omega) (by omega)).trans h2Θ) (Real.sqrt_nonneg _)`. Establish `hs' : (s : ℤ) = (G.r : ℤ) + 2 - b` using `by omega`. Establish `h1 : ∏ v, D.szL b s v = 2 ^ D.f * ∏ w, thrP G C de de' T T' l b w`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Use `_ = _ := by rw [Equiv.prod_comp e (fun w => thrP G C de de' T T' l b w)]`. Establish `hcpos : 0 < G.g * S6.rd E ^ (S6.nuBlock G.r b s)` using `by positivity`. Establish `h2 : ∏ w, thrP G C de de' T T' l b w = (∏ w, Sz.lamPrimeHat b C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T')) * √(FractionalIdeal.absNorm (S6.liftIdl E (G.g1 * G.g2) (S6.nuBlock G.r b s)) : ℝ)`.

Unfold `S6.liftIdl`. Rewrite using `[sqrt_idl hN E _ _ hgN, ← hGg, ← hcard, ← Finset.card_univ, ← Finset.prod_const, ← div_eq_mul_inv, ← Finset.prod_div_distrib]`. Use `Finset.prod_congr rfl fun w _ => eq_div_of_mul_eq hcpos.ne' ?_` and prove the remaining obligations. Rewrite using `[hs']`. Conclude with `keyP b hb w`.

Use `beta_reduce`. Rewrite using `[h1, h2, ← mul_assoc]`. Apply `mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)` to reduce the goal to its premises. Establish `h3` using `hM _ (memP G C de de' T T' l b hb (by omega))`. Rewrite using `[div_pow, div_eq_mul_inv, hf, ← hGf]`.

Conclude with `mul_le_mul_of_nonneg_left h3 (by positivity)`. Unfold `TB.Data.Ntop Sz.Glob.N`. Rewrite using `[hK, hr]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem t_InstSizes : InstSizes := by
  intro hL hI hN hDeg hFP hX E W _ _ _ D e G C de de' T T' l Θ hU hInst hg1 hg2 hC hlen hΘ hGr
  obtain ⟨hr, hK, hPl, hv, hLa, hLap, hLad, hszD, hszL, hvol⟩ := hInst
  have hgN : 0 < G.g1 * G.g2 := Nat.mul_pos hg1 hg2
  have hGg : G.g = ((G.g1 * G.g2 : ℕ) : ℝ) := by unfold Sz.Glob.g; push_cast; ring
  have hgpos : 0 < G.g := by rw [hGg]; exact_mod_cast hgN
  have hrd := rd_pos E
  have hka : G.ka = 2 * Real.pi / S6.rd E := by
    unfold Sz.Glob.ka; rw [hv]; field_simp
  have hkapos : 0 < G.ka := by rw [hka]; have := Real.pi_pos; positivity
  have hcard : Fintype.card (InfinitePlace E) = S6.deg E := (hDeg E).2.1
  have hf : D.f = Fintype.card (InfinitePlace E) := by simpa using Fintype.card_congr e
  have hGf : G.f = Fintype.card (InfinitePlace E) := rfl
  have hM : ∀ x ∈ G.thrSet C de de' T T' l, x ≤ (Θ ^ G.f)⁻¹ := fun x hx => hGr.2 hx
  have BL := fun b s => t_BlockLattices hL hI hN E hU (G.g1 * G.g2) G.r b s hgN

  have key : ∀ b s : ℕ, 1 ≤ b → 1 ≤ s → ∀ w, thrS G C de de' T T' l b s w *
      (G.g * S6.rd E ^ (S6.nuBlock G.r b s + 1)) =
      Sz.lamHat b s C G.ka G.N G.lenI G.g (sp G de de' T T' l (b = 1 ∧ s = 1) w) := by
    intro b s hb hs w
    have := (hFP G.r b s C (S6.rd E) G.g G.N G.lenI
      (supA G de de' T T' l (decide (b = 1 ∧ s = 1)) w) 0 hb hs hrd hgpos).1
    unfold thrS
    rw [show G.m = 2 * G.r + 2 from rfl, this, ← hka]
    congr 1
    exact supA_mul G de de' T T' l hgpos hkapos _ w
  have keyP : ∀ b : ℕ, 1 ≤ b → ∀ w, thrP G C de de' T T' l b w *
      (G.g * S6.rd E ^ (S6.nuBlock G.r b ((G.r : ℤ) + 2 - b))) =
      Sz.lamPrimeHat b C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T') := by
    intro b hb w
    have := (hFP G.r b 1 C (S6.rd E) G.g G.N G.lenI
      (supA G de de' T T' l false w) (T * T') hb le_rfl hrd hgpos).2
    unfold thrP
    rw [show G.m = 2 * G.r + 2 from rfl, this, ← hka]
    congr 1
    exact supA_mul G de de' T T' l hgpos hkapos False w

  have prodkey : ∀ b s : ℕ, 1 ≤ b → 1 ≤ s → ∏ w, thrS G C de de' T T' l b s w =
      (∏ w, Sz.lamHat b s C G.ka G.N G.lenI G.g (sp G de de' T T' l (b = 1 ∧ s = 1) w)) *
        √(FractionalIdeal.absNorm (S6.dualIdl E (G.g1 * G.g2) (S6.nuBlock G.r b s)) : ℝ) := by
    intro b s hb hs
    have hc : 0 < G.g * S6.rd E ^ (S6.nuBlock G.r b s + 1) := by positivity
    unfold S6.dualIdl
    rw [sqrt_idl hN E _ _ hgN, ← hGg, ← hcard, ← Finset.card_univ, ← Finset.prod_const,
      ← div_eq_mul_inv, ← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun w _ => eq_div_of_mul_eq hc.ne' (key b s hb hs w)
  have Ppos : ∀ b s : ℕ, 0 ≤ ∏ w, Sz.lamHat b s C G.ka G.N G.lenI G.g
      (sp G de de' T T' l (b = 1 ∧ s = 1) w) := fun b s =>
    Finset.prod_nonneg fun w _ => lamHat_nonneg G C hgpos hkapos hC hlen b s _
      (sp_nonneg G de de' T T' l hgpos.le hkapos.le _ w)
  have Ple : ∀ b s : ℕ, 1 ≤ b → 1 ≤ s → b + s ≤ G.r + 2 →
      ∏ w, Sz.lamHat b s C G.ka G.N G.lenI G.g (sp G de de' T T' l (b = 1 ∧ s = 1) w) ≤
        (Θ ^ G.f)⁻¹ := fun b s hb hs hbs => hM _ (memS G C de de' T T' l hX b s hb hs hbs)
  have Npos : ∀ ν : ℤ, 0 < √(FractionalIdeal.absNorm (S6.dualIdl E (G.g1 * G.g2) ν) : ℝ) := by
    intro ν
    unfold S6.dualIdl
    rw [sqrt_idl hN E _ _ hgN]
    have : (0 : ℝ) < ((G.g1 * G.g2 : ℕ) : ℝ) := by exact_mod_cast hgN
    positivity
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro b s
    rw [hvol]
    apply div_nonneg (sq_nonneg _)
    exact_mod_cast FractionalIdeal.absNorm_nonneg _
  · intro b s hb hs hbs
    rw [hr] at hbs
    rw [hvol, prodkey b s hb hs, mul_pow, Real.sq_sqrt (Real.sqrt_pos.1 (Npos _)).le,
      mul_div_assoc, div_self (Real.sqrt_pos.1 (Npos _)).ne', mul_one, hf, ← hGf]
    exact pow_le_pow_left₀ (Ppos b s) (Ple b s hb hs hbs) 2
  · intro i hi1 hi2
    rw [hr] at hi2
    refine ⟨(BL i 1).2.2.2.1, ?_, fun v => ?_, ?_⟩
    · intro x hx; rw [hLad] at hx; exact (BL i 1).1 x hx
    · rw [hszD]; exact thrS_nonneg G C de de' T T' l hgpos hkapos hC hlen _ _ _
    · have h1 : ∏ v, D.szD i v = ∏ w, thrS G C de de' T T' l i 1 w := by
        rw [← Equiv.prod_comp e]; exact Finset.prod_congr rfl fun v _ => hszD i v
      rw [h1]
      have h2 := prodkey i 1 hi1 le_rfl
      rw [Nat.cast_one] at h2
      beta_reduce
      rw [h2, one_div, inv_pow, hf, ← hGf]
      exact mul_le_mul_of_nonneg_right (Ple i 1 hi1 le_rfl (by omega)) (Real.sqrt_nonneg _)
  · intro b s hb hs hbs hne
    rw [hr] at hbs hne
    refine ⟨(BL b s).2.2.2.2.1, ?_, fun v => ?_, ?_⟩
    · intro x hx; rw [hLap] at hx; exact (BL b s).2.2.1 x hx
    · rw [hszL]; split_ifs
      · exact thrS_nonneg G C de de' T T' l hgpos hkapos hC hlen _ _ _
      · unfold thrP; positivity
    · have h2Θ : (Θ ^ G.f)⁻¹ ≤ (2 / Θ) ^ D.f := by
        rw [hf, ← hGf, div_pow, div_eq_mul_inv]
        have : (1 : ℝ) ≤ 2 ^ G.f := one_le_pow₀ (by norm_num)
        have h0 : 0 ≤ (Θ ^ G.f)⁻¹ := by positivity
        nlinarith
      by_cases hc : b + s ≤ G.r + 1
      · have h1 : ∏ v, D.szL b s v = ∏ w, thrS G C de de' T T' l b (s + 1) w := by
          rw [← Equiv.prod_comp e]
          exact Finset.prod_congr rfl fun v _ => by rw [hszL, if_pos hc]
        beta_reduce
        rw [h1, prodkey b (s + 1) hb (by omega), (BL b s).2.2.2.2.2.1]
        exact mul_le_mul_of_nonneg_right ((Ple b (s + 1) hb (by omega) (by omega)).trans h2Θ)
          (Real.sqrt_nonneg _)
      · have hs' : (s : ℤ) = (G.r : ℤ) + 2 - b := by omega
        have h1 : ∏ v, D.szL b s v = 2 ^ D.f * ∏ w, thrP G C de de' T T' l b w := by
          calc ∏ v, D.szL b s v = ∏ v, (2 * thrP G C de de' T T' l b (e v)) :=
                Finset.prod_congr rfl fun v _ => by rw [hszL, if_neg hc]
            _ = 2 ^ D.f * ∏ v, thrP G C de de' T T' l b (e v) := by
                rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            _ = _ := by rw [Equiv.prod_comp e (fun w => thrP G C de de' T T' l b w)]
        have hcpos : 0 < G.g * S6.rd E ^ (S6.nuBlock G.r b s) := by positivity
        have h2 : ∏ w, thrP G C de de' T T' l b w =
            (∏ w, Sz.lamPrimeHat b C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T')) *
              √(FractionalIdeal.absNorm (S6.liftIdl E (G.g1 * G.g2) (S6.nuBlock G.r b s)) : ℝ) := by
          unfold S6.liftIdl
          rw [sqrt_idl hN E _ _ hgN, ← hGg, ← hcard, ← Finset.card_univ, ← Finset.prod_const,
            ← div_eq_mul_inv, ← Finset.prod_div_distrib]
          refine Finset.prod_congr rfl fun w _ => eq_div_of_mul_eq hcpos.ne' ?_
          rw [hs']; exact keyP b hb w
        beta_reduce
        rw [h1, h2, ← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        have h3 := hM _ (memP G C de de' T T' l b hb (by omega))
        rw [div_pow, div_eq_mul_inv, hf, ← hGf]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
  · unfold TB.Data.Ntop Sz.Glob.N
    rw [hK, hr]; push_cast; ring

end sizes

section sums
open scoped nonZeroDivisors
/- English proof (translation)
Introduce `E W _ _ D e hP ρ l`. Unfold `TB.Data.maj prof`. Rewrite using `[← Equiv.prod_comp e]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.symm_apply_apply]`.

Rewrite using `[hP v l]`.
-/
theorem t_MajIsProf : MajIsProf := by
  intro E W _ _ D e hP ρ l
  unfold TB.Data.maj prof
  rw [← Equiv.prod_comp e]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [Equiv.symm_apply_apply]
  rw [hP v l]

/- English proof (translation)
Introduce `hB`. Take `⟨C0, hC0⟩` from `hB`. Use `⟨|C0| + 1, by have := abs_nonneg C0; linarith, ?_⟩` and prove the remaining obligations. Introduce `E _ _ _ aa L x K Θ a haa hL hx hK ha hΘ hprod`. Establish `hf1 : 0 < Fintype.card (InfinitePlace E)` using `Fintype.card_pos`.

Establish `hΘ0 : 0 < Θ` using `by linarith`. Establish `ha0 : 0 < a` using `by linarith`. Establish `hK3 : (3 : ℝ) ≤ (K : ℝ)` using `by exact_mod_cast hK`. Establish `hp : 0 < (K : ℝ) - 5 / 2` using `by linarith`. Use `⟨fun l => Finset.prod_nonneg fun w _ => le_min zero_le_one (pow_nonneg (div_nonneg (hx w) (apply_nonneg w l)) K), ?_⟩` and prove the remaining obligations.

Introduce `S hS`. Establish `hRHS : 0 ≤ ((|C0| + 1) * a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E)` using `by positivity`. Distinguish the cases in `hx0 : ∃ w, x w = 0`. Take `⟨w0, hw0⟩` from `hx0`. Establish `h0 : ∀ l ∈ S, prof x K l = 0`.

Introduce `l _`. Unfold `prof`. Apply `Finset.prod_eq_zero (Finset.mem_univ w0)` to reduce the goal to its premises. Rewrite using `[hw0, zero_div, zero_pow (by omega)]; simp`. Rewrite using `[Finset.sum_eq_zero h0]`.

Conclude with `hRHS`. Use `push Not at hx0`. Establish `hxpos : ∀ w, 0 < x w` using `fun w => lt_of_le_of_ne (hx w) (Ne.symm (hx0 w))`. Establish `hP : 0 < ∏ w, x w` using `Finset.prod_pos fun w _ => hxpos w`. Establish `hNq : (0 : ℚ) < FractionalIdeal.absNorm aa` using `lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg aa) (Ne.symm (by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]))`.

Establish `hN : 0 < √(FractionalIdeal.absNorm aa : ℝ)` using `Real.sqrt_pos.2 (by exact_mod_cast hNq)`. Establish `hq : 0 < √(FractionalIdeal.absNorm aa : ℝ) / ∏ w, x w` using `div_pos hN hP`. Take `⟨Θ₀, hΘ₀def⟩ : ∃ Θ₀ : ℝ, Θ₀ = (√(FractionalIdeal.absNorm aa : ℝ) / ∏ w, x w) ^ (((Fintype.card (InfinitePlace E) : ℕ) : ℝ)⁻¹)` from `⟨_, rfl⟩`. Establish `hΘ₀pos : 0 < Θ₀` using `by rw [hΘ₀def]; exact Real.rpow_pos_of_pos hq _`. Establish `hΘ₀f : Θ₀ ^ Fintype.card (InfinitePlace E) = √(FractionalIdeal.absNorm aa : ℝ) / ∏ w, x w`.

Rewrite using `[hΘ₀def]`. Conclude with `Real.rpow_inv_natCast_pow hq.le (ne_of_gt hf1)`. Establish `hpw : (Θ / a) ^ Fintype.card (InfinitePlace E) ≤ Θ₀ ^ Fintype.card (InfinitePlace E)`. Rewrite using `[hΘ₀f, le_div_iff₀ hP]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_assoc, ← mul_pow]`. Establish `: Θ / a * (a / Θ) = 1` using `by field_simp`. Rewrite using `[this, one_pow, one_mul]`. Establish `hle : Θ / a ≤ Θ₀` using `le_of_pow_le_pow_left₀ (ne_of_gt hf1) hΘ₀pos.le hpw`. Establish `h2 : 2 < Θ₀` using `lt_of_lt_of_le (by rw [lt_div_iff₀ ha0]; linarith) hle`.

Establish `key` using `hC0 E aa haa x Θ₀ (K : ℝ) hxpos h2 hK3 hΘ₀f S (fun l hl => ⟨hL l (hS l hl).1, (hS l hl).2⟩)`. Establish `hsum : ∑ l ∈ S, prof x K l = ∑ l ∈ S, ∏ w, min 1 ((x w / w l) ^ (K : ℝ))`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Unfold `prof`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations.

Rewrite using `[Real.rpow_natCast]`. Rewrite using `[hsum]`. Use `key.trans ?_` and prove the remaining obligations. Establish `hΘa : 0 < Θ / a` using `div_pos hΘ0 ha0`. Establish `h3 : Θ₀ ^ (-((K : ℝ) - 5 / 2)) ≤ a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.rpow_neg hΘ₀pos.le, Real.rpow_neg hΘa.le]`. Conclude with `inv_anti₀ (Real.rpow_pos_of_pos hΘa _) (Real.rpow_le_rpow hΘa.le hle hp.le))`. Use `_ = a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)) := by`. Rewrite using `[Real.div_rpow hΘ0.le ha0.le, Real.rpow_neg ha0.le, div_inv_eq_mul, mul_comm]`.

Establish `h4 : |C0 * Θ₀ ^ (-((K : ℝ) - 5 / 2))| ≤ (|C0| + 1) * a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))`. Rewrite using `[abs_mul, abs_of_pos (Real.rpow_pos_of_pos hΘ₀pos _), mul_assoc]`. Conclude with `mul_le_mul (by linarith) h3 (Real.rpow_pos_of_pos hΘ₀pos _).le (by have := abs_nonneg C0; linarith)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem t_BoxSumLattice : BoxSumLattice := by
  intro hB
  obtain ⟨C0, hC0⟩ := hB
  refine ⟨|C0| + 1, by have := abs_nonneg C0; linarith, ?_⟩
  intro E _ _ _ aa L x K Θ a haa hL hx hK ha hΘ hprod
  have hf1 : 0 < Fintype.card (InfinitePlace E) := Fintype.card_pos
  have hΘ0 : 0 < Θ := by linarith
  have ha0 : 0 < a := by linarith
  have hK3 : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hp : 0 < (K : ℝ) - 5 / 2 := by linarith
  refine ⟨fun l => Finset.prod_nonneg fun w _ =>
    le_min zero_le_one (pow_nonneg (div_nonneg (hx w) (apply_nonneg w l)) K), ?_⟩
  intro S hS
  have hRHS : 0 ≤ ((|C0| + 1) * a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))) ^
      Fintype.card (InfinitePlace E) := by positivity
  by_cases hx0 : ∃ w, x w = 0
  · obtain ⟨w0, hw0⟩ := hx0
    have h0 : ∀ l ∈ S, prof x K l = 0 := by
      intro l _
      unfold prof
      apply Finset.prod_eq_zero (Finset.mem_univ w0)
      rw [hw0, zero_div, zero_pow (by omega)]; simp
    rw [Finset.sum_eq_zero h0]; exact hRHS
  · push Not at hx0
    have hxpos : ∀ w, 0 < x w := fun w => lt_of_le_of_ne (hx w) (Ne.symm (hx0 w))
    have hP : 0 < ∏ w, x w := Finset.prod_pos fun w _ => hxpos w
    have hNq : (0 : ℚ) < FractionalIdeal.absNorm aa :=
      lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg aa)
        (Ne.symm (by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]))
    have hN : 0 < √(FractionalIdeal.absNorm aa : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hNq)
    have hq : 0 < √(FractionalIdeal.absNorm aa : ℝ) / ∏ w, x w := div_pos hN hP
    obtain ⟨Θ₀, hΘ₀def⟩ : ∃ Θ₀ : ℝ, Θ₀ = (√(FractionalIdeal.absNorm aa : ℝ) / ∏ w, x w) ^
        (((Fintype.card (InfinitePlace E) : ℕ) : ℝ)⁻¹) := ⟨_, rfl⟩
    have hΘ₀pos : 0 < Θ₀ := by rw [hΘ₀def]; exact Real.rpow_pos_of_pos hq _
    have hΘ₀f : Θ₀ ^ Fintype.card (InfinitePlace E) =
        √(FractionalIdeal.absNorm aa : ℝ) / ∏ w, x w := by
      rw [hΘ₀def]; exact Real.rpow_inv_natCast_pow hq.le (ne_of_gt hf1)
    have hpw : (Θ / a) ^ Fintype.card (InfinitePlace E) ≤ Θ₀ ^ Fintype.card (InfinitePlace E) := by
      rw [hΘ₀f, le_div_iff₀ hP]
      calc (Θ / a) ^ Fintype.card (InfinitePlace E) * ∏ w, x w
          ≤ (Θ / a) ^ Fintype.card (InfinitePlace E) *
              ((a / Θ) ^ Fintype.card (InfinitePlace E) * √(FractionalIdeal.absNorm aa : ℝ)) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = √(FractionalIdeal.absNorm aa : ℝ) := by
            rw [← mul_assoc, ← mul_pow]
            have : Θ / a * (a / Θ) = 1 := by field_simp
            rw [this, one_pow, one_mul]
    have hle : Θ / a ≤ Θ₀ := le_of_pow_le_pow_left₀ (ne_of_gt hf1) hΘ₀pos.le hpw
    have h2 : 2 < Θ₀ := lt_of_lt_of_le (by rw [lt_div_iff₀ ha0]; linarith) hle
    have key := hC0 E aa haa x Θ₀ (K : ℝ) hxpos h2 hK3 hΘ₀f S
      (fun l hl => ⟨hL l (hS l hl).1, (hS l hl).2⟩)
    have hsum : ∑ l ∈ S, prof x K l = ∑ l ∈ S, ∏ w, min 1 ((x w / w l) ^ (K : ℝ)) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      unfold prof
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [Real.rpow_natCast]
    rw [hsum]
    refine key.trans ?_
    have hΘa : 0 < Θ / a := div_pos hΘ0 ha0
    have h3 : Θ₀ ^ (-((K : ℝ) - 5 / 2)) ≤ a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)) := by
      calc Θ₀ ^ (-((K : ℝ) - 5 / 2)) ≤ (Θ / a) ^ (-((K : ℝ) - 5 / 2)) :=
            (by
              rw [Real.rpow_neg hΘ₀pos.le, Real.rpow_neg hΘa.le]
              exact inv_anti₀ (Real.rpow_pos_of_pos hΘa _) (Real.rpow_le_rpow hΘa.le hle hp.le))
        _ = a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)) := by
            rw [Real.div_rpow hΘ0.le ha0.le, Real.rpow_neg ha0.le, div_inv_eq_mul, mul_comm]
    have h4 : |C0 * Θ₀ ^ (-((K : ℝ) - 5 / 2))| ≤
        (|C0| + 1) * a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)) := by
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hΘ₀pos _), mul_assoc]
      exact mul_le_mul (by linarith) h3 (Real.rpow_pos_of_pos hΘ₀pos _).le
        (by have := abs_nonneg C0; linarith)
    calc (C0 * Θ₀ ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E)
        ≤ |(C0 * Θ₀ ^ (-((K : ℝ) - 5 / 2))) ^ Fintype.card (InfinitePlace E)| := le_abs_self _
      _ = |C0 * Θ₀ ^ (-((K : ℝ) - 5 / 2))| ^ Fintype.card (InfinitePlace E) := abs_pow _ _
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) h4 _

/- English proof (translation)
Introduce `hB`. Take `⟨C, hC1, hC⟩` from `t_BoxSumLattice hB`. Use `⟨C, hC1, ?_⟩` and prove the remaining obligations. Introduce `E W _ _ _ D e aaD aaL Θ a hP hK ha hΘ hI`. Establish `hcard : Fintype.card (InfinitePlace E) = D.f`.

Rewrite using `[← Fintype.card_congr e, Fintype.card_fin]`. Establish `hpc : ∀ ρ : Fin D.f → ℝ, ∏ w, ρ (e.symm w) = ∏ v, ρ v` using `fun ρ => Equiv.prod_comp e.symm ρ`. Establish `hΘ0 : 0 < Θ` using `by linarith`. Establish `ha0 : 0 < a` using `by linarith`. Establish `hK3 : (3 : ℝ) ≤ (D.K : ℝ)` using `by exact_mod_cast hK`.

Prove the components needed by the constructor for the conclusion. Introduce `i hi1 hi2 L hL`. Take `⟨h0, hsub, hnn, hsz⟩` from `hI.1 i hi1 hi2`. Establish `h1` using `hC E (aaD i) (D.Lad i) (fun w => D.szD i (e.symm w)) D.K Θ 1 h0 hsub (fun w => hnn _) hK le_rfl (by linarith) (by rw [hpc, hcard]; exact hsz)`. Establish `h2` using `h1.2 L hL`.

Rewrite `h2` using `[hcard]`. Repeatedly rewrite using `[t_MajIsProf E W D e hP]`. Use `h2.trans ?_` and prove the remaining obligations. Apply `pow_le_pow_left₀ (by positivity)` to reduce the goal to its premises. Rewrite using `[Real.one_rpow, mul_one]`.

Apply `mul_le_mul_of_nonneg_right _ (by positivity)` to reduce the goal to its premises. Establish `: 1 ≤ a ^ ((D.K : ℝ) - 5 / 2)` using `Real.one_le_rpow ha (by linarith)`. Use the polynomial consequences of the given equalities and inequalities. Introduce `i s hs1 hsi hi hnot L hL`. Take `⟨h0, hsub, hnn, hsz⟩` from `hI.2 (i - s + 1) s (by omega) hs1 (by omega) (by rintro ⟨hb, hs⟩; exact hnot ⟨by omega, hs⟩)`.

Establish `h1` using `hC E (aaL (i - s + 1) s) (D.Lap (i - s + 1) s) (fun w => D.szL (i - s + 1) s (e.symm w)) D.K Θ a h0 hsub (fun w => hnn _) hK ha hΘ (by rw [hpc, hcard]; exact hsz)`. Establish `h2` using `h1.2 L hL`. Rewrite `h2` using `[hcard]`. Repeatedly rewrite using `[t_MajIsProf E W D e hP]`. Conclude with `h2`.
-/
theorem t_LatticeSumsJoint : LatticeSumsJoint := by
  intro hB
  obtain ⟨C, hC1, hC⟩ := t_BoxSumLattice hB
  refine ⟨C, hC1, ?_⟩
  intro E W _ _ _ D e aaD aaL Θ a hP hK ha hΘ hI
  have hcard : Fintype.card (InfinitePlace E) = D.f := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hpc : ∀ ρ : Fin D.f → ℝ, ∏ w, ρ (e.symm w) = ∏ v, ρ v := fun ρ => Equiv.prod_comp e.symm ρ
  have hΘ0 : 0 < Θ := by linarith
  have ha0 : 0 < a := by linarith
  have hK3 : (3 : ℝ) ≤ (D.K : ℝ) := by exact_mod_cast hK
  constructor
  · intro i hi1 hi2 L hL
    obtain ⟨h0, hsub, hnn, hsz⟩ := hI.1 i hi1 hi2
    have h1 := hC E (aaD i) (D.Lad i) (fun w => D.szD i (e.symm w)) D.K Θ 1 h0 hsub
      (fun w => hnn _) hK le_rfl (by linarith) (by rw [hpc, hcard]; exact hsz)
    have h2 := h1.2 L hL
    rw [hcard] at h2
    simp_rw [t_MajIsProf E W D e hP]
    refine h2.trans ?_
    apply pow_le_pow_left₀ (by positivity)
    rw [Real.one_rpow, mul_one]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have : 1 ≤ a ^ ((D.K : ℝ) - 5 / 2) := Real.one_le_rpow ha (by linarith)
    nlinarith
  · intro i s hs1 hsi hi hnot L hL
    obtain ⟨h0, hsub, hnn, hsz⟩ := hI.2 (i - s + 1) s (by omega) hs1 (by omega)
      (by rintro ⟨hb, hs⟩; exact hnot ⟨by omega, hs⟩)
    have h1 := hC E (aaL (i - s + 1) s) (D.Lap (i - s + 1) s)
      (fun w => D.szL (i - s + 1) s (e.symm w)) D.K Θ a h0 hsub
      (fun w => hnn _) hK ha hΘ (by rw [hpc, hcard]; exact hsz)
    have h2 := h1.2 L hL
    rw [hcard] at h2
    simp_rw [t_MajIsProf E W D e hP]
    exact h2

end sums

section positivity
/- English proof (translation)
Introduce `CDel Cb hCDel hCb`. Use `⟨max 3 ⌈2 / Cb⌉₊, ?_⟩` and prove the remaining obligations. Introduce `ι _ G bb hk hyp`. Establish `hk3 : 3 ≤ G.k` using `le_trans (le_max_left _ _) hk`. Establish `hkC : 2 / Cb ≤ (G.k : ℝ)` using `le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hk)`.

Establish `hk3r : (3 : ℝ) ≤ G.k` using `by exact_mod_cast hk3`. Establish `hk0 : (0 : ℝ) < G.k` using `by linarith`. Establish `hbb` using `hyp.hbb`. Establish `hbb0 : 0 < bb` using `by linarith`. Establish `hpos : 0 < ((G.k : ℝ) * bb) ^ 8` using `by positivity`.

Establish `hg1 : 0 < G.g1`. Establish `: (0 : ℝ) < G.g1` using `lt_of_lt_of_le hpos hyp.hg1`. Conclude with `this` after adjusting the coercions. Establish `hg2 : 0 < G.g2`. Establish `: (0 : ℝ) < G.g2` using `lt_of_lt_of_le hpos hyp.hg2`.

Conclude with `this` after adjusting the coercions. Use `⟨hg1, hg2, ?_⟩` and prove the remaining obligations. Establish `hm2 : 2 ≤ G.m` using `by unfold Sz.Glob.m; omega`. Establish `hf2 : 2 ≤ G.f` using `le_trans hm2 hyp.hmf`. Establish `hne : Nonempty ι`.

Apply `Fintype.card_pos_iff.1` to reduce the goal to its premises. Establish `: G.f = Fintype.card ι` using `rfl`. Use linear arithmetic over natural numbers and integers. Take `⟨w⟩` from `hne`. Establish `h1 : (G.k : ℝ) ^ Cb ≤ G.b w 1` using `hyp.hnode w 1 le_rfl (by omega)`.

Establish `h2 : G.b w 1 ≤ bb ^ 2` using `(hyp.hsmall w).hbj 1 le_rfl (by show 1 ≤ 2 * G.r + 2 omega)`. Establish `h3 : (G.k : ℝ) ^ Cb ≤ bb ^ 2` using `le_trans h1 h2`. Establish `h4 : Cb * Real.log G.k ≤ 2 * Real.log bb`. Use `Real.log_le_log (Real.rpow_pos_of_pos hk0 Cb) h3` as an intermediate fact. Rewrite `this` using `[Real.log_rpow hk0, Real.log_pow]`.

Conclude with `this` after adjusting the coercions. Establish `hlogk : 1 ≤ Real.log G.k`. Rewrite using `[Real.le_log_iff_exp_le hk0]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hlogbb : Cb / 2 ≤ Real.log bb` using `by nlinarith`. Establish `hkCb : 2 ≤ (G.k : ℝ) * Cb`. Rewrite `hkC` using `[div_le_iff₀ hCb]`. Conclude with `hkC`. Establish `hf2r : (2 : ℝ) ≤ G.f` using `by exact_mod_cast hf2`.

Establish `hbase : 2 ≤ (G.k : ℝ) * G.f * Real.log bb`. Establish `e1 : (G.k : ℝ) * 2 * (Cb / 2) ≤ (G.k : ℝ) * G.f * Real.log bb`. Apply `mul_le_mul _ hlogbb (by positivity) (by positivity)` to reduce the goal to its premises. Conclude with `mul_le_mul_of_nonneg_left hf2r hk0.le`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h16 : (16 : ℝ) ≤ ((G.k : ℝ) * G.f * Real.log bb) ^ CDel`. Combine the equalities or inequalities in the displayed calculation. Establish `hD : 16 ≤ G.Del` using `le_trans h16 hyp.hDel`. Unfold `Sz.Glob.lenI`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem t_GlobPositive : GlobPositive := by
  intro CDel Cb hCDel hCb
  refine ⟨max 3 ⌈2 / Cb⌉₊, ?_⟩
  intro ι _ G bb hk hyp
  have hk3 : 3 ≤ G.k := le_trans (le_max_left _ _) hk
  have hkC : 2 / Cb ≤ (G.k : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hk)
  have hk3r : (3 : ℝ) ≤ G.k := by exact_mod_cast hk3
  have hk0 : (0 : ℝ) < G.k := by linarith
  have hbb := hyp.hbb
  have hbb0 : 0 < bb := by linarith
  have hpos : 0 < ((G.k : ℝ) * bb) ^ 8 := by positivity
  have hg1 : 0 < G.g1 := by
    have : (0 : ℝ) < G.g1 := lt_of_lt_of_le hpos hyp.hg1
    exact_mod_cast this
  have hg2 : 0 < G.g2 := by
    have : (0 : ℝ) < G.g2 := lt_of_lt_of_le hpos hyp.hg2
    exact_mod_cast this
  refine ⟨hg1, hg2, ?_⟩
  have hm2 : 2 ≤ G.m := by unfold Sz.Glob.m; omega
  have hf2 : 2 ≤ G.f := le_trans hm2 hyp.hmf
  have hne : Nonempty ι := by
    apply Fintype.card_pos_iff.1
    have : G.f = Fintype.card ι := rfl
    omega
  obtain ⟨w⟩ := hne
  have h1 : (G.k : ℝ) ^ Cb ≤ G.b w 1 := hyp.hnode w 1 le_rfl (by omega)
  have h2 : G.b w 1 ≤ bb ^ 2 := (hyp.hsmall w).hbj 1 le_rfl (by
    show 1 ≤ 2 * G.r + 2
    omega)
  have h3 : (G.k : ℝ) ^ Cb ≤ bb ^ 2 := le_trans h1 h2
  have h4 : Cb * Real.log G.k ≤ 2 * Real.log bb := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hk0 Cb) h3
    rw [Real.log_rpow hk0, Real.log_pow] at this
    exact_mod_cast this
  have hlogk : 1 ≤ Real.log G.k := by
    rw [Real.le_log_iff_exp_le hk0]
    have := Real.exp_one_lt_d9
    linarith
  have hlogbb : Cb / 2 ≤ Real.log bb := by nlinarith
  have hkCb : 2 ≤ (G.k : ℝ) * Cb := by
    rw [div_le_iff₀ hCb] at hkC
    exact hkC
  have hf2r : (2 : ℝ) ≤ G.f := by exact_mod_cast hf2
  have hbase : 2 ≤ (G.k : ℝ) * G.f * Real.log bb := by
    have e1 : (G.k : ℝ) * 2 * (Cb / 2) ≤ (G.k : ℝ) * G.f * Real.log bb := by
      apply mul_le_mul _ hlogbb (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hf2r hk0.le
    nlinarith
  have h16 : (16 : ℝ) ≤ ((G.k : ℝ) * G.f * Real.log bb) ^ CDel := by
    calc (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ CDel := Real.rpow_le_rpow_of_exponent_le (by norm_num) hCDel.le
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) hbase (by linarith)
  have hD : 16 ≤ G.Del := le_trans h16 hyp.hDel
  unfold Sz.Glob.lenI
  linarith

end positivity

section main
open scoped ComplexOrder
/- English proof (translation)
Introduce `hS CA C0 CG CDel cT Cb C C' hCA hC0 hCG hCDel hcT hCb hcTb hC hCCA`. Take `⟨k0, hk0⟩` from `hS CA C0 CG CDel cT Cb hCA hC0 hCG hCDel hcT hCb hcTb`. Establish `hc : 0 < Sz.cExp CDel cT Cb`. Unfold `Sz.cExp`. Establish `: 0 < min ((CDel - 4) / 2) ((cT * Cb - 1) / 4)` using `lt_min (by linarith) (by linarith)`.

Check the signs of the components of the expression. Establish `hMpos : 0 < max C' 5` using `lt_of_lt_of_le (by norm_num) (le_max_right _ _)`. Use `⟨max k0 (⌈(max C' 5) ^ (1 / Sz.cExp CDel cT Cb)⌉₊), ?_⟩` and prove the remaining obligations. Introduce `ι _ G bb Cp Cf Th de de' T T' du du' l hk hyp h16 hCf`. Take `⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16', h17, h18, h19⟩` from `hyp`.

Establish `hmain` using `hk0 ι G bb Cp Cf Th de de' T T' du du' l (le_trans (le_max_left _ _) hk) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16' h17 h18 h19`. Take `⟨hTh, hrest⟩` from `hmain`. Take `⟨hr1, hr2⟩` from `hrest h16 hCf`. Establish `hkM : (max C' 5) ^ (1 / Sz.cExp CDel cT Cb) ≤ (G.k : ℝ)` using `le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hk)`. Establish `hMle : max C' 5 ≤ (G.k : ℝ) ^ Sz.cExp CDel cT Cb`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_mul hMpos.le, one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]`. Use `_ ≤ _ := Real.rpow_le_rpow (by positivity) hkM hc.le`. Establish `hMTh : max C' 5 ≤ Th` using `le_trans hMle hTh`. Establish `hpow : (C / Th) ^ G.f ≤ (CA / Th) ^ G.f` using `pow_le_pow_left₀ (div_nonneg hC h18.le) (div_le_div_of_nonneg_right hCCA h18.le) _`.

Establish `hpn : 0 ≤ (C / Th) ^ G.f` using `pow_nonneg (div_nonneg hC h18.le) _`. Establish `hbb : (bb ^ 7)⁻¹ ≤ 1` using `inv_le_one_of_one_le₀ (one_le_pow₀ h1.hbb.le)`. Establish `hr0 : (0 : ℝ) ≤ G.r` using `Nat.cast_nonneg _`. Establish `hA1 : ((G.r : ℝ) + 1) * (CA / Th) ^ G.f ≤ CA * ((G.r : ℝ) + 1) * (CA / Th) ^ G.f`. Establish `: 0 ≤ ((G.r : ℝ) + 1) * (CA / Th) ^ G.f` using `mul_nonneg (by linarith) (le_trans hpn hpow)`.

Use the polynomial consequences of the given equalities and inequalities. Use `⟨le_trans (le_max_left _ _) hMTh, lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hMTh), le_trans (mul_le_mul_of_nonneg_left hpow hr0) hr1, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul _ hpow hpn (by positivity)` to reduce the goal to its premises.

Conclude with `mul_le_mul_of_nonneg_right hCCA (by linarith)`. Use `_ ≤ _ := hr2`.
-/
theorem t_SizesToRecursion : SizesToRecursion := by
  intro hS CA C0 CG CDel cT Cb C C' hCA hC0 hCG hCDel hcT hCb hcTb hC hCCA
  obtain ⟨k0, hk0⟩ := hS CA C0 CG CDel cT Cb hCA hC0 hCG hCDel hcT hCb hcTb
  have hc : 0 < Sz.cExp CDel cT Cb := by
    unfold Sz.cExp
    have : 0 < min ((CDel - 4) / 2) ((cT * Cb - 1) / 4) := lt_min (by linarith) (by linarith)
    positivity
  have hMpos : 0 < max C' 5 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨max k0 (⌈(max C' 5) ^ (1 / Sz.cExp CDel cT Cb)⌉₊), ?_⟩
  intro ι _ G bb Cp Cf Th de de' T T' du du' l hk hyp h16 hCf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16', h17, h18, h19⟩ := hyp
  have hmain := hk0 ι G bb Cp Cf Th de de' T T' du du' l (le_trans (le_max_left _ _) hk) h1 h2 h3 h4 h5
    h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16' h17 h18 h19
  obtain ⟨hTh, hrest⟩ := hmain
  obtain ⟨hr1, hr2⟩ := hrest h16 hCf
  have hkM : (max C' 5) ^ (1 / Sz.cExp CDel cT Cb) ≤ (G.k : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hk)
  have hMle : max C' 5 ≤ (G.k : ℝ) ^ Sz.cExp CDel cT Cb := by
    calc max C' 5 = ((max C' 5) ^ (1 / Sz.cExp CDel cT Cb)) ^ Sz.cExp CDel cT Cb := by
          rw [← Real.rpow_mul hMpos.le, one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hkM hc.le
  have hMTh : max C' 5 ≤ Th := le_trans hMle hTh
  have hpow : (C / Th) ^ G.f ≤ (CA / Th) ^ G.f :=
    pow_le_pow_left₀ (div_nonneg hC h18.le) (div_le_div_of_nonneg_right hCCA h18.le) _
  have hpn : 0 ≤ (C / Th) ^ G.f := pow_nonneg (div_nonneg hC h18.le) _
  have hbb : (bb ^ 7)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h1.hbb.le)
  have hr0 : (0 : ℝ) ≤ G.r := Nat.cast_nonneg _
  have hA1 : ((G.r : ℝ) + 1) * (CA / Th) ^ G.f ≤ CA * ((G.r : ℝ) + 1) * (CA / Th) ^ G.f := by
    have : 0 ≤ ((G.r : ℝ) + 1) * (CA / Th) ^ G.f :=
      mul_nonneg (by linarith) (le_trans hpn hpow)
    nlinarith
  refine ⟨le_trans (le_max_left _ _) hMTh, lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hMTh),
    le_trans (mul_le_mul_of_nonneg_left hpow hr0) hr1, ?_, ?_⟩
  · calc ((G.r : ℝ) + 1) * (C / Th) ^ G.f ≤ ((G.r : ℝ) + 1) * (CA / Th) ^ G.f :=
          mul_le_mul_of_nonneg_left hpow (by linarith)
      _ ≤ _ := hA1
      _ ≤ _ := hr2
      _ ≤ 1 := hbb
  · calc C * ((G.r : ℝ) + 1) * (C / Th) ^ G.f ≤ CA * ((G.r : ℝ) + 1) * (CA / Th) ^ G.f := by
          apply mul_le_mul _ hpow hpn (by positivity)
          exact mul_le_mul_of_nonneg_right hCCA (by linarith)
      _ ≤ _ := hr2

/- English proof (translation)
Establish `hmem : D.emp ∈ D.Wb D.Ntop`. Unfold `TB.Data.Wb`. Rewrite using `[Finset.mem_filter]`. Conclude with `⟨D.emp_mem, by rw [D.cnt_emp]; exact Nat.zero_le _⟩`. Establish `ht` using `hE D.emp hmem`.

Use `ge_of_tendsto ht ?_` and prove the remaining obligations. Use `eventually_nhdsWithin_of_forall ?_` and prove the remaining obligations. Introduce `ε hε`. Establish `hp` using `hG ε hε 0 D.emp {([] : TB.Pt E)}`. Unfold `TB.PSDOn at hp`.

Establish `hd` using `hp.diag_nonneg (i := ⟨[], by simp⟩)`. Establish `hre : 0 ≤ (D.gram ε 0 D.emp [] []).re`. Use `(Complex.le_def.1 hd).1` as an intermediate fact. Simplify using `using this`. Rewrite using `[D.wt_emp, div_one]`.

Conclude with `hre`.
-/
theorem jn_nonneg {E W : Type} [Field E] (D : TB.Data E W) (jn : ℝ) (hG : D.GramPSD) (hE : D.EstE jn) :
    0 ≤ jn := by
  have hmem : D.emp ∈ D.Wb D.Ntop := by
    unfold TB.Data.Wb
    rw [Finset.mem_filter]
    exact ⟨D.emp_mem, by rw [D.cnt_emp]; exact Nat.zero_le _⟩
  have ht := hE D.emp hmem
  refine ge_of_tendsto ht ?_
  refine eventually_nhdsWithin_of_forall ?_
  intro ε hε
  have hp := hG ε hε 0 D.emp {([] : TB.Pt E)}
  unfold TB.PSDOn at hp
  have hd := hp.diag_nonneg (i := ⟨[], by simp⟩)
  have hre : 0 ≤ (D.gram ε 0 D.emp [] []).re := by
    have := (Complex.le_def.1 hd).1
    simpa using this
  rw [D.wt_emp, div_one]; exact hre

/- English proof (translation)
Introduce `hA hS C₁ C₄ Cthr h1 h4`. Take `⟨CT, CT', hT⟩` from `hA C₁ C₄ h1 h4`. Use `⟨max (max Cthr 1) |CT|, |CT|, le_trans (le_max_left _ _) (le_max_left _ _), le_trans (le_max_right _ _) (le_max_left _ _), abs_nonneg _, le_max_right _ _, ?_⟩` and prove the remaining obligations. Introduce `C0 CG CDel cT Cb hC0 hCG hCDel hcT hCb hcTb`. Take `⟨k0, hk0⟩` from `t_SizesToRecursion hS (max (max Cthr 1) |CT|) C0 CG CDel cT Cb |CT| CT' (le_trans (le_max_right _ _) (le_max_left _ _)) hC0 hCG hCDel hcT hCb hcTb (abs_nonneg _) (le_max_right _ _)`.

Use `⟨k0, ?_⟩` and prove the remaining obligations. Introduce `ι _ G bb Cp Cf Th de de' T T' du du' l hk hyp h16 hCf E W _ D jn H _ _ _ Vt c hr hf hrec he P _ B hI hδ hSm`. Take `⟨s1, s2, s3, s4, s5⟩` from `hk0 ι G bb Cp Cf Th de de' T T' du du' l hk hyp h16 hCf`. Take `⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩` from `hrec`. Establish `hjn` using `jn_nonneg D jn a5 a15`.

Establish `habs : (CT / Th) ^ D.f ≤ (|CT| / Th) ^ D.f`. Combine the equalities or inequalities in the displayed calculation. Establish `hpn : 0 ≤ (|CT| / Th) ^ D.f` using `by positivity`. Establish `hr0 : (0 : ℝ) ≤ D.r` using `Nat.cast_nonneg _`. Establish `hsm : (D.r : ℝ) * (CT / Th) ^ D.f ≤ 1`.

Use `le_trans (mul_le_mul_of_nonneg_left habs hr0) ?_` and prove the remaining obligations. Rewrite using `[hr, hf]`. Conclude with `s3`. Prove the components needed by the constructor for the conclusion. Unfold `S3.MassData.InTheoremA`.

Apply `hSm` to reduce the goal to its premises. Introduce `R`. Use `hT E W D Th jn H Vt c a1 a2 a3 s1 hsm a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 R` as an intermediate fact. Rewrite `this` using `[Finset.prod_eq_one (fun i hi => by rw [he i hi, add_zero]), mul_one]`. Use `le_trans this ?_` and prove the remaining obligations.

Rewrite using `[hδ, hI]`. Apply `mul_le_mul_of_nonneg_right _ hjn` to reduce the goal to its premises. Establish `h2 : CT * ((D.r : ℝ) + 1) * (CT / Th) ^ D.f ≤ |CT| * ((D.r : ℝ) + 1) * (|CT| / Th) ^ D.f`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[abs_mul, abs_mul, abs_pow, abs_div, abs_of_pos a3, abs_of_nonneg (by linarith : (0:ℝ) ≤ (D.r : ℝ) + 1)]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hδ, hr, hf]`. Conclude with `s5`.
-/
theorem t_MainJoint : MainJoint := by
  intro hA hS C₁ C₄ Cthr h1 h4
  obtain ⟨CT, CT', hT⟩ := hA C₁ C₄ h1 h4
  refine ⟨max (max Cthr 1) |CT|, |CT|, le_trans (le_max_left _ _) (le_max_left _ _),
    le_trans (le_max_right _ _) (le_max_left _ _), abs_nonneg _, le_max_right _ _, ?_⟩
  intro C0 CG CDel cT Cb hC0 hCG hCDel hcT hCb hcTb
  obtain ⟨k0, hk0⟩ := t_SizesToRecursion hS (max (max Cthr 1) |CT|) C0 CG CDel cT Cb |CT| CT'
    (le_trans (le_max_right _ _) (le_max_left _ _)) hC0 hCG hCDel hcT hCb hcTb (abs_nonneg _)
    (le_max_right _ _)
  refine ⟨k0, ?_⟩
  intro ι _ G bb Cp Cf Th de de' T T' du du' l hk hyp h16 hCf E W _ D jn H _ _ _ Vt c hr hf hrec he
    P _ B hI hδ hSm
  obtain ⟨s1, s2, s3, s4, s5⟩ := hk0 ι G bb Cp Cf Th de de' T T' du du' l hk hyp h16 hCf
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := hrec
  have hjn := jn_nonneg D jn a5 a15
  have habs : (CT / Th) ^ D.f ≤ (|CT| / Th) ^ D.f := by
    calc (CT / Th) ^ D.f ≤ |(CT / Th) ^ D.f| := le_abs_self _
      _ = (|CT| / Th) ^ D.f := by rw [abs_pow, abs_div, abs_of_pos a3]
  have hpn : 0 ≤ (|CT| / Th) ^ D.f := by positivity
  have hr0 : (0 : ℝ) ≤ D.r := Nat.cast_nonneg _
  have hsm : (D.r : ℝ) * (CT / Th) ^ D.f ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left habs hr0) ?_
    rw [hr, hf]; exact s3
  constructor
  · unfold S3.MassData.InTheoremA
    apply hSm
    intro R
    have := hT E W D Th jn H Vt c a1 a2 a3 s1 hsm a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 R
    rw [Finset.prod_eq_one (fun i hi => by rw [he i hi, add_zero]), mul_one] at this
    refine le_trans this ?_
    rw [hδ, hI]
    apply mul_le_mul_of_nonneg_right _ hjn
    have h2 : CT * ((D.r : ℝ) + 1) * (CT / Th) ^ D.f ≤ |CT| * ((D.r : ℝ) + 1) * (|CT| / Th) ^ D.f := by
      calc CT * ((D.r : ℝ) + 1) * (CT / Th) ^ D.f ≤ |CT * ((D.r : ℝ) + 1) * (CT / Th) ^ D.f| := le_abs_self _
        _ = |CT| * ((D.r : ℝ) + 1) * (|CT| / Th) ^ D.f := by
            rw [abs_mul, abs_mul, abs_pow, abs_div, abs_of_pos a3, abs_of_nonneg (by linarith : (0:ℝ) ≤ (D.r : ℝ) + 1)]
    linarith
  · rw [hδ, hr, hf]; exact s5

/- English proof (translation)
Introduce `hLJ hIS hBox hLat hId hNorm hDeg hFP hX`. Take `⟨C, hC1, hC⟩` from `hLJ hBox`. Use `⟨C * 2 ^ ((5 : ℝ) - 5 / 2), ?_, ?_⟩` and prove the remaining obligations. Establish `: (1 : ℝ) ≤ 2 ^ ((5 : ℝ) - 5 / 2)` using `Real.one_le_rpow (by norm_num) (by norm_num)`. Use the polynomial consequences of the given equalities and inequalities.

Introduce `E W _ _ _ D e G Cc de de' T T' l Θ hU hInst hg1 hg2 hCc hlen hΘ hGr`. Take `⟨hSB, hIdl, _⟩` from `hIS hLat hId hNorm hDeg hFP hX E W D e G Cc de de' T T' l Θ hU hInst hg1 hg2 hCc hlen (by linarith) hGr`. Use `⟨hSB, ?_⟩` and prove the remaining obligations. Establish `hK : D.K = 5` using `hInst.2.1`. Use `hC E W D e _ _ Θ 2 hInst.2.2.1 (by omega) (by norm_num) (by linarith) hIdl` as an intermediate fact.

Establish `hK' : (D.K : ℝ) = 5` using `by exact_mod_cast hK`. Rewrite `this`, the goal using `[hK']`. Conclude with `this`.
-/
theorem t_InstLatticeSums : InstLatticeSums := by
  intro hLJ hIS hBox hLat hId hNorm hDeg hFP hX
  obtain ⟨C, hC1, hC⟩ := hLJ hBox
  refine ⟨C * 2 ^ ((5 : ℝ) - 5 / 2), ?_, ?_⟩
  · have : (1 : ℝ) ≤ 2 ^ ((5 : ℝ) - 5 / 2) := Real.one_le_rpow (by norm_num) (by norm_num)
    nlinarith
  intro E W _ _ _ D e G Cc de de' T T' l Θ hU hInst hg1 hg2 hCc hlen hΘ hGr
  obtain ⟨hSB, hIdl, _⟩ := hIS hLat hId hNorm hDeg hFP hX E W D e G Cc de de' T T' l Θ hU hInst hg1 hg2 hCc
    hlen (by linarith) hGr
  refine ⟨hSB, ?_⟩
  have hK : D.K = 5 := hInst.2.1
  have := hC E W D e _ _ Θ 2 hInst.2.2.1 (by omega) (by norm_num) (by linarith) hIdl
  have hK' : (D.K : ℝ) = 5 := by exact_mod_cast hK
  rw [hK'] at this ⊢
  exact this

/- English proof (translation)
Introduce `m i C ka N I A g B`. Establish `h : 2 * i - 2 = 2 * (i - 1) + 1 - 1` using `by omega`. Apply the tactic sequence `constructor <;> simp only [Sz.xThreshold, Sz.lamThreshold, Sz.xHat, Sz.lamHat, h]`.
-/
theorem t_XIsLamOne : XIsLamOne := by
  intro m i C ka N I A g B
  have h : 2 * i - 2 = 2 * (i - 1) + 1 - 1 := by omega
  constructor <;> simp only [Sz.xThreshold, Sz.lamThreshold, Sz.xHat, Sz.lamHat, h]

/- English proof (translation)
Introduce `hA hS C₁ C₄ Cthr h1 h4`. Take `⟨CT, CT', hT⟩` from `hA C₁ C₄ h1 h4`. Use `⟨max (max Cthr 1) |CT|, |CT|, le_trans (le_max_left _ _) (le_max_left _ _), le_trans (le_max_right _ _) (le_max_left _ _), abs_nonneg _, le_max_right _ _, ?_⟩` and prove the remaining obligations. Introduce `C0 CG CDel cT Cb hC0 hCG hCDel hcT hCb hcTb`. Take `⟨k0, hk0⟩` from `t_SizesToRecursion hS (max (max Cthr 1) |CT|) C0 CG CDel cT Cb |CT| CT' (le_trans (le_max_right _ _) (le_max_left _ _)) hC0 hCG hCDel hcT hCb hcTb (abs_nonneg _) (le_max_right _ _)`.

Use `⟨k0, ?_⟩` and prove the remaining obligations. Introduce `ι _ G bb Cp Cf Th de de' T T' du du' l hk hyp h16 hCf E W _ D jn H _ _ _ Vt c hr hf hrec he P _ B he1 hI hδ hrow`. Take `⟨s1, s2, s3, s4, s5⟩` from `hk0 ι G bb Cp Cf Th de de' T T' du du' l hk hyp h16 hCf`. Take `⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩` from `hrec`. Establish `hjn` using `jn_nonneg D jn a5 a15`.

Establish `habs : (CT / Th) ^ D.f ≤ (|CT| / Th) ^ D.f`. Combine the equalities or inequalities in the displayed calculation. Establish `hpn : 0 ≤ (|CT| / Th) ^ D.f` using `by positivity`. Establish `hr0 : (0 : ℝ) ≤ D.r` using `Nat.cast_nonneg _`. Establish `hsm : (D.r : ℝ) * (CT / Th) ^ D.f ≤ 1`.

Use `le_trans (mul_le_mul_of_nonneg_left habs hr0) ?_` and prove the remaining obligations. Rewrite using `[hr, hf]`. Conclude with `s3`. Establish `hprod : ∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i) = B.e1`. Rewrite using `[Finset.prod_Icc_succ_top (by omega : 1 ≤ D.r + 1), Finset.prod_eq_one (fun i hi => by rw [he i hi, add_zero]), one_mul, he1]`.

Establish `he0 : 0 ≤ D.e (D.r + 1)` using `(a9 (D.r + 1) 1 le_rfl (by omega) le_rfl).1.1`. Establish `he1p : 0 ≤ B.e1` using `by rw [← he1]; linarith`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `key` using `hrow ((1 + B.δ) * B.e1 * B.IntN) (fun R => by`. Use `hT E W D Th jn H Vt c a1 a2 a3 s1 hsm a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 R` as an intermediate fact.

Rewrite `this` using `[hprod]`. Use `le_trans this ?_` and prove the remaining obligations. Rewrite using `[hδ, hI]`. Establish `h2 : CT * ((D.r : ℝ) + 1) * (CT / Th) ^ D.f ≤ |CT| * ((D.r : ℝ) + 1) * (|CT| / Th) ^ D.f`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[abs_mul, abs_mul, abs_pow, abs_div, abs_of_pos a3, abs_of_nonneg (by linarith : (0:ℝ) ≤ (D.r : ℝ) + 1)]`. Apply `mul_le_mul_of_nonneg_right _ hjn` to reduce the goal to its premises. Apply `mul_le_mul_of_nonneg_right _ he1p` to reduce the goal to its premises. Use the proof step `linarith)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hδ]`. Check the signs of the components of the expression. Rewrite using `[hδ, hr, hf]`. Conclude with `s5`.
-/
theorem t_MainJointForm : MainJointForm := by
  intro hA hS C₁ C₄ Cthr h1 h4
  obtain ⟨CT, CT', hT⟩ := hA C₁ C₄ h1 h4
  refine ⟨max (max Cthr 1) |CT|, |CT|, le_trans (le_max_left _ _) (le_max_left _ _),
    le_trans (le_max_right _ _) (le_max_left _ _), abs_nonneg _, le_max_right _ _, ?_⟩
  intro C0 CG CDel cT Cb hC0 hCG hCDel hcT hCb hcTb
  obtain ⟨k0, hk0⟩ := t_SizesToRecursion hS (max (max Cthr 1) |CT|) C0 CG CDel cT Cb |CT| CT'
    (le_trans (le_max_right _ _) (le_max_left _ _)) hC0 hCG hCDel hcT hCb hcTb (abs_nonneg _)
    (le_max_right _ _)
  refine ⟨k0, ?_⟩
  intro ι _ G bb Cp Cf Th de de' T T' du du' l hk hyp h16 hCf E W _ D jn H _ _ _ Vt c hr hf hrec he
    P _ B he1 hI hδ hrow
  obtain ⟨s1, s2, s3, s4, s5⟩ := hk0 ι G bb Cp Cf Th de de' T T' du du' l hk hyp h16 hCf
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := hrec
  have hjn := jn_nonneg D jn a5 a15
  have habs : (CT / Th) ^ D.f ≤ (|CT| / Th) ^ D.f := by
    calc (CT / Th) ^ D.f ≤ |(CT / Th) ^ D.f| := le_abs_self _
      _ = (|CT| / Th) ^ D.f := by rw [abs_pow, abs_div, abs_of_pos a3]
  have hpn : 0 ≤ (|CT| / Th) ^ D.f := by positivity
  have hr0 : (0 : ℝ) ≤ D.r := Nat.cast_nonneg _
  have hsm : (D.r : ℝ) * (CT / Th) ^ D.f ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left habs hr0) ?_
    rw [hr, hf]; exact s3
  have hprod : ∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i) = B.e1 := by
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ D.r + 1),
      Finset.prod_eq_one (fun i hi => by rw [he i hi, add_zero]), one_mul, he1]
  have he0 : 0 ≤ D.e (D.r + 1) := (a9 (D.r + 1) 1 le_rfl (by omega) le_rfl).1.1
  have he1p : 0 ≤ B.e1 := by rw [← he1]; linarith
  refine ⟨?_, ?_, ?_⟩
  · have key := hrow ((1 + B.δ) * B.e1 * B.IntN) (fun R => by
      have := hT E W D Th jn H Vt c a1 a2 a3 s1 hsm a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 R
      rw [hprod] at this
      refine le_trans this ?_
      rw [hδ, hI]
      have h2 : CT * ((D.r : ℝ) + 1) * (CT / Th) ^ D.f ≤
          |CT| * ((D.r : ℝ) + 1) * (|CT| / Th) ^ D.f := by
        calc CT * ((D.r : ℝ) + 1) * (CT / Th) ^ D.f
            ≤ |CT * ((D.r : ℝ) + 1) * (CT / Th) ^ D.f| := le_abs_self _
          _ = |CT| * ((D.r : ℝ) + 1) * (|CT| / Th) ^ D.f := by
              rw [abs_mul, abs_mul, abs_pow, abs_div, abs_of_pos a3,
                abs_of_nonneg (by linarith : (0:ℝ) ≤ (D.r : ℝ) + 1)]
      apply mul_le_mul_of_nonneg_right _ hjn
      apply mul_le_mul_of_nonneg_right _ he1p
      linarith)
    calc B.c0 * B.c0' * B.KV ≤ B.n0c * ((1 + B.δ) * B.e1 * B.IntN) := key
      _ = _ := by ring
  · rw [hδ]; positivity
  · rw [hδ, hr, hf]; exact s5

/- English proof (translation)
Introduce `hA hS hBox hLat hId hNorm hDeg C₄ Cthr h4`. Take `⟨C₁, hC1, hIL⟩` from `t_InstLatticeSums t_LatticeSumsJoint t_InstSizes hBox hLat hId hNorm hDeg t_FrameProducts t_XIsLamOne`. Take `⟨CA, C, b1, b2, b3, b4, hM⟩` from `t_MainJointForm hA hS C₁ C₄ Cthr hC1 h4`. Use `⟨CA, C, b1, b2, b3, b4, ?_⟩` and prove the remaining obligations. Introduce `C0 CG CDel cT Cb hC0 hCG hCDel hcT hCb hcTb`.

Take `⟨k1, hk1⟩` from `hM C0 CG CDel cT Cb hC0 hCG hCDel hcT hCb hcTb`. Take `⟨k2, hk2⟩` from `t_SizesToRecursion hS CA C0 CG CDel cT Cb C 0 b2 hC0 hCG hCDel hcT hCb hcTb b3 b4`. Take `⟨k3, hk3⟩` from `t_GlobPositive CDel Cb hCDel hCb`. Use `⟨max (max k1 k2) k3, ?_⟩` and prove the remaining obligations. Introduce `E W _ _ _ D e G bb Cp Cf Th de de' T T' du du' l hk hyp h16 hCf hU hInst jn H _ _ _ Vt c hrec he P _ B he1 hI hδ hrow`.

Take `⟨hg1, hg2, hlen⟩` from `hk3 (InfinitePlace E) G bb (le_trans (le_max_right _ _) hk) hyp.1`. Establish `s` using `hk2 (InfinitePlace E) G bb Cp Cf Th de de' T T' du du' l (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk) hyp h16 hCf`. Establish `hTh4 : 4 < Th` using `s.2.1`. Establish `hGr : IsGreatest (G.thrSet CA de de' T T' l) ((Th ^ G.f)⁻¹)`. Take `⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩` from `hyp`.

Conclude with `h`. Take `⟨hSB, hLS⟩` from `hIL E W D e G CA de de' T T' l Th hU hInst hg1 hg2 (by linarith) hlen hTh4 hGr`. Establish `hf : D.f = G.f`. Use `Fintype.card_congr e` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin]`.

Conclude with `this`. Establish `hf1 : 1 ≤ D.f`. Take `⟨_, d2, d3⟩` from `hDeg E`. Rewrite using `[hf]`. Unfold `Sz.Glob.f`.

Use linear arithmetic over natural numbers and integers. Establish `hK : 4 ≤ D.K` using `by rw [hInst.2.1]; norm_num`. Take `⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩` from `hrec`. Conclude with `hk1 (InfinitePlace E) G bb Cp Cf Th de de' T T' du du' l (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk) hyp h16 hCf E W D jn H Vt c hInst.1 hf ⟨hK, hf1, by linarith, hSB, r1, r2, r3, r4, r5, r6, r7, r8, r9, hLS, r10, r11, r12⟩ he P B he1 hI hδ hrow`.
-/
theorem t_MainJointInst : MainJointInst := by
  intro hA hS hBox hLat hId hNorm hDeg C₄ Cthr h4
  obtain ⟨C₁, hC1, hIL⟩ := t_InstLatticeSums t_LatticeSumsJoint t_InstSizes hBox hLat
    hId hNorm hDeg t_FrameProducts t_XIsLamOne
  obtain ⟨CA, C, b1, b2, b3, b4, hM⟩ := t_MainJointForm hA hS C₁ C₄ Cthr hC1 h4
  refine ⟨CA, C, b1, b2, b3, b4, ?_⟩
  intro C0 CG CDel cT Cb hC0 hCG hCDel hcT hCb hcTb
  obtain ⟨k1, hk1⟩ := hM C0 CG CDel cT Cb hC0 hCG hCDel hcT hCb hcTb
  obtain ⟨k2, hk2⟩ := t_SizesToRecursion hS CA C0 CG CDel cT Cb C 0 b2 hC0 hCG hCDel hcT hCb hcTb
    b3 b4
  obtain ⟨k3, hk3⟩ := t_GlobPositive CDel Cb hCDel hCb
  refine ⟨max (max k1 k2) k3, ?_⟩
  intro E W _ _ _ D e G bb Cp Cf Th de de' T T' du du' l hk hyp h16 hCf hU hInst jn H
    _ _ _ Vt c hrec he P _ B he1 hI hδ hrow
  obtain ⟨hg1, hg2, hlen⟩ := hk3 (InfinitePlace E) G bb (le_trans (le_max_right _ _) hk) hyp.1
  have s := hk2 (InfinitePlace E) G bb Cp Cf Th de de' T T' du du' l
    (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk) hyp h16 hCf
  have hTh4 : 4 < Th := s.2.1
  have hGr : IsGreatest (G.thrSet CA de de' T T' l) ((Th ^ G.f)⁻¹) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := hyp
    exact h
  obtain ⟨hSB, hLS⟩ := hIL E W D e G CA de de' T T' l Th hU hInst hg1 hg2 (by linarith) hlen hTh4 hGr
  have hf : D.f = G.f := by
    have := Fintype.card_congr e
    rw [Fintype.card_fin] at this
    exact this
  have hf1 : 1 ≤ D.f := by
    obtain ⟨_, d2, d3⟩ := hDeg E
    rw [hf]; unfold Sz.Glob.f; omega
  have hK : 4 ≤ D.K := by rw [hInst.2.1]; norm_num
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩ := hrec
  exact hk1 (InfinitePlace E) G bb Cp Cf Th de de' T T' du du' l
    (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk) hyp h16
    hCf E W D jn H Vt c hInst.1 hf
    ⟨hK, hf1, by linarith, hSB, r1, r2, r3, r4, r5, r6, r7, r8, r9, hLS, r10, r11, r12⟩ he P B he1 hI hδ
    hrow

end main

section kernels
open scoped ComplexOrder ComplexConjugate Matrix
section psd
variable {α : Type} {F : Finset α}

/- English proof (translation)
Unfold `TB.PSDOn at *`. Establish `: (Matrix.of fun x y : F => k' x y) = Matrix.of fun x y : F => k x y`. Use extensionality with `x y`. Conclude with `(h x x.2 y y.2).symm`. Rewrite using `[this]`.

Conclude with `hk`.
-/
theorem psd_congr {k k' : α → α → ℂ} (h : ∀ x ∈ F, ∀ y ∈ F, k x y = k' x y) (hk : TB.PSDOn F k) :
    TB.PSDOn F k' := by
  unfold TB.PSDOn at *
  have : (Matrix.of fun x y : F => k' x y) = Matrix.of fun x y : F => k x y := by
    ext x y; exact (h x x.2 y y.2).symm
  rw [this]; exact hk

/- English proof (translation)
Unfold `TB.PSDOn`. Conclude with `Matrix.PosSemidef.zero`.
-/
theorem psd_zero : TB.PSDOn F (fun _ _ : α => (0 : ℂ)) := by
  unfold TB.PSDOn; exact Matrix.PosSemidef.zero

/- English proof (translation)
Unfold `TB.PSDOn at *`. Conclude with `hk.add hk'`.
-/
theorem psd_add {k k' : α → α → ℂ} (hk : TB.PSDOn F k) (hk' : TB.PSDOn F k') :
    TB.PSDOn F (fun x y => k x y + k' x y) := by
  unfold TB.PSDOn at *
  exact hk.add hk'

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using psd_zero`. Consider the case `insert a s ha ih`. Establish `h1` using `psd_add (hk a (Finset.mem_insert_self a s)) (ih (fun i hi => hk i (Finset.mem_insert_of_mem hi)))`. Use `psd_congr ?_ h1` and prove the remaining obligations.

Introduce `x _ y _`. Rewrite using `[Finset.sum_insert ha]`.
-/
theorem psd_sum {ι : Type} (s : Finset ι) (k : ι → α → α → ℂ) (hk : ∀ i ∈ s, TB.PSDOn F (k i)) :
    TB.PSDOn F (fun x y => ∑ i ∈ s, k i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using psd_zero
  | insert a s ha ih =>
    have h1 := psd_add (hk a (Finset.mem_insert_self a s))
      (ih (fun i hi => hk i (Finset.mem_insert_of_mem hi)))
    refine psd_congr ?_ h1
    intro x _ y _
    rw [Finset.sum_insert ha]
end psd

/- English proof (translation)
Introduce `E α P _ _ S F hok`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `t t' ht ht' h hh h' hh' hne`. Simplify using `only [prodSys] at hne ⊢`. Rewrite using `[AddSubgroup.mem_iInf]`.

Introduce `p`. Conclude with `(hok p).1 t t' ht ht' h hh h' hh' (fun h0 => hne (Finset.prod_eq_zero (Finset.mem_univ p) h0))`. Introduce `t ht`. Conclude with `hS α P F (fun p => (S p).N t t) (fun p => (hok p).2.1 t ht)`. Introduce `t t' htt h hh h' hh'`.

Simplify using `only [prodSys] at htt ⊢`. Rewrite `htt` using `[AddSubgroup.mem_iInf]`. Conclude with `Finset.prod_congr rfl (fun p _ => (hok p).2.2.1 t t' (htt p) h hh h' hh')`. Introduce `t`. Conclude with `hS α P F (fun p => (S p).Th t) (fun p => (hok p).2.2.2.1 t)`.

Introduce `t ht`. Conclude with `hD α P F (fun p => (S p).N t t) (fun p => (S p).Th t) (fun p => (hok p).2.1 t ht) (fun p => (hok p).2.2.2.2.1 t ht)`. Introduce `R hR`. Simplify using `only [prodSys] at hR ⊢`. Set `ρ : P → E → E` to `fun p t => ((t : E ⧸ (S p).L)).out`.

Establish `hρ : ∀ p t, t - ρ p t ∈ (S p).L`. Introduce `p t`. Establish `h1 : ((ρ p t : E) : E ⧸ (S p).L) = (t : E ⧸ (S p).L)` using `Quotient.out_eq' _`. Establish `h2` using `(QuotientAddGroup.eq (s := (S p).L)).1 h1`. Establish `: t - ρ p t = -ρ p t + t` using `by abel`.

Rewrite using `[this]`. Conclude with `h2`. Establish `hρeq : ∀ p t t', ρ p t - ρ p t' ∈ (S p).L → ρ p t = ρ p t'`. Introduce `p t t' h`. Establish `h1 : ((ρ p t : E) : E ⧸ (S p).L) = ((ρ p t' : E) : E ⧸ (S p).L)`.

Rewrite using `[QuotientAddGroup.eq]`. Establish `: -ρ p t + ρ p t' = -(ρ p t - ρ p t')` using `by abel`. Rewrite using `[this]`. Conclude with `neg_mem h`. Establish `h2 : ((ρ p t : E) : E ⧸ (S p).L) = (t : E ⧸ (S p).L)` using `Quotient.out_eq' _`.

Establish `h3 : ((ρ p t' : E) : E ⧸ (S p).L) = (t' : E ⧸ (S p).L)` using `Quotient.out_eq' _`. Use `show ((t : E ⧸ (S p).L)).out = ((t' : E ⧸ (S p).L)).out`. Rewrite using `[← h2, ← h3, h1]`. Set `T : P → Finset E` to `fun p => R.image (ρ p)`. Set `ι : E → (P → E)` to `fun t p => ρ p t`.

Establish `hιinj : Set.InjOn ι R`. Introduce `t ht t' ht' h`. Apply `hR t ht t' ht'` to reduce the goal to its premises. Rewrite using `[AddSubgroup.mem_iInf]`. Introduce `p`.

Establish `h1 : ρ p t = ρ p t'` using `congrFun h p`. Establish `h2` using `hρ p t`. Establish `h3` using `hρ p t'`. Establish `: t - t' = (t - ρ p t) - (t' - ρ p t')` using `by rw [h1]; abel`. Rewrite using `[this]`.

Conclude with `sub_mem h2 h3`. Establish `hιmem : R.image ι ⊆ Fintype.piFinset T`. Introduce `τ hτ`. Take `⟨t, ht, rfl⟩` from `Finset.mem_image.1 hτ`. Conclude with `Fintype.mem_piFinset.2 (fun p => Finset.mem_image_of_mem _ ht)`.

Establish `hTinc : ∀ p, ∀ x ∈ T p, ∀ y ∈ T p, x - y ∈ (S p).L → x = y`. Introduce `p x hx y hy hxy`. Take `⟨t, _, rfl⟩` from `Finset.mem_image.1 hx`. Take `⟨t', _, rfl⟩` from `Finset.mem_image.1 hy`. Conclude with `hρeq p t t' hxy`.

Establish `hA : TB.PSDOn F (fun h h' => ∏ p, (S p).B h h' - ∏ p, ∑ x ∈ T p, (S p).Th x h h')` using `hD α P F (fun p h h' => ∑ x ∈ T p, (S p).Th x h h') (fun p => (S p).B) (fun p => psd_sum (T p) (fun x => (S p).Th x) (fun x _ => (hok p).2.2.2.1 x)) (fun p => (hok p).2.2.2.2.2 (T p) (hTinc p))`. Establish `hB : ∀ Q : Finset (P → E), TB.PSDOn F (fun h h' => ∑ τ ∈ Q, ∏ p, (S p).Th (τ p) h h')`. Introduce `Q`. Apply `psd_sum Q (fun τ h h' => ∏ p, (S p).Th (τ p) h h')` to reduce the goal to its premises. Introduce `τ _`.

Conclude with `hS α P F (fun p => (S p).Th (τ p)) (fun p => (hok p).2.2.2.1 (τ p))`. Use `psd_congr ?_ (psd_add hA (hB (Fintype.piFinset T \ R.image ι)))` and prove the remaining obligations. Introduce `h hh h' hh'`. Establish `h1 : ∑ t ∈ R, ∏ p, (S p).Th t h h' = ∑ τ ∈ R.image ι, ∏ p, (S p).Th (τ p) h h'`. Rewrite using `[Finset.sum_image hιinj]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `t _`. Conclude with `Finset.prod_congr rfl (fun p _ => (hok p).2.2.1 t (ρ p t) (hρ p t) h hh h' hh')`. Establish `h2 : ∏ p, ∑ x ∈ T p, (S p).Th x h h' = ∑ τ ∈ Fintype.piFinset T, ∏ p, (S p).Th (τ p) h h'` using `Finset.prod_univ_sum T (fun p x => (S p).Th x h h')`. Establish `h3` using `Finset.sum_sdiff (f := fun τ => ∏ p, (S p).Th (τ p) h h') hιmem`.

Rewrite using `[h1, h2, ← h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem t_ProductLemma (hS : SchurProduct) (hD : ProductDomination) : ProductLemma := by
  classical
  intro E α P _ _ S F hok
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t t' ht ht' h hh h' hh' hne
    simp only [prodSys] at hne ⊢
    rw [AddSubgroup.mem_iInf]
    intro p
    exact (hok p).1 t t' ht ht' h hh h' hh' (fun h0 => hne (Finset.prod_eq_zero (Finset.mem_univ p) h0))
  · intro t ht
    exact hS α P F (fun p => (S p).N t t) (fun p => (hok p).2.1 t ht)
  · intro t t' htt h hh h' hh'
    simp only [prodSys] at htt ⊢
    rw [AddSubgroup.mem_iInf] at htt
    exact Finset.prod_congr rfl (fun p _ => (hok p).2.2.1 t t' (htt p) h hh h' hh')
  · intro t
    exact hS α P F (fun p => (S p).Th t) (fun p => (hok p).2.2.2.1 t)
  · intro t ht
    exact hD α P F (fun p => (S p).N t t) (fun p => (S p).Th t) (fun p => (hok p).2.1 t ht)
      (fun p => (hok p).2.2.2.2.1 t ht)
  · intro R hR
    simp only [prodSys] at hR ⊢

    let ρ : P → E → E := fun p t => ((t : E ⧸ (S p).L)).out
    have hρ : ∀ p t, t - ρ p t ∈ (S p).L := by
      intro p t
      have h1 : ((ρ p t : E) : E ⧸ (S p).L) = (t : E ⧸ (S p).L) := Quotient.out_eq' _
      have h2 := (QuotientAddGroup.eq (s := (S p).L)).1 h1
      have : t - ρ p t = -ρ p t + t := by abel
      rw [this]; exact h2
    have hρeq : ∀ p t t', ρ p t - ρ p t' ∈ (S p).L → ρ p t = ρ p t' := by
      intro p t t' h
      have h1 : ((ρ p t : E) : E ⧸ (S p).L) = ((ρ p t' : E) : E ⧸ (S p).L) := by
        rw [QuotientAddGroup.eq]
        have : -ρ p t + ρ p t' = -(ρ p t - ρ p t') := by abel
        rw [this]; exact neg_mem h
      have h2 : ((ρ p t : E) : E ⧸ (S p).L) = (t : E ⧸ (S p).L) := Quotient.out_eq' _
      have h3 : ((ρ p t' : E) : E ⧸ (S p).L) = (t' : E ⧸ (S p).L) := Quotient.out_eq' _
      show ((t : E ⧸ (S p).L)).out = ((t' : E ⧸ (S p).L)).out
      rw [← h2, ← h3, h1]
    let T : P → Finset E := fun p => R.image (ρ p)
    let ι : E → (P → E) := fun t p => ρ p t
    have hιinj : Set.InjOn ι R := by
      intro t ht t' ht' h
      apply hR t ht t' ht'
      rw [AddSubgroup.mem_iInf]
      intro p
      have h1 : ρ p t = ρ p t' := congrFun h p
      have h2 := hρ p t
      have h3 := hρ p t'
      have : t - t' = (t - ρ p t) - (t' - ρ p t') := by rw [h1]; abel
      rw [this]; exact sub_mem h2 h3
    have hιmem : R.image ι ⊆ Fintype.piFinset T := by
      intro τ hτ
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hτ
      exact Fintype.mem_piFinset.2 (fun p => Finset.mem_image_of_mem _ ht)
    have hTinc : ∀ p, ∀ x ∈ T p, ∀ y ∈ T p, x - y ∈ (S p).L → x = y := by
      intro p x hx y hy hxy
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨t', _, rfl⟩ := Finset.mem_image.1 hy
      exact hρeq p t t' hxy

    have hA : TB.PSDOn F (fun h h' => ∏ p, (S p).B h h' - ∏ p, ∑ x ∈ T p, (S p).Th x h h') :=
      hD α P F (fun p h h' => ∑ x ∈ T p, (S p).Th x h h') (fun p => (S p).B)
        (fun p => psd_sum (T p) (fun x => (S p).Th x) (fun x _ => (hok p).2.2.2.1 x))
        (fun p => (hok p).2.2.2.2.2 (T p) (hTinc p))

    have hB : ∀ Q : Finset (P → E), TB.PSDOn F (fun h h' => ∑ τ ∈ Q, ∏ p, (S p).Th (τ p) h h') := by
      intro Q
      apply psd_sum Q (fun τ h h' => ∏ p, (S p).Th (τ p) h h')
      intro τ _
      exact hS α P F (fun p => (S p).Th (τ p)) (fun p => (hok p).2.2.2.1 (τ p))
    refine psd_congr ?_ (psd_add hA (hB (Fintype.piFinset T \ R.image ι)))
    intro h hh h' hh'
    have h1 : ∑ t ∈ R, ∏ p, (S p).Th t h h' = ∑ τ ∈ R.image ι, ∏ p, (S p).Th (τ p) h h' := by
      rw [Finset.sum_image hιinj]
      apply Finset.sum_congr rfl
      intro t _
      exact Finset.prod_congr rfl (fun p _ => (hok p).2.2.1 t (ρ p t) (hρ p t) h hh h' hh')
    have h2 : ∏ p, ∑ x ∈ T p, (S p).Th x h h' = ∑ τ ∈ Fintype.piFinset T, ∏ p, (S p).Th (τ p) h h' :=
      Finset.prod_univ_sum T (fun p x => (S p).Th x h h')
    have h3 := Finset.sum_sdiff (f := fun τ => ∏ p, (S p).Th (τ p) h h') hιmem
    rw [h1, h2, ← h3]
    ring

section schur
variable {α : Type} {F : Finset α}

/- English proof (translation)
Unfold `TB.PSDOn at *`. Conclude with `hk.hadamard hk'`.
-/
theorem psd_mul {k k' : α → α → ℂ} (hk : TB.PSDOn F k) (hk' : TB.PSDOn F k') :
    TB.PSDOn F (fun x y => k x y * k' x y) := by
  unfold TB.PSDOn at *
  exact hk.hadamard hk'

/- English proof (translation)
Unfold `TB.PSDOn`. Apply `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg` to reduce the goal to its premises. Use extensionality with `x y`. Simplify using `[Matrix.conjTranspose_apply]`. Introduce `x`.

Establish `: star x ⬝ᵥ (Matrix.of fun _ _ : F => (1 : ℂ)) *ᵥ x = star (∑ i, x i) * ∑ i, x i`. Simplify using `only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, star_sum, one_mul, Finset.sum_mul]`. Rewrite using `[this]`. Conclude with `star_mul_self_nonneg _`.
-/
theorem psd_one : TB.PSDOn F (fun _ _ : α => (1 : ℂ)) := by
  unfold TB.PSDOn
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext x y; simp [Matrix.conjTranspose_apply]
  · intro x
    have : star x ⬝ᵥ (Matrix.of fun _ _ : F => (1 : ℂ)) *ᵥ x = star (∑ i, x i) * ∑ i, x i := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, star_sum, one_mul,
        Finset.sum_mul]
    rw [this]; exact star_mul_self_nonneg _

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using psd_one`. Consider the case `insert a s ha ih`. Establish `h1` using `psd_mul (hk a (Finset.mem_insert_self a s)) (ih (fun i hi => hk i (Finset.mem_insert_of_mem hi)))`. Use `psd_congr ?_ h1` and prove the remaining obligations.

Introduce `x _ y _`. Rewrite using `[Finset.prod_insert ha]`.
-/
theorem psd_prod {P : Type} (s : Finset P) (k : P → α → α → ℂ) (hk : ∀ p ∈ s, TB.PSDOn F (k p)) :
    TB.PSDOn F (fun x y => ∏ p ∈ s, k p x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using psd_one
  | insert a s ha ih =>
    have h1 := psd_mul (hk a (Finset.mem_insert_self a s))
      (ih (fun i hi => hk i (Finset.mem_insert_of_mem hi)))
    refine psd_congr ?_ h1
    intro x _ y _
    rw [Finset.prod_insert ha]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using psd_zero`. Consider the case `insert a s ha ih`. Establish `hka` using `hk a (Finset.mem_insert_self a s)`. Establish `hda` using `hd a (Finset.mem_insert_self a s)`.

Establish `hKa : TB.PSDOn F (K a)` using `psd_congr (fun x _ y _ => by ring) (psd_add hda hka)`. Establish `h1` using `psd_mul hKa (ih (fun i hi => hk i (Finset.mem_insert_of_mem hi)) (fun i hi => hd i (Finset.mem_insert_of_mem hi)))`. Establish `h2` using `psd_mul hda (psd_prod s k (fun i hi => hk i (Finset.mem_insert_of_mem hi)))`. Use `psd_congr ?_ (psd_add h1 h2)` and prove the remaining obligations. Introduce `x _ y _`.

Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psd_prod_dom {P : Type} (s : Finset P) (k K : P → α → α → ℂ) (hk : ∀ p ∈ s, TB.PSDOn F (k p))
    (hd : ∀ p ∈ s, TB.PSDOn F (fun x y => K p x y - k p x y)) :
    TB.PSDOn F (fun x y => ∏ p ∈ s, K p x y - ∏ p ∈ s, k p x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using psd_zero
  | insert a s ha ih =>
    have hka := hk a (Finset.mem_insert_self a s)
    have hda := hd a (Finset.mem_insert_self a s)
    have hKa : TB.PSDOn F (K a) := psd_congr (fun x _ y _ => by ring) (psd_add hda hka)
    have h1 := psd_mul hKa (ih (fun i hi => hk i (Finset.mem_insert_of_mem hi))
      (fun i hi => hd i (Finset.mem_insert_of_mem hi)))
    have h2 := psd_mul hda (psd_prod s k (fun i hi => hk i (Finset.mem_insert_of_mem hi)))
    refine psd_congr ?_ (psd_add h1 h2)
    intro x _ y _
    rw [Finset.prod_insert ha, Finset.prod_insert ha]; ring
end schur

/- English proof (translation)
Introduce `α P _ F k hk`. Conclude with `psd_prod univ k (fun p _ => hk p)`.
-/
theorem t_SchurProduct : SchurProduct := by
  intro α P _ F k hk
  exact psd_prod univ k (fun p _ => hk p)

/- English proof (translation)
Introduce `α P _ F k K hk hd`. Conclude with `psd_prod_dom univ k K (fun p _ => hk p) (fun p _ => hd p)`.
-/
theorem t_ProductDomination : ProductDomination := by
  intro α P _ F k K hk hd
  exact psd_prod_dom univ k K (fun p _ => hk p) (fun p _ => hd p)

/- English proof (translation)
The claim follows from `t_ProductLemma t_SchurProduct t_ProductDomination`.
-/
theorem t_ProductLemma' : ProductLemma := t_ProductLemma t_SchurProduct t_ProductDomination

/- English proof (translation)
Introduce `α F k a hk`. Establish `h1 : TB.PSDOn F (fun x y => (a x : ℂ) * (a y : ℂ))`. Unfold `TB.PSDOn`. Apply `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg` to reduce the goal to its premises. Use extensionality with `x y`.

Simplify using `[Matrix.conjTranspose_apply, mul_comm]`. Introduce `x`. Establish `: star x ⬝ᵥ (Matrix.of fun i j : F => (a i : ℂ) * (a j : ℂ)) *ᵥ x = star (∑ i : F, (a i : ℂ) * x i) * ∑ i : F, (a i : ℂ) * x i`. Rewrite using `[star_sum, Finset.sum_mul_sum]`. Simplify using `only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `star_mul_self_nonneg _`. Conclude with `psd_mul h1 hk`.
-/
theorem t_DiagScale : DiagScale := by
  intro α F k a hk
  have h1 : TB.PSDOn F (fun x y => (a x : ℂ) * (a y : ℂ)) := by
    unfold TB.PSDOn
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext x y; simp [Matrix.conjTranspose_apply, mul_comm]
    · intro x
      have : star x ⬝ᵥ (Matrix.of fun i j : F => (a i : ℂ) * (a j : ℂ)) *ᵥ x =
          star (∑ i : F, (a i : ℂ) * x i) * ∑ i : F, (a i : ℂ) * x i := by
        rw [star_sum, Finset.sum_mul_sum]
        simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        simp; ring
      rw [this]; exact star_mul_self_nonneg _
  exact psd_mul h1 hk

end kernels

end Formalism.FourierDecayAlt.P.Jx7

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `Jx7.t_MainJoint`.
-/
theorem joint_theorem_A : Formalism.FourierDecayAlt.J.MainJoint := Jx7.t_MainJoint

/- English proof (translation)
The claim follows from `Jx7.t_MainJointForm`.
-/
theorem joint_form_theorem_A : Formalism.FourierDecayAlt.J.MainJointForm := Jx7.t_MainJointForm

/- English proof (translation)
The claim follows from `Jx7.t_MainJointInst`.
-/
theorem joint_instance_theorem_A : Formalism.FourierDecayAlt.J.MainJointInst := Jx7.t_MainJointInst

/- English proof (translation)
The claim follows from `Jx7.t_SchurProduct`.
-/
theorem schur_product : Formalism.FourierDecayAlt.J.SchurProduct := Jx7.t_SchurProduct

/- English proof (translation)
The claim follows from `Jx7.t_ProductDomination`.
-/
theorem product_domination : Formalism.FourierDecayAlt.J.ProductDomination := Jx7.t_ProductDomination

/- English proof (translation)
The claim follows from `Jx7.t_DiagScale`.
-/
theorem diagonal_scaling : Formalism.FourierDecayAlt.J.DiagScale := Jx7.t_DiagScale

/- English proof (translation)
The claim follows from `Jx7.t_ProductLemma'`.
-/
theorem product_lemma : Formalism.FourierDecayAlt.J.ProductLemma := Jx7.t_ProductLemma'

end Formalism.FourierDecayAlt.P
