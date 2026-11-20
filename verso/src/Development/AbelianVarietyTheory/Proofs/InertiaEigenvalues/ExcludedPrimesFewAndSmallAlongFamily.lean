import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.CongruenceBoundParameters
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink.ExcBound

open GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes

/- English proof (translation)
Establish `h : ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℤ) = max (⌊b⌋ + 1 - ⌈a⌉) 0`. Rewrite using `[Int.card_Icc, Int.toNat_eq_max]`. Establish `h' : (((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℤ) : ℝ) = ((max (⌊b⌋ + 1 - ⌈a⌉) 0 : ℤ) : ℝ)` using `by rw [h]`. Move the coercions through the operations in `at h'`. Rewrite using `[h']`.

Conclude with `max_le_max (by linarith [Int.floor_le b, Int.le_ceil a]) le_rfl`.
-/
theorem card_Icc_ceil_floor_le (a b : ℝ) :
    ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ) ≤ max (b - a + 1) 0 := by
  have h : ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℤ) = max (⌊b⌋ + 1 - ⌈a⌉) 0 := by
    rw [Int.card_Icc, Int.toNat_eq_max]
  have h' : (((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℤ) : ℝ) = ((max (⌊b⌋ + 1 - ⌈a⌉) 0 : ℤ) : ℝ) := by rw [h]
  push_cast at h'
  rw [h']
  exact max_le_max (by linarith [Int.floor_le b, Int.le_ceil a]) le_rfl

variable {D : D7} (L : SizeData₂ D)

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, hLa, hRho, hBot, -, -, -, -, hLs, -⟩` from `hS`. Take `⟨hL1, hL2⟩` from `hLs`. Establish `hsz : szlStar L = LevelStarExponents.lStar L` using `rfl`. Rewrite `hL1`, `hL2` using `[hsz]`. Use `set ls := LevelStarExponents.lStar L with hls_def`.

Establish `hls : 0 < ls` using `lStar_pos L`. Establish `h2ls : 2 * ls < L.sc.b` using `GlobalTheory.Survey.CongruenceBoundParameters.two_lStar_lt_b L`. Establish `hx : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hb : 0 < L.sc.b` using `Real.exp_pos _`. Establish `hη` using `L.etaSz_pos`.

Establish `hSc` using `L.Sc_pos`. Establish `hm : (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)`. Establish `hn1 : (1 : ℝ) ≤ D.R.n`. Establish `: 1 ≤ D.R.n` using `D.R.ord_pos`. Conclude with `this` after adjusting the coercions.

Establish `hX : 1 ≤ L.sc.X'` using `Real.one_le_exp (by positivity)`. Establish `hb' : 0 < L.sc.b'` using `by unfold Scale.b' Scale.a; positivity`. Establish `ht0 : (0 : ℝ) ≤ D.R.t` using `Nat.cast_nonneg _`. Establish `hbl : 0 ≤ L.sc.b / ls` using `by positivity`. Establish `h8 : 8 * L.sc.b < ls ^ 2`.

Establish `: 8 * L.sc.b / ls < ls`. Establish `: 8 * L.sc.b / ls = 8 * (L.sc.b / ls)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `this` using `[div_lt_iff₀ hls]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hsg0 : (0 : ℝ) ≤ (sgPlus L : ℝ)`. Conclude with `Int.floor_nonneg.2 (by positivity)` after adjusting the coercions. Establish `hsg1 : (sgPlus L : ℝ) ≤ 2 * L.sc.b / ls` using `Int.floor_le _`. Establish `hsg2 : 2 * L.sc.b / ls = 2 * (L.sc.b / ls)` using `by ring`. Rewrite `hsg1` using `[hsg2]`.

Establish `hL2' : 2 * L.etaSz + D.R.t + 8 * (L.sc.b / ls) + 7 < ls`. Establish `: 8 * L.sc.b / ls = 8 * (L.sc.b / ls)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hw2 : L.sc.w'' D.R.n ≤ L.sc.b`. Establish `: L.sc.w'' D.R.n = L.sc.b / (L.sc.X' * D.R.n)`.

Unfold `Scale.w'' Scale.b' Scale.a`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]; exact div_le_self hb.le (by nlinarith)`. Establish `hbT : ∀ t, (L.bT t : ℝ) ≤ L.sc.b' + L.sc.b' / 4`. Introduce `t`.

Establish `h1` using `hBot t`. Establish `hk : (0 : ℝ) ≤ D.R.k` using `Nat.cast_nonneg _`. Establish `hxe : 0 < L.sc.x ^ L.sc.eps` using `Real.rpow_pos_of_pos (by linarith) _`. Establish `hΛ : 0 ≤ L.LaG` using `le_trans hxe.le hLa.1`. Establish `hsec : 0 ≤ L.sc.x ^ szTh L * Real.log L.sc.x * L.LaG / D.R.k`.

Use `Real.log_nonneg hx.le` as an intermediate fact. Use `Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ L.sc.x) (szTh L)` as an intermediate fact. Check the signs of the components of the expression. Establish `hone : L.sc.x ^ (-2 : ℝ) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)`. Establish `hA : szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4`.

Establish `: 4 * szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k)` using `by ring`. Use `hRho` as an intermediate fact. Unfold `SizeRho at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k = (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b'` using `by ring`.

Rewrite `h1` using `[this]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hfl : ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) ≤ L.sc.b'`. Use `(Int.floor_le _).trans (div_le_self hb'.le hx.le)` and prove the remaining obligations. Establish `hW2 : ∀ W ∈ baseSizes L, W ≤ 2 * L.sc.b`.

Introduce and unpack `W (rfl | rfl | ⟨t, rfl⟩)`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Use `hbT t` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hhi : ∀ W ∈ baseSizes L, W + (L.Sc + L.etaSz + L.etaSz + 2 * (sgPlus L : ℝ) + 4) < 3 * L.sc.b`. Introduce `W hW`. Use `hW2 W hW` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Set `BS : Finset ℝ` to `{L.sc.b, L.sc.w'' D.R.n} ∪ Finset.univ.image (fun t : D.host.TT => (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ))`.

Establish `hBS : ∀ W, W ∈ BS ↔ W ∈ baseSizes L`. Introduce `W`. Simplify using `only [BS, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ, true_and, baseSizes, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `((h | h) | ⟨t, h⟩)`.

Conclude with `Or.inl h`. Conclude with `Or.inr (Or.inl h)`. Conclude with `Or.inr (Or.inr ⟨t, h.symm⟩)`. Introduce and unpack `(h | h | ⟨t, h⟩)`. Conclude with `Or.inl (Or.inl h)`.

Conclude with `Or.inl (Or.inr h)`. Conclude with `Or.inr ⟨t, h.symm⟩`. Establish `hBScard : (BS.card : ℝ) ≤ (D.host.TT.card : ℝ) + 2`. Establish `h1 : BS.card ≤ ({L.sc.b, L.sc.w'' D.R.n} : Finset ℝ).card + (Finset.univ.image (fun t : D.host.TT => (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ))).card` using `Finset.card_union_le _ _`. Establish `h2 : ({L.sc.b, L.sc.w'' D.R.n} : Finset ℝ).card ≤ 2` using `Finset.card_le_two`.

Establish `h3 : (Finset.univ.image (fun t : D.host.TT => (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ))).card ≤ D.host.TT.card`. Use `Finset.card_image_le.trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `: BS.card ≤ D.host.TT.card + 2` using `by omega`. Conclude with `this` after adjusting the coercions.

Set `lo : ℝ → ℝ` to `fun W => W + (-L.etaSz - 2 * (sgPlus L : ℝ) - 3)`. Set `hi : ℝ → ℝ` to `fun W => W + (L.Sc + L.etaSz + L.etaSz + 2 * (sgPlus L : ℝ) + 4)`. Set `win : ℝ → Finset ℤ` to `fun W => Finset.Icc ⌈lo W⌉ ⌊hi W⌋`. Establish `hwin : ∀ W n, n ∈ win W ↔ n ∈ window L W`. Introduce `W n`.

Simplify using `only [win, lo, hi, Finset.mem_Icc, Int.ceil_le, Int.le_floor, window, Set.mem_setOf_eq]`. Establish `hwincard : ∀ W, ((win W).card : ℝ) ≤ L.Sc + 3 * L.etaSz + 4 * (sgPlus L : ℝ) + 8`. Introduce `W`. Use `(card_Icc_ceil_floor_le (lo W) (hi W)).trans (max_le (le_of_eq (by simp only [lo, hi]; ring)) ?_)` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion.

Set `exc : Finset ℕ` to `BS.biUnion fun W => (win W).biUnion fun n => n.natAbs.primeFactors.filter fun l : ℕ => ls < (l : ℝ)`. Establish `hmem : ∀ l, l ∈ exc ↔ ∃ W ∈ baseSizes L, ∃ n ∈ window L W, 0 < n ∧ (n : ℝ) < 3 * L.sc.b ∧ l.Prime ∧ l ∣ n.natAbs ∧ ls < (l : ℝ)`. Introduce `l`. Simplify using `only [exc, Finset.mem_biUnion, Finset.mem_filter, Nat.mem_primeFactors]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨W, hW, n, hn, ⟨hp, hd, -⟩, hl⟩`. Rewrite `hW` using `[hBS]`. Rewrite `hn` using `[hwin]`. Conclude with `⟨W, hW, n, hn, GlobalTheory.Survey.CongruenceBoundParameters.window_pos P W hW n hn, lt_of_le_of_lt hn.2 (hhi W hW), hp, hd, hl⟩`. Introduce and unpack `⟨W, hW, n, hn, hpos, -, hp, hd, hl⟩`.

Use `⟨W, (hBS W).2 hW, n, (hwin W n).2 hn, ⟨hp, hd, by omega⟩, hl⟩` and prove the remaining obligations. Use `⟨exc, ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `l`. Simplify using `only [Finset.mem_coe, hmem, Exc, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨W, hW, n, hn, -, -, hp, hd, hl⟩`. Conclude with `⟨hp, hl, W, hW, n, hn, Int.ofNat_dvd_left.2 hd⟩`. Introduce and unpack `⟨hp, hl, W, hW, n, hn, hd⟩`. Establish `hpos` using `GlobalTheory.Survey.CongruenceBoundParameters.window_pos P W hW n hn`. Conclude with `⟨W, hW, n, hn, hpos, lt_of_le_of_lt hn.2 (hhi W hW), hp, Int.ofNat_dvd_left.1 hd, hl⟩`.

Establish `hone : ∀ W ∈ BS, ∀ n ∈ win W, (n.natAbs.primeFactors.filter fun l : ℕ => ls < (l : ℝ)).card ≤ 1`. Introduce `W hW n hn`. Rewrite `hW` using `[hBS]`. Rewrite `hn` using `[hwin]`. Establish `hpos` using `GlobalTheory.Survey.CongruenceBoundParameters.window_pos P W hW n hn`.

Establish `hup : (n : ℝ) < 3 * L.sc.b` using `lt_of_le_of_lt hn.2 (hhi W hW)`. Rewrite using `[Finset.card_le_one]`. Introduce `p hp q hq`. Simplify using `only [Finset.mem_filter, Nat.mem_primeFactors] at hp hq`. Assume the negation of the conclusion as `hpq`.

Establish `hcop : Nat.Coprime p q` using `(Nat.coprime_primes hp.1.1 hq.1.1).2 hpq`. Establish `hdvd : p * q ∣ n.natAbs` using `hcop.mul_dvd_of_dvd_of_dvd hp.1.2.1 hq.1.2.1`. Establish `hle : p * q ≤ n.natAbs` using `Nat.le_of_dvd (by omega) hdvd`. Establish `hle' : ((p * q : ℕ) : ℝ) ≤ (n : ℝ)`. Establish `: ((n.natAbs : ℤ) : ℝ) = (n : ℝ)` using `by rw [Int.natAbs_of_nonneg hpos.le]`.

Rewrite using `[← this]`. Conclude with `hle` after adjusting the coercions. Move the coercions through the operations in `at hle'`. Establish `: ls ^ 2 < (p : ℝ) * q` using `by nlinarith [hp.2, hq.2]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hc1 : exc.card ≤ ∑ W ∈ BS, ∑ n ∈ win W, (n.natAbs.primeFactors.filter fun l : ℕ => ls < (l : ℝ)).card`. Use `Finset.card_biUnion_le.trans (Finset.sum_le_sum fun W _ => Finset.card_biUnion_le)` and prove the remaining obligations. Establish `hc2 : exc.card ≤ ∑ W ∈ BS, (win W).card`. Use `hc1.trans (Finset.sum_le_sum fun W hW => ?_)` and prove the remaining obligations. Rewrite using `[Finset.card_eq_sum_ones]`.

Conclude with `Finset.sum_le_sum fun n hn => hone W hW n hn`. Establish `hc3 : (exc.card : ℝ) ≤ ∑ W ∈ BS, (L.Sc + 3 * L.etaSz + 4 * (sgPlus L : ℝ) + 8)`. Establish `: (exc.card : ℝ) ≤ ∑ W ∈ BS, ((win W).card : ℝ)` using `by exact_mod_cast hc2`. Conclude with `this.trans (Finset.sum_le_sum fun W _ => hwincard W)`. Rewrite `hc3` using `[Finset.sum_const, nsmul_eq_mul]`.

Establish `hK0 : 0 ≤ L.Sc + 3 * L.etaSz + 4 * (sgPlus L : ℝ) + 8` using `by linarith`. Establish `hK : L.Sc + 3 * L.etaSz + 4 * (sgPlus L : ℝ) + 8 ≤ L.Sc + 3 * L.etaSz + D.R.t + 8 * L.sc.b / TwistedPlaces.lStar L + 9`. Establish `: 8 * L.sc.b / TwistedPlaces.lStar L = 4 * (2 * L.sc.b / ls)` using `by show 8 * L.sc.b / LevelStarExponents.lStar L = 4 * (2 * L.sc.b / ls); ring`. Rewrite using `[this, hsg2]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `hc3.trans ?_` and prove the remaining obligations. Conclude with `mul_le_mul hBScard hK hK0 (by positivity)`. Introduce `l hl`. Take `⟨W, hW, n, hn, hpos, hup, hp, hd, -⟩` from `(hmem l).1 hl`. Establish `hle : l ≤ n.natAbs` using `Nat.le_of_dvd (by omega) hd`.

Establish `: ((n.natAbs : ℤ) : ℝ) = (n : ℝ)` using `by rw [Int.natAbs_of_nonneg hpos.le]`. Establish `hle' : (l : ℝ) ≤ (n : ℝ)` using `by rw [← this]; exact_mod_cast hle`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem excOK_at (P : ParameterChoice' D L) (hS : SizesAt L) :
    ∃ exc : Finset ℕ, (exc : Set ℕ) = Exc L ∧ ExcOK L exc := by
  obtain ⟨-, -, -, -, -, -, -, -, hLa, hRho, hBot, -, -, -, -, hLs, -⟩ := hS
  obtain ⟨hL1, hL2⟩ := hLs
  have hsz : szlStar L = LevelStarExponents.lStar L := rfl
  rw [hsz] at hL1 hL2
  set ls := LevelStarExponents.lStar L with hls_def
  have hls : 0 < ls := lStar_pos L
  have h2ls : 2 * ls < L.sc.b := GlobalTheory.Survey.CongruenceBoundParameters.two_lStar_lt_b L
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hη := L.etaSz_pos
  have hSc := L.Sc_pos
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hX : 1 ≤ L.sc.X' := Real.one_le_exp (by positivity)
  have hb' : 0 < L.sc.b' := by unfold Scale.b' Scale.a; positivity
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hbl : 0 ≤ L.sc.b / ls := by positivity

  have h8 : 8 * L.sc.b < ls ^ 2 := by
    have : 8 * L.sc.b / ls < ls := by
      have : 8 * L.sc.b / ls = 8 * (L.sc.b / ls) := by ring
      linarith
    rw [div_lt_iff₀ hls] at this; nlinarith

  have hsg0 : (0 : ℝ) ≤ (sgPlus L : ℝ) := by
    exact_mod_cast Int.floor_nonneg.2 (by positivity)
  have hsg1 : (sgPlus L : ℝ) ≤ 2 * L.sc.b / ls := Int.floor_le _
  have hsg2 : 2 * L.sc.b / ls = 2 * (L.sc.b / ls) := by ring
  rw [hsg2] at hsg1
  have hL2' : 2 * L.etaSz + D.R.t + 8 * (L.sc.b / ls) + 7 < ls := by
    have : 8 * L.sc.b / ls = 8 * (L.sc.b / ls) := by ring
    linarith

  have hw2 : L.sc.w'' D.R.n ≤ L.sc.b := by
    have : L.sc.w'' D.R.n = L.sc.b / (L.sc.X' * D.R.n) := by
      unfold Scale.w'' Scale.b' Scale.a; field_simp
    rw [this]; exact div_le_self hb.le (by nlinarith)
  have hbT : ∀ t, (L.bT t : ℝ) ≤ L.sc.b' + L.sc.b' / 4 := by
    intro t
    have h1 := hBot t
    have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have hxe : 0 < L.sc.x ^ L.sc.eps := Real.rpow_pos_of_pos (by linarith) _
    have hΛ : 0 ≤ L.LaG := le_trans hxe.le hLa.1
    have hsec : 0 ≤ L.sc.x ^ szTh L * Real.log L.sc.x * L.LaG / D.R.k := by
      have := Real.log_nonneg hx.le
      have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ L.sc.x) (szTh L)
      positivity
    have hone : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
    have hA : szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
      have : 4 * szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
          4 * (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
      have := hRho
      unfold SizeRho at this
      linarith
    have : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
        (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
    rw [this] at h1
    nlinarith
  have hfl : ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) ≤ L.sc.b' := by
    refine (Int.floor_le _).trans (div_le_self hb'.le hx.le)
  have hW2 : ∀ W ∈ baseSizes L, W ≤ 2 * L.sc.b := by
    rintro W (rfl | rfl | ⟨t, rfl⟩)
    · linarith
    · linarith
    · have := hbT t; linarith

  have hhi : ∀ W ∈ baseSizes L,
      W + (L.Sc + L.etaSz + L.etaSz + 2 * (sgPlus L : ℝ) + 4) < 3 * L.sc.b := by
    intro W hW
    have := hW2 W hW
    linarith

  let BS : Finset ℝ := {L.sc.b, L.sc.w'' D.R.n} ∪
    Finset.univ.image (fun t : D.host.TT => (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ))
  have hBS : ∀ W, W ∈ BS ↔ W ∈ baseSizes L := by
    intro W
    simp only [BS, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_univ, true_and, baseSizes, Set.mem_setOf_eq]
    constructor
    · rintro ((h | h) | ⟨t, h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨t, h.symm⟩)
    · rintro (h | h | ⟨t, h⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨t, h.symm⟩
  have hBScard : (BS.card : ℝ) ≤ (D.host.TT.card : ℝ) + 2 := by
    have h1 : BS.card ≤ ({L.sc.b, L.sc.w'' D.R.n} : Finset ℝ).card +
        (Finset.univ.image (fun t : D.host.TT => (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ))).card :=
      Finset.card_union_le _ _
    have h2 : ({L.sc.b, L.sc.w'' D.R.n} : Finset ℝ).card ≤ 2 := Finset.card_le_two
    have h3 : (Finset.univ.image (fun t : D.host.TT => (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ))).card
        ≤ D.host.TT.card := by
      refine Finset.card_image_le.trans ?_
      simp
    have : BS.card ≤ D.host.TT.card + 2 := by omega
    exact_mod_cast this

  let lo : ℝ → ℝ := fun W => W + (-L.etaSz - 2 * (sgPlus L : ℝ) - 3)
  let hi : ℝ → ℝ := fun W => W + (L.Sc + L.etaSz + L.etaSz + 2 * (sgPlus L : ℝ) + 4)
  let win : ℝ → Finset ℤ := fun W => Finset.Icc ⌈lo W⌉ ⌊hi W⌋
  have hwin : ∀ W n, n ∈ win W ↔ n ∈ window L W := by
    intro W n
    simp only [win, lo, hi, Finset.mem_Icc, Int.ceil_le, Int.le_floor, window, Set.mem_setOf_eq]
  have hwincard : ∀ W, ((win W).card : ℝ) ≤ L.Sc + 3 * L.etaSz + 4 * (sgPlus L : ℝ) + 8 := by
    intro W
    refine (card_Icc_ceil_floor_le (lo W) (hi W)).trans (max_le (le_of_eq (by simp only [lo, hi]; ring)) ?_)
    linarith

  let exc : Finset ℕ := BS.biUnion fun W => (win W).biUnion fun n =>
    n.natAbs.primeFactors.filter fun l : ℕ => ls < (l : ℝ)
  have hmem : ∀ l, l ∈ exc ↔ ∃ W ∈ baseSizes L, ∃ n ∈ window L W,
      0 < n ∧ (n : ℝ) < 3 * L.sc.b ∧ l.Prime ∧ l ∣ n.natAbs ∧ ls < (l : ℝ) := by
    intro l
    simp only [exc, Finset.mem_biUnion, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨W, hW, n, hn, ⟨hp, hd, -⟩, hl⟩
      rw [hBS] at hW; rw [hwin] at hn
      exact ⟨W, hW, n, hn, GlobalTheory.Survey.CongruenceBoundParameters.window_pos P W hW n hn,
        lt_of_le_of_lt hn.2 (hhi W hW), hp, hd, hl⟩
    · rintro ⟨W, hW, n, hn, hpos, -, hp, hd, hl⟩
      refine ⟨W, (hBS W).2 hW, n, (hwin W n).2 hn, ⟨hp, hd, by omega⟩, hl⟩
  refine ⟨exc, ?_, ?_, ?_⟩
  · ext l
    simp only [Finset.mem_coe, hmem, Exc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨W, hW, n, hn, -, -, hp, hd, hl⟩
      exact ⟨hp, hl, W, hW, n, hn, Int.ofNat_dvd_left.2 hd⟩
    · rintro ⟨hp, hl, W, hW, n, hn, hd⟩
      have hpos := GlobalTheory.Survey.CongruenceBoundParameters.window_pos P W hW n hn
      exact ⟨W, hW, n, hn, hpos, lt_of_le_of_lt hn.2 (hhi W hW), hp, Int.ofNat_dvd_left.1 hd, hl⟩
  ·
    have hone : ∀ W ∈ BS, ∀ n ∈ win W,
        (n.natAbs.primeFactors.filter fun l : ℕ => ls < (l : ℝ)).card ≤ 1 := by
      intro W hW n hn
      rw [hBS] at hW; rw [hwin] at hn
      have hpos := GlobalTheory.Survey.CongruenceBoundParameters.window_pos P W hW n hn
      have hup : (n : ℝ) < 3 * L.sc.b := lt_of_le_of_lt hn.2 (hhi W hW)
      rw [Finset.card_le_one]
      intro p hp q hq
      simp only [Finset.mem_filter, Nat.mem_primeFactors] at hp hq
      by_contra hpq
      have hcop : Nat.Coprime p q := (Nat.coprime_primes hp.1.1 hq.1.1).2 hpq
      have hdvd : p * q ∣ n.natAbs := hcop.mul_dvd_of_dvd_of_dvd hp.1.2.1 hq.1.2.1
      have hle : p * q ≤ n.natAbs := Nat.le_of_dvd (by omega) hdvd
      have hle' : ((p * q : ℕ) : ℝ) ≤ (n : ℝ) := by
        have : ((n.natAbs : ℤ) : ℝ) = (n : ℝ) := by rw [Int.natAbs_of_nonneg hpos.le]
        rw [← this]; exact_mod_cast hle
      push_cast at hle'
      have : ls ^ 2 < (p : ℝ) * q := by nlinarith [hp.2, hq.2]
      linarith
    have hc1 : exc.card ≤ ∑ W ∈ BS, ∑ n ∈ win W,
        (n.natAbs.primeFactors.filter fun l : ℕ => ls < (l : ℝ)).card := by
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun W _ => Finset.card_biUnion_le)
    have hc2 : exc.card ≤ ∑ W ∈ BS, (win W).card := by
      refine hc1.trans (Finset.sum_le_sum fun W hW => ?_)
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun n hn => hone W hW n hn
    have hc3 : (exc.card : ℝ) ≤ ∑ W ∈ BS, (L.Sc + 3 * L.etaSz + 4 * (sgPlus L : ℝ) + 8) := by
      have : (exc.card : ℝ) ≤ ∑ W ∈ BS, ((win W).card : ℝ) := by exact_mod_cast hc2
      exact this.trans (Finset.sum_le_sum fun W _ => hwincard W)
    rw [Finset.sum_const, nsmul_eq_mul] at hc3
    have hK0 : 0 ≤ L.Sc + 3 * L.etaSz + 4 * (sgPlus L : ℝ) + 8 := by linarith
    have hK : L.Sc + 3 * L.etaSz + 4 * (sgPlus L : ℝ) + 8 ≤
        L.Sc + 3 * L.etaSz + D.R.t + 8 * L.sc.b / TwistedPlaces.lStar L + 9 := by
      have : 8 * L.sc.b / TwistedPlaces.lStar L = 4 * (2 * L.sc.b / ls) := by
        show 8 * L.sc.b / LevelStarExponents.lStar L = 4 * (2 * L.sc.b / ls); ring
      rw [this, hsg2]; linarith
    refine hc3.trans ?_
    exact mul_le_mul hBScard hK hK0 (by positivity)
  · intro l hl
    obtain ⟨W, hW, n, hn, hpos, hup, hp, hd, -⟩ := (hmem l).1 hl
    have hle : l ≤ n.natAbs := Nat.le_of_dvd (by omega) hd
    have : ((n.natAbs : ℤ) : ℝ) = (n : ℝ) := by rw [Int.natAbs_of_nonneg hpos.le]
    have hle' : (l : ℝ) ≤ (n : ℝ) := by rw [← this]; exact_mod_cast hle
    linarith

end GlobalTheory.NLink.ExcBound

namespace GlobalTheory.NLink

/- English proof (translation)
Introduce `eps Fm`. Conclude with `⟨Fm.x1, fun x _ hx i => ExcBound.excOK_at (Fm.L x i) (Fm.params x hx i) (Fm.sizes x hx i)⟩`.
-/
theorem excOK_family : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x,
    ∃ exc : Finset ℕ, (exc : Set ℕ) = GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc (Fm.L x i) ∧ ExcOK (Fm.L x i) exc := by
  intro eps Fm
  exact ⟨Fm.x1, fun x _ hx i => ExcBound.excOK_at (Fm.L x i) (Fm.params x hx i) (Fm.sizes x hx i)⟩

end GlobalTheory.NLink

end
