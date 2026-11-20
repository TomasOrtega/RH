import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.NoMonMultideg

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

section Up

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

/- English proof (translation)
Rewrite using `[show monomial (mPl Fr p hk nL bp) c = C c * monomial (mPl Fr p hk nL bp) 1 by`. Rewrite using `[C_mul_monomial, mul_one]]`. Simplify using `only [upPl, aeval_monomial, algebraMap_eq]`. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mPl, MvPolynomial.monomial_sum_one]`. Use `congr 1`.

Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `v _`. Rewrite using `[← pow_mul, X_pow_eq_monomial]`.
-/
theorem upPl_monomial (bp : TL J nL r × Fin r →₀ ℕ) (c : KK O) :
    upPl Fr p O hk nL (monomial bp c) = monomial (mPl Fr p hk nL bp) c := by
  rw [show monomial (mPl Fr p hk nL bp) c = C c * monomial (mPl Fr p hk nL bp) 1 by
      rw [C_mul_monomial, mul_one]]
  simp only [upPl, aeval_monomial, algebraMap_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mPl, MvPolynomial.monomial_sum_one]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  rw [← pow_mul, X_pow_eq_monomial]

/- English proof (translation)
Rewrite using `[show monomial (mNo Fr p hk nL bn) c = C c * monomial (mNo Fr p hk nL bn) 1 by`. Rewrite using `[C_mul_monomial, mul_one]]`. Simplify using `only [upNo, aeval_monomial, algebraMap_eq]`. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mNo, MvPolynomial.monomial_sum_one]`. Use `congr 1`.

Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `v _`. Rewrite using `[← pow_mul, X_pow_eq_monomial]`.
-/
theorem upNo_monomial (bn : TL J nL r × Fin K →₀ ℕ) (c : KK O) :
    upNo Fr p O hk nL (monomial bn c) = monomial (mNo Fr p hk nL bn) c := by
  rw [show monomial (mNo Fr p hk nL bn) c = C c * monomial (mNo Fr p hk nL bn) 1 by
      rw [C_mul_monomial, mul_one]]
  simp only [upNo, aeval_monomial, algebraMap_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mNo, MvPolynomial.monomial_sum_one]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  rw [← pow_mul, X_pow_eq_monomial]

/- English proof (translation)
Use `conv_lhs => rw [asm, A.as_sum, N.as_sum]`. Simplify using `only [map_sum, upPl_monomial, upNo_monomial, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `bp _`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `bn _`. Rewrite using `[monomial_mul, monomial_mul, one_mul, bigM_eq]`.
-/
theorem asm_eq_sum (rho : TL J nL r × Fin (r + K) → ℕ) (A : MvPolynomial (TL J nL r × Fin r) (KK O))
    (N : MvPolynomial (TL J nL r × Fin K) (KK O)) :
    asm Fr p O hk nL rho A N = ∑ bp ∈ A.support, ∑ bn ∈ N.support,
      monomial (bigM Fr p hk nL rho bp bn) (A.coeff bp * N.coeff bn) := by
  conv_lhs => rw [asm, A.as_sum, N.as_sum]
  simp only [map_sum, upPl_monomial, upNo_monomial, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro bp _
  apply Finset.sum_congr rfl
  intro bn _
  rw [monomial_mul, monomial_mul, one_mul, bigM_eq]

/- English proof (translation)
Simplify using `only [levImg, MvPolynomial.coeff_sum, coeff_monomial]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `mo _`. Apply the tactic sequence `by_cases h1 : plMon Fr p hk nL mo = bp <;> by_cases h2 : noMon Fr p hk nL mo = bn <;> simp [h1, h2]`.
-/
theorem levImg_coeff (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (G : MvPolynomial (TV n' (m + 1)) (KK O)) (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) :
    ((levImg Fr p hk nL rho dPl dNo G).coeff bp).coeff bn =
      ∑ mo ∈ G.support.filter (fun mo => InLow Fr p hk nL rho mo ∧ InBlock Fr p hk nL dPl dNo mo),
        if plMon Fr p hk nL mo = bp ∧ noMon Fr p hk nL mo = bn then G.coeff mo else 0 := by
  simp only [levImg, MvPolynomial.coeff_sum, coeff_monomial]
  apply Finset.sum_congr rfl
  intro mo _
  by_cases h1 : plMon Fr p hk nL mo = bp <;> by_cases h2 : noMon Fr p hk nL mo = bn <;> simp [h1, h2]

variable {Fr p O hk nL}

/- English proof (translation)
Establish `hpl` using `bigM_plMon (hk := hk) hp hinj rho hrho bp bn`. Establish `hno` using `bigM_noMon (hk := hk) hp hinj rho hrho bp bn`. Rewrite using `[levImg_coeff]`. Use `(Finset.sum_eq_single (bigM Fr p hk nL rho bp bn) ?_ ?_).trans ?_` and prove the remaining obligations. Introduce `mo hmo hne`.

Rewrite using `[if_neg]`. Introduce and unpack `⟨e1, e2⟩`. Apply `hne` to reduce the goal to its premises. Take `⟨hmo1, hlow, -⟩` from `Finset.mem_filter.mp hmo`. Rewrite using `[eq_bigM hinj rho mo (hz mo hmo1) hlow, e1, e2]`.

Introduce `hnot`. Rewrite using `[if_pos ⟨hpl, hno⟩]`. Assume the negation of the conclusion as `hc`. Conclude with `hnot (Finset.mem_filter.mpr ⟨mem_support_iff.mpr hc, bigM_inLow (hk := hk) hinj rho hrho bp bn, bigM_inBlock (hk := hk) hp hinj rho hrho bp bn dPl dNo h1 h2⟩)`. Rewrite using `[if_pos ⟨hpl, hno⟩]`.
-/
theorem levImg_coeff_bigM (hp : 0 < p) (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (G : MvPolynomial (TV n' (m + 1)) (KK O))
    (hz : ∀ mo ∈ G.support, ∀ w, w ∉ Set.range (tvar Fr hk nL) → mo w = 0)
    (rho : TL J nL r × Fin (r + K) → ℕ) (hrho : ∀ x c, rho (x, c) < lowP Fr p x) (dPl dNo : TL J nL r → ℕ)
    (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ)
    (h1 : ∀ x, multideg bp x = dPl x) (h2 : ∀ x, multideg bn x = dNo x) :
    ((levImg Fr p hk nL rho dPl dNo G).coeff bp).coeff bn = G.coeff (bigM Fr p hk nL rho bp bn) := by
  have hpl := bigM_plMon (hk := hk) hp hinj rho hrho bp bn
  have hno := bigM_noMon (hk := hk) hp hinj rho hrho bp bn
  rw [levImg_coeff]
  refine (Finset.sum_eq_single (bigM Fr p hk nL rho bp bn) ?_ ?_).trans ?_
  · intro mo hmo hne
    rw [if_neg]
    rintro ⟨e1, e2⟩
    apply hne
    obtain ⟨hmo1, hlow, -⟩ := Finset.mem_filter.mp hmo
    rw [eq_bigM hinj rho mo (hz mo hmo1) hlow, e1, e2]
  · intro hnot
    rw [if_pos ⟨hpl, hno⟩]
    by_contra hc
    exact hnot (Finset.mem_filter.mpr ⟨mem_support_iff.mpr hc, bigM_inLow (hk := hk) hinj rho hrho bp bn,
      bigM_inBlock (hk := hk) hp hinj rho hrho bp bn dPl dNo h1 h2⟩)
  · rw [if_pos ⟨hpl, hno⟩]

end Up

section Fact

/- English proof (translation)
Unfold `expFact`. Conclude with `Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero)`.
-/
theorem expFact_fintype {σ : Type} [Fintype σ] (b : σ →₀ ℕ) : expFact b = ∏ v, (b v).factorial := by
  unfold expFact
  exact Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero)

/- English proof (translation)
Rewrite using `[gamR, div_mul_cancel₀]`. Check the signs of the components of the expression.
-/
theorem gamR_spec (P rho be : ℕ) :
    ((rho + P * be).factorial : ℚ) =
      gamR P rho be * ((rho.factorial : ℚ) * (be.factorial : ℚ) * (P.factorial : ℚ) ^ be) := by
  rw [gamR, div_mul_cancel₀]
  positivity

variable {n' r K m : ℕ} [NeZero n'] {Fr : Frames n' r} {p : ℕ} {hk : m + 1 = r + K} {J : ℕ} [NeZero J]
  {nL : ZMod J → ℕ}

/- English proof (translation)
Unfold `expFact bigM`. Rewrite using `[Finsupp.prod_mapDomain_index_inj (tvar_inj (hk := hk) hinj), Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero)]`. Simplify using the standard rewrite rules.
-/
theorem expFact_bigM (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) :
    expFact (bigM Fr p hk nL rho bp bn) = ∏ v, (bigE Fr p nL rho bp bn v).factorial := by
  unfold expFact bigM
  rw [Finsupp.prod_mapDomain_index_inj (tvar_inj (hk := hk) hinj),
    Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero)]
  simp

/- English proof (translation)
Simplify using `only [Fintype.prod_prod_type, Fin.prod_univ_add, Finset.prod_mul_distrib]`.
-/
private theorem sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul {M : Type} [CommMonoid M] (f : TL J nL r × Fin (r + K) → M) :
    ∏ v, f v = (∏ v : TL J nL r × Fin r, f (v.1, Fin.castAdd K v.2)) *
      ∏ v : TL J nL r × Fin K, f (v.1, Fin.natAdd r v.2) := by
  simp only [Fintype.prod_prod_type, Fin.prod_univ_add, Finset.prod_mul_distrib]

/- English proof (translation)
Rewrite using `[expFact_bigM (hk := hk) hinj rho bp bn]`. Use `push_cast`. Unfold `bigE`. Rewrite using `[Finset.prod_congr rfl (fun v _ => gamR_spec (lowP Fr p v.1) (rho v) (joinE nL bp bn v))]`. Simplify using `only [Finset.prod_mul_distrib]`.

Rewrite using `[sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul (fun v => gamR (lowP Fr p v.1) (rho v) (joinE nL bp bn v)), sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul (fun v => ((joinE nL bp bn v).factorial : ℚ)), sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul (fun v => ((lowP Fr p v.1).factorial : ℚ …`. Simplify using `only [joinE, Fin.addCases_left, Fin.addCases_right, Prod.mk.eta]`. Rewrite using `[cstOf, expFact_fintype, expFact_fintype, gamPl, gamNo]`. Use `push_cast`. Establish `hP : ∏ x : TL J nL r, ((lowP Fr p x).factorial : ℚ) ^ (dPl x + dNo x) = (∏ v : TL J nL r × Fin r, ((lowP Fr p v.1).factorial : ℚ) ^ bp v) * ∏ v : TL J nL r × Fin K, ((lowP Fr p v.1).factorial : ℚ) ^ bn v`.

Rewrite using `[Fintype.prod_prod_type, Fintype.prod_prod_type, ← Finset.prod_mul_distrib]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `x _`. Simplify using `only`. Rewrite using `[Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, ← pow_add, ← h1 x, ← h2 x]`.

Both sides reduce to the same expression. Rewrite using `[hP]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem expFact_bigM_Q (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ)
    (h1 : ∀ x, multideg bp x = dPl x) (h2 : ∀ x, multideg bn x = dNo x) :
    ((expFact (bigM Fr p hk nL rho bp bn) : ℕ) : ℚ) = ((cstOf Fr p nL rho dPl dNo : ℕ) : ℚ) *
      ((expFact bp : ℕ) : ℚ) * ((expFact bn : ℕ) : ℚ) * gamPl Fr p nL rho bp * gamNo Fr p nL rho bn := by
  rw [expFact_bigM (hk := hk) hinj rho bp bn]
  push_cast
  unfold bigE
  rw [Finset.prod_congr rfl (fun v _ => gamR_spec (lowP Fr p v.1) (rho v) (joinE nL bp bn v))]
  simp only [Finset.prod_mul_distrib]
  rw [sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul (fun v => gamR (lowP Fr p v.1) (rho v) (joinE nL bp bn v)),
    sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul (fun v => ((joinE nL bp bn v).factorial : ℚ)),
    sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul (fun v => ((lowP Fr p v.1).factorial : ℚ) ^ (joinE nL bp bn v))]
  simp only [joinE, Fin.addCases_left, Fin.addCases_right, Prod.mk.eta]
  rw [cstOf, expFact_fintype, expFact_fintype, gamPl, gamNo]
  push_cast
  have hP : ∏ x : TL J nL r, ((lowP Fr p x).factorial : ℚ) ^ (dPl x + dNo x) =
      (∏ v : TL J nL r × Fin r, ((lowP Fr p v.1).factorial : ℚ) ^ bp v) *
        ∏ v : TL J nL r × Fin K, ((lowP Fr p v.1).factorial : ℚ) ^ bn v := by
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro x _
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, ← pow_add, ← h1 x, ← h2 x]
    rfl
  rw [hP]
  ring

end Fact

section Main

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

/- English proof (translation)
Simplify using `[classOf, Fin.addCases_left]`.
-/
theorem classOf_left (mo : TV n' (m + 1) →₀ ℕ) (x : TL J nL r) (a : Fin r) :
    classOf Fr p hk nL mo (x, Fin.castAdd K a) = mo (plVar Fr hk nL x a) % lowP Fr p x := by
  simp [classOf, Fin.addCases_left]

/- English proof (translation)
Simplify using `[classOf, Fin.addCases_right]`.
-/
theorem classOf_right (mo : TV n' (m + 1) →₀ ℕ) (x : TL J nL r) (b : Fin K) :
    classOf Fr p hk nL mo (x, Fin.natAdd r b) = mo (noVar Fr hk nL x b) % lowP Fr p x := by
  simp [classOf, Fin.addCases_right]

/- English proof (translation)
Unfold `multideg`. Rewrite using `[← Equiv.sum_comp (finCongr hk.symm) (fun c => mo (posOf n' (posTL Fr x), c)), Fin.sum_univ_add]`. Both sides reduce to the same expression.
-/
theorem sum_coords (mo : TV n' (m + 1) →₀ ℕ) (x : TL J nL r) :
    multideg mo (posOf n' (posTL Fr x)) =
      ∑ a : Fin r, mo (plVar Fr hk nL x a) + ∑ b : Fin K, mo (noVar Fr hk nL x b) := by
  unfold multideg
  rw [← Equiv.sum_comp (finCongr hk.symm) (fun c => mo (posOf n' (posTL Fr x), c)), Fin.sum_univ_add]
  rfl

/- English proof (translation)
Introduce `G hG`. Establish `hdeg : ∀ mo ∈ G.support, ∀ s, multideg mo s = d s` using `fun mo hmo => (MvPolynomial.mem_restrictSupport_iff (KK O)).1 hG hmo`. Establish `hz : ∀ mo ∈ G.support, ∀ w, w ∉ Set.range (tvar Fr hk nL) → mo w = 0`. Introduce and unpack `mo hmo ⟨s, c⟩ hw`. Distinguish the cases in `hs : s ∈ Fr.TT`.

Take `⟨x, hx⟩` from `hsurj s hs`. Conclude with `absurd ⟨(x, Fin.cast hk c), by simp [tvar, hx]⟩ hw`. Establish `h1` using `hdeg mo hmo s`. Rewrite `h1` using `[hd s hs]`. Conclude with `(Finset.sum_eq_zero_iff.1 h1) c (Finset.mem_univ _)`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `rho dPl dNo hrho A hA N hN`. Rewrite using `[asm_eq_sum, fockR_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun bp hbp => ?_` and prove the remaining obligations. Rewrite using `[fockR_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun bn hbn => ?_` and prove the remaining obligations. Establish `h1 : ∀ x, multideg bp x = dPl x` using `(MvPolynomial.mem_restrictSupport_iff (KK O)).1 hA hbp`. Establish `h2 : ∀ x, multideg bn x = dNo x` using `(MvPolynomial.mem_restrictSupport_iff (KK O)).1 hN hbn`. Rewrite using `[fockR_monomial, levImg_coeff_bigM hp hinj G hz rho hrho dPl dNo bp bn h1 h2]`. Establish `hc` using `congrArg (fun q : ℚ => (q : KK O)) (expFact_bigM_Q (p := p) (hk := hk) hinj rho dPl dNo bp bn h1 h2)`.

Simplify using `only [Rat.cast_mul, Rat.cast_natCast] at hc`. Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree. Introduce `rho dPl dNo bp`. Unfold `levImg`.

Rewrite using `[coeff_sum]`. Use `Submodule.sum_mem _ fun mo hmo => ?_` and prove the remaining obligations. Rewrite using `[coeff_monomial]`. Use `split_ifs`. Unfold `Pol`.

Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `b hb`. Establish `hb'` using `MvPolynomial.support_monomial_subset hb`. Rewrite `hb'` using `[Finset.mem_singleton]`. Substitute `hb'` using the available equality.

Introduce `x`. Conclude with `(Finset.mem_filter.1 hmo).2.2.2 x`. Conclude with `Submodule.zero_mem _`. Introduce `mo hmo`. Establish `hlow : InLow Fr p hk nL (classOf Fr p hk nL mo) mo` using `⟨fun x a => (classOf_left Fr p hk nL mo x a).symm, fun x b => (classOf_right Fr p hk nL mo x b).symm⟩`.

Establish `hrho : ∀ x c, classOf Fr p hk nL mo (x, c) < lowP Fr p x`. Introduce `x c`. Use `Fin.addCases (fun a => ?_) (fun b => ?_) c` and prove the remaining obligations. Rewrite using `[classOf_left]`. Conclude with `Nat.mod_lt _ (lowP_pos hp x)`.

Rewrite using `[classOf_right]`. Conclude with `Nat.mod_lt _ (lowP_pos hp x)`. Establish `heq` using `eq_bigM hinj (classOf Fr p hk nL mo) mo (hz mo hmo) hlow`. Use `⟨⟨hrho, fun x => ?_⟩, ?_, fun x => rfl, fun x => rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[← hdeg mo hmo, sum_coords Fr hk nL mo x, Fin.sum_univ_add]`.

Simplify using `only [classOf_left, classOf_right]`. Unfold `blkPl blkNo`. Rewrite using `[mul_add, Finset.mul_sum, Finset.mul_sum]`. Establish `e1 : ∑ a : Fin r, mo (plVar Fr hk nL x a) = ∑ a : Fin r, (mo (plVar Fr hk nL x a) % lowP Fr p x + lowP Fr p x * (mo (plVar Fr hk nL x a) / lowP Fr p x))` using `Finset.sum_congr rfl fun a _ => (Nat.mod_add_div _ _).symm`. Establish `e2 : ∑ b : Fin K, mo (noVar Fr hk nL x b) = ∑ b : Fin K, (mo (noVar Fr hk nL x b) % lowP Fr p x + lowP Fr p x * (mo (noVar Fr hk nL x b) / lowP Fr p x))` using `Finset.sum_congr rfl fun b _ => (Nat.mod_add_div _ _).symm`.

Rewrite using `[e1, e2, Finset.sum_add_distrib, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree. Establish `h` using `levImg_coeff_bigM hp hinj G hz (classOf Fr p hk nL mo) hrho (blkPl Fr p hk nL mo) (blkNo Fr p hk nL mo) (plMon Fr p hk nL mo) (noMon Fr p hk nL mo) (fun x => rfl) (fun x => rfl)`. Rewrite `h` using `[← heq]`. Conclude with `h`.

Establish `h` using `expFact_bigM_Q (p := p) (hk := hk) hinj (classOf Fr p hk nL mo) (blkPl Fr p hk nL mo) (blkNo Fr p hk nL mo) (plMon Fr p hk nL mo) (noMon Fr p hk nL mo) (fun x => rfl) (fun x => rfl)`. Rewrite `h` using `[← heq]`. Conclude with `h`.
-/
theorem digFacts_of [CharZero (KK O)] (hp : 0 < p)
    (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (hsurj : ∀ s ∈ Fr.TT, ∃ x : TL J nL r, posOf n' (posTL Fr x) = s)
    (d : Fin n' → ℕ) (hd : ∀ s, s ∉ Fr.TT → d s = 0) : DigFacts Fr p O hk nL d := by
  intro G hG
  have hdeg : ∀ mo ∈ G.support, ∀ s, multideg mo s = d s := fun mo hmo =>
    (MvPolynomial.mem_restrictSupport_iff (KK O)).1 hG hmo
  have hz : ∀ mo ∈ G.support, ∀ w, w ∉ Set.range (tvar Fr hk nL) → mo w = 0 := by
    rintro mo hmo ⟨s, c⟩ hw
    by_cases hs : s ∈ Fr.TT
    · obtain ⟨x, hx⟩ := hsurj s hs
      exact absurd ⟨(x, Fin.cast hk c), by simp [tvar, hx]⟩ hw
    · have h1 := hdeg mo hmo s
      rw [hd s hs] at h1
      exact (Finset.sum_eq_zero_iff.1 h1) c (Finset.mem_univ _)
  refine ⟨?_, ?_, ?_⟩
  · intro rho dPl dNo hrho A hA N hN
    rw [asm_eq_sum, fockR_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun bp hbp => ?_
    rw [fockR_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun bn hbn => ?_
    have h1 : ∀ x, multideg bp x = dPl x := (MvPolynomial.mem_restrictSupport_iff (KK O)).1 hA hbp
    have h2 : ∀ x, multideg bn x = dNo x := (MvPolynomial.mem_restrictSupport_iff (KK O)).1 hN hbn
    rw [fockR_monomial, levImg_coeff_bigM hp hinj G hz rho hrho dPl dNo bp bn h1 h2]
    have hc := congrArg (fun q : ℚ => (q : KK O)) (expFact_bigM_Q (p := p) (hk := hk) hinj rho dPl dNo bp bn h1 h2)
    simp only [Rat.cast_mul, Rat.cast_natCast] at hc
    rw [hc]
    ring
  · intro rho dPl dNo bp
    unfold levImg
    rw [coeff_sum]
    refine Submodule.sum_mem _ fun mo hmo => ?_
    rw [coeff_monomial]
    split_ifs
    · unfold Pol
      rw [MvPolynomial.mem_restrictSupport_iff]
      intro b hb
      have hb' := MvPolynomial.support_monomial_subset hb
      rw [Finset.mem_singleton] at hb'
      subst hb'
      intro x
      exact (Finset.mem_filter.1 hmo).2.2.2 x
    · exact Submodule.zero_mem _
  · intro mo hmo
    have hlow : InLow Fr p hk nL (classOf Fr p hk nL mo) mo :=
      ⟨fun x a => (classOf_left Fr p hk nL mo x a).symm, fun x b => (classOf_right Fr p hk nL mo x b).symm⟩
    have hrho : ∀ x c, classOf Fr p hk nL mo (x, c) < lowP Fr p x := by
      intro x c
      refine Fin.addCases (fun a => ?_) (fun b => ?_) c
      · rw [classOf_left]; exact Nat.mod_lt _ (lowP_pos hp x)
      · rw [classOf_right]; exact Nat.mod_lt _ (lowP_pos hp x)
    have heq := eq_bigM hinj (classOf Fr p hk nL mo) mo (hz mo hmo) hlow
    refine ⟨⟨hrho, fun x => ?_⟩, ?_, fun x => rfl, fun x => rfl, ?_⟩
    · rw [← hdeg mo hmo, sum_coords Fr hk nL mo x, Fin.sum_univ_add]
      simp only [classOf_left, classOf_right]
      unfold blkPl blkNo
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      have e1 : ∑ a : Fin r, mo (plVar Fr hk nL x a) =
          ∑ a : Fin r, (mo (plVar Fr hk nL x a) % lowP Fr p x + lowP Fr p x * (mo (plVar Fr hk nL x a) / lowP Fr p x)) :=
        Finset.sum_congr rfl fun a _ => (Nat.mod_add_div _ _).symm
      have e2 : ∑ b : Fin K, mo (noVar Fr hk nL x b) =
          ∑ b : Fin K, (mo (noVar Fr hk nL x b) % lowP Fr p x + lowP Fr p x * (mo (noVar Fr hk nL x b) / lowP Fr p x)) :=
        Finset.sum_congr rfl fun b _ => (Nat.mod_add_div _ _).symm
      rw [e1, e2, Finset.sum_add_distrib, Finset.sum_add_distrib]
      ring
    · have h := levImg_coeff_bigM hp hinj G hz (classOf Fr p hk nL mo) hrho (blkPl Fr p hk nL mo) (blkNo Fr p hk nL mo)
        (plMon Fr p hk nL mo) (noMon Fr p hk nL mo) (fun x => rfl) (fun x => rfl)
      rw [← heq] at h
      exact h
    · have h := expFact_bigM_Q (p := p) (hk := hk) hinj (classOf Fr p hk nL mo) (blkPl Fr p hk nL mo) (blkNo Fr p hk nL mo)
        (plMon Fr p hk nL mo) (noMon Fr p hk nL mo) (fun x => rfl) (fun x => rfl)
      rw [← heq] at h
      exact h

end Main

end Formalism.MainNotions.Proposition5Numerics
