import Formalism.HermitianCurvature.HermitianCurvatureProofs.Lam1

namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

section pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

/- English proof (translation)
Unfold `PBL.stdS`. Establish `e : h ++ [(s - 1, t), (1, c)] = (h ++ [(s - 1, t)]) ++ [(1, c)]` using `by simp`. Rewrite using `[e, PBL.toStd_append_blkT, PBL.toStd_append_blkT]`. Establish `hsz2 : D.ptSize (h ++ [(s - 1, t)]) = S.G.r`. Rewrite using `[PBJ.Asm.ptSize_append, PBJ.Asm.ptSize_single]`.

Use linear arithmetic over natural numbers and integers. Establish `n1 : S6.nuBlock (S.G.r : ℤ) ((1 + D.ptSize h : ℕ) : ℤ) ((s - 1 : ℕ) : ℤ) = (s : ℤ)`. Unfold `S6.nuBlock; push_cast [Nat.cast_sub (by omega : 1 ≤ s)]; omega`. Establish `n2 : S6.nuBlock (S.G.r : ℤ) ((1 + D.ptSize (h ++ [(s - 1, t)]) : ℕ) : ℤ) ((1 : ℕ) : ℤ) = 0`. Rewrite using `[hsz2]`.

Unfold `S6.nuBlock`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[n1, n2]`. Simplify using `only [List.append_assoc, List.singleton_append, zpow_zero, Complex.ofReal_one, one_mul, Nat.sub_self, pow_zero, zpow_natCast, lam1]`.

Use `congr 3`.
-/
theorem std_Px (S : C.HidaSetting E Wp Wq) (s : ℕ) (hs : 2 ≤ s) (h : C.LPt) (hsz : D.ptSize h + s = S.G.r + 1)
    (t c : ℂ) : PBL.stdS S (h ++ [(s - 1, t), (1, c)]) = PBL.stdS S h ++ [(s - 1, lam1 S s * t), (1, c)] := by
  unfold PBL.stdS
  have e : h ++ [(s - 1, t), (1, c)] = (h ++ [(s - 1, t)]) ++ [(1, c)] := by simp
  rw [e, PBL.toStd_append_blkT, PBL.toStd_append_blkT]
  have hsz2 : D.ptSize (h ++ [(s - 1, t)]) = S.G.r := by
    rw [PBJ.Asm.ptSize_append, PBJ.Asm.ptSize_single]; omega
  have n1 : S6.nuBlock (S.G.r : ℤ) ((1 + D.ptSize h : ℕ) : ℤ) ((s - 1 : ℕ) : ℤ) = (s : ℤ) := by
    unfold S6.nuBlock; push_cast [Nat.cast_sub (by omega : 1 ≤ s)]; omega
  have n2 : S6.nuBlock (S.G.r : ℤ) ((1 + D.ptSize (h ++ [(s - 1, t)]) : ℕ) : ℤ) ((1 : ℕ) : ℤ) = 0 := by
    rw [hsz2]; unfold S6.nuBlock; push_cast; ring
  rw [n1, n2]
  simp only [List.append_assoc, List.singleton_append, zpow_zero, Complex.ofReal_one, one_mul, Nat.sub_self,
    pow_zero, zpow_natCast, lam1]
  congr 3

/- English proof (translation)
Unfold `PBL.stdS`. Rewrite using `[PBL.toStd_append_blkT]`. Establish `n1 : S6.nuBlock (S.G.r : ℤ) ((1 + D.ptSize h : ℕ) : ℤ) (s : ℤ) = ((s - 1 : ℕ) : ℤ)`. Unfold `S6.nuBlock; push_cast [Nat.cast_sub (by omega : 1 ≤ s)]; omega`. Rewrite using `[n1, zpow_natCast]`.

Simplify using `only [lam2]`.
-/
theorem std_Qz (S : C.HidaSetting E Wp Wq) (s : ℕ) (hs : 2 ≤ s) (h : C.LPt) (hsz : D.ptSize h + s = S.G.r + 1)
    (z : ℂ) : PBL.stdS S (h ++ [(s, z)]) = PBL.stdS S h ++ [(s, lam2 S s * z)] := by
  unfold PBL.stdS
  rw [PBL.toStd_append_blkT]
  have n1 : S6.nuBlock (S.G.r : ℤ) ((1 + D.ptSize h : ℕ) : ℤ) (s : ℤ) = ((s - 1 : ℕ) : ℤ) := by
    unfold S6.nuBlock; push_cast [Nat.cast_sub (by omega : 1 ≤ s)]; omega
  rw [n1, zpow_natCast]
  simp only [lam2]

section copied

/- English proof (translation)
The claim follows from `| b, [], Q => by simp [C.nAux, D.ptSize] | b, (s, t) :: rest, Q => by simp only [List.cons_append, C.nAux] rw [weight_product_append k r GG fr (b + s) rest Q, ← mul_assoc] have e : b + D.ptSize ((s, t) :: rest) = b + s + D.ptSize rest := by simp only [D.ptSize, List.map_cons, Lis …`.
-/
theorem weight_product_append (k r : ℕ) (GG : ℝ) (fr : ℕ → ℕ → ℝ) :
    ∀ (b : ℕ) (P Q : C.LPt), C.nAux k r GG fr b (P ++ Q) = C.nAux k r GG fr b P * C.nAux k r GG fr (b + D.ptSize P) Q
  | b, [], Q => by simp [C.nAux, D.ptSize]
  | b, (s, t) :: rest, Q => by
    simp only [List.cons_append, C.nAux]
    rw [weight_product_append k r GG fr (b + s) rest Q, ← mul_assoc]
    have e : b + D.ptSize ((s, t) :: rest) = b + s + D.ptSize rest := by
      simp only [D.ptSize, List.map_cons, List.sum_cons]; ring
    rw [e]

/- English proof (translation)
The claim follows from `| b, [], _ => by simp [C.nAux] | b, (s, t) :: rest, h => by simp only [C.nAux] have hs : D.ptSize ((s, t) :: rest) = s + D.ptSize rest := by simp [D.ptSize] rw [hs] at h have hc : ¬ (b + s - 1 = r + 1 ∧ s = 1) := by omega rw [if_neg hc, if_neg hc, weight_product_germ_indep k r GG …`.
-/
theorem weight_product_germ_indep (k r : ℕ) (GG GG' : ℝ) (fr : ℕ → ℕ → ℝ) :
    ∀ (b : ℕ) (P : C.LPt), b + D.ptSize P ≤ r + 1 → C.nAux k r GG fr b P = C.nAux k r GG' fr b P
  | b, [], _ => by simp [C.nAux]
  | b, (s, t) :: rest, h => by
    simp only [C.nAux]
    have hs : D.ptSize ((s, t) :: rest) = s + D.ptSize rest := by simp [D.ptSize]
    rw [hs] at h
    have hc : ¬ (b + s - 1 = r + 1 ∧ s = 1) := by omega
    rw [if_neg hc, if_neg hc, weight_product_germ_indep k r GG GG' fr (b + s) rest (by omega)]

/- English proof (translation)
Simplify using `[D.bSt, List.map_append, List.prod_append]`.
-/
theorem bSt_append (κ : ℝ) (P Q : C.LPt) : D.bSt κ (P ++ Q) = D.bSt κ P * D.bSt κ Q := by
  simp [D.bSt, List.map_append, List.prod_append]

def betaZ (κ : ℝ) (N : ℤ) : ℝ := ∏ x ∈ Finset.Ico 1 N, (κ ^ (1 - 2 * x) / Real.pi) ^ (N - x)

/- English proof (translation)
Simplify using `[D.bSt, betaZ]`.
-/
theorem bSt_cons (κ : ℝ) (n : ℕ) (t : ℂ) (P : C.LPt) : D.bSt κ ((n, t) :: P) = betaZ κ n * D.bSt κ P := by
  simp [D.bSt, betaZ]

/- English proof (translation)
Simplify using `[D.bSt]`.
-/
theorem bSt_nil (κ : ℝ) : D.bSt κ [] = 1 := by simp [D.bSt]

/- English proof (translation)
Simplify using `[betaZ]`.
-/
theorem betaZ_one (κ : ℝ) : betaZ κ 1 = 1 := by simp [betaZ]

/- English proof (translation)
Rewrite using `[Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_insert_right h, Finset.prod_insert (by simp), mul_comm]`.
-/
theorem prod_Ico_int_succ (f : ℤ → ℝ) (a b : ℤ) (h : a ≤ b) :
    ∏ x ∈ Finset.Ico a (b + 1), f x = (∏ x ∈ Finset.Ico a b, f x) * f b := by
  rw [Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_insert_right h, Finset.prod_insert (by simp), mul_comm]

/- English proof (translation)
Unfold `betaZ`. Establish `hc : ∀ x : ℤ, κ ^ (1 - 2 * x) / Real.pi ≠ 0` using `fun x => div_ne_zero (zpow_ne_zero _ hκ) Real.pi_ne_zero`. Establish `e : ∏ x ∈ Finset.Ico 1 ((n : ℤ) + 1), (κ ^ (1 - 2 * x) / Real.pi) ^ ((n : ℤ) + 1 - x) = ∏ x ∈ Finset.Ico 1 ((n : ℤ) + 1), ((κ ^ (1 - 2 * x) / Real.pi) ^ ((n : ℤ) - x) * (κ ^ (1 - 2 * x) / Real.pi))`. Use `Finset.prod_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_add_one₀ (hc x)]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Finset.prod_mul_distrib]`. Use `congr 1`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases.

Simplify using the standard rewrite rules. Rewrite using `[prod_Ico_int_succ _ _ _ (by omega), sub_self, zpow_zero, mul_one]`.
-/
theorem betaZ_succ (κ : ℝ) (hκ : κ ≠ 0) (n : ℕ) :
    betaZ κ ((n : ℤ) + 1) = betaZ κ n * ∏ x ∈ Finset.Ico 1 ((n : ℤ) + 1), (κ ^ (1 - 2 * x) / Real.pi) := by
  unfold betaZ
  have hc : ∀ x : ℤ, κ ^ (1 - 2 * x) / Real.pi ≠ 0 := fun x => div_ne_zero (zpow_ne_zero _ hκ) Real.pi_ne_zero
  have e : ∏ x ∈ Finset.Ico 1 ((n : ℤ) + 1), (κ ^ (1 - 2 * x) / Real.pi) ^ ((n : ℤ) + 1 - x) =
      ∏ x ∈ Finset.Ico 1 ((n : ℤ) + 1), ((κ ^ (1 - 2 * x) / Real.pi) ^ ((n : ℤ) - x) * (κ ^ (1 - 2 * x) / Real.pi)) := by
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [← zpow_add_one₀ (hc x)]; congr 1; ring
  rw [e, Finset.prod_mul_distrib]
  congr 1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [prod_Ico_int_succ _ _ _ (by omega), sub_self, zpow_zero, mul_one]

/- English proof (translation)
The claim follows from `| 0 => by simp | n + 1 => by rw [show ((n + 1 : ℕ) : ℤ) + 1 = ((n : ℤ) + 1) + 1 by push_cast; ring, prod_Ico_int_succ _ _ _ (by omega), prod_c κ hκ n, div_mul_div_comm, ← zpow_add₀ hκ, pow_succ] congr 2 push_cast; ring`.
-/
theorem prod_c (κ : ℝ) (hκ : κ ≠ 0) : ∀ n : ℕ,
    ∏ x ∈ Finset.Ico 1 ((n : ℤ) + 1), (κ ^ (1 - 2 * x) / Real.pi) = κ ^ (-((n : ℤ) ^ 2)) / Real.pi ^ n
  | 0 => by simp
  | n + 1 => by
    rw [show ((n + 1 : ℕ) : ℤ) + 1 = ((n : ℤ) + 1) + 1 by push_cast; ring, prod_Ico_int_succ _ _ _ (by omega),
      prod_c κ hκ n, div_mul_div_comm, ← zpow_add₀ hκ, pow_succ]
    congr 2
    push_cast; ring

/- English proof (translation)
Rewrite using `[betaZ_succ κ hκ, prod_c κ hκ]`.
-/
theorem betaZ_succ' (κ : ℝ) (hκ : κ ≠ 0) (n : ℕ) :
    betaZ κ ((n : ℤ) + 1) = betaZ κ n * (κ ^ (-((n : ℤ) ^ 2)) / Real.pi ^ n) := by
  rw [betaZ_succ κ hκ, prod_c κ hκ]

/- English proof (translation)
The claim follows from `| _, [] => by simp [C.nAux] | b, (s, t) :: rest => by simp only [C.nAux] refine mul_nonneg ?_ (weight_product_nonneg k r fr hfr (b + s) rest) split_ifs · rcases Nat.eq_zero_or_pos (k - 1) with h | h · rw [h]; simp · rw [zero_pow h.ne'] · exact zpow_nonneg (mul_nonneg (hfr _ _) (n …`.
-/
theorem weight_product_nonneg (k r : ℕ) (fr : ℕ → ℕ → ℝ) (hfr : ∀ b s, 0 ≤ fr b s) :
    ∀ (b : ℕ) (P : C.LPt), 0 ≤ C.nAux k r 0 fr b P
  | _, [] => by simp [C.nAux]
  | b, (s, t) :: rest => by
    simp only [C.nAux]
    refine mul_nonneg ?_ (weight_product_nonneg k r fr hfr (b + s) rest)
    split_ifs
    · rcases Nat.eq_zero_or_pos (k - 1) with h | h
      · rw [h]; simp
      · rw [zero_pow h.ne']
    · exact zpow_nonneg (mul_nonneg (hfr _ _) (norm_nonneg _)) _

/- English proof (translation)
The claim follows from `Finset.prod_pos fun _ _ => zpow_pos (div_pos (zpow_pos hκ _) Real.pi_pos) _`.
-/
theorem betaZ_pos (κ : ℝ) (hκ : 0 < κ) (N : ℤ) : 0 < betaZ κ N :=
  Finset.prod_pos fun _ _ => zpow_pos (div_pos (zpow_pos hκ _) Real.pi_pos) _

end copied

/- English proof (translation)
Rewrite using `[Real.sqrt_div' _ hdG.le, Real.sqrt_one]`. Simplify using `only [mul_pow, inv_pow, ← pow_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem A_alg (u R Gm dG βn qB nh bh GGs Dn : ℝ) (hu : 0 < u) (hR : 0 < R) (hGm : 0 < Gm) (hdG : 0 < dG)
    (hβ : 0 < βn) (hq : 0 < qB) (hbh : 0 < bh) (hD : 0 < Dn) (n j : ℕ) :
    u ^ n * (√(1 / dG))⁻¹ * (√nh * ((R ^ (n + 1))⁻¹ * u⁻¹) ^ (n * ((j + 1) + n)) * GGs / (bh * βn)) * qB⁻¹ =
      (√nh / bh * (√dG * ((R ^ (n + 1))⁻¹) ^ (n * ((j + 1) + n)) * βn⁻¹ * qB⁻¹ / (Gm ^ ((n + 1) * n ^ 2)))) *
        Dn ^ j * (Gm ^ (n + 1) * u⁻¹) ^ (n ^ 2) * (GGs / (u ^ n * Dn) ^ j) := by
  rw [Real.sqrt_div' _ hdG.le, Real.sqrt_one]
  simp only [mul_pow, inv_pow, ← pow_mul]
  field_simp
  ring

/- English proof (translation)
Establish `hκ' : κ = (R * Gm)⁻¹` using `by field_simp; linarith`. Substitute `hκ'` using the available equality. Rewrite using `[Real.sqrt_div' _ hdG.le, show R ^ (2 * n) = (R ^ n) ^ 2 by ring, Real.sqrt_sq (by positivity)]`. Rewrite using `[show (j + 1) + n - 1 = j + n by omega]`. Simplify using `only [mul_pow, inv_pow, ← pow_mul, inv_inv]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem B_alg (u R Gm dG βn qL nh bh sR κ π' : ℝ) (hu : 0 < u) (hR : 0 < R) (hGm : 0 < Gm) (hdG : 0 < dG)
    (hβ : 0 < βn) (hbh : 0 < bh) (hs : 0 < sR) (n j : ℕ) (hκ : κ * R * Gm = 1) (hπ : 0 < π')
    (hqL : 0 < qL) :
    (sR * u ^ n)⁻¹ * (√(R ^ (2 * n) / dG))⁻¹ *
        (√nh * ((R ^ n)⁻¹ * u) ^ ((n + 1) * ((j + 1) + n - 1)) / (bh * (βn * (κ ^ (n ^ 2))⁻¹ / π' ^ n))) * qL⁻¹ =
      (√nh / bh * (√dG * ((R ^ (n + 1))⁻¹) ^ (n * ((j + 1) + n)) * βn⁻¹ * (π'⁻¹ ^ n * qL)⁻¹ / (Gm ^ ((n + 1) * n ^ 2)))) *
        (u ^ (n + 1)) ^ j * (sR⁻¹ * (Gm ^ n * u) ^ (n ^ 2)) := by
  have hκ' : κ = (R * Gm)⁻¹ := by field_simp; linarith
  subst hκ'
  rw [Real.sqrt_div' _ hdG.le, show R ^ (2 * n) = (R ^ n) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [show (j + 1) + n - 1 = j + n by omega]
  simp only [mul_pow, inv_pow, ← pow_mul, inv_inv]
  field_simp
  ring

/- English proof (translation)
Unfold `qU`. Establish `h1 : ‖U.betaU‖ = 2`. Simplify using `[U.betaU, Formalism.QuantumDeterminants.cStd]`. Rewrite using `[h1, Real.coe_toNNReal _ (by positivity)]`. Clear the denominators using the available nonvanishing facts.
-/
theorem qU_eq : qU = Real.pi⁻¹ := by
  unfold qU
  have h1 : ‖U.betaU‖ = 2 := by
    simp [U.betaU, Formalism.QuantumDeterminants.cStd]
  rw [h1, Real.coe_toNNReal _ (by positivity)]
  field_simp

/- English proof (translation)
Rewrite using `[pow_mul', Real.sqrt_sq (pow_nonneg hy _)]`.
-/
theorem sqrt_pow_two_mul (y : ℝ) (hy : 0 ≤ y) (m : ℕ) : √(y ^ (2 * m)) = y ^ m := by
  rw [pow_mul', Real.sqrt_sq (pow_nonneg hy _)]

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, s = n + 1` from `⟨s - 1, by omega⟩`. Take `⟨j, hj⟩ : ∃ j, S.G.k = j + 1` from `⟨S.G.k - 1, by omega⟩`. Establish `hn1 : n + 1 - 1 = n` using `by omega`. Simplify using `only [hn1]`. Rewrite using `[show S.G.k - 1 = j by omega]`.

Use `set R := S6.rd E with hRdef`. Establish `hR : 0 < R` using `PBD.rd_pos' E`. Use `set gg : ℝ := (S.g : ℝ) with hgg`. Establish `hgg0 : 0 < gg` using `by rw [hgg]; exact_mod_cast hg`. Use `set Gm : ℝ := gg / (2 * Real.pi) with hGm`.

Establish `hGm0 : 0 < Gm` using `by positivity`. Use `set κ := D.kapG gg R with hκdef`. Establish `hκ0 : 0 < κ` using `by rw [hκdef]; unfold D.kapG; positivity`. Establish `hκ : κ * R * Gm = 1`. Rewrite using `[hκdef, hGm]`.

Unfold `D.kapG`. Clear the denominators using the available nonvanishing facts. Use `set dG := D.deG gg R with hdG`. Establish `hdG0 : 0 < dG` using `by rw [hdG]; unfold D.deG; positivity`. Establish `hfr : ∀ b s, 0 ≤ S.fr b s` using `fun b s => by unfold C.HidaSetting.fr; exact Real.rpow_nonneg hR.le _`.

Use `set nh := C.nAux S.G.k S.G.r 0 S.fr 1 h with hnh`. Establish `hnh0 : 0 ≤ nh` using `weight_product_nonneg _ _ _ hfr _ _`. Use `set bh := D.bSt κ h with hbh`. Establish `hbh0 : 0 < bh` using `PBD.bSt_pos' κ hκ0 h`. Use `set βn := betaZ κ (n : ℤ) with hβn`.

Establish `hβ0 : 0 < βn` using `betaZ_pos κ hκ0 _`. Establish `hq0 : 0 < qU` using `by rw [qU_eq]; positivity`. Use `set Kc := √dG * ((R ^ (n + 1))⁻¹) ^ (n * ((j + 1) + n)) * βn⁻¹ * (qU ^ (n + (Fintype.card (G.UT n) + n)))⁻¹ / (Gm ^ ((n + 1) * n ^ 2)) with hKc`. Use `⟨√nh / bh * Kc, ?_, ?_⟩` and prove the remaining obligations. Introduce `x Dd hx hD`.

Establish `hb0 : D.ptSize h + n = S.G.r` using `by omega`. Establish `hdl1 : KB.dlB S (S.G.r + 1) 1 = 1 / dG`. Establish `e : 2 * S6.nuBlock (S.G.r : ℤ) ((S.G.r + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) = 0`. Unfold `S6.nuBlock`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Unfold `KB.dlB`. Rewrite using `[e, zpow_zero]`. Establish `hfrA : S.fr (1 + D.ptSize h) n = (R ^ (n + 1))⁻¹`. Unfold `C.HidaSetting.fr`.

Establish `e : ((S6.nuBlock (S.G.r : ℤ) ((1 + D.ptSize h : ℕ) : ℤ) (n : ℤ) : ℤ) : ℝ) = ((n + 1 : ℕ) : ℝ)`. Unfold `S6.nuBlock`. Use `push_cast`. Establish `: ((D.ptSize h : ℕ) : ℝ) + n = S.G.r` using `by exact_mod_cast hb0`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[e, Real.rpow_neg hR.le, Real.rpow_natCast]`. Establish `hM : C.Mlev S.G.k S.G.r (1 + D.ptSize h + n - 1) = (S.G.k : ℤ) + 3`. Unfold `C.Mlev`. Rewrite using `[show 1 + D.ptSize h + n - 1 = S.G.r by omega]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hexp : 2 * ((n : ℕ) : ℤ) * (C.Mlev S.G.k S.G.r (1 + D.ptSize h + n - 1) + ((n : ℕ) : ℤ) - 3) = ((2 * (n * ((j + 1) + n)) : ℕ) : ℤ)`. Rewrite using `[hM, hj]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hGG : D.ptGG (S.T * S.T') (h ++ [(n, x⁻¹), (1, x ^ n * Dd)]) = Complex.normSq (x ^ n * Dd) - S.T * S.T'`.

Unfold `D.ptGG D.ptLast`. Simplify using the standard rewrite rules. Establish `hnnA : PBL.nnS S (h ++ [(n, x⁻¹), (1, x ^ n * Dd)]) = nh * (((R ^ (n + 1))⁻¹ * ‖x⁻¹‖) ^ (2 * (n * ((j + 1) + n))) * ((Complex.normSq (x ^ n * Dd) - S.T * S.T') ^ j * 1))`. Unfold `PBL.nnS C.nLoc`. Rewrite using `[hGG, weight_product_append, weight_product_germ_indep S.G.k S.G.r _ 0 S.fr 1 h (by omega)]`.

Simplify using `only [C.nAux]`. Apply the tactic sequence `split_ifs with H1 H2 <;> first | (exfalso; omega) | (exfalso; simp only [and_true] at *; omega) | skip`. Rewrite using `[hfrA, hexp, zpow_natCast, show S.G.k - 1 = j by omega]`. Establish `hbA : PBL.bS S (h ++ [(n, x⁻¹), (1, x ^ n * Dd)]) = bh * βn`. Unfold `PBL.bS`.

Rewrite using `[bSt_append, bSt_cons, bSt_cons, bSt_nil, Nat.cast_one, betaZ_one, mul_one, mul_one]`. Establish `hsq : √(PBL.nnS S (h ++ [(n, x⁻¹), (1, x ^ n * Dd)])) = √nh * ((R ^ (n + 1))⁻¹ * ‖x‖⁻¹) ^ (n * ((j + 1) + n)) * √((Complex.normSq (x ^ n * Dd) - S.T * S.T') ^ j)`. Rewrite using `[hnnA, mul_one, ← mul_assoc, Real.sqrt_mul (mul_nonneg hnh0 (pow_nonneg (by positivity) _)), Real.sqrt_mul hnh0, sqrt_pow_two_mul _ (by positivity), norm_inv]`. Establish `hl1 : ‖lam1 S (n + 1) * x⁻¹‖ = Gm ^ (n + 1) * ‖x‖⁻¹`. Unfold `lam1`.

Rewrite using `[norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), norm_inv]`. Establish `hcn : ‖x ^ n * Dd‖ = ‖x‖ ^ n * ‖Dd‖` using `by rw [norm_mul, norm_pow]`. Rewrite using `[hdl1, hsq, hbA, hl1, hcn]`. Conclude with `A_alg ‖x‖ R Gm dG βn (qU ^ (n + (Fintype.card (G.UT n) + n))) nh bh _ ‖Dd‖ (norm_pos_iff.2 hx) hR hGm0 hdG0 hβ0 (by positivity) hbh0 (norm_pos_iff.2 hD) n j`. Introduce `z hz`.

Establish `hb0 : D.ptSize h + n = S.G.r` using `by omega`. Establish `hdl2 : KB.dlB S b (n + 1) = R ^ (2 * n) / dG`. Establish `e : 2 * S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((n + 1 : ℕ) : ℤ) = ((2 * n : ℕ) : ℤ)`. Unfold `S6.nuBlock`. Use `push_cast`.

Use linear arithmetic over natural numbers and integers. Unfold `KB.dlB`. Rewrite using `[e, zpow_natCast]`. Establish `hfrB : S.fr (1 + D.ptSize h) (n + 1) = (R ^ n)⁻¹`. Unfold `C.HidaSetting.fr`.

Establish `e : ((S6.nuBlock (S.G.r : ℤ) ((1 + D.ptSize h : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ) : ℤ) : ℝ) = ((n : ℕ) : ℝ)`. Unfold `S6.nuBlock`. Use `push_cast`. Establish `: ((D.ptSize h : ℕ) : ℝ) + n = S.G.r` using `by exact_mod_cast hb0`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[e, Real.rpow_neg hR.le, Real.rpow_natCast]`. Establish `hMB : C.Mlev S.G.k S.G.r (1 + D.ptSize h + (n + 1) - 1) = (S.G.k : ℤ) + 1`. Unfold `C.Mlev`. Rewrite using `[show 1 + D.ptSize h + (n + 1) - 1 = S.G.r + 1 by omega]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hexpB : 2 * ((n + 1 : ℕ) : ℤ) * (C.Mlev S.G.k S.G.r (1 + D.ptSize h + (n + 1) - 1) + ((n + 1 : ℕ) : ℤ) - 3) = ((2 * ((n + 1) * ((j + 1) + n - 1)) : ℕ) : ℤ)`. Rewrite using `[hMB, hj, show j + 1 + n - 1 = j + n by omega]; push_cast; ring`. Establish `hnnB : PBL.nnS S (h ++ [(n + 1, z)]) = nh * (((R ^ n)⁻¹ * ‖z‖) ^ (2 * ((n + 1) * ((j + 1) + n - 1))) * 1)`. Unfold `PBL.nnS C.nLoc`.

Rewrite using `[weight_product_append, weight_product_germ_indep S.G.k S.G.r _ 0 S.fr 1 h (by omega)]`. Simplify using `only [C.nAux]`. Apply the tactic sequence `split_ifs with H1 <;> first | (exfalso; omega) | skip`. Rewrite using `[hfrB, hexpB, zpow_natCast]`. Establish `hsqB : √(PBL.nnS S (h ++ [(n + 1, z)])) = √nh * ((R ^ n)⁻¹ * ‖z‖) ^ ((n + 1) * ((j + 1) + n - 1))`.

Rewrite using `[hnnB, mul_one, Real.sqrt_mul hnh0, sqrt_pow_two_mul _ (by positivity)]`. Establish `hbB : PBL.bS S (h ++ [(n + 1, z)]) = bh * (βn * (κ ^ (n ^ 2))⁻¹ / Real.pi ^ n)`. Unfold `PBL.bS`. Rewrite using `[bSt_append, bSt_cons, bSt_nil, mul_one, Nat.cast_add, Nat.cast_one, betaZ_succ' κ hκ0.ne' n, show (-((n : ℤ) ^ 2)) = -((n ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hl2 : ‖lam2 S (n + 1) * z‖ = Gm ^ n * ‖z‖`. Unfold `lam2`. Rewrite using `[norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), hn1]`. Establish `hzs : ‖z ^ (n + 1)‖ = ‖z‖ ^ (n + 1)` using `norm_pow _ _`. Establish `hcard : Fintype.card (G.UT (n + 1)) = Fintype.card (G.UT n) + n`.

Rewrite using `[StandardCharacterExists.card_UT, StandardCharacterExists.card_UT, Finset.sum_range_succ]`. Establish `hqB : qU ^ (n + (Fintype.card (G.UT n) + n)) = Real.pi⁻¹ ^ n * qU ^ Fintype.card (G.UT (n + 1))`. Rewrite using `[hcard, pow_add, qU_eq]`. Rewrite using `[hdl2, hsqB, hbB, hl2, hzs, hKc, hqB]`. Conclude with `B_alg ‖z‖ R Gm dG βn (qU ^ Fintype.card (G.UT (n + 1))) nh bh ((n + 1 : ℕ) : ℝ) κ Real.pi (norm_pos_iff.2 hz) hR hGm0 hdG0 hβ0 hbh0 (by positivity) n j hκ Real.pi_pos (by positivity)`.
-/
theorem const_match (S : C.HidaSetting E Wp Wq) (hg : 0 < S.g) (b s : ℕ) (hb : 1 ≤ b) (hs : 2 ≤ s)
    (hbs : b + s = S.G.r + 2) (hk : 1 ≤ S.G.k) (h : C.LPt) (hsz : D.ptSize h = b - 1) :
    ∃ Kh : ℝ,
      (∀ x D : ℂ, x ≠ 0 → D ≠ 0 →
        ‖x‖ ^ (s - 1) * (√(KB.dlB S (S.G.r + 1) 1))⁻¹ *
            (√(PBL.nnS S (h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)])) /
              PBL.bS S (h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)])) *
            (qU ^ ((s - 1) + (Fintype.card (G.UT (s - 1)) + (s - 1))))⁻¹ =
          Kh * ‖D‖ ^ (S.G.k - 1) * ‖lam1 S s * x⁻¹‖ ^ ((s - 1) ^ 2) *
            (√((Complex.normSq (x ^ (s - 1) * D) - S.T * S.T') ^ (S.G.k - 1)) /
              ‖x ^ (s - 1) * D‖ ^ (S.G.k - 1))) ∧
      (∀ z : ℂ, z ≠ 0 →
        ((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ * (√(KB.dlB S b s))⁻¹ *
            (√(PBL.nnS S (h ++ [(s, z)])) / PBL.bS S (h ++ [(s, z)])) * (qU ^ Fintype.card (G.UT s))⁻¹ =
          Kh * ‖z ^ s‖ ^ (S.G.k - 1) * ((s : ℝ)⁻¹ * ‖lam2 S s * z‖ ^ ((s - 1) ^ 2))) := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, S.G.k = j + 1 := ⟨S.G.k - 1, by omega⟩
  have hn1 : n + 1 - 1 = n := by omega
  simp only [hn1]
  rw [show S.G.k - 1 = j by omega]
  set R := S6.rd E with hRdef
  have hR : 0 < R := PBD.rd_pos' E
  set gg : ℝ := (S.g : ℝ) with hgg
  have hgg0 : 0 < gg := by rw [hgg]; exact_mod_cast hg
  set Gm : ℝ := gg / (2 * Real.pi) with hGm
  have hGm0 : 0 < Gm := by positivity
  set κ := D.kapG gg R with hκdef
  have hκ0 : 0 < κ := by rw [hκdef]; unfold D.kapG; positivity
  have hκ : κ * R * Gm = 1 := by
    rw [hκdef, hGm]; unfold D.kapG; field_simp
  set dG := D.deG gg R with hdG
  have hdG0 : 0 < dG := by rw [hdG]; unfold D.deG; positivity
  have hfr : ∀ b s, 0 ≤ S.fr b s := fun b s => by unfold C.HidaSetting.fr; exact Real.rpow_nonneg hR.le _
  set nh := C.nAux S.G.k S.G.r 0 S.fr 1 h with hnh
  have hnh0 : 0 ≤ nh := weight_product_nonneg _ _ _ hfr _ _
  set bh := D.bSt κ h with hbh
  have hbh0 : 0 < bh := PBD.bSt_pos' κ hκ0 h
  set βn := betaZ κ (n : ℤ) with hβn
  have hβ0 : 0 < βn := betaZ_pos κ hκ0 _
  have hq0 : 0 < qU := by rw [qU_eq]; positivity
  set Kc := √dG * ((R ^ (n + 1))⁻¹) ^ (n * ((j + 1) + n)) * βn⁻¹ * (qU ^ (n + (Fintype.card (G.UT n) + n)))⁻¹ /
    (Gm ^ ((n + 1) * n ^ 2)) with hKc
  refine ⟨√nh / bh * Kc, ?_, ?_⟩
  · intro x Dd hx hD
    have hb0 : D.ptSize h + n = S.G.r := by omega
    have hdl1 : KB.dlB S (S.G.r + 1) 1 = 1 / dG := by
      have e : 2 * S6.nuBlock (S.G.r : ℤ) ((S.G.r + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) = 0 := by
        unfold S6.nuBlock; push_cast; ring
      unfold KB.dlB
      rw [e, zpow_zero]
    have hfrA : S.fr (1 + D.ptSize h) n = (R ^ (n + 1))⁻¹ := by
      unfold C.HidaSetting.fr
      have e : ((S6.nuBlock (S.G.r : ℤ) ((1 + D.ptSize h : ℕ) : ℤ) (n : ℤ) : ℤ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by
        unfold S6.nuBlock; push_cast
        have : ((D.ptSize h : ℕ) : ℝ) + n = S.G.r := by exact_mod_cast hb0
        linarith
      rw [e, Real.rpow_neg hR.le, Real.rpow_natCast]
    have hM : C.Mlev S.G.k S.G.r (1 + D.ptSize h + n - 1) = (S.G.k : ℤ) + 3 := by
      unfold C.Mlev
      rw [show 1 + D.ptSize h + n - 1 = S.G.r by omega]
      ring
    have hexp : 2 * ((n : ℕ) : ℤ) * (C.Mlev S.G.k S.G.r (1 + D.ptSize h + n - 1) + ((n : ℕ) : ℤ) - 3) =
        ((2 * (n * ((j + 1) + n)) : ℕ) : ℤ) := by
      rw [hM, hj]; push_cast; ring
    have hGG : D.ptGG (S.T * S.T') (h ++ [(n, x⁻¹), (1, x ^ n * Dd)]) = Complex.normSq (x ^ n * Dd) - S.T * S.T' := by
      unfold D.ptGG D.ptLast
      simp
    have hnnA : PBL.nnS S (h ++ [(n, x⁻¹), (1, x ^ n * Dd)]) =
        nh * (((R ^ (n + 1))⁻¹ * ‖x⁻¹‖) ^ (2 * (n * ((j + 1) + n))) *
          ((Complex.normSq (x ^ n * Dd) - S.T * S.T') ^ j * 1)) := by
      unfold PBL.nnS C.nLoc
      rw [hGG, weight_product_append, weight_product_germ_indep S.G.k S.G.r _ 0 S.fr 1 h (by omega)]
      simp only [C.nAux]
      split_ifs with H1 H2 <;> first | (exfalso; omega) | (exfalso; simp only [and_true] at *; omega) | skip
      rw [hfrA, hexp, zpow_natCast, show S.G.k - 1 = j by omega]
    have hbA : PBL.bS S (h ++ [(n, x⁻¹), (1, x ^ n * Dd)]) = bh * βn := by
      unfold PBL.bS
      rw [bSt_append, bSt_cons, bSt_cons, bSt_nil, Nat.cast_one, betaZ_one, mul_one, mul_one]
    have hsq : √(PBL.nnS S (h ++ [(n, x⁻¹), (1, x ^ n * Dd)])) =
        √nh * ((R ^ (n + 1))⁻¹ * ‖x‖⁻¹) ^ (n * ((j + 1) + n)) * √((Complex.normSq (x ^ n * Dd) - S.T * S.T') ^ j) := by
      rw [hnnA, mul_one, ← mul_assoc, Real.sqrt_mul (mul_nonneg hnh0 (pow_nonneg (by positivity) _)),
        Real.sqrt_mul hnh0, sqrt_pow_two_mul _ (by positivity), norm_inv]
    have hl1 : ‖lam1 S (n + 1) * x⁻¹‖ = Gm ^ (n + 1) * ‖x‖⁻¹ := by
      unfold lam1
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity), norm_inv]
    have hcn : ‖x ^ n * Dd‖ = ‖x‖ ^ n * ‖Dd‖ := by rw [norm_mul, norm_pow]
    rw [hdl1, hsq, hbA, hl1, hcn]
    exact A_alg ‖x‖ R Gm dG βn (qU ^ (n + (Fintype.card (G.UT n) + n))) nh bh _ ‖Dd‖ (norm_pos_iff.2 hx) hR hGm0
      hdG0 hβ0 (by positivity) hbh0 (norm_pos_iff.2 hD) n j
  · intro z hz
    have hb0 : D.ptSize h + n = S.G.r := by omega
    have hdl2 : KB.dlB S b (n + 1) = R ^ (2 * n) / dG := by
      have e : 2 * S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((n + 1 : ℕ) : ℤ) = ((2 * n : ℕ) : ℤ) := by
        unfold S6.nuBlock; push_cast; omega
      unfold KB.dlB
      rw [e, zpow_natCast]
    have hfrB : S.fr (1 + D.ptSize h) (n + 1) = (R ^ n)⁻¹ := by
      unfold C.HidaSetting.fr
      have e : ((S6.nuBlock (S.G.r : ℤ) ((1 + D.ptSize h : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ) : ℤ) : ℝ) = ((n : ℕ) : ℝ) := by
        unfold S6.nuBlock; push_cast
        have : ((D.ptSize h : ℕ) : ℝ) + n = S.G.r := by exact_mod_cast hb0
        linarith
      rw [e, Real.rpow_neg hR.le, Real.rpow_natCast]
    have hMB : C.Mlev S.G.k S.G.r (1 + D.ptSize h + (n + 1) - 1) = (S.G.k : ℤ) + 1 := by
      unfold C.Mlev
      rw [show 1 + D.ptSize h + (n + 1) - 1 = S.G.r + 1 by omega]
      push_cast; ring
    have hexpB : 2 * ((n + 1 : ℕ) : ℤ) * (C.Mlev S.G.k S.G.r (1 + D.ptSize h + (n + 1) - 1) + ((n + 1 : ℕ) : ℤ) - 3) =
        ((2 * ((n + 1) * ((j + 1) + n - 1)) : ℕ) : ℤ) := by
      rw [hMB, hj, show j + 1 + n - 1 = j + n by omega]; push_cast; ring
    have hnnB : PBL.nnS S (h ++ [(n + 1, z)]) = nh * (((R ^ n)⁻¹ * ‖z‖) ^ (2 * ((n + 1) * ((j + 1) + n - 1))) * 1) := by
      unfold PBL.nnS C.nLoc
      rw [weight_product_append, weight_product_germ_indep S.G.k S.G.r _ 0 S.fr 1 h (by omega)]
      simp only [C.nAux]
      split_ifs with H1 <;> first | (exfalso; omega) | skip
      rw [hfrB, hexpB, zpow_natCast]
    have hsqB : √(PBL.nnS S (h ++ [(n + 1, z)])) = √nh * ((R ^ n)⁻¹ * ‖z‖) ^ ((n + 1) * ((j + 1) + n - 1)) := by
      rw [hnnB, mul_one, Real.sqrt_mul hnh0, sqrt_pow_two_mul _ (by positivity)]
    have hbB : PBL.bS S (h ++ [(n + 1, z)]) = bh * (βn * (κ ^ (n ^ 2))⁻¹ / Real.pi ^ n) := by
      unfold PBL.bS
      rw [bSt_append, bSt_cons, bSt_nil, mul_one, Nat.cast_add, Nat.cast_one, betaZ_succ' κ hκ0.ne' n,
        show (-((n : ℤ) ^ 2)) = -((n ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
      ring
    have hl2 : ‖lam2 S (n + 1) * z‖ = Gm ^ n * ‖z‖ := by
      unfold lam2
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity), hn1]
    have hzs : ‖z ^ (n + 1)‖ = ‖z‖ ^ (n + 1) := norm_pow _ _
    have hcard : Fintype.card (G.UT (n + 1)) = Fintype.card (G.UT n) + n := by
      rw [StandardCharacterExists.card_UT, StandardCharacterExists.card_UT, Finset.sum_range_succ]
    have hqB : qU ^ (n + (Fintype.card (G.UT n) + n)) = Real.pi⁻¹ ^ n * qU ^ Fintype.card (G.UT (n + 1)) := by
      rw [hcard, pow_add, qU_eq]
    rw [hdl2, hsqB, hbB, hl2, hzs, hKc, hqB]
    exact B_alg ‖z‖ R Gm dG βn (qU ^ Fintype.card (G.UT (n + 1))) nh bh ((n + 1 : ℕ) : ℝ) κ Real.pi
      (norm_pos_iff.2 hz) hR hGm0 hdG0 hβ0 hbh0 (by positivity) n j hκ Real.pi_pos (by positivity)

end pts

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem det_congr_size (P : C.LPt) {N N' : ℕ} (h : N = N') : (D.ptMatN P N).det = (D.ptMatN P N').det := by
  subst h; rfl

/- English proof (translation)
Unfold `U.blk2`. Rewrite using `[Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]`.
-/
theorem det_block_diagonal_two {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (Dm : Matrix (Fin s) (Fin s) ℂ) :
    (U.blk2 A 0 0 Dm).det = A.det * Dm.det := by
  unfold U.blk2
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

/- English proof (translation)
Rewrite using `[PBJ.Asm.ptMatN_append, det_block_diagonal_two]`.
-/
theorem det_append (H L : C.LPt) :
    (D.ptMatN (H ++ L) (D.ptSize H + D.ptSize L)).det = (D.ptMatN H (D.ptSize H)).det * (D.ptMatN L (D.ptSize L)).det := by
  rw [PBJ.Asm.ptMatN_append, det_block_diagonal_two]

/- English proof (translation)
Unfold `G.ptLong`. Rewrite using `[Matrix.det_smul, Fintype.card_fin]`.
-/
theorem det_ptLong (n : ℕ) (t : ℂ) : (G.ptLong n t).det = t ^ n * (G.wMat n).det := by
  unfold G.ptLong
  rw [Matrix.det_smul, Fintype.card_fin]

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Rewrite using `[det_congr_size _ (show D.ptSize [(m + 1, t), (1, c)] = m + 1 + 1 by simp [D.ptSize]), PBJ.Asm.ptMatN_block, PBJ.Asm.ptBlock_eq, det_block_diagonal_two, det_ptLong]`. Establish `h1 : (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => c).det = c`. Rewrite using `[Matrix.det_unique]`. Both sides reduce to the same expression.

Rewrite using `[h1]`.
-/
theorem det_pair (n : ℕ) (hn : 1 ≤ n) (t c : ℂ) :
    (D.ptMatN [(n, t), (1, c)] (D.ptSize [(n, t), (1, c)])).det = t ^ n * (G.wMat n).det * c := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [det_congr_size _ (show D.ptSize [(m + 1, t), (1, c)] = m + 1 + 1 by simp [D.ptSize]), PBJ.Asm.ptMatN_block,
    PBJ.Asm.ptBlock_eq, det_block_diagonal_two, det_ptLong]
  have h1 : (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => c).det = c := by
    rw [Matrix.det_unique]; rfl
  rw [h1]

/- English proof (translation)
Rewrite using `[det_congr_size _ (show D.ptSize [(n, t)] = n by simp [D.ptSize]), PBJ.Asm.ptMatN_long, det_ptLong]`.
-/
theorem det_single (n : ℕ) (t : ℂ) : (D.ptMatN [(n, t)] (D.ptSize [(n, t)])).det = t ^ n * (G.wMat n).det := by
  rw [det_congr_size _ (show D.ptSize [(n, t)] = n by simp [D.ptSize]), PBJ.Asm.ptMatN_long, det_ptLong]

/- English proof (translation)
Use extensionality with `a b`. Establish `e : H ++ [(n, t), (1, c)] = (H ++ [(n, t)]) ++ [(1, c)]` using `by simp`. Simplify using `only [D.ptMatN]`. Rewrite using `[e, PBJ.Asm.ptEntry_append, if_pos]`. Rewrite using `[PBJ.Asm.ptSize_append, PBJ.Asm.ptSize_single]`.

Conclude with `⟨by omega, by omega⟩`.
-/
theorem ptMatN_drop_last (H : C.LPt) (n : ℕ) (t c : ℂ) (r : ℕ) (hr : D.ptSize H + n = r) :
    D.ptMatN (H ++ [(n, t), (1, c)]) r = D.ptMatN (H ++ [(n, t)]) r := by
  ext a b
  have e : H ++ [(n, t), (1, c)] = (H ++ [(n, t)]) ++ [(1, c)] := by simp
  simp only [D.ptMatN]
  rw [e, PBJ.Asm.ptEntry_append, if_pos]
  rw [PBJ.Asm.ptSize_append, PBJ.Asm.ptSize_single]
  exact ⟨by omega, by omega⟩

/- English proof (translation)
Rewrite using `[Complex.normSq_eq_norm_sq, G5.norm_det_wMat]`. Evaluate the numerical expressions.
-/
theorem normSq_det_wMat (n : ℕ) : Complex.normSq (G.wMat n).det = 1 := by
  rw [Complex.normSq_eq_norm_sq, G5.norm_det_wMat]; norm_num

/- English proof (translation)
Establish `hL : D.ptSize [(n, t), (1, c)] = n + 1` using `by simp [D.ptSize]`. Rewrite using `[det_congr_size _ (show r + 1 = D.ptSize H + D.ptSize [(n, t), (1, c)] by omega), det_append, det_pair n hn]`.
-/
theorem det_top_Px (H : C.LPt) (n : ℕ) (hn : 1 ≤ n) (r : ℕ) (hr : D.ptSize H + n + 1 = r + 1) (t c : ℂ) :
    (D.ptMatN (H ++ [(n, t), (1, c)]) (r + 1)).det = (D.ptMatN H (D.ptSize H)).det * (t ^ n * (G.wMat n).det * c) := by
  have hL : D.ptSize [(n, t), (1, c)] = n + 1 := by simp [D.ptSize]
  rw [det_congr_size _ (show r + 1 = D.ptSize H + D.ptSize [(n, t), (1, c)] by omega), det_append,
    det_pair n hn]

/- English proof (translation)
Rewrite using `[ptMatN_drop_last H n t c r (by omega), det_congr_size _ (show r = D.ptSize H + D.ptSize [(n, t)] by rw [PBJ.Asm.ptSize_single]; omega), det_append, det_single]`.
-/
theorem det_low_Px (H : C.LPt) (n : ℕ) (r : ℕ) (hr : D.ptSize H + n + 1 = r + 1) (t c : ℂ) :
    (D.ptMatN (H ++ [(n, t), (1, c)]) r).det = (D.ptMatN H (D.ptSize H)).det * (t ^ n * (G.wMat n).det) := by
  rw [ptMatN_drop_last H n t c r (by omega),
    det_congr_size _ (show r = D.ptSize H + D.ptSize [(n, t)] by rw [PBJ.Asm.ptSize_single]; omega), det_append, det_single]

/- English proof (translation)
Unfold `D.ptG`. Rewrite using `[det_top_Px H n hn r hr, det_low_Px H n r hr]`. Simplify using `only [map_mul, map_pow, normSq_det_wMat, Complex.normSq_eq_norm_sq t]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ptG_Px (TT : ℝ) (H : C.LPt) (n : ℕ) (hn : 1 ≤ n) (r : ℕ) (hr : D.ptSize H + n + 1 = r + 1) (t c : ℂ) :
    D.ptG TT r (H ++ [(n, t), (1, c)]) =
      Complex.normSq (D.ptMatN H (D.ptSize H)).det * ‖t‖ ^ (2 * n) * (Complex.normSq c - TT) := by
  unfold D.ptG
  rw [det_top_Px H n hn r hr, det_low_Px H n r hr]
  simp only [map_mul, map_pow, normSq_det_wMat, Complex.normSq_eq_norm_sq t]
  ring

/- English proof (translation)
Establish `hG'` using `hG`. Rewrite `hG'` using `[ptG_Px TT H n hn r hr]`. Establish `hA : Complex.normSq (D.ptMatN H (D.ptSize H)).det * ‖t‖ ^ (2 * n) ≠ 0`. Introduce `h0`. Apply `hG'` to reduce the goal to its premises.

Rewrite using `[h0, zero_mul]`. Establish `key : Complex.normSq (D.ptMatN (H ++ [(n, t), (1, c)]) (r + 1)).det = Complex.normSq (D.ptMatN H (D.ptSize H)).det * ‖t‖ ^ (2 * n) * Complex.normSq c`. Rewrite using `[det_top_Px H n hn r hr]`. Simplify using `only [map_mul, map_pow, normSq_det_wMat, Complex.normSq_eq_norm_sq t]`. Expand and normalize the polynomial expressions, which then agree.

Unfold `Top.wPt`. Rewrite using `[ptG_Px TT H n hn r hr, key, mul_div_mul_left _ _ hA]`.
-/
theorem wPt_Px (TT : ℝ) (H : C.LPt) (n : ℕ) (hn : 1 ≤ n) (r : ℕ) (hr : D.ptSize H + n + 1 = r + 1) (t c : ℂ)
    (hG : D.ptG TT r (H ++ [(n, t), (1, c)]) ≠ 0) :
    Top.wPt TT r (H ++ [(n, t), (1, c)]) = Complex.normSq c / (Complex.normSq c - TT) := by
  have hG' := hG
  rw [ptG_Px TT H n hn r hr] at hG'
  have hA : Complex.normSq (D.ptMatN H (D.ptSize H)).det * ‖t‖ ^ (2 * n) ≠ 0 := by
    intro h0; apply hG'; rw [h0, zero_mul]
  have key : Complex.normSq (D.ptMatN (H ++ [(n, t), (1, c)]) (r + 1)).det =
      Complex.normSq (D.ptMatN H (D.ptSize H)).det * ‖t‖ ^ (2 * n) * Complex.normSq c := by
    rw [det_top_Px H n hn r hr]
    simp only [map_mul, map_pow, normSq_det_wMat, Complex.normSq_eq_norm_sq t]
    ring
  unfold Top.wPt
  rw [ptG_Px TT H n hn r hr, key, mul_div_mul_left _ _ hA]

end

end Formalism.FourierDecayAlt.P.GermRateSplit
