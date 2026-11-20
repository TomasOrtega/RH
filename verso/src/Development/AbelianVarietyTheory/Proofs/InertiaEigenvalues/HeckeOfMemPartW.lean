import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuaMatchingConjugatePrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftTransferHeckePolySplitPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingCharactersUnramifiedOffLevels
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceUniformiserIdeleValueUnramifiedChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.SplitCorr

section Algebra

open Polynomial Formalism.L2.Col

/- English proof (translation)
Establish `h` using `congrArg (Polynomial.eval (1 : ℂ)) (Multiset.prod_X_add_C_eq_sum_esymm M)`. Simplify `h` using `[Polynomial.eval_multiset_prod, Polynomial.eval_finset_sum, Multiset.map_map]`.
-/
theorem prod_one_add (M : Multiset ℂ) :
    (M.map fun b => 1 + b).prod = ∑ j ∈ Finset.range (M.card + 1), M.esymm j := by
  have h := congrArg (Polynomial.eval (1 : ℂ)) (Multiset.prod_X_add_C_eq_sum_esymm M)
  simpa [Polynomial.eval_multiset_prod, Polynomial.eval_finset_sum, Multiset.map_map] using h

/- English proof (translation)
Establish `key : ∀ (N : Multiset ℂ) (x : ℂ), x ≠ 0 → ((N.map fun b => X - C b).prod).eval x = x ^ N.card * (N.map fun b => 1 - c * b * (c * x)⁻¹).prod` using `fun N x hx => by`. Rewrite using `[Polynomial.eval_multiset_prod, Multiset.map_map, ← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul]`. Use `congr 1`. Use `Multiset.map_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp, eval_sub, eval_X, eval_C]`.

Clear the denominators using the available nonvanishing facts. Establish `e : (M.map fun b => X - C b).prod = (M'.map fun b => X - C b).prod`. Use `Polynomial.eq_of_infinite_eval_eq _ _ (Set.Infinite.mono (s := {0}ᶜ) (fun x hx => ?_) (Set.finite_singleton (0 : ℂ)).infinite_compl)` and prove the remaining obligations. Use `show eval x _ = eval x _`. Rewrite using `[key M x hx, key M' x hx, h, hc]`.

Rewrite using `[← Polynomial.roots_multiset_prod_X_sub_C M, e, Polynomial.roots_multiset_prod_X_sub_C]`.
-/
theorem eq_of_prod_eq {M M' : Multiset ℂ} (hc : M.card = M'.card) {c : ℂ} (h0 : c ≠ 0)
    (h : ∀ Y : ℂ, (M.map fun b => 1 - c * b * Y).prod = (M'.map fun b => 1 - c * b * Y).prod) : M = M' := by
  have key : ∀ (N : Multiset ℂ) (x : ℂ), x ≠ 0 → ((N.map fun b => X - C b).prod).eval x =
      x ^ N.card * (N.map fun b => 1 - c * b * (c * x)⁻¹).prod := fun N x hx => by
    rw [Polynomial.eval_multiset_prod, Multiset.map_map, ← Multiset.prod_replicate, ← Multiset.map_const',
      ← Multiset.prod_map_mul]
    congr 1
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp, eval_sub, eval_X, eval_C]
    field_simp
  have e : (M.map fun b => X - C b).prod = (M'.map fun b => X - C b).prod := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ (Set.Infinite.mono (s := {0}ᶜ) (fun x hx => ?_)
      (Set.finite_singleton (0 : ℂ)).infinite_compl)
    show eval x _ = eval x _
    rw [key M x hx, key M' x hx, h, hc]
  rw [← Polynomial.roots_multiset_prod_X_sub_C M, e, Polynomial.roots_multiset_prod_X_sub_C]

/- English proof (translation)
Rewrite using `[Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg q), Complex.ofReal_natCast, ← Complex.cpow_nat_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cpow_half {q : ℕ} (m : ℕ) : (q : ℂ) ^ ((m : ℂ) / 2) = (Real.sqrt q : ℂ) ^ m := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg q), Complex.ofReal_natCast, ← Complex.cpow_nat_mul]
  congr 1
  push_cast
  ring

/- English proof (translation)
Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg q), Complex.ofReal_natCast]`.
-/
theorem sqrt_sq' (q : ℕ) : (Real.sqrt q : ℂ) ^ 2 = q := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg q), Complex.ofReal_natCast]

/- English proof (translation)
Introduce `h` and use `by have := sqrt_sq' q rw [h] at this exact hq (by exact_mod_cast (by simpa using this.symm : (q : ℂ) = 0))`.
-/
theorem sqrt_ne {q : ℕ} (hq : q ≠ 0) : (Real.sqrt q : ℂ) ≠ 0 := fun h => by
  have := sqrt_sq' q
  rw [h] at this
  exact hq (by exact_mod_cast (by simpa using this.symm : (q : ℂ) = 0))

/- English proof (translation)
Establish `h` using `prod_one_add ((B.map fun b : ℂˣ => (b : ℂ)).map fun b => (-((Real.sqrt q : ℂ) ^ n * (Real.sqrt q : ℂ)⁻¹ * Y)) • b)`. Rewrite `h` using `[Multiset.map_map, Multiset.card_map, Multiset.card_map, hB]`. Use `Eq.trans ?_ (h.symm.trans (congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)))` and prove the remaining obligations. Rewrite using `[heckePolyOf, Polynomial.eval_finset_sum]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations.

Take `⟨m, rfl⟩ : ∃ m, n = j + m` from `Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))`. Rewrite using `[← Multiset.pow_smul_esymm, GlobalTheory.LFun.satEig, eval_mul, eval_C, eval_pow, eval_X, show (j : ℂ) * (((j + m : ℕ) : ℂ) - j) = ((j * m : ℕ) : ℂ) by push_cast; ring, cpow_half, smul_eq_mul]`. Establish `h1 : (q : ℂ) ^ (j * (j - 1) / 2) * (Real.sqrt q : ℂ) ^ j = (Real.sqrt q : ℂ) ^ (j * j)`. Rewrite using `[← sqrt_sq' q, ← pow_mul, ← pow_add, Nat.mul_div_cancel' (Nat.even_mul_pred_self j).two_dvd]`. Use `congr 1`.

Consider the cases of `j with`. Consider the case `zero => rfl`. Consider the case `succ j => simp only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (q : ℂ) ^ (j * (j - 1) / 2) = (Real.sqrt q : ℂ) ^ (j * j) * ((Real.sqrt q : ℂ)⁻¹) ^ j`.

Rewrite using `[← h1, mul_assoc, ← mul_pow, mul_inv_cancel₀ (sqrt_ne hq), one_pow, mul_one]`. Rewrite using `[h2, neg_eq_neg_one_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Function.comp, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_heckePolyOf {q n : ℕ} (hq : q ≠ 0) {B : Multiset ℂˣ} (hB : B.card = n) (Y : ℂ) :
    (heckePolyOf n q (GlobalTheory.LFun.satEig q n B)).eval Y =
      ((B.map fun b : ℂˣ => (b : ℂ)).map fun b => 1 - (Real.sqrt q : ℂ) ^ n * (Real.sqrt q : ℂ)⁻¹ * b * Y).prod := by
  have h := prod_one_add ((B.map fun b : ℂˣ => (b : ℂ)).map
    fun b => (-((Real.sqrt q : ℂ) ^ n * (Real.sqrt q : ℂ)⁻¹ * Y)) • b)
  rw [Multiset.map_map, Multiset.card_map, Multiset.card_map, hB] at h
  refine Eq.trans ?_ (h.symm.trans (congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)))
  · rw [heckePolyOf, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨m, rfl⟩ : ∃ m, n = j + m := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
    rw [← Multiset.pow_smul_esymm, GlobalTheory.LFun.satEig, eval_mul, eval_C, eval_pow, eval_X,
      show (j : ℂ) * (((j + m : ℕ) : ℂ) - j) = ((j * m : ℕ) : ℂ) by push_cast; ring, cpow_half, smul_eq_mul]
    have h1 : (q : ℂ) ^ (j * (j - 1) / 2) * (Real.sqrt q : ℂ) ^ j = (Real.sqrt q : ℂ) ^ (j * j) := by
      rw [← sqrt_sq' q, ← pow_mul, ← pow_add, Nat.mul_div_cancel' (Nat.even_mul_pred_self j).two_dvd]
      congr 1
      cases j with
      | zero => rfl
      | succ j => simp only [Nat.add_sub_cancel]; ring
    have h2 : (q : ℂ) ^ (j * (j - 1) / 2) = (Real.sqrt q : ℂ) ^ (j * j) * ((Real.sqrt q : ℂ)⁻¹) ^ j := by
      rw [← h1, mul_assoc, ← mul_pow, mul_inv_cancel₀ (sqrt_ne hq), one_pow, mul_one]
    rw [h2, neg_eq_neg_one_mul]
    ring
  · simp only [Function.comp, smul_eq_mul]
    ring

/- English proof (translation)
Establish `hs` using `sqrt_ne hq`. Establish `hz` using `z.ne_zero`. Establish `hy` using `y.ne_zero`. Use `eq_of_prod_eq (by simp [str, hB, hB']) (mul_ne_zero (pow_ne_zero (r + t) hs) (inv_ne_zero hs)) fun Y => ?_` and prove the remaining obligations. Establish `e` using `GlobalTheory.ThetaPrimeHecke.poly_id q r t ((z : ℂ)⁻¹ * (Real.sqrt q : ℂ) ^ r) ((y : ℂ)⁻¹ * (Real.sqrt q : ℂ) ^ (r + t)) (GlobalTheory.LFun.satEig q r B')`.

Establish `e1 : heckePolyOf (r + t) q (GlobalTheory.LFun.satEig q (r + t) B) = _` using `Eq.trans (by`. Unfold `heckePolyOf`. Conclude with `Finset.sum_congr rfl fun k hk => by`. Rewrite using `[h k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]) e`. Rewrite using `[← eval_heckePolyOf hq hB, e1, eval_mul, eval_comp, eval_heckePolyOf hq hB', Multiset.map_add, Multiset.prod_add]`.

Use `congr 1`. Rewrite using `[Multiset.map_map, Multiset.map_map]`. Use `congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp, eval_mul, eval_C, eval_X, Units.val_mul, Units.val_inv_eq_inv_val]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[blockPoly, Polynomial.eval_prod, ← Finset.prod_range_reflect, str, Multiset.map_map]`. Use `Finset.prod_congr rfl fun k hk => ?_` and prove the remaining obligations. Take `⟨m, rfl⟩ : ∃ m, t = k + m + 1` from `Nat.exists_eq_add_of_lt (Finset.mem_range.1 hk)`. Establish `hq' : (q : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hq`. Simplify using `only [Function.comp, eval_sub, eval_mul, eval_C, eval_X, eval_one]`.

Rewrite using `[show k + m + 1 - 1 - k = m by omega, Complex.cpow_sub _ _ hq', Complex.cpow_natCast, show (((k + m + 1 : ℕ) : ℂ) - 1) = ((k + m : ℕ) : ℂ) by push_cast; ring, cpow_half]`. Use `sqrt_sq' q` as an intermediate fact. Generalize the expression as in `(Real.sqrt q : ℂ) = s at *`. Rewrite using `[← this]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem params_eq {q r t : ℕ} (hq : q ≠ 0) {B B' : Multiset ℂˣ} (hB : B.card = r + t) (hB' : B'.card = r) (z y : ℂˣ)
    (h : ∀ k ≤ r + t, GlobalTheory.LFun.satEig q (r + t) B k = ∑ j ∈ Finset.range (r + 1),
      (if j ≤ k then (q : ℂ) ^ ((r - j) * (k - j)) * (gaussBin q t (k - j) : ℂ) *
        ((z : ℂ)⁻¹ * (Real.sqrt q : ℂ) ^ r)⁻¹ ^ k * ((y : ℂ)⁻¹ * (Real.sqrt q : ℂ) ^ (r + t)) ^ j else 0) *
        GlobalTheory.LFun.satEig q r B' j) :
    (B.map fun a : ℂˣ => (a : ℂ)) = (B'.map fun a : ℂˣ => ((a * z * y⁻¹ : ℂˣ) : ℂ)) + str q z t := by
  have hs := sqrt_ne hq
  have hz := z.ne_zero
  have hy := y.ne_zero
  refine eq_of_prod_eq (by simp [str, hB, hB']) (mul_ne_zero (pow_ne_zero (r + t) hs) (inv_ne_zero hs)) fun Y => ?_
  have e := GlobalTheory.ThetaPrimeHecke.poly_id q r t ((z : ℂ)⁻¹ * (Real.sqrt q : ℂ) ^ r)
    ((y : ℂ)⁻¹ * (Real.sqrt q : ℂ) ^ (r + t)) (GlobalTheory.LFun.satEig q r B')
  have e1 : heckePolyOf (r + t) q (GlobalTheory.LFun.satEig q (r + t) B) = _ := Eq.trans (by
    unfold heckePolyOf
    exact Finset.sum_congr rfl fun k hk => by
      rw [h k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]) e
  rw [← eval_heckePolyOf hq hB, e1, eval_mul, eval_comp, eval_heckePolyOf hq hB', Multiset.map_add, Multiset.prod_add]
  congr 1
  · rw [Multiset.map_map, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
    simp only [Function.comp, eval_mul, eval_C, eval_X, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  · rw [blockPoly, Polynomial.eval_prod, ← Finset.prod_range_reflect, str, Multiset.map_map]
    refine Finset.prod_congr rfl fun k hk => ?_
    obtain ⟨m, rfl⟩ : ∃ m, t = k + m + 1 := Nat.exists_eq_add_of_lt (Finset.mem_range.1 hk)
    have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
    simp only [Function.comp, eval_sub, eval_mul, eval_C, eval_X, eval_one]
    rw [show k + m + 1 - 1 - k = m by omega, Complex.cpow_sub _ _ hq', Complex.cpow_natCast,
      show (((k + m + 1 : ℕ) : ℂ) - 1) = ((k + m : ℕ) : ℂ) by push_cast; ring, cpow_half]
    have := sqrt_sq' q
    generalize (Real.sqrt q : ℂ) = s at *
    rw [← this]
    field_simp
    ring

end Algebra

section Place

open GlobalTheory.Hk3 GlobalTheory.LFun

variable {D : D7}

/- English proof (translation)
Take `⟨⟨η, hη⟩, hall⟩` from `hR`. Establish `hprod : y * Units.map (cA D).toMonoidHom y = idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) y)`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[GlobalTheory.Mem.EtaTilde.idF_norm]`. Both sides reduce to the same expression.

Establish `h1 : χ y * χ (Units.map (cA D).toMonoidHom y) = 1`. Rewrite using `[← map_mul, hprod, hall η hη, hη.2.2.1, one_pow]`. Conclude with `eq_inv_of_mul_eq_one_right h1`.
-/
theorem chi_conj {χ : (AE D)ˣ →* Circle} {n : ℕ} (hR : Formalism.L2.Theta.ResEta D χ n) (y : (AE D)ˣ) :
    χ (Units.map (cA D).toMonoidHom y) = (χ y)⁻¹ := by
  obtain ⟨⟨η, hη⟩, hall⟩ := hR
  have hprod : y * Units.map (cA D).toMonoidHom y =
      idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) y) := by
    apply Units.ext
    rw [GlobalTheory.Mem.EtaTilde.idF_norm]
    rfl
  have h1 : χ y * χ (Units.map (cA D).toMonoidHom y) = 1 := by
    rw [← map_mul, hprod, hall η hη, hη.2.2.1, one_pow]
  exact eq_inv_of_mul_eq_one_right h1

/- English proof (translation)
Introduce `y hy`. Establish `hP : IsPrimeIdem w e (e + cA D e)` using `Or.inl ⟨he, rfl⟩`. Establish `hf` using `finPart_of_isPrimeIdem hP`. Establish `hc : ∀ (y : (w.adicCompletion D.host.E)ˣ) u, compAt D.host.F u (finPart D (locIdele D.host.F w y : AE D)) = Neutral.B1.finiteSingle D.host.E w y u` using `fun y u => congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z u) (finTens_locIdele (F := D.host.F) w y)`. Establish `hint : ∀ y : (w.adicCompletion D.host.E)ˣ, Valued.v (y : w.adicCompletion D.host.E) = 1 → finPart D (e * (locIdele D.host.F w y : AE D)) ∈ intAE D` using `fun y hy => by`.

Rewrite using `[RingHom.map_mul, hf, singleAt_mul, one_mul, hc, finSingle_self]`. Conclude with `singleAt_mem_intAE hy.le`. Establish `h1 : χ (locIdele D.host.F w y) = 1`. Use `GlobalTheory.Hk3.SplitMatch.unr he h _ ?_ (hint y hy) ?_` and prove the remaining obligations. Use `GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ (compAt_ext fun u => ?_)` and prove the remaining obligations.

Rewrite using `[RingHom.map_mul, show infPart D (locIdele D.host.F w y : AE D) = 1 from infTens_locIdele w y, mul_one]`. Rewrite using `[RingHom.map_mul, RingHom.map_mul, hc, RingHom.map_sub, RingHom.map_one, RingHom.map_sub, RingHom.map_one, hf]`. Distinguish the cases in `hu : u = w`. Substitute `hu` using the available equality. Rewrite using `[compAt_singleAt, sub_self, zero_mul]`.

Rewrite using `[finSingle_ne hu, mul_one]`. Rewrite using `[← map_inv]`. Use `hint _ ?_` and prove the remaining obligations. Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀, show Valued.v (y : w.adicCompletion D.host.E) = 1 from hy, inv_one]`. Conclude with `(congrArg Circle.toUnits h1).trans (map_one _)`.
-/
theorem unrAt_of_unrPl {w : HeightOneSpectrum (𝓞 D.host.E)} {e : AE D} (he : Formalism.L2.NTheta.IsIdemAt e w)
    {χ : (AE D)ˣ →* Circle} (h : UnrPl w χ) : UnrAt χ w := by
  intro y hy
  have hP : IsPrimeIdem w e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have hf := finPart_of_isPrimeIdem hP
  have hc : ∀ (y : (w.adicCompletion D.host.E)ˣ) u, compAt D.host.F u (finPart D (locIdele D.host.F w y : AE D)) =
      Neutral.B1.finiteSingle D.host.E w y u := fun y u =>
    congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z u) (finTens_locIdele (F := D.host.F) w y)
  have hint : ∀ y : (w.adicCompletion D.host.E)ˣ, Valued.v (y : w.adicCompletion D.host.E) = 1 →
      finPart D (e * (locIdele D.host.F w y : AE D)) ∈ intAE D := fun y hy => by
    rw [RingHom.map_mul, hf, singleAt_mul, one_mul, hc, finSingle_self]
    exact singleAt_mem_intAE hy.le
  have h1 : χ (locIdele D.host.F w y) = 1 := by
    refine GlobalTheory.Hk3.SplitMatch.unr he h _ ?_ (hint y hy) ?_
    · refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ (compAt_ext fun u => ?_)
      · rw [RingHom.map_mul, show infPart D (locIdele D.host.F w y : AE D) = 1 from infTens_locIdele w y, mul_one]
      · rw [RingHom.map_mul, RingHom.map_mul, hc, RingHom.map_sub, RingHom.map_one, RingHom.map_sub, RingHom.map_one, hf]
        by_cases hu : u = w
        · subst hu
          rw [compAt_singleAt, sub_self, zero_mul]
        · rw [finSingle_ne hu, mul_one]
    · rw [← map_inv]
      refine hint _ ?_
      rw [Units.val_inv_eq_inv_val, map_inv₀, show Valued.v (y : w.adicCompletion D.host.E) = 1 from hy, inv_one]
  exact (congrArg Circle.toUnits h1).trans (map_one _)

/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]`. Conclude with `(Nat.card_congr (Ideal.quotientEquiv P.asIdeal (Formalism.DivisionValues.conjPl P).asIdeal (Formalism.DivisionValues.cO D.host.E) rfl).toEquiv).symm`.
-/
theorem absNorm_conjPl (P : Pl D.host.E) : Ideal.absNorm (Formalism.DivisionValues.conjPl P).asIdeal = Ideal.absNorm P.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr
    (Ideal.quotientEquiv P.asIdeal (Formalism.DivisionValues.conjPl P).asIdeal (Formalism.DivisionValues.cO D.host.E) rfl).toEquiv).symm

/- English proof (translation)
Simplify using `[dualLab, splitLab]`.
-/
theorem dual_splitLab {n k : ℕ} : dualLab (splitLab n k) = List.replicate k 1 ++ List.replicate (n - k) 0 := by
  simp [dualLab, splitLab]

/- English proof (translation)
Take `⟨e₀, he₀⟩` from `GlobalTheory.Hk3.SplitMatch.exists_isIdemAt hc`. Take `⟨e, ϖ, x, he, h1, h2, hx, hval⟩` from `GlobalTheory.SplitUnifIdele.value_eq_val D _ w rfl hs χS (unrAt_of_unrPl he₀ hS)`. Establish `hfix` using `(GlobalTheory.Hk3.SplitMatch.match_split ψ S T χS χT om w hW hc hS hT).1`. Use `⟨hfix, fun V k hk => ?_, fun k hk => ?_⟩` and prove the remaining obligations. Take `⟨_, R, _, -, -, a, -⟩` from `GlobalTheory.Hk3.SplitMatch.exists_data he h1 h2 V`.

Conclude with `⟨_, a k hk⟩`. Establish `hcc` using `GlobalTheory.Hk3.ConjMatch.conj_conj w`. Establish `he' : Formalism.L2.NTheta.IsIdemAt (cA D e) (Formalism.DivisionValues.conjPl w)` using `(GlobalTheory.IdemSupport.supported_group_and_prime_idempotents S).2.2.2 w _ e he (GlobalTheory.GoodPrimes.isConjPl_iff.2 rfl)`. Establish `h1' : Formalism.DivisionValues.cO D.host.E ϖ ∈ (Formalism.DivisionValues.conjPl w).asIdeal` using `Ideal.mem_map_of_mem _ h1`. Establish `h2' : Formalism.DivisionValues.cO D.host.E ϖ ∉ (Formalism.DivisionValues.conjPl w).asIdeal ^ 2` using `fun h => h2 (by`.

Rewrite `h` using `[show (Formalism.DivisionValues.conjPl w).asIdeal = w.asIdeal.map (Formalism.DivisionValues.cO D.host.E) from rfl, ← Ideal.map_pow, Ideal.mem_map_of_equiv]`. Take `⟨y, hy, e⟩` from `h`. Rewrite using `[← (Formalism.DivisionValues.cO D.host.E).injective e])` and apply the resulting hypothesis. Establish `hx' : ((Units.map (cA D).toMonoidHom x : (AE D)ˣ) : AE D) = cA D e * incA D ((Formalism.DivisionValues.cO D.host.E ϖ : 𝓞 D.host.E) : D.host.E) + (1 - cA D e)` using `by show cA D (x : AE D) = _`. Rewrite using `[hx, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one]`.

Both sides reduce to the same expression. Establish `hM` using `((GlobalTheory.Hk3.SplitMatch.match_split ψ S T χS χT om _ hW (by rw [hcc]; exact hc.symm) hS' hT').2 _ _ _ t he' h1' h2' hx').2 hr k hk`. Rewrite `hM` using `[((GlobalTheory.Hk3.ConjMatch.match_conj ψ S T χS χT om w hW).2 hfix).2, GlobalTheory.Hk3.SplitMatch.dualC_splitC, chi_conj hW.resS, chi_conj hW.resT, Circle.coe_inv, Circle.coe_inv, hval χS (unrAt_of_unrPl he hS), hval χT (unrAt_of_unrPl he hT), absNorm_conjPl]`. Rewrite `hM` using `[show dualC (Finsupp.single (splitLab S.rank k) 1) = Finsupp.single (dualLab (splitLab S.rank k)) 1 from Finsupp.mapDomain_single]`. Then use the resulting hypothesis.
-/
theorem match_pos {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hW : IsWeilDatumO ψ S T χS χT om) (hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)))
    (hc : Formalism.DivisionValues.conjPl w ≠ w) (hS : UnrPl w χS) (hT : UnrPl w χT) (hS' : UnrPl (Formalism.DivisionValues.conjPl w) χS)
    (hT' : UnrPl (Formalism.DivisionValues.conjPl w) χT) {t : ℕ} (hr : S.rank = T.rank + t) :
    VacFix ψ om w ∧ (∀ V : HSp D, ∀ k ≤ V.rank, IsLab V w (dualLab (splitLab V.rank k))) ∧ ∀ k ≤ S.rank,
      Match ψ om w (dualC (Finsupp.single (dualLab (splitLab S.rank k)) 1))
        (∑ j ∈ Finset.range (T.rank + 1), Finsupp.single (dualLab (splitLab T.rank j))
          (if j ≤ k then (Ideal.absNorm w.asIdeal : ℂ) ^ ((T.rank - j) * (k - j)) *
            (Formalism.L2.Col.gaussBin (Ideal.absNorm w.asIdeal) t (k - j) : ℂ) *
            ((val (F := D.host.F) χT w : ℂ)⁻¹ * (Real.sqrt (Ideal.absNorm w.asIdeal) : ℂ) ^ T.rank)⁻¹ ^ k *
            ((val (F := D.host.F) χS w : ℂ)⁻¹ * (Real.sqrt (Ideal.absNorm w.asIdeal) : ℂ) ^ S.rank) ^ j else 0)) := by
  obtain ⟨e₀, he₀⟩ := GlobalTheory.Hk3.SplitMatch.exists_isIdemAt hc
  obtain ⟨e, ϖ, x, he, h1, h2, hx, hval⟩ :=
    GlobalTheory.SplitUnifIdele.value_eq_val D _ w rfl hs χS (unrAt_of_unrPl he₀ hS)
  have hfix := (GlobalTheory.Hk3.SplitMatch.match_split ψ S T χS χT om w hW hc hS hT).1
  refine ⟨hfix, fun V k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨_, R, _, -, -, a, -⟩ := GlobalTheory.Hk3.SplitMatch.exists_data he h1 h2 V
    exact ⟨_, a k hk⟩
  have hcc := GlobalTheory.Hk3.ConjMatch.conj_conj w
  have he' : Formalism.L2.NTheta.IsIdemAt (cA D e) (Formalism.DivisionValues.conjPl w) :=
    (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents S).2.2.2 w _ e he (GlobalTheory.GoodPrimes.isConjPl_iff.2 rfl)
  have h1' : Formalism.DivisionValues.cO D.host.E ϖ ∈ (Formalism.DivisionValues.conjPl w).asIdeal := Ideal.mem_map_of_mem _ h1
  have h2' : Formalism.DivisionValues.cO D.host.E ϖ ∉ (Formalism.DivisionValues.conjPl w).asIdeal ^ 2 := fun h => h2 (by
    rw [show (Formalism.DivisionValues.conjPl w).asIdeal = w.asIdeal.map (Formalism.DivisionValues.cO D.host.E) from rfl, ← Ideal.map_pow,
      Ideal.mem_map_of_equiv] at h
    obtain ⟨y, hy, e⟩ := h
    rwa [← (Formalism.DivisionValues.cO D.host.E).injective e])
  have hx' : ((Units.map (cA D).toMonoidHom x : (AE D)ˣ) : AE D) =
      cA D e * incA D ((Formalism.DivisionValues.cO D.host.E ϖ : 𝓞 D.host.E) : D.host.E) + (1 - cA D e) := by
    show cA D (x : AE D) = _
    rw [hx, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
    rfl
  have hM := ((GlobalTheory.Hk3.SplitMatch.match_split ψ S T χS χT om _ hW (by rw [hcc]; exact hc.symm) hS' hT').2
    _ _ _ t he' h1' h2' hx').2 hr k hk
  rw [((GlobalTheory.Hk3.ConjMatch.match_conj ψ S T χS χT om w hW).2 hfix).2, GlobalTheory.Hk3.SplitMatch.dualC_splitC,
    chi_conj hW.resS, chi_conj hW.resT, Circle.coe_inv, Circle.coe_inv, hval χS (unrAt_of_unrPl he hS),
    hval χT (unrAt_of_unrPl he hT), absNorm_conjPl] at hM
  rwa [show dualC (Finsupp.single (splitLab S.rank k) 1) = Finsupp.single (dualLab (splitLab S.rank k)) 1 from
    Finsupp.mapDomain_single] at hM

/- English proof (translation)
Unfold `hk`. Rewrite using `[← Finsupp.sum_finsetSum_index (by simp) (by simp [add_smul])]`. Conclude with `Finset.sum_congr rfl fun j _ => Finsupp.sum_single_index (zero_smul _ _)`.
-/
theorem hk_sum (V : HSp D) (P : Pl D.host.E) (s : Finset ℕ) (d : ℕ → List ℤ) (z : ℕ → ℂ) :
    hk V P (∑ j ∈ s, Finsupp.single (d j) (z j)) = ∑ j ∈ s, z j • heckeLin V (Hk3.rep V P (d j)) := by
  unfold hk
  rw [← Finsupp.sum_finsetSum_index (by simp) (by simp [add_smul])]
  exact Finset.sum_congr rfl fun j _ => Finsupp.sum_single_index (zero_smul _ _)

/- English proof (translation)
Break down `hB with hB | ⟨hi, -⟩` into its components or cases. Simplify using `only [dual_splitLab]`. Conclude with `hB`. Conclude with `absurd (GlobalTheory.WeilAtPlace.conjPl_eq_of_inert hi h) hc`.
-/
theorem param_split {n : ℕ} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = v) (hc : Formalism.DivisionValues.conjPl w ≠ w) {c : List ℤ → ℂ} {B : Multiset ℂˣ}
    (hB : IsSysParam D.sp.cm.sig n h c B) : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v ∧ B.card = n ∧
      ∀ j ≤ n, c (dualLab (splitLab n j)) = satEig (Ideal.absNorm w.asIdeal) n B j := by
  rcases hB with hB | ⟨hi, -⟩
  · simp only [dual_splitLab]
    exact hB
  · exact absurd (GlobalTheory.WeilAtPlace.conjPl_eq_of_inert hi h) hc

end Place

section Real

open GlobalTheory.Hk3 GlobalTheory.LFun

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

/- English proof (translation)
The claim follows from `sub_eq_zero.1 (GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ (R.MW i (sg0 D A)) R.θ hC.models.inf (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ _ (sub_mem (hC.thP.thF_mem i t y') (GlobalTheory.DefLiftHecke.wall_laws hC i t hP cW (hC.thP.thF_mem i t y)).1) fun v => su …`.
-/
theorem thF_match (hC : Core R F) (i : Fin D.R.m) (t : T) {P : Pl D.host.E} (hP : Good R t P)
    (hfix : VacFix R.ψ (R.ωP i t) P) {cV cW : List ℤ →₀ ℂ} (hM : Match R.ψ (R.ωP i t) P (dualC cV) cW)
    {y y' : (R.HV i t).H} (hy : (R.HV i t).e y' = hkF (Vc D i) P cV ((R.HV i t).e y)) :
    R.thF i t y' = postOn (R.MW i (sg0 D A)) (hk (Wc D i) P cW) (R.thF i t y) :=
  sub_eq_zero.1 (GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ (R.MW i (sg0 D A)) R.θ hC.models.inf
    (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ _
    (sub_mem (hC.thP.thF_mem i t y') (GlobalTheory.DefLiftHecke.wall_laws hC i t hP cW (hC.thP.thF_mem i t y)).1)
    fun v => sub_eq_zero.2 (GlobalTheory.DefLiftHecke.thF_low hC i t hP hfix hM hy v))

/- English proof (translation)
Unfold `GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl`. Simplify using `only [Finset.mem_image, Finset.mem_union, not_exists, not_and]`. Introduce `PP hPP e`. Break down `GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with h1 | h1` into its components or cases. Conclude with `(hw PP hPP).1 h1.symm`.

Conclude with `(hw PP hPP).2 (GlobalTheory.GoodPrimes.isConjPl_iff.2 h1)`.
-/
theorem not_mem_badPl {t : T} {w : Pl D.host.E} (hw : Good R t w) :
    w.under (𝓞 D.host.F) ∉ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t := by
  classical
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl
  simp only [Finset.mem_image, Finset.mem_union, not_exists, not_and]
  intro PP hPP e
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with h1 | h1
  · exact (hw PP hPP).1 h1.symm
  · exact (hw PP hPP).2 (GlobalTheory.GoodPrimes.isConjPl_iff.2 h1)

/- English proof (translation)
Take `⟨n, hβ⟩` from `hC.lev.βW i`. Establish `hlev` using `GlobalTheory.LevOp.level_operators (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ P (GlobalTheory.DefLiftHecke.one_pow_notMem P n) (fun PP hPP => hP PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))`. Conclude with `((Formalism.IndefR.Mult.mem_partFull _ _ _ _ _ _ _).1 hU).2 P d _ ((hlev.2.1 _ d _).2 ⟨(GlobalTheory.GoodPrimes.offS_iff _ P).2 (not_mem_badPl hP), GlobalTheory.SphLabelOps.sphOp_rep hd⟩) v`.
-/
theorem hecke_of_mem_partW (hC : Core R F) (i : Fin D.R.m) (t : T) {P : Pl D.host.E} (hP : Good R t P) {c : Sys D}
    {U : MMap (R.MW i (sg0 D A))} (hU : U ∈ partW R i t c) {d : List ℤ} (hd : IsLab (Wc D i) P d)
    (v : (R.MW i (sg0 D A)).Vec) : heckeLin (Wc D i) (Hk3.rep (Wc D i) P d) (U v) = c P d • U v := by
  obtain ⟨n, hβ⟩ := hC.lev.βW i
  have hlev := GlobalTheory.LevOp.level_operators (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ P
    (GlobalTheory.DefLiftHecke.one_pow_notMem P n) (fun PP hPP => hP PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))
  exact ((Formalism.IndefR.Mult.mem_partFull _ _ _ _ _ _ _).1 hU).2 P d _
    ((hlev.2.1 _ d _).2 ⟨(GlobalTheory.GoodPrimes.offS_iff _ P).2 (not_mem_badPl hP), GlobalTheory.SphLabelOps.sphOp_rep hd⟩) v

/- English proof (translation)
Take `⟨v, hv⟩` from `hU`. Use `smul_left_injective ℂ hv ?_` and prove the remaining obligations. Use `show a • U v = (∑ j ∈ s, z j * b j) • U v`. Rewrite using `[h, LinearMap.sum_apply, Finset.sum_smul]`. Conclude with `Finset.sum_congr rfl fun j hj => by rw [LinearMap.smul_apply, hL j hj, smul_smul]`.
-/
theorem eig_eq {X Y : Type} [AddCommGroup Y] [Module ℂ Y] {U : X → Y} (hU : ∃ v, U v ≠ 0) {a : ℂ} {s : Finset ℕ}
    {z b : ℕ → ℂ} {L : ℕ → Y →ₗ[ℂ] Y} (h : ∀ v, a • U v = (∑ j ∈ s, z j • L j) (U v))
    (hL : ∀ j ∈ s, ∀ v, L j (U v) = b j • U v) : a = ∑ j ∈ s, z j * b j := by
  obtain ⟨v, hv⟩ := hU
  refine smul_left_injective ℂ hv ?_
  show a • U v = (∑ j ∈ s, z j * b j) • U v
  rw [h, LinearMap.sum_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun j hj => by rw [LinearMap.smul_apply, hL j hj, smul_smul]

/- English proof (translation)
Establish `hU : ∃ v, U v ≠ 0`. Assume the negation of the conclusion as `hn`. Conclude with `h0 (MultilinearMap.ext fun v => not_not.1 fun hv => hn ⟨v, hv⟩)`. Rewrite `h` using `[hk_sum]`. Conclude with `eig_eq hU (fun v => congrArg (fun U : MMap M => U v) h) hL`.
-/
theorem eig_eq' {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {U : MMap M} (h0 : U ≠ 0) {P : Pl D.host.E} {a : ℂ}
    {s : Finset ℕ} {d : ℕ → List ℤ} {z : ℕ → ℂ} (b : ℕ → ℂ)
    (h : a • U = postOn M (hk V P (∑ j ∈ s, Finsupp.single (d j) (z j))) U)
    (hL : ∀ j ∈ s, ∀ v, heckeLin V (Hk3.rep V P (d j)) (U v) = b j • U v) : a = ∑ j ∈ s, z j * b j := by
  have hU : ∃ v, U v ≠ 0 := by
    by_contra hn
    exact h0 (MultilinearMap.ext fun v => not_not.1 fun hv => hn ⟨v, hv⟩)
  rw [hk_sum] at h
  exact eig_eq hU (fun v => congrArg (fun U : MMap M => U v) h) hL

/- English proof (translation)
The claim follows from `eig_eq' h0 (fun j => c P (d j)) h fun j hj v => hecke_of_mem_partW hC i t hP hU (hd j hj) v`.
-/
theorem eig_part (hC : Core R F) (i : Fin D.R.m) (t : T) {P : Pl D.host.E} (hP : Good R t P) {c : Sys D}
    {U : MMap (R.MW i (sg0 D A))} (h0 : U ≠ 0) (hU : U ∈ partW R i t c) {a : ℂ} (s : Finset ℕ) (d : ℕ → List ℤ) (z : ℕ → ℂ)
    (h : a • U = postOn (R.MW i (sg0 D A)) (hk (Wc D i) P (∑ j ∈ s, Finsupp.single (d j) (z j))) U)
    (hd : ∀ j ∈ s, IsLab (Wc D i) P (d j)) : a = ∑ j ∈ s, z j * c P (d j) :=
  eig_eq' h0 (fun j => c P (d j)) h fun j hj v => hecke_of_mem_partW hC i t hP hU (hd j hj) v

/- English proof (translation)
Establish `hWr : (Wc D i).rank = D.R.r` using `D.sp.W_rank _ (Nat.le_add_left _ _) i.2`. Establish `hV : (Vc D i).rank = (Wc D i).rank + D.R.t`. Rewrite using `[hWr]`. Conclude with `D.sp.V_rank _ (Nat.le_add_left _ _) i.2`. Rewrite `hB'` using `[← hWr]`.

Take `⟨hs, b1, b2⟩` from `param_split rfl hne (hB _ (not_mem_badPl hw) w rfl)`. Take `⟨-, b1', b2'⟩` from `param_split rfl hne (hB' _ (not_mem_badPl hw) w rfl)`. Establish `hw'` using `((GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.1 t w hw).2.1`. Take `⟨u1, u2⟩` from `GlobalTheory.UnrOffLevels.unrPl_of_good R F hC.lev t _ hw`. Take `⟨u1', u2'⟩` from `GlobalTheory.UnrOffLevels.unrPl_of_good R F hC.lev t _ hw'`.

Establish `u3` using `u2 ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2`. Establish `u3'` using `u2' ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2`. Take `⟨hfix, hlab, hM⟩` from `match_pos (hC.thP.ωP i t) hs hne u3 (GlobalTheory.ThetaPrimeHecke.unrPl_mul_inv u3 u1) u3' (GlobalTheory.ThetaPrimeHecke.unrPl_mul_inv u3' u1') hV`. Use `params_eq (q := Ideal.absNorm w.asIdeal) (qV_ne_zero w) (b1.trans hV) b1' _ _ fun k hk => ?_` and prove the remaining obligations. Rewrite `hk`, the goal using `[← hV]`.

Establish `e1` using `thF_match hC i t hw hfix (hM k hk) (hh w hw _ y)`. Establish `e2` using `((congrArg (R.thF i t) (hy w _ hw (hlab _ k hk))).trans ((R.thF i t).map_smul _ _)).symm.trans e1`. Establish `e3` using `eig_part hC i t hw h0 hc _ (fun j => dualLab (splitLab (Wc D i).rank j)) _ e2 fun j hj => hlab _ j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))`. Use `(b2 k hk).symm.trans (e3.trans (Finset.sum_congr rfl fun j hj => ?_))` and prove the remaining obligations. Rewrite using `[b2' j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]`.

Both sides reduce to the same expression.
-/
theorem unrCorr_at (hC : Core R F) (i : Fin D.R.m) (t : T)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i t).H) (hh : IsOpsV R i t h) (s c : Sys D) (y : (R.HV i t).H)
    (hy : IsEigV R i t h s y) (h0 : R.thF i t y ≠ 0) (hc : R.thF i t y ∈ partW R i t c) (B B' : Fam D.host.E)
    (hB : IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B)
    (hB' : IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) D.R.r c B') (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : Good R t w)
    (hne : Formalism.DivisionValues.conjPl w ≠ w) :
    (B w).map (fun a : ℂˣ => (a : ℂ)) =
      (B' w).map (fun a : ℂˣ => ((a * valV R i t w * (valW R i t w)⁻¹ : ℂˣ) : ℂ)) +
        str (Ideal.absNorm w.asIdeal) (valV R i t w : ℂ) D.R.t := by
  have hWr : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hV : (Vc D i).rank = (Wc D i).rank + D.R.t := by
    rw [hWr]
    exact D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  rw [← hWr] at hB'
  obtain ⟨hs, b1, b2⟩ := param_split rfl hne (hB _ (not_mem_badPl hw) w rfl)
  obtain ⟨-, b1', b2'⟩ := param_split rfl hne (hB' _ (not_mem_badPl hw) w rfl)
  have hw' := ((GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.1 t w hw).2.1
  obtain ⟨u1, u2⟩ := GlobalTheory.UnrOffLevels.unrPl_of_good R F hC.lev t _ hw
  obtain ⟨u1', u2'⟩ := GlobalTheory.UnrOffLevels.unrPl_of_good R F hC.lev t _ hw'
  have u3 := u2 ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2
  have u3' := u2' ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2
  obtain ⟨hfix, hlab, hM⟩ := match_pos (hC.thP.ωP i t) hs hne u3 (GlobalTheory.ThetaPrimeHecke.unrPl_mul_inv u3 u1) u3'
    (GlobalTheory.ThetaPrimeHecke.unrPl_mul_inv u3' u1') hV
  refine params_eq (q := Ideal.absNorm w.asIdeal) (qV_ne_zero w) (b1.trans hV) b1' _ _ fun k hk => ?_
  rw [← hV] at hk ⊢
  have e1 := thF_match hC i t hw hfix (hM k hk) (hh w hw _ y)
  have e2 := ((congrArg (R.thF i t) (hy w _ hw (hlab _ k hk))).trans ((R.thF i t).map_smul _ _)).symm.trans e1
  have e3 := eig_part hC i t hw h0 hc _ (fun j => dualLab (splitLab (Wc D i).rank j)) _ e2
    fun j hj => hlab _ j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  refine (b2 k hk).symm.trans (e3.trans (Finset.sum_congr rfl fun j hj => ?_))
  rw [b2' j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  rfl

end Real

/- English proof (translation)
Introduce `D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t h hh s c y hy h0 hc B B' hB hB' w hw hok`. Use `unrCorr_at hG.core i t h hh s c y hy h0 hc B B' hB hB' w hw fun e => hok ?_` and prove the remaining obligations. Conclude with `GlobalTheory.GoodPrimes.isConjPl_iff.2 e.symm`.
-/
theorem unrCorr_split : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, UnrCorr R i t (fun w => ¬ IsConjPl w w) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t h hh s c y hy h0 hc B B' hB hB' w hw hok
  refine unrCorr_at hG.core i t h hh s c y hy h0 hc B B' hB hB' w hw fun e => hok ?_
  exact GlobalTheory.GoodPrimes.isConjPl_iff.2 e.symm

end GlobalTheory.SplitCorr

end
