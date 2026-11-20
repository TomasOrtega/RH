import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqProdBlockDetPolyPowMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory.FieldPolyZ

open GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT Formalism.L2.LamCM GlobalTheory.LamT.FieldPoly

/- English proof (translation)
Establish `hB : Out.SecBaseChangeSt` using `GlobalTheory.lawsFieldsSeparately.2.1`. Take `⟨A, _, _, π, X, hred, hX, hA⟩` from `exists_genericRing c.F K (E →+* ℂ) Dw.mult`. Take `⟨u₀, hu₀⟩` from `GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c K A π y`. Take `⟨u, hu, -⟩` from `GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c A u₀ (fun b => (X b).transpose) 1 (fun b => by rw [Matrix.det_transpose]; exact hX b)`. Take `⟨P, N, hP⟩` from `hA (evR Xo c F u)`.

Use `⟨P, N, fun S _ _ φ z z' Y hY hz hz' => ?_⟩` and prove the remaining obligations. Take `⟨k, hkπ, hkX, hk⟩` from `hP S φ Y hY`. Take `⟨w, hw⟩` from `GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c A S k u₀`. Establish `hw' : FrMap (k.comp π) y w` using `frMap_trans (Xo := Xo) (c := c) _ _ _ π k y u₀ w hu₀ hw`. Rewrite `hw'` using `[hkπ]`.

Establish `hwz : w = z` using `(GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c K S φ y).1 w z hw' hz`. Substitute `hwz` using the available equality. Establish `hm : FrMap k u z'`. Use `(GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c A S k u₀ u w z' _ _ hu hw).2 ?_` and prove the remaining obligations. Establish `e : (fun τ => ((X τ).transpose).map k) = fun b => (Y b).transpose`.

Use function extensionality and compare the values at `fun b => by rw [Matrix.transpose_map, hkX]`. Rewrite using `[e, Units.val_one, map_one]`. Conclude with `hz'`. Rewrite using `[GlobalTheory.FrameEval.evR_frMap_of_isReduced E H Dw l Xo c F hF k u z' hm]`. Conclude with `hk`.
-/
theorem exists_poly_div_det_of_natural (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K)
    (F : Rul Xo c) (hF : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) F) :
    ∃ (P : MvPolynomial (FrVar Dw.mult) K) (N : ℕ), ∀ (S : Type) [CommRing S] [Algebra c.F S] (φ : K →ₐ[c.F] S)
      (z z' : FrPt Xo c S) (Y : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S)),
      (∀ b, IsUnit (Y b).det) → FrMap φ y z → FrChg (fun b => (Y b).transpose) 1 z z' →
      (∏ b, (Y b).det) ^ N * evR Xo c F z' = evalFr (MvPolynomial.map φ.toRingHom P) Y := by
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨A, _, _, π, X, hred, hX, hA⟩ := exists_genericRing c.F K (E →+* ℂ) Dw.mult
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c K A π y
  obtain ⟨u, hu, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c A u₀ (fun b => (X b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact hX b)
  obtain ⟨P, N, hP⟩ := hA (evR Xo c F u)
  refine ⟨P, N, fun S _ _ φ z z' Y hY hz hz' => ?_⟩
  obtain ⟨k, hkπ, hkX, hk⟩ := hP S φ Y hY
  obtain ⟨w, hw⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c A S k u₀
  have hw' : FrMap (k.comp π) y w := frMap_trans (Xo := Xo) (c := c) _ _ _ π k y u₀ w hu₀ hw
  rw [hkπ] at hw'
  have hwz : w = z := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c K S φ y).1 w z hw' hz
  subst hwz
  have hm : FrMap k u z' := by
    refine (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c A S k u₀ u w z' _ _ hu hw).2 ?_
    have e : (fun τ => ((X τ).transpose).map k) = fun b => (Y b).transpose :=
      funext fun b => by rw [Matrix.transpose_map, hkX]
    rw [e, Units.val_one, map_one]
    exact hz'
  rw [GlobalTheory.FrameEval.evR_frMap_of_isReduced E H Dw l Xo c F hF k u z' hm]
  exact hk

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c K _ _ y₀ e k a he0 hea F hF`. Establish `: CharZero K` using `charZero_of_injective_algebraMap (algebraMap c.F K).injective`. Establish `: Infinite K` using `Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective`. Establish `hS : Out.SecBaseChangeSt` using `GlobalTheory.lawsFieldsSeparately.2.1`. Take `⟨P, N, hP⟩` from `exists_poly_div_det_of_natural E H Dw l Xo c K y₀ F hF.1`.

Establish `hrefl : FrMap (AlgHom.id c.F K) y₀ y₀` using `GlobalTheory.Frames.frMapUniq_refl y₀`. Use `set M : ℕ := ∑ b, k b with hM`. Establish `hkM : ∀ b, k b ≤ M` using `fun b => Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)`. Use `set P' : MvPolynomial (FrVar Dw.mult) K := (∏ b, blockDetPoly K Dw.mult b) ^ M * P with hP'`. Establish `hevD : ∀ Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K, evalFr (∏ b, blockDetPoly K Dw.mult b) Y = ∏ b, (Y b).det` using `fun Y => by`.

Simplify using `only [← evalFr_blockDetPoly Dw.mult _ Y]`. Simplify using `only [evalFr, map_prod]`. Establish `hA : ∀ (z' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K), (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y₀ z' → (∏ b, (Y b).det) ^ (M + N) * evR Xo c F z' = evalFr P' Y`. Introduce `z' Y hY h`. Establish `h1` using `hP K (AlgHom.id c.F K) y₀ z' Y (fun b => (hY b).isUnit) hrefl h`.

Establish `h2 : MvPolynomial.map (AlgHom.id c.F K).toRingHom P = P` using `MvPolynomial.map_id P`. Rewrite `h1` using `[h2]`. Establish `h3 : evalFr P' Y = evalFr (∏ b, blockDetPoly K Dw.mult b) Y ^ M * evalFr P Y`. Simplify using `only [hP', evalFr, map_mul, map_pow]`. Rewrite using `[h3, hevD, ← h1, pow_add, mul_assoc]`.

Establish `hB : ∀ (z₁ z₂ : FrPt Xo c K) (T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K), (∀ b, (T b).BlockTriangular id) → (∀ b, (T b).det ≠ 0) → FrChg (fun b => (T b).transpose) 1 z₁ z₂ → (∏ b, ∏ i, T b i i ^ k b) * evR Xo c F z₂ = (∏ b, ∏ i, T b i i ^ a b i) * evR Xo c F …`. Introduce `z₁ z₂ T hT hd h`. Establish `hne : ∀ b i, T b i i ≠ 0`. Introduce `b i`. Establish `h1` using `hd b`.

Rewrite `h1` using `[Matrix.det_of_isUpperTriangular (hT b)]`. Conclude with `(Finset.prod_ne_zero_iff.1 h1) i (Finset.mem_univ i)`. Set `t : Formalism.L2.Pj.Ix Dw → Kˣ` to `fun o => match o with`. Consider the case `none => 1`. Consider the case `some x => Units.mk0 (T x.1 x.2 x.2) (hne x.1 x.2)`.

Establish `hb : FrBor t z₁ z₂`. Use `((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c K z₁ z₂ z₂).1 t).2 ⟨fun b => (T b).transpose, fun τ i j hij => ?_, fun τ i => rfl, h⟩` and prove the remaining obligations. Conclude with `hT τ hij`. Establish `hw` using `GlobalTheory.evR_frBor_of_mem_secZ hS Xo c e hF K t z₁ z₂ hb`. Establish `key : ∀ b i, T b i i ^ k b * ((Units.mk0 (T b i i) (hne b i) ^ e (some ⟨b, i⟩) : Kˣ) : K) = T b i i ^ a b i`.

Introduce `b i`. Rewrite using `[Units.val_zpow_eq_zpow_val, Units.val_mk0, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hne b i), ← hea b i, add_comm]`. Establish `hc : (∏ b, ∏ i, T b i i ^ k b) * ((∏ o, t o ^ e o : Kˣ) : K) = ∏ b, ∏ i, T b i i ^ a b i`. Rewrite using `[Units.coe_prod, Fintype.prod_option, Fintype.prod_sigma]`. Simplify using `only [t, he0, zpow_zero, Units.val_one, _root_.one_mul]`.

Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `key b i`.

Rewrite using `[hw, ← _root_.mul_assoc, hc]`. Establish `hP'tr : ∀ (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K) (b : E →+* ℂ) (t : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K), (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id → evalFr P' (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i + (M + N - k …`. Introduce `X b t hX ht htri`. Set `T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K` to `Function.update (fun _ => 1) b t`. Establish `hTb : T b = t` using `Function.update_self ..`.

Establish `hTo : ∀ b', b' ≠ b → T b' = 1` using `fun b' h => Function.update_of_ne h ..`. Establish `hTtri : ∀ b', (T b').BlockTriangular id`. Introduce `b'`. Distinguish the cases in `h : b' = b`. Substitute `h` using the available equality.

Rewrite using `[hTb]`. Conclude with `htri`. Rewrite using `[hTo b' h]`. Conclude with `Matrix.blockTriangular_one`. Establish `hTd : ∀ b', (T b').det ≠ 0`.

Introduce `b'`. Distinguish the cases in `h : b' = b`. Substitute `h` using the available equality. Rewrite using `[hTb]`. Conclude with `ht`.

Rewrite using `[hTo b' h]`. Simplify using the standard rewrite rules. Establish `hup : Function.update X b (X b * t) = fun b' => X b' * T b'`. Use function extensionality and compare the values at `b'`. Distinguish the cases in `h : b' = b`.

Substitute `h` using the available equality. Rewrite using `[hTb, Function.update_self]`. Rewrite using `[hTo b' h, Function.update_of_ne h, _root_.mul_one]`. Take `⟨z₁, h₁, -⟩` from `GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (X b).transpose) 1 (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)`. Take `⟨z₂, h₂, -⟩` from `GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1 (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)`.

Rewrite `h₁`, `h₂` using `[Units.val_one]`. Establish `h₃` using `(GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y₀ z₁ z₂).2 _ _ _ _ h₁ h₂`. Simplify using `only [← Matrix.transpose_mul, _root_.mul_one] at h₃`. Establish `e₁` using `hA z₁ X hX h₁`. Establish `e₂` using `hA z₂ (fun b' => X b' * T b') (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃`.

Establish `e₃` using `hB z₁ z₂ T hTtri hTd h₂`. Establish `p₁ : ∀ f : (E →+* ℂ) → ℕ, (∏ b', ∏ i, T b' i i ^ f b') = ∏ i, t i i ^ f b`. Introduce `f`. Rewrite using `[Finset.prod_eq_single b, hTb]`. Introduce `b' _ h`.

Rewrite using `[hTo b' h]`. Simplify using the standard rewrite rules. Introduce `h`. Conclude with `absurd (Finset.mem_univ b) h`. Establish `p₁' : (∏ b', ∏ i, T b' i i ^ a b' i) = ∏ i, t i i ^ a b i`.

Rewrite using `[Finset.prod_eq_single b, hTb]`. Introduce `b' _ h`. Rewrite using `[hTo b' h]`. Simplify using the standard rewrite rules. Introduce `h`.

Conclude with `absurd (Finset.mem_univ b) h`. Establish `p₂ : (∏ b', (X b' * T b').det) = (∏ b', (X b').det) * ∏ i, t i i`. Simplify using `only [Matrix.det_mul, Finset.prod_mul_distrib]`. Use `congr 1`. Rewrite using `[Finset.prod_eq_single b, hTb, Matrix.det_of_isUpperTriangular htri]`.

Introduce `b' _ h`. Rewrite using `[hTo b' h]`. Simplify using the standard rewrite rules. Introduce `h`. Conclude with `absurd (Finset.mem_univ b) h`.

Rewrite `e₃` using `[p₁ k, p₁']`. Establish `hti : ∀ i, t i i ≠ 0`. Introduce `i`. Establish `h1` using `ht`. Rewrite `h1` using `[Matrix.det_of_isUpperTriangular htri]`.

Conclude with `(Finset.prod_ne_zero_iff.1 h1) i (Finset.mem_univ i)`. Establish `hk0 : (∏ i, t i i ^ k b) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hti i)`. Establish `hL : (∏ i, t i i ^ k b) * ∏ i, t i i ^ (a b i + (M + N - k b)) = (∏ i, t i i) ^ (M + N) * ∏ i, t i i ^ a b i`. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← pow_add, ← pow_add]`. Use `congr 1`. Use `hkM b` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[hup, ← e₂, ← e₁, p₂]`.

Apply `mul_left_cancel₀ hk0` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree. Use `_ = ((∏ b', (X b').det) ^ (M + N) * (∏ i, t i i) ^ (M + N)) * ((∏ i, t i i ^ a b i) * evR Xo c F z₁) := by`. Rewrite using `[e₃]`.

Use `_ = ((∏ i, t i i) ^ (M + N) * ∏ i, t i i ^ a b i) * ((∏ b', (X b').det) ^ (M + N) * evR Xo c F z₁) := by`. Expand and normalize the polynomial expressions, which then agree. Use `_ = (∏ i, t i i ^ k b) * ((∏ i, t i i ^ (a b i + (M + N - k b))) * ((∏ b', (X b').det) ^ (M + N) * evR Xo c F z₁)) := by`. Rewrite using `[← hL]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨G, hG⟩` from `exists_eq_prod_blockDetPoly_pow_mul K (E →+* ℂ) Dw.mult a _ (fun b => M + N - k b) rfl P' (fun X b t hX ht htri => hP'tr X b t hX ht htri)`. Establish `hGY : ∀ (z' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K), (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y₀ z' → (∏ b, (Y b).det ^ k b) * evR Xo c F z' = evalFr G Y`. Introduce `z' Y hY h`. Establish `h1` using `hA z' Y hY h`. Establish `h2 : evalFr P' Y = (∏ b, (Y b).det ^ (M + N - k b)) * evalFr G Y`.

Rewrite using `[hG]`. Simplify using `only [← evalFr_blockDetPoly Dw.mult _ Y]`. Simplify using `only [evalFr, map_mul, map_prod, map_pow]`. Establish `hne : (∏ b, (Y b).det ^ (M + N - k b)) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hY b)`. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises.

Rewrite using `[← h2, ← h1, ← _root_.mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_pow]`. Use `congr 1`. Use `Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_add]`. Use `congr 1`.

Use `hkM b` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hGhom : G.IsHomogeneous (∑ b, ∑ i, a b i)`. Use `isHomogeneous_of_scaling G (∏ b, blockDetPoly K Dw.mult b) (fun h0 => ?_) _ (fun x hx => ?_)` and prove the remaining obligations. Establish `h1` using `hevD fun _ => 1`.

Rewrite `h1` using `[h0]`. Simplify using `[evalFr] at h1`. Set `X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K` to `fun b => Matrix.of fun i j => x ⟨b, (j, i)⟩`. Set `T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K` to `fun b => Matrix.diagonal fun _ => 2`. Establish `hX : ∀ b, (X b).det ≠ 0` using `fun b => by`.

Establish `h1 : (∏ b, (X b).det) ≠ 0` using `by rw [← hevD X]; exact hx`. Conclude with `(Finset.prod_ne_zero_iff.1 h1) b (Finset.mem_univ b)`. Establish `hTtri : ∀ b, (T b).BlockTriangular id` using `fun b => Matrix.blockTriangular_diagonal _`. Establish `hTd : ∀ b, (T b).det ≠ 0` using `fun b => by simp [T]`. Take `⟨z₁, h₁, -⟩` from `GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (X b).transpose) 1 (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)`.

Take `⟨z₂, h₂, -⟩` from `GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1 (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)`. Rewrite `h₁`, `h₂` using `[Units.val_one]`. Establish `h₃` using `(GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y₀ z₁ z₂).2 _ _ _ _ h₁ h₂`. Simplify using `only [← Matrix.transpose_mul, _root_.mul_one] at h₃`. Establish `e₁` using `hGY z₁ X hX h₁`.

Establish `e₂` using `hGY z₂ (fun b' => X b' * T b') (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃`. Establish `e₃` using `hB z₁ z₂ T hTtri hTd h₂`. Establish `p₁ : (∏ b, ∏ i, T b i i ^ a b i) = 2 ^ (∑ b, ∑ i, a b i)`. Simplify using `only [T, Matrix.diagonal_apply_eq, Finset.prod_pow_eq_pow_sum]`. Establish `p₂ : evalFr G (fun b' => X b' * T b') = MvPolynomial.eval (fun v => 2 * x v) G`.

Unfold `evalFr`. Use `congr 2`. Use function extensionality and compare the values at `v`. Simplify using `only [T, Matrix.mul_diagonal, X, Matrix.of_apply]`. Conclude with `mul_comm _ _`.

Establish `p₃ : (∏ b, (X b * T b).det ^ k b) = (∏ b, (X b).det ^ k b) * ∏ b, ∏ i, T b i i ^ k b`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.det_mul, mul_pow, Matrix.det_of_isUpperTriangular (hTtri b), Finset.prod_pow]`. Establish `e₁' : MvPolynomial.eval x G = (∏ b, (X b).det ^ k b) * evR Xo c F z₁`.

Rewrite using `[e₁]`. Both sides reduce to the same expression. Rewrite using `[← p₂, ← e₂, p₃, _root_.mul_assoc, e₃, p₁, e₁']`. Expand and normalize the polynomial expressions, which then agree. Use `⟨G, hGhom, fun y' Y s hY h => ?_⟩` and prove the remaining obligations.

Establish `hYt : ∀ b, IsUnit ((Y b).transpose).det` using `fun b => by rw [Matrix.det_transpose]; exact (hY b).isUnit`. Take `⟨w₀, hw₀, -⟩` from `GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (Y b).transpose) 1 hYt`. Take `⟨w₁, hw₁, -⟩` from `GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K w₀ (fun _ => 1) s (fun _ => by simp)`. Establish `c1` using `(GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y₀ w₀ w₁).2 _ _ _ _ hw₀ hw₁`. Establish `ew : w₁ = y'`.

Use `(GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (Y b).transpose) s hYt).unique ?_ h` and prove the remaining obligations. Simplify using `using c1`. Substitute `ew` using the available equality. Set `t : Formalism.L2.Pj.Ix Dw → Kˣ` to `fun o => o.elim s (fun _ => 1)`. Establish `hb : FrBor t w₀ w₁` using `((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c K w₀ w₁ w₁).1 t).2 ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => by simp [t], hw₁⟩`.

Establish `hw` using `GlobalTheory.evR_frBor_of_mem_secZ hS Xo c e hF K t w₀ w₁ hb`. Establish `ht1 : ((∏ i, t i ^ e i : Kˣ) : K) = 1`. Simplify using `[t, Fintype.prod_option, he0]`. Rewrite using `[hw, ht1, _root_.one_mul]`. Rewrite `hw₀` using `[Units.val_one]`.

Conclude with `hGY w₀ Y hY hw₀`.
-/
theorem exists_isHomogeneous_secZ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y₀ : FrPt Xo c K) (e : Formalism.L2.Pj.Ix Dw → ℤ)
    (k : (E →+* ℂ) → ℕ) (a : ∀ b : E →+* ℂ, Fin (Dw.mult b) → ℕ), e none = 0 →
    (∀ (b : E →+* ℂ) (i : Fin (Dw.mult b)), e (some ⟨b, i⟩) + (k b : ℤ) = (a b i : ℤ)) →
    ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, ∃ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) K,
      G.IsHomogeneous (∑ b, ∑ i, a b i) ∧
      ∀ (y' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K) (s : Kˣ),
        (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : K) y₀ y' →
        (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y := by
  classical
  intro E _ _ _ H Dw l Xo c K _ _ y₀ e k a he0 hea F hF
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨P, N, hP⟩ := exists_poly_div_det_of_natural E H Dw l Xo c K y₀ F hF.1
  have hrefl : FrMap (AlgHom.id c.F K) y₀ y₀ := GlobalTheory.Frames.frMapUniq_refl y₀
  set M : ℕ := ∑ b, k b with hM
  have hkM : ∀ b, k b ≤ M := fun b =>
    Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
  set P' : MvPolynomial (FrVar Dw.mult) K := (∏ b, blockDetPoly K Dw.mult b) ^ M * P with hP'
  have hevD : ∀ Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K,
      evalFr (∏ b, blockDetPoly K Dw.mult b) Y = ∏ b, (Y b).det := fun Y => by
    simp only [← evalFr_blockDetPoly Dw.mult _ Y]
    simp only [evalFr, map_prod]

  have hA : ∀ (z' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y₀ z' →
      (∏ b, (Y b).det) ^ (M + N) * evR Xo c F z' = evalFr P' Y := by
    intro z' Y hY h
    have h1 := hP K (AlgHom.id c.F K) y₀ z' Y (fun b => (hY b).isUnit) hrefl h
    have h2 : MvPolynomial.map (AlgHom.id c.F K).toRingHom P = P := MvPolynomial.map_id P
    rw [h2] at h1
    have h3 : evalFr P' Y = evalFr (∏ b, blockDetPoly K Dw.mult b) Y ^ M * evalFr P Y := by
      simp only [hP', evalFr, map_mul, map_pow]
    rw [h3, hevD, ← h1, pow_add, mul_assoc]

  have hB : ∀ (z₁ z₂ : FrPt Xo c K) (T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      (∀ b, (T b).BlockTriangular id) → (∀ b, (T b).det ≠ 0) → FrChg (fun b => (T b).transpose) 1 z₁ z₂ →
      (∏ b, ∏ i, T b i i ^ k b) * evR Xo c F z₂ = (∏ b, ∏ i, T b i i ^ a b i) * evR Xo c F z₁ := by
    intro z₁ z₂ T hT hd h
    have hne : ∀ b i, T b i i ≠ 0 := by
      intro b i
      have h1 := hd b
      rw [Matrix.det_of_isUpperTriangular (hT b)] at h1
      exact (Finset.prod_ne_zero_iff.1 h1) i (Finset.mem_univ i)
    let t : Formalism.L2.Pj.Ix Dw → Kˣ := fun o => match o with
      | none => 1
      | some x => Units.mk0 (T x.1 x.2 x.2) (hne x.1 x.2)
    have hb : FrBor t z₁ z₂ := by
      refine ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c K z₁ z₂ z₂).1 t).2
        ⟨fun b => (T b).transpose, fun τ i j hij => ?_, fun τ i => rfl, h⟩
      exact hT τ hij
    have hw := GlobalTheory.evR_frBor_of_mem_secZ hS Xo c e hF K t z₁ z₂ hb
    have key : ∀ b i, T b i i ^ k b * ((Units.mk0 (T b i i) (hne b i) ^ e (some ⟨b, i⟩) : Kˣ) : K) =
        T b i i ^ a b i := by
      intro b i
      rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hne b i),
        ← hea b i, add_comm]
    have hc : (∏ b, ∏ i, T b i i ^ k b) * ((∏ o, t o ^ e o : Kˣ) : K) = ∏ b, ∏ i, T b i i ^ a b i := by
      rw [Units.coe_prod, Fintype.prod_option, Fintype.prod_sigma]
      simp only [t, he0, zpow_zero, Units.val_one, _root_.one_mul]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      exact key b i
    rw [hw, ← _root_.mul_assoc, hc]

  have hP'tr : ∀ (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K) (b : E →+* ℂ)
      (t : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id →
      evalFr P' (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i + (M + N - k b))) * evalFr P' X := by
    intro X b t hX ht htri
    let T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K := Function.update (fun _ => 1) b t
    have hTb : T b = t := Function.update_self ..
    have hTo : ∀ b', b' ≠ b → T b' = 1 := fun b' h => Function.update_of_ne h ..
    have hTtri : ∀ b', (T b').BlockTriangular id := by
      intro b'
      by_cases h : b' = b
      · subst h; rw [hTb]; exact htri
      · rw [hTo b' h]; exact Matrix.blockTriangular_one
    have hTd : ∀ b', (T b').det ≠ 0 := by
      intro b'
      by_cases h : b' = b
      · subst h; rw [hTb]; exact ht
      · rw [hTo b' h]; simp
    have hup : Function.update X b (X b * t) = fun b' => X b' * T b' := by
      funext b'
      by_cases h : b' = b
      · subst h; rw [hTb, Function.update_self]
      · rw [hTo b' h, Function.update_of_ne h, _root_.mul_one]
    obtain ⟨z₁, h₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (X b).transpose) 1
      (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)
    obtain ⟨z₂, h₂, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1
      (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)
    rw [Units.val_one] at h₁ h₂
    have h₃ := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y₀ z₁ z₂).2 _ _ _ _ h₁ h₂
    simp only [← Matrix.transpose_mul, _root_.mul_one] at h₃
    have e₁ := hA z₁ X hX h₁
    have e₂ := hA z₂ (fun b' => X b' * T b')
      (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃
    have e₃ := hB z₁ z₂ T hTtri hTd h₂
    have p₁ : ∀ f : (E →+* ℂ) → ℕ, (∏ b', ∏ i, T b' i i ^ f b') = ∏ i, t i i ^ f b := by
      intro f
      rw [Finset.prod_eq_single b, hTb]
      · intro b' _ h
        rw [hTo b' h]; simp
      · intro h; exact absurd (Finset.mem_univ b) h
    have p₁' : (∏ b', ∏ i, T b' i i ^ a b' i) = ∏ i, t i i ^ a b i := by
      rw [Finset.prod_eq_single b, hTb]
      · intro b' _ h
        rw [hTo b' h]; simp
      · intro h; exact absurd (Finset.mem_univ b) h
    have p₂ : (∏ b', (X b' * T b').det) = (∏ b', (X b').det) * ∏ i, t i i := by
      simp only [Matrix.det_mul, Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_eq_single b, hTb, Matrix.det_of_isUpperTriangular htri]
      · intro b' _ h
        rw [hTo b' h]; simp
      · intro h; exact absurd (Finset.mem_univ b) h
    rw [p₁ k, p₁'] at e₃
    have hti : ∀ i, t i i ≠ 0 := by
      intro i
      have h1 := ht
      rw [Matrix.det_of_isUpperTriangular htri] at h1
      exact (Finset.prod_ne_zero_iff.1 h1) i (Finset.mem_univ i)
    have hk0 : (∏ i, t i i ^ k b) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hti i)
    have hL : (∏ i, t i i ^ k b) * ∏ i, t i i ^ (a b i + (M + N - k b)) =
        (∏ i, t i i) ^ (M + N) * ∏ i, t i i ^ a b i := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_add, ← pow_add]
      congr 1
      have := hkM b
      omega
    rw [hup, ← e₂, ← e₁, p₂]
    apply mul_left_cancel₀ hk0
    calc (∏ i, t i i ^ k b) * (((∏ b', (X b').det) * ∏ i, t i i) ^ (M + N) * evR Xo c F z₂)
        = ((∏ b', (X b').det) ^ (M + N) * (∏ i, t i i) ^ (M + N)) * ((∏ i, t i i ^ k b) * evR Xo c F z₂) := by
          ring
      _ = ((∏ b', (X b').det) ^ (M + N) * (∏ i, t i i) ^ (M + N)) * ((∏ i, t i i ^ a b i) * evR Xo c F z₁) := by
          rw [e₃]
      _ = ((∏ i, t i i) ^ (M + N) * ∏ i, t i i ^ a b i) * ((∏ b', (X b').det) ^ (M + N) * evR Xo c F z₁) := by
          ring
      _ = (∏ i, t i i ^ k b) * ((∏ i, t i i ^ (a b i + (M + N - k b))) *
            ((∏ b', (X b').det) ^ (M + N) * evR Xo c F z₁)) := by
          rw [← hL]; ring

  obtain ⟨G, hG⟩ := exists_eq_prod_blockDetPoly_pow_mul K (E →+* ℂ) Dw.mult a _ (fun b => M + N - k b) rfl P'
    (fun X b t hX ht htri => hP'tr X b t hX ht htri)
  have hGY : ∀ (z' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y₀ z' →
      (∏ b, (Y b).det ^ k b) * evR Xo c F z' = evalFr G Y := by
    intro z' Y hY h
    have h1 := hA z' Y hY h
    have h2 : evalFr P' Y = (∏ b, (Y b).det ^ (M + N - k b)) * evalFr G Y := by
      rw [hG]
      simp only [← evalFr_blockDetPoly Dw.mult _ Y]
      simp only [evalFr, map_mul, map_prod, map_pow]
    have hne : (∏ b, (Y b).det ^ (M + N - k b)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hY b)
    apply mul_left_cancel₀ hne
    rw [← h2, ← h1, ← _root_.mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [← pow_add]
    congr 1
    have := hkM b
    omega

  have hGhom : G.IsHomogeneous (∑ b, ∑ i, a b i) := by
    refine isHomogeneous_of_scaling G (∏ b, blockDetPoly K Dw.mult b) (fun h0 => ?_) _ (fun x hx => ?_)
    · have h1 := hevD fun _ => 1
      rw [h0] at h1
      simp [evalFr] at h1
    · let X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K := fun b => Matrix.of fun i j => x ⟨b, (j, i)⟩
      let T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K := fun b => Matrix.diagonal fun _ => 2
      have hX : ∀ b, (X b).det ≠ 0 := fun b => by
        have h1 : (∏ b, (X b).det) ≠ 0 := by rw [← hevD X]; exact hx
        exact (Finset.prod_ne_zero_iff.1 h1) b (Finset.mem_univ b)
      have hTtri : ∀ b, (T b).BlockTriangular id := fun b => Matrix.blockTriangular_diagonal _
      have hTd : ∀ b, (T b).det ≠ 0 := fun b => by simp [T]
      obtain ⟨z₁, h₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (X b).transpose) 1
        (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)
      obtain ⟨z₂, h₂, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1
        (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)
      rw [Units.val_one] at h₁ h₂
      have h₃ := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y₀ z₁ z₂).2 _ _ _ _ h₁ h₂
      simp only [← Matrix.transpose_mul, _root_.mul_one] at h₃
      have e₁ := hGY z₁ X hX h₁
      have e₂ := hGY z₂ (fun b' => X b' * T b')
        (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃
      have e₃ := hB z₁ z₂ T hTtri hTd h₂
      have p₁ : (∏ b, ∏ i, T b i i ^ a b i) = 2 ^ (∑ b, ∑ i, a b i) := by
        simp only [T, Matrix.diagonal_apply_eq, Finset.prod_pow_eq_pow_sum]
      have p₂ : evalFr G (fun b' => X b' * T b') = MvPolynomial.eval (fun v => 2 * x v) G := by
        unfold evalFr
        congr 2
        funext v
        simp only [T, Matrix.mul_diagonal, X, Matrix.of_apply]
        exact mul_comm _ _
      have p₃ : (∏ b, (X b * T b).det ^ k b) = (∏ b, (X b).det ^ k b) * ∏ b, ∏ i, T b i i ^ k b := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun b _ => ?_
        rw [Matrix.det_mul, mul_pow, Matrix.det_of_isUpperTriangular (hTtri b), Finset.prod_pow]
      have e₁' : MvPolynomial.eval x G = (∏ b, (X b).det ^ k b) * evR Xo c F z₁ := by
        rw [e₁]; rfl
      rw [← p₂, ← e₂, p₃, _root_.mul_assoc, e₃, p₁, e₁']
      ring

  refine ⟨G, hGhom, fun y' Y s hY h => ?_⟩
  have hYt : ∀ b, IsUnit ((Y b).transpose).det := fun b => by rw [Matrix.det_transpose]; exact (hY b).isUnit
  obtain ⟨w₀, hw₀, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (Y b).transpose) 1 hYt
  obtain ⟨w₁, hw₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K w₀ (fun _ => 1) s (fun _ => by simp)
  have c1 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y₀ w₀ w₁).2 _ _ _ _ hw₀ hw₁
  have ew : w₁ = y' := by
    refine (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (Y b).transpose) s hYt).unique ?_ h
    simpa using c1
  subst ew
  let t : Formalism.L2.Pj.Ix Dw → Kˣ := fun o => o.elim s (fun _ => 1)
  have hb : FrBor t w₀ w₁ := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c K w₀ w₁ w₁).1 t).2
    ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => by simp [t], hw₁⟩
  have hw := GlobalTheory.evR_frBor_of_mem_secZ hS Xo c e hF K t w₀ w₁ hb
  have ht1 : ((∏ i, t i ^ e i : Kˣ) : K) = 1 := by
    simp [t, Fintype.prod_option, he0]
  rw [hw, ht1, _root_.one_mul]
  rw [Units.val_one] at hw₀
  exact hGY w₀ Y hY hw₀

end GlobalTheory.FieldPolyZ
