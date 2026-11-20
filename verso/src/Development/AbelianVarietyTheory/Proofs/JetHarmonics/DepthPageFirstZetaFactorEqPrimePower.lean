import Mathlib
import Development.AutomorphicArithmetic.CMTraceForms.ProdPrimeFactorsPowCeilPadicValNatMulEqPow
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.ScalarOfRun

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ceil_toNat (x : ℝ) : ⌈x⌉.toNat = ⌈x⌉₊ := rfl

/- English proof (translation)
Apply `IsFractionRing.injective (𝓞 D.host.E) D.host.E` to reduce the goal to its premises. Conclude with `barE_eq_conj D (EX.piG i)`.
-/
theorem barE_eq_piBarO {D : D7} (EX : ErrX D) (i : Fin 2) : barE D (EX.piG i) = piBarO EX i := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  exact barE_eq_conj D (EX.piG i)

/- English proof (translation)
Unfold `DepPage.cP`. Rewrite using `[if_pos (show (depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).IsRam p from Or.inl hp)]`. Use `show ⌈GlobalTheory.RunDepth.vdOf D p * _⌉.toNat = _`. Rewrite using `[GlobalTheory.RunDepth.vdOf, if_pos hp]`.
-/
theorem cP_of_mem_small (D : D7) (Tn : ℕ+) (N p : ℕ) (hp : p ∈ D.host.small) :
    (depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).cP N p = ⌈(padicValNat p D.host.QS : ℝ) * (N : ℝ)⌉.toNat := by
  unfold DepPage.cP
  rw [if_pos (show (depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).IsRam p from Or.inl hp)]
  show ⌈GlobalTheory.RunDepth.vdOf D p * _⌉.toNat = _
  rw [GlobalTheory.RunDepth.vdOf, if_pos hp]

/- English proof (translation)
Unfold `DepPage.cP`. Rewrite using `[if_pos hr, ceil_toNat]`. Use `show ⌈GlobalTheory.RunDepth.vdOf D p * _⌉₊ = _`. Rewrite using `[GlobalTheory.RunDepth.vdOf, if_neg hp, Formalism.MainNotions.DIV.Cons.cHalf]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cP_of_isRam_of_notMem_small (D : D7) (Tn : ℕ+) {j : ℕ} (w : WeightFamilies.Wt D j) (p : ℕ) (hp : p ∉ D.host.small)
    (hr : (depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).IsRam p) :
    (depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).cP (WeightAlgebra.DF w) p = Formalism.MainNotions.DIV.Cons.cHalf w := by
  unfold DepPage.cP
  rw [if_pos hr, ceil_toNat]
  show ⌈GlobalTheory.RunDepth.vdOf D p * _⌉₊ = _
  rw [GlobalTheory.RunDepth.vdOf, if_neg hp, Formalism.MainNotions.DIV.Cons.cHalf]
  congr 1; ring

/- English proof (translation)
Establish `hq` using `fun w => cP_of_isRam_of_notMem_small D Tn (j := j) w D.host.q D.host.q_notMem_small (Or.inr (Or.inl rfl))`. Establish `hd` using `fun w => cP_of_isRam_of_notMem_small D Tn (j := j) w D.host.d D.host.d_notMem_small (Or.inr (Or.inr rfl))`. Establish `hS` using `UpperTheory.prod_primeFactors_pow_ceil_padicValNat_mul_eq_pow D.host.QS Tn (WeightAlgebra.DF wL) (WeightAlgebra.DF wF) D.host.QS_pos.ne'`. Unfold `pPow c2`. Rewrite using `[← hS]`.

Use `conv_rhs => enter [1, 2]`. Rewrite using `[← hq wL, ← hq wF]`. Use `conv_rhs => enter [2]`. Rewrite using `[← hd wL, ← hd wF]`. Unfold `DepPage.Z1`.

Use `congr 2`. Use `Finset.prod_congr rfl fun p hp => ?_` and prove the remaining obligations. Establish `hp' : p ∈ D.host.small` using `(Finset.mem_filter.1 hp).1`. Rewrite using `[cP_of_mem_small D Tn _ p hp', cP_of_mem_small D Tn _ p hp']`. Both sides reduce to the same expression.
-/
theorem depth_page_first_zeta_factor_eq_prime_power (D : D7) (Tn : ℕ+) {j : ℕ} (wL wF : WeightFamilies.Wt D j) :
    (depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).Z1 (WeightAlgebra.DF wL) (WeightAlgebra.DF wF) =
      pPow D (Tn * c2 D wL + c2 D wF) (Tn * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF)
        (Tn * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF) := by
  have hq := fun w => cP_of_isRam_of_notMem_small D Tn (j := j) w D.host.q D.host.q_notMem_small (Or.inr (Or.inl rfl))
  have hd := fun w => cP_of_isRam_of_notMem_small D Tn (j := j) w D.host.d D.host.d_notMem_small (Or.inr (Or.inr rfl))
  have hS := UpperTheory.prod_primeFactors_pow_ceil_padicValNat_mul_eq_pow D.host.QS Tn (WeightAlgebra.DF wL) (WeightAlgebra.DF wF) D.host.QS_pos.ne'
  unfold pPow c2
  rw [← hS]
  conv_rhs => enter [1, 2]; rw [← hq wL, ← hq wF]
  conv_rhs => enter [2]; rw [← hd wL, ← hd wF]
  unfold DepPage.Z1
  congr 2
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp' : p ∈ D.host.small := (Finset.mem_filter.1 hp).1
  rw [cP_of_mem_small D Tn _ p hp', cP_of_mem_small D Tn _ p hp']
  rfl

/- English proof (translation)
Introduce `D L Pm Tp hK T h hinj EX j hj hE K _ _ _ φ hφ`. Establish `hM : LawsM T.toCore` using `h.toLawsCore.toLawsM`. Set `ψ : 𝓞 T.Q.c.F →+* K` to `φ.comp (algebraMap (𝓞 T.Q.c.F) T.Q.c.F)`. Establish `hψ : ∀ x, algebraMap (𝓞 D.host.E) K x = ψ (iE D hinj (recB h.toLawsCore) x)` using `hφ`. Set `Tn : ℕ+` to `⟨Tp.TO, GlobalTheory.RunDepth.TO_pos Tp⟩`.

Establish `hnn : nnKAt (H` using `T.Q.H) (LL := K) (GlobalTheory.RunDepth.depOf T.toCore EX Tp hK) j = ψ (nnW (recB h.toLawsCore) hinj EX (kaR Tp hK j)) := by`. Use `letI : StarRing (𝓞 D.host.E) := starRingOfComm`. Use `(nnKAt_depDataOf T.toCore EX _ _ _ _ _ _ _ hM hE j).trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ (map_prod ψ _ _).symm` and prove the remaining obligations. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[barE_eq_piBarO, hψ, hψ]`. Conclude with `((map_mul ψ _ _).trans (congrArg₂ (· * ·) (map_pow ψ _ _) (map_pow ψ _ _))).symm`. Establish `hL` using `GlobalTheory.WeightExponents.DF_wtA hM.pins hj (lR Tp hK j)`. Establish `hF` using `GlobalTheory.WeightExponents.DF_wtA hM.pins hj (fR Tp hK j)`. Establish `hn : (fR Tp hK j).n = 8 * D.R.f * D.R.r + 4` using `Tp.nP_eq`.

Use `show nnKAt (H := T.Q.H) (LL := K) (GlobalTheory.RunDepth.depOf T.toCore EX Tp hK) j * (((D.host.g 0 * D.host.g 1 : ℕ) : K) ^ (D.R.f * D.R.r * (8 * D.R.f * D.R.r + 4)) * (((depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).Z1 (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA (lR Tp hK j))) (Formal …`. Rewrite using `[hnn, hL, hF, depth_page_first_zeta_factor_eq_prime_power, ← hn, ← Nat.cast_pow, ← Nat.cast_mul, ← map_natCast ψ, ← map_mul]`. Both sides reduce to the same expression.
-/
theorem sigAt_eq_sigRec : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ), InR D j → HalfEX T.toCore EX → ∀ (K : Type) [Field K] [NumberField K] [Algebra (𝓞 D.host.E) K] (φ : T.Q.c.F →+* K), (∀ x : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) K x = φ ((iE D hinj (recB h.toLawsCore) x : 𝓞 T.Q.c.F) : T.Q.c.F)) → sigAt (Dw := T.Q.Dw j) (H := T.Q.H) (LL := K) (GlobalTheory.RunDepth.depOf T.toCore EX Tp hK) j = φ ((sigRec (recB h.toLawsCore) hinj EX (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO : 𝓞 T.Q.c.F) : T.Q.c.F) := by
  intro D L Pm Tp hK T h hinj EX j hj hE K _ _ _ φ hφ
  have hM : LawsM T.toCore := h.toLawsCore.toLawsM
  let ψ : 𝓞 T.Q.c.F →+* K := φ.comp (algebraMap (𝓞 T.Q.c.F) T.Q.c.F)
  have hψ : ∀ x, algebraMap (𝓞 D.host.E) K x = ψ (iE D hinj (recB h.toLawsCore) x) := hφ
  let Tn : ℕ+ := ⟨Tp.TO, GlobalTheory.RunDepth.TO_pos Tp⟩
  have hnn : nnKAt (H := T.Q.H) (LL := K) (GlobalTheory.RunDepth.depOf T.toCore EX Tp hK) j =
      ψ (nnW (recB h.toLawsCore) hinj EX (kaR Tp hK j)) := by
    letI : StarRing (𝓞 D.host.E) := starRingOfComm
    refine (nnKAt_depDataOf T.toCore EX _ _ _ _ _ _ _ hM hE j).trans ?_
    refine Eq.trans ?_ (map_prod ψ _ _).symm
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [barE_eq_piBarO, hψ, hψ]
    exact ((map_mul ψ _ _).trans (congrArg₂ (· * ·) (map_pow ψ _ _) (map_pow ψ _ _))).symm
  have hL := GlobalTheory.WeightExponents.DF_wtA hM.pins hj (lR Tp hK j)
  have hF := GlobalTheory.WeightExponents.DF_wtA hM.pins hj (fR Tp hK j)
  have hn : (fR Tp hK j).n = 8 * D.R.f * D.R.r + 4 := Tp.nP_eq
  show nnKAt (H := T.Q.H) (LL := K) (GlobalTheory.RunDepth.depOf T.toCore EX Tp hK) j *
      (((D.host.g 0 * D.host.g 1 : ℕ) : K) ^ (D.R.f * D.R.r * (8 * D.R.f * D.R.r + 4)) *
        (((depPageOf D Tn (GlobalTheory.RunDepth.vdOf D)).Z1 (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA (lR Tp hK j)))
          (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA (fR Tp hK j))) : ℕ) : K)) =
      ψ (sigRec (recB h.toLawsCore) hinj EX (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO)
  rw [hnn, hL, hF, depth_page_first_zeta_factor_eq_prime_power, ← hn, ← Nat.cast_pow, ← Nat.cast_mul, ← map_natCast ψ, ← map_mul]
  rfl

end GlobalTheory.ScalarOfRun
