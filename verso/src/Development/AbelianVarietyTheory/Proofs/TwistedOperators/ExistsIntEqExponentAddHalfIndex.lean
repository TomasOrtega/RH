import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebra
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealPointUnitaryWithComponents
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.SplitParity

/- English proof (translation)
Take `⟨δ, b, -, hb0, hb1, -⟩` from `GlobalTheory.QuadNormBase.exists_basis F E σ hr hσ hne`. Set `B` to `Algebra.TensorProduct.basis R b`. Establish `hB : ∀ i, B i = 1 ⊗ₜ[F] b i` using `fun i => Algebra.TensorProduct.basis_apply b i`. Establish `h0 : B 0 = 1` using `by rw [hB, hb0]; rfl`. Establish `hs : ∀ (r : R) (e : E), sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e` using `fun r e => rfl`.

Establish `hz'` using `B.sum_repr z`. Rewrite `hz'` using `[Fin.sum_univ_two]`. Use `set x := B.repr z 0`. Use `set y := B.repr z 1`. Establish `e : sigR R σ (x • B 0 + y • B 1) = x • B 0 - y • B 1`.

Rewrite using `[map_add, hB, hB, TensorProduct.smul_tmul', TensorProduct.smul_tmul', hs, hs, hb1, hb0, map_one, TensorProduct.tmul_neg, sub_eq_add_neg]`. Rewrite `hz` using `[← hz', e]`. Establish `h2 : (2 * y) • B 1 = 0`. Establish `: x • B 0 - y • B 1 - (x • B 0 + y • B 1) = 0` using `by rw [hz, sub_self]`. Rewrite using `[two_mul, add_smul]`.

Take the linear combination `(-1 : R ⊗[F] E) * this`. Establish `h3 : 2 * y = 0`. Use `congrArg (fun w => B.repr w 1) h2` as an intermediate fact. Simplify using `using this`. Establish `h4 : y = 0`.

Establish `hu : (2 : R) * algebraMap F R (1 / 2) = 1`. Rewrite using `[← map_ofNat (algebraMap F R) 2, ← map_mul]`. Evaluate the numerical expressions. Combine the equalities or inequalities in the displayed calculation. Use `⟨x, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hz', h4, zero_smul, add_zero, h0, Algebra.algebraMap_eq_smul_one]`.
-/
theorem exists_eq_of_sigR_fixed {F E R : Type} [Field F] [CharZero F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (hr : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x)
    (z : R ⊗[F] E) (hz : sigR R σ z = z) : ∃ r : R, algebraMap R (R ⊗[F] E) r = z := by
  obtain ⟨δ, b, -, hb0, hb1, -⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ hr hσ hne
  let B := Algebra.TensorProduct.basis R b
  have hB : ∀ i, B i = 1 ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply b i
  have h0 : B 0 = 1 := by rw [hB, hb0]; rfl
  have hs : ∀ (r : R) (e : E), sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := fun r e => rfl
  have hz' := B.sum_repr z
  rw [Fin.sum_univ_two] at hz'
  set x := B.repr z 0
  set y := B.repr z 1
  have e : sigR R σ (x • B 0 + y • B 1) = x • B 0 - y • B 1 := by
    rw [map_add, hB, hB, TensorProduct.smul_tmul', TensorProduct.smul_tmul', hs, hs, hb1, hb0,
      map_one, TensorProduct.tmul_neg, sub_eq_add_neg]
  rw [← hz', e] at hz
  have h2 : (2 * y) • B 1 = 0 := by
    have : x • B 0 - y • B 1 - (x • B 0 + y • B 1) = 0 := by rw [hz, sub_self]
    rw [two_mul, add_smul]
    linear_combination (-1 : R ⊗[F] E) * this
  have h3 : 2 * y = 0 := by
    have := congrArg (fun w => B.repr w 1) h2
    simpa using this
  have h4 : y = 0 := by
    have hu : (2 : R) * algebraMap F R (1 / 2) = 1 := by
      rw [← map_ofNat (algebraMap F R) 2, ← map_mul]; norm_num
    calc y = algebraMap F R (1 / 2) * (2 * y) := by linear_combination (-y) * hu
      _ = 0 := by rw [h3, mul_zero]
  refine ⟨x, ?_⟩
  rw [← hz', h4, zero_smul, add_zero, h0, Algebra.algebraMap_eq_smul_one]

end GlobalTheory.SplitParity

namespace GlobalTheory.SplitParity

/- English proof (translation)
Establish `hfx : ∀ z : AE D, cA D z = z → ∃ r : AF D.host.F, algebraMap (AF D.host.F) (AE D) r = z` using `fun z hz => exists_eq_of_sigR_fixed D.sp.cm.sig D.sp.cm.deg2 (fun x => star_star x) (GlobalTheory.VolHeckeCompare.exists_not_fixed D) z hz`. Take `⟨r, hr⟩` from `hfx _ hu`. Establish `hu' : cA D ((u⁻¹ : (AE D)ˣ) : AE D) = ((u⁻¹ : (AE D)ˣ) : AE D)`. Establish `h1 : (u : AE D) * cA D ((u⁻¹ : (AE D)ˣ) : AE D) = 1`. Rewrite using `[← hu, ← map_mul, Units.mul_inv, map_one]`.

Conclude with `(Units.inv_eq_of_mul_eq_one_right h1).symm`. Take `⟨r', hr'⟩` from `hfx _ hu'`. Establish `m1 : r * r' = 1` using `GlobalTheory.VolHeckeCompare.algebraMap_AE_injective D (by`. Rewrite using `[map_mul, hr, hr', Units.mul_inv, map_one])`. Use `⟨⟨r, r', m1, by rw [mul_comm]; exact m1⟩, Units.ext ?_⟩` and prove the remaining obligations.

Conclude with `hr`.
-/
theorem exists_idF_of_fixed (D : D7) (u : (AE D)ˣ) (hu : cA D (u : AE D) = u) : ∃ y, idF D y = u := by
  have hfx : ∀ z : AE D, cA D z = z → ∃ r : AF D.host.F, algebraMap (AF D.host.F) (AE D) r = z := fun z hz =>
    exists_eq_of_sigR_fixed D.sp.cm.sig D.sp.cm.deg2 (fun x => star_star x)
      (GlobalTheory.VolHeckeCompare.exists_not_fixed D) z hz
  obtain ⟨r, hr⟩ := hfx _ hu
  have hu' : cA D ((u⁻¹ : (AE D)ˣ) : AE D) = ((u⁻¹ : (AE D)ˣ) : AE D) := by
    have h1 : (u : AE D) * cA D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 := by
      rw [← hu, ← map_mul, Units.mul_inv, map_one]
    exact (Units.inv_eq_of_mul_eq_one_right h1).symm
  obtain ⟨r', hr'⟩ := hfx _ hu'
  have m1 : r * r' = 1 := GlobalTheory.VolHeckeCompare.algebraMap_AE_injective D (by
    rw [map_mul, hr, hr', Units.mul_inv, map_one])
  refine ⟨⟨r, r', m1, by rw [mul_comm]; exact m1⟩, Units.ext ?_⟩
  exact hr

/- English proof (translation)
Introduce `D χ n τ a _ hr ha`. Take `⟨N, hN, ⟨θ, hθ⟩, hχ⟩` from `ha`. Take `⟨η, -, -, hη1, hη2⟩` from `GlobalTheory.WeilParts.exists_isEtaTilde_unramified D`. Take `⟨N1, hN1, -, hηx⟩` from `hη2 τ`. Take `⟨σ, h⟩` from `GlobalTheory.RealLineAt.exists_inverse_chart hθ`.

Take `⟨e, -, e1, e2⟩` from `GlobalTheory.SplitCharExp.exists_real_hom h`. Use `set w : D.what₂.Tau → ℂ := Pi.mulSingle τ (-1) with hw`. Establish `wτ : w τ = -1` using `by simp [w]`. Establish `wo : ∀ τ', τ' ≠ τ → w τ' = 1` using `fun τ' ht => by simp [w, Pi.mulSingle_eq_of_ne ht]`. Establish `ww : w * w = 1`.

Use function extensionality and compare the values at `τ'`. Distinguish the cases in `ht : τ' = τ`. Substitute `ht` using the available equality. Simplify using `[wτ]`. Simplify using `[wo τ' ht]`.

Set `x : (AE D)ˣ` to `⟨e w, e w, by rw [← map_mul, ww, map_one], by rw [← map_mul, ww, map_one]⟩`. Establish `x1 : finPart D (x : AE D) = 1` using `e1 w`. Establish `x2 : ∀ τ', θ τ' (infPart D (x : AE D)) = w τ'` using `e2 w`. Establish `xτ : θ τ (infPart D (x : AE D)) = -1` using `by rw [x2, wτ]`. Establish `xo : ∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1` using `fun τ' ht => by rw [x2, wo τ' ht]`.

Establish `hcx : ((χ x : Circle) : ℂ) = (-1 : ℂ) ^ N` using `by rw [hχ θ hθ x x1 xo, xτ]; simp`. Establish `hN1' : N1 = 1`. Establish `: (N1 : ℚ) = 1` using `by rw [hN1]; norm_num`. Conclude with `this` after adjusting the coercions. Establish `hηc : ((η x : Circle) : ℂ) = -1` using `by rw [hηx θ hθ x x1 xo, xτ, hN1']; simp`.

Establish `hfix : cA D (x : AE D) = x`. Use `GlobalTheory.SplitCharExp.ext_of_chart h ?_ fun τ' => ?_` and prove the remaining obligations. Establish `e3 : finPart D (cA D (x : AE D)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D))` using `GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig (x : AE D)`. Rewrite using `[e3, x1, RingHom.map_one]`. Rewrite using `[GlobalTheory.FockCompare.comp_cA hθ, x2]`.

Distinguish the cases in `ht : τ' = τ`. Rewrite using `[ht, wτ]`. Simplify using the standard rewrite rules. Rewrite using `[wo τ' ht]`. Simplify using the standard rewrite rules.

Take `⟨y, hy⟩` from `exists_idF_of_fixed D x hfix`. Take `⟨⟨ε, hε⟩, hrχ⟩` from `hr`. Establish `c1` using `hrχ ε hε y`. Establish `c2` using `hη1.2 ε hε y`. Rewrite `c1`, `c2` using `[hy]`.

Establish `c2' : ((ε y : Circle) : ℂ) = -1` using `by rw [← hηc, c2, pow_one]`. Establish `c1' : ((χ x : Circle) : ℂ) = (-1 : ℂ) ^ n` using `by rw [c1, Circle.coe_pow, c2']`. Establish `hE : (-1 : ℂ) ^ N = (-1 : ℂ) ^ (n : ℤ)` using `by rw [← hcx, c1', zpow_natCast]`. Establish `hP : (-1 : ℂ) ^ (N + (n : ℤ)) = 1`. Rewrite using `[zpow_add₀ (by norm_num), hE, ← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; norm_num`.

Break down `Int.even_or_odd (N + (n : ℤ)) with ⟨k, hk⟩ | ho` into its components or cases. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `: ((N + (n : ℤ) : ℤ) : ℚ) = ((k + k : ℤ) : ℚ)` using `by rw [hk]`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite `hP` using `[ho.neg_one_zpow]`. Evaluate the numerical expressions using `at hP`.
-/
theorem exists_int_add_half : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ) (τ : D.what₂.Tau) (a : ℚ),
    IsHeckeChar D χ → ResEta D χ n → HasInfExp D χ τ a → ∃ e : ℤ, (e : ℚ) = a + (n : ℚ) / 2 := by
  intro D χ n τ a _ hr ha
  classical
  obtain ⟨N, hN, ⟨θ, hθ⟩, hχ⟩ := ha
  obtain ⟨η, -, -, hη1, hη2⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨N1, hN1, -, hηx⟩ := hη2 τ
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, -, e1, e2⟩ := GlobalTheory.SplitCharExp.exists_real_hom h
  set w : D.what₂.Tau → ℂ := Pi.mulSingle τ (-1) with hw
  have wτ : w τ = -1 := by simp [w]
  have wo : ∀ τ', τ' ≠ τ → w τ' = 1 := fun τ' ht => by simp [w, Pi.mulSingle_eq_of_ne ht]
  have ww : w * w = 1 := by
    funext τ'
    by_cases ht : τ' = τ
    · subst ht; simp [wτ]
    · simp [wo τ' ht]
  let x : (AE D)ˣ := ⟨e w, e w, by rw [← map_mul, ww, map_one], by rw [← map_mul, ww, map_one]⟩
  have x1 : finPart D (x : AE D) = 1 := e1 w
  have x2 : ∀ τ', θ τ' (infPart D (x : AE D)) = w τ' := e2 w
  have xτ : θ τ (infPart D (x : AE D)) = -1 := by rw [x2, wτ]
  have xo : ∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1 := fun τ' ht => by rw [x2, wo τ' ht]
  have hcx : ((χ x : Circle) : ℂ) = (-1 : ℂ) ^ N := by rw [hχ θ hθ x x1 xo, xτ]; simp
  have hN1' : N1 = 1 := by
    have : (N1 : ℚ) = 1 := by rw [hN1]; norm_num
    exact_mod_cast this
  have hηc : ((η x : Circle) : ℂ) = -1 := by rw [hηx θ hθ x x1 xo, xτ, hN1']; simp
  have hfix : cA D (x : AE D) = x := by
    refine GlobalTheory.SplitCharExp.ext_of_chart h ?_ fun τ' => ?_
    · have e3 : finPart D (cA D (x : AE D)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) :=
        GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig (x : AE D)
      rw [e3, x1, RingHom.map_one]
    · rw [GlobalTheory.FockCompare.comp_cA hθ, x2]
      by_cases ht : τ' = τ
      · rw [ht, wτ]; simp
      · rw [wo τ' ht]; simp
  obtain ⟨y, hy⟩ := exists_idF_of_fixed D x hfix
  obtain ⟨⟨ε, hε⟩, hrχ⟩ := hr
  have c1 := hrχ ε hε y
  have c2 := hη1.2 ε hε y
  rw [hy] at c1 c2
  have c2' : ((ε y : Circle) : ℂ) = -1 := by rw [← hηc, c2, pow_one]
  have c1' : ((χ x : Circle) : ℂ) = (-1 : ℂ) ^ n := by rw [c1, Circle.coe_pow, c2']
  have hE : (-1 : ℂ) ^ N = (-1 : ℂ) ^ (n : ℤ) := by rw [← hcx, c1', zpow_natCast]
  have hP : (-1 : ℂ) ^ (N + (n : ℤ)) = 1 := by
    rw [zpow_add₀ (by norm_num), hE, ← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; norm_num
  rcases Int.even_or_odd (N + (n : ℤ)) with ⟨k, hk⟩ | ho
  · refine ⟨k, ?_⟩
    have : ((N + (n : ℤ) : ℤ) : ℚ) = ((k + k : ℤ) : ℚ) := by rw [hk]
    push_cast at this
    linarith
  · rw [ho.neg_one_zpow] at hP
    norm_num at hP

end GlobalTheory.SplitParity
