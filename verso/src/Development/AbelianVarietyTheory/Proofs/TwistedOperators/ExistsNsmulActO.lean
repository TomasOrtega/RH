import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepThetaDatumHalfEqSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitSupportedUnitaryComponent

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinear

open GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove

variable {D : D7} {S T : HSp D}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

/- English proof (translation)
Take `⟨M, hM, hMu⟩` from `GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.fg hT.fg`. Take `⟨K, hK, hKt⟩` from `GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS hT`. Take `⟨N, hN, hNm⟩` from `GlobalTheory.PlaceDatum.exists_den_mul (Formalism.L2.Herm.intAf D.host.F D.host.E) (fun z => GlobalTheory.PlaceDatum.exists_den_adele z) ((Formalism.L2.Theta.mt T h).map (toEAf D)) ((Formalism.L2.Theta.mt S g⁻¹).map (toEAf D))`. Use `⟨K * (N * M), Nat.mul_pos hK (Nat.mul_pos hN hM), fun u hu => ?_⟩` and prove the remaining obligations. Rewrite using `[← smul_smul]`.

Apply `hKt` to reduce the goal to its premises. Establish `h0` using `GlobalTheory.SplitScalar.latO_fin hu`. Establish `hz : (actO S T g h u).map (infPart D) = 0`. Simplify using `only [actO, Matrix.map_mul, h0, Matrix.mul_zero, Matrix.zero_mul]`. Use extensionality with `i j`.

Establish `hij` using `congrFun (congrFun hz i) j`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, map_nsmul, Matrix.zero_apply] at hij ⊢`. Rewrite using `[hij, smul_zero]`. Introduce `i j`. Establish `hX` using `hNm M (u.map (toEAf D)) (fun i j => hMu u hu i j) i j`.

Establish `e1 : toEAf D (((N * M) • actO S T g h u) i j) = ((N * M : ℕ) : EAf D) * ((Formalism.L2.Theta.mt T h).map (toEAf D) * u.map (toEAf D) * (Formalism.L2.Theta.mt S g⁻¹).map (toEAf D)) i j`. Simplify using `only [actO]`. Rewrite using `[Matrix.smul_apply, map_nsmul, nsmul_eq_mul, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]`. Rewrite using `[e1]`. Conclude with `hX`.
-/
theorem exists_nsmul_actO (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT)
    (g : GA D S) (h : GA D T) : ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      N • actO S T g h u ∈ latO S T ΛS ΛT fun _ => True := by
  obtain ⟨M, hM, hMu⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.fg hT.fg
  obtain ⟨K, hK, hKt⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS hT
  obtain ⟨N, hN, hNm⟩ := GlobalTheory.PlaceDatum.exists_den_mul (Formalism.L2.Herm.intAf D.host.F D.host.E)
    (fun z => GlobalTheory.PlaceDatum.exists_den_adele z) ((Formalism.L2.Theta.mt T h).map (toEAf D))
    ((Formalism.L2.Theta.mt S g⁻¹).map (toEAf D))
  refine ⟨K * (N * M), Nat.mul_pos hK (Nat.mul_pos hN hM), fun u hu => ?_⟩
  rw [← smul_smul]
  apply hKt
  · have h0 := GlobalTheory.SplitScalar.latO_fin hu
    have hz : (actO S T g h u).map (infPart D) = 0 := by
      simp only [actO, Matrix.map_mul, h0, Matrix.mul_zero, Matrix.zero_mul]
    ext i j
    have hij := congrFun (congrFun hz i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, map_nsmul, Matrix.zero_apply] at hij ⊢
    rw [hij, smul_zero]
  · intro i j
    have hX := hNm M (u.map (toEAf D)) (fun i j => hMu u hu i j) i j
    have e1 : toEAf D (((N * M) • actO S T g h u) i j) = ((N * M : ℕ) : EAf D) *
        ((Formalism.L2.Theta.mt T h).map (toEAf D) * u.map (toEAf D) * (Formalism.L2.Theta.mt S g⁻¹).map (toEAf D)) i j := by
      simp only [actO]
      rw [Matrix.smul_apply, map_nsmul, nsmul_eq_mul, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]
    rw [e1]
    exact hX

/- English proof (translation)
Simplify using `only [IsSBHalf] at hΦ ⊢`. Take `⟨h1, k, hk, h2, h3⟩` from `hΦ`. Take `⟨N, hN, hNu⟩` from `exists_nsmul_actO hS hT g h`. Take `⟨M, hM, hMu⟩` from `exists_nsmul_actO hS hT g⁻¹ h⁻¹`. Use `⟨fun t ht => isHalf_of_act g h (h1 _ ht), k * (N * M), Nat.mul_pos hk (Nat.mul_pos hN hM), ?_, ?_⟩` and prove the remaining obligations.

Introduce `u hu hua t`. Rewrite using `[act_add, act_nsmul]`. Establish `hw` using `hNu u hu`. Establish `hwa : IsHalf a (N • actO S T g h u)` using `GlobalTheory.SplitScalar.isHalf_nsmul (GlobalTheory.SplitHecke.isHalf_actO g h hua) N`. Establish `e : (k * (N * M)) • actO S T g h u = k • (M • (N • actO S T g h u))`.

Rewrite using `[smul_smul, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h2 _ (AddSubgroup.nsmul_mem _ hw M) (GlobalTheory.SplitScalar.isHalf_nsmul hwa M) _`.

Introduce `t ht`. Establish `hm` using `hMu _ (h3 _ ht)`. Rewrite `hm` using `[act_nsmul, GlobalTheory.SplitHecke.actO_inv_actO]`. Establish `e : (k * (N * M)) • t = N • (M • (k • t))`. Rewrite using `[smul_smul, smul_smul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `AddSubgroup.nsmul_mem _ hm N`.
-/
theorem isSBHalf_actO (hS : Submodule.IsLattice D.host.E ΛS) (hT : Submodule.IsLattice D.host.E ΛT) {a : AE D}
    (g : GA D S) (h : GA D T) {Φ : WO S T → ℂ} (hΦ : IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ) :
    IsSBHalf a (latO S T ΛS ΛT fun _ => True) fun t => Φ (actO S T g h t) := by
  simp only [IsSBHalf] at hΦ ⊢
  obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
  obtain ⟨N, hN, hNu⟩ := exists_nsmul_actO hS hT g h
  obtain ⟨M, hM, hMu⟩ := exists_nsmul_actO hS hT g⁻¹ h⁻¹
  refine ⟨fun t ht => isHalf_of_act g h (h1 _ ht), k * (N * M), Nat.mul_pos hk (Nat.mul_pos hN hM), ?_, ?_⟩
  · intro u hu hua t
    rw [act_add, act_nsmul]
    have hw := hNu u hu
    have hwa : IsHalf a (N • actO S T g h u) :=
      GlobalTheory.SplitScalar.isHalf_nsmul (GlobalTheory.SplitHecke.isHalf_actO g h hua) N
    have e : (k * (N * M)) • actO S T g h u = k • (M • (N • actO S T g h u)) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [e]
    exact h2 _ (AddSubgroup.nsmul_mem _ hw M) (GlobalTheory.SplitScalar.isHalf_nsmul hwa M) _
  · intro t ht
    have hm := hMu _ (h3 _ ht)
    rw [act_nsmul, GlobalTheory.SplitHecke.actO_inv_actO] at hm
    have e : (k * (N * M)) • t = N • (M • (k • t)) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [e]
    exact AddSubgroup.nsmul_mem _ hm N

/- English proof (translation)
Unfold `absV`. Establish `hq : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0`. Conclude with `(Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)` after adjusting the coercions. Rewrite using `[Units.val_mul, map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero) ((Valuation.ne_zero_iff _).mpr y.ne_zero), zpow_add₀ hq]`.
-/
theorem absV_mul {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : (Fv F v)ˣ) :
    absV F v (x * y) = absV F v x * absV F v y := by
  unfold absV
  have hq : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  rw [Units.val_mul, map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero)
    ((Valuation.ne_zero_iff _).mpr y.ne_zero), zpow_add₀ hq]

/- English proof (translation)
Unfold `absFin`. Repeatedly rewrite using `[map_mul, absV_mul]`. Conclude with `finprod_mul_distrib (absFin_finite D x) (absFin_finite D y)`.
-/
theorem absFin_mul (x y : (AE D)ˣ) : absFin D (x * y) = absFin D x * absFin D y := by
  unfold absFin
  simp_rw [map_mul, absV_mul]
  exact finprod_mul_distrib (absFin_finite D x) (absFin_finite D y)

/- English proof (translation)
Establish `h` using `absFin_mul (D := D) 1 1`. Rewrite `h` using `[mul_one]`. Establish `hp` using `absFin_pos D 1`. Establish `h2 : absFin D 1 * (absFin D 1 - 1) = 0` using `by rw [mul_sub, mul_one, ← h, sub_self]`. Break down `mul_eq_zero.mp h2 with h3 | h3` into its components or cases.

Conclude with `absurd h3 hp.ne'`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem absFin_one : absFin D 1 = 1 := by
  have h := absFin_mul (D := D) 1 1
  rw [mul_one] at h
  have hp := absFin_pos D 1
  have h2 : absFin D 1 * (absFin D 1 - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hp.ne'
  · linarith

/- English proof (translation)
Unfold `modFac`. Rewrite using `[absFin_mul, absFin_mul, Real.mul_rpow (absFin_pos D x).le (absFin_pos D x').le, Real.mul_rpow (absFin_pos D y).le (absFin_pos D y').le]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem modFac_mul (x x' y y' : (AE D)ˣ) : modFac S T (x * x') (y * y') = modFac S T x y * modFac S T x' y' := by
  unfold modFac
  rw [absFin_mul, absFin_mul, Real.mul_rpow (absFin_pos D x).le (absFin_pos D x').le,
    Real.mul_rpow (absFin_pos D y).le (absFin_pos D y').le]
  ring

/- English proof (translation)
Unfold `modFac`. Rewrite using `[absFin_one, Real.one_rpow, Real.one_rpow, one_mul]`.
-/
theorem modFac_one : modFac S T 1 1 = 1 := by
  unfold modFac
  rw [absFin_one, Real.one_rpow, Real.one_rpow, one_mul]

end GlobalTheory.SplitLinear

end
