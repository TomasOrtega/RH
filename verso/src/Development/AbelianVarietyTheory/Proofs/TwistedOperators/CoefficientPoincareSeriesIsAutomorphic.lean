import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesUnitaryAbsolutelyConvergentModeratStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCoefficientSpaceDualDiscreteSeriesModelPos
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.PoinAut

/- English proof (translation)
Use `Matrix.frobenius_norm_mul A B` as an intermediate fact. Rewrite `this` using `[Matrix.frobenius_norm_def, Matrix.frobenius_norm_def, Matrix.frobenius_norm_def]`. Unfold `hsn`. Simplify using `only [Real.sqrt_eq_rpow]`. Simplify `this` using `only [Real.rpow_two]`.
-/
theorem hsn_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : hsn (A * B) ≤ hsn A * hsn B := by
  have := Matrix.frobenius_norm_mul A B
  rw [Matrix.frobenius_norm_def, Matrix.frobenius_norm_def, Matrix.frobenius_norm_def] at this
  unfold hsn
  simp only [Real.sqrt_eq_rpow]
  simpa only [Real.rpow_two] using this

/- English proof (translation)
Establish `h1` using `hsn_mul_le A B`. Establish `h2 : 0 ≤ hsn A` using `Real.sqrt_nonneg _`. Establish `h3 : 0 ≤ hsn B` using `Real.sqrt_nonneg _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem one_add_hsn_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    1 + hsn (A * B) ≤ (1 + hsn A) * (1 + hsn B) := by
  have h1 := hsn_mul_le A B
  have h2 : 0 ≤ hsn A := Real.sqrt_nonneg _
  have h3 : 0 ≤ hsn B := Real.sqrt_nonneg _
  nlinarith

end GlobalTheory.PoinAut

/- English proof (translation)
Introduce `D θ hθ V S M v a N hd`. Use `choose C hC using hd`. Establish `hC0 : ∀ τ, 0 ≤ C τ` using `fun τ => (mul_nonneg (norm_nonneg _) (pow_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg _)) _)).trans (hC τ 1 (GlobalTheory.PointAtPlaceHom.one_mem_UH _))`. Use `⟨∏ τ, C τ, Finset.prod_nonneg fun τ _ => hC0 τ, fun x u => ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, coefR, norm_prod]`.

Use `Finset.prod_le_prod (fun τ _ => norm_nonneg _) fun τ _ => ?_` and prove the remaining obligations. Use `set A := cmp θ τ (x * u)`. Use `set B := cmp θ τ u⁻¹`. Establish `hx : cmp θ τ x = A * B` using `by show infMat D.sp.cm.sig V.gram (θ τ) x = infMat D.sp.cm.sig V.gram (θ τ) (x * u) * infMat D.sp.cm.sig V.gram (θ τ) u⁻¹`. Rewrite using `[← GlobalTheory.PointAtPlaceHom.infMat_mul, mul_inv_cancel_right]`.

Establish `hA : 0 ≤ hsn A` using `Real.sqrt_nonneg _`. Establish `hB : 0 ≤ hsn B` using `Real.sqrt_nonneg _`. Establish `hpos : 0 < (1 + hsn (cmp θ τ x)) ^ N` using `pow_pos (add_pos_of_pos_of_nonneg one_pos (Real.sqrt_nonneg _)) _`. Establish `hdec` using `hC τ A (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V (x * u) τ)`. Rewrite using `[le_mul_inv_iff₀ hpos, hx]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem GlobalTheory.PoinAut.coefR_le_majorant : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (v a : ∀ τ, M.H τ) (N : ℕ), (∀ τ, DecayAt M τ (v τ) (a τ) N) → ∃ C : ℝ, 0 ≤ C ∧ ∀ x u : GA D V,
      ‖coefR θ M v a (x * u)‖ ≤ C * (∏ τ, (1 + hsn (cmp θ τ u⁻¹)) ^ N) * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ N)⁻¹ := by
  intro D θ hθ V S M v a N hd
  choose C hC using hd
  have hC0 : ∀ τ, 0 ≤ C τ := fun τ =>
    (mul_nonneg (norm_nonneg _) (pow_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg _)) _)).trans
      (hC τ 1 (GlobalTheory.PointAtPlaceHom.one_mem_UH _))
  refine ⟨∏ τ, C τ, Finset.prod_nonneg fun τ _ => hC0 τ, fun x u => ?_⟩
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, coefR, norm_prod]
  refine Finset.prod_le_prod (fun τ _ => norm_nonneg _) fun τ _ => ?_
  set A := cmp θ τ (x * u)
  set B := cmp θ τ u⁻¹
  have hx : cmp θ τ x = A * B := by
    show infMat D.sp.cm.sig V.gram (θ τ) x = infMat D.sp.cm.sig V.gram (θ τ) (x * u) * infMat D.sp.cm.sig V.gram (θ τ) u⁻¹
    rw [← GlobalTheory.PointAtPlaceHom.infMat_mul, mul_inv_cancel_right]
  have hA : 0 ≤ hsn A := Real.sqrt_nonneg _
  have hB : 0 ≤ hsn B := Real.sqrt_nonneg _
  have hpos : 0 < (1 + hsn (cmp θ τ x)) ^ N := pow_pos (add_pos_of_pos_of_nonneg one_pos (Real.sqrt_nonneg _)) _
  have hdec := hC τ A (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V (x * u) τ)
  rw [le_mul_inv_iff₀ hpos, hx]
  calc ‖⟪v τ, M.rep τ A (a τ)⟫_ℂ‖ * (1 + hsn (A * B)) ^ N
      ≤ ‖⟪v τ, M.rep τ A (a τ)⟫_ℂ‖ * ((1 + hsn A) * (1 + hsn B)) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (add_nonneg zero_le_one (Real.sqrt_nonneg _))
          (GlobalTheory.PoinAut.one_add_hsn_mul_le A B) _) (norm_nonneg _)
    _ = (‖⟪v τ, M.rep τ A (a τ)⟫_ℂ‖ * (1 + hsn A) ^ N) * (1 + hsn B) ^ N := by rw [mul_pow, mul_assoc]
    _ ≤ C τ * (1 + hsn B) ^ N := mul_le_mul_of_nonneg_right hdec (pow_nonneg (add_nonneg zero_le_one hB) _)

/- English proof (translation)
Introduce `D θ hθ V S M K hK v a`. Use `haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram`. Establish `hcl : IsClosed ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))` using `Subgroup.isClosed_of_isOpen _ hK`. Establish `hR : Continuous (coefR θ M v a)` using `continuous_finsetProd _ fun τ _ => continuous_const.inner (((M.ds τ).2.2.1.2.2 (a τ)).comp_continuous ((continuous_const.matrix_mul (GlobalTheory.Mem.VolExists.continuous_infMat V.gram (hθ τ))).matrix_mul continuous_const) fun g => GlobalTheory.DualCoef.frame_mem M τ (GlobalTheor …`. Use `continuous_iff_continuousAt.2 fun g => ?_` and prove the remaining obligations.

Distinguish the cases in `hg : Lev.finE V g ∈ K`. Use `hR.continuousAt.congr ?_ filter_upwards [hK.mem_nhds (show g ∈ ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) from hg)] with y hy` and prove the remaining obligations. Conclude with `(if_pos hy).symm`. Use `(continuous_const (y := (0 : ℂ))).continuousAt.congr ?_ filter_upwards [hcl.isOpen_compl.mem_nhds (show g ∈ (((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)))ᶜ from hg)] with y hy` and prove the remaining obligations. Conclude with `(if_neg hy).symm`.
-/
theorem GlobalTheory.PoinAut.continuous_coef : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))), IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) →
    ∀ v a : ∀ τ, M.H τ, Continuous (coef θ M K v a) := by
  intro D θ hθ V S M K hK v a
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hcl : IsClosed ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := Subgroup.isClosed_of_isOpen _ hK
  have hR : Continuous (coefR θ M v a) := continuous_finsetProd _ fun τ _ => continuous_const.inner
    (((M.ds τ).2.2.1.2.2 (a τ)).comp_continuous
      ((continuous_const.matrix_mul (GlobalTheory.Mem.VolExists.continuous_infMat V.gram (hθ τ))).matrix_mul continuous_const)
      fun g => GlobalTheory.DualCoef.frame_mem M τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ))
  refine continuous_iff_continuousAt.2 fun g => ?_
  by_cases hg : Lev.finE V g ∈ K
  · refine hR.continuousAt.congr ?_
    filter_upwards [hK.mem_nhds (show g ∈ ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) from hg)] with y hy
    exact (if_pos hy).symm
  · refine (continuous_const (y := (0 : ℂ))).continuousAt.congr ?_
    filter_upwards [hcl.isOpen_compl.mem_nhds (show g ∈ (((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)))ᶜ from hg)] with y hy
    exact (if_neg hy).symm

namespace GlobalTheory.PoinAut

variable {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

/- English proof (translation)
Establish `e : ∀ τ, cmp θ τ (x * k) = cmp θ τ x` using `fun τ => by show infMat D.sp.cm.sig V.gram (θ τ) (x * k) = infMat D.sp.cm.sig V.gram (θ τ) x`. Rewrite using `[GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.DualCoef.infMat_of_fin _ hk1, Matrix.mul_one]`. Unfold `coef coefR`. Rewrite using `[map_mul, K.mul_mem_cancel_right hk2]`. Simplify using `only [e]`.
-/
theorem coef_mul_lev (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v b : ∀ τ, M.H τ) {k : GA D V}
    (hk1 : k ∈ GfC V) (hk2 : Lev.finE V k ∈ K) (x : GA D V) :
    coef θ M K v b (x * k) = coef θ M K v b x := by
  have e : ∀ τ, cmp θ τ (x * k) = cmp θ τ x := fun τ => by
    show infMat D.sp.cm.sig V.gram (θ τ) (x * k) = infMat D.sp.cm.sig V.gram (θ τ) x
    rw [GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.DualCoef.infMat_of_fin _ hk1, Matrix.mul_one]
  unfold coef coefR
  rw [map_mul, K.mul_mem_cancel_right hk2]
  simp only [e]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hk`. Establish `hf : Lev.finE V (atTau θ V τ k) = 1`. Establish `: finHom V (atTau θ V τ k) = 1` using `h1`. Simplify using `[Lev.finE, this]`. Unfold `coef coefR`.

Rewrite using `[map_mul, hf, mul_one]`. Use `split_ifs with hP`. Use `Finset.prod_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Distinguish the cases in `hρ : ρ = τ`. Substitute `hρ show ⟪v ρ, M.rep ρ (infMat D.sp.cm.sig V.gram (θ ρ) x) (Function.update b ρ (M.rep ρ k (b ρ)) ρ)⟫_ℂ = ⟪v ρ, M.rep ρ (infMat D.sp.cm.sig V.gram (θ ρ) (x * atTau θ V ρ k)) (b ρ)⟫_ℂ` using the available equality.

Rewrite using `[Function.update_self, GlobalTheory.PointAtPlaceHom.infMat_mul, h2, GlobalTheory.DualCoef.rep_mul M ρ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x ρ) hk]`. Use `show ⟪v ρ, M.rep ρ (infMat D.sp.cm.sig V.gram (θ ρ) x) (Function.update b τ (M.rep τ k (b τ)) ρ)⟫_ℂ = ⟪v ρ, M.rep ρ (infMat D.sp.cm.sig V.gram (θ ρ) (x * atTau θ V τ k)) (b ρ)⟫_ℂ`. Rewrite using `[Function.update_of_ne hρ, GlobalTheory.PointAtPlaceHom.infMat_mul, h3 ρ hρ, Matrix.mul_one]`. Both sides reduce to the same expression.
-/
theorem coef_update (hθ : IsInfFam θ) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v b : ∀ τ, M.H τ)
    (τ : D.what₂.Tau) {k : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hk : k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (x : GA D V) :
    coef θ M K v (Function.update b τ (M.rep τ k (b τ))) x = coef θ M K v b (x * atTau θ V τ k) := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hk
  have hf : Lev.finE V (atTau θ V τ k) = 1 := by
    have : finHom V (atTau θ V τ k) = 1 := h1
    simp [Lev.finE, this]
  unfold coef coefR
  rw [map_mul, hf, mul_one]
  split_ifs with hP
  · refine Finset.prod_congr rfl fun ρ _ => ?_
    by_cases hρ : ρ = τ
    · subst hρ
      show ⟪v ρ, M.rep ρ (infMat D.sp.cm.sig V.gram (θ ρ) x) (Function.update b ρ (M.rep ρ k (b ρ)) ρ)⟫_ℂ =
        ⟪v ρ, M.rep ρ (infMat D.sp.cm.sig V.gram (θ ρ) (x * atTau θ V ρ k)) (b ρ)⟫_ℂ
      rw [Function.update_self, GlobalTheory.PointAtPlaceHom.infMat_mul, h2,
        GlobalTheory.DualCoef.rep_mul M ρ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x ρ) hk]
    · show ⟪v ρ, M.rep ρ (infMat D.sp.cm.sig V.gram (θ ρ) x) (Function.update b τ (M.rep τ k (b τ)) ρ)⟫_ℂ =
        ⟪v ρ, M.rep ρ (infMat D.sp.cm.sig V.gram (θ ρ) (x * atTau θ V τ k)) (b ρ)⟫_ℂ
      rw [Function.update_of_ne hρ, GlobalTheory.PointAtPlaceHom.infMat_mul, h3 ρ hρ, Matrix.mul_one]
  · rfl

end GlobalTheory.PoinAut

namespace GlobalTheory.PoinAut

/- English proof (translation)
The claim follows from `Real.sqrt_nonneg _`.
-/
theorem hsn_nonneg {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsn X := Real.sqrt_nonneg _

/- English proof (translation)
The claim follows from `Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (continuous_id.matrix_elem i j).norm.pow 2)`.
-/
theorem continuous_hsn {n : ℕ} : Continuous (hsn : Matrix (Fin n) (Fin n) ℂ → ℝ) :=
  Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_id.matrix_elem i j).norm.pow 2)

end GlobalTheory.PoinAut

open GlobalTheory.PoinAut in

/- English proof (translation)
Introduce `D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c`. Use `haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram`. Use `set K := congLev D.sp.cm V.gram Λ 𝔪 with hKdef`. Use `set N := 2 * V.rank ^ 2 + 1 with hN`. Take `⟨C₀, A₀, hI⟩` from `GlobalTheory.T.poincareSeries_unitary_absolutelyConvergent_moderateGrowth D θ hθ V Λ hΛ c`.

Establish `hopen : IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))` using `(congLev_open_compact V hΛ.1 h𝔪).1`. Establish `hKtop : ∀ y, y ∈ K → y ∈ congLev D.sp.cm V.gram Λ ⊤` using `fun y hy => by`. Rewrite using `[congLev_top]`. Conclude with `⟨hy.1, hy.2.1⟩`. Set `t : GA D V → GQ V → ℝ` to `fun g γ => if Lev.finE V (c * (γ : GA D V) * g) ∈ congLev D.sp.cm V.gram Λ ⊤ then ∏ τ, ((1 + hsn (cmp θ τ (c * (γ : GA D V) * g))) ^ N)⁻¹ else 0`.

Establish `htdef : ∀ g γ, t g γ = if Lev.finE V (c * (γ : GA D V) * g) ∈ congLev D.sp.cm V.gram Λ ⊤ then ∏ τ, ((1 + hsn (cmp θ τ (c * (γ : GA D V) * g))) ^ N)⁻¹ else 0` using `fun _ _ => rfl`. Establish `ht0 : ∀ g γ, 0 ≤ t g γ` using `fun g γ => by`. Rewrite using `[htdef]`. Use `split_ifs`. Conclude with `Finset.prod_nonneg fun τ _ => inv_nonneg.2 (pow_nonneg (add_nonneg zero_le_one (hsn_nonneg _)) _)`.

Conclude with `le_rfl`. Establish `hts : ∀ g (s : Finset (GQ V)), ∑ γ ∈ s, t g γ ≤ C₀ * height V g ^ A₀` using `fun g s => by`. Use `hI g (s.filter fun γ => Lev.finE V (c * (γ : GA D V) * g) ∈ congLev D.sp.cm V.gram Λ ⊤) (fun γ hγ => (Finset.mem_filter.1 hγ).2)` as an intermediate fact. Rewrite `this` using `[Finset.sum_filter]`. Conclude with `this`.

Establish `hC₀ : 0 ≤ C₀ * height V c ^ A₀` using `by simpa using hts c ∅`. Establish `htsum : ∀ g, Summable (t g)` using `fun g => summable_of_sum_le (ht0 g) (hts g)`. Establish `httsum : ∀ g, ∑' γ, t g γ ≤ C₀ * height V g ^ A₀` using `fun g => tsum_le_of_sum_le' (by simpa using hts g ∅) (hts g)`. Establish `hP0 : ∀ u : GA D V, 0 ≤ ∏ τ, (1 + hsn (cmp θ τ u⁻¹)) ^ N` using `fun u => Finset.prod_nonneg fun τ _ => pow_nonneg (add_nonneg zero_le_one (hsn_nonneg _)) _`. Establish `hbd : ∀ b : ∀ τ, M.H τ, (∀ τ, DecayAt M τ (v τ) (b τ) N) → ∃ C : ℝ, 0 ≤ C ∧ ∀ g u (γ : GQ V), Lev.finE V u ∈ K → ‖coef θ M K v b (c * (γ : GA D V) * (g * u))‖ ≤ C * (∏ τ, (1 + hsn (cmp θ τ u⁻¹)) ^ N) * t g γ`.

Introduce `b hb`. Take `⟨C, hC, hCb⟩` from `GlobalTheory.PoinAut.coefR_le_majorant D θ hθ V S M v b N hb`. Use `⟨C, hC, fun g u γ hu => ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc]`. Unfold `coef`.

Use `split_ifs with h1`. Establish `h2 : Lev.finE V (c * (γ : GA D V) * g) ∈ K`. Use `K.mul_mem h1 (K.inv_mem hu)` as an intermediate fact. Rewrite `this` using `[map_mul, mul_inv_cancel_right]`. Then use the resulting hypothesis. Rewrite using `[htdef, if_pos (hKtop _ h2)]`.

Conclude with `hCb _ _`. Rewrite using `[norm_zero]`. Conclude with `mul_nonneg (mul_nonneg hC (hP0 u)) (ht0 g γ)`. Establish `hcont : ∀ b : ∀ τ, M.H τ, (∀ τ, DecayAt M τ (v τ) (b τ) N) → Continuous (poin θ M K v c b)`. Introduce `b hb`.

Take `⟨C, hC, hCb⟩` from `hbd b hb`. Use `continuous_iff_continuousAt.2 fun g₀ => ?_` and prove the remaining obligations. Set `P : GA D V → ℝ` to `fun u => ∏ τ, (1 + hsn (cmp θ τ u⁻¹)) ^ N`. Establish `hPc : Continuous P` using `continuous_finsetProd _ fun τ _ => (continuous_const.add (continuous_hsn.comp ((GlobalTheory.Mem.VolExists.continuous_infMat V.gram (hθ τ)).comp continuous_inv))).pow _`. Set `W : Set (GA D V)` to `{g | Lev.finE V (g₀⁻¹ * g) ∈ K ∧ P (g₀⁻¹ * g) < P 1 + 1}`.

Establish `hW : IsOpen W` using `(hopen.preimage (continuous_const.mul continuous_id)).inter (isOpen_lt (hPc.comp (continuous_const.mul continuous_id)) continuous_const)`. Establish `hg₀ : g₀ ∈ W` using `⟨by rw [inv_mul_cancel, map_one]; exact one_mem _, by rw [inv_mul_cancel]; exact lt_add_one _⟩`. Use `show ContinuousAt (fun g => ∑' γ : GQ V, coef θ M K v b (c * (γ : GA D V) * g)) g₀`. Use `(continuousOn_tsum (u := fun γ => C * (P 1 + 1) * t g₀ γ) (fun γ => ?_) ((htsum g₀).mul_left _) (fun γ g hg => ?_)).continuousAt (hW.mem_nhds hg₀)` and prove the remaining obligations. Conclude with `((GlobalTheory.PoinAut.continuous_coef D θ hθ V S M K hopen v b).comp (continuous_const.mul continuous_id)).continuousOn`.

Use `hCb g₀ (g₀⁻¹ * g) γ hg.1` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Conclude with `this.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg.2.le hC) (ht0 _ _))`. Establish `hdec : ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, ∀ τ, DecayAt M τ (v τ) ((fun τ => (a τ : M.H τ)) τ) N` using `fun a τ => (hv τ).2 _ (a τ).2`. Establish `hb1 : ∀ b : ∀ τ, M.H τ, (∀ τ, DecayAt M τ (v τ) (b τ) N) → ∃ C : ℝ, 0 ≤ C ∧ ∀ g (γ : GQ V), ‖coef θ M K v b (c * (γ : GA D V) * g)‖ ≤ C * t g γ`.

Introduce `b hb`. Take `⟨C, hC, hCb⟩` from `hbd b hb`. Use `⟨C * ∏ τ, (1 + hsn (cmp θ τ (1 : GA D V)⁻¹)) ^ N, mul_nonneg hC (hP0 1), fun g γ => ?_⟩` and prove the remaining obligations. Use `hCb g 1 γ (by rw [map_one]; exact one_mem _)` as an intermediate fact. Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis.

Establish `hsumN : ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, ∀ g, Summable fun γ : GQ V => ‖coef θ M K v (fun τ => a τ) (c * (γ : GA D V) * g)‖`. Introduce `a g`. Take `⟨C, hC, hCb⟩` from `hb1 _ (hdec a)`. Conclude with `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hCb g) ((htsum g).mul_left C)`. Establish `hlev : ∀ b, ∀ k ∈ Lev.levA V K, ∀ g, poin θ M K v c b (g * k) = poin θ M K v c b g`.

Introduce `b k hk g`. Simplify using `only [poin]`. Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, coef_mul_lev M K v b hk.1 hk.2]`. Establish `hleft : ∀ b, ∀ γ₀ ∈ GQ V, ∀ g, poin θ M K v c b (γ₀ * g) = poin θ M K v c b g`.

Introduce `b γ₀ h g`. Simplify using `only [poin]`. Use `(Equiv.mulRight (⟨γ₀, h⟩ : GQ V)).tsum_eq (fun γ : GQ V => coef θ M K v b (c * (γ : GA D V) * g))` as an intermediate fact. Rewrite using `[← this]`. Use `tsum_congr fun γ => ?_` and prove the remaining obligations.

Simplify using `only [Equiv.coe_mulRight, Subgroup.coe_mul, mul_assoc]`. Set `L : GA D V → MultilinearMap ℂ (fun τ : D.what₂.Tau => M.H τ) ℂ` to `fun z => (MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau ℂ).compLinearMap fun τ => (innerₛₗ ℂ (v τ)).comp (M.rep τ (cmp θ τ z)).toLinearMap`. Establish `hL : ∀ z b, coefR θ M v b z = L z b` using `fun z b => by`. Simplify using `[L, coefR, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]`. Use `⟨fun a => ⟨⟨hleft _, ⟨_, hopen, fun k hk hk' g => hlev _ k ⟨hk', hk⟩ g⟩, hcont _ (hdec a)⟩, ?_, hsumN a, hlev _⟩, ⟨{ toFun := fun a => poin θ M K v c fun τ => a τ, map_update_add' := ?_, map_update_smul' := ?_ }, fun a => rfl⟩, fun a τ k hk => ?_⟩` and prove the remaining obligations.

Take `⟨C, hC, hCb⟩` from `hb1 _ (hdec a)`. Use `⟨C * C₀, A₀, fun g => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Introduce `_ a i x y`. Use function extensionality and compare the values at `g`.

Establish `e : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M i, (fun τ => ((Function.update a i w τ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) : M.H τ)) = Function.update (fun τ => (a τ : M.H τ)) i (w : M.H i)` using `fun w => by`. Use function extensionality and compare the values at `τ`. Distinguish the cases in `h : τ = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Function.update_of_ne h]`. Establish `s1` using `(hsumN (Function.update a i x) g).of_norm`. Establish `s2` using `(hsumN (Function.update a i y) g).of_norm`. Rewrite `s1`, `s2` using `[e]`. Simplify using `only [Pi.add_apply, poin]`.

Rewrite using `[e, e, e, ← s1.tsum_add s2]`. Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Unfold `coef`. Use `split_ifs`. Rewrite using `[hL, hL, hL, Submodule.coe_add, (L _).map_update_add]`.

Simplify using the standard rewrite rules. Introduce `_ a i r x`. Use function extensionality and compare the values at `g`. Establish `e : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M i, (fun τ => ((Function.update a i w τ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) : M.H τ)) = Function.update (fun τ => (a τ : M.H τ)) i (w : M.H i)` using `fun w => by`. Use function extensionality and compare the values at `τ`.

Distinguish the cases in `h : τ = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne h]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, poin]`.

Rewrite using `[e, e, ← tsum_mul_left]`. Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Unfold `coef`. Use `split_ifs`. Rewrite using `[hL, hL, Submodule.coe_smul, (L _).map_update_smul, smul_eq_mul]`.

Simplify using the standard rewrite rules. Use function extensionality and compare the values at `g`. Simplify using `only [rTr, poin]`. Conclude with `tsum_congr fun γ => by rw [coef_update M hθ K v a τ hk, mul_assoc]`.
-/
theorem GlobalTheory.PoinAut.poin_aut : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, (∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, IsAutFun V (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∧ ModGrowth V (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∧ (∀ g, Summable fun γ : GQ V => ‖coef θ M (congLev D.sp.cm V.gram Λ 𝔪) v (fun τ => a τ) (c * (γ : GA D V) * g)‖) ∧ ∀ k ∈ Lev.levA V (congLev D.sp.cm V.gram Λ 𝔪), ∀ g, poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c (fun τ => a τ) (g * k) = poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c (fun τ => a τ) g) ∧ (∃ T₀ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap M, ∀ a, T₀ a = poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∧ ∀ (a : ∀ τ, M.H τ) τ, ∀ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c (Function.update a τ (M.rep τ k (a τ))) = rTr V (atTau θ V τ k) (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c a) := by
  intro D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  set K := congLev D.sp.cm V.gram Λ 𝔪 with hKdef
  set N := 2 * V.rank ^ 2 + 1 with hN
  obtain ⟨C₀, A₀, hI⟩ := GlobalTheory.T.poincareSeries_unitary_absolutelyConvergent_moderateGrowth D θ hθ V Λ hΛ c
  have hopen : IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) :=
    (congLev_open_compact V hΛ.1 h𝔪).1
  have hKtop : ∀ y, y ∈ K → y ∈ congLev D.sp.cm V.gram Λ ⊤ := fun y hy => by
    rw [congLev_top]; exact ⟨hy.1, hy.2.1⟩

  let t : GA D V → GQ V → ℝ := fun g γ => if Lev.finE V (c * (γ : GA D V) * g) ∈ congLev D.sp.cm V.gram Λ ⊤ then
      ∏ τ, ((1 + hsn (cmp θ τ (c * (γ : GA D V) * g))) ^ N)⁻¹ else 0
  have htdef : ∀ g γ, t g γ = if Lev.finE V (c * (γ : GA D V) * g) ∈ congLev D.sp.cm V.gram Λ ⊤ then
      ∏ τ, ((1 + hsn (cmp θ τ (c * (γ : GA D V) * g))) ^ N)⁻¹ else 0 := fun _ _ => rfl
  have ht0 : ∀ g γ, 0 ≤ t g γ := fun g γ => by
    rw [htdef]; split_ifs
    · exact Finset.prod_nonneg fun τ _ => inv_nonneg.2 (pow_nonneg (add_nonneg zero_le_one (hsn_nonneg _)) _)
    · exact le_rfl
  have hts : ∀ g (s : Finset (GQ V)), ∑ γ ∈ s, t g γ ≤ C₀ * height V g ^ A₀ := fun g s => by
    have := hI g (s.filter fun γ => Lev.finE V (c * (γ : GA D V) * g) ∈ congLev D.sp.cm V.gram Λ ⊤)
      (fun γ hγ => (Finset.mem_filter.1 hγ).2)
    rw [Finset.sum_filter] at this
    exact this
  have hC₀ : 0 ≤ C₀ * height V c ^ A₀ := by simpa using hts c ∅
  have htsum : ∀ g, Summable (t g) := fun g => summable_of_sum_le (ht0 g) (hts g)
  have httsum : ∀ g, ∑' γ, t g γ ≤ C₀ * height V g ^ A₀ := fun g =>
    tsum_le_of_sum_le' (by simpa using hts g ∅) (hts g)
  have hP0 : ∀ u : GA D V, 0 ≤ ∏ τ, (1 + hsn (cmp θ τ u⁻¹)) ^ N := fun u =>
    Finset.prod_nonneg fun τ _ => pow_nonneg (add_nonneg zero_le_one (hsn_nonneg _)) _

  have hbd : ∀ b : ∀ τ, M.H τ, (∀ τ, DecayAt M τ (v τ) (b τ) N) → ∃ C : ℝ, 0 ≤ C ∧
      ∀ g u (γ : GQ V), Lev.finE V u ∈ K → ‖coef θ M K v b (c * (γ : GA D V) * (g * u))‖ ≤
        C * (∏ τ, (1 + hsn (cmp θ τ u⁻¹)) ^ N) * t g γ := by
    intro b hb
    obtain ⟨C, hC, hCb⟩ := GlobalTheory.PoinAut.coefR_le_majorant D θ hθ V S M v b N hb
    refine ⟨C, hC, fun g u γ hu => ?_⟩
    rw [← mul_assoc]
    unfold coef
    split_ifs with h1
    · have h2 : Lev.finE V (c * (γ : GA D V) * g) ∈ K := by
        have := K.mul_mem h1 (K.inv_mem hu)
        rwa [map_mul, mul_inv_cancel_right] at this
      rw [htdef, if_pos (hKtop _ h2)]
      exact hCb _ _
    · rw [norm_zero]
      exact mul_nonneg (mul_nonneg hC (hP0 u)) (ht0 g γ)
  have hcont : ∀ b : ∀ τ, M.H τ, (∀ τ, DecayAt M τ (v τ) (b τ) N) → Continuous (poin θ M K v c b) := by
    intro b hb
    obtain ⟨C, hC, hCb⟩ := hbd b hb
    refine continuous_iff_continuousAt.2 fun g₀ => ?_
    let P : GA D V → ℝ := fun u => ∏ τ, (1 + hsn (cmp θ τ u⁻¹)) ^ N
    have hPc : Continuous P := continuous_finsetProd _ fun τ _ =>
      (continuous_const.add (continuous_hsn.comp
        ((GlobalTheory.Mem.VolExists.continuous_infMat V.gram (hθ τ)).comp continuous_inv))).pow _
    let W : Set (GA D V) := {g | Lev.finE V (g₀⁻¹ * g) ∈ K ∧ P (g₀⁻¹ * g) < P 1 + 1}
    have hW : IsOpen W := (hopen.preimage (continuous_const.mul continuous_id)).inter
      (isOpen_lt (hPc.comp (continuous_const.mul continuous_id)) continuous_const)
    have hg₀ : g₀ ∈ W := ⟨by rw [inv_mul_cancel, map_one]; exact one_mem _, by rw [inv_mul_cancel]; exact lt_add_one _⟩
    show ContinuousAt (fun g => ∑' γ : GQ V, coef θ M K v b (c * (γ : GA D V) * g)) g₀
    refine (continuousOn_tsum (u := fun γ => C * (P 1 + 1) * t g₀ γ) (fun γ => ?_) ((htsum g₀).mul_left _)
      (fun γ g hg => ?_)).continuousAt (hW.mem_nhds hg₀)
    · exact ((GlobalTheory.PoinAut.continuous_coef D θ hθ V S M K hopen v b).comp (continuous_const.mul continuous_id)).continuousOn
    · have := hCb g₀ (g₀⁻¹ * g) γ hg.1
      rw [mul_inv_cancel_left] at this
      exact this.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg.2.le hC) (ht0 _ _))
  have hdec : ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, ∀ τ, DecayAt M τ (v τ) ((fun τ => (a τ : M.H τ)) τ) N :=
    fun a τ => (hv τ).2 _ (a τ).2
  have hb1 : ∀ b : ∀ τ, M.H τ, (∀ τ, DecayAt M τ (v τ) (b τ) N) → ∃ C : ℝ, 0 ≤ C ∧
      ∀ g (γ : GQ V), ‖coef θ M K v b (c * (γ : GA D V) * g)‖ ≤ C * t g γ := by
    intro b hb
    obtain ⟨C, hC, hCb⟩ := hbd b hb
    refine ⟨C * ∏ τ, (1 + hsn (cmp θ τ (1 : GA D V)⁻¹)) ^ N, mul_nonneg hC (hP0 1), fun g γ => ?_⟩
    have := hCb g 1 γ (by rw [map_one]; exact one_mem _)
    rwa [mul_one] at this
  have hsumN : ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, ∀ g,
      Summable fun γ : GQ V => ‖coef θ M K v (fun τ => a τ) (c * (γ : GA D V) * g)‖ := by
    intro a g
    obtain ⟨C, hC, hCb⟩ := hb1 _ (hdec a)
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hCb g) ((htsum g).mul_left C)
  have hlev : ∀ b, ∀ k ∈ Lev.levA V K, ∀ g, poin θ M K v c b (g * k) = poin θ M K v c b g := by
    intro b k hk g
    simp only [poin]
    refine tsum_congr fun γ => ?_
    rw [← mul_assoc, coef_mul_lev M K v b hk.1 hk.2]
  have hleft : ∀ b, ∀ γ₀ ∈ GQ V, ∀ g, poin θ M K v c b (γ₀ * g) = poin θ M K v c b g := by
    intro b γ₀ h g
    simp only [poin]
    have := (Equiv.mulRight (⟨γ₀, h⟩ : GQ V)).tsum_eq (fun γ : GQ V => coef θ M K v b (c * (γ : GA D V) * g))
    rw [← this]
    refine tsum_congr fun γ => ?_
    simp only [Equiv.coe_mulRight, Subgroup.coe_mul, mul_assoc]

  let L : GA D V → MultilinearMap ℂ (fun τ : D.what₂.Tau => M.H τ) ℂ := fun z =>
    (MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau ℂ).compLinearMap fun τ =>
      (innerₛₗ ℂ (v τ)).comp (M.rep τ (cmp θ τ z)).toLinearMap
  have hL : ∀ z b, coefR θ M v b z = L z b := fun z b => by
    simp [L, coefR, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  refine ⟨fun a => ⟨⟨hleft _, ⟨_, hopen, fun k hk hk' g => hlev _ k ⟨hk', hk⟩ g⟩, hcont _ (hdec a)⟩, ?_,
    hsumN a, hlev _⟩, ⟨{ toFun := fun a => poin θ M K v c fun τ => a τ, map_update_add' := ?_, map_update_smul' := ?_ },
    fun a => rfl⟩, fun a τ k hk => ?_⟩
  · obtain ⟨C, hC, hCb⟩ := hb1 _ (hdec a)
    refine ⟨C * C₀, A₀, fun g => ?_⟩
    calc ‖poin θ M K v c (fun τ => (a τ : M.H τ)) g‖
        ≤ ∑' γ : GQ V, ‖coef θ M K v (fun τ => a τ) (c * (γ : GA D V) * g)‖ := norm_tsum_le_tsum_norm (hsumN a g)
      _ ≤ ∑' γ, C * t g γ := Summable.tsum_le_tsum (hCb g) (hsumN a g) ((htsum g).mul_left _)
      _ = C * ∑' γ, t g γ := tsum_mul_left
      _ ≤ C * (C₀ * height V g ^ A₀) := mul_le_mul_of_nonneg_left (httsum g) hC
      _ = C * C₀ * height V g ^ A₀ := by ring
  · intro _ a i x y
    funext g
    have e : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M i, (fun τ => ((Function.update a i w τ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) : M.H τ)) =
        Function.update (fun τ => (a τ : M.H τ)) i (w : M.H i) := fun w => by
      funext τ
      by_cases h : τ = i
      · subst h; simp
      · simp [Function.update_of_ne h]
    have s1 := (hsumN (Function.update a i x) g).of_norm
    have s2 := (hsumN (Function.update a i y) g).of_norm
    rw [e] at s1 s2
    simp only [Pi.add_apply, poin]
    rw [e, e, e, ← s1.tsum_add s2]
    refine tsum_congr fun γ => ?_
    unfold coef
    split_ifs
    · rw [hL, hL, hL, Submodule.coe_add, (L _).map_update_add]
    · simp
  · intro _ a i r x
    funext g
    have e : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M i, (fun τ => ((Function.update a i w τ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) : M.H τ)) =
        Function.update (fun τ => (a τ : M.H τ)) i (w : M.H i) := fun w => by
      funext τ
      by_cases h : τ = i
      · subst h; simp
      · simp [Function.update_of_ne h]
    simp only [Pi.smul_apply, smul_eq_mul, poin]
    rw [e, e, ← tsum_mul_left]
    refine tsum_congr fun γ => ?_
    unfold coef
    split_ifs
    · rw [hL, hL, Submodule.coe_smul, (L _).map_update_smul, smul_eq_mul]
    · simp
  · funext g
    simp only [rTr, poin]
    exact tsum_congr fun γ => by rw [coef_update M hθ K v a τ hk, mul_assoc]

end
