import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyValueUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatrixIsForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatLinearCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubsetPartitionNull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberGlobalSectionEqSumCycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOnNhdOffBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAbelianLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyArithDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormIntegrablePoincareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothClosureReducedSubschemeMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChartLiftBisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatrixPullbackCellStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeIntegralDensityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensityChartFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityIntegralLinearCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityPushforwardIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignedDensityPartitionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensityCurvatureBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicFrameNearBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenCurvatureTendstoHodgeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSecondChernHodgeVanishesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundarySettingNormBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundarySettingRestrictSubvarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSectionDifferenceBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPotentialSectionBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactProjectiveAnalyticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundaryStrataSubvarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryIntegralOffStrataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularIntegralBoundaryPotentialStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical
open GlobalTheory.Cartier GlobalTheory.Published GlobalTheory.VdmWd

namespace GlobalTheory.ArchLim

section Poly

/- English proof (translation)
Establish `: P ∈ Submodule.span ℝ (Set.range fun n : κ → ℤ => lin (fun x => (n x : ℝ)) ^ d)`. Assume the negation of the conclusion as `hn`. Take `⟨f, hf, hf'⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance`. Establish `h0` using `GlobalTheory.ArInt.Model.eq_zero_of_pow d (f ∘ₗ MvPolynomial.homogeneousComponent d) (fun n => by`. Rewrite using `[LinearMap.comp_apply, MvPolynomial.homogeneousComponent_eq_self (isHomogeneous_lin_pow _ d)]`.

Conclude with `(Submodule.mem_bot ℝ).1 (hf' ▸ Submodule.mem_map_of_mem (Submodule.subset_span ⟨n, rfl⟩)))`. Use `fun Q e he hQ => by`. Rewrite using `[LinearMap.comp_apply, MvPolynomial.homogeneousComponent_of_mem hQ, if_neg (Ne.symm he), map_zero]`. Use `LinearMap.congr_fun h0 P` as an intermediate fact. Rewrite `this` using `[LinearMap.comp_apply, MvPolynomial.homogeneousComponent_eq_self hP]`.

Conclude with `hf this`. Take `⟨c, hc⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.1 this`. Conclude with `⟨c.support, inferInstance, fun j => c j, fun j => j, (Finset.sum_coe_sort c.support fun n => c n • lin (fun x => (n x : ℝ)) ^ d).trans hc⟩`.
-/
theorem exists_sum_lin_pow {κ : Type} [Fintype κ] {d : ℕ} {P : MvPolynomial κ ℝ} (hP : P.IsHomogeneous d) :
    ∃ (I : Type) (_ : Fintype I) (c : I → ℝ) (n : I → κ → ℤ), ∑ j, c j • lin (fun x => (n j x : ℝ)) ^ d = P := by
  have : P ∈ Submodule.span ℝ (Set.range fun n : κ → ℤ => lin (fun x => (n x : ℝ)) ^ d) := by
    by_contra hn
    obtain ⟨f, hf, hf'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
    have h0 := GlobalTheory.ArInt.Model.eq_zero_of_pow d (f ∘ₗ MvPolynomial.homogeneousComponent d) (fun n => by
      rw [LinearMap.comp_apply, MvPolynomial.homogeneousComponent_eq_self (isHomogeneous_lin_pow _ d)]
      exact (Submodule.mem_bot ℝ).1 (hf' ▸ Submodule.mem_map_of_mem (Submodule.subset_span ⟨n, rfl⟩)))
      fun Q e he hQ => by
        rw [LinearMap.comp_apply, MvPolynomial.homogeneousComponent_of_mem hQ, if_neg (Ne.symm he), map_zero]
    have := LinearMap.congr_fun h0 P
    rw [LinearMap.comp_apply, MvPolynomial.homogeneousComponent_eq_self hP] at this
    exact hf this
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 this
  exact ⟨c.support, inferInstance, fun j => c j, fun j => j, (Finset.sum_coe_sort c.support
    fun n => c n • lin (fun x => (n x : ℝ)) ^ d).trans hc⟩

/- English proof (translation)
Simplify using `only [Fin.card_Ioi]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => m - 1 - i), Finset.sum_range_reflect (fun i => i), Finset.sum_range_id, Nat.choose_two_right]`.
-/
theorem sum_card_Ioi (m : ℕ) : ∑ i : Fin m, (Finset.Ioi i).card = m.choose 2 := by
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => m - 1 - i), Finset.sum_range_reflect (fun i => i), Finset.sum_range_id,
    Nat.choose_two_right]

/- English proof (translation)
Rewrite using `[← sum_card_Ioi, ← Finset.card_sigma, ← Finset.card_univ]`. Apply the tactic sequence `refine Finset.card_bij' (fun s _ => ⟨s.1.2, s.1.1⟩) (fun t ht => ⟨(t.2, t.1), by simpa using ht⟩) ?_ ?_ ?_ ?_ <;>`. Simplify using the standard rewrite rules.
-/
theorem card_low_eq (m : ℕ) : Fintype.card (Low m) = m.choose 2 := by
  rw [← sum_card_Ioi, ← Finset.card_sigma, ← Finset.card_univ]
  refine Finset.card_bij' (fun s _ => ⟨s.1.2, s.1.1⟩) (fun t ht => ⟨(t.2, t.1), by simpa using ht⟩) ?_ ?_ ?_ ?_ <;>
    simp

/- English proof (translation)
Establish `h₁ : (∏ i : Fin r, ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (some i') - MvPolynomial.X (some i)) : MvPolynomial (Option (Fin r)) ℝ).IsHomogeneous (r.choose 2)`. Rewrite using `[← sum_card_Ioi]`. Use `MvPolynomial.IsHomogeneous.prod _ _ _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.card_eq_sum_ones]`. Conclude with `MvPolynomial.IsHomogeneous.prod _ _ _ fun i' _ => (MvPolynomial.isHomogeneous_X _ _).sub (MvPolynomial.isHomogeneous_X _ _)`.

Establish `h₂ : (∑ i : Fin r, MvPolynomial.X (some i) ^ 2 : MvPolynomial (Option (Fin r)) ℝ).IsHomogeneous 2` using `MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => MvPolynomial.isHomogeneous_X_pow _ _`. Use `((h₂.C_mul ((r.factorial : ℝ)⁻¹)).mul h₁).mul (MvPolynomial.isHomogeneous_X_pow (none : Option (Fin r)) e)` as an intermediate fact. Rewrite `this` using `[show 2 + r.choose 2 + e = e + 2 + r.choose 2 by omega]`. Then use the resulting hypothesis.
-/
theorem isHomogeneous_vdmPol (r e : ℕ) : (vdmPol r e).IsHomogeneous (e + 2 + r.choose 2) := by
  have h₁ : (∏ i : Fin r, ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (some i') - MvPolynomial.X (some i)) :
      MvPolynomial (Option (Fin r)) ℝ).IsHomogeneous (r.choose 2) := by
    rw [← sum_card_Ioi]
    refine MvPolynomial.IsHomogeneous.prod _ _ _ fun i _ => ?_
    rw [Finset.card_eq_sum_ones]
    exact MvPolynomial.IsHomogeneous.prod _ _ _ fun i' _ =>
      (MvPolynomial.isHomogeneous_X _ _).sub (MvPolynomial.isHomogeneous_X _ _)
  have h₂ : (∑ i : Fin r, MvPolynomial.X (some i) ^ 2 : MvPolynomial (Option (Fin r)) ℝ).IsHomogeneous 2 :=
    MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => MvPolynomial.isHomogeneous_X_pow _ _
  have := ((h₂.C_mul ((r.factorial : ℝ)⁻¹)).mul h₁).mul (MvPolynomial.isHomogeneous_X_pow (none : Option (Fin r)) e)
  rwa [show 2 + r.choose 2 + e = e + 2 + r.choose 2 by omega] at this

end Poly

section Fibre

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k}

/- English proof (translation)
Use `⟨fun c c' y hy hy' => c.chernDens_trans c' h hy hy', fun c => ?_⟩` and prove the remaining obligations. Establish `hc : Continuous fun A : Matrix (Fin D) (Fin D) ℂ => (D.factorial / Real.pi ^ D * A.det.re : ℝ)` using `continuous_const.mul (Complex.continuous_re.comp continuous_id.matrix_det)`. Conclude with `hc.comp_continuousOn ((GlobalTheory.MixDens.chernMat_isForm k Y p σ D B φ h).2.1 c)`.
-/
theorem isDens_chernDens {σ : k →+* ℂ} {D : ℕ} {B : LB Y} {φ : Weight p σ B} (h : φ.IsCInf) :
    IsDens fun (c : AlgChart p σ D) y => c.chernDens φ y := by
  refine ⟨fun c c' y hy hy' => c.chernDens_trans c' h hy hy', fun c => ?_⟩
  have hc : Continuous fun A : Matrix (Fin D) (Fin D) ℂ => (D.factorial / Real.pi ^ D * A.det.re : ℝ) :=
    continuous_const.mul (Complex.continuous_re.comp continuous_id.matrix_det)
  exact hc.comp_continuousOn ((GlobalTheory.MixDens.chernMat_isForm k Y p σ D B φ h).2.1 c)

/- English proof (translation)
Use `hY.isLocallyNoetherian` as an intermediate fact. Establish `hr` using `isRatSec_ratOfSec s hs`. Take `⟨Φ, hΦ⟩` from `((hC.arExists k Y p D hY).2 (Option ι) (fun o => o.elim M L)).1`. Take `⟨g, hg⟩` from `(hC.arExists k Y p D hY).1 (comb L n)`. Establish `h₁` using `((hC.arMix k Y p D hY ι M L Φ hΦ n g hg _ hr).1 σ).congr (g := fun v => Real.log ((M.φ σ).nsq (secVal p σ s) v) / 2) (isOpen_offSupp _).measurableSet fun y hy => logNorm_ratOfSec _ ((offSupp_divOfSec (q := p) (σ := σ) (hL := M.isLB) (hs := hs)).le hy)`.

Establish `hnull (ε : ℤˣ) : ((comb L n).φ σ).chernPart D ε (offSupp p σ (M.div hr))ᶜ = 0`. Establish `e : (offSupp p σ (M.div hr))ᶜ = {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ ((M.div hr).supp : Set Y)}`. Use extensionality with `y`. Simplify using `only [Set.mem_compl_iff, mem_offSupp, not_not]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `GlobalTheory.ChernNull.chernPart_over_closed hY _ (M.div hr).supp.isClosed (CartierDiv.genericPoint_notMem_supp _) σ _ ε`. Take `⟨h₂, h₃⟩` from `h₁`. Rewrite `h₂`, `h₃` using `[IntegrableOn, Measure.restrict_eq_self_of_ae_mem (s := offSupp p σ (M.div hr)) (hnull _)]`. Conclude with `⟨h₂.integrableOn, h₃.integrableOn⟩`.
-/
theorem chernIntegrableOn_log (hC : ArCalc) [IsIntegral Y] {D : ℕ} (hY : IsArithVar p D) {ι : Type} [Fintype ι]
    (L : ι → HermLB p) (n : ι → ℤ) (M : HermLB p) (s : M.B.Sec) (hs : genericPoint Y ∈ Out.nonzeroLocus s) (σ : k →+* ℂ) :
    ((comb L n).φ σ).ChernIntegrableOn D Set.univ fun v => Real.log ((M.φ σ).nsq (secVal p σ s) v) / 2 := by
  have := hY.isLocallyNoetherian
  have hr := isRatSec_ratOfSec s hs
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k Y p D hY).2 (Option ι) (fun o => o.elim M L)).1
  obtain ⟨g, hg⟩ := (hC.arExists k Y p D hY).1 (comb L n)
  have h₁ := ((hC.arMix k Y p D hY ι M L Φ hΦ n g hg _ hr).1 σ).congr
    (g := fun v => Real.log ((M.φ σ).nsq (secVal p σ s) v) / 2) (isOpen_offSupp _).measurableSet fun y hy =>
      logNorm_ratOfSec _ ((offSupp_divOfSec (q := p) (σ := σ) (hL := M.isLB) (hs := hs)).le hy)
  have hnull (ε : ℤˣ) : ((comb L n).φ σ).chernPart D ε (offSupp p σ (M.div hr))ᶜ = 0 := by
    have e : (offSupp p σ (M.div hr))ᶜ =
        {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ ((M.div hr).supp : Set Y)} := by
      ext y
      simp only [Set.mem_compl_iff, mem_offSupp, not_not]
      rfl
    rw [e]
    exact GlobalTheory.ChernNull.chernPart_over_closed hY _ (M.div hr).supp.isClosed
      (CartierDiv.genericPoint_notMem_supp _) σ _ ε
  obtain ⟨h₂, h₃⟩ := h₁
  rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (s := offSupp p σ (M.div hr)) (hnull _)] at h₂ h₃
  exact ⟨h₂.integrableOn, h₃.integrableOn⟩

/- English proof (translation)
Take `⟨t, ht⟩` from `GlobalTheory.T.vandermonde_integral_density r e`. Use `⟨t, fun k _ B Y _ _ q p π w E h H N fl L hZ hY hgen hfl iN iG I _ c m hcm σ f hf hint => ?_⟩` and prove the remaining obligations. Take `⟨ε⟩ : Nonempty (Fin (e + 2 + r.choose 2) ≃ Fin (e + 2) ⊕ Low r)` from `⟨Fintype.equivOfCardEq (by simp [card_low_eq])⟩`. Generalize the expression as in `e + 2 + r.choose 2 = D at *`. Use `CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver` as an intermediate fact.

Establish `hD (j) : IsDens fun (ch : AlgChart p σ D) v => ch.chernDens ((comb L (m j)).φ σ) v` using `isDens_chernDens (HermLB.cInf _ σ)`. Take `⟨l₁, l₂⟩` from `GlobalTheory.T.density_integral_linear_combination k _ _ σ D I c _ _ hD fun j => (densInt_chernDens _ _).2.2 (hint j)`. Establish `hch` using `GlobalTheory.T.second_chern_density_chart_formula k _ _ σ _ r (h.met σ) _ (N.φ σ) e (H σ) (N.cInf σ)`. Simplify using `only [← (densInt_chernDens _ _).1]`. Use `l₂.symm.trans ?_` and prove the remaining obligations.

Use `GlobalTheory.T.density_pushforward_integral k _ _ _ _ π w _ r _ ε σ hZ hY hgen _ _ _ (IsDens.sum _ fun j => (hD j).mul continuous_const) (hch.1.mul continuous_const) hf l₁ fun c₀ y₀ hy₀ => ?_` and prove the remaining obligations. Take `⟨c₁, cE, c', h₁, h₂, h₃, h₄⟩` from `GlobalTheory.T.flag_bundle_chart_lift_bis k _ _ _ _ π w _ r _ ε σ _ _ H fl hfl c₀ y₀ hy₀`. Use `⟨c₁, c', h₁, h₃, fun u hu => ?_⟩` and prove the remaining obligations. Establish `hu'` using `c₁.e.map_target hu`. Rewrite using `[hch.2 c₁ cE _ hu' (h₂ hu'), c₁.e.right_inv hu]`.

Establish `hG` using `(H σ cE _ (h₂ hu')).mContDiffAt c₁ hu'`. Establish `hψ` using `(N.cInf σ).contDiffAt c₁ hu' (mem_pick (N.φ σ).isLB _)`. Rewrite `hG`, `hψ` using `[c₁.e.right_inv hu]`. Use `ht _ ε _ _ u hG (Filter.eventually_of_mem (c₁.e.open_target.mem_nhds hu) fun v hv => (h.met σ).posDef _ _ (h₂ (c₁.e.map_target hv))) hψ I c m hcm` as an intermediate fact. Use `Eq.trans (integral_congr_ae (.of_forall fun x => Finset.sum_congr rfl fun j _ => ?_)) (this.trans ?_)` and prove the remaining obligations.

Establish `htg : pt ε u x ∈ c'.e.target`. Rewrite using `[h₃.2.1]`. Simplify `hu` using `only [Set.mem_setOf_eq, base_pt]`. Establish `hs'` using `c'.e.map_target htg`. Establish `hb : PtsOver.map π w (spMap σ) (c'.e.symm (pt ε u x)) = c₁.e.symm u`.

Use `h₃.2.2 _ hs'` as an intermediate fact. Rewrite `this` using `[c'.e.right_inv htg, base_pt]`. Conclude with `(c₁.e.left_inv (h₃.1.le hs').1).symm.trans (congrArg c₁.e.symm this.symm)`. Use `congrArg (fun A : Matrix (Fin D) (Fin D) ℂ => c j * (D.factorial / Real.pi ^ D * A.det.re)) ((GlobalTheory.MixDens.chernMat_comb k _ _ σ _ _ _ (m j) c' _ hs').trans (Finset.sum_congr rfl fun o _ => congrArg _ ?_))` and prove the remaining obligations. Break down `o with _ | i` into its components or cases.

Rewrite using `[MixDens.chernMat_congr iN c' hs', GlobalTheory.T.chern_matrix_pullback_cell k _ _ _ _ π w _ r _ ε σ c₁ c' h₃ _ _ hs', hb, c'.e.right_inv htg]`. Both sides reduce to the same expression. Rewrite using `[MixDens.chernMat_congr (iG i) c' hs', h₄ _ hs', c'.e.right_inv htg]`. Both sides reduce to the same expression. Rewrite using `[chernMat, AlgChart.hess, c₁.e.right_inv hu]`.
-/
theorem fibre (r e : ℕ) : ∃ t : ℝ, ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k)
    (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E r) (H : h.IsCInf) (N : HermLB q)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) r) (L : Option (Fin r) → HermLB p),
    IsArithVar q (e + 2) → IsArithVar p (e + 2 + r.choose 2) → π (genericPoint Y) = genericPoint B →
    IsFlagBundle π (fun _ : Unit => E) (fun _ => r) (fun _ => fl) → (L none).Isometric (N.pull π w) →
    (∀ i, (L (some i)).Isometric (VMetric.grLB fl i (H.pull π w))) →
    ∀ (I : Type) [Fintype I] (c : I → ℝ) (m : I → Option (Fin r) → ℤ),
    ∑ j, c j • lin (fun o => (m j o : ℝ)) ^ (e + 2 + r.choose 2) = vdmPol r e → ∀ (σ : k →+* ℂ) (f : CxPts q σ → ℝ),
    Measurable f → (∀ j, ((comb L (m j)).φ σ).ChernIntegrableOn (e + 2 + r.choose 2) Set.univ
      fun v => f (PtsOver.map π w (spMap σ) v)) →
    ∑ j, c j * ((comb L (m j)).φ σ).chernInt (e + 2 + r.choose 2) Set.univ (fun v => f (PtsOver.map π w (spMap σ) v)) =
      densInt (fun ch y => t * secondChernDensityOfMetric (h.met σ) (N.φ σ) e ch y) f := by
  obtain ⟨t, ht⟩ := GlobalTheory.T.vandermonde_integral_density r e
  refine ⟨t, fun k _ B Y _ _ q p π w E h H N fl L hZ hY hgen hfl iN iG I _ c m hcm σ f hf hint => ?_⟩
  obtain ⟨ε⟩ : Nonempty (Fin (e + 2 + r.choose 2) ≃ Fin (e + 2) ⊕ Low r) :=
    ⟨Fintype.equivOfCardEq (by simp [card_low_eq])⟩
  generalize e + 2 + r.choose 2 = D at *
  have := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  have hD (j) : IsDens fun (ch : AlgChart p σ D) v => ch.chernDens ((comb L (m j)).φ σ) v :=
    isDens_chernDens (HermLB.cInf _ σ)
  obtain ⟨l₁, l₂⟩ := GlobalTheory.T.density_integral_linear_combination k _ _ σ D I c _ _ hD fun j => (densInt_chernDens _ _).2.2 (hint j)
  have hch := GlobalTheory.T.second_chern_density_chart_formula k _ _ σ _ r (h.met σ) _ (N.φ σ) e (H σ) (N.cInf σ)
  simp only [← (densInt_chernDens _ _).1]
  refine l₂.symm.trans ?_
  refine GlobalTheory.T.density_pushforward_integral k _ _ _ _ π w _ r _ ε σ hZ hY hgen _ _ _ (IsDens.sum _ fun j => (hD j).mul continuous_const)
    (hch.1.mul continuous_const) hf l₁ fun c₀ y₀ hy₀ => ?_
  obtain ⟨c₁, cE, c', h₁, h₂, h₃, h₄⟩ := GlobalTheory.T.flag_bundle_chart_lift_bis k _ _ _ _ π w _ r _ ε σ _ _ H fl hfl c₀ y₀ hy₀
  refine ⟨c₁, c', h₁, h₃, fun u hu => ?_⟩
  have hu' := c₁.e.map_target hu
  rw [hch.2 c₁ cE _ hu' (h₂ hu'), c₁.e.right_inv hu]
  have hG := (H σ cE _ (h₂ hu')).mContDiffAt c₁ hu'
  have hψ := (N.cInf σ).contDiffAt c₁ hu' (mem_pick (N.φ σ).isLB _)
  rw [c₁.e.right_inv hu] at hG hψ
  have := ht _ ε _ _ u hG (Filter.eventually_of_mem (c₁.e.open_target.mem_nhds hu) fun v hv =>
    (h.met σ).posDef _ _ (h₂ (c₁.e.map_target hv))) hψ I c m hcm
  refine Eq.trans (integral_congr_ae (.of_forall fun x => Finset.sum_congr rfl fun j _ => ?_)) (this.trans ?_)
  · have htg : pt ε u x ∈ c'.e.target := by
      rw [h₃.2.1]
      simpa only [Set.mem_setOf_eq, base_pt] using hu
    have hs' := c'.e.map_target htg
    have hb : PtsOver.map π w (spMap σ) (c'.e.symm (pt ε u x)) = c₁.e.symm u := by
      have := h₃.2.2 _ hs'
      rw [c'.e.right_inv htg, base_pt] at this
      exact (c₁.e.left_inv (h₃.1.le hs').1).symm.trans (congrArg c₁.e.symm this.symm)
    refine congrArg (fun A : Matrix (Fin D) (Fin D) ℂ => c j * (D.factorial / Real.pi ^ D * A.det.re))
      ((GlobalTheory.MixDens.chernMat_comb k _ _ σ _ _ _ (m j) c' _ hs').trans (Finset.sum_congr rfl fun o _ => congrArg _ ?_))
    rcases o with _ | i
    · rw [MixDens.chernMat_congr iN c' hs', GlobalTheory.T.chern_matrix_pullback_cell k _ _ _ _ π w _ r _ ε σ c₁ c' h₃ _ _ hs', hb, c'.e.right_inv htg]
      rfl
    · rw [MixDens.chernMat_congr (iG i) c' hs', h₄ _ hs', c'.e.right_inv htg]
      rfl
  · rw [chernMat, AlgChart.hess, c₁.e.right_inv hu]

/- English proof (translation)
Take `⟨t, ht⟩` from `fibre r e`. Use `⟨t, fun k _ X _ _ p d hX E F z he => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hE : IsVB E r`. Use `swap`. Conclude with `.inl fun h => absurd h.isVB hE`.

Take `⟨hY, hsm, hz⟩` from `(GlobalTheory.T.flag_variety_arith_dimension k X p d hX E r hE).2 F`. Take `⟨y, hy, hcl, hd⟩` from `hz z`. Take `⟨I, _, c, m, hcm⟩` from `exists_sum_lin_pow (isHomogeneous_vdmPol r e)`. Establish `key (h : VMetric p E r) (H : h.IsCInf) (N M : HermLB p) (s : M.B.Sec) (hs : z ∈ Out.nonzeroLocus s) : F.arch H N M s z e = ∑ j, c j * chInt (comb (fun o => (F.fam H N o).restr (redι (clo y))) (m j)) (e + 2 + r.choose 2) fun σ v => Real.log ((M.φ σ).nsq (secVal p σ s) (PtsOver.map …`. Take `⟨y', Λ, hy', hΛ, hv⟩ : F.IsArch H N M s z e (F.arch H N M s z e)` from `Classical.epsilon_spec ((existsUnique_val_arch hC k X p d hX E r h H F N z e).2 he M s hs).exists`.

Take `rfl` from `isTop_unique hy hy'`. Rewrite using `[← hv, ← hcm, map_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [map_smul, hΛ.1, smul_eq_mul]`. Break down `hY.vertical_or_horizontal (redι (clo y)) with ⟨ℓ, _, ⟨_⟩⟩ | ⟨hc, -⟩` into its components or cases. Use `.inl fun h H N M s hs => (key h H N M s hs).trans (Finset.sum_eq_zero fun j _ => mul_eq_zero_of_right _ (finsum_eq_zero_of_forall_eq_zero fun σ => ?_))` and prove the remaining obligations.

Use `isEmpty_cxPts (p := redι (clo y) ≫ F.π ≫ p) ℓ σ` as an intermediate fact. Simplify using `[Weight.chernInt, integral_of_isEmpty]`. Use `.inr fun h H N M s hs => ?_` and prove the remaining obligations. Take `⟨ρ, hρ, w, fl, hfl, iN, iG⟩` from `GlobalTheory.T.smooth_closure_reduced_subscheme_map k X p E r h H F N z y hsm hcl`. Establish `hc' : CharZero Γ((Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme, ⊤)` using `ρ.appTop.hom.charZero`.

Use `⟨hc', ?_⟩` and prove the remaining obligations. Establish `hZ : IsArithVar (redι (clo z) ≫ p) (e + 2)` using `hX.of_isClosedImmersion _ hc' ((dim_clo z).trans he)`. Establish `hY' : IsArithVar (redι (clo y) ≫ F.π ≫ p) (e + 2 + r.choose 2)` using `hY.of_isClosedImmersion _ hc (by`. Rewrite using `[dim_clo, hd _ he]`. Use `congr 1`.

Use the proof step `omega)`. Establish `hgen : ρ (genericPoint _) = genericPoint _` using `(redι (clo z)).isClosedEmbedding.injective (by`. Rewrite using `[redι_clo, ← Scheme.Hom.comp_apply, hρ, Scheme.Hom.comp_apply, redι_clo, hy.1])`. Use `hX.finite_emb` as an intermediate fact. Use `Fintype.ofFinite (k →+* ℂ)` as an intermediate fact.

Rewrite using `[key h H N M s hs]`. Simplify using `only [chInt, finsum_eq_sum_of_fintype, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Establish `hf (v) : PtsOver.map (redι (clo y) ≫ F.π) (Category.assoc _ _ _) (spMap σ) v = PtsOver.map (redι (clo z)) rfl (spMap σ) (PtsOver.map ρ w (spMap σ) v)` using `Subtype.ext ((congrArg (v.1 ≫ ·) hρ.symm).trans (Category.assoc _ _ _).symm)`.

Simplify using `only [hf]`. Use `ht k _ _ _ _ ρ w _ _ (H.pull (redι (clo z)) rfl) (N.pull (redι (clo z)) rfl) fl (fun o => (F.fam H N o).restr (redι (clo y))) hZ hY' hgen hfl iN iG I c m hcm σ (fun y => Real.log ((M.φ σ).nsq (secVal p σ s) (PtsOver.map (redι (clo z)) rfl (spMap σ) y)) / 2) ((((M.cInf σ).continuo …` and prove the remaining obligations. Use `chernIntegrableOn_log hC hY' (fun o => (F.fam H N o).restr (redι (clo y))) (m j) (M.pull (redι (clo y) ≫ F.π) (Category.assoc _ _ _)) (Cartier.secPull s _) (by` as an intermediate fact. Use `(Cartier.nonzeroLocus_secPull s _).ge ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `F.π (redι (clo y) (genericPoint _)) ∈ Out.nonzeroLocus s`.

Rewrite using `[redι_clo, hy.1]`. Conclude with `hs) σ`. Use `this.congr MeasurableSet.univ fun v _ => ?_` and prove the remaining obligations. Conclude with `congrArg (Real.log · / 2) (((M.φ σ).nsq_pull_secPull (redι (clo y) ≫ F.π) (Category.assoc _ _ _) s v).trans (congrArg _ (hf v)))`.
-/
theorem arch_eq (hC : ArCalc) (r e : ℕ) : ∃ t : ℝ, ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    [IsLocallyNoetherian X] (p : X ⟶ Sp k) (d : ℕ), IsArithVar p d → ∀ (E : X.Modules) (F : FlagSp E r) (z : X),
    topologicalKrullDim (closure ({z} : Set X)) = (e + 3 : ℕ) →
    (∀ (h : VMetric p E r) (H : h.IsCInf) (N M : HermLB p) (s : M.B.Sec), z ∈ Out.nonzeroLocus s → F.arch H N M s z e = 0) ∨
    (∀ (h : VMetric p E r) (H : h.IsCInf) (N M : HermLB p) (s : M.B.Sec), z ∈ Out.nonzeroLocus s →
      CharZero Γ((Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme, ⊤) ∧
        F.arch H N M s z e = ∑ᶠ σ, densInt (fun c y => t * secondChernDensityOfMetric ((h.pull (redι (clo z)) rfl).met σ)
          ((N.pull (redι (clo z)) rfl).φ σ) e c y)
          fun y => Real.log ((M.φ σ).nsq (secVal p σ s) (PtsOver.map (redι (clo z)) rfl (spMap σ) y)) / 2) := by
  obtain ⟨t, ht⟩ := fibre r e
  refine ⟨t, fun k _ X _ _ p d hX E F z he => ?_⟩
  by_cases hE : IsVB E r
  swap
  · exact .inl fun h => absurd h.isVB hE
  obtain ⟨hY, hsm, hz⟩ := (GlobalTheory.T.flag_variety_arith_dimension k X p d hX E r hE).2 F
  obtain ⟨y, hy, hcl, hd⟩ := hz z
  obtain ⟨I, _, c, m, hcm⟩ := exists_sum_lin_pow (isHomogeneous_vdmPol r e)
  have key (h : VMetric p E r) (H : h.IsCInf) (N M : HermLB p) (s : M.B.Sec) (hs : z ∈ Out.nonzeroLocus s) :
      F.arch H N M s z e = ∑ j, c j * chInt (comb (fun o => (F.fam H N o).restr (redι (clo y))) (m j)) (e + 2 + r.choose 2)
        fun σ v => Real.log ((M.φ σ).nsq (secVal p σ s)
          (PtsOver.map (redι (clo y) ≫ F.π) (Category.assoc _ _ _) (spMap σ) v)) / 2 := by
    obtain ⟨y', Λ, hy', hΛ, hv⟩ : F.IsArch H N M s z e (F.arch H N M s z e) :=
      Classical.epsilon_spec ((existsUnique_val_arch hC k X p d hX E r h H F N z e).2 he M s hs).exists
    obtain rfl := isTop_unique hy hy'
    rw [← hv, ← hcm, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hΛ.1, smul_eq_mul]
  rcases hY.vertical_or_horizontal (redι (clo y)) with ⟨ℓ, _, ⟨_⟩⟩ | ⟨hc, -⟩
  · refine .inl fun h H N M s hs => (key h H N M s hs).trans (Finset.sum_eq_zero fun j _ => mul_eq_zero_of_right _
      (finsum_eq_zero_of_forall_eq_zero fun σ => ?_))
    have := isEmpty_cxPts (p := redι (clo y) ≫ F.π ≫ p) ℓ σ
    simp [Weight.chernInt, integral_of_isEmpty]
  refine .inr fun h H N M s hs => ?_
  obtain ⟨ρ, hρ, w, fl, hfl, iN, iG⟩ := GlobalTheory.T.smooth_closure_reduced_subscheme_map k X p E r h H F N z y hsm hcl
  have hc' : CharZero Γ((Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme, ⊤) := ρ.appTop.hom.charZero
  refine ⟨hc', ?_⟩
  have hZ : IsArithVar (redι (clo z) ≫ p) (e + 2) := hX.of_isClosedImmersion _ hc' ((dim_clo z).trans he)
  have hY' : IsArithVar (redι (clo y) ≫ F.π ≫ p) (e + 2 + r.choose 2) := hY.of_isClosedImmersion _ hc (by
    rw [dim_clo, hd _ he]
    congr 1
    omega)
  have hgen : ρ (genericPoint _) = genericPoint _ := (redι (clo z)).isClosedEmbedding.injective (by
    rw [redι_clo, ← Scheme.Hom.comp_apply, hρ, Scheme.Hom.comp_apply, redι_clo, hy.1])
  have := hX.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  rw [key h H N M s hs]
  simp only [chInt, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hf (v) : PtsOver.map (redι (clo y) ≫ F.π) (Category.assoc _ _ _) (spMap σ) v =
      PtsOver.map (redι (clo z)) rfl (spMap σ) (PtsOver.map ρ w (spMap σ) v) :=
    Subtype.ext ((congrArg (v.1 ≫ ·) hρ.symm).trans (Category.assoc _ _ _).symm)
  simp only [hf]
  refine ht k _ _ _ _ ρ w _ _ (H.pull (redι (clo z)) rfl) (N.pull (redι (clo z)) rfl) fl
    (fun o => (F.fam H N o).restr (redι (clo y))) hZ hY' hgen hfl iN iG I c m hcm σ
    (fun y => Real.log ((M.φ σ).nsq (secVal p σ s) (PtsOver.map (redι (clo z)) rfl (spMap σ) y)) / 2)
    ((((M.cInf σ).continuous_nsq s).comp (PtsOver.continuous_map _ _ _)).measurable.log.div_const _) fun j => ?_
  have := chernIntegrableOn_log hC hY' (fun o => (F.fam H N o).restr (redι (clo y))) (m j)
    (M.pull (redι (clo y) ≫ F.π) (Category.assoc _ _ _)) (Cartier.secPull s _) (by
      refine (Cartier.nonzeroLocus_secPull s _).ge ?_
      change F.π (redι (clo y) (genericPoint _)) ∈ Out.nonzeroLocus s
      rw [redι_clo, hy.1]
      exact hs) σ
  refine this.congr MeasurableSet.univ fun v _ => ?_
  exact congrArg (Real.log · / 2) (((M.φ σ).nsq_pull_secPull (redι (clo y) ≫ F.π) (Category.assoc _ _ _) s v).trans
    (congrArg _ (hf v)))

end Fibre

section Point

/- English proof (translation)
Establish `h` using `((Complex.continuous_re.tendsto _).comp (tendsto_finsetSum (Finset.univ : Finset (Equiv.Perm (Fin (e + 2)))) fun s _ => tendsto_finsetSum (Finset.univ : Finset (Equiv.Perm (Fin (e + 2)))) fun t _ => ((hΘ (bas _ (s 0)) (bas _ (t 0)) (bas _ (s 1)) (bas _ (t 1))).mul (tendsto_finset …`. Simplify `h` using `[secondChernDensity, Function.comp_def]`.
-/
theorem tendsto_density_zero {e : ℕ} {Θ : ℝ → V (e + 2) → V (e + 2) → V (e + 2) → V (e + 2) → ℂ}
    {A : ℝ → Matrix (Fin (e + 2)) (Fin (e + 2)) ℂ} {A₀ : Matrix (Fin (e + 2)) (Fin (e + 2)) ℂ}
    (hΘ : ∀ a b c d, Tendsto (fun R => Θ R a b c d) atTop (𝓝 0)) (hA : ∀ a b, Tendsto (fun R => A R a b) atTop (𝓝 (A₀ a b))) :
    Tendsto (fun R => secondChernDensity e (Θ R) (A R)) atTop (𝓝 0) := by
  have h := ((Complex.continuous_re.tendsto _).comp (tendsto_finsetSum (Finset.univ : Finset (Equiv.Perm (Fin (e + 2)))) fun s _ =>
    tendsto_finsetSum (Finset.univ : Finset (Equiv.Perm (Fin (e + 2)))) fun t _ =>
      ((hΘ (bas _ (s 0)) (bas _ (t 0)) (bas _ (s 1)) (bas _ (t 1))).mul
        (tendsto_finsetProd Finset.univ fun (i : Fin e) _ => hA (s i.succ.succ) (t i.succ.succ))).const_mul
          (((Equiv.Perm.sign s * Equiv.Perm.sign t : ℤˣ) : ℤ) : ℂ))).neg.div_const (Real.pi ^ e)
  simpa [secondChernDensity, Function.comp_def] using h

/- English proof (translation)
Establish `e (ξ η i j) : Tendsto (fun R => curv (H R) u ξ η i j) atTop (𝓝 (curv H₀ u ξ η i j))` using `tendsto_pi_nhds.1 (tendsto_pi_nhds.1 (h ξ η) i) j`. Use `Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_)` and prove the remaining obligations. Conclude with `((((e _ _ _ _).mul (e _ _ _ _)).add ((e _ _ _ _).mul (e _ _ _ _))).sub ((e _ _ _ _).mul (e _ _ _ _))).sub ((e _ _ _ _).mul (e _ _ _ _))`.
-/
theorem tendsto_chTwo {n m : ℕ} {H : ℝ → V n → Matrix (Fin m) (Fin m) ℂ} {H₀ : V n → Matrix (Fin m) (Fin m) ℂ} {u : V n}
    (h : ∀ ξ η, Tendsto (fun R => curv (H R) u ξ η) atTop (𝓝 (curv H₀ u ξ η))) (a b c d : V n) :
    Tendsto (fun R => chTwo (H R) u a b c d) atTop (𝓝 (chTwo H₀ u a b c d)) := by
  have e (ξ η i j) : Tendsto (fun R => curv (H R) u ξ η i j) atTop (𝓝 (curv H₀ u ξ η i j)) :=
    tendsto_pi_nhds.1 (tendsto_pi_nhds.1 (h ξ η) i) j
  refine Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_)
  exact ((((e _ _ _ _).mul (e _ _ _ _)).add ((e _ _ _ _).mul (e _ _ _ _))).sub ((e _ _ _ _).mul (e _ _ _ _))).sub
    ((e _ _ _ _).mul (e _ _ _ _))

variable {D : D7} {O : Setup D} {c : O.s.Comp} (M : DRBase O c) {Y : Scheme.{0}} (i : Y ⟶ M.B) (σ : O.κ.c.F →+* ℂ) (e : ℕ)

abbrev dens (R : ℝ) : AlgChart (i ≫ M.q) (σ.comp (algebraMap _ _)) (e + 2) → CxPts (i ≫ M.q) (σ.comp (algebraMap _ _)) → ℝ :=
  secondChernDensityOfMetric ((((M.h R).pull M.b rfl).pull i rfl).met _) (((M.lam R).pull i rfl).φ _) e

abbrev upTo : CxPts (i ≫ M.q) (σ.comp (algebraMap _ _)) → CxPts (genStr O.s.T.Z) σ :=
  up (i ≫ M.b) (Category.assoc _ _ _) σ

/- English proof (translation)
The claim follows from `Subtype.ext (Limits.pullback.hom_ext ((up_ι _ _ _ _).trans ((Category.assoc _ _ _).symm.trans (up_ι M.b rfl σ (PtsOver.map i rfl _ y)).symm)) ((upTo M i σ y).2.trans (up M.b rfl σ _).2.symm))`.
-/
theorem upTo_eq (y : CxPts (i ≫ M.q) (σ.comp (algebraMap _ _))) :
    upTo M i σ y = up M.b rfl σ (PtsOver.map i rfl _ y) :=
  Subtype.ext (Limits.pullback.hom_ext ((up_ι _ _ _ _).trans ((Category.assoc _ _ _).symm.trans (up_ι M.b rfl σ (PtsOver.map i rfl _ y)).symm))
    ((upTo M i σ y).2.trans (up M.b rfl σ _).2.symm))

/- English proof (translation)
Take `⟨U, a, hU, hu, hH, hc, ha, hR⟩` from `GlobalTheory.T.exists_holomorphic_frame_near_boundary D O c M Y i (Category.assoc _ _ _) σ e ch y hy`. Establish `hi : Inner (a (ch.e y)).1` using `by rwa [ha _ hu, ch.e.left_inv hy]`. Establish `h₁` using `GlobalTheory.T.eigen_curvature_tendsto_hodge D _ _ _ _ _ O.s M.x σ _ U a hU hH hc _ hu hi`. Use `(tendsto_density_zero (A₀ := Matrix.of fun a' b' => -∑ τ, (curv (eigGram (M.x.hodge σ) a τ) (ch.e y) (bas _ a') (bas _ b')).trace) (fun a' b' c' d' => ?_) fun a' b' => ?_).congr fun R => (hR R).2.symm` and prove the remaining obligations. Rewrite using `[← GlobalTheory.T.sum_second_chern_hodge_vanishes D _ _ _ _ _ O.s M.x σ _ U a hU hH hc _ hu hi a' b' c' d']`.

Conclude with `tendsto_finsetSum _ fun τ _ => tendsto_chTwo (h₁ τ) _ _ _ _`. Conclude with `(tendsto_finsetSum _ fun τ _ => ((continuous_id.matrix_trace).tendsto _).comp (h₁ τ _ _)).neg`.
-/
theorem tendsto_dens (ch : AlgChart (i ≫ M.q) (σ.comp (algebraMap _ _)) (e + 2)) {y} (hy : y ∈ ch.e.source)
    (hin : Inner (upTo M i σ y)) : Tendsto (fun R => dens M i σ e R ch y) atTop (𝓝 0) := by
  obtain ⟨U, a, hU, hu, hH, hc, ha, hR⟩ := GlobalTheory.T.exists_holomorphic_frame_near_boundary D O c M Y i (Category.assoc _ _ _) σ e ch y hy
  have hi : Inner (a (ch.e y)).1 := by rwa [ha _ hu, ch.e.left_inv hy]
  have h₁ := GlobalTheory.T.eigen_curvature_tendsto_hodge D _ _ _ _ _ O.s M.x σ _ U a hU hH hc _ hu hi
  refine (tendsto_density_zero (A₀ := Matrix.of fun a' b' =>
    -∑ τ, (curv (eigGram (M.x.hodge σ) a τ) (ch.e y) (bas _ a') (bas _ b')).trace) (fun a' b' c' d' => ?_)
      fun a' b' => ?_).congr fun R => (hR R).2.symm
  · rw [← GlobalTheory.T.sum_second_chern_hodge_vanishes D _ _ _ _ _ O.s M.x σ _ U a hU hH hc _ hu hi a' b' c' d']
    exact tendsto_finsetSum _ fun τ _ => tendsto_chTwo (h₁ τ) _ _ _ _
  · exact (tendsto_finsetSum _ fun τ _ => ((continuous_id.matrix_trace).tendsto _).comp (h₁ τ _ _)).neg

/- English proof (translation)
Take `⟨C', h0, hC⟩` from `GlobalTheory.T.second_chern_density_curvature_bound e (D.host.E →+* ℂ) O.S.Dw.mult C`. Establish `hk : (0 : ℝ) < (e + 2).factorial * (2 / Real.pi) ^ (e + 2)` using `by positivity`. Use `⟨C' / ((e + 2).factorial * (2 / Real.pi) ^ (e + 2)), by positivity, fun R hR ch y hy hin => ?_⟩` and prove the remaining obligations. Take `⟨U, a, hU, hu, hH, hc, ha, hR'⟩` from `GlobalTheory.T.exists_holomorphic_frame_near_boundary D O c M Y i (Category.assoc _ _ _) σ e ch y hy`. Establish `h₁ : (a (ch.e y)).1 = upTo M i σ y` using `by rw [ha _ hu, ch.e.left_inv hy]`.

Take `⟨h₂, h₃⟩` from `hP _ U a hU hH hc _ hu (h₁ ▸ hin)`. Establish `h₄ : cHess (e + 2) (fun v => (P.φ (a (ch.e y)).1 (a v).1 : ℂ)) (ch.e y) = potMat P (upTo M i σ) ch y`. Use `ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_` and prove the remaining obligations. Use `filter_upwards [hU.mem_nhds hu] with v hv`. Rewrite using `[h₁, ha v hv]`.

Use `hC U _ (hR' R).1 _ hu _ h₂ (h₃ R hR)` as an intermediate fact. Rewrite `this` using `[← (hR' R).2, h₄]`. Rewrite using `[potDens, if_pos (show upTo M i σ y ∈ {y | Inner y} from hin), ← mul_assoc, div_mul_cancel₀ _ hk.ne']`. Conclude with `this`.
-/
theorem exists_dens_le {P : LocPot (CxPts (genStr O.s.T.Z) σ)} {C : ℝ} (hP : CurvBound M.x σ P C) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ R : ℝ, 2 ≤ R → ∀ ch : AlgChart (i ≫ M.q) (σ.comp (algebraMap _ _)) (e + 2), ∀ y ∈ ch.e.source,
      Inner (upTo M i σ y) → |dens M i σ e R ch y| ≤ C' * potDens P {y | Inner y} (upTo M i σ) ch y := by
  obtain ⟨C', h0, hC⟩ := GlobalTheory.T.second_chern_density_curvature_bound e (D.host.E →+* ℂ) O.S.Dw.mult C
  have hk : (0 : ℝ) < (e + 2).factorial * (2 / Real.pi) ^ (e + 2) := by positivity
  refine ⟨C' / ((e + 2).factorial * (2 / Real.pi) ^ (e + 2)), by positivity, fun R hR ch y hy hin => ?_⟩
  obtain ⟨U, a, hU, hu, hH, hc, ha, hR'⟩ := GlobalTheory.T.exists_holomorphic_frame_near_boundary D O c M Y i (Category.assoc _ _ _) σ e ch y hy
  have h₁ : (a (ch.e y)).1 = upTo M i σ y := by rw [ha _ hu, ch.e.left_inv hy]
  obtain ⟨h₂, h₃⟩ := hP _ U a hU hH hc _ hu (h₁ ▸ hin)
  have h₄ : cHess (e + 2) (fun v => (P.φ (a (ch.e y)).1 (a v).1 : ℂ)) (ch.e y) = potMat P (upTo M i σ) ch y := by
    refine ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_
    filter_upwards [hU.mem_nhds hu] with v hv
    rw [h₁, ha v hv]
  have := hC U _ (hR' R).1 _ hu _ h₂ (h₃ R hR)
  rw [← (hR' R).2, h₄] at this
  rw [potDens, if_pos (show upTo M i σ y ∈ {y | Inner y} from hin), ← mul_assoc, div_mul_cancel₀ _ hk.ne']
  exact this

end Point

section Limit

/- English proof (translation)
Establish `he : 1 ≤ Real.exp 1` using `Real.one_le_exp zero_le_one`. Establish `ht (i) : 0 ≤ -2 * Real.log (n i)` using `by linarith [Real.log_nonpos (h i).1 (h i).2]`. Establish `h₁ : ∀ s : Finset (Fin m), 1 + ∑ i ∈ s, -2 * Real.log (n i) ≤ ∏ i ∈ s, (Real.exp 1 - 2 * Real.log (n i))` using `fun s => by`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`.

Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha]`. Use `Finset.sum_nonneg fun i (_ : i ∈ s) => ht i` as an intermediate fact. Use polynomial arithmetic with `[ht a, mul_le_mul_of_nonneg_left ih (show 0 ≤ Real.exp 1 - 2 * Real.log (n a) by linarith [ht a])]`. Establish `h₂ : -Real.log ((∏ i, n i) ^ 2) ≤ ∑ i, -2 * Real.log (n i)`.

Distinguish the cases in `h0 : ∀ i, n i ≠ 0`. Rewrite using `[Real.log_pow, Real.log_prod fun i _ => h0 i, ← Finset.mul_sum]`. Simplify using the standard rewrite rules. Take `⟨i, hi⟩` from `not_forall.1 h0`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ i) (not_not.1 hi)]`.

Simplify using `using Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => ht i`. Establish `h₃ : Real.log ((∏ i, n i) ^ 2) ≤ 0` using `Real.log_nonpos (sq_nonneg _) (pow_le_one₀ (Finset.prod_nonneg fun i _ => (h i).1) (Finset.prod_le_one (fun i _ => (h i).1) fun i _ => (h i).2))`. Establish `h₄` using `Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => ht i`. Rewrite using `[← Real.log_prod fun i _ => by linarith [ht i], ← Real.log_exp 1, Real.exp_log (by linarith), ← Real.log_mul (by linarith) (by linarith [h₁ Finset.univ])]`. Use `Real.log_le_log (by linarith) ?_` and prove the remaining obligations.

Use polynomial arithmetic with `[h₁ Finset.univ]`.
-/
theorem log_r_le {m : ℕ} {n : Fin m → ℝ} (h : ∀ i, 0 ≤ n i ∧ n i ≤ 1) :
    Real.log (Real.exp 1 - Real.log ((∏ i, n i) ^ 2)) ≤ 1 + ∑ i, Real.log (Real.exp 1 - 2 * Real.log (n i)) := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have ht (i) : 0 ≤ -2 * Real.log (n i) := by linarith [Real.log_nonpos (h i).1 (h i).2]
  have h₁ : ∀ s : Finset (Fin m), 1 + ∑ i ∈ s, -2 * Real.log (n i) ≤ ∏ i ∈ s, (Real.exp 1 - 2 * Real.log (n i)) := fun s => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have := Finset.sum_nonneg fun i (_ : i ∈ s) => ht i
      nlinarith [ht a, mul_le_mul_of_nonneg_left ih (show 0 ≤ Real.exp 1 - 2 * Real.log (n a) by linarith [ht a])]
  have h₂ : -Real.log ((∏ i, n i) ^ 2) ≤ ∑ i, -2 * Real.log (n i) := by
    by_cases h0 : ∀ i, n i ≠ 0
    · rw [Real.log_pow, Real.log_prod fun i _ => h0 i, ← Finset.mul_sum]
      simp
    · obtain ⟨i, hi⟩ := not_forall.1 h0
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (not_not.1 hi)]
      simpa using Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => ht i
  have h₃ : Real.log ((∏ i, n i) ^ 2) ≤ 0 := Real.log_nonpos (sq_nonneg _) (pow_le_one₀
    (Finset.prod_nonneg fun i _ => (h i).1) (Finset.prod_le_one (fun i _ => (h i).1) fun i _ => (h i).2))
  have h₄ := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => ht i
  rw [← Real.log_prod fun i _ => by linarith [ht i], ← Real.log_exp 1, Real.exp_log (by linarith),
    ← Real.log_mul (by linarith) (by linarith [h₁ Finset.univ])]
  refine Real.log_le_log (by linarith) ?_
  nlinarith [h₁ Finset.univ]

/- English proof (translation)
Rewrite using `[RingHom.injective_iff_ker_eq_bot]`. Use `Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_` and prove the remaining obligations. Rewrite using `[RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]`. Conclude with `RingHom.injective_int _`.
-/
theorem injective_emb {F : Type} [Field F] [NumberField F] (σ : 𝓞 F →+* ℂ) : Function.Injective σ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
  rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  exact RingHom.injective_int _

/- English proof (translation)
Assemble the required witnesses or components as `⟨IsFractionRing.lift (K := F) (injective_emb σ₀), RingHom.ext fun x => IsFractionRing.lift_algebraMap (K := F) (injective_emb σ₀) x⟩`.
-/
theorem exists_comp_eq {F : Type} [Field F] [NumberField F] (σ₀ : 𝓞 F →+* ℂ) :
    ∃ σ : F →+* ℂ, σ.comp (algebraMap _ _) = σ₀ :=
  ⟨IsFractionRing.lift (K := F) (injective_emb σ₀), RingHom.ext fun x =>
    IsFractionRing.lift_algebraMap (K := F) (injective_emb σ₀) x⟩

/- English proof (translation)
Establish `hi` using `mem_pick φ.isLB y`. Rewrite using `[Weight.nsq, mul_ne_zero_iff_right (Real.exp_ne_zero _), pow_ne_zero_iff two_ne_zero, norm_ne_zero_iff, secVal_apply, ← mem_ptsIn_basicOpen hi, mem_ptsIn]`. Conclude with `(mem_nonzeroLocus_iff s _ (mem_ptsIn.1 hi)).symm`.
-/
theorem nsq_ne_zero_iff {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {B : LB X} (φ : Weight p σ B)
    (s : B.Sec) (y : CxPts p σ) : φ.nsq (secVal p σ s) y ≠ 0 ↔ y.1 (IsLocalRing.closedPoint ℂ) ∈ Out.nonzeroLocus s := by
  have hi := mem_pick φ.isLB y
  rw [Weight.nsq, mul_ne_zero_iff_right (Real.exp_ne_zero _), pow_ne_zero_iff two_ne_zero, norm_ne_zero_iff, secVal_apply,
    ← mem_ptsIn_basicOpen hi, mem_ptsIn]
  exact (mem_nonzeroLocus_iff s _ (mem_ptsIn.1 hi)).symm

/- English proof (translation)
Establish `: CharZero Z.functionField` using `charZero_of_injective_ringHom (germ_injective_of_isIntegral Z (U := ⊤) _ trivial)`. Conclude with `charZero_of_injective_ringHom (f := (Z.residue (genericPoint Z)).hom) (RingHom.injective (R := Z.functionField) _)`.
-/
theorem charZero_residueField {Z : Scheme.{0}} [IsIntegral Z] (h : CharZero Γ(Z, ⊤)) :
    CharZero (Z.residueField (genericPoint Z)) := by
  have : CharZero Z.functionField := charZero_of_injective_ringHom (germ_injective_of_isIntegral Z (U := ⊤) _ trivial)
  exact charZero_of_injective_ringHom (f := (Z.residue (genericPoint Z)).hom)
    (RingHom.injective (R := Z.functionField) _)

variable {D : D7} {O : Setup D} {c : O.s.Comp} {M : DRBase O c} {I : M.Emb} {z : M.B} {e m : ℕ} {s : (lbPow M.lamB m).Sec}

/- English proof (translation)
Assume the negation of the conclusion as `hv`. Establish `: IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme` using `LocallyOfFiniteType.isLocallyNoetherian (redι (clo z))`. Establish `hs : genericPoint _ ∈ Out.nonzeroLocus (GlobalTheory.ZM.RepBC.secPull _ (redι (clo z)) s)`. Express the relevant statement in the definitionally equal form `_ ∈ Out.nonzeroLocus (Cartier.secPull s (redι (clo z)))`. Rewrite using `[Cartier.nonzeroLocus_secPull]`.

Express the relevant statement in the definitionally equal form `redι (clo z) (genericPoint _) ∈ Out.nonzeroLocus s`. Rewrite using `[redι_clo]`. Conclude with `hC.1`. Use `(hC.2 (redι (clo z) v) ?_).2.2 ((redι (clo z)).residueFieldMap v).hom.charZero hb` and prove the remaining obligations. Rewrite using `[cutMult, dif_pos hs, (redι (clo z)).isClosedEmbedding.injective.extend_apply]`.

Conclude with `SecCycle.mult_divOfSec_ne_zero _ _ hs h1 fun h => hv ((Cartier.nonzeroLocus_secPull s _).le h)`.
-/
theorem mem_nonzeroLocus_of_cuts (hC : I.Cuts s z e) {v : (Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme}
    (hb : (redι (clo z) ≫ M.b) v ∉ abLocus O.s.T.Z.t.G)
    (hc : CharZero ((Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme.residueField v)) (h1 : Order.coheight v = 1) :
    redι (clo z) v ∈ Out.nonzeroLocus s := by
  by_contra hv
  have : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (redι (clo z))
  have hs : genericPoint _ ∈ Out.nonzeroLocus (GlobalTheory.ZM.RepBC.secPull _ (redι (clo z)) s) := by
    change _ ∈ Out.nonzeroLocus (Cartier.secPull s (redι (clo z)))
    rw [Cartier.nonzeroLocus_secPull]
    change redι (clo z) (genericPoint _) ∈ Out.nonzeroLocus s
    rw [redι_clo]
    exact hC.1
  refine (hC.2 (redι (clo z) v) ?_).2.2 ((redι (clo z)).residueFieldMap v).hom.charZero hb
  rw [cutMult, dif_pos hs, (redι (clo z)).isClosedEmbedding.injective.extend_apply]
  exact SecCycle.mult_divOfSec_ne_zero _ _ hs h1 fun h => hv ((Cartier.nonzeroLocus_secPull s _).le h)

/- English proof (translation)
Establish `hproj : IsProjOver (genStr O.s.T.Z)` using `(GlobalTheory.ProjSpace.points_and_stability _ 0).2.2.1 _ _ _ _ O.s.T.Z.proj`. Establish `: CompactSpace (CxPts (genStr O.s.T.Z) σ)` using `PtsOver.compactSpace hproj _`. Use `CxPts.t2Space_cxPts_of_isProjOver σ hproj` as an intermediate fact. Use `CxPts.secondCountableTopology_of_isProjOver (σ.comp (algebraMap _ _)) hZ.isProjOver` as an intermediate fact. Use `(isNoetherian_of_isProjOver O.s.T.Z.proj).toIsLocallyNoetherian` as an intermediate fact.

Establish `hA` using `GlobalTheory.T.compact_projective_analytic _ _ _ σ _ (manifold O.s.T.Z σ) hproj`. Take `⟨α, Λ, sg, t₀, C, hB, hn, hcont, hbd, hcurv⟩` from `GlobalTheory.T.boundary_setting_curvature_bound D _ _ _ _ _ O.s M.x σ`. Establish `hw` using `GlobalTheory.T.boundary_setting_restrict_subvariety D _ _ _ _ _ O.s σ _ α Λ sg t₀ hB Y _ (i ≫ M.b) (Category.assoc _ _ _) (e + 2)`. Take `⟨q, Zs, T₀, h₁, h₂, hirr, hloc, hdom, hcomp⟩` from `GlobalTheory.T.exists_boundary_strata_subvariety D _ _ _ _ _ O.s M.x σ Y _ (i ≫ M.b) (Category.assoc _ _ _) (e + 2) hZ hgen`. Establish `hop : IsOpen {y : CxPts (genStr O.s.T.Z) σ | Inner y}` using `isOpen_not_liesIn _`.

Establish `hmeas` using `GlobalTheory.T.boundary_integral_off_strata D _ _ _ _ _ O.s σ Y _ (i ≫ M.b) (Category.assoc _ _ _) (e + 2) hZ q Zs T₀ h₁ h₂ hloc (poincarePot α Λ sg t₀) (boundary sg) (hbd ▸ hop.isClosed_compl) (GlobalTheory.PoincSmooth.smoothOn_nhd_off_boundary _ _ _ _ α Λ sg t₀ hB.1 (fun i => ⟨ …`. Establish `hTc : IsClosed {v : Y | (i ≫ M.b) v ∉ abLocus O.s.T.Z.t.G}` using `((GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian _ O.s.T.Z.t.semi).preimage (i ≫ M.b).continuous).isClosed_compl`. Establish `hSc : IsClosed {v : Y | i v ∉ Out.nonzeroLocus s}` using `((Out.nonzeroLocus s).isOpen.preimage i.continuous).isClosed_compl`. Establish `hnb (a) : ¬ Zs a ⊆ boundary sg` using `fun h => by`. Take `⟨y, hy, hy'⟩` from `hdom a _ hTc (not_not.2 hgen)`.

Conclude with `(hbd.le (h hy)) ((inner_up _ _ _ _).2 (not_not.1 hy'))`. Establish `hu : Continuous (upTo M i σ)` using `continuous_up _ _ _`. Establish `hr1 (y) : 1 ≤ Real.log (M.x.r σ y)` using `(Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le (M.x.exp_le_r σ y))).2 (M.x.exp_le_r σ y)`. Establish `i₁ : Integrable (fun y => Real.log (M.x.r σ (upTo M i σ y))) (part (D` using `e + 2) (potDens (poincarePot α Λ sg t₀) (boundary sg)ᶜ (upTo M i σ))) := by`. Use `⟨((((continuous_finsetProd _ fun j _ => (hcont j).comp hu).pow 2).measurable.log.const_sub _).log).aestronglyMeasurable, (lintegral_mono fun y => ?_).trans_lt ((hmeas _).trans_lt (ENNReal.sum_lt_top.2 fun a _ => GlobalTheory.T.regular_integral_boundary_potential hL hD _ _ _ hA _ …` and prove the remaining obligations.

Rewrite using `[Real.enorm_of_nonneg (zero_le_one.trans (hr1 _))]`. Use `ENNReal.ofReal_le_ofReal ((log_r_le fun j => (M.x.nrm_div σ j).1 _).trans_eq ?_)` and prove the remaining obligations. Simplify using `only [← hn]`. Both sides reduce to the same expression. Take `⟨L, sL, a, ha, hLp, hLs, hL1, hLn⟩` from `GlobalTheory.T.exists_potential_section_bounded D O c M m s σ`.

Establish `hsL (y) : sL (upTo M i σ y) (upTo M i σ y) ≠ 0 ↔ i (y.1 (IsLocalRing.closedPoint ℂ)) ∈ Out.nonzeroLocus s`. Use `Iff.trans ?_ (nsq_ne_zero_iff (((M.lam 2).pow m).φ _) s (PtsOver.map i rfl _ y))` and prove the remaining obligations. Rewrite using `[← mul_ne_zero_iff_left ha.ne', ← hLn, ← upTo_eq, pow_ne_zero_iff two_ne_zero, normSec, mul_ne_zero_iff_right (Real.exp_ne_zero _), norm_ne_zero_iff]`. Establish `hmf (R : ℝ) : Continuous fun y => (((M.lam R).pow m).φ (σ.comp (algebraMap _ _))).nsq (secVal M.q _ s) (PtsOver.map i rfl _ y)` using `((HermLB.cInf _ _).continuous_nsq _).comp (PtsOver.continuous_map _ _ _)`. Establish `i₂ : Integrable (fun y => Real.log (a * (((M.lam 2).pow m).φ _).nsq (secVal M.q _ s) (PtsOver.map i rfl _ y)) / 2) (part (D` using `e + 2) (potDens (poincarePot α Λ sg t₀) (boundary sg)ᶜ (upTo M i σ))) := by`.

Use `⟨((continuous_const.mul (hmf 2)).measurable.log.div_const _).aestronglyMeasurable, (lintegral_mono fun y => ?_).trans_lt ((hmeas (absLogNorm L sL)).trans_lt (ENNReal.sum_lt_top.2 fun b _ => GlobalTheory.T.log_norm_integrable_poincare hL hD _ _ _ hA _ α Λ sg t₀ hB _ _ (hirr b).1 ( …` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[← hLn, ← upTo_eq, Real.log_pow, absLogNorm]`. Use `split_ifs`. Conclude with `le_top`.

Rewrite using `[Real.enorm_eq_ofReal_abs, Nat.cast_ofNat, mul_div_cancel_left₀ _ two_ne_zero]`. Both sides reduce to the same expression. Take `⟨y, hy, hy'⟩` from `hdom b _ hSc (not_not.2 hzs)`. Conclude with `⟨_, hy, (hsL y).2 (not_not.1 hy')⟩`. Assume the negation of the conclusion as `hK'`.

Take `⟨v, hv, hv₁, hv₂, hv₃⟩` from `hcomp b K (hbd ▸ hK) _ hSc fun y hy h => hK' ⟨_, hy, (hsL y).2 h⟩`. Conclude with `hv (hcut v hv₁ hv₂ hv₃)`. Take `⟨C₁, hC₁, hlog⟩` from `GlobalTheory.T.log_norm_section_difference_bound D O c M m s`. Take `⟨C₂, hC₂, hle⟩` from `exists_dens_le M i σ e hcurv`. Establish `hS : (boundary sg)ᶜ = {y | Inner y}`.

Rewrite using `[hbd]`. Conclude with `compl_compl {y | Inner y}`. Rewrite `hw`, `i₁`, `i₂` using `[hS]`. Use `set g := fun y => Real.log (a * (((M.lam 2).pow m).φ (σ.comp (algebraMap _ _))).nsq (secVal M.q _ s) (PtsOver.map i rfl _ y)) / 2 with hg`. Establish `hf (R : ℝ) (y) (hy : Inner (upTo M i σ y)) : |Real.log ((((M.lam R).pow m).φ _).nsq (secVal M.q _ s) (PtsOver.map i rfl _ y)) / 2| ≤ |g y| + (|Real.log a| + C₁) * Real.log (M.x.r σ (upTo M i σ y))`.

Establish `b₁` using `hlog σ R _ (upTo_eq M i σ y ▸ hy)`. Rewrite `b₁` using `[← upTo_eq]`. Establish `b₂` using `mul_le_mul_of_nonneg_left (hr1 (upTo M i σ y)) (abs_nonneg (Real.log a))`. Establish `b₃ : |Real.log ((((M.lam 2).pow m).φ _).nsq (secVal M.q _ s) (PtsOver.map i rfl _ y)) / 2| ≤ |g y| + |Real.log a|`. Simplify using `only [hg]`.

Generalize the expression as in `(((M.lam 2).pow m).φ _).nsq (secVal M.q _ s) (PtsOver.map i rfl _ y) = x`. Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[Real.log_mul ha.ne' hx, abs_le]`. Apply the tactic sequence `constructor <;> linarith [le_abs_self ((Real.log a + Real.log x) / 2), neg_abs_le ((Real.log a + Real.log x) / 2), le_abs_self (Real.log a), neg_abs_le (Real.log a)]`.

Use `abs_sub_abs_le_abs_sub (Real.log ((((M.lam R).pow m).φ _).nsq (secVal M.q _ s) (PtsOver.map i rfl _ y)) / 2) (Real.log ((((M.lam 2).pow m).φ _).nsq (secVal M.q _ s) (PtsOver.map i rfl _ y)) / 2)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hF (y) : 0 ≤ |g y| + (|Real.log a| + C₁) * Real.log (M.x.r σ (upTo M i σ y))` using `add_nonneg (abs_nonneg _) (mul_nonneg (add_nonneg (abs_nonneg _) hC₁) (zero_le_one.trans (hr1 _)))`. Establish `hnull (ρ : AlgChart (i ≫ M.q) (σ.comp (algebraMap _ _)) (e + 2) → _ → ℝ) : part ρ {y | Inner (upTo M i σ y)}ᶜ = 0`. Use `Eq.trans (congrArg _ (Set.ext fun y => (inner_up _ _ _ y).not)) ?_` and prove the remaining obligations.

Conclude with `MixDensNull.part_over_closed _ _ _ _ hZ _ hTc (not_not.2 hgen) _ ρ`. Use `GlobalTheory.T.densInt_tendsto_zero_of_dominated _ _ _ _ _ _ _ _ (fun y => |t| * C₂ * (|g y| + (|Real.log a| + C₁) * Real.log (M.x.r σ (upTo M i σ y)))) {y | Inner (upTo M i σ y)} (fun R => (GlobalTheory.T.second_chern_density_chart_formula _ _ _ _ _ _ _ _ _ e (((M.H R).pull M.b …` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop 2] with R hR ch y hy hin`. Rewrite using `[abs_mul, abs_mul t]`. Conclude with `(mul_le_mul (hf R y hin) (mul_le_mul_of_nonneg_left (hle R hR ch y hy hin) (abs_nonneg t)) (by positivity) (hF y)).trans_eq (by ring)`.

Use `(((tendsto_dens M i σ e ch hy hin).const_mul t).abs.const_mul (|g y| + (|Real.log a| + C₁) * Real.log (M.x.r σ (upTo M i σ y))))` as an intermediate fact. Rewrite `this` using `[mul_zero, abs_zero, mul_zero]`. Use `squeeze_zero_norm (fun R => ?_) this` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, abs_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hf R y hin) (abs_nonneg _)`.
-/
theorem tendsto_densInt (hL : AnalyticLogResolution) (hD : AnalyticSetDimension) {Y : Scheme.{0}} [IsIntegral Y] (i : Y ⟶ M.B)
    [IsClosedImmersion i] (hZ : IsArithVar (i ≫ M.q) (e + 2)) (hgen : (i ≫ M.b) (genericPoint Y) ∈ abLocus O.s.T.Z.t.G)
    (hzs : i (genericPoint Y) ∈ Out.nonzeroLocus s) (hcut : ∀ v : Y, (i ≫ M.b) v ∉ abLocus O.s.T.Z.t.G →
      CharZero (Y.residueField v) → Order.coheight v = 1 → i v ∈ Out.nonzeroLocus s) (t : ℝ) (σ : O.κ.c.F →+* ℂ) :
    Tendsto (fun R => densInt (fun ch y => t * dens M i σ e R ch y) fun y =>
      Real.log ((((M.lam R).pow m).φ _).nsq (secVal M.q _ s) (PtsOver.map i rfl _ y)) / 2) atTop (𝓝 0) := by
  have hproj : IsProjOver (genStr O.s.T.Z) := (GlobalTheory.ProjSpace.points_and_stability _ 0).2.2.1 _ _ _ _ O.s.T.Z.proj
  have : CompactSpace (CxPts (genStr O.s.T.Z) σ) := PtsOver.compactSpace hproj _
  have := CxPts.t2Space_cxPts_of_isProjOver σ hproj
  have := CxPts.secondCountableTopology_of_isProjOver (σ.comp (algebraMap _ _)) hZ.isProjOver
  have := (isNoetherian_of_isProjOver O.s.T.Z.proj).toIsLocallyNoetherian
  have hA := GlobalTheory.T.compact_projective_analytic _ _ _ σ _ (manifold O.s.T.Z σ) hproj
  obtain ⟨α, Λ, sg, t₀, C, hB, hn, hcont, hbd, hcurv⟩ := GlobalTheory.T.boundary_setting_curvature_bound D _ _ _ _ _ O.s M.x σ
  have hw := GlobalTheory.T.boundary_setting_restrict_subvariety D _ _ _ _ _ O.s σ _ α Λ sg t₀ hB Y _ (i ≫ M.b) (Category.assoc _ _ _) (e + 2)
  obtain ⟨q, Zs, T₀, h₁, h₂, hirr, hloc, hdom, hcomp⟩ :=
    GlobalTheory.T.exists_boundary_strata_subvariety D _ _ _ _ _ O.s M.x σ Y _ (i ≫ M.b) (Category.assoc _ _ _) (e + 2) hZ hgen
  have hop : IsOpen {y : CxPts (genStr O.s.T.Z) σ | Inner y} := isOpen_not_liesIn _
  have hmeas := GlobalTheory.T.boundary_integral_off_strata D _ _ _ _ _ O.s σ Y _ (i ≫ M.b) (Category.assoc _ _ _) (e + 2) hZ q Zs T₀ h₁ h₂ hloc
    (poincarePot α Λ sg t₀) (boundary sg) (hbd ▸ hop.isClosed_compl)
    (GlobalTheory.PoincSmooth.smoothOn_nhd_off_boundary _ _ _ _ α Λ sg t₀ hB.1 (fun i => ⟨(hB.2.2.1 i).1, (hB.2.2.1 i).2.1⟩)
      fun i => (hB.2.2.1 i).2.2.2) hw
  have hTc : IsClosed {v : Y | (i ≫ M.b) v ∉ abLocus O.s.T.Z.t.G} :=
    ((GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian _ O.s.T.Z.t.semi).preimage (i ≫ M.b).continuous).isClosed_compl
  have hSc : IsClosed {v : Y | i v ∉ Out.nonzeroLocus s} :=
    ((Out.nonzeroLocus s).isOpen.preimage i.continuous).isClosed_compl
  have hnb (a) : ¬ Zs a ⊆ boundary sg := fun h => by
    obtain ⟨y, hy, hy'⟩ := hdom a _ hTc (not_not.2 hgen)
    exact (hbd.le (h hy)) ((inner_up _ _ _ _).2 (not_not.1 hy'))
  have hu : Continuous (upTo M i σ) := continuous_up _ _ _
  have hr1 (y) : 1 ≤ Real.log (M.x.r σ y) :=
    (Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le (M.x.exp_le_r σ y))).2 (M.x.exp_le_r σ y)
  have i₁ : Integrable (fun y => Real.log (M.x.r σ (upTo M i σ y)))
      (part (D := e + 2) (potDens (poincarePot α Λ sg t₀) (boundary sg)ᶜ (upTo M i σ))) := by
    refine ⟨((((continuous_finsetProd _ fun j _ => (hcont j).comp hu).pow 2).measurable.log.const_sub _).log).aestronglyMeasurable,
      (lintegral_mono fun y => ?_).trans_lt ((hmeas _).trans_lt (ENNReal.sum_lt_top.2 fun a _ =>
        GlobalTheory.T.regular_integral_boundary_potential hL hD _ _ _ hA _ α Λ sg t₀ hB _ _ (hirr a).1 (hirr a).2.1 (hnb a)))⟩
    rw [Real.enorm_of_nonneg (zero_le_one.trans (hr1 _))]
    refine ENNReal.ofReal_le_ofReal ((log_r_le fun j => (M.x.nrm_div σ j).1 _).trans_eq ?_)
    simp only [← hn]
    rfl
  obtain ⟨L, sL, a, ha, hLp, hLs, hL1, hLn⟩ := GlobalTheory.T.exists_potential_section_bounded D O c M m s σ
  have hsL (y) : sL (upTo M i σ y) (upTo M i σ y) ≠ 0 ↔ i (y.1 (IsLocalRing.closedPoint ℂ)) ∈ Out.nonzeroLocus s := by
    refine Iff.trans ?_ (nsq_ne_zero_iff (((M.lam 2).pow m).φ _) s (PtsOver.map i rfl _ y))
    rw [← mul_ne_zero_iff_left ha.ne', ← hLn, ← upTo_eq, pow_ne_zero_iff two_ne_zero, normSec,
      mul_ne_zero_iff_right (Real.exp_ne_zero _), norm_ne_zero_iff]
  have hmf (R : ℝ) : Continuous fun y => (((M.lam R).pow m).φ (σ.comp (algebraMap _ _))).nsq (secVal M.q _ s)
      (PtsOver.map i rfl _ y) := ((HermLB.cInf _ _).continuous_nsq _).comp (PtsOver.continuous_map _ _ _)
  have i₂ : Integrable (fun y => Real.log (a * (((M.lam 2).pow m).φ _).nsq (secVal M.q _ s) (PtsOver.map i rfl _ y)) / 2)
      (part (D := e + 2) (potDens (poincarePot α Λ sg t₀) (boundary sg)ᶜ (upTo M i σ))) := by
    refine ⟨((continuous_const.mul (hmf 2)).measurable.log.div_const _).aestronglyMeasurable,
      (lintegral_mono fun y => ?_).trans_lt ((hmeas (absLogNorm L sL)).trans_lt (ENNReal.sum_lt_top.2 fun b _ =>
        GlobalTheory.T.log_norm_integrable_poincare hL hD _ _ _ hA _ α Λ sg t₀ hB _ _ (hirr b).1 (hirr b).2.1 (hnb b) L sL hLp hLs hL1 ?_ fun K hK => ?_))⟩
    · beta_reduce
      rw [← hLn, ← upTo_eq, Real.log_pow, absLogNorm]
      split_ifs
      · exact le_top
      · rw [Real.enorm_eq_ofReal_abs, Nat.cast_ofNat, mul_div_cancel_left₀ _ two_ne_zero]
        rfl
    · obtain ⟨y, hy, hy'⟩ := hdom b _ hSc (not_not.2 hzs)
      exact ⟨_, hy, (hsL y).2 (not_not.1 hy')⟩
    · by_contra hK'
      obtain ⟨v, hv, hv₁, hv₂, hv₃⟩ := hcomp b K (hbd ▸ hK) _ hSc fun y hy h => hK' ⟨_, hy, (hsL y).2 h⟩
      exact hv (hcut v hv₁ hv₂ hv₃)
  obtain ⟨C₁, hC₁, hlog⟩ := GlobalTheory.T.log_norm_section_difference_bound D O c M m s
  obtain ⟨C₂, hC₂, hle⟩ := exists_dens_le M i σ e hcurv
  have hS : (boundary sg)ᶜ = {y | Inner y} := by
    rw [hbd]
    exact compl_compl {y | Inner y}
  rw [hS] at hw i₁ i₂
  set g := fun y => Real.log (a * (((M.lam 2).pow m).φ (σ.comp (algebraMap _ _))).nsq (secVal M.q _ s)
    (PtsOver.map i rfl _ y)) / 2 with hg
  have hf (R : ℝ) (y) (hy : Inner (upTo M i σ y)) :
      |Real.log ((((M.lam R).pow m).φ _).nsq (secVal M.q _ s) (PtsOver.map i rfl _ y)) / 2| ≤
        |g y| + (|Real.log a| + C₁) * Real.log (M.x.r σ (upTo M i σ y)) := by
    have b₁ := hlog σ R _ (upTo_eq M i σ y ▸ hy)
    rw [← upTo_eq] at b₁
    have b₂ := mul_le_mul_of_nonneg_left (hr1 (upTo M i σ y)) (abs_nonneg (Real.log a))
    have b₃ : |Real.log ((((M.lam 2).pow m).φ _).nsq (secVal M.q _ s) (PtsOver.map i rfl _ y)) / 2| ≤ |g y| + |Real.log a| := by
      simp only [hg]
      generalize (((M.lam 2).pow m).φ _).nsq (secVal M.q _ s) (PtsOver.map i rfl _ y) = x
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · rw [Real.log_mul ha.ne' hx, abs_le]
        constructor <;> linarith [le_abs_self ((Real.log a + Real.log x) / 2), neg_abs_le ((Real.log a + Real.log x) / 2),
          le_abs_self (Real.log a), neg_abs_le (Real.log a)]
    have := abs_sub_abs_le_abs_sub (Real.log ((((M.lam R).pow m).φ _).nsq (secVal M.q _ s) (PtsOver.map i rfl _ y)) / 2)
      (Real.log ((((M.lam 2).pow m).φ _).nsq (secVal M.q _ s) (PtsOver.map i rfl _ y)) / 2)
    linarith
  have hF (y) : 0 ≤ |g y| + (|Real.log a| + C₁) * Real.log (M.x.r σ (upTo M i σ y)) :=
    add_nonneg (abs_nonneg _) (mul_nonneg (add_nonneg (abs_nonneg _) hC₁) (zero_le_one.trans (hr1 _)))
  have hnull (ρ : AlgChart (i ≫ M.q) (σ.comp (algebraMap _ _)) (e + 2) → _ → ℝ) : part ρ {y | Inner (upTo M i σ y)}ᶜ = 0 := by
    refine Eq.trans (congrArg _ (Set.ext fun y => (inner_up _ _ _ y).not)) ?_
    exact MixDensNull.part_over_closed _ _ _ _ hZ _ hTc (not_not.2 hgen) _ ρ
  refine GlobalTheory.T.densInt_tendsto_zero_of_dominated _ _ _ _ _ _ _ _ (fun y => |t| * C₂ * (|g y| + (|Real.log a| + C₁) * Real.log (M.x.r σ (upTo M i σ y))))
    {y | Inner (upTo M i σ y)} (fun R => (GlobalTheory.T.second_chern_density_chart_formula _ _ _ _ _ _ _ _ _ e (((M.H R).pull M.b rfl).pull i rfl _)
      (HermLB.cInf _ _)).1.mul continuous_const) (fun R => (hmf R).measurable.log.div_const _) hw
    ((i₂.abs.add (i₁.const_mul _)).const_mul _) (hop.preimage hu).measurableSet (fun R => ⟨hnull _, hnull _⟩)
    (fun y => mul_nonneg (mul_nonneg (abs_nonneg _) hC₂) (hF y)) ?_ fun ch y hy hin => ?_
  · filter_upwards [eventually_ge_atTop 2] with R hR ch y hy hin
    rw [abs_mul, abs_mul t]
    exact (mul_le_mul (hf R y hin) (mul_le_mul_of_nonneg_left (hle R hR ch y hy hin) (abs_nonneg t))
      (by positivity) (hF y)).trans_eq (by ring)
  · have := (((tendsto_dens M i σ e ch hy hin).const_mul t).abs.const_mul
      (|g y| + (|Real.log a| + C₁) * Real.log (M.x.r σ (upTo M i σ y))))
    rw [mul_zero, abs_zero, mul_zero] at this
    refine squeeze_zero_norm (fun R => ?_) this
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hf R y hin) (abs_nonneg _)

end Limit

open MvPolynomial Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTestDR in

/- English proof (translation)
Introduce `hX h2 _ _ D O _ _ _ _ _ _ c M I z e m s hG hC`. Take `⟨t, ht⟩` from `arch_eq h2.p4 (D.R.f * O.N) e`. Establish `hd : topologicalKrullDim (closure ({z} : Set M.B)) = (e + 3 : ℕ)` using `hG.1`. Unfold `DRBase.arch`. Break down `ht _ _ M.q _ M.ar _ M.F z hd with h | h` into its components or cases.

Conclude with `tendsto_const_nhds.congr fun R => (h _ ((M.H R).pull M.b rfl) (M.lam R) ((M.lam R).pow m) s hC.1).symm`. Establish `h'` using `fun R => h _ ((M.H R).pull M.b rfl) (M.lam R) ((M.lam R).pow m) s hC.1`. Establish `hc` using `(h' 0).1`. Use `M.ar.finite_emb` as an intermediate fact. Use `Fintype.ofFinite (𝓞 O.κ.c.F →+* ℂ)` as an intermediate fact.

Use `Tendsto.congr (fun R => ((h' R).2.trans (finsum_eq_sum_of_fintype _)).symm) ?_` and prove the remaining obligations. Use `(tendsto_finsetSum (a := fun _ => (0 : ℝ)) _ fun σ₀ _ => ?_).trans_eq (congrArg 𝓝 Finset.sum_const_zero)` and prove the remaining obligations. Take `⟨σ, rfl⟩` from `exists_comp_eq σ₀`. Use `tendsto_densInt hX.logres hX.andim (redι (clo z)) (M.ar.of_isClosedImmersion _ hc ((dim_clo z).trans hd)) ?_ ?_ (fun v => mem_nonzeroLocus_of_cuts hC) t σ` and prove the remaining obligations. Use `charZero_residueField hc` as an intermediate fact.

Establish `h₁` using `((redι (clo z)).residueFieldMap (genericPoint _)).hom.charZero`. Rewrite `h₁` using `[redι_clo]`. Rewrite using `[Scheme.Hom.comp_apply, redι_clo]`. Conclude with `not_not.1 (hG.2.2 h₁)`. Rewrite using `[redι_clo]`.

Conclude with `hC.1`.
-/
theorem arch_tendsto_zero : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegularAlteration → OnObj fun _ O _ _ _ _ => ∀ c (M : DRBase O c) (I : M.Emb) (z : M.B) (e m : ℕ) (s : (lbPow M.lamB m).Sec), I.Good z (e + 1) → I.Cuts s z e → Tendsto (fun R => M.arch R m s z e) atTop (𝓝 0) := by
  intro hX h2 _ _ D O _ _ _ _ _ _ c M I z e m s hG hC
  obtain ⟨t, ht⟩ := arch_eq h2.p4 (D.R.f * O.N) e
  have hd : topologicalKrullDim (closure ({z} : Set M.B)) = (e + 3 : ℕ) := hG.1
  unfold DRBase.arch
  rcases ht _ _ M.q _ M.ar _ M.F z hd with h | h
  · exact tendsto_const_nhds.congr fun R => (h _ ((M.H R).pull M.b rfl) (M.lam R) ((M.lam R).pow m) s hC.1).symm
  have h' := fun R => h _ ((M.H R).pull M.b rfl) (M.lam R) ((M.lam R).pow m) s hC.1
  have hc := (h' 0).1
  have := M.ar.finite_emb
  have := Fintype.ofFinite (𝓞 O.κ.c.F →+* ℂ)
  refine Tendsto.congr (fun R => ((h' R).2.trans (finsum_eq_sum_of_fintype _)).symm) ?_
  refine (tendsto_finsetSum (a := fun _ => (0 : ℝ)) _ fun σ₀ _ => ?_).trans_eq (congrArg 𝓝 Finset.sum_const_zero)
  obtain ⟨σ, rfl⟩ := exists_comp_eq σ₀
  refine tendsto_densInt hX.logres hX.andim (redι (clo z)) (M.ar.of_isClosedImmersion _ hc ((dim_clo z).trans hd)) ?_ ?_
    (fun v => mem_nonzeroLocus_of_cuts hC) t σ
  · have := charZero_residueField hc
    have h₁ := ((redι (clo z)).residueFieldMap (genericPoint _)).hom.charZero
    rw [redι_clo] at h₁
    rw [Scheme.Hom.comp_apply, redι_clo]
    exact not_not.1 (hG.2.2 h₁)
  · rw [redι_clo]
    exact hC.1

end GlobalTheory.ArchLim

end
