import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.CoefBd
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatLin
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.CuspZero
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.One
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.FockSt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

/- English proof (translation)
Establish `h0 : g 1 0 = g' 1 0` using `congrFun hr 0`. Establish `h1 : g 1 1 = g' 1 1` using `congrFun hr 1`. Establish `hi : ∀ i j, (g⁻¹) i j = (!![g 1 1, -g 0 1; -g 1 0, g 0 0] : Matrix (Fin 2) (Fin 2) (A F)) i j` using `fun i j => congrFun (congrFun (specialLinear_inv_val g) i) j`. Establish `hn : g' * g⁻¹ = nU ((g' * g⁻¹) 0 1)`. Establish `d` using `specialLinear_det_entries g`.

Establish `d'` using `specialLinear_det_entries g'`. Apply `specialLinear_ext_entries` to reduce the goal to its premises. Rewrite using `[specialLinear_mul_entry, hi, hi]`. Simplify using `only [nU, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]`. Simplify using the standard rewrite rules.

Rewrite using `[h0, h1]`. Take the linear combination `d'`. Simplify using `[nU]`. Rewrite using `[specialLinear_mul_entry, hi, hi]`. Simplify using `[nU]`.

Rewrite using `[h0, h1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[specialLinear_mul_entry, hi, hi]`. Simplify using `[nU]`. Rewrite using `[← h0, ← h1]`.

Take the linear combination `d`. Conclude with `⟨_, by rw [← hn, inv_mul_cancel_right]⟩`.
-/
private theorem eq_nU_mul {F : Type} [Field F] [NumberField F] {g g' : G1 F} (hr : row g = row g') :
    ∃ b, g' = nU b * g := by
  have h0 : g 1 0 = g' 1 0 := congrFun hr 0
  have h1 : g 1 1 = g' 1 1 := congrFun hr 1
  have hi : ∀ i j, (g⁻¹) i j = (!![g 1 1, -g 0 1; -g 1 0, g 0 0] : Matrix (Fin 2) (Fin 2) (A F)) i j :=
    fun i j => congrFun (congrFun (specialLinear_inv_val g) i) j
  have hn : g' * g⁻¹ = nU ((g' * g⁻¹) 0 1) := by
    have d := specialLinear_det_entries g
    have d' := specialLinear_det_entries g'
    apply specialLinear_ext_entries
    · rw [specialLinear_mul_entry, hi, hi]
      simp only [nU, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      simp
      rw [h0, h1]
      linear_combination d'
    · simp [nU]
    · rw [specialLinear_mul_entry, hi, hi]
      simp [nU]
      rw [h0, h1]
      ring
    · rw [specialLinear_mul_entry, hi, hi]
      simp [nU]
      rw [← h0, ← h1]
      linear_combination d
  exact ⟨_, by rw [← hn, inv_mul_cancel_right]⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D W M π f hf φ hφ`. Use `⟨?_, fun g g' hr => ?_⟩` and prove the remaining obligations. Establish `hL : ∀ g, w1 W f.1 φ 1 g = Wf f.1 (gl g) * hat (W.Om g φ).1 ![0, 1, 1, 0]`. Introduce `g`. Establish `h1 : nu F (1 : GL (Fin 2) (A E)) = 1` using `by simp [nu]`.

Simplify using `[w1, h1]`. Simplify using `only [hL]`. Take `⟨hLf, -⟩` from `UpperTheory.ConvolutionTheory.R2.Pp.cuspZero F π f hf`. Take `⟨hWc, -⟩` from `UpperTheory.ConvolutionTheory.R2.Pp.wfBasic F f.1 hLf`. Establish `hKc : IsCompact (KK F)` using `(_root_.UpperTheory.ConvolutionTheory.R2.M.kkCpt F).2`.

Take `⟨U, -, hfd, hmem⟩` from `(fockSt F E D W).om φ hφ (KK F) hKc (fun k hk => hk.1)`. Take `⟨n, b, c, B, -, hc, hk⟩` from `coefBd F E D W φ (KK F) U hKc hfd hmem`. Take `⟨H, hH⟩` from `hatLin F`. Establish `hS` using `hatSt F E D W`. Establish `e : ∀ p ∈ (Set.univ ×ˢ KK F : Set (IdeleGroup F × G1 F)), hat (W.Om (mD p.1 * p.2) φ).1 ![0, 1, 1, 0] = ((W.η.1 p.1 : ℂˣ) : ℂ) * ((ab p.1 : ℝ) : ℂ) * ∑ i, c i p.2 * (H (b i)).1 ![0, ((p.1⁻¹ : (A F)ˣ) : A F), (p.1 : A F), 0]`.

Introduce and unpack `⟨a, k⟩ ⟨-, hk'⟩`. Establish `hv : (![(a : A F) * (![0, 1, 1, 0] : V4 F) 0, ((a⁻¹ : (A F)ˣ) : A F) * (![0, 1, 1, 0] : V4 F) 1, (a : A F) * (![0, 1, 1, 0] : V4 F) 2, (a : A F) * (![0, 1, 1, 0] : V4 F) 3] : V4 F) = ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0]`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp`. Simplify using `only []`.

Rewrite using `[map_mul, Module.End.mul_apply, hS.m, hv, (hk k hk').2, ← hH, map_sum]`. Simplify using `[Finset.sum_apply]`. Establish `hcont1 : Continuous fun p : IdeleGroup F × G1 F => Wf f.1 (gl (mD p.1 * p.2))` using `hWc.comp (continuous_gl.comp ((continuous_mD.comp continuous_fst).mul continuous_snd))`. Use `hcont1.continuousOn.mul (ContinuousOn.congr ?_ e)` and prove the remaining obligations. Use `ContinuousOn.mul (Continuous.continuousOn ?_) (continuousOn_finset_sum _ fun i _ => ?_)` and prove the remaining obligations.

Use `Continuous.mul ?_ ?_` and prove the remaining obligations. Conclude with `Units.continuous_val.comp (W.η.2.1.comp continuous_fst)`. Conclude with `Complex.continuous_ofReal.comp (continuous_ab.comp continuous_fst)`. Use `ContinuousOn.mul ((hc i).comp continuousOn_snd fun p hp => hp.2) (Continuous.continuousOn ?_)` and prove the remaining obligations. Use `(continuous_of_mem_schwartzBruhatPi (H (b i)).2).comp (continuous_pi fun j => ?_)` and prove the remaining obligations.

Use `fin_cases j`. Conclude with `continuous_const`. Conclude with `Units.continuous_coe_inv.comp continuous_fst`. Conclude with `Units.continuous_val.comp continuous_fst`. Conclude with `continuous_const`.

Take `⟨b, rfl⟩` from `eq_nU_mul hr`. Conclude with `((conv F E D W M π f hf φ hφ 1).2.2.2.1 b g).symm`.
-/
theorem UpperTheory.ConvolutionTheory.R2.G.contW :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ,
    ContinuousOn (fun p : IdeleGroup F × G1 F => w1 W f.1 φ 1 (mD p.1 * p.2)) (Set.univ ×ˢ KK F) ∧
    ∀ g g', row g = row g' → w1 W f.1 φ 1 g = w1 W f.1 φ 1 g' := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ
  refine ⟨?_, fun g g' hr => ?_⟩
  · have hL : ∀ g, w1 W f.1 φ 1 g = Wf f.1 (gl g) * hat (W.Om g φ).1 ![0, 1, 1, 0] := by
      intro g
      have h1 : nu F (1 : GL (Fin 2) (A E)) = 1 := by simp [nu]
      simp [w1, h1]
    simp only [hL]
    obtain ⟨hLf, -⟩ := UpperTheory.ConvolutionTheory.R2.Pp.cuspZero F π f hf
    obtain ⟨hWc, -⟩ := UpperTheory.ConvolutionTheory.R2.Pp.wfBasic F f.1 hLf
    have hKc : IsCompact (KK F) := (_root_.UpperTheory.ConvolutionTheory.R2.M.kkCpt F).2
    obtain ⟨U, -, hfd, hmem⟩ := (fockSt F E D W).om φ hφ (KK F) hKc (fun k hk => hk.1)
    obtain ⟨n, b, c, B, -, hc, hk⟩ := coefBd F E D W φ (KK F) U hKc hfd hmem
    obtain ⟨H, hH⟩ := hatLin F
    have hS := hatSt F E D W
    have e : ∀ p ∈ (Set.univ ×ˢ KK F : Set (IdeleGroup F × G1 F)),
        hat (W.Om (mD p.1 * p.2) φ).1 ![0, 1, 1, 0] = ((W.η.1 p.1 : ℂˣ) : ℂ) * ((ab p.1 : ℝ) : ℂ) *
          ∑ i, c i p.2 * (H (b i)).1 ![0, ((p.1⁻¹ : (A F)ˣ) : A F), (p.1 : A F), 0] := by
      rintro ⟨a, k⟩ ⟨-, hk'⟩
      have hv : (![(a : A F) * (![0, 1, 1, 0] : V4 F) 0, ((a⁻¹ : (A F)ˣ) : A F) * (![0, 1, 1, 0] : V4 F) 1,
          (a : A F) * (![0, 1, 1, 0] : V4 F) 2, (a : A F) * (![0, 1, 1, 0] : V4 F) 3] : V4 F) =
          ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0] := by
        funext i
        fin_cases i <;> simp
      simp only []
      rw [map_mul, Module.End.mul_apply, hS.m, hv, (hk k hk').2, ← hH, map_sum]
      simp [Finset.sum_apply]
    have hcont1 : Continuous fun p : IdeleGroup F × G1 F => Wf f.1 (gl (mD p.1 * p.2)) :=
      hWc.comp (continuous_gl.comp ((continuous_mD.comp continuous_fst).mul continuous_snd))
    refine hcont1.continuousOn.mul (ContinuousOn.congr ?_ e)
    refine ContinuousOn.mul (Continuous.continuousOn ?_) (continuousOn_finset_sum _ fun i _ => ?_)
    · refine Continuous.mul ?_ ?_
      · exact Units.continuous_val.comp (W.η.2.1.comp continuous_fst)
      · exact Complex.continuous_ofReal.comp (continuous_ab.comp continuous_fst)
    · refine ContinuousOn.mul ((hc i).comp continuousOn_snd fun p hp => hp.2) (Continuous.continuousOn ?_)
      refine (continuous_of_mem_schwartzBruhatPi (H (b i)).2).comp (continuous_pi fun j => ?_)
      fin_cases j
      · exact continuous_const
      · exact Units.continuous_coe_inv.comp continuous_fst
      · exact Units.continuous_val.comp continuous_fst
      · exact continuous_const
  · obtain ⟨b, rfl⟩ := eq_nU_mul hr
    exact ((conv F E D W M π f hf φ hφ 1).2.2.2.1 b g).symm
