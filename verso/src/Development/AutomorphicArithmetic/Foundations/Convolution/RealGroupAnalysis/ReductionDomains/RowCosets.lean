import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private def upS {F : Type} [Field F] (ξ : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, ξ; 0, 1], by simp [Matrix.det_fin_two]⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem upS_val {F : Type} [Field F] (ξ : F) : (upS ξ).1 = !![1, ξ; 0, 1] := rfl

/- English proof (translation)
The claim follows from `M.ratS_up ξ`.
-/
private theorem ratS_upS {F : Type} [Field F] [NumberField F] (ξ : F) : ratS F (upS ξ) = nU (rt ξ) :=
  M.ratS_up ξ

/- English proof (translation)
Establish `hd` using `g.det_coe`. Rewrite `hd` using `[Matrix.det_fin_two, h0, h1]`. Establish `hd' : g.1 0 0 = 1` using `by simpa using hd`. Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `g.1 = (upS (g.1 0 1)).1`.

Rewrite using `[upS_val]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [h0, h1, hd']`.
-/
private theorem specialLinear_upper_unipotent {F : Type} [Field F] (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (h0 : g.1 1 0 = 0) (h1 : g.1 1 1 = 1) : g = upS (g.1 0 1) := by
  have hd := g.det_coe
  rw [Matrix.det_fin_two, h0, h1] at hd
  have hd' : g.1 0 0 = 1 := by simpa using hd
  refine Subtype.ext ?_
  change g.1 = (upS (g.1 0 1)).1
  rw [upS_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1, hd']

/- English proof (translation)
Introduce `a b h`. Establish `hinj : Function.Injective (algebraMap F (A F))` using `AdeleRing.algebraMap_injective (𝓞 F) F`. Use `Subtype.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Apply `hinj` to reduce the goal to its premises.

Establish `h2` using `congrArg (fun g : G1 F => g.1 i j) h`. Simplify `h2` using `[M.val_ratS]`.
-/
private theorem ratS_inj {F : Type} [Field F] [NumberField F] :
    Function.Injective (ratS F) := by
  intro a b h
  have hinj : Function.Injective (algebraMap F (A F)) := AdeleRing.algebraMap_injective (𝓞 F) F
  refine Subtype.ext ?_
  ext i j
  apply hinj
  have h2 := congrArg (fun g : G1 F => g.1 i j) h
  simpa [M.val_ratS] using h2

/- English proof (translation)
Use extensionality with `j`. Express the relevant statement in the definitionally equal form `((upS ξ).1 * g.1) 1 j = _`. Rewrite using `[upS_val]`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two]`.
-/
private theorem row_up {F : Type} [Field F] (ξ : F) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    (upS ξ * g).1 1 = g.1 1 := by
  ext j
  change ((upS ξ).1 * g.1) 1 j = _
  rw [upS_val]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Introduce `F _ _`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hex : ∀ r : {r : Fin 2 → F // r ≠ 0}, ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, g.1 1 = r.1`. Introduce and unpack `⟨r, hr⟩`. Distinguish the cases in `hc : r 0 = 0`.

Apply the tactic sequence `have hd : r 1 ≠ 0 := fun hd => hr (by ext i; fin_cases i <;> simp [hc, hd])`. Use `⟨⟨!![(r 1)⁻¹, 0; r 0, r 1], by simp [Matrix.det_fin_two, hd]⟩, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext i; fin_cases i <;> simp`. Use `⟨⟨!![0, -(r 0)⁻¹; r 0, r 1], by simp [Matrix.det_fin_two, hc]⟩, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext i; fin_cases i <;> simp`.

Use `choose σ hσ using hex`. Conclude with `⟨σ, hσ⟩`. Introduce and unpack `σ hσ ⟨_, γ0, rfl⟩`. Establish `hr : γ0.1 1 ≠ 0`. Introduce `h`.

Establish `hd` using `γ0.det_coe`. Rewrite `hd` using `[Matrix.det_fin_two]`. Establish `h0 : γ0.1 1 0 = 0` using `congrFun h 0`. Establish `h1 : γ0.1 1 1 = 0` using `congrFun h 1`. Simplify using `[h0, h1] at hd`.

Take `⟨r, hrdef⟩ : ∃ r : {r : Fin 2 → F // r ≠ 0}, r = ⟨γ0.1 1, hr⟩` from `⟨_, rfl⟩`. Establish `hs : (σ r).1 1 = γ0.1 1` using `by rw [hσ r, hrdef]`. Establish `hs0 : (σ r).1 1 0 = γ0.1 1 0` using `congrFun hs 0`. Establish `hs1 : (σ r).1 1 1 = γ0.1 1 1` using `congrFun hs 1`. Establish `hdet : (σ r).1 0 0 * (σ r).1 1 1 - (σ r).1 0 1 * (σ r).1 1 0 = 1`.

Establish `hd` using `(σ r).det_coe`. Rewrite `hd` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Establish `e0 : (γ0 * (σ r)⁻¹).1 1 0 = 0`. Simplify using `only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]`. Simplify using `[hs0, hs1]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e1 : (γ0 * (σ r)⁻¹).1 1 1 = 1`. Simplify using `only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]`. Simplify using the standard rewrite rules. Take the linear combination `hdet - (σ r).1 0 0 * hs1 + (σ r).1 0 1 * hs0`.

Take `⟨ξ, hξ⟩ : ∃ ξ : F, γ0 * (σ r)⁻¹ = upS ξ` from `⟨_, specialLinear_upper_unipotent _ e0 e1⟩`. Establish `hγ : γ0 = upS ξ * σ r`. Rewrite using `[← hξ, inv_mul_cancel_right]`. Use `⟨(r, ξ), ?_, ?_⟩` and prove the remaining obligations. Use `show ratS F γ0 = nU (rt ξ) * ratS F (σ r) conv_lhs => rw [hγ]`.

Rewrite using `[map_mul, ratS_upS]`. Introduce and unpack `⟨r', ξ'⟩ heq`. Establish `heq' : ratS F γ0 = nU (rt ξ') * ratS F (σ r')` using `heq`. Rewrite `heq'` using `[← ratS_upS, ← map_mul]`. Establish `hγ'` using `ratS_inj heq'`.

Establish `hrr : r' = r`. Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[← hσ r', ← row_up ξ' (σ r'), ← hγ', hrdef]`. Substitute `hrr` using the available equality. Establish `hU : upS ξ = upS ξ'` using `mul_right_cancel (hγ.symm.trans hγ')`.

Establish `hξξ : ξ = ξ'`. Establish `h2` using `congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => g.1 0 1) hU`. Simplify `h2` using `[upS_val]`. Rewrite using `[hξξ]`.
-/
theorem UpperTheory.ConvolutionTheory.R2.M.rowCosets :
    ∀ (F : Type) [Field F] [NumberField F], (∃ σ, M.RowSec (F := F) σ) ∧ ∀ σ, M.RowSec (F := F) σ → ∀ γ : Gam F, ∃! p : {r : Fin 2 → F // r ≠ 0} × F, (γ : G1 F) = nU (rt p.2) * ratS F (σ p.1) := by
  intro F _ _
  refine ⟨?_, ?_⟩
  · have hex : ∀ r : {r : Fin 2 → F // r ≠ 0}, ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, g.1 1 = r.1 := by
      rintro ⟨r, hr⟩
      by_cases hc : r 0 = 0
      · have hd : r 1 ≠ 0 := fun hd => hr (by ext i; fin_cases i <;> simp [hc, hd])
        refine ⟨⟨!![(r 1)⁻¹, 0; r 0, r 1], by simp [Matrix.det_fin_two, hd]⟩, ?_⟩
        ext i; fin_cases i <;> simp
      · refine ⟨⟨!![0, -(r 0)⁻¹; r 0, r 1], by simp [Matrix.det_fin_two, hc]⟩, ?_⟩
        ext i; fin_cases i <;> simp
    choose σ hσ using hex
    exact ⟨σ, hσ⟩
  · rintro σ hσ ⟨_, γ0, rfl⟩
    have hr : γ0.1 1 ≠ 0 := by
      intro h
      have hd := γ0.det_coe
      rw [Matrix.det_fin_two] at hd
      have h0 : γ0.1 1 0 = 0 := congrFun h 0
      have h1 : γ0.1 1 1 = 0 := congrFun h 1
      simp [h0, h1] at hd
    obtain ⟨r, hrdef⟩ : ∃ r : {r : Fin 2 → F // r ≠ 0}, r = ⟨γ0.1 1, hr⟩ := ⟨_, rfl⟩
    have hs : (σ r).1 1 = γ0.1 1 := by rw [hσ r, hrdef]
    have hs0 : (σ r).1 1 0 = γ0.1 1 0 := congrFun hs 0
    have hs1 : (σ r).1 1 1 = γ0.1 1 1 := congrFun hs 1
    have hdet : (σ r).1 0 0 * (σ r).1 1 1 - (σ r).1 0 1 * (σ r).1 1 0 = 1 := by
      have hd := (σ r).det_coe
      rwa [Matrix.det_fin_two] at hd
    have e0 : (γ0 * (σ r)⁻¹).1 1 0 = 0 := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      simp [hs0, hs1]
      ring
    have e1 : (γ0 * (σ r)⁻¹).1 1 1 = 1 := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      simp
      linear_combination hdet - (σ r).1 0 0 * hs1 + (σ r).1 0 1 * hs0
    obtain ⟨ξ, hξ⟩ : ∃ ξ : F, γ0 * (σ r)⁻¹ = upS ξ := ⟨_, specialLinear_upper_unipotent _ e0 e1⟩
    have hγ : γ0 = upS ξ * σ r := by
      rw [← hξ, inv_mul_cancel_right]
    refine ⟨(r, ξ), ?_, ?_⟩
    · show ratS F γ0 = nU (rt ξ) * ratS F (σ r)
      conv_lhs => rw [hγ]
      rw [map_mul, ratS_upS]
    · rintro ⟨r', ξ'⟩ heq
      have heq' : ratS F γ0 = nU (rt ξ') * ratS F (σ r') := heq
      rw [← ratS_upS, ← map_mul] at heq'
      have hγ' := ratS_inj heq'
      have hrr : r' = r := by
        refine Subtype.ext ?_
        rw [← hσ r', ← row_up ξ' (σ r'), ← hγ', hrdef]
      subst hrr
      have hU : upS ξ = upS ξ' := mul_right_cancel (hγ.symm.trans hγ')
      have hξξ : ξ = ξ' := by
        have h2 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => g.1 0 1) hU
        simpa [upS_val] using h2
      rw [hξξ]
