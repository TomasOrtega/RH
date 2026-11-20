import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDblOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanSchwartzTraceFourierBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesSchwartzReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianTemperateGrowth

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixXChar GlobalTheory.DblEval
open GlobalTheory.Doubling (absE)

open scoped Classical
attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

noncomputable section

namespace GlobalTheory.DiagHeisFourier

open GlobalTheory.ArchFourier

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
Simplify using `only [GlobalTheory.ArchSch.ech, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ech_add' (s t : ℝ) : GlobalTheory.ArchSch.ech (s + t) = GlobalTheory.ArchSch.ech s * GlobalTheory.ArchSch.ech t := by
  simp only [GlobalTheory.ArchSch.ech, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/- English proof (translation)
Simplify using `[GlobalTheory.ArchSch.ech]`.
-/
theorem ech_zero' : GlobalTheory.ArchSch.ech 0 = 1 := by
  simp [GlobalTheory.ArchSch.ech]

def hop (a b : κ ⊕ κ → mixedEmbedding.mixedSpace F) (g : (κ ⊕ κ → mixedEmbedding.mixedSpace F) → ℂ) :
    (κ ⊕ κ → mixedEmbedding.mixedSpace F) → ℂ :=
  fun u => GlobalTheory.ArchSch.ech (traceDot F (κ ⊕ κ) u b + traceDot F (κ ⊕ κ) a b / 2) * g (u + a)

/- English proof (translation)
Use function extensionality and compare the values at `ξ`. Rewrite using `[hei, hop, hei, hg]`. Use `set B := traceDot F (κ ⊕ κ)`. Establish `key : ∀ x, hop a b f x * Complex.exp (-(2 * Real.pi * Complex.I) * ((B x ξ : ℝ) : ℂ)) = GlobalTheory.ArchSch.ech (-(B a b) / 2 - B a ξ) * (f (x + a) * Complex.exp (-(2 * Real.pi * Complex.I) * ((B (x + a) (ξ + b) : ℝ) : ℂ)))`. Introduce `x`.

Establish `e1 : GlobalTheory.ArchSch.ech (B x b + B a b / 2) * GlobalTheory.ArchSch.ech (B x ξ) = GlobalTheory.ArchSch.ech (-(B a b) / 2 - B a ξ) * GlobalTheory.ArchSch.ech (B (x + a) (ξ + b))`. Rewrite using `[← ech_add', ← ech_add']`. Use `congr 1`. Simplify using `only [map_add, LinearMap.add_apply]`. Expand and normalize the polynomial expressions, which then agree.

Express the relevant statement in the definitionally equal form `GlobalTheory.ArchSch.ech (B x b + B a b / 2) * f (x + a) * GlobalTheory.ArchSch.ech (B x ξ) = GlobalTheory.ArchSch.ech (-(B a b) / 2 - B a ξ) * (f (x + a) * GlobalTheory.ArchSch.ech (B (x + a) (ξ + b)))`. Take the linear combination `(f (x + a)) * e1`. Rewrite using `[integral_congr_ae (Filter.Eventually.of_forall key)]`. Rewrite using `[integral_const_mul]`. Rewrite using `[integral_add_right_eq_self (fun y => f y * Complex.exp (-(2 * Real.pi * Complex.I) * ((B y (ξ + b) : ℝ) : ℂ))) a]`.

Use `congr 1`. Use `congr 1`. Simplify using `only [map_neg, LinearMap.neg_apply]`. Rewrite using `[traceDot_comm ξ a, traceDot_comm b a]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fourier_hop (μ : Measure (κ ⊕ κ → mixedEmbedding.mixedSpace F)) [μ.IsAddHaarMeasure]
    (ei : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ → SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ)
    (hei : ∀ f y, ei f y = ∫ x, f x * Complex.exp (-(2 * Real.pi * Complex.I) *
      ((traceDot F (κ ⊕ κ) x y : ℝ) : ℂ)) ∂μ)
    (a b : κ ⊕ κ → mixedEmbedding.mixedSpace F) (f g : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ)
    (hg : ⇑g = hop a b f) : ⇑(ei g) = hop b (-a) (ei f) := by
  funext ξ
  rw [hei, hop, hei, hg]
  set B := traceDot F (κ ⊕ κ)
  have key : ∀ x, hop a b f x * Complex.exp (-(2 * Real.pi * Complex.I) * ((B x ξ : ℝ) : ℂ)) =
      GlobalTheory.ArchSch.ech (-(B a b) / 2 - B a ξ) *
        (f (x + a) * Complex.exp (-(2 * Real.pi * Complex.I) * ((B (x + a) (ξ + b) : ℝ) : ℂ))) := by
    intro x
    have e1 : GlobalTheory.ArchSch.ech (B x b + B a b / 2) * GlobalTheory.ArchSch.ech (B x ξ) =
        GlobalTheory.ArchSch.ech (-(B a b) / 2 - B a ξ) * GlobalTheory.ArchSch.ech (B (x + a) (ξ + b)) := by
      rw [← ech_add', ← ech_add']
      congr 1
      simp only [map_add, LinearMap.add_apply]
      ring
    change GlobalTheory.ArchSch.ech (B x b + B a b / 2) * f (x + a) * GlobalTheory.ArchSch.ech (B x ξ) =
      GlobalTheory.ArchSch.ech (-(B a b) / 2 - B a ξ) * (f (x + a) * GlobalTheory.ArchSch.ech (B (x + a) (ξ + b)))
    linear_combination (f (x + a)) * e1
  rw [integral_congr_ae (Filter.Eventually.of_forall key)]
  rw [integral_const_mul]
  rw [integral_add_right_eq_self (fun y => f y * Complex.exp (-(2 * Real.pi * Complex.I) * ((B y (ξ + b) : ℝ) : ℂ))) a]
  congr 1
  congr 1
  simp only [map_neg, LinearMap.neg_apply]
  rw [traceDot_comm ξ a, traceDot_comm b a]
  ring

def P2 (a : κ ⊕ κ → mixedEmbedding.mixedSpace F) : κ ⊕ κ → mixedEmbedding.mixedSpace F :=
  Sum.elim 0 (fun j => a (Sum.inr j))

def q (u v : κ ⊕ κ → mixedEmbedding.mixedSpace F) : ℝ :=
  traceDot F κ (fun j => u (Sum.inr j)) (fun j => v (Sum.inr j))

/- English proof (translation)
Simplify using `[traceDot_apply, q, P2, dotProduct, Fintype.sum_sum_type]`.
-/
theorem trace_dot_pairing_eq_quadratic (u a : κ ⊕ κ → mixedEmbedding.mixedSpace F) : traceDot F (κ ⊕ κ) u (P2 a) = q u a := by
  simp [traceDot_apply, q, P2, dotProduct, Fintype.sum_sum_type]

/- English proof (translation)
Simplify using `only [q]`. Rewrite using `[show (fun j => (u + v) (Sum.inr j)) = (fun j => u (Sum.inr j)) + (fun j => v (Sum.inr j)) from rfl, map_add, LinearMap.add_apply]`.
-/
theorem q_add_left (u v w : κ ⊕ κ → mixedEmbedding.mixedSpace F) : q (u + v) w = q u w + q v w := by
  simp only [q]
  rw [show (fun j => (u + v) (Sum.inr j)) = (fun j => u (Sum.inr j)) + (fun j => v (Sum.inr j)) from rfl, map_add,
    LinearMap.add_apply]

/- English proof (translation)
The claim follows from `traceDot_comm _ _`.
-/
theorem q_comm (u v : κ ⊕ κ → mixedEmbedding.mixedSpace F) : q u v = q v u := traceDot_comm _ _

/- English proof (translation)
Rewrite using `[q_comm, q_add_left, q_comm v, q_comm w]`.
-/
theorem q_add_right (u v w : κ ⊕ κ → mixedEmbedding.mixedSpace F) : q u (v + w) = q u v + q u w := by
  rw [q_comm, q_add_left, q_comm v, q_comm w]

def qB (c : ℝ) : LinearMap.BilinForm ℝ (κ ⊕ κ → mixedEmbedding.mixedSpace F) :=
  c • (traceDot F κ).compl₁₂ (LinearMap.funLeft ℝ (mixedEmbedding.mixedSpace F) Sum.inr)
    (LinearMap.funLeft ℝ (mixedEmbedding.mixedSpace F) Sum.inr)

/- English proof (translation)
Establish `h` using `GlobalTheory.QuadPhase.hasTemperateGrowth_quadPhase (qB (F := F) (κ := κ) c) 0 0`. Use `h using 2 with u` and compare the differences between its conclusion and the goal. Apply the tactic sequence `simp [qB, q] <;> rfl`.
-/
theorem hasTemperateGrowth_chirp (c : ℝ) :
    Function.HasTemperateGrowth (fun u : κ ⊕ κ → mixedEmbedding.mixedSpace F => GlobalTheory.ArchSch.ech (c * q u u)) := by
  have h := GlobalTheory.QuadPhase.hasTemperateGrowth_quadPhase (qB (F := F) (κ := κ) c) 0 0
  convert h using 2 with u
  simp [qB, q] <;> rfl

def chirp (c : ℝ) : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ]
    SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun u : κ ⊕ κ → mixedEmbedding.mixedSpace F => GlobalTheory.ArchSch.ech (c * q u u))

/- English proof (translation)
Rewrite using `[chirp, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_chirp c), smul_eq_mul]`.
-/
theorem chirp_apply (c : ℝ) (f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ) (u) :
    chirp c f u = GlobalTheory.ArchSch.ech (c * q u u) * f u := by
  rw [chirp, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_chirp c), smul_eq_mul]

/- English proof (translation)
Introduce `g`. Use `⟨chirp (-c) g, ?_⟩` and prove the remaining obligations. Use extensionality with `u`. Rewrite using `[chirp_apply, chirp_apply, ← mul_assoc, ← ech_add']`. Simplify using `[ech_zero']`.
-/
theorem chirp_surjective (c : ℝ) : Function.Surjective (chirp (F := F) (κ := κ) c) := by
  intro g
  refine ⟨chirp (-c) g, ?_⟩
  ext u
  rw [chirp_apply, chirp_apply, ← mul_assoc, ← ech_add']
  simp [ech_zero']

/- English proof (translation)
Use function extensionality and compare the values at `u`. Rewrite using `[chirp_apply, hg, hop, hop, chirp_apply]`. Use `set B := traceDot F (κ ⊕ κ)`. Establish `e1 : GlobalTheory.ArchSch.ech (1 / 2 * q u u) * GlobalTheory.ArchSch.ech (B u b + B a b / 2) = GlobalTheory.ArchSch.ech (B u (b - P2 a) + B a (b - P2 a) / 2) * GlobalTheory.ArchSch.ech (1 / 2 * q (u + a) (u + a))`. Rewrite using `[← ech_add', ← ech_add']`.

Use `congr 1`. Simplify using `only [map_sub, B, trace_dot_pairing_eq_quadratic, q_add_left, q_add_right]`. Rewrite using `[q_comm a u]`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(f (u + a)) * e1`.
-/
theorem chirp_hop (a b : κ ⊕ κ → mixedEmbedding.mixedSpace F) (f g : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ)
    (hg : ⇑g = hop a b f) : ⇑(chirp (1 / 2) g) = hop a (b - P2 a) (chirp (1 / 2) f) := by
  funext u
  rw [chirp_apply, hg, hop, hop, chirp_apply]
  set B := traceDot F (κ ⊕ κ)
  have e1 : GlobalTheory.ArchSch.ech (1 / 2 * q u u) * GlobalTheory.ArchSch.ech (B u b + B a b / 2) =
      GlobalTheory.ArchSch.ech (B u (b - P2 a) + B a (b - P2 a) / 2) * GlobalTheory.ArchSch.ech (1 / 2 * q (u + a) (u + a)) := by
    rw [← ech_add', ← ech_add']
    congr 1
    simp only [map_sub, B, trace_dot_pairing_eq_quadratic, q_add_left, q_add_right]
    rw [q_comm a u]
    ring
  linear_combination (f (u + a)) * e1

def shearL : (κ ⊕ κ → mixedEmbedding.mixedSpace F) ≃ₗ[ℝ] (κ ⊕ κ → mixedEmbedding.mixedSpace F) where
  toFun u := Sum.elim (fun j => u (Sum.inl j) - u (Sum.inr j)) (fun j => u (Sum.inr j))
  invFun u := Sum.elim (fun j => u (Sum.inl j) + u (Sum.inr j)) (fun j => u (Sum.inr j))
  map_add' u v := by funext i; cases i <;> simp <;> abel
  map_smul' c u := by funext i; cases i <;> simp [smul_sub]
  left_inv u := by funext i; cases i <;> simp
  right_inv u := by funext i; cases i <;> simp

def shear : (κ ⊕ κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ ⊕ κ → mixedEmbedding.mixedSpace F) :=
  (shearL (F := F) (κ := κ)).toContinuousLinearEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem shear_apply (u : κ ⊕ κ → mixedEmbedding.mixedSpace F) :
    shear u = Sum.elim (fun j => u (Sum.inl j) - u (Sum.inr j)) (fun j => u (Sum.inr j)) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem shear_symm_apply (u : κ ⊕ κ → mixedEmbedding.mixedSpace F) :
    shear.symm u = Sum.elim (fun j => u (Sum.inl j) + u (Sum.inr j)) (fun j => u (Sum.inr j)) := rfl

def shearT (b : κ ⊕ κ → mixedEmbedding.mixedSpace F) : κ ⊕ κ → mixedEmbedding.mixedSpace F :=
  Sum.elim (fun j => b (Sum.inl j)) (fun j => b (Sum.inr j) - b (Sum.inl j))

/- English proof (translation)
Rewrite using `[traceDot_apply, traceDot_apply]`. Use `congr 1`. Simplify using `only [dotProduct, Fintype.sum_sum_type, shear_apply, shearT, Sum.elim_inl, Sum.elim_inr, sub_mul, mul_sub, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws.
-/
theorem traceDot_shear (u b : κ ⊕ κ → mixedEmbedding.mixedSpace F) :
    traceDot F (κ ⊕ κ) (shear u) b = traceDot F (κ ⊕ κ) u (shearT b) := by
  rw [traceDot_apply, traceDot_apply]
  congr 1
  simp only [dotProduct, Fintype.sum_sum_type, shear_apply, shearT, Sum.elim_inl, Sum.elim_inr, sub_mul, mul_sub,
    Finset.sum_sub_distrib]
  abel

def shearOp : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ]
    SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ shear

/- English proof (translation)
Rewrite using `[shearOp, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]`.
-/
theorem shearOp_apply (f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ) (u) : shearOp f u = f (shear u) := by
  rw [shearOp, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]

/- English proof (translation)
Introduce `g`. Use `⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ shear.symm g, ?_⟩` and prove the remaining obligations. Use extensionality with `u`. Rewrite using `[shearOp_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]`.
-/
theorem shearOp_surjective : Function.Surjective (shearOp (F := F) (κ := κ)) := by
  intro g
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ shear.symm g, ?_⟩
  ext u
  rw [shearOp_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply]

/- English proof (translation)
Use function extensionality and compare the values at `u`. Rewrite using `[shearOp_apply, hg, hop, hop, shearOp_apply, ContinuousLinearEquiv.map_add, ContinuousLinearEquiv.apply_symm_apply, ← traceDot_shear, ← traceDot_shear, ContinuousLinearEquiv.apply_symm_apply]`.
-/
theorem shearOp_hop (a b : κ ⊕ κ → mixedEmbedding.mixedSpace F) (f g : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ)
    (hg : ⇑g = hop a b f) : ⇑(shearOp g) = hop (shear.symm a) (shearT b) (shearOp f) := by
  funext u
  rw [shearOp_apply, hg, hop, hop, shearOp_apply, ContinuousLinearEquiv.map_add,
    ContinuousLinearEquiv.apply_symm_apply, ← traceDot_shear, ← traceDot_shear, ContinuousLinearEquiv.apply_symm_apply]

end GlobalTheory.DiagHeisFourier

namespace GlobalTheory.DiagHeisFourier

open GlobalTheory.ArchFourier

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
Simplify using `[traceDot_apply, dotProduct, Fintype.sum_sum_type]`.
-/
theorem traceDot_elim_anti (v y : κ → mixedEmbedding.mixedSpace F) :
    traceDot F (κ ⊕ κ) (Sum.elim v v) (Sum.elim y (-y)) = 0 := by
  simp [traceDot_apply, dotProduct, Fintype.sum_sum_type]

/- English proof (translation)
Establish `hinj : Function.Injective (traceDot F (κ ⊕ κ))`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `z hz`. Conclude with `traceDot_nondeg z fun y => by rw [hz]; rfl`. Establish `hsurj` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq (K := ℝ) (V := κ ⊕ κ → mixedEmbedding.mixedSpace F)).symm).1 hinj`.

Take `⟨z, hz⟩` from `hsurj L.toLinearMap`. Conclude with `⟨z, fun u => by rw [hz]; rfl⟩`.
-/
theorem exists_traceDot_eq (L : (κ ⊕ κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) :
    ∃ z, ∀ u, L u = traceDot F (κ ⊕ κ) z u := by
  have hinj : Function.Injective (traceDot F (κ ⊕ κ)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    exact traceDot_nondeg z fun y => by rw [hz]; rfl
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ℝ) (V := κ ⊕ κ → mixedEmbedding.mixedSpace F)).symm).1 hinj
  obtain ⟨z, hz⟩ := hsurj L.toLinearMap
  exact ⟨z, fun u => by rw [hz]; rfl⟩

end GlobalTheory.DiagHeisFourier

namespace GlobalTheory

open GlobalTheory.ArchFourier GlobalTheory.DiagHeisFourier

/- English proof (translation)
Introduce `F _ _ κ _`. Use `haveI : BorelSpace (κ ⊕ κ → mixedEmbedding.mixedSpace F) := inferInstance`. Take `⟨E, hEb, hE⟩` from `exists_schwartz_fourier_form (V := κ ⊕ κ → mixedEmbedding.mixedSpace F) (traceDot F (κ ⊕ κ)) traceDot_comm traceDot_nondeg (Measure.addHaar : Measure (κ ⊕ κ → mixedEmbedding.mixedSpace F))`. Use `set A := shearOp.comp ((chirp (1 / 2)).comp (E.comp ((chirp (1 / 2)).comp E))) with hA`. Establish `hAs : Function.Surjective A` using `shearOp_surjective.comp ((chirp_surjective _).comp (hEb.2.comp ((chirp_surjective _).comp hEb.2)))`.

Establish `hmul : ∀ (z : κ ⊕ κ → mixedEmbedding.mixedSpace F) (f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ), ∃ f₁ : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ, ⇑f₁ = hop 0 z f`. Introduce `z f`. Set `Lz : (κ ⊕ κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ` to `LinearMap.toContinuousLinearMap ((traceDot F (κ ⊕ κ)).flip z)`. Establish `ht` using `GlobalTheory.SchOp.hasTemperateGrowth_ech_affine Lz 0`. Use `⟨SchwartzMap.smulLeftCLM ℂ (fun u => GlobalTheory.ArchSch.ech (Lz u + 0)) f, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `u`. Rewrite using `[SchwartzMap.smulLeftCLM_apply_apply ht, smul_eq_mul, hop]`. Simplify using `[Lz]`. Establish `hlaw : ∀ (z : κ ⊕ κ → mixedEmbedding.mixedSpace F) (f f₁ : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ), ⇑f₁ = hop 0 z f → ⇑(A f₁) = hop (Sum.elim (fun j => -z (Sum.inr j)) (fun j => -z (Sum.inr j))) (Sum.elim (fun j => -z (Sum.inl j)) (-fun j => -z (Sum.inl j))) (A f)`. Introduce `z f f₁ h₁`.

Establish `s1` using `fourier_hop _ E hE _ _ _ _ h₁`. Establish `s2` using `chirp_hop _ _ _ _ s1`. Establish `s3` using `fourier_hop _ E hE _ _ _ _ s2`. Establish `s4` using `chirp_hop _ _ _ _ s3`. Establish `s5` using `shearOp_hop _ _ _ _ s4`.

Establish `ea : shear.symm (-0 - P2 z) = Sum.elim (fun j => -z (Sum.inr j)) (fun j => -z (Sum.inr j))`. Apply the tactic sequence `funext i; cases i <;> simp [shear_symm_apply, P2]`. Establish `eb : shearT (-z - P2 (-0 - P2 z)) = Sum.elim (fun j => -z (Sum.inl j)) (-fun j => -z (Sum.inl j))`. Apply the tactic sequence `funext i; cases i <;> simp [shearT, P2]`. Rewrite `s5` using `[ea, eb]`.

Simplify `s5` using `only [neg_zero, zero_sub, hA, ContinuousLinearMap.comp_apply]`. Use `⟨A, hAs, fun z => ⟨fun j => -z (Sum.inr j), fun j => -z (Sum.inl j), fun f => ?_⟩, ?_⟩` and prove the remaining obligations. Take `⟨f₁, h₁⟩` from `hmul z f`. Use `⟨f₁, fun u => ?_, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[h₁, hop]`.

Simplify using `only [map_zero, LinearMap.zero_apply, zero_div, add_zero, traceDot_apply]`. Both sides reduce to the same expression. Rewrite using `[hlaw z f f₁ h₁, hop, traceDot_elim_anti, zero_div, add_zero, traceDot_apply]`. Both sides reduce to the same expression. Set `T : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ` to `(SchwartzMap.integralCLM ℂ (volume : Measure (GlobalTheory.DiagForm.Vi F κ))).comp ((GlobalTheory.DiagForm.compD F κ).comp A)`.

Establish `hT : ∀ (L : (κ ⊕ κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f f' : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ), (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f`. Introduce `L f f' hf'`. Take `⟨w, hw⟩` from `exists_traceDot_eq L`. Use `set z := (-(2 * Real.pi))⁻¹ • w with hz`. Establish `h₁ : ⇑f' = hop 0 z f`.

Use function extensionality and compare the values at `u`. Rewrite using `[hf', hop, hw]`. Simplify using `only [map_zero, LinearMap.zero_apply, zero_div, add_zero]`. Use `congr 1`. Rewrite using `[GlobalTheory.ArchSch.ech, traceDot_comm u z, hz, map_smul, LinearMap.smul_apply, smul_eq_mul]`.

Use `congr 1`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hl` using `hlaw z f f' h₁`.

Establish `e : ∀ p, GlobalTheory.DiagForm.compD F κ (A f') p = GlobalTheory.DiagForm.compD F κ (A f) (p + (GlobalTheory.DiagForm.eI F κ).symm (fun j => -z (Sum.inr j)))`. Introduce `p`. Express the relevant statement in the definitionally equal form `A f' (GlobalTheory.DiagForm.dI F κ p) = A f (GlobalTheory.DiagForm.dI F κ (p + (GlobalTheory.DiagForm.eI F κ).symm _))`. Rewrite using `[hl, hop, GlobalTheory.DiagForm.dI_apply, traceDot_elim_anti, traceDot_elim_anti, zero_div, add_zero, ech_zero', one_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `cases i <;> simp [GlobalTheory.DiagForm.dI_apply]`. Express the relevant statement in the definitionally equal form `SchwartzMap.integralCLM ℂ (volume : Measure (GlobalTheory.DiagForm.Vi F κ)) (GlobalTheory.DiagForm.compD F κ (A f')) = SchwartzMap.integralCLM ℂ (volume : Measure (GlobalTheory.DiagForm.Vi F κ)) (GlobalTheory.DiagForm.compD F κ (A f))`. Rewrite using `[SchwartzMap.integralCLM_apply, SchwartzMap.integralCLM_apply, integral_congr_ae (Filter.Eventually.of_forall e)]`. Conclude with `integral_add_right_eq_self (fun p => GlobalTheory.DiagForm.compD F κ (A f) p) _`.

Take `⟨a, ha⟩` from `GlobalTheory.CharInvForm.arch (κ ⊕ κ → mixedEmbedding.mixedSpace F) T hT`. Use `⟨a, ?_, fun f => ha f⟩` and prove the remaining obligations. Introduce `ha0`. Set `b : ContDiffBump (0 : κ ⊕ κ → mixedEmbedding.mixedSpace F)` to `⟨1, 2, one_pos, one_lt_two⟩`. Establish `h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ))` using `b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)`.

Set `g : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ` to `h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)`. Establish `hTg : SchwartzMap.integralCLM ℂ (volume : Measure (GlobalTheory.DiagForm.Vi F κ)) (GlobalTheory.DiagForm.compD F κ g) ≠ 0`. Rewrite using `[SchwartzMap.integralCLM_apply]`. Establish `e : ∀ u, GlobalTheory.DiagForm.compD F κ g u = ((b (GlobalTheory.DiagForm.dI F κ u) : ℝ) : ℂ)` using `fun u => rfl`. Simplify using `only [e, integral_complex_ofReal]`.

Establish `hcs : HasCompactSupport fun u : GlobalTheory.DiagForm.Vi F κ => b (GlobalTheory.DiagForm.dI F κ u)`. Use `HasCompactSupport.intro (isCompact_closedBall (0 : GlobalTheory.DiagForm.Vi F κ) (‖(GlobalTheory.DiagForm.eI F κ).symm.toContinuousLinearMap‖ * 2)) fun u hu => b.zero_of_le_dist ?_` and prove the remaining obligations. Rewrite using `[dist_zero_right]`. Assume the negation of the conclusion as `h`. Use `hu (mem_closedBall_zero_iff.2 ((GlobalTheory.DiagForm.norm_le_dI u).trans ?_))` and prove the remaining obligations.

Conclude with `mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge h)) (norm_nonneg _)`. Establish `hpos` using `(b.continuous.comp (GlobalTheory.DiagForm.dI F κ).continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := (volume : Measure (GlobalTheory.DiagForm.Vi F κ))) (x := 0) hcs (fun u => b.nonneg) (by`. Simplify using `only [Function.comp_apply, map_zero]`. Rewrite using `[b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]`. Conclude with `one_ne_zero)`.

Conclude with `hpos.ne'` after adjusting the coercions. Take `⟨f, hf⟩` from `hAs g`. Apply `hTg` to reduce the goal to its premises. Establish `h2` using `ha f`. Rewrite `h2` using `[ha0, zero_mul]`.

Rewrite using `[← hf]`. Conclude with `h2`.
-/
theorem diagHeis_archFourier : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ A : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ,
      Function.Surjective A ∧
      (∀ z : κ ⊕ κ → mixedEmbedding.mixedSpace F, ∃ x y : κ → mixedEmbedding.mixedSpace F,
        ∀ f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ, ∃ f₁ : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ,
          (∀ u, f₁ u = Complex.exp (-(2 * Real.pi * Complex.I) *
              ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (u ⬝ᵥ z) : ℝ) : ℂ)) * f u) ∧
          ∀ u, A f₁ u = Complex.exp (-(2 * Real.pi * Complex.I) *
              ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (u ⬝ᵥ Sum.elim y (-y)) : ℝ) : ℂ)) * A f (u + Sum.elim x x)) ∧
      ∃ C : ℂ, C ≠ 0 ∧ ∀ f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ,
        SchwartzMap.integralCLM ℂ (MeasureTheory.volume : Measure (GlobalTheory.DiagForm.Vi F κ)) (GlobalTheory.DiagForm.compD F κ (A f)) = C * f 0 := by
  intro F _ _ κ _
  haveI : BorelSpace (κ ⊕ κ → mixedEmbedding.mixedSpace F) := inferInstance
  obtain ⟨E, hEb, hE⟩ := exists_schwartz_fourier_form (V := κ ⊕ κ → mixedEmbedding.mixedSpace F)
    (traceDot F (κ ⊕ κ)) traceDot_comm traceDot_nondeg (Measure.addHaar : Measure (κ ⊕ κ → mixedEmbedding.mixedSpace F))
  set A := shearOp.comp ((chirp (1 / 2)).comp (E.comp ((chirp (1 / 2)).comp E))) with hA
  have hAs : Function.Surjective A :=
    shearOp_surjective.comp ((chirp_surjective _).comp (hEb.2.comp ((chirp_surjective _).comp hEb.2)))

  have hmul : ∀ (z : κ ⊕ κ → mixedEmbedding.mixedSpace F) (f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ),
      ∃ f₁ : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ, ⇑f₁ = hop 0 z f := by
    intro z f
    let Lz : (κ ⊕ κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ((traceDot F (κ ⊕ κ)).flip z)
    have ht := GlobalTheory.SchOp.hasTemperateGrowth_ech_affine Lz 0
    refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u => GlobalTheory.ArchSch.ech (Lz u + 0)) f, ?_⟩
    funext u
    rw [SchwartzMap.smulLeftCLM_apply_apply ht, smul_eq_mul, hop]
    simp [Lz]

  have hlaw : ∀ (z : κ ⊕ κ → mixedEmbedding.mixedSpace F) (f f₁ : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ),
      ⇑f₁ = hop 0 z f →
      ⇑(A f₁) = hop (Sum.elim (fun j => -z (Sum.inr j)) (fun j => -z (Sum.inr j)))
        (Sum.elim (fun j => -z (Sum.inl j)) (-fun j => -z (Sum.inl j))) (A f) := by
    intro z f f₁ h₁
    have s1 := fourier_hop _ E hE _ _ _ _ h₁
    have s2 := chirp_hop _ _ _ _ s1
    have s3 := fourier_hop _ E hE _ _ _ _ s2
    have s4 := chirp_hop _ _ _ _ s3
    have s5 := shearOp_hop _ _ _ _ s4
    have ea : shear.symm (-0 - P2 z) = Sum.elim (fun j => -z (Sum.inr j)) (fun j => -z (Sum.inr j)) := by
      funext i; cases i <;> simp [shear_symm_apply, P2]
    have eb : shearT (-z - P2 (-0 - P2 z)) = Sum.elim (fun j => -z (Sum.inl j)) (-fun j => -z (Sum.inl j)) := by
      funext i; cases i <;> simp [shearT, P2]
    rw [ea, eb] at s5
    simpa only [neg_zero, zero_sub, hA, ContinuousLinearMap.comp_apply] using s5
  refine ⟨A, hAs, fun z => ⟨fun j => -z (Sum.inr j), fun j => -z (Sum.inl j), fun f => ?_⟩, ?_⟩
  · obtain ⟨f₁, h₁⟩ := hmul z f
    refine ⟨f₁, fun u => ?_, fun u => ?_⟩
    · rw [h₁, hop]
      simp only [map_zero, LinearMap.zero_apply, zero_div, add_zero, traceDot_apply]
      rfl
    · rw [hlaw z f f₁ h₁, hop, traceDot_elim_anti, zero_div, add_zero, traceDot_apply]
      rfl
  · let T : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ :=
      (SchwartzMap.integralCLM ℂ (volume : Measure (GlobalTheory.DiagForm.Vi F κ))).comp ((GlobalTheory.DiagForm.compD F κ).comp A)
    have hT : ∀ (L : (κ ⊕ κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)
        (f f' : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ),
        (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f := by
      intro L f f' hf'
      obtain ⟨w, hw⟩ := exists_traceDot_eq L
      set z := (-(2 * Real.pi))⁻¹ • w with hz
      have h₁ : ⇑f' = hop 0 z f := by
        funext u
        rw [hf', hop, hw]
        simp only [map_zero, LinearMap.zero_apply, zero_div, add_zero]
        congr 1
        rw [GlobalTheory.ArchSch.ech, traceDot_comm u z, hz, map_smul, LinearMap.smul_apply, smul_eq_mul]
        congr 1
        have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        push_cast
        field_simp
      have hl := hlaw z f f' h₁
      have e : ∀ p, GlobalTheory.DiagForm.compD F κ (A f') p =
          GlobalTheory.DiagForm.compD F κ (A f) (p + (GlobalTheory.DiagForm.eI F κ).symm (fun j => -z (Sum.inr j))) := by
        intro p
        change A f' (GlobalTheory.DiagForm.dI F κ p) = A f (GlobalTheory.DiagForm.dI F κ (p + (GlobalTheory.DiagForm.eI F κ).symm _))
        rw [hl, hop, GlobalTheory.DiagForm.dI_apply, traceDot_elim_anti, traceDot_elim_anti, zero_div, add_zero, ech_zero',
          one_mul]
        congr 1
        funext i
        cases i <;> simp [GlobalTheory.DiagForm.dI_apply]
      change SchwartzMap.integralCLM ℂ (volume : Measure (GlobalTheory.DiagForm.Vi F κ)) (GlobalTheory.DiagForm.compD F κ (A f')) =
        SchwartzMap.integralCLM ℂ (volume : Measure (GlobalTheory.DiagForm.Vi F κ)) (GlobalTheory.DiagForm.compD F κ (A f))
      rw [SchwartzMap.integralCLM_apply, SchwartzMap.integralCLM_apply,
        integral_congr_ae (Filter.Eventually.of_forall e)]
      exact integral_add_right_eq_self (fun p => GlobalTheory.DiagForm.compD F κ (A f) p) _
    obtain ⟨a, ha⟩ := GlobalTheory.CharInvForm.arch (κ ⊕ κ → mixedEmbedding.mixedSpace F) T hT
    refine ⟨a, ?_, fun f => ha f⟩
    intro ha0
    let b : ContDiffBump (0 : κ ⊕ κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
    have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
      b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    let g : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ :=
      h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
    have hTg : SchwartzMap.integralCLM ℂ (volume : Measure (GlobalTheory.DiagForm.Vi F κ)) (GlobalTheory.DiagForm.compD F κ g) ≠ 0 := by
      rw [SchwartzMap.integralCLM_apply]
      have e : ∀ u, GlobalTheory.DiagForm.compD F κ g u = ((b (GlobalTheory.DiagForm.dI F κ u) : ℝ) : ℂ) := fun u => rfl
      simp only [e, integral_complex_ofReal]
      have hcs : HasCompactSupport fun u : GlobalTheory.DiagForm.Vi F κ => b (GlobalTheory.DiagForm.dI F κ u) := by
        refine HasCompactSupport.intro (isCompact_closedBall (0 : GlobalTheory.DiagForm.Vi F κ)
          (‖(GlobalTheory.DiagForm.eI F κ).symm.toContinuousLinearMap‖ * 2)) fun u hu => b.zero_of_le_dist ?_
        rw [dist_zero_right]
        by_contra h
        refine hu (mem_closedBall_zero_iff.2 ((GlobalTheory.DiagForm.norm_le_dI u).trans ?_))
        exact mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge h)) (norm_nonneg _)
      have hpos := (b.continuous.comp (GlobalTheory.DiagForm.dI F κ).continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
        (μ := (volume : Measure (GlobalTheory.DiagForm.Vi F κ))) (x := 0) hcs (fun u => b.nonneg) (by
          simp only [Function.comp_apply, map_zero]
          rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
          exact one_ne_zero)
      exact_mod_cast hpos.ne'
    obtain ⟨f, hf⟩ := hAs g
    apply hTg
    have h2 := ha f
    rw [ha0, zero_mul] at h2
    rw [← hf]
    exact h2

end GlobalTheory
