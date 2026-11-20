import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SetIntegralPreimageEqZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section
namespace GlobalTheory.ThetaInj
variable {F : Type} [Field F] [NumberField F]

def evIHom (F : Type) [Field F] [NumberField F] : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evI_eq (a : AF F) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F a = evIHom F a := rfl

def embI (F : Type) [Field F] [NumberField F] : F →+* mixedEmbedding.mixedSpace F :=
  (evIHom F).comp (algebraMap F (AF F))

/- English proof (translation)
The claim follows from `(Module.finBasis ℚ F).equivFun.injective.countable`.
-/
theorem countable_F : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

def infAd (m : mixedEmbedding.mixedSpace F) : AF F :=
  (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

/- English proof (translation)
Use `show (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m) = m`. Conclude with `RingEquiv.apply_symm_apply _ m`.
-/
theorem evIHom_infAd (m : mixedEmbedding.mixedSpace F) : evIHom F (infAd m) = m := by
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m) = m
  exact RingEquiv.apply_symm_apply _ m

/- English proof (translation)
Establish `h1 : u.1 = 0`. Establish `: (InfiniteAdeleRing.ringEquiv_mixedSpace F) u.1 = 0` using `hu`. Conclude with `(map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this`. Use `show (u.1 * _, u.2 * 0) = ((0 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))`. Rewrite using `[h1, zero_mul, mul_zero]`.
-/
theorem mul_infAd {u : AF F} (hu : evIHom F u = 0) (m : mixedEmbedding.mixedSpace F) : u * infAd m = 0 := by
  have h1 : u.1 = 0 := by
    have : (InfiniteAdeleRing.ringEquiv_mixedSpace F) u.1 = 0 := hu
    exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this
  show (u.1 * _, u.2 * 0) = ((0 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))
  rw [h1, zero_mul, mul_zero]

end GlobalTheory.ThetaInj

namespace GlobalTheory.ThetaInj
variable {F : Type} [Field F] [NumberField F]

def bI (F : Type) [Field F] [NumberField F] :
    Module.Basis (Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F))) ℝ (mixedEmbedding.mixedSpace F) :=
  Module.finBasis ℝ (mixedEmbedding.mixedSpace F)

def pI {κ : Type} (ξ : κ → F) : κ × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F)) → ℝ :=
  fun ij => Algebra.trace ℝ _ (embI F (ξ ij.1) * bI F ij.2)

def mI {κ : Type} (t : κ × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F)) → ℝ) (i : κ) :
    mixedEmbedding.mixedSpace F :=
  (-(1 / (2 * Real.pi))) • ∑ j, t (i, j) • bI F j

/- English proof (translation)
Use `set a := (fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i) with ha`. Establish `hAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) a`. Introduce `u hu`. Rewrite `hu` using `[evI_eq]`. Use `show u * a = 0`.

Simplify using `only [ha, dotProduct, Finset.mul_sum]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, mul_infAd hu, mul_zero]`. Rewrite using `[hψ.2.2 a hAt, evI_eq]`. Establish `hev : evIHom F a = ∑ i, embI F (ξ i) * mI t i`.

Simplify using `only [ha, dotProduct, map_sum, map_mul, evIHom_infAd, embI, RingHom.comp_apply]`. Establish `htr : Algebra.trace ℝ _ (evIHom F a) = -(1 / (2 * Real.pi)) * ∑ ij, pI ξ ij * t ij`. Rewrite using `[hev, map_sum, Fintype.sum_prod_type, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [mI, mul_smul_comm, Finset.mul_sum, map_smul, map_sum, smul_eq_mul, pI]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[htr]`. Use `congr 1`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr Real.pi_ne_zero`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem psi_dot {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) {κ : Type} [Fintype κ]
    (t : κ × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F)) → ℝ) (ξ : κ → F) :
    ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i)) =
      Complex.exp (((∑ ij, pI ξ ij * t ij : ℝ) : ℂ) * Complex.I) := by
  set a := (fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i) with ha
  have hAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) a := by
    intro u hu
    rw [evI_eq] at hu
    show u * a = 0
    simp only [ha, dotProduct, Finset.mul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [mul_left_comm, mul_infAd hu, mul_zero]
  rw [hψ.2.2 a hAt, evI_eq]
  have hev : evIHom F a = ∑ i, embI F (ξ i) * mI t i := by
    simp only [ha, dotProduct, map_sum, map_mul, evIHom_infAd, embI, RingHom.comp_apply]
  have htr : Algebra.trace ℝ _ (evIHom F a) = -(1 / (2 * Real.pi)) * ∑ ij, pI ξ ij * t ij := by
    rw [hev, map_sum, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mI, mul_smul_comm, Finset.mul_sum, map_smul, map_sum, smul_eq_mul, pI]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [htr]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

end GlobalTheory.ThetaInj

namespace GlobalTheory.ThetaInj
variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Assume the negation of the conclusion as `hne`. Establish `hz : ∀ z, Algebra.trace ℝ _ (embI F (ξ i) * z) = 0`. Introduce `z`. Rewrite using `[← (bI F).sum_repr z, Finset.mul_sum, map_sum]`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, map_smul, show Algebra.trace ℝ _ (embI F (ξ i) * bI F j) = 0 from congrFun h (i, j), smul_zero]`. Establish `h1` using `hz (embI F (ξ i)⁻¹)`. Rewrite `h1` using `[← map_mul, mul_inv_cancel₀ hne, map_one, ← map_one (algebraMap ℝ (mixedEmbedding.mixedSpace F)), Algebra.trace_algebraMap, mixedEmbedding.finrank, nsmul_eq_mul, mul_one, Nat.cast_eq_zero]`. Conclude with `(Module.finrank_pos (R := ℚ) (M := F)).ne' h1`.
-/
theorem pI_eq_zero {κ : Type} {ξ : κ → F} (h : pI ξ = 0) : ξ = 0 := by
  funext i
  by_contra hne
  have hz : ∀ z, Algebra.trace ℝ _ (embI F (ξ i) * z) = 0 := by
    intro z
    rw [← (bI F).sum_repr z, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [mul_smul_comm, map_smul, show Algebra.trace ℝ _ (embI F (ξ i) * bI F j) = 0 from congrFun h (i, j),
      smul_zero]
  have h1 := hz (embI F (ξ i)⁻¹)
  rw [← map_mul, mul_inv_cancel₀ hne, map_one, ← map_one (algebraMap ℝ (mixedEmbedding.mixedSpace F)),
    Algebra.trace_algebraMap, mixedEmbedding.finrank, nsmul_eq_mul, mul_one, Nat.cast_eq_zero] at h1
  exact (Module.finrank_pos (R := ℚ) (M := F)).ne' h1

/- English proof (translation)
Use function extensionality and compare the values at `ij`. Simplify using `[pI]`.
-/
theorem pI_zero {κ : Type} : pI (0 : κ → F) = 0 := by
  funext ij
  simp [pI]

/- English proof (translation)
Use `letI : MeasurableSpace (κ → F) := ⊤`. Use `haveI : MeasurableSingletonClass (κ → F) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩`. Use `haveI : Countable F := countable_F`. Establish `hint : Integrable c Measure.count` using `integrable_count_iff.mpr hc`. Establish `hp : Measurable (pI (F` using `F) (κ := κ)) := fun _ _ => MeasurableSpace.measurableSet_top`.

Establish `key` using `GlobalTheory.FourierPush.setIntegral_preimage_eq_zero (κ → F) Measure.count c hint (κ × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F)) → ℝ) pI hp ?_ {0} (measurableSet_singleton 0)`. Establish `hpre : pI ⁻¹' {0} = ({0} : Set (κ → F))`. Use extensionality with `ξ`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff]`. Conclude with `⟨pI_eq_zero, fun h => h ▸ pI_zero⟩`.

Rewrite `key` using `[hpre, integral_singleton]`. Simplify using `using key`. Introduce `l`. Establish `hI : Integrable (fun ξ => Complex.exp ((l (pI ξ) : ℂ) * Complex.I) * c ξ) Measure.count`. Use `integrable_count_iff.mpr (hc.congr fun ξ => ?_)` and prove the remaining obligations.

Rewrite using `[norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]`. Rewrite using `[integral_countable hI]`. Establish `hl : ∀ ξ : κ → F, l (pI ξ) = ∑ ij, pI ξ ij * l (fun k => if ij = k then 1 else 0)`. Introduce `ξ`. Rewrite using `[show l (pI ξ) = l.toLinearMap (pI ξ) from rfl, LinearMap.pi_apply_eq_sum_univ]`.

Simplify using `[smul_eq_mul]`. Use `h (fun ij => l (fun k => if ij = k then 1 else 0))` as an intermediate fact. Rewrite using `[← this]`. Use `tsum_congr fun ξ => ?_` and prove the remaining obligations. Rewrite using `[psi_dot hψ, ← hl]`.

Simplify using the standard rewrite rules.
-/
theorem coeff_zero {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ)
    (c : (κ → F) → ℂ) (hc : Summable fun ξ => ‖c ξ‖)
    (h : ∀ t : κ × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F)) → ℝ,
      ∑' ξ : κ → F, ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i)) * c ξ = 0) :
    c 0 = 0 := by
  classical
  letI : MeasurableSpace (κ → F) := ⊤
  haveI : MeasurableSingletonClass (κ → F) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  haveI : Countable F := countable_F
  have hint : Integrable c Measure.count := integrable_count_iff.mpr hc
  have hp : Measurable (pI (F := F) (κ := κ)) := fun _ _ => MeasurableSpace.measurableSet_top
  have key := GlobalTheory.FourierPush.setIntegral_preimage_eq_zero (κ → F) Measure.count c hint
    (κ × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F)) → ℝ) pI hp ?_ {0} (measurableSet_singleton 0)
  · have hpre : pI ⁻¹' {0} = ({0} : Set (κ → F)) := by
      ext ξ
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨pI_eq_zero, fun h => h ▸ pI_zero⟩
    rw [hpre, integral_singleton] at key
    simpa using key
  · intro l
    have hI : Integrable (fun ξ => Complex.exp ((l (pI ξ) : ℂ) * Complex.I) * c ξ) Measure.count := by
      refine integrable_count_iff.mpr (hc.congr fun ξ => ?_)
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    rw [integral_countable hI]
    have hl : ∀ ξ : κ → F, l (pI ξ) = ∑ ij, pI ξ ij * l (fun k => if ij = k then 1 else 0) := by
      intro ξ
      rw [show l (pI ξ) = l.toLinearMap (pI ξ) from rfl, LinearMap.pi_apply_eq_sum_univ]
      simp [smul_eq_mul]
    have := h (fun ij => l (fun k => if ij = k then 1 else 0))
    rw [← this]
    refine tsum_congr fun ξ => ?_
    rw [psi_dot hψ, ← hl]
    simp

end GlobalTheory.ThetaInj

namespace GlobalTheory.ThetaInj

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n d Y Wd M ψ hψ Z crd Φ₁ Φ₂ f h₁ h₂`. Use function extensionality and compare the values at `x`. Establish `hs : ∀ Φ, Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) → Summable fun ξ : Fin n × Fin d → F => ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖`. Introduce `Φ hΦ`. Use `GlobalTheory.WeilM.summable_norm_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F x hΦ)` as an intermediate fact.

Conclude with `this`. Establish `hsum : Summable fun ξ : Fin n × Fin d → F => ‖Φ₁ ((fun i => algebraMap F (AF F) (ξ i)) + x) - Φ₂ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖`. Use `((hs Φ₁ h₁.1).add (hs Φ₂ h₂.1)).of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_sub_le _ _)` and prove the remaining obligations. Establish `key` using `coeff_zero hψ (fun ξ => Φ₁ ((fun i => algebraMap F (AF F) (ξ i)) + x) - Φ₂ ((fun i => algebraMap F (AF F) (ξ i)) + x)) hsum ?_`. Establish `h0 : (fun i => algebraMap F (AF F) ((0 : Fin n × Fin d → F) i)) + x = x`.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Simplify using `only [h0, sub_eq_zero] at key`. Conclude with `key`. Introduce `t`.

Establish `hn : ∀ ξ : Fin n × Fin d → F, ‖ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i))‖ = 1` using `fun ξ => by`. Rewrite using `[psi_dot hψ]`. Conclude with `Complex.norm_exp_ofReal_mul_I _`. Establish `hS : ∀ Φ, Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) → Summable fun ξ : Fin n × Fin d → F => ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i)) * Φ ((fun i => algebraMap F (AF F) (ξ i)) + x)` using `fun Φ hΦ => Summable.of_norm ((hs Φ hΦ).congr fun ξ => by rw [norm_mul, hn, one_mul])`. Establish `hT : ∀ Φ, IsDatum M ψ crd Φ f → ψ (⅟(2 : AF F) * (x ⬝ᵥ fun i => infAd (mI t i))) * ∑' ξ : Fin n × Fin d → F, ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i)) * Φ ((fun i => algebraMap F (AF F) (ξ i)) + x) = f (crd (M.co.e.symm (x, fun i => infAd (mI t i))))`.

Introduce `Φ hΦ`. Rewrite using `[← hΦ.2 (M.co.e.symm (x, fun i => infAd (mI t i))), ← tsum_mul_left]`. Simplify using `only [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, LinearEquiv.apply_symm_apply, AddChar.map_add_eq_mul]`. Use `tsum_congr fun ξ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `hne : ψ (⅟(2 : AF F) * (x ⬝ᵥ fun i => infAd (mI t i))) ≠ 0`. Introduce `h0`. Use `AddChar.map_add_eq_mul ψ (⅟(2 : AF F) * (x ⬝ᵥ fun i => infAd (mI t i))) (-(⅟(2 : AF F) * (x ⬝ᵥ fun i => infAd (mI t i))))` as an intermediate fact. Rewrite `this` using `[add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul]`. Conclude with `one_ne_zero this`.

Establish `e2` using `mul_left_cancel₀ hne ((hT Φ₁ h₁).trans (hT Φ₂ h₂).symm)`. Simplify using `only [mul_sub]`. Rewrite using `[(hS Φ₁ h₁.1).tsum_sub (hS Φ₂ h₂.1), e2, sub_self]`.
-/
theorem theta_inj : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {Z : Type}
    (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → Z), ∀ (Φ₁ Φ₂ : (Fin n × Fin d → AF F) → ℂ) (f : Z → ℂ),
    IsDatum M ψ crd Φ₁ f → IsDatum M ψ crd Φ₂ f → Φ₁ = Φ₂ := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ hψ Z crd Φ₁ Φ₂ f h₁ h₂
  funext x
  have hs : ∀ Φ, Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) →
      Summable fun ξ : Fin n × Fin d → F => ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ := by
    intro Φ hΦ
    have := GlobalTheory.WeilM.summable_norm_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F x hΦ)
    exact this
  have hsum : Summable fun ξ : Fin n × Fin d → F =>
      ‖Φ₁ ((fun i => algebraMap F (AF F) (ξ i)) + x) - Φ₂ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ := by
    refine ((hs Φ₁ h₁.1).add (hs Φ₂ h₂.1)).of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_sub_le _ _)
  have key := coeff_zero hψ
    (fun ξ => Φ₁ ((fun i => algebraMap F (AF F) (ξ i)) + x) - Φ₂ ((fun i => algebraMap F (AF F) (ξ i)) + x))
    hsum ?_
  · have h0 : (fun i => algebraMap F (AF F) ((0 : Fin n × Fin d → F) i)) + x = x := by
      funext i; simp
    simp only [h0, sub_eq_zero] at key
    exact key
  · intro t
    have hn : ∀ ξ : Fin n × Fin d → F,
        ‖ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i))‖ = 1 := fun ξ => by
      rw [psi_dot hψ]; exact Complex.norm_exp_ofReal_mul_I _
    have hS : ∀ Φ, Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) → Summable fun ξ : Fin n × Fin d → F =>
        ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i)) *
          Φ ((fun i => algebraMap F (AF F) (ξ i)) + x) := fun Φ hΦ =>
      Summable.of_norm ((hs Φ hΦ).congr fun ξ => by rw [norm_mul, hn, one_mul])
    have hT : ∀ Φ, IsDatum M ψ crd Φ f →
        ψ (⅟(2 : AF F) * (x ⬝ᵥ fun i => infAd (mI t i))) * ∑' ξ : Fin n × Fin d → F,
          ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i)) *
            Φ ((fun i => algebraMap F (AF F) (ξ i)) + x) =
          f (crd (M.co.e.symm (x, fun i => infAd (mI t i)))) := by
      intro Φ hΦ
      rw [← hΦ.2 (M.co.e.symm (x, fun i => infAd (mI t i))), ← tsum_mul_left]
      simp only [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, LinearEquiv.apply_symm_apply,
        AddChar.map_add_eq_mul]
      refine tsum_congr fun ξ => ?_
      ring
    have hne : ψ (⅟(2 : AF F) * (x ⬝ᵥ fun i => infAd (mI t i))) ≠ 0 := by
      intro h0
      have := AddChar.map_add_eq_mul ψ (⅟(2 : AF F) * (x ⬝ᵥ fun i => infAd (mI t i)))
        (-(⅟(2 : AF F) * (x ⬝ᵥ fun i => infAd (mI t i))))
      rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at this
      exact one_ne_zero this
    have e2 := mul_left_cancel₀ hne ((hT Φ₁ h₁).trans (hT Φ₂ h₂).symm)
    simp only [mul_sub]
    rw [(hS Φ₁ h₁.1).tsum_sub (hS Φ₂ h₂.1), e2, sub_self]

end GlobalTheory.ThetaInj
