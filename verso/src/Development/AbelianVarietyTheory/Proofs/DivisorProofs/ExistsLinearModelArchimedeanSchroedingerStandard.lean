import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSpaceVecPairAsAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped RealInnerProductSpace

noncomputable section

namespace GlobalTheory.WeilAdm.RealModel

variable {F : Type} [Field F] [NumberField F]

def pt (a : mixedEmbedding.mixedSpace F) : AdeleRing (𝓞 F) F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0)

def fstH : AdeleRing (𝓞 F) F →+* InfiniteAdeleRing F := RingHom.fst _ _

def sndH : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _

/- English proof (translation)
The claim follows from `Prod.ext h1 h2`.
-/
theorem pt_ext {x y : AdeleRing (𝓞 F) F} (h1 : fstH x = fstH y) (h2 : sndH x = sndH y) : x = y :=
  Prod.ext h1 h2

/- English proof (translation)
Use `pt_ext ?_ ?_` and prove the remaining obligations. Simplify using `only [dotProduct, map_sum, map_mul] show ∑ i, (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i) * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i) = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (∑ i, z i * y i)`. Simplify using `only [map_sum, map_mul]`. Simplify using `only [dotProduct, map_sum, map_mul] show ∑ i, (0 : FiniteAdeleRing (𝓞 F) F) * 0 = 0`. Simplify using the standard rewrite rules.
-/
theorem dot_infE_infE {κ : Type} [Fintype κ] (z y : κ → mixedEmbedding.mixedSpace F) :
    infE F z ⬝ᵥ infE F y = pt (∑ i, z i * y i) := by
  refine pt_ext ?_ ?_
  · simp only [dotProduct, map_sum, map_mul]
    show ∑ i, (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i) * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i) = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (∑ i, z i * y i)
    simp only [map_sum, map_mul]
  · simp only [dotProduct, map_sum, map_mul]
    show ∑ i, (0 : FiniteAdeleRing (𝓞 F) F) * 0 = 0
    simp

/- English proof (translation)
Use `set c : InfiniteAdeleRing F := fstH (⅟(2 : AdeleRing (𝓞 F) F))`. Use `⟨InfiniteAdeleRing.ringEquiv_mixedSpace F (c * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm S), ?_, ?_⟩` and prove the remaining obligations. Use `pt_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul] show c * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm S = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _`. Rewrite using `[RingEquiv.symm_apply_apply]`.

Rewrite using `[map_mul] show _ * (0 : FiniteAdeleRing (𝓞 F) F) = 0`. Conclude with `mul_zero _`. Establish `hc : c * 2 = 1`. Establish `h` using `congrArg fstH (invOf_mul_self (2 : AdeleRing (𝓞 F) F))`. Rewrite `h` using `[map_mul, map_ofNat, map_one]`. Then use the resulting hypothesis.

Rewrite using `[← map_add, ← add_mul, ← mul_two, hc, one_mul, RingEquiv.apply_symm_apply]`.
-/
theorem invOf_two_mul_pt (S : mixedEmbedding.mixedSpace F) :
    ∃ t, ⅟(2 : AdeleRing (𝓞 F) F) * pt S = pt t ∧ t + t = S := by
  set c : InfiniteAdeleRing F := fstH (⅟(2 : AdeleRing (𝓞 F) F))
  refine ⟨InfiniteAdeleRing.ringEquiv_mixedSpace F (c * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm S), ?_, ?_⟩
  · refine pt_ext ?_ ?_
    · rw [map_mul]
      show c * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm S = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _
      rw [RingEquiv.symm_apply_apply]
    · rw [map_mul]
      show _ * (0 : FiniteAdeleRing (𝓞 F) F) = 0
      exact mul_zero _
  · have hc : c * 2 = 1 := by
      have h := congrArg fstH (invOf_mul_self (2 : AdeleRing (𝓞 F) F))
      rwa [map_mul, map_ofNat, map_one] at h
    rw [← map_add, ← add_mul, ← mul_two, hc, one_mul, RingEquiv.apply_symm_apply]

/- English proof (translation)
Establish `hψ' : ∀ a, ψ (pt a) = Complex.exp (2 * Real.pi * Complex.I * β a)` using `hψ`. Take `⟨t, ht, htt⟩` from `invOf_two_mul_pt (F := F) (∑ i, v.1 i * v.2 i)`. Establish `hsum : ∀ a b : mixedEmbedding.mixedSpace F, pt (F` using `F) a + pt b = pt (a + b) := by`. Introduce `a b`. Use `pt_ext ?_ ?_` and prove the remaining obligations.

Rewrite using `[map_add]`. Conclude with `(map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ _).symm`. Rewrite using `[map_add]`. Conclude with `add_zero (0 : FiniteAdeleRing (𝓞 F) F)`. Establish `hbt : β t = β (∑ i, v.1 i * v.2 i) / 2`.

Rewrite using `[← htt, map_add]`. Expand and normalize the polynomial expressions, which then agree. Use `show ψ (infE F z ⬝ᵥ infE F v.2 + ⅟(2 : AdeleRing (𝓞 F) F) * (infE F v.1 ⬝ᵥ infE F v.2)) * φ (z + v.1) = _`. Rewrite using `[dot_infE_infE, dot_infE_infE, ht, hsum, hψ', map_add, hbt]`. Use `push_cast`.

Put the polynomial expressions in normal form.
-/
theorem schrInf_eq (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hψ : ∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) =
      Complex.exp (2 * Real.pi * Complex.I * β a))
    {κ : Type} [Fintype κ] (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (z : κ → mixedEmbedding.mixedSpace F) :
    schrInf F ψ v φ z = Complex.exp (2 * Real.pi * Complex.I *
      (β (∑ i, z i * v.2 i) + β (∑ i, v.1 i * v.2 i) / 2)) * φ (z + v.1) := by
  have hψ' : ∀ a, ψ (pt a) = Complex.exp (2 * Real.pi * Complex.I * β a) := hψ
  obtain ⟨t, ht, htt⟩ := invOf_two_mul_pt (F := F) (∑ i, v.1 i * v.2 i)
  have hsum : ∀ a b : mixedEmbedding.mixedSpace F, pt (F := F) a + pt b = pt (a + b) := by
    intro a b
    refine pt_ext ?_ ?_
    · rw [map_add]
      exact (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ _).symm
    · rw [map_add]
      exact add_zero (0 : FiniteAdeleRing (𝓞 F) F)
  have hbt : β t = β (∑ i, v.1 i * v.2 i) / 2 := by
    rw [← htt, map_add]; ring
  show ψ (infE F z ⬝ᵥ infE F v.2 + ⅟(2 : AdeleRing (𝓞 F) F) * (infE F v.1 ⬝ᵥ infE F v.2)) * φ (z + v.1) = _
  rw [dot_infE_infE, dot_infE_infE, ht, hsum, hψ', map_add, hbt]
  push_cast
  ring_nf

end GlobalTheory.WeilAdm.RealModel

namespace GlobalTheory.WeilAdm.RealModel

variable {F : Type} [Field F] [NumberField F]

def bil (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z y => β (∑ i, z i * y i))
    (fun z z' y => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add])
    (fun c z y => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul, smul_eq_mul])
    (fun z y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add])
    (fun c z y => by simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul, smul_eq_mul])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bil_apply (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) {κ : Type} [Fintype κ]
    (z y : κ → mixedEmbedding.mixedSpace F) : bil β κ z y = β (∑ i, z i * y i) := rfl

def qmap (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) {κ : Type} [Fintype κ] {n : ℕ}
    (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)) :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun y := (InnerProductSpace.toDual ℝ _).symm
    (LinearMap.toContinuousLinearMap (((bil β κ).flip y).comp (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] _).toLinearMap))
  map_add' y y' := by
    refine ext_inner_right ℝ fun x => ?_
    simp [InnerProductSpace.toDual_symm_apply, inner_add_left]
  map_smul' c y := by
    refine ext_inner_right ℝ fun x => ?_
    simp [InnerProductSpace.toDual_symm_apply, real_inner_smul_left]

/- English proof (translation)
Simplify using `[qmap, InnerProductSpace.toDual_symm_apply]`.
-/
theorem inner_qmap (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) {κ : Type} [Fintype κ] {n : ℕ}
    (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)) (y : κ → mixedEmbedding.mixedSpace F)
    (x : EuclideanSpace ℝ (Fin n)) : ⟪qmap β Q y, x⟫ = bil β κ (Q x) y := by
  simp [qmap, InnerProductSpace.toDual_symm_apply]

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `y hy`. Assume the negation of the conclusion as `hne`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hne`. Take `⟨b, hb⟩` from `hβ (y i) hi`.

Establish `h` using `inner_qmap β Q y (Q.symm (Pi.single i b))`. Rewrite `h` using `[hy, inner_zero_left, ContinuousLinearEquiv.apply_symm_apply, bil_apply]`. Establish `hs : ∑ j, (Pi.single i b : κ → mixedEmbedding.mixedSpace F) j * y j = y i * b`. Rewrite using `[Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]`. Simplify using `[mul_comm]`.

Rewrite `h` using `[hs]`. Conclude with `hb h.symm`.
-/
theorem qmap_injective (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (hβ : ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0)
    {κ : Type} [Fintype κ] {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)) :
    Function.Injective (qmap β Q) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  by_contra hne
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  obtain ⟨b, hb⟩ := hβ (y i) hi
  have h := inner_qmap β Q y (Q.symm (Pi.single i b))
  rw [hy, inner_zero_left, ContinuousLinearEquiv.apply_symm_apply, bil_apply] at h
  have hs : ∑ j, (Pi.single i b : κ → mixedEmbedding.mixedSpace F) j * y j = y i * b := by
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
    simp [mul_comm]
  rw [hs] at h
  exact hb h.symm

def qEquiv (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (hβ : ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0)
    {κ : Type} [Fintype κ] {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)) :
    (κ → mixedEmbedding.mixedSpace F) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.linearEquivOfInjective (qmap β Q) (qmap_injective β hβ Q) Q.toLinearEquiv.finrank_eq.symm

/- English proof (translation)
Conclude with `(qEquiv β hβ Q).apply_symm_apply q`.
-/
theorem qmap_qEquiv_symm (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (hβ : ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0)
    {κ : Type} [Fintype κ] {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F))
    (q : EuclideanSpace ℝ (Fin n)) : qmap β Q ((qEquiv β hβ Q).symm q) = q := by
  exact (qEquiv β hβ Q).apply_symm_apply q

def Peq {V : Type} [AddCommGroup V] [Module ℝ V] {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] V)
    (Y : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] V) : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] V × V where
  toFun w := (Q (GlobalTheory.RealWeil.pPart w), Y (GlobalTheory.RealWeil.qPart w))
  invFun p := Sum.elim (WithLp.ofLp (Q.symm p.1)) (WithLp.ofLp (Y.symm p.2))
  map_add' w w' := by simp [GlobalTheory.RealWeil.pPart_add, GlobalTheory.RealWeil.qPart_add]
  map_smul' c w := by simp [GlobalTheory.RealWeil.pPart_smul, GlobalTheory.RealWeil.qPart_smul]
  left_inv w := by
    funext j
    cases j <;> simp [GlobalTheory.RealWeil.pPart, GlobalTheory.RealWeil.qPart]
  right_inv p := by
    have h1 : GlobalTheory.RealWeil.pPart (Sum.elim (WithLp.ofLp (Q.symm p.1)) (WithLp.ofLp (Y.symm p.2))) = Q.symm p.1 := by
      simp [GlobalTheory.RealWeil.pPart]
    have h2 : GlobalTheory.RealWeil.qPart (Sum.elim (WithLp.ofLp (Q.symm p.1)) (WithLp.ofLp (Y.symm p.2))) = Y.symm p.2 := by
      simp [GlobalTheory.RealWeil.qPart]
    simp only [h1, h2, LinearEquiv.apply_symm_apply]

/- English proof (translation)
Introduce `F _ _ ψ β hψ hβ κ _`. Set `Q : EuclideanSpace ℝ (Fin (Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F))) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)` to `(LinearEquiv.ofFinrankEq _ _ finrank_euclideanSpace_fin).toContinuousLinearEquiv`. Set `Y` to `(qEquiv β hβ Q).symm`. Use `⟨_, Q, Peq Q.toLinearEquiv Y, fun w φ => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`.

Establish `hq` using `qmap_qEquiv_symm β hβ Q (GlobalTheory.RealWeil.qPart w)`. Establish `h1` using `inner_qmap β Q (Y (GlobalTheory.RealWeil.qPart w)) x`. Establish `h2` using `inner_qmap β Q (Y (GlobalTheory.RealWeil.qPart w)) (GlobalTheory.RealWeil.pPart w)`. Rewrite `h1`, `h2` using `[hq, bil_apply]`. Simplify using `only [Function.comp_apply, GlobalTheory.RealWeil.rhoFun, GlobalTheory.RealWeil.phase]`.

Rewrite using `[schrInf_eq ψ β hψ]`. Use `show Complex.exp (2 * Real.pi * Complex.I * (β (∑ i, Q x i * Y (GlobalTheory.RealWeil.qPart w) i) + β (∑ i, Q (GlobalTheory.RealWeil.pPart w) i * Y (GlobalTheory.RealWeil.qPart w) i) / 2)) * φ (Q x + Q (GlobalTheory.RealWeil.pPart w)) = _`. Rewrite using `[← h1, ← h2, ← map_add, real_inner_comm (GlobalTheory.RealWeil.pPart w)]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_model : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) =
      Complex.exp (2 * Real.pi * Complex.I * β a)) →
    (∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0) → ∀ (κ : Type) [Fintype κ],
    ∃ (n : ℕ) (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F))
      (P : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      ∀ w (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ),
        GlobalTheory.WeilAdm.schrInf F ψ (P w) φ ∘ Q = GlobalTheory.RealWeil.rhoFun w (φ ∘ Q) := by
  intro F _ _ ψ β hψ hβ κ _
  let Q : EuclideanSpace ℝ (Fin (Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F))) ≃L[ℝ]
      (κ → mixedEmbedding.mixedSpace F) :=
    (LinearEquiv.ofFinrankEq _ _ finrank_euclideanSpace_fin).toContinuousLinearEquiv
  let Y := (qEquiv β hβ Q).symm
  refine ⟨_, Q, Peq Q.toLinearEquiv Y, fun w φ => ?_⟩
  funext x
  have hq := qmap_qEquiv_symm β hβ Q (GlobalTheory.RealWeil.qPart w)
  have h1 := inner_qmap β Q (Y (GlobalTheory.RealWeil.qPart w)) x
  have h2 := inner_qmap β Q (Y (GlobalTheory.RealWeil.qPart w)) (GlobalTheory.RealWeil.pPart w)
  rw [hq, bil_apply] at h1 h2
  simp only [Function.comp_apply, GlobalTheory.RealWeil.rhoFun, GlobalTheory.RealWeil.phase]
  rw [schrInf_eq ψ β hψ]
  show Complex.exp (2 * Real.pi * Complex.I * (β (∑ i, Q x i * Y (GlobalTheory.RealWeil.qPart w) i) +
      β (∑ i, Q (GlobalTheory.RealWeil.pPart w) i * Y (GlobalTheory.RealWeil.qPart w) i) / 2)) *
      φ (Q x + Q (GlobalTheory.RealWeil.pPart w)) = _
  rw [← h1, ← h2, ← map_add, real_inner_comm (GlobalTheory.RealWeil.pPart w)]
  congr 2
  push_cast
  ring

end GlobalTheory.WeilAdm.RealModel
