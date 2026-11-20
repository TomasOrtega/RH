import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeUnipRad
open Matrix NumberField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UnipFin

open Formalism.L2.SG.HidaSetting

/- English proof (translation)
Rewrite using `[Finsupp.mem_span_image_iff_linearCombination]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨l, hl, rfl⟩`. Use `⟨l, fun i hi => (Finsupp.mem_supported' R l).1 hl i hi, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum_fintype]`.

Introduce `i`. Conclude with `zero_smul R _`. Introduce and unpack `⟨f, hf, rfl⟩`. Use `⟨Finsupp.equivFunOnFinite.symm f, (Finsupp.mem_supported' R _).2 fun i hi => hf i hi, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum_fintype]`.

Both sides reduce to the same expression. Introduce `i`. Conclude with `zero_smul R _`.
-/
theorem mem_span_image_iff {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (v : ι → M) (s : Set ι) (w : M) :
    w ∈ Submodule.span R (v '' s) ↔ ∃ f : ι → R, (∀ i, i ∉ s → f i = 0) ∧ ∑ i, f i • v i = w := by
  rw [Finsupp.mem_span_image_iff_linearCombination]
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l, fun i hi => (Finsupp.mem_supported' R l).1 hl i hi, ?_⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; exact zero_smul R _
  · rintro ⟨f, hf, rfl⟩
    refine ⟨Finsupp.equivFunOnFinite.symm f, (Finsupp.mem_supported' R _).2 fun i hi => hf i hi, ?_⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    · rfl
    · intro i; exact zero_smul R _

variable (I : Formalism.MainNotions.S.AutInst)

/- English proof (translation)
Use `show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Formalism.MainNotions.S.Af I.F)) (e ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F)) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul]`. Both sides reduce to the same expression.
-/
theorem sigR_inclE (e : I.E) :
    Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F) (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) e) =
      Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (starRingEnd I.E e) := by
  show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Formalism.MainNotions.S.Af I.F)) (e ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F)) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

/- English proof (translation)
Simplify using `only [hA, Formalism.UG.hform, incl, Matrix.map_apply, map_sum, map_mul, sigR_inclE]`.
-/
theorem hA_incl_incl (p q : Fin I.n → I.E) :
    hA I (incl I p) (incl I q) =
      Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J p q) := by
  simp only [hA, Formalism.UG.hform, incl, Matrix.map_apply, map_sum, map_mul, sigR_inclE]

variable {I} {ρ : ℕ} (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E)

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, incl, map_mul]`. Conclude with `Finset.sum_congr rfl fun a _ => by ring`.
-/
theorem mulVec_flag (v : Fin ρ → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :
    (Matrix.of fun k a => c a * x a k).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) *ᵥ v =
      ∑ a, (v a * Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (c a)) • incl I (x a) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, incl, map_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.of_apply, map_sum, map_mul, hA, Formalism.UG.hform, incl, sigR_inclE, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem mulVec_dual (y : VA I) (a : Fin ρ) :
    ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map
      (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) *ᵥ y) a =
      Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (starRingEnd I.E (c a)) * hA I (incl I (x a)) y := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply,
    Matrix.of_apply, map_sum, map_mul, hA, Formalism.UG.hform, incl, sigR_inclE, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Introduce `I ρ x c z hc hz N`. Set `EA` to `(Matrix.of fun k a => c a * x a k).map (Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F))`. Set `w : Fin ρ → VA I` to `fun a => incl I (x a)`. Establish `hcol : ∀ a, (fun k => EA k a) = Formalism.UG.inclE (F` using `I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a) • w a := by`. Introduce `a`.

Use function extensionality and compare the values at `k`. Simplify using `only [EA, w, Matrix.map_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, incl, map_mul]`. Establish `hinv : ∀ a, Formalism.UG.inclE (F` using `I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹ * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a) = 1 := fun a => by`. Rewrite using `[← map_mul, inv_mul_cancel₀ (hc a), map_one]`. Establish `hinv' : ∀ a, Formalism.UG.inclE (F` using `I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a) * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹ = 1 := fun a => by`.

Rewrite using `[← map_mul, mul_inv_cancel₀ (hc a), map_one]`. Establish `hK : ∀ y : VA I, (Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (Formalism.UG.inclE (F` using `I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F)) *ᵥ y = 0 ↔ ∀ a, hA I (incl I (x a)) y = 0 := by`. Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce `h a`.

Establish `hs : starRingEnd I.E (c a) ≠ 0` using `(map_ne_zero _).2 (hc a)`. Establish `h1` using `congrFun h a`. Rewrite `h1` using `[mulVec_dual]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← map_mul, inv_mul_cancel₀ hs, map_one, one_mul]`.

Use `_ = 0 := by rw [h1, Pi.zero_apply, mul_zero]`. Introduce `h`. Use function extensionality and compare the values at `a`. Rewrite using `[mulVec_dual, h a, mul_zero, Pi.zero_apply]`. Establish `hspan : ∀ y : VA I, (∃ v, N *ᵥ y = y + EA *ᵥ v) ↔ (N - 1) *ᵥ y ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range w)`.

Introduce `y`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv⟩`. Use `⟨fun a => v a * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a), ?_⟩` and prove the remaining obligations.

Rewrite using `[← mulVec_flag, Matrix.sub_mulVec, hv, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws. Introduce and unpack `⟨f, hf⟩`. Use `⟨fun a => f a * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[mulVec_flag]`.

Repeatedly rewrite using `[mul_assoc, hinv, mul_one]`. Rewrite using `[hf, Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨T, hT, hNT⟩, h2⟩`.

Establish `hdual : ∀ y : VA I, (∀ a, hA I (incl I (x a)) y = 0) → (N - 1) *ᵥ y ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range w)` using `fun y hy => (hspan y).1 (h2 y ((hK y).2 hy))`. Use `⟨fun a => ?_, hdual _ fun a => by rw [hA_incl_incl, hz a, map_zero], hdual⟩` and prove the remaining obligations. Establish `hv : N *ᵥ (fun k => EA k a) = (fun k => EA k a) + EA *ᵥ (fun b => T b a)`. Use function extensionality and compare the values at `fun k => congrFun (congrFun hNT k) a`. Rewrite `hv` using `[hcol, Matrix.mulVec_smul, mulVec_flag]`.

Establish `hw : (N - 1) *ᵥ w a = ∑ b, (Formalism.UG.inclE (F` using `I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹ * (T b a * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c b))) • w b := by`. Use `congrArg (fun v => Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹ • v) hv` as an intermediate fact. Simplify using `only [smul_add, smul_smul, hinv, one_smul, Finset.smul_sum] at this`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, this]`. Normalize the expressions using the abelian group laws.

Use `(mem_span_image_iff w _ _).2 ⟨fun b => Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹ * (T b a * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c b)), fun b hb => ?_, hw.symm⟩` and prove the remaining obligations. Use `show _ * (T b a * _) = 0`. Rewrite using `[hT b a (not_lt.1 hb), zero_mul, mul_zero]`. Introduce and unpack `⟨h1, -, h3⟩ choose f hf0 hfs using fun a => (mem_span_image_iff w _ _).1 (h1 a)`. Use `⟨⟨fun b a => Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a) * f a b * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c b)⁻¹, fun j i hij => ?_, ?_⟩, fun y hy => ?_⟩` and prove the remaining obligations.

Use `show _ * f i j * _ = 0`. Rewrite using `[hf0 i j (not_lt.2 hij), mul_zero, zero_mul]`. Use extensionality with `k a`. It suffices to establish `hv : N *ᵥ (fun k => EA k a) = (fun k => EA k a) + EA *ᵥ (fun b => Formalism.UG.inclE (F` using `I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a) * f a b * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c b)⁻¹) from congrFun hv k`. Rewrite using `[hcol, Matrix.mulVec_smul, mulVec_flag]`.

Repeatedly rewrite using `[mul_assoc, hinv, mul_one]`. Establish `hN : N *ᵥ w a = w a + (N - 1) *ᵥ w a`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws. Rewrite using `[hN, ← hfs a, smul_add, Finset.smul_sum]`.

Repeatedly rewrite using `[smul_smul]`. Both sides reduce to the same expression. Conclude with `(hspan y).2 (h3 y ((hK y).1 hy))`.
-/
theorem unip_flag_iff_Nfin : ∀ (I : Formalism.MainNotions.S.AutInst) {ρ : ℕ} (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E) (z : Fin I.n → I.E), (∀ a, c a ≠ 0) → (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (x a) z = 0) → ∀ (N : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), GlobalTheory.BesselChar.Unip ((Matrix.of fun k a => c a * x a k).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))) ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))) N ↔ ((∀ a : Fin ρ, (N - 1) *ᵥ Formalism.L2.SG.HidaSetting.incl I (x a) ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) ((fun b => Formalism.L2.SG.HidaSetting.incl I (x b)) '' {b | b.1 < a.1})) ∧ (N - 1) *ᵥ Formalism.L2.SG.HidaSetting.incl I z ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => Formalism.L2.SG.HidaSetting.incl I (x b)) ∧ ∀ y : Formalism.L2.SG.HidaSetting.VA I, (∀ a, Formalism.L2.SG.HidaSetting.hA I (Formalism.L2.SG.HidaSetting.incl I (x a)) y = 0) → (N - 1) *ᵥ y ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => Formalism.L2.SG.HidaSetting.incl I (x b))) := by
  intro I ρ x c z hc hz N

  let EA := (Matrix.of fun k a => c a * x a k).map (Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F))
  let w : Fin ρ → VA I := fun a => incl I (x a)
  have hcol : ∀ a, (fun k => EA k a) = Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a) • w a := by
    intro a; funext k
    simp only [EA, w, Matrix.map_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, incl, map_mul]
  have hinv : ∀ a, Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹ * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a) = 1 := fun a => by
    rw [← map_mul, inv_mul_cancel₀ (hc a), map_one]
  have hinv' : ∀ a, Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a) * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹ = 1 := fun a => by
    rw [← map_mul, mul_inv_cancel₀ (hc a), map_one]

  have hK : ∀ y : VA I, (Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F)) *ᵥ y = 0 ↔
      ∀ a, hA I (incl I (x a)) y = 0 := by
    intro y
    constructor
    · intro h a
      have hs : starRingEnd I.E (c a) ≠ 0 := (map_ne_zero _).2 (hc a)
      have h1 := congrFun h a
      rw [mulVec_dual] at h1
      calc hA I (incl I (x a)) y
          = Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (starRingEnd I.E (c a))⁻¹ * (Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (starRingEnd I.E (c a)) * hA I (incl I (x a)) y) := by
            rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hs, map_one, one_mul]
        _ = 0 := by rw [h1, Pi.zero_apply, mul_zero]
    · intro h
      funext a
      rw [mulVec_dual, h a, mul_zero, Pi.zero_apply]

  have hspan : ∀ y : VA I, (∃ v, N *ᵥ y = y + EA *ᵥ v) ↔
      (N - 1) *ᵥ y ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range w) := by
    intro y
    rw [Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨fun a => v a * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a), ?_⟩
      rw [← mulVec_flag, Matrix.sub_mulVec, hv, Matrix.one_mulVec]
      abel
    · rintro ⟨f, hf⟩
      refine ⟨fun a => f a * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹, ?_⟩
      rw [mulVec_flag]
      simp_rw [mul_assoc, hinv, mul_one]
      rw [hf, Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
  constructor
  · rintro ⟨⟨T, hT, hNT⟩, h2⟩
    have hdual : ∀ y : VA I, (∀ a, hA I (incl I (x a)) y = 0) →
        (N - 1) *ᵥ y ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range w) :=
      fun y hy => (hspan y).1 (h2 y ((hK y).2 hy))
    refine ⟨fun a => ?_, hdual _ fun a => by rw [hA_incl_incl, hz a, map_zero], hdual⟩
    have hv : N *ᵥ (fun k => EA k a) = (fun k => EA k a) + EA *ᵥ (fun b => T b a) :=
      funext fun k => congrFun (congrFun hNT k) a
    rw [hcol, Matrix.mulVec_smul, mulVec_flag] at hv
    have hw : (N - 1) *ᵥ w a = ∑ b, (Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹ * (T b a * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c b))) • w b := by
      have := congrArg (fun v => Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹ • v) hv
      simp only [smul_add, smul_smul, hinv, one_smul, Finset.smul_sum] at this
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, this]
      abel
    refine (mem_span_image_iff w _ _).2 ⟨fun b => Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a)⁻¹ * (T b a * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c b)), fun b hb => ?_, hw.symm⟩
    show _ * (T b a * _) = 0
    rw [hT b a (not_lt.1 hb), zero_mul, mul_zero]
  · rintro ⟨h1, -, h3⟩
    choose f hf0 hfs using fun a => (mem_span_image_iff w _ _).1 (h1 a)
    refine ⟨⟨fun b a => Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a) * f a b * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c b)⁻¹, fun j i hij => ?_, ?_⟩, fun y hy => ?_⟩
    · show _ * f i j * _ = 0
      rw [hf0 i j (not_lt.2 hij), mul_zero, zero_mul]
    · ext k a
      suffices hv : N *ᵥ (fun k => EA k a) =
          (fun k => EA k a) + EA *ᵥ (fun b => Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c a) * f a b * Formalism.UG.inclE (F := I.F) (E := I.E) (Formalism.MainNotions.S.Af I.F) (c b)⁻¹) from congrFun hv k
      rw [hcol, Matrix.mulVec_smul, mulVec_flag]
      simp_rw [mul_assoc, hinv, mul_one]
      have hN : N *ᵥ w a = w a + (N - 1) *ᵥ w a := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
      rw [hN, ← hfs a, smul_add, Finset.smul_sum]
      simp_rw [smul_smul]
      rfl
    · exact (hspan y).2 (h3 y ((hK y).1 hy))

end GlobalTheory.UnipFin
