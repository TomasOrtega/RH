import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusMulVecX

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.DiagUnip

open Matrix

/- English proof (translation)
Establish `h : GlobalTheory.DblUnip.diagMat c J x y β = 1 + replicateCol Unit (-(c β) • y) * replicateRow Unit (J *ᵥ fun i => c (x i))`. Rewrite using `[← vecMulVec_eq Unit]`. Use extensionality with `i j`. Simplify using `[GlobalTheory.DblUnip.diagMat, vecMulVec, sub_eq_add_neg, mul_assoc]`. Rewrite using `[h, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, dotProduct_comm, hyx]`.

Simplify using the standard rewrite rules.
-/
theorem diag_det {R : Type} [CommRing R] {d : ℕ} (c : R →+* R) (J : Matrix (Fin d) (Fin d) R) (x y : Fin d → R) (β : R)
    (hyx : y ⬝ᵥ J *ᵥ (fun i => c (x i)) = -1) : (GlobalTheory.DblUnip.diagMat c J x y β).det = 1 + c β := by
  have h : GlobalTheory.DblUnip.diagMat c J x y β = 1 + replicateCol Unit (-(c β) • y) * replicateRow Unit (J *ᵥ fun i => c (x i)) := by
    rw [← vecMulVec_eq Unit]
    ext i j
    simp [GlobalTheory.DblUnip.diagMat, vecMulVec, sub_eq_add_neg, mul_assoc]
  rw [h, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, dotProduct_comm, hyx]
  simp

/- English proof (translation)
Establish `hI : ∀ (v : Fin d → R) (w : Fin d₁ → R), v ᵥ* I = 0 → v ⬝ᵥ (I *ᵥ w) = 0`. Introduce `v w h`. Rewrite using `[dotProduct_mulVec, h, zero_dotProduct]`. Establish `hP : ∀ z, (Mm * (1 + ((↑t⁻¹ : R) - 1) • vecMulVec x (J *ᵥ fun i => c (y i)))) *ᵥ z = Mm *ᵥ (z + (((↑t⁻¹ : R) - 1) * ((J *ᵥ fun i => c (y i)) ⬝ᵥ z)) • x)`. Introduce `z`.

Rewrite using `[← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, GlobalTheory.LeviTorus.vmv_mulVec, smul_smul]`. Establish `hD : ∀ z, GlobalTheory.DblUnip.diagMat c J x y ((↑t⁻¹ : R) - 1) *ᵥ z = z - (c ((↑t⁻¹ : R) - 1) * ((J *ᵥ fun i => c (x i)) ⬝ᵥ z)) • y`. Introduce `z`. Rewrite using `[GlobalTheory.DblUnip.diagMat, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, GlobalTheory.LeviTorus.vmv_mulVec, smul_smul]`. Establish `ht : (↑t⁻¹ : R) * t = 1` using `Units.inv_mul t`.

Establish `hx : (Mm * (1 + ((↑t⁻¹ : R) - 1) • vecMulVec x (J *ᵥ fun i => c (y i)))) *ᵥ x = GlobalTheory.DblUnip.diagMat c J x y ((↑t⁻¹ : R) - 1) *ᵥ x`. Rewrite using `[hP, hD, dotProduct_comm _ x, dotProduct_comm _ x, hXY, hXX]`. Rewrite using `[show x + (((↑t⁻¹ : R) - 1) * 1) • x = (↑t⁻¹ : R) • x by module, Matrix.mulVec_smul, hLx, smul_smul, ht, one_smul]`. Simplify using the standard rewrite rules. Establish `hy : (Mm * (1 + ((↑t⁻¹ : R) - 1) • vecMulVec x (J *ᵥ fun i => c (y i)))) *ᵥ y = GlobalTheory.DblUnip.diagMat c J x y ((↑t⁻¹ : R) - 1) *ᵥ y`.

Rewrite using `[hP, hD, dotProduct_comm _ y, dotProduct_comm _ y, hYY, hyx]`. Simplify using `only [mul_zero, zero_smul, add_zero, hLy, map_sub, map_one]`. Use `module`. Establish `hι : ∀ w, (Mm * (1 + ((↑t⁻¹ : R) - 1) • vecMulVec x (J *ᵥ fun i => c (y i)))) *ᵥ (I *ᵥ w) = GlobalTheory.DblUnip.diagMat c J x y ((↑t⁻¹ : R) - 1) *ᵥ (I *ᵥ w)`. Introduce `w`.

Rewrite using `[hP, hD, hI _ w hu, hI _ w hw]`. Simplify using `only [mul_zero, zero_smul, add_zero, sub_zero]`. Rewrite using `[Matrix.mulVec_mulVec, hLι]`. Apply `Matrix.ext_of_mulVec_single` to reduce the goal to its premises. Introduce `k`.

Take `⟨a, b, w, e⟩` from `hspan k`. Rewrite using `[e]`. Simplify using `only [Matrix.mulVec_add, Matrix.mulVec_smul, hx, hy, hι w]`.
-/
theorem diag_eq {R : Type} [CommRing R] {d d₁ : ℕ} (c : R →+* R) (J : Matrix (Fin d) (Fin d) R) (x y : Fin d → R)
    (I : Matrix (Fin d) (Fin d₁) R) (Mm : Matrix (Fin d) (Fin d) R) (t : Rˣ)
    (hXX : x ⬝ᵥ J *ᵥ (fun i => c (x i)) = 0) (hYY : y ⬝ᵥ J *ᵥ (fun i => c (y i)) = 0)
    (hXY : x ⬝ᵥ J *ᵥ (fun i => c (y i)) = 1) (hyx : y ⬝ᵥ J *ᵥ (fun i => c (x i)) = -1)
    (hu : (J *ᵥ fun i => c (y i)) ᵥ* I = 0) (hw : (J *ᵥ fun i => c (x i)) ᵥ* I = 0)
    (hLx : Mm *ᵥ x = (t : R) • x) (hLy : Mm *ᵥ y = c (↑t⁻¹ : R) • y) (hLι : Mm * I = I)
    (hspan : ∀ k : Fin d, ∃ (a b : R) (w : Fin d₁ → R), (Pi.single k 1 : Fin d → R) = a • x + b • y + I *ᵥ w) :
    Mm * (1 + ((↑t⁻¹ : R) - 1) • vecMulVec x (J *ᵥ fun i => c (y i))) =
      GlobalTheory.DblUnip.diagMat c J x y ((↑t⁻¹ : R) - 1) := by
  have hI : ∀ (v : Fin d → R) (w : Fin d₁ → R), v ᵥ* I = 0 → v ⬝ᵥ (I *ᵥ w) = 0 := by
    intro v w h; rw [dotProduct_mulVec, h, zero_dotProduct]
  have hP : ∀ z, (Mm * (1 + ((↑t⁻¹ : R) - 1) • vecMulVec x (J *ᵥ fun i => c (y i)))) *ᵥ z =
      Mm *ᵥ (z + (((↑t⁻¹ : R) - 1) * ((J *ᵥ fun i => c (y i)) ⬝ᵥ z)) • x) := by
    intro z
    rw [← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, GlobalTheory.LeviTorus.vmv_mulVec,
      smul_smul]
  have hD : ∀ z, GlobalTheory.DblUnip.diagMat c J x y ((↑t⁻¹ : R) - 1) *ᵥ z =
      z - (c ((↑t⁻¹ : R) - 1) * ((J *ᵥ fun i => c (x i)) ⬝ᵥ z)) • y := by
    intro z
    rw [GlobalTheory.DblUnip.diagMat, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, GlobalTheory.LeviTorus.vmv_mulVec,
      smul_smul]
  have ht : (↑t⁻¹ : R) * t = 1 := Units.inv_mul t
  have hx : (Mm * (1 + ((↑t⁻¹ : R) - 1) • vecMulVec x (J *ᵥ fun i => c (y i)))) *ᵥ x =
      GlobalTheory.DblUnip.diagMat c J x y ((↑t⁻¹ : R) - 1) *ᵥ x := by
    rw [hP, hD, dotProduct_comm _ x, dotProduct_comm _ x, hXY, hXX]
    rw [show x + (((↑t⁻¹ : R) - 1) * 1) • x = (↑t⁻¹ : R) • x by module, Matrix.mulVec_smul, hLx, smul_smul, ht, one_smul]
    simp
  have hy : (Mm * (1 + ((↑t⁻¹ : R) - 1) • vecMulVec x (J *ᵥ fun i => c (y i)))) *ᵥ y =
      GlobalTheory.DblUnip.diagMat c J x y ((↑t⁻¹ : R) - 1) *ᵥ y := by
    rw [hP, hD, dotProduct_comm _ y, dotProduct_comm _ y, hYY, hyx]
    simp only [mul_zero, zero_smul, add_zero, hLy, map_sub, map_one]
    module
  have hι : ∀ w, (Mm * (1 + ((↑t⁻¹ : R) - 1) • vecMulVec x (J *ᵥ fun i => c (y i)))) *ᵥ (I *ᵥ w) =
      GlobalTheory.DblUnip.diagMat c J x y ((↑t⁻¹ : R) - 1) *ᵥ (I *ᵥ w) := by
    intro w
    rw [hP, hD, hI _ w hu, hI _ w hw]
    simp only [mul_zero, zero_smul, add_zero, sub_zero]
    rw [Matrix.mulVec_mulVec, hLι]
  apply Matrix.ext_of_mulVec_single
  intro k
  obtain ⟨a, b, w, e⟩ := hspan k
  rw [e]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hx, hy, hι w]

end GlobalTheory.DiagUnip

namespace GlobalTheory.DiagUnip

open Matrix

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[incV, map_add]`.
-/
theorem incV_add {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {k : ℕ} (a b : Fin k → E) :
    incV F (a + b) = incV F a + incV F b := by
  funext i; simp [incV, map_add]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[incV, map_mul, smul_eq_mul]`.
-/
theorem incV_smul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {k : ℕ} (e : E) (a : Fin k → E) :
    incV F (e • a) = inclR (F := F) (AF F) e • incV F a := by
  funext i; simp [incV, map_mul, smul_eq_mul]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[incV]`.
-/
theorem incV_zero {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {k : ℕ} :
    incV F (0 : Fin k → E) = 0 := by
  funext i; simp [incV]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[incV, incM, mulVec, dotProduct, map_sum, map_mul]`.
-/
theorem incV_mulVec {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {k l : ℕ} (A : Matrix (Fin k) (Fin l) E)
    (u : Fin l → E) : incV F (A *ᵥ u) = incM F A *ᵥ incV F u := by
  funext i; simp [incV, incM, mulVec, dotProduct, map_sum, map_mul]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[incV]`. Simplify using `[incV, Pi.single_apply, h]`.
-/
theorem incV_single {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {k : ℕ} (j : Fin k) :
    incV F (Pi.single j (1 : E)) = Pi.single j 1 := by
  funext i; by_cases h : i = j
  · subst h; simp [incV]
  · simp [incV, Pi.single_apply, h]

end GlobalTheory.DiagUnip

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ t m hL`. Take `⟨hLx, hLy, hLι⟩` from `hL`. Establish `hσ` using `GlobalTheory.LeviTorus.sigma_invol hP.base.cm`. Establish `hc : ∀ a : AE F E, (cA σ).toRingHom ((cA σ).toRingHom a) = a` using `GlobalTheory.LeviTorus.cA_invol hσ`. Establish `hJ : ∀ i j, (cA σ).toRingHom (incM F W.J j i) = -incM F W.J i j`.

Introduce `i j`. Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, incM, Matrix.map_apply, GlobalTheory.LeviTorus.cA_incl, hP.skew.skew i j, map_neg]`. Establish `hXX : incV F H'.x ⬝ᵥ incM F W.J *ᵥ (fun i => (cA σ).toRingHom (incV F H'.x i)) = 0`. Rewrite using `[show (fun i => (cA σ).toRingHom (incV F H'.x i)) = fun i => cA σ (incV F H'.x i) from rfl, GlobalTheory.LeviTorus.form_incl, hA.xx, map_zero]`. Establish `hYY : incV F H'.y ⬝ᵥ incM F W.J *ᵥ (fun i => (cA σ).toRingHom (incV F H'.y i)) = 0`.

Rewrite using `[show (fun i => (cA σ).toRingHom (incV F H'.y i)) = fun i => cA σ (incV F H'.y i) from rfl, GlobalTheory.LeviTorus.form_incl, hA.yy, map_zero]`. Establish `hXY : incV F H'.x ⬝ᵥ incM F W.J *ᵥ (fun i => (cA σ).toRingHom (incV F H'.y i)) = 1`. Rewrite using `[show (fun i => (cA σ).toRingHom (incV F H'.y i)) = fun i => cA σ (incV F H'.y i) from rfl, GlobalTheory.LeviTorus.form_incl, hA.xy, map_one]`. Establish `hyx` using `GlobalTheory.LeviTorus.dot_yx hc hJ hXY`. Establish `hu : (incM F W.J *ᵥ fun i => (cA σ).toRingHom (incV F H'.y i)) ᵥ* incM F H'.ι = 0`.

Rewrite using `[show (fun i => (cA σ).toRingHom (incV F H'.y i)) = fun i => cA σ (incV F H'.y i) from rfl, GlobalTheory.LeviTorus.vecMul_incM]`. Use function extensionality and compare the values at `j`. Rewrite using `[(hA.orth _).2, map_zero]`. Both sides reduce to the same expression. Establish `hw : (incM F W.J *ᵥ fun i => (cA σ).toRingHom (incV F H'.x i)) ᵥ* incM F H'.ι = 0`.

Rewrite using `[show (fun i => (cA σ).toRingHom (incV F H'.x i)) = fun i => cA σ (incV F H'.x i) from rfl, GlobalTheory.LeviTorus.vecMul_incM]`. Use function extensionality and compare the values at `j`. Rewrite using `[(hA.orth _).1, map_zero]`. Both sides reduce to the same expression. Establish `hspan : ∀ k : Fin d, ∃ (a b : AE F E) (w : Fin d₁ → AE F E), (Pi.single k 1 : Fin d → AE F E) = a • incV F H'.x + b • incV F H'.y + incM F H'.ι *ᵥ w`.

Establish `key : ∀ z ∈ Submodule.span E (W.L : Set (Fin d → E)), ∃ (a b : AE F E) (w : Fin d₁ → AE F E), incV F z = a • incV F H'.x + b • incV F H'.y + incM F H'.ι *ᵥ w`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨s₀, t₀, u₀, -, -, -, rfl⟩` from `hA.split z hz`.

Use `⟨inclR (F := F) (AF F) s₀, inclR (F := F) (AF F) t₀, incV F u₀, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.DiagUnip.incV_add, GlobalTheory.DiagUnip.incV_add, GlobalTheory.DiagUnip.incV_smul, GlobalTheory.DiagUnip.incV_smul, GlobalTheory.DiagUnip.incV_mulVec]`. Normalize the expressions using the abelian group laws. Consider the case `zero => exact ⟨0, 0, 0, by simp [GlobalTheory.DiagUnip.incV_zero]⟩`. Consider the case `add z z' _ _ h h'`.

Take `⟨a, b, w, e⟩` from `h`. Take `⟨a', b', w', e'⟩` from `h'`. Use `⟨a + a', b + b', w + w', ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.DiagUnip.incV_add, e, e', Matrix.mulVec_add, add_smul, add_smul]`. Normalize the expressions using the abelian group laws.

Consider the case `smul e z _ h`. Take `⟨a, b, w, h⟩` from `h`. Use `⟨inclR (F := F) (AF F) e * a, inclR (F := F) (AF F) e * b, inclR (F := F) (AF F) e • w, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.DiagUnip.incV_smul, h, Matrix.mulVec_smul, smul_add, smul_add, smul_smul, smul_smul]`. Introduce `k`.

Establish `hk : Pi.single k (1 : E) ∈ Submodule.span E (W.L : Set (Fin d → E))`. Rewrite using `[hP.skew.lat.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Simplify `key _ hk` using `only [GlobalTheory.DiagUnip.incV_single]`. Establish `hm1 : mat m * incM F H'.ι = incM F H'.ι` using `by rw [hLι]; simp [mat]`.

Establish `hmul` using `GlobalTheory.DiagUnip.diag_eq (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) (incM F H'.ι) (mat m) t hXX hYY hXY hyx hu hw hLx hLy hm1 hspan`. Prove the components needed by the constructor for the conclusion. Simplify using `only [GlobalTheory.DblUnip.unipMat, diagCols]`. Rewrite using `[Matrix.fromBlocks_multiply]`. Use `erw [Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]`.

Simplify using `only [Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]`. Use `congr 1`. Rewrite using `[← hmul, Matrix.mul_add, Matrix.mul_one]`. Rewrite using `[GlobalTheory.DblUnip.diagMat, neg_smul]`. Normalize the expressions using the abelian group laws.

Rewrite using `[GlobalTheory.DiagUnip.diag_det _ _ _ _ _ hyx, map_sub, map_one]`. Simplify using the standard rewrite rules.
-/
theorem GlobalTheory.DiagUnip.diag_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ (t : (AE F E)ˣ) (m : UA σ W.J), IsLevi (W₁ := W₁) H' t 1 m →
      Matrix.fromBlocks (mat m) 0 0 1 * GlobalTheory.DblUnip.unipMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) ((↑t⁻¹ : AE F E) - 1) * diagCols (Fin d) = diagCols (Fin d) * GlobalTheory.DblUnip.diagMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) ((↑t⁻¹ : AE F E) - 1) ∧
      (GlobalTheory.DblUnip.diagMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) ((↑t⁻¹ : AE F E) - 1)).det = cA σ (↑t⁻¹ : AE F E) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ t m hL
  obtain ⟨hLx, hLy, hLι⟩ := hL
  have hσ := GlobalTheory.LeviTorus.sigma_invol hP.base.cm
  have hc : ∀ a : AE F E, (cA σ).toRingHom ((cA σ).toRingHom a) = a := GlobalTheory.LeviTorus.cA_invol hσ
  have hJ : ∀ i j, (cA σ).toRingHom (incM F W.J j i) = -incM F W.J i j := by
    intro i j
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, incM, Matrix.map_apply, GlobalTheory.LeviTorus.cA_incl, hP.skew.skew i j, map_neg]
  have hXX : incV F H'.x ⬝ᵥ incM F W.J *ᵥ (fun i => (cA σ).toRingHom (incV F H'.x i)) = 0 := by
    rw [show (fun i => (cA σ).toRingHom (incV F H'.x i)) = fun i => cA σ (incV F H'.x i) from rfl,
      GlobalTheory.LeviTorus.form_incl, hA.xx, map_zero]
  have hYY : incV F H'.y ⬝ᵥ incM F W.J *ᵥ (fun i => (cA σ).toRingHom (incV F H'.y i)) = 0 := by
    rw [show (fun i => (cA σ).toRingHom (incV F H'.y i)) = fun i => cA σ (incV F H'.y i) from rfl,
      GlobalTheory.LeviTorus.form_incl, hA.yy, map_zero]
  have hXY : incV F H'.x ⬝ᵥ incM F W.J *ᵥ (fun i => (cA σ).toRingHom (incV F H'.y i)) = 1 := by
    rw [show (fun i => (cA σ).toRingHom (incV F H'.y i)) = fun i => cA σ (incV F H'.y i) from rfl,
      GlobalTheory.LeviTorus.form_incl, hA.xy, map_one]
  have hyx := GlobalTheory.LeviTorus.dot_yx hc hJ hXY
  have hu : (incM F W.J *ᵥ fun i => (cA σ).toRingHom (incV F H'.y i)) ᵥ* incM F H'.ι = 0 := by
    rw [show (fun i => (cA σ).toRingHom (incV F H'.y i)) = fun i => cA σ (incV F H'.y i) from rfl,
      GlobalTheory.LeviTorus.vecMul_incM]
    funext j
    rw [(hA.orth _).2, map_zero]; rfl
  have hw : (incM F W.J *ᵥ fun i => (cA σ).toRingHom (incV F H'.x i)) ᵥ* incM F H'.ι = 0 := by
    rw [show (fun i => (cA σ).toRingHom (incV F H'.x i)) = fun i => cA σ (incV F H'.x i) from rfl,
      GlobalTheory.LeviTorus.vecMul_incM]
    funext j
    rw [(hA.orth _).1, map_zero]; rfl

  have hspan : ∀ k : Fin d, ∃ (a b : AE F E) (w : Fin d₁ → AE F E),
      (Pi.single k 1 : Fin d → AE F E) = a • incV F H'.x + b • incV F H'.y + incM F H'.ι *ᵥ w := by
    have key : ∀ z ∈ Submodule.span E (W.L : Set (Fin d → E)), ∃ (a b : AE F E) (w : Fin d₁ → AE F E),
        incV F z = a • incV F H'.x + b • incV F H'.y + incM F H'.ι *ᵥ w := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨s₀, t₀, u₀, -, -, -, rfl⟩ := hA.split z hz
        refine ⟨inclR (F := F) (AF F) s₀, inclR (F := F) (AF F) t₀, incV F u₀, ?_⟩
        rw [GlobalTheory.DiagUnip.incV_add, GlobalTheory.DiagUnip.incV_add, GlobalTheory.DiagUnip.incV_smul, GlobalTheory.DiagUnip.incV_smul,
          GlobalTheory.DiagUnip.incV_mulVec]
        abel
      | zero => exact ⟨0, 0, 0, by simp [GlobalTheory.DiagUnip.incV_zero]⟩
      | add z z' _ _ h h' =>
        obtain ⟨a, b, w, e⟩ := h
        obtain ⟨a', b', w', e'⟩ := h'
        refine ⟨a + a', b + b', w + w', ?_⟩
        rw [GlobalTheory.DiagUnip.incV_add, e, e', Matrix.mulVec_add, add_smul, add_smul]; abel
      | smul e z _ h =>
        obtain ⟨a, b, w, h⟩ := h
        refine ⟨inclR (F := F) (AF F) e * a, inclR (F := F) (AF F) e * b, inclR (F := F) (AF F) e • w, ?_⟩
        rw [GlobalTheory.DiagUnip.incV_smul, h, Matrix.mulVec_smul, smul_add, smul_add, smul_smul, smul_smul]
    intro k
    have hk : Pi.single k (1 : E) ∈ Submodule.span E (W.L : Set (Fin d → E)) := by
      rw [hP.skew.lat.span_eq_top]; trivial
    simpa only [GlobalTheory.DiagUnip.incV_single] using key _ hk

  have hm1 : mat m * incM F H'.ι = incM F H'.ι := by rw [hLι]; simp [mat]
  have hmul := GlobalTheory.DiagUnip.diag_eq (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) (incM F H'.ι) (mat m) t
    hXX hYY hXY hyx hu hw hLx hLy hm1 hspan
  constructor
  · simp only [GlobalTheory.DblUnip.unipMat, diagCols]
    rw [Matrix.fromBlocks_multiply]
    erw [Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    congr 1
    · rw [← hmul, Matrix.mul_add, Matrix.mul_one]
    · rw [GlobalTheory.DblUnip.diagMat, neg_smul]; abel
  · rw [GlobalTheory.DiagUnip.diag_det _ _ _ _ _ hyx, map_sub, map_one]
    simp
