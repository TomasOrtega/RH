import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSkewIdealCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchroedingerEigenvectorCompactCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEigenContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAIdeleUnitIntegralIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalUnitLevi

noncomputable section

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler GlobalTheory.LocIdeal
open GlobalTheory.Doubling (absE)
open Formalism.L2.Host (aboveF)
open scoped Classical
open scoped GlobalTheory.VacAny
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

namespace GlobalTheory.SuppOutQ

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Use `set w : Fin n → E := JX *ᵥ fun i => σ (y i) with hw`. Establish `hU : ∀ i, (∑ k, incM F JX i k * cA σ (incV F y k)) = incV F w i`. Introduce `i`. Simplify using `only [hw, incV, incM, Matrix.mulVec, dotProduct, Matrix.map_apply, GlobalTheory.SuppOut.cA_inclR, map_sum, map_mul]`. Establish `h1 : ∑ j, inclR (F` using `F) (AF F) (x j) * inclR (F := F) (AF F) (w j) = 1 := by`.

Establish `h` using `congrArg (inclR (F := F) (AF F)) hxy`. Rewrite `h` using `[map_one]`. Rewrite using `[← h, form, dotProduct, map_sum]`. Simplify using `only [map_mul, hw]`. Establish `hV : Matrix.vecMul (incV F w) (incM F (Matrix.vecMulVec x w)) = incV F w`.

Use extensionality with `k`. Simplify using `only [Matrix.vecMul, dotProduct, incV, incM, Matrix.map_apply, Matrix.vecMulVec_apply, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [h1, one_mul]`. Unfold `symp`. Rewrite using `[GlobalTheory.SuppOut.hTens_vecMulVec, GlobalTheory.SuppOut.hTens_vecMulVec]`. Use `congr 2`.

Repeatedly rewrite using `[← Finset.sum_mul, hU]`. Express the relevant statement in the definitionally equal form `incV F w ⬝ᵥ _ = incV F w ⬝ᵥ _`. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hV]`.
-/
theorem symp_projL (σ : E →ₐ[F] E) {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (x y : Fin n → E) (hxy : form σ JX x y = 1) (ξ : AE F E) (q : Fin d → AE F E)
    (γ : Matrix (Fin n) (Fin d) (AE F E)) :
    symp (R := AF F) (cA σ) ξ (incM F JX) (incM F JW)
        (incM F (Matrix.vecMulVec x (JX *ᵥ fun i => σ (y i))) * γ) (Matrix.vecMulVec (incV F y) q) =
      symp (R := AF F) (cA σ) ξ (incM F JX) (incM F JW) γ (Matrix.vecMulVec (incV F y) q) := by
  set w : Fin n → E := JX *ᵥ fun i => σ (y i) with hw
  have hU : ∀ i, (∑ k, incM F JX i k * cA σ (incV F y k)) = incV F w i := by
    intro i
    simp only [hw, incV, incM, Matrix.mulVec, dotProduct, Matrix.map_apply, GlobalTheory.SuppOut.cA_inclR, map_sum, map_mul]
  have h1 : ∑ j, inclR (F := F) (AF F) (x j) * inclR (F := F) (AF F) (w j) = 1 := by
    have h := congrArg (inclR (F := F) (AF F)) hxy
    rw [map_one] at h
    rw [← h, form, dotProduct, map_sum]; simp only [map_mul, hw]
  have hV : Matrix.vecMul (incV F w) (incM F (Matrix.vecMulVec x w)) = incV F w := by
    ext k
    simp only [Matrix.vecMul, dotProduct, incV, incM, Matrix.map_apply, Matrix.vecMulVec_apply, map_mul]
    calc (∑ i, inclR (F := F) (AF F) (w i) * (inclR (F := F) (AF F) (x i) * inclR (F := F) (AF F) (w k)))
        = (∑ i, inclR (F := F) (AF F) (x i) * inclR (F := F) (AF F) (w i)) * inclR (F := F) (AF F) (w k) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_; ring
      _ = _ := by rw [h1, one_mul]
  unfold symp
  rw [GlobalTheory.SuppOut.hTens_vecMulVec, GlobalTheory.SuppOut.hTens_vecMulVec]
  congr 2
  simp_rw [← Finset.sum_mul, hU]
  change incV F w ⬝ᵥ _ = incV F w ⬝ᵥ _
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hV]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [incM, incV, Matrix.mul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Finset.mul_sum, map_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vecMulVec_mul {n d : ℕ} (x w : Fin n → E) (γ : Matrix (Fin n) (Fin d) (AE F E)) :
    incM F (Matrix.vecMulVec x w) * γ = Matrix.vecMulVec (incV F x) (Matrix.vecMul (incV F w) γ) := by
  ext i j
  simp only [incM, incV, Matrix.mul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct,
    Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.SuppOutQ

namespace GlobalTheory.SuppOutQ

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_swap_herm {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (a b : Fin n → E) : form σ J a b = σ (form σ J b a) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Proceed by induction on `hγ using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, hav, x, hx, y, hy, rfl⟩` from `hz`. Use `AddSubgroup.subset_closure ⟨a, ha, hav, form σ X.J x H.y • H.x, (GlobalTheory.SuppOut.form_mem_ideal σ B hH hx).1, y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_smul, incM, incM, incM, ← Matrix.map_mul]`.

Use `congr 2`. Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, form, dotProduct]`. Rewrite using `[Finset.sum_mul, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => rw [Matrix.mul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [Matrix.mul_add]`. Conclude with `add_mem hx hy`.

Consider the case `neg x _ hx => rw [Matrix.mul_neg]`. Conclude with `neg_mem hx`.
-/
theorem proj_memL [NumberField E] (σ : E →ₐ[F] E) (B : Base F E) {n n₁ d : ℕ} (X : Spc F E n) (X₁ : Spc F E n₁)
    (W : Spc F E d) (H : Plane E n n₁) (i₀ i₁ : ℕ) (hH : Plane.IsAdapted σ B H X X₁ i₀ i₁) (v : Pl F)
    (γ : Matrix (Fin n) (Fin d) (AE F E)) (hγ : γ ∈ latAtV X W v) :
    incM F (Matrix.vecMulVec H.x (X.J *ᵥ fun i => σ (H.y i))) * γ ∈ latAtV X W v := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, x, hx, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hav, form σ X.J x H.y • H.x,
      (GlobalTheory.SuppOut.form_mem_ideal σ B hH hx).1, y, hy, ?_⟩
    rw [Matrix.mul_smul, incM, incM, incM, ← Matrix.map_mul]
    congr 2
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, form, dotProduct]
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, hav, x, hx, y, hy, rfl⟩` from `hz`. Establish `hform : ∀ {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (x y : Fin m → E), inclR (F` using `F) (AF F) (σ (form σ J x y)) = ∑ i, inclR (F := F) (AF F) (σ (x i)) * incV F (fun k => σ ((J *ᵥ fun k => σ (y k)) k)) i := by`. Introduce `m J x y`.

Simplify using `only [form, dotProduct, map_sum, map_mul, incV]`. Establish `he : (∑ i, ∑ j, cA σ ((a • incM F (Matrix.vecMulVec x y)) i j) * incV F (fun k => σ ((X.J *ᵥ fun k => σ (u k)) k)) i * incV F (fun k => σ ((W.J *ᵥ fun k => σ (w k)) k)) j) = a ⊗ₜ[F] (σ (form σ X.J x u) * σ (form σ W.J y w))`. Establish `h1 : a ⊗ₜ[F] (σ (form σ X.J x u) * σ (form σ W.J y w)) = a • (inclR (F` using `F) (AF F) (σ (form σ X.J x u)) * inclR (F := F) (AF F) (σ (form σ W.J y w))) := by`. Rewrite using `[← map_mul (inclR (F := F) (AF F))]`. Express the relevant statement in the definitionally equal form `a ⊗ₜ[F] _ = a • ((1 : AF F) ⊗ₜ[F] (σ (form σ X.J x u) * σ (form σ W.J y w)) : AF F ⊗[F] E)`.

Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[h1, hform, hform, Finset.sum_mul_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [incM, incV, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, map_mul, map_smul, GlobalTheory.SuppOut.cA_inclR, smul_mul_assoc, Algebra.smul_def, AlgHom.commutes]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he]`. Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) (a ⊗ₜ[F] (σ (form σ X.J x u) * σ (form σ W.J y w)) : AF F ⊗[F] E) ∈ _`. Rewrite using `[Algebra.TensorProduct.map_tmul]`.

Conclude with `AddSubgroup.subset_closure ⟨_, hav, _, FractionalIdeal.mul_mem_mul (hI₁ x hx) (hI₂ y hy), rfl⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Simplify using `only [Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib]`. Conclude with `add_mem hx hy`.

Consider the case `neg x _ hx`. Simplify using `only [Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]`. Conclude with `neg_mem hx`.
-/
theorem coefR [NumberField E] (σ : E →ₐ[F] E) {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (u : Fin n → E)
    (w : Fin d → E) (I₁ I₂ : FractionalIdeal (𝓞 E)⁰ E) (hI₁ : ∀ y ∈ X.L, σ (form σ X.J y u) ∈ I₁)
    (hI₂ : ∀ y ∈ W.L, σ (form σ W.J y w) ∈ I₂) (v : Pl F) (z : Matrix (Fin n) (Fin d) (AE F E))
    (hz : z ∈ latAtV X W v) :
    compFin F E v (∑ i, ∑ j, cA σ (z i j) * incV F (fun k => σ ((X.J *ᵥ fun k => σ (u k)) k)) i *
      incV F (fun k => σ ((W.J *ᵥ fun k => σ (w k)) k)) j) ∈ locId v (I₁ * I₂) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, x, hx, y, hy, rfl⟩ := hz
    have hform : ∀ {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (x y : Fin m → E),
        inclR (F := F) (AF F) (σ (form σ J x y)) =
          ∑ i, inclR (F := F) (AF F) (σ (x i)) * incV F (fun k => σ ((J *ᵥ fun k => σ (y k)) k)) i := by
      intro m J x y
      simp only [form, dotProduct, map_sum, map_mul, incV]
    have he : (∑ i, ∑ j, cA σ ((a • incM F (Matrix.vecMulVec x y)) i j) *
        incV F (fun k => σ ((X.J *ᵥ fun k => σ (u k)) k)) i * incV F (fun k => σ ((W.J *ᵥ fun k => σ (w k)) k)) j) =
        a ⊗ₜ[F] (σ (form σ X.J x u) * σ (form σ W.J y w)) := by
      have h1 : a ⊗ₜ[F] (σ (form σ X.J x u) * σ (form σ W.J y w)) =
          a • (inclR (F := F) (AF F) (σ (form σ X.J x u)) * inclR (F := F) (AF F) (σ (form σ W.J y w))) := by
        rw [← map_mul (inclR (F := F) (AF F))]
        change a ⊗ₜ[F] _ = a • ((1 : AF F) ⊗ₜ[F] (σ (form σ X.J x u) * σ (form σ W.J y w)) : AF F ⊗[F] E)
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, hform, hform, Finset.sum_mul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [incM, incV, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, map_mul, map_smul,
        GlobalTheory.SuppOut.cA_inclR, smul_mul_assoc, Algebra.smul_def, AlgHom.commutes]
      ring
    rw [he]
    change Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E)
      (a ⊗ₜ[F] (σ (form σ X.J x u) * σ (form σ W.J y w)) : AF F ⊗[F] E) ∈ _
    rw [Algebra.TensorProduct.map_tmul]
    exact AddSubgroup.subset_closure ⟨_, hav, _, FractionalIdeal.mul_mem_mul (hI₁ x hx) (hI₂ y hy), rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib]
    exact add_mem hx hy
  | neg x _ hx =>
    simp only [Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
    exact neg_mem hx

end GlobalTheory.SuppOutQ

namespace GlobalTheory.SuppOutQ

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Establish `hform : ∀ {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (x y : Fin m → E), inclR (F` using `F) (AF F) (σ (form σ J x y)) = ∑ i, inclR (F := F) (AF F) (σ (x i)) * incV F (fun k => σ ((J *ᵥ fun k => σ (y k)) k)) i := by`. Introduce `m J x y`. Simplify using `only [form, dotProduct, map_sum, map_mul, incV]`. Rewrite using `[hform, hform, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, map_smul, map_mul, hcc, incV, GlobalTheory.SuppOut.cA_inclR, Algebra.smul_def, AlgHom.commutes]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem read_shift (σ : E →ₐ[F] E) (hcc : ∀ z : AE F E, cA σ (cA σ z) = z) {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E)
    (JW : Matrix (Fin d) (Fin d) E) (y u : Fin n → E) (x' w : Fin d → E) (e : AF F) (l : AE F E) :
    (∑ i, ∑ j, cA σ ((e • (cA σ l • Matrix.vecMulVec (incV F y) (incV F x'))) i j) *
      incV F (fun k => σ ((JX *ᵥ fun k => σ (u k)) k)) i * incV F (fun k => σ ((JW *ᵥ fun k => σ (w k)) k)) j) =
      e • l * inclR (F := F) (AF F) (σ (form σ JX y u)) * inclR (F := F) (AF F) (σ (form σ JW x' w)) := by
  have hform : ∀ {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (x y : Fin m → E),
      inclR (F := F) (AF F) (σ (form σ J x y)) =
        ∑ i, inclR (F := F) (AF F) (σ (x i)) * incV F (fun k => σ ((J *ᵥ fun k => σ (y k)) k)) i := by
    intro m J x y
    simp only [form, dotProduct, map_sum, map_mul, incV]
  rw [hform, hform, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, map_smul, map_mul, hcc, incV,
    GlobalTheory.SuppOut.cA_inclR, Algebra.smul_def, AlgHom.commutes]
  ring

end GlobalTheory.SuppOutQ

namespace GlobalTheory.SuppOutQ

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a b G G₁ H H' hB hG hC v l _hl hnot`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Establish `hσ : ∀ x : E, σ (σ x) = x` using `GlobalTheory.VacShift.sigma_invol hB.cm`. Establish `hcc : ∀ z, cA σ (cA σ z) = z` using `fun z => by`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => simp [cA, hσ]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Establish `hsq : shiftB σ H H' l = Matrix.vecMulVec (incV F H.y) (cA σ l.1 • incV F H'.x)`.

Use extensionality with `i j`. Simplify using `only [shiftB, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `set e : AF F := GlobalTheory.LatVac.liftV v 1 with he`. Establish `heat : At (evFin F v) e` using `GlobalTheory.LatVac.at_liftV v 1`.

Establish `hev : evFin F v e = 1` using `GlobalTheory.LatVac.evFin_liftV v 1`. Establish `hsat : At (evFin F v) (e • (shiftB σ H H' l))` using `fun u hu => by`. Rewrite using `[smul_smul, ← smul_eq_mul u e, heat u hu, zero_smul]`. Establish `hsv : e • (shiftB σ H H' l) ∈ latAtV G.V' G.W v`. Rewrite using `[GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B _ _ G.V' G.W _ _ _ _ hB hG.hV' hG.hW v _ hsat]`.

Introduce `γ hγ`. Establish `hγ'L` using `proj_memL σ B G.V' G₁.V' G.W H 0 (b + 1) hC.hH v γ hγ`. Establish `hγ'at` using `(GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1 _ hγ'L`. Establish `h1` using `hall _ hγ'at ⟨_, vecMulVec_mul _ _ γ⟩ hγ'L`. Establish `h2 : symp (R` using `AF F) (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) (e • (shiftB σ H H' l)) γ = -(e * symp (R := AF F) (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) (incM F (Matrix.vecMulVec H.x (G.V'.J *ᵥ fun i => σ (H.y i))) * γ) (shiftB σ H H' l)) := by`.

Use `GlobalTheory.LatVac.symp_smul_smul σ (incM F G.V'.J) (incM F G.W.J) (-1) e 1 (shiftB σ H H' l) γ` as an intermediate fact. Rewrite `this` using `[one_smul, mul_one]`. Rewrite using `[this, GlobalTheory.SuppOut.symp_antisymm σ hσ G.V'.J G.W.J hG.hV'.herm hG.hW.skew (shiftB σ H H' l) γ, hsq, symp_projL σ G.V'.J G.W.J H.x H.y hC.hH.xy]`. Expand and normalize the polynomial expressions, which then agree. Establish `hat2 : At (evFin F v) (e * symp (R` using `AF F) (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) (incM F (Matrix.vecMulVec H.x (G.V'.J *ᵥ fun i => σ (H.y i))) * γ) (shiftB σ H H' l)) := fun u hu => by`.

Rewrite using `[smul_eq_mul, ← mul_assoc, ← smul_eq_mul u e, heat u hu, zero_mul]`. Rewrite using `[h2, AddChar.map_neg_eq_inv, GlobalTheory.VacIndic.psi_of_at _ hat2, map_mul, hev, one_mul]`. Rewrite using `[← GlobalTheory.LatVac.psiAt_apply, h1, inv_one]`. Establish `h𝔟 : H.𝔟 ≠ 0` using `(GlobalTheory.T.adapted_plane_hermitian_ideal_coprime F E σ B H G.V' G₁.V' 0 (b + 1) _ _ hB hG.hV' hC.hH (by omega) (by omega)).1`. Establish `hI₁ : ∀ z ∈ G.V'.L, σ (form σ G.V'.J z H.x) ∈ H.𝔟⁻¹`.

Introduce `z hz`. Rewrite using `[FractionalIdeal.mem_inv_iff h𝔟]`. Introduce `t ht`. Establish `htx : t • H.x ∈ G.V'.L` using `(hC.hH.ideal t).1 ht`. Establish `hint` using `(hG.hV'.dual (t • H.x)).1 htx z hz`.

Establish `e1 : form σ G.V'.J (t • H.x) z = σ (form σ G.V'.J z H.x) * t`. Rewrite using `[GlobalTheory.VacShift.form_smul_left, form_swap_herm hσ _ hG.hV'.herm H.x z]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hint` using `[e1]`. Conclude with `(FractionalIdeal.mem_one_iff _).2 ⟨⟨_, hint⟩, rfl⟩`.

Establish `hI₂ : ∀ z ∈ G.W.L, σ (form σ G.W.J z H'.y) ∈ conjI σ H'.𝔟` using `fun z hz => GlobalTheory.VacShift.mem_conjI σ (GlobalTheory.SuppOut.form_mem_ideal σ B hC.hH' hz).2`. Establish `hc` using `coefR σ G.V' G.W H.x H'.y _ _ hI₁ hI₂ v _ hsv`. Establish `hf1 : σ (form σ G.V'.J H.y H.x) = 1`. Rewrite using `[form_swap_herm hσ _ hG.hV'.herm H.y H.x, hσ, hC.hH.xy]`. Establish `hf2 : σ (form σ G.W.J H'.x H'.y) = 1` using `by rw [hC.hH'.xy, map_one]`.

Unfold `shiftB at hc`. Rewrite `hc` using `[read_shift σ hcc G.V'.J G.W.J H.y H.x H'.x H'.y e (l : AE F E), hf1, hf2, map_one, mul_one, mul_one]`. Establish `hce : compFin F E v (e • (l : AE F E)) = compFin F E v (l : AE F E)`. Rewrite using `[Algebra.smul_def, map_mul]`. Establish `: compFin F E v (algebraMap (AF F) (AE F E) e) = 1`.

Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) (e ⊗ₜ[F] (1 : E)) = 1`. Rewrite using `[Algebra.TensorProduct.map_tmul, hev]`. Both sides reduce to the same expression. Rewrite using `[this, one_mul]`. Rewrite `hc` using `[hce]`.

Conclude with `hnot hc`.
-/
theorem exists_lat_pair_ne_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {a b : ℕ} (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), B.IsGood σ → G.IsGood B → CfgB B G G₁ H H' →
    ∀ (v : Pl F) (l : (AE F E)ˣ), l ∈ idelesAt E (evFin F v) →
      compFin F E v (l : AE F E) ∉ locId v (H.𝔟⁻¹ * conjI σ H'.𝔟) →
      ∃ γ : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (AE F E), At (evFin F v) γ ∧
        (∃ z, γ = Matrix.vecMulVec (incV F H.x) z) ∧ γ ∈ latAtV G.V' G.W v ∧
        GlobalTheory.LatVac.psiAt B.ψ v (evFin F v (symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) γ (shiftB σ H H' l))) ≠ 1 := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hB hG hC v l _hl hnot
  by_contra hall
  push_neg at hall
  have hσ : ∀ x : E, σ (σ x) = x := GlobalTheory.VacShift.sigma_invol hB.cm
  have hcc : ∀ z, cA σ (cA σ z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [cA, hσ]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hsq : shiftB σ H H' l = Matrix.vecMulVec (incV F H.y) (cA σ l.1 • incV F H'.x) := by
    ext i j
    simp only [shiftB, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    ring
  set e : AF F := GlobalTheory.LatVac.liftV v 1 with he
  have heat : At (evFin F v) e := GlobalTheory.LatVac.at_liftV v 1
  have hev : evFin F v e = 1 := GlobalTheory.LatVac.evFin_liftV v 1
  have hsat : At (evFin F v) (e • (shiftB σ H H' l)) := fun u hu => by
    rw [smul_smul, ← smul_eq_mul u e, heat u hu, zero_smul]
  have hsv : e • (shiftB σ H H' l) ∈ latAtV G.V' G.W v := by
    rw [GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B _ _ G.V' G.W _ _ _ _ hB hG.hV' hG.hW v _ hsat]
    intro γ hγ
    have hγ'L := proj_memL σ B G.V' G₁.V' G.W H 0 (b + 1) hC.hH v γ hγ
    have hγ'at := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1 _ hγ'L
    have h1 := hall _ hγ'at ⟨_, vecMulVec_mul _ _ γ⟩ hγ'L
    have h2 : symp (R := AF F) (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) (e • (shiftB σ H H' l)) γ =
        -(e * symp (R := AF F) (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J)
          (incM F (Matrix.vecMulVec H.x (G.V'.J *ᵥ fun i => σ (H.y i))) * γ) (shiftB σ H H' l)) := by
      have := GlobalTheory.LatVac.symp_smul_smul σ (incM F G.V'.J) (incM F G.W.J) (-1) e 1 (shiftB σ H H' l) γ
      rw [one_smul, mul_one] at this
      rw [this, GlobalTheory.SuppOut.symp_antisymm σ hσ G.V'.J G.W.J hG.hV'.herm hG.hW.skew (shiftB σ H H' l) γ, hsq,
        symp_projL σ G.V'.J G.W.J H.x H.y hC.hH.xy]
      ring
    have hat2 : At (evFin F v) (e * symp (R := AF F) (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J)
        (incM F (Matrix.vecMulVec H.x (G.V'.J *ᵥ fun i => σ (H.y i))) * γ) (shiftB σ H H' l)) :=
      fun u hu => by
        rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u e, heat u hu, zero_mul]
    rw [h2, AddChar.map_neg_eq_inv, GlobalTheory.VacIndic.psi_of_at _ hat2, map_mul, hev, one_mul]
    rw [← GlobalTheory.LatVac.psiAt_apply, h1, inv_one]
  have h𝔟 : H.𝔟 ≠ 0 := (GlobalTheory.T.adapted_plane_hermitian_ideal_coprime F E σ B H G.V' G₁.V' 0 (b + 1) _ _ hB hG.hV' hC.hH (by omega) (by omega)).1
  have hI₁ : ∀ z ∈ G.V'.L, σ (form σ G.V'.J z H.x) ∈ H.𝔟⁻¹ := by
    intro z hz
    rw [FractionalIdeal.mem_inv_iff h𝔟]
    intro t ht
    have htx : t • H.x ∈ G.V'.L := (hC.hH.ideal t).1 ht
    have hint := (hG.hV'.dual (t • H.x)).1 htx z hz
    have e1 : form σ G.V'.J (t • H.x) z = σ (form σ G.V'.J z H.x) * t := by
      rw [GlobalTheory.VacShift.form_smul_left, form_swap_herm hσ _ hG.hV'.herm H.x z]
      ring
    rw [e1] at hint
    exact (FractionalIdeal.mem_one_iff _).2 ⟨⟨_, hint⟩, rfl⟩
  have hI₂ : ∀ z ∈ G.W.L, σ (form σ G.W.J z H'.y) ∈ conjI σ H'.𝔟 := fun z hz =>
    GlobalTheory.VacShift.mem_conjI σ (GlobalTheory.SuppOut.form_mem_ideal σ B hC.hH' hz).2
  have hc := coefR σ G.V' G.W H.x H'.y _ _ hI₁ hI₂ v _ hsv
  have hf1 : σ (form σ G.V'.J H.y H.x) = 1 := by
    rw [form_swap_herm hσ _ hG.hV'.herm H.y H.x, hσ, hC.hH.xy]
  have hf2 : σ (form σ G.W.J H'.x H'.y) = 1 := by rw [hC.hH'.xy, map_one]
  unfold shiftB at hc
  rw [read_shift σ hcc G.V'.J G.W.J H.y H.x H'.x H'.y e (l : AE F E), hf1, hf2, map_one, mul_one, mul_one] at hc
  have hce : compFin F E v (e • (l : AE F E)) = compFin F E v (l : AE F E) := by
    rw [Algebra.smul_def, map_mul]
    have : compFin F E v (algebraMap (AF F) (AE F E) e) = 1 := by
      change Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) (e ⊗ₜ[F] (1 : E)) = 1
      rw [Algebra.TensorProduct.map_tmul, hev]; rfl
    rw [this, one_mul]
  rw [hce] at hc
  exact hnot hc

end GlobalTheory.SuppOutQ
