import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.HeisLineF

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Simplify using `[cAF, incAF, sigR, inclR]`.
-/
theorem cAF_incAF (σ : E →ₐ[F] E) (x : E) : cAF σ (incAF F E x) = incAF F E (σ x) := by
  simp [cAF, incAF, sigR, inclR]

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r e => simp [cAF, sigR, hσ]`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`.
-/
theorem cAF_cAF (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (a : AEF F E) : cAF σ (cAF σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cAF, sigR, hσ]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/- English proof (translation)
Set `f : AEF F E →ₐ[AF F] AEF F E` to `Algebra.TensorProduct.map (AlgHom.id _ _) σ`. Establish `hf : ∀ a, f a = cAF σ a`. Introduce `a`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul r e => simp [f, cAF, sigR]`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`. Establish `hff : f.comp f = AlgHom.id _ _` using `AlgHom.ext fun a => by`. Rewrite using `[AlgHom.comp_apply, hf, hf, cAF_cAF σ hσ]`. Both sides reduce to the same expression.

Set `g : AEF F E ≃ₐ[AF F] AEF F E` to `AlgEquiv.ofAlgHom f f hff hff`. Rewrite using `[← hf]`. Conclude with `Algebra.trace_eq_of_algEquiv g a`.
-/
theorem trace_cAF (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (a : AEF F E) :
    Algebra.trace (AF F) (AEF F E) (cAF σ a) = Algebra.trace (AF F) (AEF F E) a := by
  let f : AEF F E →ₐ[AF F] AEF F E := Algebra.TensorProduct.map (AlgHom.id _ _) σ
  have hf : ∀ a, f a = cAF σ a := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [f, cAF, sigR]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  have hff : f.comp f = AlgHom.id _ _ := AlgHom.ext fun a => by
    rw [AlgHom.comp_apply, hf, hf, cAF_cAF σ hσ]; rfl
  let g : AEF F E ≃ₐ[AF F] AEF F E := AlgEquiv.ofAlgHom f f hff hff
  rw [← hf]
  exact Algebra.trace_eq_of_algEquiv g a

/- English proof (translation)
Simplify using `only [map_sum, map_mul, hσ, hP, hQ]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem herm_sum {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (P : Fin m → Fin m → A)
    (Q : Fin n → Fin n → A) (hP : ∀ i k, σ (P i k) = P k i) (hQ : ∀ i k, σ (Q i k) = Q k i)
    (x y : Matrix (Fin n) (Fin m) A) :
    σ (∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a) =
      ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (x c b) * Q c d * y d a := by
  simp only [map_sum, map_mul, hσ, hP, hQ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Establish `hu : IsUnit J.det` using `isUnit_iff_ne_zero.mpr hJ.2`. Establish `hT : Jᵀ = J.map σ`. Use extensionality with `i j`. Simplify using `[Matrix.transpose_apply, hJ.1 j i]`. Establish `h1 : J⁻¹.map σ * Jᵀ = 1`.

Rewrite using `[hT, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu]`. Simplify using the standard rewrite rules. Establish `h2 : (Jᵀ)⁻¹ = J⁻¹.map σ` using `Matrix.inv_eq_left_inv h1`. Rewrite `h2` using `[← Matrix.transpose_nonsing_inv]`. Use `congrFun (congrFun h2 i) k` as an intermediate fact.

Simplify `this.symm` using `[Matrix.transpose_apply]`.
-/
theorem inv_herm (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) (i k : Fin n) :
    σ (J⁻¹ i k) = J⁻¹ k i := by
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
  have hT : Jᵀ = J.map σ := by
    ext i j
    simp [Matrix.transpose_apply, hJ.1 j i]
  have h1 : J⁻¹.map σ * Jᵀ = 1 := by
    rw [hT, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu]
    simp
  have h2 : (Jᵀ)⁻¹ = J⁻¹.map σ := Matrix.inv_eq_left_inv h1
  rw [← Matrix.transpose_nonsing_inv] at h2
  have := congrFun (congrFun h2 i) k
  simpa [Matrix.transpose_apply] using this.symm

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)

/- English proof (translation)
The claim follows from `herm_sum (cAF σ) (cAF_cAF σ hσ) (fun i k => incAF F E (JS⁻¹ i k)) (fun i k => incAF F E (JT i k)) (fun i k => by rw [cAF_incAF, inv_herm σ hS]) (fun i k => by rw [cAF_incAF, hT.1 k i]) x y`.
-/
theorem hOF_herm (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (x y : WOF F E nS nT) :
    cAF σ (hOF σ JS JT x y) = hOF σ JS JT y x :=
  herm_sum (cAF σ) (cAF_cAF σ hσ) (fun i k => incAF F E (JS⁻¹ i k)) (fun i k => incAF F E (JT i k))
    (fun i k => by rw [cAF_incAF, inv_herm σ hS]) (fun i k => by rw [cAF_incAF, hT.1 k i]) x y

/- English proof (translation)
Unfold `symplOF`. Rewrite using `[← trace_cAF σ hσ (incAF F E ξ₀ * hOF σ JS JT x y), map_mul (cAF σ), cAF_incAF, hξ, hOF_herm σ JS JT hσ hS hT, map_neg, neg_mul, map_neg, neg_neg]`.
-/
theorem symplOF_skew (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (ξ₀ : E) (hξ : σ ξ₀ = -ξ₀)
    (x y : WOF F E nS nT) : symplOF σ JS JT ξ₀ y x = -symplOF σ JS JT ξ₀ x y := by
  unfold symplOF
  rw [← trace_cAF σ hσ (incAF F E ξ₀ * hOF σ JS JT x y), map_mul (cAF σ), cAF_incAF, hξ, hOF_herm σ JS JT hσ hS hT,
    map_neg, neg_mul, map_neg, neg_neg]

/- English proof (translation)
Unfold `symplOF hOF`. Simplify using `only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]`.
-/
theorem symplOF_add_left (ξ₀ : E) (x x' y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ (x + x') y = symplOF σ JS JT ξ₀ x y + symplOF σ JS JT ξ₀ x' y := by
  unfold symplOF hOF
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]

/- English proof (translation)
Unfold `symplOF hOF`. Simplify using `only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add]`.
-/
theorem symplOF_add_right (ξ₀ : E) (x y y' : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ x (y + y') = symplOF σ JS JT ξ₀ x y + symplOF σ JS JT ξ₀ x y' := by
  unfold symplOF hOF
  simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add]

/- English proof (translation)
Unfold `symplOHF`. Rewrite using `[symplOF_add_left, mul_add]`.
-/
theorem symplOHF_add_left (ξ₀ : E) (x x' y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ (x + x') y = symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x' y := by
  unfold symplOHF; rw [symplOF_add_left, mul_add]

/- English proof (translation)
Unfold `symplOHF`. Rewrite using `[symplOF_add_right, mul_add]`.
-/
theorem symplOHF_add_right (ξ₀ : E) (x y y' : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ x (y + y') = symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x y' := by
  unfold symplOHF; rw [symplOF_add_right, mul_add]

/- English proof (translation)
Use `symplOF_add_right σ JS JT ξ₀ x 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_add.mp this`.
-/
theorem symplOF_zero_right (ξ₀ : E) (x : WOF F E nS nT) : symplOF σ JS JT ξ₀ x 0 = 0 := by
  have := symplOF_add_right σ JS JT ξ₀ x 0 0
  rw [add_zero] at this
  exact left_eq_add.mp this

/- English proof (translation)
Establish `h` using `symplOF_skew σ JS JT hσ hS hT ξ₀ hξ x x`. Establish `h2 : (2 : AF F) * symplOF σ JS JT ξ₀ x x = 0`. Rewrite using `[two_mul]`. Use `nth_rewrite 1 [h]`. Conclude with `neg_add_cancel _`.

Establish `hu : IsUnit (2 : AF F)`. Establish `: (2 : AF F) = algebraMap F (AF F) 2` using `(map_ofNat _ 2).symm`. Rewrite using `[this]`. Conclude with `(isUnit_iff_ne_zero.mpr two_ne_zero).map _`. Conclude with `hu.mul_right_eq_zero.mp h2`.
-/
theorem symplOF_self (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (ξ₀ : E) (hξ : σ ξ₀ = -ξ₀)
    (x : WOF F E nS nT) : symplOF σ JS JT ξ₀ x x = 0 := by
  have h := symplOF_skew σ JS JT hσ hS hT ξ₀ hξ x x
  have h2 : (2 : AF F) * symplOF σ JS JT ξ₀ x x = 0 := by
    rw [two_mul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  have hu : IsUnit (2 : AF F) := by
    have : (2 : AF F) = algebraMap F (AF F) 2 := (map_ofNat _ 2).symm
    rw [this]
    exact (isUnit_iff_ne_zero.mpr two_ne_zero).map _
  exact hu.mul_right_eq_zero.mp h2

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (AEF F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Establish `ht : Continuous (Algebra.trace (AF F) (AEF F E))` using `IsModuleTopology.continuous_of_linearMap _`. Use `ht.comp (continuous_const.mul ?_)` and prove the remaining obligations.

Unfold `hOF`. Conclude with `continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => continuous_finset_sum _ fun c _ => continuous_finset_sum _ fun d _ => continuous_const.mul (continuous_id.matrix_elem d a)`.
-/
theorem continuous_symplOF_left (ξ₀ : E) (y : WOF F E nS nT) :
    Continuous fun x : WOF F E nS nT => symplOF σ JS JT ξ₀ x y := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AEF F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have ht : Continuous (Algebra.trace (AF F) (AEF F E)) := IsModuleTopology.continuous_of_linearMap _
  refine ht.comp (continuous_const.mul ?_)
  unfold hOF
  exact continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => continuous_finset_sum _ fun c _ =>
    continuous_finset_sum _ fun d _ => continuous_const.mul (continuous_id.matrix_elem d a)

omit [Algebra F E] [Field E] [NumberField E] in
/- English proof (translation)
Use `haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Establish `hq : ∀ r : ℚ, g ((r : ℝ) * t) = 0`. Introduce `r`. Establish `hden : (r.den : ℝ) * ((r : ℝ) * t) = (r.num : ℝ) * t`. Rewrite using `[← mul_assoc]`.

Use `congr 1`. Use `congrArg (Rat.cast : ℚ → ℝ) (Rat.den_mul_eq_num r)` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Establish `h1 : r.den • g ((r : ℝ) * t) = 0`.

Rewrite using `[← map_nsmul, nsmul_eq_mul, hden, ← zsmul_eq_mul, map_zsmul, ht, smul_zero]`. Establish `hu : IsUnit ((r.den : ℕ) : AF F)`. Establish `: ((r.den : ℕ) : AF F) = algebraMap F (AF F) (r.den : F)` using `(map_natCast _ _).symm`. Rewrite using `[this]`. Conclude with `(isUnit_iff_ne_zero.mpr (by exact_mod_cast r.den_nz)).map _`.

Rewrite `h1` using `[nsmul_eq_mul]`. Conclude with `hu.mul_right_eq_zero.mp h1`. Establish `: (fun u : ℝ => g (u * t)) = fun _ => 0` using `Rat.denseRange_cast.equalizer (hg.comp (continuous_id.mul continuous_const)) continuous_const (funext hq)`. Conclude with `congrFun this u`.
-/
theorem line_zero (g : ℝ →+ AF F) (hg : Continuous g) (t : ℝ) (ht : g t = 0) (u : ℝ) : g (u * t) = 0 := by
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have hq : ∀ r : ℚ, g ((r : ℝ) * t) = 0 := by
    intro r
    have hden : (r.den : ℝ) * ((r : ℝ) * t) = (r.num : ℝ) * t := by
      rw [← mul_assoc]
      congr 1
      have := congrArg (Rat.cast : ℚ → ℝ) (Rat.den_mul_eq_num r)
      push_cast at this
      exact this
    have h1 : r.den • g ((r : ℝ) * t) = 0 := by
      rw [← map_nsmul, nsmul_eq_mul, hden, ← zsmul_eq_mul, map_zsmul, ht, smul_zero]
    have hu : IsUnit ((r.den : ℕ) : AF F) := by
      have : ((r.den : ℕ) : AF F) = algebraMap F (AF F) (r.den : F) := (map_natCast _ _).symm
      rw [this]
      exact (isUnit_iff_ne_zero.mpr (by exact_mod_cast r.den_nz)).map _
    rw [nsmul_eq_mul] at h1
    exact hu.mul_right_eq_zero.mp h1
  have : (fun u : ℝ => g (u * t)) = fun _ => 0 :=
    Rat.denseRange_cast.equalizer (hg.comp (continuous_id.mul continuous_const)) continuous_const (funext hq)
  exact congrFun this u

end GlobalTheory.HeisLineF

open GlobalTheory.HeisLineF in
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ _ L hL _ f w s t`. Establish `hσ : ∀ x, σ (σ x) = x`. Introduce `x`. Set `τ : E →+* ℂ` to `(IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom`. Apply `τ.injective` to reduce the goal to its premises.

Rewrite using `[hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]`. Establish `key : Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ (L s) (L t) = 0`. Distinguish the cases in `ht : t = 0`. Rewrite using `[ht, map_zero L, symplOF_zero_right]`. Set `g : ℝ →+ AF F` to `AddMonoidHom.mk' (fun u => Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ (L u) (L t)) (fun a b => by simp only [map_add L, symplOF_add_left])`.

Establish `hg : Continuous g` using `(continuous_symplOF_left σ JS JT ξ₀ (L t)).comp hL`. Establish `h0 : g t = 0` using `symplOF_self σ JS JT hσ hS hT ξ₀ hξ (L t)`. Use `line_zero g hg t h0 (s / t)` as an intermediate fact. Rewrite `this` using `[div_mul_cancel₀ s ht]`. Then use the resulting hypothesis. Establish `k2 : Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (L s) (L t) = 0`.

Unfold `Formalism.IndefR.DatumF.symplOHF`. Rewrite using `[key, mul_zero]`. Unfold `Formalism.IndefR.DatumF.heisOF`. Rewrite using `[map_add L, symplOHF_add_right, symplOHF_add_left, k2, add_zero, AddChar.map_add_eq_mul, add_assoc, mul_assoc]`.
-/
theorem GlobalTheory.heisOF_line_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ) (w : Formalism.IndefR.DatumF.WOF F E nS nT) (s t : ℝ),
      Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L (s + t)) f w = B.ψ (Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ w (L s)) * Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L s) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ _ L hL _ f w s t
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
    apply τ.injective
    rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
  have key : Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ (L s) (L t) = 0 := by
    by_cases ht : t = 0
    · rw [ht, map_zero L, symplOF_zero_right]
    · let g : ℝ →+ AF F := AddMonoidHom.mk' (fun u => Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ (L u) (L t))
        (fun a b => by simp only [map_add L, symplOF_add_left])
      have hg : Continuous g := (continuous_symplOF_left σ JS JT ξ₀ (L t)).comp hL
      have h0 : g t = 0 := symplOF_self σ JS JT hσ hS hT ξ₀ hξ (L t)
      have := line_zero g hg t h0 (s / t)
      rwa [div_mul_cancel₀ s ht] at this
  have k2 : Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (L s) (L t) = 0 := by
    unfold Formalism.IndefR.DatumF.symplOHF; rw [key, mul_zero]
  unfold Formalism.IndefR.DatumF.heisOF
  rw [map_add L, symplOHF_add_right, symplOHF_add_left, k2, add_zero, AddChar.map_add_eq_mul, add_assoc, mul_assoc]
