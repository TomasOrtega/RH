import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinateAdditive
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.UnipDom
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.UnipDom.PlaneMat

open GlobalTheory.ThK.UnipDom.Additive

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2, h.2.2.2, star_star]`.
-/
theorem sigma_sigma (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

/- English proof (translation)
Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hJ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_swap (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → E) : form σ J w v = -σ (form σ J v w) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, form, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem gram_apply (σ : E →ₐ[F] E) {n : ℕ} {κ κ' : Type} (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) κ E)
    (A' : Matrix (Fin n) κ' E) (k : κ) (l : κ') :
    (Aᵀ * J * A'.map σ) k l = form σ J (fun m => A m k) (fun m => A' m l) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, form, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Establish `h : (fun i => cA σ ((w + w') i)) = (fun i => cA σ (w i)) + fun i => cA σ (w' i)`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Simplify using `only [fA]`. Rewrite using `[h, Matrix.mulVec_add, dotProduct_add]`.
-/
theorem fA_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w w' : Fin n → AE F E) :
    fA σ J v (w + w') = fA σ J v w + fA σ J v w' := by
  have h : (fun i => cA σ ((w + w') i)) = (fun i => cA σ (w i)) + fun i => cA σ (w' i) := by
    funext i; simp
  simp only [fA]
  rw [h, Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Establish `h : (fun i => cA σ ((c • w) i)) = cA σ c • fun i => cA σ (w i)`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Simplify using `only [fA]`. Rewrite using `[h, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
theorem fA_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : AE F E) (v w : Fin n → AE F E) :
    fA σ J v (c • w) = cA σ c * fA σ J v w := by
  have h : (fun i => cA σ ((c • w) i)) = cA σ c • fun i => cA σ (w i) := by
    funext i; simp
  simp only [fA]
  rw [h, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Establish `hu : (mat u)ᵀ * incM F J * (mat u).map (cA σ) = incM F J` using `u.2`. Establish `hc : (fun i => cA σ ((mat u *ᵥ w) i)) = (mat u).map (cA σ) *ᵥ fun i => cA σ (w i)`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec (cA σ).toRingHom (mat u) w i`. Simplify using `only [fA]`.

Rewrite using `[hc, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hu]`.
-/
theorem fA_mat (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (u : UA σ J) (v w : Fin n → AE F E) :
    fA σ J (mat u *ᵥ v) (mat u *ᵥ w) = fA σ J v w := by
  have hu : (mat u)ᵀ * incM F J * (mat u).map (cA σ) = incM F J := u.2
  have hc : (fun i => cA σ ((mat u *ᵥ w) i)) = (mat u).map (cA σ) *ᵥ fun i => cA σ (w i) := by
    funext i; exact RingHom.map_mulVec (cA σ).toRingHom (mat u) w i
  simp only [fA]
  rw [hc, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hu]

/- English proof (translation)
Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, incM, incV]`.
-/
theorem mul_incM_apply {n : ℕ} {κ : Type} (M : Matrix (Fin n) (Fin n) (AE F E)) (P : Matrix (Fin n) κ E)
    (i : Fin n) (o : κ) : (M * incM F P) i o = (M *ᵥ incV F (fun k => P k o)) i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, incM, incV]

/- English proof (translation)
Simplify using `[fA, Matrix.vecMul, Matrix.mulVec, dotProduct, incM, incV, Matrix.mul_apply, cA_inclR, map_sum, map_mul, Finset.mul_sum]`.
-/
theorem vecMul_incM_apply (σ : E →ₐ[F] E) {n : ℕ} {κ : Type} (J : Matrix (Fin n) (Fin n) E)
    (P : Matrix (Fin n) κ E) (v : Fin n → AE F E) (o : κ) :
    (v ᵥ* incM F (J * P.map σ)) o = fA σ J v (incV F (fun k => P k o)) := by
  simp [fA, Matrix.vecMul, Matrix.mulVec, dotProduct, incM, incV, Matrix.mul_apply, cA_inclR, map_sum, map_mul,
    Finset.mul_sum]

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Assume the negation of the conclusion as `hne`. Use `set τ : E →+* ℂ := (B.emb w).1 with hτ`. Establish `hx : star (τ ∘ v) ≠ 0`. Introduce `h0`.

Apply `hne` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Establish `h1` using `congrFun h0 i`. Simplify using `only [Pi.star_apply, Function.comp_apply, Pi.zero_apply, star_eq_zero] at h1`. Simplify using `using h1`.

Establish `hM : (Complex.I • Y₁.J.map τ) *ᵥ star (star (τ ∘ v)) = 0`. Rewrite using `[star_star]`. Use function extensionality and compare the values at `i`. Establish `h2 : (Y₁.J.map τ *ᵥ τ ∘ v) i = 0`. Rewrite using `[← RingHom.map_mulVec, hv]`.

Simplify using the standard rewrite rules. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, Pi.zero_apply] at h2 ⊢`. Rewrite using `[h2, mul_zero]`. Use `(hc w).2.2 _ hx` as an intermediate fact. Rewrite `this` using `[hM, dotProduct_zero, Complex.zero_re]`.

Conclude with `lt_irrefl _ this`.
-/
theorem eq_zero_of_cartan (B : Base F E) {n₁ : ℕ} (Y₁ : Spc F E n₁)
    (hc : ∀ w, IsCartan (Complex.I • Y₁.J.map (B.emb w).1) (Y₁.θ w)) (v : Fin n₁ → E) (hv : Y₁.J *ᵥ v = 0) :
    v = 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  by_contra hne
  set τ : E →+* ℂ := (B.emb w).1 with hτ
  have hx : star (τ ∘ v) ≠ 0 := by
    intro h0; apply hne; funext i
    have h1 := congrFun h0 i
    simp only [Pi.star_apply, Function.comp_apply, Pi.zero_apply, star_eq_zero] at h1
    simpa using h1
  have hM : (Complex.I • Y₁.J.map τ) *ᵥ star (star (τ ∘ v)) = 0 := by
    rw [star_star]; funext i
    have h2 : (Y₁.J.map τ *ᵥ τ ∘ v) i = 0 := by
      rw [← RingHom.map_mulVec, hv]; simp
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum,
      Pi.zero_apply] at h2 ⊢
    rw [h2, mul_zero]
  have := (hc w).2.2 _ hx
  rw [hM, dotProduct_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

/- English proof (translation)
Express the relevant statement in the definitionally equal form `a ⊗ₜ[F] σ 1 = a ⊗ₜ[F] (1 : E)`. Rewrite using `[map_one]`.
-/
theorem cA_base' (σ : E →ₐ[F] E) (a : AF F) : cA σ (algebraMap (AF F) (AE F E) a) = algebraMap (AF F) (AE F E) a := by
  change a ⊗ₜ[F] σ 1 = a ⊗ₜ[F] (1 : E)
  rw [map_one]

/- English proof (translation)
Use `haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Use `IsModuleTopology.continuous_of_ringHom (R := AF F) _ ?_` and prove the remaining obligations. Establish `: Continuous (algebraMap (AF F) (AE F E))` using `IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AE F E))`.

Conclude with `this.congr fun a => (cA_base' σ a).symm`.
-/
theorem cA_continuous (σ : E →ₐ[F] E) : Continuous (cA σ) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) _ ?_
  have : Continuous (algebraMap (AF F) (AE F E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AE F E))
  exact this.congr fun a => (cA_base' σ a).symm

end GlobalTheory.ThK.UnipDom.PlaneMat

open GlobalTheory.ThK.UnipDom.Additive GlobalTheory.ThK.UnipDom.PlaneMat in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n n₁ Y Y₁ H hCM hJ hP`. Take `⟨hn, hxx, hyy, hxy, horth, hgram, -, hc₁⟩` from `hP`. Establish `hσ` using `sigma_sigma σ hCM`. Use `haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _`.

Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Set `col : Option (Option (Fin n₁)) → Fin n → E` to `fun o => o.elim H.x (fun o' => o'.elim H.y (fun j => fun k => H.ι k j))`. Set `P : Matrix (Fin n) (Option (Option (Fin n₁))) E` to `Matrix.of fun k o => col o k`. Set `G` to `Pᵀ * Y.J * P.map σ`. Establish `hcolj : ∀ j, (fun k => H.ι k j) = H.ι *ᵥ Pi.single j 1` using `fun j => (Matrix.mulVec_single_one _ _).symm`.

Establish `hyx : form σ Y.J H.y H.x = -1` using `by rw [form_swap σ hσ _ hJ, hxy, map_one]`. Establish `hjx : ∀ j, form σ Y.J (fun k => H.ι k j) H.x = 0` using `fun j => by rw [hcolj]; exact (horth _).1`. Establish `hjy : ∀ j, form σ Y.J (fun k => H.ι k j) H.y = 0` using `fun j => by rw [hcolj]; exact (horth _).2`. Establish `hxj : ∀ j, form σ Y.J H.x (fun k => H.ι k j) = 0` using `fun j => by`. Rewrite using `[form_swap σ hσ _ hJ, hjx, map_zero, neg_zero]`.

Establish `hyj : ∀ j, form σ Y.J H.y (fun k => H.ι k j) = 0` using `fun j => by`. Rewrite using `[form_swap σ hσ _ hJ, hjy, map_zero, neg_zero]`. Establish `hjj : ∀ i l, form σ Y.J (fun k => H.ι k i) (fun k => H.ι k l) = Y₁.J i l` using `fun i l => by`. Rewrite using `[← hgram, gram_apply]`. Establish `hGdet : G.det ≠ 0`.

Introduce `h0`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`. Apply `hv0` to reduce the goal to its premises. Establish `hrow : ∀ o, ∑ l, form σ Y.J (col o) (col l) * v l = 0` using `fun o => by`. Use `congrFun hv o` as an intermediate fact.

Simplify using `only [Matrix.mulVec, dotProduct, G, gram_apply, Pi.zero_apply] at this`. Conclude with `this`. Establish `h1` using `hrow none`. Establish `h2` using `hrow (some none)`. Simplify using `only [Fintype.sum_option, col, Option.elim, hxx, hxy, hxj, hyx, hyy, hyj, zero_mul, one_mul, neg_mul, Finset.sum_const_zero, zero_add, add_zero, neg_eq_zero] at h1 h2`.

Establish `h3 : Y₁.J *ᵥ (fun l => v (some (some l))) = 0`. Use function extensionality and compare the values at `i`. Use `hrow (some (some i))` as an intermediate fact. Simplify using `only [Fintype.sum_option, col, Option.elim, hjx, hjy, hjj, zero_mul, zero_add] at this`. Simplify `this` using `[Matrix.mulVec, dotProduct]`.

Establish `h4` using `eq_zero_of_cartan B Y₁ hc₁ _ h3`. Use function extensionality and compare the values at `o`. Break down `o with _ | (_ | j)` into its components or cases. Conclude with `h2`. Conclude with `h1`.

Conclude with `congrFun h4 j`. Establish `hGu : IsUnit G.det` using `isUnit_iff_ne_zero.mpr hGdet`. Set `e : Option (Option (Fin n₁)) ≃ Fin n` to `Fintype.equivOfCardEq (by simp only [Fintype.card_option, Fintype.card_fin]; omega)`. Set `Rp : Matrix (Option (Option (Fin n₁))) (Fin n) E` to `(Y.J * P.map σ * G⁻¹)ᵀ`. Set `Rn : Matrix (Option (Option (Fin n₁))) (Fin n) E` to `G⁻¹ * Pᵀ`.

Establish `hPR : P * Rp = 1`. Establish `h1 : Pᵀ * (Y.J * P.map σ * G⁻¹) = 1`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc]`. Conclude with `Matrix.mul_nonsing_inv G hGu`. Establish `h2 : Rp * P = 1`.

Use `congrArg Matrix.transpose h1` as an intermediate fact. Rewrite `this` using `[Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one]`. Then use the resulting hypothesis. Conclude with `(Matrix.mul_eq_one_comm_of_equiv e).mp h2`. Establish `hNR : Y.J * P.map σ * Rn = 1`. Establish `h1 : Rn * (Y.J * P.map σ) = 1` using `by show G⁻¹ * Pᵀ * (Y.J * P.map σ) = 1`.

Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ]`. Conclude with `Matrix.nonsing_inv_mul G hGu`. Conclude with `(Matrix.mul_eq_one_comm_of_equiv e).mp h1`. Establish `hincM_mul : ∀ {a b c : Type} [Fintype b] (A : Matrix a b E) (A' : Matrix b c E), incM F (A * A') = incM F A * incM F A'` using `fun _ _ => Matrix.map_mul`. Establish `hincM_one : incM F (1 : Matrix (Fin n) (Fin n) E) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`.

Set `r : (Fin n₁ → AE F E) × AE F E → Option (Option (Fin n₁)) → AE F E` to `fun p o => o.elim (-1) (fun o' => o'.elim p.2 (fun j => cA σ (p.1 j)))`. Set `Q : (Fin n₁ → AE F E) × AE F E → Matrix (Fin n) (Option (Option (Fin n₁))) (AE F E)` to `fun p => Matrix.of fun i o => o.elim (incV F H.x i) (fun o' => o'.elim ((r p ᵥ* incM F Rn) i) (fun j => incM F H.ι i j + p.1 j * incV F H.x i))`. Use `⟨fun p => Q p * incM F Rp, ?_, fun u hu => ?_⟩` and prove the remaining obligations. Establish `hr : Continuous r`. Use `continuous_pi fun o => ?_` and prove the remaining obligations.

Break down `o with _ | (_ | j)` into its components or cases. Conclude with `continuous_const`. Conclude with `continuous_snd`. Conclude with `(cA_continuous σ).comp ((continuous_apply j).comp continuous_fst)`. Establish `hrv : Continuous fun p => r p ᵥ* incM F Rn` using `hr.matrix_vecMul continuous_const`.

Use `Continuous.matrix_mul ?_ continuous_const` and prove the remaining obligations. Use `continuous_pi fun i => continuous_pi fun o => ?_` and prove the remaining obligations. Break down `o with _ | (_ | j)` into its components or cases. Conclude with `continuous_const`. Conclude with `(continuous_apply i).comp hrv`.

Conclude with `continuous_const.add (((continuous_apply j).comp continuous_fst).mul continuous_const)`. Take `⟨hux, hua⟩` from `unip_spec hu`. Establish `ha : ∀ j, mat u *ᵥ incV F (fun k => H.ι k j) = incV F (fun k => H.ι k j) + coA σ Y.J H u j • incV F H.x`. Introduce `j`. Take `⟨a, ha⟩` from `hua (Pi.single j 1)`.

Establish `hcoA : coA σ Y.J H u j = a`. Simplify using `only [coA]`. Rewrite using `[ha, fA_add_left, fA_smul_left, fA_incV, hxy, map_one, mul_one, single_eq_incV, incM_mulVec_incV, fA_incV, (horth _).2, map_zero, zero_add]`. Rewrite using `[hcoA, hcolj, ← incM_mulVec_incV, ← single_eq_incV, ha]`. Establish `hvx : fA σ Y.J (mat u *ᵥ incV F H.y) (incV F H.x) = -1` using `by conv_lhs => rw [← hux]`.

Rewrite using `[fA_mat, fA_incV, hyx, map_neg, map_one]`. Establish `hvN : (mat u *ᵥ incV F H.y) ᵥ* incM F (Y.J * P.map σ) = r (coA σ Y.J H u, coC σ Y.J H u)`. Use function extensionality and compare the values at `o`. Rewrite using `[vecMul_incM_apply]`. Break down `o with _ | (_ | j)` into its components or cases.

Conclude with `hvx`. Both sides reduce to the same expression. Use `show fA σ Y.J (mat u *ᵥ incV F H.y) (incV F (fun k => H.ι k j)) = cA σ (coA σ Y.J H u j)`. Establish `h0 : fA σ Y.J (mat u *ᵥ incV F H.y) (mat u *ᵥ incV F (fun k => H.ι k j)) = 0`. Rewrite using `[fA_mat, fA_incV, hyj, map_zero]`.

Rewrite `h0` using `[ha, fA_add_right, fA_smul_right, hvx]`. Take the linear combination `h0`. Establish `hv : mat u *ᵥ incV F H.y = r (coA σ Y.J H u, coC σ Y.J H u) ᵥ* incM F Rn`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hNR, hincM_one, Matrix.vecMul_one]`.

Use `_ = _ := by rw [hincM_mul, ← Matrix.vecMul_vecMul, hvN]`. Establish `hMQ : mat u * incM F P = Q (coA σ Y.J H u, coC σ Y.J H u)`. Use extensionality with `i o`. Rewrite using `[mul_incM_apply]`. Break down `o with _ | (_ | j)` into its components or cases.

Use `show (mat u *ᵥ incV F H.x) i = incV F H.x i`. Rewrite using `[hux]`. Use `show (mat u *ᵥ incV F H.y) i = (r _ ᵥ* incM F Rn) i`. Rewrite using `[hv]`. Use `show (mat u *ᵥ incV F (fun k => H.ι k j)) i = incM F H.ι i j + coA σ Y.J H u j * incV F H.x i`.

Rewrite using `[ha]`. Simplify using `[incM, incV]`. Use `show mat u = Q (coA σ Y.J H u, coC σ Y.J H u) * incM F Rp`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem GlobalTheory.ThK.UnipDom.exists_continuous_mat_eq_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), IsCMExt F E σ → (∀ i j, σ (Y.J j i) = -Y.J i j) → IsIsoPlane σ B H Y Y₁ → ∃ Ψ : (Fin n₁ → AE F E) × AE F E → Matrix (Fin n) (Fin n) (AE F E), Continuous Ψ ∧ ∀ u ∈ unip σ Y H, mat u = Ψ (coA σ Y.J H u, coC σ Y.J H u) := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H hCM hJ hP
  obtain ⟨hn, hxx, hyy, hxy, horth, hgram, -, hc₁⟩ := hP
  have hσ := sigma_sigma σ hCM
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let col : Option (Option (Fin n₁)) → Fin n → E :=
    fun o => o.elim H.x (fun o' => o'.elim H.y (fun j => fun k => H.ι k j))
  let P : Matrix (Fin n) (Option (Option (Fin n₁))) E := Matrix.of fun k o => col o k
  let G := Pᵀ * Y.J * P.map σ
  have hcolj : ∀ j, (fun k => H.ι k j) = H.ι *ᵥ Pi.single j 1 := fun j => (Matrix.mulVec_single_one _ _).symm
  have hyx : form σ Y.J H.y H.x = -1 := by rw [form_swap σ hσ _ hJ, hxy, map_one]
  have hjx : ∀ j, form σ Y.J (fun k => H.ι k j) H.x = 0 := fun j => by rw [hcolj]; exact (horth _).1
  have hjy : ∀ j, form σ Y.J (fun k => H.ι k j) H.y = 0 := fun j => by rw [hcolj]; exact (horth _).2
  have hxj : ∀ j, form σ Y.J H.x (fun k => H.ι k j) = 0 := fun j => by
    rw [form_swap σ hσ _ hJ, hjx, map_zero, neg_zero]
  have hyj : ∀ j, form σ Y.J H.y (fun k => H.ι k j) = 0 := fun j => by
    rw [form_swap σ hσ _ hJ, hjy, map_zero, neg_zero]
  have hjj : ∀ i l, form σ Y.J (fun k => H.ι k i) (fun k => H.ι k l) = Y₁.J i l := fun i l => by
    rw [← hgram, gram_apply]
  have hGdet : G.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hv0
    have hrow : ∀ o, ∑ l, form σ Y.J (col o) (col l) * v l = 0 := fun o => by
      have := congrFun hv o
      simp only [Matrix.mulVec, dotProduct, G, gram_apply, Pi.zero_apply] at this
      exact this
    have h1 := hrow none
    have h2 := hrow (some none)
    simp only [Fintype.sum_option, col, Option.elim, hxx, hxy, hxj, hyx, hyy, hyj, zero_mul, one_mul, neg_mul,
      Finset.sum_const_zero, zero_add, add_zero, neg_eq_zero] at h1 h2
    have h3 : Y₁.J *ᵥ (fun l => v (some (some l))) = 0 := by
      funext i
      have := hrow (some (some i))
      simp only [Fintype.sum_option, col, Option.elim, hjx, hjy, hjj, zero_mul, zero_add] at this
      simpa [Matrix.mulVec, dotProduct] using this
    have h4 := eq_zero_of_cartan B Y₁ hc₁ _ h3
    funext o
    rcases o with _ | (_ | j)
    · exact h2
    · exact h1
    · exact congrFun h4 j
  have hGu : IsUnit G.det := isUnit_iff_ne_zero.mpr hGdet
  let e : Option (Option (Fin n₁)) ≃ Fin n :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_option, Fintype.card_fin]; omega)
  let Rp : Matrix (Option (Option (Fin n₁))) (Fin n) E := (Y.J * P.map σ * G⁻¹)ᵀ
  let Rn : Matrix (Option (Option (Fin n₁))) (Fin n) E := G⁻¹ * Pᵀ
  have hPR : P * Rp = 1 := by
    have h1 : Pᵀ * (Y.J * P.map σ * G⁻¹) = 1 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]; exact Matrix.mul_nonsing_inv G hGu
    have h2 : Rp * P = 1 := by
      have := congrArg Matrix.transpose h1
      rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
    exact (Matrix.mul_eq_one_comm_of_equiv e).mp h2
  have hNR : Y.J * P.map σ * Rn = 1 := by
    have h1 : Rn * (Y.J * P.map σ) = 1 := by
      show G⁻¹ * Pᵀ * (Y.J * P.map σ) = 1
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ]; exact Matrix.nonsing_inv_mul G hGu
    exact (Matrix.mul_eq_one_comm_of_equiv e).mp h1
  have hincM_mul : ∀ {a b c : Type} [Fintype b] (A : Matrix a b E) (A' : Matrix b c E),
      incM F (A * A') = incM F A * incM F A' := fun _ _ => Matrix.map_mul
  have hincM_one : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  let r : (Fin n₁ → AE F E) × AE F E → Option (Option (Fin n₁)) → AE F E :=
    fun p o => o.elim (-1) (fun o' => o'.elim p.2 (fun j => cA σ (p.1 j)))
  let Q : (Fin n₁ → AE F E) × AE F E → Matrix (Fin n) (Option (Option (Fin n₁))) (AE F E) :=
    fun p => Matrix.of fun i o => o.elim (incV F H.x i)
      (fun o' => o'.elim ((r p ᵥ* incM F Rn) i) (fun j => incM F H.ι i j + p.1 j * incV F H.x i))
  refine ⟨fun p => Q p * incM F Rp, ?_, fun u hu => ?_⟩
  · have hr : Continuous r := by
      refine continuous_pi fun o => ?_
      rcases o with _ | (_ | j)
      · exact continuous_const
      · exact continuous_snd
      · exact (cA_continuous σ).comp ((continuous_apply j).comp continuous_fst)
    have hrv : Continuous fun p => r p ᵥ* incM F Rn := hr.matrix_vecMul continuous_const
    refine Continuous.matrix_mul ?_ continuous_const
    refine continuous_pi fun i => continuous_pi fun o => ?_
    rcases o with _ | (_ | j)
    · exact continuous_const
    · exact (continuous_apply i).comp hrv
    · exact continuous_const.add (((continuous_apply j).comp continuous_fst).mul continuous_const)
  · obtain ⟨hux, hua⟩ := unip_spec hu
    have ha : ∀ j, mat u *ᵥ incV F (fun k => H.ι k j) =
        incV F (fun k => H.ι k j) + coA σ Y.J H u j • incV F H.x := by
      intro j
      obtain ⟨a, ha⟩ := hua (Pi.single j 1)
      have hcoA : coA σ Y.J H u j = a := by
        simp only [coA]
        rw [ha, fA_add_left, fA_smul_left, fA_incV, hxy, map_one, mul_one, single_eq_incV, incM_mulVec_incV, fA_incV,
          (horth _).2, map_zero, zero_add]
      rw [hcoA, hcolj, ← incM_mulVec_incV, ← single_eq_incV, ha]
    have hvx : fA σ Y.J (mat u *ᵥ incV F H.y) (incV F H.x) = -1 := by
      conv_lhs => rw [← hux]
      rw [fA_mat, fA_incV, hyx, map_neg, map_one]
    have hvN : (mat u *ᵥ incV F H.y) ᵥ* incM F (Y.J * P.map σ) = r (coA σ Y.J H u, coC σ Y.J H u) := by
      funext o
      rw [vecMul_incM_apply]
      rcases o with _ | (_ | j)
      · exact hvx
      · rfl
      · show fA σ Y.J (mat u *ᵥ incV F H.y) (incV F (fun k => H.ι k j)) = cA σ (coA σ Y.J H u j)
        have h0 : fA σ Y.J (mat u *ᵥ incV F H.y) (mat u *ᵥ incV F (fun k => H.ι k j)) = 0 := by
          rw [fA_mat, fA_incV, hyj, map_zero]
        rw [ha, fA_add_right, fA_smul_right, hvx] at h0
        linear_combination h0
    have hv : mat u *ᵥ incV F H.y = r (coA σ Y.J H u, coC σ Y.J H u) ᵥ* incM F Rn := by
      calc mat u *ᵥ incV F H.y = (mat u *ᵥ incV F H.y) ᵥ* incM F (Y.J * P.map σ * Rn) := by
            rw [hNR, hincM_one, Matrix.vecMul_one]
        _ = _ := by rw [hincM_mul, ← Matrix.vecMul_vecMul, hvN]
    have hMQ : mat u * incM F P = Q (coA σ Y.J H u, coC σ Y.J H u) := by
      ext i o
      rw [mul_incM_apply]
      rcases o with _ | (_ | j)
      · show (mat u *ᵥ incV F H.x) i = incV F H.x i
        rw [hux]
      · show (mat u *ᵥ incV F H.y) i = (r _ ᵥ* incM F Rn) i
        rw [hv]
      · show (mat u *ᵥ incV F (fun k => H.ι k j)) i = incM F H.ι i j + coA σ Y.J H u j * incV F H.x i
        rw [ha]
        simp [incM, incV]
    show mat u = Q (coA σ Y.J H u, coC σ Y.J H u) * incM F Rp
    calc mat u = mat u * incM F (P * Rp) := by rw [hPR, hincM_one, Matrix.mul_one]
      _ = _ := by rw [hincM_mul, ← Matrix.mul_assoc, hMQ]
