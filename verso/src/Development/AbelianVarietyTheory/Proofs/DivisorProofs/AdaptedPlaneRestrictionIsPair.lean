import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTransposeInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIsotropicLeCardStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfHasSigStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticModelRationalCoordinatesStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagrX

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Simplify using `only [hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `conv_lhs => arg 2`. Use extensionality with `i`.

Rewrite using `[Finset.sum_comm]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem hTens_eq {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    hTens c JA JB x y = ∑ j, ∑ l, (xᵀ * JA * y.map c) j l * JB j l := by
  simp only [hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Simplify using `[cA, inclR]`.
-/
theorem cA_incl (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[incM, cA_incl]`.
-/
theorem incM_map_cA {m k : Type} (A : Matrix m k E) : (incM F A).map (cA σ) = incM F (A.map σ) := by
  ext i j; simp [incM, cA_incl]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[incV, cA_incl]`.
-/
theorem incV_map_cA {m : ℕ} (a : Fin m → E) : (fun i => cA σ (incV F a i)) = incV F (fun i => σ (a i)) := by
  funext i; simp [incV, cA_incl]

/- English proof (translation)
Simplify using `only [incM]`. Conclude with `Matrix.map_mul`.
-/
theorem incM_mul {m k l : Type} [Fintype k] (A : Matrix m k E) (C : Matrix k l E) : incM F (A * C) = incM F A * incM F C := by
  simp only [incM]; exact Matrix.map_mul

/- English proof (translation)
Simplify using `only [incM]`. Conclude with `Matrix.transpose_map`.
-/
theorem incM_transpose {m k : Type} (A : Matrix m k E) : incM F Aᵀ = (incM F A)ᵀ := by
  simp only [incM]; exact Matrix.transpose_map

/- English proof (translation)
Simplify using `only [incM]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem incM_one {m : Type} [DecidableEq m] : incM F (1 : Matrix m m E) = 1 := by
  simp only [incM]; exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [incM, incV]`. Conclude with `(RingHom.map_mulVec _ A a i).symm`.
-/
theorem incM_mulVec {m k : ℕ} (A : Matrix (Fin m) (Fin k) E) (a : Fin k → E) : incM F A *ᵥ incV F a = incV F (A *ᵥ a) := by
  funext i; simp only [incM, incV]; exact (RingHom.map_mulVec _ A a i).symm

/- English proof (translation)
The claim follows from `(RingHom.map_dotProduct (inclR (F := F) (AF F)) a b).symm`.
-/
theorem incV_dot {m : ℕ} (a b : Fin m → E) : incV F a ⬝ᵥ incV F b = inclR (F := F) (AF F) (a ⬝ᵥ b) :=
  (RingHom.map_dotProduct (inclR (F := F) (AF F)) a b).symm

/- English proof (translation)
Rewrite using `[incV_map_cA, incM_mulVec, incV_dot]`. Both sides reduce to the same expression.
-/
theorem incl_form {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (a b : Fin m → E) :
    incV F a ⬝ᵥ incM F J *ᵥ (fun i => cA σ (incV F b i)) = inclR (F := F) (AF F) (form σ J a b) := by
  rw [incV_map_cA, incM_mulVec, incV_dot]; rfl

/- English proof (translation)
Simplify using `[symp, hTens_eq, h]`.
-/
theorem symp_eq_zero {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (x y : Matrix (Fin n) (Fin d) (AE F E)) (h : xᵀ * incM F JA * y.map (cA σ) = 0) :
    symp (cA σ) (-1) (incM F JA) (incM F JB) x y = 0 := by
  simp [symp, hTens_eq, h]

variable {n d n₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁}

def IsMixedX (M₁ : Model σ X₁ W) (H : Plane E n n₁) (m : Matrix (Fin n) (Fin d) (AE F E)) : Prop :=
  ∃ y : Fin d → AE F E, ∃ z : Matrix (Fin n₁) (Fin d) (AE F E), (M₁.co.e z).1 = 0 ∧
    m = Matrix.vecMulVec (incV F H.x) y + incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, 0, by simp, by ext i j; simp [Matrix.vecMulVec_apply]⟩`.
-/
theorem isMixedX_zero (M₁ : Model σ X₁ W) (H : Plane E n n₁) : IsMixedX M₁ H 0 :=
  ⟨0, 0, by simp, by ext i j; simp [Matrix.vecMulVec_apply]⟩

/- English proof (translation)
Take `⟨y, z, hz, rfl⟩` from `h`. Take `⟨y', z', hz', rfl⟩` from `h'`. Use `⟨y + y', z + z', by simp [hz, hz'], ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.vecMulVec_add, Matrix.mul_add, Matrix.add_mul]`. Normalize the expressions using the abelian group laws.
-/
theorem IsMixedX.add {M₁ : Model σ X₁ W} {H : Plane E n n₁} {m m' : Matrix (Fin n) (Fin d) (AE F E)}
    (h : IsMixedX M₁ H m) (h' : IsMixedX M₁ H m') : IsMixedX M₁ H (m + m') := by
  obtain ⟨y, z, hz, rfl⟩ := h
  obtain ⟨y', z', hz', rfl⟩ := h'
  refine ⟨y + y', z + z', by simp [hz, hz'], ?_⟩
  rw [Matrix.vecMulVec_add, Matrix.mul_add, Matrix.add_mul]
  abel

/- English proof (translation)
Take `⟨y, z, hz, rfl⟩` from `h`. Use `⟨t • y, t • z, by simp [hz], ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, Matrix.vecMulVec_smul, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem IsMixedX.smul {M₁ : Model σ X₁ W} {H : Plane E n n₁} {m : Matrix (Fin n) (Fin d) (AE F E)}
    (h : IsMixedX M₁ H m) (t : AF F) : IsMixedX M₁ H (t • m) := by
  obtain ⟨y, z, hz, rfl⟩ := h
  refine ⟨t • y, t • z, by simp [hz], ?_⟩
  rw [smul_add, Matrix.vecMulVec_smul, Matrix.mul_smul, Matrix.smul_mul]

def lagrX (M : Model σ X W) (M₁ : Model σ X₁ W) (H : Plane E n n₁) :
    Submodule F ((Fin n × Fin d → F) × (Fin n × Fin d → F)) where
  carrier := {w | IsMixedX M₁ H (M.co.e.symm (GlobalTheory.MixedLagr.hat w))}
  zero_mem' := by simpa [GlobalTheory.MixedLagr.hat_zero] using isMixedX_zero M₁ H
  add_mem' := fun ha hb => by simpa [Set.mem_setOf_eq, GlobalTheory.MixedLagr.hat_add, map_add] using ha.add hb
  smul_mem' := fun c a ha => by
    show IsMixedX M₁ H (M.co.e.symm (GlobalTheory.MixedLagr.hat (c • a)))
    rw [GlobalTheory.MixedLagr.hat_smul, LinearEquiv.map_smul]
    exact ha.smul _

section Symp
variable {B : Base F E} {j₀ j₁ : ℕ} {H : Plane E n n₁}

/- English proof (translation)
Establish `hm : (Matrix.vecMulVec (incV F H.x) y').map (cA σ) = Matrix.vecMulVec (fun i => cA σ (incV F H.x i)) (fun l => cA σ (y' l))`. Use extensionality with `i j`. Simplify using `[Matrix.vecMulVec_apply]`. Rewrite using `[hm, Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul_vecMulVec, ← Matrix.dotProduct_mulVec, incl_form, hH.xx, map_zero, zero_smul, Matrix.vecMulVec_zero]`.
-/
theorem piece_xx (hH : H.IsAdapted σ B X X₁ j₀ j₁) (y y' : Fin d → AE F E) :
    (Matrix.vecMulVec (incV F H.x) y)ᵀ * incM F X.J * (Matrix.vecMulVec (incV F H.x) y').map (cA σ) = 0 := by
  have hm : (Matrix.vecMulVec (incV F H.x) y').map (cA σ) =
      Matrix.vecMulVec (fun i => cA σ (incV F H.x i)) (fun l => cA σ (y' l)) := by
    ext i j; simp [Matrix.vecMulVec_apply]
  rw [hm, Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul_vecMulVec, ← Matrix.dotProduct_mulVec,
    incl_form, hH.xx, map_zero, zero_smul, Matrix.vecMulVec_zero]

/- English proof (translation)
Establish `hm : (Matrix.vecMulVec (incV F H.x) y').map (cA σ) = Matrix.vecMulVec (fun i => cA σ (incV F H.x i)) (fun l => cA σ (y' l))`. Use extensionality with `i j`. Simplify using `[Matrix.vecMulVec_apply]`. Establish `hv : ((incM F H.ι)ᵀ * incM F X.J) *ᵥ (fun i => cA σ (incV F H.x i)) = 0`. Use function extensionality and compare the values at `m`.

Rewrite using `[← Matrix.mulVec_mulVec]`. Express the relevant statement in the definitionally equal form `(fun i => incM F H.ι i m) ⬝ᵥ _ = 0`. Establish `: (fun i => incM F H.ι i m) = incV F (H.ι *ᵥ Pi.single m 1)`. Use function extensionality and compare the values at `i`. Simplify using `[incM, incV, Matrix.mulVec_single_one]`.

Rewrite using `[this, incl_form, (hH.orth _).1, map_zero]`. Rewrite using `[incM_one, Matrix.transpose_one, Matrix.mul_one, Matrix.transpose_mul, hm, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (incM F H.ι)ᵀ, Matrix.mul_vecMulVec, hv, Matrix.zero_vecMulVec, Matrix.mul_zero]`.
-/
theorem piece_ix (hH : H.IsAdapted σ B X X₁ j₀ j₁) (z : Matrix (Fin n₁) (Fin d) (AE F E)) (y' : Fin d → AE F E) :
    (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ)ᵀ * incM F X.J *
      (Matrix.vecMulVec (incV F H.x) y').map (cA σ) = 0 := by
  have hm : (Matrix.vecMulVec (incV F H.x) y').map (cA σ) =
      Matrix.vecMulVec (fun i => cA σ (incV F H.x i)) (fun l => cA σ (y' l)) := by
    ext i j; simp [Matrix.vecMulVec_apply]
  have hv : ((incM F H.ι)ᵀ * incM F X.J) *ᵥ (fun i => cA σ (incV F H.x i)) = 0 := by
    funext m
    rw [← Matrix.mulVec_mulVec]
    change (fun i => incM F H.ι i m) ⬝ᵥ _ = 0
    have : (fun i => incM F H.ι i m) = incV F (H.ι *ᵥ Pi.single m 1) := by
      funext i; simp [incM, incV, Matrix.mulVec_single_one]
    rw [this, incl_form, (hH.orth _).1, map_zero]
  rw [incM_one, Matrix.transpose_one, Matrix.mul_one, Matrix.transpose_mul, hm, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc (incM F H.ι)ᵀ, Matrix.mul_vecMulVec, hv, Matrix.zero_vecMulVec, Matrix.mul_zero]

/- English proof (translation)
Rewrite using `[incM_one, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_one, Matrix.transpose_mul, Matrix.map_mul, incM_map_cA, ← hH.gram, incM_mul, incM_mul, incM_transpose]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem piece_ii (hH : H.IsAdapted σ B X X₁ j₀ j₁) (z z' : Matrix (Fin n₁) (Fin d) (AE F E)) :
    (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ)ᵀ * incM F X.J *
      (incM F H.ι * z' * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ).map (cA σ) = zᵀ * incM F X₁.J * z'.map (cA σ) := by
  rw [incM_one, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_one, Matrix.transpose_mul, Matrix.map_mul, incM_map_cA,
    ← hH.gram, incM_mul, incM_mul, incM_transpose]
  simp only [Matrix.mul_assoc]

end Symp

end GlobalTheory.MixedLagrX

namespace GlobalTheory.MixedLagrX
open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d n₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {B : Base F E} {j₀ j₁ : ℕ} {H : Plane E n n₁}

/- English proof (translation)
Take `⟨y, z, hz, rfl⟩` from `h`. Take `⟨y', z', hz', rfl⟩` from `h'`. Establish `hQ : ∀ a b, (M.co.e a).1 ⬝ᵥ (M.co.e b).2 - (M.co.e b).1 ⬝ᵥ (M.co.e a).2 = symp (cA σ) (-1) (incM F X.J) (incM F W.J) a b` using `fun a b => (M.co.form a b).symm`. Establish `h1` using `symp_eq_zero (JB := W.J) _ _ _ (piece_xx hH y y')`. Establish `h2` using `symp_eq_zero (JB := W.J) _ _ _ (piece_ix hH z y')`.

Establish `h3` using `symp_eq_zero (JB := W.J) _ _ _ (piece_ix hH z' y)`. Establish `h4 : symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) (incM F H.ι * z' * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) = 0`. Establish `: symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) (incM F H.ι * z' * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) = symp (cA σ) (-1) (incM F X₁.J) (incM F W.J) z z'`. Simplify using `only [symp, hTens_eq, piece_ii hH]`. Rewrite using `[this, M₁.co.form, hz, hz', zero_dotProduct, zero_dotProduct, sub_self]`.

Rewrite `h1`, `h2`, `h3`, `h4` using `[← hQ]`. Simplify using `only [map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]`. Take the linear combination `h1 + h2 - h3 + h4`.
-/
theorem symp_mixed (hH : H.IsAdapted σ B X X₁ j₀ j₁) (M : Model σ X W) (M₁ : Model σ X₁ W)
    {m m' : Matrix (Fin n) (Fin d) (AE F E)} (h : IsMixedX M₁ H m) (h' : IsMixedX M₁ H m') :
    (M.co.e m).1 ⬝ᵥ (M.co.e m').2 - (M.co.e m').1 ⬝ᵥ (M.co.e m).2 = 0 := by
  obtain ⟨y, z, hz, rfl⟩ := h
  obtain ⟨y', z', hz', rfl⟩ := h'
  have hQ : ∀ a b, (M.co.e a).1 ⬝ᵥ (M.co.e b).2 - (M.co.e b).1 ⬝ᵥ (M.co.e a).2 =
      symp (cA σ) (-1) (incM F X.J) (incM F W.J) a b := fun a b => (M.co.form a b).symm
  have h1 := symp_eq_zero (JB := W.J) _ _ _ (piece_xx hH y y')
  have h2 := symp_eq_zero (JB := W.J) _ _ _ (piece_ix hH z y')
  have h3 := symp_eq_zero (JB := W.J) _ _ _ (piece_ix hH z' y)
  have h4 : symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ)
      (incM F H.ι * z' * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) = 0 := by
    have : symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ)
        (incM F H.ι * z' * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) =
        symp (cA σ) (-1) (incM F X₁.J) (incM F W.J) z z' := by
      simp only [symp, hTens_eq, piece_ii hH]
    rw [this, M₁.co.form, hz, hz', zero_dotProduct, zero_dotProduct, sub_self]
  rw [← hQ] at h1 h2 h3 h4
  simp only [map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  linear_combination h1 + h2 - h3 + h4

end GlobalTheory.MixedLagrX

namespace GlobalTheory.MixedLagrX
open Matrix

/- English proof (translation)
Simplify using `[form, add_dotProduct]`.
-/
theorem form_add_left {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (a b c : Fin m → E) : form σ J (a + b) c = form σ J a c + form σ J b c := by
  simp [form, add_dotProduct]

/- English proof (translation)
Simplify using `[form, smul_dotProduct]`.
-/
theorem form_smul_left {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (t : E) (a c : Fin m → E) : form σ J (t • a) c = t * form σ J a c := by
  simp [form, smul_dotProduct]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁`. Establish `h2 : Module.finrank F E = 2` using `hP.base.cm.2.2.1`. Take `⟨Φ, hΦ⟩` from `GlobalTheory.T.quadratic_model_rational_coordinates F E σ n d X W M B.ψ hP.good h2`. Take `⟨Φ₁, hΦ₁⟩` from `GlobalTheory.T.quadratic_model_rational_coordinates F E σ n₁ d X₁ W M₁ B.ψ hP₁.good h2`. Establish `hdet : X₁.J.det ≠ 0`.

Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Introduce `h0`. Apply `GlobalTheory.T.det_ne_zero_of_hasSig_divisor n₁ _ r₁ s₁ (hP₁.herm.sig w)` to reduce the goal to its premises. Use `RingHom.map_det (B.emb w).1 X₁.J` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`.

Conclude with `this.symm`. Set `f₁ : Matrix (Fin n₁) (Fin d) E →ₗ[F] (Fin n₁ × Fin d → F)` to `(LinearMap.fst F _ _).comp Φ₁.toLinearMap`. Establish `hf₁ : Function.Surjective f₁` using `fun v => ⟨Φ₁.symm (v, 0), by simp [f₁]⟩`. Establish `hZ : Module.finrank F (LinearMap.ker f₁) = n₁ * d`. Use `LinearMap.finrank_range_add_finrank_ker f₁` as an intermediate fact.

Rewrite `this` using `[LinearMap.range_eq_top.mpr hf₁, finrank_top, LinearEquiv.finrank_eq Φ₁, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Set `G : (Fin d → E) × LinearMap.ker f₁ →ₗ[F] Matrix (Fin n) (Fin d) E` to `{ toFun := fun p => Matrix.vecMulVec H.x p.1 + H.ι * (p.2 : Matrix (Fin n₁) (Fin d) E) map_add' := fun p q => by`. Simplify using `only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.vecMulVec_add, Matrix.mul_add]`. Normalize the expressions using the abelian group laws.

Use the proof step `map_smul' := fun c p => by`. Use extensionality with `i j`. Simplify using `[Matrix.vecMulVec_apply, Matrix.mul_apply, Algebra.smul_def]`. Rewrite using `[mul_add, Finset.mul_sum]`. Use `ring }`.

Establish `hmem : ∀ p, Φ (G p) ∈ lagrX M M₁ H`. Introduce `p`. Use `show IsMixedX M₁ H (M.co.e.symm (GlobalTheory.MixedLagr.hat (Φ (G p))))`. Establish `: GlobalTheory.MixedLagr.hat (Φ (G p)) = M.co.e (incM F (G p))` using `(hΦ _).symm`. Rewrite using `[this, LinearEquiv.symm_apply_apply]`.

Use `⟨incV F p.1, incM F (p.2 : Matrix (Fin n₁) (Fin d) E), ?_, ?_⟩` and prove the remaining obligations. Establish `hz : (Φ₁ (p.2 : Matrix (Fin n₁) (Fin d) E)).1 = 0` using `p.2.2`. Rewrite using `[hΦ₁, hz]`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Rewrite using `[incM_one, Matrix.transpose_one, Matrix.mul_one, ← incM_mul]`. Use extensionality with `i j`. Simplify using `only [incM, incV, G, LinearMap.coe_mk, AddHom.coe_mk, Matrix.map_apply, Matrix.add_apply, Matrix.vecMulVec_apply, map_add, map_mul]`. Establish `hGinj : ∀ p, G p = 0 → p = 0`. Introduce and unpack `⟨y, z⟩ h`.

Express the relevant statement in the definitionally equal form `Matrix.vecMulVec H.x y + H.ι * (z : Matrix (Fin n₁) (Fin d) E) = 0 at h`. Establish `hy : y = 0`. Use function extensionality and compare the values at `j`. Establish `hcol : (fun i => (Matrix.vecMulVec H.x y + H.ι * (z : Matrix (Fin n₁) (Fin d) E)) i j) = y j • H.x + H.ι *ᵥ (fun k => (z : Matrix (Fin n₁) (Fin d) E) k j)`. Use function extensionality and compare the values at `i`.

Simplify using `[Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]`. Establish `hj` using `congrArg (fun A : Fin n → E => form σ X.J A H.y) hcol`. Simplify using `only [h, Matrix.zero_apply] at hj`. Rewrite `hj` using `[form_add_left, form_smul_left, hH.xy, (hH.orth _).2, mul_one, add_zero]`. Rewrite using `[← hj]`.

Simplify using `[form]`. Substitute `hy` using the available equality. Establish `hιz : H.ι * (z : Matrix (Fin n₁) (Fin d) E) = 0`. Use extensionality with `i j`. Use `congrFun (congrFun h i) j` as an intermediate fact.

Simplify `this` using `[Matrix.vecMulVec_apply]`. Establish `h1 : H.ι.map σ * (z : Matrix (Fin n₁) (Fin d) E).map σ = 0`. Rewrite using `[← Matrix.map_mul, hιz]`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Establish `h3 : X₁.J * (z : Matrix (Fin n₁) (Fin d) E).map σ = 0`. Rewrite using `[← hH.gram, Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_zero, Matrix.mul_zero]`. Establish `h4 : (z : Matrix (Fin n₁) (Fin d) E).map σ = 0`. Use `congrArg (X₁.J⁻¹ * ·) h3` as an intermediate fact. Simplify using `only [Matrix.mul_zero] at this`.

Rewrite `this` using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mul]`. Then use the resulting hypothesis. Establish `h5 : (z : Matrix (Fin n₁) (Fin d) E) = 0`. Use extensionality with `i j`. Use `congrFun (congrFun h4 i) j` as an intermediate fact. Simplify using `using this`.

Conclude with `Prod.ext rfl (Subtype.ext h5)`. Set `T : (Fin d → E) × LinearMap.ker f₁ →ₗ[F] lagrX M M₁ H` to `(Φ.toLinearMap.comp G).codRestrict _ hmem`. Establish `hT : Function.Injective T`. Introduce `p q hpq`. Establish `hG : G p = G q` using `Φ.injective (congrArg Subtype.val hpq)`.

Rewrite `hG` using `[← sub_eq_zero, ← map_sub]`. Conclude with `sub_eq_zero.mp (hGinj _ hG)`. Establish `hle` using `LinearMap.finrank_le_finrank_of_injective hT`. Rewrite `hle` using `[Module.finrank_prod, hZ, Module.finrank_pi_fintype]`. Simplify using `only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem le_finrank_lagrX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      Fintype.card (Fin n × Fin d) ≤ Module.finrank F (lagrX M M₁ H) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁
  have h2 : Module.finrank F E = 2 := hP.base.cm.2.2.1
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.quadratic_model_rational_coordinates F E σ n d X W M B.ψ hP.good h2
  obtain ⟨Φ₁, hΦ₁⟩ := GlobalTheory.T.quadratic_model_rational_coordinates F E σ n₁ d X₁ W M₁ B.ψ hP₁.good h2
  have hdet : X₁.J.det ≠ 0 := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    intro h0
    apply GlobalTheory.T.det_ne_zero_of_hasSig_divisor n₁ _ r₁ s₁ (hP₁.herm.sig w)
    have := RingHom.map_det (B.emb w).1 X₁.J
    rw [h0, map_zero] at this
    exact this.symm
  let f₁ : Matrix (Fin n₁) (Fin d) E →ₗ[F] (Fin n₁ × Fin d → F) := (LinearMap.fst F _ _).comp Φ₁.toLinearMap
  have hf₁ : Function.Surjective f₁ := fun v => ⟨Φ₁.symm (v, 0), by simp [f₁]⟩
  have hZ : Module.finrank F (LinearMap.ker f₁) = n₁ * d := by
    have := LinearMap.finrank_range_add_finrank_ker f₁
    rw [LinearMap.range_eq_top.mpr hf₁, finrank_top, LinearEquiv.finrank_eq Φ₁, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
    omega
  let G : (Fin d → E) × LinearMap.ker f₁ →ₗ[F] Matrix (Fin n) (Fin d) E :=
    { toFun := fun p => Matrix.vecMulVec H.x p.1 + H.ι * (p.2 : Matrix (Fin n₁) (Fin d) E)
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.vecMulVec_add, Matrix.mul_add]; abel
      map_smul' := fun c p => by
        ext i j
        simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Algebra.smul_def]
        rw [mul_add, Finset.mul_sum]
        ring }
  have hmem : ∀ p, Φ (G p) ∈ lagrX M M₁ H := by
    intro p
    show IsMixedX M₁ H (M.co.e.symm (GlobalTheory.MixedLagr.hat (Φ (G p))))
    have : GlobalTheory.MixedLagr.hat (Φ (G p)) = M.co.e (incM F (G p)) := (hΦ _).symm
    rw [this, LinearEquiv.symm_apply_apply]
    refine ⟨incV F p.1, incM F (p.2 : Matrix (Fin n₁) (Fin d) E), ?_, ?_⟩
    · have hz : (Φ₁ (p.2 : Matrix (Fin n₁) (Fin d) E)).1 = 0 := p.2.2
      rw [hΦ₁, hz]; funext i; simp
    · rw [incM_one, Matrix.transpose_one, Matrix.mul_one, ← incM_mul]
      ext i j
      simp only [incM, incV, G, LinearMap.coe_mk, AddHom.coe_mk, Matrix.map_apply, Matrix.add_apply,
        Matrix.vecMulVec_apply, map_add, map_mul]
  have hGinj : ∀ p, G p = 0 → p = 0 := by
    rintro ⟨y, z⟩ h
    change Matrix.vecMulVec H.x y + H.ι * (z : Matrix (Fin n₁) (Fin d) E) = 0 at h
    have hy : y = 0 := by
      funext j
      have hcol : (fun i => (Matrix.vecMulVec H.x y + H.ι * (z : Matrix (Fin n₁) (Fin d) E)) i j) =
          y j • H.x + H.ι *ᵥ (fun k => (z : Matrix (Fin n₁) (Fin d) E) k j) := by
        funext i; simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
      have hj := congrArg (fun A : Fin n → E => form σ X.J A H.y) hcol
      simp only [h, Matrix.zero_apply] at hj
      rw [form_add_left, form_smul_left, hH.xy, (hH.orth _).2, mul_one, add_zero] at hj
      rw [← hj]; simp [form]
    subst hy
    have hιz : H.ι * (z : Matrix (Fin n₁) (Fin d) E) = 0 := by
      ext i j
      have := congrFun (congrFun h i) j
      simpa [Matrix.vecMulVec_apply] using this
    have h1 : H.ι.map σ * (z : Matrix (Fin n₁) (Fin d) E).map σ = 0 := by
      rw [← Matrix.map_mul, hιz]; ext i j; simp
    have h3 : X₁.J * (z : Matrix (Fin n₁) (Fin d) E).map σ = 0 := by
      rw [← hH.gram, Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_zero, Matrix.mul_zero]
    have h4 : (z : Matrix (Fin n₁) (Fin d) E).map σ = 0 := by
      have := congrArg (X₁.J⁻¹ * ·) h3
      simp only [Matrix.mul_zero] at this
      rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mul] at this
    have h5 : (z : Matrix (Fin n₁) (Fin d) E) = 0 := by
      ext i j
      have := congrFun (congrFun h4 i) j
      simpa using this
    exact Prod.ext rfl (Subtype.ext h5)
  let T : (Fin d → E) × LinearMap.ker f₁ →ₗ[F] lagrX M M₁ H := (Φ.toLinearMap.comp G).codRestrict _ hmem
  have hT : Function.Injective T := by
    intro p q hpq
    have hG : G p = G q := Φ.injective (congrArg Subtype.val hpq)
    rw [← sub_eq_zero, ← map_sub] at hG
    exact sub_eq_zero.mp (hGinj _ hG)
  have hle := LinearMap.finrank_le_finrank_of_injective hT
  rw [Module.finrank_prod, hZ, Module.finrank_pi_fintype] at hle
  simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
  calc Fintype.card (Fin n × Fin d) = n * d := by simp
    _ = d * 2 + n₁ * d := by rw [hH.rank]; ring
    _ ≤ _ := hle

end GlobalTheory.MixedLagrX

namespace GlobalTheory.MixedLagrX
open Matrix

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁`. Establish `hiso : ∀ a ∈ lagrX M M₁ H, ∀ b ∈ lagrX M M₁ H, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2`. Introduce `a ha b hb`. Establish `h` using `symp_mixed hH M M₁ ha hb`. Simplify using `only [LinearEquiv.apply_symm_apply, GlobalTheory.MixedLagr.hat] at h`.

Rewrite using `[← sub_eq_zero]`. Apply `AdeleRing.algebraMap_injective (𝓞 F) F` to reduce the goal to its premises. Rewrite using `[map_sub, map_zero, RingHom.map_dotProduct, RingHom.map_dotProduct]`. Conclude with `h`. Use `⟨lagrX M M₁ H, hiso, le_antisymm (GlobalTheory.T.finrank_isotropic_le_card F _ _ hiso) (le_finrank_lagrX F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁), ?_⟩` and prove the remaining obligations.

Introduce `t w hw`. Take `⟨y, z, hz, hm⟩` from `(show IsMixedX M₁ H (M.co.e.symm (GlobalTheory.MixedLagr.hat w)) from hw).smul t`. Use `⟨Matrix.vecMulVec (incV F H.x) y, ⟨y, rfl⟩, z, hz, fun φ => ?_⟩` and prove the remaining obligations. Establish `key : t • GlobalTheory.MixedLagr.hat w = M.co.e (Matrix.vecMulVec (incV F H.x) y + incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ)`. Rewrite using `[← hm, LinearEquiv.map_smul, LinearEquiv.apply_symm_apply]`.

Establish `hu : IsMixedX M₁ H (Matrix.vecMulVec (incV F H.x) y)` using `⟨y, 0, by simp, by simp⟩`. Establish `hv : IsMixedX M₁ H (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ)` using `⟨0, z, hz, by ext i j; simp [Matrix.vecMulVec_apply]⟩`. Establish `h0` using `symp_mixed hH M M₁ hu hv`. Express the relevant statement in the definitionally equal form `schr B.ψ (t • GlobalTheory.MixedLagr.hat w) φ = schr B.ψ (M.co.e _) (schr B.ψ (M.co.e _) φ)`. Rewrite using `[GlobalTheory.MixedLagr.schr_comp, h0, mul_zero, AddChar.map_zero_eq_one, one_smul, ← map_add, key]`.
-/
theorem mixed_lagrangian_plane_X : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∃ L : Submodule F ((Fin n × Fin d → F) × (Fin n × Fin d → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
        Module.finrank F L = Fintype.card (Fin n × Fin d) ∧
        ∀ (t : AF F), ∀ w ∈ L, ∃ u ∈ {u : Matrix (Fin n) (Fin d) (AE F E) | ∃ z, u = Matrix.vecMulVec (incV F H.x) z},
          ∃ z : Matrix (Fin n₁) (Fin d) (AE F E), (M₁.co.e z).1 = 0 ∧ ∀ φ : Fn F n d,
            schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ =
              M.co.rho B.ψ u (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁
  have hiso : ∀ a ∈ lagrX M M₁ H, ∀ b ∈ lagrX M M₁ H, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2 := by
    intro a ha b hb
    have h := symp_mixed hH M M₁ ha hb
    simp only [LinearEquiv.apply_symm_apply, GlobalTheory.MixedLagr.hat] at h
    rw [← sub_eq_zero]
    apply AdeleRing.algebraMap_injective (𝓞 F) F
    rw [map_sub, map_zero, RingHom.map_dotProduct, RingHom.map_dotProduct]
    exact h
  refine ⟨lagrX M M₁ H, hiso, le_antisymm (GlobalTheory.T.finrank_isotropic_le_card F _ _ hiso)
    (le_finrank_lagrX F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁), ?_⟩
  · intro t w hw
    obtain ⟨y, z, hz, hm⟩ := (show IsMixedX M₁ H (M.co.e.symm (GlobalTheory.MixedLagr.hat w)) from hw).smul t
    refine ⟨Matrix.vecMulVec (incV F H.x) y, ⟨y, rfl⟩, z, hz, fun φ => ?_⟩
    have key : t • GlobalTheory.MixedLagr.hat w = M.co.e (Matrix.vecMulVec (incV F H.x) y +
        incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) := by
      rw [← hm, LinearEquiv.map_smul, LinearEquiv.apply_symm_apply]
    have hu : IsMixedX M₁ H (Matrix.vecMulVec (incV F H.x) y) :=
      ⟨y, 0, by simp, by simp⟩
    have hv : IsMixedX M₁ H (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) :=
      ⟨0, z, hz, by ext i j; simp [Matrix.vecMulVec_apply]⟩
    have h0 := symp_mixed hH M M₁ hu hv
    change schr B.ψ (t • GlobalTheory.MixedLagr.hat w) φ = schr B.ψ (M.co.e _) (schr B.ψ (M.co.e _) φ)
    rw [GlobalTheory.MixedLagr.schr_comp, h0, mul_zero, AddChar.map_zero_eq_one, one_smul, ← map_add, key]

end GlobalTheory.MixedLagrX

end
