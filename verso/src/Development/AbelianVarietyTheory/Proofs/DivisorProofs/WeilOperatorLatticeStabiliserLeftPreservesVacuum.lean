import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.VacTransportLeft

section Alg

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type} [Fintype α] [Fintype β]

/- English proof (translation)
Simplify using `only [hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm, Finset.sum_comm (γ := β)]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hTens_eq_left (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    hTens c JA JB x y = ∑ j, ∑ l, JB j l * (xᵀ * JA * y.map c) j l := by
  simp only [hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm, Finset.sum_comm (γ := β)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
Establish `e : (g * x)ᵀ * JA * (g * y).map c = xᵀ * JA * y.map c`. Establish `hm : (g * y).map c = g.map c * y.map c` using `Matrix.map_mul (f := c.toRingHom)`. Rewrite using `[hm, Matrix.transpose_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = _ := by rw [hg]`. Unfold `symp`. Rewrite using `[hTens_eq_left, hTens_eq_left, e]`.
-/
theorem symp_mul_left [DecidableEq α] (ξ : A) (JA : Matrix α α A) (JB : Matrix β β A) (g : Matrix α α A)
    (hg : gᵀ * JA * g.map c = JA) (x y : Matrix α β A) :
    symp c ξ JA JB (g * x) (g * y) = symp c ξ JA JB x y := by
  have e : (g * x)ᵀ * JA * (g * y).map c = xᵀ * JA * y.map c := by
    have hm : (g * y).map c = g.map c * y.map c := Matrix.map_mul (f := c.toRingHom)
    rw [hm, Matrix.transpose_mul]
    calc xᵀ * gᵀ * JA * (g.map c * y.map c) = xᵀ * (gᵀ * JA * g.map c) * y.map c := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg]
  unfold symp
  rw [hTens_eq_left, hTens_eq_left, e]

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Set `f : (Fin n → AE F E) →+ Matrix (Fin n) (Fin d) (AE F E)` to `{ toFun := fun z => Matrix.vecMulVec z (fun i => inclR (F := F) (AF F) (y i)) map_zero' := by ext i j; simp [Matrix.vecMulVec_apply] map_add' := fun z z' => by ext i j; simp [Matrix.vecMulVec_apply, add_mul] }`. Establish `: GlobalTheory.InertSph.latAt X v ≤ (latAtV X W v).comap f`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `z ⟨a, ha, hai, x, hx, rfl⟩`. Use `AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, y, hy, ?_⟩` and prove the remaining obligations.

Use extensionality with `i j`. Simplify using `only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, incM, Matrix.map_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `this hz`.
-/
theorem vecMulVec_mem_left {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl F) {y : Fin d → E} (hy : y ∈ W.L)
    {z : Fin n → AE F E} (hz : z ∈ GlobalTheory.InertSph.latAt X v) :
    Matrix.vecMulVec z (fun i => inclR (F := F) (AF F) (y i)) ∈ latAtV X W v := by
  let f : (Fin n → AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun z => Matrix.vecMulVec z (fun i => inclR (F := F) (AF F) (y i))
      map_zero' := by ext i j; simp [Matrix.vecMulVec_apply]
      map_add' := fun z z' => by ext i j; simp [Matrix.vecMulVec_apply, add_mul] }
  have : GlobalTheory.InertSph.latAt X v ≤ (latAtV X W v).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, x, hx, rfl⟩
    refine AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, y, hy, ?_⟩
    ext i j
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, incM,
      Matrix.map_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]
    ring
  exact this hz

/- English proof (translation)
Set `f : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d) (AE F E)` to `{ toFun := fun γ => mat k⁻¹ * γ map_zero' := by simp map_add' := fun γ γ' => by simp [Matrix.mul_add] }`. Establish `: latAtV X W v ≤ (latAtV X W v).comap f`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `z ⟨a, ha, hai, x, hx, y, hy, rfl⟩`. Use `show mat k⁻¹ * (a • incM F (Matrix.vecMulVec x y)) ∈ latAtV X W v`.

Establish `hz : (a • fun i => inclR (F` using `F) (AF F) (x i)) ∈ GlobalTheory.InertSph.latAt X v := AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, rfl⟩`. Establish `e : mat k⁻¹ * (a • incM F (Matrix.vecMulVec x y)) = Matrix.vecMulVec (mat k⁻¹ *ᵥ (a • fun i => inclR (F` using `F) (AF F) (x i))) (fun j => inclR (F := F) (AF F) (y j)) := by`. Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, incM, Matrix.map_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `vecMulVec_mem_left X W v hy (hk.2 _ hz).2`. Conclude with `this hγ`.
-/
theorem inv_mul_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl F) {k : UA σ X.J}
    (hk : k ∈ GlobalTheory.InertSph.KAt σ X v) {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    mat k⁻¹ * γ ∈ latAtV X W v := by
  let f : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun γ => mat k⁻¹ * γ
      map_zero' := by simp
      map_add' := fun γ γ' => by simp [Matrix.mul_add] }
  have : latAtV X W v ≤ (latAtV X W v).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    show mat k⁻¹ * (a • incM F (Matrix.vecMulVec x y)) ∈ latAtV X W v
    have hz : (a • fun i => inclR (F := F) (AF F) (x i)) ∈ GlobalTheory.InertSph.latAt X v :=
      AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, rfl⟩
    have e : mat k⁻¹ * (a • incM F (Matrix.vecMulVec x y)) =
        Matrix.vecMulVec (mat k⁻¹ *ᵥ (a • fun i => inclR (F := F) (AF F) (x i)))
          (fun j => inclR (F := F) (AF F) (y j)) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Matrix.mulVec,
        dotProduct, Pi.smul_apply, incM, Matrix.map_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e]
    exact vecMulVec_mem_left X W v hy (hk.2 _ hz).2
  exact this hγ

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hT v k hk θ _ φ hφ φ₁ _ hfix hact γ hγ r hr`. Establish `etens : ∀ (c : ℂ) (f : (Fin a × Fin (a + a') → Fv F v) → ℂ), tens (evFin F v) (c • f) r = c • tens (evFin F v) f r` using `fun c f => by`. Use function extensionality and compare the values at `x`. Simplify using `only [tens, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Distinguish the cases in `h0 : φ₁ = 0`. Substitute `h0` using the available equality. Use function extensionality and compare the values at `x`. Simplify using `[Darboux.rho, schr, tens]`. Establish `hr' : Rest (evFin F v) φ r` using `GlobalTheory.RestCofactor.rest_of_rest v φ₁ φ r h0 hφ hr`.

Establish `hS` using `IsUWeilPair.isUSplitting hT.weil`. Establish `hγ' : mat k⁻¹ * γ ∈ latAtV G.V G.W v` using `inv_mul_mem G.V G.W v hk hγ`. Establish `hback : actAB (cA σ) (k, (1 : UA σ G.W.J)) (mat k⁻¹ * γ) = γ`. Express the relevant statement in the definitionally equal form `mat k * (mat k⁻¹ * γ) * (1 : Matrix _ _ _)ᵀ = γ`. Establish `e : mat k * mat k⁻¹ = 1` using `Units.mul_inv k.1`.

Rewrite using `[Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, e, Matrix.one_mul]`. Establish `hsy` using `symp_mul_left (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) (mat k⁻¹) (k⁻¹).2 γ γ`. Establish `h1` using `hS.impl (k, 1) (mat k⁻¹ * γ) _ hr'.2`. Rewrite `h1` using `[hback, hfix _ hγ' r hr', hsy, etens, map_smul, hact r hr']`. Rewrite using `[← h1, etens]`.
-/
theorem transport_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ)) → Acts (evFin F v) (om (k, 1)) φ φ₁ →
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ₁
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v k hk θ _ φ hφ φ₁ _ hfix hact γ hγ r hr
  have etens : ∀ (c : ℂ) (f : (Fin a × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • f) r = c • tens (evFin F v) f r := fun c f => by
    funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring
  by_cases h0 : φ₁ = 0
  · subst h0
    funext x
    simp [Darboux.rho, schr, tens]
  have hr' : Rest (evFin F v) φ r := GlobalTheory.RestCofactor.rest_of_rest v φ₁ φ r h0 hφ hr
  have hS := IsUWeilPair.isUSplitting hT.weil
  have hγ' : mat k⁻¹ * γ ∈ latAtV G.V G.W v := inv_mul_mem G.V G.W v hk hγ
  have hback : actAB (cA σ) (k, (1 : UA σ G.W.J)) (mat k⁻¹ * γ) = γ := by
    change mat k * (mat k⁻¹ * γ) * (1 : Matrix _ _ _)ᵀ = γ
    have e : mat k * mat k⁻¹ = 1 := Units.mul_inv k.1
    rw [Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, e, Matrix.one_mul]
  have hsy := symp_mul_left (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) (mat k⁻¹)
    (k⁻¹).2 γ γ
  have h1 := hS.impl (k, 1) (mat k⁻¹ * γ) _ hr'.2
  rw [hback, hfix _ hγ' r hr', hsy, etens, map_smul, hact r hr'] at h1
  rw [← h1, etens]

end GlobalTheory.VacTransportLeft

end
