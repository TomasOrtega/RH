import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.VacTransport

section Alg

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
/- English proof (translation)
Unfold `hTens`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hTens_eq (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * (x * JB * (y.map c)ᵀ) i k := by
  unfold hTens
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

omit [DecidableEq α] [DecidableEq β] in

/- English proof (translation)
Unfold `symp`. Rewrite using `[hTens_eq, hTens_eq]`. Establish `e : (y * hᵀ).map c = y.map c * (hᵀ).map c` using `Matrix.map_mul (f := c.toRingHom)`. Establish `e2 : x * hᵀ * JB * ((y * hᵀ).map c)ᵀ = x * JB * (y.map c)ᵀ`. Rewrite using `[e, Matrix.transpose_mul, ← Matrix.transpose_map, Matrix.transpose_transpose]`.

Use `conv_rhs => rw [← hh]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e2]`.
-/
theorem symp_mul_transpose (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (h : Matrix β β E)
    (hh : hᵀ * JB * h.map c = JB) (x y : Matrix α β E) :
    symp (R := R) c ξ JA JB (x * hᵀ) (y * hᵀ) = symp (R := R) c ξ JA JB x y := by
  unfold symp
  rw [hTens_eq, hTens_eq]
  have e : (y * hᵀ).map c = y.map c * (hᵀ).map c := Matrix.map_mul (f := c.toRingHom)
  have e2 : x * hᵀ * JB * ((y * hᵀ).map c)ᵀ = x * JB * (y.map c)ᵀ := by
    rw [e, Matrix.transpose_mul, ← Matrix.transpose_map, Matrix.transpose_transpose]
    conv_rhs => rw [← hh]
    simp only [Matrix.mul_assoc]
  rw [e2]

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, hv, y, hy, rfl⟩` from `hz`. Use `AddSubgroup.subset_closure ⟨a, ha, hv, x, hx, y, hy, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Simplify using `[Matrix.vecMulVec_apply, incM]`. Consider the case `zero`. Establish `e : Matrix.vecMulVec (fun i => inclR (F` using `F) (AF F) (x i)) (0 : Fin d → AE F E) = 0 := by`. Use extensionality with `i j`. Simplify using `[Matrix.vecMulVec_apply]`.

Rewrite using `[e]`. Conclude with `zero_mem _`. Consider the case `add z z' _ _ h h' => rw [Matrix.vecMulVec_add]`. Conclude with `add_mem h h'`. Consider the case `neg z _ h => rw [Matrix.vecMulVec_neg]`.

Conclude with `neg_mem h`.
-/
theorem vecMulVec_mem {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl F) {x : Fin n → E} (hx : x ∈ X.L)
    {z : Fin d → AE F E} (hz : z ∈ GlobalTheory.InertSph.latAt Y v) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) z ∈ latAtV X Y v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hv, x, hx, y, hy, ?_⟩
    ext i j
    simp [Matrix.vecMulVec_apply, incM]
  | zero =>
    have e : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (0 : Fin d → AE F E) = 0 := by
      ext i j
      simp [Matrix.vecMulVec_apply]
    rw [e]; exact zero_mem _
  | add z z' _ _ h h' => rw [Matrix.vecMulVec_add]; exact add_mem h h'
  | neg z _ h => rw [Matrix.vecMulVec_neg]; exact neg_mem h

/- English proof (translation)
Proceed by induction on `hγ using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, hv, x, hx, y, hy, rfl⟩` from `hz`. Establish `hm : (a • fun i => inclR (F` using `F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt Y v := AddSubgroup.subset_closure ⟨a, ha, hv, y, hy, rfl⟩`. Establish `e : a • incM F (Matrix.vecMulVec x y) = Matrix.vecMulVec (fun i => inclR (F` using `F) (AF F) (x i)) (a • fun i => inclR (F := F) (AF F) (y i)) := by`.

Use extensionality with `i j`. Simplify using `[Matrix.vecMulVec_apply, incM]`. Rewrite using `[e, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]`. Conclude with `vecMulVec_mem X Y v hx (hh _ hm)`. Consider the case `zero => rw [Matrix.zero_mul]`.

Conclude with `zero_mem _`. Consider the case `add z z' _ _ h h' => rw [Matrix.add_mul]`. Conclude with `add_mem h h'`. Consider the case `neg z _ h => rw [Matrix.neg_mul]`. Conclude with `neg_mem h`.
-/
theorem mul_transpose_mem {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl F) (h : Matrix (Fin d) (Fin d) (AE F E))
    (hh : ∀ z ∈ GlobalTheory.InertSph.latAt Y v, h *ᵥ z ∈ GlobalTheory.InertSph.latAt Y v)
    {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X Y v) : γ * hᵀ ∈ latAtV X Y v := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, x, hx, y, hy, rfl⟩ := hz
    have hm : (a • fun i => inclR (F := F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt Y v :=
      AddSubgroup.subset_closure ⟨a, ha, hv, y, hy, rfl⟩
    have e : a • incM F (Matrix.vecMulVec x y) =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (a • fun i => inclR (F := F) (AF F) (y i)) := by
      ext i j
      simp [Matrix.vecMulVec_apply, incM]
    rw [e, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
    exact vecMulVec_mem X Y v hx (hh _ hm)
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add z z' _ _ h h' => rw [Matrix.add_mul]; exact add_mem h h'
  | neg z _ h => rw [Matrix.neg_mul]; exact neg_mem h

omit [NumberField E] in
/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]`.
-/
theorem tens_smul {R κ : Type} (ev : AF F → R) (c : ℂ) (φ : (κ → R) → ℂ) (r : (κ → AF F) → ℂ) :
    tens ev (c • φ) r = c • tens ev φ r := by
  funext x
  simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hT v k hk θ _ φ hφ φ₁ _ hfix hact γ hγ r hr`. Distinguish the cases in `h0 : φ₁ = 0`. Substitute `h0` using the available equality. Use function extensionality and compare the values at `x`. Simplify using `[Darboux.rho, schr, tens]`.

Establish `hr' : Rest (evFin F v) φ r` using `GlobalTheory.RestCofactor.rest_of_rest v φ₁ φ r h0 hφ hr`. Establish `hS` using `IsUWeilPair.isUSplitting hT.weil`. Establish `hγ' : γ * (mat k⁻¹)ᵀ ∈ latAtV G.V G.W v` using `mul_transpose_mem G.V G.W v _ (fun z hz => (hk.2 z hz).2) hγ`. Establish `hback : actAB (cA σ) ((1 : UA σ G.V.J), k) (γ * (mat k⁻¹)ᵀ) = γ`. Express the relevant statement in the definitionally equal form `(1 : Matrix _ _ _) * (γ * (mat k⁻¹)ᵀ) * (mat k)ᵀ = γ`.

Establish `e : mat k * mat k⁻¹ = 1` using `Units.mul_inv k.1`. Rewrite using `[Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.mul_one]`. Establish `hsy` using `symp_mul_transpose (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) (mat k⁻¹) (k⁻¹).2 γ γ`. Establish `h1` using `hS.impl (1, k) (γ * (mat k⁻¹)ᵀ) _ hr'.2`. Rewrite `h1` using `[hback, hfix _ hγ' r hr', hsy, tens_smul, map_smul, hact r hr']`.

Rewrite using `[← h1, tens_smul]`.
-/
theorem transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ)) → Acts (evFin F v) (om (1, k)) φ φ₁ →
      (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) φ₁
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v k hk θ _ φ hφ φ₁ _ hfix hact γ hγ r hr
  by_cases h0 : φ₁ = 0
  · subst h0
    funext x
    simp [Darboux.rho, schr, tens]
  have hr' : Rest (evFin F v) φ r := GlobalTheory.RestCofactor.rest_of_rest v φ₁ φ r h0 hφ hr
  have hS := IsUWeilPair.isUSplitting hT.weil
  have hγ' : γ * (mat k⁻¹)ᵀ ∈ latAtV G.V G.W v := mul_transpose_mem G.V G.W v _ (fun z hz => (hk.2 z hz).2) hγ
  have hback : actAB (cA σ) ((1 : UA σ G.V.J), k) (γ * (mat k⁻¹)ᵀ) = γ := by
    change (1 : Matrix _ _ _) * (γ * (mat k⁻¹)ᵀ) * (mat k)ᵀ = γ
    have e : mat k * mat k⁻¹ = 1 := Units.mul_inv k.1
    rw [Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.mul_one]
  have hsy := symp_mul_transpose (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) (mat k⁻¹)
    (k⁻¹).2 γ γ
  have h1 := hS.impl (1, k) (γ * (mat k⁻¹)ᵀ) _ hr'.2
  rw [hback, hfix _ hγ' r hr', hsy, tens_smul, map_smul, hact r hr'] at h1
  rw [← h1, tens_smul]

end GlobalTheory.VacTransport

end
