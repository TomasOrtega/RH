import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorLatticeStabiliserRightPreservesVacuu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorLatticeStabiliserLeftPreservesVacuum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacTransport

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Set `T₁ : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) →+ Matrix (Fin n) (Fin d) (AE F E)` to `{ toFun := fun γ => ((γ * hᵀ).toCols₁)ᵀ map_zero' := by ext i j; simp [Matrix.toCols₁] map_add' := fun γ γ' => by ext i j; simp [Matrix.toCols₁, Matrix.add_mul] }`. Set `T₂ : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) →+ Matrix (Fin n) (Fin d) (AE F E)` to `{ toFun := fun γ => ((γ * hᵀ).toCols₂)ᵀ map_zero' := by ext i j; simp [Matrix.toCols₂] map_add' := fun γ γ' => by ext i j; simp [Matrix.toCols₂, Matrix.add_mul] }`. Set `S` to `(latAtV X Y v).comap T₁ ⊓ (latAtV X Y v).comap T₂`. Establish `key : ∀ y ∈ Y.L, ∀ z ∈ GlobalTheory.DblVac.latD X v, Matrix.vecMulVec (fun i => inclR (F` using `F) (AF F) (y i)) z ∈ S := by`. Introduce `y hy z hz`.

Establish `hz'` using `hh z hz`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show ((Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z * hᵀ).toCols₁)ᵀ ∈ latAtV X Y v`. Establish `e : ((Matrix.vecMulVec (fun i => inclR (F` using `F) (AF F) (y i)) z * hᵀ).toCols₁)ᵀ = Matrix.vecMulVec ((h *ᵥ z) ∘ Sum.inl) (fun i => inclR (F := F) (AF F) (y i)) := by`. Rewrite using `[Matrix.vecMulVec_mul, Matrix.vecMul_transpose]`.

Use extensionality with `i j`. Simplify using `[Matrix.toCols₁, Matrix.vecMulVec_apply, mul_comm]`. Rewrite using `[e]`. Conclude with `GlobalTheory.VacTransportLeft.vecMulVec_mem_left X Y v hy hz'.1`. Use `show ((Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z * hᵀ).toCols₂)ᵀ ∈ latAtV X Y v`.

Establish `e : ((Matrix.vecMulVec (fun i => inclR (F` using `F) (AF F) (y i)) z * hᵀ).toCols₂)ᵀ = Matrix.vecMulVec ((h *ᵥ z) ∘ Sum.inr) (fun i => inclR (F := F) (AF F) (y i)) := by`. Rewrite using `[Matrix.vecMulVec_mul, Matrix.vecMul_transpose]`. Use extensionality with `i j`. Simplify using `[Matrix.toCols₂, Matrix.vecMulVec_apply, mul_comm]`. Rewrite using `[e]`.

Conclude with `GlobalTheory.VacTransportLeft.vecMulVec_mem_left X Y v hy hz'.2`. Apply the tactic sequence `let A₁ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) := { toFun := fun w => Matrix.fromCols wᵀ 0 map_zero' := by ext i j; cases j <;> simp map_add' := fun w w' => by ext i j; cases j <;> simp }`. Apply the tactic sequence `let A₂ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) := { toFun := fun w => Matrix.fromCols 0 wᵀ map_zero' := by ext i j; cases j <;> simp map_add' := fun w w' => by ext i j; cases j <;> simp }`. Establish `hA₁ : latAtV X Y v ≤ S.comap A₁`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, ha, hai, x, hx, y, hy, rfl⟩`. Establish `e : A₁ (a • incM F (Matrix.vecMulVec x y)) = Matrix.vecMulVec (fun i => inclR (F` using `F) (AF F) (y i)) (Sum.elim (a • fun i => inclR (F := F) (AF F) (x i)) 0) := by`. Use extensionality with `i j`. Consider the cases of `j with`. Consider the case `inl j`.

Simplify using `only [A₁, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.fromCols_apply_inl, Matrix.transpose_apply, Matrix.smul_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply, Sum.elim_inl, Pi.smul_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `inr j => simp [A₁, Matrix.vecMulVec_apply]`. Use `show A₁ _ ∈ S`. Rewrite using `[e]`.

Use `key y hy _ ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Sum.elim_comp_inl]`. Conclude with `AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, rfl⟩`. Rewrite using `[Sum.elim_comp_inr]`. Conclude with `zero_mem _`.

Establish `hA₂ : latAtV X Y v ≤ S.comap A₂`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, hai, x, hx, y, hy, rfl⟩`. Establish `e : A₂ (a • incM F (Matrix.vecMulVec x y)) = Matrix.vecMulVec (fun i => inclR (F` using `F) (AF F) (y i)) (Sum.elim 0 (a • fun i => inclR (F := F) (AF F) (x i))) := by`. Use extensionality with `i j`.

Consider the cases of `j with`. Consider the case `inl j => simp [A₂, Matrix.vecMulVec_apply]`. Consider the case `inr j`. Simplify using `only [A₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.fromCols_apply_inr, Matrix.transpose_apply, Matrix.smul_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply, Sum.elim_inr, Pi.smul_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]`. Expand and normalize the polynomial expressions, which then agree.

Use `show A₂ _ ∈ S`. Rewrite using `[e]`. Use `key y hy _ ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Sum.elim_comp_inl]`. Conclude with `zero_mem _`.

Rewrite using `[Sum.elim_comp_inr]`. Conclude with `AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, rfl⟩`. Establish `hsum : Matrix.fromCols w₁ᵀ w₂ᵀ = A₁ w₁ + A₂ w₂`. Apply the tactic sequence `ext i j; cases j <;> simp [A₁, A₂]`. Establish `hm : Matrix.fromCols w₁ᵀ w₂ᵀ ∈ S` using `hsum ▸ add_mem (hA₁ hw₁) (hA₂ hw₂)`.

Conclude with `⟨hm.1, hm.2⟩`.
-/
theorem cols_mem {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl F)
    (h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))
    (hh : ∀ z ∈ GlobalTheory.DblVac.latD X v, h *ᵥ z ∈ GlobalTheory.DblVac.latD X v)
    {w₁ w₂ : Matrix (Fin n) (Fin d) (AE F E)} (hw₁ : w₁ ∈ latAtV X Y v) (hw₂ : w₂ ∈ latAtV X Y v) :
    ((Matrix.fromCols w₁ᵀ w₂ᵀ * hᵀ).toCols₁)ᵀ ∈ latAtV X Y v ∧
      ((Matrix.fromCols w₁ᵀ w₂ᵀ * hᵀ).toCols₂)ᵀ ∈ latAtV X Y v := by
  let T₁ : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun γ => ((γ * hᵀ).toCols₁)ᵀ
      map_zero' := by ext i j; simp [Matrix.toCols₁]
      map_add' := fun γ γ' => by ext i j; simp [Matrix.toCols₁, Matrix.add_mul] }
  let T₂ : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun γ => ((γ * hᵀ).toCols₂)ᵀ
      map_zero' := by ext i j; simp [Matrix.toCols₂]
      map_add' := fun γ γ' => by ext i j; simp [Matrix.toCols₂, Matrix.add_mul] }
  let S := (latAtV X Y v).comap T₁ ⊓ (latAtV X Y v).comap T₂
  have key : ∀ y ∈ Y.L, ∀ z ∈ GlobalTheory.DblVac.latD X v,
      Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z ∈ S := by
    intro y hy z hz
    have hz' := hh z hz
    refine ⟨?_, ?_⟩
    · show ((Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z * hᵀ).toCols₁)ᵀ ∈ latAtV X Y v
      have e : ((Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z * hᵀ).toCols₁)ᵀ =
          Matrix.vecMulVec ((h *ᵥ z) ∘ Sum.inl) (fun i => inclR (F := F) (AF F) (y i)) := by
        rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
        ext i j
        simp [Matrix.toCols₁, Matrix.vecMulVec_apply, mul_comm]
      rw [e]
      exact GlobalTheory.VacTransportLeft.vecMulVec_mem_left X Y v hy hz'.1
    · show ((Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z * hᵀ).toCols₂)ᵀ ∈ latAtV X Y v
      have e : ((Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z * hᵀ).toCols₂)ᵀ =
          Matrix.vecMulVec ((h *ᵥ z) ∘ Sum.inr) (fun i => inclR (F := F) (AF F) (y i)) := by
        rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
        ext i j
        simp [Matrix.toCols₂, Matrix.vecMulVec_apply, mul_comm]
      rw [e]
      exact GlobalTheory.VacTransportLeft.vecMulVec_mem_left X Y v hy hz'.2
  let A₁ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) :=
    { toFun := fun w => Matrix.fromCols wᵀ 0
      map_zero' := by ext i j; cases j <;> simp
      map_add' := fun w w' => by ext i j; cases j <;> simp }
  let A₂ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) :=
    { toFun := fun w => Matrix.fromCols 0 wᵀ
      map_zero' := by ext i j; cases j <;> simp
      map_add' := fun w w' => by ext i j; cases j <;> simp }
  have hA₁ : latAtV X Y v ≤ S.comap A₁ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    have e : A₁ (a • incM F (Matrix.vecMulVec x y)) = Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i))
        (Sum.elim (a • fun i => inclR (F := F) (AF F) (x i)) 0) := by
      ext i j
      cases j with
      | inl j =>
        simp only [A₁, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.fromCols_apply_inl, Matrix.transpose_apply,
          Matrix.smul_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply, Sum.elim_inl, Pi.smul_apply, map_mul,
          Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]
        ring
      | inr j => simp [A₁, Matrix.vecMulVec_apply]
    show A₁ _ ∈ S
    rw [e]
    refine key y hy _ ⟨?_, ?_⟩
    · rw [Sum.elim_comp_inl]; exact AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, rfl⟩
    · rw [Sum.elim_comp_inr]; exact zero_mem _
  have hA₂ : latAtV X Y v ≤ S.comap A₂ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    have e : A₂ (a • incM F (Matrix.vecMulVec x y)) = Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i))
        (Sum.elim 0 (a • fun i => inclR (F := F) (AF F) (x i))) := by
      ext i j
      cases j with
      | inl j => simp [A₂, Matrix.vecMulVec_apply]
      | inr j =>
        simp only [A₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.fromCols_apply_inr, Matrix.transpose_apply,
          Matrix.smul_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply, Sum.elim_inr, Pi.smul_apply, map_mul,
          Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]
        ring
    show A₂ _ ∈ S
    rw [e]
    refine key y hy _ ⟨?_, ?_⟩
    · rw [Sum.elim_comp_inl]; exact zero_mem _
    · rw [Sum.elim_comp_inr]; exact AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, rfl⟩
  have hsum : Matrix.fromCols w₁ᵀ w₂ᵀ = A₁ w₁ + A₂ w₂ := by
    ext i j; cases j <;> simp [A₁, A₂]
  have hm : Matrix.fromCols w₁ᵀ w₂ᵀ ∈ S := hsum ▸ add_mem (hA₁ hw₁) (hA₂ hw₂)
  exact ⟨hm.1, hm.2⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' _ v w _ _ d' _ dd _ θ _ _ omd hsp g hg φ hφ φ₁ _ hfix hact w₁ hw₁ w₂ hw₂ r hr`. Distinguish the cases in `h0 : φ₁ = 0`. Substitute `h0` using the available equality. Use function extensionality and compare the values at `x`. Simplify using `[Darboux.rho, schr, tens]`.

Establish `hr' : Rest (evFin F v) φ r` using `GlobalTheory.RestCofactor.rest_of_rest v φ₁ φ r h0 hφ hr`. Take `⟨h1m, h2m⟩` from `cols_mem G.V G.W v (GlobalTheory.DblVac.matD g⁻¹) (fun z hz => (hg.2 z hz).2) hw₁ hw₂`. Establish `hsplit : Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ = Matrix.fromCols (((Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ).toCols₁)ᵀ)ᵀ (((Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ).toCols₂)ᵀ)ᵀ`. Rewrite using `[Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.fromCols_toCols]`. Establish `hback : actB (cA σ) g (Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) = Matrix.fromCols w₁ᵀ w₂ᵀ`.

Express the relevant statement in the definitionally equal form `Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ * (GlobalTheory.DblVac.matD g)ᵀ = _`. Establish `e : GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD g⁻¹ = 1` using `Units.mul_inv g.1`. Rewrite using `[Matrix.mul_assoc, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.mul_one]`. Establish `hsy` using `GlobalTheory.VacTransport.symp_mul_transpose (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.W.J) (dbl (incM F G.V.J)) (GlobalTheory.DblVac.matD g⁻¹) (g⁻¹).2 (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)`. Establish `hf` using `hfix _ h1m _ h2m r hr'`.

Rewrite `hf` using `[← hsplit, hsy]`. Establish `h1` using `hsp.2.1.impl g (Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) _ hr'.2`. Rewrite `h1` using `[hback, hf, GlobalTheory.VacTransport.tens_smul, map_smul, hact r hr']`. Rewrite using `[← h1, GlobalTheory.VacTransport.tens_smul]`.
-/
theorem transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • G.M.vac v)) →
    ∀ (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, ∀ φ ∈ SB ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v), ∀ φ₁ ∈ SB ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v),
    (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.W.J) (dbl (incM F G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ)) → Acts (evFin F v) (omd g) φ φ₁ →
    (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ₁
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.W.J) (dbl (incM F G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' _ v w _ _ d' _ dd _ θ _ _ omd hsp g hg φ hφ φ₁ _ hfix hact w₁ hw₁ w₂ hw₂ r hr
  by_cases h0 : φ₁ = 0
  · subst h0
    funext x
    simp [Darboux.rho, schr, tens]
  have hr' : Rest (evFin F v) φ r := GlobalTheory.RestCofactor.rest_of_rest v φ₁ φ r h0 hφ hr
  obtain ⟨h1m, h2m⟩ := cols_mem G.V G.W v (GlobalTheory.DblVac.matD g⁻¹) (fun z hz => (hg.2 z hz).2) hw₁ hw₂
  have hsplit : Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ =
      Matrix.fromCols (((Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ).toCols₁)ᵀ)ᵀ
        (((Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ).toCols₂)ᵀ)ᵀ := by
    rw [Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.fromCols_toCols]
  have hback : actB (cA σ) g (Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) = Matrix.fromCols w₁ᵀ w₂ᵀ := by
    change Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ * (GlobalTheory.DblVac.matD g)ᵀ = _
    have e : GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD g⁻¹ = 1 := Units.mul_inv g.1
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.mul_one]
  have hsy := GlobalTheory.VacTransport.symp_mul_transpose (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.W.J)
    (dbl (incM F G.V.J)) (GlobalTheory.DblVac.matD g⁻¹) (g⁻¹).2 (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)
  have hf := hfix _ h1m _ h2m r hr'
  rw [← hsplit, hsy] at hf
  have h1 := hsp.2.1.impl g (Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) _ hr'.2
  rw [hback, hf, GlobalTheory.VacTransport.tens_smul, map_smul, hact r hr'] at h1
  rw [← h1, GlobalTheory.VacTransport.tens_smul]

end GlobalTheory.DblVacTransport

end
