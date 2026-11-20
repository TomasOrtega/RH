import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTransposeInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormRestrictedPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLagrangianSubspaceExists

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.MixedLagr GlobalTheory.MixedLagrGram

noncomputable section

namespace GlobalTheory.MixedLagrX

/- English proof (translation)
Rewrite using `[hTens_eq_trace, Matrix.transpose_mul, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem hTens_mul {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
    {α β γ γ' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [Fintype γ']
    (JA : Matrix α α E) (JB : Matrix β β E) (ι : Matrix α γ E) (ι' : Matrix α γ' E) (z : Matrix γ β E)
    (z' : Matrix γ' β E) :
    hTens c JA JB (ι * z) (ι' * z') = Matrix.trace (zᵀ * (ιᵀ * JA * ι'.map c) * z'.map c * JBᵀ) := by
  rw [hTens_eq_trace, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Rewrite using `[incM_map_cA]`. Simplify using `only [incM, Matrix.map_mul, Matrix.transpose_map]`.
-/
theorem incM_gram {α γ γ' : Type} [Fintype α] (J : Matrix α α E) (ι : Matrix α γ E) (ι' : Matrix α γ' E) :
    (incM F ι)ᵀ * incM F J * (incM F ι').map (cA σ) = incM F (ιᵀ * J * ι'.map σ) := by
  rw [incM_map_cA]
  simp only [incM, Matrix.map_mul, Matrix.transpose_map]

/- English proof (translation)
The claim follows from `Matrix.map_zero _ (map_zero _)`.
-/
theorem incM_zero {α β : Type} : incM F (0 : Matrix α β E) = 0 := Matrix.map_zero _ (map_zero _)

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Simplify using `only [form, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Conclude with `Finset.sum_comm`.
-/
theorem gram_apply {k : ℕ} {γ γ' : Type} (J : Matrix (Fin k) (Fin k) E) (P : Matrix (Fin k) γ E) (Q : Matrix (Fin k) γ' E)
    (a : γ) (b : γ') : (Pᵀ * J * Q.map σ) a b = form σ J (fun r => P r a) (fun r => Q r b) := by
  simp only [form, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/- English proof (translation)
The claim follows from `Matrix.vecMulVec_eq Unit _ _`.
-/
theorem vecMulVec_incV {n d : ℕ} (x : Fin n → E) (a : Fin d → AE F E) :
    Matrix.vecMulVec (incV F x) a = incM F (Matrix.replicateCol Unit x) * Matrix.replicateRow Unit a :=
  Matrix.vecMulVec_eq Unit _ _

/- English proof (translation)
Introduce `hJ`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Take `⟨hrs, A, hA⟩` from `h.sig w`. Establish `hM : (X.J.map (B.emb w).1).det = 0`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det, hJ, map_zero]`.

Set `e : Fin r ⊕ Fin s ≃ Fin n` to `finSumFinEquiv.trans (finCongr hrs)`. Set `P : Matrix (Fin n) (Fin n) ℂ` to `A.submatrix id e.symm`. Establish `key : Pᵀ * (X.J.map (B.emb w).1) * P.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).submatrix e.symm e.symm`. Rewrite using `[← hA]`. Both sides reduce to the same expression.

Establish `hd` using `congrArg Matrix.det key`. Rewrite `hd` using `[Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul, hM]`. Rewrite `hd` using `[Matrix.det_neg, Matrix.det_one, Matrix.det_one, mul_one, one_mul, mul_zero, zero_mul]`. Conclude with `(pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hd.symm`.
-/
theorem herm_det_ne_zero {B : Base F E} {n : ℕ} {X : Spc F E n} {r s : ℕ} (h : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  intro hJ
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨hrs, A, hA⟩ := h.sig w
  have hM : (X.J.map (B.emb w).1).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hJ, map_zero]
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let P : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : Pᵀ * (X.J.map (B.emb w).1) * P.map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).submatrix e.symm e.symm := by
    rw [← hA]; rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul, hM] at hd
  rw [Matrix.det_neg, Matrix.det_one, Matrix.det_one, mul_one, one_mul, mul_zero, zero_mul] at hd
  exact (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hd.symm

/- English proof (translation)
Introduce `a b h`. Use `Prod.ext (funext fun i => ?_) (funext fun i => ?_)` and prove the remaining obligations. Conclude with `AdeleRing.algebraMap_injective (𝓞 F) F (congrFun (congrArg Prod.fst h) i)`. Conclude with `AdeleRing.algebraMap_injective (𝓞 F) F (congrFun (congrArg Prod.snd h) i)`.
-/
theorem hat_injective {κ : Type} : Function.Injective (hat (F := F) (κ := κ)) := by
  intro a b h
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact AdeleRing.algebraMap_injective (𝓞 F) F (congrFun (congrArg Prod.fst h) i)
  · exact AdeleRing.algebraMap_injective (𝓞 F) F (congrFun (congrArg Prod.snd h) i)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [incM, Matrix.map_apply, Matrix.smul_apply, algebraMap_smul]`. Conclude with `TensorProduct.tmul_smul c (1 : AF F) (x i j)`.
-/
theorem incM_smul {α β : Type} (c : F) (x : Matrix α β E) : incM F (c • x) = algebraMap F (AF F) c • incM F x := by
  ext i j
  simp only [incM, Matrix.map_apply, Matrix.smul_apply, algebraMap_smul]
  exact TensorProduct.tmul_smul c (1 : AF F) (x i j)

/- English proof (translation)
Introduce `x y h`. Use extensionality with `i j`. Conclude with `Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F) (congrFun (congrFun h i) j)`.
-/
theorem incM_injective {α β : Type} : Function.Injective (incM F : Matrix α β E → _) := by
  intro x y h
  ext i j
  exact Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F) (congrFun (congrFun h i) j)

/- English proof (translation)
Use `choose y z h using h`. Establish `h' : ∀ x, hat (y x, z x) = M.co.e (incM F x)` using `fun x => (h x).symm`. Use `⟨⟨⟨fun x => (y x, z x), fun a b => hat_injective ?_⟩, fun c a => hat_injective ?_⟩, fun a b hab => ?_, h'⟩` and prove the remaining obligations. Rewrite using `[hat_add, h', h', h', ← map_add]`. Use `congr 1`.

Conclude with `Matrix.map_add _ (map_add _) _ _`. Rewrite using `[RingHom.id_apply, hat_smul, h', h', incM_smul, LinearEquiv.map_smul]`. Apply `incM_injective (F := F)` to reduce the goal to its premises. Apply `M.co.e.injective` to reduce the goal to its premises. Rewrite using `[← h', ← h']`.

Conclude with `congrArg hat hab`.
-/
theorem exists_ratMap {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W)
    (h : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      M.co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∃ f : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F),
      Function.Injective f ∧ ∀ x, hat (f x) = M.co.e (incM F x) := by
  choose y z h using h
  have h' : ∀ x, hat (y x, z x) = M.co.e (incM F x) := fun x => (h x).symm
  refine ⟨⟨⟨fun x => (y x, z x), fun a b => hat_injective ?_⟩, fun c a => hat_injective ?_⟩, fun a b hab => ?_, h'⟩
  · rw [hat_add, h', h', h', ← map_add]
    congr 1
    exact Matrix.map_add _ (map_add _) _ _
  · rw [RingHom.id_apply, hat_smul, h', h', incM_smul, LinearEquiv.map_smul]
  · apply incM_injective (F := F)
    apply M.co.e.injective
    rw [← h', ← h']
    exact congrArg hat hab

/- English proof (translation)
Establish `hD : ∀ p q, symp (cA σ) (-1) (incM F X.J) (incM F W.J) p q = (M.co.e p).1 ⬝ᵥ (M.co.e q).2 - (M.co.e q).1 ⬝ᵥ (M.co.e p).2` using `M.co.form`. Establish `gxx : (Matrix.replicateCol Unit H.x)ᵀ * X.J * (Matrix.replicateCol Unit H.x).map σ = 0`. Use extensionality with `i j`. Rewrite using `[gram_apply]`. Conclude with `hH.xx`.

Establish `gιx : H.ιᵀ * X.J * (Matrix.replicateCol Unit H.x).map σ = 0`. Use extensionality with `i j`. Rewrite using `[gram_apply]`. Use `(hH.orth (Pi.single i 1)).1` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_single_one]`.

Conclude with `this`. Establish `h1 : symp (cA σ) (-1) (incM F X.J) (incM F W.J) (Matrix.vecMulVec (incV F H.x) a) (Matrix.vecMulVec (incV F H.x) a') = 0`. Rewrite using `[symp, vecMulVec_incV, vecMulVec_incV, hTens_mul, incM_gram, gxx, incM_zero]`. Simplify using the standard rewrite rules. Establish `hc : ∀ (z : Matrix (Fin n₁) (Fin d) (AE F E)) (a : Fin d → AE F E), symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) a) = 0`.

Introduce `z a`. Rewrite using `[symp, vecMulVec_incV, hTens_mul, incM_gram, gιx, incM_zero]`. Simplify using the standard rewrite rules. Establish `h4 : symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * z) (incM F H.ι * z') = symp (cA σ) (-1) (incM F X₁.J) (incM F W.J) z z'`. Rewrite using `[symp, symp, hTens_mul, incM_gram, hH.gram, hTens_eq_trace]`.

Rewrite `h4` using `[M₁.co.form, hz, hz', zero_dotProduct, zero_dotProduct, sub_zero]`. Establish `h2` using `hc z a'`. Establish `h3` using `hc z' a`. Rewrite `h1`, `h2`, `h3`, `h4` using `[hD]`. Simplify using `only [map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]`.

Take the linear combination `h1 + h2 - h3 + h4`.
-/
theorem isotropic {B : Base F E} {n n₁ d : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {W : Spc F E d} {H : Plane E n n₁}
    {j₀ j₁ : ℕ} (M : Model σ X W) (M₁ : Model σ X₁ W) (hH : H.IsAdapted σ B X X₁ j₀ j₁) (a a' : Fin d → AE F E)
    (z z' : Matrix (Fin n₁) (Fin d) (AE F E)) (hz : (M₁.co.e z).1 = 0) (hz' : (M₁.co.e z').1 = 0) :
    (M.co.e (Matrix.vecMulVec (incV F H.x) a + incM F H.ι * z)).1 ⬝ᵥ
        (M.co.e (Matrix.vecMulVec (incV F H.x) a' + incM F H.ι * z')).2 =
      (M.co.e (Matrix.vecMulVec (incV F H.x) a' + incM F H.ι * z')).1 ⬝ᵥ
        (M.co.e (Matrix.vecMulVec (incV F H.x) a + incM F H.ι * z)).2 := by
  have hD : ∀ p q, symp (cA σ) (-1) (incM F X.J) (incM F W.J) p q =
      (M.co.e p).1 ⬝ᵥ (M.co.e q).2 - (M.co.e q).1 ⬝ᵥ (M.co.e p).2 := M.co.form
  have gxx : (Matrix.replicateCol Unit H.x)ᵀ * X.J * (Matrix.replicateCol Unit H.x).map σ = 0 := by
    ext i j
    rw [gram_apply]
    exact hH.xx
  have gιx : H.ιᵀ * X.J * (Matrix.replicateCol Unit H.x).map σ = 0 := by
    ext i j
    rw [gram_apply]
    have := (hH.orth (Pi.single i 1)).1
    rw [Matrix.mulVec_single_one] at this
    exact this
  have h1 : symp (cA σ) (-1) (incM F X.J) (incM F W.J) (Matrix.vecMulVec (incV F H.x) a)
      (Matrix.vecMulVec (incV F H.x) a') = 0 := by
    rw [symp, vecMulVec_incV, vecMulVec_incV, hTens_mul, incM_gram, gxx, incM_zero]
    simp
  have hc : ∀ (z : Matrix (Fin n₁) (Fin d) (AE F E)) (a : Fin d → AE F E),
      symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) a) = 0 := by
    intro z a
    rw [symp, vecMulVec_incV, hTens_mul, incM_gram, gιx, incM_zero]
    simp
  have h4 : symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * z) (incM F H.ι * z') =
      symp (cA σ) (-1) (incM F X₁.J) (incM F W.J) z z' := by
    rw [symp, symp, hTens_mul, incM_gram, hH.gram, hTens_eq_trace]
  rw [M₁.co.form, hz, hz', zero_dotProduct, zero_dotProduct, sub_zero] at h4
  have h2 := hc z a'
  have h3 := hc z' a
  rw [hD] at h1 h2 h3 h4
  simp only [map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  linear_combination h1 + h2 - h3 + h4

omit [NumberField F] [NumberField E] in

/- English proof (translation)
Establish `ha : a = 0`. Use function extensionality and compare the values at `j`. Establish `hcol : a j • x + ι *ᵥ (fun k => z k j) = 0`. Use function extensionality and compare the values at `i`. Use `congrFun (congrFun h i) j` as an intermediate fact.

Simplify using `only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.zero_apply] at this`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Pi.zero_apply]`. Rewrite using `[← this, mul_comm]`. Establish `h1 : form σ J (a j • x + ι *ᵥ (fun k => z k j)) y = a j * form σ J x y + form σ J (ι *ᵥ fun k => z k j) y`. Simplify using `[form, add_dotProduct, smul_dotProduct]`.

Rewrite `h1` using `[hcol, hxy, hιy]`. Simplify `h1.symm` using `[form]`. Use `⟨ha, ?_⟩` and prove the remaining obligations. Establish `hv : Matrix.vecMulVec x a = 0` using `by ext i j; simp [Matrix.vecMulVec_apply, ha]`. Rewrite `h` using `[hv, zero_add]`.

Establish `h0 : zᵀ * J₁ = 0`. Rewrite using `[← hg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, h, Matrix.transpose_zero, Matrix.zero_mul, Matrix.zero_mul]`. Establish `h1` using `congrArg (· * J₁⁻¹) h0`. Simplify using `only [Matrix.zero_mul] at h1`. Rewrite `h1` using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.mul_one]`.

Conclude with `Matrix.transpose_eq_zero.mp h1`.
-/
theorem eq_zero_of_mixed {n n₁ d : ℕ} {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E} {x y : Fin n → E}
    {ι : Matrix (Fin n) (Fin n₁) E} (hxy : form σ J x y = 1) (hιy : ∀ u, form σ J (ι *ᵥ u) y = 0)
    (hg : ιᵀ * J * ι.map σ = J₁) (hdet : J₁.det ≠ 0) (a : Fin d → E) (z : Matrix (Fin n₁) (Fin d) E)
    (h : Matrix.vecMulVec x a + ι * z = 0) : a = 0 ∧ z = 0 := by
  have ha : a = 0 := by
    funext j
    have hcol : a j • x + ι *ᵥ (fun k => z k j) = 0 := by
      funext i
      have := congrFun (congrFun h i) j
      simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.zero_apply] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← this, mul_comm]
    have h1 : form σ J (a j • x + ι *ᵥ (fun k => z k j)) y = a j * form σ J x y + form σ J (ι *ᵥ fun k => z k j) y := by
      simp [form, add_dotProduct, smul_dotProduct]
    rw [hcol, hxy, hιy] at h1
    simpa [form] using h1.symm
  refine ⟨ha, ?_⟩
  have hv : Matrix.vecMulVec x a = 0 := by ext i j; simp [Matrix.vecMulVec_apply, ha]
  rw [hv, zero_add] at h
  have h0 : zᵀ * J₁ = 0 := by
    rw [← hg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, h, Matrix.transpose_zero, Matrix.zero_mul,
      Matrix.zero_mul]
  have h1 := congrArg (· * J₁⁻¹) h0
  simp only [Matrix.zero_mul] at h1
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.mul_one] at h1
  exact Matrix.transpose_eq_zero.mp h1

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁`. Take `⟨f, hf, hfe⟩` from `exists_ratMap M hP.good.rat`. Take `⟨f₁, hf₁, hfe₁⟩` from `exists_ratMap M₁ hP₁.good.rat`. Establish `h2 : Module.finrank F E = 2` using `hP.base.cm.2.2.1`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)`.

Take `⟨K, hK, hKz⟩` from `rat_first_zero_dim F E σ n₁ d X₁ W M₁ h2 f₁ hf₁ hfe₁`. Set `Φ : (Fin d → E) × K →ₗ[F] Matrix (Fin n) (Fin d) E` to `{ toFun := fun p => Matrix.vecMulVec H.x p.1 + H.ι * (p.2 : Matrix (Fin n₁) (Fin d) E) map_add' := fun p q => by`. Simplify using `only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.vecMulVec_add, Matrix.mul_add]`. Normalize the expressions using the abelian group laws. Use the proof step `map_smul' := fun c p => by`.

Use extensionality with `i j`. Simplify using `[Matrix.vecMulVec_apply, Matrix.mul_apply, Finset.smul_sum, smul_add] }`. Establish `hΦ : ∀ p, Φ p = Matrix.vecMulVec H.x p.1 + H.ι * (p.2 : Matrix (Fin n₁) (Fin d) E)` using `fun _ => rfl`. Establish `hinj : Function.Injective Φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `p hp`. Take `⟨h, h'⟩` from `eq_zero_of_mixed hH.xy (fun u => (hH.orth u).2) hH.gram (herm_det_ne_zero hP₁.herm) _ _ hp`. Conclude with `Prod.ext h (Subtype.ext h')`. Establish `hhat : ∀ p, hat (f (Φ p)) = M.co.e (Matrix.vecMulVec (incV F H.x) (incV F p.1) + incM F H.ι * incM F (p.2 : Matrix (Fin n₁) (Fin d) E))`. Introduce `p`.

Rewrite using `[hfe, hΦ]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[incM, incV, Matrix.vecMulVec_apply, Matrix.mul_apply, map_sum, map_mul]`. Use `⟨LinearMap.range (f ∘ₗ Φ), ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨p, rfl⟩ _ ⟨q, rfl⟩`. Establish `h` using `isotropic M M₁ hH (incV F p.1) (incV F q.1) _ _ (hKz _ p.2.2) (hKz _ q.2.2)`. Rewrite `h` using `[← hhat, ← hhat]`. Apply `AdeleRing.algebraMap_injective (𝓞 F) F` to reduce the goal to its premises. Rewrite using `[RingHom.map_dotProduct, RingHom.map_dotProduct]`.

Conclude with `h`. Rewrite using `[LinearMap.finrank_range_of_inj (f := f ∘ₗ Φ) (hf.comp hinj), Module.finrank_prod, Module.finrank_pi_fintype, hK]`. Simplify using `[h2, hH.rank]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `t _ ⟨p, rfl⟩`.

Use `⟨t • incV F p.1, t • incM F (p.2 : Matrix (Fin n₁) (Fin d) E), by simp [hKz _ p.2.2], ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.vecMulVec_smul, Matrix.mul_smul, ← smul_add, LinearEquiv.map_smul, ← hhat]`. Both sides reduce to the same expression.
-/
theorem exists_ratLagr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∃ L : Submodule F ((Fin n × Fin d → F) × (Fin n × Fin d → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
        Module.finrank F L = Fintype.card (Fin n × Fin d) ∧
        ∀ (t : AF F), ∀ w ∈ L, ∃ (a : Fin d → AE F E) (z : Matrix (Fin n₁) (Fin d) (AE F E)), (M₁.co.e z).1 = 0 ∧
          M.co.e (Matrix.vecMulVec (incV F H.x) a + incM F H.ι * z) =
            t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i))) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁
  obtain ⟨f, hf, hfe⟩ := exists_ratMap M hP.good.rat
  obtain ⟨f₁, hf₁, hfe₁⟩ := exists_ratMap M₁ hP₁.good.rat
  have h2 : Module.finrank F E = 2 := hP.base.cm.2.2.1
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  obtain ⟨K, hK, hKz⟩ := rat_first_zero_dim F E σ n₁ d X₁ W M₁ h2 f₁ hf₁ hfe₁
  let Φ : (Fin d → E) × K →ₗ[F] Matrix (Fin n) (Fin d) E :=
    { toFun := fun p => Matrix.vecMulVec H.x p.1 + H.ι * (p.2 : Matrix (Fin n₁) (Fin d) E)
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.vecMulVec_add, Matrix.mul_add]; abel
      map_smul' := fun c p => by
        ext i j
        simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Finset.smul_sum, smul_add] }
  have hΦ : ∀ p, Φ p = Matrix.vecMulVec H.x p.1 + H.ι * (p.2 : Matrix (Fin n₁) (Fin d) E) := fun _ => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    obtain ⟨h, h'⟩ := eq_zero_of_mixed hH.xy (fun u => (hH.orth u).2) hH.gram (herm_det_ne_zero hP₁.herm) _ _ hp
    exact Prod.ext h (Subtype.ext h')
  have hhat : ∀ p, hat (f (Φ p)) = M.co.e (Matrix.vecMulVec (incV F H.x) (incV F p.1) +
      incM F H.ι * incM F (p.2 : Matrix (Fin n₁) (Fin d) E)) := by
    intro p
    rw [hfe, hΦ]
    congr 1
    ext i j
    simp [incM, incV, Matrix.vecMulVec_apply, Matrix.mul_apply, map_sum, map_mul]
  refine ⟨LinearMap.range (f ∘ₗ Φ), ?_, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    have h := isotropic M M₁ hH (incV F p.1) (incV F q.1) _ _ (hKz _ p.2.2) (hKz _ q.2.2)
    rw [← hhat, ← hhat] at h
    apply AdeleRing.algebraMap_injective (𝓞 F) F
    rw [RingHom.map_dotProduct, RingHom.map_dotProduct]
    exact h
  · rw [LinearMap.finrank_range_of_inj (f := f ∘ₗ Φ) (hf.comp hinj), Module.finrank_prod, Module.finrank_pi_fintype, hK]
    simp [h2, hH.rank]
    ring
  · rintro t _ ⟨p, rfl⟩
    refine ⟨t • incV F p.1, t • incM F (p.2 : Matrix (Fin n₁) (Fin d) E), by simp [hKz _ p.2.2], ?_⟩
    rw [Matrix.vecMulVec_smul, Matrix.mul_smul, ← smul_add, LinearEquiv.map_smul, ← hhat]
    rfl

end GlobalTheory.MixedLagrX

end
