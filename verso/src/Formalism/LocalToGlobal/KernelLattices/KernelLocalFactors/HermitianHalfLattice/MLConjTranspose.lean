import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThIndEqAmbOfOf

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker.TI

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open Formalism.L2.Th1.H (IsIsom imgLat)

section Mat

variable {E : Type} [Field E] {ι : Type} (emb : ι → E →+* ℂ)

def mL {n m : ℕ} (f : Sp E n →ₗ[E] Sp E m) (τ : ι) : Matrix (Fin m) (Fin n) ℂ :=
  Matrix.of fun i k => emb τ (f (Pi.single k 1) i)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mL_apply {n m : ℕ} (f : Sp E n →ₗ[E] Sp E m) (τ : ι) (i : Fin m) (k : Fin n) :
    mL emb f τ i k = emb τ (f (Pi.single k 1) i) := rfl

/- English proof (translation)
Establish `h` using `LinearMap.pi_apply_eq_sum_univ f v`. Establish `e : ∀ k : Fin n, (fun j => if k = j then (1 : E) else 0) = Pi.single k 1`. Introduce `k`. Use function extensionality and compare the values at `j`. Simplify using `[Pi.single_apply, eq_comm]`.

Rewrite using `[h, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[e k, Pi.smul_apply, smul_eq_mul]`.
-/
theorem lin_apply_eq_sum {n m : ℕ} (f : Sp E n →ₗ[E] Sp E m) (v : Sp E n) (i : Fin m) :
    f v i = ∑ k, v k * f (Pi.single k 1) i := by
  classical
  have h := LinearMap.pi_apply_eq_sum_univ f v
  have e : ∀ k : Fin n, (fun j => if k = j then (1 : E) else 0) = Pi.single k 1 := by
    intro k; funext j; simp [Pi.single_apply, eq_comm]
  rw [h, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [e k, Pi.smul_apply, smul_eq_mul]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, mL_apply, LinearMap.comp_apply, lin_apply_eq_sum f (g (Pi.single j 1)) i, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, mul_comm]`. Both sides reduce to the same expression.
-/
theorem mL_comp {n m l : ℕ} (f : Sp E m →ₗ[E] Sp E l) (g : Sp E n →ₗ[E] Sp E m) (τ : ι) :
    mL emb (f ∘ₗ g) τ = mL emb f τ * mL emb g τ := by
  ext i j
  rw [Matrix.mul_apply, mL_apply, LinearMap.comp_apply, lin_apply_eq_sum f (g (Pi.single j 1)) i, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, mul_comm]
  rfl

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[mL_apply, LinearMap.id_apply, Matrix.one_apply, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem mL_id {n : ℕ} (τ : ι) : mL emb (LinearMap.id : Sp E n →ₗ[E] Sp E n) τ = 1 := by
  classical
  ext i j
  rw [mL_apply, LinearMap.id_apply, Matrix.one_apply, Pi.single_apply]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[← mL_comp]`. Establish `: g.toLinearMap ∘ₗ g.symm.toLinearMap = LinearMap.id` using `by ext v i; simp`. Rewrite using `[this, mL_id]`.
-/
theorem mL_equiv {n : ℕ} (g : Sp E n ≃ₗ[E] Sp E n) (τ : ι) : mL emb g.toLinearMap τ * mL emb g.symm.toLinearMap τ = 1 := by
  rw [← mL_comp]
  have : g.toLinearMap ∘ₗ g.symm.toLinearMap = LinearMap.id := by ext v i; simp
  rw [this, mL_id]

/- English proof (translation)
Rewrite using `[← mL_comp]`. Establish `: g.symm.toLinearMap ∘ₗ g.toLinearMap = LinearMap.id` using `by ext v i; simp`. Rewrite using `[this, mL_id]`.
-/
theorem mL_equiv' {n : ℕ} (g : Sp E n ≃ₗ[E] Sp E n) (τ : ι) : mL emb g.symm.toLinearMap τ * mL emb g.toLinearMap τ = 1 := by
  rw [← mL_comp]
  have : g.symm.toLinearMap ∘ₗ g.toLinearMap = LinearMap.id := by ext v i; simp
  rw [this, mL_id]

end Mat

section Unit

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} (emb : ι → E →+* ℂ)

/- English proof (translation)
Use extensionality with `i k`. Rewrite using `[Matrix.conjTranspose_apply, mL_apply, mL_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, TE.ufInv_apply γ i k, hst]`.
-/
theorem mL_conjTranspose (hst : ∀ τ x, emb τ (star x) = star (emb τ x)) {n : ℕ} (γ : UF E n) (τ : ι) :
    (mL emb γ.1.toLinearMap τ).conjTranspose = mL emb γ.1.symm.toLinearMap τ := by
  ext i k
  rw [Matrix.conjTranspose_apply, mL_apply, mL_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, TE.ufInv_apply γ i k, hst]

end Unit

section RVdef

variable {X : Fields} (A : Amb X) {a b : ℕ}

abbrev zM (z : VCx X.Tau a b) (τ : X.Tau) : Matrix (Fin b) (Fin a) ℂ := Matrix.of (z τ)

def mulM (h : X.Tau → Matrix (Fin b) (Fin b) ℂ) (g : X.Tau → Matrix (Fin a) (Fin a) ℂ) (z : VCx X.Tau a b) : VCx X.Tau a b :=
  fun τ => Matrix.of.symm (h τ * zM z τ * g τ)

/- English proof (translation)
Simplify using `[zM, mulM]`.
-/
theorem zM_mulM (h : X.Tau → Matrix (Fin b) (Fin b) ℂ) (g : X.Tau → Matrix (Fin a) (Fin a) ℂ) (z : VCx X.Tau a b) (τ : X.Tau) :
    zM (mulM h g z) τ = h τ * zM z τ * g τ := by
  simp [zM, mulM]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulM_apply (h : X.Tau → Matrix (Fin b) (Fin b) ℂ) (g : X.Tau → Matrix (Fin a) (Fin a) ℂ) (z : VCx X.Tau a b) (τ : X.Tau) (i : Fin b) (j : Fin a) :
    mulM h g z τ i j = (h τ * zM z τ * g τ) i j := rfl

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Simplify using `only [mulM, zM_mulM, Matrix.mul_assoc]`.
-/
theorem mulM_mulM (h h' : X.Tau → Matrix (Fin b) (Fin b) ℂ) (g g' : X.Tau → Matrix (Fin a) (Fin a) ℂ) (z : VCx X.Tau a b) :
    mulM h g (mulM h' g' z) = mulM (fun τ => h τ * h' τ) (fun τ => g' τ * g τ) z := by
  funext τ
  simp only [mulM, zM_mulM, Matrix.mul_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Simplify using `[mulM, zM]`.
-/
theorem mulM_one (z : VCx X.Tau a b) : mulM (fun _ => (1 : Matrix (Fin b) (Fin b) ℂ)) (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) z = z := by
  funext τ
  simp [mulM, zM]

def RV (γ : UF X.E a) (γ' : UF X.E b) : VCx X.Tau a b ≃ₗ[ℂ] VCx X.Tau a b where
  toFun := mulM (mL (X.embC A.σ₀) γ'.1.toLinearMap) (mL (X.embC A.σ₀) γ.1.symm.toLinearMap)
  invFun := mulM (mL (X.embC A.σ₀) γ'.1.symm.toLinearMap) (mL (X.embC A.σ₀) γ.1.toLinearMap)
  map_add' z w := by
    funext τ i j
    rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, mulM_apply, mulM_apply, mulM_apply]
    have e : zM (z + w) τ = zM z τ + zM w τ := rfl
    rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
  map_smul' c z := by
    funext τ i j
    rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, mulM_apply, mulM_apply, RingHom.id_apply]
    have e : zM (c • z) τ = c • zM z τ := rfl
    rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply]
  left_inv z := by
    show mulM _ _ (mulM _ _ z) = z
    rw [mulM_mulM]
    simp only [mL_equiv']
    exact mulM_one z
  right_inv z := by
    show mulM _ _ (mulM _ _ z) = z
    rw [mulM_mulM]
    simp only [mL_equiv]
    exact mulM_one z

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem RV_apply (γ : UF X.E a) (γ' : UF X.E b) (z : VCx X.Tau a b) :
    RV A γ γ' z = mulM (mL (X.embC A.σ₀) γ'.1.toLinearMap) (mL (X.embC A.σ₀) γ.1.symm.toLinearMap) z := rfl

/- English proof (translation)
Use `show mulM _ _ z = _`. Use function extensionality and compare the values at `τ i j`. Simplify using `only [mulM, zM, Amb.pullV, Matrix.mul_apply, Matrix.of_apply, Matrix.of_symm_apply, mL_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Both sides reduce to the same expression.
-/
theorem RV_symm_apply (γ : UF X.E a) (γ' : UF X.E b) (z : VCx X.Tau a b) : (RV A γ γ').symm z = A.pullV a b γ.1 γ'.1 z := by
  show mulM _ _ z = _
  funext τ i j
  simp only [mulM, zM, Amb.pullV, Matrix.mul_apply, Matrix.of_apply, Matrix.of_symm_apply, mL_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

/- English proof (translation)
Establish `e : ∀ τ, zM (embH (X.embC A.σ₀) A.δ y) τ = A.δ • mL (X.embC A.σ₀) y τ`. Introduce `τ`. Use extensionality with `i j`. Simplify using `[zM, embH, mL_apply]`. Use function extensionality and compare the values at `τ i j`.

Rewrite using `[RV_apply, mulM_apply, e, Matrix.mul_smul, Matrix.smul_mul, ← mL_comp, ← mL_comp, Matrix.smul_apply, mL_apply, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem RV_embH (γ : UF X.E a) (γ' : UF X.E b) (y : HomE X.E a b) :
    RV A γ γ' (embH (X.embC A.σ₀) A.δ y) = embH (X.embC A.σ₀) A.δ (γ'.1.toLinearMap ∘ₗ y ∘ₗ γ.1.symm.toLinearMap) := by
  have e : ∀ τ, zM (embH (X.embC A.σ₀) A.δ y) τ = A.δ • mL (X.embC A.σ₀) y τ := by
    intro τ; ext i j; simp [zM, embH, mL_apply]
  funext τ i j
  rw [RV_apply, mulM_apply, e, Matrix.mul_smul, Matrix.smul_mul, ← mL_comp, ← mL_comp, Matrix.smul_apply, mL_apply, smul_eq_mul]
  rfl

end RVdef

section Iso

variable {X : Fields} (A : Amb X) {a b : ℕ}

/- English proof (translation)
Use `show (sc : ℂ) * ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) = _`. Use `congr 1`.
-/
theorem HV_eq_trace (sc : ℝ) (z w : VCx X.Tau a b) :
    HV sc z w = (sc : ℂ) * ∑ τ, (zM z τ * (zM w τ).conjTranspose).trace := by
  show (sc : ℂ) * ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) = _
  congr 1

/- English proof (translation)
Introduce `z w`. Use `show HV A.sc (RV A γ γ' z) (RV A γ γ' w) = HV A.sc z w`. Rewrite using `[HV_eq_trace, HV_eq_trace]`. Use `congr 1`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Simplify using `only [RV_apply, zM_mulM, Matrix.conjTranspose_mul]`. Use `set P := mL (X.embC A.σ₀) γ'.1.toLinearMap τ`. Use `set Q := mL (X.embC A.σ₀) γ.1.symm.toLinearMap τ`. Establish `hP : P.conjTranspose * P = 1`. Rewrite using `[mL_conjTranspose _ hst γ' τ]`.

Conclude with `mL_equiv' _ γ'.1 τ`. Establish `hQ : Q * Q.conjTranspose = 1`. Establish `h1` using `mL_conjTranspose _ hst γ τ`. Establish `h2 : Q.conjTranspose = mL (X.embC A.σ₀) γ.1.toLinearMap τ` using `by show (mL (X.embC A.σ₀) γ.1.symm.toLinearMap τ).conjTranspose = _`. Rewrite using `[← h1, Matrix.conjTranspose_conjTranspose]`.

Rewrite using `[h2]`. Conclude with `mL_equiv' _ γ.1 τ`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (P.conjTranspose * P * (zM z τ * (zM w τ).conjTranspose)).trace := by`.

Rewrite using `[hQ, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc]`. Use `_ = (zM z τ * (zM w τ).conjTranspose).trace := by rw [hP, Matrix.one_mul]`.
-/
theorem isIsom_RV (hst : ∀ τ x, X.embC A.σ₀ τ (star x) = star (X.embC A.σ₀ τ x)) (γ : UF X.E a) (γ' : UF X.E b) :
    IsIsom (HV A.sc) (HV A.sc) (RV A γ γ' : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) := by
  intro z w
  show HV A.sc (RV A γ γ' z) (RV A γ γ' w) = HV A.sc z w
  rw [HV_eq_trace, HV_eq_trace]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [RV_apply, zM_mulM, Matrix.conjTranspose_mul]
  set P := mL (X.embC A.σ₀) γ'.1.toLinearMap τ
  set Q := mL (X.embC A.σ₀) γ.1.symm.toLinearMap τ
  have hP : P.conjTranspose * P = 1 := by
    rw [mL_conjTranspose _ hst γ' τ]; exact mL_equiv' _ γ'.1 τ
  have hQ : Q * Q.conjTranspose = 1 := by
    have h1 := mL_conjTranspose _ hst γ τ
    have h2 : Q.conjTranspose = mL (X.embC A.σ₀) γ.1.toLinearMap τ := by
      show (mL (X.embC A.σ₀) γ.1.symm.toLinearMap τ).conjTranspose = _
      rw [← h1, Matrix.conjTranspose_conjTranspose]
    rw [h2]; exact mL_equiv' _ γ.1 τ
  calc (P * zM z τ * Q * (Q.conjTranspose * ((zM w τ).conjTranspose * P.conjTranspose))).trace
      = (P * (zM z τ * (Q * Q.conjTranspose) * (zM w τ).conjTranspose) * P.conjTranspose).trace := by
        simp only [Matrix.mul_assoc]
    _ = (P.conjTranspose * P * (zM z τ * (zM w τ).conjTranspose)).trace := by
        rw [hQ, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    _ = (zM z τ * (zM w τ).conjTranspose).trace := by rw [hP, Matrix.one_mul]

/- English proof (translation)
Unfold `alV Formalism.L2.Th1.H.alphaQ Formalism.L2.Th1.H.qOf`. Rewrite using `[show HV A.sc (RV A γ γ' z) (RV A γ γ' z) = HV A.sc z z from isIsom_RV A hst γ γ' z z]`.
-/
theorem alV_RV (hst : ∀ τ x, X.embC A.σ₀ τ (star x) = star (X.embC A.σ₀ τ x)) (γ : UF X.E a) (γ' : UF X.E b) (z : VCx X.Tau a b) :
    alV A.d A.sc (RV A γ γ' z) = alV A.d A.sc z := by
  unfold alV Formalism.L2.Th1.H.alphaQ Formalism.L2.Th1.H.qOf
  rw [show HV A.sc (RV A γ γ' z) (RV A γ γ' z) = HV A.sc z z from isIsom_RV A hst γ γ' z z]

/- English proof (translation)
Use extensionality with `v`. Simplify using `only [imgLat, laV, AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, ⟨y, hy, rfl⟩, rfl⟩`. Use `⟨γ'.1.toLinearMap ∘ₗ y ∘ₗ γ.1.symm.toLinearMap, (h _).2 ?_, ?_⟩` and prove the remaining obligations.

Establish `e : γ'.1.symm.toLinearMap ∘ₗ (γ'.1.toLinearMap ∘ₗ y ∘ₗ γ.1.symm.toLinearMap) ∘ₗ γ.1.toLinearMap = y`. Use extensionality with `v i`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `hy`.

Conclude with `(RV_embH A γ γ' y).symm`. Introduce and unpack `⟨y, hy, rfl⟩`. Use `⟨embH (X.embC A.σ₀) A.δ (γ'.1.symm.toLinearMap ∘ₗ y ∘ₗ γ.1.toLinearMap), ⟨_, (h y).1 hy, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show RV A γ γ' _ = _`. Rewrite using `[RV_embH]`.

Use `congr 1`. Use extensionality with `v i`. Simplify using the standard rewrite rules.
-/
theorem imgLat_laV (γ : UF X.E a) (γ' : UF X.E b) (M M' : Submodule (𝓞 X.E) (HomE X.E a b))
    (h : ∀ y, y ∈ M' ↔ γ'.1.symm.toLinearMap ∘ₗ y ∘ₗ γ.1.toLinearMap ∈ M) :
    imgLat (RV A γ γ' : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b) (laV (X.embC A.σ₀) A.δ M) = laV (X.embC A.σ₀) A.δ M' := by
  ext v
  simp only [imgLat, laV, AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
  constructor
  · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨γ'.1.toLinearMap ∘ₗ y ∘ₗ γ.1.symm.toLinearMap, (h _).2 ?_, ?_⟩
    · have e : γ'.1.symm.toLinearMap ∘ₗ (γ'.1.toLinearMap ∘ₗ y ∘ₗ γ.1.symm.toLinearMap) ∘ₗ γ.1.toLinearMap = y := by
        ext v i; simp
      rw [e]; exact hy
    · exact (RV_embH A γ γ' y).symm
  · rintro ⟨y, hy, rfl⟩
    refine ⟨embH (X.embC A.σ₀) A.δ (γ'.1.symm.toLinearMap ∘ₗ y ∘ₗ γ.1.toLinearMap), ⟨_, (h y).1 hy, rfl⟩, ?_⟩
    show RV A γ γ' _ = _
    rw [RV_embH]
    congr 1
    ext v i; simp

end Iso

end Formalism.L2.Ker.TI
