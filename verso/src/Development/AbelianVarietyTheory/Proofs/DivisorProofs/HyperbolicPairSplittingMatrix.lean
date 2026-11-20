import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.GramAdapted

/- English proof (translation)
Simplify using `only [form, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Conclude with `Finset.sum_comm`.
-/
theorem gram_apply {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {k : ℕ} {m : Type} [Fintype m]
    (J : Matrix (Fin k) (Fin k) E) (P : Matrix (Fin k) m E) (a b : m) :
    (Pᵀ * J * P.map σ) a b = form σ J (fun r => P r a) (fun r => P r b) := by
  simp only [form, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/- English proof (translation)
Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hJ j i]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_swap {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {k : ℕ}
    (J : Matrix (Fin k) (Fin k) E) (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (u v : Fin k → E) :
    form σ J v u = σ (form σ J u v) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ j i]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `r`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem col_eq {E : Type} [Field E] {k n : ℕ} (ι : Matrix (Fin k) (Fin n) E) (i : Fin n) :
    (fun r => ι r i) = ι *ᵥ Pi.single i 1 := by
  funext r
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/- English proof (translation)
Introduce `hσ hJ hJ₁ hxx hyy hxy horth hgram hPι hPx hPy`. Establish `cι : ∀ i, (fun r => P r (Fin.castAdd 2 i)) = ι *ᵥ Pi.single i 1` using `fun i => by`. Rewrite using `[← col_eq]`. Use function extensionality and compare the values at `r`. Conclude with `hPι r i`.

Establish `cx : (fun r => P r (Fin.natAdd n₁ 0)) = x` using `funext hPx`. Establish `cy : (fun r => P r (Fin.natAdd n₁ 1)) = y` using `funext hPy`. Establish `hyx : form σ J y x = 1` using `by rw [form_swap σ J hσ hJ, hxy, map_one]`. Establish `hCC : ∀ i i', (Pᵀ * J * P.map σ) (Fin.castAdd 2 i) (Fin.castAdd 2 i') = J₁ i i'` using `fun i i' => by`. Rewrite using `[← hgram, gram_apply, gram_apply]`.

Apply the tactic sequence `congr 1 <;> funext r <;> exact hPι r _`. Establish `hCN : ∀ i t, (Pᵀ * J * P.map σ) (Fin.castAdd 2 i) (Fin.natAdd n₁ t) = 0` using `fun i t => by`. Rewrite using `[gram_apply, cι]`. Use `fin_cases t`. Simplify using `only [Fin.zero_eta]`.

Rewrite using `[cx]`. Conclude with `(horth _).1`. Simplify using `only [Fin.mk_one]`. Rewrite using `[cy]`. Conclude with `(horth _).2`.

Establish `hNC : ∀ t i, (Pᵀ * J * P.map σ) (Fin.natAdd n₁ t) (Fin.castAdd 2 i) = 0` using `fun t i => by`. Rewrite using `[gram_apply, form_swap σ J hσ hJ, ← gram_apply, hCN, map_zero]`. Establish `h00 : (Pᵀ * J * P.map σ) (Fin.natAdd n₁ 0) (Fin.natAdd n₁ 0) = 0` using `by rw [gram_apply, cx, hxx]`. Establish `h11 : (Pᵀ * J * P.map σ) (Fin.natAdd n₁ 1) (Fin.natAdd n₁ 1) = 0` using `by rw [gram_apply, cy, hyy]`. Establish `h01 : (Pᵀ * J * P.map σ) (Fin.natAdd n₁ 0) (Fin.natAdd n₁ 1) = 1` using `by rw [gram_apply, cx, cy, hxy]`.

Establish `h10 : (Pᵀ * J * P.map σ) (Fin.natAdd n₁ 1) (Fin.natAdd n₁ 0) = 1` using `by rw [gram_apply, cx, cy, hyx]`. Use `⟨?_, hCC, hCN, hNC, h00, h11, h01, h10⟩` and prove the remaining obligations. Introduce `hdet`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Use `set G := Pᵀ * J * P.map σ with hG`.

Establish `hw : v ᵥ* G = 0`. Rewrite using `[hG, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, hv, Matrix.zero_vecMul, Matrix.zero_vecMul]`. Establish `hent : ∀ b, ∑ i : Fin n₁, v (Fin.castAdd 2 i) * G (Fin.castAdd 2 i) b + ∑ t : Fin 2, v (Fin.natAdd n₁ t) * G (Fin.natAdd n₁ t) b = 0` using `fun b => by`. Use `congr_fun hw b` as an intermediate fact. Rewrite `this` using `[Matrix.vecMul, dotProduct, Fin.sum_univ_add]`.

Conclude with `this`. Establish `hv1 : v (Fin.natAdd n₁ 1) = 0`. Use `hent (Fin.natAdd n₁ 0)` as an intermediate fact. Simplify `this` using `[hCN, h00, h10, Fin.sum_univ_two]`. Establish `hv0' : v (Fin.natAdd n₁ 0) = 0`.

Use `hent (Fin.natAdd n₁ 1)` as an intermediate fact. Simplify `this` using `[hCN, h11, h01, Fin.sum_univ_two]`. Establish `hvJ : (fun i => v (Fin.castAdd 2 i)) ᵥ* J₁ = 0`. Use function extensionality and compare the values at `i'`. Use `hent (Fin.castAdd 2 i')` as an intermediate fact.

Simplify using `only [hCC, hNC, mul_zero, Finset.sum_const_zero, add_zero] at this`. Simplify `this` using `[Matrix.vecMul, dotProduct]`. Establish `hvC : (fun i => v (Fin.castAdd 2 i)) = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hJ₁ (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hne, hvJ⟩)`.

Apply `hv0` to reduce the goal to its premises. Use function extensionality and compare the values at `a`. Use `Fin.addCases (fun i => ?_) (fun t => ?_) a` and prove the remaining obligations. Conclude with `congr_fun hvC i`. Use `fin_cases t`.

Conclude with `hv0'`. Conclude with `hv1`.
-/
theorem gram_adapted {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n₁ : ℕ) (J : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E)
    (J₁ : Matrix (Fin n₁) (Fin n₁) E) (x y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E)
    (P : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E) :
    (∀ a, σ (σ a) = a) → (∀ i j, σ (J j i) = J i j) → J₁.det ≠ 0 → form σ J x x = 0 → form σ J y y = 0 → form σ J x y = 1 →
    (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) → ιᵀ * J * ι.map σ = J₁ →
    (∀ r i, P r (Fin.castAdd 2 i) = ι r i) → (∀ r, P r (Fin.natAdd n₁ 0) = x r) → (∀ r, P r (Fin.natAdd n₁ 1) = y r) →
    P.det ≠ 0 ∧ (∀ i i', (Pᵀ * J * P.map σ) (Fin.castAdd 2 i) (Fin.castAdd 2 i') = J₁ i i') ∧
      (∀ i t, (Pᵀ * J * P.map σ) (Fin.castAdd 2 i) (Fin.natAdd n₁ t) = 0) ∧
      (∀ t i, (Pᵀ * J * P.map σ) (Fin.natAdd n₁ t) (Fin.castAdd 2 i) = 0) ∧
      (Pᵀ * J * P.map σ) (Fin.natAdd n₁ 0) (Fin.natAdd n₁ 0) = 0 ∧ (Pᵀ * J * P.map σ) (Fin.natAdd n₁ 1) (Fin.natAdd n₁ 1) = 0 ∧
      (Pᵀ * J * P.map σ) (Fin.natAdd n₁ 0) (Fin.natAdd n₁ 1) = 1 ∧ (Pᵀ * J * P.map σ) (Fin.natAdd n₁ 1) (Fin.natAdd n₁ 0) = 1 := by
  intro hσ hJ hJ₁ hxx hyy hxy horth hgram hPι hPx hPy
  have cι : ∀ i, (fun r => P r (Fin.castAdd 2 i)) = ι *ᵥ Pi.single i 1 := fun i => by
    rw [← col_eq]; funext r; exact hPι r i
  have cx : (fun r => P r (Fin.natAdd n₁ 0)) = x := funext hPx
  have cy : (fun r => P r (Fin.natAdd n₁ 1)) = y := funext hPy
  have hyx : form σ J y x = 1 := by rw [form_swap σ J hσ hJ, hxy, map_one]
  have hCC : ∀ i i', (Pᵀ * J * P.map σ) (Fin.castAdd 2 i) (Fin.castAdd 2 i') = J₁ i i' := fun i i' => by
    rw [← hgram, gram_apply, gram_apply]
    congr 1 <;> funext r <;> exact hPι r _
  have hCN : ∀ i t, (Pᵀ * J * P.map σ) (Fin.castAdd 2 i) (Fin.natAdd n₁ t) = 0 := fun i t => by
    rw [gram_apply, cι]
    fin_cases t
    · simp only [Fin.zero_eta]; rw [cx]; exact (horth _).1
    · simp only [Fin.mk_one]; rw [cy]; exact (horth _).2
  have hNC : ∀ t i, (Pᵀ * J * P.map σ) (Fin.natAdd n₁ t) (Fin.castAdd 2 i) = 0 := fun t i => by
    rw [gram_apply, form_swap σ J hσ hJ, ← gram_apply, hCN, map_zero]
  have h00 : (Pᵀ * J * P.map σ) (Fin.natAdd n₁ 0) (Fin.natAdd n₁ 0) = 0 := by rw [gram_apply, cx, hxx]
  have h11 : (Pᵀ * J * P.map σ) (Fin.natAdd n₁ 1) (Fin.natAdd n₁ 1) = 0 := by rw [gram_apply, cy, hyy]
  have h01 : (Pᵀ * J * P.map σ) (Fin.natAdd n₁ 0) (Fin.natAdd n₁ 1) = 1 := by rw [gram_apply, cx, cy, hxy]
  have h10 : (Pᵀ * J * P.map σ) (Fin.natAdd n₁ 1) (Fin.natAdd n₁ 0) = 1 := by rw [gram_apply, cx, cy, hyx]
  refine ⟨?_, hCC, hCN, hNC, h00, h11, h01, h10⟩
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set G := Pᵀ * J * P.map σ with hG
  have hw : v ᵥ* G = 0 := by
    rw [hG, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, hv, Matrix.zero_vecMul,
      Matrix.zero_vecMul]
  have hent : ∀ b, ∑ i : Fin n₁, v (Fin.castAdd 2 i) * G (Fin.castAdd 2 i) b
      + ∑ t : Fin 2, v (Fin.natAdd n₁ t) * G (Fin.natAdd n₁ t) b = 0 := fun b => by
    have := congr_fun hw b
    rw [Matrix.vecMul, dotProduct, Fin.sum_univ_add] at this
    exact this
  have hv1 : v (Fin.natAdd n₁ 1) = 0 := by
    have := hent (Fin.natAdd n₁ 0)
    simpa [hCN, h00, h10, Fin.sum_univ_two] using this
  have hv0' : v (Fin.natAdd n₁ 0) = 0 := by
    have := hent (Fin.natAdd n₁ 1)
    simpa [hCN, h11, h01, Fin.sum_univ_two] using this
  have hvJ : (fun i => v (Fin.castAdd 2 i)) ᵥ* J₁ = 0 := by
    funext i'
    have := hent (Fin.castAdd 2 i')
    simp only [hCC, hNC, mul_zero, Finset.sum_const_zero, add_zero] at this
    simpa [Matrix.vecMul, dotProduct] using this
  have hvC : (fun i => v (Fin.castAdd 2 i)) = 0 := by
    by_contra hne
    exact hJ₁ (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hne, hvJ⟩)
  apply hv0
  funext a
  refine Fin.addCases (fun i => ?_) (fun t => ?_) a
  · exact congr_fun hvC i
  · fin_cases t
    · exact hv0'
    · exact hv1

end GlobalTheory.GramAdapted
