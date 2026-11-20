import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiHolomorphicNearPositiveMatricesAtOneStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiComplexifiedKEquivarianceStatement
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm

open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.Dec.PsiPolarProof

variable {n : ℕ}

/- English proof (translation)
Establish `hY : ((1 / 2 : ℝ) • X)ᴴ = (1 / 2 : ℝ) • X`. Rewrite using `[Matrix.conjTranspose_smul, h]`. Simplify using the standard rewrite rules. Establish `e : X = (1 / 2 : ℝ) • X + (1 / 2 : ℝ) • X` using `by rw [← add_smul]; norm_num`. Establish `e2 : NormedSpace.exp X = (NormedSpace.exp ((1 / 2 : ℝ) • X))ᴴ * NormedSpace.exp ((1 / 2 : ℝ) • X)`.

Rewrite using `[exp_conjTranspose_of_hermitian hY, ← exp_add_self, ← e]`. Rewrite using `[e2]`. Conclude with `Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_exp _))`.
-/
lemma exp_posDef_of_herm {X : Matrix (Fin n) (Fin n) ℂ} (h : Xᴴ = X) : (NormedSpace.exp X).PosDef := by
  have hY : ((1 / 2 : ℝ) • X)ᴴ = (1 / 2 : ℝ) • X := by
    rw [Matrix.conjTranspose_smul, h]; simp
  have e : X = (1 / 2 : ℝ) • X + (1 / 2 : ℝ) • X := by rw [← add_smul]; norm_num
  have e2 : NormedSpace.exp X =
      (NormedSpace.exp ((1 / 2 : ℝ) • X))ᴴ * NormedSpace.exp ((1 / 2 : ℝ) • X) := by
    rw [exp_conjTranspose_of_hermitian hY, ← exp_add_self, ← e]
  rw [e2]
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_exp _))

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨⟨k, star k, Unitary.mul_star_self_of_mem hk.1, Unitary.star_mul_self_of_mem hk.1⟩, rfl⟩, hk.2⟩`.
-/
lemma mem_KC_of_mem_K {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    k ∈ KC ε :=
  ⟨⟨⟨k, star k, Unitary.mul_star_self_of_mem hk.1, Unitary.star_mul_self_of_mem hk.1⟩, rfl⟩, hk.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨mul_mem hk.1 hk'.1, by rw [Matrix.mul_assoc, hk'.2, ← Matrix.mul_assoc, hk.2, Matrix.mul_assoc]⟩`.
-/
lemma mul_mem_K {ε : Fin n → Bool} {k k' : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    (hk' : k' ∈ Kset ε) : k * k' ∈ Kset ε :=
  ⟨mul_mem hk.1 hk'.1, by rw [Matrix.mul_assoc, hk'.2, ← Matrix.mul_assoc, hk.2, Matrix.mul_assoc]⟩

/- English proof (translation)
Use `⟨Unitary.star_mem hk.1, ?_⟩` and prove the remaining obligations. Use `congrArg Matrix.conjTranspose hk.2` as an intermediate fact. Simplify `this.symm` using `[Matrix.conjTranspose_mul, Jm_conjTranspose]`.
-/
lemma star_mem_K {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ ∈ Kset ε := by
  refine ⟨Unitary.star_mem hk.1, ?_⟩
  have := congrArg Matrix.conjTranspose hk.2
  simpa [Matrix.conjTranspose_mul, Jm_conjTranspose] using this.symm

/- English proof (translation)
Introduce `n ε lam W _ _ τ w hl hτ`. Use `⟨fun k hk X hX => Psi_unitary_mul ε lam τ w hk.1 (exp_posDef_of_herm (hermitian_of_mem_hermitian_part hX)), ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `Psi_unitary_mul ε lam τ w (one_mem _) (Matrix.PosDef.one (n := Fin n) (R := ℂ))`. Rewrite `h` using `[Matrix.mul_one]`. Rewrite using `[h, (hB n ε lam W τ w hl hτ).2.2.2, hτ.2.1.1]`.

Both sides reduce to the same expression. Introduce `k₁ h₁ k₂ h₂ g hg`. Take `⟨k, X, hk, hX, rfl⟩` from `(polar_decomposition_holds n ε).1 g hg`. Establish `hp` using `exp_posDef_of_herm (hermitian_of_mem_hermitian_part hX)`. Use `set p := NormedSpace.exp X`.

Establish `hs : k₂ * k₂ᴴ = 1` using `Unitary.mul_star_self_of_mem h₂.1`. Establish `hc` using `mem_KC_of_mem_K (star_mem_K h₂)`. Establish `hq : (k₂ᴴ * p * k₂).PosDef` using `hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (mem_KC_of_mem_K h₂).1)`. Establish `e : k₁ * (k * p) * k₂ = (k₁ * k * k₂) * (k₂ᴴ * p * k₂)`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc k₂ k₂ᴴ, hs, Matrix.one_mul]`. Establish `hk3` using `mul_mem_K (mul_mem_K h₁ hk) h₂`. Establish `he` using `hE n ε lam W τ w hl hτ p k₂ᴴ hp hc`. Rewrite `he` using `[Matrix.conjTranspose_conjTranspose]`. Rewrite using `[e, Psi_unitary_mul ε lam τ w hk3.1 hq, Psi_unitary_mul ε lam τ w hk.1 hp, he, ← ContinuousLinearMap.comp_assoc]`.

Establish `hm : (τ (k₁ * k * k₂)).comp (τ k₂ᴴ) = (τ k₁).comp (τ k)`. Establish `a` using `hτ.2.1.2 _ (mem_KC_of_mem_K hk3) _ hc`. Establish `b` using `hτ.2.1.2 _ (mem_KC_of_mem_K h₁) _ (mem_KC_of_mem_K hk)`. Rewrite `a` using `[Matrix.mul_assoc, hs, Matrix.mul_one]`. Conclude with `a.symm.trans b`.

Rewrite using `[hm]`. Both sides reduce to the same expression.
-/
theorem psiPolar_of (hB : PsBasic) (hE : PsEquiv) : PsiPolar := by
  intro n ε lam W _ _ τ w hl hτ
  refine ⟨fun k hk X hX => Psi_unitary_mul ε lam τ w hk.1
    (exp_posDef_of_herm (hermitian_of_mem_hermitian_part hX)), ?_, ?_⟩
  · have h := Psi_unitary_mul ε lam τ w (one_mem _) (Matrix.PosDef.one (n := Fin n) (R := ℂ))
    rw [Matrix.mul_one] at h
    rw [h, (hB n ε lam W τ w hl hτ).2.2.2, hτ.2.1.1]
    rfl
  · intro k₁ h₁ k₂ h₂ g hg
    obtain ⟨k, X, hk, hX, rfl⟩ := (polar_decomposition_holds n ε).1 g hg
    have hp := exp_posDef_of_herm (hermitian_of_mem_hermitian_part hX)
    set p := NormedSpace.exp X
    have hs : k₂ * k₂ᴴ = 1 := Unitary.mul_star_self_of_mem h₂.1
    have hc := mem_KC_of_mem_K (star_mem_K h₂)
    have hq : (k₂ᴴ * p * k₂).PosDef :=
      hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (mem_KC_of_mem_K h₂).1)
    have e : k₁ * (k * p) * k₂ = (k₁ * k * k₂) * (k₂ᴴ * p * k₂) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc k₂ k₂ᴴ, hs, Matrix.one_mul]
    have hk3 := mul_mem_K (mul_mem_K h₁ hk) h₂
    have he := hE n ε lam W τ w hl hτ p k₂ᴴ hp hc
    rw [Matrix.conjTranspose_conjTranspose] at he
    rw [e, Psi_unitary_mul ε lam τ w hk3.1 hq, Psi_unitary_mul ε lam τ w hk.1 hp, he,
      ← ContinuousLinearMap.comp_assoc]
    have hm : (τ (k₁ * k * k₂)).comp (τ k₂ᴴ) = (τ k₁).comp (τ k) := by
      have a := hτ.2.1.2 _ (mem_KC_of_mem_K hk3) _ hc
      have b := hτ.2.1.2 _ (mem_KC_of_mem_K h₁) _ (mem_KC_of_mem_K hk)
      rw [Matrix.mul_assoc, hs, Matrix.mul_one] at a
      exact a.symm.trans b
    rw [hm]
    rfl

end GlobalTheory.Dec.PsiPolarProof

/- English proof (translation)
The claim follows from `GlobalTheory.Dec.PsiPolarProof.psiPolar_of GlobalTheory.T.psi_holomorphic_near_positive_matrices_at_one GlobalTheory.T.psi_complexifiedK_equivariance`.
-/
theorem GlobalTheory.Dec.psiPolar : GlobalTheory.Dec.PsiPolar :=
  GlobalTheory.Dec.PsiPolarProof.psiPolar_of GlobalTheory.T.psi_holomorphic_near_positive_matrices_at_one GlobalTheory.T.psi_complexifiedK_equivariance
