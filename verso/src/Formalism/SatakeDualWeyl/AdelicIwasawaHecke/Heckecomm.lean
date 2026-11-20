import Formalism.SatakeDualWeyl.StatementE
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeConvolutionMemHolds

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section Gelfand

variable {G : Type} [Group G]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem heckecomm_theta_one (θ : G → G) (hm : ∀ x y, θ (x * y) = θ y * θ x) : θ 1 = 1 := by
  have h := hm 1 1
  rw [mul_one] at h
  have h' : θ 1 * θ 1 = θ 1 * 1 := by rw [mul_one, ← h]
  exact mul_left_cancel h'

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem heckecomm_theta_inv (θ : G → G) (hm : ∀ x y, θ (x * y) = θ y * θ x) (x : G) :
    θ x⁻¹ = (θ x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← hm, mul_inv_cancel, heckecomm_theta_one θ hm]

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Apply an available result and prove the equalities needed to match it to the conclusion. A detailed English derivation is pending.
-/
theorem heckecomm_coset_inv (K : Subgroup G) (θ : G → G)
    (hm : ∀ x y, θ (x * y) = θ y * θ x) (hi : ∀ x, θ (θ x) = x) (hK : ∀ x ∈ K, θ x ∈ K)
    (h : G) (y : G ⧸ K) :
    ((θ h * (θ (((h * (θ y.out)⁻¹ : G) : G ⧸ K).out))⁻¹ : G) : G ⧸ K) = y := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K (h * (θ y.out)⁻¹)
  rw [hc]
  conv_rhs => rw [← QuotientGroup.out_eq' y]
  rw [QuotientGroup.eq]
  have hinv := heckecomm_theta_inv θ hm
  rw [hm, hm, hinv, hi]
  convert hK _ c.2 using 1
  group

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem heckecomm_gelfand {k : Type} [CommRing k] (K : Subgroup G) (θ : G → G)
    (hm : ∀ x y, θ (x * y) = θ y * θ x) (hi : ∀ x, θ (θ x) = x) (hK : ∀ x ∈ K, θ x ∈ K)
    (hdc : ∀ g, ∃ a b : K, θ g = (a : G) * g * b)
    (f₁ f₂ : G → k) (hf₁ : IsBiInv K f₁) (hf₂ : IsBiInv K f₂) :
    conv K f₁ f₂ = conv K f₂ f₁ := by
  have hθf : ∀ f : G → k, IsBiInv K f → ∀ x, f (θ x) = f x := by
    intro f hf x
    obtain ⟨a, b, e⟩ := hdc x
    rw [e, hf]
  have hinv := heckecomm_theta_inv θ hm
  funext g
  rw [← hθf _ (conv_biInv K f₁ f₂ hf₁ hf₂) g]
  let e : G ⧸ K ≃ G ⧸ K :=
    { toFun := fun y => ((g * (θ y.out)⁻¹ : G) : G ⧸ K)
      invFun := fun y => ((θ g * (θ y.out)⁻¹ : G) : G ⧸ K)
      left_inv := fun y => heckecomm_coset_inv K θ hm hi hK g y
      right_inv := fun y => by
        have := heckecomm_coset_inv K θ hm hi hK (θ g) y
        rwa [hi] at this }
  unfold conv
  conv_rhs => rw [← finsum_comp_equiv e]
  refine finsum_congr fun y => ?_
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K (g * (θ y.out)⁻¹)
  have he : (e y).out = g * (θ y.out)⁻¹ * c := hc
  rw [he, mul_comm (f₁ _)]
  have h1 : (g * (θ y.out)⁻¹ * c)⁻¹ * g = (c⁻¹ : K) * θ y.out * (1 : K) := by
    simp only [Subgroup.coe_inv, OneMemClass.coe_one, mul_one]
    group
  have h2 : g * (θ y.out)⁻¹ * c = (1 : K) * (g * (θ y.out)⁻¹) * c := by
    simp only [OneMemClass.coe_one, one_mul]
  rw [h1, hf₁, hθf _ hf₁, h2, hf₂, ← hθf _ hf₂, hm, hinv, hi]

end Gelfand

section Transpose

variable {R : Type} [CommRing R] {n : ℕ}

def heckecomm_tr (g : GL (Fin n) R) : GL (Fin n) R :=
  ⟨Matrix.transpose (g : Matrix (Fin n) (Fin n) R), Matrix.transpose ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R),
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem heckecomm_tr_val (g : GL (Fin n) R) :
    ((heckecomm_tr g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = Matrix.transpose (g : Matrix (Fin n) (Fin n) R) := rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.
-/
theorem heckecomm_tr_mul (x y : GL (Fin n) R) :
    heckecomm_tr (x * y) = heckecomm_tr y * heckecomm_tr x := by
  apply Units.ext
  simp only [heckecomm_tr_val, Units.val_mul, Matrix.transpose_mul]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.
-/
theorem heckecomm_tr_tr (x : GL (Fin n) R) : heckecomm_tr (heckecomm_tr x) = x := by
  apply Units.ext
  simp only [heckecomm_tr_val, Matrix.transpose_transpose]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem heckecomm_tr_mem {L : Type} [Field L] (O : Subring L) (x : GL (Fin n) L)
    (hx : x ∈ GLint (Fin n) O) : heckecomm_tr x ∈ GLint (Fin n) O := by
  obtain ⟨h, rfl⟩ := hx
  refine ⟨heckecomm_tr h, ?_⟩
  apply Units.ext
  ext i j
  simp [bc, heckecomm_tr_val]

end Transpose

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem heckecomm_tr_dc (hC : CartanDecomp) (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (g : GL (Fin n) (v.adicCompletion F)) :
    ∃ a b : GLint (Fin n) (Ov F v), heckecomm_tr g = (a : GL (Fin n) (v.adicCompletion F)) * g * b := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hϖO : (π : v.adicCompletion F) ∈ Ov F v := by
    show Valued.v (π : v.adicCompletion F) ≤ 1
    rw [HeightOneSpectrum.adicCompletion.valued_coe, hπ]
    exact (WithZero.exp_le_exp.mpr (by norm_num : (-1:ℤ) ≤ 0)).trans (le_of_eq WithZero.exp_zero)
  have hϖU : IsUnifV F v (π : v.adicCompletion F) := by
    unfold IsUnifV
    rw [HeightOneSpectrum.adicCompletion.valued_coe, hπ]
    rfl
  obtain ⟨a, -, k₁, hk₁, k₂, hk₂, e⟩ := hC F v n _ hϖO hϖU g
  obtain ⟨D, hDdef⟩ : ∃ D : GL (Fin n) (v.adicCompletion F), D = k₁⁻¹ * g * k₂⁻¹ := ⟨_, rfl⟩
  have hD : (D : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = diagPow F v (π : v.adicCompletion F) a := by
    rw [hDdef]
    simp only [Units.val_mul, e, mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, mul_one]
  have hDt : heckecomm_tr D = D := by
    apply Units.ext
    rw [heckecomm_tr_val, hD]
    exact Matrix.diagonal_transpose _
  have hg : g = k₁ * D * k₂ := by rw [hDdef]; group
  have hK := heckecomm_tr_mem (n := n) (Ov F v)
  refine ⟨⟨heckecomm_tr k₂ * k₁⁻¹, (GLint (Fin n) (Ov F v)).mul_mem (hK _ hk₂)
      ((GLint (Fin n) (Ov F v)).inv_mem hk₁)⟩,
    ⟨k₂⁻¹ * heckecomm_tr k₁, (GLint (Fin n) (Ov F v)).mul_mem ((GLint (Fin n) (Ov F v)).inv_mem hk₂)
      (hK _ hk₁)⟩, ?_⟩
  conv_lhs => rw [hg]
  rw [heckecomm_tr_mul, heckecomm_tr_mul, hDt, hDdef]
  simp only
  group

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem hecke_algebra_GL_comm_of_cartan (hCartanDecomp : Formalism.UG.CartanDecomp) : Formalism.UG.HeckeCommGL := by
  intro F _ _ v n k _ f₁ hf₁ f₂ hf₂
  exact heckecomm_gelfand _ heckecomm_tr heckecomm_tr_mul heckecomm_tr_tr
    (heckecomm_tr_mem (Ov F v)) (heckecomm_tr_dc hCartanDecomp F v n) f₁ f₂ hf₁.1 hf₂.1

end Formalism.UG.P
