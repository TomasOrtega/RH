import Formalism.SatakeDualWeyl.StatementE
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeConvolutionMemHolds

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section Gelfand

variable {G : Type} [Group G]

/- English proof (translation)
Establish `h` using `hm 1 1`. Rewrite `h` using `[mul_one]`. Establish `h' : θ 1 * θ 1 = θ 1 * 1` using `by rw [mul_one, ← h]`. Conclude with `mul_left_cancel h'`.
-/
theorem heckecomm_theta_one (θ : G → G) (hm : ∀ x y, θ (x * y) = θ y * θ x) : θ 1 = 1 := by
  have h := hm 1 1
  rw [mul_one] at h
  have h' : θ 1 * θ 1 = θ 1 * 1 := by rw [mul_one, ← h]
  exact mul_left_cancel h'

/- English proof (translation)
Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← hm, mul_inv_cancel, heckecomm_theta_one θ hm]`.
-/
theorem heckecomm_theta_inv (θ : G → G) (hm : ∀ x y, θ (x * y) = θ y * θ x) (x : G) :
    θ x⁻¹ = (θ x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← hm, mul_inv_cancel, heckecomm_theta_one θ hm]

/- English proof (translation)
Take `⟨c, hc⟩` from `QuotientGroup.mk_out_eq_mul K (h * (θ y.out)⁻¹)`. Rewrite using `[hc]`. Use `conv_rhs => rw [← QuotientGroup.out_eq' y]`. Rewrite using `[QuotientGroup.eq]`. Establish `hinv` using `heckecomm_theta_inv θ hm`.

Rewrite using `[hm, hm, hinv, hi]`. Use `hK _ c.2 using 1` and compare the differences between its conclusion and the goal. Use `group`.
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
Establish `hθf : ∀ f : G → k, IsBiInv K f → ∀ x, f (θ x) = f x`. Introduce `f hf x`. Take `⟨a, b, e⟩` from `hdc x`. Rewrite using `[e, hf]`. Establish `hinv` using `heckecomm_theta_inv θ hm`.

Use function extensionality and compare the values at `g`. Rewrite using `[← hθf _ (conv_biInv K f₁ f₂ hf₁ hf₂) g]`. Set `e : G ⧸ K ≃ G ⧸ K` to `{ toFun := fun y => ((g * (θ y.out)⁻¹ : G) : G ⧸ K) invFun := fun y => ((θ g * (θ y.out)⁻¹ : G) : G ⧸ K) left_inv := fun y => heckecomm_coset_inv K θ hm hi hK g y right_inv := fun y => by`. Use `heckecomm_coset_inv K θ hm hi hK (θ g) y` as an intermediate fact. Rewrite using `[hi] at this }` and apply the resulting hypothesis.

Unfold `conv`. Use `conv_rhs => rw [← finsum_comp_equiv e]`. Use `finsum_congr fun y => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `QuotientGroup.mk_out_eq_mul K (g * (θ y.out)⁻¹)`. Establish `he : (e y).out = g * (θ y.out)⁻¹ * c` using `hc`.

Rewrite using `[he, mul_comm (f₁ _)]`. Establish `h1 : (g * (θ y.out)⁻¹ * c)⁻¹ * g = (c⁻¹ : K) * θ y.out * (1 : K)`. Simplify using `only [Subgroup.coe_inv, OneMemClass.coe_one, mul_one]`. Use `group`. Establish `h2 : g * (θ y.out)⁻¹ * c = (1 : K) * (g * (θ y.out)⁻¹) * c`.

Simplify using `only [OneMemClass.coe_one, one_mul]`. Rewrite using `[h1, hf₁, hθf _ hf₁, h2, hf₂, ← hθf _ hf₂, hm, hinv, hi]`.
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
Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [heckecomm_tr_val, Units.val_mul, Matrix.transpose_mul]`.
-/
theorem heckecomm_tr_mul (x y : GL (Fin n) R) :
    heckecomm_tr (x * y) = heckecomm_tr y * heckecomm_tr x := by
  apply Units.ext
  simp only [heckecomm_tr_val, Units.val_mul, Matrix.transpose_mul]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [heckecomm_tr_val, Matrix.transpose_transpose]`.
-/
theorem heckecomm_tr_tr (x : GL (Fin n) R) : heckecomm_tr (heckecomm_tr x) = x := by
  apply Units.ext
  simp only [heckecomm_tr_val, Matrix.transpose_transpose]

/- English proof (translation)
Take `⟨h, rfl⟩` from `hx`. Use `⟨heckecomm_tr h, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Simplify using `[bc, heckecomm_tr_val]`.
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
Take `⟨π, hπ⟩` from `v.valuation_exists_uniformizer F`. Establish `hϖO : (π : v.adicCompletion F) ∈ Ov F v` using `by show Valued.v (π : v.adicCompletion F) ≤ 1`. Rewrite using `[HeightOneSpectrum.adicCompletion.valued_coe, hπ]`. Conclude with `(WithZero.exp_le_exp.mpr (by norm_num : (-1:ℤ) ≤ 0)).trans (le_of_eq WithZero.exp_zero)`. Establish `hϖU : IsUnifV F v (π : v.adicCompletion F)`.

Unfold `IsUnifV`. Rewrite using `[HeightOneSpectrum.adicCompletion.valued_coe, hπ]`. Both sides reduce to the same expression. Take `⟨a, -, k₁, hk₁, k₂, hk₂, e⟩` from `hC F v n _ hϖO hϖU g`. Take `⟨D, hDdef⟩ : ∃ D : GL (Fin n) (v.adicCompletion F), D = k₁⁻¹ * g * k₂⁻¹` from `⟨_, rfl⟩`.

Establish `hD : (D : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = diagPow F v (π : v.adicCompletion F) a`. Rewrite using `[hDdef]`. Simplify using `only [Units.val_mul, e, mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, mul_one]`. Establish `hDt : heckecomm_tr D = D`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[heckecomm_tr_val, hD]`. Conclude with `Matrix.diagonal_transpose _`. Establish `hg : g = k₁ * D * k₂` using `by rw [hDdef]; group`. Establish `hK` using `heckecomm_tr_mem (n := n) (Ov F v)`. Use `⟨⟨heckecomm_tr k₂ * k₁⁻¹, (GLint (Fin n) (Ov F v)).mul_mem (hK _ hk₂) ((GLint (Fin n) (Ov F v)).inv_mem hk₁)⟩, ⟨k₂⁻¹ * heckecomm_tr k₁, (GLint (Fin n) (Ov F v)).mul_mem ((GLint (Fin n) (Ov F v)).inv_mem hk₂) (hK _ hk₁)⟩, ?_⟩` and prove the remaining obligations.

Use `conv_lhs => rw [hg]`. Rewrite using `[heckecomm_tr_mul, heckecomm_tr_mul, hDt, hDdef]`. Simplify using `only`. Use `group`.
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
Introduce `F _ _ v n k _ f₁ hf₁ f₂ hf₂`. Conclude with `heckecomm_gelfand _ heckecomm_tr heckecomm_tr_mul heckecomm_tr_tr (heckecomm_tr_mem (Ov F v)) (heckecomm_tr_dc hCartanDecomp F v n) f₁ f₂ hf₁.1 hf₂.1`.
-/
theorem hecke_algebra_GL_comm_of_cartan (hCartanDecomp : Formalism.UG.CartanDecomp) : Formalism.UG.HeckeCommGL := by
  intro F _ _ v n k _ f₁ hf₁ f₂ hf₂
  exact heckecomm_gelfand _ heckecomm_tr heckecomm_tr_mul heckecomm_tr_tr
    (heckecomm_tr_mem (Ov F v)) (heckecomm_tr_dc hCartanDecomp F v n) f₁ f₂ hf₁.1 hf₂.1

end Formalism.UG.P
