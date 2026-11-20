import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SesqAsym
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbCent

section Mat

variable {R : Type} [CommRing R] {a : ℕ}

def sf (c : R →+* R) (G : Matrix (Fin a) (Fin a) R) (u v : Fin a → R) : R := u ⬝ᵥ (G *ᵥ (c ∘ v))

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((invT a R g)⁻¹).valᵀ = g.val`. Rewrite using `[← map_inv]`. Express the relevant statement in the definitionally equal form `((g⁻¹)⁻¹).valᵀᵀ = g.val`. Simplify using the standard rewrite rules.
-/
theorem invT_invT (g : GL (Fin a) R) : invT a R (invT a R g) = g := by
  apply Units.ext
  change ((invT a R g)⁻¹).valᵀ = g.val
  rw [← map_inv]
  change ((g⁻¹)⁻¹).valᵀᵀ = g.val
  simp

/- English proof (translation)
Introduce `x y h` and use `by rw [← invT_invT x, h, invT_invT]`.
-/
theorem invT_injective : Function.Injective (invT a R) := fun x y h => by
  rw [← invT_invT x, h, invT_invT]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, map_sum, map_mul, RingHom.mapMatrix_apply]`.
-/
theorem comp_mulVec (c : R →+* R) (M : Matrix (Fin a) (Fin a) R) (v : Fin a → R) :
    c ∘ (M *ᵥ v) = c.mapMatrix M *ᵥ (c ∘ v) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul, RingHom.mapMatrix_apply]

/- English proof (translation)
Unfold `sf`. Rewrite using `[comp_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec _ Tᵀ, Matrix.dotProduct_mulVec u Tᵀ, Matrix.vecMul_transpose]`.
-/
theorem sf_mulVec (c : R →+* R) (G T : Matrix (Fin a) (Fin a) R) (u v : Fin a → R) :
    sf c G (T *ᵥ u) (T *ᵥ v) = sf c (Tᵀ * G * c.mapMatrix T) u v := by
  unfold sf
  rw [comp_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec _ Tᵀ, Matrix.dotProduct_mulVec u Tᵀ,
    Matrix.vecMul_transpose]

/- English proof (translation)
Use extensionality with `i j`. Establish `hs : c ∘ (Pi.single j (1 : R) : Fin a → R) = Pi.single j 1`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hk]`. Use `h (Pi.single i 1) (Pi.single j 1)` as an intermediate fact. Simplify `this` using `[sf, hs, Matrix.mulVec_single_one]`.
-/
theorem ext_sf (c : R →+* R) (G G' : Matrix (Fin a) (Fin a) R) (h : ∀ u v, sf c G u v = sf c G' u v) : G = G' := by
  ext i j
  have hs : c ∘ (Pi.single j (1 : R) : Fin a → R) = Pi.single j 1 := by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [sf, hs, Matrix.mulVec_single_one] using this

/- English proof (translation)
Use `set N := δ * PhiU a R with hN`. Use `set X := GeneralLinearGroup.map c t with hX`. Use `set G₀ := ((δ.val * GlobalTheory.Tw.Phi a R)⁻¹)ᵀ with hG₀`. Establish `hA1 : t ∈ twCent (thetaGL a c) δ ↔ t * N = N * invT a R X`. Express the relevant statement in the definitionally equal form `t * δ = δ * (PhiU a R * invT a R X * (PhiU a R)⁻¹) ↔ _`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[hN, ← mul_assoc, h]`. Use `group`. Introduce `h`.

Establish `e1 : t * δ = t * N * (PhiU a R)⁻¹` using `by rw [hN]; group`. Rewrite using `[e1, h, hN]`. Use `group`. Establish `hA2 : t * N = N * invT a R X ↔ invT a R t * invT a R N = invT a R N * X`. Use `Iff.trans (invT_injective (a := a) (R := R)).eq_iff.symm ?_` and prove the remaining obligations.

Rewrite using `[map_mul (invT a R) t N, map_mul (invT a R) N, invT_invT]`. Establish `hG : (invT a R N).val = G₀`. Express the relevant statement in the definitionally equal form `((N⁻¹).val)ᵀ = _`. Rewrite using `[Matrix.coe_units_inv]`. Both sides reduce to the same expression.

Establish `hB : invT a R t * invT a R N = invT a R N * X ↔ ((t⁻¹ : GL (Fin a) R).val)ᵀ * G₀ = G₀ * c.mapMatrix t.val`. Rewrite using `[Units.ext_iff, Units.val_mul, Units.val_mul, hG]`. Both sides reduce to the same expression. Establish `hC : ((t⁻¹ : GL (Fin a) R).val)ᵀ * G₀ = G₀ * c.mapMatrix t.val ↔ t.valᵀ * G₀ * c.mapMatrix t.val = G₀`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite using `[Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.one_mul]`. Introduce `h conv_lhs => rw [← h]`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]`. Rewrite using `[hA1, hA2, hB, hC]`.

Simplify using `only [sf_mulVec]`. Conclude with `⟨fun h u v => by rw [h], fun h => ext_sf c _ _ h⟩`.
-/
theorem mem_twCent_iff (c : R →+* R) (δ t : GL (Fin a) R) :
    t ∈ twCent (thetaGL a c) δ ↔
      ∀ u v, sf c ((δ.val * GlobalTheory.Tw.Phi a R)⁻¹)ᵀ (t.val *ᵥ u) (t.val *ᵥ v) = sf c ((δ.val * GlobalTheory.Tw.Phi a R)⁻¹)ᵀ u v := by
  set N := δ * PhiU a R with hN
  set X := GeneralLinearGroup.map c t with hX
  set G₀ := ((δ.val * GlobalTheory.Tw.Phi a R)⁻¹)ᵀ with hG₀
  have hA1 : t ∈ twCent (thetaGL a c) δ ↔ t * N = N * invT a R X := by
    change t * δ = δ * (PhiU a R * invT a R X * (PhiU a R)⁻¹) ↔ _
    constructor
    · intro h
      rw [hN, ← mul_assoc, h]
      group
    · intro h
      have e1 : t * δ = t * N * (PhiU a R)⁻¹ := by rw [hN]; group
      rw [e1, h, hN]
      group
  have hA2 : t * N = N * invT a R X ↔ invT a R t * invT a R N = invT a R N * X := by
    refine Iff.trans (invT_injective (a := a) (R := R)).eq_iff.symm ?_
    rw [map_mul (invT a R) t N, map_mul (invT a R) N, invT_invT]
  have hG : (invT a R N).val = G₀ := by
    change ((N⁻¹).val)ᵀ = _
    rw [Matrix.coe_units_inv]
    rfl
  have hB : invT a R t * invT a R N = invT a R N * X ↔ ((t⁻¹ : GL (Fin a) R).val)ᵀ * G₀ = G₀ * c.mapMatrix t.val := by
    rw [Units.ext_iff, Units.val_mul, Units.val_mul, hG]
    rfl
  have hC : ((t⁻¹ : GL (Fin a) R).val)ᵀ * G₀ = G₀ * c.mapMatrix t.val ↔ t.valᵀ * G₀ * c.mapMatrix t.val = G₀ := by
    constructor
    · intro h
      rw [Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
        Matrix.one_mul]
    · intro h
      conv_lhs => rw [← h]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
        Matrix.one_mul]
  rw [hA1, hA2, hB, hC]
  simp only [sf_mulVec]
  exact ⟨fun h u v => by rw [h], fun h => ext_sf c _ _ h⟩

end Mat

section Alg

open GlobalTheory.UnitLemma

variable {K : UQ} (B : InvAlg K)

/- English proof (translation)
Simplify using `only [InvAlg.herm, mul_sub, sub_mul, map_sub]`.
-/
theorem herm_sub_left (x y z w : B.A) : B.herm x (y - z) w = B.herm x y w - B.herm x z w := by
  simp only [InvAlg.herm, mul_sub, sub_mul, map_sub]

/- English proof (translation)
Establish `h0 : (β : B.A) * x = 0`. Use `GlobalTheory.T.eq_zero_of_trace_mul_of_separable_generated K B hP (GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution K B hP) _ fun y => ?_` and prove the remaining obligations. Use `h (B.σ y)` as an intermediate fact. Simplify `this` using `[InvAlg.herm, B.σ_σ]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem herm_nondeg (hP : B.P.Separable) (β : B.Aˣ) (x : B.A) (h : ∀ z, B.herm β x z = 0) : x = 0 := by
  have h0 : (β : B.A) * x = 0 := by
    refine GlobalTheory.T.eq_zero_of_trace_mul_of_separable_generated K B hP (GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution K B hP) _ fun y => ?_
    have := h (B.σ y)
    simpa [InvAlg.herm, B.σ_σ] using this
  calc x = ((β⁻¹ : B.Aˣ) : B.A) * ((β : B.A) * x) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = 0 := by rw [h0, mul_zero]

/- English proof (translation)
Rewrite using `[InvAlg.herm, InvAlg.herm, ← GlobalTheory.SesqAsym.trace_σ, map_mul B.σ, map_mul B.σ, B.σ_σ, hβ]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_asym (β : B.Aˣ) (ε : B.A) (hβ : B.σ (β : B.A) = β * (ε * B.g)) (y z : B.A) :
    K.c (B.herm β z y) = B.herm β (ε * B.g * y) z := by
  rw [InvAlg.herm, InvAlg.herm, ← GlobalTheory.SesqAsym.trace_σ, map_mul B.σ, map_mul B.σ, B.σ_σ, hβ]
  congr 1
  ring

/- English proof (translation)
Establish `hεg : ∀ y, φ (ε * B.g * y) = ε * B.g * φ y`. Introduce `y`. Rewrite using `[← sub_eq_zero]`. Apply `herm_nondeg B hP β` to reduce the goal to its premises. Introduce `z'`.

Take `⟨z, rfl⟩` from `hsurj z'`. Rewrite using `[herm_sub_left, hφ, ← herm_asym B β ε hβ, ← hφ z y, herm_asym B β ε hβ, sub_self]`. Establish `hg : ∀ y, φ (B.g * y) = B.g * φ y`. Introduce `y`. Break down `hε with rfl | rfl` into its components or cases.

Simplify using `using hεg y`. Use `hεg y` as an intermediate fact. Simplify using `only [neg_mul, one_mul, map_neg] at this`. Conclude with `neg_injective this`. Establish `hall : ∀ c y, φ (c * y) = c * φ y`.

Introduce `c`. Take `⟨f, rfl⟩` from `GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution K B hP c`. Proceed by induction on `f using Polynomial.induction_on with`. Consider the case `C e`. Introduce `y`.

Rewrite using `[aeval_C, ← Algebra.smul_def, ← Algebra.smul_def, hsm]`. Consider the case `add p q hp hq`. Introduce `y`. Rewrite using `[map_add, add_mul, map_add, hp, hq, add_mul]`. Consider the case `monomial n e ih`.

Introduce `y`. Rewrite using `[pow_succ, ← mul_assoc, map_mul (aeval B.g), aeval_X, mul_assoc (aeval B.g (C e * X ^ n)) B.g y, ih, hg, ← mul_assoc]`. Establish `hmul : ∀ y, φ y = φ 1 * y`. Introduce `y`. Rewrite using `[mul_comm, ← hall, mul_one]`.

Use `⟨?_, hmul⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Apply `herm_nondeg B hP β` to reduce the goal to its premises. Introduce `z`. Establish `h1` using `hφ 1 z`.

Rewrite `h1` using `[hmul z]`. Rewrite using `[herm_sub_left]`. Simplify using `only [InvAlg.herm, map_mul, map_one, mul_one] at h1 ⊢`. Rewrite using `[← h1, sub_eq_zero]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem isometry_eq_mul (hP : B.P.Separable) (β : B.Aˣ) (ε : B.A) (hε : ε = 1 ∨ ε = -1)
    (hβ : B.σ (β : B.A) = β * (ε * B.g)) (φ : B.A →+ B.A) (hsm : ∀ (c : K.E) y, φ (c • y) = c • φ y)
    (hsurj : Function.Surjective φ) (hφ : ∀ y z, B.herm β (φ y) (φ z) = B.herm β y z) :
    φ 1 * B.σ (φ 1) = 1 ∧ ∀ y, φ y = φ 1 * y := by
  have hεg : ∀ y, φ (ε * B.g * y) = ε * B.g * φ y := by
    intro y
    rw [← sub_eq_zero]
    apply herm_nondeg B hP β
    intro z'
    obtain ⟨z, rfl⟩ := hsurj z'
    rw [herm_sub_left, hφ, ← herm_asym B β ε hβ, ← hφ z y, herm_asym B β ε hβ, sub_self]
  have hg : ∀ y, φ (B.g * y) = B.g * φ y := by
    intro y
    rcases hε with rfl | rfl
    · simpa using hεg y
    · have := hεg y
      simp only [neg_mul, one_mul, map_neg] at this
      exact neg_injective this
  have hall : ∀ c y, φ (c * y) = c * φ y := by
    intro c
    obtain ⟨f, rfl⟩ := GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution K B hP c
    induction f using Polynomial.induction_on with
    | C e =>
      intro y
      rw [aeval_C, ← Algebra.smul_def, ← Algebra.smul_def, hsm]
    | add p q hp hq =>
      intro y
      rw [map_add, add_mul, map_add, hp, hq, add_mul]
    | monomial n e ih =>
      intro y
      rw [pow_succ, ← mul_assoc, map_mul (aeval B.g), aeval_X, mul_assoc (aeval B.g (C e * X ^ n)) B.g y, ih, hg,
        ← mul_assoc]
  have hmul : ∀ y, φ y = φ 1 * y := by
    intro y
    rw [mul_comm, ← hall, mul_one]
  refine ⟨?_, hmul⟩
  rw [← sub_eq_zero]
  apply herm_nondeg B hP β
  intro z
  have h1 := hφ 1 z
  rw [hmul z] at h1
  rw [herm_sub_left]
  simp only [InvAlg.herm, map_mul, map_one, mul_one] at h1 ⊢
  rw [← h1, sub_eq_zero]
  congr 1
  ring

end Alg

section Crd

open GlobalTheory.UnitLemma GlobalTheory.TwOrbLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : UQ}
  (e : K.E ≃+* w.adicCompletion E) {a : ℕ} {B : InvAlg K} (b : Module.Basis (Fin a) K.E B.A)

/- English proof (translation)
Simplify using `only [InvAlg.herm, Finset.mul_sum, Finset.sum_mul, map_sum]`.
-/
theorem herm_sum_left (x z : B.A) (s : Finset (Fin a)) (f : Fin a → B.A) :
    B.herm x (∑ i ∈ s, f i) z = ∑ i ∈ s, B.herm x (f i) z := by
  simp only [InvAlg.herm, Finset.mul_sum, Finset.sum_mul, map_sum]

/- English proof (translation)
Simplify using `only [InvAlg.herm, map_sum B.σ, Finset.mul_sum, map_sum]`.
-/
theorem herm_sum_right (x y : B.A) (s : Finset (Fin a)) (f : Fin a → B.A) :
    B.herm x y (∑ i ∈ s, f i) = ∑ i ∈ s, B.herm x y (f i) := by
  simp only [InvAlg.herm, map_sum B.σ, Finset.mul_sum, map_sum]

/- English proof (translation)
Simplify using `only [InvAlg.herm, mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]`.
-/
theorem herm_smul_left (x y z : B.A) (c : K.E) : B.herm x (c • y) z = c * B.herm x y z := by
  simp only [InvAlg.herm, mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]

/- English proof (translation)
Establish `h : B.σ (c • z) = K.c c • B.σ z`. Rewrite using `[Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]`. Simplify using `only [InvAlg.herm, h, mul_smul_comm, map_smul, smul_eq_mul]`.
-/
theorem herm_smul_right (x y z : B.A) (c : K.E) : B.herm x y (c • z) = K.c c * B.herm x y z := by
  have h : B.σ (c • z) = K.c c • B.σ z := by
    rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]
  simp only [InvAlg.herm, h, mul_smul_comm, map_smul, smul_eq_mul]

/- English proof (translation)
Use `conv_lhs => rw [← b.sum_repr y, ← b.sum_repr z]`. Rewrite using `[herm_sum_left]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[herm_sum_right]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[herm_smul_left, herm_smul_right]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_basis (x y z : B.A) :
    B.herm x y z = ∑ i, ∑ j, b.repr y i * B.herm x (b i) (b j) * K.c (b.repr z j) := by
  conv_lhs => rw [← b.sum_repr y, ← b.sum_repr z]
  rw [herm_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [herm_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [herm_smul_left, herm_smul_right]
  ring

/- English proof (translation)
Rewrite using `[herm_basis b, map_sum]`. Simplify using `only [sf, dotProduct, Matrix.mulVec, Function.comp_apply, crd, hG, ← he, Finset.mul_sum, map_sum, map_mul]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sf_crd (c : w.adicCompletion E →+* w.adicCompletion E) (he : ∀ x, e (K.c x) = c (e x))
    (G : Matrix (Fin a) (Fin a) (w.adicCompletion E)) (β : B.A) (hG : ∀ i j, G i j = e (B.herm β (b i) (b j)))
    (y z : B.A) : sf c G (crd e b y) (crd e b z) = e (B.herm β y z) := by
  rw [herm_basis b, map_sum]
  simp only [sf, dotProduct, Matrix.mulVec, Function.comp_apply, crd, hG, ← he, Finset.mul_sum, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[crd]`.
-/
theorem crd_zero : crd e b (0 : B.A) = 0 := by
  funext i; simp [crd]

/- English proof (translation)
Apply `crd_injective e b` to reduce the goal to its premises. Rewrite using `[crd_add, crd_ofCrd, crd_ofCrd, crd_ofCrd]`.
-/
theorem ofCrd_add (u v : Fin a → w.adicCompletion E) : ofCrd e b (u + v) = ofCrd e b u + ofCrd e b v := by
  apply crd_injective e b
  rw [crd_add, crd_ofCrd, crd_ofCrd, crd_ofCrd]

end Crd

open GlobalTheory.UnitLemma GlobalTheory.TwOrbLat in

/- English proof (translation)
Introduce `E _ _ _ w hw K e he a B hP β ε hε hβ b δ hG`. Establish `hth : thL a w = thetaGL a (cj w)`. Unfold `thL`. Rewrite using `[if_neg hw]`. Rewrite using `[hth]`.

Establish `hs` using `sf_crd e b (cj w) he _ (β : B.A) hG`. Use extensionality with `g`. Rewrite using `[mem_twCent_iff, Subgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce `hg`.

Set `φ : B.A →+ B.A` to `{ toFun := fun y => ofCrd e b (g.val *ᵥ crd e b y) map_zero' := by`. Apply `crd_injective e b` to reduce the goal to its premises. Rewrite using `[crd_ofCrd, crd_zero, Matrix.mulVec_zero]`. Use the proof step `map_add' := fun y z => by`. Rewrite using `[crd_add, Matrix.mulVec_add, ofCrd_add] }`.

Establish `hcφ : ∀ y, crd e b (φ y) = g.val *ᵥ crd e b y` using `fun y => crd_ofCrd e b _`. Establish `hsm : ∀ (c : K.E) y, φ (c • y) = c • φ y`. Introduce `c y`. Apply `crd_injective e b` to reduce the goal to its premises. Rewrite using `[hcφ, crd_smul, crd_smul, hcφ, Matrix.mulVec_smul]`.

Establish `hsurj : Function.Surjective φ`. Introduce `y'`. Use `⟨ofCrd e b ((g⁻¹ : GLw a w).val *ᵥ crd e b y'), ?_⟩` and prove the remaining obligations. Apply `crd_injective e b` to reduce the goal to its premises. Rewrite using `[hcφ, crd_ofCrd, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`.

Establish `hφ : ∀ y z, B.herm β (φ y) (φ z) = B.herm β y z`. Introduce `y z`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[← hs, ← hs, hcφ, hcφ, hg]`. Take `⟨h1, h2⟩` from `isometry_eq_mul B hP β ε hε hβ φ hsm hsurj hφ`.

Use `⟨Units.mkOfMulEqOne (φ 1) (B.σ (φ 1)) h1, h1, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `mulHom e b (φ 1) = g.val`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.toLin'_apply, Matrix.toLin'_apply, ← crd_ofCrd e b v, ← crd_mul, ← h2, hcφ]`. Introduce and unpack `⟨t, ht, rfl⟩ u v`. Express the relevant statement in the definitionally equal form `sf (cj w) _ (mulHom e b (t : B.A) *ᵥ u) (mulHom e b (t : B.A) *ᵥ v) = _`. Rewrite using `[← crd_ofCrd e b u, ← crd_ofCrd e b v, ← crd_mul, ← crd_mul, hs, hs]`. Use `congr 1`.

Establish `ht' : (t : B.A) * B.σ (t : B.A) = 1` using `ht`. Simplify using `only [InvAlg.herm, map_mul]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem twCent_eq_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (β : B.Aˣ) (ε : B.A), (ε = 1 ∨ ε = -1) → B.σ (β : B.A) = β * (ε * B.g) → ∀ (b : Module.Basis (Fin a) K.E B.A) (δ : GLw a w), (∀ i j, ((δ.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ i j = e (B.herm β (b i) (b j))) → twCent (thL a w) δ = B.T.map (GlobalTheory.TwOrbLat.mulGL e b) := by
  intro E _ _ _ w hw K e he a B hP β ε hε hβ b δ hG
  have hth : thL a w = thetaGL a (cj w) := by
    unfold thL
    rw [if_neg hw]
  rw [hth]
  have hs := sf_crd e b (cj w) he _ (β : B.A) hG
  ext g
  rw [mem_twCent_iff, Subgroup.mem_map]
  constructor
  · intro hg
    let φ : B.A →+ B.A :=
      { toFun := fun y => ofCrd e b (g.val *ᵥ crd e b y)
        map_zero' := by
          apply crd_injective e b
          rw [crd_ofCrd, crd_zero, Matrix.mulVec_zero]
        map_add' := fun y z => by
          rw [crd_add, Matrix.mulVec_add, ofCrd_add] }
    have hcφ : ∀ y, crd e b (φ y) = g.val *ᵥ crd e b y := fun y => crd_ofCrd e b _
    have hsm : ∀ (c : K.E) y, φ (c • y) = c • φ y := by
      intro c y
      apply crd_injective e b
      rw [hcφ, crd_smul, crd_smul, hcφ, Matrix.mulVec_smul]
    have hsurj : Function.Surjective φ := by
      intro y'
      refine ⟨ofCrd e b ((g⁻¹ : GLw a w).val *ᵥ crd e b y'), ?_⟩
      apply crd_injective e b
      rw [hcφ, crd_ofCrd, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have hφ : ∀ y z, B.herm β (φ y) (φ z) = B.herm β y z := by
      intro y z
      apply e.injective
      rw [← hs, ← hs, hcφ, hcφ, hg]
    obtain ⟨h1, h2⟩ := isometry_eq_mul B hP β ε hε hβ φ hsm hsurj hφ
    refine ⟨Units.mkOfMulEqOne (φ 1) (B.σ (φ 1)) h1, h1, ?_⟩
    apply Units.ext
    change mulHom e b (φ 1) = g.val
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← crd_ofCrd e b v, ← crd_mul, ← h2, hcφ]
  · rintro ⟨t, ht, rfl⟩ u v
    change sf (cj w) _ (mulHom e b (t : B.A) *ᵥ u) (mulHom e b (t : B.A) *ᵥ v) = _
    rw [← crd_ofCrd e b u, ← crd_ofCrd e b v, ← crd_mul, ← crd_mul, hs, hs]
    congr 1
    have ht' : (t : B.A) * B.σ (t : B.A) = 1 := ht
    simp only [InvAlg.herm, map_mul]
    congr 1
    calc (β : B.A) * ((t : B.A) * ofCrd e b u) * (B.σ (t : B.A) * B.σ (ofCrd e b v))
        = (β : B.A) * ofCrd e b u * B.σ (ofCrd e b v) * ((t : B.A) * B.σ (t : B.A)) := by ring
      _ = _ := by rw [ht', mul_one]

end GlobalTheory.TwOrbCent
