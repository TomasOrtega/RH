import Mathlib
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.QuasiRefl

open HeckeCharacterZeroLocus.SiegelWeilU

section Form

variable {A : Type} [CommRing A] {n : Type} [Fintype n] {σ : A →+* A} {J : Matrix n n A}

/- English proof (translation)
Simplify using `[hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem hform_eq_dot (x y : n → A) : hform σ J x y = (σ ∘ x) ⬝ᵥ J *ᵥ y := by
  simp [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[mulVec, dotProduct]`.
-/
theorem comp_mulVec' (P : Matrix n n A) (x : n → A) : σ ∘ (P *ᵥ x) = P.map σ *ᵥ (σ ∘ x) := by
  funext i
  simp [mulVec, dotProduct]

/- English proof (translation)
Rewrite using `[hform_eq_dot, hform_eq_dot, comp_mulVec', cT, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec _ (_ᵀ), vecMul_transpose]`.
-/
theorem hform_mulVec' (P Q : Matrix n n A) (x y : n → A) :
    hform σ J (P *ᵥ x) (Q *ᵥ y) = hform σ (cT σ P * J * Q) x y := by
  rw [hform_eq_dot, hform_eq_dot, comp_mulVec', cT, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec _ (_ᵀ), vecMul_transpose]

/- English proof (translation)
Simplify using `[hform, Finset.mul_sum, sub_mul, mul_assoc]`.
-/
theorem hform_sub_left (x d y : n → A) (c : A) :
    hform σ J (x - c • d) y = hform σ J x y - σ c * hform σ J d y := by
  simp [hform, Finset.mul_sum, sub_mul, mul_assoc]

/- English proof (translation)
Simplify using `[hform, Finset.mul_sum, mul_sub, mul_left_comm]`.
-/
theorem hform_sub_right (x d y : n → A) (c : A) :
    hform σ J x (y - c • d) = hform σ J x y - c * hform σ J x d := by
  simp [hform, Finset.mul_sum, mul_sub, mul_left_comm]

/- English proof (translation)
Simplify using `[hform, Finset.mul_sum, mul_left_comm]`.
-/
theorem hform_smul_right' (d y : n → A) (c : A) :
    hform σ J y (c • d) = c * hform σ J y d := by
  simp [hform, Finset.mul_sum, mul_left_comm]

/- English proof (translation)
Simplify using `only [hform, map_sum, map_mul, hσ, hJ]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem hform_conj_symm (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x y : n → A) :
    σ (hform σ J x y) = hform σ J y x := by
  simp only [hform, map_sum, map_mul, hσ, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Form

section Refl

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {σ : A →+* A}
  {J : Matrix n n A}

def qrMat (σ : A →+* A) (J : Matrix n n A) (d : n → A) (c : A) : Matrix n n A :=
  1 - c • vecMulVec d ((σ ∘ d) ᵥ* J)

/- English proof (translation)
Rewrite using `[qrMat, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hform_eq_dot, dotProduct_mulVec]`. Use function extensionality and compare the values at `i`. Simplify using `[mul_comm, mul_left_comm]`.
-/
theorem qrMat_mulVec (d : n → A) (c : A) (z : n → A) :
    qrMat σ J d c *ᵥ z = z - (c * hform σ J d z) • d := by
  rw [qrMat, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hform_eq_dot, dotProduct_mulVec]
  funext i
  simp [mul_comm, mul_left_comm]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `using congrFun (h (Pi.single j 1)) i`.
-/
theorem ext_mulVec' {P Q : Matrix n n A} (h : ∀ z, P *ᵥ z = Q *ᵥ z) : P = Q := by
  ext i j
  simpa using congrFun (h (Pi.single j 1)) i

/- English proof (translation)
The claim follows from `ext_mulVec' fun z => by rw [← mulVec_mulVec, qrMat_mulVec, qrMat_mulVec, hform_sub_right, one_mulVec] funext i simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] linear_combination (-hform σ J d z * d i) * hc`.
-/
theorem qrMat_mul (d : n → A) {c c' : A} (hc : c + c' = c * c' * hform σ J d d) :
    qrMat σ J d c * qrMat σ J d c' = 1 := ext_mulVec' fun z => by
  rw [← mulVec_mulVec, qrMat_mulVec, qrMat_mulVec, hform_sub_right, one_mulVec]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-hform σ J d z * d i) * hc

/- English proof (translation)
Establish `: σ ∘ (Pi.single i 1 : n → A) = Pi.single i 1`. Use function extensionality and compare the values at `k`. Apply the tactic sequence `by_cases h : k = i <;> simp [h]`. Rewrite using `[hform_eq_dot, this]`. Simplify using the standard rewrite rules.
-/
theorem hform_single' (i j : n) :
    hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have : σ ∘ (Pi.single i 1 : n → A) = Pi.single i 1 := by
    funext k
    by_cases h : k = i <;> simp [h]
  rw [hform_eq_dot, this]
  simp

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[← hform_single' (σ := σ) (J := _ * J * _) i j, ← hform_mulVec', qrMat_mulVec, qrMat_mulVec, hform_sub_left, hform_sub_right, hform_sub_right, map_mul, hform_conj_symm hσ hJ, hform_single']`. Take the linear combination `(-hform σ J (Pi.single i 1) d * hform σ J d (Pi.single j 1)) * hc`.
-/
theorem qrMat_isometry (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (d : n → A) (c : A)
    (hc : c + σ c = c * σ c * hform σ J d d) :
    cT σ (qrMat σ J d c) * J * qrMat σ J d c = J := by
  ext i j
  rw [← hform_single' (σ := σ) (J := _ * J * _) i j, ← hform_mulVec', qrMat_mulVec, qrMat_mulVec,
    hform_sub_left, hform_sub_right, hform_sub_right, map_mul, hform_conj_symm hσ hJ,
    hform_single']
  linear_combination
    (-hform σ J (Pi.single i 1) d * hform σ J d (Pi.single j 1)) * hc

def qr (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (d : n → A) (c : A)
    (hc : c + σ c = c * σ c * hform σ J d d) : UJ σ J :=
  ⟨⟨qrMat σ J d c, qrMat σ J d (σ c), qrMat_mul d hc,
    qrMat_mul d (by linear_combination hc)⟩, qrMat_isometry hσ hJ d c hc⟩

end Refl

/- English proof (translation)
Take `⟨bi, hb⟩` from `hβ.exists_right_inv`. Take `⟨ui, hui⟩` from `hu.exists_right_inv`. Use `set β := hform σ J x x with hβdef`. Use `set w := hform σ J y x with hw`. Establish `hyy : hform σ J y y = β` using `hxy.symm`.

Establish `hxyw : hform σ J x y = σ w` using `by rw [hw, hform_conj_symm hσ hJ]`. Establish `hσβ : σ β = β` using `hform_conj_symm hσ hJ x x`. Establish `hσε : σ (σ ε) = ε` using `hσ ε`. Establish `hσb : σ bi = bi`. Establish `h1 : β * σ bi = 1`.

Use `congrArg σ hb` as an intermediate fact. Rewrite `this` using `[map_mul, hσβ, map_one]`. Then use the resulting hypothesis. Take the linear combination `bi * h1 - σ bi * hb`. Establish `hσui : (β - ε * σ w) * σ ui = 1`. Use `congrArg σ hui` as an intermediate fact.

Rewrite `this` using `[map_mul, map_sub, map_mul, hσβ, hσε, map_one]`. Then use the resulting hypothesis. Use `set d : Fin M → A := x - ε • y with hd`. Establish `hdx : hform σ J d x = β - σ ε * w` using `hform_sub_left x y x ε`. Establish `hdy : hform σ J d y = σ w - σ ε * β`. Rewrite using `[hd, hform_sub_left, hxyw, hyy]`.

Establish `hdd : hform σ J d d = (β - σ ε * w) + (β - ε * σ w) + (ε * σ ε - 1) * β`. Rewrite using `[hform_sub_right, hdx, hdy]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc₁ : (1 - σ ε) * bi + σ ((1 - σ ε) * bi) = (1 - σ ε) * bi * σ ((1 - σ ε) * bi) * hform σ J y y`. Rewrite using `[map_mul, map_sub, map_one, hσε, hσb, hyy]`.

Take the linear combination `(-(1 - ε - σ ε + ε * σ ε) * bi) * hb + (-bi) * hε`. Establish `hc₂ : ui + σ ui = ui * σ ui * hform σ J d d`. Rewrite using `[hdd, hε]`. Take the linear combination `(-σ ui) * hui + (-ui) * hσui`. Use `⟨((qr hσ hJ y _ hc₁ * qr hσ hJ d ui hc₂ : UJ σ J) : GL (Fin M) A), SetLike.coe_mem _, ?_, ?_⟩` and prove the remaining obligations.

Establish `h2 : qrMat σ J d ui *ᵥ x = ε • y`. Rewrite using `[qrMat_mulVec, hdx, mul_comm ui, hui, one_smul, hd]`. Simplify using the standard rewrite rules. Establish `h3 : qrMat σ J y ((1 - σ ε) * bi) *ᵥ (ε • y) = y`. Rewrite using `[qrMat_mulVec, hform_smul_right', hyy]`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Take the linear combination `((1 - σ ε) * ε * y i) * (-hb) + (y i) * hε`. Use `show (qrMat σ J y ((1 - σ ε) * bi) * qrMat σ J d ui) *ᵥ x = y`. Rewrite using `[← mulVec_mulVec, h2, h3]`.

Introduce `z hxz hyz`. Establish `hdz : hform σ J d z = 0`. Rewrite using `[hd, hform_sub_left, hxz, hyz]`. Simplify using the standard rewrite rules. Use `show (qrMat σ J y ((1 - σ ε) * bi) * qrMat σ J d ui) *ᵥ z = z`.

Establish `h2 : qrMat σ J d ui *ᵥ z = z`. Rewrite using `[qrMat_mulVec, hdz, mul_zero, zero_smul, sub_zero]`. Rewrite using `[← mulVec_mulVec, h2, qrMat_mulVec, hyz, mul_zero, zero_smul, sub_zero]`.
-/
theorem exists_unitary_carry (A : Type) [CommRing A] (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) A) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → A) (ε : A)
    (hxy : hform σ J x x = hform σ J y y) (hβ : IsUnit (hform σ J x x)) (hε : ε * σ ε = 1)
    (hu : IsUnit (hform σ J x x - σ ε * hform σ J y x)) :
    ∃ g ∈ UJ σ J, (g : Matrix (Fin M) (Fin M) A) *ᵥ x = y ∧
      ∀ z, hform σ J x z = 0 → hform σ J y z = 0 → (g : Matrix (Fin M) (Fin M) A) *ᵥ z = z := by
  obtain ⟨bi, hb⟩ := hβ.exists_right_inv
  obtain ⟨ui, hui⟩ := hu.exists_right_inv
  set β := hform σ J x x with hβdef
  set w := hform σ J y x with hw
  have hyy : hform σ J y y = β := hxy.symm
  have hxyw : hform σ J x y = σ w := by rw [hw, hform_conj_symm hσ hJ]
  have hσβ : σ β = β := hform_conj_symm hσ hJ x x
  have hσε : σ (σ ε) = ε := hσ ε
  have hσb : σ bi = bi := by
    have h1 : β * σ bi = 1 := by
      have := congrArg σ hb
      rwa [map_mul, hσβ, map_one] at this
    linear_combination bi * h1 - σ bi * hb
  have hσui : (β - ε * σ w) * σ ui = 1 := by
    have := congrArg σ hui
    rwa [map_mul, map_sub, map_mul, hσβ, hσε, map_one] at this
  set d : Fin M → A := x - ε • y with hd
  have hdx : hform σ J d x = β - σ ε * w := hform_sub_left x y x ε
  have hdy : hform σ J d y = σ w - σ ε * β := by
    rw [hd, hform_sub_left, hxyw, hyy]
  have hdd : hform σ J d d = (β - σ ε * w) + (β - ε * σ w) + (ε * σ ε - 1) * β := by
    rw [hform_sub_right, hdx, hdy]
    ring
  have hc₁ : (1 - σ ε) * bi + σ ((1 - σ ε) * bi)
      = (1 - σ ε) * bi * σ ((1 - σ ε) * bi) * hform σ J y y := by
    rw [map_mul, map_sub, map_one, hσε, hσb, hyy]
    linear_combination (-(1 - ε - σ ε + ε * σ ε) * bi) * hb + (-bi) * hε
  have hc₂ : ui + σ ui = ui * σ ui * hform σ J d d := by
    rw [hdd, hε]
    linear_combination (-σ ui) * hui + (-ui) * hσui
  refine ⟨((qr hσ hJ y _ hc₁ * qr hσ hJ d ui hc₂ : UJ σ J) : GL (Fin M) A), SetLike.coe_mem _, ?_, ?_⟩
  · have h2 : qrMat σ J d ui *ᵥ x = ε • y := by
      rw [qrMat_mulVec, hdx, mul_comm ui, hui, one_smul, hd]
      simp
    have h3 : qrMat σ J y ((1 - σ ε) * bi) *ᵥ (ε • y) = y := by
      rw [qrMat_mulVec, hform_smul_right', hyy]
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination ((1 - σ ε) * ε * y i) * (-hb) + (y i) * hε
    show (qrMat σ J y ((1 - σ ε) * bi) * qrMat σ J d ui) *ᵥ x = y
    rw [← mulVec_mulVec, h2, h3]
  · intro z hxz hyz
    have hdz : hform σ J d z = 0 := by
      rw [hd, hform_sub_left, hxz, hyz]
      simp
    show (qrMat σ J y ((1 - σ ε) * bi) * qrMat σ J d ui) *ᵥ z = z
    have h2 : qrMat σ J d ui *ᵥ z = z := by
      rw [qrMat_mulVec, hdz, mul_zero, zero_smul, sub_zero]
    rw [← mulVec_mulVec, h2, qrMat_mulVec, hyz, mul_zero, zero_smul, sub_zero]

end GlobalTheory.CompanionTheory.SW.QuasiRefl
