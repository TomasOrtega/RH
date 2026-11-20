import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq

open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace
open Matrix Topology Filter IsDedekindDomain Formalism.UG
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.AdelicUnimod

section Algebra

variable {B : Type} [CommRing B] {n : Type} [Fintype n] [DecidableEq n] {σ : B →+* B} {J M : Matrix n n B}

omit [DecidableEq n] in
/- English proof (translation)
Simplify using `[hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem hform_eq (x y : n → B) : hform σ J x y = (σ ∘ x) ⬝ᵥ J *ᵥ y := by
  simp [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

omit [DecidableEq n] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[mulVec, dotProduct]`.
-/
theorem comp_mulVec (P : Matrix n n B) (x : n → B) : σ ∘ (P *ᵥ x) = P.map σ *ᵥ (σ ∘ x) := by
  funext i
  simp [mulVec, dotProduct]

omit [DecidableEq n] in
/- English proof (translation)
Rewrite using `[hform_eq, hform_eq, comp_mulVec, cT, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec _ (_ᵀ), vecMul_transpose]`.
-/
theorem hform_mulVec (P Q : Matrix n n B) (x y : n → B) :
    hform σ J (P *ᵥ x) (Q *ᵥ y) = hform σ (cT σ P * J * Q) x y := by
  rw [hform_eq, hform_eq, comp_mulVec, cT, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec _ (_ᵀ),
    vecMul_transpose]

/- English proof (translation)
Establish `: σ ∘ (Pi.single i 1 : n → B) = Pi.single i 1`. Use function extensionality and compare the values at `k`. Apply the tactic sequence `by_cases h : k = i <;> simp [h]`. Rewrite using `[hform_eq, this]`. Simplify using the standard rewrite rules.
-/
theorem hform_single (i j : n) : hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have : σ ∘ (Pi.single i 1 : n → B) = Pi.single i 1 := by
    funext k
    by_cases h : k = i <;> simp [h]
  rw [hform_eq, this]
  simp

omit [DecidableEq n] in
/- English proof (translation)
Simplify using `[hform, Finset.mul_sum, sub_mul, mul_assoc]`.
-/
theorem hform_sub_smul_left (x d y : n → B) (c : B) :
    hform σ J (x - c • d) y = hform σ J x y - σ c * hform σ J d y := by
  simp [hform, Finset.mul_sum, sub_mul, mul_assoc]

omit [DecidableEq n] in
/- English proof (translation)
Simplify using `[hform, Finset.mul_sum, mul_sub, mul_left_comm]`.
-/
theorem hform_sub_smul_right (x d y : n → B) (c : B) :
    hform σ J x (y - c • d) = hform σ J x y - c * hform σ J x d := by
  simp [hform, Finset.mul_sum, mul_sub, mul_left_comm]

omit [DecidableEq n] in
/- English proof (translation)
Simplify using `[hform, Finset.mul_sum, mul_assoc]`.
-/
theorem hform_smul_left (d y : n → B) (c : B) : hform σ J (c • d) y = σ c * hform σ J d y := by
  simp [hform, Finset.mul_sum, mul_assoc]

omit [DecidableEq n] in
/- English proof (translation)
Simplify using `[hform, Finset.mul_sum, mul_left_comm]`.
-/
theorem hform_smul_right (d y : n → B) (c : B) : hform σ J y (c • d) = c * hform σ J y d := by
  simp [hform, Finset.mul_sum, mul_left_comm]

omit [DecidableEq n] in
/- English proof (translation)
Establish `: ∀ i j, σ (J i j) = J j i` using `fun i j => congrFun (congrFun hJ j) i`. Simplify using `only [hform, map_sum, map_mul, hσ, this]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem hform_symm (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) (x y : n → B) :
    σ (hform σ J x y) = hform σ J y x := by
  have : ∀ i j, σ (J i j) = J j i := fun i j => congrFun (congrFun hJ j) i
  simp only [hform, map_sum, map_mul, hσ, this]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq n] in
/- English proof (translation)
Rewrite using `[hform_mulVec, hM]`. Simplify using `[hform]`.
-/
theorem hform_conj (hM : cT σ M * J * M = J.map σ) (x y : n → B) :
    hform σ J (M *ᵥ (σ ∘ x)) (M *ᵥ (σ ∘ y)) = σ (hform σ J x y) := by
  rw [hform_mulVec, hM]
  simp [hform]

abbrev mat (g : UJ σ J) : Matrix n n B := ((g : GL n B) : Matrix n n B)

/- English proof (translation)
Rewrite using `[hform_mulVec]`. Use `congr 1`. Conclude with `g.2`.
-/
theorem hform_unitary (g : UJ σ J) (x y : n → B) :
    hform σ J (mat g *ᵥ x) (mat g *ᵥ y) = hform σ J x y := by
  rw [hform_mulVec]
  congr 1
  exact g.2

/- English proof (translation)
Use extensionality with `i j`. Simplify using `using congrFun (h (Pi.single j 1)) i`.
-/
theorem ext_mulVec {P Q : Matrix n n B} (h : ∀ x, P *ᵥ x = Q *ᵥ x) : P = Q := by
  ext i j
  simpa using congrFun (h (Pi.single j 1)) i

def reflMat (σ : B →+* B) (J : Matrix n n B) (d : n → B) (c : B) : Matrix n n B :=
  1 - c • vecMulVec d ((σ ∘ d) ᵥ* J)

/- English proof (translation)
Rewrite using `[reflMat, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hform_eq, dotProduct_mulVec]`. Use function extensionality and compare the values at `i`. Simplify using `[mul_comm, mul_left_comm]`.
-/
theorem reflMat_mulVec (d : n → B) (c : B) (x : n → B) :
    reflMat σ J d c *ᵥ x = x - (c * hform σ J d x) • d := by
  rw [reflMat, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hform_eq, dotProduct_mulVec]
  funext i
  simp [mul_comm, mul_left_comm]

/- English proof (translation)
The claim follows from `ext_mulVec fun x => by rw [← mulVec_mulVec, reflMat_mulVec, reflMat_mulVec, hform_sub_smul_right, one_mulVec] funext i simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] linear_combination (-hform σ J d x * d i) * hc`.
-/
theorem reflMat_mul (d : n → B) {c c' : B} (hc : c + c' = c * c' * hform σ J d d) :
    reflMat σ J d c * reflMat σ J d c' = 1 := ext_mulVec fun x => by
  rw [← mulVec_mulVec, reflMat_mulVec, reflMat_mulVec, hform_sub_smul_right, one_mulVec]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-hform σ J d x * d i) * hc

def refl (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) (d : n → B) (c : B)
    (hc : c + σ c = c * σ c * hform σ J d d) : UJ σ J :=
  ⟨⟨reflMat σ J d c, reflMat σ J d (σ c), reflMat_mul d hc,
    reflMat_mul d (by linear_combination hc)⟩, by
    show cT σ (reflMat σ J d c) * J * reflMat σ J d c = J
    ext i j
    rw [← hform_single (σ := σ) (J := _ * J * _), ← hform_mulVec, reflMat_mulVec, reflMat_mulVec, hform_sub_smul_left,
      hform_sub_smul_right, hform_sub_smul_right, map_mul, hform_symm hσ hJ, hform_single]
    linear_combination (-hform σ J d (Pi.single j 1) * hform σ J (Pi.single i 1) d) * hc⟩

/- English proof (translation)
The claim follows from `reflMat_mulVec d c x`.
-/
theorem refl_mulVec (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) (d : n → B) (c : B)
    (hc : c + σ c = c * σ c * hform σ J d d) (x : n → B) :
    mat (refl hσ hJ d c hc) *ᵥ x = x - (c * hform σ J d x) • d :=
  reflMat_mulVec d c x

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext (ext_mulVec h))`.
-/
theorem ext_UJ {g g' : UJ σ J} (h : ∀ x : n → B, mat g *ᵥ x = mat g' *ᵥ x) : g = g' :=
  Subtype.ext (Units.ext (ext_mulVec h))

/- English proof (translation)
Rewrite using `[mulVec_mulVec]`. Both sides reduce to the same expression.
-/
theorem mul_mulVec_UJ (g g' : UJ σ J) (x : n → B) :
    mat (g * g') *ᵥ x = mat g *ᵥ (mat g' *ᵥ x) := by
  rw [mulVec_mulVec]
  rfl

/- English proof (translation)
Take `⟨c, hc⟩` from `hu.exists_left_inv`. Establish `hc'` using `congrArg σ hc`. Rewrite `hc'` using `[map_mul, map_sub, hform_symm hσ hJ, hform_symm hσ hJ, map_one]`. Use `⟨c, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hform_sub_smul_left, hform_sub_smul_right, hform_sub_smul_right, map_one, hvw]`.

Take the linear combination `(-σ c) * hc - c * hc'`. Rewrite using `[refl_mulVec, hform_sub_smul_left, map_one, one_mul, hc]`. Simplify using the standard rewrite rules.
-/
theorem exists_refl (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) {v w : n → B}
    (hvw : hform σ J w w = hform σ J v v) (hu : IsUnit (hform σ J v v - hform σ J w v)) :
    ∃ c hc, mat (refl hσ hJ (v - (1 : B) • w) c hc) *ᵥ v = w := by
  obtain ⟨c, hc⟩ := hu.exists_left_inv
  have hc' := congrArg σ hc
  rw [map_mul, map_sub, hform_symm hσ hJ, hform_symm hσ hJ, map_one] at hc'
  refine ⟨c, ?_, ?_⟩
  · rw [hform_sub_smul_left, hform_sub_smul_right, hform_sub_smul_right, map_one, hvw]
    linear_combination (-σ c) * hc - c * hc'
  · rw [refl_mulVec, hform_sub_smul_left, map_one, one_mul, hc]
    simp

def Generic (σ : B →+* B) : Prop :=
  ∀ q b : B, IsUnit q → σ q = q → ∃ u, u * σ u = 1 ∧ IsUnit (q - σ u * b) ∧ IsUnit (2 * q - σ u * b - u * σ b)

/- English proof (translation)
Establish `hq` using `hform_symm hσ hJ d d`. Use `set d' := M *ᵥ (σ ∘ d) with hd'`. Establish `h1 : hform σ J d' d' = hform σ J d d` using `by rw [hd', hform_conj hM, hq]`. Take `⟨u, hu, hu1, -⟩` from `hgen _ (hform σ J d' d) hd hq`. Establish `h2 : hform σ J (u • d') (u • d') = hform σ J d d`.

Rewrite using `[hform_smul_left, hform_smul_right, h1]`. Take the linear combination `hform σ J d d * hu`. Take `⟨c₀, hc₀, hρ⟩` from `exists_refl hσ hJ h2 (by rwa [hform_smul_left])`. Generalize the expression as in `refl hσ hJ _ c₀ hc₀ = ρ at hρ`. Establish `hc1 : σ c + σ (σ c) = σ c * σ (σ c) * hform σ J d d` using `by rw [hσ]; linear_combination hc`.

Establish `hc2 : σ c + σ (σ c) = σ c * σ (σ c) * hform σ J d' d'` using `by rwa [h1]`. Establish `e1 : refl hσ hJ d c hc * refl hσ hJ d (σ c) hc1 = 1` using `Subtype.ext (Units.ext (reflMat_mul d hc))`. Establish `e2 : ρ * refl hσ hJ d (σ c) hc1 = refl hσ hJ d' (σ c) hc2 * ρ` using `ext_UJ fun x => by`. Rewrite using `[mul_mulVec_UJ, mul_mulVec_UJ, refl_mulVec, refl_mulVec, mulVec_sub, mulVec_smul, hρ, ← hform_unitary ρ d x, hρ, hform_smul_left, smul_smul]`. Use `congr 2`.

Take the linear combination `σ c * hform σ J d' _ * hu`. Establish `e3 : χ (refl hσ hJ d' (σ c) hc2) = χ (refl hσ hJ d c hc)` using `hχ _ _ (ext_mulVec fun x => by`. Take `⟨y, rfl⟩ : ∃ y, σ ∘ y = x` from `⟨σ ∘ x, funext fun i => hσ _⟩`. Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, ← comp_mulVec, refl_mulVec, refl_mulVec, hd', hform_conj hM, ← map_mul, ← mulVec_smul, ← mulVec_sub]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Use the proof step `simp)`. Establish `e4` using `congrArg χ e2`. Rewrite `e4` using `[map_mul, map_mul, e3, mul_comm]`. Establish `e5` using `((Group.isUnit ρ).map χ).mul_right_cancel e4`.

Establish `e6` using `congrArg χ e1`. Rewrite `e6` using `[map_mul, map_one, e5, ← pow_two]`. Conclude with `(pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 e6`.
-/
theorem char_refl (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) (hM : cT σ M * J * M = J.map σ)
    (hgen : Generic σ) (χ : UJ σ J →* ℝ≥0)
    (hχ : ∀ g g' : UJ σ J, mat g' * M = M * (mat g).map σ → χ g' = χ g)
    (d : n → B) (c : B) (hc : c + σ c = c * σ c * hform σ J d d) (hd : IsUnit (hform σ J d d)) :
    χ (refl hσ hJ d c hc) = 1 := by
  have hq := hform_symm hσ hJ d d
  set d' := M *ᵥ (σ ∘ d) with hd'
  have h1 : hform σ J d' d' = hform σ J d d := by rw [hd', hform_conj hM, hq]
  obtain ⟨u, hu, hu1, -⟩ := hgen _ (hform σ J d' d) hd hq
  have h2 : hform σ J (u • d') (u • d') = hform σ J d d := by
    rw [hform_smul_left, hform_smul_right, h1]
    linear_combination hform σ J d d * hu
  obtain ⟨c₀, hc₀, hρ⟩ := exists_refl hσ hJ h2 (by rwa [hform_smul_left])
  generalize refl hσ hJ _ c₀ hc₀ = ρ at hρ
  have hc1 : σ c + σ (σ c) = σ c * σ (σ c) * hform σ J d d := by rw [hσ]; linear_combination hc
  have hc2 : σ c + σ (σ c) = σ c * σ (σ c) * hform σ J d' d' := by rwa [h1]
  have e1 : refl hσ hJ d c hc * refl hσ hJ d (σ c) hc1 = 1 := Subtype.ext (Units.ext (reflMat_mul d hc))
  have e2 : ρ * refl hσ hJ d (σ c) hc1 = refl hσ hJ d' (σ c) hc2 * ρ := ext_UJ fun x => by
    rw [mul_mulVec_UJ, mul_mulVec_UJ, refl_mulVec, refl_mulVec, mulVec_sub, mulVec_smul, hρ,
      ← hform_unitary ρ d x, hρ, hform_smul_left, smul_smul]
    congr 2
    linear_combination σ c * hform σ J d' _ * hu
  have e3 : χ (refl hσ hJ d' (σ c) hc2) = χ (refl hσ hJ d c hc) := hχ _ _ (ext_mulVec fun x => by
    obtain ⟨y, rfl⟩ : ∃ y, σ ∘ y = x := ⟨σ ∘ x, funext fun i => hσ _⟩
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← comp_mulVec, refl_mulVec, refl_mulVec, hd', hform_conj hM,
      ← map_mul, ← mulVec_smul, ← mulVec_sub]
    congr 1
    funext i
    simp)
  have e4 := congrArg χ e2
  rw [map_mul, map_mul, e3, mul_comm] at e4
  have e5 := ((Group.isUnit ρ).map χ).mul_right_cancel e4
  have e6 := congrArg χ e1
  rw [map_mul, map_one, e5, ← pow_two] at e6
  exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 e6

def Framed (σ : B →+* B) (J M : Matrix n n B) : Prop :=
  cT σ J = J ∧ (∃ (Q : Matrix n n B) (a : n → B), IsUnit Q ∧ (∀ i, IsUnit (a i)) ∧ cT σ Q * J * Q = diagonal a) ∧
    cT σ M * J * M = J.map σ ∧ M * M.map σ = 1

/- English proof (translation)
Take `⟨hJ, ⟨Q, a, hQ, ha, hD⟩, hM, -⟩` from `hF`. Set `v : n → n → B` to `fun i => Q *ᵥ Pi.single i 1`. Establish `hv : ∀ i j, hform σ J (v i) (v j) = diagonal a i j` using `fun i j => by`. Rewrite using `[hform_mulVec, hD, hform_single]`. Establish `key : ∀ (s : Finset n) (g : UJ σ J), (∀ j ∉ s, mat g *ᵥ v j = v j) → χ g = 1`.

Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `g hg`. Establish `: (mat g) * Q = 1 * Q`.

Use extensionality with `i j`. Use `congrFun (hg j (by simp)) i` as an intermediate fact. Simplify using `only [v] at this`. Rewrite `this` using `[mulVec_mulVec]`. Simplify `this` using `only [mulVec_single_one, col_apply, one_mul]`.

Rewrite using `[show g = 1 from Subtype.ext (Units.ext (hQ.mul_right_cancel this)), map_one]`. Consider the case `insert i s hi ih`. Introduce `g hg`. Establish `hii : hform σ J (v i) (v i) = a i` using `by rw [hv, diagonal_apply_eq]`. Establish `hij : ∀ j ∉ insert i s, hform σ J (v i) (v j) = 0` using `fun j hj => by`.

Rewrite using `[hv, diagonal_apply_ne]`. Introduce and unpack `rfl`. Simplify using `at hj`. Establish `hσa : σ (a i) = a i` using `by rw [← hii, hform_symm hσ hJ]`. Take `⟨u, hu, hu1, hu2⟩` from `hgen _ (hform σ J (mat g *ᵥ v i) (v i)) (ha i) hσa`.

Take `⟨a', ha'⟩` from `(ha i).exists_left_inv`. Establish `hσa' : σ a' = a'`. Use `congrArg σ ha'` as an intermediate fact. Rewrite `this` using `[map_mul, hσa, map_one]`. Take the linear combination `a' * this - σ a' * ha'`.

Establish `hc : a' * (1 - u) + σ (a' * (1 - u)) = a' * (1 - u) * σ (a' * (1 - u)) * hform σ J (v i) (v i)`. Rewrite using `[map_mul, map_sub, map_one, hσa', hii]`. Take the linear combination `(-a' * (1 - u) * (1 - σ u)) * ha' - a' * hu`. Use `set t := refl hσ hJ (v i) _ hc`. Establish `ht : χ t = 1` using `char_refl hσ hJ hM hgen χ hχ _ _ hc (hii ▸ ha i)`.

Establish `hti : mat t *ᵥ v i = u • v i`. Rewrite using `[refl_mulVec, hii]`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Take the linear combination `(-(1 - u) * v i k) * ha'`.

Establish `hgt : mat (g * t) *ᵥ v i = u • (mat g *ᵥ v i)`. Rewrite using `[mul_mulVec_UJ, hti, mulVec_smul]`. Establish `hgtj : ∀ j ∉ insert i s, mat (g * t) *ᵥ v j = v j` using `fun j hj => by`. Rewrite using `[mul_mulVec_UJ, refl_mulVec, hij j hj, mul_zero, zero_smul, sub_zero, hg j hj]`. Establish `hw : hform σ J (mat (g * t) *ᵥ v i) (v i) = σ u * hform σ J (mat g *ᵥ v i) (v i)` using `by rw [hgt, hform_smul_left]`.

Take `⟨c₀, hc₀, hρ⟩` from `exists_refl hσ hJ (hform_unitary (g * t) (v i) (v i)) (by rwa [hii, hw])`. Establish `hρ1` using `char_refl hσ hJ hM hgen χ hχ _ _ hc₀ (by`. Rewrite using `[hform_sub_smul_left, hform_sub_smul_right, hform_sub_smul_right, hform_unitary, ← hform_symm hσ hJ (_ *ᵥ v i) (v i), hw, hii, map_mul, hσ, map_one]`. Use `hu2 using 1` and compare the differences between its conclusion and the goal. Use the proof step `ring)`.

Establish `hρj : ∀ j ∉ insert i s, mat (refl hσ hJ _ c₀ hc₀) *ᵥ v j = v j` using `fun j hj => by`. Rewrite using `[refl_mulVec, hform_sub_smul_left, ← hgtj j hj, hform_unitary, hgtj j hj, hij j hj]`. Simplify using the standard rewrite rules. Use `set ρ := refl hσ hJ _ c₀ hc₀`. Establish `h3` using `ih (ρ⁻¹ * (g * t)) fun j hj => by`.

Establish `: mat (g * t) *ᵥ v j = (ρ : GL n B) *ᵥ v j`. Distinguish the cases in `h : j = i`. Rewrite using `[h, hρ]`. Establish `hj' : j ∉ insert i s` using `by simp [h, hj]`. Rewrite using `[hgtj j hj', hρj j hj']`.

Rewrite using `[mul_mulVec_UJ, this, ← mul_mulVec_UJ, inv_mul_cancel]`. Conclude with `one_mulVec _`. Establish `h4 : g * t = ρ * (ρ⁻¹ * (g * t))` using `by group`. Establish `h5` using `congrArg χ h4`. Rewrite `h5` using `[map_mul, map_mul χ ρ, h3, hρ1, ht, mul_one, mul_one]`. Then use the resulting hypothesis.

Conclude with `key Finset.univ g (by simp)`.
-/
theorem char_eq_one (hσ : ∀ x, σ (σ x) = x) (hF : Framed σ J M) (hgen : Generic σ) (χ : UJ σ J →* ℝ≥0)
    (hχ : ∀ g g' : UJ σ J, mat g' * M = M * (mat g).map σ → χ g' = χ g)
    (g : UJ σ J) : χ g = 1 := by
  obtain ⟨hJ, ⟨Q, a, hQ, ha, hD⟩, hM, -⟩ := hF
  let v : n → n → B := fun i => Q *ᵥ Pi.single i 1
  have hv : ∀ i j, hform σ J (v i) (v j) = diagonal a i j := fun i j => by
    rw [hform_mulVec, hD, hform_single]
  have key : ∀ (s : Finset n) (g : UJ σ J), (∀ j ∉ s, mat g *ᵥ v j = v j) → χ g = 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro g hg
      have : (mat g) * Q = 1 * Q := by
        ext i j
        have := congrFun (hg j (by simp)) i
        simp only [v] at this
        rw [mulVec_mulVec] at this
        simpa only [mulVec_single_one, col_apply, one_mul] using this
      rw [show g = 1 from Subtype.ext (Units.ext (hQ.mul_right_cancel this)), map_one]
    | insert i s hi ih =>
      intro g hg
      have hii : hform σ J (v i) (v i) = a i := by rw [hv, diagonal_apply_eq]
      have hij : ∀ j ∉ insert i s, hform σ J (v i) (v j) = 0 := fun j hj => by
        rw [hv, diagonal_apply_ne]
        rintro rfl
        simp at hj
      have hσa : σ (a i) = a i := by rw [← hii, hform_symm hσ hJ]
      obtain ⟨u, hu, hu1, hu2⟩ := hgen _ (hform σ J (mat g *ᵥ v i) (v i)) (ha i) hσa
      obtain ⟨a', ha'⟩ := (ha i).exists_left_inv
      have hσa' : σ a' = a' := by
        have := congrArg σ ha'
        rw [map_mul, hσa, map_one] at this
        linear_combination a' * this - σ a' * ha'
      have hc : a' * (1 - u) + σ (a' * (1 - u)) = a' * (1 - u) * σ (a' * (1 - u)) * hform σ J (v i) (v i) := by
        rw [map_mul, map_sub, map_one, hσa', hii]
        linear_combination (-a' * (1 - u) * (1 - σ u)) * ha' - a' * hu
      set t := refl hσ hJ (v i) _ hc
      have ht : χ t = 1 := char_refl hσ hJ hM hgen χ hχ _ _ hc (hii ▸ ha i)
      have hti : mat t *ᵥ v i = u • v i := by
        rw [refl_mulVec, hii]
        funext k
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination (-(1 - u) * v i k) * ha'
      have hgt : mat (g * t) *ᵥ v i = u • (mat g *ᵥ v i) := by
        rw [mul_mulVec_UJ, hti, mulVec_smul]
      have hgtj : ∀ j ∉ insert i s, mat (g * t) *ᵥ v j = v j := fun j hj => by
        rw [mul_mulVec_UJ, refl_mulVec, hij j hj, mul_zero, zero_smul, sub_zero, hg j hj]
      have hw : hform σ J (mat (g * t) *ᵥ v i) (v i) =
          σ u * hform σ J (mat g *ᵥ v i) (v i) := by rw [hgt, hform_smul_left]
      obtain ⟨c₀, hc₀, hρ⟩ := exists_refl hσ hJ (hform_unitary (g * t) (v i) (v i)) (by rwa [hii, hw])
      have hρ1 := char_refl hσ hJ hM hgen χ hχ _ _ hc₀ (by
        rw [hform_sub_smul_left, hform_sub_smul_right, hform_sub_smul_right, hform_unitary,
          ← hform_symm hσ hJ (_ *ᵥ v i) (v i), hw, hii, map_mul, hσ, map_one]
        convert hu2 using 1
        ring)
      have hρj : ∀ j ∉ insert i s, mat (refl hσ hJ _ c₀ hc₀) *ᵥ v j = v j := fun j hj => by
        rw [refl_mulVec, hform_sub_smul_left, ← hgtj j hj, hform_unitary, hgtj j hj, hij j hj]
        simp
      set ρ := refl hσ hJ _ c₀ hc₀
      have h3 := ih (ρ⁻¹ * (g * t)) fun j hj => by
        have : mat (g * t) *ᵥ v j = (ρ : GL n B) *ᵥ v j := by
          by_cases h : j = i
          · rw [h, hρ]
          · have hj' : j ∉ insert i s := by simp [h, hj]
            rw [hgtj j hj', hρj j hj']
        rw [mul_mulVec_UJ, this, ← mul_mulVec_UJ, inv_mul_cancel]
        exact one_mulVec _
      have h4 : g * t = ρ * (ρ⁻¹ * (g * t)) := by group
      have h5 := congrArg χ h4
      rwa [map_mul, map_mul χ ρ, h3, hρ1, ht, mul_one, mul_one] at h5
  exact key Finset.univ g (by simp)

end Algebra

section Generic

variable {B : Type} [CommRing B] [Algebra ℚ B] [Finite (MaximalSpectrum B)]

/- English proof (translation)
Establish `key : ∀ m : MaximalSpectrum B, ∀ᶠ t : ℕ in cofinite, x * t ^ 2 + y * t + z ∉ m.asIdeal`. Introduce `m`. Use `haveI := m.isMaximal`. Use `letI := Ideal.Quotient.field m.asIdeal`. Use `haveI : CharZero (B ⧸ m.asIdeal) := algebraRat.charZero _`.

Set `π` to `Ideal.Quotient.mk m.asIdeal`. Set `p : Polynomial (B ⧸ m.asIdeal)` to `Polynomial.C (π x) * Polynomial.X ^ 2 + Polynomial.C (π y) * Polynomial.X + Polynomial.C (π z)`. Establish `hp : p ≠ 0` using `fun h0 => by`. Establish `h2 : π x = 0` using `by simpa [p] using congrArg (Polynomial.coeff · 2) h0`. Establish `h1 : π y = 0` using `by simpa [p] using congrArg (Polynomial.coeff · 1) h0`.

Establish `h3 : π z = 0` using `by simpa [p] using congrArg (Polynomial.coeff · 0) h0`. Use `(h.map π).ne_zero` as an intermediate fact. Simplify using `[h1, h2, h3] at this`. Use `((Polynomial.finite_setOf_isRoot hp).preimage (Nat.cast_injective (R := B ⧸ m.asIdeal)).injOn).subset fun t ht => ?_` and prove the remaining obligations. Use `Ideal.Quotient.eq_zero_iff_mem.2 (not_not.1 ht)` as an intermediate fact.

Simplify `this` using `[p, π]`. Use `filter_upwards [Filter.eventually_all.2 key] with t ht`. Assume the negation of the conclusion as `hn`. Take `⟨m, hm, hmem⟩` from `exists_max_ideal_of_mem_nonunits hn`. Conclude with `ht ⟨m, hm⟩ hmem`.
-/
theorem eventually_isUnit {x y z α β γ : B} (h : IsUnit (α * x + β * y + γ * z)) :
    ∀ᶠ t : ℕ in cofinite, IsUnit (x * t ^ 2 + y * t + z) := by
  have key : ∀ m : MaximalSpectrum B, ∀ᶠ t : ℕ in cofinite, x * t ^ 2 + y * t + z ∉ m.asIdeal := by
    intro m
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    haveI : CharZero (B ⧸ m.asIdeal) := algebraRat.charZero _
    let π := Ideal.Quotient.mk m.asIdeal
    let p : Polynomial (B ⧸ m.asIdeal) :=
      Polynomial.C (π x) * Polynomial.X ^ 2 + Polynomial.C (π y) * Polynomial.X + Polynomial.C (π z)
    have hp : p ≠ 0 := fun h0 => by
      have h2 : π x = 0 := by simpa [p] using congrArg (Polynomial.coeff · 2) h0
      have h1 : π y = 0 := by simpa [p] using congrArg (Polynomial.coeff · 1) h0
      have h3 : π z = 0 := by simpa [p] using congrArg (Polynomial.coeff · 0) h0
      have := (h.map π).ne_zero
      simp [h1, h2, h3] at this
    refine ((Polynomial.finite_setOf_isRoot hp).preimage
      (Nat.cast_injective (R := B ⧸ m.asIdeal)).injOn).subset fun t ht => ?_
    have := Ideal.Quotient.eq_zero_iff_mem.2 (not_not.1 ht)
    simpa [p, π] using this
  filter_upwards [Filter.eventually_all.2 key] with t ht
  by_contra hn
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hn
  exact ht ⟨m, hm⟩ hmem

/- English proof (translation)
Introduce `q b hq _`. Establish `h2 : IsUnit (2 : B)`. Use `(IsUnit.mk0 (2 : ℚ) two_ne_zero).map (algebraMap ℚ B)` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Take `⟨t, h1, h3, h4, h5⟩` from `((eventually_isUnit (x := 0) (y := 1) (z := δ) (α := 0) (β := 1) (γ := 0) (by simp)).and ((eventually_isUnit (x := 0) (y := 1) (z := -δ) (α := 0) (β := 1) (γ := 0) (by simp)).and ((eventually_isUnit (x := 0) (y := q - b) (z := δ * (q + b)) (α := 0) (β := δ) (γ := 1) (by convert ( …`.

Take `⟨r, hr⟩` from `h3.exists_left_inv`. Establish `hr'` using `congrArg σ hr`. Simplify using `only [zero_mul, one_mul, zero_add, map_mul, map_add, map_neg, map_natCast, hσδ, neg_neg, map_one] at hr hr' h1 h3`. Use `⟨r * (t + δ), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_add, map_natCast, hσδ]`.

Take the linear combination `σ r * (t + δ) * hr + hr'`. Rewrite using `[map_mul, map_add, map_natCast, hσδ, ← h1.mul_left_iff]`. Use `h4 using 1` and compare the differences between its conclusion and the goal. Take the linear combination `(-(t - δ) * b) * hr'`. Rewrite using `[map_mul, map_add, map_natCast, hσδ, ← h1.mul_left_iff, ← h3.mul_left_iff]`.

Use `h5 using 1` and compare the differences between its conclusion and the goal. Take the linear combination `(-(t - δ) ^ 2 * b) * hr' - (t + δ) ^ 2 * σ b * hr`.
-/
theorem generic_of_semilocal {σ : B →+* B} {δ : B} (hδ : IsUnit δ) (hσδ : σ δ = -δ) : Generic σ := by
  intro q b hq _
  have h2 : IsUnit (2 : B) := by
    have := (IsUnit.mk0 (2 : ℚ) two_ne_zero).map (algebraMap ℚ B)
    rwa [map_ofNat] at this
  obtain ⟨t, h1, h3, h4, h5⟩ := ((eventually_isUnit (x := 0) (y := 1) (z := δ) (α := 0) (β := 1) (γ := 0)
    (by simp)).and ((eventually_isUnit (x := 0) (y := 1) (z := -δ) (α := 0) (β := 1) (γ := 0)
    (by simp)).and ((eventually_isUnit (x := 0) (y := q - b) (z := δ * (q + b)) (α := 0) (β := δ) (γ := 1)
    (by convert (h2.mul hδ).mul hq using 1; ring)).and
    (eventually_isUnit (x := 2 * q - b - σ b) (y := 2 * δ * (b - σ b)) (z := -δ ^ 2 * (2 * q + b + σ b))
      (α := δ ^ 2) (β := 0) (γ := -1)
    (by convert ((h2.mul h2).mul (hδ.pow 2)).mul hq using 1; ring))))).exists
  obtain ⟨r, hr⟩ := h3.exists_left_inv
  have hr' := congrArg σ hr
  simp only [zero_mul, one_mul, zero_add, map_mul, map_add, map_neg, map_natCast, hσδ, neg_neg, map_one]
    at hr hr' h1 h3
  refine ⟨r * (t + δ), ?_, ?_, ?_⟩
  · rw [map_mul, map_add, map_natCast, hσδ]
    linear_combination σ r * (t + δ) * hr + hr'
  · rw [map_mul, map_add, map_natCast, hσδ, ← h1.mul_left_iff]
    convert h4 using 1
    linear_combination (-(t - δ) * b) * hr'
  · rw [map_mul, map_add, map_natCast, hσδ, ← h1.mul_left_iff, ← h3.mul_left_iff]
    convert h5 using 1
    linear_combination (-(t - δ) ^ 2 * b) * hr' - (t + δ) ^ 2 * σ b * hr

end Generic

section Split

variable {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
  {σ : A →+* A} {σ' : B →+* B} {J M : Matrix n n A}

omit [Fintype n] [DecidableEq n] in
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[hπ]`.
-/
theorem map_map_comm {π : A →+* B} (hπ : ∀ x, π (σ x) = σ' (π x)) (P : Matrix n n A) :
    (P.map σ).map π = (P.map π).map σ' := by
  ext i j
  simp [hπ]

omit [Fintype n] [DecidableEq n] in
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT, hπ]`.
-/
theorem cT_map {π : A →+* B} (hπ : ∀ x, π (σ x) = σ' (π x)) (P : Matrix n n A) :
    (cT σ P).map π = cT σ' (P.map π) := by
  ext i j
  simp [cT, hπ]

/- English proof (translation)
Take `⟨hJ, ⟨Q, a, hQ, ha, hD⟩, hM, hM'⟩` from `h`. Use `⟨by rw [← cT_map hπ, hJ], ⟨Q.map π, fun i => π (a i), hQ.map π.mapMatrix, fun i => (ha i).map π, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← cT_map hπ, ← Matrix.map_mul, ← Matrix.map_mul, hD, diagonal_map (map_zero π)]`. Rewrite using `[← cT_map hπ, ← Matrix.map_mul, ← Matrix.map_mul, hM, map_map_comm hπ]`. Rewrite using `[← map_map_comm hπ, ← Matrix.map_mul, hM', Matrix.map_one _ (map_zero π) (map_one π)]`.
-/
theorem Framed.map {π : A →+* B} (hπ : ∀ x, π (σ x) = σ' (π x)) (h : Framed σ J M) :
    Framed σ' (J.map π) (M.map π) := by
  obtain ⟨hJ, ⟨Q, a, hQ, ha, hD⟩, hM, hM'⟩ := h
  refine ⟨by rw [← cT_map hπ, hJ], ⟨Q.map π, fun i => π (a i), hQ.map π.mapMatrix, fun i => (ha i).map π, ?_⟩,
    ?_, ?_⟩
  · rw [← cT_map hπ, ← Matrix.map_mul, ← Matrix.map_mul, hD, diagonal_map (map_zero π)]
  · rw [← cT_map hπ, ← Matrix.map_mul, ← Matrix.map_mul, hM, map_map_comm hπ]
  · rw [← map_map_comm hπ, ← Matrix.map_mul, hM', Matrix.map_one _ (map_zero π) (map_one π)]

/- English proof (translation)
Take `⟨P, d, hP, hd, -⟩` from `GlobalTheory.HermDiag.exists_congr_diagonal (c := σ) two_ne_zero hσ (G := J) fun a b => congrFun (congrFun hJ b) a`. Establish `hσσ : ∀ X : Matrix n n E, (X.map σ).map σ = X` using `fun X => by ext i j; simp [hσ]`. Establish `hP' : IsUnit P` using `(isUnit_iff_isUnit_det P).2 hP.isUnit`. Take `⟨P', h1⟩` from `hP'.exists_right_inv`. Establish `h2` using `mul_eq_one_comm.1 h1`.

Establish `h3 : P'.map σ * P.map σ = 1`. Rewrite using `[← Matrix.map_mul, h2, Matrix.map_one _ (map_zero σ) (map_one σ)]`. Establish `hd' : cT σ (P.map σ) * J * P.map σ = diagonal d` using `by rw [cT, hσσ, hd]`. Establish `hdd : (diagonal d).map σ = diagonal d`. Establish `: cT σ (diagonal d) = diagonal d`.

Rewrite using `[← hd', cT_mul, cT_mul, hJ, Matrix.mul_assoc]`. Use `congr 2`. Simplify using `only [cT, ← transpose_map, hσσ, transpose_transpose]`. Rewrite `this` using `[cT, diagonal_map (map_zero σ), diagonal_transpose, ← diagonal_map (map_zero σ)]`. Then use the resulting hypothesis. Use `⟨P.map σ * P', hJ, ⟨P.map σ, d, hP'.map σ.mapMatrix, fun i => (GlobalTheory.HermDiag.ne_zero_of_congr_diagonal hP hd hdet i).isUnit, hd'⟩, ?_, ?_⟩` and prove the remaining obligations.

Establish `e : cT σ P * J.map σ * P = diagonal d`. Rewrite using `[← hdd, ← hd', Matrix.map_mul, Matrix.map_mul, hσσ, cT_map (σ' := σ) fun _ => rfl, hσσ]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.map_mul, hσσ, Matrix.mul_assoc, ← Matrix.mul_assoc P', h2, Matrix.one_mul, mul_eq_one_comm.1 h3]`.
-/
theorem exists_framed {E : Type} [Field E] [CharZero E] {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x)
    {J : Matrix n n E} (hJ : cT σ J = J) (hdet : J.det ≠ 0) : ∃ M, Framed σ J M := by
  obtain ⟨P, d, hP, hd, -⟩ := GlobalTheory.HermDiag.exists_congr_diagonal (c := σ) two_ne_zero hσ (G := J)
    fun a b => congrFun (congrFun hJ b) a
  have hσσ : ∀ X : Matrix n n E, (X.map σ).map σ = X := fun X => by ext i j; simp [hσ]
  have hP' : IsUnit P := (isUnit_iff_isUnit_det P).2 hP.isUnit
  obtain ⟨P', h1⟩ := hP'.exists_right_inv
  have h2 := mul_eq_one_comm.1 h1
  have h3 : P'.map σ * P.map σ = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have hd' : cT σ (P.map σ) * J * P.map σ = diagonal d := by rw [cT, hσσ, hd]
  have hdd : (diagonal d).map σ = diagonal d := by
    have : cT σ (diagonal d) = diagonal d := by
      rw [← hd', cT_mul, cT_mul, hJ, Matrix.mul_assoc]
      congr 2
      simp only [cT, ← transpose_map, hσσ, transpose_transpose]
    rwa [cT, diagonal_map (map_zero σ), diagonal_transpose, ← diagonal_map (map_zero σ)] at this
  refine ⟨P.map σ * P', hJ, ⟨P.map σ, d, hP'.map σ.mapMatrix,
    fun i => (GlobalTheory.HermDiag.ne_zero_of_congr_diagonal hP hd hdet i).isUnit, hd'⟩, ?_, ?_⟩
  · have e : cT σ P * J.map σ * P = diagonal d := by
      rw [← hdd, ← hd', Matrix.map_mul, Matrix.map_mul, hσσ, cT_map (σ' := σ) fun _ => rfl, hσσ]
    calc cT σ (P.map σ * P') * J * (P.map σ * P')
        = cT σ P' * (cT σ (P.map σ) * J * P.map σ) * P' := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ (P * P') * J.map σ * (P * P') := by rw [hd', ← e, cT_mul]; simp only [Matrix.mul_assoc]
      _ = J.map σ := by rw [h1, cT_one, Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.map_mul, hσσ, Matrix.mul_assoc, ← Matrix.mul_assoc P', h2, Matrix.one_mul, mul_eq_one_comm.1 h3]

/- English proof (translation)
Establish `hee : (1 - e) * e = 0` using `by rw [mul_comm]; exact hker _ (by simp [he])`. Establish `ext : ∀ {X Y : Matrix n n A}, X.map π = Y.map π → (1 - e) • X = (1 - e) • Y → X = Y`. Introduce `X Y h1 h2`. Use extensionality with `i j`. Establish `a1 : π (X i j) = π (Y i j)` using `congrFun (congrFun h1 i) j`.

Establish `a2 : (1 - e) * X i j = (1 - e) * Y i j` using `congrFun (congrFun h2 i) j`. Take the linear combination `a2 + hker (X i j - Y i j) (by rw [map_sub, a1, sub_self])`. Establish `ex : ∀ Y : Matrix n n B, ∃ X : Matrix n n A, X.map π = Y ∧ (1 - e) • X = (1 - e) • 1`. Introduce `Y`. Use `⟨e • Y.map (Function.surjInv hs) + (1 - e) • 1, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `i j`. Simplify using `[he, Function.surjInv_eq]`. Rewrite using `[smul_add, smul_smul, smul_smul, hee, zero_smul, zero_add]`. Use `congr 1`. Take the linear combination `-hee`.

Use `choose l hl hl' using ex`. Establish `hπ1 : (1 : Matrix n n A).map π = 1` using `Matrix.map_one _ (map_zero π) (map_one π)`. Establish `hr : ∀ X Y, (1 - e) • (X * l Y) = (1 - e) • X` using `fun X Y => by`. Rewrite using `[← mul_smul_comm, hl', mul_smul_comm, mul_one]`. Establish `hlf : ∀ X Y, (1 - e) • (l Y * X) = (1 - e) • X` using `fun X Y => by`.

Rewrite using `[← smul_mul_assoc, hl', smul_mul_assoc, one_mul]`. Set `L : Matrix n n B →* Matrix n n A` to `{ toFun := l map_one' := ext (by rw [hl, hπ1]) (hl' _) map_mul' := fun X Y => ext (by rw [Matrix.map_mul, hl, hl, hl]) (by rw [hr, hl', hl']) }`. Establish `hσl : ∀ Y, (1 - e) • (l Y).map σ = (1 - e) • 1` using `fun Y => by`. Use `congrArg (·.map σ) (hl' Y)` as an intermediate fact. Simplify using `only [Matrix.map_smul' _ _ _ (map_mul σ), map_sub, map_one, hσe] at this`.

Rewrite `this` using `[Matrix.map_one _ (map_zero σ) (map_one σ)]`. Then use the resulting hypothesis. Set `ι : UJ σ' (J.map π) →* UJ σ J` to `((Units.map L).comp (UJ σ' (J.map π)).subtype).codRestrict _ fun y => by show cT σ (l (mat y)) * J * l (mat y) = J`. Use `ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Matrix.map_mul, Matrix.map_mul, cT_map hπ, hl]`. Conclude with `y.2`.

Rewrite using `[hr, ← smul_mul_assoc, cT, ← transpose_smul, hσl, transpose_smul, transpose_one, smul_mul_assoc, one_mul]`. Establish `hι : ∀ y, mat (ι y) = l (mat y)` using `fun y => rfl`. Establish `h1 : ∀ y, χ (ι y) = 1` using `char_eq_one (fun x => by obtain ⟨x, rfl⟩ := hs x; rw [← hπ, ← hπ, hσ]) (hF.map hπ) hgen (χ.comp ι) fun y y' h => hχ _ _ (ext (by rw [Matrix.map_mul, Matrix.map_mul, map_map_comm hπ, hι, hι, hl, hl, h]) (by rw [hι, hι, hlf, ← mul_smul_comm, hσl, mul_smul_comm, mul_one]))`. Set `y : UJ σ' (J.map π)` to `⟨bc π g, by show cT σ' ((mat g).map π) * J.map π * (mat g).map π = J.map π`. Rewrite using `[← cT_map hπ, ← Matrix.map_mul, ← Matrix.map_mul]`.

Conclude with `congrArg (·.map π) g.2⟩`. Establish `fin : ∀ X Y : Matrix n n A, X.map π = 1 → (1 - e) • X = (1 - e) • Y → X - 1 = (1 - e) • (Y - 1)`. Introduce `X Y h1 h2`. Use `ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Matrix.map_sub _ (map_sub π), h1, hπ1, Matrix.map_smul' _ _ _ (map_mul π)]`.

Simplify using `[he]`. Rewrite using `[smul_smul, smul_sub, h2, ← smul_sub]`. Use `congr 1`. Take the linear combination `hee`. Use `⟨g * ι y⁻¹, fin _ _ ?_ (hr _ _), ?_, by rw [map_mul, h1, mul_one]⟩` and prove the remaining obligations.

Use `show (mat g * l (mat y⁻¹)).map π = 1`. Rewrite using `[Matrix.map_mul, hl]`. Conclude with `Units.mul_inv (bc π (g : GL n A))`. Rewrite using `[map_inv, _root_.mul_inv_rev, inv_inv]`. Use `fin _ _ ?_ (hlf _ _)` and prove the remaining obligations.

Use `show (l (mat y) * mat g⁻¹).map π = 1`. Rewrite using `[Matrix.map_mul, hl]`. Conclude with `Units.mul_inv (bc π (g : GL n A))`.
-/
theorem exists_char_eq {π : A →+* B} (hπ : ∀ x, π (σ x) = σ' (π x)) (hs : Function.Surjective π) {e : A}
    (he : π e = 1) (hker : ∀ x, π x = 0 → e * x = 0) (hσe : σ e = e)
    (hσ : ∀ x, σ (σ x) = x) (hF : Framed σ J M) (hgen : Generic σ') (χ : UJ σ J →* ℝ≥0)
    (hχ : ∀ g g' : UJ σ J, mat g' * M = M * (mat g).map σ → χ g' = χ g) (g : UJ σ J) :
    ∃ k : UJ σ J, mat k - 1 = (1 - e) • (mat g - 1) ∧ mat k⁻¹ - 1 = (1 - e) • (mat g⁻¹ - 1) ∧ χ k = χ g := by
  have hee : (1 - e) * e = 0 := by rw [mul_comm]; exact hker _ (by simp [he])
  have ext : ∀ {X Y : Matrix n n A}, X.map π = Y.map π → (1 - e) • X = (1 - e) • Y → X = Y := by
    intro X Y h1 h2
    ext i j
    have a1 : π (X i j) = π (Y i j) := congrFun (congrFun h1 i) j
    have a2 : (1 - e) * X i j = (1 - e) * Y i j := congrFun (congrFun h2 i) j
    linear_combination a2 + hker (X i j - Y i j) (by rw [map_sub, a1, sub_self])
  have ex : ∀ Y : Matrix n n B, ∃ X : Matrix n n A, X.map π = Y ∧ (1 - e) • X = (1 - e) • 1 := by
    intro Y
    refine ⟨e • Y.map (Function.surjInv hs) + (1 - e) • 1, ?_, ?_⟩
    · ext i j
      simp [he, Function.surjInv_eq]
    · rw [smul_add, smul_smul, smul_smul, hee, zero_smul, zero_add]
      congr 1
      linear_combination -hee
  choose l hl hl' using ex
  have hπ1 : (1 : Matrix n n A).map π = 1 := Matrix.map_one _ (map_zero π) (map_one π)
  have hr : ∀ X Y, (1 - e) • (X * l Y) = (1 - e) • X := fun X Y => by
    rw [← mul_smul_comm, hl', mul_smul_comm, mul_one]
  have hlf : ∀ X Y, (1 - e) • (l Y * X) = (1 - e) • X := fun X Y => by
    rw [← smul_mul_assoc, hl', smul_mul_assoc, one_mul]
  let L : Matrix n n B →* Matrix n n A :=
    { toFun := l
      map_one' := ext (by rw [hl, hπ1]) (hl' _)
      map_mul' := fun X Y => ext (by rw [Matrix.map_mul, hl, hl, hl]) (by rw [hr, hl', hl']) }
  have hσl : ∀ Y, (1 - e) • (l Y).map σ = (1 - e) • 1 := fun Y => by
    have := congrArg (·.map σ) (hl' Y)
    simp only [Matrix.map_smul' _ _ _ (map_mul σ), map_sub, map_one, hσe] at this
    rwa [Matrix.map_one _ (map_zero σ) (map_one σ)] at this
  let ι : UJ σ' (J.map π) →* UJ σ J := ((Units.map L).comp (UJ σ' (J.map π)).subtype).codRestrict _ fun y => by
    show cT σ (l (mat y)) * J * l (mat y) = J
    refine ext ?_ ?_
    · rw [Matrix.map_mul, Matrix.map_mul, cT_map hπ, hl]
      exact y.2
    · rw [hr, ← smul_mul_assoc, cT, ← transpose_smul, hσl, transpose_smul, transpose_one, smul_mul_assoc, one_mul]
  have hι : ∀ y, mat (ι y) = l (mat y) := fun y => rfl
  have h1 : ∀ y, χ (ι y) = 1 := char_eq_one (fun x => by obtain ⟨x, rfl⟩ := hs x; rw [← hπ, ← hπ, hσ])
    (hF.map hπ) hgen (χ.comp ι) fun y y' h => hχ _ _ (ext
      (by rw [Matrix.map_mul, Matrix.map_mul, map_map_comm hπ, hι, hι, hl, hl, h])
      (by rw [hι, hι, hlf, ← mul_smul_comm, hσl, mul_smul_comm, mul_one]))
  let y : UJ σ' (J.map π) := ⟨bc π g, by
    show cT σ' ((mat g).map π) * J.map π * (mat g).map π = J.map π
    rw [← cT_map hπ, ← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (·.map π) g.2⟩
  have fin : ∀ X Y : Matrix n n A, X.map π = 1 → (1 - e) • X = (1 - e) • Y → X - 1 = (1 - e) • (Y - 1) := by
    intro X Y h1 h2
    refine ext ?_ ?_
    · rw [Matrix.map_sub _ (map_sub π), h1, hπ1, Matrix.map_smul' _ _ _ (map_mul π)]
      simp [he]
    · rw [smul_smul, smul_sub, h2, ← smul_sub]
      congr 1
      linear_combination hee
  refine ⟨g * ι y⁻¹, fin _ _ ?_ (hr _ _), ?_, by rw [map_mul, h1, mul_one]⟩
  · show (mat g * l (mat y⁻¹)).map π = 1
    rw [Matrix.map_mul, hl]
    exact Units.mul_inv (bc π (g : GL n A))
  · rw [map_inv, _root_.mul_inv_rev, inv_inv]
    refine fin _ _ ?_ (hlf _ _)
    show (l (mat y) * mat g⁻¹).map π = 1
    rw [Matrix.map_mul, hl]
    exact Units.mul_inv (bc π (g : GL n A))

end Split

section Haar

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Take `⟨K, hK, h1⟩` from `exists_compact_mem_nhds (1 : G)`. Establish `h2` using `congrArg (fun m : Measure G => m K) h`. Simplify using `only [Measure.coe_nnreal_smul_apply] at h2`. Conclude with `(ENNReal.mul_left_inj (Measure.measure_pos_of_mem_nhds μ h1).ne' hK.measure_lt_top.ne).1 h2` after adjusting the coercions.
-/
theorem smul_inj {μ : Measure G} [μ.IsHaarMeasure] {a b : ℝ≥0} (h : a • μ = b • μ) : a = b := by
  obtain ⟨K, hK, h1⟩ := exists_compact_mem_nhds (1 : G)
  have h2 := congrArg (fun m : Measure G => m K) h
  simp only [Measure.coe_nnreal_smul_apply] at h2
  exact_mod_cast (ENNReal.mul_left_inj (Measure.measure_pos_of_mem_nhds μ h1).ne' hK.measure_lt_top.ne).1 h2

/- English proof (translation)
The claim follows from `Measure.map_right_mul_eq_modularCharacterFun_smul μ g`.
-/
theorem map_mul_right_eq (μ : Measure G) [μ.IsHaarMeasure] (g : G) :
    μ.map (fun x => x * g) = Measure.modularCharacter g • μ :=
  Measure.map_right_mul_eq_modularCharacterFun_smul μ g

/- English proof (translation)
Set `e : G ≃* G` to `{ T with invFun := T, left_inv := hT, right_inv := hT }`. Set `μ : Measure G` to `Measure.haar`. Use `haveI : (μ.map T).IsHaarMeasure := e.isHaarMeasure_map μ hc hc`. Use `smul_inj (μ := μ.map T) ?_` and prove the remaining obligations. Rewrite using `[← map_mul_right_eq, ← Measure.map_smul, ← map_mul_right_eq, Measure.map_map (measurable_mul_const _) hc.measurable, Measure.map_map hc.measurable (measurable_mul_const _)]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules.
-/
theorem modular_involution (T : G →* G) (hc : Continuous T) (hT : ∀ x, T (T x) = x) (g : G) :
    Measure.modularCharacter (T g) = Measure.modularCharacter g := by
  let e : G ≃* G := { T with invFun := T, left_inv := hT, right_inv := hT }
  let μ : Measure G := Measure.haar
  haveI : (μ.map T).IsHaarMeasure := e.isHaarMeasure_map μ hc hc
  refine smul_inj (μ := μ.map T) ?_
  rw [← map_mul_right_eq, ← Measure.map_smul, ← map_mul_right_eq,
    Measure.map_map (measurable_mul_const _) hc.measurable, Measure.map_map hc.measurable (measurable_mul_const _)]
  congr 1
  funext x
  simp

/- English proof (translation)
Set `μ : Measure G` to `Measure.haar`. Establish `h2` using `congrArg (fun m : Measure G => m K) (map_mul_right_eq μ k)`. Simplify using `only [Measure.coe_nnreal_smul_apply] at h2`. Rewrite `h2` using `[Measure.map_apply (measurable_mul_const _) ho.measurableSet, show (fun x => x * k) ⁻¹' (K : Set G) = K from Set.ext fun x => K.mul_mem_cancel_right hk]`. Establish `h3 : (Measure.modularCharacter k : ℝ≥0∞) = 1` using `(ENNReal.mul_left_inj (ho.measure_pos μ ⟨1, one_mem _⟩).ne' hc.measure_lt_top.ne).1 (by rw [one_mul]; exact h2.symm)`.

Conclude with `h3` after adjusting the coercions.
-/
theorem modular_compact (K : Subgroup G) (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) {k : G}
    (hk : k ∈ K) : Measure.modularCharacter k = 1 := by
  let μ : Measure G := Measure.haar
  have h2 := congrArg (fun m : Measure G => m K) (map_mul_right_eq μ k)
  simp only [Measure.coe_nnreal_smul_apply] at h2
  rw [Measure.map_apply (measurable_mul_const _) ho.measurableSet,
    show (fun x => x * k) ⁻¹' (K : Set G) = K from Set.ext fun x => K.mul_mem_cancel_right hk] at h2
  have h3 : (Measure.modularCharacter k : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj (ho.measure_pos μ ⟨1, one_mem _⟩).ne' hc.measure_lt_top.ne).1
      (by rw [one_mul]; exact h2.symm)
  exact_mod_cast h3

/- English proof (translation)
Use `haveI : μ.inv.IsHaarMeasure := { toIsFiniteMeasureOnCompacts := inferInstance toIsMulLeftInvariant := inferInstance toIsOpenPosMeasure := inferInstance }`. Establish `hc` using `Measure.isMulLeftInvariant_eq_smul μ.inv μ`. Use `set c : ℝ≥0 := Measure.haarScalarFactor μ.inv μ`. Establish `h1 : (c ^ 2) • μ = (1 : ℝ≥0) • μ`. Rewrite using `[one_smul]`.

Use `conv_rhs => rw [← Measure.inv_inv μ, hc, Measure.inv_def, Measure.map_smul, ← Measure.inv_def, hc, smul_smul]`. Rewrite using `[pow_two]`. Rewrite using `[hc, (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 (smul_inj h1), one_smul]`.
-/
theorem map_inv_eq (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.inv = μ := by
  haveI : μ.inv.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }
  have hc := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  set c : ℝ≥0 := Measure.haarScalarFactor μ.inv μ
  have h1 : (c ^ 2) • μ = (1 : ℝ≥0) • μ := by
    rw [one_smul]
    conv_rhs => rw [← Measure.inv_inv μ, hc, Measure.inv_def, Measure.map_smul, ← Measure.inv_def, hc, smul_smul]
    rw [pow_two]
  rw [hc, (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 (smul_inj h1), one_smul]

end Haar

section Involution

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {σ : A →+* A} {J M : Matrix n n A}

/- English proof (translation)
Take `⟨-, -, hM, hM'⟩` from `hF`. Establish `hσσ : ∀ X : Matrix n n A, (X.map σ).map σ = X` using `fun X => by ext i j; simp [hσ]`. Set `m : GL n A` to `⟨M, M.map σ, hM', mul_eq_one_comm.1 hM'⟩`. Set `T₀ : GL n A →* GL n A` to `(MulAut.conj m).toMonoidHom.comp (bc σ)`. Establish `hT₀ : ∀ g : GL n A, (T₀ g : Matrix n n A) = M * (g : Matrix n n A).map σ * M.map σ` using `fun g => rfl`.

Establish `hmem : ∀ g : UJ σ J, T₀ g ∈ UJ σ J` using `fun g => by show cT σ (T₀ g : Matrix n n A) * J * (T₀ g : Matrix n n A) = J`. Establish `h1 : cT σ ((mat g).map σ) * J.map σ * (mat g).map σ = J.map σ`. Rewrite using `[← cT_map (σ := σ) fun _ => rfl, ← Matrix.map_mul, ← Matrix.map_mul]`. Conclude with `congrArg (·.map σ) g.2`. Establish `h2 : cT σ (M.map σ) * J.map σ * M.map σ = J`.

Rewrite using `[← cT_map (σ := σ) fun _ => rfl, ← Matrix.map_mul, ← Matrix.map_mul, hM, hσσ]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hT₀, cT_mul, cT_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = J := by rw [hM, h1, h2]`.

Establish `hcv : Continuous fun g : GL n A => (T₀ g : Matrix n n A)` using `(continuous_const.matrix_mul (Units.continuous_val.matrix_map hc)).matrix_mul continuous_const`. Establish `hc₀ : Continuous T₀` using `Units.continuous_iff.2 ⟨hcv, by`. Simplify using `only [← map_inv]`. Conclude with `hcv.comp continuous_inv⟩`. Use `⟨(T₀.comp (UJ σ J).subtype).codRestrict _ hmem, (hc₀.comp continuous_subtype_val).subtype_mk _, fun x => Subtype.ext (Units.ext ?_), fun g g' h => Subtype.ext (Units.ext ?_)⟩` and prove the remaining obligations.

Use `show M * (M * (mat x).map σ * M.map σ).map σ * M.map σ = mat x`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, hσσ, hσσ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hM', Matrix.one_mul, Matrix.mul_assoc, hM', Matrix.mul_one]`. Use `show mat g' = M * (mat g).map σ * M.map σ`. Rewrite using `[← h, Matrix.mul_assoc, hM', Matrix.mul_one]`.
-/
theorem exists_involution [TopologicalSpace A] [IsTopologicalRing A] (hc : Continuous σ) (hσ : ∀ x, σ (σ x) = x)
    (hF : Framed σ J M) : ∃ T : UJ σ J →* UJ σ J, Continuous T ∧ (∀ x, T (T x) = x) ∧
      ∀ g g' : UJ σ J, mat g' * M = M * (mat g).map σ → g' = T g := by
  obtain ⟨-, -, hM, hM'⟩ := hF
  have hσσ : ∀ X : Matrix n n A, (X.map σ).map σ = X := fun X => by ext i j; simp [hσ]
  let m : GL n A := ⟨M, M.map σ, hM', mul_eq_one_comm.1 hM'⟩
  let T₀ : GL n A →* GL n A := (MulAut.conj m).toMonoidHom.comp (bc σ)
  have hT₀ : ∀ g : GL n A, (T₀ g : Matrix n n A) = M * (g : Matrix n n A).map σ * M.map σ := fun g => rfl
  have hmem : ∀ g : UJ σ J, T₀ g ∈ UJ σ J := fun g => by
    show cT σ (T₀ g : Matrix n n A) * J * (T₀ g : Matrix n n A) = J
    have h1 : cT σ ((mat g).map σ) * J.map σ * (mat g).map σ = J.map σ := by
      rw [← cT_map (σ := σ) fun _ => rfl, ← Matrix.map_mul, ← Matrix.map_mul]
      exact congrArg (·.map σ) g.2
    have h2 : cT σ (M.map σ) * J.map σ * M.map σ = J := by
      rw [← cT_map (σ := σ) fun _ => rfl, ← Matrix.map_mul, ← Matrix.map_mul, hM, hσσ]
    calc _ = cT σ (M.map σ) * (cT σ ((mat g).map σ) * (cT σ M * J * M) * (mat g).map σ) * M.map σ := by
          rw [hT₀, cT_mul, cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [hM, h1, h2]
  have hcv : Continuous fun g : GL n A => (T₀ g : Matrix n n A) :=
    (continuous_const.matrix_mul (Units.continuous_val.matrix_map hc)).matrix_mul continuous_const
  have hc₀ : Continuous T₀ := Units.continuous_iff.2 ⟨hcv, by
    simp only [← map_inv]
    exact hcv.comp continuous_inv⟩
  refine ⟨(T₀.comp (UJ σ J).subtype).codRestrict _ hmem, (hc₀.comp continuous_subtype_val).subtype_mk _,
    fun x => Subtype.ext (Units.ext ?_), fun g g' h => Subtype.ext (Units.ext ?_)⟩
  · show M * (M * (mat x).map σ * M.map σ).map σ * M.map σ = mat x
    rw [Matrix.map_mul, Matrix.map_mul, hσσ, hσσ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hM', Matrix.one_mul,
      Matrix.mul_assoc, hM', Matrix.mul_one]
  · show mat g' = M * (mat g).map σ * M.map σ
    rw [← h, Matrix.mul_assoc, hM', Matrix.mul_one]

end Involution

section Adeles

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Set `S` to `{v : HeightOneSpectrum (𝓞 F) | a v ∉ v.adicCompletionIntegers F}`. Establish `hS : S.Finite` using `Filter.eventually_cofinite.1 a.2`. Use `haveI : Finite S := hS.to_subtype`. Set `p : Af F →ₐ[F] (∀ v : S, v.1.adicCompletion F)` to `{ toFun := fun x v => x v.1 map_one' := rfl map_mul' := fun _ _ => rfl map_zero' := rfl map_add' := fun _ _ => rfl commutes' := fun _ => rfl }`. Set `s : (∀ v : S, v.1.adicCompletion F) → Af F` to `fun y => ⟨fun v => if h : v ∈ S then y ⟨v, h⟩ else 0, by filter_upwards [hS.compl_mem_cofinite] with v hv`.

Rewrite using `[dif_neg hv]`. Conclude with `zero_mem _⟩`. Establish `hs : ∀ y, p (s y) = y` using `fun y => funext fun v => dif_pos v.2`. Apply the tactic sequence `have hs1 : ∀ v, s 1 v = if v ∈ S then 1 else 0 := fun v => by show dite _ _ _ = _ split_ifs <;> rfl`. Use `⟨_, inferInstance, inferInstance, p, s 1, inferInstance, fun y => ⟨_, hs y⟩, hs 1, fun x hx => ?_, fun v => ?_⟩` and prove the remaining obligations.

Use `FiniteAdeleRing.ext _ fun v => ?_ show s 1 v * x v = 0` and prove the remaining obligations. Rewrite using `[hs1]`. Use `split_ifs with h`. Rewrite using `[one_mul]`. Conclude with `congrFun hx ⟨v, h⟩`.

Conclude with `zero_mul _`. Use `show (1 - s 1 v) * a v ∈ _`. Rewrite using `[hs1]`. Use `split_ifs with h`. Rewrite using `[sub_self, zero_mul]`.

Conclude with `zero_mem _`. Rewrite using `[sub_zero, one_mul]`. Conclude with `not_not.1 h`.
-/
theorem exists_split (a : Af F) : ∃ (R : Type) (_ : CommRing R) (_ : Algebra F R) (p : Af F →ₐ[F] R) (e : Af F),
    IsArtinianRing R ∧ Function.Surjective p ∧ p e = 1 ∧ (∀ x, p x = 0 → e * x = 0) ∧ (1 - e) * a ∈ intAd F := by
  classical
  let S := {v : HeightOneSpectrum (𝓞 F) | a v ∉ v.adicCompletionIntegers F}
  have hS : S.Finite := Filter.eventually_cofinite.1 a.2
  haveI : Finite S := hS.to_subtype
  let p : Af F →ₐ[F] (∀ v : S, v.1.adicCompletion F) :=
    { toFun := fun x v => x v.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  let s : (∀ v : S, v.1.adicCompletion F) → Af F := fun y =>
    ⟨fun v => if h : v ∈ S then y ⟨v, h⟩ else 0, by
      filter_upwards [hS.compl_mem_cofinite] with v hv
      rw [dif_neg hv]
      exact zero_mem _⟩
  have hs : ∀ y, p (s y) = y := fun y => funext fun v => dif_pos v.2
  have hs1 : ∀ v, s 1 v = if v ∈ S then 1 else 0 := fun v => by
    show dite _ _ _ = _
    split_ifs <;> rfl
  refine ⟨_, inferInstance, inferInstance, p, s 1, inferInstance, fun y => ⟨_, hs y⟩, hs 1, fun x hx => ?_,
    fun v => ?_⟩
  · refine FiniteAdeleRing.ext _ fun v => ?_
    show s 1 v * x v = 0
    rw [hs1]
    split_ifs with h
    · rw [one_mul]
      exact congrFun hx ⟨v, h⟩
    · exact zero_mul _
  · show (1 - s 1 v) * a v ∈ _
    rw [hs1]
    split_ifs with h
    · rw [sub_self, zero_mul]
      exact zero_mem _
    · rw [sub_zero, one_mul]
      exact not_not.1 h

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [sigR, hσ]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem sigR_sigR {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (R : Type) [CommRing R] [Algebra F R]
    (x : E ⊗[F] R) : sigR σ R (sigR σ R x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Use `choose d hd0 hd using fun k => P.levelaf_denom (x k)`. Establish `hD0 : algebraMap (𝓞 F) F (∏ k, d k) ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (Finset.prod_ne_zero_iff.2 fun k _ => hd0 k)`. Take `⟨R, _, _, p, e, hR, hp, hpe, hker, hint⟩` from `exists_split (algebraMap F (Af F) (algebraMap (𝓞 F) F (∏ k, d k))⁻¹)`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `letI : Algebra R (E ⊗[F] R) := Algebra.TensorProduct.rightAlgebra`.

Use `haveI : Module.Finite R (E ⊗[F] R) := Module.Finite.equiv (Algebra.TensorProduct.commRight F R E).toLinearEquiv`. Use `haveI : IsArtinianRing (E ⊗[F] R) := IsArtinianRing.of_finite R _`. Use `letI : Algebra ℚ (E ⊗[F] R) := ((inclE (F := F) R).comp (algebraMap ℚ E)).toAlgebra`. Use `⟨E ⊗[F] R, inferInstance, sigR σ R, (Algebra.TensorProduct.map (AlgHom.id F E) p).toRingHom, 1 ⊗ₜ e, fun y => ?_, Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hp, ?_, fun y hy => ?_, ?_, generic_of_semilocal (δ := inclE R δ) (hδ.isUnit.map _) ?_, fun k => ?_⟩` and prove the remaining obligations. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a b => simp [sigR]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Simplify using `[hpe, Algebra.TensorProduct.one_def]`. Establish `hy' : y ∈ RingHom.ker (Algebra.TensorProduct.map (AlgHom.id F E) p)` using `hy`.

Rewrite `hy'` using `[Algebra.TensorProduct.lTensor_ker _ hp]`. Use `clear hy`. Proceed by induction on `hy' using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨z, hz, rfl⟩` from `hy`.

Simplify using `[hker z hz]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]`. Consider the case `smul a x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]`. Simplify using `[sigR]`.

Simplify using `[sigR, inclE, hσδ, TensorProduct.neg_tmul]`. Establish `h1` using `P.levelaf_tmul_mem (E := E) 1 hint`. Rewrite `h1` using `[map_one]`. Establish `h2` using `mul_mem h1 (mul_mem (P.levelafC_mem (∏ j ∈ Finset.univ.erase k, d j)) (hd k))`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[← mul_assoc (P.levelafC _ _), ← P.levelafC_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ k), ← mul_assoc, P.levelafC, Algebra.TensorProduct.tmul_mul_tmul, IsScalarTower.algebraMap_apply (𝓞 F) F (Af F), mul_assoc, ← map_mul, inv_mul_cancel₀ hD0, map_one, mul_one, mul_one, Tenso …`. Both sides reduce to the same expression.
-/
theorem exists_split_tensor (σ : E →ₐ[F] E) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ) {κ : Type} [Fintype κ]
    (x : κ → E ⊗[F] Af F) : ∃ (B : Type) (_ : CommRing B) (σ' : B →+* B) (π : E ⊗[F] Af F →+* B)
      (e : E ⊗[F] Af F), (∀ x, π (sigR σ (Af F) x) = σ' (π x)) ∧ Function.Surjective π ∧ π e = 1 ∧
      (∀ x, π x = 0 → e * x = 0) ∧ sigR σ (Af F) e = e ∧ Generic σ' ∧ ∀ k, (1 - e) * x k ∈ IntAf F E := by
  classical
  choose d hd0 hd using fun k => P.levelaf_denom (x k)
  have hD0 : algebraMap (𝓞 F) F (∏ k, d k) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (Finset.prod_ne_zero_iff.2 fun k _ => hd0 k)
  obtain ⟨R, _, _, p, e, hR, hp, hpe, hker, hint⟩ :=
    exists_split (algebraMap F (Af F) (algebraMap (𝓞 F) F (∏ k, d k))⁻¹)
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  letI : Algebra R (E ⊗[F] R) := Algebra.TensorProduct.rightAlgebra
  haveI : Module.Finite R (E ⊗[F] R) :=
    Module.Finite.equiv (Algebra.TensorProduct.commRight F R E).toLinearEquiv
  haveI : IsArtinianRing (E ⊗[F] R) := IsArtinianRing.of_finite R _
  letI : Algebra ℚ (E ⊗[F] R) := ((inclE (F := F) R).comp (algebraMap ℚ E)).toAlgebra
  refine ⟨E ⊗[F] R, inferInstance, sigR σ R, (Algebra.TensorProduct.map (AlgHom.id F E) p).toRingHom,
    1 ⊗ₜ e, fun y => ?_, Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hp, ?_, fun y hy => ?_, ?_,
    generic_of_semilocal (δ := inclE R δ) (hδ.isUnit.map _) ?_, fun k => ?_⟩
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  · simp [hpe, Algebra.TensorProduct.one_def]
  · have hy' : y ∈ RingHom.ker (Algebra.TensorProduct.map (AlgHom.id F E) p) := hy
    rw [Algebra.TensorProduct.lTensor_ker _ hp] at hy'
    clear hy
    induction hy' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      simp [hker z hz]
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul a x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  · simp [sigR]
  · simp [sigR, inclE, hσδ, TensorProduct.neg_tmul]
  · have h1 := P.levelaf_tmul_mem (E := E) 1 hint
    rw [map_one] at h1
    have h2 := mul_mem h1 (mul_mem (P.levelafC_mem (∏ j ∈ Finset.univ.erase k, d j)) (hd k))
    convert h2 using 1
    rw [← mul_assoc (P.levelafC _ _), ← P.levelafC_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ k), ← mul_assoc,
      P.levelafC, Algebra.TensorProduct.tmul_mul_tmul, IsScalarTower.algebraMap_apply (𝓞 F) F (Af F), mul_assoc,
      ← map_mul, inv_mul_cancel₀ hD0, map_one, mul_one, mul_one, TensorProduct.tmul_sub]
    rfl

end Adeles

/- English proof (translation)
Establish `h` using `hu _ fun i => sum_mem fun j (_ : j ∈ Finset.univ) => mul_mem (hX i j) (hv y hy j)`. Rewrite using `[sub_eq_iff_eq_add.1 hk, add_mulVec, one_mulVec]`. Use `add_mem ?_ hy` and prove the remaining obligations. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`.

Simplify using `only [mulVec, dotProduct, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Take the linear combination `(-c * X i j * y j) * u.mul_inv - (c * X i j * y j * u * ((u⁻¹ : Aˣ) : A)) * v.mul_inv`.
-/
theorem mulVec_mem {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {S : Type} [CommRing S]
    [Algebra S A] (R : Subring A) (Λ : Submodule S (n → A)) (u v : Aˣ)
    (hu : ∀ w : n → A, (∀ i, w i ∈ R) → (fun i => (u : A) * w i) ∈ Λ) (hv : ∀ w ∈ Λ, ∀ i, (v : A) * w i ∈ R)
    {k X : Matrix n n A} {c : A} (hk : k - 1 = c • X)
    (hX : ∀ i j, c * (((u⁻¹ : Aˣ) : A) * ((v⁻¹ : Aˣ) : A) * X i j) ∈ R) {y : n → A} (hy : y ∈ Λ) : k *ᵥ y ∈ Λ := by
  have h := hu _ fun i => sum_mem fun j (_ : j ∈ Finset.univ) => mul_mem (hX i j) (hv y hy j)
  rw [sub_eq_iff_eq_add.1 hk, add_mulVec, one_mulVec]
  refine add_mem ?_ hy
  convert h using 1
  funext i
  simp only [mulVec, dotProduct, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  linear_combination (-c * X i j * y j) * u.mul_inv - (c * X i j * y j * u * ((u⁻¹ : Aˣ) : A)) * v.mul_inv

/- English proof (translation)
Use `by_contra! h`. Establish `hs : Function.Surjective (algebraMap I.F I.E)` using `fun a => (I.cm.fixed a).1 (by`. Assume the negation of the conclusion as `hne`. Conclude with `h (star a - a) (sub_ne_zero.2 hne) (by show star _ = _; simp))`. Use `(LinearEquiv.ofBijective (Algebra.linearMap I.F I.E) ⟨(algebraMap I.F I.E).injective, hs⟩).finrank_eq` as an intermediate fact.

Rewrite `this` using `[I.cm.deg2, Module.finrank_self]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_skew (I : AutInst) : ∃ δ : I.E, δ ≠ 0 ∧ I.cm.sig δ = -δ := by
  by_contra! h
  have hs : Function.Surjective (algebraMap I.F I.E) := fun a => (I.cm.fixed a).1 (by
    by_contra hne
    exact h (star a - a) (sub_ne_zero.2 hne) (by show star _ = _; simp))
  have := (LinearEquiv.ofBijective (Algebra.linearMap I.F I.E) ⟨(algebraMap I.F I.E).injective, hs⟩).finrank_eq
  rw [I.cm.deg2, Module.finrank_self] at this
  omega

/- English proof (translation)
Take `⟨_, _, _, hKc, hKo, -, -⟩` from `GlobalTheory.CongTop.adelic_topology I`. Take `⟨t, hr, h2, hsc, ho, hc, hσ, h0⟩` from `GlobalTheory.CongTop.exists_topology I.F I.E I.cm.sig`. Establish `hL : I.Lf = Formalism.UG.latS (F` using `I.F) (Af I.F) (IntAf I.F I.E) I.L := by`. Unfold `AutInst.Lf lamAf Formalism.UG.latS`. Rewrite using `[Set.image_eq_range]`.

Both sides reduce to the same expression. Take `⟨c, hc0, hlow⟩` from `Formalism.UG.P.adelstabL_lower (F := I.F) I.L I.L_span`. Take `⟨d, hd0, hup⟩` from `Formalism.UG.P.adelstabL_upper (F := I.F) I.L (Module.Finite.iff_fg.2 I.L_fg)`. Rewrite `hlow`, `hup` using `[← hL]`. Establish `hun : ∀ g : ℕ, 1 ≤ g → IsUnit (g : I.E ⊗[I.F] Af I.F)` using `fun g hg => by`.

Establish `: (g : I.E) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Use `this.isUnit.map (Formalism.UG.inclE (F := I.F) (Af I.F))` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Take `⟨u, hu⟩` from `GlobalTheory.CongTop.isUnit_levelafC I.F I.E hc0`. Take `⟨v, hv⟩` from `GlobalTheory.CongTop.isUnit_levelafC I.F I.E hd0`.

Rewrite `hlow` using `[← hu]`. Rewrite `hup` using `[← hv]`. Take `⟨hΛo, hΛc⟩` from `GlobalTheory.CongTop.isOpen_isCompact_of_bounds _ ho hc I.Lf u v hlow hup`. Establish `hsing : ∀ j, (Pi.single j (u : I.E ⊗[I.F] Af I.F) : Fin I.n → _) ∈ I.Lf` using `fun j => by`. Use `hlow (Pi.single j 1) fun i => ?_ using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `by_cases h : i = j <;> simp [h]`. Rewrite using `[Pi.single_apply] split_ifs exacts [one_mem _, zero_mem _]`. Establish `htop` using `GlobalTheory.CongTop.top_eq hΛo hΛc u hsing hun h0 _ I.topf I.topf_group I.topf_open I.topf_basis`. Establish `hss : ∀ x, I.cm.sig (I.cm.sig x) = x` using `fun x => star_star x`.

Take `⟨M, hM⟩` from `exists_framed (σ := starRingEnd I.E) hss I.J_herm I.J_det`. Establish `hF : Framed (sigR I.cm.sig (Af I.F)) (I.J.map (inclE (F` using `I.F) (Af I.F))) (M.map (inclE (Af I.F))) := hM.map fun x => rfl`. Take `⟨T, hTc, hT, hT'⟩` from `exists_involution hσ (sigR_sigR hss _) hF`. Establish `hTc' : @Continuous I.Gf I.Gf I.topf I.topf T`. Rewrite using `[htop]`.

Conclude with `hTc`. Take `⟨δ, hδ, hσδ⟩` from `exists_skew I`. Take `⟨B, _, σ', π, e, h1, h2, h3, h4, h5, h6, h7⟩` from `exists_split_tensor I.cm.sig hδ hσδ (κ := Bool × Fin I.n × Fin I.n) fun p => (u⁻¹ : _ˣ) * (v⁻¹ : _ˣ) * (I.fmat (bif p.1 then g else g⁻¹) - 1) p.2.1 p.2.2`. Take `⟨k, hk, hk', hkg⟩` from `exists_char_eq h1 h2 h3 h4 h5 (sigR_sigR hss _) hF h6 (Measure.modularCharacter (G := I.Gf)) (fun x x' h => by`. Rewrite using `[hT' x x' h]`.

Conclude with `modular_involution (G := I.Gf) T hTc' hT x) g`. Establish `hkK : k ∈ (stabGL I.Lf).subgroupOf (UPts I.cm.sig I.J (Af I.F))` using `fun y => ⟨fun hy => mulVec_mem _ _ u v hlow hup hk (fun i j => h7 (true, i, j)) hy, fun hy => by`. Use `mulVec_mem _ _ u v hlow hup hk' (fun i j => h7 (false, i, j)) hy` as an intermediate fact. Establish `e1 : mat k⁻¹ *ᵥ (mat k *ᵥ y) = y`. Rewrite using `[← mul_mulVec_UJ, inv_mul_cancel]`.

Conclude with `one_mulVec y`. Conclude with `e1 ▸ this⟩`. Establish `h8` using `modular_compact (G := I.Gf) _ hKo hKc hkK`. Rewrite using `[map_mul_right_eq, show Measure.modularCharacter g = 1 from hkg.symm.trans h8, one_smul]`.
-/
theorem finite_unimodular (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] (g : I.Gf) :
    Measure.map (fun x => x * g) μf = μf := by
  obtain ⟨_, _, _, hKc, hKo, -, -⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨t, hr, h2, hsc, ho, hc, hσ, h0⟩ := GlobalTheory.CongTop.exists_topology I.F I.E I.cm.sig
  have hL : I.Lf = Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
    unfold AutInst.Lf lamAf Formalism.UG.latS
    rw [Set.image_eq_range]
    rfl
  obtain ⟨c, hc0, hlow⟩ := Formalism.UG.P.adelstabL_lower (F := I.F) I.L I.L_span
  obtain ⟨d, hd0, hup⟩ := Formalism.UG.P.adelstabL_upper (F := I.F) I.L (Module.Finite.iff_fg.2 I.L_fg)
  rw [← hL] at hlow hup
  have hun : ∀ g : ℕ, 1 ≤ g → IsUnit (g : I.E ⊗[I.F] Af I.F) := fun g hg => by
    have : (g : I.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have := this.isUnit.map (Formalism.UG.inclE (F := I.F) (Af I.F))
    rwa [map_natCast] at this
  obtain ⟨u, hu⟩ := GlobalTheory.CongTop.isUnit_levelafC I.F I.E hc0
  obtain ⟨v, hv⟩ := GlobalTheory.CongTop.isUnit_levelafC I.F I.E hd0
  rw [← hu] at hlow
  rw [← hv] at hup
  obtain ⟨hΛo, hΛc⟩ := GlobalTheory.CongTop.isOpen_isCompact_of_bounds _ ho hc I.Lf u v hlow hup
  have hsing : ∀ j, (Pi.single j (u : I.E ⊗[I.F] Af I.F) : Fin I.n → _) ∈ I.Lf := fun j => by
    convert hlow (Pi.single j 1) fun i => ?_ using 1
    · funext i
      by_cases h : i = j <;> simp [h]
    · rw [Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
  have htop := GlobalTheory.CongTop.top_eq hΛo hΛc u hsing hun h0 _ I.topf I.topf_group I.topf_open I.topf_basis
  have hss : ∀ x, I.cm.sig (I.cm.sig x) = x := fun x => star_star x
  obtain ⟨M, hM⟩ := exists_framed (σ := starRingEnd I.E) hss I.J_herm I.J_det
  have hF : Framed (sigR I.cm.sig (Af I.F)) (I.J.map (inclE (F := I.F) (Af I.F))) (M.map (inclE (Af I.F))) :=
    hM.map fun x => rfl
  obtain ⟨T, hTc, hT, hT'⟩ := exists_involution hσ (sigR_sigR hss _) hF
  have hTc' : @Continuous I.Gf I.Gf I.topf I.topf T := by
    rw [htop]
    exact hTc
  obtain ⟨δ, hδ, hσδ⟩ := exists_skew I
  obtain ⟨B, _, σ', π, e, h1, h2, h3, h4, h5, h6, h7⟩ := exists_split_tensor I.cm.sig hδ hσδ
    (κ := Bool × Fin I.n × Fin I.n) fun p => (u⁻¹ : _ˣ) * (v⁻¹ : _ˣ) *
      (I.fmat (bif p.1 then g else g⁻¹) - 1) p.2.1 p.2.2
  obtain ⟨k, hk, hk', hkg⟩ := exists_char_eq h1 h2 h3 h4 h5 (sigR_sigR hss _) hF h6
    (Measure.modularCharacter (G := I.Gf))
    (fun x x' h => by
      rw [hT' x x' h]
      exact modular_involution (G := I.Gf) T hTc' hT x) g
  have hkK : k ∈ (stabGL I.Lf).subgroupOf (UPts I.cm.sig I.J (Af I.F)) := fun y => ⟨fun hy =>
    mulVec_mem _ _ u v hlow hup hk (fun i j => h7 (true, i, j)) hy, fun hy => by
      have := mulVec_mem _ _ u v hlow hup hk' (fun i j => h7 (false, i, j)) hy
      have e1 : mat k⁻¹ *ᵥ (mat k *ᵥ y) = y := by
        rw [← mul_mulVec_UJ, inv_mul_cancel]
        exact one_mulVec y
      exact e1 ▸ this⟩
  have h8 := modular_compact (G := I.Gf) _ hKo hKc hkK
  rw [map_mul_right_eq, show Measure.modularCharacter g = 1 from hkg.symm.trans h8, one_smul]

/- English proof (translation)
Introduce `I μf _ _`. Take `⟨_, _, _, -⟩` from `GlobalTheory.CongTop.adelic_topology I`. Use `haveI : μf.IsMulRightInvariant := ⟨finite_unimodular I μf⟩`. Use `haveI : ∀ v, (Formalism.REAL.muG (I.ε v)).IsMulRightInvariant := fun v => ⟨Formalism.REAL.indefinite_unitary_unimodular _ _⟩`. Use `haveI : ∀ v, (Formalism.REAL.muG (I.ε v)).IsHaarMeasure := fun v => by unfold Formalism.REAL.muG; infer_instance`.

Use `haveI : (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).IsHaarMeasure := Measure.pi.isHaarMeasure _`. Use `haveI : (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).IsMulRightInvariant := Measure.pi.isMulRightInvariant _`. Use `haveI : (I.muA μf).IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _`. Use `haveI : (I.muA μf).IsMulRightInvariant := Measure.prod.instIsMulRightInvariant`. Conclude with `⟨map_mul_left_eq_self _, map_mul_right_eq_self _, map_inv_eq _, finite_unimodular I μf, fun U hU hne => hU.measure_pos _ hne⟩`.
-/
theorem adelic_unimodular : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf], (∀ g : I.GA, Measure.map (fun x => g * x) (I.muA μf) = I.muA μf) ∧ (∀ g : I.GA, Measure.map (fun x => x * g) (I.muA μf) = I.muA μf) ∧ Measure.map (fun x : I.GA => x⁻¹) (I.muA μf) = I.muA μf ∧ (∀ g : I.Gf, Measure.map (fun x => x * g) μf = μf) ∧ ∀ U : Set I.GA, IsOpen U → U.Nonempty → 0 < I.muA μf U := by
  intro I μf _ _
  obtain ⟨_, _, _, -⟩ := GlobalTheory.CongTop.adelic_topology I
  haveI : μf.IsMulRightInvariant := ⟨finite_unimodular I μf⟩
  haveI : ∀ v, (Formalism.REAL.muG (I.ε v)).IsMulRightInvariant := fun v => ⟨Formalism.REAL.indefinite_unitary_unimodular _ _⟩
  haveI : ∀ v, (Formalism.REAL.muG (I.ε v)).IsHaarMeasure := fun v => by unfold Formalism.REAL.muG; infer_instance
  haveI : (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).IsHaarMeasure := Measure.pi.isHaarMeasure _
  haveI : (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).IsMulRightInvariant := Measure.pi.isMulRightInvariant _
  haveI : (I.muA μf).IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  haveI : (I.muA μf).IsMulRightInvariant := Measure.prod.instIsMulRightInvariant
  exact ⟨map_mul_left_eq_self _, map_mul_right_eq_self _, map_inv_eq _, finite_unimodular I μf,
    fun U hU hne => hU.measure_pos _ hne⟩

end GlobalTheory.AdelicUnimod
