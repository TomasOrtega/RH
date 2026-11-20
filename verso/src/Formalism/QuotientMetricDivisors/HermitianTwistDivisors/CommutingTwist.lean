import Mathlib
import Formalism.QuotientMetricDivisors.EigenRatHermLcv
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjugateWeightLatticeOfGeneral

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

namespace FinitelyNonzeroLinear

/- English proof (translation)
Establish `key : ∀ w, star (F *ᵥ w) ⬝ᵥ Hc *ᵥ (F *ᵥ w) = star w ⬝ᵥ (Fᴴ * Hc * F) *ᵥ w`. Introduce `w`. Simplify using `only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Establish `h0 : ∀ w, F *ᵥ w = 0`. Introduce `w`.

Assume the negation of the conclusion as `hw`. Establish `hpos` using `hH.dotProduct_mulVec_pos hw`. Rewrite `hpos` using `[key, h]`. Simplify using `at hpos`. Use extensionality with `i k`.

Use `congrFun (h0 (Pi.single k 1)) i` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_single_one]`.
-/
theorem eq_zero_of_form {n m : ℕ} {Hc : Matrix (Fin n) (Fin n) ℂ} (hH : Hc.PosDef)
    (F : Matrix (Fin n) (Fin m) ℂ) (h : Fᴴ * Hc * F = 0) : F = 0 := by
  have key : ∀ w, star (F *ᵥ w) ⬝ᵥ Hc *ᵥ (F *ᵥ w) = star w ⬝ᵥ (Fᴴ * Hc * F) *ᵥ w := by
    intro w
    simp only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have h0 : ∀ w, F *ᵥ w = 0 := by
    intro w
    by_contra hw
    have hpos := hH.dotProduct_mulVec_pos hw
    rw [key, h] at hpos
    simp at hpos
  ext i k
  have := congrFun (h0 (Pi.single k 1)) i
  simpa [Matrix.mulVec_single_one] using this

/- English proof (translation)
Establish `hHh : Hcᴴ = Hc` using `hH.isHermitian`. Establish `hE : Eᴴ * Hc = Hc * M`. Use `congrArg Matrix.conjTranspose hadj` as an intermediate fact. Rewrite `this` using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh]`. Conclude with `this.symm`.

Establish `A : ∀ X : Matrix (Fin n) (Fin n) ℂ, Mᴴ * (Hc * X) = Hc * (E * X)` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, hadj, Matrix.mul_assoc]`. Establish `B : ∀ X : Matrix (Fin n) (Fin n) ℂ, Eᴴ * (Hc * X) = Hc * (M * X)` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, hE, Matrix.mul_assoc]`. Establish `MM : ∀ X : Matrix (Fin n) (Fin n) ℂ, M * (M * X) = M * X` using `fun X => by`.

Rewrite using `[← Matrix.mul_assoc, hM]`. Establish `EM : ∀ X : Matrix (Fin n) (Fin n) ℂ, E * (M * X) = M * (E * X)` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, hc, Matrix.mul_assoc]`. Establish `h1 : M - M * E = 0`. Apply `eq_zero_of_form hH` to reduce the goal to its premises.

Simplify using `only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, sub_mul, mul_sub, Matrix.mul_assoc, A, B, MM, EM, hM, hc]`. Normalize the expressions using the abelian group laws. Establish `h2 : E - M * E = 0`. Apply `eq_zero_of_form hH` to reduce the goal to its premises. Simplify using `only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, sub_mul, mul_sub, Matrix.mul_assoc, A, B, MM, EM, hM, hc]`.

Normalize the expressions using the abelian group laws. Rewrite `h1`, `h2` using `[sub_eq_zero]`. Conclude with `h2.trans h1.symm`.
-/
theorem normal_idem {n : ℕ} {Hc : Matrix (Fin n) (Fin n) ℂ} (hH : Hc.PosDef)
    (M E : Matrix (Fin n) (Fin n) ℂ) (hM : M * M = M) (hadj : Mᴴ * Hc = Hc * E)
    (hc : E * M = M * E) : E = M := by
  have hHh : Hcᴴ = Hc := hH.isHermitian
  have hE : Eᴴ * Hc = Hc * M := by
    have := congrArg Matrix.conjTranspose hadj
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hHh] at this
    exact this.symm
  have A : ∀ X : Matrix (Fin n) (Fin n) ℂ, Mᴴ * (Hc * X) = Hc * (E * X) := fun X => by
    rw [← Matrix.mul_assoc, hadj, Matrix.mul_assoc]
  have B : ∀ X : Matrix (Fin n) (Fin n) ℂ, Eᴴ * (Hc * X) = Hc * (M * X) := fun X => by
    rw [← Matrix.mul_assoc, hE, Matrix.mul_assoc]
  have MM : ∀ X : Matrix (Fin n) (Fin n) ℂ, M * (M * X) = M * X := fun X => by
    rw [← Matrix.mul_assoc, hM]
  have EM : ∀ X : Matrix (Fin n) (Fin n) ℂ, E * (M * X) = M * (E * X) := fun X => by
    rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc]
  have h1 : M - M * E = 0 := by
    apply eq_zero_of_form hH
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, sub_mul, mul_sub,
      Matrix.mul_assoc, A, B, MM, EM, hM, hc]
    abel
  have h2 : E - M * E = 0 := by
    apply eq_zero_of_form hH
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, sub_mul, mul_sub,
      Matrix.mul_assoc, A, B, MM, EM, hM, hc]
    abel
  rw [sub_eq_zero] at h1 h2
  exact h2.trans h1.symm

section Ext

variable {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω)

structure Fnl where
  toFun : Ω → K
  add : ∀ c c', toFun (c + c') = toFun c + toFun c'
  smul : ∀ (a : K) (c : Ω), toFun (j a * c) = a * toFun c

variable {j}

/- English proof (translation)
Use `letI : Algebra K Ω := j.toAlgebra`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual K Ω, φ c ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hc ((Module.forall_dual_apply_eq_zero_iff K c).1 h)`.

Use `⟨⟨fun x => (φ c)⁻¹ * φ x, fun x y => by simp only [map_add, mul_add], fun a x => ?_⟩, ?_⟩` and prove the remaining obligations. Use `show (φ c)⁻¹ * φ (j a * x) = a * ((φ c)⁻¹ * φ x)`. Rewrite using `[show j a * x = a • x from (Algebra.smul_def a x).symm, map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `show (φ c)⁻¹ * φ c = 1`.

Conclude with `inv_mul_cancel₀ hφ`.
-/
private theorem exists_fnl_apply_eq_one_of_ne_zero (c : Ω) (hc : c ≠ 0) : ∃ ρ : Fnl j, ρ.toFun c = 1 := by
  letI : Algebra K Ω := j.toAlgebra
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K Ω, φ c ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc ((Module.forall_dual_apply_eq_zero_iff K c).1 h)
  refine ⟨⟨fun x => (φ c)⁻¹ * φ x, fun x y => by simp only [map_add, mul_add], fun a x => ?_⟩, ?_⟩
  · show (φ c)⁻¹ * φ (j a * x) = a * ((φ c)⁻¹ * φ x)
    rw [show j a * x = a • x from (Algebra.smul_def a x).symm, map_smul, smul_eq_mul]
    ring
  · show (φ c)⁻¹ * φ c = 1
    exact inv_mul_cancel₀ hφ

/- English proof (translation)
Simplify using `using ρ.smul 0 0`.
-/
theorem Fnl.zero (ρ : Fnl j) : ρ.toFun 0 = 0 := by
  simpa using ρ.smul 0 0

/- English proof (translation)
Conclude with `map_sum ({ toFun := ρ.toFun, map_zero' := ρ.zero, map_add' := ρ.add } : Ω →+ K) f s`.
-/
theorem Fnl.sum (ρ : Fnl j) {ι : Type} (s : Finset ι) (f : ι → Ω) :
    ρ.toFun (∑ i ∈ s, f i) = ∑ i ∈ s, ρ.toFun (f i) := by
  exact map_sum ({ toFun := ρ.toFun, map_zero' := ρ.zero, map_add' := ρ.add } : Ω →+ K) f s

variable (j) in
/- English proof (translation)
Take `⟨ρ, hρ⟩` from `exists_fnl_apply_eq_one_of_ne_zero (j := j) (1 : Ω) one_ne_zero`. Use `⟨ρ, fun a => ?_⟩` and prove the remaining obligations. Establish `h` using `ρ.smul a 1`. Rewrite `h` using `[mul_one, hρ, mul_one]`. Conclude with `h`.
-/
theorem exists_retract : ∃ ρ : Fnl j, ∀ a, ρ.toFun (j a) = a := by
  obtain ⟨ρ, hρ⟩ := exists_fnl_apply_eq_one_of_ne_zero (j := j) (1 : Ω) one_ne_zero
  refine ⟨ρ, fun a => ?_⟩
  have h := ρ.smul a 1
  rw [mul_one, hρ, mul_one] at h
  exact h

variable (j) in
/- English proof (translation)
Assume the negation of the conclusion as `hc`. Take `⟨ρ, hρ⟩` from `exists_fnl_apply_eq_one_of_ne_zero (j := j) c hc`. Rewrite `hρ` using `[h ρ]`. Conclude with `zero_ne_one hρ`.
-/
theorem eq_zero_of_fnl (c : Ω) (h : ∀ ρ : Fnl j, ρ.toFun c = 0) : c = 0 := by
  by_contra hc
  obtain ⟨ρ, hρ⟩ := exists_fnl_apply_eq_one_of_ne_zero (j := j) c hc
  rw [h ρ] at hρ
  exact zero_ne_one hρ

/- English proof (translation)
Use extensionality with `i k`. Simplify using `only [Matrix.map_apply, Matrix.mul_apply]`. Rewrite using `[ρ.sum]`. Conclude with `Finset.sum_congr rfl fun l _ => ρ.smul _ _`.
-/
theorem fnl_mul_left {l m n : ℕ} (ρ : Fnl j) (A : Matrix (Fin l) (Fin m) K)
    (M : Matrix (Fin m) (Fin n) Ω) : (A.map j * M).map ρ.toFun = A * M.map ρ.toFun := by
  ext i k
  simp only [Matrix.map_apply, Matrix.mul_apply]
  rw [ρ.sum]
  exact Finset.sum_congr rfl fun l _ => ρ.smul _ _

/- English proof (translation)
Use extensionality with `i k`. Simplify using `only [Matrix.map_apply, Matrix.mul_apply]`. Rewrite using `[ρ.sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm, ρ.smul, mul_comm]`.
-/
theorem fnl_mul_right {l m n : ℕ} (ρ : Fnl j) (M : Matrix (Fin l) (Fin m) Ω)
    (A : Matrix (Fin m) (Fin n) K) : (M * A.map j).map ρ.toFun = M.map ρ.toFun * A := by
  ext i k
  simp only [Matrix.map_apply, Matrix.mul_apply]
  rw [ρ.sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm, ρ.smul, mul_comm]

/- English proof (translation)
Unfold `extSpan at hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨z, hz, rfl⟩` from `hx`. Introduce `ρ`.

Establish `e : (fun i => ρ.toFun (j (z i))) = ρ.toFun 1 • z`. Use function extensionality and compare the values at `i`. Establish `h` using `ρ.smul (z i) 1`. Rewrite `h` using `[mul_one]`. Rewrite using `[h, Pi.smul_apply, smul_eq_mul, mul_comm]`.

Use `show (fun i => ρ.toFun (j (z i))) ∈ Z`. Rewrite using `[e]`. Conclude with `Z.smul_mem _ hz`. Consider the case `zero`. Introduce `ρ`.

Use `show (fun _ => ρ.toFun 0) ∈ Z`. Rewrite using `[ρ.zero]`. Conclude with `Z.zero_mem`. Consider the case `add x y _ _ hx hy`. Introduce `ρ`.

Establish `h` using `Z.add_mem (hx ρ) (hy ρ)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Conclude with `ρ.add _ _`. Consider the case `smul c x _ hx`.

Introduce `ρ`. Conclude with `hx ⟨fun t => ρ.toFun (c * t), fun t t' => by show ρ.toFun (c * (t + t')) = ρ.toFun (c * t) + ρ.toFun (c * t')`. Rewrite using `[mul_add, ρ.add],`. Use `fun a t => by show ρ.toFun (c * (j a * t)) = a * ρ.toFun (c * t)`. Rewrite using `[mul_left_comm, ρ.smul]⟩`.
-/
theorem fnl_extSpan {n : ℕ} (Z : Submodule K (Fin n → K)) (y : Fin n → Ω)
    (hy : y ∈ extSpan j Z) : ∀ ρ : Fnl j, (fun i => ρ.toFun (y i)) ∈ Z := by
  unfold extSpan at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    intro ρ
    have e : (fun i => ρ.toFun (j (z i))) = ρ.toFun 1 • z := by
      funext i
      have h := ρ.smul (z i) 1
      rw [mul_one] at h
      rw [h, Pi.smul_apply, smul_eq_mul, mul_comm]
    show (fun i => ρ.toFun (j (z i))) ∈ Z
    rw [e]
    exact Z.smul_mem _ hz
  | zero =>
    intro ρ
    show (fun _ => ρ.toFun 0) ∈ Z
    rw [ρ.zero]
    exact Z.zero_mem
  | add x y _ _ hx hy =>
    intro ρ
    have h := Z.add_mem (hx ρ) (hy ρ)
    convert h using 1
    funext i
    exact ρ.add _ _
  | smul c x _ hx =>
    intro ρ
    exact hx ⟨fun t => ρ.toFun (c * t),
      fun t t' => by
        show ρ.toFun (c * (t + t')) = ρ.toFun (c * t) + ρ.toFun (c * t')
        rw [mul_add, ρ.add],
      fun a t => by
        show ρ.toFun (c * (j a * t)) = a * ρ.toFun (c * t)
        rw [mul_left_comm, ρ.smul]⟩

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, map_sum, map_mul]`.
-/
theorem map_mulVec' {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) (x : Fin n → K) :
    (A.map j) *ᵥ (fun i => j (x i)) = fun i => j ((A *ᵥ x) i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

/- English proof (translation)
Unfold `extSpan`. Conclude with `Submodule.subset_span ⟨z, hz, rfl⟩`.
-/
theorem mem_extSpan {n : ℕ} {Z : Submodule K (Fin n → K)} {z : Fin n → K} (hz : z ∈ Z) :
    (fun i => j (z i)) ∈ extSpan j Z := by
  unfold extSpan
  exact Submodule.subset_span ⟨z, hz, rfl⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Unfold `extSpan`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Rewrite using `[SetLike.mem_coe, LinearMap.mem_range]`.

Conclude with `⟨fun i => j (z i), by rw [Matrix.mulVecLin_apply, map_mulVec', h2 z hz]⟩`. Introduce and unpack `_ ⟨y, rfl⟩`. Establish `hcol : ∀ k, (fun i => j (e i k)) ∈ extSpan j Z` using `fun k => by`. Establish `hz` using `h1 (Pi.single k 1)`. Rewrite `hz` using `[Matrix.mulVec_single_one]`.

Conclude with `mem_extSpan hz`. Establish `hy : (e.map j).mulVecLin y = ∑ k, y k • (fun i => j (e i k))`. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`.

Rewrite using `[hy]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hcol k)`.
-/
theorem extSpan_eq_range {n : ℕ} (Z : Submodule K (Fin n → K)) (e : Matrix (Fin n) (Fin n) K)
    (h1 : ∀ x, e *ᵥ x ∈ Z) (h2 : ∀ z ∈ Z, e *ᵥ z = z) :
    extSpan j Z = LinearMap.range (e.map j).mulVecLin := by
  apply le_antisymm
  · unfold extSpan
    rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_range]
    exact ⟨fun i => j (z i), by rw [Matrix.mulVecLin_apply, map_mulVec', h2 z hz]⟩
  · rintro _ ⟨y, rfl⟩
    have hcol : ∀ k, (fun i => j (e i k)) ∈ extSpan j Z := fun k => by
      have hz := h1 (Pi.single k 1)
      rw [Matrix.mulVec_single_one] at hz
      exact mem_extSpan hz
    have hy : (e.map j).mulVecLin y = ∑ k, y k • (fun i => j (e i k)) := by
      funext i
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hy]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hcol k)

end Ext

end FinitelyNonzeroLinear

open FinitelyNonzeroLinear in
/- English proof (translation)
Introduce `K Ω _ _ j n 𝒯 Z hZ B hB z hz`. Take `⟨S, hS⟩` from `hZ`. Take `⟨ρ, hρ⟩` from `exists_retract j`. Establish `hstab : ∀ χ, ∀ x ∈ simEig j 𝒯 χ, B.map j *ᵥ x ∈ simEig j 𝒯 χ`. Introduce `χ x hx`.

Establish `hx' : ∀ T ∈ 𝒯, (T.map j).mulVec x = χ T • x` using `hx`. Use `show ∀ T ∈ 𝒯, (T.map j).mulVec (B.map j *ᵥ x) = χ T • (B.map j *ᵥ x)`. Introduce `T hT`. Establish `hc : T.map j * B.map j = B.map j * T.map j`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, hB T hT]`.

Rewrite using `[Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec, hx' T hT, Matrix.mulVec_smul]`. Establish `hle : (⨆ χ ∈ S, simEig j 𝒯 χ) ≤ (⨆ χ ∈ S, simEig j 𝒯 χ).comap (B.map j).mulVecLin`. Use `iSup₂_le fun χ hχ => ?_` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[Submodule.mem_comap, Matrix.mulVecLin_apply]`.

Conclude with `(le_iSup₂ (f := fun χ (_ : χ ∈ S) => simEig j 𝒯 χ) χ hχ) (hstab χ x hx)`. Establish `hmem : (fun i => j ((B *ᵥ z) i)) ∈ extSpan j Z`. Establish `e` using `map_mulVec' (j := j) B z`. Rewrite using `[← e, hS]`. Establish `hz' : (fun i => j (z i)) ∈ ⨆ χ ∈ S, simEig j 𝒯 χ`.

Rewrite using `[← hS]`. Conclude with `mem_extSpan hz`. Conclude with `hle hz'`. Establish `h` using `fnl_extSpan Z _ hmem ρ`. Simplify using `only [hρ] at h`.

Conclude with `h`.
-/
theorem full_eigen_commuting : FullEigComm := by
  intro K Ω _ _ j n 𝒯 Z hZ B hB z hz
  obtain ⟨S, hS⟩ := hZ
  obtain ⟨ρ, hρ⟩ := exists_retract j
  have hstab : ∀ χ, ∀ x ∈ simEig j 𝒯 χ, B.map j *ᵥ x ∈ simEig j 𝒯 χ := by
    intro χ x hx
    have hx' : ∀ T ∈ 𝒯, (T.map j).mulVec x = χ T • x := hx
    show ∀ T ∈ 𝒯, (T.map j).mulVec (B.map j *ᵥ x) = χ T • (B.map j *ᵥ x)
    intro T hT
    have hc : T.map j * B.map j = B.map j * T.map j := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, hB T hT]
    rw [Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec, hx' T hT, Matrix.mulVec_smul]
  have hle : (⨆ χ ∈ S, simEig j 𝒯 χ) ≤ (⨆ χ ∈ S, simEig j 𝒯 χ).comap (B.map j).mulVecLin := by
    refine iSup₂_le fun χ hχ => ?_
    intro x hx
    rw [Submodule.mem_comap, Matrix.mulVecLin_apply]
    exact (le_iSup₂ (f := fun χ (_ : χ ∈ S) => simEig j 𝒯 χ) χ hχ) (hstab χ x hx)
  have hmem : (fun i => j ((B *ᵥ z) i)) ∈ extSpan j Z := by
    have e := map_mulVec' (j := j) B z
    rw [← e, hS]
    have hz' : (fun i => j (z i)) ∈ ⨆ χ ∈ S, simEig j 𝒯 χ := by
      rw [← hS]
      exact mem_extSpan hz
    exact hle hz'
  have h := fnl_extSpan Z _ hmem ρ
  simp only [hρ] at h
  exact h

namespace FinitelyNonzeroLinear

/- English proof (translation)
Establish `h0` using `eq_zero_of_fnl j (c - c') fun ρ => by`. Establish `h1` using `ρ.add (c - c') c'`. Rewrite `h1` using `[sub_add_cancel, h ρ]`. Simplify using `using h1`. Conclude with `sub_eq_zero.mp h0`.
-/
theorem eq_of_fnl {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω) (c c' : Ω)
    (h : ∀ ρ : Fnl j, ρ.toFun c = ρ.toFun c') : c = c' := by
  have h0 := eq_zero_of_fnl j (c - c') fun ρ => by
    have h1 := ρ.add (c - c') c'
    rw [sub_add_cancel, h ρ] at h1
    simpa using h1
  exact sub_eq_zero.mp h0

/- English proof (translation)
Use extensionality with `i k`. Use `congrFun (h (Pi.single k 1)) i` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_single_one]`.
-/
theorem ext_mulVec {R : Type} [CommRing R] {m n : ℕ} {A A' : Matrix (Fin m) (Fin n) R}
    (h : ∀ x, A *ᵥ x = A' *ᵥ x) : A = A' := by
  ext i k
  have := congrFun (h (Pi.single k 1)) i
  simpa [Matrix.mulVec_single_one] using this

/- English proof (translation)
Establish `hMρ : ∀ ρ : Fnl j, ∀ T ∈ 𝒯, M.map ρ.toFun * T = T * M.map ρ.toFun` using `fun ρ T hT => by`. Rewrite using `[← fnl_mul_right, ← fnl_mul_left, hM T hT]`. Use extensionality with `a b`. Use `eq_of_fnl j _ _ fun ρ => ?_` and prove the remaining obligations. Establish `key : (e.map j * M).map ρ.toFun = (M * e.map j).map ρ.toFun`.

Rewrite using `[fnl_mul_left, fnl_mul_right, hec _ (hMρ ρ)]`. Use `congrArg (fun X : Matrix (Fin n) (Fin n) K => X a b) key` as an intermediate fact. Conclude with `this`.
-/
theorem comm_ext {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω) {n : ℕ}
    {𝒯 : Set (Matrix (Fin n) (Fin n) K)} {e : Matrix (Fin n) (Fin n) K}
    (hec : ∀ B : Matrix (Fin n) (Fin n) K, (∀ T ∈ 𝒯, B * T = T * B) → e * B = B * e)
    (M : Matrix (Fin n) (Fin n) Ω) (hM : ∀ T ∈ 𝒯, M * T.map j = T.map j * M) :
    e.map j * M = M * e.map j := by
  have hMρ : ∀ ρ : Fnl j, ∀ T ∈ 𝒯, M.map ρ.toFun * T = T * M.map ρ.toFun := fun ρ T hT => by
    rw [← fnl_mul_right, ← fnl_mul_left, hM T hT]
  ext a b
  refine eq_of_fnl j _ _ fun ρ => ?_
  have key : (e.map j * M).map ρ.toFun = (M * e.map j).map ρ.toFun := by
    rw [fnl_mul_left, fnl_mul_right, hec _ (hMρ ρ)]
  have := congrArg (fun X : Matrix (Fin n) (Fin n) K => X a b) key
  exact this

section Herm

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Take `he | he` from `InfinitePlace.embedding_mk_eq σ`. Simplify `hpos (InfinitePlace.mk σ)` using `[he]`. Establish `hP` using `hpos (InfinitePlace.mk σ)`. Rewrite `hP` using `[he]`. Establish `e : H.map σ = (H.map (ComplexEmbedding.conjugate σ))ᵀ`.

Use extensionality with `i k`. Rewrite using `[Matrix.transpose_apply, ← hP.isHermitian.apply k i]`. Simplify using `[ComplexEmbedding.conjugate_coe_eq]`. Rewrite using `[e]`. Conclude with `hP.transpose`.
-/
theorem posDef_all {n : ℕ} {H : Matrix (Fin n) (Fin n) K}
    (hpos : ∀ v : InfinitePlace K, (H.map v.embedding).PosDef) (σ : K →+* ℂ) :
    (H.map σ).PosDef := by
  obtain he | he := InfinitePlace.embedding_mk_eq σ
  · simpa [he] using hpos (InfinitePlace.mk σ)
  · have hP := hpos (InfinitePlace.mk σ)
    rw [he] at hP
    have e : H.map σ = (H.map (ComplexEmbedding.conjugate σ))ᵀ := by
      ext i k
      rw [Matrix.transpose_apply, ← hP.isHermitian.apply k i]
      simp [ComplexEmbedding.conjugate_coe_eq]
    rw [e]
    exact hP.transpose

/- English proof (translation)
Use extensionality with `i k`. Apply `v0.embedding.injective` to reduce the goal to its premises. Rewrite using `[Matrix.conjTranspose_apply, hv0 (H k i), starRingEnd_apply]`. Conclude with `hpos.isHermitian.apply i k`.
-/
theorem herm_of_pos {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {n : ℕ}
    {H : Matrix (Fin n) (Fin n) K} (hpos : (H.map v0.embedding).PosDef) : Hᴴ = H := by
  ext i k
  apply v0.embedding.injective
  rw [Matrix.conjTranspose_apply, hv0 (H k i), starRingEnd_apply]
  exact hpos.isHermitian.apply i k

/- English proof (translation)
Rewrite using `[Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]`. Introduce `h0`. Establish `hp` using `hpos.det_pos`. Establish `e : (H.map σ).det = σ H.det` using `(RingHom.map_det σ H).symm`. Rewrite `hp` using `[e, h0, map_zero]`.

Conclude with `lt_irrefl _ hp`.
-/
theorem isUnit_of_pos {σ : K →+* ℂ} {n : ℕ}
    {H : Matrix (Fin n) (Fin n) K} (hpos : (H.map σ).PosDef) : IsUnit H := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  have hp := hpos.det_pos
  have e : (H.map σ).det = σ H.det := (RingHom.map_det σ H).symm
  rw [e, h0, map_zero] at hp
  exact lt_irrefl _ hp

/- English proof (translation)
Establish `hv0' : ∀ a : K, v0.embedding (star a) = starRingEnd ℂ (v0.embedding a)` using `hv0`. Assume the negation of the conclusion as `hx`. Establish `hx' : (fun i => v0.embedding (x i)) ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Conclude with `v0.embedding.injective (by simpa using congrFun h0 i)`. Establish `hp` using `hpos.dotProduct_mulVec_pos hx'`. Establish `e : star (fun i => v0.embedding (x i)) ⬝ᵥ (H.map v0.embedding) *ᵥ (fun i => v0.embedding (x i)) = v0.embedding (star x ⬝ᵥ H *ᵥ x)`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.star_apply, hv0', Matrix.map_apply, starRingEnd_apply]`.

Rewrite `hp` using `[e, h, map_zero]`. Conclude with `lt_irrefl _ hp`.
-/
theorem aniso {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {n : ℕ}
    {H : Matrix (Fin n) (Fin n) K} (hpos : (H.map v0.embedding).PosDef) (x : Fin n → K)
    (h : star x ⬝ᵥ H *ᵥ x = 0) : x = 0 := by
  have hv0' : ∀ a : K, v0.embedding (star a) = starRingEnd ℂ (v0.embedding a) := hv0
  by_contra hx
  have hx' : (fun i => v0.embedding (x i)) ≠ 0 := by
    intro h0
    apply hx
    funext i
    exact v0.embedding.injective (by simpa using congrFun h0 i)
  have hp := hpos.dotProduct_mulVec_pos hx'
  have e : star (fun i => v0.embedding (x i)) ⬝ᵥ (H.map v0.embedding) *ᵥ
      (fun i => v0.embedding (x i)) = v0.embedding (star x ⬝ᵥ H *ᵥ x) := by
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.star_apply, hv0', Matrix.map_apply,
      starRingEnd_apply]
  rw [e, h, map_zero] at hp
  exact lt_irrefl _ hp

open ConjugateWeightGram in

/- English proof (translation)
Establish `hHh : Hᴴ = H` using `herm_of_pos hv0 hpos`. Take `⟨d, ⟨b⟩⟩ : ∃ d, Nonempty (Basis (Fin d) K Z)` from `⟨_, ⟨Module.finBasis K Z⟩⟩`. Take `⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin d) K, ∀ c, B *ᵥ c = ∑ a, c a • (b a : Fin n → K)` from `⟨Matrix.of fun i a => (b a : Fin n → K) i, fun c => by`. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`.

Conclude with `Finset.sum_congr rfl fun a _ => mul_comm _ _⟩`. Establish `hBZ : ∀ c, B *ᵥ c ∈ Z` using `fun c => by`. Rewrite using `[hB]`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (b a).2`. Establish `hZB : ∀ z ∈ Z, ∃ c, B *ᵥ c = z` using `fun z hz => ⟨b.repr ⟨z, hz⟩, by`.

Rewrite using `[hB]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul]`. Use `_ = z := by rw [b.sum_repr]⟩`. Establish `hli : LinearIndependent K (fun a => (b a : Fin n → K))` using `b.linearIndependent.map' Z.subtype (Submodule.ker_subtype Z)`.

Establish `hinj : ∀ c, B *ᵥ c = 0 → c = 0` using `fun c hc =>`. Use function extensionality and compare the values at `(Fintype.linearIndependent_iff.mp hli c (by rw [← hB]; exact hc))`. Take `⟨G, hG⟩ : ∃ G : Matrix (Fin d) (Fin d) K, G = Bᴴ * H * B` from `⟨_, rfl⟩`. Establish `hquad : ∀ c, star c ⬝ᵥ G *ᵥ c = star (B *ᵥ c) ⬝ᵥ H *ᵥ (B *ᵥ c)` using `fun c => by`. Rewrite using `[hG]`.

Simplify using `only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Establish `hGdet : IsUnit G.det`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Take `⟨c, hc0, hc⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`.

Apply `hc0` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises. Apply `aniso hv0 hpos` to reduce the goal to its premises. Rewrite using `[← hquad, hc]`. Simplify using the standard rewrite rules.

Establish `hGi1 : G⁻¹ * G = 1` using `Matrix.nonsing_inv_mul G hGdet`. Establish `hGh : Gᴴ = G`. Rewrite using `[hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh, Matrix.mul_assoc]`. Establish `hGih : (G⁻¹)ᴴ = G⁻¹` using `by rw [Matrix.conjTranspose_nonsing_inv, hGh]`. Establish `R1 : ∀ X : Matrix (Fin d) (Fin n) K, Bᴴ * (H * (B * X)) = G * X` using `fun X => by`.

Rewrite using `[hG]`. Simplify using `only [Matrix.mul_assoc]`. Establish `R0 : Bᴴ * (H * B) = G` using `by rw [hG, Matrix.mul_assoc]`. Establish `R2 : ∀ X : Matrix (Fin d) (Fin n) K, G⁻¹ * (G * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, hGi1, Matrix.one_mul]`.

Use `⟨B * (G⁻¹ * (Bᴴ * H)), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.mul_assoc, R1, R2]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh, hGih, Matrix.mul_assoc]`. Introduce `x`. Rewrite using `[← Matrix.mulVec_mulVec]`.

Conclude with `hBZ _`. Introduce `z hz`. Take `⟨c, rfl⟩` from `hZB z hz`. Rewrite using `[Matrix.mulVec_mulVec, show B * (G⁻¹ * (Bᴴ * H)) * B = B by simp only [Matrix.mul_assoc, R0, hGi1, Matrix.mul_one]]`.
-/
theorem exists_proj {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {n : ℕ}
    {H : Matrix (Fin n) (Fin n) K} (hpos : (H.map v0.embedding).PosDef)
    (Z : Submodule K (Fin n → K)) :
    ∃ e : Matrix (Fin n) (Fin n) K, e * e = e ∧ eᴴ * H = H * e ∧ (∀ x, e *ᵥ x ∈ Z) ∧
      ∀ z ∈ Z, e *ᵥ z = z := by
  have hHh : Hᴴ = H := herm_of_pos hv0 hpos
  obtain ⟨d, ⟨b⟩⟩ : ∃ d, Nonempty (Basis (Fin d) K Z) := ⟨_, ⟨Module.finBasis K Z⟩⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin d) K,
      ∀ c, B *ᵥ c = ∑ a, c a • (b a : Fin n → K) :=
    ⟨Matrix.of fun i a => (b a : Fin n → K) i, fun c => by
      funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _⟩
  have hBZ : ∀ c, B *ᵥ c ∈ Z := fun c => by
    rw [hB]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (b a).2
  have hZB : ∀ z ∈ Z, ∃ c, B *ᵥ c = z := fun z hz => ⟨b.repr ⟨z, hz⟩, by
    rw [hB]
    calc ∑ a, b.repr ⟨z, hz⟩ a • (b a : Fin n → K)
        = ((∑ a, b.repr ⟨z, hz⟩ a • b a : Z) : Fin n → K) := by
          simp only [Submodule.coe_sum, Submodule.coe_smul]
      _ = z := by rw [b.sum_repr]⟩
  have hli : LinearIndependent K (fun a => (b a : Fin n → K)) :=
    b.linearIndependent.map' Z.subtype (Submodule.ker_subtype Z)
  have hinj : ∀ c, B *ᵥ c = 0 → c = 0 := fun c hc =>
    funext (Fintype.linearIndependent_iff.mp hli c (by rw [← hB]; exact hc))
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin d) (Fin d) K, G = Bᴴ * H * B := ⟨_, rfl⟩
  have hquad : ∀ c, star c ⬝ᵥ G *ᵥ c = star (B *ᵥ c) ⬝ᵥ H *ᵥ (B *ᵥ c) := fun c => by
    rw [hG]
    simp only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  have hGdet : IsUnit G.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hc0
    apply hinj
    apply aniso hv0 hpos
    rw [← hquad, hc]
    simp
  have hGi1 : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hGdet
  have hGh : Gᴴ = G := by
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hHh, Matrix.mul_assoc]
  have hGih : (G⁻¹)ᴴ = G⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hGh]
  have R1 : ∀ X : Matrix (Fin d) (Fin n) K, Bᴴ * (H * (B * X)) = G * X := fun X => by
    rw [hG]
    simp only [Matrix.mul_assoc]
  have R0 : Bᴴ * (H * B) = G := by rw [hG, Matrix.mul_assoc]
  have R2 : ∀ X : Matrix (Fin d) (Fin n) K, G⁻¹ * (G * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hGi1, Matrix.one_mul]
  refine ⟨B * (G⁻¹ * (Bᴴ * H)), ?_, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_assoc, R1, R2]
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh, hGih,
      Matrix.mul_assoc]
  · intro x
    rw [← Matrix.mulVec_mulVec]
    exact hBZ _
  · intro z hz
    obtain ⟨c, rfl⟩ := hZB z hz
    rw [Matrix.mulVec_mulVec,
      show B * (G⁻¹ * (Bᴴ * H)) * B = B by simp only [Matrix.mul_assoc, R0, hGi1, Matrix.mul_one]]

/- English proof (translation)
Simplify using `only [hform, Matrix.toLinearMapₛₗ₂'_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, Pi.star_apply, starRingEnd_apply, RingHom.id_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring`.
-/
private theorem hform_eq_lemma {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    hform H x y = star x ⬝ᵥ H *ᵥ y := by
  simp only [hform, Matrix.toLinearMapₛₗ₂'_apply, Matrix.mulVec, dotProduct, Finset.mul_sum,
    Pi.star_apply, starRingEnd_apply, RingHom.id_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Establish `e : ∀ x y : Fin n → K, star x ⬝ᵥ (Tᴴ * H) *ᵥ y = star x ⬝ᵥ (H * T') *ᵥ y`. Introduce `x y`. Use `h x y` as an intermediate fact. Rewrite `this` using `[hform_eq_lemma, hform_eq_lemma]`. Simplify `this` using `only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]`.

Use extensionality with `a b`. Use `e (Pi.single a 1) (Pi.single b 1)` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_single_one]`.
-/
theorem adj_matrix {n : ℕ} {H T T' : Matrix (Fin n) (Fin n) K}
    (h : ∀ x y : Fin n → K, hform H (T *ᵥ x) y = hform H x (T' *ᵥ y)) : Tᴴ * H = H * T' := by
  have e : ∀ x y : Fin n → K, star x ⬝ᵥ (Tᴴ * H) *ᵥ y = star x ⬝ᵥ (H * T') *ᵥ y := by
    intro x y
    have := h x y
    rw [hform_eq_lemma, hform_eq_lemma] at this
    simpa only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec] using this
  ext a b
  have := e (Pi.single a 1) (Pi.single b 1)
  simpa [Matrix.mulVec_single_one] using this

/- English proof (translation)
Take `⟨Hi, hH1, hH2⟩ : ∃ Hi : Matrix (Fin n) (Fin n) K, H * Hi = 1 ∧ Hi * H = 1` from `⟨↑hHu.unit⁻¹, hHu.mul_val_inv, hHu.val_inv_mul⟩`. Establish `R2 : ∀ X : Matrix (Fin n) (Fin n) K, Hi * (H * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, hH2, Matrix.one_mul]`. Establish `hHiH : Hiᴴ * H = 1`. Rewrite using `[← hHh, ← Matrix.conjTranspose_mul, hH1, Matrix.conjTranspose_one]`.

Establish `hB' : ∀ T ∈ 𝒯, Hi * (Bᴴ * H) * T = T * (Hi * (Bᴴ * H))`. Introduce `T hT`. Take `⟨T', hT', hTT'⟩` from `hadj T hT`. Establish `hHT : H * T = T'ᴴ * H`. Use `congrArg Matrix.conjTranspose hTT'` as an intermediate fact.

Rewrite `this` using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh]`. Conclude with `this`. Establish `hBT' : Bᴴ * T'ᴴ = T'ᴴ * Bᴴ`. Rewrite using `[← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, hB T' hT']`. Establish `hiT : Hi * T'ᴴ = T * Hi`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Establish `hadjB : (Hi * (Bᴴ * H))ᴴ * H = H * B`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh, Matrix.mul_assoc, hHiH, Matrix.mul_one]`. Establish `hproj : ∀ X : Matrix (Fin n) (Fin n) K, (∀ z ∈ Z, X *ᵥ z ∈ Z) → e * X * e = X * e` using `fun X hX => ext_mulVec fun x => by`.

Use `h2 _ (hX _ (h1 x))` as an intermediate fact. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_assoc] at this ⊢`. Conclude with `this`. Establish `hgen : ∀ X : Matrix (Fin n) (Fin n) K, Xᴴ * H = H * B → e * X * e = X * e → e * B * e = e * B`. Introduce `X hX hXe`.

Establish `RheH : ∀ Y : Matrix (Fin n) (Fin n) K, eᴴ * (H * Y) = H * (e * Y)` using `fun Y => by`. Rewrite using `[← Matrix.mul_assoc, heH, Matrix.mul_assoc]`. Establish `RhX : ∀ Y : Matrix (Fin n) (Fin n) K, Xᴴ * (H * Y) = H * (B * Y)` using `fun Y => by`. Rewrite using `[← Matrix.mul_assoc, hX, Matrix.mul_assoc]`. Establish `k1 : (e * X * e)ᴴ * H = H * (e * B * e)`.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc, heH, RheH, RhX]`. Establish `k2 : (X * e)ᴴ * H = H * (e * B)`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc, hX, RheH]`. Establish `k3 : H * (e * B * e) = H * (e * B)` using `by rw [← k1, ← k2, hXe]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hBe` using `hproj B fun z hz => hZ B hB z hz`. Establish `hXe` using `hproj _ fun z hz => hZ _ hB' z hz`. Conclude with `(hgen _ hadjB hXe).symm.trans hBe`.
-/
theorem comm_of_stable {n : ℕ} {H : Matrix (Fin n) (Fin n) K} (hHh : Hᴴ = H) (hHu : IsUnit H)
    {𝒯 : Set (Matrix (Fin n) (Fin n) K)} (hadj : ∀ T ∈ 𝒯, ∃ T' ∈ 𝒯, Tᴴ * H = H * T')
    {Z : Submodule K (Fin n → K)} (hZ : IsCommStable 𝒯 Z) {e : Matrix (Fin n) (Fin n) K}
    (heH : eᴴ * H = H * e) (h1 : ∀ x, e *ᵥ x ∈ Z) (h2 : ∀ z ∈ Z, e *ᵥ z = z)
    (B : Matrix (Fin n) (Fin n) K) (hB : ∀ T ∈ 𝒯, B * T = T * B) : e * B = B * e := by
  obtain ⟨Hi, hH1, hH2⟩ : ∃ Hi : Matrix (Fin n) (Fin n) K, H * Hi = 1 ∧ Hi * H = 1 :=
    ⟨↑hHu.unit⁻¹, hHu.mul_val_inv, hHu.val_inv_mul⟩
  have R2 : ∀ X : Matrix (Fin n) (Fin n) K, Hi * (H * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hH2, Matrix.one_mul]
  have hHiH : Hiᴴ * H = 1 := by
    rw [← hHh, ← Matrix.conjTranspose_mul, hH1, Matrix.conjTranspose_one]
  have hB' : ∀ T ∈ 𝒯, Hi * (Bᴴ * H) * T = T * (Hi * (Bᴴ * H)) := by
    intro T hT
    obtain ⟨T', hT', hTT'⟩ := hadj T hT
    have hHT : H * T = T'ᴴ * H := by
      have := congrArg Matrix.conjTranspose hTT'
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        hHh] at this
      exact this
    have hBT' : Bᴴ * T'ᴴ = T'ᴴ * Bᴴ := by
      rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, hB T' hT']
    have hiT : Hi * T'ᴴ = T * Hi := by
      calc Hi * T'ᴴ = Hi * T'ᴴ * (H * Hi) := by rw [hH1, Matrix.mul_one]
        _ = Hi * (T'ᴴ * H) * Hi := by simp only [Matrix.mul_assoc]
        _ = Hi * (H * T) * Hi := by rw [hHT]
        _ = T * Hi := by rw [← Matrix.mul_assoc Hi H T, hH2, Matrix.one_mul]
    calc Hi * (Bᴴ * H) * T = Hi * (Bᴴ * (H * T)) := by simp only [Matrix.mul_assoc]
      _ = Hi * (Bᴴ * T'ᴴ) * H := by rw [hHT]; simp only [Matrix.mul_assoc]
      _ = Hi * T'ᴴ * (Bᴴ * H) := by rw [hBT']; simp only [Matrix.mul_assoc]
      _ = T * (Hi * (Bᴴ * H)) := by rw [hiT]; simp only [Matrix.mul_assoc]
  have hadjB : (Hi * (Bᴴ * H))ᴴ * H = H * B := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh,
      Matrix.mul_assoc, hHiH, Matrix.mul_one]
  have hproj : ∀ X : Matrix (Fin n) (Fin n) K, (∀ z ∈ Z, X *ᵥ z ∈ Z) → e * X * e = X * e :=
    fun X hX => ext_mulVec fun x => by
      have := h2 _ (hX _ (h1 x))
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc] at this ⊢
      exact this
  have hgen : ∀ X : Matrix (Fin n) (Fin n) K, Xᴴ * H = H * B → e * X * e = X * e →
      e * B * e = e * B := by
    intro X hX hXe
    have RheH : ∀ Y : Matrix (Fin n) (Fin n) K, eᴴ * (H * Y) = H * (e * Y) := fun Y => by
      rw [← Matrix.mul_assoc, heH, Matrix.mul_assoc]
    have RhX : ∀ Y : Matrix (Fin n) (Fin n) K, Xᴴ * (H * Y) = H * (B * Y) := fun Y => by
      rw [← Matrix.mul_assoc, hX, Matrix.mul_assoc]
    have k1 : (e * X * e)ᴴ * H = H * (e * B * e) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, heH, RheH, RhX]
    have k2 : (X * e)ᴴ * H = H * (e * B) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, hX, RheH]
    have k3 : H * (e * B * e) = H * (e * B) := by rw [← k1, ← k2, hXe]
    calc e * B * e = Hi * (H * (e * B * e)) := by rw [R2]
      _ = Hi * (H * (e * B)) := by rw [k3]
      _ = e * B := R2 _
  have hBe := hproj B fun z hz => hZ B hB z hz
  have hXe := hproj _ fun z hz => hZ _ hB' z hz
  exact (hgen _ hadjB hXe).symm.trans hBe

/- English proof (translation)
Use extensionality with `i k`. Simplify using `only [Matrix.map_apply, Matrix.conjTranspose_apply, twist, RingHom.comp_apply, starRingEnd_apply, star_star]`.
-/
theorem map_conjTranspose_twist {m n : ℕ} (σ : K →+* ℂ) (A : Matrix (Fin m) (Fin n) K) :
    (Aᴴ).map σ = (A.map (twist σ))ᴴ := by
  ext i k
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply, twist, RingHom.comp_apply,
    starRingEnd_apply, star_star]

/- English proof (translation)
Use extensionality with `i k`. Simplify using `only [Matrix.map_apply, twist, RingHom.comp_apply, starRingEnd_apply]`. Rewrite using `[hK0 σ _ (hA i k), starRingEnd_apply, star_star]`.
-/
theorem map_twist_of_mem {K0 : Subfield K} (hK0 : IsCMSub K0) (σ : K →+* ℂ) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (hA : ∀ i k, A i k ∈ K0) : A.map (twist σ) = A.map σ := by
  ext i k
  simp only [Matrix.map_apply, twist, RingHom.comp_apply, starRingEnd_apply]
  rw [hK0 σ _ (hA i k), starRingEnd_apply, star_star]

end Herm

end FinitelyNonzeroLinear

open FinitelyNonzeroLinear in
/- English proof (translation)
Introduce `K _ _ _ K0 hK0 v0 hv0 n H hH hpos 𝒯 h𝒯 hcomm hadj Z hZ σ`. Take `⟨e, hee, heH, h1, h2⟩` from `exists_proj hv0 (hpos v0) Z`. Establish `hHh : Hᴴ = H` using `herm_of_pos hv0 (hpos v0)`. Establish `hHu : IsUnit H` using `isUnit_of_pos (hpos v0)`. Establish `hadjK : ∀ T ∈ 𝒯, ∃ T' ∈ 𝒯, Tᴴ * H = H * T'`.

Introduce `T hT`. Take `⟨T', hT', h⟩` from `hadj T hT`. Conclude with `⟨T', hT', adj_matrix h⟩`. Establish `hec` using `comm_of_stable hHh hHu hadjK hZ heH h1 h2`. Establish `hPD` using `posDef_all hpos σ`.

Establish `hMM : e.map (twist σ) * e.map (twist σ) = e.map (twist σ)`. Rewrite using `[← Matrix.map_mul, hee]`. Establish `hMadj : (e.map (twist σ))ᴴ * H.map σ = H.map σ * e.map σ`. Use `congrArg (fun X => X.map σ) heH` as an intermediate fact. Simplify using `only [Matrix.map_mul] at this`.

Rewrite `this` using `[map_conjTranspose_twist]`. Then use the resulting hypothesis. Establish `hMc : ∀ T ∈ 𝒯, e.map (twist σ) * T.map σ = T.map σ * e.map (twist σ)`. Introduce `T hT`. Establish `h3` using `congrArg (fun X => X.map (twist σ)) (hec T fun T' hT' => hcomm T hT T' hT')`. Simplify using `only [Matrix.map_mul] at h3`.

Rewrite `h3` using `[map_twist_of_mem hK0 σ T (h𝒯 T hT)]`. Then use the resulting hypothesis. Establish `hEM : e.map σ * e.map (twist σ) = e.map (twist σ) * e.map σ` using `comm_ext σ hec _ hMc`. Establish `heq` using `normal_idem hPD (e.map (twist σ)) (e.map σ) hMM hMadj hEM`. Use `show extSpan σ Z = extSpan (twist σ) Z`. Rewrite using `[extSpan_eq_range Z e h1 h2, extSpan_eq_range Z e h1 h2, heq]`.
-/
theorem commuting_twist : CommTwist := by
  intro K _ _ _ K0 hK0 v0 hv0 n H hH hpos 𝒯 h𝒯 hcomm hadj Z hZ σ
  obtain ⟨e, hee, heH, h1, h2⟩ := exists_proj hv0 (hpos v0) Z
  have hHh : Hᴴ = H := herm_of_pos hv0 (hpos v0)
  have hHu : IsUnit H := isUnit_of_pos (hpos v0)
  have hadjK : ∀ T ∈ 𝒯, ∃ T' ∈ 𝒯, Tᴴ * H = H * T' := by
    intro T hT
    obtain ⟨T', hT', h⟩ := hadj T hT
    exact ⟨T', hT', adj_matrix h⟩
  have hec := comm_of_stable hHh hHu hadjK hZ heH h1 h2
  have hPD := posDef_all hpos σ
  have hMM : e.map (twist σ) * e.map (twist σ) = e.map (twist σ) := by
    rw [← Matrix.map_mul, hee]
  have hMadj : (e.map (twist σ))ᴴ * H.map σ = H.map σ * e.map σ := by
    have := congrArg (fun X => X.map σ) heH
    simp only [Matrix.map_mul] at this
    rwa [map_conjTranspose_twist] at this
  have hMc : ∀ T ∈ 𝒯, e.map (twist σ) * T.map σ = T.map σ * e.map (twist σ) := by
    intro T hT
    have h3 := congrArg (fun X => X.map (twist σ)) (hec T fun T' hT' => hcomm T hT T' hT')
    simp only [Matrix.map_mul] at h3
    rwa [map_twist_of_mem hK0 σ T (h𝒯 T hT)] at h3
  have hEM : e.map σ * e.map (twist σ) = e.map (twist σ) * e.map σ := comm_ext σ hec _ hMc
  have heq := normal_idem hPD (e.map (twist σ)) (e.map σ) hMM hMadj hEM
  show extSpan σ Z = extSpan (twist σ) Z
  rw [extSpan_eq_range Z e h1 h2, extSpan_eq_range Z e h1 h2, heq]

/- English proof (translation)
Introduce `K _ _ _ K0 hK0 v0 hv0 n H hH hpos 𝒯 h𝒯 hcomm hadj Z Ω _ j hZ σ`. Conclude with `commuting_twist K K0 hK0 v0 hv0 n H hH hpos 𝒯 h𝒯 hcomm hadj Z (full_eigen_commuting K Ω j n 𝒯 Z hZ) σ`.
-/
theorem eigen_twist : EigenTwist := by
  intro K _ _ _ K0 hK0 v0 hv0 n H hH hpos 𝒯 h𝒯 hcomm hadj Z Ω _ j hZ σ
  exact commuting_twist K K0 hK0 v0 hv0 n H hH hpos 𝒯 h𝒯 hcomm hadj Z
    (full_eigen_commuting K Ω j n 𝒯 Z hZ) σ

open ConjugateWeightGram FinitelyNonzeroLinear in
/- English proof (translation)
Introduce `K _ _ _ _ K0 hK0 v0 hv0 n H X hX 𝒯 h𝒯 hcomm hadj Z Ω _ j hZ`. Establish `hpos : ∀ v : InfinitePlace K, (H.map v.embedding).PosDef` using `fun v => by`. Rewrite using `[← (hX.2 v).2]`. Apply `Matrix.PosDef.conjTranspose_mul_self` to reduce the goal to its premises. Rewrite using `[Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_nonsing_inv_iff, Matrix.isUnit_iff_isUnit_det]`.

Conclude with `(hX.2 v).1`. Establish `htw` using `eigen_twist K K0 hK0 v0 hv0 n H hX.1 hpos 𝒯 h𝒯 hcomm hadj Z Ω j hZ`. Take `⟨d, z, hzli, hzspan, hzcm⟩` from `descent_cm_field K n Z htw`. Take `⟨hcmSub, hle, hstar, -⟩` from `cm_maximal_order_spec K`. Establish `hXcm : IsRatHerm (cmMax K) H X` using `⟨fun i k => hle K0 hK0 (hX.1 i k), hX.2⟩`.

Take `⟨XT, hXT, hmaj, hform'⟩` from `restriction_rational_hermitian K (cmMax K) hcmSub hstar n H X hXcm d z hzli hzcm`. Conclude with `⟨d, z, XT, hzli, hzspan, hzcm, hXT, hmaj, hform', fun T hT => ratHermLcv_of covolume_via_basis index_change_formula semilocal_basis_exists K (cmMax K) hcmSub d (gramMat H z) XT hXT T hT⟩`.
-/
theorem eigen_rational_hermitian_covolume : EigenRatHermLcv := by
  intro K _ _ _ _ K0 hK0 v0 hv0 n H X hX 𝒯 h𝒯 hcomm hadj Z Ω _ j hZ
  have hpos : ∀ v : InfinitePlace K, (H.map v.embedding).PosDef := fun v => by
    rw [← (hX.2 v).2]
    apply Matrix.PosDef.conjTranspose_mul_self
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_nonsing_inv_iff,
      Matrix.isUnit_iff_isUnit_det]
    exact (hX.2 v).1
  have htw := eigen_twist K K0 hK0 v0 hv0 n H hX.1 hpos 𝒯 h𝒯 hcomm hadj Z Ω j hZ
  obtain ⟨d, z, hzli, hzspan, hzcm⟩ := descent_cm_field K n Z htw
  obtain ⟨hcmSub, hle, hstar, -⟩ := cm_maximal_order_spec K
  have hXcm : IsRatHerm (cmMax K) H X := ⟨fun i k => hle K0 hK0 (hX.1 i k), hX.2⟩
  obtain ⟨XT, hXT, hmaj, hform'⟩ :=
    restriction_rational_hermitian K (cmMax K) hcmSub hstar n H X hXcm d z hzli hzcm
  exact ⟨d, z, XT, hzli, hzspan, hzcm, hXT, hmaj, hform', fun T hT =>
    ratHermLcv_of covolume_via_basis index_change_formula semilocal_basis_exists K (cmMax K) hcmSub d
      (gramMat H z) XT hXT T hT⟩

namespace FinitelyNonzeroLinear

section Cx

variable {n : ℕ} {Hc : Matrix (Fin n) (Fin n) ℂ}

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Establish `hp` using `hH.dotProduct_mulVec_pos hx`. Rewrite `hp` using `[h]`. Conclude with `lt_irrefl _ hp`.
-/
theorem vec_zero_of_form (hH : Hc.PosDef) (x : Fin n → ℂ) (h : star x ⬝ᵥ Hc *ᵥ x = 0) : x = 0 := by
  by_contra hx
  have hp := hH.dotProduct_mulVec_pos hx
  rw [h] at hp
  exact lt_irrefl _ hp

/- English proof (translation)
Establish `hHh : Hcᴴ = Hc` using `hH.isHermitian`. Use `congrArg Matrix.conjTranspose hadj` as an intermediate fact. Rewrite `this` using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh]`. Conclude with `this.symm`.
-/
theorem adj_symm (hH : Hc.PosDef) {N N' : Matrix (Fin n) (Fin n) ℂ} (hadj : Nᴴ * Hc = Hc * N') :
    N'ᴴ * Hc = Hc * N := by
  have hHh : Hcᴴ = Hc := hH.isHermitian
  have := congrArg Matrix.conjTranspose hadj
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hHh] at this
  exact this.symm

/- English proof (translation)
Apply `vec_zero_of_form hH` to reduce the goal to its premises. Establish `e : star (N *ᵥ y) ⬝ᵥ Hc *ᵥ (N *ᵥ y) = star y ⬝ᵥ (Nᴴ * Hc * N) *ᵥ y`. Simplify using `only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Rewrite using `[e, hadj, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, h]`. Simplify using the standard rewrite rules.
-/
theorem ker_of_adj_mul (hH : Hc.PosDef) {N N' : Matrix (Fin n) (Fin n) ℂ}
    (hadj : Nᴴ * Hc = Hc * N') (y : Fin n → ℂ) (h : (N' * N) *ᵥ y = 0) : N *ᵥ y = 0 := by
  apply vec_zero_of_form hH
  have e : star (N *ᵥ y) ⬝ᵥ Hc *ᵥ (N *ᵥ y) = star y ⬝ᵥ (Nᴴ * Hc * N) *ᵥ y := by
    simp only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  rw [e, hadj, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, h]
  simp

/- English proof (translation)
Establish `hadj'` using `adj_symm hH hadj`. Establish `key : ∀ y, N *ᵥ (N *ᵥ y) = 0 → N *ᵥ y = 0`. Introduce `y hy`. Establish `h1 : N' *ᵥ (N *ᵥ y) = 0` using `ker_of_adj_mul hH hadj' _ (by`. Rewrite using `[hc, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero])`.

Apply `vec_zero_of_form hH` to reduce the goal to its premises. Establish `e : star (N *ᵥ y) ⬝ᵥ Hc *ᵥ (N *ᵥ y) = star y ⬝ᵥ (Nᴴ * Hc * N) *ᵥ y`. Simplify using `only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Rewrite using `[e, hadj, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1]`. Simplify using the standard rewrite rules.

Proceed by induction on `k with`. Consider the case `zero`. Simplify using `at h`. Simplify using `[h]`. Consider the case `succ k ih`.

Break down `k with _ | m` into its components or cases. Simplify using `using h`. Apply `ih` to reduce the goal to its premises. Establish `h3 : N *ᵥ (N *ᵥ ((N ^ m) *ᵥ x)) = 0`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← pow_succ', ← pow_succ']`.

Conclude with `h`. Establish `h4` using `key _ h3`. Rewrite `h4` using `[Matrix.mulVec_mulVec, ← pow_succ']`. Then use the resulting hypothesis.
-/
theorem ker_pow_normal (hH : Hc.PosDef) {N N' : Matrix (Fin n) (Fin n) ℂ}
    (hadj : Nᴴ * Hc = Hc * N') (hc : N * N' = N' * N) (k : ℕ) (x : Fin n → ℂ)
    (h : (N ^ k) *ᵥ x = 0) : N *ᵥ x = 0 := by
  have hadj' := adj_symm hH hadj
  have key : ∀ y, N *ᵥ (N *ᵥ y) = 0 → N *ᵥ y = 0 := by
    intro y hy
    have h1 : N' *ᵥ (N *ᵥ y) = 0 := ker_of_adj_mul hH hadj' _ (by
      rw [hc, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero])
    apply vec_zero_of_form hH
    have e : star (N *ᵥ y) ⬝ᵥ Hc *ᵥ (N *ᵥ y) = star y ⬝ᵥ (Nᴴ * Hc * N) *ᵥ y := by
      simp only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc]
    rw [e, hadj, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1]
    simp
  induction k with
  | zero =>
    simp at h
    simp [h]
  | succ k ih =>
    rcases k with _ | m
    · simpa using h
    · apply ih
      have h3 : N *ᵥ (N *ᵥ ((N ^ m) *ᵥ x)) = 0 := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← pow_succ', ← pow_succ']
        exact h
      have h4 := key _ h3
      rwa [Matrix.mulVec_mulVec, ← pow_succ'] at h4

end Cx

section Diag

variable {K : Type} [Field K] {n : ℕ}

/- English proof (translation)
Set `f : 𝒯 → Module.End ℂ (Fin n → ℂ)` to `fun T => Matrix.toLin' ((T : Matrix (Fin n) (Fin n) K).map σ)`. Establish `hfx : ∀ T x, f T x = ((T : Matrix (Fin n) (Fin n) K).map σ) *ᵥ x` using `fun T x => Matrix.toLin'_apply _ _`. Establish `hcommC : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T.map σ * T'.map σ = T'.map σ * T.map σ` using `fun T hT T' hT' => by rw [← Matrix.map_mul, ← Matrix.map_mul, hcomm T hT T' hT']`. Establish `hfc : ∀ i j, Commute (f i) (f j)` using `fun i j => by show f i * f j = f j * f i`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Use `show f i (f j x) = f j (f i x)`. Simplify using `only [hfx, Matrix.mulVec_mulVec, hcommC i i.2 j j.2]`. Establish `hsc : ∀ (c : ℂ) (y : Fin n → ℂ), (c • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ y = c • y` using `fun c y => by`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.one_apply]`.

Establish `hpowx : ∀ (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (k : ℕ) (x : Fin n → ℂ), ((Matrix.toLin' A - c • 1) ^ k) x = ((A - c • 1) ^ k) *ᵥ x`. Introduce `A c k`. Proceed by induction on `k with`. Consider the case `zero => intro x`. Simplify using the standard rewrite rules.

Consider the case `succ k ih`. Introduce `x`. Establish `hg : ∀ y, (Matrix.toLin' A - c • 1) y = (A - c • 1) *ᵥ y` using `fun y => by`. Simplify using `[Matrix.sub_mulVec, Matrix.toLin'_apply, hsc]`. Rewrite using `[pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← ih]`.

Conclude with `hg _`. Establish `htop` using `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo f (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hfc j i) φ) (fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i))`. Rewrite using `[eq_top_iff, ← htop]`. Use `iSup_le fun χ => ?_` and prove the remaining obligations. Set `χ' : Matrix (Fin n) (Fin n) K → ℂ` to `fun T => if h : T ∈ 𝒯 then χ ⟨T, h⟩ else 0`.

Use `le_trans ?_ (le_iSup _ χ')` and prove the remaining obligations. Introduce `x hx`. Use `show ∀ T ∈ 𝒯, (T.map σ).mulVec x = χ' T • x`. Introduce `T hT`. Establish `hxT : x ∈ (f ⟨T, hT⟩).maxGenEigenspace (χ ⟨T, hT⟩)` using `(Submodule.mem_iInf _).mp hx ⟨T, hT⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k : ℕ, ((f ⟨T, hT⟩ - χ ⟨T, hT⟩ • 1) ^ k) x = 0 := by`. Conclude with `Module.End.mem_genEigenspace_top.mp hxT`. Establish `hk' : ((T.map σ - χ ⟨T, hT⟩ • 1) ^ k) *ᵥ x = 0`. Rewrite using `[← hpowx]`. Conclude with `hk`.

Take `⟨T', hT', hadjT⟩` from `hadj T hT`. Establish `hAB : Commute (T.map σ) (T'.map σ)` using `hcommC T hT T' hT'`. Establish `hcN : Commute (T.map σ - χ ⟨T, hT⟩ • 1) (T'.map σ - starRingEnd ℂ (χ ⟨T, hT⟩) • 1)`. Use `Commute.sub_left (Commute.sub_right hAB ((Commute.one_right _).smul_right _)) ?_` and prove the remaining obligations. Conclude with `Commute.sub_right ((Commute.one_left _).smul_left _) (((Commute.refl (1 : Matrix (Fin n) (Fin n) ℂ)).smul_left _).smul_right _)`.

Establish `hadjN : (T.map σ - χ ⟨T, hT⟩ • 1)ᴴ * Hc = Hc * (T'.map σ - starRingEnd ℂ (χ ⟨T, hT⟩) • 1)`. Simplify using `only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, sub_mul, mul_sub, hadjT, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, starRingEnd_apply]`. Establish `h5` using `ker_pow_normal hH hadjN hcN.eq k x hk'`. Rewrite `h5` using `[Matrix.sub_mulVec, hsc, sub_eq_zero]`. Rewrite using `[show χ' T = χ ⟨T, hT⟩ from dif_pos hT]`.

Conclude with `h5`.
-/
theorem iSup_simEig_top (σ : K →+* ℂ) {Hc : Matrix (Fin n) (Fin n) ℂ} (hH : Hc.PosDef)
    (𝒯 : Set (Matrix (Fin n) (Fin n) K)) (hcomm : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T * T' = T' * T)
    (hadj : ∀ T ∈ 𝒯, ∃ T' ∈ 𝒯, (T.map σ)ᴴ * Hc = Hc * T'.map σ) :
    ⨆ χ : Matrix (Fin n) (Fin n) K → ℂ, simEig σ 𝒯 χ = ⊤ := by
  classical
  let f : 𝒯 → Module.End ℂ (Fin n → ℂ) := fun T =>
    Matrix.toLin' ((T : Matrix (Fin n) (Fin n) K).map σ)
  have hfx : ∀ T x, f T x = ((T : Matrix (Fin n) (Fin n) K).map σ) *ᵥ x := fun T x =>
    Matrix.toLin'_apply _ _
  have hcommC : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T.map σ * T'.map σ = T'.map σ * T.map σ :=
    fun T hT T' hT' => by rw [← Matrix.map_mul, ← Matrix.map_mul, hcomm T hT T' hT']
  have hfc : ∀ i j, Commute (f i) (f j) := fun i j => by
    show f i * f j = f j * f i
    refine LinearMap.ext fun x => ?_
    show f i (f j x) = f j (f i x)
    simp only [hfx, Matrix.mulVec_mulVec, hcommC i i.2 j j.2]
  have hsc : ∀ (c : ℂ) (y : Fin n → ℂ), (c • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ y = c • y :=
    fun c y => by
      funext i
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  have hpowx : ∀ (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (k : ℕ) (x : Fin n → ℂ),
      ((Matrix.toLin' A - c • 1) ^ k) x = ((A - c • 1) ^ k) *ᵥ x := by
    intro A c k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      have hg : ∀ y, (Matrix.toLin' A - c • 1) y = (A - c • 1) *ᵥ y := fun y => by
        simp [Matrix.sub_mulVec, Matrix.toLin'_apply, hsc]
      rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← ih]
      exact hg _
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo f
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hfc j i) φ)
    (fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i))
  rw [eq_top_iff, ← htop]
  refine iSup_le fun χ => ?_
  let χ' : Matrix (Fin n) (Fin n) K → ℂ := fun T => if h : T ∈ 𝒯 then χ ⟨T, h⟩ else 0
  refine le_trans ?_ (le_iSup _ χ')
  intro x hx
  show ∀ T ∈ 𝒯, (T.map σ).mulVec x = χ' T • x
  intro T hT
  have hxT : x ∈ (f ⟨T, hT⟩).maxGenEigenspace (χ ⟨T, hT⟩) :=
    (Submodule.mem_iInf _).mp hx ⟨T, hT⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ((f ⟨T, hT⟩ - χ ⟨T, hT⟩ • 1) ^ k) x = 0 := by
    exact Module.End.mem_genEigenspace_top.mp hxT
  have hk' : ((T.map σ - χ ⟨T, hT⟩ • 1) ^ k) *ᵥ x = 0 := by
    rw [← hpowx]
    exact hk
  obtain ⟨T', hT', hadjT⟩ := hadj T hT
  have hAB : Commute (T.map σ) (T'.map σ) := hcommC T hT T' hT'
  have hcN : Commute (T.map σ - χ ⟨T, hT⟩ • 1) (T'.map σ - starRingEnd ℂ (χ ⟨T, hT⟩) • 1) := by
    refine Commute.sub_left (Commute.sub_right hAB ((Commute.one_right _).smul_right _)) ?_
    exact Commute.sub_right ((Commute.one_left _).smul_left _)
      (((Commute.refl (1 : Matrix (Fin n) (Fin n) ℂ)).smul_left _).smul_right _)
  have hadjN : (T.map σ - χ ⟨T, hT⟩ • 1)ᴴ * Hc =
      Hc * (T'.map σ - starRingEnd ℂ (χ ⟨T, hT⟩) • 1) := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      sub_mul, mul_sub, hadjT, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      starRingEnd_apply]
  have h5 := ker_pow_normal hH hadjN hcN.eq k x hk'
  rw [Matrix.sub_mulVec, hsc, sub_eq_zero] at h5
  rw [show χ' T = χ ⟨T, hT⟩ from dif_pos hT]
  exact h5

end Diag

end FinitelyNonzeroLinear

namespace FinitelyNonzeroLinear

section Dich

variable {n : ℕ} {Hc : Matrix (Fin n) (Fin n) ℂ}

/- English proof (translation)
Simplify using `only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h]`.
-/
theorem form_adj {A A' : Matrix (Fin n) (Fin n) ℂ} (h : Aᴴ * Hc = Hc * A') (u v : Fin n → ℂ) :
    star (A *ᵥ u) ⬝ᵥ Hc *ᵥ v = star u ⬝ᵥ Hc *ᵥ (A' *ᵥ v) := by
  simp only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h]

/- English proof (translation)
Simplify using `[star_smul]`.
-/
theorem form_smul_left (c : ℂ) (u v : Fin n → ℂ) :
    star (c • u) ⬝ᵥ Hc *ᵥ v = starRingEnd ℂ c * (star u ⬝ᵥ Hc *ᵥ v) := by
  simp [star_smul]

/- English proof (translation)
Simplify using `[Matrix.mulVec_smul]`.
-/
theorem form_smul_right (c : ℂ) (u v : Fin n → ℂ) :
    star u ⬝ᵥ Hc *ᵥ (c • v) = c * (star u ⬝ᵥ Hc *ᵥ v) := by
  simp [Matrix.mulVec_smul]

def rankOne (Hc : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i k => y i * (star x ᵥ* Hc) k

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[Matrix.dotProduct_mulVec]`. Simplify using `only [rankOne, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`.
-/
theorem rankOne_mulVec (x y v : Fin n → ℂ) :
    rankOne Hc x y *ᵥ v = (star x ⬝ᵥ Hc *ᵥ v) • y := by
  funext i
  rw [Matrix.dotProduct_mulVec]
  simp only [rankOne, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Distinguish the cases in `hV : ∃ x0 ∈ simEig σ 𝒯 χ, x0 ≠ 0`. Use `swap`. Use `push_neg at hV left`. Introduce `y hy`. Rewrite using `[hV y hy, Matrix.mulVec_zero]`.

Take `⟨x0, hx0, hx00⟩` from `hV`. Establish `hxe : ∀ x ∈ simEig σ 𝒯 χ, ∀ T ∈ 𝒯, (T.map σ) *ᵥ x = χ T • x` using `fun x hx => hx`. Establish `hq : star x0 ⬝ᵥ Hc *ᵥ x0 ≠ 0` using `fun h0 => hx00 (vec_zero_of_form hH x0 h0)`. Establish `hconj : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, (T.map σ)ᴴ * Hc = Hc * T'.map σ → starRingEnd ℂ (χ T') = χ T`. Introduce `T hT T' hT' hTT`.

Establish `hf` using `form_adj hTT x0 x0`. Rewrite `hf` using `[hxe x0 hx0 T hT, hxe x0 hx0 T' hT', form_smul_left, form_smul_right]`. Establish `h5` using `mul_right_cancel₀ hq hf`. Rewrite using `[← h5, starRingEnd_self_apply]`. Establish `hcomm : ∀ y ∈ simEig σ 𝒯 χ, ∀ T ∈ 𝒯, rankOne Hc x0 y * T.map σ = T.map σ * rankOne Hc x0 y`.

Introduce `y hy T hT`. Take `⟨T', hT', hTT⟩` from `hadj T hT`. Establish `hT'T` using `adj_symm hH hTT`. Apply `ext_mulVec` to reduce the goal to its premises. Introduce `v`.

Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, rankOne_mulVec, rankOne_mulVec, Matrix.mulVec_smul, hxe y hy T hT, ← form_adj hT'T, hxe x0 hx0 T' hT', form_smul_left, hconj T hT T' hT' hTT, smul_smul, mul_comm (χ T)]`. Take `⟨c, hcdef⟩ : ∃ c : ℂ, c * (star x0 ⬝ᵥ Hc *ᵥ x0) = star x0 ⬝ᵥ Hc *ᵥ (E *ᵥ x0)` from `⟨_, div_mul_cancel₀ _ hq⟩`. Establish `hEy : ∀ y ∈ simEig σ 𝒯 χ, E *ᵥ y = c • y`. Introduce `y hy`. Establish `h1` using `congrArg (fun M => M *ᵥ x0) (hEc _ (hcomm y hy))`.

Simplify using `only [← Matrix.mulVec_mulVec, rankOne_mulVec, Matrix.mulVec_smul] at h1`. Apply `smul_right_injective (Fin n → ℂ) hq` to reduce the goal to its premises. Use `show (star x0 ⬝ᵥ Hc *ᵥ x0) • (E *ᵥ y) = (star x0 ⬝ᵥ Hc *ᵥ x0) • (c • y)`. Rewrite using `[h1, ← hcdef, smul_smul, mul_comm]`. Establish `h2 : E *ᵥ (E *ᵥ x0) = E *ᵥ x0` using `by rw [Matrix.mulVec_mulVec, hEE]`.

Rewrite `h2` using `[hEy x0 hx0, Matrix.mulVec_smul, hEy x0 hx0, smul_smul]`. Establish `h3 : (c * c - c) • x0 = 0` using `by rw [sub_smul, h2, sub_self]`. Establish `hcc : c * c - c = 0` using `(smul_eq_zero.mp h3).resolve_right hx00`. Establish `h4 : c * (c - 1) = 0` using `by linear_combination hcc`. Break down `mul_eq_zero.mp h4 with h0 | h0` into its components or cases.

Use `right`. Introduce `y hy`. Rewrite using `[hEy y hy, h0, zero_smul]`. Use `left`. Introduce `y hy`.

Rewrite using `[hEy y hy, sub_eq_zero.mp h0, one_smul]`.
-/
theorem dichotomy {K : Type} [Field K] (σ : K →+* ℂ) (hH : Hc.PosDef)
    (𝒯 : Set (Matrix (Fin n) (Fin n) K))
    (hadj : ∀ T ∈ 𝒯, ∃ T' ∈ 𝒯, (T.map σ)ᴴ * Hc = Hc * T'.map σ)
    (E : Matrix (Fin n) (Fin n) ℂ) (hEE : E * E = E)
    (hEc : ∀ M : Matrix (Fin n) (Fin n) ℂ, (∀ T ∈ 𝒯, M * T.map σ = T.map σ * M) → E * M = M * E)
    (χ : Matrix (Fin n) (Fin n) K → ℂ) :
    (∀ y ∈ simEig σ 𝒯 χ, E *ᵥ y = y) ∨ (∀ y ∈ simEig σ 𝒯 χ, E *ᵥ y = 0) := by
  by_cases hV : ∃ x0 ∈ simEig σ 𝒯 χ, x0 ≠ 0
  swap
  · push_neg at hV
    left
    intro y hy
    rw [hV y hy, Matrix.mulVec_zero]
  obtain ⟨x0, hx0, hx00⟩ := hV
  have hxe : ∀ x ∈ simEig σ 𝒯 χ, ∀ T ∈ 𝒯, (T.map σ) *ᵥ x = χ T • x := fun x hx => hx
  have hq : star x0 ⬝ᵥ Hc *ᵥ x0 ≠ 0 := fun h0 => hx00 (vec_zero_of_form hH x0 h0)
  have hconj : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, (T.map σ)ᴴ * Hc = Hc * T'.map σ →
      starRingEnd ℂ (χ T') = χ T := by
    intro T hT T' hT' hTT
    have hf := form_adj hTT x0 x0
    rw [hxe x0 hx0 T hT, hxe x0 hx0 T' hT', form_smul_left, form_smul_right] at hf
    have h5 := mul_right_cancel₀ hq hf
    rw [← h5, starRingEnd_self_apply]
  have hcomm : ∀ y ∈ simEig σ 𝒯 χ, ∀ T ∈ 𝒯,
      rankOne Hc x0 y * T.map σ = T.map σ * rankOne Hc x0 y := by
    intro y hy T hT
    obtain ⟨T', hT', hTT⟩ := hadj T hT
    have hT'T := adj_symm hH hTT
    apply ext_mulVec
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, rankOne_mulVec, rankOne_mulVec,
      Matrix.mulVec_smul, hxe y hy T hT, ← form_adj hT'T, hxe x0 hx0 T' hT', form_smul_left,
      hconj T hT T' hT' hTT, smul_smul, mul_comm (χ T)]
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c * (star x0 ⬝ᵥ Hc *ᵥ x0) = star x0 ⬝ᵥ Hc *ᵥ (E *ᵥ x0) :=
    ⟨_, div_mul_cancel₀ _ hq⟩
  have hEy : ∀ y ∈ simEig σ 𝒯 χ, E *ᵥ y = c • y := by
    intro y hy
    have h1 := congrArg (fun M => M *ᵥ x0) (hEc _ (hcomm y hy))
    simp only [← Matrix.mulVec_mulVec, rankOne_mulVec, Matrix.mulVec_smul] at h1
    apply smul_right_injective (Fin n → ℂ) hq
    show (star x0 ⬝ᵥ Hc *ᵥ x0) • (E *ᵥ y) = (star x0 ⬝ᵥ Hc *ᵥ x0) • (c • y)
    rw [h1, ← hcdef, smul_smul, mul_comm]
  have h2 : E *ᵥ (E *ᵥ x0) = E *ᵥ x0 := by rw [Matrix.mulVec_mulVec, hEE]
  rw [hEy x0 hx0, Matrix.mulVec_smul, hEy x0 hx0, smul_smul] at h2
  have h3 : (c * c - c) • x0 = 0 := by rw [sub_smul, h2, sub_self]
  have hcc : c * c - c = 0 := (smul_eq_zero.mp h3).resolve_right hx00
  have h4 : c * (c - 1) = 0 := by linear_combination hcc
  rcases mul_eq_zero.mp h4 with h0 | h0
  · right
    intro y hy
    rw [hEy y hy, h0, zero_smul]
  · left
    intro y hy
    rw [hEy y hy, sub_eq_zero.mp h0, one_smul]

end Dich

end FinitelyNonzeroLinear

open FinitelyNonzeroLinear in
/- English proof (translation)
Introduce `K _ _ _ K0 hK0 v0 hv0 n H hH hpos 𝒯 h𝒯 hcomm hadj Z hZ σ`. Take `⟨e, hee, heH, h1, h2⟩` from `exists_proj hv0 (hpos v0) Z`. Establish `hHh : Hᴴ = H` using `herm_of_pos hv0 (hpos v0)`. Establish `hHu : IsUnit H` using `isUnit_of_pos (hpos v0)`. Establish `hadjK : ∀ T ∈ 𝒯, ∃ T' ∈ 𝒯, Tᴴ * H = H * T'`.

Introduce `T hT`. Take `⟨T', hT', h⟩` from `hadj T hT`. Conclude with `⟨T', hT', adj_matrix h⟩`. Establish `hec` using `comm_of_stable hHh hHu hadjK hZ heH h1 h2`. Establish `hPD` using `posDef_all hpos σ`.

Establish `hadjC : ∀ T ∈ 𝒯, ∃ T' ∈ 𝒯, (T.map σ)ᴴ * H.map σ = H.map σ * T'.map σ`. Introduce `T hT`. Take `⟨T', hT', h⟩` from `hadjK T hT`. Use `⟨T', hT', ?_⟩` and prove the remaining obligations. Use `congrArg (fun X => X.map σ) h` as an intermediate fact.

Simplify using `only [Matrix.map_mul] at this`. Rewrite `this` using `[map_conjTranspose_twist, map_twist_of_mem hK0 σ T (h𝒯 T hT)]`. Then use the resulting hypothesis. Establish `hEE : e.map σ * e.map σ = e.map σ` using `by rw [← Matrix.map_mul, hee]`. Establish `hEc : ∀ M : Matrix (Fin n) (Fin n) ℂ, (∀ T ∈ 𝒯, M * T.map σ = T.map σ * M) → e.map σ * M = M * e.map σ` using `fun M hM => comm_ext σ hec M hM`. Establish `hdich` using `dichotomy σ hPD 𝒯 hadjC (e.map σ) hEE hEc`.

Use `⟨{χ | ∀ y ∈ simEig σ 𝒯 χ, e.map σ *ᵥ y = y}, ?_⟩` and prove the remaining obligations. Rewrite using `[extSpan_eq_range Z e h1 h2]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨v, rfl⟩`. Establish `hv : v ∈ ⨆ χ, simEig σ 𝒯 χ`.

Rewrite using `[iSup_simEig_top σ hPD 𝒯 hcomm hadjC]`. Conclude with `Submodule.mem_top`. Rewrite using `[Matrix.mulVecLin_apply]`. Proceed by induction on `hv using Submodule.iSup_induction' with`. Consider the case `mem χ y hy`.

Break down `hdich χ with hS | h0` into its components or cases. Rewrite using `[hS y hy]`. Conclude with `(le_iSup₂ (f := fun χ (_ : χ ∈ {χ | ∀ y ∈ simEig σ 𝒯 χ, e.map σ *ᵥ y = y}) => simEig σ 𝒯 χ) χ hS) hy`. Rewrite using `[h0 y hy]`. Conclude with `Submodule.zero_mem _`.

Consider the case `zero`. Rewrite using `[Matrix.mulVec_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`. Rewrite using `[Matrix.mulVec_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Use `iSup₂_le fun χ hχ => ?_` and prove the remaining obligations. Introduce `y hy`. Conclude with `LinearMap.mem_range.2 ⟨y, by rw [Matrix.mulVecLin_apply]; exact hχ y hy⟩`.
-/
theorem commuting_full_eigenspaces : CommFullEig := by
  intro K _ _ _ K0 hK0 v0 hv0 n H hH hpos 𝒯 h𝒯 hcomm hadj Z hZ σ
  obtain ⟨e, hee, heH, h1, h2⟩ := exists_proj hv0 (hpos v0) Z
  have hHh : Hᴴ = H := herm_of_pos hv0 (hpos v0)
  have hHu : IsUnit H := isUnit_of_pos (hpos v0)
  have hadjK : ∀ T ∈ 𝒯, ∃ T' ∈ 𝒯, Tᴴ * H = H * T' := by
    intro T hT
    obtain ⟨T', hT', h⟩ := hadj T hT
    exact ⟨T', hT', adj_matrix h⟩
  have hec := comm_of_stable hHh hHu hadjK hZ heH h1 h2
  have hPD := posDef_all hpos σ
  have hadjC : ∀ T ∈ 𝒯, ∃ T' ∈ 𝒯, (T.map σ)ᴴ * H.map σ = H.map σ * T'.map σ := by
    intro T hT
    obtain ⟨T', hT', h⟩ := hadjK T hT
    refine ⟨T', hT', ?_⟩
    have := congrArg (fun X => X.map σ) h
    simp only [Matrix.map_mul] at this
    rwa [map_conjTranspose_twist, map_twist_of_mem hK0 σ T (h𝒯 T hT)] at this
  have hEE : e.map σ * e.map σ = e.map σ := by rw [← Matrix.map_mul, hee]
  have hEc : ∀ M : Matrix (Fin n) (Fin n) ℂ, (∀ T ∈ 𝒯, M * T.map σ = T.map σ * M) →
      e.map σ * M = M * e.map σ := fun M hM => comm_ext σ hec M hM
  have hdich := dichotomy σ hPD 𝒯 hadjC (e.map σ) hEE hEc
  refine ⟨{χ | ∀ y ∈ simEig σ 𝒯 χ, e.map σ *ᵥ y = y}, ?_⟩
  rw [extSpan_eq_range Z e h1 h2]
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    have hv : v ∈ ⨆ χ, simEig σ 𝒯 χ := by
      rw [iSup_simEig_top σ hPD 𝒯 hcomm hadjC]
      exact Submodule.mem_top
    rw [Matrix.mulVecLin_apply]
    induction hv using Submodule.iSup_induction' with
    | mem χ y hy =>
      rcases hdich χ with hS | h0
      · rw [hS y hy]
        exact (le_iSup₂ (f := fun χ (_ : χ ∈ {χ | ∀ y ∈ simEig σ 𝒯 χ, e.map σ *ᵥ y = y}) =>
          simEig σ 𝒯 χ) χ hS) hy
      · rw [h0 y hy]
        exact Submodule.zero_mem _
    | zero =>
      rw [Matrix.mulVec_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [Matrix.mulVec_add]
      exact Submodule.add_mem _ hx hy
  · refine iSup₂_le fun χ hχ => ?_
    intro y hy
    exact LinearMap.mem_range.2 ⟨y, by rw [Matrix.mulVecLin_apply]; exact hχ y hy⟩

open FinitelyNonzeroLinear in
/- English proof (translation)
Introduce `K _ _ _ K0 hK0 n H hH hpos 𝒯 h𝒯 σ χ x hx hx0 T hT T' hT' hadj`. Establish `hM : Tᴴ * H = H * T'` using `FinitelyNonzeroLinear.adj_matrix hadj`. Establish `hPD` using `FinitelyNonzeroLinear.posDef_all hpos σ`. Establish `hmap : (T.map σ)ᴴ * H.map σ = H.map σ * T'.map σ`. Use `congrArg (fun X => X.map σ) hM` as an intermediate fact.

Simplify using `only [Matrix.map_mul] at this`. Rewrite `this` using `[FinitelyNonzeroLinear.map_conjTranspose_twist, FinitelyNonzeroLinear.map_twist_of_mem hK0 σ T (h𝒯 T hT)]`. Then use the resulting hypothesis. Establish `hxe : ∀ S ∈ 𝒯, (S.map σ).mulVec x = χ S • x` using `hx`. Establish `hf` using `FinitelyNonzeroLinear.form_adj hmap x x`. Rewrite `hf` using `[hxe T hT, hxe T' hT', FinitelyNonzeroLinear.form_smul_left, FinitelyNonzeroLinear.form_smul_right]`.

Establish `hq : star x ⬝ᵥ H.map σ *ᵥ x ≠ 0` using `fun h0 => hx0 (FinitelyNonzeroLinear.vec_zero_of_form hPD x h0)`. Conclude with `(mul_right_cancel₀ hq hf).symm`.
-/
theorem eigen_adjoint_conjugate : EigenAdjConj := by
  intro K _ _ _ K0 hK0 n H hH hpos 𝒯 h𝒯 σ χ x hx hx0 T hT T' hT' hadj
  have hM : Tᴴ * H = H * T' := FinitelyNonzeroLinear.adj_matrix hadj
  have hPD := FinitelyNonzeroLinear.posDef_all hpos σ
  have hmap : (T.map σ)ᴴ * H.map σ = H.map σ * T'.map σ := by
    have := congrArg (fun X => X.map σ) hM
    simp only [Matrix.map_mul] at this
    rwa [FinitelyNonzeroLinear.map_conjTranspose_twist, FinitelyNonzeroLinear.map_twist_of_mem hK0 σ T (h𝒯 T hT)] at this
  have hxe : ∀ S ∈ 𝒯, (S.map σ).mulVec x = χ S • x := hx
  have hf := FinitelyNonzeroLinear.form_adj hmap x x
  rw [hxe T hT, hxe T' hT', FinitelyNonzeroLinear.form_smul_left, FinitelyNonzeroLinear.form_smul_right] at hf
  have hq : star x ⬝ᵥ H.map σ *ᵥ x ≠ 0 := fun h0 => hx0 (FinitelyNonzeroLinear.vec_zero_of_form hPD x h0)
  exact (mul_right_cancel₀ hq hf).symm

end Formalism.DivisionValues
