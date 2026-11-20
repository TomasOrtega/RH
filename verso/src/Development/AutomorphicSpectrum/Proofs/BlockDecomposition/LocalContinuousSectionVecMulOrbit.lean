import Mathlib

open Matrix
open scoped Topology

namespace GlobalTheory.CompanionTheory.OrbitSection

section Shear

variable {k : Type} [Field k] {n : ℕ}

noncomputable def shear (j : Fin n) (c : k) (ζ ξ : Fin n → k) : Matrix (Fin n) (Fin n) k :=
  1 + c • vecMulVec (Pi.single j 1) (ξ - ζ)

/- English proof (translation)
Establish `hE : vecMulVec (Pi.single j (1 : k)) (ξ - ζ) * vecMulVec (Pi.single j 1) (ξ - ζ) = (ξ j - ζ j) • vecMulVec (Pi.single j (1 : k)) (ξ - ζ)`. Rewrite using `[vecMulVec_mul_vecMulVec, vecMulVec_smul]`. Simplify using the standard rewrite rules. Establish `hc : (ζ j)⁻¹ + -(ξ j)⁻¹ + (ζ j)⁻¹ * -(ξ j)⁻¹ * (ξ j - ζ j) = 0`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ E : Matrix (Fin n) (Fin n) k, E * E = (ξ j - ζ j) • E → (1 + (ζ j)⁻¹ • E) * (1 + (-(ξ j)⁻¹) • E) = 1`. Introduce `E hEE`. Establish `: (1 + (ζ j)⁻¹ • E) * (1 + (-(ξ j)⁻¹) • E) = 1 + ((ζ j)⁻¹ + -(ξ j)⁻¹ + (ζ j)⁻¹ * -(ξ j)⁻¹ * (ξ j - ζ j)) • E`. Simplify using `only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hEE]`.

Use `module`. Rewrite using `[this, hc, zero_smul, add_zero]`. Conclude with `key _ hE`.
-/
theorem shear_mul_shear (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) (h1 : ξ j ≠ 0) :
    shear j (ζ j)⁻¹ ζ ξ * shear j (-(ξ j)⁻¹) ζ ξ = 1 := by
  have hE : vecMulVec (Pi.single j (1 : k)) (ξ - ζ) * vecMulVec (Pi.single j 1) (ξ - ζ)
      = (ξ j - ζ j) • vecMulVec (Pi.single j (1 : k)) (ξ - ζ) := by
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
    simp
  have hc : (ζ j)⁻¹ + -(ξ j)⁻¹ + (ζ j)⁻¹ * -(ξ j)⁻¹ * (ξ j - ζ j) = 0 := by
    field_simp
    ring
  have key : ∀ E : Matrix (Fin n) (Fin n) k, E * E = (ξ j - ζ j) • E →
      (1 + (ζ j)⁻¹ • E) * (1 + (-(ξ j)⁻¹) • E) = 1 := by
    intro E hEE
    have : (1 + (ζ j)⁻¹ • E) * (1 + (-(ξ j)⁻¹) • E)
        = 1 + ((ζ j)⁻¹ + -(ξ j)⁻¹ + (ζ j)⁻¹ * -(ξ j)⁻¹ * (ξ j - ζ j)) • E := by
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hEE]
      module
    rw [this, hc, zero_smul, add_zero]
  exact key _ hE

/- English proof (translation)
Establish `: ζ ᵥ* vecMulVec (Pi.single j (1 : k)) (ξ - ζ) = (ζ j) • (ξ - ζ)`. Rewrite using `[vecMul_vecMulVec]`. Simplify using the standard rewrite rules. Rewrite using `[shear, vecMul_add, vecMul_one, vecMul_smul, this, smul_smul, inv_mul_cancel₀ h0, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem vecMul_shear (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) :
    ζ ᵥ* shear j (ζ j)⁻¹ ζ ξ = ξ := by
  have : ζ ᵥ* vecMulVec (Pi.single j (1 : k)) (ξ - ζ) = (ζ j) • (ξ - ζ) := by
    rw [vecMul_vecMulVec]
    simp
  rw [shear, vecMul_add, vecMul_one, vecMul_smul, this, smul_smul, inv_mul_cancel₀ h0, one_smul]
  abel

/- English proof (translation)
Simplify using `[shear]`.
-/
theorem shear_self (j : Fin n) (c : k) (ζ : Fin n → k) : shear j c ζ ζ = 1 := by
  simp [shear]

open Classical in

noncomputable def orbitSection (j : Fin n) (ζ ξ : Fin n → k) : GL (Fin n) k :=
  if h : ζ j ≠ 0 ∧ ξ j ≠ 0 then
    ⟨shear j (ζ j)⁻¹ ζ ξ, shear j (-(ξ j)⁻¹) ζ ξ, shear_mul_shear j ζ ξ h.1 h.2,
      mul_eq_one_comm.mp (shear_mul_shear j ζ ξ h.1 h.2)⟩
  else 1

/- English proof (translation)
Rewrite using `[orbitSection, dif_pos ⟨h0, h1⟩]`.
-/
theorem coe_orbitSection (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) (h1 : ξ j ≠ 0) :
    (orbitSection j ζ ξ : Matrix (Fin n) (Fin n) k) = shear j (ζ j)⁻¹ ζ ξ := by
  rw [orbitSection, dif_pos ⟨h0, h1⟩]

/- English proof (translation)
Rewrite using `[orbitSection, dif_pos ⟨h0, h1⟩]`. Both sides reduce to the same expression.
-/
theorem coe_orbitSection_inv (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) (h1 : ξ j ≠ 0) :
    ((orbitSection j ζ ξ)⁻¹ : (Matrix (Fin n) (Fin n) k)ˣ).val = shear j (-(ξ j)⁻¹) ζ ξ := by
  rw [orbitSection, dif_pos ⟨h0, h1⟩]
  rfl

end Shear

section Top

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k] {n : ℕ}

/- English proof (translation)
Use `continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_` and prove the remaining obligations. Simplify using `only [shear, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.sub_apply, smul_eq_mul]`. Use `continuousOn_const.add (hc.mul (continuousOn_const.mul ?_))` and prove the remaining obligations. Conclude with `((continuous_apply b).sub continuous_const).continuousOn`.
-/
theorem continuousOn_shear (j : Fin n) (ζ : Fin n → k) {N : Set (Fin n → k)} {c : (Fin n → k) → k}
    (hc : ContinuousOn c N) : ContinuousOn (fun ξ => shear j (c ξ) ζ ξ) N := by
  refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_
  simp only [shear, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.sub_apply, smul_eq_mul]
  refine continuousOn_const.add (hc.mul (continuousOn_const.mul ?_))
  exact ((continuous_apply b).sub continuous_const).continuousOn

/- English proof (translation)
Establish `hinv : ContinuousOn (fun ξ : Fin n → k => -(ξ j)⁻¹) {ξ | ξ j ≠ 0}` using `(((continuous_apply j).continuousOn).inv₀ fun ξ h => h).neg`. Rewrite using `[continuousOn_iff_continuous_restrict, Units.continuous_iff]`. Use `⟨(continuousOn_iff_continuous_restrict.1 (continuousOn_shear j ζ (c := fun _ => (ζ j)⁻¹) continuousOn_const)).congr fun ξ => ?_, (continuousOn_iff_continuous_restrict.1 (continuousOn_shear j ζ hinv)).congr fun ξ => ?_⟩` and prove the remaining obligations. Conclude with `(coe_orbitSection j ζ ξ.1 h0 ξ.2).symm`. Conclude with `(coe_orbitSection_inv j ζ ξ.1 h0 ξ.2).symm`.
-/
theorem continuousOn_orbitSection (j : Fin n) (ζ : Fin n → k) (h0 : ζ j ≠ 0) :
    ContinuousOn (orbitSection j ζ) {ξ | ξ j ≠ 0} := by
  have hinv : ContinuousOn (fun ξ : Fin n → k => -(ξ j)⁻¹) {ξ | ξ j ≠ 0} :=
    (((continuous_apply j).continuousOn).inv₀ fun ξ h => h).neg
  rw [continuousOn_iff_continuous_restrict, Units.continuous_iff]
  refine ⟨(continuousOn_iff_continuous_restrict.1
      (continuousOn_shear j ζ (c := fun _ => (ζ j)⁻¹) continuousOn_const)).congr fun ξ => ?_,
    (continuousOn_iff_continuous_restrict.1 (continuousOn_shear j ζ hinv)).congr fun ξ => ?_⟩
  · exact (coe_orbitSection j ζ ξ.1 h0 ξ.2).symm
  · exact (coe_orbitSection_inv j ζ ξ.1 h0 ξ.2).symm

end Top

/- English proof (translation)
Introduce `k _ _ _ _ n ζ hζ`. Use `haveI : T2Space k := by`. Use `letI := IsTopologicalAddGroup.rightUniformSpace k`. Use `haveI := isUniformAddGroup_of_addCommGroup (G := k)`. Use `infer_instance`.

Take `⟨j, hj⟩` from `Function.ne_iff.mp hζ`. Establish `hj' : ζ j ≠ 0` using `hj`. Use `⟨{ξ | ξ j ≠ 0}, isOpen_ne.preimage (continuous_apply j), hj', orbitSection j ζ, continuousOn_orbitSection j ζ hj', ?_, fun ξ hξ => ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[coe_orbitSection j ζ ζ hj' hj', shear_self]`.

Both sides reduce to the same expression. Rewrite using `[coe_orbitSection j ζ ξ hj' hξ, vecMul_shear j ζ ξ hj']`.
-/
theorem exists_local_section : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ζ : Fin n → k), ζ ≠ 0 → ∃ N : Set (Fin n → k), IsOpen N ∧ ζ ∈ N ∧ ∃ f : (Fin n → k) → GL (Fin n) k, ContinuousOn f N ∧ f ζ = 1 ∧ ∀ ξ ∈ N, ζ ᵥ* (f ξ : Matrix (Fin n) (Fin n) k) = ξ := by
  intro k _ _ _ _ n ζ hζ
  haveI : T2Space k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hζ
  have hj' : ζ j ≠ 0 := hj
  refine ⟨{ξ | ξ j ≠ 0}, isOpen_ne.preimage (continuous_apply j), hj', orbitSection j ζ,
    continuousOn_orbitSection j ζ hj', ?_, fun ξ hξ => ?_⟩
  · apply Units.ext
    rw [coe_orbitSection j ζ ζ hj' hj', shear_self]
    rfl
  · rw [coe_orbitSection j ζ ξ hj' hξ, vecMul_shear j ζ ξ hj']

end GlobalTheory.CompanionTheory.OrbitSection
