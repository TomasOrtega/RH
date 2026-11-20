import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

noncomputable section

open Formalism.UG

namespace GlobalTheory.SatakeWeyl.IdxFour

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

def rootMat (σ : L →+* L) (x : L) : Matrix (Fin 4) (Fin 4) L :=
  !![1, x, 0, 0; 0, 1, 0, 0; 0, 0, 1, -σ x; 0, 0, 0, 1]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [P.fSatake_cTJ, Fin.sum_univ_four]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [rootMat, antiJ, Fin.rev, hσ]`.
-/
theorem rootMat_unitary (hσ : ∀ x, σ (σ x) = x) (x : L) :
    cT σ (rootMat σ x) * antiJ L 4 * rootMat σ x = antiJ L 4 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [P.fSatake_cTJ, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp [rootMat, antiJ, Fin.rev, hσ]

omit [Valued L (WithZero (Multiplicative ℤ))] in
/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [rootMat, Matrix.mul_apply, Fin.sum_univ_four, add_comm]`.
-/
theorem rootMat_add (x y : L) : rootMat σ (x + y) = rootMat σ x * rootMat σ y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootMat, Matrix.mul_apply, Fin.sum_univ_four, add_comm]

/- English proof (translation)
Use `choose f hf using fun x : L => exists_mat (rootMat σ x) (rootMat_unitary hσ x)`. Use `⟨MonoidHom.mk' (fun x => f x.toAdd) fun a b => mat_injective ?_, fun x => hf _⟩` and prove the remaining obligations. Rewrite using `[mat_mul, hf, hf, hf, toAdd_mul, rootMat_add]`.
-/
theorem exists_hom (hσ : ∀ x, σ (σ x) = x) :
    ∃ φ : Multiplicative L →* GU σ 4, ∀ x, mat (φ x) = rootMat σ x.toAdd := by
  choose f hf using fun x : L => exists_mat (rootMat σ x) (rootMat_unitary hσ x)
  refine ⟨MonoidHom.mk' (fun x => f x.toAdd) fun a b => mat_injective ?_, fun x => hf _⟩
  rw [mat_mul, hf, hf, hf, toAdd_mul, rootMat_add]

/- English proof (translation)
Establish `h1 : ∀ i j : Fin 4, j.val ≤ i.val → mat g i j = (1 : Matrix (Fin 4) (Fin 4) L) i j` using `hg.1`. Establish `h2 : ∀ i j : Fin 4, (![0, 0, 1, 1] : Fin 4 → ℕ) i ≠ (![0, 0, 1, 1] : Fin 4 → ℕ) j → mat g i j = 0` using `hg.2`. Establish `h3 : cT σ (mat g) * antiJ L 4 * mat g = antiJ L 4` using `g.2`. Establish `h4` using `congrFun (congrFun h3 1) 3`. Rewrite `h4` using `[Matrix.mul_apply]`.

Simplify using `only [P.fSatake_cTJ, Fin.sum_univ_four] at h4`. Establish `e00` using `h1 0 0 (by decide)`. Establish `e11` using `h1 1 1 (by decide)`. Establish `e22` using `h1 2 2 (by decide)`. Establish `e33` using `h1 3 3 (by decide)`.

Establish `e10` using `h1 1 0 (by decide)`. Establish `e32` using `h1 3 2 (by decide)`. Establish `e02` using `h2 0 2 (by decide)`. Establish `e03` using `h2 0 3 (by decide)`. Establish `e12` using `h2 1 2 (by decide)`.

Establish `e13` using `h2 1 3 (by decide)`. Establish `e20` using `h2 2 0 (by decide)`. Establish `e21` using `h2 2 1 (by decide)`. Establish `e30` using `h2 3 0 (by decide)`. Establish `e31` using `h2 3 1 (by decide)`.

Establish `r0 : Fin.rev (0 : Fin 4) = 3` using `rfl`. Establish `r1 : Fin.rev (1 : Fin 4) = 2` using `rfl`. Establish `r2 : Fin.rev (2 : Fin 4) = 1` using `rfl`. Establish `r3 : Fin.rev (3 : Fin 4) = 0` using `rfl`. Rewrite `h4` using `[r0, r1, r2, r3, e03, e13, e11, e33]`.

Establish `e23 : mat g 2 3 = -σ (mat g 0 1)`. Simplify using `[antiJ] at h4`. Conclude with `eq_neg_of_add_eq_zero_left h4`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [rootMat, *]`.
-/
theorem mat_of_mem (hσ : ∀ x, σ (σ x) = x) {g : GU σ 4} (hg : g ∈ rootU σ ![0, 0, 1, 1]) :
    mat g = rootMat σ (mat g 0 1) := by
  have h1 : ∀ i j : Fin 4, j.val ≤ i.val → mat g i j = (1 : Matrix (Fin 4) (Fin 4) L) i j := hg.1
  have h2 : ∀ i j : Fin 4, (![0, 0, 1, 1] : Fin 4 → ℕ) i ≠ (![0, 0, 1, 1] : Fin 4 → ℕ) j → mat g i j = 0 := hg.2
  have h3 : cT σ (mat g) * antiJ L 4 * mat g = antiJ L 4 := g.2
  have h4 := congrFun (congrFun h3 1) 3
  rw [Matrix.mul_apply] at h4
  simp only [P.fSatake_cTJ, Fin.sum_univ_four] at h4
  have e00 := h1 0 0 (by decide)
  have e11 := h1 1 1 (by decide)
  have e22 := h1 2 2 (by decide)
  have e33 := h1 3 3 (by decide)
  have e10 := h1 1 0 (by decide)
  have e32 := h1 3 2 (by decide)
  have e02 := h2 0 2 (by decide)
  have e03 := h2 0 3 (by decide)
  have e12 := h2 1 2 (by decide)
  have e13 := h2 1 3 (by decide)
  have e20 := h2 2 0 (by decide)
  have e21 := h2 2 1 (by decide)
  have e30 := h2 3 0 (by decide)
  have e31 := h2 3 1 (by decide)
  have r0 : Fin.rev (0 : Fin 4) = 3 := rfl
  have r1 : Fin.rev (1 : Fin 4) = 2 := rfl
  have r2 : Fin.rev (2 : Fin 4) = 1 := rfl
  have r3 : Fin.rev (3 : Fin 4) = 0 := rfl
  rw [r0, r1, r2, r3, e03, e13, e11, e33] at h4
  have e23 : mat g 2 3 = -σ (mat g 0 1) := by
    simp [antiJ] at h4
    exact eq_neg_of_add_eq_zero_left h4
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootMat, *]

/- English proof (translation)
Use `⟨fun i j h => ?_, fun i j h => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [hg] fin_cases i <;> fin_cases j <;> simp [rootMat] at h ⊢`. Apply the tactic sequence `rw [hg] fin_cases i <;> fin_cases j <;> simp [rootMat] at h ⊢`.
-/
theorem mem_root {g : GU σ 4} {x : L} (hg : mat g = rootMat σ x) : g ∈ rootU σ ![0, 0, 1, 1] := by
  refine ⟨fun i j h => ?_, fun i j h => ?_⟩
  · rw [hg]
    fin_cases i <;> fin_cases j <;> simp [rootMat] at h ⊢
  · rw [hg]
    fin_cases i <;> fin_cases j <;> simp [rootMat] at h ⊢

/- English proof (translation)
Rewrite using `[mem_KU_iff hv, hg]`. Use `⟨fun h => by simpa [rootMat] using h 0 1, fun h i j => ?_⟩` and prove the remaining obligations. Establish `h' : σ x ∈ intL L` using `by show Valued.v (σ x) ≤ 1`. Rewrite using `[hv]`. Conclude with `h`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [rootMat, h, h', one_mem, zero_mem]`.
-/
theorem mem_K_iff (hv : ∀ x, Valued.v (σ x) = Valued.v x) {g : GU σ 4} {x : L} (hg : mat g = rootMat σ x) :
    g ∈ KU σ 4 ↔ x ∈ intL L := by
  rw [mem_KU_iff hv, hg]
  refine ⟨fun h => by simpa [rootMat] using h 0 1, fun h i j => ?_⟩
  have h' : σ x ∈ intL L := by
    show Valued.v (σ x) ≤ 1
    rw [hv]
    exact h
  fin_cases i <;> fin_cases j <;> simp [rootMat, h, h', one_mem, zero_mem]

/- English proof (translation)
Introduce `L _ _ ϖ σ q hU s₀ hs`. Take `⟨φ, hφ⟩` from `exists_hom hU.1`. Establish `hϖ : ϖ ≠ 0`. Introduce and unpack `rfl`. Use `hU.2.2.2.1` as an intermediate fact.

Simplify using `at this`. Establish `hinj : Function.Injective φ` using `fun a b h => by`. Use `congrFun (congrFun ((hφ a).symm.trans ((congrArg mat h).trans (hφ b))) 0) 1` as an intermediate fact. Simplify `this` using `[rootMat]`. Establish `hK : KU σ 4 ⊓ rootU σ ![0, 0, 1, 1] = (AddSubgroup.toSubgroup (intL L).toAddSubgroup).map φ`.

Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Establish `e` using `mat_of_mem hU.1 h2`. Conclude with `⟨Multiplicative.ofAdd (mat g 0 1), (mem_K_iff hU.2.1 e).1 h1, mat_injective ((hφ _).trans e.symm)⟩`.

Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨(mem_K_iff hU.2.1 (hφ x)).2 hx, mem_root (hφ x)⟩`. Establish `hc : ∀ x : L, s₀ * φ (Multiplicative.ofAdd x) * s₀⁻¹ = φ (Multiplicative.ofAdd (ϖ * x))`. Introduce `x`. Rewrite using `[mul_inv_eq_iff_eq_mul]`.

Apply `mat_injective` to reduce the goal to its premises. Rewrite using `[mat_mul, mat_mul, hφ, hφ, hs]`. Use extensionality with `i j`. Rewrite using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [rootMat, hU.2.2.1]`.

Clear the denominators using the available nonvanishing facts. Establish `hK' : ((AddSubgroup.toSubgroup (intL L).toAddSubgroup).map φ).map (MulAut.conj s₀).toMonoidHom = (AddSubgroup.toSubgroup ((intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ))).map φ`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, rfl⟩`.

Conclude with `⟨Multiplicative.ofAdd (ϖ * x.toAdd), ⟨x.toAdd, hx, rfl⟩, (hc x.toAdd).symm⟩`. Introduce and unpack `⟨y, ⟨x, hx, e⟩, rfl⟩`. Use `⟨φ (Multiplicative.ofAdd x), ⟨_, hx, rfl⟩, (hc x).trans (congrArg φ ?_)⟩` and prove the remaining obligations. Conclude with `congrArg Multiplicative.ofAdd e`. Rewrite using `[hK, hK', Subgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_toSubgroup]`.

Conclude with `hI L ϖ σ q hU`.
-/
theorem indexFour (hI : IntIndex) : IndexFour := by
  intro L _ _ ϖ σ q hU s₀ hs
  obtain ⟨φ, hφ⟩ := exists_hom hU.1
  have hϖ : ϖ ≠ 0 := by
    rintro rfl
    have := hU.2.2.2.1
    simp at this
  have hinj : Function.Injective φ := fun a b h => by
    have := congrFun (congrFun ((hφ a).symm.trans ((congrArg mat h).trans (hφ b))) 0) 1
    simpa [rootMat] using this
  have hK : KU σ 4 ⊓ rootU σ ![0, 0, 1, 1] = (AddSubgroup.toSubgroup (intL L).toAddSubgroup).map φ := by
    ext g
    constructor
    · rintro ⟨h1, h2⟩
      have e := mat_of_mem hU.1 h2
      exact ⟨Multiplicative.ofAdd (mat g 0 1), (mem_K_iff hU.2.1 e).1 h1, mat_injective ((hφ _).trans e.symm)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(mem_K_iff hU.2.1 (hφ x)).2 hx, mem_root (hφ x)⟩
  have hc : ∀ x : L, s₀ * φ (Multiplicative.ofAdd x) * s₀⁻¹ = φ (Multiplicative.ofAdd (ϖ * x)) := by
    intro x
    rw [mul_inv_eq_iff_eq_mul]
    apply mat_injective
    rw [mat_mul, mat_mul, hφ, hφ, hs]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    fin_cases i <;> fin_cases j <;> simp [rootMat, hU.2.2.1]
    field_simp
  have hK' : ((AddSubgroup.toSubgroup (intL L).toAddSubgroup).map φ).map (MulAut.conj s₀).toMonoidHom =
      (AddSubgroup.toSubgroup ((intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ))).map φ := by
    ext g
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨Multiplicative.ofAdd (ϖ * x.toAdd), ⟨x.toAdd, hx, rfl⟩, (hc x.toAdd).symm⟩
    · rintro ⟨y, ⟨x, hx, e⟩, rfl⟩
      refine ⟨φ (Multiplicative.ofAdd x), ⟨_, hx, rfl⟩, (hc x).trans (congrArg φ ?_)⟩
      exact congrArg Multiplicative.ofAdd e
  rw [hK, hK', Subgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_toSubgroup]
  exact hI L ϖ σ q hU

end GlobalTheory.SatakeWeyl.IdxFour

end
