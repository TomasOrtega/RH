import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.MatrixLeftInverseLift

/- English proof (translation)
Introduce `F E _ _ _ _ _ d v π₁ π₂ hinj hsurj K hK N₁ N₂ h₁ h₂`. Use `choose Z hZA hZ₁ hZ₂ using fun i j => hsurj ((N₁ - 1) i j) ((N₂ - 1) i j)`. Set `Zm : Matrix (Fin d) (Fin d) (AE F E)` to `Matrix.of Z`. Establish `hZm : ∀ u, evFin F v u = 0 → u • Zm = 0`. Introduce `u hu`.

Use extensionality with `i j`. Simplify `hZA i j u hu` using `[Zm]`. Establish `hmap : ∀ (π : AE F E →+* Fv F v) (N : Matrix (Fin d) (Fin d) (Fv F v)), (∀ i j, π (Z i j) = (N - 1) i j) → (Zm + 1).map π = N`. Introduce `π N hπ`. Use extensionality with `i j`.

Establish `h` using `hπ i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[Zm, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, h]`. Simplify using `[Zm, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, hij, h]`.

Establish `hM₁` using `hmap π₁ N₁ hZ₁`. Establish `hM₂` using `hmap π₂ N₂ hZ₂`. Use `⟨Zm + 1, ?_, hM₁, hM₂⟩` and prove the remaining obligations. Establish `hdecomp : (Zm + 1) * K - 1 = Zm * (K - 1) + Zm + (K - 1)`. Rewrite using `[Matrix.mul_sub, Matrix.mul_one, add_mul, one_mul]`.

Normalize the expressions using the abelian group laws. Establish `hAt : ∀ u, evFin F v u = 0 → u • ((Zm + 1) * K - 1) = 0`. Introduce `u hu`. Rewrite using `[hdecomp, smul_add, smul_add, ← Matrix.mul_smul, hK u hu, hZm u hu]`. Simplify using the standard rewrite rules.

Establish `hπ : ∀ (π : AE F E →+* Fv F v) (N : Matrix (Fin d) (Fin d) (Fv F v)), (Zm + 1).map π = N → N * K.map π = 1 → ((Zm + 1) * K - 1).map π = 0`. Introduce `π N hM hN`. Establish `: π.mapMatrix ((Zm + 1) * K - 1) = π.mapMatrix (Zm + 1) * π.mapMatrix K - 1`. Rewrite using `[map_sub, map_mul, map_one]`. Express the relevant statement in the definitionally equal form `π.mapMatrix ((Zm + 1) * K - 1) = 0`.

Rewrite using `[this]`. Express the relevant statement in the definitionally equal form `(Zm + 1).map π * K.map π - 1 = 0`. Rewrite using `[hM, hN, sub_self]`. Establish `e₁` using `hπ π₁ N₁ hM₁ h₁`. Establish `e₂` using `hπ π₂ N₂ hM₂ h₂`.

Rewrite using `[← sub_eq_zero]`. Use extensionality with `i j`. Apply `hinj` to reduce the goal to its premises. Introduce `u hu`. Use `congrArg (fun m => m i j) (hAt u hu)` as an intermediate fact.

Simplify using `using this`. Simplify using `using congrArg (fun m => m i j) e₁`. Simplify using `using congrArg (fun m => m i j) e₂`.
-/
theorem matrix_left_inverse_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl F) (π₁ π₂ : AE F E →+* Fv F v), (∀ z : AE F E, At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) → (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) →
  ∀ K : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) (K - 1) →
  ∀ N₁ N₂ : Matrix (Fin d) (Fin d) (Fv F v), N₁ * K.map π₁ = 1 → N₂ * K.map π₂ = 1 →
  ∃ M : Matrix (Fin d) (Fin d) (AE F E), M * K = 1 ∧ M.map π₁ = N₁ ∧ M.map π₂ = N₂ := by
  intro F E _ _ _ _ _ d v π₁ π₂ hinj hsurj K hK N₁ N₂ h₁ h₂
  choose Z hZA hZ₁ hZ₂ using fun i j => hsurj ((N₁ - 1) i j) ((N₂ - 1) i j)
  let Zm : Matrix (Fin d) (Fin d) (AE F E) := Matrix.of Z
  have hZm : ∀ u, evFin F v u = 0 → u • Zm = 0 := by
    intro u hu; ext i j; simpa [Zm] using hZA i j u hu
  have hmap : ∀ (π : AE F E →+* Fv F v) (N : Matrix (Fin d) (Fin d) (Fv F v)),
      (∀ i j, π (Z i j) = (N - 1) i j) → (Zm + 1).map π = N := by
    intro π N hπ
    ext i j
    have h := hπ i j
    by_cases hij : i = j
    · subst hij; simp [Zm, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, h]
    · simp [Zm, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, hij, h]
  have hM₁ := hmap π₁ N₁ hZ₁
  have hM₂ := hmap π₂ N₂ hZ₂
  refine ⟨Zm + 1, ?_, hM₁, hM₂⟩
  have hdecomp : (Zm + 1) * K - 1 = Zm * (K - 1) + Zm + (K - 1) := by
    rw [Matrix.mul_sub, Matrix.mul_one, add_mul, one_mul]; abel
  have hAt : ∀ u, evFin F v u = 0 → u • ((Zm + 1) * K - 1) = 0 := by
    intro u hu
    rw [hdecomp, smul_add, smul_add, ← Matrix.mul_smul, hK u hu, hZm u hu]; simp
  have hπ : ∀ (π : AE F E →+* Fv F v) (N : Matrix (Fin d) (Fin d) (Fv F v)),
      (Zm + 1).map π = N → N * K.map π = 1 → ((Zm + 1) * K - 1).map π = 0 := by
    intro π N hM hN
    have : π.mapMatrix ((Zm + 1) * K - 1) = π.mapMatrix (Zm + 1) * π.mapMatrix K - 1 := by
      rw [map_sub, map_mul, map_one]
    change π.mapMatrix ((Zm + 1) * K - 1) = 0
    rw [this]; change (Zm + 1).map π * K.map π - 1 = 0
    rw [hM, hN, sub_self]
  have e₁ := hπ π₁ N₁ hM₁ h₁
  have e₂ := hπ π₂ N₂ hM₂ h₂
  rw [← sub_eq_zero]
  ext i j
  apply hinj
  · intro u hu
    have := congrArg (fun m => m i j) (hAt u hu)
    simpa using this
  · simpa using congrArg (fun m => m i j) e₁
  · simpa using congrArg (fun m => m i j) e₂

end GlobalTheory.MatrixLeftInverseLift
