import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LocGram
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.CharacterAugmentationSubspaceQuotientActionTop
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsBasisCols
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl

noncomputable section

namespace GlobalTheory.CompanionTheory.IwaDbl

/- English proof (translation)
Establish `hB : ∀ y : Fin (n + n) → Fv F v ⊗[F] E, (∀ i, y i ∈ intLoc F E v) ↔ (blkGL finSumFinEquiv (b, b)).1 *ᵥ y ∈ latLoc F (sumLat finSumFinEquiv L L) v`. Introduce `y`. Rewrite using `[latLoc_sumLat]`. Use `conv_rhs => rw [← pairVec_eta finSumFinEquiv y]`. Rewrite using `[val_blkGL, blkMat_mulVec, pairVec_mem_sumLat, ← hb, ← hb]`.

Prove the components needed by the constructor for the conclusion. Conclude with `fun h => ⟨fun i => h _, fun i => h _⟩`. Introduce and unpack `⟨h, h'⟩ j`. Take `⟨i | i, rfl⟩` from `finSumFinEquiv.surjective j`. Use `exacts [h i, h' i]`.

Establish `hint : ∀ K : Matrix (Fin (n + n)) (Fin (n + n)) (Fv F v ⊗[F] E), (∀ i j, K i j ∈ intLoc F E v) → ∀ z : Fin (n + n) → Fv F v ⊗[F] E, (∀ i, z i ∈ intLoc F E v) → ∀ i, (K *ᵥ z) i ∈ intLoc F E v` using `fun K hK z hz i => by`. Express the relevant statement in the definitionally equal form `∑ j, K i j * z j ∈ _`. Conclude with `sum_mem fun j _ => mul_mem (hK i j) (hz j)`. Use `mem_stabLoc.2 fun y => ?_` and prove the remaining obligations. Generalize the expression as in `blkGL finSumFinEquiv (b, b) = B at hB h1 h2`.

Generalize the expression as in `matHom _ σ Q k = M at h1 h2 ⊢`. Establish `e0 : y = B.1 *ᵥ ((B⁻¹).1 *ᵥ y)`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Establish `e1 : M.1 *ᵥ y = B.1 *ᵥ ((B⁻¹ * M * B).1 *ᵥ ((B⁻¹).1 *ᵥ y))`. Simplify using `only [Matrix.mulVec_mulVec, ← Units.val_mul]`.

Use `congr 2`. Use `group`. Establish `e2 : (B⁻¹).1 *ᵥ y = (B⁻¹ * M⁻¹ * B).1 *ᵥ ((B⁻¹ * M * B).1 *ᵥ ((B⁻¹).1 *ᵥ y))`. Simplify using `only [Matrix.mulVec_mulVec, ← Units.val_mul]`. Use `congr 2`.

Use `group`. Establish `hy : y ∈ latLoc F (sumLat finSumFinEquiv L L) v ↔ ∀ i, ((B⁻¹).1 *ᵥ y) i ∈ intLoc F E v`. Rewrite using `[hB, ← e0]`. Establish `hMy : M.1 *ᵥ y ∈ latLoc F (sumLat finSumFinEquiv L L) v ↔ ∀ i, ((B⁻¹ * M * B).1 *ᵥ ((B⁻¹).1 *ᵥ y)) i ∈ intLoc F E v`. Rewrite using `[hB, ← e1]`.

Rewrite using `[hy, hMy]`. Use `⟨hint _ h1 _, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[e2]`. Conclude with `hint _ h2 _ h`.
-/
theorem mem_KFin_of_frame_integral {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (σ : E →ₐ[F] E) {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} {L : Submodule (𝓞 E) (Fin n → E)}
    {v : HeightOneSpectrum (𝓞 F)} (b : GL (Fin n) (Fv F v ⊗[F] E))
    (hb : ∀ y : Fin n → Fv F v ⊗[F] E, (∀ i, y i ∈ intLoc F E v) ↔ b.1 *ᵥ y ∈ latLoc F L v) (k : GLoc σ Q v)
    (h1 : ∀ i j, ((blkGL finSumFinEquiv (b, b))⁻¹ * matHom _ σ Q k * blkGL finSumFinEquiv (b, b)).1 i j ∈ intLoc F E v)
    (h2 : ∀ i j, ((blkGL finSumFinEquiv (b, b))⁻¹ * (matHom _ σ Q k)⁻¹ * blkGL finSumFinEquiv (b, b)).1 i j ∈ intLoc F E v) :
    k ∈ KFin σ Q L v := by
  have hB : ∀ y : Fin (n + n) → Fv F v ⊗[F] E, (∀ i, y i ∈ intLoc F E v) ↔
      (blkGL finSumFinEquiv (b, b)).1 *ᵥ y ∈ latLoc F (sumLat finSumFinEquiv L L) v := by
    intro y
    rw [latLoc_sumLat]
    conv_rhs => rw [← pairVec_eta finSumFinEquiv y]
    rw [val_blkGL, blkMat_mulVec, pairVec_mem_sumLat, ← hb, ← hb]
    constructor
    · exact fun h => ⟨fun i => h _, fun i => h _⟩
    · rintro ⟨h, h'⟩ j
      obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective j
      exacts [h i, h' i]
  have hint : ∀ K : Matrix (Fin (n + n)) (Fin (n + n)) (Fv F v ⊗[F] E), (∀ i j, K i j ∈ intLoc F E v) →
      ∀ z : Fin (n + n) → Fv F v ⊗[F] E, (∀ i, z i ∈ intLoc F E v) → ∀ i, (K *ᵥ z) i ∈ intLoc F E v :=
    fun K hK z hz i => by
      change ∑ j, K i j * z j ∈ _
      exact sum_mem fun j _ => mul_mem (hK i j) (hz j)
  refine mem_stabLoc.2 fun y => ?_
  generalize blkGL finSumFinEquiv (b, b) = B at hB h1 h2
  generalize matHom _ σ Q k = M at h1 h2 ⊢
  have e0 : y = B.1 *ᵥ ((B⁻¹).1 *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have e1 : M.1 *ᵥ y = B.1 *ᵥ ((B⁻¹ * M * B).1 *ᵥ ((B⁻¹).1 *ᵥ y)) := by
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul]
    congr 2
    group
  have e2 : (B⁻¹).1 *ᵥ y = (B⁻¹ * M⁻¹ * B).1 *ᵥ ((B⁻¹ * M * B).1 *ᵥ ((B⁻¹).1 *ᵥ y)) := by
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul]
    congr 2
    group
  have hy : y ∈ latLoc F (sumLat finSumFinEquiv L L) v ↔ ∀ i, ((B⁻¹).1 *ᵥ y) i ∈ intLoc F E v := by
    rw [hB, ← e0]
  have hMy : M.1 *ᵥ y ∈ latLoc F (sumLat finSumFinEquiv L L) v ↔
      ∀ i, ((B⁻¹ * M * B).1 *ᵥ ((B⁻¹).1 *ᵥ y)) i ∈ intLoc F E v := by
    rw [hB, ← e1]
  rw [hy, hMy]
  refine ⟨hint _ h1 _, fun h => ?_⟩
  rw [e2]
  exact hint _ h2 _ h

end GlobalTheory.CompanionTheory.IwaDbl
