import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblOpOfConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnlyTrivialPartner
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeFixedAtOfSummands
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsComplAtBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTripleStabilizerFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteCompactArchimedeanMaximal
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftInv GlobalTheory.ThK.LiftSemis

namespace GlobalTheory.DefiniteLevel

open GlobalTheory.ThK.ConeEuler GlobalTheory.ThK.UnifLevel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Take `⟨hr, A, hA⟩` from `h`. Use `⟨by omega, A.submatrix id Sum.swap, ?_⟩` and prove the remaining obligations. Establish `e : (A.submatrix id Sum.swap)ᵀ * -M * (A.submatrix id Sum.swap).map star = -((Aᵀ * M * A.map star).submatrix Sum.swap Sum.swap)`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.submatrix_apply, Finset.sum_neg_distrib]`.

Rewrite using `[e, hA]`. Use extensionality with `i j`. Break down `i with i | i` into its components or cases. Break down `j with j | j` into its components or cases. Simplify using `[Matrix.fromBlocks, Matrix.one_apply]`.

Conclude with `j.elim0`. Conclude with `i.elim0`.
-/
theorem hasSig_neg {n s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M 0 s) : HasSig (-M) s 0 := by
  obtain ⟨hr, A, hA⟩ := h
  refine ⟨by omega, A.submatrix id Sum.swap, ?_⟩
  have e : (A.submatrix id Sum.swap)ᵀ * -M * (A.submatrix id Sum.swap).map star =
      -((Aᵀ * M * A.map star).submatrix Sum.swap Sum.swap) := by
    ext i j; simp [Matrix.mul_apply, Matrix.submatrix_apply, Finset.sum_neg_distrib]
  rw [e, hA]
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [Matrix.fromBlocks, Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hθ`. Establish `hc : IsCartan (-M) (-θ)`. Use `⟨by rw [neg_mul_neg, h1], ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[show (-θ).map star = -θ.map star from by ext; simp]`. Simplify using `only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, h2]`.

Use `h3 x hx` as an intermediate fact. Rewrite using `[Matrix.neg_mulVec, Matrix.neg_mulVec, neg_dotProduct, dotProduct_neg, neg_neg]`. Conclude with `this`. Use `DefiniteCartan.eq_one_of_hasSig (hasSig_neg hM) hc` as an intermediate fact. Rewrite using `[← neg_neg θ, this]`.
-/
theorem eq_neg_one_of_hasSig {n s : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : HasSig M 0 s) (hθ : IsCartan M θ) :
    θ = -1 := by
  obtain ⟨h1, h2, h3⟩ := hθ
  have hc : IsCartan (-M) (-θ) := by
    refine ⟨by rw [neg_mul_neg, h1], ?_, fun x hx => ?_⟩
    · rw [show (-θ).map star = -θ.map star from by ext; simp]
      simp only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, h2]
    · have := h3 x hx
      rw [Matrix.neg_mulVec, Matrix.neg_mulVec, neg_dotProduct, dotProduct_neg, neg_neg]
      exact this
  have := DefiniteCartan.eq_one_of_hasSig (hasSig_neg hM) hc
  rw [← neg_neg θ, this]

noncomputable def finPart {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : UA σ J →* UA σ J :=
  idemU σ J (1 - eInf F) (one_sub_idem eInf_idem)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_finPart {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) :
    mat (finPart J g) = (1 - eInf F) • mat g + (1 - (1 - eInf F)) • 1 := rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `mat (compArch σ J g) * mat (finPart J g) = mat g`. Rewrite using `[mat_compArch, mat_finPart, sub_sub_cancel]`. Establish `h1` using `idem_mul_one_sub (eInf_idem (F := F))`.

Establish `h2` using `one_sub_idem (eInf_idem (F := F))`. Establish `h3` using `eInf_idem (F := F)`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_add, smul_smul, h1, h2, h3, mul_comm (1 - eInf F) (eInf F), zero_smul, add_zero, zero_add]`. Establish `h4 : eInf F • mat g + (1 - eInf F) • mat g = mat g` using `by rw [← add_smul, add_sub_cancel, one_smul]`. Apply the tactic sequence `first | exact h4 | (rw [add_comm]; exact h4)`.
-/
theorem compArch_mul_finPart {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) :
    compArch σ J g * finPart J g = g := by
  apply Subtype.ext; apply Units.ext
  change mat (compArch σ J g) * mat (finPart J g) = mat g
  rw [mat_compArch, mat_finPart, sub_sub_cancel]
  have h1 := idem_mul_one_sub (eInf_idem (F := F))
  have h2 := one_sub_idem (eInf_idem (F := F))
  have h3 := eInf_idem (F := F)
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    smul_add, smul_smul, h1, h2, h3, mul_comm (1 - eInf F) (eInf F), zero_smul, add_zero, zero_add]
  have h4 : eInf F • mat g + (1 - eInf F) • mat g = mat g := by rw [← add_smul, add_sub_cancel, one_smul]
  first | exact h4 | (rw [add_comm]; exact h4)

/- English proof (translation)
Simplify using `only [eInf, realAd, fstA]`. Conclude with `map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm`.
-/
theorem fstA_eInf : fstA F (eInf F) = 1 := by
  simp only [eInf, realAd, fstA]
  exact map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm

/- English proof (translation)
Rewrite using `[mat_finPart]`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, tmap_smul, fstA_eInf, Matrix.one_apply]`.

Conclude with `Algebra.TensorProduct.one_def.symm`. Simplify using `[Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, tmap_smul, fstA_eInf, Matrix.one_apply, h]`.
-/
theorem finPart_inf {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) :
    (mat (finPart J g)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 := by
  rw [mat_finPart]
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, tmap_smul, fstA_eInf, Matrix.one_apply]
    exact Algebra.TensorProduct.one_def.symm
  · simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, tmap_smul, fstA_eInf, Matrix.one_apply, h]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n s X _ hX V _ _ ρ x S hS hK U hU hfix`. Use `⟨U.comap (finPart X.J), hU.preimage (continuous_idemU _ _ _), ?_⟩` and prove the remaining obligations. Establish `hle : Submodule.span ℂ (Set.range fun u : U.comap (finPart X.J) => ρ u x) ≤ S`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨u, rfl⟩`.

Use `show ρ u.1 x ∈ S`. Establish `h1 : ρ (finPart X.J u.1) x = x` using `hfix _ u.2 (finPart_inf _ _)`. Establish `h2 : compArch σ X.J u.1 ∈ KInf σ X B.emb`. Use `⟨compArch_mem u.1, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[eq_neg_one_of_hasSig (hX.sig w) (hX.cartan w)]`.

Conclude with `Commute.neg_one_right _`. Establish `h3 : ρ u.1 x = ρ (compArch σ X.J u.1) x` using `by conv_lhs => rw [← compArch_mul_finPart X.J u.1]`. Rewrite using `[map_mul, Module.End.mul_apply, h1]`. Rewrite using `[h3]`. Conclude with `hK _ h2`.

Conclude with `Submodule.finiteDimensional_of_le hle`.
-/
theorem span_finiteDimensional : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B 0 s →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : UA σ X.J →* Module.End ℂ V) (x : V) (S : Submodule ℂ V), FiniteDimensional ℂ S →
    (∀ k ∈ KInf σ X B.emb, ρ k x ∈ S) → ∀ U : Subgroup (UA σ X.J), IsOpen (U : Set (UA σ X.J)) →
    (∀ k ∈ U, (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 → ρ k x = x) →
    ∃ U' : Subgroup (UA σ X.J), IsOpen (U' : Set (UA σ X.J)) ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun u : U' => ρ u x)) := by
  intro F E _ _ _ _ _ σ B n s X _ hX V _ _ ρ x S hS hK U hU hfix
  refine ⟨U.comap (finPart X.J), hU.preimage (continuous_idemU _ _ _), ?_⟩
  have hle : Submodule.span ℂ (Set.range fun u : U.comap (finPart X.J) => ρ u x) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨u, rfl⟩
    show ρ u.1 x ∈ S
    have h1 : ρ (finPart X.J u.1) x = x := hfix _ u.2 (finPart_inf _ _)
    have h2 : compArch σ X.J u.1 ∈ KInf σ X B.emb := by
      refine ⟨compArch_mem u.1, fun w => ?_⟩
      rw [eq_neg_one_of_hasSig (hX.sig w) (hX.cartan w)]
      exact Commute.neg_one_right _
    have h3 : ρ u.1 x = ρ (compArch σ X.J u.1) x := by
      conv_lhs => rw [← compArch_mul_finPart X.J u.1]
      rw [map_mul, Module.End.mul_apply, h1]
    rw [h3]
    exact hK _ h2
  exact Submodule.finiteDimensional_of_le hle
end GlobalTheory.DefiniteLevel
