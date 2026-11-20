import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsGlIsometryCompEqOfNondegenerate
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.RatOrbit

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_eq {A : Type} [CommRing A] {n : Type} [Fintype n] (s : A →+* A) (J : Matrix n n A) (a b : n → A) :
    Formalism.UG.hform s J a b = b ⬝ᵥ Jᵀ *ᵥ (⇑s ∘ a) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, transpose_apply, Function.comp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hform_mem {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (s : A →+* A) (J : Matrix n n A)
    (g : GL n A) (hg : g ∈ Formalism.UG.UJ s J) (a b : n → A) :
    Formalism.UG.hform s J ((g : Matrix n n A) *ᵥ a) ((g : Matrix n n A) *ᵥ b) = Formalism.UG.hform s J a b := by
  have h : Formalism.UG.cT s (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  have h1 : ⇑s ∘ ((g : Matrix n n A) *ᵥ a) = ((g : Matrix n n A).map s) *ᵥ (⇑s ∘ a) := by
    funext i
    exact RingHom.map_mulVec s _ _ i
  rw [hform_eq, hform_eq, h1]
  conv_rhs => rw [← h]
  simp only [Formalism.UG.cT, transpose_mul, transpose_transpose, ← mulVec_mulVec]
  rw [mulVec_transpose (g : Matrix n n A), dotProduct_comm b, ← dotProduct_mulVec, dotProduct_comm]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem bc_mem {R A : Type} [CommRing R] [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (p : R →+* A) (s : R →+* R) (t : A →+* A) (hp : ∀ x, p (s x) = t (p x)) (J : Matrix n n R)
    (g : GL n R) (hg : g ∈ Formalism.UG.UJ s J) : Formalism.UG.bc p g ∈ Formalism.UG.UJ t (J.map p) := by
  have h : Formalism.UG.cT s (g : Matrix n n R) * J * (g : Matrix n n R) = J := hg
  show Formalism.UG.cT t ((g : Matrix n n R).map p) * J.map p * (g : Matrix n n R).map p = J.map p
  rw [← GlobalTheory.UnitarySplit.map_cond p s t hp, h]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem inclR_injective (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem smul_ratTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (γ : HA R σ J) (g : GL (Fin M) E)
    (hg : Formalism.UG.bc (inclR (F := F) R) g = (γ : HR R σ J).1) (x : Fin n → Fin M → E) :
    γ • ratTup (F := F) R x = ratTup (F := F) R (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ x a) := by
  funext a i
  show (((γ : HR R σ J).1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ (ratTup (F := F) R x a)) i = _
  rw [← hg]
  exact (RingHom.map_mulVec (inclR (F := F) R) _ _ i).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem rational_sphere_orbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → Function.Injective (ratTup (F := F) (AF F) : (Fin 1 → Fin M → E) → _) ∧ ∀ y : Fin 1 → Fin M → AF F ⊗[F] E, (∃ x' : Fin 1 → Fin M → E, hE σ J (x' 0) (x' 0) = hE σ J (x 0) (x 0) ∧ ratTup (F := F) (AF F) x' = y) ↔ ∃ γ ∈ ratPts (AF F) σ J, γ • ratTup (F := F) (AF F) x = y := by
  intro F E _ _ _ _ _ σ hCM M J hJ x hx
  refine ⟨?_, fun y => ⟨?_, ?_⟩⟩
  · intro a b hab
    funext k i
    exact inclR_injective F E (congrFun (congrFun hab k) i)
  · rintro ⟨x', hx', rfl⟩
    simp only [hE, hform_eq] at hx hx'
    obtain ⟨g, hg, hgx, -⟩ := GlobalTheory.HermWitt.exists_gl_isometry_mulVec_eq (c := (σ : E →+* E))
      (G := Jᵀ) two_ne_zero (sigma_sigma σ hCM) (fun a b => hJ.1 a b) hx'.symm hx
    have hU : g ∈ Formalism.UG.UJ (σ : E →+* E) J :=
      GlobalTheory.UnitarySplit.mem_of_form _ _ _ fun z w => by rw [hform_eq, hform_eq, hg]
    have hH : Formalism.UG.bc (inclR (F := F) (AF F)) g ∈ HR (AF F) σ J :=
      bc_mem (inclR (F := F) (AF F)) (σ : E →+* E) (sigR (AF F) σ) (fun t => by
        simp [inclR, sigR]) J g hU
    refine ⟨(⟨_, hH⟩ : HR (AF F) σ J), ⟨g, hU, rfl⟩, ?_⟩
    refine (smul_ratTup (AF F) σ J (⟨_, hH⟩ : HR (AF F) σ J) g rfl x).trans ?_
    congr 1
    funext a
    obtain rfl : a = 0 := Subsingleton.elim _ _
    exact hgx
  · rintro ⟨γ, ⟨g, hU, hg⟩, rfl⟩
    exact ⟨fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ x a, hform_mem _ J g hU _ _,
      (smul_ratTup (AF F) σ J γ g hg x).symm⟩

end GlobalTheory.RatOrbit
