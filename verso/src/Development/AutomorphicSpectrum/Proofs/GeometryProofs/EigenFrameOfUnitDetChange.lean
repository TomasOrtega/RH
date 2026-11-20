import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEig
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsActionStatement

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

namespace GlobalTheory.CompanionTheory.Ar.FrameUnit

/- English proof (translation)
Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem sum_smul_comb {R U : Type} [CommRing R] [AddCommGroup U] [Module R U] {n : ℕ}
    (C : Matrix (Fin n) (Fin n) R) (b : Fin n → U) (a : Fin n → R) :
    ∑ i, a i • ∑ k, C i k • b k = ∑ k, (Matrix.vecMul a C) k • b k := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.vecMul, dotProduct, Finset.sum_smul]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem comb_basis {R U : Type} [CommRing R] [AddCommGroup U] [Module R U] {n : ℕ}
    (C : Matrix (Fin n) (Fin n) R) (hC : IsUnit C.det) (b : Fin n → U) (hb : LinearIndependent R b) :
    LinearIndependent R (fun i => ∑ k, C i k • b k) ∧
      Submodule.span R (Set.range fun i => ∑ k, C i k • b k) = Submodule.span R (Set.range b) := by
  have hDC : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul C hC
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [sum_smul_comb] at hg
    have h0 : Matrix.vecMul g C = 0 := by
      funext k
      exact (Fintype.linearIndependent_iff.1 hb) _ hg k
    have h1 : g = Matrix.vecMul (Matrix.vecMul g C) C⁻¹ := by
      rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv C hC, Matrix.vecMul_one]
    rw [h1, h0, Matrix.zero_vecMul]
    rfl
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have h : b j = ∑ i, (C⁻¹ j i) • ∑ k, C i k • b k := by
      rw [sum_smul_comb]
      have : Matrix.vecMul (C⁻¹ j) C = Pi.single j 1 := by
        have := congrFun (congrArg (fun A : Matrix (Fin n) (Fin n) R => A) hDC) j
        funext k
        have h2 := congrFun this k
        simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.one_apply, Pi.single_apply, eq_comm] using h2
      rw [this]
      simp [Pi.single_apply]
    rw [SetLike.mem_coe, h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Substitute using the available equality.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem isEigFrame_of_isUnit_det : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (O : Type) [CommRing O] (act : OAct O G) (σ : O →+* R) (n : ℕ) (u v : Fin n → (epsAt x ⟶ G)) (C : Matrix (Fin n) (Fin n) R), IsEigFrame act x σ u → (∀ i, IsComb (C i) u (v i)) → IsUnit C.det → IsEigFrame act x σ v := by
  intro S R _ G _ _ x O _ act σ n u v C hu hv hC
  obtain ⟨L, _, _, ⟨M⟩⟩ := lieModel_exists S G R x
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act S G R x L M O act.act act.hom act.one act.mul act.add
  obtain ⟨hc, hf⟩ := GlobalTheory.T.lie_model_eigenvectors_action S R G x L M
  have hf' := (hf O act ρ σ hρ).2 n
  have hex : ∀ k, ∃ e, M.pt e = u k := fun k => M.onto _ (hu.1 k).1
  choose b hb using hex
  obtain rfl : u = fun k => M.pt (b k) := funext fun k => (hb k).symm
  have hvv : v = fun i => M.pt (∑ k, C i k • b k) :=
    funext fun i => (hc n (C i) b (v i)).1 (hv i)
  subst hvv
  obtain ⟨hli, hsp⟩ := (hf' b).1 hu
  obtain ⟨h1, h2⟩ := comb_basis C hC b hli
  exact (hf' _).2 ⟨h1, h2.trans hsp⟩

end GlobalTheory.CompanionTheory.Ar.FrameUnit
