import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing

set_option autoImplicit false
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4
open CrystallineSemistableComparison.Onto

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem dZ_addEquiv_apply {ι : Type} [DecidableEq ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)]
    [∀ S, AddCommGroup (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T)
    (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T) (e : ∀ S, M S ≃+ N S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (r h x) = r' h (e S x)) (m : ℕ)
    (c : ∀ i : Fin (m + 1) → ι, M (ent i)) (i : Fin (m + 2) → ι) :
    e _ (dZ M r m c i) = dZ N r' m (fun i => e _ (c i)) i := by
  simp only [dZ, map_sum, map_zsmul, hn]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem dZ_eq_zero_of_addEquiv {ι : Type} [DecidableEq ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)]
    [∀ S, AddCommGroup (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T)
    (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T) (e : ∀ S, M S ≃+ N S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (r h x) = r' h (e S x)) (m : ℕ)
    (c : ∀ i : Fin (m + 1) → ι, N (ent i)) (hc : dZ N r' m c = 0) :
    dZ M r m (fun i => (e _).symm (c i)) = 0 := by
  funext i
  apply (e _).injective
  rw [dZ_addEquiv_apply M N r r' e hn m, Pi.zero_apply, map_zero]
  simp only [AddEquiv.apply_symm_apply]
  exact congrFun hc i

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem exP_of_addEquiv : ∀ {ι : Type} [DecidableEq ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, AddCommGroup (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T) (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T) (e : ∀ S, M S ≃+ N S), (∀ {S T : Finset ι} (h : S ⊆ T) x, e T (r h x) = r' h (e S x)) → ExP M r → ExP N r' := by
  intro ι _ M N _ _ r r' e hn hM
  obtain ⟨h0, h1, h2⟩ := hM
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx' : (e ∅).symm x = 0 := by
      apply h0
      intro i
      have h7 := hn (Finset.empty_subset (ent i)) ((e ∅).symm x)
      rw [AddEquiv.apply_symm_apply] at h7
      have h8 : r' (Finset.empty_subset (ent i)) x = 0 := hx i
      rw [h8] at h7
      exact (e _).injective (h7.trans (map_zero _).symm)
    simpa using congrArg (e ∅) hx'
  · intro c hc
    obtain ⟨x, hx⟩ := h1 (fun i => (e _).symm (c i)) (dZ_eq_zero_of_addEquiv M N r r' e hn 0 c hc)
    refine ⟨e ∅ x, fun i => ?_⟩
    have h5 : r (Finset.empty_subset (ent i)) x = (e _).symm (c i) := hx i
    have h6 := hn (Finset.empty_subset (ent i)) x
    rw [h5, AddEquiv.apply_symm_apply] at h6
    exact h6.symm
  · intro m c hc
    obtain ⟨b, hb⟩ := h2 m (fun i => (e _).symm (c i)) (dZ_eq_zero_of_addEquiv M N r r' e hn (m + 1) c hc)
    refine ⟨fun i => e _ (b i), ?_⟩
    funext i
    have h3 := dZ_addEquiv_apply M N r r' e hn m b i
    have h4 : dZ M r m b i = (e _).symm (c i) := congrFun hb i
    rw [h4, AddEquiv.apply_symm_apply] at h3
    exact h3.symm

end GlobalTheory.CompanionTheory.SurjectionOntoH4
