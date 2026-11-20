import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing

set_option autoImplicit false
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4
open CrystallineSemistableComparison.Onto

/- English proof (translation)
Simplify using `only [dZ, map_sum, map_zsmul, hn]`.
-/
theorem dZ_addEquiv_apply {ι : Type} [DecidableEq ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)]
    [∀ S, AddCommGroup (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T)
    (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T) (e : ∀ S, M S ≃+ N S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (r h x) = r' h (e S x)) (m : ℕ)
    (c : ∀ i : Fin (m + 1) → ι, M (ent i)) (i : Fin (m + 2) → ι) :
    e _ (dZ M r m c i) = dZ N r' m (fun i => e _ (c i)) i := by
  simp only [dZ, map_sum, map_zsmul, hn]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply `(e _).injective` to reduce the goal to its premises. Rewrite using `[dZ_addEquiv_apply M N r r' e hn m, Pi.zero_apply, map_zero]`. Simplify using `only [AddEquiv.apply_symm_apply]`. Conclude with `congrFun hc i`.
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
Introduce `ι _ M N _ _ r r' e hn hM`. Take `⟨h0, h1, h2⟩` from `hM`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Establish `hx' : (e ∅).symm x = 0`.

Apply `h0` to reduce the goal to its premises. Introduce `i`. Establish `h7` using `hn (Finset.empty_subset (ent i)) ((e ∅).symm x)`. Rewrite `h7` using `[AddEquiv.apply_symm_apply]`. Establish `h8 : r' (Finset.empty_subset (ent i)) x = 0` using `hx i`.

Rewrite `h7` using `[h8]`. Conclude with `(e _).injective (h7.trans (map_zero _).symm)`. Simplify using `using congrArg (e ∅) hx'`. Introduce `c hc`. Take `⟨x, hx⟩` from `h1 (fun i => (e _).symm (c i)) (dZ_eq_zero_of_addEquiv M N r r' e hn 0 c hc)`.

Use `⟨e ∅ x, fun i => ?_⟩` and prove the remaining obligations. Establish `h5 : r (Finset.empty_subset (ent i)) x = (e _).symm (c i)` using `hx i`. Establish `h6` using `hn (Finset.empty_subset (ent i)) x`. Rewrite `h6` using `[h5, AddEquiv.apply_symm_apply]`. Conclude with `h6.symm`.

Introduce `m c hc`. Take `⟨b, hb⟩` from `h2 m (fun i => (e _).symm (c i)) (dZ_eq_zero_of_addEquiv M N r r' e hn (m + 1) c hc)`. Use `⟨fun i => e _ (b i), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `h3` using `dZ_addEquiv_apply M N r r' e hn m b i`.

Establish `h4 : dZ M r m b i = (e _).symm (c i)` using `congrFun hb i`. Rewrite `h3` using `[h4, AddEquiv.apply_symm_apply]`. Conclude with `h3.symm`.
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
