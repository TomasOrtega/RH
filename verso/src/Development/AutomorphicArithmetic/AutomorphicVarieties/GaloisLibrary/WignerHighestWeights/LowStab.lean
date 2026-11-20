import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

/- English proof (translation)
Introduce `ι V _ _ _ n F hF ν v hv`. Take `⟨hgl, hcomm⟩` from `hF`. Establish `hvlow : v ∈ low F v`. Unfold `UpperTheory.V.AlgRepEndIrreducible.low`. Rewrite using `[Submodule.mem_sInf]`.

Introduce `p hp`. Conclude with `hp.1`. Establish `hlow : ∀ t (i j : Fin n), j < i → ∀ w ∈ low F v, F t i j w ∈ low F v`. Introduce `t i j hji w hw`. Unfold `UpperTheory.V.AlgRepEndIrreducible.low at hw ⊢`.

Rewrite `hw`, the goal using `[Submodule.mem_sInf]`. Introduce `p hp`. Conclude with `hp.2 t i j hji w (hw p hp)`. Set `W' : Submodule ℂ V` to `low F v ⊓ ⨅ t, ⨅ i, ⨅ j, (low F v).comap (F t i j)`. Establish `hmem : ∀ w, w ∈ W' ↔ w ∈ low F v ∧ ∀ t i j, F t i j w ∈ low F v`.

Introduce `w`. Simplify using `[W', Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]`. Establish `hvW : v ∈ W'`. Rewrite using `[hmem]`. Use `⟨hvlow, fun t i j => ?_⟩` and prove the remaining obligations.

Break down `lt_trichotomy i j with h | h | h` into its components or cases. Rewrite using `[(hv t).2 i j h]`. Conclude with `zero_mem _`. Substitute `h` using the available equality. Rewrite using `[(hv t).1 i]`.

Conclude with `Submodule.smul_mem _ _ hvlow`. Conclude with `hlow t i j h v hvlow`. Establish `hWst : ∀ t (k l : Fin n), l < k → ∀ w ∈ W', F t k l w ∈ W'`. Introduce `t k l hlk w hw`. Rewrite `hw`, the goal using `[hmem]`.

Use `⟨hlow t k l hlk w hw.1, fun s i j => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hst : s = t`. Substitute `hst` using the available equality. Establish `h1` using `congrArg (fun f : Module.End ℂ V => f w) (hgl s i j k l)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h1`.

Rewrite `h1` using `[sub_eq_iff_eq_add]`. Rewrite using `[h1]`. Use `add_mem (sub_mem ?_ ?_) (hlow s k l hlk _ (hw.2 s i j))` and prove the remaining obligations. Use `split_ifs`. Conclude with `hw.2 s i l`.

Rewrite using `[LinearMap.zero_apply]`. Conclude with `zero_mem _`. Use `split_ifs`. Conclude with `hw.2 s k j`. Rewrite using `[LinearMap.zero_apply]`.

Conclude with `zero_mem _`. Establish `h1` using `congrArg (fun f : Module.End ℂ V => f w) (hcomm s t hst i j k l)`. Simplify using `only [Module.End.mul_apply] at h1`. Rewrite using `[h1]`. Conclude with `hlow t k l hlk _ (hw.2 s i j)`.

Establish `hle : low F v ≤ W'`. Unfold `UpperTheory.V.AlgRepEndIrreducible.low`. Conclude with `sInf_le ⟨hvW, hWst⟩`. Conclude with `⟨hvlow, fun t i j w hw => ((hmem w).mp (hle hw)).2 t i j⟩`.
-/
theorem UpperTheory.V.AlgRepEndIrreducible.lowStab :
    ∀ (ι V : Type) [Fintype ι] [AddCommGroup V] [Module ℂ V] (n : ℕ) (F : ι → Fin n → Fin n → Module.End ℂ V), IsMultiGl F → ∀ (ν : ι → Fin n → ℂ) (v : V), (∀ t, Formalism.REAL.IsHW (F t) (ν t) v) →
      v ∈ low F v ∧ Stab F (low F v) := by
  intro ι V _ _ _ n F hF ν v hv
  classical
  obtain ⟨hgl, hcomm⟩ := hF
  have hvlow : v ∈ low F v := by
    unfold UpperTheory.V.AlgRepEndIrreducible.low
    rw [Submodule.mem_sInf]
    intro p hp
    exact hp.1
  have hlow : ∀ t (i j : Fin n), j < i → ∀ w ∈ low F v, F t i j w ∈ low F v := by
    intro t i j hji w hw
    unfold UpperTheory.V.AlgRepEndIrreducible.low at hw ⊢
    rw [Submodule.mem_sInf] at hw ⊢
    intro p hp
    exact hp.2 t i j hji w (hw p hp)
  let W' : Submodule ℂ V := low F v ⊓ ⨅ t, ⨅ i, ⨅ j, (low F v).comap (F t i j)
  have hmem : ∀ w, w ∈ W' ↔ w ∈ low F v ∧ ∀ t i j, F t i j w ∈ low F v := by
    intro w
    simp [W', Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
  have hvW : v ∈ W' := by
    rw [hmem]
    refine ⟨hvlow, fun t i j => ?_⟩
    rcases lt_trichotomy i j with h | h | h
    · rw [(hv t).2 i j h]
      exact zero_mem _
    · subst h
      rw [(hv t).1 i]
      exact Submodule.smul_mem _ _ hvlow
    · exact hlow t i j h v hvlow
  have hWst : ∀ t (k l : Fin n), l < k → ∀ w ∈ W', F t k l w ∈ W' := by
    intro t k l hlk w hw
    rw [hmem] at hw ⊢
    refine ⟨hlow t k l hlk w hw.1, fun s i j => ?_⟩
    by_cases hst : s = t
    · subst hst
      have h1 := congrArg (fun f : Module.End ℂ V => f w) (hgl s i j k l)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1
      rw [sub_eq_iff_eq_add] at h1
      rw [h1]
      refine add_mem (sub_mem ?_ ?_) (hlow s k l hlk _ (hw.2 s i j))
      · split_ifs
        · exact hw.2 s i l
        · rw [LinearMap.zero_apply]
          exact zero_mem _
      · split_ifs
        · exact hw.2 s k j
        · rw [LinearMap.zero_apply]
          exact zero_mem _
    · have h1 := congrArg (fun f : Module.End ℂ V => f w) (hcomm s t hst i j k l)
      simp only [Module.End.mul_apply] at h1
      rw [h1]
      exact hlow t k l hlk _ (hw.2 s i j)
  have hle : low F v ≤ W' := by
    unfold UpperTheory.V.AlgRepEndIrreducible.low
    exact sInf_le ⟨hvW, hWst⟩
  exact ⟨hvlow, fun t i j w hw => ((hmem w).mp (hle hw)).2 t i j⟩
