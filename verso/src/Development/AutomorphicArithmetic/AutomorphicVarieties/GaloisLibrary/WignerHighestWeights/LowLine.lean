import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

/- English proof (translation)
Take `⟨hgl, hcomm⟩` from `hF`. Establish `key : ∀ s (a : Fin n), F s a a (F t i j x) = F t i j (F s a a x) + (if s = t then ((if a = i then F t a j x else 0) - (if j = a then F t i a x else 0)) else 0)`. Introduce `s a`. Distinguish the cases in `hst : s = t`. Substitute `hst` using the available equality.

Rewrite using `[if_pos rfl]`. Establish `h1` using `congrArg (fun f : Module.End ℂ V => f x) (hgl s a a i j)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h1`. Apply the tactic sequence `have h2 : (if a = i then F s a j x else 0) - (if j = a then F s i a x else 0) = (if a = i then F s a j else 0) x - (if j = a then F s i a else 0) x := by split_ifs <;> simp`. Rewrite using `[h2, ← h1]`.

Normalize the expressions using the abelian group laws. Rewrite using `[if_neg hst]`. Establish `h1` using `congrArg (fun f : Module.End ℂ V => f x) (hcomm s t hst a a i j)`. Simplify using `only [Module.End.mul_apply] at h1`. Rewrite using `[h1, add_zero]`.

Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, key, smul_add, Finset.sum_add_distrib, map_sum, map_smul]`. Use `congr 1`. Simplify using `[smul_ite, smul_sub, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.sum_ite_irrel, sub_smul]`.
-/
private theorem weight_operator_commutator_multiGl {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (F : ι → Fin n → Fin n → Module.End ℂ V) (hF : IsMultiGl F) (t : ι) (i j : Fin n) (x : V) :
    (∑ s, ∑ a : Fin n, ((a : ℕ) : ℂ) • F s a a) (F t i j x) =
      F t i j ((∑ s, ∑ a : Fin n, ((a : ℕ) : ℂ) • F s a a) x) +
        (((i : ℕ) : ℂ) - ((j : ℕ) : ℂ)) • F t i j x := by
  classical
  obtain ⟨hgl, hcomm⟩ := hF
  have key : ∀ s (a : Fin n), F s a a (F t i j x) = F t i j (F s a a x) +
      (if s = t then ((if a = i then F t a j x else 0) - (if j = a then F t i a x else 0)) else 0) := by
    intro s a
    by_cases hst : s = t
    · subst hst
      rw [if_pos rfl]
      have h1 := congrArg (fun f : Module.End ℂ V => f x) (hgl s a a i j)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1
      have h2 : (if a = i then F s a j x else 0) - (if j = a then F s i a x else 0) =
          (if a = i then F s a j else 0) x - (if j = a then F s i a else 0) x := by
        split_ifs <;> simp
      rw [h2, ← h1]
      abel
    · rw [if_neg hst]
      have h1 := congrArg (fun f : Module.End ℂ V => f x) (hcomm s t hst a a i j)
      simp only [Module.End.mul_apply] at h1
      rw [h1, add_zero]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, key, smul_add, Finset.sum_add_distrib,
    map_sum, map_smul]
  congr 1
  simp [smul_ite, smul_sub, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.sum_ite_irrel, sub_smul]

/- English proof (translation)
Introduce `ι V _ _ _ n F hF ν v hv w hw hwν`. Use `set H : Module.End ℂ V := ∑ s, ∑ a : Fin n, ((a : ℕ) : ℂ) • F s a a with hH`. Use `set l0 : ℂ := ∑ s, ∑ a : Fin n, ((a : ℕ) : ℂ) * ν s a with hl0`. Establish `hHx : ∀ x : V, (∀ s k, F s k k x = ν s k • x) → H x = l0 • x`. Introduce `x hx`.

Simplify using `only [hH, hl0, LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul, Finset.sum_smul]`. Establish `hsh : ∀ t (i j : Fin n) (μ : ℂ) (x : V), H x = μ • x → H (F t i j x) = (μ + (((i : ℕ) : ℂ) - ((j : ℕ) : ℂ))) • F t i j x`. Introduce `t i j μ x hx`. Rewrite using `[hH, weight_operator_commutator_multiGl F hF t i j x, ← hH, hx, map_smul, add_smul]`. Establish `hdist : ∀ i j : Fin n, j < i → ∃ d : ℕ, ((i : ℕ) : ℂ) - ((j : ℕ) : ℂ) = (d : ℂ) + 1`.

Introduce `i j hji`. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_lt (show (j : ℕ) < (i : ℕ) from hji)`. Use `⟨d, ?_⟩` and prove the remaining obligations. Rewrite using `[hd]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Set `M : Submodule ℂ V` to `⨆ k : ℕ, H.eigenspace (l0 + ((k : ℂ) + 1))`. Establish `hFM : ∀ t (i j : Fin n), j < i → ∀ z ∈ M, F t i j z ∈ M`. Introduce `t i j hji z hz`. Take `⟨d, hd⟩` from `hdist i j hji`.

Use `Submodule.iSup_induction _ (motive := fun z => F t i j z ∈ M) hz ?_ ?_ ?_` and prove the remaining obligations. Introduce `k z hz`. Rewrite `hz` using `[Module.End.mem_eigenspace_iff]`. Establish `h1` using `hsh t i j _ z hz`. Use `(le_iSup (fun k : ℕ => H.eigenspace (l0 + ((k : ℂ) + 1))) (k + d + 1)) ?_` and prove the remaining obligations.

Rewrite using `[Module.End.mem_eigenspace_iff, h1, hd]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

Introduce `x y hx hy`. Rewrite using `[map_add]`. Conclude with `add_mem hx hy`. Set `P : Submodule ℂ V` to `(ℂ ∙ v) ⊔ M`. Establish `hvP : v ∈ P` using `Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)`.

Establish `hPst : ∀ t (i j : Fin n), j < i → ∀ x ∈ P, F t i j x ∈ P`. Introduce `t i j hji x hx`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp hx`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.mp hy`. Rewrite using `[map_add, map_smul]`.

Use `Submodule.mem_sup_right (add_mem (Submodule.smul_mem _ _ ?_) (hFM t i j hji z hz))` and prove the remaining obligations. Take `⟨d, hd⟩` from `hdist i j hji`. Use `(le_iSup (fun k : ℕ => H.eigenspace (l0 + ((k : ℂ) + 1))) d) ?_` and prove the remaining obligations. Rewrite using `[Module.End.mem_eigenspace_iff, hsh t i j l0 v (hHx v (fun s k => (hv s).1 k)), hd]`. Establish `hle : low F v ≤ P`.

Unfold `UpperTheory.V.AlgRepEndIrreducible.low`. Conclude with `sInf_le ⟨hvP, hPst⟩`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.mp (hle hw)`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.mp hy`. Establish `hHz : H z = l0 • z`.

Establish `e1` using `hHx w hwν`. Establish `e2` using `hHx v (fun s k => (hv s).1 k)`. Establish `e3 : z = w - c • v`. Rewrite using `[← hyz]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e3, map_sub, map_smul, e1, e2, smul_sub, smul_comm]`. Establish `hMle : M ≤ ⨆ μ, ⨆ (_ : μ ≠ l0), H.eigenspace μ`. Use `iSup_le fun k => le_iSup₂_of_le (l0 + ((k : ℂ) + 1)) ?_ le_rfl` and prove the remaining obligations. Introduce `h`. Establish `h2 : ((k : ℂ) + 1) = 0` using `by linear_combination h`.

Conclude with `Nat.cast_add_one_ne_zero k h2`. Establish `hz0 : z = 0` using `(Submodule.disjoint_def.mp ((Module.End.eigenspaces_iSupIndep H) l0)) z (Module.End.mem_eigenspace_iff.mpr hHz) (hMle hz)`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[← hyz, hz0, add_zero]`.
-/
theorem UpperTheory.V.AlgRepEndIrreducible.lowLine :
    ∀ (ι V : Type) [Fintype ι] [AddCommGroup V] [Module ℂ V] (n : ℕ) (F : ι → Fin n → Fin n → Module.End ℂ V), IsMultiGl F → ∀ (ν : ι → Fin n → ℂ) (v : V), (∀ t, Formalism.REAL.IsHW (F t) (ν t) v) →
      ∀ w ∈ low F v, (∀ t k, F t k k w = ν t k • w) → ∃ c : ℂ, w = c • v := by
  intro ι V _ _ _ n F hF ν v hv w hw hwν
  classical
  set H : Module.End ℂ V := ∑ s, ∑ a : Fin n, ((a : ℕ) : ℂ) • F s a a with hH
  set l0 : ℂ := ∑ s, ∑ a : Fin n, ((a : ℕ) : ℂ) * ν s a with hl0
  have hHx : ∀ x : V, (∀ s k, F s k k x = ν s k • x) → H x = l0 • x := by
    intro x hx
    simp only [hH, hl0, LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul, Finset.sum_smul]
  have hsh : ∀ t (i j : Fin n) (μ : ℂ) (x : V), H x = μ • x →
      H (F t i j x) = (μ + (((i : ℕ) : ℂ) - ((j : ℕ) : ℂ))) • F t i j x := by
    intro t i j μ x hx
    rw [hH, weight_operator_commutator_multiGl F hF t i j x, ← hH, hx, map_smul, add_smul]
  have hdist : ∀ i j : Fin n, j < i → ∃ d : ℕ, ((i : ℕ) : ℂ) - ((j : ℕ) : ℂ) = (d : ℂ) + 1 := by
    intro i j hji
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (show (j : ℕ) < (i : ℕ) from hji)
    refine ⟨d, ?_⟩
    rw [hd]
    push_cast
    ring
  let M : Submodule ℂ V := ⨆ k : ℕ, H.eigenspace (l0 + ((k : ℂ) + 1))
  have hFM : ∀ t (i j : Fin n), j < i → ∀ z ∈ M, F t i j z ∈ M := by
    intro t i j hji z hz
    obtain ⟨d, hd⟩ := hdist i j hji
    refine Submodule.iSup_induction _ (motive := fun z => F t i j z ∈ M) hz ?_ ?_ ?_
    · intro k z hz
      rw [Module.End.mem_eigenspace_iff] at hz
      have h1 := hsh t i j _ z hz
      refine (le_iSup (fun k : ℕ => H.eigenspace (l0 + ((k : ℂ) + 1))) (k + d + 1)) ?_
      rw [Module.End.mem_eigenspace_iff, h1, hd]
      congr 1
      push_cast
      ring
    · simp
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy
  let P : Submodule ℂ V := (ℂ ∙ v) ⊔ M
  have hvP : v ∈ P := Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
  have hPst : ∀ t (i j : Fin n), j < i → ∀ x ∈ P, F t i j x ∈ P := by
    intro t i j hji x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_add, map_smul]
    refine Submodule.mem_sup_right (add_mem (Submodule.smul_mem _ _ ?_) (hFM t i j hji z hz))
    obtain ⟨d, hd⟩ := hdist i j hji
    refine (le_iSup (fun k : ℕ => H.eigenspace (l0 + ((k : ℂ) + 1))) d) ?_
    rw [Module.End.mem_eigenspace_iff, hsh t i j l0 v (hHx v (fun s k => (hv s).1 k)), hd]
  have hle : low F v ≤ P := by
    unfold UpperTheory.V.AlgRepEndIrreducible.low
    exact sInf_le ⟨hvP, hPst⟩
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hle hw)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hHz : H z = l0 • z := by
    have e1 := hHx w hwν
    have e2 := hHx v (fun s k => (hv s).1 k)
    have e3 : z = w - c • v := by
      rw [← hyz]
      abel
    rw [e3, map_sub, map_smul, e1, e2, smul_sub, smul_comm]
  have hMle : M ≤ ⨆ μ, ⨆ (_ : μ ≠ l0), H.eigenspace μ := by
    refine iSup_le fun k => le_iSup₂_of_le (l0 + ((k : ℂ) + 1)) ?_ le_rfl
    intro h
    have h2 : ((k : ℂ) + 1) = 0 := by linear_combination h
    exact Nat.cast_add_one_ne_zero k h2
  have hz0 : z = 0 :=
    (Submodule.disjoint_def.mp ((Module.End.eigenspaces_iSupIndep H) l0)) z
      (Module.End.mem_eigenspace_iff.mpr hHz) (hMle hz)
  refine ⟨c, ?_⟩
  rw [← hyz, hz0, add_zero]
