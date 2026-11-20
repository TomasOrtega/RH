import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.KerCoreSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.DescPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FunKerPf

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct
open TensorProduct

/- English proof (translation)
Establish `hwf : WellFoundedLT (Submodule K V)` using `inferInstance`. Take `⟨N0, ⟨t0, ht0S, rfl⟩, hmin⟩` from `hwf.wf.has_min {N | ∃ t : Finset (Submodule K V), (t : Set (Submodule K V)) ⊆ S ∧ N = t.inf id} ⟨⊤, ∅, by simp, by simp⟩`. Use `⟨t0, ht0S, fun N hN => ?_⟩` and prove the remaining obligations. Establish `hmem : (insert N t0).inf id ∈ {N | ∃ t : Finset (Submodule K V), (t : Set (Submodule K V)) ⊆ S ∧ N = t.inf id}` using `⟨insert N t0, by`. Rewrite using `[Finset.coe_insert, Set.insert_subset_iff]`.

Conclude with `⟨hN, ht0S⟩, rfl⟩`. Establish `hle : (insert N t0).inf id ≤ t0.inf id` using `Finset.inf_mono (Finset.subset_insert _ _)`. Establish `heq : (insert N t0).inf id = t0.inf id` using `eq_of_le_of_not_lt hle (hmin _ hmem)`. Rewrite `heq` using `[Finset.inf_insert]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_finset_inf_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Set (Submodule K V)) : ∃ t : Finset (Submodule K V), (t : Set _) ⊆ S ∧ ∀ N ∈ S, t.inf id ≤ N := by
  classical
  have hwf : WellFoundedLT (Submodule K V) := inferInstance
  obtain ⟨N0, ⟨t0, ht0S, rfl⟩, hmin⟩ := hwf.wf.has_min
    {N | ∃ t : Finset (Submodule K V), (t : Set (Submodule K V)) ⊆ S ∧ N = t.inf id}
    ⟨⊤, ∅, by simp, by simp⟩
  refine ⟨t0, ht0S, fun N hN => ?_⟩
  have hmem : (insert N t0).inf id ∈
      {N | ∃ t : Finset (Submodule K V), (t : Set (Submodule K V)) ⊆ S ∧ N = t.inf id} :=
    ⟨insert N t0, by
      rw [Finset.coe_insert, Set.insert_subset_iff]
      exact ⟨hN, ht0S⟩, rfl⟩
  have hle : (insert N t0).inf id ≤ t0.inf id := Finset.inf_mono (Finset.subset_insert _ _)
  have heq : (insert N t0).inf id = t0.inf id := eq_of_le_of_not_lt hle (hmin _ hmem)
  rw [Finset.inf_insert] at heq
  calc t0.inf id = N ⊓ t0.inf id := heq.symm
    _ ≤ N := inf_le_left

/- English proof (translation)
Introduce `K _ _ V _ _ _ W Fam hkill hdet henl`. Set `S : Set (Submodule K V)` to `{N | ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra K K₁) (f : V →ₗ[K] K₁), Fam K₁ f ∧ N = LinearMap.ker f}`. Take `⟨t, htS, htinf⟩` from `exists_finset_inf_eq S`. Establish `hmem : ∀ N : t, ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra K K₁) (f : V →ₗ[K] K₁), Fam K₁ f ∧ (N : Submodule K V) = LinearMap.ker f` using `fun N => htS N.2`. Use `choose Ki fKi nfKi aKi fi hfam hNker using hmem`.

Establish `hWinf : t.inf id = W`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `v hv`. Apply `hdet v` to reduce the goal to its premises. Introduce `K₁ _ _ _ f hf`.

Use `htinf (LinearMap.ker f) ⟨K₁, inferInstance, inferInstance, inferInstance, f, hf, rfl⟩ hv` as an intermediate fact. Conclude with `this`. Use `Finset.le_inf fun N hN => ?_` and prove the remaining obligations. Establish `h1` using `hNker ⟨N, hN⟩`. Simplify using `only at h1`.

Use `show W ≤ N`. Rewrite using `[h1]`. Conclude with `hkill _ _ (hfam ⟨N, hN⟩)`. Establish `hWmem : ∀ v, v ∈ W ↔ ∀ N : t, fi N v = 0`. Introduce `v`.

Rewrite using `[← hWinf, Finset.inf_eq_iInf]`. Simplify using `only [Submodule.mem_iInf, id]`. Prove the components needed by the constructor for the conclusion. Introduce `hv N`. Establish `h1` using `hv N N.2`.

Rewrite `h1` using `[hNker N]`. Conclude with `h1`. Introduce `h N hN`. Establish `h1` using `hNker ⟨N, hN⟩`. Simplify using `only at h1`.

Rewrite using `[h1]`. Conclude with `h ⟨N, hN⟩`. Set `Ω` to `AlgebraicClosure K`. Establish `hfinKi : ∀ N, FiniteDimensional K (Ki N)` using `fun N => Module.Finite.of_restrictScalars_finite ℚ K (Ki N)`. Set `ιi : ∀ N : t, Ki N →ₐ[K] Ω` to `fun N =>`.

Use `hfinKi N` as an intermediate fact. Use the proof step `IsAlgClosed.lift`. Set `M : IntermediateField K Ω` to `⨆ N : t, (ιi N).fieldRange`. Establish `hMfin : FiniteDimensional K M`. Establish `: ∀ N : t, FiniteDimensional K (ιi N).fieldRange` using `fun N => haveI := hfinKi N (AlgHom.equivFieldRange (ιi N)).toLinearEquiv.finiteDimensional`.

Conclude with `IntermediateField.finiteDimensional_iSup_of_finite`. Set `L : IntermediateField K Ω` to `IntermediateField.normalClosure K M Ω`. Establish `hLfin : FiniteDimensional K L` using `inferInstance`. Establish `hLgal : IsGalois K L` using `inferInstance`. Establish `hML : M ≤ L` using `IntermediateField.le_normalClosure M`.

Establish `hQL : FiniteDimensional ℚ L` using `Module.Finite.trans K L`. Establish `hnfL : NumberField L` using `⟨⟩`. Establish `hrange : ∀ N (x : Ki N), ιi N x ∈ L` using `fun N x => hML (le_iSup (fun N : t => (ιi N).fieldRange) N ⟨x, rfl⟩)`. Set `e0 : ∀ N : t, Ki N →ₐ[K] L` to `fun N => (ιi N).codRestrict L.toSubalgebra (hrange N)`. Establish `hg : ∀ (N : t) (e : Ki N →ₐ[K] L), ∃ g : V →ₗ[K] L, Fam L g ∧ ∀ v, g v = e (fi N v)` using `fun N e => henl (Ki N) L e (fi N) (hfam N)`.

Use `choose g hgfam hgval using hg`. Set `gh : (Σ N : t, (Ki N →ₐ[K] L)) → Module.Dual L (L ⊗[K] V)` to `fun p => (g p.1 p.2).liftBaseChange L`. Establish `hgh1 : ∀ p v, gh p ((1 : L) ⊗ₜ[K] v) = g p.1 p.2 v` using `fun p v => LinearMap.liftBaseChange_one_tmul _ _ _`. Set `Kc : Submodule L (L ⊗[K] V)` to `⨅ p, LinearMap.ker (gh p)`. Establish `hkey : ∀ (σ : L ≃ₐ[K] L) (N : t) (e : Ki N →ₐ[K] L) (x : L ⊗[K] V), gh ⟨N, e⟩ (galAct σ x) = σ (gh ⟨N, (σ.symm.toAlgHom).comp e⟩ x)`.

Introduce `σ N e x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a v`. Simplify using `only [gh, galAct_tmul, LinearMap.liftBaseChange_tmul, hgval, smul_eq_mul, map_mul, AlgHom.comp_apply]`.

Use `congr 1`. Conclude with `(σ.apply_symm_apply _).symm`. Consider the case `add y z hy hz => simp only [map_add, hy, hz]`. Establish `hstab : ∀ σ : L ≃ₐ[K] L, ∀ x ∈ Kc, galAct σ x ∈ Kc`. Introduce `σ x hx`.

Rewrite `hx`, the goal using `[Submodule.mem_iInf]`. Introduce and unpack `⟨N, e⟩`. Rewrite using `[LinearMap.mem_ker, hkey, LinearMap.mem_ker.mp (hx ⟨N, _⟩), map_zero]`. Establish `hGD` using `galoisDescent_holds K L V Kc hstab`. Establish `hkP : kPoints Kc = W`.

Use extensionality with `v`. Rewrite using `[hWmem]`. Use `show (1 : L) ⊗ₜ[K] v ∈ Kc ↔ _`. Rewrite using `[Submodule.mem_iInf]`. Prove the components needed by the constructor for the conclusion.

Introduce `h N`. Establish `h1` using `LinearMap.mem_ker.mp (h ⟨N, e0 N⟩)`. Establish `h2 : e0 N (fi N v) = 0`. Establish `h3` using `hgval N (e0 N) v`. Rewrite using `[← h3]`.

Simplify `h1` using `[hgh1]`. Conclude with `(e0 N).toRingHom.injective (by simpa using h2)`. Introduce `h p`. Rewrite using `[LinearMap.mem_ker, hgh1, hgval p.1 p.2 v, h p.1, map_zero]`. Establish `hKc : Kc = baseSpan L W` using `by rw [hGD, hkP]`.

Set `G : Set (Module.Dual L (L ⊗[K] V))` to `Set.range gh`. Take `⟨t', ht'sub, ht'span, ht'li⟩` from `exists_linearIndependent L G`. Establish `ht'fin : t'.Finite` using `ht'li.setFinite`. Establish `: Fintype t'` using `ht'fin.fintype`. Use `set ρ := Fintype.card t' with hρ`.

Set `eT` to `Fintype.equivFin t'`. Establish `hpick : ∀ i : Fin ρ, ∃ p, gh p = (eT.symm i : Module.Dual L (L ⊗[K] V))` using `fun i => ht'sub (eT.symm i).2`. Use `choose pk hpk using hpick`. Set `cfL : Fin ρ → Module.Dual L (L ⊗[K] V)` to `fun i => (eT.symm i : Module.Dual L (L ⊗[K] V))`. Establish `hcomm : ∀ x : L ⊗[K] V, (∀ i, cfL i x = 0) ↔ x ∈ Kc`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[Submodule.mem_iInf]`. Introduce `p`.

Rewrite using `[LinearMap.mem_ker]`. Establish `hsp : Submodule.span L t' ≤ LinearMap.ker (Module.Dual.eval L (L ⊗[K] V) x)`. Use `Submodule.span_le.mpr fun φ hφ => ?_` and prove the remaining obligations. Use `h (eT ⟨φ, hφ⟩)` as an intermediate fact. Simplify `this` using `[cfL]`.

Establish `hmem : gh p ∈ Submodule.span L t'` using `ht'span ▸ Submodule.subset_span ⟨p, rfl⟩`. Simplify using `using hsp hmem`. Introduce `hx i`. Rewrite `hx` using `[Submodule.mem_iInf]`. Use `show (eT.symm i : Module.Dual L (L ⊗[K] V)) x = 0`.

Rewrite using `[← hpk i]`. Conclude with `LinearMap.mem_ker.mp (hx (pk i))`. Establish `hcoan : (Submodule.span L t').dualCoannihilator = Kc`. Use extensionality with `x`. Rewrite using `[Submodule.mem_dualCoannihilator, ← hcomm]`.

Prove the components needed by the constructor for the conclusion. Introduce `h i`. Conclude with `h _ (Submodule.subset_span (eT.symm i).2)`. Introduce `h φ hφ`. Establish `hsp : Submodule.span L t' ≤ LinearMap.ker (Module.Dual.eval L (L ⊗[K] V) x)`.

Use `Submodule.span_le.mpr fun ψ hψ => ?_` and prove the remaining obligations. Use `h (eT ⟨ψ, hψ⟩)` as an intermediate fact. Simplify `this` using `[cfL]`. Simplify using `using hsp hφ`. Establish `hWfd : FiniteDimensional K W` using `inferInstance`.

Establish `hdim : Module.finrank K W + ρ = Module.finrank K V`. Establish `h1` using `Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span L t')`. Rewrite `h1` using `[hcoan, hKc, finrank_baseSpan L W, Module.finrank_baseChange]`. Establish `h2 : Module.finrank L (Submodule.span L t') = ρ`. Rewrite using `[hρ, finrank_span_set_eq_card ht'li, Set.toFinset_card]`.

Use linear arithmetic over natural numbers and integers. Use `⟨L, inferInstance, hnfL, inferInstance, ρ, fun i => g (pk i).1 (pk i).2, cfL, fun i => hgfam _ _, fun i v => ?_, fun x => ?_, hdim⟩` and prove the remaining obligations. Rewrite using `[show cfL i = gh (pk i) from (hpk i).symm, hgh1]`. Rewrite using `[hcomm, hKc]`.
-/
theorem kerCore_holds : KerCoreStatement := by
  intro K _ _ V _ _ _ W Fam hkill hdet henl
  classical

  let S : Set (Submodule K V) := {N | ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra K K₁)
    (f : V →ₗ[K] K₁), Fam K₁ f ∧ N = LinearMap.ker f}
  obtain ⟨t, htS, htinf⟩ := exists_finset_inf_eq S
  have hmem : ∀ N : t, ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra K K₁)
      (f : V →ₗ[K] K₁), Fam K₁ f ∧ (N : Submodule K V) = LinearMap.ker f := fun N => htS N.2
  choose Ki fKi nfKi aKi fi hfam hNker using hmem
  have hWinf : t.inf id = W := by
    apply le_antisymm
    · intro v hv
      apply hdet v
      intro K₁ _ _ _ f hf
      have := htinf (LinearMap.ker f) ⟨K₁, inferInstance, inferInstance, inferInstance, f, hf, rfl⟩ hv
      exact this
    · refine Finset.le_inf fun N hN => ?_
      have h1 := hNker ⟨N, hN⟩
      simp only at h1
      show W ≤ N
      rw [h1]
      exact hkill _ _ (hfam ⟨N, hN⟩)
  have hWmem : ∀ v, v ∈ W ↔ ∀ N : t, fi N v = 0 := by
    intro v
    rw [← hWinf, Finset.inf_eq_iInf]
    simp only [Submodule.mem_iInf, id]
    constructor
    · intro hv N
      have h1 := hv N N.2
      rw [hNker N] at h1
      exact h1
    · intro h N hN
      have h1 := hNker ⟨N, hN⟩
      simp only at h1
      rw [h1]
      exact h ⟨N, hN⟩

  let Ω := AlgebraicClosure K
  have hfinKi : ∀ N, FiniteDimensional K (Ki N) := fun N =>
    Module.Finite.of_restrictScalars_finite ℚ K (Ki N)
  let ιi : ∀ N : t, Ki N →ₐ[K] Ω := fun N =>
    have := hfinKi N
    IsAlgClosed.lift
  let M : IntermediateField K Ω := ⨆ N : t, (ιi N).fieldRange
  have hMfin : FiniteDimensional K M := by
    have : ∀ N : t, FiniteDimensional K (ιi N).fieldRange := fun N =>
      haveI := hfinKi N
      (AlgHom.equivFieldRange (ιi N)).toLinearEquiv.finiteDimensional
    exact IntermediateField.finiteDimensional_iSup_of_finite
  let L : IntermediateField K Ω := IntermediateField.normalClosure K M Ω
  have hLfin : FiniteDimensional K L := inferInstance
  have hLgal : IsGalois K L := inferInstance
  have hML : M ≤ L := IntermediateField.le_normalClosure M
  have hQL : FiniteDimensional ℚ L := Module.Finite.trans K L
  have hnfL : NumberField L := ⟨⟩

  have hrange : ∀ N (x : Ki N), ιi N x ∈ L := fun N x =>
    hML (le_iSup (fun N : t => (ιi N).fieldRange) N ⟨x, rfl⟩)
  let e0 : ∀ N : t, Ki N →ₐ[K] L := fun N => (ιi N).codRestrict L.toSubalgebra (hrange N)

  have hg : ∀ (N : t) (e : Ki N →ₐ[K] L), ∃ g : V →ₗ[K] L, Fam L g ∧ ∀ v, g v = e (fi N v) :=
    fun N e => henl (Ki N) L e (fi N) (hfam N)
  choose g hgfam hgval using hg
  let gh : (Σ N : t, (Ki N →ₐ[K] L)) → Module.Dual L (L ⊗[K] V) :=
    fun p => (g p.1 p.2).liftBaseChange L
  have hgh1 : ∀ p v, gh p ((1 : L) ⊗ₜ[K] v) = g p.1 p.2 v := fun p v =>
    LinearMap.liftBaseChange_one_tmul _ _ _
  let Kc : Submodule L (L ⊗[K] V) := ⨅ p, LinearMap.ker (gh p)

  have hkey : ∀ (σ : L ≃ₐ[K] L) (N : t) (e : Ki N →ₐ[K] L) (x : L ⊗[K] V),
      gh ⟨N, e⟩ (galAct σ x) = σ (gh ⟨N, (σ.symm.toAlgHom).comp e⟩ x) := by
    intro σ N e x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      simp only [gh, galAct_tmul, LinearMap.liftBaseChange_tmul, hgval, smul_eq_mul, map_mul,
        AlgHom.comp_apply]
      congr 1
      exact (σ.apply_symm_apply _).symm
    | add y z hy hz => simp only [map_add, hy, hz]
  have hstab : ∀ σ : L ≃ₐ[K] L, ∀ x ∈ Kc, galAct σ x ∈ Kc := by
    intro σ x hx
    rw [Submodule.mem_iInf] at hx ⊢
    rintro ⟨N, e⟩
    rw [LinearMap.mem_ker, hkey, LinearMap.mem_ker.mp (hx ⟨N, _⟩), map_zero]
  have hGD := galoisDescent_holds K L V Kc hstab
  have hkP : kPoints Kc = W := by
    ext v
    rw [hWmem]
    show (1 : L) ⊗ₜ[K] v ∈ Kc ↔ _
    rw [Submodule.mem_iInf]
    constructor
    · intro h N
      have h1 := LinearMap.mem_ker.mp (h ⟨N, e0 N⟩)
      have h2 : e0 N (fi N v) = 0 := by
        have h3 := hgval N (e0 N) v
        rw [← h3]
        simpa [hgh1] using h1
      exact (e0 N).toRingHom.injective (by simpa using h2)
    · intro h p
      rw [LinearMap.mem_ker, hgh1, hgval p.1 p.2 v, h p.1, map_zero]
  have hKc : Kc = baseSpan L W := by rw [hGD, hkP]

  let G : Set (Module.Dual L (L ⊗[K] V)) := Set.range gh
  obtain ⟨t', ht'sub, ht'span, ht'li⟩ := exists_linearIndependent L G
  have ht'fin : t'.Finite := ht'li.setFinite
  have : Fintype t' := ht'fin.fintype
  set ρ := Fintype.card t' with hρ
  let eT := Fintype.equivFin t'
  have hpick : ∀ i : Fin ρ, ∃ p, gh p = (eT.symm i : Module.Dual L (L ⊗[K] V)) :=
    fun i => ht'sub (eT.symm i).2
  choose pk hpk using hpick
  let cfL : Fin ρ → Module.Dual L (L ⊗[K] V) := fun i => (eT.symm i : Module.Dual L (L ⊗[K] V))
  have hcomm : ∀ x : L ⊗[K] V, (∀ i, cfL i x = 0) ↔ x ∈ Kc := by
    intro x
    constructor
    · intro h
      rw [Submodule.mem_iInf]
      intro p
      rw [LinearMap.mem_ker]
      have hsp : Submodule.span L t' ≤ LinearMap.ker (Module.Dual.eval L (L ⊗[K] V) x) := by
        refine Submodule.span_le.mpr fun φ hφ => ?_
        have := h (eT ⟨φ, hφ⟩)
        simpa [cfL] using this
      have hmem : gh p ∈ Submodule.span L t' := ht'span ▸ Submodule.subset_span ⟨p, rfl⟩
      simpa using hsp hmem
    · intro hx i
      rw [Submodule.mem_iInf] at hx
      show (eT.symm i : Module.Dual L (L ⊗[K] V)) x = 0
      rw [← hpk i]
      exact LinearMap.mem_ker.mp (hx (pk i))
  have hcoan : (Submodule.span L t').dualCoannihilator = Kc := by
    ext x
    rw [Submodule.mem_dualCoannihilator, ← hcomm]
    constructor
    · intro h i
      exact h _ (Submodule.subset_span (eT.symm i).2)
    · intro h φ hφ
      have hsp : Submodule.span L t' ≤ LinearMap.ker (Module.Dual.eval L (L ⊗[K] V) x) := by
        refine Submodule.span_le.mpr fun ψ hψ => ?_
        have := h (eT ⟨ψ, hψ⟩)
        simpa [cfL] using this
      simpa using hsp hφ
  have hWfd : FiniteDimensional K W := inferInstance
  have hdim : Module.finrank K W + ρ = Module.finrank K V := by
    have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span L t')
    rw [hcoan, hKc, finrank_baseSpan L W, Module.finrank_baseChange] at h1
    have h2 : Module.finrank L (Submodule.span L t') = ρ := by
      rw [hρ, finrank_span_set_eq_card ht'li, Set.toFinset_card]
    omega
  refine ⟨L, inferInstance, hnfL, inferInstance, ρ, fun i => g (pk i).1 (pk i).2, cfL,
    fun i => hgfam _ _, fun i v => ?_, fun x => ?_, hdim⟩
  · rw [show cfL i = gh (pk i) from (hpk i).symm, hgh1]
  · rw [hcomm, hKc]

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
