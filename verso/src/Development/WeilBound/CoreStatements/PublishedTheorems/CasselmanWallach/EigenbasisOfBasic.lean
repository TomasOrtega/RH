import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace EigenspaceDecomposition

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

abbrev Es (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (μ : ℝ) : Submodule ℂ V :=
  Module.End.eigenspace (casimirK ε E) (μ : ℂ)

/- English proof (translation)
The claim follows from `Module.End.mem_eigenspace_iff`.
-/
theorem mem_Es {μ : ℝ} {v : V} : v ∈ Es ε E μ ↔ Eig ε E μ v :=
  Module.End.mem_eigenspace_iff

/- English proof (translation)
Use `haveI := h.fin μ`. Use `Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {v : V | ∃ μ' ≤ μ, Eig ε E μ' v}) ?_` and prove the remaining obligations. Introduce `v hv`. Conclude with `Submodule.subset_span ⟨μ, le_rfl, mem_Es.mp hv⟩`.
-/
theorem fd (h : Mod ε E) (μ : ℝ) : FiniteDimensional ℂ (Es ε E μ) := by
  haveI := h.fin μ
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {v : V | ∃ μ' ≤ μ, Eig ε E μ' v}) ?_
  intro v hv
  exact Submodule.subset_span ⟨μ, le_rfl, mem_Es.mp hv⟩

end EigenspaceDecomposition

open EigenspaceDecomposition in
/- English proof (translation)
Introduce `hA n ε V _ _ E h`. Take `⟨hsym, hnn, -, -⟩` from `hA n ε V E h`. Use `haveI : ∀ μ : ℝ, FiniteDimensional ℂ (Es ε E μ) := fun μ => fd h μ`. Set `f : (Σ μ : ℝ, Fin (Module.finrank ℂ (Es ε E μ))) → V` to `fun i => ((stdOrthonormalBasis ℂ (Es ε E i.1)) i.2 : V)`. Establish `hOF : OrthogonalFamily ℂ (fun μ : ℝ => Es ε E μ) (fun μ => (Es ε E μ).subtypeₗᵢ)` using `(LinearMap.IsSymmetric.orthogonalFamily_eigenspaces (T := casimirK ε E) hsym).comp (f := fun μ : ℝ => (μ : ℂ)) Complex.ofReal_injective`.

Establish `hon : Orthonormal ℂ f` using `hOF.orthonormal_sigma_orthonormal (fun μ => (stdOrthonormalBasis ℂ (Es ε E μ)).orthonormal)`. Establish `hli : LinearIndependent ℂ f` using `hon.linearIndependent`. Establish `hEs : ∀ μ : ℝ, ∀ v ∈ Es ε E μ, v ∈ Submodule.span ℂ (Set.range f)`. Introduce `μ v hv`. Establish `key` using `(stdOrthonormalBasis ℂ (Es ε E μ)).sum_repr ⟨v, hv⟩`.

Establish `hv' : v = ∑ i, ((stdOrthonormalBasis ℂ (Es ε E μ)).repr ⟨v, hv⟩ i) • ((stdOrthonormalBasis ℂ (Es ε E μ)) i : V)`. Use `congrArg Subtype.val key` as an intermediate fact. Rewrite `this` using `[Submodule.coe_sum]`. Simplify using `using this.symm`. Rewrite using `[hv']`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨μ, i⟩, rfl⟩)`. Establish `hsp : ⊤ ≤ Submodule.span ℂ (Set.range f)`. Rewrite using `[← h.span, Submodule.span_le]`. Introduce and unpack `v ⟨μ, hμ⟩`. Conclude with `hEs μ v (mem_Es.mpr hμ)`.

Establish `heig : ∀ i, Eig ε E i.1 (f i)` using `fun i => mem_Es.mp ((stdOrthonormalBasis ℂ (Es ε E i.1)) i.2).2`. Use `⟨_, Module.Basis.mk hli hsp, fun i => i.1, ?_⟩` and prove the remaining obligations. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using hon`. Introduce `i`.

Simplify using `using heig i`. Introduce `i`. Use `hnn i.1 (f i) (heig i) ?_` and prove the remaining obligations. Introduce `h0`. Use `hon.1 i` as an intermediate fact.

Rewrite `this` using `[h0, norm_zero]`. Conclude with `zero_ne_one this`. Introduce `R haveI := h.fin R`. Set `W` to `Submodule.span ℂ {v : V | ∃ μ ≤ R, Eig ε E μ v}`. Set `g : {i : (Σ μ : ℝ, Fin (Module.finrank ℂ (Es ε E μ))) | i.1 ≤ R} → W` to `fun i => ⟨f i.1, Submodule.subset_span ⟨i.1.1, i.2, heig i.1⟩⟩`.

Establish `hg : LinearIndependent ℂ g` using `LinearIndependent.of_comp W.subtype (hli.comp _ Subtype.val_injective)`. Use `haveI := hg.finite`. Conclude with `Set.toFinite _`.
-/
theorem eigenbasis_of_basic : A0 → EigenbasisExists := by
  intro hA n ε V _ _ E h
  obtain ⟨hsym, hnn, -, -⟩ := hA n ε V E h
  haveI : ∀ μ : ℝ, FiniteDimensional ℂ (Es ε E μ) := fun μ => fd h μ
  let f : (Σ μ : ℝ, Fin (Module.finrank ℂ (Es ε E μ))) → V :=
    fun i => ((stdOrthonormalBasis ℂ (Es ε E i.1)) i.2 : V)
  have hOF : OrthogonalFamily ℂ (fun μ : ℝ => Es ε E μ) (fun μ => (Es ε E μ).subtypeₗᵢ) :=
    (LinearMap.IsSymmetric.orthogonalFamily_eigenspaces (T := casimirK ε E) hsym).comp
      (f := fun μ : ℝ => (μ : ℂ)) Complex.ofReal_injective
  have hon : Orthonormal ℂ f :=
    hOF.orthonormal_sigma_orthonormal (fun μ => (stdOrthonormalBasis ℂ (Es ε E μ)).orthonormal)
  have hli : LinearIndependent ℂ f := hon.linearIndependent
  have hEs : ∀ μ : ℝ, ∀ v ∈ Es ε E μ, v ∈ Submodule.span ℂ (Set.range f) := by
    intro μ v hv
    have key := (stdOrthonormalBasis ℂ (Es ε E μ)).sum_repr ⟨v, hv⟩
    have hv' : v = ∑ i, ((stdOrthonormalBasis ℂ (Es ε E μ)).repr ⟨v, hv⟩ i) •
        ((stdOrthonormalBasis ℂ (Es ε E μ)) i : V) := by
      have := congrArg Subtype.val key
      rw [Submodule.coe_sum] at this
      simpa using this.symm
    rw [hv']
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨μ, i⟩, rfl⟩)
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range f) := by
    rw [← h.span, Submodule.span_le]
    rintro v ⟨μ, hμ⟩
    exact hEs μ v (mem_Es.mpr hμ)
  have heig : ∀ i, Eig ε E i.1 (f i) := fun i =>
    mem_Es.mp ((stdOrthonormalBasis ℂ (Es ε E i.1)) i.2).2
  refine ⟨_, Module.Basis.mk hli hsp, fun i => i.1, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hon
  · intro i
    simpa using heig i
  · intro i
    refine hnn i.1 (f i) (heig i) ?_
    intro h0
    have := hon.1 i
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  · intro R
    haveI := h.fin R
    let W := Submodule.span ℂ {v : V | ∃ μ ≤ R, Eig ε E μ v}
    let g : {i : (Σ μ : ℝ, Fin (Module.finrank ℂ (Es ε E μ))) | i.1 ≤ R} → W :=
      fun i => ⟨f i.1, Submodule.subset_span ⟨i.1.1, i.2, heig i.1⟩⟩
    have hg : LinearIndependent ℂ g :=
      LinearIndependent.of_comp W.subtype (hli.comp _ Subtype.val_injective)
    haveI := hg.finite
    exact Set.toFinite _

end PositivityTheory.CW

end
