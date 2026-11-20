import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.QLTop

open ValuativeRel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Set `` to `IsTopologicalAddGroup.rightUniformSpace k`. Use `isUniformAddGroup_of_addCommGroup (G := k)` as an intermediate fact. Set `: (Valued.v (R` to `k)).RankOne :=`. Use the proof step `{ hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding strictMono' := IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }`. Use `open scoped Valued in`.

Establish `: ProperSpace k` using `.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k`. Conclude with `⟨secondCountable_of_proper, inferInstance⟩`.
-/
theorem nonarchimedeanLocalField_secondCountable_t2Space (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SecondCountableTopology k ∧ T2Space k := by
  let := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  let : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  exact ⟨secondCountable_of_proper, inferInstance⟩

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `Valuation.isOpen_valuationSubring (valuation F)`. Conclude with `isCompact_iff_compactSpace.2 (inferInstance : CompactSpace 𝒪[F])`.
-/
theorem isOpen_isCompact_integers : IsOpen ((𝒪[F] : Subring F) : Set F) ∧ IsCompact ((𝒪[F] : Subring F) : Set F) := by
  refine ⟨?_, ?_⟩
  · exact Valuation.isOpen_valuationSubring (valuation F)
  · exact isCompact_iff_compactSpace.2 (inferInstance : CompactSpace 𝒪[F])

def intSet (O : Subring F) (n : ℕ) : Set (Matrix (Fin n) (Fin n) F) := {M | IsInt O M}

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/- English proof (translation)
Establish `: intSet O n = ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) F => M i j) ⁻¹' (O : Set F)`. Use extensionality with `M`. Simplify using `[intSet, IsInt]`. Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage ((continuous_apply j).comp (continuous_apply i))`.
-/
theorem isOpen_intSet {O : Subring F} (hO : IsOpen (O : Set F)) (n : ℕ) : IsOpen (intSet O n) := by
  have : intSet O n = ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) F => M i j) ⁻¹' (O : Set F) := by
    ext M; simp [intSet, IsInt]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    hO.preimage ((continuous_apply j).comp (continuous_apply i))

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/- English proof (translation)
Establish `: intSet O n = Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => (O : Set F)`. Use extensionality with `M`. Conclude with `⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩`. Rewrite using `[this]`. Conclude with `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hO`.
-/
theorem isCompact_intSet {O : Subring F} (hO : IsCompact (O : Set F)) (n : ℕ) : IsCompact (intSet O n) := by
  have : intSet O n = Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => (O : Set F) := by
    ext M
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hO

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/- English proof (translation)
Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, ⟨_, h2, rfl⟩⟩`. Introduce and unpack `⟨h1, ⟨y, hy, he⟩⟩`.

Establish `hy' : y = ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)` using `MulOpposite.op_injective he`. Conclude with `⟨h1, hy' ▸ hy⟩`.
-/
theorem GLint_eq_preimage (O : Subring F) (n : ℕ) :
    (GLint O n : Set (GL (Fin n) F)) =
      Units.embedProduct (Matrix (Fin n) (Fin n) F) ⁻¹' (intSet O n ×ˢ (MulOpposite.op '' intSet O n)) := by
  ext g
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, ⟨_, h2, rfl⟩⟩
  · rintro ⟨h1, ⟨y, hy, he⟩⟩
    have hy' : y = ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := MulOpposite.op_injective he
    exact ⟨h1, hy' ▸ hy⟩

/- English proof (translation)
Introduce `F _ _ _ _ O ϖ nrm q h n`. Take `⟨hsc, ht2⟩` from `nonarchimedeanLocalField_secondCountable_t2Space F`. Choose the witnesses or unpack the hypotheses as in `⟨hOo, hOc⟩ : IsOpen (O : Set F) ∧ IsCompact (O : Set F) := by`. Rewrite using `[h.O_eq]`. Conclude with `isOpen_isCompact_integers`.

Establish `: T2Space (Matrix (Fin n) (Fin n) F)` using `inferInstanceAs (T2Space (Fin n → Fin n → F))`. Establish `: SecondCountableTopology (Matrix (Fin n) (Fin n) F)` using `inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F))`. Establish `: LocallyCompactSpace (Matrix (Fin n) (Fin n) F)` using `inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → F))`. Establish `: SecondCountableTopology (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ` using `(MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) F)).symm.isEmbedding.secondCountableTopology`. Establish `hSo` using `isOpen_intSet hOo n`.

Establish `hSc` using `isCompact_intSet hOc n`. Establish `hemb` using `Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)`. Establish `hMint : Mint O n = Units.val ⁻¹' intSet O n` using `rfl`. Use `⟨?_, ?_, hemb.locallyCompactSpace, hemb.isEmbedding.secondCountableTopology, inferInstance, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[GLint_eq_preimage]`.

Conclude with `(hSo.prod (MulOpposite.opHomeomorph.isOpenMap _ hSo)).preimage hemb.continuous`. Rewrite using `[GLint_eq_preimage]`. Conclude with `hemb.isCompact_preimage (hSc.prod (hSc.image MulOpposite.continuous_op))`. Rewrite using `[hMint]`. Conclude with `hSo.preimage Units.continuous_val`.

Rewrite using `[hMint]`. Conclude with `hSc.isClosed.preimage Units.continuous_val`.
-/
theorem gl_topology : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n : ℕ,
    IsOpen (GLint O n : Set (GL (Fin n) F)) ∧ IsCompact (GLint O n : Set (GL (Fin n) F)) ∧
    LocallyCompactSpace (GL (Fin n) F) ∧ SecondCountableTopology (GL (Fin n) F) ∧ T2Space (GL (Fin n) F) ∧
    IsOpen (Mint O n) ∧ IsClosed (Mint O n) := by
  intro F _ _ _ _ O ϖ nrm q h n
  obtain ⟨hsc, ht2⟩ := nonarchimedeanLocalField_secondCountable_t2Space F
  obtain ⟨hOo, hOc⟩ : IsOpen (O : Set F) ∧ IsCompact (O : Set F) := by
    rw [h.O_eq]; exact isOpen_isCompact_integers
  have : T2Space (Matrix (Fin n) (Fin n) F) := inferInstanceAs (T2Space (Fin n → Fin n → F))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F))
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → F))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) F)).symm.isEmbedding.secondCountableTopology
  have hSo := isOpen_intSet hOo n
  have hSc := isCompact_intSet hOc n
  have hemb := Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)
  have hMint : Mint O n = Units.val ⁻¹' intSet O n := rfl
  refine ⟨?_, ?_, hemb.locallyCompactSpace, hemb.isEmbedding.secondCountableTopology, inferInstance, ?_, ?_⟩
  · rw [GLint_eq_preimage]
    exact (hSo.prod (MulOpposite.opHomeomorph.isOpenMap _ hSo)).preimage hemb.continuous
  · rw [GLint_eq_preimage]
    exact hemb.isCompact_preimage (hSc.prod (hSc.image MulOpposite.continuous_op))
  · rw [hMint]; exact hSo.preimage Units.continuous_val
  · rw [hMint]; exact hSc.isClosed.preimage Units.continuous_val

end GlobalTheory.CompanionTheory.QLTop
