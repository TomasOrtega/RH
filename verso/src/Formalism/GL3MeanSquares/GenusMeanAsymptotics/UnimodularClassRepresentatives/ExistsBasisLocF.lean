import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LocalSpans

variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

abbrev sF (K : Type) {F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] : Submonoid (𝓞 K) :=
  Algebra.algebraMapSubmonoid (𝓞 K) 𝔭.primeCompl

/- English proof (translation)
Establish `: {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s} = (sF K 𝔭 : Set (𝓞 K))`. Use extensionality with `s`. Both sides reduce to the same expression. Rewrite using `[this, Submonoid.closure_eq]`.
-/
theorem closure_eq (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] :
    Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s} = sF K 𝔭 := by
  have : {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s} = (sF K 𝔭 : Set (𝓞 K)) := by
    ext s
    rfl
  rw [this, Submonoid.closure_eq]

/- English proof (translation)
Unfold `locF`. Rewrite using `[closure_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, ⟨t, ht, rfl⟩, h⟩`. Conclude with `⟨t, ht, h⟩`.

Introduce and unpack `⟨t, ht, h⟩`. Conclude with `⟨_, ⟨t, ht, rfl⟩, h⟩`.
-/
theorem mem_locF {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime]
    (L : Submodule (𝓞 K) W) (x : W) :
    x ∈ locF 𝔭 L ↔ ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t • x ∈ L := by
  unfold locF
  rw [closure_eq]
  constructor
  · rintro ⟨s, ⟨t, ht, rfl⟩, h⟩
    exact ⟨t, ht, h⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨_, ⟨t, ht, rfl⟩, h⟩

/- English proof (translation)
The claim follows from `algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ 𝔭.primeCompl_le_nonZeroDivisors`.
-/
theorem sF_le (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] : sF K 𝔭 ≤ nonZeroDivisors (𝓞 K) :=
  algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ 𝔭.primeCompl_le_nonZeroDivisors

abbrev RP (K : Type) {F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K (sF K 𝔭) (sF_le 𝔭)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact (mem_locF 𝔭 N x).2 ⟨1, fun h => (Ideal.ne_top_iff_one 𝔭).1 (Ideal.IsPrime.ne_top inferInstance) h, by simpa using hx⟩`. Consider the case `zero => exact (locF 𝔭 N).zero_mem`.

Consider the case `add x y _ _ hx hy => exact (locF 𝔭 N).add_mem hx hy`. Consider the case `smul c x _ hx`. Take `⟨a, s, ⟨t, ht, rfl⟩, hc⟩` from `c.2`. Take `⟨u, hu, hx⟩` from `(mem_locF 𝔭 N x).1 hx`. Use `(mem_locF 𝔭 N _).2 ⟨t * u, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ht hu, ?_⟩` and prove the remaining obligations.

Establish `ht0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0`. Introduce `h0`. Establish `h1` using `(FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)`. Establish `h2` using `(FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm)`. Conclude with `ht (h2 ▸ 𝔭.zero_mem)`.

Establish `: algebraMap (𝓞 F) (𝓞 K) (t * u) • c • x = a • (algebraMap (𝓞 F) (𝓞 K) u • x)`. Rewrite using `[Subalgebra.smul_def, hc, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) (t * u)), ← algebraMap_smul K a, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) u), smul_smul, smul_smul, map_mul, map_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`.

Conclude with `N.smul_mem _ hx`. Introduce `hx`. Take `⟨t, ht, hx⟩` from `(mem_locF 𝔭 N x).1 hx`. Establish `ht0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0`. Introduce `h0`.

Establish `h1` using `(FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)`. Establish `h2` using `(FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm)`. Conclude with `ht (h2 ▸ 𝔭.zero_mem)`. Set `c : RP K 𝔭` to `⟨(algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹, ⟨1, _, ⟨t, ht, rfl⟩, by simp⟩⟩`. Establish `: x = c • (algebraMap (𝓞 F) (𝓞 K) t • x)`.

Rewrite using `[Subalgebra.smul_def, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t), smul_smul, inv_mul_cancel₀ ht0, one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hx)`.
-/
theorem mem_span_RP (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (N : Submodule (𝓞 K) V) (x : V) :
    x ∈ Submodule.span (RP K 𝔭) (N : Set V) ↔ x ∈ locF 𝔭 N := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact (mem_locF 𝔭 N x).2 ⟨1, fun h => (Ideal.ne_top_iff_one 𝔭).1 (Ideal.IsPrime.ne_top inferInstance) h, by simpa using hx⟩
    | zero => exact (locF 𝔭 N).zero_mem
    | add x y _ _ hx hy => exact (locF 𝔭 N).add_mem hx hy
    | smul c x _ hx =>
      obtain ⟨a, s, ⟨t, ht, rfl⟩, hc⟩ := c.2
      obtain ⟨u, hu, hx⟩ := (mem_locF 𝔭 N x).1 hx
      refine (mem_locF 𝔭 N _).2 ⟨t * u, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ht hu, ?_⟩
      have ht0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
        intro h0
        have h1 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)
        have h2 := (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm)
        exact ht (h2 ▸ 𝔭.zero_mem)
      have : algebraMap (𝓞 F) (𝓞 K) (t * u) • c • x = a • (algebraMap (𝓞 F) (𝓞 K) u • x) := by
        rw [Subalgebra.smul_def, hc, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) (t * u)),
          ← algebraMap_smul K a, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) u), smul_smul, smul_smul,
          map_mul, map_mul]
        congr 1
        field_simp
      rw [this]
      exact N.smul_mem _ hx
  · intro hx
    obtain ⟨t, ht, hx⟩ := (mem_locF 𝔭 N x).1 hx
    have ht0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
      intro h0
      have h1 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)
      have h2 := (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm)
      exact ht (h2 ▸ 𝔭.zero_mem)
    let c : RP K 𝔭 := ⟨(algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹,
      ⟨1, _, ⟨t, ht, rfl⟩, by simp⟩⟩
    have : x = c • (algebraMap (𝓞 F) (𝓞 K) t • x) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t), smul_smul,
        inv_mul_cancel₀ ht0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

/- English proof (translation)
Establish `: 𝔭.IsPrime` using `h𝔭.isPrime`. Establish `hp0 : 𝔭 ≠ ⊥` using `fun h => RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.2 (h ▸ h𝔭))`. Establish `: IsDedekindDomain (RP K 𝔭)` using `IsLocalization.isDedekindDomain (𝓞 K) (sF_le 𝔭) _`. Establish `: IsPrincipalIdealRing (RP K 𝔭)` using `IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 K) 𝔭 hp0`. Set `M : Submodule (RP K 𝔭) V` to `Submodule.span (RP K 𝔭) (L : Set V)`.

Establish `: Submodule.IsLattice K M` using `{ fg := by`. Take `⟨s, hs⟩` from `hL.fg`. Use `⟨s, ?_⟩` and prove the remaining obligations. Use `show _ = Submodule.span (RP K 𝔭) (L : Set V)`. Rewrite using `[← hs, Submodule.span_span_of_tower]`.

Use `span_eq_top := by`. Rewrite using `[eq_top_iff, ← hL.span_eq_top]`. Conclude with `Submodule.span_mono Submodule.subset_span }`. Set `b0` to `Module.Free.chooseBasis (RP K 𝔭) M`. Set `b1` to `b0.extendOfIsLattice K`.

Establish `hb1 : ∀ i, b1 i = (b0 i : V)` using `fun i => Basis.extendOfIsLattice_apply K b0 i`. Establish `hmem : ∀ i, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t • b1 i ∈ L` using `fun i => by`. Rewrite using `[← mem_locF, ← mem_span_RP, hb1]`. Conclude with `(b0 i).2`. Use `choose t ht htL using hmem`.

Establish `ht0 : ∀ i, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (t i)) ≠ 0`. Introduce `i h0`. Establish `h1` using `(FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)`. Establish `h2` using `(FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm)`. Conclude with `ht i (h2 ▸ 𝔭.zero_mem)`.

Set `b2` to `b1.unitsSMul fun i => Units.mk0 _ (ht0 i)`. Establish `hb2 : ∀ i, b2 i = algebraMap (𝓞 F) (𝓞 K) (t i) • b1 i` using `fun i => by`. Rewrite using `[Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, algebraMap_smul]`. Set `e` to `Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b2).symm`. Use `⟨b2.reindex e, fun i => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Basis.reindex_apply, hb2]`. Conclude with `htL _`. Use extensionality with `x`. Rewrite using `[← mem_span_RP, ← mem_span_RP, Submodule.span_span_of_tower, Basis.range_reindex]`. Establish `: Submodule.span (RP K 𝔭) (Set.range b2) = M`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[hb2]`. Conclude with `Submodule.subset_span (htL i)`.

Establish `h1 : M = Submodule.map M.subtype (Submodule.span (RP K 𝔭) (Set.range b0))`. Rewrite using `[b0.span_eq, Submodule.map_top, Submodule.range_subtype]`. Use `h1.le.trans ?_` and prove the remaining obligations. Rewrite using `[Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, rfl⟩`.

Set `c : RP K 𝔭` to `⟨(algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (t i)))⁻¹, ⟨1, _, ⟨t i, ht i, rfl⟩, by simp⟩⟩`. Establish `: M.subtype (b0 i) = c • b2 i`. Rewrite using `[hb2, Subalgebra.smul_def, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) (t i)), smul_smul, inv_mul_cancel₀ (ht0 i), one_smul, hb1]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite using `[this]`.
-/
theorem exists_basis_locF {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ b : Basis (Fin (finrank K V)) K V, (∀ i, b i ∈ L) ∧
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L := by
  have : 𝔭.IsPrime := h𝔭.isPrime
  have hp0 : 𝔭 ≠ ⊥ := fun h => RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.2 (h ▸ h𝔭))
  have : IsDedekindDomain (RP K 𝔭) := IsLocalization.isDedekindDomain (𝓞 K) (sF_le 𝔭) _
  have : IsPrincipalIdealRing (RP K 𝔭) :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 K) 𝔭 hp0
  let M : Submodule (RP K 𝔭) V := Submodule.span (RP K 𝔭) (L : Set V)
  have : Submodule.IsLattice K M :=
    { fg := by
        obtain ⟨s, hs⟩ := hL.fg
        refine ⟨s, ?_⟩
        show _ = Submodule.span (RP K 𝔭) (L : Set V)
        rw [← hs, Submodule.span_span_of_tower]
      span_eq_top := by
        rw [eq_top_iff, ← hL.span_eq_top]
        exact Submodule.span_mono Submodule.subset_span }
  let b0 := Module.Free.chooseBasis (RP K 𝔭) M
  let b1 := b0.extendOfIsLattice K
  have hb1 : ∀ i, b1 i = (b0 i : V) := fun i => Basis.extendOfIsLattice_apply K b0 i
  have hmem : ∀ i, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t • b1 i ∈ L := fun i => by
    rw [← mem_locF, ← mem_span_RP, hb1]
    exact (b0 i).2
  choose t ht htL using hmem
  have ht0 : ∀ i, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (t i)) ≠ 0 := by
    intro i h0
    have h1 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (h0.trans (map_zero _).symm)
    have h2 := (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)) (h1.trans (map_zero _).symm)
    exact ht i (h2 ▸ 𝔭.zero_mem)
  let b2 := b1.unitsSMul fun i => Units.mk0 _ (ht0 i)
  have hb2 : ∀ i, b2 i = algebraMap (𝓞 F) (𝓞 K) (t i) • b1 i := fun i => by
    rw [Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, algebraMap_smul]
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b2).symm
  refine ⟨b2.reindex e, fun i => ?_, ?_⟩
  · rw [Basis.reindex_apply, hb2]
    exact htL _
  · ext x
    rw [← mem_span_RP, ← mem_span_RP, Submodule.span_span_of_tower, Basis.range_reindex]
    have : Submodule.span (RP K 𝔭) (Set.range b2) = M := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        rw [hb2]
        exact Submodule.subset_span (htL i)
      · have h1 : M = Submodule.map M.subtype (Submodule.span (RP K 𝔭) (Set.range b0)) := by
          rw [b0.span_eq, Submodule.map_top, Submodule.range_subtype]
        refine h1.le.trans ?_
        rw [Submodule.map_span, Submodule.span_le]
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        let c : RP K 𝔭 := ⟨(algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (t i)))⁻¹,
          ⟨1, _, ⟨t i, ht i, rfl⟩, by simp⟩⟩
        have : M.subtype (b0 i) = c • b2 i := by
          rw [hb2, Subalgebra.smul_def, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) (t i)), smul_smul,
            inv_mul_cancel₀ (ht0 i), one_smul, hb1]
          rfl
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [this]

end Formalism.HermitianLattices.Ext.L3.LocalSpans
