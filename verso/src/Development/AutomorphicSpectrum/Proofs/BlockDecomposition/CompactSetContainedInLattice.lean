import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

namespace GlobalTheory.CompanionTheory.AvgFree

/- English proof (translation)
Take `⟨t, ht⟩` from `hC.elim_finite_subcover (fun x : K => (fun y => y - x) ⁻¹' (O : Set K)) (fun x => hOo.preimage (continuous_id.sub continuous_const)) (fun x _ => Set.mem_iUnion.2 ⟨x, by simpa using O.zero_mem⟩)`. Set `s : Finset K` to `insert 1 t`. Set `L : Submodule O K` to `Submodule.span O (s : Set K)`. Establish `h1 : (1 : K) ∈ L` using `Submodule.subset_span (by simp [s])`. Establish `hO : ∀ a ∈ O, a ∈ L` using `fun a ha => by`.

Use `L.smul_mem (⟨a, ha⟩ : O) h1` as an intermediate fact. Simplify `this` using `[Subring.smul_def]`. Use `⟨L, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `haveI : CompactSpace O := isCompact_iff_compactSpace.1 hOc`. Establish `hr : (L : Set K) = Set.range (fun c : s → O => ∑ i, (c i : K) * (i : K))`.

Use extensionality with `x`. Establish `hs : (s : Set K) = Set.range (Subtype.val : s → K)` using `by simp`. Express the relevant statement in the definitionally equal form `x ∈ Submodule.span O (s : Set K) ↔ _`. Rewrite using `[hs, Submodule.mem_span_range_iff_exists_fun]`. Both sides reduce to the same expression.

Rewrite using `[hr]`. Use `isCompact_range ?_` and prove the remaining obligations. Use `fun_prop`. Establish `hopen : IsOpen ((L.toAddSubgroup : AddSubgroup K) : Set K)`. Use `AddSubgroup.isOpen_mono (H₁ := O.toAddSubgroup) (fun a ha => hO a ha) hOo` and prove the remaining obligations.

Conclude with `hopen`. Introduce `x hx`. Take `⟨y, hy, hxy⟩` from `Set.mem_iUnion₂.1 (ht hx)`. Establish `hyL : y ∈ L` using `Submodule.subset_span (by simp [s, hy])`. Establish `: x = (x - y) + y` using `by ring`.

Rewrite using `[this]`. Conclude with `L.add_mem (hO _ hxy) hyL`.
-/
theorem exists_lattice_of_compact {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (O : Subring K) (hOc : IsCompact (O : Set K)) (hOo : IsOpen (O : Set K)) {C : Set K} (hC : IsCompact C) :
    ∃ L : Submodule O K, IsCompact (L : Set K) ∧ IsOpen (L : Set K) ∧ C ⊆ (L : Set K) := by
  classical
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x : K => (fun y => y - x) ⁻¹' (O : Set K))
    (fun x => hOo.preimage (continuous_id.sub continuous_const))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simpa using O.zero_mem⟩)
  let s : Finset K := insert 1 t
  let L : Submodule O K := Submodule.span O (s : Set K)
  have h1 : (1 : K) ∈ L := Submodule.subset_span (by simp [s])
  have hO : ∀ a ∈ O, a ∈ L := fun a ha => by
    have := L.smul_mem (⟨a, ha⟩ : O) h1
    simpa [Subring.smul_def] using this
  refine ⟨L, ?_, ?_, ?_⟩
  · haveI : CompactSpace O := isCompact_iff_compactSpace.1 hOc
    have hr : (L : Set K) = Set.range (fun c : s → O => ∑ i, (c i : K) * (i : K)) := by
      ext x
      have hs : (s : Set K) = Set.range (Subtype.val : s → K) := by simp
      change x ∈ Submodule.span O (s : Set K) ↔ _
      rw [hs, Submodule.mem_span_range_iff_exists_fun]
      rfl
    rw [hr]
    refine isCompact_range ?_
    fun_prop
  · have hopen : IsOpen ((L.toAddSubgroup : AddSubgroup K) : Set K) := by
      refine AddSubgroup.isOpen_mono (H₁ := O.toAddSubgroup) (fun a ha => hO a ha) hOo
    exact hopen
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    have hyL : y ∈ L := Submodule.subset_span (by simp [s, hy])
    have : x = (x - y) + y := by ring
    rw [this]
    exact L.add_mem (hO _ hxy) hyL

end GlobalTheory.CompanionTheory.AvgFree

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ v O hOc hOo n M A hA`. Take `⟨r1, r2, r3, r4, -⟩` from `GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v`. Use `haveI := r1`. Use `haveI := r2`. Use `haveI := r3`.

Use `haveI := r4`. Take `⟨a1, -⟩` from `GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)`. Use `haveI := a1`. Establish `hC : IsCompact (⋃ i : Fin n, ⋃ k : Fin M, (fun X : Fin n → Fin M → Fv F v ⊗[F] E => X i k) '' A)` using `isCompact_iUnion fun i => isCompact_iUnion fun k => hA.image (by fun_prop)`. Take `⟨L, h1, h2, h3⟩` from `exists_lattice_of_compact O hOc hOo hC`.

Use `⟨L, h1, h2, fun X hX i k => h3 ?_⟩` and prove the remaining obligations. Conclude with `Set.mem_iUnion₂.2 ⟨i, k, X, hX, rfl⟩`.
-/
theorem GlobalTheory.CompanionTheory.AvgFree.exists_lattice_tupIn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (O : Subring (Fv F v ⊗[F] E)), IsCompact (O : Set (Fv F v ⊗[F] E)) → IsOpen (O : Set (Fv F v ⊗[F] E)) → ∀ (n M : ℕ) (A : Set (Fin n → Fin M → (Fv F v ⊗[F] E))), IsCompact A → ∃ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) ∧ IsOpen (L : Set (Fv F v ⊗[F] E)) ∧ A ⊆ tupIn (Fv F v) (L : Set (Fv F v ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hσ v O hOc hOo n M A hA
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  obtain ⟨a1, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  have hC : IsCompact (⋃ i : Fin n, ⋃ k : Fin M, (fun X : Fin n → Fin M → Fv F v ⊗[F] E => X i k) '' A) :=
    isCompact_iUnion fun i => isCompact_iUnion fun k => hA.image (by fun_prop)
  obtain ⟨L, h1, h2, h3⟩ := exists_lattice_of_compact O hOc hOo hC
  refine ⟨L, h1, h2, fun X hX i k => h3 ?_⟩
  exact Set.mem_iUnion₂.2 ⟨i, k, X, hX, rfl⟩
