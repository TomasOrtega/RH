import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

noncomputable section

namespace GlobalTheory.RepFinExtJoint

/- English proof (translation)
Simplify using `[GlobalTheory.TripleGal.rk1, Matrix.scalar_apply]`.
-/
theorem characterAsRankOneRep_entry {Γ K : Type} [Group Γ] [CommRing K] (χ : Γ →* Kˣ) (g : Γ) :
    ((GlobalTheory.TripleGal.rk1 χ g : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) 0 0 = ((χ g : Kˣ) : K) := by
  simp [GlobalTheory.TripleGal.rk1, Matrix.scalar_apply]

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on generalizing L₀ with`. Consider the case `empty => exact ⟨L₀, le_rfl, fun s hs => absurd hs (Finset.notMem_empty s)⟩`. Consider the case `insert i S hi ih`. Take `⟨L₁, h01, h1⟩` from `ih L₀`. Take `⟨L₂, h12, h2⟩` from `GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) 1 (GlobalTheory.TripleGal.rk1 (χ i)) (Units.continuous_val.comp (hχ i)) L₁`.

Use `⟨L₂, h01.trans h12, fun s hs g => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hs with rfl | hs` into its components or cases. Use `h2 g 0 0` as an intermediate fact. Rewrite `this` using `[characterAsRankOneRep_entry]`. Then use the resulting hypothesis. Conclude with `h12 (h1 s hs g)`.
-/
theorem exists_finExt_chars (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] {ι : Type} (χ : ι → G E Ω →* (PadicAlgCl l)ˣ)
    (hχ : ∀ s, Continuous (GlobalTheory.TripleGal.rk1 (χ s))) (S : Finset ι) (L₀ : FinExt l) :
    ∃ L : FinExt l, L₀.1 ≤ L.1 ∧ ∀ s ∈ S, ∀ g, ((χ s g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ∈ L.1 := by
  classical
  induction S using Finset.induction_on generalizing L₀ with
  | empty => exact ⟨L₀, le_rfl, fun s hs => absurd hs (Finset.notMem_empty s)⟩
  | insert i S hi ih =>
    obtain ⟨L₁, h01, h1⟩ := ih L₀
    obtain ⟨L₂, h12, h2⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) 1
      (GlobalTheory.TripleGal.rk1 (χ i)) (Units.continuous_val.comp (hχ i)) L₁
    refine ⟨L₂, h01.trans h12, fun s hs g => ?_⟩
    rcases Finset.mem_insert.1 hs with rfl | hs
    · have := h2 g 0 0
      rwa [characterAsRankOneRep_entry] at this
    · exact h12 (h1 s hs g)

/- English proof (translation)
Take `⟨ζ, hζ⟩ : ∃ ζ : PadicAlgCl l, IsPrimitiveRoot ζ l` from `HasEnoughRootsOfUnity.prim`. Set `b` to `Module.finBasis ℚ E`. Use `haveI : Fintype (E →+* PadicAlgCl l) := Fintype.ofFinite _`. Set `T : Finset (PadicAlgCl l)` to `insert ζ (Finset.univ.image fun p : (E →+* PadicAlgCl l) × Fin (Module.finrank ℚ E) => p.1 (b p.2))`. Set `K : IntermediateField ℚ_[l] (PadicAlgCl l)` to `IntermediateField.adjoin ℚ_[l] (T : Set (PadicAlgCl l))`.

Use `haveI : FiniteDimensional ℚ_[l] K := IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x`. Establish `hT : ∀ x ∈ T, x ∈ K` using `fun x hx => IntermediateField.subset_adjoin _ _ hx`. Use `⟨⟨K, inferInstance⟩, ⟨⟨ζ, hT _ (Finset.mem_insert_self _ _)⟩, ?_⟩, fun τ x => ?_⟩` and prove the remaining obligations. Conclude with `IsPrimitiveRoot.of_map_of_injective (f := K.val) (by simpa using hζ) K.val.injective`. Rewrite using `[← b.sum_repr x, map_sum]`.

Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_rat_smul]`. Conclude with `SubfieldClass.qsmul_mem K _ (hT _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(τ, i), Finset.mem_univ _, rfl⟩)))`.
-/
theorem exists_finExt_root_emb (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] :
    ∃ L : FinExt l, (∃ ζ : ↥L.1, IsPrimitiveRoot ζ l) ∧ ∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ L.1 := by
  classical
  obtain ⟨ζ, hζ⟩ : ∃ ζ : PadicAlgCl l, IsPrimitiveRoot ζ l := HasEnoughRootsOfUnity.prim
  let b := Module.finBasis ℚ E
  haveI : Fintype (E →+* PadicAlgCl l) := Fintype.ofFinite _
  let T : Finset (PadicAlgCl l) :=
    insert ζ (Finset.univ.image fun p : (E →+* PadicAlgCl l) × Fin (Module.finrank ℚ E) => p.1 (b p.2))
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] (T : Set (PadicAlgCl l))
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hT : ∀ x ∈ T, x ∈ K := fun x hx => IntermediateField.subset_adjoin _ _ hx
  refine ⟨⟨K, inferInstance⟩, ⟨⟨ζ, hT _ (Finset.mem_insert_self _ _)⟩, ?_⟩, fun τ x => ?_⟩
  · exact IsPrimitiveRoot.of_map_of_injective (f := K.val) (by simpa using hζ) K.val.injective
  · rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact SubfieldClass.qsmul_mem K _ (hT _ (Finset.mem_insert_of_mem
      (Finset.mem_image.2 ⟨(τ, i), Finset.mem_univ _, rfl⟩)))

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ l _ n a t r ρ χ hr hρ hχ`. Take `⟨L₀, ⟨ζ, hζ⟩, hemb⟩` from `exists_finExt_root_emb E l`. Take `⟨L₁, h01, h1⟩` from `GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) n r (Units.continuous_val.comp hr) L₀`. Take `⟨L₂, h12, h2⟩` from `GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) a ρ (Units.continuous_val.comp hρ) L₁`. Take `⟨L₃, h23, h3⟩` from `exists_finExt_chars E Ω l χ hχ Finset.univ L₂`.

Use `⟨L₃, ⟨⟨ζ, h23 (h12 (h01 ζ.2))⟩, ?_⟩, fun τ x => h23 (h12 (h01 (hemb τ x))), fun g i j => h23 (h12 (h1 g i j)), fun g i j => h23 (h2 g i j), fun s g => h3 s (Finset.mem_univ s) g⟩` and prove the remaining obligations. Establish `h0 : IsPrimitiveRoot ((ζ : ↥L₀.1) : PadicAlgCl l) l` using `hζ.map_of_injective (f := L₀.1.val) L₀.1.val.injective`. Conclude with `IsPrimitiveRoot.of_map_of_injective (f := L₃.1.val) h0 L₃.1.val.injective`.
-/
theorem finext_joint : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n a t : ℕ) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) (ρ : G E Ω →* GL (Fin a) (PadicAlgCl l)) (χ : Fin t → G E Ω →* (PadicAlgCl l)ˣ), Continuous r → Continuous ρ → (∀ s, Continuous (GlobalTheory.TripleGal.rk1 (χ s))) → ∃ LL : FinExt l, (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) ∧ (∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1) ∧ (∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) ∧ (∀ g i j, (ρ g : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j ∈ LL.1) ∧ ∀ s g, ((χ s g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ∈ LL.1 := by
  intro E Ω _ _ _ _ _ l _ n a t r ρ χ hr hρ hχ
  obtain ⟨L₀, ⟨ζ, hζ⟩, hemb⟩ := exists_finExt_root_emb E l
  obtain ⟨L₁, h01, h1⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) n r
    (Units.continuous_val.comp hr) L₀
  obtain ⟨L₂, h12, h2⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) a ρ
    (Units.continuous_val.comp hρ) L₁
  obtain ⟨L₃, h23, h3⟩ := exists_finExt_chars E Ω l χ hχ Finset.univ L₂
  refine ⟨L₃, ⟨⟨ζ, h23 (h12 (h01 ζ.2))⟩, ?_⟩, fun τ x => h23 (h12 (h01 (hemb τ x))),
    fun g i j => h23 (h12 (h1 g i j)), fun g i j => h23 (h2 g i j), fun s g => h3 s (Finset.mem_univ s) g⟩
  have h0 : IsPrimitiveRoot ((ζ : ↥L₀.1) : PadicAlgCl l) l :=
    hζ.map_of_injective (f := L₀.1.val) L₀.1.val.injective
  exact IsPrimitiveRoot.of_map_of_injective (f := L₃.1.val) h0 L₃.1.val.injective

end GlobalTheory.RepFinExtJoint
