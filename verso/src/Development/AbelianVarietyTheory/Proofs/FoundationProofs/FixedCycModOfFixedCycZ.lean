import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import ReciprocityTheory.GaloisValuations.Global
import GroundTheory.GlobalFields.CyclotomicCharacters.ProfinitePadic
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.KZ GlobalTheory.Glue

namespace GlobalTheory

/- English proof (translation)
Introduce `l _ Ω _ _ _ A _ F y hy`. Use `haveI : CompactSpace (G ℚ Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[ℚ] Ω))`. Use `haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic`. Use `set K : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ ({y} : Set Ω) with hK`. Establish `: FiniteDimensional ℚ K` using `IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic y).isIntegral`.

Establish `hSo : IsOpen (MulAction.stabilizer (G ℚ Ω) y : Set (G ℚ Ω))`. Use `Subgroup.isOpen_mono (H₁ := K.fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen K)` and prove the remaining obligations. Introduce `g hg`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff K g).mp hg y (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton y))`. Use `set S : Set (G ℚ Ω) := (MulAction.stabilizer (G ℚ Ω) y : Set (G ℚ Ω)) with hS`.

Establish `memS : ∀ s : G ℚ Ω, s ∈ S ↔ s y = y` using `fun s => Iff.rfl`. Use `set H0 : Set (G ℚ Ω) := (Ine (F := ℚ) A : Set (G ℚ Ω)) ∩ ⋂ z ∈ F, {s : G ℚ Ω | s z = z} with hH0`. Establish `hH0c : IsClosed H0` using `(isClosed_Ine A).inter (isClosed_biInter fun z _ => isClosed_setOf_apply z (fun t => t = z))`. Establish `hcm : ∀ (m : ℕ) (s : G ℚ Ω), cycMod ℚ Ω l m s = 1 ↔ PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1`. Introduce `m s`.

Rewrite using `[Units.ext_iff]`. Both sides reduce to the same expression. Use `set C : ℕ → Set (G ℚ Ω) := fun m => (H0 ∩ {s | PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1}) ∩ Sᶜ with hC`. Establish `hCc : ∀ m, IsClosed (C m)`. Introduce `m`.

Establish `hc : Continuous fun s : G ℚ Ω => PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])` using `(GroundTheory.Global.Cyclotomic.continuous_toZModPow m).comp (Units.continuous_val.comp (continuous_cycZ ℚ Ω l))`. Conclude with `(hH0c.inter ((isClosed_discrete ({1} : Set (ZMod (l ^ m)))).preimage hc)).inter hSo.isClosed_compl`. Establish `hmono : ∀ m k, m ≤ k → C k ⊆ C m`. Introduce `m k hmk s ⟨⟨h0, h1⟩, h2⟩`. Use `⟨⟨h0, ?_⟩, h2⟩` and prove the remaining obligations.

Simplify using `only [Set.mem_setOf_eq] at h1 ⊢`. Rewrite using `[← PadicInt.zmod_cast_comp_toZModPow m k hmk, RingHom.comp_apply, h1, map_one]`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hCn : ∀ m, (C m).Nonempty`.

Introduce `m`. Take `⟨s, ⟨hs1, hs2, hs3⟩, hs4⟩` from `hne m`. Use `⟨s, ⟨⟨hs1, ?_⟩, (hcm m s).mp hs3⟩, hs4⟩` and prove the remaining obligations. Simplify using `only [Set.mem_iInter, Set.mem_setOf_eq]`. Conclude with `hs2`.

Establish `hdir : Directed (· ⊇ ·) C` using `fun m k => ⟨max m k, hmono m _ (le_max_left m k), hmono k _ (le_max_right m k)⟩`. Take `⟨s, hs⟩` from `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hCn (fun m => (hCc m).isCompact) hCc`. Simplify using `only [Set.mem_iInter] at hs`. Take `⟨⟨h0i, h0f⟩, -⟩` from `(hs 0).1`. Establish `hz : cycZ ℚ Ω l s = 1`.

Use `Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)` and prove the remaining obligations. Rewrite using `[(hs n).1.2, Units.val_one, map_one]`. Simplify using `only [Set.mem_iInter, Set.mem_setOf_eq] at h0f`. Conclude with `(hs 0).2 ((memS s).mpr (hy s h0i h0f hz))`.
-/
theorem fixed_cycMod_of_fixed_cycZ : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ (F : Finset Ω) (y : Ω), (∀ s ∈ Ine (F := ℚ) A, (∀ z ∈ F, s z = z) → cycZ ℚ Ω l s = 1 → s y = y) →
  ∃ m : ℕ, ∀ s : G ℚ Ω, s ∈ Ine (F := ℚ) A ∧ (∀ z ∈ F, s z = z) ∧ cycMod ℚ Ω l m s = 1 → s y = y := by
  intro l _ Ω _ _ _ A _ F y hy
  haveI : CompactSpace (G ℚ Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[ℚ] Ω))
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic

  set K : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ ({y} : Set Ω) with hK
  have : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  have hSo : IsOpen (MulAction.stabilizer (G ℚ Ω) y : Set (G ℚ Ω)) := by
    refine Subgroup.isOpen_mono (H₁ := K.fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen K)
    intro g hg
    exact (IntermediateField.mem_fixingSubgroup_iff K g).mp hg y
      (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton y))
  set S : Set (G ℚ Ω) := (MulAction.stabilizer (G ℚ Ω) y : Set (G ℚ Ω)) with hS
  have memS : ∀ s : G ℚ Ω, s ∈ S ↔ s y = y := fun s => Iff.rfl
  set H0 : Set (G ℚ Ω) := (Ine (F := ℚ) A : Set (G ℚ Ω)) ∩ ⋂ z ∈ F, {s : G ℚ Ω | s z = z} with hH0
  have hH0c : IsClosed H0 :=
    (isClosed_Ine A).inter (isClosed_biInter fun z _ => isClosed_setOf_apply z (fun t => t = z))

  have hcm : ∀ (m : ℕ) (s : G ℚ Ω), cycMod ℚ Ω l m s = 1 ↔
      PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    intro m s; rw [Units.ext_iff]; rfl
  set C : ℕ → Set (G ℚ Ω) := fun m =>
    (H0 ∩ {s | PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1}) ∩ Sᶜ with hC
  have hCc : ∀ m, IsClosed (C m) := by
    intro m
    have hc : Continuous fun s : G ℚ Ω => PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
      (GroundTheory.Global.Cyclotomic.continuous_toZModPow m).comp
        (Units.continuous_val.comp (continuous_cycZ ℚ Ω l))
    exact (hH0c.inter ((isClosed_discrete ({1} : Set (ZMod (l ^ m)))).preimage hc)).inter
      hSo.isClosed_compl
  have hmono : ∀ m k, m ≤ k → C k ⊆ C m := by
    intro m k hmk s ⟨⟨h0, h1⟩, h2⟩
    refine ⟨⟨h0, ?_⟩, h2⟩
    simp only [Set.mem_setOf_eq] at h1 ⊢
    rw [← PadicInt.zmod_cast_comp_toZModPow m k hmk, RingHom.comp_apply, h1, map_one]
  by_contra hne
  push_neg at hne
  have hCn : ∀ m, (C m).Nonempty := by
    intro m
    obtain ⟨s, ⟨hs1, hs2, hs3⟩, hs4⟩ := hne m
    refine ⟨s, ⟨⟨hs1, ?_⟩, (hcm m s).mp hs3⟩, hs4⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact hs2
  have hdir : Directed (· ⊇ ·) C := fun m k =>
    ⟨max m k, hmono m _ (le_max_left m k), hmono k _ (le_max_right m k)⟩
  obtain ⟨s, hs⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hCn
    (fun m => (hCc m).isCompact) hCc
  simp only [Set.mem_iInter] at hs
  obtain ⟨⟨h0i, h0f⟩, -⟩ := (hs 0).1
  have hz : cycZ ℚ Ω l s = 1 := by
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [(hs n).1.2, Units.val_one, map_one]
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at h0f
  exact (hs 0).2 ((memS s).mpr (hy s h0i h0f hz))

end GlobalTheory
