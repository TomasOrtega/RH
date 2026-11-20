import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabel
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsStandardUnipotentRadicalBijOnNilradicalStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveExtendZeroOfSumUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.GreenCuspLabels.GreenCuspidal

noncomputable section

open GlobalTheory.SmGL GlobalTheory.Shin GlobalTheory.SplitWeil

namespace UpperTheory.Gal.InertialTypesAlt

/- English proof (translation)
Take `⟨⟨b, j⟩, hbj⟩ : ∃ p, (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd).symm i = p` from `⟨_, rfl⟩`. Establish `hi` using `stdBlocks_val (![a, m - a] : Fin 2 → ℕ) hd b j`. Rewrite `hi` using `[← hbj, Equiv.apply_symm_apply]`. Unfold `blk`. Rewrite using `[hbj]`.

Establish `hj` using `j.isLt`. Use `fin_cases b`. Simplify using `at hi hj ⊢`. Use linear arithmetic over natural numbers and integers. Simplify using `at hi hj ⊢`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem blk_two {m a : ℕ} (ha : a < m) (hd : ∑ b, (![a, m - a] : Fin 2 → ℕ) b = m) (i : Fin m) :
    (blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) i = 0 ↔ (i : ℕ) < a) := by
  obtain ⟨⟨b, j⟩, hbj⟩ : ∃ p, (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd).symm i = p := ⟨_, rfl⟩
  have hi := stdBlocks_val (![a, m - a] : Fin 2 → ℕ) hd b j
  rw [← hbj, Equiv.apply_symm_apply] at hi
  unfold blk
  rw [hbj]
  have hj := j.isLt
  fin_cases b
  · simp at hi hj ⊢
    omega
  · simp at hi hj ⊢
    omega

/- English proof (translation)
Establish `hi` using `blk_two ha hd i`. Establish `hj` using `blk_two ha hd j`. Establish `h1` using `(blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) i).isLt`. Establish `h2` using `(blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) j).isLt`. Rewrite using `[Fin.lt_iff_val_lt_val]`.

Rewrite `hi`, `hj` using `[Fin.ext_iff, Fin.val_zero]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem blk_lt_iff {m a : ℕ} (ha : a < m) (hd : ∑ b, (![a, m - a] : Fin 2 → ℕ) b = m) (i j : Fin m) :
    blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) i < blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) j ↔
      (i : ℕ) < a ∧ a ≤ (j : ℕ) := by
  have hi := blk_two ha hd i
  have hj := blk_two ha hd j
  have h1 := (blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) i).isLt
  have h2 := (blk (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) j).isLt
  rw [Fin.lt_iff_val_lt_val]
  rw [Fin.ext_iff, Fin.val_zero] at hi hj
  omega

/- English proof (translation)
Establish `hu'` using `GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries.mp hu`. Establish `hmem : u ∈ (H : Set (GL (Fin m) F))`. Rewrite using `[hH]`. Introduce `i j`. Distinguish the cases in `h : (i : ℕ) < a ∧ a ≤ (j : ℕ)`.

Conclude with `Or.inr h`. Use `left`. Rewrite using `[hu' i j (by rwa [blk_lt_iff ha hd])]`. Simplify using `[Matrix.one_apply]`. Conclude with `hmem`.
-/
private theorem rad_le {F : Type} [Field F] {m a : ℕ} (h0 : 0 < a) (ha : a < m) (H : Subgroup (GL (Fin m) F))
    (hH : (H : Set (GL (Fin m) F)) = {u : GL (Fin m) F | ∀ i j : Fin m, (u : Matrix (Fin m) (Fin m) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)})
    (hd : ∑ b, (![a, m - a] : Fin 2 → ℕ) b = m) (u : GL (Fin m) F)
    (hu : u ∈ unipRad F (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd)) : u ∈ H := by
  have hu' := GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries.mp hu
  have hmem : u ∈ (H : Set (GL (Fin m) F)) := by
    rw [hH]
    intro i j
    by_cases h : (i : ℕ) < a ∧ a ≤ (j : ℕ)
    · exact Or.inr h
    · left
      rw [hu' i j (by rwa [blk_lt_iff ha hd])]
      simp [Matrix.one_apply]
  exact hmem

/- English proof (translation)
Introduce `F _ _ θ hθ m hm W _ _ _ κ hirr hcusp`. Use `haveI : Fintype F := Fintype.ofFinite F`. Establish `hc` using `GlobalTheory.T.isCharacterOverSubfield_of_representation ℂ ℂ (GL (Fin m) F) W κ`. Establish `hprim : GlobalTheory.CuspGL.IsPrimitive (GlobalTheory.CuspGL.extZero (fun g : GL (Fin m) F => algebraMap ℂ ℂ (κ.character g)))`. Use `GlobalTheory.T.isPrimitive_extendZero_of_sum_unipotentRadical F m _ hc.1 fun a h0 ham => ?_` and prove the remaining obligations.

Take `⟨A, H, -, hH, -⟩` from `GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical F m a ham.le`. Establish `hd : ∑ b, (![a, m - a] : Fin 2 → ℕ) b = m`. Simplify using `[Fin.sum_univ_two]`. Use linear arithmetic over natural numbers and integers. Establish `hne : unipRad F (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) ≠ ⊥`.

Rewrite using `[GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff]`. Use `⟨⟨0, hm⟩, ⟨a, ham⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[blk_lt_iff ham hd]`. Conclude with `⟨h0, le_refl a⟩`. Establish `hfix : ∀ v : W, (∀ u ∈ H, κ u v = v) → v = 0` using `fun v hv => hcusp 2 _ _ hne v fun u hu => hv u (rad_le h0 ham H hH hd u hu)`.

Establish `hz` using `PositivityTheory.GreenCharacters.sum_char_eq_zero κ H hfix`. Rewrite using `[← hH, finsum_mem_def, finsum_eq_sum_of_fintype]`. Rewrite using `[← hz]`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hu : u ∈ H <;> simp [Set.indicator_apply, hu]`.

Take `⟨k, hk, hx⟩` from `GlobalTheory.CuspFormula.exists_regular F θ hθ m hm _ (hc.2 hirr) hprim`. Use `⟨k, hk, fun x => ?_⟩` and prove the remaining obligations. Use `hx x` as an intermediate fact. Simplify using `only [Algebra.algebraMap_self, RingHom.id_apply] at this`. Conclude with `this`.
-/
theorem cuspChar : CuspChar := by
  intro F _ _ θ hθ m hm W _ _ _ κ hirr hcusp
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hc := GlobalTheory.T.isCharacterOverSubfield_of_representation ℂ ℂ (GL (Fin m) F) W κ
  have hprim : GlobalTheory.CuspGL.IsPrimitive
      (GlobalTheory.CuspGL.extZero (fun g : GL (Fin m) F => algebraMap ℂ ℂ (κ.character g))) := by
    refine GlobalTheory.T.isPrimitive_extendZero_of_sum_unipotentRadical F m _ hc.1 fun a h0 ham => ?_
    obtain ⟨A, H, -, hH, -⟩ := GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical F m a ham.le
    have hd : ∑ b, (![a, m - a] : Fin 2 → ℕ) b = m := by
      simp [Fin.sum_univ_two]
      omega
    have hne : unipRad F (stdBlocks (![a, m - a] : Fin 2 → ℕ) hd) ≠ ⊥ := by
      rw [GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff]
      refine ⟨⟨0, hm⟩, ⟨a, ham⟩, ?_⟩
      rw [blk_lt_iff ham hd]
      exact ⟨h0, le_refl a⟩
    have hfix : ∀ v : W, (∀ u ∈ H, κ u v = v) → v = 0 := fun v hv =>
      hcusp 2 _ _ hne v fun u hu => hv u (rad_le h0 ham H hH hd u hu)
    have hz := PositivityTheory.GreenCharacters.sum_char_eq_zero κ H hfix
    rw [← hH, finsum_mem_def, finsum_eq_sum_of_fintype]
    rw [← hz]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u ∈ H <;> simp [Set.indicator_apply, hu]
  obtain ⟨k, hk, hx⟩ := GlobalTheory.CuspFormula.exists_regular F θ hθ m hm _ (hc.2 hirr) hprim
  refine ⟨k, hk, fun x => ?_⟩
  have := hx x
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at this
  exact this

end UpperTheory.Gal.InertialTypesAlt
