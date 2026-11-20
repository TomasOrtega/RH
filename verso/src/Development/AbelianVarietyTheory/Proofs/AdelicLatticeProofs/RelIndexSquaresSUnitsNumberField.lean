import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexSqsTopOfFgStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsNumberFieldFgStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinrankSUnitsNumberFieldAddOneStatement
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[Subgroup.mem_subgroupOf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, h⟩`. Conclude with `⟨⟨y, hy⟩, Subgroup.mem_top _, Subtype.ext h⟩`.

Introduce and unpack `⟨y, -, h⟩`. Conclude with `⟨y.1, y.2, congrArg Subtype.val h⟩`.
-/
theorem sqs_subgroupOf_self {G : Type} [CommGroup G] (U : Subgroup G) :
    (sqs U).subgroupOf U = sqs (⊤ : Subgroup U) := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨⟨y, hy⟩, Subgroup.mem_top _, Subtype.ext h⟩
  · rintro ⟨y, -, h⟩
    exact ⟨y.1, y.2, congrArg Subtype.val h⟩

/- English proof (translation)
Establish `hm : (-1 : Fˣ) ∈ sUnits F S`. Rewrite using `[mem_sUnits]`. Introduce `v _`. Simplify using the standard rewrite rules. Rewrite using `[Nat.card_eq_two_iff]`.

Use `⟨⟨1, by simp⟩, ⟨⟨-1, hm⟩, Subtype.ext (by simp)⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Establish `h1` using `congrArg (fun a : {a : sUnits F S // a ^ 2 = 1} => ((a.1.1 : Fˣ) : F)) h`. Simplify using `only [OneMemClass.coe_one, Units.val_one, Units.val_neg] at h1`. Evaluate the numerical expressions using `at h1`.

Rewrite using `[Set.eq_univ_iff_forall]`. Introduce and unpack `⟨⟨a, ha⟩, h⟩`. Establish `h1 : (a : F) ^ 2 = 1`. Use `congrArg (fun a : sUnits F S => ((a.1 : Fˣ) : F)) h` as an intermediate fact. Simplify using `using this`.

Break down `sq_eq_one_iff.mp h1 with h2 | h2` into its components or cases. Use `left`. Conclude with `Subtype.ext (Subtype.ext (Units.ext h2))`. Use `right`. Conclude with `Subtype.ext (Subtype.ext (Units.ext h2))`.
-/
theorem card_sq_eq_one_sUnits (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Nat.card {a : sUnits F S // a ^ 2 = 1} = 2 := by
  have hm : (-1 : Fˣ) ∈ sUnits F S := by
    rw [mem_sUnits]; intro v _; simp
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, by simp⟩, ⟨⟨-1, hm⟩, Subtype.ext (by simp)⟩, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun a : {a : sUnits F S // a ^ 2 = 1} => ((a.1.1 : Fˣ) : F)) h
    simp only [OneMemClass.coe_one, Units.val_one, Units.val_neg] at h1
    norm_num at h1
  · rw [Set.eq_univ_iff_forall]
    rintro ⟨⟨a, ha⟩, h⟩
    have h1 : (a : F) ^ 2 = 1 := by
      have := congrArg (fun a : sUnits F S => ((a.1 : Fˣ) : F)) h
      simpa using this
    rcases sq_eq_one_iff.mp h1 with h2 | h2
    · left
      exact Subtype.ext (Subtype.ext (Units.ext h2))
    · right
      exact Subtype.ext (Subtype.ext (Units.ext h2))

/- English proof (translation)
Introduce `F _ _ S`. Use `haveI := GlobalTheory.T.sUnitsNumberField_fg F S`. Rewrite using `[Subgroup.relIndex, sqs_subgroupOf_self, GlobalTheory.T.index_sqs_of_fg, card_sq_eq_one_sUnits, ← GlobalTheory.T.finrank_sUnitsNumberField_add_one F S, pow_succ]`.
-/
theorem relIndex_sqs_sUnits : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), (sqs (sUnits F S)).relIndex (sUnits F S) = 2 ^ (S.card + Fintype.card (InfinitePlace F)) := by
  intro F _ _ S
  haveI := GlobalTheory.T.sUnitsNumberField_fg F S
  rw [Subgroup.relIndex, sqs_subgroupOf_self, GlobalTheory.T.index_sqs_of_fg, card_sq_eq_one_sUnits,
    ← GlobalTheory.T.finrank_sUnitsNumberField_add_one F S, pow_succ]

end GlobalTheory.QNorm
