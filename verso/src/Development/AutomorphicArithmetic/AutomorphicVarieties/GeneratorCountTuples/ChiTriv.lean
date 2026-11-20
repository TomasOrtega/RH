import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.Bridge
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.TateLimit UpperTheory.V UpperTheory.V.Kum UpperTheory.V.K

/- English proof (translation)
Introduce `l hl L Ω _ _ _ _ _ D hμ g`. Choose the witnesses or unpack the hypotheses as in `⟨ζ, hζ⟩ : ∃ ζ : L, IsPrimitiveRoot ζ (l ^ 1) := by`. Take `⟨ζ, hζ⟩` from `hμ`. Rewrite using `[pow_one]`. Distinguish the cases in `h2 : l = 2`.

Rewrite `hζ` using `[if_pos h2]`. Conclude with `⟨ζ ^ 2, hζ.pow (by norm_num) (by rw [h2])⟩`. Rewrite `hζ` using `[if_neg h2]`. Conclude with `⟨ζ, hζ⟩`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed L`.

Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective`. Use `haveI : NeZero l := ⟨hl.out.ne_zero⟩`. Use `haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance`. Establish `hζ' : IsPrimitiveRoot (algebraMap L Ω ζ) (l ^ 1)` using `hζ.map_of_injective (algebraMap L Ω).injective`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective g`.

Establish `hc : D.chi (QuotientGroup.mk g) = cyclotomicCharacter Ω l g.toRingEquiv` using `DFunLike.congr_fun D.hchi g`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[redChar_coe, hc, Units.val_one, cyclotomicCharacter.toZModPow]`. Use `(modularCyclotomicCharacter.unique Ω _ _ fun t ht => ?_).symm` and prove the remaining obligations. Establish `ht' : (t : Ω) ^ l ^ 1 = 1`.

Rewrite using `[← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ht, Units.val_one]`. Rewrite using `[ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ ht', pow_one]`. Take `⟨i, -, hi⟩` from `hζ'.eq_pow_of_pow_eq_one ht'`. Rewrite using `[← hi, ← map_pow]`. Conclude with `g.commutes _`.
-/
theorem UpperTheory.V.K.chiTriv :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (D : LData L Ω l), HasMuQ l L → ∀ g, redChar D.chi 1 g = 1 := by
  intro l hl L Ω _ _ _ _ _ D hμ g
  obtain ⟨ζ, hζ⟩ : ∃ ζ : L, IsPrimitiveRoot ζ (l ^ 1) := by
    obtain ⟨ζ, hζ⟩ := hμ
    rw [pow_one]
    by_cases h2 : l = 2
    · rw [if_pos h2] at hζ
      exact ⟨ζ ^ 2, hζ.pow (by norm_num) (by rw [h2])⟩
    · rw [if_neg h2] at hζ
      exact ⟨ζ, hζ⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed L
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have hζ' : IsPrimitiveRoot (algebraMap L Ω ζ) (l ^ 1) := hζ.map_of_injective (algebraMap L Ω).injective
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  have hc : D.chi (QuotientGroup.mk g) = cyclotomicCharacter Ω l g.toRingEquiv := DFunLike.congr_fun D.hchi g
  apply Units.ext
  rw [redChar_coe, hc, Units.val_one, cyclotomicCharacter.toZModPow]
  refine (modularCyclotomicCharacter.unique Ω _ _ fun t ht => ?_).symm
  have ht' : (t : Ω) ^ l ^ 1 = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ht, Units.val_one]
  rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ ht', pow_one]
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one ht'
  rw [← hi, ← map_pow]
  exact g.commutes _
