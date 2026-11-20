import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelCore

noncomputable section

open NumberField

namespace Formalism.L2.S.Pv.DdTraceCore

/- English proof (translation)
Establish `hD : ((differentIdeal ℤ (𝓞 F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot`. Rewrite using `[FractionalIdeal.mem_inv_iff hD]`. Introduce `x hx`. Take `⟨d, hd, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).mp hx`. Take `⟨a, ha⟩` from `hy d hd`.

Rewrite using `[FractionalIdeal.mem_one_iff]`. Establish `key : Algebra.trace F E ((o : E) * y) * algebraMap (𝓞 F) F d = Algebra.trace F E (algebraMap (𝓞 E) E (o * a))`. Rewrite using `[map_mul (algebraMap (𝓞 E) E), ha]`. Express the relevant statement in the definitionally equal form `_ = Algebra.trace F E ((o : E) * (y * algebraMap F E (d : F)))`. Rewrite using `[← mul_assoc]`.

Generalize the expression as in `(o : E) * y = z`. Establish `h` using `(Algebra.trace F E).map_smul (d : F) z`. Rewrite `h` using `[Algebra.smul_def, smul_eq_mul]`. Rewrite using `[mul_comm z, h, mul_comm]`. Establish `hint : IsIntegral ℤ (Algebra.trace F E (algebraMap (𝓞 E) E (o * a)))` using `Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe (o * a))`.

Conclude with `⟨⟨_, hint⟩, key.symm⟩`.
-/
theorem relTrace_mem_inv_different (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (y : E)
    (hy : ∀ d ∈ differentIdeal ℤ (𝓞 F), ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = y * algebraMap F E (d : F))
    (o : 𝓞 E) :
    Algebra.trace F E ((o : E) * y) ∈
      ((differentIdeal ℤ (𝓞 F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F))⁻¹ := by
  have hD : ((differentIdeal ℤ (𝓞 F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot
  rw [FractionalIdeal.mem_inv_iff hD]
  intro x hx
  obtain ⟨d, hd, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hx
  obtain ⟨a, ha⟩ := hy d hd
  rw [FractionalIdeal.mem_one_iff]
  have key : Algebra.trace F E ((o : E) * y) * algebraMap (𝓞 F) F d =
      Algebra.trace F E (algebraMap (𝓞 E) E (o * a)) := by
    rw [map_mul (algebraMap (𝓞 E) E), ha]
    change _ = Algebra.trace F E ((o : E) * (y * algebraMap F E (d : F)))
    rw [← mul_assoc]
    generalize (o : E) * y = z
    have h := (Algebra.trace F E).map_smul (d : F) z
    rw [Algebra.smul_def, smul_eq_mul] at h
    rw [mul_comm z, h, mul_comm]
  have hint : IsIntegral ℤ (Algebra.trace F E (algebraMap (𝓞 E) E (o * a))) :=
    Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe (o * a))
  exact ⟨⟨_, hint⟩, key.symm⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ y hy o`. Establish `hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E))` using `FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)`. Establish `hne : ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F)) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0`. Rewrite using `[FractionalIdeal.coeIdeal_ne_zero, ne_eq, Ideal.map_eq_bot_iff_of_injective hinj]`. Conclude with `differentIdeal_ne_bot`.

Establish `hyF : ∀ d ∈ differentIdeal ℤ (𝓞 F), ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = y * algebraMap F E (d : F)`. Introduce `d hd`. Establish `hmem : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) d) ∈ ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F)) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)` using `(FractionalIdeal.mem_coeIdeal _).mpr ⟨_, Ideal.mem_map_of_mem _ hd, rfl⟩`. Take `⟨a, ha⟩` from `(FractionalIdeal.mem_one_iff _).mp ((FractionalIdeal.mem_inv_iff hne).mp hy _ hmem)`. Conclude with `⟨a, ha⟩`.

Establish `h1` using `relTrace_mem_inv_different F E y hyF o`. Establish `h10 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0` using `@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 F)) F) _ _ _`. Rewrite `h1` using `[coeIdeal_differentIdeal (K := ℚ), inv_inv, FractionalIdeal.mem_dual h10]`. Take `⟨m, hm⟩` from `h1 1 (FractionalIdeal.one_mem_one _)`. Use `⟨m, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Algebra.trace_trace (S := F)]`. Rewrite `hm` using `[Algebra.traceForm_apply, mul_one]`. Rewrite using `[← hm]`. Both sides reduce to the same expression.
-/
theorem ddTraceCore_holds : Formalism.L2.SG.Pf.DdTraceCore := by
  intro F E _ _ _ _ _ y hy o
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)
  have hne : ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F)) :
      Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
    rw [FractionalIdeal.coeIdeal_ne_zero, ne_eq, Ideal.map_eq_bot_iff_of_injective hinj]
    exact differentIdeal_ne_bot
  have hyF : ∀ d ∈ differentIdeal ℤ (𝓞 F),
      ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = y * algebraMap F E (d : F) := by
    intro d hd
    have hmem : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) d) ∈
        ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F)) :
          Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
      (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, Ideal.mem_map_of_mem _ hd, rfl⟩
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp ((FractionalIdeal.mem_inv_iff hne).mp hy _ hmem)
    exact ⟨a, ha⟩
  have h1 := relTrace_mem_inv_different F E y hyF o
  have h10 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
    @one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 F)) F) _ _ _
  rw [coeIdeal_differentIdeal (K := ℚ), inv_inv, FractionalIdeal.mem_dual h10] at h1
  obtain ⟨m, hm⟩ := h1 1 (FractionalIdeal.one_mem_one _)
  refine ⟨m, ?_⟩
  rw [← Algebra.trace_trace (S := F)]
  rw [Algebra.traceForm_apply, mul_one] at hm
  rw [← hm]
  rfl

end Formalism.L2.S.Pv.DdTraceCore
