import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

/- English proof (translation)
The claim follows from `(A.valuation_le_one_iff _).mpr (ReciprocityTheory.Gal.mem_of_isIntegral_int A (map_isIntegral_int (algebraMap L Ω) c.isIntegral_coe))`.
-/
private theorem coe_le_one {L Ω : Type} [Field Ω] [Field L] [NumberField L] [Algebra L Ω]
    (A : ValuationSubring Ω) (c : 𝓞 L) : A.valuation (algebraMap L Ω (c : L)) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr
    (ReciprocityTheory.Gal.mem_of_isIntegral_int A (map_isIntegral_int (algebraMap L Ω) c.isIntegral_coe))

/- English proof (translation)
Introduce `K L Ω _ _ _ _ _ _ _ _ _ _ _ A v h`. Set `m : Ideal (𝓞 L)` to `{ carrier := {y | A.valuation (algebraMap L Ω (y : L)) < 1} add_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq, map_add] at ha hb ⊢`. Conclude with `Valuation.map_add_lt _ ha hb`.

Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := by`. Introduce `c y hy`. Simplify using `only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at hy ⊢`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (coe_le_one A c)) hy }`.

Establish `hmem : ∀ y : 𝓞 L, y ∈ m ↔ A.valuation (algebraMap L Ω (y : L)) < 1` using `fun y => Iff.rfl`. Establish `hprime : m.IsPrime`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, Ideal.eq_top_iff_one, hmem]`. Simplify using the standard rewrite rules.

Introduce `x y hxy`. Rewrite `*` using `[hmem, hmem]`. Establish `e : ((x * y : 𝓞 L) : L) = (x : L) * y` using `rfl`. Rewrite `hxy` using `[e, map_mul, map_mul]`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `absurd hxy (not_lt.mpr (one_le_mul hc.1 hc.2))`. Establish `hK : ∀ x : 𝓞 K, (algebraMap (𝓞 K) (𝓞 L) x ∈ m ↔ x ∈ v.asIdeal)`. Introduce `x`. Rewrite using `[hmem, ← h x]`.

Establish `: algebraMap L Ω ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K Ω (x : K)`. Establish `e : ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K L (x : K)` using `rfl`. Rewrite using `[e, ← IsScalarTower.algebraMap_apply]`. Rewrite using `[this]`. Establish `hne : m ≠ ⊥`.

Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot`. Introduce `hb`. Establish `h1 : algebraMap (𝓞 K) (𝓞 L) x ∈ m` using `(hK x).mpr hx`. Rewrite `h1` using `[hb, Ideal.mem_bot]`. Apply `hx0` to reduce the goal to its premises.

Conclude with `(FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L)) (by rw [h1, map_zero])`. Use `⟨⟨m, hprime, hne⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `y`. Conclude with `(hmem y).symm.trans Iff.rfl`. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises.

Use extensionality with `x`. Conclude with `hK x`.
-/
theorem exists_isPlaceOver_of_tower : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v → ∃ v' : HeightOneSpectrum (𝓞 L), IsPlaceOver A v' ∧ v'.under (𝓞 K) = v := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v h
  let m : Ideal (𝓞 L) :=
    { carrier := {y | A.valuation (algebraMap L Ω (y : L)) < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
        exact Valuation.map_add_lt _ ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro c y hy
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at hy ⊢
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (coe_le_one A c)) hy }
  have hmem : ∀ y : 𝓞 L, y ∈ m ↔ A.valuation (algebraMap L Ω (y : L)) < 1 := fun y => Iff.rfl
  have hprime : m.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, hmem]; simp
    · intro x y hxy
      rw [hmem, hmem] at *
      have e : ((x * y : 𝓞 L) : L) = (x : L) * y := rfl
      rw [e, map_mul, map_mul] at hxy
      by_contra hc
      push_neg at hc
      exact absurd hxy (not_lt.mpr (one_le_mul hc.1 hc.2))
  have hK : ∀ x : 𝓞 K, (algebraMap (𝓞 K) (𝓞 L) x ∈ m ↔ x ∈ v.asIdeal) := by
    intro x
    rw [hmem, ← h x]
    have : algebraMap L Ω ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K Ω (x : K) := by
      have e : ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K L (x : K) := rfl
      rw [e, ← IsScalarTower.algebraMap_apply]
    rw [this]
  have hne : m ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    intro hb
    have h1 : algebraMap (𝓞 K) (𝓞 L) x ∈ m := (hK x).mpr hx
    rw [hb, Ideal.mem_bot] at h1
    apply hx0
    exact (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L)) (by rw [h1, map_zero])
  refine ⟨⟨m, hprime, hne⟩, ?_, ?_⟩
  · intro y
    exact (hmem y).symm.trans Iff.rfl
  · apply HeightOneSpectrum.ext
    ext x
    exact hK x

end GlobalTheory.AboveL
