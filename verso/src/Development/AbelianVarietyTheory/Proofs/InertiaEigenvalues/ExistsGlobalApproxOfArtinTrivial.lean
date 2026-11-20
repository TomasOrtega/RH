import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ArtinApprox

open Neutral.B1 GlobalTheory.HeckeGal

/- English proof (translation)
The claim follows from `RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _) (p := fun v => v ≠ w)`.
-/
theorem isOpen_integers_away {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    IsOpen {f : FiniteAdeleRing (𝓞 E) E | ∀ v, v ≠ w → f v ∈ v.adicCompletionIntegers E} :=
  RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _) (p := fun v => v ≠ w)

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Use `show Valued.v ((z : v.adicCompletion E)) ≤ 1 ↔ _`. Rewrite using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`.
-/
theorem mem_integers_iff {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (z : E) :
    algebraMap E (v.adicCompletion E) z ∈ v.adicCompletionIntegers E ↔ v.valuation E z ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  show Valued.v ((z : v.adicCompletion E)) ≤ 1 ↔ _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

/- English proof (translation)
Rewrite `h` using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]`. Establish `hp : 0 < Valued.v t`. Rewrite using `[pos_iff_ne_zero]`. Conclude with `(_root_.map_ne_zero _).mpr ht`. Simplify using `using (mul_inv_le_iff₀ hp).mp h`.
-/
theorem le_of_mul_inv_mem {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (y t : w.adicCompletion E) (ht : t ≠ 0) (h : y * t⁻¹ ∈ w.adicCompletionIntegers E) : Valued.v y ≤ Valued.v t := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀] at h
  have hp : 0 < Valued.v t := by
    rw [pos_iff_ne_zero]; exact (_root_.map_ne_zero _).mpr ht
  simpa using (mul_inv_le_iff₀ hp).mp h

/- English proof (translation)
Take `⟨c', _, rfl⟩` from `hc`. Rewrite using `[Units.val_mul]`. Use `show (d : AdeleRing (𝓞 E) E).2 * 1 = _`. Rewrite using `[mul_one]`.
-/
theorem snd_mul_infConn {E : Type} [Field E] [NumberField E] (d c : Ideles E) (hc : c ∈ infConn E) :
    ((d * c : Ideles E) : AdeleRing (𝓞 E) E).2 = (d : AdeleRing (𝓞 E) E).2 := by
  obtain ⟨c', _, rfl⟩ := hc
  rw [Units.val_mul]
  show (d : AdeleRing (𝓞 E) E).2 * 1 = _
  rw [mul_one]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem snd_diagUnits {E : Type} [Field E] [NumberField E] (k : Eˣ) :
    ((diagUnits E k : Ideles E) : AdeleRing (𝓞 E) E).2 = algebraMap E (FiniteAdeleRing (𝓞 E) E) (k : E) := rfl

/- English proof (translation)
The claim follows from `(localIdele_isSupportedAt E w x).2 v hv`.
-/
theorem localIdele_snd_ne' {E : Type} [Field E] [NumberField E] (w v : HeightOneSpectrum (𝓞 E)) (hv : v ≠ w)
    (x : (w.adicCompletion E)ˣ) : ((localIdele E w x : Ideles E) : AdeleRing (𝓞 E) E).2 v = 1 :=
  (localIdele_isSupportedAt E w x).2 v hv

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ art ha w x hx a _ t ht`. Establish `hmem : localIdele E w x ∈ closure (((diagUnits E).range ⊔ infConn E : Subgroup (Ideles E)) : Set (Ideles E))`. Rewrite using `[← Subgroup.topologicalClosure_coe, ← ha.ker]`. Conclude with `hx`. Set `g1 : Ideles E → FiniteAdeleRing (𝓞 E) E` to `fun y => (y : AdeleRing (𝓞 E) E).2`.

Set `g2 : Ideles E → FiniteAdeleRing (𝓞 E) E` to `fun y => ((y⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).2`. Establish `hg1 : Continuous g1` using `continuous_snd.comp Units.continuous_val`. Establish `hg2 : Continuous g2` using `continuous_snd.comp Units.continuous_coe_inv`. Set `c : FiniteAdeleRing (𝓞 E) E` to `algebraMap E (FiniteAdeleRing (𝓞 E) E) ((a : E)⁻¹)`. Set `U : Set (FiniteAdeleRing (𝓞 E) E)` to `{f | ∀ v, v ≠ w → f v ∈ v.adicCompletionIntegers E}`.

Establish `hU : IsOpen U` using `isOpen_integers_away w`. Set `N : Set (Ideles E)` to `(fun y => (g1 y - 1) * c) ⁻¹' U ∩ g2 ⁻¹' U ∩ (fun y => (g1 y w - (x : w.adicCompletion E)) * t⁻¹) ⁻¹' (w.adicCompletionIntegers E : Set (w.adicCompletion E))`. Establish `hN : IsOpen N`. Use `((hU.preimage ((hg1.sub continuous_const).mul continuous_const)).inter (hU.preimage hg2)).inter ?_` and prove the remaining obligations. Conclude with `(Valued.isOpen_valuationSubring _).preimage ((((RestrictedProduct.continuous_eval w).comp hg1).sub continuous_const).mul continuous_const)`.

Establish `hxN : localIdele E w x ∈ N`. Use `⟨⟨fun v hv => ?_, fun v hv => ?_⟩, ?_⟩` and prove the remaining obligations. Use `show ((g1 (localIdele E w x) - 1) * c) v ∈ v.adicCompletionIntegers E`. Establish `e : ((g1 (localIdele E w x) - 1) * c) v = 0` using `by show (((localIdele E w x : Ideles E) : AdeleRing (𝓞 E) E).2 v - 1) * c v = 0`. Rewrite using `[localIdele_snd_ne' w v hv, sub_self, zero_mul]`.

Rewrite using `[e]`. Conclude with `zero_mem _`. Use `show g2 (localIdele E w x) v ∈ v.adicCompletionIntegers E`. Establish `e : g2 (localIdele E w x) v = 1` using `by show (((localIdele E w x)⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).2 v = 1`. Rewrite using `[← map_inv]`.

Conclude with `localIdele_snd_ne' w v hv _`. Rewrite using `[e]`. Conclude with `one_mem _`. Use `show (g1 (localIdele E w x) w - (x : w.adicCompletion E)) * t⁻¹ ∈ w.adicCompletionIntegers E`. Establish `e : g1 (localIdele E w x) w = (x : w.adicCompletion E)` using `localIdele_snd_self E w x`.

Rewrite using `[e, sub_self, zero_mul]`. Conclude with `zero_mem _`. Take `⟨h, hhN, hhH⟩` from `mem_closure_iff.mp hmem N hN hxN`. Take `⟨_, ⟨k, rfl⟩, d, hd, rfl⟩` from `Subgroup.mem_sup.1 hhH`. Establish `e1 : g1 (diagUnits E k * d) = algebraMap E (FiniteAdeleRing (𝓞 E) E) (k : E)` using `by show ((diagUnits E k * d : Ideles E) : AdeleRing (𝓞 E) E).2 = _`.

Rewrite using `[snd_mul_infConn _ _ hd, snd_diagUnits]`. Establish `e2 : g2 (diagUnits E k * d) = algebraMap E (FiniteAdeleRing (𝓞 E) E) ((k⁻¹ : Eˣ) : E)` using `by show (((diagUnits E k * d)⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).2 = _`. Rewrite using `[mul_inv, ← map_inv, snd_mul_infConn _ _ (inv_mem hd), snd_diagUnits]`. Take `⟨⟨h1, h2⟩, h3⟩` from `hhN`. Use `⟨k, fun v hv => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Establish `this : ((g1 (diagUnits E k * d) - 1) * c) v ∈ v.adicCompletionIntegers E` using `h1 v hv`. Establish `e : ((g1 (diagUnits E k * d) - 1) * c) v = algebraMap E (v.adicCompletion E) (((k : E) - 1) / (a : E))`. Rewrite using `[e1, div_eq_mul_inv, map_mul, map_sub, map_one]`. Both sides reduce to the same expression. Rewrite `this` using `[e]`.

Conclude with `(mem_integers_iff v _).mp this`. Establish `this : g2 (diagUnits E k * d) v ∈ v.adicCompletionIntegers E` using `h2 v hv`. Rewrite `this` using `[e2]`. Rewrite using `[← Units.val_inv_eq_inv_val]`. Conclude with `(mem_integers_iff v _).mp this`.

Establish `e : g1 (diagUnits E k * d) w = algebraMap E (w.adicCompletion E) (k : E)`. Rewrite using `[e1]`. Both sides reduce to the same expression. Establish `h3' : (g1 (diagUnits E k * d) w - (x : w.adicCompletion E)) * t⁻¹ ∈ w.adicCompletionIntegers E` using `h3`. Rewrite `h3'` using `[e]`.

Conclude with `le_of_mul_inv_mem w _ t ht h3'`.
-/
theorem exists_global_approx : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ), art (Neutral.B1.localIdele E w x) = 1 →
    (∀ a : ℕ, 0 < a → ∀ t : w.adicCompletion E, t ≠ 0 → ∃ k : Eˣ,
      (∀ v : HeightOneSpectrum (𝓞 E), v ≠ w →
        v.valuation E (((k : E) - 1) / (a : E)) ≤ 1 ∧ v.valuation E ((k : E)⁻¹) ≤ 1) ∧
      Valued.v (algebraMap E (w.adicCompletion E) (k : E) - (x : w.adicCompletion E)) ≤ Valued.v t) := by
  intro E Ω _ _ _ _ _ art ha w x hx a _ t ht
  classical
  have hmem : localIdele E w x ∈ closure (((diagUnits E).range ⊔ infConn E : Subgroup (Ideles E)) : Set (Ideles E)) := by
    rw [← Subgroup.topologicalClosure_coe, ← ha.ker]
    exact hx
  let g1 : Ideles E → FiniteAdeleRing (𝓞 E) E := fun y => (y : AdeleRing (𝓞 E) E).2
  let g2 : Ideles E → FiniteAdeleRing (𝓞 E) E := fun y => ((y⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).2
  have hg1 : Continuous g1 := continuous_snd.comp Units.continuous_val
  have hg2 : Continuous g2 := continuous_snd.comp Units.continuous_coe_inv
  let c : FiniteAdeleRing (𝓞 E) E := algebraMap E (FiniteAdeleRing (𝓞 E) E) ((a : E)⁻¹)
  let U : Set (FiniteAdeleRing (𝓞 E) E) := {f | ∀ v, v ≠ w → f v ∈ v.adicCompletionIntegers E}
  have hU : IsOpen U := isOpen_integers_away w
  let N : Set (Ideles E) := (fun y => (g1 y - 1) * c) ⁻¹' U ∩ g2 ⁻¹' U ∩
    (fun y => (g1 y w - (x : w.adicCompletion E)) * t⁻¹) ⁻¹' (w.adicCompletionIntegers E : Set (w.adicCompletion E))
  have hN : IsOpen N := by
    refine ((hU.preimage ((hg1.sub continuous_const).mul continuous_const)).inter (hU.preimage hg2)).inter ?_
    exact (Valued.isOpen_valuationSubring _).preimage
      ((((RestrictedProduct.continuous_eval w).comp hg1).sub continuous_const).mul continuous_const)
  have hxN : localIdele E w x ∈ N := by
    refine ⟨⟨fun v hv => ?_, fun v hv => ?_⟩, ?_⟩
    · show ((g1 (localIdele E w x) - 1) * c) v ∈ v.adicCompletionIntegers E
      have e : ((g1 (localIdele E w x) - 1) * c) v = 0 := by
        show (((localIdele E w x : Ideles E) : AdeleRing (𝓞 E) E).2 v - 1) * c v = 0
        rw [localIdele_snd_ne' w v hv, sub_self, zero_mul]
      rw [e]; exact zero_mem _
    · show g2 (localIdele E w x) v ∈ v.adicCompletionIntegers E
      have e : g2 (localIdele E w x) v = 1 := by
        show (((localIdele E w x)⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).2 v = 1
        rw [← map_inv]
        exact localIdele_snd_ne' w v hv _
      rw [e]; exact one_mem _
    · show (g1 (localIdele E w x) w - (x : w.adicCompletion E)) * t⁻¹ ∈ w.adicCompletionIntegers E
      have e : g1 (localIdele E w x) w = (x : w.adicCompletion E) := localIdele_snd_self E w x
      rw [e, sub_self, zero_mul]; exact zero_mem _
  obtain ⟨h, hhN, hhH⟩ := mem_closure_iff.mp hmem N hN hxN
  obtain ⟨_, ⟨k, rfl⟩, d, hd, rfl⟩ := Subgroup.mem_sup.1 hhH
  have e1 : g1 (diagUnits E k * d) = algebraMap E (FiniteAdeleRing (𝓞 E) E) (k : E) := by
    show ((diagUnits E k * d : Ideles E) : AdeleRing (𝓞 E) E).2 = _
    rw [snd_mul_infConn _ _ hd, snd_diagUnits]
  have e2 : g2 (diagUnits E k * d) = algebraMap E (FiniteAdeleRing (𝓞 E) E) ((k⁻¹ : Eˣ) : E) := by
    show (((diagUnits E k * d)⁻¹ : Ideles E) : AdeleRing (𝓞 E) E).2 = _
    rw [mul_inv, ← map_inv, snd_mul_infConn _ _ (inv_mem hd), snd_diagUnits]
  obtain ⟨⟨h1, h2⟩, h3⟩ := hhN
  refine ⟨k, fun v hv => ⟨?_, ?_⟩, ?_⟩
  · have this : ((g1 (diagUnits E k * d) - 1) * c) v ∈ v.adicCompletionIntegers E := h1 v hv
    have e : ((g1 (diagUnits E k * d) - 1) * c) v = algebraMap E (v.adicCompletion E) (((k : E) - 1) / (a : E)) := by
      rw [e1, div_eq_mul_inv, map_mul, map_sub, map_one]
      rfl
    rw [e] at this
    exact (mem_integers_iff v _).mp this
  · have this : g2 (diagUnits E k * d) v ∈ v.adicCompletionIntegers E := h2 v hv
    rw [e2] at this
    rw [← Units.val_inv_eq_inv_val]
    exact (mem_integers_iff v _).mp this
  · have e : g1 (diagUnits E k * d) w = algebraMap E (w.adicCompletion E) (k : E) := by
      rw [e1]; rfl
    have h3' : (g1 (diagUnits E k * d) w - (x : w.adicCompletion E)) * t⁻¹ ∈ w.adicCompletionIntegers E := h3
    rw [e] at h3'
    exact le_of_mul_inv_mem w _ t ht h3'

end GlobalTheory.ArtinApprox
