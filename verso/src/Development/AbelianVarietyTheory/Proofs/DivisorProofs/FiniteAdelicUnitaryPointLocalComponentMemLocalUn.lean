import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt

noncomputable section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.LocMem

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Use `set c : E ≃+* E := (IsCMField.complexConj E).toRingEquiv`. Use `set u := conjSrc c w with hu`. Establish `h : GlobalTheory.Mem.Chr.ConjPl c u w` using `conjPl_conjSrc c w`. Assume the negation of the conclusion as `hne`. Apply `hw` to reduce the goal to its premises.

Use `⟨u, hne, ?_⟩` and prove the remaining obligations. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `y`. Express the relevant statement in the definitionally equal form `algebraMap _ _ y ∈ u.asIdeal ↔ algebraMap _ _ y ∈ w.asIdeal`. Rewrite using `[← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]`.

Establish `hfix : c ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) y : 𝓞 E) : E) = ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) y : 𝓞 E) : E)`. Express the relevant statement in the definitionally equal form `IsCMField.complexConj E _ = _`. Rewrite using `[IsCMField.complexConj_eq_self_iff]`. Conclude with `((y : maximalRealSubfield E)).2`. Rewrite using `[← h, hfix]`.
-/
theorem conjSrc_eq_of_not_split (w : Pl E) (hw : ¬ IsSplitAt w) :
    conjSrc (IsCMField.complexConj E).toRingEquiv w = w := by
  set c : E ≃+* E := (IsCMField.complexConj E).toRingEquiv
  set u := conjSrc c w with hu
  have h : GlobalTheory.Mem.Chr.ConjPl c u w := conjPl_conjSrc c w
  by_contra hne
  apply hw
  refine ⟨u, hne, ?_⟩
  apply HeightOneSpectrum.ext
  ext y
  change algebraMap _ _ y ∈ u.asIdeal ↔ algebraMap _ _ y ∈ w.asIdeal
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
  have hfix : c ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) y : 𝓞 E) : E) =
      ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) y : 𝓞 E) : E) := by
    change IsCMField.complexConj E _ = _
    rw [IsCMField.complexConj_eq_self_iff]
    exact ((y : maximalRealSubfield E)).2
  rw [← h, hfix]

/- English proof (translation)
Substitute `hu` using the available equality. Establish `hex : ∃ s : u.adicCompletion E →+* u.adicCompletion E, Continuous s ∧ ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)` using `⟨f, hf, hext⟩`. Establish `hcj : cj u = hex.choose`. Unfold `cj`. Rewrite using `[dif_pos hex]`.

Establish `hfs : (f : u.adicCompletion E → u.adicCompletion E) = hex.choose` using `(HeightOneSpectrum.denseRange_algebraMap E u).equalizer hf hex.choose_spec.1 (funext fun k => by simp only [Function.comp_apply, hext, hex.choose_spec.2])`. Rewrite using `[hcj, ← hfs]`.
-/
theorem eq_cj_of_ext (w u : Pl E) (hu : u = w) (f : u.adicCompletion E →+* w.adicCompletion E) (hf : Continuous f)
    (hext : ∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) (b : Af E) :
    f (pLoc E u b) = cj w (pLoc E w b) := by
  subst hu
  have hex : ∃ s : u.adicCompletion E →+* u.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, hext⟩
  have hcj : cj u = hex.choose := by
    unfold cj
    rw [dif_pos hex]
  have hfs : (f : u.adicCompletion E → u.adicCompletion E) = hex.choose :=
    (HeightOneSpectrum.denseRange_algebraMap E u).equalizer hf hex.choose_spec.1
      (funext fun k => by simp only [Function.comp_apply, hext, hex.choose_spec.2])
  rw [hcj, ← hfs]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `_ = pLoc E w (conjFin (IsCMField.complexConj E).toRingEquiv (pFin E a))`. Rewrite using `[pLoc_conjFin]`. Conclude with `(eq_cj_of_ext w _ (conjSrc_eq_of_not_split w hw) _ (conjLoc_spec _ w).1 (fun k => (conjLoc_spec _ w).2.1 k) (pFin E a)).symm`.
-/
theorem cj_pLoc_pFin (w : Pl E) (hw : ¬ IsSplitAt w) (a : Ad E) :
    cj w (pLoc E w (pFin E a)) = pLoc E w (pFin E (conjAd E a)) := by
  change _ = pLoc E w (conjFin (IsCMField.complexConj E).toRingEquiv (pFin E a))
  rw [pLoc_conjFin]
  exact (eq_cj_of_ext w _ (conjSrc_eq_of_not_split w hw) _ (conjLoc_spec _ w).1
    (fun k => (conjLoc_spec _ w).2.1 k) (pFin E a)).symm

end GlobalTheory.BCT.LocMem

open GlobalTheory.BCT.LocMem in

/- English proof (translation)
Introduce `E _ _ _ _ n w x`. Unfold `UL`. Use `split_ifs with hs`. Conclude with `Subgroup.mem_top _`. Establish `hx : cT (conjAd E) ((x : UA E n) : GA E n).val * 1 * ((x : UA E n) : GA E n).val = 1` using `(x : UA E n).2`.

Use `set φ : Ad E →+* w.adicCompletion E := (pLoc E w).comp (pFin E)`. Establish `hval : (cLoc w (x : UA E n)).val = φ.mapMatrix ((x : UA E n) : GA E n).val` using `rfl`. Establish `hcT : cT (cj w) (φ.mapMatrix ((x : UA E n) : GA E n).val) = φ.mapMatrix (cT (conjAd E) ((x : UA E n) : GA E n).val)`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Conclude with `cj_pLoc_pFin w hs _`.

Express the relevant statement in the definitionally equal form `cT (cj w) (cLoc w (x : UA E n)).val * 1 * (cLoc w (x : UA E n)).val = 1`. Rewrite using `[hval, hcT, ← map_one φ.mapMatrix, ← map_mul, ← map_mul, hx]`.
-/
theorem GlobalTheory.BCT.cLoc_mem_UL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ,
    ∀ (w : Pl E) (x : finU E n), cLoc w (x : UA E n) ∈ UL n w := by
  intro E _ _ _ _ n w x
  unfold UL
  split_ifs with hs
  · exact Subgroup.mem_top _
  have hx : cT (conjAd E) ((x : UA E n) : GA E n).val * 1 * ((x : UA E n) : GA E n).val = 1 := (x : UA E n).2
  set φ : Ad E →+* w.adicCompletion E := (pLoc E w).comp (pFin E)
  have hval : (cLoc w (x : UA E n)).val = φ.mapMatrix ((x : UA E n) : GA E n).val := rfl
  have hcT : cT (cj w) (φ.mapMatrix ((x : UA E n) : GA E n).val) =
      φ.mapMatrix (cT (conjAd E) ((x : UA E n) : GA E n).val) := by
    refine Matrix.ext fun i j => ?_
    exact cj_pLoc_pFin w hs _
  change cT (cj w) (cLoc w (x : UA E n)).val * 1 * (cLoc w (x : UA E n)).val = 1
  rw [hval, hcT, ← map_one φ.mapMatrix, ← map_mul, ← map_mul, hx]
