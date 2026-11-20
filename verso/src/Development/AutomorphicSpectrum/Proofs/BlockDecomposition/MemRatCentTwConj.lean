import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (quotIntegral IsQuotNormaliser twConj twConj_mul_left mem_twCent)

namespace GlobalTheory.CompanionTheory.OrbInv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Establish `h : ∀ g : GL (Fin n) E, (ratGL E n g).val = g.val.map (algebraMap E (Ad E))` using `fun _ => rfl`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[thetaR_val, ← map_inv, h, h, thetaR_val]`. Use extensionality with `i j`. Conclude with `conjAd_algebraMap _`.
-/
theorem thetaA_ratGL (g : GL (Fin n) E) : thetaA E n (ratGL E n g) = ratGL E n (thetaE E n g) := by
  have h : ∀ g : GL (Fin n) E, (ratGL E n g).val = g.val.map (algebraMap E (Ad E)) := fun _ => rfl
  apply Units.ext
  rw [thetaR_val, ← map_inv, h, h, thetaR_val]
  ext i j
  exact conjAd_algebraMap _

/- English proof (translation)
Simplify using `only [twConj, map_mul, map_inv, thetaA_ratGL]`. Use `group`.
-/
theorem twConj_ratGL (g d : GL (Fin n) E) (x : GA E n) :
    twConj (thetaA E n) x (ratGL E n (twConj (thetaE E n) g d)) =
      twConj (thetaA E n) (ratGL E n g * x) (ratGL E n d) := by
  simp only [twConj, map_mul, map_inv, thetaA_ratGL]
  group

/- English proof (translation)
Simplify using `only [ratCent, Subgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, rfl⟩`. Establish `hc'` using `(mem_twCent _ _ _).1 hc`. Simplify using `only [twConj] at hc'`.

Use `⟨g * c * g⁻¹, (mem_twCent _ _ _).2 ?_, by simp only [map_mul, map_inv]⟩` and prove the remaining obligations. Simplify using `only [map_mul, map_inv]`. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `⟨c, hc, h⟩`. Establish `hc'` using `(mem_twCent _ _ _).1 hc`.

Use `⟨g⁻¹ * c * g, (mem_twCent _ _ _).2 ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [twConj, map_mul, map_inv]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [map_mul, map_inv, h] group`.
-/
theorem mem_ratCent_twConj (g d : GL (Fin n) E) (x : GA E n) :
    x ∈ ratCent (twConj (thetaE E n) g d) ↔ ratGL E n g * x * (ratGL E n g)⁻¹ ∈ ratCent d := by
  simp only [ratCent, Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' := (mem_twCent _ _ _).1 hc
    simp only [twConj] at hc'
    refine ⟨g * c * g⁻¹, (mem_twCent _ _ _).2 ?_, by simp only [map_mul, map_inv]⟩
    simp only [map_mul, map_inv]
    calc (g * c * g⁻¹)⁻¹ * d * (thetaE E n g * thetaE E n c * (thetaE E n g)⁻¹)
        = g * (c⁻¹ * (g⁻¹ * d * thetaE E n g) * thetaE E n c) * (thetaE E n g)⁻¹ := by group
      _ = g * (g⁻¹ * d * thetaE E n g) * (thetaE E n g)⁻¹ := by rw [hc']
      _ = d := by group
  · rintro ⟨c, hc, h⟩
    have hc' := (mem_twCent _ _ _).1 hc
    refine ⟨g⁻¹ * c * g, (mem_twCent _ _ _).2 ?_, ?_⟩
    · simp only [twConj, map_mul, map_inv]
      calc (g⁻¹ * c * g)⁻¹ * (g⁻¹ * d * thetaE E n g) *
            ((thetaE E n g)⁻¹ * thetaE E n c * thetaE E n g)
          = g⁻¹ * (c⁻¹ * d * thetaE E n c) * thetaE E n g := by group
        _ = g⁻¹ * d * thetaE E n g := by rw [hc']
    · simp only [map_mul, map_inv, h]
      group

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `Subgroup.mem_map.1 hh`. Establish `hc'` using `(mem_twCent _ _ _).1 hc`. Use `twConj_mul_left _ _ ((mem_twCent _ _ _).2 ?_) x` and prove the remaining obligations. Rewrite using `[thetaA_ratGL, ← map_inv, ← map_mul, ← map_mul, hc']`.
-/
theorem twConj_ratCent (d : GL (Fin n) E) {h : GA E n} (hh : h ∈ ratCent d) (x : GA E n) :
    twConj (thetaA E n) (h * x) (ratGL E n d) = twConj (thetaA E n) x (ratGL E n d) := by
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hh
  have hc' := (mem_twCent _ _ _).1 hc
  refine twConj_mul_left _ _ ((mem_twCent _ _ _).2 ?_) x
  rw [thetaA_ratGL, ← map_inv, ← map_mul, ← map_mul, hc']

/- English proof (translation)
The claim follows from `(Set.countable_range (ratGL E n)).mono (by rintro _ ⟨c, -, rfl⟩ exact ⟨c, rfl⟩)`.
-/
theorem countable_ratCent [Countable (GL (Fin n) E)] (d : GL (Fin n) E) :
    (ratCent d : Set (GA E n)).Countable :=
  (Set.countable_range (ratGL E n)).mono (by
    rintro _ ⟨c, -, rfl⟩
    exact ⟨c, rfl⟩)

/- English proof (translation)
Introduce `hQ hT E _ _ _ a b _ _ _ _ μ₁ _ μ₂ _ φ d₁ g₁ d₂ g₂ hc`. Take `⟨⟨lc₁, sc₁, t₁⟩, -, -, cn₁, -, -⟩` from `hT E a`. Take `⟨⟨lc₂, sc₂, t₂⟩, -, -, cn₂, -, -⟩` from `hT E b`. Establish `hcnt : (((ratCent d₁).prod (ratCent d₂) : Subgroup (GA E a × GA E b)) : Set (GA E a × GA E b)).Countable`. Rewrite using `[Subgroup.coe_prod]`.

Conclude with `(countable_ratCent d₁).prod (countable_ratCent d₂)`. Establish `: Countable ((ratCent d₁).prod (ratCent d₂) : Subgroup (GA E a × GA E b))` using `hcnt.to_subtype`. Use `set F : GA E a × GA E b → ℂ := fun x => φ (twConj (thetaA E a) x.1 (ratGL E a d₁), twConj (thetaA E b) x.2 (ratGL E b d₂)) with hF`. Establish `key` using `hQ (GA E a × GA E b) (μ₁.prod μ₂) ((ratCent d₁).prod (ratCent d₂)) ((ratCent (twConj (thetaE E a) g₁ d₁)).prod (ratCent (twConj (thetaE E b) g₂ d₂))) F (ratGL E a g₁, ratGL E b g₂) hc.measurable (fun h hh x => by`. Simplify using `only [hF, Prod.fst_mul, Prod.snd_mul]`.

Rewrite using `[twConj_ratCent d₁ hh.1, twConj_ratCent d₂ hh.2])`. Use the proof step `(fun x => by`. Simplify using `only [Subgroup.mem_prod, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, mem_ratCent_twConj])`. Simplify using `only [hF, Prod.fst_mul, Prod.snd_mul] at key`. Simplify using `only [orbTerm2, twConj_ratGL]`.

Conclude with `key`.
-/
theorem orbInvOf : OrbInvOf := by
  intro hQ hT E _ _ _ a b _ _ _ _ μ₁ _ μ₂ _ φ d₁ g₁ d₂ g₂ hc
  obtain ⟨⟨lc₁, sc₁, t₁⟩, -, -, cn₁, -, -⟩ := hT E a
  obtain ⟨⟨lc₂, sc₂, t₂⟩, -, -, cn₂, -, -⟩ := hT E b
  have hcnt : (((ratCent d₁).prod (ratCent d₂) : Subgroup (GA E a × GA E b)) :
      Set (GA E a × GA E b)).Countable := by
    rw [Subgroup.coe_prod]
    exact (countable_ratCent d₁).prod (countable_ratCent d₂)
  have : Countable ((ratCent d₁).prod (ratCent d₂) : Subgroup (GA E a × GA E b)) := hcnt.to_subtype
  set F : GA E a × GA E b → ℂ := fun x =>
    φ (twConj (thetaA E a) x.1 (ratGL E a d₁), twConj (thetaA E b) x.2 (ratGL E b d₂)) with hF
  have key := hQ (GA E a × GA E b) (μ₁.prod μ₂) ((ratCent d₁).prod (ratCent d₂))
    ((ratCent (twConj (thetaE E a) g₁ d₁)).prod (ratCent (twConj (thetaE E b) g₂ d₂))) F
    (ratGL E a g₁, ratGL E b g₂) hc.measurable
    (fun h hh x => by
      simp only [hF, Prod.fst_mul, Prod.snd_mul]
      rw [twConj_ratCent d₁ hh.1, twConj_ratCent d₂ hh.2])
    (fun x => by
      simp only [Subgroup.mem_prod, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv,
        mem_ratCent_twConj])
  simp only [hF, Prod.fst_mul, Prod.snd_mul] at key
  simp only [orbTerm2, twConj_ratGL]
  exact key

end GlobalTheory.CompanionTheory.OrbInv

end
