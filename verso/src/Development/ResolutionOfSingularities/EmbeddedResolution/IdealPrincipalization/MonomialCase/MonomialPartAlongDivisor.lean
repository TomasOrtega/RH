import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IrreducibleComponentsOfSupport
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtGenericPoint
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.Foundations.Schemes.AffineOpens
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialSplitting
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `z hz`. Simplify using `using hz`. Consider the case `succ m ih`.

Introduce `z hz`. Use `ih z (hcan n (h ^ m * z) ?_)` and prove the remaining obligations. Establish `hmul : h * (h ^ m * z) = h ^ (m + 1) * z` using `by ring`. Rewrite using `[hmul]`. Conclude with `hz`.
-/
private theorem mem_span_of_pow_mul_mem_span {R : Type*} [CommRing R] (g h : R)
    (hcan : ∀ (n : ℕ) (z : R), h * z ∈ Ideal.span ({g ^ n} : Set R) →
      z ∈ Ideal.span ({g ^ n} : Set R)) (n m : ℕ) :
    ∀ z : R, h ^ m * z ∈ Ideal.span ({g ^ n} : Set R) → z ∈ Ideal.span ({g ^ n} : Set R) := by
  induction m with
  | zero =>
      intro z hz
      simpa using hz
  | succ m ih =>
      intro z hz
      refine ih z (hcan n (h ^ m * z) ?_)
      have hmul : h * (h ^ m * z) = h ^ (m + 1) * z := by ring
      rw [hmul]
      exact hz

variable {X : Scheme.{u}}

/- English proof (translation)
Establish `h` using `stalkIdeal_mul (1 : X.IdealSheafData) (⊤ : X.IdealSheafData) x`. Rewrite `h` using `[one_mul, stalkIdeal_top]`. Use `le_antisymm le_top ?_` and prove the remaining obligations. Rewrite using `[h]`. Conclude with `Ideal.mul_le.mpr (fun r hr s _ => Ideal.mul_mem_right s _ hr)`.
-/
theorem stalkIdeal_one (x : X) : stalkIdeal (1 : X.IdealSheafData) x = ⊤ := by
  have h := stalkIdeal_mul (1 : X.IdealSheafData) (⊤ : X.IdealSheafData) x
  rw [one_mul, stalkIdeal_top] at h
  refine le_antisymm le_top ?_
  rw [h]
  exact Ideal.mul_le.mpr (fun r hr s _ => Ideal.mul_mem_right s _ hr)

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil`. Rewrite using `[List.prod_nil, List.map_nil, List.prod_nil, stalkIdeal_one x, Ideal.one_eq_top]`. Consider the case `cons J L ih`. Rewrite using `[List.prod_cons, stalkIdeal_mul, ih, List.map_cons, List.prod_cons]`.
-/
theorem stalkIdeal_listProd (L : List X.IdealSheafData) (x : X) :
    stalkIdeal L.prod x = (L.map (fun I => stalkIdeal I x)).prod := by
  induction L with
  | nil =>
      rw [List.prod_nil, List.map_nil, List.prod_nil, stalkIdeal_one x, Ideal.one_eq_top]
  | cons J L ih =>
      rw [List.prod_cons, stalkIdeal_mul, ih, List.map_cons, List.prod_cons]

variable {k : Type u} [Field k]

@[reducible]
def IsEtaleLocallyCoordinateDivisor (p : X ⟶ Spec (CommRingCat.of k)) (D : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
    restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j}

/- English proof (translation)
Take `⟨i, hi, hiD⟩` from `List.getElem_of_mem hD`. Take `⟨-, hpos⟩` from `(inStrictNormalCrossingPosition_iff p E).mp hE`. Introduce `x`. Take `⟨U, hxU, m, c, a, -, hnone, hsome⟩` from `InStrictNormalCrossingPositionAt.exists_etaleChart (hpos x)`. Use `⟨U, hxU, m, c, ?_⟩` and prove the remaining obligations.

Consider the cases of `hai : a i with`. Consider the case `none => left`. Establish `h` using `hnone i hi hai`. Rewrite `h` using `[hiD]`. Then use the resulting hypothesis. Consider the case `some t => right`.

Use `⟨t, ?_⟩` and prove the remaining obligations. Establish `h` using `hsome i hi t hai`. Rewrite `h` using `[hiD]`. Then use the resulting hypothesis.
-/
theorem isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition (p : X ⟶ Spec (CommRingCat.of k))
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) (D : X.IdealSheafData) (hD : D ∈ E) :
    IsEtaleLocallyCoordinateDivisor p D := by
  obtain ⟨i, hi, hiD⟩ := List.getElem_of_mem hD
  obtain ⟨-, hpos⟩ := (inStrictNormalCrossingPosition_iff p E).mp hE
  intro x
  obtain ⟨U, hxU, m, c, a, -, hnone, hsome⟩ := InStrictNormalCrossingPositionAt.exists_etaleChart (hpos x)
  refine ⟨U, hxU, m, c, ?_⟩
  cases hai : a i with
  | none =>
      left
      have h := hnone i hi hai
      rwa [hiD] at h
  | some t =>
      right
      refine ⟨t, ?_⟩
      have h := hsome i hi t hai
      rwa [hiD] at h

def orderAlongComponent (I : X.IdealSheafData) {C : Set X} (hC : IsIrreducible C) : ℕ :=
  (orderAt I hC.genericPoint).toNat

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem orderAlongComponent_eq_orderAt_genericPoint (I : X.IdealSheafData) {C : Set X} (hC : IsIrreducible C) :
    orderAlongComponent I hC = (orderAt I hC.genericPoint).toNat := rfl

/- English proof (translation)
Establish `h : orderAt I hC.isIrreducible.genericPoint ≠ ⊤` using `hC.orderAt_genericPoint_ne_top I hI`. Rewrite using `[orderAlongComponent_eq_orderAt_genericPoint, ENat.natCast_toNat h]`.
-/
theorem coe_orderAlongComponent_eq_orderAt_genericPoint [IsLocallyNoetherian X] {D I : X.IdealSheafData} {C : Set X}
    (hC : IsIrreducibleComponentOfSupport D C) (hI : NonzeroOnComponents I) :
    (orderAlongComponent I hC.isIrreducible : ℕ∞) = orderAt I hC.isIrreducible.genericPoint := by
  have h : orderAt I hC.isIrreducible.genericPoint ≠ ⊤ :=
    hC.orderAt_genericPoint_ne_top I hI
  rw [orderAlongComponent_eq_orderAt_genericPoint, ENat.natCast_toNat h]

def componentPowerIdeal (I D : X.IdealSheafData) (C : Set X) : X.IdealSheafData :=
  letI : Decidable (IsIrreducibleComponentOfSupport D C) := Classical.propDecidable _
  if h : IsIrreducibleComponentOfSupport D C then
    Scheme.IdealSheafData.vanishingIdeal (⟨C, h.isClosed⟩ : TopologicalSpace.Closeds ↥X) ^
      orderAlongComponent I h.isIrreducible
  else ⊤

/- English proof (translation)
The claim follows from `@dif_neg (IsIrreducibleComponentOfSupport D C) (Classical.propDecidable (IsIrreducibleComponentOfSupport D C)) h X.IdealSheafData _ _`.
-/
theorem componentPowerIdeal_of_not_isIrreducibleComponentOfSupport (I D : X.IdealSheafData) {C : Set X}
    (h : ¬ IsIrreducibleComponentOfSupport D C) : componentPowerIdeal I D C = ⊤ :=
  @dif_neg (IsIrreducibleComponentOfSupport D C) (Classical.propDecidable (IsIrreducibleComponentOfSupport D C)) h
    X.IdealSheafData _ _

/- English proof (translation)
Unfold `componentPowerIdeal`. Conclude with `dif_pos h`.
-/
theorem componentPowerIdeal_of_isIrreducibleComponentOfSupport (I D : X.IdealSheafData) {C : Set X}
    (h : IsIrreducibleComponentOfSupport D C) :
    componentPowerIdeal I D C =
      Scheme.IdealSheafData.vanishingIdeal (⟨C, h.isClosed⟩ : TopologicalSpace.Closeds ↥X) ^
        orderAlongComponent I h.isIrreducible := by
  unfold componentPowerIdeal
  exact dif_pos h

/- English proof (translation)
Distinguish the cases in `hC : IsIrreducibleComponentOfSupport D C`. Establish `htop : stalkIdeal (Scheme.IdealSheafData.vanishingIdeal (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)) x = ⊤`. Assume the negation of the conclusion as `h`. Establish `hmem : x ∈ ((Scheme.IdealSheafData.vanishingIdeal (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)).support : Set ↥X)` using `(mem_support_iff_stalkIdeal_ne_top _ x).mpr h`. Rewrite `hmem` using `[Scheme.IdealSheafData.coe_support_vanishingIdeal]`.

Conclude with `hx hmem`. Rewrite using `[componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC, stalkIdeal_pow, htop, ← Ideal.one_eq_top, one_pow]`. Rewrite using `[componentPowerIdeal_of_not_isIrreducibleComponentOfSupport I D hC, stalkIdeal_top]`.
-/
theorem stalkIdeal_componentPowerIdeal_of_not_mem (I D : X.IdealSheafData) (C : Set X) {x : X}
    (hx : x ∉ C) : stalkIdeal (componentPowerIdeal I D C) x = ⊤ := by
  by_cases hC : IsIrreducibleComponentOfSupport D C
  · have htop : stalkIdeal (Scheme.IdealSheafData.vanishingIdeal
        (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)) x = ⊤ := by
      by_contra h
      have hmem : x ∈ ((Scheme.IdealSheafData.vanishingIdeal
          (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)).support : Set ↥X) :=
        (mem_support_iff_stalkIdeal_ne_top _ x).mpr h
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hmem
      exact hx hmem
    rw [componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC, stalkIdeal_pow, htop, ← Ideal.one_eq_top,
      one_pow]
  · rw [componentPowerIdeal_of_not_isIrreducibleComponentOfSupport I D hC, stalkIdeal_top]

/- English proof (translation)
Rewrite using `[componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC, stalkIdeal_pow, hC.stalkIdeal_vanishingIdeal_eq p hD x hx]`.
-/
theorem stalkIdeal_componentPowerIdeal_of_mem [TopologicalSpace.NoetherianSpace ↥X]
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) {D : X.IdealSheafData}
    (hD : IsEtaleLocallyCoordinateDivisor p D) {C : Set X} (hC : IsIrreducibleComponentOfSupport D C) {x : X}
    (hx : x ∈ C) :
    stalkIdeal (componentPowerIdeal I D C) x =
      stalkIdeal D x ^ orderAlongComponent I hC.isIrreducible := by
  rw [componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC, stalkIdeal_pow,
    hC.stalkIdeal_vanishingIdeal_eq p hD x hx]

def supportComponentsFinset [TopologicalSpace.NoetherianSpace ↥X] (D : X.IdealSheafData) :
    Finset (Set X) :=
  (finite_isIrreducibleComponentOfSupport D).toFinset

def monomialPartAlongDivisor [TopologicalSpace.NoetherianSpace ↥X] (I D : X.IdealSheafData) :
    X.IdealSheafData :=
  (supportComponentsFinset D).inf (fun C => componentPowerIdeal I D C)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem monomialPartAlongDivisor_eq_inf_componentPowerIdeal [TopologicalSpace.NoetherianSpace ↥X] (I D : X.IdealSheafData) :
    monomialPartAlongDivisor I D = (supportComponentsFinset D).inf (fun C => componentPowerIdeal I D C) := rfl

/- English proof (translation)
Rewrite using `[le_iff_forall_stalkIdeal_le]`. Introduce `x`. Rewrite using `[stalkIdeal_mul]`. Conclude with `Ideal.mul_le.mpr fun r hr s _ => Ideal.mul_mem_right s _ hr`.
-/
private theorem idealSheafData_mul_le_left (a b : X.IdealSheafData) : a * b ≤ a := by
  rw [le_iff_forall_stalkIdeal_le]
  intro x
  rw [stalkIdeal_mul]
  exact Ideal.mul_le.mpr fun r hr s _ => Ideal.mul_mem_right s _ hr

/- English proof (translation)
Rewrite using `[le_iff_forall_stalkIdeal_le]`. Introduce `x`. Rewrite using `[stalkIdeal_mul]`. Conclude with `Ideal.mul_le.mpr fun r _ s hs => Ideal.mul_mem_left _ r hs`.
-/
private theorem idealSheafData_mul_le_right (a b : X.IdealSheafData) : a * b ≤ b := by
  rw [le_iff_forall_stalkIdeal_le]
  intro x
  rw [stalkIdeal_mul]
  exact Ideal.mul_le.mpr fun r _ s hs => Ideal.mul_mem_left _ r hs

/- English proof (translation)
Use `le_antisymm le_top ?_` and prove the remaining obligations. Establish `hmono` using `stalkIdeal_mono (le_inf (idealSheafData_mul_le_left a b) (idealSheafData_mul_le_right a b)) x`. Rewrite `hmono` using `[stalkIdeal_mul, ha, hb]`. Establish `htop : (⊤ : Ideal (X.presheaf.stalk x)) * ⊤ = ⊤`. Rewrite using `[← Ideal.one_eq_top, one_mul]`.

Rewrite `hmono` using `[htop]`. Then use the resulting hypothesis.
-/
private theorem stalkIdeal_inf_eq_top (a b : X.IdealSheafData) (x : X)
    (ha : stalkIdeal a x = ⊤) (hb : stalkIdeal b x = ⊤) :
    stalkIdeal (a ⊓ b) x = ⊤ := by
  refine le_antisymm le_top ?_
  have hmono := stalkIdeal_mono
    (le_inf (idealSheafData_mul_le_left a b) (idealSheafData_mul_le_right a b)) x
  rw [stalkIdeal_mul, ha, hb] at hmono
  have htop : (⊤ : Ideal (X.presheaf.stalk x)) * ⊤ = ⊤ := by
    rw [← Ideal.one_eq_top, one_mul]
  rwa [htop] at hmono

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Rewrite using `[Finset.inf_empty]`. Conclude with `stalkIdeal_top x`. Introduce `a t ha ih hs`.

Rewrite using `[Finset.inf_insert]`. Conclude with `stalkIdeal_inf_eq_top _ _ x (hs a (Finset.mem_insert_self a t)) (ih fun b hb => hs b (Finset.mem_insert_of_mem hb))`.
-/
private theorem stalkIdeal_finsetInf_eq_top {β : Type u} (f : β → X.IdealSheafData) (x : X)
    (s : Finset β) : (∀ b ∈ s, stalkIdeal (f b) x = ⊤) → stalkIdeal (s.inf f) x = ⊤ := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.inf_empty]
    exact stalkIdeal_top x
  · intro a t ha ih hs
    rw [Finset.inf_insert]
    exact stalkIdeal_inf_eq_top _ _ x (hs a (Finset.mem_insert_self a t))
      (ih fun b hb => hs b (Finset.mem_insert_of_mem hb))

/- English proof (translation)
Rewrite using `[monomialPartAlongDivisor_eq_inf_componentPowerIdeal]`. Use `stalkIdeal_finsetInf_eq_top (fun C => componentPowerIdeal I D C) x (supportComponentsFinset D) ?_` and prove the remaining obligations. Introduce `C hC`. Establish `hCmem : IsIrreducibleComponentOfSupport D C` using `(Set.Finite.mem_toFinset (finite_isIrreducibleComponentOfSupport D)).mp hC`. Conclude with `stalkIdeal_componentPowerIdeal_of_not_mem I D C (fun hxC => hx (hCmem.subset_support hxC))`.
-/
theorem stalkIdeal_monomialPartAlongDivisor_of_not_mem_support [TopologicalSpace.NoetherianSpace ↥X]
    (I D : X.IdealSheafData) {x : X} (hx : x ∉ (D.support : Set X)) :
    stalkIdeal (monomialPartAlongDivisor I D) x = ⊤ := by
  rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
  refine stalkIdeal_finsetInf_eq_top (fun C => componentPowerIdeal I D C) x
    (supportComponentsFinset D) ?_
  intro C hC
  have hCmem : IsIrreducibleComponentOfSupport D C :=
    (Set.Finite.mem_toFinset (finite_isIrreducibleComponentOfSupport D)).mp hC
  exact stalkIdeal_componentPowerIdeal_of_not_mem I D C (fun hxC => hx (hCmem.subset_support hxC))

/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil`. Introduce `a ha`. Simplify using `at ha`.

Consider the case `cons b L ih`. Introduce `a ha`. Rewrite using `[List.prod_cons]`. Break down `List.mem_cons.mp ha with h | h` into its components or cases. Rewrite using `[h]`.

Conclude with `idealSheafData_mul_le_left _ _`. Conclude with `le_trans (idealSheafData_mul_le_right _ _) (ih a h)`.
-/
private theorem idealSheafData_listProd_le_of_mem :
    ∀ (L : List X.IdealSheafData) (a : X.IdealSheafData), a ∈ L → L.prod ≤ a := by
  intro L
  induction L with
  | nil =>
      intro a ha
      simp at ha
  | cons b L ih =>
      intro a ha
      rw [List.prod_cons]
      rcases List.mem_cons.mp ha with h | h
      · rw [h]
        exact idealSheafData_mul_le_left _ _
      · exact le_trans (idealSheafData_mul_le_right _ _) (ih a h)

/- English proof (translation)
The claim follows from `List.prod_eq_one fun x hx => by obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx exact h a ha`.
-/
private theorem prod_map_eq_one_of_forall_eq_one {α : Type*} {M : Type*} [CommMonoid M]
    (g : α → M) (L : List α) (h : ∀ b ∈ L, g b = 1) : (L.map g).prod = 1 :=
  List.prod_eq_one fun x hx => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact h a ha

/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil`. Introduce `a _ ha _`. Simplify using `at ha`.

Consider the case `cons b L ih`. Introduce `a hnd ha hone`. Rewrite using `[List.map_cons, List.prod_cons]`. Break down `List.mem_cons.mp ha with h | h` into its components or cases. Establish `hL : (L.map g).prod = 1`.

Use `prod_map_eq_one_of_forall_eq_one g L ?_` and prove the remaining obligations. Introduce `c hc`. Use `hone c (List.mem_cons.mpr (Or.inr hc)) ?_` and prove the remaining obligations. Introduce `hca`. Conclude with `absurd (show b ∈ L by rw [← h, ← hca]; exact hc) (List.nodup_cons.mp hnd).1`.

Rewrite using `[hL, mul_one, h]`. Establish `hb : g b = 1`. Use `hone b (List.mem_cons.mpr (Or.inl rfl)) ?_` and prove the remaining obligations. Introduce `hba`. Conclude with `absurd (show b ∈ L by rw [hba]; exact h) (List.nodup_cons.mp hnd).1`.

Rewrite using `[hb, one_mul]`. Conclude with `ih a (List.nodup_cons.mp hnd).2 h (fun c hc => hone c (List.mem_cons.mpr (Or.inr hc)))`.
-/
private theorem prod_map_eq_apply_of_nodup_of_forall_ne {α : Type*} {M : Type*} [CommMonoid M]
    (g : α → M) : ∀ (L : List α) (a : α), L.Nodup → a ∈ L →
      (∀ b ∈ L, b ≠ a → g b = 1) → (L.map g).prod = g a := by
  intro L
  induction L with
  | nil =>
      intro a _ ha _
      simp at ha
  | cons b L ih =>
      intro a hnd ha hone
      rw [List.map_cons, List.prod_cons]
      rcases List.mem_cons.mp ha with h | h
      · have hL : (L.map g).prod = 1 := by
          refine prod_map_eq_one_of_forall_eq_one g L ?_
          intro c hc
          refine hone c (List.mem_cons.mpr (Or.inr hc)) ?_
          intro hca
          exact absurd (show b ∈ L by rw [← h, ← hca]; exact hc) (List.nodup_cons.mp hnd).1
        rw [hL, mul_one, h]
      · have hb : g b = 1 := by
          refine hone b (List.mem_cons.mpr (Or.inl rfl)) ?_
          intro hba
          exact absurd (show b ∈ L by rw [hba]; exact h) (List.nodup_cons.mp hnd).1
        rw [hb, one_mul]
        exact ih a (List.nodup_cons.mp hnd).2 h
          (fun c hc => hone c (List.mem_cons.mpr (Or.inr hc)))

/- English proof (translation)
Establish `hmemiff : ∀ C' : Set X, C' ∈ supportComponentsFinset D ↔ IsIrreducibleComponentOfSupport D C'`. Introduce `C'`. Simplify using `only [supportComponentsFinset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]`. Establish `hCS : C ∈ supportComponentsFinset D` using `(hmemiff C).mpr hC`. Establish `hCpart : stalkIdeal (componentPowerIdeal I D C) x = stalkIdeal D x ^ orderAlongComponent I hC.isIrreducible` using `stalkIdeal_componentPowerIdeal_of_mem p I hD hC hx`.

Use `le_antisymm ?_ ?_` and prove the remaining obligations. Establish `h1 : monomialPartAlongDivisor I D ≤ componentPowerIdeal I D C`. Rewrite using `[monomialPartAlongDivisor_eq_inf_componentPowerIdeal]`. Conclude with `Finset.inf_le hCS`. Establish `h2` using `stalkIdeal_mono h1 x`.

Rewrite `h2` using `[hCpart]`. Then use the resulting hypothesis. Establish `hle : ((supportComponentsFinset D).toList.map (fun C' => componentPowerIdeal I D C')).prod ≤ monomialPartAlongDivisor I D`. Rewrite using `[monomialPartAlongDivisor_eq_inf_componentPowerIdeal]`. Use `Finset.le_inf ?_` and prove the remaining obligations. Introduce `C' hC'`.

Conclude with `idealSheafData_listProd_le_of_mem _ (componentPowerIdeal I D C') (List.mem_map.mpr ⟨C', Finset.mem_toList.mpr hC', rfl⟩)`. Establish `hprod : stalkIdeal ((supportComponentsFinset D).toList.map (fun C' => componentPowerIdeal I D C')).prod x = stalkIdeal (componentPowerIdeal I D C) x`. Rewrite using `[stalkIdeal_listProd, List.map_map]`. Use `prod_map_eq_apply_of_nodup_of_forall_ne (fun C' => stalkIdeal (componentPowerIdeal I D C') x) ((supportComponentsFinset D).toList) C (Finset.nodup_toList _) (Finset.mem_toList.mpr hCS) ?_` and prove the remaining obligations. Introduce `C' hC' hne`.

Use `show stalkIdeal (componentPowerIdeal I D C') x = 1`. Establish `hC'comp : IsIrreducibleComponentOfSupport D C'` using `(hmemiff C').mp (Finset.mem_toList.mp hC')`. Establish `hdisj : Disjoint C C'` using `hC.disjoint hC'comp p hD (Ne.symm hne)`. Establish `hxC' : x ∉ C'` using `Set.disjoint_left.mp hdisj hx`. Rewrite using `[stalkIdeal_componentPowerIdeal_of_not_mem I D C' hxC', Ideal.one_eq_top]`.

Establish `h3` using `stalkIdeal_mono hle x`. Rewrite `h3` using `[hprod, hCpart]`. Conclude with `h3`.
-/
theorem stalkIdeal_monomialPartAlongDivisor_of_mem [TopologicalSpace.NoetherianSpace ↥X]
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) {D : X.IdealSheafData}
    (hD : IsEtaleLocallyCoordinateDivisor p D) {C : Set X} (hC : IsIrreducibleComponentOfSupport D C) {x : X}
    (hx : x ∈ C) :
    stalkIdeal (monomialPartAlongDivisor I D) x = stalkIdeal D x ^ orderAlongComponent I hC.isIrreducible := by
  classical
  have hmemiff : ∀ C' : Set X, C' ∈ supportComponentsFinset D ↔ IsIrreducibleComponentOfSupport D C' := by
    intro C'
    simp only [supportComponentsFinset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hCS : C ∈ supportComponentsFinset D := (hmemiff C).mpr hC
  have hCpart : stalkIdeal (componentPowerIdeal I D C) x
      = stalkIdeal D x ^ orderAlongComponent I hC.isIrreducible :=
    stalkIdeal_componentPowerIdeal_of_mem p I hD hC hx
  refine le_antisymm ?_ ?_
  · have h1 : monomialPartAlongDivisor I D ≤ componentPowerIdeal I D C := by
      rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
      exact Finset.inf_le hCS
    have h2 := stalkIdeal_mono h1 x
    rwa [hCpart] at h2
  · have hle : ((supportComponentsFinset D).toList.map (fun C' => componentPowerIdeal I D C')).prod
        ≤ monomialPartAlongDivisor I D := by
      rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
      refine Finset.le_inf ?_
      intro C' hC'
      exact idealSheafData_listProd_le_of_mem _ (componentPowerIdeal I D C')
        (List.mem_map.mpr ⟨C', Finset.mem_toList.mpr hC', rfl⟩)
    have hprod : stalkIdeal
        ((supportComponentsFinset D).toList.map (fun C' => componentPowerIdeal I D C')).prod x
        = stalkIdeal (componentPowerIdeal I D C) x := by
      rw [stalkIdeal_listProd, List.map_map]
      refine prod_map_eq_apply_of_nodup_of_forall_ne (fun C' => stalkIdeal (componentPowerIdeal I D C') x)
        ((supportComponentsFinset D).toList) C (Finset.nodup_toList _)
        (Finset.mem_toList.mpr hCS) ?_
      intro C' hC' hne
      show stalkIdeal (componentPowerIdeal I D C') x = 1
      have hC'comp : IsIrreducibleComponentOfSupport D C' := (hmemiff C').mp (Finset.mem_toList.mp hC')
      have hdisj : Disjoint C C' := hC.disjoint hC'comp p hD (Ne.symm hne)
      have hxC' : x ∉ C' := Set.disjoint_left.mp hdisj hx
      rw [stalkIdeal_componentPowerIdeal_of_not_mem I D C' hxC', Ideal.one_eq_top]
    have h3 := stalkIdeal_mono hle x
    rw [hprod, hCpart] at h3
    exact h3

def monomialFactorIdeal [TopologicalSpace.NoetherianSpace ↥X] (E : List X.IdealSheafData)
    (I : X.IdealSheafData) : X.IdealSheafData :=
  (E.map (fun D => monomialPartAlongDivisor I D)).prod

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem monomialFactorIdeal_eq_prod_monomialPartAlongDivisor [TopologicalSpace.NoetherianSpace ↥X] (E : List X.IdealSheafData)
    (I : X.IdealSheafData) :
    monomialFactorIdeal E I = (E.map (fun D => monomialPartAlongDivisor I D)).prod := rfl

/- English proof (translation)
Establish `h : monomialFactorIdeal E I = (E.map (fun D => monomialPartAlongDivisor I D)).prod` using `rfl`. Rewrite using `[h, stalkIdeal_listProd, List.map_map]`. Both sides reduce to the same expression.
-/
theorem stalkIdeal_monomialFactorIdeal [TopologicalSpace.NoetherianSpace ↥X]
    (E : List X.IdealSheafData) (I : X.IdealSheafData) (x : X) :
    stalkIdeal (monomialFactorIdeal E I) x =
      (E.map (fun D => stalkIdeal (monomialPartAlongDivisor I D) x)).prod := by
  have h : monomialFactorIdeal E I = (E.map (fun D => monomialPartAlongDivisor I D)).prod := rfl
  rw [h, stalkIdeal_listProd, List.map_map]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem idealSheafData_ideal_mul (I J : X.IdealSheafData) (W : X.affineOpens) :
    (I * J).ideal W = I.ideal W * J.ideal W := rfl

/- English proof (translation)
The claim follows from `(Ideal.eq_top_iff_one _).mpr (by simp)`.
-/
private theorem idealSheafData_ideal_top (W : X.affineOpens) :
    (⊤ : X.IdealSheafData).ideal W = ⊤ :=
  (Ideal.eq_top_iff_one _).mpr (by simp)

/- English proof (translation)
Rewrite using `[Ideal.one_eq_top]`. Conclude with `idealSheafData_ideal_top W`.
-/
private theorem idealSheafData_ideal_one (W : X.affineOpens) :
    (1 : X.IdealSheafData).ideal W = 1 := by
  rw [Ideal.one_eq_top]
  exact idealSheafData_ideal_top W

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_zero]`. Conclude with `idealSheafData_ideal_one W`. Consider the case `succ n ih => rw [pow_succ, pow_succ, idealSheafData_ideal_mul, ih]`.
-/
private theorem idealSheafData_ideal_pow (J : X.IdealSheafData) (n : ℕ)
    (W : X.affineOpens) : (J ^ n).ideal W = J.ideal W ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact idealSheafData_ideal_one W
  | succ n ih => rw [pow_succ, pow_succ, idealSheafData_ideal_mul, ih]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => rw [List.prod_nil, List.map_nil, List.prod_nil]`. Conclude with `idealSheafData_ideal_one W`. Consider the case `cons J L ih`. Rewrite using `[List.prod_cons, List.map_cons, List.prod_cons, idealSheafData_ideal_mul, ih]`.
-/
private theorem idealSheafData_ideal_listProd (L : List X.IdealSheafData) (W : X.affineOpens) :
    L.prod.ideal W = (L.map (fun J => J.ideal W)).prod := by
  induction L with
  | nil => rw [List.prod_nil, List.map_nil, List.prod_nil]; exact idealSheafData_ideal_one W
  | cons J L ih =>
      rw [List.prod_cons, List.map_cons, List.prod_cons, idealSheafData_ideal_mul, ih]

/- English proof (translation)
Use `(Ideal.eq_top_iff_one _).mpr ?_` and prove the remaining obligations. Rewrite using `[Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]`. Introduce `q hq`. Establish `hqC : (W.2.fromSpec).base q ∈ C` using `hq`. Establish `hmem0 : (W.2.fromSpec).base q ∈ ((W : X.Opens) : Set ↥X)`.

Rewrite using `[← AlgebraicGeometry.IsAffineOpen.range_fromSpec W.2]`. Conclude with `Set.mem_range_self q`. Establish `hmem : (W.2.fromSpec).base q ∈ (W : X.Opens)` using `hmem0`. Conclude with `absurd hqC (h _ hmem)`.
-/
private theorem ideal_vanishingIdeal_eq_top_of_disjoint (C : Set X) (hCcl : IsClosed C) (W : X.affineOpens)
    (h : ∀ y : X, y ∈ (W : X.Opens) → y ∉ C) :
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨C, hCcl⟩ : TopologicalSpace.Closeds ↥X)).ideal W = ⊤ := by
  refine (Ideal.eq_top_iff_one _).mpr ?_
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  intro q hq
  have hqC : (W.2.fromSpec).base q ∈ C := hq
  have hmem0 : (W.2.fromSpec).base q ∈ ((W : X.Opens) : Set ↥X) := by
    rw [← AlgebraicGeometry.IsAffineOpen.range_fromSpec W.2]
    exact Set.mem_range_self q
  have hmem : (W.2.fromSpec).base q ∈ (W : X.Opens) := hmem0
  exact absurd hqC (h _ hmem)

/- English proof (translation)
Distinguish the cases in `hC : IsIrreducibleComponentOfSupport D C`. Rewrite using `[componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC, idealSheafData_ideal_pow, ideal_vanishingIdeal_eq_top_of_disjoint C hC.isClosed W h, ← Ideal.one_eq_top, one_pow]`. Rewrite using `[componentPowerIdeal_of_not_isIrreducibleComponentOfSupport I D hC]`. Conclude with `idealSheafData_ideal_top W`.
-/
private theorem ideal_componentPowerIdeal_eq_top_of_disjoint (I D : X.IdealSheafData) (C : Set X)
    (W : X.affineOpens) (h : ∀ y : X, y ∈ (W : X.Opens) → y ∉ C) :
    (componentPowerIdeal I D C).ideal W = ⊤ := by
  by_cases hC : IsIrreducibleComponentOfSupport D C
  · rw [componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC, idealSheafData_ideal_pow,
      ideal_vanishingIdeal_eq_top_of_disjoint C hC.isClosed W h, ← Ideal.one_eq_top, one_pow]
  · rw [componentPowerIdeal_of_not_isIrreducibleComponentOfSupport I D hC]
    exact idealSheafData_ideal_top W

/- English proof (translation)
Establish `hmemiff : ∀ C' : Set X, C' ∈ supportComponentsFinset D ↔ IsIrreducibleComponentOfSupport D C'`. Introduce `C'`. Simplify using `only [supportComponentsFinset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]`. Establish `hprodle : ∀ W : X.affineOpens, (((supportComponentsFinset D).toList.map (fun C => componentPowerIdeal I D C)).prod).ideal W ≤ (monomialPartAlongDivisor I D).ideal W`. Introduce `W`.

Establish `hle : ((supportComponentsFinset D).toList.map (fun C => componentPowerIdeal I D C)).prod ≤ monomialPartAlongDivisor I D`. Rewrite using `[monomialPartAlongDivisor_eq_inf_componentPowerIdeal]`. Use `Finset.le_inf ?_` and prove the remaining obligations. Introduce `C' hC'`. Conclude with `idealSheafData_listProd_le_of_mem _ (componentPowerIdeal I D C') (List.mem_map.mpr ⟨C', Finset.mem_toList.mpr hC', rfl⟩)`.

Conclude with `hle W`. Distinguish the cases in `hx : ∃ C ∈ supportComponentsFinset D, x ∈ C`. Take `⟨C₀, hC₀mem, hxC₀⟩` from `hx`. Establish `hC₀ : IsIrreducibleComponentOfSupport D C₀` using `(hmemiff C₀).mp hC₀mem`. Take `⟨V, hV, hxV, n, c, j, hDV, hVsupp, -, hagree, -⟩` from `hC₀.exists_affineOpen_etaleChart_coordIdeal p hD x hxC₀`.

Use `⟨V, hxV, ?_⟩` and prove the remaining obligations. Introduce `W hWV`. Use `⟨(c.restrict hWV).coord j ^ orderAlongComponent I hC₀.isIrreducible, pow_mem (coord_mem_nonZeroDivisors W.2 (c.restrict hWV) j) _, ?_⟩` and prove the remaining obligations. Establish `hres : restrictIdeal D (W : X.Opens) = (c.restrict hWV).coordIdeal {j}` using `restrictIdeal_eq_restrict_coordIdeal_of_le hWV c D {j} hDV`. Establish `hDW : D.ideal W = Ideal.span {(c.restrict hWV).coord j}`.

Establish `h1` using `EtaleChart.ideal_eq_span_coord (c.restrict hWV) W.2 D {j} hres`. Simplify using `using h1`. Establish `hcomp0 : (componentPowerIdeal I D C₀).ideal W = Ideal.span {(c.restrict hWV).coord j ^ orderAlongComponent I hC₀.isIrreducible}`. Rewrite using `[componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC₀, idealSheafData_ideal_pow, hagree W hWV, hDW, Ideal.span_singleton_pow]`. Establish `hother : ∀ C : Set X, C ∈ (supportComponentsFinset D).toList → C ≠ C₀ → (componentPowerIdeal I D C).ideal W = ⊤`.

Introduce `C hCmem hne`. Establish `hCcomp : IsIrreducibleComponentOfSupport D C` using `(hmemiff C).mp (Finset.mem_toList.mp hCmem)`. Use `ideal_componentPowerIdeal_eq_top_of_disjoint I D C W ?_` and prove the remaining obligations. Introduce `y hy hyC`. Establish `hyV : y ∈ V` using `hWV hy`.

Establish `hyD : y ∈ (D.support : Set X)` using `hCcomp.subset_support hyC`. Establish `hyC₀ : y ∈ C₀` using `hVsupp y hyV hyD`. Establish `hdisj : Disjoint C C₀` using `hCcomp.disjoint hC₀ p hD hne`. Conclude with `(Set.disjoint_left.mp hdisj hyC) hyC₀`. Establish `hprodideal : (((supportComponentsFinset D).toList.map (fun C => componentPowerIdeal I D C)).prod).ideal W = (componentPowerIdeal I D C₀).ideal W`.

Rewrite using `[idealSheafData_ideal_listProd, List.map_map]`. Use `prod_map_eq_apply_of_nodup_of_forall_ne (fun C => (componentPowerIdeal I D C).ideal W) ((supportComponentsFinset D).toList) C₀ (Finset.nodup_toList _) (Finset.mem_toList.mpr hC₀mem) ?_` and prove the remaining obligations. Introduce `C' hC' hne`. Use `show (componentPowerIdeal I D C').ideal W = 1`. Rewrite using `[Ideal.one_eq_top]`.

Conclude with `hother C' hC' hne`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Rewrite using `[← hcomp0]`. Establish `hle : monomialPartAlongDivisor I D ≤ componentPowerIdeal I D C₀`. Rewrite using `[monomialPartAlongDivisor_eq_inf_componentPowerIdeal]`.

Conclude with `Finset.inf_le hC₀mem`. Conclude with `hle W`. Rewrite using `[← hcomp0, ← hprodideal]`. Conclude with `hprodle W`. Use `push Not at hx`.

Establish `hclosed : IsClosed (⋃ C ∈ (supportComponentsFinset D : Set (Set X)), C)`. Use `Set.Finite.isClosed_biUnion (supportComponentsFinset D).finite_toSet ?_` and prove the remaining obligations. Introduce `C hC`. Conclude with `((hmemiff C).mp (Finset.mem_coe.mp hC)).isClosed`. Use `⟨⟨(⋃ C ∈ (supportComponentsFinset D : Set (Set X)), C)ᶜ, hclosed.isOpen_compl⟩, ?_, ?_⟩` and prove the remaining obligations.

Introduce `hmem`. Rewrite `hmem` using `[Set.mem_iUnion₂]`. Take `⟨C, hC, hxC⟩` from `hmem`. Conclude with `hx C (Finset.mem_coe.mp hC) hxC`. Introduce `W hWΩ`.

Use `⟨1, one_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_one]`. Establish `hall : ∀ C ∈ (supportComponentsFinset D).toList, (componentPowerIdeal I D C).ideal W = 1`. Introduce `C hC`. Rewrite using `[Ideal.one_eq_top]`.

Use `ideal_componentPowerIdeal_eq_top_of_disjoint I D C W ?_` and prove the remaining obligations. Introduce `y hy hyC`. Establish `hyS : y ∈ (⋃ C' ∈ (supportComponentsFinset D : Set (Set X)), C')` using `Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_toList.mp hC)) hyC`. Conclude with `absurd hyS (hWΩ hy)`. Establish `hprodtop : (((supportComponentsFinset D).toList.map (fun C => componentPowerIdeal I D C)).prod).ideal W = ⊤`.

Rewrite using `[idealSheafData_ideal_listProd, List.map_map, ← Ideal.one_eq_top]`. Conclude with `prod_map_eq_one_of_forall_eq_one (fun C => (componentPowerIdeal I D C).ideal W) ((supportComponentsFinset D).toList) hall`. Use `le_antisymm le_top ?_` and prove the remaining obligations. Rewrite using `[← hprodtop]`. Conclude with `hprodle W`.
-/
private theorem exists_nhds_ideal_monomialPartAlongDivisor_eq_span [TopologicalSpace.NoetherianSpace ↥X]
    (p : X ⟶ Spec (CommRingCat.of k)) (I D : X.IdealSheafData)
    (hD : IsEtaleLocallyCoordinateDivisor p D) (x : X) :
    ∃ Ω : X.Opens, x ∈ Ω ∧ ∀ W : X.affineOpens, (W : X.Opens) ≤ Ω →
      ∃ g ∈ nonZeroDivisors Γ(X, (W : X.Opens)),
        (monomialPartAlongDivisor I D).ideal W = Ideal.span {g} := by
  classical
  have hmemiff : ∀ C' : Set X, C' ∈ supportComponentsFinset D ↔ IsIrreducibleComponentOfSupport D C' := by
    intro C'
    simp only [supportComponentsFinset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hprodle : ∀ W : X.affineOpens,
      (((supportComponentsFinset D).toList.map (fun C => componentPowerIdeal I D C)).prod).ideal W
        ≤ (monomialPartAlongDivisor I D).ideal W := by
    intro W
    have hle : ((supportComponentsFinset D).toList.map (fun C => componentPowerIdeal I D C)).prod
        ≤ monomialPartAlongDivisor I D := by
      rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
      refine Finset.le_inf ?_
      intro C' hC'
      exact idealSheafData_listProd_le_of_mem _ (componentPowerIdeal I D C')
        (List.mem_map.mpr ⟨C', Finset.mem_toList.mpr hC', rfl⟩)
    exact hle W
  by_cases hx : ∃ C ∈ supportComponentsFinset D, x ∈ C
  · obtain ⟨C₀, hC₀mem, hxC₀⟩ := hx
    have hC₀ : IsIrreducibleComponentOfSupport D C₀ := (hmemiff C₀).mp hC₀mem
    obtain ⟨V, hV, hxV, n, c, j, hDV, hVsupp, -, hagree, -⟩ :=
      hC₀.exists_affineOpen_etaleChart_coordIdeal p hD x hxC₀
    refine ⟨V, hxV, ?_⟩
    intro W hWV
    refine ⟨(c.restrict hWV).coord j ^ orderAlongComponent I hC₀.isIrreducible,
      pow_mem (coord_mem_nonZeroDivisors W.2 (c.restrict hWV) j) _, ?_⟩
    have hres : restrictIdeal D (W : X.Opens) = (c.restrict hWV).coordIdeal {j} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hWV c D {j} hDV
    have hDW : D.ideal W = Ideal.span {(c.restrict hWV).coord j} := by
      have h1 := EtaleChart.ideal_eq_span_coord (c.restrict hWV) W.2 D {j} hres
      simpa using h1
    have hcomp0 : (componentPowerIdeal I D C₀).ideal W
        = Ideal.span {(c.restrict hWV).coord j ^ orderAlongComponent I hC₀.isIrreducible} := by
      rw [componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC₀, idealSheafData_ideal_pow,
        hagree W hWV, hDW, Ideal.span_singleton_pow]
    have hother : ∀ C : Set X, C ∈ (supportComponentsFinset D).toList → C ≠ C₀ →
        (componentPowerIdeal I D C).ideal W = ⊤ := by
      intro C hCmem hne
      have hCcomp : IsIrreducibleComponentOfSupport D C := (hmemiff C).mp (Finset.mem_toList.mp hCmem)
      refine ideal_componentPowerIdeal_eq_top_of_disjoint I D C W ?_
      intro y hy hyC
      have hyV : y ∈ V := hWV hy
      have hyD : y ∈ (D.support : Set X) := hCcomp.subset_support hyC
      have hyC₀ : y ∈ C₀ := hVsupp y hyV hyD
      have hdisj : Disjoint C C₀ := hCcomp.disjoint hC₀ p hD hne
      exact (Set.disjoint_left.mp hdisj hyC) hyC₀
    have hprodideal : (((supportComponentsFinset D).toList.map
        (fun C => componentPowerIdeal I D C)).prod).ideal W = (componentPowerIdeal I D C₀).ideal W := by
      rw [idealSheafData_ideal_listProd, List.map_map]
      refine prod_map_eq_apply_of_nodup_of_forall_ne (fun C => (componentPowerIdeal I D C).ideal W)
        ((supportComponentsFinset D).toList) C₀ (Finset.nodup_toList _)
        (Finset.mem_toList.mpr hC₀mem) ?_
      intro C' hC' hne
      show (componentPowerIdeal I D C').ideal W = 1
      rw [Ideal.one_eq_top]
      exact hother C' hC' hne
    refine le_antisymm ?_ ?_
    · rw [← hcomp0]
      have hle : monomialPartAlongDivisor I D ≤ componentPowerIdeal I D C₀ := by
        rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
        exact Finset.inf_le hC₀mem
      exact hle W
    · rw [← hcomp0, ← hprodideal]
      exact hprodle W
  · push Not at hx
    have hclosed : IsClosed (⋃ C ∈ (supportComponentsFinset D : Set (Set X)), C) := by
      refine Set.Finite.isClosed_biUnion (supportComponentsFinset D).finite_toSet ?_
      intro C hC
      exact ((hmemiff C).mp (Finset.mem_coe.mp hC)).isClosed
    refine ⟨⟨(⋃ C ∈ (supportComponentsFinset D : Set (Set X)), C)ᶜ, hclosed.isOpen_compl⟩, ?_, ?_⟩
    · intro hmem
      rw [Set.mem_iUnion₂] at hmem
      obtain ⟨C, hC, hxC⟩ := hmem
      exact hx C (Finset.mem_coe.mp hC) hxC
    · intro W hWΩ
      refine ⟨1, one_mem _, ?_⟩
      rw [Ideal.span_singleton_one]
      have hall : ∀ C ∈ (supportComponentsFinset D).toList,
          (componentPowerIdeal I D C).ideal W = 1 := by
        intro C hC
        rw [Ideal.one_eq_top]
        refine ideal_componentPowerIdeal_eq_top_of_disjoint I D C W ?_
        intro y hy hyC
        have hyS : y ∈ (⋃ C' ∈ (supportComponentsFinset D : Set (Set X)), C') :=
          Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_toList.mp hC)) hyC
        exact absurd hyS (hWΩ hy)
      have hprodtop : (((supportComponentsFinset D).toList.map
          (fun C => componentPowerIdeal I D C)).prod).ideal W = ⊤ := by
        rw [idealSheafData_ideal_listProd, List.map_map, ← Ideal.one_eq_top]
        exact prod_map_eq_one_of_forall_eq_one (fun C => (componentPowerIdeal I D C).ideal W)
          ((supportComponentsFinset D).toList) hall
      refine le_antisymm le_top ?_
      rw [← hprodtop]
      exact hprodle W

/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil`. Introduce `_`. Use `⟨⊤, trivial, ?_⟩` and prove the remaining obligations.

Introduce `W _`. Use `⟨1, one_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[List.map_nil, List.prod_nil, Ideal.span_singleton_one]`. Conclude with `idealSheafData_ideal_top W`. Consider the case `cons D L ih`.

Introduce `hmem`. Take `⟨Ω₁, hxΩ₁, h₁⟩` from `exists_nhds_ideal_monomialPartAlongDivisor_eq_span p I D (hmem D (List.mem_cons.mpr (Or.inl rfl))) x`. Take `⟨Ω₂, hxΩ₂, h₂⟩` from `ih (fun D' hD' => hmem D' (List.mem_cons.mpr (Or.inr hD')))`. Use `⟨Ω₁ ⊓ Ω₂, ⟨hxΩ₁, hxΩ₂⟩, ?_⟩` and prove the remaining obligations. Introduce `W hW`.

Take `⟨g₁, hg₁, he₁⟩` from `h₁ W (le_trans hW inf_le_left)`. Take `⟨g₂, hg₂, he₂⟩` from `h₂ W (le_trans hW inf_le_right)`. Use `⟨g₁ * g₂, mul_mem hg₁ hg₂, ?_⟩` and prove the remaining obligations. Rewrite using `[List.map_cons, List.prod_cons, idealSheafData_ideal_mul, he₁, he₂, Ideal.span_singleton_mul_span_singleton]`.
-/
private theorem exists_prod_monomialPartAlongDivisor_eq_span_singleton [TopologicalSpace.NoetherianSpace ↥X]
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (x : X) :
    ∀ L : List X.IdealSheafData, (∀ D ∈ L, IsEtaleLocallyCoordinateDivisor p D) →
      ∃ Ω : X.Opens, x ∈ Ω ∧ ∀ W : X.affineOpens, (W : X.Opens) ≤ Ω →
        ∃ g ∈ nonZeroDivisors Γ(X, (W : X.Opens)),
          ((L.map (fun D => monomialPartAlongDivisor I D)).prod).ideal W = Ideal.span {g} := by
  intro L
  induction L with
  | nil =>
      intro _
      refine ⟨⊤, trivial, ?_⟩
      intro W _
      refine ⟨1, one_mem _, ?_⟩
      rw [List.map_nil, List.prod_nil, Ideal.span_singleton_one]
      exact idealSheafData_ideal_top W
  | cons D L ih =>
      intro hmem
      obtain ⟨Ω₁, hxΩ₁, h₁⟩ := exists_nhds_ideal_monomialPartAlongDivisor_eq_span p I D
        (hmem D (List.mem_cons.mpr (Or.inl rfl))) x
      obtain ⟨Ω₂, hxΩ₂, h₂⟩ := ih (fun D' hD' => hmem D' (List.mem_cons.mpr (Or.inr hD')))
      refine ⟨Ω₁ ⊓ Ω₂, ⟨hxΩ₁, hxΩ₂⟩, ?_⟩
      intro W hW
      obtain ⟨g₁, hg₁, he₁⟩ := h₁ W (le_trans hW inf_le_left)
      obtain ⟨g₂, hg₂, he₂⟩ := h₂ W (le_trans hW inf_le_right)
      refine ⟨g₁ * g₂, mul_mem hg₁ hg₂, ?_⟩
      rw [List.map_cons, List.prod_cons, idealSheafData_ideal_mul, he₁, he₂,
        Ideal.span_singleton_mul_span_singleton]

/- English proof (translation)
Introduce `x`. Take `⟨Ω, hxΩ, hΩ⟩` from `exists_prod_monomialPartAlongDivisor_eq_span_singleton p I x E (fun D hD => isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE D hD)`. Take `⟨U, hxU⟩` from `Scheme.exists_affineOpens_mem x`. Establish `hU : IsAffineOpen (U : X.Opens)` using `U.2`. Take `⟨f, hfle, hxf⟩` from `hU.exists_basicOpen_le (⟨x, hxΩ⟩ : ↥Ω) hxU`.

Take `⟨g, hg, hgeq⟩` from `hΩ (X.affineBasicOpen f) hfle`. Use `⟨X.affineBasicOpen f, g, hxf, hg, ?_⟩` and prove the remaining obligations. Rewrite using `[monomialFactorIdeal_eq_prod_monomialPartAlongDivisor]`. Conclude with `hgeq`.
-/
theorem isLocallyGeneratedByNonZeroDivisor_monomialFactorIdeal [TopologicalSpace.NoetherianSpace ↥X]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (I : X.IdealSheafData)
    (hE : InStrictNormalCrossingPosition p E) : Blowup.IsLocallyGeneratedByNonZeroDivisor (monomialFactorIdeal E I) := by
  intro x
  obtain ⟨Ω, hxΩ, hΩ⟩ := exists_prod_monomialPartAlongDivisor_eq_span_singleton p I x E
    (fun D hD => isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE D hD)
  obtain ⟨U, hxU⟩ := Scheme.exists_affineOpens_mem x
  have hU : IsAffineOpen (U : X.Opens) := U.2
  obtain ⟨f, hfle, hxf⟩ := hU.exists_basicOpen_le (⟨x, hxΩ⟩ : ↥Ω) hxU
  obtain ⟨g, hg, hgeq⟩ := hΩ (X.affineBasicOpen f) hfle
  refine ⟨X.affineBasicOpen f, g, hxf, hg, ?_⟩
  rw [monomialFactorIdeal_eq_prod_monomialPartAlongDivisor]
  exact hgeq

/- English proof (translation)
Rewrite using `[Nat.cast_succ]`. Conclude with `ENat.natCast_add_one_le_iff.2 (not_le.mp h)`.
-/
private theorem natCast_add_one_le_of_not_le (n : ℕ) (b : ℕ∞) (h : ¬ b ≤ (n : ℕ∞)) :
    ((n + 1 : ℕ) : ℕ∞) ≤ b := by
  rw [Nat.cast_succ]
  exact ENat.natCast_add_one_le_iff.2 (not_le.mp h)

/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil`. Introduce `i hi`. Conclude with `absurd hi (by simp only [List.length_nil]; omega)`.

Consider the case `cons b L ih`. Introduce `i hi hone`. Consider the cases of `i with`. Consider the case `zero`. Establish `h1 : (L.map g).prod = 1`.

Use `prod_map_eq_one_of_forall_eq_one g L ?_` and prove the remaining obligations. Introduce `y hy`. Take `⟨j, hj, hjy⟩` from `List.getElem_of_mem hy`. Establish `h2` using `hone (j + 1) (by simp only [List.length_cons]; omega) (by omega)`. Rewrite using `[← hjy]`.

Simplify using `using h2`. Use `show (List.map g (b :: L)).prod = g b`. Rewrite using `[List.map_cons, List.prod_cons, h1, mul_one]`. Consider the case `succ i`. Establish `hi' : i < L.length`.

Simplify using `only [List.length_cons] at hi`. Use linear arithmetic over natural numbers and integers. Establish `hb : g b = 1`. Establish `h0` using `hone 0 (by simp only [List.length_cons]; omega) (by omega)`. Simplify using `using h0`.

Establish `hrest : (L.map g).prod = g L[i]`. Use `ih i hi' ?_` and prove the remaining obligations. Introduce `j hj hji`. Establish `h2` using `hone (j + 1) (by simp only [List.length_cons]; omega) (by omega)`. Simplify using `using h2`.

Use `show (List.map g (b :: L)).prod = g L[i]`. Rewrite using `[List.map_cons, List.prod_cons, hb, one_mul]`. Conclude with `hrest`.
-/
private theorem prod_map_eq_apply_getElem_of_forall_ne {α : Type*} {M : Type*} [CommMonoid M] (g : α → M) :
    ∀ (L : List α) (i : ℕ) (hi : i < L.length),
      (∀ (j : ℕ) (hj : j < L.length), j ≠ i → g L[j] = 1) → (L.map g).prod = g L[i] := by
  intro L
  induction L with
  | nil =>
      intro i hi
      exact absurd hi (by simp only [List.length_nil]; omega)
  | cons b L ih =>
      intro i hi hone
      cases i with
      | zero =>
          have h1 : (L.map g).prod = 1 := by
            refine prod_map_eq_one_of_forall_eq_one g L ?_
            intro y hy
            obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem hy
            have h2 := hone (j + 1) (by simp only [List.length_cons]; omega) (by omega)
            rw [← hjy]
            simpa using h2
          show (List.map g (b :: L)).prod = g b
          rw [List.map_cons, List.prod_cons, h1, mul_one]
      | succ i =>
          have hi' : i < L.length := by
            simp only [List.length_cons] at hi
            omega
          have hb : g b = 1 := by
            have h0 := hone 0 (by simp only [List.length_cons]; omega) (by omega)
            simpa using h0
          have hrest : (L.map g).prod = g L[i] := by
            refine ih i hi' ?_
            intro j hj hji
            have h2 := hone (j + 1) (by simp only [List.length_cons]; omega) (by omega)
            simpa using h2
          show (List.map g (b :: L)).prod = g L[i]
          rw [List.map_cons, List.prod_cons, hb, one_mul]
          exact hrest

/- English proof (translation)
Establish `hDspan : stalkIdeal D x = Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord t)} : Set (X.presheaf.stalk x))` using `stalkIdeal_eq_span_germ_coord p hV c t D hDV x hx`. Establish `hD'span : stalkIdeal D' x = Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord s)} : Set (X.presheaf.stalk x))` using `stalkIdeal_eq_span_germ_coord p hV c s D' hD'V x hx`. Establish `hle : stalkIdeal D' x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x)` using `(mem_support_iff_stalkIdeal_le_maximalIdeal D' x).mp hxD'`. Establish `hmem : (X.presheaf.germ V x hx).hom (c.coord s) ∈ stalkIdeal D x`. Rewrite using `[hmax]`.

Use `hle ?_` and prove the remaining obligations. Rewrite using `[hD'span]`. Conclude with `Ideal.mem_span_singleton_self _`. Rewrite `hmem` using `[hDspan, Ideal.mem_span_singleton']`. Take `⟨g, hg⟩` from `hmem`.

Set `: Algebra Γ(X, V) (X.presheaf.stalk x)` to `(X.presheaf.germ V x hx).hom.toAlgebra`. Establish `hlocz : IsLocalization (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (X.presheaf.stalk x)` using `hV.isLocalization_stalk ⟨x, hx⟩`. Establish `halg : (algebraMap Γ(X, V) (X.presheaf.stalk x)) = (X.presheaf.germ V x hx).hom` using `rfl`. Take `⟨w, hw⟩` from `IsLocalization.surj (M := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) g`. Establish `hw' : g * (X.presheaf.germ V x hx).hom (w.2 : Γ(X, V)) = (X.presheaf.germ V x hx).hom w.1`.

Rewrite using `[← halg]`. Conclude with `hw`. Establish `heq : (algebraMap Γ(X, V) (X.presheaf.stalk x)) ((w.2 : Γ(X, V)) * c.coord s) = (algebraMap Γ(X, V) (X.presheaf.stalk x)) (w.1 * c.coord t)`. Rewrite using `[map_mul, map_mul, halg, ← hg, ← hw']`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨v, hv⟩ : ∃ v : (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl, (v : Γ(X, V)) * ((w.2 : Γ(X, V)) * c.coord s) = (v : Γ(X, V)) * (w.1 * c.coord t)` from `(IsLocalization.eq_iff_exists (M := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) (S := X.presheaf.stalk x)).mp heq`. Establish `hspan : ((v : Γ(X, V)) * (w.2 : Γ(X, V))) ∈ Ideal.span ({c.coord t} : Set Γ(X, V))`. Use `mem_span_coord_of_coord_mul_mem hV c hts ((v : Γ(X, V)) * (w.2 : Γ(X, V))) ?_` and prove the remaining obligations. Establish `hmul : c.coord s * ((v : Γ(X, V)) * (w.2 : Γ(X, V))) = ((v : Γ(X, V)) * w.1) * c.coord t` using `by linear_combination hv`. Rewrite using `[hmul]`.

Conclude with `Ideal.mem_span_singleton'.mpr ⟨(v : Γ(X, V)) * w.1, rfl⟩`. Establish `hunit : IsUnit ((X.presheaf.germ V x hx).hom ((v : Γ(X, V)) * (w.2 : Γ(X, V))))`. Rewrite using `[← halg, map_mul]`. Conclude with `(IsLocalization.map_units (X.presheaf.stalk x) v).mul (IsLocalization.map_units (X.presheaf.stalk x) w.2)`. Establish `hfin : (X.presheaf.germ V x hx).hom ((v : Γ(X, V)) * (w.2 : Γ(X, V))) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)`.

Rewrite using `[← hmax, hDspan]`. Take `⟨z, hz⟩` from `Ideal.mem_span_singleton'.mp hspan`. Use `Ideal.mem_span_singleton'.mpr ⟨(X.presheaf.germ V x hx).hom z, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, hz]`. Conclude with `(mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hfin)) hunit`.
-/
private theorem not_mem_support_of_stalkIdeal_eq_maximalIdeal (p : X ⟶ Spec (CommRingCat.of k))
    {V : X.Opens} (hV : IsAffineOpen V) {m : ℕ} (c : EtaleChart p V m)
    {D D' : X.IdealSheafData} {t s : Fin m} (hts : t ≠ s)
    (hDV : restrictIdeal D V = c.coordIdeal {t})
    (hD'V : restrictIdeal D' V = c.coordIdeal {s})
    {x : ↥X} (hx : x ∈ V)
    (hmax : stalkIdeal D x = IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hxD' : x ∈ D'.support) : False := by
  classical
  have hDspan : stalkIdeal D x =
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord t)} : Set (X.presheaf.stalk x)) :=
    stalkIdeal_eq_span_germ_coord p hV c t D hDV x hx
  have hD'span : stalkIdeal D' x =
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord s)} : Set (X.presheaf.stalk x)) :=
    stalkIdeal_eq_span_germ_coord p hV c s D' hD'V x hx
  have hle : stalkIdeal D' x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (mem_support_iff_stalkIdeal_le_maximalIdeal D' x).mp hxD'
  have hmem : (X.presheaf.germ V x hx).hom (c.coord s) ∈ stalkIdeal D x := by
    rw [hmax]
    refine hle ?_
    rw [hD'span]
    exact Ideal.mem_span_singleton_self _
  rw [hDspan, Ideal.mem_span_singleton'] at hmem
  obtain ⟨g, hg⟩ := hmem
  let : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hx).hom.toAlgebra
  have hlocz : IsLocalization (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) := hV.isLocalization_stalk ⟨x, hx⟩
  have halg : (algebraMap Γ(X, V) (X.presheaf.stalk x)) = (X.presheaf.germ V x hx).hom := rfl
  obtain ⟨w, hw⟩ := IsLocalization.surj
    (M := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) g
  have hw' : g * (X.presheaf.germ V x hx).hom (w.2 : Γ(X, V))
      = (X.presheaf.germ V x hx).hom w.1 := by
    rw [← halg]
    exact hw
  have heq : (algebraMap Γ(X, V) (X.presheaf.stalk x)) ((w.2 : Γ(X, V)) * c.coord s)
      = (algebraMap Γ(X, V) (X.presheaf.stalk x)) (w.1 * c.coord t) := by
    rw [map_mul, map_mul, halg, ← hg, ← hw']
    ring
  obtain ⟨v, hv⟩ : ∃ v : (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl,
      (v : Γ(X, V)) * ((w.2 : Γ(X, V)) * c.coord s)
        = (v : Γ(X, V)) * (w.1 * c.coord t) :=
    (IsLocalization.eq_iff_exists (M := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
      (S := X.presheaf.stalk x)).mp heq
  have hspan : ((v : Γ(X, V)) * (w.2 : Γ(X, V))) ∈ Ideal.span ({c.coord t} : Set Γ(X, V)) := by
    refine mem_span_coord_of_coord_mul_mem hV c hts ((v : Γ(X, V)) * (w.2 : Γ(X, V))) ?_
    have hmul : c.coord s * ((v : Γ(X, V)) * (w.2 : Γ(X, V)))
        = ((v : Γ(X, V)) * w.1) * c.coord t := by linear_combination hv
    rw [hmul]
    exact Ideal.mem_span_singleton'.mpr ⟨(v : Γ(X, V)) * w.1, rfl⟩
  have hunit : IsUnit ((X.presheaf.germ V x hx).hom ((v : Γ(X, V)) * (w.2 : Γ(X, V)))) := by
    rw [← halg, map_mul]
    exact (IsLocalization.map_units (X.presheaf.stalk x) v).mul
      (IsLocalization.map_units (X.presheaf.stalk x) w.2)
  have hfin : (X.presheaf.germ V x hx).hom ((v : Γ(X, V)) * (w.2 : Γ(X, V)))
      ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [← hmax, hDspan]
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hspan
    refine Ideal.mem_span_singleton'.mpr ⟨(X.presheaf.germ V x hx).hom z, ?_⟩
    rw [← map_mul, hz]
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hfin)) hunit

/- English proof (translation)
Take `⟨i0, hi0, hi0D⟩` from `List.getElem_of_mem hD`. Establish `hloc : IsEtaleLocallyCoordinateDivisor p D` using `isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE D hD`. Take `⟨-, hpos⟩` from `(inStrictNormalCrossingPosition_iff p E).mp hE`. Take `⟨U, hηU, m, c, a, hinj, hnone, hsome⟩` from `InStrictNormalCrossingPositionAt.exists_etaleChart (hpos hC.isIrreducible.genericPoint)`. Establish `hmaxD : stalkIdeal D hC.isIrreducible.genericPoint = IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint)` using `stalkIdeal_genericPoint_eq_maximalIdeal p D hloc hC.isIrreducible hC.subset_support hC.maximal`.

Establish `hηD : hC.isIrreducible.genericPoint ∈ D.support` using `hC.genericPoint_mem_support`. Choose the witnesses or unpack the hypotheses as in `⟨t, hat⟩ : ∃ t : Fin m, a i0 = some t := by`. Consider the cases of `hai : a i0 with`. Consider the case `none`. Use `absurd hηD (notMem_support_of_mem_opens_of_restrictIdeal_eq_top D U ?_ _ hηU)` and prove the remaining obligations.

Rewrite using `[← hi0D]`. Conclude with `hnone i0 hi0 hai`. Consider the case `some t`. Use `⟨t, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Establish `hDU : restrictIdeal D U = c.coordIdeal {t}`. Rewrite using `[← hi0D]`. Conclude with `hsome i0 hi0 t hat`. Establish `hother : ∀ (j : ℕ) (hj : j < E.length), j ≠ i0 → hC.isIrreducible.genericPoint ∉ (E[j].support : Set ↥X)`. Introduce `j hj hji0 hmem`.

Consider the cases of `haj : a j with`. Consider the case `none`. Conclude with `notMem_support_of_mem_opens_of_restrictIdeal_eq_top E[j] U (hnone j hj haj) _ hηU hmem`. Consider the case `some s`. Establish `hts : t ≠ s`.

Introduce `h`. Conclude with `hji0 (hinj j hj i0 hi0 t (by rw [haj, h]) hat)`. Establish `hmem' : hC.isIrreducible.genericPoint ∈ E[j].support` using `hmem`. Establish `hxtop : hC.isIrreducible.genericPoint ∈ (⨆ W : X.affineOpens, (W : X.Opens))`. Rewrite using `[AlgebraicGeometry.iSup_affineOpens_eq_top X]`.

Discharge the goal by the elementary cases of `trivial`. Take `⟨W, hηW⟩` from `TopologicalSpace.Opens.mem_iSup.mp hxtop`. Take `⟨f, hfU, hηf⟩` from `W.2.exists_basicOpen_le (⟨hC.isIrreducible.genericPoint, hηU⟩ : ↥U) hηW`. Establish `hηf' : hC.isIrreducible.genericPoint ∈ X.basicOpen f` using `hηf`. Establish `hVaff : IsAffineOpen (X.basicOpen f)` using `W.2.basicOpen f`.

Conclude with `not_mem_support_of_stalkIdeal_eq_maximalIdeal p hVaff (c.restrict hfU) hts (restrictIdeal_eq_restrict_coordIdeal_of_le hfU c D {t} hDU) (restrictIdeal_eq_restrict_coordIdeal_of_le hfU c E[j] {s} (hsome j hj s haj)) hηf' hmaxD hmem'`. Establish `hprod : (E.map (fun D' => stalkIdeal (monomialPartAlongDivisor I D') hC.isIrreducible.genericPoint)).prod = stalkIdeal (monomialPartAlongDivisor I E[i0]) hC.isIrreducible.genericPoint`. Use `prod_map_eq_apply_getElem_of_forall_ne (fun D' => stalkIdeal (monomialPartAlongDivisor I D') hC.isIrreducible.genericPoint) E i0 hi0 ?_` and prove the remaining obligations. Introduce `j hj hji0`. Use `show stalkIdeal (monomialPartAlongDivisor I E[j]) hC.isIrreducible.genericPoint = 1`.

Establish `h1 : stalkIdeal (monomialPartAlongDivisor I E[j]) hC.isIrreducible.genericPoint = ⊤` using `stalkIdeal_monomialPartAlongDivisor_of_not_mem_support I E[j] (hother j hj hji0)`. Rewrite using `[h1, Ideal.one_eq_top]`. Rewrite using `[stalkIdeal_monomialFactorIdeal, hprod, hi0D, stalkIdeal_monomialPartAlongDivisor_of_mem p I hloc hC hC.genericPoint_mem]`.
-/
private theorem stalkIdeal_monomialFactorIdeal_genericPoint [TopologicalSpace.NoetherianSpace ↥X]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (I : X.IdealSheafData)
    (hE : InStrictNormalCrossingPosition p E) {D : X.IdealSheafData} (hD : D ∈ E) {C : Set X}
    (hC : IsIrreducibleComponentOfSupport D C) :
    stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint =
      stalkIdeal D hC.isIrreducible.genericPoint ^ orderAlongComponent I hC.isIrreducible := by
  classical
  obtain ⟨i0, hi0, hi0D⟩ := List.getElem_of_mem hD
  have hloc : IsEtaleLocallyCoordinateDivisor p D := isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE D hD
  obtain ⟨-, hpos⟩ := (inStrictNormalCrossingPosition_iff p E).mp hE
  obtain ⟨U, hηU, m, c, a, hinj, hnone, hsome⟩ :=
    InStrictNormalCrossingPositionAt.exists_etaleChart (hpos hC.isIrreducible.genericPoint)
  have hmaxD : stalkIdeal D hC.isIrreducible.genericPoint
      = IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) :=
    stalkIdeal_genericPoint_eq_maximalIdeal p D hloc hC.isIrreducible hC.subset_support hC.maximal
  have hηD : hC.isIrreducible.genericPoint ∈ D.support := hC.genericPoint_mem_support
  obtain ⟨t, hat⟩ : ∃ t : Fin m, a i0 = some t := by
    cases hai : a i0 with
    | none =>
        refine absurd hηD (notMem_support_of_mem_opens_of_restrictIdeal_eq_top D U ?_ _ hηU)
        rw [← hi0D]
        exact hnone i0 hi0 hai
    | some t =>
        refine ⟨t, ?_⟩
        simp
  have hDU : restrictIdeal D U = c.coordIdeal {t} := by
    rw [← hi0D]
    exact hsome i0 hi0 t hat
  have hother : ∀ (j : ℕ) (hj : j < E.length), j ≠ i0 →
      hC.isIrreducible.genericPoint ∉ (E[j].support : Set ↥X) := by
    intro j hj hji0 hmem
    cases haj : a j with
    | none =>
        exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top E[j] U (hnone j hj haj) _ hηU hmem
    | some s =>
        have hts : t ≠ s := by
          intro h
          exact hji0 (hinj j hj i0 hi0 t (by rw [haj, h]) hat)
        have hmem' : hC.isIrreducible.genericPoint ∈ E[j].support := hmem
        have hxtop : hC.isIrreducible.genericPoint ∈ (⨆ W : X.affineOpens, (W : X.Opens)) := by
          rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
          trivial
        obtain ⟨W, hηW⟩ := TopologicalSpace.Opens.mem_iSup.mp hxtop
        obtain ⟨f, hfU, hηf⟩ :=
          W.2.exists_basicOpen_le (⟨hC.isIrreducible.genericPoint, hηU⟩ : ↥U) hηW
        have hηf' : hC.isIrreducible.genericPoint ∈ X.basicOpen f := hηf
        have hVaff : IsAffineOpen (X.basicOpen f) := W.2.basicOpen f
        exact not_mem_support_of_stalkIdeal_eq_maximalIdeal p hVaff (c.restrict hfU) hts
          (restrictIdeal_eq_restrict_coordIdeal_of_le hfU c D {t} hDU)
          (restrictIdeal_eq_restrict_coordIdeal_of_le hfU c E[j] {s} (hsome j hj s haj))
          hηf' hmaxD hmem'
  have hprod : (E.map (fun D' => stalkIdeal (monomialPartAlongDivisor I D') hC.isIrreducible.genericPoint)).prod
      = stalkIdeal (monomialPartAlongDivisor I E[i0]) hC.isIrreducible.genericPoint := by
    refine prod_map_eq_apply_getElem_of_forall_ne
      (fun D' => stalkIdeal (monomialPartAlongDivisor I D') hC.isIrreducible.genericPoint) E i0 hi0 ?_
    intro j hj hji0
    show stalkIdeal (monomialPartAlongDivisor I E[j]) hC.isIrreducible.genericPoint = 1
    have h1 : stalkIdeal (monomialPartAlongDivisor I E[j]) hC.isIrreducible.genericPoint = ⊤ :=
      stalkIdeal_monomialPartAlongDivisor_of_not_mem_support I E[j] (hother j hj hji0)
    rw [h1, Ideal.one_eq_top]
  rw [stalkIdeal_monomialFactorIdeal, hprod, hi0D,
    stalkIdeal_monomialPartAlongDivisor_of_mem p I hloc hC hC.genericPoint_mem]

/- English proof (translation)
Establish `hloc : IsEtaleLocallyCoordinateDivisor p D` using `isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE D hD`. Establish `hmaxD : stalkIdeal D hC.isIrreducible.genericPoint = IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint)` using `stalkIdeal_genericPoint_eq_maximalIdeal p D hloc hC.isIrreducible hC.subset_support hC.maximal`. Establish `hstalk : stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint = stalkIdeal D hC.isIrreducible.genericPoint ^ orderAlongComponent I hC.isIrreducible` using `stalkIdeal_monomialFactorIdeal_genericPoint p E I hE hD hC`. Establish `hmono : stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint = IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) ^ orderAlongComponent I hC.isIrreducible`. Rewrite using `[hstalk, hmaxD]`.

Establish `hordI : orderAt I hC.isIrreducible.genericPoint = ((orderAlongComponent I hC.isIrreducible : ℕ) : ℕ∞)` using `(coe_orderAlongComponent_eq_orderAt_genericPoint hC hI).symm`. Establish `h3 : stalkIdeal I hC.isIrreducible.genericPoint ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) ^ orderAlongComponent I hC.isIrreducible`. Rewrite using `[← hmaxD]`. Conclude with `stalkIdeal_le_pow_of_le_orderAt_genericPoint p D hloc hC.isIrreducible hC.subset_support hC.maximal I (orderAlongComponent I hC.isIrreducible) (le_of_eq hordI.symm) hC.isIrreducible.genericPoint hC.genericPoint_mem`. Use `le_antisymm ?_ ((le_orderAt_iff _ _ _).mpr (le_of_eq hmono))` and prove the remaining obligations.

Assume the negation of the conclusion as `hcon`. Establish `h2 : ((orderAlongComponent I hC.isIrreducible + 1 : ℕ) : ℕ∞) ≤ orderAt (monomialFactorIdeal E I) hC.isIrreducible.genericPoint` using `natCast_add_one_le_of_not_le (orderAlongComponent I hC.isIrreducible) _ hcon`. Rewrite `h2` using `[le_orderAt_iff, hmono]`. Conclude with `not_stalkIdeal_le_pow_succ_genericPoint p D hloc hC.isIrreducible hC.subset_support hC.maximal I (orderAlongComponent I hC.isIrreducible) hordI (by rw [hmaxD]; exact le_trans h3 h2)`.
-/
theorem orderAt_monomialFactorIdeal_genericPoint [TopologicalSpace.NoetherianSpace ↥X]
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (E : List X.IdealSheafData) (I : X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (hI : NonzeroOnComponents I) {D : X.IdealSheafData} (hD : D ∈ E) {C : Set X}
    (hC : IsIrreducibleComponentOfSupport D C) :
    orderAt (monomialFactorIdeal E I) hC.isIrreducible.genericPoint =
      (orderAlongComponent I hC.isIrreducible : ℕ∞) := by
  classical
  have hloc : IsEtaleLocallyCoordinateDivisor p D := isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE D hD
  have hmaxD : stalkIdeal D hC.isIrreducible.genericPoint
      = IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) :=
    stalkIdeal_genericPoint_eq_maximalIdeal p D hloc hC.isIrreducible hC.subset_support hC.maximal
  have hstalk : stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint
      = stalkIdeal D hC.isIrreducible.genericPoint ^ orderAlongComponent I hC.isIrreducible :=
    stalkIdeal_monomialFactorIdeal_genericPoint p E I hE hD hC
  have hmono : stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint
      = IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint)
        ^ orderAlongComponent I hC.isIrreducible := by
    rw [hstalk, hmaxD]
  have hordI : orderAt I hC.isIrreducible.genericPoint
      = ((orderAlongComponent I hC.isIrreducible : ℕ) : ℕ∞) :=
    (coe_orderAlongComponent_eq_orderAt_genericPoint hC hI).symm
  have h3 : stalkIdeal I hC.isIrreducible.genericPoint
      ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint)
        ^ orderAlongComponent I hC.isIrreducible := by
    rw [← hmaxD]
    exact stalkIdeal_le_pow_of_le_orderAt_genericPoint p D hloc hC.isIrreducible
      hC.subset_support hC.maximal I (orderAlongComponent I hC.isIrreducible)
      (le_of_eq hordI.symm) hC.isIrreducible.genericPoint hC.genericPoint_mem
  refine le_antisymm ?_ ((le_orderAt_iff _ _ _).mpr (le_of_eq hmono))
  by_contra hcon
  have h2 : ((orderAlongComponent I hC.isIrreducible + 1 : ℕ) : ℕ∞)
      ≤ orderAt (monomialFactorIdeal E I) hC.isIrreducible.genericPoint :=
    natCast_add_one_le_of_not_le (orderAlongComponent I hC.isIrreducible) _ hcon
  rw [le_orderAt_iff, hmono] at h2
  exact not_stalkIdeal_le_pow_succ_genericPoint p D hloc hC.isIrreducible hC.subset_support
    hC.maximal I (orderAlongComponent I hC.isIrreducible) hordI
    (by rw [hmaxD]; exact le_trans h3 h2)

def nonMonomialFactorIdeal [TopologicalSpace.NoetherianSpace ↥X] [IsLocallyNoetherian X]
    (E : List X.IdealSheafData) (I : X.IdealSheafData) : X.IdealSheafData :=
  idealSheafColon I (monomialFactorIdeal E I)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem nonMonomialFactorIdeal_eq_idealSheafColon [TopologicalSpace.NoetherianSpace ↥X] [IsLocallyNoetherian X]
    (E : List X.IdealSheafData) (I : X.IdealSheafData) :
    nonMonomialFactorIdeal E I = idealSheafColon I (monomialFactorIdeal E I) := rfl

/- English proof (translation)
Introduce `L`. Proceed by induction on `L with`. Consider the case `nil`. Introduce `g _ _ z _`. Rewrite using `[List.map_nil, List.prod_nil, Ideal.one_eq_top]`.

Conclude with `Submodule.mem_top`. Consider the case `cons b L ih`. Introduce `g hF hcan z hz`. Establish `hb0 : F b = Ideal.span ({g 0} : Set R)`. Establish `h` using `hF 0 (by simp only [List.length_cons]; omega)`.

Simplify using `using h`. Establish `hz0 : z ∈ Ideal.span ({g 0} : Set R)` using `hz 0 (by simp only [List.length_cons]; omega)`. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.mp hz0`. Establish `hzy : z = g 0 * y` using `by rw [← hy]; ring`. Establish `hyprod : y ∈ (L.map F).prod`.

Use `ih (fun i => g (i + 1)) ?_ ?_ y ?_` and prove the remaining obligations. Introduce `i h`. Establish `h2` using `hF (i + 1) (by simp only [List.length_cons]; omega)`. Simplify using `using h2`. Introduce `i hi j hj hij n w hw`.

Conclude with `hcan (i + 1) (by simp only [List.length_cons]; omega) (j + 1) (by simp only [List.length_cons]; omega) (by omega) n w hw`. Introduce `i h`. Establish `hzi : z ∈ Ideal.span ({g (i + 1)} : Set R)` using `hz (i + 1) (by simp only [List.length_cons]; omega)`. Establish `hzi' : g 0 * y ∈ Ideal.span ({g (i + 1) ^ 1} : Set R)`. Rewrite using `[pow_one, ← hzy]`.

Conclude with `hzi`. Establish `h3` using `hcan (i + 1) (by simp only [List.length_cons]; omega) 0 (by simp only [List.length_cons]; omega) (by omega) 1 y hzi'`. Rewrite `h3` using `[pow_one]`. Then use the resulting hypothesis. Establish `hg0 : g 0 ∈ F b`. Rewrite using `[hb0]`.

Conclude with `Ideal.mem_span_singleton_self _`. Rewrite using `[List.map_cons, List.prod_cons, hzy]`. Conclude with `Ideal.mul_mem_mul hg0 hyprod`.
-/
private theorem mem_prod_map_of_forall_mem_span {R : Type*} [CommRing R] {α : Type*}
    (F : α → Ideal R) :
    ∀ (L : List α) (g : ℕ → R),
      (∀ (i : ℕ) (h : i < L.length), F L[i] = Ideal.span ({g i} : Set R)) →
      (∀ (i : ℕ), i < L.length → ∀ (j : ℕ), j < L.length → i ≠ j →
        ∀ (n : ℕ) (w : R), g j * w ∈ Ideal.span ({g i ^ n} : Set R) →
          w ∈ Ideal.span ({g i ^ n} : Set R)) →
      ∀ z : R, (∀ (i : ℕ), i < L.length → z ∈ Ideal.span ({g i} : Set R)) →
        z ∈ (L.map F).prod := by
  intro L
  induction L with
  | nil =>
      intro g _ _ z _
      rw [List.map_nil, List.prod_nil, Ideal.one_eq_top]
      exact Submodule.mem_top
  | cons b L ih =>
      intro g hF hcan z hz
      have hb0 : F b = Ideal.span ({g 0} : Set R) := by
        have h := hF 0 (by simp only [List.length_cons]; omega)
        simpa using h
      have hz0 : z ∈ Ideal.span ({g 0} : Set R) :=
        hz 0 (by simp only [List.length_cons]; omega)
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hz0
      have hzy : z = g 0 * y := by rw [← hy]; ring
      have hyprod : y ∈ (L.map F).prod := by
        refine ih (fun i => g (i + 1)) ?_ ?_ y ?_
        · intro i h
          have h2 := hF (i + 1) (by simp only [List.length_cons]; omega)
          simpa using h2
        · intro i hi j hj hij n w hw
          exact hcan (i + 1) (by simp only [List.length_cons]; omega) (j + 1)
            (by simp only [List.length_cons]; omega) (by omega) n w hw
        · intro i h
          have hzi : z ∈ Ideal.span ({g (i + 1)} : Set R) :=
            hz (i + 1) (by simp only [List.length_cons]; omega)
          have hzi' : g 0 * y ∈ Ideal.span ({g (i + 1) ^ 1} : Set R) := by
            rw [pow_one, ← hzy]
            exact hzi
          have h3 := hcan (i + 1) (by simp only [List.length_cons]; omega) 0
            (by simp only [List.length_cons]; omega) (by omega) 1 y hzi'
          rwa [pow_one] at h3
      have hg0 : g 0 ∈ F b := by
        rw [hb0]
        exact Ideal.mem_span_singleton_self _
      rw [List.map_cons, List.prod_cons, hzy]
      exact Ideal.mul_mem_mul hg0 hyprod

/- English proof (translation)
Take `⟨u, hu⟩` from `Ideal.mem_span_singleton'.mp hz`. Take `⟨⟨z₀, w₁⟩, hz₁⟩` from `IsLocalization.surj (M := q) (S := A) z`. Take `⟨⟨u₀, w₂⟩, hu₁⟩` from `IsLocalization.surj (M := q) (S := A) u`. Establish `key : algebraMap S A (b * z₀ * (w₂ : S)) = algebraMap S A (d * u₀ * (w₁ : S))`. Simplify using `only [map_mul]`.

Take the linear combination `(-(algebraMap S A b) * algebraMap S A (w₂ : S)) * hz₁ + (algebraMap S A d * algebraMap S A (w₁ : S)) * hu₁ + (-(algebraMap S A (w₁ : S)) * algebraMap S A (w₂ : S)) * hu`. Take `⟨cc, hcc⟩` from `(IsLocalization.eq_iff_exists (M := q) (S := A)).mp key`. Establish `hmem : b * (z₀ * (w₂ : S) * (cc : S)) ∈ Ideal.span ({d} : Set S)` using `Ideal.mem_span_singleton'.mpr ⟨u₀ * (w₁ : S) * (cc : S), by linear_combination -hcc⟩`. Take `⟨v, hv⟩` from `Ideal.mem_span_singleton'.mp (hcan _ hmem)`. Establish `hstep : z * algebraMap S A ((w₁ : S) * (w₂ : S) * (cc : S)) ∈ Ideal.span ({algebraMap S A d} : Set A)`.

Use `Ideal.mem_span_singleton'.mpr ⟨algebraMap S A v, ?_⟩` and prove the remaining obligations. Establish `h6 : algebraMap S A (z₀ * (w₂ : S) * (cc : S)) = algebraMap S A (v * d)` using `by rw [hv]`. Simplify using `only [map_mul] at h6 ⊢`. Take the linear combination `-h6 - (algebraMap S A (w₂ : S) * algebraMap S A (cc : S)) * hz₁`. Establish `hunit : IsUnit (algebraMap S A ((w₁ : S) * (w₂ : S) * (cc : S)))`.

Establish `h1` using `IsLocalization.map_units (M := q) (S := A) w₁`. Establish `h2` using `IsLocalization.map_units (M := q) (S := A) w₂`. Establish `h3` using `IsLocalization.map_units (M := q) (S := A) cc`. Rewrite using `[map_mul, map_mul]`. Conclude with `(h1.mul h2).mul h3`.

Take `⟨eu, heu⟩` from `hunit`. Establish `h7` using `(Ideal.span ({algebraMap S A d} : Set A)).mul_mem_right ((eu⁻¹ : Aˣ) : A) hstep`. Rewrite `h7` using `[mul_assoc, ← heu, Units.mul_inv, mul_one]`. Conclude with `h7`.
-/
private theorem mem_span_algebraMap_of_mul_mem {S : Type*} [CommRing S] {q : Submonoid S}
    {A : Type*} [CommRing A] [Algebra S A] [IsLocalization q A] (b d : S)
    (hcan : ∀ w : S, b * w ∈ Ideal.span ({d} : Set S) → w ∈ Ideal.span ({d} : Set S))
    (z : A) (hz : algebraMap S A b * z ∈ Ideal.span ({algebraMap S A d} : Set A)) :
    z ∈ Ideal.span ({algebraMap S A d} : Set A) := by
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hz
  obtain ⟨⟨z₀, w₁⟩, hz₁⟩ := IsLocalization.surj (M := q) (S := A) z
  obtain ⟨⟨u₀, w₂⟩, hu₁⟩ := IsLocalization.surj (M := q) (S := A) u
  have key : algebraMap S A (b * z₀ * (w₂ : S)) = algebraMap S A (d * u₀ * (w₁ : S)) := by
    simp only [map_mul]
    linear_combination (-(algebraMap S A b) * algebraMap S A (w₂ : S)) * hz₁ +
      (algebraMap S A d * algebraMap S A (w₁ : S)) * hu₁ +
      (-(algebraMap S A (w₁ : S)) * algebraMap S A (w₂ : S)) * hu
  obtain ⟨cc, hcc⟩ := (IsLocalization.eq_iff_exists (M := q) (S := A)).mp key
  have hmem : b * (z₀ * (w₂ : S) * (cc : S)) ∈ Ideal.span ({d} : Set S) :=
    Ideal.mem_span_singleton'.mpr ⟨u₀ * (w₁ : S) * (cc : S), by linear_combination -hcc⟩
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp (hcan _ hmem)
  have hstep : z * algebraMap S A ((w₁ : S) * (w₂ : S) * (cc : S)) ∈
      Ideal.span ({algebraMap S A d} : Set A) := by
    refine Ideal.mem_span_singleton'.mpr ⟨algebraMap S A v, ?_⟩
    have h6 : algebraMap S A (z₀ * (w₂ : S) * (cc : S)) = algebraMap S A (v * d) := by rw [hv]
    simp only [map_mul] at h6 ⊢
    linear_combination -h6 - (algebraMap S A (w₂ : S) * algebraMap S A (cc : S)) * hz₁
  have hunit : IsUnit (algebraMap S A ((w₁ : S) * (w₂ : S) * (cc : S))) := by
    have h1 := IsLocalization.map_units (M := q) (S := A) w₁
    have h2 := IsLocalization.map_units (M := q) (S := A) w₂
    have h3 := IsLocalization.map_units (M := q) (S := A) cc
    rw [map_mul, map_mul]
    exact (h1.mul h2).mul h3
  obtain ⟨eu, heu⟩ := hunit
  have h7 := (Ideal.span ({algebraMap S A d} : Set A)).mul_mem_right ((eu⁻¹ : Aˣ) : A) hstep
  rw [mul_assoc, ← heu, Units.mul_inv, mul_one] at h7
  exact h7

/- English proof (translation)
Set `: Algebra Γ(X, V) (X.presheaf.stalk x)` to `(X.presheaf.germ V x hx).hom.toAlgebra`. Establish `: IsLocalization (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (X.presheaf.stalk x)` using `hV.isLocalization_stalk ⟨x, hx⟩`. Establish `hmap : ∀ y : Γ(X, V), algebraMap Γ(X, V) (X.presheaf.stalk x) y = (X.presheaf.germ V x hx).hom y` using `fun _ => rfl`. Establish `hpow : algebraMap Γ(X, V) (X.presheaf.stalk x) (c.coord i ^ N) = (X.presheaf.germ V x hx).hom (c.coord i) ^ N`. Rewrite using `[map_pow, hmap]`.

Establish `hmain` using `mem_span_algebraMap_of_mul_mem (q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) (c.coord j) (c.coord i ^ N) (fun w hw => mem_span_coord_pow_of_mul_mem hV c hij N w hw) z (by rw [hpow, hmap]; exact hz)`. Rewrite `hmain` using `[hpow]`. Then use the resulting hypothesis.
-/
private theorem mem_span_germ_coord_pow_of_mul_mem (p : X ⟶ Spec (CommRingCat.of k))
    {V : X.Opens} (hV : IsAffineOpen V) {m : ℕ} (c : EtaleChart p V m) {x : X} (hx : x ∈ V)
    {i j : Fin m} (hij : i ≠ j) (N : ℕ) (z : X.presheaf.stalk x)
    (hz : (X.presheaf.germ V x hx).hom (c.coord j) * z ∈
      Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord i) ^ N} : Set (X.presheaf.stalk x))) :
    z ∈ Ideal.span ({(X.presheaf.germ V x hx).hom (c.coord i) ^ N} :
      Set (X.presheaf.stalk x)) := by
  let : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hx).hom.toAlgebra
  have : IsLocalization (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (X.presheaf.stalk x) :=
    hV.isLocalization_stalk ⟨x, hx⟩
  have hmap : ∀ y : Γ(X, V), algebraMap Γ(X, V) (X.presheaf.stalk x) y =
      (X.presheaf.germ V x hx).hom y := fun _ => rfl
  have hpow : algebraMap Γ(X, V) (X.presheaf.stalk x) (c.coord i ^ N) =
      (X.presheaf.germ V x hx).hom (c.coord i) ^ N := by
    rw [map_pow, hmap]
  have hmain := mem_span_algebraMap_of_mul_mem
    (q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) (c.coord j) (c.coord i ^ N)
    (fun w hw => mem_span_coord_pow_of_mul_mem hV c hij N w hw) z
    (by rw [hpow, hmap]; exact hz)
  rwa [hpow] at hmain

/- English proof (translation)
Establish `hM : Blowup.IsLocallyGeneratedByNonZeroDivisor (monomialFactorIdeal E I)` using `isLocallyGeneratedByNonZeroDivisor_monomialFactorIdeal p E I hE`. Establish `hIM : I ≤ monomialFactorIdeal E I`. Rewrite using `[le_iff_forall_stalkIdeal_le]`. Introduce `x`. Take `⟨-, hposall⟩` from `(inStrictNormalCrossingPosition_iff p E).mp hE`.

Take `⟨U, hxU, m, c, aa, hinj, hnone, hsome⟩` from `InStrictNormalCrossingPositionAt.exists_etaleChart (hposall x)`. Take `⟨V, hVaff, hxV, hVU⟩` from `exists_isAffineOpen_mem_and_subset hxU`. Establish `hdata : ∀ i : ℕ, ∃ ee : X.presheaf.stalk x, ∀ h : i < E.length, stalkIdeal (monomialPartAlongDivisor I (E[i]'h)) x = Ideal.span ({ee} : Set (X.presheaf.stalk x)) ∧ stalkIdeal I x ≤ Ideal.span ({ee} : Set (X.presheaf.stalk x)) ∧ (ee = 1 ∨ ∃ (t : Fin m) (bb : ℕ), aa i = some t ∧ ee …`. Introduce `i`. Distinguish the cases in `hi : i < E.length`.

Distinguish the cases in `hxs : x ∈ (((E[i]'hi)).support : Set ↥X)`. Establish `hDloc : IsEtaleLocallyCoordinateDivisor p (E[i]'hi)` using `isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE (E[i]'hi) (List.getElem_mem hi)`. Take `⟨C, hC, hxC⟩` from `exists_isIrreducibleComponentOfSupport (E[i]'hi) x hxs`. Establish `hopt : ∃ t : Fin m, aa i = some t`. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Establish `hnone' : aa i = none`. Consider the cases of `hca : aa i with`. Consider the case `none => rfl`. Consider the case `some t => exact absurd hca (hcon t)`.

Conclude with `absurd hxs (notMem_support_of_mem_opens_of_restrictIdeal_eq_top (E[i]'hi) U (hnone i hi hnone') x hxU)`. Take `⟨t, haa⟩` from `hopt`. Establish `hDU : restrictIdeal (E[i]'hi) U = c.coordIdeal {t}` using `hsome i hi t haa`. Establish `hDV : restrictIdeal (E[i]'hi) V = (c.restrict hVU).coordIdeal {t}` using `restrictIdeal_eq_restrict_coordIdeal_of_le hVU c (E[i]'hi) {t} hDU`. Establish `hst : stalkIdeal (E[i]'hi) x = Ideal.span ({(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord t)} : Set (X.presheaf.stalk x))` using `stalkIdeal_eq_span_germ_coord p hVaff (c.restrict hVU) t (E[i]'hi) hDV x hxV`.

Establish `hA : stalkIdeal (monomialPartAlongDivisor I (E[i]'hi)) x = Ideal.span ({(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord t) ^ orderAlongComponent I hC.isIrreducible} : Set (X.presheaf.stalk x))`. Rewrite using `[stalkIdeal_monomialPartAlongDivisor_of_mem p I hDloc hC hxC, hst, Ideal.span_singleton_pow]`. Establish `hB : stalkIdeal I x ≤ Ideal.span ({(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord t) ^ orderAlongComponent I hC.isIrreducible} : Set (X.presheaf.stalk x))`. Establish `hn : ((orderAlongComponent I hC.isIrreducible : ℕ) : ℕ∞) ≤ orderAt I hC.isIrreducible.genericPoint`. Rewrite using `[orderAlongComponent_eq_orderAt_genericPoint]`.

Conclude with `ENat.natCast_toNat_le_self _`. Establish `hle` using `stalkIdeal_le_pow_of_le_orderAt_genericPoint p (E[i]'hi) hDloc hC.isIrreducible hC.subset_support hC.maximal I (orderAlongComponent I hC.isIrreducible) hn x hxC`. Rewrite `hle` using `[hst, Ideal.span_singleton_pow]`. Then use the resulting hypothesis. Conclude with `⟨(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord t) ^ orderAlongComponent I hC.isIrreducible, fun _ => ⟨hA, hB, Or.inr ⟨t, orderAlongComponent I hC.isIrreducible, haa, rfl⟩⟩⟩`. Establish `hA : stalkIdeal (monomialPartAlongDivisor I (E[i]'hi)) x = Ideal.span ({1} : Set (X.presheaf.stalk x))`.

Rewrite using `[stalkIdeal_monomialPartAlongDivisor_of_not_mem_support I (E[i]'hi) hxs, Ideal.span_singleton_one]`. Establish `hB : stalkIdeal I x ≤ Ideal.span ({1} : Set (X.presheaf.stalk x))`. Rewrite using `[Ideal.span_singleton_one]`. Conclude with `le_top`. Conclude with `⟨1, fun _ => ⟨hA, hB, Or.inl rfl⟩⟩`.

Conclude with `⟨1, fun h => absurd h hi⟩`. Use `choose ee hee using hdata`. Establish `hcan : ∀ (i : ℕ), i < E.length → ∀ (j : ℕ), j < E.length → i ≠ j → ∀ (n : ℕ) (w : X.presheaf.stalk x), ee j * w ∈ Ideal.span ({ee i ^ n} : Set (X.presheaf.stalk x)) → w ∈ Ideal.span ({ee i ^ n} : Set (X.presheaf.stalk x))`. Introduce `i hi j hj hij n w hw`. Break down `(hee i hi).2.2 with hi1 | ⟨ti, bi, hai, hei⟩` into its components or cases.

Rewrite using `[hi1, one_pow, Ideal.span_singleton_one]`. Conclude with `Submodule.mem_top`. Break down `(hee j hj).2.2 with hj1 | ⟨tj, bj, haj, hej⟩` into its components or cases. Rewrite `hw` using `[hj1, one_mul]`. Conclude with `hw`.

Establish `htne : ti ≠ tj`. Introduce `htt`. Use `hij ?_` and prove the remaining obligations. Establish `haj' : aa j = some ti` using `by rw [htt]; exact haj`. Conclude with `hinj i hi j hj ti hai haj'`.

Establish `hsingle : ∀ (N : ℕ) (zz : X.presheaf.stalk x), (X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord tj) * zz ∈ Ideal.span ({(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord ti) ^ N} : Set (X.presheaf.stalk x)) → zz ∈ Ideal.span ({(X.presheaf.germ V x hxV).hom ((c.restrict h …` using `fun N zz hzz => mem_span_germ_coord_pow_of_mul_mem p hVaff (c.restrict hVU) hxV htne N zz hzz`. Rewrite `hw` using `[hei, hej]`. Rewrite using `[hei]`. Rewrite `hw`, the goal using `[← pow_mul]`. Conclude with `mem_span_of_pow_mul_mem_span _ _ hsingle (bi * n) bj w hw`.

Rewrite using `[stalkIdeal_monomialFactorIdeal]`. Introduce `z hz`. Use `mem_prod_map_of_forall_mem_span (fun D => stalkIdeal (monomialPartAlongDivisor I D) x) E ee ?_ hcan z ?_` and prove the remaining obligations. Introduce `i h`. Conclude with `(hee i h).1`.

Introduce `i h`. Conclude with `(hee i h).2.1 hz`. Rewrite using `[nonMonomialFactorIdeal_eq_idealSheafColon]`. Conclude with `hM.mul_idealSheafColon hIM`.
-/
theorem monomialFactorIdeal_mul_nonMonomialFactorIdeal [TopologicalSpace.NoetherianSpace ↥X]
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (E : List X.IdealSheafData) (I : X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) :
    monomialFactorIdeal E I * nonMonomialFactorIdeal E I = I := by
  have hM : Blowup.IsLocallyGeneratedByNonZeroDivisor (monomialFactorIdeal E I) :=
    isLocallyGeneratedByNonZeroDivisor_monomialFactorIdeal p E I hE
  have hIM : I ≤ monomialFactorIdeal E I := by
    rw [le_iff_forall_stalkIdeal_le]
    intro x
    obtain ⟨-, hposall⟩ := (inStrictNormalCrossingPosition_iff p E).mp hE
    obtain ⟨U, hxU, m, c, aa, hinj, hnone, hsome⟩ := InStrictNormalCrossingPositionAt.exists_etaleChart (hposall x)
    obtain ⟨V, hVaff, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
    have hdata : ∀ i : ℕ, ∃ ee : X.presheaf.stalk x, ∀ h : i < E.length,
        stalkIdeal (monomialPartAlongDivisor I (E[i]'h)) x = Ideal.span ({ee} : Set (X.presheaf.stalk x)) ∧
        stalkIdeal I x ≤ Ideal.span ({ee} : Set (X.presheaf.stalk x)) ∧
        (ee = 1 ∨ ∃ (t : Fin m) (bb : ℕ), aa i = some t ∧
          ee = (X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord t) ^ bb) := by
      intro i
      by_cases hi : i < E.length
      · by_cases hxs : x ∈ (((E[i]'hi)).support : Set ↥X)
        · have hDloc : IsEtaleLocallyCoordinateDivisor p (E[i]'hi) :=
            isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE (E[i]'hi) (List.getElem_mem hi)
          obtain ⟨C, hC, hxC⟩ := exists_isIrreducibleComponentOfSupport (E[i]'hi) x hxs
          have hopt : ∃ t : Fin m, aa i = some t := by
            by_contra hcon
            push Not at hcon
            have hnone' : aa i = none := by
              cases hca : aa i with
              | none => rfl
              | some t => exact absurd hca (hcon t)
            exact absurd hxs (notMem_support_of_mem_opens_of_restrictIdeal_eq_top (E[i]'hi) U
              (hnone i hi hnone') x hxU)
          obtain ⟨t, haa⟩ := hopt
          have hDU : restrictIdeal (E[i]'hi) U = c.coordIdeal {t} := hsome i hi t haa
          have hDV : restrictIdeal (E[i]'hi) V = (c.restrict hVU).coordIdeal {t} :=
            restrictIdeal_eq_restrict_coordIdeal_of_le hVU c (E[i]'hi) {t} hDU
          have hst : stalkIdeal (E[i]'hi) x =
              Ideal.span ({(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord t)} :
                Set (X.presheaf.stalk x)) :=
            stalkIdeal_eq_span_germ_coord p hVaff (c.restrict hVU) t (E[i]'hi) hDV x hxV
          have hA : stalkIdeal (monomialPartAlongDivisor I (E[i]'hi)) x =
              Ideal.span ({(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord t) ^
                orderAlongComponent I hC.isIrreducible} : Set (X.presheaf.stalk x)) := by
            rw [stalkIdeal_monomialPartAlongDivisor_of_mem p I hDloc hC hxC, hst, Ideal.span_singleton_pow]
          have hB : stalkIdeal I x ≤
              Ideal.span ({(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord t) ^
                orderAlongComponent I hC.isIrreducible} : Set (X.presheaf.stalk x)) := by
            have hn : ((orderAlongComponent I hC.isIrreducible : ℕ) : ℕ∞) ≤
                orderAt I hC.isIrreducible.genericPoint := by
              rw [orderAlongComponent_eq_orderAt_genericPoint]
              exact ENat.natCast_toNat_le_self _
            have hle := stalkIdeal_le_pow_of_le_orderAt_genericPoint p (E[i]'hi) hDloc
              hC.isIrreducible hC.subset_support hC.maximal I
              (orderAlongComponent I hC.isIrreducible) hn x hxC
            rwa [hst, Ideal.span_singleton_pow] at hle
          exact ⟨(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord t) ^
            orderAlongComponent I hC.isIrreducible,
            fun _ => ⟨hA, hB, Or.inr ⟨t, orderAlongComponent I hC.isIrreducible, haa, rfl⟩⟩⟩
        · have hA : stalkIdeal (monomialPartAlongDivisor I (E[i]'hi)) x =
              Ideal.span ({1} : Set (X.presheaf.stalk x)) := by
            rw [stalkIdeal_monomialPartAlongDivisor_of_not_mem_support I (E[i]'hi) hxs,
              Ideal.span_singleton_one]
          have hB : stalkIdeal I x ≤ Ideal.span ({1} : Set (X.presheaf.stalk x)) := by
            rw [Ideal.span_singleton_one]
            exact le_top
          exact ⟨1, fun _ => ⟨hA, hB, Or.inl rfl⟩⟩
      · exact ⟨1, fun h => absurd h hi⟩
    choose ee hee using hdata
    have hcan : ∀ (i : ℕ), i < E.length → ∀ (j : ℕ), j < E.length → i ≠ j →
        ∀ (n : ℕ) (w : X.presheaf.stalk x),
          ee j * w ∈ Ideal.span ({ee i ^ n} : Set (X.presheaf.stalk x)) →
            w ∈ Ideal.span ({ee i ^ n} : Set (X.presheaf.stalk x)) := by
      intro i hi j hj hij n w hw
      rcases (hee i hi).2.2 with hi1 | ⟨ti, bi, hai, hei⟩
      · rw [hi1, one_pow, Ideal.span_singleton_one]
        exact Submodule.mem_top
      · rcases (hee j hj).2.2 with hj1 | ⟨tj, bj, haj, hej⟩
        · rw [hj1, one_mul] at hw
          exact hw
        · have htne : ti ≠ tj := by
            intro htt
            refine hij ?_
            have haj' : aa j = some ti := by rw [htt]; exact haj
            exact hinj i hi j hj ti hai haj'
          have hsingle : ∀ (N : ℕ) (zz : X.presheaf.stalk x),
              (X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord tj) * zz ∈
                Ideal.span ({(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord ti) ^ N} :
                  Set (X.presheaf.stalk x)) →
              zz ∈ Ideal.span ({(X.presheaf.germ V x hxV).hom ((c.restrict hVU).coord ti) ^ N} :
                  Set (X.presheaf.stalk x)) :=
            fun N zz hzz =>
              mem_span_germ_coord_pow_of_mul_mem p hVaff (c.restrict hVU) hxV htne N zz hzz
          rw [hei, hej] at hw
          rw [hei]
          rw [← pow_mul] at hw ⊢
          exact mem_span_of_pow_mul_mem_span _ _ hsingle (bi * n) bj w hw
    rw [stalkIdeal_monomialFactorIdeal]
    intro z hz
    refine mem_prod_map_of_forall_mem_span (fun D => stalkIdeal (monomialPartAlongDivisor I D) x) E ee ?_
      hcan z ?_
    · intro i h
      exact (hee i h).1
    · intro i h
      exact (hee i h).2.1 hz
  rw [nonMonomialFactorIdeal_eq_idealSheafColon]
  exact hM.mul_idealSheafColon hIM

/- English proof (translation)
Establish `haff : IsAffineOpen (Ω.ι ''ᵁ (V : Ω.toScheme.Opens))` using `V.2.image_of_isOpenImmersion Ω.ι`. Establish `he : (V : Ω.toScheme.Opens) ≤ (TopologicalSpace.Opens.map Ω.ι.base).obj (Ω.ι ''ᵁ (V : Ω.toScheme.Opens))`. Introduce `y hy`. Conclude with `⟨y, hy, rfl⟩`. Establish `hle : (Ω.ι ''ᵁ (V : Ω.toScheme.Opens)) ≤ Ω`.

Introduce and unpack `z ⟨y, -, rfl⟩`. Conclude with `y.2`. Conclude with `⟨⟨_, haff⟩, he, hle, fun A => Scheme.IdealSheafData.comap_ideal_eq_map_appLE A Ω.ι ⟨_, haff⟩ V he⟩`.
-/
private theorem exists_affineOpens_ideal_comap_ι_eq_map (Ω : X.Opens)
    (V : Ω.toScheme.affineOpens) :
    ∃ (W : X.affineOpens) (e : (V : Ω.toScheme.Opens) ≤
        (TopologicalSpace.Opens.map Ω.ι.base).obj (W : X.Opens)),
      (W : X.Opens) ≤ Ω ∧ ∀ A : X.IdealSheafData,
        (A.comap Ω.ι).ideal V
          = Ideal.map (Ω.ι.appLE (W : X.Opens) (V : Ω.toScheme.Opens) e).hom (A.ideal W) := by
  have haff : IsAffineOpen (Ω.ι ''ᵁ (V : Ω.toScheme.Opens)) :=
    V.2.image_of_isOpenImmersion Ω.ι
  have he : (V : Ω.toScheme.Opens) ≤
      (TopologicalSpace.Opens.map Ω.ι.base).obj (Ω.ι ''ᵁ (V : Ω.toScheme.Opens)) := by
    intro y hy
    exact ⟨y, hy, rfl⟩
  have hle : (Ω.ι ''ᵁ (V : Ω.toScheme.Opens)) ≤ Ω := by
    rintro z ⟨y, -, rfl⟩
    exact y.2
  exact ⟨⟨_, haff⟩, he, hle, fun A =>
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE A Ω.ι ⟨_, haff⟩ V he⟩

/- English proof (translation)
Use `le_antisymm ?_ ?_` and prove the remaining obligations. Introduce `V`. Take `⟨W, e, hW, hform⟩` from `exists_affineOpens_ideal_comap_ι_eq_map Ω V`. Rewrite using `[hform A, hform B, h W hW]`. Introduce `V`.

Take `⟨W, e, hW, hform⟩` from `exists_affineOpens_ideal_comap_ι_eq_map Ω V`. Rewrite using `[hform A, hform B, h W hW]`.
-/
private theorem comap_ι_eq_of_forall_affineOpens_ideal_eq (A B : X.IdealSheafData) (Ω : X.Opens)
    (h : ∀ W : X.affineOpens, (W : X.Opens) ≤ Ω → A.ideal W = B.ideal W) :
    A.comap Ω.ι = B.comap Ω.ι := by
  refine le_antisymm ?_ ?_
  · intro V
    obtain ⟨W, e, hW, hform⟩ := exists_affineOpens_ideal_comap_ι_eq_map Ω V
    rw [hform A, hform B, h W hW]
  · intro V
    obtain ⟨W, e, hW, hform⟩ := exists_affineOpens_ideal_comap_ι_eq_map Ω V
    rw [hform A, hform B, h W hW]

/- English proof (translation)
Rewrite using `[Scheme.IdealSheafData.one_eq_top]`. Conclude with `Scheme.IdealSheafData.comap_top _`.
-/
private theorem idealSheafData_comap_one (Ω : X.Opens) :
    (1 : X.IdealSheafData).comap Ω.ι = 1 := by
  rw [Scheme.IdealSheafData.one_eq_top]
  exact Scheme.IdealSheafData.comap_top _

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `J`. Simplify using `only [Finset.univ_eq_empty, Finset.prod_empty]`.

Conclude with `idealSheafData_comap_one Ω`. Consider the case `succ n ih`. Introduce `J`. Rewrite using `[Fin.prod_univ_succ, Scheme.IdealSheafData.comap_mul, ih (fun i => J i.succ), Fin.prod_univ_succ]`.
-/
private theorem idealSheafData_comap_prod (Ω : X.Opens) :
    ∀ (n : ℕ) (J : Fin n → X.IdealSheafData),
      (∏ i, J i).comap Ω.ι = ∏ i, (J i).comap Ω.ι := by
  intro n
  induction n with
  | zero =>
      intro J
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
      exact idealSheafData_comap_one Ω
  | succ n ih =>
      intro J
      rw [Fin.prod_univ_succ, Scheme.IdealSheafData.comap_mul, ih (fun i => J i.succ),
        Fin.prod_univ_succ]

/- English proof (translation)
Establish `hmemiff : ∀ C' : Set X, C' ∈ supportComponentsFinset D ↔ IsIrreducibleComponentOfSupport D C'`. Introduce `C'`. Simplify using `only [supportComponentsFinset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]`. Establish `hprodle : ∀ W : X.affineOpens, (((supportComponentsFinset D).toList.map (fun C => componentPowerIdeal I D C)).prod).ideal W ≤ (monomialPartAlongDivisor I D).ideal W`. Introduce `W`.

Establish `hle : ((supportComponentsFinset D).toList.map (fun C => componentPowerIdeal I D C)).prod ≤ monomialPartAlongDivisor I D`. Rewrite using `[monomialPartAlongDivisor_eq_inf_componentPowerIdeal]`. Use `Finset.le_inf ?_` and prove the remaining obligations. Introduce `C' hC'`. Conclude with `idealSheafData_listProd_le_of_mem _ (componentPowerIdeal I D C') (List.mem_map.mpr ⟨C', Finset.mem_toList.mpr hC', rfl⟩)`.

Conclude with `hle W`. Distinguish the cases in `hx : ∃ C ∈ supportComponentsFinset D, x ∈ C`. Take `⟨C₀, hC₀mem, hxC₀⟩` from `hx`. Establish `hC₀ : IsIrreducibleComponentOfSupport D C₀` using `(hmemiff C₀).mp hC₀mem`. Take `⟨V, hV, hxV, n, c, j, hDV, hVsupp, -, hagree, -⟩` from `hC₀.exists_affineOpen_etaleChart_coordIdeal p hD x hxC₀`.

Use `⟨V, hxV, orderAlongComponent I hC₀.isIrreducible, ?_⟩` and prove the remaining obligations. Introduce `W hWV`. Establish `hres : restrictIdeal D (W : X.Opens) = (c.restrict hWV).coordIdeal {j}` using `restrictIdeal_eq_restrict_coordIdeal_of_le hWV c D {j} hDV`. Establish `hDW : D.ideal W = Ideal.span {(c.restrict hWV).coord j}`. Establish `h1` using `EtaleChart.ideal_eq_span_coord (c.restrict hWV) W.2 D {j} hres`.

Simplify using `using h1`. Establish `hcomp0 : (componentPowerIdeal I D C₀).ideal W = Ideal.span {(c.restrict hWV).coord j ^ orderAlongComponent I hC₀.isIrreducible}`. Rewrite using `[componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC₀, idealSheafData_ideal_pow, hagree W hWV, hDW, Ideal.span_singleton_pow]`. Establish `hDpow : (D ^ orderAlongComponent I hC₀.isIrreducible).ideal W = Ideal.span {(c.restrict hWV).coord j ^ orderAlongComponent I hC₀.isIrreducible}`. Rewrite using `[idealSheafData_ideal_pow, hDW, Ideal.span_singleton_pow]`.

Establish `hother : ∀ C : Set X, C ∈ (supportComponentsFinset D).toList → C ≠ C₀ → (componentPowerIdeal I D C).ideal W = ⊤`. Introduce `C hCmem hne`. Establish `hCcomp : IsIrreducibleComponentOfSupport D C` using `(hmemiff C).mp (Finset.mem_toList.mp hCmem)`. Use `ideal_componentPowerIdeal_eq_top_of_disjoint I D C W ?_` and prove the remaining obligations. Introduce `y hy hyC`.

Establish `hyV : y ∈ V` using `hWV hy`. Establish `hyD : y ∈ (D.support : Set X)` using `hCcomp.subset_support hyC`. Establish `hyC₀ : y ∈ C₀` using `hVsupp y hyV hyD`. Establish `hdisj : Disjoint C C₀` using `hCcomp.disjoint hC₀ p hD hne`. Conclude with `(Set.disjoint_left.mp hdisj hyC) hyC₀`.

Establish `hprodideal : (((supportComponentsFinset D).toList.map (fun C => componentPowerIdeal I D C)).prod).ideal W = (componentPowerIdeal I D C₀).ideal W`. Rewrite using `[idealSheafData_ideal_listProd, List.map_map]`. Use `prod_map_eq_apply_of_nodup_of_forall_ne (fun C => (componentPowerIdeal I D C).ideal W) ((supportComponentsFinset D).toList) C₀ (Finset.nodup_toList _) (Finset.mem_toList.mpr hC₀mem) ?_` and prove the remaining obligations. Introduce `C' hC' hne`. Use `show (componentPowerIdeal I D C').ideal W = 1`.

Rewrite using `[Ideal.one_eq_top]`. Conclude with `hother C' hC' hne`. Rewrite using `[hDpow, ← hcomp0]`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Establish `hle : monomialPartAlongDivisor I D ≤ componentPowerIdeal I D C₀`.

Rewrite using `[monomialPartAlongDivisor_eq_inf_componentPowerIdeal]`. Conclude with `Finset.inf_le hC₀mem`. Conclude with `hle W`. Rewrite using `[← hprodideal]`. Conclude with `hprodle W`.

Use `push Not at hx`. Establish `hclosed : IsClosed (⋃ C ∈ (supportComponentsFinset D : Set (Set X)), C)`. Use `Set.Finite.isClosed_biUnion (supportComponentsFinset D).finite_toSet ?_` and prove the remaining obligations. Introduce `C hC`. Conclude with `((hmemiff C).mp (Finset.mem_coe.mp hC)).isClosed`.

Use `⟨⟨(⋃ C ∈ (supportComponentsFinset D : Set (Set X)), C)ᶜ, hclosed.isOpen_compl⟩, ?_, 0, ?_⟩` and prove the remaining obligations. Introduce `hmem`. Rewrite `hmem` using `[Set.mem_iUnion₂]`. Take `⟨C, hC, hxC⟩` from `hmem`. Conclude with `hx C (Finset.mem_coe.mp hC) hxC`.

Introduce `W hWΩ`. Rewrite using `[pow_zero, idealSheafData_ideal_one, Ideal.one_eq_top]`. Establish `hall : ∀ C ∈ (supportComponentsFinset D).toList, (componentPowerIdeal I D C).ideal W = 1`. Introduce `C hC`. Rewrite using `[Ideal.one_eq_top]`.

Use `ideal_componentPowerIdeal_eq_top_of_disjoint I D C W ?_` and prove the remaining obligations. Introduce `y hy hyC`. Establish `hyS : y ∈ (⋃ C' ∈ (supportComponentsFinset D : Set (Set X)), C')` using `Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_toList.mp hC)) hyC`. Conclude with `absurd hyS (hWΩ hy)`. Establish `hprodtop : (((supportComponentsFinset D).toList.map (fun C => componentPowerIdeal I D C)).prod).ideal W = ⊤`.

Rewrite using `[idealSheafData_ideal_listProd, List.map_map, ← Ideal.one_eq_top]`. Conclude with `prod_map_eq_one_of_forall_eq_one (fun C => (componentPowerIdeal I D C).ideal W) ((supportComponentsFinset D).toList) hall`. Use `le_antisymm le_top ?_` and prove the remaining obligations. Rewrite using `[← hprodtop]`. Conclude with `hprodle W`.
-/
private theorem exists_nhds_ideal_monomialPartAlongDivisor_eq_pow [TopologicalSpace.NoetherianSpace ↥X]
    (p : X ⟶ Spec (CommRingCat.of k)) (I D : X.IdealSheafData)
    (hD : IsEtaleLocallyCoordinateDivisor p D) (x : X) :
    ∃ Ω : X.Opens, x ∈ Ω ∧ ∃ a : ℕ, ∀ W : X.affineOpens, (W : X.Opens) ≤ Ω →
      (monomialPartAlongDivisor I D).ideal W = (D ^ a).ideal W := by
  classical
  have hmemiff : ∀ C' : Set X, C' ∈ supportComponentsFinset D ↔ IsIrreducibleComponentOfSupport D C' := by
    intro C'
    simp only [supportComponentsFinset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hprodle : ∀ W : X.affineOpens,
      (((supportComponentsFinset D).toList.map (fun C => componentPowerIdeal I D C)).prod).ideal W
        ≤ (monomialPartAlongDivisor I D).ideal W := by
    intro W
    have hle : ((supportComponentsFinset D).toList.map (fun C => componentPowerIdeal I D C)).prod
        ≤ monomialPartAlongDivisor I D := by
      rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
      refine Finset.le_inf ?_
      intro C' hC'
      exact idealSheafData_listProd_le_of_mem _ (componentPowerIdeal I D C')
        (List.mem_map.mpr ⟨C', Finset.mem_toList.mpr hC', rfl⟩)
    exact hle W
  by_cases hx : ∃ C ∈ supportComponentsFinset D, x ∈ C
  · obtain ⟨C₀, hC₀mem, hxC₀⟩ := hx
    have hC₀ : IsIrreducibleComponentOfSupport D C₀ := (hmemiff C₀).mp hC₀mem
    obtain ⟨V, hV, hxV, n, c, j, hDV, hVsupp, -, hagree, -⟩ :=
      hC₀.exists_affineOpen_etaleChart_coordIdeal p hD x hxC₀
    refine ⟨V, hxV, orderAlongComponent I hC₀.isIrreducible, ?_⟩
    intro W hWV
    have hres : restrictIdeal D (W : X.Opens) = (c.restrict hWV).coordIdeal {j} :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hWV c D {j} hDV
    have hDW : D.ideal W = Ideal.span {(c.restrict hWV).coord j} := by
      have h1 := EtaleChart.ideal_eq_span_coord (c.restrict hWV) W.2 D {j} hres
      simpa using h1
    have hcomp0 : (componentPowerIdeal I D C₀).ideal W
        = Ideal.span {(c.restrict hWV).coord j ^ orderAlongComponent I hC₀.isIrreducible} := by
      rw [componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC₀, idealSheafData_ideal_pow,
        hagree W hWV, hDW, Ideal.span_singleton_pow]
    have hDpow : (D ^ orderAlongComponent I hC₀.isIrreducible).ideal W
        = Ideal.span {(c.restrict hWV).coord j ^ orderAlongComponent I hC₀.isIrreducible} := by
      rw [idealSheafData_ideal_pow, hDW, Ideal.span_singleton_pow]
    have hother : ∀ C : Set X, C ∈ (supportComponentsFinset D).toList → C ≠ C₀ →
        (componentPowerIdeal I D C).ideal W = ⊤ := by
      intro C hCmem hne
      have hCcomp : IsIrreducibleComponentOfSupport D C := (hmemiff C).mp (Finset.mem_toList.mp hCmem)
      refine ideal_componentPowerIdeal_eq_top_of_disjoint I D C W ?_
      intro y hy hyC
      have hyV : y ∈ V := hWV hy
      have hyD : y ∈ (D.support : Set X) := hCcomp.subset_support hyC
      have hyC₀ : y ∈ C₀ := hVsupp y hyV hyD
      have hdisj : Disjoint C C₀ := hCcomp.disjoint hC₀ p hD hne
      exact (Set.disjoint_left.mp hdisj hyC) hyC₀
    have hprodideal : (((supportComponentsFinset D).toList.map
        (fun C => componentPowerIdeal I D C)).prod).ideal W = (componentPowerIdeal I D C₀).ideal W := by
      rw [idealSheafData_ideal_listProd, List.map_map]
      refine prod_map_eq_apply_of_nodup_of_forall_ne (fun C => (componentPowerIdeal I D C).ideal W)
        ((supportComponentsFinset D).toList) C₀ (Finset.nodup_toList _)
        (Finset.mem_toList.mpr hC₀mem) ?_
      intro C' hC' hne
      show (componentPowerIdeal I D C').ideal W = 1
      rw [Ideal.one_eq_top]
      exact hother C' hC' hne
    rw [hDpow, ← hcomp0]
    refine le_antisymm ?_ ?_
    · have hle : monomialPartAlongDivisor I D ≤ componentPowerIdeal I D C₀ := by
        rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
        exact Finset.inf_le hC₀mem
      exact hle W
    · rw [← hprodideal]
      exact hprodle W
  · push Not at hx
    have hclosed : IsClosed (⋃ C ∈ (supportComponentsFinset D : Set (Set X)), C) := by
      refine Set.Finite.isClosed_biUnion (supportComponentsFinset D).finite_toSet ?_
      intro C hC
      exact ((hmemiff C).mp (Finset.mem_coe.mp hC)).isClosed
    refine ⟨⟨(⋃ C ∈ (supportComponentsFinset D : Set (Set X)), C)ᶜ, hclosed.isOpen_compl⟩,
      ?_, 0, ?_⟩
    · intro hmem
      rw [Set.mem_iUnion₂] at hmem
      obtain ⟨C, hC, hxC⟩ := hmem
      exact hx C (Finset.mem_coe.mp hC) hxC
    · intro W hWΩ
      rw [pow_zero, idealSheafData_ideal_one, Ideal.one_eq_top]
      have hall : ∀ C ∈ (supportComponentsFinset D).toList,
          (componentPowerIdeal I D C).ideal W = 1 := by
        intro C hC
        rw [Ideal.one_eq_top]
        refine ideal_componentPowerIdeal_eq_top_of_disjoint I D C W ?_
        intro y hy hyC
        have hyS : y ∈ (⋃ C' ∈ (supportComponentsFinset D : Set (Set X)), C') :=
          Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_toList.mp hC)) hyC
        exact absurd hyS (hWΩ hy)
      have hprodtop : (((supportComponentsFinset D).toList.map
          (fun C => componentPowerIdeal I D C)).prod).ideal W = ⊤ := by
        rw [idealSheafData_ideal_listProd, List.map_map, ← Ideal.one_eq_top]
        exact prod_map_eq_one_of_forall_eq_one (fun C => (componentPowerIdeal I D C).ideal W)
          ((supportComponentsFinset D).toList) hall
      refine le_antisymm le_top ?_
      rw [← hprodtop]
      exact hprodle W

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `g _`. Use `⟨⊤, trivial, Fin.elim0, ?_⟩` and prove the remaining obligations.

Introduce `W _`. Simplify using `only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.prod_empty]`. Consider the case `succ n ih`. Introduce `g hg`. Take `⟨Ω₁, hxΩ₁, a₀, h₁⟩` from `exists_nhds_ideal_monomialPartAlongDivisor_eq_pow p I (g 0) (hg 0) x`.

Take `⟨Ω₂, hxΩ₂, a', h₂⟩` from `ih (fun i => g i.succ) (fun i => hg i.succ)`. Use `⟨Ω₁ ⊓ Ω₂, ⟨hxΩ₁, hxΩ₂⟩, Fin.cons a₀ a', ?_⟩` and prove the remaining obligations. Introduce `W hW`. Establish `e1` using `h₁ W (le_trans hW inf_le_left)`. Establish `e2` using `h₂ W (le_trans hW inf_le_right)`.

Simplify using `only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]`. Rewrite using `[idealSheafData_ideal_mul, idealSheafData_ideal_mul, e1, e2]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`.
-/
private theorem exists_prod_monomialPartAlongDivisor_eq_prod_pow
    [TopologicalSpace.NoetherianSpace ↥X] (p : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (x : X) :
    ∀ (n : ℕ) (g : Fin n → X.IdealSheafData), (∀ i, IsEtaleLocallyCoordinateDivisor p (g i)) →
      ∃ Ω : X.Opens, x ∈ Ω ∧ ∃ a : Fin n → ℕ, ∀ W : X.affineOpens, (W : X.Opens) ≤ Ω →
        ((List.ofFn fun i => monomialPartAlongDivisor I (g i)).prod).ideal W = (∏ i, g i ^ a i).ideal W := by
  intro n
  induction n with
  | zero =>
      intro g _
      refine ⟨⊤, trivial, Fin.elim0, ?_⟩
      intro W _
      simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.prod_empty]
  | succ n ih =>
      intro g hg
      obtain ⟨Ω₁, hxΩ₁, a₀, h₁⟩ := exists_nhds_ideal_monomialPartAlongDivisor_eq_pow p I (g 0) (hg 0) x
      obtain ⟨Ω₂, hxΩ₂, a', h₂⟩ := ih (fun i => g i.succ) (fun i => hg i.succ)
      refine ⟨Ω₁ ⊓ Ω₂, ⟨hxΩ₁, hxΩ₂⟩, Fin.cons a₀ a', ?_⟩
      intro W hW
      have e1 := h₁ W (le_trans hW inf_le_left)
      have e2 := h₂ W (le_trans hW inf_le_right)
      simp only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
      rw [idealSheafData_ideal_mul, idealSheafData_ideal_mul, e1, e2]
      simp only [Fin.cons_zero, Fin.cons_succ]

/- English proof (translation)
Establish `hetaleCoord : ∀ i : Fin E.length, IsEtaleLocallyCoordinateDivisor p (E.get i)`. Introduce `i`. Use `isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE _ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `⟨monomialFactorIdeal E I, nonMonomialFactorIdeal E I, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `(monomialFactorIdeal_mul_nonMonomialFactorIdeal p E I hE).symm`. Introduce `z hz`. Assume the negation of the conclusion as `hcon`. Establish `hnot : ∀ D ∈ E, z ∉ (D.support : Set X)`. Introduce `D hD hmem`.

Use `hcon ?_` and prove the remaining obligations. Rewrite using `[Set.mem_iUnion₂]`. Conclude with `⟨D, hD, hmem⟩`. Establish `htop : stalkIdeal (monomialFactorIdeal E I) z = ⊤`. Rewrite using `[stalkIdeal_monomialFactorIdeal, ← Ideal.one_eq_top]`.

Use `prod_map_eq_one_of_forall_eq_one (fun D => stalkIdeal (monomialPartAlongDivisor I D) z) E ?_` and prove the remaining obligations. Introduce `D hD`. Rewrite using `[stalkIdeal_monomialPartAlongDivisor_of_not_mem_support I D (hnot D hD), Ideal.one_eq_top]`. Establish `hz' : z ∈ (monomialFactorIdeal E I).support` using `hz`. Conclude with `(mem_support_iff_stalkIdeal_ne_top (monomialFactorIdeal E I) z).mp hz' htop`.

Introduce `x`. Take `⟨Ω, hxΩ, a, ha⟩` from `exists_prod_monomialPartAlongDivisor_eq_prod_pow p I x E.length E.get hetaleCoord`. Use `⟨Ω, hxΩ, a, ?_⟩` and prove the remaining obligations. Establish `hlist : (List.ofFn fun i : Fin E.length => monomialPartAlongDivisor I (E.get i)) = E.map fun D => monomialPartAlongDivisor I D`. Use `List.ext_getElem (by simp) ?_` and prove the remaining obligations.

Introduce `i h1 h2`. Simplify using the standard rewrite rules. Establish `hcongr : (monomialFactorIdeal E I).comap Ω.ι = (∏ i : Fin E.length, E.get i ^ a i).comap Ω.ι`. Use `comap_ι_eq_of_forall_affineOpens_ideal_eq _ _ Ω ?_` and prove the remaining obligations. Introduce `W hW`.

Establish `hW'` using `ha W hW`. Rewrite `hW'` using `[hlist]`. Rewrite using `[monomialFactorIdeal_eq_prod_monomialPartAlongDivisor]`. Conclude with `hW'`. Rewrite using `[hcongr, idealSheafData_comap_prod Ω E.length (fun i => E.get i ^ a i)]`.

Conclude with `Finset.prod_congr rfl (fun i _ => Scheme.IdealSheafData.comap_pow (E.get i) Ω.ι (a i))`. Introduce `D hD C hCirr hCsub hCmax hCN`. Establish `hC : IsIrreducibleComponentOfSupport D C` using `{ isIrreducible := hCirr maximal := fun C' h1 h2 h3 => Set.Subset.antisymm (hCmax C' h1 h3 h2) h2 subset_support := hCsub }`. Establish `hloc : IsEtaleLocallyCoordinateDivisor p D` using `isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE D hD`. Establish `hmaxD : stalkIdeal D hC.isIrreducible.genericPoint = IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint)` using `stalkIdeal_genericPoint_eq_maximalIdeal p D hloc hC.isIrreducible hC.subset_support hC.maximal`.

Establish `hstalkM : stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint = IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) ^ orderAlongComponent I hC.isIrreducible`. Rewrite using `[stalkIdeal_monomialFactorIdeal_genericPoint p E I hE hD hC, hmaxD]`. Establish `hN : stalkIdeal (nonMonomialFactorIdeal E I) hC.isIrreducible.genericPoint ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint)` using `(mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp (hCN hC.genericPoint_mem)`. Establish `hIeq : stalkIdeal I hC.isIrreducible.genericPoint = stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint * stalkIdeal (nonMonomialFactorIdeal E I) hC.isIrreducible.genericPoint`. Rewrite using `[← stalkIdeal_mul, monomialFactorIdeal_mul_nonMonomialFactorIdeal p E I hE]`.

Establish `hle : stalkIdeal I hC.isIrreducible.genericPoint ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) ^ (orderAlongComponent I hC.isIrreducible + 1)`. Rewrite using `[hIeq, hstalkM, pow_succ]`. Conclude with `Ideal.mul_mono le_rfl hN`. Establish `h2 : ((orderAlongComponent I hC.isIrreducible + 1 : ℕ) : ℕ∞) ≤ orderAt I hC.isIrreducible.genericPoint` using `(le_orderAt_iff I _ _).mpr hle`. Rewrite `h2` using `[← coe_orderAlongComponent_eq_orderAt_genericPoint hC hI]`.

Establish `h3 : orderAlongComponent I hC.isIrreducible + 1 ≤ orderAlongComponent I hC.isIrreducible` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_isMonomialSplitting [TopologicalSpace.NoetherianSpace ↥X] [IsLocallyNoetherian X]
    [CharZero k] (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [LocallyOfFiniteType p] [QuasiCompact p] (E : List X.IdealSheafData)
    (hE : InStrictNormalCrossingPosition p E) (I : X.IdealSheafData) (hI : NonzeroOnComponents I) :
    ∃ M N : X.IdealSheafData, IsMonomialSplitting E I M N := by
  classical
  have hetaleCoord : ∀ i : Fin E.length, IsEtaleLocallyCoordinateDivisor p (E.get i) := by
    intro i
    refine isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE _ ?_
    simp
  refine ⟨monomialFactorIdeal E I, nonMonomialFactorIdeal E I, ?_, ?_, ?_, ?_⟩
  · exact (monomialFactorIdeal_mul_nonMonomialFactorIdeal p E I hE).symm
  · intro z hz
    by_contra hcon
    have hnot : ∀ D ∈ E, z ∉ (D.support : Set X) := by
      intro D hD hmem
      refine hcon ?_
      rw [Set.mem_iUnion₂]
      exact ⟨D, hD, hmem⟩
    have htop : stalkIdeal (monomialFactorIdeal E I) z = ⊤ := by
      rw [stalkIdeal_monomialFactorIdeal, ← Ideal.one_eq_top]
      refine prod_map_eq_one_of_forall_eq_one (fun D => stalkIdeal (monomialPartAlongDivisor I D) z) E ?_
      intro D hD
      rw [stalkIdeal_monomialPartAlongDivisor_of_not_mem_support I D (hnot D hD), Ideal.one_eq_top]
    have hz' : z ∈ (monomialFactorIdeal E I).support := hz
    exact (mem_support_iff_stalkIdeal_ne_top (monomialFactorIdeal E I) z).mp hz' htop
  · intro x
    obtain ⟨Ω, hxΩ, a, ha⟩ :=
      exists_prod_monomialPartAlongDivisor_eq_prod_pow p I x E.length E.get hetaleCoord
    refine ⟨Ω, hxΩ, a, ?_⟩
    have hlist : (List.ofFn fun i : Fin E.length => monomialPartAlongDivisor I (E.get i))
        = E.map fun D => monomialPartAlongDivisor I D := by
      refine List.ext_getElem (by simp) ?_
      intro i h1 h2
      simp
    have hcongr : (monomialFactorIdeal E I).comap Ω.ι
        = (∏ i : Fin E.length, E.get i ^ a i).comap Ω.ι := by
      refine comap_ι_eq_of_forall_affineOpens_ideal_eq _ _ Ω ?_
      intro W hW
      have hW' := ha W hW
      rw [hlist] at hW'
      rw [monomialFactorIdeal_eq_prod_monomialPartAlongDivisor]
      exact hW'
    rw [hcongr, idealSheafData_comap_prod Ω E.length (fun i => E.get i ^ a i)]
    exact Finset.prod_congr rfl
      (fun i _ => Scheme.IdealSheafData.comap_pow (E.get i) Ω.ι (a i))
  · intro D hD C hCirr hCsub hCmax hCN
    have hC : IsIrreducibleComponentOfSupport D C :=
      { isIrreducible := hCirr
        maximal := fun C' h1 h2 h3 => Set.Subset.antisymm (hCmax C' h1 h3 h2) h2
        subset_support := hCsub }
    have hloc : IsEtaleLocallyCoordinateDivisor p D := isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE D hD
    have hmaxD : stalkIdeal D hC.isIrreducible.genericPoint
        = IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) :=
      stalkIdeal_genericPoint_eq_maximalIdeal p D hloc hC.isIrreducible hC.subset_support
        hC.maximal
    have hstalkM : stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint
        = IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint)
          ^ orderAlongComponent I hC.isIrreducible := by
      rw [stalkIdeal_monomialFactorIdeal_genericPoint p E I hE hD hC, hmaxD]
    have hN : stalkIdeal (nonMonomialFactorIdeal E I) hC.isIrreducible.genericPoint
        ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) :=
      (mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp (hCN hC.genericPoint_mem)
    have hIeq : stalkIdeal I hC.isIrreducible.genericPoint
        = stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint
          * stalkIdeal (nonMonomialFactorIdeal E I) hC.isIrreducible.genericPoint := by
      rw [← stalkIdeal_mul, monomialFactorIdeal_mul_nonMonomialFactorIdeal p E I hE]
    have hle : stalkIdeal I hC.isIrreducible.genericPoint
        ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint)
          ^ (orderAlongComponent I hC.isIrreducible + 1) := by
      rw [hIeq, hstalkM, pow_succ]
      exact Ideal.mul_mono le_rfl hN
    have h2 : ((orderAlongComponent I hC.isIrreducible + 1 : ℕ) : ℕ∞)
        ≤ orderAt I hC.isIrreducible.genericPoint :=
      (le_orderAt_iff I _ _).mpr hle
    rw [← coe_orderAlongComponent_eq_orderAt_genericPoint hC hI] at h2
    have h3 : orderAlongComponent I hC.isIrreducible + 1
        ≤ orderAlongComponent I hC.isIrreducible := by exact_mod_cast h2
    omega

end FunctorialResolution.EmbeddedResolution

end
