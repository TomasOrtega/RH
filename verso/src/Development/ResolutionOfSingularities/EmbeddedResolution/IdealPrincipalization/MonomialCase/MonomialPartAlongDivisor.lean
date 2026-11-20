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

/- English proof (authored)
Induct on the power of the factor being cancelled. At zero the membership is the conclusion. For a successor power, factor off one copy and apply the assumed cancellation in the principal power ideal. Then use the induction hypothesis on the remaining power.
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

/- English proof (authored)
Multiply the identity for sheaf multiplication by the full structure sheaf ideal. The result is the full structure sheaf ideal. Taking stalks and using the known stalk of the unit ideal gives the product of the sought stalk ideal with the unit stalk ideal equal to the unit ideal. This product is contained in the sought stalk ideal, forcing it to be the unit ideal.
-/
theorem stalkIdeal_one (x : X) : stalkIdeal (1 : X.IdealSheafData) x = ⊤ := by
  have h := stalkIdeal_mul (1 : X.IdealSheafData) (⊤ : X.IdealSheafData) x
  rw [one_mul, stalkIdeal_top] at h
  refine le_antisymm le_top ?_
  rw [h]
  exact Ideal.mul_le.mpr (fun r hr s _ => Ideal.mul_mem_right s _ hr)

/- English proof (authored)
Induct on the list of ideal sheaves. The empty product has the unit ideal as its stalk. For a nonempty list, take the stalk of the head multiplied by the tail product, then use preservation of multiplication and the induction formula for the tail.
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

/- English proof (authored)
Choose the listed index of the divisor and take an étale normal-crossings chart around the given point. The chart assigns to this entry either the unit ideal or the ideal of a single coordinate. Use that chart for the local description of the divisor.
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

/- English proof (authored)
By definition, the natural-number order along the component is obtained by taking the natural-number value of the order at its generic point.
-/
theorem orderAlongComponent_eq_orderAt_genericPoint (I : X.IdealSheafData) {C : Set X} (hC : IsIrreducible C) :
    orderAlongComponent I hC = (orderAt I hC.genericPoint).toNat := rfl

/- English proof (authored)
The ideal is nonzero on the ambient components, so the order at the generic point of the given component is finite. Taking its natural-number value and inserting that value back into the extended natural numbers recovers it.
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

/- English proof (authored)
The component-power construction uses the unit ideal in the branch where the given subset is not an irreducible component of the divisor's support. The hypothesis selects that branch.
-/
theorem componentPowerIdeal_of_not_isIrreducibleComponentOfSupport (I D : X.IdealSheafData) {C : Set X}
    (h : ¬ IsIrreducibleComponentOfSupport D C) : componentPowerIdeal I D C = ⊤ :=
  @dif_neg (IsIrreducibleComponentOfSupport D C) (Classical.propDecidable (IsIrreducibleComponentOfSupport D C)) h
    X.IdealSheafData _ _

/- English proof (authored)
The component is a closed irreducible subset of the divisor's support. The construction thus takes its vanishing ideal to the power given by the order of the marked ideal along that component.
-/
theorem componentPowerIdeal_of_isIrreducibleComponentOfSupport (I D : X.IdealSheafData) {C : Set X}
    (h : IsIrreducibleComponentOfSupport D C) :
    componentPowerIdeal I D C =
      Scheme.IdealSheafData.vanishingIdeal (⟨C, h.isClosed⟩ : TopologicalSpace.Closeds ↥X) ^
        orderAlongComponent I h.isIrreducible := by
  unfold componentPowerIdeal
  exact dif_pos h

/- English proof (authored)
If the subset is not a component, the ideal is already the unit ideal. If it is a component, its vanishing ideal has precisely the component as support. At a point outside it the vanishing ideal has unit stalk. Stalks commute with powers, so its specified power also has unit stalk.
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

/- English proof (authored)
For this component the defining ideal is the specified power of its vanishing ideal. At the given point on the component, the étale coordinate-divisor description identifies the stalk of its vanishing ideal with the divisor stalk. Taking stalks of the power gives the formula.
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

/- English proof (authored)
The contribution along a divisor is defined by intersecting the component-power ideals for its finite set of support components. This intersection is their infimum.
-/
theorem monomialPartAlongDivisor_eq_inf_componentPowerIdeal [TopologicalSpace.NoetherianSpace ↥X] (I D : X.IdealSheafData) :
    monomialPartAlongDivisor I D = (supportComponentsFinset D).inf (fun C => componentPowerIdeal I D C) := rfl

/- English proof (authored)
Check inclusion at each stalk. Products of a section from the first stalk ideal with any element of the second belong to the first ideal. Thus the product ideal is contained in the first.
-/
private theorem idealSheafData_mul_le_left (a b : X.IdealSheafData) : a * b ≤ a := by
  rw [le_iff_forall_stalkIdeal_le]
  intro x
  rw [stalkIdeal_mul]
  exact Ideal.mul_le.mpr fun r hr s _ => Ideal.mul_mem_right s _ hr

/- English proof (authored)
At each stalk, a product with a factor in the second ideal belongs to that ideal. Hence the product of the stalk ideals is contained in the second stalk ideal, and the sheaf inclusion follows.
-/
private theorem idealSheafData_mul_le_right (a b : X.IdealSheafData) : a * b ≤ b := by
  rw [le_iff_forall_stalkIdeal_le]
  intro x
  rw [stalkIdeal_mul]
  exact Ideal.mul_le.mpr fun r _ s hs => Ideal.mul_mem_left _ r hs

/- English proof (authored)
The product of the two ideals is contained in their intersection. Its stalk is the product of two unit stalk ideals, hence is the unit ideal. By monotonicity the stalk of the intersection contains the unit ideal and is therefore equal to it.
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

/- English proof (authored)
Induct on the finite set of indices. The empty intersection is the unit ideal. Inserting one index intersects the previous ideal with the additional ideal, both of which have unit stalk at the chosen point. The binary intersection then has unit stalk.
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

/- English proof (authored)
Each support component lies in the divisor support, so none contains the given point. Each component-power ideal has unit stalk there by the calculation away from its component. Their finite intersection therefore has unit stalk.
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

/- English proof (authored)
Induct on the list. If the specified ideal is its head, the product is contained in the head ideal. If it occurs in the tail, the full product is contained in the tail product, which is contained in the specified ideal by induction. The empty list has no specified member.
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

/- English proof (authored)
Each entry of the mapped list is the image of a listed element and therefore equals the multiplicative identity. Their product is the identity.
-/
private theorem prod_map_eq_one_of_forall_eq_one {α : Type*} {M : Type*} [CommMonoid M]
    (g : α → M) (L : List α) (h : ∀ b ∈ L, g b = 1) : (L.map g).prod = 1 :=
  List.prod_eq_one fun x hx => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact h a ha

/- English proof (authored)
The distinguished element occurs exactly once by membership and the absence of repetitions. Every other entry maps to the identity. Multiplying the mapped entries therefore leaves only the value at the distinguished element.
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

/- English proof (authored)
The intersection of the component-power ideals is contained in the ideal for the component containing the point. Its stalk is therefore contained in the stated power. For the reverse containment, use the product of all component-power ideals, which is contained in their intersection. Distinct components of this étale coordinate divisor are disjoint, so all other factors have unit stalk at the point. The product stalk is exactly the power for the chosen component, giving the other inclusion.
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

/- English proof (authored)
The monomial factor is defined as the product of the contributions along the listed boundary divisors. Applying the divisor-contribution operation to the list gives the factors in the stated product.
-/
theorem monomialFactorIdeal_eq_prod_monomialPartAlongDivisor [TopologicalSpace.NoetherianSpace ↥X] (E : List X.IdealSheafData)
    (I : X.IdealSheafData) :
    monomialFactorIdeal E I = (E.map (fun D => monomialPartAlongDivisor I D)).prod := rfl

/- English proof (authored)
Take the stalk of the finite product of the contributions along the boundary. Stalks preserve list products, so the result is the product of the stalks of those contributions.
-/
theorem stalkIdeal_monomialFactorIdeal [TopologicalSpace.NoetherianSpace ↥X]
    (E : List X.IdealSheafData) (I : X.IdealSheafData) (x : X) :
    stalkIdeal (monomialFactorIdeal E I) x =
      (E.map (fun D => stalkIdeal (monomialPartAlongDivisor I D) x)).prod := by
  have h : monomialFactorIdeal E I = (E.map (fun D => monomialPartAlongDivisor I D)).prod := rfl
  rw [h, stalkIdeal_listProd, List.map_map]
  rfl

/- English proof (authored)
On the given affine open, the product of ideal sheaves is defined by multiplying their section ideals. This gives the equality there.
-/
private theorem idealSheafData_ideal_mul (I J : X.IdealSheafData) (W : X.affineOpens) :
    (I * J).ideal W = I.ideal W * J.ideal W := rfl

/- English proof (authored)
The section ideal of the unit ideal sheaf contains the unit section on every affine open. Thus it is the unit ideal of that section ring.
-/
private theorem idealSheafData_ideal_top (W : X.affineOpens) :
    (⊤ : X.IdealSheafData).ideal W = ⊤ :=
  (Ideal.eq_top_iff_one _).mpr (by simp)

/- English proof (authored)
The multiplicative identity for ideal sheaves is the unit ideal sheaf. Its section ideal on the affine open is the unit ideal, the multiplicative identity for ideals in the section ring.
-/
private theorem idealSheafData_ideal_one (W : X.affineOpens) :
    (1 : X.IdealSheafData).ideal W = 1 := by
  rw [Ideal.one_eq_top]
  exact idealSheafData_ideal_top W

/- English proof (authored)
Induct on the exponent. At zero both sides are the unit ideal by the section calculation for the identity sheaf. At a successor, use preservation of products of section ideals and then the induction hypothesis for the preceding power.
-/
private theorem idealSheafData_ideal_pow (J : X.IdealSheafData) (n : ℕ)
    (W : X.affineOpens) : (J ^ n).ideal W = J.ideal W ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact idealSheafData_ideal_one W
  | succ n ih => rw [pow_succ, pow_succ, idealSheafData_ideal_mul, ih]

/- English proof (authored)
Induct on the list. The empty product gives the unit section ideal. For the head and tail, take sections of their product using the affine multiplication formula and substitute the induction formula for the tail.
-/
private theorem idealSheafData_ideal_listProd (L : List X.IdealSheafData) (W : X.affineOpens) :
    L.prod.ideal W = (L.map (fun J => J.ideal W)).prod := by
  induction L with
  | nil => rw [List.prod_nil, List.map_nil, List.prod_nil]; exact idealSheafData_ideal_one W
  | cons J L ih =>
      rw [List.prod_cons, List.map_cons, List.prod_cons, idealSheafData_ideal_mul, ih]

/- English proof (authored)
The section ideal consists of elements lying in every prime of the affine open corresponding to a point of the closed set. There are no such primes because the open is disjoint from the set. The unit satisfies the defining condition and the ideal is the unit ideal.
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

/- English proof (authored)
If the subset is a support component, its vanishing ideal has unit sections on the disjoint affine open. Thus its specified power has unit sections there. If it is not a support component, the component-power ideal is already the unit ideal sheaf.
-/
private theorem ideal_componentPowerIdeal_eq_top_of_disjoint (I D : X.IdealSheafData) (C : Set X)
    (W : X.affineOpens) (h : ∀ y : X, y ∈ (W : X.Opens) → y ∉ C) :
    (componentPowerIdeal I D C).ideal W = ⊤ := by
  by_cases hC : IsIrreducibleComponentOfSupport D C
  · rw [componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC, idealSheafData_ideal_pow,
      ideal_vanishingIdeal_eq_top_of_disjoint C hC.isClosed W h, ← Ideal.one_eq_top, one_pow]
  · rw [componentPowerIdeal_of_not_isIrreducibleComponentOfSupport I D hC]
    exact idealSheafData_ideal_top W

/- English proof (authored)
If the point lies on a component, take an affine étale chart in which the divisor is a coordinate divisor and all its support in the chart belongs to that component. On every affine open inside the chart the component's vanishing ideal agrees with the divisor ideal, generated by the restricted coordinate. The component-power ideal is therefore generated by the corresponding power of this coordinate, a nonzerodivisor. Every other component is disjoint from the chart, so its contribution is the unit ideal. The intersection is bounded above by the chosen component ideal and below by the product of all component ideals, which has the same sections there. If the point is off every component, take the open complement of their finite closed union. On any affine open inside it every component power is the unit ideal, so the product and the intersection are the unit ideal, generated by 1.
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

/- English proof (authored)
Induct on the list of divisors. For the empty list, use the whole scheme and the unit generator. Otherwise intersect the neighborhoods giving a single nonzerodivisor generator for the first divisor's contribution and for the product of the remaining contributions. On every affine open inside this intersection the full product is generated by the product of their generators, which remains a nonzerodivisor.
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

/- English proof (authored)
Every listed divisor is étale locally a coordinate divisor by strict normal crossings. The product calculation gives a neighborhood of each point where every affine open has a nonzerodivisor generator for the product. Choose an affine basic neighborhood of the point inside it. The generator on that basic open gives the required local generation of the monomial factor.
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

/- English proof (authored)
The hypothesis says that the extended natural number is strictly greater than n. Every such value, including infinity, is at least n + 1.
-/
private theorem natCast_add_one_le_of_not_le (n : ℕ) (b : ℕ∞) (h : ¬ b ≤ (n : ℕ∞)) :
    ((n + 1 : ℕ) : ℕ∞) ≤ b := by
  rw [Nat.cast_succ]
  exact ENat.natCast_add_one_le_iff.2 (not_le.mp h)

/- English proof (authored)
The specified position is the only one whose mapped entry can differ from the identity. Removing all the identity factors leaves the mapped entry at that position. This works even when the original list contains repeated entries, since the hypothesis is imposed on positions.
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

/- English proof (authored)
Suppose the point also lies on the second divisor. Its coordinate germ then belongs to the maximal ideal, which by hypothesis is generated by the first coordinate germ. Express the second germ as a multiple of the first. Clear the coefficient's denominator in the affine localization, then clear any remaining localization equality by another element outside the point's prime. This puts the second coordinate times a product of denominators in the affine ideal generated by the first coordinate. Because the coordinates are distinct on the étale chart, the second coordinate acts injectively modulo that ideal. Thus the product of denominators lies in the first-coordinate ideal. Its germ is therefore in the maximal ideal, yet it is a unit because every denominator is outside the prime. This is a contradiction.
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

/- English proof (authored)
Take an étale boundary chart at the generic point of the given divisor component. The chosen divisor stalk is the maximal ideal. Any other boundary entry is the unit ideal on the chart or is given by a distinct coordinate. In the latter case its support cannot contain the point, since the second-coordinate argument excludes this when the chosen divisor generates the maximal ideal. All these other divisor contributions therefore have unit stalk. The product stalk reduces to the chosen divisor's contribution, which is its stalk raised to the order along the component.
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

/- English proof (authored)
At the generic point the monomial factor's stalk is the maximal ideal raised to the finite order of the original ideal along the component. This gives a lower bound on its order by that exponent. If its order were greater, the maximal-ideal power would lie in the next power. The original ideal's stalk is contained in the maximal-ideal power with the original order as exponent, so it would then lie in the next power too. That contradicts the exact finite order of the original ideal at the generic point.
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

/- English proof (authored)
The residual factor is defined as the ideal quotient of the original ideal by the monomial factor.
-/
theorem nonMonomialFactorIdeal_eq_idealSheafColon [TopologicalSpace.NoetherianSpace ↥X] [IsLocallyNoetherian X]
    (E : List X.IdealSheafData) (I : X.IdealSheafData) :
    nonMonomialFactorIdeal E I = idealSheafColon I (monomialFactorIdeal E I) := rfl

/- English proof (authored)
Induct on the list of principal ideals. For the empty list the product is the unit ideal. Otherwise write the given element as the first generator times a coefficient, using its membership in the first principal ideal. For each remaining ideal, membership of this product and the cancellation hypothesis show that the coefficient belongs to that ideal. The tail satisfies the same pairwise cancellation assumptions, so the coefficient belongs to the product of the tail by induction. The original element then belongs to the full product.
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

/- English proof (authored)
Write the localized element and the coefficient of the generator as fractions. Clear their denominators in the equality expressing divisibility, multiplying by one further denominator to obtain the equality in the original ring. The original cancellation property shows that the numerator times the necessary denominators is divisible by d. In the localization this says that the localized element times a product of denominators belongs to the extended principal ideal. These denominators become units, so the localized element itself belongs to the ideal.
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

/- English proof (authored)
On the affine étale chart, the coordinate with the second index acts injectively modulo the given power of the coordinate with the first index, because the indices are distinct. The stalk is the localization of the chart ring at the point's prime. Apply preservation of the cancellation property under localization. The image of the first coordinate power is the same power of its germ, giving the stated membership.
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

/- English proof (authored)
First show that the original ideal is contained in its proposed monomial factor by testing stalks. Choose an affine étale boundary chart at a point. A boundary entry that misses the point contributes the unit ideal. An entry through the point contributes the principal ideal generated by its coordinate germ raised to the order along the component through the point. The original stalk is contained in each of these principal ideals by the generic-order bound along a divisor. Distinct boundary entries through the point have distinct coordinates. Each coordinate germ can be cancelled modulo any power of another, and repeated cancellation gives the same property for their powers. Unit generators satisfy the cancellation condition as well. The product membership lemma now puts the original stalk inside the product of all these principal ideals, which is the monomial stalk. The monomial factor is locally generated by a nonzerodivisor. For an ideal contained in such a factor, multiplying the factor by the ideal quotient recovers the ideal. This is the proposed product.
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

/- English proof (authored)
Take the image of the affine open under the open inclusion. It is affine, lies inside the original open, and its inverse image contains the given affine open. The affine formula for pullback of ideal sheaves expresses the restricted ideal there as extension along the indicated map on sections.
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

/- English proof (authored)
Take any affine open of the open subscheme. Its image is an ambient affine open contained in the specified open. On the chosen affine open of the subscheme, each restricted ideal is obtained by extending the section ideal on the image. Those section ideals agree by hypothesis. Hence the restricted ideals agree on every affine open and are equal.
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

/- English proof (authored)
The multiplicative identity is the unit ideal sheaf. Its pullback to an open is the unit ideal sheaf there.
-/
private theorem idealSheafData_comap_one (Ω : X.Opens) :
    (1 : X.IdealSheafData).comap Ω.ι = 1 := by
  rw [Scheme.IdealSheafData.one_eq_top]
  exact Scheme.IdealSheafData.comap_top _

/- English proof (authored)
Induct on the number of factors. The empty product pulls back to the unit ideal. Split a nonempty product into its first factor and the remaining factors. Pullback preserves the product of two factors, and induction handles the remaining factors.
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

/- English proof (authored)
If the point lies on a divisor component, choose an affine étale chart that meets the divisor only along this component and where its vanishing ideal equals the divisor ideal. On any affine open inside the chart, its contribution is the divisor ideal raised to the order along that component. Other components miss the chart and contribute unit ideals. The intersection of the component-power ideals lies between their product and the chosen power, which have equal section ideals there. If the point lies on no component, take the complement of the finite closed union of components. Each contribution is the unit ideal on all affine opens inside it, so the intersection agrees there with the zeroth power of the divisor.
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

/- English proof (authored)
Induct on the size of the finite family. The empty products agree on the whole scheme. For a nonempty family, find a neighborhood and exponent for the first divisor, and a neighborhood and exponents for the remaining product by induction. Intersect the neighborhoods. On every affine open in the intersection, multiply the established section equalities for the first and remaining factors. This gives the product of the powers with the combined exponents.
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

/- English proof (authored)
Take the monomial factor to be the product of the contributions along all boundary divisors and the residual factor to be the ideal quotient by that product. Their product is the original ideal by the factorization result. Off all listed divisor supports each contribution has unit stalk, so the monomial factor has support contained in the boundary. Around each point the neighborhood formula writes the section ideals of the monomial factor as a product of powers of boundary ideals. Equality on all affine opens of the neighborhood gives equality after restriction, and restriction preserves products and powers. It remains to check the residual support. At the generic point of a boundary component the monomial factor is the maximal ideal raised to the original order along that component. If the residual support contained the component, its stalk would be contained in the maximal ideal there. The product identity would force the original stalk into the next power, contradicting its order. Thus no boundary component is contained in the residual support.
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
