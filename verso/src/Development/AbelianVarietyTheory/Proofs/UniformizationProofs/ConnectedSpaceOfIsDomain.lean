import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConnDvr

/- English proof (translation)
Establish `hne : Nonempty X`. Assume the negation of the conclusion as `h`. Establish `hT : (⊤ : X.Opens) = ⊥`. Use extensionality with `x`. Conclude with `(h ⟨x⟩).elim`.

Establish `: Subsingleton Γ(X, ⊤)` using `CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hT)`. Conclude with `false_of_nontrivial_of_subsingleton Γ(X, ⊤)`. Use `{ toNonempty := hne, isPreconnected_univ := ?_ }` and prove the remaining obligations. Introduce `U W hU hW hc ⟨u, _, hu⟩ ⟨w, _, hw⟩`. Assume the negation of the conclusion as `hd`.

Set `U' : X.Opens` to `⟨U, hU⟩`. Set `W' : X.Opens` to `⟨W, hW⟩`. Establish `h0 : U' ⊓ W' = ⊥` using `le_bot_iff.1 fun y hy => hd ⟨y, trivial, hy⟩`. Establish `h1 : U' ⊔ W' = ⊤` using `top_unique fun y _ => hc (Set.mem_univ y)`. Establish `: Nonempty U'` using `⟨⟨u, hu⟩⟩`.

Establish `: Nonempty W'` using `⟨⟨w, hw⟩⟩`. Establish `hdom : IsDomain Γ(X, U' ⊔ W')` using `by rw [h1]; infer_instance`. Set `e : Γ(X, U' ⊔ W') ≅ CommRingCat.of _` to `(X.sheaf.isProductOfDisjoint U' W' h0).conePointUniqueUpToIso (CommRingCat.prodFanIsLimit _ _)`. Establish `: IsDomain (Γ(X, U') × Γ(X, W'))` using `e.symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _`. Conclude with `false_of_nontrivial_of_product_domain Γ(X, U') Γ(X, W')`.
-/
theorem connectedSpace_of_isDomain (X : Scheme.{0}) [IsDomain Γ(X, ⊤)] : ConnectedSpace X := by
  have hne : Nonempty X := by
    by_contra h
    have hT : (⊤ : X.Opens) = ⊥ := by
      ext x
      exact (h ⟨x⟩).elim
    have : Subsingleton Γ(X, ⊤) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hT)
    exact false_of_nontrivial_of_subsingleton Γ(X, ⊤)
  refine { toNonempty := hne, isPreconnected_univ := ?_ }
  intro U W hU hW hc ⟨u, _, hu⟩ ⟨w, _, hw⟩
  by_contra hd
  let U' : X.Opens := ⟨U, hU⟩
  let W' : X.Opens := ⟨W, hW⟩
  have h0 : U' ⊓ W' = ⊥ := le_bot_iff.1 fun y hy => hd ⟨y, trivial, hy⟩
  have h1 : U' ⊔ W' = ⊤ := top_unique fun y _ => hc (Set.mem_univ y)
  have : Nonempty U' := ⟨⟨u, hu⟩⟩
  have : Nonempty W' := ⟨⟨w, hw⟩⟩
  have hdom : IsDomain Γ(X, U' ⊔ W') := by rw [h1]; infer_instance
  let e : Γ(X, U' ⊔ W') ≅ CommRingCat.of _ :=
    (X.sheaf.isProductOfDisjoint U' W' h0).conePointUniqueUpToIso
      (CommRingCat.prodFanIsLimit _ _)
  have : IsDomain (Γ(X, U') × Γ(X, W')) :=
    e.symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  exact false_of_nontrivial_of_product_domain Γ(X, U') Γ(X, W')

/- English proof (translation)
Distinguish the cases in `h : RingHom.ker φ = ⊥`. Conclude with `Or.inl ((RingHom.injective_iff_ker_eq_bot φ).2 h)`. Establish `hp : (RingHom.ker φ).IsPrime` using `RingHom.ker_isPrime φ`. Establish `hm : (RingHom.ker φ).IsMaximal` using `Ring.DimensionLEOne.maximalOfPrime h hp`. Conclude with `Or.inr (IsLocalRing.eq_maximalIdeal hm).ge`.
-/
theorem injective_or_le_ker {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] (φ : V →+* K) :
    Function.Injective φ ∨ IsLocalRing.maximalIdeal V ≤ RingHom.ker φ := by
  by_cases h : RingHom.ker φ = ⊥
  · exact Or.inl ((RingHom.injective_iff_ker_eq_bot φ).2 h)
  · have hp : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
    have hm : (RingHom.ker φ).IsMaximal := Ring.DimensionLEOne.maximalOfPrime h hp
    exact Or.inr (IsLocalRing.eq_maximalIdeal hm).ge

/- English proof (translation)
Introduce `V _ _ _ B _ hb hc`. Use `⟨geometrically_iff_of_commRing.2 ?_⟩` and prove the remaining obligations. Introduce `K _ _ Y p q H`. Break down `injective_or_le_ker (algebraMap V K) with h | h` into its components or cases. Establish `: FaithfulSMul V K` using `(faithfulSMul_iff_algebraMap_injective V K).2 h`.

Establish `hf : Module.Flat V K` using `inferInstance`. Establish `: Flat (Spec.map (CommRingCat.ofHom (algebraMap V K)))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Conclude with `RingHom.flat_algebraMap_iff.2 hf`. Establish `: IsIso B.hom.appTop` using `(ConcreteCategory.isIso_iff_bijective _).2 hb`.

Establish `: IsIso q.appTop` using `GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback H`. Establish `: IsDomain Γ(Y, ⊤)` using `(asIso q.appTop).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _`. Conclude with `connectedSpace_of_isDomain Y`. Establish `h' : ∀ a ∈ IsLocalRing.maximalIdeal V ^ (0 + 1), algebraMap V K a = 0` using `fun a ha => by`. Rewrite `ha` using `[zero_add, pow_one]`.

Conclude with `h ha`. Set `y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)))` to `Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ (algebraMap V K) h'))`. Establish `hy : y ≫ thick V (IsLocalRing.maximalIdeal V) 0 = Spec.map (CommRingCat.ofHom (algebraMap V K))`. Simplify using `only [y, thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Both sides reduce to the same expression.

Rewrite `H` using `[← hy]`. Set `r : Y ⟶ pullback B.hom (thick V (IsLocalRing.maximalIdeal V) 0)` to `pullback.lift p (q ≫ y) (by rw [H.w, Category.assoc])`. Establish `H' : IsPullback r q (pullback.snd B.hom (thick V (IsLocalRing.maximalIdeal V) 0)) y`. Use `IsPullback.of_right (h₁₂ := pullback.fst _ _) (v₁₃ := B.hom) (h₂₂ := thick V _ 0) ?_ ?_ (IsPullback.of_hasPullback _ _)` and prove the remaining obligations. Rewrite using `[pullback.lift_fst]`.

Conclude with `H`. Conclude with `pullback.lift_snd _ _ _`. Conclude with `hc.geometrically_connectedSpace y r q H'`.
-/
theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (B : Over (Spec (CommRingCat.of V))) [IsProper B.hom], Function.Bijective B.hom.appTop.hom → GeometricallyConnected (thickObj V (IsLocalRing.maximalIdeal V) 0 B).hom → GeometricallyConnected B.hom := by
  intro V _ _ _ B _ hb hc
  refine ⟨geometrically_iff_of_commRing.2 ?_⟩
  intro K _ _ Y p q H
  rcases injective_or_le_ker (algebraMap V K) with h | h
  · have : FaithfulSMul V K := (faithfulSMul_iff_algebraMap_injective V K).2 h
    have hf : Module.Flat V K := inferInstance
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap V K))) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact RingHom.flat_algebraMap_iff.2 hf
    have : IsIso B.hom.appTop := (ConcreteCategory.isIso_iff_bijective _).2 hb
    have : IsIso q.appTop := GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback H
    have : IsDomain Γ(Y, ⊤) :=
      (asIso q.appTop).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
    exact connectedSpace_of_isDomain Y
  · have h' : ∀ a ∈ IsLocalRing.maximalIdeal V ^ (0 + 1), algebraMap V K a = 0 := fun a ha => by
      rw [zero_add, pow_one] at ha
      exact h ha
    let y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1))) :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ (algebraMap V K) h'))
    have hy : y ≫ thick V (IsLocalRing.maximalIdeal V) 0 =
        Spec.map (CommRingCat.ofHom (algebraMap V K)) := by
      simp only [y, thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    rw [← hy] at H
    let r : Y ⟶ pullback B.hom (thick V (IsLocalRing.maximalIdeal V) 0) :=
      pullback.lift p (q ≫ y) (by rw [H.w, Category.assoc])
    have H' : IsPullback r q (pullback.snd B.hom (thick V (IsLocalRing.maximalIdeal V) 0)) y := by
      refine IsPullback.of_right (h₁₂ := pullback.fst _ _) (v₁₃ := B.hom) (h₂₂ := thick V _ 0) ?_ ?_
        (IsPullback.of_hasPullback _ _)
      · rw [pullback.lift_fst]; exact H
      · exact pullback.lift_snd _ _ _
    exact hc.geometrically_connectedSpace y r q H'

end GlobalTheory.ConnDvr
