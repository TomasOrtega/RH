import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocUApply
import Development.AutomorphicArithmetic.TwistedTraces.ExistsCompactOpenFamilyInfFixedNeBot
import Development.AutomorphicArithmetic.TwistedTraces.TrOnRestrictAndEqOfMapsInto
import Development.AutomorphicArithmetic.TwistedTraces.LeClosureSpanAllOfCommutingUnitaryReps
import Development.AutomorphicArithmetic.TwistedTraces.MemFixedVectorsOfProductOfCompactOpen
import Development.AutomorphicArithmetic.TwistedTraces.IsotypicComponentProductOfSmoothReps
import Development.AutomorphicArithmetic.TwistedTraces.TwistedIntertwinerFixedVectorsOfIrreducible
import Development.AutomorphicArithmetic.TwistedTraces.IsotypicIntersectionProductEq
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

/- English proof (translation)
Introduce `r G _ _ _ _ _ _ H _ _ _ S _ _ π τ V Z hsm hirr hcm hZc hZV hZi hV hadm s I R hRZ hRs hI`. Distinguish the cases in `hZ : Z = ⊥`. Use `⟨0, fun U T A t hU _ _ _ _ _ _ => ?_⟩` and prove the remaining obligations. Establish `hb : (Z ⊓ ⨅ i, fixU (π i) (U i)) = ⊥` using `by rw [hZ, bot_inf_eq]`. Use `haveI := hadm U hU`.

Rewrite using `[zero_mul, (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (U i)) (Z ⊓ ⨅ i, fixU (π i) (U i)) ((List.ofFn T).prod ∘L R)).1 0 ?_, map_zero]`. Introduce `v`. Establish `hv0 : (v : H) = 0`. Establish `h : ∀ w ∈ (Z ⊓ ⨅ i, fixU (π i) (U i)), w = 0`. Rewrite using `[hb]`.

Simplify using the standard rewrite rules. Conclude with `h _ v.2`. Simplify using `[hv0]`. Establish `hX : ∀ (U : ∀ i, Subgroup (G i)) v, v ∈ Z ⊓ ⨅ i, fixU (π i) (U i) ↔ v ∈ Z ∧ ∀ i, v ∈ fixU (π i) (U i)` using `fun U v => by`. Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf]`.

Take `⟨U₀, hU₀, h0⟩` from `UpperTheory.exists_compactOpen_family_inf_fixed_ne_bot r G H π hcm Z hZc hZi hZ`. Take `⟨hS, -⟩` from `UpperTheory.le_closure_spanAll_of_commuting_unitaryReps r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV hadm hZ`. Establish `hmono : ∀ L U : ∀ i, Subgroup (G i), (∀ i, L i ≤ U i) → Z ⊓ ⨅ i, fixU (π i) (U i) ≤ Z ⊓ ⨅ i, fixU (π i) (L i)` using `fun L U h v hv => (hX L v).2 ⟨hv.1, fun i u hu => ((hX U v).1 hv).2 i u (h i hu)⟩`. Establish `hmF : ∀ i (L U : Subgroup (G i)), L ≤ U → ∀ v ∈ fixU (π i) U, v ∈ fixU (π i) L` using `fun i L U h v hv u hu => hv u (h hu)`. Establish `hmS : ∀ i (L U : Subgroup (G i)), L ≤ U → fixedVectors (τ i) U ≤ fixedVectors (τ i) L` using `fun i L U h v hv => mem_fixedVectors.2 fun u hu => mem_fixedVectors.1 hv u (h hu)`.

Establish `hSK : ∀ i (K : Subgroup (G i)), IsCompact (K : Set (G i)) → IsOpen (K : Set (G i)) → FiniteDimensional ℂ (fixedVectors (τ i) K)`. Introduce `i K hc ho`. Establish `h` using `hS (Function.update U₀ i K) (fun j => by`. Distinguish the cases in `e : j = i`. Substitute `e` using the available equality.

Rewrite using `[Function.update_self]`. Conclude with `⟨hc, ho⟩`. Rewrite using `[Function.update_of_ne e]`. Conclude with `hU₀ j) i`. Rewrite `h` using `[Function.update_self]`. Then use the resulting hypothesis.

Use `haveI hfd0 : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U₀ i)) := hadm U₀ hU₀`. Take `⟨h1, -⟩` from `UpperTheory.isotypic_component_product_of_smooth_reps r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV U₀ hU₀ hfd0 h0`. Establish `hex` using `fun i => UpperTheory.twisted_intertwiner_fixedVectors_of_irreducible (G i) H (S i) (τ i) (hsm i) (hirr i) (π i) (s i) (I i) (hI i) (hSK i) (U₀ i) (hU₀ i).1 (hU₀ i).2 (h1 i).2`. Use `choose T₀ A₀ t₀ hP ht₀ ht₀0 using hex`. Establish `a1 : ∀ i v, T₀ i v ∈ fixU (π i) (U₀ i)` using `fun i => (hP i).1`.

Establish `a2 : ∀ i, ∀ x, A₀ i x ∈ fixedVectors (τ i) (U₀ i)` using `fun i => (hP i).2.1`. Establish `a3 : ∀ i, ∀ v ∈ Z, T₀ i v ∈ Z` using `fun i => (hP i).2.2.1 Z hZc (hZi i)`. Establish `a4 : ∀ i j, i ≠ j → ∀ h v, T₀ i (π j h v) = π j h (T₀ i v)` using `fun i j hij => (hP i).2.2.2.1 (G j) (π j) (hcm i j hij)`. Establish `a5 : ∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x, T₀ i (f x) = f (A₀ i x)` using `fun i => (hP i).2.2.2.2`. Establish `hprod : (∏ i, t₀ i) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => ht₀0 i`.

Take `⟨κ₀, hκ₀⟩` from `UpperTheory.isotypic_intersection_product_eq r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV hadm s I R hRZ hRs hI U₀ hU₀ h0`. Use `⟨κ₀, fun U T A t hU b1 b3 b4 b5 b2 bt => ?_⟩` and prove the remaining obligations. Establish `hL : ∀ i, IsCompact ((U i ⊓ U₀ i : Subgroup (G i)) : Set (G i)) ∧ IsOpen ((U i ⊓ U₀ i : Subgroup (G i)) : Set (G i))` using `fun i => ⟨(hU i).1.inter (hU₀ i).1, (hU i).2.inter (hU₀ i).2⟩`. Establish `hle0` using `hmono (fun i => U i ⊓ U₀ i) U₀ fun i => inf_le_right`. Establish `hleU` using `hmono (fun i => U i ⊓ U₀ i) U fun i => inf_le_left`.

Establish `hneL : (Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i)) ≠ ⊥` using `fun e => h0 (le_bot_iff.1 (e ▸ hle0))`. Use `haveI hfdL : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i)) := hadm _ hL`. Use `haveI hfdU : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i)) := hadm U hU`. Take `⟨κ, hκ⟩` from `UpperTheory.isotypic_intersection_product_eq r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV hadm s I R hRZ hRs hI (fun i => U i ⊓ U₀ i) hL hneL`. Establish `e1` using `hκ T₀ A₀ t₀ (fun i v => hmF i _ _ inf_le_right _ (a1 i v)) a3 a4 a5 (fun i x => hmS i _ _ inf_le_right (a2 i x)) ht₀`.

Establish `e2` using `hκ₀ T₀ A₀ t₀ a1 a3 a4 a5 a2 ht₀`. Establish `e3` using `(UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (U₀ i)) (Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i)) ((List.ofFn T₀).prod ∘L R)).2 hle0 fun v hv => UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z U₀ T₀ a1 a3 a4 _ (hRZ v (Submodule.mem_inf.1 hv).1)`. Establish `hκκ : κ = κ₀` using `mul_right_cancel₀ hprod (by rw [← e1, ← e2, e3])`. Establish `e4` using `hκ T A t (fun i v => hmF i _ _ inf_le_left _ (b1 i v)) b3 b4 b5 (fun i x => hmS i _ _ inf_le_left (b2 i x)) bt`. Establish `e5` using `(UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (U i)) (Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i)) ((List.ofFn T).prod ∘L R)).2 hleU fun v hv => UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z U T b1 b3 b4 _ (hRZ v (Submodule.mem_inf.1 hv).1)`.

Rewrite using `[← e5, e4, hκκ]`.
-/
theorem UpperTheory.isotypic_multiplicity_tensor_product :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (V Z : Submodule ℂ H), (∀ i, GroundTheory.Automorphic.IsSmooth (τ i)) → (∀ i, (τ i).IsIrreducible) → (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → IsClosed (Z : Set H) → Z ≤ V → (∀ i, (π i).IsInvariant Z) → (∀ i, V ≤ (spanAll (τ i) (π i) V).topologicalClosure) → (∀ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i))) → ∀ (s : ∀ i, G i ≃ₜ* G i) (I : ∀ i, S i ≃ₗ[ℂ] S i) (R : H →L[ℂ] H), (∀ v ∈ Z, R v ∈ Z) → (∀ i g, ∀ v ∈ Z, R (π i g v) = π i (s i g) (R v)) → (∀ i g x, I i (τ i g x) = τ i (s i g) (I i x)) → ∃ c : ℂ, ∀ (U : ∀ i, Subgroup (G i)) (T : Fin r → H →L[ℂ] H) (A : ∀ i, S i →ₗ[ℂ] S i) (t : Fin r → ℂ), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → (∀ i v, T i v ∈ fixU (π i) (U i)) → (∀ i, ∀ v ∈ Z, T i v ∈ Z) → (∀ i j, i ≠ j → ∀ h v, T i (π j h v) = π j h (T i v)) → (∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x, T i (f x) = f (A i x)) → (∀ i x, A i x ∈ fixedVectors (τ i) (U i)) → (∀ i, HasFinTrace (A i ∘ₗ (I i : S i →ₗ[ℂ] S i)) (t i)) → trOn (Z ⊓ ⨅ i, fixU (π i) (U i)) ((List.ofFn T).prod ∘L R) = c * ∏ i, t i := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ V Z hsm hirr hcm hZc hZV hZi hV hadm s I R hRZ hRs hI
  by_cases hZ : Z = ⊥
  · refine ⟨0, fun U T A t hU _ _ _ _ _ _ => ?_⟩
    have hb : (Z ⊓ ⨅ i, fixU (π i) (U i)) = ⊥ := by rw [hZ, bot_inf_eq]
    haveI := hadm U hU
    rw [zero_mul, (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (U i)) (Z ⊓ ⨅ i, fixU (π i) (U i))
      ((List.ofFn T).prod ∘L R)).1 0 ?_, map_zero]
    intro v
    have hv0 : (v : H) = 0 := by
      have h : ∀ w ∈ (Z ⊓ ⨅ i, fixU (π i) (U i)), w = 0 := by
        rw [hb]
        simp
      exact h _ v.2
    simp [hv0]
  have hX : ∀ (U : ∀ i, Subgroup (G i)) v, v ∈ Z ⊓ ⨅ i, fixU (π i) (U i) ↔ v ∈ Z ∧ ∀ i, v ∈ fixU (π i) (U i) := fun U v => by
    simp only [Submodule.mem_inf, Submodule.mem_iInf]
  obtain ⟨U₀, hU₀, h0⟩ := UpperTheory.exists_compactOpen_family_inf_fixed_ne_bot r G H π hcm Z hZc hZi hZ
  obtain ⟨hS, -⟩ := UpperTheory.le_closure_spanAll_of_commuting_unitaryReps r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV hadm hZ
  have hmono : ∀ L U : ∀ i, Subgroup (G i), (∀ i, L i ≤ U i) → Z ⊓ ⨅ i, fixU (π i) (U i) ≤ Z ⊓ ⨅ i, fixU (π i) (L i) :=
    fun L U h v hv => (hX L v).2 ⟨hv.1, fun i u hu => ((hX U v).1 hv).2 i u (h i hu)⟩
  have hmF : ∀ i (L U : Subgroup (G i)), L ≤ U → ∀ v ∈ fixU (π i) U, v ∈ fixU (π i) L :=
    fun i L U h v hv u hu => hv u (h hu)
  have hmS : ∀ i (L U : Subgroup (G i)), L ≤ U → fixedVectors (τ i) U ≤ fixedVectors (τ i) L :=
    fun i L U h v hv => mem_fixedVectors.2 fun u hu => mem_fixedVectors.1 hv u (h hu)
  have hSK : ∀ i (K : Subgroup (G i)), IsCompact (K : Set (G i)) → IsOpen (K : Set (G i)) →
      FiniteDimensional ℂ (fixedVectors (τ i) K) := by
    intro i K hc ho
    have h := hS (Function.update U₀ i K) (fun j => by
      by_cases e : j = i
      · subst e
        rw [Function.update_self]
        exact ⟨hc, ho⟩
      · rw [Function.update_of_ne e]
        exact hU₀ j) i
    rwa [Function.update_self] at h
  haveI hfd0 : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U₀ i)) := hadm U₀ hU₀
  obtain ⟨h1, -⟩ := UpperTheory.isotypic_component_product_of_smooth_reps r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV U₀ hU₀ hfd0 h0
  have hex := fun i => UpperTheory.twisted_intertwiner_fixedVectors_of_irreducible (G i) H (S i) (τ i) (hsm i) (hirr i) (π i) (s i) (I i) (hI i)
    (hSK i) (U₀ i) (hU₀ i).1 (hU₀ i).2 (h1 i).2
  choose T₀ A₀ t₀ hP ht₀ ht₀0 using hex
  have a1 : ∀ i v, T₀ i v ∈ fixU (π i) (U₀ i) := fun i => (hP i).1
  have a2 : ∀ i, ∀ x, A₀ i x ∈ fixedVectors (τ i) (U₀ i) := fun i => (hP i).2.1
  have a3 : ∀ i, ∀ v ∈ Z, T₀ i v ∈ Z := fun i => (hP i).2.2.1 Z hZc (hZi i)
  have a4 : ∀ i j, i ≠ j → ∀ h v, T₀ i (π j h v) = π j h (T₀ i v) := fun i j hij =>
    (hP i).2.2.2.1 (G j) (π j) (hcm i j hij)
  have a5 : ∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x, T₀ i (f x) = f (A₀ i x) := fun i => (hP i).2.2.2.2
  have hprod : (∏ i, t₀ i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ht₀0 i
  obtain ⟨κ₀, hκ₀⟩ := UpperTheory.isotypic_intersection_product_eq r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV hadm s I R hRZ hRs hI U₀ hU₀ h0
  refine ⟨κ₀, fun U T A t hU b1 b3 b4 b5 b2 bt => ?_⟩
  have hL : ∀ i, IsCompact ((U i ⊓ U₀ i : Subgroup (G i)) : Set (G i)) ∧ IsOpen ((U i ⊓ U₀ i : Subgroup (G i)) : Set (G i)) :=
    fun i => ⟨(hU i).1.inter (hU₀ i).1, (hU i).2.inter (hU₀ i).2⟩
  have hle0 := hmono (fun i => U i ⊓ U₀ i) U₀ fun i => inf_le_right
  have hleU := hmono (fun i => U i ⊓ U₀ i) U fun i => inf_le_left
  have hneL : (Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i)) ≠ ⊥ := fun e => h0 (le_bot_iff.1 (e ▸ hle0))
  haveI hfdL : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i)) := hadm _ hL
  haveI hfdU : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i)) := hadm U hU
  obtain ⟨κ, hκ⟩ := UpperTheory.isotypic_intersection_product_eq r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV hadm s I R hRZ hRs hI
    (fun i => U i ⊓ U₀ i) hL hneL
  have e1 := hκ T₀ A₀ t₀ (fun i v => hmF i _ _ inf_le_right _ (a1 i v)) a3 a4 a5
    (fun i x => hmS i _ _ inf_le_right (a2 i x)) ht₀
  have e2 := hκ₀ T₀ A₀ t₀ a1 a3 a4 a5 a2 ht₀
  have e3 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (U₀ i)) (Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i))
    ((List.ofFn T₀).prod ∘L R)).2 hle0 fun v hv =>
      UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z U₀ T₀ a1 a3 a4 _ (hRZ v (Submodule.mem_inf.1 hv).1)
  have hκκ : κ = κ₀ := mul_right_cancel₀ hprod (by rw [← e1, ← e2, e3])
  have e4 := hκ T A t (fun i v => hmF i _ _ inf_le_left _ (b1 i v)) b3 b4 b5
    (fun i x => hmS i _ _ inf_le_left (b2 i x)) bt
  have e5 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (U i)) (Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i))
    ((List.ofFn T).prod ∘L R)).2 hleU fun v hv =>
      UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z U T b1 b3 b4 _ (hRZ v (Submodule.mem_inf.1 hv).1)
  rw [← e5, e4, hκκ]
