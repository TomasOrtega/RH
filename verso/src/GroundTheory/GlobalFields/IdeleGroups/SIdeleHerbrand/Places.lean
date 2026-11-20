import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.SIdeleHerbrand.Product
import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Decomposition
import GroundTheory.GlobalFields.IdeleGroups.LocalHerbrandInfinite

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum GroundTheory.GroupCoh
  AdeleBaseChange SemiLocal

open scoped Pointwise NumberField.LiesOver

noncomputable section

namespace IdeleGroup

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

section Finite

variable (v : HeightOneSpectrum (𝓞 K))

omit [NumberField K] [NumberField L] in

/- English proof (translation)
Rewrite using `[MulAction.mem_stabilizer_iff, Subtype.ext_iff, coe_smul_placesOver, HeightOneSpectrum.ext_iff, smul_asIdeal]`.
-/
theorem mem_stabilizer_iff_smul_placesOver (w : PlacesOver L v) (σ : Gal(L/K)) :
    σ ∈ MulAction.stabilizer Gal(L/K) w.1.asIdeal ↔ σ • w = w := by
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, coe_smul_placesOver,
    HeightOneSpectrum.ext_iff, smul_asIdeal]

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `finiteUnitsAbove_smul_apply v σ y w`.
-/
theorem finiteUnitsAbove_smul_apply_of_eq (σ : Gal(L/K))
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) (w w' : PlacesOver L v)
    (h : w' = σ • w) :
    (((σ • y) w' : (w'.1.adicCompletion L)ˣ) : w'.1.adicCompletion L) =
      galEquiv v σ w.1 w'.1 (by rw [h]; rfl) (y w) := by
  subst h
  exact finiteUnitsAbove_smul_apply v σ y w

omit [NumberField K] in

/- English proof (translation)
Rewrite using `[decomposition_smul_def]`. Conclude with `congrFun (congrArg DFunLike.coe (ringHom_ext_adicCompletion w.1 (continuous_galHom _ _ _ h) (continuous_adicCompletionRingHomOf _ _) fun y ↦ by`. Rewrite using `[galHom_algebraMap, adicCompletionRingHomOf_algebraMap])) x`.
-/
theorem galHom_eq_decomposition_smul (w : PlacesOver L v)
    (σ : MulAction.stabilizer Gal(L/K) w.1.asIdeal) (h : w.1 = (σ : Gal(L/K)) • w.1)
    (x : w.1.adicCompletion L) : galHom (σ : Gal(L/K)) w.1 w.1 h x = σ • x := by
  rw [decomposition_smul_def]
  exact congrFun (congrArg DFunLike.coe (ringHom_ext_adicCompletion w.1
    (continuous_galHom _ _ _ h) (continuous_adicCompletionRingHomOf _ _) fun y ↦ by
      rw [galHom_algebraMap, adicCompletionRingHomOf_algebraMap])) x

/- English proof (translation)
Establish `hw : w = (σ : Gal(L/K)) • w` using `((mem_stabilizer_iff_smul_placesOver v w σ).1 σ.2).symm`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[finiteUnitsAbove_smul_apply_of_eq v _ y w w hw, galEquiv_apply, galHom_eq_decomposition_smul]`. Both sides reduce to the same expression.
-/
theorem finiteUnitsAbove_smul_apply_self (w : PlacesOver L v)
    (σ : MulAction.stabilizer Gal(L/K) w.1.asIdeal)
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) : ((σ : Gal(L/K)) • y) w = σ • y w := by
  have hw : w = (σ : Gal(L/K)) • w :=
    ((mem_stabilizer_iff_smul_placesOver v w σ).1 σ.2).symm
  apply Units.ext
  rw [finiteUnitsAbove_smul_apply_of_eq v _ y w w hw, galEquiv_apply,
    galHom_eq_decomposition_smul]
  rfl

/- English proof (translation)
The claim follows from `Units.ext (by rw [finiteUnitsAbove_smul_apply, hy, Units.val_one, map_one, Units.val_one])`.
-/
theorem finiteUnitsAbove_smul_apply_eq_one (σ : Gal(L/K))
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) (w : PlacesOver L v) (hy : y w = 1) :
    (σ • y) (σ • w) = 1 :=
  Units.ext (by rw [finiteUnitsAbove_smul_apply, hy, Units.val_one, map_one, Units.val_one])

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[coe_decomposition_smul_integerUnits, ← coe_integerUnitsAboveIncl_apply, integerUnitsAboveIncl_smul, finiteUnitsAbove_smul_apply_self, coe_decomposition_smul_units, coe_integerUnitsAboveIncl_apply]`.
-/
theorem integerUnitsAbove_smul_apply_self (w : PlacesOver L v)
    (σ : MulAction.stabilizer Gal(L/K) w.1.asIdeal)
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) :
    ((σ : Gal(L/K)) • z) w = σ • z w := by
  apply Units.ext
  apply Subtype.ext
  rw [coe_decomposition_smul_integerUnits, ← coe_integerUnitsAboveIncl_apply,
    integerUnitsAboveIncl_smul, finiteUnitsAbove_smul_apply_self, coe_decomposition_smul_units,
    coe_integerUnitsAboveIncl_apply]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[integerUnitsAbove_smul_apply, hz, Units.val_one, OneMemClass.coe_one, map_one, Units.val_one, OneMemClass.coe_one]`.
-/
theorem integerUnitsAbove_smul_apply_eq_one (σ : Gal(L/K))
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) (w : PlacesOver L v)
    (hz : z w = 1) : (σ • z) (σ • w) = 1 := by
  apply Units.ext
  apply Subtype.ext
  rw [integerUnitsAbove_smul_apply, hz, Units.val_one, OneMemClass.coe_one, map_one,
    Units.val_one, OneMemClass.coe_one]

variable [IsGalois K L] [Fintype Gal(L/K)]

open AdicLiesOver in

/- English proof (translation)
Establish `: IsCyclic Gal(L/K)` using `⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩`. Take `⟨τ, hτ⟩` from `IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w.1.asIdeal)`. Set `_ : Fintype (MulAction.stabilizer Gal(L/K) w.1.asIdeal)` to `Fintype.ofFinite _`. Rewrite using `[cycHerbrand_mulOrbit (U := fun u : PlacesOver L v ↦ (u.1.adicCompletion L)ˣ) (finiteUnitsAbove_smul_apply_eq_one v) w _ (mem_stabilizer_iff_smul_placesOver v w) (finiteUnitsAbove_smul_apply_self v w) σ hσ τ hτ]`. Conclude with `(cycHerbrand_adicCompletion_units v w.1 τ hτ).2`.
-/
theorem cycHerbrand_finiteUnitsAbove (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (w : PlacesOver L v) :
    cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K)
        ((u : PlacesOver L v) → (u.1.adicCompletion L)ˣ)) σ =
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w.1.asIdeal)
  let _ : Fintype (MulAction.stabilizer Gal(L/K) w.1.asIdeal) := Fintype.ofFinite _
  rw [cycHerbrand_mulOrbit (U := fun u : PlacesOver L v ↦ (u.1.adicCompletion L)ˣ)
    (finiteUnitsAbove_smul_apply_eq_one v) w _ (mem_stabilizer_iff_smul_placesOver v w)
    (finiteUnitsAbove_smul_apply_self v w) σ hσ τ hτ]
  exact (cycHerbrand_adicCompletion_units v w.1 τ hτ).2

/- English proof (translation)
Establish `: IsCyclic Gal(L/K)` using `⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩`. Take `⟨τ, hτ⟩` from `IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w.1.asIdeal)`. Set `_ : Fintype (MulAction.stabilizer Gal(L/K) w.1.asIdeal)` to `Fintype.ofFinite _`. Use `subsingleton_cycTateZero_adicCompletionIntegers_units v w.1 he τ hτ` as an intermediate fact. Conclude with `(cycTateZeroMulOrbitEquiv (U := fun u : PlacesOver L v ↦ (u.1.adicCompletionIntegers L)ˣ) (integerUnitsAbove_smul_apply_eq_one v) w _ (mem_stabilizer_iff_smul_placesOver v w) (integerUnitsAbove_smul_apply_self v w) σ hσ τ hτ).toEquiv.subsingleton`.
-/
theorem subsingleton_cycTateZero_integerUnitsAbove (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (w : PlacesOver L v)
    (he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1) :
    Subsingleton (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K)
      ((u : PlacesOver L v) → (u.1.adicCompletionIntegers L)ˣ)) σ) := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w.1.asIdeal)
  let _ : Fintype (MulAction.stabilizer Gal(L/K) w.1.asIdeal) := Fintype.ofFinite _
  have := subsingleton_cycTateZero_adicCompletionIntegers_units v w.1 he τ hτ
  exact (cycTateZeroMulOrbitEquiv (U := fun u : PlacesOver L v ↦ (u.1.adicCompletionIntegers L)ˣ)
    (integerUnitsAbove_smul_apply_eq_one v) w _ (mem_stabilizer_iff_smul_placesOver v w)
    (integerUnitsAbove_smul_apply_self v w) σ hσ τ hτ).toEquiv.subsingleton

/- English proof (translation)
Establish `: IsCyclic Gal(L/K)` using `⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩`. Take `⟨τ, hτ⟩` from `IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w.1.asIdeal)`. Set `_ : Fintype (MulAction.stabilizer Gal(L/K) w.1.asIdeal)` to `Fintype.ofFinite _`. Use `subsingleton_cycTateNegOne_adicCompletionIntegers_units v w.1 he τ hτ` as an intermediate fact. Conclude with `(cycTateNegOneMulOrbitEquiv (U := fun u : PlacesOver L v ↦ (u.1.adicCompletionIntegers L)ˣ) (integerUnitsAbove_smul_apply_eq_one v) w _ (mem_stabilizer_iff_smul_placesOver v w) (integerUnitsAbove_smul_apply_self v w) σ hσ τ hτ).toEquiv.subsingleton`.
-/
theorem subsingleton_cycTateNegOne_integerUnitsAbove (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (w : PlacesOver L v)
    (he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1) :
    Subsingleton (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K)
      ((u : PlacesOver L v) → (u.1.adicCompletionIntegers L)ˣ)) σ) := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w.1.asIdeal)
  let _ : Fintype (MulAction.stabilizer Gal(L/K) w.1.asIdeal) := Fintype.ofFinite _
  have := subsingleton_cycTateNegOne_adicCompletionIntegers_units v w.1 he τ hτ
  exact (cycTateNegOneMulOrbitEquiv
    (U := fun u : PlacesOver L v ↦ (u.1.adicCompletionIntegers L)ˣ)
    (integerUnitsAbove_smul_apply_eq_one v) w _ (mem_stabilizer_iff_smul_placesOver v w)
    (integerUnitsAbove_smul_apply_self v w) σ hσ τ hτ).toEquiv.subsingleton

end Finite

section Infinite

def infiniteCompletionCongr {u u' : InfinitePlace L} (h : u = u') :
    u.Completion ≃+* u'.Completion :=
  h ▸ RingEquiv.refl _

omit [NumberField L] in
/- English proof (translation)
Substitute `h` using the available equality. Conclude with `continuous_id`.
-/
theorem continuous_infiniteCompletionCongr {u u' : InfinitePlace L} (h : u = u') :
    Continuous (infiniteCompletionCongr h) := by
  subst h
  exact continuous_id

omit [NumberField L] in
/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem infiniteCompletionCongr_algebraMap {u u' : InfinitePlace L} (h : u = u') (x : L) :
    infiniteCompletionCongr h (algebraMap L u.Completion x) = algebraMap L u'.Completion x := by
  subst h
  rfl

/- English proof (translation)
Set `_ : Algebra M M'` to `(τ : M →+* M').toAlgebra`. Conclude with `NumberField.LiesOver.continuous_completionMap`.
-/
theorem continuous_infiniteCompletionMap {M M' : Type*} [Field M] [NumberField M] [Field M']
    [NumberField M'] (τ : M ≃+* M') (w' : InfinitePlace M') :
    Continuous (infiniteCompletionMap τ w') := by
  let _ : Algebra M M' := (τ : M →+* M').toAlgebra
  exact NumberField.LiesOver.continuous_completionMap

variable (v : InfinitePlace K)

/- English proof (translation)
Take `rfl : u = ⟨w.1.comap ((σ : L ≃+* L) : L →+* L), comap_mem_placesOver v σ w⟩` from `Subtype.ext h`. Conclude with `infiniteUnitsAbove_smul_apply v σ y w`.
-/
theorem infiniteUnitsAbove_smul_apply_of_eq (σ : Gal(L/K))
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) (u w : v.placesOver L)
    (h : u.1 = w.1.comap ((σ : L ≃+* L) : L →+* L)) :
    (((σ • y) w : (w.1.Completion)ˣ) : w.1.Completion) =
      infiniteCompletionMap (σ : L ≃+* L) w.1 (infiniteCompletionCongr h (y u)) := by
  obtain rfl : u = ⟨w.1.comap ((σ : L ≃+* L) : L →+* L), comap_mem_placesOver v σ w⟩ :=
    Subtype.ext h
  exact infiniteUnitsAbove_smul_apply v σ y w

omit [NumberField K] [NumberField L] in
/- English proof (translation)
Rewrite using `[comap_eq_inv_smul, InfinitePlace.coe_smul_placesOver, inv_smul_smul]`.
-/
theorem eq_comap_smul_placesOver (σ : Gal(L/K)) (w : v.placesOver L) :
    w.1 = (σ • w).1.comap ((σ : L ≃+* L) : L →+* L) := by
  rw [comap_eq_inv_smul, InfinitePlace.coe_smul_placesOver, inv_smul_smul]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[infiniteUnitsAbove_smul_apply_of_eq v σ y w (σ • w) (eq_comap_smul_placesOver v σ w), hy, Units.val_one, map_one, map_one, Units.val_one]`.
-/
theorem infiniteUnitsAbove_smul_apply_eq_one (σ : Gal(L/K))
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) (w : v.placesOver L) (hy : y w = 1) :
    (σ • y) (σ • w) = 1 := by
  apply Units.ext
  rw [infiniteUnitsAbove_smul_apply_of_eq v σ y w (σ • w) (eq_comap_smul_placesOver v σ w), hy,
    Units.val_one, map_one, map_one, Units.val_one]

omit [NumberField K] [NumberField L] in

/- English proof (translation)
Rewrite using `[MulAction.mem_stabilizer_iff, Subtype.ext_iff, InfinitePlace.coe_smul_placesOver]`.
-/
theorem mem_stabilizer_iff_smul_placesOver_infinite (w : v.placesOver L) (σ : Gal(L/K)) :
    σ ∈ MulAction.stabilizer Gal(L/K) w.1 ↔ σ • w = w := by
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, InfinitePlace.coe_smul_placesOver]

omit [NumberField K] in

/- English proof (translation)
Rewrite using `[infiniteDecomposition_smul_def]`. Use `ringHom_ext_completion w.1 (f := (infiniteCompletionMap ((σ : Gal(L/K)) : L ≃+* L) w.1).comp (infiniteCompletionCongr h).toRingHom) ((continuous_infiniteCompletionMap _ _).comp (continuous_infiniteCompletionCongr h)) (continuous_completionRingHomOf σ.2) fun y ↦ by` as an intermediate fact. Rewrite using `[completionRingHomOf_coe]`. Express the relevant statement in the definitionally equal form `infiniteCompletionMap _ w.1 (infiniteCompletionCongr h (algebraMap L w.1.Completion y.ofAbs)) = algebraMap L w.1.Completion (withAbsMapOf w.1 (σ : Gal(L/K)) y).ofAbs`. Rewrite using `[infiniteCompletionCongr_algebraMap, infiniteCompletionMap_algebraMap, ofAbs_withAbsMapOf]`.

Both sides reduce to the same expression. Conclude with `congrFun (congrArg DFunLike.coe this) x`.
-/
theorem infiniteCompletionMap_eq_decomposition_smul (w : v.placesOver L)
    (σ : MulAction.stabilizer Gal(L/K) w.1)
    (h : w.1 = w.1.comap (((σ : Gal(L/K)) : L ≃+* L) : L →+* L)) (x : w.1.Completion) :
    infiniteCompletionMap ((σ : Gal(L/K)) : L ≃+* L) w.1 (infiniteCompletionCongr h x) =
      σ • x := by
  rw [infiniteDecomposition_smul_def]
  have := ringHom_ext_completion w.1
    (f := (infiniteCompletionMap ((σ : Gal(L/K)) : L ≃+* L) w.1).comp
      (infiniteCompletionCongr h).toRingHom)
    ((continuous_infiniteCompletionMap _ _).comp (continuous_infiniteCompletionCongr h))
    (continuous_completionRingHomOf σ.2) fun y ↦ by
      rw [completionRingHomOf_coe]
      change infiniteCompletionMap _ w.1
          (infiniteCompletionCongr h (algebraMap L w.1.Completion y.ofAbs)) =
        algebraMap L w.1.Completion (withAbsMapOf w.1 (σ : Gal(L/K)) y).ofAbs
      rw [infiniteCompletionCongr_algebraMap, infiniteCompletionMap_algebraMap,
        ofAbs_withAbsMapOf]
      rfl
  exact congrFun (congrArg DFunLike.coe this) x

/- English proof (translation)
Establish `hw : w = (σ : Gal(L/K)) • w` using `((mem_stabilizer_iff_smul_placesOver_infinite v w σ).1 σ.2).symm`. Establish `h : w.1 = w.1.comap (((σ : Gal(L/K)) : L ≃+* L) : L →+* L)`. Establish `h'` using `eq_comap_smul_placesOver v (σ : Gal(L/K)) w`. Rewrite `h'` using `[← hw]`. Then use the resulting hypothesis. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[infiniteUnitsAbove_smul_apply_of_eq v (σ : Gal(L/K)) y w w h, infiniteCompletionMap_eq_decomposition_smul]`. Both sides reduce to the same expression.
-/
theorem infiniteUnitsAbove_smul_apply_self (w : v.placesOver L)
    (σ : MulAction.stabilizer Gal(L/K) w.1) (y : (w : v.placesOver L) → (w.1.Completion)ˣ) :
    ((σ : Gal(L/K)) • y) w = σ • y w := by
  have hw : w = (σ : Gal(L/K)) • w :=
    ((mem_stabilizer_iff_smul_placesOver_infinite v w σ).1 σ.2).symm
  have h : w.1 = w.1.comap (((σ : Gal(L/K)) : L ≃+* L) : L →+* L) := by
    have h' := eq_comap_smul_placesOver v (σ : Gal(L/K)) w
    rwa [← hw] at h'
  apply Units.ext
  rw [infiniteUnitsAbove_smul_apply_of_eq v (σ : Gal(L/K)) y w w h,
    infiniteCompletionMap_eq_decomposition_smul]
  rfl

variable [IsGalois K L] [Fintype Gal(L/K)]

/- English proof (translation)
Establish `: IsCyclic Gal(L/K)` using `⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩`. Take `⟨τ, hτ⟩` from `IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w.1)`. Set `_ : Fintype (MulAction.stabilizer Gal(L/K) w.1)` to `Fintype.ofFinite _`. Rewrite using `[cycHerbrand_mulOrbit (U := fun u : v.placesOver L ↦ (u.1.Completion)ˣ) (infiniteUnitsAbove_smul_apply_eq_one v) w _ (mem_stabilizer_iff_smul_placesOver_infinite v w) (infiniteUnitsAbove_smul_apply_self v w) σ hσ τ hτ]`. Conclude with `(cycHerbrand_infiniteCompletion_units v w.1 τ hτ).2`.
-/
theorem cycHerbrand_infiniteUnitsAbove (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (w : v.placesOver L) :
    cycHerbrand (Representation.ofMulDistribMulAction Gal(L/K)
        ((u : v.placesOver L) → (u.1.Completion)ˣ)) σ =
      Module.finrank v.Completion w.1.Completion := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := MulAction.stabilizer Gal(L/K) w.1)
  let _ : Fintype (MulAction.stabilizer Gal(L/K) w.1) := Fintype.ofFinite _
  rw [cycHerbrand_mulOrbit (U := fun u : v.placesOver L ↦ (u.1.Completion)ˣ)
    (infiniteUnitsAbove_smul_apply_eq_one v) w _ (mem_stabilizer_iff_smul_placesOver_infinite v w)
    (infiniteUnitsAbove_smul_apply_self v w) σ hσ τ hτ]
  exact (cycHerbrand_infiniteCompletion_units v w.1 τ hτ).2

end Infinite

end IdeleGroup

end

end GroundTheory.Global
