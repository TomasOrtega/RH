import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

namespace GlobalTheory.IdeleCyl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `show GlobalTheory.AutFunCompare.evW w ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ 1)) = 1`. Rewrite using `[map_one, map_one, map_one]`.
-/
theorem evInf_eInf (w : InfinitePlace F) : evInf F w (eInf F) = 1 := by
  show GlobalTheory.AutFunCompare.evW w ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ 1)) = 1
  rw [map_one, map_one, map_one]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `compInf F E w (eInf F • (l : AE F E) + (1 - eInf F) • 1) = _`. Rewrite using `[map_add, compInf_smul, compInf_smul, evInf_eInf, map_sub, map_one, evInf_eInf, sub_self, zero_smul, one_smul, add_zero]`.
-/
theorem compInf_unitArch (w : InfinitePlace F) (l : (AE F E)ˣ) :
    compInf F E w (unitArch F E l : AE F E) = compInf F E w l := by
  change compInf F E w (eInf F • (l : AE F E) + (1 - eInf F) • 1) = _
  rw [map_add, compInf_smul, compInf_smul, evInf_eInf, map_sub, map_one, evInf_eInf, sub_self, zero_smul, one_smul,
    add_zero]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `compFin F E v (eFin v • (l : AE F E) + (1 - eFin v) • 1) = _`. Rewrite using `[map_add, compFin_smul, compFin_smul, eFin, GlobalTheory.LatVac.evFin_liftV, map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self, zero_smul, one_smul, add_zero]`.
-/
theorem compFin_unitAt (v : Pl F) (l : (AE F E)ˣ) :
    compFin F E v (unitAt E v l : AE F E) = compFin F E v l := by
  change compFin F E v (eFin v • (l : AE F E) + (1 - eFin v) • 1) = _
  rw [map_add, compFin_smul, compFin_smul, eFin, GlobalTheory.LatVac.evFin_liftV, map_sub, map_one, GlobalTheory.LatVac.evFin_liftV,
    sub_self, zero_smul, one_smul, add_zero]

end GlobalTheory.IdeleCyl

namespace GlobalTheory.IdeleCyl

/- English proof (translation)
Set `S : Set ι` to `{i | C i ⊆ A i}`. Establish `hS : (Filter.cofinite : Filter ι) ≤ Filter.principal S` using `Filter.le_principal_iff.2 hCA`. Establish `h1 : IsCompact (((↑) : RestrictedProduct R A (Filter.principal S) → ∀ i, R i) ⁻¹' Set.univ.pi C)`. Use `RestrictedProduct.isEmbedding_coe_of_principal.isCompact_preimage_iff ?_ |>.mpr (isCompact_univ_pi hC)` and prove the remaining obligations. Introduce and unpack `f hf`.

Use `⟨⟨f, Filter.eventually_principal.2 fun i hi => hi (hf i trivial)⟩, rfl⟩` and prove the remaining obligations. Use `h1.image (RestrictedProduct.continuous_inclusion hS) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Conclude with `⟨⟨x, Filter.eventually_principal.2 fun i hi => hi (hx i)⟩, fun i _ => hx i, rfl⟩`. Introduce and unpack `⟨y, hy, rfl⟩ i`. Conclude with `hy i trivial`.
-/
theorem isCompact_restrictedProduct_forall_mem {ι : Type} (R : ι → Type) [∀ i, TopologicalSpace (R i)]
    (A : ∀ i, Set (R i)) (C : ∀ i, Set (R i)) (hC : ∀ i, IsCompact (C i)) (hCA : ∀ᶠ i in Filter.cofinite, C i ⊆ A i) :
    IsCompact {x : RestrictedProduct R A Filter.cofinite | ∀ i, x i ∈ C i} := by
  let S : Set ι := {i | C i ⊆ A i}
  have hS : (Filter.cofinite : Filter ι) ≤ Filter.principal S := Filter.le_principal_iff.2 hCA
  have h1 : IsCompact (((↑) : RestrictedProduct R A (Filter.principal S) → ∀ i, R i) ⁻¹' Set.univ.pi C) := by
    refine RestrictedProduct.isEmbedding_coe_of_principal.isCompact_preimage_iff ?_ |>.mpr (isCompact_univ_pi hC)
    rintro f hf
    refine ⟨⟨f, Filter.eventually_principal.2 fun i hi => hi (hf i trivial)⟩, rfl⟩
  convert h1.image (RestrictedProduct.continuous_inclusion hS) using 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, Filter.eventually_principal.2 fun i hi => hi (hx i)⟩, fun i _ => hx i, rfl⟩
  · rintro ⟨y, hy, rfl⟩ i
    exact hy i trivial

/- English proof (translation)
Simplify using `[Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def, mul_comm]`.
-/
theorem repr_tmul_basis {n : ℕ} {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (b : Module.Basis (Fin n) F E) (a : R) (x : E) (j : Fin n) :
    (Algebra.TensorProduct.basis R b).repr (a ⊗ₜ[F] x) j = a * algebraMap F R (b.repr x j) := by
  simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def, mul_comm]

/- English proof (translation)
Set `b` to `Module.finBasis F E`. Set `β` to `RingOfIntegers.basis E`. Establish `hfin : ∀ᶠ v in Filter.cofinite, ∀ k, algebraMap F (Fv F v) (b.repr (β k : E) j) ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F` using `Filter.eventually_all.2 fun k => (algebraMap F (FiniteAdeleRing (𝓞 F) F) (b.repr (β k : E) j)).2`. Use `hfin.mono fun v hv y hy => ?_` and prove the remaining obligations. Establish `hx : ∀ x : 𝓞 E, algebraMap F (Fv F v) (b.repr (x : E) j) ∈ v.adicCompletionIntegers F`.

Introduce `x`. Establish `e : (x : E) = ∑ k, (β.repr x k : ℤ) • (β k : E)` using `by conv_lhs => rw [← β.sum_repr x]`. Simplify using the standard rewrite rules. Rewrite using `[e, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, map_sum]`. Use `Subring.sum_mem (v.adicCompletionIntegers F).toSubring fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_zsmul, Finsupp.smul_apply, map_zsmul]`. Conclude with `Subring.zsmul_mem (v.adicCompletionIntegers F).toSubring (hv k) _`. Use `intLoc_induction (p := fun y => (Algebra.TensorProduct.basis (Fv F v) b).repr y j ∈ (v.adicCompletionIntegers F : Set (Fv F v))) (fun a ha x => ?_) (by simp) (fun y z hy hz => ?_) (fun y hy => ?_) hy` and prove the remaining obligations. Rewrite using `[repr_tmul_basis]`. Conclude with `mul_mem ha (hx x)`.

Rewrite using `[map_add, Finsupp.add_apply]`. Conclude with `add_mem hy hz`. Rewrite using `[map_neg, Finsupp.neg_apply]`. Conclude with `neg_mem hy`.
-/
theorem eventually_repr_mem_of_mem_intLoc (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Module.Finite F E] (j : Fin (Module.finrank F E)) : ∀ᶠ v in Filter.cofinite, ∀ y ∈ intLoc F E v,
      (Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)).repr y j ∈ (v.adicCompletionIntegers F : Set (Fv F v)) := by
  classical
  let b := Module.finBasis F E
  let β := RingOfIntegers.basis E
  have hfin : ∀ᶠ v in Filter.cofinite, ∀ k, algebraMap F (Fv F v) (b.repr (β k : E) j) ∈ (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => (algebraMap F (FiniteAdeleRing (𝓞 F) F) (b.repr (β k : E) j)).2
  refine hfin.mono fun v hv y hy => ?_
  have hx : ∀ x : 𝓞 E, algebraMap F (Fv F v) (b.repr (x : E) j) ∈ v.adicCompletionIntegers F := by
    intro x
    have e : (x : E) = ∑ k, (β.repr x k : ℤ) • (β k : E) := by
      conv_lhs => rw [← β.sum_repr x]
      simp
    rw [e, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply, map_sum]
    refine Subring.sum_mem (v.adicCompletionIntegers F).toSubring fun k _ => ?_
    rw [map_zsmul, Finsupp.smul_apply, map_zsmul]
    exact Subring.zsmul_mem (v.adicCompletionIntegers F).toSubring (hv k) _
  refine intLoc_induction (p := fun y => (Algebra.TensorProduct.basis (Fv F v) b).repr y j ∈ (v.adicCompletionIntegers F : Set (Fv F v)))
    (fun a ha x => ?_) (by simp) (fun y z hy hz => ?_) (fun y hy => ?_) hy
  · rw [repr_tmul_basis]
    exact mul_mem ha (hx x)
  · rw [map_add, Finsupp.add_apply]; exact add_mem hy hz
  · rw [map_neg, Finsupp.neg_apply]; exact neg_mem hy

end GlobalTheory.IdeleCyl

namespace GlobalTheory.IdeleCyl

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]`. Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`.
-/
theorem repr_map_tens {n : ℕ} {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (b : Module.Basis (Fin n) F E) (φ : R →ₐ[F] R') (z : R ⊗[F] E) (j : Fin n) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) j =
      φ ((Algebra.TensorProduct.basis R b).repr z j) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

end GlobalTheory.IdeleCyl

open GlobalTheory.IdeleCyl in

/- English proof (translation)
Introduce `F E _ _ _ _ _ M L hM hL hLc`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩`. Set `b` to `Module.finBasis F E`. Set `e` to `(Algebra.TensorProduct.basis (AF F) b).equivFun`.

Establish `he : Continuous e.symm` using `IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap`. Set `Mc : Fin (Module.finrank F E) → ∀ w : InfinitePlace F, Set w.Completion` to `fun j w => (fun y => (Algebra.TensorProduct.basis w.Completion b).repr y j) '' M w`. Set `Lc : Fin (Module.finrank F E) → ∀ v : Pl F, Set (Fv F v)` to `fun j v => (fun y => (Algebra.TensorProduct.basis (Fv F v) b).repr y j) '' L v`. Establish `hMc : ∀ j w, IsCompact (Mc j w)` using `fun j w => by haveI : IsModuleTopology w.Completion (w.Completion ⊗[F] E) := ⟨rfl⟩`. Conclude with `(hM w).image (IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis w.Completion b).coord j))`.

Establish `hLc' : ∀ j v, IsCompact (Lc j v)` using `fun j v => by haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩`. Conclude with `(hL v).image (IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis (Fv F v) b).coord j))`. Set `Q : Fin (Module.finrank F E) → Set (AF F)` to `fun j => (Set.univ.pi (Mc j)) ×ˢ {y : FiniteAdeleRing (𝓞 F) F | ∀ v, y v ∈ Lc j v}`. Establish `hQ : ∀ j, IsCompact (Q j)` using `fun j => by`. Use `(isCompact_univ_pi (hMc j)).prod ?_` and prove the remaining obligations.

Use `isCompact_restrictedProduct_forall_mem (fun v : Pl F => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (Lc j) (hLc' j) ((hLc.and (eventually_repr_mem_of_mem_intLoc F E j)).mono fun v ⟨h1, h2⟩ => by` as an intermediate fact. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `h2 y (h1 hy))`. Conclude with `this`. Use `⟨e.symm '' Set.univ.pi Q, (isCompact_univ_pi hQ).image he, fun z hz1 hz2 => ⟨e z, fun j _ => ⟨fun w _ => ?_, fun v => ?_⟩, e.symm_apply_apply z⟩⟩` and prove the remaining obligations.

Use `⟨compInf F E w z, hz1 w, ?_⟩` and prove the remaining obligations. Conclude with `repr_map_tens b (evInf F w) z j`. Use `⟨compFin F E v z, hz2 v, ?_⟩` and prove the remaining obligations. Conclude with `repr_map_tens b (evFin F v) z j`.
-/
theorem GlobalTheory.IdeleCyl.exists_isCompact_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (M : ∀ w : InfinitePlace F, Set (w.Completion ⊗[F] E)) (L : ∀ v : Pl F, Set (Fv F v ⊗[F] E)),
    (∀ w, IsCompact (M w)) → (∀ v, IsCompact (L v)) → (∀ᶠ v in Filter.cofinite, L v ⊆ (intLoc F E v : Set (Fv F v ⊗[F] E))) →
    ∃ K : Set (AE F E), IsCompact K ∧ ∀ z : AE F E, (∀ w, compInf F E w z ∈ M w) → (∀ v, compFin F E v z ∈ L v) → z ∈ K := by
  intro F E _ _ _ _ _ M L hM hL hLc
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  let b := Module.finBasis F E
  let e := (Algebra.TensorProduct.basis (AF F) b).equivFun
  have he : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let Mc : Fin (Module.finrank F E) → ∀ w : InfinitePlace F, Set w.Completion := fun j w =>
    (fun y => (Algebra.TensorProduct.basis w.Completion b).repr y j) '' M w
  let Lc : Fin (Module.finrank F E) → ∀ v : Pl F, Set (Fv F v) := fun j v =>
    (fun y => (Algebra.TensorProduct.basis (Fv F v) b).repr y j) '' L v
  have hMc : ∀ j w, IsCompact (Mc j w) := fun j w => by
    haveI : IsModuleTopology w.Completion (w.Completion ⊗[F] E) := ⟨rfl⟩
    exact (hM w).image (IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis w.Completion b).coord j))
  have hLc' : ∀ j v, IsCompact (Lc j v) := fun j v => by
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    exact (hL v).image (IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis (Fv F v) b).coord j))
  let Q : Fin (Module.finrank F E) → Set (AF F) := fun j =>
    (Set.univ.pi (Mc j)) ×ˢ {y : FiniteAdeleRing (𝓞 F) F | ∀ v, y v ∈ Lc j v}
  have hQ : ∀ j, IsCompact (Q j) := fun j => by
    refine (isCompact_univ_pi (hMc j)).prod ?_
    have := isCompact_restrictedProduct_forall_mem (fun v : Pl F => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (Lc j) (hLc' j) ((hLc.and (eventually_repr_mem_of_mem_intLoc F E j)).mono fun v ⟨h1, h2⟩ => by
        rintro _ ⟨y, hy, rfl⟩
        exact h2 y (h1 hy))
    exact this
  refine ⟨e.symm '' Set.univ.pi Q, (isCompact_univ_pi hQ).image he, fun z hz1 hz2 => ⟨e z, fun j _ => ⟨fun w _ => ?_, fun v => ?_⟩, e.symm_apply_apply z⟩⟩
  · refine ⟨compInf F E w z, hz1 w, ?_⟩
    exact repr_map_tens b (evInf F w) z j
  · refine ⟨compFin F E v z, hz2 v, ?_⟩
    exact repr_map_tens b (evFin F v) z j

namespace GlobalTheory.IdeleCyl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens`. Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `(Units.continuous_val.const_smul ε).add continuous_const`.

Conclude with `(Units.continuous_coe_inv.const_smul ε).add continuous_const`.
-/
theorem continuous_idemUnit (ε : AF F) (hε : ε * ε = ε) : Continuous (idemUnit E ε hε) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.const_smul ε).add continuous_const
  · exact (Units.continuous_coe_inv.const_smul ε).add continuous_const

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Use `haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens`. Use `haveI : T2Space (AE F E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension`. Use `haveI : T2Space (AE F E)ˣ := Units.isEmbedding_embedProduct.t2Space`.

Establish `e : (unitsAt E v : Set (AE F E)ˣ) = Subtype.val '' {l : idelesAt E (evFin F v) | l.1 ∈ unitsAt E v}`. Use extensionality with `l`. Conclude with `⟨fun h => ⟨⟨l, unitsAt_le v h⟩, h, rfl⟩, by rintro ⟨m, hm, rfl⟩; exact hm⟩`. Rewrite using `[e]`. Conclude with `((isCompact_isOpen_unitsAt v).1.image continuous_subtype_val).isClosed`.
-/
theorem isClosed_unitsAt (v : Pl F) : IsClosed (unitsAt E v : Set (AE F E)ˣ) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : T2Space (AE F E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  haveI : T2Space (AE F E)ˣ := Units.isEmbedding_embedProduct.t2Space
  have e : (unitsAt E v : Set (AE F E)ˣ) = Subtype.val '' {l : idelesAt E (evFin F v) | l.1 ∈ unitsAt E v} := by
    ext l
    exact ⟨fun h => ⟨⟨l, unitsAt_le v h⟩, h, rfl⟩, by rintro ⟨m, hm, rfl⟩; exact hm⟩
  rw [e]
  exact ((isCompact_isOpen_unitsAt v).1.image continuous_subtype_val).isClosed

end GlobalTheory.IdeleCyl

open GlobalTheory.IdeleCyl in

/- English proof (translation)
Introduce `F E _ _ _ _ _ S A B hA hB`. Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Use `haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens`. Use `haveI : T2Space (AE F E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension`.

Use `haveI : T2Space (AE F E)ˣ := Units.isEmbedding_embedProduct.t2Space`. Establish `cArch : Continuous (unitArch F E)` using `continuous_idemUnit (E := E) _ _`. Establish `cAt : ∀ v : Pl F, Continuous (unitAt E v)` using `fun v => continuous_idemUnit (E := E) _ _`. Set `M : ∀ w : InfinitePlace F, Set (w.Completion ⊗[F] E)` to `fun w => (fun u : (AE F E)ˣ => (GlobalTheory.Doubling.unitInf F E w u : w.Completion ⊗[F] E)) '' A`. Set `M' : ∀ w : InfinitePlace F, Set (w.Completion ⊗[F] E)` to `fun w => (fun u : (AE F E)ˣ => (GlobalTheory.Doubling.unitInf F E w u⁻¹ : w.Completion ⊗[F] E)) '' A`.

Set `L : ∀ v : Pl F, Set (Fv F v ⊗[F] E)` to `fun v => if v ∈ S then (fun u : (AE F E)ˣ => (unitFin F E v u : Fv F v ⊗[F] E)) '' B v else intLoc F E v`. Set `L' : ∀ v : Pl F, Set (Fv F v ⊗[F] E)` to `fun v => if v ∈ S then (fun u : (AE F E)ˣ => (unitFin F E v u⁻¹ : Fv F v ⊗[F] E)) '' B v else intLoc F E v`. Establish `hM : ∀ w, IsCompact (M w)` using `fun w => hA.image (Units.continuous_val.comp (GlobalTheory.Doubling.continuous_unitInf w))`. Establish `hM' : ∀ w, IsCompact (M' w)` using `fun w => hA.image (Units.continuous_val.comp ((GlobalTheory.Doubling.continuous_unitInf w).comp continuous_inv))`. Establish `hL : ∀ v, IsCompact (L v)` using `fun v => by`.

Distinguish the cases in `hv : v ∈ S`. Simplify using `only [L, if_pos hv]`. Conclude with `(hB v hv).image (Units.continuous_val.comp (GlobalTheory.Doubling.continuous_unitFin v))`. Simplify using `only [L, if_neg hv]`. Conclude with `(isCompact_isOpen_intLoc v).1`.

Establish `hL' : ∀ v, IsCompact (L' v)` using `fun v => by`. Distinguish the cases in `hv : v ∈ S`. Simplify using `only [L', if_pos hv]`. Conclude with `(hB v hv).image (Units.continuous_val.comp ((GlobalTheory.Doubling.continuous_unitFin v).comp continuous_inv))`. Simplify using `only [L', if_neg hv]`.

Conclude with `(isCompact_isOpen_intLoc v).1`. Establish `hfin : ∀ᶠ v in Filter.cofinite, v ∉ S` using `Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => by`. Simplify using `using hv)`. Establish `hLc : ∀ᶠ v in Filter.cofinite, L v ⊆ (intLoc F E v : Set (Fv F v ⊗[F] E))` using `hfin.mono fun v hv => by simp only [L, if_neg hv]; exact subset_rfl`. Establish `hLc' : ∀ᶠ v in Filter.cofinite, L' v ⊆ (intLoc F E v : Set (Fv F v ⊗[F] E))` using `hfin.mono fun v hv => by simp only [L', if_neg hv]; exact subset_rfl`.

Take `⟨K₁, hK₁, h₁⟩` from `GlobalTheory.IdeleCyl.exists_isCompact_box F E M L hM hL hLc`. Take `⟨K₂, hK₂, h₂⟩` from `GlobalTheory.IdeleCyl.exists_isCompact_box F E M' L' hM' hL' hLc'`. Establish `hC : IsClosed {l : (AE F E)ˣ | unitArch F E l ∈ A ∧ (∀ v ∈ S, unitAt E v l ∈ B v) ∧ ∀ v ∉ S, unitAt E v l ∈ unitsAt E v}`. Establish `c1 : IsClosed {l : (AE F E)ˣ | unitArch F E l ∈ A}` using `hA.isClosed.preimage cArch`. Establish `c2 : IsClosed {l : (AE F E)ˣ | ∀ v ∈ S, unitAt E v l ∈ B v}`.

Simplify using `only [Set.setOf_forall]`. Conclude with `isClosed_iInter fun v => isClosed_iInter fun hv => (hB v hv).isClosed.preimage (cAt v)`. Establish `c3 : IsClosed {l : (AE F E)ˣ | ∀ v ∉ S, unitAt E v l ∈ unitsAt E v}`. Simplify using `only [Set.setOf_forall]`. Conclude with `isClosed_iInter fun v => isClosed_iInter fun _ => (isClosed_unitsAt v).preimage (cAt v)`.

Conclude with `c1.inter (c2.inter c3)`. Use `IsCompact.of_isClosed_subset (Units.isClosedEmbedding_embedProduct.isCompact_preimage (hK₁.prod (hK₂.image MulOpposite.continuous_op))) hC ?_` and prove the remaining obligations. Introduce and unpack `l ⟨hl1, hl2, hl3⟩`. Use `⟨h₁ _ (fun w => ⟨unitArch F E l, hl1, ?_⟩) (fun v => ?_), ⟨_, h₂ (l⁻¹ : (AE F E)ˣ) (fun w => ⟨unitArch F E l, hl1, ?_⟩) (fun v => ?_), rfl⟩⟩` and prove the remaining obligations. Conclude with `compInf_unitArch w l`.

Distinguish the cases in `hv : v ∈ S`. Simplify using `only [L, if_pos hv]`. Conclude with `⟨unitAt E v l, hl2 v hv, compFin_unitAt v l⟩`. Simplify using `only [L, if_neg hv]`. Express the relevant statement in the definitionally equal form `compFin F E v (l : AE F E) ∈ (intLoc F E v : Set (Fv F v ⊗[F] E))`.

Rewrite using `[← compFin_unitAt v l]`. Conclude with `(mem_unitsAt.1 (hl3 v hv)).2.1`. Use `show compInf F E w ((unitArch F E l)⁻¹ : (AE F E)ˣ) = compInf F E w ((l⁻¹ : (AE F E)ˣ) : AE F E)`. Rewrite using `[← map_inv]`. Conclude with `compInf_unitArch w l⁻¹`.

Distinguish the cases in `hv : v ∈ S`. Simplify using `only [L', if_pos hv]`. Use `⟨unitAt E v l, hl2 v hv, ?_⟩` and prove the remaining obligations. Use `show compFin F E v ((unitAt E v l)⁻¹ : (AE F E)ˣ) = _`. Rewrite using `[← map_inv]`.

Conclude with `compFin_unitAt v l⁻¹`. Simplify using `only [L', if_neg hv]`. Express the relevant statement in the definitionally equal form `compFin F E v ((l⁻¹ : (AE F E)ˣ) : AE F E) ∈ (intLoc F E v : Set (Fv F v ⊗[F] E))`. Rewrite using `[← compFin_unitAt v l⁻¹, map_inv]`. Conclude with `(mem_unitsAt.1 (hl3 v hv)).2.2`.
-/
theorem GlobalTheory.IdeleCyl.isCompact_cyl : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (S : Finset (Pl F)) (A : Set (AE F E)ˣ) (B : Pl F → Set (AE F E)ˣ), IsCompact A → (∀ v ∈ S, IsCompact (B v)) →
    IsCompact {l : (AE F E)ˣ | unitArch F E l ∈ A ∧ (∀ v ∈ S, unitAt E v l ∈ B v) ∧ ∀ v ∉ S, unitAt E v l ∈ unitsAt E v} := by
  intro F E _ _ _ _ _ S A B hA hB
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : T2Space (AE F E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  haveI : T2Space (AE F E)ˣ := Units.isEmbedding_embedProduct.t2Space
  have cArch : Continuous (unitArch F E) := continuous_idemUnit (E := E) _ _
  have cAt : ∀ v : Pl F, Continuous (unitAt E v) := fun v => continuous_idemUnit (E := E) _ _

  let M : ∀ w : InfinitePlace F, Set (w.Completion ⊗[F] E) := fun w =>
    (fun u : (AE F E)ˣ => (GlobalTheory.Doubling.unitInf F E w u : w.Completion ⊗[F] E)) '' A
  let M' : ∀ w : InfinitePlace F, Set (w.Completion ⊗[F] E) := fun w =>
    (fun u : (AE F E)ˣ => (GlobalTheory.Doubling.unitInf F E w u⁻¹ : w.Completion ⊗[F] E)) '' A
  let L : ∀ v : Pl F, Set (Fv F v ⊗[F] E) := fun v =>
    if v ∈ S then (fun u : (AE F E)ˣ => (unitFin F E v u : Fv F v ⊗[F] E)) '' B v else intLoc F E v
  let L' : ∀ v : Pl F, Set (Fv F v ⊗[F] E) := fun v =>
    if v ∈ S then (fun u : (AE F E)ˣ => (unitFin F E v u⁻¹ : Fv F v ⊗[F] E)) '' B v else intLoc F E v
  have hM : ∀ w, IsCompact (M w) := fun w =>
    hA.image (Units.continuous_val.comp (GlobalTheory.Doubling.continuous_unitInf w))
  have hM' : ∀ w, IsCompact (M' w) := fun w =>
    hA.image (Units.continuous_val.comp ((GlobalTheory.Doubling.continuous_unitInf w).comp continuous_inv))
  have hL : ∀ v, IsCompact (L v) := fun v => by
    by_cases hv : v ∈ S
    · simp only [L, if_pos hv]
      exact (hB v hv).image (Units.continuous_val.comp (GlobalTheory.Doubling.continuous_unitFin v))
    · simp only [L, if_neg hv]
      exact (isCompact_isOpen_intLoc v).1
  have hL' : ∀ v, IsCompact (L' v) := fun v => by
    by_cases hv : v ∈ S
    · simp only [L', if_pos hv]
      exact (hB v hv).image (Units.continuous_val.comp ((GlobalTheory.Doubling.continuous_unitFin v).comp continuous_inv))
    · simp only [L', if_neg hv]
      exact (isCompact_isOpen_intLoc v).1
  have hfin : ∀ᶠ v in Filter.cofinite, v ∉ S := Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => by
    simpa using hv)
  have hLc : ∀ᶠ v in Filter.cofinite, L v ⊆ (intLoc F E v : Set (Fv F v ⊗[F] E)) :=
    hfin.mono fun v hv => by simp only [L, if_neg hv]; exact subset_rfl
  have hLc' : ∀ᶠ v in Filter.cofinite, L' v ⊆ (intLoc F E v : Set (Fv F v ⊗[F] E)) :=
    hfin.mono fun v hv => by simp only [L', if_neg hv]; exact subset_rfl
  obtain ⟨K₁, hK₁, h₁⟩ := GlobalTheory.IdeleCyl.exists_isCompact_box F E M L hM hL hLc
  obtain ⟨K₂, hK₂, h₂⟩ := GlobalTheory.IdeleCyl.exists_isCompact_box F E M' L' hM' hL' hLc'

  have hC : IsClosed {l : (AE F E)ˣ | unitArch F E l ∈ A ∧ (∀ v ∈ S, unitAt E v l ∈ B v) ∧
      ∀ v ∉ S, unitAt E v l ∈ unitsAt E v} := by
    have c1 : IsClosed {l : (AE F E)ˣ | unitArch F E l ∈ A} := hA.isClosed.preimage cArch
    have c2 : IsClosed {l : (AE F E)ˣ | ∀ v ∈ S, unitAt E v l ∈ B v} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun v => isClosed_iInter fun hv => (hB v hv).isClosed.preimage (cAt v)
    have c3 : IsClosed {l : (AE F E)ˣ | ∀ v ∉ S, unitAt E v l ∈ unitsAt E v} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun v => isClosed_iInter fun _ => (isClosed_unitsAt v).preimage (cAt v)
    exact c1.inter (c2.inter c3)
  refine IsCompact.of_isClosed_subset (Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hK₁.prod (hK₂.image MulOpposite.continuous_op))) hC ?_
  rintro l ⟨hl1, hl2, hl3⟩
  refine ⟨h₁ _ (fun w => ⟨unitArch F E l, hl1, ?_⟩) (fun v => ?_), ⟨_, h₂ (l⁻¹ : (AE F E)ˣ) (fun w => ⟨unitArch F E l, hl1, ?_⟩) (fun v => ?_), rfl⟩⟩
  · exact compInf_unitArch w l
  · by_cases hv : v ∈ S
    · simp only [L, if_pos hv]
      exact ⟨unitAt E v l, hl2 v hv, compFin_unitAt v l⟩
    · simp only [L, if_neg hv]
      change compFin F E v (l : AE F E) ∈ (intLoc F E v : Set (Fv F v ⊗[F] E))
      rw [← compFin_unitAt v l]
      exact (mem_unitsAt.1 (hl3 v hv)).2.1
  · show compInf F E w ((unitArch F E l)⁻¹ : (AE F E)ˣ) = compInf F E w ((l⁻¹ : (AE F E)ˣ) : AE F E)
    rw [← map_inv]
    exact compInf_unitArch w l⁻¹
  · by_cases hv : v ∈ S
    · simp only [L', if_pos hv]
      refine ⟨unitAt E v l, hl2 v hv, ?_⟩
      show compFin F E v ((unitAt E v l)⁻¹ : (AE F E)ˣ) = _
      rw [← map_inv]
      exact compFin_unitAt v l⁻¹
    · simp only [L', if_neg hv]
      change compFin F E v ((l⁻¹ : (AE F E)ˣ) : AE F E) ∈ (intLoc F E v : Set (Fv F v ⊗[F] E))
      rw [← compFin_unitAt v l⁻¹, map_inv]
      exact (mem_unitsAt.1 (hl3 v hv)).2.2
