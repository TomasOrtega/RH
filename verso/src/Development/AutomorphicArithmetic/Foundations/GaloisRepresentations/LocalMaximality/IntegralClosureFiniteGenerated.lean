import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryChartHodgeMatrix

set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

open scoped IntermediateField.algebraAdjoinAdjoin in

/- English proof (translation)
Use `pd.indep.isTranscendenceBasis_iff_isAlgebraic.mpr ⟨fun a => ?_⟩` and prove the remaining obligations. Use `(IsFractionRing.isAlgebraic_iff (Algebra.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0)) (IntermediateField.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0)) F).mpr ?_` and prove the remaining obligations. Establish `ha : a ∈ IntermediateField.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0)`. Rewrite using `[pd.gen]`. Discharge the goal by the elementary cases of `trivial`.

Conclude with `isAlgebraic_algebraMap (⟨a, ha⟩ : IntermediateField.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0))`.
-/
private theorem tb_F {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} {x : Fin (d + 1) → F} (pd : IsPd ℂ x) :
    IsTranscendenceBasis ℂ (fun j : Fin d => x j.succ / x 0) := by
  refine pd.indep.isTranscendenceBasis_iff_isAlgebraic.mpr ⟨fun a => ?_⟩
  refine (IsFractionRing.isAlgebraic_iff (Algebra.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0))
    (IntermediateField.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0)) F).mpr ?_
  have ha : a ∈ IntermediateField.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0) := by
    rw [pd.gen]; trivial
  exact isAlgebraic_algebraMap (⟨a, ha⟩ : IntermediateField.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0))

/- English proof (translation)
Establish `hF` using `tb_F pd`. Use `set t : Fin d → F := fun j => x j.succ / x 0 with ht`. Establish `hL : IsTranscendenceBasis ℂ (algebraMap F L ∘ t)` using `hF.algebraMap_comp`. Establish `hK : IsTranscendenceBasis ℂ (algebraMap F K ∘ t)` using `hF.algebraMap_comp`. Use `letI : Algebra K L := j2.toRingHom.toAlgebra`.

Use `haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm`. Establish `hw : AlgebraicIndependent ℂ (algebraMap K L ∘ (algebraMap F K ∘ t))` using `hK.1.map' (f := IsScalarTower.toAlgHom ℂ K L) (algebraMap K L).injective`. Establish `hwb : IsTranscendenceBasis ℂ (algebraMap K L ∘ (algebraMap F K ∘ t))` using `hw.isTranscendenceBasis_of_trdeg_le_of_finite (by rw [← hL.cardinalMk_eq_trdeg])`. Establish `halg : Algebra.IsAlgebraic K L` using `hwb.isAlgebraic_iff.2 fun i => isAlgebraic_algebraMap _`. Take `⟨s, hs⟩` from `(Module.finite_def (R := F) (M := L)).1 inferInstance`.

Set `S : Set L` to `(s : Set L) ∪ Set.range (algebraMap F L ∘ t)`. Establish `hSfin : S.Finite` using `s.finite_toSet.union (Set.finite_range _)`. Use `haveI : Finite S := hSfin`. Establish `htop : IntermediateField.adjoin K S = ⊤`. Rewrite using `[eq_top_iff]`.

Introduce and unpack `y -`. Set `P : IntermediateField ℂ L` to `(IntermediateField.adjoin K S).restrictScalars ℂ`. Establish `hP : ∀ f : F, algebraMap F L f ∈ P`. Establish `hle : IntermediateField.adjoin ℂ (Set.range t) ≤ P.comap (IsScalarTower.toAlgHom ℂ F L)`. Rewrite using `[IntermediateField.adjoin_le_iff]`.

Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `IntermediateField.subset_adjoin K S (Or.inr ⟨j, rfl⟩)`. Rewrite `hle` using `[pd.gen]`. Conclude with `fun f => hle (IntermediateField.mem_top)`. Establish `hy : y ∈ Submodule.span F (s : Set L)` using `by rw [hs]; trivial`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz => exact IntermediateField.subset_adjoin K S (Or.inl hz)`. Consider the case `zero => exact zero_mem _`. Consider the case `add a c _ _ ha hc => exact add_mem ha hc`. Consider the case `smul r a _ ha`.

Rewrite using `[Algebra.smul_def]`. Conclude with `mul_mem (hP r) ha`. Use `haveI : FiniteDimensional K (IntermediateField.adjoin K S) := IntermediateField.finiteDimensional_adjoin fun z _ => (halg.isAlgebraic z).isIntegral`. Rewrite `this` using `[htop]`. Express the relevant statement in the definitionally equal form `Module.Finite K L`.

Conclude with `(IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv.finiteDimensional`.
-/
private theorem algHom_finite_of_proper {F K L : Type} [Field F] [Field K] [Field L] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ L]
    [Algebra F K] [IsScalarTower ℂ F K] [Algebra F L] [IsScalarTower ℂ F L] {d : ℕ} {x : Fin (d + 1) → F}
    (pd : IsPd ℂ x) [FiniteDimensional F K] [FiniteDimensional F L] (j2 : K →ₐ[ℂ] L) :
    j2.toRingHom.Finite := by
  have hF := tb_F pd
  set t : Fin d → F := fun j => x j.succ / x 0 with ht
  have hL : IsTranscendenceBasis ℂ (algebraMap F L ∘ t) := hF.algebraMap_comp
  have hK : IsTranscendenceBasis ℂ (algebraMap F K ∘ t) := hF.algebraMap_comp
  letI : Algebra K L := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  have hw : AlgebraicIndependent ℂ (algebraMap K L ∘ (algebraMap F K ∘ t)) :=
    hK.1.map' (f := IsScalarTower.toAlgHom ℂ K L) (algebraMap K L).injective
  have hwb : IsTranscendenceBasis ℂ (algebraMap K L ∘ (algebraMap F K ∘ t)) :=
    hw.isTranscendenceBasis_of_trdeg_le_of_finite (by rw [← hL.cardinalMk_eq_trdeg])
  have halg : Algebra.IsAlgebraic K L := hwb.isAlgebraic_iff.2 fun i => isAlgebraic_algebraMap _
  obtain ⟨s, hs⟩ := (Module.finite_def (R := F) (M := L)).1 inferInstance
  let S : Set L := (s : Set L) ∪ Set.range (algebraMap F L ∘ t)
  have hSfin : S.Finite := s.finite_toSet.union (Set.finite_range _)
  haveI : Finite S := hSfin
  have htop : IntermediateField.adjoin K S = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    let P : IntermediateField ℂ L := (IntermediateField.adjoin K S).restrictScalars ℂ
    have hP : ∀ f : F, algebraMap F L f ∈ P := by
      have hle : IntermediateField.adjoin ℂ (Set.range t) ≤ P.comap (IsScalarTower.toAlgHom ℂ F L) := by
        rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨j, rfl⟩
        exact IntermediateField.subset_adjoin K S (Or.inr ⟨j, rfl⟩)
      rw [pd.gen] at hle
      exact fun f => hle (IntermediateField.mem_top)
    have hy : y ∈ Submodule.span F (s : Set L) := by rw [hs]; trivial
    induction hy using Submodule.span_induction with
    | mem z hz => exact IntermediateField.subset_adjoin K S (Or.inl hz)
    | zero => exact zero_mem _
    | add a c _ _ ha hc => exact add_mem ha hc
    | smul r a _ ha =>
      rw [Algebra.smul_def]
      exact mul_mem (hP r) ha
  haveI : FiniteDimensional K (IntermediateField.adjoin K S) :=
    IntermediateField.finiteDimensional_adjoin fun z _ => (halg.isAlgebraic z).isIntegral
  rw [htop] at this
  change Module.Finite K L
  exact (IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv.finiteDimensional

/- English proof (translation)
Break down `J.eq_empty_or_nonempty with rfl | ⟨i, hi⟩` into its components or cases. Establish `hbot : rB ℂ L x ∅ = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `y hy`. Use `haveI : Algebra.IsIntegral ℂ (rA ℂ x ∅) := Algebra.IsIntegral.adjoin (by simp)`.

Establish `h : IsIntegral ℂ y` using `isIntegral_trans (A := rA ℂ x ∅) y hy`. Use `minpoly.mem_range_of_degree_eq_one ℂ y (IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible h))` as an intermediate fact. Conclude with `Algebra.mem_bot.2 this`. Rewrite using `[hbot]`. Conclude with `Subalgebra.fg_bot`.

Use `haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℂ F).injective haveI : IsFractionRing (rA ℂ x J) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing ℂ F d x pd J ⟨i, hi⟩).1 haveI : IsNoetherianRing (rA ℂ x J) := (GlobalTheory.T.stand …`. Establish `hfg : (rA ℂ x J).FG`. Use `Subalgebra.fg_def.2 ⟨_, ?_, rfl⟩` and prove the remaining obligations. Use `((J.finite_toSet.prod (Set.finite_univ (α := Fin (d + 1)))).image fun p => x p.2 / x p.1).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i', hi', j, rfl⟩`.

Conclude with `⟨(i', j), ⟨hi', trivial⟩, rfl⟩`. Use `haveI : Algebra.FiniteType ℂ (rA ℂ x J) := (Subalgebra.fg_iff_finiteType _).1 hfg`. Establish `hft : Algebra.FiniteType ℂ (integralClosure (rA ℂ x J) L)` using `Algebra.FiniteType.trans (S := rA ℂ x J) inferInstance inferInstance`. Conclude with `(Subalgebra.fg_iff_finiteType (rB ℂ L x J)).2 hft`.
-/
private theorem fg_rB {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L]
    [IsScalarTower ℂ F L] {d : ℕ} {x : Fin (d + 1) → F} (pd : IsPd ℂ x) [FiniteDimensional F L]
    (J : Finset (Fin (d + 1))) : (rB ℂ L x J).FG := by
  rcases J.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · have hbot : rB ℂ L x ∅ = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      haveI : Algebra.IsIntegral ℂ (rA ℂ x ∅) := Algebra.IsIntegral.adjoin (by simp)
      have h : IsIntegral ℂ y := isIntegral_trans (A := rA ℂ x ∅) y hy
      have := minpoly.mem_range_of_degree_eq_one ℂ y
        (IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible h))
      exact Algebra.mem_bot.2 this
    rw [hbot]
    exact Subalgebra.fg_bot
  · haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℂ F).injective
    haveI : IsFractionRing (rA ℂ x J) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing ℂ F d x pd J ⟨i, hi⟩).1
    haveI : IsNoetherianRing (rA ℂ x J) := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing ℂ F d x pd J ⟨i, hi⟩).2
    haveI := rA_isIntegrallyClosed pd hi
    haveI : Module.Finite (rA ℂ x J) (integralClosure (rA ℂ x J) L) :=
      IsIntegralClosure.finite (rA ℂ x J) F L (integralClosure (rA ℂ x J) L)
    have hfg : (rA ℂ x J).FG := by
      refine Subalgebra.fg_def.2 ⟨_, ?_, rfl⟩
      refine ((J.finite_toSet.prod (Set.finite_univ (α := Fin (d + 1)))).image
        fun p => x p.2 / x p.1).subset ?_
      rintro _ ⟨i', hi', j, rfl⟩
      exact ⟨(i', j), ⟨hi', trivial⟩, rfl⟩
    haveI : Algebra.FiniteType ℂ (rA ℂ x J) := (Subalgebra.fg_iff_finiteType _).1 hfg
    have hft : Algebra.FiniteType ℂ (integralClosure (rA ℂ x J) L) :=
      Algebra.FiniteType.trans (S := rA ℂ x J) inferInstance inferInstance
    exact (Subalgebra.fg_iff_finiteType (rB ℂ L x J)).2 hft

/- English proof (translation)
Use `letI : Algebra K L := j2.toRingHom.toAlgebra`. Use `letI : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra`. Use `haveI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm`. Use `haveI : IsScalarTower ℂ F L := IsScalarTower.of_algebraMap_eq fun c => by`.

Express the relevant statement in the definitionally equal form `algebraMap ℂ L c = algebraMap K L (algebraMap F K (algebraMap ℂ F c))`. Rewrite using `[← IsScalarTower.algebraMap_apply ℂ F K c]`. Conclude with `(j2.commutes c).symm`. Use `haveI : Module.Finite K L := hf`. Use `haveI : FiniteDimensional F L := Module.Finite.trans K L`.

Set `A` to `rA ℂ x J`. Set `B` to `(rB ℂ K x J).map j2`. Set `φ : A →+* B` to `{ toFun := fun a => ⟨algebraMap K L (algebraMap F K a), Subalgebra.mem_map.2 ⟨algebraMap F K a, (integralClosure A K).algebraMap_mem a, rfl⟩⟩ map_one' := Subtype.ext (by simp) map_mul' := fun a b => Subtype.ext (by simp) map_zero' := Subtype.ext (by simp) map_add' := fun a b => S …`. Use `letI : Algebra A B := φ.toAlgebra`. Use `haveI : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun _ => rfl`.

Use `haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : Algebra.IsIntegral A B := ⟨fun b => by`. Take `⟨c, hc, hb⟩` from `Subalgebra.mem_map.1 b.2`. Establish `h1 : IsIntegral A (algebraMap K L c)` using `IsIntegral.algebraMap hc`. Establish `h2 : algebraMap B L b = algebraMap K L c` using `hb.symm`.

Rewrite `h1` using `[← h2]`. Conclude with `(isIntegral_algebraMap_iff (Subtype.val_injective : Function.Injective (algebraMap B L))).1 h1⟩`. Establish `e : R2 x j2 J = rB ℂ L x J`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Conclude with `isIntegral_trans (A := B) y hy`. Introduce `hy`. Conclude with `IsIntegral.tower_top (A := B) hy`. Rewrite using `[e]`.

Conclude with `fg_rB pd J`.
-/
private theorem integralClosure_finiteGenerated {F K L : Type} [Field F] [Field K] [Field L] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ L]
    [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ} {x : Fin (d + 1) → F} (pd : IsPd ℂ x) [FiniteDimensional F K]
    (j2 : K →ₐ[ℂ] L) (hf : j2.toRingHom.Finite) (J : Finset (Fin (d + 1))) : (R2 x j2 J).FG := by
  letI : Algebra K L := j2.toRingHom.toAlgebra
  letI : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  haveI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  haveI : IsScalarTower ℂ F L := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap ℂ L c = algebraMap K L (algebraMap F K (algebraMap ℂ F c))
    rw [← IsScalarTower.algebraMap_apply ℂ F K c]
    exact (j2.commutes c).symm
  haveI : Module.Finite K L := hf
  haveI : FiniteDimensional F L := Module.Finite.trans K L
  let A := rA ℂ x J
  let B := (rB ℂ K x J).map j2
  let φ : A →+* B :=
    { toFun := fun a => ⟨algebraMap K L (algebraMap F K a),
        Subalgebra.mem_map.2 ⟨algebraMap F K a, (integralClosure A K).algebraMap_mem a, rfl⟩⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  letI : Algebra A B := φ.toAlgebra
  haveI : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral A B := ⟨fun b => by
    obtain ⟨c, hc, hb⟩ := Subalgebra.mem_map.1 b.2
    have h1 : IsIntegral A (algebraMap K L c) := IsIntegral.algebraMap hc
    have h2 : algebraMap B L b = algebraMap K L c := hb.symm
    rw [← h2] at h1
    exact (isIntegral_algebraMap_iff (Subtype.val_injective : Function.Injective (algebraMap B L))).1 h1⟩
  have e : R2 x j2 J = rB ℂ L x J := by
    ext y
    constructor
    · intro hy
      exact isIntegral_trans (A := B) y hy
    · intro hy
      exact IsIntegral.tower_top (A := B) hy
  rw [e]
  exact fg_rB pd J

/- English proof (translation)
Introduce `F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 h I J hI`. Establish `pd` using `h.covZ.pd`. Use `haveI := h.covZ.fin`. Use `haveI := h.covY.fin`. Establish `h1 : (rB ℂ K' (xv x) I).FG` using `fg_rB h.covY.pd I`.

Establish `h2 : (R2 (xv x) j2 J).FG` using `integralClosure_finiteGenerated pd j2 (algHom_finite_of_proper pd j2) J`. Conclude with `(Subalgebra.fg_iff_finiteType _).1 (h1.sup h2)`.
-/
theorem rYFT_of :
    RYFT := by
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 h I J hI
  have pd := h.covZ.pd
  haveI := h.covZ.fin
  haveI := h.covY.fin
  have h1 : (rB ℂ K' (xv x) I).FG := fg_rB h.covY.pd I
  have h2 : (R2 (xv x) j2 J).FG := integralClosure_finiteGenerated pd j2 (algHom_finite_of_proper pd j2) J
  exact (Subalgebra.fg_iff_finiteType _).1 (h1.sup h2)

end UpperTheory.Gal.productCup_of_system

end
