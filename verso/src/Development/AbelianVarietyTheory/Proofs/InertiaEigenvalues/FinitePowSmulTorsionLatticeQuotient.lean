import Mathlib
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LatTorsFinite

/- English proof (translation)
Establish `hU : ∀ x : O, IsOpen ((fun y => y - x) ⁻¹' (I : Set O))` using `fun x => hI.preimage (continuous_id.sub continuous_const)`. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover (fun x : O => (fun y => y - x) ⁻¹' (I : Set O)) hU (fun y _ => Set.mem_iUnion.2 ⟨y, by simp [I.zero_mem]⟩)`. Use `Finite.of_surjective (fun x : t => Ideal.Quotient.mk I (x : O)) ?_` and prove the remaining obligations. Introduce `q`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective q`.

Take `⟨x, hx, hyx⟩` from `Set.mem_iUnion₂.1 (ht (Set.mem_univ y))`. Use `⟨⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Conclude with `(Ideal.Quotient.eq.2 hyx).symm`.
-/
theorem finite_quot_of_isOpen {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] (I : Ideal O) (hI : IsOpen (I : Set O)) : Finite (O ⧸ I) := by
  have hU : ∀ x : O, IsOpen ((fun y => y - x) ⁻¹' (I : Set O)) := fun x =>
    hI.preimage (continuous_id.sub continuous_const)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : O => (fun y => y - x) ⁻¹' (I : Set O))
    hU (fun y _ => Set.mem_iUnion.2 ⟨y, by simp [I.zero_mem]⟩)
  refine Finite.of_surjective (fun x : t => Ideal.Quotient.mk I (x : O)) ?_
  intro q
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  refine ⟨⟨x, hx⟩, ?_⟩
  exact (Ideal.Quotient.eq.2 hyx).symm

/- English proof (translation)
Establish `hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}` using `hϖ.maximalIdeal_eq`. Establish `hopen : IsOpen (((IsLocalRing.maximalIdeal O) ^ n : Ideal O) : Set O)` using `(isAdic_iff.1 hA).1 n`. Rewrite `hopen` using `[hm, Ideal.span_singleton_pow]`. Conclude with `finite_quot_of_isOpen _ hopen`.
-/
theorem finite_quot_pow {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] (hO : IsTopologicalRing O) (hc : CompactSpace O)
    (hA : IsAdic (IsLocalRing.maximalIdeal O)) {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    Finite (O ⧸ Ideal.span {ϖ ^ n}) := by
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hopen : IsOpen (((IsLocalRing.maximalIdeal O) ^ n : Ideal O) : Set O) :=
    (isAdic_iff.1 hA).1 n
  rw [hm, Ideal.span_singleton_pow] at hopen
  exact finite_quot_of_isOpen _ hopen

/- English proof (translation)
Use `haveI := finite_quot_pow hO hc hA hϖ n`. Use `haveI : Module.Finite O T := Module.Finite.iff_fg.2 hT.1`. Use `haveI : Module.Finite (O ⧸ Ideal.span {ϖ ^ n}) (T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O T)) := Module.Finite.of_restrictScalars_finite O _ _`. Use `haveI : Finite (T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O T)) := Module.finite_of_finite (O ⧸ Ideal.span {ϖ ^ n})`. Set `rep : V ⧸ T → V` to `fun q => Classical.choose (Submodule.Quotient.mk_surjective T q)`.

Establish `hrep : ∀ q, Submodule.Quotient.mk (p` using `T) (rep q) = q := fun q => Classical.choose_spec (Submodule.Quotient.mk_surjective T q)`. Establish `hmem : ∀ x : LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n)), ϖ ^ n • rep (x : V ⧸ T) ∈ T`. Introduce `x`. Establish `hx : (ϖ ^ n) • (x : V ⧸ T) = 0` using `x.2`. Rewrite `hx` using `[← hrep (x : V ⧸ T), ← Submodule.Quotient.mk_smul]`.

Conclude with `(Submodule.Quotient.mk_eq_zero T).1 hx`. Establish `hinj : ∀ v w : V, ϖ ^ n • v = ϖ ^ n • w → v = w`. Introduce `v w h`. Establish `h0 : algebraMap O (FractionRing O) (ϖ ^ n) ≠ 0`. Rewrite using `[Ne, IsFractionRing.to_map_eq_zero_iff]`.

Conclude with `pow_ne_zero _ hϖ.ne_zero`. Rewrite `h` using `[← algebraMap_smul (FractionRing O) (ϖ ^ n) v, ← algebraMap_smul (FractionRing O) (ϖ ^ n) w]`. Conclude with `smul_right_injective V h0 h`. Set `f : LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n)) → T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O T)` to `fun x => Submodule.Quotient.mk ⟨ϖ ^ n • rep (x : V ⧸ T), hmem x⟩`. Use `Finite.of_injective f ?_` and prove the remaining obligations.

Introduce `x y hxy`. Rewrite `hxy` using `[Submodule.Quotient.eq, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Take `⟨t, -, ht⟩` from `hxy`. Establish `ht' : ϖ ^ n • (t : V) = ϖ ^ n • (rep (x : V ⧸ T) - rep (y : V ⧸ T))`. Rewrite using `[smul_sub]`.

Conclude with `congrArg Subtype.val ht`. Establish `hd` using `hinj _ _ ht'`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hrep (x : V ⧸ T), ← hrep (y : V ⧸ T), Submodule.Quotient.eq, ← hd]`. Conclude with `t.2`.
-/
theorem finite_ker_pow_smul {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] (T : Submodule O V) (hO : IsTopologicalRing O)
    (hc : CompactSpace O) (hA : IsAdic (IsLocalRing.maximalIdeal O)) (hT : IsLatticeIn T)
    (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) :
    Finite ↥(LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n))) := by
  haveI := finite_quot_pow hO hc hA hϖ n
  haveI : Module.Finite O T := Module.Finite.iff_fg.2 hT.1
  haveI : Module.Finite (O ⧸ Ideal.span {ϖ ^ n})
      (T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O T)) :=
    Module.Finite.of_restrictScalars_finite O _ _
  haveI : Finite (T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O T)) :=
    Module.finite_of_finite (O ⧸ Ideal.span {ϖ ^ n})

  let rep : V ⧸ T → V := fun q => Classical.choose (Submodule.Quotient.mk_surjective T q)
  have hrep : ∀ q, Submodule.Quotient.mk (p := T) (rep q) = q := fun q =>
    Classical.choose_spec (Submodule.Quotient.mk_surjective T q)
  have hmem : ∀ x : LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n)),
      ϖ ^ n • rep (x : V ⧸ T) ∈ T := by
    intro x
    have hx : (ϖ ^ n) • (x : V ⧸ T) = 0 := x.2
    rw [← hrep (x : V ⧸ T), ← Submodule.Quotient.mk_smul] at hx
    exact (Submodule.Quotient.mk_eq_zero T).1 hx

  have hinj : ∀ v w : V, ϖ ^ n • v = ϖ ^ n • w → v = w := by
    intro v w h
    have h0 : algebraMap O (FractionRing O) (ϖ ^ n) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact pow_ne_zero _ hϖ.ne_zero
    rw [← algebraMap_smul (FractionRing O) (ϖ ^ n) v,
      ← algebraMap_smul (FractionRing O) (ϖ ^ n) w] at h
    exact smul_right_injective V h0 h
  let f : LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n)) →
      T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O T) :=
    fun x => Submodule.Quotient.mk ⟨ϖ ^ n • rep (x : V ⧸ T), hmem x⟩
  refine Finite.of_injective f ?_
  intro x y hxy
  rw [Submodule.Quotient.eq, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hxy
  obtain ⟨t, -, ht⟩ := hxy
  have ht' : ϖ ^ n • (t : V) = ϖ ^ n • (rep (x : V ⧸ T) - rep (y : V ⧸ T)) := by
    rw [smul_sub]
    exact congrArg Subtype.val ht
  have hd := hinj _ _ ht'
  apply Subtype.ext
  rw [← hrep (x : V ⧸ T), ← hrep (y : V ⧸ T), Submodule.Quotient.eq, ← hd]
  exact t.2

end GlobalTheory.LatTorsFinite
