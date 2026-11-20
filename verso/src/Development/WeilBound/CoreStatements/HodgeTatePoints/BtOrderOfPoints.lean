import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import ReciprocityTheory.DualLattices.TensorSpan

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace PositivityTheory.HtPt.Mk

/- English proof (translation)
Introduce `R C _ _ _ _ _ hinj N _ _ _ A hA`. Set `φ : (Multiplicative N → R) →ₗ[R] (N → C)` to `{ toFun := fun g x => algebraMap R C (g (Multiplicative.ofAdd x)) map_add' := by`. Introduce `g h`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules.

Use the proof step `map_smul' := by`. Introduce `r g`. Use function extensionality and compare the values at `x`. Simplify using `[Algebra.smul_def] }`. Establish `hφ : ∀ g x, φ g x = algebraMap R C (g (Multiplicative.ofAdd x))` using `fun _ _ => rfl`.

Use `haveI := hA.finite`. Use `haveI := hA.projective`. Use `haveI : Module.Free R A := Module.free_of_flat_of_isLocalRing`. Take `⟨d, hd0, hd⟩` from `hA.full`. Establish `hcardT : Module.finrank R (Multiplicative N → R) = Fintype.card N`.

Rewrite using `[Module.finrank_fintype_fun_eq_card]`. Conclude with `Fintype.card_congr Multiplicative.toAdd`. Establish `hrank : Module.finrank R A = Fintype.card N`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← hcardT]`.

Conclude with `LinearMap.finrank_le_finrank_of_injective (f := A.val.toLinearMap) Subtype.val_injective`. Set `sc : (Multiplicative N → R) →ₗ[R] A` to `{ toFun := fun f => ⟨d • f, hd f⟩ map_add' := fun f g => Subtype.ext (smul_add d f g) map_smul' := fun r f => Subtype.ext (smul_comm d r f) }`. Establish `hsc : Function.Injective sc`. Introduce `f g hfg`. Establish `h2 : d • f = d • g` using `congrArg Subtype.val hfg`.

Conclude with `smul_right_injective _ hd0 h2`. Rewrite using `[← hcardT]`. Conclude with `LinearMap.finrank_le_finrank_of_injective hsc`. Set `b : Module.Basis N R A` to `(Module.finBasisOfFinrankEq R A hrank).reindex (Fintype.equivFin N).symm`. Use `⟨{ carrier := (Subalgebra.toSubmodule A).map φ lat := ?_ le_int := ?_ one_mem := ?_ mul_mem := ?_ comul := ?_ antipode := ?_ }, ?_⟩` and prove the remaining obligations.

Use `⟨fun x j => φ (b j) x, ?_, ?_⟩` and prove the remaining obligations. Set `M : Matrix N N R` to `fun x j => (b j : Multiplicative N → R) (Multiplicative.ofAdd x)`. Establish `hdet : Matrix.det (fun x j => φ (b j) x : Matrix N N C) = algebraMap R C M.det`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.

Rewrite using `[hdet]`. Apply `isUnit_iff_ne_zero.mpr` to reduce the goal to its premises. Rewrite using `[map_ne_zero_iff _ hinj]`. Introduce `h0`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`.

Apply `hv0` to reduce the goal to its premises. Establish `hsum : ∑ j, v j • b j = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `t`. Establish `h3` using `congrFun hv (Multiplicative.toAdd t)`.

Simplify `h3` using `[Matrix.mulVec, dotProduct, M, mul_comm]`. Conclude with `funext (Fintype.linearIndependent_iff.mp b.linearIndependent v hsum)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `f ⟨g, hg, rfl⟩`. Establish `hg' : (⟨g, hg⟩ : A) = ∑ j, b.repr ⟨g, hg⟩ j • b j` using `(b.sum_repr _).symm`.

Establish `hgs : g = ∑ j, b.repr ⟨g, hg⟩ j • (b j : Multiplicative N → R)`. Establish `h4 : ((⟨g, hg⟩ : A) : Multiplicative N → R) = ((∑ j, b.repr ⟨g, hg⟩ j • b j : A) : Multiplicative N → R)` using `congrArg Subtype.val hg'`. Rewrite `h4` using `[AddSubmonoidClass.coe_finset_sum]`. Conclude with `h4`. Rewrite using `[hgs, map_sum]`.

Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Conclude with `⟨b j, (b j).2, rfl⟩`. Introduce and unpack `f ⟨g, hg, rfl⟩ x`. Conclude with `⟨g (Multiplicative.ofAdd x), rfl⟩`. Use `⟨1, A.one_mem, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`.

Simplify using `[hφ]`. Introduce and unpack `f g ⟨f', hf', rfl⟩ ⟨g', hg', rfl⟩`. Use `⟨f' * g', A.mul_mem hf' hg', ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify using `[hφ]`.

Introduce and unpack `f ⟨g, hg, rfl⟩`. Set `ψ : (Multiplicative N × Multiplicative N → R) →ₗ[R] (N × N → C)` to `{ toFun := fun F p => algebraMap R C (F (Multiplicative.ofAdd p.1, Multiplicative.ofAdd p.2)) map_add' := by`. Introduce `F G`. Use function extensionality and compare the values at `p`. Simplify using the standard rewrite rules.

Use the proof step `map_smul' := by`. Introduce `r F`. Use function extensionality and compare the values at `p`. Simplify using `[Algebra.smul_def] }`. Establish `hle : GlobalTheory.CompanionTheory.Ar.BT.prodSpan A ≤ (ReciprocityTheory.PGsh.L2.tensorSpan R ((Subalgebra.toSubmodule A).map φ)).comap ψ`.

Rewrite using `[GlobalTheory.CompanionTheory.Ar.BT.prodSpan, Submodule.span_le]`. Introduce and unpack `_ ⟨a, ha, a', ha', rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap]`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨φ a, ⟨a, ha, rfl⟩, φ a', ⟨a', ha', rfl⟩, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `p`. Simplify using `[hφ, ψ]`. Establish `h5` using `hle (hA.comul g hg)`. Rewrite `h5` using `[Submodule.mem_comap]`. Use `h5 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `p`. Simplify using `[hφ, ψ, ReciprocityTheory.PGsh.L2.addPull, LinearMap.funLeft_apply]`. Introduce and unpack `f ⟨g, hg, rfl⟩`. Use `⟨fun t => g t⁻¹, hA.inv g hg, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`.

Simplify using `[hφ]`. Introduce `f show f ∈ (Subalgebra.toSubmodule A).map φ ↔ _`. Rewrite using `[Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, rfl⟩`.

Conclude with `⟨g, hg, fun x => rfl⟩`. Introduce and unpack `⟨g, hg, hfg⟩`. Conclude with `⟨g, hg, funext fun x => (hfg x).symm⟩`.
-/
theorem bt_pgsh : ∀ (R C : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field C] [Algebra R C], Function.Injective (algebraMap R C) → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (A : Subalgebra R (Multiplicative N → R)), IsHopfOrder A → ∃ AA : ReciprocityTheory.PGsh.L2.HopfOrder R (C := C) N, ∀ f : N → C, f ∈ AA.carrier ↔ ∃ g ∈ A, ∀ x, f x = algebraMap R C (g (Multiplicative.ofAdd x)) := by
  intro R C _ _ _ _ _ hinj N _ _ _ A hA
  classical
  let φ : (Multiplicative N → R) →ₗ[R] (N → C) :=
    { toFun := fun g x => algebraMap R C (g (Multiplicative.ofAdd x))
      map_add' := by
        intro g h
        funext x
        simp
      map_smul' := by
        intro r g
        funext x
        simp [Algebra.smul_def] }
  have hφ : ∀ g x, φ g x = algebraMap R C (g (Multiplicative.ofAdd x)) := fun _ _ => rfl
  haveI := hA.finite
  haveI := hA.projective
  haveI : Module.Free R A := Module.free_of_flat_of_isLocalRing
  obtain ⟨d, hd0, hd⟩ := hA.full
  have hcardT : Module.finrank R (Multiplicative N → R) = Fintype.card N := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact Fintype.card_congr Multiplicative.toAdd
  have hrank : Module.finrank R A = Fintype.card N := by
    apply le_antisymm
    · rw [← hcardT]
      exact LinearMap.finrank_le_finrank_of_injective (f := A.val.toLinearMap) Subtype.val_injective
    · let sc : (Multiplicative N → R) →ₗ[R] A :=
        { toFun := fun f => ⟨d • f, hd f⟩
          map_add' := fun f g => Subtype.ext (smul_add d f g)
          map_smul' := fun r f => Subtype.ext (smul_comm d r f) }
      have hsc : Function.Injective sc := by
        intro f g hfg
        have h2 : d • f = d • g := congrArg Subtype.val hfg
        exact smul_right_injective _ hd0 h2
      rw [← hcardT]
      exact LinearMap.finrank_le_finrank_of_injective hsc
  let b : Module.Basis N R A := (Module.finBasisOfFinrankEq R A hrank).reindex (Fintype.equivFin N).symm
  refine ⟨{ carrier := (Subalgebra.toSubmodule A).map φ
            lat := ?_
            le_int := ?_
            one_mem := ?_
            mul_mem := ?_
            comul := ?_
            antipode := ?_ }, ?_⟩
  · refine ⟨fun x j => φ (b j) x, ?_, ?_⟩
    · let M : Matrix N N R := fun x j => (b j : Multiplicative N → R) (Multiplicative.ofAdd x)
      have hdet : Matrix.det (fun x j => φ (b j) x : Matrix N N C) = algebraMap R C M.det := by
        rw [RingHom.map_det]
        rfl
      rw [hdet]
      apply isUnit_iff_ne_zero.mpr
      rw [map_ne_zero_iff _ hinj]
      intro h0
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      apply hv0
      have hsum : ∑ j, v j • b j = 0 := by
        apply Subtype.ext
        funext t
        have h3 := congrFun hv (Multiplicative.toAdd t)
        simpa [Matrix.mulVec, dotProduct, M, mul_comm] using h3
      exact funext (Fintype.linearIndependent_iff.mp b.linearIndependent v hsum)
    · apply le_antisymm
      · rintro f ⟨g, hg, rfl⟩
        have hg' : (⟨g, hg⟩ : A) = ∑ j, b.repr ⟨g, hg⟩ j • b j := (b.sum_repr _).symm
        have hgs : g = ∑ j, b.repr ⟨g, hg⟩ j • (b j : Multiplicative N → R) := by
          have h4 : ((⟨g, hg⟩ : A) : Multiplicative N → R)
              = ((∑ j, b.repr ⟨g, hg⟩ j • b j : A) : Multiplicative N → R) := congrArg Subtype.val hg'
          rw [AddSubmonoidClass.coe_finset_sum] at h4
          exact h4
        rw [hgs, map_sum]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [map_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact ⟨b j, (b j).2, rfl⟩
  · rintro f ⟨g, hg, rfl⟩ x
    exact ⟨g (Multiplicative.ofAdd x), rfl⟩
  · refine ⟨1, A.one_mem, ?_⟩
    funext x
    simp [hφ]
  · rintro f g ⟨f', hf', rfl⟩ ⟨g', hg', rfl⟩
    refine ⟨f' * g', A.mul_mem hf' hg', ?_⟩
    funext x
    simp [hφ]
  · rintro f ⟨g, hg, rfl⟩
    let ψ : (Multiplicative N × Multiplicative N → R) →ₗ[R] (N × N → C) :=
      { toFun := fun F p => algebraMap R C (F (Multiplicative.ofAdd p.1, Multiplicative.ofAdd p.2))
        map_add' := by
          intro F G
          funext p
          simp
        map_smul' := by
          intro r F
          funext p
          simp [Algebra.smul_def] }
    have hle : GlobalTheory.CompanionTheory.Ar.BT.prodSpan A ≤
        (ReciprocityTheory.PGsh.L2.tensorSpan R ((Subalgebra.toSubmodule A).map φ)).comap ψ := by
      rw [GlobalTheory.CompanionTheory.Ar.BT.prodSpan, Submodule.span_le]
      rintro _ ⟨a, ha, a', ha', rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      apply Submodule.subset_span
      refine ⟨φ a, ⟨a, ha, rfl⟩, φ a', ⟨a', ha', rfl⟩, ?_⟩
      funext p
      simp [hφ, ψ]
    have h5 := hle (hA.comul g hg)
    rw [Submodule.mem_comap] at h5
    convert h5 using 1
    funext p
    simp [hφ, ψ, ReciprocityTheory.PGsh.L2.addPull, LinearMap.funLeft_apply]
  · rintro f ⟨g, hg, rfl⟩
    refine ⟨fun t => g t⁻¹, hA.inv g hg, ?_⟩
    funext x
    simp [hφ]
  · intro f
    show f ∈ (Subalgebra.toSubmodule A).map φ ↔ _
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, fun x => rfl⟩
    · rintro ⟨g, hg, hfg⟩
      exact ⟨g, hg, funext fun x => (hfg x).symm⟩

end PositivityTheory.HtPt.Mk
