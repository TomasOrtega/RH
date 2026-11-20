import Mathlib

open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `⟨fun J hJ => ?_⟩` and prove the remaining obligations. Establish `hfin : Module.Finite B J` using `Module.Finite.iff_fg.2 hJ`. Establish `htB : Submodule.torsion W B = ⊥` using `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.1 inferInstance`. Establish `hW : Module.Flat W J`. Rewrite using `[Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]`.

Introduce and unpack `x ⟨a, ha⟩`. Establish `hx : (x : B) ∈ Submodule.torsion W B` using `⟨a, congrArg Subtype.val ha⟩`. Rewrite `hx` using `[htB, Submodule.mem_bot]`. Conclude with `(Submodule.mem_bot W).2 (Subtype.ext hx)`. Establish `hB : Module.Flat B J` using `Algebra.FormallyUnramified.flat_of_restrictScalars W B J`.

Establish `hfree : Module.Free B J` using `Module.free_of_flat_of_isLocalRing`. Rewrite using `[← Submodule.rank_le_one_iff_isPrincipal]`. Conclude with `(Submodule.rank_le J).trans (Module.rank_self B).le`.
-/
theorem isBezout_of_flat_of_formallyUnramified (W B : Type) [CommRing W] [IsDomain W] [IsBezout W]
    [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra W B] [Module.Flat W B]
    [Algebra.EssFiniteType W B] [Algebra.FormallyUnramified W B] : IsBezout B := by
  refine ⟨fun J hJ => ?_⟩
  have hfin : Module.Finite B J := Module.Finite.iff_fg.2 hJ
  have htB : Submodule.torsion W B = ⊥ :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.1 inferInstance
  have hW : Module.Flat W J := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro x ⟨a, ha⟩
    have hx : (x : B) ∈ Submodule.torsion W B := ⟨a, congrArg Subtype.val ha⟩
    rw [htB, Submodule.mem_bot] at hx
    exact (Submodule.mem_bot W).2 (Subtype.ext hx)
  have hB : Module.Flat B J := Algebra.FormallyUnramified.flat_of_restrictScalars W B J
  have hfree : Module.Free B J := Module.free_of_flat_of_isLocalRing
  rw [← Submodule.rank_le_one_iff_isPrincipal]
  exact (Submodule.rank_le J).trans (Module.rank_self B).le

/- English proof (translation)
Set `K` to `FractionRing W`. Establish `hfin : Module.Finite K (K ⊗[W] B)` using `Algebra.FormallyUnramified.finite_of_free K _`. Establish `halg : Algebra.IsAlgebraic K (K ⊗[W] B)` using `inferInstance`. Establish `hK : Algebra.IsAlgebraic W K` using `IsLocalization.isAlgebraic K (nonZeroDivisors W)`. Establish `halgW : Algebra.IsAlgebraic W (K ⊗[W] B)` using `Algebra.IsAlgebraic.trans W K _`.

Conclude with `Algebra.IsAlgebraic.of_injective (Algebra.TensorProduct.includeRight (R := W) (A := K) (B := B)) (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective W K))`.
-/
theorem isAlgebraic_of_flat_of_formallyUnramified (W B : Type) [CommRing W] [IsDomain W]
    [CommRing B] [Algebra W B] [Module.Flat W B]
    [Algebra.EssFiniteType W B] [Algebra.FormallyUnramified W B] : Algebra.IsAlgebraic W B := by
  let K := FractionRing W
  have hfin : Module.Finite K (K ⊗[W] B) := Algebra.FormallyUnramified.finite_of_free K _
  have halg : Algebra.IsAlgebraic K (K ⊗[W] B) := inferInstance
  have hK : Algebra.IsAlgebraic W K := IsLocalization.isAlgebraic K (nonZeroDivisors W)
  have halgW : Algebra.IsAlgebraic W (K ⊗[W] B) := Algebra.IsAlgebraic.trans W K _
  exact Algebra.IsAlgebraic.of_injective
    (Algebra.TensorProduct.includeRight (R := W) (A := K) (B := B))
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective W K))

/- English proof (translation)
Introduce `W B _ _ _ _ _ _ _ _ _ _`. Use `isBezout_of_flat_of_formallyUnramified W B` as an intermediate fact. Conclude with `⟨inferInstance, isAlgebraic_of_flat_of_formallyUnramified W B⟩`.
-/
theorem valuationRing_of_flat_of_formallyUnramified :
    ∀ (W B : Type) [CommRing W] [IsDomain W] [ValuationRing W] [CommRing B] [IsDomain B]
      [IsLocalRing B] [Algebra W B] [Module.Flat W B] [Algebra.EssFiniteType W B]
      [Algebra.FormallyUnramified W B], ValuationRing B ∧ Algebra.IsAlgebraic W B := by
  intro W B _ _ _ _ _ _ _ _ _ _
  have := isBezout_of_flat_of_formallyUnramified W B
  exact ⟨inferInstance, isAlgebraic_of_flat_of_formallyUnramified W B⟩

end GlobalTheory
