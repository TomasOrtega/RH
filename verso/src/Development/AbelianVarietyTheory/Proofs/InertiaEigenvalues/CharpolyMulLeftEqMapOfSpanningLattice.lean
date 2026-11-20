import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Establish `hRF : Function.Injective (algebraMap R F)` using `IsFractionRing.injective R F`. Use `haveI : Module.IsTorsionFree R S := by`. Use `Module.IsTorsionFree.of_smul_eq_zero ?_` and prove the remaining obligations. Introduce `r x h`. Distinguish the cases in `hr : r = 0`.

Conclude with `Or.inl hr`. Use `right`. Apply `hι` to reduce the goal to its premises. Establish `h1 : algebraMap R F r • ι x = 0`. Rewrite using `[algebraMap_smul, ← map_smul, h, map_zero]`.

Establish `h2 : algebraMap R F r ≠ 0` using `fun h0 => hr (hRF (by simpa using h0))`. Rewrite using `[map_zero]`. Conclude with `(smul_eq_zero.mp h1).resolve_left h2`. Use `haveI : Module.Free R S := Module.free_of_finite_type_torsion_free'`. Set `b : Module.Basis (Fin (Module.finrank R S)) R S` to `Module.finBasis R S`.

Use `⟨_, b, fun x => ?_⟩` and prove the remaining obligations. Establish `hexp : ∀ y : S, ι y = ∑ i, algebraMap R F (b.repr y i) • ι (b i)`. Introduce `y`. Use `conv_lhs => rw [← b.sum_repr y]`. Simplify using `only [map_sum, map_smul, algebraMap_smul]`.

Establish `hliR : LinearIndependent R (fun i => ι (b i))` using `b.linearIndependent.map' ι.toLinearMap (LinearMap.ker_eq_bot.mpr hι)`. Establish `hli : LinearIndependent F (fun i => ι (b i))` using `(LinearIndependent.iff_fractionRing R F).mp hliR`. Establish `hsp : ⊤ ≤ Submodule.span F (Set.range (fun i => ι (b i)))`. Rewrite using `[← hspan, Submodule.span_le]`. Introduce and unpack `_ ⟨y, rfl⟩`.

Rewrite using `[hexp y]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Set `b' : Module.Basis (Fin (Module.finrank R S)) F A` to `Module.Basis.mk hli hsp`. Establish `hb' : ∀ i, b' i = ι (b i)` using `fun i => by simp [b']`. Establish `hM : LinearMap.toMatrix b' b' (LinearMap.mulLeft F (ι x)) = (LinearMap.toMatrix b b (LinearMap.mulLeft R x)).map (algebraMap R F)`.

Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, hb', ← map_mul, hexp]`. Simplify using `only [← hb']`. Rewrite using `[b'.repr_sum_self]`. Rewrite using `[← LinearMap.charpoly_toMatrix _ b', hM, Matrix.charpoly_map]`.
-/
theorem charpoly_mulLeft_eq_map_of_spanning_lattice (R F A S : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field F] [Algebra R F] [IsFractionRing R F] [CommRing A]
    [Algebra F A] [Algebra R A] [IsScalarTower R F A] [Module.Finite F A] [CommRing S]
    [Algebra R S] [Module.Finite R S] (ι : S →ₐ[R] A) (hι : Function.Injective ι)
    (hspan : Submodule.span F (Set.range ι) = ⊤) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) R S), ∀ x : S, (LinearMap.mulLeft F (ι x)).charpoly =
      ((LinearMap.toMatrix b b (LinearMap.mulLeft R x)).charpoly).map (algebraMap R F) := by
  classical
  have hRF : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  haveI : Module.IsTorsionFree R S := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro r x h
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      apply hι
      have h1 : algebraMap R F r • ι x = 0 := by
        rw [algebraMap_smul, ← map_smul, h, map_zero]
      have h2 : algebraMap R F r ≠ 0 := fun h0 => hr (hRF (by simpa using h0))
      rw [map_zero]
      exact (smul_eq_zero.mp h1).resolve_left h2
  haveI : Module.Free R S := Module.free_of_finite_type_torsion_free'
  let b : Module.Basis (Fin (Module.finrank R S)) R S := Module.finBasis R S
  refine ⟨_, b, fun x => ?_⟩
  have hexp : ∀ y : S, ι y = ∑ i, algebraMap R F (b.repr y i) • ι (b i) := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    simp only [map_sum, map_smul, algebraMap_smul]
  have hliR : LinearIndependent R (fun i => ι (b i)) :=
    b.linearIndependent.map' ι.toLinearMap (LinearMap.ker_eq_bot.mpr hι)
  have hli : LinearIndependent F (fun i => ι (b i)) :=
    (LinearIndependent.iff_fractionRing R F).mp hliR
  have hsp : ⊤ ≤ Submodule.span F (Set.range (fun i => ι (b i))) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    rw [hexp y]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' : Module.Basis (Fin (Module.finrank R S)) F A := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = ι (b i) := fun i => by simp [b']
  have hM : LinearMap.toMatrix b' b' (LinearMap.mulLeft F (ι x)) =
      (LinearMap.toMatrix b b (LinearMap.mulLeft R x)).map (algebraMap R F) := by
    ext i j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
      LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, hb', ← map_mul, hexp]
    simp only [← hb']
    rw [b'.repr_sum_self]
  rw [← LinearMap.charpoly_toMatrix _ b', hM, Matrix.charpoly_map]

end GlobalTheory
