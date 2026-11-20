import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPres
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsPowUniformizerSmulEqZeroQuotientLattice
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.IsLocallyConstantTorsionPushOfContinuous

open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

/- English proof (translation)
Introduce `G O LL _ _ _ _ _ _ _ _ _ _ hinj lam Xs n k N M f hlam hopen hN hP`. Take `⟨m, x, E, Y, hYfg, hst, hE, φ, hφ, hf⟩` from `hP`. Use `haveI : Module.Finite O Y := Module.Finite.iff_fg.mpr hYfg`. Take `⟨e, he⟩` from `exists_pow_uniformizer_smul_eq_zero_quotient_lattice lam hlam φ`. Establish `hmul : ∀ g h (v : Fin m → Fin n → LL), actN LL (fun j => N (x j)) (g * h) v = actN LL (fun j => N (x j)) g (actN LL (fun j => N (x j)) h v)`.

Introduce `g h v`. Use function extensionality and compare the values at `j`. Simplify using `only [actN, map_mul, Matrix.map_mul, Matrix.mulVec_mulVec]`. Establish `hsub : ∀ g (v w : Fin m → Fin n → LL), actN LL (fun j => N (x j)) g (v - w) = actN LL (fun j => N (x j)) g v - actN LL (fun j => N (x j)) g w`. Introduce `g v w`.

Use function extensionality and compare the values at `j`. Simplify using `only [actN, Pi.sub_apply, Matrix.mulVec_sub]`. Establish `hfun : f = fun g => φ ⟨actN LL (fun j => N (x j)) g E - E, hE g⟩` using `funext hf`. Use `⟨e, ⟨?_, fun g h => ?_⟩, fun g => by rw [hf g]; exact he _⟩` and prove the remaining obligations. Rewrite using `[hfun]`.

Use `isLocallyConstant_torsion_push_of_continuous Y φ _ hE (lam ^ e) hopen ?_ (pow_ne_zero _ hlam.ne_zero) he` and prove the remaining obligations. Conclude with `(continuous_pi fun j => (hN (x j)).matrix_mulVec continuous_const).sub continuous_const`. Establish `hsplit : (⟨actN LL (fun j => N (x j)) (g * h) E - E, hE (g * h)⟩ : Y) = ⟨actN LL (fun j => N (x j)) g ↑(⟨actN LL (fun j => N (x j)) h E - E, hE h⟩ : Y), hst g _ (hE h)⟩ + ⟨actN LL (fun j => N (x j)) g E - E, hE g⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Submodule.coe_add, hmul, hsub]`.

Normalize the expressions using the abelian group laws. Rewrite using `[hf, hf, hf, hsplit, map_add, hφ]`. Conclude with `add_comm _ _`.
-/
theorem _root_.UpperTheory.KN.exists_cocycle_torsion_of_hasPres :
    ∀ {G O LL : Type} [Group G] [TopologicalSpace G] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field LL]
      [TopologicalSpace LL] [IsTopologicalRing LL] [Algebra O LL] [IsFractionRing O LL] (hinj : Function.Injective (algebraMap O LL))
      (lam : O) {Xs : Type} {n k : ℕ} (N : Xs → (G →* Matrix (Fin n) (Fin n) O)) (M : G →* Matrix (Fin k) (Fin k) O)
      (f : G → (Fin k → LL) ⧸ stdG O LL k), Irreducible lam → IsOpen (Set.range (algebraMap O LL)) →
      (∀ x, Continuous fun g => (N x g).map (algebraMap O LL)) →
      HasPres LL N (Q := (Fin k → LL) ⧸ stdG O LL k) (fun g => actD (stdLatG hinj M) g) f →
      ∃ a : ℕ, f ∈ divisibleCocycles (stdLatG hinj M) ∧ ∀ g, lam ^ a • f g = 0 := by
  intro G O LL _ _ _ _ _ _ _ _ _ _ hinj lam Xs n k N M f hlam hopen hN hP
  obtain ⟨m, x, E, Y, hYfg, hst, hE, φ, hφ, hf⟩ := hP
  haveI : Module.Finite O Y := Module.Finite.iff_fg.mpr hYfg
  obtain ⟨e, he⟩ := exists_pow_uniformizer_smul_eq_zero_quotient_lattice lam hlam φ
  have hmul : ∀ g h (v : Fin m → Fin n → LL), actN LL (fun j => N (x j)) (g * h) v =
      actN LL (fun j => N (x j)) g (actN LL (fun j => N (x j)) h v) := by
    intro g h v
    funext j
    simp only [actN, map_mul, Matrix.map_mul, Matrix.mulVec_mulVec]
  have hsub : ∀ g (v w : Fin m → Fin n → LL), actN LL (fun j => N (x j)) g (v - w) =
      actN LL (fun j => N (x j)) g v - actN LL (fun j => N (x j)) g w := by
    intro g v w
    funext j
    simp only [actN, Pi.sub_apply, Matrix.mulVec_sub]
  have hfun : f = fun g => φ ⟨actN LL (fun j => N (x j)) g E - E, hE g⟩ := funext hf
  refine ⟨e, ⟨?_, fun g h => ?_⟩, fun g => by rw [hf g]; exact he _⟩
  · rw [hfun]
    refine isLocallyConstant_torsion_push_of_continuous Y φ _ hE (lam ^ e) hopen ?_ (pow_ne_zero _ hlam.ne_zero) he
    exact (continuous_pi fun j => (hN (x j)).matrix_mulVec continuous_const).sub continuous_const
  · have hsplit : (⟨actN LL (fun j => N (x j)) (g * h) E - E, hE (g * h)⟩ : Y) =
        ⟨actN LL (fun j => N (x j)) g ↑(⟨actN LL (fun j => N (x j)) h E - E, hE h⟩ : Y),
          hst g _ (hE h)⟩ + ⟨actN LL (fun j => N (x j)) g E - E, hE g⟩ := by
      apply Subtype.ext
      simp only [Submodule.coe_add, hmul, hsub]
      abel
    rw [hf, hf, hf, hsplit, map_add, hφ]
    exact add_comm _ _
