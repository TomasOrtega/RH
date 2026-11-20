import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.LamSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.PairTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsDeterminantPairMapOfAlgHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi

open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

/- English proof (translation)
Introduce `l _ F O _ _ _ n r B R _ _ _ f₀ γ hγ`. Take `⟨p, hp, hp'⟩` from `exists_determinantPair_map_of_algHom l F O n r B.B R f₀ B.u`. Take `⟨q, hq, hq'⟩` from `pairTw p γ hγ`. Take `⟨f, ⟨hf, hf'⟩, -⟩` from `B.univ R q`. Use `⟨f, fun g i hi => ?_, fun v i g => ?_⟩` and prove the remaining obligations.

Rewrite using `[← (UpperTheory.V.AlgebraTools.Det.mapApi B.u.D (f : B.B →+* R)).2.2.1, hf, hq, lam_twD, twA_single, ← (UpperTheory.V.AlgebraTools.Det.mapApi B.u.D (f₀ : B.B →+* R)).2.2.1, hp]`. Establish `h : MonoidAlgebra.single g (1 * algebraMap R R (γ g)) = (γ g : R) • (MonoidAlgebra.single g 1 : MonoidAlgebra R F.G₀)` using `by simp`. Rewrite using `[h, lamSmul, min_eq_left hi]`. Establish `h1` using `congrArg (fun χ : F.Gv v →* Rˣ => (χ g : R)) ((hf' v i).trans (hq' v i))`. Rewrite `h1` using `[← hp' v i]`.

Conclude with `h1`.
-/
theorem UpperTheory.V.Ws.H5.twMapEx :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (f₀ : B.B →ₐ[O] R) (γ : F.G₀ →* Rˣ), TwCh F γ → ∃ f : B.B →ₐ[O] R, TwMap B (f₀ : B.B →+* R) (f : B.B →+* R) γ := by
  intro l _ F O _ _ _ n r B R _ _ _ f₀ γ hγ
  obtain ⟨p, hp, hp'⟩ := exists_determinantPair_map_of_algHom l F O n r B.B R f₀ B.u
  obtain ⟨q, hq, hq'⟩ := pairTw p γ hγ
  obtain ⟨f, ⟨hf, hf'⟩, -⟩ := B.univ R q
  refine ⟨f, fun g i hi => ?_, fun v i g => ?_⟩
  · rw [← (UpperTheory.V.AlgebraTools.Det.mapApi B.u.D (f : B.B →+* R)).2.2.1, hf, hq, lam_twD, twA_single,
      ← (UpperTheory.V.AlgebraTools.Det.mapApi B.u.D (f₀ : B.B →+* R)).2.2.1, hp]
    have h : MonoidAlgebra.single g (1 * algebraMap R R (γ g)) =
        (γ g : R) • (MonoidAlgebra.single g 1 : MonoidAlgebra R F.G₀) := by simp
    rw [h, lamSmul, min_eq_left hi]
  · have h1 := congrArg (fun χ : F.Gv v →* Rˣ => (χ g : R)) ((hf' v i).trans (hq' v i))
    rw [← hp' v i] at h1
    exact h1
