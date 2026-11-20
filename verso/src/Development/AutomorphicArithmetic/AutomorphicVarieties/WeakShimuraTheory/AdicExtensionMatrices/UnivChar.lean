import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivLift

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def toMat {G R : Type} [Group G] [CommRing R] (ψ : G →* R) : G →* Matrix Unit Unit R where
  toFun g := Matrix.of fun _ _ => ψ g
  map_one' := Matrix.ext fun _ _ => by simp
  map_mul' g h := Matrix.ext fun _ _ => by simp [Matrix.mul_apply]

private def ofMat {G R : Type} [Group G] [CommRing R] (r : G →* Matrix Unit Unit R) : G →* R where
  toFun g := r g () ()
  map_one' := by simp
  map_mul' g h := by simp [Matrix.mul_apply]

/- English proof (translation)
Introduce `l _ Λ _ _ _ _ _ _ G _ _ _ _ _ χ hΦ hχ`. Establish `hloc : IsLocallyConstant (toMat χ)` using `hχ.comp (fun x : ResidueField Λ => (Matrix.of fun _ _ => x : Matrix Unit Unit (ResidueField Λ)))`. Take `⟨R, _, _, _, r, hr⟩` from `univ_lift l Λ G Unit (toMat χ) hΦ hloc`. Use `⟨R, inferInstance, inferInstance, inferInstance, ofMat r.hom, r.cont () (), fun s => r.red s () (), ?_⟩` and prove the remaining obligations. Introduce `R' _ _ _ ψ' hc hred`.

Set `r' : Lift Λ (toMat χ) R'` to `⟨toMat ψ', fun _ _ => hc, fun g _ _ => hred g⟩`. Take `⟨f, hf, huniq⟩` from `(hr R').2 r' trivial`. Establish `key : ∀ g : R →ₐ[Λ] R', (∀ s, g (ofMat r.hom s) = ψ' s) ↔ Lift.map g r = r'`. Introduce `g`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Apply `Lift.ext` to reduce the goal to its premises. Use extensionality with `s a b`. Consider the cases of `a`. Consider the cases of `b`.

Conclude with `(Lift.map_hom g r s () ()).trans (h s)`. Introduce `h s`. Use `congrArg (fun x : Lift Λ (toMat χ) R' => x.hom s () ()) h` as an intermediate fact. Conclude with `(Lift.map_hom g r s () ()).symm.trans this`. Conclude with `⟨f, (key f).2 hf, fun g hg => huniq g ((key g).1 hg)⟩`.
-/
theorem UpperTheory.V.Ws.sxUnivChar :
    ∀ (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] [CharP (ResidueField Λ) l] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (χ : G →* ResidueField Λ), PhiCond G l → IsLocallyConstant χ → ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (ψ : G →* R), AdicCont (maximalIdeal R) ψ ∧ (∀ s, res Λ R (ψ s) = χ s) ∧ ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (ψ' : G →* R'), AdicCont (maximalIdeal R') ψ' → (∀ s, res Λ R' (ψ' s) = χ s) → ∃! f : R →ₐ[Λ] R', ∀ s, f (ψ s) = ψ' s := by
  intro l _ Λ _ _ _ _ _ _ G _ _ _ _ _ χ hΦ hχ
  have hloc : IsLocallyConstant (toMat χ) :=
    hχ.comp (fun x : ResidueField Λ => (Matrix.of fun _ _ => x : Matrix Unit Unit (ResidueField Λ)))
  obtain ⟨R, _, _, _, r, hr⟩ := univ_lift l Λ G Unit (toMat χ) hΦ hloc
  refine ⟨R, inferInstance, inferInstance, inferInstance, ofMat r.hom, r.cont () (), fun s => r.red s () (), ?_⟩
  intro R' _ _ _ ψ' hc hred
  let r' : Lift Λ (toMat χ) R' := ⟨toMat ψ', fun _ _ => hc, fun g _ _ => hred g⟩
  obtain ⟨f, hf, huniq⟩ := (hr R').2 r' trivial
  have key : ∀ g : R →ₐ[Λ] R', (∀ s, g (ofMat r.hom s) = ψ' s) ↔ Lift.map g r = r' := by
    intro g
    constructor
    · intro h
      apply Lift.ext
      ext s a b
      cases a
      cases b
      exact (Lift.map_hom g r s () ()).trans (h s)
    · intro h s
      have := congrArg (fun x : Lift Λ (toMat χ) R' => x.hom s () ()) h
      exact (Lift.map_hom g r s () ()).symm.trans this
  exact ⟨f, (key f).2 hf, fun g hg => huniq g ((key g).1 hg)⟩
