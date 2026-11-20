import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.ExistsUniformizerOrd
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsHasse

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN.TL

attribute [local instance 2000] Rep.hV2

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Use `show inv ((cohomologyMap μ 2).hom (cohomologyULiftIntAddEquiv A 2 (cohomologyπ A 2 x))) = _`. Rewrite using `[cohomologyULiftIntAddEquiv_cohomologyπ']`. Conclude with `congrArg inv (cohomologyMap_cohomologyπ μ (cocyclesULiftInt A x))`.
-/
theorem inv_push (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] (B : Rep.{0} ℤ G) [IsDiscreteRep B]
    [IsDiscreteRep (uliftIntToIntRep A)] (μ : uliftIntToIntRep A ⟶ B) (inv : cohomology B 2 →+ QZ)
    (x : cocycles A 2) :
    (inv.comp ((cohomologyMap μ 2).hom.toAddMonoidHom.comp
        (cohomologyULiftIntAddEquiv A 2).toAddMonoidHom)) (cohomologyπ A 2 x) =
      inv (cohomologyπ B 2 (HomologicalComplex.cyclesMap (cochainsMap μ) 2 (cocyclesULiftInt A x))) := by
  show inv ((cohomologyMap μ 2).hom (cohomologyULiftIntAddEquiv A 2 (cohomologyπ A 2 x))) = _
  rw [cohomologyULiftIntAddEquiv_cohomologyπ']
  exact congrArg inv (cohomologyMap_cohomologyπ μ (cocyclesULiftInt A x))

/- English proof (translation)
Rewrite using `[cochainOf_cocycleι_cyclesMap, cochainOf_cocycleι_cocyclesULiftInt]`.
-/
theorem cochain_push (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] (B : Rep.{0} ℤ G) [IsDiscreteRep B]
    [IsDiscreteRep (uliftIntToIntRep A)] (μ : uliftIntToIntRep A ⟶ B) (x : cocycles A 2)
    (s : Fin 2 → G) :
    cochainOf B (cocycleι B 2 (HomologicalComplex.cyclesMap (cochainsMap μ) 2 (cocyclesULiftInt A x))) s =
      μ.hom (cochainOf A (cocycleι A 2 x) s) := by
  rw [cochainOf_cocycleι_cyclesMap, cochainOf_cocycleι_cocyclesULiftInt]

end Generic

section Local

variable {Kf : FiniteSubfield} [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
  {S : Set (HeightOneSpectrum (𝓞 Kf.1))} [Fintype S] {l r : ℕ} [Fact l.Prime]
  {ιs : ∀ v : S, AlgebraicClosure ℚ →ₐ[Kf.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)}
  {v : S} {A : ValuationSubring (AlgebraicClosure ℚ)}

/- English proof (translation)
Introduce `h`. Rewrite `hϖ` using `[h, ord_zero]`. Conclude with `zero_ne_one hϖ`.
-/
theorem ord_ne_zero_loc {ϖ : 𝓞 Kf.1} (hϖ : ord (((ϖ : Kf.1) : ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))) = 1) :
    (((ϖ : Kf.1) : ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))) ≠ 0 := by
  intro h
  rw [h, ord_zero] at hϖ
  exact zero_ne_one hϖ

/- English proof (translation)
Use `show (ιs v y) ^ (l ^ r) = _`. Rewrite using `[← map_pow, hy, AlgHom.commutes, Units.val_mk0, IsScalarTower.algebraMap_apply Kf.1 ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))]`. Both sides reduce to the same expression.
-/
theorem root_loc {ϖ : 𝓞 Kf.1} (hϖ0 : (((ϖ : Kf.1) : ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))) ≠ 0) {y : AlgebraicClosure ℚ}
    (hy : y ^ (l ^ r) = algebraMap Kf.1 (AlgebraicClosure ℚ) (ϖ : Kf.1)) :
    (ιs v y) ^ ((⟨l ^ r, pow_pos (Fact.out : l.Prime).pos r⟩ : ℕ+) : ℕ) =
      algebraMap ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ((Units.mk0 _ hϖ0 : ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)ˣ) : ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) := by
  show (ιs v y) ^ (l ^ r) = _
  rw [← map_pow, hy, AlgHom.commutes, Units.val_mk0,
    IsScalarTower.algebraMap_apply Kf.1 ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))]
  rfl

/- English proof (translation)
The claim follows from `hζ.map_of_injective (ιs v).toRingHom.injective`.
-/
theorem prim_loc {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ (l ^ r)) :
    IsPrimitiveRoot (ιs v ζ) ((⟨l ^ r, pow_pos (Fact.out : l.Prime).pos r⟩ : ℕ+) : ℕ) :=
  hζ.map_of_injective (ιs v).toRingHom.injective

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `h1` using `hev g y`. Rewrite `h1` using `[hκ (ev g), map_mul, map_pow]`. Conclude with `h1.symm`.
-/
theorem kummer_loc
    {ev : ((AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ≃ₐ[((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)] (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))) ≃* Dec (F := Kf.1) A}
    (hev : ∀ σ x, ιs v (((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) x) = σ (ιs v x))
    {ζ y : AlgebraicClosure ℚ} (κ : Dec (F := Kf.1) A → ZMod (l ^ r))
    (hκ : ∀ g : Dec (F := Kf.1) A, (g : G Kf.1 (AlgebraicClosure ℚ)) y = ζ ^ (κ g).val * y)
    (g : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ≃ₐ[((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)] (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))) : g (ιs v y) = ιs v ζ ^ (κ (ev g)).val * ιs v y := by
  have h1 := hev g y
  rw [hκ (ev g), map_mul, map_pow] at h1
  exact h1.symm

end Local

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `haveI : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩`. Use `(DFunLike.congr_fun (gsLocalInvRootsQZ_eq S ιs (l ^ r) v) (cohomologyπ _ 2 x0)).trans ?_` and prove the remaining obligations. Use `(inv_push _ _ (rootsLocalMorZ S ιs (l ^ r) v) _ x0).trans ?_` and prove the remaining obligations. Establish `hϖ0` using `ord_ne_zero_loc (Kf := Kf) (v := v) hϖ`. Establish `hY` using `root_loc (ιs := ιs) (v := v) (l := l) (r := r) hϖ0 hy`.

Establish `hζv` using `prim_loc (ιs := ιs) (v := v) hζ`. Establish `hκv` using `kummer_loc (ιs := ιs) (v := v) (ev := ev) hev κ hκ`. Use `hasse_kummer_unram' ⟨l ^ r, pow_pos (Fact.out : l.Prime).pos r⟩ (Units.mk0 _ hϖ0) (by rw [Units.val_mk0]; exact hϖ) (ιs v y) hY (ιs v ζ) hζv (fun σ => κ (ev σ)) hκv _ fun s => ?_` and prove the remaining obligations. Rewrite using `[cochain_push]`. Use `(rootsLocalMorZ_hom_apply S ιs (l ^ r) v _).trans ?_` and prove the remaining obligations.

Rewrite using `[hx0 s, map_pow]`. Conclude with `congrArg (fun m : ZMod (l ^ r) => ιs v ζ ^ m.val) (congrArg (κ (ev (s 0)) * ·) (hχ (s 1)))`.
-/
theorem found_side_inv' (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (S : Set (HeightOneSpectrum (𝓞 Kf.1))) [Fintype S] {l r : ℕ} [Fact l.Prime] (hr : 0 < r)
    (hS : ∀ v : HeightOneSpectrum (𝓞 Kf.1), ((l : ℕ) : 𝓞 Kf.1) ∈ v.asIdeal → v ∈ S)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (ιs : ∀ v : S, AlgebraicClosure ℚ →ₐ[Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))
    (v : S) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : IsPlaceOver A v.1)
    (ev : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ≃* Dec (F := Kf.1) A)
    (hev : ∀ σ x, ιs v (((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) x) = σ (ιs v x))
    (ϖ : 𝓞 Kf.1) (hϖ : ord (((ϖ : Kf.1) : (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) = 1)
    (y : AlgebraicClosure ℚ) (hy : y ^ (l ^ r) = algebraMap Kf.1 (AlgebraicClosure ℚ) (ϖ : Kf.1))
    (κ : Dec (F := Kf.1) A → ZMod (l ^ r))
    (hκ : ∀ g : Dec (F := Kf.1) A, (g : G Kf.1 (AlgebraicClosure ℚ)) y = ζ ^ (κ g).val * y)
    (χ : Dec (F := Kf.1) A → ZMod (l ^ r))
    (hχ : ∀ σ, χ (ev σ) = urChar ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))
      ⟨l ^ r, pow_pos (Fact.out : l.Prime).pos r⟩ σ)
    (x0 : cocycles (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S (l ^ r))) 2)
    (hx0 : ∀ s : Fin 2 → (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
          (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)),
        ((((Additive.toMul (cochainOf _ (cocycleι _ 2 x0) s) :
          rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) :
          (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) :
          maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ) =
          ζ ^ (κ (ev (s 0)) * χ (ev (s 1))).val) :
    gsLocalInvRootsQZ S ιs (l ^ r) v (cohomologyπ _ 2 x0) = - zmodToQZ (l ^ r) 1 := by
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  refine (DFunLike.congr_fun (gsLocalInvRootsQZ_eq S ιs (l ^ r) v) (cohomologyπ _ 2 x0)).trans ?_
  refine (inv_push _ _ (rootsLocalMorZ S ιs (l ^ r) v) _ x0).trans ?_
  have hϖ0 := ord_ne_zero_loc (Kf := Kf) (v := v) hϖ
  have hY := root_loc (ιs := ιs) (v := v) (l := l) (r := r) hϖ0 hy
  have hζv := prim_loc (ιs := ιs) (v := v) hζ
  have hκv := kummer_loc (ιs := ιs) (v := v) (ev := ev) hev κ hκ
  refine hasse_kummer_unram' ⟨l ^ r, pow_pos (Fact.out : l.Prime).pos r⟩ (Units.mk0 _ hϖ0)
    (by rw [Units.val_mk0]; exact hϖ) (ιs v y) hY (ιs v ζ) hζv (fun σ => κ (ev σ)) hκv _ fun s => ?_
  rw [cochain_push]
  refine (rootsLocalMorZ_hom_apply S ιs (l ^ r) v _).trans ?_
  rw [hx0 s, map_pow]
  exact congrArg (fun m : ZMod (l ^ r) => ιs v ζ ^ m.val) (congrArg (κ (ev (s 0)) * ·) (hχ (s 1)))

end PositivityTheory.Lit1.PTN.TL
