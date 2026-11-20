import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PlainAtR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Gam UpperTheory.V.Z.Win
open GroundTheory.Global.SemiLocal UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace UpperTheory.V.Z.Win

/- English proof (translation)
Take `⟨a, ha⟩` from `hb.2 (Algebra.norm B' x)`. Establish `h1 : Module.finrank A B' = 1`. Rewrite using `[← (AlgEquiv.ofBijective (Algebra.ofId A B') hb).toLinearEquiv.finrank_eq, Module.finrank_self]`. Rewrite using `[Algebra.norm_norm, ← Algebra.norm_norm (S := B') (R := A), ← ha, Algebra.norm_algebraMap, h1, pow_one]`.
-/
private theorem norm_through {A B B' C : Type} [Field A] [Field B] [Field B'] [Field C] [Algebra A B] [Algebra A B'] [Algebra A C]
    [Algebra B C] [Algebra B' C] [IsScalarTower A B C] [IsScalarTower A B' C] [FiniteDimensional A B] [FiniteDimensional B C]
    [FiniteDimensional A B'] [FiniteDimensional B' C] (hb : Function.Bijective (algebraMap A B')) (x : C) :
    algebraMap A B' (Algebra.norm A (Algebra.norm B x)) = Algebra.norm B' x := by
  obtain ⟨a, ha⟩ := hb.2 (Algebra.norm B' x)
  have h1 : Module.finrank A B' = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId A B') hb).toLinearEquiv.finrank_eq, Module.finrank_self]
  rw [Algebra.norm_norm, ← Algebra.norm_norm (S := B') (R := A), ← ha, Algebra.norm_algebraMap, h1, pow_one]

/- English proof (translation)
Use `IsScalarTower.of_algebraMap_eq fun x => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `completionMap v u x = completionMap w u (completionMap v w x)`. Use `(HeightOneSpectrum.denseRange_algebraMap F v).induction_on x (isClosed_eq (continuous_completionMap v u) ((continuous_completionMap w u).comp (continuous_completionMap v w))) fun k => ?_` and prove the remaining obligations. Rewrite using `[completionMap_algebraMap, completionMap_algebraMap, IsScalarTower.algebraMap_apply F E (w.adicCompletion E), completionMap_algebraMap, IsScalarTower.algebraMap_apply F E (u.adicCompletion M), IsScalarTower.algebraMap_apply E M (u.adicCompletion M)]`.
-/
private theorem tower {F E M : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field M] [NumberField M]
    [Algebra F E] [Algebra F M] [Algebra E M] [IsScalarTower F E M] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (u : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver w.asIdeal] [u.asIdeal.LiesOver v.asIdeal] :
    IsScalarTower (v.adicCompletion F) (w.adicCompletion E) (u.adicCompletion M) := by
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  change completionMap v u x = completionMap w u (completionMap v w x)
  refine (HeightOneSpectrum.denseRange_algebraMap F v).induction_on x
    (isClosed_eq (continuous_completionMap v u) ((continuous_completionMap w u).comp (continuous_completionMap v w))) fun k => ?_
  rw [completionMap_algebraMap, completionMap_algebraMap, IsScalarTower.algebraMap_apply F E (w.adicCompletion E),
    completionMap_algebraMap, IsScalarTower.algebraMap_apply F E (u.adicCompletion M),
    IsScalarTower.algebraMap_apply E M (u.adicCompletion M)]

/- English proof (translation)
Use `haveI hUv : U.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans U.asIdeal w'.asIdeal v.asIdeal`. Use `haveI hwv : w.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.tower_bot U.asIdeal w.asIdeal v.asIdeal`. Use `haveI := tower v w U`. Use `haveI := tower v w' U`. Use `haveI f1 : FiniteDimensional (v.adicCompletion F) (w.adicCompletion E) := GroundTheory.Global.finite_adicCompletion v w`.

Use `haveI f2 : FiniteDimensional (w.adicCompletion E) (U.adicCompletion M) := GroundTheory.Global.finite_adicCompletion w U`. Use `haveI f3 : FiniteDimensional (v.adicCompletion F) (w'.adicCompletion E') := GroundTheory.Global.finite_adicCompletion v w'`. Use `haveI f4 : FiniteDimensional (w'.adicCompletion E') (U.adicCompletion M) := GroundTheory.Global.finite_adicCompletion w' U`. Establish `hmap : ∀ a, algebraMap (v.adicCompletion F) (w'.adicCompletion E') a = i a`. Introduce `a`.

Express the relevant statement in the definitionally equal form `completionMap v w' a = i a`. Use `(HeightOneSpectrum.denseRange_algebraMap F v).induction_on a (isClosed_eq (continuous_completionMap v w') hi.1) fun k => ?_` and prove the remaining obligations. Rewrite using `[completionMap_algebraMap, hi.2, IsScalarTower.algebraMap_apply F E' (w'.adicCompletion E')]`. Establish `hb : Function.Bijective (algebraMap (v.adicCompletion F) (w'.adicCompletion E'))`. Establish `: (algebraMap (v.adicCompletion F) (w'.adicCompletion E') : _ → _) = i` using `funext hmap`.

Rewrite using `[this]`. Conclude with `i.bijective`. Set `j : (v.adicCompletion F)ˣ →* (w'.adicCompletion E')ˣ` to `Units.map ((i : v.adicCompletion F →+* w'.adicCompletion E') : v.adicCompletion F →* w'.adicCompletion E')`. Establish `hj : Continuous j` using `Continuous.units_map _ hi.1`. Establish `hc : Continuous (algebraMap (v.adicCompletion F) (w.adicCompletion E))` using `continuous_completionMap v w`.

Use `⟨(χ'.comp j).comp (nm (⟨w, hwv⟩ : PlacesOver E v)), GlobalTheory.LBC.Inh.isSmoothChar_comp_norm hc (hχ'.comp j hj), ?_⟩` and prove the remaining obligations. Use `MonoidHom.ext fun x => ?_` and prove the remaining obligations. Simplify using `only [MonoidHom.comp_apply]`. Use `congrArg χ' (Units.ext ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `i (Algebra.norm (v.adicCompletion F) (Algebra.norm (w.adicCompletion E) (x : U.adicCompletion M))) = Algebra.norm (w'.adicCompletion E') (x : U.adicCompletion M)`.

Rewrite using `[← hmap]`. Conclude with `norm_through hb _`.
-/
private theorem exists_char {F E E' M : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field E'] [NumberField E']
    [Field M] [NumberField M] [Algebra F E] [Algebra F E'] [Algebra F M] [Algebra E M] [Algebra E' M]
    [IsScalarTower F E M] [IsScalarTower F E' M] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (w' : HeightOneSpectrum (𝓞 E')) (hw'v : w'.asIdeal.LiesOver v.asIdeal) (U : HeightOneSpectrum (𝓞 M)) (hU : U.asIdeal.LiesOver w.asIdeal) (hU' : U.asIdeal.LiesOver w'.asIdeal)
    (i : v.adicCompletion F ≃+* w'.adicCompletion E') (hi : IsCompl i)
    (χ' : (w'.adicCompletion E')ˣ →* ℂˣ) (hχ' : IsSmoothChar χ') :
    ∃ χ : (w.adicCompletion E)ˣ →* ℂˣ, IsSmoothChar χ ∧
      χ.comp (nm (⟨U, hU⟩ : PlacesOver M w)) = χ'.comp (nm (⟨U, hU'⟩ : PlacesOver M w')) := by
  haveI hUv : U.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans U.asIdeal w'.asIdeal v.asIdeal
  haveI hwv : w.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.tower_bot U.asIdeal w.asIdeal v.asIdeal
  haveI := tower v w U
  haveI := tower v w' U
  haveI f1 : FiniteDimensional (v.adicCompletion F) (w.adicCompletion E) := GroundTheory.Global.finite_adicCompletion v w
  haveI f2 : FiniteDimensional (w.adicCompletion E) (U.adicCompletion M) := GroundTheory.Global.finite_adicCompletion w U
  haveI f3 : FiniteDimensional (v.adicCompletion F) (w'.adicCompletion E') := GroundTheory.Global.finite_adicCompletion v w'
  haveI f4 : FiniteDimensional (w'.adicCompletion E') (U.adicCompletion M) := GroundTheory.Global.finite_adicCompletion w' U
  have hmap : ∀ a, algebraMap (v.adicCompletion F) (w'.adicCompletion E') a = i a := by
    intro a
    change completionMap v w' a = i a
    refine (HeightOneSpectrum.denseRange_algebraMap F v).induction_on a
      (isClosed_eq (continuous_completionMap v w') hi.1) fun k => ?_
    rw [completionMap_algebraMap, hi.2, IsScalarTower.algebraMap_apply F E' (w'.adicCompletion E')]
  have hb : Function.Bijective (algebraMap (v.adicCompletion F) (w'.adicCompletion E')) := by
    have : (algebraMap (v.adicCompletion F) (w'.adicCompletion E') : _ → _) = i := funext hmap
    rw [this]
    exact i.bijective
  let j : (v.adicCompletion F)ˣ →* (w'.adicCompletion E')ˣ :=
    Units.map ((i : v.adicCompletion F →+* w'.adicCompletion E') : v.adicCompletion F →* w'.adicCompletion E')
  have hj : Continuous j := Continuous.units_map _ hi.1
  have hc : Continuous (algebraMap (v.adicCompletion F) (w.adicCompletion E)) := continuous_completionMap v w
  refine ⟨(χ'.comp j).comp (nm (⟨w, hwv⟩ : PlacesOver E v)), GlobalTheory.LBC.Inh.isSmoothChar_comp_norm hc (hχ'.comp j hj), ?_⟩
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.comp_apply]
  refine congrArg χ' (Units.ext ?_)
  change i (Algebra.norm (v.adicCompletion F) (Algebra.norm (w.adicCompletion E) (x : U.adicCompletion M))) =
    Algebra.norm (w'.adicCompletion E') (x : U.adicCompletion M)
  rw [← hmap]
  exact norm_through hb _

end UpperTheory.V.Z.Win

/- English proof (translation)
Introduce `F E E' M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n Q w w' u u' huu i hi hT`. Take `⟨U, hU⟩` from `u`. Take `⟨U', hU'⟩` from `u'`. Take `rfl : U = U'` from `huu`. Introduce `s hs ζ hζ hm`.

Take `⟨χ', hχ', hun⟩` from `hT s hs ζ hζ hm`. Take `⟨χ, hχ, e⟩` from `exists_char _ w w' inferInstance U hU hU' i hi χ' hχ'`. Conclude with `⟨χ, hχ, by rw [e]; exact hun⟩`.
-/
theorem UpperTheory.V.Z.Win.thruTr :
    ThruTr := by
  intro F E E' M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n Q w w' u u' huu i hi hT
  obtain ⟨U, hU⟩ := u
  obtain ⟨U', hU'⟩ := u'
  obtain rfl : U = U' := huu
  intro s hs ζ hζ hm
  obtain ⟨χ', hχ', hun⟩ := hT s hs ζ hζ hm
  obtain ⟨χ, hχ, e⟩ := exists_char _ w w' inferInstance U hU hU' i hi χ' hχ'
  exact ⟨χ, hχ, by rw [e]; exact hun⟩
