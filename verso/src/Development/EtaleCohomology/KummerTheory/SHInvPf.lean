import Development.EtaleCohomology.KummerTheory.InjSlice

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

/- English proof (translation)
Introduce `n`. Use `Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n, fun x => ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← pull_comp, IsIso.inv_hom_id, pull_id]`. Rewrite using `[← pull_comp, IsIso.hom_inv_id, pull_id]`.
-/
theorem shinv_eqv_of_iso {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') [IsIso f] (F : Shv R) : Eqv R f F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Conclude with `pull_comp R f g F n x`.
-/
theorem shinv_pull_comp_fun {R : Type} [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R) (n : ℤ) :
    (pull R (f ≫ g) F n : H R E'' F n → H R E F n) = pull R f F n ∘ pull R g F n := by
  funext x; exact pull_comp R f g F n x

/- English proof (translation)
Introduce `n`. Rewrite using `[shinv_pull_comp_fun]`. Conclude with `(hf n).comp (hg n)`.
-/
theorem shinv_eqv_comp {R : Type} [CommRing R] {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv R}
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n; rw [shinv_pull_comp_fun]; exact (hf n).comp (hg n)

/- English proof (translation)
Introduce `n`. Use `hfg n` as an intermediate fact. Rewrite `this` using `[shinv_pull_comp_fun]`. Conclude with `(Function.Bijective.of_comp_iff' (hf n) _).1 this`.
-/
theorem shinv_eqv_right {R : Type} [CommRing R] {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv R}
    (hf : Eqv R f F) (hfg : Eqv R (f ≫ g) F) : Eqv R g F := by
  intro n; have := hfg n; rw [shinv_pull_comp_fun] at this
  exact (Function.Bijective.of_comp_iff' (hf n) _).1 this

/- English proof (translation)
Introduce `hA9 hB2 hB3 hE2 hE3 q _ k _ _ hq X p _ _ A s hSH i`. Take `⟨hHL, hsc⟩` from `hSH`. Establish `hqA : IsUnit (q : A)` using `by simpa using hq.map s.hom`. Establish `hqκ : IsUnit (q : IsLocalRing.ResidueField A)` using `by simpa using hqA.map (IsLocalRing.residue A)`. Use `haveI : IsPurelyInseparable (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A)) := (isSepClosed_iff_isPurelyInseparable_algebraicClosure _ _).mp hsc`.

Set `res` to `Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))`. Set `alg` to `Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))))`. Set `pA` to `pullback.snd p (Spec.map s)`. Establish `h1 : Eqv _ (sch.map (pullback.fst pA res)) (tw q i)` using `hE2 q A ⟨hHL, hsc⟩ hqA pA i`. Establish `h2 : Eqv _ (sch.map (pullback.fst (pullback.snd pA res) alg)) (tw q i)` using `hInsep hA9 hB2 hB3 q _ _ hqκ (pullback.snd pA res) i`.

Set `f : k →+* AlgebraicClosure (IsLocalRing.ResidueField A)` to `(algebraMap (IsLocalRing.ResidueField A) _).comp ((IsLocalRing.residue A).comp s.hom)`. Establish `h3` using `hAlgExt hE2 hE3 q k _ f hq p i`. Establish `hf : Spec.map (CommRingCat.ofHom f) = (alg ≫ res) ≫ Spec.map s`. Simplify using `only [alg, res, ← Spec.map_comp]`. Both sides reduce to the same expression.

Establish `h3' : Eqv _ (sch.map (pullback.fst p ((alg ≫ res) ≫ Spec.map s))) (tw q i)`. Establish `key : ∀ g, g = (alg ≫ res) ≫ Spec.map s → Eqv _ (sch.map (pullback.fst p g)) (tw q i) → Eqv _ (sch.map (pullback.fst p ((alg ≫ res) ≫ Spec.map s))) (tw q i)`. Introduce `g hg h`. Substitute `hg` using the available equality. Conclude with `h`.

Conclude with `key _ hf h3`. Establish `hcomp : pullback.fst (pullback.snd pA res) alg ≫ pullback.fst pA res ≫ pullback.fst p (Spec.map s) = ((pullbackLeftPullbackSndIso pA res alg).hom ≫ (pullbackLeftPullbackSndIso p (Spec.map s) (alg ≫ res)).hom) ≫ pullback.fst p ((alg ≫ res) ≫ Spec.map s)`. Rewrite using `[Category.assoc, pullbackLeftPullbackSndIso_hom_fst p (Spec.map s) (alg ≫ res)]`. Use `erw [← Category.assoc (pullbackLeftPullbackSndIso pA res alg).hom, pullbackLeftPullbackSndIso_hom_fst pA res alg]`. Rewrite using `[Category.assoc]`.

Establish `hall : Eqv _ (sch.map (pullback.fst (pullback.snd pA res) alg) ≫ sch.map (pullback.fst pA res) ≫ sch.map (pullback.fst p (Spec.map s))) (tw q i)`. Rewrite using `[← Functor.map_comp, ← Functor.map_comp, hcomp, Functor.map_comp]`. Conclude with `shinv_eqv_comp (shinv_eqv_of_iso _ _) h3'`. Conclude with `shinv_eqv_right h1 (shinv_eqv_right h2 hall)`.
-/
theorem SHInv_of (hAlgExt : AlgExt) (hInsep : Insep) : SHInv := by
  intro hA9 hB2 hB3 hE2 hE3 q _ k _ _ hq X p _ _ A s hSH i
  obtain ⟨hHL, hsc⟩ := hSH
  have hqA : IsUnit (q : A) := by simpa using hq.map s.hom
  have hqκ : IsUnit (q : IsLocalRing.ResidueField A) := by simpa using hqA.map (IsLocalRing.residue A)
  haveI : IsPurelyInseparable (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A)) :=
    (isSepClosed_iff_isPurelyInseparable_algebraicClosure _ _).mp hsc
  let res := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  let alg := Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField A)
    (AlgebraicClosure (IsLocalRing.ResidueField A))))
  let pA := pullback.snd p (Spec.map s)
  have h1 : Eqv _ (sch.map (pullback.fst pA res)) (tw q i) := hE2 q A ⟨hHL, hsc⟩ hqA pA i
  have h2 : Eqv _ (sch.map (pullback.fst (pullback.snd pA res) alg)) (tw q i) :=
    hInsep hA9 hB2 hB3 q _ _ hqκ (pullback.snd pA res) i
  let f : k →+* AlgebraicClosure (IsLocalRing.ResidueField A) :=
    (algebraMap (IsLocalRing.ResidueField A) _).comp ((IsLocalRing.residue A).comp s.hom)
  have h3 := hAlgExt hE2 hE3 q k _ f hq p i
  have hf : Spec.map (CommRingCat.ofHom f) = (alg ≫ res) ≫ Spec.map s := by
    simp only [alg, res, ← Spec.map_comp]; rfl
  have h3' : Eqv _ (sch.map (pullback.fst p ((alg ≫ res) ≫ Spec.map s))) (tw q i) := by
    have key : ∀ g, g = (alg ≫ res) ≫ Spec.map s → Eqv _ (sch.map (pullback.fst p g)) (tw q i) →
        Eqv _ (sch.map (pullback.fst p ((alg ≫ res) ≫ Spec.map s))) (tw q i) := by
      intro g hg h; subst hg; exact h
    exact key _ hf h3
  have hcomp : pullback.fst (pullback.snd pA res) alg ≫ pullback.fst pA res ≫ pullback.fst p (Spec.map s) =
      ((pullbackLeftPullbackSndIso pA res alg).hom ≫ (pullbackLeftPullbackSndIso p (Spec.map s) (alg ≫ res)).hom) ≫
        pullback.fst p ((alg ≫ res) ≫ Spec.map s) := by
    rw [Category.assoc, pullbackLeftPullbackSndIso_hom_fst p (Spec.map s) (alg ≫ res)]
    erw [← Category.assoc (pullbackLeftPullbackSndIso pA res alg).hom, pullbackLeftPullbackSndIso_hom_fst pA res alg]
    rw [Category.assoc]
  have hall : Eqv _ (sch.map (pullback.fst (pullback.snd pA res) alg) ≫ sch.map (pullback.fst pA res) ≫
      sch.map (pullback.fst p (Spec.map s))) (tw q i) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hcomp, Functor.map_comp]
    exact shinv_eqv_comp (shinv_eqv_of_iso _ _) h3'
  exact shinv_eqv_right h1 (shinv_eqv_right h2 hall)

end LateralTheory.KummerTheory
