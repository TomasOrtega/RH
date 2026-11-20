import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFibFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PChart

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

namespace UpperTheory.Gal.G3

/- English proof (translation)
Establish `h` using `UpperTheory.Gal.TranscendenceTraces.fibFin_of UpperTheory.Gal.TranscendenceTraces.chart_of s Ω x`. Conclude with `h.to_subtype`.
-/
private theorem fibre_finite {Y Z : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] (Ω : Type) [Field Ω] (x : sp Ω ⟶ Z) :
    Finite {y : sp Ω ⟶ Y // y ≫ s = x} := by
  have h := UpperTheory.Gal.TranscendenceTraces.fibFin_of UpperTheory.Gal.TranscendenceTraces.chart_of s Ω x
  exact h.to_subtype

/- English proof (translation)
Conclude with `Flat.epi_of_flat_of_surjective x`.
-/
private theorem epi_of_field {Ω Ω' : Type} [Field Ω] [Field Ω'] (x : sp Ω' ⟶ sp Ω) : Epi x := by
  exact Flat.epi_of_flat_of_surjective x

/- English proof (translation)
Use `⟨AlgebraicClosure (Z.residueField z), inferInstance, inferInstance, Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) (AlgebraicClosure (Z.residueField z)))) ≫ Z.fromSpecResidueField z, ?_⟩` and prove the remaining obligations. Conclude with `Scheme.fromSpecResidueField_apply z _`.
-/
private theorem point_over {Z : Scheme.{0}} (z : Z) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (x : sp Ω ⟶ Z), x (IsLocalRing.closedPoint Ω) = z := by
  refine ⟨AlgebraicClosure (Z.residueField z), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) (AlgebraicClosure (Z.residueField z)))) ≫
      Z.fromSpecResidueField z, ?_⟩
  exact Scheme.fromSpecResidueField_apply z _

end UpperTheory.Gal.G3

/- English proof (translation)
Establish `hfin` using `UpperTheory.Gal.G3.fibre_finite s Ω (x ≫ c)`. Set `f : Fin d → {y : UpperTheory.Gal.G3.sp Ω ⟶ Y // y ≫ s = x ≫ c}` to `fun j => ⟨x ≫ σ j, by rw [Category.assoc, hσ]⟩`. Establish `hf : Function.Injective f`. Introduce `i j hij`. Conclude with `hinj Ω x (congrArg Subtype.val hij)`.

Establish `hb` using `hf.bijective_of_nat_card_le (by rw [hd Ω (x ≫ c), Nat.card_eq_fintype_card, Fintype.card_fin])`. Take `⟨j, hj⟩` from `hb.2 ⟨y, hy⟩`. Conclude with `⟨j, congrArg Subtype.val hj⟩`.
-/
private theorem exists_comp_sigma_eq_of_comp_eq_comp {Z Y W : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] {d : ℕ}
    (hd : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ Z),
      Nat.card {y // y ≫ s = x} = d)
    (c : W ⟶ Z) (σ : Fin d → (W ⟶ Y)) (hσ : ∀ j, σ j ≫ s = c)
    (hinj : ∀ (Ω : Type) [Field Ω] (x : UpperTheory.Gal.G3.sp Ω ⟶ W), Function.Injective fun j => x ≫ σ j)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : UpperTheory.Gal.G3.sp Ω ⟶ W) (y : UpperTheory.Gal.G3.sp Ω ⟶ Y)
    (hy : y ≫ s = x ≫ c) :
    ∃ j, x ≫ σ j = y := by
  have hfin := UpperTheory.Gal.G3.fibre_finite s Ω (x ≫ c)
  let f : Fin d → {y : UpperTheory.Gal.G3.sp Ω ⟶ Y // y ≫ s = x ≫ c} :=
    fun j => ⟨x ≫ σ j, by rw [Category.assoc, hσ]⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact hinj Ω x (congrArg Subtype.val hij)
  have hb := hf.bijective_of_nat_card_le (by rw [hd Ω (x ≫ c), Nat.card_eq_fintype_card, Fintype.card_fin])
  obtain ⟨j, hj⟩ := hb.2 ⟨y, hy⟩
  exact ⟨j, congrArg Subtype.val hj⟩

/- English proof (translation)
Introduce `hS hO Z Y s d hF`. Take `⟨hfin, het, hd⟩` from `hF`. Take `⟨W, c, σ, hcf, hce, hσ, hinj, huniv⟩` from `hO s d`. Establish `hex : ∀ g : Equiv.Perm (Fin d), ∃! w : W ⟶ W, w ≫ c = c ∧ ∀ j, w ≫ σ j = σ (g j)`. Introduce `g`.

Use `huniv W c (fun j => σ (g j)) (fun j => hσ (g j)) ?_` and prove the remaining obligations. Introduce `Ω _ x i j hij`. Conclude with `g.injective (hinj Ω x hij)`. Use `choose a ha using fun g => (hex g).exists`. Establish `hone : a 1 = 𝟙 W` using `(hex 1).unique (ha 1) ⟨Category.id_comp c, fun j => by simp⟩`.

Establish `hmul : ∀ g h, a (g * h) = a g ≫ a h`. Introduce `g h`. Use `(hex (g * h)).unique (ha (g * h)) ⟨?_, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, (ha h).1, (ha g).1]`. Rewrite using `[Category.assoc, (ha h).2 j, (ha g).2 (h j)]`.

Both sides reduce to the same expression. Establish `hspl : Splits s c σ`. Use `hS s c (Fin d) σ hσ ?_` and prove the remaining obligations. Introduce `Ω _ _ x y hy`. Take `⟨j, hj⟩` from `exists_comp_sigma_eq_of_comp_eq_comp s hd c σ hσ hinj Ω x y hy`.

Conclude with `⟨j, hj, fun j' hj' => hinj Ω x (hj'.trans hj.symm)⟩`. Establish `hsur : Surjective c`. Prove the components needed by the constructor for the conclusion. Introduce `z`. Take `⟨Ω, _, _, x, hx⟩` from `UpperTheory.Gal.G3.point_over z`.

Establish `hfF` using `UpperTheory.Gal.G3.fibre_finite s Ω x`. Establish `hcard : Nat.card {y : UpperTheory.Gal.G3.sp Ω ⟶ Y // y ≫ s = x} = d` using `hd Ω x`. Set `e` to `Finite.equivFin {y : UpperTheory.Gal.G3.sp Ω ⟶ Y // y ≫ s = x}`. Set `yy : Fin d → (UpperTheory.Gal.G3.sp Ω ⟶ Y)` to `fun j => (e.symm (Fin.cast hcard.symm j)).1`. Establish `hyy : ∀ j, yy j ≫ s = x` using `fun j => (e.symm (Fin.cast hcard.symm j)).2`.

Establish `hinj' : ∀ (Ω' : Type) [Field Ω'] (x' : UpperTheory.Gal.G3.sp Ω' ⟶ UpperTheory.Gal.G3.sp Ω), Function.Injective fun j => x' ≫ yy j`. Introduce `Ω' _ x' i j hij`. Use `haveI := UpperTheory.Gal.G3.epi_of_field x'`. Establish `h1 : yy i = yy j` using `(cancel_epi x').1 hij`. Establish `h2` using `Subtype.val_injective h1`.

Conclude with `Fin.cast_injective _ (e.symm.injective h2)`. Take `⟨w, ⟨hw, _⟩, _⟩` from `huniv (UpperTheory.Gal.G3.sp Ω) x yy hyy hinj'`. Use `⟨w (IsLocalRing.closedPoint Ω), ?_⟩` and prove the remaining obligations. Rewrite using `[← hx, ← hw]`. Both sides reduce to the same expression.

Establish `hgal : Splits c c a`. Use `hS c c (Equiv.Perm (Fin d)) a (fun g => (ha g).1) ?_` and prove the remaining obligations. Introduce `Ω _ _ x y hy`. Establish `hpt : ∀ j, ∃ k, x ≫ σ k = y ≫ σ j`. Introduce `j`.

Conclude with `exists_comp_sigma_eq_of_comp_eq_comp s hd c σ hσ hinj Ω x (y ≫ σ j) (by rw [Category.assoc, hσ, hy])`. Use `choose p hp using hpt`. Establish `hpi : Function.Injective p`. Introduce `i j hij`. Apply `hinj Ω y` to reduce the goal to its premises.

Simplify using `only`. Rewrite using `[← hp i, ← hp j, hij]`. Set `g` to `Equiv.ofBijective p (Finite.injective_iff_bijective.1 hpi)`. Establish `hinjy : ∀ (Ω' : Type) [Field Ω'] (x' : UpperTheory.Gal.G3.sp Ω' ⟶ UpperTheory.Gal.G3.sp Ω), Function.Injective fun j => x' ≫ (y ≫ σ j)`. Introduce `Ω' _ x' i j hij`.

Apply `hinj Ω' (x' ≫ y)` to reduce the goal to its premises. Simplify `hij` using `only [Category.assoc]`. Use `⟨g, ?_, ?_⟩` and prove the remaining obligations. Use `(huniv (UpperTheory.Gal.G3.sp Ω) (x ≫ c) (fun j => y ≫ σ j) (fun j => by rw [Category.assoc, hσ, hy]) hinjy).unique ⟨?_, fun j => ?_⟩ ⟨hy, fun j => rfl⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, (ha g).1]`.

Rewrite using `[Category.assoc, (ha g).2 j]`. Conclude with `hp j`. Introduce `g' hg'`. Use `Equiv.ext fun j => ?_` and prove the remaining obligations. Apply `hinj Ω x` to reduce the goal to its premises.

Simplify using `only`. Rewrite using `[← (ha g').2 j, ← Category.assoc, hg', ← hp j]`. Both sides reduce to the same expression. Conclude with `⟨W, c, Equiv.Perm (Fin d), inferInstance, inferInstance, a, σ, ⟨hcf, hce, hsur, hone, hmul, hgal⟩, hspl⟩`.
-/
theorem UpperTheory.Gal.G3.pGalClosD :
    SplitsPts → OrdEx → GalClosD := by
  intro hS hO Z Y s d hF
  obtain ⟨hfin, het, hd⟩ := hF
  obtain ⟨W, c, σ, hcf, hce, hσ, hinj, huniv⟩ := hO s d
  have hex : ∀ g : Equiv.Perm (Fin d), ∃! w : W ⟶ W, w ≫ c = c ∧ ∀ j, w ≫ σ j = σ (g j) := by
    intro g
    refine huniv W c (fun j => σ (g j)) (fun j => hσ (g j)) ?_
    intro Ω _ x i j hij
    exact g.injective (hinj Ω x hij)
  choose a ha using fun g => (hex g).exists
  have hone : a 1 = 𝟙 W :=
    (hex 1).unique (ha 1) ⟨Category.id_comp c, fun j => by simp⟩
  have hmul : ∀ g h, a (g * h) = a g ≫ a h := by
    intro g h
    refine (hex (g * h)).unique (ha (g * h)) ⟨?_, fun j => ?_⟩
    · rw [Category.assoc, (ha h).1, (ha g).1]
    · rw [Category.assoc, (ha h).2 j, (ha g).2 (h j)]
      rfl
  have hspl : Splits s c σ := by
    refine hS s c (Fin d) σ hσ ?_
    intro Ω _ _ x y hy
    obtain ⟨j, hj⟩ := exists_comp_sigma_eq_of_comp_eq_comp s hd c σ hσ hinj Ω x y hy
    exact ⟨j, hj, fun j' hj' => hinj Ω x (hj'.trans hj.symm)⟩
  have hsur : Surjective c := by
    constructor
    intro z
    obtain ⟨Ω, _, _, x, hx⟩ := UpperTheory.Gal.G3.point_over z
    have hfF := UpperTheory.Gal.G3.fibre_finite s Ω x
    have hcard : Nat.card {y : UpperTheory.Gal.G3.sp Ω ⟶ Y // y ≫ s = x} = d := hd Ω x
    let e := Finite.equivFin {y : UpperTheory.Gal.G3.sp Ω ⟶ Y // y ≫ s = x}
    let yy : Fin d → (UpperTheory.Gal.G3.sp Ω ⟶ Y) := fun j => (e.symm (Fin.cast hcard.symm j)).1
    have hyy : ∀ j, yy j ≫ s = x := fun j => (e.symm (Fin.cast hcard.symm j)).2
    have hinj' : ∀ (Ω' : Type) [Field Ω'] (x' : UpperTheory.Gal.G3.sp Ω' ⟶ UpperTheory.Gal.G3.sp Ω),
        Function.Injective fun j => x' ≫ yy j := by
      intro Ω' _ x' i j hij
      haveI := UpperTheory.Gal.G3.epi_of_field x'
      have h1 : yy i = yy j := (cancel_epi x').1 hij
      have h2 := Subtype.val_injective h1
      exact Fin.cast_injective _ (e.symm.injective h2)
    obtain ⟨w, ⟨hw, _⟩, _⟩ := huniv (UpperTheory.Gal.G3.sp Ω) x yy hyy hinj'
    refine ⟨w (IsLocalRing.closedPoint Ω), ?_⟩
    rw [← hx, ← hw]
    rfl
  have hgal : Splits c c a := by
    refine hS c c (Equiv.Perm (Fin d)) a (fun g => (ha g).1) ?_
    intro Ω _ _ x y hy
    have hpt : ∀ j, ∃ k, x ≫ σ k = y ≫ σ j := by
      intro j
      exact exists_comp_sigma_eq_of_comp_eq_comp s hd c σ hσ hinj Ω x (y ≫ σ j) (by rw [Category.assoc, hσ, hy])
    choose p hp using hpt
    have hpi : Function.Injective p := by
      intro i j hij
      apply hinj Ω y
      simp only
      rw [← hp i, ← hp j, hij]
    let g := Equiv.ofBijective p (Finite.injective_iff_bijective.1 hpi)
    have hinjy : ∀ (Ω' : Type) [Field Ω'] (x' : UpperTheory.Gal.G3.sp Ω' ⟶ UpperTheory.Gal.G3.sp Ω),
        Function.Injective fun j => x' ≫ (y ≫ σ j) := by
      intro Ω' _ x' i j hij
      apply hinj Ω' (x' ≫ y)
      simpa only [Category.assoc] using hij
    refine ⟨g, ?_, ?_⟩
    · refine (huniv (UpperTheory.Gal.G3.sp Ω) (x ≫ c) (fun j => y ≫ σ j)
        (fun j => by rw [Category.assoc, hσ, hy]) hinjy).unique ⟨?_, fun j => ?_⟩ ⟨hy, fun j => rfl⟩
      · rw [Category.assoc, (ha g).1]
      · rw [Category.assoc, (ha g).2 j]
        exact hp j
    · intro g' hg'
      refine Equiv.ext fun j => ?_
      apply hinj Ω x
      simp only
      rw [← (ha g').2 j, ← Category.assoc, hg', ← hp j]
      rfl
  exact ⟨W, c, Equiv.Perm (Fin d), inferInstance, inferInstance, a, σ,
    ⟨hcf, hce, hsur, hone, hmul, hgal⟩, hspl⟩
