import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionRank

/- English proof (translation)
Set `A'` to `(Over.pullback y).obj A`. Set `K'` to `(Over.pullback y).obj K`. Set `i' : K' ⟶ A'` to `(Over.pullback y).map i`. Establish `hA' : IsAbelianScheme A'` using `Out.TLinPf.isAb_pullback y A hA`. Use `hA'.comm` as an intermediate fact.

Use `hA'.smooth` as an intermediate fact. Establish `hc' : IsUnit (c : Γ(Sp k, ⊤))`. Use `(Ne.isUnit hc).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom` as an intermediate fact. Simplify using `using this`. Establish `hTe : Etale (torsion A' c).hom` using `GrpTangent.etale_torsion A' hc'`.

Establish `hi' : i' ^ c = 1`. Establish `h` using `map_pow (Over.pullback y).homMonoidHom i c`. Rewrite `h` using `[hi, map_one]`. Conclude with `h.symm`. Take `⟨j, hj, -⟩` from `GlobalTheory.LatticeTorsion.existsUnique_torsion A' c i' hi'`.

Establish `: Mono i'` using `inferInstance`. Establish `hjm : Mono j` using `mono_of_mono_fac hj`. Establish `hjml : Mono j.left` using `inferInstanceAs (Mono ((Over.forget _).map j))`. Establish `hju : FormallyUnramified j.left` using `inferInstance`. Establish `hKu : FormallyUnramified K'.hom`.

Rewrite using `[← Over.w j]`. Conclude with `MorphismProperty.comp_mem @FormallyUnramified _ _ hju inferInstance`. Establish `: Flat K'.hom` using `by change Flat (pullback.snd K.hom y); infer_instance`. Establish `: IsFinite K'.hom` using `by change IsFinite (pullback.snd K.hom y); infer_instance`. Establish `: LocallyOfFinitePresentation K'.hom` using `inferInstance`.

Conclude with `Etale.of_formallyUnramified_of_flat K'.hom`.
-/
theorem etale_pullback_snd {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) (K : Over S) (i : K ⟶ A) (c : ℕ) [Mono i] [IsFinite K.hom]
    [Flat K.hom] (hi : i ^ c = 1) (k : Type) [Field k] (hc : (c : k) ≠ 0) (y : Sp k ⟶ S) :
    Etale (pullback.snd K.hom y) := by
  let A' := (Over.pullback y).obj A
  let K' := (Over.pullback y).obj K
  let i' : K' ⟶ A' := (Over.pullback y).map i
  have hA' : IsAbelianScheme A' := Out.TLinPf.isAb_pullback y A hA
  have := hA'.comm
  have := hA'.smooth
  have hc' : IsUnit (c : Γ(Sp k, ⊤)) := by
    have := (Ne.isUnit hc).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    simpa using this
  have hTe : Etale (torsion A' c).hom := GrpTangent.etale_torsion A' hc'
  have hi' : i' ^ c = 1 := by
    have h := map_pow (Over.pullback y).homMonoidHom i c
    rw [hi, map_one] at h
    exact h.symm
  obtain ⟨j, hj, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion A' c i' hi'
  have : Mono i' := inferInstance
  have hjm : Mono j := mono_of_mono_fac hj
  have hjml : Mono j.left := inferInstanceAs (Mono ((Over.forget _).map j))
  have hju : FormallyUnramified j.left := inferInstance
  have hKu : FormallyUnramified K'.hom := by
    rw [← Over.w j]
    exact MorphismProperty.comp_mem @FormallyUnramified _ _ hju inferInstance
  have : Flat K'.hom := by change Flat (pullback.snd K.hom y); infer_instance
  have : IsFinite K'.hom := by change IsFinite (pullback.snd K.hom y); infer_instance
  have : LocallyOfFinitePresentation K'.hom := inferInstance
  exact Etale.of_formallyUnramified_of_flat K'.hom

/- English proof (translation)
Introduce `S A _ _ hA K i c hi hfin hfl hic k _ _ hc y z`. Establish `het` using `etale_pullback_snd A hA K i c hic k hc y`. Take `⟨-, hcard⟩` from `GlobalTheory.FinEt.card_points_eq_finrank (pullback.snd K.hom y) (𝟙 (Sp k)) z`. Establish `hz : (𝟙 (Sp k) : Sp k ⟶ Sp k) z = z` using `rfl`. Rewrite `hcard` using `[hz, Scheme.Hom.finrank_pullback_snd]`.

Rewrite using `[← hcard]`. Use `Nat.card_congr { toFun := fun x => Over.homMk (x.1 ≫ pullback.fst K.hom y) (by` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(x.1 ≫ pullback.fst K.hom y) ≫ K.hom = y`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, x.2, Category.id_comp])`. Use `invFun := fun g => ⟨pullback.lift g.left (𝟙 _) (by`.

Rewrite using `[Category.id_comp]`. Conclude with `Over.w g), pullback.lift_snd _ _ _⟩`. Use `left_inv := fun x => Subtype.ext (pullback.hom_ext (pullback.lift_fst _ _ _) ((pullback.lift_snd _ _ _).trans x.2.symm))`. Use `right_inv := fun g => Over.OverMorphism.ext (pullback.lift_fst _ _ _) }`.
-/
theorem finrank_eq_card : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (K : Over S) (i : K ⟶ A) (c : ℕ), Mono i → IsFinite K.hom → Flat K.hom → i ^ c = 1 → ∀ (k : Type) [Field k] [IsAlgClosed k], (c : k) ≠ 0 → ∀ (y : Sp k ⟶ S) (z : Sp k), K.hom.finrank (y z) = Nat.card (Over.mk y ⟶ K) := by
  intro S A _ _ hA K i c hi hfin hfl hic k _ _ hc y z
  have het := etale_pullback_snd A hA K i c hic k hc y
  obtain ⟨-, hcard⟩ := GlobalTheory.FinEt.card_points_eq_finrank (pullback.snd K.hom y) (𝟙 (Sp k)) z
  have hz : (𝟙 (Sp k) : Sp k ⟶ Sp k) z = z := rfl
  rw [hz, Scheme.Hom.finrank_pullback_snd] at hcard
  rw [← hcard]
  refine Nat.card_congr
    { toFun := fun x => Over.homMk (x.1 ≫ pullback.fst K.hom y) (by
        change (x.1 ≫ pullback.fst K.hom y) ≫ K.hom = y
        rw [Category.assoc, pullback.condition, ← Category.assoc, x.2, Category.id_comp])
      invFun := fun g => ⟨pullback.lift g.left (𝟙 _) (by
        rw [Category.id_comp]; exact Over.w g), pullback.lift_snd _ _ _⟩
      left_inv := fun x => Subtype.ext (pullback.hom_ext (pullback.lift_fst _ _ _)
        ((pullback.lift_snd _ _ _).trans x.2.symm))
      right_inv := fun g => Over.OverMorphism.ext (pullback.lift_fst _ _ _) }

end GlobalTheory.TorsionRank
