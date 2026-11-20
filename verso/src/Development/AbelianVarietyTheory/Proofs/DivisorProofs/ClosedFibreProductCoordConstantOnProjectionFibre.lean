import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFactorResidueFieldOfClosedPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreProductCoordinateIndependentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ M G' _ E N fU l hl hf hπ O h hyp z z' hzz hcl`. Establish `hzz' : (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) z = (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) z'`. Rewrite using `[Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]`. Conclude with `hzz`. Take `⟨w, hw, hw'⟩` from `Scheme.Pullback.exists_preimage_pullback z z' hzz'`.

Set `P` to `pullback (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π)`. Set `t : Sp (P.residueField w) ⟶ O.toScheme` to `P.fromSpecResidueField w ≫ pullback.fst _ _`. Set `t' : Sp (P.residueField w) ⟶ O.toScheme` to `P.fromSpecResidueField w ≫ pullback.snd _ _`. Establish `ht : ∀ u, t u = z` using `fun u => by show (P.fromSpecResidueField w ≫ pullback.fst _ _) u = z`. Rewrite using `[Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]`.

Conclude with `hw`. Establish `ht' : ∀ u, t' u = z'` using `fun u => by show (P.fromSpecResidueField w ≫ pullback.snd _ _) u = z'`. Rewrite using `[Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]`. Conclude with `hw'`. Establish `hc₀ : t' ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π = t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π` using `by show (P.fromSpecResidueField w ≫ pullback.snd _ _) ≫ (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) = (P.fromSpecResidueField w ≫ pullback.fst _ _) ≫ (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π)`.

Rewrite using `[Category.assoc, Category.assoc, pullback.condition]`. Take `⟨κ, hκ⟩` from `GlobalTheory.T.exists_spMap_residueField_of_forall_eq_closedPoint R (P.residueField w) ((t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (N.U ⊗ N.U).hom) (fun u => by`. Rewrite using `[Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ht]`. Conclude with `hcl)`. Establish `key : ∀ (t₁ : Sp (P.residueField w) ⟶ O.toScheme), t₁ ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π = t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π → ∃ (s : Sp (P.residueField w) ⟶ M.S) (x y : Over.mk s ⟶ G'), s ≫ M.π = spMap (κ.comp (residue R)) ∧ N.Pt s ((t ≫ O.ι ≫ pullback.fst (N.U ⊗ …`.

Introduce `t₁ e`. Establish `hs : (t₁ ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π) ≫ M.π = (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (N.U ⊗ N.U).hom`. Rewrite using `[← e, Category.assoc, Category.assoc, Category.assoc, Category.assoc, pullback.condition]`. Establish `ea : ((t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (fst N.U N.U).left) ≫ N.U.hom = (t₁ ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π) ≫ M.π`. Rewrite using `[hs, Category.assoc, Over.w]`.

Establish `eb : ((t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (snd N.U N.U).left) ≫ N.U.hom = (t₁ ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π) ≫ M.π`. Rewrite using `[hs, Category.assoc, Over.w]`. Set `x : Over.mk (t₁ ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π) ⟶ G'` to `Over.homMk (pullback.lift _ _ ea ≫ N.u) (by`. Rewrite using `[Category.assoc, N.u_over, pullback.lift_snd]`. Use the proof step `rfl)`.

Set `y : Over.mk (t₁ ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π) ⟶ G'` to `Over.homMk (pullback.lift _ _ eb ≫ N.u) (by`. Rewrite using `[Category.assoc, N.u_over, pullback.lift_snd]`. Use the proof step `rfl)`. Use `⟨_, x, y, hs.trans hκ, ⟨pullback.lift _ _ ea, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, rfl⟩, ⟨pullback.lift _ _ eb, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, rfl⟩, hyp _ t₁ _ x y rfl ?_ ?_⟩` and prove the remaining obligations. Use `⟨pullback.lift _ _ ea, ?_, pullback.lift_snd _ _ _, rfl⟩` and prove the remaining obligations.

Rewrite using `[pullback.lift_fst, ← e]`. Simplify using `only [Category.assoc]`. Use `⟨pullback.lift _ _ eb, ?_, pullback.lift_snd _ _ _, rfl⟩` and prove the remaining obligations. Rewrite using `[pullback.lift_fst, ← e]`. Simplify using `only [Category.assoc]`.

Take `⟨s, x, y, hs, hx, hy, hxy⟩` from `key t rfl`. Take `⟨s', x', y', hs', hx', hy', hxy'⟩` from `key t' hc₀`. Establish `e` using `GlobalTheory.T.closedFibre_product_coordinate_independent R M G' E N fU l hl hf hπ (P.residueField w) κ s s' _ _ (t ≫ h) (t' ≫ h) x y x' y' hs hs' hx hy hxy hx' hy' hxy'`. Use `congrArg (fun g : Sp (P.residueField w) ⟶ N.U.left => g (IsLocalRing.closedPoint _)) e` as an intermediate fact. Rewrite using `[← ht (IsLocalRing.closedPoint _), ← ht' (IsLocalRing.closedPoint _)]`.

Use `first`. Consider the case `exact this`. Consider the case `simpa only [Scheme.Hom.comp_apply] using this`. Consider the case `simpa only [Scheme.comp_base_apply] using this`.
-/
theorem Near.closed_fibre_constant : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → Surjective M.π → ∀ (O : (pullback (N.U ⊗ N.U).hom M.π).Opens) (h : O.toScheme ⟶ N.U.left), (∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (s : T ⟶ M.S) (x y : Over.mk s ⟶ G'), t ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π = s → N.Pt s (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (fst N.U N.U).left) x.left → N.Pt s (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (snd N.U N.U).left) y.left → N.Pt s (t ≫ h) (x * y).left) → ∀ z z' : O.toScheme, pullback.fst (N.U ⊗ N.U).hom M.π (O.ι z) = pullback.fst (N.U ⊗ N.U).hom M.π (O.ι z') → (N.U ⊗ N.U).hom (pullback.fst (N.U ⊗ N.U).hom M.π (O.ι z)) = closedPoint R → h z = h z' := by
  intro R _ _ _ M G' _ E N fU l hl hf hπ O h hyp z z' hzz hcl
  have hzz' : (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) z = (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) z' := by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]; exact hzz
  obtain ⟨w, hw, hw'⟩ := Scheme.Pullback.exists_preimage_pullback z z' hzz'
  let P := pullback (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π)
  let t : Sp (P.residueField w) ⟶ O.toScheme := P.fromSpecResidueField w ≫ pullback.fst _ _
  let t' : Sp (P.residueField w) ⟶ O.toScheme := P.fromSpecResidueField w ≫ pullback.snd _ _
  have ht : ∀ u, t u = z := fun u => by
    show (P.fromSpecResidueField w ≫ pullback.fst _ _) u = z
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]; exact hw
  have ht' : ∀ u, t' u = z' := fun u => by
    show (P.fromSpecResidueField w ≫ pullback.snd _ _) u = z'
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]; exact hw'
  have hc₀ : t' ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π = t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π := by
    show (P.fromSpecResidueField w ≫ pullback.snd _ _) ≫ (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) =
      (P.fromSpecResidueField w ≫ pullback.fst _ _) ≫ (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π)
    rw [Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_spMap_residueField_of_forall_eq_closedPoint R (P.residueField w)
    ((t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (N.U ⊗ N.U).hom) (fun u => by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ht]; exact hcl)
  have key : ∀ (t₁ : Sp (P.residueField w) ⟶ O.toScheme),
      t₁ ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π = t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π →
      ∃ (s : Sp (P.residueField w) ⟶ M.S) (x y : Over.mk s ⟶ G'), s ≫ M.π = spMap (κ.comp (residue R)) ∧
        N.Pt s ((t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (fst N.U N.U).left) x.left ∧
        N.Pt s ((t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (snd N.U N.U).left) y.left ∧
        N.Pt s (t₁ ≫ h) (x * y).left := by
    intro t₁ e
    have hs : (t₁ ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π) ≫ M.π =
        (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (N.U ⊗ N.U).hom := by
      rw [← e, Category.assoc, Category.assoc, Category.assoc, Category.assoc, pullback.condition]
    have ea : ((t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (fst N.U N.U).left) ≫ N.U.hom =
        (t₁ ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π) ≫ M.π := by
      rw [hs, Category.assoc, Over.w]
    have eb : ((t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (snd N.U N.U).left) ≫ N.U.hom =
        (t₁ ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π) ≫ M.π := by
      rw [hs, Category.assoc, Over.w]
    let x : Over.mk (t₁ ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π) ⟶ G' :=
      Over.homMk (pullback.lift _ _ ea ≫ N.u) (by
        rw [Category.assoc, N.u_over, pullback.lift_snd]; rfl)
    let y : Over.mk (t₁ ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π) ⟶ G' :=
      Over.homMk (pullback.lift _ _ eb ≫ N.u) (by
        rw [Category.assoc, N.u_over, pullback.lift_snd]; rfl)
    refine ⟨_, x, y, hs.trans hκ, ⟨pullback.lift _ _ ea, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, rfl⟩,
      ⟨pullback.lift _ _ eb, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, rfl⟩, hyp _ t₁ _ x y rfl ?_ ?_⟩
    · refine ⟨pullback.lift _ _ ea, ?_, pullback.lift_snd _ _ _, rfl⟩
      rw [pullback.lift_fst, ← e]; simp only [Category.assoc]
    · refine ⟨pullback.lift _ _ eb, ?_, pullback.lift_snd _ _ _, rfl⟩
      rw [pullback.lift_fst, ← e]; simp only [Category.assoc]
  obtain ⟨s, x, y, hs, hx, hy, hxy⟩ := key t rfl
  obtain ⟨s', x', y', hs', hx', hy', hxy'⟩ := key t' hc₀
  have e := GlobalTheory.T.closedFibre_product_coordinate_independent R M G' E N fU l hl hf hπ (P.residueField w) κ s s' _ _ (t ≫ h) (t' ≫ h) x y x' y'
    hs hs' hx hy hxy hx' hy' hxy'
  have := congrArg (fun g : Sp (P.residueField w) ⟶ N.U.left => g (IsLocalRing.closedPoint _)) e
  rw [← ht (IsLocalRing.closedPoint _), ← ht' (IsLocalRing.closedPoint _)]
  first
    | exact this
    | simpa only [Scheme.Hom.comp_apply] using this
    | simpa only [Scheme.comp_base_apply] using this

end GlobalTheory.Mum
