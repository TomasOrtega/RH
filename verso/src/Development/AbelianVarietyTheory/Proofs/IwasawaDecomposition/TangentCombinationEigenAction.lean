import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb

noncomputable section

namespace GlobalTheory.FlagEmb

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules.
-/
theorem det_cell_eq_one {T : Type} {m : T → ℕ} {S : Type} [CommRing S] (y : CellVar m → S) (τ : T) :
    (Matrix.of fun i j => cell y τ i j).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [cell]
  · intro i j hij
    have h : i < j := hij
    simp [cell, h.ne, not_lt.2 h.le]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X) {R : Type} [CommRing R] {x : Sp R ⟶ X}

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Substitute using the available equality. A detailed English derivation is pending.
-/
theorem eig_of_comb {n : ℕ} (u : Fin n → Tn t R) (cf : Fin n → R) (w : Tn t R) (a : 𝓞 E) (r : R)
    (hu : ∀ j, IsTanAtG t x (u j) ∧ u j ≫ (t.act.act a).left = spMap (epsMul r) ≫ u j)
    (h : IsCombAtG t x u cf w) : w ≫ (t.act.act a).left = spMap (epsMul r) ≫ w := by
  have e := (isCombAtG_iff t x (fun j => ovT (hu j).1) cf w).1 h
  have := t.act.hom a
  have h2 := combT_eig x (fun j => ovT (hu j).1) (t.act.act a) r
    (fun j => Over.OverMorphism.ext (hu j).2) cf
  subst e
  exact congrArg (fun φ => φ.left) h2

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isCombAtG_perm {n : ℕ} {u : Fin n → Tn t R} (hu : ∀ j, IsTanAtG t x (u j)) (σ : Equiv.Perm (Fin n))
    (a : Fin n → R) (w : Tn t R) :
    IsCombAtG t x (fun i => u (σ i)) (fun i => a (σ i)) w ↔ IsCombAtG t x u a w := by
  have e : combT x (fun j => ovT (hu (σ j))) (fun i => a (σ i)) = combT x (fun j => ovT (hu j)) a :=
    Equiv.prod_comp σ (fun j => smT x (a j) (ovT (hu j)))
  refine (isCombAtG_iff t x (fun j => ovT (hu (σ j))) _ w).trans ?_
  rw [e]
  exact (isCombAtG_iff t x (fun j => ovT (hu j)) _ w).symm

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Substitute using the available equality. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem existsUnique_comb_change {n : ℕ} {e u : Fin n → Tn t R} (he : ∀ j, IsTanAtG t x (e j))
    (K : Matrix (Fin n) (Fin n) R) (hK : IsUnit K.det) (hu : ∀ j, IsCombAtG t x e (fun i => K i j) (u j))
    {w : Tn t R} (hw : IsTanAtG t x w) (hb : ∃! a, IsCombAtG t x e a w) : ∃! a, IsCombAtG t x u a w := by
  have hU : u = fun j => (combT x (fun i => ovT (he i)) (fun i => K i j)).left :=
    funext fun j => ((isCombAtG_iff t x (fun i => ovT (he i)) _ _).1 (hu j)).symm
  subst hU
  have h2 : ∃! a : Fin n → R, ovT hw = combT x (fun j => ovT (he j)) a := by
    obtain ⟨a, ha, hq⟩ := hb
    exact ⟨a, Over.OverMorphism.ext ((isCombAtG_iff t x (fun j => ovT (he j)) _ _).1 ha).symm,
      fun b hb => hq b ((isCombAtG_iff t x (fun j => ovT (he j)) _ _).2 (by rw [← hb]; rfl))⟩
  obtain ⟨a, ha, hq⟩ := reframe_basis x _ (fun j => smT_zero_ovT _) K hK _ h2
  exact ⟨a, (isCombAtG_iff t x _ _ _).2 (by rw [← ha]; rfl),
    fun b hb => hq b (Over.OverMorphism.ext ((isCombAtG_iff t x _ _ _).1 hb).symm)⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem isFrame_cell {Dw : Datum H} {l : Level H} {c : Coeff l} (f : c.F →+* R) (e u : Vecs Dw t R) (w : Pm Dw.mult)
    (y : CellVar Dw.mult → R) (he : GlobalTheory.LocM.IsFrame t f x e)
    (hu : ∀ τ j, IsCombAtG t x (fun i => e τ (w τ i)) (fun i => cell y τ i j) (u τ j)) :
    GlobalTheory.LocM.IsFrame t f x u := by
  refine ⟨fun τ j => ⟨comb_tan t (fun i => (he.1 τ (w τ i)).1) (hu τ j), fun a => ?_⟩, fun τ v hv hE => ?_⟩
  · exact eig_of_comb t _ _ _ a _ (fun i => ⟨(he.1 τ (w τ i)).1, (he.1 τ (w τ i)).2 a⟩) (hu τ j)
  · refine existsUnique_comb_change t (fun i => (he.1 τ (w τ i)).1) (Matrix.of fun i j => cell y τ i j)
      (by rw [det_cell_eq_one]; exact isUnit_one) (hu τ) hv ?_
    obtain ⟨a, ha, hq⟩ := he.2 τ v hv hE
    refine ⟨fun i => a (w τ i), (isCombAtG_perm t (fun i => (he.1 τ i).1) (w τ) a v).2 ha, fun b hb => ?_⟩
    have h1 := hq (fun i => b ((w τ).symm i))
      ((isCombAtG_perm t (fun i => (he.1 τ i).1) (w τ) _ v).1 (by simpa using hb))
    funext i
    rw [← h1]
    simp

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem eig_comb_and_frame_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X)
    (R : Type) [CommRing R] (x : Sp R ⟶ X),
    (∀ (n : ℕ) (u : Fin n → Tn t R) (cf : Fin n → R) (w : Tn t R) (a : 𝓞 E) (r : R),
      (∀ j, IsTanAtG t x (u j) ∧ u j ≫ (t.act.act a).left = spMap (epsMul r) ≫ u j) → IsCombAtG t x u cf w →
        w ≫ (t.act.act a).left = spMap (epsMul r) ≫ w) ∧
    ∀ (f : c.F →+* R) (e u : Vecs Dw t R) (w : Pm Dw.mult) (y : CellVar Dw.mult → R), GlobalTheory.LocM.IsFrame t f x e →
      (∀ τ j, IsCombAtG t x (fun i => e τ (w τ i)) (fun i => cell y τ i j) (u τ j)) → GlobalTheory.LocM.IsFrame t f x u :=
  fun _ _ _ _ _ _ _ _ _ t _ _ _ =>
    ⟨fun _ u cf w a r hu h => eig_of_comb t u cf w a r hu h, fun f e u w y he hu => isFrame_cell t f e u w y he hu⟩

end GlobalTheory.FlagEmb
