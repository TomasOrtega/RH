import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.CechLine

variable {X : Scheme.{0}} (D : LineData X)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem u_self {V : Scheme.{0}} (a : V ⟶ D.Y) (h : a ≫ D.f = a ≫ D.f) : D.u a a h = 1 := by
  have h2 : D.u a a h * D.u a a h = D.u a a h * 1 := by
    rw [mul_one]
    exact D.coc a a a h h
  exact mul_left_cancel h2

/- English proof (translation)
Substitute using the available equality. Substitute using the available equality. Both sides reduce to the same expression.
-/
theorem u_congr {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y} (ha : a = a') (hb : b = b')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) : D.u a b h = D.u a' b' h' := by
  subst ha
  subst hb
  rfl

def lineFun {V : Scheme.{0}} {k : ℕ} (y : Fin (k + 1) → (V ⟶ D.Y)) (hy : ∀ i j, y i ≫ D.f = y j ≫ D.f) :
    ComposableArrows (SingleObj (GL (Fin 1) Γ(V, ⊤))) k where
  obj _ := SingleObj.star _
  map {i j} _ := Matrix.GeneralLinearGroup.scalar (Fin 1) (D.u (y i) (y j) (hy i j))
  map_id i := by rw [u_self]; exact map_one (Matrix.GeneralLinearGroup.scalar (Fin 1))
  map_comp {i j l} _ _ := by
    rw [SingleObj.comp_as_mul]
    refine Eq.trans ?_ (map_mul (Matrix.GeneralLinearGroup.scalar (Fin 1)) _ _)
    rw [mul_comm, D.coc]

variable {D}

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_pts (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) :
    ∃ y : Fin (k + 1) → (U ⟶ D.Y), ∃ x h, z = cechPt D.f k x y h := by
  obtain ⟨x, y, h, hz⟩ := (hC D.Y X D.f k U).1 z
  exact ⟨y, x, h, hz⟩

def pts (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) : Fin (k + 1) → (U ⟶ D.Y) :=
  (exists_pts hC z).choose

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pts_spec (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) :
    ∃ x h, z = cechPt D.f k x (pts hC z) h := by
  exact (exists_pts hC z).choose_spec

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem pts_eq (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U) (i j : Fin (k + 1)) :
    pts hC z i ≫ D.f = pts hC z j ≫ D.f := by
  obtain ⟨x, h, -⟩ := pts_spec hC z
  exact (h i).trans (h j).symm

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem pts_cechPt (hC : CechPt) {k : ℕ} {U : Scheme.{0}} (x : U ⟶ X) (y : Fin (k + 1) → (U ⟶ D.Y))
    (h : ∀ i, y i ≫ D.f = x) : pts hC (cechPt D.f k x y h) = y := by
  obtain ⟨x', h', hz⟩ := pts_spec hC (cechPt D.f k x y h)
  exact ((hC D.Y X D.f k U).2.1 _ _ _ _ _ _ hz).symm

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem pts_res (hC : CechPt) {k : ℕ} {U V : Scheme.{0}} (g : V ⟶ U) (z : Sx (cech D.f) k U) (i : Fin (k + 1)) :
    pts hC (Sx.res g z) i = g ≫ pts hC z i := by
  obtain ⟨x, h, hz⟩ := pts_spec hC z
  have e := ((hC D.Y X D.f k U).2.2 x (pts hC z) h).2.1 V g
  rw [← hz] at e
  rw [e, pts_cechPt]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem pts_along (hC : CechPt) {k p : ℕ} {U : Scheme.{0}} (z : Sx (cech D.f) k U)
    (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk k) (i : Fin (p + 1)) :
    pts hC (Sx.along z θ) i = pts hC z (θ.toOrderHom i) := by
  obtain ⟨x, h, hz⟩ := pts_spec hC z
  have e := ((hC D.Y X D.f k U).2.2 x (pts hC z) h).2.2 p θ
  rw [← hz] at e
  rw [e, pts_cechPt]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem scalar_map {A B : CommRingCat.{0}} (f : A ⟶ B) (u : (A : Type)ˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.map f.hom.toMonoidHom u) =
      Matrix.GeneralLinearGroup.map f.hom (Matrix.GeneralLinearGroup.scalar (Fin 1) u) := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

variable (D) in
/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem lineFun_res {U V : Scheme.{0}} {k : ℕ} (g : V ⟶ U) (y : Fin (k + 1) → (U ⟶ D.Y))
    (hy : ∀ i j, y i ≫ D.f = y j ≫ D.f) (y' : Fin (k + 1) → (V ⟶ D.Y))
    (hy' : ∀ i j, y' i ≫ D.f = y' j ≫ D.f) (e : ∀ i, y' i = g ≫ y i) :
    lineFun D y' hy' = (show Fin (k + 1) ⥤ (glCat 1).obj Γ(U, ⊤) from lineFun D y hy) ⋙
      ((glCat 1).map (Scheme.Γ.map g.op)).toFunctor := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j _ => ?_)
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  change Matrix.GeneralLinearGroup.scalar (Fin 1) (D.u (y' i) (y' j) (hy' i j)) =
    Matrix.GeneralLinearGroup.map (Scheme.Γ.map g.op).hom
      (Matrix.GeneralLinearGroup.scalar (Fin 1) (D.u (y i) (y j) (hy i j)))
  rw [← scalar_map]
  congr 1
  rw [u_congr D (e i) (e j) (hy' i j) (by rw [Category.assoc, Category.assoc, hy i j]),
    D.nat g (y i) (y j) (hy i j)]
  rfl

variable (D) in

def lineMap (hC : CechPt) : cech D.f ⟶ ofCat (glCat 1) where
  app n :=
    { app := fun U => TypeCat.ofHom fun z =>
        lineFun D (pts hC (show Sx (cech D.f) n.unop.len U.unop from z)) (pts_eq hC _)
      naturality := fun U U' g => by
        ext z
        exact lineFun_res D g.unop _ (pts_eq hC _) _ (pts_eq hC _) (fun i => pts_res hC g.unop _ i) }
  naturality n m θ := by
    ext U z
    change lineFun D (pts hC (Sx.along (show Sx (cech D.f) n.unop.len U.unop from z) θ.unop)) (pts_eq hC _) =
      (SimplexCategory.toCat.map θ.unop).toFunctor ⋙ lineFun D (pts hC (show Sx (cech D.f) n.unop.len U.unop from z)) (pts_eq hC _)
    refine CategoryTheory.Functor.hext (fun _ => rfl) (fun i j p => heq_of_eq ?_)
    exact congrArg (Matrix.GeneralLinearGroup.scalar (Fin 1))
      (u_congr D (pts_along hC _ θ.unop i) (pts_along hC _ θ.unop j) _ _)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem lineMap_exists : CrystallineSemistableComparison.E.CechPt → CrystallineSemistableComparison.E.LineMap := by
  intro hC X D
  refine ⟨lineMap D hC, ?_⟩
  unfold CrystallineSemistableComparison.E.LineData.IsMap
  intro V x a h
  have hp := pts_cechPt (D := D) hC x a h
  change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1)
    (D.u (pts hC (cechPt D.f 1 x a h) 0) (pts hC (cechPt D.f 1 x a h) 1) (pts_eq hC _ 0 1))) = _
  rw [u_congr D (congrFun hp 0) (congrFun hp 1) _ ((h 0).trans (h 1).symm)]
  ext
  simp [Matrix.GeneralLinearGroup.scalar]

end GlobalTheory.CompanionTheory.CechLine
