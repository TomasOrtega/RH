import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Simplify using `[reGL]`.
-/
theorem reGL_rfl {a : ℕ} (R : Type) [CommRing R] (x : GL (Fin a) R) : reGL rfl R x = x := by
  apply Units.ext
  ext i j
  simp [reGL]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[reV]`.
-/
theorem reV_rfl {a : ℕ} (E : Type) [Field E] (x : Fin a → E) : reV rfl E x = x := by
  ext i
  simp [reV]

/- English proof (translation)
Use extensionality with `z`. Simplify using `[reL, reV_rfl]`.
-/
theorem reL_rfl {a : ℕ} {E : Type} [Field E] [NumberField E] (L : Submodule (𝓞 E) (Fin a → E)) : reL rfl L = L := by
  ext z
  simp [reL, reV_rfl]

/- English proof (translation)
Unfold `AtTTied.Pv`. Rewrite using `[J.res]`. Conclude with `(X.atT u).res_ker v`.
-/
theorem Joint.Pv {D : D7} {X : Formalism.L2.Herm.ColsHerm D} {u : D.what₂.Word} {T : FormsTied D u} (J : Joint X u T)
    (v : (D.mem u).A.vT) : T.atT.Pv v = (X.atT u).Pv v := by
  unfold AtTTied.Pv
  rw [J.res]
  exact (X.atT u).res_ker v

end Formalism.L2.Forms
