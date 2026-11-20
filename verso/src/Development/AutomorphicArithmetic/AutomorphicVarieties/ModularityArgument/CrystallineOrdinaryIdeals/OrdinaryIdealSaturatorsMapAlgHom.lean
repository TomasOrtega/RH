import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLocNat

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O)
  {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG 3 C)

/- English proof (translation)
Use `show (GG.map (f : C →+* C') (r g)).mat = _`. Rewrite using `[GG.map_mat]`. Both sides reduce to the same expression.
-/
theorem push_mat (g : GQ l) : (push f r g).mat = (r g).mat.map f := by
  show (GG.map (f : C →+* C') (r g)).mat = _
  rw [GG.map_mat]; rfl

/- English proof (translation)
Unfold `GlobalTheory.OrdLoc.sh`. Rewrite using `[push_mat]`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h]`.
-/
theorem sh_push (a : Fin 3) (s : GQ l) : GlobalTheory.OrdLoc.sh D (push f r) a s = (GlobalTheory.OrdLoc.sh D r a s).map f := by
  unfold GlobalTheory.OrdLoc.sh
  rw [push_mat]
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h]

/- English proof (translation)
Unfold `GlobalTheory.OrdLoc.tr`. Rewrite using `[sh_push, sh_push, push_mat, ← Matrix.map_mul, ← Matrix.map_mul]`. Rewrite using `[Matrix.trace, Matrix.trace, map_sum]`. Both sides reduce to the same expression.
-/
theorem tr_push (a : Fin 3) : f (GlobalTheory.OrdLoc.tr D r a) = GlobalTheory.OrdLoc.tr D (push f r) a := by
  unfold GlobalTheory.OrdLoc.tr
  rw [sh_push, sh_push, push_mat, ← Matrix.map_mul, ← Matrix.map_mul]
  rw [Matrix.trace, Matrix.trace, map_sum]
  rfl

/- English proof (translation)
Unfold `GlobalTheory.OrdLoc.dd`. Simplify using `only [map_sub, map_mul, AlgHom.commutes, tr_push]`.
-/
theorem dd_push (a : Fin 3) : f (GlobalTheory.OrdLoc.dd D r a) = GlobalTheory.OrdLoc.dd D (push f r) a := by
  unfold GlobalTheory.OrdLoc.dd
  simp only [map_sub, map_mul, AlgHom.commutes, tr_push]

/- English proof (translation)
Unfold `GlobalTheory.OrdLoc.del`. Simplify using `only [map_mul, map_natCast, dd_push]`.
-/
theorem del_push : f (GlobalTheory.OrdLoc.del D r) = GlobalTheory.OrdLoc.del D (push f r) := by
  unfold GlobalTheory.OrdLoc.del
  simp only [map_mul, map_natCast, dd_push]

/- English proof (translation)
Unfold `GlobalTheory.OrdLoc.ordIdeal`. Rewrite using `[Ideal.map_span, Set.image_union]`. Use `congr 2`. Use extensionality with `x`. Simplify using `only [Set.mem_image, Set.mem_setOf_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨s, hs, i, rfl⟩, rfl⟩`. Use `⟨s, hs, i, ?_⟩` and prove the remaining obligations. Rewrite using `[push_mat, show ((r s).mat.map f).charpoly = (r s).mat.charpoly.map (f : C →+* C') from Matrix.charpoly_map _ _]`. Rewrite using `[← Polynomial.coeff_map]`.

Simplify using `[Polynomial.map_sub, Polynomial.map_prod]`. Introduce and unpack `⟨s, hs, i, rfl⟩`. Use `⟨_, ⟨s, hs, i, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[push_mat, show ((r s).mat.map f).charpoly = (r s).mat.charpoly.map (f : C →+* C') from Matrix.charpoly_map _ _]`. Rewrite using `[← Polynomial.coeff_map]`.

Simplify using `[Polynomial.map_sub, Polynomial.map_prod]`. Use extensionality with `x`. Simplify using `only [Set.mem_image, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨s, hs, i, j, rfl⟩, rfl⟩`.

Use `⟨s, hs, i, j, ?_⟩` and prove the remaining obligations. Rewrite using `[sh_push, sh_push, sh_push, ← Matrix.map_mul, ← Matrix.map_mul]`. Both sides reduce to the same expression. Introduce and unpack `⟨s, hs, i, j, rfl⟩`. Use `⟨_, ⟨s, hs, i, j, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[sh_push, sh_push, sh_push, ← Matrix.map_mul, ← Matrix.map_mul]`. Both sides reduce to the same expression.
-/
theorem ordIdeal_push : (GlobalTheory.OrdLoc.ordIdeal D r).map (f : C →+* C') = GlobalTheory.OrdLoc.ordIdeal D (push f r) := by
  unfold GlobalTheory.OrdLoc.ordIdeal
  rw [Ideal.map_span, Set.image_union]
  congr 2
  · ext x
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, ⟨s, hs, i, rfl⟩, rfl⟩
      refine ⟨s, hs, i, ?_⟩
      rw [push_mat, show ((r s).mat.map f).charpoly = (r s).mat.charpoly.map (f : C →+* C') from Matrix.charpoly_map _ _]
      rw [← Polynomial.coeff_map]
      simp [Polynomial.map_sub, Polynomial.map_prod]
    · rintro ⟨s, hs, i, rfl⟩
      refine ⟨_, ⟨s, hs, i, rfl⟩, ?_⟩
      rw [push_mat, show ((r s).mat.map f).charpoly = (r s).mat.charpoly.map (f : C →+* C') from Matrix.charpoly_map _ _]
      rw [← Polynomial.coeff_map]
      simp [Polynomial.map_sub, Polynomial.map_prod]
  · ext x
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, ⟨s, hs, i, j, rfl⟩, rfl⟩
      refine ⟨s, hs, i, j, ?_⟩
      rw [sh_push, sh_push, sh_push, ← Matrix.map_mul, ← Matrix.map_mul]
      rfl
    · rintro ⟨s, hs, i, j, rfl⟩
      refine ⟨_, ⟨s, hs, i, j, rfl⟩, ?_⟩
      rw [sh_push, sh_push, sh_push, ← Matrix.map_mul, ← Matrix.map_mul]
      rfl

/- English proof (translation)
Introduce `l _ O _ _ _ D C C' _ _ _ _ f r`. Conclude with `⟨GlobalTheory.OrdLocNat.ordIdeal_push D f r, GlobalTheory.OrdLocNat.dd_push D f r, GlobalTheory.OrdLocNat.del_push D f r⟩`.
-/
theorem main : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O) {C C' : Type} [CommRing C] [Algebra O C] [CommRing C'] [Algebra O C'] (f : C →ₐ[O] C') (r : GQ l →* GG 3 C), (GlobalTheory.OrdLoc.ordIdeal D r).map (f : C →+* C') = GlobalTheory.OrdLoc.ordIdeal D (push f r) ∧ (∀ a, f (GlobalTheory.OrdLoc.dd D r a) = GlobalTheory.OrdLoc.dd D (push f r) a) ∧ f (GlobalTheory.OrdLoc.del D r) = GlobalTheory.OrdLoc.del D (push f r) :=
  by intro l _ O _ _ _ D C C' _ _ _ _ f r; exact ⟨GlobalTheory.OrdLocNat.ordIdeal_push D f r, GlobalTheory.OrdLocNat.dd_push D f r, GlobalTheory.OrdLocNat.del_push D f r⟩

end GlobalTheory.OrdLocNat
