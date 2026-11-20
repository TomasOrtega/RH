import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.LatticeComparisonCompatible
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CmpCMemFunMod

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem reGL_apply {a b : ℕ} (h : a = b) (R : Type) [CommRing R] (g : GL (Fin a) R) (x y : Fin b) :
    (reGL h R g : Matrix (Fin b) (Fin b) R) x y = (g : Matrix (Fin a) (Fin a) R) (Fin.cast h.symm x) (Fin.cast h.symm y) := by
  rfl

/- English proof (translation)
Substitute `h` using the available equality. Establish `hJ' : J' = J`. Use extensionality with `x y`. Rewrite using `[hJ]`. Simplify using the standard rewrite rules.

Substitute `hJ'` using the available equality. Establish `hg' : reGL rfl R g = g`. Use extensionality with `x y`. Rewrite using `[reGL_apply]`. Simplify using the standard rewrite rules.

Rewrite using `[hg']`. Conclude with `hg`.
-/
theorem reGL_mem_UJ {a b : ℕ} (h : a = b) {R : Type} [CommRing R] (σ : R →+* R) (J : Matrix (Fin a) (Fin a) R)
    (J' : Matrix (Fin b) (Fin b) R) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y)) (g : GL (Fin a) R)
    (hg : g ∈ UJ σ J) : reGL h R g ∈ UJ σ J' := by
  subst h
  have hJ' : J' = J := by
    ext x y
    rw [hJ]
    simp
  subst hJ'
  have hg' : reGL rfl R g = g := by
    ext x y
    rw [reGL_apply]
    simp
  rw [hg']
  exact hg

/- English proof (translation)
Introduce `i v γ`. Establish `key : ((bc (A.phE v) B0)⁻¹ * bc (A.phE v) (γ0 i γ) * bc (A.phE v) B0 : GL (Fin k) _) = bc (A.phE v) (B0⁻¹ * γ0 i γ * B0)`. Simplify using `only [map_mul, map_inv]`. Establish `key2 : (A.B⁻¹ * A.gamI i γ * A.B : GL (Fin n) E) = reGL hk E (B0⁻¹ * γ0 i γ * B0)`. Rewrite using `[hB, hγ]`.

Simplify using `only [map_mul, map_inv]`. Establish `hiw : ∀ z, A.eQ v (A.iw v z) = A.phE v z` using `fun z => by`. Simplify using `[LocAt.iw]`. Use extensionality with `x y`. Apply `(A.eQ v).injective` to reduce the goal to its premises.

Establish `h1` using `hact i v γ (Fin.cast A.rk.symm x) (Fin.cast A.rk.symm y) (Fin.cast hk.symm x) (Fin.cast hk.symm y) rfl rfl`. Rewrite `h1` using `[key]`. Rewrite using `[key2]`. Conclude with `h1.trans (hiw _).symm`.
-/
theorem LocAt.actB_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ}
    {G : GAtP p} (A : LocAt F E n G) {k : ℕ} (hk : k = n) (B0 : GL (Fin k) E) (γ0 : ∀ i, (G.lev i).Γ → GL (Fin k) E)
    (hB : A.B = reGL hk E B0) (hγ : ∀ i γ, A.gamI i γ = reGL hk E (γ0 i γ))
    (hact : ∀ i v (γ : (G.lev i).Γ) (a b : Fin (G.P.m + 1)) (a' b' : Fin k), (a : ℕ) = a' → (b : ℕ) = b' →
      A.eQ v (((G.lev i).act v γ : GL (Fin (G.P.m + 1)) (G.P.Qq v)) a b) =
        (((bc (A.phE v) B0)⁻¹ * bc (A.phE v) (γ0 i γ) * bc (A.phE v) B0 : GL (Fin k) _) : Matrix (Fin k) (Fin k) _) a' b') :
    A.ActB := by
  intro i v γ
  have key : ((bc (A.phE v) B0)⁻¹ * bc (A.phE v) (γ0 i γ) * bc (A.phE v) B0 : GL (Fin k) _) =
      bc (A.phE v) (B0⁻¹ * γ0 i γ * B0) := by
    simp only [map_mul, map_inv]
  have key2 : (A.B⁻¹ * A.gamI i γ * A.B : GL (Fin n) E) = reGL hk E (B0⁻¹ * γ0 i γ * B0) := by
    rw [hB, hγ]
    simp only [map_mul, map_inv]
  have hiw : ∀ z, A.eQ v (A.iw v z) = A.phE v z := fun z => by
    simp [LocAt.iw]
  ext x y
  apply (A.eQ v).injective
  have h1 := hact i v γ (Fin.cast A.rk.symm x) (Fin.cast A.rk.symm y) (Fin.cast hk.symm x)
    (Fin.cast hk.symm y) rfl rfl
  rw [key] at h1
  rw [key2]
  exact h1.trans (hiw _).symm

variable {D : D7}

/- English proof (translation)
The claim follows from `D.sp.cm.cmUnram.2.1 (embT D τ) x`.
-/
theorem embT_conj (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (sigD D x) = starRingEnd ℂ (embT D τ x) :=
  D.sp.cm.cmUnram.2.1 (embT D τ) x

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gramN_zero (D : D7) (x y : Fin (D.R.N 0)) :
    gramN D 0 (Nat.zero_le _) x y = D.sp.gram0 (Fin.cast (rank_eq_first_level D.R).symm x) (Fin.cast (rank_eq_first_level D.R).symm y) := rfl

variable {X : Formalism.L2.Herm.Herm0 D}

/- English proof (translation)
Conclude with `reGL_mem_UJ (rank_eq_first_level D.R) (sigD D : D.host.E →+* D.host.E) D.sp.gram0 _ (fun x y => gramN_zero D x y) _ ((X.g u w hg).gamI i γ).2`.
-/
theorem locAt_UJ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (B : GL (Fin D.R.k) D.host.E) (i : (D.gat u w hg).comp) (γ : ((D.gat u w hg).lev i).Γ) :
    (locAt X u w hg B).gamI i γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) := by
  exact reGL_mem_UJ (rank_eq_first_level D.R) (sigD D : D.host.E →+* D.host.E) D.sp.gram0 _ (fun x y => gramN_zero D x y) _
    ((X.g u w hg).gamI i γ).2

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `LocAt.actB_of (locAt X u w hg B) (rank_eq_first_level D.R) B (fun i γ => ((X.g u w hg).gamI i γ : GL (Fin D.R.k) D.host.E)) rfl (fun i γ => rfl) ?_` and prove the remaining obligations. Introduce `i v γ a b a' b' ha hb`. Establish `h1` using `(X.g u w hg).act_eq i v _ rfl ((X.g u w hg).pl v).2 γ a b a' b' ha hb`. Rewrite `h1` using `[hB _ ((X.g u w hg).pl v).2]`. Establish `hbc : bc ((RingHom.fst _ _).comp ((X.g u w hg).spl _ ((X.g u w hg).pl v).2).toRingHom) (bc (inclE (F` using `D.host.F) _) ((X.g u w hg).gamI i γ : GL (Fin D.R.k) D.host.E)) = bc (((RingHom.fst _ _).comp ((X.g u w hg).spl _ ((X.g u w hg).pl v).2).toRingHom).comp (inclE (F := D.host.F) _)) ((X.g u w hg).gamI i γ : GL (Fin D.R.k) D.host.E) := by`.

Use extensionality with `x y`. Both sides reduce to the same expression. Rewrite `h1` using `[hbc]`. Conclude with `h1`.
-/
theorem locAt_actB (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (B : GL (Fin D.R.k) D.host.E) (hB : FrRat X u w hg B) : (locAt X u w hg B).ActB := by
  refine LocAt.actB_of (locAt X u w hg B) (rank_eq_first_level D.R) B
    (fun i γ => ((X.g u w hg).gamI i γ : GL (Fin D.R.k) D.host.E)) rfl (fun i γ => rfl) ?_
  intro i v γ a b a' b' ha hb
  have h1 := (X.g u w hg).act_eq i v _ rfl ((X.g u w hg).pl v).2 γ a b a' b' ha hb
  rw [hB _ ((X.g u w hg).pl v).2] at h1
  have hbc : bc ((RingHom.fst _ _).comp ((X.g u w hg).spl _ ((X.g u w hg).pl v).2).toRingHom)
      (bc (inclE (F := D.host.F) _) ((X.g u w hg).gamI i γ : GL (Fin D.R.k) D.host.E)) =
      bc (((RingHom.fst _ _).comp ((X.g u w hg).spl _ ((X.g u w hg).pl v).2).toRingHom).comp
        (inclE (F := D.host.F) _)) ((X.g u w hg).gamI i γ : GL (Fin D.R.k) D.host.E) := by
    ext x y
    rfl
  rw [hbc] at h1
  exact h1

/- English proof (translation)
Conclude with `hB.1`.
-/
theorem locAt_std (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (B : GL (Fin D.R.k) D.host.E) (hB : StdB D B) :
    cT (sigD D : D.host.E →+* D.host.E) (locAt X u w hg B).B.1 * gramN D 0 (Nat.zero_le _) * (locAt X u w hg B).B.1 = 1 := by
  exact hB.1

end Formalism.L2.G.Cmp

end
