import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective

set_option autoImplicit false

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.Dieu

section FrobInv

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

/- English proof (translation)
Apply `(WittVector.frobeniusEquiv p k).injective` to reduce the goal to its premises. Rewrite using `[RingEquiv.apply_symm_apply]`. Use extensionality with `n`. Simplify using `[WittVector.coeff_frobenius_charP, WittVector.map_coeff]`.
-/
theorem wittMap_frobeniusEquiv_symm (x : WittVector p k) :
    WittVector.map ((frobeniusEquiv k p).symm : k →+* k) x = (WittVector.frobeniusEquiv p k).symm x := by
  apply (WittVector.frobeniusEquiv p k).injective
  rw [RingEquiv.apply_symm_apply]
  ext n
  simp [WittVector.coeff_frobenius_charP, WittVector.map_coeff]

noncomputable def frobInv (G : PDivGroup p k) :
    SemiHom ((frobeniusEquiv k p).symm : k →+* k) G (frobTwist (p_eq_zero p k) G) :=
  letI := (frobRing (p_eq_zero p k)).toAlgebra
  (SemiHom.ofHom (𝟙 G)).liftOver _ fun r => by
    change r = (frobeniusEquiv k p).symm (frobRing (p_eq_zero p k) r)
    rw [frobRing_apply, ← frobenius_def, frobeniusEquiv_symm_apply_frobenius]

/- English proof (translation)
Use `letI := (frobRing (p_eq_zero p k)).toAlgebra`. Use `(SemiHom.liftOver_app _ _ _ n 1 a).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem frobInv_frobProj (G : PDivGroup p k) (n : ℕ) (a : G.A n) :
    (frobInv G).app n ((frobProj (p_eq_zero p k) G).app n a) = a := by
  letI := (frobRing (p_eq_zero p k)).toAlgebra
  refine (SemiHom.liftOver_app _ _ _ n 1 a).trans ?_
  simp

/- English proof (translation)
Establish `h0 : (p : G.A n) = 0` using `natCast_eq_zero_of_algebra (p_eq_zero p k) _`. Proceed by induction on `y using frobTwist_induction (p_eq_zero p k) n with`. Consider the case `h0 => simp [zero_pow (Fact.out : p.Prime).ne_zero]`. Consider the case `h1 r a`. Rewrite using `[(frobInv G).app n |>.smul_map, frobInv_frobProj, map_smul, relFrob_app_frobProj, smul_pow]`.

Use `congr 1`. Conclude with `frobeniusEquiv_symm_pow_p k p r`. Consider the case `h2 x y hx hy`. Rewrite using `[map_add, map_add, ← hx, ← hy]`. Simplify using `using map_add (frobRing h0) ((frobInv G).app n x) ((frobInv G).app n y)`.
-/
theorem frobInv_app_pow (G : PDivGroup p k) (n : ℕ) (y : (frobTwist (p_eq_zero p k) G).A n) :
    ((frobInv G).app n y) ^ p = (relFrob (p_eq_zero p k) G).app n y := by
  have h0 : (p : G.A n) = 0 := natCast_eq_zero_of_algebra (p_eq_zero p k) _
  induction y using frobTwist_induction (p_eq_zero p k) n with
  | h0 => simp [zero_pow (Fact.out : p.Prime).ne_zero]
  | h1 r a =>
    rw [(frobInv G).app n |>.smul_map, frobInv_frobProj, map_smul, relFrob_app_frobProj, smul_pow]
    congr 1
    exact frobeniusEquiv_symm_pow_p k p r
  | h2 x y hx hy =>
    rw [map_add, map_add, ← hx, ← hy]
    simpa using map_add (frobRing h0) ((frobInv G).app n x) ((frobInv G).app n y)

omit [CharP k p] [PerfectRing k p] in

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `e` using `B.smap_add h h 0 0 m`. Rewrite `e` using `[add_zero]`. Rewrite using `[zero_smul, zero_smul]`.

Simplify using `using e`. Consider the case `succ n ih => rw [succ_nsmul, B.smap_add, ih, B.smap_id, succ_nsmul]`.
-/
theorem Base.smap_ofHom_nsmul_id {P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop} (B : Base p P)
    [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G) (n : ℕ) (m : B.M G h) :
    B.smap h h (SemiHom.ofHom (n • 𝟙 G)) m = n • m := by
  induction n with
  | zero =>
    have e := B.smap_add h h 0 0 m
    rw [add_zero] at e
    rw [zero_smul, zero_smul]
    simpa using e
  | succ n ih => rw [succ_nsmul, B.smap_add, ih, B.smap_id, succ_nsmul]

noncomputable def Base.verOp (B : Base p fun _ _ _ => True) (G : PDivGroup p k) :
    B.M G trivial →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)]
      B.M G trivial where
  toFun m := B.smap trivial trivial (frobInv G) (B.map trivial trivial (verschiebung (p_eq_zero p k) G) m)
  map_add' x y := by rw [map_add, map_add]
  map_smul' a m := by
    rw [LinearMap.map_smul, B.smap_smul, wittMap_frobeniusEquiv_symm]
    rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `B.smap trivial trivial (absFrob (p_eq_zero p k) G) (B.smap trivial trivial (frobInv G) (B.smap trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)) m)) = _`. Rewrite using `[← B.smap_comp trivial trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)) (frobInv G) ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G))) (fun n a => rfl)]`. Rewrite using `[← B.smap_comp trivial trivial trivial ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G))) (absFrob (p_eq_zero p k) G) (SemiHom.ofHom (relFrob (p_eq_zero p k) G ≫ verschiebung (p_eq_zero p k) G)) ?_]`. Rewrite using `[relFrob_comp_verschiebung, Nat.cast_smul_eq_nsmul, B.smap_ofHom_nsmul_id]`. Introduce `n a`.

Rewrite using `[SemiHom.ofHom_app, absFrob_app, SemiHom.comp_app, SemiHom.ofHom_app, frobInv_app_pow]`. Both sides reduce to the same expression.
-/
theorem Base.F_verOp (B : Base p fun _ _ _ => True) (G : PDivGroup p k) (m : B.M G trivial) :
    B.F G trivial (B.verOp G m) = p • m := by
  change B.smap trivial trivial (absFrob (p_eq_zero p k) G) (B.smap trivial trivial (frobInv G)
    (B.smap trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)) m)) = _
  rw [← B.smap_comp trivial trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)) (frobInv G)
    ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G))) (fun n a => rfl)]
  rw [← B.smap_comp trivial trivial trivial ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)))
    (absFrob (p_eq_zero p k) G) (SemiHom.ofHom (relFrob (p_eq_zero p k) G ≫ verschiebung (p_eq_zero p k) G)) ?_]
  · rw [relFrob_comp_verschiebung, Nat.cast_smul_eq_nsmul, B.smap_ofHom_nsmul_id]
  · intro n a
    rw [SemiHom.ofHom_app, absFrob_app, SemiHom.comp_app, SemiHom.ofHom_app, frobInv_app_pow]
    rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `B.smap trivial trivial (frobInv G) (B.smap trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)) (B.smap trivial trivial (absFrob (p_eq_zero p k) G) m)) = _`. Rewrite using `[← B.smap_comp trivial trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)) (frobInv G) ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G))) (fun n a => rfl)]`. Rewrite using `[← B.smap_comp trivial trivial trivial (absFrob (p_eq_zero p k) G) ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G))) (SemiHom.ofHom (relFrob (p_eq_zero p k) G ≫ verschiebung (p_eq_zero p k) G)) ?_]`. Rewrite using `[relFrob_comp_verschiebung, Nat.cast_smul_eq_nsmul, B.smap_ofHom_nsmul_id]`. Introduce `n a`.

Rewrite using `[SemiHom.ofHom_app, absFrob_app, SemiHom.comp_app, SemiHom.ofHom_app]`. Rewrite using `[map_pow, map_pow, frobInv_app_pow]`. Both sides reduce to the same expression.
-/
theorem Base.verOp_F (B : Base p fun _ _ _ => True) (G : PDivGroup p k) (m : B.M G trivial) :
    B.verOp G (B.F G trivial m) = p • m := by
  change B.smap trivial trivial (frobInv G)
    (B.smap trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G))
      (B.smap trivial trivial (absFrob (p_eq_zero p k) G) m)) = _
  rw [← B.smap_comp trivial trivial trivial (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)) (frobInv G)
    ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G))) (fun n a => rfl)]
  rw [← B.smap_comp trivial trivial trivial (absFrob (p_eq_zero p k) G)
    ((frobInv G).comp (SemiHom.ofHom (verschiebung (p_eq_zero p k) G)))
    (SemiHom.ofHom (relFrob (p_eq_zero p k) G ≫ verschiebung (p_eq_zero p k) G)) ?_]
  · rw [relFrob_comp_verschiebung, Nat.cast_smul_eq_nsmul, B.smap_ofHom_nsmul_id]
  · intro n a
    rw [SemiHom.ofHom_app, absFrob_app, SemiHom.comp_app, SemiHom.ofHom_app]
    rw [map_pow, map_pow, frobInv_app_pow]
    rfl

end FrobInv

/- English proof (translation)
Introduce `_ _ B` and use `⟨fun G => B.verOp G, fun G m => B.F_verOp G m, fun G m => B.verOp_F G m⟩`.
-/
theorem exists_V_of_base : ∀ (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Dieu.Base p (fun _ _ _ => True)),
    ∃ V : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k),
      B.M G trivial →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)] B.M G trivial,
      (∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k) (m : B.M G trivial),
        B.F G trivial (V G m) = p • m) ∧
      ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k) (m : B.M G trivial),
        V G (B.F G trivial m) = p • m :=
  fun _ _ B => ⟨fun G => B.verOp G, fun G m => B.F_verOp G m, fun G m => B.verOp_F G m⟩

end GlobalTheory.Dieu
