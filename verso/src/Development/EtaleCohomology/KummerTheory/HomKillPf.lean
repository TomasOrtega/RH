import Development.EtaleCohomology.KummerTheory.FinalTheorems

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.HomKillPf
open LateralTheory.KummerTheory.LHCut

/- English proof (translation)
Rewrite using `[GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]`. Apply `Precoverage.generate_mem_toGrothendieck` to reduce the goal to its premises. Use `(Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun x => ⟨x, ?_⟩, fun u => (hg u).1⟩` and prove the remaining obligations. Take `⟨v, hv⟩` from `(hg x).2`. Conclude with `⟨v, hv⟩`.
-/
lemma cover_mem {S : Scheme.{0}} {U : Over S} (V : U.left → Over S) (g : ∀ u, V u ⟶ U)
    (hg : ∀ u, Nbhd (g u) u) : Sieve.ofArrows V g ∈ (Scheme.etaleTopology.over S) U := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  apply Precoverage.generate_mem_toGrothendieck
  refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun x => ⟨x, ?_⟩, fun u => (hg u).1⟩
  obtain ⟨v, hv⟩ := (hg x).2
  exact ⟨v, hv⟩

/- English proof (translation)
Rewrite using `[← ModuleCat.mono_iff_injective]`. Establish `: Mono ((sheafToPresheaf _ _).map f)` using `inferInstance`. Conclude with `(NatTrans.mono_iff_mono_app _).1 this (op U)`.
-/
lemma inj_app {Λ : Type} [CommRing Λ] {S : Scheme.{0}} {F G : SlShv Λ S} (f : F ⟶ G) [Mono f]
    (U : Over S) : Function.Injective (f.hom.app (op U)).hom := by
  rw [← ModuleCat.mono_iff_injective]
  have : Mono ((sheafToPresheaf _ _).map f) := inferInstance
  exact (NatTrans.mono_iff_mono_app _).1 this (op U)

variable {Λ : Type} [CommRing Λ] {S : Scheme.{0}}

/- English proof (translation)
Apply `F.isSeparated U R hR s 0` to reduce the goal to its premises. Introduce `W f hf`. Rewrite using `[h W f hf, map_zero]`.
-/
lemma sec_eq_zero (F : SlShv Λ S) {U : Over S}
    (s : F.obj.obj (op U)) (R : Sieve U) (hR : R ∈ (Scheme.etaleTopology.over S) U)
    (h : ∀ (W : Over S) (f : W ⟶ U), R f → (F.obj.map f.op).hom s = 0) : s = 0 := by
  apply F.isSeparated U R hR s 0
  intro W f hf
  rw [h W f hf, map_zero]

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ N ih => rw [succ_nsmul, succ_nsmul, ← ih]`. Both sides reduce to the same expression.
-/
lemma nsmul_app {F G : SlShv Λ S} (f : F ⟶ G) (N : ℕ)
    (U : Over S) (x : F.obj.obj (op U)) :
    ((N • f).hom.app (op U)).hom x = N • (f.hom.app (op U)).hom x := by
  induction N with
  | zero => simp
  | succ N ih => rw [succ_nsmul, succ_nsmul, ← ih]; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma comp_sec {F G H : SlShv Λ S} (f : F ⟶ G) (g : G ⟶ H) (U : Over S) (x : F.obj.obj (op U)) :
    ((f ≫ g).hom.app (op U)).hom x = (g.hom.app (op U)).hom ((f.hom.app (op U)).hom x) := rfl

/- English proof (translation)
Use `congrArg (fun φ => φ.hom x) (f.hom.naturality g.op)` as an intermediate fact. Simplify using `using this`.
-/
lemma nat_sec {F G : SlShv Λ S} (f : F ⟶ G) {U V : Over S} (g : V ⟶ U) (x : F.obj.obj (op U)) :
    (f.hom.app (op V)).hom ((F.obj.map g.op).hom x) = (G.obj.map g.op).hom ((f.hom.app (op U)).hom x) := by
  have := congrArg (fun φ => φ.hom x) (f.hom.naturality g.op)
  simpa using this

/- English proof (translation)
Apply `Sheaf.hom_ext` to reduce the goal to its premises. Use extensionality with `U x`. Conclude with `h U.unop x`.
-/
lemma hom_eq_zero {F G : SlShv Λ S} (f : F ⟶ G)
    (h : ∀ (U : Over S) (x : F.obj.obj (op U)), (f.hom.app (op U)).hom x = 0) : f = 0 := by
  apply Sheaf.hom_ext
  ext U x
  exact h U.unop x

/- English proof (translation)
Introduce `Λ _ S C N j hloc`. Rewrite using `[← cancel_epi (C.homologyπ j), comp_zero, Preadditive.comp_nsmul, Category.comp_id]`. Apply `hom_eq_zero` to reduce the goal to its premises. Introduce `U z`. Rewrite using `[nsmul_app]`.

Establish `hx : ((C.d j (j + 1)).hom.app (op U)).hom ((C.iCycles j).hom.app (op U) |>.hom z) = 0`. Rewrite using `[← comp_sec, C.iCycles_d]`. Both sides reduce to the same expression. Use `choose V g hg y hy using hloc U _ hx`. Apply `sec_eq_zero _ _ (Sieve.ofArrows V g) (cover_mem V g hg)` to reduce the goal to its premises.

Introduce and unpack `W f ⟨Y, h, _, ⟨u⟩, rfl⟩`. Rewrite using `[op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]`. Use `map_zero ((C.homology j).obj.map h.op).hom` and compare the differences between its conclusion and the goal. Rewrite using `[map_nsmul, ← nat_sec, ← map_nsmul]`. Establish `key : N • ((C.cycles j).obj.map (g u).op).hom z = ((C.toCycles (j - 1) j).hom.app (op (V u))).hom (y u)`.

Apply `inj_app (C.iCycles j)` to reduce the goal to its premises. Rewrite using `[← comp_sec, C.toCycles_i, hy u, map_nsmul, nat_sec]`. Rewrite using `[key, ← comp_sec, C.toCycles_comp_homologyπ]`. Both sides reduce to the same expression.
-/
theorem homKill_of : HomKill := by
  intro Λ _ S C N j hloc
  rw [← cancel_epi (C.homologyπ j), comp_zero, Preadditive.comp_nsmul, Category.comp_id]
  apply hom_eq_zero
  intro U z
  rw [nsmul_app]
  have hx : ((C.d j (j + 1)).hom.app (op U)).hom ((C.iCycles j).hom.app (op U) |>.hom z) = 0 := by
    rw [← comp_sec, C.iCycles_d]; rfl
  choose V g hg y hy using hloc U _ hx
  apply sec_eq_zero _ _ (Sieve.ofArrows V g) (cover_mem V g hg)
  rintro W f ⟨Y, h, _, ⟨u⟩, rfl⟩
  rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  convert map_zero ((C.homology j).obj.map h.op).hom
  rw [map_nsmul, ← nat_sec, ← map_nsmul]
  have key : N • ((C.cycles j).obj.map (g u).op).hom z = ((C.toCycles (j - 1) j).hom.app (op (V u))).hom (y u) := by
    apply inj_app (C.iCycles j)
    rw [← comp_sec, C.toCycles_i, hy u, map_nsmul, nat_sec]
  rw [key, ← comp_sec, C.toCycles_comp_homologyπ]; rfl

end LateralTheory.KummerTheory.HomKillPf
