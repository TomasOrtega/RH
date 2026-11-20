import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.KapBij

section Res

variable {R : Type} [CommRing R] {F : Shv R}

/- English proof (translation)
The claim follows from `map_smul _ _ _`.
-/
theorem res_smul {V U : Scheme.{0}} (g : V ⟶ U) (c : ULift.{1} R) (a : Sec F U) :
    Sec.res g (c • a) = c • Sec.res g a :=
  map_smul _ _ _

/- English proof (translation)
Use `show (F.obj.map k.op).hom ((F.obj.map g.op).hom a) = (F.obj.map (k ≫ g).op).hom a`. Rewrite using `[op_comp, F.obj.map_comp]`. Both sides reduce to the same expression.
-/
theorem res_res {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res k (Sec.res g a) = Sec.res (k ≫ g) a := by
  show (F.obj.map k.op).hom ((F.obj.map g.op).hom a) = (F.obj.map (k ≫ g).op).hom a
  rw [op_comp, F.obj.map_comp]
  rfl

end Res

/- English proof (translation)
Rewrite using `[← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]`. Use `congr 1`.
-/
theorem nsmul_eq_up {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (c : ℕ) (t : M) :
    c • t = (ULift.up (c : ZMod q) : ULift.{1} (ZMod q)) • t := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  congr 1

/- English proof (translation)
Establish `hq : q ∣ a.val` using `(hg q i).2.1 V ζ a.val (by`. Rewrite using `[nsmul_eq_up (q := q), ZMod.natCast_zmod_val]`. Conclude with `h)`. Rewrite using `[← ZMod.natCast_zmod_val a]`. Conclude with `(ZMod.natCast_eq_zero_iff _ _).2 hq`.
-/
theorem coef_eq_zero (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {V : Scheme.{0}} [Nonempty V]
    (ζ : Prim q Γ(V, ⊤)) (a : ZMod q)
    (h : (ULift.up a : ULift.{1} (ZMod q)) • twGen i ζ = 0) : a = 0 := by
  have hq : q ∣ a.val := (hg q i).2.1 V ζ a.val (by
    rw [nsmul_eq_up (q := q), ZMod.natCast_zmod_val]
    exact h)
  rw [← ZMod.natCast_zmod_val a]
  exact (ZMod.natCast_eq_zero_iff _ _).2 hq

/- English proof (translation)
Use `sub_eq_zero.1 (coef_eq_zero hg i ζ _ ?_)` and prove the remaining obligations. Establish `e : (ULift.up (a - b) : ULift.{1} (ZMod q)) = ULift.up a - ULift.up b` using `rfl`. Rewrite using `[e, sub_smul, h, sub_self]`.
-/
theorem coef_unique (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {V : Scheme.{0}} [Nonempty V]
    (ζ : Prim q Γ(V, ⊤)) (a b : ZMod q)
    (h : (ULift.up a : ULift.{1} (ZMod q)) • twGen i ζ = (ULift.up b : ULift.{1} (ZMod q)) • twGen i ζ) :
    a = b := by
  refine sub_eq_zero.1 (coef_eq_zero hg i ζ _ ?_)
  have e : (ULift.up (a - b) : ULift.{1} (ZMod q)) = ULift.up a - ULift.up b := rfl
  rw [e, sub_smul, h, sub_self]

/- English proof (translation)
Take `⟨z, -, -⟩` from `Scheme.Pullback.exists_preimage_pullback v v' hv`. Establish `: Nonempty ↑(pullback g g')` using `⟨z⟩`. Establish `e1 : Sec.res (pullback.fst g g' ≫ g) x = (ULift.up c : ULift.{1} (ZMod q)) • Sec.res (pullback.fst g g' ≫ g) (twGen i ζ)`. Rewrite using `[← res_res, h, res_smul, res_res]`. Establish `e2 : Sec.res (pullback.fst g g' ≫ g) x = (ULift.up c' : ULift.{1} (ZMod q)) • Sec.res (pullback.fst g g' ≫ g) (twGen i ζ)`.

Rewrite using `[pullback.condition, ← res_res, h', res_smul, res_res]`. Rewrite `e1`, `e2` using `[((hR q i U ζ).1 _ (pullback.fst g g' ≫ g)).1]`. Conclude with `coef_unique hg i _ c c' (e1.symm.trans e2)`.
-/
theorem coef_agree (hR : RepRoot) (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}}
    (ζ : Prim q Γ(U, ⊤)) (x : Sec (tw q i) U) {V V' : Scheme.{0}} (g : V ⟶ U) (g' : V' ⟶ U)
    (c c' : ZMod q)
    (h : Sec.res g x = (ULift.up c : ULift.{1} (ZMod q)) • Sec.res g (twGen i ζ))
    (h' : Sec.res g' x = (ULift.up c' : ULift.{1} (ZMod q)) • Sec.res g' (twGen i ζ))
    (v : V) (v' : V') (hv : g v = g' v') : c = c' := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback v v' hv
  have : Nonempty ↑(pullback g g') := ⟨z⟩
  have e1 : Sec.res (pullback.fst g g' ≫ g) x =
      (ULift.up c : ULift.{1} (ZMod q)) • Sec.res (pullback.fst g g' ≫ g) (twGen i ζ) := by
    rw [← res_res, h, res_smul, res_res]
  have e2 : Sec.res (pullback.fst g g' ≫ g) x =
      (ULift.up c' : ULift.{1} (ZMod q)) • Sec.res (pullback.fst g g' ≫ g) (twGen i ζ) := by
    rw [pullback.condition, ← res_res, h', res_smul, res_res]
  rw [((hR q i U ζ).1 _ (pullback.fst g g' ≫ g)).1] at e1 e2
  exact coef_unique hg i _ c c' (e1.symm.trans e2)

/- English proof (translation)
Use `(loc_iff_etale_affine_points U (fun V g => ∃ c : ZMod q, Sec.res g x = (ULift.up c : ULift.{1} (ZMod q)) • Sec.res g (twGen i ζ)) ?_).1 ?_ u` and prove the remaining obligations. Introduce and unpack `V W g k ⟨c, hc⟩`. Conclude with `⟨c, by rw [← res_res, hc, res_smul, res_res]⟩`. Take `⟨S, hS, hc⟩` from `(hg q i).1 U ζ x`. Use `⟨S, hS, fun V g hgS => ?_⟩` and prove the remaining obligations.

Take `⟨c, hc⟩` from `hc V g hgS`. Use `⟨(c : ZMod q), ?_⟩` and prove the remaining obligations. Rewrite using `[hc, nsmul_eq_up (q := q), ((hR q i U ζ).1 V g).1]`. Both sides reduce to the same expression.
-/
theorem exists_chart (hR : RepRoot) (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}}
    (ζ : Prim q Γ(U, ⊤)) (x : Sec (tw q i) U) (u : U) :
    ∃ (V : Scheme.{0}) (g : V ⟶ U), IsAffine V ∧ Etale g ∧ u ∈ Set.range g ∧
      ∃ c : ZMod q, Sec.res g x = (ULift.up c : ULift.{1} (ZMod q)) • Sec.res g (twGen i ζ) := by
  refine (loc_iff_etale_affine_points U
    (fun V g => ∃ c : ZMod q, Sec.res g x = (ULift.up c : ULift.{1} (ZMod q)) • Sec.res g (twGen i ζ))
    ?_).1 ?_ u
  · rintro V W g k ⟨c, hc⟩
    exact ⟨c, by rw [← res_res, hc, res_smul, res_res]⟩
  · obtain ⟨S, hS, hc⟩ := (hg q i).1 U ζ x
    refine ⟨S, hS, fun V g hgS => ?_⟩
    obtain ⟨c, hc⟩ := hc V g hgS
    refine ⟨(c : ZMod q), ?_⟩
    rw [hc, nsmul_eq_up (q := q), ((hR q i U ζ).1 V g).1]
    rfl

/- English proof (translation)
Use `(injective_iff_map_eq_zero (kap i ζ)).2 fun f hf => LocallyConstant.ext fun u => ?_` and prove the remaining obligations. Set `O : U.Opens` to `⟨f ⁻¹' {f u}, f.isLocallyConstant.isOpen_fiber _⟩`. Establish `: Nonempty O.toScheme` using `⟨⟨u, rfl⟩⟩`. Establish `hO : ∀ v : O.toScheme, f (O.ι v) = f u` using `fun v => by`. Establish `: O.ι v ∈ Set.range O.ι` using `⟨v, rfl⟩`.

Rewrite `this` using `[Scheme.Opens.range_ι]`. Conclude with `this`. Establish `h` using `(hK q i U ζ f).1 O.toScheme O.ι (f u) hO`. Rewrite `h` using `[hf]`. Establish `h0 : Sec.res O.ι (0 : Sec (tw q i) U) = 0` using `map_zero _`.

Rewrite `h` using `[h0]`. Conclude with `coef_eq_zero hg i _ _ h.symm`.
-/
theorem kap_injective (hK : KapSpec) (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}}
    (ζ : Prim q Γ(U, ⊤)) : Function.Injective (kap i ζ) := by
  refine (injective_iff_map_eq_zero (kap i ζ)).2 fun f hf => LocallyConstant.ext fun u => ?_
  let O : U.Opens := ⟨f ⁻¹' {f u}, f.isLocallyConstant.isOpen_fiber _⟩
  have : Nonempty O.toScheme := ⟨⟨u, rfl⟩⟩
  have hO : ∀ v : O.toScheme, f (O.ι v) = f u := fun v => by
    have : O.ι v ∈ Set.range O.ι := ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι] at this
    exact this
  have h := (hK q i U ζ f).1 O.toScheme O.ι (f u) hO
  rw [hf] at h
  have h0 : Sec.res O.ι (0 : Sec (tw q i) U) = 0 := map_zero _
  rw [h0] at h
  exact coef_eq_zero hg i _ _ h.symm

/- English proof (translation)
Introduce `x`. Use `choose V g hA hE hu c hc using exists_chart hR hg i ζ x`. Use `choose y hy using hu`. Establish `hagree : ∀ (u : U) (v : V u), c (g u v) = c u` using `fun u v => coef_agree hR hg i ζ x (g (g u v)) (g u) _ _ (hc _) (hc u) (y _) v (hy _)`. Establish `hop : ∀ u, IsOpen (Set.range (g u))` using `fun u => by`.

Use `hE u` as an intermediate fact. Conclude with `(g u).isOpenMap.isOpen_range`. Set `f : LocallyConstant U (ZMod q)` to `⟨c, (IsLocallyConstant.iff_exists_open c).2 fun u => ⟨Set.range (g u), hop u, ⟨y u, hy u⟩, by`. Introduce and unpack `_ ⟨v, rfl⟩`. Conclude with `hagree u v⟩⟩`.

Use `⟨f, ((sec_ext_glue _ _ U).1 _ _ ?_)⟩` and prove the remaining obligations. Use `(loc_iff_etale_affine_points U (fun V g => Sec.res g (kap i ζ f) = Sec.res g x) ?_).2 fun u => ?_` and prove the remaining obligations. Introduce `V W g k h`. Rewrite using `[← res_res, h, res_res]`. Use `⟨V u, g u, hA u, hE u, ⟨y u, hy u⟩, ?_⟩` and prove the remaining obligations.

Establish `h` using `(hK q i U ζ f).1 (V u) (g u) (c u) (hagree u)`. Rewrite using `[h, hc u, ((hR q i U ζ).1 _ (g u)).1]`.
-/
theorem kap_surjective (hR : RepRoot) (hK : KapSpec) (hg : InGen) {q : ℕ} [NeZero q] (i : ℤ)
    {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) : Function.Surjective (kap i ζ) := by
  intro x
  choose V g hA hE hu c hc using exists_chart hR hg i ζ x
  choose y hy using hu
  have hagree : ∀ (u : U) (v : V u), c (g u v) = c u := fun u v =>
    coef_agree hR hg i ζ x (g (g u v)) (g u) _ _ (hc _) (hc u) (y _) v (hy _)
  have hop : ∀ u, IsOpen (Set.range (g u)) := fun u => by
    have := hE u
    exact (g u).isOpenMap.isOpen_range
  let f : LocallyConstant U (ZMod q) := ⟨c, (IsLocallyConstant.iff_exists_open c).2 fun u =>
    ⟨Set.range (g u), hop u, ⟨y u, hy u⟩, by
      rintro _ ⟨v, rfl⟩
      exact hagree u v⟩⟩
  refine ⟨f, ((sec_ext_glue _ _ U).1 _ _ ?_)⟩
  refine (loc_iff_etale_affine_points U (fun V g => Sec.res g (kap i ζ f) = Sec.res g x) ?_).2 fun u => ?_
  · intro V W g k h
    rw [← res_res, h, res_res]
  · refine ⟨V u, g u, hA u, hE u, ⟨y u, hy u⟩, ?_⟩
    have h := (hK q i U ζ f).1 (V u) (g u) (c u) (hagree u)
    rw [h, hc u, ((hR q i U ζ).1 _ (g u)).1]

/- English proof (translation)
Introduce `_ hR hK hg q _ i _ ζ` and use `⟨kap_injective hK hg i ζ, kap_surjective hR hK hg i ζ⟩`.
-/
theorem kapBij : LcCover → RepRoot → KapSpec → KapBij := fun _ hR hK hg q _ i _ ζ =>
  ⟨kap_injective hK hg i ζ, kap_surjective hR hK hg i ζ⟩

end GlobalTheory.CompanionTheory.KapBij
