import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedN
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.ClsSum

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace Formalism.L2.Geo

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type}

def InPW (p : ℕ) [Fact p.Prime] (a : DV.KW p) : Prop :=
  ∃ b : WittVector p (AlgebraicClosure (ZMod p)), algebraMap _ (DV.KW p) b = a ∧ b.coeff 0 = 0

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b', hb', h0⟩`. Take `rfl` from `IsFractionRing.injective (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p) hb'`. Conclude with `h0`. Introduce `h`.

Conclude with `⟨b, rfl, h⟩`.
-/
theorem inPW_algebraMap (p : ℕ) [Fact p.Prime] (b : WittVector p (AlgebraicClosure (ZMod p))) :
    InPW p (algebraMap _ (DV.KW p) b) ↔ b.coeff 0 = 0 := by
  constructor
  · rintro ⟨b', hb', h0⟩
    obtain rfl := IsFractionRing.injective (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p) hb'
    exact h0
  · intro h
    exact ⟨b, rfl, h⟩

def ComplexEmbeddingsCompatible (jc : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p) (τ : DV.Emb D p) (e : D.host.E →+* D.what₂.LL),
    (jc p la).comp τ = D.what₂.embLL.comp e →
      ∀ x : 𝓞 D.host.E, (InPW p (τ (x : D.host.E)) ↔ la.1.valuation D.what₂.LL (e (x : D.host.E)) < 1)

def CuspTieX (X : DivX D) : Prop :=
  ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ (c : X.Comp j) (x : (X.MjH j).V),
    X.geo.vanishOn (X.Yv j c) (X.Lw j c (DV.kapW D j)) (X.iMj j c x) (X.Ybd j c)

def FormsTieX (X : DivX D) (F : ShimFam D X.geo X.Lev)
    (eC : ∀ j, 1 ≤ j → j ≤ D.R.m → X.Comp j ≃ (F.U (datW D F.κg j)).Comp) : Prop :=
  ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (w : WeightFamilies.Wt D j), w.n = D.R.nV → wtOf w = DV.kapW D j →
    ∀ (c : X.Comp j) (x : (X.MjH j).V),
      ∃ f ∈ Submodule.span D.what₂.LL (Set.range (F.forms.cmp j w (eC j h1 h2 c))), HEq (X.iMj j c x) f

/- English proof (translation)
Substitute `hY` using the available equality. Take `rfl` from `eq_of_heq hΔ`. Take `rfl` from `eq_of_heq hff`. Conclude with `hf`.
-/
theorem mem_global_sections_transport (G : DV.Geo D.what₂.LL) {Y Y' : G.Var} (hY : Y = Y') {Δ : G.Dv Y} {Δ' : G.Dv Y'}
    (hΔ : HEq Δ Δ') {f : G.Fn Y} (hf : f ∈ G.H0 Y Δ) {f' : G.Fn Y'} (hff : HEq f f') : f' ∈ G.H0 Y' Δ' := by
  subst hY
  obtain rfl := eq_of_heq hΔ
  obtain rfl := eq_of_heq hff
  exact hf

/- English proof (translation)
Substitute `hY` using the available equality. Take `rfl` from `eq_of_heq hΔ`. Take `rfl` from `eq_of_heq hZ`. Take `rfl` from `eq_of_heq hff`. Conclude with `hf`.
-/
theorem vanish_transport (G : DV.Geo D.what₂.LL) {Y Y' : G.Var} (hY : Y = Y') {Δ : G.Dv Y} {Δ' : G.Dv Y'}
    (hΔ : HEq Δ Δ') {Z : G.Cl Y} {Z' : G.Cl Y'} (hZ : HEq Z Z') {f : G.Fn Y} (hf : G.vanishOn Y Δ f Z)
    {f' : G.Fn Y'} (hff : HEq f f') : G.vanishOn Y' Δ' f' Z' := by
  subst hY
  obtain rfl := eq_of_heq hΔ
  obtain rfl := eq_of_heq hZ
  obtain rfl := eq_of_heq hff
  exact hf

/- English proof (translation)
Introduce `j h1 h2 w _hn hw c x`. Use `set U := F.U (datW D F.κg j) with hU`. Establish `hwt : (fun τ i => DV.kapW D j τ (Fin.cast (datW_N D F.κg j) i)) = wtOfN (datW D F.κg j).N w`. Use function extensionality and compare the values at `τ i`. Rewrite using `[← hw]`.

Both sides reduce to the same expression. Establish `hFn : ∀ c0 : X.Comp j, X.geo.Fn (X.Yv j c0) = X.geo.Fn (U.alg.Yv (eC j h1 h2 c0))` using `fun c0 => by`. Rewrite using `[hT.geo.yv j h1 h2 c0]`. Set `t : ∀ c0 : X.Comp j, X.geo.Fn (U.alg.Yv (eC j h1 h2 c0))` to `fun c0 => cast (hFn c0) (X.iMj j c0 x)`. Establish `ht : ∀ c0, HEq (t c0) (X.iMj j c0 x)` using `fun c0 => cast_heq _ _`.

Set `s : ∀ c' : U.Comp, X.geo.Fn (U.alg.Yv c')` to `fun c' => (eC j h1 h2).apply_symm_apply c' ▸ t ((eC j h1 h2).symm c')`. Establish `hs : ∀ c', HEq (s c') (X.iMj j ((eC j h1 h2).symm c') x)` using `fun c' => by`. Use `HEq.trans ?_ (ht _)` and prove the remaining obligations. Establish `key : ∀ {a b : U.Comp} (h : a = b) (v : X.geo.Fn (U.alg.Yv a)), HEq (h ▸ v : X.geo.Fn (U.alg.Yv b)) v`. Introduce `a b h v`.

Substitute `h` using the available equality. Both sides reduce to the same expression. Conclude with `key _ _`. Establish `hmem : ∀ c', s c' ∈ X.geo.H0 (U.alg.Yv c') (U.alg.Lw c' (wtOfN (datW D F.κg j).N w)) ∧ X.geo.vanishOn (U.alg.Yv c') (U.alg.Lw c' (wtOfN (datW D F.κg j).N w)) (s c') (U.alg.Ybd c')`. Introduce `c'`.

Establish `hyv` using `hT.geo.yv j h1 h2 ((eC j h1 h2).symm c')`. Rewrite `hyv` using `[Equiv.apply_symm_apply]`. Establish `hlw` using `hT.geo.lw j h1 h2 ((eC j h1 h2).symm c') (DV.kapW D j)`. Establish `hbd` using `hT.geo.ybd j h1 h2 ((eC j h1 h2).symm c')`. Rewrite `hlw` using `[hwt]`.

Establish `e1 : HEq (U.alg.Lw (eC j h1 h2 ((eC j h1 h2).symm c')) (wtOfN (datW D F.κg j).N w)) (U.alg.Lw c' (wtOfN (datW D F.κg j).N w))` using `by rw [Equiv.apply_symm_apply]`. Establish `e2 : HEq (U.alg.Ybd (eC j h1 h2 ((eC j h1 h2).symm c'))) (U.alg.Ybd c')` using `by rw [Equiv.apply_symm_apply]`. Conclude with `⟨mem_global_sections_transport X.geo hyv (hlw.trans e1) (X.iMj_mem j _ x) (hs c').symm, vanish_transport X.geo hyv (hlw.trans e1) (hbd.trans e2) (hC j h1 h2 _ x) (hs c').symm⟩`. Establish `hspan` using `F.forms.cmp_span j h1 h2 w s hmem`. Establish `hmap` using `Submodule.mem_map_of_mem (f := LinearMap.proj (R := D.what₂.LL) (φ := fun c' : U.Comp => X.geo.Fn (U.alg.Yv c')) (eC j h1 h2 c)) hspan`.

Rewrite `hmap` using `[Submodule.map_span]`. Use `⟨s (eC j h1 h2 c), ?_, ?_⟩` and prove the remaining obligations. Use `(Submodule.span_mono ?_) hmap` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨G, rfl⟩, rfl⟩`. Conclude with `⟨G, rfl⟩`.

Use `HEq.trans ?_ (hs _).symm` and prove the remaining obligations. Rewrite using `[Equiv.symm_apply_apply]`.
-/
theorem formsTieX_of_cusp (X : DivX D) (F : ShimFam D X.geo X.Lev)
    (ePl : ∀ (p : ℕ) [Fact p.Prime], X.PlP p ≃ PlL D p)
    (eC : ∀ j, 1 ≤ j → j ≤ D.R.m → X.Comp j ≃ (F.U (datW D F.κg j)).Comp)
    (hT : TiedX (jC := F.jC) (ng := F.ng) X F.levPr F.levPr_prime F.κg ePl F.U eC)
    (hC : CuspTieX X) : FormsTieX X F eC := by
  intro j h1 h2 w _hn hw c x
  set U := F.U (datW D F.κg j) with hU
  have hwt : (fun τ i => DV.kapW D j τ (Fin.cast (datW_N D F.κg j) i)) = wtOfN (datW D F.κg j).N w := by
    funext τ i
    rw [← hw]
    rfl
  have hFn : ∀ c0 : X.Comp j, X.geo.Fn (X.Yv j c0) = X.geo.Fn (U.alg.Yv (eC j h1 h2 c0)) := fun c0 => by
    rw [hT.geo.yv j h1 h2 c0]
  let t : ∀ c0 : X.Comp j, X.geo.Fn (U.alg.Yv (eC j h1 h2 c0)) := fun c0 => cast (hFn c0) (X.iMj j c0 x)
  have ht : ∀ c0, HEq (t c0) (X.iMj j c0 x) := fun c0 => cast_heq _ _
  let s : ∀ c' : U.Comp, X.geo.Fn (U.alg.Yv c') := fun c' =>
    (eC j h1 h2).apply_symm_apply c' ▸ t ((eC j h1 h2).symm c')
  have hs : ∀ c', HEq (s c') (X.iMj j ((eC j h1 h2).symm c') x) := fun c' => by
    refine HEq.trans ?_ (ht _)
    have key : ∀ {a b : U.Comp} (h : a = b) (v : X.geo.Fn (U.alg.Yv a)),
        HEq (h ▸ v : X.geo.Fn (U.alg.Yv b)) v := by
      intro a b h v; subst h; rfl
    exact key _ _
  have hmem : ∀ c', s c' ∈ X.geo.H0 (U.alg.Yv c') (U.alg.Lw c' (wtOfN (datW D F.κg j).N w)) ∧
      X.geo.vanishOn (U.alg.Yv c') (U.alg.Lw c' (wtOfN (datW D F.κg j).N w)) (s c') (U.alg.Ybd c') := by
    intro c'
    have hyv := hT.geo.yv j h1 h2 ((eC j h1 h2).symm c')
    rw [Equiv.apply_symm_apply] at hyv
    have hlw := hT.geo.lw j h1 h2 ((eC j h1 h2).symm c') (DV.kapW D j)
    have hbd := hT.geo.ybd j h1 h2 ((eC j h1 h2).symm c')
    rw [hwt] at hlw
    have e1 : HEq (U.alg.Lw (eC j h1 h2 ((eC j h1 h2).symm c')) (wtOfN (datW D F.κg j).N w))
        (U.alg.Lw c' (wtOfN (datW D F.κg j).N w)) := by rw [Equiv.apply_symm_apply]
    have e2 : HEq (U.alg.Ybd (eC j h1 h2 ((eC j h1 h2).symm c'))) (U.alg.Ybd c') := by rw [Equiv.apply_symm_apply]
    exact ⟨mem_global_sections_transport X.geo hyv (hlw.trans e1) (X.iMj_mem j _ x) (hs c').symm,
      vanish_transport X.geo hyv (hlw.trans e1) (hbd.trans e2) (hC j h1 h2 _ x) (hs c').symm⟩
  have hspan := F.forms.cmp_span j h1 h2 w s hmem
  have hmap := Submodule.mem_map_of_mem (f := LinearMap.proj (R := D.what₂.LL)
    (φ := fun c' : U.Comp => X.geo.Fn (U.alg.Yv c')) (eC j h1 h2 c)) hspan
  rw [Submodule.map_span] at hmap
  refine ⟨s (eC j h1 h2 c), ?_, ?_⟩
  · refine (Submodule.span_mono ?_) hmap
    rintro _ ⟨_, ⟨G, rfl⟩, rfl⟩
    exact ⟨G, rfl⟩
  · refine HEq.trans ?_ (hs _).symm
    rw [Equiv.symm_apply_apply]

def IsoSp (S S' : letI := D.host.cmStar; HSpace D.host.E) : Prop :=
  letI := D.host.cmStar
  ∃ ι : S.V ≃ₗ[D.host.E] S'.V, HSpace.IsIsomEmb S S' ι.toLinearMap ∧
    S.L0.map (ι.toLinearMap.restrictScalars (𝓞 D.host.E)) = S'.L0

/- English proof (translation)
Take `⟨ι, -, -⟩` from `h`. Use `letI := D.host.cmStar`. Rewrite using `[← S.rank_eq, ← S'.rank_eq]`. Conclude with `ι.finrank_eq`.
-/
theorem IsoSp.rank_eq {S S' : letI := D.host.cmStar; HSpace D.host.E} (h : IsoSp S S') :
    (letI := D.host.cmStar; S.rank) = (letI := D.host.cmStar; S'.rank) := by
  obtain ⟨ι, -, -⟩ := h
  letI := D.host.cmStar
  rw [← S.rank_eq, ← S'.rank_eq]
  exact ι.finrank_eq

def IsoInv (F : ShimFam D G Lev) : Prop :=
  ∀ (w w' : Dat D Lev), IsoSp w.S w'.S → w.κ = w'.κ → w.j = w'.j → ∀ (h : w.Indef) (h' : w'.Indef),
    toShimX (F.U w) h (F.levPr w.κ) (F.levPr_prime w.κ) = toShimX (F.U w') h' (F.levPr w'.κ) (F.levPr_prime w'.κ)

def LevInTie (F : ShimFam D G Lev) (inK : Lev → ℕ → Prop) : Prop :=
  ∀ (w : Dat D Lev) (M : ℕ), (F.U w).pad.levIn M ↔ inK w.κ M

def LevPinW (F : ShimFam D G Lev) : Prop :=
  Nonempty ((F.U (datW D F.κg D.R.m)).Comp ≃ Def.XDef D)

def GeoTiedP (X : DivX D) (inK : X.Lev → ℕ → Prop) : Prop :=
  ∃ (F : ShimFam D X.geo X.Lev) (ePl : ∀ (p : ℕ) [Fact p.Prime], X.PlP p ≃ PlL D p)
    (eC : ∀ j, 1 ≤ j → j ≤ D.R.m → X.Comp j ≃ (F.U (datW D F.κg j)).Comp),
    TiedX (jC := F.jC) (ng := F.ng) X F.levPr F.levPr_prime F.κg ePl F.U eC ∧ ComplexEmbeddingsCompatible F.jC ∧ CuspTieX X ∧
      IsoInv F ∧ LevInTie F inK

def GeoTiedPL (X : DivX D) (inK : X.Lev → ℕ → Prop) : Prop :=
  ∃ (F : ShimFam D X.geo X.Lev) (ePl : ∀ (p : ℕ) [Fact p.Prime], X.PlP p ≃ PlL D p)
    (eC : ∀ j, 1 ≤ j → j ≤ D.R.m → X.Comp j ≃ (F.U (datW D F.κg j)).Comp),
    TiedX (jC := F.jC) (ng := F.ng) X F.levPr F.levPr_prime F.κg ePl F.U eC ∧ ComplexEmbeddingsCompatible F.jC ∧ CuspTieX X ∧
      IsoInv F ∧ LevInTie F inK ∧ LevPinW F

/- English proof (translation)
Take `⟨F, ePl, eC, hT, _, _, _, _⟩` from `h`. Conclude with `⟨F, ePl, eC, hT⟩`.
-/
theorem GeoTiedP.geoTied {X : DivX D} {inK : X.Lev → ℕ → Prop} (h : GeoTiedP X inK) : GeoTied X := by
  obtain ⟨F, ePl, eC, hT, _, _, _, _⟩ := h
  exact ⟨F, ePl, eC, hT⟩

/- English proof (translation)
Take `⟨F, ePl, eC, hT, -, hC, -, -⟩` from `h`. Conclude with `⟨F, eC, formsTieX_of_cusp X F ePl eC hT hC⟩`.
-/
theorem GeoTiedP.formsTieX {X : DivX D} {inK : X.Lev → ℕ → Prop} (h : GeoTiedP X inK) :
    ∃ (F : ShimFam D X.geo X.Lev) (eC : ∀ j, 1 ≤ j → j ≤ D.R.m → X.Comp j ≃ (F.U (datW D F.κg j)).Comp),
      FormsTieX X F eC := by
  obtain ⟨F, ePl, eC, hT, -, hC, -, -⟩ := h
  exact ⟨F, eC, formsTieX_of_cusp X F ePl eC hT hC⟩

/- English proof (translation)
Take `⟨F, ePl, eC, h1, h2, h3, h4, h5, -⟩` from `h`. Conclude with `⟨F, ePl, eC, h1, h2, h3, h4, h5⟩`.
-/
theorem GeoTiedPL.geoTiedP {X : DivX D} {inK : X.Lev → ℕ → Prop} (h : GeoTiedPL X inK) : GeoTiedP X inK := by
  obtain ⟨F, ePl, eC, h1, h2, h3, h4, h5, -⟩ := h
  exact ⟨F, ePl, eC, h1, h2, h3, h4, h5⟩

variable (D)

def famFlJ (jc : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (KO : Type) [Field KO] [NumberField KO]
    (eO : 𝓞 KO ≃+* D.what₂.O) (kL : KO →+* D.what₂.LL) (kL_eO : ∀ x : 𝓞 KO, kL (x : KO) = D.what₂.OtoLL (eO x)) :
    ShimFam D (geoDegenerate D.what₂.LL D.what₂.Tau) PUnit where
  levPr := fun _ => Finset.univ.image D.host.g
  levPr_prime := fun _ p hp => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hp
    exact D.host.g_prime i
  κg := PUnit.unit
  levPr_κg := rfl
  jC := jc
  ng := ng1
  U := fun w => shimUFl D jc w
  forms := formsFl D KO eO kL kL_eO _ _ _ (fun _ _ => true)

/- English proof (translation)
Introduce `w w' hiso _ hj h h'`. Conclude with `(toShimX_fl D jc w h _).trans ((shimXFl_congr D jc _ _ _ _ hiso.rank_eq hj).trans (toShimX_fl D jc w' h' _).symm)`.
-/
theorem isoInv_famFlJ (jc : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (KO : Type) [Field KO]
    [NumberField KO] (eO : 𝓞 KO ≃+* D.what₂.O) (kL : KO →+* D.what₂.LL)
    (kL_eO : ∀ x : 𝓞 KO, kL (x : KO) = D.what₂.OtoLL (eO x)) : IsoInv (famFlJ D jc KO eO kL kL_eO) := by
  intro w w' hiso _ hj h h'
  exact (toShimX_fl D jc w h _).trans ((shimXFl_congr D jc _ _ _ _ hiso.rank_eq hj).trans
    (toShimX_fl D jc w' h' _).symm)

/- English proof (translation)
Introduce `_ _` and use `Iff.rfl`.
-/
theorem levInTie_famFlJ (jc : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (KO : Type) [Field KO]
    [NumberField KO] (eO : 𝓞 KO ≃+* D.what₂.O) (kL : KO →+* D.what₂.LL)
    (kL_eO : ∀ x : 𝓞 KO, kL (x : KO) = D.what₂.OtoLL (eO x)) :
    LevInTie (famFlJ D jc KO eO kL kL_eO) (fun _ _ => True) :=
  fun _ _ => Iff.rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨divXFl D jc X0, famFlJ D jc KO eO kL kL_eO, fun p _ => Equiv.refl _, fun _ _ _ => Equiv.refl _, tiedX_fl D jc X0, hjc, fun _ _ _ _ _ => trivial, isoInv_famFlJ D jc KO eO kL kL_eO, levInTie_famFlJ D jc KO eO kL kL_eO⟩`.
-/
theorem geoTiedP_satisfiable (X0 : DivX D) (KO : Type) [Field KO] [NumberField KO] (eO : 𝓞 KO ≃+* D.what₂.O)
    (kL : KO →+* D.what₂.LL) (kL_eO : ∀ x : 𝓞 KO, kL (x : KO) = D.what₂.OtoLL (eO x))
    (jc : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (hjc : ComplexEmbeddingsCompatible jc) :
    ∃ X : DivX D, GeoTiedP X (fun _ _ => True) :=
  ⟨divXFl D jc X0, famFlJ D jc KO eO kL kL_eO, fun p _ => Equiv.refl _, fun _ _ _ => Equiv.refl _,
    tiedX_fl D jc X0, hjc, fun _ _ _ _ _ => trivial, isoInv_famFlJ D jc KO eO kL kL_eO,
    levInTie_famFlJ D jc KO eO kL kL_eO⟩

end Formalism.L2.Geo
