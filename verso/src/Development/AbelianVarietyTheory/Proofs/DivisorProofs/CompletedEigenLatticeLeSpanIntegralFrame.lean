import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralInIntegralEigenbasis

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
open Limits MonObj

noncomputable section
namespace GlobalTheory.EigLatSpan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

/- English proof (translation)
Take `⟨U, hU, hprod⟩` from `h`. Set `Q : Fin k → (epsR S ⟶ t.G)` to `fun j => Over.homMk (spMap (epsMul (a j)) ≫ (q j).left) (by show (spMap (epsMul (a j)) ≫ (q j).left) ≫ t.G.hom = spMap (algebraMap S (DualNumber S))`. Rewrite using `[Category.assoc, Over.w (q j)]`. Conclude with `(GlobalTheory.IntLie.spMap_comp₂ _ _).trans (congrArg spMap (GlobalTheory.IntLie.epsMul_alg (a j))))`. Use `⟨Q, fun j => rfl, ?_⟩` and prove the remaining obligations.

Establish `hP` using `GlobalTheory.IntLie.prod_push m.cart (epsR S) (tEps x) (𝟙 _) (Category.id_comp _) Q U (fun j => by`. Rewrite using `[Category.id_comp, hU j]`. Conclude with `Category.assoc _ _ _)`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `m.cart.1.hom_ext` to reduce the goal to its premises.

Rewrite using `[hP, Category.id_comp, hprod]`. Rewrite using `[Over.w z, Over.w ((List.ofFn Q).prod)]`.
-/
theorem lieComb_of_combAt {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S]
    {x : Sp S ⟶ Xo.X} {t : SAB H (Sp S)} (m : SABMap t Xo.univ.t x) {k : ℕ} (q : Fin k → (epsR S ⟶ t.G))
    (a : Fin k → S) (z : epsR S ⟶ t.G) (h : IsCombAt x (fun j => (q j).left ≫ m.φ) a (z.left ≫ m.φ)) :
    IsLieComb a q z := by
  obtain ⟨U, hU, hprod⟩ := h
  let Q : Fin k → (epsR S ⟶ t.G) := fun j => Over.homMk (spMap (epsMul (a j)) ≫ (q j).left) (by
    show (spMap (epsMul (a j)) ≫ (q j).left) ≫ t.G.hom = spMap (algebraMap S (DualNumber S))
    rw [Category.assoc, Over.w (q j)]
    exact (GlobalTheory.IntLie.spMap_comp₂ _ _).trans (congrArg spMap (GlobalTheory.IntLie.epsMul_alg (a j))))
  refine ⟨Q, fun j => rfl, ?_⟩
  have hP := GlobalTheory.IntLie.prod_push m.cart (epsR S) (tEps x) (𝟙 _) (Category.id_comp _) Q U (fun j => by
    rw [Category.id_comp, hU j]; exact Category.assoc _ _ _)
  apply Over.OverMorphism.ext
  apply m.cart.1.hom_ext
  · rw [hP, Category.id_comp, hprod]
  · rw [Over.w z, Over.w ((List.ofFn Q).prod)]

end GlobalTheory.EigLatSpan

noncomputable section
namespace GlobalTheory.EigLatSpan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

/- English proof (translation)
Use `haveI : IsCommMonObj F.P₀.A := F.P₀.isAb.comm`. Use `haveI := F.P₀.smoothDim`. Establish `hs : Smooth F.P₀.A.hom` using `SmoothOfRelativeDimension.smooth F.P₀.g _`. Establish `hF` using `F.fib.2.1`. Establish `hc : (n'.φ ≫ m2.φ) ≫ B.pol.A.hom = (t'.G.hom ≫ spMap iK) ≫ spMap (algebraMap (𝓞 K) K)`.

Rewrite using `[Category.assoc, m2.cart.1.w, ← Category.assoc, n'.cart.1.w, Category.assoc]`. Set `ψ : t'.G.left ⟶ F.P₀.A.left` to `hF.1.lift (n'.φ ≫ m2.φ) (t'.G.hom ≫ spMap iK) hc`. Establish `hψ1 : ψ ≫ F.φ = n'.φ ≫ m2.φ` using `hF.1.lift_fst _ _ _`. Establish `hψ2 : ψ ≫ F.P₀.A.hom = t'.G.hom ≫ spMap iK` using `hF.1.lift_snd _ _ _`. Establish `hout : IsPullback (ψ ≫ F.φ) t'.G.hom B.pol.A.hom (spMap iK ≫ spMap (algebraMap (𝓞 K) K))`.

Rewrite using `[hψ1]`. Conclude with `IsPullback.paste_horiz n'.cart.1 m2.cart.1`. Establish `hpull : IsGrpPullback t'.G F.P₀.A (spMap iK) ψ`. Use `⟨IsPullback.of_right hout hψ2 hF.1, ?_⟩` and prove the remaining obligations. Introduce `T x y x₀ y₀ hx hy`.

Set `T₁ : Over (Sp K)` to `Over.mk (T.hom ≫ spMap iK)`. Set `x' : T₁ ⟶ t₀.G` to `Over.homMk (x.left ≫ n'.φ) (by show (x.left ≫ n'.φ) ≫ t₀.G.hom = T.hom ≫ spMap iK`. Rewrite using `[Category.assoc, n'.cart.1.w, ← Category.assoc, Over.w x])`. Set `y' : T₁ ⟶ t₀.G` to `Over.homMk (y.left ≫ n'.φ) (by show (y.left ≫ n'.φ) ≫ t₀.G.hom = T.hom ≫ spMap iK`. Rewrite using `[Category.assoc, n'.cart.1.w, ← Category.assoc, Over.w y])`.

Set `x'' : Over.mk (T₁.hom ≫ spMap (algebraMap (𝓞 K) K)) ⟶ B.t.G` to `Over.homMk (x.left ≫ n'.φ ≫ m2.φ) (by show (x.left ≫ n'.φ ≫ m2.φ) ≫ B.t.G.hom = (T.hom ≫ spMap iK) ≫ spMap (algebraMap (𝓞 K) K)`. Rewrite using `[Category.assoc, Category.assoc, m2.cart.1.w, ← Category.assoc n'.φ, n'.cart.1.w, ← Category.assoc, ← Category.assoc, Over.w x, Category.assoc])`. Set `y'' : Over.mk (T₁.hom ≫ spMap (algebraMap (𝓞 K) K)) ⟶ B.t.G` to `Over.homMk (y.left ≫ n'.φ ≫ m2.φ) (by show (y.left ≫ n'.φ ≫ m2.φ) ≫ B.t.G.hom = (T.hom ≫ spMap iK) ≫ spMap (algebraMap (𝓞 K) K)`. Rewrite using `[Category.assoc, Category.assoc, m2.cart.1.w, ← Category.assoc n'.φ, n'.cart.1.w, ← Category.assoc, ← Category.assoc, Over.w y, Category.assoc])`. Establish `k1 : (x' * y').left = (x * y).left ≫ n'.φ` using `n'.cart.2 T x y x' y' rfl rfl`.

Establish `k2 : (x'' * y'').left = (x' * y').left ≫ m2.φ` using `m2.cart.2 T₁ x' y' x'' y'' rfl rfl`. Establish `k3 : (x'' * y'').left = (x₀ * y₀).left ≫ F.φ` using `hF.2 T₁ x₀ y₀ x'' y'' (by show x.left ≫ n'.φ ≫ m2.φ = x₀.left ≫ F.φ; rw [hx, Category.assoc, hψ1]) (by show y.left ≫ n'.φ ≫ m2.φ = y₀.left ≫ F.φ; rw [hy, Category.assoc, hψ1])`. Apply `hF.1.hom_ext` to reduce the goal to its premises. Rewrite using `[← k3, k2, k1, Category.assoc, Category.assoc, hψ1]`. Rewrite using `[Over.w (x₀ * y₀), Category.assoc, hψ2, ← Category.assoc, Over.w (x * y)]`.

Both sides reduce to the same expression. Take `⟨e, he, hev⟩` from `GlobalTheory.exists_isLieBasis_baseChange K L iK F.P₀.A t'.G ψ hpull hs F.P₀.g F.v F.basis`. Use `⟨e, he, fun d w z hw hz => ?_⟩` and prove the remaining obligations. Take `⟨U, hU, rfl⟩` from `hw`. Establish `hg : spMap (Formalism.L2.Pj.dualMap iK) ≫ (epsR K).hom = (epsR L).hom ≫ spMap iK` using `by show spMap (Formalism.L2.Pj.dualMap iK) ≫ spMap (algebraMap K (DualNumber K)) = spMap (algebraMap L (DualNumber L)) ≫ spMap iK`.

Rewrite using `[GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.dualMap_alg]`. Set `Z : Fin F.P₀.g → (epsR L ⟶ t'.G)` to `fun j => Over.homMk (spMap (epsMul (iK (d j))) ≫ (e j).left) (by show (spMap (epsMul (iK (d j))) ≫ (e j).left) ≫ t'.G.hom = spMap (algebraMap L (DualNumber L))`. Rewrite using `[Category.assoc, Over.w (e j)]`. Conclude with `(GlobalTheory.IntLie.spMap_comp₂ _ _).trans (congrArg spMap (GlobalTheory.IntLie.epsMul_alg _)))`. Use `⟨Z, fun j => rfl, ?_⟩` and prove the remaining obligations.

Establish `hP` using `GlobalTheory.IntLie.prod_push hpull (epsR L) (epsR K) (spMap (Formalism.L2.Pj.dualMap iK)) hg Z U (fun j => by show (spMap (epsMul (iK (d j))) ≫ (e j).left) ≫ ψ = _`. Rewrite using `[hU j, Category.assoc, hev j, ← Category.assoc, ← Category.assoc, GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂]`. Use `congr 2`. Conclude with `(GlobalTheory.IntLie.dualMap_epsMul iK (d j)).symm)`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Apply `hpull.1.hom_ext` to reduce the goal to its premises. Rewrite using `[hP]`. Apply `hF.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hψ1, hz, Category.assoc]`. Simplify using `only [Category.assoc]`.

Rewrite using `[hψ2, Over.w ((List.ofFn U).prod), ← Category.assoc, Over.w z]`. Conclude with `hg.symm`. Rewrite using `[Over.w z, Over.w ((List.ofFn Z).prod)]`.
-/
theorem baseChange_basis {K : Type} [Field K] [NumberField K] (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K))
    (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) {L : Type} [Field L] (iK : K →+* L)
    (t' : SAB H (Sp L)) (n' : SABMap t' t₀ (spMap iK)) :
    ∃ e : Fin F.P₀.g → (epsR L ⟶ t'.G), IsLieBasis e ∧
      ∀ (d : Fin F.P₀.g → K) (w : epsR K ⟶ F.P₀.A) (z : epsR L ⟶ t'.G), IsLieComb d F.v w →
        z.left ≫ n'.φ ≫ m2.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ w.left ≫ F.φ → IsLieComb (fun k => iK (d k)) e z := by
  haveI : IsCommMonObj F.P₀.A := F.P₀.isAb.comm
  haveI := F.P₀.smoothDim
  have hs : Smooth F.P₀.A.hom := SmoothOfRelativeDimension.smooth F.P₀.g _
  have hF := F.fib.2.1
  have hc : (n'.φ ≫ m2.φ) ≫ B.pol.A.hom = (t'.G.hom ≫ spMap iK) ≫ spMap (algebraMap (𝓞 K) K) := by
    rw [Category.assoc, m2.cart.1.w, ← Category.assoc, n'.cart.1.w, Category.assoc]
  let ψ : t'.G.left ⟶ F.P₀.A.left := hF.1.lift (n'.φ ≫ m2.φ) (t'.G.hom ≫ spMap iK) hc
  have hψ1 : ψ ≫ F.φ = n'.φ ≫ m2.φ := hF.1.lift_fst _ _ _
  have hψ2 : ψ ≫ F.P₀.A.hom = t'.G.hom ≫ spMap iK := hF.1.lift_snd _ _ _
  have hout : IsPullback (ψ ≫ F.φ) t'.G.hom B.pol.A.hom (spMap iK ≫ spMap (algebraMap (𝓞 K) K)) := by
    rw [hψ1]
    exact IsPullback.paste_horiz n'.cart.1 m2.cart.1
  have hpull : IsGrpPullback t'.G F.P₀.A (spMap iK) ψ := by
    refine ⟨IsPullback.of_right hout hψ2 hF.1, ?_⟩
    intro T x y x₀ y₀ hx hy
    let T₁ : Over (Sp K) := Over.mk (T.hom ≫ spMap iK)
    let x' : T₁ ⟶ t₀.G := Over.homMk (x.left ≫ n'.φ) (by
      show (x.left ≫ n'.φ) ≫ t₀.G.hom = T.hom ≫ spMap iK
      rw [Category.assoc, n'.cart.1.w, ← Category.assoc, Over.w x])
    let y' : T₁ ⟶ t₀.G := Over.homMk (y.left ≫ n'.φ) (by
      show (y.left ≫ n'.φ) ≫ t₀.G.hom = T.hom ≫ spMap iK
      rw [Category.assoc, n'.cart.1.w, ← Category.assoc, Over.w y])
    let x'' : Over.mk (T₁.hom ≫ spMap (algebraMap (𝓞 K) K)) ⟶ B.t.G := Over.homMk (x.left ≫ n'.φ ≫ m2.φ) (by
      show (x.left ≫ n'.φ ≫ m2.φ) ≫ B.t.G.hom = (T.hom ≫ spMap iK) ≫ spMap (algebraMap (𝓞 K) K)
      rw [Category.assoc, Category.assoc, m2.cart.1.w, ← Category.assoc n'.φ, n'.cart.1.w, ← Category.assoc,
        ← Category.assoc, Over.w x, Category.assoc])
    let y'' : Over.mk (T₁.hom ≫ spMap (algebraMap (𝓞 K) K)) ⟶ B.t.G := Over.homMk (y.left ≫ n'.φ ≫ m2.φ) (by
      show (y.left ≫ n'.φ ≫ m2.φ) ≫ B.t.G.hom = (T.hom ≫ spMap iK) ≫ spMap (algebraMap (𝓞 K) K)
      rw [Category.assoc, Category.assoc, m2.cart.1.w, ← Category.assoc n'.φ, n'.cart.1.w, ← Category.assoc,
        ← Category.assoc, Over.w y, Category.assoc])
    have k1 : (x' * y').left = (x * y).left ≫ n'.φ := n'.cart.2 T x y x' y' rfl rfl
    have k2 : (x'' * y'').left = (x' * y').left ≫ m2.φ := m2.cart.2 T₁ x' y' x'' y'' rfl rfl
    have k3 : (x'' * y'').left = (x₀ * y₀).left ≫ F.φ := hF.2 T₁ x₀ y₀ x'' y''
      (by show x.left ≫ n'.φ ≫ m2.φ = x₀.left ≫ F.φ; rw [hx, Category.assoc, hψ1])
      (by show y.left ≫ n'.φ ≫ m2.φ = y₀.left ≫ F.φ; rw [hy, Category.assoc, hψ1])
    apply hF.1.hom_ext
    · rw [← k3, k2, k1, Category.assoc, Category.assoc, hψ1]
    · rw [Over.w (x₀ * y₀), Category.assoc, hψ2, ← Category.assoc, Over.w (x * y)]
      rfl
  obtain ⟨e, he, hev⟩ := GlobalTheory.exists_isLieBasis_baseChange K L iK F.P₀.A t'.G ψ hpull hs F.P₀.g F.v F.basis
  refine ⟨e, he, fun d w z hw hz => ?_⟩
  obtain ⟨U, hU, rfl⟩ := hw
  have hg : spMap (Formalism.L2.Pj.dualMap iK) ≫ (epsR K).hom = (epsR L).hom ≫ spMap iK := by
    show spMap (Formalism.L2.Pj.dualMap iK) ≫ spMap (algebraMap K (DualNumber K)) =
      spMap (algebraMap L (DualNumber L)) ≫ spMap iK
    rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.dualMap_alg]
  let Z : Fin F.P₀.g → (epsR L ⟶ t'.G) := fun j => Over.homMk (spMap (epsMul (iK (d j))) ≫ (e j).left) (by
    show (spMap (epsMul (iK (d j))) ≫ (e j).left) ≫ t'.G.hom = spMap (algebraMap L (DualNumber L))
    rw [Category.assoc, Over.w (e j)]
    exact (GlobalTheory.IntLie.spMap_comp₂ _ _).trans (congrArg spMap (GlobalTheory.IntLie.epsMul_alg _)))
  refine ⟨Z, fun j => rfl, ?_⟩
  have hP := GlobalTheory.IntLie.prod_push hpull (epsR L) (epsR K) (spMap (Formalism.L2.Pj.dualMap iK)) hg Z U (fun j => by
    show (spMap (epsMul (iK (d j))) ≫ (e j).left) ≫ ψ = _
    rw [hU j, Category.assoc, hev j, ← Category.assoc, ← Category.assoc, GlobalTheory.IntLie.spMap_comp₂,
      GlobalTheory.IntLie.spMap_comp₂]
    congr 2
    exact (GlobalTheory.IntLie.dualMap_epsMul iK (d j)).symm)
  apply Over.OverMorphism.ext
  apply hpull.1.hom_ext
  · rw [hP]
    apply hF.1.hom_ext
    · rw [Category.assoc, hψ1, hz, Category.assoc]
    · simp only [Category.assoc]
      rw [hψ2, Over.w ((List.ofFn U).prod), ← Category.assoc, Over.w z]
      exact hg.symm
  · rw [Over.w z, Over.w ((List.ofFn Z).prod)]

/- English proof (translation)
Establish `hB1 : (1 : ptOver (𝓞 K) (𝓞 K) ⟶ B.t.G).left = η[B.t.G].left`. Establish `e : (1 : ptOver (𝓞 K) (𝓞 K) ⟶ B.t.G) = CartesianMonoidalCategory.toUnit _ ≫ η[B.t.G]` using `rfl`. Rewrite using `[e, Over.comp_left]`. Establish `e2 : (CartesianMonoidalCategory.toUnit (ptOver (𝓞 K) (𝓞 K))).left = 𝟙 (Sp (𝓞 K))`. Use `Over.w (CartesianMonoidalCategory.toUnit (ptOver (𝓞 K) (𝓞 K)))` as an intermediate fact.

Conclude with `((Category.comp_id _).symm.trans this).trans (Spec.map_id _)`. Rewrite using `[e2]`. Conclude with `Category.id_comp _`. Establish `hpt : ∀ (R : Type) [CommRing R], spMap (algebraMap R R) = 𝟙 (Sp R)` using `fun R _ => by`. Rewrite using `[Algebra.algebraMap_self]`.

Conclude with `Spec.map_id _`. Prove the components needed by the constructor for the conclusion. Unfold `IsTan`. Apply `n.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hW, ← Category.assoc, GlobalTheory.IntLie.spMap_comp₂]`.

Rewrite using `[GlobalTheory.IntLie.one_push n.cart (ptOver T.V T.V) (ptOver (𝓞 K) (𝓞 K)) (spMap ρV) (by simp only [Over.mk_hom, hpt]; exact (Category.comp_id _).trans (Category.id_comp _).symm), hB1, ← hu, ← Category.assoc, GlobalTheory.IntLie.spMap_comp₂]`. Use `congr 2`. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[Formalism.L2.Pj.dualMap]`.

Rewrite using `[Category.assoc, Over.w W, Over.w (1 : ptOver T.V T.V ⟶ G.G)] show spMap (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom ≫ spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) = spMap (algebraMap T.V T.V)`. Rewrite using `[GlobalTheory.IntLie.spMap_comp₂]`. Use `congr 1`. Introduce `a z hz`. Establish `hzρ : z = ρV (tt a)`.

Apply `IsFractionRing.injective T.V T.Fr` to reduce the goal to its premises. Rewrite using `[hz]`. Use `congrArg (fun f => f (tt a)) hρV` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`. Rewrite using `[this]`.

Use `show iK (algebraMap c.F K (embK c ρ a)) = iK (algebraMap (𝓞 K) K (tt a))`. Rewrite using `[← htt]`. Substitute `hzρ` using the available equality. Take `⟨U, hU, hprod⟩` from `he a`. Establish `hU0 : (u₀ ≫ B.t.act.act a).left = spMap (epsMul (tt a)) ≫ u₀.left`.

Rewrite using `[hprod]`. Simplify using `only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, _root_.mul_one]`. Conclude with `hU 0`. Apply `n.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Over.comp_left, Category.assoc, n.act a, ← Category.assoc, hW, Category.assoc, ← Over.comp_left, hU0, Category.assoc (spMap (epsMul (ρV (tt a)))) W.left n.φ, hW, ← Category.assoc, ← Category.assoc, GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.In …`.

Rewrite using `[Over.comp_left, Category.assoc, Over.w (G.act.act a), Category.assoc, Over.w W] show spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) = spMap (epsMul (ρV (tt a))) ≫ spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V))`. Rewrite using `[GlobalTheory.IntLie.spMap_comp₂, ← RingHom.comp_assoc, GlobalTheory.IntLie.epsMul_alg]`.
-/
theorem isTan_isEigV {l : Level H} (c : Coeff l) {K : Type} [Field K] [NumberField K] [Algebra c.F K]
    (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (T : CDVR) (iK : K →+* T.Fr) (ρV : 𝓞 K →+* T.V)
    (hρV : (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K)) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K)
    (htt : ∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) (G : SAB H (Sp T.V)) (n : SABMap G B.t (spMap ρV))
    (u₀ : epsR (𝓞 K) ⟶ B.t.G) (hu : IsTangent u₀) (he : ∀ a, IsLieComb ![tt a] ![u₀] (u₀ ≫ B.t.act.act a))
    (W : epsOver T.V T.V ⟶ G.G) (hW : W.left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap ρV) ≫ u₀.left) :
    IsTan W ∧ IsEigV c (iK.comp (algebraMap c.F K)) G ρ W := by
  have hB1 : (1 : ptOver (𝓞 K) (𝓞 K) ⟶ B.t.G).left = η[B.t.G].left := by
    have e : (1 : ptOver (𝓞 K) (𝓞 K) ⟶ B.t.G) = CartesianMonoidalCategory.toUnit _ ≫ η[B.t.G] := rfl
    rw [e, Over.comp_left]
    have e2 : (CartesianMonoidalCategory.toUnit (ptOver (𝓞 K) (𝓞 K))).left = 𝟙 (Sp (𝓞 K)) := by
      have := Over.w (CartesianMonoidalCategory.toUnit (ptOver (𝓞 K) (𝓞 K)))
      exact ((Category.comp_id _).symm.trans this).trans (Spec.map_id _)
    rw [e2]
    exact Category.id_comp _
  have hpt : ∀ (R : Type) [CommRing R], spMap (algebraMap R R) = 𝟙 (Sp R) := fun R _ => by
    rw [Algebra.algebraMap_self]; exact Spec.map_id _
  constructor
  · unfold IsTan
    apply n.cart.1.hom_ext
    · rw [Category.assoc, hW, ← Category.assoc, GlobalTheory.IntLie.spMap_comp₂]
      rw [GlobalTheory.IntLie.one_push n.cart (ptOver T.V T.V) (ptOver (𝓞 K) (𝓞 K)) (spMap ρV)
        (by simp only [Over.mk_hom, hpt]; exact (Category.comp_id _).trans (Category.id_comp _).symm), hB1, ← hu, ← Category.assoc,
        GlobalTheory.IntLie.spMap_comp₂]
      congr 2
      apply RingHom.ext
      intro r
      simp [Formalism.L2.Pj.dualMap]
    · rw [Category.assoc, Over.w W, Over.w (1 : ptOver T.V T.V ⟶ G.G)]
      show spMap (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom ≫
        spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) = spMap (algebraMap T.V T.V)
      rw [GlobalTheory.IntLie.spMap_comp₂]
      congr 1
  · intro a z hz
    have hzρ : z = ρV (tt a) := by
      apply IsFractionRing.injective T.V T.Fr
      rw [hz]
      have := congrArg (fun f => f (tt a)) hρV
      simp only [RingHom.comp_apply] at this
      rw [this]
      show iK (algebraMap c.F K (embK c ρ a)) = iK (algebraMap (𝓞 K) K (tt a))
      rw [← htt]
    subst hzρ
    obtain ⟨U, hU, hprod⟩ := he a
    have hU0 : (u₀ ≫ B.t.act.act a).left = spMap (epsMul (tt a)) ≫ u₀.left := by
      rw [hprod]
      simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, _root_.mul_one]
      exact hU 0
    apply n.cart.1.hom_ext
    · rw [Over.comp_left, Category.assoc, n.act a, ← Category.assoc, hW, Category.assoc, ← Over.comp_left, hU0,
        Category.assoc (spMap (epsMul (ρV (tt a)))) W.left n.φ, hW, ← Category.assoc, ← Category.assoc, GlobalTheory.IntLie.spMap_comp₂,
        GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.dualMap_epsMul]
    · rw [Over.comp_left, Category.assoc, Over.w (G.act.act a), Category.assoc, Over.w W]
      show spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) =
        spMap (epsMul (ρV (tt a))) ≫ spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V))
      rw [GlobalTheory.IntLie.spMap_comp₂, ← RingHom.comp_assoc, GlobalTheory.IntLie.epsMul_alg]

end GlobalTheory.EigLatSpan

noncomputable section
namespace GlobalTheory.EigLatSpan

/- English proof (translation)
Apply `RingHom.ext` to reduce the goal to its premises. Introduce `r`. Apply the tactic sequence `ext <;> simp [Formalism.L2.Pj.dualMap]`.
-/
theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (Formalism.L2.Pj.dualMap g).comp (Formalism.L2.Pj.dualMap f) = Formalism.L2.Pj.dualMap (g.comp f) := by
  apply RingHom.ext
  intro r
  ext <;> simp [Formalism.L2.Pj.dualMap]

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ tt htt u hu 𝔓 T iK hval ρV hρV`. Use `letI := (iK.comp (algebraMap c.F K)).toAlgebra`. Introduce `yT hmap G t' n n' m1' m2' h1 h2 C a y' hchg hint`. Take `⟨e, he, htr⟩` from `baseChange_basis B t₀ m2 F iK t' n'`. Establish `hA` using `GlobalTheory.LieComb.lieComb_algebra T.Fr t'.G _ e he.1`.

Take `⟨ub, -, -, hubu, hl⟩` from `hint`. Use `choose u' hu1 hu2 using hl ρ`. Establish `hδ : spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr)`. Rewrite using `[GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂]`. Use `show spMap ((Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)).comp (algebraMap T.V (DualNumber T.V))) = _`.

Rewrite using `[GlobalTheory.IntLie.dualMap_alg]`. Establish `hov : ∀ (z : epsOver T.V T.V ⟶ G.t.G) (z' : Sp (DualNumber T.Fr) ⟶ t'.G.left), z' ≫ m2'.φ = spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ z.left → z' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr))`. Introduce `z z' hz`. Apply `GlobalTheory.IntLie.spMap_frac_cancel (V := T.V)` to reduce the goal to its premises. Rewrite using `[Category.assoc, ← m2'.cart.1.w, ← Category.assoc, hz, Category.assoc, Over.w z]`.

Conclude with `hδ`. Set `r : Fin (Dw.mult ρ) → (epsR T.Fr ⟶ t'.G)` to `fun i => Over.homMk (u' i) (hov _ _ (hu2 i))`. Set `q : Fin (Dw.mult ρ) → (epsR T.Fr ⟶ t'.G)` to `fun j => Over.homMk (m1'.cart.1.lift (yT.u ρ j) (spMap (algebraMap T.Fr (DualNumber T.Fr))) (yT.tan ρ j).1) (m1'.cart.1.lift_snd _ _ _)`. Establish `hq1 : ∀ j, (q j).left ≫ m1'.φ = yT.u ρ j` using `fun j => m1'.cart.1.lift_fst _ _ _`. Establish `hrq : ∀ i, IsLieComb (C ρ i) q (r i)`.

Introduce `i`. Apply `lieComb_of_combAt m1'` to reduce the goal to its premises. Establish `e1 : (fun j => (q j).left ≫ m1'.φ) = yT.u ρ` using `funext hq1`. Rewrite using `[e1]`. Use `show IsCombAt yT.x (yT.u ρ) (C ρ i) (u' i ≫ m1'.φ)`.

Rewrite using `[hu1]`. Conclude with `hchg.2.1 ρ i`. Use `choose uu ww hA1 hA2 hA3 using hu`. Establish `huu : ∀ j, uu j ≫ t₀.G.hom = spMap (algebraMap K (DualNumber K))`. Introduce `j`.

Apply `GlobalTheory.IntLie.spMap_frac_cancel (V := 𝓞 K)` to reduce the goal to its premises. Rewrite using `[Category.assoc, ← m2.cart.1.w, ← Category.assoc, hA2 j, Category.assoc, F.fib.2.1.1.w, ← Category.assoc, Over.w (ww j)]`. Both sides reduce to the same expression. Establish `hq : ∀ j, IsLieComb (fun k => iK (u j k)) e (q j)`. Introduce `j`.

Use `htr (u j) (ww j) (q j) (hA3 j) ?_` and prove the remaining obligations. Establish `e2 : (q j).left ≫ n'.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ uu j`. Apply `m1.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, ← h1, hq1, hmap.2.1 ρ j, Category.assoc, hA1 j]`. Rewrite using `[Category.assoc, n'.cart.1.w, ← Category.assoc, Over.w (q j), Category.assoc, huu j] show spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap iK = _`.

Rewrite using `[GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.dualMap_alg]`. Rewrite using `[← Category.assoc, e2, Category.assoc, hA2 j]`. Establish `hr : ∀ i, IsLieComb (∑ j, C ρ i j • fun k => iK (u j k)) e (r i)` using `fun i => hA.2.2.1 _ _ q (C ρ i) (r i) hq (hrq i)`. Establish `key : ∀ cc : Fin F.P₀.g → K, (∃ u₀, F.IsCoord u₀ cc ∧ ∀ a, IsLieComb ![tt a] ![u₀] (u₀ ≫ B.t.act.act a)) → (fun k => iK (cc k)) ∈ Submodule.span T.V (Set.range fun i => ∑ j, C ρ i j • fun k => iK (u j k))`. Introduce and unpack `cc ⟨u₀, ⟨htan, w, hwv, hwc⟩, heig⟩`.

Establish `hcond : (spMap (Formalism.L2.Pj.dualMap ρV) ≫ u₀.left) ≫ B.t.G.hom = (epsOver T.V T.V).hom ≫ spMap ρV`. Rewrite using `[Category.assoc, Over.w u₀]`. Use `show spMap (Formalism.L2.Pj.dualMap ρV) ≫ spMap (algebraMap (𝓞 K) (DualNumber (𝓞 K))) = spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) ≫ spMap ρV`. Rewrite using `[GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.dualMap_alg, Algebra.algebraMap_self, RingHom.comp_id]`. Set `W' : epsOver T.V T.V ⟶ G.t.G` to `Over.homMk (n.cart.1.lift _ _ hcond) (n.cart.1.lift_snd _ _ _)`.

Establish `hW' : W'.left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap ρV) ≫ u₀.left` using `n.cart.1.lift_fst _ _ _`. Take `⟨hW't, hW'e⟩` from `isTan_isEigV c B T iK ρV hρV ρ tt htt G.t n u₀ htan heig W' hW'`. Take `⟨aV, haV, -⟩` from `hubu ρ W' hW't hW'e`. Establish `hcs : (spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ W'.left) ≫ G.t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr)`. Rewrite using `[Category.assoc, Over.w W']`.

Conclude with `hδ`. Set `s' : epsR T.Fr ⟶ t'.G` to `Over.homMk (m2'.cart.1.lift _ _ hcs) (m2'.cart.1.lift_snd _ _ _)`. Establish `hs2 : s'.left ≫ m2'.φ = spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ W'.left` using `m2'.cart.1.lift_fst _ _ _`. Establish `hgen` using `GlobalTheory.IntLie.comb_generic m1' m2' (ub ρ) u' hu2 W' s'.left hs2 aV haV`. Establish `hsr : IsLieComb (fun j => algebraMap T.V T.Fr (aV j)) r s'` using `lieComb_of_combAt m1' r _ s' hgen`.

Establish `hs` using `hA.2.2.1 _ _ r _ s' hr hsr`. Establish `hc : IsLieComb (fun k => iK (cc k)) e s'`. Use `htr cc w s' hwc ?_` and prove the remaining obligations. Establish `ed : spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ spMap (Formalism.L2.Pj.dualMap ρV) = spMap (Formalism.L2.Pj.dualMap iK) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap (𝓞 K) K))`. Rewrite using `[GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂, dualMap_comp', hρV]`.

Conclude with `congrArg spMap (dualMap_comp' _ _).symm`. Rewrite using `[hwv, ← h2, ← Category.assoc, hs2, Category.assoc, hW', ← Category.assoc, ed, Category.assoc]`. Establish `heq` using `(he.2 s' (hA.2.1 _ _ hc)).unique hc hs`. Rewrite using `[heq]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[algebraMap_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact key x hx`.

Consider the case `zero`. Use `Submodule.zero_mem (Submodule.span T.V _) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k`. Simplify using the standard rewrite rules. Consider the case `add x z _ _ hx hz`.

Establish `: (fun k => iK ((x + z) k)) = (fun k => iK (x k)) + fun k => iK (z k)`. Use extensionality with `k`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ hx hz`.

Consider the case `smul s x _ hx`. Establish `: (fun k => iK ((s • x) k)) = ρV s • fun k => iK (x k)`. Use extensionality with `k`. Use `congrArg (fun f => f s) hρV` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`.

Simplify using `[Algebra.smul_def, this]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem eigLat_le_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u → ∀ v ∈ F.eigLat B.t.act tt, (fun k => iK (v k)) ∈ Submodule.span T.V (Set.range fun i => ∑ j, C ρ i j • fun k => iK (u j k)) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ tt htt u hu 𝔓 T iK hval ρV hρV
  letI := (iK.comp (algebraMap c.F K)).toAlgebra
  intro yT hmap G t' n n' m1' m2' h1 h2 C a y' hchg hint
  obtain ⟨e, he, htr⟩ := baseChange_basis B t₀ m2 F iK t' n'
  have hA := GlobalTheory.LieComb.lieComb_algebra T.Fr t'.G _ e he.1
  obtain ⟨ub, -, -, hubu, hl⟩ := hint
  choose u' hu1 hu2 using hl ρ
  have hδ : spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫
      spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) =
      spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr) := by
    rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂]
    show spMap ((Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)).comp (algebraMap T.V (DualNumber T.V))) = _
    rw [GlobalTheory.IntLie.dualMap_alg]
  have hov : ∀ (z : epsOver T.V T.V ⟶ G.t.G) (z' : Sp (DualNumber T.Fr) ⟶ t'.G.left),
      z' ≫ m2'.φ = spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ z.left →
      z' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
    intro z z' hz
    apply GlobalTheory.IntLie.spMap_frac_cancel (V := T.V)
    rw [Category.assoc, ← m2'.cart.1.w, ← Category.assoc, hz, Category.assoc, Over.w z]
    exact hδ

  let r : Fin (Dw.mult ρ) → (epsR T.Fr ⟶ t'.G) := fun i => Over.homMk (u' i) (hov _ _ (hu2 i))

  let q : Fin (Dw.mult ρ) → (epsR T.Fr ⟶ t'.G) := fun j =>
    Over.homMk (m1'.cart.1.lift (yT.u ρ j) (spMap (algebraMap T.Fr (DualNumber T.Fr))) (yT.tan ρ j).1)
      (m1'.cart.1.lift_snd _ _ _)
  have hq1 : ∀ j, (q j).left ≫ m1'.φ = yT.u ρ j := fun j => m1'.cart.1.lift_fst _ _ _
  have hrq : ∀ i, IsLieComb (C ρ i) q (r i) := by
    intro i
    apply lieComb_of_combAt m1'
    have e1 : (fun j => (q j).left ≫ m1'.φ) = yT.u ρ := funext hq1
    rw [e1]
    show IsCombAt yT.x (yT.u ρ) (C ρ i) (u' i ≫ m1'.φ)
    rw [hu1]
    exact hchg.2.1 ρ i

  choose uu ww hA1 hA2 hA3 using hu
  have huu : ∀ j, uu j ≫ t₀.G.hom = spMap (algebraMap K (DualNumber K)) := by
    intro j
    apply GlobalTheory.IntLie.spMap_frac_cancel (V := 𝓞 K)
    rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, hA2 j, Category.assoc, F.fib.2.1.1.w, ← Category.assoc,
      Over.w (ww j)]
    rfl
  have hq : ∀ j, IsLieComb (fun k => iK (u j k)) e (q j) := by
    intro j
    refine htr (u j) (ww j) (q j) (hA3 j) ?_
    have e2 : (q j).left ≫ n'.φ = spMap (Formalism.L2.Pj.dualMap iK) ≫ uu j := by
      apply m1.cart.1.hom_ext
      · rw [Category.assoc, ← h1, hq1, hmap.2.1 ρ j, Category.assoc, hA1 j]
      · rw [Category.assoc, n'.cart.1.w, ← Category.assoc, Over.w (q j), Category.assoc, huu j]
        show spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap iK = _
        rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.dualMap_alg]
    rw [← Category.assoc, e2, Category.assoc, hA2 j]
  have hr : ∀ i, IsLieComb (∑ j, C ρ i j • fun k => iK (u j k)) e (r i) :=
    fun i => hA.2.2.1 _ _ q (C ρ i) (r i) hq (hrq i)
  have key : ∀ cc : Fin F.P₀.g → K, (∃ u₀, F.IsCoord u₀ cc ∧ ∀ a, IsLieComb ![tt a] ![u₀] (u₀ ≫ B.t.act.act a)) →
      (fun k => iK (cc k)) ∈ Submodule.span T.V (Set.range fun i => ∑ j, C ρ i j • fun k => iK (u j k)) := by
    rintro cc ⟨u₀, ⟨htan, w, hwv, hwc⟩, heig⟩
    have hcond : (spMap (Formalism.L2.Pj.dualMap ρV) ≫ u₀.left) ≫ B.t.G.hom =
        (epsOver T.V T.V).hom ≫ spMap ρV := by
      rw [Category.assoc, Over.w u₀]
      show spMap (Formalism.L2.Pj.dualMap ρV) ≫ spMap (algebraMap (𝓞 K) (DualNumber (𝓞 K))) =
        spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) ≫ spMap ρV
      rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.dualMap_alg, Algebra.algebraMap_self,
        RingHom.comp_id]
    let W' : epsOver T.V T.V ⟶ G.t.G := Over.homMk (n.cart.1.lift _ _ hcond) (n.cart.1.lift_snd _ _ _)
    have hW' : W'.left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap ρV) ≫ u₀.left := n.cart.1.lift_fst _ _ _
    obtain ⟨hW't, hW'e⟩ := isTan_isEigV c B T iK ρV hρV ρ tt htt G.t n u₀ htan heig W' hW'
    obtain ⟨aV, haV, -⟩ := hubu ρ W' hW't hW'e
    have hcs : (spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ W'.left) ≫ G.t.G.hom =
        spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr) := by
      rw [Category.assoc, Over.w W']
      exact hδ
    let s' : epsR T.Fr ⟶ t'.G := Over.homMk (m2'.cart.1.lift _ _ hcs) (m2'.cart.1.lift_snd _ _ _)
    have hs2 : s'.left ≫ m2'.φ = spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ W'.left :=
      m2'.cart.1.lift_fst _ _ _
    have hgen := GlobalTheory.IntLie.comb_generic m1' m2' (ub ρ) u' hu2 W' s'.left hs2 aV haV
    have hsr : IsLieComb (fun j => algebraMap T.V T.Fr (aV j)) r s' := lieComb_of_combAt m1' r _ s' hgen
    have hs := hA.2.2.1 _ _ r _ s' hr hsr
    have hc : IsLieComb (fun k => iK (cc k)) e s' := by
      refine htr cc w s' hwc ?_
      have ed : spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫ spMap (Formalism.L2.Pj.dualMap ρV) =
          spMap (Formalism.L2.Pj.dualMap iK) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (algebraMap (𝓞 K) K)) := by
        rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂, dualMap_comp', hρV]
        exact congrArg spMap (dualMap_comp' _ _).symm
      rw [hwv, ← h2, ← Category.assoc, hs2, Category.assoc, hW', ← Category.assoc, ed, Category.assoc]
    have heq := (he.2 s' (hA.2.1 _ _ hc)).unique hc hs
    rw [heq]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact key x hx
  | zero =>
    convert Submodule.zero_mem (Submodule.span T.V _) using 1
    ext k
    simp
  | add x z _ _ hx hz =>
    have : (fun k => iK ((x + z) k)) = (fun k => iK (x k)) + fun k => iK (z k) := by
      ext k; simp
    rw [this]
    exact Submodule.add_mem _ hx hz
  | smul s x _ hx =>
    have : (fun k => iK ((s • x) k)) = ρV s • fun k => iK (x k) := by
      ext k
      have := congrArg (fun f => f s) hρV
      simp only [RingHom.comp_apply] at this
      simp [Algebra.smul_def, this]
    rw [this]
    exact Submodule.smul_mem _ _ hx

end GlobalTheory.EigLatSpan
