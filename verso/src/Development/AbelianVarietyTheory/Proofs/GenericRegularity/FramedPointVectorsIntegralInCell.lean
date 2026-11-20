import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.LieFreePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsTriangularOfSpanFirstColumnsLe

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.IntLie

/- English proof (translation)
Establish `h1` using `((GlobalTheory.cell_columns_saturated_and_triangular V L n r ix u hu).1 r x).1 (by`. Rewrite using `[h]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, i.2, rfl⟩))`. Take `⟨a, -, ha⟩` from `(GlobalTheory.mem_span_first_columns_iff u r x).1 h1`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Rewrite using `[ha]`. Use extensionality with `j`. Simplify using `[Matrix.mulVec, dotProduct, Finset.sum_apply, _root_.mul_comm]`.
-/
theorem int_comb {V L : Type} [CommRing V] [IsDomain V] [Field L] [Algebra V L] [IsFractionRing V L] {n r : ℕ}
    (ix : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) V) (hu : InCell ix u) (x : Fin n → V) (cf : Fin r → L)
    (h : (fun j => algebraMap V L (x j)) = ∑ i, cf i • fun j => algebraMap V L (u j i)) :
    ∃ a : Fin r → V, x = ∑ i, a i • fun j => u j i := by
  have h1 := ((GlobalTheory.cell_columns_saturated_and_triangular V L n r ix u hu).1 r x).1 (by
    rw [h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, i.2, rfl⟩))
  obtain ⟨a, -, ha⟩ := (GlobalTheory.mem_span_first_columns_iff u r x).1 h1
  refine ⟨a, ?_⟩
  rw [ha]
  ext j
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, _root_.mul_comm]

/- English proof (translation)
Establish `: ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (g.comp f) = (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR g).comp (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f)`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]`. Rewrite using `[this, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.
-/
theorem dualMapR_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (g.comp f)) =
      spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR g) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) := by
  have : ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (g.comp f) =
      (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR g).comp (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]
  rw [this, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end GlobalTheory.Reg.IntLie

namespace GlobalTheory.Reg

open IntLie
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap tvec_inj tvec_eig_iff isTan_tvec tcoord tcoord_spec univChartLoc tanBC_alg
  pushR pushR_left pushR_inj pushR_map tvec_tmap fB scaleD IsUnivChart dualMapA chart_of_basis dualMapR)
open Formalism.L2.Pj.LieRel
open scoped CategoryTheory.Obj

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Y M T io f₀ ix u₀ hcell`. Set `_` to `io.toAlgebra`. Introduce `z Λ tie G m m2 hφ`. Use `G.semi.smooth` as an intermediate fact. Establish `: ∀ a, IsMonHom (G.act.act a)` using `G.act.hom`.

Take `⟨v, hv0, hvb, -⟩` from `M.lie T.V f₀ G m`. Take `⟨xc, hxc, hxv⟩` from `chart_of_basis hvb`. Take `⟨x', hx', hcomp⟩` from `tanBC_alg (R := T.V) (R' := T.Fr) G.G M.n xc hxc`. Establish `hpt : ∀ cc : Fin M.n → T.V, pushR G.G (tvec (x` using `x') (algebraMap T.V T.Fr ∘ cc)) = ReciprocityTheory.ChartRestriction.G.Chart.spMap (dualMapA T.V T.Fr) ≫ tvec (x := xc) cc := fun cc => Over.OverMorphism.ext (by rw [pushR_left, hcomp cc]; rfl)`. Establish `hM0 : ∀ (a : 𝓞 E) (cc : Fin M.n → T.V), tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) (algebraMap T.V T.Fr ∘ cc) = algebraMap T.V T.Fr ∘ tmap hxc (G.act.act a) cc`.

Introduce `a cc`. Apply `tvec_inj hx'` to reduce the goal to its premises. Apply `pushR_inj G.G` to reduce the goal to its premises. Rewrite using `[tvec_tmap hx', pushR_map, hpt, hpt, tvec_tmap hxc, Category.assoc]`. Establish `hM : ∀ (a : 𝓞 E) (cc : Fin M.n → T.V), tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) (fun j => algebraMap T.V T.Fr (cc j)) = fun j => algebraMap T.V T.Fr (tmap hxc (G.act.act a) cc j)` using `hM0`.

Establish `h1` using `Λ.m1.cart`. Establish `h2 : IsGrpPullback Λ.t'.G G.G (fB T.V T.Fr) m2.φ` using `m2.cart`. Use `choose vA hvA using fun e : Fin M.n → T.Fr => relA_exists_v z.x h1 h2 (tvec (x := x') e)`. Establish `tanA : ∀ e, IsTanAt z.x (vA e).left` using `fun e => ⟨Over.w (vA e), (relA_tan z.x h1 h2 (hvA e)).2 (isTan_tvec hx' e)⟩`. Establish `eigA : ∀ (τ : E →+* ℂ) e, IsEigAt c τ (vA e).left ↔ ∀ a, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) e = io (embK c τ a) • e`.

Introduce `τ e`. Unfold `IsEigAt`. Use `forall_congr' fun a => ?_` and prove the remaining obligations. Rewrite using `[← tvec_eig_iff hx']`. Conclude with `relA_eig z.x h1 h2 (hvA e) (Λ.t'.act.act a) (Xo.univ.t.act.act a) (G.act.act a) (Λ.m1.act a) (m2.act a) _`.

Establish `combA : ∀ {m : ℕ} (d : Fin m → Fin M.n → T.Fr) (cf : Fin m → T.Fr) (e : Fin M.n → T.Fr), IsCombAt z.x (fun i => (vA (d i)).left) cf (vA e).left ↔ e = ∑ i, cf i • d i`. Introduce `m d cf e`. Establish `hr : ∀ i, RelA z.x Λ.m1.φ m2.φ (sclA z.x (cf i) ≫ vA (d i)) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (cf i)) ≫ tvec (x` using `x') (d i)) := fun i => relA_scl z.x (hvA (d i)) (cf i)`. Establish `hp` using `relA_prod z.x h1 h2 _ _ hr`. Rewrite `hp` using `[prod_tvec hx']`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, hw⟩`. Establish `hu' : u = fun i => sclA z.x (cf i) ≫ vA (d i)` using `funext fun i => Over.OverMorphism.ext (hu i)`. Substitute `hu'` using the available equality. Conclude with `tvec_inj hx' ((relA_uniq z.x h1 h2 (hvA e) hp).1 (Over.OverMorphism.ext hw.symm))`.

Introduce and unpack `rfl`. Conclude with `⟨fun i => sclA z.x (cf i) ≫ vA (d i), fun i => rfl, congrArg (fun q => q.left) ((relA_uniq z.x h1 h2 hp (hvA _)).2 rfl)⟩`. Use `choose χ hχ using fun τ a => int_val c T io τ a`. Establish `combV : ∀ cc : Fin M.n → T.V, IsLieComb cc v (tvec (x` using `xc) cc) := by`. Introduce `cc`.

Use `⟨fun i => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (cc i)) ≫ tvec (x := xc) (Pi.single i 1), fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hxv i]`. Both sides reduce to the same expression. Use `Eq.trans ?_ (prod_tvec hxc cc fun i => Pi.single i 1).symm` and prove the remaining obligations. Use `congr 1`.

Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `gen : ∀ τ i, ∃ u' : epsR T.Fr ⟶ Λ.t'.G, u'.left ≫ Λ.m1.φ = z.u τ i ∧ u'.left ≫ m2.φ = spMap (dualMapR (algebraMap T.V T.Fr)) ≫ (tvec (x` using `xc) fun j => u₀ τ j i).left := by`. Introduce `τ i`. Take `⟨v', u', hv', hc, hu'⟩` from `tie τ i`.

Use `⟨u', hu', ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.lieComb_baseChange T.V T.Fr (algebraMap T.V T.Fr) G.G Λ.t'.G m2.φ m2.cart M.n v _ _ v' u' (fun j => ?_) (combV fun j => u₀ τ j i)).2 hc` and prove the remaining obligations. Apply `m.cart.1.hom_ext` to reduce the goal to its premises. Use `(Category.assoc _ _ _).trans (((congrArg ((v' j).left ≫ ·) hφ).trans (hv' j)).trans ?_)` and prove the remaining obligations. Rewrite using `[dualMapR_comp]`.

Conclude with `(Category.assoc _ _ _).trans ((congrArg (spMap (dualMapR (algebraMap T.V T.Fr)) ≫ ·) (hv0 j).symm).trans (Category.assoc _ _ _).symm)`. Rewrite using `[Category.assoc, m2.cart.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w]`. Conclude with `(GlobalTheory.LieCombBaseChange.dualMap_over _).symm`. Establish `hz : ∀ τ, z.u τ = fun i => (vA fun j => algebraMap T.V T.Fr (u₀ τ j i)).left`. Introduce `τ`.

Use function extensionality and compare the values at `i`. Take `⟨u', hu1, hu2⟩` from `gen τ i`. Take `⟨w, hw, hwl⟩` from `hvA (fun j => algebraMap T.V T.Fr (u₀ τ j i))`. Establish `hw' : w.left ≫ m2.φ = (tvec (x` using `x') (fun j => algebraMap T.V T.Fr (u₀ τ j i))).left ≫ pullback.fst G.G.hom (fB T.V T.Fr) := hw`. Establish `e : u'.left = w.left`.

Apply `m2.cart.1.hom_ext` to reduce the goal to its premises. Conclude with `hu2.trans (hw'.trans (hcomp fun j => u₀ τ j i)).symm`. Conclude with `(Over.w u').trans ((Over.w w).trans (Category.comp_id _)).symm`. Rewrite using `[hwl, ← hu1, e]`. Establish `inj : Function.Injective (algebraMap T.V T.Fr)` using `IsFractionRing.injective T.V T.Fr`.

Establish `eigV : ∀ τ (cc : Fin M.n → T.V), IsEigAt c τ (vA fun j => algebraMap T.V T.Fr (cc j)).left ↔ ∀ a, tmap hxc (G.act.act a) cc = χ τ a • cc`. Introduce `τ cc`. Rewrite using `[eigA]`. Use `forall_congr' fun a => ?_` and prove the remaining obligations. Rewrite using `[hM, ← hχ, funext_iff, funext_iff]`.

Use `forall_congr' fun j => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← map_mul]`. Conclude with `inj.eq_iff`. Establish `mapc : ∀ τ (r : Fin (Dw.mult τ) → T.V) (cc : Fin M.n → T.V), (cc = ∑ i, r i • fun j => u₀ τ j i) → (fun j => algebraMap T.V T.Fr (cc j)) = ∑ i, algebraMap T.V T.Fr (r i) • fun j => algebraMap T.V T.Fr (u₀ τ j i)`. Introduce and unpack `τ r cc rfl`.

Use extensionality with `j`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]`. Use `⟨fun τ i => cvV (tvec (x := xc) fun j => u₀ τ j i), fun τ i => isTan_cvV (isTan_tvec hxc _), fun τ i a s hs => ?_, fun τ w hw he => ?_, fun τ i => ?_⟩` and prove the remaining obligations. Establish `hs' : s = χ τ a` using `inj (hs.trans (hχ τ a).symm)`. Substitute `hs'` using the available equality.

Use `(eigV_iff hxc (G.act.act a) _ _).2 ((eigV τ _).1 ?_ a)` and prove the remaining obligations. Use `z.eig τ i` as an intermediate fact. Rewrite `this` using `[hz τ]`. Conclude with `this`. Take `⟨cc, rfl⟩` from `tan_eq_cvV hxc hw`.

Establish `hcc : ∀ a, tmap hxc (G.act.act a) cc = χ τ a • cc` using `fun a => (eigV_iff hxc (G.act.act a) cc _).1 (he a (χ τ a) (hχ τ a))`. Take `⟨cf, hcf, hu⟩` from `z.basis τ _ (tanA _) ((eigV τ cc).2 hcc)`. Rewrite `hcf`, `hu` using `[hz τ]`. Take `⟨r, hr⟩` from `int_comb (ix τ) (u₀ τ) (hcell τ) cc cf ((combA _ cf _).1 hcf)`. Use `⟨r, (comb_iff hxc (fun i j => u₀ τ j i) r cc).2 hr, fun r' h' => ?_⟩` and prove the remaining obligations.

Establish `h''` using `(comb_iff hxc (fun i j => u₀ τ j i) r' cc).1 h'`. Establish `e1` using `hu _ ((combA _ _ _).2 (mapc τ r cc hr))`. Establish `e2` using `hu _ ((combA _ _ _).2 (mapc τ r' cc h''))`. Use function extensionality and compare the values at `i`. Conclude with `inj (congrFun (e2.trans e1.symm) i)`.

Take `⟨u', hu1, hu2⟩` from `gen τ i`. Use `⟨u'.left, hu1, ?_⟩` and prove the remaining obligations. Rewrite using `[cvV_left]`. Conclude with `hu2`.
-/
theorem tie_vectors_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n) (u₀ : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) T.V), (∀ τ, InCell (ix τ) (u₀ τ)) → letI := io.toAlgebra; ∀ (z : FrPt Xo c T.Fr) (Λ : M.Lift ((algebraMap T.V T.Fr).comp f₀) z.x), Λ.LieTie (fun τ => (u₀ τ).map (algebraMap T.V T.Fr)) z.u → ∀ (G : SAB H (Sp T.V)) (m : SABMap G Y.t (spMap f₀ ≫ M.hU.fromSpec)) (m2 : SABMap Λ.t' G (spMap (algebraMap T.V T.Fr))), m2.φ ≫ m.φ = Λ.m2.φ → ∃ ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G), (∀ τ i, IsTan (ub τ i)) ∧ (∀ τ i, IsEigV c io G τ (ub τ i)) ∧ (∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w) ∧ ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ Λ.t'.G.left, u' ≫ Λ.m1.φ = z.u τ i ∧ u' ≫ m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left := by
  intro E _ _ _ H Dw l Xo c O _ β Y M T io f₀ ix u₀ hcell
  let _ := io.toAlgebra
  intro z Λ tie G m m2 hφ
  have := G.semi.smooth
  have : ∀ a, IsMonHom (G.act.act a) := G.act.hom
  obtain ⟨v, hv0, hvb, -⟩ := M.lie T.V f₀ G m
  obtain ⟨xc, hxc, hxv⟩ := chart_of_basis hvb
  obtain ⟨x', hx', hcomp⟩ := tanBC_alg (R := T.V) (R' := T.Fr) G.G M.n xc hxc
  have hpt : ∀ cc : Fin M.n → T.V, pushR G.G (tvec (x := x') (algebraMap T.V T.Fr ∘ cc)) =
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (dualMapA T.V T.Fr) ≫ tvec (x := xc) cc := fun cc =>
    Over.OverMorphism.ext (by rw [pushR_left, hcomp cc]; rfl)
  have hM0 : ∀ (a : 𝓞 E) (cc : Fin M.n → T.V),
      tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) (algebraMap T.V T.Fr ∘ cc) =
        algebraMap T.V T.Fr ∘ tmap hxc (G.act.act a) cc := by
    intro a cc
    apply tvec_inj hx'
    apply pushR_inj G.G
    rw [tvec_tmap hx', pushR_map, hpt, hpt, tvec_tmap hxc, Category.assoc]
  have hM : ∀ (a : 𝓞 E) (cc : Fin M.n → T.V),
      tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) (fun j => algebraMap T.V T.Fr (cc j)) =
        fun j => algebraMap T.V T.Fr (tmap hxc (G.act.act a) cc j) := hM0
  have h1 := Λ.m1.cart
  have h2 : IsGrpPullback Λ.t'.G G.G (fB T.V T.Fr) m2.φ := m2.cart
  choose vA hvA using fun e : Fin M.n → T.Fr => relA_exists_v z.x h1 h2 (tvec (x := x') e)
  have tanA : ∀ e, IsTanAt z.x (vA e).left := fun e =>
    ⟨Over.w (vA e), (relA_tan z.x h1 h2 (hvA e)).2 (isTan_tvec hx' e)⟩
  have eigA : ∀ (τ : E →+* ℂ) e, IsEigAt c τ (vA e).left ↔
      ∀ a, tmap hx' ((Over.pullback (fB T.V T.Fr)).map (G.act.act a)) e = io (embK c τ a) • e := by
    intro τ e
    unfold IsEigAt
    refine forall_congr' fun a => ?_
    rw [← tvec_eig_iff hx']
    exact relA_eig z.x h1 h2 (hvA e) (Λ.t'.act.act a) (Xo.univ.t.act.act a) (G.act.act a) (Λ.m1.act a) (m2.act a) _
  have combA : ∀ {m : ℕ} (d : Fin m → Fin M.n → T.Fr) (cf : Fin m → T.Fr) (e : Fin M.n → T.Fr),
      IsCombAt z.x (fun i => (vA (d i)).left) cf (vA e).left ↔ e = ∑ i, cf i • d i := by
    intro m d cf e
    have hr : ∀ i, RelA z.x Λ.m1.φ m2.φ (sclA z.x (cf i) ≫ vA (d i))
        (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (cf i)) ≫ tvec (x := x') (d i)) :=
      fun i => relA_scl z.x (hvA (d i)) (cf i)
    have hp := relA_prod z.x h1 h2 _ _ hr
    rw [prod_tvec hx'] at hp
    constructor
    · rintro ⟨u, hu, hw⟩
      have hu' : u = fun i => sclA z.x (cf i) ≫ vA (d i) := funext fun i => Over.OverMorphism.ext (hu i)
      subst hu'
      exact tvec_inj hx' ((relA_uniq z.x h1 h2 (hvA e) hp).1 (Over.OverMorphism.ext hw.symm))
    · rintro rfl
      exact ⟨fun i => sclA z.x (cf i) ≫ vA (d i), fun i => rfl,
        congrArg (fun q => q.left) ((relA_uniq z.x h1 h2 hp (hvA _)).2 rfl)⟩
  choose χ hχ using fun τ a => int_val c T io τ a
  have combV : ∀ cc : Fin M.n → T.V, IsLieComb cc v (tvec (x := xc) cc) := by
    intro cc
    refine ⟨fun i => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (cc i)) ≫ tvec (x := xc) (Pi.single i 1), fun i => ?_, ?_⟩
    · rw [hxv i]; rfl
    · refine Eq.trans ?_ (prod_tvec hxc cc fun i => Pi.single i 1).symm
      congr 1
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
  have gen : ∀ τ i, ∃ u' : epsR T.Fr ⟶ Λ.t'.G, u'.left ≫ Λ.m1.φ = z.u τ i ∧
      u'.left ≫ m2.φ = spMap (dualMapR (algebraMap T.V T.Fr)) ≫ (tvec (x := xc) fun j => u₀ τ j i).left := by
    intro τ i
    obtain ⟨v', u', hv', hc, hu'⟩ := tie τ i
    refine ⟨u', hu', ?_⟩
    refine (GlobalTheory.lieComb_baseChange T.V T.Fr (algebraMap T.V T.Fr) G.G Λ.t'.G m2.φ m2.cart M.n v _ _ v' u'
      (fun j => ?_) (combV fun j => u₀ τ j i)).2 hc
    apply m.cart.1.hom_ext
    · refine (Category.assoc _ _ _).trans (((congrArg ((v' j).left ≫ ·) hφ).trans (hv' j)).trans ?_)
      rw [dualMapR_comp]
      exact (Category.assoc _ _ _).trans
        ((congrArg (spMap (dualMapR (algebraMap T.V T.Fr)) ≫ ·) (hv0 j).symm).trans (Category.assoc _ _ _).symm)
    · rw [Category.assoc, m2.cart.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (GlobalTheory.LieCombBaseChange.dualMap_over _).symm
  have hz : ∀ τ, z.u τ = fun i => (vA fun j => algebraMap T.V T.Fr (u₀ τ j i)).left := by
    intro τ
    funext i
    obtain ⟨u', hu1, hu2⟩ := gen τ i
    obtain ⟨w, hw, hwl⟩ := hvA (fun j => algebraMap T.V T.Fr (u₀ τ j i))
    have hw' : w.left ≫ m2.φ = (tvec (x := x') (fun j => algebraMap T.V T.Fr (u₀ τ j i))).left ≫
          pullback.fst G.G.hom (fB T.V T.Fr) := hw
    have e : u'.left = w.left := by
      apply m2.cart.1.hom_ext
      · exact hu2.trans (hw'.trans (hcomp fun j => u₀ τ j i)).symm
      · exact (Over.w u').trans ((Over.w w).trans (Category.comp_id _)).symm
    rw [hwl, ← hu1, e]
  have inj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  have eigV : ∀ τ (cc : Fin M.n → T.V), IsEigAt c τ (vA fun j => algebraMap T.V T.Fr (cc j)).left ↔
      ∀ a, tmap hxc (G.act.act a) cc = χ τ a • cc := by
    intro τ cc
    rw [eigA]
    refine forall_congr' fun a => ?_
    rw [hM, ← hχ, funext_iff, funext_iff]
    refine forall_congr' fun j => ?_
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← map_mul]
    exact inj.eq_iff
  have mapc : ∀ τ (r : Fin (Dw.mult τ) → T.V) (cc : Fin M.n → T.V), (cc = ∑ i, r i • fun j => u₀ τ j i) →
      (fun j => algebraMap T.V T.Fr (cc j)) =
        ∑ i, algebraMap T.V T.Fr (r i) • fun j => algebraMap T.V T.Fr (u₀ τ j i) := by
    rintro τ r cc rfl
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  refine ⟨fun τ i => cvV (tvec (x := xc) fun j => u₀ τ j i), fun τ i => isTan_cvV (isTan_tvec hxc _),
    fun τ i a s hs => ?_, fun τ w hw he => ?_, fun τ i => ?_⟩
  · have hs' : s = χ τ a := inj (hs.trans (hχ τ a).symm)
    subst hs'
    refine (eigV_iff hxc (G.act.act a) _ _).2 ((eigV τ _).1 ?_ a)
    have := z.eig τ i
    rw [hz τ] at this
    exact this
  · obtain ⟨cc, rfl⟩ := tan_eq_cvV hxc hw
    have hcc : ∀ a, tmap hxc (G.act.act a) cc = χ τ a • cc := fun a =>
      (eigV_iff hxc (G.act.act a) cc _).1 (he a (χ τ a) (hχ τ a))
    obtain ⟨cf, hcf, hu⟩ := z.basis τ _ (tanA _) ((eigV τ cc).2 hcc)
    rw [hz τ] at hcf hu
    obtain ⟨r, hr⟩ := int_comb (ix τ) (u₀ τ) (hcell τ) cc cf ((combA _ cf _).1 hcf)
    refine ⟨r, (comb_iff hxc (fun i j => u₀ τ j i) r cc).2 hr, fun r' h' => ?_⟩
    have h'' := (comb_iff hxc (fun i j => u₀ τ j i) r' cc).1 h'
    have e1 := hu _ ((combA _ _ _).2 (mapc τ r cc hr))
    have e2 := hu _ ((combA _ _ _).2 (mapc τ r' cc h''))
    funext i
    exact inj (congrFun (e2.trans e1.symm) i)
  · obtain ⟨u', hu1, hu2⟩ := gen τ i
    refine ⟨u'.left, hu1, ?_⟩
    rw [cvV_left]
    exact hu2

end GlobalTheory.Reg
