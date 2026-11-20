import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeyInputAtChartPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AppLEEqIffStalk
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ValueAtNormalForm
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels Formalism.L2.Pj
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)

namespace GlobalTheory.KeyFramePoint

open scoped CategoryTheory.MonObj in

/- English proof (translation)
Take `⟨b₁⟩` from `GlobalTheory.KeyAtEx.nonempty_basis_of_isLieBasis h hb`. Take `⟨b₂⟩` from `GlobalTheory.KeyAtEx.nonempty_basis_of_isLieBasis h hb'`. Simplify using `using Fintype.card_congr (b₁.indexEquiv b₂)`.
-/
theorem card_eq_of_isLieBasis {X : Scheme.{0}} {R : Type} [CommRing R] [Nontrivial R] {x : Sp R ⟶ X} {G : Over X} [GrpObj G]
    [IsCommMonObj G] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G x Φ) {n n' : ℕ} {v : Fin n → (epsR R ⟶ G')} {v' : Fin n' → (epsR R ⟶ G')}
    (hb : IsLieBasis v) (hb' : IsLieBasis v') : n = n' := by
  obtain ⟨b₁⟩ := GlobalTheory.KeyAtEx.nonempty_basis_of_isLieBasis h hb
  obtain ⟨b₂⟩ := GlobalTheory.KeyAtEx.nonempty_basis_of_isLieBasis h hb'
  simpa using Fintype.card_congr (b₁.indexEquiv b₂)

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ β Y M V K _ _ _ _ _ yt hz t m n w hw θ x hx hgen`. Take `⟨w₁, θM, ⟨hw₁, hr₁⟩, hth, hne⟩` from `GlobalTheory.exists_sec_pull_nonzero_on_fibres E H _ _ Y.t t yt m M.U hz M.θ M.θ_mem M.θ_ne`. Choose the witnesses or unpack the hypotheses as in `⟨m', hm'⟩ : ∃ m' : SABMap t Y.t (spMap (ev yt M.U hz) ≫ M.hU.fromSpec), m'.φ = m.φ := by`. Rewrite using `[GlobalTheory.FlagMod.spMap_ev yt M.hU hz]`. Conclude with `⟨m, rfl⟩`.

Take `⟨vM, hvM, hbM, -⟩` from `M.lie V (ev yt M.U hz) t m'`. Rewrite `hvM` using `[hm']`. Establish `he : eSec t.G ≫ m.φ = yt ≫ eSec Y.t.G` using `m.cm.e_comm.trans (congrArg (· ≫ eSec Y.t.G) m.base)`. Establish `hrig : m.cm.rigPull Y.t.PP.L Y.t.PP.rig = rigPullOf m.φ yt he Y.t.PP.L Y.t.PP.rig`. Establish `key : ∀ (a b : Sp V ⟶ Y.X) (_ : a = b) ha hb, rigPullOf (G'` using `t.G) m.φ a ha Y.t.PP.L Y.t.PP.rig = rigPullOf m.φ b hb Y.t.PP.L Y.t.PP.rig := by`.

Introduce and unpack `a b rfl _ _`. Both sides reduce to the same expression. Conclude with `key _ _ m.base _ _`. Rewrite `hr₁` using `[hrig]`. Take `⟨a, ha, -⟩` from `hgen θM`.

Establish `hau : IsUnit a`. Take `⟨g, i, h₁, h₂⟩` from `hne (IsLocalRing.closedPoint V)`. Conclude with `(NonzeroClosed.of_isMul ha ⟨g, h₁, Opens.mem_iSup.2 ⟨i, h₂⟩⟩).1`. Take `⟨a, rfl⟩` from `hau`. Take `⟨P, hP, rig, hrig', th, hthne, v, hv⟩` from `x`.

Take `⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩` from `hx`. Simplify using `only at φ' he' w' hg' hp' hw' hr' hs' hv'`. Substitute `hg'` using the available equality. Establish `hn : P.g = M.n` using `card_eq_of_isLieBasis m.cart hw hbM`. Establish `hbM' : IsLieBasis (fun i : Fin P.g => vM (i.cast hn))`.

Establish `key : ∀ (k : ℕ) (h : k = M.n), IsLieBasis (fun i : Fin k => vM (i.cast h))`. Introduce and unpack `k rfl`. Conclude with `hbM`. Conclude with `key _ hn`. Use `choose Mat hMat using fun i : Fin P.g => (hw.2 _ (hbM'.1 i)).exists`.

Take `⟨d, hd⟩ : IsUnit (Matrix.det (Matrix.of Mat))` from `((GlobalTheory.LieComb.lieComb_algebra V t.G P.g w hw.1).2.2.2.2 (Matrix.of Mat) _ hw hMat).1 hbM'`. Use `haveI := P.isAb.comm`. Take `⟨ex, -, -, -, bas⟩` from `GlobalTheory.LieComb.lieComb_algebra K P.A P.g v hv.1`. Use `choose v' hvv' using fun i => (ex (((Matrix.of Mat).map (algebraMap V K)) i)).exists`. Establish `hdet : ((Matrix.of Mat).map (algebraMap V K)).det = algebraMap V K d`.

Rewrite using `[hd, RingHom.map_det]`. Both sides reduce to the same expression. Establish `hb' : IsLieBasis v'` using `(bas _ v' hv hvv').2 (hdet ▸ d.isUnit.map _)`. Take `⟨th', e₀, -, hle⟩` from `GlobalTheory.KeyPow.exists_sec_div P.A.hom (a := algebraMap V K (a⁻¹ : Vˣ)) (b := algebraMap V K a) (by rw [← map_mul, Units.inv_mul, map_one]) th`. Establish `hth' : ∀ s : Sp K, ∃ y : P.A.left, P.A.hom y = s ∧ y ∈ Out.nonzeroLocus th'` using `fun s => (hthne s).imp fun y hy => ⟨hy.1, hle hy.2⟩`.

Use `⟨⟨P, hP, rig, hrig', th', hth', v', hb'⟩, a, d, ?_, fun κ hκ => ?_⟩` and prove the remaining obligations. Use `swap`. Rewrite using `[← hdet]`. Conclude with `hκ.1 K P hP rig hrig' th hthne v hv th' hth' v' hb' _ _ e₀ hvv'`. Establish `g` using `(isGen_iff w₁).1 hw₁`.

Establish `g'` using `(isGen_iff w').1 hw'`. Take `⟨w'', T⟩` from `exists_comp t.PP.isLB w₁ w' g g' Y.t.PP.isLB P.isLB`. Establish `he'' : eSec P.A ≫ φ' ≫ m.φ = (spMap (algebraMap V K) ≫ yt) ≫ eSec Y.t.G`. Rewrite using `[← Category.assoc, he', Category.assoc, he, Category.assoc]`. Establish `hF : F' = dualMap (algebraMap V K)` using `KeyCancel.dualNumber_ringHom_ext (fun a => by`.

Rewrite using `[hF']`. Apply the tactic sequence `ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])`. Use the proof step `(by`. Rewrite using `[hε']`. Apply the tactic sequence `ext <;> simp [dualMap])`.

Establish `hq` using `hp'.comp m.cart`. Use `⟨φ' ≫ m.φ, he'', w'', hn, hq, (isGen_iff w'').2 (T.pgen_comp t.PP.isLB g g'), ?_, ?_, fun i => ?_⟩` and prove the remaining obligations. Establish `r₀` using `(maps_iff w₁ _ (fun _ => eSec Y.t.G) _ t.PP.rig Y.t.PP.rig yt _ (rigPull_le m.φ yt he Y.t.PP.L) (fun _ => rfl)).1 hr₁`. Establish `r₁` using `(maps_iff w' _ (fun _ => eSec t.G) _ rig t.PP.rig (spMap (algebraMap V K)) _ (rigPull_le φ' (spMap (algebraMap V K)) he' t.PP.L) (fun _ => rfl)).1 hr'`. Conclude with `(maps_iff w'' _ (fun _ => eSec Y.t.G) _ rig Y.t.PP.rig (spMap (algebraMap V K) ≫ yt) _ (rigPull_le (φ' ≫ m.φ) (spMap (algebraMap V K) ≫ yt) he'' Y.t.PP.L) (fun _ => rfl)).2 (T.pmaps_comp t.PP.isLB (fun _ => he') r₀ r₁)`.

Use `(KeyAtBC.appLE_eq_iff_stalk w'' (KeyAtBC.mem_of_comm hq.1.w (le_preimage_comp _ hz)) M.θ th').2 fun Z q y j k hj hk => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `exists_chart t.PP.isLB (φ' (q y))`. Establish `a₁` using `(KeyAtBC.appLE_eq_iff_stalk w₁ (KeyAtBC.mem_of_comm m.cart.1.w hz) M.θ θM).1 (fun j i h => (hth (j PUnit.unit) i _ h le_rfl).trans (congrArg (· * _) (GlobalTheory.LB.resG_self _ _))) Z (q ≫ φ') y j i hj hi`. Establish `b₁` using `(KeyCancel.appLE_eq_iff_stalk w' θ th).1 hs' Z q y i k hi hk`. Establish `c₁ : gs (q ≫ φ') y _ (θM.f i) = cst ((q ≫ φ') ≫ t.G.hom) y a * gs (q ≫ φ') y _ (θ.f i)`.

Rewrite using `[ha i, gs_mul _ y _ hi, gs_constFn _ _ _ y hi]`. Establish `c₂ : gs q y _ (th'.f k) = cst (q ≫ P.A.hom) y (algebraMap V K a) * gs q y _ (th.f k)`. Rewrite using `[e₀ k, gs_mul _ y _ hk, gs_constFn _ _ _ y hk]`. Rewrite `c₁` using `[Category.assoc, hp'.1.w, ← Category.assoc, cst_comp]`. Rewrite using `[T Z q y j i k hj hi hk, ← Category.assoc, a₁, c₁, b₁, c₂, Units.val_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e` using `(GlobalTheory.lieComb_baseChange V K (algebraMap V K) t.G P.A φ' hp' P.g w (vM (i.cast hn)) (Mat i) v (v' i) (fun j => (hv' j).trans (by rw [hF]; rfl)) (hMat i)).2 (hvv' i)`. Rewrite using `[← Category.assoc, e, Category.assoc, hvM, FlagMod.ev_spMap _ yt M.U hz, FlagMod.dualMap_comp, KeyAtBC.spMap_comp₀, Category.assoc]`. Both sides reduce to the same expression.
-/
theorem exists_keyAt_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : GChart Y) (V K : Type) [CommRing V] [IsLocalRing V] [Field K] [CharZero K] [Algebra V K] (yt : Sp V ⟶ Y.X) (hz : ⊤ ≤ yt ⁻¹ᵁ M.U) (t : SAB H (Sp V)) (_ : SABMap t Y.t yt) (n : ℕ) (w : Fin n → (epsR V ⟶ t.G)), IsLieBasis w → ∀ (θ : t.PP.L.Sec) (x : KeyIn K), IsFibreOf x t.G t.PP.L t.PP.rig θ w (algebraMap V K) → Generates (X := t.G) θ → ∃ (x' : KeyIn K) (a d : Vˣ), KeyAt M (spMap (algebraMap V K) ≫ yt) (le_preimage_comp _ hz) x' ∧ ∀ κ : KeyRule, IsKeyRule κ → algebraMap V K a ^ 8 * (κ K x' : K) = algebraMap V K d ^ 4 * (κ K x : K) := by
  intro E _ _ _ H D l Xo c O _ β Y M V K _ _ _ _ _ yt hz t m n w hw θ x hx hgen
  obtain ⟨w₁, θM, ⟨hw₁, hr₁⟩, hth, hne⟩ :=
    GlobalTheory.exists_sec_pull_nonzero_on_fibres E H _ _ Y.t t yt m M.U hz M.θ M.θ_mem M.θ_ne
  obtain ⟨m', hm'⟩ : ∃ m' : SABMap t Y.t (spMap (ev yt M.U hz) ≫ M.hU.fromSpec), m'.φ = m.φ := by
    rw [GlobalTheory.FlagMod.spMap_ev yt M.hU hz]
    exact ⟨m, rfl⟩
  obtain ⟨vM, hvM, hbM, -⟩ := M.lie V (ev yt M.U hz) t m'
  rw [hm'] at hvM
  have he : eSec t.G ≫ m.φ = yt ≫ eSec Y.t.G := m.cm.e_comm.trans (congrArg (· ≫ eSec Y.t.G) m.base)
  have hrig : m.cm.rigPull Y.t.PP.L Y.t.PP.rig = rigPullOf m.φ yt he Y.t.PP.L Y.t.PP.rig := by
    have key : ∀ (a b : Sp V ⟶ Y.X) (_ : a = b) ha hb,
        rigPullOf (G' := t.G) m.φ a ha Y.t.PP.L Y.t.PP.rig = rigPullOf m.φ b hb Y.t.PP.L Y.t.PP.rig := by
      rintro a b rfl _ _
      rfl
    exact key _ _ m.base _ _
  rw [hrig] at hr₁

  obtain ⟨a, ha, -⟩ := hgen θM
  have hau : IsUnit a := by
    obtain ⟨g, i, h₁, h₂⟩ := hne (IsLocalRing.closedPoint V)
    exact (NonzeroClosed.of_isMul ha ⟨g, h₁, Opens.mem_iSup.2 ⟨i, h₂⟩⟩).1
  obtain ⟨a, rfl⟩ := hau

  obtain ⟨P, hP, rig, hrig', th, hthne, v, hv⟩ := x
  obtain ⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := hx
  dsimp only at φ' he' w' hg' hp' hw' hr' hs' hv'
  subst hg'
  have hn : P.g = M.n := card_eq_of_isLieBasis m.cart hw hbM
  have hbM' : IsLieBasis (fun i : Fin P.g => vM (i.cast hn)) := by
    have key : ∀ (k : ℕ) (h : k = M.n), IsLieBasis (fun i : Fin k => vM (i.cast h)) := by
      rintro k rfl
      exact hbM
    exact key _ hn
  choose Mat hMat using fun i : Fin P.g => (hw.2 _ (hbM'.1 i)).exists
  obtain ⟨d, hd⟩ : IsUnit (Matrix.det (Matrix.of Mat)) :=
    ((GlobalTheory.LieComb.lieComb_algebra V t.G P.g w hw.1).2.2.2.2 (Matrix.of Mat) _ hw hMat).1 hbM'
  haveI := P.isAb.comm
  obtain ⟨ex, -, -, -, bas⟩ := GlobalTheory.LieComb.lieComb_algebra K P.A P.g v hv.1
  choose v' hvv' using fun i => (ex (((Matrix.of Mat).map (algebraMap V K)) i)).exists
  have hdet : ((Matrix.of Mat).map (algebraMap V K)).det = algebraMap V K d := by
    rw [hd, RingHom.map_det]; rfl
  have hb' : IsLieBasis v' := (bas _ v' hv hvv').2 (hdet ▸ d.isUnit.map _)
  obtain ⟨th', e₀, -, hle⟩ := GlobalTheory.KeyPow.exists_sec_div P.A.hom (a := algebraMap V K (a⁻¹ : Vˣ)) (b := algebraMap V K a)
    (by rw [← map_mul, Units.inv_mul, map_one]) th
  have hth' : ∀ s : Sp K, ∃ y : P.A.left, P.A.hom y = s ∧ y ∈ Out.nonzeroLocus th' :=
    fun s => (hthne s).imp fun y hy => ⟨hy.1, hle hy.2⟩
  refine ⟨⟨P, hP, rig, hrig', th', hth', v', hb'⟩, a, d, ?_, fun κ hκ => ?_⟩
  swap
  · rw [← hdet]
    exact hκ.1 K P hP rig hrig' th hthne v hv th' hth' v' hb' _ _ e₀ hvv'
  have g := (isGen_iff w₁).1 hw₁
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp t.PP.isLB w₁ w' g g' Y.t.PP.isLB P.isLB
  have he'' : eSec P.A ≫ φ' ≫ m.φ = (spMap (algebraMap V K) ≫ yt) ≫ eSec Y.t.G := by
    rw [← Category.assoc, he', Category.assoc, he, Category.assoc]
  have hF : F' = dualMap (algebraMap V K) := KeyCancel.dualNumber_ringHom_ext
    (fun a => by
      rw [hF']
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [hε']
      ext <;> simp [dualMap])
  have hq := hp'.comp m.cart
  refine ⟨φ' ≫ m.φ, he'', w'', hn, hq, (isGen_iff w'').2 (T.pgen_comp t.PP.isLB g g'), ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff w₁ _ (fun _ => eSec Y.t.G) _ t.PP.rig Y.t.PP.rig yt _
      (rigPull_le m.φ yt he Y.t.PP.L) (fun _ => rfl)).1 hr₁
    have r₁ := (maps_iff w' _ (fun _ => eSec t.G) _ rig t.PP.rig (spMap (algebraMap V K)) _
      (rigPull_le φ' (spMap (algebraMap V K)) he' t.PP.L) (fun _ => rfl)).1 hr'
    exact (maps_iff w'' _ (fun _ => eSec Y.t.G) _ rig Y.t.PP.rig (spMap (algebraMap V K) ≫ yt) _
      (rigPull_le (φ' ≫ m.φ) (spMap (algebraMap V K) ≫ yt) he'' Y.t.PP.L) (fun _ => rfl)).2
      (T.pmaps_comp t.PP.isLB (fun _ => he') r₀ r₁)
  · refine (KeyAtBC.appLE_eq_iff_stalk w'' (KeyAtBC.mem_of_comm hq.1.w (le_preimage_comp _ hz)) M.θ th').2
      fun Z q y j k hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart t.PP.isLB (φ' (q y))
    have a₁ := (KeyAtBC.appLE_eq_iff_stalk w₁ (KeyAtBC.mem_of_comm m.cart.1.w hz) M.θ θM).1 (fun j i h =>
      (hth (j PUnit.unit) i _ h le_rfl).trans (congrArg (· * _) (GlobalTheory.LB.resG_self _ _))) Z (q ≫ φ') y j i hj hi
    have b₁ := (KeyCancel.appLE_eq_iff_stalk w' θ th).1 hs' Z q y i k hi hk
    have c₁ : gs (q ≫ φ') y _ (θM.f i) = cst ((q ≫ φ') ≫ t.G.hom) y a * gs (q ≫ φ') y _ (θ.f i) := by
      rw [ha i, gs_mul _ y _ hi, gs_constFn _ _ _ y hi]
    have c₂ : gs q y _ (th'.f k) = cst (q ≫ P.A.hom) y (algebraMap V K a) * gs q y _ (th.f k) := by
      rw [e₀ k, gs_mul _ y _ hk, gs_constFn _ _ _ y hk]
    rw [Category.assoc, hp'.1.w, ← Category.assoc, cst_comp] at c₁
    rw [T Z q y j i k hj hi hk, ← Category.assoc, a₁, c₁, b₁, c₂, Units.val_mul]
    ring
  · have e := (GlobalTheory.lieComb_baseChange V K (algebraMap V K) t.G P.A φ' hp' P.g w (vM (i.cast hn)) (Mat i) v (v' i)
      (fun j => (hv' j).trans (by rw [hF]; rfl)) (hMat i)).2 (hvv' i)
    rw [← Category.assoc, e, Category.assoc, hvM, FlagMod.ev_spMap _ yt M.U hz, FlagMod.dualMap_comp,
      KeyAtBC.spMap_comp₀, Category.assoc]
    rfl

end GlobalTheory.KeyFramePoint
