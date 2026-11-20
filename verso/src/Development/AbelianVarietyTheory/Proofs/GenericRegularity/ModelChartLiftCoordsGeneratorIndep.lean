import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabMapCubical
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.LiftUnique

/- English proof (translation)
Take `⟨Fn, F3, e, hec, hp⟩` from `n`. Simplify using `only at hF he`. Substitute `hF he` using the available equality. Establish `g` using `(isGen_iff w).1 hw.1`. Establish `g'` using `(isGen_iff w').1 hw'.1`.

Establish `r` using `(maps_iff w _ (fun _ => eSec G) _ L'.rig L.rig m.e _ (rigPull_le m.F m.e m.e_comm L.L) (fun _ => rfl)).1 hw.2`. Establish `r'` using `(maps_iff w' _ (fun _ => eSec G') _ L''.rig L'.rig m'.e _ (rigPull_le m'.F m'.e m'.e_comm L'.L) (fun _ => rfl)).1 hw'.2`. Take `⟨w'', T⟩` from `exists_comp L'.isLB w w' g g' L.isLB L''.isLB`. Conclude with `⟨w'', ⟨(isGen_iff w'').2 (T.pgen_comp L'.isLB g g'), (maps_iff w'' _ (fun _ => eSec G) _ L''.rig L.rig (m'.e ≫ m.e) _ (rigPull_le _ _ hec L.L) (fun _ => rfl)).2 (T.pmaps_comp L'.isLB (fun _ => m'.e_comm) r r')⟩, T⟩`.
-/
theorem cube_rig_comp {S S' S'' : Scheme.{0}} {G'' : Over S''} {G' : Over S'} {G : Over S} [GrpObj G'']
    [IsCommMonObj G''] [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (m : CubeMap G' G)
    (m' : CubeMap G'' G') (n : CubeMap G'' G) (hF : n.F = m'.F ≫ m.F) (he : n.e = m'.e ≫ m.e)
    (L'' : RigLB G'') (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F))
    (w' : LB.Iso L''.L (L'.L.pull m'.F))
    (hw : w.IsGen ∧ LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig
      (m.rigPull L.L L.rig))
    (hw' : w'.IsGen ∧ LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec G'') (fun _ => 1)) L''.rig
      (m'.rigPull L'.L L'.rig)) :
    ∃ w'' : LB.Iso L''.L (L.L.pull n.F),
      (w''.IsGen ∧ LB.Gen.Maps (LB.linCombIso w'' (K := PUnit) (fun _ => eSec G'') (fun _ => 1)) L''.rig
        (n.rigPull L.L L.rig)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ G''.left) (z : Z) (j : L.L.ι) (i : L'.L.ι) (k : L''.L.ι),
        n.F (r z) ∈ L.L.U j → m'.F (r z) ∈ L'.L.U i → r z ∈ L''.L.U k →
        gw w'' r z j k = gw w (r ≫ m'.F) z j i * gw w' r z i k := by
  obtain ⟨Fn, F3, e, hec, hp⟩ := n
  dsimp only at hF he
  subst hF he
  have g := (isGen_iff w).1 hw.1
  have g' := (isGen_iff w').1 hw'.1
  have r := (maps_iff w _ (fun _ => eSec G) _ L'.rig L.rig m.e _ (rigPull_le m.F m.e m.e_comm L.L)
    (fun _ => rfl)).1 hw.2
  have r' := (maps_iff w' _ (fun _ => eSec G') _ L''.rig L'.rig m'.e _ (rigPull_le m'.F m'.e m'.e_comm L'.L)
    (fun _ => rfl)).1 hw'.2
  obtain ⟨w'', T⟩ := exists_comp L'.isLB w w' g g' L.isLB L''.isLB
  exact ⟨w'', ⟨(isGen_iff w'').2 (T.pgen_comp L'.isLB g g'),
    (maps_iff w'' _ (fun _ => eSec G) _ L''.rig L.rig (m'.e ≫ m.e) _ (rigPull_le _ _ hec L.L) (fun _ => rfl)).2
      (T.pmaps_comp L'.isLB (fun _ => m'.e_comm) r r')⟩, T⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
The claim follows from `cube_rig_comp m.cm m'.cm n.cm hF (by rw [n.base, m.base, m'.base]; exact (Category.id_comp f).symm) _ _ _ w w' hw hw'`.
-/
theorem rig_comp {S S' : Scheme.{0}} {t : SAB H S} {t₁ t₂ : SAB H S'} {f : S' ⟶ S} (m : SABMap t₁ t f)
    (m' : SABMap t₂ t₁ (𝟙 S')) (n : SABMap t₂ t f) (hF : n.φ = m'.φ ≫ m.φ)
    (w : LB.Iso t₁.PP.L (t.PP.L.pull m.φ)) (w' : LB.Iso t₂.PP.L (t₁.PP.L.pull m'.φ)) (hw : RigIso m w)
    (hw' : RigIso m' w') :
    ∃ w'' : LB.Iso t₂.PP.L (t.PP.L.pull n.φ), RigIso n w'' ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ t₂.G.left) (z : Z) (j : t.PP.L.ι) (i : t₁.PP.L.ι) (k : t₂.PP.L.ι),
        n.φ (r z) ∈ t.PP.L.U j → m'.φ (r z) ∈ t₁.PP.L.U i → r z ∈ t₂.PP.L.U k →
        gw w'' r z j k = gw w (r ≫ m'.φ) z j i * gw w' r z i k :=
  cube_rig_comp m.cm m'.cm n.cm hF (by rw [n.base, m.base, m'.base]; exact (Category.id_comp f).symm) _ _ _ w w' hw hw'

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `sabCancel pullCubCancel E H _ _ _ t t₁ t₂ f (𝟙 _) m n`.
-/
theorem exists_over_id {S S' : Scheme.{0}} {t : SAB H S} {t₁ t₂ : SAB H S'} {f f' : S' ⟶ S} (e : f' = 𝟙 _ ≫ f)
    (m : SABMap t₁ t f) (n : SABMap t₂ t f') : ∃ m' : SABMap t₂ t₁ (𝟙 S'), n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabCancel pullCubCancel E H _ _ _ t t₁ t₂ f (𝟙 _) m n

/- English proof (translation)
Substitute `e` using the available equality. Take `⟨ψ, h₁, h₂, -⟩` from `sabMap_iso m n rfl rfl`. Conclude with `⟨ψ.hom, h₁, h₂⟩`.
-/
theorem exists_hom {S S' : Scheme.{0}} {t : SAB H S} {t₁ t₂ : SAB H S'} {f f' : S' ⟶ S} (e : f' = f)
    (m : SABMap t₁ t f) (n : SABMap t₂ t f') : ∃ ψ : t₁.G ⟶ t₂.G, IsMonHom ψ ∧ ψ.left ≫ n.φ = m.φ := by
  subst e
  obtain ⟨ψ, h₁, h₂, -⟩ := sabMap_iso m n rfl rfl
  exact ⟨ψ.hom, h₁, h₂⟩

/- English proof (translation)
Take `⟨u, hu, rfl⟩` from `h`. Establish `hL : ∀ L : List (epsR R ⟶ G), (L.map (· ≫ ψ)).prod = L.prod ≫ ψ`. Introduce `L`. Proceed by induction on `L with`. Consider the case `nil => simp [MonObj.one_comp]`.

Consider the case `cons a L ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ih, MonObj.mul_comp]`. Use `⟨fun j => u j ≫ ψ, fun j => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Over.comp_left, Over.comp_left, hu j, Category.assoc]`. Rewrite using `[← hL, List.map_ofFn]`. Both sides reduce to the same expression.
-/
theorem lieComb_map {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [GrpObj G'] (ψ : G ⟶ G') [IsMonHom ψ]
    {n : ℕ} {c : Fin n → R} {v : Fin n → (epsR R ⟶ G)} {w : epsR R ⟶ G} (h : IsLieComb c v w) :
    IsLieComb c (fun j => v j ≫ ψ) (w ≫ ψ) := by
  obtain ⟨u, hu, rfl⟩ := h
  have hL : ∀ L : List (epsR R ⟶ G), (L.map (· ≫ ψ)).prod = L.prod ≫ ψ := by
    intro L
    induction L with
    | nil => simp [MonObj.one_comp]
    | cons a L ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ih, MonObj.mul_comp]
  refine ⟨fun j => u j ≫ ψ, fun j => ?_, ?_⟩
  · rw [Over.comp_left, Over.comp_left, hu j, Category.assoc]
  · rw [← hL, List.map_ofFn]
    rfl

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {M : MChart Y} {R : Type} [CommRing R] [Algebra c.F R] {f : Γ(Y.X, M.U) →+* R}
  {x : Sp R ⟶ Xo.X}

/- English proof (translation)
Apply `pullback.hom_ext` to reduce the goal to its premises. Conclude with `Λ'.xF_fst.trans Λ.xF_fst.symm`. Conclude with `Λ'.xF_snd.trans Λ.xF_snd.symm`.
-/
theorem xF_eq (Λ Λ' : M.Lift f x) : Λ'.xF = Λ.xF := by
  apply pullback.hom_ext
  · exact Λ'.xF_fst.trans Λ.xF_fst.symm
  · exact Λ'.xF_snd.trans Λ.xF_snd.symm

/- English proof (translation)
Take `⟨ψ, hψ, e⟩` from `exists_hom (xF_eq Λ Λ') Λ.m' Λ'.m'`. Take `⟨v', u', h₁, h₂, h₃⟩` from `h`. Establish `e₁ : ψ.left ≫ Λ'.m1.φ = Λ.m1.φ` using `by rw [Λ'.liftedChartMap_eq, Λ.liftedChartMap_eq, ← Category.assoc, e]`. Establish `e₂ : ψ.left ≫ Λ'.m2.φ = Λ.m2.φ` using `by rw [Λ'.matrix_two_by_two_congr, Λ.matrix_two_by_two_congr, ← Category.assoc, e]`. Use `⟨fun j => v' j ≫ ψ, u' ≫ ψ, fun j => ?_, lieComb_map ψ h₂, ?_⟩` and prove the remaining obligations.

Rewrite using `[Over.comp_left, Category.assoc, e₂, h₁ j]`. Rewrite using `[Over.comp_left, Category.assoc, e₁, h₃]`.
-/
theorem vec (Λ Λ' : M.Lift f x) (cv : Fin M.n → R) (w : Sp (DualNumber R) ⟶ Xo.univ.t.G.left) (h : Λ.Vec cv w) :
    Λ'.Vec cv w := by
  obtain ⟨ψ, hψ, e⟩ := exists_hom (xF_eq Λ Λ') Λ.m' Λ'.m'
  obtain ⟨v', u', h₁, h₂, h₃⟩ := h
  have e₁ : ψ.left ≫ Λ'.m1.φ = Λ.m1.φ := by rw [Λ'.liftedChartMap_eq, Λ.liftedChartMap_eq, ← Category.assoc, e]
  have e₂ : ψ.left ≫ Λ'.m2.φ = Λ.m2.φ := by rw [Λ'.matrix_two_by_two_congr, Λ.matrix_two_by_two_congr, ← Category.assoc, e]
  refine ⟨fun j => v' j ≫ ψ, u' ≫ ψ, fun j => ?_, lieComb_map ψ h₂, ?_⟩
  · rw [Over.comp_left, Category.assoc, e₂, h₁ j]
  · rw [Over.comp_left, Category.assoc, e₁, h₃]

/- English proof (translation)
Take `⟨n, e⟩` from `exists_over_id ((xF_eq Λ Λ').trans (Category.id_comp _).symm) Λ.m' Λ'.m'`. Establish `e₁ : Λ'.m1.φ = n.φ ≫ Λ.m1.φ` using `by rw [Λ'.liftedChartMap_eq, Λ.liftedChartMap_eq, ← Category.assoc, e]`. Establish `e₂ : Λ'.m2.φ = n.φ ≫ Λ.m2.φ` using `by rw [Λ'.matrix_two_by_two_congr, Λ.matrix_two_by_two_congr, ← Category.assoc, e]`. Take `⟨w1, w2, σ, s1, r1, r2, i1, c2, c1⟩` from `h`. Take `⟨w0, g0, r0, -⟩` from `n.lin`.

Take `⟨w1', r1', T1⟩` from `rig_comp Λ.m1 n Λ'.m1 e₁ w1 w0 r1 ⟨g0, r0⟩`. Take `⟨w2', r2', T2⟩` from `rig_comp Λ.m2 n Λ'.m2 e₂ w2 w0 r2 ⟨g0, r0⟩`. Establish `hL` using `Λ.t'.PP.isLB`. Establish `hL'` using `Λ'.t'.PP.isLB`. Take `⟨σ', hσ'⟩` from `sec_pull_down ((isGen_iff w0).1 g0) hL hL' σ`.

Take `⟨s1', hs1⟩` from `thf_secUp ((isGen_iff w1').1 r1'.1) Xo.univ.t.PP.isLB hL' σ'`. Use `⟨w1', w2', σ', s1', r1', r2', fun (i : PUnit → Xo.univ.t.PP.L.ι) k => fn_ext fun y hy => ?_, fun j k W h₁ h₂ => fn_ext fun y hy => ?_, fun g hs hf (j : PUnit → Xo.univ.t.PP.L.ι) hj => fn_ext fun y hy => ?_⟩` and prove the remaining obligations. Conclude with `(gs_res _ y _ hy _).trans ((hs1 _ (𝟙 _) y i k hy.1 hy.2).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _)))))`. Take `⟨i, hi⟩` from `exists_chart hL (n.φ y)`. Establish `hm : Λ.m2.φ (n.φ y) ∈ Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j` using `(congrArg (fun q => q y ∈ Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j) e₂).mp (h₁ hy)`.

Establish `hz : (𝟙 _ ≫ n.φ) y ∈ Λ.m2.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j) ⊓ ((Y.t.PP.L.pull Λ.m2.φ).U (fun _ => j) ⊓ Λ.t'.PP.L.U i)` using `⟨hm, mem_pull.2 hm.2, hi⟩`. Establish `a` using `congrArg (gs (𝟙 _ ≫ n.φ) y _) (c2 j i _ inf_le_left inf_le_right)`. Establish `a' : gs ((𝟙 _ ≫ n.φ) ≫ Λ.m2.φ) y _ (M.θ j) = (gw w2 (𝟙 _ ≫ n.φ) y j i).val * gs (𝟙 _ ≫ n.φ) y _ (σ.f i)` using `(gs_appLE Λ.m2.φ _ _ _ _ y hz _).symm.trans (a.trans ((gs_mul _ y _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res _ y _ hz _).trans (gs_unit _ y _ hz.2 _)) (gs_res _ y _ hz _))))`. Establish `b` using `hσ' _ (𝟙 _) y i k hi (h₂ hy).2`. Establish `t` using `T2 _ (𝟙 _) y j i k (h₁ hy).2 hi (h₂ hy).2`.

Use `(gs_appLE Λ'.m2.φ _ _ h₁ (𝟙 _) y hy _).trans ?_` and prove the remaining obligations. Use `(congrArg (fun q => gs q y _ (M.θ j)) (show 𝟙 _ ≫ Λ'.m2.φ = (𝟙 _ ≫ n.φ) ≫ Λ.m2.φ by rw [e₂, Category.assoc])).trans (a'.trans ?_)` and prove the remaining obligations. Use `Eq.symm ((gs_mul _ y _ hy _ _).trans ((congrArg₂ (· * ·) ((gs_res _ y _ hy _).trans ((gs_unit _ y _ (h₂ hy) _).trans (congrArg Units.val t))) (gs_res _ y _ hy _)).trans ?_))` and prove the remaining obligations. Rewrite using `[Units.val_mul, _root_.mul_assoc]`. Conclude with `congrArg _ b.symm`.

Set `A` to `Xo.univ.t.G`. Set `a0 : Over.mk (Λ.t'.G.hom ≫ x) ⟶ Over.mk x` to `Over.homMk Λ.t'.G.hom rfl`. Set `b0 : Over.mk (Λ.t'.G.hom ≫ x) ⟶ A` to `Over.homMk Λ.m1.φ Λ.m1.cart.1.w`. Set `q : Λ.t'.G.left ⟶ Gx x` to `(lift a0 b0).left`. Establish `qf : q ≫ (fst (Over.mk x) A).left = Λ.t'.G.hom` using `congrArg (fun q => q.left) (lift_fst a0 b0)`.

Establish `qs : q ≫ (snd (Over.mk x) A).left = Λ.m1.φ` using `congrArg (fun q => q.left) (lift_snd a0 b0)`. Establish `hq : n.φ ≫ q = g`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc] show n.φ ≫ q ≫ (fst (Over.mk x) A).left = g ≫ (fst (Over.mk x) A).left`. Rewrite using `[qf, hf]`.

Conclude with `n.cart.1.w.trans (Category.comp_id _)`. Rewrite using `[Category.assoc] show n.φ ≫ q ≫ (snd (Over.mk x) A).left = g ≫ (snd (Over.mk x) A).left`. Rewrite using `[qs, hs, e₁]`. Establish `le : (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ≤ q ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)` using `fun z hz => Set.mem_iInter.2 fun _ => (congrArg (fun p => p z ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) qs).mpr (mem_pull.1 hz)`. Take `⟨i, hi⟩` from `exists_chart hL (n.φ y)`.

Take `⟨k, hk⟩` from `exists_chart hL' y`. Establish `hm : Λ.m1.φ (n.φ y) ∈ Xo.univ.t.PP.L.U (j PUnit.unit)` using `(congrArg (fun p => p y ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) e₁).mp (mem_pull.1 hy)`. Establish `hz : (𝟙 _ ≫ n.φ) y ∈ (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ⊓ Λ.t'.PP.L.U i` using `⟨mem_pull.2 hm, hi⟩`. Establish `a` using `congrArg (gs (𝟙 _ ≫ n.φ) y _) (i1 j i)`. Establish `a' : gs (𝟙 _ ≫ n.φ) y _ (s1.f j) = (gw w1 (𝟙 _ ≫ n.φ) y (j PUnit.unit) i).val * gs (𝟙 _ ≫ n.φ) y _ (σ.f i)` using `(gs_res _ y _ hz _).symm.trans (a.trans ((gs_mul _ y _ hz _ _).trans (congrArg₂ (· * ·) (gs_unit _ y _ hz _) (gs_res _ y _ hz _))))`.

Establish `b` using `hσ' _ (𝟙 _) y i k hi hk`. Establish `t` using `T1 _ (𝟙 _) y (j PUnit.unit) i k (mem_pull.1 hy) hi hk`. Establish `d : gs (𝟙 _ ≫ n.φ) y _ (s1.f j) = gs (𝟙 _ ≫ g) y _ (s.f (fun _ => j PUnit.unit))` using `(congrArg (gs (𝟙 _ ≫ n.φ) y _) (c1 q qs qf j le)).trans ((gs_appLE q _ _ le _ y hz.1 _).trans (congrArg (fun p => gs p y _ (s.f (fun _ => j PUnit.unit))) (by rw [Category.assoc, hq])))`. Use `(hs1 _ (𝟙 _) y j k hy hk).trans (Eq.trans ?_ (a'.symm.trans (d.trans (gs_appLE g _ _ hj (𝟙 _) y hy _).symm)))` and prove the remaining obligations. Rewrite using `[t, Units.val_mul, _root_.mul_assoc]`.

Conclude with `congrArg _ b.symm`.
-/
theorem thTie (Λ Λ' : M.Lift f x) (s : LB.Sec (PPx x)) (h : Λ.ThTie s) : Λ'.ThTie s := by
  obtain ⟨n, e⟩ := exists_over_id ((xF_eq Λ Λ').trans (Category.id_comp _).symm) Λ.m' Λ'.m'
  have e₁ : Λ'.m1.φ = n.φ ≫ Λ.m1.φ := by rw [Λ'.liftedChartMap_eq, Λ.liftedChartMap_eq, ← Category.assoc, e]
  have e₂ : Λ'.m2.φ = n.φ ≫ Λ.m2.φ := by rw [Λ'.matrix_two_by_two_congr, Λ.matrix_two_by_two_congr, ← Category.assoc, e]
  obtain ⟨w1, w2, σ, s1, r1, r2, i1, c2, c1⟩ := h
  obtain ⟨w0, g0, r0, -⟩ := n.lin
  obtain ⟨w1', r1', T1⟩ := rig_comp Λ.m1 n Λ'.m1 e₁ w1 w0 r1 ⟨g0, r0⟩
  obtain ⟨w2', r2', T2⟩ := rig_comp Λ.m2 n Λ'.m2 e₂ w2 w0 r2 ⟨g0, r0⟩
  have hL := Λ.t'.PP.isLB
  have hL' := Λ'.t'.PP.isLB
  obtain ⟨σ', hσ'⟩ := sec_pull_down ((isGen_iff w0).1 g0) hL hL' σ
  obtain ⟨s1', hs1⟩ := thf_secUp ((isGen_iff w1').1 r1'.1) Xo.univ.t.PP.isLB hL' σ'
  refine ⟨w1', w2', σ', s1', r1', r2', fun (i : PUnit → Xo.univ.t.PP.L.ι) k => fn_ext fun y hy => ?_,
    fun j k W h₁ h₂ => fn_ext fun y hy => ?_, fun g hs hf (j : PUnit → Xo.univ.t.PP.L.ι) hj => fn_ext fun y hy => ?_⟩
  · exact (gs_res _ y _ hy _).trans ((hs1 _ (𝟙 _) y i k hy.1 hy.2).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _)))))
  · obtain ⟨i, hi⟩ := exists_chart hL (n.φ y)
    have hm : Λ.m2.φ (n.φ y) ∈ Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j :=
      (congrArg (fun q => q y ∈ Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j) e₂).mp (h₁ hy)
    have hz : (𝟙 _ ≫ n.φ) y ∈ Λ.m2.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j) ⊓
        ((Y.t.PP.L.pull Λ.m2.φ).U (fun _ => j) ⊓ Λ.t'.PP.L.U i) := ⟨hm, mem_pull.2 hm.2, hi⟩
    have a := congrArg (gs (𝟙 _ ≫ n.φ) y _) (c2 j i _ inf_le_left inf_le_right)
    have a' : gs ((𝟙 _ ≫ n.φ) ≫ Λ.m2.φ) y _ (M.θ j) =
        (gw w2 (𝟙 _ ≫ n.φ) y j i).val * gs (𝟙 _ ≫ n.φ) y _ (σ.f i) :=
      (gs_appLE Λ.m2.φ _ _ _ _ y hz _).symm.trans (a.trans ((gs_mul _ y _ hz _ _).trans
        (congrArg₂ (· * ·) ((gs_res _ y _ hz _).trans (gs_unit _ y _ hz.2 _)) (gs_res _ y _ hz _))))
    have b := hσ' _ (𝟙 _) y i k hi (h₂ hy).2
    have t := T2 _ (𝟙 _) y j i k (h₁ hy).2 hi (h₂ hy).2
    refine (gs_appLE Λ'.m2.φ _ _ h₁ (𝟙 _) y hy _).trans ?_
    refine (congrArg (fun q => gs q y _ (M.θ j))
      (show 𝟙 _ ≫ Λ'.m2.φ = (𝟙 _ ≫ n.φ) ≫ Λ.m2.φ by rw [e₂, Category.assoc])).trans (a'.trans ?_)
    refine Eq.symm ((gs_mul _ y _ hy _ _).trans ((congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_unit _ y _ (h₂ hy) _).trans (congrArg Units.val t))) (gs_res _ y _ hy _)).trans ?_))
    rw [Units.val_mul, _root_.mul_assoc]
    exact congrArg _ b.symm
  · let A := Xo.univ.t.G
    let a0 : Over.mk (Λ.t'.G.hom ≫ x) ⟶ Over.mk x := Over.homMk Λ.t'.G.hom rfl
    let b0 : Over.mk (Λ.t'.G.hom ≫ x) ⟶ A := Over.homMk Λ.m1.φ Λ.m1.cart.1.w
    let q : Λ.t'.G.left ⟶ Gx x := (lift a0 b0).left
    have qf : q ≫ (fst (Over.mk x) A).left = Λ.t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
    have qs : q ≫ (snd (Over.mk x) A).left = Λ.m1.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
    have hq : n.φ ≫ q = g := by
      apply pullback.hom_ext
      · rw [Category.assoc]
        show n.φ ≫ q ≫ (fst (Over.mk x) A).left = g ≫ (fst (Over.mk x) A).left
        rw [qf, hf]
        exact n.cart.1.w.trans (Category.comp_id _)
      · rw [Category.assoc]
        show n.φ ≫ q ≫ (snd (Over.mk x) A).left = g ≫ (snd (Over.mk x) A).left
        rw [qs, hs, e₁]
    have le : (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ≤ q ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit) := fun z hz =>
      Set.mem_iInter.2 fun _ => (congrArg (fun p => p z ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) qs).mpr (mem_pull.1 hz)
    obtain ⟨i, hi⟩ := exists_chart hL (n.φ y)
    obtain ⟨k, hk⟩ := exists_chart hL' y
    have hm : Λ.m1.φ (n.φ y) ∈ Xo.univ.t.PP.L.U (j PUnit.unit) :=
      (congrArg (fun p => p y ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) e₁).mp (mem_pull.1 hy)
    have hz : (𝟙 _ ≫ n.φ) y ∈ (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ⊓ Λ.t'.PP.L.U i := ⟨mem_pull.2 hm, hi⟩
    have a := congrArg (gs (𝟙 _ ≫ n.φ) y _) (i1 j i)
    have a' : gs (𝟙 _ ≫ n.φ) y _ (s1.f j) =
        (gw w1 (𝟙 _ ≫ n.φ) y (j PUnit.unit) i).val * gs (𝟙 _ ≫ n.φ) y _ (σ.f i) :=
      (gs_res _ y _ hz _).symm.trans (a.trans ((gs_mul _ y _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ y _ hz _) (gs_res _ y _ hz _))))
    have b := hσ' _ (𝟙 _) y i k hi hk
    have t := T1 _ (𝟙 _) y (j PUnit.unit) i k (mem_pull.1 hy) hi hk
    have d : gs (𝟙 _ ≫ n.φ) y _ (s1.f j) = gs (𝟙 _ ≫ g) y _ (s.f (fun _ => j PUnit.unit)) :=
      (congrArg (gs (𝟙 _ ≫ n.φ) y _) (c1 q qs qf j le)).trans ((gs_appLE q _ _ le _ y hz.1 _).trans
        (congrArg (fun p => gs p y _ (s.f (fun _ => j PUnit.unit))) (by rw [Category.assoc, hq])))
    refine (hs1 _ (𝟙 _) y j k hy hk).trans (Eq.trans ?_ (a'.symm.trans (d.trans (gs_appLE g _ _ hj (𝟙 _) y hy _).symm)))
    rw [t, Units.val_mul, _root_.mul_assoc]
    exact congrArg _ b.symm

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ Λ'`. Conclude with `⟨vec Λ Λ', thTie Λ Λ'⟩`.
-/
theorem lift_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ Λ' : M.Lift f x, (∀ cv w, Λ.Vec cv w → Λ'.Vec cv w) ∧ ∀ s, Λ.ThTie s → Λ'.ThTie s := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ Λ'
  exact ⟨vec Λ Λ', thTie Λ Λ'⟩

end GlobalTheory.Reg.LiftUnique
