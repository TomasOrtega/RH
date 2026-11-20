import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AgreeOfCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGrpPullbackThick
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordCompatOfPull

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThickIso

open GlobalTheory.TorusCoord GlobalTheory.TorusCoordPull

/- English proof (translation)
Take `⟨a0, ha0, H0⟩` from `exists_pmaps hw hL hL' hψ t ht`. Establish `hs : ∀ q, a.s q = a0.s q`. Introduce `q`. Apply `unit_ext` to reduce the goal to its premises. Introduce `x hx`.

Take `⟨J', hJ'⟩` from `TorusCoordPull.exists_good' hL' x`. Take `⟨J, hJ⟩` from `TorusCoordPull.exists_good' hL x`. Establish `hv : val a (𝟙 _) x J' = val a0 (𝟙 _) x J'` using `mul_left_cancel ((H x J J' hJ hJ').symm.trans (val_of_pmaps hψ H0 (𝟙 _) hJ hJ'))`. Establish `hm` using `Good.mem hJ' φ' (𝟙 _)`. Use `show gm (𝟙 Y') x (LB.wchart L' φ' q) (a.s q) = gm (𝟙 Y') x (LB.wchart L' φ' q) (a0.s q)`.

Rewrite using `[gen_trans ha (𝟙 _) x hx hm, gen_trans ha0 (𝟙 _) x hx hm]`. Use `congr 1`. Introduce `Z r z p q hp hq`. Rewrite using `[hs q]`. Conclude with `H0 Z r z p q hp hq`.
-/
theorem pmaps_of_good {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y' ⟶ X')}
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
    {a : LB.Gen (LB.LinComb L' φ' ε)} (ha : a.IsGen) {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (H : ∀ (y : Y') J J', Good L y J → Good L' y J' →
      val t (𝟙 _ ≫ h) y J = (∏ k, om w y J J' (𝟙 _ ≫ φ' k) ^ ε k) * val a (𝟙 _) y J') :
    PMaps w φ' φ ε a t h := by
  obtain ⟨a0, ha0, H0⟩ := exists_pmaps hw hL hL' hψ t ht
  have hs : ∀ q, a.s q = a0.s q := by
    intro q
    apply unit_ext
    intro x hx
    obtain ⟨J', hJ'⟩ := TorusCoordPull.exists_good' hL' x
    obtain ⟨J, hJ⟩ := TorusCoordPull.exists_good' hL x
    have hv : val a (𝟙 _) x J' = val a0 (𝟙 _) x J' :=
      mul_left_cancel ((H x J J' hJ hJ').symm.trans (val_of_pmaps hψ H0 (𝟙 _) hJ hJ'))
    have hm := Good.mem hJ' φ' (𝟙 _)
    show gm (𝟙 Y') x (LB.wchart L' φ' q) (a.s q) = gm (𝟙 Y') x (LB.wchart L' φ' q) (a0.s q)
    rw [gen_trans ha (𝟙 _) x hx hm, gen_trans ha0 (𝟙 _) x hx hm]
    congr 1
  intro Z r z p q hp hq
  rw [hs q]
  exact H0 Z r z p q hp hq

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R}

/- English proof (translation)
Establish `hT : π ≫ T.hom = x ≫ T'.hom`. Rewrite using `[← Over.w b, ← Over.w b', ← Category.assoc, h, Category.assoc]`. Set `p : Over.mk (π ≫ T.hom) ⟶ T` to `Over.homMk π`. Set `q : Over.mk (π ≫ T.hom) ⟶ T'` to `Over.homMk x hT.symm`. Establish `hb : p ≫ b = q ≫ b'`.

Use `ext`. Conclude with `h`. Establish `hu : p ≫ toUnit T = q ≫ toUnit T'` using `toUnit_unique _ _`. Establish `key : ∀ (f : T ⟶ D.P.A) (f' : T' ⟶ D.P.A), p ≫ f = q ≫ f' → π ≫ f.left = x ≫ f'.left` using `fun f f' e => congrArg Over.Hom.left e`. Establish `e1 : p ≫ (toUnit T ≫ D.c χ) = q ≫ (toUnit T' ≫ D.c χ)`.

Rewrite using `[← Category.assoc, hu, Category.assoc]`. Simplify using `only [DegPre.Oφ, padd]`. Use `match k with`. Consider the case `0 => exact key _ _ (by rw [← Category.assoc, ← Category.assoc, comp_lift, comp_lift, hb, e1])`. Consider the case `1 => exact key _ _ e1`.

Consider the case `2 => exact key _ _ hb`. Consider the case `3 => exact key _ _ (by rw [← Category.assoc, ← Category.assoc, hu])`.
-/
theorem Oφ_congr {T T' : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (b' : T' ⟶ D.P.A) {W : Scheme.{0}}
    (π : W ⟶ T.left) (x : W ⟶ T'.left) (h : π ≫ b.left = x ≫ b'.left) (χ : D.X) (k : Fin 4) :
    π ≫ D.Oφ b χ k = x ≫ D.Oφ b' χ k := by
  have hT : π ≫ T.hom = x ≫ T'.hom := by
    rw [← Over.w b, ← Over.w b', ← Category.assoc, h, Category.assoc]
  let p : Over.mk (π ≫ T.hom) ⟶ T := Over.homMk π
  let q : Over.mk (π ≫ T.hom) ⟶ T' := Over.homMk x hT.symm
  have hb : p ≫ b = q ≫ b' := by
    ext
    exact h
  have hu : p ≫ toUnit T = q ≫ toUnit T' := toUnit_unique _ _
  have key : ∀ (f : T ⟶ D.P.A) (f' : T' ⟶ D.P.A), p ≫ f = q ≫ f' → π ≫ f.left = x ≫ f'.left :=
    fun f f' e => congrArg Over.Hom.left e
  have e1 : p ≫ (toUnit T ≫ D.c χ) = q ≫ (toUnit T' ≫ D.c χ) := by
    rw [← Category.assoc, hu, Category.assoc]
  simp only [DegPre.Oφ, padd]
  match k with
  | 0 => exact key _ _ (by rw [← Category.assoc, ← Category.assoc, comp_lift, comp_lift, hb, e1])
  | 1 => exact key _ _ e1
  | 2 => exact key _ _ hb
  | 3 => exact key _ _ (by rw [← Category.assoc, ← Category.assoc, hu])

/- English proof (translation)
Establish `hF : ∀ χ, FormEq (φ χ) Oinvε (D.gtφT T b χ) DegPre.gtε` using `fun χ U _ hU => by`. Rewrite using `[formEq_of_left' b b (𝟙 _) (Category.id_comp _).symm χ U hU]`. Simplify using `[hφ]`. Use `choose s' hs' hv using fun χ => exists_gen D.P.isLB (hF χ) (s χ) (hs χ)`. Establish `hc0 : cP D T 0 = 1`.

Establish `h` using `cPoint_add D T 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `(mul_eq_left.mp h.symm)`. Establish `hz : ∀ y J, Good D.P.L y J → val (s 0) (𝟙 _) y J = 1`. Introduce `y J hJ`.

Establish `h0` using `hm 0 0 y J hJ`. Generalize the expression as in `e : (0 : D.X) + 0 = c at h0`. Rewrite `e` using `[add_zero]`. Substitute `e` using the available equality. Rewrite `h0` using `[hc0, (isCub_cubV D.cub hJ).face, _root_.mul_one]`.

Conclude with `(mul_eq_left.mp h0.symm)`. Set `ξ : GtPt D T` to `⟨b, s', hs', corr_of_val D.P.isLB fun y J hJ => by`. Rewrite using `[hv 0 _ _ _ _ hJ, hz y J hJ, val_one], fun χ χ' => corr_of_val D.P.isLB fun y J hJ => by`. Use `Eq.trans ?_ (val_mul hJ _ _ _).symm` and prove the remaining obligations. Use `Eq.trans (val_mul hJ _ _ _) ?_` and prove the remaining obligations.

Rewrite using `[hv _ _ _ _ _ hJ, hv _ _ _ _ _ hJ, hv _ _ _ _ _ hJ, ← hm χ χ' y J hJ]`. Use `congr 1`. Use `(val_pull hJ _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Category.id_comp]`. Use the proof step `rfl⟩`.

Take `⟨x, hx⟩` from `exists_point g σ hσ ξ`. Use `⟨x, hx.1, fun χ V r v J hJ => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_of_vals {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of R))}
    (σ : T.left ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (hσ : σ ≫ thick R I e = T.hom) (b : T ⟶ D.P.A)
    (φ : D.X → Fin 4 → (T.left ⟶ D.P.A.left)) (hφ : ∀ χ k, φ χ k = D.Oφ b χ k)
    (s : ∀ χ, LB.Gen (LB.LinComb D.P.L (φ χ) Oinvε)) (hs : ∀ χ, (s χ).IsGen)
    (hm : ∀ χ χ' y J, Good D.P.L y J → val (s (χ + χ')) (𝟙 _) y J * cubV D.cub y J (cP D T χ) (cP D T χ') b =
      val (s χ) (𝟙 _) y J * val (s χ') (𝟙 _) y J) :
    ∃ x : T.left ⟶ (thickObj R I e G).left, b.left = x ≫ g.pG.left ∧
      ∀ χ (V : Scheme.{0}) (r : V ⟶ T.left) (v : V) (J), Good D.P.L v J →
        val (g.t χ) (r ≫ x) v J = val (s χ) r v J := by
  have hF : ∀ χ, FormEq (φ χ) Oinvε (D.gtφT T b χ) DegPre.gtε := fun χ U _ hU => by
    rw [formEq_of_left' b b (𝟙 _) (Category.id_comp _).symm χ U hU]
    simp [hφ]
  choose s' hs' hv using fun χ => exists_gen D.P.isLB (hF χ) (s χ) (hs χ)
  have hc0 : cP D T 0 = 1 := by
    have h := cPoint_add D T 0 0
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)
  have hz : ∀ y J, Good D.P.L y J → val (s 0) (𝟙 _) y J = 1 := by
    intro y J hJ
    have h0 := hm 0 0 y J hJ
    generalize e : (0 : D.X) + 0 = c at h0
    rw [add_zero] at e
    subst e
    rw [hc0, (isCub_cubV D.cub hJ).face, _root_.mul_one] at h0
    exact (mul_eq_left.mp h0.symm)
  let ξ : GtPt D T := ⟨b, s', hs', corr_of_val D.P.isLB fun y J hJ => by
      rw [hv 0 _ _ _ _ hJ, hz y J hJ, val_one], fun χ χ' => corr_of_val D.P.isLB fun y J hJ => by
      refine Eq.trans ?_ (val_mul hJ _ _ _).symm
      refine Eq.trans (val_mul hJ _ _ _) ?_
      rw [hv _ _ _ _ _ hJ, hv _ _ _ _ _ hJ, hv _ _ _ _ _ hJ, ← hm χ χ' y J hJ]
      congr 1
      refine (val_pull hJ _ _ _).trans ?_
      rw [Category.id_comp]
      rfl⟩
  obtain ⟨x, hx⟩ := exists_point g σ hσ ξ
  refine ⟨x, hx.1, fun χ V r v J hJ => ?_⟩
  calc val (g.t χ) (r ≫ x) v J = val (LB.pullGen D.P.L _ _ (g.t χ) x) r v J := (val_pull hJ _ _ _).symm
    _ = val (s' χ) r v J := (val_corr hJ (hx.2 χ) r).symm
    _ = val (s χ) r v J := hv χ V r v J hJ

variable (hD : IsPullDeg (RingHom.id R) D D')

abbrev abMap : D'.P.A.left ⟶ D.P.A.left := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))

omit [IsDomain R] in
/- English proof (translation)
Rewrite using `[specOf, CommRingCat.ofHom_id, Spec.map_id]`.
-/
theorem specOf_id : specOf (RingHom.id R) = 𝟙 _ := by
  rw [specOf, CommRingCat.ofHom_id, Spec.map_id]

def abHom : D'.P.A ⟶ D.P.A :=
  Over.homMk (abMap hD) ((pull_grp hD).1.w.trans ((congrArg (_ ≫ ·) specOf_id).trans (Category.comp_id _)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem abHom_left : (abHom hD).left = abMap hD := rfl

instance isIso_abMap : IsIso (abMap hD) := by
  have : IsIso (specOf (RingHom.id R)) := by rw [specOf_id]; infer_instance
  have : IsIso hD.e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map hD.e.hom))
  infer_instance

instance isIso_abHom : IsIso (abHom hD) := by
  have : IsIso ((Over.forget _).map (abHom hD)) := isIso_abMap hD
  exact isIso_of_reflects_iso _ (Over.forget _)

/- English proof (translation)
Take `⟨-, hm⟩` from `pull_grp hD`. Establish `hs : T.hom ≫ spMap (RingHom.id R) = T.hom`. Rewrite using `[show spMap (RingHom.id R) = 𝟙 _ from specOf_id, Category.comp_id]`. Set `e : T ⟶ Over.mk (T.hom ≫ spMap (RingHom.id R))` to `Over.homMk (𝟙 T.left) (by simp [hs])`. Set `e' : Over.mk (T.hom ≫ spMap (RingHom.id R)) ⟶ T` to `Over.homMk (𝟙 T.left) (by simp [hs])`.

Establish `hee : e ≫ e' = 𝟙 T`. Use `ext`. Simplify using `[e, e']`. Establish `key` using `hm T x y (e' ≫ x ≫ abHom hD) (e' ≫ y ≫ abHom hD) (by simp [e', abHom_left]) (by simp [e', abHom_left])`. Establish `hxy : x ≫ abHom hD * y ≫ abHom hD = e ≫ ((e' ≫ x ≫ abHom hD) * (e' ≫ y ≫ abHom hD))`.

Rewrite using `[comp_mul]`. Simplify using `only [← Category.assoc, hee, Category.id_comp]`. Rewrite using `[hxy]`. Use `ext`. Simplify using `[e, key, abHom_left]`.
-/
theorem abHom_mul {T : Over (Spec (CommRingCat.of R))} (x y : T ⟶ D'.P.A) :
    (x * y) ≫ abHom hD = (x ≫ abHom hD) * (y ≫ abHom hD) := by
  obtain ⟨-, hm⟩ := pull_grp hD
  have hs : T.hom ≫ spMap (RingHom.id R) = T.hom := by
    rw [show spMap (RingHom.id R) = 𝟙 _ from specOf_id, Category.comp_id]
  let e : T ⟶ Over.mk (T.hom ≫ spMap (RingHom.id R)) := Over.homMk (𝟙 T.left) (by simp [hs])
  let e' : Over.mk (T.hom ≫ spMap (RingHom.id R)) ⟶ T := Over.homMk (𝟙 T.left) (by simp [hs])
  have hee : e ≫ e' = 𝟙 T := by
    ext
    simp [e, e']
  have key := hm T x y (e' ≫ x ≫ abHom hD) (e' ≫ y ≫ abHom hD) (by simp [e', abHom_left])
    (by simp [e', abHom_left])
  have hxy : x ≫ abHom hD * y ≫ abHom hD = e ≫ ((e' ≫ x ≫ abHom hD) * (e' ≫ y ≫ abHom hD)) := by
    rw [comp_mul]
    simp only [← Category.assoc, hee, Category.id_comp]
  rw [hxy]
  ext
  simp [e, key, abHom_left]

/- English proof (translation)
Establish `hs : T.hom ≫ spMap (RingHom.id R) = T.hom`. Rewrite using `[show spMap (RingHom.id R) = 𝟙 _ from specOf_id, Category.comp_id]`. Set `e : T ⟶ Over.mk (T.hom ≫ spMap (RingHom.id R))` to `Over.homMk (𝟙 T.left) (by simp [hs])`. Establish `he : cP D T (hD.xe χ) = e ≫ cP D _ (hD.xe χ)`. Simplify using `only [cP, ← Category.assoc, toUnit_unique (e ≫ toUnit _) (toUnit T)]`.

Use `ext`. Rewrite using `[he, Over.comp_left, Over.comp_left, abHom_left, ← push_cP hD T χ]`. Simplify using `[pushPt, e, abMap]`.
-/
theorem cPoint_comp_abHom (T : Over (Spec (CommRingCat.of R))) (χ : D'.X) : cP D' T χ ≫ abHom hD = cP D T (hD.xe χ) := by
  have hs : T.hom ≫ spMap (RingHom.id R) = T.hom := by
    rw [show spMap (RingHom.id R) = 𝟙 _ from specOf_id, Category.comp_id]
  let e : T ⟶ Over.mk (T.hom ≫ spMap (RingHom.id R)) := Over.homMk (𝟙 T.left) (by simp [hs])
  have he : cP D T (hD.xe χ) = e ≫ cP D _ (hD.xe χ) := by
    simp only [cP, ← Category.assoc, toUnit_unique (e ≫ toUnit _) (toUnit T)]
  ext
  rw [he, Over.comp_left, Over.comp_left, abHom_left, ← push_cP hD T χ]
  simp [pushPt, e, abMap]

def lam {T : Over (Spec (CommRingCat.of R))} (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι)
    (J' : (T.left ⟶ D'.P.A.left) → D'.P.L.ι) (a c : T ⟶ D'.P.A) : (T.left.presheaf.stalk z)ˣ :=
  (om hD.w z J J' (a * c).left)⁻¹ * om hD.w z J J' c.left * om hD.w z J J' a.left *
    (om hD.w z J J' (1 : T ⟶ D'.P.A).left)⁻¹

/- English proof (translation)
Unfold `lam`. Rewrite using `[mul_comm a c]`. The two sides agree by associativity and commutativity.
-/
theorem lam_comm {T : Over (Spec (CommRingCat.of R))} (z : T.left) (J J') (a c : T ⟶ D'.P.A) :
    lam hD z J J' a c = lam hD z J J' c a := by
  unfold lam
  rw [mul_comm a c]
  ac_rfl

/- English proof (translation)
Establish `hp` using `cub_pull hG hD hJ hJ' a b c`. Establish `e1 : cubV D.cub z J (a ≫ abHom hD) (b ≫ abHom hD) (c ≫ abHom hD) = val (L` using `D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t ((lift a (lift b c)).left ≫ (cubeMapOf (pull_grp hD)).F3) z J := by`. Unfold `cubV`. Use `congr 1`. Apply `hom_ext_triple` to reduce the goal to its premises.

Introduce `i`. Rewrite using `[Category.assoc, cubeMap_comp_proj_three]`. Use `clear hp hJ hJ'`. Rewrite using `[← Category.assoc, ← Over.comp_left, ← Over.comp_left]`. Apply the tactic sequence `fin_cases i <;>`.

Apply the tactic sequence `simp only [x3, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, lift_fst, lift_snd_assoc, lift_fst, lift_snd, Over.comp_left, abHom_left] <;>`. Both sides reduce to the same expression. Establish `hP : (∏ I : thK, gw hD.w ((lift a (lift b c)).left ≫ thφ D'.P.A (x3 D'.P.A) I) z (J (((lift a (lift b c)).left ≫ thφ D'.P.A (x3 D'.P.A) I) ≫ (cubeMapOf (pull_grp hD)).F)) (J' ((lift a (lift b c)).left ≫ thφ D'.P.A (x3 D'.P.A) I)) ^ thε I) = om hD.w z J J' (a * b * c).left * (om h …` using `prod_cub a b c (fun q => om hD.w z J J' q)`. Rewrite using `[e1, hp, hP]`. Unfold `lam`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
theorem cub_lam (hG : GlobalFnsSt) {T : Over (Spec (CommRingCat.of R))} {z : T.left} {J J'} (hJ : Good D.P.L z J)
    (hJ' : Good D'.P.L z J') (a b c : T ⟶ D'.P.A) :
    cubV D.cub z J (a ≫ abHom hD) (b ≫ abHom hD) (c ≫ abHom hD) * lam hD z J J' (a * b) c =
      lam hD z J J' a c * lam hD z J J' b c * cubV D'.cub z J' a b c := by
  have hp := cub_pull hG hD hJ hJ' a b c
  have e1 : cubV D.cub z J (a ≫ abHom hD) (b ≫ abHom hD) (c ≫ abHom hD) =
      val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
        ((lift a (lift b c)).left ≫ (cubeMapOf (pull_grp hD)).F3) z J := by
    unfold cubV
    congr 1
    apply hom_ext_triple
    intro i
    rw [Category.assoc, cubeMap_comp_proj_three]
    clear hp hJ hJ'
    rw [← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;>
      simp only [x3, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, lift_fst, lift_snd_assoc, lift_fst,
        lift_snd, Over.comp_left, abHom_left] <;>
      rfl
  have hP : (∏ I : thK, gw hD.w ((lift a (lift b c)).left ≫ thφ D'.P.A (x3 D'.P.A) I) z
        (J (((lift a (lift b c)).left ≫ thφ D'.P.A (x3 D'.P.A) I) ≫ (cubeMapOf (pull_grp hD)).F))
        (J' ((lift a (lift b c)).left ≫ thφ D'.P.A (x3 D'.P.A) I)) ^ thε I) =
      om hD.w z J J' (a * b * c).left * (om hD.w z J J' (a * b).left)⁻¹ * (om hD.w z J J' (a * c).left)⁻¹ *
        (om hD.w z J J' (b * c).left)⁻¹ * om hD.w z J J' a.left * om hD.w z J J' b.left *
        om hD.w z J J' c.left * (om hD.w z J J' (1 : T ⟶ D'.P.A).left)⁻¹ :=
    prod_cub a b c (fun q => om hD.w z J J' q)
  rw [e1, hp, hP]
  unfold lam
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/- English proof (translation)
Establish `hc : ρ ≫ cP D' T χ = cP D' T' χ`. Simplify using `only [cP, ← Category.assoc, toUnit_unique (ρ ≫ toUnit T) (toUnit T')]`. Rewrite using `[prod_O D' p χ (fun f => om hD.w z J J' (ρ.left ≫ f))]`. Simplify using `only [lam, ← Over.comp_left, comp_mul, hc, comp_one]`.
-/
theorem prod_lam {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) (p : T ⟶ D'.P.A) (χ : D'.X) (z : T'.left)
    (J J') : ∏ k, om hD.w z J J' (ρ.left ≫ D'.Oφ p χ k) ^ Oinvε k = lam hD z J J' (ρ ≫ p) (cP D' T' χ) := by
  have hc : ρ ≫ cP D' T χ = cP D' T' χ := by
    simp only [cP, ← Category.assoc, toUnit_unique (ρ ≫ toUnit T) (toUnit T')]
  rw [prod_O D' p χ (fun f => om hD.w z J J' (ρ.left ≫ f))]
  simp only [lam, ← Over.comp_left, comp_mul, hc, comp_one]

/- English proof (translation)
Establish `hq : x ≫ g.q.left = y ≫ g.q.left`. Establish `: Mono (DegPre.prBe I D e).left` using `GlobalTheory.LevelCompat.mono_fstG I e D.P.A`. Rewrite using `[← cancel_mono (DegPre.prBe I D e).left]`. Simplify `hA` using `[GtCoord.pG, Category.assoc]`. Establish `hxy : x ≫ (thickObj R I e G).hom = y ≫ (thickObj R I e G).hom`.

Rewrite using `[← Over.w g.q]`. Simplify using `only [← Category.assoc, hq]`. Set `Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))` to `Over.mk (y ≫ (thickObj R I e G).hom)`. Set `a : Z ⟶ thickObj R I e G` to `Over.homMk x hxy`. Set `b : Z ⟶ thickObj R I e G` to `Over.homMk y`.

Take `⟨τ, hτ⟩` from `exists_torus g a b (by ext; exact hq)`. Use `g.i_hom` as an intermediate fact. Establish `h1i : (1 : Z ⟶ WeightPf.Te D I e) ≫ g.i = 1` using `by simp`. Establish `hc : ∀ (χ : D.X) (z : W), gm τ.left z ⊤ (charUnit _ D.X χ) = gm (1 : Z ⟶ WeightPf.Te D I e).left z ⊤ (charUnit _ D.X χ)`. Introduce `χ z`.

Take `⟨J, hJ⟩` from `TorusCoordPull.exists_good' D.P.isLB z`. Establish `e1` using `val_torus g χ hJ τ b`. Establish `e0` using `val_torus g χ hJ 1 b`. Rewrite `e1` using `[← hτ]`. Rewrite `e0` using `[h1i, _root_.one_mul]`.

Establish `ex : val (g.t χ) a.left z J = val (g.t χ) b.left z J` using `hV χ z J hJ`. Rewrite `e1` using `[ex]`. Conclude with `(mul_eq_right.mp e1.symm).trans (mul_eq_right.mp e0.symm).symm`. Establish `hc' : ∀ χ : D.X, τ.left.appTop.hom (charUnit _ D.X χ).val = (1 : Z ⟶ WeightPf.Te D I e).left.appTop.hom (charUnit _ D.X χ).val` using `fun χ => appTop_eq_of_gm _ _ _ (hc χ)`. Establish `hτ1 : τ = 1` using `by ext1`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Establish `key : ∀ χ : D.X, (τ.left ≫ pullback.fst _ _).appTop.hom ((Scheme.ΓSpecIso (torusRing ZU D.X)).inv.hom (AddMonoidAlgebra.single χ 1)) = ((1 : Z ⟶ WeightPf.Te D I e).left ≫ pullback.fst _ _).appTop.hom ((Scheme.ΓSpecIso (torusRing ZU D.X)).inv.hom (AddMonoidAlgebra.single χ 1))`. Introduce `χ`. Establish `hz` using `appTop_eq_of_gm (τ.left ≫ pullback.fst _ _) ((1 : Z ⟶ WeightPf.Te D I e).left ≫ pullback.fst _ _) (Units.map (Scheme.ΓSpecIso (torusRing ZU D.X)).inv.hom.toMonoidHom (Units.map (AddMonoidAlgebra.of ZU D.X) (toUnits (Multiplicative.ofAdd χ)))) (fun z => by`. Establish `h` using `hc χ z`.

Unfold `charUnit at h`. Use `erw [gm_res, gm_res, gm_pull, gm_pull] at h`. Conclude with `h`. Apply the tactic sequence `all_goals simp)`. Simplify using `using hz`.

Establish `: IsAffine (splitTorusAff ZU D.X).left`. Unfold `splitTorusAff`. Conclude with `inferInstanceAs (IsAffine (Spec _))`. Apply `ext_of_isAffine` to reduce the goal to its premises. Use `(cancel_epi (Scheme.ΓSpecIso (torusRing ZU D.X)).inv).mp ?_` and prove the remaining obligations.

Apply `CommRingCat.hom_ext` to reduce the goal to its premises. Apply `AddMonoidAlgebra.ringHom_ext` to reduce the goal to its premises. Introduce `b`. Take `⟨n⟩` from `b`. Establish `hn : (AddMonoidAlgebra.single 0 (ULift.up n) : AddMonoidAlgebra (ULift.{0} ℤ) D.X) = ((n : ℤ) : AddMonoidAlgebra (ULift.{0} ℤ) D.X)`.

Rewrite using `[AddMonoidAlgebra.intCast_def]`. Both sides reduce to the same expression. Simplify using `only [hn, map_intCast]`. Introduce `χ`. Conclude with `key χ`.

Conclude with `(Over.w τ).trans (Over.w (1 : Z ⟶ WeightPf.Te D I e)).symm`. Establish `hab : a = b` using `by rw [hτ, hτ1, h1i, _root_.one_mul]`. Conclude with `congrArg Over.Hom.left hab`.
-/
private theorem gtCoord_point_ext' {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (g : GtCoord I D e G) {W : Scheme.{0}} {x y : W ⟶ (thickObj R I e G).left}
    (hA : x ≫ g.pG.left = y ≫ g.pG.left)
    (hV : ∀ (χ : D.X) (w : W) J, Good D.P.L w J → val (g.t χ) x w J = val (g.t χ) y w J) : x = y := by
  have hq : x ≫ g.q.left = y ≫ g.q.left := by
    have : Mono (DegPre.prBe I D e).left := GlobalTheory.LevelCompat.mono_fstG I e D.P.A
    rw [← cancel_mono (DegPre.prBe I D e).left]
    simpa [GtCoord.pG, Category.assoc] using hA
  have hxy : x ≫ (thickObj R I e G).hom = y ≫ (thickObj R I e G).hom := by
    rw [← Over.w g.q]
    simp only [← Category.assoc, hq]
  let Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (y ≫ (thickObj R I e G).hom)
  let a : Z ⟶ thickObj R I e G := Over.homMk x hxy
  let b : Z ⟶ thickObj R I e G := Over.homMk y
  obtain ⟨τ, hτ⟩ := exists_torus g a b (by ext; exact hq)
  have := g.i_hom
  have h1i : (1 : Z ⟶ WeightPf.Te D I e) ≫ g.i = 1 := by simp
  have hc : ∀ (χ : D.X) (z : W),
      gm τ.left z ⊤ (charUnit _ D.X χ) = gm (1 : Z ⟶ WeightPf.Te D I e).left z ⊤ (charUnit _ D.X χ) := by
    intro χ z
    obtain ⟨J, hJ⟩ := TorusCoordPull.exists_good' D.P.isLB z
    have e1 := val_torus g χ hJ τ b
    have e0 := val_torus g χ hJ 1 b
    rw [← hτ] at e1
    rw [h1i, _root_.one_mul] at e0
    have ex : val (g.t χ) a.left z J = val (g.t χ) b.left z J := hV χ z J hJ
    rw [ex] at e1
    exact (mul_eq_right.mp e1.symm).trans (mul_eq_right.mp e0.symm).symm
  have hc' : ∀ χ : D.X, τ.left.appTop.hom (charUnit _ D.X χ).val =
      (1 : Z ⟶ WeightPf.Te D I e).left.appTop.hom (charUnit _ D.X χ).val := fun χ =>
    appTop_eq_of_gm _ _ _ (hc χ)
  have hτ1 : τ = 1 := by
    ext1
    apply pullback.hom_ext
    · have key : ∀ χ : D.X, (τ.left ≫ pullback.fst _ _).appTop.hom
            ((Scheme.ΓSpecIso (torusRing ZU D.X)).inv.hom (AddMonoidAlgebra.single χ 1)) =
          ((1 : Z ⟶ WeightPf.Te D I e).left ≫ pullback.fst _ _).appTop.hom
            ((Scheme.ΓSpecIso (torusRing ZU D.X)).inv.hom (AddMonoidAlgebra.single χ 1)) := by
        intro χ
        have hz := appTop_eq_of_gm (τ.left ≫ pullback.fst _ _) ((1 : Z ⟶ WeightPf.Te D I e).left ≫ pullback.fst _ _)
          (Units.map (Scheme.ΓSpecIso (torusRing ZU D.X)).inv.hom.toMonoidHom
            (Units.map (AddMonoidAlgebra.of ZU D.X) (toUnits (Multiplicative.ofAdd χ)))) (fun z => by
            have h := hc χ z
            unfold charUnit at h
            erw [gm_res, gm_res, gm_pull, gm_pull] at h
            · exact h
            all_goals simp)
        simpa using hz
      have : IsAffine (splitTorusAff ZU D.X).left := by
        unfold splitTorusAff
        exact inferInstanceAs (IsAffine (Spec _))
      apply ext_of_isAffine
      refine (cancel_epi (Scheme.ΓSpecIso (torusRing ZU D.X)).inv).mp ?_
      apply CommRingCat.hom_ext
      apply AddMonoidAlgebra.ringHom_ext
      · intro b
        obtain ⟨n⟩ := b
        have hn : (AddMonoidAlgebra.single 0 (ULift.up n) : AddMonoidAlgebra (ULift.{0} ℤ) D.X) =
            ((n : ℤ) : AddMonoidAlgebra (ULift.{0} ℤ) D.X) := by
          rw [AddMonoidAlgebra.intCast_def]
          rfl
        simp only [hn, map_intCast]
      · intro χ
        exact key χ
    · exact (Over.w τ).trans (Over.w (1 : Z ⟶ WeightPf.Te D I e)).symm
  have hab : a = b := by rw [hτ, hτ1, h1i, _root_.one_mul]
  exact congrArg Over.Hom.left hab

section Level

variable {e : ℕ} {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  (g : GtCoord I D e G) (g' : GtCoord I D' e G')

def Rel {W : Scheme.{0}} (x' : W ⟶ (thickObj R I e G').left) (x : W ⟶ (thickObj R I e G).left) : Prop :=
  (x' ≫ g'.pG.left) ≫ abMap hD = x ≫ g.pG.left ∧ ∀ (χ : D'.X) (w : W) J J', Good D.P.L w J → Good D'.P.L w J' →
    val (g.t (hD.xe χ)) x w J =
      (∏ k, om hD.w w J J' (x' ≫ D'.Oφ g'.pG χ k) ^ Oinvε k) * val (g'.t χ) x' w J'

variable {hD g g'}

/- English proof (translation)
Establish `hA : x ≫ g.pG.left = y ≫ g.pG.left` using `h₁.1.symm.trans h₂.1`. Establish `hV : ∀ (χ : D.X) (w : W) J, Good D.P.L w J → val (g.t χ) x w J = val (g.t χ) y w J`. Introduce `χ w J hJ`. Take `⟨J', hJ'⟩` from `TorusCoordPull.exists_good' D'.P.isLB w`. Take `⟨χ', rfl⟩` from `hD.xe.surjective χ`.

Rewrite using `[h₁.2 χ' w J J' hJ hJ', h₂.2 χ' w J J' hJ hJ']`. Conclude with `gtCoord_point_ext' g hA hV`.
-/
theorem Rel.unique_right {W : Scheme.{0}} {x' : W ⟶ (thickObj R I e G').left} {x y : W ⟶ (thickObj R I e G).left}
    (h₁ : Rel hD g g' x' x) (h₂ : Rel hD g g' x' y) : x = y := by
  have hA : x ≫ g.pG.left = y ≫ g.pG.left := h₁.1.symm.trans h₂.1
  have hV : ∀ (χ : D.X) (w : W) J, Good D.P.L w J → val (g.t χ) x w J = val (g.t χ) y w J := by
    intro χ w J hJ
    obtain ⟨J', hJ'⟩ := TorusCoordPull.exists_good' D'.P.isLB w
    obtain ⟨χ', rfl⟩ := hD.xe.surjective χ
    rw [h₁.2 χ' w J J' hJ hJ', h₂.2 χ' w J J' hJ hJ']
  exact gtCoord_point_ext' g hA hV

/- English proof (translation)
Establish `hA : x' ≫ g'.pG.left = y' ≫ g'.pG.left` using `(cancel_mono (abMap hD)).mp (h₁.1.trans h₂.1.symm)`. Establish `hV : ∀ (χ : D'.X) (w : W) J', Good D'.P.L w J' → val (g'.t χ) x' w J' = val (g'.t χ) y' w J'`. Introduce `χ w J' hJ'`. Take `⟨J, hJ⟩` from `TorusCoordPull.exists_good' D.P.isLB w`. Establish `e1` using `h₁.2 χ w J J' hJ hJ'`.

Establish `e2` using `h₂.2 χ w J J' hJ hJ'`. Establish `hp : ∀ k, x' ≫ D'.Oφ g'.pG χ k = y' ≫ D'.Oφ g'.pG χ k` using `fun k => Oφ_congr g'.pG g'.pG x' y' hA χ k`. Simplify using `only [hp] at e1`. Conclude with `mul_left_cancel (e1.symm.trans e2)`. Conclude with `gtCoord_point_ext' g' hA hV`.
-/
theorem Rel.unique_left {W : Scheme.{0}} {x' y' : W ⟶ (thickObj R I e G').left} {x : W ⟶ (thickObj R I e G).left}
    (h₁ : Rel hD g g' x' x) (h₂ : Rel hD g g' y' x) : x' = y' := by
  have hA : x' ≫ g'.pG.left = y' ≫ g'.pG.left := (cancel_mono (abMap hD)).mp (h₁.1.trans h₂.1.symm)
  have hV : ∀ (χ : D'.X) (w : W) J', Good D'.P.L w J' → val (g'.t χ) x' w J' = val (g'.t χ) y' w J' := by
    intro χ w J' hJ'
    obtain ⟨J, hJ⟩ := TorusCoordPull.exists_good' D.P.isLB w
    have e1 := h₁.2 χ w J J' hJ hJ'
    have e2 := h₂.2 χ w J J' hJ hJ'
    have hp : ∀ k, x' ≫ D'.Oφ g'.pG χ k = y' ≫ D'.Oφ g'.pG χ k := fun k => Oφ_congr g'.pG g'.pG x' y' hA χ k
    simp only [hp] at e1
    exact mul_left_cancel (e1.symm.trans e2)
  exact gtCoord_point_ext' g' hA hV

/- English proof (translation)
Establish `w1` using `Over.w g.pG`. Establish `w2` using `Over.w g'.pG`. Establish `w3` using `Over.w (abHom hD)`. Rewrite `w3` using `[abHom_left]`. Simplify using `only [Over.map_obj_hom] at w1 w2`.

Use `mono_thick I e` as an intermediate fact. Rewrite using `[← cancel_mono (thick R I e)]`. Use `congrArg (· ≫ D.P.A.hom) h.1` as an intermediate fact. Simplify using `only [Category.assoc, w3, w1, w2] at this`. Simplify `this.symm` using `only [Category.assoc]`.
-/
theorem Rel.comp_hom {W : Scheme.{0}} {x' : W ⟶ (thickObj R I e G').left} {x : W ⟶ (thickObj R I e G).left}
    (h : Rel hD g g' x' x) : x ≫ (thickObj R I e G).hom = x' ≫ (thickObj R I e G').hom := by
  have w1 := Over.w g.pG
  have w2 := Over.w g'.pG
  have w3 := Over.w (abHom hD)
  rw [abHom_left] at w3
  simp only [Over.map_obj_hom] at w1 w2
  have := mono_thick I e
  rw [← cancel_mono (thick R I e)]
  have := congrArg (· ≫ D.P.A.hom) h.1
  simp only [Category.assoc, w3, w1, w2] at this
  simpa only [Category.assoc] using this.symm

/- English proof (translation)
Use `ext`. Use `h.1` as an intermediate fact. Simplify using `only [Category.assoc] at this`. Simplify `this` using `[im, abHom_left]`.
-/
theorem Rel.im {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} {x' : T ⟶ thickObj R I e G'}
    {x : T ⟶ thickObj R I e G} (h : Rel hD g g' x'.left x.left) : im g' x' ≫ abHom hD = im g x := by
  ext
  have := h.1
  simp only [Category.assoc] at this
  simpa [im, abHom_left] using this

/- English proof (translation)
The claim follows from `prod_lam hD ((Over.map (thick R I e)).map x') g'.pG χ z J J'`.
-/
theorem prod_lam' {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x' : T ⟶ thickObj R I e G') (χ : D'.X)
    (z : T.left) (J J') : ∏ k, om hD.w z J J' (x'.left ≫ D'.Oφ g'.pG χ k) ^ Oinvε k =
      lam hD (T := (Over.map (thick R I e)).obj T) z J J' (im g' x') (cP D' _ χ) := prod_lam hD ((Over.map (thick R I e)).map x') g'.pG χ z J J'

/- English proof (translation)
Apply `mul_right_cancel (b := c)` to reduce the goal to its premises. Rewrite using `[h]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem alg_mul {U : Type} [CommGroup U] {ab a b c ab' a' b' c' l la lb : U} (h : ab * c = a * b)
    (h' : ab' * c' = a' * b') (ha : a = la * a') (hb : b = lb * b') (hc : c * l = la * lb * c') : ab = l * ab' := by
  apply mul_right_cancel (b := c)
  rw [h]
  calc a * b = la * lb * (a' * b') := by rw [ha, hb]; ac_rfl
    _ = la * lb * (ab' * c') := by rw [h']
    _ = ab' * (c * l) := by rw [hc]; ac_rfl
    _ = l * ab' * c := by ac_rfl

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem alg_up {U : Type} [CommGroup U] {ab a b c ab' a' b' c' l la lb : U} (h : ab = l * ab')
    (h' : ab' * c' = a' * b') (ha : a = la * a') (hb : b = lb * b') (hc : c * l = la * lb * c') : ab * c = a * b := by
  calc ab * c = ab' * (c * l) := by rw [h]; ac_rfl
    _ = la * lb * (ab' * c') := by rw [hc]; ac_rfl
    _ = a * b := by rw [h', ha, hb]; ac_rfl

/- English proof (translation)
Apply `mul_left_cancel (a := la * lb)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem alg_down {U : Type} [CommGroup U] {ab a b c ab' a' b' c' l la lb : U} (h : ab * c = a * b)
    (h' : ab = l * ab') (ha : a = la * a') (hb : b = lb * b') (hc : c * l = la * lb * c') : ab' * c' = a' * b' := by
  apply mul_left_cancel (a := la * lb)
  calc la * lb * (ab' * c') = ab' * (la * lb * c') := by ac_rfl
    _ = ab' * (c * l) := by rw [hc]
    _ = ab * c := by rw [h']; ac_rfl
    _ = la * lb * (a' * b') := by rw [h, ha, hb]; ac_rfl

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hm : TorusCoord.im g' (x' * y') ≫ abHom hD = TorusCoord.im g (x * y)`. Rewrite using `[im_mul, im_mul, abHom_mul, Rel.im h₁, Rel.im h₂]`. Use `congrArg Over.Hom.left hm` as an intermediate fact. Simplify `this` using `[TorusCoord.im, abHom_left, Category.assoc]`.

Introduce `χ w J J' hJ hJ'`. Establish `a1` using `val_t_mul_points g hG (hD.xe χ) x y w J hJ`. Establish `a2` using `val_t_mul_points g' hG χ x' y' w J' hJ'`. Establish `e1` using `h₁.2 χ w J J' hJ hJ'`. Establish `e2` using `h₂.2 χ w J J' hJ hJ'`.

Rewrite `e1` using `[prod_lam' x' χ w J J']`. Rewrite `e2` using `[prod_lam' y' χ w J J']`. Rewrite using `[prod_lam' (x' * y') χ w J J']`. Use `alg_mul a1 a2 e1 e2 ?_` and prove the remaining obligations. Establish `hcub` using `cub_lam hD hG hJ hJ' (TorusCoord.im g' x') (TorusCoord.im g' y') (cP D' _ χ)`.

Rewrite `hcub` using `[Rel.im h₁, Rel.im h₂, cPoint_comp_abHom, ← im_mul]`. Unfold `cubeVal`. Rewrite using `[(isCub_cubV D.cub hJ).s01, (isCub_cubV D.cub hJ).s12, (isCub_cubV D'.cub hJ').s01, (isCub_cubV D'.cub hJ').s12]`. Conclude with `hcub`.
-/
theorem Rel.mul (hG : GlobalFnsSt) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    {x' y' : T ⟶ thickObj R I e G'} {x y : T ⟶ thickObj R I e G} (h₁ : Rel hD g g' x'.left x.left)
    (h₂ : Rel hD g g' y'.left y.left) : Rel hD g g' (x' * y').left (x * y).left := by
  refine ⟨?_, ?_⟩
  · have hm : TorusCoord.im g' (x' * y') ≫ abHom hD = TorusCoord.im g (x * y) := by
      rw [im_mul, im_mul, abHom_mul, Rel.im h₁, Rel.im h₂]
    have := congrArg Over.Hom.left hm
    simpa [TorusCoord.im, abHom_left, Category.assoc] using this
  · intro χ w J J' hJ hJ'
    have a1 := val_t_mul_points g hG (hD.xe χ) x y w J hJ
    have a2 := val_t_mul_points g' hG χ x' y' w J' hJ'
    have e1 := h₁.2 χ w J J' hJ hJ'
    have e2 := h₂.2 χ w J J' hJ hJ'
    rw [prod_lam' x' χ w J J'] at e1
    rw [prod_lam' y' χ w J J'] at e2
    rw [prod_lam' (x' * y') χ w J J']
    refine alg_mul a1 a2 e1 e2 ?_
    have hcub := cub_lam hD hG hJ hJ' (TorusCoord.im g' x') (TorusCoord.im g' y') (cP D' _ χ)
    rw [Rel.im h₁, Rel.im h₂, cPoint_comp_abHom, ← im_mul] at hcub
    unfold cubeVal
    rw [(isCub_cubV D.cub hJ).s01, (isCub_cubV D.cub hJ).s12, (isCub_cubV D'.cub hJ').s01,
      (isCub_cubV D'.cub hJ').s12]
    exact hcub

variable (hD g g')

/- English proof (translation)
Establish `h` using `cub_lam hD hG hJ hJ' (cP D' T χ) (cP D' T χ') b`. Rewrite `h` using `[cPoint_comp_abHom, cPoint_comp_abHom, ← cPoint_add]`. Rewrite using `[lam_comm hD z J J' b (cP D' T (χ + χ')), lam_comm hD z J J' b (cP D' T χ), lam_comm hD z J J' b (cP D' T χ')]`. Conclude with `h`.
-/
theorem cub_lam_char (hG : GlobalFnsSt) {T : Over (Spec (CommRingCat.of R))} {z : T.left} {J J'}
    (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') (χ χ' : D'.X) (b : T ⟶ D'.P.A) :
    cubV D.cub z J (cP D T (hD.xe χ)) (cP D T (hD.xe χ')) (b ≫ abHom hD) * lam hD z J J' b (cP D' T (χ + χ')) =
      lam hD z J J' b (cP D' T χ) * lam hD z J J' b (cP D' T χ') * cubV D'.cub z J' (cP D' T χ) (cP D' T χ') b := by
  have h := cub_lam hD hG hJ hJ' (cP D' T χ) (cP D' T χ') b
  rw [cPoint_comp_abHom, cPoint_comp_abHom, ← cPoint_add] at h
  rw [lam_comm hD z J J' b (cP D' T (χ + χ')), lam_comm hD z J J' b (cP D' T χ),
    lam_comm hD z J J' b (cP D' T χ')]
  exact h

/- English proof (translation)
Establish `h` using `val_corr hJ (g.t_mul χ χ') (𝟙 _)`. Use `Eq.trans ?_ (h.trans (val_mul hJ _ _ _))` and prove the remaining obligations. Use `Eq.trans ?_ (val_mul hJ _ _ _).symm` and prove the remaining obligations. Use `congr 1`. Use `Eq.trans ?_ (val_pull hJ _ _ _).symm` and prove the remaining obligations.

Rewrite using `[Category.id_comp]`. Both sides reduce to the same expression.
-/
theorem val_t_mul_id (χ χ' : D.X) (y : (thickObj R I e G).left) (J) (hJ : Good D.P.L y J) :
    val (g.t (χ + χ')) (𝟙 _) y J * cubV D.cub (T := (Over.map (thick R I e)).obj (thickObj R I e G)) y J
      (cP D _ χ) (cP D _ χ') g.pG = val (g.t χ) (𝟙 _) y J * val (g.t χ') (𝟙 _) y J := by
  have h := val_corr hJ (g.t_mul χ χ') (𝟙 _)
  refine Eq.trans ?_ (h.trans (val_mul hJ _ _ _))
  refine Eq.trans ?_ (val_mul hJ _ _ _).symm
  congr 1
  refine Eq.trans ?_ (val_pull hJ _ _ _).symm
  rw [Category.id_comp]
  rfl

/- English proof (translation)
Rewrite using `[prod_O D' p χ (fun f => om hD.w z J J' (𝟙 _ ≫ f))]`. Simplify using `only [Category.id_comp, lam]`.
-/
theorem prod_lam_id {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D'.P.A) (χ : D'.X) (z : T.left)
    (J J') : ∏ k, om hD.w z J J' (𝟙 _ ≫ D'.Oφ p χ k) ^ Oinvε k = lam hD z J J' p (cP D' T χ) := by
  rw [prod_O D' p χ (fun f => om hD.w z J J' (𝟙 _ ≫ f))]
  simp only [Category.id_comp, lam]

/- English proof (translation)
Take `⟨t, ht, H⟩` from `exists_up hw hL hL' a ha`. Use `⟨t, ht, fun Z r z p q hp hq => ?_⟩` and prove the remaining obligations. Rewrite using `[Category.comp_id]`. Conclude with `H Z r z p q (Set.mem_iInter.2 fun k => hp k) (Set.mem_iInter.2 fun k => hq k)`.
-/
private theorem exists_isGen_pMaps_of_pGen {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type}
    [Fintype K] {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')}
    {ε : K → ℤ} (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε), t.IsGen ∧
      PMaps w φ' (fun k => φ' k ≫ F) ε a t (𝟙 Y) := by
  obtain ⟨t, ht, H⟩ := exists_up hw hL hL' a ha
  refine ⟨t, ht, fun Z r z p q hp hq => ?_⟩
  rw [Category.comp_id]
  exact H Z r z p q (Set.mem_iInter.2 fun k => hp k) (Set.mem_iInter.2 fun k => hq k)

/- English proof (translation)
Establish `hwg : PGen hD.w` using `(isGen_iff hD.w).mp hD.w_gen`. Set `T : Over (Spec (CommRingCat.of R))` to `(Over.map (thick R I e)).obj (thickObj R I e G')`. Set `b : T ⟶ D.P.A` to `g'.pG ≫ abHom hD`. Establish `key : ∀ χ : D.X, ∃ t : LB.Gen (LB.LinComb D.P.L (fun k => D'.Oφ g'.pG (hD.xe.symm χ) k ≫ abMap hD) Oinvε), t.IsGen ∧ PMaps hD.w (D'.Oφ g'.pG (hD.xe.symm χ)) (fun k => D'.Oφ g'.pG (hD.xe.symm χ) k ≫ abMap hD) Oinvε (g'.t (hD.xe.symm χ)) t (𝟙 _)` using `fun χ => exists_isGen_pMaps_of_pGen hwg D.P.isLB D'.P.isLB (g'.t _) (g'.t_gen _)`. Use `choose s hs hP using key`.

Establish `hφ : ∀ χ k, D'.Oφ g'.pG (hD.xe.symm χ) k ≫ abMap hD = D.Oφ b χ k`. Introduce `χ k`. Use `Oφ_pull hD b g'.pG (𝟙 _) (by simp [b, abHom_left]) (hD.xe.symm χ) k` as an intermediate fact. Simplify using `using this`. Establish `hval : ∀ χ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' → val (s χ) r z J = (∏ k, om hD.w z J J' (r ≫ D'.Oφ g'.pG (hD.xe.symm χ) k) ^ Oinvε k) * val (g'.t (hD.xe.symm χ)) r z J'`.

Introduce `χ Z r z J J' hJ hJ'`. Use `val_of_pmaps (fun k => (Category.id_comp _).symm) (hP χ) r hJ hJ'` as an intermediate fact. Rewrite `this` using `[Category.comp_id]`. Then use the resulting hypothesis. Establish `hm : ∀ (χ₁ χ₂ : D.X) y J, Good D.P.L y J → val (s (χ₁ + χ₂)) (𝟙 _) y J * cubV D.cub y J (cP D T χ₁) (cP D T χ₂) b = val (s χ₁) (𝟙 _) y J * val (s χ₂) (𝟙 _) y J`. Introduce `χ₁ χ₂ y J hJ`.

Take `⟨J', hJ'⟩` from `TorusCoordPull.exists_good' D'.P.isLB y`. Establish `e12` using `hval (χ₁ + χ₂) _ (𝟙 _) y J J' hJ hJ'`. Establish `e1` using `hval χ₁ _ (𝟙 _) y J J' hJ hJ'`. Establish `e2` using `hval χ₂ _ (𝟙 _) y J J' hJ hJ'`. Rewrite `e12`, `e1`, `e2` using `[prod_lam_id]`.

Establish `hs1 : val (g'.t (hD.xe.symm (χ₁ + χ₂))) (𝟙 _) y J' = val (g'.t (hD.xe.symm χ₁ + hD.xe.symm χ₂)) (𝟙 _) y J'` using `congrArg (fun x => val (g'.t x) (𝟙 _) y J') (map_add _ _ _)`. Establish `hs2 : lam hD y J J' g'.pG (cP D' T (hD.xe.symm (χ₁ + χ₂))) = lam hD y J J' g'.pG (cP D' T (hD.xe.symm χ₁ + hD.xe.symm χ₂))` using `congrArg (fun x => lam hD y J J' g'.pG (cP D' T x)) (map_add _ _ _)`. Rewrite `e12` using `[hs1, hs2]`. Establish `hc` using `cub_lam_char hD hG hJ hJ' (hD.xe.symm χ₁) (hD.xe.symm χ₂) g'.pG`. Rewrite `hc` using `[AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]`.

Conclude with `alg_up e12 (val_t_mul_id g' _ _ y J' hJ') e1 e2 hc`. Take `⟨x, hx1, hx2⟩` from `exists_of_vals g (thickObj R I e G').hom rfl b (fun χ k => D'.Oφ g'.pG (hD.xe.symm χ) k ≫ abMap hD) hφ s hs hm`. Use `⟨x, fun W r => ⟨?_, fun χ w J J' hJ hJ' => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, ← hx1]`. Simplify using `[b, abHom_left]`.

Rewrite using `[hx2 (hD.xe χ) W r w J hJ, hval (hD.xe χ) W r w J J' hJ hJ', AddEquiv.symm_apply_apply]`.
-/
theorem exists_fwd (hG : GlobalFnsSt) : ∃ j : (thickObj R I e G').left ⟶ (thickObj R I e G).left,
    ∀ (W : Scheme.{0}) (r : W ⟶ (thickObj R I e G').left), Rel hD g g' r (r ≫ j) := by
  have hwg : PGen hD.w := (isGen_iff hD.w).mp hD.w_gen
  let T : Over (Spec (CommRingCat.of R)) := (Over.map (thick R I e)).obj (thickObj R I e G')
  let b : T ⟶ D.P.A := g'.pG ≫ abHom hD
  have key : ∀ χ : D.X, ∃ t : LB.Gen (LB.LinComb D.P.L (fun k => D'.Oφ g'.pG (hD.xe.symm χ) k ≫ abMap hD) Oinvε),
      t.IsGen ∧ PMaps hD.w (D'.Oφ g'.pG (hD.xe.symm χ)) (fun k => D'.Oφ g'.pG (hD.xe.symm χ) k ≫ abMap hD) Oinvε
        (g'.t (hD.xe.symm χ)) t (𝟙 _) :=
    fun χ => exists_isGen_pMaps_of_pGen hwg D.P.isLB D'.P.isLB (g'.t _) (g'.t_gen _)
  choose s hs hP using key
  have hφ : ∀ χ k, D'.Oφ g'.pG (hD.xe.symm χ) k ≫ abMap hD = D.Oφ b χ k := by
    intro χ k
    have := Oφ_pull hD b g'.pG (𝟙 _) (by simp [b, abHom_left]) (hD.xe.symm χ) k
    simpa using this
  have hval : ∀ χ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (s χ) r z J = (∏ k, om hD.w z J J' (r ≫ D'.Oφ g'.pG (hD.xe.symm χ) k) ^ Oinvε k) *
        val (g'.t (hD.xe.symm χ)) r z J' := by
    intro χ Z r z J J' hJ hJ'
    have := val_of_pmaps (fun k => (Category.id_comp _).symm) (hP χ) r hJ hJ'
    rwa [Category.comp_id] at this
  have hm : ∀ (χ₁ χ₂ : D.X) y J, Good D.P.L y J → val (s (χ₁ + χ₂)) (𝟙 _) y J *
      cubV D.cub y J (cP D T χ₁) (cP D T χ₂) b = val (s χ₁) (𝟙 _) y J * val (s χ₂) (𝟙 _) y J := by
    intro χ₁ χ₂ y J hJ
    obtain ⟨J', hJ'⟩ := TorusCoordPull.exists_good' D'.P.isLB y
    have e12 := hval (χ₁ + χ₂) _ (𝟙 _) y J J' hJ hJ'
    have e1 := hval χ₁ _ (𝟙 _) y J J' hJ hJ'
    have e2 := hval χ₂ _ (𝟙 _) y J J' hJ hJ'
    rw [prod_lam_id] at e12 e1 e2
    have hs1 : val (g'.t (hD.xe.symm (χ₁ + χ₂))) (𝟙 _) y J' =
        val (g'.t (hD.xe.symm χ₁ + hD.xe.symm χ₂)) (𝟙 _) y J' :=
      congrArg (fun x => val (g'.t x) (𝟙 _) y J') (map_add _ _ _)
    have hs2 : lam hD y J J' g'.pG (cP D' T (hD.xe.symm (χ₁ + χ₂))) =
        lam hD y J J' g'.pG (cP D' T (hD.xe.symm χ₁ + hD.xe.symm χ₂)) :=
      congrArg (fun x => lam hD y J J' g'.pG (cP D' T x)) (map_add _ _ _)
    rw [hs1, hs2] at e12
    have hc := cub_lam_char hD hG hJ hJ' (hD.xe.symm χ₁) (hD.xe.symm χ₂) g'.pG
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at hc
    exact alg_up e12 (val_t_mul_id g' _ _ y J' hJ') e1 e2 hc
  obtain ⟨x, hx1, hx2⟩ := exists_of_vals g (thickObj R I e G').hom rfl b
    (fun χ k => D'.Oφ g'.pG (hD.xe.symm χ) k ≫ abMap hD) hφ s hs hm
  refine ⟨x, fun W r => ⟨?_, fun χ w J J' hJ hJ' => ?_⟩⟩
  · rw [Category.assoc, Category.assoc, ← hx1]
    simp [b, abHom_left]
  · rw [hx2 (hD.xe χ) W r w J hJ, hval (hD.xe χ) W r w J J' hJ hJ', AddEquiv.symm_apply_apply]

/- English proof (translation)
Establish `hwg : PGen hD.w` using `(isGen_iff hD.w).mp hD.w_gen`. Set `T : Over (Spec (CommRingCat.of R))` to `(Over.map (thick R I e)).obj (thickObj R I e G)`. Set `b : T ⟶ D'.P.A` to `g.pG ≫ inv (abHom hD)`. Establish `hb : b ≫ abHom hD = g.pG` using `by simp [b]`. Establish `hbl : b.left ≫ abMap hD = 𝟙 _ ≫ g.pG.left`.

Rewrite using `[Category.id_comp, ← abHom_left, ← Over.comp_left, hb]`. Establish `key : ∀ χ : D'.X, ∃ a : LB.Gen (LB.LinComb D'.P.L (D'.Oφ b χ) Oinvε), a.IsGen ∧ PMaps hD.w (D'.Oφ b χ) (D.Oφ g.pG (hD.xe χ)) Oinvε a (g.t (hD.xe χ)) (𝟙 _)` using `fun χ => exists_pmaps hwg D.P.isLB D'.P.isLB (fun k => Oφ_pull hD g.pG b (𝟙 _) hbl χ k) (g.t _) (g.t_gen _)`. Use `choose s hs hP using key`. Establish `hval : ∀ χ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' → val (g.t (hD.xe χ)) r z J = (∏ k, om hD.w z J J' (r ≫ D'.Oφ b χ k) ^ Oinvε k) * val (s χ) r z J'`. Introduce `χ Z r z J J' hJ hJ'`.

Use `val_of_pmaps (fun k => Oφ_pull hD g.pG b (𝟙 _) hbl χ k) (hP χ) r hJ hJ'` as an intermediate fact. Rewrite `this` using `[Category.comp_id]`. Then use the resulting hypothesis. Establish `hm : ∀ (χ₁ χ₂ : D'.X) y J', Good D'.P.L y J' → val (s (χ₁ + χ₂)) (𝟙 _) y J' * cubV D'.cub y J' (cP D' T χ₁) (cP D' T χ₂) b = val (s χ₁) (𝟙 _) y J' * val (s χ₂) (𝟙 _) y J'`. Introduce `χ₁ χ₂ y J' hJ'`. Take `⟨J, hJ⟩` from `TorusCoordPull.exists_good' D.P.isLB y`.

Establish `e12` using `hval (χ₁ + χ₂) _ (𝟙 _) y J J' hJ hJ'`. Establish `e1` using `hval χ₁ _ (𝟙 _) y J J' hJ hJ'`. Establish `e2` using `hval χ₂ _ (𝟙 _) y J J' hJ hJ'`. Rewrite `e12`, `e1`, `e2` using `[prod_lam_id]`. Establish `hs1 : val (g.t (hD.xe (χ₁ + χ₂))) (𝟙 _) y J = val (g.t (hD.xe χ₁ + hD.xe χ₂)) (𝟙 _) y J` using `congrArg (fun x => val (g.t x) (𝟙 _) y J) (map_add _ _ _)`.

Rewrite `e12` using `[hs1]`. Establish `hc` using `cub_lam_char hD hG hJ hJ' χ₁ χ₂ b`. Rewrite `hc` using `[hb]`. Conclude with `alg_down (val_t_mul_id g _ _ y J hJ) e12 e1 e2 hc`. Take `⟨x, hx1, hx2⟩` from `exists_of_vals g' (thickObj R I e G).hom rfl b (D'.Oφ b) (fun _ _ => rfl) s hs hm`.

Use `⟨x, fun W r => ⟨?_, fun χ w J J' hJ hJ' => ?_⟩⟩` and prove the remaining obligations. Simplify using `only [Category.assoc]`. Rewrite using `[← Category.assoc x, ← hx1, hbl, Category.id_comp]`. Rewrite using `[hval χ W r w J J' hJ hJ', hx2 χ W r w J' hJ']`. Use `congr 1`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Oφ_congr b g'.pG r (r ≫ x) (by rw [Category.assoc, ← hx1]) χ k]`.
-/
theorem exists_bwd (hG : GlobalFnsSt) : ∃ k : (thickObj R I e G).left ⟶ (thickObj R I e G').left,
    ∀ (W : Scheme.{0}) (r : W ⟶ (thickObj R I e G).left), Rel hD g g' (r ≫ k) r := by
  have hwg : PGen hD.w := (isGen_iff hD.w).mp hD.w_gen
  let T : Over (Spec (CommRingCat.of R)) := (Over.map (thick R I e)).obj (thickObj R I e G)
  let b : T ⟶ D'.P.A := g.pG ≫ inv (abHom hD)
  have hb : b ≫ abHom hD = g.pG := by simp [b]
  have hbl : b.left ≫ abMap hD = 𝟙 _ ≫ g.pG.left := by
    rw [Category.id_comp, ← abHom_left, ← Over.comp_left, hb]
  have key : ∀ χ : D'.X, ∃ a : LB.Gen (LB.LinComb D'.P.L (D'.Oφ b χ) Oinvε), a.IsGen ∧
      PMaps hD.w (D'.Oφ b χ) (D.Oφ g.pG (hD.xe χ)) Oinvε a (g.t (hD.xe χ)) (𝟙 _) :=
    fun χ => exists_pmaps hwg D.P.isLB D'.P.isLB (fun k => Oφ_pull hD g.pG b (𝟙 _) hbl χ k) (g.t _) (g.t_gen _)
  choose s hs hP using key
  have hval : ∀ χ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (g.t (hD.xe χ)) r z J = (∏ k, om hD.w z J J' (r ≫ D'.Oφ b χ k) ^ Oinvε k) * val (s χ) r z J' := by
    intro χ Z r z J J' hJ hJ'
    have := val_of_pmaps (fun k => Oφ_pull hD g.pG b (𝟙 _) hbl χ k) (hP χ) r hJ hJ'
    rwa [Category.comp_id] at this
  have hm : ∀ (χ₁ χ₂ : D'.X) y J', Good D'.P.L y J' → val (s (χ₁ + χ₂)) (𝟙 _) y J' *
      cubV D'.cub y J' (cP D' T χ₁) (cP D' T χ₂) b = val (s χ₁) (𝟙 _) y J' * val (s χ₂) (𝟙 _) y J' := by
    intro χ₁ χ₂ y J' hJ'
    obtain ⟨J, hJ⟩ := TorusCoordPull.exists_good' D.P.isLB y
    have e12 := hval (χ₁ + χ₂) _ (𝟙 _) y J J' hJ hJ'
    have e1 := hval χ₁ _ (𝟙 _) y J J' hJ hJ'
    have e2 := hval χ₂ _ (𝟙 _) y J J' hJ hJ'
    rw [prod_lam_id] at e12 e1 e2
    have hs1 : val (g.t (hD.xe (χ₁ + χ₂))) (𝟙 _) y J = val (g.t (hD.xe χ₁ + hD.xe χ₂)) (𝟙 _) y J :=
      congrArg (fun x => val (g.t x) (𝟙 _) y J) (map_add _ _ _)
    rw [hs1] at e12
    have hc := cub_lam_char hD hG hJ hJ' χ₁ χ₂ b
    rw [hb] at hc
    exact alg_down (val_t_mul_id g _ _ y J hJ) e12 e1 e2 hc
  obtain ⟨x, hx1, hx2⟩ := exists_of_vals g' (thickObj R I e G).hom rfl b (D'.Oφ b) (fun _ _ => rfl) s hs hm
  refine ⟨x, fun W r => ⟨?_, fun χ w J J' hJ hJ' => ?_⟩⟩
  · simp only [Category.assoc]
    rw [← Category.assoc x, ← hx1, hbl, Category.id_comp]
  · rw [hval χ W r w J J' hJ hJ', hx2 χ W r w J' hJ']
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Oφ_congr b g'.pG r (r ≫ x) (by rw [Category.assoc, ← hx1]) χ k]

/- English proof (translation)
Take `⟨j, hj⟩` from `exists_fwd hD g g' hG`. Take `⟨k, hk⟩` from `exists_bwd hD g g' hG`. Establish `hjk : j ≫ k = 𝟙 _`. Use `Rel.unique_left (hk _ (𝟙 _ ≫ j)) (hj _ (𝟙 _))` as an intermediate fact. Simplify using `using this`.

Establish `hkj : k ≫ j = 𝟙 _`. Use `Rel.unique_right (hk _ (𝟙 _)) (hj _ (𝟙 _ ≫ k))` as an intermediate fact. Simplify using `using this.symm`. Establish `hjo : j ≫ (thickObj R I e G).hom = (thickObj R I e G').hom`. Simplify using `using (hj _ (𝟙 _)).comp_hom`.

Establish `hko : k ≫ (thickObj R I e G').hom = (thickObj R I e G).hom`. Use `(hk _ (𝟙 _)).comp_hom` as an intermediate fact. Simplify using `only [Category.id_comp] at this`. Conclude with `this.symm`. Set `J : thickObj R I e G' ⟶ thickObj R I e G` to `Over.homMk j hjo`.

Set `K : thickObj R I e G ⟶ thickObj R I e G'` to `Over.homMk k hko`. Use `⟨⟨J, K, by ext; exact hjk, by ext; exact hkj⟩, ?_, fun W r => hj W r⟩` and prove the remaining obligations. Use `isMonHom_of_mul J fun T x y => ?_` and prove the remaining obligations. Use `ext`. Conclude with `Rel.unique_right (hj _ (x * y).left) (Rel.mul hG (hj _ x.left) (hj _ y.left))`.
-/
theorem exists_iso (hG : GlobalFnsSt) : ∃ j : thickObj R I e G' ≅ thickObj R I e G, IsMonHom j.hom ∧
    ∀ (W : Scheme.{0}) (r : W ⟶ (thickObj R I e G').left), Rel hD g g' r (r ≫ j.hom.left) := by
  obtain ⟨j, hj⟩ := exists_fwd hD g g' hG
  obtain ⟨k, hk⟩ := exists_bwd hD g g' hG
  have hjk : j ≫ k = 𝟙 _ := by
    have := Rel.unique_left (hk _ (𝟙 _ ≫ j)) (hj _ (𝟙 _))
    simpa using this
  have hkj : k ≫ j = 𝟙 _ := by
    have := Rel.unique_right (hk _ (𝟙 _)) (hj _ (𝟙 _ ≫ k))
    simpa using this.symm
  have hjo : j ≫ (thickObj R I e G).hom = (thickObj R I e G').hom := by
    simpa using (hj _ (𝟙 _)).comp_hom
  have hko : k ≫ (thickObj R I e G').hom = (thickObj R I e G).hom := by
    have := (hk _ (𝟙 _)).comp_hom
    simp only [Category.id_comp] at this
    exact this.symm
  let J : thickObj R I e G' ⟶ thickObj R I e G := Over.homMk j hjo
  let K : thickObj R I e G ⟶ thickObj R I e G' := Over.homMk k hko
  refine ⟨⟨J, K, by ext; exact hjk, by ext; exact hkj⟩, ?_, fun W r => hj W r⟩
  refine isMonHom_of_mul J fun T x y => ?_
  ext
  exact Rel.unique_right (hj _ (x * y).left) (Rel.mul hG (hj _ x.left) (hj _ y.left))

variable {hD g g'}

/- English proof (translation)
Use `⟨?_, fun χ w J J' hJ hJ' => ?_⟩` and prove the remaining obligations. Simplify using `only [Category.assoc, reassoc_of% hq', hq]`. Simplify `h.1` using `only [Category.assoc]`. Establish `e1 : val (g₁.t (hD.xe χ)) (x ≫ thickMap R I e G) w J = val (g.t (hD.xe χ)) x w J` using `(val_pull hJ _ _ _).symm.trans (val_corr hJ (ht _) x)`. Establish `e2 : val (g₁'.t χ) (x' ≫ thickMap R I e G') w J' = val (g'.t χ) x' w J'` using `(val_pull hJ' _ _ _).symm.trans (val_corr hJ' (ht' _) x')`.

Rewrite using `[e1, e2, h.2 χ w J J' hJ hJ']`. Use `congr 1`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, GlobalTheory.LevelCompat.thickMap_Oφ g' g₁' hq' χ k]`.
-/
theorem Rel.succ {g₁ : GtCoord I D (e + 1) G} {g₁' : GtCoord I D' (e + 1) G'}
    (hq : thickMap R I e G ≫ g₁.pG.left = g.pG.left)
    (ht : ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g₁.t χ) (thickMap R I e G)) (g.t χ))
    (hq' : thickMap R I e G' ≫ g₁'.pG.left = g'.pG.left)
    (ht' : ∀ χ, LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ (g₁'.t χ) (thickMap R I e G')) (g'.t χ))
    {W : Scheme.{0}} {x' : W ⟶ (thickObj R I e G').left} {x : W ⟶ (thickObj R I e G).left}
    (h : Rel hD g g' x' x) : Rel hD g₁ g₁' (x' ≫ thickMap R I e G') (x ≫ thickMap R I e G) := by
  refine ⟨?_, fun χ w J J' hJ hJ' => ?_⟩
  · simp only [Category.assoc, reassoc_of% hq', hq]
    simpa only [Category.assoc] using h.1
  · have e1 : val (g₁.t (hD.xe χ)) (x ≫ thickMap R I e G) w J = val (g.t (hD.xe χ)) x w J :=
      (val_pull hJ _ _ _).symm.trans (val_corr hJ (ht _) x)
    have e2 : val (g₁'.t χ) (x' ≫ thickMap R I e G') w J' = val (g'.t χ) x' w J' :=
      (val_pull hJ' _ _ _).symm.trans (val_corr hJ' (ht' _) x')
    rw [e1, e2, h.2 χ w J J' hJ hJ']
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Category.assoc, GlobalTheory.LevelCompat.thickMap_Oφ g' g₁' hq' χ k]

end Level

end GlobalTheory.ThickIso

namespace GlobalTheory

open NumberField ThickIso TorusCoordPull

/- English proof (translation)
Introduce `hG R _ _ _ I hI hmax D D' A A' G G' _ _ _ _ hSG hSG' U U' hD`. Establish `hwg : PGen hD.w` using `(isGen_iff hD.w).mp hD.w_gen`. Use `choose j hjm hjr using fun e => ThickIso.exists_iso hD (U.gt e) (U'.gt e) hG`. Establish `hp : ∀ e, (U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ (U.gt e).pG.left`. Introduce `e`.

Use `(hjr e _ (𝟙 _)).1` as an intermediate fact. Simplify using `only [Category.id_comp] at this`. Conclude with `this`. Establish `hO : ∀ e x κ, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ` using `fun e x κ => Oφ_pull hD (U.gt e).pG (U'.gt e).pG (j e).hom.left (hp e) x κ`. Use `⟨j, fun e => ⟨hjm e, ?_, hp e, fun x => ⟨hO e x, ?_⟩⟩⟩` and prove the remaining obligations.

Establish `r1` using `ThickIso.Rel.succ (U.gt_q e) (U.gt_t e) (U'.gt_q e) (U'.gt_t e) (hjr e _ (𝟙 _))`. Establish `r2` using `hjr (e + 1) _ (thickMap R I e G')`. Simplify using `only [Category.id_comp] at r1`. Conclude with `ThickIso.Rel.unique_right r2 r1`. Conclude with `pmaps_of_good hwg D.toPre.P.isLB D'.toPre.P.isLB (hO e x) ((U'.gt e).t_gen x) ((U.gt e).t_gen (hD.xe x)) fun y J J' hJ hJ' => (hjr e _ (𝟙 _)).2 x y J J' hJ hJ'`.
-/
theorem exists_thick_iso_of_isPullDeg : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre), ∃ (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), (∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧ (U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) (j e).hom.left) := by
  intro hG R _ _ _ I hI hmax D D' A A' G G' _ _ _ _ hSG hSG' U U' hD
  have hwg : PGen hD.w := (isGen_iff hD.w).mp hD.w_gen
  choose j hjm hjr using fun e => ThickIso.exists_iso hD (U.gt e) (U'.gt e) hG
  have hp : ∀ e, (U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) =
      (j e).hom.left ≫ (U.gt e).pG.left := by
    intro e
    have := (hjr e _ (𝟙 _)).1
    simp only [Category.id_comp] at this
    exact this
  have hO : ∀ e x κ, D'.toPre.Oφ (U'.gt e).pG x κ ≫
      (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) =
      (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ :=
    fun e x κ => Oφ_pull hD (U.gt e).pG (U'.gt e).pG (j e).hom.left (hp e) x κ
  refine ⟨j, fun e => ⟨hjm e, ?_, hp e, fun x => ⟨hO e x, ?_⟩⟩⟩
  · have r1 := ThickIso.Rel.succ (U.gt_q e) (U.gt_t e) (U'.gt_q e) (U'.gt_t e) (hjr e _ (𝟙 _))
    have r2 := hjr (e + 1) _ (thickMap R I e G')
    simp only [Category.id_comp] at r1
    exact ThickIso.Rel.unique_right r2 r1
  · exact pmaps_of_good hwg D.toPre.P.isLB D'.toPre.P.isLB (hO e x) ((U'.gt e).t_gen x) ((U.gt e).t_gen (hD.xe x))
      fun y J J' hJ hJ' => (hjr e _ (𝟙 _)).2 x y J J' hJ hJ'

end GlobalTheory
