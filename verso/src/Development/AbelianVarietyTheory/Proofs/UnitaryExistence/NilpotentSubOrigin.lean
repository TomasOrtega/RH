import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBiextDictionarySecondPartialLaw
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameCompatOfGerms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.H1 Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun GlobalTheory.FrameBiextId
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)

/- English proof (translation)
Set `π` to `(snd (Over.mk x0) G).left`. Set `f : (Over.mk x0 ⊗ G).left ⟶ Sp S` to `(fst (Over.mk x0) G).left`. Establish `hp : IsPullback π f G.hom x0` using `(IsPullback.of_hasPullback x0 G.hom).flip`. Take `⟨N, hN, M, s, hcov, -⟩` from `AmpleBaseChange.relAmple_of_isPullback hL hA hp ⊤ (isAffineOpen_top _)`. Take `⟨h, hh⟩ : ∃ h : (Over.mk x0 ⊗ G).left ⟶ (f ⁻¹ᵁ ⊤).toScheme, h ≫ (f ⁻¹ᵁ ⊤).ι = 𝟙 _` from `⟨IsOpenImmersion.lift _ (𝟙 _) (by rw [Scheme.Opens.range_ι]; exact fun _ _ => trivial), IsOpenImmersion.lift_fac _ _ _⟩`.

Establish `hy : ∀ y, (f ⁻¹ᵁ ⊤).ι (h y) = y` using `fun y => congrArg (fun g => g y) hh`. Establish `le : ∀ j : Fin 1 → L.ι, (LPow G L N (Over.mk x0)).U j ≤ h ⁻¹ᵁ (powOver (Over.mk f) (L.pull π) ⊤ N).U (fun _ _ => j 0)` using `fun j y hj => Set.mem_iInter.2 fun _ => mem_pull.2 (by show π ((f ⁻¹ᵁ ⊤).ι (h y)) ∈ L.U (j 0)`. Rewrite using `[hy]`. Conclude with `Set.mem_iInter.1 hj 0)`. Set `a : ChartPull (LPow G L N (Over.mk x0)) (powOver (Over.mk f) (L.pull π) ⊤ N) h` to `{ idx := fun j _ _ => j 0 le := le g := fun y j j' hj hj' => by`.

Use `(gm_linComb L (fun _ : Fin 1 => π) (fun _ => (N : ℤ)) (𝟙 _) y j j' hj hj').trans (Eq.trans ?_ (gm_linComb (L.pull π) (fun _ : Fin N => (f ⁻¹ᵁ ⊤).ι) (fun _ => 1) h y _ _ (le j hj) (le j' hj')).symm)` and prove the remaining obligations. Rewrite using `[Fin.prod_univ_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, zpow_one, zpow_natCast, hh]`. Conclude with `congrArg (· ^ N) (gm_pull_g L π (𝟙 _) y (fun _ => j 0) (fun _ => j' 0) (mem_pull.2 (Set.mem_iInter.1 hj 0)) (mem_pull.2 (Set.mem_iInter.1 hj' 0))).symm }`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 (show h q ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)`. Use `⟨N, hN, chartSec a (s i), (nonzeroLocus_chartSec a (s i) fun y _ _ => ?_).ge hi⟩` and prove the remaining obligations.

Take `⟨i, hi⟩` from `exists_chart hL (π y)`. Conclude with `⟨fun _ => i, Set.mem_iInter.2 fun _ => hi⟩`.
-/
theorem exists_sec_ne_zero {X0 : Scheme.{0}} {G : Over X0} [GrpObj G] [IsProper G.hom] {L : LB G.left} (hL : L.IsLB)
    (hA : RelAmple G L) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (q : (Over.mk x0 ⊗ G).left) :
    ∃ k : ℕ, 0 < k ∧ ∃ F : LB.Sec (LPow G L k (Over.mk x0)), q ∈ nonzeroLocus F := by
  let π := (snd (Over.mk x0) G).left
  let f : (Over.mk x0 ⊗ G).left ⟶ Sp S := (fst (Over.mk x0) G).left
  have hp : IsPullback π f G.hom x0 := (IsPullback.of_hasPullback x0 G.hom).flip
  obtain ⟨N, hN, M, s, hcov, -⟩ := AmpleBaseChange.relAmple_of_isPullback hL hA hp ⊤ (isAffineOpen_top _)
  obtain ⟨h, hh⟩ : ∃ h : (Over.mk x0 ⊗ G).left ⟶ (f ⁻¹ᵁ ⊤).toScheme, h ≫ (f ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift _ (𝟙 _) (by rw [Scheme.Opens.range_ι]; exact fun _ _ => trivial),
      IsOpenImmersion.lift_fac _ _ _⟩
  have hy : ∀ y, (f ⁻¹ᵁ ⊤).ι (h y) = y := fun y => congrArg (fun g => g y) hh
  have le : ∀ j : Fin 1 → L.ι, (LPow G L N (Over.mk x0)).U j ≤
      h ⁻¹ᵁ (powOver (Over.mk f) (L.pull π) ⊤ N).U (fun _ _ => j 0) := fun j y hj =>
    Set.mem_iInter.2 fun _ => mem_pull.2 (by
      show π ((f ⁻¹ᵁ ⊤).ι (h y)) ∈ L.U (j 0)
      rw [hy]; exact Set.mem_iInter.1 hj 0)
  let a : ChartPull (LPow G L N (Over.mk x0)) (powOver (Over.mk f) (L.pull π) ⊤ N) h :=
    { idx := fun j _ _ => j 0
      le := le
      g := fun y j j' hj hj' => by
        refine (gm_linComb L (fun _ : Fin 1 => π) (fun _ => (N : ℤ)) (𝟙 _) y j j' hj hj').trans
          (Eq.trans ?_ (gm_linComb (L.pull π) (fun _ : Fin N => (f ⁻¹ᵁ ⊤).ι) (fun _ => 1) h y _ _
            (le j hj) (le j' hj')).symm)
        rw [Fin.prod_univ_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, zpow_one, zpow_natCast, hh]
        exact congrArg (· ^ N) (gm_pull_g L π (𝟙 _) y (fun _ => j 0) (fun _ => j' 0)
          (mem_pull.2 (Set.mem_iInter.1 hj 0)) (mem_pull.2 (Set.mem_iInter.1 hj' 0))).symm }
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show h q ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
  refine ⟨N, hN, chartSec a (s i), (nonzeroLocus_chartSec a (s i) fun y _ _ => ?_).ge hi⟩
  obtain ⟨i, hi⟩ := exists_chart hL (π y)
  exact ⟨fun _ => i, Set.mem_iInter.2 fun _ => hi⟩

/- English proof (translation)
Rewrite using `[val_of t (κ ≫ r) w J (fun k => J (κ ≫ r ≫ φ k)) fun k => by rw [Category.assoc]]`. Establish `h : r (κ w) ∈ LB.wchart L φ fun k => J (κ ≫ r ≫ φ k)` using `Set.mem_iInter.2 fun k => hJ (κ ≫ r ≫ φ k)`. Conclude with `Units.ext ((congrArg (κ.stalkMap w).hom (gm_val r (κ w) _ h _)).trans ((Scheme.Hom.germ_stalkMap_apply κ (r ⁻¹ᵁ (LB.wchart L φ fun k => J (κ ≫ r ≫ φ k))) w h _).trans (gm_val (κ ≫ r) w _ h _).symm))`.
-/
theorem val_stalk {X Y Z W : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (κ : W ⟶ Z) (r : Z ⟶ Y) {w : W} {J : (W ⟶ X) → L.ι} (hJ : Good L w J) :
    Units.map (κ.stalkMap w).hom.toMonoidHom (val t r (κ w) fun ψ => J (κ ≫ ψ)) = val t (κ ≫ r) w J := by
  rw [val_of t (κ ≫ r) w J (fun k => J (κ ≫ r ≫ φ k)) fun k => by rw [Category.assoc]]
  have h : r (κ w) ∈ LB.wchart L φ fun k => J (κ ≫ r ≫ φ k) := Set.mem_iInter.2 fun k => hJ (κ ≫ r ≫ φ k)
  exact Units.ext ((congrArg (κ.stalkMap w).hom (gm_val r (κ w) _ h _)).trans
    ((Scheme.Hom.germ_stalkMap_apply κ (r ⁻¹ᵁ (LB.wchart L φ fun k => J (κ ≫ r ≫ φ k))) w h _).trans (gm_val (κ ≫ r) w _ h _).symm))

/- English proof (translation)
Establish `h1 : r - 1 ∣ (∑ i ∈ Finset.range k, r ^ i) - k`. Establish `: (∑ i ∈ Finset.range k, r ^ i) - k = ∑ i ∈ Finset.range k, (r ^ i - 1)`. Rewrite using `[Finset.sum_sub_distrib]`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow r 1 i`. Take `⟨c, hc⟩` from `h1`. Establish `hu : IsUnit (∑ i ∈ Finset.range k, r ^ i)`. Rewrite using `[sub_eq_iff_eq_add.1 hc]`. Conclude with `((Commute.all _ _).isNilpotent_mul_right hn).isUnit_add_right_of_commute hk (Commute.all _ _)`.

Use `geom_sum_mul r k` as an intermediate fact. Rewrite `this` using `[h, sub_self]`. Conclude with `sub_eq_zero.1 (hu.mul_right_eq_zero.1 this)`.
-/
theorem eq_one_of_pow {R : Type} [CommRing R] {r : R} {k : ℕ} (hk : IsUnit (k : R)) (hn : IsNilpotent (r - 1))
    (h : r ^ k = 1) : r = 1 := by
  have h1 : r - 1 ∣ (∑ i ∈ Finset.range k, r ^ i) - k := by
    have : (∑ i ∈ Finset.range k, r ^ i) - k = ∑ i ∈ Finset.range k, (r ^ i - 1) := by
      rw [Finset.sum_sub_distrib]; simp
    rw [this]
    exact Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow r 1 i
  obtain ⟨c, hc⟩ := h1
  have hu : IsUnit (∑ i ∈ Finset.range k, r ^ i) := by
    rw [sub_eq_iff_eq_add.1 hc]
    exact ((Commute.all _ _).isNilpotent_mul_right hn).isUnit_add_right_of_commute hk (Commute.all _ _)
  have := geom_sum_mul r k
  rw [h, sub_self] at this
  exact sub_eq_zero.1 (hu.mul_right_eq_zero.1 this)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d n : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}

/- English proof (translation)
The claim follows from `Ideal.Quotient.eq.2 (psTrunc_succ_sub f)`.
-/
theorem trunc_psJet {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ S) :
    (jetTrunc : Jet S κ (m + 1) →ₐ[S] _) (psJet (m + 1) f) = psJet m f :=
  Ideal.Quotient.eq.2 (psTrunc_succ_sub f)

variable (x0 d) in

abbrev tr (m n : ℕ) : jOG x0 d m n ⟶ jOG x0 d (m + 1) n :=
  homAt x0 (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] Jet S (Fin n × Fin d) m)

/- English proof (translation)
Rewrite using `[homAt_comp, homAt_comp]`. Use `congrArg (homAt x0) (jet_hom_ext fun s => ?_)` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, jQ_X, trunc_psJet, jetTrunc_mk, jQ_X]`.
-/
theorem tr_jQ (m : ℕ) {k : ℕ} (b : Fin k → Q S d n) :
    tr x0 d m n ≫ homAt x0 (jQ (m + 1) b) = homAt x0 (jQ m b) ≫ tr x0 d m k := by
  rw [homAt_comp, homAt_comp]
  refine congrArg (homAt x0) (jet_hom_ext fun s => ?_)
  rw [AlgHom.comp_apply, AlgHom.comp_apply, jQ_X, trunc_psJet, jetTrunc_mk, jQ_X]

/- English proof (translation)
Rewrite using `[PP, PP, ← Category.assoc, tr_jQ, Category.assoc, hx]`.
-/
theorem tr_PP (hx : ∀ m, tr x0 d m 1 ≫ x (m + 1) = x m) (m : ℕ) (u : Q S d n) :
    tr x0 d m n ≫ PP (m + 1) x u = PP m x u := by
  rw [PP, PP, ← Category.assoc, tr_jQ, Category.assoc, hx]

/- English proof (translation)
Use `(gs_stalkMap (tr x0 d m n).left y ⊤ trivial _).symm.trans ?_` and prove the remaining obligations. Rewrite using `[VV, ← trunc_psJet m f]`. Use `Eq.trans ?_ (cst_comp (𝟙 _) ((jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] Jet S (Fin n × Fin d) m) : Jet S (Fin n × Fin d) (m + 1) →+* Jet S (Fin n × Fin d) m) y _)` and prove the remaining obligations. Rewrite using `[Category.id_comp]`. Both sides reduce to the same expression.
-/
theorem tr_VV (m : ℕ) (y : (jOG x0 d m n).left) (f : PS S n d) :
    ((tr x0 d m n).left.stalkMap y).hom (VV (m + 1) ((tr x0 d m n).left y) f) = VV m y f := by
  refine (gs_stalkMap (tr x0 d m n).left y ⊤ trivial _).symm.trans ?_
  rw [VV, ← trunc_psJet m f]
  refine Eq.trans ?_ (cst_comp (𝟙 _) ((jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] Jet S (Fin n × Fin d) m) :
    Jet S (Fin n × Fin d) (m + 1) →+* Jet S (Fin n × Fin d) m) y _)
  rw [Category.id_comp]; rfl

/- English proof (translation)
Establish `hL` using `t.PP.isLB`. Take `⟨F₀, τ₀, p₀, c₀, v₀⟩` from `hf m`. Take `⟨F₁, τ₁, p₁, c₁, v₁⟩` from `hf (m + 1)`. Establish `hρx : (r ≫ (tr x0 d m 1).left) ≫ (x (m + 1)).left = r ≫ (x m).left`. Rewrite using `[Category.assoc, ← Over.comp_left, hx m]`.

Take `⟨i, hi⟩ : ∃ i, J (r ≫ (x m).left) = i` from `⟨_, rfl⟩`. Establish `mem : ∀ {Y : Scheme.{0}} (a : Z ⟶ Y) (b : Y ⟶ t.G.left), a ≫ b = r ≫ (x m).left → a z ∈ LB.wchart t.PP.L (fun _ : Fin 1 => b) (fun _ => i)` using `fun a b e => Set.mem_iInter.2 fun _ => by`. Use `hJ (r ≫ (x m).left)` as an intermediate fact. Rewrite `this` using `[hi, ← e]`. Conclude with `this`.

Establish `hps : ∀ m, (ptSecT t.G (x m)).left ≫ (snd (jOG x0 d m 1) t.G).left = (x m).left` using `fun m => by`. Rewrite using `[← Over.comp_left, ptSecT, lift_snd]`. Establish `e0` using `value_stalk t.G t.PP.L hL (k : ℤ) v₀ r z (fun _ => i) (mem _ _ rfl)`. Establish `e1` using `value_stalk t.G t.PP.L hL (k : ℤ) v₁ (r ≫ (tr x0 d m 1).left) z (fun _ => i) (mem _ _ hρx)`. Establish `l0` using `pullSec_stalk t.G t.PP.L (k : ℤ) p₀ (r ≫ (ptSecT t.G (x m)).left) z (fun _ => i) (mem _ _ (by rw [Category.assoc, hps]))`.

Establish `l1` using `pullSec_stalk t.G t.PP.L (k : ℤ) p₁ ((r ≫ (tr x0 d m 1).left) ≫ (ptSecT t.G (x (m + 1))).left) z (fun _ => i) (mem _ _ (by rw [Category.assoc, hps, hρx]))`. Establish `hmor : (r ≫ (ptSecT t.G (x m)).left) ≫ (jBaseG x0 d m 1 ▷ t.G).left = ((r ≫ (tr x0 d m 1).left) ≫ (ptSecT t.G (x (m + 1))).left) ≫ (jBaseG x0 d (m + 1) 1 ▷ t.G).left`. Simplify using `only [Category.assoc, ← Over.comp_left]`. Use `congrArg (fun f => r ≫ Over.Hom.left f) ?_` and prove the remaining obligations. Simplify using `only [ptSecT, lift_whiskerRight, comp_lift, Category.id_comp]`.

Rewrite using `[jBase_trunc, hx m]`. Establish `hu` using `(mem_nonzeroLocus_iff_pull F _ z (k := fun _ => i) (mem _ _ (by`. Rewrite using `[Category.assoc, ← Over.comp_left, whiskerRight_snd, Category.assoc, hps]))).1 hz`. Establish `hv : gs (r ≫ (tr x0 d m 1).left) z ⊤ (toΓ _ (psJet (m + 1) f)) = gs r z ⊤ (toΓ _ (psJet m f))`. Rewrite using `[← trunc_psJet m f]`.

Conclude with `cst_comp r ((jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) : Jet S (Fin 1 × Fin d) (m + 1) →+* Jet S (Fin 1 × Fin d) m) z _`. Establish `h0` using `l0.symm.trans e0`. Establish `h1` using `((congrArg (fun q => gs q z _ (F.f (fun _ => i))) hmor).trans (l1.symm.trans e1)).trans (congrArg (· * _) hv)`. Establish `hw` using `isUnit_of_mul_isUnit_left ((congrArg IsUnit h0).mp hu)`. Establish `h2` using `Units.ext (hw.mul_left_cancel (h1.symm.trans h0))`.

Conclude with `(val_genPowG t _ _ _ k _ z J).symm.trans ((val_corr hJ c₁ _).symm.trans ((val_of τ₁ _ z J (fun _ => i) fun _ => by rw [hρx]; exact hi).trans (h2.trans ((val_of τ₀ r z J (fun _ => i) fun _ => hi).symm.trans ((val_corr hJ c₀ _).trans (val_genPowG t _ _ _ k _ z J))))))`.
-/
theorem pow_eL_eq (hx : ∀ m, tr x0 d m 1 ≫ x (m + 1) = x m) {act : 𝓞 E → Pt S 1 d} {e : ∀ m, FrTyG t x0 d x m}
    {wP : PrimTyG t} {k : ℕ} {F : LB.Sec (LPow t.G t.PP.L k (Over.mk x0))} {f : PS S 1 d}
    (hf : IsGermG t x0 d x act e wP k F f) (m : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (jOG x0 d m 1).left) {z : Z}
    {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J)
    (hz : ((r ≫ (ptSecT t.G (x m)).left) ≫ (jBaseG x0 d m 1 ▷ t.G).left) z ∈ nonzeroLocus F) :
    val (eLG t x0 d x act e wP (m + 1)) (r ≫ (tr x0 d m 1).left) z J ^ k = val (eLG t x0 d x act e wP m) r z J ^ k := by
  have hL := t.PP.isLB
  obtain ⟨F₀, τ₀, p₀, c₀, v₀⟩ := hf m
  obtain ⟨F₁, τ₁, p₁, c₁, v₁⟩ := hf (m + 1)
  have hρx : (r ≫ (tr x0 d m 1).left) ≫ (x (m + 1)).left = r ≫ (x m).left := by
    rw [Category.assoc, ← Over.comp_left, hx m]
  obtain ⟨i, hi⟩ : ∃ i, J (r ≫ (x m).left) = i := ⟨_, rfl⟩
  have mem : ∀ {Y : Scheme.{0}} (a : Z ⟶ Y) (b : Y ⟶ t.G.left), a ≫ b = r ≫ (x m).left →
      a z ∈ LB.wchart t.PP.L (fun _ : Fin 1 => b) (fun _ => i) := fun a b e => Set.mem_iInter.2 fun _ => by
    have := hJ (r ≫ (x m).left)
    rw [hi, ← e] at this
    exact this
  have hps : ∀ m, (ptSecT t.G (x m)).left ≫ (snd (jOG x0 d m 1) t.G).left = (x m).left := fun m => by
    rw [← Over.comp_left, ptSecT, lift_snd]
  have e0 := value_stalk t.G t.PP.L hL (k : ℤ) v₀ r z (fun _ => i) (mem _ _ rfl)
  have e1 := value_stalk t.G t.PP.L hL (k : ℤ) v₁ (r ≫ (tr x0 d m 1).left) z (fun _ => i) (mem _ _ hρx)
  have l0 := pullSec_stalk t.G t.PP.L (k : ℤ) p₀ (r ≫ (ptSecT t.G (x m)).left) z (fun _ => i)
    (mem _ _ (by rw [Category.assoc, hps]))
  have l1 := pullSec_stalk t.G t.PP.L (k : ℤ) p₁ ((r ≫ (tr x0 d m 1).left) ≫ (ptSecT t.G (x (m + 1))).left) z
    (fun _ => i) (mem _ _ (by rw [Category.assoc, hps, hρx]))
  have hmor : (r ≫ (ptSecT t.G (x m)).left) ≫ (jBaseG x0 d m 1 ▷ t.G).left =
      ((r ≫ (tr x0 d m 1).left) ≫ (ptSecT t.G (x (m + 1))).left) ≫ (jBaseG x0 d (m + 1) 1 ▷ t.G).left := by
    simp only [Category.assoc, ← Over.comp_left]
    refine congrArg (fun f => r ≫ Over.Hom.left f) ?_
    simp only [ptSecT, lift_whiskerRight, comp_lift, Category.id_comp]
    rw [jBase_trunc, hx m]
  have hu := (mem_nonzeroLocus_iff_pull F _ z (k := fun _ => i) (mem _ _ (by
    rw [Category.assoc, ← Over.comp_left, whiskerRight_snd, Category.assoc, hps]))).1 hz
  have hv : gs (r ≫ (tr x0 d m 1).left) z ⊤ (toΓ _ (psJet (m + 1) f)) = gs r z ⊤ (toΓ _ (psJet m f)) := by
    rw [← trunc_psJet m f]
    exact cst_comp r ((jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) :
      Jet S (Fin 1 × Fin d) (m + 1) →+* Jet S (Fin 1 × Fin d) m) z _
  have h0 := l0.symm.trans e0
  have h1 := ((congrArg (fun q => gs q z _ (F.f (fun _ => i))) hmor).trans (l1.symm.trans e1)).trans
    (congrArg (· * _) hv)
  have hw := isUnit_of_mul_isUnit_left ((congrArg IsUnit h0).mp hu)
  have h2 := Units.ext (hw.mul_left_cancel (h1.symm.trans h0))
  exact (val_genPowG t _ _ _ k _ z J).symm.trans ((val_corr hJ c₁ _).symm.trans
    ((val_of τ₁ _ z J (fun _ => i) fun _ => by rw [hρx]; exact hi).trans (h2.trans
      ((val_of τ₀ r z J (fun _ => i) fun _ => hi).symm.trans ((val_corr hJ c₀ _).trans (val_genPowG t _ _ _ k _ z J))))))

/- English proof (translation)
Establish `h : Ideal.Quotient.mkₐ S (nilradical (Jet S (Fin 2 × Fin d) m)) = (Ideal.Quotient.mkₐ S (nilradical (Jet S (Fin 2 × Fin d) m))).comp (jQ m ![(0 : Q S d 2), 0])` using `jet_hom_ext fun s => by`. Establish `z : psJet m (((![(0 : Q S d 2), 0] : Fin 2 → Q S d 2) s.1).1 s.2) = 0`. Take `⟨i, j⟩` from `s`. Apply the tactic sequence `fin_cases i <;> exact psJet_zero m`. Rewrite using `[AlgHom.comp_apply, jQ_X, z, map_zero]`.

Use `Ideal.Quotient.eq_zero_iff_mem.2 ⟨m + 1, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow (X_mem_orig s) _)`. Conclude with `Ideal.Quotient.eq.1 (AlgHom.congr_fun h a)`.
-/
theorem nilpotent_sub_origin (m : ℕ) (a : Jet S (Fin 2 × Fin d) m) :
    IsNilpotent (a - jQ m ![(0 : Q S d 2), 0] a) := by
  have h : Ideal.Quotient.mkₐ S (nilradical (Jet S (Fin 2 × Fin d) m)) =
      (Ideal.Quotient.mkₐ S (nilradical (Jet S (Fin 2 × Fin d) m))).comp (jQ m ![(0 : Q S d 2), 0]) :=
    jet_hom_ext fun s => by
      have z : psJet m (((![(0 : Q S d 2), 0] : Fin 2 → Q S d 2) s.1).1 s.2) = 0 := by
        obtain ⟨i, j⟩ := s
        fin_cases i <;> exact psJet_zero m
      rw [AlgHom.comp_apply, jQ_X, z, map_zero]
      refine Ideal.Quotient.eq_zero_iff_mem.2 ⟨m + 1, ?_⟩
      rw [← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow (X_mem_orig s) _)
  exact Ideal.Quotient.eq.1 (AlgHom.congr_fun h a)

def cstHom {V : Type} [CommRing V] (y : Sp V) : V →+* (Sp V).presheaf.stalk y :=
  ((Sp V).presheaf.germ ⊤ y trivial).hom.comp (toΓ V)

/- English proof (translation)
The claim follows from `gs_eq (𝟙 _) y ⊤ trivial _`.
-/
theorem cst_eq {V : Type} [CommRing V] (y : Sp V) (a : V) : cst (𝟙 _) y a = cstHom y a := gs_eq (𝟙 _) y ⊤ trivial _

/- English proof (translation)
Establish `k` using `congrArg Additive.ofMul h`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv] at k ⊢`. Take the linear combination `(norm := abel) -k`.
-/
theorem mul_div_alg {U : Type} [CommGroup U] {c a b d p q r : U}
    (h : c * (p * a)⁻¹ * (q * b) * (r * d) = c * a⁻¹ * b * d) : p = q * r := by
  have k := congrArg Additive.ofMul h
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at k ⊢
  linear_combination (norm := abel) -k

variable {G : FGLaw S d} {A : Germ.OAct (𝓞 E) G} {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)}
  {uvec : κ → Fin d → S} {e : ∀ m, FrTyG t x0 d x m} {ph1 ph2 : PS S 3 d} {sy : PS S 2 d} {ad : 𝓞 E → PS S 2 d}

/- English proof (translation)
Establish `hL` using `t.PP.isLB`. Introduce `m`. Establish `hφ : ∀ I : ULift.{0} (Finset (Fin 2)), (tr x0 d m 2).left ≫ cφG t ![jptG t x0 d x (m + 1) (0 : Fin 2), jptG t x0 d x (m + 1) (1 : Fin 2)] I = cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I` using `fun I => by`. Apply the tactic sequence `have : (fun i => tr x0 d m 2 ≫ (![jptG t x0 d x (m + 1) (0 : Fin 2), jptG t x0 d x (m + 1) (1 : Fin 2)] : Fin 2 → _) i) = ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] := funext fun i => by fin_cases i <;> simp only [PP_gen] <;> exact tr_PP hc.trunc m _`. Simplify using `only [cφG, ← Over.comp_left]`.

Conclude with `congrArg (fun f => Over.Hom.left f) ((psum_hom (preHom (tr x0 d m 2)) _ I.down).trans (congrArg (fun f => psum t.G f I.down) this))`. Take `⟨U, hU⟩` from `GermB.exists_ratio _ hL (fun _ _ h => Finset.prod_congr rfl fun I _ => congrArg (h · ^ _) (hφ I)) (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x (m + 1) (0 : Fin 2), jptG t x0 d x (m + 1) (1 : Fin 2)]) (cε 2) (e (m + 1)) (tr x0 d m 2).left) (pullGen_isGen _ _ _ _ (hf.gen (m + 1)) _) ( …`. Take `⟨a, ha⟩ : ∃ a, toΓ (Jet S (Fin 2 × Fin d) m) a = U.val` from `⟨_, congrArg (fun f => CommRingCat.Hom.hom f U.val) (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of (Jet S (Fin 2 × Fin d) m))))⟩`. Set `R : ∀ y : (jOG x0 d m 2).left, Q S d 2 → Q S d 2 → ((jOG x0 d m 2).left.presheaf.stalk y)ˣ` to `fun y u v => gm (homAt x0 (jQ m ![u, v])).left y ⊤ U`. Establish `hR : ∀ y u v, (R y u v).val = cstHom y (jQ m ![u, v] a)` using `fun y u v => by`.

Use `(gs_unit _ y ⊤ trivial U).symm.trans (Eq.trans ?_ ((cst_comp (𝟙 _) (jQ m ![u, v] : Jet S (Fin 2 × Fin d) m →+* Jet S (Fin 2 × Fin d) m) y a).trans (cst_eq y _)))` and prove the remaining obligations. Rewrite using `[← ha, Category.id_comp]`. Both sides reduce to the same expression. Set `σ` to `fun y : (jOG x0 d m 2).left => Units.map ((tr x0 d m 2).left.stalkMap y).hom.toMonoidHom`. Establish `good : ∀ y J, Good t.PP.L y J → Good t.PP.L ((tr x0 d m 2).left y) fun ψ => J ((tr x0 d m 2).left ≫ ψ)` using `fun y J hJ ψ => hJ ((tr x0 d m 2).left ≫ ψ)`.

Establish `σe : ∀ y J, Good t.PP.L y J → ∀ u v, σ y (ee x e ((tr x0 d m 2).left y) (fun ψ => J ((tr x0 d m 2).left ≫ ψ)) u v) = R y u v * ee x e y J u v` using `fun y J hJ u v => by`. Use `(val_stalk _ _ _ hJ).trans (Eq.trans ?_ (hU _ (homAt x0 (jQ m ![u, v])).left y J hJ))` and prove the remaining obligations. Use `Eq.trans ?_ (val_pull hJ _ _ _).symm` and prove the remaining obligations. Rewrite using `[← Over.comp_left, ← Over.comp_left, tr_jQ]`. Establish `σV : ∀ (y : (jOG x0 d m 2).left) (f : PS S 2 d) (w w'), VV (m + 1) ((tr x0 d m 2).left y) f = Units.val w → VV m y f = Units.val w' → σ y w = w'` using `fun y f w w' h h' => Units.ext ((congrArg ((tr x0 d m 2).left.stalkMap y).hom h.symm).trans ((tr_VV m y f).trans h'))`.

Establish `R1 : ∀ y J, Good t.PP.L y J → ∀ u v w, R y (op (FQ G) u v) w = R y u w * R y v w` using `fun y J hJ u v w => by`. Establish `k` using `σV y _ _ _ (frame_biext_dictionary_first_partial_law (good y J hJ) hf u v w) (frame_biext_dictionary_first_partial_law hJ hf u v w)`. Establish `c : σ y (cubV t.cub _ (fun ψ => J ((tr x0 d m 2).left ≫ ψ)) (PP (m + 1) x u) (PP (m + 1) x v) (PP (m + 1) x w)) = cubV t.cub y J (PP m x u) (PP m x v) (PP m x w)`. Use `(val_stalk _ _ _ hJ).trans ?_` and prove the remaining obligations. Rewrite using `[← Over.comp_left, comp_lift, comp_lift, tr_PP hc.trunc, tr_PP hc.trunc, tr_PP hc.trunc]`.

Both sides reduce to the same expression. Rewrite `k` using `[map_mul, map_mul, map_mul, map_inv, c, σe y J hJ, σe y J hJ, σe y J hJ]`. Conclude with `mul_div_alg k`. Establish `R2 : ∀ y J, Good t.PP.L y J → ∀ u v, R y v u = R y u v` using `fun y J hJ u v => by`. Establish `k` using `σV y _ _ _ (dict_sy (good y J hJ) hf u v) (dict_sy hJ hf u v)`.

Rewrite `k` using `[map_mul, map_inv, σe y J hJ, σe y J hJ]`. Establish `k'` using `congrArg Additive.ofMul k`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv] at k' ⊢`. Take the linear combination `(norm := abel) k'`.

Establish `R3 : ∀ y J, Good t.PP.L y J → ∀ b u v, R y (ac (AQ A b) u) v = R y u (ac (AQ A (H.bar b)) v)` using `fun y J hJ b u v => by`. Take `⟨wL, -, hw⟩` from `hf.ad b`. Take `⟨U₀, p₀, q₀⟩` from `hw m`. Take `⟨U₁, p₁, q₁⟩` from `hw (m + 1)`. Establish `k` using `σV y _ _ _ (dict_ad (good y J hJ) b wL U₁ p₁ q₁ u v) (dict_ad hJ b wL U₀ p₀ q₀ u v)`.

Establish `c : σ y (val₂ wL _ (fun ψ => J ((tr x0 d m 2).left ≫ ψ)) (PP (m + 1) x u) (PP (m + 1) x v)) = val₂ wL y J (PP m x u) (PP m x v)`. Use `(val_stalk _ _ _ hJ).trans ?_` and prove the remaining obligations. Rewrite using `[← Over.comp_left, comp_lift, tr_PP hc.trunc, tr_PP hc.trunc]`. Both sides reduce to the same expression. Rewrite `k` using `[map_mul, map_mul, map_inv, c, σe y J hJ, σe y J hJ]`.

Establish `k'` using `congrArg Additive.ofMul k`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv] at k' ⊢`. Take the linear combination `(norm := abel) k'`. Establish `a0 : jQ m ![(0 : Q S d 2), 0] a = 1` using `cst_ext fun y => by choose J hJ using fun ψ : (jOG x0 d m 2).left ⟶ t.G.left => exists_chart hL (ψ y)`.

Establish `k` using `R1 y J hJ 0 0 0`. Rewrite `k` using `[op0]`. Rewrite using `[cst_eq, cst_eq, map_one, ← hR, left_eq_mul.1 k, Units.val_one]`. Establish `nil : ∀ y u v, IsNilpotent ((R y u v).val - 1)` using `fun y u v => by`. Use `((nilpotent_sub_origin m a).map (jQ m ![u, v])).map (cstHom (V := Jet S (Fin 2 × Fin d) m) y)` as an intermediate fact.

Rewrite `this` using `[a0, map_sub, map_sub, map_one, map_one, ← hR]`. Then use the resulting hypothesis. Establish `vL : ∀ {m : ℕ} (y : (jOG x0 d m 2).left) J, Good t.PP.L y J → ∀ u : Q S d 2, val (eLG t x0 d x A.act e wP m) (homAt x0 (jQ m ![u])).left y J = val wP (PP m x u).left y J * ee x e y J u (ac (AQ A H.w0) u)` using `fun {m} y J hJ u => by`. Establish `e₀` using `val_peG x hJ e ![u] ![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (A.act H.w0 j)] (gen 0) (ac (AQ A H.w0) (gen 0)) (by rintro ⟨l, j⟩; fin_cases l; exacts [hX 0 j, FrameBiextId.hA _ 0 j]) (by rintro ⟨l, j⟩; fin_cases l exacts [MvPolynomial.constantCoeff_X _ _, …`. Rewrite `e₀` using `[sq_ac, sq_gen]`. Conclude with `(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _) e₀)`.

Establish `R4 : ∀ y J, Good t.PP.L y J → ∀ u, R y u (ac (AQ A H.w0) u) = 1` using `fun y J hJ u => by`. Take `⟨k, hk, F, hF⟩` from `exists_sec_ne_zero hL hA x0 ((((homAt x0 (jQ m ![u])).left ≫ (ptSecT t.G (x m)).left) ≫ (jBaseG x0 d m 1 ▷ t.G).left) y)`. Take `⟨f, hf⟩` from `hg k F`. Establish `p` using `pow_eL_eq hc.trunc hf m _ hJ hF`. Establish `q` using `congrArg (σ y) (vL _ _ (good y J hJ) u)`.

Rewrite `q` using `[map_mul, σe y J hJ]`. Establish `q₁` using `(val_stalk _ _ _ hJ).symm.trans (q.trans (congrArg (· * _) (val_stalk _ _ _ hJ)))`. Rewrite `q₁` using `[← Over.comp_left, ← Over.comp_left, tr_jQ, tr_PP hc.trunc, Over.comp_left]`. Rewrite `p` using `[q₁, vL y J hJ u, mul_left_comm, mul_pow, mul_eq_right]`. Use `Units.ext (eq_one_of_pow (k := k) ?_ (nil y _ _) (congrArg Units.val p))` and prove the remaining obligations.

Use `(IsUnit.mk0 (k : ℚ) (by exact_mod_cast hk.ne')).map ((cstHom (V := Jet S (Fin 2 × Fin d) m) y).comp ((algebraMap S _).comp (algebraMap ℚ S)))` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Use `corr_of_val hL fun y J hJ => ?_` and prove the remaining obligations. Establish `R5 : ∀ u v, R y u v = 1` using `fun u v => by`. Establish `k` using `R4 y J hJ (op (FQ G) u v)`.

Rewrite `k` using `[ac_op, R1 y J hJ, R2 y J hJ _ u, R2 y J hJ _ v, R1 y J hJ, R1 y J hJ, R2 y J hJ u (ac _ u), R4 y J hJ, R2 y J hJ v (ac _ v), R4 y J hJ, _root_.one_mul, _root_.mul_one, R3 y J hJ H.w0 u v, R2 y J hJ _ u, ← R1 y J hJ, ← ac_add, HostModel.cmHost_bar_halfIntegerGenerator, add_sub_ca …`. Rewrite using `[R2 y J hJ, k]`. Establish `hid : (homAt x0 (jQ m ![(gen 0 : Q S d 2), gen 1])).left = 𝟙 _`. Establish `: jQ m ![(gen 0 : Q S d 2), gen 1] = AlgHom.id S _` using `jet_hom_ext fun s => by`. Take `⟨i, j⟩` from `s`.

Rewrite using `[jQ_X]`. Apply the tactic sequence `fin_cases i <;> exact psJet_X m _`. Rewrite using `[this]`. Conclude with `Spec.map_id _`. Establish `k` using `R5 (gen 0) (gen 1)`.

Simplify using `only [R, hid] at k`. Conclude with `(hU _ (𝟙 _) y J hJ).trans ((congrArg (· * _) k).trans (_root_.one_mul _))`.
-/
theorem frTrunc_of_germs [Algebra ℚ S] [IsProper t.G.hom] (hA : RelAmple t.G t.PP.L)
    (hc : IsChartG t x0 d G.F A.act tg uvec x) (hf : IsFrameG t x0 d x G.F A.act ph1 ph2 sy ad e) {wP : PrimTyG t}
    (hg : ∀ (k : ℕ) (F : LB.Sec (LPow t.G t.PP.L k (Over.mk x0))), ∃ f, IsGermG t x0 d x A.act e wP k F f) :
    FrTrunc t x0 d x e := by
  have hL := t.PP.isLB
  intro m
  have hφ : ∀ I : ULift.{0} (Finset (Fin 2)), (tr x0 d m 2).left ≫ cφG t ![jptG t x0 d x (m + 1) (0 : Fin 2), jptG t x0 d x (m + 1) (1 : Fin 2)] I =
      cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I := fun I => by
    have : (fun i => tr x0 d m 2 ≫ (![jptG t x0 d x (m + 1) (0 : Fin 2), jptG t x0 d x (m + 1) (1 : Fin 2)] :
        Fin 2 → _) i) = ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] := funext fun i => by
      fin_cases i <;> simp only [PP_gen] <;> exact tr_PP hc.trunc m _
    simp only [cφG, ← Over.comp_left]
    exact congrArg (fun f => Over.Hom.left f) ((psum_hom (preHom (tr x0 d m 2)) _ I.down).trans
      (congrArg (fun f => psum t.G f I.down) this))
  obtain ⟨U, hU⟩ := GermB.exists_ratio _ hL (fun _ _ h => Finset.prod_congr rfl fun I _ => congrArg (h · ^ _) (hφ I))
    (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x (m + 1) (0 : Fin 2), jptG t x0 d x (m + 1) (1 : Fin 2)]) (cε 2)
      (e (m + 1)) (tr x0 d m 2).left) (pullGen_isGen _ _ _ _ (hf.gen (m + 1)) _)
    (φ' := cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (ε' := cε 2) (e m) (hf.gen m)
  obtain ⟨a, ha⟩ : ∃ a, toΓ (Jet S (Fin 2 × Fin d) m) a = U.val := ⟨_, congrArg (fun f => CommRingCat.Hom.hom f U.val)
    (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of (Jet S (Fin 2 × Fin d) m))))⟩
  let R : ∀ y : (jOG x0 d m 2).left, Q S d 2 → Q S d 2 → ((jOG x0 d m 2).left.presheaf.stalk y)ˣ :=
    fun y u v => gm (homAt x0 (jQ m ![u, v])).left y ⊤ U
  have hR : ∀ y u v, (R y u v).val = cstHom y (jQ m ![u, v] a) := fun y u v => by
    refine (gs_unit _ y ⊤ trivial U).symm.trans (Eq.trans ?_ ((cst_comp (𝟙 _)
      (jQ m ![u, v] : Jet S (Fin 2 × Fin d) m →+* Jet S (Fin 2 × Fin d) m) y a).trans (cst_eq y _)))
    rw [← ha, Category.id_comp]; rfl
  let σ := fun y : (jOG x0 d m 2).left => Units.map ((tr x0 d m 2).left.stalkMap y).hom.toMonoidHom
  have good : ∀ y J, Good t.PP.L y J → Good t.PP.L ((tr x0 d m 2).left y) fun ψ => J ((tr x0 d m 2).left ≫ ψ) :=
    fun y J hJ ψ => hJ ((tr x0 d m 2).left ≫ ψ)
  have σe : ∀ y J, Good t.PP.L y J → ∀ u v,
      σ y (ee x e ((tr x0 d m 2).left y) (fun ψ => J ((tr x0 d m 2).left ≫ ψ)) u v) = R y u v * ee x e y J u v :=
    fun y J hJ u v => by
      refine (val_stalk _ _ _ hJ).trans (Eq.trans ?_ (hU _ (homAt x0 (jQ m ![u, v])).left y J hJ))
      refine Eq.trans ?_ (val_pull hJ _ _ _).symm
      rw [← Over.comp_left, ← Over.comp_left, tr_jQ]
  have σV : ∀ (y : (jOG x0 d m 2).left) (f : PS S 2 d) (w w'), VV (m + 1) ((tr x0 d m 2).left y) f = Units.val w →
      VV m y f = Units.val w' → σ y w = w' := fun y f w w' h h' =>
    Units.ext ((congrArg ((tr x0 d m 2).left.stalkMap y).hom h.symm).trans ((tr_VV m y f).trans h'))
  have R1 : ∀ y J, Good t.PP.L y J → ∀ u v w, R y (op (FQ G) u v) w = R y u w * R y v w := fun y J hJ u v w => by
    have k := σV y _ _ _ (frame_biext_dictionary_first_partial_law (good y J hJ) hf u v w) (frame_biext_dictionary_first_partial_law hJ hf u v w)
    have c : σ y (cubV t.cub _ (fun ψ => J ((tr x0 d m 2).left ≫ ψ)) (PP (m + 1) x u) (PP (m + 1) x v)
        (PP (m + 1) x w)) = cubV t.cub y J (PP m x u) (PP m x v) (PP m x w) := by
      refine (val_stalk _ _ _ hJ).trans ?_
      rw [← Over.comp_left, comp_lift, comp_lift, tr_PP hc.trunc, tr_PP hc.trunc, tr_PP hc.trunc]; rfl
    rw [map_mul, map_mul, map_mul, map_inv, c, σe y J hJ, σe y J hJ, σe y J hJ] at k
    exact mul_div_alg k
  have R2 : ∀ y J, Good t.PP.L y J → ∀ u v, R y v u = R y u v := fun y J hJ u v => by
    have k := σV y _ _ _ (dict_sy (good y J hJ) hf u v) (dict_sy hJ hf u v)
    rw [map_mul, map_inv, σe y J hJ, σe y J hJ] at k
    have k' := congrArg Additive.ofMul k
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at k' ⊢
    linear_combination (norm := abel) k'
  have R3 : ∀ y J, Good t.PP.L y J → ∀ b u v, R y (ac (AQ A b) u) v = R y u (ac (AQ A (H.bar b)) v) :=
    fun y J hJ b u v => by
      obtain ⟨wL, -, hw⟩ := hf.ad b
      obtain ⟨U₀, p₀, q₀⟩ := hw m
      obtain ⟨U₁, p₁, q₁⟩ := hw (m + 1)
      have k := σV y _ _ _ (dict_ad (good y J hJ) b wL U₁ p₁ q₁ u v) (dict_ad hJ b wL U₀ p₀ q₀ u v)
      have c : σ y (val₂ wL _ (fun ψ => J ((tr x0 d m 2).left ≫ ψ)) (PP (m + 1) x u) (PP (m + 1) x v)) =
          val₂ wL y J (PP m x u) (PP m x v) := by
        refine (val_stalk _ _ _ hJ).trans ?_
        rw [← Over.comp_left, comp_lift, tr_PP hc.trunc, tr_PP hc.trunc]; rfl
      rw [map_mul, map_mul, map_inv, c, σe y J hJ, σe y J hJ] at k
      have k' := congrArg Additive.ofMul k
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv] at k' ⊢
      linear_combination (norm := abel) k'
  have a0 : jQ m ![(0 : Q S d 2), 0] a = 1 := cst_ext fun y => by
    choose J hJ using fun ψ : (jOG x0 d m 2).left ⟶ t.G.left => exists_chart hL (ψ y)
    have k := R1 y J hJ 0 0 0
    rw [op0] at k
    rw [cst_eq, cst_eq, map_one, ← hR, left_eq_mul.1 k, Units.val_one]
  have nil : ∀ y u v, IsNilpotent ((R y u v).val - 1) := fun y u v => by
    have := ((nilpotent_sub_origin m a).map (jQ m ![u, v])).map (cstHom (V := Jet S (Fin 2 × Fin d) m) y)
    rwa [a0, map_sub, map_sub, map_one, map_one, ← hR] at this
  have vL : ∀ {m : ℕ} (y : (jOG x0 d m 2).left) J, Good t.PP.L y J → ∀ u : Q S d 2,
      val (eLG t x0 d x A.act e wP m) (homAt x0 (jQ m ![u])).left y J =
        val wP (PP m x u).left y J * ee x e y J u (ac (AQ A H.w0) u) := fun {m} y J hJ u => by
    have e₀ := val_peG x hJ e ![u] ![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (A.act H.w0 j)]
      (gen 0) (ac (AQ A H.w0) (gen 0)) (by rintro ⟨l, j⟩; fin_cases l; exacts [hX 0 j, FrameBiextId.hA _ 0 j])
      (by rintro ⟨l, j⟩; fin_cases l
          exacts [MvPolynomial.constantCoeff_X _ _, (FBIdPh.cc_psIn d m _ _).trans (A.const _ j)])
    rw [sq_ac, sq_gen] at e₀
    exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _) e₀)
  have R4 : ∀ y J, Good t.PP.L y J → ∀ u, R y u (ac (AQ A H.w0) u) = 1 := fun y J hJ u => by
    obtain ⟨k, hk, F, hF⟩ := exists_sec_ne_zero hL hA x0
      ((((homAt x0 (jQ m ![u])).left ≫ (ptSecT t.G (x m)).left) ≫ (jBaseG x0 d m 1 ▷ t.G).left) y)
    obtain ⟨f, hf⟩ := hg k F
    have p := pow_eL_eq hc.trunc hf m _ hJ hF
    have q := congrArg (σ y) (vL _ _ (good y J hJ) u)
    rw [map_mul, σe y J hJ] at q
    have q₁ := (val_stalk _ _ _ hJ).symm.trans (q.trans (congrArg (· * _) (val_stalk _ _ _ hJ)))
    rw [← Over.comp_left, ← Over.comp_left, tr_jQ, tr_PP hc.trunc, Over.comp_left] at q₁
    rw [q₁, vL y J hJ u, mul_left_comm, mul_pow, mul_eq_right] at p
    refine Units.ext (eq_one_of_pow (k := k) ?_ (nil y _ _) (congrArg Units.val p))
    have := (IsUnit.mk0 (k : ℚ) (by exact_mod_cast hk.ne')).map ((cstHom (V := Jet S (Fin 2 × Fin d) m) y).comp
      ((algebraMap S _).comp (algebraMap ℚ S)))
    rwa [map_natCast] at this
  refine corr_of_val hL fun y J hJ => ?_
  have R5 : ∀ u v, R y u v = 1 := fun u v => by
    have k := R4 y J hJ (op (FQ G) u v)
    rw [ac_op, R1 y J hJ, R2 y J hJ _ u, R2 y J hJ _ v, R1 y J hJ, R1 y J hJ, R2 y J hJ u (ac _ u), R4 y J hJ,
      R2 y J hJ v (ac _ v), R4 y J hJ, _root_.one_mul, _root_.mul_one, R3 y J hJ H.w0 u v, R2 y J hJ _ u,
      ← R1 y J hJ, ← ac_add, HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, ac_one] at k
    rw [R2 y J hJ, k]
  have hid : (homAt x0 (jQ m ![(gen 0 : Q S d 2), gen 1])).left = 𝟙 _ := by
    have : jQ m ![(gen 0 : Q S d 2), gen 1] = AlgHom.id S _ := jet_hom_ext fun s => by
      obtain ⟨i, j⟩ := s
      rw [jQ_X]
      fin_cases i <;> exact psJet_X m _
    rw [this]; exact Spec.map_id _
  have k := R5 (gen 0) (gen 1)
  simp only [R, hid] at k
  exact (hU _ (𝟙 _) y J hJ).trans ((congrArg (· * _) k).trans (_root_.one_mul _))

end GlobalTheory.FrameCompatOfGerms
