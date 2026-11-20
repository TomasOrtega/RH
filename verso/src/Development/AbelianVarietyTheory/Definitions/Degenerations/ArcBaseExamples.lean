import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecExtendOfNonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN.Model

variable {Z : Scheme.{0}} (G : Over Z) (A : LB Z) (N : ℕ)

/- English proof (translation)
The claim follows from `(Over.w (snd T G)).trans (Over.w (fst T G)).symm`.
-/
theorem snd_hom (T : Over Z) : (snd T G).left ≫ G.hom = (fst T G).left ≫ T.hom :=
  (Over.w (snd T G)).trans (Over.w (fst T G)).symm

/- English proof (translation)
Rewrite using `[snd_hom]`. Conclude with `hT _`.
-/
theorem mem_chart {T : Over Z} {i : A.ι} (hT : ∀ t, T.hom t ∈ A.U i) {Y : Scheme.{0}} (r : Y ⟶ (T ⊗ G).left) (y : Y) :
    (r ≫ (snd T G).left ≫ G.hom) y ∈ A.U i := by
  rw [snd_hom]; exact hT _

def IsChartFrame (T : Over Z) (i : A.ι) (e : LB.Sec (LPow G (A.pull G.hom) (N : ℤ) T)) : Prop :=
  ∀ (Y : Scheme.{0}) (r : Y ⟶ (T ⊗ G).left) (y : Y) (J), Good (A.pull G.hom) y J →
    sval (L := A.pull G.hom) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) e r y J =
      (gm (r ≫ (snd T G).left ≫ G.hom) y _ (A.g (J (r ≫ (snd T G).left) PUnit.unit) i) ^ N).val

/- English proof (translation)
Establish `le : ∀ j : Fin 1 → PUnit → A.ι, LB.wchart (A.pull G.hom) (fun _ : Fin 1 => (snd T G).left) j ≤ ((snd T G).left ≫ G.hom) ⁻¹ᵁ (A.U (j 0 PUnit.unit) ⊓ A.U i)` using `fun j y hy => ⟨mem_pull (L := A) (F := G.hom) (x := (snd T G).left y) |>.1 (Set.mem_iInter.1 hy 0), mem_chart G A hT (𝟙 _) y⟩`. Establish `v : ∀ (j : Fin 1 → PUnit → A.ι) (Y : Scheme.{0}) (r : Y ⟶ (T ⊗ G).left) (y : Y), r y ∈ LB.wchart (A.pull G.hom) (fun _ : Fin 1 => (snd T G).left) j → gs r y _ (res (le j) (pullU _ _ (A.g (j 0 PUnit.unit) i)) ^ N).val = (gm (r ≫ (snd T G).left ≫ G.hom) y _ (A.g (j 0 PUnit.unit) i) …` using `fun j Y r y hy => by`. Rewrite using `[gs_unit r y _ hy, map_pow, gm_res r y _ hy, gm_pull r ((snd T G).left ≫ G.hom) y (A.U (j 0 PUnit.unit) ⊓ A.U i) (le j hy)]`. Use `⟨⟨fun j => (res (le j) (pullU _ _ (A.g (j 0 PUnit.unit) i)) ^ N).val, fun j j' => fn_ext fun y hy => ?_⟩, fun Y r y J hJ => v _ Y r y (hJ.mem (fun _ : Fin 1 => (snd T G).left) r)⟩` and prove the remaining obligations. Use `((gs_res (𝟙 _) y _ hy _).trans (v j _ _ y hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 _) y _ hy _).trans (congrArg Units.val (gm_linComb (A.pull G.hom) _ _ (𝟙 _) y j j' hy.1 hy.2))) ((gs_res (𝟙 _) y _ hy _).trans (v j' _ _ y hy.2)))) …` and prove the remaining obligations.

Establish `h1` using `Set.mem_iInter.1 hy.1 (0 : Fin 1)`. Establish `h2` using `Set.mem_iInter.1 hy.2 (0 : Fin 1)`. Rewrite using `[Fin.prod_univ_one, gm_pull_g A G.hom (𝟙 _ ≫ (snd T G).left) y (j 0) (j' 0) h1 h2, zpow_natCast, ← Units.val_mul, ← mul_pow, Category.assoc, gm_cocycle hA (𝟙 _ ≫ (snd T G).left ≫ G.hom) y (i := j 0 PUnit.unit) (j := j' 0 PUnit.unit) ((mem_pull (L := A) (F := G.hom) (x := (snd T G …`.
-/
theorem exists_chartFrame (hA : A.IsLB) (T : Over Z) (i : A.ι) (hT : ∀ t, T.hom t ∈ A.U i) :
    ∃ e, IsChartFrame G A N T i e := by
  have le : ∀ j : Fin 1 → PUnit → A.ι, LB.wchart (A.pull G.hom) (fun _ : Fin 1 => (snd T G).left) j ≤
      ((snd T G).left ≫ G.hom) ⁻¹ᵁ (A.U (j 0 PUnit.unit) ⊓ A.U i) := fun j y hy =>
    ⟨mem_pull (L := A) (F := G.hom) (x := (snd T G).left y) |>.1 (Set.mem_iInter.1 hy 0), mem_chart G A hT (𝟙 _) y⟩
  have v : ∀ (j : Fin 1 → PUnit → A.ι) (Y : Scheme.{0}) (r : Y ⟶ (T ⊗ G).left) (y : Y),
      r y ∈ LB.wchart (A.pull G.hom) (fun _ : Fin 1 => (snd T G).left) j →
      gs r y _ (res (le j) (pullU _ _ (A.g (j 0 PUnit.unit) i)) ^ N).val =
        (gm (r ≫ (snd T G).left ≫ G.hom) y _ (A.g (j 0 PUnit.unit) i) ^ N).val := fun j Y r y hy => by
    rw [gs_unit r y _ hy, map_pow, gm_res r y _ hy,
      gm_pull r ((snd T G).left ≫ G.hom) y (A.U (j 0 PUnit.unit) ⊓ A.U i) (le j hy)]
  refine ⟨⟨fun j => (res (le j) (pullU _ _ (A.g (j 0 PUnit.unit) i)) ^ N).val, fun j j' => fn_ext fun y hy => ?_⟩,
    fun Y r y J hJ => v _ Y r y (hJ.mem (fun _ : Fin 1 => (snd T G).left) r)⟩
  refine ((gs_res (𝟙 _) y _ hy _).trans (v j _ _ y hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 _) y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 _) y _ hy _).trans
      (congrArg Units.val (gm_linComb (A.pull G.hom) _ _ (𝟙 _) y j j' hy.1 hy.2)))
      ((gs_res (𝟙 _) y _ hy _).trans (v j' _ _ y hy.2)))).symm)
  have h1 := Set.mem_iInter.1 hy.1 (0 : Fin 1)
  have h2 := Set.mem_iInter.1 hy.2 (0 : Fin 1)
  rw [Fin.prod_univ_one, gm_pull_g A G.hom (𝟙 _ ≫ (snd T G).left) y (j 0) (j' 0) h1 h2, zpow_natCast, ← Units.val_mul,
    ← mul_pow, Category.assoc, gm_cocycle hA (𝟙 _ ≫ (snd T G).left ≫ G.hom) y (i := j 0 PUnit.unit) (j := j' 0 PUnit.unit)
      ((mem_pull (L := A) (F := G.hom) (x := (snd T G).left y)).1 h1)
      ((mem_pull (L := A) (F := G.hom) (x := (snd T G).left y)).1 h2) (mem_chart G A hT (𝟙 _) y)]

/- English proof (translation)
Rewrite using `[Category.id_comp, ← Over.comp_left, whiskerRight_snd]`.
-/
theorem whisker_snd {T T' : Over Z} (h : T' ⟶ T) : (h ▷ G).left ≫ (snd T G).left = 𝟙 _ ≫ (snd T' G).left := by
  rw [Category.id_comp, ← Over.comp_left, whiskerRight_snd]

/- English proof (translation)
Rewrite using `[he _ _ y J hJ, ← Category.assoc, whisker_snd, Category.assoc]`.
-/
theorem IsChartFrame.pull {T T' : Over Z} (h : T' ⟶ T) {i : A.ι} {e} (he : IsChartFrame G A N T i e) (y : (T' ⊗ G).left) (J)
    (hJ : Good (A.pull G.hom) y J) :
    sval (L := A.pull G.hom) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) e (h ▷ G).left y J =
      (gm (𝟙 _ ≫ (snd T' G).left ≫ G.hom) y _ (A.g (J (𝟙 _ ≫ (snd T' G).left) PUnit.unit) i) ^ N).val := by
  rw [he _ _ y J hJ, ← Category.assoc, whisker_snd, Category.assoc]

/- English proof (translation)
Introduce `y J hJ`. Rewrite using `[Fin.sum_univ_one, hb, he.pull G A N h y J hJ, he' _ _ y J hJ, hc, ← Units.val_mul, ← mul_pow, mul_comm, gm_cocycle hA (𝟙 _ ≫ (snd T' G).left ≫ G.hom) y (i := J (𝟙 _ ≫ (snd T' G).left) PUnit.unit) ((mem_pull (L := A) (F := G.hom)).1 (hJ (𝟙 _ ≫ (snd T' G).left))) (mem_chart G A hj …`.
-/
theorem lin_of (hA : A.IsLB) {T T' : Over Z} (h : T' ⟶ T) {i j : A.ι} (hi : ∀ t, T'.hom t ∈ A.U i) (hj : ∀ t, T'.hom t ∈ A.U j)
    {e e'} (he : IsChartFrame G A N T j e) (he' : IsChartFrame G A N T' i e') (b : Fin 1 → _) (hb : b 0 = e)
    (c : Fin 1 → Γ(T'.left, ⊤))
    (hc : ∀ y, gs (fst T' G).left y ⊤ (c 0) = (gm (𝟙 _ ≫ (snd T' G).left ≫ G.hom) y _ (A.g j i) ^ N).val) :
    Lin G (A.pull G.hom) N h b c e' := by
  intro y J hJ
  rw [Fin.sum_univ_one, hb, he.pull G A N h y J hJ, he' _ _ y J hJ, hc, ← Units.val_mul, ← mul_pow, mul_comm,
    gm_cocycle hA (𝟙 _ ≫ (snd T' G).left ≫ G.hom) y (i := J (𝟙 _ ≫ (snd T' G).left) PUnit.unit)
      ((mem_pull (L := A) (F := G.hom)).1 (hJ (𝟙 _ ≫ (snd T' G).left))) (mem_chart G A hj (𝟙 _) y) (mem_chart G A hi (𝟙 _) y)]

/- English proof (translation)
Introduce `s`. Establish `hL : (A.pull G.hom).IsLB` using `LB.isLB_linComb hA _ _`. Establish `le : (⊤ : (T' ⊗ G).left.Opens) ≤ LB.wchart (A.pull G.hom) (fun _ : Fin 1 => (snd T' G).left) (fun _ _ => i)` using `fun y _ => Set.mem_iInter.2 fun _ => mem_pull.2 (mem_chart G A hi (𝟙 _) y)`. Establish `gv : ∀ (c : Γ(T'.left, ⊤)) (y : (T' ⊗ G).left), gs (fst T' G).left y ⊤ c = gs (𝟙 _) y ⊤ ((fst T' G).left.appTop.hom c)` using `fun c y => ((gs_pull (𝟙 _) (fst T' G).left y ⊤ trivial c).trans (by rw [Category.id_comp])).symm`. Take `⟨c, hc⟩` from `hb.2 (((T' ⊗ G).left.presheaf.map (homOfLE le).op).hom (s.f (fun _ _ => i)))`.

Establish `H : Lin G (A.pull G.hom) N h (fun _ : Fin 1 => e) (fun _ => c) s`. Introduce `y J hJ`. Rewrite using `[Fin.sum_univ_one, he.pull G A N h y J hJ, gv, hc, mul_comm]`. Use `(sec_trans s (𝟙 _) y (hJ.mem (fun _ : Fin 1 => (snd T' G).left) (𝟙 _)) (le (show y ∈ (⊤ : (T' ⊗ G).left.Opens) from trivial))).trans (congrArg₂ (· * ·) (congrArg Units.val ?_) (gs_res (𝟙 _) y le trivial _).symm)` and prove the remaining obligations. Unfold `ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF`.

Rewrite using `[Fin.prod_univ_one, gm_pull_g A G.hom (𝟙 _ ≫ (snd T' G).left) y _ _ (hJ _) (mem_pull.2 (mem_chart G A hi (𝟙 _) y)), zpow_natCast, Category.assoc]`. Use `⟨fun _ => c, H, fun c' H' => funext fun k => ?_⟩` and prove the remaining obligations. Take `rfl : k = 0` from `Subsingleton.elim _ _`. Use `hb.1 (fn_ext fun y _ => ?_)` and prove the remaining obligations. Use `choose J hJ using fun χ : (T' ⊗ G).left ⟶ G.left => exists_chart hL (χ y)`.

Establish `e1` using `(H' y J hJ).symm.trans (H y J hJ)`. Rewrite `e1` using `[Fin.sum_univ_one, Fin.sum_univ_one, he.pull G A N h y J hJ, Units.mul_left_inj, gv, gv]`. Conclude with `e1`.
-/
theorem basisAlong_of (hA : A.IsLB) {T T' : Over Z} (h : T' ⟶ T) {i : A.ι} (hi : ∀ t, T'.hom t ∈ A.U i)
    (hb : Function.Bijective (fst T' G).left.appTop.hom) {e} (he : IsChartFrame G A N T i e) :
    BasisAlong G (A.pull G.hom) N h (fun _ : Fin 1 => e) := by
  intro s
  have hL : (A.pull G.hom).IsLB := LB.isLB_linComb hA _ _
  have le : (⊤ : (T' ⊗ G).left.Opens) ≤
      LB.wchart (A.pull G.hom) (fun _ : Fin 1 => (snd T' G).left) (fun _ _ => i) := fun y _ =>
    Set.mem_iInter.2 fun _ => mem_pull.2 (mem_chart G A hi (𝟙 _) y)
  have gv : ∀ (c : Γ(T'.left, ⊤)) (y : (T' ⊗ G).left),
      gs (fst T' G).left y ⊤ c = gs (𝟙 _) y ⊤ ((fst T' G).left.appTop.hom c) := fun c y =>
    ((gs_pull (𝟙 _) (fst T' G).left y ⊤ trivial c).trans (by rw [Category.id_comp])).symm
  obtain ⟨c, hc⟩ := hb.2 (((T' ⊗ G).left.presheaf.map (homOfLE le).op).hom (s.f (fun _ _ => i)))
  have H : Lin G (A.pull G.hom) N h (fun _ : Fin 1 => e) (fun _ => c) s := by
    intro y J hJ
    rw [Fin.sum_univ_one, he.pull G A N h y J hJ, gv, hc, mul_comm]
    refine (sec_trans s (𝟙 _) y (hJ.mem (fun _ : Fin 1 => (snd T' G).left) (𝟙 _)) (le (show y ∈ (⊤ : (T' ⊗ G).left.Opens) from trivial))).trans
      (congrArg₂ (· * ·) (congrArg Units.val ?_) (gs_res (𝟙 _) y le trivial _).symm)
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.trF
    rw [Fin.prod_univ_one, gm_pull_g A G.hom (𝟙 _ ≫ (snd T' G).left) y _ _ (hJ _)
      (mem_pull.2 (mem_chart G A hi (𝟙 _) y)), zpow_natCast, Category.assoc]
  refine ⟨fun _ => c, H, fun c' H' => funext fun k => ?_⟩
  obtain rfl : k = 0 := Subsingleton.elim _ _
  refine hb.1 (fn_ext fun y _ => ?_)
  choose J hJ using fun χ : (T' ⊗ G).left ⟶ G.left => exists_chart hL (χ y)
  have e1 := (H' y J hJ).symm.trans (H y J hJ)
  rw [Fin.sum_univ_one, Fin.sum_univ_one, he.pull G A N h y J hJ, Units.mul_left_inj, gv, gv] at e1
  exact e1

/- English proof (translation)
Establish `hm : ∀ t : (A.U i ⊓ A.U j).toScheme, (A.U i ⊓ A.U j).ι t ∈ A.U i ⊓ A.U j` using `fun t => t.2`. Rewrite using `[Category.id_comp, snd_hom, ← gs_unit _ y _ (hm _), ← gs_pull _ (Over.mk (A.U i ⊓ A.U j).ι).hom y _ (hm _)]`. Use `Eq.trans ?_ (gs_res (fst (Over.mk (A.U i ⊓ A.U j).ι) G).left y (show ⊤ ≤ (A.U i ⊓ A.U j).ι ⁻¹ᵁ (A.U i ⊓ A.U j) from fun t _ => hm t) trivial _)` and prove the remaining obligations. Use `congrArg (gs _ y ⊤) ?_` and prove the remaining obligations. Establish `e : (A.U i ⊓ A.U j).topIso.inv = (A.U i ⊓ A.U j).ι.appLE (A.U i ⊓ A.U j) ⊤ (fun t _ => hm t)`.

Conclude with `(Scheme.Opens.ι_appLE (A.U i ⊓ A.U j) (A.U i ⊓ A.U j) ⊤ (fun t _ => hm t)).symm`. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem gs_unit_overlap (i j : A.ι) (a : Γ(Z, A.U i ⊓ A.U j)ˣ) (y : ((Over.mk (A.U i ⊓ A.U j).ι) ⊗ G).left) :
    gs (fst (Over.mk (A.U i ⊓ A.U j).ι) G).left y ⊤ ((A.U i ⊓ A.U j).topIso.inv.hom a.val) =
      (gm (𝟙 _ ≫ (snd (Over.mk (A.U i ⊓ A.U j).ι) G).left ≫ G.hom) y _ a).val := by
  have hm : ∀ t : (A.U i ⊓ A.U j).toScheme, (A.U i ⊓ A.U j).ι t ∈ A.U i ⊓ A.U j := fun t => t.2
  rw [Category.id_comp, snd_hom, ← gs_unit _ y _ (hm _), ← gs_pull _ (Over.mk (A.U i ⊓ A.U j).ι).hom y _ (hm _)]
  refine Eq.trans ?_ (gs_res (fst (Over.mk (A.U i ⊓ A.U j).ι) G).left y
    (show ⊤ ≤ (A.U i ⊓ A.U j).ι ⁻¹ᵁ (A.U i ⊓ A.U j) from fun t _ => hm t) trivial _)
  refine congrArg (gs _ y ⊤) ?_
  have e : (A.U i ⊓ A.U j).topIso.inv = (A.U i ⊓ A.U j).ι.appLE (A.U i ⊓ A.U j) ⊤ (fun t _ => hm t) := by
    exact (Scheme.Opens.ι_appLE (A.U i ⊓ A.U j) (A.U i ⊓ A.U j) ⊤ (fun t _ => hm t)).symm
  rw [e]; rfl

/- English proof (translation)
Establish `hT : ∀ (i : A.ι) (t : (Over.mk (A.U i).ι).left), (Over.mk (A.U i).ι).hom t ∈ A.U i` using `fun i t => t.2`. Use `choose th hth using fun i => exists_chartFrame G A 1 hA.isLB _ i (hT i)`. Use `choose b hb using fun i => exists_chartFrame G A N hA.isLB _ i (hT i)`. Use `⟨⟨A, hA.isLB, fun z => ?_, 1, th, fun i _ => b i, -1 - N, 1, fun i j => ?_, fun i V _ _ _ hV χ _ => ?_⟩, rfl, rfl, rfl, rfl⟩` and prove the remaining obligations. Take `⟨n, hn, s, hs⟩` from `hA.exists_affine z`.

Take `⟨s', e, -⟩` from `exists_sec_oneTerm A (K' := Fin 1) (e' := (n : ℤ)) rfl s`. Conclude with `⟨n, s', hn, by rw [← e] at hs; exact hs⟩`. Establish `hi : ∀ t : (Over.mk (A.U i ⊓ A.U j).ι).left, (Over.mk (A.U i ⊓ A.U j).ι).hom t ∈ A.U i` using `fun t => t.2.1`. Establish `hj : ∀ t : (Over.mk (A.U i ⊓ A.U j).ι).left, (Over.mk (A.U i ⊓ A.U j).ι).hom t ∈ A.U j` using `fun t => t.2.2`. Set `u : Γ((A.U i ⊓ A.U j).toScheme, ⊤)ˣ` to `Units.map (A.U i ⊓ A.U j).topIso.inv.hom.toMonoidHom (A.g i j)⁻¹`.

Establish `hu : ∀ (k : ℕ) y, gs (fst (Over.mk (A.U i ⊓ A.U j).ι) G).left y ⊤ (u ^ k).val = (gm (𝟙 _ ≫ (snd (Over.mk (A.U i ⊓ A.U j).ι) G).left ≫ G.hom) y _ (A.g j i) ^ k).val` using `fun k y => by`. Establish `e : (u ^ k).val = (A.U i ⊓ A.U j).topIso.inv.hom ((A.g i j)⁻¹ ^ k).val`. Simplify using `only [u, ← map_pow]`. Both sides reduce to the same expression. Establish `m₁` using `mem_chart G A hi (𝟙 _) y`.

Establish `m₂` using `mem_chart G A hj (𝟙 _) y`. Rewrite using `[e, gs_unit_overlap, map_pow, map_inv]`. Use `congr 2`. Conclude with `(eq_inv_of_mul_eq_one_right ((gm_cocycle hA.isLB _ y m₁ m₂ m₁).trans (gm_self hA.isLB _ y m₁))).symm`. Establish `h1 : ∀ (k : ℕ) y, gs (fst (Over.mk (A.U i ⊓ A.U j).ι) G).left y ⊤ 1 = (gm (𝟙 _ ≫ (snd (Over.mk (A.U i ⊓ A.U j).ι) G).left ≫ G.hom) y _ (A.g i i) ^ k).val` using `fun k y => by`.

Rewrite using `[gm_self hA.isLB _ y (mem_chart G A hi (𝟙 _) y), one_pow, gs_eq _ y ⊤ trivial, map_one, map_one]`. Both sides reduce to the same expression. Take `⟨t, ht⟩` from `exists_chartFrame G A 1 hA.isLB _ i hi`. Take `⟨t', ht'⟩` from `exists_chartFrame G A N hA.isLB _ i hi`. Use `⟨u, Matrix.GeneralLinearGroup.scalar (Fin 1) (u ^ N), ⟨t, lin_of G A 1 hA.isLB _ hi hi (hth i) ht _ rfl _ (h1 1), lin_of G A 1 hA.isLB _ hi hj (hth j) ht _ rfl _ (fun y => by simpa only [pow_one] using hu 1 y)⟩, fun k => ⟨t', lin_of G A N hA.isLB _ hi hi (hb i) ht' _ rfl _ (h1 N) …` and prove the remaining obligations.

Take `rfl : k = 0` from `Subsingleton.elim _ _`. Conclude with `hu N y`. Rewrite using `[Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_one, zpow_one, ← zpow_natCast, ← zpow_add, sub_add_cancel, zpow_neg_one]`. Simplify using `only [u, map_inv, inv_inv]`. Both sides reduce to the same expression.

Establish `hi : ∀ t : (Over.mk (χ ≫ (A.U i).ι)).left, (Over.mk (χ ≫ (A.U i).ι)).hom t ∈ A.U i` using `fun t => (χ t).2`. Use `hV.1` as an intermediate fact. Establish `hbij : Function.Bijective (fst (Over.mk (χ ≫ (A.U i).ι)) G).left.appTop.hom`. Establish `H : IsPullback (snd (Over.mk (χ ≫ (A.U i).ι)) G).left (fst (Over.mk (χ ≫ (A.U i).ι)) G).left G.hom (χ ≫ (A.U i).ι)` using `(IsPullback.of_hasPullback (χ ≫ (A.U i).ι) G.hom).flip`. Establish `: IsProper (fst (Over.mk (χ ≫ (A.U i).ι)) G).left` using `MorphismProperty.of_isPullback H ‹_›`.

Establish `: Flat (fst (Over.mk (χ ≫ (A.U i).ι)) G).left` using `MorphismProperty.of_isPullback H ‹_›`. Establish `: GeometricallyIntegral (fst (Over.mk (χ ≫ (A.U i).ι)) G).left` using `MorphismProperty.of_isPullback H ‹_›`. Establish `: IsAffine (Over.mk (χ ≫ (A.U i).ι)).left` using `inferInstanceAs (IsAffine (Sp V))`. Establish `: IsLocallyNoetherian (Over.mk (χ ≫ (A.U i).ι)).left` using `inferInstanceAs (IsLocallyNoetherian (Sp V))`. Use `ProperFunctions.isIso_appTop_of_isAffine (fst (Over.mk (χ ≫ (A.U i).ι)) G).left` as an intermediate fact.

Conclude with `ConcreteCategory.bijective_of_isIso _`. Conclude with `⟨basisAlong_of G A 1 hA.isLB _ hi hbij (hth i), basisAlong_of G A N hA.isLB _ hi hbij (hb i)⟩`.
-/
theorem exists_ampFrames [IsProper G.hom] [Flat G.hom] [GeometricallyIntegral G.hom] (hA : IsAmpleLB A) :
    ∃ F : AmpFrames G (A.pull G.hom) N, F.A = A ∧ F.n = 1 ∧ F.r = -1 - N ∧ F.s = 1 := by
  have hT : ∀ (i : A.ι) (t : (Over.mk (A.U i).ι).left), (Over.mk (A.U i).ι).hom t ∈ A.U i := fun i t => t.2
  choose th hth using fun i => exists_chartFrame G A 1 hA.isLB _ i (hT i)
  choose b hb using fun i => exists_chartFrame G A N hA.isLB _ i (hT i)
  refine ⟨⟨A, hA.isLB, fun z => ?_, 1, th, fun i _ => b i, -1 - N, 1, fun i j => ?_, fun i V _ _ _ hV χ _ => ?_⟩,
    rfl, rfl, rfl, rfl⟩
  · obtain ⟨n, hn, s, hs⟩ := hA.exists_affine z
    obtain ⟨s', e, -⟩ := exists_sec_oneTerm A (K' := Fin 1) (e' := (n : ℤ)) rfl s
    exact ⟨n, s', hn, by rw [← e] at hs; exact hs⟩
  · have hi : ∀ t : (Over.mk (A.U i ⊓ A.U j).ι).left, (Over.mk (A.U i ⊓ A.U j).ι).hom t ∈ A.U i := fun t => t.2.1
    have hj : ∀ t : (Over.mk (A.U i ⊓ A.U j).ι).left, (Over.mk (A.U i ⊓ A.U j).ι).hom t ∈ A.U j := fun t => t.2.2
    let u : Γ((A.U i ⊓ A.U j).toScheme, ⊤)ˣ := Units.map (A.U i ⊓ A.U j).topIso.inv.hom.toMonoidHom (A.g i j)⁻¹
    have hu : ∀ (k : ℕ) y, gs (fst (Over.mk (A.U i ⊓ A.U j).ι) G).left y ⊤ (u ^ k).val =
        (gm (𝟙 _ ≫ (snd (Over.mk (A.U i ⊓ A.U j).ι) G).left ≫ G.hom) y _ (A.g j i) ^ k).val := fun k y => by
      have e : (u ^ k).val = (A.U i ⊓ A.U j).topIso.inv.hom ((A.g i j)⁻¹ ^ k).val := by
        simp only [u, ← map_pow]; rfl
      have m₁ := mem_chart G A hi (𝟙 _) y
      have m₂ := mem_chart G A hj (𝟙 _) y
      rw [e, gs_unit_overlap, map_pow, map_inv]
      congr 2
      exact (eq_inv_of_mul_eq_one_right ((gm_cocycle hA.isLB _ y m₁ m₂ m₁).trans (gm_self hA.isLB _ y m₁))).symm
    have h1 : ∀ (k : ℕ) y, gs (fst (Over.mk (A.U i ⊓ A.U j).ι) G).left y ⊤ 1 =
        (gm (𝟙 _ ≫ (snd (Over.mk (A.U i ⊓ A.U j).ι) G).left ≫ G.hom) y _ (A.g i i) ^ k).val := fun k y => by
      rw [gm_self hA.isLB _ y (mem_chart G A hi (𝟙 _) y), one_pow, gs_eq _ y ⊤ trivial, map_one, map_one]; rfl
    obtain ⟨t, ht⟩ := exists_chartFrame G A 1 hA.isLB _ i hi
    obtain ⟨t', ht'⟩ := exists_chartFrame G A N hA.isLB _ i hi
    refine ⟨u, Matrix.GeneralLinearGroup.scalar (Fin 1) (u ^ N),
      ⟨t, lin_of G A 1 hA.isLB _ hi hi (hth i) ht _ rfl _ (h1 1),
        lin_of G A 1 hA.isLB _ hi hj (hth j) ht _ rfl _ (fun y => by simpa only [pow_one] using hu 1 y)⟩,
      fun k => ⟨t', lin_of G A N hA.isLB _ hi hi (hb i) ht' _ rfl _ (h1 N),
        lin_of G A N hA.isLB _ hi hj (hb j) ht' _ rfl _ (fun y => ?_)⟩, ?_⟩
    · obtain rfl : k = 0 := Subsingleton.elim _ _
      exact hu N y
    · rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_one, zpow_one, ← zpow_natCast, ← zpow_add,
        sub_add_cancel, zpow_neg_one]
      simp only [u, map_inv, inv_inv]; rfl
  · have hi : ∀ t : (Over.mk (χ ≫ (A.U i).ι)).left, (Over.mk (χ ≫ (A.U i).ι)).hom t ∈ A.U i := fun t => (χ t).2
    have := hV.1
    have hbij : Function.Bijective (fst (Over.mk (χ ≫ (A.U i).ι)) G).left.appTop.hom := by
      have H : IsPullback (snd (Over.mk (χ ≫ (A.U i).ι)) G).left (fst (Over.mk (χ ≫ (A.U i).ι)) G).left G.hom
          (χ ≫ (A.U i).ι) := (IsPullback.of_hasPullback (χ ≫ (A.U i).ι) G.hom).flip
      have : IsProper (fst (Over.mk (χ ≫ (A.U i).ι)) G).left := MorphismProperty.of_isPullback H ‹_›
      have : Flat (fst (Over.mk (χ ≫ (A.U i).ι)) G).left := MorphismProperty.of_isPullback H ‹_›
      have : GeometricallyIntegral (fst (Over.mk (χ ≫ (A.U i).ι)) G).left := MorphismProperty.of_isPullback H ‹_›
      have : IsAffine (Over.mk (χ ≫ (A.U i).ι)).left := inferInstanceAs (IsAffine (Sp V))
      have : IsLocallyNoetherian (Over.mk (χ ≫ (A.U i).ι)).left := inferInstanceAs (IsLocallyNoetherian (Sp V))
      have := ProperFunctions.isIso_appTop_of_isAffine (fst (Over.mk (χ ≫ (A.U i).ι)) G).left
      exact ConcreteCategory.bijective_of_isIso _
    exact ⟨basisAlong_of G A 1 hA.isLB _ hi hbij (hth i), basisAlong_of G A N hA.isLB _ hi hbij (hb i)⟩

/- English proof (translation)
The claim follows from `Set.eq_univ_of_forall fun _ _ _ _ _ _ => inferInstance`.
-/
theorem abLocus_eq_univ [IsProper G.hom] : abLocus G = Set.univ :=
  Set.eq_univ_of_forall fun _ _ _ _ _ _ => inferInstance

/- English proof (translation)
Assemble the required witnesses or components as `⟨inferInstance, inferInstance, inferInstance⟩`.
-/
theorem cDvr_padicInt (p : ℕ) [Fact p.Prime] : CDvr ℤ_[p] := ⟨inferInstance, inferInstance, inferInstance⟩

def constFamily (C : _root_.WeierstrassCurve ℤ) : Over (PSpace ℤ 1) :=
  Over.mk (pullback.snd (WeierstrassCurve.toSpec C) (PSpace.str ℤ 1))

/- English proof (translation)
Take `⟨h₁, h₂, -, h₃, -⟩` from `WeierstrassCurve.proper_flat_geometricallyIntegral_smooth C`. Establish `: IsProper (constFamily C).hom` using `inferInstanceAs (IsProper (pullback.snd _ _))`. Establish `: Flat (constFamily C).hom` using `inferInstanceAs (Flat (pullback.snd _ _))`. Establish `: GeometricallyIntegral (constFamily C).hom` using `inferInstanceAs (GeometricallyIntegral (pullback.snd _ _))`. Take `⟨F, a, b, -⟩` from `exists_ampFrames (constFamily C) _ N (isAmple_projective_O_one ℤ 1)`.

Conclude with `⟨⟨F, a, b⟩, abLocus_eq_univ _⟩`.
-/
theorem ampFrames_constFamily (C : _root_.WeierstrassCurve ℤ) :
    (∃ F : AmpFrames (constFamily C) ((ProjSpace.O1 ℤ 1).pull (constFamily C).hom) N, F.A = ProjSpace.O1 ℤ 1 ∧ F.n = 1) ∧
      abLocus (constFamily C) = Set.univ := by
  obtain ⟨h₁, h₂, -, h₃, -⟩ := WeierstrassCurve.proper_flat_geometricallyIntegral_smooth C
  have : IsProper (constFamily C).hom := inferInstanceAs (IsProper (pullback.snd _ _))
  have : Flat (constFamily C).hom := inferInstanceAs (Flat (pullback.snd _ _))
  have : GeometricallyIntegral (constFamily C).hom := inferInstanceAs (GeometricallyIntegral (pullback.snd _ _))
  obtain ⟨F, a, b, -⟩ := exists_ampFrames (constFamily C) _ N (isAmple_projective_O_one ℤ 1)
  exact ⟨⟨F, a, b⟩, abLocus_eq_univ _⟩

/- English proof (translation)
Establish `H : IsPullback (snd (Over.mk χ) G).left (fst (Over.mk χ) G).left G.hom χ` using `(IsPullback.of_hasPullback χ G.hom).flip`. Establish `: IsProper (fst (Over.mk χ) G).left` using `MorphismProperty.of_isPullback H ‹_›`. Establish `: Flat (fst (Over.mk χ) G).left` using `MorphismProperty.of_isPullback H ‹_›`. Establish `: GeometricallyIntegral (fst (Over.mk χ) G).left` using `MorphismProperty.of_isPullback H ‹_›`. Establish `: IsAffine (Over.mk χ).left` using `inferInstanceAs (IsAffine (Sp V))`.

Establish `: IsLocallyNoetherian (Over.mk χ).left` using `inferInstanceAs (IsLocallyNoetherian (Sp V))`. Use `ProperFunctions.isIso_appTop_of_isAffine (fst (Over.mk χ) G).left` as an intermediate fact. Conclude with `ConcreteCategory.bijective_of_isIso _`.
-/
theorem bijective_fst [IsProper G.hom] [Flat G.hom] [GeometricallyIntegral G.hom] {V : Type} [CommRing V] [IsNoetherianRing V]
    (χ : Sp V ⟶ Z) : Function.Bijective (fst (Over.mk χ) G).left.appTop.hom := by
  have H : IsPullback (snd (Over.mk χ) G).left (fst (Over.mk χ) G).left G.hom χ := (IsPullback.of_hasPullback χ G.hom).flip
  have : IsProper (fst (Over.mk χ) G).left := MorphismProperty.of_isPullback H ‹_›
  have : Flat (fst (Over.mk χ) G).left := MorphismProperty.of_isPullback H ‹_›
  have : GeometricallyIntegral (fst (Over.mk χ) G).left := MorphismProperty.of_isPullback H ‹_›
  have : IsAffine (Over.mk χ).left := inferInstanceAs (IsAffine (Sp V))
  have : IsLocallyNoetherian (Over.mk χ).left := inferInstanceAs (IsLocallyNoetherian (Sp V))
  have := ProperFunctions.isIso_appTop_of_isAffine (fst (Over.mk χ) G).left
  exact ConcreteCategory.bijective_of_isIso _

/- English proof (translation)
Take `⟨e, he⟩` from `exists_chartFrame G A N hA (Over.mk x) i (fun _ => hi _)`. Use `⟨e, he, fun V _ _ _ hV φ gam _ χ h => ?_⟩` and prove the remaining obligations. Use `hV.1` as an intermediate fact. Take `⟨e', he'⟩` from `exists_chartFrame G A N hA (Over.mk χ) i (fun _ => hi _)`. Take `⟨s, hs⟩` from `exists_chartFrame G A N hA (Over.mk (jK V ≫ χ)) i (fun _ => hi _)`.

Establish `h1 : ∀ y, gs (fst (Over.mk (jK V ≫ χ)) G).left y ⊤ 1 = (gm (𝟙 _ ≫ (snd (Over.mk (jK V ≫ χ)) G).left ≫ G.hom) y _ (A.g i i) ^ N).val` using `fun y => by`. Rewrite using `[gm_self hA _ y (hi _), one_pow, gs_eq _ y ⊤ trivial, map_one, map_one]`. Both sides reduce to the same expression. Conclude with `⟨fun _ => e', basisAlong_of G A N hA _ (fun _ => hi _) (bijective_fst G χ) he', fun _ => ⟨s, lin_of G A N hA _ (fun _ => hi _) (fun _ => hi _) he hs _ rfl _ h1, lin_of G A N hA _ (fun _ => hi _) (fun _ => hi _) he' hs _ rfl _ h1⟩⟩`.
-/
theorem exists_isFrame [IsProper G.hom] [Flat G.hom] [GeometricallyIntegral G.hom] (hA : A.IsLB) (i : A.ι)
    (hi : ∀ z, z ∈ A.U i) {R₁ : Type} [CommRing R₁] [IsDomain R₁] (x : Sp (FractionRing R₁) ⟶ Z) :
    ∃ e, IsChartFrame G A N (Over.mk x) i e ∧ IsFrame G (A.pull G.hom) N x (fun _ : Fin 1 => e) := by
  obtain ⟨e, he⟩ := exists_chartFrame G A N hA (Over.mk x) i (fun _ => hi _)
  refine ⟨e, he, fun V _ _ _ hV φ gam _ χ h => ?_⟩
  have := hV.1
  obtain ⟨e', he'⟩ := exists_chartFrame G A N hA (Over.mk χ) i (fun _ => hi _)
  obtain ⟨s, hs⟩ := exists_chartFrame G A N hA (Over.mk (jK V ≫ χ)) i (fun _ => hi _)
  have h1 : ∀ y, gs (fst (Over.mk (jK V ≫ χ)) G).left y ⊤ 1 =
      (gm (𝟙 _ ≫ (snd (Over.mk (jK V ≫ χ)) G).left ≫ G.hom) y _ (A.g i i) ^ N).val := fun y => by
    rw [gm_self hA _ y (hi _), one_pow, gs_eq _ y ⊤ trivial, map_one, map_one]; rfl
  exact ⟨fun _ => e', basisAlong_of G A N hA _ (fun _ => hi _) (bijective_fst G χ) he', fun _ => ⟨s,
    lin_of G A N hA _ (fun _ => hi _) (fun _ => hi _) he hs _ rfl _ h1,
    lin_of G A N hA _ (fun _ => hi _) (fun _ => hi _) he' hs _ rfl _ h1⟩⟩

/- English proof (translation)
Introduce `H`. Establish `hE : IsEmpty (LPow G L (N : ℤ) T').ι` using `⟨fun j => isEmptyElim (j (0 : Fin 1))⟩`. Take `⟨c, -, hc⟩` from `H ⟨fun j => hE.elim j, fun j => hE.elim j⟩`. Establish `v : ∀ c', Lin G L N h b c' ⟨fun j => hE.elim j, fun j => hE.elim j⟩` using `fun c' z J _ => isEmptyElim (J (snd T' G).left)`. Conclude with `zero_ne_one (congrFun ((hc (fun _ => 0) (v _)).trans (hc (fun _ => 1) (v _)).symm) 0)`.
-/
theorem not_basisAlong_of_isEmpty (L : LB G.left) [IsEmpty L.ι] {T T' : Over Z} (h : T' ⟶ T) [Nontrivial Γ(T'.left, ⊤)]
    (b : Fin 1 → LB.Sec (LPow G L (N : ℤ) T)) : ¬ BasisAlong G L N h b := by
  intro H
  have hE : IsEmpty (LPow G L (N : ℤ) T').ι := ⟨fun j => isEmptyElim (j (0 : Fin 1))⟩
  obtain ⟨c, -, hc⟩ := H ⟨fun j => hE.elim j, fun j => hE.elim j⟩
  have v : ∀ c', Lin G L N h b c' ⟨fun j => hE.elim j, fun j => hE.elim j⟩ := fun c' z J _ =>
    isEmptyElim (J (snd T' G).left)
  exact zero_ne_one (congrFun ((hc (fun _ => 0) (v _)).trans (hc (fun _ => 1) (v _)).symm) 0)

/- English proof (translation)
Use `⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance, inferInstance, inferInstance, ?_⟩` and prove the remaining obligations. Use `letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal ℤ_[p])`. Use `infer_instance`.
-/
theorem admissible_padicInt_maximalIdeal (p : ℕ) [Fact p.Prime] : admitted ℤ_[p] (IsLocalRing.maximalIdeal ℤ_[p]) := by
  refine ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance, inferInstance, inferInstance, ?_⟩
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal ℤ_[p])
  infer_instance

/- English proof (translation)
Assemble the required witnesses or components as `⟨.inl ⟨Field.toIsField ℚ, rfl⟩, .inr ⟨inferInstance, PadicInt.irreducible_p, by rw [← PadicInt.maximalIdeal_eq_span_p]; infer_instance⟩⟩`.
-/
theorem arcBase_examples (p : ℕ) [Fact p.Prime] : ArcBase ℚ 1 ∧ ArcBase ℤ_[p] (p : ℤ_[p]) :=
  ⟨.inl ⟨Field.toIsField ℚ, rfl⟩, .inr ⟨inferInstance, PadicInt.irreducible_p, by
    rw [← PadicInt.maximalIdeal_eq_span_p]; infer_instance⟩⟩

end GlobalTheory.LN.Model
end
