import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrimitiveCocycle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIsGenTranslDiffComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DescendedPrincipal

open CommutatorPairing

section Gen

variable {X Y : Scheme.{0}} {N N' : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

/- English proof (translation)
Unfold `trF`. Rewrite using `[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← inv_zpow, ← mul_zpow]`. Conclude with `congrArg (· ^ ε k) (gm_div N' N (r ≫ φ k) z (j k) (j' k) ⟨Set.mem_iInter.1 hj k, Set.mem_iInter.1 hj' k⟩)`.
-/
theorem trF_div {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {j j' : K → N.ι × N'.ι}
    (hj : r z ∈ LB.wchart (LB.div N N') φ j) (hj' : r z ∈ LB.wchart (LB.div N N') φ j') :
    trF (L := LB.div N N') φ ε r z j j' = trF φ ε r z (fun k => (j k).1) (fun k => (j' k).1) *
      (trF φ ε r z (fun k => (j k).2) (fun k => (j' k).2))⁻¹ := by
  unfold trF
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← inv_zpow, ← mul_zpow]
  exact congrArg (· ^ ε k) (gm_div N' N (r ≫ φ k) z (j k) (j' k)
    ⟨Set.mem_iInter.1 hj k, Set.mem_iInter.1 hj' k⟩)

def chartPullDiv (N N' : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    ChartPull (LB.LinComb (LB.div N N') φ ε) (LB.div (LB.LinComb N φ ε) (LB.LinComb N' φ ε)) (𝟙 Y) :=
  have le : ∀ j : K → N.ι × N'.ι, LB.wchart (LB.div N N') φ j ≤
      LB.wchart N φ (fun k => (j k).1) ⊓ LB.wchart N' φ (fun k => (j k).2) := fun j y hy =>
    ⟨Set.mem_iInter.2 fun k => (Set.mem_iInter.1 hy k).1, Set.mem_iInter.2 fun k => (Set.mem_iInter.1 hy k).2⟩
  { idx := fun j => (fun k => (j k).1, fun k => (j k).2)
    le := le
    g := fun y j j' hj hj' => (gm_linComb (LB.div N N') φ ε (𝟙 Y) y j j' hj hj').trans
      ((trF_div (𝟙 Y) y hj hj').trans (Eq.symm
        ((gm_div (LB.LinComb N' φ ε) (LB.LinComb N φ ε) (𝟙 Y) y (fun k => (j k).1, fun k => (j k).2)
          (fun k => (j' k).1, fun k => (j' k).2) ⟨le j hj, le j' hj'⟩).trans
          (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb N φ ε (𝟙 Y) y _ _ (le j hj).1 (le j' hj').1)
            (gm_linComb N' φ ε (𝟙 Y) y _ _ (le j hj).2 (le j' hj').2))))) }

/- English proof (translation)
Set `O : (K → N.ι) → (K → N'.ι) → Y.Opens` to `fun j j' => LB.wchart N φ j ⊓ LB.wchart N' φ j'`. Establish `le : ∀ j j', O j j' ≤ LB.wchart (LB.div N N') φ (fun k => (j k, j' k))` using `fun j j' y hy => Set.mem_iInter.2 fun k => ⟨Set.mem_iInter.1 hy.1 k, Set.mem_iInter.1 hy.2 k⟩`. Set `v : ∀ j j', Γ(Y, O j j')ˣ` to `fun j j' => res (inf_le_right : O j j' ≤ _) (u'.s j') * res (le j j') (q.s fun k => (j k, j' k))`. Establish `germ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j j', r z ∈ O j j' → gm r z (O j j') (v j j') = gm r z (LB.wchart N' φ j') (u'.s j') * gm r z (LB.wchart (LB.div N N') φ fun k => (j k, j' k)) (q.s fun k => (j k, j' k))` using `fun Z r z j j' hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _) (gm_res r z _ hz _))`. Establish `tr : ∀ (y : Y) j j' i i', y ∈ O j j' → y ∈ O i i' → gm (𝟙 Y) y (O j j') (v j j') = trF φ ε (𝟙 Y) y j i * gm (𝟙 Y) y (O i i') (v i i')` using `fun y j j' i i' h h' => by`.

Rewrite using `[germ _ _ y j j' h, germ _ _ y i i' h', gen_trans hu' (𝟙 Y) y h.2 h'.2, gen_trans (L := LB.div N N') hq (𝟙 Y) y (le _ _ h) (le _ _ h'), trF_div (𝟙 Y) y (le _ _ h) (le _ _ h')]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws. Establish `memO : ∀ y : Y, ∃ j', y ∈ LB.wchart N' φ j'` using `fun y => by choose p hp using fun k => exists_chart hN' (φ k y)`.

Conclude with `⟨p, Set.mem_iInter.2 hp⟩`. Establish `glue : ∀ j, ∃ s : Γ(Y, LB.wchart N φ j)ˣ, ∀ j', res (inf_le_left : O j j' ≤ _) s = v j j'` using `fun j => by`. Use `glue_unit _ (O j) (fun p => inf_le_left) (fun y hy => ?_) (v j) fun p p' y hy => ?_` and prove the remaining obligations. Take `⟨p, hp⟩` from `memO y`. Conclude with `Opens.mem_iSup.2 ⟨p, hy, hp⟩`.

Rewrite using `[tr y j p j p' hy.1 hy.2, mul_eq_left.1 (trF_trans hN φ ε (𝟙 Y) y hy.1.1 hy.1.1 hy.1.1), _root_.one_mul]`. Use `choose s hs using glue`. Establish `vals : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j j', r z ∈ O j j' → gm r z (LB.wchart N φ j) (s j) = gm r z (O j j') (v j j')` using `fun Z r z j j' hz => by`. Rewrite using `[← gm_res r z (inf_le_left : O j j' ≤ _) hz, hs]`. Use `⟨⟨s⟩, fun j i => unit_ext fun y hy => ?_, fun Z r z J J' hJ hJ' => ?_⟩` and prove the remaining obligations.

Take `⟨p, hp⟩` from `memO y`. Conclude with `((gm_res _ y _ hy _).trans ((vals _ (𝟙 Y) y j p ⟨hy.1, hp⟩).trans (tr y j p i p ⟨hy.1, hp⟩ ⟨hy.2, hp⟩))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_linComb N φ ε (𝟙 Y) y j i hy.1 hy.2) ((gm_res _ y _ hy _).trans (vals _ (𝟙 Y) y i p ⟨hy.2, hp⟩)))).symm`. Establish `m : r z ∈ O (fun k => J (r ≫ φ k)) (fun k => J' (r ≫ φ k))` using `⟨hJ.mem φ r, hJ'.mem φ r⟩`. Conclude with `(vals Z r z _ _ m).trans (germ Z r z _ _ m)`.
-/
theorem exists_gen_mul_div (hN : N.IsLB) (hN' : N'.IsLB) (u' : LB.Gen (LB.LinComb N' φ ε)) (hu' : u'.IsGen)
    (q : LB.Gen (LB.LinComb (LB.div N N') φ ε)) (hq : q.IsGen) :
    ∃ u : LB.Gen (LB.LinComb N φ ε), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J'), Good N z J →
      Good N' z J' → val u r z J = val u' r z J' * val (L := LB.div N N') q r z (fun χ => (J χ, J' χ)) := by
  let O : (K → N.ι) → (K → N'.ι) → Y.Opens := fun j j' => LB.wchart N φ j ⊓ LB.wchart N' φ j'
  have le : ∀ j j', O j j' ≤ LB.wchart (LB.div N N') φ (fun k => (j k, j' k)) := fun j j' y hy =>
    Set.mem_iInter.2 fun k => ⟨Set.mem_iInter.1 hy.1 k, Set.mem_iInter.1 hy.2 k⟩
  let v : ∀ j j', Γ(Y, O j j')ˣ := fun j j' =>
    res (inf_le_right : O j j' ≤ _) (u'.s j') * res (le j j') (q.s fun k => (j k, j' k))
  have germ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j j', r z ∈ O j j' → gm r z (O j j') (v j j') =
      gm r z (LB.wchart N' φ j') (u'.s j') *
        gm r z (LB.wchart (LB.div N N') φ fun k => (j k, j' k)) (q.s fun k => (j k, j' k)) :=
    fun Z r z j j' hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _) (gm_res r z _ hz _))
  have tr : ∀ (y : Y) j j' i i', y ∈ O j j' → y ∈ O i i' → gm (𝟙 Y) y (O j j') (v j j') =
      trF φ ε (𝟙 Y) y j i * gm (𝟙 Y) y (O i i') (v i i') := fun y j j' i i' h h' => by
    rw [germ _ _ y j j' h, germ _ _ y i i' h', gen_trans hu' (𝟙 Y) y h.2 h'.2,
      gen_trans (L := LB.div N N') hq (𝟙 Y) y (le _ _ h) (le _ _ h'), trF_div (𝟙 Y) y (le _ _ h) (le _ _ h')]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have memO : ∀ y : Y, ∃ j', y ∈ LB.wchart N' φ j' := fun y => by
    choose p hp using fun k => exists_chart hN' (φ k y)
    exact ⟨p, Set.mem_iInter.2 hp⟩
  have glue : ∀ j, ∃ s : Γ(Y, LB.wchart N φ j)ˣ, ∀ j', res (inf_le_left : O j j' ≤ _) s = v j j' := fun j => by
    refine glue_unit _ (O j) (fun p => inf_le_left) (fun y hy => ?_) (v j) fun p p' y hy => ?_
    · obtain ⟨p, hp⟩ := memO y
      exact Opens.mem_iSup.2 ⟨p, hy, hp⟩
    · rw [tr y j p j p' hy.1 hy.2, mul_eq_left.1 (trF_trans hN φ ε (𝟙 Y) y hy.1.1 hy.1.1 hy.1.1), _root_.one_mul]
  choose s hs using glue
  have vals : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j j', r z ∈ O j j' →
      gm r z (LB.wchart N φ j) (s j) = gm r z (O j j') (v j j') := fun Z r z j j' hz => by
    rw [← gm_res r z (inf_le_left : O j j' ≤ _) hz, hs]
  refine ⟨⟨s⟩, fun j i => unit_ext fun y hy => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · obtain ⟨p, hp⟩ := memO y
    exact ((gm_res _ y _ hy _).trans ((vals _ (𝟙 Y) y j p ⟨hy.1, hp⟩).trans (tr y j p i p ⟨hy.1, hp⟩ ⟨hy.2, hp⟩))).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_linComb N φ ε (𝟙 Y) y j i hy.1 hy.2)
        ((gm_res _ y _ hy _).trans (vals _ (𝟙 Y) y i p ⟨hy.2, hp⟩)))).symm
  · have m : r z ∈ O (fun k => J (r ≫ φ k)) (fun k => J' (r ≫ φ k)) := ⟨hJ.mem φ r, hJ'.mem φ r⟩
    exact (vals Z r z _ _ m).trans (germ Z r z _ _ m)

/- English proof (translation)
Establish `le : ∀ i, M.U i ≤ M.U i ⊓ M.U i₀` using `fun i y hy => ⟨hy, h y⟩`. Use `⟨⟨fun i => res (le i) (M.g i i₀)⟩, fun i j => unit_ext fun y hy => ?_⟩` and prove the remaining obligations. Conclude with `((gm_res _ y _ hy _).trans (gm_res _ y _ hy.1 _)).trans ((gm_cocycle hM (𝟙 Y) y hy.1 hy.2 (h y)).symm.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))).symm)`.
-/
theorem exists_gen_of_chart {M : LB Y} (hM : M.IsLB) (i₀ : M.ι) (h : ∀ y, y ∈ M.U i₀) :
    ∃ t : LB.Gen M, t.IsGen := by
  have le : ∀ i, M.U i ≤ M.U i ⊓ M.U i₀ := fun i y hy => ⟨hy, h y⟩
  refine ⟨⟨fun i => res (le i) (M.g i i₀)⟩, fun i j => unit_ext fun y hy => ?_⟩
  exact ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.1 _)).trans
    ((gm_cocycle hM (𝟙 Y) y hy.1 hy.2 (h y)).symm.trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) rfl ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))).symm)

end Gen

section Pairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_gen_of_chart (DVR.linComb_isLB Q hQ (K := Fin 2) ![x.left, (1 : T ⟶ A).left] ![-1, 1]) ![i, i₀] (fun p => Set.mem_iInter.2 fun k => by fin_cases k; exacts [hx p, h₀ p])`. Take `⟨u, hu, hv⟩` from `exists_gen hQ (K' := Fin 2) (φ' := ![(snd T A).left, (translPt A x).left]) (ε' := ![1, -1]) (fun U _ h => by`. Use `(DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := Fin 2) (U := U) _ (DVR.prod_neg _ _ (PrimCocycle.prod_lam (fst T A ≫ x) (snd T A) h)) (c' := h (fst T A ≫ x).left ^ (-1 : ℤ) * h (fst T A ≫ (1 : T ⟶ A)).left ^ (1 : ℤ)) (Fin.prod_univ_two _)).trans ?_` and prove the remaining obligations. Rewrite using `[Fin.prod_univ_two, MonObj.comp_one]`. Use `show _ = h (snd T A).left ^ (1 : ℤ) * h ((fst T A ≫ x) * snd T A).left ^ (-1 : ℤ)`.

Simplify using `only [zpow_neg, zpow_one]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Use the proof step `abel)`. Use the proof step `(LB.mulGen Q _ _ _ _ (LB.invGen Q _ _ (LB.pullGen Q _ _ t (lift (fst T A ≫ x) (snd T A)).left)) (LB.pullGen Q _ _ s (fst T A).left))`.

Use the proof step `(DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)) (DVR.pullGen_isGen _ _ _ _ hs _))`. Use `⟨⟨x, u, hu⟩, rfl, fun Z τ z J hJ => ⟨val s τ.left z J, fun a => ?_⟩⟩` and prove the remaining obligations. Use `(hv _ (lift τ a).left z J hJ).trans ?_` and prove the remaining obligations. Rewrite using `[val_mul hJ, val_inv, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd, lift_fst]`. Both sides reduce to the same expression.
-/
theorem exists_theta_of_lam [IsCommMonObj A] {Q : LB A.left} (hQ : Q.IsLB)
    (t : LB.Gen (LB.LinComb Q (PrimCocycle.lamφ A) PrimCocycle.lamε)) (ht : t.IsGen) {T : Over S} (x : T ⟶ A)
    {i i₀ : Q.ι} (hx : ∀ p, x.left p ∈ Q.U i) (h₀ : ∀ p, (1 : T ⟶ A).left p ∈ Q.U i₀) :
    ∃ θ : ThetaGrp A Q 1 T, θ.pt = x ∧ ∀ (Z : Over S) (τ : Z ⟶ T) (z : Z.left) (J), Good Q z J →
      ∃ σ, ∀ a : Z ⟶ A, thetaVal θ τ a z J = (val₂ t z J (τ ≫ x) a)⁻¹ * σ := by
  obtain ⟨s, hs⟩ := exists_gen_of_chart (DVR.linComb_isLB Q hQ (K := Fin 2) ![x.left, (1 : T ⟶ A).left] ![-1, 1])
    ![i, i₀] (fun p => Set.mem_iInter.2 fun k => by fin_cases k; exacts [hx p, h₀ p])
  obtain ⟨u, hu, hv⟩ := exists_gen hQ (K' := Fin 2) (φ' := ![(snd T A).left, (translPt A x).left])
    (ε' := ![1, -1]) (fun U _ h => by
      refine (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := Fin 2) (U := U) _
        (DVR.prod_neg _ _ (PrimCocycle.prod_lam (fst T A ≫ x) (snd T A) h))
        (c' := h (fst T A ≫ x).left ^ (-1 : ℤ) * h (fst T A ≫ (1 : T ⟶ A)).left ^ (1 : ℤ))
        (Fin.prod_univ_two _)).trans ?_
      rw [Fin.prod_univ_two, MonObj.comp_one]
      show _ = h (snd T A).left ^ (1 : ℤ) * h ((fst T A ≫ x) * snd T A).left ^ (-1 : ℤ)
      simp only [zpow_neg, zpow_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen Q _ _ _ _ (LB.invGen Q _ _ (LB.pullGen Q _ _ t (lift (fst T A ≫ x) (snd T A)).left))
      (LB.pullGen Q _ _ s (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _))
      (DVR.pullGen_isGen _ _ _ _ hs _))
  refine ⟨⟨x, u, hu⟩, rfl, fun Z τ z J hJ => ⟨val s τ.left z J, fun a => ?_⟩⟩
  refine (hv _ (lift τ a).left z J hJ).trans ?_
  rw [val_mul hJ, val_inv, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift, lift_fst_assoc,
    lift_snd, lift_fst]
  rfl

/- English proof (translation)
Use `hA.comm` as an intermediate fact. Use `WeilIsogeny.weilIs_of_local hG hA hQ fun p => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `exists_chart hQ (x.left p)`. Take `⟨j, hj⟩` from `exists_chart hQ (y.left p)`. Take `⟨l, hl⟩` from `exists_chart hQ ((1 : T ⟶ A).left p)`.

Set `V : T.left.Opens` to `x.left ⁻¹ᵁ Q.U i ⊓ y.left ⁻¹ᵁ Q.U j ⊓ (1 : T ⟶ A).left ⁻¹ᵁ Q.U l`. Establish `h₀ : ∀ q, (1 : overRes V ⟶ A).left q ∈ Q.U l` using `fun q => by`. Rewrite using `[← MonObj.comp_one (overResι V)]`. Conclude with `q.2.2`. Take `⟨θx, ex, vx⟩` from `exists_theta_of_lam hQ t ht (overResι V ≫ x) (i := i) (fun q => q.2.1.1) h₀`.

Take `⟨θy, ey, vy⟩` from `exists_theta_of_lam hQ t ht (overResι V ≫ y) (i := j) (fun q => q.2.1.2) h₀`. Use `⟨V, ⟨⟨hi, hj⟩, hl⟩, θx, θy, ex, ey, (commIsOf_iff hQ _ _ _).2 fun Z τ a z J hJ => ?_⟩` and prove the remaining obligations. Take `⟨σ, hσ⟩` from `vx Z τ z J hJ`. Take `⟨ρ, hρ⟩` from `vy Z τ z J hJ`. Set `p₀` to `x3 A 0`.

Set `p₁` to `x3 A 1`. Set `p₂` to `x3 A 2`. Set `e : 𝟙_ (Over S) ⟶ G3 A` to `lift 1 (lift 1 1)`. Establish `e₀ : e ≫ p₀ = 1` using `by simp [e, p₀, x3]`. Establish `e₁ : e ≫ p₁ = 1` using `by simp [e, p₁, x3]`.

Establish `e₂ : e ≫ p₂ = 1` using `by simp [e, p₂, x3]`. Establish `r₀ : ∀ x y w : Z ⟶ A, lift x (lift y w) ≫ p₀ = x` using `fun x y w => by simp [p₀, x3]`. Establish `r₁ : ∀ x y w : Z ⟶ A, lift x (lift y w) ≫ p₁ = y` using `fun x y w => by simp [p₁, x3]`. Establish `r₂ : ∀ x y w : Z ⟶ A, lift x (lift y w) ≫ p₂ = w` using `fun x y w => by simp [p₂, x3]`. Establish `key` using `PrimCocycle.val_mul_eq hG hA hQ t ht e p₀ p₂ p₁ (p₀ * p₂) p₁ p₂ p₀ (p₁ * p₂) (fun V _ k => by`.

Rewrite using `[mul_left_comm p₁ p₀ p₂]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Use the proof step `abel) e₀ e₂ e₁ ((MonObj.comp_mul _ _ _).trans (by rw [e₀, e₂, _root_.mul_one])) e₁ e₂ e₀`. Use the proof step `((MonObj.comp_mul _ _ _).trans (by rw [e₁, e₂, _root_.mul_one]))`.

Use the proof step `(lift (τ ≫ overResι V ≫ x) (lift (τ ≫ overResι V ≫ y) a)) hJ`. Rewrite `key` using `[MonObj.comp_mul, MonObj.comp_mul, r₀, r₁, r₂]`. Establish `e' : unitRes V (1 : Γ(T.left, ⊤)ˣ) = 1` using `map_one _`. Rewrite using `[e', map_one, commVal, hσ, hσ, hρ, hρ, ex, ey]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Use `congrArg Additive.ofMul key` as an intermediate fact. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_one] at this ⊢`. Take the linear combination `(norm := abel) -this`.
-/
theorem weilIs_one_of_lam (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {Q : LB A.left} (hQ : Q.IsLB)
    (t : LB.Gen (abelian₂ A Q)) (ht : t.IsGen) {T : Over S} (x y : T ⟶ A) : WeilIs A Q 1 x y 1 := by
  have := hA.comm
  refine WeilIsogeny.weilIs_of_local hG hA hQ fun p => ?_
  obtain ⟨i, hi⟩ := exists_chart hQ (x.left p)
  obtain ⟨j, hj⟩ := exists_chart hQ (y.left p)
  obtain ⟨l, hl⟩ := exists_chart hQ ((1 : T ⟶ A).left p)
  let V : T.left.Opens := x.left ⁻¹ᵁ Q.U i ⊓ y.left ⁻¹ᵁ Q.U j ⊓ (1 : T ⟶ A).left ⁻¹ᵁ Q.U l
  have h₀ : ∀ q, (1 : overRes V ⟶ A).left q ∈ Q.U l := fun q => by
    rw [← MonObj.comp_one (overResι V)]; exact q.2.2
  obtain ⟨θx, ex, vx⟩ := exists_theta_of_lam hQ t ht (overResι V ≫ x) (i := i) (fun q => q.2.1.1) h₀
  obtain ⟨θy, ey, vy⟩ := exists_theta_of_lam hQ t ht (overResι V ≫ y) (i := j) (fun q => q.2.1.2) h₀
  refine ⟨V, ⟨⟨hi, hj⟩, hl⟩, θx, θy, ex, ey, (commIsOf_iff hQ _ _ _).2 fun Z τ a z J hJ => ?_⟩
  obtain ⟨σ, hσ⟩ := vx Z τ z J hJ
  obtain ⟨ρ, hρ⟩ := vy Z τ z J hJ
  let p₀ := x3 A 0
  let p₁ := x3 A 1
  let p₂ := x3 A 2
  let e : 𝟙_ (Over S) ⟶ G3 A := lift 1 (lift 1 1)
  have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
  have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
  have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
  have r₀ : ∀ x y w : Z ⟶ A, lift x (lift y w) ≫ p₀ = x := fun x y w => by simp [p₀, x3]
  have r₁ : ∀ x y w : Z ⟶ A, lift x (lift y w) ≫ p₁ = y := fun x y w => by simp [p₁, x3]
  have r₂ : ∀ x y w : Z ⟶ A, lift x (lift y w) ≫ p₂ = w := fun x y w => by simp [p₂, x3]
  have key := PrimCocycle.val_mul_eq hG hA hQ t ht e p₀ p₂ p₁ (p₀ * p₂) p₁ p₂ p₀ (p₁ * p₂) (fun V _ k => by
      rw [mul_left_comm p₁ p₀ p₂]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) e₀ e₂ e₁ ((MonObj.comp_mul _ _ _).trans (by rw [e₀, e₂, _root_.mul_one])) e₁ e₂ e₀
      ((MonObj.comp_mul _ _ _).trans (by rw [e₁, e₂, _root_.mul_one]))
      (lift (τ ≫ overResι V ≫ x) (lift (τ ≫ overResι V ≫ y) a)) hJ
  rw [MonObj.comp_mul, MonObj.comp_mul, r₀, r₁, r₂] at key
  have e' : unitRes V (1 : Γ(T.left, ⊤)ˣ) = 1 := map_one _
  rw [e', map_one, commVal, hσ, hσ, hρ, hρ, ex, ey]
  apply Additive.ofMul.injective
  have := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at this ⊢
  linear_combination (norm := abel) -this

/- English proof (translation)
Take `⟨x', u', hu'⟩` from `θ'`. Take `⟨x'', q, hq⟩` from `η'`. Take `rfl : x' = x` from `h`. Take `rfl : x'' = x'` from `h'`. Take `⟨u, hu, hv⟩` from `exists_gen_mul_div (K := Fin 2) (φ := ![(snd T A).left, (translPt A x'').left]) (ε := ![k, -k]) hN hN' u' hu' q hq`.

Conclude with `⟨⟨x'', u, hu⟩, rfl, fun Z τ a z J J' hJ hJ' => hv _ _ z J J' hJ hJ'⟩`.
-/
theorem exists_theta_mul_div {N N' : LB A.left} (hN : N.IsLB) (hN' : N'.IsLB) {k : ℤ} {T : Over S} (x : T ⟶ A)
    (θ' : ThetaGrp A N' k T) (η' : ThetaGrp A (LB.div N N') k T) (h : θ'.pt = x) (h' : η'.pt = x) :
    ∃ θ : ThetaGrp A N k T, θ.pt = x ∧ ∀ (Z : Over S) (τ : Z ⟶ T) (a : Z ⟶ A) (z : Z.left) (J J'), Good N z J →
      Good N' z J' → thetaVal θ τ a z J = thetaVal θ' τ a z J' * thetaVal η' τ a z (fun χ => (J χ, J' χ)) := by
  obtain ⟨x', u', hu'⟩ := θ'
  obtain ⟨x'', q, hq⟩ := η'
  obtain rfl : x' = x := h
  obtain rfl : x'' = x' := h'
  obtain ⟨u, hu, hv⟩ := exists_gen_mul_div (K := Fin 2) (φ := ![(snd T A).left, (translPt A x'').left])
    (ε := ![k, -k]) hN hN' u' hu' q hq
  exact ⟨⟨x'', u, hu⟩, rfl, fun Z τ a z J J' hJ hJ' => hv _ _ z J J' hJ hJ'⟩

/- English proof (translation)
Establish `hQ : (LB.div N N').IsLB` using `LB.isLB_div hN hN'`. Use `WeilIsogeny.weilIs_of_local hG hA hN fun p => ?_` and prove the remaining obligations. Take `⟨V, hV, ⟨θx, θy, ex, ey⟩, H⟩` from `h p`. Take `⟨V', hV', ⟨ηx, ηy, fx, fy⟩, H'⟩` from `h' p`. Set `t` to `overLE (inf_le_left : V ⊓ V' ≤ V)`.

Set `t'` to `overLE (inf_le_right : V ⊓ V' ≤ V')`. Take `⟨θx', ex'⟩` from `exists_pull hN' θx t`. Take `⟨θy', ey'⟩` from `exists_pull hN' θy t`. Take `⟨ηx', fx'⟩` from `exists_pull hQ ηx t'`. Take `⟨ηy', fy'⟩` from `exists_pull hQ ηy t'`.

Establish `a₁ : θx'.pt = overResι (V ⊓ V') ≫ x` using `by rw [ex', ex, ← Category.assoc, overLE_ι]`. Establish `a₂ : θy'.pt = overResι (V ⊓ V') ≫ y` using `by rw [ey', ey, ← Category.assoc, overLE_ι]`. Establish `a₃ : ηx'.pt = overResι (V ⊓ V') ≫ x` using `by rw [fx', fx, ← Category.assoc, overLE_ι]`. Establish `a₄ : ηy'.pt = overResι (V ⊓ V') ≫ y` using `by rw [fy', fy, ← Category.assoc, overLE_ι]`. Take `⟨ξx, gx, vx⟩` from `exists_theta_mul_div hN hN' _ θx' ηx' a₁ a₃`.

Take `⟨ξy, gy, vy⟩` from `exists_theta_mul_div hN hN' _ θy' ηy' a₂ a₄`. Use `⟨V ⊓ V', ⟨hV, hV'⟩, ξx, ξy, gx, gy, (commIsOf_iff hN _ _ _).2 fun Z τ a z J hJ => ?_⟩` and prove the remaining obligations. Use `choose J' hJ' using fun χ : Z.left ⟶ A.left => exists_chart hN' (χ z)`. Establish `hJQ : Good (LB.div N N') z (fun χ => (J χ, J' χ))` using `fun χ => ⟨hJ χ, hJ' χ⟩`. Establish `b₁` using `(commVal_indep hG hA hN' θx' θy' θx θy τ (τ ≫ t) (by rw [ex', Category.assoc]) (by rw [ey', Category.assoc]) a z J' hJ').trans ((commIsOf_iff hN' _ _ _).1 (H θx θy ex ey) Z (τ ≫ t) a z J' hJ')`.

Establish `b₂` using `(commVal_indep hG hA hQ ηx' ηy' ηx ηy τ (τ ≫ t') (by rw [fx', Category.assoc]) (by rw [fy', Category.assoc]) a z _ hJQ).trans ((commIsOf_iff hQ _ _ _).1 (H' ηx ηy fx fy) Z (τ ≫ t') a z _ hJQ)`. Establish `c₁ : (τ ≫ t).left ≫ V.ι = τ.left ≫ (V ⊓ V').ι` using `congrArg (fun q => q.left) (show (τ ≫ t) ≫ overResι V = τ ≫ overResι (V ⊓ V') by rw [Category.assoc, overLE_ι])`. Establish `c₂ : (τ ≫ t').left ≫ V'.ι = τ.left ≫ (V ⊓ V').ι` using `congrArg (fun q => q.left) (show (τ ≫ t') ≫ overResι V' = τ ≫ overResι (V ⊓ V') by rw [Category.assoc, overLE_ι])`. Establish `d₁` using `b₁.trans ((gm_unitRes V c (τ ≫ t).left z).trans (congrArg (fun q => gm q z ⊤ c) c₁))`. Establish `d₂` using `b₂.trans ((gm_unitRes V' d (τ ≫ t').left z).trans (congrArg (fun q => gm q z ⊤ d) c₂))`.

Use `Eq.trans ?_ ((gm_unitRes (V ⊓ V') (c * d) τ.left z).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) d₁ d₂).symm)).symm` and prove the remaining obligations. Unfold `commVal`. Rewrite using `[vx _ _ _ _ _ _ hJ hJ', vx _ _ _ _ _ _ hJ hJ', vy _ _ _ _ _ _ hJ hJ', vy _ _ _ _ _ _ hJ hJ', gx, gy, a₁, a₂, a₃, a₄]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`.

Normalize the expressions using the abelian group laws.
-/
theorem weilIs_mul_div (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {N N' : LB A.left} (hN : N.IsLB) (hN' : N'.IsLB)
    {k : ℤ} {T : Over S} {x y : T ⟶ A} {c d : Γ(T.left, ⊤)ˣ} (h : WeilIs A N' k x y c)
    (h' : WeilIs A (LB.div N N') k x y d) : WeilIs A N k x y (c * d) := by
  have hQ : (LB.div N N').IsLB := LB.isLB_div hN hN'
  refine WeilIsogeny.weilIs_of_local hG hA hN fun p => ?_
  obtain ⟨V, hV, ⟨θx, θy, ex, ey⟩, H⟩ := h p
  obtain ⟨V', hV', ⟨ηx, ηy, fx, fy⟩, H'⟩ := h' p
  let t := overLE (inf_le_left : V ⊓ V' ≤ V)
  let t' := overLE (inf_le_right : V ⊓ V' ≤ V')
  obtain ⟨θx', ex'⟩ := exists_pull hN' θx t
  obtain ⟨θy', ey'⟩ := exists_pull hN' θy t
  obtain ⟨ηx', fx'⟩ := exists_pull hQ ηx t'
  obtain ⟨ηy', fy'⟩ := exists_pull hQ ηy t'
  have a₁ : θx'.pt = overResι (V ⊓ V') ≫ x := by rw [ex', ex, ← Category.assoc, overLE_ι]
  have a₂ : θy'.pt = overResι (V ⊓ V') ≫ y := by rw [ey', ey, ← Category.assoc, overLE_ι]
  have a₃ : ηx'.pt = overResι (V ⊓ V') ≫ x := by rw [fx', fx, ← Category.assoc, overLE_ι]
  have a₄ : ηy'.pt = overResι (V ⊓ V') ≫ y := by rw [fy', fy, ← Category.assoc, overLE_ι]
  obtain ⟨ξx, gx, vx⟩ := exists_theta_mul_div hN hN' _ θx' ηx' a₁ a₃
  obtain ⟨ξy, gy, vy⟩ := exists_theta_mul_div hN hN' _ θy' ηy' a₂ a₄
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, ξx, ξy, gx, gy, (commIsOf_iff hN _ _ _).2 fun Z τ a z J hJ => ?_⟩
  choose J' hJ' using fun χ : Z.left ⟶ A.left => exists_chart hN' (χ z)
  have hJQ : Good (LB.div N N') z (fun χ => (J χ, J' χ)) := fun χ => ⟨hJ χ, hJ' χ⟩
  have b₁ := (commVal_indep hG hA hN' θx' θy' θx θy τ (τ ≫ t) (by rw [ex', Category.assoc])
    (by rw [ey', Category.assoc]) a z J' hJ').trans
    ((commIsOf_iff hN' _ _ _).1 (H θx θy ex ey) Z (τ ≫ t) a z J' hJ')
  have b₂ := (commVal_indep hG hA hQ ηx' ηy' ηx ηy τ (τ ≫ t') (by rw [fx', Category.assoc])
    (by rw [fy', Category.assoc]) a z _ hJQ).trans
    ((commIsOf_iff hQ _ _ _).1 (H' ηx ηy fx fy) Z (τ ≫ t') a z _ hJQ)
  have c₁ : (τ ≫ t).left ≫ V.ι = τ.left ≫ (V ⊓ V').ι :=
    congrArg (fun q => q.left) (show (τ ≫ t) ≫ overResι V = τ ≫ overResι (V ⊓ V') by rw [Category.assoc, overLE_ι])
  have c₂ : (τ ≫ t').left ≫ V'.ι = τ.left ≫ (V ⊓ V').ι :=
    congrArg (fun q => q.left) (show (τ ≫ t') ≫ overResι V' = τ ≫ overResι (V ⊓ V') by rw [Category.assoc, overLE_ι])
  have d₁ := b₁.trans ((gm_unitRes V c (τ ≫ t).left z).trans (congrArg (fun q => gm q z ⊤ c) c₁))
  have d₂ := b₂.trans ((gm_unitRes V' d (τ ≫ t').left z).trans (congrArg (fun q => gm q z ⊤ d) c₂))
  refine Eq.trans ?_ ((gm_unitRes (V ⊓ V') (c * d) τ.left z).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) d₁ d₂).symm)).symm
  unfold commVal
  rw [vx _ _ _ _ _ _ hJ hJ', vx _ _ _ _ _ _ hJ hJ', vy _ _ _ _ _ _ hJ hJ',
    vy _ _ _ _ _ _ hJ hJ', gx, gy, a₁, a₂, a₃, a₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/- English proof (translation)
Take `⟨w, hw⟩` from `hw.symm`. Take `⟨t, ht⟩` from `gen_chartPull (chartPullDiv N N' (PrimCocycle.lamφ A) PrimCocycle.lamε) w hw`. Use `weilIs_mul_div hG hA hN hN' h (weilIs_one_of_lam hG hA (LB.isLB_div hN hN') t ht x y)` as an intermediate fact. Rewrite `this` using `[_root_.mul_one]`. Then use the resulting hypothesis.
-/
theorem weilIs_of_lam_iso (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {N N' : LB A.left} (hN : N.IsLB)
    (hN' : N'.IsLB) (hw : LBIso (abelian₂ A N) (abelian₂ A N')) {T : Over S} {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ}
    (h : WeilIs A N' 1 x y c) : WeilIs A N 1 x y c := by
  obtain ⟨w, hw⟩ := hw.symm
  obtain ⟨t, ht⟩ := gen_chartPull (chartPullDiv N N' (PrimCocycle.lamφ A) PrimCocycle.lamε) w hw
  have := weilIs_mul_div hG hA hN hN' h (weilIs_one_of_lam hG hA (LB.isLB_div hN hN') t ht x y)
  rwa [_root_.mul_one] at this

/- English proof (translation)
Establish `e₁ : translPt A (1 : T ⟶ A) = snd T A` using `by show (fst _ A ≫ (1 : T ⟶ A)) * snd _ A = _`. Rewrite using `[MonObj.comp_one, _root_.one_mul]`. Take `⟨o, ho, hv⟩` from `exists_gen hM (K' := Fin 2) (φ' := ![(snd T A).left, (translPt A (1 : T ⟶ A)).left]) (ε' := ![1, -1]) (fun U _ g => by`. Rewrite using `[Fin.prod_univ_two, Fintype.prod_empty, e₁]`. Use `show _ = g (snd T A).left ^ (1 : ℤ) * g (snd T A).left ^ (-1 : ℤ)`.

Use the proof step `simp)`. Use the proof step `(LB.oneGen M) (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)`. Conclude with `⟨⟨_, o, ho⟩, rfl, fun Z τ a z J hJ => (hv _ _ z J hJ).trans (val_one _)⟩`.
-/
theorem exists_theta_one {M : LB A.left} (hM : M.IsLB) (T : Over S) :
    ∃ θ : ThetaGrp A M 1 T, θ.pt = 1 ∧ ∀ (Z : Over S) (τ : Z ⟶ T) (a : Z ⟶ A) (z : Z.left) (J), Good M z J →
      thetaVal θ τ a z J = 1 := by
  have e₁ : translPt A (1 : T ⟶ A) = snd T A := by
    show (fst _ A ≫ (1 : T ⟶ A)) * snd _ A = _
    rw [MonObj.comp_one, _root_.one_mul]
  obtain ⟨o, ho, hv⟩ := exists_gen hM (K' := Fin 2)
    (φ' := ![(snd T A).left, (translPt A (1 : T ⟶ A)).left]) (ε' := ![1, -1])
    (fun U _ g => by
      rw [Fin.prod_univ_two, Fintype.prod_empty, e₁]
      show _ = g (snd T A).left ^ (1 : ℤ) * g (snd T A).left ^ (-1 : ℤ)
      simp)
    (LB.oneGen M) (fun i j => (map_one _).trans
      ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  exact ⟨⟨_, o, ho⟩, rfl, fun Z τ a z J hJ => (hv _ _ z J hJ).trans (val_one _)⟩

/- English proof (translation)
Use `WeilIsogeny.weilIs_of_local hG hA hM fun p => ?_` and prove the remaining obligations. Take `⟨V, hV, θ, hθ⟩` from `h p`. Take `⟨o, ho, v⟩` from `exists_theta_one hM (overRes V)`. Use `⟨V, hV, θ, o, hθ, ho.trans (MonObj.comp_one _).symm, (commIsOf_iff hM _ _ _).2 fun Z τ a z J hJ => ?_⟩` and prove the remaining obligations. Establish `e' : unitRes V (1 : Γ(T.left, ⊤)ˣ) = 1` using `map_one _`.

Rewrite using `[e', map_one, commVal, v _ _ _ _ _ hJ, v _ _ _ _ _ hJ, ho, MonObj.comp_one, _root_.one_mul, _root_.one_mul, _root_.mul_one, mul_inv_cancel]`.
-/
theorem weilIs_one_right (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {M : LB A.left} (hM : M.IsLB) {T : Over S}
    {y : T ⟶ A} (h : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp A M 1 (overRes V), θ.pt = overResι V ≫ y) : WeilIs A M 1 y 1 1 := by
  refine WeilIsogeny.weilIs_of_local hG hA hM fun p => ?_
  obtain ⟨V, hV, θ, hθ⟩ := h p
  obtain ⟨o, ho, v⟩ := exists_theta_one hM (overRes V)
  refine ⟨V, hV, θ, o, hθ, ho.trans (MonObj.comp_one _).symm, (commIsOf_iff hM _ _ _).2 fun Z τ a z J hJ => ?_⟩
  have e' : unitRes V (1 : Γ(T.left, ⊤)ˣ) = 1 := map_one _
  rw [e', map_one, commVal, v _ _ _ _ _ hJ, v _ _ _ _ _ hJ, ho, MonObj.comp_one, _root_.one_mul, _root_.one_mul,
    _root_.mul_one, mul_inv_cancel]

/- English proof (translation)
Take `⟨d, hd⟩` from `exists_isGen_translDiff_comp A M y (overResι V) V (fun q => q.2) c hc`. Take `⟨u, hu, -⟩` from `exists_gen hM (K' := Fin 2) (φ' := ![(snd (overRes V) A).left, (translPt A (overResι V ≫ y)).left]) (ε' := ![1, -1]) (fun U _ g => by`. Rewrite using `[Fin.prod_univ_two, Fin.prod_univ_two, mul_comm]`. Use the proof step `rfl)`. Use the proof step `(LB.invGen M (K := Fin 2) ![(translPt A (overResι V ≫ y)).left, (snd (overRes V) A).left] ![1, -1] d)`.

Use the proof step `(DVR.invGen_isGen _ _ _ _ hd)`. Conclude with `⟨⟨_, u, hu⟩, rfl⟩`.
-/
theorem exists_theta_of_translDiff {M : LB A.left} (hM : M.IsLB) {T : Over S} (y : T ⟶ A) (V : T.left.Opens)
    (c : LB.Gen ((translDiff A M y).pull ((fst T A).left ⁻¹ᵁ V).ι)) (hc : c.IsGen) :
    ∃ θ : ThetaGrp A M 1 (overRes V), θ.pt = overResι V ≫ y := by
  obtain ⟨d, hd⟩ := exists_isGen_translDiff_comp A M y (overResι V) V (fun q => q.2) c hc
  obtain ⟨u, hu, -⟩ := exists_gen hM (K' := Fin 2)
    (φ' := ![(snd (overRes V) A).left, (translPt A (overResι V ≫ y)).left]) (ε' := ![1, -1]) (fun U _ g => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two, mul_comm]; rfl)
    (LB.invGen M (K := Fin 2) ![(translPt A (overResι V ≫ y)).left, (snd (overRes V) A).left] ![1, -1] d)
    (DVR.invGen_isGen _ _ _ _ hd)
  exact ⟨⟨_, u, hu⟩, rfl⟩

/- English proof (translation)
Use `Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun p => ?_)` and prove the remaining obligations. Take `⟨V, hV, ⟨θ, -, hx, -⟩, -⟩` from `h p`. Establish `key : θ.pt ^ n = 1` using `(hK S P n hn _ θ.pt).1 fun p => ⟨⊤, trivial, gen_chartPull (chartPullPull _ _ _ rfl) θ.φ θ.isGen⟩`. Rewrite `key` using `[hx, ← MonObj.comp_pow, ← MonObj.comp_one (overResι V)]`. Conclude with `⟨V, hV, congrArg (fun q => q.left) key⟩`.
-/
theorem pow_eq_one_of_weilIs (hK : KerPowSt) [IsLocallyNoetherian S] (P : PolAV S) {T : Over S} {n : ℕ}
    (hn : 0 < n) {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ} (h : WeilIs P.A P.L n x y c) : x ^ n = 1 := by
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun p => ?_)
  obtain ⟨V, hV, ⟨θ, -, hx, -⟩, -⟩ := h p
  have key : θ.pt ^ n = 1 :=
    (hK S P n hn _ θ.pt).1 fun p => ⟨⊤, trivial, gen_chartPull (chartPullPull _ _ _ rfl) θ.φ θ.isGen⟩
  rw [hx, ← MonObj.comp_pow, ← MonObj.comp_one (overResι V)] at key
  exact ⟨V, hV, congrArg (fun q => q.left) key⟩

end Pairing

/- English proof (translation)
The claim follows from `LBIso.chartPull (chartPullPull L (𝟙 X) (𝟙 X) rfl) ⟨id, fun _ _ h => h, fun _ _ _ _ _ => rfl⟩ (PolBaseChange.lbIso_refl hL)`.
-/
theorem lbIso_pull_id {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso (L.pull (𝟙 X)) L :=
  LBIso.chartPull (chartPullPull L (𝟙 X) (𝟙 X) rfl) ⟨id, fun _ _ h => h, fun _ _ _ _ _ => rfl⟩
    (PolBaseChange.lbIso_refl hL)

/- English proof (translation)
Set `D : Subgroup G` to `⨅ c : C, (e.flip c).ker`. Establish `mem : ∀ d, d ∈ D ↔ ∀ c ∈ C, e d c = 1` using `fun d => by simp [D, Subgroup.mem_iInf]`. Establish `hCD : C ≤ D` using `fun c hc => (mem c).2 (iso c hc)`. Set `f : D → (G ⧸ C →* kˣ)` to `fun d => QuotientGroup.lift C (e d) ((mem d).1 d.2)`. Establish `hf : Function.Injective f` using `fun d d' h => Subtype.ext (by`.

Use `mul_inv_eq_one.1 (he _ fun y => ?_)` and prove the remaining obligations. Establish `: e d y = e d' y` using `DFunLike.congr_fun h (y : G ⧸ C)`. Rewrite using `[map_mul, map_inv, MonoidHom.mul_apply, MonoidHom.inv_apply, this, mul_inv_cancel])`. Establish `: NeZero (Monoid.exponent (G ⧸ C) : k)` using `⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩`. Establish `h₁ : Nat.card (G ⧸ C →* kˣ) = Nat.card (G ⧸ C)` using `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ _`.

Establish `h₂ : Nat.card (G ⧸ C) = Nat.card C` using `Nat.eq_of_mul_eq_mul_right Nat.card_pos ((Subgroup.card_eq_card_quotient_mul_card_subgroup C).symm.trans hC)`. Establish `: Finite (G ⧸ C →* kˣ)` using `Nat.finite_of_card_ne_zero (by rw [h₁]; exact Nat.card_pos.ne')`. Establish `h₃ : Nat.card D ≤ Nat.card C` using `(Nat.card_le_card_of_injective f hf).trans (h₁.trans h₂).le`. Rewrite using `[Subgroup.eq_of_le_of_card_ge hCD h₃]`. Conclude with `(mem x).2 hx`.
-/
theorem mem_of_orthogonal {G k : Type} [CommGroup G] [Finite G] [Field k] [IsAlgClosed k] [CharZero k]
    (e : G →* G →* kˣ) (he : ∀ x, (∀ y, e x y = 1) → x = 1) (C : Subgroup G)
    (hC : Nat.card G = Nat.card C * Nat.card C) (iso : ∀ c ∈ C, ∀ c' ∈ C, e c c' = 1)
    {x : G} (hx : ∀ c ∈ C, e x c = 1) : x ∈ C := by
  let D : Subgroup G := ⨅ c : C, (e.flip c).ker
  have mem : ∀ d, d ∈ D ↔ ∀ c ∈ C, e d c = 1 := fun d => by simp [D, Subgroup.mem_iInf]
  have hCD : C ≤ D := fun c hc => (mem c).2 (iso c hc)
  let f : D → (G ⧸ C →* kˣ) := fun d => QuotientGroup.lift C (e d) ((mem d).1 d.2)
  have hf : Function.Injective f := fun d d' h => Subtype.ext (by
    refine mul_inv_eq_one.1 (he _ fun y => ?_)
    have : e d y = e d' y := DFunLike.congr_fun h (y : G ⧸ C)
    rw [map_mul, map_inv, MonoidHom.mul_apply, MonoidHom.inv_apply, this, mul_inv_cancel])
  have : NeZero (Monoid.exponent (G ⧸ C) : k) := ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  have h₁ : Nat.card (G ⧸ C →* kˣ) = Nat.card (G ⧸ C) := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ _
  have h₂ : Nat.card (G ⧸ C) = Nat.card C :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos ((Subgroup.card_eq_card_quotient_mul_card_subgroup C).symm.trans hC)
  have : Finite (G ⧸ C →* kˣ) := Nat.finite_of_card_ne_zero (by rw [h₁]; exact Nat.card_pos.ne')
  have h₃ : Nat.card D ≤ Nat.card C := (Nat.card_le_card_of_injective f hf).trans (h₁.trans h₂).le
  rw [Subgroup.eq_of_le_of_card_ge hCD h₃]
  exact (mem x).2 hx

section Main

variable {k : Type} [Field k] {P : PolAV (Sp k)} {n : ℕ} {B : Over (Sp k)} [GrpObj B] {ψ : P.A ⟶ B} [IsMonHom ψ]
  {M : LB B.left}

/- English proof (translation)
Establish `hM' : (M.pull ψ.left).IsLB` using `DVR.linComb_isLB _ hM _ _`. Establish `hN : (lbPow P.L n).IsLB` using `DVR.linComb_isLB _ P.isLB _ _`. Establish `h₁ : WeilIs P.A (M.pull ψ.left) 1 x c 1` using `WeilIsogeny.weilIs_pull_hom (d := 1) (n := 1) hG P.isAb hM' hM ψ (lbIso_pull_id hM') (hc.symm ▸ hx)`. Establish `h₂` using `weilIs_of_lam_iso hG P.isAb hN hM' hw h₁`. Establish `h₃` using `WeilIsogeny.weilIs_pull_hom (d := n) (n := 1) (x := x) (y := c) (c := 1) hG P.isAb P.isLB hN (𝟙 P.A) (lbIso_pull_id hN).symm (by rwa [Category.comp_id, Category.comp_id])`.

Rewrite `h₃` using `[_root_.one_mul]`. Then use the resulting hypothesis.
-/
theorem weilIs_of_ker (hG : GlobalFnsSt) (hM : M.IsLB)
    (hw : LBIso (abelian₂ P.A (lbPow P.L n)) (abelian₂ P.A (M.pull ψ.left))) {T : Over (Sp k)} {x c : T ⟶ P.A}
    (hx : WeilIs B M 1 (x ≫ ψ) 1 1) (hc : c ≫ ψ = 1) : WeilIs P.A P.L n x c 1 := by
  have hM' : (M.pull ψ.left).IsLB := DVR.linComb_isLB _ hM _ _
  have hN : (lbPow P.L n).IsLB := DVR.linComb_isLB _ P.isLB _ _
  have h₁ : WeilIs P.A (M.pull ψ.left) 1 x c 1 :=
    WeilIsogeny.weilIs_pull_hom (d := 1) (n := 1) hG P.isAb hM' hM ψ (lbIso_pull_id hM') (hc.symm ▸ hx)
  have h₂ := weilIs_of_lam_iso hG P.isAb hN hM' hw h₁
  have h₃ := WeilIsogeny.weilIs_pull_hom (d := n) (n := 1) (x := x) (y := c) (c := 1) hG P.isAb P.isLB hN (𝟙 P.A)
    (lbIso_pull_id hN).symm (by rwa [Category.comp_id, Category.comp_id])
  rwa [_root_.one_mul] at h₃

/- English proof (translation)
Use `P.isAb.comm` as an intermediate fact. Establish `hG` using `hL.globalFns`. Establish `hnk : (n : k) ≠ 0` using `Nat.cast_ne_zero.2 hn.ne'`. Establish `iso : ∀ c c' : 𝟙_ (Over (Sp k)) ⟶ P.A, c ≫ ψ = 1 → c' ≫ ψ = 1 → WeilIs P.A P.L n c c' 1` using `fun c c' h h' => weilIs_of_ker hG hM hw (by`. Rewrite using `[h]`.

Conclude with `weilIs_one_right hG hB hM fun p => ⟨⊤, trivial, (exists_theta_one hM _).imp fun θ e => e.1.trans (MonObj.comp_one _).symm⟩) h'`. Set `G : Subgroup (𝟙_ (Over (Sp k)) ⟶ P.A)` to `(powMonoidHom n).ker`. Establish `hGc : Nat.card G = n ^ (2 * P.g)` using `(hL.mulN _ P n hn).2.2.2.2 k (𝟙 _) hnk`. Establish `: Finite G` using `Nat.finite_of_card_ne_zero (by rw [hGc]; exact pow_ne_zero _ hn.ne')`. Take `⟨hex, hmul, -, -⟩` from `hL.weil _ P n (𝟙_ (Over (Sp k)))`.

Use `choose v hv using fun a b : G => (hex a.1 b.1 a.2 b.2).exists`. Establish `un : ∀ {a b : G} {c}, WeilIs P.A P.L n a.1 b.1 c → v a b = c` using `fun h => weilIs_unique hG P.isAb P.isLB (hv _ _) h`. Set `κ : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ →* kˣ` to `Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom`. Establish `hι : Function.Injective κ` using `Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).hom).1`. Establish `ml : ∀ a a' b : G, v (a * a') b = v a b * v a' b` using `fun a a' b => un (hmul _ _ _ _ _ (hv a b) (hv a' b))`.

Establish `sy : ∀ a b : G, v a b = (v b a)⁻¹` using `fun a b => un (CommPairing.weilIs_symm P.isLB (hv b a))`. Set `e : G →* G →* kˣ` to `MonoidHom.mk' (fun a => MonoidHom.mk' (fun b => κ (v a b)) fun b b' => by`. Rewrite using `[← map_mul, sy, ml, mul_inv, ← sy, ← sy]) fun a a' => MonoidHom.ext fun b => by`. Use `show κ _ = κ _ * κ _`. Rewrite using `[ml, map_mul]`.

Establish `e1 : ∀ {a b : G}, WeilIs P.A P.L n a.1 b.1 1 → e a b = 1` using `fun h => (congrArg κ (un h)).trans (map_one κ)`. Set `ρ : (𝟙_ (Over (Sp k)) ⟶ P.A) →* (𝟙_ (Over (Sp k)) ⟶ B)` to `MonoidHom.mk' (· ≫ ψ) fun a b => MonObj.mul_comp a b ψ`. Establish `le : ρ.ker ≤ G` using `fun c h => pow_eq_one_of_weilIs hL.kerPow P hn (iso c c h h)`. Establish `hC : Nat.card (ρ.ker.subgroupOf G) = n ^ P.g` using `(Nat.card_congr (Subgroup.subgroupOfEquivOfLe le).toEquiv).trans hc`. Conclude with `mem_of_orthogonal e (fun a ha => Subtype.ext (hL.weilNondeg k P n hnk a.1 a.2 fun y hy => by`.

Establish `: v a ⟨y, hy⟩ = 1` using `hι ((ha ⟨y, hy⟩).trans (map_one κ).symm)`. Conclude with `this ▸ hv a ⟨y, hy⟩)) (ρ.ker.subgroupOf G) (by rw [hGc, hC, ← pow_add, two_mul])`. Use the proof step `(fun c h c' h' => e1 (iso _ _ h h')) (x := ⟨x, hx⟩) (fun c h => e1 (ho _ h))`.
-/
theorem comp_eq_one_of_orthogonal [IsAlgClosed k] [CharZero k] (hL : Laws) (hn : 0 < n) (hB : IsAbelianScheme B)
    (hM : M.IsLB) (hc : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ≫ ψ = 1} = n ^ P.g)
    (hw : LBIso (abelian₂ P.A (lbPow P.L n)) (abelian₂ P.A (M.pull ψ.left))) {x : 𝟙_ (Over (Sp k)) ⟶ P.A} (hx : x ^ n = 1)
    (ho : ∀ c : 𝟙_ (Over (Sp k)) ⟶ P.A, c ≫ ψ = 1 → WeilIs P.A P.L n x c 1) : x ≫ ψ = 1 := by
  have := P.isAb.comm
  have hG := hL.globalFns
  have hnk : (n : k) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have iso : ∀ c c' : 𝟙_ (Over (Sp k)) ⟶ P.A, c ≫ ψ = 1 → c' ≫ ψ = 1 → WeilIs P.A P.L n c c' 1 := fun c c' h h' =>
    weilIs_of_ker hG hM hw (by
      rw [h]
      exact weilIs_one_right hG hB hM fun p => ⟨⊤, trivial, (exists_theta_one hM _).imp fun θ e =>
        e.1.trans (MonObj.comp_one _).symm⟩) h'
  let G : Subgroup (𝟙_ (Over (Sp k)) ⟶ P.A) := (powMonoidHom n).ker
  have hGc : Nat.card G = n ^ (2 * P.g) := (hL.mulN _ P n hn).2.2.2.2 k (𝟙 _) hnk
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hGc]; exact pow_ne_zero _ hn.ne')
  obtain ⟨hex, hmul, -, -⟩ := hL.weil _ P n (𝟙_ (Over (Sp k)))
  choose v hv using fun a b : G => (hex a.1 b.1 a.2 b.2).exists
  have un : ∀ {a b : G} {c}, WeilIs P.A P.L n a.1 b.1 c → v a b = c := fun h =>
    weilIs_unique hG P.isAb P.isLB (hv _ _) h
  let κ : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ →* kˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom
  have hι : Function.Injective κ :=
    Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).hom).1
  have ml : ∀ a a' b : G, v (a * a') b = v a b * v a' b := fun a a' b => un (hmul _ _ _ _ _ (hv a b) (hv a' b))
  have sy : ∀ a b : G, v a b = (v b a)⁻¹ := fun a b => un (CommPairing.weilIs_symm P.isLB (hv b a))
  let e : G →* G →* kˣ := MonoidHom.mk' (fun a => MonoidHom.mk' (fun b => κ (v a b)) fun b b' => by
      rw [← map_mul, sy, ml, mul_inv, ← sy, ← sy]) fun a a' => MonoidHom.ext fun b => by
    show κ _ = κ _ * κ _
    rw [ml, map_mul]
  have e1 : ∀ {a b : G}, WeilIs P.A P.L n a.1 b.1 1 → e a b = 1 := fun h => (congrArg κ (un h)).trans (map_one κ)
  let ρ : (𝟙_ (Over (Sp k)) ⟶ P.A) →* (𝟙_ (Over (Sp k)) ⟶ B) :=
    MonoidHom.mk' (· ≫ ψ) fun a b => MonObj.mul_comp a b ψ
  have le : ρ.ker ≤ G := fun c h => pow_eq_one_of_weilIs hL.kerPow P hn (iso c c h h)
  have hC : Nat.card (ρ.ker.subgroupOf G) = n ^ P.g :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe le).toEquiv).trans hc
  exact mem_of_orthogonal e (fun a ha => Subtype.ext (hL.weilNondeg k P n hnk a.1 a.2 fun y hy => by
      have : v a ⟨y, hy⟩ = 1 := hι ((ha ⟨y, hy⟩).trans (map_one κ).symm)
      exact this ▸ hv a ⟨y, hy⟩)) (ρ.ker.subgroupOf G) (by rw [hGc, hC, ← pow_add, two_mul])
    (fun c h c' h' => e1 (iso _ _ h h')) (x := ⟨x, hx⟩) (fun c h => e1 (ho _ h))

end Main

end GlobalTheory.DescendedPrincipal

namespace GlobalTheory

open DescendedPrincipal in

/- English proof (translation)
Introduce `hL k _ _ _ P n B _ ψ M hn hB hM hψ _ _ _ hc hw R _ t y hy`. Establish `hG` using `hL.globalFns`. Establish `h₀ : WeilIs B M 1 y 1 1` using `weilIs_one_right hG hB hM fun p => by`. Take `⟨V, hV, c, hc⟩` from `hy p`. Conclude with `⟨V, hV, exists_theta_of_translDiff hM y V c hc⟩`.

Set `T : Over (Sp k)` to `Over.mk (pullback.snd ψ.left y.left ≫ t)`. Set `π : T ⟶ Over.mk t` to `Over.homMk (pullback.snd ψ.left y.left) rfl`. Set `x : T ⟶ P.A` to `Over.homMk (pullback.fst ψ.left y.left) (by show pullback.fst ψ.left y.left ≫ P.A.hom = pullback.snd ψ.left y.left ≫ t`. Rewrite using `[← Over.w ψ, pullback.condition_assoc]`. Conclude with `congrArg (_ ≫ ·) (Over.w y))`.

Establish `hxy : x ≫ ψ = π ≫ y` using `Over.OverMorphism.ext pullback.condition`. Establish `h₁ : WeilIs B M 1 (x ≫ ψ) 1 1`. Use `CommPairing.weilIs_pull hG hB hM π h₀` as an intermediate fact. Rewrite `this` using `[MonObj.comp_one, map_one, ← hxy]`. Then use the resulting hypothesis. Establish `hx : x ^ n = 1` using `pow_eq_one_of_weilIs hL.kerPow P hn (weilIs_of_ker hG hM hw h₁ (MonObj.one_comp ψ))`.

Establish `: Etale (mulA P.A n).left` using `(hL.mulN _ P n hn).2.2.2.1 (by`. Simplify using `using (Ne.isUnit (Nat.cast_ne_zero.2 hn.ne' : (n : k) ≠ 0)).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)`. Establish `hz : x ≫ ψ = 1`. Use `Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun p => ?_)` and prove the remaining obligations. Take `⟨W, c, _, ⟨w, hp⟩, x₀, hx₀, e⟩` from `exists_local_rational_torsion P.A n x hx p`.

Establish `h₂ : WeilIs B M 1 ((toUnit W ≫ x₀) ≫ ψ) 1 1`. Use `CommPairing.weilIs_pull hG hB hM c h₁` as an intermediate fact. Rewrite `this` using `[MonObj.comp_one, map_one, ← Category.assoc, e]`. Then use the resulting hypothesis. Establish `h₃ : x₀ ≫ ψ = 1` using `comp_eq_one_of_orthogonal hL hn hB hM hc hw hx₀ fun d hd => by`. Establish `h₄` using `weilIs_of_ker hG hM hw h₂ (c := toUnit W ≫ d) (by rw [Category.assoc, hd, MonObj.comp_one])`.

Establish `hd' : d ^ n = 1` using `pow_eq_one_of_weilIs hL.kerPow P hn (weilIs_of_ker hG hM hw (c := 1) (by`. Rewrite using `[hd]`. Conclude with `weilIs_one_right hG hB hM fun p => ⟨⊤, trivial, (exists_theta_one hM _).imp fun θ e => e.1.trans (MonObj.comp_one _).symm⟩) (MonObj.one_comp ψ))`. Take `⟨ζ, hζ, -⟩` from `(hL.weil _ P n _).1 x₀ d hx₀ hd'`. Establish `h₅` using `CommutatorPairing.weilIs_unique hG P.isAb P.isLB (CommPairing.weilIs_pull hG P.isAb P.isLB (toUnit W) hζ) h₄`.

Establish `: Nonempty (⊤ : W.left.Opens)` using `⟨⟨w, trivial⟩⟩`. Establish `hinj : Function.Injective (toUnit W).left.appTop.hom`. Establish `: Function.Injective ((toUnit W).left.appTop.hom ∘ (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)` using `RingHom.injective ((toUnit W).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)`. Conclude with `this.of_comp_right (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2`. Take `rfl : ζ = 1` from `Units.map_injective (f := (toUnit W).left.appTop.hom.toMonoidHom) hinj (h₅.trans (map_one _).symm)`.

Conclude with `hζ`. Establish `h₆ : c ≫ x ≫ ψ = c ≫ 1`. Rewrite using `[← Category.assoc, e, Category.assoc, h₃, MonObj.comp_one, MonObj.comp_one]`. Use `⟨c.left.opensRange, ⟨w, hp⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_epi c.left.isoOpensRange.hom, Scheme.Hom.isoOpensRange_hom_ι_assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc]`.

Conclude with `congrArg (fun q => q.left) h₆`. Establish `: Epi (pullback.snd ψ.left y.left)` using `Flat.epi_of_flat_of_surjective _`. Establish `h₇ : π ≫ y = π ≫ 1` using `by rw [← hxy, hz, MonObj.comp_one]`. Conclude with `Over.OverMorphism.ext ((cancel_epi (pullback.snd ψ.left y.left)).1 (congrArg (fun q => q.left) h₇))`.
-/
theorem kTriv_of_descent : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (P : Out.PolAV (Sp k)) (n : ℕ) (B : Over (Sp k)) [GrpObj B] (ψ : P.A ⟶ B) (M : LB B.left), 0 < n → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ≫ ψ = 1} = n ^ P.g → LBIso (abelian₂ P.A (lbPow P.L n)) (abelian₂ P.A (M.pull ψ.left)) → Out.KTriv B M := by
  intro hL k _ _ _ P n B _ ψ M hn hB hM hψ _ _ _ hc hw R _ t y hy
  have hG := hL.globalFns
  have h₀ : WeilIs B M 1 y 1 1 := weilIs_one_right hG hB hM fun p => by
    obtain ⟨V, hV, c, hc⟩ := hy p
    exact ⟨V, hV, exists_theta_of_translDiff hM y V c hc⟩
  let T : Over (Sp k) := Over.mk (pullback.snd ψ.left y.left ≫ t)
  let π : T ⟶ Over.mk t := Over.homMk (pullback.snd ψ.left y.left) rfl
  let x : T ⟶ P.A := Over.homMk (pullback.fst ψ.left y.left) (by
    show pullback.fst ψ.left y.left ≫ P.A.hom = pullback.snd ψ.left y.left ≫ t
    rw [← Over.w ψ, pullback.condition_assoc]
    exact congrArg (_ ≫ ·) (Over.w y))
  have hxy : x ≫ ψ = π ≫ y := Over.OverMorphism.ext pullback.condition
  have h₁ : WeilIs B M 1 (x ≫ ψ) 1 1 := by
    have := CommPairing.weilIs_pull hG hB hM π h₀
    rwa [MonObj.comp_one, map_one, ← hxy] at this
  have hx : x ^ n = 1 := pow_eq_one_of_weilIs hL.kerPow P hn (weilIs_of_ker hG hM hw h₁ (MonObj.one_comp ψ))
  have : Etale (mulA P.A n).left := (hL.mulN _ P n hn).2.2.2.1 (by
    simpa using (Ne.isUnit (Nat.cast_ne_zero.2 hn.ne' : (n : k) ≠ 0)).map
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
  have hz : x ≫ ψ = 1 := by
    refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun p => ?_)
    obtain ⟨W, c, _, ⟨w, hp⟩, x₀, hx₀, e⟩ := exists_local_rational_torsion P.A n x hx p
    have h₂ : WeilIs B M 1 ((toUnit W ≫ x₀) ≫ ψ) 1 1 := by
      have := CommPairing.weilIs_pull hG hB hM c h₁
      rwa [MonObj.comp_one, map_one, ← Category.assoc, e] at this
    have h₃ : x₀ ≫ ψ = 1 := comp_eq_one_of_orthogonal hL hn hB hM hc hw hx₀ fun d hd => by
      have h₄ := weilIs_of_ker hG hM hw h₂ (c := toUnit W ≫ d) (by rw [Category.assoc, hd, MonObj.comp_one])
      have hd' : d ^ n = 1 := pow_eq_one_of_weilIs hL.kerPow P hn (weilIs_of_ker hG hM hw (c := 1) (by
        rw [hd]
        exact weilIs_one_right hG hB hM fun p => ⟨⊤, trivial, (exists_theta_one hM _).imp fun θ e =>
          e.1.trans (MonObj.comp_one _).symm⟩) (MonObj.one_comp ψ))
      obtain ⟨ζ, hζ, -⟩ := (hL.weil _ P n _).1 x₀ d hx₀ hd'
      have h₅ := CommutatorPairing.weilIs_unique hG P.isAb P.isLB
        (CommPairing.weilIs_pull hG P.isAb P.isLB (toUnit W) hζ) h₄
      have : Nonempty (⊤ : W.left.Opens) := ⟨⟨w, trivial⟩⟩
      have hinj : Function.Injective (toUnit W).left.appTop.hom := by
        have : Function.Injective ((toUnit W).left.appTop.hom ∘ (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) :=
          RingHom.injective ((toUnit W).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
        exact this.of_comp_right (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2
      obtain rfl : ζ = 1 := Units.map_injective (f := (toUnit W).left.appTop.hom.toMonoidHom) hinj
        (h₅.trans (map_one _).symm)
      exact hζ
    have h₆ : c ≫ x ≫ ψ = c ≫ 1 := by
      rw [← Category.assoc, e, Category.assoc, h₃, MonObj.comp_one, MonObj.comp_one]
    refine ⟨c.left.opensRange, ⟨w, hp⟩, ?_⟩
    rw [← cancel_epi c.left.isoOpensRange.hom, Scheme.Hom.isoOpensRange_hom_ι_assoc,
      Scheme.Hom.isoOpensRange_hom_ι_assoc]
    exact congrArg (fun q => q.left) h₆
  have : Epi (pullback.snd ψ.left y.left) := Flat.epi_of_flat_of_surjective _
  have h₇ : π ≫ y = π ≫ 1 := by rw [← hxy, hz, MonObj.comp_one]
  exact Over.OverMorphism.ext ((cancel_epi (pullback.snd ψ.left y.left)).1 (congrArg (fun q => q.left) h₇))

end GlobalTheory
