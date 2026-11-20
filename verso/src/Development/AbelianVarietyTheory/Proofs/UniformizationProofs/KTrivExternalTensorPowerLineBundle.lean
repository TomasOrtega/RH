import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoxKernel

open GlobalTheory.KerPow

variable {X X' Y B : Scheme.{0}} {L : LB X} {K J : Type} [Fintype K] [Fintype J]

/- English proof (translation)
Establish `le : ∀ (j : K × J → L.ι) (y : Y), y ∈ LB.wchart L (K` using `K × J) (fun q => ψ q.1 ≫ F q.2) j → y ∈ LB.wchart (LB.LinComb L F (fun _ => 1)) ψ (fun k i => j (k, i)) := fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy (k, i)`. Use `gen_transfer (M := LB.LinComb (LB.LinComb L F (fun _ => 1)) ψ ε) (M' := LB.LinComb L (K := K × J) (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1)) (fun j k i => j (k, i)) (fun j y hy => le j y hy) (fun j j' y hj hj' => ?_) H` and prove the remaining obligations. Use `(gm_linComb L (K := K × J) (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1) (𝟙 Y) y j j' hj hj').trans (Eq.trans ?_ (gm_linComb (LB.LinComb L F (fun _ => 1)) ψ ε (𝟙 Y) y _ _ (le j y hj) (le j' y hj')).symm)` and prove the remaining obligations. Rewrite using `[Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Use `Eq.trans ?_ (congrArg (· ^ ε k) (gm_linComb L F (fun _ => 1) (𝟙 Y ≫ ψ k) y (fun i => j (k, i)) (fun i => j' (k, i)) (Set.mem_iInter.1 (le j y hj) k) (Set.mem_iInter.1 (le j' y hj') k)).symm)` and prove the remaining obligations. Simplify using `only [zpow_one, Category.assoc, Finset.prod_zpow]`.
-/
theorem hasGen_flat (F : J → (X' ⟶ X)) {ψ : K → (Y ⟶ X')} {ε : K → ℤ}
    (H : HasGen (LB.LinComb L F (fun _ => 1)) ψ ε) :
    HasGen L (K := K × J) (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1) := by
  have le : ∀ (j : K × J → L.ι) (y : Y), y ∈ LB.wchart L (K := K × J) (fun q => ψ q.1 ≫ F q.2) j →
      y ∈ LB.wchart (LB.LinComb L F (fun _ => 1)) ψ (fun k i => j (k, i)) := fun j y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy (k, i)
  refine gen_transfer (M := LB.LinComb (LB.LinComb L F (fun _ => 1)) ψ ε)
    (M' := LB.LinComb L (K := K × J) (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1))
    (fun j k i => j (k, i)) (fun j y hy => le j y hy) (fun j j' y hj hj' => ?_) H
  refine (gm_linComb L (K := K × J) (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1) (𝟙 Y) y j j' hj hj').trans
    (Eq.trans ?_ (gm_linComb (LB.LinComb L F (fun _ => 1)) ψ ε (𝟙 Y) y _ _ (le j y hj) (le j' y hj')).symm)
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => ?_
  refine Eq.trans ?_ (congrArg (· ^ ε k) (gm_linComb L F (fun _ => 1) (𝟙 Y ≫ ψ k) y (fun i => j (k, i))
    (fun i => j' (k, i)) (Set.mem_iInter.1 (le j y hj) k) (Set.mem_iInter.1 (le j' y hj') k)).symm)
  simp only [zpow_one, Category.assoc, Finset.prod_zpow]

/- English proof (translation)
Use `⟨⟨fun i => res (le_inf le_rfl (fun y _ => h y) : M.U i ≤ M.U i ⊓ M.U i₀) (M.g i i₀)⟩, fun i j => ?_⟩` and prove the remaining obligations. Use `LB.res_cocycle hM i j i₀ (W := M.U i ⊓ M.U j) le_rfl (le_inf inf_le_right fun y _ => h y) (le_inf inf_le_left fun y _ => h y)` as an intermediate fact. Use `(LB.res_res _ _ _).trans (this.symm.trans (congrArg₂ (· * ·) ?_ (LB.res_res _ _ _).symm))` and prove the remaining obligations. Conclude with `unit_ext fun y hy => gm_res _ y _ hy _`.
-/
theorem gen_of_chart {M : LB Y} (hM : M.IsLB) (i₀ : M.ι) (h : ∀ y, y ∈ M.U i₀) : ∃ t : LB.Gen M, t.IsGen := by
  refine ⟨⟨fun i => res (le_inf le_rfl (fun y _ => h y) : M.U i ≤ M.U i ⊓ M.U i₀) (M.g i i₀)⟩, fun i j => ?_⟩
  have := LB.res_cocycle hM i j i₀ (W := M.U i ⊓ M.U j) le_rfl (le_inf inf_le_right fun y _ => h y)
    (le_inf inf_le_left fun y _ => h y)
  refine (LB.res_res _ _ _).trans (this.symm.trans (congrArg₂ (· * ·) ?_ (LB.res_res _ _ _).symm))
  exact unit_ext fun y hy => gm_res _ y _ hy _

/- English proof (translation)
Introduce `p`. Use `choose j hj using fun k => exists_chart hL (b k p)`. Use `⟨LB.wchart L b j, Set.mem_iInter.2 hj, gen_of_chart (LB.isLB_linComb hL _ _) j fun y => ?_⟩` and prove the remaining obligations. Conclude with `Set.mem_iInter.2 fun k => Set.mem_iInter.1 y.2 k`.
-/
theorem locGen_base (hL : L.IsLB) (π : Y ⟶ B) (b : K → (B ⟶ X)) (ε : K → ℤ) :
    LocGen L π (fun k => π ≫ b k) ε := by
  intro p
  choose j hj using fun k => exists_chart hL (b k p)
  refine ⟨LB.wchart L b j, Set.mem_iInter.2 hj, gen_of_chart (LB.isLB_linComb hL _ _) j fun y => ?_⟩
  exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 y.2 k

/- English proof (translation)
Introduce `p`. Take `⟨V, hV, t⟩` from `H p`. Conclude with `⟨V, hV, (hasGen_flat F t).pull (𝟙 _) fun q => by rw [Category.id_comp, Category.assoc]⟩`.
-/
theorem locGen_flat (F : J → (X' ⟶ X)) {π : Y ⟶ B} {ψ : K → (Y ⟶ X')} {ε : K → ℤ}
    (H : LocGen (LB.LinComb L F (fun _ => 1)) π ψ ε) :
    LocGen L (K := K × J) π (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1) := by
  intro p
  obtain ⟨V, hV, t⟩ := H p
  exact ⟨V, hV, (hasGen_flat F t).pull (𝟙 _) fun q => by rw [Category.id_comp, Category.assoc]⟩

end GlobalTheory.BoxKernel

namespace GlobalTheory

open KerPow BoxKernel in

/- English proof (translation)
Introduce `S G' G _ _ _ _ j p L hL hK R _ t x hx`. Establish `H : LocGen (boxLB L p.pr) (K` using `Fin 2) (fst (Over.mk t) G').left ![(translPt G' x).left, (snd (Over.mk t) G').left] ![1, -1] := (locGen_iff _ _ _).1 hx`. Use `clear hx`. Generalize the expression as in `Over.mk t = T at x H`. Use `p.lim.hom_ext fun ⟨i⟩ => ?_` and prove the remaining obligations.

Use `p.hom` as an intermediate fact. Use `show x ≫ p.pr i = (1 : T ⟶ G') ≫ p.pr i`. Rewrite using `[MonObj.one_comp]`. Set `u : G ⟶ G'` to `p.lim.lift (Fan.mk G fun i' => if i' = i then 𝟙 G else 1)`. Establish `hu : ∀ i', u ≫ p.pr i' = if i' = i then 𝟙 G else 1` using `fun i' => p.lim.fac _ ⟨i'⟩`.

Set `a : Fin 2 → (T ⊗ G ⟶ G')` to `![(fst T G ≫ x) * (snd T G ≫ u), snd T G ≫ u]`. Establish `H₁` using `H.baseChange (π' := (fst T G).left) (T ◁ u).left (𝟙 _) ((congrArg (fun q => q.left) (whiskerLeft_fst T u)).trans (Category.comp_id _).symm) (φ' := fun k => (a k).left) (fun k => by fin_cases k`. Use `congrArg (fun q => q.left) (show T ◁ u ≫ ((fst T G' ≫ x) * snd T G') = (fst T G ≫ x) * (snd T G ≫ u) from ?_)` and prove the remaining obligations. Rewrite using `[MonObj.comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd]`. Conclude with `congrArg (fun q => q.left) (whiskerLeft_snd T u))`.

Set `b : Fin 2 × Fin j → (T ⟶ G)` to `fun q => ![x ≫ p.pr q.2, 1] q.1`. Establish `H₂` using `locGen_base hL (fst T G).left (fun q => (b q).left) (fun q => if q.2 = i then 0 else (![1, -1] : Fin 2 → ℤ) q.1)`. Use `eq_one_of_locGen hK _ ((locGen_flat _ H₁).comb hL H₂ fun U _ h => ?_)` and prove the remaining obligations. Establish `e₀ : ∀ k i', i' ≠ i → (a k).left ≫ (p.pr i').left = (fst T G).left ≫ (b (k, i')).left` using `fun k i' hi => by`. Use `congrArg (fun q => q.left) (show a k ≫ p.pr i' = fst T G ≫ b (k, i') from ?_)` and prove the remaining obligations.

Use `fin_cases k`. Use `show ((fst T G ≫ x) * (snd T G ≫ u)) ≫ p.pr i' = fst T G ≫ x ≫ p.pr i'`. Rewrite using `[MonObj.mul_comp, Category.assoc, Category.assoc, hu, if_neg hi, MonObj.comp_one, _root_.mul_one]`. Use `show (snd T G ≫ u) ≫ p.pr i' = fst T G ≫ 1`. Rewrite using `[Category.assoc, hu, if_neg hi, MonObj.comp_one, MonObj.comp_one]`.

Establish `e₁ : ∀ k, (a k).left ≫ (p.pr i).left = (![(translPt G (x ≫ p.pr i)).left, (snd T G).left] : Fin 2 → _) k` using `fun k => by fin_cases k`. Use `congrArg (fun q => q.left) (show ((fst T G ≫ x) * (snd T G ≫ u)) ≫ p.pr i = (fst T G ≫ x ≫ p.pr i) * snd T G from ?_)` and prove the remaining obligations. Rewrite using `[MonObj.mul_comp, Category.assoc, Category.assoc, hu, if_pos rfl, Category.comp_id]`. Use `congrArg (fun q => q.left) (show (snd T G ≫ u) ≫ p.pr i = snd T G from ?_)` and prove the remaining obligations. Rewrite using `[Category.assoc, hu, if_pos rfl, Category.comp_id]`.

Rewrite using `[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_single i (fun i' _ hi => ?_) (fun hi => (hi (Finset.mem_univ _)).elim)]`. Simplify using `only [if_true, zpow_zero, inv_one, _root_.mul_one, e₁]`. Simplify using `only [if_neg hi, e₀ k i' hi, mul_inv_cancel]`.
-/
theorem kTriv_boxLB : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left), L.IsLB → KTriv G L → KTriv G' (boxLB L p.pr) := by
  intro S G' G _ _ _ _ j p L hL hK R _ t x hx
  classical
  have H : LocGen (boxLB L p.pr) (K := Fin 2) (fst (Over.mk t) G').left
      ![(translPt G' x).left, (snd (Over.mk t) G').left] ![1, -1] := (locGen_iff _ _ _).1 hx
  clear hx
  generalize Over.mk t = T at x H
  refine p.lim.hom_ext fun ⟨i⟩ => ?_
  have := p.hom
  show x ≫ p.pr i = (1 : T ⟶ G') ≫ p.pr i
  rw [MonObj.one_comp]
  let u : G ⟶ G' := p.lim.lift (Fan.mk G fun i' => if i' = i then 𝟙 G else 1)
  have hu : ∀ i', u ≫ p.pr i' = if i' = i then 𝟙 G else 1 := fun i' => p.lim.fac _ ⟨i'⟩
  let a : Fin 2 → (T ⊗ G ⟶ G') := ![(fst T G ≫ x) * (snd T G ≫ u), snd T G ≫ u]
  have H₁ := H.baseChange (π' := (fst T G).left) (T ◁ u).left (𝟙 _)
    ((congrArg (fun q => q.left) (whiskerLeft_fst T u)).trans (Category.comp_id _).symm)
    (φ' := fun k => (a k).left) (fun k => by
      fin_cases k
      · refine congrArg (fun q => q.left) (show T ◁ u ≫ ((fst T G' ≫ x) * snd T G') = (fst T G ≫ x) * (snd T G ≫ u) from ?_)
        rw [MonObj.comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd]
      · exact congrArg (fun q => q.left) (whiskerLeft_snd T u))
  let b : Fin 2 × Fin j → (T ⟶ G) := fun q => ![x ≫ p.pr q.2, 1] q.1
  have H₂ := locGen_base hL (fst T G).left (fun q => (b q).left)
    (fun q => if q.2 = i then 0 else (![1, -1] : Fin 2 → ℤ) q.1)
  refine eq_one_of_locGen hK _ ((locGen_flat _ H₁).comb hL H₂ fun U _ h => ?_)
  have e₀ : ∀ k i', i' ≠ i → (a k).left ≫ (p.pr i').left = (fst T G).left ≫ (b (k, i')).left := fun k i' hi => by
    refine congrArg (fun q => q.left) (show a k ≫ p.pr i' = fst T G ≫ b (k, i') from ?_)
    fin_cases k
    · show ((fst T G ≫ x) * (snd T G ≫ u)) ≫ p.pr i' = fst T G ≫ x ≫ p.pr i'
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hu, if_neg hi, MonObj.comp_one, _root_.mul_one]
    · show (snd T G ≫ u) ≫ p.pr i' = fst T G ≫ 1
      rw [Category.assoc, hu, if_neg hi, MonObj.comp_one, MonObj.comp_one]
  have e₁ : ∀ k, (a k).left ≫ (p.pr i).left =
      (![(translPt G (x ≫ p.pr i)).left, (snd T G).left] : Fin 2 → _) k := fun k => by
    fin_cases k
    · refine congrArg (fun q => q.left)
        (show ((fst T G ≫ x) * (snd T G ≫ u)) ≫ p.pr i = (fst T G ≫ x ≫ p.pr i) * snd T G from ?_)
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hu, if_pos rfl, Category.comp_id]
    · refine congrArg (fun q => q.left) (show (snd T G ≫ u) ≫ p.pr i = snd T G from ?_)
      rw [Category.assoc, hu, if_pos rfl, Category.comp_id]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_eq_single i (fun i' _ hi => ?_) (fun hi => (hi (Finset.mem_univ _)).elim)]
  · simp only [if_true, zpow_zero, inv_one, _root_.mul_one, e₁]
  · simp only [if_neg hi, e₀ k i' hi, mul_inv_cancel]

end GlobalTheory
