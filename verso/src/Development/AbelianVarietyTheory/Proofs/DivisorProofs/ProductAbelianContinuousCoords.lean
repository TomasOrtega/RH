import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqAndWeilIsOfIsHolTo
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.WeilIsExpRiemannForm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix Filter Topology MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open scoped ContDiff
open scoped CategoryTheory.Obj MonObj

namespace GlobalTheory.PolFrame

open GlobalTheory.ArchMetricCompare (val_iso val_g_self le_pull_iff val_pull_g ex_add_period)
open GlobalTheory.WeilExp (le_wchart_iff)

variable {X Y : Scheme.{0}}

/- English proof (translation)
The claim follows from `(exists_chart hL (x (default : PrimeSpectrum ℂ))).imp fun _ h => (top_le_preimage_iff_mem _ _).2 h`.
-/
theorem exists_chart_pt {L : LB X} (hL : L.IsLB) (x : Sp ℂ ⟶ X) : ∃ i, ⊤ ≤ x ⁻¹ᵁ L.U i :=
  (exists_chart hL (x (default : PrimeSpectrum ℂ))).imp fun _ h => (top_le_preimage_iff_mem _ _).2 h

/- English proof (translation)
Use `(valAt'_units_prod p h _ _).trans (Finset.prod_congr rfl fun k _ => ?_)` and prove the remaining obligations. Use `(valAt'_zpow p h _ _).trans ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `(valAt'_res p _ _ h).trans (valAt'_comp p (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val)`.
-/
theorem val_linComb (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (p : Sp ℂ ⟶ Y)
    (j j' : K → L.ι) (h : ⊤ ≤ p ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) :
    valAt' p (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j').val =
      ∏ k, valAt' (p ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k := by
  refine (valAt'_units_prod p h _ _).trans (Finset.prod_congr rfl fun k _ => ?_)
  refine (valAt'_zpow p h _ _).trans ?_
  congr 1
  exact (valAt'_res p _ _ h).trans (valAt'_comp p (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val)

/- English proof (translation)
Use `choose a ha using fun q => exists_chart_pt hN (c q)`. Establish `key : ∀ j i q, ⊤ ≤ c q ⁻¹ᵁ N'.U j → ⊤ ≤ c q ⁻¹ᵁ N.U i → valAt' (c q) (N'.U j ⊓ N.U (a q)) (w.s (j, a q)).val * G (a q) q = valAt' (c q) (N'.U j ⊓ N.U i) (w.s (j, i)).val * G i q` using `fun j i q hj hi => by`. Establish `hm` using `(top_le_preimage_inf _ _ _).2 ⟨hi, ha q⟩`. Use `valAt'_unit_ne_zero _ hm (N.g i (a q))` as an intermediate fact. Rewrite using `[val_iso hw _ j j i (a q) hj hj hi (ha q), val_g_self hN' _ j hj, h₃ i (a q) q hm]`.

Clear the denominators using the available nonvanishing facts. Use `⟨fun j q => valAt' (c q) (N'.U j ⊓ N.U (a q)) (w.s (j, a q)).val * G (a q) q, fun j q hj => ?_, fun j q hj => ?_, fun j j' q hq => ?_, key⟩` and prove the remaining obligations. Establish `H` using `hc (N'.U j ⊓ N.U (a q)) (w.s (j, a q)).val`. Establish `hn` using `H.1.mem_nhds (x := q) ⟨trivial, (top_le_preimage_inf _ _ _).2 ⟨hj, ha q⟩⟩`. Use `((H.2.differentiableAt hn).continuousAt.mul (h₁ _ q (ha q))).congr ?_` and prove the remaining obligations.

Use `filter_upwards [hn] with y hy`. Conclude with `(key j (a q) y (top_le_preimage_mono _ inf_le_left hy.2) (top_le_preimage_mono _ inf_le_right hy.2)).symm`. Conclude with `mul_ne_zero (valAt'_unit_ne_zero _ ((top_le_preimage_inf _ _ _).2 ⟨hj, ha q⟩) _) (h₂ _ q (ha q))`. Take `⟨hj, hj'⟩` from `(top_le_preimage_inf _ _ _).1 hq beta_reduce`. Rewrite using `[val_iso hw _ j j' (a q) (a q) hj hj' (ha q) (ha q), val_g_self hN _ _ (ha q), inv_one, _root_.mul_one, _root_.mul_assoc]`.
-/
theorem exists_frame_of_iso {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {N N' : LB Y} (hN : N.IsLB)
    (hN' : N'.IsLB) {w : LB.Iso N N'} (hw : w.IsGen) {c : V → (Sp ℂ ⟶ Y)} (hc : IsHolTo Set.univ c)
    (G : N.ι → V → ℂ) (h₁ : ∀ i q, ⊤ ≤ c q ⁻¹ᵁ N.U i → ContinuousAt (G i) q)
    (h₂ : ∀ i q, ⊤ ≤ c q ⁻¹ᵁ N.U i → G i q ≠ 0)
    (h₃ : ∀ i j q, ⊤ ≤ c q ⁻¹ᵁ (N.U i ⊓ N.U j) → G i q = valAt' (c q) (N.U i ⊓ N.U j) (N.g i j).val * G j q) :
    ∃ F : N'.ι → V → ℂ, (∀ j q, ⊤ ≤ c q ⁻¹ᵁ N'.U j → ContinuousAt (F j) q) ∧
      (∀ j q, ⊤ ≤ c q ⁻¹ᵁ N'.U j → F j q ≠ 0) ∧
      (∀ j j' q, ⊤ ≤ c q ⁻¹ᵁ (N'.U j ⊓ N'.U j') →
        F j q = valAt' (c q) (N'.U j ⊓ N'.U j') (N'.g j j').val * F j' q) ∧
      ∀ j i q, ⊤ ≤ c q ⁻¹ᵁ N'.U j → ⊤ ≤ c q ⁻¹ᵁ N.U i →
        F j q = valAt' (c q) (N'.U j ⊓ N.U i) (w.s (j, i)).val * G i q := by
  choose a ha using fun q => exists_chart_pt hN (c q)
  have key : ∀ j i q, ⊤ ≤ c q ⁻¹ᵁ N'.U j → ⊤ ≤ c q ⁻¹ᵁ N.U i →
      valAt' (c q) (N'.U j ⊓ N.U (a q)) (w.s (j, a q)).val * G (a q) q =
        valAt' (c q) (N'.U j ⊓ N.U i) (w.s (j, i)).val * G i q := fun j i q hj hi => by
    have hm := (top_le_preimage_inf _ _ _).2 ⟨hi, ha q⟩
    have := valAt'_unit_ne_zero _ hm (N.g i (a q))
    rw [val_iso hw _ j j i (a q) hj hj hi (ha q), val_g_self hN' _ j hj, h₃ i (a q) q hm]
    field_simp
  refine ⟨fun j q => valAt' (c q) (N'.U j ⊓ N.U (a q)) (w.s (j, a q)).val * G (a q) q, fun j q hj => ?_,
    fun j q hj => ?_, fun j j' q hq => ?_, key⟩
  · have H := hc (N'.U j ⊓ N.U (a q)) (w.s (j, a q)).val
    have hn := H.1.mem_nhds (x := q) ⟨trivial, (top_le_preimage_inf _ _ _).2 ⟨hj, ha q⟩⟩
    refine ((H.2.differentiableAt hn).continuousAt.mul (h₁ _ q (ha q))).congr ?_
    filter_upwards [hn] with y hy
    exact (key j (a q) y (top_le_preimage_mono _ inf_le_left hy.2) (top_le_preimage_mono _ inf_le_right hy.2)).symm
  · exact mul_ne_zero (valAt'_unit_ne_zero _ ((top_le_preimage_inf _ _ _).2 ⟨hj, ha q⟩) _) (h₂ _ q (ha q))
  · obtain ⟨hj, hj'⟩ := (top_le_preimage_inf _ _ _).1 hq
    beta_reduce
    rw [val_iso hw _ j j' (a q) (a q) hj hj' (ha q) (ha q), val_g_self hN _ _ (ha q), inv_one, _root_.mul_one,
      _root_.mul_assoc]

section Square

variable {B : Over (Sp ℂ)} [GrpObj B] {L : LB B.left} {g : ℕ} (u : HolUnif B L g)

def sqMaps (B : Over (Sp ℂ)) [GrpObj B] : Fin 4 → ((B ⊗ B).left ⟶ B.left) :=
  ![(fst B B * snd B B).left, (fst B B).left, (snd B B).left, (1 : B ⊗ B ⟶ B).left]

def sqPts (q : (Fin g → ℂ) × (Fin g → ℂ)) : Fin 4 → Fin g → ℂ := ![q.1 + q.2, q.1, q.2, 0]

def sqEx (q : (Fin g → ℂ) × (Fin g → ℂ)) : Sp ℂ ⟶ (B ⊗ B).left := (lift (u.ex q.1) (u.ex q.2)).left

/- English proof (translation)
Establish `e : ∀ f : B ⊗ B ⟶ B, sqEx u q ≫ f.left = (lift (u.ex q.1) (u.ex q.2) ≫ f).left` using `fun f => rfl`. Use `fin_cases k`. Use `(e _).trans ?_` and prove the remaining obligations. Rewrite using `[MonObj.comp_mul, lift_fst, lift_snd, ← u.ex_add]`. Both sides reduce to the same expression.

Conclude with `(e _).trans (congrArg Over.Hom.left (lift_fst _ _))`. Conclude with `(e _).trans (congrArg Over.Hom.left (lift_snd _ _))`. Use `(e _).trans ?_` and prove the remaining obligations. Rewrite using `[MonObj.comp_one, ← (u.ker 0).2 (zero_mem _)]`. Both sides reduce to the same expression.
-/
theorem sqEx_sqMaps (q : (Fin g → ℂ) × (Fin g → ℂ)) (k : Fin 4) :
    sqEx u q ≫ sqMaps B k = (u.ex (sqPts q k)).left := by
  have e : ∀ f : B ⊗ B ⟶ B, sqEx u q ≫ f.left = (lift (u.ex q.1) (u.ex q.2) ≫ f).left := fun f => rfl
  fin_cases k
  · refine (e _).trans ?_
    rw [MonObj.comp_mul, lift_fst, lift_snd, ← u.ex_add]
    rfl
  · exact (e _).trans (congrArg Over.Hom.left (lift_fst _ _))
  · exact (e _).trans (congrArg Over.Hom.left (lift_snd _ _))
  · refine (e _).trans ?_
    rw [MonObj.comp_one, ← (u.ker 0).2 (zero_mem _)]
    rfl

/- English proof (translation)
Introduce `U s`. Simplify using `only [Set.mem_univ, true_and]`. Conclude with `⟨(u.hol U s).1.preimage hf.continuous, (u.hol U s).2.comp hf.differentiableOn fun _ h => h⟩`.
-/
theorem isHolTo_ex {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : V → Fin g → ℂ}
    (hf : Differentiable ℂ f) : IsHolTo Set.univ fun q => (show Sp ℂ ⟶ B.left from (u.ex (f q)).left) := by
  intro U s
  simp only [Set.mem_univ, true_and]
  exact ⟨(u.hol U s).1.preimage hf.continuous, (u.hol U s).2.comp hf.differentiableOn fun _ h => h⟩

/- English proof (translation)
Use `HolTorsion.isHolTo_of_isPullback (p := (fst B B).left) (q := (snd B B).left) (IsPullback.of_hasPullback B.hom B.hom) ?_ ?_` and prove the remaining obligations. Conclude with `HolTorsion.isHolTo_congr (isHolTo_ex u differentiable_fst) fun q _ => sqEx_sqMaps u q 1`. Conclude with `HolTorsion.isHolTo_congr (isHolTo_ex u differentiable_snd) fun q _ => sqEx_sqMaps u q 2`.
-/
theorem isHolTo_sqEx : IsHolTo Set.univ (sqEx u) := by
  refine HolTorsion.isHolTo_of_isPullback (p := (fst B B).left) (q := (snd B B).left)
    (IsPullback.of_hasPullback B.hom B.hom) ?_ ?_
  · exact HolTorsion.isHolTo_congr (isHolTo_ex u differentiable_fst) fun q _ => sqEx_sqMaps u q 1
  · exact HolTorsion.isHolTo_congr (isHolTo_ex u differentiable_snd) fun q _ => sqEx_sqMaps u q 2

/- English proof (translation)
The claim follows from `(le_wchart_iff L _ j _).trans (forall_congr' fun k => by rw [sqEx_sqMaps])`.
-/
theorem le_sq_iff (ε : Fin 4 → ℤ) (j : Fin 4 → L.ι) (q : (Fin g → ℂ) × (Fin g → ℂ)) :
    ⊤ ≤ sqEx u q ⁻¹ᵁ (LB.LinComb L (sqMaps B) ε).U j ↔ ∀ k, ⊤ ≤ (u.ex (sqPts q k)).left ⁻¹ᵁ L.U (j k) :=
  (le_wchart_iff L _ j _).trans (forall_congr' fun k => by rw [sqEx_sqMaps])

def sqFr (ε : Fin 4 → ℤ) (j : Fin 4 → L.ι) (q : (Fin g → ℂ) × (Fin g → ℂ)) : ℂ :=
  ∏ k, u.fr (j k) (sqPts q k) ^ ε k

/- English proof (translation)
Use `tendsto_finset_prod _ fun k _ => ?_` and prove the remaining obligations. Establish `hk` using `(le_sq_iff u ε j q).1 h k`. Establish `hp : Continuous fun q : (Fin g → ℂ) × (Fin g → ℂ) => sqPts q k` using `by fin_cases k exacts [continuous_fst.add continuous_snd, continuous_fst, continuous_snd, continuous_const]`. Conclude with `(ContinuousAt.comp (f := fun q => sqPts q k) (x := q) ((u.fr_hol (j k)).differentiableAt ((u.hol _ 0).1.mem_nhds hk)).continuousAt hp.continuousAt).zpow₀ _ (.inl (u.fr_ne _ _ hk))`.
-/
theorem continuousAt_sqFr (ε : Fin 4 → ℤ) (j : Fin 4 → L.ι) (q : (Fin g → ℂ) × (Fin g → ℂ))
    (h : ⊤ ≤ sqEx u q ⁻¹ᵁ (LB.LinComb L (sqMaps B) ε).U j) : ContinuousAt (sqFr u ε j) q := by
  refine tendsto_finset_prod _ fun k _ => ?_
  have hk := (le_sq_iff u ε j q).1 h k
  have hp : Continuous fun q : (Fin g → ℂ) × (Fin g → ℂ) => sqPts q k := by
    fin_cases k
    exacts [continuous_fst.add continuous_snd, continuous_fst, continuous_snd, continuous_const]
  exact (ContinuousAt.comp (f := fun q => sqPts q k) (x := q)
    ((u.fr_hol (j k)).differentiableAt ((u.hol _ 0).1.mem_nhds hk)).continuousAt hp.continuousAt).zpow₀ _
    (.inl (u.fr_ne _ _ hk))

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (u.fr_ne _ _ ((le_sq_iff u ε j q).1 h k))`.
-/
theorem sqFr_ne_zero (ε : Fin 4 → ℤ) (j : Fin 4 → L.ι) (q : (Fin g → ℂ) × (Fin g → ℂ))
    (h : ⊤ ≤ sqEx u q ⁻¹ᵁ (LB.LinComb L (sqMaps B) ε).U j) : sqFr u ε j q ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (u.fr_ne _ _ ((le_sq_iff u ε j q).1 h k))

/- English proof (translation)
Take `⟨hi, hj⟩` from `(top_le_preimage_inf _ _ _).1 h`. Use `Eq.trans ?_ (congrArg (· * _) (val_linComb L _ ε _ i j h).symm)` and prove the remaining obligations. Rewrite using `[sqFr, sqFr, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[sqEx_sqMaps, ← mul_zpow, u.fr_compat (i k) (j k) _ ((top_le_preimage_inf _ _ _).2 ⟨(le_sq_iff u ε i q).1 hi k, (le_sq_iff u ε j q).1 hj k⟩)]`.
-/
theorem sqFr_compat (ε : Fin 4 → ℤ) (i j : Fin 4 → L.ι) (q : (Fin g → ℂ) × (Fin g → ℂ))
    (h : ⊤ ≤ sqEx u q ⁻¹ᵁ ((LB.LinComb L (sqMaps B) ε).U i ⊓ (LB.LinComb L (sqMaps B) ε).U j)) :
    sqFr u ε i q = valAt' (sqEx u q) ((LB.LinComb L (sqMaps B) ε).U i ⊓ (LB.LinComb L (sqMaps B) ε).U j)
      ((LB.LinComb L (sqMaps B) ε).g i j).val * sqFr u ε j q := by
  obtain ⟨hi, hj⟩ := (top_le_preimage_inf _ _ _).1 h
  refine Eq.trans ?_ (congrArg (· * _) (val_linComb L _ ε _ i j h).symm)
  rw [sqFr, sqFr, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [sqEx_sqMaps, ← mul_zpow, u.fr_compat (i k) (j k) _
    ((top_le_preimage_inf _ _ _).2 ⟨(le_sq_iff u ε i q).1 hi k, (le_sq_iff u ε j q).1 hj k⟩)]

variable {u} in

/- English proof (translation)
Establish `hk` using `(le_sq_iff u _ j _).1 h`. Establish `hχ : χ l ≠ 0` using `fun e => by simpa [e] using hAH.2.2.1 l`. Establish `e₀ : u.fr (j 0) (z + w) = _` using `hAH.2.2.2 l _ _ (hk 0)`. Establish `e₁ : u.fr (j 1) z = _` using `hAH.2.2.2 l _ _ (hk 1)`. Establish `e₂ : u.fr (j 2) w = _` using `hAH.2.2.2 l _ _ (hk 2)`.

Establish `v : ∀ a b : Fin g → ℂ, sqFr u ![1, -1, -1, 1] j (a, b) = u.fr (j 0) (a + b) * (u.fr (j 1) a)⁻¹ * (u.fr (j 2) b)⁻¹ * u.fr (j 3) 0` using `fun a b => by`. Simplify using `[sqFr, sqPts, Fin.prod_univ_four]`. Simplify using `only [sqPts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, add_dotProduct, mul_add, Complex.exp_add] at e₀ e₁ e₂`. Rewrite using `[v, v, v, add_right_comm z, ← add_assoc z, HermFrame.form, HermFrame.form]`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[e₀, e₁]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e₀, e₂]`. Clear the denominators using the available nonvanishing facts.
-/
theorem sqFr_period {H : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hAH : u.IsAH H χ) (l : u.Λ)
    (j : Fin 4 → L.ι) (z w : Fin g → ℂ)
    (h : ⊤ ≤ sqEx u (z, w) ⁻¹ᵁ (LB.LinComb L (sqMaps B) ![1, -1, -1, 1]).U j) :
    sqFr u ![1, -1, -1, 1] j (z, w) =
        Complex.exp (Real.pi * HermFrame.form H w l) * sqFr u ![1, -1, -1, 1] j (z + l, w) ∧
      sqFr u ![1, -1, -1, 1] j (z, w) =
        Complex.exp (Real.pi * HermFrame.form H z l) * sqFr u ![1, -1, -1, 1] j (z, w + l) := by
  have hk := (le_sq_iff u _ j _).1 h
  have hχ : χ l ≠ 0 := fun e => by simpa [e] using hAH.2.2.1 l
  have e₀ : u.fr (j 0) (z + w) = _ := hAH.2.2.2 l _ _ (hk 0)
  have e₁ : u.fr (j 1) z = _ := hAH.2.2.2 l _ _ (hk 1)
  have e₂ : u.fr (j 2) w = _ := hAH.2.2.2 l _ _ (hk 2)
  have v : ∀ a b : Fin g → ℂ, sqFr u ![1, -1, -1, 1] j (a, b) =
      u.fr (j 0) (a + b) * (u.fr (j 1) a)⁻¹ * (u.fr (j 2) b)⁻¹ * u.fr (j 3) 0 := fun a b => by
    simp [sqFr, sqPts, Fin.prod_univ_four]
  simp only [sqPts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, add_dotProduct, mul_add,
    Complex.exp_add] at e₀ e₁ e₂
  rw [v, v, v, add_right_comm z, ← add_assoc z, HermFrame.form, HermFrame.form]
  constructor
  · rw [e₀, e₁]
    field_simp
  · rw [e₀, e₂]
    field_simp

end Square

/- English proof (translation)
Introduce `S P y d M hM hc x hx`. Establish `hx' : ∀ q, x q = sqEx d.u q ≫ sqMap d.isPull.1.w` using `fun q => by`. Use `Limits.pullback.hom_ext ((hx q).1.trans ?_) ((hx q).2.trans ?_)` and prove the remaining obligations. Rewrite using `[Category.assoc, sqMap, Limits.pullback.lift_fst, ← Category.assoc]`. Conclude with `congrArg (· ≫ d.φ) (sqEx_sqMaps d.u q 1).symm`.

Rewrite using `[Category.assoc, sqMap, Limits.pullback.lift_snd, ← Category.assoc]`. Conclude with `congrArg (· ≫ d.φ) (sqEx_sqMaps d.u q 2).symm`. Establish `hN` using `LB.isLB_linComb d.isLB (sqMaps d.B) ![1, -1, -1, 1]`. Establish `hN'` using `pull_isLB hM (sqMap d.isPull.1.w)`. Take `⟨w, hw⟩` from `(CechPic.cls_eq_iff hN hN').1 (by`.

Rewrite using `[CechPic.cls_pull hM, hc, d.pol, CechPic.cls_linComb d.isLB, Fin.sum_univ_four]`. Simplify using `only [CechPic.lam, sqMaps, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul, sub_eq_add_neg])`. Take `⟨F, h₁, h₂, h₃, h₄⟩` from `exists_frame_of_iso hN hN' hw (isHolTo_sqEx d.u) (sqFr d.u _) (continuousAt_sqFr d.u _) (sqFr_ne_zero d.u _) (sqFr_compat d.u _)`. Establish `m : ∀ i q, ⊤ ≤ x q ⁻¹ᵁ M.U i → ⊤ ≤ sqEx d.u q ⁻¹ᵁ (M.pull (sqMap d.isPull.1.w)).U fun _ => i` using `fun i q h => (le_pull_iff _ _ _ _).2 (hx' q ▸ h)`. Use `⟨fun i => F fun _ => i, fun i q h => (h₁ _ q (m i q h)).continuousWithinAt, fun i q h => h₂ _ q (m i q h), fun i j q h => ?_, fun l i z v h => ?_⟩` and prove the remaining obligations.

Take `⟨hi, hj⟩` from `(top_le_preimage_inf _ _ _).1 h`. Establish `hm` using `(top_le_preimage_inf _ _ _).2 ⟨m i q hi, m j q hj⟩`. Use `beta_reduce`. Rewrite using `[h₃ _ _ q hm, val_pull_g _ _ _ _ _ hm, hx' q]`. Take `⟨j, hj⟩` from `exists_chart_pt hN (sqEx d.u (z, v))`.

Establish `e₁ : sqEx d.u (z + l, v) = sqEx d.u (z, v)` using `by simp only [sqEx, ex_add_period]`. Establish `e₂ : sqEx d.u (z, v + l) = sqEx d.u (z, v)` using `by simp only [sqEx, ex_add_period]`. Establish `hi` using `m i _ h`. Take `⟨p₁, p₂⟩` from `sqFr_period d.isAH l j z v hj`. Use `beta_reduce`.

Rewrite using `[h₄ _ j _ hi hj, h₄ (fun _ => i) j (z + l, v) (by rw [e₁]; exact hi) (by rw [e₁]; exact hj), h₄ (fun _ => i) j (z, v + l) (by rw [e₂]; exact hi) (by rw [e₂]; exact hj), e₁, e₂]`. Conclude with `⟨(congrArg _ p₁).trans (mul_left_comm _ _ _), (congrArg _ p₂).trans (mul_left_comm _ _ _)⟩`.
-/
theorem exists_frame_sq : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y) (M : LB (P.A ⊗ P.A).left) (hM : M.IsLB), CechPic.cls M hM = P.c → ∀ x : (Fin P.g → ℂ) × (Fin P.g → ℂ) → (Sp ℂ ⟶ (P.A ⊗ P.A).left), (∀ q, x q ≫ (fst P.A P.A).left = (d.u.ex q.1).left ≫ d.φ ∧ x q ≫ (snd P.A P.A).left = (d.u.ex q.2).left ≫ d.φ) → ∃ F : M.ι → (Fin P.g → ℂ) × (Fin P.g → ℂ) → ℂ, (∀ i, ContinuousOn (F i) {q | ⊤ ≤ x q ⁻¹ᵁ M.U i}) ∧ (∀ i q, ⊤ ≤ x q ⁻¹ᵁ M.U i → F i q ≠ 0) ∧ (∀ i j q, ⊤ ≤ x q ⁻¹ᵁ (M.U i ⊓ M.U j) → F i q = valAt' (x q) (M.U i ⊓ M.U j) (M.g i j).val * F j q) ∧ ∀ (l : d.u.Λ) (i : M.ι) (z w : Fin P.g → ℂ), ⊤ ≤ x (z, w) ⁻¹ᵁ M.U i → F i (z, w) = Complex.exp (Real.pi * HermFrame.form d.H w l) * F i (z + l, w) ∧ F i (z, w) = Complex.exp (Real.pi * HermFrame.form d.H z l) * F i (z, w + l) := by
  intro S P y d M hM hc x hx
  have hx' : ∀ q, x q = sqEx d.u q ≫ sqMap d.isPull.1.w := fun q => by
    refine Limits.pullback.hom_ext ((hx q).1.trans ?_) ((hx q).2.trans ?_)
    · rw [Category.assoc, sqMap, Limits.pullback.lift_fst, ← Category.assoc]
      exact congrArg (· ≫ d.φ) (sqEx_sqMaps d.u q 1).symm
    · rw [Category.assoc, sqMap, Limits.pullback.lift_snd, ← Category.assoc]
      exact congrArg (· ≫ d.φ) (sqEx_sqMaps d.u q 2).symm
  have hN := LB.isLB_linComb d.isLB (sqMaps d.B) ![1, -1, -1, 1]
  have hN' := pull_isLB hM (sqMap d.isPull.1.w)
  obtain ⟨w, hw⟩ := (CechPic.cls_eq_iff hN hN').1 (by
    rw [CechPic.cls_pull hM, hc, d.pol, CechPic.cls_linComb d.isLB, Fin.sum_univ_four]
    simp only [CechPic.lam, sqMaps, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul,
      neg_smul, sub_eq_add_neg])
  obtain ⟨F, h₁, h₂, h₃, h₄⟩ := exists_frame_of_iso hN hN' hw (isHolTo_sqEx d.u) (sqFr d.u _)
    (continuousAt_sqFr d.u _) (sqFr_ne_zero d.u _) (sqFr_compat d.u _)
  have m : ∀ i q, ⊤ ≤ x q ⁻¹ᵁ M.U i → ⊤ ≤ sqEx d.u q ⁻¹ᵁ (M.pull (sqMap d.isPull.1.w)).U fun _ => i :=
    fun i q h => (le_pull_iff _ _ _ _).2 (hx' q ▸ h)
  refine ⟨fun i => F fun _ => i, fun i q h => (h₁ _ q (m i q h)).continuousWithinAt,
    fun i q h => h₂ _ q (m i q h), fun i j q h => ?_, fun l i z v h => ?_⟩
  · obtain ⟨hi, hj⟩ := (top_le_preimage_inf _ _ _).1 h
    have hm := (top_le_preimage_inf _ _ _).2 ⟨m i q hi, m j q hj⟩
    beta_reduce
    rw [h₃ _ _ q hm, val_pull_g _ _ _ _ _ hm, hx' q]
  · obtain ⟨j, hj⟩ := exists_chart_pt hN (sqEx d.u (z, v))
    have e₁ : sqEx d.u (z + l, v) = sqEx d.u (z, v) := by simp only [sqEx, ex_add_period]
    have e₂ : sqEx d.u (z, v + l) = sqEx d.u (z, v) := by simp only [sqEx, ex_add_period]
    have hi := m i _ h
    obtain ⟨p₁, p₂⟩ := sqFr_period d.isAH l j z v hj
    beta_reduce
    rw [h₄ _ j _ hi hj, h₄ (fun _ => i) j (z + l, v) (by rw [e₁]; exact hi) (by rw [e₁]; exact hj),
      h₄ (fun _ => i) j (z, v + l) (by rw [e₂]; exact hi) (by rw [e₂]; exact hj), e₁, e₂]
    exact ⟨(congrArg _ p₁).trans (mul_left_comm _ _ _), (congrArg _ p₂).trans (mul_left_comm _ _ _)⟩

end GlobalTheory.PolFrame
