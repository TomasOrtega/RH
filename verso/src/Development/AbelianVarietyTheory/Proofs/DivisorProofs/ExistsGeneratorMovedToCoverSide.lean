import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportSymmetricLiftsThetaGroupTraitImports
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaMove

/- English proof (translation)
Introduce `XA XP XG XT Y Y' LA LP LG LT hA hP hG hT α β c wA hwA ℓ hℓ w hw f _ sA mA sT mT e' h₁ h₂ h₃ k u' hu'`. Take `⟨t1, ht1, v1⟩` from `ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_up ((isGen_iff w).1 hw) hG hT (φ' := ![sT, mT]) (ε := ![k, -k]) u' hu'`. Take `⟨t2, ht2, v2⟩` from `ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_up ((isGen_iff ℓ).1 hℓ) hP hG (φ' := fun i => ![sT, mT] i ≫ c) (ε := ![k, -k]) t1 ht1`. Establish `ht3` using `ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen LP _ _ t2 ht2 (inv f)`. Establish `hfe : ∀ i, inv f ≫ (![sT, mT] i ≫ c) ≫ β = ![sA, mA] i ≫ α`.

Introduce `i`. Use `fin_cases i`. Simplify using `only [Fin.zero_eta, Matrix.cons_val_zero, Category.assoc, ← h₁, IsIso.inv_hom_id_assoc]`. Simplify using `only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Category.assoc]`. Rewrite using `[← h₂, Category.assoc, ← h₁, reassoc_of% h₃, IsIso.inv_hom_id_assoc]`.

Take `⟨t4, ht4, v4⟩` from `ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hP (φ' := fun i => ![sA, mA] i ≫ α) (ε' := ![k, -k]) (fun U _ h => by simp only [hfe]) _ ht3`. Take `⟨u, hu, v5⟩` from `GlobalTheory.ArcPull.exists_down_om hwA hP hA (φ' := ![sA, mA]) (φ := fun i => ![sA, mA] i ≫ α) (𝟙 Y) (fun i => (Category.id_comp _).symm) t4 ht4`. Use `⟨u, hu, fun Z q z JP JA JG Jt gP gA gG gT => ?_⟩` and prove the remaining obligations. Establish `e5` using `v5 Z (q ≫ f) z JP JA gP gA`. Establish `e4` using `v4 Z ((q ≫ f) ≫ 𝟙 Y) z JP gP`.

Establish `e3` using `ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull gP t2 (inv f) ((q ≫ f) ≫ 𝟙 Y)`. Establish `hq : ((q ≫ f) ≫ 𝟙 Y) ≫ inv f = q` using `by simp`. Rewrite `e3` using `[hq]`. Establish `e2 : val t2 q z JP = pw ℓ (fun i => ![sT, mT] i ≫ c) ![k, -k] q z _ _ * val t1 q z JG` using `v2 Z q z _ _ (gP.mem _ q) (gG.mem _ q)`. Establish `e1 : val t1 q z JG = pw w ![sT, mT] ![k, -k] q z _ _ * val u' q z Jt` using `v1 Z q z _ _ (gG.mem _ q) (gT.mem _ q)`.

Establish `h₄ : f ≫ mA ≫ α = mT ≫ c ≫ β` using `by rw [← reassoc_of% h₃, h₁, reassoc_of% h₂]`. Simplify using `only [pw, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, GlobalTheory.ArcPull.om, tf, Category.assoc, Category.comp_id] at e1 e2 e3 e4 e5 ⊢`. Establish `p₁ : q ≫ f ≫ sA ≫ α = q ≫ sT ≫ c ≫ β` using `by rw [h₁]`. Establish `p₄ : q ≫ f ≫ mA ≫ α = q ≫ mT ≫ c ≫ β` using `by rw [h₄]`. Establish `p₃ : q ≫ e' ≫ f ≫ sA = q ≫ f ≫ mA` using `by rw [h₃]`.

Establish `p₂ : q ≫ e' ≫ sT = q ≫ mT` using `by rw [h₂]`. Establish `p₂' : q ≫ e' ≫ sT ≫ c = q ≫ mT ≫ c` using `by rw [reassoc_of% h₂]`. Establish `p₂'' : q ≫ e' ≫ sT ≫ c ≫ β = q ≫ mT ≫ c ≫ β` using `by rw [reassoc_of% h₂]`. Rewrite `e5` using `[e4, e3, e2, e1, p₁, p₄]`. Rewrite using `[p₃, p₂'', p₂', p₂]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `e'` using `congrArg Additive.ofMul e5`. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow] at e' ⊢`. Take the linear combination `(norm := module) -e'`.
-/
theorem exists_gen_up : ∀ {XA XP XG XT Y Y' : Scheme.{0}} {LA : LB XA} {LP : LB XP} {LG : LB XG} {LT : LB XT} (hA : LA.IsLB) (hP : LP.IsLB) (hG : LG.IsLB) (hT : LT.IsLB) {α : XA ⟶ XP} {β : XG ⟶ XP} {c : XT ⟶ XG} (wA : LB.Iso LA (LP.pull α)) (hwA : wA.IsGen) (ℓ : LB.Iso LG (LP.pull β)) (hℓ : ℓ.IsGen) (w : LB.Iso LT (LG.pull c)) (hw : w.IsGen) (f : Y' ⟶ Y) [IsIso f] (sA mA : Y ⟶ XA) (sT mT : Y' ⟶ XT) (e' : Y' ⟶ Y') (h₁ : f ≫ sA ≫ α = sT ≫ c ≫ β) (h₂ : e' ≫ sT = mT) (h₃ : e' ≫ f ≫ sA = f ≫ mA) (k : ℤ) (u' : LB.Gen (LB.LinComb LT ![sT, mT] ![k, -k])) (hu' : u'.IsGen), ∃ u : LB.Gen (LB.LinComb LA ![sA, mA] ![k, -k]), u.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y') (z : Z) JP JA JG Jt, Good LP z JP → Good LA z JA → Good LG z JG → Good LT z Jt → val u (q ≫ f) z JA = tf wA ℓ w f sA sT q z JP JA JG Jt ^ k * val u' q z Jt * (tf wA ℓ w f sA sT (q ≫ e') z JP JA JG Jt ^ k)⁻¹ := by
  intro XA XP XG XT Y Y' LA LP LG LT hA hP hG hT α β c wA hwA ℓ hℓ w hw f _ sA mA sT mT e' h₁ h₂ h₃ k u' hu'
  obtain ⟨t1, ht1, v1⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_up ((isGen_iff w).1 hw) hG hT (φ' := ![sT, mT])
    (ε := ![k, -k]) u' hu'
  obtain ⟨t2, ht2, v2⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_up ((isGen_iff ℓ).1 hℓ) hP hG
    (φ' := fun i => ![sT, mT] i ≫ c) (ε := ![k, -k]) t1 ht1
  have ht3 := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen LP _ _ t2 ht2 (inv f)
  have hfe : ∀ i, inv f ≫ (![sT, mT] i ≫ c) ≫ β = ![sA, mA] i ≫ α := by
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, Category.assoc, ← h₁, IsIso.inv_hom_id_assoc]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Category.assoc]
      rw [← h₂, Category.assoc, ← h₁, reassoc_of% h₃, IsIso.inv_hom_id_assoc]
  obtain ⟨t4, ht4, v4⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hP (φ' := fun i => ![sA, mA] i ≫ α) (ε' := ![k, -k])
    (fun U _ h => by simp only [hfe]) _ ht3
  obtain ⟨u, hu, v5⟩ := GlobalTheory.ArcPull.exists_down_om hwA hP hA (φ' := ![sA, mA]) (φ := fun i => ![sA, mA] i ≫ α)
    (𝟙 Y) (fun i => (Category.id_comp _).symm) t4 ht4
  refine ⟨u, hu, fun Z q z JP JA JG Jt gP gA gG gT => ?_⟩
  have e5 := v5 Z (q ≫ f) z JP JA gP gA
  have e4 := v4 Z ((q ≫ f) ≫ 𝟙 Y) z JP gP
  have e3 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull gP t2 (inv f) ((q ≫ f) ≫ 𝟙 Y)
  have hq : ((q ≫ f) ≫ 𝟙 Y) ≫ inv f = q := by simp
  rw [hq] at e3
  have e2 : val t2 q z JP = pw ℓ (fun i => ![sT, mT] i ≫ c) ![k, -k] q z _ _ * val t1 q z JG :=
    v2 Z q z _ _ (gP.mem _ q) (gG.mem _ q)
  have e1 : val t1 q z JG = pw w ![sT, mT] ![k, -k] q z _ _ * val u' q z Jt := v1 Z q z _ _ (gG.mem _ q) (gT.mem _ q)
  have h₄ : f ≫ mA ≫ α = mT ≫ c ≫ β := by rw [← reassoc_of% h₃, h₁, reassoc_of% h₂]
  simp only [pw, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, GlobalTheory.ArcPull.om, tf, Category.assoc, Category.comp_id] at e1 e2 e3 e4 e5 ⊢
  have p₁ : q ≫ f ≫ sA ≫ α = q ≫ sT ≫ c ≫ β := by rw [h₁]
  have p₄ : q ≫ f ≫ mA ≫ α = q ≫ mT ≫ c ≫ β := by rw [h₄]
  have p₃ : q ≫ e' ≫ f ≫ sA = q ≫ f ≫ mA := by rw [h₃]
  have p₂ : q ≫ e' ≫ sT = q ≫ mT := by rw [h₂]
  have p₂' : q ≫ e' ≫ sT ≫ c = q ≫ mT ≫ c := by rw [reassoc_of% h₂]
  have p₂'' : q ≫ e' ≫ sT ≫ c ≫ β = q ≫ mT ≫ c ≫ β := by rw [reassoc_of% h₂]
  rw [e4, e3, e2, e1, p₁, p₄] at e5
  rw [p₃, p₂'', p₂', p₂]
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e5
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at e' ⊢
  linear_combination (norm := module) -e'

end GlobalTheory.ThetaMove
