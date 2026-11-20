import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GermExist

/- English proof (translation)
Take `⟨h1, -, h3, -⟩` from `hrep R G d x hx (Fin 1 × Fin d)`. Take `⟨y, hy, -⟩` from `h1 (pt R (n := 1) d 0) (gp_pt 0)`. Establish `hc` using `(h3 _ y hy).1`. Establish `hs` using `h 1 _ y hy`. Establish `e : ev (n` using `1) ![pt R (n := 1) d 0] r = r := by`.

Establish `: (![pt R d 0] : Fin 1 → Pt R 1 d) = fun j => pt R d j`. Use function extensionality and compare the values at `j`. Use `fin_cases j`. Both sides reduce to the same expression. Rewrite using `[this]`.

Unfold `ev`. Conclude with `congrFun MvPowerSeries.subst_self r`. Rewrite `hs` using `[e]`. Take `⟨⟨τ, hτ⟩, -⟩` from `hser R (Fin 1 × Fin d) G.left (fun m => (y m).left) (fun m => by rw [← Over.comp_left, hc m]) U (hs 0).1`. Rewrite using `[(hτ f r).1 hs]`.

Conclude with `hf.map τ`.
-/
theorem isUnit_of_isSer1 (hrep : RepSt) (hser : SerSt) {R : Type} [CommRing R]
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} {x : Fam G (Fin d)} (hx : IsUnivChart G d x)
    {U : G.left.Opens} {f : Γ(G.left, U)} (hf : IsUnit f) {r : PS R 1 d} (h : IsSer1 x U f r) : IsUnit r := by
  obtain ⟨h1, -, h3, -⟩ := hrep R G d x hx (Fin 1 × Fin d)
  obtain ⟨y, hy, -⟩ := h1 (pt R (n := 1) d 0) (gp_pt 0)
  have hc := (h3 _ y hy).1
  have hs := h 1 _ y hy
  have e : ev (n := 1) ![pt R (n := 1) d 0] r = r := by
    have : (![pt R d 0] : Fin 1 → Pt R 1 d) = fun j => pt R d j := by
      funext j; fin_cases j; rfl
    rw [this]
    unfold ev
    exact congrFun MvPowerSeries.subst_self r
  rw [e] at hs
  obtain ⟨⟨τ, hτ⟩, -⟩ := hser R (Fin 1 × Fin d) G.left (fun m => (y m).left)
    (fun m => by rw [← Over.comp_left, hc m]) U (hs 0).1
  rw [(hτ f r).1 hs]
  exact hf.map τ

/- English proof (translation)
Introduce `z hz`. Conclude with `Set.mem_iInter.2 fun k => h k hz`.
-/
theorem top_le_preimage_wchart {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (j : L.ι) (e : Z ⟶ Y) (h : ∀ k, ⊤ ≤ (e ≫ φ k) ⁻¹ᵁ L.U j) : ⊤ ≤ e ⁻¹ᵁ LB.wchart L φ (fun _ => j) := by
  intro z hz
  exact Set.mem_iInter.2 fun k => h k hz

/- English proof (translation)
Establish `h1 : η[A] ≫ (1 : A ⟶ A) = η[A]`. Rewrite using `[MonObj.comp_one, Hom.one_def]`. Simplify using the standard rewrite rules. Establish `h2 : η[A] ≫ (𝟙 A * w : A ⟶ A) = η[A]`. Rewrite using `[MonObj.comp_mul, hw, Category.comp_id]`.

Establish `: η[A] = (1 : 𝟙_ (Over S) ⟶ A)`. Rewrite using `[Hom.one_def]`. Simplify using the standard rewrite rules. Rewrite using `[this, _root_.mul_one]`. Use `fin_cases k`.

Conclude with `Category.comp_id _`. Conclude with `congrArg (·.left) h2`. Conclude with `Category.comp_id _`. Conclude with `congrArg (·.left) hw`. Conclude with `congrArg (·.left) h1`.
-/
theorem unit_comp_primφ {S : Scheme.{0}} {A : Over S} [GrpObj A] (w : A ⟶ A) (hw : η[A] ≫ w = η[A])
    (k : Fin 5) : η[A].left ≫ primφ w k = η[A].left := by
  have h1 : η[A] ≫ (1 : A ⟶ A) = η[A] := by
    rw [MonObj.comp_one, Hom.one_def]
    simp
  have h2 : η[A] ≫ (𝟙 A * w : A ⟶ A) = η[A] := by
    rw [MonObj.comp_mul, hw, Category.comp_id]
    have : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by
      rw [Hom.one_def]; simp
    rw [this, _root_.mul_one]
  fin_cases k
  · exact Category.comp_id _
  · exact congrArg (·.left) h2
  · exact Category.comp_id _
  · exact congrArg (·.left) hw
  · exact congrArg (·.left) h1

/- English proof (translation)
Introduce `_ hrep hser hex R _ G _ L _ w hw ρ d x hx j hj m s`. Take `⟨h1, -⟩` from `hex R G d x hx`. Take `⟨σ, hσ, uσ⟩` from `h1 (LB.wchart L (K := PUnit) (fun _ => 𝟙 G.left) (fun _ => j)) (top_le_preimage_wchart L _ j _ (fun _ => by rw [Category.comp_id]; exact hj)) (s.f (fun _ => j))`. Take `⟨r, hr, ur⟩` from `h1 (LB.wchart L (primφ w) (fun _ => j)) (top_le_preimage_wchart L _ j _ (fun k => by rw [unit_comp_primφ w hw k]; exact hj)) (ρ.s (fun _ => j)).val`. Establish `hu : IsUnit (r ^ m)` using `(isUnit_of_isSer1 hrep hser hx (Units.isUnit _) hr).pow m`.

Take `⟨v, hv⟩` from `hu`. Use `⟨σ * (v⁻¹).val, ⟨σ, r, hσ, hr, by rw [← hv, Units.inv_mul_cancel_right]⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `f ⟨σ', r', hσ', hr', hf⟩`. Rewrite `hf` using `[uσ σ' hσ', ur r' hr', ← hv]`. Rewrite using `[← hf, Units.mul_inv_cancel_right]`.
-/
theorem germ_exists_unique : JetAlgSt → RepSt → SerSt → SerExSt → GermExSt := by
  intro _ hrep hser hex R _ G _ L _ w hw ρ d x hx j hj m s
  obtain ⟨h1, -⟩ := hex R G d x hx
  obtain ⟨σ, hσ, uσ⟩ := h1 (LB.wchart L (K := PUnit) (fun _ => 𝟙 G.left) (fun _ => j))
    (top_le_preimage_wchart L _ j _ (fun _ => by rw [Category.comp_id]; exact hj)) (s.f (fun _ => j))
  obtain ⟨r, hr, ur⟩ := h1 (LB.wchart L (primφ w) (fun _ => j))
    (top_le_preimage_wchart L _ j _ (fun k => by rw [unit_comp_primφ w hw k]; exact hj)) (ρ.s (fun _ => j)).val
  have hu : IsUnit (r ^ m) := (isUnit_of_isSer1 hrep hser hx (Units.isUnit _) hr).pow m
  obtain ⟨v, hv⟩ := hu
  refine ⟨σ * (v⁻¹).val, ⟨σ, r, hσ, hr, by rw [← hv, Units.inv_mul_cancel_right]⟩, ?_⟩
  rintro f ⟨σ', r', hσ', hr', hf⟩
  rw [uσ σ' hσ', ur r' hr', ← hv] at hf
  rw [← hf, Units.mul_inv_cancel_right]

end GlobalTheory.GermExist
