import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTermsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.WeightValue
open GlobalTheory.UT.CoefBasic

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨GeneratorPullback.powGen L φ ε t n, powGen_isGen L φ ε t ht n, fun _ _ _ _ => map_pow _ _ _⟩`.
-/
theorem exists_pow {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε ε' : K → ℤ} (n : ℕ)
    (h : ε' = fun i => (n : ℤ) * ε i) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε'), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), val t' r z J = val t r z J ^ n := by
  subst h
  exact ⟨GeneratorPullback.powGen L φ ε t n, powGen_isGen L φ ε t ht n, fun _ _ _ _ => map_pow _ _ _⟩

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [DegPre.lineε]`.
-/
theorem line_exp (k : ℕ) : DegPre.lineε k = fun i => (k : ℤ) * DegPre.lineε 1 i := by
  funext i
  fin_cases i <;> simp [DegPre.lineε]

/- English proof (translation)
Take `⟨S, hS⟩` from `h q`. Use `v.map_le_add (hS S le_rfl) (v.map_le_sum (s := S) fun i _ => hq i)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem le_of_sumV {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) {q : ℚ} (hq : ∀ i, (q : WithTop ℚ) ≤ v (x i)) : (q : WithTop ℚ) ≤ v s := by
  obtain ⟨S, hS⟩ := h q
  have := v.map_le_add (hS S le_rfl) (v.map_le_sum (s := S) fun i _ => hq i)
  rwa [sub_add_cancel] at this

/- English proof (translation)
Introduce `q`. Take `⟨S, hS⟩` from `h q`. Use `⟨S, fun T hT => ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, ← mul_sub, v.map_mul, hc, zero_add]`. Conclude with `hS T hT`.
-/
theorem sumV_mul {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s c : F}
    (h : SumV v x s) (hc : v c = 0) : SumV v (fun i => c * x i) (c * s) := by
  intro q
  obtain ⟨S, hS⟩ := h q
  refine ⟨S, fun T hT => ?_⟩
  rw [← Finset.mul_sum, ← mul_sub, v.map_mul, hc, zero_add]
  exact hS T hT

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} {hϖ : Irreducible ϖ}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} {hv : ValOver ϖ F v}
  {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → ((TF (R := V) F).left ⟶ X)}

/- English proof (translation)
Take `⟨φ₀, hφ, t₀, ht₀, x, hx, hval⟩` from `ht`. Take `⟨t₁, ht₁, hv₁⟩` from `exists_pow n h t₀ ht₀`. Use `⟨φ₀, hφ, t₁, ht₁, x ^ n, ?_, fun z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[v.map_pow, hx]`. Simplify using the standard rewrite rules.

Rewrite using `[e z J hJ, hv₁, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hval z J hJ, mul_pow, cst_eq, cst_eq, map_pow]`.
-/
theorem genV_pow {ε ε' : K → ℤ} (n : ℕ) (h : ε' = fun i => (n : ℤ) * ε i) {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ ε')} (ht : GenV hϖ hv t 0)
    (e : ∀ z J, Good L z J → val t' (𝟙 _) z J = val t (𝟙 _) z J ^ n) : GenV hϖ hv t' 0 := by
  obtain ⟨φ₀, hφ, t₀, ht₀, x, hx, hval⟩ := ht
  obtain ⟨t₁, ht₁, hv₁⟩ := exists_pow n h t₀ ht₀
  refine ⟨φ₀, hφ, t₁, ht₁, x ^ n, ?_, fun z J hJ => ?_⟩
  · rw [v.map_pow, hx]; simp
  · rw [e z J hJ, hv₁, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hval z J hJ, mul_pow, cst_eq, cst_eq, map_pow]

/- English proof (translation)
Take `⟨φ₀, hφ, t₀, ht₀, x, hx, hval⟩` from `ht`. Use `⟨φ₀, hφ, t₀, ht₀, c * x, ?_, fun z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[v.map_mul, hx, hc]`. Simplify using the standard rewrite rules. Rewrite using `[e z J hJ, hval z J hJ, cst_eq, cst_eq, cst_eq, map_mul, _root_.mul_assoc]`.
-/
theorem genV_smul {ε : K → ℤ} {t t' : LB.Gen (LB.LinComb L φ ε)} (ht : GenV hϖ hv t 0) {c : F} {r : ℚ}
    (hc : v c = (r : WithTop ℚ))
    (e : ∀ z J, Good L z J → (val t' (𝟙 _) z J).val = cst F z c * (val t (𝟙 _) z J).val) : GenV hϖ hv t' r := by
  obtain ⟨φ₀, hφ, t₀, ht₀, x, hx, hval⟩ := ht
  refine ⟨φ₀, hφ, t₀, ht₀, c * x, ?_, fun z J hJ => ?_⟩
  · rw [v.map_mul, hx, hc]; simp
  · rw [e z J hJ, hval z J hJ, cst_eq, cst_eq, cst_eq, map_mul, _root_.mul_assoc]

end

section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

/- English proof (translation)
Use `coef_eq fun z J hJ => ?_` and prove the remaining obligations. Establish `e : sval (s.s χ) (lift (𝟙 (TF (R` using `R) F)) g.b).left z J = 0 := (congrArg (gs _ z _) (h _)).trans ((gs_eq _ z _ (hJ.mem (DegPre.famφ D F χ) _) _).trans ((congrArg _ (map_zero _)).trans (map_zero _)))`. Rewrite using `[e, cst_eq, map_zero, zero_mul, zero_mul, zero_mul]`.
-/
theorem coef_zero {k : ℕ} (g : GtPtF D F) (w : Frm D F k g.b) (s : Fam D F k) (χ : D.X)
    (h : ∀ j, (s.s χ).f j = 0) : coef s g w χ = 0 := by
  refine coef_eq fun z J hJ => ?_
  have e : sval (s.s χ) (lift (𝟙 (TF (R := R) F)) g.b).left z J = 0 :=
    (congrArg (gs _ z _) (h _)).trans ((gs_eq _ z _ (hJ.mem (DegPre.famφ D F χ) _) _).trans
      ((congrArg _ (map_zero _)).trans (map_zero _)))
  rw [e, cst_eq, map_zero, zero_mul, zero_mul, zero_mul]

/- English proof (translation)
Take `⟨hb, hs⟩` from `(isZero_iff o).1 ho`. Use `coef_eq fun z J hJ => ?_` and prove the remaining obligations. Establish `a` using `isCoef_coef o hw₁.1 χ s z J hJ`. Establish `e₁ : lift (𝟙 (TF (R` using `R) F)) g.b = lift (𝟙 (TF (R := R) F)) o.b := by rw [hb, hτ.1]`. Rewrite `a` using `[hw₁.2 z J hJ, hs χ z J hJ]`.

Rewrite using `[hw.2 z J hJ, e₁, hτ.2 χ z J hJ]`. Simplify using `only [cst_eq, map_mul, Units.val_one] at a ⊢`. Take the linear combination `cstH z (τ (Multiplicative.ofAdd χ)).val * a`.
-/
theorem coef_tor {k : ℕ} {τ : Multiplicative D.X →* Fˣ} {g o : GtPtF D F} (hτ : IsTor τ g) (ho : o.IsZero)
    {w : Frm D F k g.b} {w₁ : Frm D F k o.b} (hw : FrmOne w) (hw₁ : FrmOne w₁) (s : Fam D F k) (χ : D.X) :
    coef s g w χ = (τ (Multiplicative.ofAdd χ)).val * coef s o w₁ χ := by
  obtain ⟨hb, hs⟩ := (isZero_iff o).1 ho
  refine coef_eq fun z J hJ => ?_
  have a := isCoef_coef o hw₁.1 χ s z J hJ
  have e₁ : lift (𝟙 (TF (R := R) F)) g.b = lift (𝟙 (TF (R := R) F)) o.b := by rw [hb, hτ.1]
  rw [hw₁.2 z J hJ, hs χ z J hJ] at a
  rw [hw.2 z J hJ, e₁, hτ.2 χ z J hJ]
  simp only [cst_eq, map_mul, Units.val_one] at a ⊢
  linear_combination cstH z (τ (Multiplicative.ofAdd χ)).val * a

end

/- English proof (translation)
Introduce `hL hT hVR hTW hUU V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN n k hn hk p x hy hx e he`. Take `⟨w₁, hw₁, hv₁, hsum⟩` from `GlobalTheory.T.section_value_at_torsionPoint_eq_sum_terms hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN n hn p x hx e he`. Establish `hv₁ : GenV hϖ hv w₁ 0`. Establish `e0 : ((Q p.y : ℚ) / (n : ℚ) ^ 2) = 0` using `by rw [hy, QForm.Q_zero hϖ D hQ]; simp`. Rewrite `hv₁` using `[e0]`. Then use the resulting hypothesis.

Take `⟨-, huniq, hone, -, hqk, -, hterm⟩` from `GlobalTheory.UT.CoefVal.main hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv p.g`. Take `⟨w, hw, hwv⟩` from `exists_pow k (line_exp k) w₁ hw₁`. Establish `hw0 : GenV hϖ hv w 0` using `genV_pow k (line_exp k) hv₁ fun z J _ => hwv _ _ z J`. Take `⟨-, hex, hb⟩` from `coef_basic V D.toPre F k p.g`. Establish `hζ : ∃ ζ : F, v ζ = 0 ∧ (p.g.b = 1 → ∃ w' : Frm D.toPre F k p.g.b, FrmOne w' ∧ ∀ (s : Fam D.toPre F k) χ, coef s p.g w' χ = ζ * coef s p.g w χ)`.

Distinguish the cases in `h1 : p.g.b = 1`. Take `⟨w', hw'⟩` from `hex h1`. Take `⟨c, hc, hcv, hcc⟩` from `(hb w hw).2.2.1 w' hw'.1`. Take `⟨r, hr⟩` from `WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hc)`. Establish `r0 : r = 0` using `(huniq k w' hw'.1).unique (genV_smul hw0 hr.symm hcv) (hone k w' hw' h1)`.

Conclude with `⟨c, by rw [← hr, r0]; rfl, fun _ => ⟨w', hw', hcc⟩⟩`. Conclude with `⟨1, v.map_one, fun h => absurd h h1⟩`. Take `⟨ζ, hζ, hζ'⟩` from `hζ`. Use `⟨ζ, hζ, fun t s c hts hc => ?_⟩` and prove the remaining obligations. Establish `hS : SumV v (coef s p.g w) c` using `hsum k hk w ⟨hw, fun z J _ => hwv _ _ z J⟩ t s c hts hc`.

Use `⟨fun hν a q hsupp hq => le_of_sumV hS fun β => ?_, fun τ hτ o w₂ ho hw₂ => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hβ : ∀ z : D.toPre.X, β ≠ a + k • z`. Rewrite using `[coef_zero p.g w s β (hsupp β hβ), v.map_zero]`. Conclude with `le_top`. Take `⟨z, hz⟩` from `not_forall.1 hβ`.

Take `rfl` from `not_not.1 hz`. Use `le_trans (WithTop.coe_le_coe.2 ?_) ((hterm k hk w s hw).2 _ 0 0 (hqk n hn p) hw0 hν (a + k • z))` and prove the remaining obligations. Establish `b0 : QForm.bOf D.toPre Q p.y (a + k • z) = 0`. Rewrite using `[hy, QForm.bOf, zero_add, QForm.Q_zero hϖ D hQ]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[b0]`. Simplify using `using hq z`. Take `⟨w', hw', hcc⟩` from `hζ' hτ.1`. Use `sumV_mul hS hζ` as an intermediate fact. Simplify `this` using `only [← hcc, coef_tor hτ ho hw' hw₂]`.
-/
theorem value_at_formal_torsion : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (n k : ℕ), 1 ≤ n → 1 ≤ k → ∀ (p : QkPt D.toPre F n) x, p.y = 0 → QkToAkU U.toUnifPre F n p x → ∀ e, IsTorsFrame A ρ n x e → ∃ ζ : F, v ζ = 0 ∧ ∀ (t : SecA A F k) s (c : F), U.ExpandsF F k w₀ t s → (∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J = @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z c) * (val (powFrame A.A A.L x e k) (𝟙 _) z J).val) → (NuGe D Q F v k s 0 → ∀ (a : D.toPre.X) (q : ℚ), (∀ β, (∀ z : D.toPre.X, β ≠ a + k • z) → ∀ j, (s.s β).f j = 0) → (∀ z : D.toPre.X, q ≤ (Q (a + k • z) : ℚ) / k) → (q : WithTop ℚ) ≤ v c) ∧ ∀ τ, IsTor τ p.g → ∀ (o : GtPtF D.toPre F) (w₁ : Frm D.toPre F k o.b), o.IsZero → FrmOne w₁ → SumV v (fun α => (τ (Multiplicative.ofAdd α)).val * coef s o w₁ α) (ζ * c) := by
  intro hL hT hVR hTW hUU V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN n k hn hk p x hy hx e he
  obtain ⟨w₁, hw₁, hv₁, hsum⟩ := GlobalTheory.T.section_value_at_torsionPoint_eq_sum_terms hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN n hn p x hx e he
  have hv₁ : GenV hϖ hv w₁ 0 := by
    have e0 : ((Q p.y : ℚ) / (n : ℚ) ^ 2) = 0 := by rw [hy, QForm.Q_zero hϖ D hQ]; simp
    rwa [e0] at hv₁
  obtain ⟨-, huniq, hone, -, hqk, -, hterm⟩ := GlobalTheory.UT.CoefVal.main hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv p.g
  obtain ⟨w, hw, hwv⟩ := exists_pow k (line_exp k) w₁ hw₁
  have hw0 : GenV hϖ hv w 0 := genV_pow k (line_exp k) hv₁ fun z J _ => hwv _ _ z J
  obtain ⟨-, hex, hb⟩ := coef_basic V D.toPre F k p.g
  have hζ : ∃ ζ : F, v ζ = 0 ∧ (p.g.b = 1 → ∃ w' : Frm D.toPre F k p.g.b, FrmOne w' ∧
      ∀ (s : Fam D.toPre F k) χ, coef s p.g w' χ = ζ * coef s p.g w χ) := by
    by_cases h1 : p.g.b = 1
    · obtain ⟨w', hw'⟩ := hex h1
      obtain ⟨c, hc, hcv, hcc⟩ := (hb w hw).2.2.1 w' hw'.1
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hc)
      have r0 : r = 0 := (huniq k w' hw'.1).unique (genV_smul hw0 hr.symm hcv) (hone k w' hw' h1)
      exact ⟨c, by rw [← hr, r0]; rfl, fun _ => ⟨w', hw', hcc⟩⟩
    · exact ⟨1, v.map_one, fun h => absurd h h1⟩
  obtain ⟨ζ, hζ, hζ'⟩ := hζ
  refine ⟨ζ, hζ, fun t s c hts hc => ?_⟩
  have hS : SumV v (coef s p.g w) c := hsum k hk w ⟨hw, fun z J _ => hwv _ _ z J⟩ t s c hts hc
  refine ⟨fun hν a q hsupp hq => le_of_sumV hS fun β => ?_, fun τ hτ o w₂ ho hw₂ => ?_⟩
  · by_cases hβ : ∀ z : D.toPre.X, β ≠ a + k • z
    · rw [coef_zero p.g w s β (hsupp β hβ), v.map_zero]
      exact le_top
    · obtain ⟨z, hz⟩ := not_forall.1 hβ
      obtain rfl := not_not.1 hz
      refine le_trans (WithTop.coe_le_coe.2 ?_) ((hterm k hk w s hw).2 _ 0 0 (hqk n hn p) hw0 hν (a + k • z))
      have b0 : QForm.bOf D.toPre Q p.y (a + k • z) = 0 := by
        rw [hy, QForm.bOf, zero_add, QForm.Q_zero hϖ D hQ]; ring
      rw [b0]
      simpa using hq z
  · obtain ⟨w', hw', hcc⟩ := hζ' hτ.1
    have := sumV_mul hS hζ
    simpa only [← hcc, coef_tor hτ ho hw' hw₂] using this

end GlobalTheory.UT.WeightValue
end
