import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsLevelPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.TorusVal
open GlobalTheory.ZH.GeoModel ReciprocityTheory.ChartRestriction.G.DVR

variable {p : ℕ} [Fact p.Prime]

def NormIs (z : Sp (PadicAlgCl p)) (a : ((Sp (PadicAlgCl p)).presheaf.stalk z)ˣ) (r : ℝ) : Prop :=
  ∃ x, toStk z x = a.val ∧ ‖x‖ = r

variable {z : Sp (PadicAlgCl p)}

/- English proof (translation)
Take `⟨x, hx, rfl⟩` from `h`. Take `⟨y, hy, rfl⟩` from `h'`. Conclude with `⟨x * y, by rw [map_mul, hx, hy, Units.val_mul], norm_mul _ _⟩`.
-/
theorem NormIs.mul {a b} {r s : ℝ} (h : NormIs z a r) (h' : NormIs z b s) : NormIs z (a * b) (r * s) := by
  obtain ⟨x, hx, rfl⟩ := h
  obtain ⟨y, hy, rfl⟩ := h'
  exact ⟨x * y, by rw [map_mul, hx, hy, Units.val_mul], norm_mul _ _⟩

/- English proof (translation)
Take `rfl : z = cpt (PadicAlgCl p)` from `Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) _ _`. Conclude with `toStkA_injective`.
-/
theorem toStk_inj : Function.Injective (toStk z) := by
  obtain rfl : z = cpt (PadicAlgCl p) := Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) _ _
  exact toStkA_injective

/- English proof (translation)
Take `⟨x, hx, rfl⟩` from `h`. Take `⟨y, hy, rfl⟩` from `h'`. Rewrite using `[toStk_inj (hx.trans hy.symm)]`.
-/
theorem NormIs.unique {a} {r s : ℝ} (h : NormIs z a r) (h' : NormIs z a s) : r = s := by
  obtain ⟨x, hx, rfl⟩ := h
  obtain ⟨y, hy, rfl⟩ := h'
  rw [toStk_inj (hx.trans hy.symm)]

/- English proof (translation)
Take `⟨x, hx, rfl⟩` from `h`. Establish `h0 : x ≠ 0` using `fun h0 => by`. Establish `: toStk z 1 = toStk z 0`. Rewrite using `[map_one, ← a.mul_inv, ← hx, h0, map_zero, zero_mul]`. Conclude with `one_ne_zero (toStk_inj this)`.

Use `⟨x⁻¹, ?_, norm_inv _⟩` and prove the remaining obligations. Use `(Units.inv_eq_of_mul_eq_one_right ?_).symm` and prove the remaining obligations. Rewrite using `[← hx, ← map_mul, mul_inv_cancel₀ h0, map_one]`.
-/
theorem NormIs.inv {a} {r : ℝ} (h : NormIs z a r) : NormIs z a⁻¹ r⁻¹ := by
  obtain ⟨x, hx, rfl⟩ := h
  have h0 : x ≠ 0 := fun h0 => by
    have : toStk z 1 = toStk z 0 := by
      rw [map_one, ← a.mul_inv, ← hx, h0, map_zero, zero_mul]
    exact one_ne_zero (toStk_inj this)
  refine ⟨x⁻¹, ?_, norm_inv _⟩
  refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
  rw [← hx, ← map_mul, mul_inv_cancel₀ h0, map_one]

/- English proof (translation)
Rewrite using `[val_of t r z J j hj]`. Conclude with `⟨_, toStk_valF r _ z h _, rfl⟩`.
-/
theorem normIs_val {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp (PadicAlgCl p) ⟶ Y) (J) (j : K → L.ι) (hj : ∀ k, J (r ≫ φ k) = j k)
    (h : r z ∈ LB.wchart L φ j) : NormIs z (val t r z J) ‖valF r (LB.wchart L φ j) (t.s j).val‖ := by
  rw [val_of t r z J j hj]
  exact ⟨_, toStk_valF r _ z h _, rfl⟩

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}
  {ρ : S.Real} {y₀ : S.R →+* PadicAlgCl p} {u : ρ.UTest p y₀}

/- English proof (translation)
Substitute `hr` using the available equality. Establish `h : ⊤ ≤ r₀ ⁻¹ᵁ LB.wchart u.D.toPre.P.L φ (fun k => J (gPt p ≫ r₀ ≫ φ k))` using `fun w _ => Set.mem_iInter.2 fun k => hJ (r₀ ≫ φ k) (by rw [Category.assoc, h₀]) (x := w) trivial`. Establish `e` using `normIs_val (z := z) t (gPt p ≫ r₀) J (fun k => J (gPt p ≫ r₀ ≫ φ k)) (fun k => rfl) (h (x := gPt p z) trivial)`. Conclude with `(norm_unit r₀ _ h _) ▸ e`.
-/
theorem normIs_int {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ u.D.toPre.P.A.left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb u.D.toPre.P.L φ ε)) (r₀ : Sp (OO p) ⟶ Y)
    (h₀ : ∀ k, r₀ ≫ φ k ≫ u.D.toPre.P.A.hom = spMap u.j) {r : Sp (PadicAlgCl p) ⟶ Y} (hr : gPt p ≫ r₀ = r)
    {J} (hJ : u.IntGood J) : NormIs z (val t r z J) 1 := by
  subst hr
  have h : ⊤ ≤ r₀ ⁻¹ᵁ LB.wchart u.D.toPre.P.L φ (fun k => J (gPt p ≫ r₀ ≫ φ k)) := fun w _ =>
    Set.mem_iInter.2 fun k => hJ (r₀ ≫ φ k) (by rw [Category.assoc, h₀]) (x := w) trivial
  have e := normIs_val (z := z) t (gPt p ≫ r₀) J (fun k => J (gPt p ≫ r₀ ≫ φ k)) (fun k => rfl)
    (h (x := gPt p z) trivial)
  exact (norm_unit r₀ _ h _) ▸ e

/- English proof (translation)
Use `show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem tf_hom : (TF (R := u.V) (PadicAlgCl p)).hom = gPt p ≫ spMap u.j := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/- English proof (translation)
Set `T : Over (Sp u.V)` to `Over.mk (spMap u.j)`. Set `i₀ : TF (R` to `u.V) (PadicAlgCl p) ⟶ T := Over.homMk (gPt p) tf_hom.symm`. Establish `ex : ∀ b : TF (R` using `u.V) (PadicAlgCl p) ⟶ u.D.toPre.P.A, ∃ m : T ⟶ u.D.toPre.P.A, i₀ ≫ m = b := fun b => by`. Take `⟨ψ, h1, h2⟩` from `exists_ext u b`. Conclude with `⟨Over.homMk ψ h1, Over.OverMorphism.ext h2⟩`.

Take `⟨m, hm⟩` from `ex x`. Take `⟨m', hm'⟩` from `ex x'`. Take `⟨n, hn⟩` from `ex y`. Use `normIs_int (φ := thφ u.D.toPre.P.A (x3 u.D.toPre.P.A)) (ε := thε) u.D.toPre.cub.t (lift m (lift m' n)).left (fun k => ?_) ?_ hJ` and prove the remaining obligations. Conclude with `(congrArg _ (Over.w (psum _ _ _))).trans (Over.w _)`.

Use `show i₀.left ≫ _ = _`. Rewrite using `[← Over.comp_left, comp_lift, comp_lift, hm, hm', hn]`.
-/
theorem normIs_th (x x' y : TF (R := u.V) (PadicAlgCl p) ⟶ u.D.toPre.P.A) {J} (hJ : u.IntGood J) :
    NormIs z (th u.D.toPre (T := TF (R := u.V) (PadicAlgCl p)) z J x x' y) 1 := by
  let T : Over (Sp u.V) := Over.mk (spMap u.j)
  let i₀ : TF (R := u.V) (PadicAlgCl p) ⟶ T := Over.homMk (gPt p) tf_hom.symm
  have ex : ∀ b : TF (R := u.V) (PadicAlgCl p) ⟶ u.D.toPre.P.A, ∃ m : T ⟶ u.D.toPre.P.A, i₀ ≫ m = b := fun b => by
    obtain ⟨ψ, h1, h2⟩ := exists_ext u b
    exact ⟨Over.homMk ψ h1, Over.OverMorphism.ext h2⟩
  obtain ⟨m, hm⟩ := ex x
  obtain ⟨m', hm'⟩ := ex x'
  obtain ⟨n, hn⟩ := ex y
  refine normIs_int (φ := thφ u.D.toPre.P.A (x3 u.D.toPre.P.A)) (ε := thε) u.D.toPre.cub.t
    (lift m (lift m' n)).left (fun k => ?_) ?_ hJ
  · exact (congrArg _ (Over.w (psum _ _ _))).trans (Over.w _)
  · show i₀.left ≫ _ = _
    rw [← Over.comp_left, comp_lift, comp_lift, hm, hm', hn]

/- English proof (translation)
The claim follows from `normIs_val (g.s χ) (𝟙 _) J _ (fun k => by rw [Category.id_comp]) (Set.mem_iInter.2 fun k => hG _)`.
-/
theorem normIs_gt {g : GtPtF u.D.toPre (PadicAlgCl p)} {J} (hG : Good u.D.toPre.P.L z J) (χ : u.D.toPre.X) :
    NormIs z (val (g.s χ) (𝟙 _) z J) ‖valF (𝟙 (Sp (PadicAlgCl p))) _
      ((g.s χ).s (fun k => J (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k))).val‖ :=
  normIs_val (g.s χ) (𝟙 _) J _ (fun k => by rw [Category.id_comp]) (Set.mem_iInter.2 fun k => hG _)

/- English proof (translation)
Use `⟨fun h χ => h J hJ χ ▸ normIs_gt hG χ, fun h => ?_⟩` and prove the remaining obligations. Take `⟨ν', h'⟩` from `exists_gtN u g`. Take `rfl : ν' = ν` from `funext fun χ => by`. Use `(h χ).unique (h' J hJ χ ▸ normIs_gt hG χ)` as an intermediate fact. Simplify using `using this.symm`.

Conclude with `h'`.
-/
theorem gtN_iff {g : GtPtF u.D.toPre (PadicAlgCl p)} {J} (hJ : u.IntGood J) (hG : Good u.D.toPre.P.L z J)
    {ν : u.D.toPre.X → ℝ} : u.GtN g ν ↔ ∀ χ, NormIs z (val (g.s χ) (𝟙 _) z J) (Real.exp (-ν χ)) := by
  refine ⟨fun h χ => h J hJ χ ▸ normIs_gt hG χ, fun h => ?_⟩
  obtain ⟨ν', h'⟩ := exists_gtN u g
  obtain rfl : ν' = ν := funext fun χ => by
    have := (h χ).unique (h' J hJ χ ▸ normIs_gt hG χ)
    simpa using this.symm
  exact h'

/- English proof (translation)
Establish `: IsLocalHom u.j` using `((IsLocalRing.local_hom_TFAE u.j).out 0 3).2 (fun x hx => j_mem_max u x hx)`. Use `(top_le_iff_cpt (𝟙 (Sp u.V)) U).2 ?_` and prove the remaining obligations. Establish `e : spMap u.j (cpt (OO p)) = cpt u.V` using `IsLocalRing.comap_closedPoint u.j`. Use `h (x := cpt (OO p)) trivial` as an intermediate fact. Rewrite using `[← e]`.

Conclude with `this`.
-/
theorem top_le_of_j (U : (Sp u.V).Opens) (h : ⊤ ≤ spMap u.j ⁻¹ᵁ U) : ⊤ ≤ U := by
  have : IsLocalHom u.j := ((IsLocalRing.local_hom_TFAE u.j).out 0 3).2 (fun x hx => j_mem_max u x hx)
  refine (top_le_iff_cpt (𝟙 (Sp u.V)) U).2 ?_
  have e : spMap u.j (cpt (OO p)) = cpt u.V := IsLocalRing.comap_closedPoint u.j
  have := h (x := cpt (OO p)) trivial
  rw [← e]; exact this

/- English proof (translation)
Set `j : PUnit → u.D.toPre.P.L.ι` to `fun _ => J (gPt p ≫ spMap u.j ≫ (u.D.toPre.c χ).left)`. Establish `h1 : ⊤ ≤ (u.D.toPre.c χ).left ⁻¹ᵁ u.D.toPre.P.L.U (j PUnit.unit)` using `top_le_of_j _ (hJ (spMap u.j ≫ (u.D.toPre.c χ).left) (by`. Rewrite using `[Category.assoc, Over.w]`. Conclude with `Category.comp_id _))`. Establish `h2 : ⊤ ≤ (𝟙 (Sp (FractionRing u.V))) ⁻¹ᵁ LB.wchart u.D.toPre.P.L (fun _ : PUnit => ptK (u.D.toPre.c χ)) j` using `fun w _ => Set.mem_iInter.2 fun k => by`.

Rewrite using `[QForm.ptK_eq]`. Conclude with `h1 (x := jK u.V w) trivial`. Establish `e` using `normIs_val (z := z) (u.D.toPre.psi χ) (jFK (R := u.V) (PadicAlgCl p)) J j (fun _ => by`. Use `congrArg J ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc (gPt p), ← tf_hom]`.

Conclude with `(congrArg _ (QForm.ptK_eq _ χ)).trans (Category.assoc _ _ _).symm) (h2 (x := jFK (R := u.V) (PadicAlgCl p) z) trivial)`. Rewrite using `[← l.q_eq χ j h1]`. Establish `e2` using `GlobalTheory.Points.valR_spMap_comp (algebraMap (FractionRing u.V) (PadicAlgCl p)) (𝟙 (Sp (FractionRing u.V))) _ h2 ((u.D.toPre.psi χ).s j).val`. Rewrite `e2` using `[Category.comp_id]`. Conclude with `(congrArg norm e2) ▸ e`.
-/
theorem normIs_psi (l : u.Lab) {J} (hJ : u.IntGood J) (χ : u.D.toPre.X) :
    NormIs z (val (u.D.toPre.psi χ) (jFK (R := u.V) (PadicAlgCl p)) z J) (Real.exp (-l.q χ)) := by
  let j : PUnit → u.D.toPre.P.L.ι := fun _ => J (gPt p ≫ spMap u.j ≫ (u.D.toPre.c χ).left)
  have h1 : ⊤ ≤ (u.D.toPre.c χ).left ⁻¹ᵁ u.D.toPre.P.L.U (j PUnit.unit) :=
    top_le_of_j _ (hJ (spMap u.j ≫ (u.D.toPre.c χ).left) (by
      rw [Category.assoc, Over.w]; exact Category.comp_id _))
  have h2 : ⊤ ≤ (𝟙 (Sp (FractionRing u.V))) ⁻¹ᵁ LB.wchart u.D.toPre.P.L (fun _ : PUnit => ptK (u.D.toPre.c χ)) j :=
    fun w _ => Set.mem_iInter.2 fun k => by
      rw [QForm.ptK_eq]; exact h1 (x := jK u.V w) trivial
  have e := normIs_val (z := z) (u.D.toPre.psi χ) (jFK (R := u.V) (PadicAlgCl p)) J j (fun _ => by
    refine congrArg J ?_
    rw [← Category.assoc (gPt p), ← tf_hom]
    exact (congrArg _ (QForm.ptK_eq _ χ)).trans (Category.assoc _ _ _).symm) (h2 (x := jFK (R := u.V) (PadicAlgCl p) z) trivial)
  rw [← l.q_eq χ j h1]
  have e2 := GlobalTheory.Points.valR_spMap_comp (algebraMap (FractionRing u.V) (PadicAlgCl p)) (𝟙 (Sp (FractionRing u.V))) _ h2
    ((u.D.toPre.psi χ).s j).val
  rw [Category.comp_id] at e2
  exact (congrArg norm e2) ▸ e

/- English proof (translation)
Establish `hr : NormIs z (val u.D.toPre.rigK (jFK (R` using `u.V) (PadicAlgCl p)) z J) 1 := by`. Rewrite using `[DegPre.rigK, val_pull hG]`. Use `normIs_int u.D.toPre.rig (spMap u.j) (fun k => ?_) tf_hom.symm hJ` and prove the remaining obligations. Simplify using `[eSec]`. Establish `e` using `(((normIs_psi (z := z) l hJ (y + χ)).mul (normIs_psi l hJ y).inv).mul (normIs_psi l hJ χ).inv).mul hr.inv`.

Rewrite using `[DegPre.tau, val_mul hG, val_mul hG, val_mul hG, val_inv, val_inv, val_inv]`. Use `e using 1` and compare the differences between its conclusion and the goal. Rewrite using `[inv_one, _root_.mul_one, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add, QuadraticMap.polar]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem normIs_tau (l : u.Lab) {J} (hJ : u.IntGood J) (hG : Good u.D.toPre.P.L z J) (y χ : u.D.toPre.X) :
    NormIs z (val (u.D.toPre.tau y χ) (jFK (R := u.V) (PadicAlgCl p)) z J)
      (Real.exp (-QuadraticMap.polar l.q y χ)) := by
  have hr : NormIs z (val u.D.toPre.rigK (jFK (R := u.V) (PadicAlgCl p)) z J) 1 := by
    rw [DegPre.rigK, val_pull hG]
    refine normIs_int u.D.toPre.rig (spMap u.j) (fun k => ?_) tf_hom.symm hJ
    simp [eSec]
  have e := (((normIs_psi (z := z) l hJ (y + χ)).mul (normIs_psi l hJ y).inv).mul (normIs_psi l hJ χ).inv).mul hr.inv
  rw [DegPre.tau, val_mul hG, val_mul hG, val_mul hG, val_inv, val_inv, val_inv]
  convert e using 1
  rw [inv_one, _root_.mul_one, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add, QuadraticMap.polar]
  congr 1; ring

/- English proof (translation)
Introduce `_ o Ω _ _ _ _ S ρ p _ y₀ u l`. Take `⟨J, hJ, hG'⟩` from `exists_intGood u`. Set `z : Sp (PadicAlgCl p)` to `cpt _`. Establish `hG` using `hG' z`. Use `⟨⟨J, hJ, hG'⟩, fun g => ?_, gtN_unique u, fun g g' g'' ν ν' h a a' => ?_, fun y g h => ?_⟩` and prove the remaining obligations.

Take `⟨ν, hν⟩` from `exists_gtN u g`. Use `⟨AddMonoidHom.mk' ν fun χ χ' => ?_, hν⟩` and prove the remaining obligations. Establish `a` using `(gtN_iff hJ hG).1 hν`. Establish `e` using `gt_mul (𝟙 (TF (R := u.V) (PadicAlgCl p))) hG g χ χ'`. Rewrite `e` using `[Category.id_comp, Over.id_left]`.

Establish `b` using `(a (χ + χ')).mul (normIs_th (cP _ _ χ) (cP _ _ χ') g.b hJ)`. Establish `c` using `(e ▸ b).unique ((a χ).mul (a χ'))`. Rewrite `c` using `[_root_.mul_one, ← Real.exp_add, Real.exp_eq_exp]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨-, hs⟩` from `(isAdd_iff _ _ _).1 h`.

Take `⟨ν'', hν⟩` from `exists_gtN u g''`. Take `rfl : ν'' = ν + ν'` from `funext fun χ => by`. Establish `b` using `((gtN_iff hJ hG).1 hν χ).mul (normIs_th (cP _ _ χ) g.b g'.b hJ)`. Establish `c` using `(hs χ z J hG ▸ b).unique (((gtN_iff hJ hG).1 a χ).mul ((gtN_iff hJ hG).1 a' χ))`. Rewrite `c` using `[_root_.mul_one, ← Real.exp_add, Real.exp_eq_exp]`.

Use `show ν'' χ = ν χ + ν' χ`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hν`. Take `⟨-, hs⟩` from `(isIota_iff _ _).1 h`. Use `(gtN_iff hJ hG).2 fun χ => ?_` and prove the remaining obligations.

Establish `e` using `hs χ z J hG`. Rewrite `e` using `[Category.id_comp]`. Conclude with `e ▸ normIs_tau l hJ hG y χ`.
-/
theorem main : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∃ J, u.IntGood J ∧ ∀ z, Good u.D.toPre.P.L z J) ∧ (∀ g : GtPtF u.D.toPre (PadicAlgCl p), ∃ ν : u.D.toPre.X →+ ℝ, u.GtN g ν) ∧ (∀ (g : GtPtF u.D.toPre (PadicAlgCl p)) ν ν', u.GtN g ν → u.GtN g ν' → ν = ν') ∧ (∀ (g g' g'' : GtPtF u.D.toPre (PadicAlgCl p)) ν ν', GtPtF.IsAdd g g' g'' → u.GtN g ν → u.GtN g' ν' → u.GtN g'' (ν + ν')) ∧ ∀ (y : u.D.toPre.X) (g : GtPtF u.D.toPre (PadicAlgCl p)), GtPtF.IsIota y g → u.GtN g (QuadraticMap.polar l.q y) := by
  intro _ o Ω _ _ _ _ S ρ p _ y₀ u l
  obtain ⟨J, hJ, hG'⟩ := exists_intGood u
  let z : Sp (PadicAlgCl p) := cpt _
  have hG := hG' z
  refine ⟨⟨J, hJ, hG'⟩, fun g => ?_, gtN_unique u, fun g g' g'' ν ν' h a a' => ?_, fun y g h => ?_⟩
  · obtain ⟨ν, hν⟩ := exists_gtN u g
    refine ⟨AddMonoidHom.mk' ν fun χ χ' => ?_, hν⟩
    have a := (gtN_iff hJ hG).1 hν
    have e := gt_mul (𝟙 (TF (R := u.V) (PadicAlgCl p))) hG g χ χ'
    rw [Category.id_comp, Over.id_left] at e
    have b := (a (χ + χ')).mul (normIs_th (cP _ _ χ) (cP _ _ χ') g.b hJ)
    have c := (e ▸ b).unique ((a χ).mul (a χ'))
    rw [_root_.mul_one, ← Real.exp_add, Real.exp_eq_exp] at c
    linarith
  · obtain ⟨-, hs⟩ := (isAdd_iff _ _ _).1 h
    obtain ⟨ν'', hν⟩ := exists_gtN u g''
    obtain rfl : ν'' = ν + ν' := funext fun χ => by
      have b := ((gtN_iff hJ hG).1 hν χ).mul (normIs_th (cP _ _ χ) g.b g'.b hJ)
      have c := (hs χ z J hG ▸ b).unique (((gtN_iff hJ hG).1 a χ).mul ((gtN_iff hJ hG).1 a' χ))
      rw [_root_.mul_one, ← Real.exp_add, Real.exp_eq_exp] at c
      show ν'' χ = ν χ + ν' χ
      linarith
    exact hν
  · obtain ⟨-, hs⟩ := (isIota_iff _ _).1 h
    refine (gtN_iff hJ hG).2 fun χ => ?_
    have e := hs χ z J hG
    rw [Category.id_comp] at e
    exact e ▸ normIs_tau l hJ hG y χ

end GlobalTheory.ZH.TorusVal
end
