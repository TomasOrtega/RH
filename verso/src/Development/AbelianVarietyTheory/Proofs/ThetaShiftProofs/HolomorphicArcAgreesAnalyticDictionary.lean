import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSubspaceIsometric
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCompare

section Dict

variable {O : Type} [CommRing O] [StarRing O] [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]
  {D₀ : Out.DegPre ℂ} [Module O D₀.X] {oa : D₀.OAct O} (d : GtDict D₀ oa)

/- English proof (translation)
Rewrite using `[d.ex₀_eq_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨la, hy, e⟩ x`. Establish `hl : la.l = 0` using `Subtype.ext (by simpa [hy] using (congrArg Prod.snd e).symm)`. Establish `: l x = l' x + (la.n x : ℤ)`.

Use `congrArg (fun v : d.A.V => v.1 x) e` as an intermediate fact. Simplify using `[hy, hl] at this`. Take the linear combination `this`. Rewrite using `[this, AnArc.e_add, AnArc.e_intCast, _root_.mul_one]`. Introduce `h`.

Take `⟨n, hn⟩` from `(ToricDict.expChar_eq_one_iff (l - l')).1 (MonoidHom.ext fun x => Units.ext (by`. Express the relevant statement in the definitionally equal form `eTwoPi (l x.toAdd - l' x.toAdd) = 1`. Use `mul_right_cancel₀ (AnArc.e_ne_zero (l' x.toAdd)) ?_` and prove the remaining obligations. Rewrite using `[← AnArc.e_add, sub_add_cancel, h, _root_.one_mul]))`. Conclude with `⟨AnArc.La.mk 0 n 0, rfl, Prod.ext (AddMonoidHom.ext fun x => by simpa using hn x) (by simp)⟩`.
-/
theorem ex₀_eq_iff_char (l l' : d.A.X →+ ℂ) (z : Fin d.A.gB → ℂ) :
    d.ex₀ (l, z) = d.ex₀ (l', z) ↔ ∀ x, eTwoPi (l x) = eTwoPi (l' x) := by
  rw [d.ex₀_eq_iff]
  constructor
  · rintro ⟨la, hy, e⟩ x
    have hl : la.l = 0 := Subtype.ext (by simpa [hy] using (congrArg Prod.snd e).symm)
    have : l x = l' x + (la.n x : ℤ) := by
      have := congrArg (fun v : d.A.V => v.1 x) e
      simp [hy, hl] at this
      linear_combination this
    rw [this, AnArc.e_add, AnArc.e_intCast, _root_.mul_one]
  · intro h
    obtain ⟨n, hn⟩ := (ToricDict.expChar_eq_one_iff (l - l')).1 (MonoidHom.ext fun x => Units.ext (by
      change eTwoPi (l x.toAdd - l' x.toAdd) = 1
      refine mul_right_cancel₀ (AnArc.e_ne_zero (l' x.toAdd)) ?_
      rw [← AnArc.e_add, sub_add_cancel, h, _root_.one_mul]))
    exact ⟨AnArc.La.mk 0 n 0, rfl, Prod.ext (AddMonoidHom.ext fun x => by simpa using hn x) (by simp)⟩

/- English proof (translation)
Take `⟨-, -, -, -, t1, t2, -⟩` from `AHWeil.tangent_and_weil_of_isAH hT D₀.P _ d.u _ _ d.isAH`. Set `j₀ : 𝟙_ (Over (Sp ℂ)) ⟶ Out.TF (R` to `ℂ) ℂ := Over.homMk (𝟙 (Sp ℂ)) ((Category.id_comp _).trans AbelianLetters.tf_hom)`. Establish `hj : ∀ z, (j₀ ≫ (ex z).b).left = (show Sp ℂ ⟶ _ from (ex z).b.left)` using `fun z => Category.id_comp _`. Take `⟨F, hF, -⟩` from `existsUnique_linear_lift_of_isHolTo D₀.P.A D₀.P.isAb D₀.P.L _ g d.u t1 t2 (fun z => j₀ ≫ (ex z).b) (fun z w => by rw [AbelianLetters.b_add add, MonObj.comp_mul]) (by simpa only [hj] using hol_b)`. Establish `hb : ∀ z l, (d.ex₀ (l, F z)).b = (ex z).b` using `fun z l => Over.OverMorphism.ext ((d.ex₀_b_left _).trans ((congrArg (·.left) (hF z)).trans (hj z)))`.

Establish `hv : ∀ z, ∃ l, d.ex₀ (l, F z) = ex z` using `fun z => by`. Take `⟨v, hv⟩` from `d.onto (ex z)`. Establish `e : d.u.ex v.2 = d.u.ex (F z)` using `Over.OverMorphism.ext ((d.ex₀_b_left v).symm.trans (Eq.trans (by rw [hv, hb]) (d.ex₀_b_left (0, F z))))`. Establish `hm : v.2 - F z ∈ d.A.abelian₂`. Use `d.lam_eq.le ((d.u.ker _).1 ?_)` and prove the remaining obligations.

Use `d.u.ex_add (v.2 - F z) (F z)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, e]`. Conclude with `right_eq_mul.1 this`. Use `⟨(v - d.A.P0 (AnArc.La.mk 0 0 ⟨_, hm⟩)).1, Eq.trans (Eq.symm ?_) hv⟩` and prove the remaining obligations. Use `(d.ex₀_eq_iff _ _).2 ⟨AnArc.La.mk 0 0 ⟨_, hm⟩, rfl, Prod.ext (by simp) (by simp)⟩` and prove the remaining obligations.

Use `choose l hl using hv`. Establish `hmul : ∀ x z z', eTwoPi (l (z + z') x) = eTwoPi (l z x) * eTwoPi (l z' x)` using `fun x z z' => by`. Establish `h` using `d.add (l z, F z) (l z', F z')`. Rewrite `h` using `[hl, hl, Prod.mk_add_mk, ← map_add]`. Rewrite using `[(ex₀_eq_iff_char d _ _ _).1 ((hl _).trans (TorusExt.isAdd_unique (add z z') h)) x, AddMonoidHom.add_apply, AnArc.e_add]`.

Establish `hd : ∀ x, DifferentiableAt ℂ (fun z => eTwoPi (l z x)) 0` using `fun x => by choose j hj using fun k : Fin 4 => exists_chart_complexPoint D₀.P.isLB (d.u.ex (![d.A.ct x + F 0, d.A.ct x, F 0, 0] k)).left`. Establish `hFd : Differentiable ℂ F` using `(LinearMap.toContinuousLinearMap F).differentiable`. Establish `hS : ∀ z, ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφ D₀ ℂ (ex z).b (d.eX x)) j ↔ ∀ k, ⊤ ≤ (d.u.ex (![d.A.ct x + F z, d.A.ct x, F z, 0] k)).left ⁻¹ᵁ D₀.P.L.U (j k)` using `fun z => by`. Rewrite using `[← hb z 0]`. Conclude with `d.top_le_gtChart_iff (0, F z) x j`.

Establish `ho : {z | ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφ D₀ ℂ (ex z).b (d.eX x)) j} ∈ nhds (0 : Fin g → ℂ)`. Simplify using `only [hS]`. Use `Filter.eventually_all.2 fun k => ?_` and prove the remaining obligations. Use `((d.u.hol (D₀.P.L.U (j k)) 0).1.preimage (f := fun z => ![d.A.ct x + F z, d.A.ct x, F z, 0] k) ?_).mem_nhds (hj k)` and prove the remaining obligations. Use `hFd.continuous` as an intermediate fact.

Apply the tactic sequence `fin_cases k <;> simp <;> fun_prop`. Establish `h₂` using `(d.hol_chi (d.eX x) j).comp (f := fun z => ((0, F z) : d.A.V)) (s := {z | ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφ D₀ ℂ (ex z).b (d.eX x)) j}) ((differentiable_const _).prodMk hFd).differentiableOn (fun z hz => by`. Rewrite using `[Set.mem_setOf_eq, hb]`. Conclude with `hz)`. Establish `c₀ : ∀ z, ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφ D₀ ℂ (ex z).b (d.eX x)) j → ∀ l', chiVal (d.ex₀ (l', F z)) (d.eX x) j = eTwoPi (l' x) * frameProd d.u j ![d.A.ct x + F z, d.A.ct x, F z, 0] Out.DegPre.gtε` using `fun z hz l' => d.chi_val (l', F z) x j (by rw [hb]; exact hz)`.

Establish `n₀ : ∀ z, ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφ D₀ ℂ (ex z).b (d.eX x)) j → chiVal (d.ex₀ (0, F z)) (d.eX x) j ≠ 0` using `fun z hz => by`. Rewrite using `[c₀ z hz]`. Conclude with `mul_ne_zero (AnArc.e_ne_zero _) (frameProd_ne_zero d.u _ ((hS z).1 hz))`. Use `(((hol_chi (d.eX x) j).mul (h₂.inv n₀)).congr fun z hz => ?_).differentiableAt ho` and prove the remaining obligations. Use `eq_div_of_mul_eq (n₀ z hz) ?_` and prove the remaining obligations.

Use `c₀ z hz (l z)` as an intermediate fact. Rewrite `this` using `[hl]`. Use `beta_reduce`. Rewrite using `[this, Function.comp_apply, c₀ z hz]`. Simplify using the standard rewrite rules.

Set `L : d.A.X → (Fin g → ℂ) →L[ℂ] ℂ` to `fun x => fderiv ℂ (fun z => eTwoPi (l z x)) 0`. Establish `hL : ∀ x z, eTwoPi (l z x) = Complex.exp (L x z)` using `fun x => Doubling.eq_cexp_fderiv_of_map_add (hd x) (AnArc.e_ne_zero _) (hmul x)`. Establish `hadd : ∀ x x' z, L (x + x') z = L x z + L x' z` using `fun x x' z => by`. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_forall_smul_mem_countable (Set.countable_range fun n : ℤ => (n : ℂ) * (2 * Real.pi * Complex.I)) fun s => ?_` and prove the remaining obligations.

Take `⟨n, hn⟩` from `Complex.exp_eq_exp_iff_exists_int.1 (show Complex.exp (L (x + x') (s • z)) = Complex.exp (L x (s • z) + L x' (s • z)) by`. Rewrite using `[Complex.exp_add, ← hL, ← hL, ← hL, map_add, AnArc.e_add])`. Use `⟨n, ?_⟩` and prove the remaining obligations. Simplify using `only [map_smul, smul_eq_mul] at hn ⊢`. Take the linear combination `-hn`.

Set `h₁ : (Fin g → ℂ) →ₗ[ℂ] (d.A.X →+ ℂ)` to `{ toFun := fun z => AddMonoidHom.mk' (fun x => (2 * Real.pi * Complex.I)⁻¹ * L x z) fun x x' => by`. Rewrite using `[hadd, mul_add]`. Use the proof step `map_add' := fun z z' => AddMonoidHom.ext fun x => by simp [mul_add]`. Use the proof step `map_smul' := fun s z => AddMonoidHom.ext fun x => by simp [mul_left_comm s] }`. Use `⟨h₁.prod F, fun z => Eq.trans ((ex₀_eq_iff_char d _ _ _).2 fun x => ?_) (hl z)⟩` and prove the remaining obligations.

Rewrite using `[hL]`. Conclude with `congrArg Complex.exp (mul_inv_cancel_left₀ Complex.two_pi_I_ne_zero _)`.
-/
theorem exists_linear (hT : ThetaUnifAV) {g : ℕ} (ex : (Fin g → ℂ) → Out.GtPtF D₀ ℂ)
    (add : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z')))
    (hol_b : IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)))
    (hol_chi : ∀ x j, DifferentiableOn ℂ (fun z => chiVal (ex z) x j)
      {z | ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφ D₀ ℂ (ex z).b x) j}) :
    ∃ h : (Fin g → ℂ) →ₗ[ℂ] d.A.V, ∀ z, d.ex₀ (h z) = ex z := by
  obtain ⟨-, -, -, -, t1, t2, -⟩ := AHWeil.tangent_and_weil_of_isAH hT D₀.P _ d.u _ _ d.isAH
  let j₀ : 𝟙_ (Over (Sp ℂ)) ⟶ Out.TF (R := ℂ) ℂ :=
    Over.homMk (𝟙 (Sp ℂ)) ((Category.id_comp _).trans AbelianLetters.tf_hom)
  have hj : ∀ z, (j₀ ≫ (ex z).b).left = (show Sp ℂ ⟶ _ from (ex z).b.left) := fun z => Category.id_comp _
  obtain ⟨F, hF, -⟩ := existsUnique_linear_lift_of_isHolTo D₀.P.A D₀.P.isAb D₀.P.L _ g d.u t1 t2
    (fun z => j₀ ≫ (ex z).b) (fun z w => by rw [AbelianLetters.b_add add, MonObj.comp_mul])
    (by simpa only [hj] using hol_b)
  have hb : ∀ z l, (d.ex₀ (l, F z)).b = (ex z).b := fun z l =>
    Over.OverMorphism.ext ((d.ex₀_b_left _).trans ((congrArg (·.left) (hF z)).trans (hj z)))
  have hv : ∀ z, ∃ l, d.ex₀ (l, F z) = ex z := fun z => by
    obtain ⟨v, hv⟩ := d.onto (ex z)
    have e : d.u.ex v.2 = d.u.ex (F z) := Over.OverMorphism.ext
      ((d.ex₀_b_left v).symm.trans (Eq.trans (by rw [hv, hb]) (d.ex₀_b_left (0, F z))))
    have hm : v.2 - F z ∈ d.A.abelian₂ := by
      refine d.lam_eq.le ((d.u.ker _).1 ?_)
      have := d.u.ex_add (v.2 - F z) (F z)
      rw [sub_add_cancel, e] at this
      exact right_eq_mul.1 this
    refine ⟨(v - d.A.P0 (AnArc.La.mk 0 0 ⟨_, hm⟩)).1, Eq.trans (Eq.symm ?_) hv⟩
    refine (d.ex₀_eq_iff _ _).2 ⟨AnArc.La.mk 0 0 ⟨_, hm⟩, rfl, Prod.ext (by simp) (by simp)⟩
  choose l hl using hv
  have hmul : ∀ x z z', eTwoPi (l (z + z') x) = eTwoPi (l z x) * eTwoPi (l z' x) := fun x z z' => by
    have h := d.add (l z, F z) (l z', F z')
    rw [hl, hl, Prod.mk_add_mk, ← map_add] at h
    rw [(ex₀_eq_iff_char d _ _ _).1 ((hl _).trans (TorusExt.isAdd_unique (add z z') h)) x, AddMonoidHom.add_apply,
      AnArc.e_add]
  have hd : ∀ x, DifferentiableAt ℂ (fun z => eTwoPi (l z x)) 0 := fun x => by
    choose j hj using fun k : Fin 4 =>
      exists_chart_complexPoint D₀.P.isLB (d.u.ex (![d.A.ct x + F 0, d.A.ct x, F 0, 0] k)).left
    have hFd : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
    have hS : ∀ z, ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφ D₀ ℂ (ex z).b (d.eX x)) j ↔
        ∀ k, ⊤ ≤ (d.u.ex (![d.A.ct x + F z, d.A.ct x, F z, 0] k)).left ⁻¹ᵁ D₀.P.L.U (j k) := fun z => by
      rw [← hb z 0]
      exact d.top_le_gtChart_iff (0, F z) x j
    have ho : {z | ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφ D₀ ℂ (ex z).b (d.eX x)) j} ∈ nhds (0 : Fin g → ℂ) := by
      simp only [hS]
      refine Filter.eventually_all.2 fun k => ?_
      refine ((d.u.hol (D₀.P.L.U (j k)) 0).1.preimage
        (f := fun z => ![d.A.ct x + F z, d.A.ct x, F z, 0] k) ?_).mem_nhds (hj k)
      have := hFd.continuous
      fin_cases k <;> simp <;> fun_prop
    have h₂ := (d.hol_chi (d.eX x) j).comp (f := fun z => ((0, F z) : d.A.V))
      (s := {z | ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφ D₀ ℂ (ex z).b (d.eX x)) j})
      ((differentiable_const _).prodMk hFd).differentiableOn (fun z hz => by
        rw [Set.mem_setOf_eq, hb]; exact hz)
    have c₀ : ∀ z, ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφ D₀ ℂ (ex z).b (d.eX x)) j → ∀ l',
        chiVal (d.ex₀ (l', F z)) (d.eX x) j =
          eTwoPi (l' x) * frameProd d.u j ![d.A.ct x + F z, d.A.ct x, F z, 0] Out.DegPre.gtε := fun z hz l' =>
      d.chi_val (l', F z) x j (by rw [hb]; exact hz)
    have n₀ : ∀ z, ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφ D₀ ℂ (ex z).b (d.eX x)) j →
        chiVal (d.ex₀ (0, F z)) (d.eX x) j ≠ 0 := fun z hz => by
      rw [c₀ z hz]
      exact mul_ne_zero (AnArc.e_ne_zero _) (frameProd_ne_zero d.u _ ((hS z).1 hz))
    refine (((hol_chi (d.eX x) j).mul (h₂.inv n₀)).congr fun z hz => ?_).differentiableAt ho
    refine eq_div_of_mul_eq (n₀ z hz) ?_
    have := c₀ z hz (l z)
    rw [hl] at this
    beta_reduce
    rw [this, Function.comp_apply, c₀ z hz]
    simp
  let L : d.A.X → (Fin g → ℂ) →L[ℂ] ℂ := fun x => fderiv ℂ (fun z => eTwoPi (l z x)) 0
  have hL : ∀ x z, eTwoPi (l z x) = Complex.exp (L x z) := fun x =>
    Doubling.eq_cexp_fderiv_of_map_add (hd x) (AnArc.e_ne_zero _) (hmul x)
  have hadd : ∀ x x' z, L (x + x') z = L x z + L x' z := fun x x' z => by
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_smul_mem_countable
      (Set.countable_range fun n : ℤ => (n : ℂ) * (2 * Real.pi * Complex.I)) fun s => ?_
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1
      (show Complex.exp (L (x + x') (s • z)) = Complex.exp (L x (s • z) + L x' (s • z)) by
        rw [Complex.exp_add, ← hL, ← hL, ← hL, map_add, AnArc.e_add])
    refine ⟨n, ?_⟩
    simp only [map_smul, smul_eq_mul] at hn ⊢
    linear_combination -hn
  let h₁ : (Fin g → ℂ) →ₗ[ℂ] (d.A.X →+ ℂ) :=
    { toFun := fun z => AddMonoidHom.mk' (fun x => (2 * Real.pi * Complex.I)⁻¹ * L x z) fun x x' => by
        rw [hadd, mul_add]
      map_add' := fun z z' => AddMonoidHom.ext fun x => by simp [mul_add]
      map_smul' := fun s z => AddMonoidHom.ext fun x => by simp [mul_left_comm s] }
  refine ⟨h₁.prod F, fun z => Eq.trans ((ex₀_eq_iff_char d _ _ _).2 fun x => ?_) (hl z)⟩
  rw [hL]
  exact congrArg Complex.exp (mul_inv_cancel_left₀ Complex.two_pi_I_ne_zero _)

/- English proof (translation)
Establish `: Countable d.A.La` using `Finsupp.Countable.of_moduleFinite (R := ℤ)`. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_forall_smul_mem_countable (Set.countable_range d.A.P0) fun s => ?_` and prove the remaining obligations. Take `⟨la, -, e⟩` from `(d.ex₀_eq_iff _ _).1 (h s)`. Conclude with `⟨la, by rw [← e, smul_sub]⟩`.
-/
theorem eq_of_ex₀_smul {v v' : d.A.V} (h : ∀ s : ℂ, d.ex₀ (s • v) = d.ex₀ (s • v')) : v = v' := by
  have : Countable d.A.La := Finsupp.Countable.of_moduleFinite (R := ℤ)
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_smul_mem_countable (Set.countable_range d.A.P0) fun s => ?_
  obtain ⟨la, -, e⟩ := (d.ex₀_eq_iff _ _).1 (h s)
  exact ⟨la, by rw [← e, smul_sub]⟩

end Dict

section Form

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

/- English proof (translation)
Establish `hl : m.l = m'.l` using `Subtype.ext (by simpa [hy] using congrArg Prod.snd e)`. Use `AnArc.La.ext hy (AddMonoidHom.ext fun x => ?_) hl` and prove the remaining obligations. Simplify `congrArg (fun v : A.V => v.1 x) e` using `[hy, hl]`.
-/
theorem la_ext {m m' : A.La} (hy : m.y = m'.y) (e : A.P0 m = A.P0 m') : m = m' := by
  have hl : m.l = m'.l := Subtype.ext (by simpa [hy] using congrArg Prod.snd e)
  refine AnArc.La.ext hy (AddMonoidHom.ext fun x => ?_) hl
  simpa [hy, hl] using congrArg (fun v : A.V => v.1 x) e

/- English proof (translation)
Establish `hc : ∀ (s : ℂ) a, D a = 0 → D (s • a) = 0` using `fun s a ha => by`. Establish `e : s • a = s.re • a + s.im • (Complex.I • a)` using `by conv_lhs => rw [← Complex.re_add_im s]`. Rewrite using `[add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]`. Establish `: D (Complex.I • a) = 0` using `LinearMap.ext fun b => by rw [hI, ha]; simp`. Rewrite using `[e, map_add, map_smul, map_smul, ha, this, smul_zero, smul_zero, add_zero]`.

Establish `hT : ∀ a : A.V, a.2 = 0 → D a = 0` using `fun a ha => by`. Set `b` to `Module.Free.chooseBasis ℤ A.X`. Establish `e : a = ∑ i, a.1 (b i) • A.P0 (AnArc.La.mk 0 (b.coord i).toAddMonoidHom 0)`. Use `Prod.ext (A.coord.injective (funext fun k => ?_)) (by simp [ha, Prod.snd_sum])` and prove the remaining obligations. Simplify using `[Prod.fst_sum, AnArc.coord_apply, b, Finsupp.single_apply]`.

Rewrite using `[e, map_sum]`. Conclude with `Finset.sum_eq_zero fun i _ => hc _ _ (h₁ _)`. Set `s : Set A.V` to `{a | a.2 = 0} ∪ Set.range fun l => A.P0 (AnArc.La.mk 0 0 l)`. Establish `hs : Submodule.span ℝ s = ⊤`. Use `eq_top_iff.2 fun a _ => ?_` and prove the remaining obligations.

Establish `: ∀ z ∈ Submodule.span ℝ (A.abelian₂ : Set (Fin A.gB → ℂ)), ∃ p ∈ Submodule.span ℝ s, p.2 = z` using `fun z hz => by`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz => exact ⟨_, Submodule.subset_span (Or.inr ⟨⟨z, hz⟩, rfl⟩), by simp⟩`. Consider the case `zero => exact ⟨0, zero_mem _, rfl⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨p, hp, rfl⟩` from `hx`. Take `⟨q, hq, rfl⟩` from `hy`. Conclude with `⟨p + q, add_mem hp hq, rfl⟩`. Consider the case `smul r x _ hx`. Take `⟨p, hp, rfl⟩` from `hx`.

Conclude with `⟨r • p, Submodule.smul_mem _ _ hp, rfl⟩`. Take `⟨p, hp, e⟩` from `this a.2 (A.full ▸ Submodule.mem_top)`. Rewrite using `[← sub_add_cancel a p]`. Conclude with `add_mem (Submodule.subset_span (Or.inl (by simp [e]))) hp`. Use `LinearMap.ext_on hs ?_` and prove the remaining obligations.

Introduce and unpack `a (ha | ⟨l, rfl⟩)`. Conclude with `hT a ha`. Use `LinearMap.ext_on hs ?_` and prove the remaining obligations. Introduce and unpack `b (hb | ⟨m, rfl⟩)`. Rewrite using `[alt, hT b hb]`.

Simplify using the standard rewrite rules. Conclude with `h₂ l m`.
-/
theorem form_eq_zero (D : A.V →ₗ[ℝ] A.V →ₗ[ℝ] ℝ) (alt : ∀ a b, D a b = -D b a)
    (hI : ∀ a b, D (Complex.I • a) b = -D a (Complex.I • b)) (h₁ : ∀ n, D (A.P0 (AnArc.La.mk 0 n 0)) = 0)
    (h₂ : ∀ l m, D (A.P0 (AnArc.La.mk 0 0 l)) (A.P0 (AnArc.La.mk 0 0 m)) = 0) : D = 0 := by
  classical
  have hc : ∀ (s : ℂ) a, D a = 0 → D (s • a) = 0 := fun s a ha => by
    have e : s • a = s.re • a + s.im • (Complex.I • a) := by
      conv_lhs => rw [← Complex.re_add_im s]
      rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
    have : D (Complex.I • a) = 0 := LinearMap.ext fun b => by rw [hI, ha]; simp
    rw [e, map_add, map_smul, map_smul, ha, this, smul_zero, smul_zero, add_zero]
  have hT : ∀ a : A.V, a.2 = 0 → D a = 0 := fun a ha => by
    let b := Module.Free.chooseBasis ℤ A.X
    have e : a = ∑ i, a.1 (b i) • A.P0 (AnArc.La.mk 0 (b.coord i).toAddMonoidHom 0) := by
      refine Prod.ext (A.coord.injective (funext fun k => ?_)) (by simp [ha, Prod.snd_sum])
      simp [Prod.fst_sum, AnArc.coord_apply, b, Finsupp.single_apply]
    rw [e, map_sum]
    exact Finset.sum_eq_zero fun i _ => hc _ _ (h₁ _)
  let s : Set A.V := {a | a.2 = 0} ∪ Set.range fun l => A.P0 (AnArc.La.mk 0 0 l)
  have hs : Submodule.span ℝ s = ⊤ := by
    refine eq_top_iff.2 fun a _ => ?_
    have : ∀ z ∈ Submodule.span ℝ (A.abelian₂ : Set (Fin A.gB → ℂ)), ∃ p ∈ Submodule.span ℝ s, p.2 = z := fun z hz => by
      induction hz using Submodule.span_induction with
      | mem z hz => exact ⟨_, Submodule.subset_span (Or.inr ⟨⟨z, hz⟩, rfl⟩), by simp⟩
      | zero => exact ⟨0, zero_mem _, rfl⟩
      | add x y _ _ hx hy =>
        obtain ⟨p, hp, rfl⟩ := hx
        obtain ⟨q, hq, rfl⟩ := hy
        exact ⟨p + q, add_mem hp hq, rfl⟩
      | smul r x _ hx =>
        obtain ⟨p, hp, rfl⟩ := hx
        exact ⟨r • p, Submodule.smul_mem _ _ hp, rfl⟩
    obtain ⟨p, hp, e⟩ := this a.2 (A.full ▸ Submodule.mem_top)
    rw [← sub_add_cancel a p]
    exact add_mem (Submodule.subset_span (Or.inl (by simp [e]))) hp
  refine LinearMap.ext_on hs ?_
  rintro a (ha | ⟨l, rfl⟩)
  · exact hT a ha
  · refine LinearMap.ext_on hs ?_
    rintro b (hb | ⟨m, rfl⟩)
    · rw [alt, hT b hb]; simp
    · exact h₂ l m

open AppellHumbertTrivial in

/- English proof (translation)
Set `D : A.V →ₗ[ℝ] A.V →ₗ[ℝ] ℝ` to `LinearMap.mk₂ ℝ (fun p q => (hermForm Hm (k p) (k q)).im - (A.Hw w p q).im) (fun p p' q => by simp only [map_add, LinearMap.add_apply, hermForm_add_left, Complex.add_im]; ring) (fun r p q => by`. Rewrite using `[← Complex.coe_smul, map_smul, map_smul, hermForm_smul_left, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, Complex.im_ofReal_mul, Complex.im_ofReal_mul, mul_sub])`. Use the proof step `(fun p q q' => by simp only [map_add, hermForm_add_right, Complex.add_im]; ring)`. Use the proof step `(fun r p q => by`. Rewrite using `[← Complex.coe_smul, map_smul, map_smulₛₗ, hermForm_smul_right, Complex.star_def, Complex.conj_ofReal, smul_eq_mul, smul_eq_mul, Complex.im_ofReal_mul, Complex.im_ofReal_mul, mul_sub])`.

Establish `hD : ∀ p q, D p q = (hermForm Hm (k p) (k q)).im - (A.Hw w p q).im` using `fun _ _ => rfl`. Establish `hD0 : D = 0`. Use `form_eq_zero A D (fun p q => ?_) (fun p q => ?_) (fun n => ?_) (fun m m' => ?_)` and prove the remaining obligations. Rewrite using `[hD, hD, ← A.Hw_conj w q p, hermForm_swap hH, Complex.star_def, Complex.conj_im, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hD, hD, map_smul, map_smul, map_smul, map_smulₛₗ, hermForm_smul_left, hermForm_smul_right, LinearMap.smul_apply]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Use `LinearMap.ext_on (A.Pw_lattice hw).2.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨m, rfl⟩`.

Rewrite using `[← A.degeneratingTori_periodMap_eq_base_of_y_eq_zero w rfl, hD, h₁, A.im_Hw_Pw hw, sub_self, LinearMap.zero_apply]`. Rewrite using `[← A.degeneratingTori_periodMap_eq_base_of_y_eq_zero w rfl, ← A.degeneratingTori_periodMap_eq_base_of_y_eq_zero w rfl, hD, h₂, A.im_Hw_Pw hw, sub_self]`. Use `hD (A.Pw w a) (A.Pw w b)` as an intermediate fact. Rewrite `this` using `[hD0, A.im_Hw_Pw hw]`. Conclude with `sub_eq_zero.1 this.symm`.
-/
theorem im_eq_EF {w : ℂ} (hw : (A.BwMat w).PosDef) {g : ℕ} (k : A.V →ₗ[ℂ] (Fin g → ℂ))
    {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (h₁ : ∀ n m, (hermForm Hm (k (A.Pw w (AnArc.La.mk 0 n 0))) (k (A.Pw w m))).im = A.EF (AnArc.La.mk 0 n 0) m)
    (h₂ : ∀ l m, (hermForm Hm (k (A.Pw w (AnArc.La.mk 0 0 l))) (k (A.Pw w (AnArc.La.mk 0 0 m)))).im =
      A.EF (AnArc.La.mk 0 0 l) (AnArc.La.mk 0 0 m)) (a b : A.La) :
    (hermForm Hm (k (A.Pw w a)) (k (A.Pw w b))).im = A.EF a b := by
  let D : A.V →ₗ[ℝ] A.V →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ
    (fun p q => (hermForm Hm (k p) (k q)).im - (A.Hw w p q).im)
    (fun p p' q => by simp only [map_add, LinearMap.add_apply, hermForm_add_left, Complex.add_im]; ring)
    (fun r p q => by
      rw [← Complex.coe_smul, map_smul, map_smul, hermForm_smul_left, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
        Complex.im_ofReal_mul, Complex.im_ofReal_mul, mul_sub])
    (fun p q q' => by simp only [map_add, hermForm_add_right, Complex.add_im]; ring)
    (fun r p q => by
      rw [← Complex.coe_smul, map_smul, map_smulₛₗ, hermForm_smul_right, Complex.star_def, Complex.conj_ofReal,
        smul_eq_mul, smul_eq_mul, Complex.im_ofReal_mul, Complex.im_ofReal_mul, mul_sub])
  have hD : ∀ p q, D p q = (hermForm Hm (k p) (k q)).im - (A.Hw w p q).im := fun _ _ => rfl
  have hD0 : D = 0 := by
    refine form_eq_zero A D (fun p q => ?_) (fun p q => ?_) (fun n => ?_) (fun m m' => ?_)
    · rw [hD, hD, ← A.Hw_conj w q p, hermForm_swap hH, Complex.star_def, Complex.conj_im, Complex.conj_im]
      ring
    · rw [hD, hD, map_smul, map_smul, map_smul, map_smulₛₗ, hermForm_smul_left, hermForm_smul_right,
        LinearMap.smul_apply]
      simp
      ring
    · refine LinearMap.ext_on (A.Pw_lattice hw).2.2 ?_
      rintro _ ⟨m, rfl⟩
      rw [← A.degeneratingTori_periodMap_eq_base_of_y_eq_zero w rfl, hD, h₁, A.im_Hw_Pw hw, sub_self, LinearMap.zero_apply]
    · rw [← A.degeneratingTori_periodMap_eq_base_of_y_eq_zero w rfl, ← A.degeneratingTori_periodMap_eq_base_of_y_eq_zero w rfl, hD, h₂, A.im_Hw_Pw hw, sub_self]
  have := hD (A.Pw w a) (A.Pw w b)
  rw [hD0, A.im_Hw_Pw hw] at this
  exact sub_eq_zero.1 this.symm

end Form

section ThetaShiftProofs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]
  {σ : c.F →+* ℂ} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {a : ArcIn Dw l β ℂ (σ.comp β)}
  {χ : Sp (PowerSeries ℂ) ⟶ Y.X} {W : Wit Y a χ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty} (Ha : HolArc Y σ a χ W Fu)

open AbelianLetters AppellHumbertTrivial in

/- English proof (translation)
Establish `hw : Ha.T < ((Ha.T + 1 : ℝ) * Complex.I).im` using `by simp`. Generalize the expression as in `(Ha.T + 1 : ℝ) * Complex.I = w at hw`. Establish `hty : IsTypeFn H Dw.p Dw.q ty`. Rewrite using `[← (Fu.sig Ha.i).1, ← (Fu.sig Ha.i).2]`. Conclude with `PeriodCompare.isTypeFn_of_isPeriod (Ha.period _ hw)`.

Take `⟨th, hth⟩` from `(ThetaOverField.nonzero_generates hL hL2 ℂ a.D₀ ⟨fun _ => 0, fun _ _ => by simp⟩).2.2`. Take `⟨Θ⟩` from `T.arc_model_witness_extension hL hL2 E H Dw l Xo c σ O β Y a χ W g ty Fu Ha hty th hth`. Set `p : (Fin g ⊕ Fin g → ℤ) →+ (Fin g → ℂ)` to `(Ha.Pw w).comp Θ.bas.toAddMonoidHom`. Establish `hp : ∀ v, p v = Ha.Pw w (Θ.bas v)` using `fun _ => rfl`. Take `⟨wL, hwL⟩ : LBIso a.D₀.P.L (a.D₀.P.L.pull (𝟙 _))` from `LBIso.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ _ _ rfl) (PolBaseChange.lbIso_refl a.D₀.P.isLB)`.

Take `⟨fr, f₁, f₂, f₃, -, f₅⟩` from `Θ.onB w hw`. Take `⟨ρ, r₁, r₂, r₃⟩` from `T.exists_entire_unit_appellHumbert_frame_ratio a.D₀.P.A _ a.D₀.P.L a.D₀.P.L a.D₀.P.isLB a.D₀.P.isLB (𝟙 _) wL hwL g _ u Hm χ' hAH _ F (fun z => (Category.comp_id _).trans (hF z)) fr th _ f₁ f₂ f₃ f₅`. Take `⟨t₁, t₂, t₃⟩` from `T.thetaCharOff_ne_zero_differentiable_quasiPeriodic' g Θ.S (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.pos w hw).1 (Θ.pos w hw).2 Θ.half₁ Θ.half₂ Θ.c₁_S`. Establish `hfac : ∀ v, Ha.y (Θ.bas v) = 0 → ∃ a₁ b₁ : ℂ, a₁ ≠ 0 ∧ (∀ z, Θ.κ * thetaCharOff Θ.S (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec (z + p v)) = a₁ * Complex.exp (dotForm Θ.h (fun i => (v (.inr i) : ℂ)) z) * (Θ.κ * thetaCharOff Θ.S (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z))) ∧ ∀ z, Θ.κ * thetaCharOff Θ.S ( …`. Introduce `v hy`.

Take `⟨a₁, ha₁, ha⟩` from `t₃ (fun i => v (.inl i)) (fun i => v (.inr i)) ((Θ.ker v).1 hy)`. Establish `hl : F (p v) ∈ u.Λ` using `by rw [hp, hP _ _ hy]; exact hΛ _ hy`. Use `⟨a₁, χ' ⟨_, hl⟩ * Complex.exp (Real.pi / 2 * hermForm Hm (F (p v)) (F (p v))), ha₁, fun z => ?_, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_add, mulVec_period Θ.h (Θ.τ w) p (Θ.per w), ha]`. Simplify using `only [dotForm, LinearMap.coe_mk, AddHom.coe_mk]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[r₃ _ ⟨_, hl⟩ rfl, Complex.exp_add]`. Simplify using `only [piHerm, LinearMap.coe_mk, AddHom.coe_mk]`. Expand and normalize the polynomial expressions, which then agree. Establish `hθ : (fun z => Θ.κ * thetaCharOff Θ.S (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) ≠ 0` using `fun h0 => t₁ (funext fun y => by`.

Take `⟨z, rfl⟩` from `surjective_mulVec Θ.h _ (fun k => (Θ.per w k).1) y`. Conclude with `(mul_eq_zero.1 (congrFun h0 z)).resolve_left Θ.κ_ne)`. Establish `hθd : Differentiable ℂ (fun z => Θ.κ * thetaCharOff Θ.S (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z))` using `(t₂.comp (LinearMap.toContinuousLinearMap Θ.h.mulVecLin).differentiable).const_mul _`. Take `⟨v₁, rfl⟩` from `Θ.bas.surjective v₁`. Take `⟨v₂, rfl⟩` from `Θ.bas.surjective v₂`.

Take `⟨a₁, b₁, ha₁, e₁, e₁'⟩` from `hfac v₁ h₁`. Take `⟨a₂, b₂, ha₂, e₂, e₂'⟩` from `hfac v₂ h₂`. Establish `hc` using `T.factor_exponent_commutator_eq_of_quasiPeriodic g _ ρ _ _ _ _ _ _ a₁ a₂ b₁ b₂ hθd hθ r₁ r₂ ha₁ ha₂ e₁ e₂ e₁' e₂'`. Simplify using `only [piHerm, dotForm, LinearMap.coe_mk, AddHom.coe_mk, mulVec_period Θ.h (Θ.τ w) p (Θ.per w)] at hc`. Rewrite `hc` using `[hermForm_swap hAH.1]`.

Rewrite using `[← hP w _ h₁, ← hP w _ h₂, Θ.sympl]`. Conclude with `im_eq_neg_omega _ (Θ.pos w hw).1 v₁ v₂ _ hc`.
-/
theorem im_hermForm_eq (hL : Out.Laws) (hL2 : Out.Laws2) (hP : ∀ w v, Ha.y v = 0 → Ha.Pw w v = Ha.P₀ v) {n : ℕ}
    (u : HolUnif a.D₀.P.A a.D₀.P.L n) {Hm : Matrix (Fin n) (Fin n) ℂ} {χ' : u.Λ → ℂ} (hAH : u.IsAH Hm χ')
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (hF : ∀ z, (u.ex (F z)).left = (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left))
    (hΛ : ∀ v, Ha.y v = 0 → F (Ha.P₀ v) ∈ u.Λ) {v₁ v₂ : (Fu.Di Ha.i).La} (h₁ : Ha.y v₁ = 0) (h₂ : Ha.y v₂ = 0) :
    (hermForm Hm (F (Ha.P₀ v₁)) (F (Ha.P₀ v₂))).im = (Fu.Di Ha.i).EF v₁ v₂ := by
  have hw : Ha.T < ((Ha.T + 1 : ℝ) * Complex.I).im := by simp
  generalize (Ha.T + 1 : ℝ) * Complex.I = w at hw
  have hty : IsTypeFn H Dw.p Dw.q ty := by
    rw [← (Fu.sig Ha.i).1, ← (Fu.sig Ha.i).2]
    exact PeriodCompare.isTypeFn_of_isPeriod (Ha.period _ hw)
  obtain ⟨th, hth⟩ := (ThetaOverField.nonzero_generates hL hL2 ℂ a.D₀ ⟨fun _ => 0, fun _ _ => by simp⟩).2.2
  obtain ⟨Θ⟩ := T.arc_model_witness_extension hL hL2 E H Dw l Xo c σ O β Y a χ W g ty Fu Ha hty th hth
  let p : (Fin g ⊕ Fin g → ℤ) →+ (Fin g → ℂ) := (Ha.Pw w).comp Θ.bas.toAddMonoidHom
  have hp : ∀ v, p v = Ha.Pw w (Θ.bas v) := fun _ => rfl
  obtain ⟨wL, hwL⟩ : LBIso a.D₀.P.L (a.D₀.P.L.pull (𝟙 _)) :=
    LBIso.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ _ _ rfl) (PolBaseChange.lbIso_refl a.D₀.P.isLB)
  obtain ⟨fr, f₁, f₂, f₃, -, f₅⟩ := Θ.onB w hw
  obtain ⟨ρ, r₁, r₂, r₃⟩ := T.exists_entire_unit_appellHumbert_frame_ratio a.D₀.P.A _ a.D₀.P.L a.D₀.P.L a.D₀.P.isLB a.D₀.P.isLB (𝟙 _) wL hwL g _ u Hm χ' hAH
    _ F (fun z => (Category.comp_id _).trans (hF z)) fr th _ f₁ f₂ f₃ f₅
  obtain ⟨t₁, t₂, t₃⟩ := T.thetaCharOff_ne_zero_differentiable_quasiPeriodic' g Θ.S (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.pos w hw).1 (Θ.pos w hw).2 Θ.half₁ Θ.half₂ Θ.c₁_S
  have hfac : ∀ v, Ha.y (Θ.bas v) = 0 → ∃ a₁ b₁ : ℂ, a₁ ≠ 0 ∧
      (∀ z, Θ.κ * thetaCharOff Θ.S (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec (z + p v)) =
        a₁ * Complex.exp (dotForm Θ.h (fun i => (v (.inr i) : ℂ)) z) *
          (Θ.κ * thetaCharOff Θ.S (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z))) ∧
      ∀ z, Θ.κ * thetaCharOff Θ.S (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec (z + p v)) * ρ (z + p v) =
        b₁ * Complex.exp (piHerm Hm F (F (p v)) z) *
          (Θ.κ * thetaCharOff Θ.S (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) * ρ z) := by
    intro v hy
    obtain ⟨a₁, ha₁, ha⟩ := t₃ (fun i => v (.inl i)) (fun i => v (.inr i)) ((Θ.ker v).1 hy)
    have hl : F (p v) ∈ u.Λ := by rw [hp, hP _ _ hy]; exact hΛ _ hy
    refine ⟨a₁, χ' ⟨_, hl⟩ * Complex.exp (Real.pi / 2 * hermForm Hm (F (p v)) (F (p v))), ha₁, fun z => ?_,
      fun z => ?_⟩
    · rw [Matrix.mulVec_add, mulVec_period Θ.h (Θ.τ w) p (Θ.per w), ha]
      simp only [dotForm, LinearMap.coe_mk, AddHom.coe_mk]
      ring
    · rw [r₃ _ ⟨_, hl⟩ rfl, Complex.exp_add]
      simp only [piHerm, LinearMap.coe_mk, AddHom.coe_mk]
      ring
  have hθ : (fun z => Θ.κ * thetaCharOff Θ.S (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) ≠ 0 := fun h0 => t₁ (funext fun y => by
    obtain ⟨z, rfl⟩ := surjective_mulVec Θ.h _ (fun k => (Θ.per w k).1) y
    exact (mul_eq_zero.1 (congrFun h0 z)).resolve_left Θ.κ_ne)
  have hθd : Differentiable ℂ (fun z => Θ.κ * thetaCharOff Θ.S (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) :=
    (t₂.comp (LinearMap.toContinuousLinearMap Θ.h.mulVecLin).differentiable).const_mul _
  obtain ⟨v₁, rfl⟩ := Θ.bas.surjective v₁
  obtain ⟨v₂, rfl⟩ := Θ.bas.surjective v₂
  obtain ⟨a₁, b₁, ha₁, e₁, e₁'⟩ := hfac v₁ h₁
  obtain ⟨a₂, b₂, ha₂, e₂, e₂'⟩ := hfac v₂ h₂
  have hc := T.factor_exponent_commutator_eq_of_quasiPeriodic g _ ρ _ _ _ _ _ _ a₁ a₂ b₁ b₂ hθd hθ r₁ r₂ ha₁ ha₂ e₁ e₂ e₁' e₂'
  simp only [piHerm, dotForm, LinearMap.coe_mk, AddHom.coe_mk, mulVec_period Θ.h (Θ.τ w) p (Θ.per w)] at hc
  rw [hermForm_swap hAH.1] at hc
  rw [← hP w _ h₁, ← hP w _ h₂, Θ.sympl]
  exact im_eq_neg_omega _ (Θ.pos w hw).1 v₁ v₂ _ hc

end ThetaShiftProofs

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `hK E _ _ _ H Dw l Xo c _ _ σ O _ β Y a χ W g ty Fu Ha Λ`. Use `letI := H.starRing`. Use `letI := TorusExt.gtGroup a.D₀ ℂ`. Establish `hO : Countable (𝓞 E)` using `Finsupp.Countable.of_moduleFinite (R := ℤ)`. Establish `hfin` using `(Fu.Di Ha.i).fin`.

Establish `cL : Countable (Fu.Di Ha.i).La` using `Finsupp.Countable.of_moduleFinite (R := 𝓞 E)`. Establish `cA : Countable Λ.A.La` using `Finsupp.Countable.of_moduleFinite (R := ℤ)`. Take `⟨nn, hN, -, -, hnn, -, hξ⟩` from `holArc_nilpotent E H Dw l Xo c σ O β Y a χ W g ty Fu Ha`. Establish `hP : ∀ w v, Ha.y v = 0 → Ha.Pw w v = Ha.P₀ v` using `fun w v hv => by`. Rewrite using `[Ha.Pw_eq, hN, hnn v hv, map_zero, smul_zero, add_zero]`.

Take `⟨h₀, hh₀⟩` from `exists_linear Λ.toGtDict hK.theta Ha.ex₀ Ha.add Ha.hol_b Ha.hol_chi`. Establish `hinj : Function.Injective h₀` using `(injective_iff_map_eq_zero h₀).2 fun z hz => eq_zero_of_forall_smul_mem_countable (Set.countable_range Ha.P₀) fun s => by`. Take `⟨v, -, e⟩` from `(Ha.ker (s • z)).1 (by`. Rewrite using `[← hh₀, map_smul, hz, smul_zero]`. Conclude with `Λ.toGtDict.isZero_ex₀_zero)`.

Conclude with `⟨v, e.symm⟩`. Establish `hsurj : Function.Surjective h₀` using `FibreUnif.surjective_of_countable h₀ (Set.countable_range Λ.A.P0) fun v => by`. Take `⟨z, hz⟩` from `Ha.onto (Λ.ex₀ v)`. Take `⟨la, -, e⟩` from `(Λ.toGtDict.ex₀_eq_iff v (h₀ z)).1 (by rw [hh₀, hz])`. Conclude with `⟨z, la, e.symm⟩`.

Set `h` to `LinearEquiv.ofBijective h₀ ⟨hinj, hsurj⟩`. Establish `hh : ∀ z, Λ.ex₀ (h z) = Ha.ex₀ z` using `hh₀`. Use `clear_value h`. Use `clear hh₀ hinj hsurj h₀`. Establish `hext : ∀ m m', Λ.y m = Λ.y m' → Λ.A.P0 m = Λ.A.P0 m' → m = m'` using `fun m m' hy => la_ext Λ.A (Λ.eX.injective hy)`.

Establish `hg : ∀ v, ∃ m, Λ.y m = Ha.y v ∧ Λ.A.P0 m = h (Ha.P₀ v)` using `fun v => by`. Take `⟨m, hm⟩` from `Λ.y_onto (Ha.y v)`. Take `⟨n, hn, e⟩` from `(Λ.toGtDict.ex₀_eq_iff (h (Ha.P₀ v)) (Λ.A.P0 m)).1 ((hh _).trans (TorusExt.isIota_unique (Ha.iota v) (hm ▸ Λ.iota m)))`. Conclude with `⟨n + m, by simpa [hn] using hm, by rw [map_add, ← e, sub_add_cancel]⟩`. Use `choose gm hgy hgP using hg`.

Establish `hgN : ∀ v, Λ.A.N (gm v) = h (Ha.N v)` using `fun v => eq_of_ex₀_smul Λ.toGtDict fun s => by`. Rewrite using `[← map_smul h, hh]`. Conclude with `TorusExt.IsTorusPtF.unique ((TorusExt.isTorusPtF_iff_isTorusPt _ _).2 (Λ.shift_be s (gm v))) ((TorusExt.isTorusPtF_iff_isTorusPt _ _).2 (hgy v ▸ Ha.shift s v))`. Establish `hgw : ∀ w v, h (Ha.Pw w v) = Λ.A.Pw w (gm v)` using `fun w v => by`. Rewrite using `[Ha.Pw_eq, map_add, map_smul, AnArc.Pw_apply, hgP, hgN]`.

Take `⟨T₀, hT₀⟩` from `Λ.A.exists_BwMat_posDef`. Take `⟨w, hw, hw'⟩ : ∃ w : ℂ, Ha.T < w.im ∧ T₀ < w.im` from `⟨(max Ha.T T₀ + 1 : ℝ) * Complex.I, by simpa using (le_max_left _ _).trans_lt (lt_add_one _), by simpa using (le_max_right _ _).trans_lt (lt_add_one _)⟩`. Take `⟨pl, pinj, -, -, Hm, hH, -, hE⟩` from `Ha.period w hw`. Take `⟨qinj, -, qspan⟩` from `Λ.A.Pw_lattice (hT₀ w hw')`. Establish `hlin : ∀ (x : 𝓞 E) z, h (fun k => ty k (x : E) * z k) = Λ.A.actV x (h z)` using `fun x z => eq_of_ex₀_smul Λ.toGtDict fun s => by`.

Establish `e : s • (fun k => ty k (x : E) * z k) = fun k => ty k (x : E) * (s • z) k`. Use function extensionality and compare the values at `fun k => mul_left_comm _ _ _`. Rewrite using `[← map_smul, ← map_smul, ← map_smul, hh, e]`. Conclude with `TorusExt.gtAct_unique hK.laws.globalFns (Ha.lin x (s • z)) (hh (s • z) ▸ Λ.lin x (h (s • z)))`. Set `gm₁ : (Fu.Di Ha.i).La →ₗ[𝓞 E] Λ.A.La` to `{ toFun := gm map_add' := fun v v' => qinj (by rw [map_add, ← hgw, ← hgw, ← hgw, map_add, map_add]) map_smul' := fun x v => qinj (by`.

Rewrite using `[RingHom.id_apply, AnArc.Pw_smul, ← hgw, ← hgw, ← hlin]`. Conclude with `congrArg h (funext (pl x v))) }`. Establish `ginj : Function.Injective gm₁` using `fun v v' e => pinj (h.injective ((hgw w v).trans ((congrArg _ e).trans (hgw w v').symm)))`. Establish `gsurj : Function.Surjective gm₁` using `fun m => by`. Take `⟨v, hv⟩` from `Ha.y_onto (Λ.y m)`.

Take `⟨n, hn, e⟩` from `(Ha.ker (h.symm (Λ.A.P0 (m - gm v)))).1 (by`. Rewrite using `[← hh, h.apply_symm_apply]`. Conclude with `(Λ.ker_y _).2 ⟨_, by rw [map_sub, hgy, hv, sub_self], rfl⟩)`. Use `⟨n + v, hext _ _ ((hgy _).trans (by rw [map_add, hn, zero_add, hv])) ((hgP _).trans ?_)⟩` and prove the remaining obligations. Rewrite using `[map_add, map_add, ← e, h.apply_symm_apply, ← hgP, map_sub, sub_add_cancel]`.

Use `⟨LinearEquiv.ofBijective gm₁ ⟨ginj, gsurj⟩, h, hh, hgy, hgw, ?_⟩` and prove the remaining obligations. Establish `hD : ∀ v v', (hermForm Hm (h.symm (Λ.A.Pw w (gm v))) (h.symm (Λ.A.Pw w (gm v')))).im = (Fu.Di Ha.i).EF v v'` using `fun v v' => by`. Rewrite using `[← hgw, ← hgw, h.symm_apply_apply, h.symm_apply_apply, hE]`. Establish `gs : Function.Surjective gm` using `gsurj`. Introduce `v v'`.

Use `Int.cast_injective (α := ℝ) ((im_eq_EF Λ.A (hT₀ w hw') h.symm.toLinearMap hH (fun n m => ?_) (fun m m' => ?_) _ _).symm.trans (hD v v'))` and prove the remaining obligations. Take `⟨t, ht, -⟩` from `hξ (n.comp Λ.eX.symm.toAddEquiv.toAddMonoidHom).toIntLinearMap replace ht : ∀ v', -(Fu.Di Ha.i).EF t v' = n (Λ.eX.symm (Ha.y v')) := ht`. Take `⟨hy, hs⟩` from `(Ha.riemann t).1 fun v' hv' => by simpa [hv'] using ht v'`. Establish `e : gm t = AnArc.La.mk 0 n 0` using `hext _ _ (by rw [hgy, hy]; exact (map_zero Λ.eX).symm) (by`. Rewrite using `[hgP]`.

Use `eq_of_ex₀_smul Λ.toGtDict fun s => ?_` and prove the remaining obligations. Take `⟨x, hx, hx'⟩` from `hs s`. Rewrite using `[← map_smul h, hh]`. Use `TorusExt.IsTorusPtF.unique ((TorusExt.isTorusPtF_iff_isTorusPt _ _).2 hx) ((TorusExt.isTorusPtF_iff_isTorusPt _ _).2 ?_)` and prove the remaining obligations. Use `Λ.toGtDict.isTorusPt_ex₀ (v := s • Λ.A.P0 (AnArc.La.mk 0 n 0)) (by simp) using 2 with y` and compare the differences between its conclusion and the goal.

Take `⟨v', rfl⟩` from `Ha.y_onto y`. Rewrite using `[hx', ← mul_neg, ← Int.cast_neg, ht]`. Use the proof step `simp)`. Take `⟨v', rfl⟩` from `gs m`. Rewrite using `[← e]`.

Use `(hD t v').trans (congrArg _ ?_)` and prove the remaining obligations. Rewrite using `[e, AnArc.EF_n_left, ← neg_neg ((Fu.Di Ha.i).EF t v'), ht, ← hgy, GtAn₀.y_apply, LinearEquiv.symm_apply_apply]`. Take `⟨v, hv⟩` from `gs (AnArc.La.mk 0 0 m)`. Take `⟨v', hv'⟩` from `gs (AnArc.La.mk 0 0 m')`. Establish `k` using `im_hermForm_eq Ha hK.laws hK.laws2 hP Λ.u Λ.isAH (LinearMap.snd ℂ _ _ ∘ₗ h.toLinearMap) (fun z => by rw [← hh]; exact (Λ.toGtDict.ex₀_b_left _).symm) (fun v hv => by`.

Establish `: (gm v).y = 0` using `Λ.eX.injective (by rw [map_zero, ← hv]; exact hgy v)`. Use `Λ.lam_eq.ge ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(h (Ha.P₀ v)).2 ∈ _`. Rewrite using `[← hgP, AnArc.degeneratingTori_basePeriodMap_snd, this, map_zero, zero_add]`. Conclude with `(gm v).l.2)`.

Use the proof step `(v₁ := v) (v₂ := v') (by rw [← hgy, hv]; exact map_zero Λ.eX) (by rw [← hgy, hv']; exact map_zero Λ.eX)`. Express the relevant statement in the definitionally equal form `(hermForm _ (h (Ha.P₀ v)).2 (h (Ha.P₀ v')).2).im = _ at k`. Rewrite `k` using `[← hgP, ← hgP, hv, hv', AnArc.degeneratingTori_basePeriodMap_snd, AnArc.degeneratingTori_basePeriodMap_snd, AnArc.La.mk_y, AnArc.La.mk_y, map_zero, zero_add, zero_add]`. Rewrite using `[AnArc.EF_l_l, ← hv, ← hv']`. Conclude with `(hD v v').trans k.symm`.
-/
theorem holArc_agrees : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (Λ : GtAn₀ a), letI := H.starRing; ∃ (gam : (Fu.Di Ha.i).La ≃ₗ[𝓞 E] Λ.A.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] Λ.A.V), (∀ z, Λ.ex₀ (h z) = Ha.ex₀ z) ∧ (∀ v, Λ.y (gam v) = Ha.y v) ∧ (∀ w v, h (Ha.Pw w v) = Λ.A.Pw w (gam v)) ∧ ∀ v v', Λ.A.EF (gam v) (gam v') = (Fu.Di Ha.i).EF v v' := by
  intro hK E _ _ _ H Dw l Xo c _ _ σ O _ β Y a χ W g ty Fu Ha Λ
  letI := H.starRing
  letI := TorusExt.gtGroup a.D₀ ℂ
  have hO : Countable (𝓞 E) := Finsupp.Countable.of_moduleFinite (R := ℤ)
  have hfin := (Fu.Di Ha.i).fin
  have cL : Countable (Fu.Di Ha.i).La := Finsupp.Countable.of_moduleFinite (R := 𝓞 E)
  have cA : Countable Λ.A.La := Finsupp.Countable.of_moduleFinite (R := ℤ)
  obtain ⟨nn, hN, -, -, hnn, -, hξ⟩ := holArc_nilpotent E H Dw l Xo c σ O β Y a χ W g ty Fu Ha
  have hP : ∀ w v, Ha.y v = 0 → Ha.Pw w v = Ha.P₀ v := fun w v hv => by
    rw [Ha.Pw_eq, hN, hnn v hv, map_zero, smul_zero, add_zero]
  obtain ⟨h₀, hh₀⟩ := exists_linear Λ.toGtDict hK.theta Ha.ex₀ Ha.add Ha.hol_b Ha.hol_chi
  have hinj : Function.Injective h₀ := (injective_iff_map_eq_zero h₀).2 fun z hz =>
    eq_zero_of_forall_smul_mem_countable (Set.countable_range Ha.P₀) fun s => by
      obtain ⟨v, -, e⟩ := (Ha.ker (s • z)).1 (by
        rw [← hh₀, map_smul, hz, smul_zero]; exact Λ.toGtDict.isZero_ex₀_zero)
      exact ⟨v, e.symm⟩
  have hsurj : Function.Surjective h₀ :=
    FibreUnif.surjective_of_countable h₀ (Set.countable_range Λ.A.P0) fun v => by
      obtain ⟨z, hz⟩ := Ha.onto (Λ.ex₀ v)
      obtain ⟨la, -, e⟩ := (Λ.toGtDict.ex₀_eq_iff v (h₀ z)).1 (by rw [hh₀, hz])
      exact ⟨z, la, e.symm⟩
  let h := LinearEquiv.ofBijective h₀ ⟨hinj, hsurj⟩
  have hh : ∀ z, Λ.ex₀ (h z) = Ha.ex₀ z := hh₀
  clear_value h
  clear hh₀ hinj hsurj h₀
  have hext : ∀ m m', Λ.y m = Λ.y m' → Λ.A.P0 m = Λ.A.P0 m' → m = m' := fun m m' hy =>
    la_ext Λ.A (Λ.eX.injective hy)
  have hg : ∀ v, ∃ m, Λ.y m = Ha.y v ∧ Λ.A.P0 m = h (Ha.P₀ v) := fun v => by
    obtain ⟨m, hm⟩ := Λ.y_onto (Ha.y v)
    obtain ⟨n, hn, e⟩ := (Λ.toGtDict.ex₀_eq_iff (h (Ha.P₀ v)) (Λ.A.P0 m)).1
      ((hh _).trans (TorusExt.isIota_unique (Ha.iota v) (hm ▸ Λ.iota m)))
    exact ⟨n + m, by simpa [hn] using hm, by rw [map_add, ← e, sub_add_cancel]⟩
  choose gm hgy hgP using hg
  have hgN : ∀ v, Λ.A.N (gm v) = h (Ha.N v) := fun v => eq_of_ex₀_smul Λ.toGtDict fun s => by
    rw [← map_smul h, hh]
    exact TorusExt.IsTorusPtF.unique ((TorusExt.isTorusPtF_iff_isTorusPt _ _).2 (Λ.shift_be s (gm v)))
      ((TorusExt.isTorusPtF_iff_isTorusPt _ _).2 (hgy v ▸ Ha.shift s v))
  have hgw : ∀ w v, h (Ha.Pw w v) = Λ.A.Pw w (gm v) := fun w v => by
    rw [Ha.Pw_eq, map_add, map_smul, AnArc.Pw_apply, hgP, hgN]
  obtain ⟨T₀, hT₀⟩ := Λ.A.exists_BwMat_posDef
  obtain ⟨w, hw, hw'⟩ : ∃ w : ℂ, Ha.T < w.im ∧ T₀ < w.im :=
    ⟨(max Ha.T T₀ + 1 : ℝ) * Complex.I, by simpa using (le_max_left _ _).trans_lt (lt_add_one _),
      by simpa using (le_max_right _ _).trans_lt (lt_add_one _)⟩
  obtain ⟨pl, pinj, -, -, Hm, hH, -, hE⟩ := Ha.period w hw
  obtain ⟨qinj, -, qspan⟩ := Λ.A.Pw_lattice (hT₀ w hw')
  have hlin : ∀ (x : 𝓞 E) z, h (fun k => ty k (x : E) * z k) = Λ.A.actV x (h z) := fun x z =>
    eq_of_ex₀_smul Λ.toGtDict fun s => by
      have e : s • (fun k => ty k (x : E) * z k) = fun k => ty k (x : E) * (s • z) k :=
        funext fun k => mul_left_comm _ _ _
      rw [← map_smul, ← map_smul, ← map_smul, hh, e]
      exact TorusExt.gtAct_unique hK.laws.globalFns (Ha.lin x (s • z)) (hh (s • z) ▸ Λ.lin x (h (s • z)))
  let gm₁ : (Fu.Di Ha.i).La →ₗ[𝓞 E] Λ.A.La :=
    { toFun := gm
      map_add' := fun v v' => qinj (by rw [map_add, ← hgw, ← hgw, ← hgw, map_add, map_add])
      map_smul' := fun x v => qinj (by
        rw [RingHom.id_apply, AnArc.Pw_smul, ← hgw, ← hgw, ← hlin]
        exact congrArg h (funext (pl x v))) }
  have ginj : Function.Injective gm₁ := fun v v' e =>
    pinj (h.injective ((hgw w v).trans ((congrArg _ e).trans (hgw w v').symm)))
  have gsurj : Function.Surjective gm₁ := fun m => by
    obtain ⟨v, hv⟩ := Ha.y_onto (Λ.y m)
    obtain ⟨n, hn, e⟩ := (Ha.ker (h.symm (Λ.A.P0 (m - gm v)))).1 (by
      rw [← hh, h.apply_symm_apply]
      exact (Λ.ker_y _).2 ⟨_, by rw [map_sub, hgy, hv, sub_self], rfl⟩)
    refine ⟨n + v, hext _ _ ((hgy _).trans (by rw [map_add, hn, zero_add, hv])) ((hgP _).trans ?_)⟩
    rw [map_add, map_add, ← e, h.apply_symm_apply, ← hgP, map_sub, sub_add_cancel]
  refine ⟨LinearEquiv.ofBijective gm₁ ⟨ginj, gsurj⟩, h, hh, hgy, hgw, ?_⟩
  have hD : ∀ v v', (hermForm Hm (h.symm (Λ.A.Pw w (gm v))) (h.symm (Λ.A.Pw w (gm v')))).im =
      (Fu.Di Ha.i).EF v v' := fun v v' => by
    rw [← hgw, ← hgw, h.symm_apply_apply, h.symm_apply_apply, hE]
  have gs : Function.Surjective gm := gsurj
  intro v v'
  refine Int.cast_injective (α := ℝ)
    ((im_eq_EF Λ.A (hT₀ w hw') h.symm.toLinearMap hH (fun n m => ?_) (fun m m' => ?_) _ _).symm.trans (hD v v'))
  · obtain ⟨t, ht, -⟩ := hξ (n.comp Λ.eX.symm.toAddEquiv.toAddMonoidHom).toIntLinearMap
    replace ht : ∀ v', -(Fu.Di Ha.i).EF t v' = n (Λ.eX.symm (Ha.y v')) := ht
    obtain ⟨hy, hs⟩ := (Ha.riemann t).1 fun v' hv' => by simpa [hv'] using ht v'
    have e : gm t = AnArc.La.mk 0 n 0 := hext _ _ (by rw [hgy, hy]; exact (map_zero Λ.eX).symm) (by
      rw [hgP]
      refine eq_of_ex₀_smul Λ.toGtDict fun s => ?_
      obtain ⟨x, hx, hx'⟩ := hs s
      rw [← map_smul h, hh]
      refine TorusExt.IsTorusPtF.unique ((TorusExt.isTorusPtF_iff_isTorusPt _ _).2 hx)
        ((TorusExt.isTorusPtF_iff_isTorusPt _ _).2 ?_)
      convert Λ.toGtDict.isTorusPt_ex₀ (v := s • Λ.A.P0 (AnArc.La.mk 0 n 0)) (by simp) using 2 with y
      obtain ⟨v', rfl⟩ := Ha.y_onto y
      rw [hx', ← mul_neg, ← Int.cast_neg, ht]
      simp)
    obtain ⟨v', rfl⟩ := gs m
    rw [← e]
    refine (hD t v').trans (congrArg _ ?_)
    rw [e, AnArc.EF_n_left, ← neg_neg ((Fu.Di Ha.i).EF t v'), ht, ← hgy, GtAn₀.y_apply, LinearEquiv.symm_apply_apply]
  · obtain ⟨v, hv⟩ := gs (AnArc.La.mk 0 0 m)
    obtain ⟨v', hv'⟩ := gs (AnArc.La.mk 0 0 m')
    have k := im_hermForm_eq Ha hK.laws hK.laws2 hP Λ.u Λ.isAH (LinearMap.snd ℂ _ _ ∘ₗ h.toLinearMap)
      (fun z => by rw [← hh]; exact (Λ.toGtDict.ex₀_b_left _).symm)
      (fun v hv => by
        have : (gm v).y = 0 := Λ.eX.injective (by rw [map_zero, ← hv]; exact hgy v)
        refine Λ.lam_eq.ge ?_
        change (h (Ha.P₀ v)).2 ∈ _
        rw [← hgP, AnArc.degeneratingTori_basePeriodMap_snd, this, map_zero, zero_add]
        exact (gm v).l.2)
      (v₁ := v) (v₂ := v') (by rw [← hgy, hv]; exact map_zero Λ.eX) (by rw [← hgy, hv']; exact map_zero Λ.eX)
    change (hermForm _ (h (Ha.P₀ v)).2 (h (Ha.P₀ v')).2).im = _ at k
    rw [← hgP, ← hgP, hv, hv', AnArc.degeneratingTori_basePeriodMap_snd, AnArc.degeneratingTori_basePeriodMap_snd, AnArc.La.mk_y, AnArc.La.mk_y, map_zero, zero_add,
      zero_add] at k
    rw [AnArc.EF_l_l, ← hv, ← hv']
    exact (hD v v').trans k.symm

end GlobalTheory.ArcCompare
