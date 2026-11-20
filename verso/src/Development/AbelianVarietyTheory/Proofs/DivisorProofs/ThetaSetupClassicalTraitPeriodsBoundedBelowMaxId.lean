import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemHasTestsOfRealPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionPpavPadicField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationExistenceAndTorsionStatements
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemMaximalIdealExpLeNormVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagEndIsMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLab
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.LamBound

/- English proof (translation)
Introduce `k`. Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Introduce `x hk hx`. Distinguish the cases in `hd : ∃ v, x = m • v`.

Take `⟨v, rfl⟩` from `hd`. Establish `hv : v ≠ 0` using `by rintro rfl; simp at hx`. Establish `hvv` using `hβ v hv`. Establish `e : β (m • v) (m • v) = (m : ℤ) * ((m : ℤ) * β v v)`. Simplify using `[map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]`.

Establish `hm' : (2 : ℤ) ≤ m` using `by exact_mod_cast hm`. Establish `h2 : 2 * β v v ≤ (m : ℤ) * β v v` using `mul_le_mul_of_nonneg_right hm' hvv.le`. Establish `h3 : 2 * ((m : ℤ) * β v v) ≤ (m : ℤ) * ((m : ℤ) * β v v)` using `mul_le_mul_of_nonneg_right hm' (by linarith)`. Establish `hlt : β v v < β (m • v) (m • v)` using `by rw [e]; linarith`. Take `⟨x', h1, h2, h3⟩` from `ih (β v v).toNat (by omega) v rfl hv`.

Conclude with `⟨x', h1, h2, h3.trans hlt.le⟩`. Conclude with `⟨x, hx, hd, le_rfl⟩`.
-/
theorem exists_not_dvd_le {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (hβ : ∀ y, y ≠ 0 → 0 < β y y) (m : ℕ) (hm : 2 ≤ m) :
    ∀ (k : ℕ) (x : X), (β x x).toNat = k → x ≠ 0 →
      ∃ x', x' ≠ 0 ∧ (¬ ∃ v, x' = m • v) ∧ β x' x' ≤ β x x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hk hx
    by_cases hd : ∃ v, x = m • v
    · obtain ⟨v, rfl⟩ := hd
      have hv : v ≠ 0 := by rintro rfl; simp at hx
      have hvv := hβ v hv
      have e : β (m • v) (m • v) = (m : ℤ) * ((m : ℤ) * β v v) := by
        simp [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
      have h2 : 2 * β v v ≤ (m : ℤ) * β v v := mul_le_mul_of_nonneg_right hm' hvv.le
      have h3 : 2 * ((m : ℤ) * β v v) ≤ (m : ℤ) * ((m : ℤ) * β v v) :=
        mul_le_mul_of_nonneg_right hm' (by linarith)
      have hlt : β v v < β (m • v) (m • v) := by rw [e]; linarith
      obtain ⟨x', h1, h2, h3⟩ := ih (β v v).toNat (by omega) v rfl hv
      exact ⟨x', h1, h2, h3.trans hlt.le⟩
    · exact ⟨x, hx, hd, le_rfl⟩

/- English proof (translation)
Establish `h1` using `h.1.diag_pos (i := 0)`. Simplify using `only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Int.cast_add] at h1`. Establish `: (0 : ℝ) < W 0 0` using `by linarith`. Conclude with `this` after adjusting the coercions.
-/
theorem isE8_apply_zero_zero_pos {W : Matrix (Fin 8) (Fin 8) ℤ} (h : IsE8 W) : 0 < W 0 0 := by
  have h1 := h.1.diag_pos (i := 0)
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Int.cast_add] at h1
  have : (0 : ℝ) < W 0 0 := by linarith
  exact_mod_cast this

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

/- English proof (translation)
Take `⟨j, hj⟩` from `IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx`. Use `fin_cases j`. Simplify using `using hj`.
-/
theorem beta_pos (T : Trait F) (x : T.D.toPre.X) (hx : x ≠ 0) : 0 < T.β x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases j
  simpa using hj

/- English proof (translation)
Establish `hϖ0 : algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 c.T.irr.ne_zero`. Establish `h0 : c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ) ≠ 0` using `(map_ne_zero _).2 hϖ0`. Establish `hlt : ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖ < 1`. Assume the negation of the conclusion as `hge`. Use `push_neg at hge`.

Establish `hinv : ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)⁻¹‖ ≤ 1`. Rewrite using `[map_inv₀, norm_inv]`. Conclude with `inv_le_one_of_one_le₀ hge`. Take `⟨w, hw⟩` from `(c.int _).1 hinv`. Apply `c.T.irr.not_isUnit` to reduce the goal to its premises.

Use `isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective c.T.V (FractionRing c.T.V) ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]`. Unfold `CTrait.sc`. Use `Real.log_neg (norm_pos_iff.2 h0) hlt` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sc_pos {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (c : CTrait X₁ p z₁) : 0 < c.sc := by
  have hϖ0 : algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 c.T.irr.ne_zero
  have h0 : c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖ < 1 := by
    by_contra hge
    push_neg at hge
    have hinv : ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨w, hw⟩ := (c.int _).1 hinv
    apply c.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective c.T.V (FractionRing c.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold CTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

/- English proof (translation)
Establish `hfin : {x | ¬ q a < q x}.Finite` using `Filter.eventually_cofinite.1 (hq.eventually_gt_atTop (q a))`. Take `⟨b, ⟨hb, v, rfl⟩, hmin⟩` from `Set.exists_min_image ({x | ¬ q a < q x} ∩ Set.range fun v => a + N • v) q (hfin.inter_of_left _) ⟨a, lt_irrefl _, 0, by simp⟩`. Use `⟨v, fun v0 => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : q a < q (a + N • v + N • v0)`. Conclude with `(not_lt.1 hb).trans h.le`.

Conclude with `hmin _ ⟨h, v + v0, by simp [add_assoc]⟩`.
-/
theorem exists_shortest {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (N : ℕ) (a : X) :
    ∃ v : X, ∀ v0, q (a + N • v) ≤ q (a + N • v + N • v0) := by
  have hfin : {x | ¬ q a < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop (q a))
  obtain ⟨b, ⟨hb, v, rfl⟩, hmin⟩ := Set.exists_min_image ({x | ¬ q a < q x} ∩ Set.range fun v => a + N • v) q
    (hfin.inter_of_left _) ⟨a, lt_irrefl _, 0, by simp⟩
  refine ⟨v, fun v0 => ?_⟩
  by_cases h : q a < q (a + N • v + N • v0)
  · exact (not_lt.1 hb).trans h.le
  · exact hmin _ ⟨h, v + v0, by simp [add_assoc]⟩

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `h : q a ≤ 0` using `not_lt.1 h`. Establish `hfin : {x | ¬ (0 : ℝ) < q x}.Finite` using `Filter.eventually_cofinite.1 (hq.eventually_gt_atTop 0)`. Use `Set.infinite_of_injective_forall_mem (f := fun n : ℤ => n • a) (smul_left_injective ℤ ha) (fun n => ?_) hfin` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, not_lt, QuadraticMap.map_smul, zsmul_eq_mul]`.

Use `push_cast`. Conclude with `mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) h`.
-/
theorem pos_of_tendsto {X : Type} [AddCommGroup X] [Module.Free ℤ X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (a : X) (ha : a ≠ 0) : 0 < q a := by
  by_contra h
  have h : q a ≤ 0 := not_lt.1 h
  have hfin : {x | ¬ (0 : ℝ) < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop 0)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => n • a) (smul_left_injective ℤ ha) (fun n => ?_) hfin
  simp only [Set.mem_setOf_eq, not_lt, QuadraticMap.map_smul, zsmul_eq_mul]
  push_cast
  exact mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) h

/- English proof (translation)
Simplify using `[qW, Fin.sum_univ_succ]`.
-/
theorem qW_single {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (x : X) :
    qW W β (Pi.single 0 x) = W 0 0 * β x x := by
  simp [qW, Fin.sum_univ_succ]

/- English proof (translation)
Introduce `g n F W Z i X₁ hg hn ho hi hE hT hP p _ z₁ c`. Take `⟨ε, hε, -⟩` from `GlobalTheory.Poinc.exists_diagEnd_isMonHom g n F W _ X₁.ρ.P X₁.u X₁.sharp`. Conclude with `⟨ε, GlobalTheory.Poinc.exists_isLab g n F W Z i X₁ hg hn ho hi hE hT hP ε hε p z₁ c⟩`.
-/
theorem lab : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁), ∃ ε yy, IsLab X₁ ε c yy := by
  intro g n F W Z i X₁ hg hn ho hi hE hT hP p _ z₁ c
  obtain ⟨ε, hε, -⟩ := GlobalTheory.Poinc.exists_diagEnd_isMonHom g n F W _ X₁.ρ.P X₁.u X₁.sharp
  exact ⟨ε, GlobalTheory.Poinc.exists_isLab g n F W Z i X₁ hg hn ho hi hE hT hP ε hε p z₁ c⟩

/- English proof (translation)
Introduce `g n F W Z i X₁ hg hn ho hi hE hT hP p _ z₁ hz`. Take `⟨hL, hL2⟩` from `GlobalTheory.abelianSchemeLaws_all`. Take `⟨hU, hUT⟩` from `GlobalTheory.ZH.thmU_and_uTors`. Establish `hdiv : X₁.M.HasDiv X₁.S.th` using `hT X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.u X₁.sharp X₁.gen X₁.M X₁.π X₁.normal X₁.comp`. Use `⟨(W 0 0 : ℝ) / X₁.S.N, fun c x hx => ?_⟩` and prove the remaining obligations.

Take `⟨x', hx', hnd, hle⟩` from `exists_not_dvd_le c.T.β (beta_pos c.T) X₁.S.N X₁.S.N_ge _ x rfl hx`. Take `⟨ε, yy, c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, hR, y₀, hat, u, l, j, hq, -⟩` from `lab g n F W Z i X₁ hg hn ho hi hE hT hP p z₁ c`. Set `S'` to `X₁.S.rechart c₀ hc R' fg frac hth hev`. Establish `hdiv' : X₁.M.HasDiv S'.th` using `fun z => (hdiv z).imp fun k hk => (RatModel.div_mul_iff hc).2 hk`. Establish `htests : S'.HasTests` using `(hasTests_of_real GlobalTheory.SS.semistableReductionSt hU hL hL2 hUT X₁.o₁ X₁.Ω₁ S' ρ').1`.

Establish `hy : ∀ a : X₁.o₁, ‖y₀ (algebraMap X₁.o₁ S'.R a)‖ ≤ 1` using `fun a => by`. Rewrite using `[hat]`. Conclude with `RatModel.norm_val_le_one c.cen ((X₁.M.O z₁).algebraMap_mem a)`. Take `⟨τ, e, hτ, -⟩` from `exists_test_match X₁.o₁ X₁.Ω₁ S' ρ' p y₀ u l (GlobalTheory.T.thetaConstant_bounded_by_shortestVector hL hL2 hUT _ _ S' ρ' p y₀ u l hy) (GlobalTheory.T.unitThetaConstants_generate_integralTorsion hL hL2 hUT _ _ S' ρ' p y₀ u l hy) (GlobalTheory.T.weightSpace_values_integralTorsion_ …`. Set `α₀ : τ.X` to `e.symm (j.symm (Pi.single 0 x'))`.

Take `⟨v, hv⟩` from `exists_shortest τ.q τ.pos X₁.S.N α₀`. Establish `hne : α₀ + X₁.S.N • v ≠ 0` using `fun h0 => hnd ⟨-(j (e v) 0), by`. Establish `h1` using `congrFun (congrArg (fun t => j (e t)) h0) 0`. Simplify using `only [α₀, map_add, map_nsmul, AddEquiv.apply_symm_apply, map_zero, Pi.add_apply, Pi.single_eq_same, Pi.smul_apply, Pi.zero_apply] at h1`. Rewrite using `[smul_neg]`.

Conclude with `eq_neg_of_add_eq_zero_left h1⟩`. Establish `hqle : τ.q (α₀ + X₁.S.N • v) ≤ (W 0 0 : ℝ) * (c.sc * c.T.β x' x')`. Establish `h1` using `hv (-v)`. Rewrite `h1` using `[smul_neg, add_neg_cancel_right]`. Use `h1.trans_eq ?_` and prove the remaining obligations.

Rewrite using `[hτ, hq]`. Simplify using `only [α₀, AddEquiv.apply_symm_apply, qW_single]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨h, hm, hh⟩` from `GlobalTheory.exists_mem_maximalIdeal_exp_le_norm_val X₁.o₁ X₁.Ω₁ S' X₁.M X₁.normal hdiv' htests z₁ hz p c.y y₀ c.cen (fun a ha => hR ha) hat τ _ hv (pos_of_tendsto τ.q τ.pos _ hne)`.

Use `⟨h, hm, le_trans (Real.exp_le_exp.2 ?_) hh⟩` and prove the remaining obligations. Establish `hsc` using `sc_pos c`. Establish `hW : (0 : ℝ) ≤ W 0 0` using `by exact_mod_cast (isE8_apply_zero_zero_pos hE).le`. Establish `hNpos : (0 : ℝ) < X₁.S.N`. Use `X₁.S.N_ge` as an intermediate fact.

Conclude with `(by omega : 0 < X₁.S.N)` after adjusting the coercions. Establish `hb : (c.T.β x' x' : ℝ) ≤ c.T.β x x` using `by exact_mod_cast hle`. Establish `h1 : τ.q (α₀ + X₁.S.N • v) ≤ (W 0 0 : ℝ) * (c.sc * c.T.β x x)` using `hqle.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hsc.le) hW)`. Rewrite using `[neg_le_neg_iff, div_mul_eq_mul_div]`. Conclude with `div_le_div_of_nonneg_right h1 hNpos.le`.
-/
theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ C : ℝ, ∀ (c : CTrait X₁ p z₁) (x : c.T.D.toPre.X), x ≠ 0 → ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(C * (c.sc * c.T.β x x))) ≤ ‖c.val h‖ := by
  intro g n F W Z i X₁ hg hn ho hi hE hT hP p _ z₁ hz
  obtain ⟨hL, hL2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨hU, hUT⟩ := GlobalTheory.ZH.thmU_and_uTors
  have hdiv : X₁.M.HasDiv X₁.S.th :=
    hT X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.u X₁.sharp X₁.gen X₁.M X₁.π X₁.normal X₁.comp
  refine ⟨(W 0 0 : ℝ) / X₁.S.N, fun c x hx => ?_⟩
  obtain ⟨x', hx', hnd, hle⟩ :=
    exists_not_dvd_le c.T.β (beta_pos c.T) X₁.S.N X₁.S.N_ge _ x rfl hx
  obtain ⟨ε, yy, c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, hR, y₀, hat, u, l, j, hq, -⟩ :=
    lab g n F W Z i X₁ hg hn ho hi hE hT hP p z₁ c
  let S' := X₁.S.rechart c₀ hc R' fg frac hth hev
  have hdiv' : X₁.M.HasDiv S'.th := fun z => (hdiv z).imp fun k hk => (RatModel.div_mul_iff hc).2 hk
  have htests : S'.HasTests :=
    (hasTests_of_real GlobalTheory.SS.semistableReductionSt hU hL hL2 hUT X₁.o₁ X₁.Ω₁ S' ρ').1
  have hy : ∀ a : X₁.o₁, ‖y₀ (algebraMap X₁.o₁ S'.R a)‖ ≤ 1 := fun a => by
    rw [hat]
    exact RatModel.norm_val_le_one c.cen ((X₁.M.O z₁).algebraMap_mem a)
  obtain ⟨τ, e, hτ, -⟩ := exists_test_match X₁.o₁ X₁.Ω₁ S' ρ' p y₀ u l
    (GlobalTheory.T.thetaConstant_bounded_by_shortestVector hL hL2 hUT _ _ S' ρ' p y₀ u l hy) (GlobalTheory.T.unitThetaConstants_generate_integralTorsion hL hL2 hUT _ _ S' ρ' p y₀ u l hy)
    (GlobalTheory.T.weightSpace_values_integralTorsion_bound_shortestVector hL hL2 hUT _ _ S' ρ' p y₀ u l hy) (GlobalTheory.T.exists_norm_torsionSum_shortestVector_eq hL hL2 hUT _ _ S' ρ' p y₀ u l hy)
    (GlobalTheory.T.exists_weightZeroSection_unit_integralTorsionPoint hL hL2 hUT _ _ S' ρ' p y₀ u l hy)
  let α₀ : τ.X := e.symm (j.symm (Pi.single 0 x'))
  obtain ⟨v, hv⟩ := exists_shortest τ.q τ.pos X₁.S.N α₀
  have hne : α₀ + X₁.S.N • v ≠ 0 := fun h0 => hnd ⟨-(j (e v) 0), by
    have h1 := congrFun (congrArg (fun t => j (e t)) h0) 0
    simp only [α₀, map_add, map_nsmul, AddEquiv.apply_symm_apply, map_zero, Pi.add_apply, Pi.single_eq_same,
      Pi.smul_apply, Pi.zero_apply] at h1
    rw [smul_neg]
    exact eq_neg_of_add_eq_zero_left h1⟩
  have hqle : τ.q (α₀ + X₁.S.N • v) ≤ (W 0 0 : ℝ) * (c.sc * c.T.β x' x') := by
    have h1 := hv (-v)
    rw [smul_neg, add_neg_cancel_right] at h1
    refine h1.trans_eq ?_
    rw [hτ, hq]
    simp only [α₀, AddEquiv.apply_symm_apply, qW_single]
    push_cast
    ring
  obtain ⟨h, hm, hh⟩ := GlobalTheory.exists_mem_maximalIdeal_exp_le_norm_val X₁.o₁ X₁.Ω₁ S' X₁.M X₁.normal hdiv' htests z₁ hz p
    c.y y₀ c.cen (fun a ha => hR ha) hat τ _ hv (pos_of_tendsto τ.q τ.pos _ hne)
  refine ⟨h, hm, le_trans (Real.exp_le_exp.2 ?_) hh⟩
  have hsc := sc_pos c
  have hW : (0 : ℝ) ≤ W 0 0 := by exact_mod_cast (isE8_apply_zero_zero_pos hE).le
  have hNpos : (0 : ℝ) < X₁.S.N := by
    have := X₁.S.N_ge
    exact_mod_cast (by omega : 0 < X₁.S.N)
  have hb : (c.T.β x' x' : ℝ) ≤ c.T.β x x := by exact_mod_cast hle
  have h1 : τ.q (α₀ + X₁.S.N • v) ≤ (W 0 0 : ℝ) * (c.sc * c.T.β x x) :=
    hqle.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hsc.le) hW)
  rw [neg_le_neg_iff, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right h1 hNpos.le

end GlobalTheory.Poinc.LamBound
