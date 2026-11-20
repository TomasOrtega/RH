import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomOfLinearScalingHermForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LambdaBundleIsoOfPrimeToPWeilPairings
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.AlphaPair
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam.SamePeriod

/- English proof (translation)
Take `⟨k, hk⟩` from `Complex.exp_eq_exp_iff_exists_int.1 (h ((m' - m).natAbs + 1) (Nat.succ_pos _))`. Establish `hn : (((m' - m).natAbs + 1 : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)`. Establish `h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `Complex.two_pi_I_ne_zero`. Establish `e : ((m' - m : ℤ) : ℂ) = ((((m' - m).natAbs + 1 : ℕ) : ℤ) * k : ℤ)`. Rewrite using `[Int.cast_mul, Int.cast_natCast, Int.cast_sub]`.

Generalize the expression as in `(((m' - m).natAbs + 1 : ℕ) : ℂ) = N at hk hn`. Apply `mul_left_cancel₀ h2` to reduce the goal to its premises. Clear denominators, using `at hk` for the nonvanishing conditions. Take the linear combination `(2 * Real.pi * Complex.I) * hk`. Establish `e' : ((((m' - m).natAbs + 1 : ℕ) : ℤ)) ∣ m' - m` using `⟨k, by exact_mod_cast e⟩`.

Use `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs e' (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem int_eq_of_exp {m m' : ℤ} (h : ∀ n : ℕ, 0 < n →
    Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / n) = Complex.exp (-(2 * Real.pi * Complex.I) * (m' : ℂ) / n)) :
    m = m' := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h ((m' - m).natAbs + 1) (Nat.succ_pos _))
  have hn : (((m' - m).natAbs + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have e : ((m' - m : ℤ) : ℂ) = ((((m' - m).natAbs + 1 : ℕ) : ℤ) * k : ℤ) := by
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_sub]
    generalize (((m' - m).natAbs + 1 : ℕ) : ℂ) = N at hk hn
    apply mul_left_cancel₀ h2
    field_simp at hk
    linear_combination (2 * Real.pi * Complex.I) * hk
  have e' : ((((m' - m).natAbs + 1 : ℕ) : ℤ)) ∣ m' - m := ⟨k, by exact_mod_cast e⟩
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs e' (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)
  omega

noncomputable def imForm {g m : ℕ} (Hm : Matrix (Fin m) (Fin m) ℂ) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin m → ℂ)) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm Hm (F z) (F w)).im)
    (fun z z' w => by simp [hermForm])
    (fun r z w => by simp [hermForm])
    (fun z w w' => by simp [hermForm, Matrix.mulVec_add])
    (fun r z w => by simp [hermForm, Matrix.mulVec_smul])

/- English proof (translation)
Establish `e : imForm Hm F = imForm Hm' F'` using `LinearMap.ext_on hs fun z hz => LinearMap.ext_on hs fun w hw => h z hz w hw`. Establish `k : ∀ z w, (hermForm Hm (F z) (F w)).im = (hermForm Hm' (F' z) (F' w)).im` using `fun z w => LinearMap.congr_fun₂ e z w`. Use `Complex.ext ?_ (k z w)` and prove the remaining obligations. Simplify `k (Complex.I • z) w` using `[hermForm]`.
-/
theorem hermForm_eq_of_im {g m m' : ℕ} (Hm : Matrix (Fin m) (Fin m) ℂ) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (Hm' : Matrix (Fin m') (Fin m') ℂ) (F' : (Fin g → ℂ) →ₗ[ℂ] (Fin m' → ℂ)) {s : Set (Fin g → ℂ)}
    (hs : Submodule.span ℝ s = ⊤)
    (h : ∀ z ∈ s, ∀ w ∈ s, (hermForm Hm (F z) (F w)).im = (hermForm Hm' (F' z) (F' w)).im) (z w : Fin g → ℂ) :
    hermForm Hm (F z) (F w) = hermForm Hm' (F' z) (F' w) := by
  have e : imForm Hm F = imForm Hm' F' :=
    LinearMap.ext_on hs fun z hz => LinearMap.ext_on hs fun w hw => h z hz w hw
  have k : ∀ z w, (hermForm Hm (F z) (F w)).im = (hermForm Hm' (F' z) (F' w)).im := fun z w =>
    LinearMap.congr_fun₂ e z w
  refine Complex.ext ?_ (k z w)
  simpa [hermForm] using k (Complex.I • z) w

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [Nat.cast_zero, zero_smul, pow_zero, (u.ker 0).2 u.Λ.zero_mem]`. Consider the case `succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]`.
-/
theorem ex_nsmul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (z : Fin g → ℂ) (n : ℕ) :
    u.ex ((n : ℂ) • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, pow_zero, (u.ker 0).2 u.Λ.zero_mem]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]

/- English proof (translation)
Rewrite using `[← ex_nsmul, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), one_smul]`. Conclude with `(u.ker _).2 hz`.
-/
theorem ex_inv_pow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) {z : Fin g → ℂ}
    (hz : z ∈ u.Λ) {n : ℕ} (hn : 0 < n) : u.ex ((n : ℂ)⁻¹ • z) ^ n = 1 := by
  rw [← ex_nsmul, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), one_smul]
  exact (u.ker _).2 hz

/- English proof (translation)
Take `⟨rig, hrig⟩` from `P.rigid`. Take `⟨u₀, Hm, χ, Ef, hAH, -, hv, hw, -, hθ, hE, -, hW₀⟩` from `hU P rig hrig`. Take `⟨F, hF, -⟩` from `GlobalTheory.existsUnique_linear_lift_of_isHolTo P.A P.isAb P.L P.g g u₀ hv hw u.ex u.ex_add (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)`. Use `haveI := u.discrete`. Use `haveI := u₀.discrete`.

Establish `hinj` using `AnyUnif.injective_of_ker_le_discrete u.Λ F fun z hz => by`. Rewrite using `[← u.ker, ← hF, hz]`. Conclude with `(u₀.ker 0).2 u₀.Λ.zero_mem`. Establish `hsurj : LinearMap.range F = ⊤` using `AHWeil.eq_top_of_add_discrete u₀.Λ _ fun w => by`. Take `⟨z, hz⟩` from `u.ex_onto (u₀.ex w)`.

Use `⟨⟨w - F z, (u₀.ker _).1 ?_⟩, z, by simp⟩` and prove the remaining obligations. Establish `h` using `u₀.ex_add (w - F z) (F z)`. Rewrite `h` using `[sub_add_cancel, hF, hz]`. Conclude with `(mul_eq_right.1 h.symm)`. Use `⟨u₀, Hm, χ, LinearEquiv.ofBijective F ⟨hinj, LinearMap.range_eq_top.1 hsurj⟩, hAH, hθ, hF, fun a b => ?_⟩` and prove the remaining obligations.

Establish `hm : ∀ a, per τ a ∈ u.Λ` using `fun a => (hΛ _).2 ⟨a, rfl⟩`. Establish `hm₀ : ∀ a, F (per τ a) ∈ u₀.Λ` using `fun a => by`. Rewrite using `[← u₀.ker, hF, u.ker]`. Conclude with `hm a`. Establish `e : Ef ⟨_, hm₀ a⟩ ⟨_, hm₀ b⟩ = omegaStd a b` using `int_eq_of_exp fun n hn => by`.

Establish `h₁` using `hW₀ n ⟨_, hm₀ a⟩ ⟨_, hm₀ b⟩ (Units.mk0 _ (Complex.exp_ne_zero _)) hn rfl`. Establish `h₂` using `hW n a b (Units.mk0 _ (Complex.exp_ne_zero _)) hn rfl`. Rewrite `h₁` using `[← map_smul, ← map_smul, hF, hF]`. Use `((hL.weil _ P n _).1 _ _ (ex_inv_pow u (hm a) hn) (ex_inv_pow u (hm b) hn)).unique h₁ h₂` as an intermediate fact. Conclude with `congrArg Units.val (H1.unitOn_injective this)`.

Rewrite using `[← e]`. Conclude with `(hE ⟨_, hm₀ a⟩ ⟨_, hm₀ b⟩).symm`.
-/
theorem exists_equiv (hL : Out.Laws) (hU : ThetaUnifAV) (P : Out.PolAV (Sp ℂ)) {g : ℕ}
    (τ : Matrix (Fin g) (Fin g) ℂ) (u : HolUnif P.A P.L g) (hΛ : ∀ z, z ∈ u.Λ ↔ ∃ a, z = per τ a)
    (hW : ∀ (n : ℕ) (a b : Fin g ⊕ Fin g → ℤ) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / n) →
      Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • per τ a)) (u.ex ((n : ℂ)⁻¹ • per τ b)) (unitOn c)) :
    ∃ (u₀ : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u₀.Λ → ℂ)
      (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ)), u₀.IsAH Hm χ ∧
      (∀ n : ℕ, (∀ s, ∃! θ, u₀.IsThetaFn Hm χ n θ ∧ u₀.IsFnPow n s θ) ∧
        ∀ θ, u₀.IsThetaFn Hm χ n θ → ∃! s, u₀.IsFnPow n s θ) ∧
      (∀ z, u₀.ex (F z) = u.ex z) ∧
      ∀ a b, (hermForm Hm (F (per τ a)) (F (per τ b))).im = omegaStd a b := by
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u₀, Hm, χ, Ef, hAH, -, hv, hw, -, hθ, hE, -, hW₀⟩ := hU P rig hrig
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo P.A P.isAb P.L P.g g u₀ hv hw u.ex u.ex_add
    (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  haveI := u.discrete
  haveI := u₀.discrete
  have hinj := AnyUnif.injective_of_ker_le_discrete u.Λ F fun z hz => by
    rw [← u.ker, ← hF, hz]
    exact (u₀.ker 0).2 u₀.Λ.zero_mem
  have hsurj : LinearMap.range F = ⊤ := AHWeil.eq_top_of_add_discrete u₀.Λ _ fun w => by
    obtain ⟨z, hz⟩ := u.ex_onto (u₀.ex w)
    refine ⟨⟨w - F z, (u₀.ker _).1 ?_⟩, z, by simp⟩
    have h := u₀.ex_add (w - F z) (F z)
    rw [sub_add_cancel, hF, hz] at h
    exact (mul_eq_right.1 h.symm)
  refine ⟨u₀, Hm, χ, LinearEquiv.ofBijective F ⟨hinj, LinearMap.range_eq_top.1 hsurj⟩, hAH, hθ, hF, fun a b => ?_⟩
  have hm : ∀ a, per τ a ∈ u.Λ := fun a => (hΛ _).2 ⟨a, rfl⟩
  have hm₀ : ∀ a, F (per τ a) ∈ u₀.Λ := fun a => by
    rw [← u₀.ker, hF, u.ker]
    exact hm a
  have e : Ef ⟨_, hm₀ a⟩ ⟨_, hm₀ b⟩ = omegaStd a b := int_eq_of_exp fun n hn => by
    have h₁ := hW₀ n ⟨_, hm₀ a⟩ ⟨_, hm₀ b⟩ (Units.mk0 _ (Complex.exp_ne_zero _)) hn rfl
    have h₂ := hW n a b (Units.mk0 _ (Complex.exp_ne_zero _)) hn rfl
    rw [← map_smul, ← map_smul, hF, hF] at h₁
    have := ((hL.weil _ P n _).1 _ _ (ex_inv_pow u (hm a) hn) (ex_inv_pow u (hm b) hn)).unique h₁ h₂
    exact congrArg Units.val (H1.unitOn_injective this)
  rw [← e]
  exact (hE ⟨_, hm₀ a⟩ ⟨_, hm₀ b⟩).symm

/- English proof (translation)
Take `⟨v, Hm, χ, F, hA, hθ, hF, hE⟩` from `exists_equiv hL hU P τ u hΛ hW`. Take `⟨v', Hm', χ', F', hA', hθ', hF', hE'⟩` from `exists_equiv hL hU P' τ u' hΛ' hW'`. Establish `hH` using `hermForm_eq_of_im Hm' F'.toLinearMap Hm F.toLinearMap u.full fun z hz w hw => by`. Take `⟨a, rfl⟩` from `(hΛ z).1 hz`. Take `⟨b, rfl⟩` from `(hΛ w).1 hw`.

Conclude with `(hE' a b).trans (hE a b).symm`. Take `⟨f, hf, hfe⟩` from `exists_hom_of_linear_scaling_hermForm P P' v v' Hm χ Hm' χ' hA hA' (fun k => (hθ k).2) (fun k => (hθ' k).1) (F.symm.trans F').toLinearMap 1 (fun l hl => by`. Take `⟨z, rfl⟩` from `F.surjective l`. Rewrite `hl` using `[← v.ker, hF, u.ker, hΛ, ← hΛ', ← u'.ker, ← hF', v'.ker]`. Simplify using `using hl)`.

Use the proof step `(fun z w => by`. Take `⟨z, rfl⟩` from `F.surjective z`. Take `⟨w, rfl⟩` from `F.surjective w`. Simplify using `using hH z w)`. Use `⟨f, hf, fun z => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hF, ← hfe, ← hF']`. Simplify using the standard rewrite rules.
-/
theorem exists_hom (hL : Out.Laws) (hU : ThetaUnifAV) (P P' : Out.PolAV (Sp ℂ)) {g : ℕ}
    (τ : Matrix (Fin g) (Fin g) ℂ) (u : HolUnif P.A P.L g) (hΛ : ∀ z, z ∈ u.Λ ↔ ∃ a, z = per τ a)
    (hW : ∀ (n : ℕ) (a b : Fin g ⊕ Fin g → ℤ) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / n) →
      Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • per τ a)) (u.ex ((n : ℂ)⁻¹ • per τ b)) (unitOn c))
    (u' : HolUnif P'.A P'.L g) (hΛ' : ∀ z, z ∈ u'.Λ ↔ ∃ a, z = per τ a)
    (hW' : ∀ (n : ℕ) (a b : Fin g ⊕ Fin g → ℤ) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / n) →
      Out.WeilIs P'.A P'.L n (u'.ex ((n : ℂ)⁻¹ • per τ a)) (u'.ex ((n : ℂ)⁻¹ • per τ b)) (unitOn c)) :
    ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u.ex z ≫ f = u'.ex z := by
  obtain ⟨v, Hm, χ, F, hA, hθ, hF, hE⟩ := exists_equiv hL hU P τ u hΛ hW
  obtain ⟨v', Hm', χ', F', hA', hθ', hF', hE'⟩ := exists_equiv hL hU P' τ u' hΛ' hW'
  have hH := hermForm_eq_of_im Hm' F'.toLinearMap Hm F.toLinearMap u.full fun z hz w hw => by
    obtain ⟨a, rfl⟩ := (hΛ z).1 hz
    obtain ⟨b, rfl⟩ := (hΛ w).1 hw
    exact (hE' a b).trans (hE a b).symm
  obtain ⟨f, hf, hfe⟩ := exists_hom_of_linear_scaling_hermForm P P' v v' Hm χ Hm' χ' hA hA'
    (fun k => (hθ k).2) (fun k => (hθ' k).1) (F.symm.trans F').toLinearMap 1
    (fun l hl => by
      obtain ⟨z, rfl⟩ := F.surjective l
      rw [← v.ker, hF, u.ker, hΛ, ← hΛ', ← u'.ker, ← hF', v'.ker] at hl
      simpa using hl)
    (fun z w => by
      obtain ⟨z, rfl⟩ := F.surjective z
      obtain ⟨w, rfl⟩ := F.surjective w
      simpa using hH z w)
  refine ⟨f, hf, fun z => ?_⟩
  rw [← hF, ← hfe, ← hF']
  simp

end GlobalTheory.KeyFam.SamePeriod

namespace GlobalTheory.KeyFam
open SamePeriod

/- English proof (translation)
Introduce and unpack `hL hU g k τ P P' lev lev' ⟨-, -, -, u, hΛ, hW, hlev⟩ ⟨-, -, -, u', hΛ', hW', hlev'⟩`. Take `⟨f, hf, hfe⟩` from `exists_hom hL hU P' P τ u' hΛ' hW' u hΛ hW`. Take `⟨f', -, hfe'⟩` from `exists_hom hL hU P P' τ u hΛ hW u' hΛ' hW'`. Use `haveI := P.isAb.smooth`. Use `haveI := P'.isAb.smooth`.

Use `haveI := P.isAb.proper`. Use `haveI := P'.isAb.proper`. Use `haveI := P.isAb.comm`. Use `haveI := P'.isAb.comm`. Use `haveI := isReduced_of_smooth_complex _ P.A.hom inferInstance`.

Use `haveI := isReduced_of_smooth_complex _ P'.A.hom inferInstance`. Set `e : P'.A ≅ P.A` to `{ hom := f inv := f' hom_inv_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by`. Take `⟨z, rfl⟩` from `u'.ex_onto x`. Rewrite using `[← Category.assoc, hfe, hfe', Category.comp_id]`. Use `inv_hom_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by`.

Take `⟨z, rfl⟩` from `u.ex_onto x`. Rewrite using `[← Category.assoc, hfe', hfe, Category.comp_id] }`. Establish `tors : ∀ (n : ℕ) (x : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A), 0 < n → x ^ n = 1 → ∃ a, x = u'.ex ((n : ℂ)⁻¹ • per τ a)` using `fun n x hn hx => by`. Take `⟨z, rfl⟩` from `u'.ex_onto x`. Rewrite `hx` using `[← ex_nsmul, u'.ker, hΛ']`.

Take `⟨a, ha⟩` from `hx`. Conclude with `⟨a, by rw [← ha, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), one_smul]⟩`. Establish `h₁` using `lam_iso_of_weil_pairings hL ℂ P' P f 2 1 hf Nat.prime_two inferInstance fun n x y c hn _ hx hy h => by`. Take `⟨a, ha⟩` from `tors n x hn hx`. Take `⟨b, hb⟩` from `tors n y hn hy`.

Establish `h₂` using `hW' n a b (Units.mk0 _ (Complex.exp_ne_zero _)) hn rfl`. Rewrite `h₂` using `[← ha, ← hb]`. Rewrite using `[pow_one, ((hL.weil _ P' n _).1 _ _ hx hy).unique h h₂, ha, hb, hfe, hfe]`. Conclude with `hW n a b _ hn rfl`. Establish `hp : IsGrpPullback P'.A P.A (𝟙 _) f.left` using `@isGrpPullback_of_iso _ _ _ _ _ e hf`.

Establish `hq` using `LamPull.exists_isSquare hp.1.w`. Establish `hfL : (P.L.pull f.left).IsLB` using `pull_isLB P.isLB _`. Establish `h₂` using `LamPull.lbIso_lam_pull hp P.isLB hfL ⟨idIso _, idIso_isGen hfL⟩ hq`. Establish `h₀ : LBIso (abelian₂ P'.A (lbPow P'.L 1)) (abelian₂ P'.A P'.L)`. Take `⟨w, hw⟩` from `lbIso_lbPow_one P'.isLB`.

Conclude with `⟨LB.linCombIso w _ _, DVR.linCombIso_isGen w hw _ _⟩`. Establish `l₀ : (abelian₂ P'.A P'.L).IsLB` using `DVR.linComb_isLB _ P'.isLB _ _`. Establish `l₁ : (abelian₂ P'.A (lbPow P'.L 1)).IsLB` using `DVR.linComb_isLB _ (DVR.linComb_isLB _ P'.isLB _ _) _ _`. Establish `l₂ : (abelian₂ P'.A (P.L.pull f.left)).IsLB` using `DVR.linComb_isLB _ hfL _ _`. Establish `l₃ : (abelian₂ P.A P.L).IsLB` using `DVR.linComb_isLB _ P.isLB _ _`.

Use `⟨e, hf, ⟨_, hq, LBIso.trans l₀ l₂ (pull_isLB l₃ _) (LBIso.trans l₀ l₁ l₂ h₀.symm h₁) h₂⟩, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[hlev, hlev']`. Conclude with `hfe _`.
-/
theorem exists_iso_of_perLev : Out.Laws → ThetaUnifAV → ∀ (g k : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (P P' : Out.PolAV (Sp ℂ)) (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) (lev' : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P'.A)), PerLev P τ k lev → PerLev P' τ k lev' → ∃ e : P'.A ≅ P.A, IsMonHom e.hom ∧ LamIs P'.A P'.L P.A (abelian₂ P.A P.L) e.hom.left ∧ ∀ a, lev' a ≫ e.hom = lev a := by
  rintro hL hU g k τ P P' lev lev' ⟨-, -, -, u, hΛ, hW, hlev⟩ ⟨-, -, -, u', hΛ', hW', hlev'⟩
  obtain ⟨f, hf, hfe⟩ := exists_hom hL hU P' P τ u' hΛ' hW' u hΛ hW
  obtain ⟨f', -, hfe'⟩ := exists_hom hL hU P P' τ u hΛ hW u' hΛ' hW'
  haveI := P.isAb.smooth
  haveI := P'.isAb.smooth
  haveI := P.isAb.proper
  haveI := P'.isAb.proper
  haveI := P.isAb.comm
  haveI := P'.isAb.comm
  haveI := isReduced_of_smooth_complex _ P.A.hom inferInstance
  haveI := isReduced_of_smooth_complex _ P'.A.hom inferInstance
  let e : P'.A ≅ P.A :=
    { hom := f
      inv := f'
      hom_inv_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u'.ex_onto x
        rw [← Category.assoc, hfe, hfe', Category.comp_id]
      inv_hom_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u.ex_onto x
        rw [← Category.assoc, hfe', hfe, Category.comp_id] }
  have tors : ∀ (n : ℕ) (x : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A), 0 < n → x ^ n = 1 →
      ∃ a, x = u'.ex ((n : ℂ)⁻¹ • per τ a) := fun n x hn hx => by
    obtain ⟨z, rfl⟩ := u'.ex_onto x
    rw [← ex_nsmul, u'.ker, hΛ'] at hx
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, by rw [← ha, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), one_smul]⟩
  have h₁ := lam_iso_of_weil_pairings hL ℂ P' P f 2 1 hf Nat.prime_two inferInstance
    fun n x y c hn _ hx hy h => by
      obtain ⟨a, ha⟩ := tors n x hn hx
      obtain ⟨b, hb⟩ := tors n y hn hy
      have h₂ := hW' n a b (Units.mk0 _ (Complex.exp_ne_zero _)) hn rfl
      rw [← ha, ← hb] at h₂
      rw [pow_one, ((hL.weil _ P' n _).1 _ _ hx hy).unique h h₂, ha, hb, hfe, hfe]
      exact hW n a b _ hn rfl
  have hp : IsGrpPullback P'.A P.A (𝟙 _) f.left := @isGrpPullback_of_iso _ _ _ _ _ e hf
  have hq := LamPull.exists_isSquare hp.1.w
  have hfL : (P.L.pull f.left).IsLB := pull_isLB P.isLB _
  have h₂ := LamPull.lbIso_lam_pull hp P.isLB hfL ⟨idIso _, idIso_isGen hfL⟩ hq
  have h₀ : LBIso (abelian₂ P'.A (lbPow P'.L 1)) (abelian₂ P'.A P'.L) := by
    obtain ⟨w, hw⟩ := lbIso_lbPow_one P'.isLB
    exact ⟨LB.linCombIso w _ _, DVR.linCombIso_isGen w hw _ _⟩
  have l₀ : (abelian₂ P'.A P'.L).IsLB := DVR.linComb_isLB _ P'.isLB _ _
  have l₁ : (abelian₂ P'.A (lbPow P'.L 1)).IsLB := DVR.linComb_isLB _ (DVR.linComb_isLB _ P'.isLB _ _) _ _
  have l₂ : (abelian₂ P'.A (P.L.pull f.left)).IsLB := DVR.linComb_isLB _ hfL _ _
  have l₃ : (abelian₂ P.A P.L).IsLB := DVR.linComb_isLB _ P.isLB _ _
  refine ⟨e, hf, ⟨_, hq, LBIso.trans l₀ l₂ (pull_isLB l₃ _) (LBIso.trans l₀ l₁ l₂ h₀.symm h₁) h₂⟩, fun a => ?_⟩
  rw [hlev, hlev']
  exact hfe _

end GlobalTheory.KeyFam
