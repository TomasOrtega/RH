import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGenRosati
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LambdaBundleAdjointOfWeilPairingAdjoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppellHumbertUniformisationRiemannForm

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HermAdjoint

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [Nat.cast_zero, zero_smul, pow_zero]`. Conclude with `(u.ker 0).2 u.Λ.zero_mem`. Consider the case `succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]`.
-/
theorem ex_nsmul (n : ℕ) (z : Fin g → ℂ) : u.ex ((n : ℂ) • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, pow_zero]; exact (u.ker 0).2 u.Λ.zero_mem
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]

/- English proof (translation)
Take `⟨z, rfl⟩` from `u.ex_onto x`. Use `⟨⟨(n : ℂ) • z, (u.ker _).1 ((ex_nsmul u n z).trans hx)⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), one_smul]`.
-/
theorem exists_period_of_pow_eq_one {n : ℕ} (hn : 0 < n) {x : 𝟙_ (Over (Sp ℂ)) ⟶ A} (hx : x ^ n = 1) :
    ∃ a : u.Λ, u.ex ((n : ℂ)⁻¹ • (a : Fin g → ℂ)) = x := by
  obtain ⟨z, rfl⟩ := u.ex_onto x
  refine ⟨⟨(n : ℂ) • z, (u.ker _).1 ((ex_nsmul u n z).trans hx)⟩, ?_⟩
  rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), one_smul]

/- English proof (translation)
Rewrite using `[← ex_nsmul, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), one_smul]`. Conclude with `(u.ker _).2 a.2`.
-/
theorem ex_period_pow {n : ℕ} (hn : 0 < n) (a : u.Λ) : u.ex ((n : ℂ)⁻¹ • (a : Fin g → ℂ)) ^ n = 1 := by
  rw [← ex_nsmul, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), one_smul]
  exact (u.ker _).2 a.2

/- English proof (translation)
The claim follows from `Units.map_injective (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.injective`.
-/
theorem unitOn_injective {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) :=
  Units.map_injective (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.injective

/- English proof (translation)
Take `⟨m, hm⟩` from `Complex.exp_eq_exp_iff_exists_int.1 (h ((q - p).natAbs + 1) (Nat.succ_pos _))`. Establish `hn : (((q - p).natAbs + 1 : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)`. Establish `h₁ : ((q - p : ℤ) : ℂ) = ((m * (((q - p).natAbs + 1 : ℕ) : ℤ) : ℤ) : ℂ)`. Rewrite using `[Int.cast_mul, Int.cast_natCast, Int.cast_sub]`. Generalize the expression as in `(((q - p).natAbs + 1 : ℕ) : ℂ) = N at hm hn`.

Use `mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_` and prove the remaining obligations. Clear denominators, using `at hm ⊢` for the nonvanishing conditions. Take the linear combination `hm`. Establish `h₂ : (((q - p).natAbs + 1 : ℕ) : ℤ) ∣ q - p` using `⟨m, by rw [mul_comm]; exact Int.cast_injective h₁⟩`. Establish `h₃` using `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h₂ (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)`.

Use linear arithmetic over natural numbers and integers.
-/
theorem int_eq_of_exp {p q : ℤ}
    (h : ∀ n : ℕ, 0 < n → Complex.exp (-(2 * Real.pi * Complex.I) * (p : ℂ) / n) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (q : ℂ) / n)) : p = q := by
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h ((q - p).natAbs + 1) (Nat.succ_pos _))
  have hn : (((q - p).natAbs + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
  have h₁ : ((q - p : ℤ) : ℂ) = ((m * (((q - p).natAbs + 1 : ℕ) : ℤ) : ℤ) : ℂ) := by
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_sub]
    generalize (((q - p).natAbs + 1 : ℕ) : ℂ) = N at hm hn
    refine mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_
    field_simp at hm ⊢
    linear_combination hm
  have h₂ : (((q - p).natAbs + 1 : ℕ) : ℤ) ∣ q - p := ⟨m, by rw [mul_comm]; exact Int.cast_injective h₁⟩
  have h₃ := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h₂ (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)
  omega

/- English proof (translation)
Establish `sl : ∀ (t : ℂ) a b, hermForm Hm (t • a) b = t * hermForm Hm a b` using `fun t a b => by`. Simplify using `[hermForm, smul_dotProduct]`. Establish `sr : ∀ (t : ℝ) a b, hermForm Hm a ((t : ℂ) • b) = t * hermForm Hm a b` using `fun t a b => by`. Simplify using `only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]`. Establish `al : ∀ a a' b, hermForm Hm (a + a') b = hermForm Hm a b + hermForm Hm a' b` using `fun a a' b => by`.

Simplify using `[hermForm, add_dotProduct]`. Establish `ar : ∀ a b b', hermForm Hm a (b + b') = hermForm Hm a b + hermForm Hm a b'` using `fun a b b' => by`. Simplify using `[hermForm, Matrix.mulVec_add, dotProduct_add]`. Establish `all : ∀ a b, (hermForm Hm (F a) b).im = (hermForm Hm a (F' b)).im` using `fun a b => by`. Establish `ha : a ∈ Submodule.span ℝ s` using `hs ▸ Submodule.mem_top`.

Establish `hb : b ∈ Submodule.span ℝ s` using `hs ▸ Submodule.mem_top`. Proceed by induction on `ha, hb using Submodule.span_induction₂ with`. Consider the case `mem_mem a b ha hb => exact h a ha b hb`. Consider the case `zero_left b _ => simp [hermForm]`. Consider the case `zero_right a _ => simp [hermForm]`.

Consider the case `add_left a a' b _ _ _ h₁ h₂ => rw [map_add, al, al, Complex.add_im, Complex.add_im, h₁, h₂]`. Consider the case `add_right a b b' _ _ _ h₁ h₂ => rw [map_add, ar, ar, Complex.add_im, Complex.add_im, h₁, h₂]`. Consider the case `smul_left t a b _ _ h₁`. Rewrite using `[← Complex.coe_smul, map_smul, sl, sl, Complex.im_ofReal_mul, Complex.im_ofReal_mul, h₁]`. Consider the case `smul_right t a b _ _ h₁`.

Rewrite using `[← Complex.coe_smul, map_smul, sr, sr, Complex.im_ofReal_mul, Complex.im_ofReal_mul, h₁]`. Use `Complex.ext ?_ (all z w)` and prove the remaining obligations. Use `all (Complex.I • z) w` as an intermediate fact. Rewrite `this` using `[map_smul, sl, sl, Complex.I_mul_im, Complex.I_mul_im]`. Then use the resulting hypothesis.
-/
theorem adjoint_of_im (Hm : Matrix (Fin g) (Fin g) ℂ) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤) (h : ∀ a ∈ s, ∀ b ∈ s, (hermForm Hm (F a) b).im = (hermForm Hm a (F' b)).im)
    (z w : Fin g → ℂ) : hermForm Hm (F z) w = hermForm Hm z (F' w) := by
  have sl : ∀ (t : ℂ) a b, hermForm Hm (t • a) b = t * hermForm Hm a b := fun t a b => by
    simp [hermForm, smul_dotProduct]
  have sr : ∀ (t : ℝ) a b, hermForm Hm a ((t : ℂ) • b) = t * hermForm Hm a b := fun t a b => by
    simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.star_def,
      Complex.conj_ofReal]
  have al : ∀ a a' b, hermForm Hm (a + a') b = hermForm Hm a b + hermForm Hm a' b := fun a a' b => by
    simp [hermForm, add_dotProduct]
  have ar : ∀ a b b', hermForm Hm a (b + b') = hermForm Hm a b + hermForm Hm a b' := fun a b b' => by
    simp [hermForm, Matrix.mulVec_add, dotProduct_add]
  have all : ∀ a b, (hermForm Hm (F a) b).im = (hermForm Hm a (F' b)).im := fun a b => by
    have ha : a ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    have hb : b ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction ha, hb using Submodule.span_induction₂ with
    | mem_mem a b ha hb => exact h a ha b hb
    | zero_left b _ => simp [hermForm]
    | zero_right a _ => simp [hermForm]
    | add_left a a' b _ _ _ h₁ h₂ => rw [map_add, al, al, Complex.add_im, Complex.add_im, h₁, h₂]
    | add_right a b b' _ _ _ h₁ h₂ => rw [map_add, ar, ar, Complex.add_im, Complex.add_im, h₁, h₂]
    | smul_left t a b _ _ h₁ =>
      rw [← Complex.coe_smul, map_smul, sl, sl, Complex.im_ofReal_mul, Complex.im_ofReal_mul, h₁]
    | smul_right t a b _ _ h₁ =>
      rw [← Complex.coe_smul, map_smul, sr, sr, Complex.im_ofReal_mul, Complex.im_ofReal_mul, h₁]
  refine Complex.ext ?_ (all z w)
  have := all (Complex.I • z) w
  rwa [map_smul, sl, sl, Complex.I_mul_im, Complex.I_mul_im] at this

/- English proof (translation)
Introduce `hl hl₂ hc hU P u Hm χ f f' F F' hAH hf hf' e e'`. Use `P.isAb.comm` as an intermediate fact. Take `⟨Ef, hE, -, -, -, -, -, -, hW⟩` from `GlobalTheory.AnyAppellHumbert.isAH_properties hl hl₂ hc hU P u Hm χ hAH`. Establish `hF : ∀ a : u.Λ, F a ∈ u.Λ` using `fun a => by rw [← u.ker, e, (u.ker _).2 a.2, MonObj.one_comp]`. Establish `hF' : ∀ a : u.Λ, F' a ∈ u.Λ` using `fun a => by rw [← u.ker, e', (u.ker _).2 a.2, MonObj.one_comp]`.

Set `c : ℤ → ℕ → ℂˣ` to `fun p n => Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (p : ℂ) / n))`. Establish `w₁ : ∀ (n : ℕ) (a b : u.Λ), 0 < n → Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (a : Fin P.g → ℂ)) ≫ f) (u.ex ((n : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn (c (Ef ⟨_, hF a⟩ b) n))` using `fun n a b hn => by`. Rewrite using `[← e, map_smul]`. Conclude with `hW n ⟨_, hF a⟩ b _ hn rfl`. Establish `w₂ : ∀ (n : ℕ) (a b : u.Λ), 0 < n → Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((n : ℂ)⁻¹ • (b : Fin P.g → ℂ)) ≫ f') (unitOn (c (Ef a ⟨_, hF' b⟩) n))` using `fun n a b hn => by`.

Rewrite using `[← e', map_smul]`. Conclude with `hW n a ⟨_, hF' b⟩ _ hn rfl`. Establish `uq : ∀ (n : ℕ) (x y : 𝟙_ (Over (Sp ℂ)) ⟶ P.A) (d d' : Γ((𝟙_ (Over (Sp ℂ))).left, ⊤)ˣ), x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n (x ≫ f) y d → Out.WeilIs P.A P.L n (x ≫ f) y d' → d = d'` using `fun n x y d d' hx hy h h' => ((hl.weil _ P n _).1 _ _ (by rw [← MonObj.pow_comp, hx, MonObj.one_comp]) hy).unique h h'`. Prove the components needed by the constructor for the conclusion. Introduce `hiso`.

Take `⟨t, ht⟩` from `GlobalTheory.NormRos.exists_gen_rosati P.isLB _ _ hiso`. Establish `hR : Out.RosatiAdj P.A P.L f f'` using `fun _ => ⟨⊤, trivial, LB.pullGen _ _ _ t _, DVR.pullGen_isGen _ _ _ _ ht _⟩`. Use `adjoint_of_im Hm F F' _ u.full fun a ha b hb => ?_` and prove the remaining obligations. Establish `: Ef ⟨_, hF ⟨a, ha⟩⟩ ⟨b, hb⟩ = Ef ⟨a, ha⟩ ⟨_, hF' ⟨b, hb⟩⟩` using `int_eq_of_exp fun n hn => by`. Establish `hx` using `ex_period_pow u hn ⟨a, ha⟩`.

Establish `hy` using `ex_period_pow u hn ⟨b, hb⟩`. Conclude with `congrArg Units.val (unitOn_injective (uq n _ _ _ _ hx hy (w₁ n ⟨a, ha⟩ ⟨b, hb⟩ hn) ((GlobalTheory.weilIs_rosati_iff hl.globalFns hl.cube P f f' hR n _ _ hx hy _).2 (w₂ n ⟨a, ha⟩ ⟨b, hb⟩ hn))))`. Conclude with `(hE ⟨_, hF ⟨a, ha⟩⟩ ⟨b, hb⟩).symm.trans ((congrArg Int.cast this).trans (hE _ _))`. Introduce `H`. Use `GlobalTheory.lbIso_cubeLB_of_pairing_adjoint hl ℂ P f f' hf hf' fun n x y d hn hx hy hd => ?_` and prove the remaining obligations.

Take `⟨a, rfl⟩` from `exists_period_of_pow_eq_one u hn hx`. Take `⟨b, rfl⟩` from `exists_period_of_pow_eq_one u hn hy`. Establish `hab : Ef ⟨_, hF a⟩ b = Ef a ⟨_, hF' b⟩`. Apply `Int.cast_injective (α := ℝ)` to reduce the goal to its premises. Rewrite using `[hE, hE]`.

Conclude with `congrArg Complex.im (H a b)`. Rewrite using `[uq n _ _ _ _ hx hy hd (w₁ n a b hn), hab]`. Conclude with `w₂ n a b hn`.
-/
theorem lbIso_cubeLB_iff_hermForm : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (f f' : P.A ⟶ P.A) (F F' : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)), u.IsAH Hm χ → IsMonHom f → IsMonHom f' → (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, u.ex (F' z) = u.ex z ≫ f') → (LBIso (cubeLB P.A ![fst P.A P.A ≫ f, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ f'] P.L) ↔ ∀ z w, hermForm Hm (F z) w = hermForm Hm z (F' w)) := by
  intro hl hl₂ hc hU P u Hm χ f f' F F' hAH hf hf' e e'
  have := P.isAb.comm
  obtain ⟨Ef, hE, -, -, -, -, -, -, hW⟩ := GlobalTheory.AnyAppellHumbert.isAH_properties hl hl₂ hc hU P u Hm χ hAH
  have hF : ∀ a : u.Λ, F a ∈ u.Λ := fun a => by rw [← u.ker, e, (u.ker _).2 a.2, MonObj.one_comp]
  have hF' : ∀ a : u.Λ, F' a ∈ u.Λ := fun a => by rw [← u.ker, e', (u.ker _).2 a.2, MonObj.one_comp]
  let c : ℤ → ℕ → ℂˣ := fun p n => Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (p : ℂ) / n))
  have w₁ : ∀ (n : ℕ) (a b : u.Λ), 0 < n → Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (a : Fin P.g → ℂ)) ≫ f)
      (u.ex ((n : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn (c (Ef ⟨_, hF a⟩ b) n)) := fun n a b hn => by
    rw [← e, map_smul]
    exact hW n ⟨_, hF a⟩ b _ hn rfl
  have w₂ : ∀ (n : ℕ) (a b : u.Λ), 0 < n → Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (a : Fin P.g → ℂ)))
      (u.ex ((n : ℂ)⁻¹ • (b : Fin P.g → ℂ)) ≫ f') (unitOn (c (Ef a ⟨_, hF' b⟩) n)) := fun n a b hn => by
    rw [← e', map_smul]
    exact hW n a ⟨_, hF' b⟩ _ hn rfl
  have uq : ∀ (n : ℕ) (x y : 𝟙_ (Over (Sp ℂ)) ⟶ P.A) (d d' : Γ((𝟙_ (Over (Sp ℂ))).left, ⊤)ˣ), x ^ n = 1 → y ^ n = 1 →
      Out.WeilIs P.A P.L n (x ≫ f) y d → Out.WeilIs P.A P.L n (x ≫ f) y d' → d = d' := fun n x y d d' hx hy h h' =>
    ((hl.weil _ P n _).1 _ _ (by rw [← MonObj.pow_comp, hx, MonObj.one_comp]) hy).unique h h'
  constructor
  · intro hiso
    obtain ⟨t, ht⟩ := GlobalTheory.NormRos.exists_gen_rosati P.isLB _ _ hiso
    have hR : Out.RosatiAdj P.A P.L f f' := fun _ =>
      ⟨⊤, trivial, LB.pullGen _ _ _ t _, DVR.pullGen_isGen _ _ _ _ ht _⟩
    refine adjoint_of_im Hm F F' _ u.full fun a ha b hb => ?_
    have : Ef ⟨_, hF ⟨a, ha⟩⟩ ⟨b, hb⟩ = Ef ⟨a, ha⟩ ⟨_, hF' ⟨b, hb⟩⟩ := int_eq_of_exp fun n hn => by
      have hx := ex_period_pow u hn ⟨a, ha⟩
      have hy := ex_period_pow u hn ⟨b, hb⟩
      exact congrArg Units.val (unitOn_injective (uq n _ _ _ _ hx hy (w₁ n ⟨a, ha⟩ ⟨b, hb⟩ hn)
        ((GlobalTheory.weilIs_rosati_iff hl.globalFns hl.cube P f f' hR n _ _ hx hy _).2 (w₂ n ⟨a, ha⟩ ⟨b, hb⟩ hn))))
    exact (hE ⟨_, hF ⟨a, ha⟩⟩ ⟨b, hb⟩).symm.trans ((congrArg Int.cast this).trans (hE _ _))
  · intro H
    refine GlobalTheory.lbIso_cubeLB_of_pairing_adjoint hl ℂ P f f' hf hf' fun n x y d hn hx hy hd => ?_
    obtain ⟨a, rfl⟩ := exists_period_of_pow_eq_one u hn hx
    obtain ⟨b, rfl⟩ := exists_period_of_pow_eq_one u hn hy
    have hab : Ef ⟨_, hF a⟩ b = Ef a ⟨_, hF' b⟩ := by
      apply Int.cast_injective (α := ℝ)
      rw [hE, hE]
      exact congrArg Complex.im (H a b)
    rw [uq n _ _ _ _ hx hy hd (w₁ n a b hn), hab]
    exact w₂ n a b hn

end GlobalTheory.HermAdjoint
