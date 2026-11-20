import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySmallHeisenbergLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAnnihilatorOpenSubgroupFiniteAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU Filter Topology
open IsDedekindDomain
open scoped Matrix

noncomputable section
namespace GlobalTheory.CoefSupp
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def lat (F : Type) [Field F] [NumberField F] (κ : Type) (N : ℕ) : AddSubgroup (κ → Af F) where
  carrier := {y | ∀ i, algebraMap F (Af F) ((N : F)⁻¹) * y i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F}
  zero_mem' := fun i => by simp only [Pi.zero_apply, mul_zero]; exact Subring.zero_mem _
  add_mem' := fun ha hb i => by simp only [Pi.add_apply, mul_add]; exact Subring.add_mem _ (ha i) (hb i)
  neg_mem' := fun ha i => by simp only [Pi.neg_apply, mul_neg]; exact Subring.neg_mem _ (ha i)

/- English proof (translation)
Establish `: (lat F κ N : Set (κ → Af F)) = ⋂ i, (fun y : κ → Af F => algebraMap F (Af F) ((N : F)⁻¹) * y i) ⁻¹' (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (Af F))`. Use extensionality with `y`. Simplify using `[lat]`. Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun i => GroundTheory.Global.isOpen_integralFiniteAdeles.preimage (continuous_const.mul (continuous_apply i))`.
-/
theorem isOpen_lat (N : ℕ) : IsOpen (lat F κ N : Set (κ → Af F)) := by
  have : (lat F κ N : Set (κ → Af F)) = ⋂ i, (fun y : κ → Af F => algebraMap F (Af F) ((N : F)⁻¹) * y i) ⁻¹'
      (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (Af F)) := by
    ext y; simp [lat]
  rw [this]
  exact isOpen_iInter_of_finite fun i => GroundTheory.Global.isOpen_integralFiniteAdeles.preimage
    (continuous_const.mul (continuous_apply i))

/- English proof (translation)
Introduce `v`. Use `⟨evalV F v (algebraMap F (Af F) ((N : F)⁻¹) * y i), hy i v, ?_⟩` and prove the remaining obligations. Establish `hN0 : (N : F) ≠ 0` using `by exact_mod_cast (show N ≠ 0 by omega)`. Use `show evalV F v (y i) = _`. Rewrite using `[map_mul, AlgHom.commutes, ← mul_assoc, ← map_natCast (algebraMap F (Fv F v)), ← map_mul, mul_inv_cancel₀ hN0, map_one, one_mul]`.
-/
theorem finDiv_of_mem {N : ℕ} (hN : 1 ≤ N) {y : κ → Af F} (hy : y ∈ lat F κ N) (i : κ) :
    GlobalTheory.FinSupp.FinDiv F N (pairA F 0 (y i)) := by
  intro v
  refine ⟨evalV F v (algebraMap F (Af F) ((N : F)⁻¹) * y i), hy i v, ?_⟩
  have hN0 : (N : F) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  show evalV F v (y i) = _
  rw [map_mul, AlgHom.commutes, ← mul_assoc, ← map_natCast (algebraMap F (Fv F v)), ← map_mul,
    mul_inv_cancel₀ hN0, map_one, one_mul]

/- English proof (translation)
Simplify using `only [dotProduct]`. Establish `h1 : ∀ y, fstA F (pairA F 0 y) = 0` using `fun _ => rfl`. Establish `h2 : ∀ y, sndA F (pairA F 0 y) = y` using `fun _ => rfl`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show fstA F (∑ x, pairA F 0 (a x) * z x) = 0`.

Rewrite using `[map_sum]`. Simplify using `[map_mul, h1]`. Use `show sndA F (∑ x, pairA F 0 (a x) * z x) = ∑ x, (z x).2 * a x`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, h2, mul_comm]`. Both sides reduce to the same expression.
-/
theorem dot_left (a : κ → Af F) (z : κ → AF F) :
    (fun i => pairA F 0 (a i)) ⬝ᵥ z = pairA F 0 ((fun i => (z i).2) ⬝ᵥ a) := by
  simp only [dotProduct]
  have h1 : ∀ y, fstA F (pairA F 0 y) = 0 := fun _ => rfl
  have h2 : ∀ y, sndA F (pairA F 0 y) = y := fun _ => rfl
  refine Prod.ext ?_ ?_
  · show fstA F (∑ x, pairA F 0 (a x) * z x) = 0
    rw [map_sum]; simp [map_mul, h1]
  · show sndA F (∑ x, pairA F 0 (a x) * z x) = ∑ x, (z x).2 * a x
    rw [map_sum]; refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, h2, mul_comm]; rfl

/- English proof (translation)
Rewrite using `[dotProduct_comm]`. Conclude with `dot_left a z`.
-/
theorem dot_right (a : κ → Af F) (z : κ → AF F) :
    z ⬝ᵥ (fun i => pairA F 0 (a i)) = pairA F 0 ((fun i => (z i).2) ⬝ᵥ a) := by
  rw [dotProduct_comm]; exact dot_left a z

/- English proof (translation)
Simplify using `[schr]`.
-/
theorem schr_fst (ψ : AddChar (AF F) ℂ) (a : κ → AF F) (Φ : (κ → AF F) → ℂ) (x : κ → AF F) :
    schr ψ (a, 0) Φ x = Φ (x + a) := by
  simp [schr]

/- English proof (translation)
Simplify using `[schr]`.
-/
theorem schr_snd (ψ : AddChar (AF F) ℂ) (b : κ → AF F) (Φ : (κ → AF F) → ℂ) (x : κ → AF F) :
    schr ψ (0, b) Φ x = ψ (x ⬝ᵥ b) * Φ x := by
  simp [schr]

/- English proof (translation)
Introduce `F _ _ κ _ ψ hψ Φ hΦ`. Take `⟨N, hN, hfix⟩` from `GlobalTheory.FinSuppHeis.heis_fix_finDiv F κ ψ hψ.1 Φ hΦ`. Establish `hdiv0 : GlobalTheory.FinSupp.FinDiv F N (0 : AF F)` using `fun v => ⟨0, Subring.zero_mem _, by simp⟩`. Use `⟨{x : κ → Af F | ∀ y ∈ lat F κ N, ψ (pairA F 0 (x ⬝ᵥ y)) = 1}, GlobalTheory.AnnCompactStd.isCompact_annihilator F ψ hψ κ _ (isOpen_lat N), ?_⟩` and prove the remaining obligations. Introduce `μ hμ w hne`.

Use `letI : MeasurableSpace (κ → AF F) := borel _`. Use `haveI : BorelSpace (κ → AF F) := ⟨rfl⟩`. Use `haveI := hμ`. Use `set f : (κ → AF F) → ℂ := fun x => Φ x * starRingEnd ℂ (schr ψ w Φ x) with hf`. Establish `hnorm : ∀ z : AF F, ψ z * starRingEnd ℂ (ψ z) = 1` using `fun z => by`.

Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, GlobalTheory.StdCharFromIsStd.norm_psi hψ z]`. Simplify using the standard rewrite rules. Establish `key : ∀ c : ℂ, (∀ x, f x = c * f x) → c = 1`. Introduce `c hc`. Establish `: ∫ x, f x ∂μ = c * ∫ x, f x ∂μ`.

Rewrite using `[← integral_const_mul]`. Conclude with `integral_congr_ae (Filter.Eventually.of_forall hc)`. Establish `hne' : ∫ x, f x ∂μ ≠ 0` using `hne`. Conclude with `(mul_eq_right₀ hne').1 this.symm`. Prove the components needed by the constructor for the conclusion.

Introduce `y hy set b : κ → AF F := fun i => pairA F 0 (y i)`. Establish `hb : ∀ x, Φ x = ψ (x ⬝ᵥ b) * Φ x` using `fun x => by`. Use `congrFun (hfix (0, b) fun i => ⟨rfl, hdiv0, rfl, finDiv_of_mem hN hy i⟩) x` as an intermediate fact. Rewrite `this` using `[schr_snd]`. Conclude with `this.symm`.

Establish `hc` using `key (starRingEnd ℂ (ψ (w.1 ⬝ᵥ b))) fun x => by`. Simplify using `only [hf, schr]`. Establish `e1` using `hb x`. Establish `e2 : starRingEnd ℂ (Φ (x + w.1)) = starRingEnd ℂ (ψ (x ⬝ᵥ b)) * starRingEnd ℂ (ψ (w.1 ⬝ᵥ b)) * starRingEnd ℂ (Φ (x + w.1))` using `by conv_lhs => rw [hb (x + w.1)]`. Rewrite using `[add_dotProduct, AddChar.map_add_eq_mul, map_mul, map_mul]`.

Establish `hn` using `hnorm (x ⬝ᵥ b)`. Rewrite using `[map_mul]`. Take the linear combination `(starRingEnd ℂ (ψ (x ⬝ᵥ w.2 + ⅟2 * (w.1 ⬝ᵥ w.2))) * starRingEnd ℂ (Φ (x + w.1))) * e1 + (ψ (x ⬝ᵥ b) * Φ x * starRingEnd ℂ (ψ (x ⬝ᵥ w.2 + ⅟2 * (w.1 ⬝ᵥ w.2)))) * e2 + (starRingEnd ℂ (ψ (w.1 ⬝ᵥ b)) * Φ x * starRingEnd ℂ (ψ (x ⬝ᵥ w.2 + ⅟2 * (w.1 ⬝ᵥ w.2))) * starRingEnd ℂ (Φ (x + w.1) …`. Establish `: ψ (w.1 ⬝ᵥ b) = 1` using `by simpa using congrArg (starRingEnd ℂ) hc`. Rewrite `this` using `[dot_right]`.

Conclude with `this`. Introduce `y hy set a : κ → AF F := fun i => pairA F 0 (y i)`. Establish `ha : ∀ x, Φ (x + a) = Φ x` using `fun x => by`. Use `congrFun (hfix (a, 0) fun i => ⟨rfl, finDiv_of_mem hN hy i, rfl, hdiv0⟩) x` as an intermediate fact. Rewrite `this` using `[schr_fst]`.

Conclude with `this`. Establish `htr : ∫ x, f (a + x) ∂μ = ∫ x, f x ∂μ` using `integral_add_left_eq_self f a`. Establish `hfa : ∀ x, f (a + x) = starRingEnd ℂ (ψ (a ⬝ᵥ w.2)) * f x` using `fun x => by`. Simplify using `only [hf, schr]`. Establish `e1 : Φ (a + x) = Φ x` using `by rw [add_comm]; exact ha x`.

Establish `e2 : Φ (a + x + w.1) = Φ (x + w.1)` using `by rw [show a + x + w.1 = x + w.1 + a by abel]; exact ha _`. Establish `e3 : ψ ((a + x) ⬝ᵥ w.2 + ⅟2 * (w.1 ⬝ᵥ w.2)) = ψ (a ⬝ᵥ w.2) * ψ (x ⬝ᵥ w.2 + ⅟2 * (w.1 ⬝ᵥ w.2))`. Rewrite using `[← AddChar.map_add_eq_mul, add_dotProduct, add_assoc]`. Rewrite using `[e1, e2, e3, map_mul, map_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hc : starRingEnd ℂ (ψ (a ⬝ᵥ w.2)) = 1`. Establish `hne' : ∫ x, f x ∂μ ≠ 0` using `hne`. Use `(mul_eq_right₀ hne').1 ?_` and prove the remaining obligations. Rewrite using `[← integral_const_mul, ← htr]`. Conclude with `integral_congr_ae (Filter.Eventually.of_forall fun x => (hfa x).symm)`.

Establish `: ψ (a ⬝ᵥ w.2) = 1` using `by simpa using congrArg (starRingEnd ℂ) hc`. Rewrite `this` using `[dot_left]`. Conclude with `this`.
-/
theorem coef_supp : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∃ K : Set (κ → Af F), IsCompact K ∧
      ∀ μ : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ w : (κ → AF F) × (κ → AF F),
        @MeasureTheory.integral _ ℂ _ _ (borel _) μ (fun x => Φ x * starRingEnd ℂ (GlobalTheory.WeilM.schr ψ w Φ x)) ≠ 0 →
        (fun i => (w.1 i).2) ∈ K ∧ (fun i => (w.2 i).2) ∈ K := by
  intro F _ _ κ _ ψ hψ Φ hΦ
  obtain ⟨N, hN, hfix⟩ := GlobalTheory.FinSuppHeis.heis_fix_finDiv F κ ψ hψ.1 Φ hΦ
  have hdiv0 : GlobalTheory.FinSupp.FinDiv F N (0 : AF F) := fun v => ⟨0, Subring.zero_mem _, by simp⟩
  refine ⟨{x : κ → Af F | ∀ y ∈ lat F κ N, ψ (pairA F 0 (x ⬝ᵥ y)) = 1},
    GlobalTheory.AnnCompactStd.isCompact_annihilator F ψ hψ κ _ (isOpen_lat N), ?_⟩
  intro μ hμ w hne
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI := hμ
  set f : (κ → AF F) → ℂ := fun x => Φ x * starRingEnd ℂ (schr ψ w Φ x) with hf
  have hnorm : ∀ z : AF F, ψ z * starRingEnd ℂ (ψ z) = 1 := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, GlobalTheory.StdCharFromIsStd.norm_psi hψ z]; simp
  have key : ∀ c : ℂ, (∀ x, f x = c * f x) → c = 1 := by
    intro c hc
    have : ∫ x, f x ∂μ = c * ∫ x, f x ∂μ := by
      rw [← integral_const_mul]; exact integral_congr_ae (Filter.Eventually.of_forall hc)
    have hne' : ∫ x, f x ∂μ ≠ 0 := hne
    exact (mul_eq_right₀ hne').1 this.symm
  constructor
  · intro y hy
    set b : κ → AF F := fun i => pairA F 0 (y i)
    have hb : ∀ x, Φ x = ψ (x ⬝ᵥ b) * Φ x := fun x => by
      have := congrFun (hfix (0, b) fun i => ⟨rfl, hdiv0, rfl, finDiv_of_mem hN hy i⟩) x
      rw [schr_snd] at this; exact this.symm
    have hc := key (starRingEnd ℂ (ψ (w.1 ⬝ᵥ b))) fun x => by
      simp only [hf, schr]
      have e1 := hb x
      have e2 : starRingEnd ℂ (Φ (x + w.1)) =
          starRingEnd ℂ (ψ (x ⬝ᵥ b)) * starRingEnd ℂ (ψ (w.1 ⬝ᵥ b)) * starRingEnd ℂ (Φ (x + w.1)) := by
        conv_lhs => rw [hb (x + w.1)]
        rw [add_dotProduct, AddChar.map_add_eq_mul, map_mul, map_mul]
      have hn := hnorm (x ⬝ᵥ b)
      rw [map_mul]
      linear_combination (starRingEnd ℂ (ψ (x ⬝ᵥ w.2 + ⅟2 * (w.1 ⬝ᵥ w.2))) * starRingEnd ℂ (Φ (x + w.1))) * e1 +
        (ψ (x ⬝ᵥ b) * Φ x * starRingEnd ℂ (ψ (x ⬝ᵥ w.2 + ⅟2 * (w.1 ⬝ᵥ w.2)))) * e2 +
        (starRingEnd ℂ (ψ (w.1 ⬝ᵥ b)) * Φ x * starRingEnd ℂ (ψ (x ⬝ᵥ w.2 + ⅟2 * (w.1 ⬝ᵥ w.2))) *
          starRingEnd ℂ (Φ (x + w.1))) * hn
    have : ψ (w.1 ⬝ᵥ b) = 1 := by simpa using congrArg (starRingEnd ℂ) hc
    rw [dot_right] at this
    exact this
  · intro y hy
    set a : κ → AF F := fun i => pairA F 0 (y i)
    have ha : ∀ x, Φ (x + a) = Φ x := fun x => by
      have := congrFun (hfix (a, 0) fun i => ⟨rfl, finDiv_of_mem hN hy i, rfl, hdiv0⟩) x
      rw [schr_fst] at this; exact this
    have htr : ∫ x, f (a + x) ∂μ = ∫ x, f x ∂μ := integral_add_left_eq_self f a
    have hfa : ∀ x, f (a + x) = starRingEnd ℂ (ψ (a ⬝ᵥ w.2)) * f x := fun x => by
      simp only [hf, schr]
      have e1 : Φ (a + x) = Φ x := by rw [add_comm]; exact ha x
      have e2 : Φ (a + x + w.1) = Φ (x + w.1) := by rw [show a + x + w.1 = x + w.1 + a by abel]; exact ha _
      have e3 : ψ ((a + x) ⬝ᵥ w.2 + ⅟2 * (w.1 ⬝ᵥ w.2)) = ψ (a ⬝ᵥ w.2) * ψ (x ⬝ᵥ w.2 + ⅟2 * (w.1 ⬝ᵥ w.2)) := by
        rw [← AddChar.map_add_eq_mul, add_dotProduct, add_assoc]
      rw [e1, e2, e3, map_mul, map_mul, map_mul]; ring
    have hc : starRingEnd ℂ (ψ (a ⬝ᵥ w.2)) = 1 := by
      have hne' : ∫ x, f x ∂μ ≠ 0 := hne
      refine (mul_eq_right₀ hne').1 ?_
      rw [← integral_const_mul, ← htr]; exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hfa x).symm)
    have : ψ (a ⬝ᵥ w.2) = 1 := by simpa using congrArg (starRingEnd ℂ) hc
    rw [dot_left] at this
    exact this
end GlobalTheory.CoefSupp
