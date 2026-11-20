import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleCharactersExist

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaTriple

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

/- English proof (translation)
Establish `h : Hf D T (w0 D • x) y = w0 D * Hf D T x y`. Rewrite using `[GlobalTheory.ThetaLine.Hf_eq, GlobalTheory.ThetaLine.sq_smul_left, GlobalTheory.ThetaLine.Hf_eq, mul_div_assoc]`. Establish `h1 : (w0 D).re = 1 / 2` using `by simp [w0]`. Establish `h2 : (w0 D).im = Real.sqrt D.host.d / 2` using `by simp [w0]`. Rewrite using `[bc, h, Complex.mul_im, h1, h2]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem theta_cocycle_eq_exp_hermitian (T : Tor D) (x y : VC D N N') :
    bc D T x y = Complex.exp (-(2 * Real.pi * Complex.I) * ((Hf D T (w0 D • x) y).im : ℂ)) := by
  have h : Hf D T (w0 D • x) y = w0 D * Hf D T x y := by
    rw [GlobalTheory.ThetaLine.Hf_eq, GlobalTheory.ThetaLine.sq_smul_left, GlobalTheory.ThetaLine.Hf_eq, mul_div_assoc]
  have h1 : (w0 D).re = 1 / 2 := by simp [w0]
  have h2 : (w0 D).im = Real.sqrt D.host.d / 2 := by simp [w0]
  rw [bc, h, Complex.mul_im, h1, h2]
  congr 1
  push_cast
  ring

/- English proof (translation)
Take `⟨-, h0, h1, h2, -, -, -⟩` from `GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc N N' A hA`. Use `⟨h0, fun x hx y hy => ?_, fun x hx => h2 x fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `GlobalTheory.NormSum.exists_integer_map_eq_w0 D`. Establish `hw` using `GlobalTheory.ThetaInter.klat_smul_mem hA a hx`. Rewrite `hw` using `[ha]`.

Take `⟨m, hm⟩` from `h1 _ hw y hy`. Rewrite using `[theta_cocycle_eq_exp_hermitian, hm, Complex.exp_eq_one_iff]`. Conclude with `⟨-m, by push_cast; ring⟩`. Establish `h` using `hx y hy`. Rewrite `h` using `[bc_comm, mul_eq_right₀ (bc_ne_zero _ _ _ _), Complex.exp_eq_one_iff]`.

Take `⟨n, hn⟩` from `h`. Use `⟨-n, ?_⟩` and prove the remaining obligations. Establish `h3 : (2 * (Real.pi : ℂ) * Complex.I) * ((Hf D (tor0 D cc δ) x y).im : ℂ) = (2 * (Real.pi : ℂ) * Complex.I) * ((-n : ℤ) : ℂ)`. Use `push_cast`. Take the linear combination `-hn`.

Conclude with `mul_left_cancel₀ Complex.two_pi_I_ne_zero h3` after adjusting the coercions.
-/
theorem nice_of_klat (hc : Crv D cc δ) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    Nice D (tor0 D cc δ) A := by
  obtain ⟨-, h0, h1, h2, -, -, -⟩ :=
    GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc N N' A hA
  refine ⟨h0, fun x hx y hy => ?_, fun x hx => h2 x fun y hy => ?_⟩
  · obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have hw := GlobalTheory.ThetaInter.klat_smul_mem hA a hx
    rw [ha] at hw
    obtain ⟨m, hm⟩ := h1 _ hw y hy
    rw [theta_cocycle_eq_exp_hermitian, hm, Complex.exp_eq_one_iff]
    exact ⟨-m, by push_cast; ring⟩
  · have h := hx y hy
    rw [bc_comm, mul_eq_right₀ (bc_ne_zero _ _ _ _), Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨-n, ?_⟩
    have h3 : (2 * (Real.pi : ℂ) * Complex.I) * ((Hf D (tor0 D cc δ) x y).im : ℂ) =
        (2 * (Real.pi : ℂ) * Complex.I) * ((-n : ℤ) : ℂ) := by
      push_cast
      linear_combination -hn
    exact_mod_cast mul_left_cancel₀ Complex.two_pi_I_ne_zero h3

/- English proof (translation)
Use `haveI := GlobalTheory.ThetaInter.klat_finite (GlobalTheory.InducedType.induced_type D).1.1 hc.1.1 h₁ h₂ (GlobalTheory.ThetaInter.klat_facts hc h₂).1`. Conclude with `AddSubgroup.index_ne_zero_of_finite`.
-/
theorem index_ne_zero (hc : Crv D cc δ) {A₁ A₂ : AddSubgroup (VC D N N')} (h₁ : KLat D (tor0 D cc δ) A₁)
    (h₂ : KLat D (tor0 D cc δ) A₂) : (A₁.addSubgroupOf A₂).index ≠ 0 := by
  haveI := GlobalTheory.ThetaInter.klat_finite (GlobalTheory.InducedType.induced_type D).1.1 hc.1.1 h₁ h₂
    (GlobalTheory.ThetaInter.klat_facts hc h₂).1
  exact AddSubgroup.index_ne_zero_of_finite

/- English proof (translation)
Rewrite using `[hA.Iop_eq]`. Use function extensionality and compare the values at `z`. Establish `hi : (A.addSubgroupOf A).index = 1` using `by simp`. Establish `hc : Nat.card (A ⧸ A.addSubgroupOf A) = 1` using `hi`. Take `⟨hs, ⟨q₀⟩⟩` from `Nat.card_eq_one_iff_unique.1 hc`.

Rewrite using `[finsum_eq_single _ q₀ (fun q hq => absurd (Subsingleton.elim q q₀) hq), hi, ((hA.mem_ThSp e).1 he).2 _ (Quotient.out q₀ : A).2]`. Simplify using the standard rewrite rules.
-/
theorem iop_self {T : Tor D} {A : AddSubgroup (VC D N N')} (hA : Nice D T A) {e : VC D N N' → ℂ}
    (he : e ∈ ThSp D T A) : Iop D T A A e = e := by
  rw [hA.Iop_eq]
  funext z
  have hi : (A.addSubgroupOf A).index = 1 := by simp
  have hc : Nat.card (A ⧸ A.addSubgroupOf A) = 1 := hi
  obtain ⟨hs, ⟨q₀⟩⟩ := Nat.card_eq_one_iff_unique.1 hc
  rw [finsum_eq_single _ q₀ (fun q hq => absurd (Subsingleton.elim q q₀) hq), hi,
    ((hA.mem_ThSp e).1 he).2 _ (Quotient.out q₀ : A).2]
  simp

/- English proof (translation)
Introduce `D cc δ hc N N'`. Use `⟨fun A hA => nice_of_klat hc hA, fun A₁ A₂ h₁ h₂ _ _ _ => index_ne_zero hc h₁ h₂, fun A hA e he => iop_self (nice_of_klat hc hA) he, fun A₁ A₂ A₃ h₁ h₂ h₃ e he h0 => ?_⟩` and prove the remaining obligations. Take `⟨μ, hμ, h⟩` from `GlobalTheory.TripleIntertwiner.triple_constant D cc δ hc N N' A₁ A₂ A₃ h₁ h₂ h₃ e he`. Conclude with `⟨μ, nice_of_klat hc h₁, nice_of_klat hc h₂, nice_of_klat hc h₃, index_ne_zero hc h₁ h₂, index_ne_zero hc h₂ h₃, index_ne_zero hc h₁ h₃, he, h0, hμ, h⟩`.
-/
theorem klat_triples : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ A : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A → Nice D (tor0 D cc δ) A) ∧ (∀ A₁ A₂ : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → ∀ e ∈ ThSp D (tor0 D cc δ) A₁, e ≠ 0 → (A₁.addSubgroupOf A₂).index ≠ 0) ∧ (∀ A : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A → ∀ e ∈ ThSp D (tor0 D cc δ) A, Iop D (tor0 D cc δ) A A e = e) ∧ ∀ A₁ A₂ A₃ : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → KLat D (tor0 D cc δ) A₃ → ∀ e ∈ ThSp D (tor0 D cc δ) A₁, e ≠ 0 → ∃ μ, Trip D (tor0 D cc δ) A₁ A₂ A₃ e μ := by
  intro D cc δ hc N N'
  refine ⟨fun A hA => nice_of_klat hc hA, fun A₁ A₂ h₁ h₂ _ _ _ => index_ne_zero hc h₁ h₂,
    fun A hA e he => iop_self (nice_of_klat hc hA) he, fun A₁ A₂ A₃ h₁ h₂ h₃ e he h0 => ?_⟩
  obtain ⟨μ, hμ, h⟩ := GlobalTheory.TripleIntertwiner.triple_constant D cc δ hc N N' A₁ A₂ A₃ h₁ h₂ h₃ e he
  exact ⟨μ, nice_of_klat hc h₁, nice_of_klat hc h₂, nice_of_klat hc h₃, index_ne_zero hc h₁ h₂,
    index_ne_zero hc h₂ h₃, index_ne_zero hc h₁ h₃, he, h0, hμ, h⟩

end GlobalTheory.ThetaTriple
