import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

noncomputable section

namespace GlobalTheory.KappaPowMod

/- English proof (translation)
Use `⟨one_mem _, fun σ => ?_⟩` and prove the remaining obligations. Establish `e : (⟨1, one_mem _⟩ : TaylorLogMetric.Qbar) = 1` using `rfl`. Rewrite using `[e, map_one, norm_one]`.
-/
theorem algebraicModulusOneAll_one : StandardLatticesGL3.Mod1All 1 := by
  refine ⟨one_mem _, fun σ => ?_⟩
  have e : (⟨1, one_mem _⟩ : TaylorLogMetric.Qbar) = 1 := rfl
  rw [e, map_one, norm_one]

/- English proof (translation)
Take `⟨h1, h1'⟩` from `ha`. Take `⟨h2, h2'⟩` from `hb`. Use `⟨mul_mem h1 h2, fun σ => ?_⟩` and prove the remaining obligations. Establish `e : (⟨a * b, mul_mem h1 h2⟩ : TaylorLogMetric.Qbar) = ⟨a, h1⟩ * ⟨b, h2⟩` using `rfl`. Rewrite using `[e, map_mul, norm_mul, h1' σ, h2' σ, one_mul]`.
-/
theorem algebraicModulusOneAll_mul {a b : ℂ} (ha : StandardLatticesGL3.Mod1All a) (hb : StandardLatticesGL3.Mod1All b) : StandardLatticesGL3.Mod1All (a * b) := by
  obtain ⟨h1, h1'⟩ := ha
  obtain ⟨h2, h2'⟩ := hb
  refine ⟨mul_mem h1 h2, fun σ => ?_⟩
  have e : (⟨a * b, mul_mem h1 h2⟩ : TaylorLogMetric.Qbar) = ⟨a, h1⟩ * ⟨b, h2⟩ := rfl
  rw [e, map_mul, norm_mul, h1' σ, h2' σ, one_mul]

/- English proof (translation)
Take `⟨h1, h1'⟩` from `ha`. Use `⟨inv_mem h1, fun σ => ?_⟩` and prove the remaining obligations. Establish `e : (⟨a⁻¹, inv_mem h1⟩ : TaylorLogMetric.Qbar) = (⟨a, h1⟩ : TaylorLogMetric.Qbar)⁻¹` using `rfl`. Rewrite using `[e, map_inv₀, norm_inv, h1' σ, inv_one]`.
-/
theorem algebraicModulusOneAll_inv {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) : StandardLatticesGL3.Mod1All a⁻¹ := by
  obtain ⟨h1, h1'⟩ := ha
  refine ⟨inv_mem h1, fun σ => ?_⟩
  have e : (⟨a⁻¹, inv_mem h1⟩ : TaylorLogMetric.Qbar) = (⟨a, h1⟩ : TaylorLogMetric.Qbar)⁻¹ := rfl
  rw [e, map_inv₀, norm_inv, h1' σ, inv_one]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using algebraicModulusOneAll_one`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `algebraicModulusOneAll_mul ih ha`.
-/
theorem algebraicModulusOneAll_pow {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) (n : ℕ) : StandardLatticesGL3.Mod1All (a ^ n) := by
  induction n with
  | zero => simpa using algebraicModulusOneAll_one
  | succ n ih => rw [pow_succ]; exact algebraicModulusOneAll_mul ih ha

/- English proof (translation)
Consider the cases of `n with`. Consider the case `ofNat n => simpa using algebraicModulusOneAll_pow ha n`. Consider the case `negSucc n => rw [zpow_negSucc]`. Conclude with `algebraicModulusOneAll_inv (algebraicModulusOneAll_pow ha _)`.
-/
theorem algebraicModulusOneAll_zpow {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) (n : ℤ) : StandardLatticesGL3.Mod1All (a ^ n) := by
  cases n with
  | ofNat n => simpa using algebraicModulusOneAll_pow ha n
  | negSucc n => rw [zpow_negSucc]; exact algebraicModulusOneAll_inv (algebraicModulusOneAll_pow ha _)

def phiQ (D : D7) : D.host.E →+* TaylorLogMetric.Qbar :=
  D.host.φ₀.codRestrict TaylorLogMetric.Qbar fun x => Formalism.L2.KerInert.AlgP.phi_mem_Qbar x

/- English proof (translation)
Use `set h := 2 * classNumber D.host.K with hh`. Establish `h0 : h ≠ 0` using `mul_ne_zero two_ne_zero (classNumber_ne D)`. Use `set x : D.host.E := (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E) with hx`. Establish `hx0 : x ≠ 0`. Establish `h1 : ((k.pi p : 𝓞 D.host.K) : D.host.K) ≠ 0` using `by simpa using k.pi_ne_zero p hp hs`.

Simplify `h1` using `[hx]`. Establish `hpow` using `k.rt_pow p hp hs`. Establish `hmem : k.rt p ∈ TaylorLogMetric.Qbar`. Establish `hq : k.rt p ^ h ∈ TaylorLogMetric.Qbar`. Rewrite using `[hpow]`.

Conclude with `div_mem (Formalism.L2.KerInert.AlgP.phi_mem_Qbar _) (Formalism.L2.KerInert.AlgP.phi_mem_Qbar _)`. Conclude with `mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := h) (Nat.pos_of_ne_zero h0) (mem_algebraicClosure_iff.1 hq))`. Use `⟨hmem, fun σ => ?_⟩` and prove the remaining obligations. Set `ψ : D.host.E →+* ℂ` to `σ.comp (phiQ D)`. Establish `hc : ψ (D.host.conj x) = starRingEnd ℂ (ψ x)` using `Formalism.HC.HostAx.conjE_apply _ _ _`.

Establish `hψ0 : ψ x ≠ 0` using `(map_ne_zero ψ).2 hx0`. Establish `e : (⟨k.rt p, hmem⟩ : TaylorLogMetric.Qbar) ^ h = phiQ D x / phiQ D (D.host.conj x)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [IntermediateField.coe_pow, IntermediateField.coe_div]`. Conclude with `hpow`.

Establish `hn : ‖σ ⟨k.rt p, hmem⟩‖ ^ h = 1`. Rewrite using `[← norm_pow, ← map_pow, e, map_div₀]`. Express the relevant statement in the definitionally equal form `‖ψ x / ψ (D.host.conj x)‖ = 1`. Rewrite using `[hc, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hψ0)]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) h0).1 hn`.
-/
theorem splitPrime_rootChoice_algebraicModulusOneAll {D : D7} {γ₀ : IsoK D} (k : KapChoice γ₀) (p : ℕ) (hp : p.Prime) (hs : SplitK D p) :
    StandardLatticesGL3.Mod1All (k.rt p) := by
  set h := 2 * classNumber D.host.K with hh
  have h0 : h ≠ 0 := mul_ne_zero two_ne_zero (classNumber_ne D)
  set x : D.host.E := (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E) with hx
  have hx0 : x ≠ 0 := by
    have h1 : ((k.pi p : 𝓞 D.host.K) : D.host.K) ≠ 0 := by simpa using k.pi_ne_zero p hp hs
    simpa [hx] using h1
  have hpow := k.rt_pow p hp hs
  have hmem : k.rt p ∈ TaylorLogMetric.Qbar := by
    have hq : k.rt p ^ h ∈ TaylorLogMetric.Qbar := by
      rw [hpow]
      exact div_mem (Formalism.L2.KerInert.AlgP.phi_mem_Qbar _) (Formalism.L2.KerInert.AlgP.phi_mem_Qbar _)
    exact mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := h) (Nat.pos_of_ne_zero h0)
      (mem_algebraicClosure_iff.1 hq))
  refine ⟨hmem, fun σ => ?_⟩
  let ψ : D.host.E →+* ℂ := σ.comp (phiQ D)
  have hc : ψ (D.host.conj x) = starRingEnd ℂ (ψ x) := Formalism.HC.HostAx.conjE_apply _ _ _
  have hψ0 : ψ x ≠ 0 := (map_ne_zero ψ).2 hx0
  have e : (⟨k.rt p, hmem⟩ : TaylorLogMetric.Qbar) ^ h = phiQ D x / phiQ D (D.host.conj x) := by
    apply Subtype.ext
    simp only [IntermediateField.coe_pow, IntermediateField.coe_div]
    exact hpow
  have hn : ‖σ ⟨k.rt p, hmem⟩‖ ^ h = 1 := by
    rw [← norm_pow, ← map_pow, e, map_div₀]
    change ‖ψ x / ψ (D.host.conj x)‖ = 1
    rw [hc, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hψ0)]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) h0).1 hn

/- English proof (translation)
Introduce `D cc δ B m`. Use `algebraicModulusOneAll_pow ?_ m` and prove the remaining obligations. Use `show StandardLatticesGL3.Mod1All (∏ᶠ p : {p : ℕ // p.Prime ∧ SplitK D p}, B.kc.rt p ^ (-(B.kc.yP p)))`. Conclude with `finprod_induction StandardLatticesGL3.Mod1All algebraicModulusOneAll_one (fun _ _ => algebraicModulusOneAll_mul) fun p => algebraicModulusOneAll_zpow (splitPrime_rootChoice_algebraicModulusOneAll B.kc p p.2.1 p.2.2) _`.
-/
theorem kappa_pow_mod1All : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (m : ℕ),
    StandardLatticesGL3.Mod1All (B.kappa ^ m) := by
  intro D cc δ B m
  refine algebraicModulusOneAll_pow ?_ m
  show StandardLatticesGL3.Mod1All (∏ᶠ p : {p : ℕ // p.Prime ∧ SplitK D p}, B.kc.rt p ^ (-(B.kc.yP p)))
  exact finprod_induction StandardLatticesGL3.Mod1All algebraicModulusOneAll_one (fun _ _ => algebraicModulusOneAll_mul)
    fun p => algebraicModulusOneAll_zpow (splitPrime_rootChoice_algebraicModulusOneAll B.kc p p.2.1 p.2.2) _

end GlobalTheory.KappaPowMod
