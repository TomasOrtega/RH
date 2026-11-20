import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralTensorAdelesEqAdelicCompletionOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatIntFacts

/- English proof (translation)
Establish `a1 : P.intValuation ϖ ≤ WithZero.exp (-((1 : ℕ) : ℤ))` using `(P.intValuation_le_pow_iff_mem ϖ 1).2 (by rw [pow_one]; exact h1)`. Establish `a2 : ¬ P.intValuation ϖ ≤ WithZero.exp (-((2 : ℕ) : ℤ))` using `fun h => h2 ((P.intValuation_le_pow_iff_mem ϖ 2).1 h)`. Establish `a0 : P.intValuation ϖ ≠ 0` using `fun h => a2 (h ▸ zero_le')`. Rewrite `a1`, `a2`, the goal using `[← WithZero.exp_log a0]`. Rewrite `a1`, `a2` using `[WithZero.exp_le_exp]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem intValuation_uniformiser {R : Type} [CommRing R] [IsDedekindDomain R] (P : HeightOneSpectrum R) {ϖ : R}
    (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) : P.intValuation ϖ = WithZero.exp (-1 : ℤ) := by
  have a1 : P.intValuation ϖ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (P.intValuation_le_pow_iff_mem ϖ 1).2 (by rw [pow_one]; exact h1)
  have a2 : ¬ P.intValuation ϖ ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((P.intValuation_le_pow_iff_mem ϖ 2).1 h)
  have a0 : P.intValuation ϖ ≠ 0 := fun h => a2 (h ▸ zero_le')
  rw [← WithZero.exp_log a0] at a1 a2 ⊢
  rw [WithZero.exp_le_exp] at a1 a2
  congr 1
  omega

/- English proof (translation)
Establish `key : ∀ X Y : Matrix (Fin n) (Fin n) R, (ε • X + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) * (ε • Y + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) = ε • (X * Y) + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)`. Introduce `X Y`. Establish `e1 : ε * (1 - ε) = 0` using `by linear_combination -hε`. Establish `e2 : (1 - ε) * ε = 0` using `by linear_combination -hε`. Establish `e3 : (1 - ε) * (1 - ε) = 1 - ε` using `by linear_combination hε`.

Simplify using `only [add_mul, mul_add, smul_mul_smul_comm, hε, e1, e2, e3, zero_smul, mul_one, add_zero, zero_add]`. Establish `h1` using `key B C`. Rewrite `h1` using `[h, ← add_smul, add_sub_cancel, one_smul]`. Establish `h2` using `mul_eq_one_comm.1 h1`. Rewrite `h2` using `[key]`.

Rewrite using `[eq_sub_of_add_eq h2, sub_smul, one_smul, sub_sub_cancel]`.
-/
theorem exists_left_inverse {R : Type} [CommRing R] {n : ℕ} (ε : R) (B C : Matrix (Fin n) (Fin n) R)
    (hε : ε * ε = ε) (h : ε • (B * C) = ε • (1 : Matrix (Fin n) (Fin n) R)) :
    ε • (C * B) = ε • (1 : Matrix (Fin n) (Fin n) R) := by
  have key : ∀ X Y : Matrix (Fin n) (Fin n) R,
      (ε • X + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) * (ε • Y + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) =
        ε • (X * Y) + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) := by
    intro X Y
    have e1 : ε * (1 - ε) = 0 := by linear_combination -hε
    have e2 : (1 - ε) * ε = 0 := by linear_combination -hε
    have e3 : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hε
    simp only [add_mul, mul_add, smul_mul_smul_comm, hε, e1, e2, e3, zero_smul, mul_one, add_zero, zero_add]
  have h1 := key B C
  rw [h, ← add_smul, add_sub_cancel, one_smul] at h1
  have h2 := mul_eq_one_comm.1 h1
  rw [key] at h2
  rw [eq_sub_of_add_eq h2, sub_smul, one_smul, sub_sub_cancel]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D V`. Use `⟨GlobalTheory.LatDual.smul_mem_lamHat V, ?_, ?_⟩` and prove the remaining obligations. Introduce `P e ϖ ϖ' he h1 h2 h1' h2' n`. Establish `hv : P.valuation D.host.E ((ϖ' : D.host.E) ^ n / (ϖ : D.host.E) ^ n) ≤ 1`. Establish `v1 : P.valuation D.host.E (ϖ : D.host.E) = WithZero.exp (-1 : ℤ)` using `(P.valuation_of_algebraMap ϖ).trans (intValuation_uniformiser P h1 h2)`.

Establish `v2 : P.valuation D.host.E (ϖ' : D.host.E) = WithZero.exp (-1 : ℤ)` using `(P.valuation_of_algebraMap ϖ').trans (intValuation_uniformiser P h1' h2')`. Rewrite using `[map_div₀, map_zpow₀, map_zpow₀, v1, v2]`. Conclude with `div_self_le_one _`. Take `⟨a, b, hab⟩` from `P.exists_primeCompl_mul_eq_of_integer _ hv`. Establish `hb : (b : 𝓞 D.host.E) ∉ P.asIdeal` using `b.2`.

Establish `hb0 : (b : 𝓞 D.host.E) ≠ 0` using `fun h => hb (h ▸ zero_mem _)`. Establish `hb1 : ((b : 𝓞 D.host.E) : D.host.E) ≠ 0` using `by exact_mod_cast hb0`. Establish `hi : finPart D (e * incA D (((b : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D`. Assume the negation of the conclusion as `hc`. Conclude with `hb ((he.2 _ hb0).2 hc)`.

Establish `hq : (ϖ' : D.host.E) ^ n / (ϖ : D.host.E) ^ n = (a : D.host.E) * ((b : 𝓞 D.host.E) : D.host.E)⁻¹`. Rewrite using `[eq_mul_inv_iff_mul_eq₀ hb1]`. Conclude with `hab`. Establish `ha : finPart D (incA D (a : D.host.E)) ∈ intAE D` using `AddSubgroup.subset_closure ⟨1, fun v => one_mem _, a, rfl⟩`. Establish `hm : ∀ {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E}, x ∈ intAE D → y ∈ intAE D → x * y ∈ intAE D`.

Introduce `x y hx hy`. Use `AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy` and prove the remaining obligations. Introduce and unpack `_ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩`. Use `AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`.

Conclude with `mul_mem (ha w) (hb w)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul]`. Both sides reduce to the same expression. Introduce `x _`. Rewrite using `[zero_mul]`.

Conclude with `zero_mem _`. Introduce `x _`. Rewrite using `[mul_zero]`. Conclude with `zero_mem _`. Introduce `x y z _ _ _ h1 h2`.

Rewrite using `[add_mul]`. Conclude with `add_mem h1 h2`. Introduce `x y z _ _ _ h1 h2`. Rewrite using `[mul_add]`. Conclude with `add_mem h1 h2`.

Introduce `x y _ _ h`. Rewrite using `[neg_mul]`. Conclude with `neg_mem h`. Introduce `x y _ _ h`. Rewrite using `[mul_neg]`.

Conclude with `neg_mem h`. Use `hm ha hi` as an intermediate fact. Rewrite `this` using `[RingHom.map_mul, mul_left_comm]`. Rewrite using `[hq, RingHom.map_mul, RingHom.map_mul]`. Conclude with `this`.

Introduce `ε B hε h`. Take `⟨-, -, -, hspan, -⟩` from `GlobalTheory.Member.latHat_eq_hat_and_gram D V`. Establish `hx : ∀ x : Fin V.rank → D.host.E, ∃ z, ∀ a, ε * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x a) = ε * B.mulVec z a`. Introduce `x`. Establish `hx : x ∈ Submodule.span D.host.E (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))`.

Rewrite using `[hspan]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨z, hz⟩` from `h (fun a => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x a) (by`.

Rewrite using `[GlobalTheory.LatDual.lamHat_eq_hat]`. Conclude with `AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩)`. Conclude with `⟨z, congrFun hz⟩`. Consider the case `zero => exact ⟨0, fun a => by simp⟩`. Consider the case `add u w _ _ hu hw`.

Take `⟨z, hz⟩` from `hu`. Take `⟨z', hz'⟩` from `hw`. Conclude with `⟨z + z', fun a => by`. Rewrite using `[Pi.add_apply, TensorProduct.tmul_add, mul_add, hz, hz', Matrix.mulVec_add, Pi.add_apply, mul_add]⟩`. Consider the case `smul c u _ hu`.

Take `⟨z, hz⟩` from `hu`. Use `⟨((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c) • z, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, ← hz, mul_left_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one]`. Use `choose z hz using hx`. Establish `hBC : ε • (B * Matrix.of fun j i => z (Pi.single i 1) j) = ε • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))`.

Use `Matrix.ext fun a i => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]`. Use `(hz (Pi.single i 1) a).symm.trans ?_` and prove the remaining obligations. Use `congr 1`. Distinguish the cases in `hai : a = i`.

Substitute `hai` using the available equality. Rewrite using `[Pi.single_eq_same, Matrix.one_apply_eq]`. Both sides reduce to the same expression. Rewrite using `[Pi.single_eq_of_ne hai, Matrix.one_apply_ne hai, TensorProduct.tmul_zero]`. Conclude with `⟨_, hBC, exists_left_inverse ε B _ hε hBC⟩`.
-/
theorem int_facts : ∀ {D : D7} (V : HSp D), (∀ a ∈ intAE D, ∀ y ∈ LamHat V, (fun i => a * y i) ∈ LamHat V) ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ ϖ' : 𝓞 D.host.E), IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → ∀ n : ℤ, finPart D e * finPart D (incA D ((ϖ' : D.host.E) ^ n / (ϖ : D.host.E) ^ n)) ∈ intAE D) ∧ ∀ (ε : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (B : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), ε * ε = ε → (∀ y ∈ LamHat V, ∃ z, (fun a => ε * y a) = fun a => ε * B.mulVec z a) → ∃ C : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), ε • (B * C) = ε • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) ∧ ε • (C * B) = ε • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
  intro D V
  refine ⟨GlobalTheory.LatDual.smul_mem_lamHat V, ?_, ?_⟩
  · intro P e ϖ ϖ' he h1 h2 h1' h2' n
    have hv : P.valuation D.host.E ((ϖ' : D.host.E) ^ n / (ϖ : D.host.E) ^ n) ≤ 1 := by
      have v1 : P.valuation D.host.E (ϖ : D.host.E) = WithZero.exp (-1 : ℤ) :=
        (P.valuation_of_algebraMap ϖ).trans (intValuation_uniformiser P h1 h2)
      have v2 : P.valuation D.host.E (ϖ' : D.host.E) = WithZero.exp (-1 : ℤ) :=
        (P.valuation_of_algebraMap ϖ').trans (intValuation_uniformiser P h1' h2')
      rw [map_div₀, map_zpow₀, map_zpow₀, v1, v2]
      exact div_self_le_one _
    obtain ⟨a, b, hab⟩ := P.exists_primeCompl_mul_eq_of_integer _ hv
    have hb : (b : 𝓞 D.host.E) ∉ P.asIdeal := b.2
    have hb0 : (b : 𝓞 D.host.E) ≠ 0 := fun h => hb (h ▸ zero_mem _)
    have hb1 : ((b : 𝓞 D.host.E) : D.host.E) ≠ 0 := by exact_mod_cast hb0
    have hi : finPart D (e * incA D (((b : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
      by_contra hc
      exact hb ((he.2 _ hb0).2 hc)
    have hq : (ϖ' : D.host.E) ^ n / (ϖ : D.host.E) ^ n = (a : D.host.E) * ((b : 𝓞 D.host.E) : D.host.E)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hb1]
      exact hab
    have ha : finPart D (incA D (a : D.host.E)) ∈ intAE D :=
      AddSubgroup.subset_closure ⟨1, fun v => one_mem _, a, rfl⟩
    have hm : ∀ {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E}, x ∈ intAE D → y ∈ intAE D → x * y ∈ intAE D := by
      intro x y hx hy
      refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
      · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
        refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
        · rw [map_mul]; exact mul_mem (ha w) (hb w)
        · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
      · intro x _; rw [zero_mul]; exact zero_mem _
      · intro x _; rw [mul_zero]; exact zero_mem _
      · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
      · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
      · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
      · intro x y _ _ h; rw [mul_neg]; exact neg_mem h
    have := hm ha hi
    rw [RingHom.map_mul, mul_left_comm] at this
    rw [hq, RingHom.map_mul, RingHom.map_mul]
    exact this
  · intro ε B hε h
    obtain ⟨-, -, -, hspan, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
    have hx : ∀ x : Fin V.rank → D.host.E, ∃ z, ∀ a,
        ε * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x a) = ε * B.mulVec z a := by
      intro x
      have hx : x ∈ Submodule.span D.host.E (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
        rw [hspan]; trivial
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨z, hz⟩ := h (fun a => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x a) (by
          rw [GlobalTheory.LatDual.lamHat_eq_hat]
          exact AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩)
        exact ⟨z, congrFun hz⟩
      | zero => exact ⟨0, fun a => by simp⟩
      | add u w _ _ hu hw =>
        obtain ⟨z, hz⟩ := hu
        obtain ⟨z', hz'⟩ := hw
        exact ⟨z + z', fun a => by
          rw [Pi.add_apply, TensorProduct.tmul_add, mul_add, hz, hz', Matrix.mulVec_add, Pi.add_apply, mul_add]⟩
      | smul c u _ hu =>
        obtain ⟨z, hz⟩ := hu
        refine ⟨((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c) • z, fun a => ?_⟩
        rw [Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, ← hz,
          mul_left_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    choose z hz using hx
    have hBC : ε • (B * Matrix.of fun j i => z (Pi.single i 1) j) =
        ε • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
      refine Matrix.ext fun a i => ?_
      rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      refine (hz (Pi.single i 1) a).symm.trans ?_
      congr 1
      by_cases hai : a = i
      · subst hai
        rw [Pi.single_eq_same, Matrix.one_apply_eq]; rfl
      · rw [Pi.single_eq_of_ne hai, Matrix.one_apply_ne hai, TensorProduct.tmul_zero]
    exact ⟨_, hBC, exists_left_inverse ε B _ hε hBC⟩

end GlobalTheory.LatIntFacts
