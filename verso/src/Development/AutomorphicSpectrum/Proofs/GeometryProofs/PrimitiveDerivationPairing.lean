import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MemPrimitiveTensorsIffIsPrimitiveElem
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusStableSubspaceElementStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SubspaceContainsUnitStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NilpotentDerivationRankStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultiplicativeDerivationRankStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveElementPowersIndepStatement
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HopfCount
open Coalgebra GlobalTheory WithConv

section dual
variable {k : Type} [Field k] {A : Type} [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A]
  [Module.Finite k A]

/- English proof (translation)
Rewrite using `[CartierDual.mul_apply, hg]`. Simplify using the standard rewrite rules.
-/
theorem mul_apply_prim {g : A} (hg : comul (R := k) g = g ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] g)
    (w w' : CartierDual k A) : (w * w') g = w g * w' 1 + w 1 * w' g := by
  rw [CartierDual.mul_apply, hg]
  simp

noncomputable def dualDer (f : A) (hf : comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) :
    Derivation k (CartierDual k A) (CartierDual k A) :=
  Derivation.mk' (CartierDual.transpose (LinearMap.mulLeft k f)) (by
    intro a b
    refine CartierDual.ext_apply fun c => ?_
    have h : ∀ t : A ⊗[k] A, CartierDual.pair k A A (a ⊗ₜ b) ((f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) * t) =
        CartierDual.pair k A A ((CartierDual.transpose (LinearMap.mulLeft k f) a) ⊗ₜ b) t +
        CartierDual.pair k A A (a ⊗ₜ (CartierDual.transpose (LinearMap.mulLeft k f) b)) t := by
      intro t
      induction t with
      | zero => simp
      | add x y hx hy => simp only [mul_add, map_add, hx, hy]; ring
      | tmul c d => simp [add_mul]
    have h2 := h (comul (R := k) c)
    rw [← hf, ← Bialgebra.comul_mul] at h2
    change (a * b) (f * c) = (a * CartierDual.transpose (LinearMap.mulLeft k f) b +
      b * CartierDual.transpose (LinearMap.mulLeft k f) a) c
    rw [mul_comm b, CartierDual.mul_apply a b (f * c), h2, ← CartierDual.mul_apply, ← CartierDual.mul_apply]
    simp [add_comm])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dualDer_apply (f : A) (hf) (w : CartierDual k A) (a : A) :
    dualDer (k := k) f hf w a = w (f * a) := rfl

/- English proof (translation)
Proceed by induction on `n generalizing a with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Function.iterate_succ_apply', dualDer_apply, ih, pow_succ, mul_assoc, mul_comm f a, ← mul_assoc, mul_assoc, mul_comm a f]`.
-/
theorem dualDer_iter (f : A) (hf) (n : ℕ) (w : CartierDual k A) (a : A) :
    ((⇑(dualDer (k := k) f hf))^[n] w) a = w (f ^ n * a) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', dualDer_apply, ih, pow_succ, mul_assoc, mul_comm f a,
      ← mul_assoc, mul_assoc, mul_comm a f]

/- English proof (translation)
Set `X : CartierDual k (CartierDual k A)` to `toConv x.toLinearMap`. Set `g : A` to `(CartierDual.bidual k A).symm X`. Establish `hg : ∀ w : CartierDual k A, x w = w g` using `fun w => by`. Rewrite using `[CartierDual.apply_bidual_symm]`. Both sides reduce to the same expression.

Use `⟨g, ?_, hg⟩` and prove the remaining obligations. Establish `h1 : comul (R` using `k) g = g ⊗ₜ[k] g := by`. Use `CartierDual.tensor_eq_of_forall_pair fun φ ψ => ?_` and prove the remaining obligations. Rewrite using `[← CartierDual.mul_apply, CartierDual.pair_tmul_tmul, ← hg, ← hg, ← hg, map_mul]`. Establish `h2 : counit (R` using `k) g = 1 := by`.

Rewrite using `[← CartierDual.one_apply, ← hg, map_one]`. Establish `h3` using `HopfAlgebra.mul_antipode_rTensor_comul_apply (R := k) g`. Rewrite `h3` using `[h1, h2]`. Simplify using `at h3`. Conclude with `IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact h3)`.
-/
theorem point_eval (x : CartierDual k A →ₐ[k] k) :
    ∃ g : A, IsUnit g ∧ ∀ w : CartierDual k A, x w = w g := by
  let X : CartierDual k (CartierDual k A) := toConv x.toLinearMap
  let g : A := (CartierDual.bidual k A).symm X
  have hg : ∀ w : CartierDual k A, x w = w g := fun w => by
    rw [CartierDual.apply_bidual_symm]; rfl
  refine ⟨g, ?_, hg⟩
  have h1 : comul (R := k) g = g ⊗ₜ[k] g := by
    refine CartierDual.tensor_eq_of_forall_pair fun φ ψ => ?_
    rw [← CartierDual.mul_apply, CartierDual.pair_tmul_tmul, ← hg, ← hg, ← hg, map_mul]
  have h2 : counit (R := k) g = 1 := by
    rw [← CartierDual.one_apply, ← hg, map_one]
  have h3 := HopfAlgebra.mul_antipode_rTensor_comul_apply (R := k) g
  rw [h1, h2] at h3
  simp at h3
  exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact h3)

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `h (CartierDual.eq_of_forall_apply (R := k) fun w => by simp [hc w])`.
-/
theorem exists_dual_ne {a : A} (h : a ≠ 0) : ∃ w : CartierDual k A, w a ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (CartierDual.eq_of_forall_apply (R := k) fun w => by simp [hc w])

end dual

/- English proof (translation)
Establish `hp2 : 2 ≤ p` using `hp.out.two_le`. Set `D` to `dualDer (k := k) f hf`. Set `ε` to `Bialgebra.counitAlgHom k (CartierDual k A)`. Establish `hεD : ∀ z : CartierDual k A, ε (D z) = z f` using `fun z => by show (D z) 1 = z f`. Rewrite using `[dualDer_apply, mul_one]`.

Establish `hG : Module.finrank k (CartierDual k A) = p * Module.finrank k (LinearMap.ker (D : CartierDual k A →ₗ[k] CartierDual k A)) ∧ ∃ z : CartierDual k A, ε (D z) ≠ 0 ∧ ∀ u : CartierDual k A →ₗ[k] k, (∀ a b : CartierDual k A, u (a * b) = u a * ε b + ε a * u b) → (∀ a : CartierDual k A, …`. Break down `hc with hc | hc` into its components or cases. Establish `hD : ∀ a, (⇑D)^[p] a = 0` using `fun a => CartierDual.ext_apply fun c => by`. Rewrite using `[dualDer_iter, hc]`. Simplify using the standard rewrite rules.

Establish `hnz : f ^ (p - 1) ≠ 0`. Introduce `hz`. Use `GlobalTheory.T.primitive_element_powers_indep k p A f hf h0 (fun i => if i = p - 1 then 1 else 0) (by` as an intermediate fact. Rewrite using `[Finset.sum_eq_single (p - 1)]`. Simplify using `[hz]`.

Introduce `b _ hb`. Simplify using `[hb]`. Introduce `h; simp at h; omega) (p - 1) (by omega)`. Simplify using `at this`. Take `⟨w, hw, hwu⟩` from `GlobalTheory.T.subspace_contains_unit k (CartierDual k A) (LinearMap.range (((D : CartierDual k A →ₗ[k] CartierDual k A)) ^ (p - 1))) (by`.

Introduce `x`. Take `⟨g, hgu, hg⟩` from `point_eval x`. Take `⟨w, hw⟩` from `exists_dual_ne (k := k) (hgu.mul_left_eq_zero.not.2 hnz)`. Use `⟨_, ⟨w, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hg, Module.End.pow_apply]`.

Conclude with `(dualDer_iter f hf (p - 1) w g).symm ▸ hw)`. Take `⟨t, rfl⟩` from `hw`. Conclude with `GlobalTheory.T.nilpotent_derivation_rank k p _ D ε hD t (by simpa [Module.End.pow_apply] using hwu)`. Establish `hD : ∀ a, (⇑D)^[p] a = D a` using `fun a => CartierDual.ext_apply fun c => by`. Rewrite using `[dualDer_iter, hc]`.

Both sides reduce to the same expression. Set `u0 : A` to `∑ i ∈ Finset.Ico 1 p, f ^ i`. Establish `hu1 : f * u0 = u0`. Establish `h` using `geom_sum_Ico_mul f (show 1 ≤ p by omega)`. Rewrite `h` using `[hc, pow_one, sub_self]`.

Establish `h' : u0 * (f - 1) = 0` using `h`. Take the linear combination `h'`. Establish `hu0 : u0 ≠ 0`. Introduce `hz`. Use `GlobalTheory.T.primitive_element_powers_indep k p A f hf h0 (fun i => if i = 0 then 0 else 1) (by` as an intermediate fact.

Rewrite using `[Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]`. Simplify using `only [if_true, zero_smul, zero_add]`. Rewrite using `[← hz]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `: i ≠ 0` using `by have := (Finset.mem_Ico.1 hi).1; omega`.

Simplify using `[this]) 1 (by omega)`. Simplify using `at this`. Take `⟨w, hw, hwu⟩` from `GlobalTheory.T.subspace_contains_unit k (CartierDual k A) (LinearMap.ker ((D : CartierDual k A →ₗ[k] CartierDual k A) - LinearMap.id)) (by`. Introduce `x`. Take `⟨g, hgu, hg⟩` from `point_eval x`.

Take `⟨w, hw⟩` from `exists_dual_ne (k := k) (hgu.mul_left_eq_zero.not.2 hu0)`. Use `⟨CartierDual.transpose (LinearMap.mulLeft k u0) w, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`. Use `CartierDual.ext_apply fun c => ?_` and prove the remaining obligations. Use `show w (u0 * (f * c)) = w (u0 * c)`.

Rewrite using `[← mul_assoc, mul_comm u0, hu1]`. Rewrite using `[hg]`. Conclude with `hw)`. Establish `hw' : D w = w`. Simplify `hw` using `[sub_eq_zero]`.

Conclude with `GlobalTheory.T.multiplicative_derivation_rank k p _ D ε hD w hwu hw'`. Take `⟨hdim, z, hz, hu⟩` from `hG`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Set `Ik : Submodule k A` to `(Ideal.span {f}).restrictScalars k`. Establish `h1 : Module.finrank k (CartierDual k A) = Module.finrank k A`.

Rewrite using `[LinearEquiv.finrank_eq (CartierDual.toDual k A)]`. Conclude with `Subspace.dual_finrank_eq`. Establish `h2 : Module.finrank k (A ⧸ Ideal.span {f}) = Module.finrank k (A ⧸ Ik)` using `(LinearEquiv.finrank_eq (Submodule.Quotient.restrictScalarsEquiv k (Ideal.span {f}))).symm`. Establish `h3` using `Subspace.finrank_add_finrank_dualAnnihilator_eq Ik`. Establish `h4` using `Submodule.finrank_quotient_add_finrank Ik`.

Establish `h5 : (LinearMap.ker (D : CartierDual k A →ₗ[k] CartierDual k A)).map (CartierDual.toDual k A).toLinearMap = Ik.dualAnnihilator`. Use extensionality with `φ`. Rewrite using `[Submodule.mem_map, Submodule.mem_dualAnnihilator]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩ x hx`.

Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 hx`. Establish `hw0 : D w = 0` using `LinearMap.mem_ker.1 hw`. Establish `: (D w) a = 0` using `by rw [hw0]; rfl`. Rewrite `this` using `[dualDer_apply]`. Rewrite using `[mul_comm]`.

Conclude with `this`. Introduce `h`. Use `⟨(CartierDual.toDual k A).symm φ, ?_, by simp⟩` and prove the remaining obligations. Use `LinearMap.mem_ker.2 (CartierDual.ext_apply fun c => ?_)` and prove the remaining obligations. Conclude with `h _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f))`.

Establish `h6 : Module.finrank k (LinearMap.ker (D : CartierDual k A →ₗ[k] CartierDual k A)) = Module.finrank k Ik.dualAnnihilator`. Rewrite using `[← h5]`. Conclude with `LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (CartierDual.toDual k A).injective _)`. Rewrite using `[← h1, hdim, h6, h2]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Introduce `g hgI hg`. Take `⟨b, rfl⟩` from `Ideal.mem_span_singleton'.1 hgI`. Establish `hzf : z f ≠ 0` using `by rwa [hεD] at hz`. Set `a : k` to `z (b * f) / z f`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Set `u : CartierDual k A →ₗ[k] k` to `CartierDual.evalAt k A (b * f) - a • CartierDual.evalAt k A f`. Establish `hua : ∀ w : CartierDual k A, u w = w (b * f) - a * w f` using `fun w => rfl`. Establish `hu0` using `hu u (fun w w' => by`. Rewrite using `[hua, hua, hua, mul_apply_prim hg, mul_apply_prim hf]`.

Use `show _ = (w (b * f) - a * w f) * w' 1 + w 1 * (w' (b * f) - a * w' f)`. Use the proof step `ring) (fun w hw => by`. Establish `h1 : ∀ c, w (f * c) = 0` using `fun c => by`. Establish `: (D w) c = 0` using `by rw [hw]; rfl`. Rewrite `this` using `[dualDer_apply]`. Then use the resulting hypothesis.

Establish `h2 : w f = 0` using `by simpa using h1 1`. Establish `h3 : w (b * f) = 0` using `by rw [mul_comm]; exact h1 b`. Rewrite using `[hua, h2, h3]; simp) (by`. Rewrite using `[hua]`. Simplify using `only [a]`.

Clear the denominators using the available nonvanishing facts. Use the proof step `ring)`. Use `CartierDual.eq_of_forall_apply (R := k) fun w => ?_` and prove the remaining obligations. Use `congr($hu0 w)` as an intermediate fact. Rewrite `this` using `[hua]`.

Simplify using `only [LinearMap.zero_apply, sub_eq_zero] at this`. Rewrite using `[this, map_smul]`. Both sides reduce to the same expression.
-/
theorem key (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]
    (f : A) (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) (h0 : f ≠ 0)
    (hc : f ^ p = 0 ∨ f ^ p = f) :
    Module.finrank k A = p * Module.finrank k (A ⧸ Ideal.span {f}) ∧
    ∀ g ∈ Ideal.span {f}, Coalgebra.comul (R := k) g = g ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] g →
      ∃ a : k, g = a • f := by
  classical
  have hp2 : 2 ≤ p := hp.out.two_le
  let D := dualDer (k := k) f hf
  let ε := Bialgebra.counitAlgHom k (CartierDual k A)
  have hεD : ∀ z : CartierDual k A, ε (D z) = z f := fun z => by
    show (D z) 1 = z f
    rw [dualDer_apply, mul_one]
  have hG : Module.finrank k (CartierDual k A) =
        p * Module.finrank k (LinearMap.ker (D : CartierDual k A →ₗ[k] CartierDual k A)) ∧
      ∃ z : CartierDual k A, ε (D z) ≠ 0 ∧ ∀ u : CartierDual k A →ₗ[k] k,
        (∀ a b : CartierDual k A, u (a * b) = u a * ε b + ε a * u b) →
        (∀ a : CartierDual k A, D a = 0 → u a = 0) → u z = 0 → u = 0 := by
    rcases hc with hc | hc
    · have hD : ∀ a, (⇑D)^[p] a = 0 := fun a => CartierDual.ext_apply fun c => by
        rw [dualDer_iter, hc]; simp
      have hnz : f ^ (p - 1) ≠ 0 := by
        intro hz
        have := GlobalTheory.T.primitive_element_powers_indep k p A f hf h0 (fun i => if i = p - 1 then 1 else 0) (by
          rw [Finset.sum_eq_single (p - 1)]
          · simp [hz]
          · intro b _ hb; simp [hb]
          · intro h; simp at h; omega) (p - 1) (by omega)
        simp at this
      obtain ⟨w, hw, hwu⟩ := GlobalTheory.T.subspace_contains_unit k (CartierDual k A)
        (LinearMap.range (((D : CartierDual k A →ₗ[k] CartierDual k A)) ^ (p - 1))) (by
        intro x
        obtain ⟨g, hgu, hg⟩ := point_eval x
        obtain ⟨w, hw⟩ := exists_dual_ne (k := k) (hgu.mul_left_eq_zero.not.2 hnz)
        refine ⟨_, ⟨w, rfl⟩, ?_⟩
        rw [hg, Module.End.pow_apply]
        exact (dualDer_iter f hf (p - 1) w g).symm ▸ hw)
      obtain ⟨t, rfl⟩ := hw
      exact GlobalTheory.T.nilpotent_derivation_rank k p _ D ε hD t (by simpa [Module.End.pow_apply] using hwu)
    · have hD : ∀ a, (⇑D)^[p] a = D a := fun a => CartierDual.ext_apply fun c => by
        rw [dualDer_iter, hc]; rfl
      let u0 : A := ∑ i ∈ Finset.Ico 1 p, f ^ i
      have hu1 : f * u0 = u0 := by
        have h := geom_sum_Ico_mul f (show 1 ≤ p by omega)
        rw [hc, pow_one, sub_self] at h
        have h' : u0 * (f - 1) = 0 := h
        linear_combination h'
      have hu0 : u0 ≠ 0 := by
        intro hz
        have := GlobalTheory.T.primitive_element_powers_indep k p A f hf h0 (fun i => if i = 0 then 0 else 1) (by
          rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
          simp only [if_true, zero_smul, zero_add]
          rw [← hz]
          refine Finset.sum_congr rfl fun i hi => ?_
          have : i ≠ 0 := by have := (Finset.mem_Ico.1 hi).1; omega
          simp [this]) 1 (by omega)
        simp at this
      obtain ⟨w, hw, hwu⟩ := GlobalTheory.T.subspace_contains_unit k (CartierDual k A)
        (LinearMap.ker ((D : CartierDual k A →ₗ[k] CartierDual k A) - LinearMap.id)) (by
        intro x
        obtain ⟨g, hgu, hg⟩ := point_eval x
        obtain ⟨w, hw⟩ := exists_dual_ne (k := k) (hgu.mul_left_eq_zero.not.2 hu0)
        refine ⟨CartierDual.transpose (LinearMap.mulLeft k u0) w, ?_, ?_⟩
        · rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
          refine CartierDual.ext_apply fun c => ?_
          show w (u0 * (f * c)) = w (u0 * c)
          rw [← mul_assoc, mul_comm u0, hu1]
        · rw [hg]; exact hw)
      have hw' : D w = w := by
        simpa [sub_eq_zero] using hw
      exact GlobalTheory.T.multiplicative_derivation_rank k p _ D ε hD w hwu hw'
  obtain ⟨hdim, z, hz, hu⟩ := hG
  refine ⟨?_, ?_⟩
  · let Ik : Submodule k A := (Ideal.span {f}).restrictScalars k
    have h1 : Module.finrank k (CartierDual k A) = Module.finrank k A := by
      rw [LinearEquiv.finrank_eq (CartierDual.toDual k A)]
      exact Subspace.dual_finrank_eq
    have h2 : Module.finrank k (A ⧸ Ideal.span {f}) = Module.finrank k (A ⧸ Ik) :=
      (LinearEquiv.finrank_eq (Submodule.Quotient.restrictScalarsEquiv k (Ideal.span {f}))).symm
    have h3 := Subspace.finrank_add_finrank_dualAnnihilator_eq Ik
    have h4 := Submodule.finrank_quotient_add_finrank Ik
    have h5 : (LinearMap.ker (D : CartierDual k A →ₗ[k] CartierDual k A)).map
        (CartierDual.toDual k A).toLinearMap = Ik.dualAnnihilator := by
      ext φ
      rw [Submodule.mem_map, Submodule.mem_dualAnnihilator]
      constructor
      · rintro ⟨w, hw, rfl⟩ x hx
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
        have hw0 : D w = 0 := LinearMap.mem_ker.1 hw
        have : (D w) a = 0 := by rw [hw0]; rfl
        rw [dualDer_apply] at this
        rw [mul_comm]; exact this
      · intro h
        refine ⟨(CartierDual.toDual k A).symm φ, ?_, by simp⟩
        refine LinearMap.mem_ker.2 (CartierDual.ext_apply fun c => ?_)
        exact h _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f))
    have h6 : Module.finrank k (LinearMap.ker (D : CartierDual k A →ₗ[k] CartierDual k A)) =
        Module.finrank k Ik.dualAnnihilator := by
      rw [← h5]
      exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
        (CartierDual.toDual k A).injective _)
    rw [← h1, hdim, h6, h2]
    congr 1
    omega
  · intro g hgI hg
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hgI
    have hzf : z f ≠ 0 := by rwa [hεD] at hz
    let a : k := z (b * f) / z f
    refine ⟨a, ?_⟩
    let u : CartierDual k A →ₗ[k] k :=
      CartierDual.evalAt k A (b * f) - a • CartierDual.evalAt k A f
    have hua : ∀ w : CartierDual k A, u w = w (b * f) - a * w f := fun w => rfl
    have hu0 := hu u (fun w w' => by
      rw [hua, hua, hua, mul_apply_prim hg, mul_apply_prim hf]
      show _ = (w (b * f) - a * w f) * w' 1 + w 1 * (w' (b * f) - a * w' f)
      ring) (fun w hw => by
      have h1 : ∀ c, w (f * c) = 0 := fun c => by
        have : (D w) c = 0 := by rw [hw]; rfl
        rwa [dualDer_apply] at this
      have h2 : w f = 0 := by simpa using h1 1
      have h3 : w (b * f) = 0 := by rw [mul_comm]; exact h1 b
      rw [hua, h2, h3]; simp) (by
      rw [hua]
      simp only [a]
      field_simp
      ring)
    refine CartierDual.eq_of_forall_apply (R := k) fun w => ?_
    have := congr($hu0 w)
    rw [hua] at this
    simp only [LinearMap.zero_apply, sub_eq_zero] at this
    rw [this, map_smul]
    rfl

end GlobalTheory.CompanionTheory.Ar.HopfCount

namespace GlobalTheory.CompanionTheory.Ar.HopfCount
open Coalgebra

section
variable {k : Type} [Field k] {A : Type} [CommRing A] [HopfAlgebra k A]

/- English proof (translation)
Establish `h` using `HopfAlgebra.mul_antipode_rTensor_comul_apply (R := k) f`. Establish `h0 : counit (R` using `k) f = 0 := GlobalTheory.IsPrimitiveElem.counit_eq_zero (R := k) hf`. Rewrite `h` using `[hf]`. Simplify using `[h0] at h`. Conclude with `eq_neg_of_add_eq_zero_left h`.
-/
theorem antipode_prim {f : A} (hf : comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) :
    HopfAlgebra.antipode k f = -f := by
  have h := HopfAlgebra.mul_antipode_rTensor_comul_apply (R := k) f
  have h0 : counit (R := k) f = 0 := GlobalTheory.IsPrimitiveElem.counit_eq_zero (R := k) hf
  rw [hf] at h
  simp [h0] at h
  exact eq_neg_of_add_eq_zero_left h

/- English proof (translation)
Establish `h0 : counit (R` using `k) f = 0 := GlobalTheory.IsPrimitiveElem.counit_eq_zero (R := k) hf'`. Use `{ counit_eq_zero := ?_, map_mkQ_comul_eq_zero := ?_, antipode_mem := ?_ }` and prove the remaining obligations. Introduce `x hx`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 hx`. Use `Bialgebra.counit_mul (R := k) a f` as an intermediate fact.

Simplify using `[h0]`. Introduce `x hx`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 hx`. Establish `hz : Ideal.Quotient.mkₐ k (Ideal.span {f}) f = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self f)`. Establish `: (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (Ideal.span {f})) (Ideal.Quotient.mkₐ k (Ideal.span {f}))) (comul (R` using `k) (a * f)) = 0 := by`.

Rewrite using `[Bialgebra.comul_mul, map_mul, hf', map_add]`. Simplify using `[hz]`. Conclude with `this`. Introduce `x hx`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 hx`.

Establish `: HopfAlgebra.antipode k (a * f) = HopfAlgebra.antipode k a * (- f)`. Rewrite using `[← antipode_prim (k := k) hf']`. Conclude with `map_mul (HopfAlgebra.antipodeAlgHom k A) a f`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ (neg_mem (Ideal.mem_span_singleton_self f))`.
-/
theorem isHopfIdeal_span {f : A}
    (hf' : comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) :
    (Ideal.span {f}).IsHopfIdeal k := by
  have h0 : counit (R := k) f = 0 := GlobalTheory.IsPrimitiveElem.counit_eq_zero (R := k) hf'
  refine { counit_eq_zero := ?_, map_mkQ_comul_eq_zero := ?_, antipode_mem := ?_ }
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have := Bialgebra.counit_mul (R := k) a f
    simp [h0]
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have hz : Ideal.Quotient.mkₐ k (Ideal.span {f}) f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self f)
    have : (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (Ideal.span {f}))
        (Ideal.Quotient.mkₐ k (Ideal.span {f}))) (comul (R := k) (a * f)) = 0 := by
      rw [Bialgebra.comul_mul, map_mul, hf', map_add]
      simp [hz]
    exact this
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have : HopfAlgebra.antipode k (a * f) = HopfAlgebra.antipode k a * (- f) := by
      rw [← antipode_prim (k := k) hf']
      exact map_mul (HopfAlgebra.antipodeAlgHom k A) a f
    rw [this]
    exact Ideal.mul_mem_left _ _ (neg_mem (Ideal.mem_span_singleton_self f))

/- English proof (translation)
Use `⟨LinearMap.ext fun x => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Establish `h` using `congr($(Coalgebra.IsCocomm.comm_comp_comul (R := k) (A := A)) a)`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h ⊢`. Rewrite using `[Bialgebra.Quotient.comul_mk]`.

Use `conv_rhs => rw [← h]`. Generalize the expression as in `comul (R := k) a = t`. Proceed by induction on `t with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.

Consider the case `tmul a b => simp`.
-/
theorem isCocomm_quot (I : Ideal A) [I.IsHopfIdeal k] [Coalgebra.IsCocomm k A] :
    Coalgebra.IsCocomm k (A ⧸ I) := by
  refine ⟨LinearMap.ext fun x => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h := congr($(Coalgebra.IsCocomm.comm_comp_comul (R := k) (A := A)) a)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h ⊢
  rw [Bialgebra.Quotient.comul_mk]
  conv_rhs => rw [← h]
  generalize comul (R := k) a = t
  induction t with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => simp
end

/- English proof (translation)
Establish `hp2 : 2 ≤ p` using `hp.out.two_le`. Set `Q : Submodule k A` to `GlobalTheory.primitiveElems k A ⊓ ⨅ v ∈ W, LinearMap.ker v`. Establish `memQ : ∀ g, g ∈ Q ↔ (comul (R` using `k) g = g ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] g) ∧ ∀ v ∈ W, v g = 0 := by`. Introduce `g`. Simplify using `[Q, Submodule.mem_iInf, GlobalTheory.mem_primitiveElems, GlobalTheory.IsPrimitiveElem]`.

Establish `hPQ : P ≤ Q` using `fun f hf => (memQ f).2 ⟨hP f hf, fun v hv => hPW v hv f hf⟩`. Establish `hQ0 : Q ≠ ⊥` using `fun h => hP0 (le_bot_iff.1 (h ▸ hPQ))`. Establish `hNT : Nontrivial A`. Take `⟨x, -, hx⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hP0`. Conclude with `⟨x, 0, hx⟩`.

Establish `hfrob : ∀ f ∈ Q, f ^ p ∈ Q`. Introduce `f hf`. Take `⟨h1, h2⟩` from `(memQ f).1 hf`. Establish `hcf : counit (R` using `k) f = 0 := GlobalTheory.IsPrimitiveElem.counit_eq_zero (R := k) h1`. Use `(memQ _).2 ⟨?_, fun v hv => ?_⟩` and prove the remaining obligations.

Establish `: CharP (A ⊗[k] A) p` using `charP_of_injective_algebraMap (algebraMap k (A ⊗[k] A)).injective p`. Establish `: comul (R` using `k) (f ^ p) = (comul (R := k) f) ^ p := map_pow (Bialgebra.comulAlgHom k A) f p`. Rewrite using `[this, h1, add_pow_char, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow, one_pow]`. Take `⟨q, rfl⟩ : ∃ q, p = q + 1` from `⟨p - 1, by omega⟩`. Rewrite using `[pow_succ, hW v hv, h2 v hv, hcf]`.

Simplify using the standard rewrite rules. Take `⟨f, hfQ, hf0, hfc⟩` from `GlobalTheory.T.frobenius_stable_subspace_element k p A Q hQ0 hfrob`. Take `⟨hfp, hfW⟩` from `(memQ f).1 hfQ`. Take `⟨hdim, hker⟩` from `key k p A f hfp hf0 hfc`. Establish `: (Ideal.span {f}).IsHopfIdeal k` using `isHopfIdeal_span hfp`.

Establish `: Coalgebra.IsCocomm k (A ⧸ Ideal.span {f})` using `isCocomm_quot _`. Establish `hcf : counit (R` using `k) f = 0 := GlobalTheory.IsPrimitiveElem.counit_eq_zero (R := k) hfp`. Set `π` to `Ideal.Quotient.mkₐ k (Ideal.span {f})`. Set `dm : ((A ⧸ Ideal.span {f}) →ₗ[k] k) →ₗ[k] (A →ₗ[k] k)` to `π.toLinearMap.dualMap`. Establish `hπ : Function.Surjective π` using `Ideal.Quotient.mkₐ_surjective k _`.

Establish `hdm : Function.Injective dm` using `LinearMap.dualMap_injective_of_surjective hπ`. Set `PB : Submodule k (A ⧸ Ideal.span {f})` to `Q.map π.toLinearMap`. Set `WB : Submodule k ((A ⧸ Ideal.span {f}) →ₗ[k] k)` to `W.comap dm`. Establish `hWmap : WB.map dm = W`. Use `le_antisymm (Submodule.map_comap_le _ _) fun v hv => ?_` and prove the remaining obligations.

Establish `hvI : ∀ x ∈ (Ideal.span {f}).restrictScalars k, v x = 0`. Introduce `x hx`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 hx`. Rewrite using `[hW v hv, hfW v hv, hcf]`. Simplify using the standard rewrite rules.

Set `u : (A ⧸ Ideal.span {f}) →ₗ[k] k` to `((Ideal.span {f}).restrictScalars k).liftQ v (fun x hx => hvI x hx)`. Establish `hu : dm u = v` using `LinearMap.ext fun a => rfl`. Conclude with `⟨u, by show dm u ∈ W; rwa [hu], hu⟩`. Establish `hfW' : Module.finrank k WB = Module.finrank k W`. Rewrite using `[← hWmap]`.

Conclude with `LinearEquiv.finrank_eq (Submodule.equivMapOfInjective dm hdm WB)`. Set `q : Q →ₗ[k] (A ⧸ Ideal.span {f})` to `π.toLinearMap.domRestrict Q`. Establish `hker' : LinearMap.ker q = Submodule.span k {(⟨f, hfQ⟩ : Q)}`. Use extensionality with `⟨x, hx⟩`. Rewrite using `[LinearMap.mem_ker, Submodule.mem_span_singleton]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hxI : x ∈ Ideal.span {f}` using `Ideal.Quotient.eq_zero_iff_mem.1 h`. Take `⟨a, rfl⟩` from `hker x hxI ((memQ x).1 hx).1`. Conclude with `⟨a, rfl⟩`.

Introduce and unpack `⟨a, ha⟩`. Establish `: x = a • f` using `(congrArg Subtype.val ha).symm`. Substitute `this` using the available equality. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Submodule.smul_of_tower_mem _ a (Ideal.mem_span_singleton_self f))`. Establish `hfQ' : Module.finrank k PB + 1 = Module.finrank k Q`.

Establish `h` using `LinearMap.finrank_range_add_finrank_ker q`. Rewrite `h` using `[hker', finrank_span_singleton (by simpa [Subtype.ext_iff] using hf0), LinearMap.range_domRestrict]`. Conclude with `h`. Establish `hpos : 0 < Module.finrank k A` using `Module.finrank_pos`. Establish `hlt : Module.finrank k (A ⧸ Ideal.span {f}) < Module.finrank k A`.

Rewrite `hpos`, the goal using `[hdim]`. Establish `: 0 < Module.finrank k (A ⧸ Ideal.span {f})` using `Nat.pos_of_mul_pos_left hpos`. Use the polynomial consequences of the given equalities and inequalities. Establish `key2` using `IH (A ⧸ Ideal.span {f}) hlt PB WB ?_ ?_ ?_`. Establish `hle : Module.finrank k P ≤ Module.finrank k Q` using `Submodule.finrank_mono hPQ`.

Rewrite `key2` using `[hfW']`. Establish `h3 : p ^ (Module.finrank k Q + Module.finrank k W) ∣ Module.finrank k A`. Rewrite using `[hdim, ← hfQ', show Module.finrank k PB + 1 + Module.finrank k W = (Module.finrank k PB + Module.finrank k W) + 1 by ring, pow_succ, mul_comm]`. Conclude with `Nat.mul_dvd_mul_left p key2`. Conclude with `(pow_dvd_pow p (by omega)).trans h3`.

Introduce and unpack `_ ⟨g, hg, rfl⟩`. Establish `h` using `((memQ g).1 hg).1`. Use `show comul (R := k) (Ideal.Quotient.mk (Ideal.span {f}) g) = _`. Rewrite using `[Bialgebra.Quotient.comul_mk, h]`. Simplify using `[π]`.

Introduce `u hu x y`. Take `⟨a, rfl⟩` from `hπ x`. Take `⟨b, rfl⟩` from `hπ y`. Conclude with `hW (dm u) hu a b`. Introduce and unpack `u hu _ ⟨g, hg, rfl⟩`.

Conclude with `((memQ g).1 hg).2 (dm u) hu`.
-/
theorem stepP (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]
    (IH : ∀ (B : Type) [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B],
      Module.finrank k B < Module.finrank k A →
      ∀ (P : Submodule k B) (W : Submodule k (B →ₗ[k] k)),
      (∀ f ∈ P, Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : B) + (1 : B) ⊗ₜ[k] f) →
      (∀ v ∈ W, ∀ f g : B, v (f * g) = v f * Coalgebra.counit (R := k) g + Coalgebra.counit (R := k) f * v g) →
      (∀ v ∈ W, ∀ f ∈ P, v f = 0) →
      p ^ (Module.finrank k P + Module.finrank k W) ∣ Module.finrank k B)
    (P : Submodule k A) (W : Submodule k (A →ₗ[k] k)) (hP0 : P ≠ ⊥)
    (hP : ∀ f ∈ P, Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f)
    (hW : ∀ v ∈ W, ∀ f g : A, v (f * g) = v f * Coalgebra.counit (R := k) g + Coalgebra.counit (R := k) f * v g)
    (hPW : ∀ v ∈ W, ∀ f ∈ P, v f = 0) :
    p ^ (Module.finrank k P + Module.finrank k W) ∣ Module.finrank k A := by
  classical
  have hp2 : 2 ≤ p := hp.out.two_le

  let Q : Submodule k A := GlobalTheory.primitiveElems k A ⊓ ⨅ v ∈ W, LinearMap.ker v
  have memQ : ∀ g, g ∈ Q ↔ (comul (R := k) g = g ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] g) ∧ ∀ v ∈ W, v g = 0 := by
    intro g
    simp [Q, Submodule.mem_iInf, GlobalTheory.mem_primitiveElems, GlobalTheory.IsPrimitiveElem]
  have hPQ : P ≤ Q := fun f hf => (memQ f).2 ⟨hP f hf, fun v hv => hPW v hv f hf⟩
  have hQ0 : Q ≠ ⊥ := fun h => hP0 (le_bot_iff.1 (h ▸ hPQ))
  have hNT : Nontrivial A := by
    obtain ⟨x, -, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    exact ⟨x, 0, hx⟩
  have hfrob : ∀ f ∈ Q, f ^ p ∈ Q := by
    intro f hf
    obtain ⟨h1, h2⟩ := (memQ f).1 hf
    have hcf : counit (R := k) f = 0 := GlobalTheory.IsPrimitiveElem.counit_eq_zero (R := k) h1
    refine (memQ _).2 ⟨?_, fun v hv => ?_⟩
    · have : CharP (A ⊗[k] A) p :=
        charP_of_injective_algebraMap (algebraMap k (A ⊗[k] A)).injective p
      have : comul (R := k) (f ^ p) = (comul (R := k) f) ^ p :=
        map_pow (Bialgebra.comulAlgHom k A) f p
      rw [this, h1, add_pow_char, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow,
        one_pow]
    · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      rw [pow_succ, hW v hv, h2 v hv, hcf]
      simp
  obtain ⟨f, hfQ, hf0, hfc⟩ := GlobalTheory.T.frobenius_stable_subspace_element k p A Q hQ0 hfrob
  obtain ⟨hfp, hfW⟩ := (memQ f).1 hfQ
  obtain ⟨hdim, hker⟩ := key k p A f hfp hf0 hfc
  have : (Ideal.span {f}).IsHopfIdeal k := isHopfIdeal_span hfp
  have : Coalgebra.IsCocomm k (A ⧸ Ideal.span {f}) := isCocomm_quot _
  have hcf : counit (R := k) f = 0 := GlobalTheory.IsPrimitiveElem.counit_eq_zero (R := k) hfp
  let π := Ideal.Quotient.mkₐ k (Ideal.span {f})
  let dm : ((A ⧸ Ideal.span {f}) →ₗ[k] k) →ₗ[k] (A →ₗ[k] k) := π.toLinearMap.dualMap
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective k _
  have hdm : Function.Injective dm := LinearMap.dualMap_injective_of_surjective hπ
  let PB : Submodule k (A ⧸ Ideal.span {f}) := Q.map π.toLinearMap
  let WB : Submodule k ((A ⧸ Ideal.span {f}) →ₗ[k] k) := W.comap dm
  have hWmap : WB.map dm = W := by
    refine le_antisymm (Submodule.map_comap_le _ _) fun v hv => ?_
    have hvI : ∀ x ∈ (Ideal.span {f}).restrictScalars k, v x = 0 := by
      intro x hx
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      rw [hW v hv, hfW v hv, hcf]; simp
    let u : (A ⧸ Ideal.span {f}) →ₗ[k] k := ((Ideal.span {f}).restrictScalars k).liftQ v
      (fun x hx => hvI x hx)
    have hu : dm u = v := LinearMap.ext fun a => rfl
    exact ⟨u, by show dm u ∈ W; rwa [hu], hu⟩
  have hfW' : Module.finrank k WB = Module.finrank k W := by
    rw [← hWmap]; exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective dm hdm WB)
  let q : Q →ₗ[k] (A ⧸ Ideal.span {f}) := π.toLinearMap.domRestrict Q
  have hker' : LinearMap.ker q = Submodule.span k {(⟨f, hfQ⟩ : Q)} := by
    ext ⟨x, hx⟩
    rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
    constructor
    · intro h
      have hxI : x ∈ Ideal.span {f} := Ideal.Quotient.eq_zero_iff_mem.1 h
      obtain ⟨a, rfl⟩ := hker x hxI ((memQ x).1 hx).1
      exact ⟨a, rfl⟩
    · rintro ⟨a, ha⟩
      have : x = a • f := (congrArg Subtype.val ha).symm
      subst this
      exact Ideal.Quotient.eq_zero_iff_mem.2
        (Submodule.smul_of_tower_mem _ a (Ideal.mem_span_singleton_self f))
  have hfQ' : Module.finrank k PB + 1 = Module.finrank k Q := by
    have h := LinearMap.finrank_range_add_finrank_ker q
    rw [hker', finrank_span_singleton (by simpa [Subtype.ext_iff] using hf0),
      LinearMap.range_domRestrict] at h
    exact h
  have hpos : 0 < Module.finrank k A := Module.finrank_pos
  have hlt : Module.finrank k (A ⧸ Ideal.span {f}) < Module.finrank k A := by
    rw [hdim] at hpos ⊢
    have : 0 < Module.finrank k (A ⧸ Ideal.span {f}) := Nat.pos_of_mul_pos_left hpos
    nlinarith
  have key2 := IH (A ⧸ Ideal.span {f}) hlt PB WB ?_ ?_ ?_
  · have hle : Module.finrank k P ≤ Module.finrank k Q := Submodule.finrank_mono hPQ
    rw [hfW'] at key2
    have h3 : p ^ (Module.finrank k Q + Module.finrank k W) ∣ Module.finrank k A := by
      rw [hdim, ← hfQ', show Module.finrank k PB + 1 + Module.finrank k W =
        (Module.finrank k PB + Module.finrank k W) + 1 by ring, pow_succ, mul_comm]
      exact Nat.mul_dvd_mul_left p key2
    exact (pow_dvd_pow p (by omega)).trans h3
  · rintro _ ⟨g, hg, rfl⟩
    have h := ((memQ g).1 hg).1
    show comul (R := k) (Ideal.Quotient.mk (Ideal.span {f}) g) = _
    rw [Bialgebra.Quotient.comul_mk, h]
    simp [π]
  · intro u hu x y
    obtain ⟨a, rfl⟩ := hπ x
    obtain ⟨b, rfl⟩ := hπ y
    exact hW (dm u) hu a b
  · rintro u hu _ ⟨g, hg, rfl⟩
    exact ((memQ g).1 hg).2 (dm u) hu

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `A _ _ _ _ hn P W hP hW hPW`. Establish `IH : ∀ (B : Type) [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B], Module.finrank k B < Module.finrank k A → ∀ (P : Submodule k B) (W : Submodule k (B →ₗ[k] k)), (∀ f ∈ P, Coalgebra.comul (R` using `k) f = f ⊗ₜ[k] (1 : B) + (1 : B) ⊗ₜ[k] f) → (∀ v ∈ W, ∀ f g : B, v (f * g) = v f * Coalgebra.counit (R := k) g + Coalgebra.counit (R := k) f * v g) → (∀ v ∈ W, ∀ f ∈ P, v f = 0) → p ^ (Module.finrank k P + Module.finrank k W) ∣ Module.finrank k B := by`. Introduce `B _ _ _ _ hB`.

Conclude with `ih _ (hn ▸ hB) B rfl`. Distinguish the cases in `hP0 : P = ⊥`. Distinguish the cases in `hW0 : W = ⊥`. Simplify using `[hP0, hW0]`. Set `e : (A →ₗ[k] k) ≃ₗ[k] GlobalTheory.CartierDual k A` to `(GlobalTheory.CartierDual.toDual k A).symm`.

Establish `hd : Module.finrank k (GlobalTheory.CartierDual k A) = Module.finrank k A`. Rewrite using `[LinearEquiv.finrank_eq (GlobalTheory.CartierDual.toDual k A)]`. Conclude with `Subspace.dual_finrank_eq`. Set `P' : Submodule k (GlobalTheory.CartierDual k A)` to `W.map e.toLinearMap`. Establish `hfin : Module.finrank k P' = Module.finrank k W` using `(LinearEquiv.finrank_eq (Submodule.equivMapOfInjective e.toLinearMap e.injective W)).symm`.

Establish `hP'0 : P' ≠ ⊥`. Introduce `h`. Conclude with `hW0 (Submodule.map_injective_of_injective (f := e.toLinearMap) e.injective (h.trans (Submodule.map_bot _).symm))`. Use `stepP k p (GlobalTheory.CartierDual k A) (fun B _ _ _ _ hB => IH B (hd ▸ hB)) P' ⊥ hP'0 ?_ (by simp) (by simp)` as an intermediate fact. Rewrite using `[hP0]`.

Simplify `this` using `[hfin, hd, add_comm]`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Rewrite using `[GlobalTheory.CartierDual.comul_eq_iff]`. Introduce `a b`. Use `hW v hv a b` as an intermediate fact.

Establish `he : ∀ a, (e v).ofConv a = v a` using `fun _ => rfl`. Simplify `this.symm` using `[GlobalTheory.CartierDual.one_apply, he]`. Conclude with `stepP k p A IH P W hP0 hP hW hPW`.
-/
theorem norm_index_count_bound (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] (n : ℕ) :
    ∀ (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A],
      Module.finrank k A = n →
      ∀ (P : Submodule k A) (W : Submodule k (A →ₗ[k] k)),
      (∀ f ∈ P, Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) →
      (∀ v ∈ W, ∀ f g : A, v (f * g) = v f * Coalgebra.counit (R := k) g + Coalgebra.counit (R := k) f * v g) →
      (∀ v ∈ W, ∀ f ∈ P, v f = 0) →
      p ^ (Module.finrank k P + Module.finrank k W) ∣ Module.finrank k A := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ _ _ hn P W hP hW hPW
  have IH : ∀ (B : Type) [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B],
      Module.finrank k B < Module.finrank k A →
      ∀ (P : Submodule k B) (W : Submodule k (B →ₗ[k] k)),
      (∀ f ∈ P, Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : B) + (1 : B) ⊗ₜ[k] f) →
      (∀ v ∈ W, ∀ f g : B, v (f * g) = v f * Coalgebra.counit (R := k) g + Coalgebra.counit (R := k) f * v g) →
      (∀ v ∈ W, ∀ f ∈ P, v f = 0) →
      p ^ (Module.finrank k P + Module.finrank k W) ∣ Module.finrank k B := by
    intro B _ _ _ _ hB
    exact ih _ (hn ▸ hB) B rfl
  by_cases hP0 : P = ⊥
  · by_cases hW0 : W = ⊥
    · simp [hP0, hW0]
    ·
      let e : (A →ₗ[k] k) ≃ₗ[k] GlobalTheory.CartierDual k A := (GlobalTheory.CartierDual.toDual k A).symm
      have hd : Module.finrank k (GlobalTheory.CartierDual k A) = Module.finrank k A := by
        rw [LinearEquiv.finrank_eq (GlobalTheory.CartierDual.toDual k A)]
        exact Subspace.dual_finrank_eq
      let P' : Submodule k (GlobalTheory.CartierDual k A) := W.map e.toLinearMap
      have hfin : Module.finrank k P' = Module.finrank k W :=
        (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective e.toLinearMap e.injective W)).symm
      have hP'0 : P' ≠ ⊥ := by
        intro h
        exact hW0 (Submodule.map_injective_of_injective (f := e.toLinearMap) e.injective
          (h.trans (Submodule.map_bot _).symm))
      have := stepP k p (GlobalTheory.CartierDual k A) (fun B _ _ _ _ hB => IH B (hd ▸ hB)) P' ⊥ hP'0 ?_
        (by simp) (by simp)
      · rw [hP0]
        simpa [hfin, hd, add_comm] using this
      · rintro _ ⟨v, hv, rfl⟩
        rw [GlobalTheory.CartierDual.comul_eq_iff]
        intro a b
        have := hW v hv a b
        have he : ∀ a, (e v).ofConv a = v a := fun _ => rfl
        simpa [GlobalTheory.CartierDual.one_apply, he] using this.symm
  · exact stepP k p A IH P W hP0 hP hW hPW

/- English proof (translation)
Introduce `k _ _ p _ _ A _ _ _ _ P W hP hW hPW` and use `norm_index_count_bound k p _ A rfl P W hP hW hPW`.
-/
theorem primitive_tangent_dvd_finrank :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]
    (P : Submodule k A) (W : Submodule k (A →ₗ[k] k)),
    (∀ f ∈ P, Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) →
    (∀ v ∈ W, ∀ f g : A, v (f * g) = v f * Coalgebra.counit (R := k) g + Coalgebra.counit (R := k) f * v g) →
    (∀ v ∈ W, ∀ f ∈ P, v f = 0) →
    p ^ (Module.finrank k P + Module.finrank k W) ∣ Module.finrank k A :=
  fun k _ _ p _ _ A _ _ _ _ P W hP hW hPW => norm_index_count_bound k p _ A rfl P W hP hW hPW

end GlobalTheory.CompanionTheory.Ar.HopfCount
