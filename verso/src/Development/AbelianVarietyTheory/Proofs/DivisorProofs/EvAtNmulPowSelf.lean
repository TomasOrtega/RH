import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupFormalChartEvNatMultipleEqConvPowerStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EvTor

/- English proof (translation)
Take `⟨s, hs⟩` from `Module.Projective.out (R := O) (P := A)`. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Establish `hdiv : ∀ m : ℕ, (p : A) ^ m ∣ a` using `fun m => by`. Use `CEval.dvd_of_smodEq p m (ha m)` as an intermediate fact. Simplify using `using this`.

Establish `hcoord : ∀ x, s a x = 0` using `fun x => by`. Use `CEval.eq_of_forall_dvd p fun m => ?_` and prove the remaining obligations. Take `⟨b, hb⟩` from `hdiv m`. Establish `: a = ((p : O) ^ m) • b`. Rewrite using `[hb, Algebra.smul_def, map_pow, map_natCast]`.

Rewrite using `[this, map_smul, Finsupp.smul_apply, smul_eq_mul, sub_zero]`. Conclude with `dvd_mul_right _ _`. Establish `h0 : s a = 0` using `Finsupp.ext hcoord`. Rewrite using `[← hs a, h0, map_zero]`.
-/
theorem isHausdorff_of_projective (p : ℕ) {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    [Module.Projective O A] [IsHausdorff (Ideal.span {(p : O)}) O] :
    IsHausdorff (Ideal.span {(p : A)}) A := by
  obtain ⟨s, hs⟩ := Module.Projective.out (R := O) (P := A)
  refine ⟨fun a ha => ?_⟩
  have hdiv : ∀ m : ℕ, (p : A) ^ m ∣ a := fun m => by
    have := CEval.dvd_of_smodEq p m (ha m)
    simpa using this
  have hcoord : ∀ x, s a x = 0 := fun x => by
    refine CEval.eq_of_forall_dvd p fun m => ?_
    obtain ⟨b, hb⟩ := hdiv m
    have : a = ((p : O) ^ m) • b := by
      rw [hb, Algebra.smul_def, map_pow, map_natCast]
    rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul, sub_zero]
    exact dvd_mul_right _ _
  have h0 : s a = 0 := Finsupp.ext hcoord
  rw [← hs a, h0, map_zero]

/- English proof (translation)
Establish `hs : HasSubst u` using `hasSubst_of_constantCoeff_zero hu`. Rewrite using `[← coe_substAlgHom hs]`. Conclude with `CEval.ext_of_cont p ((E.comp (substAlgHom hs)).toRingHom) ψ (fun c => by show E (substAlgHom hs (C c)) = ψ (C c)`. Rewrite using `[hC, c_eq_algebraMap, AlgHom.commutes, AlgHom.commutes])`. Use the proof step `(fun j => by show E (substAlgHom hs (X j)) = ψ (X j)`.

Rewrite using `[substAlgHom_X, hX])`. Use the proof step `(fun m => by`. Take `⟨N, hN⟩` from `hE m`. Use `⟨N, fun f hf => ?_⟩` and prove the remaining obligations. Use `show (p : A) ^ m ∣ E (substAlgHom hs f)`.

Rewrite using `[coe_substAlgHom]`. Use `hN _ fun α hα => coeff_of_lt_order ?_` and prove the remaining obligations. Establish `h1 : (1 : ℕ∞) ≤ ⨅ j, (u j).order` using `le_iInf fun j => one_le_order_iff_constCoeff_eq_zero.2 (hu j)`. Establish `h2 : (N : ℕ∞) ≤ f.order` using `nat_le_order hf`. Combine the equalities or inequalities in the displayed calculation.

Use `hψ f`.
-/
theorem eval_subst {σ τ R A : Type} [Fintype σ] [Fintype τ] [CommRing R] [CommRing A] [Algebra R A]
    (p : ℕ) [IsHausdorff (Ideal.span {(p : A)}) A] (E : MvPowerSeries σ R →ₐ[R] A)
    (hE : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ E f)
    (u : τ → MvPowerSeries σ R) (hu : ∀ j, constantCoeff (u j) = 0) (ψ : MvPowerSeries τ R →+* A)
    (hC : ∀ c, ψ (C c) = algebraMap R A c) (hX : ∀ j, ψ (X j) = E (u j))
    (hψ : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : τ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ ψ f)
    (f : MvPowerSeries τ R) : E (subst u f) = ψ f := by
  have hs : HasSubst u := hasSubst_of_constantCoeff_zero hu
  rw [← coe_substAlgHom hs]
  exact CEval.ext_of_cont p ((E.comp (substAlgHom hs)).toRingHom) ψ
    (fun c => by
      show E (substAlgHom hs (C c)) = ψ (C c)
      rw [hC, c_eq_algebraMap, AlgHom.commutes, AlgHom.commutes])
    (fun j => by
      show E (substAlgHom hs (X j)) = ψ (X j)
      rw [substAlgHom_X, hX])
    (fun m => by
      obtain ⟨N, hN⟩ := hE m
      refine ⟨N, fun f hf => ?_⟩
      show (p : A) ^ m ∣ E (substAlgHom hs f)
      rw [coe_substAlgHom]
      refine hN _ fun α hα => coeff_of_lt_order ?_
      have h1 : (1 : ℕ∞) ≤ ⨅ j, (u j).order :=
        le_iInf fun j => one_le_order_iff_constCoeff_eq_zero.2 (hu j)
      have h2 : (N : ℕ∞) ≤ f.order := nat_le_order hf
      calc (α.degree : ℕ∞) < N := by exact_mod_cast hα
        _ = 1 * N := (one_mul _).symm
        _ ≤ (⨅ j, (u j).order) * f.order := mul_le_mul' h1 h2
        _ ≤ (subst u f).order := le_order_subst hs f)
    hψ f

end GlobalTheory.EvTor

namespace GlobalTheory.EvTor

/- English proof (translation)
Proceed by induction on `k generalizing i with`. Consider the case `zero => simp [nmul]`. Consider the case `succ k ih`. Establish `e : nmul μ (k + 1) = op μ (nmul μ k) (fun i => X i)`. Simplify using `only [nmul]`.

Rewrite using `[Function.iterate_succ_apply']`. Rewrite using `[e]`. Establish `h0 : ∀ s : Fin d ⊕ Fin d, constantCoeff (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R)) s) = 0`. Introduce and unpack `(s | s)`. Conclude with `ih s`.

Simplify using the standard rewrite rules. Conclude with `constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 (hμ i)`.
-/
theorem constantCoeff_nmul {R : Type} [CommRing R] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ)
    (i : Fin d) : constantCoeff (nmul μ k i) = 0 := by
  induction k generalizing i with
  | zero => simp [nmul]
  | succ k ih =>
    have e : nmul μ (k + 1) = op μ (nmul μ k) (fun i => X i) := by
      simp only [nmul]
      rw [Function.iterate_succ_apply']
    rw [e]
    have h0 : ∀ s : Fin d ⊕ Fin d,
        constantCoeff (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R)) s) = 0 := by
      rintro (s | s)
      · exact ih s
      · simp
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 (hμ i)

/- English proof (translation)
Establish `h0 : ∀ s, constantCoeff ((fun i => (X (e i) : MvPowerSeries τ R)) s) = 0` using `fun s => by simp`. Conclude with `constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 hf`.
-/
theorem constantCoeff_subst_var {R : Type} [CommRing R] {σ τ : Type} [Finite σ] (e : σ → τ)
    (f : MvPowerSeries σ R) (hf : constantCoeff f = 0) :
    constantCoeff (subst (fun i => (X (e i) : MvPowerSeries τ R)) f) = 0 := by
  have h0 : ∀ s, constantCoeff ((fun i => (X (e i) : MvPowerSeries τ R)) s) = 0 := fun s => by simp
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 hf

end GlobalTheory.EvTor

namespace GlobalTheory.EvTor

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ hv G d c n g`. Use `haveI : IsHausdorff (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) := isHausdorff_of_projective (O := O) (A := G.A n ⊗[O] G.A n) p`. Establish `hz : ∀ i, c.ev n (nmul c.μ (p ^ n) i) = 0` using `fun i => by`. Rewrite using `[GlobalTheory.T.pDivGroupFormalChart_ev_natMultiple_eq_convPower p C v O hv G d c n (p ^ n) i, G.mulBy_pow_self n (c.x n i), c.aug n i, map_zero]`. Establish `hcont : ∀ (φ : G.A n →ₐ[O] G.A n ⊗[O] G.A n) (m : ℕ), ∃ N : ℕ, ∀ f : MvPowerSeries (Fin d) O, (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) → ((p : G.A n ⊗[O] G.A n)) ^ m ∣ (φ.comp (c.ev n)).toRingHom f` using `fun φ m => by`.

Take `⟨N, hN⟩` from `(c.isEval n).2 m`. Use `⟨N, fun f hf => ?_⟩` and prove the remaining obligations. Use `map_dvd φ (hN f hf)` as an intermediate fact. Rewrite `this` using `[map_pow, map_natCast]`. Then use the resulting hypothesis. Establish `hL : ∀ f : MvPowerSeries (Fin d) O, c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1` using `fun f => eval_subst p (c.ev₂ n) (c.isEval₂ n).2 _ (fun i => by simp) ((Algebra.TensorProduct.includeLeft (S := O)).comp (c.ev n)).toRingHom (fun r => by show (Algebra.TensorProduct.includeLeft (S := O)).comp (c.ev n) (MvPowerSeries.C r) = _`.

Rewrite using `[c_eq_algebraMap, AlgHom.commutes])`. Use the proof step `(fun i => by show Algebra.TensorProduct.includeLeft (S := O) (c.ev n (X i)) = _`. Rewrite using `[(c.isEval n).1 i, (c.isEval₂ n).1 (Sum.inl i)]`. Use the proof step `rfl)`. Use the proof step `(hcont _) f`.

Establish `hR : ∀ f : MvPowerSeries (Fin d) O, c.ev₂ n (inR f) = (1 : G.A n) ⊗ₜ[O] c.ev n f` using `fun f => eval_subst p (c.ev₂ n) (c.isEval₂ n).2 _ (fun i => by simp) ((Algebra.TensorProduct.includeRight).comp (c.ev n)).toRingHom (fun r => by show (Algebra.TensorProduct.includeRight).comp (c.ev n) (MvPowerSeries.C r) = _`. Rewrite using `[c_eq_algebraMap, AlgHom.commutes])`. Use the proof step `(fun i => by show Algebra.TensorProduct.includeRight (c.ev n (X i)) = _`. Rewrite using `[(c.isEval n).1 i, (c.isEval₂ n).1 (Sum.inr i)]`. Use the proof step `rfl)`.

Use the proof step `(hcont _) f`. Establish `hμ` using `c.isLaw.const`. Establish `hu : ∀ j, constantCoeff (Sum.elim (fun i => inL (nmul c.μ (p ^ n) i)) (fun i => inR (nmul c.μ (p ^ n) i)) j) = 0`. Introduce and unpack `(j | j)`. Conclude with `constantCoeff_subst_var _ _ (constantCoeff_nmul hμ _ j)`.

Conclude with `constantCoeff_subst_var _ _ (constantCoeff_nmul hμ _ j)`. Use `eval_subst p (c.ev₂ n) (c.isEval₂ n).2 _ hu ((algebraMap O (G.A n ⊗[O] G.A n)).comp constantCoeff) (fun r => by simp) ?_ ?_ g` and prove the remaining obligations. Introduce and unpack `(j | j)`. Simplify using `only [RingHom.comp_apply, constantCoeff_X, map_zero, Sum.elim_inl]`. Rewrite using `[hL, hz, TensorProduct.zero_tmul]`.

Simplify using `only [RingHom.comp_apply, constantCoeff_X, map_zero, Sum.elim_inr]`. Rewrite using `[hR, hz, TensorProduct.tmul_zero]`. Introduce `m`. Use `⟨1, fun f hf => ?_⟩` and prove the remaining obligations. Establish `h0 : constantCoeff f = 0`.

Rewrite using `[← coeff_zero_eq_constantCoeff_apply]`. Conclude with `hf 0 (by simp)`. Simplify using `[h0]`.
-/
theorem ev₂_at_nmul_pow_self : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (n : ℕ) (g : MvPowerSeries (Fin d ⊕ Fin d) O), c.ev₂ n (at2 g (fun i => inL (nmul c.μ (p ^ n) i)) (fun i => inR (nmul c.μ (p ^ n) i))) = algebraMap O (G.A n ⊗[O] G.A n) (constantCoeff g) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c n g
  haveI : IsHausdorff (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
    isHausdorff_of_projective (O := O) (A := G.A n ⊗[O] G.A n) p
  have hz : ∀ i, c.ev n (nmul c.μ (p ^ n) i) = 0 := fun i => by
    rw [GlobalTheory.T.pDivGroupFormalChart_ev_natMultiple_eq_convPower p C v O hv G d c n (p ^ n) i, G.mulBy_pow_self n (c.x n i), c.aug n i,
      map_zero]
  have hcont : ∀ (φ : G.A n →ₐ[O] G.A n ⊗[O] G.A n) (m : ℕ), ∃ N : ℕ, ∀ f : MvPowerSeries (Fin d) O,
      (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) →
        ((p : G.A n ⊗[O] G.A n)) ^ m ∣ (φ.comp (c.ev n)).toRingHom f := fun φ m => by
    obtain ⟨N, hN⟩ := (c.isEval n).2 m
    refine ⟨N, fun f hf => ?_⟩
    have := map_dvd φ (hN f hf)
    rwa [map_pow, map_natCast] at this
  have hL : ∀ f : MvPowerSeries (Fin d) O, c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 := fun f =>
    eval_subst p (c.ev₂ n) (c.isEval₂ n).2 _ (fun i => by simp)
      ((Algebra.TensorProduct.includeLeft (S := O)).comp (c.ev n)).toRingHom
      (fun r => by
        show (Algebra.TensorProduct.includeLeft (S := O)).comp (c.ev n) (MvPowerSeries.C r) = _
        rw [c_eq_algebraMap, AlgHom.commutes])
      (fun i => by
        show Algebra.TensorProduct.includeLeft (S := O) (c.ev n (X i)) = _
        rw [(c.isEval n).1 i, (c.isEval₂ n).1 (Sum.inl i)]
        rfl)
      (hcont _) f
  have hR : ∀ f : MvPowerSeries (Fin d) O, c.ev₂ n (inR f) = (1 : G.A n) ⊗ₜ[O] c.ev n f := fun f =>
    eval_subst p (c.ev₂ n) (c.isEval₂ n).2 _ (fun i => by simp)
      ((Algebra.TensorProduct.includeRight).comp (c.ev n)).toRingHom
      (fun r => by
        show (Algebra.TensorProduct.includeRight).comp (c.ev n) (MvPowerSeries.C r) = _
        rw [c_eq_algebraMap, AlgHom.commutes])
      (fun i => by
        show Algebra.TensorProduct.includeRight (c.ev n (X i)) = _
        rw [(c.isEval n).1 i, (c.isEval₂ n).1 (Sum.inr i)]
        rfl)
      (hcont _) f
  have hμ := c.isLaw.const
  have hu : ∀ j, constantCoeff (Sum.elim (fun i => inL (nmul c.μ (p ^ n) i))
      (fun i => inR (nmul c.μ (p ^ n) i)) j) = 0 := by
    rintro (j | j)
    · exact constantCoeff_subst_var _ _ (constantCoeff_nmul hμ _ j)
    · exact constantCoeff_subst_var _ _ (constantCoeff_nmul hμ _ j)
  refine eval_subst p (c.ev₂ n) (c.isEval₂ n).2 _ hu
    ((algebraMap O (G.A n ⊗[O] G.A n)).comp constantCoeff) (fun r => by simp) ?_ ?_ g
  · rintro (j | j)
    · simp only [RingHom.comp_apply, constantCoeff_X, map_zero, Sum.elim_inl]
      rw [hL, hz, TensorProduct.zero_tmul]
    · simp only [RingHom.comp_apply, constantCoeff_X, map_zero, Sum.elim_inr]
      rw [hR, hz, TensorProduct.tmul_zero]
  · intro m
    refine ⟨1, fun f hf => ?_⟩
    have h0 : constantCoeff f = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      exact hf 0 (by simp)
    simp [h0]

end GlobalTheory.EvTor
