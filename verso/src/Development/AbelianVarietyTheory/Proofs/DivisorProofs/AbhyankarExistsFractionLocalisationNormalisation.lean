import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocHomAlgebraMap
open IsLocalRing

namespace GlobalTheory.AbhyankarLocal

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ ψ _ _ _ _ Q _ w`. Establish `hS : ∀ r : S, algebraMap D (Localization.AtPrime Q) (algebraMap S D r) = locHom Q (algebraMap _ _ (algebraMap S (integralClosure S L) r))`. Introduce `r`. Rewrite using `[locHom_algebraMap, IsScalarTower.algebraMap_apply D (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)]`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [toNorm_coe, Subalgebra.coe_algebraMap, Algebra.TensorProduct.algebraMap_apply]`. Rewrite using `[Algebra.algebraMap_eq_smul_one r, Algebra.algebraMap_eq_smul_one r]`. Simplify using `only [Algebra.algebraMap_self, RingHom.id_apply]`. Rewrite using `[TensorProduct.smul_tmul]`.

Establish `hD : ∀ d : D, algebraMap D (Localization.AtPrime Q) d ∈ Subring.closure (Set.range (GlobalTheory.AbhyankarLocal.locHom Q) ∪ {algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)))})`. Introduce `d`. Rewrite using `[← ψ.symm_apply_apply d]`. Generalize the expression as in `ψ d = a`. Establish `hd : a ∈ Algebra.adjoin S ({AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)} : Set _)`.

Rewrite using `[AdjoinRoot.adjoinRoot_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hd using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Rewrite `hx` using `[Set.mem_singleton_iff]`.

Substitute `hx` using the available equality. Conclude with `Subring.subset_closure (Or.inr rfl)`. Consider the case `algebraMap r`. Rewrite using `[AlgEquiv.commutes, hS]`. Conclude with `Subring.subset_closure (Or.inl ⟨_, rfl⟩)`.

Consider the case `add x y _ _ hx hy => rw [map_add, map_add]`. Conclude with `add_mem hx hy`. Consider the case `mul x y _ _ hx hy => rw [map_mul, map_mul]`. Conclude with `mul_mem hx hy`. Establish `hT : ∀ u : TensorProduct S D (integralClosure S L), ∃ b : integralClosure D (TensorProduct S D L), (b : TensorProduct S D L) = Algebra.TensorProduct.map (AlgHom.id S D) (integralClosure S L).val u ∧ algebraMap _ (Localization.AtPrime Q) b ∈ Subring.closure (Set.range (GlobalTheor …`.

Introduce `u`. Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp, by simp⟩`. Consider the case `tmul d o`. Use `⟨algebraMap D _ d * toNorm S L D o, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `[toNorm_coe, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]`. Rewrite using `[map_mul, ← IsScalarTower.algebraMap_apply, ← locHom_algebraMap]`. Conclude with `mul_mem (hD d) (Subring.subset_closure (Or.inl ⟨_, rfl⟩))`. Consider the case `add u v hu hv`. Take `⟨b1, h1, m1⟩` from `hu`.

Take `⟨b2, h2, m2⟩` from `hv`. Conclude with `⟨b1 + b2, by simp [h1, h2], by rw [map_add]; exact add_mem m1 m2⟩`. Establish `hI : ∀ y : TensorProduct S D L, ∃ σ : S, σ ≠ 0 ∧ ∃ u : TensorProduct S D (integralClosure S L), Algebra.TensorProduct.map (AlgHom.id S D) (integralClosure S L).val u = σ • y`. Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => exact ⟨1, one_ne_zero, 0, by simp⟩`. Consider the case `tmul d l`. Establish `hl : IsAlgebraic S l` using `(IsFractionRing.isAlgebraic_iff S K L).2 (Algebra.IsAlgebraic.isAlgebraic l)`. Take `⟨σ, hσ, hint⟩` from `hl.exists_integral_multiple`. Conclude with `⟨σ, hσ, d ⊗ₜ ⟨σ • l, hint⟩, by simp [TensorProduct.tmul_smul]⟩`.

Consider the case `add y1 y2 h1 h2`. Take `⟨σ1, n1, u1, e1⟩` from `h1`. Take `⟨σ2, n2, u2, e2⟩` from `h2`. Use `⟨σ1 * σ2, mul_ne_zero n1 n2, σ2 • u1 + σ1 • u2, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_smul, map_smul, e1, e2, smul_add, smul_smul, smul_smul, mul_comm σ1 σ2]`.

Take `⟨⟨b, s⟩, rfl⟩` from `IsLocalization.mk'_surjective Q.primeCompl w`. Take `⟨σ1, n1, u1, e1⟩` from `hI (b : TensorProduct S D L)`. Take `⟨σ2, n2, u2, e2⟩` from `hI ((s : integralClosure D (TensorProduct S D L)) : TensorProduct S D L)`. Take `⟨bb, hbb, mb⟩` from `hT (σ2 • u1)`. Take `⟨ss, hss, ms⟩` from `hT (σ1 • u2)`.

Use `set a : integralClosure D (TensorProduct S D L) := algebraMap D _ (algebraMap S D (σ1 * σ2)) with ha`. Establish `hcoe : ∀ y : integralClosure D (TensorProduct S D L), ((a * y : integralClosure D (TensorProduct S D L)) : TensorProduct S D L) = (σ1 * σ2) • (y : TensorProduct S D L)`. Introduce `y`. Rewrite using `[ha, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, ← IsScalarTower.algebraMap_apply, Algebra.smul_def]`. Establish `hbb' : bb = a * b`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hcoe, hbb, map_smul, e1, smul_smul, mul_comm σ2 σ1]`. Establish `hss' : ss = a * s`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hcoe, hss, map_smul, e2, smul_smul]`.

Establish `hL : algebraMap S L (σ1 * σ2) ≠ 0`. Introduce `h`. Rewrite `h` using `[IsScalarTower.algebraMap_apply S K L, map_eq_zero, IsFractionRing.to_map_eq_zero_iff]`. Conclude with `mul_ne_zero n1 n2 h`. Establish `hU : IsUnit (algebraMap S (TensorProduct S D L) (σ1 * σ2))`.

Rewrite using `[← (Algebra.TensorProduct.includeRight (R := S) (A := D) (B := L)).commutes]`. Conclude with `(IsUnit.mk0 _ hL).map _`. Establish `haN : a ∈ nonZeroDivisors (integralClosure D (TensorProduct S D L))`. Rewrite using `[mem_nonZeroDivisors_iff_right]`. Introduce `y hy`.

Use `congrArg Subtype.val hy` as an intermediate fact. Rewrite `this` using `[mul_comm, hcoe, Algebra.smul_def, ZeroMemClass.coe_zero]`. Conclude with `Subtype.ext (by simpa using (hU.mul_right_eq_zero).1 this)`. Use `⟨algebraMap _ _ bb, algebraMap _ _ ss, mb, ms, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hss', map_mul]`.

Establish `h1 : algebraMap _ (Localization.AtPrime Q) a ∈ nonZeroDivisors (Localization.AtPrime Q)` using `IsLocalization.map_nonZeroDivisors_le Q.primeCompl (Localization.AtPrime Q) (Submonoid.mem_map_of_mem (algebraMap _ (Localization.AtPrime Q)) haN)`. Conclude with `mul_mem h1 (IsLocalization.map_units (Localization.AtPrime Q) s).mem_nonZeroDivisors`. Rewrite using `[hss', hbb', map_mul, map_mul, mul_assoc, IsLocalization.mk'_spec']`.
-/
theorem exists_frac_closure : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D] (ψ : D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial S)), Irreducible π → 0 < e → ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal] (w : Localization.AtPrime Q), ∃ x z : Localization.AtPrime Q, x ∈ Subring.closure (Set.range (GlobalTheory.AbhyankarLocal.locHom Q) ∪ {algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)))}) ∧ z ∈ Subring.closure (Set.range (GlobalTheory.AbhyankarLocal.locHom Q) ∪ {algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)))}) ∧ z ∈ nonZeroDivisors (Localization.AtPrime Q) ∧ z * w = x := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ ψ _ _ _ _ Q _ w

  have hS : ∀ r : S, algebraMap D (Localization.AtPrime Q) (algebraMap S D r) =
      locHom Q (algebraMap _ _ (algebraMap S (integralClosure S L) r)) := by
    intro r
    rw [locHom_algebraMap, IsScalarTower.algebraMap_apply D (integralClosure D (TensorProduct S D L))
      (Localization.AtPrime Q)]
    congr 1
    apply Subtype.ext
    simp only [toNorm_coe, Subalgebra.coe_algebraMap, Algebra.TensorProduct.algebraMap_apply]
    rw [Algebra.algebraMap_eq_smul_one r, Algebra.algebraMap_eq_smul_one r]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [TensorProduct.smul_tmul]
  have hD : ∀ d : D, algebraMap D (Localization.AtPrime Q) d ∈ Subring.closure (Set.range (GlobalTheory.AbhyankarLocal.locHom Q) ∪ {algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)))}) := by
    intro d
    rw [← ψ.symm_apply_apply d]
    generalize ψ d = a
    have hd : a ∈ Algebra.adjoin S ({AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)} : Set _) := by
      rw [AdjoinRoot.adjoinRoot_eq_top]; trivial
    induction hd using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subring.subset_closure (Or.inr rfl)
    | algebraMap r =>
      rw [AlgEquiv.commutes, hS]
      exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
    | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul, map_mul]; exact mul_mem hx hy

  have hT : ∀ u : TensorProduct S D (integralClosure S L), ∃ b : integralClosure D (TensorProduct S D L),
      (b : TensorProduct S D L) = Algebra.TensorProduct.map (AlgHom.id S D) (integralClosure S L).val u ∧
      algebraMap _ (Localization.AtPrime Q) b ∈ Subring.closure (Set.range (GlobalTheory.AbhyankarLocal.locHom Q) ∪ {algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)))}) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | tmul d o =>
      refine ⟨algebraMap D _ d * toNorm S L D o, ?_, ?_⟩
      · simp [toNorm_coe, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
      · rw [map_mul, ← IsScalarTower.algebraMap_apply, ← locHom_algebraMap]
        exact mul_mem (hD d) (Subring.subset_closure (Or.inl ⟨_, rfl⟩))
    | add u v hu hv =>
      obtain ⟨b1, h1, m1⟩ := hu
      obtain ⟨b2, h2, m2⟩ := hv
      exact ⟨b1 + b2, by simp [h1, h2], by rw [map_add]; exact add_mem m1 m2⟩
  have hI : ∀ y : TensorProduct S D L, ∃ σ : S, σ ≠ 0 ∧ ∃ u : TensorProduct S D (integralClosure S L),
      Algebra.TensorProduct.map (AlgHom.id S D) (integralClosure S L).val u = σ • y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
    | tmul d l =>
      have hl : IsAlgebraic S l := (IsFractionRing.isAlgebraic_iff S K L).2 (Algebra.IsAlgebraic.isAlgebraic l)
      obtain ⟨σ, hσ, hint⟩ := hl.exists_integral_multiple
      exact ⟨σ, hσ, d ⊗ₜ ⟨σ • l, hint⟩, by simp [TensorProduct.tmul_smul]⟩
    | add y1 y2 h1 h2 =>
      obtain ⟨σ1, n1, u1, e1⟩ := h1
      obtain ⟨σ2, n2, u2, e2⟩ := h2
      refine ⟨σ1 * σ2, mul_ne_zero n1 n2, σ2 • u1 + σ1 • u2, ?_⟩
      rw [map_add, map_smul, map_smul, e1, e2, smul_add, smul_smul, smul_smul, mul_comm σ1 σ2]
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl w
  obtain ⟨σ1, n1, u1, e1⟩ := hI (b : TensorProduct S D L)
  obtain ⟨σ2, n2, u2, e2⟩ := hI ((s : integralClosure D (TensorProduct S D L)) : TensorProduct S D L)
  obtain ⟨bb, hbb, mb⟩ := hT (σ2 • u1)
  obtain ⟨ss, hss, ms⟩ := hT (σ1 • u2)
  set a : integralClosure D (TensorProduct S D L) := algebraMap D _ (algebraMap S D (σ1 * σ2)) with ha
  have hcoe : ∀ y : integralClosure D (TensorProduct S D L), ((a * y : integralClosure D (TensorProduct S D L)) : TensorProduct S D L) = (σ1 * σ2) • (y : TensorProduct S D L) := by
    intro y
    rw [ha, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, ← IsScalarTower.algebraMap_apply, Algebra.smul_def]
  have hbb' : bb = a * b := by
    apply Subtype.ext
    rw [hcoe, hbb, map_smul, e1, smul_smul, mul_comm σ2 σ1]
  have hss' : ss = a * s := by
    apply Subtype.ext
    rw [hcoe, hss, map_smul, e2, smul_smul]
  have hL : algebraMap S L (σ1 * σ2) ≠ 0 := by
    intro h
    rw [IsScalarTower.algebraMap_apply S K L, map_eq_zero, IsFractionRing.to_map_eq_zero_iff] at h
    exact mul_ne_zero n1 n2 h
  have hU : IsUnit (algebraMap S (TensorProduct S D L) (σ1 * σ2)) := by
    rw [← (Algebra.TensorProduct.includeRight (R := S) (A := D) (B := L)).commutes]
    exact (IsUnit.mk0 _ hL).map _
  have haN : a ∈ nonZeroDivisors (integralClosure D (TensorProduct S D L)) := by
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    have := congrArg Subtype.val hy
    rw [mul_comm, hcoe, Algebra.smul_def, ZeroMemClass.coe_zero] at this
    exact Subtype.ext (by simpa using (hU.mul_right_eq_zero).1 this)
  refine ⟨algebraMap _ _ bb, algebraMap _ _ ss, mb, ms, ?_, ?_⟩
  · rw [hss', map_mul]
    have h1 : algebraMap _ (Localization.AtPrime Q) a ∈ nonZeroDivisors (Localization.AtPrime Q) :=
      IsLocalization.map_nonZeroDivisors_le Q.primeCompl (Localization.AtPrime Q)
        (Submonoid.mem_map_of_mem (algebraMap _ (Localization.AtPrime Q)) haN)
    exact mul_mem h1 (IsLocalization.map_units (Localization.AtPrime Q) s).mem_nonZeroDivisors
  · rw [hss', hbb', map_mul, map_mul, mul_assoc, IsLocalization.mk'_spec']

end GlobalTheory.AbhyankarLocal
