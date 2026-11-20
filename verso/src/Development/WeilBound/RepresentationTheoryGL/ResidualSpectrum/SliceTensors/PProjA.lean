import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementA
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLIwasawaDecompositionStandardParabolic
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTwA

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs.ParabolicProjection

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem mulChi_absC_neg (n : ℕ) (z : ℂ) (φ : Sm E n) :
    mulChi n (Model.absC E (-z)) (mulChi n (Model.absC E z) φ) = φ := by
  refine Subtype.ext (funext fun g => ?_)
  rw [mulChi_apply, mulChi_apply, ExponentTwist.chiDet_absC_val, ExponentTwist.chiDet_absC_val, mul_assoc, ← Complex.exp_add]
  simp

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem mulChi_absC_neg' (n : ℕ) (z : ℂ) (φ : Sm E n) :
    mulChi n (Model.absC E z) (mulChi n (Model.absC E (-z)) φ) = φ := by
  have h := mulChi_absC_neg n (-z) φ
  rwa [neg_neg] at h

/- English proof (translation)
Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem isStable_tw {n : ℕ} {U : Submodule ℂ (Sm E n)} (hU : IsStable U) (z : ℂ) : IsStable (tw U z) := by
  rintro o _ ⟨φ, hφ, rfl⟩
  exact ⟨_, add_mem (U.smul_mem _ (hU o φ hφ)) (U.smul_mem _ hφ), (act_mulChi _ o φ).symm⟩

def twMap (n : ℕ) (z : ℂ) (f : Sm E n →ₗ[ℂ] Sm E n) : Sm E n →ₗ[ℂ] Sm E n :=
  (mulChi n (Model.absC E z)).toLinearMap ∘ₗ f ∘ₗ (mulChi n (Model.absC E (-z))).toLinearMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem twMap_apply (n : ℕ) (z : ℂ) (f : Sm E n →ₗ[ℂ] Sm E n) (φ : Sm E n) :
    twMap n z f φ = mulChi n (Model.absC E z) (f (mulChi n (Model.absC E (-z)) φ)) := rfl

/- English proof (translation)
Assume the hypotheses and unpack their components. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem twMap_equiv {n : ℕ} {z : ℂ} {U : Submodule ℂ (Sm E n)} (_hU : IsStable U) {f : Sm E n →ₗ[ℂ] Sm E n}
    (hf : ∀ o, ∀ ψ ∈ U, f (act o ψ) = act o (f ψ)) : ∀ o, ∀ ψ ∈ tw U z, twMap n z f (act o ψ) = act o (twMap n z f ψ) := by
  rintro o _ ⟨φ, hφ, rfl⟩
  change twMap n z f (act o (mulChi n (Model.absC E z) φ)) = act o (twMap n z f (mulChi n (Model.absC E z) φ))
  rw [twMap_apply, twMap_apply, mulChi_absC_neg, act_mulChi, mulChi_absC_neg, map_add, map_smul, map_smul, hf o φ hφ,
    act_mulChi]

/- English proof (translation)
Assume the hypotheses and unpack their components. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem twMap_mem {n : ℕ} {z : ℂ} {U W : Submodule ℂ (Sm E n)} {f : Sm E n →ₗ[ℂ] Sm E n} (hf : ∀ ψ ∈ U, f ψ ∈ W) :
    ∀ ψ ∈ tw U z, twMap n z f ψ ∈ tw W z := by
  rintro _ ⟨φ, hφ, rfl⟩
  change twMap n z f (mulChi n (Model.absC E z) φ) ∈ tw W z
  rw [twMap_apply, mulChi_absC_neg]
  exact ⟨_, hf φ hφ, rfl⟩

/- English proof (translation)
Assume the hypotheses and unpack their components. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem twMap_ne {n : ℕ} {z : ℂ} {U : Submodule ℂ (Sm E n)} {f : Sm E n →ₗ[ℂ] Sm E n} (hf : ∀ ψ ∈ U, f ψ = 0 → ψ = 0) :
    ∀ ψ ∈ tw U z, twMap n z f ψ = 0 → ψ = 0 := by
  rintro _ ⟨φ, hφ, rfl⟩ h
  change twMap n z f (mulChi n (Model.absC E z) φ) = 0 at h
  rw [twMap_apply, mulChi_absC_neg, LinearEquiv.map_eq_zero_iff] at h
  change mulChi n (Model.absC E z) φ = 0
  rw [hf φ hφ h, map_zero]

variable {r s : ℕ}

/- English proof (translation)
Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately.

Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts.

Simplify using the standard rewrite rules. Treat this case separately. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Simplify using the standard rewrite rules.
-/
theorem tensor_pair_finite_sum {V₁ : Submodule ℂ (Sm E r)} {V₂ : Submodule ℂ (Sm E s)} {F : GA E r × GA E s → ℂ}
    (hF : F ∈ tens2 V₁ V₂) : ∃ (n : ℕ) (ψ₁ : Fin n → Sm E r) (ψ₂ : Fin n → Sm E s), (∀ i, ψ₁ i ∈ V₁) ∧ (∀ i, ψ₂ i ∈ V₂) ∧
      ∀ m, F m = ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2 := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := hF
    exact ⟨1, fun _ => φ₁, fun _ => φ₂, fun _ => h₁, fun _ => h₂, fun m => by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun m => by simp⟩
  | add F G _ _ hF hG =>
    obtain ⟨n, a₁, a₂, ha₁, ha₂, ha⟩ := hF
    obtain ⟨n', b₁, b₂, hb₁, hb₂, hb⟩ := hG
    refine ⟨n + n', Fin.append a₁ b₁, Fin.append a₂ b₂, fun i => ?_, fun i => ?_, fun m => ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using ha₁ j
      · simpa using hb₁ j
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using ha₂ j
      · simpa using hb₂ j
    · simp [Fin.sum_univ_add, ha, hb]
  | smul c F _ hF =>
    obtain ⟨n, a₁, a₂, ha₁, ha₂, ha⟩ := hF
    exact ⟨n, fun i => c • a₁ i, a₂, fun i => Submodule.smul_mem _ c (ha₁ i), ha₂, fun m => by
      simp [ha, Finset.mul_sum, mul_assoc]⟩

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sum_mem_tens2 {V₁ : Submodule ℂ (Sm E r)} {V₂ : Submodule ℂ (Sm E s)} {n : ℕ} {ψ₁ : Fin n → Sm E r}
    {ψ₂ : Fin n → Sm E s} (h₁ : ∀ i, ψ₁ i ∈ V₁) (h₂ : ∀ i, ψ₂ i ∈ V₂) :
    (fun m : GA E r × GA E s => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2) ∈ tens2 V₁ V₂ := by
  have e : (fun m : GA E r × GA E s => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2) =
      ∑ i, fun m : GA E r × GA E s => (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2 := by
    funext m
    simp [Finset.sum_apply]
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨ψ₁ i, h₁ i, ψ₂ i, h₂ i, rfl⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem exists_decomp (g : GA E (r + s)) : ∃ (x : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s))
    (g' : GL (Fin (r + s)) (Af E)), g = unip x * lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g') := by
  obtain ⟨T, hT⟩ := GlobalTheory.CompanionTheory.CTFin.IwaAd.iwasawa_finite_cosets E r s ⊤ isOpen_univ
  obtain ⟨x, m, t, k, l, -, -, rfl⟩ := hT g
  refine ⟨x, m, k, t * l, ?_⟩
  rw [map_mul, ← mul_assoc (infGL E (r + s) _), infGL_comm]
  simp only [mul_assoc]

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem exists_slice_ne {F : Sm E (r + s)} (hF : F ≠ 0) (hu : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g) :
    ∃ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m : GA E r × GA E s),
      F.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hF
  apply Subtype.ext
  funext g
  obtain ⟨x, m, k, g', rfl⟩ := exists_decomp g
  rw [mul_assoc, hu, hcon k g' m]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem sum_left_ne {n : ℕ} {ψ₁ : Fin n → Sm E r} {ψ₂ : Fin n → Sm E s} {m₁ : GA E r} {m₂ : GA E s}
    (h : ∑ i, (ψ₁ i).1 m₁ * (ψ₂ i).1 m₂ ≠ 0) : ∑ i, (ψ₂ i).1 m₂ • ψ₁ i ≠ 0 := by
  intro h0
  apply h
  have := congrArg (fun φ : Sm E r => φ.1 m₁) h0
  simpa [Submodule.coe_sum, Finset.sum_apply, mul_comm] using this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem sum_right_ne {n : ℕ} {ψ₁ : Fin n → Sm E r} {ψ₂ : Fin n → Sm E s} {m₁ : GA E r} {m₂ : GA E s}
    (h : ∑ i, (ψ₁ i).1 m₁ * (ψ₂ i).1 m₂ ≠ 0) : ∑ i, (ψ₁ i).1 m₁ • ψ₂ i ≠ 0 := by
  intro h0
  apply h
  have := congrArg (fun φ : Sm E s => φ.1 m₂) h0
  simpa [Submodule.coe_sum, Finset.sum_apply] using this

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem step_left {n : ℕ} {ψ₁ : Fin n → Sm E r} {ψ₂ : Fin n → Sm E s} {m₂ : GA E s} (f : Sm E r →ₗ[ℂ] Sm E r)
    (h : f (∑ i, (ψ₂ i).1 m₂ • ψ₁ i) ≠ 0) : ∃ b₁, ∑ i, (f (ψ₁ i)).1 b₁ * (ψ₂ i).1 m₂ ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  apply Subtype.ext
  funext b
  have := hc b
  simpa [map_sum, Submodule.coe_sum, Finset.sum_apply, mul_comm] using this

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem step_right {n : ℕ} {ψ₁ : Fin n → Sm E r} {ψ₂ : Fin n → Sm E s} {m₁ : GA E r} (f : Sm E s →ₗ[ℂ] Sm E s)
    (h : f (∑ i, (ψ₁ i).1 m₁ • ψ₂ i) ≠ 0) : ∃ b₂, ∑ i, (ψ₁ i).1 m₁ * (f (ψ₂ i)).1 b₂ ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  apply Subtype.ext
  funext b
  have := hc b
  simpa [map_sum, Submodule.coe_sum, Finset.sum_apply] using this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Supply the required witnesses or components. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem inj_of_irred {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {T : Sm E N →ₗ[ℂ] Sm E N}
    (hT : ∀ o, ∀ φ ∈ V, T (act o φ) = act o (T φ)) (hne : ∃ φ ∈ V, T φ ≠ 0) : ∀ φ ∈ V, T φ = 0 → φ = 0 := by
  intro φ hφ h0
  have hW : IsStable (V ⊓ LinearMap.ker T) := fun o ψ hψ => by
    rw [Submodule.mem_inf, LinearMap.mem_ker] at hψ ⊢
    exact ⟨hV.stable o ψ hψ.1, by rw [hT o ψ hψ.1, hψ.2, map_zero]⟩
  rcases hV.irred _ inf_le_left hW with h | h
  · have hm : φ ∈ V ⊓ LinearMap.ker T := Submodule.mem_inf.2 ⟨hφ, h0⟩
    rw [h] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  · obtain ⟨ψ, hψ, hne⟩ := hne
    exact absurd (LinearMap.mem_ker.1 (Submodule.mem_inf.1 (h.ge hψ)).2) hne

end PositivityTheory.Rg.Rs.ParabolicProjection

end
