import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseStageA

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open scoped TensorProduct

namespace PositivityTheory.Rg.BcB.N3.PseStage

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {r t : ℕ} {U X Y : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Split into cases according to the possible forms of the given data. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem kinj_prod₂MapR (π₁ : Representation ℂ (GL (Fin r) k) U) {π₂ : Representation ℂ (GL (Fin t) k) X}
    {π₂' : Representation ℂ (GL (Fin t) k) Y} (f : π₂.IntertwiningMap π₂') (hf : KInj k f) :
    KInj k (GlobalTheory.CompanionTheory.CuspStd.prod₂MapR π₁ f) := by
  intro F hF h0
  have hind := F.1.2
  simp only [indSpace, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq] at hind
  have hF' : ∀ w : ↥(KO k (Fin (r + t))),
      prod₂ π₁ π₂ w F = ((1 : ↥(KO k (Fin (r + t))) →* ℂˣ) w : ℂ) • F := hF
  have hFix : ∀ w ∈ KO k (Fin (r + t)), ∀ x, F.1.1 (x * w) = F.1.1 x := by
    intro w hw x
    have e1 : (prod₂ π₁ π₂ w F).1.1 x = F.1.1 (x * w) := rfl
    rw [← e1, hF' ⟨w, hw⟩]
    simp only [MonoidHom.one_apply, Units.val_one]
    rw [one_smul]
  have h0' : ∀ x, LinearMap.lTensor U f.toLinearMap (F.1.1 x) = 0 := by
    intro x
    have e0 : (GlobalTheory.CompanionTheory.CuspStd.prod₂MapR π₁ f F).1.1 x =
        TensorProduct.map LinearMap.id f.toLinearMap (F.1.1 x) := rfl
    rw [LinearMap.lTensor, ← e0, h0]
    rfl
  have hf' : ∀ x, (∀ h ∈ (KO k (Fin t) : Set (GL (Fin t) k)), π₂ h x = x) →
      f.toLinearMap x = 0 → x = 0 := by
    intro x hx hfx
    refine hf x ?_ hfx
    show ∀ h : ↥(KO k (Fin t)), π₂ h x = ((1 : ↥(KO k (Fin t)) →* ℂˣ) h : ℂ) • x
    intro h
    simpa using hx h h.2
  have hv : ∀ h ∈ (KO k (Fin t) : Set (GL (Fin t) k)),
      LinearMap.lTensor U (π₂ h) (F.1.1 1) = F.1.1 1 := by
    intro h hh
    set ℓ : Levi k (Two (Fin r) (Fin t)) := leviTwo k (Fin r) (Fin t) (1, h) with hℓ
    have hℓK : ℓ ∈ leviK k (Two (Fin r) (Fin t)) := by
      rw [leviK, Subgroup.mem_pi]
      intro b _
      cases b
      · exact one_mem _
      · exact hh
    have h2 : F.1.1 (leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ) = F.1.1 1 := by
      simpa using hFix _ (leviEmb_mem_KO _ hℓK) 1
    have h1 := hind ⟨leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ, leviEmb_mem_parab k _ ℓ⟩ 1
    rw [mul_one] at h1
    change F.1.1 (leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ) = _ at h1
    rw [h2] at h1
    have hE : extTensor π₁ π₂ (1, h) = LinearMap.lTensor U (π₂ h) := by
      apply TensorProduct.ext'
      intro u x
      simp [extTensor_tmul]
    clear hind hF' hFix h0' hf' hF h0 h2
    conv_rhs => rw [h1]
    rw [MonoidHom.comp_apply, twist_apply, leviProj_leviEmb, deltaHalf_of_mem_leviK hℓK,
      MonoidHom.comp_apply, hℓ]
    simp [hE]
  have h1F : F.1.1 1 = 0 :=
    eq_zero_of_lTensor π₂ (KO k (Fin t) : Set (GL (Fin t) k)) f.toLinearMap hf' (F.1.1 1) hv (h0' 1)
  have hall : ∀ x, F.1.1 x = 0 := by
    intro x
    obtain ⟨p, c, hc, rfl⟩ := GlobalTheory.SmGL.Stages.iwasawa_two (k := k) (stdSum (rfl : r + t = r + t)) x
    rw [hFix c hc, ← mul_one (p : GL (Fin (r + t)) k), hind p 1, h1F, map_zero]
  apply Subtype.ext
  apply Subtype.ext
  funext x
  rw [hall x]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Split into cases according to the possible forms of the given data. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem kinj_prod₂MapL {π₁ : Representation ℂ (GL (Fin r) k) X} {π₁' : Representation ℂ (GL (Fin r) k) Y}
    (f : π₁.IntertwiningMap π₁') (hf : KInj k f) (π₂ : Representation ℂ (GL (Fin t) k) U) :
    KInj k (GlobalTheory.CompanionTheory.CuspStd.prod₂MapL f π₂) := by
  intro F hF h0
  have hind := F.1.2
  simp only [indSpace, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq] at hind
  have hF' : ∀ w : ↥(KO k (Fin (r + t))),
      prod₂ π₁ π₂ w F = ((1 : ↥(KO k (Fin (r + t))) →* ℂˣ) w : ℂ) • F := hF
  have hFix : ∀ w ∈ KO k (Fin (r + t)), ∀ x, F.1.1 (x * w) = F.1.1 x := by
    intro w hw x
    have e1 : (prod₂ π₁ π₂ w F).1.1 x = F.1.1 (x * w) := rfl
    rw [← e1, hF' ⟨w, hw⟩]
    simp only [MonoidHom.one_apply, Units.val_one]
    rw [one_smul]
  have h0' : ∀ x, LinearMap.rTensor U f.toLinearMap (F.1.1 x) = 0 := by
    intro x
    have e0 : (GlobalTheory.CompanionTheory.CuspStd.prod₂MapL f π₂ F).1.1 x =
        TensorProduct.map f.toLinearMap LinearMap.id (F.1.1 x) := rfl
    rw [LinearMap.rTensor, ← e0, h0]
    rfl
  have hf' : ∀ x, (∀ h ∈ (KO k (Fin r) : Set (GL (Fin r) k)), π₁ h x = x) →
      f.toLinearMap x = 0 → x = 0 := by
    intro x hx hfx
    refine hf x ?_ hfx
    show ∀ h : ↥(KO k (Fin r)), π₁ h x = ((1 : ↥(KO k (Fin r)) →* ℂˣ) h : ℂ) • x
    intro h
    simpa using hx h h.2
  have hv : ∀ h ∈ (KO k (Fin r) : Set (GL (Fin r) k)),
      LinearMap.rTensor U (π₁ h) (F.1.1 1) = F.1.1 1 := by
    intro h hh
    set ℓ : Levi k (Two (Fin r) (Fin t)) := leviTwo k (Fin r) (Fin t) (h, 1) with hℓ
    have hℓK : ℓ ∈ leviK k (Two (Fin r) (Fin t)) := by
      rw [leviK, Subgroup.mem_pi]
      intro b _
      cases b
      · exact hh
      · exact one_mem _
    have h2 : F.1.1 (leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ) = F.1.1 1 := by
      simpa using hFix _ (leviEmb_mem_KO _ hℓK) 1
    have h1 := hind ⟨leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ, leviEmb_mem_parab k _ ℓ⟩ 1
    rw [mul_one] at h1
    change F.1.1 (leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ) = _ at h1
    rw [h2] at h1
    have hE : extTensor π₁ π₂ (h, 1) = LinearMap.rTensor U (π₁ h) := by
      apply TensorProduct.ext'
      intro x u
      simp [extTensor_tmul]
    clear hind hF' hFix h0' hf' hF h0 h2
    conv_rhs => rw [h1]
    rw [MonoidHom.comp_apply, twist_apply, leviProj_leviEmb, deltaHalf_of_mem_leviK hℓK,
      MonoidHom.comp_apply, hℓ]
    simp [hE]
  have h1F : F.1.1 1 = 0 :=
    eq_zero_of_rTensor π₁ (KO k (Fin r) : Set (GL (Fin r) k)) f.toLinearMap hf' (F.1.1 1) hv (h0' 1)
  have hall : ∀ x, F.1.1 x = 0 := by
    intro x
    obtain ⟨p, c, hc, rfl⟩ := GlobalTheory.SmGL.Stages.iwasawa_two (k := k) (stdSum (rfl : r + t = r + t)) x
    rw [hFix c hc, ← mul_one (p : GL (Fin (r + t)) k), hind p 1, h1F, map_zero]
  apply Subtype.ext
  apply Subtype.ext
  funext x
  rw [hall x]
  rfl

end PositivityTheory.Rg.BcB.N3.PseStage

end
