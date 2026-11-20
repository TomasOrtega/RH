import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionContragredient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaCorrespondenceLargeRank
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairingEquivContra
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedInductionProductParabolicPiTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContraAdmissibleTrace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ContraProd

section Family

variable {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)]
  [∀ a, TopologicalSpace (Γ a)] [∀ a, IsTopologicalGroup (Γ a)]
  [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

/- English proof (translation)
Rewrite `hU` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, -, t, ht, hsub⟩` from `hU`. Use `choose H hHo hHc hHs using fun a => hG a (t a) (ht a)`. Use `⟨H, hHo, hHc, fun x hx => hsub fun a _ => hHs a ?_⟩` and prove the remaining obligations. Conclude with `(Subgroup.mem_pi Set.univ).mp hx a (Set.mem_univ a)`.
-/
theorem exists_pi_subset
    (hG : ∀ a, ∀ U ∈ nhds (1 : Γ a), ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧
      IsCompact (K : Set (Γ a)) ∧ (K : Set (Γ a)) ⊆ U)
    (U : Set (∀ a, Γ a)) (hU : U ∈ nhds (1 : ∀ a, Γ a)) :
    ∃ H : ∀ a, Subgroup (Γ a), (∀ a, IsOpen (H a : Set (Γ a))) ∧ (∀ a, IsCompact (H a : Set (Γ a))) ∧
      ((Subgroup.pi Set.univ H : Subgroup (∀ a, Γ a)) : Set (∀ a, Γ a)) ⊆ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  choose H hHo hHc hHs using fun a => hG a (t a) (ht a)
  refine ⟨H, hHo, hHc, fun x hx => hsub fun a _ => hHs a ?_⟩
  exact (Subgroup.mem_pi Set.univ).mp hx a (Set.mem_univ a)

/- English proof (translation)
Introduce `U hU`. Take `⟨H, hHo, hHc, hsub⟩` from `exists_pi_subset hG U hU`. Use `⟨Subgroup.pi Set.univ H, ?_, ?_, hsub⟩` and prove the remaining obligations. Use `show IsOpen (Set.pi Set.univ fun a => (H a : Set (Γ a)))`. Conclude with `isOpen_set_pi Set.finite_univ fun a _ => hHo a`.

Use `show IsCompact (Set.pi Set.univ fun a => (H a : Set (Γ a)))`. Conclude with `isCompact_univ_pi fun a => hHc a`.
-/
theorem pi_compactOpen_basis
    (hG : ∀ a, ∀ U ∈ nhds (1 : Γ a), ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧
      IsCompact (K : Set (Γ a)) ∧ (K : Set (Γ a)) ⊆ U) :
    ∀ U ∈ nhds (1 : ∀ a, Γ a), ∃ K : Subgroup (∀ a, Γ a), IsOpen (K : Set (∀ a, Γ a)) ∧
      IsCompact (K : Set (∀ a, Γ a)) ∧ (K : Set (∀ a, Γ a)) ⊆ U := by
  intro U hU
  obtain ⟨H, hHo, hHc, hsub⟩ := exists_pi_subset hG U hU
  refine ⟨Subgroup.pi Set.univ H, ?_, ?_, hsub⟩
  · show IsOpen (Set.pi Set.univ fun a => (H a : Set (Γ a)))
    exact isOpen_set_pi Set.finite_univ fun a _ => hHo a
  · show IsCompact (Set.pi Set.univ fun a => (H a : Set (Γ a)))
    exact isCompact_univ_pi fun a => hHc a

/- English proof (translation)
Use `⟨isSmooth_piTensor fun a => (hρ a).1, fun K ho hc => ?_⟩` and prove the remaining obligations. Take `⟨H, h1, h2, h3⟩` from `exists_pi_subset hG _ (ho.mem_nhds (one_mem K))`. Use `haveI : ∀ a, FiniteDimensional ℂ (fixed (ρ a) (H a)) := fun a => (hρ a).2 _ (h1 a) (h2 a)`. Set `M : (⨂[ℂ] a, fixed (ρ a) (H a)) →ₗ[ℂ] ⨂[ℂ] a, X a` to `PiTensorProduct.map fun a => (fixed (ρ a) (H a)).subtype`. Establish `hle : fixed (piTensor ρ) K ≤ LinearMap.range M`.

Introduce `w hw`. Establish `hs` using `GlobalTheory.SmGL.IndTensor.mem_span_of_fixed (fun a => (hρ a).1) h2 w fun h hh => GlobalTheory.ContraRefl.mem_fix.1 hw h (h3 hh)`. Use `Submodule.span_le.2 ?_ hs` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Conclude with `⟨PiTensorProduct.tprod ℂ fun a => ⟨v a, hv a⟩, by simp [M]⟩`.

Conclude with `Submodule.finiteDimensional_of_le hle`.
-/
theorem isAdmissible_piTensor [∀ a, T2Space (Γ a)]
    (hG : ∀ a, ∀ U ∈ nhds (1 : Γ a), ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧
      IsCompact (K : Set (Γ a)) ∧ (K : Set (Γ a)) ⊆ U)
    {ρ : ∀ a, Representation ℂ (Γ a) (X a)} (hρ : ∀ a, IsAdmissible (ρ a)) :
    IsAdmissible (piTensor ρ) := by
  refine ⟨isSmooth_piTensor fun a => (hρ a).1, fun K ho hc => ?_⟩
  obtain ⟨H, h1, h2, h3⟩ := exists_pi_subset hG _ (ho.mem_nhds (one_mem K))
  haveI : ∀ a, FiniteDimensional ℂ (fixed (ρ a) (H a)) := fun a => (hρ a).2 _ (h1 a) (h2 a)
  let M : (⨂[ℂ] a, fixed (ρ a) (H a)) →ₗ[ℂ] ⨂[ℂ] a, X a :=
    PiTensorProduct.map fun a => (fixed (ρ a) (H a)).subtype
  have hle : fixed (piTensor ρ) K ≤ LinearMap.range M := by
    intro w hw
    have hs := GlobalTheory.SmGL.IndTensor.mem_span_of_fixed (fun a => (hρ a).1) h2 w fun h hh =>
      GlobalTheory.ContraRefl.mem_fix.1 hw h (h3 hh)
    refine Submodule.span_le.2 ?_ hs
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨PiTensorProduct.tprod ℂ fun a => ⟨v a, hv a⟩, by simp [M]⟩
  exact Submodule.finiteDimensional_of_le hle

def pairForm (ρ : ∀ a, Representation ℂ (Γ a) (X a)) :
    (⨂[ℂ] a, X a) →ₗ[ℂ] (⨂[ℂ] a, smoothPart (ρ a).dual) →ₗ[ℂ] ℂ :=
  ((PiTensorProduct.dualDistrib (R := ℂ) (M := X)) ∘ₗ
    PiTensorProduct.map fun a => (smoothPart (ρ a).dual).subtype).flip

/- English proof (translation)
Simplify using `only [pairForm, LinearMap.flip_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod, PiTensorProduct.dualDistrib_apply, Submodule.subtype_apply]`.
-/
theorem pairForm_tprod (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (v : ∀ a, X a)
    (l : ∀ a, smoothPart (ρ a).dual) :
    pairForm ρ (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ l) =
      ∏ a, (l a : Module.Dual ℂ (X a)) (v a) := by
  simp only [pairForm, LinearMap.flip_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
    PiTensorProduct.dualDistrib_apply, Submodule.subtype_apply]

/- English proof (translation)
Establish `hpt : ∀ v : ∀ a, X a, piTensor ρ g (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (fun a => ρ a (g a) (v a))`. Introduce `v`. Use `show PiTensorProduct.mapMonoidHom ((MonoidHom.pi fun a => (ρ a).comp (Pi.evalMonoidHom Γ a)) g) (PiTensorProduct.tprod ℂ v) = _`. Rewrite using `[PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]`. Both sides reduce to the same expression.

Establish `hpt' : ∀ l : ∀ a, smoothPart (ρ a).dual, piTensor (fun a => contra (ρ a)) g (PiTensorProduct.tprod ℂ l) = PiTensorProduct.tprod ℂ (fun a => contra (ρ a) (g a) (l a))`. Introduce `l`. Use `show PiTensorProduct.mapMonoidHom ((MonoidHom.pi fun a => (contra (ρ a)).comp (Pi.evalMonoidHom Γ a)) g) (PiTensorProduct.tprod ℂ l) = _`. Rewrite using `[PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]`. Both sides reduce to the same expression.

Use `PiTensorProduct.induction_on s (fun r v => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Use `PiTensorProduct.induction_on t (fun r' l => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Simplify using `only [map_smul, LinearMap.smul_apply]`. Rewrite using `[hpt, hpt', pairForm_tprod, pairForm_tprod]`. Use `congr 2`.

Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `show (l a : Module.Dual ℂ (X a)) (ρ a (g a)⁻¹ (ρ a (g a) (v a))) = (l a : Module.Dual ℂ (X a)) (v a)`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Simplify using `only [map_add, hx, hy]`. Simplify using `only [map_add, LinearMap.add_apply, hx, hy]`.
-/
theorem pairForm_invariant (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a)
    (s : ⨂[ℂ] a, X a) (t : ⨂[ℂ] a, smoothPart (ρ a).dual) :
    pairForm ρ (piTensor ρ g s) (piTensor (fun a => contra (ρ a)) g t) = pairForm ρ s t := by
  have hpt : ∀ v : ∀ a, X a, piTensor ρ g (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (fun a => ρ a (g a) (v a)) := by
    intro v
    show PiTensorProduct.mapMonoidHom ((MonoidHom.pi fun a => (ρ a).comp (Pi.evalMonoidHom Γ a)) g)
      (PiTensorProduct.tprod ℂ v) = _
    rw [PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]
    rfl
  have hpt' : ∀ l : ∀ a, smoothPart (ρ a).dual, piTensor (fun a => contra (ρ a)) g (PiTensorProduct.tprod ℂ l) =
      PiTensorProduct.tprod ℂ (fun a => contra (ρ a) (g a) (l a)) := by
    intro l
    show PiTensorProduct.mapMonoidHom ((MonoidHom.pi fun a => (contra (ρ a)).comp (Pi.evalMonoidHom Γ a)) g)
      (PiTensorProduct.tprod ℂ l) = _
    rw [PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]
    rfl
  refine PiTensorProduct.induction_on s (fun r v => ?_) (fun x y hx hy => ?_)
  · refine PiTensorProduct.induction_on t (fun r' l => ?_) (fun x y hx hy => ?_)
    · simp only [map_smul, LinearMap.smul_apply]
      rw [hpt, hpt', pairForm_tprod, pairForm_tprod]
      congr 2
      refine Finset.prod_congr rfl fun a _ => ?_
      show (l a : Module.Dual ℂ (X a)) (ρ a (g a)⁻¹ (ρ a (g a) (v a))) = (l a : Module.Dual ℂ (X a)) (v a)
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · simp only [map_add, hx, hy]
  · simp only [map_add, LinearMap.add_apply, hx, hy]

/- English proof (translation)
Establish `hK : ∀ a, ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧ IsCompact (K : Set (Γ a))` using `fun a => by`. Take `⟨K, h1, h2, -⟩` from `hG a Set.univ Filter.univ_mem`. Conclude with `⟨K, h1, h2⟩`. Use `choose K0 hK1 hK2 using hK`. Establish `hschur : ∀ a, ∀ φ : X a →ₗ[ℂ] X a, (∀ g x, φ (ρ a g x) = ρ a g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id` using `fun a => GlobalTheory.SchurAdm.schur_admissible (Γ a) (K0 a) (hK1 a) (hK2 a) (X a) (ρ a) (hi a) (hρ a)`.

Establish `hci : ∀ a, (contra (ρ a)).IsIrreducible` using `fun a => GlobalTheory.ContraRefl.contra_isIrreducible (hG a) (hρ a) (hi a)`. Establish `hca : ∀ a, IsAdmissible (contra (ρ a))` using `fun a => GlobalTheory.SmGL.ContraTrace.isAdmissible_contra (hρ a)`. Establish `hcschur : ∀ a, ∀ φ : smoothPart (ρ a).dual →ₗ[ℂ] smoothPart (ρ a).dual, (∀ g x, φ (contra (ρ a) g x) = contra (ρ a) g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id` using `fun a => GlobalTheory.SchurAdm.schur_admissible (Γ a) (K0 a) (hK1 a) (hK2 a) _ (contra (ρ a)) (hci a) (hca a)`. Establish `hI : (piTensor ρ).IsIrreducible` using `GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur ρ hi hschur`. Establish `hI' : (piTensor fun a => contra (ρ a)).IsIrreducible` using `GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ hci hcschur`.

Establish `hCI : (contra (piTensor ρ)).IsIrreducible` using `GlobalTheory.ContraRefl.contra_isIrreducible (pi_compactOpen_basis hG) (isAdmissible_piTensor hG hρ) hI`. Establish `hB0 : pairForm ρ ≠ 0`. Establish `hne : ∀ a, ∃ v : X a, v ≠ 0` using `fun a => by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Apply `(bot_ne_top : (⊥ : Subrepresentation (ρ a)) ≠ ⊤)` to reduce the goal to its premises. Apply `Subrepresentation.ext` to reduce the goal to its premises. Use extensionality with `x`. Rewrite using `[h x]`. Conclude with `⟨fun _ => zero_mem _, fun _ => zero_mem _⟩`.

Use `choose v hv using hne`. Use `choose l hl using fun a => GlobalTheory.ContraRefl.exists_smooth_form_ne (hρ a).1 (hG a) (hv a)`. Introduce `h0`. Establish `h1` using `pairForm_tprod ρ v l`. Rewrite `h1` using `[h0]`.

Conclude with `Finset.prod_ne_zero_iff.2 (fun a _ => hl a) (by simpa using h1.symm)`. Conclude with `⟨(GlobalTheory.InvPairing.pairMap (piTensor ρ) (isSmooth_piTensor fun a => isSmooth_contra (ρ a)) (pairForm ρ) (pairForm_invariant ρ)).ofBijective (GlobalTheory.InvPairing.pairMap_bijective _ _ _ _ hB0 hI' hCI)⟩`.
-/
theorem nonempty_equiv_piTensor_contra [∀ a, T2Space (Γ a)]
    (hG : ∀ a, ∀ U ∈ nhds (1 : Γ a), ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧
      IsCompact (K : Set (Γ a)) ∧ (K : Set (Γ a)) ⊆ U)
    {ρ : ∀ a, Representation ℂ (Γ a) (X a)} (hρ : ∀ a, IsAdmissible (ρ a))
    (hi : ∀ a, (ρ a).IsIrreducible) :
    Nonempty ((piTensor fun a => contra (ρ a)).Equiv (contra (piTensor ρ))) := by
  have hK : ∀ a, ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧ IsCompact (K : Set (Γ a)) := fun a => by
    obtain ⟨K, h1, h2, -⟩ := hG a Set.univ Filter.univ_mem
    exact ⟨K, h1, h2⟩
  choose K0 hK1 hK2 using hK
  have hschur : ∀ a, ∀ φ : X a →ₗ[ℂ] X a, (∀ g x, φ (ρ a g x) = ρ a g (φ x)) →
      ∃ c : ℂ, φ = c • LinearMap.id := fun a =>
    GlobalTheory.SchurAdm.schur_admissible (Γ a) (K0 a) (hK1 a) (hK2 a) (X a) (ρ a) (hi a) (hρ a)
  have hci : ∀ a, (contra (ρ a)).IsIrreducible := fun a =>
    GlobalTheory.ContraRefl.contra_isIrreducible (hG a) (hρ a) (hi a)
  have hca : ∀ a, IsAdmissible (contra (ρ a)) := fun a =>
    GlobalTheory.SmGL.ContraTrace.isAdmissible_contra (hρ a)
  have hcschur : ∀ a, ∀ φ : smoothPart (ρ a).dual →ₗ[ℂ] smoothPart (ρ a).dual,
      (∀ g x, φ (contra (ρ a) g x) = contra (ρ a) g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id := fun a =>
    GlobalTheory.SchurAdm.schur_admissible (Γ a) (K0 a) (hK1 a) (hK2 a) _ (contra (ρ a)) (hci a) (hca a)
  have hI : (piTensor ρ).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur ρ hi hschur
  have hI' : (piTensor fun a => contra (ρ a)).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ hci hcschur
  have hCI : (contra (piTensor ρ)).IsIrreducible :=
    GlobalTheory.ContraRefl.contra_isIrreducible (pi_compactOpen_basis hG) (isAdmissible_piTensor hG hρ) hI
  have hB0 : pairForm ρ ≠ 0 := by
    have hne : ∀ a, ∃ v : X a, v ≠ 0 := fun a => by
      by_contra h
      push_neg at h
      apply (bot_ne_top : (⊥ : Subrepresentation (ρ a)) ≠ ⊤)
      apply Subrepresentation.ext
      ext x
      rw [h x]
      exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
    choose v hv using hne
    choose l hl using fun a => GlobalTheory.ContraRefl.exists_smooth_form_ne (hρ a).1 (hG a) (hv a)
    intro h0
    have h1 := pairForm_tprod ρ v l
    rw [h0] at h1
    exact Finset.prod_ne_zero_iff.2 (fun a _ => hl a) (by simpa using h1.symm)
  exact ⟨(GlobalTheory.InvPairing.pairMap (piTensor ρ) (isSmooth_piTensor fun a => isSmooth_contra (ρ a))
    (pairForm ρ) (pairForm_invariant ρ)).ofBijective (GlobalTheory.InvPairing.pairMap_bijective _ _ _ _ hB0 hI' hCI)⟩

end Family

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
The claim follows from `GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k x.1) (hA k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr) x.2.rep.irr`.
-/
theorem contra_rep_isIrreducible (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL k) :
    (contra x.rep).IsIrreducible :=
  GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k x.1)
    (hA k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr) x.2.rep.irr

/- English proof (translation)
Use `haveI : ∀ a, T2Space (GL (Fin (x a).1) k) := fun a => GlobalTheory.SplitFlip.t2Space_general_linear_group`. Conclude with `nonempty_equiv_piTensor_contra (Γ := fun a => GL (Fin (x a).1) k) (fun a => GlobalTheory.SqIntUnit.compactOpen_basis k (x a).1) (fun a => hA k (x a).1 _ (x a).rep (x a).2.rep.smooth (x a).2.rep.irr) fun a => (x a).2.rep.irr`.
-/
theorem contra_piTensor_rep (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h : ℕ} (x : Fin h → IrrGL k) :
    Nonempty ((piTensor fun a => contra (x a).rep).Equiv (contra (piTensor fun a => (x a).rep))) := by
  haveI : ∀ a, T2Space (GL (Fin (x a).1) k) := fun a => GlobalTheory.SplitFlip.t2Space_general_linear_group
  exact nonempty_equiv_piTensor_contra (Γ := fun a => GL (Fin (x a).1) k)
    (fun a => GlobalTheory.SqIntUnit.compactOpen_basis k (x a).1)
    (fun a => hA k (x a).1 _ (x a).rep (x a).2.rep.smooth (x a).2.rep.irr)
    fun a => (x a).2.rep.irr

/- English proof (translation)
Take `⟨φ⟩` from `φ`. Take `⟨ψ⟩` from `InductionContragredient.nonempty_equiv (GlobalTheory.CompanionTheory.Glob.inductionContragredient k) e hρ`. Conclude with `⟨(parIndEquiv e φ).trans ψ⟩`.
-/
theorem parInd_equiv_contra {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : (Σ a, m a) ≃ n) {σ : Representation ℂ (Levi k m) V} {ρ : Representation ℂ (Levi k m) W}
    (hρ : IsSmooth ρ) (φ : Nonempty (σ.Equiv (contra ρ))) :
    Nonempty ((parInd e σ).Equiv (contra (parInd e ρ))) := by
  obtain ⟨φ⟩ := φ
  obtain ⟨ψ⟩ := InductionContragredient.nonempty_equiv (GlobalTheory.CompanionTheory.Glob.inductionContragredient k) e hρ
  exact ⟨(parIndEquiv e φ).trans ψ⟩

/- English proof (translation)
The claim follows from `parInd_equiv_contra (stdBlocks (fun a => (x a).1) hd) (isSmooth_piTensor fun a => (x a).2.rep.smooth) (contra_piTensor_rep hA x)`.
-/
theorem contra_prodIrr_multiProd (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ}
    (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) :
    Nonempty ((multiProd (stdBlocks (fun a => (x a).1) hd) fun a => contra (x a).rep).Equiv
      (contra (prodIrr x hd))) :=
  parInd_equiv_contra (stdBlocks (fun a => (x a).1) hd)
    (isSmooth_piTensor fun a => (x a).2.rep.smooth) (contra_piTensor_rep hA x)

/- English proof (translation)
Introduce `k _ _ _ _ hA h N x hd`. Establish `hci` using `fun a => contra_rep_isIrreducible hA (x a)`. Establish `hy : (fun a => dualCl (x a)) = fun a => IrrGL.of (contra (x a).rep) (isSmooth_smoothRep _) (hci a)`. Use function extensionality and compare the values at `fun a => dif_pos (hci a)`. Establish `key : ∀ y : Fin h → IrrGL k, y = (fun a => IrrGL.of (contra (x a).rep) (isSmooth_smoothRep _) (hci a)) → ∃ hd' : ∑ a, (y a).1 = N, Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr y hd'))`.

Introduce and unpack `_ rfl`. Conclude with `⟨hd, (contra_prodIrr_multiProd hA x hd).map fun ψ => ψ.symm.trans (prodIrrEquiv hd (fun a => contra (x a).rep) (fun a => isSmooth_smoothRep _) hci)⟩`. Conclude with `key _ hy`.
-/
theorem contra_prodIrr : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ}
    (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), ∃ hd' : ∑ a, (dualCl (x a)).1 = N,
      Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr (fun a => dualCl (x a)) hd')) := by
  intro k _ _ _ _ hA h N x hd
  have hci := fun a => contra_rep_isIrreducible hA (x a)
  have hy : (fun a => dualCl (x a)) =
      fun a => IrrGL.of (contra (x a).rep) (isSmooth_smoothRep _) (hci a) :=
    funext fun a => dif_pos (hci a)
  have key : ∀ y : Fin h → IrrGL k,
      y = (fun a => IrrGL.of (contra (x a).rep) (isSmooth_smoothRep _) (hci a)) →
      ∃ hd' : ∑ a, (y a).1 = N, Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr y hd')) := by
    rintro _ rfl
    exact ⟨hd, (contra_prodIrr_multiProd hA x hd).map fun ψ => ψ.symm.trans
      (prodIrrEquiv hd (fun a => contra (x a).rep) (fun a => isSmooth_smoothRep _) hci)⟩
  exact key _ hy

end GlobalTheory.CompanionTheory.ContraProd

end
