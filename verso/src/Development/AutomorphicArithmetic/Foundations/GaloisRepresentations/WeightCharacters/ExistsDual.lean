import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem tor_one (a k : ℕ) : tor a k 1 = 1 := by
  apply Units.ext
  rw [tor_coe]
  simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem top_ne {a : ℕ} (κ : DomWeight a) : top κ ≠ 0 := by
  intro h
  have h1 : extremal ℂ a κ = 0 := congrArg Subtype.val h
  exact Formalism.GradedWeylDivisibility.hwNe ℂ a a le_rfl _ h1

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
private theorem exists_dual {a : ℕ} {κ : DomWeight a} {w : nablaSq ℂ a κ} (hw : w ≠ 0) :
    ∃ L : nablaSq ℂ a κ →ₗ[ℂ] ℂ, L w ≠ 0 := by
  by_contra hc
  push Not at hc
  exact hw ((Module.forall_dual_apply_eq_zero_iff ℂ w).1 hc)

/- English proof (translation)
Introduce a local definition for the expression. Express the relevant assertion in an equivalent form by its definition. Proceed by induction. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. Separate the alternatives or extract the components of the hypothesis. It suffices to derive a contradiction. Extract witnesses or component facts from the available result.

Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem span_top {a : ℕ} {κ : DomWeight a} (A : Set (nablaSq ℂ a κ)) (hA : ∃ w ∈ A, w ≠ 0)
    (hst : ∀ u : Matrix.unitaryGroup (Fin a) ℂ, ∀ w ∈ A, sqRep ℂ a κ (unitaryIncl a u) w ∈ A) :
    Submodule.span ℂ A = ⊤ := by
  let S : Subrepresentation (smallRep (unitaryIncl a) κ) :=
    ⟨Submodule.span ℂ A, fun u x hx => by
      change sqRep ℂ a κ (unitaryIncl a u) x ∈ Submodule.span ℂ A
      induction hx using Submodule.span_induction with
      | mem x h => exact Submodule.subset_span (hst u x h)
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx⟩
  rcases (isIrreducible_smallRep_unitary a κ).eq_bot_or_eq_top S with h | h
  · exfalso
    obtain ⟨w, hw, hw0⟩ := hA
    have h1 : Submodule.span ℂ A = ⊥ := congrArg Subrepresentation.toSubmodule h
    exact hw0 ((Submodule.span_eq_bot.1 h1) w hw)
  · exact congrArg Subrepresentation.toSubmodule h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Treat this case separately. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Treat this case separately. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Assume the negation of the conclusion and derive a contradiction.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.Wt.wtBd_of :
    UpperTheory.Gal.Wt.ExpBasic → UpperTheory.Gal.Wt.ExpDisj → UpperTheory.Gal.Wt.SqExp → UpperTheory.Gal.Wt.TopUp → UpperTheory.Gal.Wt.TorFacts → UpperTheory.Gal.Wt.WtBd := by
  intro hB hD hS hT hF a k κ s
  have hz1 : ∀ f : Circle → ℂ, f = 0 → f 1 = 0 := fun f h => by rw [h]; rfl
  refine ⟨fun A hA hst hexp => ?_, fun w hw hexp => ?_⟩
  · have htop : Submodule.span ℂ A = ⊤ := span_top A hA hst
    by_contra hlt
    push Not at hlt
    obtain ⟨L, hL⟩ := exists_dual (top_ne κ)
    have hall : ∀ x ∈ Submodule.span ℂ A, (fun z => L (sqRep ℂ a κ (tor a k z) x)) ∈ ExpLe s := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x h => exact hexp x h L
      | zero =>
        have h0 := (ExpLe s).zero_mem
        convert h0 using 1
        funext z
        simp
      | add x y _ _ hx hy =>
        have := (ExpLe s).add_mem hx hy
        convert this using 1
        funext z
        simp
      | smul c x _ hx =>
        have := (ExpLe s).smul_mem c hx
        convert this using 1
        funext z
        simp
    have hmem := hall (top κ) (htop.ge Submodule.mem_top)
    have hfun : (fun z => L (sqRep ℂ a κ (tor a k z) (top κ))) = fun z : Circle => L (top κ) * (z : ℂ) ^ psum κ k := by
      funext z
      obtain ⟨hup, -, hchi, -⟩ := hF a k z
      rw [hT a κ _ hup, hchi κ, map_smul, smul_eq_mul, mul_comm]
    rw [hfun] at hmem
    have hge := (hB.2.2.2.1 (L (top κ)) (psum κ k)).2
    have h0 := hz1 _ (hD s (psum κ k) _ hlt hmem hge)
    simp at h0
    exact hL h0
  · by_contra hlt
    push Not at hlt
    obtain ⟨L, hL⟩ := exists_dual hw
    have h0 := hz1 _ (hD (psum κ k) s _ hlt (hS a k κ w L).1 (hexp L))
    simp only [tor_one, map_one, Module.End.one_apply] at h0
    exact hL h0
