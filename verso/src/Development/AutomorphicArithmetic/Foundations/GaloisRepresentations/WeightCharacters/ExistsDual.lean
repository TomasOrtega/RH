import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[tor_coe]`. Simplify using the standard rewrite rules.
-/
private theorem tor_one (a k : ℕ) : tor a k 1 = 1 := by
  apply Units.ext
  rw [tor_coe]
  simp

/- English proof (translation)
Introduce `h`. Establish `h1 : extremal ℂ a κ = 0` using `congrArg Subtype.val h`. Conclude with `Formalism.GradedWeylDivisibility.hwNe ℂ a a le_rfl _ h1`.
-/
private theorem top_ne {a : ℕ} (κ : DomWeight a) : top κ ≠ 0 := by
  intro h
  have h1 : extremal ℂ a κ = 0 := congrArg Subtype.val h
  exact Formalism.GradedWeylDivisibility.hwNe ℂ a a le_rfl _ h1

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hw ((Module.forall_dual_apply_eq_zero_iff ℂ w).1 hc)`.
-/
private theorem exists_dual {a : ℕ} {κ : DomWeight a} {w : nablaSq ℂ a κ} (hw : w ≠ 0) :
    ∃ L : nablaSq ℂ a κ →ₗ[ℂ] ℂ, L w ≠ 0 := by
  by_contra hc
  push Not at hc
  exact hw ((Module.forall_dual_apply_eq_zero_iff ℂ w).1 hc)

/- English proof (translation)
Set `S : Subrepresentation (smallRep (unitaryIncl a) κ)` to `⟨Submodule.span ℂ A, fun u x hx => by`. Express the relevant statement in the definitionally equal form `sqRep ℂ a κ (unitaryIncl a u) x ∈ Submodule.span ℂ A`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h => exact Submodule.subset_span (hst u x h)`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx⟩`. Break down `(isIrreducible_smallRep_unitary a κ).eq_bot_or_eq_top S with h | h` into its components or cases.

It suffices to derive a contradiction. Take `⟨w, hw, hw0⟩` from `hA`. Establish `h1 : Submodule.span ℂ A = ⊥` using `congrArg Subrepresentation.toSubmodule h`. Conclude with `hw0 ((Submodule.span_eq_bot.1 h1) w hw)`. Conclude with `congrArg Subrepresentation.toSubmodule h`.
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
Introduce `hB hD hS hT hF a k κ s`. Establish `hz1 : ∀ f : Circle → ℂ, f = 0 → f 1 = 0` using `fun f h => by rw [h]; rfl`. Use `⟨fun A hA hst hexp => ?_, fun w hw hexp => ?_⟩` and prove the remaining obligations. Establish `htop : Submodule.span ℂ A = ⊤` using `span_top A hA hst`. Assume the negation of the conclusion as `hlt`.

Use `push Not at hlt`. Take `⟨L, hL⟩` from `exists_dual (top_ne κ)`. Establish `hall : ∀ x ∈ Submodule.span ℂ A, (fun z => L (sqRep ℂ a κ (tor a k z) x)) ∈ ExpLe s`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x h => exact hexp x h L`. Consider the case `zero`. Establish `h0` using `(ExpLe s).zero_mem`. Use `h0 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`.

Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`. Use `(ExpLe s).add_mem hx hy` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`.

Simplify using the standard rewrite rules. Consider the case `smul c x _ hx`. Use `(ExpLe s).smul_mem c hx` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`.

Simplify using the standard rewrite rules. Establish `hmem` using `hall (top κ) (htop.ge Submodule.mem_top)`. Establish `hfun : (fun z => L (sqRep ℂ a κ (tor a k z) (top κ))) = fun z : Circle => L (top κ) * (z : ℂ) ^ psum κ k`. Use function extensionality and compare the values at `z`. Take `⟨hup, -, hchi, -⟩` from `hF a k z`.

Rewrite using `[hT a κ _ hup, hchi κ, map_smul, smul_eq_mul, mul_comm]`. Rewrite `hmem` using `[hfun]`. Establish `hge` using `(hB.2.2.2.1 (L (top κ)) (psum κ k)).2`. Establish `h0` using `hz1 _ (hD s (psum κ k) _ hlt hmem hge)`. Simplify using `at h0`.

Conclude with `hL h0`. Assume the negation of the conclusion as `hlt push Not at hlt`. Take `⟨L, hL⟩` from `exists_dual hw`. Establish `h0` using `hz1 _ (hD (psum κ k) s _ hlt (hS a k κ w L).1 (hexp L))`. Simplify using `only [tor_one, map_one, Module.End.one_apply] at h0`.

Conclude with `hL h0`.
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
