import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermUnipotentIntegralVariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermTranslateFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLeviParabolicFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermKFiniteCoefficientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CtGrowthStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAutomorphicCriterionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermUnseenStatementAStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimCoefficientsFiniteDeterminingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparatelyFiniteDimFunctionsFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermCofiniteIdealTransferStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermUnseenStatementBStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDeterminantPolynomialCoefficientsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofiniteOfCapelliMonicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofiniteCenterMonicAnnihilatorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliOperatorsCommuteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliUnseenStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliConstantTermVanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliPolynomialCoefficientsIdealStatement

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CTFin

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

def leftN (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) : Submodule ℂ (Sm E (r + s)) where
  carrier := {F | ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g}
  add_mem' := fun {F G} hF hG x g => by
    change F.1 _ + G.1 _ = F.1 _ + G.1 _
    rw [hF, hG]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c F hF x g => by
    change c • F.1 _ = c • F.1 _
    rw [hF]

def vanM (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) : Submodule ℂ (Sm E (r + s)) where
  carrier := {F | ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0}
  add_mem' := fun {F G} hF hG m => by
    change F.1 _ + G.1 _ = 0
    rw [hF, hG, add_zero]
  zero_mem' := fun _ => rfl
  smul_mem' := fun c F hF m => by
    change c • F.1 _ = 0
    rw [hF, smul_zero]

/- English proof (translation)
Rewrite using `[← Polynomial.aeval_subalgebra_coe q (Zalg E n) ⟨x, hx⟩]`. Conclude with `(Polynomial.aeval (⟨x, hx⟩ : Zalg E n) q).2`.
-/
theorem aeval_mem_Zalg {n : ℕ} {x : Module.End ℂ (Sm E n)} (hx : x ∈ Zalg E n) (q : Polynomial ℂ) :
    Polynomial.aeval x q ∈ Zalg E n := by
  rw [← Polynomial.aeval_subalgebra_coe q (Zalg E n) ⟨x, hx⟩]
  exact (Polynomial.aeval (⟨x, hx⟩ : Zalg E n) q).2

/- English proof (translation)
The claim follows from `Algebra.subset_adjoin ⟨τ, u, rfl⟩`.
-/
theorem cap_mem_Zalg {n : ℕ} (τ : E →+* ℂ) (u : ℂ) : cap (a := n) τ u ∈ Zalg E n :=
  Algebra.subset_adjoin ⟨τ, u, rfl⟩

/- English proof (translation)
Set `W₀ : Set (Sm E (r + s))` to `{F | F ∈ leftN E r s ∧ ∀ z ∈ J, z F = 0}`. Establish `key : ∀ τ : E →+* ℂ, (∀ u, ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀, Polynomial.aeval (capR r s τ u) q F ∈ vanM E r s) ∧ ∀ u, ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀, Polynomial.aeval (capS r s τ u) q F ∈ vanM E r s`. Introduce `τ`. Take `⟨a, a1, a2, a3⟩` from `GlobalTheory.T.quantum_determinant_polynomial_coefficients (Module.End ℂ (Sm E (r + s))) r (fun i j : Fin r => Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s j)) (((r : ℂ) - 1) / 2)`. Take `⟨b, b1, b2, b3⟩` from `GlobalTheory.T.quantum_determinant_polynomial_coefficients (Module.End ℂ (Sm E (r + s))) s (fun i j : Fin s => Eop (a := r + s) τ (Fin.natAdd r i) (Fin.natAdd r j)) (((s : ℂ) - 1) / 2)`.

Use `GlobalTheory.T.capelli_polynomial_coefficients_ideal (Sm E (r + s)) (fun u => cap (a := r + s) τ u) (capR r s τ) (capS r s τ) (leftN E r s) (vanM E r s) W₀ (-(s : ℂ) / 2) ((r : ℂ) / 2) r s a b (fun u v => (GlobalTheory.T.capelli_operators_commute E r s τ u v).1) (fun u v => (Glob …` and prove the remaining obligations. Introduce `u F hF m`. Use `GlobalTheory.T.capelli_levi_factorization_sum E r s τ u F hF m` as an intermediate fact. Express the relevant statement in the definitionally equal form `(cap (a := r + s) τ u F).1 _ - (capS r s τ (u + (r : ℂ) / 2) (capR r s τ (u + -(s : ℂ) / 2) F)).1 _ = 0`. Rewrite using `[this, sub_eq_zero]`.

Establish `e : u + -(s : ℂ) / 2 = u - (s : ℂ) / 2` using `by ring`. Rewrite using `[e]`. Introduce `u`. Take `⟨p, hp, h⟩` from `GlobalTheory.T.cofinite_center_monic_annihilator E (r + s) J hJ _ (cap_mem_Zalg τ u)`. Conclude with `⟨p, hp, fun F hF => h F hF.2⟩`.

Use `choose q₁ m₁ h₁ using fun τ => (key τ).1`. Use `choose q₂ m₂ h₂ using fun τ => (key τ).2`. Use `⟨{z | ∃ (τ : E →+* ℂ) (u : ℂ), z = Polynomial.aeval (cap (a := r) τ u) (q₁ τ u)}, {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = Polynomial.aeval (cap (a := s) τ u) (q₂ τ u)}, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `GlobalTheory.T.cofinite_of_capelli_monic E r _ ?_ fun τ u => ⟨q₁ τ u, m₁ τ u, τ, u, rfl⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨τ, u, rfl⟩`.

Conclude with `aeval_mem_Zalg (cap_mem_Zalg τ u) _`. Use `GlobalTheory.T.cofinite_of_capelli_monic E s _ ?_ fun τ u => ⟨q₂ τ u, m₂ τ u, τ, u, rfl⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨τ, u, rfl⟩`. Conclude with `aeval_mem_Zalg (cap_mem_Zalg τ u) _`. Introduce and unpack `F hF hz G hG _ ⟨τ, u, rfl⟩`.

Use `Subtype.ext (funext fun m => ?_)` and prove the remaining obligations. Rewrite using `[(GlobalTheory.T.capelli_restrict_levi E r s τ u (q₁ τ u) F).1 G hG m]`. Conclude with `h₁ τ u F ⟨hF, hz⟩ (m, 1)`. Introduce and unpack `F hF hz G hG _ ⟨τ, u, rfl⟩`. Use `Subtype.ext (funext fun m => ?_)` and prove the remaining obligations.

Rewrite using `[(GlobalTheory.T.capelli_restrict_levi E r s τ u (q₂ τ u) F).2 G hG m]`. Conclude with `h₂ τ u F ⟨hF, hz⟩ (1, m)`.
-/
theorem centre (J : Set (Module.End ℂ (Sm E (r + s)))) (hJ : Cofin J) :
    ∃ (J₁ : Set (Module.End ℂ (Sm E r))) (J₂ : Set (Module.End ℂ (Sm E s))), Cofin J₁ ∧ Cofin J₂ ∧
    (∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → (∀ z ∈ J, z F = 0) →
      ∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ z ∈ J₁, z G = 0) ∧
    (∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → (∀ z ∈ J, z F = 0) →
      ∀ G : Sm E s, (∀ m, G.1 m = F.1 (lev (Ad E) r s (1, m))) → ∀ z ∈ J₂, z G = 0) := by
  let W₀ : Set (Sm E (r + s)) := {F | F ∈ leftN E r s ∧ ∀ z ∈ J, z F = 0}
  have key : ∀ τ : E →+* ℂ, (∀ u, ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀, Polynomial.aeval (capR r s τ u) q F ∈ vanM E r s) ∧
      ∀ u, ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀, Polynomial.aeval (capS r s τ u) q F ∈ vanM E r s := by
    intro τ
    obtain ⟨a, a1, a2, a3⟩ := GlobalTheory.T.quantum_determinant_polynomial_coefficients (Module.End ℂ (Sm E (r + s))) r
      (fun i j : Fin r => Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s j)) (((r : ℂ) - 1) / 2)
    obtain ⟨b, b1, b2, b3⟩ := GlobalTheory.T.quantum_determinant_polynomial_coefficients (Module.End ℂ (Sm E (r + s))) s
      (fun i j : Fin s => Eop (a := r + s) τ (Fin.natAdd r i) (Fin.natAdd r j)) (((s : ℂ) - 1) / 2)
    refine GlobalTheory.T.capelli_polynomial_coefficients_ideal (Sm E (r + s)) (fun u => cap (a := r + s) τ u) (capR r s τ) (capS r s τ) (leftN E r s) (vanM E r s) W₀
      (-(s : ℂ) / 2) ((r : ℂ) / 2) r s a b (fun u v => (GlobalTheory.T.capelli_operators_commute E r s τ u v).1)
      (fun u v => (GlobalTheory.T.capelli_operators_commute E r s τ u v).2.1) (fun u v => (GlobalTheory.T.capelli_operators_commute E r s τ u v).2.2)
      (fun u F hF => (GlobalTheory.T.capelli_constant_term_vanishing E r s τ u F).2 hF) (fun u F hF => ((GlobalTheory.T.capelli_constant_term_vanishing E r s τ u F).1 hF).1)
      (fun u F hF => ((GlobalTheory.T.capelli_constant_term_vanishing E r s τ u F).1 hF).2) ?_ a1 a2 a3 b1 b2 b3 (fun F hF => hF.1) ?_
    · intro u F hF m
      have := GlobalTheory.T.capelli_levi_factorization_sum E r s τ u F hF m
      change (cap (a := r + s) τ u F).1 _ - (capS r s τ (u + (r : ℂ) / 2) (capR r s τ (u + -(s : ℂ) / 2) F)).1 _ = 0
      rw [this, sub_eq_zero]
      have e : u + -(s : ℂ) / 2 = u - (s : ℂ) / 2 := by ring
      rw [e]
    · intro u
      obtain ⟨p, hp, h⟩ := GlobalTheory.T.cofinite_center_monic_annihilator E (r + s) J hJ _ (cap_mem_Zalg τ u)
      exact ⟨p, hp, fun F hF => h F hF.2⟩
  choose q₁ m₁ h₁ using fun τ => (key τ).1
  choose q₂ m₂ h₂ using fun τ => (key τ).2
  refine ⟨{z | ∃ (τ : E →+* ℂ) (u : ℂ), z = Polynomial.aeval (cap (a := r) τ u) (q₁ τ u)},
    {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = Polynomial.aeval (cap (a := s) τ u) (q₂ τ u)}, ?_, ?_, ?_, ?_⟩
  · refine GlobalTheory.T.cofinite_of_capelli_monic E r _ ?_ fun τ u => ⟨q₁ τ u, m₁ τ u, τ, u, rfl⟩
    rintro _ ⟨τ, u, rfl⟩
    exact aeval_mem_Zalg (cap_mem_Zalg τ u) _
  · refine GlobalTheory.T.cofinite_of_capelli_monic E s _ ?_ fun τ u => ⟨q₂ τ u, m₂ τ u, τ, u, rfl⟩
    rintro _ ⟨τ, u, rfl⟩
    exact aeval_mem_Zalg (cap_mem_Zalg τ u) _
  · rintro F hF hz G hG _ ⟨τ, u, rfl⟩
    refine Subtype.ext (funext fun m => ?_)
    rw [(GlobalTheory.T.capelli_restrict_levi E r s τ u (q₁ τ u) F).1 G hG m]
    exact h₁ τ u F ⟨hF, hz⟩ (m, 1)
  · rintro F hF hz G hG _ ⟨τ, u, rfl⟩
    refine Subtype.ext (funext fun m => ?_)
    rw [(GlobalTheory.T.capelli_restrict_levi E r s τ u (q₂ τ u) F).2 G hG m]
    exact h₂ τ u F ⟨hF, hz⟩ (1, m)

/- English proof (translation)
Take `⟨hA, hLf, hK, hZ⟩` from `hφ`. Take `⟨F, hF1, hF2⟩` from `GlobalTheory.T.constant_term_unipotent_integral_variant E (r + s) r φ hA.left hA.level μ 𝓕 hμ h𝓕`. Establish `hlie : ∀ φ' F' : Sm E (r + s), (∀ (γ : GL (Fin (r + s)) E) (g : GA E (r + s)), φ'.1 (ratGL E (r + s) γ * g) = φ'.1 g) → IsOpen {k | finRep E (r + s) k φ' = φ'} → (∀ g, F'.1 g = ∫ x in 𝓕, φ'.1 (unip x * g) ∂μ) → ∀ (X : Lie E (r + s)) (g : GA E (r + s)), (lie E (r + s) X F').1 g = …`. Introduce `φ' F' h1 h2 h3 X g`. Take `⟨F'', e1, e2⟩` from `GlobalTheory.T.constant_term_unipotent_integral_variant E (r + s) r φ' h1 h2 μ 𝓕 hμ h𝓕`.

Establish `: F' = F''` using `Subtype.ext (funext fun g => (h3 g).trans (e1 g).symm)`. Rewrite using `[this]`. Conclude with `e2 X g`. Use `⟨F, ⟨fun x g => ?_, fun γ g => ?_, fun k hk => ?_, fun g => ?_, fun g => ?_, fun z hz => ?_⟩, hF1⟩` and prove the remaining obligations. Rewrite using `[hF1, hF1]`.

Conclude with `GlobalTheory.T.constant_term_translate_formula E (r + s) r φ hA.left hA.level μ 𝓕 hμ h𝓕 x g`. Rewrite using `[hF1, hF1]`. Conclude with `GlobalTheory.T.constant_term_levi_parabolic_formula E r s φ hA.left hA.level μ 𝓕 hμ h𝓕 γ g`. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `F.1 (g * finGL E (r + s) k) = F.1 g`.

Rewrite using `[hF1, hF1]`. Use `congrArg (fun f : (BlockIx (r + s) r → Ad E) → ℂ => ∫ x in 𝓕, f x ∂μ) (funext fun x => ?_)` and prove the remaining obligations. Use `congrFun (congrArg Subtype.val (hLf k hk)) (unip x * g)` as an intermediate fact. Rewrite using `[← this]`. Express the relevant statement in the definitionally equal form `_ = φ.1 (unip x * g * finGL E (r + s) k)`.

Rewrite using `[mul_assoc]`. Establish `h` using `GlobalTheory.T.constant_term_k_finite_coefficient E (r + s) r φ hA.left hA.level W ρ hK μ 𝓕 hμ h𝓕 g`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Conclude with `hF1 _`.

Take `⟨C, N, h⟩` from `GlobalTheory.T.constant_term_moderate_growth_alt E (r + s) r φ hA μ 𝓕 hμ h𝓕 g`. Conclude with `⟨C, N, fun y => by rw [hF1]; exact h y⟩`. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.constant_term_automorphic_criterion E (r + s) r μ 𝓕 hμ h𝓕 hlie φ F hA.left hA.level hF1 z (hJ.1 hz) g, hZ z hz]`. Simplify using the standard rewrite rules.
-/
theorem exists_mem_goodCT (L : Subgroup (GL (Fin (r + s)) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E (r + s)) W) (J : Set (Module.End ℂ (Sm E (r + s))))
    (hJ : Cofin J) (φ : Sm E (r + s)) (hφ : φ ∈ genSpace L ρ J)
    [MeasurableSpace (BlockIx (r + s) r → Ad E)] [BorelSpace (BlockIx (r + s) r → Ad E)]
    (μ : Measure (BlockIx (r + s) r → Ad E)) (𝓕 : Set (BlockIx (r + s) r → Ad E)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratN E (r + s) r) 𝓕 μ) :
    ∃ F ∈ goodCT L ρ J, ∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ := by
  obtain ⟨hA, hLf, hK, hZ⟩ := hφ
  obtain ⟨F, hF1, hF2⟩ := GlobalTheory.T.constant_term_unipotent_integral_variant E (r + s) r φ hA.left hA.level μ 𝓕 hμ h𝓕
  have hlie : ∀ φ' F' : Sm E (r + s), (∀ (γ : GL (Fin (r + s)) E) (g : GA E (r + s)), φ'.1 (ratGL E (r + s) γ * g) = φ'.1 g) →
      IsOpen {k | finRep E (r + s) k φ' = φ'} → (∀ g, F'.1 g = ∫ x in 𝓕, φ'.1 (unip x * g) ∂μ) →
      ∀ (X : Lie E (r + s)) (g : GA E (r + s)), (lie E (r + s) X F').1 g = ∫ x in 𝓕, (lie E (r + s) X φ').1 (unip x * g) ∂μ := by
    intro φ' F' h1 h2 h3 X g
    obtain ⟨F'', e1, e2⟩ := GlobalTheory.T.constant_term_unipotent_integral_variant E (r + s) r φ' h1 h2 μ 𝓕 hμ h𝓕
    have : F' = F'' := Subtype.ext (funext fun g => (h3 g).trans (e1 g).symm)
    rw [this]
    exact e2 X g
  refine ⟨F, ⟨fun x g => ?_, fun γ g => ?_, fun k hk => ?_, fun g => ?_, fun g => ?_, fun z hz => ?_⟩, hF1⟩
  · rw [hF1, hF1]
    exact GlobalTheory.T.constant_term_translate_formula E (r + s) r φ hA.left hA.level μ 𝓕 hμ h𝓕 x g
  · rw [hF1, hF1]
    exact GlobalTheory.T.constant_term_levi_parabolic_formula E r s φ hA.left hA.level μ 𝓕 hμ h𝓕 γ g
  · refine Subtype.ext (funext fun g => ?_)
    change F.1 (g * finGL E (r + s) k) = F.1 g
    rw [hF1, hF1]
    refine congrArg (fun f : (BlockIx (r + s) r → Ad E) → ℂ => ∫ x in 𝓕, f x ∂μ) (funext fun x => ?_)
    have := congrFun (congrArg Subtype.val (hLf k hk)) (unip x * g)
    rw [← this]
    change _ = φ.1 (unip x * g * finGL E (r + s) k)
    rw [mul_assoc]
  · have h := GlobalTheory.T.constant_term_k_finite_coefficient E (r + s) r φ hA.left hA.level W ρ hK μ 𝓕 hμ h𝓕 g
    convert h using 1
    funext k
    exact hF1 _
  · obtain ⟨C, N, h⟩ := GlobalTheory.T.constant_term_moderate_growth_alt E (r + s) r φ hA μ 𝓕 hμ h𝓕 g
    exact ⟨C, N, fun y => by rw [hF1]; exact h y⟩
  · refine Subtype.ext (funext fun g => ?_)
    rw [GlobalTheory.T.constant_term_automorphic_criterion E (r + s) r μ 𝓕 hμ h𝓕 hlie φ F hA.left hA.level hF1 z (hJ.1 hz) g, hZ z hz]
    simp

/- English proof (translation)
Take `⟨J₁, J₂, c₁, c₂, k₁, k₂⟩` from `centre J hJ`. Take `⟨T, hT⟩` from `GlobalTheory.T.constant_term_unseen_statement_a E r s L hL`. Take `⟨S, hS⟩` from `GlobalTheory.T.finite_dim_coefficients_finite_determining (Kinf E (r + s)) W ρ`. Establish `key : ∀ (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)), ∃ 𝓥 : Submodule ℂ (GA E r × GA E s → ℂ), FiniteDimensional ℂ 𝓥 ∧ ∀ F ∈ goodCT L ρ J, (fun m => F.1 (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ))) ∈ 𝓥`. Introduce `t κ`.

Take `⟨L₁, ρ₁, o₁, q₁, e₁⟩` from `GlobalTheory.T.constant_term_cofinite_ideal_transfer E r s L hL W ρ hρ J hJ J₁ c₁ k₁ t κ`. Take `⟨L₂, ρ₂, o₂, q₂, e₂⟩` from `GlobalTheory.T.constant_term_unseen_statement_b E r s L hL W ρ hρ J hJ J₂ c₂ k₂ t κ`. Establish `f₁` using `h₁ L₁ o₁ W ρ₁ q₁ J₁ c₁`. Establish `f₂` using `h₂ L₂ o₂ W ρ₂ q₂ J₂ c₂`. Take `⟨𝓥, fd, hV⟩` from `GlobalTheory.T.separately_finite_dim_functions_finite (GA E r) (GA E s) ((Submodule.span ℂ (genSpace L₁ ρ₁ J₁)).map (Sm E r).subtype) ((Submodule.span ℂ (genSpace L₂ ρ₂ J₂)).map (Sm E s).subtype) inferInstance inferInstance`.

Use `⟨𝓥, fd, fun F hF => hV _ (fun m₂ => ?_) (fun m₁ => ?_)⟩` and prove the remaining obligations. Take `⟨G, hG, e⟩` from `e₁ F hF m₂`. Conclude with `⟨G, Submodule.subset_span hG, funext e⟩`. Take `⟨G, hG, e⟩` from `e₂ F hF m₁`. Conclude with `⟨G, Submodule.subset_span hG, funext e⟩`.

Use `choose 𝓥 fd hV using key`. Set `Ψ : goodCT L ρ J →ₗ[ℂ] ∀ p : T × S, 𝓥 p.1.1 p.2.1` to `{ toFun := fun F p => ⟨_, hV p.1.1 p.2.1 F.1 F.2⟩ map_add' := fun F G => rfl map_smul' := fun c F => rfl }`. Establish `hΨ : Function.Injective Ψ`. Use `(injective_iff_map_eq_zero Ψ).2 fun F hF => ?_` and prove the remaining obligations. Take `⟨F, a1, a2, a3, a4, a5, a6⟩` from `F`.

Use `Subtype.ext (Subtype.ext (funext fun g => ?_))` and prove the remaining obligations. Take `⟨x, m, t, k, l, ht, hl, rfl⟩` from `hT g`. Establish `e0 : ∀ κ ∈ S, F.1 (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) = 0`. Introduce `κ hκ`. Use `congrFun (congrArg Subtype.val (congrFun hF (⟨t, ht⟩, ⟨κ, hκ⟩))) m` as an intermediate fact.

Conclude with `this`. Establish `hc` using `hS _ (a4 (lev (Ad E) r s m * finGL E (r + s) t)) e0`. Establish `h1` using `congrFun hc k`. Establish `h2` using `congrFun (congrArg Subtype.val (a3 l hl)) (unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k))`. Express the relevant statement in the definitionally equal form `F.1 (_ * finGL E (r + s) l) = _ at h2`.

Use `h2.trans ?_` and prove the remaining obligations. Establish `e1 : unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) = unip x * (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k))`. Simplify using `only [mul_assoc]`. Rewrite using `[e1, a1]`. Conclude with `h1`.

Conclude with `FiniteDimensional.of_injective Ψ hΨ`.
-/
theorem finiteDimensional_goodCT (h₁ : GenFin E r) (h₂ : GenFin E s) (L : Subgroup (GL (Fin (r + s)) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin (r + s)) (Af E)))) {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (Kinf E (r + s)) W) (hρ : GlobalTheory.Published.AutFin.IsContRep ρ)
    (J : Set (Module.End ℂ (Sm E (r + s)))) (hJ : Cofin J) : FiniteDimensional ℂ (goodCT L ρ J) := by
  obtain ⟨J₁, J₂, c₁, c₂, k₁, k₂⟩ := centre J hJ
  obtain ⟨T, hT⟩ := GlobalTheory.T.constant_term_unseen_statement_a E r s L hL
  obtain ⟨S, hS⟩ := GlobalTheory.T.finite_dim_coefficients_finite_determining (Kinf E (r + s)) W ρ
  have key : ∀ (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)),
      ∃ 𝓥 : Submodule ℂ (GA E r × GA E s → ℂ), FiniteDimensional ℂ 𝓥 ∧ ∀ F ∈ goodCT L ρ J,
        (fun m => F.1 (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ))) ∈ 𝓥 := by
    intro t κ
    obtain ⟨L₁, ρ₁, o₁, q₁, e₁⟩ := GlobalTheory.T.constant_term_cofinite_ideal_transfer E r s L hL W ρ hρ J hJ J₁ c₁ k₁ t κ
    obtain ⟨L₂, ρ₂, o₂, q₂, e₂⟩ := GlobalTheory.T.constant_term_unseen_statement_b E r s L hL W ρ hρ J hJ J₂ c₂ k₂ t κ
    have f₁ := h₁ L₁ o₁ W ρ₁ q₁ J₁ c₁
    have f₂ := h₂ L₂ o₂ W ρ₂ q₂ J₂ c₂
    obtain ⟨𝓥, fd, hV⟩ := GlobalTheory.T.separately_finite_dim_functions_finite (GA E r) (GA E s)
      ((Submodule.span ℂ (genSpace L₁ ρ₁ J₁)).map (Sm E r).subtype)
      ((Submodule.span ℂ (genSpace L₂ ρ₂ J₂)).map (Sm E s).subtype) inferInstance inferInstance
    refine ⟨𝓥, fd, fun F hF => hV _ (fun m₂ => ?_) (fun m₁ => ?_)⟩
    · obtain ⟨G, hG, e⟩ := e₁ F hF m₂
      exact ⟨G, Submodule.subset_span hG, funext e⟩
    · obtain ⟨G, hG, e⟩ := e₂ F hF m₁
      exact ⟨G, Submodule.subset_span hG, funext e⟩
  choose 𝓥 fd hV using key
  let Ψ : goodCT L ρ J →ₗ[ℂ] ∀ p : T × S, 𝓥 p.1.1 p.2.1 :=
    { toFun := fun F p => ⟨_, hV p.1.1 p.2.1 F.1 F.2⟩
      map_add' := fun F G => rfl
      map_smul' := fun c F => rfl }
  have hΨ : Function.Injective Ψ := by
    refine (injective_iff_map_eq_zero Ψ).2 fun F hF => ?_
    obtain ⟨F, a1, a2, a3, a4, a5, a6⟩ := F
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    obtain ⟨x, m, t, k, l, ht, hl, rfl⟩ := hT g
    have e0 : ∀ κ ∈ S, F.1 (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) = 0 := by
      intro κ hκ
      have := congrFun (congrArg Subtype.val (congrFun hF (⟨t, ht⟩, ⟨κ, hκ⟩))) m
      exact this
    have hc := hS _ (a4 (lev (Ad E) r s m * finGL E (r + s) t)) e0
    have h1 := congrFun hc k
    have h2 := congrFun (congrArg Subtype.val (a3 l hl))
      (unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k))
    change F.1 (_ * finGL E (r + s) l) = _ at h2
    refine h2.trans ?_
    have e1 : unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) =
        unip x * (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k)) := by
      simp only [mul_assoc]
    rw [e1, a1]
    exact h1
  exact FiniteDimensional.of_injective Ψ hΨ

/- English proof (translation)
Introduce `E _ _ _ a hG r h0 hr`. Take `⟨s, rfl⟩ : ∃ s, a = r + s` from `⟨a - r, by omega⟩`. Introduce `L hL W _ _ _ ρ hρ J hJ`. Establish `hfd` using `finiteDimensional_goodCT (hG r hr) (hG s (by omega)) L hL ρ hρ J hJ`. Use `⟨(goodCT L ρ J).map (Sm E (r + s)).subtype, inferInstance, ?_⟩` and prove the remaining obligations.

Introduce `φ hφ _ _ μ 𝓕 hμ h𝓕`. Take `⟨F, hF, e⟩` from `exists_mem_goodCT L ρ J hJ φ hφ μ 𝓕 hμ h𝓕`. Conclude with `⟨F, hF, funext e⟩`.
-/
theorem ctFin : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ b < a, GenFin E b) →
    ∀ r, 0 < r → r < a → CTFin E a r := by
  intro E _ _ _ a hG r h0 hr
  obtain ⟨s, rfl⟩ : ∃ s, a = r + s := ⟨a - r, by omega⟩
  intro L hL W _ _ _ ρ hρ J hJ
  have hfd := finiteDimensional_goodCT (hG r hr) (hG s (by omega)) L hL ρ hρ J hJ
  refine ⟨(goodCT L ρ J).map (Sm E (r + s)).subtype, inferInstance, ?_⟩
  intro φ hφ _ _ μ 𝓕 hμ h𝓕
  obtain ⟨F, hF, e⟩ := exists_mem_goodCT L ρ J hJ φ hφ μ 𝓕 hμ h𝓕
  exact ⟨F, hF, funext e⟩

end GlobalTheory.CompanionTheory.CTFin

end
