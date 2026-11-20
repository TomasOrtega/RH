import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniqueness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCoordinatesEvalZeroFormMemAdmissible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairRestrictionThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBlockGeneratorsLagrangianNormalFStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerCompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanBaseChangeOfAnnihilatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGeneratorPreservesFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedLagrangianOrthogonalDescentStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.StraightEv0

variable {F : Type} [Field F]

/- English proof (translation)
Establish `h : Sum.elim (v + w).1 (v + w).2 = Sum.elim v.1 v.2 + Sum.elim w.1 w.2`. Apply the tactic sequence `funext i; cases i <;> rfl`. Simplify using `only [GlobalTheory.AdelicSvN.act, h, Matrix.mulVec_add]`. Both sides reduce to the same expression.
-/
theorem act_add {R : Type} [CommRing R] [Algebra F R] {κ : Type} [Fintype κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F)
    (v w : (κ → R) × (κ → R)) : GlobalTheory.AdelicSvN.act g (v + w) = GlobalTheory.AdelicSvN.act g v + GlobalTheory.AdelicSvN.act g w := by
  have h : Sum.elim (v + w).1 (v + w).2 = Sum.elim v.1 v.2 + Sum.elim w.1 w.2 := by
    funext i; cases i <;> rfl
  simp only [GlobalTheory.AdelicSvN.act, h, Matrix.mulVec_add]
  rfl

/- English proof (translation)
Establish `h : Sum.elim (t • v).1 (t • v).2 = t • Sum.elim v.1 v.2`. Apply the tactic sequence `funext i; cases i <;> rfl`. Simplify using `only [GlobalTheory.AdelicSvN.act, h, Matrix.mulVec_smul]`. Both sides reduce to the same expression.
-/
theorem act_smul {R : Type} [CommRing R] [Algebra F R] {κ : Type} [Fintype κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F)
    (t : R) (v : (κ → R) × (κ → R)) : GlobalTheory.AdelicSvN.act g (t • v) = t • GlobalTheory.AdelicSvN.act g v := by
  have h : Sum.elim (t • v).1 (t • v).2 = t • Sum.elim v.1 v.2 := by
    funext i; cases i <;> rfl
  simp only [GlobalTheory.AdelicSvN.act, h, Matrix.mulVec_smul]
  rfl

/- English proof (translation)
Establish `h` using `act_smul g (0 : R) (0 : (κ → R) × (κ → R))`. Rewrite `h` using `[zero_smul, zero_smul]`. Then use the resulting hypothesis.
-/
theorem act_zero {R : Type} [CommRing R] [Algebra F R] {κ : Type} [Fintype κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F) :
    GlobalTheory.AdelicSvN.act g (0 : (κ → R) × (κ → R)) = 0 := by
  have h := act_smul g (0 : R) (0 : (κ → R) × (κ → R))
  rwa [zero_smul, zero_smul] at h

/- English proof (translation)
Establish `h : Sum.elim (fun i => algebraMap F R (a i)) (fun i => algebraMap F R (b i)) = (algebraMap F R) ∘ Sum.elim a b`. Apply the tactic sequence `funext i; cases i <;> rfl`. Establish `key : ∀ k, (g.map (algebraMap F R) *ᵥ ((algebraMap F R) ∘ Sum.elim a b)) k = algebraMap F R ((g *ᵥ Sum.elim a b) k)` using `fun k => (RingHom.map_mulVec (algebraMap F R) g _ k).symm`. Use extensionality with `i`. Simplify using `only [GlobalTheory.AdelicSvN.act, Function.comp_apply, h, key]`.

Simplify using `only [GlobalTheory.AdelicSvN.act, Function.comp_apply, h, key]`.
-/
theorem act_hat {R : Type} [CommRing R] [Algebra F R] {κ : Type} [Fintype κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F)
    (a b : κ → F) :
    GlobalTheory.AdelicSvN.act g ((fun i => algebraMap F R (a i)), (fun i => algebraMap F R (b i))) =
      ((fun i => algebraMap F R (((g *ᵥ Sum.elim a b) ∘ Sum.inl) i)),
        (fun i => algebraMap F R (((g *ᵥ Sum.elim a b) ∘ Sum.inr) i))) := by
  have h : Sum.elim (fun i => algebraMap F R (a i)) (fun i => algebraMap F R (b i)) =
      (algebraMap F R) ∘ Sum.elim a b := by
    funext i; cases i <;> rfl
  have key : ∀ k, (g.map (algebraMap F R) *ᵥ ((algebraMap F R) ∘ Sum.elim a b)) k =
      algebraMap F R ((g *ᵥ Sum.elim a b) k) := fun k => (RingHom.map_mulVec (algebraMap F R) g _ k).symm
  ext i
  · simp only [GlobalTheory.AdelicSvN.act, Function.comp_apply, h, key]
  · simp only [GlobalTheory.AdelicSvN.act, Function.comp_apply, h, key]

variable {E : Type} [Field E] [Algebra F E]

/- English proof (translation)
Unfold `incM`. Conclude with `Matrix.map_mul`.
-/
theorem incM_mul [NumberField F] {a b c : ℕ} (x : Matrix (Fin a) (Fin b) E) (y : Matrix (Fin b) (Fin c) E) :
    incM F (x * y) = incM F x * incM F y := by
  unfold incM; exact Matrix.map_mul

/- English proof (translation)
Unfold `incM`. Conclude with `Matrix.transpose_map`.
-/
theorem incM_transpose [NumberField F] {a b : ℕ} (x : Matrix (Fin a) (Fin b) E) : incM F xᵀ = (incM F x)ᵀ := by
  unfold incM; exact Matrix.transpose_map

end GlobalTheory.StraightEv0

namespace GlobalTheory.StraightEv0
/- English proof (translation)
The claim follows from `GlobalTheory.T.span_base_change_of_annihilator`.
-/
theorem T1 : ∀ (F R : Type) [Field F] [CommRing R] [Algebra F R] (κ : Type) [Fintype κ] (A : Set (κ → F)) (x : κ → R),
    (∀ y : κ → F, (∀ a ∈ A, a ⬝ᵥ y = 0) → x ⬝ᵥ (fun i => algebraMap F R (y i)) = 0) →
    x ∈ Submodule.span R ((fun a : κ → F => fun i => algebraMap F R (a i)) '' A) := GlobalTheory.T.span_base_change_of_annihilator
/- English proof (translation)
The claim follows from `GlobalTheory.T.symplectic_generator_preserves_form`.
-/
theorem T2 : ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] [DecidableEq κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F),
    g ∈ Submonoid.closure (GlobalTheory.AdelicSvN.gens F κ) →
    (∀ v w : κ ⊕ κ → F, ((g *ᵥ v) ∘ Sum.inl) ⬝ᵥ ((g *ᵥ w) ∘ Sum.inr) - ((g *ᵥ w) ∘ Sum.inl) ⬝ᵥ ((g *ᵥ v) ∘ Sum.inr) =
      (v ∘ Sum.inl) ⬝ᵥ (w ∘ Sum.inr) - (w ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inr)) ∧ Function.Surjective fun v : κ ⊕ κ → F => g *ᵥ v := GlobalTheory.T.symplectic_generator_preserves_form
/- English proof (translation)
The claim follows from `GlobalTheory.T.mixed_lagrangian_orthogonal_descent`.
-/
theorem T3 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ w : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F),
        (∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), ∃ z : Matrix (Fin n) (Fin d₁) (AE F E),
          (M₁.co.e z).1 = 0 ∧ ∀ φ : Fn F n d,
            schr B.ψ w φ = M.co.rho B.ψ u (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) φ)) →
        (∀ z : Matrix (Fin n) (Fin d₁) E,
          w.1 ⬝ᵥ (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * incM F z * (incM F H'.ι)ᵀ)).2 =
            (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * incM F z * (incM F H'.ι)ᵀ)).1 ⬝ᵥ w.2) →
        ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), w = M.co.e u := GlobalTheory.T.mixed_lagrangian_orthogonal_descent

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e₀ he`. Establish `hψ : IsStd B.ψ` using `hP.base.std`. Establish `hψne : ∀ a, B.ψ a ≠ 0` using `fun a h => by`. Establish `h'` using `AddChar.map_add_eq_mul B.ψ a (-a)`. Rewrite `h'` using `[add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul]`.

Conclude with `one_ne_zero h'`. Take `⟨L, hiso, hrk, hL⟩` from `GlobalTheory.T.skew_adapted_pair_restriction_theta F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁`. Take `⟨g, hg, hgL⟩` from `GlobalTheory.T.exists_symplecticBlockGenerators_lagrangian_normal_form F (Fin n × Fin d) L hiso hrk`. Take `⟨S, hS, hSs, hSa, hSi⟩` from `GlobalTheory.AdelicSvN.realised_of_mem_closure B.ψ hψ hg`. Take `⟨hω, hsurj⟩` from `T2 F (Fin n × Fin d) g hg`.

Set `V : Matrix (Fin n) (Fin d₁) (AE F E) → Matrix (Fin n) (Fin d) (AE F E)` to `fun z => incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ`. Set `Arat : Set (Fin n × Fin d → F)` to `{a | ∃ w : (Fin n × Fin d → F) × (Fin n × Fin d → F), w.1 = a ∧ ∃ z : Matrix (Fin n) (Fin d₁) E, GlobalTheory.AdelicSvN.act g ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i))) = M.co.e (V (incM F z))}`. Set `Y₀ : Submodule F (Fin n × Fin d → F)` to `{ carrier := {y | ∀ a ∈ Arat, a ⬝ᵥ y = 0} add_mem' := fun {y y'} hy hy' a ha => by rw [dotProduct_add, hy a ha, hy' a ha, add_zero] zero_mem' := fun a _ => dotProduct_zero a smul_mem' := fun c y hy a ha => by rw [dotProduct_smul, hy a ha, smul_zero] }`. Establish `hVrat : ∀ z : Matrix (Fin n) (Fin d₁) E, V (incM F z) = incM F ((1 : Matrix (Fin n) (Fin n) E) * z * H'.ιᵀ)`. Introduce `z`.

Simplify using `only [V, incM_mul, incM_transpose]`. Establish `hY : ∀ y ∈ Y₀, ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), GlobalTheory.AdelicSvN.act g ((0 : Fin n × Fin d → AF F), fun i => algebraMap F (AF F) (y i)) = M.co.e u`. Introduce `y hy`. Establish `h0 : GlobalTheory.AdelicSvN.act g ((0 : Fin n × Fin d → AF F), fun i => algebraMap F (AF F) (y i)) = ((fun i => algebraMap F (AF F) (((g *ᵥ Sum.elim 0 y) ∘ Sum.inl) i)), (fun i => algebraMap F (AF F) (((g *ᵥ Sum.elim 0 y) ∘ Sum.inr) i)))`. Rewrite using `[← act_hat]`.

Reduce the equality to equality of the corresponding arguments. Rewrite using `[h0]`. Take `⟨u, hu, z, hz, hrel⟩` from `hL 1 _ (hgL y)`. Use `T3 F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ _ ⟨u, hu, z, hz, fun φ => by rw [← hrel φ, one_smul]⟩ ?_` and prove the remaining obligations. Introduce `z'`.

Take `⟨p, q, hpq⟩` from `hP.good.rat ((1 : Matrix (Fin n) (Fin n) E) * z' * H'.ιᵀ)`. Take `⟨v, hv⟩` from `hsurj (Sum.elim p q)`. Use `replace hv : g *ᵥ v = Sum.elim p q := hv`. Establish `hvA : v ∘ Sum.inl ∈ Arat` using `⟨(v ∘ Sum.inl, v ∘ Sum.inr), rfl, z', by`. Rewrite using `[act_hat, hVrat, hpq]`.

Simplify using `only [Sum.elim_comp_inl_inr]`. Rewrite using `[hv, Sum.elim_comp_inl, Sum.elim_comp_inr]⟩`. Establish `horth : (v ∘ Sum.inl) ⬝ᵥ y = 0` using `hy _ hvA`. Establish `hω'` using `hω (Sum.elim 0 y) v`. Rewrite `hω'` using `[hv, Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_comp_inl, Sum.elim_comp_inr, zero_dotProduct, horth, sub_zero, sub_eq_zero]`.

Establish `hM : V (incM F z') = incM F (1 : Matrix (Fin n) (Fin n) E) * incM F z' * (incM F H'.ι)ᵀ` using `rfl`. Rewrite using `[← hM, hVrat, hpq]`. Use `show (algebraMap F (AF F)) ∘ ((g *ᵥ Sum.elim 0 y) ∘ Sum.inl) ⬝ᵥ (algebraMap F (AF F)) ∘ q = (algebraMap F (AF F)) ∘ p ⬝ᵥ (algebraMap F (AF F)) ∘ ((g *ᵥ Sum.elim 0 y) ∘ Sum.inr)`. Rewrite using `[← RingHom.map_dotProduct, ← RingHom.map_dotProduct, hω']`. Establish `hδ : GlobalTheory.MixUniq.ev0 (Fin n × Fin d₁) ∘ₗ e₀ ∈ (adeleClass F).adm (Fin n × Fin d)` using `GlobalTheory.T.eigen_intertwiner_composition F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e₀ hP.good hP₁.good he _ (GlobalTheory.MixUniq.adelicCoordinatesEvalZeroForm_mem_admissible _)`.

Take `⟨l', hl', hl'e⟩` from `hSa _ hδ`. Take `⟨c, hc⟩` from `GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F B.ψ hψ (Fin n × Fin d) l' hl' (fun y φ hφ => by`. Establish `hm : (fun x => B.ψ (x ⬝ᵥ y) * φ x) = schr B.ψ (0, y) φ` using `by funext x; simp [schr]`. Rewrite using `[hm, hl'e _ (GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ _ φ hφ), hl'e φ hφ, hSi _ φ hφ, GlobalTheory.AdelicSvN.act_zero_eq_sum]`. Conclude with `GlobalTheory.AdelicSvN.inv_sum B.ψ hψ L hiso _ (fun t w hw Φ hΦ => GlobalTheory.MixUniq.evAt_zero_comp_eq_of_exp_phase_mul M M₁ B.ψ hψ H' e₀ he.Heisenberg₂ he.inv _ (hL t w hw) Φ hΦ) Finset.univ y _ (fun j => hgL _) _ (hS φ hφ))`.

Take `⟨Φ₀, hΦ₀, hne⟩` from `GlobalTheory.T.eigen_intertwiner_transitive F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e₀ hP.good hP₁.good he`. Take `⟨y₀, hy₀⟩` from `Function.ne_iff.1 hne`. Establish `hΦ₁` using `GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ (incM F (1 : Matrix (Fin n) (Fin n) E) * M₁.co.e.symm (y₀, 0) * (incM F H'.ι)ᵀ) Φ₀ hΦ₀`. Take `⟨φ₁, hφ₁, hSφ₁⟩` from `hSs _ hΦ₁`. Establish `hc0 : c ≠ 0`.

Introduce `h0`. Apply `hy₀` to reduce the goal to its premises. Establish `h1 : (GlobalTheory.MixUniq.ev0 (Fin n × Fin d₁) ∘ₗ e₀) (S φ₁) = 0` using `by rw [← hl'e φ₁ hφ₁, hc φ₁ hφ₁, h0, zero_mul]`. Rewrite `h1` using `[LinearMap.comp_apply, hSφ₁]`. Rewrite using `[GlobalTheory.MixUniq.apply_eq_evaluation_zero M M₁ B.ψ H'.ι e₀ he.Heisenberg₂ Φ₀ hΦ₀ y₀, h1]`.

Both sides reduce to the same expression. Use `⟨Y₀, S, hS, fun Φ hΦ => hSs Φ hΦ, hSa, ?_, ?_⟩` and prove the remaining obligations. Introduce `t y hy`. Take `⟨u, ⟨y', rfl⟩, hu⟩` from `hY y hy`. Use `⟨Matrix.vecMulVec (t • y') (incV F H'.x), ⟨t • y', rfl⟩, fun φ hφ => ?_⟩` and prove the remaining obligations.

Rewrite using `[hSi _ φ hφ]`. Establish `ht : ((0 : Fin n × Fin d → AF F), t • fun i => algebraMap F (AF F) (y i)) = t • ((0 : Fin n × Fin d → AF F), fun i => algebraMap F (AF F) (y i))`. Simplify using the standard rewrite rules. Rewrite using `[ht, act_smul, hu, ← map_smul, Matrix.smul_vecMulVec]`. Both sides reduce to the same expression.

Introduce `φ hφ h0 x hx`. Establish `hspan` using `T1 F (AF F) (Fin n × Fin d) Arat x (fun y hy => hx y hy)`. Establish `key : ∀ x' ∈ Submodule.span (AF F) ((fun a : Fin n × Fin d → F => fun i => algebraMap F (AF F) (a i)) '' Arat), ∃ w : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F), w.1 = x' ∧ ∃ Z, GlobalTheory.AdelicSvN.act g w = M.co.e (V Z)`. Introduce `x' hx'`. Proceed by induction on `hx' using Submodule.span_induction with`.

Consider the case `mem x' hx'`. Take `⟨a, ⟨w, rfl, z, hz⟩, rfl⟩` from `hx'`. Conclude with `⟨_, rfl, incM F z, hz⟩`. Consider the case `zero => exact ⟨0, rfl, 0, by rw [act_zero]; simp [V]⟩`. Consider the case `add x₁ x₂ _ _ h₁ h₂`.

Take `⟨w₁, rfl, Z₁, hZ₁⟩` from `h₁`. Take `⟨w₂, rfl, Z₂, hZ₂⟩` from `h₂`. Conclude with `⟨w₁ + w₂, rfl, Z₁ + Z₂, by`. Rewrite using `[act_add, hZ₁, hZ₂, ← map_add]`. Use `congr 1`.

Simplify using `only [V, Matrix.mul_add, Matrix.add_mul]⟩`. Consider the case `smul t x₁ _ h₁`. Take `⟨w₁, rfl, Z₁, hZ₁⟩` from `h₁`. Conclude with `⟨t • w₁, rfl, t • Z₁, by`. Rewrite using `[act_smul, hZ₁, ← map_smul]`.

Use `congr 1`. Simplify using `only [V, Matrix.mul_smul, Matrix.smul_mul]⟩`. Take `⟨w, hwx, Z, hZ⟩` from `key x hspan`. Establish `hw` using `hSi w φ hφ`. Establish `h1 : (GlobalTheory.MixUniq.ev0 (Fin n × Fin d₁) ∘ₗ e₀) (S (schr B.ψ w φ)) = 0`.

Rewrite using `[hw, hZ]`. Use `show GlobalTheory.MixUniq.ev0 _ (e₀ (M.co.rho B.ψ (V Z) (S φ))) = 0`. Rewrite using `[he.Heisenberg₂ Z (S φ) (hS φ hφ), h0]`. Simplify using `[Darboux.rho, schr]`. Rewrite `h1` using `[← hl'e _ (GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ w φ hφ), hc _ (GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ w φ hφ)]`.

Simplify using `only [schr, zero_dotProduct, zero_add, hwx] at h1`. Break down `mul_eq_zero.1 h1 with h | h` into its components or cases. Conclude with `absurd h hc0`. Break down `mul_eq_zero.1 h with h | h` into its components or cases. Conclude with `absurd h (hψne _)`.

Conclude with `h`.
-/
theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ →
      ∃ (Y₀ : Submodule F (Fin n × Fin d → F)) (S : Fn F n d → Fn F n d),
        (∀ φ ∈ schA F (Fin n × Fin d), S φ ∈ schA F (Fin n × Fin d)) ∧
        (∀ Φ ∈ schA F (Fin n × Fin d), ∃ φ ∈ schA F (Fin n × Fin d), S φ = Φ) ∧
        (∀ l ∈ (adeleClass F).adm (Fin n × Fin d), ∃ l' ∈ (adeleClass F).adm (Fin n × Fin d),
          ∀ φ ∈ schA F (Fin n × Fin d), l' φ = l (S φ)) ∧
        (∀ (t : AF F), ∀ y ∈ Y₀, ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))),
          ∀ φ ∈ schA F (Fin n × Fin d), S (schr B.ψ (0, t • fun i => algebraMap F (AF F) (y i)) φ) = M.co.rho B.ψ u (S φ)) ∧
        (∀ φ ∈ schA F (Fin n × Fin d), e₀ (S φ) = 0 →
          ∀ x : Fin n × Fin d → AF F, (∀ y ∈ Y₀, x ⬝ᵥ (fun i => algebraMap F (AF F) (y i)) = 0) → φ x = 0) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e₀ he
  classical
  have hψ : IsStd B.ψ := hP.base.std
  have hψne : ∀ a, B.ψ a ≠ 0 := fun a h => by
    have h' := AddChar.map_add_eq_mul B.ψ a (-a)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at h'
    exact one_ne_zero h'
  obtain ⟨L, hiso, hrk, hL⟩ := GlobalTheory.T.skew_adapted_pair_restriction_theta F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁
  obtain ⟨g, hg, hgL⟩ := GlobalTheory.T.exists_symplecticBlockGenerators_lagrangian_normal_form F (Fin n × Fin d) L hiso hrk
  obtain ⟨S, hS, hSs, hSa, hSi⟩ := GlobalTheory.AdelicSvN.realised_of_mem_closure B.ψ hψ hg
  obtain ⟨hω, hsurj⟩ := T2 F (Fin n × Fin d) g hg
  let V : Matrix (Fin n) (Fin d₁) (AE F E) → Matrix (Fin n) (Fin d) (AE F E) :=
    fun z => incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ
  let Arat : Set (Fin n × Fin d → F) := {a | ∃ w : (Fin n × Fin d → F) × (Fin n × Fin d → F), w.1 = a ∧
    ∃ z : Matrix (Fin n) (Fin d₁) E, GlobalTheory.AdelicSvN.act g ((fun i => algebraMap F (AF F) (w.1 i)),
      (fun i => algebraMap F (AF F) (w.2 i))) = M.co.e (V (incM F z))}
  let Y₀ : Submodule F (Fin n × Fin d → F) :=
    { carrier := {y | ∀ a ∈ Arat, a ⬝ᵥ y = 0}
      add_mem' := fun {y y'} hy hy' a ha => by rw [dotProduct_add, hy a ha, hy' a ha, add_zero]
      zero_mem' := fun a _ => dotProduct_zero a
      smul_mem' := fun c y hy a ha => by rw [dotProduct_smul, hy a ha, smul_zero] }
  have hVrat : ∀ z : Matrix (Fin n) (Fin d₁) E, V (incM F z) = incM F ((1 : Matrix (Fin n) (Fin n) E) * z * H'.ιᵀ) := by
    intro z; simp only [V, incM_mul, incM_transpose]
  have hY : ∀ y ∈ Y₀, ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))),
      GlobalTheory.AdelicSvN.act g ((0 : Fin n × Fin d → AF F), fun i => algebraMap F (AF F) (y i)) = M.co.e u := by
    intro y hy
    have h0 : GlobalTheory.AdelicSvN.act g ((0 : Fin n × Fin d → AF F), fun i => algebraMap F (AF F) (y i)) =
        ((fun i => algebraMap F (AF F) (((g *ᵥ Sum.elim 0 y) ∘ Sum.inl) i)),
          (fun i => algebraMap F (AF F) (((g *ᵥ Sum.elim 0 y) ∘ Sum.inr) i))) := by
      rw [← act_hat]; congr
    rw [h0]
    obtain ⟨u, hu, z, hz, hrel⟩ := hL 1 _ (hgL y)
    refine T3 F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ _
      ⟨u, hu, z, hz, fun φ => by rw [← hrel φ, one_smul]⟩ ?_
    intro z'
    obtain ⟨p, q, hpq⟩ := hP.good.rat ((1 : Matrix (Fin n) (Fin n) E) * z' * H'.ιᵀ)
    obtain ⟨v, hv⟩ := hsurj (Sum.elim p q)
    replace hv : g *ᵥ v = Sum.elim p q := hv
    have hvA : v ∘ Sum.inl ∈ Arat := ⟨(v ∘ Sum.inl, v ∘ Sum.inr), rfl, z', by
      rw [act_hat, hVrat, hpq]
      simp only [Sum.elim_comp_inl_inr]
      rw [hv, Sum.elim_comp_inl, Sum.elim_comp_inr]⟩
    have horth : (v ∘ Sum.inl) ⬝ᵥ y = 0 := hy _ hvA
    have hω' := hω (Sum.elim 0 y) v
    rw [hv, Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_comp_inl, Sum.elim_comp_inr, zero_dotProduct, horth,
      sub_zero, sub_eq_zero] at hω'
    have hM : V (incM F z') = incM F (1 : Matrix (Fin n) (Fin n) E) * incM F z' * (incM F H'.ι)ᵀ := rfl
    rw [← hM, hVrat, hpq]
    show (algebraMap F (AF F)) ∘ ((g *ᵥ Sum.elim 0 y) ∘ Sum.inl) ⬝ᵥ (algebraMap F (AF F)) ∘ q =
      (algebraMap F (AF F)) ∘ p ⬝ᵥ (algebraMap F (AF F)) ∘ ((g *ᵥ Sum.elim 0 y) ∘ Sum.inr)
    rw [← RingHom.map_dotProduct, ← RingHom.map_dotProduct, hω']
  have hδ : GlobalTheory.MixUniq.ev0 (Fin n × Fin d₁) ∘ₗ e₀ ∈ (adeleClass F).adm (Fin n × Fin d) :=
    GlobalTheory.T.eigen_intertwiner_composition F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e₀ hP.good hP₁.good he _ (GlobalTheory.MixUniq.adelicCoordinatesEvalZeroForm_mem_admissible _)
  obtain ⟨l', hl', hl'e⟩ := hSa _ hδ
  obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F B.ψ hψ (Fin n × Fin d) l' hl' (fun y φ hφ => by
      have hm : (fun x => B.ψ (x ⬝ᵥ y) * φ x) = schr B.ψ (0, y) φ := by funext x; simp [schr]
      rw [hm, hl'e _ (GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ _ φ hφ), hl'e φ hφ, hSi _ φ hφ, GlobalTheory.AdelicSvN.act_zero_eq_sum]
      exact GlobalTheory.AdelicSvN.inv_sum B.ψ hψ L hiso _
        (fun t w hw Φ hΦ => GlobalTheory.MixUniq.evAt_zero_comp_eq_of_exp_phase_mul M M₁ B.ψ hψ H' e₀ he.Heisenberg₂ he.inv _ (hL t w hw) Φ hΦ)
        Finset.univ y _ (fun j => hgL _) _ (hS φ hφ))
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.T.eigen_intertwiner_transitive F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e₀ hP.good hP₁.good he
  obtain ⟨y₀, hy₀⟩ := Function.ne_iff.1 hne
  have hΦ₁ := GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ
    (incM F (1 : Matrix (Fin n) (Fin n) E) * M₁.co.e.symm (y₀, 0) * (incM F H'.ι)ᵀ) Φ₀ hΦ₀
  obtain ⟨φ₁, hφ₁, hSφ₁⟩ := hSs _ hΦ₁
  have hc0 : c ≠ 0 := by
    intro h0
    apply hy₀
    have h1 : (GlobalTheory.MixUniq.ev0 (Fin n × Fin d₁) ∘ₗ e₀) (S φ₁) = 0 := by rw [← hl'e φ₁ hφ₁, hc φ₁ hφ₁, h0, zero_mul]
    rw [LinearMap.comp_apply, hSφ₁] at h1
    rw [GlobalTheory.MixUniq.apply_eq_evaluation_zero M M₁ B.ψ H'.ι e₀ he.Heisenberg₂ Φ₀ hΦ₀ y₀, h1]
    rfl
  refine ⟨Y₀, S, hS, fun Φ hΦ => hSs Φ hΦ, hSa, ?_, ?_⟩
  · intro t y hy
    obtain ⟨u, ⟨y', rfl⟩, hu⟩ := hY y hy
    refine ⟨Matrix.vecMulVec (t • y') (incV F H'.x), ⟨t • y', rfl⟩, fun φ hφ => ?_⟩
    rw [hSi _ φ hφ]
    have ht : ((0 : Fin n × Fin d → AF F), t • fun i => algebraMap F (AF F) (y i)) =
        t • ((0 : Fin n × Fin d → AF F), fun i => algebraMap F (AF F) (y i)) := by
      simp
    rw [ht, act_smul, hu, ← map_smul, Matrix.smul_vecMulVec]
    rfl
  · intro φ hφ h0 x hx
    have hspan := T1 F (AF F) (Fin n × Fin d) Arat x (fun y hy => hx y hy)
    have key : ∀ x' ∈ Submodule.span (AF F) ((fun a : Fin n × Fin d → F => fun i => algebraMap F (AF F) (a i)) '' Arat),
        ∃ w : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F), w.1 = x' ∧ ∃ Z, GlobalTheory.AdelicSvN.act g w = M.co.e (V Z) := by
      intro x' hx'
      induction hx' using Submodule.span_induction with
      | mem x' hx' =>
        obtain ⟨a, ⟨w, rfl, z, hz⟩, rfl⟩ := hx'
        exact ⟨_, rfl, incM F z, hz⟩
      | zero => exact ⟨0, rfl, 0, by rw [act_zero]; simp [V]⟩
      | add x₁ x₂ _ _ h₁ h₂ =>
        obtain ⟨w₁, rfl, Z₁, hZ₁⟩ := h₁
        obtain ⟨w₂, rfl, Z₂, hZ₂⟩ := h₂
        exact ⟨w₁ + w₂, rfl, Z₁ + Z₂, by
          rw [act_add, hZ₁, hZ₂, ← map_add]; congr 1; simp only [V, Matrix.mul_add, Matrix.add_mul]⟩
      | smul t x₁ _ h₁ =>
        obtain ⟨w₁, rfl, Z₁, hZ₁⟩ := h₁
        exact ⟨t • w₁, rfl, t • Z₁, by
          rw [act_smul, hZ₁, ← map_smul]; congr 1; simp only [V, Matrix.mul_smul, Matrix.smul_mul]⟩
    obtain ⟨w, hwx, Z, hZ⟩ := key x hspan
    have hw := hSi w φ hφ
    have h1 : (GlobalTheory.MixUniq.ev0 (Fin n × Fin d₁) ∘ₗ e₀) (S (schr B.ψ w φ)) = 0 := by
      rw [hw, hZ]
      show GlobalTheory.MixUniq.ev0 _ (e₀ (M.co.rho B.ψ (V Z) (S φ))) = 0
      rw [he.Heisenberg₂ Z (S φ) (hS φ hφ), h0]
      simp [Darboux.rho, schr]
    rw [← hl'e _ (GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ w φ hφ), hc _ (GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ w φ hφ)] at h1
    simp only [schr, zero_dotProduct, zero_add, hwx] at h1
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h hc0
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h (hψne _)
      · exact h

end GlobalTheory.StraightEv0
