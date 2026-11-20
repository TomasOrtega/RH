import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLawApplyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorIsometrySchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterLocalGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocalStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GoodPlaceAct

/- English proof (translation)
Introduce `m hm r hr`. Establish `hn : ‖((chrW χ t (unifAt v) : ℂˣ) : ℂ)‖ = 1`. Simplify using `only [chrW, locChar, MonoidHom.coe_comp, Function.comp_apply]`. Apply the tactic sequence `first | exact Circle.norm_coe _ | exact Circle.abs_coe _ | simp`. Establish `hr1 : |r| = 1`.

Establish `e` using `congrArg norm hr`. Rewrite `e` using `[norm_pow, hn, one_pow, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `e.symm`. Establish `hsq : r ^ 2 = 1` using `by rw [← sq_abs, hr1, one_pow]`. Apply `h ((2 * m : ℕ) : ℤ) (by exact_mod_cast (by omega : 2 * m ≠ 0))` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[zpow_natCast, Units.val_pow_eq_pow_val, Units.val_one, pow_mul', hr]`. Conclude with `hsq` after adjusting the coercions.
-/
theorem chrW_pow_not_real {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (χ : Chr F E) {v : Pl F} (t : E →ₐ[F] Fv F v)
    (h : ∀ k : ℤ, k ≠ 0 → chrW χ t (unifAt v) ^ k ≠ 1) :
    ∀ m : ℕ, 0 < m → ∀ r : ℝ, ((chrW χ t (unifAt v) : ℂ)) ^ m ≠ (r : ℂ) := by
  intro m hm r hr
  have hn : ‖((chrW χ t (unifAt v) : ℂˣ) : ℂ)‖ = 1 := by
    simp only [chrW, locChar, MonoidHom.coe_comp, Function.comp_apply]
    first | exact Circle.norm_coe _ | exact Circle.abs_coe _ | simp
  have hr1 : |r| = 1 := by
    have e := congrArg norm hr
    rw [norm_pow, hn, one_pow, Complex.norm_real, Real.norm_eq_abs] at e
    exact e.symm
  have hsq : r ^ 2 = 1 := by rw [← sq_abs, hr1, one_pow]
  apply h ((2 * m : ℕ) : ℤ) (by exact_mod_cast (by omega : 2 * m ≠ 0))
  apply Units.ext
  rw [zpow_natCast, Units.val_pow_eq_pow_val, Units.val_one, pow_mul', hr]
  exact_mod_cast hsq

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hv hnr t`. Take `⟨K, hK⟩` from `GlobalTheory.T.exists_local_GL_embedding_unitary F E σ B a a' G X om om' hTr v hv t`. Set `Bs : Base F E` to `{ B with v₁ := v, τ₁ := t }`. Establish `hTr' : IsTriple Bs G X om om'` using `⟨{ hTr.base with }, { hTr.geo with hV := { hTr.geo.hV with }, hV' := { hTr.geo.hV' with }, hW := { hTr.geo.hW with } }, { hTr.chars with good := hv }, hTr.weil, hTr.weil'⟩`. Establish `hB` using `fun g => GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hTr v (K g) (hK g).1`.

Use `choose S hS using hB`. Establish `hSplit` using `GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'`. Establish `pres : ∀ p Φ, Φ ∈ GlobalTheory.WeilM.schA F _ → om' p Φ ∈ GlobalTheory.WeilM.schA F _` using `fun p Φ hΦ => hSplit.pres p Φ hΦ`. Establish `restS : ∀ g φ r, φ ∈ SB _ → Rest (evFin F v) φ r → Rest (evFin F v) (S g φ) r` using `fun g φ r hφ hr => ⟨hr.1, by rw [← (hS g φ hφ).2 r hr]; exact pres _ _ hr.2⟩`. Establish `h1 : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S g φ ∈ SB _` using `fun g φ hφ => (hS g φ hφ).1`.

Establish `hvac` using `hTr.geo.hM'.vac v`. Establish `hlin : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ c : ℂ, S g (c • φ + φ') = c • S g φ + S g φ'`. Introduce `g φ hφ φ' hφ' c`. Use `GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v (G.M'.vac v) _ _ hvac.1 fun r hr => ?_` and prove the remaining obligations. Establish `hsum : c • φ + φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v)` using `Submodule.add_mem _ (Submodule.smul_mem _ c hφ) hφ'`.

Establish `r0` using `GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hsum hr`. Establish `r1` using `GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hφ hr`. Establish `r2` using `GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hφ' hr`. Establish `et : ∀ (ψ₁ ψ₂ : (Fin a' × Fin (a + a') → Fv F v) → ℂ), tens (evFin F v) (c • ψ₁ + ψ₂) r = c • tens (evFin F v) ψ₁ r + tens (evFin F v) ψ₂ r` using `fun ψ₁ ψ₂ => by`. Use function extensionality and compare the values at `x`.

Simplify using `only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← (hS g _ hsum).2 r r0, et, map_add, map_smul, (hS g φ hφ).2 r r1, (hS g φ' hφ').2 r r2, et]`. Establish `h2 : ∀ g g', ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S (g * g') φ = S g (S g' φ)`. Introduce `g g' φ hφ`.

Use `GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_` and prove the remaining obligations. Establish `e1 : ((K (g * g'), (1 : UA σ G.W.J))) = (K g, 1) * (K g', 1)` using `by rw [map_mul, Prod.mk_mul_mk, one_mul]`. Rewrite using `[← (hS (g * g') φ hφ).2 r hr, e1, map_mul, Module.End.mul_apply, (hS g' φ hφ).2 r hr, (hS g (S g' φ) (h1 g' φ hφ)).2 r (restS g' φ r hφ hr)]`. Establish `h3 : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S 1 φ = φ`. Introduce `φ hφ`.

Use `GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_` and prove the remaining obligations. Establish `e1 : ((K 1, (1 : UA σ G.W.J))) = 1` using `by rw [map_one]; rfl`. Rewrite using `[← (hS 1 φ hφ).2 r hr, e1, map_one, Module.End.one_apply]`. Establish `hψ : Continuous B.ψ` using `hTr.base.std.1`. Establish `atAct : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F v) γ → At (evFin F v) (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ)`.

Introduce `g γ hγ u hu`. Simplify using `only [GlobalTheory.WeilM.actAB]`. Rewrite using `[← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]`. Establish `h4 : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F v) γ → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) = GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ …`. Introduce `g γ hγ φ hφ`.

Establish `hw` using `GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hψ v (GlobalTheory.LatVac.locCo G.M'.co v γ) φ hφ`. Use `GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_` and prove the remaining obligations. Establish `hb1` using `GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v γ hγ φ r hr`. Establish `hRw : Rest (evFin F v) (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) r` using `⟨hr.1, by rw [← hb1]; exact GlobalTheory.T.weil_representation_preserves_schwartz G.M' B.ψ hTr.base.std γ _ hr.2⟩`. Rewrite using `[← (hS g _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hS g φ hφ).2 r hr, GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v _ (atAct g γ hγ) (S g φ) r (restS g φ r hφ hr)]`.

Establish `h5 : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ μ : @MeasureTheory.Measure (Fin a' × Fin (a + a') → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ` using `fun g φ hφ μ hμ => GlobalTheory.T.localWeilOperator_isometry_schwartzBruhat B G X om om' hTr v (K g) (hK g).1 φ (S g φ) hφ (h1 g φ hφ) (hS g φ hφ).2 μ hμ`. Distinguish the cases in `hex : ∃ ι, G.M'.IsLinBar B.ψ t 1 1 ι`. Take `⟨ν, α, -, hC⟩` from `GlobalTheory.T.heisenbergIntertwiner_eq_twisted_weilOperator Bs G X om om' hTr' K hK S h1 hlin h2 h3 h4 h5`. Take `⟨ι₀, hι₀⟩` from `hex`. Use `⟨ν, GlobalTheory.T.unramified_character_local_GL hP F E σ B a a' G X om om' hTr v hv hnr t K hK S hS ν α ι₀ hι₀ (hC ι₀ hι₀), fun ι hι g₀ => ⟨K g₀, (hK g₀).1, fun φ hφ => ⟨S g₀ φ, h1 g₀ φ hφ, (hS g₀ φ hφ).2, ?_⟩⟩⟩` and prove the remaining obligations.

Rewrite using `[hC ι hι g₀ φ hφ]`. Use function extensionality and compare the values at `Y`. Simplify using `only [GlobalTheory.SplitFlip.omB, map_one, Units.val_one]`. Conclude with `⟨chrW X.ν t, chrW_pow_not_real _ t (fun k hk => hnr t k hk), fun ι hι => absurd ⟨ι, hι⟩ hex⟩`.
-/
theorem act_omB : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v →
    (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) → ∀ t : E →ₐ[F] Fv F v,
    ∃ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν₀ (unifAt v) : ℂ)) ^ m ≠ (r : ℂ)) ∧
      ∀ ι, G.M'.IsLinBar B.ψ t 1 1 ι → ∀ g₀ : GL (Fin a') (Fv F v), ∃ g ∈ UAt σ G.V' (evFin F v),
        ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
          Acts (evFin F v) (om' (g, 1)) φ φ₁ ∧ ι φ₁ = GlobalTheory.SplitFlip.omB ν₀ ν₀ g₀ 1 (ι φ) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hv hnr t
  obtain ⟨K, hK⟩ := GlobalTheory.T.exists_local_GL_embedding_unitary F E σ B a a' G X om om' hTr v hv t
  let Bs : Base F E := { B with v₁ := v, τ₁ := t }
  have hTr' : IsTriple Bs G X om om' := ⟨{ hTr.base with }, { hTr.geo with hV := { hTr.geo.hV with }, hV' := { hTr.geo.hV' with }, hW := { hTr.geo.hW with } },
    { hTr.chars with good := hv }, hTr.weil, hTr.weil'⟩
  have hB := fun g => GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hTr v (K g) (hK g).1
  choose S hS using hB
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  have pres : ∀ p Φ, Φ ∈ GlobalTheory.WeilM.schA F _ → om' p Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun p Φ hΦ => hSplit.pres p Φ hΦ
  have restS : ∀ g φ r, φ ∈ SB _ → Rest (evFin F v) φ r → Rest (evFin F v) (S g φ) r := fun g φ r hφ hr =>
    ⟨hr.1, by rw [← (hS g φ hφ).2 r hr]; exact pres _ _ hr.2⟩
  have h1 : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S g φ ∈ SB _ := fun g φ hφ => (hS g φ hφ).1
  have hvac := hTr.geo.hM'.vac v
  have hlin : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ c : ℂ,
      S g (c • φ + φ') = c • S g φ + S g φ' := by
    intro g φ hφ φ' hφ' c
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v (G.M'.vac v) _ _ hvac.1 fun r hr => ?_
    have hsum : c • φ + φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v) := Submodule.add_mem _ (Submodule.smul_mem _ c hφ) hφ'
    have r0 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hsum hr
    have r1 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hφ hr
    have r2 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hφ' hr
    have et : ∀ (ψ₁ ψ₂ : (Fin a' × Fin (a + a') → Fv F v) → ℂ), tens (evFin F v) (c • ψ₁ + ψ₂) r =
        c • tens (evFin F v) ψ₁ r + tens (evFin F v) ψ₂ r := fun ψ₁ ψ₂ => by
      funext x; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [← (hS g _ hsum).2 r r0, et, map_add, map_smul, (hS g φ hφ).2 r r1, (hS g φ' hφ').2 r r2, et]
  have h2 : ∀ g g', ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S (g * g') φ = S g (S g' φ) := by
    intro g g' φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_
    have e1 : ((K (g * g'), (1 : UA σ G.W.J))) = (K g, 1) * (K g', 1) := by rw [map_mul, Prod.mk_mul_mk, one_mul]
    rw [← (hS (g * g') φ hφ).2 r hr, e1, map_mul, Module.End.mul_apply, (hS g' φ hφ).2 r hr,
      (hS g (S g' φ) (h1 g' φ hφ)).2 r (restS g' φ r hφ hr)]
  have h3 : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S 1 φ = φ := by
    intro φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_
    have e1 : ((K 1, (1 : UA σ G.W.J))) = 1 := by rw [map_one]; rfl
    rw [← (hS 1 φ hφ).2 r hr, e1, map_one, Module.End.one_apply]
  have hψ : Continuous B.ψ := hTr.base.std.1
  have atAct : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F v) γ →
      At (evFin F v) (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ) := by
    intro g γ hγ u hu
    simp only [GlobalTheory.WeilM.actAB]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]
  have h4 : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F v) γ → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v)
            (GlobalTheory.LatVac.locCo G.M'.co v (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ)) (S g φ) := by
    intro g γ hγ φ hφ
    have hw := GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hψ v (GlobalTheory.LatVac.locCo G.M'.co v γ) φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v γ hγ φ r hr
    have hRw : Rest (evFin F v) (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.T.weil_representation_preserves_schwartz G.M' B.ψ hTr.base.std γ _ hr.2⟩
    rw [← (hS g _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hS g φ hφ).2 r hr,
      GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v _ (atAct g γ hγ) (S g φ) r (restS g φ r hφ hr)]
  have h5 : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ μ : @MeasureTheory.Measure (Fin a' × Fin (a + a') → Fv F v) (borel _),
      @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ :=
    fun g φ hφ μ hμ => GlobalTheory.T.localWeilOperator_isometry_schwartzBruhat B G X om om' hTr v (K g) (hK g).1 φ (S g φ) hφ (h1 g φ hφ) (hS g φ hφ).2 μ hμ
  by_cases hex : ∃ ι, G.M'.IsLinBar B.ψ t 1 1 ι
  · obtain ⟨ν, α, -, hC⟩ := GlobalTheory.T.heisenbergIntertwiner_eq_twisted_weilOperator Bs G X om om' hTr' K hK S h1 hlin h2 h3 h4 h5
    obtain ⟨ι₀, hι₀⟩ := hex
    refine ⟨ν, GlobalTheory.T.unramified_character_local_GL hP F E σ B a a' G X om om' hTr v hv hnr t K hK S hS ν α ι₀ hι₀ (hC ι₀ hι₀),
      fun ι hι g₀ => ⟨K g₀, (hK g₀).1, fun φ hφ => ⟨S g₀ φ, h1 g₀ φ hφ, (hS g₀ φ hφ).2, ?_⟩⟩⟩
    rw [hC ι hι g₀ φ hφ]
    funext Y
    simp only [GlobalTheory.SplitFlip.omB, map_one, Units.val_one]
  · exact ⟨chrW X.ν t, chrW_pow_not_real _ t (fun k hk => hnr t k hk), fun ι hι => absurd ⟨ι, hι⟩ hex⟩

end GlobalTheory.GoodPlaceAct
