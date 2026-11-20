import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.AdaptC

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

open PositivityTheory.Mix.Adapt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {κ₀ : Type} [Fintype κ₀]
  (ε : Fin n × Fin d ≃ κ₀ ⊕ Fin n₁ × Fin d₁)

/- English proof (translation)
Take `⟨T, hT⟩` from `exists_slice ε (0 : κ₀ → mixedEmbedding.mixedSpace F)`. It suffices to establish `h : _ ∧ _ ∧ _ ∧ T ≠ 0 ∧ _ from ⟨LinearMap.funLeft ℂ ℂ fun b => glue ε 0 b, ⟨h.1, h.2.1, h.2.2.1, T, fun v => LinearMap.funLeft ℂ ℂ fun b => glue ε 0 b, h.2.2.2.1, h.2.2.2.2⟩, T, hT, _, h.2.2.2.2⟩`. Use `⟨fun Φ hΦ => slice_mem_schA ε 0 hΦ, fun z Φ _ => ?_, fun u hu Φ _ => ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `b`. Simplify using `only [LinearMap.funLeft_apply, Darboux.rho, schr, hco, (hj z).1, (hj z).2, glue_dot, glue_add, zero_dotProduct, zero_add]`.

Use function extensionality and compare the values at `b`. Simplify using `only [LinearMap.funLeft_apply, Darboux.rho, schr, hco, (hI u hu).1, (hI u hu).2, glue_dot, glue_add, zero_dotProduct, map_zero, Prod.fst_zero, Prod.snd_zero, add_zero, dotProduct_zero, mul_zero, AddChar.map_zero_eq_one, one_mul]`. Use `⟨fun h => ?_, fun v => ⟨funext (hvac v), ?_⟩, fun f φ _ _ => ?_⟩` and prove the remaining obligations. Take `⟨f, hf⟩` from `exists_schwartz_ne (Fin n × Fin d → mixedEmbedding.mixedSpace F)`. Use `hT f 0` as an intermediate fact.

Rewrite `this` using `[h, glue_zero]`. Conclude with `hf this.symm`. Use `le_antisymm ?_ fun φ hφ => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Conclude with `slice_mem_SB ε 0 hg`.

Establish `h1 : IsOpen (Set.univ.pi fun _ : κ₀ => (v.adicCompletionIntegers F : Set (Fv F v)))` using `isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _`. Establish `h2 : IsCompact (Set.univ.pi fun _ : κ₀ => (v.adicCompletionIntegers F : Set (Fv F v)))` using `isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v`. Use `⟨_, box_mem_SB ε h1 h2 hφ, funext fun b => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.funLeft_apply, box_glue, Set.indicator_of_mem (by exact fun _ _ => zero_mem _), Pi.one_apply, one_mul]`. Use function extensionality and compare the values at `b`.

Simplify using `only [LinearMap.funLeft_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hT]`. Rewrite using `[glue_map ε (evI F)]`. Use `congr 1`. Use `congr 2`. Use function extensionality and compare the values at `k`.

Conclude with `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)`. Use `finprod_congr fun v => ?_` and prove the remaining obligations. Rewrite using `[glue_map ε (evFin F v)]`. Simplify using `only [Pi.zero_apply, map_zero]`. Both sides reduce to the same expression.
-/
theorem exists_isEvS (B : Base F E) (Ma : Model σ X W) (M₁ : Model σ X₁ W₁)
    (p q : Matrix (Fin n) (Fin d) (AE F E) → κ₀ → AF F) (π : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n₁) (Fin d₁) (AE F E))
    (hco : ∀ z, Ma.co.e z = (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2))
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    (hj : ∀ z, p (incM F ι * z * (incM F ι')ᵀ) = 0 ∧ π (incM F ι * z * (incM F ι')ᵀ) = z)
    (hI : ∀ u ∈ I, p u = 0 ∧ π u = 0) (hvac : ∀ v b, Ma.vac v (glue ε 0 b) = M₁.vac v b) :
    ∃ e, IsEv B Ma M₁ ι ι' I e ∧ ∃ T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁), (∀ f b, T f b = f (glue ε 0 b)) ∧
      ∃ ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ,
        (∀ v, ev v (Ma.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Ma.vac v) →
          e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (T f) fun v => ev v (φ v) := by
  classical
  obtain ⟨T, hT⟩ := exists_slice ε (0 : κ₀ → mixedEmbedding.mixedSpace F)
  suffices h : _ ∧ _ ∧ _ ∧ T ≠ 0 ∧ _ from
    ⟨LinearMap.funLeft ℂ ℂ fun b => glue ε 0 b, ⟨h.1, h.2.1, h.2.2.1, T, fun v => LinearMap.funLeft ℂ ℂ fun b => glue ε 0 b,
      h.2.2.2.1, h.2.2.2.2⟩, T, hT, _, h.2.2.2.2⟩
  refine ⟨fun Φ hΦ => slice_mem_schA ε 0 hΦ, fun z Φ _ => ?_, fun u hu Φ _ => ?_, ?_⟩
  · funext b
    simp only [LinearMap.funLeft_apply, Darboux.rho, schr, hco, (hj z).1, (hj z).2, glue_dot, glue_add, zero_dotProduct,
      zero_add]
  · funext b
    simp only [LinearMap.funLeft_apply, Darboux.rho, schr, hco, (hI u hu).1, (hI u hu).2, glue_dot, glue_add,
      zero_dotProduct, map_zero, Prod.fst_zero, Prod.snd_zero, add_zero, dotProduct_zero, mul_zero,
      AddChar.map_zero_eq_one, one_mul]
  · refine ⟨fun h => ?_, fun v => ⟨funext (hvac v), ?_⟩,
      fun f φ _ _ => ?_⟩
    · obtain ⟨f, hf⟩ := exists_schwartz_ne (Fin n × Fin d → mixedEmbedding.mixedSpace F)
      have := hT f 0
      rw [h, glue_zero] at this
      exact hf this.symm
    · refine le_antisymm ?_ fun φ hφ => ?_
      · rintro _ ⟨g, hg, rfl⟩
        exact slice_mem_SB ε 0 hg
      · have h1 : IsOpen (Set.univ.pi fun _ : κ₀ => (v.adicCompletionIntegers F : Set (Fv F v))) :=
          isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _
        have h2 : IsCompact (Set.univ.pi fun _ : κ₀ => (v.adicCompletionIntegers F : Set (Fv F v))) :=
          isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
        refine ⟨_, box_mem_SB ε h1 h2 hφ, funext fun b => ?_⟩
        rw [LinearMap.funLeft_apply, box_glue, Set.indicator_of_mem (by exact fun _ _ => zero_mem _), Pi.one_apply, one_mul]
    · funext b
      simp only [LinearMap.funLeft_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hT]
      rw [glue_map ε (evI F)]
      congr 1
      · congr 2
        funext k
        exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
      · refine finprod_congr fun v => ?_
        rw [glue_map ε (evFin F v)]
        simp only [Pi.zero_apply, map_zero]
        rfl

/- English proof (translation)
Set `ε : Fin n × Fin d ≃ (κ × Fin 2) ⊕ Fin n₁ × Fin d₁` to `Fintype.equivOfCardEq (by simp [hcard])`. Set `β` to `Module.finBasisOfFinrankEq F E hB.cm.2.2.1`. Set `βA` to `Algebra.TensorProduct.basis (AF F) β`. Set `Tr` to `Algebra.trace (AF F) (AE F E)`. Set `p : Matrix (Fin n) (Fin d) (AE F E) → κ × Fin 2 → AF F` to `fun z k => βA.repr (b z k.1) k.2`.

Set `q : Matrix (Fin n) (Fin d) (AE F E) → κ × Fin 2 → AF F` to `fun z k => -Tr (βA k.2 * D z k.1)`. Establish `hpq : ∀ z z', p z ⬝ᵥ q z' = -Tr (b z ⬝ᵥ D z')` using `fun z z' => by`. Simplify using `only [dotProduct, Fintype.sum_prod_type, map_sum, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [← βA.sum_repr (b z k), Finset.sum_mul, map_sum, ← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, map_smul, smul_eq_mul, ← mul_neg]`. Establish `hTr : ∀ z, Tr (cA σ z) = Tr z` using `GlobalTheory.VacCocycle.trace_conj (cA σ) (cA_cA hB)`. Set `Φ : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)` to `{ toFun := fun z => (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2) map_add' := fun z z' => by`. Rewrite using `[Prod.mk_add_mk, glue_add, glue_add, hπ.map_add, map_add]`.

Apply the tactic sequence `congr 2 <;> funext k <;> simp [p, q, hb.map_add, hD.map_add, mul_add, add_comm]`. Use the proof step `map_smul' := fun c z => by`. Rewrite using `[Prod.smul_mk, glue_smul, glue_smul, hπ.map_smul, map_smul]`. Apply the tactic sequence `congr 2 <;> funext k <;> simp [p, q, hb.map_smul, hD.map_smul] }`. Establish `hΦ : ∀ z z', symp (R` using `AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) z z' = (Φ z).1 ⬝ᵥ (Φ z').2 - (Φ z').1 ⬝ᵥ (Φ z).2 := fun z z' => by`.

Establish `h1` using `M₁.co.form (π z) (π z')`. Use `show Tr _ = glue ε _ _ ⬝ᵥ glue ε _ _ - glue ε _ _ ⬝ᵥ glue ε _ _`. Express the relevant statement in the definitionally equal form `Tr _ = _ at h1`. Rewrite using `[glue_dot, glue_dot, hpq, hpq, hH, mul_add, map_add, h1, neg_one_mul, map_neg, map_sub, hTr]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hbij : Function.Bijective Φ`. Use `(bijective_of_symp (Φ ∘ₗ M.co.e.symm.toLinearMap) fun u w => by` as an intermediate fact. Establish `h1` using `M.co.form (M.co.e.symm u) (M.co.e.symm w)`. Rewrite `h1` using `[hΦ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Conclude with `h1).comp M.co.e.bijective`.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`. Simplify using the standard rewrite rules. Set `co : Darboux (symp (R` to `AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d) := ⟨LinearEquiv.ofBijective Φ hbij, hΦ⟩`. Establish `hco : ∀ z, co.e z = (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2)` using `fun z => rfl`.

Establish `hr : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))` using `fun x => by`. Take `⟨⟨y, hy⟩, ⟨y', hy'⟩, x₁, hx₁⟩` from `hrat x`. Take `⟨u, w, huw⟩` from `hM₁.rat x₁`. Use `⟨glue ε (fun k => β.repr (y k.1) k.2) u, glue ε (fun k => -Algebra.trace F E (β k.2 * y' k.1)) w, ?_⟩` and prove the remaining obligations. Rewrite using `[hco, hx₁, huw, glue_map ε (algebraMap F (AF F)), glue_map ε (algebraMap F (AF F))]`.

Apply the tactic sequence `congr 2 <;> funext k`. Simplify using `only [p, hy] show βA.repr ((1 : AF F) ⊗ₜ[F] y k.1) k.2 = _`. Simplify using `[βA, Algebra.TensorProduct.basis_repr_tmul]`. Simplify using `only [q, hy']`. Rewrite using `[map_neg, ← GlobalTheory.VacIndic.trace_inclR, map_mul (inclR (F := F) (AF F)), Algebra.TensorProduct.basis_apply]`.

Both sides reduce to the same expression. Establish `hδ : ∀ v, ∀ γ ∈ latAtV X W v, ∀ γ' ∈ latAtV X W v, ∀ θ : 𝓞 E, B.ψ (Tr (inclR (F` using `F) (AF F) (θ : E) * (b γ' ⬝ᵥ D γ))) = 1 := fun v γ hγ γ' hγ' θ => by`. Take `⟨-, δ, h0, h1, h2, h3⟩` from `hlat v γ hγ`. Use `GlobalTheory.LatVacArith.psi_symp_latAtV σ B X W r s r' s' hB hX hW v θ 1 (by rw [map_one]; exact one_mem _) γ' hγ' δ h0` as an intermediate fact. Rewrite `this` using `[one_mul, symp, hH, h1, h2, h3]`.

Simplify `this` using `[hTens]`. Establish `hv : ∀ v, ∃ φa, Model.IsVac (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W) B.ψ v φa ∧ ∀ c, φa (glue ε 0 c) = M₁.vac v c`. Introduce `v`. Use `exists_isVac ε hX hW _ M₁ hr p q π hco v (fun γ hγ => (hlat v γ hγ).1) (fun γ hγ γ' hγ' => ?_) (fun θ hθ γ hγ => ?_) (hM₁.vac v)` and prove the remaining obligations. Use `hδ v γ hγ γ' hγ' (-1)` as an intermediate fact.

Rewrite `this` using `[show ((-1 : 𝓞 E) : E) = -1 by simp, map_neg, map_one, neg_one_mul, map_neg]`. Rewrite using `[hpq, this]`. Rewrite using `[← one_mul (B.ψ _ * B.ψ _), ← hδ v γ hγ γ hγ θ]`. Simplify using `only [← AddChar.map_add_eq_mul]`. Use `congr 1`.

Establish `h1 : inclR (F` using `F) (AF F) (θ : E) + cA σ (inclR (F := F) (AF F) (θ : E)) = 1 := by`. Rewrite using `[GlobalTheory.VacIndic.cA_inclR, ← map_add, hθ, map_one]`. Establish `h2 : Tr (inclR (F` using `F) (AF F) (θ : E) * cA σ (b γ ⬝ᵥ D γ)) = Tr (b γ ⬝ᵥ D γ) - Tr (inclR (F := F) (AF F) (θ : E) * (b γ ⬝ᵥ D γ)) := by`. Rewrite using `[← hTr, map_mul, cA_cA hB, ← map_sub, eq_sub_of_add_eq' h1, sub_mul, one_mul]`. Establish `h3 : (⅟(2 : AF F)) * 2 = 1` using `invOf_mul_self _`.

Use `show _ * Tr _ = _ + (_ + _ * Tr _)`. Rewrite using `[hpq, hH, mul_add (inclR (F := F) (AF F) (θ : E)), mul_sub, map_add, map_sub, h2]`. Generalize the expression as in `(⅟(2 : AF F)) = t at h3 ⊢`. Take the linear combination `(Tr (inclR (F := F) (AF F) (θ : E) * (b γ ⬝ᵥ D γ))) * h3`. Use `choose φa hφa hφb using hv`.

Set `S : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ` to `fun v => Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1`. Set `G : Pl F → Prop` to `fun v => Model.IsVac (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W) B.ψ v (S v) ∧ M₁.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1`. Set `Ma : Model σ X W` to `⟨co, fun v => if G v then S v else φa v, M.μ, M.dom⟩`. Take `⟨e, he⟩` from `exists_isEvS ε B Ma M₁ p q π hco ι ι' I (fun z => ⟨funext fun k => by simp [p, (hj z).1], (hj z).2⟩) (fun u hu => ⟨funext fun k => by simp [p, (hI u hu).1], (hI u hu).2⟩) fun v c => by`. Distinguish the cases in `h : G v`.

Use `show (if G v then S v else φa v) _ = _`. Rewrite using `[if_pos h, h.2]`. Use `Set.indicator_eq_indicator ⟨fun hx i => ?_, fun hx i => ?_⟩ rfl` and prove the remaining obligations. Simplify using `using hx (ε.symm (.inr i))`. Take `⟨i, rfl⟩` from `ε.symm.surjective i`.

Break down `i with i | i` into its components or cases. Rewrite using `[glue_inl]`. Conclude with `zero_mem _`. Rewrite using `[glue_inr]`. Conclude with `hx i`.

Use `show (if G v then S v else φa v) _ = _`. Rewrite using `[if_neg h, hφb]`. Use `⟨ε, Ma, e, p, q, ⟨hr, fun v => ?_, ?_, hM.haar, hM.dom⟩, hco, fun z h => funext fun k => by simp [p, h], fun z h => funext fun k => by simp [q, h], he⟩` and prove the remaining obligations. Use `show Model.IsVac _ _ _ (if G v then S v else φa v) split_ifs with h`. Conclude with `h.1`.

Conclude with `hφa v`. Use `filter_upwards [GlobalTheory.VacIndic.eventually_isVac_indicator B hB X W r s r' s' hX hW co hr, hM₁.std] with v h1 h2`. Conclude with `if_pos ⟨h1, h2⟩`.
-/
theorem exists_modelS {B : Base F E} {r s r' s' : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    {M : Model σ X W} (hM : M.IsGood B.ψ) {M₁ : Model σ X₁ W₁} (hM₁ : M₁.IsGood B.ψ) {κ : Type} [Fintype κ]
    (hcard : n * d = Fintype.card κ * 2 + n₁ * d₁) (b D : Matrix (Fin n) (Fin d) (AE F E) → κ → AE F E)
    (π : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n₁) (Fin d₁) (AE F E)) (hb : IsLinearMap (AF F) b)
    (hD : IsLinearMap (AF F) D) (hπ : IsLinearMap (AF F) π)
    (hH : ∀ z z', hTens (cA σ) (incM F X.J) (incM F W.J) z z' =
      b z ⬝ᵥ D z' - cA σ (b z' ⬝ᵥ D z) + hTens (cA σ) (incM F X₁.J) (incM F W₁.J) (π z) (π z'))
    (hrat : ∀ x, (∃ y : κ → E, b (incM F x) = fun k => inclR (F := F) (AF F) (y k)) ∧
      (∃ y : κ → E, D (incM F x) = fun k => inclR (F := F) (AF F) (y k)) ∧ ∃ x₁, π (incM F x) = incM F x₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    (hj : ∀ z, b (incM F ι * z * (incM F ι')ᵀ) = 0 ∧ π (incM F ι * z * (incM F ι')ᵀ) = z)
    (hI : ∀ u ∈ I, b u = 0 ∧ π u = 0)
    (hlat : ∀ v, ∀ γ ∈ latAtV X W v, π γ ∈ latAtV X₁ W₁ v ∧ ∃ δ ∈ latAtV X W v, b δ = 0 ∧ π δ = 0 ∧ D δ = D γ) :
    ∃ (ε : Fin n × Fin d ≃ (κ × Fin 2) ⊕ Fin n₁ × Fin d₁) (Ma : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁)
      (p q : Matrix (Fin n) (Fin d) (AE F E) → κ × Fin 2 → AF F), Ma.IsGood B.ψ ∧
      (∀ z, Ma.co.e z = (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2)) ∧ (∀ z, b z = 0 → p z = 0) ∧
      (∀ z, D z = 0 → q z = 0) ∧ IsEv B Ma M₁ ι ι' I e ∧
      ∃ T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁), (∀ f b, T f b = f (glue ε 0 b)) ∧
      ∃ ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ,
        (∀ v, ev v (Ma.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Ma.vac v) →
          e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (T f) fun v => ev v (φ v) := by
  classical
  let ε : Fin n × Fin d ≃ (κ × Fin 2) ⊕ Fin n₁ × Fin d₁ := Fintype.equivOfCardEq (by simp [hcard])
  let β := Module.finBasisOfFinrankEq F E hB.cm.2.2.1
  let βA := Algebra.TensorProduct.basis (AF F) β
  let Tr := Algebra.trace (AF F) (AE F E)
  let p : Matrix (Fin n) (Fin d) (AE F E) → κ × Fin 2 → AF F := fun z k => βA.repr (b z k.1) k.2
  let q : Matrix (Fin n) (Fin d) (AE F E) → κ × Fin 2 → AF F := fun z k => -Tr (βA k.2 * D z k.1)
  have hpq : ∀ z z', p z ⬝ᵥ q z' = -Tr (b z ⬝ᵥ D z') := fun z z' => by
    simp only [dotProduct, Fintype.sum_prod_type, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    conv_rhs => rw [← βA.sum_repr (b z k), Finset.sum_mul, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, ← mul_neg]
  have hTr : ∀ z, Tr (cA σ z) = Tr z := GlobalTheory.VacCocycle.trace_conj (cA σ) (cA_cA hB)
  let Φ : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    { toFun := fun z => (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2)
      map_add' := fun z z' => by
        rw [Prod.mk_add_mk, glue_add, glue_add, hπ.map_add, map_add]
        congr 2 <;> funext k <;> simp [p, q, hb.map_add, hD.map_add, mul_add, add_comm]
      map_smul' := fun c z => by
        rw [Prod.smul_mk, glue_smul, glue_smul, hπ.map_smul, map_smul]
        congr 2 <;> funext k <;> simp [p, q, hb.map_smul, hD.map_smul] }
  have hΦ : ∀ z z', symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) z z' =
      (Φ z).1 ⬝ᵥ (Φ z').2 - (Φ z').1 ⬝ᵥ (Φ z).2 := fun z z' => by
    have h1 := M₁.co.form (π z) (π z')
    show Tr _ = glue ε _ _ ⬝ᵥ glue ε _ _ - glue ε _ _ ⬝ᵥ glue ε _ _
    change Tr _ = _ at h1
    rw [glue_dot, glue_dot, hpq, hpq, hH, mul_add, map_add, h1, neg_one_mul, map_neg, map_sub, hTr]
    ring
  have hbij : Function.Bijective Φ := by
    have := (bijective_of_symp (Φ ∘ₗ M.co.e.symm.toLinearMap) fun u w => by
      have h1 := M.co.form (M.co.e.symm u) (M.co.e.symm w)
      rw [hΦ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
      exact h1).comp M.co.e.bijective
    convert this using 1
    funext z
    simp
  let co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d) :=
    ⟨LinearEquiv.ofBijective Φ hbij, hΦ⟩
  have hco : ∀ z, co.e z = (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2) := fun z => rfl
  have hr : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := fun x => by
    obtain ⟨⟨y, hy⟩, ⟨y', hy'⟩, x₁, hx₁⟩ := hrat x
    obtain ⟨u, w, huw⟩ := hM₁.rat x₁
    refine ⟨glue ε (fun k => β.repr (y k.1) k.2) u, glue ε (fun k => -Algebra.trace F E (β k.2 * y' k.1)) w, ?_⟩
    rw [hco, hx₁, huw, glue_map ε (algebraMap F (AF F)), glue_map ε (algebraMap F (AF F))]
    congr 2 <;> funext k
    · simp only [p, hy]
      show βA.repr ((1 : AF F) ⊗ₜ[F] y k.1) k.2 = _
      simp [βA, Algebra.TensorProduct.basis_repr_tmul]
    · simp only [q, hy']
      rw [map_neg, ← GlobalTheory.VacIndic.trace_inclR, map_mul (inclR (F := F) (AF F)), Algebra.TensorProduct.basis_apply]
      rfl
  have hδ : ∀ v, ∀ γ ∈ latAtV X W v, ∀ γ' ∈ latAtV X W v, ∀ θ : 𝓞 E,
      B.ψ (Tr (inclR (F := F) (AF F) (θ : E) * (b γ' ⬝ᵥ D γ))) = 1 := fun v γ hγ γ' hγ' θ => by
    obtain ⟨-, δ, h0, h1, h2, h3⟩ := hlat v γ hγ
    have := GlobalTheory.LatVacArith.psi_symp_latAtV σ B X W r s r' s' hB hX hW v θ 1 (by rw [map_one]; exact one_mem _) γ' hγ' δ h0
    rw [one_mul, symp, hH, h1, h2, h3] at this
    simpa [hTens] using this
  have hv : ∀ v, ∃ φa, Model.IsVac (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W) B.ψ v φa ∧ ∀ c, φa (glue ε 0 c) = M₁.vac v c := by
    intro v
    refine exists_isVac ε hX hW _ M₁ hr p q π hco v (fun γ hγ => (hlat v γ hγ).1) (fun γ hγ γ' hγ' => ?_)
      (fun θ hθ γ hγ => ?_) (hM₁.vac v)
    · have := hδ v γ hγ γ' hγ' (-1)
      rw [show ((-1 : 𝓞 E) : E) = -1 by simp, map_neg, map_one, neg_one_mul, map_neg] at this
      rw [hpq, this]
    · rw [← one_mul (B.ψ _ * B.ψ _), ← hδ v γ hγ γ hγ θ]
      simp only [← AddChar.map_add_eq_mul]
      congr 1
      have h1 : inclR (F := F) (AF F) (θ : E) + cA σ (inclR (F := F) (AF F) (θ : E)) = 1 := by
        rw [GlobalTheory.VacIndic.cA_inclR, ← map_add, hθ, map_one]
      have h2 : Tr (inclR (F := F) (AF F) (θ : E) * cA σ (b γ ⬝ᵥ D γ)) =
          Tr (b γ ⬝ᵥ D γ) - Tr (inclR (F := F) (AF F) (θ : E) * (b γ ⬝ᵥ D γ)) := by
        rw [← hTr, map_mul, cA_cA hB, ← map_sub, eq_sub_of_add_eq' h1, sub_mul, one_mul]
      have h3 : (⅟(2 : AF F)) * 2 = 1 := invOf_mul_self _
      show _ * Tr _ = _ + (_ + _ * Tr _)
      rw [hpq, hH, mul_add (inclR (F := F) (AF F) (θ : E)), mul_sub, map_add, map_sub, h2]
      generalize (⅟(2 : AF F)) = t at h3 ⊢
      linear_combination (Tr (inclR (F := F) (AF F) (θ : E) * (b γ ⬝ᵥ D γ))) * h3
  choose φa hφa hφb using hv
  let S : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v => Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let G : Pl F → Prop := fun v => Model.IsVac (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W) B.ψ v (S v) ∧
    M₁.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let Ma : Model σ X W := ⟨co, fun v => if G v then S v else φa v, M.μ, M.dom⟩
  obtain ⟨e, he⟩ := exists_isEvS ε B Ma M₁ p q π hco ι ι' I
    (fun z => ⟨funext fun k => by simp [p, (hj z).1], (hj z).2⟩)
    (fun u hu => ⟨funext fun k => by simp [p, (hI u hu).1], (hI u hu).2⟩) fun v c => by
      by_cases h : G v
      · show (if G v then S v else φa v) _ = _
        rw [if_pos h, h.2]
        refine Set.indicator_eq_indicator ⟨fun hx i => ?_, fun hx i => ?_⟩ rfl
        · simpa using hx (ε.symm (.inr i))
        · obtain ⟨i, rfl⟩ := ε.symm.surjective i
          rcases i with i | i
          · rw [glue_inl]; exact zero_mem _
          · rw [glue_inr]; exact hx i
      · show (if G v then S v else φa v) _ = _
        rw [if_neg h, hφb]
  refine ⟨ε, Ma, e, p, q, ⟨hr, fun v => ?_, ?_, hM.haar, hM.dom⟩, hco, fun z h => funext fun k => by simp [p, h],
    fun z h => funext fun k => by simp [q, h], he⟩
  · show Model.IsVac _ _ _ (if G v then S v else φa v)
    split_ifs with h
    · exact h.1
    · exact hφa v
  · filter_upwards [GlobalTheory.VacIndic.eventually_isVac_indicator B hB X W r s r' s' hX hW co hr, hM₁.std] with v h1 h2
    exact if_pos ⟨h1, h2⟩

end PositivityTheory.ThKF0
