import Development.WeilBound.ThetaLifts.LeviDeterminants.EqZeroOfTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOriginStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDoubledBlockDiagOneStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace PositivityTheory.ThKF0

def SiegelChar : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ε : ℤˣ), (∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) → J.det ≠ 0 → ∀ c : UG (cA σ) (dbl (incM F J)) →* ℂˣ, Continuous c → (∀ (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)), (p.1.1 : Matrix _ _ (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.1 → c p = 1) → c = 1

variable {F : Type} [Field F] [NumberField F]

open scoped Classical in

/- English proof (translation)
Introduce `g _`. Use `⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp', Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply, BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]`. Establish `h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0`. Use function extensionality and compare the values at `i`.

Conclude with `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)`. Establish `h2 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) = 0`. Use function extensionality and compare the values at `i`. Both sides reduce to the same expression. Rewrite using `[h1, h2, mul_comm]`.
-/
theorem evalZero_mem_adelicSchwartzAdmittedForms (κ : Type) [Fintype κ] :
    (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h2 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) = 0 := by
    funext i; rfl
  rw [h1, h2, mul_comm]

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Unfold `actB`. Rewrite using `[Matrix.mul_assoc, ← Matrix.transpose_mul]`. Establish `: ((↑(p⁻¹) : GL β E') : Matrix β β E') * ((p : GL β E') : Matrix β β E') = 1`. Rewrite using `[← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]`. Both sides reduce to the same expression.

Rewrite using `[this, Matrix.transpose_one, Matrix.mul_one]`.
-/
theorem actB_inv_actB {R E' : Type} [CommRing R] [CommRing E'] [Algebra R E'] {c : E' →ₐ[R] E'} {α β : Type}
    [Fintype β] [DecidableEq β] {J : Matrix β β E'} (p : UG c J) (x : Matrix α β E') :
    actB c p⁻¹ (actB c p x) = x := by
  unfold actB
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul]
  have : ((↑(p⁻¹) : GL β E') : Matrix β β E') * ((p : GL β E') : Matrix β β E') = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  rw [this, Matrix.transpose_one, Matrix.mul_one]

/- English proof (translation)
Unfold `Darboux.rho`. Rewrite using `[← h]`. Use `congr 2`. Use extensionality with `i j`. Apply the tactic sequence `rcases j with j | j <;> erw [Matrix.mul_apply] <;> simp [diagCols, Matrix.one_apply]`.
-/
theorem dd_rho_diag {a b : ℕ} {σ : E →ₐ[F] E} {JA : Matrix (Fin a) (Fin a) E} {JB : Matrix (Fin b) (Fin b) E} {κ : Type}
    [Fintype κ] {d : Darboux (symp (cA σ) (-1) (incM F JA) (incM F JB)) κ}
    {dd : Darboux (symp (cA σ) (-1) (incM F JA) (dbl (incM F JB))) (κ ⊕ κ)}
    (h : IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd) (ψ : AddChar (AF F) ℂ)
    (z : Matrix (Fin a) (Fin b) (AE F E)) :
    dd.rho ψ (z * (diagCols (Fin b))ᵀ) =
      schr ψ (Sum.elim (d.e z).1 (d.e z).1, Sum.elim (d.e z).2 (-(d.e z).2)) := by
  unfold Darboux.rho
  rw [← h]
  congr 2
  ext i j
  rcases j with j | j <;> erw [Matrix.mul_apply] <;> simp [diagCols, Matrix.one_apply]

/- English proof (translation)
Take `⟨hS0, dd, omd, hdd, ⟨-, hS, hR⟩, hres⟩` from `h`. Take `⟨-, dd₁, omd₁, hdd₁, ⟨-, hS₁, hR₁⟩, hres₁⟩` from `h₁`. Take `⟨ed, hd⟩` from `hT F ψ hψ _ _ _ dd dd₁`. Take `⟨ed₀, hd₀⟩` from `hT F ψ hψ _ _ _ dd₁ dd`. Take `⟨ed', hd', hl1, hl2⟩` from `hd.exists_inv hψ hd₀ (hr.dbl hdd hdd₁) (hr'.dbl hdd₁ hdd)`.

Establish `inv_mul : ∀ (p : UG (cA σ) (dbl (incM F JB))) φ, omd p (omd p⁻¹ φ) = φ` using `fun p φ => by`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Take `⟨φy, hφy, hφy0⟩` from `GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F (κ ⊕ κ)`. Take `⟨φz, hφz, hφz0⟩ : ∃ φ ∈ schA F (κ ⊕ κ), ed φ 0 ≠ 0` from `⟨ed' φy, hd'.maps _ hφy, by rwa [hl2 _ hφy]⟩`. Establish `hsp : ∀ p, ∀ φ ∈ schA F (κ ⊕ κ), omd p φ ∈ schA F (κ ⊕ κ)` using `fun p φ hφ => hS.pres p φ hφ`.

Establish `hsp₁ : ∀ p, ∀ φ ∈ schA F (κ ⊕ κ), omd₁ p φ ∈ schA F (κ ⊕ κ)` using `fun p φ hφ => hS₁.pres p φ hφ`. Establish `key : ∀ p, ∃ c : ℂ, ∀ φ ∈ schA F (κ ⊕ κ), omd₁ p (ed φ) = c • ed (omd p φ)` using `fun p => by`. Take `⟨c, hc⟩` from `schur hψ dd (omd p⁻¹ ∘ₗ ed' ∘ₗ omd₁ p ∘ₗ ed) (fun φ hφ => hsp _ _ (hd'.maps _ (hsp₁ _ _ (hd.maps φ hφ)))) (fun l hl => hd.adm _ (hS₁.adm p _ (hd'.adm _ (hS.adm p⁻¹ l hl)))) (fun w φ hφ => by`. Establish `m1` using `hd.maps φ hφ`. Establish `m2` using `hsp₁ p _ m1`.

Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[hd.Heisenberg₂ w φ hφ, hS₁.impl p w _ m1, hd'.Heisenberg₂ _ _ m2, hS.impl _ _ _ (hd'.maps _ m2), actB_inv_actB])`. Use `⟨c, fun φ hφ => ?_⟩` and prove the remaining obligations. Use `congrArg (fun x => ed (omd p x)) (hc φ hφ)` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, inv_mul, map_smul] at this`.

Rewrite `this` using `[hl2 _ (hsp₁ p _ (hd.maps φ hφ))]`. Then use the resulting hypothesis. Use `choose cf hcf using key`. Establish `huniq : ∀ p (c : ℂ), (∀ φ ∈ schA F (κ ⊕ κ), omd₁ p (ed φ) = c • ed (omd p φ)) → c = cf p` using `fun p c hc => by`. Establish `h1` using `hc _ (hsp p⁻¹ φz hφz)`. Rewrite `h1` using `[hcf p _ (hsp p⁻¹ φz hφz), inv_mul]`.

Establish `h2` using `congrFun h1 0`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at h2`. Conclude with `(mul_right_cancel₀ hφz0 h2).symm`. Establish `hmul : ∀ p q, cf (p * q) = cf p * cf q` using `fun p q => (huniq (p * q) _ fun φ hφ => by`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcf q φ hφ, map_smul, hcf p _ (hsp q φ hφ), smul_smul, mul_comm]).symm`.

Establish `hone : cf 1 = 1` using `(huniq 1 1 fun φ _ => by simp).symm`. Set `cM : UG (cA σ) (dbl (incM F JB)) →* ℂ` to `{ toFun := cf, map_one' := hone, map_mul' := hmul }`. Set `c` to `cM.toHomUnits`. Establish `hcv : ∀ p, ((c p : ℂˣ) : ℂ) = cf p` using `fun p => rfl`. Establish `hcont_cf : Continuous cf`.

Use `continuous_iff_continuousAt.2 fun p₀ => ?_` and prove the remaining obligations. Establish `hφ` using `hsp p₀⁻¹ φz hφz`. Establish `hf` using `hS.cont _ (hd.adm _ (evalZero_mem_adelicSchwartzAdmittedForms (κ ⊕ κ))) _ hφ`. Establish `hf₁` using `hS₁.cont _ (evalZero_mem_adelicSchwartzAdmittedForms (κ ⊕ κ)) _ (hd.maps _ hφ)`. Simplify using `only [LinearMap.comp_apply, LinearMap.proj_apply] at hf hf₁`.

Establish `h0 : ed (omd p₀ (omd p₀⁻¹ φz)) 0 ≠ 0` using `by rw [inv_mul]; exact hφz0`. Use `(hf₁.continuousAt.div hf.continuousAt h0).congr ?_` and prove the remaining obligations. Use `filter_upwards [hf.continuousAt.eventually_ne h0] with p hp`. Use `show omd₁ p _ 0 / ed (omd p _) 0 = cf p`. Rewrite using `[hcf p _ hφ]`.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Establish `hcont : Continuous c`. Use `Units.continuous_iff.2 ⟨hcont_cf, ?_⟩` and prove the remaining obligations. Establish `: (fun p => ((c p)⁻¹ : ℂˣ).val) = fun p => (cf p)⁻¹` using `funext fun p => by`.

Rewrite using `[Units.val_inv_eq_inv_val, hcv]`. Rewrite using `[this]`. Conclude with `hcont_cf.inv₀ fun p => by rw [← hcv]; exact (c p).ne_zero`. Take `⟨l, hl, hlinv, φ₀, hφ₀, hl0⟩` from `GlobalTheory.T.exists_diagonalLagrangian_invariant_form F ψ κ`. Establish `hinv₁ : ∀ z : Matrix (Fin a) (Fin b) (AE F E), ∀ φ ∈ schA F (κ ⊕ κ), l (dd₁.rho ψ (z * (diagCols (Fin b))ᵀ) φ) = l φ` using `fun z φ hφ => by rw [dd_rho_diag hdd₁ ψ z]; exact hlinv _ _ φ hφ`.

Establish `hP : ∀ (p : UG (cA σ) (dbl (incM F JB))) (t : GL (Fin b) (AE F E)), ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix _ _ (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * t.1 → c p = 1` using `fun p t hpt => by`. Establish `hφ` using `hsp p⁻¹ _ (hd'.maps φ₀ hφ₀)`. Establish `e1` using `hR (l ∘ₗ ed) (hd.adm l hl) (fun z φ hφ => by`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hd.Heisenberg₂ _ φ hφ]`. Conclude with `hinv₁ z _ (hd.maps φ hφ)) p t hpt _ hφ`.

Establish `e2` using `hR₁ l hl hinv₁ p t hpt _ (hd.maps _ hφ)`. Rewrite `e1` using `[LinearMap.comp_apply, LinearMap.comp_apply, ← e2, hcf p _ hφ, inv_mul, hl2 _ hφ₀, map_smul, smul_eq_mul]`. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[hcv, Units.val_one]`. Conclude with `mul_right_cancel₀ hl0 (by rw [one_mul]; exact e1.symm)`.

Establish `hc1` using `hC F E σ hσ b JB ε hJ hdet c hcont hP`. Establish `hcf1 : ∀ p, cf p = 1` using `fun p => by`. Rewrite using `[← hcv, hc1]`. Both sides reduce to the same expression. Introduce `g Φ hΦ`.

Take `⟨gd, hgd⟩` from `GlobalTheory.T.exists_unitaryDoubled_blockDiag_one (AF F) (AE F E) (cA σ) (Fin b) (incM F JB) g`. Take `⟨e₂, h₂, hbox⟩` from `box_compat hT hψ hr hdd hdd₁ he hd`. Take `⟨φ₂, hφ₂, hφ₂0⟩` from `h₂.ne`. Take `⟨y, hy⟩` from `Function.ne_iff.1 hφ₂0`. Establish `k` using `hcf gd _ (GlobalTheory.T.theta_sum_tensor_product F κ κ Φ hΦ φ₂ hφ₂).1`.

Rewrite `k` using `[hcf1 gd, one_smul, hres g gd hgd Φ hΦ φ₂ hφ₂, hbox Φ hΦ φ₂ hφ₂, hbox _ (hS0.pres g Φ hΦ) φ₂ hφ₂, hres₁ g gd hgd _ (he.maps Φ hΦ) _ (h₂.maps φ₂ hφ₂)]`. Use function extensionality and compare the values at `x`. Use `congrFun k (Sum.elim x y)` as an intermediate fact. Simplify using `only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr] at this`. Conclude with `(mul_right_cancel₀ hy this).symm`.
-/
theorem member_tw (hT : TwEx) (hC : SiegelChar) (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {a b : ℕ} (JA : Matrix (Fin a) (Fin a) E)
    (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ) (hJ : ∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) (hdet : JB.det ≠ 0)
    (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (d d₁ : Darboux (symp (cA σ) (-1) (incM F JA) (incM F JB)) κ) (hr : RatRel d d₁) (hr' : RatRel d₁ d) (χ : Chr F E)
    (om om₁ : UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ))
    (h : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d χ om)
    (h₁ : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d₁ χ om₁) {e} (he : Tw ψ d d₁ e) :
    ∀ g, ∀ Φ ∈ schA F κ, e (om g Φ) = om₁ g (e Φ) := by
  obtain ⟨hS0, dd, omd, hdd, ⟨-, hS, hR⟩, hres⟩ := h
  obtain ⟨-, dd₁, omd₁, hdd₁, ⟨-, hS₁, hR₁⟩, hres₁⟩ := h₁
  obtain ⟨ed, hd⟩ := hT F ψ hψ _ _ _ dd dd₁
  obtain ⟨ed₀, hd₀⟩ := hT F ψ hψ _ _ _ dd₁ dd
  obtain ⟨ed', hd', hl1, hl2⟩ := hd.exists_inv hψ hd₀ (hr.dbl hdd hdd₁) (hr'.dbl hdd₁ hdd)
  have inv_mul : ∀ (p : UG (cA σ) (dbl (incM F JB))) φ, omd p (omd p⁻¹ φ) = φ := fun p φ => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨φy, hφy, hφy0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F (κ ⊕ κ)
  obtain ⟨φz, hφz, hφz0⟩ : ∃ φ ∈ schA F (κ ⊕ κ), ed φ 0 ≠ 0 := ⟨ed' φy, hd'.maps _ hφy, by rwa [hl2 _ hφy]⟩
  have hsp : ∀ p, ∀ φ ∈ schA F (κ ⊕ κ), omd p φ ∈ schA F (κ ⊕ κ) := fun p φ hφ => hS.pres p φ hφ
  have hsp₁ : ∀ p, ∀ φ ∈ schA F (κ ⊕ κ), omd₁ p φ ∈ schA F (κ ⊕ κ) := fun p φ hφ => hS₁.pres p φ hφ
  have key : ∀ p, ∃ c : ℂ, ∀ φ ∈ schA F (κ ⊕ κ), omd₁ p (ed φ) = c • ed (omd p φ) := fun p => by
    obtain ⟨c, hc⟩ := schur hψ dd (omd p⁻¹ ∘ₗ ed' ∘ₗ omd₁ p ∘ₗ ed)
      (fun φ hφ => hsp _ _ (hd'.maps _ (hsp₁ _ _ (hd.maps φ hφ))))
      (fun l hl => hd.adm _ (hS₁.adm p _ (hd'.adm _ (hS.adm p⁻¹ l hl))))
      (fun w φ hφ => by
        have m1 := hd.maps φ hφ
        have m2 := hsp₁ p _ m1
        simp only [LinearMap.comp_apply]
        rw [hd.Heisenberg₂ w φ hφ, hS₁.impl p w _ m1, hd'.Heisenberg₂ _ _ m2, hS.impl _ _ _ (hd'.maps _ m2), actB_inv_actB])
    refine ⟨c, fun φ hφ => ?_⟩
    have := congrArg (fun x => ed (omd p x)) (hc φ hφ)
    simp only [LinearMap.comp_apply, inv_mul, map_smul] at this
    rwa [hl2 _ (hsp₁ p _ (hd.maps φ hφ))] at this
  choose cf hcf using key
  have huniq : ∀ p (c : ℂ), (∀ φ ∈ schA F (κ ⊕ κ), omd₁ p (ed φ) = c • ed (omd p φ)) → c = cf p := fun p c hc => by
    have h1 := hc _ (hsp p⁻¹ φz hφz)
    rw [hcf p _ (hsp p⁻¹ φz hφz), inv_mul] at h1
    have h2 := congrFun h1 0
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    exact (mul_right_cancel₀ hφz0 h2).symm
  have hmul : ∀ p q, cf (p * q) = cf p * cf q := fun p q => (huniq (p * q) _ fun φ hφ => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcf q φ hφ, map_smul,
      hcf p _ (hsp q φ hφ), smul_smul, mul_comm]).symm
  have hone : cf 1 = 1 := (huniq 1 1 fun φ _ => by simp).symm
  let cM : UG (cA σ) (dbl (incM F JB)) →* ℂ := { toFun := cf, map_one' := hone, map_mul' := hmul }
  let c := cM.toHomUnits
  have hcv : ∀ p, ((c p : ℂˣ) : ℂ) = cf p := fun p => rfl
  have hcont_cf : Continuous cf := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    have hφ := hsp p₀⁻¹ φz hφz
    have hf := hS.cont _ (hd.adm _ (evalZero_mem_adelicSchwartzAdmittedForms (κ ⊕ κ))) _ hφ
    have hf₁ := hS₁.cont _ (evalZero_mem_adelicSchwartzAdmittedForms (κ ⊕ κ)) _ (hd.maps _ hφ)
    simp only [LinearMap.comp_apply, LinearMap.proj_apply] at hf hf₁
    have h0 : ed (omd p₀ (omd p₀⁻¹ φz)) 0 ≠ 0 := by rw [inv_mul]; exact hφz0
    refine (hf₁.continuousAt.div hf.continuousAt h0).congr ?_
    filter_upwards [hf.continuousAt.eventually_ne h0] with p hp
    show omd₁ p _ 0 / ed (omd p _) 0 = cf p
    rw [hcf p _ hφ]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  have hcont : Continuous c := by
    refine Units.continuous_iff.2 ⟨hcont_cf, ?_⟩
    have : (fun p => ((c p)⁻¹ : ℂˣ).val) = fun p => (cf p)⁻¹ := funext fun p => by
      rw [Units.val_inv_eq_inv_val, hcv]
    rw [this]
    exact hcont_cf.inv₀ fun p => by rw [← hcv]; exact (c p).ne_zero
  obtain ⟨l, hl, hlinv, φ₀, hφ₀, hl0⟩ := GlobalTheory.T.exists_diagonalLagrangian_invariant_form F ψ κ
  have hinv₁ : ∀ z : Matrix (Fin a) (Fin b) (AE F E), ∀ φ ∈ schA F (κ ⊕ κ), l (dd₁.rho ψ (z * (diagCols (Fin b))ᵀ) φ) = l φ :=
    fun z φ hφ => by rw [dd_rho_diag hdd₁ ψ z]; exact hlinv _ _ φ hφ
  have hP : ∀ (p : UG (cA σ) (dbl (incM F JB))) (t : GL (Fin b) (AE F E)),
      ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix _ _ (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * t.1 →
        c p = 1 := fun p t hpt => by
    have hφ := hsp p⁻¹ _ (hd'.maps φ₀ hφ₀)
    have e1 := hR (l ∘ₗ ed) (hd.adm l hl) (fun z φ hφ => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hd.Heisenberg₂ _ φ hφ]
      exact hinv₁ z _ (hd.maps φ hφ)) p t hpt _ hφ
    have e2 := hR₁ l hl hinv₁ p t hpt _ (hd.maps _ hφ)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← e2, hcf p _ hφ, inv_mul, hl2 _ hφ₀, map_smul, smul_eq_mul] at e1
    refine Units.ext ?_
    rw [hcv, Units.val_one]
    exact mul_right_cancel₀ hl0 (by rw [one_mul]; exact e1.symm)
  have hc1 := hC F E σ hσ b JB ε hJ hdet c hcont hP
  have hcf1 : ∀ p, cf p = 1 := fun p => by
    rw [← hcv, hc1]; rfl
  intro g Φ hΦ
  obtain ⟨gd, hgd⟩ := GlobalTheory.T.exists_unitaryDoubled_blockDiag_one (AF F) (AE F E) (cA σ) (Fin b) (incM F JB) g
  obtain ⟨e₂, h₂, hbox⟩ := box_compat hT hψ hr hdd hdd₁ he hd
  obtain ⟨φ₂, hφ₂, hφ₂0⟩ := h₂.ne
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hφ₂0
  have k := hcf gd _ (GlobalTheory.T.theta_sum_tensor_product F κ κ Φ hΦ φ₂ hφ₂).1
  rw [hcf1 gd, one_smul, hres g gd hgd Φ hΦ φ₂ hφ₂, hbox Φ hΦ φ₂ hφ₂, hbox _ (hS0.pres g Φ hΦ) φ₂ hφ₂,
    hres₁ g gd hgd _ (he.maps Φ hΦ) _ (h₂.maps φ₂ hφ₂)] at k
  funext x
  have := congrFun k (Sum.elim x y)
  simp only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr] at this
  exact (mul_right_cancel₀ hy this).symm

/- English proof (translation)
Introduce `x Φ hΦ`. Take `⟨hB, ⟨d', hd', hA⟩, -⟩` from `h`. Take `⟨hB₁, ⟨d₁, hd₁, hA₁⟩, -⟩` from `h₁`. Establish `eW : ∀ i j, σ (W.J j i) = (((-1 : ℤˣ) : ℤ) : E) * W.J i j` using `fun i j => by simp [hW i j]`. Establish `eX : ∀ i j, σ (X.J j i) = (((1 : ℤˣ) : ℤ) : E) * X.J i j` using `fun i j => by simp [hX i j]`.

Establish `uB` using `member_tw hT hC σ hσ X.J W.J (-1) eW hWd ψ hψ M.co M₁.co hr hr' χX _ _ hB hB₁ he`. Establish `r1 : RatRel d' d₁` using `fun y z => by`. Take `⟨w, y', z', h1, h2⟩` from `hr y z`. Conclude with `⟨wᵀ, y', z', (hd' w).trans h1, (hd₁ w).trans h2⟩`. Establish `r2 : RatRel d₁ d'` using `fun y z => by`.

Take `⟨w, y', z', h1, h2⟩` from `hr' y z`. Conclude with `⟨wᵀ, y', z', (hd₁ w).trans h1, (hd' w).trans h2⟩`. Establish `he' : Tw ψ d' d₁ e` using `⟨he.maps, fun w Φ hΦ => by`. Use `he.Heisenberg₂ wᵀ Φ hΦ` as an intermediate fact. Rewrite `this` using `[Darboux.rho, Darboux.rho, ← hd', ← hd₁, Matrix.transpose_transpose]`.

Conclude with `this, he.adm, he.ne⟩`. Establish `uA` using `member_tw hT hC σ hσ W.J X.J 1 eX hXd ψ hψ d' d₁ r1 r2 χW _ _ hA hA₁ he'`. Establish `hx : x = (x.1, 1) * (1, x.2)` using `by simp`. Rewrite using `[hx, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]`. Establish `h1 : e (om (1, x.2) Φ) = om₁ (1, x.2) (e Φ)` using `uB x.2 Φ hΦ`.

Rewrite using `[← h1]`. Conclude with `uA x.1 _ (hB.1.pres x.2 Φ hΦ)`.
-/
theorem pair_tw (hT : TwEx) (hC : SiegelChar) (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
    (M M₁ : Model σ X W) {ψ : AddChar (AF F) ℂ} {χX χW : Chr F E} (hψ : IsStd ψ) (hX : ∀ i j, σ (X.J j i) = X.J i j)
    (hXd : X.J.det ≠ 0) (hW : ∀ i j, σ (W.J j i) = -W.J i j) (hWd : W.J.det ≠ 0) (hr : RatRel M.co M₁.co) (hr' : RatRel M₁.co M.co)
    {om om₁ : Rep σ X W} (h : M.IsWeil ψ χX χW om) (h₁ : M₁.IsWeil ψ χX χW om₁) {e} (he : Tw ψ M.co M₁.co e) :
    ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), e (om x Φ) = om₁ x (e Φ) := by
  intro x Φ hΦ
  obtain ⟨hB, ⟨d', hd', hA⟩, -⟩ := h
  obtain ⟨hB₁, ⟨d₁, hd₁, hA₁⟩, -⟩ := h₁
  have eW : ∀ i j, σ (W.J j i) = (((-1 : ℤˣ) : ℤ) : E) * W.J i j := fun i j => by simp [hW i j]
  have eX : ∀ i j, σ (X.J j i) = (((1 : ℤˣ) : ℤ) : E) * X.J i j := fun i j => by simp [hX i j]
  have uB := member_tw hT hC σ hσ X.J W.J (-1) eW hWd ψ hψ M.co M₁.co hr hr' χX _ _ hB hB₁ he
  have r1 : RatRel d' d₁ := fun y z => by
    obtain ⟨w, y', z', h1, h2⟩ := hr y z
    exact ⟨wᵀ, y', z', (hd' w).trans h1, (hd₁ w).trans h2⟩
  have r2 : RatRel d₁ d' := fun y z => by
    obtain ⟨w, y', z', h1, h2⟩ := hr' y z
    exact ⟨wᵀ, y', z', (hd₁ w).trans h1, (hd' w).trans h2⟩
  have he' : Tw ψ d' d₁ e := ⟨he.maps, fun w Φ hΦ => by
    have := he.Heisenberg₂ wᵀ Φ hΦ
    rw [Darboux.rho, Darboux.rho, ← hd', ← hd₁, Matrix.transpose_transpose] at this
    exact this, he.adm, he.ne⟩
  have uA := member_tw hT hC σ hσ W.J X.J 1 eX hXd ψ hψ d' d₁ r1 r2 χW _ _ hA hA₁ he'
  have hx : x = (x.1, 1) * (1, x.2) := by simp
  rw [hx, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  have h1 : e (om (1, x.2) Φ) = om₁ (1, x.2) (e Φ) := uB x.2 Φ hΦ
  rw [← h1]
  exact uA x.1 _ (hB.1.pres x.2 Φ hΦ)

end PositivityTheory.ThKF0

end
