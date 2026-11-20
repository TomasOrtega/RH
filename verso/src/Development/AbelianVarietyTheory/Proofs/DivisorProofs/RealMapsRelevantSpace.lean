import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanWeilOperatorTransportsHeisenbergLineDStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryCompatStatement

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.MajTransport

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Groups

variable {n : ℕ} {X : Spc F E n}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_mul (a b : UA σ X.J) : mat (a * b) = mat a * mat b := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_one : mat (1 : UA σ X.J) = 1 := rfl

/- English proof (translation)
Rewrite using `[← mat_mul, inv_mul_cancel, mat_one]`.
-/
theorem mat_inv_mul (a : UA σ X.J) : mat a⁻¹ * mat a = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

/- English proof (translation)
Rewrite using `[← mat_mul, mul_inv_cancel, mat_one]`.
-/
theorem mat_mul_inv (a : UA σ X.J) : mat a * mat a⁻¹ = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

/- English proof (translation)
Introduce `u hu`. Rewrite using `[smul_add, hy u hu, hz u hu, add_zero]`.
-/
theorem at_add {m p : Type} {y z : Matrix m p (AE F E)} (hy : At (evI F) y) (hz : At (evI F) z) :
    At (evI F) (y + z) := by
  intro u hu; rw [smul_add, hy u hu, hz u hu, add_zero]

/- English proof (translation)
Introduce `u hu`. Rewrite using `[smul_neg, hz u hu, neg_zero]`.
-/
theorem at_neg {m p : Type} {z : Matrix m p (AE F E)} (hz : At (evI F) z) : At (evI F) (-z) := by
  intro u hu; rw [smul_neg, hz u hu, neg_zero]

/- English proof (translation)
Introduce `u hu`. Rewrite using `[← Matrix.mul_smul, hz u hu, Matrix.mul_zero]`.
-/
theorem at_mul_left {m p q : Type} [Fintype p] (A : Matrix m p (AE F E)) {z : Matrix p q (AE F E)}
    (hz : At (evI F) z) : At (evI F) (A * z) := by
  intro u hu; rw [← Matrix.mul_smul, hz u hu, Matrix.mul_zero]

/- English proof (translation)
Introduce `u hu`. Rewrite using `[← Matrix.smul_mul, hz u hu, Matrix.zero_mul]`.
-/
theorem at_mul_right {m p q : Type} [Fintype p] {z : Matrix m p (AE F E)} (hz : At (evI F) z)
    (A : Matrix p q (AE F E)) : At (evI F) (z * A) := by
  intro u hu; rw [← Matrix.smul_mul, hz u hu, Matrix.zero_mul]

/- English proof (translation)
Establish `e : mat (a * b) - 1 = (mat a - 1) * mat b + (mat b - 1)` using `by rw [mat_mul]; noncomm_ring`. Use `show At (evI F) (mat (a * b) - 1)`. Rewrite using `[e]`. Conclude with `at_add (at_mul_right ha _) hb`.
-/
theorem uat_mul {a b : UA σ X.J} (ha : a ∈ UAt σ X (evI F)) (hb : b ∈ UAt σ X (evI F)) :
    a * b ∈ UAt σ X (evI F) := by
  have e : mat (a * b) - 1 = (mat a - 1) * mat b + (mat b - 1) := by rw [mat_mul]; noncomm_ring
  show At (evI F) (mat (a * b) - 1)
  rw [e]; exact at_add (at_mul_right ha _) hb

/- English proof (translation)
Establish `e : mat a⁻¹ - 1 = -(mat a⁻¹ * (mat a - 1))`. Rewrite using `[Matrix.mul_sub, mat_inv_mul, Matrix.mul_one]`. Normalize the expressions using the abelian group laws. Use `show At (evI F) (mat a⁻¹ - 1)`. Rewrite using `[e]`.

Conclude with `at_neg (at_mul_left _ ha)`.
-/
theorem uat_inv {a : UA σ X.J} (ha : a ∈ UAt σ X (evI F)) : a⁻¹ ∈ UAt σ X (evI F) := by
  have e : mat a⁻¹ - 1 = -(mat a⁻¹ * (mat a - 1)) := by
    rw [Matrix.mul_sub, mat_inv_mul, Matrix.mul_one]; abel
  show At (evI F) (mat a⁻¹ - 1)
  rw [e]; exact at_neg (at_mul_left _ ha)

/- English proof (translation)
The claim follows from `uat_mul (uat_mul ha hk) (uat_inv ha)`.
-/
theorem uat_conj {a k : UA σ X.J} (ha : a ∈ UAt σ X (evI F)) (hk : k ∈ UAt σ X (evI F)) :
    a * k * a⁻¹ ∈ UAt σ X (evI F) :=
  uat_mul (uat_mul ha hk) (uat_inv ha)

/- English proof (translation)
Set `e : UA σ X.J ≃* GAd σ ((1 : E) • X.J.map σ)` to `MulEquiv.subgroupCongr (GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := X.J) hσ (one_ne_zero : (1 : E) ≠ 0))`. Establish `he : Continuous e` using `continuous_subtype_val.subtype_mk _`. Establish `he' : Continuous e.symm` using `continuous_subtype_val.subtype_mk _`. Use `haveI : ContinuousMul (UA σ X.J) := ⟨by`. Establish `h3 : (fun p : UA σ X.J × UA σ X.J => p.1 * p.2) = fun p => e.symm (e p.1 * e p.2)`.

Use function extensionality and compare the values at `fun p => by rw [← map_mul, MulEquiv.symm_apply_apply]`. Rewrite using `[h3]`. Conclude with `he'.comp ((he.comp continuous_fst).mul (he.comp continuous_snd))⟩`. Use `⟨?_, fun t => ?_⟩` and prove the remaining obligations. Use `show Continuous fun t => a * γ t * a⁻¹`.

Conclude with `(continuous_const.mul hγ.1).mul continuous_const`. Conclude with `uat_conj ha (hγ.2 t)`.
-/
theorem lines_conj (hσ : ∀ x, σ (σ x) = x) {γ : Multiplicative ℝ →* UA σ X.J} (hγ : γ ∈ Lines σ X)
    {a : UA σ X.J} (ha : a ∈ UAt σ X (evI F)) : (MulAut.conj a).toMonoidHom.comp γ ∈ Lines σ X := by
  let e : UA σ X.J ≃* GAd σ ((1 : E) • X.J.map σ) :=
    MulEquiv.subgroupCongr (GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := X.J) hσ (one_ne_zero : (1 : E) ≠ 0))
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  haveI : ContinuousMul (UA σ X.J) := ⟨by
    have h3 : (fun p : UA σ X.J × UA σ X.J => p.1 * p.2) = fun p => e.symm (e p.1 * e p.2) :=
      funext fun p => by rw [← map_mul, MulEquiv.symm_apply_apply]
    rw [h3]
    exact he'.comp ((he.comp continuous_fst).mul (he.comp continuous_snd))⟩
  refine ⟨?_, fun t => ?_⟩
  · show Continuous fun t => a * γ t * a⁻¹
    exact (continuous_const.mul hγ.1).mul continuous_const
  · exact uat_conj ha (hγ.2 t)

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, mat_mul_inv, Matrix.map_one _ (map_zero π) (map_one π)]`.
-/
theorem map_mul_inv (π : AE F E →+* ℂ) (a : UA σ X.J) : (mat a).map π * (mat a⁻¹).map π = 1 := by
  rw [← Matrix.map_mul, mat_mul_inv, Matrix.map_one _ (map_zero π) (map_one π)]

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, mat_inv_mul, Matrix.map_one _ (map_zero π) (map_one π)]`.
-/
theorem map_inv_mul (π : AE F E →+* ℂ) (a : UA σ X.J) : (mat a⁻¹).map π * (mat a).map π = 1 := by
  rw [← Matrix.map_mul, mat_inv_mul, Matrix.map_one _ (map_zero π) (map_one π)]

end Groups

section Mat

variable {m : Type} [Fintype m] [DecidableEq m]

/- English proof (translation)
Establish `e : θ' = A * θ * A'` using `by rw [h, Matrix.mul_assoc, h1, Matrix.mul_one]`. Rewrite using `[e]`. Use `show A * K * A' * (A * θ * A') = A * θ * A' * (A * K * A')`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc A' A, h2, Matrix.one_mul]`. Use `_ = A * (θ * K) * A' := by rw [hk.eq]`. Use `_ = A * θ * A' * (A * K * A') := by`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc A' A, h2, Matrix.one_mul]`.
-/
theorem comm_conj {A A' K θ θ' : Matrix m m ℂ} (h1 : A * A' = 1) (h2 : A' * A = 1) (h : A * θ = θ' * A)
    (hk : Commute K θ) : Commute (A * K * A') θ' := by
  have e : θ' = A * θ * A' := by rw [h, Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [e]
  show A * K * A' * (A * θ * A') = A * θ * A' * (A * K * A')
  calc A * K * A' * (A * θ * A') = A * (K * θ) * A' := by
        simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc A' A, h2, Matrix.one_mul]
    _ = A * (θ * K) * A' := by rw [hk.eq]
    _ = A * θ * A' * (A * K * A') := by
        simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc A' A, h2, Matrix.one_mul]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem rev_conj {A A' θ θ' : Matrix m m ℂ} (h1 : A * A' = 1) (h2 : A' * A = 1) (h : A * θ = θ' * A) :
    A' * θ' = θ * A' := by
  calc A' * θ' = A' * θ' * (A * A') := by rw [h1, Matrix.mul_one]
    _ = A' * (θ' * A) * A' := by simp only [Matrix.mul_assoc]
    _ = (A' * A) * θ * A' := by rw [← h]; simp only [Matrix.mul_assoc]
    _ = θ * A' := by rw [h2, Matrix.one_mul]

end Mat

section KInf

variable {n : ℕ} {X Y : Spc F E n}

/- English proof (translation)
Use `⟨uat_conj ha hk.1, fun w => ?_⟩` and prove the remaining obligations. Use `show Commute ((mat (a * k * a⁻¹)).map (piInf (τ w))) (Y.θ w)`. Rewrite using `[mat_mul, mat_mul, Matrix.map_mul, Matrix.map_mul]`. Conclude with `comm_conj (map_mul_inv _ a) (map_inv_mul _ a) (hθ w) (hk.2 w)`.
-/
theorem kinf_conj (τ : ∀ w : InfinitePlace F, EmbOver E w) {a : UA σ X.J} (ha : a ∈ UAt σ X (evI F))
    (hθ : ∀ w, (mat a).map (piInf (τ w)) * X.θ w = Y.θ w * (mat a).map (piInf (τ w))) {k : UA σ X.J}
    (hk : k ∈ KInf σ X τ) : a * k * a⁻¹ ∈ KInf σ (reS X Y) τ := by
  refine ⟨uat_conj ha hk.1, fun w => ?_⟩
  show Commute ((mat (a * k * a⁻¹)).map (piInf (τ w))) (Y.θ w)
  rw [mat_mul, mat_mul, Matrix.map_mul, Matrix.map_mul]
  exact comm_conj (map_mul_inv _ a) (map_inv_mul _ a) (hθ w) (hk.2 w)

end KInf

section Acts

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

/- English proof (translation)
Introduce `x Φ hΦ` and use `(IsUWeilPair.isUSplitting h).pres x Φ hΦ`.
-/
theorem pres_of {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {χX χW : Chr F E} {om : Rep σ X W}
    (h : M.IsWeil ψ χX χW om) : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) :=
  fun x Φ hΦ => (IsUWeilPair.isUSplitting h).pres x Φ hΦ

/- English proof (translation)
Introduce `r hr`. Establish `e0 : om p⁻¹ (tens (evI F) (T f) r) = tens (evI F) f r`. Use `hT' (T f) r hr` as an intermediate fact. Rewrite `this` using `[LinearEquiv.symm_apply_apply]`. Then use the resulting hypothesis. Establish `hr0 : Rest (evI F) (⇑f) r` using `⟨hr.1, e0 ▸ pres _ _ hr.2⟩`.

Establish `e1` using `h r hr0`. Establish `hr1 : Rest (evI F) (⇑f₁) r` using `⟨hr.1, e1 ▸ pres _ _ hr0.2⟩`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e0, e1]`. Conclude with `hT f₁ r hr1`.
-/
theorem acts_conj {om : Rep σ X W}
    (pres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d))
    {p : UA σ X.J × UA σ W.J} {T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d)}
    (hT : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om p) f (T f))
    (hT' : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om p⁻¹) f (T.symm f))
    {q : UA σ X.J × UA σ W.J} {f f₁ : SInf F (Fin n × Fin d)} (h : Acts (evI F) (om q) f f₁) :
    Acts (evI F) (om (p * q * p⁻¹)) (T f) (T f₁) := by
  intro r hr
  have e0 : om p⁻¹ (tens (evI F) (T f) r) = tens (evI F) f r := by
    have := hT' (T f) r hr
    rwa [LinearEquiv.symm_apply_apply] at this
  have hr0 : Rest (evI F) (⇑f) r := ⟨hr.1, e0 ▸ pres _ _ hr.2⟩
  have e1 := h r hr0
  have hr1 : Rest (evI F) (⇑f₁) r := ⟨hr.1, e1 ▸ pres _ _ hr0.2⟩
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e0, e1]
  exact hT f₁ r hr1

end Acts

section Pol

variable {n d : ℕ} {X₁ X₂ : Spc F E n} {W₁ W₂ : Spc F E d}

/- English proof (translation)
The claim follows from `Submodule.mem_sInf.2 fun _ hN => hN.1 f₀ h`.
-/
theorem gauss_mem {M : Model σ X₁ W₁} {ψ : AddChar (AF F) ℂ} {τ : ∀ w : InfinitePlace F, EmbOver E w}
    {f₀ : SInf F (Fin n × Fin d)} (h : M.IsGauss ψ τ f₀) : f₀ ∈ M.Pol ψ τ :=
  Submodule.mem_sInf.2 fun _ hN => hN.1 f₀ h

/- English proof (translation)
The claim follows from `Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h`.
-/
theorem pol_stab {M : Model σ X₁ W₁} {ψ : AddChar (AF F) ℂ} {τ : ∀ w : InfinitePlace F, EmbOver E w} {u}
    (hu : At (evI F) u) {f f₁ : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol ψ τ)
    (h : ActsD (evI F) (M.heisLine ψ u) f f₁) : f₁ ∈ M.Pol ψ τ :=
  Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h

/- English proof (translation)
The claim follows from `sInf_le ⟨fun f₀ hf₀ => gauss_mem (hG f₀ hf₀), fun u hu f hf f₁ hf₁ => pol_stab (hAt u hu) hf (hD u hu f f₁ hf₁)⟩`.
-/
theorem pol_le (M₁ : Model σ X₁ W₁) (M₂ : Model σ X₂ W₂) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d))
    (φ : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (AE F E))
    (hAt : ∀ u, At (evI F) u → At (evI F) (φ u))
    (hD : ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M₁.heisLine ψ u) f f₁ →
      ActsD (evI F) (M₂.heisLine ψ (φ u)) (T f) (T f₁))
    (hG : ∀ f₀, M₁.IsGauss ψ τ f₀ → M₂.IsGauss ψ τ (T f₀)) :
    M₁.Pol ψ τ ≤ (M₂.Pol ψ τ).comap T :=
  sInf_le ⟨fun f₀ hf₀ => gauss_mem (hG f₀ hf₀),
    fun u hu f hf f₁ hf₁ => pol_stab (hAt u hu) hf (hD u hu f f₁ hf₁)⟩

/- English proof (translation)
Take `⟨ε, hε⟩` from `hf₀`. Use `⟨ε, fun u u' hu hu' huu f f' hf hf' => ?_⟩` and prove the remaining obligations. Establish `h1` using `hD u hu _ _ hf`. Establish `h2` using `hD u' hu' _ _ hf'`. Rewrite `h1`, `h2` using `[LinearEquiv.symm_apply_apply]`.

Establish `key` using `hε (A * u * C.transpose) (A * u' * C.transpose) (at_mul_right (at_mul_left _ hu) _) (at_mul_right (at_mul_left _ hu') _) (fun w => ?_) _ _ h1 h2`. Use `congrArg T key` as an intermediate fact. Simplify using `using this`. Establish `eA` using `hX w`. Establish `eC` using `hW w`.

Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, huu w, Matrix.transpose_map, Matrix.mul_smul, Matrix.smul_mul]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.transpose_mul]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = _ := by rw [eA, eC, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]`.
-/
theorem gauss_transport (M₁ : Model σ X₁ W₁) (M₂ : Model σ X₂ W₂) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d))
    (A : Matrix (Fin n) (Fin n) (AE F E)) (C : Matrix (Fin d) (Fin d) (AE F E))
    (hD : ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M₂.heisLine ψ u) f f₁ →
      ActsD (evI F) (M₁.heisLine ψ (A * u * C.transpose)) (T.symm f) (T.symm f₁))
    (hX : ∀ w, A.map (piInf (τ w)) * X₂.θ w = X₁.θ w * A.map (piInf (τ w)))
    (hW : ∀ w, C.map (piInf (τ w)) * W₂.θ w = W₁.θ w * C.map (piInf (τ w)))
    {f₀ : SInf F (Fin n × Fin d)} (hf₀ : M₁.IsGauss ψ τ f₀) : M₂.IsGauss ψ τ (T f₀) := by
  obtain ⟨ε, hε⟩ := hf₀
  refine ⟨ε, fun u u' hu hu' huu f f' hf hf' => ?_⟩
  have h1 := hD u hu _ _ hf
  have h2 := hD u' hu' _ _ hf'
  rw [LinearEquiv.symm_apply_apply] at h1 h2
  have key := hε (A * u * C.transpose) (A * u' * C.transpose) (at_mul_right (at_mul_left _ hu) _)
    (at_mul_right (at_mul_left _ hu') _) (fun w => ?_) _ _ h1 h2
  · have := congrArg T key
    simpa using this
  · have eA := hX w
    have eC := hW w
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, huu w, Matrix.transpose_map,
      Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    calc A.map (piInf (τ w)) * (X₂.θ w * u.map (piInf (τ w)) * (W₂.θ w).transpose) * (C.map (piInf (τ w))).transpose
        = (A.map (piInf (τ w)) * X₂.θ w) * u.map (piInf (τ w)) * (C.map (piInf (τ w)) * W₂.θ w).transpose := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [eA, eC, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]

end Pol

section Pair

variable {n d : ℕ} {X Y : Spc F E n} {W Z : Spc F E d}

def reM (M : Model σ X W) (Y : Spc F E n) (Z : Spc F E d) : Model σ (reS X Y) (reS W Z) :=
  ⟨M.co, M.vac, M.μ, M.dom⟩

/- English proof (translation)
Use `⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩` and prove the remaining obligations. Establish `hz0 : ∀ v i, evFin F v (z i) = 0` using `fun v i => by`. Establish `h` using `congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i`. Establish `h2 : (1 : Af F) * (z i).2 = 0` using `congrArg Prod.snd h`. Rewrite `h2` using `[one_mul]`.

Rewrite using `[evFin, AlgHom.comp_apply]`. Use `map_zero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)` and compare the differences between its conclusion and the goal. Conclude with `h2`. Simplify using `only [Pi.add_apply, map_add, hz0, add_zero]`.
-/
theorem rest_pure {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hSB : ∀ v, φ v ∈ SB (κ → Fv F v))
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    Rest (evI F) (⇑f) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) := by
  refine ⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
  have hz0 : ∀ v i, evFin F v (z i) = 0 := fun v i => by
    have h := congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i
    have h2 : (1 : Af F) * (z i).2 = 0 := congrArg Prod.snd h
    rw [one_mul] at h2
    rw [evFin, AlgHom.comp_apply]
    convert map_zero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)
    exact h2
  simp only [Pi.add_apply, map_add, hz0, add_zero]

/- English proof (translation)
Establish `hfw` using `GlobalTheory.T.archimedeanWeilOperator_transports_heisenbergLineDerivative F E σ B n d X W M χX χW om r s r' s' hB hX hW hM hw g hg h hh T hT1 hT2`. Establish `hbw` using `GlobalTheory.T.archimedeanWeilOperator_transports_heisenbergLineDerivative F E σ B n d X W M χX χW om r s r' s' hB hX hW hM hw g⁻¹ (uat_inv hg) h⁻¹ (uat_inv hh) T.symm hT2 (fun f => by simpa only [inv_inv, LinearEquiv.symm_symm] using hT1 f)`. Establish `hX' : ∀ w, (mat g⁻¹).map (piInf (B.emb w)) * Y.θ w = X.θ w * (mat g⁻¹).map (piInf (B.emb w))` using `fun w => rev_conj (map_mul_inv _ g) (map_inv_mul _ g) (hθX w)`. Establish `hW' : ∀ w, (mat h⁻¹).map (piInf (B.emb w)) * Z.θ w = W.θ w * (mat h⁻¹).map (piInf (B.emb w))` using `fun w => rev_conj (map_mul_inv _ h) (map_inv_mul _ h) (hθW w)`. Establish `le1 : M.Pol B.ψ B.emb ≤ ((reM M Y Z).Pol B.ψ B.emb).comap (T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d))` using `pol_le M (reM M Y Z) B.ψ B.emb T (fun u => mat g * u * (mat h).transpose) (fun u hu => at_mul_right (at_mul_left _ hu) _) hfw (fun f₀ hf₀ => gauss_transport M (reM M Y Z) B.ψ B.emb T (mat g⁻¹) (mat h⁻¹) hbw hX' hW' hf₀)`.

Establish `le2 : (reM M Y Z).Pol B.ψ B.emb ≤ (M.Pol B.ψ B.emb).comap (T.symm : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d))` using `pol_le (reM M Y Z) M B.ψ B.emb T.symm (fun u => mat g⁻¹ * u * (mat h⁻¹).transpose) (fun u hu => at_mul_right (at_mul_left _ hu) _) hbw (fun f₀ hf₀ => gauss_transport (reM M Y Z) M B.ψ B.emb T.symm (mat g) (mat h) (fun u hu f f₁ hf => hfw u hu f f₁ hf) hθX hθW hf₀)`. Use `le_antisymm (Submodule.map_le_iff_le_comap.2 le1) fun f' hf' => ⟨T.symm f', le2 hf', by simp⟩` and prove the remaining obligations.
-/
theorem pair_pol {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hM : M.IsGood B.ψ)
    (hw : M.IsWeil B.ψ χX χW om) {g : UA σ X.J} {h : UA σ W.J} (hg : g ∈ UAt σ X (evI F))
    (hh : h ∈ UAt σ W (evI F)) {T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d)}
    (hT1 : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f))
    (hT2 : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f))
    (hθX : ∀ w, (mat g).map (piInf (B.emb w)) * X.θ w = Y.θ w * (mat g).map (piInf (B.emb w)))
    (hθW : ∀ w, (mat h).map (piInf (B.emb w)) * W.θ w = Z.θ w * (mat h).map (piInf (B.emb w))) :
    (M.Pol B.ψ B.emb).map (T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) = (reM M Y Z).Pol B.ψ B.emb := by
  have hfw := GlobalTheory.T.archimedeanWeilOperator_transports_heisenbergLineDerivative F E σ B n d X W M χX χW om r s r' s' hB hX hW hM hw g hg h hh T hT1 hT2
  have hbw := GlobalTheory.T.archimedeanWeilOperator_transports_heisenbergLineDerivative F E σ B n d X W M χX χW om r s r' s' hB hX hW hM hw g⁻¹ (uat_inv hg) h⁻¹ (uat_inv hh) T.symm
    hT2 (fun f => by simpa only [inv_inv, LinearEquiv.symm_symm] using hT1 f)
  have hX' : ∀ w, (mat g⁻¹).map (piInf (B.emb w)) * Y.θ w = X.θ w * (mat g⁻¹).map (piInf (B.emb w)) :=
    fun w => rev_conj (map_mul_inv _ g) (map_inv_mul _ g) (hθX w)
  have hW' : ∀ w, (mat h⁻¹).map (piInf (B.emb w)) * Z.θ w = W.θ w * (mat h⁻¹).map (piInf (B.emb w)) :=
    fun w => rev_conj (map_mul_inv _ h) (map_inv_mul _ h) (hθW w)
  have le1 : M.Pol B.ψ B.emb ≤ ((reM M Y Z).Pol B.ψ B.emb).comap (T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) :=
    pol_le M (reM M Y Z) B.ψ B.emb T (fun u => mat g * u * (mat h).transpose)
      (fun u hu => at_mul_right (at_mul_left _ hu) _) hfw
      (fun f₀ hf₀ => gauss_transport M (reM M Y Z) B.ψ B.emb T (mat g⁻¹) (mat h⁻¹) hbw hX' hW' hf₀)
  have le2 : (reM M Y Z).Pol B.ψ B.emb ≤ (M.Pol B.ψ B.emb).comap (T.symm : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) :=
    pol_le (reM M Y Z) M B.ψ B.emb T.symm (fun u => mat g⁻¹ * u * (mat h⁻¹).transpose)
      (fun u hu => at_mul_right (at_mul_left _ hu) _) hbw
      (fun f₀ hf₀ => gauss_transport (reM M Y Z) M B.ψ B.emb T.symm (mat g) (mat h)
        (fun u hu f f₁ hf => hfw u hu f f₁ hf)
        hθX hθW hf₀)
  refine le_antisymm (Submodule.map_le_iff_le_comap.2 le1) fun f' hf' => ⟨T.symm f', le2 hf', by simp⟩

/- English proof (translation)
Establish `hpol` using `pair_pol hB hX hW hM hw hg hh hT1 hT2 hθX hθW`. Establish `memT : ∀ f ∈ M.Pol B.ψ B.emb, T f ∈ (reM M Y Z).Pol B.ψ B.emb` using `fun f hf => by`. Use `Submodule.mem_map_of_mem (f := (T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d))) hf` as an intermediate fact. Rewrite `this` using `[hpol]`. Conclude with `this`.

Use `⟨?_, fun γ hγ f hf f₁ hD => ?_, fun k hk f hf f₁ hA => ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.map_comp, hpol]`. Conclude with `hq.onto`. Conclude with `hq.lie _ (lines_conj hσ hγ hg) (T f) (memT f hf) (T f₁) (GlobalTheory.T.weil_representation_unitary_unique hKP F E σ B n d X W M χX χW om r s r' s' hB hX hW hM hw g hg h hh T hT1 hT2 γ hγ f hf f₁ hD)`. Establish `hA'` using `acts_conj (pres_of hw) hT1 hT2 hA`.

Establish `e : ((g, h) * (k, 1) * (g, h)⁻¹ : UA σ X.J × UA σ W.J) = (g * k * g⁻¹, 1)` using `Prod.ext rfl (by simp)`. Rewrite `hA'` using `[e]`. Conclude with `hq.cpt (g * k * g⁻¹) (kinf_conj B.emb hg hθX hk) (T f) (memT f hf) (T f₁) hA'`.
-/
theorem pair_quot (hKP : KP) (hσ : ∀ x, σ (σ x) = x) {B : Base F E} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} {r s r' s' : ℕ}
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hM : M.IsGood B.ψ)
    (hw : M.IsWeil B.ψ χX χW om) {g : UA σ X.J} {h : UA σ W.J} (hg : g ∈ UAt σ X (evI F))
    (hh : h ∈ UAt σ W (evI F)) {T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d)}
    (hT1 : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f))
    (hT2 : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f))
    (hθX : ∀ w, (mat g).map (piInf (B.emb w)) * X.θ w = Y.θ w * (mat g).map (piInf (B.emb w)))
    (hθW : ∀ w, (mat h).map (piInf (B.emb w)) * W.θ w = Z.θ w * (mat h).map (piInf (B.emb w)))
    {P : Type} [AddCommGroup P] [Module ℂ P] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    (hq : RealQuot B (reM M Y Z) om p) :
    RealQuot B M om (p ∘ₗ (T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d))) := by
  have hpol := pair_pol hB hX hW hM hw hg hh hT1 hT2 hθX hθW
  have memT : ∀ f ∈ M.Pol B.ψ B.emb, T f ∈ (reM M Y Z).Pol B.ψ B.emb := fun f hf => by
    have := Submodule.mem_map_of_mem (f := (T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d))) hf
    rw [hpol] at this; exact this
  refine ⟨?_, fun γ hγ f hf f₁ hD => ?_, fun k hk f hf f₁ hA => ?_⟩
  · rw [Submodule.map_comp, hpol]; exact hq.onto
  · exact hq.lie _ (lines_conj hσ hγ hg) (T f) (memT f hf) (T f₁)
      (GlobalTheory.T.weil_representation_unitary_unique hKP F E σ B n d X W M χX χW om r s r' s' hB hX hW hM hw g hg h hh T hT1 hT2 γ hγ f hf f₁ hD)
  · have hA' := acts_conj (pres_of hw) hT1 hT2 hA
    have e : ((g, h) * (k, 1) * (g, h)⁻¹ : UA σ X.J × UA σ W.J) = (g * k * g⁻¹, 1) := Prod.ext rfl (by simp)
    rw [e] at hA'
    exact hq.cpt (g * k * g⁻¹) (kinf_conj B.emb hg hθX hk) (T f) (memT f hf) (T f₁) hA'

end Pair

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B a a' G X om om' hT V V' W R₂ hT₂ hR₂ g hg g' hg' h hh hθ hθ' hθW`. Establish `hσ : ∀ x, σ (σ x) = x` using `GlobalTheory.SiegelSet.sigma_sigma hT.base.cm`. Take `⟨T, hT1, hT2⟩` from `GlobalTheory.T.weil_representation_unitary_equiv hKP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil g hg h hh`. Take `⟨T', hT1', hT2'⟩` from `GlobalTheory.T.weil_representation_unitary_equiv hKP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hT.base hT.geo.hV' hT.geo.hW hT.geo.hM' hT.weil' g' hg' h hh`. Establish `hT1s : ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (g⁻¹⁻¹, h⁻¹⁻¹)) f (T.symm.symm f)` using `fun f => by simpa only [inv_inv, LinearEquiv.symm_symm] using hT1 f`.

Establish `hpol` using `pair_pol (Y := V) (Z := W) hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil hg hh hT1 hT2 hθ hθW`. Establish `hpol'` using `pair_pol (Y := V') (Z := W) hT.base hT.geo.hV' hT.geo.hW hT.geo.hM' hT.weil' hg' hh hT1' hT2' hθ' hθW`. Establish `memT : ∀ f ∈ G.M.Pol B.ψ B.emb, T f ∈ (reG G V V' W).M.Pol B.ψ B.emb` using `fun f hf => by`. Use `Submodule.mem_map_of_mem (f := (T : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')))) hf` as an intermediate fact. Rewrite `this` using `[hpol]`.

Conclude with `this`. Establish `memT' : ∀ f ∈ G.M'.Pol B.ψ B.emb, T' f ∈ (reG G V V' W).M'.Pol B.ψ B.emb` using `fun f hf => by`. Use `Submodule.mem_map_of_mem (f := (T' : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')))) hf` as an intermediate fact. Rewrite `this` using `[hpol']`. Conclude with `this`.

Establish `memTs : ∀ f' ∈ (reG G V V' W).M.Pol B.ψ B.emb, T.symm f' ∈ G.M.Pol B.ψ B.emb` using `fun f' hf' => by`. Establish `hf'' : f' ∈ (G.M.Pol B.ψ B.emb).map (T : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')))`. Rewrite using `[hpol]`. Conclude with `hf'`. Take `⟨f, hf, rfl⟩` from `hf''`.

Simplify using `using hf`. Establish `hW' : ∀ w, (mat h⁻¹).map (piInf (B.emb w)) * W.θ w = G.W.θ w * (mat h⁻¹).map (piInf (B.emb w))` using `fun w => rev_conj (map_mul_inv _ h) (map_inv_mul _ h) (hθW w)`. Use `⟨⟨R₂.Pi, R₂.p ∘ₗ (T : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a'))), R₂.p' ∘ₗ (T' : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')))⟩, ⟨?_, ?_, ?_, ?_, hR₂.nontriv, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `pair_quot (Y := V) (Z := W) hKP hσ hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil hg hh hT1 hT2 hθ hθW R₂.p hR₂.quot`. Conclude with `pair_quot (Y := V') (Z := W) hKP hσ hT.base hT.geo.hV' hT.geo.hW hT.geo.hM' hT.weil' hg' hh hT1' hT2' hθ' hθW R₂.p' hR₂.quot'`.

Introduce `γ hγ f hf f' hf' f₁ f₁' hD hD' hpp`. Conclude with `hR₂.lie _ (lines_conj hσ hγ hh) (T f) (memT f hf) (T' f') (memT' f' hf') (T f₁) (T' f₁') (GlobalTheory.T.weil_representation_unitary_compat hKP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil g hg h hh T hT1 hT2 γ hγ f hf f₁ …`. Introduce `k hk f hf f' hf' f₁ f₁' hA hA' hpp`. Establish `e : ((g, h) * (1, k) * (g, h)⁻¹ : UA σ G.V.J × UA σ G.W.J) = (1, h * k * h⁻¹)` using `Prod.ext (by simp) rfl`. Establish `e' : ((g', h) * (1, k) * (g', h)⁻¹ : UA σ G.V'.J × UA σ G.W.J) = (1, h * k * h⁻¹)` using `Prod.ext (by simp) rfl`.

Establish `hB` using `acts_conj (pres_of hT.weil) hT1 hT2 hA`. Establish `hB'` using `acts_conj (pres_of hT.weil') hT1' hT2' hA'`. Rewrite `hB` using `[e]`. Rewrite `hB'` using `[e']`. Conclude with `hR₂.cpt (h * k * h⁻¹) (kinf_conj B.emb hh hθW hk) (T f) (memT f hf) (T' f') (memT' f' hf') (T f₁) (T' f₁') hB hB' hpp`.

Introduce `N hL hK`. Use `hR₂.irred N (fun γ' hγ' f' hf' f₁' hD hN => ?_) (fun k' hk' f' hf' f₁' hA hN => ?_)` and prove the remaining obligations. Establish `hD'` using `GlobalTheory.T.weil_representation_unitary_compat hKP F E σ B a (a + a') (reS G.V V) (reS G.W W) (reG G V V' W).M X.β (X.β / X.α) om _ _ _ _ hT₂.base hT₂.geo.hV hT₂.geo.hW hT₂.geo.hM hT₂.weil g⁻¹ (uat_inv hg) h⁻¹ (uat_inv hh) T.symm hT2 hT1s γ' hγ' f' hf' f₁' hD`. Establish `hN' : R₂.p (T (T.symm f')) ∈ N` using `by rwa [LinearEquiv.apply_symm_apply]`. Use `hL _ (lines_conj hσ hγ' (uat_inv hh)) (T.symm f') (memTs f' hf') (T.symm f₁') hD' hN'` as an intermediate fact.

Establish `this' : R₂.p (T (T.symm f₁')) ∈ N` using `this`. Rewrite `this'` using `[LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Establish `hB` using `acts_conj (pres_of hT.weil) hT2 hT1s hA`. Establish `hB' : Acts (evI F) (om (1, h⁻¹ * (id k' : UA σ G.W.J) * h⁻¹⁻¹)) (T.symm f') (T.symm f₁')`. Use `hB using 3` and compare the differences between its conclusion and the goal.

Conclude with `Prod.ext (by show (1 : UA σ G.V.J) = g⁻¹ * 1 * g⁻¹⁻¹; simp) rfl`. Establish `hN' : R₂.p (T (T.symm f')) ∈ N` using `by rwa [LinearEquiv.apply_symm_apply]`. Use `hK _ (kinf_conj (X := reS G.W W) (Y := G.W) B.emb (uat_inv hh) hW' hk') (T.symm f') (memTs f' hf') (T.symm f₁') hB' hN'` as an intermediate fact. Establish `this' : R₂.p (T (T.symm f₁')) ∈ N` using `this`. Rewrite `this'` using `[LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis.

Introduce and unpack `Rf Φ Φ' ⟨T₀, hT₀, m, m', f, φ, f', φ', hf, hf', hΦ, hΦ', hsum⟩`. Establish `hcof : ∀ᶠ v in cofinite, v ∉ T₀` using `T₀.finite_toSet.eventually_cofinite_notMem`. Use `⟨T₀, hT₀, m, m', fun i => T (f i), φ, fun j => T' (f' j), φ', fun i => ⟨memT _ (hf i).1, (hf i).2.1, (hf i).2.2⟩, fun j => ⟨memT' _ (hf' j).1, (hf' j).2.1, (hf' j).2.2⟩, ?_, ?_, hsum⟩` and prove the remaining obligations. Rewrite using `[hΦ, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Conclude with `hT1 (f i) _ (rest_pure (f i) (φ i) (hf i).2.1 ((hcof.and hT.geo.hM.std).mono fun v hv => ((hf i).2.2 v hv.1).trans hv.2))`. Rewrite using `[hΦ', map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Conclude with `hT1' (f' j) _ (rest_pure (f' j) (φ' j) (hf' j).2.1 ((hcof.and hT.geo.hM'.std).mono fun v hv => ((hf' j).2.2 v hv.1).trans hv.2))`.
-/
theorem transport : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (R₂ : RealMaps F a a'),
    IsTriple B (reG G V V' W) X om om' → IsRealMaps B (reG G V V' W) om om' R₂ →
    ∀ g ∈ UAt σ G.V (evI F), ∀ g' ∈ UAt σ G.V' (evI F), ∀ h ∈ UAt σ G.W (evI F),
    (∀ w, (mat g).map (piInf (B.emb w)) * G.V.θ w = V.θ w * (mat g).map (piInf (B.emb w))) →
    (∀ w, (mat g').map (piInf (B.emb w)) * G.V'.θ w = V'.θ w * (mat g').map (piInf (B.emb w))) →
    (∀ w, (mat h).map (piInf (B.emb w)) * G.W.θ w = W.θ w * (mat h).map (piInf (B.emb w))) →
    ∃ R₃ : RealMaps F a a', IsRealMaps B G om om' R₃ ∧ ∀ (Rf : FinMaps F a a') Φ Φ', PolMatch B G X R₃ Rf Φ Φ' →
        PolMatch B (reG G V V' W) X R₂ Rf (om (g, h) Φ) (om' (g', h) Φ') := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT V V' W R₂ hT₂ hR₂ g hg g' hg' h hh hθ hθ' hθW
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hT.base.cm
  obtain ⟨T, hT1, hT2⟩ := GlobalTheory.T.weil_representation_unitary_equiv hKP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hT.base hT.geo.hV
    hT.geo.hW hT.geo.hM hT.weil g hg h hh
  obtain ⟨T', hT1', hT2'⟩ := GlobalTheory.T.weil_representation_unitary_equiv hKP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hT.base
    hT.geo.hV' hT.geo.hW hT.geo.hM' hT.weil' g' hg' h hh
  have hT1s : ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (g⁻¹⁻¹, h⁻¹⁻¹)) f (T.symm.symm f) :=
    fun f => by simpa only [inv_inv, LinearEquiv.symm_symm] using hT1 f
  have hpol := pair_pol (Y := V) (Z := W) hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil hg hh hT1 hT2 hθ hθW
  have hpol' := pair_pol (Y := V') (Z := W) hT.base hT.geo.hV' hT.geo.hW hT.geo.hM' hT.weil' hg' hh hT1' hT2' hθ' hθW
  have memT : ∀ f ∈ G.M.Pol B.ψ B.emb, T f ∈ (reG G V V' W).M.Pol B.ψ B.emb := fun f hf => by
    have := Submodule.mem_map_of_mem (f := (T : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')))) hf
    rw [hpol] at this; exact this
  have memT' : ∀ f ∈ G.M'.Pol B.ψ B.emb, T' f ∈ (reG G V V' W).M'.Pol B.ψ B.emb := fun f hf => by
    have := Submodule.mem_map_of_mem (f := (T' : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')))) hf
    rw [hpol'] at this; exact this
  have memTs : ∀ f' ∈ (reG G V V' W).M.Pol B.ψ B.emb, T.symm f' ∈ G.M.Pol B.ψ B.emb := fun f' hf' => by
    have hf'' : f' ∈ (G.M.Pol B.ψ B.emb).map (T : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a'))) := by
      rw [hpol]; exact hf'
    obtain ⟨f, hf, rfl⟩ := hf''
    simpa using hf
  have hW' : ∀ w, (mat h⁻¹).map (piInf (B.emb w)) * W.θ w = G.W.θ w * (mat h⁻¹).map (piInf (B.emb w)) :=
    fun w => rev_conj (map_mul_inv _ h) (map_inv_mul _ h) (hθW w)
  refine ⟨⟨R₂.Pi, R₂.p ∘ₗ (T : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a'))),
    R₂.p' ∘ₗ (T' : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')))⟩,
    ⟨?_, ?_, ?_, ?_, hR₂.nontriv, ?_⟩, ?_⟩
  · exact pair_quot (Y := V) (Z := W) hKP hσ hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil hg hh hT1 hT2 hθ hθW
      R₂.p hR₂.quot
  · exact pair_quot (Y := V') (Z := W) hKP hσ hT.base hT.geo.hV' hT.geo.hW hT.geo.hM' hT.weil' hg' hh hT1' hT2' hθ'
      hθW R₂.p' hR₂.quot'
  · intro γ hγ f hf f' hf' f₁ f₁' hD hD' hpp
    exact hR₂.lie _ (lines_conj hσ hγ hh) (T f) (memT f hf) (T' f') (memT' f' hf') (T f₁) (T' f₁')
      (GlobalTheory.T.weil_representation_unitary_compat hKP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hT.base hT.geo.hV hT.geo.hW hT.geo.hM
        hT.weil g hg h hh T hT1 hT2 γ hγ f hf f₁ hD)
      (GlobalTheory.T.weil_representation_unitary_compat hKP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hT.base hT.geo.hV' hT.geo.hW
        hT.geo.hM' hT.weil' g' hg' h hh T' hT1' hT2' γ hγ f' hf' f₁' hD') hpp
  · intro k hk f hf f' hf' f₁ f₁' hA hA' hpp
    have e : ((g, h) * (1, k) * (g, h)⁻¹ : UA σ G.V.J × UA σ G.W.J) = (1, h * k * h⁻¹) := Prod.ext (by simp) rfl
    have e' : ((g', h) * (1, k) * (g', h)⁻¹ : UA σ G.V'.J × UA σ G.W.J) = (1, h * k * h⁻¹) := Prod.ext (by simp) rfl
    have hB := acts_conj (pres_of hT.weil) hT1 hT2 hA
    have hB' := acts_conj (pres_of hT.weil') hT1' hT2' hA'
    rw [e] at hB
    rw [e'] at hB'
    exact hR₂.cpt (h * k * h⁻¹) (kinf_conj B.emb hh hθW hk) (T f) (memT f hf) (T' f') (memT' f' hf') (T f₁) (T' f₁')
      hB hB' hpp
  · intro N hL hK
    refine hR₂.irred N (fun γ' hγ' f' hf' f₁' hD hN => ?_) (fun k' hk' f' hf' f₁' hA hN => ?_)
    · have hD' := GlobalTheory.T.weil_representation_unitary_compat hKP F E σ B a (a + a') (reS G.V V) (reS G.W W) (reG G V V' W).M X.β (X.β / X.α) om _ _ _ _
        hT₂.base hT₂.geo.hV hT₂.geo.hW hT₂.geo.hM hT₂.weil g⁻¹ (uat_inv hg) h⁻¹ (uat_inv hh) T.symm hT2 hT1s γ' hγ'
        f' hf' f₁' hD
      have hN' : R₂.p (T (T.symm f')) ∈ N := by rwa [LinearEquiv.apply_symm_apply]
      have := hL _ (lines_conj hσ hγ' (uat_inv hh)) (T.symm f') (memTs f' hf') (T.symm f₁') hD' hN'
      have this' : R₂.p (T (T.symm f₁')) ∈ N := this
      rwa [LinearEquiv.apply_symm_apply] at this'
    · have hB := acts_conj (pres_of hT.weil) hT2 hT1s hA
      have hB' : Acts (evI F) (om (1, h⁻¹ * (id k' : UA σ G.W.J) * h⁻¹⁻¹)) (T.symm f') (T.symm f₁') := by
        convert hB using 3
        exact Prod.ext (by show (1 : UA σ G.V.J) = g⁻¹ * 1 * g⁻¹⁻¹; simp) rfl
      have hN' : R₂.p (T (T.symm f')) ∈ N := by rwa [LinearEquiv.apply_symm_apply]
      have := hK _ (kinf_conj (X := reS G.W W) (Y := G.W) B.emb (uat_inv hh) hW' hk') (T.symm f') (memTs f' hf')
        (T.symm f₁') hB' hN'
      have this' : R₂.p (T (T.symm f₁')) ∈ N := this
      rwa [LinearEquiv.apply_symm_apply] at this'
  · rintro Rf Φ Φ' ⟨T₀, hT₀, m, m', f, φ, f', φ', hf, hf', hΦ, hΦ', hsum⟩
    have hcof : ∀ᶠ v in cofinite, v ∉ T₀ := T₀.finite_toSet.eventually_cofinite_notMem
    refine ⟨T₀, hT₀, m, m', fun i => T (f i), φ, fun j => T' (f' j), φ',
      fun i => ⟨memT _ (hf i).1, (hf i).2.1, (hf i).2.2⟩, fun j => ⟨memT' _ (hf' j).1, (hf' j).2.1, (hf' j).2.2⟩,
      ?_, ?_, hsum⟩
    · rw [hΦ, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact hT1 (f i) _ (rest_pure (f i) (φ i) (hf i).2.1
        ((hcof.and hT.geo.hM.std).mono fun v hv => ((hf i).2.2 v hv.1).trans hv.2))
    · rw [hΦ', map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact hT1' (f' j) _ (rest_pure (f' j) (φ' j) (hf' j).2.1
        ((hcof.and hT.geo.hM'.std).mono fun v hv => ((hf' j).2.2 v hv.1).trans hv.2))

end GlobalTheory.MajTransport
