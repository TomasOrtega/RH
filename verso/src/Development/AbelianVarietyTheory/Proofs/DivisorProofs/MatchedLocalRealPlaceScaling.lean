import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocType
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLatticeSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelCoinvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodPlaceInducedIntertwinerExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFactorizationAwayBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFactorizationBasePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantLocalFunctionalUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSchwartzStableUnderW

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.LocTypeGood

noncomputable section

namespace GlobalTheory.LocTypeDiffs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Use `set q := P.domRestrict S`. Establish `hs : Function.Surjective q` using `fun x => by`. Take `⟨y, hy, rfl⟩` from `onto x`. Conclude with `⟨⟨y, hy⟩, rfl⟩`. Establish `hker : LinearMap.ker q ≤ LinearMap.ker (L.domRestrict S)` using `fun x hx => ker x.1 x.2 hx`.

Set `T₀ : V →ₗ[ℂ] W` to `((LinearMap.ker q).liftQ (L.domRestrict S) hker).comp (q.quotKerEquivOfSurjective hs).symm.toLinearMap`. Establish `hT₀ : ∀ s ∈ S, T₀ (P s) = L s` using `fun s h => by`. Establish `: (q.quotKerEquivOfSurjective hs).symm (P s) = Submodule.Quotient.mk ⟨s, h⟩`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Both sides reduce to the same expression.

Simplify using `[T₀, this]`. Establish `hE : ∀ g, (T₀ ∘ₗ π d⁻¹) ∘ₗ π g = ρ g ∘ₗ (T₀ ∘ₗ π d⁻¹)` using `fun g => by`. Use extensionality with `x`. Take `⟨s, h, e⟩` from `onto (π d⁻¹ x)`. Take `⟨s₁, h₁, e₁, e₂⟩` from `eqv g s h`.

Establish `e₃ : π d⁻¹ (π g x) = P s₁`. Rewrite using `[e₁, e, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel_right]`. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[e₃, ← e, hT₀ _ h₁, hT₀ _ h, e₂]`. Introduce `s h`.

Use `Submodule.mem_iSup_of_mem (T₀ ∘ₗ π d⁻¹) (Submodule.mem_iSup_of_mem hE ⟨π d (P s), ?_⟩)` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, hT₀ _ h]`.
-/
theorem mem_imgSpan {Γ V W A : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup A] [Module ℂ A] (π : Representation ℂ Γ V) (ρ : Representation ℂ Γ W) (S : Submodule ℂ A)
    (P : A →ₗ[ℂ] V) (L : A →ₗ[ℂ] W) (d : Γ) (onto : ∀ f, ∃ s ∈ S, P s = f) (ker : ∀ s ∈ S, P s = 0 → L s = 0)
    (eqv : ∀ g, ∀ s ∈ S, ∃ s₁ ∈ S, P s₁ = π (d⁻¹ * g * d) (P s) ∧ L s₁ = ρ g (L s)) :
    ∀ s ∈ S, L s ∈ imgSpan π ρ := by
  set q := P.domRestrict S
  have hs : Function.Surjective q := fun x => by
    obtain ⟨y, hy, rfl⟩ := onto x
    exact ⟨⟨y, hy⟩, rfl⟩
  have hker : LinearMap.ker q ≤ LinearMap.ker (L.domRestrict S) := fun x hx => ker x.1 x.2 hx
  let T₀ : V →ₗ[ℂ] W :=
    ((LinearMap.ker q).liftQ (L.domRestrict S) hker).comp (q.quotKerEquivOfSurjective hs).symm.toLinearMap
  have hT₀ : ∀ s ∈ S, T₀ (P s) = L s := fun s h => by
    have : (q.quotKerEquivOfSurjective hs).symm (P s) = Submodule.Quotient.mk ⟨s, h⟩ := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp [T₀, this]
  have hE : ∀ g, (T₀ ∘ₗ π d⁻¹) ∘ₗ π g = ρ g ∘ₗ (T₀ ∘ₗ π d⁻¹) := fun g => by
    ext x
    obtain ⟨s, h, e⟩ := onto (π d⁻¹ x)
    obtain ⟨s₁, h₁, e₁, e₂⟩ := eqv g s h
    have e₃ : π d⁻¹ (π g x) = P s₁ := by
      rw [e₁, e, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel_right]
    simp only [LinearMap.comp_apply]
    rw [e₃, ← e, hT₀ _ h₁, hT₀ _ h, e₂]
  intro s h
  refine Submodule.mem_iSup_of_mem (T₀ ∘ₗ π d⁻¹) (Submodule.mem_iSup_of_mem hE ⟨π d (P s), ?_⟩)
  rw [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, hT₀ _ h]

/- English proof (translation)
Use `⟨⟨e.symm.toPEquiv.toMatrix, e.toPEquiv.toMatrix, ?_, ?_⟩, fun g => Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[PEquiv.toMatrix_toPEquiv_mul, ← PEquiv.toMatrix_toPEquiv_mul, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]`. Simplify using the standard rewrite rules. Rewrite using `[← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]`. Simplify using the standard rewrite rules.

Use `show (g : Matrix n n k).submatrix e.symm e.symm = e.symm.toPEquiv.toMatrix * (g : Matrix n n k) * e.toPEquiv.toMatrix`. Rewrite using `[PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]`. Both sides reduce to the same expression.
-/
theorem glReindex_conj {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (e : n ≃ n) :
    ∃ q : GL n k, ∀ g, glReindex e g = q * g * q⁻¹ := by
  refine ⟨⟨e.symm.toPEquiv.toMatrix, e.toPEquiv.toMatrix, ?_, ?_⟩, fun g => Units.ext ?_⟩
  · rw [PEquiv.toMatrix_toPEquiv_mul, ← PEquiv.toMatrix_toPEquiv_mul, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
    simp
  · rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
    simp
  · show (g : Matrix n n k).submatrix e.symm e.symm = e.symm.toPEquiv.toMatrix * (g : Matrix n n k) * e.toPEquiv.toMatrix
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    rfl

/- English proof (translation)
Establish `h : ∀ χ χ', χ = χ' → imgSpan (GlobalTheory.SmGL.parInd (GlobalTheory.ThK.MidJac.e2 a a') (GlobalTheory.SmGL.ofChar χ)) ρ = imgSpan (GlobalTheory.SmGL.parInd (GlobalTheory.ThK.MidJac.e2 a a') (GlobalTheory.SmGL.ofChar χ')) ρ`. Introduce and unpack `_ _ rfl`. Both sides reduce to the same expression. Conclude with `h _ _ (by`. Unfold `GlobalTheory.ThK.DetProd.twoDet GlobalTheory.LeviBlockExponent.pairChar`.

Rewrite using `[Fin.prod_univ_two]`. Use the proof step `rfl)`.
-/
theorem imgSpan_detInd {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GL (Fin (a + a')) k) W) :
    imgSpan (GlobalTheory.ThK.MidJac.detInd a a' χ₁ χ₂) ρ = imgSpan (GlobalTheory.JacLineSplit.indAA k a a' ![χ₁, χ₂]) ρ := by
  have h : ∀ χ χ', χ = χ' → imgSpan (GlobalTheory.SmGL.parInd (GlobalTheory.ThK.MidJac.e2 a a') (GlobalTheory.SmGL.ofChar χ)) ρ =
      imgSpan (GlobalTheory.SmGL.parInd (GlobalTheory.ThK.MidJac.e2 a a') (GlobalTheory.SmGL.ofChar χ')) ρ := by
    rintro _ _ rfl; rfl
  exact h _ _ (by
    unfold GlobalTheory.ThK.DetProd.twoDet GlobalTheory.LeviBlockExponent.pairChar
    rw [Fin.prod_univ_two]
    rfl)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def tensAt {κ : Type} (v : Pl F) (r : (κ → AF F) → ℂ) : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun φ := tens (evFin F v) φ r
  map_add' φ ψ := by funext x; simp only [tens, Pi.add_apply]; ring
  map_smul' c φ := by funext x; simp only [tens, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

section Pair

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

/- English proof (translation)
Use function extensionality and compare the values at `h`. Unfold `Model.I theta`. Use `congr 1`. Use function extensionality and compare the values at `g`. Rewrite using `[← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]`.
-/
theorem I_right (M : Model σ X W) (om : Rep σ X W) (Φ : (Fin n × Fin d → AF F) → ℂ) (k : UA σ W.J) :
    M.I om (om (1, k) Φ) = fun h => M.I om Φ (h * k) := by
  funext h
  unfold Model.I theta
  congr 1
  funext g
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

/- English proof (translation)
Set `ℓ₀ : N →ₗ[ℂ] (UA σ W.J → ℂ)` to `{ toFun := fun Φ => M.I om Φ.1 map_add' := fun Φ₁ Φ₂ => by`. Use function extensionality and compare the values at `h`. Establish `e : ∀ g, theta om (Φ₁.1 + Φ₂.1) g h = theta om Φ₁.1 g h + theta om Φ₂.1 g h` using `fun g => by`. Unfold `theta thetaSum`. Rewrite using `[map_add]`.

Conclude with `(summable_of_mem_schA F (hpres _ _ (hN Φ₁.2))).tsum_add (summable_of_mem_schA F (hpres _ _ (hN Φ₂.2)))`. Simplify using `only [Submodule.coe_add, Pi.add_apply, Model.I, e]`. Conclude with `integral_add (hconv _ Φ₁.2 h) (hconv _ Φ₂.2 h)`. Use the proof step `map_smul' := fun c Φ => by`. Use function extensionality and compare the values at `h`.

Establish `e : ∀ g, theta om (c • Φ.1) g h = c * theta om Φ.1 g h` using `fun g => by`. Unfold `theta thetaSum`. Rewrite using `[map_smul]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Conclude with `tsum_mul_left`.

Simplify using `only [Submodule.coe_smul, Pi.smul_apply, Model.I, e, RingHom.id_apply, smul_eq_mul]`. Conclude with `integral_const_mul c _ }`. Take `⟨ℓ, hℓ⟩` from `LinearMap.exists_extend ℓ₀`. Conclude with `⟨ℓ, fun Φ hΦ => LinearMap.congr_fun hℓ ⟨Φ, hΦ⟩⟩`.
-/
theorem exists_linear_I (M : Model σ X W) (om : Rep σ X W)
    (hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d))
    (N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) (hN : N ≤ schA F (Fin n × Fin d)) (hconv : ∀ Φ ∈ N, M.Conv om Φ) :
    ∃ ℓ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] (UA σ W.J → ℂ), ∀ Φ ∈ N, ℓ Φ = M.I om Φ := by
  let ℓ₀ : N →ₗ[ℂ] (UA σ W.J → ℂ) :=
    { toFun := fun Φ => M.I om Φ.1
      map_add' := fun Φ₁ Φ₂ => by
        funext h
        have e : ∀ g, theta om (Φ₁.1 + Φ₂.1) g h = theta om Φ₁.1 g h + theta om Φ₂.1 g h := fun g => by
          unfold theta thetaSum
          rw [map_add]
          exact (summable_of_mem_schA F (hpres _ _ (hN Φ₁.2))).tsum_add (summable_of_mem_schA F (hpres _ _ (hN Φ₂.2)))
        simp only [Submodule.coe_add, Pi.add_apply, Model.I, e]
        exact integral_add (hconv _ Φ₁.2 h) (hconv _ Φ₂.2 h)
      map_smul' := fun c Φ => by
        funext h
        have e : ∀ g, theta om (c • Φ.1) g h = c * theta om Φ.1 g h := fun g => by
          unfold theta thetaSum
          rw [map_smul]
          simp only [Pi.smul_apply, smul_eq_mul]
          exact tsum_mul_left
        simp only [Submodule.coe_smul, Pi.smul_apply, Model.I, e, RingHom.id_apply, smul_eq_mul]
        exact integral_const_mul c _ }
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
  exact ⟨ℓ, fun Φ hΦ => LinearMap.congr_fun hℓ ⟨Φ, hΦ⟩⟩

/- English proof (translation)
Introduce `c _` and use `by simp [mat]`.
-/
theorem one_mem_UAt (v : Pl F) : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := fun c _ => by simp [mat]

/- English proof (translation)
Take `⟨T, m, f, φ, hSB, hstd, hsum⟩` from `GlobalTheory.SchADecomp.exists_sum_pure F _ Ψ hΨ`. Establish `hev : ∀ i, ∀ᶠ w in Filter.cofinite, φ i w = Set.indicator {x | ∀ j, x j ∈ w.adicCompletionIntegers F} 1` using `fun i => (T.finite_toSet.eventually_cofinite_notMem).mono fun w hw => hstd i w hw`. Use `choose r hr1 hr2 using fun i => GlobalTheory.PureFactor.exists_rest_factor v (f i) (φ i) (hev i)`. Use `⟨m, fun i => φ i v, r, fun i => hSB i v, fun i φ' hφ' => ⟨hr1 i, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hr2 i]`.

Use `GlobalTheory.TensUniq.pure_mem_schA (f i) _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually _ v φ' (hev i))` and prove the remaining obligations. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `hφ'`.

Rewrite using `[Function.update_of_ne hw]`. Conclude with `hSB i w`. Rewrite using `[hsum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hr2 i, Function.update_eq_self]`.
-/
theorem exists_sum_tens {κ : Type} [Fintype κ] (v : Pl F) (Ψ : (κ → AF F) → ℂ) (hΨ : Ψ ∈ schA F κ) :
    ∃ (m : ℕ) (ψ : Fin m → (κ → Fv F v) → ℂ) (r : Fin m → (κ → AF F) → ℂ), (∀ i, ψ i ∈ SB (κ → Fv F v)) ∧
      (∀ i, ∀ φ ∈ SB (κ → Fv F v), Rest (evFin F v) φ (r i)) ∧ Ψ = ∑ i, tens (evFin F v) (ψ i) (r i) := by
  classical
  obtain ⟨T, m, f, φ, hSB, hstd, hsum⟩ := GlobalTheory.SchADecomp.exists_sum_pure F _ Ψ hΨ
  have hev : ∀ i, ∀ᶠ w in Filter.cofinite, φ i w = Set.indicator {x | ∀ j, x j ∈ w.adicCompletionIntegers F} 1 :=
    fun i => (T.finite_toSet.eventually_cofinite_notMem).mono fun w hw => hstd i w hw
  choose r hr1 hr2 using fun i => GlobalTheory.PureFactor.exists_rest_factor v (f i) (φ i) (hev i)
  refine ⟨m, fun i => φ i v, r, fun i => hSB i v, fun i φ' hφ' => ⟨hr1 i, ?_⟩, ?_⟩
  · rw [hr2 i]
    refine GlobalTheory.TensUniq.pure_mem_schA (f i) _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually _ v φ' (hev i))
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ'
    · rw [Function.update_of_ne hw]; exact hSB i w
  · rw [hsum]
    exact Finset.sum_congr rfl fun i _ => by rw [hr2 i, Function.update_eq_self]

end Pair

variable {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'} {v : Pl F} {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Introduce `Ψ hΨ`. Establish `hp` using `GlobalTheory.ThK.Inhab.pairV hT`. Establish `hAE` using `(GlobalTheory.T.theta_action_exists hK.base F E σ B _ _ _ _ _ _ _ om _ _ _ _ hp v).1 1 (one_mem_UAt v)`. Take `⟨ℓ, hℓ⟩` from `exists_linear_I G.M om (fun x Φ h => hp.weil.isUSplitting.pres x Φ h) _ le_rfl (GlobalTheory.T.theta_kernel_decay hK F E σ B a a' G X om om' hT).1`. Take `⟨m, ψ, r, hψ, hr, rfl⟩` from `exists_sum_tens v Ψ hΨ`.

Rewrite using `[← hℓ _ hΨ, map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `hL : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), (ℓ ∘ₗ tensAt v (r i)) φ = G.M.I om (tens (evFin F v) φ (r i))` using `fun φ h => hℓ _ (hr i φ h).2`. Use `mem_imgSpan π _ (SB _) P (ℓ ∘ₗ tensAt v (r i)) d onto (fun φ h h0 => ?_) (fun g φ h => ?_) _ (hψ i)` and prove the remaining obligations. Establish `hle : augAt om v ≤ LinearMap.ker (ℓ ∘ₗ tensAt v (r i))`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g', hg', φ, hφ, φ₁, hφ₁, hA, rfl⟩`. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero, hL _ hφ₁, hL _ hφ, ← hA (r i) (hr i φ hφ), GlobalTheory.ThetaIntegralInv.integral_translate hK.base hp g' _ (hr i φ hφ).2]`. Conclude with `hle (ker φ h h0)`. Take `⟨φ₁, h₁, hA⟩` from `(hAE (j g) (loc g) φ h).exists`.

Use `⟨φ₁, h₁, eqv g φ h φ₁ h₁ hA, ?_⟩` and prove the remaining obligations. Rewrite using `[hL _ h₁, hL _ h, ← hA (r i) (hr i φ h), I_right]`. Both sides reduce to the same expression.
-/
theorem big_mem (hK : KP) (hT : IsTriple B G X om om') (π : Representation ℂ Γ V) (j : Γ →* UA σ G.W.J)
    (P : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] V) (d : Γ) (loc : ∀ g, j g ∈ UAt σ G.W (evFin F v))
    (onto : ∀ f, ∃ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), P φ = f)
    (ker : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), P φ = 0 → φ ∈ augAt om v)
    (eqv : ∀ g, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, j g)) φ φ₁ → P φ₁ = π (d⁻¹ * g * d) (P φ)) :
    ∀ Ψ ∈ schA F (Fin a × Fin (a + a')), G.M.I om Ψ ∈ imgSpan π ((GlobalTheory.PRep.rightReg ℂ (UA σ G.W.J) ℂ).comp j) := by
  intro Ψ hΨ
  have hp := GlobalTheory.ThK.Inhab.pairV hT
  have hAE := (GlobalTheory.T.theta_action_exists hK.base F E σ B _ _ _ _ _ _ _ om _ _ _ _ hp v).1 1 (one_mem_UAt v)
  obtain ⟨ℓ, hℓ⟩ := exists_linear_I G.M om (fun x Φ h => hp.weil.isUSplitting.pres x Φ h) _ le_rfl
    (GlobalTheory.T.theta_kernel_decay hK F E σ B a a' G X om om' hT).1
  obtain ⟨m, ψ, r, hψ, hr, rfl⟩ := exists_sum_tens v Ψ hΨ
  rw [← hℓ _ hΨ, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hL : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), (ℓ ∘ₗ tensAt v (r i)) φ = G.M.I om (tens (evFin F v) φ (r i)) :=
    fun φ h => hℓ _ (hr i φ h).2
  refine mem_imgSpan π _ (SB _) P (ℓ ∘ₗ tensAt v (r i)) d onto (fun φ h h0 => ?_) (fun g φ h => ?_) _ (hψ i)
  · have hle : augAt om v ≤ LinearMap.ker (ℓ ∘ₗ tensAt v (r i)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g', hg', φ, hφ, φ₁, hφ₁, hA, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero, hL _ hφ₁, hL _ hφ, ← hA (r i) (hr i φ hφ),
        GlobalTheory.ThetaIntegralInv.integral_translate hK.base hp g' _ (hr i φ hφ).2]
    exact hle (ker φ h h0)
  · obtain ⟨φ₁, h₁, hA⟩ := (hAE (j g) (loc g) φ h).exists
    refine ⟨φ₁, h₁, eqv g φ h φ₁ h₁ hA, ?_⟩
    rw [hL _ h₁, hL _ h, ← hA (r i) (hr i φ h), I_right]
    rfl

/- English proof (translation)
Establish `hT` using `hM.triple`. Establish `hAE` using `(GlobalTheory.T.theta_action_exists hK.base F E σ B _ _ _ _ _ _ _ om _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hT) v).1 1 (one_mem_UAt v)`. Establish `hAE'` using `(GlobalTheory.T.theta_action_exists hK.base F E σ B _ _ _ _ _ _ _ om' _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hT) v).1 1 (one_mem_UAt v)`. Establish `hk` using `((GlobalTheory.T.theta_kernel_coinvariant hK.base F E σ B a a' G X om om' R Rf hM).1 v hv).2.1`. Set `S : Submodule ℂ (((Fin a × Fin (a + a') → Fv F v) → ℂ) × ((Fin a' × Fin (a + a') → Fv F v) → ℂ))` to `(SB _).prod (SB _) ⊓ LinearMap.ker (Rf.p v ∘ₗ LinearMap.fst ℂ _ _ - Rf.p' v ∘ₗ LinearMap.snd ℂ _ _)`.

Establish `hSm : ∀ s, s ∈ S ↔ s.1 ∈ SB _ ∧ s.2 ∈ SB _ ∧ Rf.p v s.1 = Rf.p' v s.2` using `fun s => by`. Simplify using `only [S, Submodule.mem_inf, Submodule.mem_prod, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, sub_eq_zero, and_assoc]`. Introduce `φ' hφ'`. Take `⟨φ, hφ, e⟩ : Rf.p' v φ' ∈ (SB _).map (Rf.p v)` from `hM.fin.onto v ▸ Submodule.mem_top`. Use `mem_imgSpan π _ S (P ∘ₗ LinearMap.fst ℂ _ _) (L ∘ₗ LinearMap.snd ℂ _ _) d (fun f => ?_) (fun s hs h0 => ?_) (fun g s hs => ?_) (φ, φ') ((hSm _).2 ⟨hφ, hφ', e⟩)` and prove the remaining obligations.

Take `⟨ψ, hψ, rfl⟩` from `onto f`. Take `⟨ψ', hψ', e'⟩` from `hon (Rf.p v ψ)`. Conclude with `⟨(ψ, ψ'), (hSm _).2 ⟨hψ, hS _ hψ', e'.symm⟩, rfl⟩`. Take `⟨h1, h2, h3⟩` from `(hSm s).1 hs`. Establish `h4 : Rf.p v s.1 = 0` using `hM.fin.inv v (ker s.1 h1 h0)`.

Conclude with `haug ((hk s.2 h2).1 (h3.symm.trans h4))`. Take `⟨h1, h2, h3⟩` from `(hSm s).1 hs`. Take `⟨ψ', hψ', e'⟩` from `hon (Rf.p' v s.2)`. Establish `e₀ : L s.2 = L ψ'`. Use `haug ((hk _ (sub_mem h2 (hS _ hψ'))).1 (by rw [map_sub, e', sub_self]))` as an intermediate fact.

Rewrite `this` using `[LinearMap.mem_ker, map_sub, sub_eq_zero]`. Then use the resulting hypothesis. Take `⟨φ₁, h₁, hA⟩` from `(hAE (j g) (loc g) s.1 h1).exists`. Take `⟨φ₁', h₁', hA'⟩` from `(hAE' (j g) (loc g) ψ' (hS _ hψ')).exists`. Use `⟨(φ₁, φ₁'), (hSm _).2 ⟨h₁, h₁', hM.fin.equiv v _ (loc g) _ h1 _ (hS _ hψ') _ h₁ _ h₁' hA hA' (h3.trans e'.symm)⟩, eqv g _ h1 _ h₁ hA, ?_⟩` and prove the remaining obligations. Use `show L φ₁' = (GlobalTheory.PRep.rightReg ℂ (UA σ G.W.J) ℂ).comp j g (L s.2)`.

Rewrite using `[hL g ψ' hψ' φ₁' h₁' hA', e₀]`. Both sides reduce to the same expression.
-/
theorem small_loc (hK : KP) (hM : IsMatched B G X om om' R Rf) (hv : X.Good v) (π : Representation ℂ Γ V) (j : Γ →* UA σ G.W.J)
    (P : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] V) (d : Γ) (loc : ∀ g, j g ∈ UAt σ G.W (evFin F v))
    (onto : ∀ f, ∃ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), P φ = f)
    (ker : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), P φ = 0 → φ ∈ augAt om v)
    (eqv : ∀ g, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, j g)) φ φ₁ → P φ₁ = π (d⁻¹ * g * d) (P φ))
    (L : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (UA σ G.W.J → ℂ)) (haug : augAt om' v ≤ LinearMap.ker L)
    (S₀ : Set ((Fin a' × Fin (a + a') → Fv F v) → ℂ)) (hS : ∀ φ ∈ S₀, φ ∈ SB (Fin a' × Fin (a + a') → Fv F v))
    (hon : ∀ ξ, ∃ φ ∈ S₀, Rf.p' v φ = ξ)
    (hL : ∀ g, ∀ φ ∈ S₀, ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, j g)) φ φ₁ →
      L φ₁ = fun h => L φ (h * j g)) :
    ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), L φ ∈ imgSpan π ((GlobalTheory.PRep.rightReg ℂ (UA σ G.W.J) ℂ).comp j) := by
  have hT := hM.triple
  have hAE := (GlobalTheory.T.theta_action_exists hK.base F E σ B _ _ _ _ _ _ _ om _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hT) v).1 1 (one_mem_UAt v)
  have hAE' := (GlobalTheory.T.theta_action_exists hK.base F E σ B _ _ _ _ _ _ _ om' _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hT) v).1 1 (one_mem_UAt v)
  have hk := ((GlobalTheory.T.theta_kernel_coinvariant hK.base F E σ B a a' G X om om' R Rf hM).1 v hv).2.1
  let S : Submodule ℂ (((Fin a × Fin (a + a') → Fv F v) → ℂ) × ((Fin a' × Fin (a + a') → Fv F v) → ℂ)) :=
    (SB _).prod (SB _) ⊓ LinearMap.ker (Rf.p v ∘ₗ LinearMap.fst ℂ _ _ - Rf.p' v ∘ₗ LinearMap.snd ℂ _ _)
  have hSm : ∀ s, s ∈ S ↔ s.1 ∈ SB _ ∧ s.2 ∈ SB _ ∧ Rf.p v s.1 = Rf.p' v s.2 := fun s => by
    simp only [S, Submodule.mem_inf, Submodule.mem_prod, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, sub_eq_zero, and_assoc]
  intro φ' hφ'
  obtain ⟨φ, hφ, e⟩ : Rf.p' v φ' ∈ (SB _).map (Rf.p v) := hM.fin.onto v ▸ Submodule.mem_top
  refine mem_imgSpan π _ S (P ∘ₗ LinearMap.fst ℂ _ _) (L ∘ₗ LinearMap.snd ℂ _ _) d (fun f => ?_) (fun s hs h0 => ?_)
    (fun g s hs => ?_) (φ, φ') ((hSm _).2 ⟨hφ, hφ', e⟩)
  · obtain ⟨ψ, hψ, rfl⟩ := onto f
    obtain ⟨ψ', hψ', e'⟩ := hon (Rf.p v ψ)
    exact ⟨(ψ, ψ'), (hSm _).2 ⟨hψ, hS _ hψ', e'.symm⟩, rfl⟩
  · obtain ⟨h1, h2, h3⟩ := (hSm s).1 hs
    have h4 : Rf.p v s.1 = 0 := hM.fin.inv v (ker s.1 h1 h0)
    exact haug ((hk s.2 h2).1 (h3.symm.trans h4))
  · obtain ⟨h1, h2, h3⟩ := (hSm s).1 hs
    obtain ⟨ψ', hψ', e'⟩ := hon (Rf.p' v s.2)
    have e₀ : L s.2 = L ψ' := by
      have := haug ((hk _ (sub_mem h2 (hS _ hψ'))).1 (by rw [map_sub, e', sub_self]))
      rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
    obtain ⟨φ₁, h₁, hA⟩ := (hAE (j g) (loc g) s.1 h1).exists
    obtain ⟨φ₁', h₁', hA'⟩ := (hAE' (j g) (loc g) ψ' (hS _ hψ')).exists
    refine ⟨(φ₁, φ₁'), (hSm _).2 ⟨h₁, h₁', hM.fin.equiv v _ (loc g) _ h1 _ (hS _ hψ') _ h₁ _ h₁' hA hA'
      (h3.trans e'.symm)⟩, eqv g _ h1 _ h₁ hA, ?_⟩
    show L φ₁' = (GlobalTheory.PRep.rightReg ℂ (UA σ G.W.J) ℂ).comp j g (L s.2)
    rw [hL g ψ' hψ' φ₁' h₁' hA', e₀]
    rfl

/- English proof (translation)
Introduce `Ψ hΨ`. Establish `hT` using `hM.triple`. Establish `hp` using `GlobalTheory.ThK.Inhab.pairV' hT`. Choose the witnesses or unpack the hypotheses as in `⟨ℓ, hℓ⟩ : ∃ ℓ : ((Fin a' × Fin (a + a') → AF F) → ℂ) →ₗ[ℂ] (UA σ G.W.J → ℂ), ∀ Φ ∈ G.M'.So B.ψ B.τ₁, ℓ Φ = G.M'.I om' Φ := by`. Establish `I0 : G.M'.I om' 0 = 0`.

Use function extensionality and compare the values at `h`. Simplify using `[Model.I, theta, thetaSum]`. Set `ℓ₀ : G.M'.So B.ψ B.τ₁ →ₗ[ℂ] (UA σ G.W.J → ℂ)` to `{ toFun := fun Φ => G.M'.I om' Φ.1 map_add' := fun Φ₁ Φ₂ => by`. Establish `e` using `GlobalTheory.T.theta_integral_linear hK F E σ B a a' G X om om' hT Φ₁.1 Φ₁.2 Φ₂.1 Φ₂.2 1`. Rewrite `e` using `[one_smul, one_smul]`. Then use the resulting hypothesis.

Use the proof step `map_smul' := fun c Φ => by`. Establish `e` using `GlobalTheory.T.theta_integral_linear hK F E σ B a a' G X om om' hT Φ.1 Φ.2 0 (zero_mem _) c`. Rewrite using `[add_zero, I0, add_zero] at e }` and apply the resulting hypothesis. Take `⟨ℓ, hℓ⟩` from `LinearMap.exists_extend ℓ₀`. Conclude with `⟨ℓ, fun Φ hΦ => LinearMap.congr_fun hℓ ⟨Φ, hΦ⟩⟩`.

Rewrite using `[← hℓ _ hΨ]`. Distinguish the cases in `hv1 : v = B.v₁`. Substitute `hv1` using the available equality. Take `⟨N, ψ, r, hψ, hrest, hso, rfl⟩` from `GlobalTheory.T.schwartz_factorization_base_place F E σ B a a' G X om om' hT _ hΨ`. Rewrite using `[map_sum]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `hl : ∀ z : UA σ G.W.J, ∃ Λ : ((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] ℂ, augAt om' B.v₁ ≤ LinearMap.ker Λ ∧ ∀ φ ∈ G.M'.SoLoc B.ψ B.τ₁, Λ φ = (LinearMap.proj z ∘ₗ ℓ ∘ₗ tensAt B.v₁ (r i)) φ` using `fun z => by`. Use `GlobalTheory.T.invariant_local_functional_unique hK.base F E σ B a a' G X om om' hT B.v₁ hv B.τ₁ _ ?_` and prove the remaining obligations. Introduce `g' hg' φ hφ φ₁ hφ₁ hA`. Use `show ℓ (tens _ φ₁ (r i)) z = ℓ (tens _ φ (r i)) z`.

Rewrite using `[hℓ _ (hso i φ₁ hφ₁), hℓ _ (hso i φ hφ), ← hA (r i) (hrest i φ hφ.1), GlobalTheory.ThetaIntegralInv.integral_translate hK.base hp g' _ (hrest i φ hφ.1).2]`. Use `choose Λ hΛa hΛs using hl`. Establish `hL : ∀ φ ∈ G.M'.SoLoc B.ψ B.τ₁, LinearMap.pi Λ φ = G.M'.I om' (tens (evFin F B.v₁) φ (r i))` using `fun φ h => by`. Rewrite using `[← hℓ _ (hso i φ h)]`. Conclude with `funext fun z => hΛs z φ h`.

Rewrite using `[hℓ _ (hso i _ (hψ i)), ← hL _ (hψ i)]`. Use `small_loc hK hM hv π j P d loc onto ker eqv (LinearMap.pi Λ) (fun φ h => funext fun z => hΛa z h) (G.M'.SoLoc B.ψ B.τ₁) (fun φ h => h.1) (((GlobalTheory.T.theta_kernel_coinvariant hK.base F E σ B a a' G X om om' R Rf hM).1 _ hv).2.2.1 B.τ₁) (fun g φ h φ₁ h₁ hA => ?_) _ (hψ i).1` and prove the remaining obligations. Rewrite using `[hL _ h, hL _ (GlobalTheory.T.local_schwartz_stable_under_W hK.base F E σ B a a' G X om om' hT B.v₁ hv B.τ₁ _ (loc g) φ h φ₁ h₁ hA), ← hA (r i) (hrest i φ h.1), I_right]`. Take `⟨N, ψ, r, hψ, hr, rfl⟩` from `GlobalTheory.T.schwartz_factorization_away_base F E σ B a a' G X om om' hT _ hΨ v hv1`. Rewrite using `[map_sum]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `hL : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), (ℓ ∘ₗ tensAt v (r i)) φ = G.M'.I om' (tens (evFin F v) φ (r i))` using `fun φ h => hℓ _ (hr i φ h).2`. Use `small_loc hK hM hv π j P d loc onto ker eqv (ℓ ∘ₗ tensAt v (r i)) ?_ (SB (Fin a' × Fin (a + a') → Fv F v) : Set _) (fun φ h => h) (fun ξ => ?_) (fun g φ h φ₁ h₁ hA => ?_) _ (hψ i)` and prove the remaining obligations. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g', hg', φ, hφ, φ₁, hφ₁, hA, rfl⟩`.

Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero, hL _ hφ₁, hL _ hφ, ← hA (r i) (hr i φ hφ).1, GlobalTheory.ThetaIntegralInv.integral_translate hK.base hp g' _ (hr i φ hφ).1.2]`. Conclude with `(hM.fin.onto' v ▸ Submodule.mem_top : ξ ∈ (SB _).map (Rf.p' v))`. Rewrite using `[hL _ h, hL _ h₁, ← hA (r i) (hr i φ h).1, I_right]`.
-/
theorem small_mem (hK : KP) (hM : IsMatched B G X om om' R Rf) (hv : X.Good v) (π : Representation ℂ Γ V) (j : Γ →* UA σ G.W.J)
    (P : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] V) (d : Γ) (loc : ∀ g, j g ∈ UAt σ G.W (evFin F v))
    (onto : ∀ f, ∃ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), P φ = f)
    (ker : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), P φ = 0 → φ ∈ augAt om v)
    (eqv : ∀ g, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, j g)) φ φ₁ → P φ₁ = π (d⁻¹ * g * d) (P φ)) :
    ∀ Ψ ∈ G.M'.So B.ψ B.τ₁, G.M'.I om' Ψ ∈ imgSpan π ((GlobalTheory.PRep.rightReg ℂ (UA σ G.W.J) ℂ).comp j) := by
  intro Ψ hΨ
  have hT := hM.triple
  have hp := GlobalTheory.ThK.Inhab.pairV' hT
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ((Fin a' × Fin (a + a') → AF F) → ℂ) →ₗ[ℂ] (UA σ G.W.J → ℂ), ∀ Φ ∈ G.M'.So B.ψ B.τ₁,
      ℓ Φ = G.M'.I om' Φ := by
    have I0 : G.M'.I om' 0 = 0 := by
      funext h; simp [Model.I, theta, thetaSum]
    let ℓ₀ : G.M'.So B.ψ B.τ₁ →ₗ[ℂ] (UA σ G.W.J → ℂ) :=
      { toFun := fun Φ => G.M'.I om' Φ.1
        map_add' := fun Φ₁ Φ₂ => by
          have e := GlobalTheory.T.theta_integral_linear hK F E σ B a a' G X om om' hT Φ₁.1 Φ₁.2 Φ₂.1 Φ₂.2 1
          rwa [one_smul, one_smul] at e
        map_smul' := fun c Φ => by
          have e := GlobalTheory.T.theta_integral_linear hK F E σ B a a' G X om om' hT Φ.1 Φ.2 0 (zero_mem _) c
          rwa [add_zero, I0, add_zero] at e }
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
    exact ⟨ℓ, fun Φ hΦ => LinearMap.congr_fun hℓ ⟨Φ, hΦ⟩⟩
  rw [← hℓ _ hΨ]
  by_cases hv1 : v = B.v₁
  · subst hv1
    obtain ⟨N, ψ, r, hψ, hrest, hso, rfl⟩ := GlobalTheory.T.schwartz_factorization_base_place F E σ B a a' G X om om' hT _ hΨ
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hl : ∀ z : UA σ G.W.J, ∃ Λ : ((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] ℂ,
        augAt om' B.v₁ ≤ LinearMap.ker Λ ∧ ∀ φ ∈ G.M'.SoLoc B.ψ B.τ₁,
          Λ φ = (LinearMap.proj z ∘ₗ ℓ ∘ₗ tensAt B.v₁ (r i)) φ := fun z => by
      refine GlobalTheory.T.invariant_local_functional_unique hK.base F E σ B a a' G X om om' hT B.v₁ hv B.τ₁ _ ?_
      intro g' hg' φ hφ φ₁ hφ₁ hA
      show ℓ (tens _ φ₁ (r i)) z = ℓ (tens _ φ (r i)) z
      rw [hℓ _ (hso i φ₁ hφ₁), hℓ _ (hso i φ hφ), ← hA (r i) (hrest i φ hφ.1),
        GlobalTheory.ThetaIntegralInv.integral_translate hK.base hp g' _ (hrest i φ hφ.1).2]
    choose Λ hΛa hΛs using hl
    have hL : ∀ φ ∈ G.M'.SoLoc B.ψ B.τ₁, LinearMap.pi Λ φ = G.M'.I om' (tens (evFin F B.v₁) φ (r i)) := fun φ h => by
      rw [← hℓ _ (hso i φ h)]
      exact funext fun z => hΛs z φ h
    rw [hℓ _ (hso i _ (hψ i)), ← hL _ (hψ i)]
    refine small_loc hK hM hv π j P d loc onto ker eqv (LinearMap.pi Λ) (fun φ h => funext fun z => hΛa z h)
      (G.M'.SoLoc B.ψ B.τ₁) (fun φ h => h.1) (((GlobalTheory.T.theta_kernel_coinvariant hK.base F E σ B a a' G X om om' R Rf hM).1 _ hv).2.2.1 B.τ₁)
      (fun g φ h φ₁ h₁ hA => ?_) _ (hψ i).1
    rw [hL _ h, hL _ (GlobalTheory.T.local_schwartz_stable_under_W hK.base F E σ B a a' G X om om' hT B.v₁ hv B.τ₁ _ (loc g) φ h φ₁ h₁ hA),
      ← hA (r i) (hrest i φ h.1), I_right]
  · obtain ⟨N, ψ, r, hψ, hr, rfl⟩ := GlobalTheory.T.schwartz_factorization_away_base F E σ B a a' G X om om' hT _ hΨ v hv1
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hL : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), (ℓ ∘ₗ tensAt v (r i)) φ = G.M'.I om' (tens (evFin F v) φ (r i)) :=
      fun φ h => hℓ _ (hr i φ h).2
    refine small_loc hK hM hv π j P d loc onto ker eqv (ℓ ∘ₗ tensAt v (r i)) ?_ (SB (Fin a' × Fin (a + a') → Fv F v) : Set _)
      (fun φ h => h)
      (fun ξ => ?_) (fun g φ h φ₁ h₁ hA => ?_) _ (hψ i)
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨g', hg', φ, hφ, φ₁, hφ₁, hA, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero, hL _ hφ₁, hL _ hφ, ← hA (r i) (hr i φ hφ).1,
        GlobalTheory.ThetaIntegralInv.integral_translate hK.base hp g' _ (hr i φ hφ).1.2]
    · exact (hM.fin.onto' v ▸ Submodule.mem_top : ξ ∈ (SB _).map (Rf.p' v))
    · rw [hL _ h, hL _ h₁, ← hA (r i) (hr i φ h).1, I_right]

end GlobalTheory.LocTypeDiffs

open GlobalTheory.LocTypeDiffs in

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM c v hv τ hcm ε herm hJ x hx e f hf y`. Take `rfl` from `hx.symm`. Establish `hT` using `hM.triple`. Take `⟨P, b, onto, ker, -, eqv⟩` from `GlobalTheory.T.good_place_induced_intertwiner_exists hK F E σ B a a' G X om om' hT v hv τ`. Take `⟨q, hq⟩` from `glReindex_conj (k := Fv F v) e`.

Use `set j := (GlobalTheory.SplitUnitLift.liftU hcm τ G.W.J ε herm hJ).comp (glReindex e) with hj`. Establish `loc : ∀ g, j g ∈ UAt σ G.W (evFin F v)` using `fun g => GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm τ G.W ε herm hJ _`. Establish `eqv'` using `fun g => eqv (j g) (loc g) ((q⁻¹ * b)⁻¹ * g * (q⁻¹ * b)) (by`. Rewrite using `[hj, MonoidHom.comp_apply, GlobalTheory.SplitUnitLift.liftU_piW, hq]`. Use `congr 1`.

Use the proof step `group)`. Establish `h1` using `big_mem hK hT _ j P (q⁻¹ * b) loc onto ker eqv'`. Establish `h2` using `small_mem hK hM hv _ j P (q⁻¹ * b) loc onto ker eqv'`. Rewrite using `[imgSpan_detInd]`. Use `show (GlobalTheory.PRep.rightReg ℂ (UA σ G.W.J) ℂ) y f ∈ imgSpan _ ((GlobalTheory.PRep.rightReg ℂ (UA σ G.W.J) ℂ).comp j)`.

Use `Submodule.mem_comap.1 (Submodule.span_le.2 ?_ hf)` and prove the remaining obligations. Introduce and unpack `_ ⟨Φ, Φ', hΦ', ⟨T, -, m, m', f₁, φ, -, -, hφ, -, hΦ, -, -⟩, rfl⟩`. Establish `hS : Φ ∈ schA F (Fin a × Fin (a + a'))`. Rewrite using `[hΦ]`. Use `Submodule.sum_mem _ fun i _ => GlobalTheory.TensUniq.pure_mem_schA _ _ (hφ i).2.1 ?_` and prove the remaining obligations.

Conclude with `(T.finite_toSet.eventually_cofinite_notMem.and hT.geo.hM.std).mono fun w hw => ((hφ i).2.2 w hw.1).trans hw.2`. Establish `h3` using `h1 _ ((GlobalTheory.ThK.Inhab.pairV hT).weil.isUSplitting.pres (1, y) Φ hS)`. Establish `h4` using `h2 _ ((GlobalTheory.T.theta_kernel_coinvariant hK.base F E σ B a a' G X om om' R Rf hM).2 (1, y) Φ' hΦ')`. Rewrite `h3`, `h4` using `[I_right]`. Conclude with `sub_mem h3 (Submodule.smul_mem _ c h4)`.
-/
theorem GlobalTheory.LocTypeDiffs.diffs_locType : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → ∀ (c : ℂ) (v : Pl F), X.Good v → ∀ (τ : E →ₐ[F] Fv F v) (hcm : IsCMExt F E σ) (ε : F)
    (herm : ∀ i j, σ (G.W.J j i) = algebraMap F E ε * G.W.J i j) (hJ : IsUnit (G.W.J.map τ).det) (x : ℕ), x = a →
    ∀ e : Fin (x + a') ≃ Fin (a + a'), ∀ f ∈ Diffs B G X om om' R Rf c,
      HasLocType hcm τ G.W.J ε herm hJ e (chrW X.α τ) (chrW X.β τ) f := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM c v hv τ hcm ε herm hJ x hx e f hf y
  obtain rfl := hx.symm
  have hT := hM.triple
  obtain ⟨P, b, onto, ker, -, eqv⟩ := GlobalTheory.T.good_place_induced_intertwiner_exists hK F E σ B a a' G X om om' hT v hv τ
  obtain ⟨q, hq⟩ := glReindex_conj (k := Fv F v) e
  set j := (GlobalTheory.SplitUnitLift.liftU hcm τ G.W.J ε herm hJ).comp (glReindex e) with hj
  have loc : ∀ g, j g ∈ UAt σ G.W (evFin F v) := fun g => GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm τ G.W ε herm hJ _
  have eqv' := fun g => eqv (j g) (loc g) ((q⁻¹ * b)⁻¹ * g * (q⁻¹ * b)) (by
    rw [hj, MonoidHom.comp_apply, GlobalTheory.SplitUnitLift.liftU_piW, hq]
    congr 1
    group)
  have h1 := big_mem hK hT _ j P (q⁻¹ * b) loc onto ker eqv'
  have h2 := small_mem hK hM hv _ j P (q⁻¹ * b) loc onto ker eqv'
  rw [imgSpan_detInd]
  show (GlobalTheory.PRep.rightReg ℂ (UA σ G.W.J) ℂ) y f ∈ imgSpan _ ((GlobalTheory.PRep.rightReg ℂ (UA σ G.W.J) ℂ).comp j)
  refine Submodule.mem_comap.1 (Submodule.span_le.2 ?_ hf)
  rintro _ ⟨Φ, Φ', hΦ', ⟨T, -, m, m', f₁, φ, -, -, hφ, -, hΦ, -, -⟩, rfl⟩
  have hS : Φ ∈ schA F (Fin a × Fin (a + a')) := by
    rw [hΦ]
    refine Submodule.sum_mem _ fun i _ => GlobalTheory.TensUniq.pure_mem_schA _ _ (hφ i).2.1 ?_
    exact (T.finite_toSet.eventually_cofinite_notMem.and hT.geo.hM.std).mono fun w hw => ((hφ i).2.2 w hw.1).trans hw.2
  have h3 := h1 _ ((GlobalTheory.ThK.Inhab.pairV hT).weil.isUSplitting.pres (1, y) Φ hS)
  have h4 := h2 _ ((GlobalTheory.T.theta_kernel_coinvariant hK.base F E σ B a a' G X om om' R Rf hM).2 (1, y) Φ' hΦ')
  rw [I_right] at h3 h4
  exact sub_mem h3 (Submodule.smul_mem _ c h4)

end
