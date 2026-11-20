import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestrictionPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationMapAdaptedPlaneContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.AnisRatInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
The claim follows from `Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)`.
-/
theorem inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

/- English proof (translation)
Introduce `a b h` and use `funext fun i => inclR_inj (congrFun h i)`.
-/
theorem incV_injective {n : ℕ} : Function.Injective (incV F (E := E) (n := n)) := fun a b h =>
  funext fun i => inclR_inj (congrFun h i)

/- English proof (translation)
Proceed by induction on `hg using Subgroup.closure_induction with`. Consider the case `mem g h => exact h.1`. Consider the case `one => show ((1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ _ = _`. Simplify using the standard rewrite rules. Consider the case `mul a b _ _ ha hb => show ((a.1 * b.1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ _ = _`.

Rewrite using `[Units.val_mul, ← Matrix.mulVec_mulVec]`. Conclude with `(congrArg _ hb).trans ha`. Consider the case `inv a _ ha`. Establish `h1 : mat a⁻¹ * mat a = 1` using `Units.inv_mul a.1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem unip_fix {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁} {g : UA σ W.J}
    (hg : g ∈ unip σ W H') : mat g *ᵥ incV F H'.x = incV F H'.x := by
  induction hg using Subgroup.closure_induction with
  | mem g h => exact h.1
  | one => show ((1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ _ = _; simp
  | mul a b _ _ ha hb =>
    show ((a.1 * b.1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ _ = _
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (congrArg _ hb).trans ha
  | inv a _ ha =>
    have h1 : mat a⁻¹ * mat a = 1 := Units.inv_mul a.1
    calc mat a⁻¹ *ᵥ incV F H'.x = mat a⁻¹ *ᵥ (mat a *ᵥ incV F H'.x) := by rw [ha]
      _ = incV F H'.x := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

/- English proof (translation)
Take `⟨G, hG⟩` from `Subgroup.mem_subgroupOf.1 hg`. Conclude with `⟨G, by rw [mat, ← hG]; rfl⟩`.
-/
theorem exists_rat {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} {g : UA σ J} (hg : g ∈ ratU σ J) :
    ∃ G : Matrix (Fin d) (Fin d) E, mat g = incM F G := by
  obtain ⟨G, hG⟩ := Subgroup.mem_subgroupOf.1 hg
  exact ⟨G, by rw [mat, ← hG]; rfl⟩

/- English proof (translation)
Establish `h' : (incM F G)ᵀ * incM F J * (incM F G).map (cA σ) = incM F J` using `by rw [← hG]; exact g.2`. Establish `h3 : (incM F G).map (cA σ) = incM F (G.map σ)`. Use extensionality with `i j`. Simplify using `[incM, GlobalTheory.UnipMass.cA_inclR]`. Establish `e : incM F (Gᵀ * J * G.map σ) = incM F J`.

Rewrite using `[← h', h3]`. Simplify using `only [incM, Matrix.map_mul, Matrix.transpose_map]`. Conclude with `Matrix.map_injective inclR_inj e`.
-/
theorem unitary_rat {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (g : UA σ J) (G : Matrix (Fin d) (Fin d) E)
    (hG : mat g = incM F G) : Gᵀ * J * G.map σ = J := by
  have h' : (incM F G)ᵀ * incM F J * (incM F G).map (cA σ) = incM F J := by rw [← hG]; exact g.2
  have h3 : (incM F G).map (cA σ) = incM F (G.map σ) := by
    ext i j; simp [incM, GlobalTheory.UnipMass.cA_inclR]
  have e : incM F (Gᵀ * J * G.map σ) = incM F J := by
    rw [← h', h3]; simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  exact Matrix.map_injective inclR_inj e

/- English proof (translation)
Unfold `form`. Establish `: (fun i => σ ((G *ᵥ w) i)) = G.map σ *ᵥ fun i => σ (w i)`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, map_sum, map_mul]`. Rewrite using `[this, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, hG]`.
-/
theorem form_mulVec (σ : E →ₐ[F] E) {d : ℕ} (J G : Matrix (Fin d) (Fin d) E) (hG : Gᵀ * J * G.map σ = J)
    (v w : Fin d → E) : form σ J (G *ᵥ v) (G *ᵥ w) = form σ J v w := by
  unfold form
  have : (fun i => σ ((G *ᵥ w) i)) = G.map σ *ᵥ fun i => σ (w i) := by
    funext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [this, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, hG]

/- English proof (translation)
Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[hJ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_swap (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (v w : Fin d → E) : form σ J w v = -σ (form σ J v w) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun l _ => by ring`.
-/
theorem vecMulVec_mul_transpose {m k : ℕ} (a : Fin m → AE F E) (b : Fin k → AE F E) (N : Matrix (Fin k) (Fin k) (AE F E)) :
    Matrix.vecMulVec a b * Nᵀ = Matrix.vecMulVec a (N *ᵥ b) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

end GlobalTheory.AnisRatInv

namespace GlobalTheory.AnisRatInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Set `S : Submodule E (Fin d → E)` to `{ carrier := {r | ∃ (s t : E) (u : Fin d₁ → E), r = s • H'.x + H'.ι *ᵥ u + t • H'.y} add_mem' := by`. Introduce and unpack `_ _ ⟨s, t, u, rfl⟩ ⟨s', t', u', rfl⟩`. Conclude with `⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩`. Use the proof step `zero_mem' := ⟨0, 0, 0, by simp⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `c _ ⟨s, t, u, rfl⟩`. Conclude with `⟨c * s, c * t, c • u, by rw [Matrix.mulVec_smul]; module⟩ }`. Establish `hle : Submodule.span E (W.L : Set (Fin d → E)) ≤ S`. Use `Submodule.span_le.mpr fun z hz => ?_` and prove the remaining obligations. Take `⟨s, t, u, -, -, -, h⟩` from `hH.split z hz`.

Conclude with `⟨s, t, u, h⟩`. Rewrite `hle` using `[Submodule.IsLattice.span_eq_top]`. Conclude with `hle (Submodule.mem_top (x := r))`.
-/
theorem exists_split_vec {σ : E →ₐ[F] E} {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁}
    {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (hL : W.L.IsLattice E) (r : Fin d → E) :
    ∃ (s t : E) (u : Fin d₁ → E), r = s • H'.x + H'.ι *ᵥ u + t • H'.y := by
  let S : Submodule E (Fin d → E) :=
    { carrier := {r | ∃ (s t : E) (u : Fin d₁ → E), r = s • H'.x + H'.ι *ᵥ u + t • H'.y}
      add_mem' := by
        rintro _ _ ⟨s, t, u, rfl⟩ ⟨s', t', u', rfl⟩
        exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩
      zero_mem' := ⟨0, 0, 0, by simp⟩
      smul_mem' := by
        rintro c _ ⟨s, t, u, rfl⟩
        exact ⟨c * s, c * t, c • u, by rw [Matrix.mulVec_smul]; module⟩ }
  have hle : Submodule.span E (W.L : Set (Fin d → E)) ≤ S := by
    refine Submodule.span_le.mpr fun z hz => ?_
    obtain ⟨s, t, u, -, -, -, h⟩ := hH.split z hz
    exact ⟨s, t, u, h⟩
  rw [Submodule.IsLattice.span_eq_top] at hle
  exact hle (Submodule.mem_top (x := r))

/- English proof (translation)
The claim follows from `add_dotProduct _ _ _`.
-/
theorem form_add_left (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (v v' w : Fin d → E) :
    form σ J (v + v') w = form σ J v w + form σ J v' w := add_dotProduct _ _ _

/- English proof (translation)
The claim follows from `sub_dotProduct _ _ _`.
-/
theorem form_sub_left (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (v v' w : Fin d → E) :
    form σ J (v - v') w = form σ J v w - form σ J v' w := sub_dotProduct _ _ _

/- English proof (translation)
The claim follows from `smul_dotProduct _ _ _`.
-/
theorem form_smul_left (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (a : E) (v w : Fin d → E) :
    form σ J (a • v) w = a * form σ J v w := smul_dotProduct _ _ _

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he χX χW om r s r' s' hP ξ γ hγr hγu u Ψ hΨ`. Establish `hψ : IsStd B.ψ` using `hP.base.std`. Establish `hM : M.IsGood B.ψ` using `hP.good`. Establish `hσ : ∀ a, σ (σ a) = a` using `fun a => by`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`.

Conclude with `τ.injective (by rw [hP.base.cm.2.2.2, hP.base.cm.2.2.2, star_star])`. Establish `hspl` using `IsUWeilPair.isUSplitting hP.weil`. Establish `hΦ : om (1, u) Ψ ∈ schA F (Fin n × Fin d)` using `hspl.pres (1, u) Ψ hΨ`. Take `⟨G, hG⟩` from `exists_rat (inv_mem hγr)`. Establish `hGu : Gᵀ * W.J * G.map σ = W.J` using `unitary_rat _ G hG`.

Establish `hGx : G *ᵥ H'.x = H'.x` using `incV_injective (F := F) (by`. Rewrite using `[← GlobalTheory.UnipMass.incM_mulVec_incV, ← hG]`. Conclude with `unip_fix (inv_mem hγu))`. Take `⟨a, t, b, hv⟩` from `exists_split_vec hH hP.skew.lat (G *ᵥ H'.y - H'.y)`. Establish `hyx : form σ W.J H'.y H'.x = -1`.

Rewrite using `[form_swap σ hσ hP.skew.skew, hH.xy, map_one]`. Establish `ht : t = 0`. Establish `h0 : form σ W.J (G *ᵥ H'.y - H'.y) H'.x = 0`. Rewrite using `[form_sub_left]`. Use `conv_lhs => rw [← hGx]`.

Rewrite using `[form_mulVec σ W.J G hGu, hGx, sub_self]`. Rewrite `h0` using `[hv, form_add_left, form_add_left, form_smul_left, form_smul_left, hH.xx, (hH.orth b).1, hyx]`. Take the linear combination `-h0`. Substitute `ht` using the available equality. Establish `hGy : G *ᵥ H'.y = H'.y + a • H'.x + H'.ι *ᵥ b`.

Rewrite `hv` using `[zero_smul, add_zero, sub_eq_iff_eq_add']`. Rewrite using `[hv, add_assoc]`. Establish `hmul : om (1, γ * u) Ψ = om (1, γ) (om (1, u) Ψ)`. Rewrite using `[show ((1 : UA σ X.J), γ * u) = ((1 : UA σ X.J), γ) * (1, u) by simp, map_mul, Module.End.mul_apply]`. Establish `hw' : actAB (cA σ) ((1 : UA σ X.J), γ⁻¹) (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) = incM F (Matrix.vecMulVec ξ (G *ᵥ H'.y))` using `by show ((1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * _ * (mat γ⁻¹)ᵀ = _`.

Rewrite using `[Units.val_one, Matrix.one_mul, hG, vecMulVec_mul_transpose, GlobalTheory.UnipMass.incM_mulVec_incV, GlobalTheory.ThetaExpandInv.incM_vecMulVec]`. Establish `hact : actAB (cA σ) ((1 : UA σ X.J), γ) (actAB (cA σ) ((1 : UA σ X.J), γ⁻¹) (Matrix.vecMulVec (incV F ξ) (incV F H'.y))) = Matrix.vecMulVec (incV F ξ) (incV F H'.y)` using `by show ((1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * (((1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * _ * (mat γ⁻¹)ᵀ) * (mat γ)ᵀ = _`. Establish `h1 : mat γ * mat γ⁻¹ = 1` using `Units.mul_inv γ.1`. Rewrite using `[Units.val_one, Matrix.one_mul, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, h1, Matrix.transpose_one, Matrix.mul_one]`. Establish `step : M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, γ) (om (1, u) Ψ)) = om (1, γ) (M.co.rho B.ψ (incM F (Matrix.vecMulVec ξ (G *ᵥ H'.y))) (om (1, u) Ψ))`.

Rewrite using `[← hw', hspl.impl _ _ _ hΦ, hact]`. Rewrite using `[hmul, step, GlobalTheory.T.eigen_intertwiner_restriction_pair hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he χX χW om r s r' s' hP γ hγu _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ _ hΦ)]`. Establish `hsum : Matrix.vecMulVec ξ (G *ᵥ H'.y) = Matrix.vecMulVec (a • ξ) H'.x + (Matrix.vecMulVec ξ b * H'.ιᵀ + Matrix.vecMulVec ξ H'.y)`. Rewrite using `[hGy]`. Use extensionality with `i j`.

Simplify using `only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.transpose_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, mul_add, Finset.mul_sum]`. Rewrite using `[show ∑ k, ξ i * (H'.ι j k * b k) = ∑ k, ξ i * b k * H'.ι j k from Finset.sum_congr rfl fun _ _ => by ring]`. Expand and normalize the polynomial expressions, which then agree. Establish `hiso : incM F (Matrix.vecMulVec (a • ξ) H'.x) ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E)))` using `⟨incV F (a • ξ), GlobalTheory.ThetaExpandInv.incM_vecMulVec _ _⟩`. Rewrite using `[hsum, ← GlobalTheory.ThetaExpandInv.rho_rat_rho_rat M hψ hM, he.inv _ hiso _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ _ hΦ), ← GlobalTheory.ThetaExpandInv.rho_rat_rho_rat M hψ hM, GlobalTheory.ThetaExpandInv.incM_mul_transpose, he.Heisenberg₂ _ _ (GlobalTheory.HeisSchA.rho …`.
-/
theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ ξ : Fin n → E, ∀ γ ∈ ratU σ W.J, γ ∈ unip σ W H' → ∀ (u : UA σ W.J), ∀ Ψ ∈ schA F (Fin n × Fin d),
      thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, γ * u) Ψ))) = thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, u) Ψ))) := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he χX χW om r s r' s' hP ξ γ hγr hγu u Ψ hΨ
  have hψ : IsStd B.ψ := hP.base.std
  have hM : M.IsGood B.ψ := hP.good
  have hσ : ∀ a, σ (σ a) = a := fun a => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hP.base.cm.2.2.2, hP.base.cm.2.2.2, star_star])
  have hspl := IsUWeilPair.isUSplitting hP.weil
  have hΦ : om (1, u) Ψ ∈ schA F (Fin n × Fin d) := hspl.pres (1, u) Ψ hΨ
  obtain ⟨G, hG⟩ := exists_rat (inv_mem hγr)
  have hGu : Gᵀ * W.J * G.map σ = W.J := unitary_rat _ G hG
  have hGx : G *ᵥ H'.x = H'.x := incV_injective (F := F) (by
    rw [← GlobalTheory.UnipMass.incM_mulVec_incV, ← hG]; exact unip_fix (inv_mem hγu))
  obtain ⟨a, t, b, hv⟩ := exists_split_vec hH hP.skew.lat (G *ᵥ H'.y - H'.y)
  have hyx : form σ W.J H'.y H'.x = -1 := by
    rw [form_swap σ hσ hP.skew.skew, hH.xy, map_one]
  have ht : t = 0 := by
    have h0 : form σ W.J (G *ᵥ H'.y - H'.y) H'.x = 0 := by
      rw [form_sub_left]
      conv_lhs => rw [← hGx]
      rw [form_mulVec σ W.J G hGu, hGx, sub_self]
    rw [hv, form_add_left, form_add_left, form_smul_left, form_smul_left, hH.xx, (hH.orth b).1, hyx] at h0
    linear_combination -h0
  subst ht
  have hGy : G *ᵥ H'.y = H'.y + a • H'.x + H'.ι *ᵥ b := by
    rw [zero_smul, add_zero, sub_eq_iff_eq_add'] at hv
    rw [hv, add_assoc]
  have hmul : om (1, γ * u) Ψ = om (1, γ) (om (1, u) Ψ) := by
    rw [show ((1 : UA σ X.J), γ * u) = ((1 : UA σ X.J), γ) * (1, u) by simp, map_mul, Module.End.mul_apply]
  have hw' : actAB (cA σ) ((1 : UA σ X.J), γ⁻¹) (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) =
      incM F (Matrix.vecMulVec ξ (G *ᵥ H'.y)) := by
    show ((1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * _ * (mat γ⁻¹)ᵀ = _
    rw [Units.val_one, Matrix.one_mul, hG, vecMulVec_mul_transpose, GlobalTheory.UnipMass.incM_mulVec_incV,
      GlobalTheory.ThetaExpandInv.incM_vecMulVec]
  have hact : actAB (cA σ) ((1 : UA σ X.J), γ) (actAB (cA σ) ((1 : UA σ X.J), γ⁻¹)
      (Matrix.vecMulVec (incV F ξ) (incV F H'.y))) = Matrix.vecMulVec (incV F ξ) (incV F H'.y) := by
    show ((1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *
      (((1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * _ * (mat γ⁻¹)ᵀ) * (mat γ)ᵀ = _
    have h1 : mat γ * mat γ⁻¹ = 1 := Units.mul_inv γ.1
    rw [Units.val_one, Matrix.one_mul, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, h1,
      Matrix.transpose_one, Matrix.mul_one]
  have step : M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (om (1, γ) (om (1, u) Ψ)) =
      om (1, γ) (M.co.rho B.ψ (incM F (Matrix.vecMulVec ξ (G *ᵥ H'.y))) (om (1, u) Ψ)) := by
    rw [← hw', hspl.impl _ _ _ hΦ, hact]
  rw [hmul, step, GlobalTheory.T.eigen_intertwiner_restriction_pair hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he χX χW om r s r' s' hP γ hγu _
    (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ _ hΦ)]
  have hsum : Matrix.vecMulVec ξ (G *ᵥ H'.y) =
      Matrix.vecMulVec (a • ξ) H'.x + (Matrix.vecMulVec ξ b * H'.ιᵀ + Matrix.vecMulVec ξ H'.y) := by
    rw [hGy]
    ext i j
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.transpose_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, mul_add, Finset.mul_sum]
    rw [show ∑ k, ξ i * (H'.ι j k * b k) = ∑ k, ξ i * b k * H'.ι j k from
      Finset.sum_congr rfl fun _ _ => by ring]
    ring
  have hiso : incM F (Matrix.vecMulVec (a • ξ) H'.x) ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))) :=
    ⟨incV F (a • ξ), GlobalTheory.ThetaExpandInv.incM_vecMulVec _ _⟩
  rw [hsum, ← GlobalTheory.ThetaExpandInv.rho_rat_rho_rat M hψ hM,
    he.inv _ hiso _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ _ hΦ), ← GlobalTheory.ThetaExpandInv.rho_rat_rho_rat M hψ hM,
    GlobalTheory.ThetaExpandInv.incM_mul_transpose, he.Heisenberg₂ _ _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ _ hΦ),
    GlobalTheory.ThetaExpandInv.thetaSum_rho_rat M₁ hψ hM₁, GlobalTheory.ThetaExpandInv.incM_vecMulVec]

end GlobalTheory.AnisRatInv
