import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLinearHeightForm
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

noncomputable section

namespace GlobalTheory.ConeSmallMidJB.IsoMid

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Simplify using `only [form, add_dotProduct]`.
-/
theorem form_add_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (u w y : Fin n → E) :
    form σ J (u + w) y = form σ J u y + form σ J w y := by
  simp only [form, add_dotProduct]

/- English proof (translation)
Simplify using `only [form, smul_dotProduct, smul_eq_mul]`.
-/
theorem form_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : E) (u y : Fin n → E) :
    form σ J (c • u) y = c * form σ J u y := by
  simp only [form, smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Simplify using `only [form, zero_dotProduct]`.
-/
theorem form_zero_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    form σ J 0 y = 0 := by
  simp only [form, zero_dotProduct]

/- English proof (translation)
Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hJ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_swap (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (u w : Fin n → E) : form σ J w u = -σ (form σ J u w) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

/- English proof (translation)
Establish `h : (fun i => σ ((M *ᵥ w) i)) = M.map σ *ᵥ fun i => σ (w i)`. Use function extensionality and compare the values at `i`. Conclude with `(σ.toRingHom.map_mulVec M w i)`. Simplify using `only [form]`. Rewrite using `[h]`.

Use `conv_rhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]`.
-/
theorem form_mulVec (σ : E →ₐ[F] E) {m k : ℕ} (J : Matrix (Fin m) (Fin m) E) (M : Matrix (Fin m) (Fin k) E)
    (u w : Fin k → E) : form σ J (M *ᵥ u) (M *ᵥ w) = form σ (Mᵀ * J * M.map σ) u w := by
  have h : (fun i => σ ((M *ᵥ w) i)) = M.map σ *ᵥ fun i => σ (w i) := by
    funext i
    exact (σ.toRingHom.map_mulVec M w i)
  simp only [form]
  rw [h]
  conv_rhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

end GlobalTheory.ConeSmallMidJB.IsoMid

end

namespace GlobalTheory.ConeSmallMidJB.IsoMid

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' hT T hTs t ht`. Take `⟨htT, hnS, hO⟩` from `ht`. Establish `hσ : ∀ x, σ (σ x) = x`. Introduce `e`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`.

Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hT.base.cm.2.2.2, hT.base.cm.2.2.2, star_star]`. Establish `hA` using `hC.hH'`. Establish `hskew` using `hT.geo.hW.skew`. Establish `hinj : Function.Injective (inclR (F` using `F) (E := E) (AF F)) := by haveI : Nontrivial (AF F) := inferInstanceAs (Nontrivial (Ainf F × Af F))`.

Conclude with `Algebra.TensorProduct.includeRight_injective (algebraMap F (AF F)).injective`. Establish `htr : t ∈ ratU σ G.W.J` using `hTs htT`. Establish `h1` using `Subgroup.mem_subgroupOf.1 htr`. Rewrite `h1` using `[MonoidHom.mem_range]`. Take `⟨g0, hg0⟩` from `h1`.

Establish `hmt : mat t = incM F (g0 : Matrix (Fin (a + (b + 2))) (Fin (a + (b + 2))) E)`. Unfold `mat`. Rewrite using `[← hg0]`. Both sides reduce to the same expression. Take `⟨h0, hh0⟩ : ∃ h0 : Matrix (Fin (a + (b + 2))) (Fin (a + (b + 2))) E, h0 = ↑g0⁻¹` from `⟨_, rfl⟩`.

Establish `hmti : mat t⁻¹ = incM F h0`. Unfold `mat`. Rewrite using `[Subgroup.coe_inv, ← hg0, ← map_inv, hh0]`. Both sides reduce to the same expression. Establish `hu : h0ᵀ * G.W.J * h0.map σ = G.W.J`.

Establish `e : (mat t⁻¹)ᵀ * incM F G.W.J * (mat t⁻¹).map (cA σ) = incM F G.W.J` using `(t⁻¹).2`. Rewrite `e` using `[hmti]`. Apply `Matrix.map_injective hinj` to reduce the goal to its premises. Use `show (h0ᵀ * G.W.J * h0.map σ).map (inclR (F := F) (E := E) (AF F)) = G.W.J.map (inclR (F := F) (E := E) (AF F))`. Establish `e2 : (h0.map σ).map (inclR (F` using `F) (E := E) (AF F)) = (incM F h0).map (cA σ) := by`.

Use extensionality with `i j`. Conclude with `(GlobalTheory.ThK.IsoPhase.cA_inclR σ _).symm`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, e2]`. Conclude with `e`. Take `⟨v, hvdef⟩ : ∃ v : Fin (a + (b + 2)) → E, v = h0 *ᵥ H'.x` from `⟨_, rfl⟩`.

Establish `hvv : form σ G.W.J v v = 0` using `by rw [hvdef, form_mulVec, hu]; exact hA.xx`. Establish `hvx : form σ G.W.J v H'.x = 0`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[GlobalTheory.ThK.IsoPhase.inclR_form, map_zero]`. Establish `e : incV F v = mat t⁻¹ *ᵥ incV F H'.x` using `by rw [hmti, GlobalTheory.ThK.IsoPhase.incM_mulVec_incV, hvdef]`.

Rewrite using `[e]`. Conclude with `hO`. Establish `hspan : ∀ w : Fin (a + (b + 2)) → E, ∃ (α : E) (z : Fin (a + b) → E) (β : E), w = α • H'.x + H'.ι *ᵥ z + β • H'.y`. Introduce `w`. Set `S : Submodule E (Fin (a + (b + 2)) → E)` to `Submodule.span E {H'.x} ⊔ LinearMap.range (Matrix.mulVecLin H'.ι) ⊔ Submodule.span E {H'.y}`.

Establish `hLS : (G.W.L : Set (Fin (a + (b + 2)) → E)) ⊆ S`. Introduce `u hu`. Take `⟨s, r, z, -, -, -, rfl⟩` from `hA.split u hu`. Conclude with `Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.smul_mem _ s (Submodule.mem_span_singleton_self _)))) (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨z, rfl⟩))) (Submodule.mem_sup_right (Submodule.smul_mem _ r (Submodule.mem_s …`. Establish `hw : w ∈ S`.

Establish `h2 : Submodule.span E (G.W.L : Set (Fin (a + (b + 2)) → E)) ≤ S` using `Submodule.span_le.2 hLS`. Rewrite `h2` using `[hT.geo.hW.lat.span_eq_top]`. Conclude with `h2 Submodule.mem_top`. Take `⟨p, hp, q, hq, rfl⟩` from `Submodule.mem_sup.1 hw`. Take `⟨p1, hp1, p2, hp2, rfl⟩` from `Submodule.mem_sup.1 hp`.

Take `⟨α, rfl⟩` from `Submodule.mem_span_singleton.1 hp1`. Take `⟨β, rfl⟩` from `Submodule.mem_span_singleton.1 hq`. Take `⟨z, rfl⟩` from `hp2`. Conclude with `⟨α, z, β, rfl⟩`. Take `⟨α, z, β, hv⟩` from `hspan v`.

Establish `hyx : form σ G.W.J H'.y H'.x = -1` using `by rw [form_swap σ hσ G.W.J hskew H'.x H'.y, hA.xy, map_one]`. Establish `hιx : form σ G.W.J (H'.ι *ᵥ z) H'.x = 0` using `(hA.orth z).1`. Establish `hβ : β = 0`. Establish `e` using `hvx`. Rewrite `e` using `[hv, form_add_left, form_add_left, form_smul_left, form_smul_left, hA.xx, hιx, hyx]`.

Take the linear combination `(-1 : E) * e`. Substitute `hβ` using the available equality. Establish `hxv : form σ G.W.J H'.x v = 0` using `by rw [form_swap σ hσ G.W.J hskew v H'.x, hvx, map_zero, neg_zero]`. Establish `hxι : form σ G.W.J H'.x (H'.ι *ᵥ z) = 0`. Rewrite using `[form_swap σ hσ G.W.J hskew (H'.ι *ᵥ z) H'.x, hιx, map_zero, neg_zero]`.

Establish `h2 : form σ G.W.J v (H'.ι *ᵥ z) = form σ G.W.J (H'.ι *ᵥ z) (H'.ι *ᵥ z)`. Rewrite using `[hv, form_add_left, form_add_left, form_smul_left, form_smul_left, hxι]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : form σ G.W.J (H'.ι *ᵥ z) v = -σ (form σ G.W.J (H'.ι *ᵥ z) (H'.ι *ᵥ z))`. Rewrite using `[form_swap σ hσ G.W.J hskew v (H'.ι *ᵥ z), h2]`.

Establish `h4 : form σ G.W.J v v = form σ G.W.J (α • H'.x + H'.ι *ᵥ z + (0 : E) • H'.y) v` using `by rw [← hv]`. Rewrite `h4` using `[form_add_left, form_add_left, form_smul_left, form_smul_left, hxv, h3]`. Establish `h5 : σ (form σ G.W.J (H'.ι *ᵥ z) (H'.ι *ᵥ z)) = 0` using `by linear_combination h4 - hvv`. Establish `hιι : form σ G.W.J (H'.ι *ᵥ z) (H'.ι *ᵥ z) = 0` using `by rw [← hσ (form σ G.W.J _ _), h5, map_zero]`. Use `⟨z, ?_, ?_⟩` and prove the remaining obligations.

Introduce `hz`. Substitute `hz` using the available equality. Establish `hv0 : v = α • H'.x` using `by rw [hv]; simp`. Establish `hgv : (g0 : Matrix _ _ E) *ᵥ v = H'.x`. Rewrite using `[hvdef, hh0, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`.

Establish `hx0 : H'.x ≠ 0`. Introduce `h`. Establish `e` using `hA.xy`. Rewrite `e` using `[h, form_zero_left]`. Conclude with `zero_ne_one e`.

Establish `hα : α ≠ 0`. Introduce and unpack `rfl`. Apply `hx0` to reduce the goal to its premises. Rewrite using `[← hgv, hv0, zero_smul, Matrix.mulVec_zero]`. Establish `hgx : (g0 : Matrix _ _ E) *ᵥ H'.x = α⁻¹ • H'.x`.

Rewrite `hgv` using `[hv0, Matrix.mulVec_smul]`. Rewrite using `[← hgv, smul_smul, inv_mul_cancel₀ hα, one_smul, hgv]`. Apply `hnS` to reduce the goal to its premises. Use `⟨Units.map (inclR (F := F) (E := E) (AF F)).toMonoidHom (Units.mk0 α⁻¹ (inv_ne_zero hα)), ?_⟩` and prove the remaining obligations. Rewrite using `[hmt, GlobalTheory.ThK.IsoPhase.incM_mulVec_incV, hgx]`.

Use function extensionality and compare the values at `i`. Simplify using `[incV, smul_eq_mul, map_mul]`. Rewrite using `[← hA.gram, ← form_mulVec]`. Conclude with `hιι`.
-/
theorem exists_isotropic_of_mid : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ X om om', IsTriple B G X om om' →
    ∀ T : Set (UA σ G.W.J), T ⊆ ratU σ G.W.J → ∀ t ∈ GlobalTheory.ConeSmallSer.midSet H'.x T, ∃ z : Fin (a + b) → E, z ≠ 0 ∧ form σ G₁.W.J z z = 0 := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' hT T hTs t ht
  obtain ⟨htT, hnS, hO⟩ := ht
  have hσ : ∀ x, σ (σ x) = x := by
    intro e
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hT.base.cm.2.2.2, hT.base.cm.2.2.2, star_star]
  have hA := hC.hH'
  have hskew := hT.geo.hW.skew
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) := by
    haveI : Nontrivial (AF F) := inferInstanceAs (Nontrivial (Ainf F × Af F))
    exact Algebra.TensorProduct.includeRight_injective (algebraMap F (AF F)).injective
  have htr : t ∈ ratU σ G.W.J := hTs htT
  have h1 := Subgroup.mem_subgroupOf.1 htr
  rw [MonoidHom.mem_range] at h1
  obtain ⟨g0, hg0⟩ := h1
  have hmt : mat t = incM F (g0 : Matrix (Fin (a + (b + 2))) (Fin (a + (b + 2))) E) := by
    unfold mat
    rw [← hg0]; rfl
  obtain ⟨h0, hh0⟩ : ∃ h0 : Matrix (Fin (a + (b + 2))) (Fin (a + (b + 2))) E, h0 = ↑g0⁻¹ := ⟨_, rfl⟩
  have hmti : mat t⁻¹ = incM F h0 := by
    unfold mat
    rw [Subgroup.coe_inv, ← hg0, ← map_inv, hh0]; rfl
  have hu : h0ᵀ * G.W.J * h0.map σ = G.W.J := by
    have e : (mat t⁻¹)ᵀ * incM F G.W.J * (mat t⁻¹).map (cA σ) = incM F G.W.J := (t⁻¹).2
    rw [hmti] at e
    apply Matrix.map_injective hinj
    show (h0ᵀ * G.W.J * h0.map σ).map (inclR (F := F) (E := E) (AF F)) = G.W.J.map (inclR (F := F) (E := E) (AF F))
    have e2 : (h0.map σ).map (inclR (F := F) (E := E) (AF F)) = (incM F h0).map (cA σ) := by
      ext i j; exact (GlobalTheory.ThK.IsoPhase.cA_inclR σ _).symm
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, e2]
    exact e
  obtain ⟨v, hvdef⟩ : ∃ v : Fin (a + (b + 2)) → E, v = h0 *ᵥ H'.x := ⟨_, rfl⟩
  have hvv : form σ G.W.J v v = 0 := by rw [hvdef, form_mulVec, hu]; exact hA.xx
  have hvx : form σ G.W.J v H'.x = 0 := by
    apply hinj
    rw [GlobalTheory.ThK.IsoPhase.inclR_form, map_zero]
    have e : incV F v = mat t⁻¹ *ᵥ incV F H'.x := by rw [hmti, GlobalTheory.ThK.IsoPhase.incM_mulVec_incV, hvdef]
    rw [e]; exact hO
  have hspan : ∀ w : Fin (a + (b + 2)) → E, ∃ (α : E) (z : Fin (a + b) → E) (β : E),
      w = α • H'.x + H'.ι *ᵥ z + β • H'.y := by
    intro w
    let S : Submodule E (Fin (a + (b + 2)) → E) :=
      Submodule.span E {H'.x} ⊔ LinearMap.range (Matrix.mulVecLin H'.ι) ⊔ Submodule.span E {H'.y}
    have hLS : (G.W.L : Set (Fin (a + (b + 2)) → E)) ⊆ S := by
      intro u hu
      obtain ⟨s, r, z, -, -, -, rfl⟩ := hA.split u hu
      exact Submodule.add_mem _ (Submodule.add_mem _
        (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.smul_mem _ s (Submodule.mem_span_singleton_self _))))
        (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨z, rfl⟩)))
        (Submodule.mem_sup_right (Submodule.smul_mem _ r (Submodule.mem_span_singleton_self _)))
    have hw : w ∈ S := by
      have h2 : Submodule.span E (G.W.L : Set (Fin (a + (b + 2)) → E)) ≤ S := Submodule.span_le.2 hLS
      rw [hT.geo.hW.lat.span_eq_top] at h2
      exact h2 Submodule.mem_top
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hw
    obtain ⟨p1, hp1, p2, hp2, rfl⟩ := Submodule.mem_sup.1 hp
    obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.1 hp1
    obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.1 hq
    obtain ⟨z, rfl⟩ := hp2
    exact ⟨α, z, β, rfl⟩
  obtain ⟨α, z, β, hv⟩ := hspan v
  have hyx : form σ G.W.J H'.y H'.x = -1 := by rw [form_swap σ hσ G.W.J hskew H'.x H'.y, hA.xy, map_one]
  have hιx : form σ G.W.J (H'.ι *ᵥ z) H'.x = 0 := (hA.orth z).1
  have hβ : β = 0 := by
    have e := hvx
    rw [hv, form_add_left, form_add_left, form_smul_left, form_smul_left, hA.xx, hιx, hyx] at e
    linear_combination (-1 : E) * e
  subst hβ
  have hxv : form σ G.W.J H'.x v = 0 := by rw [form_swap σ hσ G.W.J hskew v H'.x, hvx, map_zero, neg_zero]
  have hxι : form σ G.W.J H'.x (H'.ι *ᵥ z) = 0 := by
    rw [form_swap σ hσ G.W.J hskew (H'.ι *ᵥ z) H'.x, hιx, map_zero, neg_zero]
  have h2 : form σ G.W.J v (H'.ι *ᵥ z) = form σ G.W.J (H'.ι *ᵥ z) (H'.ι *ᵥ z) := by
    rw [hv, form_add_left, form_add_left, form_smul_left, form_smul_left, hxι]; ring
  have h3 : form σ G.W.J (H'.ι *ᵥ z) v = -σ (form σ G.W.J (H'.ι *ᵥ z) (H'.ι *ᵥ z)) := by
    rw [form_swap σ hσ G.W.J hskew v (H'.ι *ᵥ z), h2]
  have h4 : form σ G.W.J v v = form σ G.W.J (α • H'.x + H'.ι *ᵥ z + (0 : E) • H'.y) v := by rw [← hv]
  rw [form_add_left, form_add_left, form_smul_left, form_smul_left, hxv, h3] at h4
  have h5 : σ (form σ G.W.J (H'.ι *ᵥ z) (H'.ι *ᵥ z)) = 0 := by linear_combination h4 - hvv
  have hιι : form σ G.W.J (H'.ι *ᵥ z) (H'.ι *ᵥ z) = 0 := by rw [← hσ (form σ G.W.J _ _), h5, map_zero]
  refine ⟨z, ?_, ?_⟩
  · intro hz
    subst hz
    have hv0 : v = α • H'.x := by rw [hv]; simp
    have hgv : (g0 : Matrix _ _ E) *ᵥ v = H'.x := by
      rw [hvdef, hh0, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have hx0 : H'.x ≠ 0 := by
      intro h; have e := hA.xy; rw [h, form_zero_left] at e; exact zero_ne_one e
    have hα : α ≠ 0 := by
      rintro rfl; apply hx0; rw [← hgv, hv0, zero_smul, Matrix.mulVec_zero]
    have hgx : (g0 : Matrix _ _ E) *ᵥ H'.x = α⁻¹ • H'.x := by
      rw [hv0, Matrix.mulVec_smul] at hgv
      rw [← hgv, smul_smul, inv_mul_cancel₀ hα, one_smul, hgv]
    apply hnS
    refine ⟨Units.map (inclR (F := F) (E := E) (AF F)).toMonoidHom (Units.mk0 α⁻¹ (inv_ne_zero hα)), ?_⟩
    rw [hmt, GlobalTheory.ThK.IsoPhase.incM_mulVec_incV, hgx]
    funext i
    simp [incV, smul_eq_mul, map_mul]
  · rw [← hA.gram, ← form_mulVec]; exact hιι

end GlobalTheory.ConeSmallMidJB.IsoMid
