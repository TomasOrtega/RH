import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumInvariantRationalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralCompactInvariant

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.ThetaAdelicInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Substitute `hk` using the available equality. Introduce `a`. Establish `e` using `h a`. Establish `e'` using `h' a`. Rewrite using `[MonoidHom.div_apply, Circle.coe_div, e, e']`.

Use `split_ifs`. Simplify using the standard rewrite rules. Rewrite using `[pow_add]`. Apply the tactic sequence `rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring`.
-/
theorem resEtaPow_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, ⟨h.chars.heckeα.1.div' h.chars.heckeβ.1, fun x => by simp only [MonoidHom.div_apply, h.chars.heckeα.2 x, h.chars.heckeβ.2 x, div_self']⟩, h.chars.resα, resEtaPow_div h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩`.
-/
theorem isPair_small {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα,
    ⟨h.chars.heckeα.1.div' h.chars.heckeβ.1, fun x => by
      simp only [MonoidHom.div_apply, h.chars.heckeα.2 x, h.chars.heckeβ.2 x, div_self']⟩, h.chars.resα,
    resEtaPow_div h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, φ, h1, h2, -, rfl⟩`. Conclude with `GlobalTheory.TensUniq.pure_mem_schA f φ h1 ((h2.and hM.std).mono fun w hw => hw.1.trans hw.2)`.
-/
theorem so_le_schA {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ)
    {v : Pl F} (t : E →ₐ[F] Fv F v) : M.So ψ t ≤ schA F _ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, φ, h1, h2, -, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ h1 ((h2.and hM.std).mono fun w hw => hw.1.trans hw.2)

/- English proof (translation)
Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Use `haveI : IsTopologicalGroup (UA σ X.J) := inferInstanceAs (IsTopologicalGroup (UG (cA σ) (incM F X.J)))`. Use `haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩`. Use `haveI : Countable (ratU σ X.J) := GlobalTheory.ThetaKInv.countable_ratU σ X.J`. Use `haveI hH : M.μ.IsHaarMeasure := hP.good.haar`.

Use `haveI hR : M.μ.IsMulRightInvariant := GlobalTheory.ThetaKInv.isMulRightInvariant σ hP.base.cm X.J hP.herm.herm (GlobalTheory.ThetaKInv.det_ne_zero_of_isHerm hP.herm) M.μ`. Use `haveI : MeasurableConstSMul (ratU σ X.J) (UA σ X.J) := ⟨fun γ => measurable_const_mul (γ.1 : UA σ X.J)⟩`. Use `haveI : SMulInvariantMeasure (ratU σ X.J) (UA σ X.J) M.μ := ⟨fun γ A _ => measure_preimage_mul M.μ γ.1 A⟩`. Set `f : UA σ X.J → ℂ` to `fun g => theta om Φ g h`. Establish `hf : ∀ (γ : ratU σ X.J) (x : UA σ X.J), f (γ • x) = f x` using `fun γ x => by`.

Establish `e : om (γ.1 * x, h) Φ = om (γ.1, 1) (om (x, h) Φ)`. Rewrite using `[← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]`. Express the relevant statement in the definitionally equal form `thetaSum F (om (γ.1 * x, h) Φ) = thetaSum F (om (x, h) Φ)`. Rewrite using `[e]`. Conclude with `GlobalTheory.T.thetaSum_invariant_rational_unitary hKP F E σ B n d X W M χX χW om r s r' s' hP γ.1 γ.2 1 (one_mem _) _ (hP.weil.isUSplitting.pres _ _ hΦ)`.

Establish `hcomp : ∀ g, theta om (om (k, 1) Φ) g h = f (g * k)`. Introduce `g`. Simplify using `only [theta, f]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]`. Establish `hmp : MeasurePreserving (fun x : UA σ X.J => x * k) M.μ M.μ` using `measurePreserving_mul_right M.μ k`.

Establish `hemb : MeasurableEmbedding (fun x : UA σ X.J => x * k)` using `(MeasurableEquiv.mulRight k).measurableEmbedding`. Establish `hdom : IsFundamentalDomain (ratU σ X.J) ((fun x : UA σ X.J => x * k) '' M.dom) M.μ`. Use `hP.good.dom.image_of_equiv (Equiv.mulRight k) (measurePreserving_mul_right M.μ k⁻¹).quasiMeasurePreserving (Equiv.refl _) (fun γ x => by simp [Subgroup.smul_def, mul_assoc])` as an intermediate fact. Simplify using `using this`. Unfold `Model.I`.

Repeatedly rewrite using `[hcomp]`. Rewrite using `[← hmp.setIntegral_image_emb hemb f M.dom]`. Conclude with `hdom.setIntegral_eq hP.good.dom hf`.
-/
theorem integral_invariant (hKP : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
    {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s')
    (k : UA σ X.J) {Φ : (Fin n × Fin d → AF F) → ℂ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) (h : UA σ W.J) :
    M.I om (om (k, 1) Φ) h = M.I om Φ h := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (UA σ X.J) := inferInstanceAs (IsTopologicalGroup (UG (cA σ) (incM F X.J)))
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : Countable (ratU σ X.J) := GlobalTheory.ThetaKInv.countable_ratU σ X.J
  haveI hH : M.μ.IsHaarMeasure := hP.good.haar
  haveI hR : M.μ.IsMulRightInvariant := GlobalTheory.ThetaKInv.isMulRightInvariant σ hP.base.cm X.J hP.herm.herm
    (GlobalTheory.ThetaKInv.det_ne_zero_of_isHerm hP.herm) M.μ
  haveI : MeasurableConstSMul (ratU σ X.J) (UA σ X.J) :=
    ⟨fun γ => measurable_const_mul (γ.1 : UA σ X.J)⟩
  haveI : SMulInvariantMeasure (ratU σ X.J) (UA σ X.J) M.μ :=
    ⟨fun γ A _ => measure_preimage_mul M.μ γ.1 A⟩
  let f : UA σ X.J → ℂ := fun g => theta om Φ g h
  have hf : ∀ (γ : ratU σ X.J) (x : UA σ X.J), f (γ • x) = f x := fun γ x => by
    have e : om (γ.1 * x, h) Φ = om (γ.1, 1) (om (x, h) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
    change thetaSum F (om (γ.1 * x, h) Φ) = thetaSum F (om (x, h) Φ)
    rw [e]
    exact GlobalTheory.T.thetaSum_invariant_rational_unitary hKP F E σ B n d X W M χX χW om r s r' s' hP γ.1 γ.2 1 (one_mem _) _
      (hP.weil.isUSplitting.pres _ _ hΦ)
  have hcomp : ∀ g, theta om (om (k, 1) Φ) g h = f (g * k) := by
    intro g
    simp only [theta, f]
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hmp : MeasurePreserving (fun x : UA σ X.J => x * k) M.μ M.μ := measurePreserving_mul_right M.μ k
  have hemb : MeasurableEmbedding (fun x : UA σ X.J => x * k) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have hdom : IsFundamentalDomain (ratU σ X.J) ((fun x : UA σ X.J => x * k) '' M.dom) M.μ := by
    have := hP.good.dom.image_of_equiv (Equiv.mulRight k)
      (measurePreserving_mul_right M.μ k⁻¹).quasiMeasurePreserving (Equiv.refl _)
      (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
    simpa using this
  unfold Model.I
  simp_rw [hcomp]
  rw [← hmp.setIntegral_image_emb hemb f M.dom]
  exact hdom.setIntegral_eq hP.good.dom hf

/- English proof (translation)
Introduce `hKP _ _ _ _ _ _ _ _ B _ _ _ _ _ _ hT _ hΦ g h` and use `integral_invariant hKP.base (isPair_small hT) g (so_le_schA hT.geo.hM' B.τ₁ hΦ) h`.
-/
theorem small_integral_invariant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ Φ ∈ G.M'.So B.ψ B.τ₁, ∀ (g : UA σ G.V'.J) (h : UA σ G.W.J), G.M'.I om' (om' (g, 1) Φ) h = G.M'.I om' Φ h :=
  fun hKP _ _ _ _ _ _ _ _ B _ _ _ _ _ _ hT _ hΦ g h =>
    integral_invariant hKP.base (isPair_small hT) g (so_le_schA hT.geo.hM' B.τ₁ hΦ) h

end GlobalTheory.ThetaAdelicInv

end
