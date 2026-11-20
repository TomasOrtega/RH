import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsJacMapZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedLocalInducedSpaceIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBThetaDescentIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetMapIntertwinerUniqueStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IndLine.SplitB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField E] in

/- English proof (translation)
Introduce `u _` and use `by rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero]`.
-/
theorem one_mem_UAt' {n : ℕ} (Y : Spc F E n) (v : Pl F) : (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := fun u _ => by
  rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero]

/- English proof (translation)
Use `⟨?_, fun x => ?_⟩` and prove the remaining obligations. Use `show Continuous fun x => χ₁ x / χ₂ x`. Conclude with `h₁.1.div' h₂.1`. Rewrite using `[MonoidHom.div_apply, h₁.2 x, h₂.2 x, div_one]`.
-/
theorem isHecke_div' {χ₁ χ₂ : Chr F E} (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) := by
  refine ⟨?_, fun x => ?_⟩
  · show Continuous fun x => χ₁ x / χ₂ x
    exact h₁.1.div' h₂.1
  · rw [MonoidHom.div_apply, h₁.2 x, h₂.2 x, div_one]

/- English proof (translation)
Introduce `u`. Rewrite using `[MonoidHom.div_apply, Circle.coe_div, h u, h' u]`. Use `split_ifs`. Simplify using the standard rewrite rules. Rewrite using `[div_eq_mul_inv, ← inv_pow, inv_neg_one, ← pow_add]`.
-/
theorem resEtaPow_div' {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E}
    {m m' : ℕ} (h : ResEtaPow K χ m) (h' : ResEtaPow K χ' m') : ResEtaPow K (χ / χ') (m + m') := by
  intro u
  rw [MonoidHom.div_apply, Circle.coe_div, h u, h' u]
  split_ifs
  · simp
  · rw [div_eq_mul_inv, ← inv_pow, inv_neg_one, ← pow_add]

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, isHecke_div' h.chars.heckeβ h.chars.heckeα, h.chars.resβ, resEtaPow_div' h.chars.resβ h.chars.resα, h.weil⟩`.
-/
theorem isPair_big' {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, isHecke_div' h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
    resEtaPow_div' h.chars.resβ h.chars.resα, h.weil⟩

end GlobalTheory.IndLine.SplitB

open GlobalTheory.IndLine.SplitB in

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ v ⟨t⟩ A A' hA hA'`. Take `⟨c, c₁, hα, hβ, hG⟩` from `GlobalTheory.T.config_b_theta_descent_identity hK F E σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ v t`. Take `⟨eB, heB⟩` from `GlobalTheory.T.matched_local_induced_space_iso hK F E σ B a (b + 2) G X om om' R Rf hM v t c`. Take `⟨eS, heS⟩` from `GlobalTheory.T.matched_local_induced_space_iso hK F E σ B a b G₁ X om₁ om₁' R₁ Rf₁ hM₁ v t c₁`. Establish `hlt : b + 2 < a` using `hM.triple.geo.lt`.

Establish `hx` using `(GlobalTheory.T.theta_action_exists hK.base F E σ B _ _ _ _ _ _ _ om _ _ _ _ (isPair_big' hM.triple) v).1`. Establish `h1` using `one_mem_UAt' (σ := σ) G.W v`. Establish `dtm : ∀ x, ∀ h ∈ UAt σ G.W (evFin F v), ∃ y, ∀ A₀ : Rf.Pi v →ₗ[ℂ] (UA σ G.W.J → Rf₁.Pi v), IsIndMap v om om₁ (Rf.p v) (Rf₁.p v) H' X.β ((a : ℝ) / 2) A₀ → A₀ x h = A₀ y 1`. Introduce `x h hh`. Take `⟨φ, hφ, rfl⟩ : x ∈ (SB _).map (Rf.p v)` from `(hM.fin.onto v).symm ▸ Submodule.mem_top`.

Take `⟨φ₁, ⟨hφ₁, H₁⟩, -⟩` from `hx 1 (one_mem_UAt' G.V v) h hh φ hφ`. Use `⟨Rf.p v φ₁, fun A₀ hA₀ => ?_⟩` and prove the remaining obligations. Rewrite using `[hA₀.right h hh φ hφ φ₁ hφ₁ H₁ 1 h1, one_mul]`. Establish `jac : ∀ A₀ : Rf.Pi v →ₗ[ℂ] (UA σ G.W.J → Rf₁.Pi v), IsIndMap v om om₁ (Rf.p v) (Rf₁.p v) H' X.β ((a : ℝ) / 2) A₀ → GlobalTheory.JacLine.IsJacMap a b (chrW X.α t) (chrW X.β t) (fun x => (chrW X.β t x : ℂ) * GlobalTheory.SplitFlip.apow x ((a : ℂ) / 2)) (fun y => (chrW X.β t y : ℂ) …` using `ℂ) (φ := fun _ : UA σ G.W.J => Rf₁.Pi v) 1) ∘ₗ A₀) ∘ₗ eB.symm.toLinearMap) := by`. Introduce `A₀ hA₀`.

Use `hG eB eS heB heS _ (fun u hu huv ψ hψ ψ₁ hψ₁ H₁ => ?_) (fun s h₁ m hL hm hh₁ ψ hψ ψ₁ hψ₁ H₁ θ hθ θ₁ hθ₁ H₂ he => ?_)` and prove the remaining obligations. Use `show A₀ (Rf.p v ψ₁) 1 = A₀ (Rf.p v ψ) 1`. Rewrite using `[hA₀.right u huv ψ hψ ψ₁ hψ₁ H₁ 1 h1, one_mul]`. Use `hA₀.unip u hu huv (Rf.p v ψ) 1 h1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis.

Use `show A₀ (Rf.p v ψ₁) 1 = _`. Rewrite using `[hA₀.right m hm ψ hψ ψ₁ hψ₁ H₁ 1 h1, one_mul]`. Use `hA₀.levi s h₁ m hL hm hh₁ θ hθ θ₁ hθ₁ H₂ (Rf.p v ψ) 1 h1 he` as an intermediate fact. Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis. Break down `GlobalTheory.T.jacquet_map_intertwiner_unique hK (Fv F v) a b _ _ hα hβ hlt _ _ (jac A hA) (jac A' hA') with h0 | ⟨k, hk⟩` into its components or cases.

Use `left`. Introduce `x h hh`. Take `⟨y, hy⟩` from `dtm x h hh`. Rewrite using `[hy A hA]`. Use `LinearMap.congr_fun h0 (eB y)` as an intermediate fact.

Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.zero_apply, LinearEquiv.map_eq_zero_iff] at this`. Conclude with `this`. Use `right`. Use `⟨k, fun x h hh => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `dtm x h hh`.

Rewrite using `[hy A hA, hy A' hA']`. Use `LinearMap.congr_fun hk (eB y)` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.smul_apply, ← LinearEquiv.map_smul] at this`. Conclude with `eS.injective this`.
-/
theorem GlobalTheory.IndLine.SplitB.indLineFin_beta_of_isMatched_of_nonempty_algHom : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ v : Pl F, Nonempty (E →ₐ[F] Fv F v) → IndLineFin v om om₁ (Rf.p v) (Rf₁.p v) H' X.β ((a : ℝ) / 2) := by
  intro hK F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ v ⟨t⟩ A A' hA hA'
  obtain ⟨c, c₁, hα, hβ, hG⟩ := GlobalTheory.T.config_b_theta_descent_identity hK F E σ B a b G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ v t
  obtain ⟨eB, heB⟩ := GlobalTheory.T.matched_local_induced_space_iso hK F E σ B a (b + 2) G X om om' R Rf hM v t c
  obtain ⟨eS, heS⟩ := GlobalTheory.T.matched_local_induced_space_iso hK F E σ B a b G₁ X om₁ om₁' R₁ Rf₁ hM₁ v t c₁
  have hlt : b + 2 < a := hM.triple.geo.lt
  have hx := (GlobalTheory.T.theta_action_exists hK.base F E σ B _ _ _ _ _ _ _ om _ _ _ _ (isPair_big' hM.triple) v).1
  have h1 := one_mem_UAt' (σ := σ) G.W v

  have dtm : ∀ x, ∀ h ∈ UAt σ G.W (evFin F v), ∃ y, ∀ A₀ : Rf.Pi v →ₗ[ℂ] (UA σ G.W.J → Rf₁.Pi v),
      IsIndMap v om om₁ (Rf.p v) (Rf₁.p v) H' X.β ((a : ℝ) / 2) A₀ → A₀ x h = A₀ y 1 := by
    intro x h hh
    obtain ⟨φ, hφ, rfl⟩ : x ∈ (SB _).map (Rf.p v) := (hM.fin.onto v).symm ▸ Submodule.mem_top
    obtain ⟨φ₁, ⟨hφ₁, H₁⟩, -⟩ := hx 1 (one_mem_UAt' G.V v) h hh φ hφ
    refine ⟨Rf.p v φ₁, fun A₀ hA₀ => ?_⟩
    rw [hA₀.right h hh φ hφ φ₁ hφ₁ H₁ 1 h1, one_mul]

  have jac : ∀ A₀ : Rf.Pi v →ₗ[ℂ] (UA σ G.W.J → Rf₁.Pi v),
      IsIndMap v om om₁ (Rf.p v) (Rf₁.p v) H' X.β ((a : ℝ) / 2) A₀ →
      GlobalTheory.JacLine.IsJacMap a b (chrW X.α t) (chrW X.β t)
        (fun x => (chrW X.β t x : ℂ) * GlobalTheory.SplitFlip.apow x ((a : ℂ) / 2))
        (fun y => (chrW X.β t y : ℂ) * GlobalTheory.SplitFlip.apow y (-(a : ℂ) / 2))
        (eS.toLinearMap ∘ₗ ((LinearMap.proj (R := ℂ) (φ := fun _ : UA σ G.W.J => Rf₁.Pi v) 1) ∘ₗ A₀) ∘ₗ
          eB.symm.toLinearMap) := by
    intro A₀ hA₀
    refine hG eB eS heB heS _ (fun u hu huv ψ hψ ψ₁ hψ₁ H₁ => ?_) (fun s h₁ m hL hm hh₁ ψ hψ ψ₁ hψ₁ H₁ θ hθ θ₁ hθ₁ H₂ he => ?_)
    · show A₀ (Rf.p v ψ₁) 1 = A₀ (Rf.p v ψ) 1
      rw [hA₀.right u huv ψ hψ ψ₁ hψ₁ H₁ 1 h1, one_mul]
      have := hA₀.unip u hu huv (Rf.p v ψ) 1 h1
      rwa [mul_one] at this
    · show A₀ (Rf.p v ψ₁) 1 = _
      rw [hA₀.right m hm ψ hψ ψ₁ hψ₁ H₁ 1 h1, one_mul]
      have := hA₀.levi s h₁ m hL hm hh₁ θ hθ θ₁ hθ₁ H₂ (Rf.p v ψ) 1 h1 he
      rwa [mul_one] at this
  rcases GlobalTheory.T.jacquet_map_intertwiner_unique hK (Fv F v) a b _ _ hα hβ hlt _ _ (jac A hA) (jac A' hA') with h0 | ⟨k, hk⟩
  · left
    intro x h hh
    obtain ⟨y, hy⟩ := dtm x h hh
    rw [hy A hA]
    have := LinearMap.congr_fun h0 (eB y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.zero_apply,
      LinearEquiv.map_eq_zero_iff] at this
    exact this
  · right
    refine ⟨k, fun x h hh => ?_⟩
    obtain ⟨y, hy⟩ := dtm x h hh
    rw [hy A hA, hy A' hA']
    have := LinearMap.congr_fun hk (eB y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.smul_apply,
      ← LinearEquiv.map_smul] at this
    exact eS.injective this

end
