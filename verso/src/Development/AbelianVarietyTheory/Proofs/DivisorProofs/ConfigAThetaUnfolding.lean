import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFieldFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedLocalInducedSpaceIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryMatrixSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLocalEqOfMatrixMapEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedRepExistsLocalComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawIdentityConfigAFirstStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped GlobalTheory.IndLineGL

noncomputable section

namespace GlobalTheory.IndLineGLBridge

/- English proof (translation)
Introduce `u hu`. Establish `e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1)`. Simplify using `only [mat, Subgroup.coe_mul, Units.val_mul]`. Use `noncomm_ring`. Rewrite using `[e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]`.
-/
theorem mul_mem_UAt' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n : ℕ} {Y : Spc F E n} {R : Type} [Zero R] {ev : AF F → R} {g h : UA σ Y.J}
    (hg : g ∈ UAt σ Y ev) (hh : h ∈ UAt σ Y ev) : g * h ∈ UAt σ Y ev := by
  intro u hu
  have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
    simp only [mat, Subgroup.coe_mul, Units.val_mul]; noncomm_ring
  rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]

/- English proof (translation)
Introduce `u _`. Simplify using `[mat]`.
-/
theorem one_mem_UAt' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n : ℕ} (Y : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ Y.J) ∈ UAt σ Y ev := by
  intro u _
  simp [mat]

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ v ⟨t⟩`. Establish `hT` using `hM.triple`. Establish `hT₁` using `hM₁.triple`. Take `⟨c, e, ξ₁, ξ₂, hU, hL⟩` from `GlobalTheory.T.seesaw_identity_config_a_first F E σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ v t`. Take `⟨π, hπs, hπe, hπ⟩` from `GlobalTheory.T.matched_rep_exists_local_component hK F E σ B (b + 2) a' G X om om' R Rf hM v t c`.

Take `⟨σ₁, -, -, hσ₁⟩` from `GlobalTheory.T.matched_rep_exists_local_component hK F E σ B b a' G₁ X om₁ om₁' R₁ Rf₁ hM₁ v t 1`. Establish `hα` using `(GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.α hT.chars.heckeα v t).1`. Establish `hβ` using `(GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.β hT.chars.heckeβ v t).1`. Use `choose Θ hΘU hΘ using fun x => GlobalTheory.T.local_unitary_matrix_surjective F E σ B _ G.W _ _ hT.base hT.geo.hW v t c x`. Establish `inj : ∀ h₁ ∈ UAt σ G.W (evFin F v), ∀ h₂ ∈ UAt σ G.W (evFin F v), GlobalTheory.KSplit.locMat t c h₁ = GlobalTheory.KSplit.locMat t c h₂ → h₁ = h₂`.

Introduce `h₁ hh₁ h₂ hh₂ heq`. Use `GlobalTheory.T.unitary_local_eq_of_matrix_map_eq F E σ B _ G.W _ _ hT.base hT.geo.hW v t h₁ hh₁ h₂ hh₂ ?_` and prove the remaining obligations. Establish `h2` using `congrArg (fun g : GL (Fin (b + 2 + a')) (Fv F v) => c.val * g.val * (c⁻¹).val) heq`. Simplify using `only [GlobalTheory.KSplit.locMat_val] at h2`. Simplify `h2` using `[Matrix.mul_assoc]`.

Establish `Θmul : ∀ g h, Θ (g * h) = Θ g * Θ h` using `fun g h => inj _ (hΘU _) _ (mul_mem_UAt' (hΘU g) (hΘU h)) (by rw [map_mul, hΘ, hΘ, hΘ])`. Establish `hAE` using `GlobalTheory.T.theta_action_exists hK.base`. Establish `exA : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), ∃ φ₁ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁` using `fun h hh φ hφ => by`. Take `⟨φ₁, ⟨h1, h2⟩, -⟩` from `(hAE F E σ B _ _ _ _ _ _ _ om _ _ _ _ (Inhab.pairV hT) v).1 1 (one_mem_UAt' _ _) h hh φ hφ`. Conclude with `⟨φ₁, h1, h2⟩`.

Establish `exA₁ : ∀ h ∈ UAt σ G₁.W (evFin F v), ∀ φ ∈ SB (Fin b × Fin (b + a') → Fv F v), ∃ φ₁ ∈ SB (Fin b × Fin (b + a') → Fv F v), Acts (evFin F v) (om₁ (1, h)) φ φ₁` using `fun h hh φ hφ => by`. Take `⟨φ₁, ⟨h1, h2⟩, -⟩` from `(hAE F E σ B _ _ _ _ _ _ _ om₁ _ _ _ _ (Inhab.pairV hT₁) v).1 1 (one_mem_UAt' _ _) h hh φ hφ`. Conclude with `⟨φ₁, h1, h2⟩`. Establish `ontoA : ∀ x : Rf.Pi v, ∃ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), Rf.p v φ = x` using `fun x => by`. Establish `: x ∈ (SB _).map (Rf.p v)` using `by rw [hM.fin.onto v]; trivial`.

Take `⟨φ, hφ, rfl⟩` from `this`. Conclude with `⟨φ, hφ, rfl⟩`. Establish `ontoA₁ : ∀ x : Rf₁.Pi v, ∃ φ ∈ SB (Fin b × Fin (b + a') → Fv F v), Rf₁.p v φ = x` using `fun x => by`. Establish `: x ∈ (SB _).map (Rf₁.p v)` using `by rw [hM₁.fin.onto v]; trivial`. Take `⟨φ, hφ, rfl⟩` from `this`.

Conclude with `⟨φ, hφ, rfl⟩`. Establish `hirr : σ₁.IsIrreducible` using `by haveI := hM₁.fin.nontriv v haveI : Nontrivial (Subrepresentation σ₁) := ⟨⟨⊥, ⊤, fun h0 => by`. Take `⟨x, hx⟩` from `exists_ne (0 : Rf₁.Pi v)`. Establish `: x ∈ (⊤ : Subrepresentation σ₁).toSubmodule` using `trivial`. Rewrite `this` using `[← h0]`.

Conclude with `hx this⟩⟩`. Use `⟨fun N => ?_⟩` and prove the remaining obligations. Break down `hM₁.fin.irred v N.toSubmodule (fun h hh φ hφ φ₁ hφ₁ hAct hN => by` into its components or cases. Rewrite using `[hσ₁ h hh φ hφ φ₁ hφ₁ hAct]`. Conclude with `N.apply_mem_toSubmodule _ hN) with h0 | h0`.

Use the proof step `left; exact Subrepresentation.ext (by rw [h0]; rfl)`. Use the proof step `right; exact Subrepresentation.ext (by rw [h0]; rfl)`. Use `⟨π, σ₁, chrW X.α t, chrW X.β t, ξ₁, ξ₂, e, Θ, hα.1, hβ.1, hα.2, hβ.2, hπs, hπe, hirr, fun h hh => ⟨GlobalTheory.KSplit.locMat t c h, inj _ (hΘU _) _ hh (hΘ _)⟩, fun A hA => ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `g x h`. Take `⟨φ, hφ, rfl⟩` from `ontoA x`.

Take `⟨φ₁, hφ₁, hAct⟩` from `exA (Θ g) (hΘU g) φ hφ`. Establish `e1 : π g (Rf.p v φ) = Rf.p v φ₁` using `by rw [hπ _ (hΘU g) φ hφ φ₁ hφ₁ hAct, hΘ]`. Simplify using `only [LinearMap.comp_apply, LinearMap.funLeft_apply]`. Rewrite using `[e1, hA.right (Θ g) (hΘU g) φ hφ φ₁ hφ₁ hAct (Θ h) (hΘU h), Θmul]`. Introduce `u hu x h`.

Simplify using `only [LinearMap.comp_apply, LinearMap.funLeft_apply]`. Rewrite using `[Θmul]`. Conclude with `hA.unip (Θ u) (hU _ (hΘU u) (by rw [hΘ]; exact hu)) (hΘU u) x (Θ h) (hΘU h)`. Introduce `l x h`. Simplify using `only [LinearMap.comp_apply, LinearMap.funLeft_apply]`.

Take `⟨s, h₁, hLv, hh₁, hl1, hχ⟩` from `hL l (Θ (leviEmb _ e l)) (hΘU _) (hΘ _)`. Take `⟨φ, hφ, hφe⟩` from `ontoA₁ (A x (Θ h))`. Take `⟨φ₁, hφ₁, hAct⟩` from `exA₁ h₁ hh₁ φ hφ`. Rewrite using `[Θmul, hA.levi s h₁ _ hLv (hΘU _) hh₁ φ hφ φ₁ hφ₁ hAct x (Θ h) (hΘU h) hφe.symm, hχ, ← hφe, hσ₁ h₁ hh₁ φ hφ φ₁ hφ₁ hAct, hl1]`.
-/
theorem isGLIndMap_of_isIndMap : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ v : Pl F, Nonempty (E →ₐ[F] Fv F v) →
      ∃ (π : Representation ℂ (GL (Fin (b + 2 + a')) (Fv F v)) (Rf.Pi v))
        (σ₁ : Representation ℂ (GL (Fin (b + a')) (Fv F v)) (Rf₁.Pi v)) (α₀ β₀ ξ₁ ξ₂ : (Fv F v)ˣ →* ℂˣ)
        (e : (Σ i : Fin 3, Fin (blk3 (b + a') i)) ≃ Fin (b + 2 + a'))
        (Θ : GL (Fin (b + 2 + a')) (Fv F v) → UA σ G.W.J),
        IsSmoothChar α₀ ∧ IsSmoothChar β₀ ∧ (∀ x, ‖((α₀ x : ℂˣ) : ℂ)‖ = 1) ∧ (∀ x, ‖((β₀ x : ℂˣ) : ℂ)‖ = 1) ∧
        IsSmooth π ∧ Nonempty (π.Equiv (prod₂ (detRep (Fin (b + 2)) α₀) (detRep (Fin a') β₀))) ∧
        σ₁.IsIrreducible ∧ (∀ h ∈ UAt σ G.W (evFin F v), ∃ g, Θ g = h) ∧
        ∀ A : Rf.Pi v →ₗ[ℂ] (UA σ G.W.J → Rf₁.Pi v),
          IsIndMap v om om₁ (Rf.p v) (Rf₁.p v) H' X.α ((a' : ℝ) / 2) A →
          IsGLIndMap e π σ₁ ξ₁ ξ₂ ((LinearMap.funLeft ℂ (Rf₁.Pi v) Θ).comp A) := by
  intro hK F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ v ⟨t⟩
  have hT := hM.triple
  have hT₁ := hM₁.triple
  obtain ⟨c, e, ξ₁, ξ₂, hU, hL⟩ := GlobalTheory.T.seesaw_identity_config_a_first F E σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ v t
  obtain ⟨π, hπs, hπe, hπ⟩ := GlobalTheory.T.matched_rep_exists_local_component hK F E σ B (b + 2) a' G X om om' R Rf hM v t c
  obtain ⟨σ₁, -, -, hσ₁⟩ := GlobalTheory.T.matched_rep_exists_local_component hK F E σ B b a' G₁ X om₁ om₁' R₁ Rf₁ hM₁ v t 1
  have hα := (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.α hT.chars.heckeα v t).1
  have hβ := (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.β hT.chars.heckeβ v t).1
  choose Θ hΘU hΘ using fun x => GlobalTheory.T.local_unitary_matrix_surjective F E σ B _ G.W _ _ hT.base hT.geo.hW v t c x
  have inj : ∀ h₁ ∈ UAt σ G.W (evFin F v), ∀ h₂ ∈ UAt σ G.W (evFin F v),
      GlobalTheory.KSplit.locMat t c h₁ = GlobalTheory.KSplit.locMat t c h₂ → h₁ = h₂ := by
    intro h₁ hh₁ h₂ hh₂ heq
    refine GlobalTheory.T.unitary_local_eq_of_matrix_map_eq F E σ B _ G.W _ _ hT.base hT.geo.hW v t h₁ hh₁ h₂ hh₂ ?_
    have h2 := congrArg (fun g : GL (Fin (b + 2 + a')) (Fv F v) => c.val * g.val * (c⁻¹).val) heq
    simp only [GlobalTheory.KSplit.locMat_val] at h2
    simpa [Matrix.mul_assoc] using h2
  have Θmul : ∀ g h, Θ (g * h) = Θ g * Θ h := fun g h =>
    inj _ (hΘU _) _ (mul_mem_UAt' (hΘU g) (hΘU h)) (by rw [map_mul, hΘ, hΘ, hΘ])
  have hAE := GlobalTheory.T.theta_action_exists hK.base
  have exA : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ := fun h hh φ hφ => by
    obtain ⟨φ₁, ⟨h1, h2⟩, -⟩ := (hAE F E σ B _ _ _ _ _ _ _ om _ _ _ _ (Inhab.pairV hT) v).1 1
      (one_mem_UAt' _ _) h hh φ hφ
    exact ⟨φ₁, h1, h2⟩
  have exA₁ : ∀ h ∈ UAt σ G₁.W (evFin F v), ∀ φ ∈ SB (Fin b × Fin (b + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin b × Fin (b + a') → Fv F v), Acts (evFin F v) (om₁ (1, h)) φ φ₁ := fun h hh φ hφ => by
    obtain ⟨φ₁, ⟨h1, h2⟩, -⟩ := (hAE F E σ B _ _ _ _ _ _ _ om₁ _ _ _ _ (Inhab.pairV hT₁) v).1 1
      (one_mem_UAt' _ _) h hh φ hφ
    exact ⟨φ₁, h1, h2⟩
  have ontoA : ∀ x : Rf.Pi v, ∃ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), Rf.p v φ = x := fun x => by
    have : x ∈ (SB _).map (Rf.p v) := by rw [hM.fin.onto v]; trivial
    obtain ⟨φ, hφ, rfl⟩ := this
    exact ⟨φ, hφ, rfl⟩
  have ontoA₁ : ∀ x : Rf₁.Pi v, ∃ φ ∈ SB (Fin b × Fin (b + a') → Fv F v), Rf₁.p v φ = x := fun x => by
    have : x ∈ (SB _).map (Rf₁.p v) := by rw [hM₁.fin.onto v]; trivial
    obtain ⟨φ, hφ, rfl⟩ := this
    exact ⟨φ, hφ, rfl⟩
  have hirr : σ₁.IsIrreducible := by
    haveI := hM₁.fin.nontriv v
    haveI : Nontrivial (Subrepresentation σ₁) := ⟨⟨⊥, ⊤, fun h0 => by
      obtain ⟨x, hx⟩ := exists_ne (0 : Rf₁.Pi v)
      have : x ∈ (⊤ : Subrepresentation σ₁).toSubmodule := trivial
      rw [← h0] at this
      exact hx this⟩⟩
    refine ⟨fun N => ?_⟩
    · rcases hM₁.fin.irred v N.toSubmodule (fun h hh φ hφ φ₁ hφ₁ hAct hN => by
        rw [hσ₁ h hh φ hφ φ₁ hφ₁ hAct]; exact N.apply_mem_toSubmodule _ hN) with h0 | h0
      · left; exact Subrepresentation.ext (by rw [h0]; rfl)
      · right; exact Subrepresentation.ext (by rw [h0]; rfl)
  refine ⟨π, σ₁, chrW X.α t, chrW X.β t, ξ₁, ξ₂, e, Θ, hα.1, hβ.1, hα.2, hβ.2, hπs, hπe, hirr,
    fun h hh => ⟨GlobalTheory.KSplit.locMat t c h, inj _ (hΘU _) _ hh (hΘ _)⟩, fun A hA => ⟨?_, ?_, ?_⟩⟩
  · intro g x h
    obtain ⟨φ, hφ, rfl⟩ := ontoA x
    obtain ⟨φ₁, hφ₁, hAct⟩ := exA (Θ g) (hΘU g) φ hφ
    have e1 : π g (Rf.p v φ) = Rf.p v φ₁ := by rw [hπ _ (hΘU g) φ hφ φ₁ hφ₁ hAct, hΘ]
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply]
    rw [e1, hA.right (Θ g) (hΘU g) φ hφ φ₁ hφ₁ hAct (Θ h) (hΘU h), Θmul]
  · intro u hu x h
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply]
    rw [Θmul]
    exact hA.unip (Θ u) (hU _ (hΘU u) (by rw [hΘ]; exact hu)) (hΘU u) x (Θ h) (hΘU h)
  · intro l x h
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply]
    obtain ⟨s, h₁, hLv, hh₁, hl1, hχ⟩ := hL l (Θ (leviEmb _ e l)) (hΘU _) (hΘ _)
    obtain ⟨φ, hφ, hφe⟩ := ontoA₁ (A x (Θ h))
    obtain ⟨φ₁, hφ₁, hAct⟩ := exA₁ h₁ hh₁ φ hφ
    rw [Θmul, hA.levi s h₁ _ hLv (hΘU _) hh₁ φ hφ φ₁ hφ₁ hAct x (Θ h) (hΘU h) hφe.symm, hχ, ← hφe,
      hσ₁ h₁ hh₁ φ hφ φ₁ hφ₁ hAct, hl1]

end GlobalTheory.IndLineGLBridge

end
