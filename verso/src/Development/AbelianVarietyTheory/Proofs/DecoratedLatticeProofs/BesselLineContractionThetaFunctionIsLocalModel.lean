import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousKappa
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunctionSuperpositionOrthogonalSlices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped Topology

namespace GlobalTheory.ContrModL

section SlopeTestRemainingChoices
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)

/- English proof (translation)
Establish `hm : ∀ x y, p.ι (x * y) = p.ι x * p.ι y` using `fun x y => by conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, Witness.e_ι]`. Rewrite using `[hm]`. Express the relevant statement in the definitionally equal form `_ = p.ι x * p.ι (p.π (incA D b))`. Rewrite using `[p.ι_π, ← mul_assoc, mul_comm (p.ι x) p.e, Witness.e_ι]`.
-/
theorem ι_mul_incA (x : k) (b : D.host.E) : p.ι x * incA D b = p.ι (x * p.pr b) := by
  have hm : ∀ x y, p.ι (x * y) = p.ι x * p.ι y := fun x y => by
    conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, Witness.e_ι]
  rw [hm]
  change _ = p.ι x * p.ι (p.π (incA D b))
  rw [p.ι_π, ← mul_assoc, mul_comm (p.ι x) p.e, Witness.e_ι]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, ι_mul_incA, map_sum]`.
-/
theorem map_ι_mul_rat {a b c : Type} [Fintype b] (M : Matrix a b k) (N : Matrix b c D.host.E) :
    M.map p.ι * N.map (incA D) = (M * N.map p.pr).map p.ι := by
  ext i j
  simp [Matrix.mul_apply, ι_mul_incA, map_sum]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem map_pr_eq {a b : Type} (M : Matrix a b D.host.E) : M.map p.pr = M.map (Witness.prH p) := rfl

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

/- English proof (translation)
Establish `hβ : B.o.iA.map p.pr * FA.β = F₀.β * fromRows (1 : Matrix n' n' k) (0 : Matrix Unit n' k)`. Use extensionality with `r a`. Rewrite using `[← h.1 r a]`. Simplify using `[Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, FA.βγ, Matrix.mul_one]`. Use `_ = fromRows FA.γ 0 := by`. Rewrite using `[hβ, ← Matrix.mul_assoc, F₀.γβ, Matrix.one_mul, fromRows_mul, Matrix.one_mul, Matrix.zero_mul]`.
-/
theorem core_iA {ρ : ℕ} (B : BesLev D ρ) {s : k} (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (h : p.IsCoreFrame B s FA F₀) : F₀.γ * B.o.iA.map p.pr = fromRows FA.γ (0 : Matrix Unit (Fin B.A.rank) k) := by
  have hβ : B.o.iA.map p.pr * FA.β = F₀.β * fromRows (1 : Matrix n' n' k) (0 : Matrix Unit n' k) := by
    ext r a
    rw [← h.1 r a]
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  calc F₀.γ * B.o.iA.map p.pr = F₀.γ * (B.o.iA.map p.pr * FA.β) * FA.γ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, FA.βγ, Matrix.mul_one]
    _ = fromRows FA.γ 0 := by
        rw [hβ, ← Matrix.mul_assoc, F₀.γβ, Matrix.one_mul, fromRows_mul, Matrix.one_mul, Matrix.zero_mul]

/- English proof (translation)
Establish `hA : FA.γ * B.o.qA.map p.pr * (B.o.iA.map p.pr * FA.β) = 1`. Rewrite using `[map_pr_eq, map_pr_eq, Matrix.mul_assoc, ← Matrix.mul_assoc (B.o.qA.map _), ← Matrix.map_mul, B.o.qA_iA, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, FA.γβ]`. Establish `hB : FA.γ * B.o.qA.map p.pr * B.o.iB.map p.pr = 0`. Rewrite using `[map_pr_eq, map_pr_eq, Matrix.mul_assoc, ← Matrix.map_mul, B.o.qA_iB, Matrix.map_zero _ (map_zero _), Matrix.mul_zero]`. Establish `hc : ∀ r, F₀.β r (Sum.inr ()) = s * ((B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c))) r`.

Introduce `r`. Rewrite using `[h.2 r, vecB, map_pr_eq]`. Use `congr 1`. Conclude with `(RingHom.map_mulVec (Witness.prH p) B.o.iB B.ζ r)`. Establish `hv : (FA.γ * B.o.qA.map p.pr) *ᵥ ((B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c))) = 0`.

Rewrite using `[Matrix.mulVec_mulVec, hB, Matrix.zero_mulVec]`. Generalize the expression as in `(B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c)) = v at hc hv`. Generalize the expression as in `FA.γ * B.o.qA.map p.pr = X at hA hv ⊢`. Use extensionality with `i (a | u)`. Use `congrFun (congrFun hA i) a` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_apply]`. Rewrite using `[Matrix.mul_apply, fromCols_apply_inl, ← this]`. Simplify using `only [h.1]`. Rewrite using `[Matrix.mul_apply, fromCols_apply_inr, Matrix.zero_apply]`. Simplify using `only [hc, mul_left_comm _ s, ← Finset.mul_sum]`.

Establish `h2` using `congrFun hv i`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h2`. Rewrite using `[h2, mul_zero]`.
-/
theorem core_qA {ρ : ℕ} (B : BesLev D ρ) {s : k} (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (h : p.IsCoreFrame B s FA F₀) :
    FA.γ * B.o.qA.map p.pr * F₀.β = fromCols (1 : Matrix n' n' k) (0 : Matrix n' Unit k) := by
  have hA : FA.γ * B.o.qA.map p.pr * (B.o.iA.map p.pr * FA.β) = 1 := by
    rw [map_pr_eq, map_pr_eq, Matrix.mul_assoc, ← Matrix.mul_assoc (B.o.qA.map _), ← Matrix.map_mul, B.o.qA_iA,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, FA.γβ]
  have hB : FA.γ * B.o.qA.map p.pr * B.o.iB.map p.pr = 0 := by
    rw [map_pr_eq, map_pr_eq, Matrix.mul_assoc, ← Matrix.map_mul, B.o.qA_iB, Matrix.map_zero _ (map_zero _),
      Matrix.mul_zero]
  have hc : ∀ r, F₀.β r (Sum.inr ()) = s * ((B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c))) r := by
    intro r
    rw [h.2 r, vecB, map_pr_eq]
    congr 1
    exact (RingHom.map_mulVec (Witness.prH p) B.o.iB B.ζ r)
  have hv : (FA.γ * B.o.qA.map p.pr) *ᵥ ((B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c))) = 0 := by
    rw [Matrix.mulVec_mulVec, hB, Matrix.zero_mulVec]
  generalize (B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c)) = v at hc hv
  generalize FA.γ * B.o.qA.map p.pr = X at hA hv ⊢
  ext i (a | u)
  · have := congrFun (congrFun hA i) a
    rw [Matrix.mul_apply] at this
    rw [Matrix.mul_apply, fromCols_apply_inl, ← this]
    simp only [h.1]
  · rw [Matrix.mul_apply, fromCols_apply_inr, Matrix.zero_apply]
    simp only [hc, mul_left_comm _ s, ← Finset.mul_sum]
    have h2 := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h2
    rw [h2, mul_zero]

end SlopeTestRemainingChoices
end GlobalTheory.ContrModL

namespace GlobalTheory.ContrModL

section Up
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

/- English proof (translation)
Establish `hX : FA.γ * B.o.qA.map p.pr = fromCols (1 : Matrix n' n' k) (0 : Matrix n' Unit k) * F₀.γ`. Rewrite using `[← core_qA p B FA F₀ h, Matrix.mul_assoc _ F₀.β, F₀.βγ, Matrix.mul_one]`. Establish `hx : fromCols x (0 : Matrix n Unit k) = x * fromCols (1 : Matrix n' n' k) (0 : Matrix n' Unit k)`. Rewrite using `[Matrix.mul_fromCols, Matrix.mul_one, Matrix.mul_zero]`. Rewrite using `[OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero, Place.up, Place.up, OrthDec.pA, rat, map_ι_mul_rat, Matrix.mul_assoc (FS.β * x), hX, hx]`.

Simplify using `only [Matrix.mul_assoc]`.
-/
theorem up_fromCols {ρ : ℕ} (B : BesLev D ρ) {s : k} (S : HSp D) (FA : Frame k B.A.rank n')
    (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (h : p.IsCoreFrame B s FA F₀) (x : Matrix n n' k) :
    p.up F₀ FS (fromCols x (0 : Matrix n Unit k)) = (B.o.resS S).symm (p.up FA FS x, 0) := by
  have hX : FA.γ * B.o.qA.map p.pr = fromCols (1 : Matrix n' n' k) (0 : Matrix n' Unit k) * F₀.γ := by
    rw [← core_qA p B FA F₀ h, Matrix.mul_assoc _ F₀.β, F₀.βγ, Matrix.mul_one]
  have hx : fromCols x (0 : Matrix n Unit k) = x * fromCols (1 : Matrix n' n' k) (0 : Matrix n' Unit k) := by
    rw [Matrix.mul_fromCols, Matrix.mul_one, Matrix.mul_zero]
  rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero, Place.up, Place.up, OrthDec.pA, rat, map_ι_mul_rat, Matrix.mul_assoc (FS.β * x), hX, hx]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[Place.up, Place.up, OrthDec.jA, rat, map_ι_mul_rat, Matrix.mul_assoc _ F₀.γ, core_iA p B FA F₀ h]`. Use `conv_lhs => rw [← fromCols_toCols t]`. Rewrite using `[Matrix.mul_assoc, fromCols_mul_fromRows, Matrix.mul_zero, add_zero, ← Matrix.mul_assoc]`.
-/
theorem up_jA {ρ : ℕ} (B : BesLev D ρ) {s : k} (S : HSp D) (FA : Frame k B.A.rank n')
    (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (h : p.IsCoreFrame B s FA F₀)
    (t : Matrix n (n' ⊕ Unit) k) : p.up F₀ FS t ⬝ B.o.jA = p.up FA FS t.toCols₁ := by
  rw [Place.up, Place.up, OrthDec.jA, rat, map_ι_mul_rat, Matrix.mul_assoc _ F₀.γ, core_iA p B FA F₀ h]
  conv_lhs => rw [← fromCols_toCols t]
  rw [Matrix.mul_assoc, fromCols_mul_fromRows, Matrix.mul_zero, add_zero, ← Matrix.mul_assoc]

end Up

section Pass
variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ)

/- English proof (translation)
Establish `: hO S T x 0 = 0` using `by simp [hO]`. Simplify using `[symplOH, symplO, this]`.
-/
theorem symplOH_zero_r {S T : HSp D} (x : WO S T) : symplOH S T x 0 = 0 := by
  have : hO S T x 0 = 0 := by simp [hO]
  simp [symplOH, symplO, this]

/- English proof (translation)
Simplify using `only [heisO]`. Rewrite using `[o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_r, add_zero, ← map_add, Prod.mk_add_mk, add_zero]`.
-/
theorem heis_pass {V A L : HSp D} (o : OrthDec V A L) (S : HSp D) (f : WO V S → ℂ) (a u : WO A S) (z : WO L S) :
    heisO ψ V S ((o.resS S).symm (a, 0)) f ((o.resS S).symm (u, z)) =
      ψ (symplOH A S u a) * f ((o.resS S).symm (u + a, z)) := by
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_r, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

end Pass

end GlobalTheory.ContrModL

namespace GlobalTheory.ContrModL

/- English proof (translation)
Introduce `D k _ _ _ _ p ψ hψ ρ σ B B' l S vL s hs n n' _ _ _ _ FA F₀ FS hcore T₁ hT₁ φ₀ Ξ₂ hΞ₂ v T hT`. Establish `pass : ∀ (a : WO B.A S) (Φ Φ' : SB (Matrix n n' k)), T₁ (GlobalTheory.ContractionLocal.colTens φ₀ Φ') = heisO ψ B.V₀ S ((B.o.resS S).symm (a, 0)) (T₁ (GlobalTheory.ContractionLocal.colTens φ₀ Φ)) → T Φ' = heisO ψ B.A S a (T Φ)`. Introduce `a Φ Φ' e`. Use function extensionality and compare the values at `u`. Rewrite using `[hT Φ' u, e]`.

Express the relevant statement in the definitionally equal form `_ = ψ (symplOH B.A S u a) * T Φ (u + a)`. Rewrite using `[hT Φ (u + a)]`. Unfold `GlobalTheory.Unf.contr`. Rewrite using `[← integral_const_mul]`. Use `congrArg (fun f : WO S B'.L → ℂ => ∫ w in vL.𝓕, f w ∂vL.μ) (funext fun w => ?_)` and prove the remaining obligations.

Rewrite using `[heis_pass]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨fun Φ => ?_, fun x Φ Φ' e => ?_, fun y hy Φ Φ' e => ?_⟩` and prove the remaining obligations. Use `haveI : ∀ m n, BorelSpace (Mx D m n) := fun _ _ => ⟨rfl⟩`. Use `haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) := ⟨by rw [Measure.restrict_apply_univ, vL.covol.2.2]; exact ENNReal.one_lt_top⟩`.

Take `⟨C₂, hC₂⟩` from `GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hψ Ξ₂ hΞ₂`. Establish `hc : Continuous fun w => Ξ₂ ((B'.o.resT S).symm (v, w))` using `hΞ₂.cont.comp ((OrthDec.continuous_resT_symm _ _).comp (Continuous.prodMk continuous_const continuous_id))`. Establish `hint : Integrable (fun w => Ξ₂ ((B'.o.resT S).symm (v, w))) (vL.μ.restrict vL.𝓕)` using `(integrable_const C₂).mono' hc.aestronglyMeasurable (ae_of_all _ fun w => hC₂ _)`. Establish `h` using `GlobalTheory.SuperposS.superpos_isTheta D ψ hψ B.V₀ B.A B.L S B.o (T₁ (GlobalTheory.ContractionLocal.colTens φ₀ Φ)) (hT₁.theta _) (WO S B'.L) (vL.μ.restrict vL.𝓕) (l.κ S) (fun w => Ξ₂ ((B'.o.resT S).symm (v, w))) (GlobalTheory.ContractionLocal.continuous_kappa l S).measurable hin …`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `u`. Rewrite using `[hT]`. Both sides reduce to the same expression. Use `pass (p.up FA FS x) Φ Φ' ?_` and prove the remaining obligations. Rewrite using `[← up_fromCols p B S FA F₀ FS hcore x]`.

Use `hT₁.trans _ _ _ fun t => ?_` and prove the remaining obligations. Establish `h1 : (t + fromCols x (0 : Matrix n Unit k)).toCols₁ = t.toCols₁ + x`. Use extensionality with `i j`. Simplify using `[Matrix.toCols₁]`. Establish `h2 : (fun r => (t + fromCols x (0 : Matrix n Unit k)) r (Sum.inr ())) = fun r => t r (Sum.inr ())`.

Use function extensionality and compare the values at `r`. Simplify using the standard rewrite rules. Simplify using `only [GlobalTheory.ContractionLocal.colTens_apply, e, h1, h2]`. Use `pass y Φ Φ' (hT₁.modul _ ?_ _ _ fun t => ?_)` and prove the remaining obligations. Introduce `i j`.

Rewrite using `[OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero, Matrix.mul_apply, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun c _ => by rw [← mul_assoc, hy i c]`. Simplify using `only [GlobalTheory.ContractionLocal.colTens_apply, e]`. Rewrite using `[B.o.symplO_resS S (p.up F₀ FS t), AddEquiv.apply_symm_apply]`. Rewrite using `[OrthDec.resS_apply B.o S (p.up F₀ FS t)]`.

Simplify using `only`. Rewrite using `[up_jA p B S FA F₀ FS hcore t]`. Establish `: symplO B.L S (p.up F₀ FS t ⬝ B.o.jB) 0 = 0`. Establish `h0 : hO B.L S (p.up F₀ FS t ⬝ B.o.jB) 0 = 0` using `by simp [hO]`. Simplify using `[symplO, h0]`.

Simplify using `only [this, add_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem contr_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ (T₁ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.V₀ S → ℂ)), p.IsModel ψ F₀ FS T₁ → ∀ (φ₀ : SB (n → k)) (Ξ₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ S B'.V₀ Ξ₂ → ∀ (v : WO S B'.A) (T : SB (Matrix n n' k) →ₗ[ℂ] (WO B.A S → ℂ)), (∀ Ξ₁ u, T Ξ₁ u = GlobalTheory.Unf.contr l S vL (T₁ (GlobalTheory.ContractionLocal.colTens φ₀ Ξ₁)) Ξ₂ u v) → p.IsModel ψ FA FS T := by
  intro D k _ _ _ _ p ψ hψ ρ σ B B' l S vL s hs n n' _ _ _ _ FA F₀ FS hcore T₁ hT₁ φ₀ Ξ₂ hΞ₂ v T hT

  have pass : ∀ (a : WO B.A S) (Φ Φ' : SB (Matrix n n' k)),
      T₁ (GlobalTheory.ContractionLocal.colTens φ₀ Φ') =
        heisO ψ B.V₀ S ((B.o.resS S).symm (a, 0)) (T₁ (GlobalTheory.ContractionLocal.colTens φ₀ Φ)) →
      T Φ' = heisO ψ B.A S a (T Φ) := by
    intro a Φ Φ' e
    funext u
    rw [hT Φ' u, e]
    change _ = ψ (symplOH B.A S u a) * T Φ (u + a)
    rw [hT Φ (u + a)]
    unfold GlobalTheory.Unf.contr
    rw [← integral_const_mul]
    refine congrArg (fun f : WO S B'.L → ℂ => ∫ w in vL.𝓕, f w ∂vL.μ) (funext fun w => ?_)
    rw [heis_pass]
    ring
  refine ⟨fun Φ => ?_, fun x Φ Φ' e => ?_, fun y hy Φ Φ' e => ?_⟩
  ·
    haveI : ∀ m n, BorelSpace (Mx D m n) := fun _ _ => ⟨rfl⟩
    haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) :=
      ⟨by rw [Measure.restrict_apply_univ, vL.covol.2.2]; exact ENNReal.one_lt_top⟩
    obtain ⟨C₂, hC₂⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hψ Ξ₂ hΞ₂
    have hc : Continuous fun w => Ξ₂ ((B'.o.resT S).symm (v, w)) :=
      hΞ₂.cont.comp ((OrthDec.continuous_resT_symm _ _).comp (Continuous.prodMk continuous_const continuous_id))
    have hint : Integrable (fun w => Ξ₂ ((B'.o.resT S).symm (v, w))) (vL.μ.restrict vL.𝓕) :=
      (integrable_const C₂).mono' hc.aestronglyMeasurable (ae_of_all _ fun w => hC₂ _)
    have h := GlobalTheory.SuperposS.superpos_isTheta D ψ hψ B.V₀ B.A B.L S B.o (T₁ (GlobalTheory.ContractionLocal.colTens φ₀ Φ))
      (hT₁.theta _) (WO S B'.L) (vL.μ.restrict vL.𝓕) (l.κ S) (fun w => Ξ₂ ((B'.o.resT S).symm (v, w)))
      (GlobalTheory.ContractionLocal.continuous_kappa l S).measurable hint
    convert h using 1
    funext u
    rw [hT]
    rfl
  ·
    refine pass (p.up FA FS x) Φ Φ' ?_
    rw [← up_fromCols p B S FA F₀ FS hcore x]
    refine hT₁.trans _ _ _ fun t => ?_
    have h1 : (t + fromCols x (0 : Matrix n Unit k)).toCols₁ = t.toCols₁ + x := by
      ext i j; simp [Matrix.toCols₁]
    have h2 : (fun r => (t + fromCols x (0 : Matrix n Unit k)) r (Sum.inr ())) = fun r => t r (Sum.inr ()) := by
      funext r; simp
    simp only [GlobalTheory.ContractionLocal.colTens_apply, e, h1, h2]
  ·
    refine pass y Φ Φ' (hT₁.modul _ ?_ _ _ fun t => ?_)
    · intro i j
      rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [← mul_assoc, hy i c]
    · simp only [GlobalTheory.ContractionLocal.colTens_apply, e]
      rw [B.o.symplO_resS S (p.up F₀ FS t), AddEquiv.apply_symm_apply]
      rw [OrthDec.resS_apply B.o S (p.up F₀ FS t)]
      simp only
      rw [up_jA p B S FA F₀ FS hcore t]
      have : symplO B.L S (p.up F₀ FS t ⬝ B.o.jB) 0 = 0 := by
        have h0 : hO B.L S (p.up F₀ FS t ⬝ B.o.jB) 0 = 0 := by simp [hO]
        simp [symplO, h0]
      simp only [this, add_zero]
      ring

end GlobalTheory.ContrModL

end
