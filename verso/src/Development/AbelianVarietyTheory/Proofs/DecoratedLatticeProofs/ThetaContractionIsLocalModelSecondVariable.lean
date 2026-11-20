import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousKappa
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunSuperpositionTargetOrthSummand
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped Topology

namespace GlobalTheory.ContrModR

section SlopeTestRemainingChoices
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)

/- English proof (translation)
Establish `hm : ∀ x y, p.ι (x * y) = p.ι x * p.ι y` using `fun x y => by conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, Witness.e_ι]`. Rewrite using `[hm]`. Express the relevant statement in the definitionally equal form `_ = p.ι (p.π (incA D b)) * p.ι x`. Rewrite using `[p.ι_π, mul_assoc, mul_left_comm, Witness.e_ι]`.
-/
theorem incA_mul_ι (b : D.host.E) (x : k) : incA D b * p.ι x = p.ι (p.pr b * x) := by
  have hm : ∀ x y, p.ι (x * y) = p.ι x * p.ι y := fun x y => by
    conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, Witness.e_ι]
  rw [hm]
  change _ = p.ι (p.π (incA D b)) * p.ι x
  rw [p.ι_π, mul_assoc, mul_left_comm, Witness.e_ι]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, incA_mul_ι, map_sum]`.
-/
theorem map_rat_mul_ι {a b c : Type} [Fintype b] (N : Matrix a b D.host.E) (M : Matrix b c k) :
    N.map (incA D) * M.map p.ι = (N.map p.pr * M).map p.ι := by
  ext i j
  simp [Matrix.mul_apply, incA_mul_ι, map_sum]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem map_pr_eq {a b : Type} (M : Matrix a b D.host.E) : M.map p.pr = M.map (Witness.prH p) := rfl

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

/- English proof (translation)
Use extensionality with `r a`. Rewrite using `[← h.1 r a]`. Simplify using `[Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]`.
-/
theorem core_β {ρ : ℕ} (B : BesLev D ρ) {s : k} (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (h : p.IsCoreFrame B s FA F₀) : F₀.β * fromRows (1 : Matrix n' n' k) (0 : Matrix Unit n' k) = B.o.iA.map p.pr * FA.β := by
  ext r a
  rw [← h.1 r a]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

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

section Up
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)
variable {n n'' : Type} [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n'']

/- English proof (translation)
Establish `hx : fromRows x (0 : Matrix Unit n k) = fromRows (1 : Matrix n'' n'' k) (0 : Matrix Unit n'' k) * x`. Rewrite using `[Matrix.fromRows_mul, Matrix.one_mul, Matrix.zero_mul]`. Rewrite using `[OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Place.up, Place.up, OrthDec.jA, rat, map_rat_mul_ι, hx, ← Matrix.mul_assoc, core_β p B' FA' F₀' h]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem up_fromRows {σ : ℕ} (B' : BesLev D σ) {s : k} (S : HSp D) (FA' : Frame k B'.A.rank n'')
    (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)) (FS : Frame k S.rank n) (h : p.IsCoreFrame B' s FA' F₀')
    (x : Matrix n'' n k) :
    p.up FS F₀' (fromRows x (0 : Matrix Unit n k)) = (B'.o.resT S).symm (p.up FS FA' x, 0) := by
  have hx : fromRows x (0 : Matrix Unit n k) = fromRows (1 : Matrix n'' n'' k) (0 : Matrix Unit n'' k) * x := by
    rw [Matrix.fromRows_mul, Matrix.one_mul, Matrix.zero_mul]
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Place.up, Place.up, OrthDec.jA, rat, map_rat_mul_ι, hx,
    ← Matrix.mul_assoc, core_β p B' FA' F₀' h]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Establish `hq : B'.o.qA.map p.pr * F₀'.β = fromCols FA'.β (0 : Matrix (Fin B'.A.rank) Unit k)`. Use `congrArg (FA'.β * ·) (core_qA p B' FA' F₀' h)` as an intermediate fact. Simplify using `only [← Matrix.mul_assoc, FA'.βγ, Matrix.one_mul] at this`. Rewrite using `[this, Matrix.mul_fromCols, Matrix.mul_one, Matrix.mul_zero]`. Rewrite using `[Place.up, Place.up, OrthDec.pA, rat, map_rat_mul_ι, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hq]`.

Use `conv_lhs => rw [← fromRows_toRows t]`. Rewrite using `[fromCols_mul_fromRows, Matrix.zero_mul, add_zero]`.
-/
theorem pA_up {σ : ℕ} (B' : BesLev D σ) {s : k} (S : HSp D) (FA' : Frame k B'.A.rank n'')
    (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)) (FS : Frame k S.rank n) (h : p.IsCoreFrame B' s FA' F₀')
    (t : Matrix (n'' ⊕ Unit) n k) : B'.o.pA ⬝ p.up FS F₀' t = p.up FS FA' t.toRows₁ := by
  have hq : B'.o.qA.map p.pr * F₀'.β = fromCols FA'.β (0 : Matrix (Fin B'.A.rank) Unit k) := by
    have := congrArg (FA'.β * ·) (core_qA p B' FA' F₀' h)
    simp only [← Matrix.mul_assoc, FA'.βγ, Matrix.one_mul] at this
    rw [this, Matrix.mul_fromCols, Matrix.mul_one, Matrix.mul_zero]
  rw [Place.up, Place.up, OrthDec.pA, rat, map_rat_mul_ι, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hq]
  conv_lhs => rw [← fromRows_toRows t]
  rw [fromCols_mul_fromRows, Matrix.zero_mul, add_zero]

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
Simplify using `only [heisO]`. Rewrite using `[o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_r, add_zero, ← map_add, Prod.mk_add_mk, add_zero]`.
-/
theorem heis_pass {V A L : HSp D} (o : OrthDec V A L) (S : HSp D) (f : WO S V → ℂ) (b v : WO S A) (z : WO S L) :
    heisO ψ S V ((o.resT S).symm (b, 0)) f ((o.resT S).symm (v, z)) =
      ψ (symplOH S A v b) * f ((o.resT S).symm (v + b, z)) := by
  simp only [heisO]
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_r, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

end Pass

end GlobalTheory.ContrModR

namespace GlobalTheory.ContrModR

/- English proof (translation)
Introduce `D k _ _ _ _ p ψ hψ ρ σ B B' l S vL s hs n n'' _ _ _ _ FS FA' F₀' hcore T₂ hT₂ φ₀ Ξ₁ hΞ₁ u T hT`. Establish `pass : ∀ (b : WO S B'.A) (Φ Φ' : SB (Matrix n'' n k)), T₂ (GlobalTheory.ContractionLocal.rowTens φ₀ Φ') = heisO ψ S B'.V₀ ((B'.o.resT S).symm (b, 0)) (T₂ (GlobalTheory.ContractionLocal.rowTens φ₀ Φ)) → T Φ' = heisO ψ S B'.A b (T Φ)`. Introduce `b Φ Φ' e`. Use function extensionality and compare the values at `v`. Rewrite using `[hT Φ' v, e]`.

Express the relevant statement in the definitionally equal form `_ = ψ (symplOH S B'.A v b) * T Φ (v + b)`. Rewrite using `[hT Φ (v + b)]`. Unfold `GlobalTheory.Unf.contr`. Rewrite using `[← integral_const_mul]`. Use `congrArg (fun f : WO S B'.L → ℂ => ∫ w in vL.𝓕, f w ∂vL.μ) (funext fun w => ?_)` and prove the remaining obligations.

Rewrite using `[heis_pass]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨fun Φ => ?_, fun x Φ Φ' e => ?_, fun y hy Φ Φ' e => ?_⟩` and prove the remaining obligations. Use `haveI : ∀ m n, BorelSpace (Mx D m n) := fun _ _ => ⟨rfl⟩`. Use `haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) := ⟨by rw [Measure.restrict_apply_univ, vL.covol.2.2]; exact ENNReal.one_lt_top⟩`.

Take `⟨C₁, hC₁⟩` from `GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hψ Ξ₁ hΞ₁`. Establish `hc : Continuous fun w => Ξ₁ ((B.o.resS S).symm (u, l.κ S w))` using `hΞ₁.cont.comp ((OrthDec.continuous_resS_symm _ _).comp (Continuous.prodMk continuous_const (GlobalTheory.ContractionLocal.continuous_kappa l S)))`. Establish `hint : Integrable (fun w => Ξ₁ ((B.o.resS S).symm (u, l.κ S w))) (vL.μ.restrict vL.𝓕)` using `(integrable_const C₁).mono' hc.aestronglyMeasurable (ae_of_all _ fun w => hC₁ _)`. Establish `h` using `GlobalTheory.SuperposT.superpos_target D ψ hψ B'.V₀ B'.A B'.L S B'.o (T₂ (GlobalTheory.ContractionLocal.rowTens φ₀ Φ)) (hT₂.theta _) (WO S B'.L) (vL.μ.restrict vL.𝓕) id (fun w => Ξ₁ ((B.o.resS S).symm (u, l.κ S w))) measurable_id hint`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `v`. Rewrite using `[hT]`. Unfold `GlobalTheory.Unf.contr`. Use `congrArg (fun f : WO S B'.L → ℂ => ∫ w in vL.𝓕, f w ∂vL.μ) (funext fun w => ?_)` and prove the remaining obligations. Simplify using `only [id]`.

Expand and normalize the polynomial expressions, which then agree. Use `pass (p.up FS FA' x) Φ Φ' ?_` and prove the remaining obligations. Rewrite using `[← up_fromRows p B' S FA' F₀' FS hcore x]`. Use `hT₂.trans _ _ _ fun t => ?_` and prove the remaining obligations. Establish `h1 : (t + fromRows x (0 : Matrix Unit n k)).toRows₁ = t.toRows₁ + x`.

Use extensionality with `i j`. Simplify using `[Matrix.toRows₁]`. Establish `h2 : (t + fromRows x (0 : Matrix Unit n k)) (Sum.inr ()) = t (Sum.inr ())`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules.

Simplify using `only [GlobalTheory.ContractionLocal.rowTens_apply, e, h1, h2]`. Use `pass y Φ Φ' (hT₂.modul _ ?_ _ _ fun t => ?_)` and prove the remaining obligations. Introduce `i j`. Rewrite using `[OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Matrix.mul_apply, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun c _ => by rw [mul_left_comm, hy c j]`.

Simplify using `only [GlobalTheory.ContractionLocal.rowTens_apply, e]`. Rewrite using `[B'.o.symplO_resT S (p.up FS F₀' t), AddEquiv.apply_symm_apply]`. Rewrite using `[OrthDec.resT_apply B'.o S (p.up FS F₀' t)]`. Simplify using `only`. Rewrite using `[pA_up p B' S FA' F₀' FS hcore t]`.

Establish `: symplO S B'.L (B'.o.pB ⬝ p.up FS F₀' t) 0 = 0`. Establish `h0 : hO S B'.L (B'.o.pB ⬝ p.up FS F₀' t) 0 = 0` using `by simp [hO]`. Simplify using `[symplO, h0]`. Simplify using `only [this, add_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem contr_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (s : k), s ≠ 0 → ∀ (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (FS : Frame k S.rank n) (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)), p.IsCoreFrame B' s FA' F₀' → ∀ (T₂ : SB (Matrix (n'' ⊕ Unit) n k) →ₗ[ℂ] (WO S B'.V₀ → ℂ)), p.IsModel ψ FS F₀' T₂ → ∀ (φ₀ : SB (n → k)) (Ξ₁ : WO B.V₀ S → ℂ), IsThetaFunO ψ B.V₀ S Ξ₁ → ∀ (u : WO B.A S) (T : SB (Matrix n'' n k) →ₗ[ℂ] (WO S B'.A → ℂ)), (∀ Ξ₂ v, T Ξ₂ v = GlobalTheory.Unf.contr l S vL Ξ₁ (T₂ (GlobalTheory.ContractionLocal.rowTens φ₀ Ξ₂)) u v) → p.IsModel ψ FS FA' T := by
  intro D k _ _ _ _ p ψ hψ ρ σ B B' l S vL s hs n n'' _ _ _ _ FS FA' F₀' hcore T₂ hT₂ φ₀ Ξ₁ hΞ₁ u T hT

  have pass : ∀ (b : WO S B'.A) (Φ Φ' : SB (Matrix n'' n k)),
      T₂ (GlobalTheory.ContractionLocal.rowTens φ₀ Φ') =
        heisO ψ S B'.V₀ ((B'.o.resT S).symm (b, 0)) (T₂ (GlobalTheory.ContractionLocal.rowTens φ₀ Φ)) →
      T Φ' = heisO ψ S B'.A b (T Φ) := by
    intro b Φ Φ' e
    funext v
    rw [hT Φ' v, e]
    change _ = ψ (symplOH S B'.A v b) * T Φ (v + b)
    rw [hT Φ (v + b)]
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
    obtain ⟨C₁, hC₁⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hψ Ξ₁ hΞ₁
    have hc : Continuous fun w => Ξ₁ ((B.o.resS S).symm (u, l.κ S w)) :=
      hΞ₁.cont.comp ((OrthDec.continuous_resS_symm _ _).comp
        (Continuous.prodMk continuous_const (GlobalTheory.ContractionLocal.continuous_kappa l S)))
    have hint : Integrable (fun w => Ξ₁ ((B.o.resS S).symm (u, l.κ S w))) (vL.μ.restrict vL.𝓕) :=
      (integrable_const C₁).mono' hc.aestronglyMeasurable (ae_of_all _ fun w => hC₁ _)
    have h := GlobalTheory.SuperposT.superpos_target D ψ hψ B'.V₀ B'.A B'.L S B'.o (T₂ (GlobalTheory.ContractionLocal.rowTens φ₀ Φ))
      (hT₂.theta _) (WO S B'.L) (vL.μ.restrict vL.𝓕) id (fun w => Ξ₁ ((B.o.resS S).symm (u, l.κ S w)))
      measurable_id hint
    convert h using 1
    funext v
    rw [hT]
    unfold GlobalTheory.Unf.contr
    refine congrArg (fun f : WO S B'.L → ℂ => ∫ w in vL.𝓕, f w ∂vL.μ) (funext fun w => ?_)
    simp only [id]
    ring
  ·
    refine pass (p.up FS FA' x) Φ Φ' ?_
    rw [← up_fromRows p B' S FA' F₀' FS hcore x]
    refine hT₂.trans _ _ _ fun t => ?_
    have h1 : (t + fromRows x (0 : Matrix Unit n k)).toRows₁ = t.toRows₁ + x := by
      ext i j; simp [Matrix.toRows₁]
    have h2 : (t + fromRows x (0 : Matrix Unit n k)) (Sum.inr ()) = t (Sum.inr ()) := by
      funext j; simp
    simp only [GlobalTheory.ContractionLocal.rowTens_apply, e, h1, h2]
  ·
    refine pass y Φ Φ' (hT₂.modul _ ?_ _ _ fun t => ?_)
    · intro i j
      rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [mul_left_comm, hy c j]
    · simp only [GlobalTheory.ContractionLocal.rowTens_apply, e]
      rw [B'.o.symplO_resT S (p.up FS F₀' t), AddEquiv.apply_symm_apply]
      rw [OrthDec.resT_apply B'.o S (p.up FS F₀' t)]
      simp only
      rw [pA_up p B' S FA' F₀' FS hcore t]
      have : symplO S B'.L (B'.o.pB ⬝ p.up FS F₀' t) 0 = 0 := by
        have h0 : hO S B'.L (B'.o.pB ⬝ p.up FS F₀' t) 0 = 0 := by simp [hO]
        simp [symplO, h0]
      simp only [this, add_zero]
      ring

end GlobalTheory.ContrModR

end
