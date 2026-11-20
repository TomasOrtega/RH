import Formalism.LocalToGlobal.GlobalTheory.GL4.CoeffMemOfIntSpanAt

open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col Formalism.BasicNotions.SkeletonIndexLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Int2

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

/- English proof (translation)
Rewrite using `[mem_twId]`. Introduce `w B hB`. Use `set w' := D.plEq.symm w with hw'`. Establish `hw : D.plEq w' = w` using `D.plEq.apply_symm_apply w`. Establish `hLB : ∀ τ, LocBasis D w' (CV.Q c τ) (CV.eQ c τ) (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)` using `fun τ => locBasis_of_isBasisAt CV c τ w' (B τ) (by rw [hw]; exact hB τ)`.

Set `γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL` to `fun c' τ => if c' = c then (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) else Classical.choose (exists_locBasis w' (CV.Q c' τ) (CV.Q_good c' τ) (CV.eQ c' τ))`. Establish `hγ : ∀ c' τ, LocBasis D w' (CV.Q c' τ) (CV.eQ c' τ) (γ c' τ)`. Introduce `c' τ`. Distinguish the cases in `h : c' = c`. Simplify using `only [γ, if_pos h]`.

Rewrite using `[h]`. Conclude with `hLB τ`. Simplify using `only [γ, if_neg h]`. Conclude with `Classical.choose_spec (exists_locBasis w' (CV.Q c' τ) (CV.Q_good c' τ) (CV.eQ c' τ))`. Establish `hxL : x ∈ ((D.fm u).lat 0).L`.

Take `⟨x', hx', rfl⟩` from `hx`. Conclude with `prjC_mem CV c hx'`. Establish `hxW : x ∈ locW D.what₂.places w' ((D.fm u).lat 0).L` using `Submodule.subset_span hxL`. Establish `hP` using `(CV.fin w' γ hγ x).1 hxW c`. Simplify using `only [γ, if_pos rfl] at hP`.

Use `set F : Pol D.what₂.LL D.what₂.Tau (D.R.N 0) := ((coE CV (hTV0 D u) x c : VV D.what₂.LL ((D.fm u).lam 0)) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0)) with hF`. Establish `hFco : F = CV.co x c` using `coE_coe CV (hTV0 D u) x c`. Establish `hinvB : (fun τ => (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)⁻¹) = fun τ => (((B⁻¹) τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)`. Use function extensionality and compare the values at `τ`. Rewrite using `[Pi.inv_apply, Matrix.coe_units_inv]`.

Rewrite `hP` using `[← hFco, hinvB, actAll_eq_actP]`. Establish `hF0 : actP ((D.fm u).lam 0) B⁻¹ F ∈ (map (σ` using `D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) (locRing w).subtype).range := by`. Use `mem_range_of_coeff_mem _ fun m' => ?_` and prove the remaining obligations. Rewrite using `[← hw]`. Conclude with `intW_mem_locRing w' (coeff_mem_of_intSpanAt w' _ hP m')`.

Establish `hU : ∀ τ a b, (((g * B) τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)ᵀ a b ∈ locRing w`. Introduce `τ a b`. Establish `hcol : (fun c => (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) c a) ∈ localization₂ w.asIdeal (MQ CV c τ)`. Rewrite using `[hB τ]`. Conclude with `le_localisation w _ (Submodule.subset_span ⟨a, rfl⟩)`.

Take `⟨s, hs, hsx⟩` from `hcol`. Rewrite using `[mem_locRing]`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Use `gM_int CV c y hy τ _ hsx b` as an intermediate fact. Rewrite `this` using `[← hg τ, Matrix.mulVec_smul]`.

Establish `e : (((g * B) τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)ᵀ a b = ((g τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) *ᵥ fun c => (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) c a) b`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Rewrite using `[e]`. Conclude with `this`. Establish `hkey` using `coeff_mem_of_mem_range _ (block_action_integral (locRing w) _ hU hF0) m.1`.

Establish `e : Formalism.GradedWeylDivisibility.blockAct D.what₂.LL (fun τ => (((g * B) τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)ᵀ) (actP ((D.fm u).lam 0) B⁻¹ F) = detTwK ((D.fm u).lam 0) B⁻¹ • trAct g F` using `by show trAct (g * B) (actP ((D.fm u).lam 0) B⁻¹ F) = _`. Rewrite using `[trAct_mul]`. Simplify using `only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, map_smul, transpose_action_inv_right]`. Rewrite `hkey` using `[e, coeff_smul, smul_eq_mul, mem_locRing]`. Conclude with `hkey`.
-/
theorem cf_mem_twId (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V)
    (hy : ∀ a, y a ∈ dualSub (D.sp.X 0) (D.clsLat u 0 c)) (g : D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL)
    (hg : ∀ τ, ((g τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) = gM CV c y τ)
    {x : ((D.fm u).lat 0).V} (hx : x ∈ NC CV c) (m : MonI ((D.fm u).lam 0)) :
    cfMap ((D.fm u).lam 0) g (coE CV (hTV0 D u) x c) m ∈ twId ((D.fm u).lam 0) (MQ CV c) := by
  classical
  rw [mem_twId]
  intro w B hB
  set w' := D.plEq.symm w with hw'
  have hw : D.plEq w' = w := D.plEq.apply_symm_apply w
  have hLB : ∀ τ, LocBasis D w' (CV.Q c τ) (CV.eQ c τ) (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) :=
    fun τ => locBasis_of_isBasisAt CV c τ w' (B τ) (by rw [hw]; exact hB τ)
  let γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL := fun c' τ =>
    if c' = c then (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)
    else Classical.choose (exists_locBasis w' (CV.Q c' τ) (CV.Q_good c' τ) (CV.eQ c' τ))
  have hγ : ∀ c' τ, LocBasis D w' (CV.Q c' τ) (CV.eQ c' τ) (γ c' τ) := by
    intro c' τ
    by_cases h : c' = c
    · simp only [γ, if_pos h]
      rw [h]
      exact hLB τ
    · simp only [γ, if_neg h]
      exact Classical.choose_spec (exists_locBasis w' (CV.Q c' τ) (CV.Q_good c' τ) (CV.eQ c' τ))
  have hxL : x ∈ ((D.fm u).lat 0).L := by
    obtain ⟨x', hx', rfl⟩ := hx
    exact prjC_mem CV c hx'
  have hxW : x ∈ locW D.what₂.places w' ((D.fm u).lat 0).L := Submodule.subset_span hxL
  have hP := (CV.fin w' γ hγ x).1 hxW c
  simp only [γ, if_pos rfl] at hP
  set F : Pol D.what₂.LL D.what₂.Tau (D.R.N 0) := ((coE CV (hTV0 D u) x c : VV D.what₂.LL ((D.fm u).lam 0)) :
    Pol D.what₂.LL D.what₂.Tau (D.R.N 0)) with hF
  have hFco : F = CV.co x c := coE_coe CV (hTV0 D u) x c
  have hinvB : (fun τ => (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)⁻¹) =
      fun τ => (((B⁻¹) τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) := by
    funext τ
    rw [Pi.inv_apply, Matrix.coe_units_inv]
  rw [← hFco, hinvB, actAll_eq_actP] at hP
  have hF0 : actP ((D.fm u).lam 0) B⁻¹ F ∈ (map (σ := D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) (locRing w).subtype).range := by
    refine mem_range_of_coeff_mem _ fun m' => ?_
    rw [← hw]
    exact intW_mem_locRing w' (coeff_mem_of_intSpanAt w' _ hP m')
  have hU : ∀ τ a b, (((g * B) τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)ᵀ a b ∈
      locRing w := by
    intro τ a b
    have hcol : (fun c => (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) c a) ∈ localization₂ w.asIdeal (MQ CV c τ) := by
      rw [hB τ]
      exact le_localisation w _ (Submodule.subset_span ⟨a, rfl⟩)
    obtain ⟨s, hs, hsx⟩ := hcol
    rw [mem_locRing]
    refine ⟨s, hs, ?_⟩
    have := gM_int CV c y hy τ _ hsx b
    rw [← hg τ, Matrix.mulVec_smul] at this
    have e : (((g * B) τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)ᵀ a b =
        ((g τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) *ᵥ fun c => (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) c a) b := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [e]
    exact this
  have hkey := coeff_mem_of_mem_range _ (block_action_integral (locRing w) _ hU hF0) m.1
  have e : Formalism.GradedWeylDivisibility.blockAct D.what₂.LL (fun τ => (((g * B) τ : GL (Fin (D.R.N 0)) D.what₂.LL) :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)ᵀ) (actP ((D.fm u).lam 0) B⁻¹ F) =
      detTwK ((D.fm u).lam 0) B⁻¹ • trAct g F := by
    show trAct (g * B) (actP ((D.fm u).lam 0) B⁻¹ F) = _
    rw [trAct_mul]
    simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, map_smul, transpose_action_inv_right]
  rw [e, coeff_smul, smul_eq_mul, mem_locRing] at hkey
  exact hkey

end Int2

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
