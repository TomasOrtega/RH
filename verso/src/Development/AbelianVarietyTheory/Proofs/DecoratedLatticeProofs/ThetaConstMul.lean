import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section

namespace GlobalTheory.SeeSawFold

variable {D : D7}

/- English proof (translation)
Rewrite using `[hf.quasi, hg.quasi]; ring level := by`. Take `⟨U, hU, hUf⟩` from `hf.level`. Take `⟨V, hV, hVg⟩` from `hg.level`. Use `⟨U ⊓ V, hU.inter hV, fun u hu h0 => ?_⟩` and prove the remaining obligations. Establish `e1` using `hUf u hu.1 h0`.

Establish `e2` using `hVg u hu.2 h0`. Use function extensionality and compare the values at `w`. Establish `a1` using `congrFun e1 w`. Establish `a2` using `congrFun e2 w`. Simplify using `only [heisO] at a1 a2 ⊢`.

Rewrite using `[mul_add, a1, a2]`. Use `cont := hf.cont.add hg.cont`. Use `smooth k L hL hL' w := (hf.smooth k L hL hL' w).add (hg.smooth k L hL hL' w)`.
-/
theorem theta_add' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (fun w => f w + g w) where
  quasi γ w := by rw [hf.quasi, hg.quasi]; ring
  level := by
    obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨V, hV, hVg⟩ := hg.level
    refine ⟨U ⊓ V, hU.inter hV, fun u hu h0 => ?_⟩
    have e1 := hUf u hu.1 h0
    have e2 := hVg u hu.2 h0
    funext w
    have a1 := congrFun e1 w
    have a2 := congrFun e2 w
    simp only [heisO] at a1 a2 ⊢
    rw [mul_add, a1, a2]
  cont := hf.cont.add hg.cont
  smooth k L hL hL' w := (hf.smooth k L hL hL' w).add (hg.smooth k L hL hL' w)

/- English proof (translation)
Rewrite using `[hf.quasi]; ring level := by`. Take `⟨U, hU, hUf⟩` from `hf.level`. Use `⟨U, hU, fun u hu h0 => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `w`. Establish `a1` using `congrFun (hUf u hu h0) w`.

Simplify using `only [heisO] at a1 ⊢`. Rewrite using `[mul_left_comm, a1]`. Use `cont := continuous_const.mul hf.cont`. Use `smooth k L hL hL' w := contDiff_const.mul (hf.smooth k L hL hL' w)`.
-/
theorem theta_const_mul' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ}
    (a : ℂ) (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (fun w => a * f w) where
  quasi γ w := by rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hU, hUf⟩ := hf.level
    refine ⟨U, hU, fun u hu h0 => ?_⟩
    funext w
    have a1 := congrFun (hUf u hu h0) w
    simp only [heisO] at a1 ⊢
    rw [mul_left_comm, a1]
  cont := continuous_const.mul hf.cont
  smooth k L hL hL' w := contDiff_const.mul (hf.smooth k L hL hL' w)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ => by simp, ⟨⊤, isOpen_univ, fun a _ _ => by funext w; simp [heisO]⟩, continuous_const, fun _ _ _ _ _ => contDiff_const⟩`.
-/
theorem theta_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : IsThetaFunO ψ S T (fun _ => 0) :=
  ⟨fun _ _ => by simp, ⟨⊤, isOpen_univ, fun a _ _ => by funext w; simp [heisO]⟩, continuous_const,
    fun _ _ _ _ _ => contDiff_const⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using theta_zero' ψ S T`. Consider the case `insert i s hi ih`. Simplify using `only [Finset.sum_insert hi]`. Conclude with `theta_add' (hF i (Finset.mem_insert_self i s)) (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))`.
-/
theorem theta_sum' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {ι : Type*} (s : Finset ι) (F : ι → WO S T → ℂ)
    (hF : ∀ i ∈ s, IsThetaFunO ψ S T (F i)) : IsThetaFunO ψ S T (fun w => ∑ i ∈ s, F i w) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using theta_zero' ψ S T
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact theta_add' (hF i (Finset.mem_insert_self i s)) (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

section Ops

variable (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D)

def opL (a : WO A S →₀ ℂ) (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u v => comb ψ A S a (fun u' => C u' v) u

def opR (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u v => comb ψ S A' b (C u) v

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem biComb_eq (a : WO A S →₀ ℂ) (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' a b C = opL ψ A S A' a (opR ψ A S A' b C) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `u v`. Simplify using `only [opL, opR, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem opL_opR (a : WO A S →₀ ℂ) (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    opL ψ A S A' a (opR ψ A S A' b C) = opR ψ A S A' b (opL ψ A S A' a C) := by
  funext u v
  simp only [opL, opR, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons p l ih => simp only [List.foldr_cons, ih, opL_opR]`.
-/
theorem foldL_opR (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    l.foldr (fun p C => opL ψ A S A' p.1 C) (opR ψ A S A' b C) =
      opR ψ A S A' b (l.foldr (fun p C => opL ψ A S A' p.1 C) C) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.foldr_cons, ih, opL_opR]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons p l ih => simp only [List.foldr_cons, foldL_opR, ih, biComb_eq]`.
-/
theorem foldL_foldR (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) (Y : WO A S → WO S A' → ℂ) :
    l.foldr (fun p C => opL ψ A S A' p.1 C) (l.foldr (fun p C => opR ψ A S A' p.2 C) Y) =
      l.foldr (fun p C => biComb ψ A S A' p.1 p.2 C) Y := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.foldr_cons, foldL_opR, ih, biComb_eq]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons p l ih => simp only [List.foldr_cons, ← ih]`. Both sides reduce to the same expression.
-/
theorem foldR_apply (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) (Y : WO A S → WO S A' → ℂ) (u : WO A S) :
    l.foldr (fun p C => opR ψ A S A' p.2 C) Y u = l.foldr (fun p f => comb ψ S A' p.2 f) (Y u) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.foldr_cons, ← ih]; rfl

/- English proof (translation)
Proceed by induction on `l generalizing u with`. Consider the case `nil => rfl`. Consider the case `cons p l ih`. Simplify using `only [List.foldr_cons]`. Use `show comb ψ A S p.1 (fun u' => l.foldr (fun p C => opL ψ A S A' p.1 C) C u' v) u = _`.

Use `congr 1`. Use function extensionality and compare the values at `u'`. Rewrite using `[ih]`.
-/
theorem foldL_apply (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) (C : WO A S → WO S A' → ℂ) (u : WO A S)
    (v : WO S A') :
    l.foldr (fun p C => opL ψ A S A' p.1 C) C u v = l.foldr (fun p f => comb ψ A S p.1 f) (fun u' => C u' v) u := by
  induction l generalizing u with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldr_cons]
    show comb ψ A S p.1 (fun u' => l.foldr (fun p C => opL ψ A S A' p.1 C) C u' v) u = _
    congr 1
    funext u'
    rw [ih]

/- English proof (translation)
Simplify using `only [opR, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO]`. Use `theta_sum' _ _ fun y _ => ?_` and prove the remaining obligations. Establish `h` using `theta_const_mul' (b y * ψ (symplOH S A' v y)) (hC (v + y))`. Simplify `h` using `only [mul_assoc]`.
-/
theorem theta_opR (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) (hC : ∀ v, IsThetaFunO ψ A S (fun u => C u v))
    (v : WO S A') : IsThetaFunO ψ A S (fun u => opR ψ A S A' b C u v) := by
  simp only [opR, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO]
  refine theta_sum' _ _ fun y _ => ?_
  have h := theta_const_mul' (b y * ψ (symplOH S A' v y)) (hC (v + y))
  simpa only [mul_assoc] using h

/- English proof (translation)
Proceed by induction on `l generalizing v with`. Consider the case `nil => exact hY v`. Consider the case `cons p l ih => exact theta_opR ψ A S A' p.2 _ ih v`.
-/
theorem theta_foldR (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) (Y : WO A S → WO S A' → ℂ)
    (hY : ∀ v, IsThetaFunO ψ A S (fun u => Y u v)) (v : WO S A') :
    IsThetaFunO ψ A S (fun u => l.foldr (fun p C => opR ψ A S A' p.2 C) Y u v) := by
  induction l generalizing v with
  | nil => exact hY v
  | cons p l ih => exact theta_opR ψ A S A' p.2 _ ih v

end Ops

end GlobalTheory.SeeSawFold

open GlobalTheory.SeeSawFold in

/- English proof (translation)
Introduce `D ψ A S A' c c' l hc hc' Y hYv hYu`. Establish `hR : opR ψ A S A' c' Y = l.foldr (fun p C => opR ψ A S A' p.2 C) Y`. Use function extensionality and compare the values at `u v`. Use `show comb ψ S A' c' (Y u) v = _`. Rewrite using `[hc' _ (hYu u), foldR_apply]`.

Rewrite using `[← foldL_foldR, biComb_eq, hR]`. Use function extensionality and compare the values at `u v`. Rewrite using `[foldL_apply]`. Conclude with `congrFun (hc _ (theta_foldR ψ A S A' l Y hYv v)) u`.
-/
theorem GlobalTheory.SeeSaw.biComb_eq_foldr : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ)
    (c' : WO S A' →₀ ℂ) (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))),
    (∀ f, IsThetaFunO ψ A S f → comb ψ A S c f = l.foldr (fun p f' => comb ψ A S p.1 f') f) →
    (∀ f, IsThetaFunO ψ S A' f → comb ψ S A' c' f = l.foldr (fun p f' => comb ψ S A' p.2 f') f) →
    ∀ Y : WO A S → WO S A' → ℂ, (∀ v, IsThetaFunO ψ A S (fun u => Y u v)) → (∀ u, IsThetaFunO ψ S A' (Y u)) →
      biComb ψ A S A' c c' Y = l.foldr (fun p C => biComb ψ A S A' p.1 p.2 C) Y := by
  intro D ψ A S A' c c' l hc hc' Y hYv hYu
  have hR : opR ψ A S A' c' Y = l.foldr (fun p C => opR ψ A S A' p.2 C) Y := by
    funext u v
    show comb ψ S A' c' (Y u) v = _
    rw [hc' _ (hYu u), foldR_apply]
  rw [← foldL_foldR, biComb_eq, hR]
  funext u v
  rw [foldL_apply]
  exact congrFun (hc _ (theta_foldR ψ A S A' l Y hYv v)) u

end
