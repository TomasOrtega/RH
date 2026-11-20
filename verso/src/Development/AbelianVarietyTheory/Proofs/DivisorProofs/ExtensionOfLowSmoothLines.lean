import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorTorusActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorFockVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemUJsetOfKset

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.IoExtPf

section Rep

open Formalism.MainNotions.S

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool} {lam : Fin n → ℝ}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

/- English proof (translation)
Take `⟨v, hvS, hv0, hv⟩` from `hS.2.2.2.1`. Establish `hK` using `pM_mem (revNeg ε) (eps_revNeg ε)`. Establish `hn : ‖σ (pM (revNeg ε)) v‖ = ‖v‖` using `hU.2.1 _ (kset_uj hK) v`. Establish `hp : ‖v‖ ≠ 0` using `norm_ne_zero_iff.2 hv0`. Use `⟨((‖v‖⁻¹ : ℝ) : ℂ) • σ (pM (revNeg ε)) v, ?_, ?_, isWtOn_smul (isWtOn_perm hU _ (eps_revNeg ε) hv) _⟩` and prove the remaining obligations.

Conclude with `Submodule.smul_mem _ _ (hS.2.1 _ hK v hvS)`. Rewrite using `[norm_smul, hn, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hp]`.
-/
theorem exists_ext_mem (hU : IsURepOn (UJset ε) σ) {Λ : Fin n → ℝ} {S : Submodule ℂ H} (hS : IsKTypeOf ε σ Λ S) :
    ∃ w ∈ S, ‖w‖ = 1 ∧ IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Λ (revNeg ε a)) w := by
  obtain ⟨v, hvS, hv0, hv⟩ := hS.2.2.2.1
  have hK := pM_mem (revNeg ε) (eps_revNeg ε)
  have hn : ‖σ (pM (revNeg ε)) v‖ = ‖v‖ := hU.2.1 _ (kset_uj hK) v
  have hp : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • σ (pM (revNeg ε)) v, ?_, ?_, isWtOn_smul (isWtOn_perm hU _ (eps_revNeg ε) hv) _⟩
  · exact Submodule.smul_mem _ _ (hS.2.1 _ hK v hvS)
  · rw [norm_smul, hn, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hp]

/- English proof (translation)
Take `⟨-, -, hU, -, -, ⟨S, hS⟩, -⟩` from `hσ`. Establish `hle : ∀ S', IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S' ≤ lowKSub ε lam σ` using `fun S' h => le_sSup (s := {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S}) h`. Establish `key : lowKSub ε lam σ = S`. Use `le_antisymm (sSup_le fun S' hS' => ?_) (hle S hS)` and prove the remaining obligations. Take `⟨w, hw, hw1, hwt⟩` from `exists_ext_mem hU hS`.

Take `⟨w', hw', hw1', hwt'⟩` from `exists_ext_mem hU hS'`. Take `⟨c, hc⟩` from `hl w w' hw1 (hle S hS hw) hwt hw1' (hle S' hS' hw') hwt'`. Establish `hm : w' ∈ S' ⊓ S` using `⟨hw', hc ▸ S.smul_mem c hw⟩`. Break down `hS'.2.2.1 (S' ⊓ S) inf_le_left (fun g hg v hv => ⟨hS'.2.1 g hg v hv.1, hS.2.1 g hg v hv.2⟩) with h | h` into its components or cases. Rewrite `hm` using `[h, Submodule.mem_bot]`.

Rewrite `hw1'` using `[hm, norm_zero]`. Conclude with `absurd hw1' zero_ne_one`. Conclude with `h ▸ inf_le_right`. Rewrite `hN`, the goal using `[key]`. Conclude with `hS.2.2.1 N hN hst`.
-/
theorem lowK_irred (hσ : IsDS ε lam σ)
    (hl : ∀ w w' : H, ‖w‖ = 1 → w ∈ lowKSub ε lam σ →
      IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) w → ‖w'‖ = 1 → w' ∈ lowKSub ε lam σ →
      IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) w' → ∃ c : ℂ, w' = c • w)
    (N : Submodule ℂ H) (hN : N ≤ lowKSub ε lam σ) (hst : IsKStableOn ε σ N) : N = ⊥ ∨ N = lowKSub ε lam σ := by
  obtain ⟨-, -, hU, -, -, ⟨S, hS⟩, -⟩ := hσ
  have hle : ∀ S', IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S' ≤ lowKSub ε lam σ := fun S' h =>
    le_sSup (s := {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S}) h
  have key : lowKSub ε lam σ = S := by
    refine le_antisymm (sSup_le fun S' hS' => ?_) (hle S hS)
    obtain ⟨w, hw, hw1, hwt⟩ := exists_ext_mem hU hS
    obtain ⟨w', hw', hw1', hwt'⟩ := exists_ext_mem hU hS'
    obtain ⟨c, hc⟩ := hl w w' hw1 (hle S hS hw) hwt hw1' (hle S' hS' hw') hwt'
    have hm : w' ∈ S' ⊓ S := ⟨hw', hc ▸ S.smul_mem c hw⟩
    rcases hS'.2.2.1 (S' ⊓ S) inf_le_left (fun g hg v hv => ⟨hS'.2.1 g hg v hv.1, hS.2.1 g hg v hv.2⟩) with h | h
    · rw [h, Submodule.mem_bot] at hm
      rw [hm, norm_zero] at hw1'
      exact absurd hw1' zero_ne_one
    · exact h ▸ inf_le_right
  rw [key] at hN ⊢
  exact hS.2.2.1 N hN hst

end Rep

section Minors

variable {D : D7} {m n : ℕ}

/- English proof (translation)
Introduce `h`. Establish `h1` using `congrArg (MvPolynomial.eval fun x : FVar D m n => if (x.2.1 : ℕ) + b = x.2.2 + a then (1 : ℂ) else 0) h`. Rewrite `h1` using `[RingHom.map_det, map_zero]`. Establish `h2 : (MvPolynomial.eval fun x : FVar D m n => if (x.2.1 : ℕ) + b = x.2.2 + a then (1 : ℂ) else 0).mapMatrix (Matrix.of fun α β : Fin k => (varF τ (a + β) (b + α) : MvPolynomial (FVar D m n) ℂ)) = 1`. Use extensionality with `α β`.

Establish `hα` using `α.2`. Establish `hβ` using `β.2`. Establish `hr : a + β < m ∧ b + α < n` using `⟨by omega, by omega⟩`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, varF, dif_pos hr, MvPolynomial.eval_X, Matrix.one_apply, Fin.ext_iff]`. Conclude with `if_congr ⟨fun h => by omega, fun h => by omega⟩ rfl rfl`.

Rewrite `h1` using `[h2, Matrix.det_one]`. Conclude with `one_ne_zero h1`.
-/
theorem minor_ne (τ : D.what₂.Tau) (a b k : ℕ) (ha : a + k ≤ m) (hb : b + k ≤ n) :
    (Matrix.of fun α β : Fin k => (varF τ (a + β) (b + α) : MvPolynomial (FVar D m n) ℂ)).det ≠ 0 := by
  intro h
  have h1 := congrArg (MvPolynomial.eval fun x : FVar D m n => if (x.2.1 : ℕ) + b = x.2.2 + a then (1 : ℂ) else 0) h
  rw [RingHom.map_det, map_zero] at h1
  have h2 : (MvPolynomial.eval fun x : FVar D m n => if (x.2.1 : ℕ) + b = x.2.2 + a then (1 : ℂ) else 0).mapMatrix
      (Matrix.of fun α β : Fin k => (varF τ (a + β) (b + α) : MvPolynomial (FVar D m n) ℂ)) = 1 := by
    ext α β
    have hα := α.2
    have hβ := β.2
    have hr : a + β < m ∧ b + α < n := ⟨by omega, by omega⟩
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, varF, dif_pos hr, MvPolynomial.eval_X,
      Matrix.one_apply, Fin.ext_iff]
    exact if_congr ⟨fun h => by omega, fun h => by omega⟩ rfl rfl
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

/- English proof (translation)
Unfold `delta deltaAt`. Use `Finset.prod_ne_zero_iff.2 fun τ _ => mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i hi => pow_ne_zero _ ?_) (Finset.prod_ne_zero_iff.2 fun i hi => pow_ne_zero _ ?_)` and prove the remaining obligations. Use `Finset.mem_range.1 hi` as an intermediate fact. Use `hpq τ` as an intermediate fact. Establish `h` using `minor_ne (m := m) (n := n) τ 0 0 (i + 1) (by omega) (by omega)`.

Simplify `h` using `only [minorPlus, zero_add]`. Use `Finset.mem_range.1 hi` as an intermediate fact. Use `hpq τ` as an intermediate fact. Conclude with `minor_ne (m := m) (n := n) τ (p τ) (n - (i + 1)) (i + 1) (by omega) (by omega)`.
-/
theorem delta_ne (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (hpq : ∀ τ, p τ + q τ ≤ m) (hmn : m ≤ n) :
    (delta p q ap am : MvPolynomial (FVar D m n) ℂ) ≠ 0 := by
  unfold delta deltaAt
  refine Finset.prod_ne_zero_iff.2 fun τ _ => mul_ne_zero
    (Finset.prod_ne_zero_iff.2 fun i hi => pow_ne_zero _ ?_) (Finset.prod_ne_zero_iff.2 fun i hi => pow_ne_zero _ ?_)
  · have := Finset.mem_range.1 hi
    have := hpq τ
    have h := minor_ne (m := m) (n := n) τ 0 0 (i + 1) (by omega) (by omega)
    simpa only [minorPlus, zero_add] using h
  · have := Finset.mem_range.1 hi
    have := hpq τ
    exact minor_ne (m := m) (n := n) τ (p τ) (n - (i + 1)) (i + 1) (by omega) (by omega)

/- English proof (translation)
Use `delta_ne _ _ _ _ (fun τ => ?_) ((rank_Wc i).le.trans (r_le_V i))` and prove the remaining obligations. Rewrite using `[D.sp.W_sigval _ (Nat.le_add_left _ _) i.2, rank_Wc]`. Use `i.2` as an intermediate fact. Simplify using `only [Ranks.sigW, Ranks.r]`. Use linear arithmetic over natural numbers and integers.
-/
theorem Delta_ne (i : Fin D.R.m) : RealDat.Delta (D := D) i ≠ 0 := by
  refine delta_ne _ _ _ _ (fun τ => ?_) ((rank_Wc i).le.trans (r_le_V i))
  rw [D.sp.W_sigval _ (Nat.le_add_left _ _) i.2, rank_Wc]
  have := i.2
  simp only [Ranks.sigW, Ranks.r]
  omega

end Minors

section Io

open Formalism.MainNotions.S Formalism.IndefR.Mult

variable {D : D7} {W : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel W S)

/- English proof (translation)
Use `lowK_irred (M.ds τ) (fun w w' h1 h2 h3 h1' h2' h3' => ?_) N hN hst` and prove the remaining obligations. Take `⟨e, he⟩` from `exists_isExtVec M hs`. Establish `hu : ∀ (x : M.sm τ), ‖(x : M.H τ)‖ = 1 → (x : M.H τ) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) → IsWtOn (Formalism.REAL.Kset (M.ε τ)) (M.σ τ) (extWt M τ) (x : M.H τ) → IsExtVec M (Function.update e τ x)`. Introduce `x a b c ρ`. Distinguish the cases in `h : ρ = τ`.

Substitute `h` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `⟨a, b, c⟩`. Rewrite using `[Function.update_of_ne h]`. Conclude with `he ρ`.

Take `⟨c, -, hc⟩` from `hl _ _ (hu ⟨w, hs τ h2⟩ h1 h2 h3) (hu ⟨w', hs τ h2'⟩ h1' h2' h3') τ`. Rewrite `hc` using `[Function.update_self, Function.update_self]`. Conclude with `⟨c, congrArg Subtype.val hc⟩`.
-/
theorem model_irred (hs : LowSm M) (hl : ExtLine M) (τ : D.what₂.Tau) (N : Submodule ℂ (M.H τ))
    (hN : N ≤ lowKSub (M.ε τ) (M.lam τ) (M.σ τ)) (hst : IsKStableOn (M.ε τ) (M.σ τ) N) :
    N = ⊥ ∨ N = lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := by
  refine lowK_irred (M.ds τ) (fun w w' h1 h2 h3 h1' h2' h3' => ?_) N hN hst
  obtain ⟨e, he⟩ := exists_isExtVec M hs
  have hu : ∀ (x : M.sm τ), ‖(x : M.H τ)‖ = 1 → (x : M.H τ) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) →
      IsWtOn (Formalism.REAL.Kset (M.ε τ)) (M.σ τ) (extWt M τ) (x : M.H τ) → IsExtVec M (Function.update e τ x) := by
    intro x a b c ρ
    by_cases h : ρ = τ
    · subst h
      rw [Function.update_self]
      exact ⟨a, b, c⟩
    · rw [Function.update_of_ne h]
      exact he ρ
  obtain ⟨c, -, hc⟩ := hl _ _ (hu ⟨w, hs τ h2⟩ h1 h2 h3) (hu ⟨w', hs τ h2'⟩ h1' h2' h3') τ
  rw [Function.update_self, Function.update_self] at hc
  exact ⟨c, congrArg Subtype.val hc⟩

/- English proof (translation)
Set `g : lowT M τ →ₗ[ℂ] X` to `f ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap v τ`. Establish `hg : ∀ y, g y = f (PiTensorProduct.tprod ℂ (Function.update v τ y))` using `fun y => rfl`. Set `j : lowT M τ →ₗ[ℂ] M.H τ` to `(M.sm τ).subtype ∘ₗ (lowT M τ).subtype`. Establish `hj : Function.Injective j` using `Subtype.val_injective.comp Subtype.val_injective`. Establish `hst` using `GlobalTheory.LowKProj.lowKSub_stable (M.ε τ) (M.lam τ) (M.σ τ)`.

Break down `model_irred M hs hl τ ((LinearMap.ker g).map j) (by rintro _ ⟨y, -, rfl⟩; exact y.2) (by` into its components or cases. Introduce and unpack `k hk _ ⟨y, hy, rfl⟩`. Establish `hm : M.σ τ k (j y) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ)` using `hst k hk _ y.2`. Use `⟨⟨⟨_, hs τ hm⟩, hm⟩, ?_, rfl⟩` and prove the remaining obligations. Use `hf k hk (Function.update v τ y) ⟨⟨_, hs τ hm⟩, hm⟩ (by rw [Function.update_self]; rfl)` as an intermediate fact.

Rewrite `this` using `[Function.update_idem, ← hg, ← hg, (LinearMap.mem_ker.1 hy : g y = 0), map_zero]`. Conclude with `this.symm) with h | h`. Establish `: j x ∈ (LinearMap.ker g).map j` using `⟨x, hx, rfl⟩`. Rewrite `this` using `[h, Submodule.mem_bot]`. Conclude with `hj (this.trans (map_zero j).symm)`.

Establish `: j (v τ) ∈ (LinearMap.ker g).map j` using `by rw [h]; exact (v τ).2`. Take `⟨y, hy, hy'⟩` from `this`. Rewrite `hy` using `[hj hy']`. Establish `h0 : g (v τ) = 0` using `hy`. Rewrite `h0` using `[hg, Function.update_eq_self]`.

Conclude with `absurd h0 hv`.
-/
theorem inj_factor (hs : LowSm M) (hl : ExtLine M) (τ : D.what₂.Tau) {X : Type} [AddCommGroup X] [Module ℂ X]
    (f : LowT M →ₗ[ℂ] X) (om : Matrix (Fin W.rank) (Fin W.rank) ℂ → X →ₗ[ℂ] X)
    (hf : ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ),
      ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) →
      om k (f (PiTensorProduct.tprod ℂ v)) = f (PiTensorProduct.tprod ℂ (Function.update v τ u)))
    (v : ∀ ρ, lowT M ρ) (hv : f (PiTensorProduct.tprod ℂ v) ≠ 0) (x : lowT M τ)
    (hx : f (PiTensorProduct.tprod ℂ (Function.update v τ x)) = 0) : x = 0 := by
  let g : lowT M τ →ₗ[ℂ] X := f ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap v τ
  have hg : ∀ y, g y = f (PiTensorProduct.tprod ℂ (Function.update v τ y)) := fun y => rfl
  let j : lowT M τ →ₗ[ℂ] M.H τ := (M.sm τ).subtype ∘ₗ (lowT M τ).subtype
  have hj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
  have hst := GlobalTheory.LowKProj.lowKSub_stable (M.ε τ) (M.lam τ) (M.σ τ)
  rcases model_irred M hs hl τ ((LinearMap.ker g).map j) (by rintro _ ⟨y, -, rfl⟩; exact y.2) (by
      rintro k hk _ ⟨y, hy, rfl⟩
      have hm : M.σ τ k (j y) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := hst k hk _ y.2
      refine ⟨⟨⟨_, hs τ hm⟩, hm⟩, ?_, rfl⟩
      have := hf k hk (Function.update v τ y) ⟨⟨_, hs τ hm⟩, hm⟩ (by rw [Function.update_self]; rfl)
      rw [Function.update_idem, ← hg, ← hg, (LinearMap.mem_ker.1 hy : g y = 0), map_zero] at this
      exact this.symm) with h | h
  · have : j x ∈ (LinearMap.ker g).map j := ⟨x, hx, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact hj (this.trans (map_zero j).symm)
  · have : j (v τ) ∈ (LinearMap.ker g).map j := by rw [h]; exact (v τ).2
    obtain ⟨y, hy, hy'⟩ := this
    rw [hj hy'] at hy
    have h0 : g (v τ) = 0 := hy
    rw [hg, Function.update_eq_self] at h0
    exact absurd h0 hv

end Io

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hR hV hM i`. Take `⟨hs, hl⟩` from `hM i`. Take `⟨-, hK, v, w, hv1, hw1, hio⟩` from `hR.thP.ioP i A.μ0`. Take `⟨hth, hvac, hcW, hcV, hbW⟩` from `GlobalTheory.T.theta_vector_fock_vacuum D G Pl0 T0 A Ks R F hR i A.μ0 (hV i)`. Establish `hP` using `(GlobalTheory.AdTh.RecPair.isPair_record D G Pl0 T0 A Ks R F hR i A.μ0 (hV i)).1`.

Establish `hinj` using `GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hP.weil.std hP.inf (fun _ => 1) (R.BV i) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) (fun τ => ((Wc D i).sig (tauE D τ)).1) hcV hcW (hR.models.BV i) hbW hP.sigV hP.sigW _ hth …`. Set `pt` to `pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) (R.vP i A.μ0)`. Set `f : LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)` to `pt ∘ₗ (R.ioP i).flip w`. Establish `hf : ∀ x, f x = R.ptP i A.μ0 (R.ioP i x w)` using `fun x => rfl`. Establish `hv0 : f (PiTensorProduct.tprod ℂ v) ≠ 0`.

Rewrite using `[hf, hio]`. Conclude with `fun h => Delta_ne i (hinj (h.trans (map_zero pt).symm))`. Use `⟨fun ρ => v ρ, fun τ => ⟨hv1 τ, (v τ).2, fun a ha => ?_⟩, v, w, fun _ => rfl, hw1, hio⟩` and prove the remaining obligations. Establish `hm` using `GlobalTheory.LowKProj.lowKSub_stable _ _ _ _ ha _ (v τ).2`. Set `u : lowT (R.MW i (sg0 D A)) τ` to `⟨⟨_, hs τ hm⟩, hm⟩`.

Establish `h1` using `hK τ _ ha v u rfl w`. Rewrite `h1` using `[hio, GlobalTheory.T.theta_vector_torus_action D G Pl0 T0 A Ks R F hR i (hV i) τ a A.μ0, ← hio, ← hf, ← hf]`. Establish `h2` using `inj_factor (R.MW i (sg0 D A)) hs hl τ f (fun k => R.ωP i A.μ0 (1, atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))) (fun k hk v u hu => hK τ k hk v u hu w) v hv0 (u - cexp (((∑ j, extWt (R.MW i (sg0 D A)) τ j * a j : ℝ) : ℂ) * I) • v τ) (by`. Rewrite using `[MultilinearMap.map_update_sub, MultilinearMap.map_update_smul, Function.update_eq_self, map_sub, map_smul, ← h1, sub_self])`. Conclude with `congrArg (fun y : lowT (R.MW i (sg0 D A)) τ => ((y : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ)) (sub_eq_zero.1 h2)`.
-/
theorem ioExt : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → (∀ i, VStd D i) → (∀ i, LowSm (R.MW i (sg0 D A)) ∧ ExtLine (R.MW i (sg0 D A))) → IoExt R := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR hV hM i
  obtain ⟨hs, hl⟩ := hM i
  obtain ⟨-, hK, v, w, hv1, hw1, hio⟩ := hR.thP.ioP i A.μ0
  obtain ⟨hth, hvac, hcW, hcV, hbW⟩ := GlobalTheory.T.theta_vector_fock_vacuum D G Pl0 T0 A Ks R F hR i A.μ0 (hV i)
  have hP := (GlobalTheory.AdTh.RecPair.isPair_record D G Pl0 T0 A Ks R F hR i A.μ0 (hV i)).1
  have hinj := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hP.weil.std hP.inf (fun _ => 1) (R.BV i)
    (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) (fun τ => ((Wc D i).sig (tauE D τ)).1)
    hcV hcW (hR.models.BV i) hbW hP.sigV hP.sigW _ hth hvac (GlobalTheory.T.theta_vector_ne_zero D G Pl0 T0 A Ks R F hR i (hV i))
  let pt := pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
    (R.vP i A.μ0)
  let f : LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) := pt ∘ₗ (R.ioP i).flip w
  have hf : ∀ x, f x = R.ptP i A.μ0 (R.ioP i x w) := fun x => rfl
  have hv0 : f (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    rw [hf, hio]
    exact fun h => Delta_ne i (hinj (h.trans (map_zero pt).symm))
  refine ⟨fun ρ => v ρ, fun τ => ⟨hv1 τ, (v τ).2, fun a ha => ?_⟩, v, w, fun _ => rfl, hw1, hio⟩
  have hm := GlobalTheory.LowKProj.lowKSub_stable _ _ _ _ ha _ (v τ).2
  let u : lowT (R.MW i (sg0 D A)) τ := ⟨⟨_, hs τ hm⟩, hm⟩
  have h1 := hK τ _ ha v u rfl w
  rw [hio, GlobalTheory.T.theta_vector_torus_action D G Pl0 T0 A Ks R F hR i (hV i) τ a A.μ0, ← hio, ← hf, ← hf] at h1
  have h2 := inj_factor (R.MW i (sg0 D A)) hs hl τ f
    (fun k => R.ωP i A.μ0 (1, atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ)))
    (fun k hk v u hu => hK τ k hk v u hu w) v hv0
    (u - cexp (((∑ j, extWt (R.MW i (sg0 D A)) τ j * a j : ℝ) : ℂ) * I) • v τ) (by
      rw [MultilinearMap.map_update_sub, MultilinearMap.map_update_smul, Function.update_eq_self, map_sub, map_smul, ← h1,
        sub_self])
  exact congrArg (fun y : lowT (R.MW i (sg0 D A)) τ => ((y : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ))
    (sub_eq_zero.1 h2)

end GlobalTheory.AdTh.IoExtPf
