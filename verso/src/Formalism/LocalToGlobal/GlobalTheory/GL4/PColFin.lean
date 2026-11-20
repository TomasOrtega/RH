import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL4.PColLoc

open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.BasicNotions.SkeletonIndexLemmas Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions.flipTwoThree
open Formalism.LFunctionChainParameters.slopeLatticeData (FinPl)

section Alg

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem actAll_eq_actP (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (p : Pol K ι n) :
    actAll lam (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) p = actP lam g p := by
  unfold actAll actP detTwK detPow trAct Formalism.GradedWeylDivisibility.blockAct
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]

def rhoEquiv (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) : VV K lam ≃ₗ[K] VV K lam :=
  LinearEquiv.ofLinearMap (rhoK lam g) (rhoK lam g⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rhoEquiv_apply (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (y : VV K lam) : rhoEquiv lam g y = rhoK lam g y := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem rhoEquiv_symm_coe (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (y : VV K lam) :
    (((rhoEquiv lam g).symm y : VV K lam) : Pol K ι n) =
      actAll lam (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)⁻¹) (y : Pol K ι n) := by
  show actP lam g⁻¹ (y : Pol K ι n) = _
  rw [← actAll_eq_actP]
  congr 1
  funext τ
  simp

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the resulting assumption.
-/
theorem mem_span_subtype {P : Type} [AddCommGroup P] [Module K P] (R : Subring K) (U : Submodule K P) {J : Type} (b : J → U) (y : U) :
    y ∈ Submodule.span R (Set.range b) ↔ (y : P) ∈ Submodule.span R (Set.range fun i => (b i : P)) := by
  have h : (Submodule.span R (Set.range b)).map (U.subtype.restrictScalars R) =
      Submodule.span R (Set.range fun i => (b i : P)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [← h]
  constructor
  · intro hy; exact ⟨y, hy, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    have : z = y := Subtype.ext hzy
    rwa [← this]

end Alg

section Gen

variable {K : Type} [Field K] [NumberField K] {V W : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W]
  {Cl : Type} [Fintype Cl] [DecidableEq Cl] {J0 : Type} [Fintype J0] [DecidableEq J0]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem sumBasis_twist (coE : V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W) (Φ : Cl → (W ≃ₗ[K] W)) :
    ⇑(sumBasis (coE.trans (LinearEquiv.piCongrRight fun c => (Φ c).symm)) BK) =
      fun j : J0 × Cl => coE.symm (Pi.single j.2 (Φ j.2 (BK j.1))) := by
  funext ⟨i, c⟩
  rw [sumBasis_apply]
  show coE.symm ((LinearEquiv.piCongrRight fun c => (Φ c).symm).symm (Pi.single c (BK i))) = _
  congr 1
  funext c'
  show (Φ c').symm.symm ((Pi.single c (BK i) : Cl → W) c') = _
  by_cases h : c' = c
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

end Gen

section Rec

variable {D : D7}

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.
-/
theorem exists_locBasis (w : D.what₂.places.Pl) (Q : HLat D.what₂.LL) (hQ : Q.Good) {n : ℕ} (e : Q.ι ≃ Fin n) :
    ∃ γ, LocBasis D w Q e γ := by
  classical
  have hn : Module.finrank D.what₂.LL Q.V = n := by
    rw [Module.finrank_eq_card_basis Q.b, Fintype.card_congr e, Fintype.card_fin]
  obtain ⟨bK, hbK⟩ := exists_basis_locP (D.plEq w) hQ.2.1 hQ.2.2 hn
  refine ⟨(Q.b.reindex e).toMatrix bK, ?_, ?_⟩
  · have := (Q.b.reindex e).isUnit_det bK
    rwa [Basis.det_apply] at this
  · have hfam : (fun a : Fin n => ∑ i, (Q.b.reindex e).toMatrix bK i a • Q.b (e.symm i)) = bK := by
      funext a
      have := (Q.b.reindex e).sum_repr (bK a)
      simpa [Basis.toMatrix_apply, Basis.reindex_apply] using this
    rw [hfam]
    ext x
    rw [← mem_localization_iff_localizationAtPlace, ← hbK, mem_localization_latticeOf_iff]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.
-/
theorem localization_eq_of_locBasis (w : D.what₂.places.Pl) (Q : HLat D.what₂.LL) {n : ℕ} (e : Q.ι ≃ Fin n)
    (γ : Matrix (Fin n) (Fin n) D.what₂.LL) (h : LocBasis D w Q e γ) :
    localization₂ (D.plEq w).asIdeal Q.L =
      localization₂ (D.plEq w).asIdeal (latOf (K := D.what₂.LL) fun a : Fin n => ∑ i, γ i a • Q.b (e.symm i)) := by
  ext x
  rw [mem_localization_iff_localizationAtPlace, h.2, mem_localization_latticeOf_iff]

variable {u : D.what₂.Word} (CV : ColVal D u) (hTV : TSpan D.what₂.LL ((D.fm u).lam 0) = VV D.what₂.LL ((D.fm u).lam 0))

def coL : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)) :=
  LinearMap.pi fun c => LinearMap.codRestrict (VV D.what₂.LL ((D.fm u).lam 0)) ((LinearMap.proj c).comp CV.co)
    (fun x => hTV ▸ ((CV.co_range _).1 ⟨x, rfl⟩ c))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coL_coe (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    ((coL CV hTV x c : VV D.what₂.LL ((D.fm u).lam 0)) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0)) = CV.co x c := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem coL_bijective : Function.Bijective (coL CV hTV) := by
  constructor
  · intro x y h
    apply CV.co_inj
    funext c
    exact congrArg Subtype.val (congrFun h c)
  · intro F
    obtain ⟨x, hx⟩ := (CV.co_range (fun c => ((F c : VV D.what₂.LL ((D.fm u).lam 0)) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0)))).2
      (fun c => hTV.symm ▸ (F c).2)
    refine ⟨x, ?_⟩
    funext c
    apply Subtype.ext
    rw [coL_coe, hx]

def coE : ((D.fm u).lat 0).V ≃ₗ[D.what₂.LL] ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)) :=
  LinearEquiv.ofBijective (coL CV hTV) (coL_bijective CV hTV)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coE_coe (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    ((coE CV hTV x c : VV D.what₂.LL ((D.fm u).lam 0)) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0)) = CV.co x c := rfl

open Classical in

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem localization_lattice_eq (Z : ZBasis ((D.fm u).lam 0)) (w : D.what₂.places.Pl)
    (g : (D.mem u).C.cls 0 → D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL)
    (hg : ∀ c τ, LocBasis D w (CV.Q c τ) (CV.eQ c τ) (g c τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)) :
    localization₂ (D.plEq w).asIdeal ((D.fm u).lat 0).L =
      localization₂ (D.plEq w).asIdeal (latOf (K := D.what₂.LL) fun j : Z.J0 × (D.mem u).C.cls 0 =>
        (coE CV hTV).symm (Pi.single j.2 (rhoK ((D.fm u).lam 0) (g j.2) (Z.basis D.what₂.LL j.1)))) := by
  ext x
  have hf := sumBasis_twist (coE CV hTV) (Z.basis D.what₂.LL) (fun c => rhoEquiv ((D.fm u).lam 0) (g c))
  simp only [rhoEquiv_apply] at hf
  rw [mem_localization_iff_localizationAtPlace, CV.fin w (fun c τ => (g c τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)) hg x,
    mem_localization_latticeOf_iff, ← hf, mem_span_sumBasis]
  refine forall_congr' fun c => ?_
  rw [mem_span_subtype, mem_intSpanAt_iff w _ Z]
  have h1 : (fun i => ((Z.basis D.what₂.LL i : VV D.what₂.LL ((D.fm u).lam 0)) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0))) =
      fun i => MvPolynomial.map (Int.castRingHom D.what₂.LL) (Z.bZ i) := funext fun i => Z.basis_coe D.what₂.LL i
  rw [h1]
  have h2 : ((((coE CV hTV).trans (LinearEquiv.piCongrRight fun c => (rhoEquiv ((D.fm u).lam 0) (g c)).symm)) x c :
      VV D.what₂.LL ((D.fm u).lam 0)) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0)) =
      actAll ((D.fm u).lam 0) (fun τ => (g c τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)⁻¹) (CV.co x c) :=
    rhoEquiv_symm_coe _ _ _
  rw [h2]

end Rec

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
