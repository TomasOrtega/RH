import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleTensorOfJacquetSubquotient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientJacquetModuleRefineTensorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmptyPiTensorIsSubquotientJacquetModuleDegreeZerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientJacquetModuleSingleBlockSelfStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

noncomputable section

namespace GlobalTheory.CuspQuot

/- English proof (translation)
The claim follows from `GlobalTheory.T.isSubquotient_jacquetModule_refine_tensor`.
-/
theorem stage : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
    ∀ (X : Fin s → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), (∀ a, IsSmooth (ρ a)) →
    IsSubquotient (piTensor ρ) (jac e π) →
    ∀ (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (Y : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (Y a b)] [∀ a b, Module ℂ (Y a b)]
    (ρ' : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (Y a b)),
    (∀ a, IsSubquotient (piTensor (ρ' a)) (jac (e' a) (ρ a))) →
    ∃ E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n,
      IsSubquotient (piTensor fun c => ρ' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) (jac E π) := GlobalTheory.T.isSubquotient_jacquetModule_refine_tensor

/- English proof (translation)
The claim follows from `GlobalTheory.T.emptyPiTensor_isSubquotient_jacquetModule_degreeZero`.
-/
theorem degZero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ), N = 0 → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (π : Representation ℂ (GL (Fin N) k) V) (d : Fin 0 → ℕ) (X : Fin 0 → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (e : (Σ a, Fin (d a)) ≃ Fin N),
    IsSubquotient (piTensor ρ) (jac e π) := GlobalTheory.T.emptyPiTensor_isSubquotient_jacquetModule_degreeZero

/- English proof (translation)
The claim follows from `GlobalTheory.T.isSubquotient_jacquetModule_singleBlock_self`.
-/
theorem oneBlock : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (e : (Σ _ : Fin 1, Fin N) ≃ Fin N), IsSubquotient (piTensor fun _ : Fin 1 => π) (jac e π) := GlobalTheory.T.isSubquotient_jacquetModule_singleBlock_self

open GlobalTheory.Published GlobalTheory.LocGL.SupportUnique

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`. Introduce and unpack `x rfl s hs`. Use `haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible x.2.rep.irr`. Break down `Nat.eq_zero_or_pos x.1 with h0 | hpos` into its components or cases.

Use `haveI : IsEmpty (Fin x.1) := by rw [h0]; infer_instance`. Conclude with `⟨0, Fin.elim0, Equiv.equivOfIsEmpty _ _, fun a => a.elim0, degZero k x.1 h0 _ x.rep _ _ _ _⟩`. Distinguish the cases in `hc : IsCuspidal x.rep`. Rewrite using `[eq_singleton_of_isCusp ⟨hpos, hc⟩ hs]`. Conclude with `⟨1, fun _ => x, GlobalTheory.JacTensor.oneBlock x.1, fun _ => Multiset.mem_singleton_self x, oneBlock k x.1 _ x.rep _⟩`.

Take `⟨r, d, e, hU, hJ⟩ : ∃ (r : ℕ) (d : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin x.1), unipRad k e ≠ ⊥ ∧ ¬ Subsingleton (Jacquet x.rep (unipRad k e))` from `by by_contra! hn`. Conclude with `hc ⟨x.2.rep.smooth, hn⟩`. Take `⟨Y, _, _, τ, hτ, hτs⟩` from `GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ (jac e x.rep) (not_subsingleton_iff_nontrivial.1 hJ)`. Establish `hτsm : IsSmooth τ` using `hτs.isSmooth (isSmooth_jac e x.2.rep.smooth)`. Establish `hy : ∀ j, ∃ y : IrrRep (GL (Fin (d j)) k), IsSubquotient y.ρ (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) : Representation ℂ (GL (Fin (d j)) k) Y)`.

Introduce `j`. Take `⟨X, _, _, υ, hυ, hυs⟩` from `GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j)) (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ)`. Conclude with `⟨⟨X, υ, hυs.isSmooth (isSmooth_comp hτsm _ (continuous_mulSingle (A := fun j => GL (Fin (d j)) k) j)), hυ⟩, hυs⟩`. Use `choose y hy using hy`. Take `⟨t, ht, rfl⟩` from `exists_sum_of_jac hG hZ hs e hτ hτs y hy`.

Establish `hlt : ∀ j, d j < x.1`. Introduce `j`. Establish `hN : ∑ a, d a = x.1` using `by simpa using Fintype.card_congr e`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha, hda⟩ : ∃ a, a ≠ j ∧ 0 < d a := by`. Take `⟨p, q, hpq⟩` from `GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.1 hU`.

Take `⟨⟨a, p⟩, rfl⟩` from `e.surjective p`. Take `⟨⟨b, q⟩, rfl⟩` from `e.surjective q`. Rewrite `hpq` using `[blk_apply, blk_apply]`. Distinguish the cases in `haj : a = j`. Conclude with `⟨b, fun hb => hpq.ne (haj.trans hb.symm), q.pos⟩`.

Conclude with `⟨a, haj, p.pos⟩`. Establish `h1` using `Finset.add_le_sum (s := Finset.univ) (f := d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a) (Finset.mem_univ j) ha`. Use linear arithmetic over natural numbers and integers. Set `z : Fin r → IrrGL k` to `fun j => IrrGL.of (y j).ρ (y j).smooth (y j).irr`. Establish `hrec` using `fun j => ih (d j) (hlt j) (z j) rfl (t j) ((ht j).of_equiv (IrrGL.equivOf _ _ _))`.

Use `choose T u E hu hsub using hrec`. Set `πI : GlobalTheory.SplitRead.Irr k x.1` to `⟨x.2.rep.V, x.rep, x.2.rep.smooth, x.2.rep.irr⟩`. Take `⟨σ, hσ⟩` from `GlobalTheory.JacTensor.exists_irr_tensor_of_isSubquotient_jac hG k x.1 πI r d e Y τ hτ hτs`. Establish `hSch : ∀ a, ∀ φ : (σ a).V →ₗ[ℂ] (σ a).V, (∀ g v, φ ((σ a).π g v) = (σ a).π g (φ v)) → ∃ c : ℂ, φ = c • LinearMap.id` using `fun a => GlobalTheory.SchurAdm.schur_admissible _ (GlobalTheory.SplitWeil.KO k (Fin (d a))) GlobalTheory.SplitFlip.isOpen_KO GlobalTheory.SplitFlip.isCompact_KO (σ a).V (σ a).π (σ a).irr ((hBZ k).1 (Fin (d a)) (σ a).V (σ a).π (σ a).smooth (σ a).irr)`. Establish `hirr : (piTensor fun a => (σ a).π).IsIrreducible` using `GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (σ a).irr) hSch`.

Take `⟨φ⟩` from `nonempty_equiv_of_isSubquotient hτ hirr hσ`. Establish `hyσ : ∀ j, Nonempty ((σ j).π.Equiv (y j).ρ)` using `fun j => nonempty_equiv_of_isSubquotient (y j).irr (σ j).irr (isSubquotient_factor (fun a => (σ a).π) j (y j).irr ((hy j).trans (isSubquotient_comp (.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective) _)))`. Establish `ψ` using `fun j => (hyσ j).some`. Set `χ : (piTensor fun j => (z j).rep).Equiv τ` to `(piTensorEquiv fun j => ((ψ j).trans (IrrGL.equivOf (y j).ρ (y j).smooth (y j).irr)).symm).trans φ`. Establish `hz : IsSubquotient (piTensor fun j => (z j).rep) (jac e x.rep)` using `(IsSubquotient.of_injective χ.toIntertwiningMap χ.toLinearEquiv.injective).trans hτs`.

Take `⟨E', hE'⟩` from `stage k x.1 r d e _ x.rep x.2.rep.smooth _ (fun j => (z j).rep) (fun j => (z j).2.rep.smooth) hz T (fun a b => (u a b).1) E _ (fun a b => (u a b).rep) hsub`. Use `⟨∑ a, T a, fun c => u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2, E', fun c => ?_, hE'⟩` and prove the remaining obligations. Conclude with `Multiset.mem_of_le (Finset.single_le_sum (f := t) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ (finSigmaFinEquiv.symm c).1)) (hu _ _)`.
-/
theorem finiteRing_sq_sub_mul_sq_eq_of_card (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) (hZ : ZelevinskyPolynomialRing) (N : ℕ) :
    ∀ (x : IrrGL k), x.1 = N → ∀ s : Multiset (IrrGL k), HasSupport x.rep s →
      ∃ (r : ℕ) (u : Fin r → IrrGL k) (e : (Σ a, Fin (u a).1) ≃ Fin x.1),
        (∀ a, u a ∈ s) ∧ IsSubquotient (piTensor fun a => (u a).rep) (jac e x.rep) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rintro x rfl s hs
    haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible x.2.rep.irr
    rcases Nat.eq_zero_or_pos x.1 with h0 | hpos
    · haveI : IsEmpty (Fin x.1) := by rw [h0]; infer_instance
      exact ⟨0, Fin.elim0, Equiv.equivOfIsEmpty _ _, fun a => a.elim0,
        degZero k x.1 h0 _ x.rep _ _ _ _⟩
    by_cases hc : IsCuspidal x.rep
    · rw [eq_singleton_of_isCusp ⟨hpos, hc⟩ hs]
      exact ⟨1, fun _ => x, GlobalTheory.JacTensor.oneBlock x.1, fun _ => Multiset.mem_singleton_self x,
        oneBlock k x.1 _ x.rep _⟩
    obtain ⟨r, d, e, hU, hJ⟩ : ∃ (r : ℕ) (d : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin x.1), unipRad k e ≠ ⊥ ∧
        ¬ Subsingleton (Jacquet x.rep (unipRad k e)) := by
      by_contra! hn
      exact hc ⟨x.2.rep.smooth, hn⟩
    obtain ⟨Y, _, _, τ, hτ, hτs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ (jac e x.rep)
      (not_subsingleton_iff_nontrivial.1 hJ)
    have hτsm : IsSmooth τ := hτs.isSmooth (isSmooth_jac e x.2.rep.smooth)
    have hy : ∀ j, ∃ y : IrrRep (GL (Fin (d j)) k), IsSubquotient y.ρ
        (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) : Representation ℂ (GL (Fin (d j)) k) Y) := by
      intro j
      obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
        (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j))
        (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ)
      exact ⟨⟨X, υ, hυs.isSmooth (isSmooth_comp hτsm _
        (continuous_mulSingle (A := fun j => GL (Fin (d j)) k) j)), hυ⟩, hυs⟩
    choose y hy using hy
    obtain ⟨t, ht, rfl⟩ := exists_sum_of_jac hG hZ hs e hτ hτs y hy
    have hlt : ∀ j, d j < x.1 := by
      intro j
      have hN : ∑ a, d a = x.1 := by simpa using Fintype.card_congr e
      obtain ⟨a, ha, hda⟩ : ∃ a, a ≠ j ∧ 0 < d a := by
        obtain ⟨p, q, hpq⟩ := GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.1 hU
        obtain ⟨⟨a, p⟩, rfl⟩ := e.surjective p
        obtain ⟨⟨b, q⟩, rfl⟩ := e.surjective q
        rw [blk_apply, blk_apply] at hpq
        by_cases haj : a = j
        · exact ⟨b, fun hb => hpq.ne (haj.trans hb.symm), q.pos⟩
        · exact ⟨a, haj, p.pos⟩
      have h1 := Finset.add_le_sum (s := Finset.univ) (f := d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
        (Finset.mem_univ j) ha
      omega
    let z : Fin r → IrrGL k := fun j => IrrGL.of (y j).ρ (y j).smooth (y j).irr
    have hrec := fun j => ih (d j) (hlt j) (z j) rfl (t j) ((ht j).of_equiv (IrrGL.equivOf _ _ _))
    choose T u E hu hsub using hrec

    let πI : GlobalTheory.SplitRead.Irr k x.1 := ⟨x.2.rep.V, x.rep, x.2.rep.smooth, x.2.rep.irr⟩
    obtain ⟨σ, hσ⟩ := GlobalTheory.JacTensor.exists_irr_tensor_of_isSubquotient_jac hG k x.1 πI r d e Y τ hτ hτs
    have hSch : ∀ a, ∀ φ : (σ a).V →ₗ[ℂ] (σ a).V, (∀ g v, φ ((σ a).π g v) = (σ a).π g (φ v)) →
        ∃ c : ℂ, φ = c • LinearMap.id := fun a =>
      GlobalTheory.SchurAdm.schur_admissible _ (GlobalTheory.SplitWeil.KO k (Fin (d a))) GlobalTheory.SplitFlip.isOpen_KO
        GlobalTheory.SplitFlip.isCompact_KO (σ a).V (σ a).π (σ a).irr ((hBZ k).1 (Fin (d a)) (σ a).V (σ a).π (σ a).smooth (σ a).irr)
    have hirr : (piTensor fun a => (σ a).π).IsIrreducible :=
      GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (σ a).irr) hSch
    obtain ⟨φ⟩ := nonempty_equiv_of_isSubquotient hτ hirr hσ
    have hyσ : ∀ j, Nonempty ((σ j).π.Equiv (y j).ρ) := fun j =>
      nonempty_equiv_of_isSubquotient (y j).irr (σ j).irr
        (isSubquotient_factor (fun a => (σ a).π) j (y j).irr ((hy j).trans
          (isSubquotient_comp (.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective) _)))
    have ψ := fun j => (hyσ j).some
    let χ : (piTensor fun j => (z j).rep).Equiv τ :=
      (piTensorEquiv fun j => ((ψ j).trans (IrrGL.equivOf (y j).ρ (y j).smooth (y j).irr)).symm).trans φ
    have hz : IsSubquotient (piTensor fun j => (z j).rep) (jac e x.rep) :=
      (IsSubquotient.of_injective χ.toIntertwiningMap χ.toLinearEquiv.injective).trans hτs
    obtain ⟨E', hE'⟩ := stage k x.1 r d e _ x.rep x.2.rep.smooth _ (fun j => (z j).rep) (fun j => (z j).2.rep.smooth) hz
      T (fun a b => (u a b).1) E _ (fun a b => (u a b).rep) hsub
    refine ⟨∑ a, T a, fun c => u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2, E', fun c => ?_, hE'⟩
    exact Multiset.mem_of_le (Finset.single_le_sum (f := t) (fun _ _ => Multiset.zero_le _)
      (Finset.mem_univ (finSigmaFinEquiv.symm c).1)) (hu _ _)

/- English proof (translation)
Introduce `hG hBZ hZ _ _ _ _ _ _ x s hs` and use `finiteRing_sq_sub_mul_sq_eq_of_card hG hBZ hZ x.1 x rfl s hs`.
-/
theorem exists_isSubquotient_jac_of_hasSupport : GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL k) (s : Multiset (IrrGL k)), HasSupport x.rep s → ∃ (r : ℕ) (u : Fin r → IrrGL k) (e : (Σ a, Fin (u a).1) ≃ Fin x.1), (∀ a, u a ∈ s) ∧ IsSubquotient (piTensor fun a => (u a).rep) (jac e x.rep) :=
  fun hG hBZ hZ _ _ _ _ _ _ x s hs => finiteRing_sq_sub_mul_sq_eq_of_card hG hBZ hZ x.1 x rfl s hs

end GlobalTheory.CuspQuot
