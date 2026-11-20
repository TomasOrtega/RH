import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HkMemFixed
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeSub

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Establish `hc : IsCompact (tsupport e)` using `hE.2.2.1`. Take `⟨t, ht⟩` from `hc.elim_finite_subcover (fun g : GL ι F => (fun x => g⁻¹ * x) ⁻¹' (K : Set (GL ι F))) (fun g => hE.1.preimage (continuous_const.mul continuous_id)) (fun g _ => Set.mem_iUnion.2 ⟨g, by simp [K.one_mem]⟩)`. Use `(t.finite_toSet.image (fun g => (QuotientGroup.mk g : GL ι F ⧸ K))).subset fun q hq => ?_` and prove the remaining obligations. Establish `hq' : q.out ∈ tsupport e` using `subset_tsupport _ hq`. Take `⟨g, hg, hgq⟩` from `Set.mem_iUnion₂.1 (ht hq')`.

Conclude with `⟨g, hg, (QuotientGroup.eq.2 hgq).trans (QuotientGroup.out_eq' q)⟩`.
-/
theorem finite_cosets {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (hE : IsHk K e) :
    {q : GL ι F ⧸ K | e q.out ≠ 0}.Finite := by
  have hc : IsCompact (tsupport e) := hE.2.2.1
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun g : GL ι F => (fun x => g⁻¹ * x) ⁻¹' (K : Set (GL ι F)))
    (fun g => hE.1.preimage (continuous_const.mul continuous_id))
    (fun g _ => Set.mem_iUnion.2 ⟨g, by simp [K.one_mem]⟩)
  refine (t.finite_toSet.image (fun g => (QuotientGroup.mk g : GL ι F ⧸ K))).subset fun q hq => ?_
  have hq' : q.out ∈ tsupport e := subset_tsupport _ hq
  obtain ⟨g, hg, hgq⟩ := Set.mem_iUnion₂.1 (ht hq')
  exact ⟨g, hg, (QuotientGroup.eq.2 hgq).trans (QuotientGroup.out_eq' q)⟩

/- English proof (translation)
Unfold `hk`. Establish `hfin : (Function.support fun q : GL ι F ⧸ K => e q.out • ρ q.out v).Finite` using `(finite_cosets hE).subset fun q hq h0 => hq (by simp [show e q.out = 0 from h0])`. Rewrite using `[map_finsum f hfin]`. Simplify using `only [map_smul, hf]`.
-/
theorem hk_map {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL ι F) V) (σ : Representation ℂ (GL ι F) W) (f : V →ₗ[ℂ] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (hE : IsHk K e) (v : V) :
    f (hk ρ K e v) = hk σ K e (f v) := by
  unfold hk
  have hfin : (Function.support fun q : GL ι F ⧸ K => e q.out • ρ q.out v).Finite :=
    (finite_cosets hE).subset fun q hq h0 => hq (by simp [show e q.out = 0 from h0])
  rw [map_finsum f hfin]
  simp only [map_smul, hf]

/- English proof (translation)
Take `⟨hGT, hLT⟩` from `(hasFiniteLength_iff_wellFounded ρ).1 hfl`. Proceed by induction on `S using WellFoundedLT.induction with`. Consider the case `ind S ih`. Distinguish the cases in `hS : S = ⊥`. Substitute `hS` using the available equality.

Conclude with `⟨0, fun u hu _ => hu⟩`. Take `⟨T, hT, hmax⟩` from `(wellFounded_gt (α := Subrepresentation ρ)).has_min {T | T < S} ⟨⊥, bot_lt_iff_ne_bot.2 hS⟩`. Establish `hcov : T ⋖ S` using `⟨hT, fun c h1 h2 => hmax c h2 h1⟩`. Set `p : S.toRepresentation.IntertwiningMap (subQuot S T)` to `⟨Submodule.mkQ _, fun _ => rfl⟩`. Establish `hsq : IsSubquotient (subQuot S T) ρ` using `⟨S, p, Submodule.mkQ_surjective _⟩`.

Establish `hne : IsEmpty ((subQuot S T).Equiv π)` using `⟨fun φ => hns ((IsSubquotient.trans (IsSubquotient.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective) hsq))⟩`. Take `⟨r, hr⟩` from `ih T hT`. Use `⟨r + 1, fun u huS hufix => ?_⟩` and prove the remaining obligations. Establish `hfixS : (Submodule.mkQ _ (⟨u, huS⟩ : S.toSubmodule) : S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) ∈ fixed (subQuot S T) K`. Introduce `h`.

Establish `h1 : ρ (h : GL ι F) u = u` using `by simpa using hufix h`. Establish `h2 : S.toRepresentation (h : GL ι F) ⟨u, huS⟩ = ⟨u, huS⟩` using `Subtype.ext h1`. Simplify using `only [MonoidHom.one_apply, Units.val_one, one_smul]`. Conclude with `congrArg (Submodule.mkQ _) h2`. Establish `h0` using `hkill _ (subQuot S T) (hsq.isSmooth hρ) (isIrreducible_subQuot hcov) hne _ hfixS`.

Establish `h1 : (hk S.toRepresentation K e ⟨u, huS⟩ : S.toSubmodule).1 = hk ρ K e u` using `hk_map S.toRepresentation ρ S.toSubmodule.subtype (fun _ _ => rfl) hE ⟨u, huS⟩`. Establish `h2` using `hk_map S.toRepresentation (subQuot S T) (Submodule.mkQ _) (fun _ _ => rfl) hE ⟨u, huS⟩`. Rewrite `h2` using `[h0]`. Establish `h3 : hk ρ K e u ∈ T.toSubmodule`. Rewrite using `[← h1]`.

Conclude with `(Submodule.Quotient.mk_eq_zero (T.toSubmodule.comap S.toSubmodule.subtype)).1 h2`. Rewrite using `[Function.iterate_succ_apply]`. Conclude with `hr _ h3 (GlobalTheory.CompanionTheory.HeckeFix.hk_mem_fixed F ι K e hE U ρ u hufix).1`.
-/
theorem exists_iterate_eq_zero {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (hE : IsHk K e) (π : Representation ℂ (GL ι F) V)
    (hkill : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL ι F) W), IsSmooth τ →
      τ.IsIrreducible → IsEmpty (τ.Equiv π) → ∀ w ∈ fixed τ K, hk τ K e w = 0)
    (ρ : Representation ℂ (GL ι F) U) (hρ : IsSmooth ρ) (hfl : HasFiniteLength ρ)
    (hns : ¬ IsSubquotient π ρ) (S : Subrepresentation ρ) :
    ∃ r : ℕ, ∀ u ∈ S.toSubmodule, u ∈ fixed ρ K → (hk ρ K e)^[r] u = 0 := by
  obtain ⟨hGT, hLT⟩ := (hasFiniteLength_iff_wellFounded ρ).1 hfl
  induction S using WellFoundedLT.induction with
  | ind S ih =>
    by_cases hS : S = ⊥
    · subst hS
      exact ⟨0, fun u hu _ => hu⟩
    obtain ⟨T, hT, hmax⟩ := (wellFounded_gt (α := Subrepresentation ρ)).has_min {T | T < S}
      ⟨⊥, bot_lt_iff_ne_bot.2 hS⟩
    have hcov : T ⋖ S := ⟨hT, fun c h1 h2 => hmax c h2 h1⟩
    let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    have hsq : IsSubquotient (subQuot S T) ρ := ⟨S, p, Submodule.mkQ_surjective _⟩
    have hne : IsEmpty ((subQuot S T).Equiv π) := ⟨fun φ => hns
      ((IsSubquotient.trans (IsSubquotient.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective) hsq))⟩
    obtain ⟨r, hr⟩ := ih T hT
    refine ⟨r + 1, fun u huS hufix => ?_⟩
    have hfixS : (Submodule.mkQ _ (⟨u, huS⟩ : S.toSubmodule) :
        S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) ∈ fixed (subQuot S T) K := by
      intro h
      have h1 : ρ (h : GL ι F) u = u := by simpa using hufix h
      have h2 : S.toRepresentation (h : GL ι F) ⟨u, huS⟩ = ⟨u, huS⟩ := Subtype.ext h1
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      exact congrArg (Submodule.mkQ _) h2
    have h0 := hkill _ (subQuot S T) (hsq.isSmooth hρ) (isIrreducible_subQuot hcov) hne _ hfixS
    have h1 : (hk S.toRepresentation K e ⟨u, huS⟩ : S.toSubmodule).1 = hk ρ K e u :=
      hk_map S.toRepresentation ρ S.toSubmodule.subtype (fun _ _ => rfl) hE ⟨u, huS⟩
    have h2 := hk_map S.toRepresentation (subQuot S T) (Submodule.mkQ _) (fun _ _ => rfl) hE ⟨u, huS⟩
    rw [h0] at h2
    have h3 : hk ρ K e u ∈ T.toSubmodule := by
      rw [← h1]
      exact (Submodule.Quotient.mk_eq_zero (T.toSubmodule.comap S.toSubmodule.subtype)).1 h2
    rw [Function.iterate_succ_apply]
    exact hr _ h3 (GlobalTheory.CompanionTheory.HeckeFix.hk_mem_fixed F ι K e hE U ρ u hufix).1

/- English proof (translation)
Introduce `F _ _ _ _ ι _ _ K e hE V _ _ π _ _ hkill U _ _ ρ hρ hfl hnil`. Assume the negation of the conclusion as `hns`. Take `⟨r, hr⟩` from `exists_iterate_eq_zero hE π hkill ρ hρ hfl hns ⊤`. Take `⟨u, hu, hne⟩` from `hnil r`. Conclude with `hne (hr u trivial hu)`.
-/
theorem subOfNonNil : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], SubOfNonNil F ι := by
  intro F _ _ _ _ ι _ _ K e hE V _ _ π _ _ hkill U _ _ ρ hρ hfl hnil
  by_contra hns
  obtain ⟨r, hr⟩ := exists_iterate_eq_zero hE π hkill ρ hρ hfl hns ⊤
  obtain ⟨u, hu, hne⟩ := hnil r
  exact hne (hr u trivial hu)

end GlobalTheory.CompanionTheory.HeckeSub
