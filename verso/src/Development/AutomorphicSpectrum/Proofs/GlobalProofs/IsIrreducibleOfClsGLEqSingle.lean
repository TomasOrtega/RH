import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TotallyDisjointProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCuspidalSupportIrreducibleSmoothGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonomialOfCountZero
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.RankOne

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.JHMult GlobalTheory.LocGL.SupportRing GlobalTheory.LocGL.UnramSupport

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `e` using `clsGL_of_pos hB hs hi hsq`. Rewrite `e` using `[h, Finsupp.single_apply]`. Use `split_ifs at e with heq`. Conclude with `heq.symm`. Conclude with `absurd e (lt_irrefl 0)`.
-/
private theorem irrGL_of_eq_of_cls_single {N : ℕ} {B : Representation ℂ (GL (Fin N) k) V}
    (hB : HasFiniteLength B) {w : IrrGL k} (h : clsGL B hB = Finsupp.single w 1)
    {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GL (Fin N) k) W}
    (hs : IsSmooth σ) (hi : σ.IsIrreducible) (hsq : IsSubquotient σ B) : IrrGL.of σ hs hi = w := by
  classical
  have e := clsGL_of_pos hB hs hi hsq
  rw [h, Finsupp.single_apply] at e
  split_ifs at e with heq
  · exact heq.symm
  · exact absurd e (lt_irrefl 0)

/- English proof (translation)
Establish `h'` using `eq_of_heq (Sigma.mk.inj_iff.mp h).2`. Take `⟨e⟩` from `Quotient.exact h'`. Conclude with `IsSubquotient.of_injective e.toIntertwiningMap e.toLinearEquiv.injective`.
-/
private theorem isSubquotient_of_irrGL_of_eq {N : ℕ} {W₁ W₂ : Type} [AddCommGroup W₁] [Module ℂ W₁]
    [AddCommGroup W₂] [Module ℂ W₂] {σ₁ : Representation ℂ (GL (Fin N) k) W₁}
    {σ₂ : Representation ℂ (GL (Fin N) k) W₂} (hs₁ : IsSmooth σ₁) (hi₁ : σ₁.IsIrreducible)
    (hs₂ : IsSmooth σ₂) (hi₂ : σ₂.IsIrreducible) (h : IrrGL.of σ₁ hs₁ hi₁ = IrrGL.of σ₂ hs₂ hi₂) :
    IsSubquotient σ₁ σ₂ := by
  have h' := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  obtain ⟨e⟩ := Quotient.exact h'
  exact IsSubquotient.of_injective e.toIntertwiningMap e.toLinearEquiv.injective

/- English proof (translation)
Take `⟨r, hr1, hr2⟩` from `cls_apply_cl B hB (IrrRep.mk W σ hs hi)`. Establish `e : clsGL B hB (IrrGL.of σ hs hi) = 1`. Rewrite using `[h, irrGL_of_eq_of_cls_single hB h hs hi hsq, Finsupp.single_eq_same]`. Establish `e2` using `(clsGL_apply B hB (IrrRep.mk W σ hs hi).cl).symm.trans e`. Rewrite `e2` using `[hr2]`.

Establish `hr : r = 1` using `by exact_mod_cast e2`. Use `show jhMult (IrrRep.mk W σ hs hi).ρ B = 1`. Rewrite using `[hr1, hr]`. Both sides reduce to the same expression.
-/
private theorem jhMult_eq_one_of_cls_single {N : ℕ} {B : Representation ℂ (GL (Fin N) k) V}
    (hB : HasFiniteLength B) {w : IrrGL k} (h : clsGL B hB = Finsupp.single w 1)
    {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GL (Fin N) k) W}
    (hs : IsSmooth σ) (hi : σ.IsIrreducible) (hsq : IsSubquotient σ B) : jhMult σ B = 1 := by
  obtain ⟨r, hr1, hr2⟩ := cls_apply_cl B hB (IrrRep.mk W σ hs hi)
  have e : clsGL B hB (IrrGL.of σ hs hi) = 1 := by
    rw [h, irrGL_of_eq_of_cls_single hB h hs hi hsq, Finsupp.single_eq_same]
  have e2 := (clsGL_apply B hB (IrrRep.mk W σ hs hi).cl).symm.trans e
  rw [hr2] at e2
  have hr : r = 1 := by exact_mod_cast e2
  show jhMult (IrrRep.mk W σ hs hi).ρ B = 1
  rw [hr1, hr]
  rfl

/- English proof (translation)
Establish `hV : Nontrivial V`. Assume the negation of the conclusion as `hnt`. Rewrite `hnt` using `[not_nontrivial_iff_subsingleton]`. Establish `h0 : cls B hB = 0`. Use extensionality with `c`.

Rewrite using `[cls_apply, jhMult_of_subsingleton c.rep.irr]`. Both sides reduce to the same expression. Establish `h1 : clsGL B hB = 0` using `by simp [clsGL, h0]`. Rewrite `h1` using `[h]`. Conclude with `one_ne_zero (Finsupp.single_eq_zero.mp h1)`.

Establish `hbt : (⊥ : Subrepresentation B) ≠ ⊤`. Introduce `e`. Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Establish `hv' : v ∈ (⊤ : Subrepresentation B).toSubmodule` using `Submodule.mem_top`. Rewrite `hv'` using `[← e]`.

Conclude with `hv ((Submodule.mem_bot ℂ).mp hv')`. Use `{ exists_pair_ne := ⟨⊥, ⊤, hbt⟩, eq_bot_or_eq_top := fun S => ?_ }` and prove the remaining obligations. Assume the negation of the conclusion as `hS`. Use `push_neg at hS`. Take `⟨hS0, hS1⟩` from `hS`.

Establish `hn1 : Nontrivial S.toSubmodule` using `Submodule.nontrivial_iff_ne_bot.mpr (fun e => hS0 (Subrepresentation.toSubmodule_injective e))`. Establish `hn2 : Nontrivial (↥(⊤ : Subrepresentation B).toSubmodule ⧸ Submodule.comap (⊤ : Subrepresentation B).toSubmodule.subtype S.toSubmodule)`. Establish `hp : Submodule.comap (⊤ : Subrepresentation B).toSubmodule.subtype S.toSubmodule ≠ ⊤`. Introduce `e`. Rewrite `e` using `[Submodule.comap_subtype_eq_top]`.

Conclude with `hS1 (Subrepresentation.toSubmodule_injective (eq_top_iff.mpr e))`. Take `⟨x, -, hx⟩` from `SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hp)`. Conclude with `nontrivial_of_ne (Submodule.Quotient.mk x) 0 (by rwa [Ne, Submodule.Quotient.mk_eq_zero])`. Take `⟨Y₁, i₁, j₁, σ₁, hi₁, hq₁⟩` from `IrrSubquot.exists_irreducible_subquotient _ _ S.toRepresentation hn1`. Take `⟨Y₂, i₂, j₂, σ₂, hi₂, hq₂⟩` from `IrrSubquot.exists_irreducible_subquotient _ _ (subQuot ⊤ S) hn2`.

Establish `hsum` using `jhMult_sub_add_quot hi₁ S`. Establish `a₁ : jhMult σ₁ S.toRepresentation ≠ 0` using `jhMult_ne_zero_iff.mpr hq₁`. Establish `b₁ : IsSubquotient σ₁ B`. Apply `jhMult_ne_zero_iff.mp` to reduce the goal to its premises. Rewrite using `[hsum]`.

Conclude with `fun h0 => a₁ (add_eq_zero.mp h0).1`. Establish `b₂ : IsSubquotient σ₂ B`. Apply `jhMult_ne_zero_iff.mp` to reduce the goal to its premises. Rewrite using `[jhMult_sub_add_quot hi₂ S]`. Conclude with `fun h0 => (jhMult_ne_zero_iff.mpr hq₂) (add_eq_zero.mp h0).2`.

Establish `hs₁` using `IsSubquotient.isSmooth b₁ hsm`. Establish `hs₂` using `IsSubquotient.isSmooth b₂ hsm`. Establish `e₁` using `irrGL_of_eq_of_cls_single hB h hs₁ hi₁ b₁`. Establish `e₂` using `irrGL_of_eq_of_cls_single hB h hs₂ hi₂ b₂`. Establish `q₁₂ : IsSubquotient σ₁ σ₂` using `isSubquotient_of_irrGL_of_eq hs₁ hi₁ hs₂ hi₂ (e₁.trans e₂.symm)`.

Establish `c₁ : jhMult σ₁ (subQuot ⊤ S) ≠ 0` using `jhMult_ne_zero_iff.mpr (q₁₂.trans hq₂)`. Establish `one` using `jhMult_eq_one_of_cls_single hB h hs₁ hi₁ b₁`. Rewrite `one` using `[hsum]`. Establish `hle` using `add_le_add (ENat.one_le_iff_ne_zero.mpr a₁) (ENat.one_le_iff_ne_zero.mpr c₁)`. Rewrite `hle` using `[one]`.

Evaluate the numerical expressions using `at hle`.
-/
theorem isIrreducible_of_clsGL_eq_single {N : ℕ} {B : Representation ℂ (GL (Fin N) k) V}
    (hB : HasFiniteLength B) (hsm : IsSmooth B) {w : IrrGL k}
    (h : clsGL B hB = Finsupp.single w 1) : B.IsIrreducible := by
  classical
  have hV : Nontrivial V := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have h0 : cls B hB = 0 := by
      ext c
      rw [cls_apply, jhMult_of_subsingleton c.rep.irr]
      rfl
    have h1 : clsGL B hB = 0 := by simp [clsGL, h0]
    rw [h] at h1
    exact one_ne_zero (Finsupp.single_eq_zero.mp h1)
  have hbt : (⊥ : Subrepresentation B) ≠ ⊤ := by
    intro e
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hv' : v ∈ (⊤ : Subrepresentation B).toSubmodule := Submodule.mem_top
    rw [← e] at hv'
    exact hv ((Submodule.mem_bot ℂ).mp hv')
  refine { exists_pair_ne := ⟨⊥, ⊤, hbt⟩, eq_bot_or_eq_top := fun S => ?_ }
  by_contra hS
  push_neg at hS
  obtain ⟨hS0, hS1⟩ := hS
  have hn1 : Nontrivial S.toSubmodule :=
    Submodule.nontrivial_iff_ne_bot.mpr (fun e => hS0 (Subrepresentation.toSubmodule_injective e))
  have hn2 : Nontrivial (↥(⊤ : Subrepresentation B).toSubmodule ⧸
      Submodule.comap (⊤ : Subrepresentation B).toSubmodule.subtype S.toSubmodule) := by
    have hp : Submodule.comap (⊤ : Subrepresentation B).toSubmodule.subtype S.toSubmodule ≠ ⊤ := by
      intro e
      rw [Submodule.comap_subtype_eq_top] at e
      exact hS1 (Subrepresentation.toSubmodule_injective (eq_top_iff.mpr e))
    obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hp)
    exact nontrivial_of_ne (Submodule.Quotient.mk x) 0 (by rwa [Ne, Submodule.Quotient.mk_eq_zero])
  obtain ⟨Y₁, i₁, j₁, σ₁, hi₁, hq₁⟩ := IrrSubquot.exists_irreducible_subquotient _ _ S.toRepresentation hn1
  obtain ⟨Y₂, i₂, j₂, σ₂, hi₂, hq₂⟩ := IrrSubquot.exists_irreducible_subquotient _ _ (subQuot ⊤ S) hn2
  have hsum := jhMult_sub_add_quot hi₁ S
  have a₁ : jhMult σ₁ S.toRepresentation ≠ 0 := jhMult_ne_zero_iff.mpr hq₁
  have b₁ : IsSubquotient σ₁ B := by
    apply jhMult_ne_zero_iff.mp
    rw [hsum]
    exact fun h0 => a₁ (add_eq_zero.mp h0).1
  have b₂ : IsSubquotient σ₂ B := by
    apply jhMult_ne_zero_iff.mp
    rw [jhMult_sub_add_quot hi₂ S]
    exact fun h0 => (jhMult_ne_zero_iff.mpr hq₂) (add_eq_zero.mp h0).2
  have hs₁ := IsSubquotient.isSmooth b₁ hsm
  have hs₂ := IsSubquotient.isSmooth b₂ hsm
  have e₁ := irrGL_of_eq_of_cls_single hB h hs₁ hi₁ b₁
  have e₂ := irrGL_of_eq_of_cls_single hB h hs₂ hi₂ b₂
  have q₁₂ : IsSubquotient σ₁ σ₂ := isSubquotient_of_irrGL_of_eq hs₁ hi₁ hs₂ hi₂ (e₁.trans e₂.symm)
  have c₁ : jhMult σ₁ (subQuot ⊤ S) ≠ 0 := jhMult_ne_zero_iff.mpr (q₁₂.trans hq₂)
  have one := jhMult_eq_one_of_cls_single hB h hs₁ hi₁ b₁
  rw [hsum] at one
  have hle := add_le_add (ENat.one_le_iff_ne_zero.mpr a₁) (ENat.one_le_iff_ne_zero.mpr c₁)
  rw [one] at hle
  norm_num at hle

section Ring

open MvPolynomial

def msum (m : Segment k →₀ ℕ) : Multiset (IrrGL k) := ∑ Δ ∈ m.support, m Δ • Δ.ms

variable {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)}
  {Ψ : GrothGL k ≃+ MvPolynomial (Segment k) ℤ}

/- English proof (translation)
Use `hasSupport_of_monomial hS hΨ hX u.snd.rep.smooth u.snd.rep.irr m ?_` and prove the remaining obligations. Rewrite using `[IrrGL.of_rep]` and apply the resulting hypothesis.
-/
private theorem hasSupport_of_symm_monomial_ne_zero (hS : IsSegmentClass k Z) (hΨ : IsProductIso k Ψ)
    (hX : ∀ Δ, Ψ (Finsupp.single ⟨Δ.len * Δ.d, Z Δ⟩ 1) = MvPolynomial.X Δ)
    (u : IrrGL k) (m : Segment k →₀ ℕ) (h : (Ψ.symm (monomial m 1)) u ≠ 0) :
    HasSupport u.rep (msum m) := by
  refine hasSupport_of_monomial hS hΨ hX u.snd.rep.smooth u.snd.rep.irr m ?_
  rwa [IrrGL.of_rep]

/- English proof (translation)
Rewrite `h` using `[map_sum, Finsupp.finset_sum_apply]`. Take `⟨n, hn, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h`. Use `⟨n, hn, hasSupport_of_symm_monomial_ne_zero hS hΨ hX u n ?_⟩` and prove the remaining obligations. Introduce `h0`. Apply `hne` to reduce the goal to its premises.

Establish `e : monomial n (c n) = c n • monomial n (1 : ℤ)`. Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[e, map_zsmul, Finsupp.smul_apply, h0, smul_zero]`.
-/
private theorem exists_hasSupport_of_symm_sum_ne_zero (hS : IsSegmentClass k Z) (hΨ : IsProductIso k Ψ)
    (hX : ∀ Δ, Ψ (Finsupp.single ⟨Δ.len * Δ.d, Z Δ⟩ 1) = MvPolynomial.X Δ)
    (F : Finset (Segment k →₀ ℕ)) (c : (Segment k →₀ ℕ) → ℤ) (u : IrrGL k)
    (h : (Ψ.symm (∑ n ∈ F, monomial n (c n))) u ≠ 0) : ∃ n ∈ F, HasSupport u.rep (msum n) := by
  rw [map_sum, Finsupp.finset_sum_apply] at h
  obtain ⟨n, hn, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨n, hn, hasSupport_of_symm_monomial_ne_zero hS hΨ hX u n ?_⟩
  intro h0
  apply hne
  have e : monomial n (c n) = c n • monomial n (1 : ℤ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_zsmul, Finsupp.smul_apply, h0, smul_zero]

/- English proof (translation)
Use `set P := Ψ (Finsupp.single w 1) with hP`. Assume the negation of the conclusion as `hne`. Use `set S := P.support.filter (fun n => msum n ≠ s) with hSdef`. Use `set P1 := ∑ n ∈ S, monomial n (coeff n P) with hP1def`. Use `set P2 := ∑ n ∈ P.support.filter (fun n => ¬ msum n ≠ s), monomial n (coeff n P) with hP2def`.

Establish `hsplit : P1 + P2 = P`. Rewrite using `[hP1def, hP2def, hSdef, Finset.sum_filter_add_sum_filter_not]`. Conclude with `support_sum_monomial_coeff P`. Establish `hsum : Ψ.symm P1 + Ψ.symm P2 = Finsupp.single w 1`. Rewrite using `[← map_add, hsplit, hP, AddEquiv.symm_apply_apply]`.

Establish `hz : ∀ u, (Ψ.symm P1) u = 0`. Introduce `u`. Assume the negation of the conclusion as `hu`. Take `⟨n, hnS, hn⟩` from `exists_hasSupport_of_symm_sum_ne_zero hS hΨ hX S (fun n => coeff n P) u hu`. Establish `hnS'` using `(Finset.mem_filter.mp hnS).2`.

Distinguish the cases in `huw : u = w`. Substitute `huw` using the available equality. Conclude with `hnS' (TD.hasSupport_unique hG hBZ hn hw)`. Establish `h2 : (Ψ.symm P2) u ≠ 0`. Introduce `h2`.

Apply `hu` to reduce the goal to its premises. Establish `e` using `congrArg (fun f => f u) hsum`. Simplify using `only [Finsupp.add_apply, h2, add_zero, Finsupp.single_apply, if_neg (Ne.symm huw)] at e`. Conclude with `e`. Take `⟨n', hn'S, hn'⟩` from `exists_hasSupport_of_symm_sum_ne_zero hS hΨ hX _ (fun n => coeff n P) u h2`.

Establish `h3` using `(Finset.mem_filter.mp hn'S).2`. Conclude with `hnS' ((TD.hasSupport_unique hG hBZ hn hn').trans (not_not.mp h3))`. Establish `hP1 : P1 = 0`. Establish `e : Ψ.symm P1 = 0` using `Finsupp.ext hz`. Simplify using `using congrArg Ψ e`.

Establish `hmS : m ∈ S` using `Finset.mem_filter.mpr ⟨mem_support_iff.mpr hm, hne⟩`. Establish `hc : coeff m P1 = coeff m P`. Rewrite using `[hP1def, coeff_sum]`. Simplify using `only [coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq' S m (fun n => coeff n P), if_pos hmS]`.

Rewrite `hc` using `[hP1, coeff_zero]`. Conclude with `hm hc.symm`.
-/
theorem msum_eq_of_coeff_ne (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness)
    (hS : IsSegmentClass k Z) (hΨ : IsProductIso k Ψ)
    (hX : ∀ Δ, Ψ (Finsupp.single ⟨Δ.len * Δ.d, Z Δ⟩ 1) = MvPolynomial.X Δ)
    {w : IrrGL k} {s : Multiset (IrrGL k)} (hw : HasSupport w.rep s) {m : Segment k →₀ ℕ}
    (hm : coeff m (Ψ (Finsupp.single w 1)) ≠ 0) : msum m = s := by
  classical
  set P := Ψ (Finsupp.single w 1) with hP
  by_contra hne
  set S := P.support.filter (fun n => msum n ≠ s) with hSdef
  set P1 := ∑ n ∈ S, monomial n (coeff n P) with hP1def
  set P2 := ∑ n ∈ P.support.filter (fun n => ¬ msum n ≠ s), monomial n (coeff n P) with hP2def
  have hsplit : P1 + P2 = P := by
    rw [hP1def, hP2def, hSdef, Finset.sum_filter_add_sum_filter_not]
    exact support_sum_monomial_coeff P
  have hsum : Ψ.symm P1 + Ψ.symm P2 = Finsupp.single w 1 := by
    rw [← map_add, hsplit, hP, AddEquiv.symm_apply_apply]
  have hz : ∀ u, (Ψ.symm P1) u = 0 := by
    intro u
    by_contra hu
    obtain ⟨n, hnS, hn⟩ := exists_hasSupport_of_symm_sum_ne_zero hS hΨ hX S (fun n => coeff n P) u hu
    have hnS' := (Finset.mem_filter.mp hnS).2
    by_cases huw : u = w
    · subst huw
      exact hnS' (TD.hasSupport_unique hG hBZ hn hw)
    · have h2 : (Ψ.symm P2) u ≠ 0 := by
        intro h2
        apply hu
        have e := congrArg (fun f => f u) hsum
        simp only [Finsupp.add_apply, h2, add_zero, Finsupp.single_apply, if_neg (Ne.symm huw)] at e
        exact e
      obtain ⟨n', hn'S, hn'⟩ := exists_hasSupport_of_symm_sum_ne_zero hS hΨ hX _ (fun n => coeff n P) u h2
      have h3 := (Finset.mem_filter.mp hn'S).2
      exact hnS' ((TD.hasSupport_unique hG hBZ hn hn').trans (not_not.mp h3))
  have hP1 : P1 = 0 := by
    have e : Ψ.symm P1 = 0 := Finsupp.ext hz
    simpa using congrArg Ψ e
  have hmS : m ∈ S := Finset.mem_filter.mpr ⟨mem_support_iff.mpr hm, hne⟩
  have hc : coeff m P1 = coeff m P := by
    rw [hP1def, coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq' S m (fun n => coeff n P), if_pos hmS]
  rw [hP1, coeff_zero] at hc
  exact hm hc.symm

end Ring

section Monomials

open MvPolynomial GlobalTheory.SmGL.Segment

/- English proof (translation)
Establish `h1 : m Δ • Δ.ms ≤ msum m` using `Finset.single_le_sum (f := fun Γ => m Γ • Γ.ms) (fun _ _ => Multiset.zero_le _) h`. Take `⟨n, hn⟩` from `Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.mp h)`. Use `le_trans ?_ h1` and prove the remaining obligations. Rewrite using `[hn, succ_nsmul]`. Conclude with `le_add_self`.
-/
theorem ms_le_msum {m : Segment k →₀ ℕ} {Δ : Segment k} (h : Δ ∈ m.support) : Δ.ms ≤ msum m := by
  have h1 : m Δ • Δ.ms ≤ msum m :=
    Finset.single_le_sum (f := fun Γ => m Γ • Γ.ms) (fun _ _ => Multiset.zero_le _) h
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.mp h)
  refine le_trans ?_ h1
  rw [hn, succ_nsmul]
  exact le_add_self

/- English proof (translation)
The claim follows from `ext_first rfl h`.
-/
theorem eq_single_of_len {Δ : Segment k} (h : Δ.len = 1) : Δ = single Δ.first Δ.isCusp_first :=
  ext_first rfl h

/- English proof (translation)
Use `conv_lhs => rw [eq_single_of_len h]`. Rewrite using `[ms_single]`.
-/
theorem ms_of_len {Δ : Segment k} (h : Δ.len = 1) : Δ.ms = {Δ.first} := by
  conv_lhs => rw [eq_single_of_len h]
  rw [ms_single]

open scoped Classical in
/- English proof (translation)
Establish `hf : (single z hz).first = z` using `first_ofFirst z hz 1 (by norm_num)`. Establish `key : ∀ Δ ∈ m.support, (m Δ • Δ.ms).count z = if Δ = single z hz then m Δ else 0`. Introduce `Δ hΔ`. Rewrite using `[Multiset.count_nsmul, ms_of_len (hl Δ hΔ), Multiset.count_singleton]`. Distinguish the cases in `hE : Δ = single z hz`.

Substitute `hE` using the available equality. Simplify using `[hf]`. Establish `hne : z ≠ Δ.first`. Introduce `hzf`. Apply `hE` to reduce the goal to its premises.

Rewrite using `[eq_single_of_len (hl Δ hΔ)]`. Substitute `hzf` using the available equality. Both sides reduce to the same expression. Simplify using `[hE, hne]`. Rewrite using `[show msum m = ∑ Δ ∈ m.support, m Δ • Δ.ms from rfl, Multiset.count_sum', Finset.sum_congr rfl key, Finset.sum_ite_eq']`.

Use `split_ifs with h0`. Both sides reduce to the same expression. Conclude with `(Finsupp.notMem_support_iff.mp h0).symm`.
-/
theorem count_msum {m : Segment k →₀ ℕ} (hl : ∀ Δ ∈ m.support, Δ.len = 1) {z : IrrGL k}
    (hz : z.IsCusp) : (msum m).count z = m (single z hz) := by
  have hf : (single z hz).first = z := first_ofFirst z hz 1 (by norm_num)
  have key : ∀ Δ ∈ m.support, (m Δ • Δ.ms).count z = if Δ = single z hz then m Δ else 0 := by
    intro Δ hΔ
    rw [Multiset.count_nsmul, ms_of_len (hl Δ hΔ), Multiset.count_singleton]
    by_cases hE : Δ = single z hz
    · subst hE
      simp [hf]
    · have hne : z ≠ Δ.first := by
        intro hzf
        apply hE
        rw [eq_single_of_len (hl Δ hΔ)]
        subst hzf
        rfl
      simp [hE, hne]
  rw [show msum m = ∑ Δ ∈ m.support, m Δ • Δ.ms from rfl, Multiset.count_sum',
    Finset.sum_congr rfl key, Finset.sum_ite_eq']
  split_ifs with h0
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h0).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem msum_eq (m : Segment k →₀ ℕ) : msum m = m.sum fun Δ c => c • Δ.ms := rfl

/- English proof (translation)
Rewrite using `[msum_eq, msum_eq, msum_eq]`. Conclude with `Finsupp.sum_add_index' (fun _ => zero_nsmul _) (fun _ _ _ => add_nsmul _ _ _)`.
-/
theorem msum_add (a b : Segment k →₀ ℕ) : msum (a + b) = msum a + msum b := by
  rw [msum_eq, msum_eq, msum_eq]
  exact Finsupp.sum_add_index' (fun _ => zero_nsmul _) (fun _ _ _ => add_nsmul _ _ _)

/- English proof (translation)
Simplify using `[msum]`.
-/
theorem msum_single (Δ : Segment k) : msum (Finsupp.single Δ 1) = Δ.ms := by
  simp [msum]

variable {x y : IrrGL k}

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hΔ` using `ms_le_msum h`. Rewrite `hΔ` using `[hm]`. Establish `hcard : Multiset.card Δ.ms = Δ.len` using `by simp [Segment.ms]`. Establish `hle` using `Multiset.card_le_card hΔ`.

Rewrite `hle` using `[hcard]`. Simplify using `at hle`. Establish `h2 : Δ.len = 2` using `by have := Δ.len_pos; omega`. Establish `heq : Δ.ms = {x} + {y}` using `Multiset.eq_of_le_of_card_le hΔ (by rw [hcard, h2]; simp)`. Establish `hx : x ∈ Δ.ms` using `by rw [heq]; simp`.

Establish `hy : y ∈ Δ.ms` using `by rw [heq]; simp`. Take `⟨a, -, ha⟩` from `Multiset.mem_map.mp hx`. Take `⟨b, -, hb⟩` from `Multiset.mem_map.mp hy`. Establish `ha2 : (a : ℕ) < 2` using `h2 ▸ a.isLt`. Establish `hb2 : (b : ℕ) < 2` using `h2 ▸ b.isLt`.

Apply the tactic sequence `apply hl (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) (by rw [abs_le]; constructor <;> omega)`. Rewrite using `[← ha, ← hb]`. Simplify using `only [Segment.term, IrrGL.nu_nu]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem len_eq_one (hl : ∀ j : ℤ, |j| ≤ 1 → x ≠ y.nu (j : ℂ)) {m : Segment k →₀ ℕ}
    (hm : msum m = {x} + {y}) {Δ : Segment k} (h : Δ ∈ m.support) : Δ.len = 1 := by
  by_contra hne
  have hΔ := ms_le_msum h
  rw [hm] at hΔ
  have hcard : Multiset.card Δ.ms = Δ.len := by simp [Segment.ms]
  have hle := Multiset.card_le_card hΔ
  rw [hcard] at hle
  simp at hle
  have h2 : Δ.len = 2 := by have := Δ.len_pos; omega
  have heq : Δ.ms = {x} + {y} := Multiset.eq_of_le_of_card_le hΔ (by rw [hcard, h2]; simp)
  have hx : x ∈ Δ.ms := by rw [heq]; simp
  have hy : y ∈ Δ.ms := by rw [heq]; simp
  obtain ⟨a, -, ha⟩ := Multiset.mem_map.mp hx
  obtain ⟨b, -, hb⟩ := Multiset.mem_map.mp hy
  have ha2 : (a : ℕ) < 2 := h2 ▸ a.isLt
  have hb2 : (b : ℕ) < 2 := h2 ▸ b.isLt
  apply hl (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) (by rw [abs_le]; constructor <;> omega)
  rw [← ha, ← hb]
  simp only [Segment.term, IrrGL.nu_nu]
  congr 1
  push_cast
  ring

/- English proof (translation)
Establish `hL : ∀ Δ ∈ m.support, Δ.len = 1` using `fun Δ h => len_eq_one hl hm h`. Establish `hsl : ∀ (z : IrrGL k) (hz : z.IsCusp), (single z hz).len = 1` using `fun _ _ => rfl`. Establish `hsf : ∀ (z : IrrGL k) (hz : z.IsCusp), (single z hz).first = z` using `fun z hz => first_ofFirst z hz 1 (by norm_num)`. Use extensionality with `Γ`. Simplify using `only [Finsupp.add_apply, Finsupp.single_apply]`.

Distinguish the cases in `hΓ : Γ.len = 1`. Establish `e` using `eq_single_of_len hΓ`. Establish `hc` using `count_msum hL Γ.isCusp_first`. Rewrite `hc` using `[← e, hm, Multiset.count_add, Multiset.count_singleton, Multiset.count_singleton]`. Establish `ix : single x hx = Γ ↔ Γ.first = x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `hsf x hx`. Introduce `h'`. Rewrite using `[e]`.

Substitute `h'` using the available equality. Both sides reduce to the same expression. Establish `iy : single y hy = Γ ↔ Γ.first = y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`.

Conclude with `hsf y hy`. Introduce `h'`. Rewrite using `[e]`. Substitute `h'` using the available equality. Both sides reduce to the same expression.

Rewrite using `[← hc]`. Simplify using `only [ix, iy]`. Establish `h0 : m Γ = 0` using `Finsupp.notMem_support_iff.mp (fun h => hΓ (hL Γ h))`. Establish `nx : single x hx ≠ Γ` using `fun h => hΓ (h ▸ hsl x hx)`. Establish `ny : single y hy ≠ Γ` using `fun h => hΓ (h ▸ hsl y hy)`.

Simplify using `[h0, nx, ny]`.
-/
theorem eq_pair (hx : x.IsCusp) (hy : y.IsCusp) (hl : ∀ j : ℤ, |j| ≤ 1 → x ≠ y.nu (j : ℂ))
    {m : Segment k →₀ ℕ} (hm : msum m = {x} + {y}) :
    m = Finsupp.single (single x hx) 1 + Finsupp.single (single y hy) 1 := by
  have hL : ∀ Δ ∈ m.support, Δ.len = 1 := fun Δ h => len_eq_one hl hm h
  have hsl : ∀ (z : IrrGL k) (hz : z.IsCusp), (single z hz).len = 1 := fun _ _ => rfl
  have hsf : ∀ (z : IrrGL k) (hz : z.IsCusp), (single z hz).first = z :=
    fun z hz => first_ofFirst z hz 1 (by norm_num)
  classical
  ext Γ
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  by_cases hΓ : Γ.len = 1
  · have e := eq_single_of_len hΓ
    have hc := count_msum hL Γ.isCusp_first
    rw [← e, hm, Multiset.count_add, Multiset.count_singleton, Multiset.count_singleton] at hc
    have ix : single x hx = Γ ↔ Γ.first = x := by
      constructor
      · rintro rfl
        exact hsf x hx
      · intro h'
        rw [e]
        subst h'
        rfl
    have iy : single y hy = Γ ↔ Γ.first = y := by
      constructor
      · rintro rfl
        exact hsf y hy
      · intro h'
        rw [e]
        subst h'
        rfl
    rw [← hc]
    simp only [ix, iy]
  · have h0 : m Γ = 0 := Finsupp.notMem_support_iff.mp (fun h => hΓ (hL Γ h))
    have nx : single x hx ≠ Γ := fun h => hΓ (h ▸ hsl x hx)
    have ny : single y hy ≠ Γ := fun h => hΓ (h ▸ hsl y hy)
    simp [h0, nx, ny]

end Monomials

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Establish `hx` using `hasFiniteLength_of_isIrreducible x.snd.rep.irr`. Establish `hy` using `hasFiniteLength_of_isIrreducible y.snd.rep.irr`. Take `⟨h, e⟩` from `hΨ.2 x.fst y.fst _ _ x.rep y.rep hx hy x.snd.rep.smooth y.snd.rep.smooth`. Conclude with `⟨h, by rw [e, bas_eq x hx, bas_eq y hy]⟩`.
-/
theorem prod₂_cls {A : Type 1} [CommRing A] {Ψ : GrothGL k ≃+ A} (hΨ : IsProductIso k Ψ) (x y : IrrGL k) :
    ∃ h : HasFiniteLength (prod₂ x.rep y.rep), Ψ (clsGL (prod₂ x.rep y.rep) h) = bas Ψ x * bas Ψ y := by
  have hx := hasFiniteLength_of_isIrreducible x.snd.rep.irr
  have hy := hasFiniteLength_of_isIrreducible y.snd.rep.irr
  obtain ⟨h, e⟩ := hΨ.2 x.fst y.fst _ _ x.rep y.rep hx hy x.snd.rep.smooth y.snd.rep.smooth
  exact ⟨h, by rw [e, bas_eq x hx, bas_eq y hy]⟩

section Main

open MvPolynomial

variable {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)}
  {Ψ : GrothGL k ≃+ MvPolynomial (Segment k) ℤ}

/- English proof (translation)
Take `⟨h1, h2⟩` from `pos_X hS hΨ hX (Segment.single z hz)`. Rewrite `h2` using `[Segment.ms_single]`. Establish `hpc : pc Ψ {z} = bas Ψ z` using `by simp [pc]`. Rewrite `h2` using `[hpc]`. Establish `hb : Ψ.symm (bas Ψ z) = Finsupp.single z 1` using `by simp [bas]`.

Use `set Q := Ψ.symm (X (Segment.single z hz)) with hQ`. Establish `hpos : ∀ u, 0 ≤ Q u` using `fun u => h1 u`. Establish `hle : ∀ u, Q u ≤ (Finsupp.single z 1 : GrothGL k) u`. Introduce `u`. Establish `e` using `h2 u`.

Rewrite `e` using `[map_sub, hb, Finsupp.sub_apply]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hQne : Q ≠ 0`. Introduce `h0`. Establish `e` using `Ψ.apply_symm_apply (X (Segment.single z hz))`.

Rewrite `e` using `[← hQ, h0, map_zero]`. Conclude with `X_ne_zero _ e.symm`. Establish `hoff : ∀ u, u ≠ z → Q u = 0`. Introduce `u hu`. Use `le_antisymm ?_ (hpos u)` and prove the remaining obligations.

Establish `e` using `hle u`. Rewrite `e` using `[Finsupp.single_apply, if_neg (Ne.symm hu)]`. Then use the resulting hypothesis. Establish `hz1 : Q z = 1`. Establish `a` using `hle z`. Establish `b` using `hpos z`.

Rewrite `a` using `[Finsupp.single_eq_same]`. Break down `(show Q z = 0 ∨ Q z = 1 by omega) with h | h` into its components or cases. It suffices to derive a contradiction. Apply `hQne` to reduce the goal to its premises. Use extensionality with `u`.

Distinguish the cases in `hu : u = z`. Substitute `hu` using the available equality. Simplify using `using h`. Simplify using `using hoff u hu`. Conclude with `h`.

Establish `hQ1 : Q = Finsupp.single z 1`. Use extensionality with `u`. Distinguish the cases in `hu : u = z`. Substitute `hu` using the available equality. Simplify using `using hz1`.

Rewrite using `[hoff u hu, Finsupp.single_apply, if_neg (Ne.symm hu)]`. Apply `Ψ.symm.injective` to reduce the goal to its premises. Rewrite using `[hb, ← hQ1]`.
-/
theorem bas_eq_X (hS : IsSegmentClass k Z) (hΨ : IsProductIso k Ψ)
    (hX : ∀ Δ, Ψ (Finsupp.single ⟨Δ.len * Δ.d, Z Δ⟩ 1) = MvPolynomial.X Δ)
    (z : IrrGL k) (hz : z.IsCusp) : bas Ψ z = X (Segment.single z hz) := by
  classical
  obtain ⟨h1, h2⟩ := pos_X hS hΨ hX (Segment.single z hz)
  rw [Segment.ms_single] at h2
  have hpc : pc Ψ {z} = bas Ψ z := by simp [pc]
  rw [hpc] at h2
  have hb : Ψ.symm (bas Ψ z) = Finsupp.single z 1 := by simp [bas]
  set Q := Ψ.symm (X (Segment.single z hz)) with hQ
  have hpos : ∀ u, 0 ≤ Q u := fun u => h1 u
  have hle : ∀ u, Q u ≤ (Finsupp.single z 1 : GrothGL k) u := by
    intro u
    have e := h2 u
    rw [map_sub, hb, Finsupp.sub_apply] at e
    linarith
  have hQne : Q ≠ 0 := by
    intro h0
    have e := Ψ.apply_symm_apply (X (Segment.single z hz))
    rw [← hQ, h0, map_zero] at e
    exact X_ne_zero _ e.symm
  have hoff : ∀ u, u ≠ z → Q u = 0 := by
    intro u hu
    refine le_antisymm ?_ (hpos u)
    have e := hle u
    rwa [Finsupp.single_apply, if_neg (Ne.symm hu)] at e
  have hz1 : Q z = 1 := by
    have a := hle z
    have b := hpos z
    rw [Finsupp.single_eq_same] at a
    rcases (show Q z = 0 ∨ Q z = 1 by omega) with h | h
    · exfalso
      apply hQne
      ext u
      by_cases hu : u = z
      · subst hu
        simpa using h
      · simpa using hoff u hu
    · exact h
  have hQ1 : Q = Finsupp.single z 1 := by
    ext u
    by_cases hu : u = z
    · subst hu
      simpa using hz1
    · rw [hoff u hu, Finsupp.single_apply, if_neg (Ne.symm hu)]
  apply Ψ.symm.injective
  rw [hb, ← hQ1]

/- English proof (translation)
Use `⟨coeff (Finsupp.single (Segment.single x hx) 1 + Finsupp.single (Segment.single y hy) 1) (Ψ (Finsupp.single w 1)), ?_⟩` and prove the remaining obligations. Use extensionality with `n`. Rewrite using `[coeff_monomial]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Both sides reduce to the same expression. Assume the negation of the conclusion as `hne`. Conclude with `h (eq_pair hx hy hl (msum_eq_of_coeff_ne hG hBZ hS hΨ hX hw hne)).symm`.
-/
theorem eq_monomial_of_hasSupport (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness)
    (hS : IsSegmentClass k Z) (hΨ : IsProductIso k Ψ)
    (hX : ∀ Δ, Ψ (Finsupp.single ⟨Δ.len * Δ.d, Z Δ⟩ 1) = MvPolynomial.X Δ)
    {x y w : IrrGL k} (hx : x.IsCusp) (hy : y.IsCusp) (hl : ∀ j : ℤ, |j| ≤ 1 → x ≠ y.nu (j : ℂ))
    (hw : HasSupport w.rep ({x} + {y})) :
    ∃ c : ℤ, Ψ (Finsupp.single w 1) =
      monomial (Finsupp.single (Segment.single x hx) 1 + Finsupp.single (Segment.single y hy) 1) c := by
  classical
  refine ⟨coeff (Finsupp.single (Segment.single x hx) 1 + Finsupp.single (Segment.single y hy) 1)
    (Ψ (Finsupp.single w 1)), ?_⟩
  ext n
  rw [coeff_monomial]
  split_ifs with h
  · subst h
    rfl
  · by_contra hne
    exact h (eq_pair hx hy hl (msum_eq_of_coeff_ne hG hBZ hS hΨ hX hw hne)).symm

/- English proof (translation)
Use `set m0 := Finsupp.single (Segment.single x hx) 1 + Finsupp.single (Segment.single y hy) 1 with hm0`. Establish `hmon : Ψ (clsGL B hB) = monomial m0 1`. Rewrite using `[eB, bas_eq_X hS hΨ hX x hx, bas_eq_X hS hΨ hX y hy, X, X, monomial_mul, one_mul]`. Use `set C := clsGL B hB with hCdef`. Establish `hC0 : C ≠ 0`.

Introduce `h`. Rewrite `hmon` using `[h, map_zero]`. Conclude with `one_ne_zero (monomial_eq_zero.mp hmon.symm)`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : ∃ w : IrrGL k, C w ≠ 0 := by`. Assume the negation of the conclusion as `hh`.

Use `push_neg at hh`. Conclude with `hC0 (Finsupp.ext hh)`. Establish `hms : msum m0 = {x} + {y}`. Rewrite using `[hm0, msum_add, msum_single, msum_single, Segment.ms_single, Segment.ms_single]`. Establish `hsupp : HasSupport w.rep ({x} + {y})`.

Rewrite using `[← hms]`. Use `hasSupport_of_symm_monomial_ne_zero hS hΨ hX w m0 ?_` and prove the remaining obligations. Rewrite using `[← hmon, AddEquiv.symm_apply_apply]`. Conclude with `hw`. Take `⟨c, hc⟩` from `eq_monomial_of_hasSupport hG hBZ hS hΨ hX hx hy hl hsupp`.

Establish `hsw : Finsupp.single w 1 = c • C`. Apply `Ψ.injective` to reduce the goal to its premises. Rewrite using `[hc, map_zsmul, hmon, smul_monomial, smul_eq_mul, mul_one]`. Establish `hw1 : c * C w = 1`. Establish `e` using `congrArg (fun f => f w) hsw`.

Simplify using `only [Finsupp.single_eq_same, Finsupp.smul_apply, smul_eq_mul] at e`. Conclude with `e.symm`. Establish `hCw : 0 ≤ C w` using `clsGL_nonneg B hB w`. Establish `hc1 : c = 1`. Break down `Int.eq_one_or_neg_one_of_mul_eq_one' hw1 with h | h` into its components or cases.

Conclude with `h.1`. Use linear arithmetic over natural numbers and integers. Establish `hCeq : C = Finsupp.single w 1`. Rewrite using `[hsw, hc1, one_smul]`. Conclude with `isIrreducible_of_clsGL_eq_single hB hsm hCeq`.
-/
theorem isIrreducible_of_cls_eq_mul (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness)
    (hS : IsSegmentClass k Z) (hΨ : IsProductIso k Ψ)
    (hX : ∀ Δ, Ψ (Finsupp.single ⟨Δ.len * Δ.d, Z Δ⟩ 1) = MvPolynomial.X Δ)
    {x y : IrrGL k} (hx : x.IsCusp) (hy : y.IsCusp) (hl : ∀ j : ℤ, |j| ≤ 1 → x ≠ y.nu (j : ℂ))
    {N : ℕ} {B : Representation ℂ (GL (Fin N) k) V} (hB : HasFiniteLength B) (hsm : IsSmooth B)
    (eB : Ψ (clsGL B hB) = bas Ψ x * bas Ψ y) : B.IsIrreducible := by
  classical
  set m0 := Finsupp.single (Segment.single x hx) 1 + Finsupp.single (Segment.single y hy) 1 with hm0
  have hmon : Ψ (clsGL B hB) = monomial m0 1 := by
    rw [eB, bas_eq_X hS hΨ hX x hx, bas_eq_X hS hΨ hX y hy, X, X, monomial_mul, one_mul]
  set C := clsGL B hB with hCdef
  have hC0 : C ≠ 0 := by
    intro h
    rw [h, map_zero] at hmon
    exact one_ne_zero (monomial_eq_zero.mp hmon.symm)
  obtain ⟨w, hw⟩ : ∃ w : IrrGL k, C w ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hC0 (Finsupp.ext hh)
  have hms : msum m0 = {x} + {y} := by
    rw [hm0, msum_add, msum_single, msum_single, Segment.ms_single, Segment.ms_single]
  have hsupp : HasSupport w.rep ({x} + {y}) := by
    rw [← hms]
    refine hasSupport_of_symm_monomial_ne_zero hS hΨ hX w m0 ?_
    rw [← hmon, AddEquiv.symm_apply_apply]
    exact hw
  obtain ⟨c, hc⟩ := eq_monomial_of_hasSupport hG hBZ hS hΨ hX hx hy hl hsupp
  have hsw : Finsupp.single w 1 = c • C := by
    apply Ψ.injective
    rw [hc, map_zsmul, hmon, smul_monomial, smul_eq_mul, mul_one]
  have hw1 : c * C w = 1 := by
    have e := congrArg (fun f => f w) hsw
    simp only [Finsupp.single_eq_same, Finsupp.smul_apply, smul_eq_mul] at e
    exact e.symm
  have hCw : 0 ≤ C w := clsGL_nonneg B hB w
  have hc1 : c = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hw1 with h | h
    · exact h.1
    · omega
  have hCeq : C = Finsupp.single w 1 := by
    rw [hsw, hc1, one_smul]
  exact isIrreducible_of_clsGL_eq_single hB hsm hCeq

end Main

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Take `⟨Z, Ψ, hS, hΨ, hX⟩` from `hZ k`. Take `⟨hB, eB⟩` from `prod₂_cls hΨ x y`. Conclude with `isIrreducible_of_cls_eq_mul hG hBZ hS hΨ hX hx hy hl hB (isSmooth_prod₂ _ _) eB`.
-/
theorem isIrreducible_prod₂_of_polynomialRing (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness)
    (hZ : ZelevinskyPolynomialRing) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (x y : IrrGL k) (hx : x.IsCusp) (hy : y.IsCusp)
    (hl : ∀ j : ℤ, |j| ≤ 1 → x ≠ y.nu (j : ℂ)) : (prod₂ x.rep y.rep).IsIrreducible := by
  obtain ⟨Z, Ψ, hS, hΨ, hX⟩ := hZ k
  obtain ⟨hB, eB⟩ := prod₂_cls hΨ x y
  exact isIrreducible_of_cls_eq_mul hG hBZ hS hΨ hX hx hy hl hB (isSmooth_prod₂ _ _) eB

end GlobalTheory.CompanionTheory.Hypotheses₂.RankOne
