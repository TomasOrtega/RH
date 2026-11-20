import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames

open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace LevelTowerAlt

/- English proof (translation)
Use `haveI : NoZeroSMulDivisors R (M ⧸ N) := by`. Use `⟨fun {c} {q} hcq => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective N q`. Distinguish the cases in `hc : c = 0`. Conclude with `Or.inl hc`.

Use `right`. Rewrite `hcq` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `(Submodule.Quotient.mk_eq_zero N).2 (hs x c hc hcq)`. Use `haveI : Module.Free R (M ⧸ N) := Module.free_of_finite_type_torsion_free'`. Use `haveI : Module.Finite R N := Module.Finite.of_injective N.subtype Subtype.val_injective`.

Use `haveI : Module.Free R N := Module.free_of_finite_type_torsion_free'`. Take `⟨g, hg⟩` from `Module.projective_lifting_property N.mkQ (LinearMap.id) (Submodule.mkQ_surjective N)`. Establish `hq : ∀ x : M, x - g (N.mkQ x) ∈ N`. Introduce `x`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.mkQ_apply]`.

Use `LinearMap.congr_fun hg (Submodule.Quotient.mk x)` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply, Submodule.mkQ_apply] at this`. Rewrite using `[this, sub_self]`. Set `p : M →ₗ[R] N` to `LinearMap.codRestrict N (LinearMap.id - g ∘ₗ N.mkQ) (fun x => by simpa using hq x)`. Establish `hp : ∀ x (hx : x ∈ N), p x = ⟨x, hx⟩`.

Introduce `x hx`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[p, (Submodule.Quotient.mk_eq_zero N).2 hx]`. Set `e` to `Module.finBasis R N`. Use `⟨Module.finrank R N, fun b => (e b : M), fun b => e.coord b ∘ₗ p, fun b => (e b).2, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Establish `h2` using `congrArg Subtype.val (e.sum_repr ⟨x, hx⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h2`. Simplify using `only [LinearMap.comp_apply, hp x hx, Module.Basis.coord_apply]`. Conclude with `h2.symm`.

Introduce `a b`. Simplify using `only [LinearMap.comp_apply, hp _ (e b).2, Subtype.coe_eta, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`.
-/
theorem exists_retraction {R M : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Free R M] (N : Submodule R M)
    (hs : ∀ (x : M) (n : R), n ≠ 0 → n • x ∈ N → x ∈ N) :
    ∃ (k : ℕ) (i : Fin k → M) (φ : Fin k → M →ₗ[R] R), (∀ b, i b ∈ N) ∧ (∀ x ∈ N, x = ∑ b, φ b x • i b) ∧
      ∀ a b, φ a (i b) = if b = a then 1 else 0 := by
  classical
  haveI : NoZeroSMulDivisors R (M ⧸ N) := by
    refine ⟨fun {c} {q} hcq => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hcq
      exact (Submodule.Quotient.mk_eq_zero N).2 (hs x c hc hcq)
  haveI : Module.Free R (M ⧸ N) := Module.free_of_finite_type_torsion_free'
  haveI : Module.Finite R N := Module.Finite.of_injective N.subtype Subtype.val_injective
  haveI : Module.Free R N := Module.free_of_finite_type_torsion_free'
  obtain ⟨g, hg⟩ := Module.projective_lifting_property N.mkQ (LinearMap.id) (Submodule.mkQ_surjective N)
  have hq : ∀ x : M, x - g (N.mkQ x) ∈ N := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.mkQ_apply]
    have := LinearMap.congr_fun hg (Submodule.Quotient.mk x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Submodule.mkQ_apply] at this
    rw [this, sub_self]
  let p : M →ₗ[R] N := LinearMap.codRestrict N (LinearMap.id - g ∘ₗ N.mkQ) (fun x => by simpa using hq x)
  have hp : ∀ x (hx : x ∈ N), p x = ⟨x, hx⟩ := by
    intro x hx
    apply Subtype.ext
    simp [p, (Submodule.Quotient.mk_eq_zero N).2 hx]
  let e := Module.finBasis R N
  refine ⟨Module.finrank R N, fun b => (e b : M), fun b => e.coord b ∘ₗ p, fun b => (e b).2, ?_, ?_⟩
  · intro x hx
    have h2 := congrArg Subtype.val (e.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    simp only [LinearMap.comp_apply, hp x hx, Module.Basis.coord_apply]
    exact h2.symm
  · intro a b
    simp only [LinearMap.comp_apply, hp _ (e b).2, Subtype.coe_eta, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply]

/- English proof (translation)
Establish `h1` using `Submodule.finrank_quotient_add_finrank (LinearMap.ker h)`. Rewrite `h1` using `[(h.quotKerEquivOfSurjective hh).finrank_eq, ← he, LinearMap.finrank_range_of_inj hf]`. Conclude with `h1`.
-/
theorem rank_exact {R A B C : Type} [CommRing R] [IsDomain R] [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [AddCommGroup C] [Module R C] [Module.Finite R B] (f : A →ₗ[R] B) (h : B →ₗ[R] C)
    (hf : Function.Injective f) (hh : Function.Surjective h) (he : LinearMap.range f = LinearMap.ker h) :
    Module.finrank R C + Module.finrank R A = Module.finrank R B := by
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker h)
  rw [(h.quotKerEquivOfSurjective hh).finrank_eq, ← he, LinearMap.finrank_range_of_inj hf] at h1
  exact h1

variable {O Λ : Type} [CommRing O] [AddCommGroup Λ] [Module O Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  {form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ} {I : Submodule O Λ}

/- English proof (translation)
Establish `anti : ∀ x y, form x y = -form y x`. Introduce `x y`. Establish `h` using `halt (x + y)`. Simplify using `only [map_add, LinearMap.add_apply, halt x, halt y, zero_add, add_zero] at h`. Use linear arithmetic over natural numbers and integers.

Take `⟨k, i, φ, hiI, hsum, hφ⟩` from `exists_retraction (R := ℤ) (M := Λ) (I.restrictScalars ℤ) (fun x n hn hx => hsat x n hn hx)`. Establish `hiI' : ∀ b, i b ∈ I` using `hiI`. Establish `hsum' : ∀ x ∈ I, x = ∑ b, φ b x • i b` using `fun x hx => hsum x hx`. Use `choose f hf using fun b => hb.2 (φ b)`. Establish `hfi : ∀ a b, form (f a) (i b) = if b = a then 1 else 0`.

Introduce `a b`. Rewrite using `[hf, hφ]`. Establish `hif : ∀ a b, form (i b) (f a) = -(if b = a then 1 else 0)`. Introduce `a b`. Rewrite using `[anti, hfi]`.

Establish `hImem : ∀ c : Fin k → ℤ, ∑ b, c b • i b ∈ I` using `fun c => I.sum_mem fun b _ => Submodule.smul_of_tower_mem I (c b) (hiI' b)`. Establish `hsumI_f : ∀ (c : Fin k → ℤ) a, form (∑ b, c b • i b) (f a) = -c a`. Introduce `c a`. Simplify using `[hif]`. Establish `hsumf_i : ∀ (c : Fin k → ℤ) b, form (∑ a, c a • f a) (i b) = c b`.

Introduce `c b`. Simplify using `[hfi]`. Establish `hperp : ∀ x, (∀ b, form x (i b) = 0) → ∀ y ∈ I, form x y = 0`. Introduce `x hx y hy`. Rewrite using `[hsum' y hy]`.

Simplify using `[hx]`. Set `r : Λ →ₗ[ℤ] Λ` to `LinearMap.id + ∑ b, LinearMap.toSpanSingleton ℤ Λ (i b) ∘ₗ form.flip (f b)`. Establish `hr_apply : ∀ x, r x = x + ∑ b, form x (f b) • i b`. Introduce `x`. Simplify using `[r]`.

Establish `hrI : ∀ x, r x - x ∈ I`. Introduce `x`. Rewrite using `[hr_apply, add_sub_cancel_left]`. Conclude with `hImem _`. Establish `hr_kill : ∀ x ∈ I, r x = 0`.

Introduce `x hx`. Establish `h1 : ∀ b, form x (f b) = -φ b x`. Introduce `b`. Rewrite using `[anti, hf]`. Rewrite using `[hr_apply]`.

Simplify using `only [h1, neg_smul, Finset.sum_neg_distrib]`. Rewrite using `[← hsum' x hx, add_neg_cancel]`. Establish `hr_f : ∀ x a, form (r x) (f a) = 0`. Introduce `x a`. Establish `h2` using `hsumI_f (fun b => form x (f b)) a`.

Rewrite using `[hr_apply, map_add, LinearMap.add_apply, h2]`. Use linear arithmetic over natural numbers and integers. Establish `hr_perp : ∀ x, (∀ y ∈ I, form x y = 0) → ∀ y ∈ I, form (r x) y = 0`. Introduce `x hx y hy`. Establish `e : r x = x + (r x - x)` using `by abel`.

Rewrite using `[e, map_add, LinearMap.add_apply, hx y hy, hiso _ (hrI x) y hy, add_zero]`. Set `ιZ : M →ₗ[ℤ] Λ` to `ι.restrictScalars ℤ`. Set `πZ : M →ₗ[ℤ] Λ'` to `π.restrictScalars ℤ`. Establish `hπZ : Function.Surjective πZ` using `hπ`. Establish `hker : LinearMap.ker πZ ≤ LinearMap.ker (r ∘ₗ ιZ)`.

Introduce `m hm`. Rewrite `hm`, the goal using `[LinearMap.mem_ker]`. Conclude with `hr_kill _ ((hk m).1 hm)`. Set `s : Λ' →ₗ[ℤ] Λ` to `(LinearMap.ker πZ).liftQ (r ∘ₗ ιZ) hker ∘ₗ (πZ.quotKerEquivOfSurjective hπZ).symm.toLinearMap`. Establish `hs_apply : ∀ m, s (π m) = r (ι m)`.

Introduce `m`. Establish `e : (πZ.quotKerEquivOfSurjective hπZ).symm (π m) = Submodule.Quotient.mk m`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Simplify using `only [s, LinearMap.comp_apply, LinearEquiv.coe_coe, e, Submodule.liftQ_apply]`.

Both sides reduce to the same expression. Establish `hs_perp : ∀ z, ∀ y ∈ I, form (s z) y = 0`. Introduce `z`. Take `⟨m, rfl⟩` from `hπ z`. Rewrite using `[hs_apply]`.

Conclude with `hr_perp _ ((hr _).2 ⟨m, rfl⟩)`. Establish `hs_f : ∀ z a, form (s z) (f a) = 0`. Introduce `z a`. Take `⟨m, rfl⟩` from `hπ z`. Rewrite using `[hs_apply]`.

Conclude with `hr_f _ a`. Establish `hs_sect : ∀ x, (∀ y ∈ I, form x y = 0) → ∃ z, s z - x ∈ I`. Introduce `x hx`. Take `⟨m, hm⟩` from `(hr x).1 hx`. Conclude with `⟨π m, by rw [hs_apply, hm]; exact hrI x⟩`.

Establish `hs_inj : Function.Injective s`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`. Take `⟨m, rfl⟩` from `hπ z`. Rewrite `hz` using `[hs_apply]`.

Establish `h1` using `hrI (ι m)`. Rewrite `h1` using `[hz, zero_sub, neg_mem_iff]`. Conclude with `(hk m).2 h1`. Establish `hs_Olin : ∀ (a : O) z, s (a • z) - a • s z ∈ I`. Introduce `a z`.

Take `⟨m, rfl⟩` from `hπ z`. Rewrite using `[show a • π m = π (a • m) from (map_smul π a m).symm, hs_apply, hs_apply, map_smul]`. Establish `e : r (a • ι m) - a • r (ι m) = (r (a • ι m) - a • ι m) - a • (r (ι m) - ι m)`. Rewrite using `[smul_sub]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Conclude with `I.sub_mem (hrI _) (I.smul_mem a (hrI _))`. Use `haveI : Module.Finite ℤ Λ' := Module.Finite.of_injective s hs_inj`. Use `haveI : Module.IsTorsionFree ℤ Λ' := ⟨fun n hn x y hxy => by`. Express the relevant statement in the definitionally equal form `n • x = n • y at hxy`.

Apply `hs_inj` to reduce the goal to its premises. Apply `Module.IsTorsionFree.isSMulRegular (M := Λ) hn` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `n • s x = n • s y`. Rewrite using `[← map_smul, ← map_smul, hxy]⟩`. Use `haveI : Module.Free ℤ Λ' := Module.free_of_finite_type_torsion_free'`.

Establish `hdecomp : ∀ x, ∃ w, ∃ y ∈ I, ∃ c : Fin k → ℤ, x = s w + y + ∑ a, c a • f a`. Introduce `x`. Establish `hp : ∀ y ∈ I, form (x - ∑ a, form x (i a) • f a) y = 0`. Apply `hperp` to reduce the goal to its premises. Introduce `b`.

Establish `h2` using `hsumf_i (fun a => form x (i a)) b`. Rewrite using `[map_sub, LinearMap.sub_apply, h2, sub_self]`. Take `⟨w, hw⟩` from `hs_sect _ hp`. Use `⟨w, (x - ∑ a, form x (i a) • f a) - s w, ?_, fun a => form x (i a), ?_⟩` and prove the remaining obligations. Establish `h3` using `I.neg_mem hw`.

Rewrite `h3` using `[neg_sub]`. Then use the resulting hypothesis. Normalize the expressions using the abelian group laws. Use `⟨k, i, s, ?_, hiI', fun x hx => ⟨fun b => φ b x, hsum' x hx⟩, inferInstance, inferInstance, ?_, hs_perp, hs_sect, hs_Olin, ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg b`.

Establish `h4` using `congrArg (φ b) hg`. Simplify `h4` using `[hφ]`. Set `F : Λ' × (Fin k → ℤ) →ₗ[ℤ] Λ` to `s ∘ₗ LinearMap.fst ℤ Λ' (Fin k → ℤ) + (∑ b, LinearMap.toSpanSingleton ℤ Λ (i b) ∘ₗ LinearMap.proj b) ∘ₗ LinearMap.snd ℤ Λ' (Fin k → ℤ)`. Establish `hF : ∀ z c, F (z, c) = s z + ∑ b, c b • i b`. Introduce `z c`.

Simplify using `[F]`. Set `H : Λ →ₗ[ℤ] (Fin k → ℤ)` to `LinearMap.pi fun b => form.flip (i b)`. Establish `hH : ∀ x b, H x b = form x (i b)` using `fun x b => rfl`. Establish `hFinj : Function.Injective F`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce and unpack `⟨z, c⟩ h0`. Rewrite `h0` using `[hF]`. Establish `hc : c = 0`. Use function extensionality and compare the values at `a`. Establish `h5` using `congrArg (fun x => form x (f a)) h0`.

Simplify using `only [map_add, LinearMap.add_apply, hs_f, hsumI_f, map_zero, LinearMap.zero_apply] at h5`. Simplify using `using h5`. Substitute `hc` using the available equality. Simplify using `at h0`. Conclude with `Prod.ext (hs_inj (h0.trans (map_zero s).symm)) rfl`.

Establish `hHsurj : Function.Surjective H`. Introduce `c`. Use `⟨∑ a, c a • f a, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `b`. Rewrite using `[hH]`.

Conclude with `hsumf_i c b`. Establish `hex : LinearMap.range F = LinearMap.ker H`. Use extensionality with `x`. Simplify using `only [LinearMap.mem_range, LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨z, c⟩, rfl⟩`. Use function extensionality and compare the values at `b`. Rewrite using `[hH, hF, map_add, LinearMap.add_apply, hs_perp z _ (hiI' b), hiso _ (hImem c) _ (hiI' b)]`. Simplify using the standard rewrite rules. Introduce `hx`.

Establish `hx' : ∀ y ∈ I, form x y = 0` using `hperp x (fun b => by`. Establish `h9` using `congrFun hx b`. Rewrite `h9` using `[hH]`. Simplify using `using h9)`. Take `⟨z, hz⟩` from `hs_sect x hx'`.

Use `⟨(z, fun b => -φ b (s z - x)), ?_⟩` and prove the remaining obligations. Rewrite using `[hF]`. Simplify using `only [neg_smul, Finset.sum_neg_distrib]`. Rewrite using `[← hsum' _ hz]`. Normalize the expressions using the abelian group laws.

Establish `h6` using `rank_exact F H hFinj hHsurj hex`. Rewrite `h6` using `[Module.finrank_prod, Module.finrank_fin_fun]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`.

Apply `hs_inj` to reduce the goal to its premises. Rewrite using `[map_zero]`. Apply `hb.1` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Take `⟨w, y, hy, c, rfl⟩` from `hdecomp x`. Establish `hw` using `LinearMap.congr_fun hz w`. Simplify using `only [LinearMap.compl₁₂_apply, LinearMap.zero_apply] at hw`. Simplify using `[map_add, hw, hs_perp z y hy, hs_f]`. Introduce `ψ`.

Set `P : Λ →ₗ[ℤ] Λ` to `LinearMap.id - ∑ a, LinearMap.toSpanSingleton ℤ Λ (f a) ∘ₗ form.flip (i a)`. Establish `hP : ∀ x, P x = x - ∑ a, form x (i a) • f a`. Introduce `x`. Simplify using `[P]`. Establish `hPr : ∀ x, P x ∈ LinearMap.range ιZ`.

Introduce `x`. Take `⟨m, hm⟩` from `(hr (P x)).1 (hperp _ fun b => by`. Establish `h2` using `hsumf_i (fun a => form x (i a)) b`. Rewrite using `[hP, map_sub, LinearMap.sub_apply, h2, sub_self])`. Conclude with `⟨m, hm⟩`.

Set `E` to `LinearEquiv.ofInjective ιZ hι`. Set `t : Λ →ₗ[ℤ] Λ'` to `πZ ∘ₗ E.symm.toLinearMap ∘ₗ LinearMap.codRestrict (LinearMap.range ιZ) P hPr`. Establish `ht0 : ∀ m, t (ι m) = π m`. Introduce `m`. Establish `hPi : P (ι m) = ι m`.

Rewrite using `[hP]`. Simplify using `[(hr (ι m)).2 ⟨m, rfl⟩ _ (hiI' _)]`. Establish `h7 : E.symm (LinearMap.codRestrict (LinearMap.range ιZ) P hPr (ι m)) = m`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[LinearMap.codRestrict_apply, hPi]`. Both sides reduce to the same expression. Use `show πZ (E.symm (LinearMap.codRestrict (LinearMap.range ιZ) P hPr (ι m))) = π m`. Rewrite using `[h7]`. Both sides reduce to the same expression.

Establish `ht : ∀ w, t (s w) = w`. Introduce `w`. Take `⟨m, rfl⟩` from `hπ w`. Take `⟨m2, hm2⟩` from `(hr (r (ι m))).1 (hr_perp _ ((hr _).2 ⟨m, rfl⟩))`. Rewrite using `[hs_apply, ← hm2, ht0, ← sub_eq_zero, ← map_sub, hk, map_sub, hm2]`.

Conclude with `hrI _`. Take `⟨x0, hx0⟩` from `hb.2 (ψ ∘ₗ t)`. Establish `hx1p : ∀ y ∈ I, form (x0 - ∑ a, form x0 (i a) • f a) y = 0` using `hperp _ fun b => by`. Establish `h2` using `hsumf_i (fun a => form x0 (i a)) b`. Rewrite using `[map_sub, LinearMap.sub_apply, h2, sub_self]`.

Take `⟨z, hz⟩` from `hs_sect _ hx1p`. Use `⟨z, LinearMap.ext fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.compl₁₂_apply]`. Establish `e1 : form (s z) (s w) = form (x0 - ∑ a, form x0 (i a) • f a) (s w) + form (s z - (x0 - ∑ a, form x0 (i a) • f a)) (s w)`. Rewrite using `[map_sub (form) (s z), LinearMap.sub_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : form (s z - (x0 - ∑ a, form x0 (i a) • f a)) (s w) = 0`. Rewrite using `[anti, hs_perp w _ hz, neg_zero]`. Establish `e3 : form (x0 - ∑ a, form x0 (i a) • f a) (s w) = form x0 (s w)`. Establish `h8 : ∀ a, form (f a) (s w) = 0` using `fun a => by rw [anti, hs_f, neg_zero]`.

Simplify using `[h8]`. Rewrite using `[e1, e2, e3, hx0, LinearMap.comp_apply, ht, add_zero]`.
-/
theorem commGroup_mul_mul_eq_mul_inv_mul_mul_mul (hb : Function.Bijective form) (halt : ∀ x, form x x = 0) (hsat : IsSaturated I)
    (hiso : IsIsoSub form I) {M Λ' : Type} [AddCommGroup M] [Module O M] [AddCommGroup Λ'] [Module O Λ']
    (ι : M →ₗ[O] Λ) (π : M →ₗ[O] Λ') (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hr : ∀ x, (∀ y ∈ I, form x y = 0) ↔ ∃ m, ι m = x) (hk : ∀ m, π m = 0 ↔ ι m ∈ I) :
    ∃ (k : ℕ) (i : Fin k → Λ) (s : Λ' →ₗ[ℤ] Λ), LinearIndependent ℤ i ∧ (∀ b, i b ∈ I) ∧
      (∀ x ∈ I, ∃ c : Fin k → ℤ, x = ∑ b, c b • i b) ∧ Module.Free ℤ Λ' ∧ Module.Finite ℤ Λ' ∧
      Module.finrank ℤ Λ' + 2 * k = Module.finrank ℤ Λ ∧ (∀ z, ∀ y ∈ I, form (s z) y = 0) ∧
      (∀ x, (∀ y ∈ I, form x y = 0) → ∃ z, s z - x ∈ I) ∧ (∀ (a : O) z, s (a • z) - a • s z ∈ I) ∧
      Function.Bijective (form.compl₁₂ s s) := by
  classical
  have anti : ∀ x y, form x y = -form y x := by
    intro x y
    have h := halt (x + y)
    simp only [map_add, LinearMap.add_apply, halt x, halt y, zero_add, add_zero] at h
    omega
  obtain ⟨k, i, φ, hiI, hsum, hφ⟩ := exists_retraction (R := ℤ) (M := Λ) (I.restrictScalars ℤ)
    (fun x n hn hx => hsat x n hn hx)
  have hiI' : ∀ b, i b ∈ I := hiI
  have hsum' : ∀ x ∈ I, x = ∑ b, φ b x • i b := fun x hx => hsum x hx
  choose f hf using fun b => hb.2 (φ b)
  have hfi : ∀ a b, form (f a) (i b) = if b = a then 1 else 0 := by
    intro a b
    rw [hf, hφ]
  have hif : ∀ a b, form (i b) (f a) = -(if b = a then 1 else 0) := by
    intro a b
    rw [anti, hfi]
  have hImem : ∀ c : Fin k → ℤ, ∑ b, c b • i b ∈ I := fun c =>
    I.sum_mem fun b _ => Submodule.smul_of_tower_mem I (c b) (hiI' b)
  have hsumI_f : ∀ (c : Fin k → ℤ) a, form (∑ b, c b • i b) (f a) = -c a := by
    intro c a
    simp [hif]
  have hsumf_i : ∀ (c : Fin k → ℤ) b, form (∑ a, c a • f a) (i b) = c b := by
    intro c b
    simp [hfi]
  have hperp : ∀ x, (∀ b, form x (i b) = 0) → ∀ y ∈ I, form x y = 0 := by
    intro x hx y hy
    rw [hsum' y hy]
    simp [hx]
  let r : Λ →ₗ[ℤ] Λ := LinearMap.id + ∑ b, LinearMap.toSpanSingleton ℤ Λ (i b) ∘ₗ form.flip (f b)
  have hr_apply : ∀ x, r x = x + ∑ b, form x (f b) • i b := by
    intro x
    simp [r]
  have hrI : ∀ x, r x - x ∈ I := by
    intro x
    rw [hr_apply, add_sub_cancel_left]
    exact hImem _
  have hr_kill : ∀ x ∈ I, r x = 0 := by
    intro x hx
    have h1 : ∀ b, form x (f b) = -φ b x := by
      intro b
      rw [anti, hf]
    rw [hr_apply]
    simp only [h1, neg_smul, Finset.sum_neg_distrib]
    rw [← hsum' x hx, add_neg_cancel]
  have hr_f : ∀ x a, form (r x) (f a) = 0 := by
    intro x a
    have h2 := hsumI_f (fun b => form x (f b)) a
    rw [hr_apply, map_add, LinearMap.add_apply, h2]
    omega
  have hr_perp : ∀ x, (∀ y ∈ I, form x y = 0) → ∀ y ∈ I, form (r x) y = 0 := by
    intro x hx y hy
    have e : r x = x + (r x - x) := by abel
    rw [e, map_add, LinearMap.add_apply, hx y hy, hiso _ (hrI x) y hy, add_zero]
  let ιZ : M →ₗ[ℤ] Λ := ι.restrictScalars ℤ
  let πZ : M →ₗ[ℤ] Λ' := π.restrictScalars ℤ
  have hπZ : Function.Surjective πZ := hπ
  have hker : LinearMap.ker πZ ≤ LinearMap.ker (r ∘ₗ ιZ) := by
    intro m hm
    rw [LinearMap.mem_ker] at hm ⊢
    exact hr_kill _ ((hk m).1 hm)
  let s : Λ' →ₗ[ℤ] Λ :=
    (LinearMap.ker πZ).liftQ (r ∘ₗ ιZ) hker ∘ₗ (πZ.quotKerEquivOfSurjective hπZ).symm.toLinearMap
  have hs_apply : ∀ m, s (π m) = r (ι m) := by
    intro m
    have e : (πZ.quotKerEquivOfSurjective hπZ).symm (π m) = Submodule.Quotient.mk m := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [s, LinearMap.comp_apply, LinearEquiv.coe_coe, e, Submodule.liftQ_apply]
    rfl
  have hs_perp : ∀ z, ∀ y ∈ I, form (s z) y = 0 := by
    intro z
    obtain ⟨m, rfl⟩ := hπ z
    rw [hs_apply]
    exact hr_perp _ ((hr _).2 ⟨m, rfl⟩)
  have hs_f : ∀ z a, form (s z) (f a) = 0 := by
    intro z a
    obtain ⟨m, rfl⟩ := hπ z
    rw [hs_apply]
    exact hr_f _ a
  have hs_sect : ∀ x, (∀ y ∈ I, form x y = 0) → ∃ z, s z - x ∈ I := by
    intro x hx
    obtain ⟨m, hm⟩ := (hr x).1 hx
    exact ⟨π m, by rw [hs_apply, hm]; exact hrI x⟩
  have hs_inj : Function.Injective s := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨m, rfl⟩ := hπ z
    rw [hs_apply] at hz
    have h1 := hrI (ι m)
    rw [hz, zero_sub, neg_mem_iff] at h1
    exact (hk m).2 h1
  have hs_Olin : ∀ (a : O) z, s (a • z) - a • s z ∈ I := by
    intro a z
    obtain ⟨m, rfl⟩ := hπ z
    rw [show a • π m = π (a • m) from (map_smul π a m).symm, hs_apply, hs_apply, map_smul]
    have e : r (a • ι m) - a • r (ι m) = (r (a • ι m) - a • ι m) - a • (r (ι m) - ι m) := by
      rw [smul_sub]
      abel
    rw [e]
    exact I.sub_mem (hrI _) (I.smul_mem a (hrI _))
  haveI : Module.Finite ℤ Λ' := Module.Finite.of_injective s hs_inj
  haveI : Module.IsTorsionFree ℤ Λ' := ⟨fun n hn x y hxy => by
    change n • x = n • y at hxy
    apply hs_inj
    apply Module.IsTorsionFree.isSMulRegular (M := Λ) hn
    change n • s x = n • s y
    rw [← map_smul, ← map_smul, hxy]⟩
  haveI : Module.Free ℤ Λ' := Module.free_of_finite_type_torsion_free'
  have hdecomp : ∀ x, ∃ w, ∃ y ∈ I, ∃ c : Fin k → ℤ, x = s w + y + ∑ a, c a • f a := by
    intro x
    have hp : ∀ y ∈ I, form (x - ∑ a, form x (i a) • f a) y = 0 := by
      apply hperp
      intro b
      have h2 := hsumf_i (fun a => form x (i a)) b
      rw [map_sub, LinearMap.sub_apply, h2, sub_self]
    obtain ⟨w, hw⟩ := hs_sect _ hp
    refine ⟨w, (x - ∑ a, form x (i a) • f a) - s w, ?_, fun a => form x (i a), ?_⟩
    · have h3 := I.neg_mem hw
      rwa [neg_sub] at h3
    · abel
  refine ⟨k, i, s, ?_, hiI', fun x hx => ⟨fun b => φ b x, hsum' x hx⟩, inferInstance, inferInstance, ?_,
    hs_perp, hs_sect, hs_Olin, ⟨?_, ?_⟩⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg b
    have h4 := congrArg (φ b) hg
    simpa [hφ] using h4
  · let F : Λ' × (Fin k → ℤ) →ₗ[ℤ] Λ := s ∘ₗ LinearMap.fst ℤ Λ' (Fin k → ℤ) +
      (∑ b, LinearMap.toSpanSingleton ℤ Λ (i b) ∘ₗ LinearMap.proj b) ∘ₗ LinearMap.snd ℤ Λ' (Fin k → ℤ)
    have hF : ∀ z c, F (z, c) = s z + ∑ b, c b • i b := by
      intro z c
      simp [F]
    let H : Λ →ₗ[ℤ] (Fin k → ℤ) := LinearMap.pi fun b => form.flip (i b)
    have hH : ∀ x b, H x b = form x (i b) := fun x b => rfl
    have hFinj : Function.Injective F := by
      rw [injective_iff_map_eq_zero]
      rintro ⟨z, c⟩ h0
      rw [hF] at h0
      have hc : c = 0 := by
        funext a
        have h5 := congrArg (fun x => form x (f a)) h0
        simp only [map_add, LinearMap.add_apply, hs_f, hsumI_f, map_zero, LinearMap.zero_apply] at h5
        simpa using h5
      subst hc
      simp at h0
      exact Prod.ext (hs_inj (h0.trans (map_zero s).symm)) rfl
    have hHsurj : Function.Surjective H := by
      intro c
      refine ⟨∑ a, c a • f a, ?_⟩
      funext b
      rw [hH]
      exact hsumf_i c b
    have hex : LinearMap.range F = LinearMap.ker H := by
      ext x
      simp only [LinearMap.mem_range, LinearMap.mem_ker]
      constructor
      · rintro ⟨⟨z, c⟩, rfl⟩
        funext b
        rw [hH, hF, map_add, LinearMap.add_apply, hs_perp z _ (hiI' b), hiso _ (hImem c) _ (hiI' b)]
        simp
      · intro hx
        have hx' : ∀ y ∈ I, form x y = 0 := hperp x (fun b => by
          have h9 := congrFun hx b
          rw [hH] at h9
          simpa using h9)
        obtain ⟨z, hz⟩ := hs_sect x hx'
        refine ⟨(z, fun b => -φ b (s z - x)), ?_⟩
        rw [hF]
        simp only [neg_smul, Finset.sum_neg_distrib]
        rw [← hsum' _ hz]
        abel
    have h6 := rank_exact F H hFinj hHsurj hex
    rw [Module.finrank_prod, Module.finrank_fin_fun] at h6
    omega
  · rw [injective_iff_map_eq_zero]
    intro z hz
    apply hs_inj
    rw [map_zero]
    apply hb.1
    rw [map_zero]
    refine LinearMap.ext fun x => ?_
    obtain ⟨w, y, hy, c, rfl⟩ := hdecomp x
    have hw := LinearMap.congr_fun hz w
    simp only [LinearMap.compl₁₂_apply, LinearMap.zero_apply] at hw
    simp [map_add, hw, hs_perp z y hy, hs_f]
  · intro ψ
    let P : Λ →ₗ[ℤ] Λ := LinearMap.id - ∑ a, LinearMap.toSpanSingleton ℤ Λ (f a) ∘ₗ form.flip (i a)
    have hP : ∀ x, P x = x - ∑ a, form x (i a) • f a := by
      intro x
      simp [P]
    have hPr : ∀ x, P x ∈ LinearMap.range ιZ := by
      intro x
      obtain ⟨m, hm⟩ := (hr (P x)).1 (hperp _ fun b => by
        have h2 := hsumf_i (fun a => form x (i a)) b
        rw [hP, map_sub, LinearMap.sub_apply, h2, sub_self])
      exact ⟨m, hm⟩
    let E := LinearEquiv.ofInjective ιZ hι
    let t : Λ →ₗ[ℤ] Λ' := πZ ∘ₗ E.symm.toLinearMap ∘ₗ LinearMap.codRestrict (LinearMap.range ιZ) P hPr
    have ht0 : ∀ m, t (ι m) = π m := by
      intro m
      have hPi : P (ι m) = ι m := by
        rw [hP]
        simp [(hr (ι m)).2 ⟨m, rfl⟩ _ (hiI' _)]
      have h7 : E.symm (LinearMap.codRestrict (LinearMap.range ιZ) P hPr (ι m)) = m := by
        rw [LinearEquiv.symm_apply_eq]
        apply Subtype.ext
        rw [LinearMap.codRestrict_apply, hPi]
        rfl
      show πZ (E.symm (LinearMap.codRestrict (LinearMap.range ιZ) P hPr (ι m))) = π m
      rw [h7]
      rfl
    have ht : ∀ w, t (s w) = w := by
      intro w
      obtain ⟨m, rfl⟩ := hπ w
      obtain ⟨m2, hm2⟩ := (hr (r (ι m))).1 (hr_perp _ ((hr _).2 ⟨m, rfl⟩))
      rw [hs_apply, ← hm2, ht0, ← sub_eq_zero, ← map_sub, hk, map_sub, hm2]
      exact hrI _
    obtain ⟨x0, hx0⟩ := hb.2 (ψ ∘ₗ t)
    have hx1p : ∀ y ∈ I, form (x0 - ∑ a, form x0 (i a) • f a) y = 0 := hperp _ fun b => by
      have h2 := hsumf_i (fun a => form x0 (i a)) b
      rw [map_sub, LinearMap.sub_apply, h2, sub_self]
    obtain ⟨z, hz⟩ := hs_sect _ hx1p
    refine ⟨z, LinearMap.ext fun w => ?_⟩
    rw [LinearMap.compl₁₂_apply]
    have e1 : form (s z) (s w) = form (x0 - ∑ a, form x0 (i a) • f a) (s w) +
        form (s z - (x0 - ∑ a, form x0 (i a) • f a)) (s w) := by
      rw [map_sub (form) (s z), LinearMap.sub_apply]
      ring
    have e2 : form (s z - (x0 - ∑ a, form x0 (i a) • f a)) (s w) = 0 := by
      rw [anti, hs_perp w _ hz, neg_zero]
    have e3 : form (x0 - ∑ a, form x0 (i a) • f a) (s w) = form x0 (s w) := by
      have h8 : ∀ a, form (f a) (s w) = 0 := fun a => by rw [anti, hs_f, neg_zero]
      simp [h8]
    rw [e1, e2, e3, hx0, LinearMap.comp_apply, ht, add_zero]

/- English proof (translation)
Set `P : Submodule O Λ` to `{ carrier := {x | ∀ y ∈ I, form x y = 0} add_mem' := by`. Introduce `x z hx hz y hy`. Simplify using `only [Set.mem_setOf_eq, map_add, LinearMap.add_apply, hx y hy, hz y hy, add_zero]`. Use the proof step `zero_mem' := by`. Introduce `y _`.

Simplify using the standard rewrite rules. Use the proof step `smul_mem' := by`. Introduce `a x hx y hy`. Take `⟨a', ha'⟩` from `hadj a`. Use `show form (a • x) y = 0`.

Rewrite using `[ha']`. Conclude with `hx _ (I.smul_mem a' hy) }`. Take `⟨k, i, s, h⟩` from `commGroup_mul_mul_eq_mul_inv_mul_mul_mul hb halt hsat hiso (M := P) (Λ' := P ⧸ I.comap P.subtype) P.subtype (Submodule.mkQ _) Subtype.val_injective (Submodule.mkQ_surjective _) (fun x => ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨m, hm⟩ => hm ▸ m.2⟩) (fun m => by rw [Submodule.mkQ_apply, Su …`. Conclude with `⟨P ⧸ I.comap P.subtype, inferInstance, inferInstance, k, i, s, h⟩`.
-/
theorem exists_quot (hb : Function.Bijective form) (halt : ∀ x, form x x = 0) (hsat : IsSaturated I)
    (hiso : IsIsoSub form I) (hadj : ∀ a : O, ∃ a' : O, ∀ x y, form (a • x) y = form x (a' • y)) :
    ∃ (Λ' : Type) (_ : AddCommGroup Λ') (_ : Module O Λ') (k : ℕ) (i : Fin k → Λ) (s : Λ' →ₗ[ℤ] Λ),
      LinearIndependent ℤ i ∧ (∀ b, i b ∈ I) ∧
      (∀ x ∈ I, ∃ c : Fin k → ℤ, x = ∑ b, c b • i b) ∧ Module.Free ℤ Λ' ∧ Module.Finite ℤ Λ' ∧
      Module.finrank ℤ Λ' + 2 * k = Module.finrank ℤ Λ ∧ (∀ z, ∀ y ∈ I, form (s z) y = 0) ∧
      (∀ x, (∀ y ∈ I, form x y = 0) → ∃ z, s z - x ∈ I) ∧ (∀ (a : O) z, s (a • z) - a • s z ∈ I) ∧
      Function.Bijective (form.compl₁₂ s s) := by
  let P : Submodule O Λ :=
    { carrier := {x | ∀ y ∈ I, form x y = 0}
      add_mem' := by
        intro x z hx hz y hy
        simp only [Set.mem_setOf_eq, map_add, LinearMap.add_apply, hx y hy, hz y hy, add_zero]
      zero_mem' := by
        intro y _
        simp
      smul_mem' := by
        intro a x hx y hy
        obtain ⟨a', ha'⟩ := hadj a
        show form (a • x) y = 0
        rw [ha']
        exact hx _ (I.smul_mem a' hy) }
  obtain ⟨k, i, s, h⟩ := commGroup_mul_mul_eq_mul_inv_mul_mul_mul hb halt hsat hiso (M := P) (Λ' := P ⧸ I.comap P.subtype) P.subtype
    (Submodule.mkQ _) Subtype.val_injective (Submodule.mkQ_surjective _)
    (fun x => ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨m, hm⟩ => hm ▸ m.2⟩)
    (fun m => by rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap])
  exact ⟨P ⧸ I.comap P.subtype, inferInstance, inferInstance, k, i, s, h⟩

end LevelTowerAlt
