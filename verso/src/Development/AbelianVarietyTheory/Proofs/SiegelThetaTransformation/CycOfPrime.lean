import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement

open scoped TensorProduct LinearAlgebra.Projectivization

namespace GlobalTheory.SW.Hyper

variable {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]

/- English proof (translation)
Set `g : O →ₗ[O] M ⧸ N` to `LinearMap.toSpanSingleton O (M ⧸ N) (N.mkQ v)`. Establish `hker : LinearMap.ker g = P`. Use extensionality with `r`. Simplify using `only [LinearMap.mem_ker, g, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply]`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hr`. Take `⟨y, i, hi, hyi⟩` from `hP.exists_inv hr`. Apply `hv` to reduce the goal to its premises.

Establish `hv' : v = y • (r • v) + i • v` using `by rw [smul_smul, ← add_smul, hyi, one_smul]`. Rewrite using `[hv']`. Conclude with `N.add_mem (N.smul_mem y h) (hPv i hi)`. Conclude with `hPv r`. Establish `hs : Function.Surjective g`.

Introduce `z`. Take `⟨x, rfl⟩` from `Submodule.mkQ_surjective N z`. Take `⟨r, hr⟩` from `hc x`. Use `⟨r, ?_⟩` and prove the remaining obligations. Simplify using `only [g, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply]`.

Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← neg_sub]`. Conclude with `N.neg_mem hr`. Set `e : (O ⧸ P) ≃ₗ[O] M ⧸ N` to `(Submodule.quotEquivOfEq _ _ hker.symm).trans (g.quotKerEquivOfSurjective hs)`. Use `⟨e.symm.toLinearMap ∘ₗ N.mkQ, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`.

Apply `hv` to reduce the goal to its premises. Establish `h1 : (e.symm.toLinearMap ∘ₗ N.mkQ) v = 0` using `by rw [h0]; rfl`. Simplify `h1` using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Rewrite using `[LinearEquiv.ker_comp, Submodule.ker_mkQ]`.
-/
theorem exists_fun (P : Ideal O) [hP : P.IsMaximal] (N : Submodule O M) (v : M) (hv : v ∉ N)
    (hPv : ∀ c ∈ P, c • v ∈ N) (hc : ∀ x, ∃ r : O, x - r • v ∈ N) :
    ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N := by
  classical
  let g : O →ₗ[O] M ⧸ N := LinearMap.toSpanSingleton O (M ⧸ N) (N.mkQ v)
  have hker : LinearMap.ker g = P := by
    ext r
    simp only [LinearMap.mem_ker, g, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro h
      by_contra hr
      obtain ⟨y, i, hi, hyi⟩ := hP.exists_inv hr
      apply hv
      have hv' : v = y • (r • v) + i • v := by rw [smul_smul, ← add_smul, hyi, one_smul]
      rw [hv']
      exact N.add_mem (N.smul_mem y h) (hPv i hi)
    · exact hPv r
  have hs : Function.Surjective g := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N z
    obtain ⟨r, hr⟩ := hc x
    refine ⟨r, ?_⟩
    simp only [g, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← neg_sub]
    exact N.neg_mem hr
  let e : (O ⧸ P) ≃ₗ[O] M ⧸ N :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (g.quotKerEquivOfSurjective hs)
  refine ⟨e.symm.toLinearMap ∘ₗ N.mkQ, ?_, ?_⟩
  · intro h0
    apply hv
    have h1 : (e.symm.toLinearMap ∘ₗ N.mkQ) v = 0 := by rw [h0]; rfl
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using h1
  · rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : ∃ w, f w ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hf (LinearMap.ext fun x => by simpa using h x)`. Take `⟨b, hb⟩` from `Ideal.Quotient.exists_inv hw`.

Take `⟨c, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Use `⟨c • w, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_comm, hb]`.
-/
theorem surj_of_ne (P : Ideal O) [hP : P.IsMaximal] (f : M →ₗ[O] O ⧸ P) (hf : f ≠ 0) :
    ∃ v, f v = 1 := by
  obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (LinearMap.ext fun x => by simpa using h x)
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv hw
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨c • w, ?_⟩
  rw [map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_comm, hb]

/- English proof (translation)
Take `⟨v, hv⟩` from `surj_of_ne P f hf`. Establish `hs : Function.Surjective f`. Introduce `y`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Use `⟨r • v, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul, hv, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]`. Establish `h` using `AddSubgroup.index_ker f.toAddMonoidHom`. Rewrite `h` using `[AddMonoidHom.range_eq_top.mpr hs, AddSubgroup.card_top]`. Conclude with `h`.
-/
theorem index_ker (P : Ideal O) [hP : P.IsMaximal] (f : M →ₗ[O] O ⧸ P) (hf : f ≠ 0) :
    (LinearMap.ker f).toAddSubgroup.index = Nat.card (O ⧸ P) := by
  obtain ⟨v, hv⟩ := surj_of_ne P f hf
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨r • v, ?_⟩
    rw [map_smul, hv, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
  have h := AddSubgroup.index_ker f.toAddMonoidHom
  rw [AddMonoidHom.range_eq_top.mpr hs, AddSubgroup.card_top] at h
  exact h

/- English proof (translation)
Establish `: Fact q.Prime` using `⟨hq⟩`. Establish `hcard : Nat.card (M ⧸ N.toAddSubgroup) = q`. Rewrite using `[← AddSubgroup.index_eq_card]`. Conclude with `h`. Establish `hne : N.toAddSubgroup ≠ ⊤`.

Introduce `ht`. Rewrite `h` using `[ht, AddSubgroup.index_top]`. Conclude with `hq.one_lt.ne h`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, v ∉ N := by`. Assume the negation of the conclusion as `hn`.

Use `push Not at hn`. Conclude with `hne (eq_top_iff.mpr fun x _ => hn x)`. Use `⟨v, hv, fun x => ?_⟩` and prove the remaining obligations. Establish `hv0 : (QuotientAddGroup.mk v : M ⧸ N.toAddSubgroup) ≠ 0`. Rewrite using `[Ne, QuotientAddGroup.eq_zero_iff]`.

Conclude with `hv`. Establish `hx : (QuotientAddGroup.mk x : M ⧸ N.toAddSubgroup) ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk v)` using `mem_zmultiples_of_prime_card hcard hv0`. Take `⟨n, hn⟩` from `AddSubgroup.mem_zmultiples_iff.mp hx`. Use `⟨(n : O), ?_⟩` and prove the remaining obligations. Rewrite using `[Int.cast_smul_eq_zsmul]`.

Establish `h2 : (QuotientAddGroup.mk (n • v) : M ⧸ N.toAddSubgroup) = QuotientAddGroup.mk x`. Rewrite using `[QuotientAddGroup.mk_zsmul]`. Conclude with `hn`. Rewrite `h2` using `[QuotientAddGroup.eq]`. Rewrite using `[sub_eq_neg_add]`.

Conclude with `h2`.
-/
theorem cyc_of_prime (N : Submodule O M) {q : ℕ} (hq : q.Prime)
    (h : N.toAddSubgroup.index = q) : ∃ v, v ∉ N ∧ ∀ x, ∃ r : O, x - r • v ∈ N := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hcard : Nat.card (M ⧸ N.toAddSubgroup) = q := by
    rw [← AddSubgroup.index_eq_card]; exact h
  have hne : N.toAddSubgroup ≠ ⊤ := by
    intro ht
    rw [ht, AddSubgroup.index_top] at h
    exact hq.one_lt.ne h
  obtain ⟨v, hv⟩ : ∃ v, v ∉ N := by
    by_contra hn
    push Not at hn
    exact hne (eq_top_iff.mpr fun x _ => hn x)
  refine ⟨v, hv, fun x => ?_⟩
  have hv0 : (QuotientAddGroup.mk v : M ⧸ N.toAddSubgroup) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]; exact hv
  have hx : (QuotientAddGroup.mk x : M ⧸ N.toAddSubgroup) ∈
      AddSubgroup.zmultiples (QuotientAddGroup.mk v) := mem_zmultiples_of_prime_card hcard hv0
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  refine ⟨(n : O), ?_⟩
  rw [Int.cast_smul_eq_zsmul]
  have h2 : (QuotientAddGroup.mk (n • v) : M ⧸ N.toAddSubgroup) = QuotientAddGroup.mk x := by
    rw [QuotientAddGroup.mk_zsmul]; exact hn
  rw [QuotientAddGroup.eq] at h2
  rw [sub_eq_neg_add]
  exact h2

/- English proof (translation)
Establish `: Module.FinitePresentation O M` using `Module.finitePresentation_of_projective O M`. Establish `hlc` using `Module.isLocallyConstant_rankAtStalk (R := O) (M := M)`. Set `q0 : PrimeSpectrum k` to `⟨⊥, Ideal.isPrime_bot⟩`. Set `p0 : PrimeSpectrum O` to `⟨⊥, Ideal.isPrime_bot⟩`. Establish `h1 : Module.finrank k (k ⊗[O] M) = Module.rankAtStalk (R` using `k) (k ⊗[O] M) q0 := by`.

Rewrite using `[Module.rankAtStalk_eq_finrank_of_free]`. Both sides reduce to the same expression. Establish `hp : p0.asIdeal.primeCompl ≤ nonZeroDivisors O`. Introduce `x hx`. Establish `hx0 : x ≠ 0` using `fun h0 => hx (h0 ▸ Ideal.zero_mem _)`.

Conclude with `mem_nonZeroDivisors_of_ne_zero hx0`. Establish `h2 : Module.rankAtStalk (R` using `O) M p0 = Module.finrank O M := by`. Rewrite using `[Module.rankAtStalk, IsLocalization.finrank_eq (Localization.AtPrime p0.asIdeal) p0.asIdeal.primeCompl hp, IsLocalizedModule.finrank_eq p0.asIdeal.primeCompl (LocalizedModule.mkLinearMap p0.asIdeal.primeCompl M) hp]`. Rewrite using `[h1, Module.rankAtStalk_baseChange, hlc.apply_eq_of_preconnectedSpace _ p0, h2]`.
-/
theorem finrank_fibre (O M k : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [Algebra O k] :
    Module.finrank k (k ⊗[O] M) = Module.finrank O M := by
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  have hlc := Module.isLocallyConstant_rankAtStalk (R := O) (M := M)
  let q0 : PrimeSpectrum k := ⟨⊥, Ideal.isPrime_bot⟩
  let p0 : PrimeSpectrum O := ⟨⊥, Ideal.isPrime_bot⟩
  have h1 : Module.finrank k (k ⊗[O] M) = Module.rankAtStalk (R := k) (k ⊗[O] M) q0 := by
    rw [Module.rankAtStalk_eq_finrank_of_free]; rfl
  have hp : p0.asIdeal.primeCompl ≤ nonZeroDivisors O := by
    intro x hx
    have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ Ideal.zero_mem _)
    exact mem_nonZeroDivisors_of_ne_zero hx0
  have h2 : Module.rankAtStalk (R := O) M p0 = Module.finrank O M := by
    rw [Module.rankAtStalk,
      IsLocalization.finrank_eq (Localization.AtPrime p0.asIdeal) p0.asIdeal.primeCompl hp,
      IsLocalizedModule.finrank_eq p0.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap p0.asIdeal.primeCompl M) hp]
  rw [h1, Module.rankAtStalk_baseChange, hlc.apply_eq_of_preconnectedSpace _ p0, h2]

attribute [local instance] Ideal.Quotient.field in

/- English proof (translation)
Establish `hcard : Nat.card (M →ₗ[O] O ⧸ P) = Nat.card (O ⧸ P) ^ Module.finrank O M`. Rewrite using `[Nat.card_congr (LinearMap.liftBaseChangeEquiv (M := M) (N := O ⧸ P) (O ⧸ P)).toEquiv, Module.natCard_eq_pow_finrank (K := O ⧸ P)]`. Use `congr 1`. Rewrite using `[← finrank_fibre O M (O ⧸ P)]`. Conclude with `Subspace.dual_finrank_eq`.

Establish `: Finite (M →ₗ[O] O ⧸ P)` using `Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ Nat.card_pos.ne')`. Set `φ : ℙ (O ⧸ P) (M →ₗ[O] O ⧸ P) → Submodule O M` to `Projectivization.lift (fun f => LinearMap.ker f.1) (by`. Introduce and unpack `⟨a, ha⟩ ⟨b, hb⟩ t (hab : a = t • b)`. Establish `ht : t ≠ 0`. Introduce and unpack `rfl`.

Apply `ha` to reduce the goal to its premises. Rewrite using `[hab, zero_smul]`. Use extensionality with `x`. Simplify using `only [LinearMap.mem_ker, hab, LinearMap.smul_apply, smul_eq_zero, ht, false_or])`. Establish `key : ∀ (f g : M →ₗ[O] O ⧸ P) (hf : f ≠ 0) (hg : g ≠ 0), LinearMap.ker f = LinearMap.ker g → Projectivization.mk (O ⧸ P) g hg = Projectivization.mk (O ⧸ P) f hf`.

Introduce `f g hf hg hfg`. Take `⟨w, hw⟩` from `surj_of_ne P f hf`. Rewrite using `[Projectivization.mk_eq_mk_iff']`. Use `⟨g w, ?_⟩` and prove the remaining obligations. Use extensionality with `x`.

Take `⟨r, hr⟩` from `Ideal.Quotient.mk_surjective (f x)`. Establish `hmem : x - r • w ∈ LinearMap.ker g`. Rewrite using `[← hfg, LinearMap.mem_ker, map_sub, map_smul, hw, ← hr, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one, sub_self]`. Rewrite `hmem` using `[LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero]`. Rewrite using `[LinearMap.smul_apply, hmem, smul_eq_mul, ← hr, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_comm]`.

Establish `hφ : Function.Injective φ`. Introduce `x y hxy`. Rewrite `hxy`, the goal using `[← Projectivization.mk_rep x, ← Projectivization.mk_rep y]`. Conclude with `(key _ _ _ _ hxy).symm`. Establish `hS : {N : Submodule O M | ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N} = Set.range φ`.

Use extensionality with `N`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, hf, rfl⟩`. Conclude with `⟨Projectivization.mk _ f hf, rfl⟩`. Introduce and unpack `⟨x, rfl⟩`.

Use `⟨x.rep, x.rep_nonzero, ?_⟩` and prove the remaining obligations. Establish `h1 : φ (Projectivization.mk _ x.rep x.rep_nonzero) = LinearMap.ker x.rep` using `rfl`. Rewrite `h1` using `[Projectivization.mk_rep]`. Conclude with `h1.symm`. Rewrite using `[hS]`.

Use `⟨Set.finite_range φ, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.ncard_range_of_injective hφ]`. Establish `h'` using `Projectivization.card' (O ⧸ P) (M →ₗ[O] O ⧸ P)`. Rewrite `h'` using `[hcard]`. Rewrite using `[h', Nat.add_sub_cancel]`.
-/
theorem count [IsDomain O] [Module.Finite O M] [Module.Projective O M] (P : Ideal O)
    [hP : P.IsMaximal] [Finite (O ⧸ P)] :
    {N : Submodule O M | ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N}.Finite ∧
    {N : Submodule O M | ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N}.ncard *
      (Nat.card (O ⧸ P) - 1) = Nat.card (O ⧸ P) ^ Module.finrank O M - 1 := by
  classical
  have hcard : Nat.card (M →ₗ[O] O ⧸ P) = Nat.card (O ⧸ P) ^ Module.finrank O M := by
    rw [Nat.card_congr (LinearMap.liftBaseChangeEquiv (M := M) (N := O ⧸ P) (O ⧸ P)).toEquiv,
      Module.natCard_eq_pow_finrank (K := O ⧸ P)]
    congr 1
    rw [← finrank_fibre O M (O ⧸ P)]
    exact Subspace.dual_finrank_eq
  have : Finite (M →ₗ[O] O ⧸ P) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ Nat.card_pos.ne')
  let φ : ℙ (O ⧸ P) (M →ₗ[O] O ⧸ P) → Submodule O M :=
    Projectivization.lift (fun f => LinearMap.ker f.1) (by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ t (hab : a = t • b)
      have ht : t ≠ 0 := by
        rintro rfl
        apply ha
        rw [hab, zero_smul]
      ext x
      simp only [LinearMap.mem_ker, hab, LinearMap.smul_apply, smul_eq_zero, ht, false_or])
  have key : ∀ (f g : M →ₗ[O] O ⧸ P) (hf : f ≠ 0) (hg : g ≠ 0),
      LinearMap.ker f = LinearMap.ker g →
      Projectivization.mk (O ⧸ P) g hg = Projectivization.mk (O ⧸ P) f hf := by
    intro f g hf hg hfg
    obtain ⟨w, hw⟩ := surj_of_ne P f hf
    rw [Projectivization.mk_eq_mk_iff']
    refine ⟨g w, ?_⟩
    ext x
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (f x)
    have hmem : x - r • w ∈ LinearMap.ker g := by
      rw [← hfg, LinearMap.mem_ker, map_sub, map_smul, hw, ← hr, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, mul_one, sub_self]
    rw [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at hmem
    rw [LinearMap.smul_apply, hmem, smul_eq_mul, ← hr, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, mul_comm]
  have hφ : Function.Injective φ := by
    intro x y hxy
    rw [← Projectivization.mk_rep x, ← Projectivization.mk_rep y] at hxy ⊢
    exact (key _ _ _ _ hxy).symm
  have hS : {N : Submodule O M | ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N}
      = Set.range φ := by
    ext N
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨Projectivization.mk _ f hf, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨x.rep, x.rep_nonzero, ?_⟩
      have h1 : φ (Projectivization.mk _ x.rep x.rep_nonzero) = LinearMap.ker x.rep := rfl
      rw [Projectivization.mk_rep] at h1
      exact h1.symm
  rw [hS]
  refine ⟨Set.finite_range φ, ?_⟩
  rw [Set.ncard_range_of_injective hφ]
  have h' := Projectivization.card' (O ⧸ P) (M →ₗ[O] O ⧸ P)
  rw [hcard] at h'
  rw [h', Nat.add_sub_cancel]

end GlobalTheory.SW.Hyper
