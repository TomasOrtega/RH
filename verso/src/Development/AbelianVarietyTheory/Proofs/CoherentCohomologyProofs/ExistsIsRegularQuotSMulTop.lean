import Mathlib

universe u_1 u_2

open CategoryTheory Abelian Limits RingTheory.Sequence Pointwise

namespace GlobalTheory.RegularElementQuotient

/- English proof (translation)
Rewrite using `[lt_top_iff_ne_top]`. Introduce `h`. Establish `hbot : (⊤ : Submodule R M) = ⊥` using `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) ⊤ Module.Finite.fg_top h.ge (IsLocalRing.maximalIdeal_le_jacobson ⊥)`. Conclude with `top_ne_bot hbot`.
-/
theorem maximalIdeal_smul_top_lt_top {R : Type u_1} [CommRing R] [IsLocalRing R]
    (M : Type u_2) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro h

  have hbot : (⊤ : Submodule R M) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) ⊤
      Module.Finite.fg_top h.ge (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  exact top_ne_bot hbot

/- English proof (translation)
Use `set 𝔪 := IsLocalRing.maximalIdeal R`. Establish `: Nontrivial M` using `(Submodule.nontrivial_iff R).mp (nontrivial_of_ne _ _ hxs.top_ne_smul)`. Establish `hmem : ∀ x ∈ xs, x ∈ 𝔪`. Introduce `x hx`. Assume the negation of the conclusion as `hx𝔪`.

Establish `hu : IsUnit x`. Assume the negation of the conclusion as `hnu`. Conclude with `hx𝔪 ((IsLocalRing.mem_maximalIdeal x).mpr hnu)`. Establish `htop : Ideal.ofList xs = ⊤` using `Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span hx) hu`. Apply `hxs.top_ne_smul` to reduce the goal to its premises.

Rewrite using `[htop, Submodule.top_smul]`. Establish `: Nontrivial (QuotSMulTop y M)`. Apply `Submodule.Quotient.nontrivial_iff.mpr` to reduce the goal to its premises. Use `ne_top_of_le_ne_top (maximalIdeal_smul_top_lt_top (R := R) M).ne ?_` and prove the remaining obligations. Rewrite using `[← Submodule.ideal_span_singleton_smul]`.

Conclude with `Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem _).mpr hy)`. Establish `hltM : 𝔪 • (⊤ : Submodule R M) < ⊤` using `maximalIdeal_smul_top_lt_top M`. Establish `hltQ : 𝔪 • (⊤ : Submodule R (QuotSMulTop y M)) < ⊤` using `maximalIdeal_smul_top_lt_top (QuotSMulTop y M)`. Establish `hM` using `(ModuleCat.exists_isRegular_tfae 𝔪 xs.length (ModuleCat.of R M) hltM).out 3 1`. Establish `hExtM` using `hM.mp ⟨xs, rfl, hmem, hxs⟩`.

Establish `hS` using `IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of R M) hreg`. Establish `hExtQ : ∀ i < n, Subsingleton (Abelian.Ext (ModuleCat.of R (Shrink.{u_2} (R ⧸ 𝔪))) (ModuleCat.of R (QuotSMulTop y M)) i)`. Introduce `i hi`. Establish `hE` using `Abelian.Ext.covariant_sequence_exact₃' (ModuleCat.of R (Shrink.{u_2} (R ⧸ 𝔪))) hS i (i + 1) rfl`. Rewrite `hE` using `[ShortComplex.ab_exact_iff_function_exact]`.

Establish `h0` using `hExtM i (by omega)`. Establish `h1` using `hExtM (i + 1) (by omega)`. Establish `key : ∀ x : Abelian.Ext (ModuleCat.of R (Shrink.{u_2} (R ⧸ 𝔪))) (ModuleCat.of R (QuotSMulTop y M)) i, x = 0`. Introduce `x`. Take `⟨w, hw⟩` from `(hE x).mp (h1.elim _ _)`.

Rewrite using `[← hw, h0.elim w 0]`. Conclude with `map_zero _`. Conclude with `⟨fun a b => by rw [key a, key b]⟩`. Establish `hQ` using `(ModuleCat.exists_isRegular_tfae 𝔪 n (ModuleCat.of R (QuotSMulTop y M)) hltQ).out 1 3`. Take `⟨zs, hlen, -, hzs⟩` from `hQ.mp hExtQ`.

Conclude with `⟨zs, hlen, hzs⟩`.
-/
theorem exists_isRegular_quotSMulTop {R : Type u_1} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [Small.{u_2, u_1} R] {M : Type u_2} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {xs : List R} (hxs : IsRegular M xs) {n : ℕ}
    (hn : n + 1 ≤ xs.length) {y : R} (hy : y ∈ IsLocalRing.maximalIdeal R)
    (hreg : IsSMulRegular M y) :
    ∃ zs : List R, zs.length = n ∧ IsRegular (QuotSMulTop y M) zs := by
  set 𝔪 := IsLocalRing.maximalIdeal R

  have : Nontrivial M :=
    (Submodule.nontrivial_iff R).mp (nontrivial_of_ne _ _ hxs.top_ne_smul)

  have hmem : ∀ x ∈ xs, x ∈ 𝔪 := by
    intro x hx
    by_contra hx𝔪
    have hu : IsUnit x := by
      by_contra hnu
      exact hx𝔪 ((IsLocalRing.mem_maximalIdeal x).mpr hnu)
    have htop : Ideal.ofList xs = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span hx) hu
    apply hxs.top_ne_smul
    rw [htop, Submodule.top_smul]

  have : Nontrivial (QuotSMulTop y M) := by
    apply Submodule.Quotient.nontrivial_iff.mpr
    refine ne_top_of_le_ne_top (maximalIdeal_smul_top_lt_top (R := R) M).ne ?_
    rw [← Submodule.ideal_span_singleton_smul]
    exact Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem _).mpr hy)
  have hltM : 𝔪 • (⊤ : Submodule R M) < ⊤ := maximalIdeal_smul_top_lt_top M
  have hltQ : 𝔪 • (⊤ : Submodule R (QuotSMulTop y M)) < ⊤ :=
    maximalIdeal_smul_top_lt_top (QuotSMulTop y M)

  have hM := (ModuleCat.exists_isRegular_tfae 𝔪 xs.length (ModuleCat.of R M) hltM).out 3 1
  have hExtM := hM.mp ⟨xs, rfl, hmem, hxs⟩

  have hS := IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of R M) hreg
  have hExtQ : ∀ i < n, Subsingleton (Abelian.Ext
      (ModuleCat.of R (Shrink.{u_2} (R ⧸ 𝔪))) (ModuleCat.of R (QuotSMulTop y M)) i) := by
    intro i hi
    have hE := Abelian.Ext.covariant_sequence_exact₃'
      (ModuleCat.of R (Shrink.{u_2} (R ⧸ 𝔪))) hS i (i + 1) rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at hE
    have h0 := hExtM i (by omega)
    have h1 := hExtM (i + 1) (by omega)
    have key : ∀ x : Abelian.Ext (ModuleCat.of R (Shrink.{u_2} (R ⧸ 𝔪)))
        (ModuleCat.of R (QuotSMulTop y M)) i, x = 0 := by
      intro x
      obtain ⟨w, hw⟩ := (hE x).mp (h1.elim _ _)
      rw [← hw, h0.elim w 0]
      exact map_zero _
    exact ⟨fun a b => by rw [key a, key b]⟩

  have hQ := (ModuleCat.exists_isRegular_tfae 𝔪 n
    (ModuleCat.of R (QuotSMulTop y M)) hltQ).out 1 3
  obtain ⟨zs, hlen, -, hzs⟩ := hQ.mp hExtQ
  exact ⟨zs, hlen, hzs⟩

end GlobalTheory.RegularElementQuotient
