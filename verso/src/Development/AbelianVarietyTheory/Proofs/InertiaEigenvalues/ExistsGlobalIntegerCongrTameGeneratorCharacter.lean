import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChiTameUnit

/- English proof (translation)
Introduce `D k v`. Use `set w := D.naut.plGw k v with hw`. Use `set A := D.nd.plOm.1 w with hAdef`. Establish `hA : IsPlaceOver A w` using `D.nd.plOm.2 w`. Establish `: IsAlgClosed D.nd.Om` using `IsAlgClosure.isAlgClosed D.host.E`.

Establish `hp : (D.host.g k).Prime` using `D.host.g_prime k`. Establish `hN : normV w = D.host.g k` using `GlobalTheory.TameLabels.normV_eq_of_split hp (D.nd.g_split k) (D.naut.plGw_over k v)`. Establish `hgw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal` using `D.naut.plGw_over k v`. Establish `hn : 0 < normV w - 1` using `by rw [hN]; have := hp.two_le; omega`. Take `⟨ϖ, h1, h2⟩` from `SetLike.exists_of_lt (Ideal.pow_lt_self w.asIdeal w.ne_bot w.isPrime.ne_top 2 le_rfl)`.

Take `⟨π, hπ⟩` from `IsAlgClosed.exists_pow_nat_eq (algebraMap D.host.E D.nd.Om (ϖ : D.host.E)) hn`. Establish `hϖ0 : ϖ ≠ 0` using `by rintro rfl; exact h2 (zero_mem _)`. Establish `h0 : π ≠ 0`. Introduce and unpack `rfl`. Rewrite `hπ` using `[zero_pow hn.ne', eq_comm, map_eq_zero]`.

Conclude with `hϖ0 (by simpa using hπ)`. Use `set ζ := D.ntypes.tg k v π / π with hζ`. Establish `hζn : ζ ^ (normV w - 1) = 1`. Rewrite using `[hζ, div_pow, ← map_pow, hπ, AlgEquiv.commutes, ← hπ, div_self (pow_ne_zero _ h0)]`. Establish `hv1 : A.valuation ζ = 1`.

Use `pow_left_injective hn.ne' ?_` and prove the remaining obligations. Use `show _ ^ _ = 1 ^ _`. Rewrite using `[← map_pow, hζn, map_one, one_pow]`. Establish `hζA : ζ ∈ A` using `(A.valuation_le_one_iff ζ).mp hv1.le`. Use `haveI hcp : CharP (IsLocalRing.ResidueField A) (D.host.g k) := by`.

Use `(CharP.charP_iff_prime_eq_zero hp).2 ?_` and prove the remaining obligations. Rewrite using `[← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]`. Use `(hA _).mpr hgw` as an intermediate fact. Simplify using `using this`. Use `haveI : Fact (D.host.g k).Prime := ⟨hp⟩`.

Use `set z := IsLocalRing.residue A ⟨ζ, hζA⟩ with hz`. Establish `hzp : z ^ (D.host.g k) - z = 0`. Establish `e : (⟨ζ, hζA⟩ : A) ^ (normV w - 1) = 1` using `Subtype.ext (by simpa using hζn)`. Establish `e2 : z ^ (normV w - 1) = 1` using `by rw [hz, ← map_pow, e, map_one]`. Rewrite `e2` using `[hN]`.

Establish `: z ^ (D.host.g k) = z`. Rewrite using `[← Nat.sub_add_cancel hp.one_lt.le, pow_succ, e2, one_mul]`. Rewrite using `[this, sub_self]`. Establish `hmon : (X ^ (D.host.g k) - X : (ZMod (D.host.g k))[X]).Monic` using `monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hp.one_lt)`. Establish `hroots` using `FiniteField.roots_X_pow_card_sub_X (ZMod (D.host.g k))`.

Rewrite `hroots` using `[ZMod.card]`. Establish `hprod` using `prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by`. Rewrite using `[hroots, FiniteField.X_pow_card_sub_X_natDegree_eq _ hp.one_lt, Finset.card_val, Finset.card_univ, ZMod.card])`. Establish `hev` using `congrArg (fun P => (P.map (ZMod.castHom (dvd_refl _) (IsLocalRing.ResidueField A))).eval z) hprod`. Simplify using `only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.map_pow, eval_multiset_prod, Multiset.map_map, eval_sub, eval_X, eval_C, eval_pow, hzp] at hev`.

Take `⟨a, -, hy0⟩` from `Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hev)`. Establish `hcong : A.valuation (ζ - ((a.val : ℕ) : D.nd.Om)) < 1`. Establish `: (⟨ζ, hζA⟩ : A) - ((a.val : ℕ) : A) ∈ IsLocalRing.maximalIdeal A`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, ← hz, map_natCast, ZMod.natCast_val]`. Simplify using `using hy0`.

Rewrite `this` using `[ValuationSubring.valuation_lt_one_iff]`. Simplify `this` using `[-ZMod.natCast_val]`. Establish `hu : ((a.val : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal`. Introduce `hm`. Establish `h3` using `(hA _).mpr hm`.

Simplify using `only [map_natCast] at h3`. Establish `h4` using `Valuation.map_add_lt _ hcong h3`. Rewrite `h4` using `[sub_add_cancel, hv1]`. Conclude with `lt_irrefl _ h4`. Use `⟨((a.val : ℕ) : 𝓞 D.host.E), ?_, hu, ϖ, π, h1, h2, hπ, ?_⟩` and prove the remaining obligations.

Introduce `h`. Apply `hu` to reduce the goal to its premises. Establish `: ((a.val : ℕ) : 𝓞 D.host.E) = 0` using `by exact_mod_cast h`. Rewrite using `[this]`. Conclude with `zero_mem _`.

Establish `e : algebraMap D.host.E D.nd.Om (((a.val : ℕ) : 𝓞 D.host.E) : D.host.E) = ((a.val : ℕ) : D.nd.Om)`. Simplify using `only [RingOfIntegers.coe_eq_algebraMap, map_natCast]`. Rewrite using `[e]`. Conclude with `hcong`.
-/
theorem exists_int_cong_tg : ∀ (D : D7) (k : Fin 2) (v : D.nd.PlG k), ∃ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), u ∉ (D.naut.plGw k v).asIdeal ∧ ∃ (ϖ : 𝓞 D.host.E) (π : D.nd.Om), ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1 := by
  intro D k v
  set w := D.naut.plGw k v with hw
  set A := D.nd.plOm.1 w with hAdef
  have hA : IsPlaceOver A w := D.nd.plOm.2 w
  have : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  have hp : (D.host.g k).Prime := D.host.g_prime k
  have hN : normV w = D.host.g k := GlobalTheory.TameLabels.normV_eq_of_split hp (D.nd.g_split k) (D.naut.plGw_over k v)
  have hgw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := D.naut.plGw_over k v
  have hn : 0 < normV w - 1 := by rw [hN]; have := hp.two_le; omega
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt
    (Ideal.pow_lt_self w.asIdeal w.ne_bot w.isPrime.ne_top 2 le_rfl)
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap D.host.E D.nd.Om (ϖ : D.host.E)) hn
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have h0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne', eq_comm, map_eq_zero] at hπ
    exact hϖ0 (by simpa using hπ)
  set ζ := D.ntypes.tg k v π / π with hζ
  have hζn : ζ ^ (normV w - 1) = 1 := by
    rw [hζ, div_pow, ← map_pow, hπ, AlgEquiv.commutes, ← hπ, div_self (pow_ne_zero _ h0)]
  have hv1 : A.valuation ζ = 1 := by
    refine pow_left_injective hn.ne' ?_
    show _ ^ _ = 1 ^ _
    rw [← map_pow, hζn, map_one, one_pow]

  have hζA : ζ ∈ A := (A.valuation_le_one_iff ζ).mp hv1.le
  haveI hcp : CharP (IsLocalRing.ResidueField A) (D.host.g k) := by
    refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    have := (hA _).mpr hgw
    simpa using this
  haveI : Fact (D.host.g k).Prime := ⟨hp⟩
  set z := IsLocalRing.residue A ⟨ζ, hζA⟩ with hz
  have hzp : z ^ (D.host.g k) - z = 0 := by
    have e : (⟨ζ, hζA⟩ : A) ^ (normV w - 1) = 1 := Subtype.ext (by simpa using hζn)
    have e2 : z ^ (normV w - 1) = 1 := by rw [hz, ← map_pow, e, map_one]
    rw [hN] at e2
    have : z ^ (D.host.g k) = z := by
      rw [← Nat.sub_add_cancel hp.one_lt.le, pow_succ, e2, one_mul]
    rw [this, sub_self]
  have hmon : (X ^ (D.host.g k) - X : (ZMod (D.host.g k))[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hp.one_lt)
  have hroots := FiniteField.roots_X_pow_card_sub_X (ZMod (D.host.g k))
  rw [ZMod.card] at hroots
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by
    rw [hroots, FiniteField.X_pow_card_sub_X_natDegree_eq _ hp.one_lt, Finset.card_val, Finset.card_univ,
      ZMod.card])
  have hev := congrArg (fun P => (P.map (ZMod.castHom (dvd_refl _) (IsLocalRing.ResidueField A))).eval z) hprod
  simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_pow, eval_multiset_prod, Multiset.map_map, eval_sub, eval_X, eval_C, eval_pow, hzp] at hev
  obtain ⟨a, -, hy0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hev)

  have hcong : A.valuation (ζ - ((a.val : ℕ) : D.nd.Om)) < 1 := by
    have : (⟨ζ, hζA⟩ : A) - ((a.val : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hz, map_natCast, ZMod.natCast_val]
      simpa using hy0
    rw [ValuationSubring.valuation_lt_one_iff] at this
    simpa [-ZMod.natCast_val] using this
  have hu : ((a.val : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
    intro hm
    have h3 := (hA _).mpr hm
    simp only [map_natCast] at h3
    have h4 := Valuation.map_add_lt _ hcong h3
    rw [sub_add_cancel, hv1] at h4
    exact lt_irrefl _ h4
  refine ⟨((a.val : ℕ) : 𝓞 D.host.E), ?_, hu, ϖ, π, h1, h2, hπ, ?_⟩
  · intro h
    apply hu
    have : ((a.val : ℕ) : 𝓞 D.host.E) = 0 := by exact_mod_cast h
    rw [this]; exact zero_mem _
  · have e : algebraMap D.host.E D.nd.Om (((a.val : ℕ) : 𝓞 D.host.E) : D.host.E) = ((a.val : ℕ) : D.nd.Om) := by
      simp only [RingOfIntegers.coe_eq_algebraMap, map_natCast]
    rw [e]
    exact hcong

end GlobalTheory.ChiTameUnit

end
