import Mathlib

open NumberField Polynomial

namespace ReciprocityTheory.Cheb

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois ℚ K] [IsGalois ℚ M]

/- English proof (translation)
Establish `hl : NeZero l` using `⟨(Fact.out : l.Prime).ne_zero⟩`. Establish `htop` using `IsCyclotomicExtension.adjoin_primitive_root_eq_top (A := K) hζ`. Use `AlgEquiv.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[AlgEquiv.one_apply]`. Establish `hx : x ∈ Algebra.adjoin K ({ζ} : Set M)` using `htop ▸ Algebra.mem_top`.

Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem y hy => rw [Set.mem_singleton_iff.mp hy]`. Conclude with `h1`. Consider the case `algebraMap r`. Use `AlgEquiv.restrictNormal_commutes h K r` as an intermediate fact.

Rewrite `this` using `[hK, AlgEquiv.one_apply]`. Conclude with `this.symm`. Consider the case `add y z _ _ hy hz => rw [map_add, hy, hz]`. Consider the case `mul y z _ _ hy hz => rw [map_mul, hy, hz]`.
-/
theorem eq_one_of_restrict_eq_one {l : ℕ} [Fact l.Prime] [IsCyclotomicExtension {l} K M]
    {ζ : M} (hζ : IsPrimitiveRoot ζ l) (h : Gal(M/ℚ)) (hK : AlgEquiv.restrictNormal h K = 1) (h1 : h ζ = ζ) : h = 1 := by
  have hl : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have htop := IsCyclotomicExtension.adjoin_primitive_root_eq_top (A := K) hζ
  refine AlgEquiv.ext fun x => ?_
  rw [AlgEquiv.one_apply]
  have hx : x ∈ Algebra.adjoin K ({ζ} : Set M) := htop ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact h1
  | algebraMap r =>
    have := AlgEquiv.restrictNormal_commutes h K r
    rw [hK, AlgEquiv.one_apply] at this
    exact this.symm
  | add y z _ _ hy hz => rw [map_add, hy, hz]
  | mul y z _ _ hy hz => rw [map_mul, hy, hz]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rw [pow_succ, AlgEquiv.mul_apply, hg, map_pow, ih, ← pow_mul, ← pow_succ]`.
-/
theorem pow_apply_zeta_of_apply_eq_pow {ζ : M} (g : Gal(M/ℚ)) (t : ℕ) (hg : g ζ = ζ ^ t) (m : ℕ) :
    (g ^ m) ζ = ζ ^ (t ^ m) := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, AlgEquiv.mul_apply, hg, map_pow, ih, ← pow_mul, ← pow_succ]

/- English proof (translation)
Establish `hfin : IsOfFinOrder ζ` using `isOfFinOrder_iff_pow_eq_one.2 ⟨l, NeZero.pos l, hζ.pow_eq_one⟩`. Rewrite using `[ZMod.natCast_eq_natCast_iff, hζ.eq_orderOf]`. Conclude with `hfin.pow_eq_pow_iff_modEq`.
-/
theorem zeta_pow_eq_pow_iff_natCast {l : ℕ} [NeZero l] {ζ : M} (hζ : IsPrimitiveRoot ζ l) (a b : ℕ) :
    ζ ^ a = ζ ^ b ↔ (a : ZMod l) = b := by
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨l, NeZero.pos l, hζ.pow_eq_one⟩
  rw [ZMod.natCast_eq_natCast_iff, hζ.eq_orderOf]
  exact hfin.pow_eq_pow_iff_modEq

/- English proof (translation)
Rewrite using `[pow_apply_zeta_of_apply_eq_pow g _ hgζ m, zeta_pow_eq_pow_iff_natCast hζ]`. Simplify using the standard rewrite rules.
-/
theorem pow_apply_zeta_eq_units_pow {l : ℕ} [NeZero l] {ζ : M} (hζ : IsPrimitiveRoot ζ l) (τ : (ZMod l)ˣ)
    (g : Gal(M/ℚ)) (hgζ : g ζ = ζ ^ (τ : ZMod l).val) (m : ℕ) :
    (g ^ m) ζ = ζ ^ (((τ ^ m : (ZMod l)ˣ) : ZMod l).val) := by
  rw [pow_apply_zeta_of_apply_eq_pow g _ hgζ m, zeta_pow_eq_pow_iff_natCast hζ]
  simp

/- English proof (translation)
The claim follows from `map_pow (AlgEquiv.restrictNormalHom K) g m`.
-/
theorem restrictNormal_pow_of_gal (g : Gal(M/ℚ)) (m : ℕ) :
    AlgEquiv.restrictNormal (g ^ m) K = (AlgEquiv.restrictNormal g K) ^ m :=
  map_pow (AlgEquiv.restrictNormalHom K) g m

/- English proof (translation)
Establish `hl : NeZero l` using `⟨(Fact.out : l.Prime).ne_zero⟩`. Establish `hmem' : φ.restrictScalars ℚ ∈ IntermediateField.fixingSubgroup (IntermediateField.fixedField (Subgroup.zpowers g))`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Conclude with `φ.commutes ⟨x, hx⟩`.

Establish `hmem : φ.restrictScalars ℚ ∈ Subgroup.zpowers g`. Rewrite `hmem'` using `[IntermediateField.fixingSubgroup_fixedField]`. Then use the resulting hypothesis. Take `⟨k, hk : g ^ k = _⟩` from `mem_powers_iff_mem_zpowers.mpr hmem`. Establish `hpos` using `orderOf_pos g`. Use `set m := k + orderOf g - 1 with hm`.

Establish `hkm : g ^ (m + 1) = g ^ k`. Rewrite using `[show m + 1 = k + orderOf g by omega, pow_add, pow_orderOf_eq_one, mul_one]`. Establish `hφ' : (g ^ (m + 1)) ζ = ζ ^ n` using `by rw [hkm, hk]; exact hφ`. Rewrite `hφ'` using `[pow_apply_zeta_eq_units_pow hζ τ g hgζ, zeta_pow_eq_pow_iff_natCast hζ, ZMod.natCast_zmod_val, hn]`. Establish `hτm : τ ^ m = 1`.

Establish `h2 : τ ^ (m + 1) = τ` using `Units.ext hφ'`. Rewrite `h2` using `[pow_succ]`. Conclude with `mul_eq_right.mp h2`. Establish `hdiv : l - 1 ∣ m` using `hτ ▸ orderOf_dvd_of_pow_eq_one hτm`. Establish `hσm : σ ^ m = 1` using `orderOf_dvd_iff_pow_eq_one.mp (hσ.trans hdiv)`.

Establish `hgm : g ^ m = 1`. Use `eq_one_of_restrict_eq_one (K := K) hζ (g ^ m) ?_ ?_` and prove the remaining obligations. Rewrite using `[restrictNormal_pow_of_gal, hg, hσm]`. Rewrite using `[pow_apply_zeta_eq_units_pow hζ τ g hgζ, hτm, Units.val_one, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (Fact.out : l.Prime).one_lt, pow_one]`. Rewrite using `[← hk, ← hkm, pow_succ, hgm, one_mul]`.
-/
theorem eq_of_apply_eq_pow {l : ℕ} [Fact l.Prime] [IsCyclotomicExtension {l} K M]
    {ζ : M} (hζ : IsPrimitiveRoot ζ l) (σ : Gal(K/ℚ)) (hσ : orderOf σ ∣ l - 1) (τ : (ZMod l)ˣ) (hτ : orderOf τ = l - 1)
    (g : Gal(M/ℚ)) (hg : AlgEquiv.restrictNormal g K = σ) (hgζ : g ζ = ζ ^ (τ : ZMod l).val)
    (φ : M ≃ₐ[IntermediateField.fixedField (Subgroup.zpowers g)] M) (n : ℕ) (hφ : φ ζ = ζ ^ n) (hn : (n : ZMod l) = τ) :
    φ.restrictScalars ℚ = g := by
  have hl : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hmem' : φ.restrictScalars ℚ ∈
      IntermediateField.fixingSubgroup (IntermediateField.fixedField (Subgroup.zpowers g)) := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact φ.commutes ⟨x, hx⟩
  have hmem : φ.restrictScalars ℚ ∈ Subgroup.zpowers g := by
    rwa [IntermediateField.fixingSubgroup_fixedField] at hmem'
  obtain ⟨k, hk : g ^ k = _⟩ := mem_powers_iff_mem_zpowers.mpr hmem
  have hpos := orderOf_pos g
  set m := k + orderOf g - 1 with hm
  have hkm : g ^ (m + 1) = g ^ k := by
    rw [show m + 1 = k + orderOf g by omega, pow_add, pow_orderOf_eq_one, mul_one]
  have hφ' : (g ^ (m + 1)) ζ = ζ ^ n := by rw [hkm, hk]; exact hφ
  rw [pow_apply_zeta_eq_units_pow hζ τ g hgζ, zeta_pow_eq_pow_iff_natCast hζ, ZMod.natCast_zmod_val, hn] at hφ'
  have hτm : τ ^ m = 1 := by
    have h2 : τ ^ (m + 1) = τ := Units.ext hφ'
    rw [pow_succ] at h2
    exact mul_eq_right.mp h2
  have hdiv : l - 1 ∣ m := hτ ▸ orderOf_dvd_of_pow_eq_one hτm
  have hσm : σ ^ m = 1 := orderOf_dvd_iff_pow_eq_one.mp (hσ.trans hdiv)
  have hgm : g ^ m = 1 := by
    refine eq_one_of_restrict_eq_one (K := K) hζ (g ^ m) ?_ ?_
    · rw [restrictNormal_pow_of_gal, hg, hσm]
    · rw [pow_apply_zeta_eq_units_pow hζ τ g hgζ, hτm, Units.val_one, ZMod.val_one_eq_one_mod,
        Nat.mod_eq_of_lt (Fact.out : l.Prime).one_lt, pow_one]
  rw [← hk, ← hkm, pow_succ, hgm, one_mul]

/- English proof (translation)
Establish `hlp` using `(Fact.out : l.Prime)`. Establish `hl : NeZero l` using `⟨hlp.ne_zero⟩`. Use `set E := IntermediateField.fixedField (Subgroup.zpowers g)`. Establish `hint : IsIntegral E ζ` using `Algebra.IsIntegral.isIntegral ζ`. Use `set p := minpoly E ζ with hp`.

Establish `hcard : Fintype.card (ZMod l)ˣ = l - 1`. Rewrite using `[ZMod.card_units_eq_totient, Nat.totient_prime hlp]`. Establish `htop : Subgroup.zpowers τ = ⊤`. Apply `Subgroup.eq_top_of_card_eq` to reduce the goal to its premises. Rewrite using `[Nat.card_zpowers, hτ, Nat.card_eq_fintype_card, hcard]`.

Establish `hroot : ∀ u : (ZMod l)ˣ, aeval (ζ ^ (u : ZMod l).val) p = 0`. Introduce `u`. Establish `hu : u ∈ Subgroup.zpowers τ` using `htop ▸ Subgroup.mem_top u`. Take `⟨k, hk : τ ^ k = u⟩` from `mem_powers_iff_mem_zpowers.mpr hu`. Establish `hgk : g ^ k ∈ IntermediateField.fixingSubgroup E`.

Rewrite using `[IntermediateField.fixingSubgroup_fixedField]`. Conclude with `Subgroup.npow_mem_zpowers g k`. Use `set ψ := IntermediateField.fixingSubgroupEquiv E ⟨g ^ k, hgk⟩`. Establish `hψ : ψ ζ = ζ ^ (u : ZMod l).val`. Express the relevant statement in the definitionally equal form `(g ^ k) ζ = _`.

Rewrite using `[pow_apply_zeta_eq_units_pow hζ τ g hgζ, hk]`. Rewrite using `[← hψ, Polynomial.aeval_algEquiv, AlgHom.comp_apply, hp, minpoly.aeval, map_zero]`. Establish `hdvd : p ∣ cyclotomic l E`. Apply `minpoly.dvd` to reduce the goal to its premises. Rewrite using `[← Polynomial.eval_map_algebraMap, Polynomial.map_cyclotomic]`.

Conclude with `(hζ.isRoot_cyclotomic (NeZero.pos l))`. Establish `hp0 : p.map (algebraMap E M) ≠ 0` using `Polynomial.map_ne_zero (minpoly.ne_zero hint)`. Set `Z : Finset M` to `Finset.univ.image (fun u : (ZMod l)ˣ => ζ ^ (u : ZMod l).val)`. Establish `hZcard : Z.card = l - 1`. Rewrite using `[Finset.card_image_of_injective _ ?_, Finset.card_univ, hcard]`.

Introduce `u v huv`. Use `hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) huv` as an intermediate fact. Conclude with `Units.ext (ZMod.val_injective l this)`. Establish `hZ : Z.val ⊆ (p.map (algebraMap E M)).roots`. Introduce `z hz`.

Take `⟨u, -, rfl⟩` from `Finset.mem_image.mp hz`. Rewrite using `[Polynomial.mem_roots hp0, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]`. Conclude with `hroot u`. Establish `hdeg` using `Polynomial.card_le_degree_of_subset_roots hZ`. Rewrite `hdeg` using `[hZcard, Polynomial.natDegree_map]`.

Establish `heq : cyclotomic l E = p`. Use `Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (Polynomial.cyclotomic.monic l E) hdvd ?_` and prove the remaining obligations. Rewrite using `[Polynomial.natDegree_cyclotomic, Nat.totient_prime hlp]`. Conclude with `hdeg`. Rewrite using `[heq]`.

Conclude with `minpoly.irreducible hint`.
-/
theorem irreducible_cyclotomic_fixedField {l : ℕ} [Fact l.Prime] [IsCyclotomicExtension {l} K M]
    {ζ : M} (hζ : IsPrimitiveRoot ζ l) (σ : Gal(K/ℚ)) (hσ : orderOf σ ∣ l - 1) (τ : (ZMod l)ˣ) (hτ : orderOf τ = l - 1)
    (g : Gal(M/ℚ)) (hg : AlgEquiv.restrictNormal g K = σ) (hgζ : g ζ = ζ ^ (τ : ZMod l).val) :
    Irreducible (cyclotomic l (IntermediateField.fixedField (Subgroup.zpowers g))) := by
  have hlp := (Fact.out : l.Prime)
  have hl : NeZero l := ⟨hlp.ne_zero⟩
  set E := IntermediateField.fixedField (Subgroup.zpowers g)
  have hint : IsIntegral E ζ := Algebra.IsIntegral.isIntegral ζ
  set p := minpoly E ζ with hp
  have hcard : Fintype.card (ZMod l)ˣ = l - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hlp]

  have htop : Subgroup.zpowers τ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hτ, Nat.card_eq_fintype_card, hcard]

  have hroot : ∀ u : (ZMod l)ˣ, aeval (ζ ^ (u : ZMod l).val) p = 0 := by
    intro u
    have hu : u ∈ Subgroup.zpowers τ := htop ▸ Subgroup.mem_top u
    obtain ⟨k, hk : τ ^ k = u⟩ := mem_powers_iff_mem_zpowers.mpr hu
    have hgk : g ^ k ∈ IntermediateField.fixingSubgroup E := by
      rw [IntermediateField.fixingSubgroup_fixedField]
      exact Subgroup.npow_mem_zpowers g k
    set ψ := IntermediateField.fixingSubgroupEquiv E ⟨g ^ k, hgk⟩
    have hψ : ψ ζ = ζ ^ (u : ZMod l).val := by
      change (g ^ k) ζ = _
      rw [pow_apply_zeta_eq_units_pow hζ τ g hgζ, hk]
    rw [← hψ, Polynomial.aeval_algEquiv, AlgHom.comp_apply, hp, minpoly.aeval, map_zero]
  have hdvd : p ∣ cyclotomic l E := by
    apply minpoly.dvd
    rw [← Polynomial.eval_map_algebraMap, Polynomial.map_cyclotomic]
    exact (hζ.isRoot_cyclotomic (NeZero.pos l))
  have hp0 : p.map (algebraMap E M) ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hint)
  classical
  let Z : Finset M := Finset.univ.image (fun u : (ZMod l)ˣ => ζ ^ (u : ZMod l).val)
  have hZcard : Z.card = l - 1 := by
    rw [Finset.card_image_of_injective _ ?_, Finset.card_univ, hcard]
    intro u v huv
    have := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) huv
    exact Units.ext (ZMod.val_injective l this)
  have hZ : Z.val ⊆ (p.map (algebraMap E M)).roots := by
    intro z hz
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hz
    rw [Polynomial.mem_roots hp0, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
    exact hroot u
  have hdeg := Polynomial.card_le_degree_of_subset_roots hZ
  rw [hZcard, Polynomial.natDegree_map] at hdeg
  have heq : cyclotomic l E = p := by
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
      (Polynomial.cyclotomic.monic l E) hdvd ?_
    rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hlp]
    exact hdeg
  rw [heq]
  exact minpoly.irreducible hint

end ReciprocityTheory.Cheb
