import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `k A _ _ _ _ _ y hfin hinj hsep`. Use `letI : Algebra k[X] A := (Polynomial.aeval (R := k) y).toRingHom.toAlgebra`. Establish `hmap : ∀ p : k[X], algebraMap k[X] A p = Polynomial.aeval y p` using `fun p => rfl`. Use `haveI : IsScalarTower k k[X] A := IsScalarTower.of_algebraMap_eq (fun c => by`. Rewrite using `[hmap, Polynomial.algebraMap_apply, Polynomial.aeval_C]`.

Use the proof step `rfl)`. Use `haveI : Module.Finite k[X] A := hfin`. Use `haveI : FaithfulSMul k[X] A := (faithfulSMul_iff_algebraMap_injective k[X] A).mpr hinj`. Use `letI : Algebra (FractionRing k[X]) (FractionRing A) := FractionRing.liftAlgebra k[X] (FractionRing A)`. Use `haveI : IsScalarTower k[X] (FractionRing k[X]) (FractionRing A) := FractionRing.isScalarTower_liftAlgebra k[X] (FractionRing A)`.

Use `set L := FractionRing A`. Use `set K := FractionRing k[X]`. Use `set ybar : L := algebraMap A L y`. Use `set E := IntermediateField.adjoin k {ybar}`. Establish `hpoly : ∀ p : k[X], algebraMap K L (algebraMap k[X] K p) = algebraMap A L (Polynomial.aeval y p)`.

Introduce `p`. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply k[X] A L]`. Both sides reduce to the same expression. Establish `hpolyE : ∀ p : k[X], algebraMap A L (Polynomial.aeval y p) ∈ E`. Introduce `p`.

Establish `: algebraMap A L (Polynomial.aeval y p) = Polynomial.aeval ybar p`. Rewrite using `[Polynomial.aeval_algebraMap_apply]`. Rewrite using `[this]`. Establish `hy : ybar ∈ E` using `IntermediateField.mem_adjoin_simple_self k ybar`. Use `Polynomial.aeval_algHom_apply E.val (⟨ybar, hy⟩ : E) p` as an intermediate fact.

Simplify using `only [IntermediateField.coe_val] at this`. Rewrite using `[show ybar = ((⟨ybar, hy⟩ : E) : L) from rfl, this]`. Conclude with `(Polynomial.aeval (⟨ybar, hy⟩ : E) p).2`. Establish `hrange : ∀ z : K, algebraMap K L z ∈ E`. Introduce `z`.

Take `⟨a, b, _, rfl⟩` from `IsFractionRing.div_surjective (A := k[X]) z`. Rewrite using `[map_div₀, hpoly, hpoly]`. Conclude with `div_mem (hpolyE a) (hpolyE b)`. Set `f : K →+* E` to `(algebraMap K L).codRestrict E hrange`. Establish `hf : ∀ z : K, (f z : L) = algebraMap K L z` using `fun z => rfl`.

Set `S : IntermediateField k L` to `(algebraMap K L).fieldRange.toIntermediateField (fun c => ⟨algebraMap k[X] K (Polynomial.C c), by`. Rewrite using `[hpoly, Polynomial.aeval_C, ← IsScalarTower.algebraMap_apply]⟩)`. Establish `hES : E ≤ S` using `IntermediateField.adjoin_simple_le_iff.2 ⟨algebraMap k[X] K Polynomial.X, by rw [hpoly, Polynomial.aeval_X]⟩`. Establish `hsurj : Function.Surjective f`. Introduce `e`.

Take `⟨z, hz⟩` from `hES e.2`. Conclude with `⟨z, Subtype.ext (by rw [hf]; exact hz)⟩`. Set `e₁ : E ≃+* K` to `(RingEquiv.ofBijective f ⟨f.injective, hsurj⟩).symm`. Establish `he : (algebraMap K L).comp (e₁ : E →+* K) = (RingEquiv.refl L : L →+* L).comp (algebraMap E L)`. Use extensionality with `x`.

Simplify using `only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, RingEquiv.refl_apply]`. Rewrite using `[← hf]`. Express the relevant statement in the definitionally equal form `((RingEquiv.ofBijective f ⟨f.injective, hsurj⟩) ((RingEquiv.ofBijective f ⟨f.injective, hsurj⟩).symm x) : L) = _`. Rewrite using `[RingEquiv.apply_symm_apply]`. Both sides reduce to the same expression.

Use `haveI : Algebra.IsSeparable K L := Algebra.IsSeparable.of_equiv_equiv e₁ (RingEquiv.refl L) he`. Establish `hD` using `differentIdeal_ne_bot (A := k[X]) (B := A)`. Take `⟨d, hd, hd0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hD`. Establish `hc` using `Ideal.comap_ne_bot_of_integral_mem hd0 hd (Algebra.IsIntegral.isIntegral (R := k[X]) d)`. Take `⟨δ, hδ, hδ0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hc`.

Use `⟨δ, hδ0, fun α hα Q hQ hmem' => hα ?_⟩` and prove the remaining obligations. Establish `hmem : algebraMap k[X] A (X - C α) ∈ Q ^ 2`. Rewrite using `[hmap, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]`. Conclude with `hmem'`. Use `set p : Ideal k[X] := Ideal.span {X - C α} with hpdef`.

Use `haveI hpmax : p.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C α)`. Establish `hp0 : p ≠ ⊥`. Rewrite using `[hpdef, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `X_sub_C_ne_zero α`. Establish `hP : Q ^ 2 ∣ p.map (algebraMap k[X] A)`.

Rewrite using `[Ideal.dvd_iff_le, hpdef, Ideal.map_span, Ideal.span_le]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Rewrite `hy` using `[Set.mem_singleton_iff]`. Substitute `hy` using the available equality. Conclude with `hmem`.

Establish `hdiv` using `pow_sub_one_dvd_differentIdeal (A := k[X]) (B := A) Q 2 hp0 hP`. Rewrite `hdiv` using `[show 2 - 1 = 1 from rfl, pow_one, Ideal.dvd_iff_le]`. Establish `hδQ : δ ∈ Q.comap (algebraMap k[X] A)` using `hdiv hδ`. Establish `hXQ : X - C α ∈ Q.comap (algebraMap k[X] A)` using `Ideal.mem_comap.mpr (Ideal.pow_le_self two_ne_zero hmem)`. Establish `hle : p ≤ Q.comap (algebraMap k[X] A)`.

Rewrite using `[hpdef, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hXQ`. Establish `heq : p = Q.comap (algebraMap k[X] A)` using `hpmax.eq_of_le (hQ.isPrime.comap _).ne_top hle`. Rewrite `hδQ` using `[← heq, hpdef, Ideal.mem_span_singleton, dvd_iff_isRoot]`. Conclude with `hδQ`.
-/
theorem reduced_fibres_almost_all_sep : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] (y : A), (Polynomial.aeval (R := k) y).Finite → Function.Injective (Polynomial.aeval (R := k) y) → Algebra.IsSeparable (IntermediateField.adjoin k {algebraMap A (FractionRing A) y}) (FractionRing A) → ∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal → y - algebraMap k A α ∉ Q ^ 2 := by
  intro k A _ _ _ _ _ y hfin hinj hsep
  letI : Algebra k[X] A := (Polynomial.aeval (R := k) y).toRingHom.toAlgebra
  have hmap : ∀ p : k[X], algebraMap k[X] A p = Polynomial.aeval y p := fun p => rfl
  haveI : IsScalarTower k k[X] A := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [hmap, Polynomial.algebraMap_apply, Polynomial.aeval_C]; rfl)
  haveI : Module.Finite k[X] A := hfin
  haveI : FaithfulSMul k[X] A := (faithfulSMul_iff_algebraMap_injective k[X] A).mpr hinj
  letI : Algebra (FractionRing k[X]) (FractionRing A) := FractionRing.liftAlgebra k[X] (FractionRing A)
  haveI : IsScalarTower k[X] (FractionRing k[X]) (FractionRing A) :=
    FractionRing.isScalarTower_liftAlgebra k[X] (FractionRing A)
  set L := FractionRing A
  set K := FractionRing k[X]
  set ybar : L := algebraMap A L y
  set E := IntermediateField.adjoin k {ybar}
  have hpoly : ∀ p : k[X], algebraMap K L (algebraMap k[X] K p) = algebraMap A L (Polynomial.aeval y p) := by
    intro p
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply k[X] A L]; rfl
  have hpolyE : ∀ p : k[X], algebraMap A L (Polynomial.aeval y p) ∈ E := by
    intro p
    have : algebraMap A L (Polynomial.aeval y p) = Polynomial.aeval ybar p := by
      rw [Polynomial.aeval_algebraMap_apply]
    rw [this]
    have hy : ybar ∈ E := IntermediateField.mem_adjoin_simple_self k ybar
    have := Polynomial.aeval_algHom_apply E.val (⟨ybar, hy⟩ : E) p
    simp only [IntermediateField.coe_val] at this
    rw [show ybar = ((⟨ybar, hy⟩ : E) : L) from rfl, this]
    exact (Polynomial.aeval (⟨ybar, hy⟩ : E) p).2
  have hrange : ∀ z : K, algebraMap K L z ∈ E := by
    intro z
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := k[X]) z
    rw [map_div₀, hpoly, hpoly]
    exact div_mem (hpolyE a) (hpolyE b)
  let f : K →+* E := (algebraMap K L).codRestrict E hrange
  have hf : ∀ z : K, (f z : L) = algebraMap K L z := fun z => rfl
  let S : IntermediateField k L := (algebraMap K L).fieldRange.toIntermediateField (fun c =>
    ⟨algebraMap k[X] K (Polynomial.C c), by
      rw [hpoly, Polynomial.aeval_C, ← IsScalarTower.algebraMap_apply]⟩)
  have hES : E ≤ S := IntermediateField.adjoin_simple_le_iff.2
    ⟨algebraMap k[X] K Polynomial.X, by rw [hpoly, Polynomial.aeval_X]⟩
  have hsurj : Function.Surjective f := by
    intro e
    obtain ⟨z, hz⟩ := hES e.2
    exact ⟨z, Subtype.ext (by rw [hf]; exact hz)⟩
  let e₁ : E ≃+* K := (RingEquiv.ofBijective f ⟨f.injective, hsurj⟩).symm
  have he : (algebraMap K L).comp (e₁ : E →+* K) = (RingEquiv.refl L : L →+* L).comp (algebraMap E L) := by
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, RingEquiv.refl_apply]
    rw [← hf]
    change ((RingEquiv.ofBijective f ⟨f.injective, hsurj⟩) ((RingEquiv.ofBijective f ⟨f.injective, hsurj⟩).symm x) : L) = _
    rw [RingEquiv.apply_symm_apply]; rfl
  haveI : Algebra.IsSeparable K L := Algebra.IsSeparable.of_equiv_equiv e₁ (RingEquiv.refl L) he
  have hD := differentIdeal_ne_bot (A := k[X]) (B := A)
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
  have hc := Ideal.comap_ne_bot_of_integral_mem hd0 hd (Algebra.IsIntegral.isIntegral (R := k[X]) d)
  obtain ⟨δ, hδ, hδ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  refine ⟨δ, hδ0, fun α hα Q hQ hmem' => hα ?_⟩
  have hmem : algebraMap k[X] A (X - C α) ∈ Q ^ 2 := by
    rw [hmap, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]; exact hmem'
  set p : Ideal k[X] := Ideal.span {X - C α} with hpdef
  haveI hpmax : p.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C α)
  have hp0 : p ≠ ⊥ := by
    rw [hpdef, Ne, Ideal.span_singleton_eq_bot]; exact X_sub_C_ne_zero α
  have hP : Q ^ 2 ∣ p.map (algebraMap k[X] A) := by
    rw [Ideal.dvd_iff_le, hpdef, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy; exact hmem
  have hdiv := pow_sub_one_dvd_differentIdeal (A := k[X]) (B := A) Q 2 hp0 hP
  rw [show 2 - 1 = 1 from rfl, pow_one, Ideal.dvd_iff_le] at hdiv
  have hδQ : δ ∈ Q.comap (algebraMap k[X] A) := hdiv hδ
  have hXQ : X - C α ∈ Q.comap (algebraMap k[X] A) :=
    Ideal.mem_comap.mpr (Ideal.pow_le_self two_ne_zero hmem)
  have hle : p ≤ Q.comap (algebraMap k[X] A) := by
    rw [hpdef, Ideal.span_le, Set.singleton_subset_iff]; exact hXQ
  have heq : p = Q.comap (algebraMap k[X] A) :=
    hpmax.eq_of_le (hQ.isPrime.comap _).ne_top hle
  rw [← heq, hpdef, Ideal.mem_span_singleton, dvd_iff_isRoot] at hδQ
  exact hδQ

end GlobalTheory
