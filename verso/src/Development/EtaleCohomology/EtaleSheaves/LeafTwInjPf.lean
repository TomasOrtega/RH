import Development.EtaleCohomology.EtaleSheaves.LeafTwSecPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.LeafTwSecPf

namespace LateralTheory.E.LeafTwInjPf

/- English proof (translation)
Establish `hq : (q : K) ≠ 0` using `by simpa using (ξ.2.1.map π).ne_zero`. Use `haveI : NeZero (q : K) := ⟨hq⟩`. Rewrite using `[← Polynomial.isRoot_cyclotomic_iff]`. Establish `h` using `Polynomial.aeval_algHom_apply π.toIntAlgHom ξ.1 (Polynomial.cyclotomic q ℤ)`. Rewrite `h` using `[ξ.2.2, map_zero]`.

Rewrite using `[Polynomial.IsRoot, ← Polynomial.map_cyclotomic q (Int.castRingHom K), Polynomial.eval_map]`. Rewrite `h` using `[Polynomial.aeval_def, algebraMap_int_eq]`. Conclude with `h`.
-/
theorem prim_field {q : ℕ} [NeZero q] {A : Type} [CommRing A] {K : Type} [Field K] (π : A →+* K)
    (ξ : Prim q A) : IsPrimitiveRoot (π ξ.1) q := by
  have hq : (q : K) ≠ 0 := by simpa using (ξ.2.1.map π).ne_zero
  haveI : NeZero (q : K) := ⟨hq⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have h := Polynomial.aeval_algHom_apply π.toIntAlgHom ξ.1 (Polynomial.cyclotomic q ℤ)
  rw [ξ.2.2, map_zero] at h
  rw [Polynomial.IsRoot, ← Polynomial.map_cyclotomic q (Int.castRingHom K), Polynomial.eval_map]
  rw [Polynomial.aeval_def, algebraMap_int_eq] at h
  exact h

/- English proof (translation)
Establish `hf : IsOfFinOrder μ` using `isOfFinOrder_iff_pow_eq_one.2 ⟨q, NeZero.pos q, hμ.pow_eq_one⟩`. Rewrite using `[hf.pow_eq_pow_iff_modEq, ← hμ.eq_orderOf, ZMod.natCast_eq_natCast_iff]`.
-/
theorem pow_val_eq {q : ℕ} [NeZero q] {K : Type} [Field K] {μ : K} (hμ : IsPrimitiveRoot μ q) (m n : ℕ) :
    μ ^ m = μ ^ n ↔ (m : ZMod q) = n := by
  have hf : IsOfFinOrder μ := isOfFinOrder_iff_pow_eq_one.2 ⟨q, NeZero.pos q, hμ.pow_eq_one⟩
  rw [hf.pow_eq_pow_iff_modEq, ← hμ.eq_orderOf, ZMod.natCast_eq_natCast_iff]

/- English proof (translation)
Take `⟨m, hm⟩` from `Ideal.exists_maximal A`. Use `letI : Field (A ⧸ m) := Ideal.Quotient.field m`. Set `π : A →+* A ⧸ m` to `Ideal.Quotient.mk m`. Establish `hμ` using `prim_field π ζ`. Establish `hex : ∀ ξ : Prim q A, ∃ u : (ZMod q)ˣ, π ξ.1 = π ζ.1 ^ (u : ZMod q).val`.

Introduce `ξ`. Take `⟨j, hj, hj'⟩` from `hμ.eq_pow_of_pow_eq_one (prim_field π ξ).pow_eq_one`. Establish `cop : j.Coprime q` using `(hμ.pow_iff_coprime (NeZero.pos q) j).1 (hj' ▸ prim_field π ξ)`. Use `⟨ZMod.unitOfCoprime j cop, ?_⟩` and prove the remaining obligations. Rewrite using `[ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hj, hj']`.

Establish `uniq : ∀ u w : (ZMod q)ˣ, π ζ.1 ^ (u : ZMod q).val = π ζ.1 ^ (w : ZMod q).val → u = w`. Introduce `u w huw`. Rewrite `huw` using `[pow_val_eq hμ, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]`. Conclude with `Units.ext huw`. Use `choose e he using hex`.

Establish `hmul : ∀ (ζ' ξ : Prim q A) (b : (ZMod q)ˣ), ξ.1 = ζ'.1 ^ (b : ZMod q).val → e ξ = e ζ' * b`. Introduce `ζ' ξ b hb`. Apply `uniq` to reduce the goal to its premises. Rewrite using `[← he ξ, hb, map_pow, he ζ', ← pow_mul, pow_val_eq hμ]`. Use `push_cast`.

Simplify using `[ZMod.natCast_zmod_val]`. Establish `h1 : e ζ = 1`. Apply `uniq` to reduce the goal to its premises. Rewrite using `[← he ζ]`. Use `conv_lhs => rw [← pow_one (π ζ.1)]`.

Rewrite using `[pow_val_eq hμ]`. Simplify using `[ZMod.natCast_zmod_val]`. Set `f` to `Finsupp.linearCombination (ULift.{1} (ZMod q)) (fun ξ : Prim q A => (ULift.up (((e ξ) ^ i : (ZMod q)ˣ) : ZMod q) : ULift.{1} (ZMod q)))`. Establish `hker : twRel q i A ≤ LinearMap.ker f`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `x ⟨ζ', ξ, b, hb, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, f, Finsupp.linearCombination_single, hmul ζ' ξ b hb, mul_zpow, sub_eq_zero]`. Apply `ULift.ext` to reduce the goal to its premises. Simplify using `[mul_comm]`. Rewrite `h` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`.

Establish `h2` using `hker h`. Rewrite `h2` using `[LinearMap.mem_ker, map_smul]`. Establish `h3 : (ULift.up (1 : ZMod q) : ULift.{1} (ZMod q)) = 1` using `rfl`. Simplify `h2` using `[f, Finsupp.linearCombination_single, h1, h3]`.
-/
theorem key {q : ℕ} [NeZero q] {A : Type} [CommRing A] [Nontrivial A] (i : ℤ) (ζ : Prim q A)
    (c : ULift.{1} (ZMod q))
    (h : c • (Submodule.Quotient.mk (p := twRel q i A) (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))) = 0) :
    c = 0 := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  let π : A →+* A ⧸ m := Ideal.Quotient.mk m
  have hμ := prim_field π ζ
  have hex : ∀ ξ : Prim q A, ∃ u : (ZMod q)ˣ, π ξ.1 = π ζ.1 ^ (u : ZMod q).val := by
    intro ξ
    obtain ⟨j, hj, hj'⟩ := hμ.eq_pow_of_pow_eq_one (prim_field π ξ).pow_eq_one
    have cop : j.Coprime q := (hμ.pow_iff_coprime (NeZero.pos q) j).1 (hj' ▸ prim_field π ξ)
    refine ⟨ZMod.unitOfCoprime j cop, ?_⟩
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hj, hj']
  have uniq : ∀ u w : (ZMod q)ˣ, π ζ.1 ^ (u : ZMod q).val = π ζ.1 ^ (w : ZMod q).val → u = w := by
    intro u w huw
    rw [pow_val_eq hμ, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at huw
    exact Units.ext huw
  choose e he using hex
  have hmul : ∀ (ζ' ξ : Prim q A) (b : (ZMod q)ˣ), ξ.1 = ζ'.1 ^ (b : ZMod q).val → e ξ = e ζ' * b := by
    intro ζ' ξ b hb
    apply uniq
    rw [← he ξ, hb, map_pow, he ζ', ← pow_mul, pow_val_eq hμ]
    push_cast
    simp [ZMod.natCast_zmod_val]
  have h1 : e ζ = 1 := by
    apply uniq
    rw [← he ζ]
    conv_lhs => rw [← pow_one (π ζ.1)]
    rw [pow_val_eq hμ]
    simp [ZMod.natCast_zmod_val]
  let f := Finsupp.linearCombination (ULift.{1} (ZMod q))
    (fun ξ : Prim q A => (ULift.up (((e ξ) ^ i : (ZMod q)ˣ) : ZMod q) : ULift.{1} (ZMod q)))
  have hker : twRel q i A ≤ LinearMap.ker f := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ', ξ, b, hb, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, f, Finsupp.linearCombination_single,
      hmul ζ' ξ b hb, mul_zpow, sub_eq_zero]
    apply ULift.ext
    simp [mul_comm]
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  have h2 := hker h
  rw [LinearMap.mem_ker, map_smul] at h2
  have h3 : (ULift.up (1 : ZMod q) : ULift.{1} (ZMod q)) = 1 := rfl
  simpa [f, Finsupp.linearCombination_single, h1, h3] using h2

/- English proof (translation)
The claim follows from `sub_eq_zero.1 (key i ζ (x - y) (by rw [sub_smul, sub_eq_zero]; exact h))`.
-/
theorem aux {q : ℕ} [NeZero q] {A : Type} [CommRing A] [Nontrivial A] (i : ℤ) (ζ : Prim q A)
    (x y : ULift.{1} (ZMod q))
    (h : x • (Submodule.Quotient.mk (p := twRel q i A) (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))) =
      y • (Submodule.Quotient.mk (p := twRel q i A) (Finsupp.single ζ (1 : ULift.{1} (ZMod q))))) : x = y :=
  sub_eq_zero.1 (key i ζ (x - y) (by rw [sub_smul, sub_eq_zero]; exact h))

/- English proof (translation)
Introduce `q _ B _ ζ k`. Use `⟨fun {X} x y h => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hX : Nonempty X.unop.left`. Use `haveI : Nontrivial Γ(X.unop.left, ⊤) := by`. Take `⟨p⟩` from `hX`.

Conclude with `RingHom.domain_nontrivial (X.unop.left.presheaf.germ ⊤ p trivial).hom`. Establish `h0 : x • gen ζ k X.unop = y • gen ζ k X.unop` using `h`. Establish `hxy : x = y` using `aux (A := Γ(X.unop.left, ⊤)) k _ x y h0`. Substitute `hxy` using the available equality. Rewrite using `[Presheaf.equalizerSieve_self_eq_top]`.

Conclude with `GrothendieckTopology.top_mem _ _`. Use `haveI : IsEmpty X.unop.left := not_nonempty_iff.1 hX`. Rewrite using `[GrothendieckTopology.mem_over_iff]`. Use `GrothendieckTopology.superset_covering _ bot_le ?_` and prove the remaining obligations. Use `first`.

Consider the case `exact Scheme.bot_mem_grothendieckTopology _`. Consider the case `exact bot_mem_grothendieckTopology _`. Consider the case `exact AlgebraicGeometry.Scheme.bot_mem_grothendieckTopology (P := @Etale) _`.
-/
theorem LeafTwInj_of : LeafTwInj := by
  intro q _ B _ ζ k
  refine ⟨fun {X} x y h => ?_⟩
  by_cases hX : Nonempty X.unop.left
  · haveI : Nontrivial Γ(X.unop.left, ⊤) := by
      obtain ⟨p⟩ := hX
      exact RingHom.domain_nontrivial (X.unop.left.presheaf.germ ⊤ p trivial).hom
    have h0 : x • gen ζ k X.unop = y • gen ζ k X.unop := h
    have hxy : x = y := aux (A := Γ(X.unop.left, ⊤)) k _ x y h0
    subst hxy
    rw [Presheaf.equalizerSieve_self_eq_top]
    exact GrothendieckTopology.top_mem _ _
  · haveI : IsEmpty X.unop.left := not_nonempty_iff.1 hX
    rw [GrothendieckTopology.mem_over_iff]
    refine GrothendieckTopology.superset_covering _ bot_le ?_
    first
      | exact Scheme.bot_mem_grothendieckTopology _
      | exact bot_mem_grothendieckTopology _
      | exact AlgebraicGeometry.Scheme.bot_mem_grothendieckTopology (P := @Etale) _

end LateralTheory.E.LeafTwInjPf
