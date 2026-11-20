import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FrobeniusLiftEmbeddingsUnit
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.ResidueChar

/- English proof (translation)
Use `Fintype.ofFinite K` as an intermediate fact. Establish `hmem : ∀ y, g y ∈ f.range` using `fun y => by`. Establish `h1 : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K) = ∏ a : K, (Polynomial.X - Polynomial.C a)`. Establish `hm : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).Monic` using `Polynomial.monic_X_pow_sub (by`. Rewrite using `[Polynomial.degree_X]`.

Conclude with `Fintype.one_lt_card)` after adjusting the coercions. Use `Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (by` as an intermediate fact. Rewrite using `[FiniteField.roots_X_pow_card_sub_X, FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card]`. Use the proof step `rfl)`. Rewrite using `[← this, FiniteField.roots_X_pow_card_sub_X]`.

Both sides reduce to the same expression. Establish `h2` using `congrArg (Polynomial.eval₂RingHom f (g y)) h1`. Rewrite `h2` using `[map_prod]`. Simplify using `only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C] at h2`. Rewrite `h2` using `[← map_pow, FiniteField.pow_card, sub_self]`.

Take `⟨a, -, ha⟩` from `Finset.prod_eq_zero_iff.1 h2.symm`. Conclude with `⟨a, (sub_eq_zero.1 ha).symm⟩`. Set `e : K ≃+* f.range` to `RingEquiv.ofBijective f.rangeRestrict ⟨f.rangeRestrict.injective, f.rangeRestrict_surjective⟩`. Set `s : K →+* K` to `e.symm.toRingHom.comp (g.codRestrict f.range hmem)`. Establish `hs : ∀ y, f (s y) = g y` using `fun y => congrArg Subtype.val (e.apply_symm_apply (g.codRestrict f.range hmem y))`.

Set `` to `ZMod.algebra K l`. Set `s' : K →ₐ[ZMod l] K` to `{ s with commutes' := fun r => DFunLike.congr_fun (Subsingleton.elim (s.comp (algebraMap (ZMod l) K)) (algebraMap (ZMod l) K)) r }`. Take `⟨j, hj⟩` from `(FiniteField.bijective_frobeniusAlgHom_pow (ZMod l) K).2 s'`. Use `⟨j, fun y => ?_⟩` and prove the remaining obligations. Establish `: s y = y ^ l ^ (j : ℕ)`.

Establish `h` using `DFunLike.congr_fun hj y`. Simplify using `only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card] at h`. Conclude with `h.symm`. Rewrite using `[← hs, this, map_pow]`.
-/
theorem exists_pow_of_finite_field {K k : Type} [Field K] [Finite K] [CommRing k] [IsDomain k]
    (l : ℕ) [Fact l.Prime] [CharP K l] (f g : K →+* k) :
    ∃ j : ℕ, ∀ y, g y = f y ^ l ^ j := by
  classical
  have := Fintype.ofFinite K
  have hmem : ∀ y, g y ∈ f.range := fun y => by
    have h1 : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K) =
        ∏ a : K, (Polynomial.X - Polynomial.C a) := by
      have hm : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).Monic :=
        Polynomial.monic_X_pow_sub (by
          rw [Polynomial.degree_X]; exact_mod_cast Fintype.one_lt_card)
      have := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (by
        rw [FiniteField.roots_X_pow_card_sub_X,
          FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card]
        rfl)
      rw [← this, FiniteField.roots_X_pow_card_sub_X]
      rfl
    have h2 := congrArg (Polynomial.eval₂RingHom f (g y)) h1
    rw [map_prod] at h2
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C] at h2
    rw [← map_pow, FiniteField.pow_card, sub_self] at h2
    obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h2.symm
    exact ⟨a, (sub_eq_zero.1 ha).symm⟩
  let e : K ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨f.rangeRestrict.injective, f.rangeRestrict_surjective⟩
  let s : K →+* K := e.symm.toRingHom.comp (g.codRestrict f.range hmem)
  have hs : ∀ y, f (s y) = g y := fun y =>
    congrArg Subtype.val (e.apply_symm_apply (g.codRestrict f.range hmem y))
  let := ZMod.algebra K l
  let s' : K →ₐ[ZMod l] K := { s with
    commutes' := fun r => DFunLike.congr_fun
      (Subsingleton.elim (s.comp (algebraMap (ZMod l) K)) (algebraMap (ZMod l) K)) r }
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod l) K).2 s'
  refine ⟨j, fun y => ?_⟩
  have : s y = y ^ l ^ (j : ℕ) := by
    have h := DFunLike.congr_fun hj y
    simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card] at h
    exact h.symm
  rw [← hs, this, map_pow]

/- English proof (translation)
Establish `hl : 1 < l` using `(Fact.out : l.Prime).one_lt`. Establish `hq : 1 < l ^ d` using `Nat.one_lt_pow (NeZero.ne d) hl`. Establish `hper : ∀ x, φ 0 x ^ l ^ d = φ 0 x` using `fun x => by`. Rewrite using `[← TeichSeq.frob_iter l φ h]`. Simplify using the standard rewrite rules.

Establish `hfin : ((φ 0).range : Set k).Finite`. Establish `hne : (Polynomial.X ^ l ^ d - Polynomial.X : Polynomial k) ≠ 0` using `(Polynomial.monic_X_pow_sub (by`. Rewrite using `[Polynomial.degree_X]`. Conclude with `hq)).ne_zero` after adjusting the coercions. Use `(Polynomial.finite_setOfPred_isRoot hne).subset ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, rfl⟩`. Simplify using `[hper]`. Establish `: Finite (φ 0).range` using `hfin`. Set `: Field (φ 0).range` to `(Finite.isField_of_domain _).toField`. Set `g' : (φ 0).range →+* k` to `(φ 0).rangeRestrict.liftOfSurjective (φ 0).rangeRestrict_surjective ⟨g, fun x hx => hg x (congrArg Subtype.val (RingHom.mem_ker.1 hx))⟩`.

Establish `hg' : ∀ x, g' ((φ 0).rangeRestrict x) = g x` using `fun x => RingHom.liftOfRightInverse_comp_apply _ _ _ _ x`. Take `⟨j, hj⟩` from `exists_pow_of_finite_field l (φ 0).range.subtype g'`. Use `⟨0 + (j : ZMod d), fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[TeichSeq.frob_iter l φ h, ← hg', hj]`. Both sides reduce to the same expression.
-/
theorem exists_eq_of_ker_le {O k : Type} [CommRing O] [CommRing k] [IsDomain k] {d : ℕ} [NeZero d]
    (l : ℕ) [Fact l.Prime] [CharP k l] (φ : ZMod d → (O →+* k))
    (h : ∀ a x, φ (a + 1) x = φ a x ^ l) (g : O →+* k) (hg : ∀ x, φ 0 x = 0 → g x = 0) :
    ∃ a, ∀ x, g x = φ a x := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hq : 1 < l ^ d := Nat.one_lt_pow (NeZero.ne d) hl
  have hper : ∀ x, φ 0 x ^ l ^ d = φ 0 x := fun x => by
    rw [← TeichSeq.frob_iter l φ h]; simp
  have hfin : ((φ 0).range : Set k).Finite := by
    have hne : (Polynomial.X ^ l ^ d - Polynomial.X : Polynomial k) ≠ 0 :=
      (Polynomial.monic_X_pow_sub (by
        rw [Polynomial.degree_X]; exact_mod_cast hq)).ne_zero
    refine (Polynomial.finite_setOfPred_isRoot hne).subset ?_
    rintro _ ⟨x, rfl⟩
    simp [hper]
  have : Finite (φ 0).range := hfin
  let : Field (φ 0).range := (Finite.isField_of_domain _).toField
  let g' : (φ 0).range →+* k :=
    (φ 0).rangeRestrict.liftOfSurjective (φ 0).rangeRestrict_surjective
      ⟨g, fun x hx => hg x (congrArg Subtype.val (RingHom.mem_ker.1 hx))⟩
  have hg' : ∀ x, g' ((φ 0).rangeRestrict x) = g x := fun x =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ x
  obtain ⟨j, hj⟩ := exists_pow_of_finite_field l (φ 0).range.subtype g'
  refine ⟨0 + (j : ZMod d), fun x => ?_⟩
  rw [TeichSeq.frob_iter l φ h, ← hg', hj]
  rfl

open TeichSeq in

/- English proof (translation)
Introduce `C _ V O _ d _ em hint hfrob ψ hψ hker`. Establish `: Fact V.l.Prime` using `⟨V.l_prime⟩`. Set `π : intRing V →+* intRing V ⧸ maxId V` to `Ideal.Quotient.mk _`. Set `e : ZMod d → (O →+* intRing V)` to `fun a => (em a).codRestrict (intRing V) (hint a)`. Set `φ : ZMod d → (O →+* intRing V ⧸ maxId V)` to `fun a => π.comp (e a)`.

Set `p : O →+* intRing V` to `ψ.codRestrict (intRing V) hψ`. Establish `hπ : ∀ u w : intRing V, π u = π w ↔ V.MM ((u : C) - w)` using `fun u w => Ideal.Quotient.eq`. Establish `hπ0 : ∀ u : intRing V, π u = 0 ↔ V.MM (u : C)` using `fun u => Ideal.Quotient.eq_zero_iff_mem`. Establish `hφ : ∀ a x, φ (a + 1) x = φ a x ^ V.l` using `fun a x => by show π (e (a + 1) x) = π (e a x) ^ V.l`. Rewrite using `[← map_pow, hπ]`.

Conclude with `hfrob a x`. Establish `: CharP (intRing V ⧸ maxId V) V.l`. Use `(CharP.charP_iff_prime_eq_zero V.l_prime).2 ?_` and prove the remaining obligations. Rewrite using `[← map_natCast π, hπ0]`. Simplify using `using mm_of_ge_one V VF.ge_l`.

Take `⟨a, ha⟩` from `exists_eq_of_ker_le V.l φ hφ (π.comp p) (fun x hx => by`. Use `(hπ0 (p x)).2 (hker x fun a => (hπ0 (e a x)).1 ?_)` and prove the remaining obligations. Use `frob_iter V.l φ hφ 0 x a.val` as an intermediate fact. Rewrite `this` using `[hx, zero_pow (pow_ne_zero _ V.l_prime.ne_zero)]`. Use `show φ a x = 0`.

Simplify using `using this)`. Conclude with `⟨a, fun x => (hπ (p x) (e a x)).1 (ha x)⟩`.
-/
theorem main : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (d : ℕ) [NeZero d] (em : ZMod d → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → ∀ ψ : O →+* C, (∀ x, V.Ge 0 (ψ x)) → (∀ x, (∀ a, V.MM (em a x)) → V.MM (ψ x)) → ∃ a, ∀ x, V.MM (ψ x - em a x) := by
  intro C _ V O _ d _ em hint hfrob ψ hψ hker
  have : Fact V.l.Prime := ⟨V.l_prime⟩
  let π : intRing V →+* intRing V ⧸ maxId V := Ideal.Quotient.mk _
  let e : ZMod d → (O →+* intRing V) := fun a => (em a).codRestrict (intRing V) (hint a)
  let φ : ZMod d → (O →+* intRing V ⧸ maxId V) := fun a => π.comp (e a)
  let p : O →+* intRing V := ψ.codRestrict (intRing V) hψ
  have hπ : ∀ u w : intRing V, π u = π w ↔ V.MM ((u : C) - w) := fun u w => Ideal.Quotient.eq
  have hπ0 : ∀ u : intRing V, π u = 0 ↔ V.MM (u : C) := fun u => Ideal.Quotient.eq_zero_iff_mem
  have hφ : ∀ a x, φ (a + 1) x = φ a x ^ V.l := fun a x => by
    show π (e (a + 1) x) = π (e a x) ^ V.l
    rw [← map_pow, hπ]
    exact hfrob a x
  have : CharP (intRing V ⧸ maxId V) V.l := by
    refine (CharP.charP_iff_prime_eq_zero V.l_prime).2 ?_
    rw [← map_natCast π, hπ0]
    simpa using mm_of_ge_one V VF.ge_l
  obtain ⟨a, ha⟩ := exists_eq_of_ker_le V.l φ hφ (π.comp p) (fun x hx => by
    refine (hπ0 (p x)).2 (hker x fun a => (hπ0 (e a x)).1 ?_)
    have := frob_iter V.l φ hφ 0 x a.val
    rw [hx, zero_pow (pow_ne_zero _ V.l_prime.ne_zero)] at this
    show φ a x = 0
    simpa using this)
  exact ⟨a, fun x => (hπ (p x) (e a x)).1 (ha x)⟩

end GlobalTheory.ResidueChar
