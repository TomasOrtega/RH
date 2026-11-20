import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.BaseChars

/- English proof (translation)
Use `haveI := Fact.mk hp`. Establish `hp1 : 0 < p - 1` using `by have := hp.two_le; omega`. Establish `hpos : 0 < p * (p - 1)` using `Nat.mul_pos hp.pos hp1`. Establish `h1 : IsPrimitiveRoot (z ^ (p - 1)) p` using `hz.pow hpos (mul_comm _ _)`. Establish `h2 : IsPrimitiveRoot (z ^ p) (p - 1)` using `hz.pow hpos rfl`.

Take `⟨u, hu⟩` from `h2.isUnit hp1.ne'`. Establish `h3 : IsPrimitiveRoot u (p - 1)` using `IsPrimitiveRoot.coe_units_iff.1 (hu ▸ h2)`. Take `⟨g, hg⟩` from `IsCyclic.exists_generator (α := (ZMod p)ˣ)`. Establish `hog : orderOf g = p - 1`. Rewrite using `[orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]`.

Establish `hou : orderOf u = p - 1` using `h3.eq_orderOf.symm`. Use `⟨AddChar.zmodChar p h1.pow_eq_one, monoidHomOfForallMemZpowers hg (g' := u) (by rw [hog, hou]), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[AddChar.zmodChar_apply, ZMod.val_one, pow_one]`. Conclude with `h1.ne_one hp.one_lt`. Rewrite using `[injective_iff_map_eq_one]`.

Introduce `x hx`. Take `⟨n, rfl⟩` from `Subgroup.mem_zpowers_iff.1 (hg x)`. Rewrite `hx` using `[map_zpow, monoidHomOfForallMemZpowers_apply_gen, ← orderOf_dvd_iff_zpow_eq_one, hou, ← hog]`. Conclude with `orderOf_dvd_iff_zpow_eq_one.1 hx`.
-/
theorem exists_chars_zmod {K : Type} [Field K] {p : ℕ} (hp : p.Prime) {z : K} (hz : IsPrimitiveRoot z (p * (p - 1))) :
    ∃ (ψ : AddChar (ZMod p) K) (om : (ZMod p)ˣ →* Kˣ), ψ 1 ≠ 1 ∧ Function.Injective om := by
  haveI := Fact.mk hp
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  have hpos : 0 < p * (p - 1) := Nat.mul_pos hp.pos hp1
  have h1 : IsPrimitiveRoot (z ^ (p - 1)) p := hz.pow hpos (mul_comm _ _)
  have h2 : IsPrimitiveRoot (z ^ p) (p - 1) := hz.pow hpos rfl
  obtain ⟨u, hu⟩ := h2.isUnit hp1.ne'
  have h3 : IsPrimitiveRoot u (p - 1) := IsPrimitiveRoot.coe_units_iff.1 (hu ▸ h2)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have hou : orderOf u = p - 1 := h3.eq_orderOf.symm
  refine ⟨AddChar.zmodChar p h1.pow_eq_one, monoidHomOfForallMemZpowers hg (g' := u) (by rw [hog, hou]), ?_, ?_⟩
  · rw [AddChar.zmodChar_apply, ZMod.val_one, pow_one]
    exact h1.ne_one hp.one_lt
  · rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
    rw [map_zpow, monoidHomOfForallMemZpowers_apply_gen, ← orderOf_dvd_iff_zpow_eq_one, hou, ← hog] at hx
    exact orderOf_dvd_iff_zpow_eq_one.1 hx

/- English proof (translation)
Use `haveI := Fact.mk hp`. Take `⟨g, hg⟩` from `IsCyclic.exists_generator (α := (ZMod p)ˣ)`. Establish `hog : orderOf g = p - 1`. Rewrite using `[orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]`. Establish `h1` using `h g`.

Rewrite `h1` using `[← map_pow, ← map_pow]`. Conclude with `pow_injOn_Iio_orderOf (x := g) (by rwa [Set.mem_Iio, hog]) (by rwa [Set.mem_Iio, hog]) (hom h1)`.
-/
theorem eq_of_pow_eq {K : Type} [Field K] {p : ℕ} (hp : p.Prime) {om : (ZMod p)ˣ →* Kˣ} (hom : Function.Injective om)
    {a b : ℕ} (ha : a < p - 1) (hb : b < p - 1) (h : ∀ x, om x ^ a = om x ^ b) : a = b := by
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have h1 := h g
  rw [← map_pow, ← map_pow] at h1
  exact pow_injOn_Iio_orderOf (x := g) (by rwa [Set.mem_Iio, hog]) (by rwa [Set.mem_Iio, hog]) (hom h1)

/- English proof (translation)
Establish `hc : Nat.card (𝓞 E ⧸ w.asIdeal) = p`. Rewrite using `[← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Use `haveI : Finite (𝓞 E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ hp.ne_zero)`. Use `letI := Fintype.ofFinite (𝓞 E ⧸ w.asIdeal)`. Conclude with `⟨(ZMod.ringEquivOfPrime _ hp (by rw [← Nat.card_eq_fintype_card, hc])).symm⟩`.
-/
theorem nonempty_equiv_zmod {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 E))
    (hw : Ideal.absNorm w.asIdeal = p) : Nonempty ((𝓞 E ⧸ w.asIdeal) ≃+* ZMod p) := by
  have hc : Nat.card (𝓞 E ⧸ w.asIdeal) = p := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ hp.ne_zero)
  letI := Fintype.ofFinite (𝓞 E ⧸ w.asIdeal)
  exact ⟨(ZMod.ringEquivOfPrime _ hp (by rw [← Nat.card_eq_fintype_card, hc])).symm⟩

/- English proof (translation)
Establish `h0 : ∀ i, ∃ (ψ : AddChar (ZMod (Pr.g i)) X.K) (om : (ZMod (Pr.g i))ˣ →* X.Kˣ), ψ 1 ≠ 1 ∧ Function.Injective om` using `fun i => by`. Take `⟨z, hz⟩` from `hz i`. Conclude with `exists_chars_zmod (hPr.g_prime i) hz`. Use `choose ψ om hψ hom using h0`. Establish `hmem : ∀ w : {w // w ∈ Pr.vGs}, ∃ i, w.1 ∈ Pr.vG i` using `fun w => by`.

Establish `h` using `w.2`. Unfold `Primes.vGs at h`. Break down `Finset.mem_union.1 h with h | h` into its components or cases. Conclude with `⟨0, h⟩`. Conclude with `⟨1, h⟩`.

Establish `hg : Function.Injective Pr.g`. Introduce `i j hij`. Use `hPr.g_ne` as an intermediate fact. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp_all`. Establish `h1 : ∀ w : {w // w ∈ Pr.vGs}, ∃ (ψw : AddChar (𝓞 X.E ⧸ w.1.asIdeal) X.K) (omw : (𝓞 X.E ⧸ w.1.asIdeal)ˣ →* X.Kˣ), ∀ i, w.1 ∈ Pr.vG i → ∃ φ : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* ZMod (Pr.g i), (∀ x, ψw x = ψ i (φ x)) ∧ ∀ (x : (𝓞 X.E ⧸ w.1.asIdeal)ˣ) (a : (ZMod (Pr.g i))ˣ), φ x = a → omw x = …` using `fun w => by`.

Take `⟨i, hi⟩` from `hmem w`. Take `⟨φ⟩` from `nonempty_equiv_zmod (hPr.g_prime i) w.1 (hPr.vG_norm i w.1 hi)`. Use `⟨(ψ i).compAddMonoidHom φ.toAddMonoidHom, (om i).comp (Units.map φ.toMonoidHom), fun i' hi' => ?_⟩` and prove the remaining obligations. Take `rfl : i = i'` from `hg ((hPr.vG_norm i w.1 hi).symm.trans (hPr.vG_norm i' w.1 hi'))`. Use `⟨φ, fun x => rfl, fun x a h => ?_⟩` and prove the remaining obligations.

Rewrite using `[MonoidHom.comp_apply]`. Use `congr 1`. Conclude with `Units.ext h`. Use `choose ψw omw hw using h1`. Use `⟨⟨ψw, fun j w => omw w ^ (2 * (j.1 + 1)), mu, eta⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩` and prove the remaining obligations.

Introduce `w h`. Take `⟨i, hi⟩` from `hmem w`. Take `⟨φ, h1, -⟩` from `hw w i hi`. Apply `hψ i` to reduce the goal to its premises. Rewrite using `[← map_one φ, ← h1]`.

Conclude with `DFunLike.congr_fun h 1`. Introduce `w j j' h`. Take `⟨i, hi⟩` from `hmem w`. Take `⟨φ, -, h2⟩` from `hw w i hi`. Establish `hj` using `j.2`.

Establish `hj'` using `j'.2`. Establish `hmi` using `hm i`. Establish `h3 : 2 * (j.1 + 1) = 2 * (j'.1 + 1)`. Use `eq_of_pow_eq (hPr.g_prime i) (hom i) (by omega) (by omega) fun a => ?_` and prove the remaining obligations. Rewrite using `[← h2 (Units.map φ.symm.toMonoidHom a) a (φ.apply_symm_apply _)]`.

Conclude with `DFunLike.congr_fun h _`. Conclude with `Fin.ext (by omega)`. Introduce `i w w' hi hi' j a x x' hx hx'`. Take `⟨φ, -, h2⟩` from `hw w i hi`. Take `⟨φ', -, h2'⟩` from `hw w' i hi'`.

Use `show omw w x ^ _ = omw w' x' ^ _`. Rewrite using `[h2 x (Units.map φ.toMonoidHom x) rfl, h2' x' (Units.map φ.toMonoidHom x)]`. Use `show φ' x' = φ x`. Rewrite using `[hx, hx', map_intCast, map_intCast]`. Introduce `i w w' hi hi' a`.

Take `⟨φ, h1, -⟩` from `hw w i hi`. Take `⟨φ', h1', -⟩` from `hw w' i hi'`. Use `show ψw w _ = ψw w' _`. Rewrite using `[h1, h1', map_intCast φ, map_intCast φ']`. Introduce `i`.

Use `⟨om i, hom i, fun w hi j a x hx => ?_⟩` and prove the remaining obligations. Use `haveI := Fact.mk (hPr.g_prime i)`. Take `⟨φ, -, h2⟩` from `hw w i hi`. Use `show omw w x ^ _ = _`. Rewrite using `[h2 x a (by rw [hx, map_natCast, ZMod.natCast_zmod_val])]`.
-/
theorem exists_chars_of_roots {X : Fields} (Pr : Primes X) (hPr : Pr.Ok) (m : ℕ) (hm : ∀ i, 2 * m < Pr.g i - 1)
    (hz : ∀ i, ∃ z : X.K, IsPrimitiveRoot z (Pr.g i * (Pr.g i - 1)))
    (mu : Fin m → HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (eta : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) :
    ∃ Ch : Chars X Pr m, Ch.Ok ∧ Ch.muVal = mu ∧ Ch.etaVal = eta := by
  classical
  have h0 : ∀ i, ∃ (ψ : AddChar (ZMod (Pr.g i)) X.K) (om : (ZMod (Pr.g i))ˣ →* X.Kˣ),
      ψ 1 ≠ 1 ∧ Function.Injective om := fun i => by
    obtain ⟨z, hz⟩ := hz i
    exact exists_chars_zmod (hPr.g_prime i) hz
  choose ψ om hψ hom using h0
  have hmem : ∀ w : {w // w ∈ Pr.vGs}, ∃ i, w.1 ∈ Pr.vG i := fun w => by
    have h := w.2
    unfold Primes.vGs at h
    rcases Finset.mem_union.1 h with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hg : Function.Injective Pr.g := by
    intro i j hij
    have := hPr.g_ne
    fin_cases i <;> fin_cases j <;> simp_all
  have h1 : ∀ w : {w // w ∈ Pr.vGs}, ∃ (ψw : AddChar (𝓞 X.E ⧸ w.1.asIdeal) X.K)
      (omw : (𝓞 X.E ⧸ w.1.asIdeal)ˣ →* X.Kˣ), ∀ i, w.1 ∈ Pr.vG i →
      ∃ φ : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* ZMod (Pr.g i), (∀ x, ψw x = ψ i (φ x)) ∧
        ∀ (x : (𝓞 X.E ⧸ w.1.asIdeal)ˣ) (a : (ZMod (Pr.g i))ˣ), φ x = a → omw x = om i a := fun w => by
    obtain ⟨i, hi⟩ := hmem w
    obtain ⟨φ⟩ := nonempty_equiv_zmod (hPr.g_prime i) w.1 (hPr.vG_norm i w.1 hi)
    refine ⟨(ψ i).compAddMonoidHom φ.toAddMonoidHom, (om i).comp (Units.map φ.toMonoidHom), fun i' hi' => ?_⟩
    obtain rfl : i = i' := hg ((hPr.vG_norm i w.1 hi).symm.trans (hPr.vG_norm i' w.1 hi'))
    refine ⟨φ, fun x => rfl, fun x a h => ?_⟩
    rw [MonoidHom.comp_apply]
    congr 1
    exact Units.ext h
  choose ψw omw hw using h1
  refine ⟨⟨ψw, fun j w => omw w ^ (2 * (j.1 + 1)), mu, eta⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
  · intro w h
    obtain ⟨i, hi⟩ := hmem w
    obtain ⟨φ, h1, -⟩ := hw w i hi
    apply hψ i
    rw [← map_one φ, ← h1]
    exact DFunLike.congr_fun h 1
  · intro w j j' h
    obtain ⟨i, hi⟩ := hmem w
    obtain ⟨φ, -, h2⟩ := hw w i hi
    have hj := j.2
    have hj' := j'.2
    have hmi := hm i
    have h3 : 2 * (j.1 + 1) = 2 * (j'.1 + 1) := by
      refine eq_of_pow_eq (hPr.g_prime i) (hom i) (by omega) (by omega) fun a => ?_
      rw [← h2 (Units.map φ.symm.toMonoidHom a) a (φ.apply_symm_apply _)]
      exact DFunLike.congr_fun h _
    exact Fin.ext (by omega)
  · intro i w w' hi hi' j a x x' hx hx'
    obtain ⟨φ, -, h2⟩ := hw w i hi
    obtain ⟨φ', -, h2'⟩ := hw w' i hi'
    show omw w x ^ _ = omw w' x' ^ _
    rw [h2 x (Units.map φ.toMonoidHom x) rfl, h2' x' (Units.map φ.toMonoidHom x)]
    show φ' x' = φ x
    rw [hx, hx', map_intCast, map_intCast]
  · intro i w w' hi hi' a
    obtain ⟨φ, h1, -⟩ := hw w i hi
    obtain ⟨φ', h1', -⟩ := hw w' i hi'
    show ψw w _ = ψw w' _
    rw [h1, h1', map_intCast φ, map_intCast φ']
  · intro i
    refine ⟨om i, hom i, fun w hi j a x hx => ?_⟩
    haveI := Fact.mk (hPr.g_prime i)
    obtain ⟨φ, -, h2⟩ := hw w i hi
    show omw w x ^ _ = _
    rw [h2 x a (by rw [hx, map_natCast, ZMod.natCast_zmod_val])]

/- English proof (translation)
Introduce `B X mu eta`. Use `exists_chars_of_roots (B.primes X) (GlobalTheory.BasePrimes.primes_ok B X).1 B.R.m (fun i => ?_) (fun i => ?_) mu eta` and prove the remaining obligations. Establish `h1` using `(B.primes_sizes X).g_big i`. Establish `h2` using `B.R.m_add_three_le_k`. Establish `h3 : 0 < B.fields.f`.

Rewrite using `[B.fields_f]`. Unfold `Ranks.f Ranks.n`. Check the signs of the components of the expression. Use `lt_of_le_of_lt ?_ h1` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities.

Establish `hp` using `B.host.g_prime i`. Apply the tactic sequence `obtain ⟨z, -, hz⟩ := B.roots_Ks (B.host.g i * (B.host.g i - 1)) (by fin_cases i <;> simp)`. Establish `hne : B.host.g i * (B.host.g i - 1) ≠ 0` using `mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)`. Use `⟨z, IsPrimitiveRoot.of_map_of_injective (f := B.embLL) ?_ B.embLL.injective⟩` and prove the remaining obligations. Rewrite using `[hz]`.

Conclude with `Complex.isPrimitiveRoot_exp _ hne`.
-/
theorem exists_chars : ∀ (B : Base) (X : PreX B.toPre) (mu : Fin B.R.m → HeightOneSpectrum (𝓞 B.host.E) → B.LLˣ)
    (eta : HeightOneSpectrum (𝓞 B.host.E) → B.LLˣ),
    ∃ Ch : Chars B.fields (B.primes X) B.R.m, Ch.Ok ∧ Ch.muVal = mu ∧ Ch.etaVal = eta := by
  intro B X mu eta
  refine exists_chars_of_roots (B.primes X) (GlobalTheory.BasePrimes.primes_ok B X).1 B.R.m (fun i => ?_) (fun i => ?_) mu eta
  · have h1 := (B.primes_sizes X).g_big i
    have h2 := B.R.m_add_three_le_k
    have h3 : 0 < B.fields.f := by
      rw [B.fields_f]
      unfold Ranks.f Ranks.n
      positivity
    refine lt_of_le_of_lt ?_ h1
    nlinarith
  · have hp := B.host.g_prime i
    obtain ⟨z, -, hz⟩ := B.roots_Ks (B.host.g i * (B.host.g i - 1)) (by fin_cases i <;> simp)
    have hne : B.host.g i * (B.host.g i - 1) ≠ 0 := mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
    refine ⟨z, IsPrimitiveRoot.of_map_of_injective (f := B.embLL) ?_ B.embLL.injective⟩
    rw [hz]
    exact Complex.isPrimitiveRoot_exp _ hne

end GlobalTheory.BaseChars
