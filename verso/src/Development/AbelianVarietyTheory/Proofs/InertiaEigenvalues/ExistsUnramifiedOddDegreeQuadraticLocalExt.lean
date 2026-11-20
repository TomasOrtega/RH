import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.IsPrecompleteOfBasis

noncomputable section

open GlobalTheory.UnitLemma Polynomial IsLocalRing

namespace GlobalTheory.UnitLemma.UnrExt

/- English proof (translation)
Use `letI : Algebra (ZMod p) k := ZMod.algebra k p`. Set `σ : k ≃ₐ[ZMod p] k` to `AlgEquiv.ofRingEquiv (f := s) (fun x => by`. Take `⟨n, rfl⟩` from `ZMod.natCast_zmod_surjective x`. Use the proof step `simp)`. Take `⟨⟨j, hj⟩, e⟩` from `(FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) k).2 σ`.

Establish `ho` using `FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod p) k`. Simplify using `only at e`. Establish `h2 : FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k ^ (2 * j) = 1`. Rewrite using `[mul_comm, pow_mul, e]`. Use extensionality with `x`.

Conclude with `hss x`. Establish `hdvd` using `orderOf_dvd_of_pow_eq_one h2`. Rewrite `hdvd` using `[ho]`. Establish `hj0 : j ≠ 0`. Introduce and unpack `rfl`.

Take `⟨x, hx⟩` from `hne`. Apply `hx` to reduce the goal to its premises. Establish `: σ x = x` using `by rw [← e]; simp`. Conclude with `this`. Establish `hn : Module.finrank (ZMod p) k = 2 * j`.

Take `⟨m, hm⟩` from `hdvd`. Establish `: m = 1`. Break down `m with _ | _ | m` into its components or cases. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression.

Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hm, this, mul_one]`. Establish `hc : Nat.card k = p ^ (2 * j)`. Rewrite using `[← hn, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]`. Establish `hqp : q = p ^ j`.

Rewrite `hq` using `[hc, mul_comm, pow_mul]`. Conclude with `(Nat.pow_left_injective two_ne_zero hq).symm`. Use `⟨⟨j, hqp⟩, fun x => ?_⟩` and prove the remaining obligations. Establish `h3 : σ x = (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k ^ j) x` using `by rw [e]`. Rewrite `h3` using `[AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]`.

Rewrite using `[hqp]`. Conclude with `h3`.
-/
theorem invol_eq_pow {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p] {q : ℕ}
    (hq : Nat.card k = q ^ 2) (s : k ≃+* k) (hss : ∀ x, s (s x) = x) (hne : ∃ x, s x ≠ x) :
    (∃ f, q = p ^ f) ∧ ∀ x, s x = x ^ q := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  let σ : k ≃ₐ[ZMod p] k := AlgEquiv.ofRingEquiv (f := s) (fun x => by
    obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective x
    simp)
  obtain ⟨⟨j, hj⟩, e⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) k).2 σ
  have ho := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod p) k
  simp only at e
  have h2 : FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k ^ (2 * j) = 1 := by
    rw [mul_comm, pow_mul, e]
    ext x
    exact hss x
  have hdvd := orderOf_dvd_of_pow_eq_one h2
  rw [ho] at hdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hne
    apply hx
    have : σ x = x := by rw [← e]; simp
    exact this
  have hn : Module.finrank (ZMod p) k = 2 * j := by
    obtain ⟨m, hm⟩ := hdvd
    have : m = 1 := by
      rcases m with _ | _ | m
      · omega
      · rfl
      · nlinarith
    rw [hm, this, mul_one]
  have hc : Nat.card k = p ^ (2 * j) := by
    rw [← hn, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hqp : q = p ^ j := by
    rw [hc, mul_comm, pow_mul] at hq
    exact (Nat.pow_left_injective two_ne_zero hq).symm
  refine ⟨⟨j, hqp⟩, fun x => ?_⟩
  have h3 : σ x = (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k ^ j) x := by rw [e]
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card] at h3
  rw [hqp]
  exact h3

section Hensel

variable {W k : Type} [CommRing W] [IsLocalRing W] [Field k] (v : W →+* k)
  (hker : RingHom.ker v = maximalIdeal W)
include hker

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `: x ∈ maximalIdeal W` using `h`. Rewrite `this` using `[← hker]`. Conclude with `hx this`.
-/
theorem isUnit_of_ne {x : W} (hx : v x ≠ 0) : IsUnit x := by
  by_contra h
  have : x ∈ maximalIdeal W := h
  rw [← hker] at this
  exact hx this

/- English proof (translation)
Take `⟨a₀, rfl⟩` from `hv a`. Establish `h1 : f.eval a₀ ∈ maximalIdeal W`. Rewrite using `[← hker, RingHom.mem_ker, ← ha, eval_map, eval₂_at_apply]`. Establish `h2 : v (f.derivative.eval a₀) ≠ 0`. Use `hsep.eval₂_derivative_ne_zero (RingHom.id k) (x := v a₀) (by simpa using ha)` as an intermediate fact.

Rewrite `this` using `[eval₂_id, derivative_map, eval_map, eval₂_at_apply]`. Then use the resulting hypothesis. Take `⟨w, hw, hw'⟩` from `(IsAdicComplete.henselianRing W (maximalIdeal W)).is_henselian f hf a₀ h1 ((isUnit_of_ne v hker h2).map _)`. Use `⟨w, hw, ?_⟩` and prove the remaining obligations. Rewrite `hw'` using `[← hker, RingHom.mem_ker, map_sub, sub_eq_zero]`. Conclude with `hw'`.
-/
theorem exists_root [IsAdicComplete (maximalIdeal W) W] (hv : Function.Surjective v) (f : W[X]) (hf : f.Monic)
    (hsep : (f.map v).Separable) (a : k) (ha : (f.map v).eval a = 0) : ∃ w, f.eval w = 0 ∧ v w = a := by
  obtain ⟨a₀, rfl⟩ := hv a
  have h1 : f.eval a₀ ∈ maximalIdeal W := by
    rw [← hker, RingHom.mem_ker, ← ha, eval_map, eval₂_at_apply]
  have h2 : v (f.derivative.eval a₀) ≠ 0 := by
    have := hsep.eval₂_derivative_ne_zero (RingHom.id k) (x := v a₀) (by simpa using ha)
    rwa [eval₂_id, derivative_map, eval_map, eval₂_at_apply] at this
  obtain ⟨w, hw, hw'⟩ := (IsAdicComplete.henselianRing W (maximalIdeal W)).is_henselian f hf a₀ h1
    ((isUnit_of_ne v hker h2).map _)
  refine ⟨w, hw, ?_⟩
  rw [← hker, RingHom.mem_ker, map_sub, sub_eq_zero] at hw'
  exact hw'

/- English proof (translation)
Establish `ha' : (f.map v).eval (v a) = 0` using `by rw [eval_map, eval₂_at_apply, ha, map_zero]`. Establish `h2 : v (f.derivative.eval a) ≠ 0`. Use `hsep.eval₂_derivative_ne_zero (RingHom.id k) (x := v a) (by simpa using ha')` as an intermediate fact. Rewrite `this` using `[eval₂_id, derivative_map, eval_map, eval₂_at_apply]`. Then use the resulting hypothesis. Use `IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := f) ha hb ?_ (isUnit_of_ne v hker h2)` and prove the remaining obligations.

Establish `: a - b ∈ maximalIdeal W` using `by rw [← hker, RingHom.mem_ker, map_sub, hab, sub_self]`. Conclude with `this`.
-/
theorem root_unique (f : W[X]) (hsep : (f.map v).Separable) {a b : W} (ha : f.eval a = 0) (hb : f.eval b = 0)
    (hab : v a = v b) : a = b := by
  have ha' : (f.map v).eval (v a) = 0 := by rw [eval_map, eval₂_at_apply, ha, map_zero]
  have h2 : v (f.derivative.eval a) ≠ 0 := by
    have := hsep.eval₂_derivative_ne_zero (RingHom.id k) (x := v a) (by simpa using ha')
    rwa [eval₂_id, derivative_map, eval_map, eval₂_at_apply] at this
  refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := f) ha hb ?_ (isUnit_of_ne v hker h2)
  have : a - b ∈ maximalIdeal W := by rw [← hker, RingHom.mem_ker, map_sub, hab, sub_self]
  exact this

end Hensel

open ReciprocityTheory.ChartRestriction.G.Semi in

/- English proof (translation)
Use `haveI : NeZero d := ⟨hd.pos.ne'⟩`. Set `k` to `ResidueField O`. Set `k'` to `FiniteField.Extension k p d`. Establish `hrk : Module.finrank k k' = d` using `FiniteField.finrank_extension k p d`. Establish `hcard : Nat.card k' = (q ^ d) ^ 2`.

Rewrite using `[Module.natCard_eq_pow_finrank (K := k), hrk, hq, ← pow_mul, ← pow_mul, mul_comm]`. Use `haveI : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p`. Establish `hq2 : 2 ≤ q ^ d`. Establish `h1 : 1 < Nat.card k'` using `Finite.one_lt_card`. Rewrite `h1` using `[hcard]`.

Assume the negation of the conclusion as `h`. Establish `: q ^ d = 0 ∨ q ^ d = 1` using `by omega`. Apply the tactic sequence `rcases this with h | h <;> simp [h] at h1`. Use `set N := (q ^ d) ^ 2 - 1 with hN`. Establish `hNpos : q ^ d - 1 < N`.

Establish `: q ^ d < (q ^ d) ^ 2` using `by nlinarith`. Use linear arithmetic over natural numbers and integers. Take `⟨αu, hαu⟩` from `IsCyclic.exists_ofOrder_eq_natCard (α := k'ˣ)`. Rewrite `hαu` using `[Nat.card_units, hcard, ← hN]`. Set `α : k'` to `αu`.

Establish `hα : IsPrimitiveRoot α N`. Rewrite using `[← hαu]`. Conclude with `IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.orderOf αu)`. Establish `hpowk' : ∀ y : k', y ^ ((q ^ d) ^ 2) = y` using `fun y => by haveI := Fintype.ofFinite k'`. Rewrite using `[← hcard, Nat.card_eq_fintype_card, FiniteField.pow_card]`.

Establish `hgen : ∀ y : k', y ≠ 0 → ∃ i, α ^ i = y` using `fun y hy => by haveI : NeZero N := ⟨by omega⟩`. Establish `: y ^ N = 1`. Apply `mul_left_cancel₀ hy` to reduce the goal to its premises. Rewrite using `[← pow_succ', mul_one, show N + 1 = (q ^ d) ^ 2 by omega, hpowk']`. Take `⟨i, -, hi⟩` from `hα.eq_pow_of_pow_eq_one this`.

Conclude with `⟨i, hi⟩`. Establish `hint : IsIntegral k α` using `.of_finite k α`. Establish `htop : IntermediateField.adjoin k {α} = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `y _`.

Distinguish the cases in `hy : y = 0`. Rewrite using `[hy]`. Conclude with `zero_mem _`. Take `⟨i, rfl⟩` from `hgen y hy`. Conclude with `pow_mem (IntermediateField.mem_adjoin_simple_self k α) i`.

Establish `hdeg : (minpoly k α).natDegree = d`. Rewrite using `[← IntermediateField.adjoin.finrank hint, htop, IntermediateField.finrank_top', hrk]`. Take `⟨g, hgm, hgd, hg⟩` from `Nb.exists_monic_lift (minpoly k α) (minpoly.monic hint)`. Establish `hirr : Irreducible (g.map (residue O))` using `hgm ▸ minpoly.irreducible hint`. Use `haveI := Nb.isDomain g hg hirr`.

Use `haveI := Nb.isLocal g hg hirr`. Use `haveI := Nb.dvr g hg hirr`. Use `haveI := Nb.complete g hg hirr`. Use `haveI := Nb.finite g hg`. Set `W` to `AdjoinRoot g`.

Set `u : O →+* k'` to `(algebraMap k k').comp (residue O)`. Establish `hgu : g.map u = (minpoly k α).map (algebraMap k k')` using `by rw [← hgm, Polynomial.map_map]`. Establish `hsep : (g.map u).Separable`. Rewrite using `[hgu]`. Conclude with `Separable.map (Algebra.IsSeparable.isSeparable k α)`.

Establish `hev : g.eval₂ u α = 0`. Rewrite using `[← eval_map, hgu, eval_map]`. Conclude with `minpoly.aeval k α`. Set `v : W →+* k'` to `AdjoinRoot.lift u α hev`. Establish `hvr : v (AdjoinRoot.root g) = α` using `AdjoinRoot.lift_root hev`.

Establish `hva : v.comp (AdjoinRoot.of g) = u`. Conclude with `RingHom.ext fun x => AdjoinRoot.lift_of hev`. Establish `hmax : maximalIdeal W = (maximalIdeal O).map (algebraMap O W)` using `Nb.maxEq g hg hirr`. Establish `hker : RingHom.ker v = maximalIdeal W`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top v)`. Rewrite using `[hmax, Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, AdjoinRoot.algebraMap_eq, ← RingHom.comp_apply, hva]`. Simplify using `only [u, RingHom.comp_apply]`.

Rewrite using `[(residue_eq_zero_iff x).2 hx, map_zero]`. Establish `hsurj : Function.Surjective v` using `fun y => by`. Distinguish the cases in `hy : y = 0`. Conclude with `⟨0, by rw [hy, map_zero]⟩`. Take `⟨i, rfl⟩` from `hgen y hy`.

Conclude with `⟨AdjoinRoot.root g ^ i, by rw [map_pow, hvr]⟩`. Set `e : ResidueField W ≃+* k'` to `(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)`. Set `τ : k' →+* k'` to `iterateFrobenius k' p (f * d)`. Establish `hτ : ∀ y, τ y = y ^ (q ^ d)` using `fun y => by`. Rewrite using `[hf, ← pow_mul]`.

Conclude with `iterateFrobenius_def ..`. Establish `hττ : ∀ y, τ (τ y) = y` using `fun y => by`. Rewrite using `[hτ, hτ, ← pow_mul, ← sq, hpowk']`. Establish `hτu : τ.comp u = u.comp c`. Use extensionality with `x`.

Establish `h1 : ∀ (y : k) (m : ℕ), y ^ (q ^ (2 * m + 1)) = y ^ q` using `fun y m => by haveI := Fintype.ofFinite k`. Rewrite using `[pow_succ, pow_mul, pow_mul, ← hq, Nat.card_eq_fintype_card, FiniteField.pow_card_pow]`. Take `⟨m, hm⟩` from `hd`. Simplify using `only [u, RingHom.comp_apply]`. Rewrite using `[hτ, hc, ← map_pow, show q ^ d = q ^ (2 * m + 1) from congrArg _ hm, h1]`.

Establish `hG : (g.map ((AdjoinRoot.of g).comp c)).map v = (g.map u).map τ`. Rewrite using `[Polynomial.map_map, Polynomial.map_map, ← RingHom.comp_assoc, hva, hτu]`. Take `⟨w, hw, hvw⟩` from `exists_root v hker hsurj (g.map ((AdjoinRoot.of g).comp c)) (hg.map _) (by rw [hG]; exact hsep.map) (τ α) (by rw [hG, eval_map, eval₂_at_apply, eval_map, hev, map_zero])`. Rewrite `hw` using `[eval_map]`. Set `c' : W →+* W` to `AdjoinRoot.lift _ w hw`.

Establish `hc'r : c' (AdjoinRoot.root g) = w` using `AdjoinRoot.lift_root hw`. Establish `hc'a : c'.comp (AdjoinRoot.of g) = (AdjoinRoot.of g).comp c`. Conclude with `RingHom.ext fun x => AdjoinRoot.lift_of hw`. Establish `hvc : v.comp c' = τ.comp v`. Apply `AdjoinRoot.ringHom_ext` to reduce the goal to its premises.

Rewrite using `[RingHom.comp_assoc, hc'a, ← RingHom.comp_assoc, hva, ← hτu, RingHom.comp_assoc _ v τ, hva]`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[hc'r, hvw, hvr]`. Establish `hvc' : ∀ y, v (c' y) = τ (v y)` using `fun y => RingHom.congr_fun hvc y`. Establish `hcca : (c'.comp c').comp (AdjoinRoot.of g) = AdjoinRoot.of g`.

Rewrite using `[RingHom.comp_assoc, hc'a, ← RingHom.comp_assoc, hc'a]`. Use extensionality with `x`. Simplify using `[hcc]`. Establish `hinv : c'.comp c' = RingHom.id W`. Apply `AdjoinRoot.ringHom_ext` to reduce the goal to its premises.

Rewrite using `[hcca]`. Both sides reduce to the same expression. Use `root_unique v hker (g.map (AdjoinRoot.of g)) (by rw [Polynomial.map_map, hva]; exact hsep) ?_ ?_ ?_` and prove the remaining obligations. Establish `h1` using `hom_eval₂ g (AdjoinRoot.of g) (c'.comp c') (AdjoinRoot.root g)`. Rewrite `h1` using `[AdjoinRoot.eval₂_root, map_zero, hcca]`.

Rewrite using `[eval_map]`. Conclude with `h1.symm`. Rewrite using `[eval_map]`. Conclude with `AdjoinRoot.eval₂_root g`. Conclude with `(hvc' _).trans ((congrArg τ (hvc' _)).trans (hττ _))`.

Establish `hNk : (N : k') ≠ 0` using `by haveI := Fintype.ofFinite k'`. Establish `h1 : ((N + 1 : ℕ) : k') = 0`. Rewrite using `[show N + 1 = (q ^ d) ^ 2 by omega, ← hcard, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]`. Introduce `h`. Simplify using `[h] at h1`.

Take `⟨z, hz, hvz⟩` from `exists_root v hker hsurj (X ^ N - 1) (by simpa using monic_X_pow_sub_C (1 : W) (by omega : N ≠ 0)) (by simpa using X_pow_sub_one_separable_iff.2 hNk) α (by simp [hα.pow_eq_one])`. Establish `hz1 : z ^ N = 1` using `by simpa [sub_eq_zero] using hz`. Use `⟨W, inferInstance, inferInstance, inferInstance, inferInstance, Finite.of_equiv _ e.symm.toEquiv, inferInstance, c', z, inferInstance, Nb.inj g hg hirr, fun ϖ hϖ => ?_, ?_, ?_, fun y => RingHom.congr_fun hinv y, fun x => RingHom.congr_fun hc'a x, ?_, ⟨hz1, fun l hl => hα.dvd_of_p …` and prove the remaining obligations. Rewrite using `[IsDiscreteValuationRing.irreducible_iff_uniformizer, hmax, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]`. Rewrite using `[(AdjoinRoot.powerBasis' hg).finrank, AdjoinRoot.powerBasis'_dim, hgd, hdeg]`.

Rewrite using `[Nat.card_congr e.toEquiv, hcard]`. Rewrite using `[← hker, RingHom.mem_ker, map_sub, hvc', hvz, hτ, sub_eq_zero]`. Introduce `h`. Establish `h1 : α ^ (q ^ d - 1) = 1`. Apply `mul_left_cancel₀ αu.ne_zero` to reduce the goal to its premises.

Rewrite using `[← pow_succ', mul_one, show q ^ d - 1 + 1 = q ^ d by omega]`. Conclude with `h.symm`. Use `Nat.le_of_dvd (by omega) (hα.dvd_of_pow_eq_one _ h1)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[← hvz, ← map_pow, hl, map_one]`.

Establish `key : (⊤ : Submodule O W) ≤ Subalgebra.toSubmodule (Algebra.adjoin O {z})`. Use `Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal O) Module.Finite.fg_top (maximalIdeal_le_jacobson _) fun y _ => ?_` and prove the remaining obligations. Establish `hm : ∀ t : W, v t = 0 → t ∈ (maximalIdeal O • ⊤ : Submodule O W)` using `fun t ht => by`. Rewrite using `[Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, ← hmax, ← hker]`. Conclude with `ht`.

Distinguish the cases in `hy : v y = 0`. Conclude with `Submodule.mem_sup_right (hm y hy)`. Take `⟨i, hi⟩` from `hgen _ hy`. Rewrite using `[show y = z ^ i + (y - z ^ i) by ring]`. Conclude with `Submodule.add_mem_sup (pow_mem (Algebra.self_mem_adjoin_singleton O z) i) (hm _ (by rw [map_sub, map_pow, hvz, hi, sub_self]))`.

Rewrite using `[eq_top_iff]`. Conclude with `fun y _ => key Submodule.mem_top`.
-/
theorem exists_ring (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] (p : ℕ) [Fact p.Prime] [CharP (ResidueField O) p]
    {q f d : ℕ} (hq : Nat.card (ResidueField O) = q ^ 2) (hf : q = p ^ f) (hd : Odd d) (c : O →+* O)
    (hcc : ∀ x, c (c x) = x) (hc : ∀ x, residue O (c x) = residue O x ^ q) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (_ : Finite (ResidueField W)) (_ : Algebra O W) (c' : W →+* W) (z : W),
      Module.Finite O W ∧ Function.Injective (algebraMap O W) ∧
      (∀ ϖ : O, Irreducible ϖ → Irreducible (algebraMap O W ϖ)) ∧ Module.finrank O W = d ∧
      Nat.card (ResidueField W) = (q ^ d) ^ 2 ∧ (∀ y, c' (c' y) = y) ∧
      (∀ x, c' (algebraMap O W x) = algebraMap O W (c x)) ∧ z - c' z ∉ maximalIdeal W ∧
      IsPrimitiveRoot z ((q ^ d) ^ 2 - 1) ∧ Algebra.adjoin O {z} = ⊤ := by
  haveI : NeZero d := ⟨hd.pos.ne'⟩
  let k := ResidueField O
  let k' := FiniteField.Extension k p d
  have hrk : Module.finrank k k' = d := FiniteField.finrank_extension k p d
  have hcard : Nat.card k' = (q ^ d) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := k), hrk, hq, ← pow_mul, ← pow_mul, mul_comm]
  haveI : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  have hq2 : 2 ≤ q ^ d := by
    have h1 : 1 < Nat.card k' := Finite.one_lt_card
    rw [hcard] at h1
    by_contra h
    have : q ^ d = 0 ∨ q ^ d = 1 := by omega
    rcases this with h | h <;> simp [h] at h1
  set N := (q ^ d) ^ 2 - 1 with hN
  have hNpos : q ^ d - 1 < N := by
    have : q ^ d < (q ^ d) ^ 2 := by nlinarith
    omega
  obtain ⟨αu, hαu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := k'ˣ)
  rw [Nat.card_units, hcard, ← hN] at hαu
  let α : k' := αu
  have hα : IsPrimitiveRoot α N := by
    rw [← hαu]; exact IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.orderOf αu)
  have hpowk' : ∀ y : k', y ^ ((q ^ d) ^ 2) = y := fun y => by
    haveI := Fintype.ofFinite k'
    rw [← hcard, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hgen : ∀ y : k', y ≠ 0 → ∃ i, α ^ i = y := fun y hy => by
    haveI : NeZero N := ⟨by omega⟩
    have : y ^ N = 1 := by
      apply mul_left_cancel₀ hy
      rw [← pow_succ', mul_one, show N + 1 = (q ^ d) ^ 2 by omega, hpowk']
    obtain ⟨i, -, hi⟩ := hα.eq_pow_of_pow_eq_one this
    exact ⟨i, hi⟩
  have hint : IsIntegral k α := .of_finite k α
  have htop : IntermediateField.adjoin k {α} = ⊤ := by
    rw [eq_top_iff]
    intro y _
    by_cases hy : y = 0
    · rw [hy]; exact zero_mem _
    · obtain ⟨i, rfl⟩ := hgen y hy
      exact pow_mem (IntermediateField.mem_adjoin_simple_self k α) i
  have hdeg : (minpoly k α).natDegree = d := by
    rw [← IntermediateField.adjoin.finrank hint, htop, IntermediateField.finrank_top', hrk]
  obtain ⟨g, hgm, hgd, hg⟩ := Nb.exists_monic_lift (minpoly k α) (minpoly.monic hint)
  have hirr : Irreducible (g.map (residue O)) := hgm ▸ minpoly.irreducible hint
  haveI := Nb.isDomain g hg hirr
  haveI := Nb.isLocal g hg hirr
  haveI := Nb.dvr g hg hirr
  haveI := Nb.complete g hg hirr
  haveI := Nb.finite g hg
  let W := AdjoinRoot g
  let u : O →+* k' := (algebraMap k k').comp (residue O)
  have hgu : g.map u = (minpoly k α).map (algebraMap k k') := by rw [← hgm, Polynomial.map_map]
  have hsep : (g.map u).Separable := by
    rw [hgu]; exact Separable.map (Algebra.IsSeparable.isSeparable k α)
  have hev : g.eval₂ u α = 0 := by
    rw [← eval_map, hgu, eval_map]; exact minpoly.aeval k α
  let v : W →+* k' := AdjoinRoot.lift u α hev
  have hvr : v (AdjoinRoot.root g) = α := AdjoinRoot.lift_root hev
  have hva : v.comp (AdjoinRoot.of g) = u := by
    exact RingHom.ext fun x => AdjoinRoot.lift_of hev
  have hmax : maximalIdeal W = (maximalIdeal O).map (algebraMap O W) := Nb.maxEq g hg hirr
  have hker : RingHom.ker v = maximalIdeal W := by
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top v)
    · rw [hmax, Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker, AdjoinRoot.algebraMap_eq, ← RingHom.comp_apply, hva]
      simp only [u, RingHom.comp_apply]
      rw [(residue_eq_zero_iff x).2 hx, map_zero]
  have hsurj : Function.Surjective v := fun y => by
    by_cases hy : y = 0
    · exact ⟨0, by rw [hy, map_zero]⟩
    · obtain ⟨i, rfl⟩ := hgen y hy
      exact ⟨AdjoinRoot.root g ^ i, by rw [map_pow, hvr]⟩
  let e : ResidueField W ≃+* k' :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  let τ : k' →+* k' := iterateFrobenius k' p (f * d)
  have hτ : ∀ y, τ y = y ^ (q ^ d) := fun y => by
    rw [hf, ← pow_mul]; exact iterateFrobenius_def ..
  have hττ : ∀ y, τ (τ y) = y := fun y => by
    rw [hτ, hτ, ← pow_mul, ← sq, hpowk']
  have hτu : τ.comp u = u.comp c := by
    ext x
    have h1 : ∀ (y : k) (m : ℕ), y ^ (q ^ (2 * m + 1)) = y ^ q := fun y m => by
      haveI := Fintype.ofFinite k
      rw [pow_succ, pow_mul, pow_mul, ← hq, Nat.card_eq_fintype_card, FiniteField.pow_card_pow]
    obtain ⟨m, hm⟩ := hd
    simp only [u, RingHom.comp_apply]
    rw [hτ, hc, ← map_pow, show q ^ d = q ^ (2 * m + 1) from congrArg _ hm, h1]
  have hG : (g.map ((AdjoinRoot.of g).comp c)).map v = (g.map u).map τ := by
    rw [Polynomial.map_map, Polynomial.map_map, ← RingHom.comp_assoc, hva, hτu]
  obtain ⟨w, hw, hvw⟩ := exists_root v hker hsurj (g.map ((AdjoinRoot.of g).comp c)) (hg.map _)
    (by rw [hG]; exact hsep.map) (τ α) (by rw [hG, eval_map, eval₂_at_apply, eval_map, hev, map_zero])
  rw [eval_map] at hw
  let c' : W →+* W := AdjoinRoot.lift _ w hw
  have hc'r : c' (AdjoinRoot.root g) = w := AdjoinRoot.lift_root hw
  have hc'a : c'.comp (AdjoinRoot.of g) = (AdjoinRoot.of g).comp c := by
    exact RingHom.ext fun x => AdjoinRoot.lift_of hw
  have hvc : v.comp c' = τ.comp v := by
    apply AdjoinRoot.ringHom_ext
    · rw [RingHom.comp_assoc, hc'a, ← RingHom.comp_assoc, hva, ← hτu, RingHom.comp_assoc _ v τ, hva]
    · simp only [RingHom.comp_apply]
      rw [hc'r, hvw, hvr]
  have hvc' : ∀ y, v (c' y) = τ (v y) := fun y => RingHom.congr_fun hvc y
  have hcca : (c'.comp c').comp (AdjoinRoot.of g) = AdjoinRoot.of g := by
    rw [RingHom.comp_assoc, hc'a, ← RingHom.comp_assoc, hc'a]
    ext x; simp [hcc]
  have hinv : c'.comp c' = RingHom.id W := by
    apply AdjoinRoot.ringHom_ext
    · rw [hcca]; rfl
    · refine root_unique v hker (g.map (AdjoinRoot.of g)) (by rw [Polynomial.map_map, hva]; exact hsep) ?_ ?_ ?_
      · have h1 := hom_eval₂ g (AdjoinRoot.of g) (c'.comp c') (AdjoinRoot.root g)
        rw [AdjoinRoot.eval₂_root, map_zero, hcca] at h1
        rw [eval_map]; exact h1.symm
      · rw [eval_map]; exact AdjoinRoot.eval₂_root g
      · exact (hvc' _).trans ((congrArg τ (hvc' _)).trans (hττ _))
  have hNk : (N : k') ≠ 0 := by
    haveI := Fintype.ofFinite k'
    have h1 : ((N + 1 : ℕ) : k') = 0 := by
      rw [show N + 1 = (q ^ d) ^ 2 by omega, ← hcard, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]
    intro h
    simp [h] at h1
  obtain ⟨z, hz, hvz⟩ := exists_root v hker hsurj (X ^ N - 1) (by simpa using monic_X_pow_sub_C (1 : W) (by omega : N ≠ 0))
    (by simpa using X_pow_sub_one_separable_iff.2 hNk) α (by simp [hα.pow_eq_one])
  have hz1 : z ^ N = 1 := by simpa [sub_eq_zero] using hz
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, Finite.of_equiv _ e.symm.toEquiv,
    inferInstance, c', z, inferInstance, Nb.inj g hg hirr, fun ϖ hϖ => ?_, ?_, ?_, fun y => RingHom.congr_fun hinv y,
    fun x => RingHom.congr_fun hc'a x, ?_, ⟨hz1, fun l hl => hα.dvd_of_pow_eq_one l ?_⟩, ?_⟩
  · rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, hmax, hϖ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]
  · rw [(AdjoinRoot.powerBasis' hg).finrank, AdjoinRoot.powerBasis'_dim, hgd, hdeg]
  · rw [Nat.card_congr e.toEquiv, hcard]
  · rw [← hker, RingHom.mem_ker, map_sub, hvc', hvz, hτ, sub_eq_zero]
    intro h
    have h1 : α ^ (q ^ d - 1) = 1 := by
      apply mul_left_cancel₀ αu.ne_zero
      rw [← pow_succ', mul_one, show q ^ d - 1 + 1 = q ^ d by omega]
      exact h.symm
    have := Nat.le_of_dvd (by omega) (hα.dvd_of_pow_eq_one _ h1)
    omega
  · rw [← hvz, ← map_pow, hl, map_one]
  · have key : (⊤ : Submodule O W) ≤ Subalgebra.toSubmodule (Algebra.adjoin O {z}) := by
      refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal O) Module.Finite.fg_top
        (maximalIdeal_le_jacobson _) fun y _ => ?_
      have hm : ∀ t : W, v t = 0 → t ∈ (maximalIdeal O • ⊤ : Submodule O W) := fun t ht => by
        rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, ← hmax, ← hker]
        exact ht
      by_cases hy : v y = 0
      · exact Submodule.mem_sup_right (hm y hy)
      · obtain ⟨i, hi⟩ := hgen _ hy
        rw [show y = z ^ i + (y - z ^ i) by ring]
        exact Submodule.add_mem_sup (pow_mem (Algebra.self_mem_adjoin_singleton O z) i)
          (hm _ (by rw [map_sub, map_pow, hvz, hi, sub_self]))
    rw [eq_top_iff]
    exact fun y _ => key Submodule.mem_top

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `h1 : ∀ a : O, (IsDiscreteValuationRing.maximalIdeal W).valuation L (φ (algebraMap O E a)) = (IsDiscreteValuationRing.maximalIdeal O).valuation E (algebraMap O E a)` using `fun a => by`. Rewrite using `[hφ, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]`. Distinguish the cases in `ha : a = 0`. Simplify using `[ha]`.

Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ`. Establish `e1` using `IsDedekindDomain.HeightOneSpectrum.intValuation_singleton (IsDiscreteValuationRing.maximalIdeal O) hϖ.ne_zero hϖ.maximalIdeal_eq`. Establish `e2` using `IsDedekindDomain.HeightOneSpectrum.intValuation_singleton (IsDiscreteValuationRing.maximalIdeal W) (hj ϖ hϖ).ne_zero (hj ϖ hϖ).maximalIdeal_eq`. Establish `e3 : (IsDiscreteValuationRing.maximalIdeal O).intValuation (u : O) = 1` using `IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 fun h => h u.isUnit`. Establish `e4 : (IsDiscreteValuationRing.maximalIdeal W).intValuation (j u) = 1` using `IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 fun h => h (u.isUnit.map j)`.

Simplify using `only [map_mul, map_pow, e1, e2, e3, e4]`. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := O) x`. Unfold `val`. Rewrite using `[map_div₀, map_div₀, map_div₀, h1, h1]`.
-/
theorem val_map {O W E L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field E] [Field L] [Algebra O E] [IsFractionRing O E] [Algebra W L]
    [IsFractionRing W L] (j : O →+* W) (hj : ∀ ϖ : O, Irreducible ϖ → Irreducible (j ϖ)) (φ : E →+* L)
    (hφ : ∀ x, φ (algebraMap O E x) = algebraMap W L (j x)) (x : E) : val W (φ x) = val O x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h1 : ∀ a : O, (IsDiscreteValuationRing.maximalIdeal W).valuation L (φ (algebraMap O E a)) =
      (IsDiscreteValuationRing.maximalIdeal O).valuation E (algebraMap O E a) := fun a => by
    rw [hφ, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    by_cases ha : a = 0
    · simp [ha]
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    have e1 := IsDedekindDomain.HeightOneSpectrum.intValuation_singleton
      (IsDiscreteValuationRing.maximalIdeal O) hϖ.ne_zero hϖ.maximalIdeal_eq
    have e2 := IsDedekindDomain.HeightOneSpectrum.intValuation_singleton
      (IsDiscreteValuationRing.maximalIdeal W) (hj ϖ hϖ).ne_zero (hj ϖ hϖ).maximalIdeal_eq
    have e3 : (IsDiscreteValuationRing.maximalIdeal O).intValuation (u : O) = 1 :=
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 fun h => h u.isUnit
    have e4 : (IsDiscreteValuationRing.maximalIdeal W).intValuation (j u) = 1 :=
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 fun h => h (u.isUnit.map j)
    simp only [map_mul, map_pow, e1, e2, e3, e4]
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := O) x
  unfold val
  rw [map_div₀, map_div₀, map_div₀, h1, h1]

/- English proof (translation)
Introduce `K d hd`. Use `choose c0 hc0 using K.c_int`. Establish `hi` using `IsFractionRing.injective K.O K.E`. Set `c : K.O →+* K.O` to `{ toFun := c0 map_one' := hi (by rw [← hc0]; simp) map_mul' := fun x y => hi (by rw [map_mul, ← hc0, ← hc0, ← hc0]; simp) map_zero' := hi (by rw [← hc0]; simp) map_add' := fun x y => hi (by rw [map_add, ← hc0, ← hc0, ← hc0]; simp) }`. Establish `hc : ∀ x, K.c (algebraMap K.O K.E x) = algebraMap K.O K.E (c x)` using `hc0`.

Establish `hcc : ∀ x, c (c x) = x` using `fun x => hi (by rw [← hc, ← hc, K.c_c])`. Set `ce : K.O ≃+* K.O` to `RingEquiv.ofRingHom c c (RingHom.ext hcc) (RingHom.ext hcc)`. Set `s` to `ResidueField.mapEquiv ce`. Establish `hs : ∀ x, s (residue K.O x) = residue K.O (c x)` using `fun x => rfl`. Take `⟨p, hp⟩` from `CharP.exists (ResidueField K.O)`.

Use `haveI : Fact p.Prime := ⟨CharP.char_is_prime (ResidueField K.O) p⟩`. Take `⟨⟨f, hf⟩, hsq⟩` from `invol_eq_pow p K.card_res s (fun x => by`. Take `⟨x, rfl⟩` from `residue_surjective x`. Rewrite using `[hs, hs, hcc]) (by`. Take `⟨x, y, hxy, hn⟩` from `K.c_res`.

Use `⟨residue K.O x, fun h => hn ?_⟩` and prove the remaining obligations. Rewrite `h` using `[hs]`. Rewrite using `[← residue_eq_zero_iff, map_sub, ← hi ((hc x).symm.trans hxy), h, sub_self])`. Take `⟨W, _, _, _, _, _, _, c', z, hfin, hinj, hirr, hrk, hcard, hinv, hca, hres, hz, hadj⟩` from `exists_ring K.O p K.card_res hf hd c hcc (fun x => by rw [← hs, hsq])`. Set `L` to `FractionRing W`.

Establish `hiW` using `IsFractionRing.injective W L`. Establish `hj : Function.Injective ((algebraMap W L).comp (algebraMap K.O W))` using `hiW.comp hinj`. Set `φ : K.E →+* L` to `IsFractionRing.lift hj`. Establish `hφ : ∀ x, φ (algebraMap K.O K.E x) = algebraMap W L (algebraMap K.O W x)` using `IsFractionRing.lift_algebraMap hj`. Use `haveI : CharZero L := charZero_of_injective_ringHom φ.injective`.

Set `ce' : W ≃+* W` to `RingEquiv.ofRingHom c' c' (RingHom.ext hinv) (RingHom.ext hinv)`. Set `cL : L ≃+* L` to `IsFractionRing.ringEquivOfRingEquiv ce'`. Establish `hcL : ∀ y, cL (algebraMap W L y) = algebraMap W L (c' y)` using `fun y => IsFractionRing.ringEquivOfRingEquiv_algebraMap ce' y`. Use `letI : Algebra K.E L := φ.toAlgebra`. Use `haveI : IsScalarTower K.O K.E L := IsScalarTower.of_algebraMap_eq fun x => by`.

Rewrite using `[IsScalarTower.algebraMap_apply K.O W L]`. Conclude with `(hφ x).symm`. Use `⟨{ O := W, E := L, c := cL c_c := fun x => ?_ c_int := fun x => ⟨c' x, hcL x⟩ c_res := ⟨z, c' z, hcL z, hres⟩ q := K.q ^ d card_res := hcard }, φ, rfl, fun x => ?_, val_map (algebraMap K.O W) hirr φ hφ, fun h => ?_, ?_, algebraMap W L z, hz.map_of_injective hiW, ?_⟩` and prove the remaining obligations. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := W) x`. Simplify using `only [map_div₀, hcL, hinv]`.

Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := K.O) x`. Simplify using `only [map_div₀, hc, hφ, hcL, hca]`. Use `IsUnit.map (algebraMap K.O W) h` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Conclude with `(IsFractionRing.finrank_eq K.O K.E W L).trans hrk`.

Establish `hint : IsIntegral K.E (algebraMap W L z)` using `((IsIntegral.of_finite K.O z).map (IsScalarTower.toAlgHom K.O W L)).tower_top`. Establish `hmem : ∀ y : W, algebraMap W L y ∈ IntermediateField.adjoin K.E {algebraMap W L z}` using `fun y => by`. Establish `hy : y ∈ Algebra.adjoin K.O {z}` using `hadj ▸ Algebra.mem_top`. Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem x hx`.

Take `rfl : x = z` from `hx`. Conclude with `IntermediateField.mem_adjoin_simple_self _ _`. Consider the case `algebraMap r => rw [← hφ]`. Conclude with `IntermediateField.algebraMap_mem _ _`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `mul_mem hx hy`. Use `show Algebra.adjoin K.E {algebraMap W L z} = ⊤`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, eq_top_iff]`.

Introduce `x _`. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := W) x`. Conclude with `IntermediateField.div_mem _ (hmem a) (hmem b)`.
-/
theorem exists_unramified_ext : ∀ (K : UQ) (d : ℕ), Odd d → ∃ (K' : UQ) (φ : K.E →+* K'.E), K'.q = K.q ^ d ∧ (∀ x, φ (K.c x) = K'.c (φ x)) ∧ (∀ x, val K'.O (φ x) = val K.O x) ∧ (K.Odd → K'.Odd) ∧ @Module.finrank K.E K'.E _ _ (φ.toAlgebra).toModule = d ∧ ∃ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) ∧ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤ := by
  intro K d hd
  choose c0 hc0 using K.c_int
  have hi := IsFractionRing.injective K.O K.E
  let c : K.O →+* K.O :=
    { toFun := c0
      map_one' := hi (by rw [← hc0]; simp)
      map_mul' := fun x y => hi (by rw [map_mul, ← hc0, ← hc0, ← hc0]; simp)
      map_zero' := hi (by rw [← hc0]; simp)
      map_add' := fun x y => hi (by rw [map_add, ← hc0, ← hc0, ← hc0]; simp) }
  have hc : ∀ x, K.c (algebraMap K.O K.E x) = algebraMap K.O K.E (c x) := hc0
  have hcc : ∀ x, c (c x) = x := fun x => hi (by rw [← hc, ← hc, K.c_c])
  let ce : K.O ≃+* K.O := RingEquiv.ofRingHom c c (RingHom.ext hcc) (RingHom.ext hcc)
  let s := ResidueField.mapEquiv ce
  have hs : ∀ x, s (residue K.O x) = residue K.O (c x) := fun x => rfl
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField K.O)
  haveI : Fact p.Prime := ⟨CharP.char_is_prime (ResidueField K.O) p⟩
  obtain ⟨⟨f, hf⟩, hsq⟩ := invol_eq_pow p K.card_res s (fun x => by
    obtain ⟨x, rfl⟩ := residue_surjective x
    rw [hs, hs, hcc]) (by
    obtain ⟨x, y, hxy, hn⟩ := K.c_res
    refine ⟨residue K.O x, fun h => hn ?_⟩
    rw [hs] at h
    rw [← residue_eq_zero_iff, map_sub, ← hi ((hc x).symm.trans hxy), h, sub_self])
  obtain ⟨W, _, _, _, _, _, _, c', z, hfin, hinj, hirr, hrk, hcard, hinv, hca, hres, hz, hadj⟩ :=
    exists_ring K.O p K.card_res hf hd c hcc (fun x => by rw [← hs, hsq])
  let L := FractionRing W
  have hiW := IsFractionRing.injective W L
  have hj : Function.Injective ((algebraMap W L).comp (algebraMap K.O W)) := hiW.comp hinj
  let φ : K.E →+* L := IsFractionRing.lift hj
  have hφ : ∀ x, φ (algebraMap K.O K.E x) = algebraMap W L (algebraMap K.O W x) :=
    IsFractionRing.lift_algebraMap hj
  haveI : CharZero L := charZero_of_injective_ringHom φ.injective
  let ce' : W ≃+* W := RingEquiv.ofRingHom c' c' (RingHom.ext hinv) (RingHom.ext hinv)
  let cL : L ≃+* L := IsFractionRing.ringEquivOfRingEquiv ce'
  have hcL : ∀ y, cL (algebraMap W L y) = algebraMap W L (c' y) := fun y =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap ce' y
  letI : Algebra K.E L := φ.toAlgebra
  haveI : IsScalarTower K.O K.E L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply K.O W L]; exact (hφ x).symm
  refine ⟨{ O := W, E := L, c := cL
            c_c := fun x => ?_
            c_int := fun x => ⟨c' x, hcL x⟩
            c_res := ⟨z, c' z, hcL z, hres⟩
            q := K.q ^ d
            card_res := hcard }, φ, rfl, fun x => ?_, val_map (algebraMap K.O W) hirr φ hφ, fun h => ?_, ?_,
    algebraMap W L z, hz.map_of_injective hiW, ?_⟩
  · obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W) x
    simp only [map_div₀, hcL, hinv]
  · obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := K.O) x
    simp only [map_div₀, hc, hφ, hcL, hca]
  · have := IsUnit.map (algebraMap K.O W) h
    rwa [map_ofNat] at this
  · exact (IsFractionRing.finrank_eq K.O K.E W L).trans hrk
  · have hint : IsIntegral K.E (algebraMap W L z) :=
      ((IsIntegral.of_finite K.O z).map (IsScalarTower.toAlgHom K.O W L)).tower_top
    have hmem : ∀ y : W, algebraMap W L y ∈ IntermediateField.adjoin K.E {algebraMap W L z} := fun y => by
      have hy : y ∈ Algebra.adjoin K.O {z} := hadj ▸ Algebra.mem_top
      induction hy using Algebra.adjoin_induction with
      | mem x hx =>
        obtain rfl : x = z := hx
        exact IntermediateField.mem_adjoin_simple_self _ _
      | algebraMap r => rw [← hφ]; exact IntermediateField.algebraMap_mem _ _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    show Algebra.adjoin K.E {algebraMap W L z} = ⊤
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, eq_top_iff]
    intro x _
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W) x
    exact IntermediateField.div_mem _ (hmem a) (hmem b)

end GlobalTheory.UnitLemma.UnrExt
