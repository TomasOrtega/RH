import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra WithConv

namespace GlobalTheory.ConstHT

/- English proof (translation)
The claim follows from `isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h => hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 h)⟩`.
-/
theorem isIntegrallyClosedIn_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsIntegrallyClosedIn O C :=
  isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h => hv.exists_of_le_one
    (hv.isIntegral_iff_v_le_one.1 h)⟩

/- English proof (translation)
Establish `hsq : ∀ k, (Pi.single k (1 : O) : Fin N → O) * Pi.single k 1 = Pi.single k 1` using `fun k => by`. Apply the tactic sequence `ext j; by_cases hj : j = k <;> simp [Pi.single_apply, hj]`. Establish `hid : ∀ k, f (Pi.single k 1) = 0 ∨ f (Pi.single k 1) = 1` using `fun k => IsIdempotentElem.iff_eq_zero_or_one.1 (by`. Express the relevant statement in the definitionally equal form `f _ * f _ = f _`. Rewrite using `[← map_mul, hsq])`.

Establish `hsum : ∑ k, f (Pi.single k 1) = 1`. Rewrite using `[← map_sum, ← map_one f]`. Use `congr 1`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, f (Pi.single k 1) = 1 := by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `h0 : ∑ k, f (Pi.single k 1) = 0` using `Finset.sum_eq_zero fun k _ => (hid k).resolve_right (hne k)`. Conclude with `zero_ne_one (h0.symm.trans hsum)`.

Use `⟨k, fun v => ?_⟩` and prove the remaining obligations. Establish `h1 : v * Pi.single k 1 = (v k) • (Pi.single k 1 : Fin N → O)`. Apply the tactic sequence `ext j; by_cases hj : j = k <;> simp [Pi.single_apply, hj]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_eq_apply_of_algHom {O : Type} [CommRing O] [IsDomain O] {N : ℕ}
    (f : (Fin N → O) →ₐ[O] O) : ∃ k, ∀ v, f v = v k := by
  have hsq : ∀ k, (Pi.single k (1 : O) : Fin N → O) * Pi.single k 1 = Pi.single k 1 := fun k => by
    ext j; by_cases hj : j = k <;> simp [Pi.single_apply, hj]
  have hid : ∀ k, f (Pi.single k 1) = 0 ∨ f (Pi.single k 1) = 1 := fun k =>
    IsIdempotentElem.iff_eq_zero_or_one.1 (by
      change f _ * f _ = f _
      rw [← map_mul, hsq])
  have hsum : ∑ k, f (Pi.single k 1) = 1 := by
    rw [← map_sum, ← map_one f]
    congr 1
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  obtain ⟨k, hk⟩ : ∃ k, f (Pi.single k 1) = 1 := by
    by_contra hne
    push_neg at hne
    have h0 : ∑ k, f (Pi.single k 1) = 0 :=
      Finset.sum_eq_zero fun k _ => (hid k).resolve_right (hne k)
    exact zero_ne_one (h0.symm.trans hsum)
  refine ⟨k, fun v => ?_⟩
  have h1 : v * Pi.single k 1 = (v k) • (Pi.single k 1 : Fin N → O) := by
    ext j; by_cases hj : j = k <;> simp [Pi.single_apply, hj]
  calc f v = f v * f (Pi.single k 1) := by rw [hk, mul_one]
    _ = v k := by rw [← map_mul, h1, map_smul, hk, smul_eq_mul, mul_one]

/- English proof (translation)
Take `⟨a, rfl⟩` from `AugCot.d_surjective _ w`. Take `⟨k, hk⟩` from `exists_eq_apply_of_algHom ((counitAlgHom O A).comp (e.symm : (Fin N → O) →ₐ[O] A))`. Establish `he : ∀ x, counitAlgHom O A x = e x k` using `fun x => by`. Use `hk (e x)` as an intermediate fact. Simplify using `using this`.

Use `set b := a - algebraMap O A (counitAlgHom O A a) with hbdef`. Use `set c := e.symm (1 - Pi.single k 1) with hcdef`. Establish `hb : counitAlgHom O A b = 0` using `by simp [b]`. Establish `hc : counitAlgHom O A c = 0` using `by rw [he]; simp [c]`. Establish `hbc : b = b * c` using `e.injective <| funext fun j => by`.

Rewrite using `[map_mul, Pi.mul_apply]`. Distinguish the cases in `hj : j = k`. Substitute `hj` using the available equality. Rewrite using `[← he, ← he, hb, zero_mul]`. Simplify using `[c, hj]`.

Establish `h : AugCot.d (counitAlgHom O A) b = 0`. Rewrite using `[hbc, AugCot.d_mul, hb, hc, zero_smul, zero_smul, add_zero]`. Rewrite `h` using `[hbdef, map_sub, AugCot.d_algebraMap, sub_zero]`. Then use the resulting hypothesis.
-/
theorem cot_eq_zero_of_equiv {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [Bialgebra O A]
    {N : ℕ} (e : A ≃ₐ[O] (Fin N → O)) (w : Cot O A) : w = 0 := by
  obtain ⟨a, rfl⟩ := AugCot.d_surjective _ w
  obtain ⟨k, hk⟩ := exists_eq_apply_of_algHom ((counitAlgHom O A).comp (e.symm : (Fin N → O) →ₐ[O] A))
  have he : ∀ x, counitAlgHom O A x = e x k := fun x => by
    have := hk (e x)
    simpa using this
  set b := a - algebraMap O A (counitAlgHom O A a) with hbdef
  set c := e.symm (1 - Pi.single k 1) with hcdef
  have hb : counitAlgHom O A b = 0 := by simp [b]
  have hc : counitAlgHom O A c = 0 := by rw [he]; simp [c]
  have hbc : b = b * c := e.injective <| funext fun j => by
    rw [map_mul, Pi.mul_apply]
    by_cases hj : j = k
    · subst hj
      rw [← he, ← he, hb, zero_mul]
    · simp [c, hj]
  have h : AugCot.d (counitAlgHom O A) b = 0 := by
    rw [hbc, AugCot.d_mul, hb, hc, zero_smul, zero_smul, add_zero]
  rwa [hbdef, map_sub, AugCot.d_algebraMap, sub_zero] at h

/- English proof (translation)
Take `⟨c, hc⟩` from `pow_dvd_sub_digit n a`. Establish `ha : a = (digit n a : ℤ_[p]) + (p : ℤ_[p]) ^ n * c` using `by rw [← hc]; ring`. Establish `h2 : (hodgeTate G ((p : ℤ_[p]) ^ n • (c • t))).1 n = 0`. Rewrite using `[← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul]`. Express the relevant statement in the definitionally equal form `(p ^ n) • ((hodgeTate G (c • t)).1 n) = 0`.

Rewrite using `[← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]`. Conclude with `G.dual.pow_smul_cot n _`. Establish `h3 : (hodgeTate G ((digit n a : ℤ_[p]) • t)).1 n = (digit n a : O) • (hodgeTate G t).1 n`. Rewrite using `[Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul O]`. Both sides reduce to the same expression.

Establish `e1 : a • t = (digit n a : ℤ_[p]) • t + (p : ℤ_[p]) ^ n • (c • t)`. Rewrite using `[← mul_smul, ← add_smul, ← ha]`. Rewrite using `[e1, map_add]`. Express the relevant statement in the definitionally equal form `(hodgeTate G _).1 n + (hodgeTate G _).1 n = _`. Rewrite using `[h2, add_zero, h3]`.
-/
theorem hodgeTate_smul_val {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (G : PDivGroup p O)
    (a : ℤ_[p]) (t : G.Tate) (n : ℕ) :
    (hodgeTate G (a • t)).1 n = (digit n a : O) • (hodgeTate G t).1 n := by
  obtain ⟨c, hc⟩ := pow_dvd_sub_digit n a
  have ha : a = (digit n a : ℤ_[p]) + (p : ℤ_[p]) ^ n * c := by rw [← hc]; ring
  have h2 : (hodgeTate G ((p : ℤ_[p]) ^ n • (c • t))).1 n = 0 := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul]
    change (p ^ n) • ((hodgeTate G (c • t)).1 n) = 0
    rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
    exact G.dual.pow_smul_cot n _
  have h3 : (hodgeTate G ((digit n a : ℤ_[p]) • t)).1 n = (digit n a : O) • (hodgeTate G t).1 n := by
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul O]
    rfl
  have e1 : a • t = (digit n a : ℤ_[p]) • t + (p : ℤ_[p]) ^ n • (c • t) := by
    rw [← mul_smul, ← add_smul, ← ha]
  rw [e1, map_add]
  change (hodgeTate G _).1 n + (hodgeTate G _).1 n = _
  rw [h2, add_zero, h3]

end GlobalTheory.ConstHT

namespace GlobalTheory.ConstHT
open GlobalTheory.PDivLat

/- English proof (translation)
Take `⟨e⟩` from `hG n`. Set `Lev : (Fin h → O) →ₗ[O] Cot O (G.dual.A n)` to `(LinearMap.proj n ∘ₗ G.dual.omegaSub.subtype) ∘ₗ Fintype.linearCombination O (fun i => hodgeTate G (b i))`. Establish `hLev : ∀ c, Lev c = ∑ i, c i • (hodgeTate G (b i)).1 n` using `fun c => by`. Simplify using `only [Lev, LinearMap.comp_apply, Fintype.linearCombination_apply, map_sum, map_smul]`. Both sides reduce to the same expression.

Establish `hpt : ∀ t : G.Tate, (hodgeTate G t).1 n ∈ LinearMap.range Lev` using `fun t => by`. Use `⟨fun i => (digit n (b.repr t i) : O), ?_⟩` and prove the remaining obligations. Rewrite using `[hLev]`. Use `conv_rhs => rw [← b.sum_repr t]`. Rewrite using `[map_sum]`.

Express the relevant statement in the definitionally equal form `_ = ((∑ i, hodgeTate G (b.repr t i • b i) : G.dual.omega) : ∀ k, Cot O (G.dual.A k)) n`. Rewrite using `[Submodule.coe_sum, Finset.sum_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => (hodgeTate_smul_val G _ _ n).symm`. Set `β : Module.Basis (Fin (p ^ (n * G.height))) O (G.A n)` to `(Pi.basisFun O (Fin (p ^ (n * G.height)))).map e.symm.toLinearEquiv`. Set `γ : Fin (p ^ (n * G.height)) → (G.A n →ₐ[O] O)` to `fun k => (Pi.evalAlgHom O (fun _ => O) k).comp (e : G.A n →ₐ[O] _)`.

Establish `hγ : ∀ k, β.coord k = (γ k).toLinearMap` using `fun k => LinearMap.ext fun x => by`. Simplify using `[β, γ]`. Establish `hmem : ∀ k, dUnit O (toConv (γ k).toLinearMap : CartierDual O (G.A n)) ∈ LinearMap.range Lev` using `fun k => by`. Take `⟨t, ht⟩` from `G.pt_surjective C n (γ k)`. Use `hodgeTate_val t n` as an intermediate fact.

Simplify using `only at ht`. Rewrite `this` using `[ht]`. Rewrite using `[← this]`. Conclude with `hpt t`. Take `⟨φ, rfl⟩` from `AugCot.d_surjective _ w`.

Establish `hφ : φ = ∑ k, φ.ofConv (β k) • (toConv (γ k).toLinearMap : CartierDual O (G.A n))`. Use `WithConv.ofConv_injective ?_` and prove the remaining obligations. Use `conv_lhs => rw [← β.sum_dual_apply_smul_coord φ.ofConv]`. Express the relevant statement in the definitionally equal form `_ = CartierDual.toDual O (G.A n) _`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hγ]`. Both sides reduce to the same expression. It suffices to establish `hw : AugCot.d (counitAlgHom O (G.dual.A n)) φ ∈ LinearMap.range Lev by`. Take `⟨c, hc⟩` from `hw`.

Conclude with `⟨c, (hLev c).symm.trans hc⟩`. Rewrite using `[hφ, map_sum]`. Conclude with `Submodule.sum_mem _ fun k _ => by rw [map_smul]; exact Submodule.smul_mem _ _ (hmem k)`.
-/
theorem level_span (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (O : Type) [CommRing O] [IsDomain O] [Algebra O C] [IsIntegrallyClosedIn O C]
    (G : PDivGroup p O) (hG : IsConst G) (h : ℕ) (b : Module.Basis (Fin h) ℤ_[p] G.Tate) (n : ℕ)
    (w : Cot O (G.dual.A n)) : ∃ c : Fin h → O, ∑ i, c i • (hodgeTate G (b i)).1 n = w := by
  obtain ⟨e⟩ := hG n
  let Lev : (Fin h → O) →ₗ[O] Cot O (G.dual.A n) :=
    (LinearMap.proj n ∘ₗ G.dual.omegaSub.subtype) ∘ₗ
      Fintype.linearCombination O (fun i => hodgeTate G (b i))
  have hLev : ∀ c, Lev c = ∑ i, c i • (hodgeTate G (b i)).1 n := fun c => by
    simp only [Lev, LinearMap.comp_apply, Fintype.linearCombination_apply, map_sum, map_smul]
    rfl
  have hpt : ∀ t : G.Tate, (hodgeTate G t).1 n ∈ LinearMap.range Lev := fun t => by
    refine ⟨fun i => (digit n (b.repr t i) : O), ?_⟩
    rw [hLev]
    conv_rhs => rw [← b.sum_repr t]
    rw [map_sum]
    change _ = ((∑ i, hodgeTate G (b.repr t i • b i) : G.dual.omega) : ∀ k, Cot O (G.dual.A k)) n
    rw [Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => (hodgeTate_smul_val G _ _ n).symm
  let β : Module.Basis (Fin (p ^ (n * G.height))) O (G.A n) :=
    (Pi.basisFun O (Fin (p ^ (n * G.height)))).map e.symm.toLinearEquiv
  let γ : Fin (p ^ (n * G.height)) → (G.A n →ₐ[O] O) := fun k =>
    (Pi.evalAlgHom O (fun _ => O) k).comp (e : G.A n →ₐ[O] _)
  have hγ : ∀ k, β.coord k = (γ k).toLinearMap := fun k => LinearMap.ext fun x => by
    simp [β, γ]
  have hmem : ∀ k, dUnit O (toConv (γ k).toLinearMap : CartierDual O (G.A n)) ∈
      LinearMap.range Lev := fun k => by
    obtain ⟨t, ht⟩ := G.pt_surjective C n (γ k)
    have := hodgeTate_val t n
    simp only at ht
    rw [ht] at this
    rw [← this]
    exact hpt t
  obtain ⟨φ, rfl⟩ := AugCot.d_surjective _ w
  have hφ : φ = ∑ k, φ.ofConv (β k) • (toConv (γ k).toLinearMap : CartierDual O (G.A n)) := by
    refine WithConv.ofConv_injective ?_
    conv_lhs => rw [← β.sum_dual_apply_smul_coord φ.ofConv]
    change _ = CartierDual.toDual O (G.A n) _
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hγ]
    rfl
  suffices hw : AugCot.d (counitAlgHom O (G.dual.A n)) φ ∈ LinearMap.range Lev by
    obtain ⟨c, hc⟩ := hw
    exact ⟨c, (hLev c).symm.trans hc⟩
  rw [hφ, map_sum]
  exact Submodule.sum_mem _ fun k _ => by rw [map_smul]; exact Submodule.smul_mem _ _ (hmem k)

end GlobalTheory.ConstHT

namespace GlobalTheory.ConstHT
open GlobalTheory.PDivLat

/- English proof (translation)
Take `⟨e⟩` from `hG n`. Set `β : Module.Basis (Fin (p ^ (n * G.height))) O (G.A n)` to `(Pi.basisFun O (Fin (p ^ (n * G.height)))).map e.symm.toLinearEquiv`. Set `γ : Fin (p ^ (n * G.height)) → (G.A n →ₐ[O] O)` to `fun k => (Pi.evalAlgHom O (fun _ => O) k).comp (e : G.A n →ₐ[O] _)`. Establish `hγ : ∀ k, β.coord k = (γ k).toLinearMap` using `fun k => LinearMap.ext fun x => by`. Simplify using `[β, γ]`.

Set `B : Module.Basis (Fin (p ^ (n * G.height))) O (CartierDual O (G.A n))` to `β.dualBasis.map (CartierDual.toDual O (G.A n)).symm`. Establish `hB : ∀ k, B k = toConv (γ k).toLinearMap` using `fun k => by`. Simplify using `only [B, Module.Basis.map_apply, Module.Basis.coe_dualBasis, hγ]`. Both sides reduce to the same expression. Establish `hall : ∀ x : G.A n →ₐ[O] O, ∃ k, x = γ k` using `fun x => by`.

Take `⟨k, hk⟩` from `exists_eq_apply_of_algHom (x.comp e.symm.toAlgHom)`. Conclude with `⟨k, AlgHom.ext fun a => by simpa [γ] using hk (e a)⟩`. Set `Q` to `O ⧸ Ideal.span {(p : O) ^ n}`. Set `g : ZMod (p ^ n) →+ Q` to `ZMod.lift (p ^ n) ⟨Int.castAddHom Q, by`. Express the relevant statement in the definitionally equal form `(((p ^ n : ℕ) : ℤ) : Q) = 0`.

Rewrite using `[Int.cast_natCast, Nat.cast_pow]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)⟩`. Establish `hg1 : g 1 = 1`. Rewrite using `[← Int.cast_one, ZMod.lift_coe]`. Simplify using the standard rewrite rules.

Set `f : G.Tate →+ Q` to `g.comp ((PadicInt.toZModPow n).toAddMonoidHom.comp (b.coord i).toAddMonoidHom)`. Establish `hz : ((p : ZMod (p ^ n)) ^ n) = 0` using `by rw [← Nat.cast_pow, ZMod.natCast_self]`. Establish `hf0 : ∀ u : G.Tate, f ((p : ℤ_[p]) ^ n • u) = 0` using `fun u => by`. Simplify using `only [f, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, map_smul, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, smul_eq_mul, map_mul, map_pow, map_natCast]`. Rewrite using `[hz, zero_mul, map_zero]`.

Establish `hf : ∀ t s : G.Tate, t.pt n = s.pt n → f t = f s` using `fun t s hts => by`. Establish `h1 : tateLevel G n (t - s) = 0`. Rewrite using `[map_sub, sub_eq_zero, tateLevel_apply, tateLevel_apply]`. Simplify using `only [TateOver.conv, hts]`. Take `⟨u, hu⟩` from `(TateOver.conv_eq_one_iff (t - s) n).1 (by simpa using h1)`.

Rewrite using `[← sub_eq_zero, ← map_sub, ← hu, hf0]`. Set `a : (G.A n →ₐ[O] O) → Q` to `fun x => f (Classical.choose (G.pt_surjective C n x))`. Establish `ha : ∀ t : G.Tate, a (t.pt n) = f t` using `fun t => hf _ _ (Classical.choose_spec (G.pt_surjective C n (t.pt n)))`. Set `D : CartierDual O (G.A n) →ₗ[O] Q` to `B.constr O (fun k => a (γ k))`. Establish `hDpt : ∀ x : G.A n →ₐ[O] O, D (toConv x.toLinearMap) = a x` using `fun x => by`.

Take `⟨k, rfl⟩` from `hall x`. Rewrite using `[← hB, Module.Basis.constr_basis]`. Establish `hε : ∀ x : G.A n →ₐ[O] O, counitAlgHom O (CartierDual O (G.A n)) (toConv x.toLinearMap) = 1` using `fun x => by`. Rewrite using `[Bialgebra.counitAlgHom_apply, CartierDual.counit_apply]`. Conclude with `map_one x`.

Establish `hmul : ∀ x y : G.A n →ₐ[O] O, a (toConv x * toConv y).ofConv = a x + a y` using `fun x y => by`. Take `⟨t, rfl⟩` from `G.pt_surjective C n x`. Take `⟨s, rfl⟩` from `G.pt_surjective C n y`. Express the relevant statement in the definitionally equal form `a ((t + s).pt n) = _`. Rewrite using `[ha, ha, ha, map_add]`.

Set `M : CartierDual O (G.A n) →ₗ[O] CartierDual O (G.A n) →ₗ[O] Q` to `(LinearMap.lsmul O Q).compl₁₂ (counitAlgHom O (CartierDual O (G.A n))).toLinearMap D`. Establish `key : (LinearMap.mul O (CartierDual O (G.A n))).compr₂ D = M + M.flip` using `B.ext fun k => B.ext fun l => by`. Simplify using `only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.add_apply, LinearMap.flip_apply, M, LinearMap.compl₁₂_apply, LinearMap.lsmul_apply, AlgHom.toLinearMap_apply, hB, hε, one_smul]`. Rewrite using `[← AlgHom.toLinearMap_convMul, hDpt, hDpt, hDpt, hmul, add_comm]`. Establish `hD : ∀ u v, D (u * v) = counitAlgHom O (CartierDual O (G.A n)) u • D v + counitAlgHom O (CartierDual O (G.A n)) v • D u` using `fun u v => LinearMap.congr_fun₂ key u v`.

Set `Dl` to `AugCot.lift (counitAlgHom O (CartierDual O (G.A n))) D hD`. Establish `hDl : ∀ i', Dl ((hodgeTate G (b i')).1 n) = if i' = i then 1 else 0` using `fun i' => by`. Rewrite using `[hodgeTate_val]`. Express the relevant statement in the definitionally equal form `Dl (AugCot.d _ _) = _`. Rewrite using `[AugCot.lift_d, hDpt, ha]`.

Simplify using `only [f, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply, Module.Basis.repr_self, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]`. Distinguish the cases in `hi : i' = i`. Substitute `hi` using the available equality. Rewrite using `[Finsupp.single_eq_same, map_one, hg1, if_pos rfl]`. Rewrite using `[Finsupp.single_eq_of_ne (Ne.symm hi), map_zero, map_zero, if_neg hi]`.

Establish `h2` using `congrArg Dl hc`. Rewrite `h2` using `[map_sum, map_zero]`. Simplify using `only [map_smul, hDl, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2`. Rewrite using `[← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]`. Rewrite `h2` using `[Algebra.smul_def, mul_one]`.

Conclude with `h2`.
-/
theorem level_indep (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (O : Type) [CommRing O] [IsDomain O] [Algebra O C] [IsIntegrallyClosedIn O C]
    (G : PDivGroup p O) (hG : IsConst G) (h : ℕ) (b : Module.Basis (Fin h) ℤ_[p] G.Tate) (n : ℕ)
    (c : Fin h → O) (hc : ∑ i, c i • (hodgeTate G (b i)).1 n = 0) (i : Fin h) :
    (p : O) ^ n ∣ c i := by
  obtain ⟨e⟩ := hG n
  let β : Module.Basis (Fin (p ^ (n * G.height))) O (G.A n) :=
    (Pi.basisFun O (Fin (p ^ (n * G.height)))).map e.symm.toLinearEquiv
  let γ : Fin (p ^ (n * G.height)) → (G.A n →ₐ[O] O) := fun k =>
    (Pi.evalAlgHom O (fun _ => O) k).comp (e : G.A n →ₐ[O] _)
  have hγ : ∀ k, β.coord k = (γ k).toLinearMap := fun k => LinearMap.ext fun x => by
    simp [β, γ]
  let B : Module.Basis (Fin (p ^ (n * G.height))) O (CartierDual O (G.A n)) :=
    β.dualBasis.map (CartierDual.toDual O (G.A n)).symm
  have hB : ∀ k, B k = toConv (γ k).toLinearMap := fun k => by
    simp only [B, Module.Basis.map_apply, Module.Basis.coe_dualBasis, hγ]
    rfl
  have hall : ∀ x : G.A n →ₐ[O] O, ∃ k, x = γ k := fun x => by
    obtain ⟨k, hk⟩ := exists_eq_apply_of_algHom (x.comp e.symm.toAlgHom)
    exact ⟨k, AlgHom.ext fun a => by simpa [γ] using hk (e a)⟩
  let Q := O ⧸ Ideal.span {(p : O) ^ n}
  let g : ZMod (p ^ n) →+ Q := ZMod.lift (p ^ n) ⟨Int.castAddHom Q, by
    change (((p ^ n : ℕ) : ℤ) : Q) = 0
    rw [Int.cast_natCast, Nat.cast_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)⟩
  have hg1 : g 1 = 1 := by
    rw [← Int.cast_one, ZMod.lift_coe]
    simp
  let f : G.Tate →+ Q :=
    g.comp ((PadicInt.toZModPow n).toAddMonoidHom.comp (b.coord i).toAddMonoidHom)
  have hz : ((p : ZMod (p ^ n)) ^ n) = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hf0 : ∀ u : G.Tate, f ((p : ℤ_[p]) ^ n • u) = 0 := fun u => by
    simp only [f, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, map_smul,
      RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, smul_eq_mul, map_mul, map_pow,
      map_natCast]
    rw [hz, zero_mul, map_zero]
  have hf : ∀ t s : G.Tate, t.pt n = s.pt n → f t = f s := fun t s hts => by
    have h1 : tateLevel G n (t - s) = 0 := by
      rw [map_sub, sub_eq_zero, tateLevel_apply, tateLevel_apply]
      simp only [TateOver.conv, hts]
    obtain ⟨u, hu⟩ := (TateOver.conv_eq_one_iff (t - s) n).1 (by simpa using h1)
    rw [← sub_eq_zero, ← map_sub, ← hu, hf0]
  let a : (G.A n →ₐ[O] O) → Q := fun x => f (Classical.choose (G.pt_surjective C n x))
  have ha : ∀ t : G.Tate, a (t.pt n) = f t := fun t =>
    hf _ _ (Classical.choose_spec (G.pt_surjective C n (t.pt n)))
  let D : CartierDual O (G.A n) →ₗ[O] Q := B.constr O (fun k => a (γ k))
  have hDpt : ∀ x : G.A n →ₐ[O] O, D (toConv x.toLinearMap) = a x := fun x => by
    obtain ⟨k, rfl⟩ := hall x
    rw [← hB, Module.Basis.constr_basis]
  have hε : ∀ x : G.A n →ₐ[O] O,
      counitAlgHom O (CartierDual O (G.A n)) (toConv x.toLinearMap) = 1 := fun x => by
    rw [Bialgebra.counitAlgHom_apply, CartierDual.counit_apply]
    exact map_one x
  have hmul : ∀ x y : G.A n →ₐ[O] O, a (toConv x * toConv y).ofConv = a x + a y := fun x y => by
    obtain ⟨t, rfl⟩ := G.pt_surjective C n x
    obtain ⟨s, rfl⟩ := G.pt_surjective C n y
    change a ((t + s).pt n) = _
    rw [ha, ha, ha, map_add]
  let M : CartierDual O (G.A n) →ₗ[O] CartierDual O (G.A n) →ₗ[O] Q :=
    (LinearMap.lsmul O Q).compl₁₂ (counitAlgHom O (CartierDual O (G.A n))).toLinearMap D
  have key : (LinearMap.mul O (CartierDual O (G.A n))).compr₂ D = M + M.flip :=
    B.ext fun k => B.ext fun l => by
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.add_apply,
        LinearMap.flip_apply, M, LinearMap.compl₁₂_apply, LinearMap.lsmul_apply,
        AlgHom.toLinearMap_apply, hB, hε, one_smul]
      rw [← AlgHom.toLinearMap_convMul, hDpt, hDpt, hDpt, hmul, add_comm]
  have hD : ∀ u v, D (u * v) = counitAlgHom O (CartierDual O (G.A n)) u • D v +
      counitAlgHom O (CartierDual O (G.A n)) v • D u := fun u v =>
    LinearMap.congr_fun₂ key u v
  let Dl := AugCot.lift (counitAlgHom O (CartierDual O (G.A n))) D hD
  have hDl : ∀ i', Dl ((hodgeTate G (b i')).1 n) = if i' = i then 1 else 0 := fun i' => by
    rw [hodgeTate_val]
    change Dl (AugCot.d _ _) = _
    rw [AugCot.lift_d, hDpt, ha]
    simp only [f, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply,
      Module.Basis.repr_self, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    by_cases hi : i' = i
    · subst hi; rw [Finsupp.single_eq_same, map_one, hg1, if_pos rfl]
    · rw [Finsupp.single_eq_of_ne (Ne.symm hi), map_zero, map_zero, if_neg hi]
  have h2 := congrArg Dl hc
  rw [map_sum, map_zero] at h2
  simp only [map_smul, hDl, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  rw [Algebra.smul_def, mul_one] at h2
  exact h2

end GlobalTheory.ConstHT

namespace GlobalTheory.ConstHT
open GlobalTheory.PDivLat

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ _ hv G hG`. Use `haveI := isIntegrallyClosedIn_of_integers hv`. Use `⟨⟨fun x y => Subtype.ext (funext fun n => ?_)⟩, fun h b => ?_⟩` and prove the remaining obligations. Take `⟨e⟩` from `hG n`. Rewrite using `[cot_eq_zero_of_equiv e (x.1 n), cot_eq_zero_of_equiv e (y.1 n)]`.

Use `set Φ := Fintype.linearCombination O fun i => hodgeTate G (b i) with hΦ`. Establish `hval : ∀ c n, (Φ c).1 n = ∑ i, c i • (hodgeTate G (b i)).1 n` using `fun c n => by`. Rewrite using `[hΦ, Fintype.linearCombination_apply]`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]`. Establish `hsmod : ∀ (n : ℕ) (x y : O), x ≡ y [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O O)] ↔ (p : O) ^ n ∣ x - y` using `fun n x y => by`.

Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `c hc`. Use function extensionality and compare the values at `i`.

Use `IsHausdorff.haus' (I := Ideal.span {(p : O)}) (c i) fun n => (hsmod n _ _).2 ?_` and prove the remaining obligations. Rewrite using `[sub_zero]`. Conclude with `level_indep p C O G hG h b n c (by rw [← hval, hc]; rfl) i`. Introduce `w choose c hc using fun n => level_span p C O G hG h b n (w.1 n)`. Establish `hcompat : ∀ n i, (p : O) ^ n ∣ c (n + 1) i - c n i` using `fun n => level_indep p C O G hG h b n _ (by`.

Simplify using `only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[sub_eq_zero, hc n, ← w.2 n, ← hc (n + 1), map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, (hodgeTate G (b i)).2 n])`. Establish `hL : ∀ i, ∃ L : O, ∀ n, (p : O) ^ n ∣ c n i - L` using `fun i => by`.

Take `⟨L, hL⟩` from `IsPrecomplete.prec' (I := Ideal.span {(p : O)}) (fun n => c n i) fun {m n} hmn => by`. Proceed by induction on `n, hmn using Nat.le_induction with`. Consider the case `base => exact SModEq.refl _`. Consider the case `succ n hmn ih`. Conclude with `ih.trans ((hsmod m _ _).2 (dvd_sub_comm.1 ((pow_dvd_pow _ hmn).trans (hcompat n i))))`.

Conclude with `⟨L, fun n => (hsmod n _ _).1 (hL n)⟩`. Use `choose L hL using hL`. Use `⟨L, Subtype.ext (funext fun n => ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Φ L).1 n = w.1 n`. Rewrite using `[hval, ← hc n, ← sub_eq_zero, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Take `⟨d, hd⟩` from `hL i n`. Rewrite using `[← sub_smul, show L i - c n i = -((p : O) ^ n * d) by rw [← hd]; ring, neg_smul, mul_smul, G.dual.pow_smul_cot n, neg_zero]`.
-/
theorem omega_const : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ G : PDivGroup p O, IsConst G → Subsingleton G.omega ∧ ∀ (h : ℕ) (b : Module.Basis (Fin h) ℤ_[p] G.Tate), Function.Bijective (Fintype.linearCombination O fun i => hodgeTate G (b i)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ hv G hG
  haveI := isIntegrallyClosedIn_of_integers hv
  refine ⟨⟨fun x y => Subtype.ext (funext fun n => ?_)⟩, fun h b => ?_⟩
  · obtain ⟨e⟩ := hG n
    rw [cot_eq_zero_of_equiv e (x.1 n), cot_eq_zero_of_equiv e (y.1 n)]
  set Φ := Fintype.linearCombination O fun i => hodgeTate G (b i) with hΦ
  have hval : ∀ c n, (Φ c).1 n = ∑ i, c i • (hodgeTate G (b i)).1 n := fun c n => by
    rw [hΦ, Fintype.linearCombination_apply]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  have hsmod : ∀ (n : ℕ) (x y : O),
      x ≡ y [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O O)] ↔ (p : O) ^ n ∣ x - y :=
    fun n x y => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    funext i
    refine IsHausdorff.haus' (I := Ideal.span {(p : O)}) (c i) fun n => (hsmod n _ _).2 ?_
    rw [sub_zero]
    exact level_indep p C O G hG h b n c (by rw [← hval, hc]; rfl) i
  · intro w
    choose c hc using fun n => level_span p C O G hG h b n (w.1 n)
    have hcompat : ∀ n i, (p : O) ^ n ∣ c (n + 1) i - c n i := fun n =>
      level_indep p C O G hG h b n _ (by
        simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
        rw [sub_eq_zero, hc n, ← w.2 n, ← hc (n + 1), map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, (hodgeTate G (b i)).2 n])
    have hL : ∀ i, ∃ L : O, ∀ n, (p : O) ^ n ∣ c n i - L := fun i => by
      obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : O)}) (fun n => c n i)
        fun {m n} hmn => by
          induction n, hmn using Nat.le_induction with
          | base => exact SModEq.refl _
          | succ n hmn ih =>
            exact ih.trans ((hsmod m _ _).2 (dvd_sub_comm.1
              ((pow_dvd_pow _ hmn).trans (hcompat n i))))
      exact ⟨L, fun n => (hsmod n _ _).1 (hL n)⟩
    choose L hL using hL
    refine ⟨L, Subtype.ext (funext fun n => ?_)⟩
    change (Φ L).1 n = w.1 n
    rw [hval, ← hc n, ← sub_eq_zero, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨d, hd⟩ := hL i n
    rw [← sub_smul, show L i - c n i = -((p : O) ^ n * d) by rw [← hd]; ring, neg_smul, mul_smul,
      G.dual.pow_smul_cot n, neg_zero]

end GlobalTheory.ConstHT
