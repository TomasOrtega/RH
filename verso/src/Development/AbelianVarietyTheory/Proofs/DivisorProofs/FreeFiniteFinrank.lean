import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TateFree

open GlobalTheory.PDiv

variable {M : Type} [CommGroup M] {l : ℕ} [Fact l.Prime] {r : ℕ}

/- English proof (translation)
Set `h : Tate l M →+ Additive M` to `{ toFun := fun t => Additive.ofMul (t.lev n), map_zero' := rfl, map_add' := fun _ _ => rfl }`. Use `congrArg Additive.toMul (map_sum h f s)` as an intermediate fact. Rewrite `this` using `[toMul_sum]`. Conclude with `this`.
-/
theorem lev_sum {I : Type} (s : Finset I) (f : I → Tate l M) (n : ℕ) :
    (∑ i ∈ s, f i).lev n = ∏ i ∈ s, (f i).lev n := by
  let h : Tate l M →+ Additive M :=
    { toFun := fun t => Additive.ofMul (t.lev n), map_zero' := rfl, map_add' := fun _ _ => rfl }
  have := congrArg Additive.toMul (map_sum h f s)
  rw [toMul_sum] at this
  exact this

/- English proof (translation)
Rewrite using `[← zpow_natCast, ← zpow_natCast a m, ← zpow_mul, ← zpow_mul, mul_comm]`.
-/
theorem zpow_pow_comm' (a : M) (k : ℤ) (m : ℕ) : (a ^ k) ^ m = (a ^ m) ^ k := by
  rw [← zpow_natCast, ← zpow_natCast a m, ← zpow_mul, ← zpow_mul, mul_comm]

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Set `K : ℕ → Subgroup M` to `fun n => (powMonoidHom (l ^ n) : M →* M).ker`. Establish `hmem : ∀ n (y : M), y ∈ K n ↔ y ^ l ^ n = 1` using `fun n y => by`. Simplify using `[K, MonoidHom.mem_ker, powMonoidHom_apply]`. Establish `hK : ∀ n, Nat.card (K n) = l ^ (r * n)` using `fun n => (Nat.card_congr (Equiv.subtypeEquivRight fun y => hmem n y)).trans (hc n)`.

Establish `hfin : ∀ n, Finite (K n)` using `fun n => Nat.finite_of_card_ne_zero (by rw [hK n]; exact pow_ne_zero _ hp.ne_zero)`. Set `φ : K (n + 1) →* M` to `(powMonoidHom l).comp (K (n + 1)).subtype`. Establish `hφ : ∀ y : K (n + 1), φ y = (y : M) ^ l` using `fun y => rfl`. Establish `hrange : φ.range ≤ K n`. Introduce and unpack `_ ⟨y, rfl⟩`.

Rewrite using `[hmem, hφ, ← pow_mul, ← pow_succ']`. Conclude with `(hmem _ _).1 y.2`. Establish `h1 : ∀ z : M, z ^ l = 1 → z ^ l ^ (n + 1) = 1` using `fun z h => by`. Rewrite using `[pow_succ', pow_mul, h, one_pow]`. Establish `hker : Nat.card φ.ker = l ^ (r * 1)`.

Rewrite using `[← hc 1]`. Use `Nat.card_congr { toFun := fun z => ⟨z.1.1, by rw [pow_one, ← hφ]; exact MonoidHom.mem_ker.1 z.2⟩ invFun := fun z => ⟨⟨z.1, (hmem _ _).2 (h1 _ (by simpa using z.2))⟩, MonoidHom.mem_ker.2 (by rw [hφ]; simpa using z.2)⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }` and prove the remaining obligations. Establish `hcard : Nat.card φ.range = l ^ (r * n)`. Establish `h` using `Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker`. Rewrite `h` using `[Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker, hK]`.

Use `Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos (r * 1)) ?_` and prove the remaining obligations. Rewrite using `[← h, ← pow_add]`. Put the polynomial expressions in normal form. Use `haveI := hfin n`. Establish `heq : φ.range = K n` using `Subgroup.eq_of_le_of_card_ge hrange (by rw [hcard, hK])`.

Take `⟨y, hy⟩ : x ∈ φ.range` from `heq ▸ (hmem n x).2 hx`. Conclude with `⟨y.1, (hmem _ _).1 y.2, hy⟩`.
-/
theorem exists_pow_eq (hc : ∀ n : ℕ, Nat.card {x : M // x ^ (l ^ n) = 1} = l ^ (r * n)) (n : ℕ)
    (x : M) (hx : x ^ l ^ n = 1) : ∃ y : M, y ^ l ^ (n + 1) = 1 ∧ y ^ l = x := by
  have hp : l.Prime := Fact.out
  let K : ℕ → Subgroup M := fun n => (powMonoidHom (l ^ n) : M →* M).ker
  have hmem : ∀ n (y : M), y ∈ K n ↔ y ^ l ^ n = 1 := fun n y => by
    simp [K, MonoidHom.mem_ker, powMonoidHom_apply]
  have hK : ∀ n, Nat.card (K n) = l ^ (r * n) := fun n =>
    (Nat.card_congr (Equiv.subtypeEquivRight fun y => hmem n y)).trans (hc n)
  have hfin : ∀ n, Finite (K n) := fun n =>
    Nat.finite_of_card_ne_zero (by rw [hK n]; exact pow_ne_zero _ hp.ne_zero)
  let φ : K (n + 1) →* M := (powMonoidHom l).comp (K (n + 1)).subtype
  have hφ : ∀ y : K (n + 1), φ y = (y : M) ^ l := fun y => rfl
  have hrange : φ.range ≤ K n := by
    rintro _ ⟨y, rfl⟩
    rw [hmem, hφ, ← pow_mul, ← pow_succ']
    exact (hmem _ _).1 y.2
  have h1 : ∀ z : M, z ^ l = 1 → z ^ l ^ (n + 1) = 1 := fun z h => by
    rw [pow_succ', pow_mul, h, one_pow]
  have hker : Nat.card φ.ker = l ^ (r * 1) := by
    rw [← hc 1]
    refine Nat.card_congr
      { toFun := fun z => ⟨z.1.1, by rw [pow_one, ← hφ]; exact MonoidHom.mem_ker.1 z.2⟩
        invFun := fun z => ⟨⟨z.1, (hmem _ _).2 (h1 _ (by simpa using z.2))⟩,
          MonoidHom.mem_ker.2 (by rw [hφ]; simpa using z.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hcard : Nat.card φ.range = l ^ (r * n) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker, hK] at h
    refine Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos (r * 1)) ?_
    rw [← h, ← pow_add]
    ring_nf
  haveI := hfin n
  have heq : φ.range = K n := Subgroup.eq_of_le_of_card_ge hrange (by rw [hcard, hK])
  obtain ⟨y, hy⟩ : x ∈ φ.range := heq ▸ (hmem n x).2 hx
  exact ⟨y.1, (hmem _ _).1 y.2, hy⟩

/- English proof (translation)
Use `choose L hL using exists_pow_eq hc`. Set `u : ∀ m : ℕ, {y : M // y ^ l ^ (m + 1) = 1}` to `fun m => Nat.rec (motive := fun m => {y : M // y ^ l ^ (m + 1) = 1}) ⟨x, by simpa using hx⟩ (fun m y => ⟨L (m + 1) y.1 y.2, (hL _ _ _).1⟩) m`. Establish `hu : ∀ m, (u (m + 1)).1 ^ l = (u m).1` using `fun m => (hL _ _ _).2`. Set `s : ℕ → M` to `fun k => Nat.casesOn k 1 fun m => (u m).1`. Use `⟨Tate.mk s fun k => ⟨?_, ?_⟩, rfl⟩` and prove the remaining obligations.

Break down `k with _ | m` into its components or cases. Conclude with `one_pow _`. Conclude with `(u m).2`. Break down `k with _ | m` into its components or cases. Conclude with `hx`.

Conclude with `hu m`.
-/
theorem exists_tate (hc : ∀ n : ℕ, Nat.card {x : M // x ^ (l ^ n) = 1} = l ^ (r * n)) (x : M)
    (hx : x ^ l = 1) : ∃ t : Tate l M, t.lev 1 = x := by
  choose L hL using exists_pow_eq hc
  let u : ∀ m : ℕ, {y : M // y ^ l ^ (m + 1) = 1} := fun m =>
    Nat.rec (motive := fun m => {y : M // y ^ l ^ (m + 1) = 1}) ⟨x, by simpa using hx⟩
      (fun m y => ⟨L (m + 1) y.1 y.2, (hL _ _ _).1⟩) m
  have hu : ∀ m, (u (m + 1)).1 ^ l = (u m).1 := fun m => (hL _ _ _).2
  let s : ℕ → M := fun k => Nat.casesOn k 1 fun m => (u m).1
  refine ⟨Tate.mk s fun k => ⟨?_, ?_⟩, rfl⟩
  · rcases k with _ | m
    · exact one_pow _
    · exact (u m).2
  · rcases k with _ | m
    · exact hx
    · exact hu m

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Set `K : Subgroup M` to `(powMonoidHom l : M →* M).ker`. Establish `hmem : ∀ y : M, y ∈ K ↔ y ^ l = 1` using `fun y => by`. Simplify using `[K, MonoidHom.mem_ker, powMonoidHom_apply]`. Establish `hK : Nat.card K = l ^ r` using `(Nat.card_congr (Equiv.subtypeEquivRight fun y => hmem y)).trans hr`.

Use `haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hp.ne_zero)`. Use `letI : Module (ZMod l) (Additive K) := AddCommGroup.zmodModule fun z => by`. Apply `Additive.toMul.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [toMul_nsmul, toMul_zero, SubmonoidClass.coe_pow, OneMemClass.coe_one]`.

Conclude with `(hmem _).1 (Additive.toMul z).2`. Use `haveI : Finite (Additive K) := inferInstanceAs (Finite K)`. Use `haveI : Fintype (Additive K) := Fintype.ofFinite _`. Use `haveI hMF : Module.Finite (ZMod l) (Additive K) := Module.Finite.of_finite`. Use `haveI hMFr : Module.Free (ZMod l) (Additive K) := Module.Free.of_divisionRing _ _`.

Establish `hfr : Module.finrank (ZMod l) (Additive K) = r`. Establish `h1` using `Module.card_eq_pow_finrank (K := ZMod l) (V := Additive K)`. Rewrite `h1` using `[ZMod.card, ← Nat.card_eq_fintype_card]`. Conclude with `Nat.pow_right_injective hp.two_le (h1.symm.trans hK)`. Set `b : Module.Basis (Fin r) (ZMod l) (Additive K)` to `@Module.finBasisOfFinrankEq (ZMod l) (Additive K) _ _ _ hMFr _ hMF r hfr`.

Set `v : Fin r → Additive K` to `@DFunLike.coe _ _ _ Module.Basis.instFunLike b`. Establish `hv : LinearIndependent (ZMod l) v` using `b.linearIndependent`. Use `⟨fun i => ((Additive.toMul (v i) : K) : M), fun i => (hmem _).1 (Additive.toMul (v i)).2, fun k hk i => ?_⟩` and prove the remaining obligations. Establish `hli` using `Fintype.linearIndependent_iff.1 hv (fun i => (k i : ZMod l)) ?_ i`. Conclude with `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hli`.

Repeatedly rewrite using `[Int.cast_smul_eq_zsmul]`. Apply `Additive.toMul.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[toMul_sum]`. Simplify `hk` using `[toMul_zsmul]`.
-/
theorem exists_independent (hr : Nat.card {x : M // x ^ l = 1} = l ^ r) :
    ∃ e : Fin r → M, (∀ i, e i ^ l = 1) ∧
      ∀ k : Fin r → ℤ, ∏ i, e i ^ k i = 1 → ∀ i, (l : ℤ) ∣ k i := by
  have hp : l.Prime := Fact.out
  let K : Subgroup M := (powMonoidHom l : M →* M).ker
  have hmem : ∀ y : M, y ∈ K ↔ y ^ l = 1 := fun y => by
    simp [K, MonoidHom.mem_ker, powMonoidHom_apply]
  have hK : Nat.card K = l ^ r :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun y => hmem y)).trans hr
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hp.ne_zero)
  letI : Module (ZMod l) (Additive K) := AddCommGroup.zmodModule fun z => by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [toMul_nsmul, toMul_zero, SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact (hmem _).1 (Additive.toMul z).2
  haveI : Finite (Additive K) := inferInstanceAs (Finite K)
  haveI : Fintype (Additive K) := Fintype.ofFinite _
  haveI hMF : Module.Finite (ZMod l) (Additive K) := Module.Finite.of_finite
  haveI hMFr : Module.Free (ZMod l) (Additive K) := Module.Free.of_divisionRing _ _
  have hfr : Module.finrank (ZMod l) (Additive K) = r := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod l) (V := Additive K)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at h1
    exact Nat.pow_right_injective hp.two_le (h1.symm.trans hK)
  let b : Module.Basis (Fin r) (ZMod l) (Additive K) :=
    @Module.finBasisOfFinrankEq (ZMod l) (Additive K) _ _ _ hMFr _ hMF r hfr
  let v : Fin r → Additive K := @DFunLike.coe _ _ _ Module.Basis.instFunLike b
  have hv : LinearIndependent (ZMod l) v := b.linearIndependent
  refine ⟨fun i => ((Additive.toMul (v i) : K) : M), fun i => (hmem _).1 (Additive.toMul (v i)).2,
    fun k hk i => ?_⟩
  have hli := Fintype.linearIndependent_iff.1 hv (fun i => (k i : ZMod l)) ?_ i
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hli
  · simp_rw [Int.cast_smul_eq_zsmul]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [toMul_sum]
    simpa [toMul_zsmul] using hk

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Take `⟨e, he1, hind⟩` from `exists_independent (M := M) (l := l) (r := r) (by simpa using hc 1)`. Use `choose t ht using fun i => exists_tate hc (e i) (he1 i)`. Establish `key : ∀ n (k : Fin r → ℤ), ∏ i, (t i).lev n ^ k i = 1 → ∀ i, (l : ℤ) ^ n ∣ k i`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => intro k _ i`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `k hk i`.

Establish `hl : ∀ j, (t j).lev (n + 1) ^ l ^ n = e j` using `fun j => by`. Rewrite using `[add_comm, Tate.lev_add_pow, ht]`. Establish `h1 : ∏ j, e j ^ k j = 1`. Establish `h2` using `congrArg (· ^ (l ^ n)) hk`. Simplify using `only [one_pow, ← Finset.prod_pow, zpow_pow_comm', hl] at h2`.

Conclude with `h2`. Use `choose k' hk' using hind k h1`. Establish `h3 : ∏ j, (t j).lev n ^ k' j = 1`. Rewrite using `[← hk]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[hk' j, zpow_mul, zpow_natCast, Tate.lev_succ]`. Rewrite using `[hk' i, pow_succ']`. Conclude with `mul_dvd_mul_left _ (ih k' h3 i)`. Establish `key2 : ∀ n (k k' : Fin r → ℕ), ∏ i, (t i).lev n ^ k i = ∏ i, (t i).lev n ^ k' i → ∀ i, (l : ℤ) ^ n ∣ (k i : ℤ) - k' i` using `fun n k k' h => key n (fun i => (k i : ℤ) - k' i) (by`. Simplify using `only [zpow_sub, zpow_natCast, Finset.prod_mul_distrib, Finset.prod_inv_distrib, h, mul_inv_cancel])`.

Establish `hgen : ∀ n (x : M), x ^ l ^ n = 1 → ∃ c : Fin r → ℕ, ∏ i, (t i).lev n ^ c i = x`. Introduce `n`. Use `haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩`. Use `haveI : Finite {x : M // x ^ l ^ n = 1} := Nat.finite_of_card_ne_zero (by rw [hc n]; exact pow_ne_zero _ hp.ne_zero)`. Set `ψ : (Fin r → ZMod (l ^ n)) → {x : M // x ^ l ^ n = 1}` to `fun c => ⟨∏ i, (t i).lev n ^ (c i).val, by`.

Rewrite using `[← Finset.prod_pow]`. Conclude with `Finset.prod_eq_one fun i _ => by`. Rewrite using `[← pow_mul, mul_comm, pow_mul, Tate.lev_pow, one_pow]⟩`. Establish `hinj : Function.Injective ψ` using `fun c c' h => funext fun i => by`. Establish `h1` using `key2 n _ _ (congrArg Subtype.val h) i`.

Rewrite using `[← sub_eq_zero, ← ZMod.natCast_zmod_val (c i), ← ZMod.natCast_zmod_val (c' i)]`. Establish `h2` using `(ZMod.intCast_zmod_eq_zero_iff_dvd (((c i).val : ℤ) - (c' i).val) (l ^ n)).2 (by exact_mod_cast h1)`. Move the coercions through the operations in `at h2`. Conclude with `h2`. Establish `hbij` using `hinj.bijective_of_nat_card_le (by`.

Rewrite using `[hc n, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, mul_comm])`. Introduce `x hx`. Take `⟨c, hc'⟩` from `hbij.2 ⟨x, hx⟩`. Conclude with `⟨fun i => (c i).val, congrArg Subtype.val hc'⟩`. Set `Φ` to `Fintype.linearCombination ℤ_[l] t`.

Establish `hΦ : ∀ a n, (Φ a).lev n = ∏ i, (t i).lev n ^ digit n (a i)` using `fun a n => by`. Rewrite using `[Fintype.linearCombination_apply, lev_sum]`. Both sides reduce to the same expression. Establish `hinj : Function.Injective Φ`. Use `(injective_iff_map_eq_zero Φ).2 fun a ha => funext fun i => PadicInt.ext_of_toZModPow.1 fun n => ?_` and prove the remaining obligations.

Establish `h1` using `key2 n (fun i => digit n (a i)) (fun _ => 0) (by`. Rewrite using `[← hΦ, ha]`. Use the proof step `simp) i`. Rewrite using `[← cast_digit, Pi.zero_apply, map_zero]`. Establish `h2` using `(ZMod.intCast_zmod_eq_zero_iff_dvd (digit n (a i) : ℤ) (l ^ n)).2 (by simpa using h1)`.

Conclude with `h2` after adjusting the coercions. Establish `hsurj : Function.Surjective Φ`. Introduce `x`. Use `choose c hc' using fun n => hgen n (x.lev n) (x.lev_pow n)`. Establish `hdiv : ∀ i n, (l : ℤ) ^ n ∣ ((c (n + 1) i : ℕ) : ℤ) - c n i` using `fun i n => key2 n (c (n + 1)) (c n) (by`.

Rewrite using `[hc' n, ← x.lev_succ, ← hc' (n + 1), ← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_mul, mul_comm, pow_mul, Tate.lev_succ]) i`. Establish `hex : ∀ i, ∃ a : ℤ_[l], ∀ n, PadicInt.toZModPow n a = ((c n i : ℤ) : ZMod (l ^ n))` using `fun i => ⟨_, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => (c n i : ℤ)) l (hdiv i)⟩`. Use `choose a ha using hex`.

Use `⟨a, Tate.ext fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[hΦ, ← hc' n]`. Use `Finset.prod_congr rfl fun i _ => pow_digit_eq ((t i).lev_pow n) ?_` and prove the remaining obligations. Rewrite using `[ha, Int.cast_natCast]`. Set `E : (Fin r → ℤ_[l]) ≃ₗ[ℤ_[l]] Tate l M` to `LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩`.

Conclude with `⟨Module.Free.of_equiv E, Module.Finite.equiv E, E.finrank_eq.symm.trans (Module.finrank_fin_fun ℤ_[l])⟩`.
-/
theorem free_finite_finrank (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (r : ℕ)
    (hc : ∀ n : ℕ, Nat.card {x : M // x ^ (l ^ n) = 1} = l ^ (r * n)) :
    Module.Free ℤ_[l] (Tate l M) ∧ Module.Finite ℤ_[l] (Tate l M) ∧
      Module.finrank ℤ_[l] (Tate l M) = r := by
  have hp : l.Prime := Fact.out
  obtain ⟨e, he1, hind⟩ := exists_independent (M := M) (l := l) (r := r) (by simpa using hc 1)
  choose t ht using fun i => exists_tate hc (e i) (he1 i)

  have key : ∀ n (k : Fin r → ℤ), ∏ i, (t i).lev n ^ k i = 1 → ∀ i, (l : ℤ) ^ n ∣ k i := by
    intro n
    induction n with
    | zero => intro k _ i; simp
    | succ n ih =>
      intro k hk i
      have hl : ∀ j, (t j).lev (n + 1) ^ l ^ n = e j := fun j => by
        rw [add_comm, Tate.lev_add_pow, ht]
      have h1 : ∏ j, e j ^ k j = 1 := by
        have h2 := congrArg (· ^ (l ^ n)) hk
        simp only [one_pow, ← Finset.prod_pow, zpow_pow_comm', hl] at h2
        exact h2
      choose k' hk' using hind k h1
      have h3 : ∏ j, (t j).lev n ^ k' j = 1 := by
        rw [← hk]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [hk' j, zpow_mul, zpow_natCast, Tate.lev_succ]
      rw [hk' i, pow_succ']
      exact mul_dvd_mul_left _ (ih k' h3 i)
  have key2 : ∀ n (k k' : Fin r → ℕ), ∏ i, (t i).lev n ^ k i = ∏ i, (t i).lev n ^ k' i →
      ∀ i, (l : ℤ) ^ n ∣ (k i : ℤ) - k' i := fun n k k' h =>
    key n (fun i => (k i : ℤ) - k' i) (by
      simp only [zpow_sub, zpow_natCast, Finset.prod_mul_distrib, Finset.prod_inv_distrib, h,
        mul_inv_cancel])

  have hgen : ∀ n (x : M), x ^ l ^ n = 1 → ∃ c : Fin r → ℕ, ∏ i, (t i).lev n ^ c i = x := by
    intro n
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
    haveI : Finite {x : M // x ^ l ^ n = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hc n]; exact pow_ne_zero _ hp.ne_zero)
    let ψ : (Fin r → ZMod (l ^ n)) → {x : M // x ^ l ^ n = 1} := fun c =>
      ⟨∏ i, (t i).lev n ^ (c i).val, by
        rw [← Finset.prod_pow]
        exact Finset.prod_eq_one fun i _ => by
          rw [← pow_mul, mul_comm, pow_mul, Tate.lev_pow, one_pow]⟩
    have hinj : Function.Injective ψ := fun c c' h => funext fun i => by
      have h1 := key2 n _ _ (congrArg Subtype.val h) i
      rw [← sub_eq_zero, ← ZMod.natCast_zmod_val (c i), ← ZMod.natCast_zmod_val (c' i)]
      have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (((c i).val : ℤ) - (c' i).val) (l ^ n)).2
        (by exact_mod_cast h1)
      push_cast at h2
      exact h2
    have hbij := hinj.bijective_of_nat_card_le (by
      rw [hc n, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul,
        mul_comm])
    intro x hx
    obtain ⟨c, hc'⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨fun i => (c i).val, congrArg Subtype.val hc'⟩

  let Φ := Fintype.linearCombination ℤ_[l] t
  have hΦ : ∀ a n, (Φ a).lev n = ∏ i, (t i).lev n ^ digit n (a i) := fun a n => by
    rw [Fintype.linearCombination_apply, lev_sum]
    rfl
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun a ha => funext fun i =>
      PadicInt.ext_of_toZModPow.1 fun n => ?_
    have h1 := key2 n (fun i => digit n (a i)) (fun _ => 0) (by
      rw [← hΦ, ha]
      simp) i
    rw [← cast_digit, Pi.zero_apply, map_zero]
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (digit n (a i) : ℤ) (l ^ n)).2
      (by simpa using h1)
    exact_mod_cast h2
  have hsurj : Function.Surjective Φ := by
    intro x
    choose c hc' using fun n => hgen n (x.lev n) (x.lev_pow n)
    have hdiv : ∀ i n, (l : ℤ) ^ n ∣ ((c (n + 1) i : ℕ) : ℤ) - c n i := fun i n =>
      key2 n (c (n + 1)) (c n) (by
        rw [hc' n, ← x.lev_succ, ← hc' (n + 1), ← Finset.prod_pow]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← pow_mul, mul_comm, pow_mul, Tate.lev_succ]) i
    have hex : ∀ i, ∃ a : ℤ_[l], ∀ n, PadicInt.toZModPow n a = ((c n i : ℤ) : ZMod (l ^ n)) :=
      fun i => ⟨_, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => (c n i : ℤ)) l (hdiv i)⟩
    choose a ha using hex
    refine ⟨a, Tate.ext fun n => ?_⟩
    rw [hΦ, ← hc' n]
    refine Finset.prod_congr rfl fun i _ => pow_digit_eq ((t i).lev_pow n) ?_
    rw [ha, Int.cast_natCast]
  let E : (Fin r → ℤ_[l]) ≃ₗ[ℤ_[l]] Tate l M := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  exact ⟨Module.Free.of_equiv E, Module.Finite.equiv E,
    E.finrank_eq.symm.trans (Module.finrank_fin_fun ℤ_[l])⟩

end GlobalTheory.TateFree
