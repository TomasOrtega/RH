import Mathlib
open scoped Matrix

namespace GlobalTheory.NormSystemVanishing

/- English proof (translation)
Establish `hn : 0 < orderOf u` using `orderOf_pos u`. Proceed by induction on `S using Finset.strongInduction with`. Consider the case `H S ih`. Break down `S.eq_empty_or_nonempty with rfl | ⟨g, hg⟩` into its components or cases. Simplify using the standard rewrite rules.

Establish `hpow : ∀ j, g * u ^ j ∈ S`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simpa using hg`. Consider the case `succ j ihj => rw [pow_succ, ← mul_assoc]`.

Conclude with `hS _ ihj`. Establish `hOS : (Finset.range (orderOf u)).image (fun j => g * u ^ j) ⊆ S`. Introduce `y hy`. Take `⟨j, -, rfl⟩` from `Finset.mem_image.mp hy`. Conclude with `hpow j`.

Establish `hgO : g ∈ (Finset.range (orderOf u)).image (fun j => g * u ^ j)` using `Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hn, by simp⟩`. Establish `hsumO : ∑ y ∈ (Finset.range (orderOf u)).image (fun j => g * u ^ j), f y = ∑ j ∈ Finset.range (orderOf u), f (g * u ^ j)`. Rewrite using `[Finset.sum_image]`. Introduce `i hi j hj hij`. Conclude with `pow_injOn_Iio_orderOf (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (mul_left_cancel hij)`.

Rewrite using `[← Finset.sum_sdiff hOS, hsumO]`. Use `P.add_mem (ih _ (Finset.sdiff_ssubset hOS ⟨g, hgO⟩) ?_) (hP g)` and prove the remaining obligations. Introduce `y hy`. Rewrite `hy`, the goal using `[Finset.mem_sdiff]`. Use `⟨hS y hy.1, fun hyu => hy.2 ?_⟩` and prove the remaining obligations.

Take `⟨j, -, hj⟩` from `Finset.mem_image.mp hyu`. Use `Finset.mem_image.mpr ⟨(j + (orderOf u - 1)) % orderOf u, Finset.mem_range.mpr (Nat.mod_lt _ hn), ?_⟩` and prove the remaining obligations. Use `show g * u ^ ((j + (orderOf u - 1)) % orderOf u) = y`. Rewrite using `[pow_mod_orderOf, pow_add, ← mul_assoc, hj, mul_assoc, ← pow_succ', Nat.sub_add_cancel hn, pow_orderOf_eq_one, mul_one]`.
-/
theorem sum_mem_of_orbit_sums {G H : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] (P : AddSubgroup H) (u : G) (f : G → H) (S : Finset G)
    (hS : ∀ g ∈ S, g * u ∈ S)
    (hP : ∀ g, ∑ j ∈ Finset.range (orderOf u), f (g * u ^ j) ∈ P) :
    ∑ g ∈ S, f g ∈ P := by
  have hn : 0 < orderOf u := orderOf_pos u
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | ⟨g, hg⟩
    · simp
    have hpow : ∀ j, g * u ^ j ∈ S := by
      intro j
      induction j with
      | zero => simpa using hg
      | succ j ihj => rw [pow_succ, ← mul_assoc]; exact hS _ ihj
    have hOS : (Finset.range (orderOf u)).image (fun j => g * u ^ j) ⊆ S := by
      intro y hy
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
      exact hpow j
    have hgO : g ∈ (Finset.range (orderOf u)).image (fun j => g * u ^ j) :=
      Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hn, by simp⟩
    have hsumO : ∑ y ∈ (Finset.range (orderOf u)).image (fun j => g * u ^ j), f y =
        ∑ j ∈ Finset.range (orderOf u), f (g * u ^ j) := by
      rw [Finset.sum_image]
      intro i hi j hj hij
      exact pow_injOn_Iio_orderOf (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
        (mul_left_cancel hij)
    rw [← Finset.sum_sdiff hOS, hsumO]
    refine P.add_mem (ih _ (Finset.sdiff_ssubset hOS ⟨g, hgO⟩) ?_) (hP g)
    intro y hy
    rw [Finset.mem_sdiff] at hy ⊢
    refine ⟨hS y hy.1, fun hyu => hy.2 ?_⟩
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hyu
    refine Finset.mem_image.mpr
      ⟨(j + (orderOf u - 1)) % orderOf u, Finset.mem_range.mpr (Nat.mod_lt _ hn), ?_⟩
    show g * u ^ ((j + (orderOf u - 1)) % orderOf u) = y
    rw [pow_mod_orderOf, pow_add, ← mul_assoc, hj, mul_assoc, ← pow_succ',
      Nat.sub_add_cancel hn, pow_orderOf_eq_one, mul_one]

/- English proof (translation)
Take `⟨k, rfl⟩` from `h`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [Nat.mul_succ, pow_add, Module.End.mul_apply, hm, ih]`.
-/
theorem fixed_of_dvd {O H : Type} [CommRing O] [AddCommGroup H] [Module O H]
    (ψ : Module.End O H) (m : H) {p n : ℕ} (hm : (ψ ^ p) m = m) (h : p ∣ n) :
    (ψ ^ n) m = m := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, Module.End.mul_apply, hm, ih]

/- English proof (translation)
Establish `: IsNoetherian O M` using `isNoetherian_of_fg_of_noetherian M hM`. Establish `key : ∀ (a : ℕ) (x : M), x ∈ LinearMap.ker ((ψ ^ l ^ a - 1).comp M.subtype) ↔ (ψ ^ l ^ a) x = x`. Introduce `a x`. Simplify using `[sub_eq_zero]`. Take `⟨n, hn⟩` from `monotone_stabilizes_iff_noetherian.mpr ‹IsNoetherian O M› ⟨fun a => LinearMap.ker ((ψ ^ l ^ a - 1).comp M.subtype), fun a b hab x hx => by`.

Rewrite `hx`, the goal using `[key]`. Conclude with `fixed_of_dvd ψ _ hx (pow_dvd_pow l hab)⟩`. Use `⟨n, fun m hm a ha => ?_⟩` and prove the remaining obligations. Break down `le_total a n with h | h` into its components or cases. Conclude with `fixed_of_dvd ψ m ha (pow_dvd_pow l h)`.

Establish `e : LinearMap.ker ((ψ ^ l ^ n - 1).comp M.subtype) = LinearMap.ker ((ψ ^ l ^ a - 1).comp M.subtype)` using `hn a h`. Establish `h1 : (⟨m, hm⟩ : M) ∈ LinearMap.ker ((ψ ^ l ^ a - 1).comp M.subtype)` using `(key a _).mpr ha`. Rewrite `h1` using `[← e]`. Conclude with `(key n _).mp h1`.
-/
theorem exists_stable_exponent {O H : Type} [CommRing O] [IsNoetherianRing O] [AddCommGroup H]
    [Module O H] (M : Submodule O H) (hM : M.FG) (ψ : Module.End O H) (l : ℕ) :
    ∃ a₀ : ℕ, ∀ m ∈ M, ∀ a : ℕ, (ψ ^ l ^ a) m = m → (ψ ^ l ^ a₀) m = m := by
  have : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hM
  have key : ∀ (a : ℕ) (x : M),
      x ∈ LinearMap.ker ((ψ ^ l ^ a - 1).comp M.subtype) ↔ (ψ ^ l ^ a) x = x := by
    intro a x
    simp [sub_eq_zero]
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr ‹IsNoetherian O M›
    ⟨fun a => LinearMap.ker ((ψ ^ l ^ a - 1).comp M.subtype), fun a b hab x hx => by
      rw [key] at hx ⊢
      exact fixed_of_dvd ψ _ hx (pow_dvd_pow l hab)⟩
  refine ⟨n, fun m hm a ha => ?_⟩
  rcases le_total a n with h | h
  · exact fixed_of_dvd ψ m ha (pow_dvd_pow l h)
  · have e : LinearMap.ker ((ψ ^ l ^ n - 1).comp M.subtype) =
        LinearMap.ker ((ψ ^ l ^ a - 1).comp M.subtype) := hn a h
    have h1 : (⟨m, hm⟩ : M) ∈ LinearMap.ker ((ψ ^ l ^ a - 1).comp M.subtype) := (key a _).mpr ha
    rw [← e] at h1
    exact (key n _).mp h1

/- English proof (translation)
Establish `: Module.Finite O M` using `Module.Finite.iff_fg.mpr hM`. Establish `hx0 : x ∈ M`. Take `⟨m, hm, e⟩` from `hx 0`. Simplify `hm` using `[e]`. Establish `hI : Ideal.span {t} ≠ ⊤` using `by rwa [Ne, Ideal.span_singleton_eq_top]`.

Establish `hbot` using `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) _ hI`. Establish `hmem : (⟨x, hx0⟩ : M) ∈ (⨅ i : ℕ, (Ideal.span {t}) ^ i • ⊤ : Submodule O M)`. Rewrite using `[Submodule.mem_iInf]`. Introduce `i`. Take `⟨m, hm, e⟩` from `hx i`.

Establish `he : (⟨x, hx0⟩ : M) = t ^ i • (⟨m, hm⟩ : M)` using `Subtype.ext (by simpa using e)`. Rewrite using `[he]`. Use `Submodule.smul_mem_smul ?_ Submodule.mem_top` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_pow]`. Conclude with `Ideal.mem_span_singleton_self _`.

Rewrite `hmem` using `[hbot, Submodule.mem_bot]`. Simplify using `using congrArg Subtype.val hmem`.
-/
theorem eq_zero_of_forall_divisible {O H : Type} [CommRing O] [IsNoetherianRing O]
    [IsLocalRing O] [AddCommGroup H] [Module O H] (M : Submodule O H) (hM : M.FG) (t : O)
    (ht : ¬ IsUnit t) (x : H) (hx : ∀ k : ℕ, ∃ m ∈ M, x = t ^ k • m) : x = 0 := by
  have : Module.Finite O M := Module.Finite.iff_fg.mpr hM
  have hx0 : x ∈ M := by
    obtain ⟨m, hm, e⟩ := hx 0
    simpa [e] using hm
  have hI : Ideal.span {t} ≠ ⊤ := by rwa [Ne, Ideal.span_singleton_eq_top]
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) _ hI
  have hmem : (⟨x, hx0⟩ : M) ∈ (⨅ i : ℕ, (Ideal.span {t}) ^ i • ⊤ : Submodule O M) := by
    rw [Submodule.mem_iInf]
    intro i
    obtain ⟨m, hm, e⟩ := hx i
    have he : (⟨x, hx0⟩ : M) = t ^ i • (⟨m, hm⟩ : M) := Subtype.ext (by simpa using e)
    rw [he]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  rw [hbot, Submodule.mem_bot] at hmem
  simpa using congrArg Subtype.val hmem

/- English proof (translation)
Introduce `n hn`. Proceed by induction on `n, hn using Nat.le_induction with`. Consider the case `base`. Simplify using `[Finset.filter_eq']`. Consider the case `succ n hmn ih`.

Establish `hcomp : ∀ y : (ZMod (l ^ (n + 1)))ˣ, ZMod.unitsMap (pow_dvd_pow l (Nat.le_succ_of_le hmn)) y = ZMod.unitsMap (pow_dvd_pow l hmn) (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))).toMonoidHom y)` using `fun y => (DFunLike.congr_fun (ZMod.unitsMap_comp (pow_dvd_pow l hmn) (pow_dvd_pow l (Nat.le_succ n))) y).symm`. Establish `hmaps : ∀ y ∈ Finset.univ.filter (fun y : (ZMod (l ^ (n + 1)))ˣ => ZMod.unitsMap (pow_dvd_pow l (Nat.le_succ_of_le hmn)) y = x), Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))).toMonoidHom y ∈ Finset.univ.filter (fun x' : (ZMod (l ^ n))ˣ => ZMod.unitsMap ( …`. Introduce `y hy`. Rewrite `hy`, the goal using `[Finset.mem_filter]`. Conclude with `⟨Finset.mem_univ _, by rw [← hcomp]; exact hy.2⟩`.

Rewrite using `[ih, ← Finset.sum_fiberwise_of_maps_to hmaps (c (n + 1))]`. Use `Finset.sum_congr rfl fun x' hx' => ?_` and prove the remaining obligations. Rewrite using `[hc n x', Finset.filter_filter]`. Use `Finset.sum_congr (Finset.filter_congr fun y _ => ?_) fun _ _ => rfl` and prove the remaining obligations. Rewrite `hx'` using `[Finset.mem_filter]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨by rw [hcomp, h]; exact hx'.2, h⟩`. Conclude with `fun h => h.2`.
-/
private theorem sum_fibre_units_zmod_pow_eq_of_le {H : Type} [AddCommGroup H] (l : ℕ) [Fact l.Prime]
    (c : ∀ r : ℕ, (ZMod (l ^ r))ˣ → H)
    (hc : ∀ r x, c r x = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ (r + 1)))ˣ =>
      Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom x' = x),
        c (r + 1) x') (r : ℕ) (x : (ZMod (l ^ r))ˣ) :
    ∀ (n : ℕ) (hn : r ≤ n), c r x = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ n))ˣ =>
      ZMod.unitsMap (pow_dvd_pow l hn) x' = x), c n x' := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    simp [Finset.filter_eq']
  | succ n hmn ih =>
    have hcomp : ∀ y : (ZMod (l ^ (n + 1)))ˣ,
        ZMod.unitsMap (pow_dvd_pow l (Nat.le_succ_of_le hmn)) y =
          ZMod.unitsMap (pow_dvd_pow l hmn)
            (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))).toMonoidHom y) :=
      fun y => (DFunLike.congr_fun
        (ZMod.unitsMap_comp (pow_dvd_pow l hmn) (pow_dvd_pow l (Nat.le_succ n))) y).symm
    have hmaps : ∀ y ∈ Finset.univ.filter (fun y : (ZMod (l ^ (n + 1)))ˣ =>
        ZMod.unitsMap (pow_dvd_pow l (Nat.le_succ_of_le hmn)) y = x),
        Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))).toMonoidHom y ∈
          Finset.univ.filter (fun x' : (ZMod (l ^ n))ˣ => ZMod.unitsMap (pow_dvd_pow l hmn) x' = x) := by
      intro y hy
      rw [Finset.mem_filter] at hy ⊢
      exact ⟨Finset.mem_univ _, by rw [← hcomp]; exact hy.2⟩
    rw [ih, ← Finset.sum_fiberwise_of_maps_to hmaps (c (n + 1))]
    refine Finset.sum_congr rfl fun x' hx' => ?_
    rw [hc n x', Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun y _ => ?_) fun _ _ => rfl
    rw [Finset.mem_filter] at hx'
    constructor
    · intro h
      exact ⟨by rw [hcomp, h]; exact hx'.2, h⟩
    · exact fun h => h.2

/- English proof (translation)
The claim follows from `sum_fibre_units_zmod_pow_eq_of_le l c hc r x (r + k) (Nat.le_add_right r k)`.
-/
theorem sum_tower {H : Type} [AddCommGroup H] (l : ℕ) [Fact l.Prime]
    (c : ∀ r : ℕ, (ZMod (l ^ r))ˣ → H)
    (hc : ∀ r x, c r x = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ (r + 1)))ˣ =>
      Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom x' = x),
        c (r + 1) x') (r k : ℕ) (x : (ZMod (l ^ r))ˣ) :
    c r x = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ (r + k)))ˣ =>
      ZMod.unitsMap (pow_dvd_pow l (Nat.le_add_right r k)) x' = x), c (r + k) x' := sum_fibre_units_zmod_pow_eq_of_le l c hc r x (r + k) (Nat.le_add_right r k)

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Take `⟨n, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hn.ne'`. Rewrite using `[Nat.totient_prime_pow_succ hl.out, mul_comm (l ^ n)]`. Conclude with `mul_dvd_mul_left _ (pow_dvd_pow l (by omega))`.
-/
theorem totient_dvd (l : ℕ) [hl : Fact l.Prime] (n s : ℕ) (h : n ≤ s) :
    Nat.totient (l ^ n) ∣ (l - 1) * l ^ s := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [Nat.totient_prime_pow_succ hl.out, mul_comm (l ^ n)]
    exact mul_dvd_mul_left _ (pow_dvd_pow l (by omega))

/- English proof (translation)
Take `⟨d, hd⟩` from `totient_dvd l n s h`. Rewrite using `[hd, pow_mul, ZMod.pow_totient, one_pow]`.
-/
theorem unit_pow_eq_one (l : ℕ) [hl : Fact l.Prime] (n s : ℕ) (h : n ≤ s)
    (v : (ZMod (l ^ n))ˣ) : v ^ ((l - 1) * l ^ s) = 1 := by
  obtain ⟨d, hd⟩ := totient_dvd l n s h
  rw [hd, pow_mul, ZMod.pow_totient, one_pow]

/- English proof (translation)
Introduce `he`. Establish `hl2 : 2 ≤ l` using `hl.out.two_le`. Establish `hqB : 2 ≤ q ^ B` using `le_trans h2 (Nat.le_self_pow hB.ne' q)`. Establish `hlt : q ^ B < l ^ n` using `lt_of_le_of_lt hn (Nat.lt_pow_self (by omega))`. Establish `h1` using `congrArg Units.val he`.

Rewrite `h1` using `[Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one, ← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem unit_pow_ne_one (l : ℕ) [hl : Fact l.Prime] (q : ℕ) (hq : Nat.Coprime q l) (h2 : 2 ≤ q)
    (B n : ℕ) (hB : 0 < B) (hn : q ^ B ≤ n) :
    (ZMod.unitOfCoprime q (Nat.Coprime.pow_right n hq)) ^ B ≠ 1 := by
  intro he
  have hl2 : 2 ≤ l := hl.out.two_le
  have hqB : 2 ≤ q ^ B := le_trans h2 (Nat.le_self_pow hB.ne' q)
  have hlt : q ^ B < l ^ n := lt_of_le_of_lt hn (Nat.lt_pow_self (by omega))
  have h1 := congrArg Units.val he
  rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one, ← Nat.cast_pow,
    ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hlt,
    Nat.mod_eq_of_lt (by omega)] at h1
  omega

/- English proof (translation)
Introduce `O H _ _ _ _ _ l _ hl q hq hq2 M hM F _ c hcM hF hc r x`. Establish `hl2 : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Establish `hFpow : ∀ (r : ℕ) (y : (ZMod (l ^ r))ˣ) (j : ℕ), (F ^ j) (c r y) = c r (y * ZMod.unitOfCoprime q (Nat.Coprime.pow_right r hq) ^ j)`. Introduce `r y j`. Proceed by induction on `j generalizing y with`.

Consider the case `zero => simp`. Consider the case `succ j ih => rw [pow_succ, Module.End.mul_apply, hF, ih, mul_assoc, ← pow_succ']`. Take `⟨a₀, ha₀⟩` from `exists_stable_exponent M hM (F ^ (l - 1)) l`. Establish `hfix : ∀ s, a₀ ≤ s → ∀ (r : ℕ) (y : (ZMod (l ^ r))ˣ), (F ^ ((l - 1) * l ^ s)) (c r y) = c r y`. Introduce `s hs r y`.

Establish `h1 : ((F ^ (l - 1)) ^ l ^ r) (c r y) = c r y`. Rewrite using `[← pow_mul, hFpow, unit_pow_eq_one l r r le_rfl, mul_one]`. Establish `h3` using `ha₀ _ (hcM r y) r h1`. Rewrite `h3` using `[← pow_mul]`. Conclude with `fixed_of_dvd F _ h3 (mul_dvd_mul_left _ (pow_dvd_pow l hs))`.

Use `eq_zero_of_forall_divisible M hM (l : O) hl (c r x) fun K => ?_` and prove the remaining obligations. Take `⟨s, hs1, hs2⟩ : ∃ s, a₀ ≤ s ∧ r ≤ s` from `⟨max a₀ r, le_max_left _ _, le_max_right _ _⟩`. Establish `hBpos : 0 < (l - 1) * l ^ (s + K)` using `Nat.mul_pos (by omega) (pow_pos (by omega) _)`. Take `⟨k, hk⟩ : ∃ k, q ^ ((l - 1) * l ^ (s + K)) ≤ r + k` from `⟨_, Nat.le_add_left _ _⟩`. Take `⟨u, hu⟩ : ∃ u : (ZMod (l ^ (r + k)))ˣ, u = ZMod.unitOfCoprime q (Nat.Coprime.pow_right (r + k) hq)` from `⟨_, rfl⟩`.

Establish `hmap : ZMod.unitsMap (pow_dvd_pow l (Nat.le_add_right r k)) u = ZMod.unitOfCoprime q (Nat.Coprime.pow_right r hq)`. Substitute `hu` using the available equality. Use `ext`. Rewrite using `[ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime, map_natCast]`. Establish `hw1 : ZMod.unitsMap (pow_dvd_pow l (Nat.le_add_right r k)) (u ^ ((l - 1) * l ^ s)) = 1`.

Rewrite using `[map_pow, hmap, unit_pow_eq_one l r s hs2]`. Establish `hwinv : ∀ (g : (ZMod (l ^ (r + k)))ˣ) (j : ℕ), c (r + k) (g * (u ^ ((l - 1) * l ^ s)) ^ j) = c (r + k) g`. Introduce `g j`. Rewrite using `[← pow_mul, hu, ← hFpow]`. Conclude with `fixed_of_dvd F _ (hfix s hs1 (r + k) g) (dvd_mul_right _ _)`.

Establish `hdvd : orderOf (u ^ ((l - 1) * l ^ s)) ∣ l ^ (r + k)`. Apply `orderOf_dvd_of_pow_eq_one` to reduce the goal to its premises. Rewrite using `[← pow_mul, mul_assoc, ← pow_add]`. Conclude with `unit_pow_eq_one l (r + k) (s + (r + k)) (by omega) u`. Establish `hne : (u ^ ((l - 1) * l ^ s)) ^ l ^ K ≠ 1`.

Rewrite using `[← pow_mul, mul_assoc, ← pow_add, hu]`. Conclude with `unit_pow_ne_one l q hq hq2 _ (r + k) hBpos hk`. Establish `hK : l ^ K ∣ orderOf (u ^ ((l - 1) * l ^ s))`. Take `⟨e, -, he⟩` from `(Nat.dvd_prime_pow (Fact.out : l.Prime)).mp hdvd`. Break down `le_or_gt K e with h | h` into its components or cases.

Rewrite using `[he]`. Conclude with `pow_dvd_pow l h`. Conclude with `absurd (orderOf_dvd_iff_pow_eq_one.mp (he ▸ pow_dvd_pow l h.le)) hne`. Take `⟨t, ht⟩` from `hK`. Establish `hmem : c r x ∈ (Submodule.map (((l : O) ^ K) • LinearMap.id) M).toAddSubgroup`.

Rewrite using `[sum_tower l c hc r k x]`. Use `sum_mem_of_orbit_sums _ (u ^ ((l - 1) * l ^ s)) (c (r + k)) _ ?_ ?_` and prove the remaining obligations. Introduce `g hg`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, hw1, mul_one] at hg ⊢`. Conclude with `hg`.

Introduce `g`. Rewrite using `[Finset.sum_congr rfl (fun j _ => hwinv g j), Finset.sum_const, Finset.card_range, ht]`. Rewrite using `[Submodule.mem_toAddSubgroup, Submodule.mem_map]`. Use `⟨(t : O) • c (r + k) g, M.smul_mem _ (hcM _ _), ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, LinearMap.id_apply, smul_smul, ← Nat.cast_smul_eq_nsmul O, Nat.cast_mul, Nat.cast_pow]`.

Rewrite `hmem` using `[Submodule.mem_toAddSubgroup, Submodule.mem_map]`. Take `⟨m, hm, e⟩` from `hmem`. Conclude with `⟨m, hm, by simpa using e.symm⟩`.
-/
theorem normCompatible_eq_zero : ∀ (O H : Type) [CommRing O] [IsNoetherianRing O] [IsLocalRing O] [AddCommGroup H] [Module O H] (l : ℕ) [Fact l.Prime], ¬ IsUnit (l : O) → ∀ (q : ℕ) (hq : Nat.Coprime q l), 2 ≤ q → ∀ (M : Submodule O H), M.FG → ∀ (F : H →ₗ[O] H), (∀ x ∈ M, F x ∈ M) → ∀ (c : ∀ r : ℕ, (ZMod (l ^ r))ˣ → H), (∀ r x, c r x ∈ M) → (∀ r x, F (c r x) = c r (x * ZMod.unitOfCoprime q (Nat.Coprime.pow_right r hq))) → (∀ r x, c r x = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ (r + 1)))ˣ => Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom x' = x), c (r + 1) x') → ∀ r x, c r x = 0 := by
  intro O H _ _ _ _ _ l _ hl q hq hq2 M hM F _ c hcM hF hc r x
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hFpow : ∀ (r : ℕ) (y : (ZMod (l ^ r))ˣ) (j : ℕ),
      (F ^ j) (c r y) = c r (y * ZMod.unitOfCoprime q (Nat.Coprime.pow_right r hq) ^ j) := by
    intro r y j
    induction j generalizing y with
    | zero => simp
    | succ j ih => rw [pow_succ, Module.End.mul_apply, hF, ih, mul_assoc, ← pow_succ']
  obtain ⟨a₀, ha₀⟩ := exists_stable_exponent M hM (F ^ (l - 1)) l
  have hfix : ∀ s, a₀ ≤ s → ∀ (r : ℕ) (y : (ZMod (l ^ r))ˣ),
      (F ^ ((l - 1) * l ^ s)) (c r y) = c r y := by
    intro s hs r y
    have h1 : ((F ^ (l - 1)) ^ l ^ r) (c r y) = c r y := by
      rw [← pow_mul, hFpow, unit_pow_eq_one l r r le_rfl, mul_one]
    have h3 := ha₀ _ (hcM r y) r h1
    rw [← pow_mul] at h3
    exact fixed_of_dvd F _ h3 (mul_dvd_mul_left _ (pow_dvd_pow l hs))
  refine eq_zero_of_forall_divisible M hM (l : O) hl (c r x) fun K => ?_
  obtain ⟨s, hs1, hs2⟩ : ∃ s, a₀ ≤ s ∧ r ≤ s := ⟨max a₀ r, le_max_left _ _, le_max_right _ _⟩
  have hBpos : 0 < (l - 1) * l ^ (s + K) := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  obtain ⟨k, hk⟩ : ∃ k, q ^ ((l - 1) * l ^ (s + K)) ≤ r + k := ⟨_, Nat.le_add_left _ _⟩
  obtain ⟨u, hu⟩ : ∃ u : (ZMod (l ^ (r + k)))ˣ,
      u = ZMod.unitOfCoprime q (Nat.Coprime.pow_right (r + k) hq) := ⟨_, rfl⟩
  have hmap : ZMod.unitsMap (pow_dvd_pow l (Nat.le_add_right r k)) u =
      ZMod.unitOfCoprime q (Nat.Coprime.pow_right r hq) := by
    subst hu
    ext
    rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.coe_unitOfCoprime,
      ZMod.coe_unitOfCoprime, map_natCast]
  have hw1 : ZMod.unitsMap (pow_dvd_pow l (Nat.le_add_right r k)) (u ^ ((l - 1) * l ^ s)) = 1 := by
    rw [map_pow, hmap, unit_pow_eq_one l r s hs2]
  have hwinv : ∀ (g : (ZMod (l ^ (r + k)))ˣ) (j : ℕ),
      c (r + k) (g * (u ^ ((l - 1) * l ^ s)) ^ j) = c (r + k) g := by
    intro g j
    rw [← pow_mul, hu, ← hFpow]
    exact fixed_of_dvd F _ (hfix s hs1 (r + k) g) (dvd_mul_right _ _)
  have hdvd : orderOf (u ^ ((l - 1) * l ^ s)) ∣ l ^ (r + k) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, mul_assoc, ← pow_add]
    exact unit_pow_eq_one l (r + k) (s + (r + k)) (by omega) u
  have hne : (u ^ ((l - 1) * l ^ s)) ^ l ^ K ≠ 1 := by
    rw [← pow_mul, mul_assoc, ← pow_add, hu]
    exact unit_pow_ne_one l q hq hq2 _ (r + k) hBpos hk
  have hK : l ^ K ∣ orderOf (u ^ ((l - 1) * l ^ s)) := by
    obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow (Fact.out : l.Prime)).mp hdvd
    rcases le_or_gt K e with h | h
    · rw [he]; exact pow_dvd_pow l h
    · exact absurd (orderOf_dvd_iff_pow_eq_one.mp (he ▸ pow_dvd_pow l h.le)) hne
  obtain ⟨t, ht⟩ := hK
  have hmem : c r x ∈ (Submodule.map (((l : O) ^ K) • LinearMap.id) M).toAddSubgroup := by
    rw [sum_tower l c hc r k x]
    refine sum_mem_of_orbit_sums _ (u ^ ((l - 1) * l ^ s)) (c (r + k)) _ ?_ ?_
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, hw1, mul_one] at hg ⊢
      exact hg
    · intro g
      rw [Finset.sum_congr rfl (fun j _ => hwinv g j), Finset.sum_const, Finset.card_range, ht]
      rw [Submodule.mem_toAddSubgroup, Submodule.mem_map]
      refine ⟨(t : O) • c (r + k) g, M.smul_mem _ (hcM _ _), ?_⟩
      rw [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, ← Nat.cast_smul_eq_nsmul O,
        Nat.cast_mul, Nat.cast_pow]
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_map] at hmem
  obtain ⟨m, hm, e⟩ := hmem
  exact ⟨m, hm, by simpa using e.symm⟩

end GlobalTheory.NormSystemVanishing
