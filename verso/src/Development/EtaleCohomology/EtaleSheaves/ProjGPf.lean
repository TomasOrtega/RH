import Development.EtaleCohomology.EtaleSheaves.TorEtPf

noncomputable section
open LateralTheory.E.t_E1Cut LateralTheory.E.LCSplitPf LateralTheory.E.TorEtPf

namespace LateralTheory.E.ProjGPf

variable {S : Type} [CommRing S]

/- English proof (translation)
The claim follows from `isUnit_of_dvd_unit (map_dvd _ (dvd_mul_right f g)) (IsLocalization.Away.algebraMap_isUnit (f * g))`.
-/
theorem isUnit_f_fg (f g : S) : IsUnit (algebraMap S (Localization.Away (f * g)) f) :=
  isUnit_of_dvd_unit (map_dvd _ (dvd_mul_right f g)) (IsLocalization.Away.algebraMap_isUnit (f * g))

/- English proof (translation)
The claim follows from `IsLocalization.Away.awayToAwayRight_eq f g a`.
-/
theorem rL_alg (f g : S) (a : S) :
    rL f g (algebraMap S _ a) = algebraMap S (Localization.Away (f * g)) a :=
  IsLocalization.Away.awayToAwayRight_eq f g a

/- English proof (translation)
The claim follows from `IsLocalization.Away.awayToAwayLeft_eq g f a`.
-/
theorem rR_alg (f g : S) (a : S) :
    rR f g (algebraMap S _ a) = algebraMap S (Localization.Away (f * g)) a :=
  IsLocalization.Away.awayToAwayLeft_eq g f a

/- English proof (translation)
Take `⟨⟨b, hb'⟩, hb⟩` from `IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers (f * g)) w`. Take `⟨n, rfl⟩` from `Submonoid.mem_powers_iff _ _ |>.mp hb'`. Use `choose a ha using hb`. Use `⟨n, fun k => IsLocalization.mk' (Localization.Away f) (a k) (⟨f ^ n, n, rfl⟩ : Submonoid.powers f), fun k => ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (algebraMap S (Localization.Away (f * g)) (f ^ n))`.

Rewrite using `[map_pow]`. Conclude with `(isUnit_f_fg f g).pow n`. Apply `hu.mul_left_cancel` to reduce the goal to its premises. Establish `hs` using `IsLocalization.mk'_spec' (Localization.Away f) (a k) (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)`. Express the relevant statement in the definitionally equal form `algebraMap S _ (f ^ n) * _ = _ at hs`.

Rewrite using `[← rL_alg, ← map_mul, hs, rL_alg, ha k, Algebra.smul_def]`. Express the relevant statement in the definitionally equal form `algebraMap S _ ((f * g) ^ n) * w k = _`. Rewrite using `[mul_pow, map_mul, mul_assoc, rL_alg]`.
-/
theorem rL_surj {ι : Type} [Finite ι] (f g : S) (w : ι → Localization.Away (f * g)) :
    ∃ (n : ℕ) (x : ι → Localization.Away f), ∀ k, rL f g (x k) = algebraMap S _ (g ^ n) * w k := by
  obtain ⟨⟨b, hb'⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers (f * g)) w
  obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.mp hb'
  choose a ha using hb
  refine ⟨n, fun k => IsLocalization.mk' (Localization.Away f) (a k) (⟨f ^ n, n, rfl⟩ : Submonoid.powers f), fun k => ?_⟩
  have hu : IsUnit (algebraMap S (Localization.Away (f * g)) (f ^ n)) := by
    rw [map_pow]; exact (isUnit_f_fg f g).pow n
  apply hu.mul_left_cancel
  have hs := IsLocalization.mk'_spec' (Localization.Away f) (a k) (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
  change algebraMap S _ (f ^ n) * _ = _ at hs
  rw [← rL_alg, ← map_mul, hs, rL_alg, ha k, Algebra.smul_def]
  change algebraMap S _ ((f * g) ^ n) * w k = _
  rw [mul_pow, map_mul, mul_assoc, rL_alg]

/- English proof (translation)
Take `⟨⟨a, s⟩, hs⟩` from `IsLocalization.surj (Submonoid.powers f) x`. Establish `h0 : algebraMap S (Localization.Away (f * g)) a = 0`. Rewrite using `[← rL_alg, ← hs, map_mul, hx, zero_mul]`. Take `⟨⟨m, n, rfl⟩, hm⟩` from `(IsLocalization.map_eq_zero_iff (Submonoid.powers (f * g)) _ a).mp h0`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Establish `hu : IsUnit (algebraMap S (Localization.Away f) (f ^ n * s))` using `IsLocalization.map_units (Localization.Away f) (⟨f ^ n * s, Submonoid.mul_mem _ (Submonoid.pow_mem _ (Submonoid.mem_powers f) n) s.2⟩ : Submonoid.powers f)`. Apply `(hu.mul_left_eq_zero).mp` to reduce the goal to its premises. Establish `e1 : algebraMap S (Localization.Away f) (g ^ n) * x * algebraMap S _ (f ^ n * s) = algebraMap S _ (g ^ n * f ^ n) * (x * algebraMap S _ (s : S))`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, hs, ← map_mul, show g ^ n * f ^ n * a = (f * g) ^ n * a by ring, hm, map_zero]`.
-/
theorem rL_ker (f g : S) (x : Localization.Away f) (hx : rL f g x = 0) :
    ∃ n : ℕ, algebraMap S _ (g ^ n) * x = 0 := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) x
  have h0 : algebraMap S (Localization.Away (f * g)) a = 0 := by
    rw [← rL_alg, ← hs, map_mul, hx, zero_mul]
  obtain ⟨⟨m, n, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f * g)) _ a).mp h0
  refine ⟨n, ?_⟩
  have hu : IsUnit (algebraMap S (Localization.Away f) (f ^ n * s)) :=
    IsLocalization.map_units (Localization.Away f)
      (⟨f ^ n * s, Submonoid.mul_mem _ (Submonoid.pow_mem _ (Submonoid.mem_powers f) n) s.2⟩ : Submonoid.powers f)
  apply (hu.mul_left_eq_zero).mp
  have e1 : algebraMap S (Localization.Away f) (g ^ n) * x * algebraMap S _ (f ^ n * s)
      = algebraMap S _ (g ^ n * f ^ n) * (x * algebraMap S _ (s : S)) := by
    simp only [map_mul]; ring
  rw [e1, hs, ← map_mul, show g ^ n * f ^ n * a = (f * g) ^ n * a by ring, hm, map_zero]

/- English proof (translation)
Use `choose n hn using fun k => rL_ker f g (x k) (hx k)`. Use `⟨Finset.univ.sup n, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[← Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ k) : n k ≤ _), pow_add, map_mul, mul_assoc, hn k, mul_zero]`.
-/
theorem rL_ker_fam {ι : Type} [Fintype ι] (f g : S) (x : ι → Localization.Away f)
    (hx : ∀ k, rL f g (x k) = 0) : ∃ n : ℕ, ∀ k, algebraMap S _ (g ^ n) * x k = 0 := by
  choose n hn using fun k => rL_ker f g (x k) (hx k)
  refine ⟨Finset.univ.sup n, fun k => ?_⟩
  rw [← Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ k) : n k ≤ _), pow_add, map_mul, mul_assoc, hn k,
    mul_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem twist_apply {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ε : ZMod q → A}
    (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) (k : ZMod q) :
    twist hε z k = ∑ c, ε c * z (k + c) := rfl

/- English proof (translation)
Introduce `q _ S _ f g hfg ε hε`. Set `_` to `(torMap f g hε).toAlgebra`. Set `_` to `(pr2 f g hε).toAlgebra`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨_, n, rfl⟩`.

Establish `e : algebraMap (Tor f g hε) (ZMod q → Localization.Away g) (algebraMap S (Tor f g hε) g ^ n) = fun _ => algebraMap S (Localization.Away g) g ^ n`. Rewrite using `[map_pow]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `Pi.isUnit_iff.mpr fun _ => (IsLocalization.Away.algebraMap_isUnit g).pow n`.

Introduce `y`. Take `⟨n, x, hx⟩` from `rL_surj f g (twist hε (fun k => rR f g (y k)))`. Establish `hmem : ((x, fun k => algebraMap S _ (g ^ n) * y k) : Amb f g q) ∈ Tor f g hε` using `by show h1 f g _ = h2 f g hε _`. Use function extensionality and compare the values at `k`. Express the relevant statement in the definitionally equal form `rL f g (x k) = ∑ c, ε c * rR f g (algebraMap S _ (g ^ n) * y (k + c))`.

Rewrite using `[hx k, twist_apply]`. Simplify using `only [map_mul, rR_alg]`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun c _ => by ring`. Use `⟨(⟨_, hmem⟩, ⟨algebraMap S _ g ^ n, n, rfl⟩), ?_⟩` and prove the remaining obligations.

Use `show y * pr2 f g hε (torMap f g hε g ^ n) = pr2 f g hε ⟨_, hmem⟩`. Rewrite using `[map_pow]`. Use function extensionality and compare the values at `k`. Express the relevant statement in the definitionally equal form `y k * (algebraMap S (Localization.Away g) g) ^ n = algebraMap S _ (g ^ n) * y k`. Rewrite using `[map_pow, mul_comm]`.

Introduce `t1 t2 h`. Establish `h0 : (t1 - t2).1.2 = 0`. Establish `: pr2 f g hε (t1 - t2) = 0`. Rewrite using `[map_sub]`. Conclude with `sub_eq_zero.mpr h`.

Conclude with `this`. Establish `hx : ∀ k, rL f g ((t1 - t2).1.1 k) = 0`. Introduce `k`. Establish `hm : h1 f g (t1 - t2).1 = h2 f g hε (t1 - t2).1` using `(t1 - t2).2`. Establish `hk` using `congrFun hm k`.

Express the relevant statement in the definitionally equal form `rL f g ((t1 - t2).1.1 k) = ∑ c, ε c * rR f g ((t1 - t2).1.2 (k + c)) at hk`. Rewrite using `[hk, h0]`. Simplify using the standard rewrite rules. Take `⟨n, hn⟩` from `rL_ker_fam f g (fun k => (t1 - t2).1.1 k) hx`. Use `⟨⟨algebraMap S _ g ^ n, n, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← sub_eq_zero, ← mul_sub]`. Use `show torMap f g hε g ^ n * (t1 - t2) = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use `Prod.ext (funext fun k => ?_) (funext fun k => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(algebraMap S (Localization.Away f) g) ^ n * (t1 - t2).1.1 k = 0`.

Rewrite using `[← map_pow]`. Conclude with `hn k`. Express the relevant statement in the definitionally equal form `(algebraMap S (Localization.Away g) g) ^ n * (t1 - t2).1.2 k = 0`. Rewrite using `[h0]`. Simplify using the standard rewrite rules.
-/
theorem ProjG_of : ProjG := by
  intro q _ S _ f g hfg ε hε
  let _ := (torMap f g hε).toAlgebra
  let _ := (pr2 f g hε).toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    have e : algebraMap (Tor f g hε) (ZMod q → Localization.Away g) (algebraMap S (Tor f g hε) g ^ n)
        = fun _ => algebraMap S (Localization.Away g) g ^ n := by
      rw [map_pow]; rfl
    rw [e]
    exact Pi.isUnit_iff.mpr fun _ => (IsLocalization.Away.algebraMap_isUnit g).pow n
  · intro y
    obtain ⟨n, x, hx⟩ := rL_surj f g (twist hε (fun k => rR f g (y k)))
    have hmem : ((x, fun k => algebraMap S _ (g ^ n) * y k) : Amb f g q) ∈ Tor f g hε := by
      show h1 f g _ = h2 f g hε _
      funext k
      change rL f g (x k) = ∑ c, ε c * rR f g (algebraMap S _ (g ^ n) * y (k + c))
      rw [hx k, twist_apply]
      simp only [map_mul, rR_alg]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    refine ⟨(⟨_, hmem⟩, ⟨algebraMap S _ g ^ n, n, rfl⟩), ?_⟩
    show y * pr2 f g hε (torMap f g hε g ^ n) = pr2 f g hε ⟨_, hmem⟩
    rw [map_pow]
    funext k
    change y k * (algebraMap S (Localization.Away g) g) ^ n = algebraMap S _ (g ^ n) * y k
    rw [map_pow, mul_comm]
  · intro t1 t2 h
    have h0 : (t1 - t2).1.2 = 0 := by
      have : pr2 f g hε (t1 - t2) = 0 := by
        rw [map_sub]; exact sub_eq_zero.mpr h
      exact this
    have hx : ∀ k, rL f g ((t1 - t2).1.1 k) = 0 := by
      intro k
      have hm : h1 f g (t1 - t2).1 = h2 f g hε (t1 - t2).1 := (t1 - t2).2
      have hk := congrFun hm k
      change rL f g ((t1 - t2).1.1 k) = ∑ c, ε c * rR f g ((t1 - t2).1.2 (k + c)) at hk
      rw [hk, h0]; simp
    obtain ⟨n, hn⟩ := rL_ker_fam f g (fun k => (t1 - t2).1.1 k) hx
    refine ⟨⟨algebraMap S _ g ^ n, n, rfl⟩, ?_⟩
    rw [← sub_eq_zero, ← mul_sub]
    show torMap f g hε g ^ n * (t1 - t2) = 0
    apply Subtype.ext
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · change (algebraMap S (Localization.Away f) g) ^ n * (t1 - t2).1.1 k = 0
      rw [← map_pow]; exact hn k
    · change (algebraMap S (Localization.Away g) g) ^ n * (t1 - t2).1.2 k = 0
      rw [h0]; simp

end LateralTheory.E.ProjGPf
