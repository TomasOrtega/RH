import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LimLift

open CrystallineSemistableComparison.CechClassBoundaries

variable {R : Type} [CommRing R]

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem cls_congr {K : Cx.{1} R} {j : ℕ} {a b : K.X j} (h : a = b) (ha : K.d j a = 0) (hb : K.d j b = 0) :
    K.cls a ha = K.cls b hb := by
  subst h
  rfl

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using h`. Consider the case `succ n ih`. Rewrite `h` using `[pow_succ', mul_smul]`. Conclude with `ih (ht _ _ h)`.
-/
theorem pow_tf {K : Cx.{1} R} {c : R} (ht : ∀ j (x : K.X j), c • x = 0 → x = 0) (n j : ℕ) (x : K.X j)
    (h : c ^ n • x = 0) : x = 0 := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ', mul_smul] at h
    exact ih (ht _ _ h)

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj K j).1 z`. Rewrite `hz` using `[mapH_cls' r a ha (cyc r a ha), (CrystallineSemistableComparison.P.cls_surj L j).2.1]`. Establish `hv : ∃ v : K.X j, v ∈ K.B j ∧ K.d j v = 0 ∧ r.f j (a - v) = 0`. Consider the cases of `j with`. Consider the case `zero`.

Use `⟨0, (mem_boundaries_zero_iff _).2 rfl, map_zero _, ?_⟩` and prove the remaining obligations. Rewrite using `[sub_zero]`. Conclude with `(mem_boundaries_zero_iff _).1 hz`. Consider the case `succ j`. Take `⟨b, hb⟩` from `(mem_Bs _).1 hz`.

Take `⟨v, rfl⟩` from `hs j b`. Use `⟨K.d j v, (mem_Bs _).2 ⟨v, rfl⟩, K.dd j v, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, ← r.comm, hb, sub_self]`. Take `⟨v, hvB, hvd, h0⟩` from `hv`. Take `⟨y, hy⟩` from `(hk j _).1 h0`.

Establish `hdy : K.d j y = 0`. Use `pow_tf ht n _ _ ?_` and prove the remaining obligations. Rewrite using `[← map_smul, ← hy, map_sub, ha, hvd, sub_zero]`. Use `⟨K.cls y hdy, ?_⟩` and prove the remaining obligations. Establish `hcy : K.d j (c ^ n • y) = 0` using `by rw [map_smul, hdy, smul_zero]`.

Rewrite using `[← cls_smul _ _ hdy hcy, (CrystallineSemistableComparison.P.cls_surj K j).2.2.1 _ _ ha hcy, ← hy]`. Simplify using `using hvB`.
-/
theorem ker_red {K L : Cx.{1} R} (c : R) (n : ℕ) (r : Cx.Hom K L (RingHom.id R))
    (hs : ∀ j, Function.Surjective (r.f j)) (hk : ∀ j x, r.f j x = 0 ↔ ∃ y, x = c ^ n • y)
    (ht : ∀ j (x : K.X j), c • x = 0 → x = 0) (j : ℕ) (z : K.H j) (hz : r.mapH j z = 0) :
    ∃ y, z = c ^ n • y := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K j).1 z
  rw [mapH_cls' r a ha (cyc r a ha), (CrystallineSemistableComparison.P.cls_surj L j).2.1] at hz
  have hv : ∃ v : K.X j, v ∈ K.B j ∧ K.d j v = 0 ∧ r.f j (a - v) = 0 := by
    cases j with
    | zero =>
      refine ⟨0, (mem_boundaries_zero_iff _).2 rfl, map_zero _, ?_⟩
      rw [sub_zero]
      exact (mem_boundaries_zero_iff _).1 hz
    | succ j =>
      obtain ⟨b, hb⟩ := (mem_Bs _).1 hz
      obtain ⟨v, rfl⟩ := hs j b
      refine ⟨K.d j v, (mem_Bs _).2 ⟨v, rfl⟩, K.dd j v, ?_⟩
      rw [map_sub, ← r.comm, hb, sub_self]
  obtain ⟨v, hvB, hvd, h0⟩ := hv
  obtain ⟨y, hy⟩ := (hk j _).1 h0
  have hdy : K.d j y = 0 := by
    refine pow_tf ht n _ _ ?_
    rw [← map_smul, ← hy, map_sub, ha, hvd, sub_zero]
  refine ⟨K.cls y hdy, ?_⟩
  have hcy : K.d j (c ^ n • y) = 0 := by rw [map_smul, hdy, smul_zero]
  rw [← cls_smul _ _ hdy hcy, (CrystallineSemistableComparison.P.cls_surj K j).2.2.1 _ _ ha hcy, ← hy]
  simpa using hvB

/- English proof (translation)
Take `⟨w, hw, rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj L j).1 h`. Take `⟨a, rfl⟩` from `hs j w`. Establish `h0 : c ^ n • r.f j a = 0`. Rewrite using `[← map_smul]`. Conclude with `(hk j _).2 ⟨a, rfl⟩`.

Establish `hd : L.d j (c ^ n • r.f j a) = 0` using `by rw [h0, map_zero]`. Rewrite using `[← cls_smul _ _ hw hd, (CrystallineSemistableComparison.P.cls_surj L j).2.1, h0]`. Conclude with `zero_mem _`.
-/
theorem kill_H {K L : Cx.{1} R} (c : R) (n : ℕ) (r : Cx.Hom K L (RingHom.id R))
    (hs : ∀ j, Function.Surjective (r.f j)) (hk : ∀ j x, r.f j x = 0 ↔ ∃ y, x = c ^ n • y)
    (j : ℕ) (h : L.H j) : c ^ n • h = 0 := by
  obtain ⟨w, hw, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L j).1 h
  obtain ⟨a, rfl⟩ := hs j w
  have h0 : c ^ n • r.f j a = 0 := by
    rw [← map_smul]
    exact (hk j _).2 ⟨a, rfl⟩
  have hd : L.d j (c ^ n • r.f j a) = 0 := by rw [h0, map_zero]
  rw [← cls_smul _ _ hw hd, (CrystallineSemistableComparison.P.cls_surj L j).2.1, h0]
  exact zero_mem _

/- English proof (translation)
Take `⟨w, hw, rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj L j).1 x`. Take `⟨a, rfl⟩` from `hs j w`. Establish `h1 : r.f (j + 1) (K.d j a) = 0` using `by rw [← r.comm]; exact hw`. Take `⟨b, hb⟩` from `(hk (j + 1) _).1 h1`. Establish `hdb : K.d (j + 1) b = 0`.

Use `pow_tf ht n _ _ ?_` and prove the remaining obligations. Rewrite using `[← map_smul, ← hb, K.dd]`. Establish `hcb : K.d (j + 1) (c ^ n • b) = 0` using `by rw [map_smul, hdb, smul_zero]`. Establish `h2 : c ^ n • K.cls b hdb = 0`. Rewrite using `[← cls_smul _ _ hdb hcb, (CrystallineSemistableComparison.P.cls_surj K (j + 1)).2.1]`.

Conclude with `(mem_Bs _).2 ⟨a, hb⟩`. Establish `h3` using `hA _ n h2`. Establish `hkb : K.d (j + 1) (c ^ k • b) = 0` using `by rw [map_smul, hdb, smul_zero]`. Rewrite `h3` using `[← cls_smul _ _ hdb hkb, (CrystallineSemistableComparison.P.cls_surj K (j + 1)).2.1]`. Take `⟨e, he⟩` from `(mem_Bs _).1 h3`.

Establish `hy : K.d j (c ^ k • a - c ^ n • e) = 0`. Rewrite using `[map_sub, map_smul, map_smul, he, hb, smul_smul, smul_smul, mul_comm, sub_self]`. Establish `hr : r.f j (c ^ k • a - c ^ n • e) = c ^ k • r.f j a`. Rewrite using `[map_sub, (hk j _).2 ⟨e, rfl⟩, sub_zero, map_smul]`. Establish `hd : L.d j (c ^ k • r.f j a) = 0` using `by rw [map_smul, hw, smul_zero]`.

Use `⟨K.cls _ hy, ?_⟩` and prove the remaining obligations. Rewrite using `[mapH_cls' r _ hy (cyc r _ hy), ← cls_smul _ _ hw hd]`. Conclude with `cls_congr hr _ _`.
-/
theorem lift_level {K L : Cx.{1} R} (c : R) (n k j : ℕ) (r : Cx.Hom K L (RingHom.id R))
    (hs : ∀ j, Function.Surjective (r.f j)) (hk : ∀ j x, r.f j x = 0 ↔ ∃ y, x = c ^ n • y)
    (ht : ∀ j (x : K.X j), c • x = 0 → x = 0)
    (hA : ∀ (x : K.H (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0) (x : L.H j) :
    ∃ y : K.H j, r.mapH j y = c ^ k • x := by
  obtain ⟨w, hw, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L j).1 x
  obtain ⟨a, rfl⟩ := hs j w
  have h1 : r.f (j + 1) (K.d j a) = 0 := by rw [← r.comm]; exact hw
  obtain ⟨b, hb⟩ := (hk (j + 1) _).1 h1
  have hdb : K.d (j + 1) b = 0 := by
    refine pow_tf ht n _ _ ?_
    rw [← map_smul, ← hb, K.dd]
  have hcb : K.d (j + 1) (c ^ n • b) = 0 := by rw [map_smul, hdb, smul_zero]
  have h2 : c ^ n • K.cls b hdb = 0 := by
    rw [← cls_smul _ _ hdb hcb, (CrystallineSemistableComparison.P.cls_surj K (j + 1)).2.1]
    exact (mem_Bs _).2 ⟨a, hb⟩
  have h3 := hA _ n h2
  have hkb : K.d (j + 1) (c ^ k • b) = 0 := by rw [map_smul, hdb, smul_zero]
  rw [← cls_smul _ _ hdb hkb, (CrystallineSemistableComparison.P.cls_surj K (j + 1)).2.1] at h3
  obtain ⟨e, he⟩ := (mem_Bs _).1 h3
  have hy : K.d j (c ^ k • a - c ^ n • e) = 0 := by
    rw [map_sub, map_smul, map_smul, he, hb, smul_smul, smul_smul, mul_comm, sub_self]
  have hr : r.f j (c ^ k • a - c ^ n • e) = c ^ k • r.f j a := by
    rw [map_sub, (hk j _).2 ⟨e, rfl⟩, sub_zero, map_smul]
  have hd : L.d j (c ^ k • r.f j a) = 0 := by rw [map_smul, hw, smul_zero]
  refine ⟨K.cls _ hy, ?_⟩
  rw [mapH_cls' r _ hy (cyc r _ hy), ← cls_smul _ _ hw hd]
  exact cls_congr hr _ _

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj K j).1 z`. Rewrite using `[mapH_cls' r a ha (cyc r a ha), mapH_cls' t _ _ (cyc t _ (cyc r a ha)), mapH_cls' r' a ha (cyc r' a ha)]`. Conclude with `cls_congr (h a) _ _`.
-/
theorem mapH_tr {K L M : Cx.{1} R} (r : Cx.Hom K L (RingHom.id R)) (r' : Cx.Hom K M (RingHom.id R))
    (t : Cx.Hom L M (RingHom.id R)) (j : ℕ) (h : ∀ x, t.f j (r.f j x) = r'.f j x) (z : K.H j) :
    t.mapH j (r.mapH j z) = r'.mapH j z := by
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K j).1 z
  rw [mapH_cls' r a ha (cyc r a ha), mapH_cls' t _ _ (cyc t _ (cyc r a ha)), mapH_cls' r' a ha (cyc r' a ha)]
  exact cls_congr (h a) _ _

/- English proof (translation)
Introduce `R _ K Kn c red tr hc hs hk ht j k hA hB hC`. Use `⟨fun x hx => ?_, fun z hz => hB z fun n => ker_red c n (red n) (hs n) (hk n) ht j z (hz n)⟩` and prove the remaining obligations. Use `choose y hy using fun n => lift_level c n k j (red n) (hs n) (hk n) ht hA (x n)`. Establish `hdiff : ∀ n, ∃ u, y (n + 1) - y n = c ^ n • u`. Introduce `n`.

Use `ker_red c n (red n) (hs n) (hk n) ht j _ ?_` and prove the remaining obligations. Rewrite using `[map_sub, ← mapH_tr (red (n + 1)) (red n) (tr n) j (hc n j), hy, hy, map_smul, hx, sub_self]`. Take `⟨z, hz⟩` from `hC y hdiff`. Use `⟨z, fun n => ?_⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `hz n`.

Establish `e : z = c ^ k • y n + c ^ n • u` using `by rw [← hu]; abel`. Rewrite using `[e, map_add, map_smul, map_smul, hy, kill_H c n (red n) (hs n) (hk n), add_zero, smul_smul, ← pow_add, two_mul]`.
-/
theorem lim_lift : ∀ {R : Type} [CommRing R] {K : Cx.{1} R} (Kn : ℕ → Cx.{1} R) (c : R) (red : ∀ n, Cx.Hom K (Kn n) (RingHom.id R))
    (tr : ∀ n, Cx.Hom (Kn (n + 1)) (Kn n) (RingHom.id R)), (∀ n j x, (tr n).f j ((red (n + 1)).f j x) = (red n).f j x) →
    (∀ n j, Function.Surjective ((red n).f j)) → (∀ n j x, (red n).f j x = 0 ↔ ∃ y, x = c ^ n • y) → (∀ j (x : K.X j), c • x = 0 → x = 0) →
    ∀ j k : ℕ, (∀ (x : K.H (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0) → (∀ x : K.H j, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0) →
    (∀ x : ℕ → K.H j, (∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) → ∃ z : K.H j, ∀ n, ∃ y, z - c ^ k • x n = c ^ n • y) →
    (∀ x : ∀ n, (Kn n).H j, (∀ n, (tr n).mapH j (x (n + 1)) = x n) → ∃ z : K.H j, ∀ n, (red n).mapH j z = c ^ (2 * k) • x n) ∧
    ∀ z : K.H j, (∀ n, (red n).mapH j z = 0) → c ^ k • z = 0 := by
  intro R _ K Kn c red tr hc hs hk ht j k hA hB hC
  refine ⟨fun x hx => ?_, fun z hz => hB z fun n => ker_red c n (red n) (hs n) (hk n) ht j z (hz n)⟩
  choose y hy using fun n => lift_level c n k j (red n) (hs n) (hk n) ht hA (x n)
  have hdiff : ∀ n, ∃ u, y (n + 1) - y n = c ^ n • u := by
    intro n
    refine ker_red c n (red n) (hs n) (hk n) ht j _ ?_
    rw [map_sub, ← mapH_tr (red (n + 1)) (red n) (tr n) j (hc n j), hy, hy, map_smul, hx, sub_self]
  obtain ⟨z, hz⟩ := hC y hdiff
  refine ⟨z, fun n => ?_⟩
  obtain ⟨u, hu⟩ := hz n
  have e : z = c ^ k • y n + c ^ n • u := by rw [← hu]; abel
  rw [e, map_add, map_smul, map_smul, hy, kill_H c n (red n) (hs n) (hk n), add_zero, smul_smul, ← pow_add, two_mul]

end GlobalTheory.CompanionTheory.LimLift
