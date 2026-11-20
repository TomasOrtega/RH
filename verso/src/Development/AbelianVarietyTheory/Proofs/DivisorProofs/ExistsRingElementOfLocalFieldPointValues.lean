import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Establish `hloc' : ∀ k : {p : Ideal R // p.IsPrime}, ∃ f ∉ k.1, ∃ c : Localization.Away f, ∀ (K : Type) [Field K] (j : Localization.Away f →+* K), P K (j.comp (algebraMap R (Localization.Away f))) (j c)` using `fun k => hloc k.1 k.2`. Use `choose f hf c hc using hloc'`. Establish `hsurj : ∀ k : {p : Ideal R // p.IsPrime}, ∃ (a : R) (n : ℕ), c k * algebraMap R _ (f k ^ n) = algebraMap R _ a`. Introduce `k`. Take `⟨n, a, h⟩` from `IsLocalization.Away.surj (f k) (c k)`.

Conclude with `⟨a, n, by rw [map_pow]; exact h⟩`. Use `choose a n ha using hsurj`. Establish `key : ∀ (K : Type) [Field K] (i : R →+* K) (k : {p : Ideal R // p.IsPrime}), i (f k) ≠ 0 → ∃ v, P K i v ∧ v * i (f k) ^ n k = i (a k)`. Introduce `K _ i k hk`. Set `j : Localization.Away (f k) →+* K` to `IsLocalization.Away.lift (f k) (isUnit_iff_ne_zero.mpr hk)`.

Apply the tactic sequence `have hj : j.comp (algebraMap R _) = i := by first | exact IsLocalization.Away.lift_comp _ | exact IsLocalization.lift_comp _`. Use `⟨j (c k), ?_, ?_⟩` and prove the remaining obligations. Use `hc k K j` as an intermediate fact. Rewrite `this` using `[hj]`. Then use the resulting hypothesis. Establish `h2` using `congrArg j (ha k)`.

Rewrite `h2` using `[map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply, hj, map_pow]`. Conclude with `h2`. Establish `hnil : ∀ k l : {p : Ideal R // p.IsPrime}, IsNilpotent (f k * f l * (a k * f l ^ n l - a l * f k ^ n k))`. Introduce `k l`. Rewrite using `[← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]`.

Introduce `q hq`. Use `haveI : q.IsPrime := hq`. Distinguish the cases in `hk : f k ∈ q`. Conclude with `q.mul_mem_right _ (q.mul_mem_right _ hk)`. Distinguish the cases in `hl : f l ∈ q`.

Conclude with `q.mul_mem_right _ (q.mul_mem_left _ hl)`. Apply `q.mul_mem_left` to reduce the goal to its premises. Establish `hker : RingHom.ker (algebraMap R q.ResidueField) = q` using `Ideal.ker_algebraMap_residueField q`. Establish `hik : algebraMap R q.ResidueField (f k) ≠ 0` using `fun h => hk (hker ▸ RingHom.mem_ker.mpr h)`. Establish `hil : algebraMap R q.ResidueField (f l) ≠ 0` using `fun h => hl (hker ▸ RingHom.mem_ker.mpr h)`.

Take `⟨v, hv, hv'⟩` from `key _ (algebraMap R q.ResidueField) k hik`. Take `⟨w, hw, hw'⟩` from `key _ (algebraMap R q.ResidueField) l hil`. Establish `hvw` using `huniq _ _ v w hv hw`. Substitute `hvw` using the available equality. Rewrite using `[← hker, RingHom.mem_ker, map_sub, map_mul, map_mul, map_pow, map_pow, ← hv', ← hw']`.

Expand and normalize the polynomial expressions, which then agree. Set `g : {p : Ideal R // p.IsPrime} → R` to `fun k => f k ^ (n k + 1)`. Set `α : {p : Ideal R // p.IsPrime} → R` to `fun k => f k * a k`. Establish `hspan : Ideal.span (Set.range g) = ⊤`. Assume the negation of the conclusion as `hne`.

Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal _ hne`. Set `k : {p : Ideal R // p.IsPrime}` to `⟨m, hm.isPrime⟩`. Conclude with `hf k (hm.isPrime.mem_of_pow_mem _ (hle (Ideal.subset_span ⟨k, rfl⟩)))`. Establish `h1 : (1 : R) ∈ Submodule.span R (Set.range g)`. Rewrite using `[← Ideal.span, hspan]`.

Conclude with `Submodule.mem_top`. Take `⟨b, hb⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.mp h1`. Set `π` to `Ideal.Quotient.mk (nilradical R)`. Establish `hrel : ∀ k l, π (g l) * π (α k) = π (g k) * π (α l)`. Introduce `k l`.

Rewrite using `[← map_mul, ← map_mul, Ideal.Quotient.eq, mem_nilradical]`. Establish `e : g l * α k - g k * α l = f k * f l * (a k * f l ^ n l - a l * f k ^ n k)`. Simplify using `only [g, α]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `hnil k l`. Take `⟨c0, hc0⟩` from `Ideal.Quotient.mk_surjective (I := nilradical R) (b.sum fun k r => π r * π (α k))`. Establish `hb' : (b.sum fun k r => π r * π (g k)) = 1`. Use `congrArg π hb` as an intermediate fact. Simplify `this` using `[Finsupp.sum, map_sum, smul_eq_mul]`.

Establish `hglue : ∀ l, IsNilpotent (g l * c0 - α l)`. Introduce `l`. Rewrite using `[← mem_nilradical, ← Ideal.Quotient.eq]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul]`.

Express the relevant statement in the definitionally equal form `π (g l) * Ideal.Quotient.mk (nilradical R) c0 = _`. Rewrite using `[hc0, Finsupp.mul_sum]`. Use `Finsupp.sum_congr fun k _ => ?_` and prove the remaining obligations. Take the linear combination `π (b k) * hrel k l`. Use `_ = π (α l) := by rw [← Finsupp.sum_mul, hb', _root_.one_mul]`.

Use `⟨c0, fun K _ i => ?_⟩` and prove the remaining obligations. Set `k : {p : Ideal R // p.IsPrime}` to `⟨RingHom.ker i, RingHom.ker_isPrime i⟩`. Establish `hik : i (f k) ≠ 0` using `fun h => hf k (RingHom.mem_ker.mpr h)`. Take `⟨v, hv, hv'⟩` from `key K i k hik`. Establish `h0 : i (g k * c0 - α k) = 0` using `((hglue k).map i).eq_zero`.

Establish `hcv : i c0 = v`. Establish `hp : i (f k) ^ (n k + 1) ≠ 0` using `pow_ne_zero _ hik`. Apply `mul_left_cancel₀ hp` to reduce the goal to its premises. Simplify using `only [g, α, map_sub, map_mul, map_pow, sub_eq_zero] at h0`. Rewrite using `[h0, ← hv']`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hcv]`. Conclude with `hv`.
-/
theorem glue_field_points (R : Type) [CommRing R]
    (P : (K : Type) → [Field K] → (R →+* K) → K → Prop)
    (huniq : ∀ (K : Type) [Field K] (i : R →+* K) (u v : K), P K i u → P K i v → u = v)
    (hloc : ∀ p : Ideal R, p.IsPrime → ∃ f ∉ p, ∃ c : Localization.Away f,
      ∀ (K : Type) [Field K] (j : Localization.Away f →+* K),
        P K (j.comp (algebraMap R (Localization.Away f))) (j c)) :
    ∃ c : R, ∀ (K : Type) [Field K] (i : R →+* K), P K i (i c) := by
  classical
  have hloc' : ∀ k : {p : Ideal R // p.IsPrime}, ∃ f ∉ k.1, ∃ c : Localization.Away f,
      ∀ (K : Type) [Field K] (j : Localization.Away f →+* K),
        P K (j.comp (algebraMap R (Localization.Away f))) (j c) := fun k => hloc k.1 k.2
  choose f hf c hc using hloc'
  have hsurj : ∀ k : {p : Ideal R // p.IsPrime}, ∃ (a : R) (n : ℕ),
      c k * algebraMap R _ (f k ^ n) = algebraMap R _ a := by
    intro k
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (f k) (c k)
    exact ⟨a, n, by rw [map_pow]; exact h⟩
  choose a n ha using hsurj

  have key : ∀ (K : Type) [Field K] (i : R →+* K) (k : {p : Ideal R // p.IsPrime}),
      i (f k) ≠ 0 → ∃ v, P K i v ∧ v * i (f k) ^ n k = i (a k) := by
    intro K _ i k hk
    let j : Localization.Away (f k) →+* K :=
      IsLocalization.Away.lift (f k) (isUnit_iff_ne_zero.mpr hk)
    have hj : j.comp (algebraMap R _) = i := by first | exact IsLocalization.Away.lift_comp _ | exact IsLocalization.lift_comp _
    refine ⟨j (c k), ?_, ?_⟩
    · have := hc k K j
      rwa [hj] at this
    · have h2 := congrArg j (ha k)
      rw [map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply, hj, map_pow] at h2
      exact h2

  have hnil : ∀ k l : {p : Ideal R // p.IsPrime},
      IsNilpotent (f k * f l * (a k * f l ^ n l - a l * f k ^ n k)) := by
    intro k l
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
    intro q hq
    haveI : q.IsPrime := hq
    by_cases hk : f k ∈ q
    · exact q.mul_mem_right _ (q.mul_mem_right _ hk)
    by_cases hl : f l ∈ q
    · exact q.mul_mem_right _ (q.mul_mem_left _ hl)
    apply q.mul_mem_left
    have hker : RingHom.ker (algebraMap R q.ResidueField) = q := Ideal.ker_algebraMap_residueField q
    have hik : algebraMap R q.ResidueField (f k) ≠ 0 := fun h => hk (hker ▸ RingHom.mem_ker.mpr h)
    have hil : algebraMap R q.ResidueField (f l) ≠ 0 := fun h => hl (hker ▸ RingHom.mem_ker.mpr h)
    obtain ⟨v, hv, hv'⟩ := key _ (algebraMap R q.ResidueField) k hik
    obtain ⟨w, hw, hw'⟩ := key _ (algebraMap R q.ResidueField) l hil
    have hvw := huniq _ _ v w hv hw
    subst hvw
    rw [← hker, RingHom.mem_ker, map_sub, map_mul, map_mul, map_pow, map_pow, ← hv', ← hw']
    ring

  let g : {p : Ideal R // p.IsPrime} → R := fun k => f k ^ (n k + 1)
  let α : {p : Ideal R // p.IsPrime} → R := fun k => f k * a k
  have hspan : Ideal.span (Set.range g) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let k : {p : Ideal R // p.IsPrime} := ⟨m, hm.isPrime⟩
    exact hf k (hm.isPrime.mem_of_pow_mem _ (hle (Ideal.subset_span ⟨k, rfl⟩)))
  have h1 : (1 : R) ∈ Submodule.span R (Set.range g) := by
    rw [← Ideal.span, hspan]; exact Submodule.mem_top
  obtain ⟨b, hb⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h1
  let π := Ideal.Quotient.mk (nilradical R)
  have hrel : ∀ k l, π (g l) * π (α k) = π (g k) * π (α l) := by
    intro k l
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, mem_nilradical]
    have e : g l * α k - g k * α l = f k * f l * (a k * f l ^ n l - a l * f k ^ n k) := by
      simp only [g, α]; ring
    rw [e]; exact hnil k l
  obtain ⟨c0, hc0⟩ := Ideal.Quotient.mk_surjective (I := nilradical R)
    (b.sum fun k r => π r * π (α k))
  have hb' : (b.sum fun k r => π r * π (g k)) = 1 := by
    have := congrArg π hb
    simpa [Finsupp.sum, map_sum, smul_eq_mul] using this
  have hglue : ∀ l, IsNilpotent (g l * c0 - α l) := by
    intro l
    rw [← mem_nilradical, ← Ideal.Quotient.eq]
    calc π (g l * c0) = b.sum (fun k r => π r * π (g k) * π (α l)) := by
          rw [map_mul]
          change π (g l) * Ideal.Quotient.mk (nilradical R) c0 = _
          rw [hc0, Finsupp.mul_sum]
          refine Finsupp.sum_congr fun k _ => ?_
          linear_combination π (b k) * hrel k l
      _ = π (α l) := by rw [← Finsupp.sum_mul, hb', _root_.one_mul]
  refine ⟨c0, fun K _ i => ?_⟩
  let k : {p : Ideal R // p.IsPrime} := ⟨RingHom.ker i, RingHom.ker_isPrime i⟩
  have hik : i (f k) ≠ 0 := fun h => hf k (RingHom.mem_ker.mpr h)
  obtain ⟨v, hv, hv'⟩ := key K i k hik
  have h0 : i (g k * c0 - α k) = 0 := ((hglue k).map i).eq_zero
  have hcv : i c0 = v := by
    have hp : i (f k) ^ (n k + 1) ≠ 0 := pow_ne_zero _ hik
    apply mul_left_cancel₀ hp
    simp only [g, α, map_sub, map_mul, map_pow, sub_eq_zero] at h0
    rw [h0, ← hv']; ring
  rw [hcv]; exact hv

end GlobalTheory
