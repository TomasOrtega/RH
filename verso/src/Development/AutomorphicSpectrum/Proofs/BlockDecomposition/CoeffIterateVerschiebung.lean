import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LcSp

section Witt

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]

/- English proof (translation)
Proceed by induction on `m generalizing i with`. Consider the case `zero => omega`. Consider the case `succ m ih`. Rewrite using `[Function.iterate_succ_apply']`. Consider the cases of `i with`.

Consider the case `zero => exact WittVector.verschiebung_coeff_zero _`. Consider the case `succ i`. Rewrite using `[WittVector.verschiebung_coeff_succ]`. Conclude with `ih i (by omega)`.
-/
theorem coeff_iterate_verschiebung (m : ℕ) (y : WittVector p R) (i : ℕ) (h : i < m) :
    (WittVector.verschiebung^[m] y).coeff i = 0 := by
  induction m generalizing i with
  | zero => omega
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    cases i with
    | zero => exact WittVector.verschiebung_coeff_zero _
    | succ i =>
      rw [WittVector.verschiebung_coeff_succ]
      exact ih i (by omega)

/- English proof (translation)
Establish `key : ∀ n, ∀ i < n + 1, u.coeff i = 0`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `i hi`.

Take `rfl : i = 0` from `by omega`. Conclude with `h0`. Consider the case `succ n ih`. Introduce `i hi`. Distinguish the cases in `h : i < n + 1`.

Conclude with `ih i h`. Take `rfl : i = n + 1` from `by omega`. Take `⟨y, e⟩ : ∃ y, u = WittVector.verschiebung^[n + 1] y` from `⟨_, WittVector.eq_iterate_verschiebung ih⟩`. Establish `e2 : u = WittVector.verschiebung^[(n + 1) + (n + 1)] (WittVector.frobenius^[n + 1] y * WittVector.frobenius^[n + 1] y)`. Rewrite using `[← WittVector.iterate_verschiebung_mul, ← e, hu]`.

Rewrite using `[e2]`. Conclude with `coeff_iterate_verschiebung _ _ _ (by omega)`. Use extensionality with `i`. Rewrite using `[key i i (by omega)]`. Simplify using the standard rewrite rules.
-/
theorem idem_eq_zero (u : WittVector p R) (hu : u * u = u) (h0 : u.coeff 0 = 0) : u = 0 := by
  have key : ∀ n, ∀ i < n + 1, u.coeff i = 0 := by
    intro n
    induction n with
    | zero =>
      intro i hi
      obtain rfl : i = 0 := by omega
      exact h0
    | succ n ih =>
      intro i hi
      by_cases h : i < n + 1
      · exact ih i h
      obtain rfl : i = n + 1 := by omega
      obtain ⟨y, e⟩ : ∃ y, u = WittVector.verschiebung^[n + 1] y := ⟨_, WittVector.eq_iterate_verschiebung ih⟩
      have e2 : u = WittVector.verschiebung^[(n + 1) + (n + 1)]
          (WittVector.frobenius^[n + 1] y * WittVector.frobenius^[n + 1] y) := by
        rw [← WittVector.iterate_verschiebung_mul, ← e, hu]
      rw [e2]
      exact coeff_iterate_verschiebung _ _ _ (by omega)
  ext i
  rw [key i i (by omega)]
  simp

/- English proof (translation)
Establish `ho : OrthogonalIdempotents fun i => WittVector.teichmuller p (e i)` using `{ idem := fun i => by`. Express the relevant statement in the definitionally equal form `_ * _ = _`. Rewrite using `[← map_mul, (he.idem i).eq]`. Use `ortho := fun i j hij => by`. Express the relevant statement in the definitionally equal form `_ * _ = _`.

Rewrite using `[← map_mul, he.ortho hij, WittVector.teichmuller_zero] }`. Establish `hs : IsIdempotentElem (∑ i, WittVector.teichmuller p (e i))` using `ho.isIdempotentElem_sum`. Establish `h1 : (1 : WittVector p R) - ∑ i, WittVector.teichmuller p (e i) = 0`. Use `idem_eq_zero _ hs.one_sub.eq ?_` and prove the remaining obligations. Rewrite using `[← WittVector.constantCoeff_apply, map_sub, map_one, map_sum]`.

Simplify using `only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]`. Rewrite using `[he.complete, sub_self]`. Conclude with `(sub_eq_zero.1 h1).symm`.
-/
theorem sum_teichmuller {ι : Type} [Fintype ι] (e : ι → R) (he : CompleteOrthogonalIdempotents e) :
    ∑ i, WittVector.teichmuller p (e i) = (1 : WittVector p R) := by
  have ho : OrthogonalIdempotents fun i => WittVector.teichmuller p (e i) :=
    { idem := fun i => by
        change _ * _ = _
        rw [← map_mul, (he.idem i).eq]
      ortho := fun i j hij => by
        change _ * _ = _
        rw [← map_mul, he.ortho hij, WittVector.teichmuller_zero] }
  have hs : IsIdempotentElem (∑ i, WittVector.teichmuller p (e i)) := ho.isIdempotentElem_sum
  have h1 : (1 : WittVector p R) - ∑ i, WittVector.teichmuller p (e i) = 0 := by
    refine idem_eq_zero _ hs.one_sub.eq ?_
    rw [← WittVector.constantCoeff_apply, map_sub, map_one, map_sum]
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    rw [he.complete, sub_self]
  exact (sub_eq_zero.1 h1).symm

end Witt

variable {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ)

/- English proof (translation)
Break down `subsingleton_or_nontrivial A.A with h | h` into its components or cases. Conclude with `WittVector.ext fun _ => Subsingleton.elim _ _`. Use `haveI : CharP A.A l := (CharP.charP_iff_prime_eq_zero Fact.out).2 A.natCast_l`. Conclude with `sum_teichmuller e he`.
-/
theorem sum_teich {ι : Type} [Fintype ι] (e : ι → A.A) (he : CompleteOrthogonalIdempotents e) :
    ∑ i, WittVector.teichmuller l (e i) = (1 : A.W) := by
  rcases subsingleton_or_nontrivial A.A with h | h
  · exact WittVector.ext fun _ => Subsingleton.elim _ _
  · haveI : CharP A.A l := (CharP.charP_iff_prime_eq_zero Fact.out).2 A.natCast_l
    exact sum_teichmuller e he

/- English proof (translation)
Establish `hs : ∑ i, A.toAcr n (WittVector.teichmuller l (e i)) = 1`. Rewrite using `[← map_sum, sum_teich A e he, map_one]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => h i`.

Use `_ = y := by rw [hs, one_mul]`.
-/
theorem acr_ext {ι : Type} [Fintype ι] (e : ι → A.A) (he : CompleteOrthogonalIdempotents e) {x y : A.Acr n}
    (h : ∀ i, A.toAcr n (WittVector.teichmuller l (e i)) * x = A.toAcr n (WittVector.teichmuller l (e i)) * y) :
    x = y := by
  have hs : ∑ i, A.toAcr n (WittVector.teichmuller l (e i)) = 1 := by
    rw [← map_sum, sum_teich A e he, map_one]
  calc x = (∑ i, A.toAcr n (WittVector.teichmuller l (e i))) * x := by rw [hs, one_mul]
    _ = (∑ i, A.toAcr n (WittVector.teichmuller l (e i))) * y := by
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => h i
    _ = y := by rw [hs, one_mul]

/- English proof (translation)
Use `haveI : CharP (A.Acr n) (ringChar (A.Acr n)) := ringChar.charP _`. Establish `hd : ringChar (A.Acr n) ∣ l ^ n` using `(CharP.cast_eq_zero_iff (A.Acr n) (ringChar (A.Acr n)) (l ^ n)).1 (by`. Rewrite using `[Nat.cast_pow]`. Conclude with `A.pow_l_acr n)`. Use `⟨ZMod.castHom hd _, fun a => ?_⟩` and prove the remaining obligations.

Rewrite using `[ZMod.castHom_apply, ZMod.natCast_val]`.
-/
theorem exists_cast : ∃ c : ZMod (l ^ n) →+* A.Acr n, ∀ a, c a = (a.val : A.Acr n) := by
  haveI : CharP (A.Acr n) (ringChar (A.Acr n)) := ringChar.charP _
  have hd : ringChar (A.Acr n) ∣ l ^ n :=
    (CharP.cast_eq_zero_iff (A.Acr n) (ringChar (A.Acr n)) (l ^ n)).1 (by
      rw [Nat.cast_pow]
      exact A.pow_l_acr n)
  refine ⟨ZMod.castHom hd _, fun a => ?_⟩
  rw [ZMod.castHom_apply, ZMod.natCast_val]

variable {A n}

section Main

variable (hI : LcIdem) (H : RIn l) (hA : A.IsTest)
include hI H hA

/- English proof (translation)
Take `⟨e, he, -, h2⟩` from `hI l H A hA (ZMod (l ^ n)) f`. Use `⟨∑ a, A.toAcr n (WittVector.teichmuller l (e a)) * (a.val : A.Acr n), fun e' a he' hf => ?_⟩` and prove the remaining obligations. Establish `h3 : e' * e a = e'` using `h2 e' a he' hf`. Rewrite using `[Finset.mul_sum, Finset.sum_eq_single a]`. Rewrite using `[← mul_assoc, ← map_mul, ← map_mul, h3]`.

Introduce `b _ hb`. Establish `h4 : e' * e b = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← map_mul, ← map_mul, h4, WittVector.teichmuller_zero, map_zero, zero_mul]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ a) h`.
-/
theorem exists_isLcA (f : LocallyConstant (SU A) (ZMod (l ^ n))) : ∃ x, IsLcA A n f x := by
  obtain ⟨e, he, -, h2⟩ := hI l H A hA (ZMod (l ^ n)) f
  refine ⟨∑ a, A.toAcr n (WittVector.teichmuller l (e a)) * (a.val : A.Acr n), fun e' a he' hf => ?_⟩
  have h3 : e' * e a = e' := h2 e' a he' hf
  rw [Finset.mul_sum, Finset.sum_eq_single a]
  · rw [← mul_assoc, ← map_mul, ← map_mul, h3]
  · intro b _ hb
    have h4 : e' * e b = 0 := by
      calc e' * e b = e' * e a * e b := by rw [h3]
        _ = 0 := by rw [mul_assoc, he.ortho hb.symm, mul_zero]
    rw [← mul_assoc, ← map_mul, ← map_mul, h4, WittVector.teichmuller_zero, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

/- English proof (translation)
Take `⟨e, he, h1, -⟩` from `hI l H A hA (ZMod (l ^ n)) f`. Use `acr_ext A n e he fun a => ?_` and prove the remaining obligations. Establish `hf : ∀ p : PrimeSpectrum A.Ug, algebraMap A.U A.Ug (A.sharp (e a)) ∉ p.asIdeal → f p = a` using `fun p hp => (h1 a p).1 hp`. Rewrite using `[hx (e a) a (he.idem a) hf, hy (e a) a (he.idem a) hf]`.
-/
theorem isLcA_unique {f : LocallyConstant (SU A) (ZMod (l ^ n))} {x y : A.Acr n}
    (hx : IsLcA A n f x) (hy : IsLcA A n f y) : x = y := by
  obtain ⟨e, he, h1, -⟩ := hI l H A hA (ZMod (l ^ n)) f
  refine acr_ext A n e he fun a => ?_
  have hf : ∀ p : PrimeSpectrum A.Ug, algebraMap A.U A.Ug (A.sharp (e a)) ∉ p.asIdeal → f p = a :=
    fun p hp => (h1 a p).1 hp
  rw [hx (e a) a (he.idem a) hf, hy (e a) a (he.idem a) hf]

/- English proof (translation)
Take `⟨c, hc⟩` from `exists_cast A n`. Take `⟨e, he, -, h2⟩` from `hI l H A hA (ZMod (l ^ n)) 1`. Introduce `e' a he' hf`. Distinguish the cases in `ha : a = 1`. Substitute `ha` using the available equality.

Rewrite using `[← hc, map_one]`. Establish `h3 : e' * e a = e'` using `h2 e' a he' hf`. Establish `h4 : e' * e 1 = e'` using `h2 e' 1 he' fun _ _ => rfl`. Establish `h5 : e' = 0`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[h5, WittVector.teichmuller_zero, map_zero, zero_mul, zero_mul]`.
-/
theorem isLcA_one : IsLcA A n 1 1 := by
  obtain ⟨c, hc⟩ := exists_cast A n
  obtain ⟨e, he, -, h2⟩ := hI l H A hA (ZMod (l ^ n)) 1
  intro e' a he' hf
  by_cases ha : a = 1
  · subst ha
    rw [← hc, map_one]
  · have h3 : e' * e a = e' := h2 e' a he' hf
    have h4 : e' * e 1 = e' := h2 e' 1 he' fun _ _ => rfl
    have h5 : e' = 0 := by
      calc e' = e' * e 1 * e a := by rw [h4, h3]
        _ = 0 := by rw [mul_assoc, he.ortho (Ne.symm ha), mul_zero]
    rw [h5, WittVector.teichmuller_zero, map_zero, zero_mul, zero_mul]

/- English proof (translation)
Set `h : LocallyConstant (SU A) (ZMod (l ^ n) × ZMod (l ^ n))` to `⟨fun p => (f p, g p), f.isLocallyConstant.prodMk g.isLocallyConstant⟩`. Take `⟨e, he, h1, -⟩` from `hI l H A hA _ h`. Use `⟨e, he, fun ab p hp => ?_⟩` and prove the remaining obligations. Establish `h2 : (f p, g p) = ab` using `(h1 ab p).1 hp`. Conclude with `⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩`.
-/
theorem exists_pair (f g : LocallyConstant (SU A) (ZMod (l ^ n))) :
    ∃ e : ZMod (l ^ n) × ZMod (l ^ n) → A.A, CompleteOrthogonalIdempotents e ∧
      ∀ (ab : ZMod (l ^ n) × ZMod (l ^ n)) (p : PrimeSpectrum A.Ug),
        algebraMap A.U A.Ug (A.sharp (e ab)) ∉ p.asIdeal → f p = ab.1 ∧ g p = ab.2 := by
  let h : LocallyConstant (SU A) (ZMod (l ^ n) × ZMod (l ^ n)) :=
    ⟨fun p => (f p, g p), f.isLocallyConstant.prodMk g.isLocallyConstant⟩
  obtain ⟨e, he, h1, -⟩ := hI l H A hA _ h
  refine ⟨e, he, fun ab p hp => ?_⟩
  have h2 : (f p, g p) = ab := (h1 ab p).1 hp
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

/- English proof (translation)
Take `⟨e, he, h⟩` from `exists_pair hI H hA f g`. Take `⟨c, hc⟩` from `exists_cast A n`. Use `acr_ext A n e he fun ab => ?_` and prove the remaining obligations. Establish `h1` using `hx (e ab) ab.1 (he.idem ab) fun p hp => (h ab p hp).1`. Establish `h2` using `hy (e ab) ab.2 (he.idem ab) fun p hp => (h ab p hp).2`.

Establish `h3` using `hz (e ab) (ab.1 + ab.2) (he.idem ab) fun p hp => by`. Express the relevant statement in the definitionally equal form `f p + g p = _`. Rewrite using `[(h ab p hp).1, (h ab p hp).2]`. Rewrite using `[h3, mul_add, h1, h2, ← hc, ← hc, ← hc, map_add, mul_add]`.
-/
theorem isLcA_add {f g : LocallyConstant (SU A) (ZMod (l ^ n))} {x y z : A.Acr n}
    (hx : IsLcA A n f x) (hy : IsLcA A n g y) (hz : IsLcA A n (f + g) z) : z = x + y := by
  obtain ⟨e, he, h⟩ := exists_pair hI H hA f g
  obtain ⟨c, hc⟩ := exists_cast A n
  refine acr_ext A n e he fun ab => ?_
  have h1 := hx (e ab) ab.1 (he.idem ab) fun p hp => (h ab p hp).1
  have h2 := hy (e ab) ab.2 (he.idem ab) fun p hp => (h ab p hp).2
  have h3 := hz (e ab) (ab.1 + ab.2) (he.idem ab) fun p hp => by
    change f p + g p = _
    rw [(h ab p hp).1, (h ab p hp).2]
  rw [h3, mul_add, h1, h2, ← hc, ← hc, ← hc, map_add, mul_add]

/- English proof (translation)
Take `⟨e, he, h⟩` from `exists_pair hI H hA f g`. Take `⟨c, hc⟩` from `exists_cast A n`. Use `acr_ext A n e he fun ab => ?_` and prove the remaining obligations. Establish `h1` using `hx (e ab) ab.1 (he.idem ab) fun p hp => (h ab p hp).1`. Establish `h2` using `hy (e ab) ab.2 (he.idem ab) fun p hp => (h ab p hp).2`.

Establish `h3` using `hz (e ab) (ab.1 * ab.2) (he.idem ab) fun p hp => by`. Express the relevant statement in the definitionally equal form `f p * g p = _`. Rewrite using `[(h ab p hp).1, (h ab p hp).2]`. Establish `ht : A.toAcr n (WittVector.teichmuller l (e ab)) * A.toAcr n (WittVector.teichmuller l (e ab)) = A.toAcr n (WittVector.teichmuller l (e ab))`. Rewrite using `[← map_mul, ← map_mul, (he.idem ab).eq]`.

Rewrite `h1`, `h2`, `h3` using `[← hc]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_mul_mul_comm, ht]`. Use `_ = (A.toAcr n (WittVector.teichmuller l (e ab)) * x) * (A.toAcr n (WittVector.teichmuller l (e ab)) * y) := by`. Rewrite using `[h1, h2]`.

Use `_ = _ := by rw [mul_mul_mul_comm, ht]`.
-/
theorem isLcA_mul {f g : LocallyConstant (SU A) (ZMod (l ^ n))} {x y z : A.Acr n}
    (hx : IsLcA A n f x) (hy : IsLcA A n g y) (hz : IsLcA A n (f * g) z) : z = x * y := by
  obtain ⟨e, he, h⟩ := exists_pair hI H hA f g
  obtain ⟨c, hc⟩ := exists_cast A n
  refine acr_ext A n e he fun ab => ?_
  have h1 := hx (e ab) ab.1 (he.idem ab) fun p hp => (h ab p hp).1
  have h2 := hy (e ab) ab.2 (he.idem ab) fun p hp => (h ab p hp).2
  have h3 := hz (e ab) (ab.1 * ab.2) (he.idem ab) fun p hp => by
    change f p * g p = _
    rw [(h ab p hp).1, (h ab p hp).2]
  have ht : A.toAcr n (WittVector.teichmuller l (e ab)) * A.toAcr n (WittVector.teichmuller l (e ab)) =
      A.toAcr n (WittVector.teichmuller l (e ab)) := by
    rw [← map_mul, ← map_mul, (he.idem ab).eq]
  rw [← hc] at h1 h2 h3
  calc _ = A.toAcr n (WittVector.teichmuller l (e ab)) * (c ab.1 * c ab.2) := by rw [h3, map_mul]
    _ = (A.toAcr n (WittVector.teichmuller l (e ab)) * c ab.1) * (A.toAcr n (WittVector.teichmuller l (e ab)) * c ab.2) := by
      rw [mul_mul_mul_comm, ht]
    _ = (A.toAcr n (WittVector.teichmuller l (e ab)) * x) * (A.toAcr n (WittVector.teichmuller l (e ab)) * y) := by
      rw [h1, h2]
    _ = _ := by rw [mul_mul_mul_comm, ht]

end Main

/- English proof (translation)
Introduce `hI l _ H A hA n`. Establish `P : ∃ κ : LocallyConstant (SU A) (ZMod (l ^ n)) →+ A.Acr n, ∀ f, IsLcA A n f (κ f)` using `by choose k hk using exists_isLcA (n := n) hI H hA`. Conclude with `⟨AddMonoidHom.mk' k fun f g => isLcA_add hI H hA (hk f) (hk g) (hk (f + g)), hk⟩`. Establish `S : ∀ f, IsLcA A n f (lcA A n f)` using `pick_spec P`. Use `⟨S, isLcA_unique hI H hA (S 1) (isLcA_one hI H hA), fun f g => isLcA_mul hI H hA (S f) (S g) (S (f * g)), fun f e he h => ?_⟩` and prove the remaining obligations.

Use `acr_ext A n e he fun a => ?_` and prove the remaining obligations. Rewrite using `[S f (e a) a (he.idem a) (h a), Finset.mul_sum, Finset.sum_eq_single a]`. Rewrite using `[← mul_assoc, ← map_mul, ← map_mul, (he.idem a).eq]`. Introduce `b _ hb`. Rewrite using `[← mul_assoc, ← map_mul, ← map_mul, he.ortho hb.symm, WittVector.teichmuller_zero, map_zero, zero_mul]`.

Introduce `h'`. Conclude with `absurd (Finset.mem_univ a) h'`.
-/
theorem lcSpec_of_lcIdem : CrystallineSemistableComparison.E.LcIdem → CrystallineSemistableComparison.E.LcSpec := by
  intro hI l _ H A hA n
  have P : ∃ κ : LocallyConstant (SU A) (ZMod (l ^ n)) →+ A.Acr n, ∀ f, IsLcA A n f (κ f) := by
    choose k hk using exists_isLcA (n := n) hI H hA
    exact ⟨AddMonoidHom.mk' k fun f g => isLcA_add hI H hA (hk f) (hk g) (hk (f + g)), hk⟩
  have S : ∀ f, IsLcA A n f (lcA A n f) := pick_spec P
  refine ⟨S, isLcA_unique hI H hA (S 1) (isLcA_one hI H hA),
    fun f g => isLcA_mul hI H hA (S f) (S g) (S (f * g)), fun f e he h => ?_⟩
  refine acr_ext A n e he fun a => ?_
  rw [S f (e a) a (he.idem a) (h a), Finset.mul_sum, Finset.sum_eq_single a]
  · rw [← mul_assoc, ← map_mul, ← map_mul, (he.idem a).eq]
  · intro b _ hb
    rw [← mul_assoc, ← map_mul, ← map_mul, he.ortho hb.symm, WittVector.teichmuller_zero, map_zero, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ a) h'

end GlobalTheory.CompanionTheory.LcSp
