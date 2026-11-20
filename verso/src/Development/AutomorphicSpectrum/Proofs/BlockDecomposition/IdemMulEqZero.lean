import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.LcLogProof

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `ha' : a * a = a` using `ha`. Establish `hb' : b * b = b` using `hb`. Use `set d := a - b with hd`. Establish `hd3 : d * d * d = d`. Rewrite using `[hd]`.

Take the linear combination `(a + 1 - 3 * b) * ha' + (3 * a - b - 1) * hb'`. Establish `hmem : d ∈ Ideal.span {(l : A.W)}`. Rewrite using `[A.mem_span_l_iff, hd, ← WittVector.constantCoeff_apply, map_sub, sub_eq_zero]`. Conclude with `h`. Establish `hall : ∀ k : ℕ, d ∈ Ideal.span {(l : A.W)} ^ k`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[← hd3, pow_succ]`.

Conclude with `Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ ih) hmem`. Establish `h0 : d = 0` using `IsHausdorff.haus (A.completeW.toIsHausdorff) d fun k => by`. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top]`. Conclude with `hall k`. Conclude with `sub_eq_zero.1 h0`.
-/
theorem eq_of_idem (A : PAlg l) {a b : A.W} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (h : a.coeff 0 = b.coeff 0) : a = b := by
  have ha' : a * a = a := ha
  have hb' : b * b = b := hb
  set d := a - b with hd
  have hd3 : d * d * d = d := by
    rw [hd]
    linear_combination (a + 1 - 3 * b) * ha' + (3 * a - b - 1) * hb'
  have hmem : d ∈ Ideal.span {(l : A.W)} := by
    rw [A.mem_span_l_iff, hd, ← WittVector.constantCoeff_apply, map_sub, sub_eq_zero]
    exact h
  have hall : ∀ k : ℕ, d ∈ Ideal.span {(l : A.W)} ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← hd3, pow_succ]
      exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ ih) hmem
  have h0 : d = 0 := IsHausdorff.haus (A.completeW.toIsHausdorff) d fun k => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact hall k
  exact sub_eq_zero.1 h0

/- English proof (translation)
Establish `ho : OrthogonalIdempotents fun i => (WittVector.teichmuller l (e i) : A.W)` using `⟨fun i => by show _ * _ = _`. Rewrite using `[← map_mul, (he.idem i).eq],`. Use `fun i j hij => by show _ * _ = _`. Rewrite using `[← map_mul, he.ortho hij, WittVector.teichmuller_zero]⟩`. Use `eq_of_idem A ho.isIdempotentElem_sum IsIdempotentElem.one ?_` and prove the remaining obligations.

Use `show WittVector.constantCoeff (∑ a, (WittVector.teichmuller l (e a) : A.W)) = WittVector.constantCoeff (1 : A.W)`. Rewrite using `[map_sum, map_one]`. Simplify using `only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]`. Conclude with `he.complete`.
-/
theorem teich_sum_one (A : PAlg l) {ι : Type} [Fintype ι] {e : ι → A.A}
    (he : CompleteOrthogonalIdempotents e) : ∑ a, WittVector.teichmuller l (e a) = (1 : A.W) := by
  have ho : OrthogonalIdempotents fun i => (WittVector.teichmuller l (e i) : A.W) :=
    ⟨fun i => by
      show _ * _ = _
      rw [← map_mul, (he.idem i).eq],
     fun i j hij => by
      show _ * _ = _
      rw [← map_mul, he.ortho hij, WittVector.teichmuller_zero]⟩
  refine eq_of_idem A ho.isIdempotentElem_sum IsIdempotentElem.one ?_
  show WittVector.constantCoeff (∑ a, (WittVector.teichmuller l (e a) : A.W)) = WittVector.constantCoeff (1 : A.W)
  rw [map_sum, map_one]
  simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  exact he.complete

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, pow_succ, ← mul_assoc, ih]`. Take the linear combination `y ^ k * h`.
-/
theorem mul_pow_congr {R : Type*} [CommRing R] {s x y : R} (h : s * x = s * y) (k : ℕ) :
    s * x ^ k = s * y ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, ← mul_assoc, ih]
    linear_combination y ^ k * h

/- English proof (translation)
Take `⟨⟨_, k, rfl⟩, hk⟩` from `(IsLocalization.map_eq_zero_iff (Submonoid.powers c) _ x).1 h`. Consider the cases of `k with`. Consider the case `zero => simp only [pow_zero, one_mul] at hk`. Simplify using `[hk]`. Consider the case `succ k => simpa only [hc.pow_succ_eq] using hk`.
-/
theorem idem_mul_eq_zero {R : Type} [CommRing R] {c x : R} (hc : IsIdempotentElem c)
    (h : algebraMap R (Localization.Away c) x = 0) : c * x = 0 := by
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers c) _ x).1 h
  cases k with
  | zero => simp only [pow_zero, one_mul] at hk; simp [hk]
  | succ k => simpa only [hc.pow_succ_eq] using hk

/- English proof (translation)
Introduce `x y h` and use `by have := congrArg (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom h simpa [toΓ] using this`.
-/
theorem toΓ_injective (B : Type) [CommRing B] : Function.Injective (toΓ B) := fun x y h => by
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom h
  simpa [toΓ] using this

/- English proof (translation)
Establish `hv : ∀ v : Spec (CommRingCat.of (Localization.Away c)), f ((Spec.map (CommRingCat.ofHom (algebraMap A.Ug (Localization.Away c)))) v) = a`. Introduce `v`. Use `hf (PrimeSpectrum.comap (algebraMap A.Ug (Localization.Away c)) v) fun hm => ?_` and prove the remaining obligations. Establish `hu : IsUnit (algebraMap A.Ug (Localization.Away c) c)` using `IsLocalization.Away.algebraMap_isUnit c`. Establish `hm' : algebraMap A.Ug (Localization.Away c) c ∈ PrimeSpectrum.asIdeal v` using `hm`.

Conclude with `(PrimeSpectrum.isPrime v).ne_top (Ideal.eq_top_of_isUnit_mem _ hm' hu)`. Establish `h` using `hp _ (Spec.map (CommRingCat.ofHom (algebraMap A.Ug (Localization.Away c)))) a hv`. Establish `h2 : toΓ _ (algebraMap A.Ug (Localization.Away c) x) = toΓ _ (algebraMap A.Ug (Localization.Away c) (kb A (r.ρ n).1 ^ a.val))`. Rewrite using `[map_pow, map_pow, ← toΓ_nat, h, ← toΓ_nat]`. Both sides reduce to the same expression.

Use `idem_mul_eq_zero hc ?_` and prove the remaining obligations. Rewrite using `[map_sub, toΓ_injective _ h2, sub_self]`.
-/
theorem pow_on_part (r : Roots l) (A : PAlg l) (n : ℕ) (f : LocallyConstant (SU A) (ZMod (l ^ n))) (x : A.Ug)
    (hp : IsPow (r.zeta A n) f (toΓ A.Ug x)) (a : ZMod (l ^ n)) (c : A.Ug) (hc : IsIdempotentElem c)
    (hf : ∀ p : PrimeSpectrum A.Ug, c ∉ p.asIdeal → f p = a) :
    c * (x - kb A (r.ρ n).1 ^ a.val) = 0 := by
  have hv : ∀ v : Spec (CommRingCat.of (Localization.Away c)),
      f ((Spec.map (CommRingCat.ofHom (algebraMap A.Ug (Localization.Away c)))) v) = a := by
    intro v
    refine hf (PrimeSpectrum.comap (algebraMap A.Ug (Localization.Away c)) v) fun hm => ?_
    have hu : IsUnit (algebraMap A.Ug (Localization.Away c) c) := IsLocalization.Away.algebraMap_isUnit c
    have hm' : algebraMap A.Ug (Localization.Away c) c ∈ PrimeSpectrum.asIdeal v := hm
    exact (PrimeSpectrum.isPrime v).ne_top (Ideal.eq_top_of_isUnit_mem _ hm' hu)
  have h := hp _ (Spec.map (CommRingCat.ofHom (algebraMap A.Ug (Localization.Away c)))) a hv
  have h2 : toΓ _ (algebraMap A.Ug (Localization.Away c) x) =
      toΓ _ (algebraMap A.Ug (Localization.Away c) (kb A (r.ρ n).1 ^ a.val)) := by
    rw [map_pow, map_pow, ← toΓ_nat, h, ← toΓ_nat]
    rfl
  refine idem_mul_eq_zero hc ?_
  rw [map_sub, toΓ_injective _ h2, sub_self]

/- English proof (translation)
The claim follows from `IsLocalization.injective _ (Submonoid.powers_le.2 (H.tf A))`.
-/
theorem ug_injective (H : RIn l) (A : PAlg l) : Function.Injective (algebraMap A.U A.Ug) :=
  IsLocalization.injective _ (Submonoid.powers_le.2 (H.tf A))

/- English proof (translation)
Use `show A.cToUg (clToC l (r.ρ n).1) = _`. Rewrite using `[r.hρ]`. Conclude with `A.cToUg_coe (rootSeqInt l n)`.
-/
theorem kb_rho (r : Roots l) (A : PAlg l) (n : ℕ) :
    kb A (r.ρ n).1 = algebraMap A.U A.Ug (A.oC (rootSeqInt l n)) := by
  show A.cToUg (clToC l (r.ρ n).1) = _
  rw [r.hρ]
  exact A.cToUg_coe (rootSeqInt l n)

/- English proof (translation)
Rewrite using `[← map_pow, show rootSeqInt l n ^ l ^ n = 1 from Subtype.ext (rootSeq_pow n), map_one]`.
-/
theorem root_pow (A : PAlg l) (n : ℕ) : A.oC (rootSeqInt l n) ^ l ^ n = 1 := by
  rw [← map_pow, show rootSeqInt l n ^ l ^ n = 1 from Subtype.ext (rootSeq_pow n), map_one]

/- English proof (translation)
Take `⟨y, hy⟩` from `(hEx l A n).1 1 (map_one _)`. Establish `h` using `hMul l A n 1 1 y y (map_one _) (map_one _) hy hy`. Rewrite `h` using `[mul_one]`. Establish `h0 : y + y = y` using `(hEx l A n).2.1 _ _ _ h hy`. Establish `: y = 0` using `by linear_combination h0`.

Rewrite `hy` using `[this]`. Then use the resulting hypothesis.
-/
theorem isLog_one (hEx : LogEx) (hMul : LogMul) (A : PAlg l) (n : ℕ) : IsLog A n 1 0 := by
  obtain ⟨y, hy⟩ := (hEx l A n).1 1 (map_one _)
  have h := hMul l A n 1 1 y y (map_one _) (map_one _) hy hy
  rw [mul_one] at h
  have h0 : y + y = y := (hEx l A n).2.1 _ _ _ h hy
  have : y = 0 := by linear_combination h0
  rwa [this] at hy

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using isLog_one hEx hMul A n`. Consider the case `succ k ih`. Establish `h` using `hMul l A n (w ^ k) w _ _ (by rw [map_pow, h1, one_pow]) h1 ih hy`. Rewrite `h` using `[← pow_succ]`.

Establish `e : (k : A.Acr n) * y + y = ((k + 1 : ℕ) : A.Acr n) * y` using `by push_cast; ring`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem isLog_pow (hEx : LogEx) (hMul : LogMul) (A : PAlg l) (n : ℕ) {w : A.W} {y : A.Acr n} (h1 : A.th w = 1)
    (hy : IsLog A n w y) (k : ℕ) : IsLog A n (w ^ k) ((k : A.Acr n) * y) := by
  induction k with
  | zero => simpa using isLog_one hEx hMul A n
  | succ k ih =>
    have h := hMul l A n (w ^ k) w _ _ (by rw [map_pow, h1, one_pow]) h1 ih hy
    rw [← pow_succ] at h
    have e : (k : A.Acr n) * y + y = ((k + 1 : ℕ) : A.Acr n) * y := by push_cast; ring
    rwa [e] at h

/- English proof (translation)
Rewrite using `[Nat.cast_pow]`. Conclude with `A.pow_l_acr n`.
-/
theorem natCast_q (A : PAlg l) (n : ℕ) : ((l ^ n : ℕ) : A.Acr n) = 0 := by
  rw [Nat.cast_pow]; exact A.pow_l_acr n

/- English proof (translation)
Establish `hq : 1 ≤ l ^ n` using `Nat.one_le_pow _ _ (Fact.out : l.Prime).pos`. Take `⟨m, hm⟩ : ∃ m, m + v = l ^ n * v` from `⟨(l ^ n - 1) * v, by`. Rewrite using `[Nat.sub_mul, one_mul]`. Conclude with `Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hq)⟩`. Use `set E : A.W := WittVector.teichmuller l c with hEdef`.

Use `set U : A.W := WittVector.teichmuller l u with hU`. Use `set N : A.W := WittVector.teichmuller l η with hN`. Establish `hEi : E * E = E` using `by rw [hEdef, ← map_mul, hc.eq]`. Establish `hthE : A.th E = A.sharp c` using `rfl`. Establish `hthU : A.th U = A.sharp u` using `rfl`.

Establish `hthN : A.th N = A.sharp η` using `rfl`. Establish `hw1 : A.th (E * U * N ^ m + (1 - E)) = 1`. Establish `e1 : A.sharp η ^ (m + v) = 1` using `by rw [hm, pow_mul, hz, one_pow]`. Simplify using `only [map_add, map_sub, map_mul, map_pow, map_one, hthE, hthU, hthN]`. Rewrite `e1` using `[pow_add]`.

Take the linear combination `A.sharp η ^ m * hE + A.sharp c * e1`. Take `⟨yw, hyw⟩` from `(hEx l A n).1 _ hw1`. Establish `hwq` using `isLog_pow hEx hMul A n hw1 hyw (l ^ n)`. Rewrite `hwq` using `[natCast_q, zero_mul]`. Establish `hε1 : A.th (WittVector.teichmuller l (A.s (epsilon l))) = 1`.

Rewrite using `[← hη]`. Conclude with `(map_pow A.sharp η (l ^ n)).trans hz`. Establish `hεm` using `isLog_pow hEx hMul A n hε1 (hEps l A n) m`. Establish `hprod` using `hMul l A n _ _ _ _ h1 (by rw [map_pow, hε1, one_pow]) hy hεm`. Establish `hid : E * (E * U * N ^ m + (1 - E)) ^ l ^ n = E * (WittVector.teichmuller l (u ^ l ^ n) * WittVector.teichmuller l (A.s (epsilon l)) ^ m)`.

Establish `h2 : E * (E * U * N ^ m + (1 - E)) = E * (U * N ^ m)`. Take the linear combination `(U * N ^ m - 1) * hEi`. Rewrite using `[mul_pow_congr h2, ← hη, map_pow, map_pow, ← hU, ← hN, mul_pow, ← pow_mul, ← pow_mul, mul_comm m]`. Establish `key` using `(hEx l A n).2.2 E _ _ _ _ (show IsIdempotentElem E from hEi) hid hwq hprod`. Establish `hm' : (m : A.Acr n) + (v : A.Acr n) = 0`.

Use `congrArg (Nat.cast : ℕ → A.Acr n) hm` as an intermediate fact. Rewrite `this` using `[Nat.cast_add, Nat.cast_mul, natCast_q, zero_mul]`. Conclude with `this`. Take the linear combination `(-1 : A.Acr n) * key + (A.toAcr n E * A.cris n (ACris.periodT (untilt_epsilon (p := l)))) * (-hm')`.
-/
theorem log_on_part (hEx : LogEx) (hMul : LogMul) (hEps : LogEps) (A : PAlg l) (n : ℕ) {η u c : A.A} {v : ℕ}
    (hη : η ^ l ^ n = A.s (epsilon l)) (hz : A.sharp η ^ l ^ n = 1) (hc : IsIdempotentElem c)
    (hE : A.sharp c * (A.sharp u - A.sharp η ^ v) = 0) {y : A.Acr n}
    (h1 : A.th (WittVector.teichmuller l (u ^ l ^ n)) = 1)
    (hy : IsLog A n (WittVector.teichmuller l (u ^ l ^ n)) y) :
    A.toAcr n (WittVector.teichmuller l c) * y = A.toAcr n (WittVector.teichmuller l c) * ((v : A.Acr n) *
      A.cris n (ACris.periodT (untilt_epsilon (p := l)))) := by
  have hq : 1 ≤ l ^ n := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
  obtain ⟨m, hm⟩ : ∃ m, m + v = l ^ n * v := ⟨(l ^ n - 1) * v, by
    rw [Nat.sub_mul, one_mul]; exact Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hq)⟩
  set E : A.W := WittVector.teichmuller l c with hEdef
  set U : A.W := WittVector.teichmuller l u with hU
  set N : A.W := WittVector.teichmuller l η with hN
  have hEi : E * E = E := by rw [hEdef, ← map_mul, hc.eq]
  have hthE : A.th E = A.sharp c := rfl
  have hthU : A.th U = A.sharp u := rfl
  have hthN : A.th N = A.sharp η := rfl

  have hw1 : A.th (E * U * N ^ m + (1 - E)) = 1 := by
    have e1 : A.sharp η ^ (m + v) = 1 := by rw [hm, pow_mul, hz, one_pow]
    simp only [map_add, map_sub, map_mul, map_pow, map_one, hthE, hthU, hthN]
    rw [pow_add] at e1
    linear_combination A.sharp η ^ m * hE + A.sharp c * e1
  obtain ⟨yw, hyw⟩ := (hEx l A n).1 _ hw1
  have hwq := isLog_pow hEx hMul A n hw1 hyw (l ^ n)
  rw [natCast_q, zero_mul] at hwq

  have hε1 : A.th (WittVector.teichmuller l (A.s (epsilon l))) = 1 := by
    rw [← hη]; exact (map_pow A.sharp η (l ^ n)).trans hz
  have hεm := isLog_pow hEx hMul A n hε1 (hEps l A n) m
  have hprod := hMul l A n _ _ _ _ h1 (by rw [map_pow, hε1, one_pow]) hy hεm
  have hid : E * (E * U * N ^ m + (1 - E)) ^ l ^ n =
      E * (WittVector.teichmuller l (u ^ l ^ n) * WittVector.teichmuller l (A.s (epsilon l)) ^ m) := by
    have h2 : E * (E * U * N ^ m + (1 - E)) = E * (U * N ^ m) := by
      linear_combination (U * N ^ m - 1) * hEi
    rw [mul_pow_congr h2, ← hη, map_pow, map_pow, ← hU, ← hN, mul_pow, ← pow_mul, ← pow_mul, mul_comm m]
  have key := (hEx l A n).2.2 E _ _ _ _ (show IsIdempotentElem E from hEi) hid hwq hprod
  have hm' : (m : A.Acr n) + (v : A.Acr n) = 0 := by
    have := congrArg (Nat.cast : ℕ → A.Acr n) hm
    rw [Nat.cast_add, Nat.cast_mul, natCast_q, zero_mul] at this
    exact this
  linear_combination (-1 : A.Acr n) * key + (A.toAcr n E * A.cris n (ACris.periodT (untilt_epsilon (p := l)))) * (-hm')

/- English proof (translation)
Introduce `hI hS _ hEx hMul hEps hR l _ H r A hA n u f hp`. Take `⟨η, hη, hsh⟩` from `hR l n`. Take `⟨e, he, hiff, -⟩` from `hI l H A hA (ZMod (l ^ n)) f`. Establish `hz : A.sharp (A.s η) ^ l ^ n = 1` using `by rw [hsh A]; exact root_pow A n`. Establish `hη' : (A.s η) ^ l ^ n = A.s (epsilon l)` using `by rw [← map_pow, hη]`.

Establish `hid : ∀ a, IsIdempotentElem (A.sharp (e a))` using `fun a => by show _ * _ = _`. Rewrite using `[← map_mul, (he.idem a).eq]`. Establish `hE : ∀ a : ZMod (l ^ n), A.sharp (e a) * (A.sharp u - A.sharp (A.s η) ^ a.val) = 0`. Introduce `a`. Establish `hidg : IsIdempotentElem (algebraMap A.U A.Ug (A.sharp (e a)))` using `(hid a).map _`.

Establish `h` using `pow_on_part r A n f _ hp a _ hidg (fun p hpn => (hiff a p).1 hpn)`. Rewrite `h` using `[kb_rho]`. Apply `ug_injective H A` to reduce the goal to its premises. Rewrite using `[map_zero, ← h, hsh A]`. Simplify using `only [map_mul, map_sub, map_pow]`.

Establish `hsum : ∑ a, A.sharp (e a) = 1`. Use `congrArg A.th (teich_sum_one A he)` as an intermediate fact. Rewrite `this` using `[map_sum, map_one]`. Then use the resulting hypothesis. Establish `h1 : A.th (WittVector.teichmuller l (u ^ l ^ n)) = 1`. Establish `e0 : A.th (WittVector.teichmuller l (u ^ l ^ n)) = A.sharp u ^ l ^ n` using `map_pow A.sharp u _`.

Rewrite using `[e0, ← one_mul (A.sharp u ^ l ^ n), ← hsum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `h2 : A.sharp (e a) * A.sharp u = A.sharp (e a) * A.sharp (A.s η) ^ a.val`. Take the linear combination `hE a`. Rewrite using `[mul_pow_congr h2, ← pow_mul, mul_comm a.val, pow_mul, hz, one_pow, mul_one]`.

Take `⟨y, hy⟩` from `(hEx l A n).1 _ h1`. Establish `hloc` using `fun a : ZMod (l ^ n) => log_on_part hEx hMul hEps A n hη' hz (he.idem a) (hE a) h1 hy`. Establish `hsumA : ∑ a, A.toAcr n (WittVector.teichmuller l (e a)) = 1`. Rewrite using `[← map_sum, teich_sum_one A he, map_one]`. Establish `hlc` using `((hS l H A hA n).2.2.2 f e he (fun a p hpn => (hiff a p).1 hpn))`.

Establish `hfin : y = (ACris.periodT (untilt_epsilon (p` using `l)) : Acris l) • lcA A n f := by`. Rewrite using `[Algebra.smul_def, hlc]`. Use `show y = A.cris n _ * _`. Rewrite using `[← one_mul y, ← hsumA, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[hloc a]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hfin]` and apply the resulting hypothesis.
-/
theorem lcLog : CrystallineSemistableComparison.E.LcIdem → CrystallineSemistableComparison.E.LcSpec → CrystallineSemistableComparison.E.LcCover → CrystallineSemistableComparison.E.LogEx → CrystallineSemistableComparison.E.LogMul → CrystallineSemistableComparison.E.LogEps →
    CrystallineSemistableComparison.E.EpsRoot → CrystallineSemistableComparison.E.LcLog := by
  intro hI hS _ hEx hMul hEps hR l _ H r A hA n u f hp
  obtain ⟨η, hη, hsh⟩ := hR l n
  obtain ⟨e, he, hiff, -⟩ := hI l H A hA (ZMod (l ^ n)) f
  have hz : A.sharp (A.s η) ^ l ^ n = 1 := by rw [hsh A]; exact root_pow A n
  have hη' : (A.s η) ^ l ^ n = A.s (epsilon l) := by rw [← map_pow, hη]
  have hid : ∀ a, IsIdempotentElem (A.sharp (e a)) := fun a => by
    show _ * _ = _
    rw [← map_mul, (he.idem a).eq]
  have hE : ∀ a : ZMod (l ^ n), A.sharp (e a) * (A.sharp u - A.sharp (A.s η) ^ a.val) = 0 := by
    intro a
    have hidg : IsIdempotentElem (algebraMap A.U A.Ug (A.sharp (e a))) := (hid a).map _
    have h := pow_on_part r A n f _ hp a _ hidg (fun p hpn => (hiff a p).1 hpn)
    rw [kb_rho] at h
    apply ug_injective H A
    rw [map_zero, ← h, hsh A]
    simp only [map_mul, map_sub, map_pow]
  have hsum : ∑ a, A.sharp (e a) = 1 := by
    have := congrArg A.th (teich_sum_one A he)
    rwa [map_sum, map_one] at this
  have h1 : A.th (WittVector.teichmuller l (u ^ l ^ n)) = 1 := by
    have e0 : A.th (WittVector.teichmuller l (u ^ l ^ n)) = A.sharp u ^ l ^ n := map_pow A.sharp u _
    rw [e0, ← one_mul (A.sharp u ^ l ^ n), ← hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h2 : A.sharp (e a) * A.sharp u = A.sharp (e a) * A.sharp (A.s η) ^ a.val := by
      linear_combination hE a
    rw [mul_pow_congr h2, ← pow_mul, mul_comm a.val, pow_mul, hz, one_pow, mul_one]
  obtain ⟨y, hy⟩ := (hEx l A n).1 _ h1
  have hloc := fun a : ZMod (l ^ n) => log_on_part hEx hMul hEps A n hη' hz (he.idem a) (hE a) h1 hy
  have hsumA : ∑ a, A.toAcr n (WittVector.teichmuller l (e a)) = 1 := by
    rw [← map_sum, teich_sum_one A he, map_one]
  have hlc := ((hS l H A hA n).2.2.2 f e he (fun a p hpn => (hiff a p).1 hpn))
  have hfin : y = (ACris.periodT (untilt_epsilon (p := l)) : Acris l) • lcA A n f := by
    rw [Algebra.smul_def, hlc]
    show y = A.cris n _ * _
    rw [← one_mul y, ← hsumA, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hloc a]; ring
  rwa [← hfin]

end GlobalTheory.CompanionTheory.LcLogProof
