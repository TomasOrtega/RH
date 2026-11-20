import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRingHomPowPrimePow

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

/- English proof (translation)
Introduce `p _ B _ T _ π g hC hB`. Establish `hp0 : 0 < p` using `(Fact.out : p.Prime).pos`. Establish `hT : (p : T) = 0` using `by rw [← map_natCast g p, hB.char, map_zero]`. Take `⟨FB, hFB⟩` from `GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p B hB.char 1`. Take `⟨FT, hFT⟩` from `GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p T hT 1`.

Establish `subB : ∀ x y : B, (x - y) ^ p = x ^ p - y ^ p` using `fun x y => by`. Establish `h` using `map_sub FB x y`. Simplify `h` using `only [hFB, pow_one]`. Establish `subT : ∀ x y : T, (x - y) ^ p = x ^ p - y ^ p` using `fun x y => by`. Establish `h` using `map_sub FT x y`.

Simplify `h` using `only [hFT, pow_one]`. Establish `surj' : ∀ (M : ℕ) (y : T), ∃ x, g π ^ M ∣ y - g x` using `fun M y => by`. Take `⟨x, hx⟩` from `hC.surj M y`. Conclude with `⟨x, Ideal.mem_span_singleton.1 hx⟩`. Establish `inj' : ∀ (M : ℕ) (x : B), g π ^ M ∣ g x → π ^ M ∣ x` using `fun M x h => Ideal.mem_span_singleton.1 (hC.inj M x (Ideal.mem_span_singleton.2 h))`.

Establish `root : ∀ (M : ℕ) (b : B), π ^ (p * M) ∣ b ^ p → π ^ M ∣ b`. Introduce and unpack `M b ⟨c, hc⟩`. Take `⟨d, hd⟩` from `hB.bij.2 c`. Establish `hd' : d ^ p = c` using `hd`. Use `⟨d, hB.bij.1 (show b ^ p = (π ^ M * d) ^ p from ?_)⟩` and prove the remaining obligations.

Rewrite using `[hc, mul_pow, ← pow_mul, mul_comm M p, hd']`. Establish `haus : ∀ x : T, (∀ n : ℕ, g π ^ n ∣ x) → x = 0`. Introduce `x hx`. Use `hC.compl.toIsHausdorff.haus x fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.

Conclude with `hx n`. Establish `dvdp : ∀ (n : ℕ) (x : T), g π ^ n ∣ x → g π ^ n ∣ x ^ p` using `fun n x h => h.trans (dvd_pow_self x hp0.ne')`. Use `⟨hT, ?_, ?_⟩` and prove the remaining obligations. Introduce `z w hzw`. Establish `hzw' : z ^ p = w ^ p` using `hzw`.

Rewrite using `[← sub_eq_zero]`. Establish `h0 : (z - w) ^ p = 0` using `by rw [subT, hzw', sub_self]`. Apply `haus` to reduce the goal to its premises. Introduce `M`. Take `⟨b, hb⟩` from `surj' (p * M) (z - w)`.

Establish `h1 : g π ^ (p * M) ∣ g (b ^ p)`. Establish `h2 : (z - w - g b) ^ p = (z - w) ^ p - g b ^ p` using `subT _ _`. Rewrite `h2` using `[h0, zero_sub]`. Establish `h3 : g π ^ (p * M) ∣ (z - w - g b) ^ p` using `dvdp _ _ hb`. Rewrite `h3` using `[h2, dvd_neg]`.

Rewrite using `[map_pow]` and apply the resulting hypothesis. Establish `h4 : π ^ M ∣ b` using `root M b (inj' _ _ h1)`. Establish `h5 : g π ^ M ∣ g b`. Rewrite using `[← map_pow]`. Conclude with `map_dvd g h4`.

Establish `h6 : g π ^ M ∣ z - w - g b` using `(pow_dvd_pow _ (Nat.le_mul_of_pos_left M hp0)).trans hb`. Establish `h7` using `dvd_add h6 h5`. Rewrite `h7` using `[sub_add_cancel]`. Then use the resulting hypothesis. Introduce `y choose b hb using fun M : ℕ => surj' (p * M) y choose e he using fun M : ℕ => hB.bij.2 (b M)`. Establish `he' : ∀ M, e M ^ p = b M` using `he`.

Establish `cauchy : ∀ m n : ℕ, m ≤ n → π ^ m ∣ e m - e n`. Introduce `m n hmn`. Apply `root` to reduce the goal to its premises. Rewrite using `[subB, he', he']`. Apply `inj'` to reduce the goal to its premises.

Establish `h1 : g π ^ (p * m) ∣ y - g (b n)` using `(pow_dvd_pow _ (Nat.mul_le_mul le_rfl hmn)).trans (hb n)`. Establish `h2` using `dvd_sub h1 (hb m)`. Rewrite using `[map_sub]`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Take `⟨L, hL⟩` from `hC.compl.toIsPrecomplete.prec (f := fun n => g (e n)) (fun {m n} hmn => by beta_reduce`. Rewrite using `[SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_sub, ← map_pow]`. Conclude with `map_dvd g (cauchy m n hmn))`. Use `⟨L, ?_⟩` and prove the remaining obligations. Use `show L ^ p = y`.

Rewrite using `[← sub_eq_zero]`. Apply `haus` to reduce the goal to its premises. Introduce `n`. Establish `hn : g π ^ n ∣ g (e n) - L`. Establish `h3` using `hL n`.

Rewrite `h3` using `[SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Then use the resulting hypothesis. Establish `h1 : g π ^ n ∣ (g (e n) - L) ^ p` using `dvdp _ _ hn`. Rewrite `h1` using `[subT, ← map_pow g (e n) p, he']`. Establish `h2 : g π ^ n ∣ y - g (b n)` using `(pow_dvd_pow _ (Nat.le_mul_of_pos_left n hp0)).trans (hb n)`. Establish `h4` using `dvd_add h1 h2`.

Rewrite using `[← dvd_neg]`. Use `h4 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pf_of_isCompl : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (T : Type) [CommRing T]
    (π : B) (g : B →+* T), IsCompl π g → Pf p B → Pf p T := by
  intro p _ B _ T _ π g hC hB
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hT : (p : T) = 0 := by rw [← map_natCast g p, hB.char, map_zero]
  obtain ⟨FB, hFB⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p B hB.char 1
  obtain ⟨FT, hFT⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p T hT 1
  have subB : ∀ x y : B, (x - y) ^ p = x ^ p - y ^ p := fun x y => by
    have h := map_sub FB x y
    simpa only [hFB, pow_one] using h
  have subT : ∀ x y : T, (x - y) ^ p = x ^ p - y ^ p := fun x y => by
    have h := map_sub FT x y
    simpa only [hFT, pow_one] using h
  have surj' : ∀ (M : ℕ) (y : T), ∃ x, g π ^ M ∣ y - g x := fun M y => by
    obtain ⟨x, hx⟩ := hC.surj M y
    exact ⟨x, Ideal.mem_span_singleton.1 hx⟩
  have inj' : ∀ (M : ℕ) (x : B), g π ^ M ∣ g x → π ^ M ∣ x := fun M x h =>
    Ideal.mem_span_singleton.1 (hC.inj M x (Ideal.mem_span_singleton.2 h))
  have root : ∀ (M : ℕ) (b : B), π ^ (p * M) ∣ b ^ p → π ^ M ∣ b := by
    rintro M b ⟨c, hc⟩
    obtain ⟨d, hd⟩ := hB.bij.2 c
    have hd' : d ^ p = c := hd
    refine ⟨d, hB.bij.1 (show b ^ p = (π ^ M * d) ^ p from ?_)⟩
    rw [hc, mul_pow, ← pow_mul, mul_comm M p, hd']
  have haus : ∀ x : T, (∀ n : ℕ, g π ^ n ∣ x) → x = 0 := by
    intro x hx
    refine hC.compl.toIsHausdorff.haus x fun n => ?_
    rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact hx n
  have dvdp : ∀ (n : ℕ) (x : T), g π ^ n ∣ x → g π ^ n ∣ x ^ p := fun n x h =>
    h.trans (dvd_pow_self x hp0.ne')
  refine ⟨hT, ?_, ?_⟩
  · intro z w hzw
    have hzw' : z ^ p = w ^ p := hzw
    rw [← sub_eq_zero]
    have h0 : (z - w) ^ p = 0 := by rw [subT, hzw', sub_self]
    apply haus
    intro M
    obtain ⟨b, hb⟩ := surj' (p * M) (z - w)
    have h1 : g π ^ (p * M) ∣ g (b ^ p) := by
      have h2 : (z - w - g b) ^ p = (z - w) ^ p - g b ^ p := subT _ _
      rw [h0, zero_sub] at h2
      have h3 : g π ^ (p * M) ∣ (z - w - g b) ^ p := dvdp _ _ hb
      rw [h2, dvd_neg] at h3
      rwa [map_pow]
    have h4 : π ^ M ∣ b := root M b (inj' _ _ h1)
    have h5 : g π ^ M ∣ g b := by
      rw [← map_pow]
      exact map_dvd g h4
    have h6 : g π ^ M ∣ z - w - g b := (pow_dvd_pow _ (Nat.le_mul_of_pos_left M hp0)).trans hb
    have h7 := dvd_add h6 h5
    rwa [sub_add_cancel] at h7
  · intro y
    choose b hb using fun M : ℕ => surj' (p * M) y
    choose e he using fun M : ℕ => hB.bij.2 (b M)
    have he' : ∀ M, e M ^ p = b M := he
    have cauchy : ∀ m n : ℕ, m ≤ n → π ^ m ∣ e m - e n := by
      intro m n hmn
      apply root
      rw [subB, he', he']
      apply inj'
      have h1 : g π ^ (p * m) ∣ y - g (b n) :=
        (pow_dvd_pow _ (Nat.mul_le_mul le_rfl hmn)).trans (hb n)
      have h2 := dvd_sub h1 (hb m)
      rw [map_sub]
      convert h2 using 1
      ring
    obtain ⟨L, hL⟩ := hC.compl.toIsPrecomplete.prec (f := fun n => g (e n)) (fun {m n} hmn => by
      beta_reduce
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton, ← map_sub, ← map_pow]
      exact map_dvd g (cauchy m n hmn))
    refine ⟨L, ?_⟩
    show L ^ p = y
    rw [← sub_eq_zero]
    apply haus
    intro n
    have hn : g π ^ n ∣ g (e n) - L := by
      have h3 := hL n
      rwa [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton] at h3
    have h1 : g π ^ n ∣ (g (e n) - L) ^ p := dvdp _ _ hn
    rw [subT, ← map_pow g (e n) p, he'] at h1
    have h2 : g π ^ n ∣ y - g (b n) :=
      (pow_dvd_pow _ (Nat.le_mul_of_pos_left n hp0)).trans (hb n)
    have h4 := dvd_add h1 h2
    rw [← dvd_neg]
    convert h4 using 1
    ring

end GlobalTheory.CompanionTheory.PerfectRing
