import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassGroupDedekindAlgClosedDivisibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinitzPiIdealsLinearEquivOfClassGroupProd

open scoped nonZeroDivisors
open GlobalTheory.EtC

namespace GlobalTheory.KummerDiv

variable {B : Type} [CommRing B] [IsDedekindDomain B]

/- English proof (translation)
Rewrite using `[isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]`. Introduce `p hp`. Establish `h1 : (p.comap (Ideal.Quotient.mk I)).IsMaximal`. Use `Ring.DimensionLEOne.maximalOfPrime ?_ inferInstance` and prove the remaining obligations. Introduce `h`.

Apply `hI` to reduce the goal to its premises. Rewrite using `[eq_bot_iff, ← h]`. Introduce `x hx`. Simplify using `[Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]`. Establish `h2` using `Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective p`.

Break down `Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective h1 with h | h` into its components or cases. Conclude with `absurd (h2 ▸ h) hp.ne_top`. Conclude with `h2 ▸ h`.
-/
theorem artinian_quot {I : Ideal B} (hI : I ≠ ⊥) : IsArtinianRing (B ⧸ I) := by
  rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
  intro p hp
  have h1 : (p.comap (Ideal.Quotient.mk I)).IsMaximal := by
    refine Ring.DimensionLEOne.maximalOfPrime ?_ inferInstance
    intro h
    apply hI
    rw [eq_bot_iff, ← h]
    intro x hx
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have h2 := Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective p
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective h1 with h | h
  · exact absurd (h2 ▸ h) hp.ne_top
  · exact h2 ▸ h

/- English proof (translation)
Use `haveI := artinian_quot (I := Ideal.span {b}) (by simpa using hb)`. Take `⟨N, y, hy⟩` from `IsArtinian.exists_pow_succ_smul_dvd (Ideal.Quotient.mk (Ideal.span {b}) f) (1 : B ⧸ Ideal.span {b})`. Take `⟨y', rfl⟩` from `Ideal.Quotient.mk_surjective y`. Establish `hmem : f ^ N - f ^ (N + 1) * y' ∈ Ideal.span {b}`. Rewrite using `[← Ideal.Quotient.eq]`.

Simplify using `only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at hy`. Rewrite using `[map_mul, map_pow, map_pow, hy]`. Use `set P := Ideal.span {b} ⊔ Ideal.span {f ^ N} with hPdef`. Establish `hbP : Ideal.span {b} ≤ P` using `le_sup_left`. Take `⟨Q, hQ⟩` from `Ideal.dvd_iff_le.2 hbP`.

Use `⟨N, Q, hQ, ?_⟩` and prove the remaining obligations. Establish `hP0 : P ≠ 0`. Introduce `h`. Apply `hb` to reduce the goal to its premises. Establish `: b ∈ P` using `hbP (Ideal.mem_span_singleton_self b)`.

Rewrite `this` using `[h]`. Simplify using `using this`. Establish `key : P * (Q ⊔ Ideal.span {f}) = P * ⊤`. Rewrite using `[Ideal.mul_top, Ideal.mul_sup, ← hQ]`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `sup_le hbP Ideal.mul_le_left`. Apply `sup_le le_sup_left` to reduce the goal to its premises. Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Establish `e : f ^ N = (f ^ N - f ^ (N + 1) * y') + f ^ N * y' * f` using `by ring`. Rewrite using `[e]`.

Use `add_mem (Ideal.mem_sup_left hmem) (Ideal.mem_sup_right ?_)` and prove the remaining obligations. Conclude with `Ideal.mul_mem_mul (Ideal.mul_mem_right _ _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))) (Ideal.mem_span_singleton_self f)`. Conclude with `mul_left_cancel₀ hP0 key`.
-/
theorem exists_split (f b : B) (hb : b ≠ 0) :
    ∃ (N : ℕ) (Q : Ideal B), Ideal.span {b} = (Ideal.span {b} ⊔ Ideal.span {f ^ N}) * Q ∧
      Q ⊔ Ideal.span {f} = ⊤ := by
  haveI := artinian_quot (I := Ideal.span {b}) (by simpa using hb)
  obtain ⟨N, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd
    (Ideal.Quotient.mk (Ideal.span {b}) f) (1 : B ⧸ Ideal.span {b})
  obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
  have hmem : f ^ N - f ^ (N + 1) * y' ∈ Ideal.span {b} := by
    rw [← Ideal.Quotient.eq]
    simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at hy
    rw [map_mul, map_pow, map_pow, hy]
  set P := Ideal.span {b} ⊔ Ideal.span {f ^ N} with hPdef
  have hbP : Ideal.span {b} ≤ P := le_sup_left
  obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.2 hbP
  refine ⟨N, Q, hQ, ?_⟩
  have hP0 : P ≠ 0 := by
    intro h
    apply hb
    have : b ∈ P := hbP (Ideal.mem_span_singleton_self b)
    rw [h] at this
    simpa using this
  have key : P * (Q ⊔ Ideal.span {f}) = P * ⊤ := by
    rw [Ideal.mul_top, Ideal.mul_sup, ← hQ]
    apply le_antisymm
    · exact sup_le hbP Ideal.mul_le_left
    · apply sup_le le_sup_left
      rw [Ideal.span_singleton_le_iff_mem]
      have e : f ^ N = (f ^ N - f ^ (N + 1) * y') + f ^ N * y' * f := by ring
      rw [e]
      refine add_mem (Ideal.mem_sup_left hmem) (Ideal.mem_sup_right ?_)
      exact Ideal.mul_mem_mul (Ideal.mul_mem_right _ _ (Ideal.mem_sup_right
        (Ideal.mem_span_singleton_self _))) (Ideal.mem_span_singleton_self f)
  exact mul_left_cancel₀ hP0 key

/- English proof (translation)
Establish `h1 : (1 : B) ∈ I ⊔ Ideal.span {f}` using `h ▸ Submodule.mem_top`. Take `⟨a, ha, y, hy, hay⟩` from `Submodule.mem_sup.1 h1`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Distinguish the cases in `ha0 : a = 0`. Substitute `ha0` using the available equality.

Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`. Conclude with `⟨x, hx, hx0, ⟨c, 0, by simpa using hay⟩⟩`. Conclude with `⟨a, ha, ha0, ⟨c, 1, by linear_combination hay⟩⟩`.
-/
theorem exists_mem_coprime {I : Ideal B} (hI : I ≠ ⊥) (f : B) (h : I ⊔ Ideal.span {f} = ⊤) :
    ∃ g ∈ I, g ≠ 0 ∧ IsCoprime f g := by
  have h1 : (1 : B) ∈ I ⊔ Ideal.span {f} := h ▸ Submodule.mem_top
  obtain ⟨a, ha, y, hy, hay⟩ := Submodule.mem_sup.1 h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  by_cases ha0 : a = 0
  · subst ha0
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    exact ⟨x, hx, hx0, ⟨c, 0, by simpa using hay⟩⟩
  · exact ⟨a, ha, ha0, ⟨c, 1, by linear_combination hay⟩⟩

/- English proof (translation)
Rewrite `h`, the goal using `[Ideal.isCoprime_iff_sup_eq]`. Conclude with `eq_top_iff.2 (h ▸ sup_le_sup_left hle I)`.
-/
theorem isCoprime_ideal_of_le {I J J' : Ideal B} (h : IsCoprime I J) (hle : J ≤ J') :
    IsCoprime I J' := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  exact eq_top_iff.2 (h ▸ sup_le_sup_left hle I)

end GlobalTheory.KummerDiv

namespace GlobalTheory.KummerDiv

variable {B : Type} [CommRing B] [IsDedekindDomain B]

/- English proof (translation)
Take `⟨N, Q, hQ, hQf⟩` from `exists_split f b hb`. Use `set P := Ideal.span {b} ⊔ Ideal.span {f ^ N} with hPdef`. Establish `hQ0 : Q ≠ ⊥`. Introduce and unpack `rfl`. Apply `hb` to reduce the goal to its premises.

Simplify using `using hQ`. Establish `hf0 : Ideal.span {f} ≠ ⊥` using `by simpa using hf`. Set `Q' : (Ideal B)⁰` to `⟨Q, mem_nonZeroDivisors_of_ne_zero hQ0⟩`. Take `⟨c, hc⟩` from `hdiv (ClassGroup.mk0 Q')⁻¹`. Take `⟨J, hJf, hJc⟩` from `GlobalTheory.SteinitzProd.classGroup_exists_integral_ideal_coprime hf0 c`.

Establish `hmemQJ : Q * (J : Ideal B) ^ q ∈ (Ideal B)⁰` using `(Q' * J ^ q).2`. Establish `h1 : ClassGroup.mk0 ⟨Q * (J : Ideal B) ^ q, hmemQJ⟩ = 1`. Establish `: (⟨Q * (J : Ideal B) ^ q, hmemQJ⟩ : (Ideal B)⁰) = Q' * J ^ q` using `Subtype.ext (by simp [Q'])`. Rewrite using `[this, map_mul, map_pow, hJc, hc, mul_inv_cancel]`. Take `⟨n, hn⟩` from `((ClassGroup.mk0_eq_one_iff hmemQJ).1 h1).principal`.

Establish `hn' : Q * (J : Ideal B) ^ q = Ideal.span {n}` using `hn`. Establish `hJ0 : (J : Ideal B) ≠ ⊥` using `by simpa using nonZeroDivisors.coe_ne_zero J`. Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Establish `: Q * (J : Ideal B) ^ q = ⊥` using `by rw [hn']; simp`.

Break down `Ideal.mul_eq_bot.1 this with h | h` into its components or cases. Conclude with `hQ0 h`. Conclude with `hJ0 (pow_eq_zero_iff hq |>.1 h)`. Establish `cQ : IsCoprime (Ideal.span {f}) Q`. Rewrite using `[Ideal.isCoprime_iff_sup_eq, sup_comm]`.

Conclude with `hQf`. Establish `cJ : IsCoprime (Ideal.span {f}) (J : Ideal B)`. Rewrite using `[Ideal.isCoprime_iff_sup_eq, sup_comm]`. Conclude with `hJf`. Establish `hfn : IsCoprime f n`.

Rewrite using `[← Ideal.isCoprime_span_singleton_iff, ← hn']`. Conclude with `cQ.mul_right (cJ.pow_right)`. Establish `hQJ0 : Q * (J : Ideal B) ≠ ⊥` using `mul_ne_zero hQ0 hJ0`. Establish `hQJf : Q * (J : Ideal B) ⊔ Ideal.span {f} = ⊤`. Rewrite using `[← Ideal.isCoprime_iff_sup_eq]`.

Conclude with `(cQ.mul_right cJ).symm`. Take `⟨g, hgQJ, hg0, hfg⟩` from `exists_mem_coprime hQJ0 f hQJf`. Establish `hg0' : Ideal.span {g} ≠ ⊥` using `by simpa using hg0`. Take `⟨J₂, hJ₂g, hJ₂c⟩` from `GlobalTheory.SteinitzProd.classGroup_exists_integral_ideal_coprime hg0' (ClassGroup.mk0 J)⁻¹`. Establish `hmemJJ : (J : Ideal B) * (J₂ : Ideal B) ∈ (Ideal B)⁰` using `(J * J₂).2`.

Establish `h2 : ClassGroup.mk0 ⟨(J : Ideal B) * (J₂ : Ideal B), hmemJJ⟩ = 1`. Establish `: (⟨(J : Ideal B) * (J₂ : Ideal B), hmemJJ⟩ : (Ideal B)⁰) = J * J₂` using `rfl`. Rewrite using `[this, map_mul, hJ₂c, mul_inv_cancel]`. Take `⟨t, ht⟩` from `((ClassGroup.mk0_eq_one_iff hmemJJ).1 h2).principal`. Establish `ht' : (J : Ideal B) * (J₂ : Ideal B) = Ideal.span {t}` using `ht`.

Establish `hspan : Ideal.span {b * t ^ q} = Ideal.span {n} * (P * (J₂ : Ideal B) ^ q)`. Rewrite using `[← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, ← ht', hQ, ← hn', mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdvd : n ∣ b * t ^ q`. Rewrite using `[← Ideal.mem_span_singleton]`.

Establish `hle : Ideal.span {b * t ^ q} ≤ Ideal.span {n}` using `hspan ▸ Ideal.mul_le_left`. Conclude with `hle (Ideal.mem_span_singleton_self _)`. Take `⟨w, hw⟩` from `hdvd`. Establish `hn0' : Ideal.span {n} ≠ 0` using `by simpa using hn0`. Establish `hwspan : Ideal.span {w} = P * (J₂ : Ideal B) ^ q`.

Apply `mul_left_cancel₀ hn0'` to reduce the goal to its premises. Rewrite using `[Ideal.span_singleton_mul_span_singleton, ← hw, hspan]`. Establish `cgP : IsCoprime (Ideal.span {g}) P`. Apply `isCoprime_ideal_of_le _ (le_sup_right : Ideal.span {f ^ N} ≤ P)` to reduce the goal to its premises. Rewrite using `[Ideal.isCoprime_span_singleton_iff]`.

Conclude with `hfg.symm.pow_right`. Establish `cgJ₂ : IsCoprime (Ideal.span {g}) (J₂ : Ideal B)`. Rewrite using `[Ideal.isCoprime_iff_sup_eq, sup_comm]`. Conclude with `hJ₂g`. Establish `hgw : IsCoprime g w`.

Rewrite using `[← Ideal.isCoprime_span_singleton_iff, hwspan]`. Conclude with `cgP.mul_right cgJ₂.pow_right`. Use `⟨g, n, t, w, N, hg0, hfg, hfn, hgw, ?_, ?_, hw⟩` and prove the remaining obligations. Rewrite using `[← Ideal.mem_span_singleton, hQ]`. Conclude with `Ideal.mul_mem_mul (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) ((Ideal.mul_le_left : Q * (J : Ideal B) ≤ Q) hgQJ)`.

Rewrite using `[← Ideal.mem_span_singleton, ← hn']`. Establish `: g ^ q ∈ (Q * (J : Ideal B)) ^ q` using `Ideal.pow_mem_pow hgQJ q`. Rewrite `this` using `[mul_pow]`. Conclude with `Ideal.mul_mono_left (Ideal.pow_le_self hq) this`.
-/
theorem core (q : ℕ) (hq : q ≠ 0) (hdiv : ∀ c : ClassGroup B, ∃ d : ClassGroup B, d ^ q = c)
    (f b : B) (hf : f ≠ 0) (hb : b ≠ 0) :
    ∃ (g n t w : B) (N : ℕ), g ≠ 0 ∧ IsCoprime f g ∧ IsCoprime f n ∧ IsCoprime g w ∧
      b ∣ f ^ N * g ∧ n ∣ g ^ q ∧ b * t ^ q = n * w := by
  obtain ⟨N, Q, hQ, hQf⟩ := exists_split f b hb
  set P := Ideal.span {b} ⊔ Ideal.span {f ^ N} with hPdef
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply hb
    simpa using hQ
  have hf0 : Ideal.span {f} ≠ ⊥ := by simpa using hf
  let Q' : (Ideal B)⁰ := ⟨Q, mem_nonZeroDivisors_of_ne_zero hQ0⟩
  obtain ⟨c, hc⟩ := hdiv (ClassGroup.mk0 Q')⁻¹
  obtain ⟨J, hJf, hJc⟩ := GlobalTheory.SteinitzProd.classGroup_exists_integral_ideal_coprime hf0 c
  have hmemQJ : Q * (J : Ideal B) ^ q ∈ (Ideal B)⁰ := (Q' * J ^ q).2
  have h1 : ClassGroup.mk0 ⟨Q * (J : Ideal B) ^ q, hmemQJ⟩ = 1 := by
    have : (⟨Q * (J : Ideal B) ^ q, hmemQJ⟩ : (Ideal B)⁰) = Q' * J ^ q := Subtype.ext (by simp [Q'])
    rw [this, map_mul, map_pow, hJc, hc, mul_inv_cancel]
  obtain ⟨n, hn⟩ := ((ClassGroup.mk0_eq_one_iff hmemQJ).1 h1).principal
  have hn' : Q * (J : Ideal B) ^ q = Ideal.span {n} := hn
  have hJ0 : (J : Ideal B) ≠ ⊥ := by simpa using nonZeroDivisors.coe_ne_zero J
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : Q * (J : Ideal B) ^ q = ⊥ := by rw [hn']; simp
    rcases Ideal.mul_eq_bot.1 this with h | h
    · exact hQ0 h
    · exact hJ0 (pow_eq_zero_iff hq |>.1 h)

  have cQ : IsCoprime (Ideal.span {f}) Q := by
    rw [Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hQf
  have cJ : IsCoprime (Ideal.span {f}) (J : Ideal B) := by
    rw [Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hJf
  have hfn : IsCoprime f n := by
    rw [← Ideal.isCoprime_span_singleton_iff, ← hn']
    exact cQ.mul_right (cJ.pow_right)

  have hQJ0 : Q * (J : Ideal B) ≠ ⊥ := mul_ne_zero hQ0 hJ0
  have hQJf : Q * (J : Ideal B) ⊔ Ideal.span {f} = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq]; exact (cQ.mul_right cJ).symm
  obtain ⟨g, hgQJ, hg0, hfg⟩ := exists_mem_coprime hQJ0 f hQJf

  have hg0' : Ideal.span {g} ≠ ⊥ := by simpa using hg0
  obtain ⟨J₂, hJ₂g, hJ₂c⟩ := GlobalTheory.SteinitzProd.classGroup_exists_integral_ideal_coprime hg0' (ClassGroup.mk0 J)⁻¹
  have hmemJJ : (J : Ideal B) * (J₂ : Ideal B) ∈ (Ideal B)⁰ := (J * J₂).2
  have h2 : ClassGroup.mk0 ⟨(J : Ideal B) * (J₂ : Ideal B), hmemJJ⟩ = 1 := by
    have : (⟨(J : Ideal B) * (J₂ : Ideal B), hmemJJ⟩ : (Ideal B)⁰) = J * J₂ := rfl
    rw [this, map_mul, hJ₂c, mul_inv_cancel]
  obtain ⟨t, ht⟩ := ((ClassGroup.mk0_eq_one_iff hmemJJ).1 h2).principal
  have ht' : (J : Ideal B) * (J₂ : Ideal B) = Ideal.span {t} := ht

  have hspan : Ideal.span {b * t ^ q} = Ideal.span {n} * (P * (J₂ : Ideal B) ^ q) := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, ← ht', hQ, ← hn',
      mul_pow]
    ring
  have hdvd : n ∣ b * t ^ q := by
    rw [← Ideal.mem_span_singleton]
    have hle : Ideal.span {b * t ^ q} ≤ Ideal.span {n} := hspan ▸ Ideal.mul_le_left
    exact hle (Ideal.mem_span_singleton_self _)
  obtain ⟨w, hw⟩ := hdvd
  have hn0' : Ideal.span {n} ≠ 0 := by simpa using hn0
  have hwspan : Ideal.span {w} = P * (J₂ : Ideal B) ^ q := by
    apply mul_left_cancel₀ hn0'
    rw [Ideal.span_singleton_mul_span_singleton, ← hw, hspan]
  have cgP : IsCoprime (Ideal.span {g}) P := by
    apply isCoprime_ideal_of_le _ (le_sup_right : Ideal.span {f ^ N} ≤ P)
    rw [Ideal.isCoprime_span_singleton_iff]
    exact hfg.symm.pow_right
  have cgJ₂ : IsCoprime (Ideal.span {g}) (J₂ : Ideal B) := by
    rw [Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hJ₂g
  have hgw : IsCoprime g w := by
    rw [← Ideal.isCoprime_span_singleton_iff, hwspan]
    exact cgP.mul_right cgJ₂.pow_right
  refine ⟨g, n, t, w, N, hg0, hfg, hfn, hgw, ?_, ?_, hw⟩
  · rw [← Ideal.mem_span_singleton, hQ]
    exact Ideal.mul_mem_mul (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      ((Ideal.mul_le_left : Q * (J : Ideal B) ≤ Q) hgQJ)
  · rw [← Ideal.mem_span_singleton, ← hn']
    have : g ^ q ∈ (Q * (J : Ideal B)) ^ q := Ideal.pow_mem_pow hgQJ q
    rw [mul_pow] at this
    exact Ideal.mul_mono_left (Ideal.pow_le_self hq) this

end GlobalTheory.KummerDiv

namespace GlobalTheory.KummerDiv

/- English proof (translation)
Introduce `k B _ _ _ _ _ _ q hq f hf b hb m`. Establish `hqk : (q : k) ≠ 0` using `hq.ne_zero`. Establish `hq0 : q ≠ 0`. Introduce and unpack `rfl`. Conclude with `hqk (by simp)`.

Establish `hdiv : ∀ c : ClassGroup B, ∃ d : ClassGroup B, d ^ q = c` using `GlobalTheory.T.classGroup_dedekind_algClosed_divisible k B q hqk`. Take `⟨g, n, t, w, N, hg0, hfg, hfn, hgw, hbd, hnd, hw⟩` from `core q hq0 hdiv f b hf hb`. Use `⟨g, hg0, hfg, ?_⟩` and prove the remaining obligations. Use `set L := Localization.Away (f * g)`. Establish `hfgU : IsUnit (algebraMap B L (f * g))` using `IsLocalization.Away.algebraMap_isUnit (f * g)`.

Rewrite `hfgU` using `[map_mul]`. Establish `hfU : IsUnit (algebraMap B L f)` using `isUnit_of_mul_isUnit_left hfgU`. Establish `hgU : IsUnit (algebraMap B L g)` using `isUnit_of_mul_isUnit_right hfgU`. Establish `hbU : IsUnit (algebraMap B L b)`. Use `isUnit_of_dvd_unit (map_dvd (algebraMap B L) hbd) ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_pow]`. Conclude with `(hfU.pow N).mul hgU`. Establish `hnU : IsUnit (algebraMap B L n)`. Use `isUnit_of_dvd_unit (map_dvd (algebraMap B L) hnd) ?_` and prove the remaining obligations. Rewrite using `[map_pow]`.

Conclude with `hgU.pow q`. Use `set un := (hnU.mul (hfU.pow m)).unit with hun`. Establish `hv : (algebraMap B L n * algebraMap B L f ^ m) * ((un⁻¹ : Lˣ) : L) = 1`. Establish `: (un : L) = algebraMap B L n * algebraMap B L f ^ m` using `rfl`. Rewrite using `[← this]`.

Conclude with `Units.mul_inv un`. Use `⟨hbU.unit * un⁻¹, n, 1, t, w, f ^ m, hfn, isCoprime_one_right, hgw, hfg.symm.pow_right, ?_, ?_⟩` and prove the remaining obligations. Establish `hb' : ((hbU.unit : Lˣ) : L) = algebraMap B L b` using `rfl`. Rewrite using `[Units.val_mul, hb', map_mul, map_mul, map_one, map_pow]`. Take the linear combination `(-(algebraMap B L b)) * hv`.

Establish `hb' : ((hbU.unit : Lˣ) : L) = algebraMap B L b` using `rfl`. Establish `hw'` using `congrArg (algebraMap B L) hw`. Simplify using `only [map_mul, map_pow] at hw'`. Rewrite using `[Units.val_mul, hb', map_mul, map_pow, map_pow]`. Take the linear combination `(((un⁻¹ : Lˣ) : L) * algebraMap B L f ^ m) * hw' + algebraMap B L w * hv`.
-/
theorem divisor_step : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
    [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ b : B, b ≠ 0 →
    ∀ m : ℕ, ∃ g : B, g ≠ 0 ∧ IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ,
      ∃ n d t n' d' : B, IsCoprime f n ∧ IsCoprime f d ∧ IsCoprime g n' ∧ IsCoprime g d' ∧
      algebraMap B (Localization.Away (f * g)) (b * d) =
        (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (n * f ^ m) ∧
      (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (t ^ q * d') =
        algebraMap B (Localization.Away (f * g)) n' := by
  intro k B _ _ _ _ _ _ q hq f hf b hb m
  have hqk : (q : k) ≠ 0 := hq.ne_zero
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hqk (by simp)
  have hdiv : ∀ c : ClassGroup B, ∃ d : ClassGroup B, d ^ q = c := GlobalTheory.T.classGroup_dedekind_algClosed_divisible k B q hqk
  obtain ⟨g, n, t, w, N, hg0, hfg, hfn, hgw, hbd, hnd, hw⟩ := core q hq0 hdiv f b hf hb
  refine ⟨g, hg0, hfg, ?_⟩
  set L := Localization.Away (f * g)
  have hfgU : IsUnit (algebraMap B L (f * g)) := IsLocalization.Away.algebraMap_isUnit (f * g)
  rw [map_mul] at hfgU
  have hfU : IsUnit (algebraMap B L f) := isUnit_of_mul_isUnit_left hfgU
  have hgU : IsUnit (algebraMap B L g) := isUnit_of_mul_isUnit_right hfgU
  have hbU : IsUnit (algebraMap B L b) := by
    refine isUnit_of_dvd_unit (map_dvd (algebraMap B L) hbd) ?_
    rw [map_mul, map_pow]
    exact (hfU.pow N).mul hgU
  have hnU : IsUnit (algebraMap B L n) := by
    refine isUnit_of_dvd_unit (map_dvd (algebraMap B L) hnd) ?_
    rw [map_pow]
    exact hgU.pow q
  set un := (hnU.mul (hfU.pow m)).unit with hun
  have hv : (algebraMap B L n * algebraMap B L f ^ m) * ((un⁻¹ : Lˣ) : L) = 1 := by
    have : (un : L) = algebraMap B L n * algebraMap B L f ^ m := rfl
    rw [← this]; exact Units.mul_inv un
  refine ⟨hbU.unit * un⁻¹, n, 1, t, w, f ^ m, hfn, isCoprime_one_right, hgw, hfg.symm.pow_right, ?_, ?_⟩
  · have hb' : ((hbU.unit : Lˣ) : L) = algebraMap B L b := rfl
    rw [Units.val_mul, hb', map_mul, map_mul, map_one, map_pow]
    linear_combination (-(algebraMap B L b)) * hv
  · have hb' : ((hbU.unit : Lˣ) : L) = algebraMap B L b := rfl
    have hw' := congrArg (algebraMap B L) hw
    simp only [map_mul, map_pow] at hw'
    rw [Units.val_mul, hb', map_mul, map_pow, map_pow]
    linear_combination (((un⁻¹ : Lˣ) : L) * algebraMap B L f ^ m) * hw' + algebraMap B L w * hv

end GlobalTheory.KummerDiv
