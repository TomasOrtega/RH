import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ChartGlueFrame
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open ReciprocityTheory.ChartRestriction.G.Geo

/- English proof (translation)
Establish `: e = ∑ q, a q • (Module.Basis.mk hli hsp.ge) q` using `by simpa [Module.Basis.coe_mk] using hae`. Rewrite using `[this, (Module.Basis.mk hli hsp.ge).repr_sum_self a]`.
-/
theorem repr_of_eq_sum {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}
    {b : Fin r → E} (hli : LinearIndependent Ω b)
    (hsp : Submodule.span Ω (Set.range b) = ⊤) {e : E} {a : Fin r → Ω} (hae : e = ∑ q, a q • b q)
    (q : Fin r) : (Module.Basis.mk hli hsp.ge).repr e q = a q := by
  have : e = ∑ q, a q • (Module.Basis.mk hli hsp.ge) q := by simpa [Module.Basis.coe_mk] using hae
  rw [this, (Module.Basis.mk hli hsp.ge).repr_sum_self a]

section FrameGlueP

variable {Ω : Type} [Field Ω] [CharZero Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
  {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
  {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
  {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
  [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
  [∀ p, Algebra (o p) Ω]
  {B₀ : ChartBundle o₀ x r E} {Bp : ∀ p, ChartBundle (o p) x r E}

/- English proof (translation)
Establish `hPp : Prime (((p : Nat.Primes) : ℕ) : ℤ)` using `Nat.prime_iff_prime_int.mp (p : Nat.Primes).2`. Establish `hnot : ∀ {s : ℤ}, ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ s → (s : (chartRing ℤ x i)) ∉ Q` using `fun hs => intCast_not_mem_of_not_dvd hQ.ne_top (p : Nat.Primes).2 (by simpa using hpQ) hs`. Take `⟨k, g, d, hg, hd, hsum, hb⟩` from `(Bp p).frame i hi`. Take `⟨t, ht, htg⟩` from `exists_mul_mem_chartRing_int_fin x i (o p) (primeTo (p : Nat.Primes)) g hg`. Take `⟨t', ht', htd⟩` from `exists_mul_mem_chartRing_int_fin x i (o p) (primeTo (p : Nat.Primes)) d hd`.

Establish `hex : ∃ l, (⟨(t : Ω) * g l, htg l⟩ : (chartRing ℤ x i)) ∉ Q`. Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Establish `hmem` using `mem_ideal_of_sum Q (fun l => (t' : Ω) * d l) (fun l => (t : Ω) * g l) htd htg hall (z := ((t' * t : ℤ) : Ω)) (intCast_mem (chartRing ℤ x i) _) (by`. Establish `: ∑ l, (t' : Ω) * d l * ((t : Ω) * g l) = ((t' : Ω) * t) * ∑ l, d l * g l`.

Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring`. Rewrite using `[this, hsum]`. Use `push_cast`. Use the proof step `ring)`. Rewrite `hmem` using `[intCast_subtype]`.

Conclude with `hnot (mem_primeTo.1 (mul_mem ht' ht)) hmem`. Take `⟨l, hl⟩` from `hex`. Establish `hγA : (t : Ω) * g l ∈ (chartRing ℤ x i)` using `htg l`. Take `⟨b, hli, hsp, hiff⟩` from `hb l`. Establish `hγpow : ∀ (n : ℕ) {y : Ω}, g l ^ n * y ∈ chartRing (o p) x i → ((t : Ω) * g l) ^ n * y ∈ chartRing (o p) x i` using `fun n y hy => by`.

Rewrite using `[mul_pow, mul_assoc]`. Conclude with `mul_mem (pow_mem (intCast_mem_chartRing x i _ _) _) hy`. Establish `hsingle : ∀ q q' : Fin r, ∃ n : ℕ, g l ^ n * (Pi.single q (1 : Ω) : Fin r → Ω) q' ∈ chartRing (o p) x i` using `fun q q' => ⟨0, by`. Rewrite using `[pow_zero, one_mul]`. Distinguish the cases in `h : q' = q`.

Substitute `h` using the available equality. Simplify using `only [Pi.single_eq_same]`. Conclude with `one_mem _`. Rewrite using `[Pi.single_eq_of_ne h]`. Conclude with `zero_mem _⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨σ₁, hσ₁, n₁, hC1⟩ : ∃ σ ∈ primeTo (p : Nat.Primes), ∃ n : ℕ, ∀ q, ∀ n' ≥ n, ((σ : Ω) * ((t : Ω) * g l) ^ n') • b q ∈ glueLat B₀ Bp i := by`. Use `exists_uniform_mul _ (chartRing ℤ x i) (glueLat B₀ Bp i) (glueLat_stable i) hγA b fun q => ?_` and prove the remaining obligations. Take `⟨n, hn⟩` from `(hiff (b q)).2 ⟨Pi.single q 1, hsingle q, by simp [Pi.single_apply]⟩`. Establish `hγn : ((t : Ω) * g l) ^ n • b q ∈ (Bp p).lat i`. Rewrite using `[mul_pow, mul_smul]`.

Conclude with `smul_mem_of_chart (Bp p) (pow_mem (intCast_mem_chartRing x i _ _) _) hn`. Take `⟨s, hs, hsm⟩` from `(mem_Bp_iff hSR p _).1 hγn`. Use `⟨s, mem_primeTo.2 hs, n, ?_⟩` and prove the remaining obligations. Rewrite `hsm` using `[← Int.cast_smul_eq_zsmul Ω, smul_smul]`. Conclude with `hsm`.

Set `bb` to `Module.Basis.mk hli hsp.ge`. Establish `hbb : ∀ q, bb q = b q` using `fun q => by simp [bb, Module.Basis.coe_mk]`. Take `⟨K₀, Gn, hG, hGspan⟩` from `chartBundle_exists_gens B₀ hi`. Choose the witnesses or unpack the hypotheses as in `⟨σ₂, hσ₂, n₂, hC2⟩ : ∃ σ ∈ primeTo (p : Nat.Primes), ∃ n : ℕ, ∀ jq : (Fin K₀ × Fin r) × Fin r, ∀ n' ≥ n, ((σ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n') • bb.repr (Gn jq.1) jq.2 ∈ (chartRing ℤ x i).toSubring.toAddSubgroup := by`. Use `exists_uniform_mul (E := Ω) _ (chartRing ℤ x i) (chartRing ℤ x i).toSubring.toAddSubgroup (fun a ha e he => show a * e ∈ (chartRing ℤ x i) from mul_mem ha he) (mul_mem (intCast_mem (chartRing ℤ x i) _) hγA) _ fun jq => ?_` and prove the remaining obligations.

Take `⟨v, hv⟩` from `exists_prime_pow_smul_mem p (hSR p) (hG jq.1)`. Take `⟨a, ha, hae⟩` from `(hiff (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ v • Gn jq.1)).1 ⟨0, by rw [pow_zero, one_smul]; exact hv⟩`. Establish `hq : ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ v * bb.repr (Gn jq.1) jq.2 = a jq.2`. Use `repr_of_eq_sum hli hsp hae jq.2` as an intermediate fact. Rewrite `this` using `[map_smul, Finsupp.smul_apply, smul_eq_mul]`.

Conclude with `this`. Take `⟨n, hn⟩` from `ha jq.2`. Take `⟨s, hs, hsA⟩` from `exists_mul_mem_chartRing_int x i (o p) (primeTo (p : Nat.Primes)) (hγpow n hn)`. Use `⟨s, hs, v + n, ?_⟩` and prove the remaining obligations. Use `show (s : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ (v + n) * bb.repr (Gn jq.1) jq.2 ∈ (chartRing ℤ x i)`.

Establish `: (s : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ (v + n) * bb.repr (Gn jq.1) jq.2 = (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ n * ((t : Ω) * g l) ^ v) * ((s : Ω) * (((t : Ω) * g l) ^ n * a jq.2))`. Rewrite using `[← hq]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `mul_mem (mul_mem (pow_mem (intCast_mem (chartRing ℤ x i) _) _) (pow_mem hγA _)) hsA`.

Establish `hσ : ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ σ₁ * σ₂ * primeProdErase S (p : Nat.Primes)`. Rewrite using `[hPp.dvd_mul, hPp.dvd_mul]`. Introduce and unpack `((h | h) | h)`. Conclude with `mem_primeTo.1 hσ₁ h`. Conclude with `mem_primeTo.1 hσ₂ h`.

Conclude with `not_dvd_primeProdErase _ h`. Establish `hmPμ : ((primeProd S : ℤ) : Ω) = ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω)`. Rewrite using `[primeProd_eq_mul p.2, Int.cast_mul]`. Establish `hhA : ((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) * ((t : Ω) * g l) ∈ (chartRing ℤ x i)` using `mul_mem (intCast_mem (chartRing ℤ x i) _) hγA`. Establish `hC3 : ∀ e ∈ glueLat B₀ Bp i, ∀ q, ∃ n : ℕ, (((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n * bb.repr e q ∈ (chartRing ℤ x i)`.

Introduce `e he q`. Take `⟨he0, hep⟩` from `(mem_glueLat B₀ Bp).1 he`. Take `⟨a, ha, hae⟩` from `(hiff e).1 ⟨0, by simpa using hep p⟩`. Establish `hra : bb.repr e q = a q` using `repr_of_eq_sum hli hsp hae q`. Take `⟨n, hn⟩` from `ha q`.

Take `⟨se, hse, hseA⟩` from `exists_mul_mem_chartRing_int x i (o p) (primeTo (p : Nat.Primes)) (hγpow n hn)`. Take `⟨β, hβ, heβ⟩` from `hGspan e he0`. Take `⟨t₀, ht₀, ht₀β⟩` from `exists_mul_mem_chartRing_int_fin x i o₀ (Submonoid.powers (primeProd S)) β hβ`. Take `⟨κ, rfl⟩` from `(Submonoid.mem_powers_iff _ _).1 ht₀`. Establish `hrepr_e : bb.repr e q = ∑ j, β j * bb.repr (Gn j) q` using `by conv_lhs => rw [heβ]`.

Simplify using `[map_sum, map_smul]`. Establish `hii : (σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * (((primeProd S : ℤ) : Ω) ^ κ * bb.repr e q) ∈ (chartRing ℤ x i)`. Rewrite using `[hrepr_e, Finset.mul_sum, Finset.mul_sum]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Establish `h1 : (σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * bb.repr (Gn j) q ∈ (chartRing ℤ x i)` using `hC2 (j, q) n₂ le_rfl`.

Establish `h2` using `ht₀β j`. Establish `: (σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * (((primeProd S : ℤ) : Ω) ^ κ * (β j * bb.repr (Gn j) q)) = ((((primeProd S) ^ κ : ℤ) : Ω) * β j) * ((σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * bb.repr (Gn j) q)`. Rewrite using `[Int.cast_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `mul_mem h2 h1`. Establish `hc1 : ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ (n₂ + κ) * ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) ∈ (chartRing ℤ x i)`. Establish `: ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ (n₂ + κ) * ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) = ((t : Ω) * g l) ^ n * ((σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * (((primeProd S : ℤ) : Ω) ^ …`. Rewrite using `[hmPμ]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `mul_mem (pow_mem hγA _) hii`. Establish `hc2 : (se : Ω) * ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) ∈ (chartRing ℤ x i)`. Establish `: (se : Ω) * ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) = ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ n₂) * ((se : Ω) * (((t : Ω) * g l) ^ n * a q))`. Rewrite using `[hra]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `mul_mem (mul_mem (mul_mem (intCast_mem (chartRing ℤ x i) _) (pow_mem (intCast_mem (chartRing ℤ x i) _) _)) (pow_mem hγA _)) hseA`. Establish `hc` using `mem_of_prime_pow_mul_mem (A := (chartRing ℤ x i)) (p : Nat.Primes).2 (mem_primeTo.1 hse) (n₂ + κ) hc1 hc2`. Use `⟨κ + n + n₂ + 1, ?_⟩` and prove the remaining obligations.

Establish `: (((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) * ((t : Ω) * g l)) ^ (κ + n + n₂ + 1) * bb.repr e q = ((σ₁ : Ω) ^ (κ + n + n₂ + 1) * (σ₂ : Ω) ^ (κ + n + n₂) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ (n + n₂ + 1) * ((t : Ω) * g l) ^ (κ + 1)) * ((σ₂ : Ω) * ((prim …`. Rewrite using `[Int.cast_mul, Int.cast_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `mul_mem (mul_mem (mul_mem (mul_mem (pow_mem (intCast_mem (chartRing ℤ x i) _) _) (pow_mem (intCast_mem (chartRing ℤ x i) _) _)) (pow_mem (intCast_mem (chartRing ℤ x i) _) _)) (pow_mem hγA _)) hc`.

Establish `hhQ : (⟨_, hhA⟩ : (chartRing ℤ x i)) ∉ Q`. Establish `: (⟨_, hhA⟩ : (chartRing ℤ x i)) = ((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : (chartRing ℤ x i)) * ⟨_, hγA⟩` using `Subtype.ext (by simp)`. Rewrite using `[this]`. Introduce `hmem`. Break down `hQ.mem_or_mem hmem with h | h` into its components or cases.

Conclude with `hnot hσ h`. Conclude with `hl h`. Use `⟨_, hhA, hhQ, b, hli, hsp, fun e => ⟨fun ⟨n, hn⟩ => ?_, fun ⟨a, ha, hae⟩ => ?_⟩⟩` and prove the remaining obligations. Use `⟨fun q => bb.repr e q, fun q => ?_, ?_⟩` and prove the remaining obligations. Take `⟨n', hn'⟩` from `hC3 _ hn q`.

Use `⟨n' + n, ?_⟩` and prove the remaining obligations. Rewrite `hn'` using `[map_smul, Finsupp.smul_apply, smul_eq_mul, ← mul_assoc, ← pow_add]`. Conclude with `hn'`. Use `conv_lhs => rw [← bb.sum_repr e]`. Simplify using `only [hbb]`.

Use `choose nq hnq using ha`. Use `⟨Finset.univ.sup nq + (n₁ + 1), ?_⟩` and prove the remaining obligations. Rewrite using `[hae, Finset.smul_sum]`. Use `sum_mem fun q _ => ?_` and prove the remaining obligations. Use `set h := ((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) * ((t : Ω) * g l) with hh`.

Establish `hbq : h ^ (n₁ + 1) • b q ∈ glueLat B₀ Bp i`. Establish `: h ^ (n₁ + 1) = ((σ₁ : Ω) ^ n₁ * ((σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ (n₁ + 1) * ((t : Ω) * g l)) * ((σ₁ : Ω) * ((t : Ω) * g l) ^ n₁)`. Rewrite using `[hh]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, mul_smul]`. Conclude with `glueLat_stable i _ (mul_mem (mul_mem (pow_mem (intCast_mem (chartRing ℤ x i) _) _) (pow_mem (intCast_mem (chartRing ℤ x i) _) _)) hγA) _ (hC1 q n₁ le_rfl)`. Establish `haq : h ^ (Finset.univ.sup nq) * a q ∈ (chartRing ℤ x i)`. Rewrite using `[← pow_sub_mul_pow h (Finset.le_sup (f := nq) (Finset.mem_univ q)), mul_assoc]`. Conclude with `mul_mem (pow_mem hhA _) (hnq q)`.

Establish `: h ^ (Finset.univ.sup nq + (n₁ + 1)) • (a q • b q) = (h ^ (Finset.univ.sup nq) * a q) • (h ^ (n₁ + 1) • b q)`. Rewrite using `[smul_smul, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `glueLat_stable i _ haq _ hbq`.
-/
theorem frame_at_prime {i : τ} (hi : x i ≠ 0)
    (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) (Q : Ideal (chartRing ℤ x i))
    (hQ : Q.IsPrime) (p : S) (hpQ : ((((p : Nat.Primes) : ℕ) : ℤ) : (chartRing ℤ x i)) ∈ Q) :
    ∃ h : Ω, ∃ hh : h ∈ (chartRing ℤ x i), (⟨h, hh⟩ : (chartRing ℤ x i)) ∉ Q ∧
      IsFrameAt (chartRing ℤ x i) r (glueLat B₀ Bp i) h := by
  classical
  have hPp : Prime (((p : Nat.Primes) : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp (p : Nat.Primes).2
  have hnot : ∀ {s : ℤ}, ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ s → (s : (chartRing ℤ x i)) ∉ Q := fun hs =>
    intCast_not_mem_of_not_dvd hQ.ne_top (p : Nat.Primes).2 (by simpa using hpQ) hs
  obtain ⟨k, g, d, hg, hd, hsum, hb⟩ := (Bp p).frame i hi
  obtain ⟨t, ht, htg⟩ := exists_mul_mem_chartRing_int_fin x i (o p) (primeTo (p : Nat.Primes)) g hg
  obtain ⟨t', ht', htd⟩ := exists_mul_mem_chartRing_int_fin x i (o p) (primeTo (p : Nat.Primes)) d hd
  have hex : ∃ l, (⟨(t : Ω) * g l, htg l⟩ : (chartRing ℤ x i)) ∉ Q := by
    by_contra hall
    push Not at hall
    have hmem := mem_ideal_of_sum Q (fun l => (t' : Ω) * d l) (fun l => (t : Ω) * g l) htd htg hall
      (z := ((t' * t : ℤ) : Ω)) (intCast_mem (chartRing ℤ x i) _) (by
        have : ∑ l, (t' : Ω) * d l * ((t : Ω) * g l) = ((t' : Ω) * t) * ∑ l, d l * g l := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
        rw [this, hsum]; push_cast; ring)
    rw [intCast_subtype] at hmem
    exact hnot (mem_primeTo.1 (mul_mem ht' ht)) hmem
  obtain ⟨l, hl⟩ := hex
  have hγA : (t : Ω) * g l ∈ (chartRing ℤ x i) := htg l
  obtain ⟨b, hli, hsp, hiff⟩ := hb l

  have hγpow : ∀ (n : ℕ) {y : Ω}, g l ^ n * y ∈ chartRing (o p) x i →
      ((t : Ω) * g l) ^ n * y ∈ chartRing (o p) x i := fun n y hy => by
    rw [mul_pow, mul_assoc]; exact mul_mem (pow_mem (intCast_mem_chartRing x i _ _) _) hy
  have hsingle : ∀ q q' : Fin r, ∃ n : ℕ, g l ^ n * (Pi.single q (1 : Ω) : Fin r → Ω) q' ∈
      chartRing (o p) x i := fun q q' => ⟨0, by
    rw [pow_zero, one_mul]
    by_cases h : q' = q
    · subst h; simp only [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _⟩

  obtain ⟨σ₁, hσ₁, n₁, hC1⟩ : ∃ σ ∈ primeTo (p : Nat.Primes), ∃ n : ℕ, ∀ q, ∀ n' ≥ n,
      ((σ : Ω) * ((t : Ω) * g l) ^ n') • b q ∈ glueLat B₀ Bp i := by
    refine exists_uniform_mul _ (chartRing ℤ x i) (glueLat B₀ Bp i) (glueLat_stable i) hγA b fun q => ?_
    obtain ⟨n, hn⟩ := (hiff (b q)).2 ⟨Pi.single q 1, hsingle q, by simp [Pi.single_apply]⟩
    have hγn : ((t : Ω) * g l) ^ n • b q ∈ (Bp p).lat i := by
      rw [mul_pow, mul_smul]
      exact smul_mem_of_chart (Bp p) (pow_mem (intCast_mem_chartRing x i _ _) _) hn
    obtain ⟨s, hs, hsm⟩ := (mem_Bp_iff hSR p _).1 hγn
    refine ⟨s, mem_primeTo.2 hs, n, ?_⟩
    rw [← Int.cast_smul_eq_zsmul Ω, smul_smul] at hsm
    exact hsm
  let bb := Module.Basis.mk hli hsp.ge
  have hbb : ∀ q, bb q = b q := fun q => by simp [bb, Module.Basis.coe_mk]

  obtain ⟨K₀, Gn, hG, hGspan⟩ := chartBundle_exists_gens B₀ hi

  obtain ⟨σ₂, hσ₂, n₂, hC2⟩ : ∃ σ ∈ primeTo (p : Nat.Primes), ∃ n : ℕ,
      ∀ jq : (Fin K₀ × Fin r) × Fin r, ∀ n' ≥ n,
        ((σ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n') • bb.repr (Gn jq.1) jq.2 ∈ (chartRing ℤ x i).toSubring.toAddSubgroup := by
    refine exists_uniform_mul (E := Ω) _ (chartRing ℤ x i) (chartRing ℤ x i).toSubring.toAddSubgroup
      (fun a ha e he => show a * e ∈ (chartRing ℤ x i) from mul_mem ha he)
      (mul_mem (intCast_mem (chartRing ℤ x i) _) hγA) _ fun jq => ?_
    obtain ⟨v, hv⟩ := exists_prime_pow_smul_mem p (hSR p) (hG jq.1)
    obtain ⟨a, ha, hae⟩ := (hiff (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ v • Gn jq.1)).1 ⟨0, by rw [pow_zero, one_smul]; exact hv⟩
    have hq : ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ v * bb.repr (Gn jq.1) jq.2 = a jq.2 := by
      have := repr_of_eq_sum hli hsp hae jq.2
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul] at this
      exact this
    obtain ⟨n, hn⟩ := ha jq.2
    obtain ⟨s, hs, hsA⟩ := exists_mul_mem_chartRing_int x i (o p) (primeTo (p : Nat.Primes)) (hγpow n hn)
    refine ⟨s, hs, v + n, ?_⟩
    show (s : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ (v + n) * bb.repr (Gn jq.1) jq.2 ∈ (chartRing ℤ x i)
    have : (s : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ (v + n) * bb.repr (Gn jq.1) jq.2 =
        (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ n * ((t : Ω) * g l) ^ v) * ((s : Ω) * (((t : Ω) * g l) ^ n * a jq.2)) := by
      rw [← hq]; ring
    rw [this]
    exact mul_mem (mul_mem (pow_mem (intCast_mem (chartRing ℤ x i) _) _) (pow_mem hγA _)) hsA
  have hσ : ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) := by
    rw [hPp.dvd_mul, hPp.dvd_mul]
    rintro ((h | h) | h)
    · exact mem_primeTo.1 hσ₁ h
    · exact mem_primeTo.1 hσ₂ h
    · exact not_dvd_primeProdErase _ h
  have hmPμ : ((primeProd S : ℤ) : Ω) = ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) := by
    rw [primeProd_eq_mul p.2, Int.cast_mul]
  have hhA : ((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) * ((t : Ω) * g l) ∈ (chartRing ℤ x i) :=
    mul_mem (intCast_mem (chartRing ℤ x i) _) hγA

  have hC3 : ∀ e ∈ glueLat B₀ Bp i, ∀ q, ∃ n : ℕ,
      (((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n * bb.repr e q ∈ (chartRing ℤ x i) := by
    intro e he q
    obtain ⟨he0, hep⟩ := (mem_glueLat B₀ Bp).1 he
    obtain ⟨a, ha, hae⟩ := (hiff e).1 ⟨0, by simpa using hep p⟩
    have hra : bb.repr e q = a q := repr_of_eq_sum hli hsp hae q
    obtain ⟨n, hn⟩ := ha q
    obtain ⟨se, hse, hseA⟩ := exists_mul_mem_chartRing_int x i (o p) (primeTo (p : Nat.Primes)) (hγpow n hn)
    obtain ⟨β, hβ, heβ⟩ := hGspan e he0
    obtain ⟨t₀, ht₀, ht₀β⟩ :=
      exists_mul_mem_chartRing_int_fin x i o₀ (Submonoid.powers (primeProd S)) β hβ
    obtain ⟨κ, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 ht₀
    have hrepr_e : bb.repr e q = ∑ j, β j * bb.repr (Gn j) q := by
      conv_lhs => rw [heβ]
      simp [map_sum, map_smul]
    have hii : (σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * (((primeProd S : ℤ) : Ω) ^ κ * bb.repr e q) ∈ (chartRing ℤ x i) := by
      rw [hrepr_e, Finset.mul_sum, Finset.mul_sum]
      refine sum_mem fun j _ => ?_
      have h1 : (σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * bb.repr (Gn j) q ∈ (chartRing ℤ x i) := hC2 (j, q) n₂ le_rfl
      have h2 := ht₀β j
      have : (σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * (((primeProd S : ℤ) : Ω) ^ κ * (β j * bb.repr (Gn j) q)) =
          ((((primeProd S) ^ κ : ℤ) : Ω) * β j) *
            ((σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * bb.repr (Gn j) q) := by
        rw [Int.cast_pow]; ring
      rw [this]
      exact mul_mem h2 h1
    have hc1 : ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ (n₂ + κ) *
        ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) ∈ (chartRing ℤ x i) := by
      have : ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ (n₂ + κ) * ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) =
          ((t : Ω) * g l) ^ n * ((σ₂ : Ω) * (((((p : Nat.Primes) : ℕ) : ℤ) : Ω) * ((t : Ω) * g l)) ^ n₂ * (((primeProd S : ℤ) : Ω) ^ κ * bb.repr e q)) := by
        rw [hmPμ]; ring
      rw [this]
      exact mul_mem (pow_mem hγA _) hii
    have hc2 : (se : Ω) * ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) ∈ (chartRing ℤ x i) := by
      have : (se : Ω) * ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) =
          ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ n₂) * ((se : Ω) * (((t : Ω) * g l) ^ n * a q)) := by
        rw [hra]; ring
      rw [this]
      exact mul_mem (mul_mem (mul_mem (intCast_mem (chartRing ℤ x i) _) (pow_mem (intCast_mem (chartRing ℤ x i) _) _))
        (pow_mem hγA _)) hseA
    have hc := mem_of_prime_pow_mul_mem (A := (chartRing ℤ x i)) (p : Nat.Primes).2 (mem_primeTo.1 hse)
      (n₂ + κ) hc1 hc2
    refine ⟨κ + n + n₂ + 1, ?_⟩
    have : (((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) * ((t : Ω) * g l)) ^ (κ + n + n₂ + 1) *
        bb.repr e q = ((σ₁ : Ω) ^ (κ + n + n₂ + 1) * (σ₂ : Ω) ^ (κ + n + n₂) *
          ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ (n + n₂ + 1) * ((t : Ω) * g l) ^ (κ + 1)) *
          ((σ₂ : Ω) * ((primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ κ * ((t : Ω) * g l) ^ (n + n₂) * bb.repr e q) := by
      rw [Int.cast_mul, Int.cast_mul]; ring
    rw [this]
    exact mul_mem (mul_mem (mul_mem (mul_mem (pow_mem (intCast_mem (chartRing ℤ x i) _) _)
      (pow_mem (intCast_mem (chartRing ℤ x i) _) _)) (pow_mem (intCast_mem (chartRing ℤ x i) _) _)) (pow_mem hγA _)) hc

  have hhQ : (⟨_, hhA⟩ : (chartRing ℤ x i)) ∉ Q := by
    have : (⟨_, hhA⟩ : (chartRing ℤ x i)) =
        ((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : (chartRing ℤ x i)) * ⟨_, hγA⟩ :=
      Subtype.ext (by simp)
    rw [this]
    intro hmem
    rcases hQ.mem_or_mem hmem with h | h
    · exact hnot hσ h
    · exact hl h
  refine ⟨_, hhA, hhQ, b, hli, hsp, fun e => ⟨fun ⟨n, hn⟩ => ?_, fun ⟨a, ha, hae⟩ => ?_⟩⟩
  · refine ⟨fun q => bb.repr e q, fun q => ?_, ?_⟩
    · obtain ⟨n', hn'⟩ := hC3 _ hn q
      refine ⟨n' + n, ?_⟩
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, ← mul_assoc, ← pow_add] at hn'
      exact hn'
    · conv_lhs => rw [← bb.sum_repr e]
      simp only [hbb]
  · choose nq hnq using ha
    refine ⟨Finset.univ.sup nq + (n₁ + 1), ?_⟩
    rw [hae, Finset.smul_sum]
    refine sum_mem fun q _ => ?_
    set h := ((σ₁ * σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) * ((t : Ω) * g l) with hh
    have hbq : h ^ (n₁ + 1) • b q ∈ glueLat B₀ Bp i := by
      have : h ^ (n₁ + 1) = ((σ₁ : Ω) ^ n₁ * ((σ₂ * primeProdErase S (p : Nat.Primes) : ℤ) : Ω) ^ (n₁ + 1) *
          ((t : Ω) * g l)) * ((σ₁ : Ω) * ((t : Ω) * g l) ^ n₁) := by
        rw [hh]; push_cast; ring
      rw [this, mul_smul]
      exact glueLat_stable i _ (mul_mem (mul_mem (pow_mem (intCast_mem (chartRing ℤ x i) _) _)
        (pow_mem (intCast_mem (chartRing ℤ x i) _) _)) hγA) _ (hC1 q n₁ le_rfl)
    have haq : h ^ (Finset.univ.sup nq) * a q ∈ (chartRing ℤ x i) := by
      rw [← pow_sub_mul_pow h (Finset.le_sup (f := nq) (Finset.mem_univ q)), mul_assoc]
      exact mul_mem (pow_mem hhA _) (hnq q)
    have : h ^ (Finset.univ.sup nq + (n₁ + 1)) • (a q • b q) =
        (h ^ (Finset.univ.sup nq) * a q) • (h ^ (n₁ + 1) • b q) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [this]
    exact glueLat_stable i _ haq _ hbq

end FrameGlueP

end GroundTheory.Heights₂.Heights.Model
