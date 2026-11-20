import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.WeakClosed

/- English proof (translation)
Use `letI := cbValued l`. Establish `hle : ∀ x y : Cb l, Valued.v x ≤ Valued.v y ↔ ∃ e : OCb l, algebraMap (OCb l) (Cb l) e * y = x`. Introduce `x y`. Express the relevant statement in the definitionally equal form `(∃ e : OCb l, e • y = x) ↔ _`. Simplify using `only [Algebra.smul_def]`.

Establish `hinj` using `IsFractionRing.injective (OCb l) (Cb l)`. Take `⟨a, d, hd, rfl⟩` from `IsFractionRing.div_surjective (OCb l) c`. Establish `hd0 : algebraMap (OCb l) (Cb l) d ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd`. Establish `ha : a ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hc`. Take `⟨m₀, b, hb⟩` from `hdiv a ha`. Use `⟨m₀ + 1, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨t, rfl⟩` from `Ideal.mem_span_singleton'.1 hx`. Express the relevant statement in the definitionally equal form `Valued.v _ < Valued.v _`.

Rewrite using `[← not_le, hle]`. Introduce and unpack `⟨e, he⟩`. Rewrite `he` using `[eq_div_iff hd0]`. Establish `he' : e * (t * ϖ ^ (m₀ + 1)) * d = a` using `hinj (by rw [map_mul, map_mul]; exact he)`. Apply `hϖ` to reduce the goal to its premises.

Establish `h0 : a * (1 - ϖ * (e * t * d * b)) = 0`. Take the linear combination `(-1 : OCb l) * he' + e * t * d * ϖ * hb`. Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `absurd h ha`. Conclude with `isUnit_iff_exists_inv.2 ⟨e * t * d * b, (sub_eq_zero.1 h).symm⟩`.
-/
theorem lt_of_mem_span_pow {l : ℕ} [Fact l.Prime] (ϖ : OCb l) (hϖ : ¬ IsUnit ϖ)
    (hdiv : ∀ a : OCb l, a ≠ 0 → ∃ m : ℕ, a ∣ ϖ ^ m) (c : Cb l) (hc : c ≠ 0) :
    ∃ m : ℕ, ∀ x ∈ Ideal.span {ϖ ^ m},
      (cbValued l).v (algebraMap (OCb l) (Cb l) x) < (cbValued l).v c := by
  letI := cbValued l
  have hle : ∀ x y : Cb l, Valued.v x ≤ Valued.v y ↔
      ∃ e : OCb l, algebraMap (OCb l) (Cb l) e * y = x := by
    intro x y
    change (∃ e : OCb l, e • y = x) ↔ _
    simp only [Algebra.smul_def]
  have hinj := IsFractionRing.injective (OCb l) (Cb l)
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (OCb l) c
  have hd0 : algebraMap (OCb l) (Cb l) d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hc
  obtain ⟨m₀, b, hb⟩ := hdiv a ha
  refine ⟨m₀ + 1, fun x hx => ?_⟩
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  change Valued.v _ < Valued.v _
  rw [← not_le, hle]
  rintro ⟨e, he⟩
  rw [eq_div_iff hd0] at he
  have he' : e * (t * ϖ ^ (m₀ + 1)) * d = a := hinj (by rw [map_mul, map_mul]; exact he)
  apply hϖ
  have h0 : a * (1 - ϖ * (e * t * d * b)) = 0 := by
    linear_combination (-1 : OCb l) * he' + e * t * d * ϖ * hb
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd h ha
  · exact isUnit_iff_exists_inv.2 ⟨e * t * d * b, (sub_eq_zero.1 h).symm⟩

/- English proof (translation)
Introduce `l _ ϖ hϖ hdiv`. Use `letI := wTop l`. Use `letI := cbTop l`. Introduce `U hU`. Rewrite `hU` using `[nhds_induced]`.

Take `⟨t, ht, htU⟩` from `Filter.mem_comap.1 hU`. Rewrite `ht` using `[nhds_pi, Filter.mem_pi']`. Take `⟨I, V, hV, hIV⟩` from `ht`. Establish `key : ∀ i, ∃ m : ℕ, ∀ x ∈ Ideal.span {ϖ ^ m}, algebraMap (OCb l) (Cb l) x ∈ V i`. Introduce `i`.

Establish `h` using `hV i`. Rewrite `h` using `[WittVector.zero_coeff]`. Take `⟨c, hc, hcV⟩` from `(@GlobalTheory.WeakTop.mem_nhds_iff_lt _ _ _ _ (cbValued l) _ _).1 h`. Take `⟨m, hm⟩` from `lt_of_mem_span_pow ϖ hϖ hdiv c hc`. Conclude with `⟨m, fun x hx => hcV (by simpa using hm x hx)⟩`.

Use `choose M hM using key`. Use `⟨I.sup id + 1, I.sup M, fun w hw => htU (hIV ?_)⟩` and prove the remaining obligations. Introduce `i hi`. Use `show (inclW l w).coeff i ∈ V i`. Simplify using `only [inclW, WittVector.map_coeff]`.

Apply `hM i` to reduce the goal to its premises. Establish `hlt : i < I.sup id + 1` using `Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)`. Conclude with `Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (Finset.le_sup hi)) (hw i hlt)`.
-/
theorem weakly_small : ∀ {l : ℕ} [Fact l.Prime] (ϖ : OCb l), ¬ IsUnit ϖ → (∀ a : OCb l, a ≠ 0 → ∃ m : ℕ, a ∣ ϖ ^ m) → letI := wTop l; ∀ U ∈ 𝓝 (0 : WCb l), ∃ N m : ℕ, ∀ w : Ainf l, (∀ n < N, w.coeff n ∈ Ideal.span {ϖ ^ m}) → inclW l w ∈ U := by
  intro l _ ϖ hϖ hdiv
  letI := wTop l
  letI := cbTop l
  intro U hU
  rw [nhds_induced] at hU
  obtain ⟨t, ht, htU⟩ := Filter.mem_comap.1 hU
  rw [nhds_pi, Filter.mem_pi'] at ht
  obtain ⟨I, V, hV, hIV⟩ := ht
  have key : ∀ i, ∃ m : ℕ, ∀ x ∈ Ideal.span {ϖ ^ m}, algebraMap (OCb l) (Cb l) x ∈ V i := by
    intro i
    have h := hV i
    rw [WittVector.zero_coeff] at h
    obtain ⟨c, hc, hcV⟩ := (@GlobalTheory.WeakTop.mem_nhds_iff_lt _ _ _ _ (cbValued l) _ _).1 h
    obtain ⟨m, hm⟩ := lt_of_mem_span_pow ϖ hϖ hdiv c hc
    exact ⟨m, fun x hx => hcV (by simpa using hm x hx)⟩
  choose M hM using key
  refine ⟨I.sup id + 1, I.sup M, fun w hw => htU (hIV ?_)⟩
  intro i hi
  show (inclW l w).coeff i ∈ V i
  simp only [inclW, WittVector.map_coeff]
  apply hM i
  have hlt : i < I.sup id + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  exact Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (Finset.le_sup hi)) (hw i hlt)

end GlobalTheory.WeakClosed
