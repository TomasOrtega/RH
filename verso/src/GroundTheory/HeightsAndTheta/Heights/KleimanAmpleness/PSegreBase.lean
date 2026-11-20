import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreJoin
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver GeneratesOver)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 (joinVec joinChart oneBlock pullDeg locIn modelPts)
open GroundTheory.Heights₂.Heights.NumbersDVR (segreVec)

section Local

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

/- English proof (translation)
Establish `ne0 : ∀ t : R, t ∉ P → (t : Ω) ≠ 0`. Introduce `t ht h0`. Conclude with `ht (by rw [show t = 0 from Subtype.ext h0]; exact P.zero_mem)`. Apply `le_antisymm` to reduce the goal to its premises. Use `Subring.closure_le.mpr ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨r, t, ht, rfl⟩`. Take `⟨s, hs, hrs⟩` from `hR r`. Take `⟨s', hs', hts⟩` from `hR t`. Establish `hs0 : (s : Ω) ≠ 0` using `ne0 _ hs`. Establish `hs'0 : (s' : Ω) ≠ 0` using `ne0 _ hs'`.

Establish `ht0 : (t : Ω) ≠ 0` using `ne0 _ ht`. Set `a : A` to `⟨(r : Ω) * s, hrs⟩`. Set `a' : A` to `⟨(t : Ω) * s', hts⟩`. Establish `hden : a' * s ∉ P.comap (Subalgebra.inclusion h)`. Rewrite using `[Ideal.mem_comap, map_mul]`.

Establish `e : Subalgebra.inclusion h a' = t * Subalgebra.inclusion h s'` using `Subtype.ext rfl`. Rewrite using `[e]`. Introduce `hm`. Break down `hP.mem_or_mem hm with hm | hm` into its components or cases. Break down `hP.mem_or_mem hm with hm | hm` into its components or cases.

Conclude with `ht hm`. Conclude with `hs' hm`. Conclude with `hs hm`. Use `Subring.subset_closure ⟨a * s', a' * s, hden, ?_⟩` and prove the remaining obligations. Use `show (r : Ω) / t = (r * s * s') / (t * s' * s)`.

Clear the denominators using the available nonvanishing facts. Use `Subring.closure_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, b, hb, rfl⟩`. Conclude with `Subring.subset_closure ⟨Subalgebra.inclusion h a, Subalgebra.inclusion h b, hb, rfl⟩`.
-/
theorem locIn_eq_of_le (A R : Subalgebra S Ω) (h : A ≤ R) (P : Ideal R) [hP : P.IsPrime]
    (hR : ∀ r : R, ∃ s : A, Subalgebra.inclusion h s ∉ P ∧ (r : Ω) * s ∈ A) :
    locIn R P = locIn A (P.comap (Subalgebra.inclusion h)) := by
  have ne0 : ∀ t : R, t ∉ P → (t : Ω) ≠ 0 := by
    intro t ht h0
    exact ht (by rw [show t = 0 from Subtype.ext h0]; exact P.zero_mem)
  apply le_antisymm
  · refine Subring.closure_le.mpr ?_
    rintro _ ⟨r, t, ht, rfl⟩
    obtain ⟨s, hs, hrs⟩ := hR r
    obtain ⟨s', hs', hts⟩ := hR t
    have hs0 : (s : Ω) ≠ 0 := ne0 _ hs
    have hs'0 : (s' : Ω) ≠ 0 := ne0 _ hs'
    have ht0 : (t : Ω) ≠ 0 := ne0 _ ht
    let a : A := ⟨(r : Ω) * s, hrs⟩
    let a' : A := ⟨(t : Ω) * s', hts⟩
    have hden : a' * s ∉ P.comap (Subalgebra.inclusion h) := by
      rw [Ideal.mem_comap, map_mul]
      have e : Subalgebra.inclusion h a' = t * Subalgebra.inclusion h s' := Subtype.ext rfl
      rw [e]
      intro hm
      rcases hP.mem_or_mem hm with hm | hm
      · rcases hP.mem_or_mem hm with hm | hm
        · exact ht hm
        · exact hs' hm
      · exact hs hm
    refine Subring.subset_closure ⟨a * s', a' * s, hden, ?_⟩
    show (r : Ω) / t = (r * s * s') / (t * s' * s)
    field_simp
  · refine Subring.closure_le.mpr ?_
    rintro _ ⟨a, b, hb, rfl⟩
    exact Subring.subset_closure ⟨Subalgebra.inclusion h a, Subalgebra.inclusion h b, hb, rfl⟩

end Local

section Segre

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type}
  {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)

def segreChart (d c : ∀ k, ι k) : ∀ k, Sum.elim (fun _ : Unit => ∀ k, ι k) ι k :=
  joinChart (fun _ : Unit => d) c

omit [Fintype K] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨C (Sum.inl ()), fun k => C (Sum.inr k), by funext k rcases k with ⟨⟩ | k <;> rfl⟩`.
-/
theorem segreChart_eta (C : ∀ k, Sum.elim (fun _ : Unit => ∀ k, ι k) ι k) :
    ∃ d c, C = segreChart (ι := ι) d c :=
  ⟨C (Sum.inl ()), fun k => C (Sum.inr k), by
    funext k
    rcases k with ⟨⟩ | k <;> rfl⟩

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.mpr fun k _ => hc k`.
-/
theorem segreVec_ne_zero {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : segreVec y c ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => hc k

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.mp hd k (Finset.mem_univ k)`.
-/
theorem ne_zero_of_segreVec {d : ∀ k, ι k} (hd : segreVec y d ≠ 0) (k : K) : y ⟨k, d k⟩ ≠ 0 :=
  Finset.prod_ne_zero_iff.mp hd k (Finset.mem_univ k)

/- English proof (translation)
Introduce and unpack `(⟨⟩ | k)`. Conclude with `hd`. Conclude with `hc k`.
-/
theorem segreChart_adm {d c : ∀ k, ι k} (hd : segreVec y d ≠ 0) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∀ k, segreJoin y ⟨k, segreChart d c k⟩ ≠ 0 := by
  rintro (⟨⟩ | k)
  · exact hd
  · exact hc k

/- English proof (translation)
Unfold `segreVec`. Rewrite using `[← Finset.prod_div_distrib]`. Conclude with `Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, d' k⟩, rfl⟩`.
-/
theorem segreVec_div_mem (c d' : ∀ k, ι k) : segreVec y d' / segreVec y c ∈ chartRingOver S y c := by
  unfold segreVec
  rw [← Finset.prod_div_distrib]
  exact Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, d' k⟩, rfl⟩

/- English proof (translation)
Unfold `segreVec`. Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), ← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', c k'⟩) (Finset.mem_univ k)]`. Establish `e : ∏ k' ∈ Finset.univ.erase k, y ⟨k', Function.update c k i k'⟩ = ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩` using `Finset.prod_congr rfl fun k' hk' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]`. Rewrite using `[e, Function.update_self]`. Clear denominators, using `[hc k]` for the nonvanishing conditions.
-/
theorem segreVec_update [DecidableEq K] (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : K) (i : ι k) :
    segreVec y (Function.update c k i) = y ⟨k, i⟩ / y ⟨k, c k⟩ * segreVec y c := by
  unfold segreVec
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
    ← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', c k'⟩) (Finset.mem_univ k)]
  have e : ∏ k' ∈ Finset.univ.erase k, y ⟨k', Function.update c k i k'⟩ =
      ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ :=
    Finset.prod_congr rfl fun k' hk' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]
  rw [e, Function.update_self]
  field_simp [hc k]

/- English proof (translation)
Rewrite using `[Fintype.prod_sum_type]`. Simplify using `[pullDeg]`. Both sides reduce to the same expression.
-/
theorem prod_segreChart (d c : ∀ k, ι k) (β : K → ℤ) :
    ∏ k, segreJoin y ⟨k, segreChart d c k⟩ ^ (-pullDeg (K₁ := Unit) β k) =
      ∏ k, y ⟨k, c k⟩ ^ (-β k) := by
  rw [Fintype.prod_sum_type]
  simp [pullDeg]
  rfl

/- English proof (translation)
Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨k, i⟩, rfl⟩`. Conclude with `Algebra.subset_adjoin ⟨⟨Sum.inr k, i⟩, rfl⟩`.
-/
theorem chartRingOver_le_segre (d c : ∀ k, ι k) :
    chartRingOver S y c ≤ chartRingOver S (segreJoin y) (segreChart d c) := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨⟨k, i⟩, rfl⟩
  exact Algebra.subset_adjoin ⟨⟨Sum.inr k, i⟩, rfl⟩

/- English proof (translation)
Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨⟨⟩ | k, i⟩, rfl⟩`. Conclude with `segreVec_div_mem y c i`. Conclude with `Algebra.subset_adjoin ⟨⟨k, i⟩, rfl⟩`.
-/
theorem segre_diag_le (c : ∀ k, ι k) :
    chartRingOver S (segreJoin y) (segreChart c c) ≤ chartRingOver S y c := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨⟨⟨⟩ | k, i⟩, rfl⟩
  · exact segreVec_div_mem y c i
  · exact Algebra.subset_adjoin ⟨⟨k, i⟩, rfl⟩

/- English proof (translation)
Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨⟨⟩, d'⟩, rfl⟩`. Conclude with `Algebra.subset_adjoin ⟨⟨Sum.inl (), d'⟩, rfl⟩`.
-/
theorem segreBlock_le (d c : ∀ k, ι k) :
    chartRingOver S (oneBlock (segreVec y)) (fun _ : Unit => d) ≤
      chartRingOver S (segreJoin y) (segreChart d c) := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨⟨⟨⟩, d'⟩, rfl⟩
  exact Algebra.subset_adjoin ⟨⟨Sum.inl (), d'⟩, rfl⟩

/- English proof (translation)
Use `set B := chartRingOver S (oneBlock (segreVec y)) (fun _ : Unit => d)`. Establish `hu : segreVec y c / segreVec y d ∈ B` using `Algebra.subset_adjoin ⟨⟨(), c⟩, rfl⟩`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨⟨⟨⟩ | k, i⟩, rfl⟩` from `hx`.

Conclude with `⟨0, by rw [pow_zero, mul_one]; exact Algebra.subset_adjoin ⟨⟨(), i⟩, rfl⟩⟩`. Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one]`. Express the relevant statement in the definitionally equal form `y ⟨k, i⟩ / y ⟨k, c k⟩ * (segreVec y c / segreVec y d) ∈ B`. Rewrite using `[mul_div_assoc', ← segreVec_update y c hc k i]`.

Conclude with `Algebra.subset_adjoin ⟨⟨(), Function.update c k i⟩, rfl⟩`. Consider the case `algebraMap r => exact ⟨0, by rw [pow_zero, mul_one]; exact B.algebraMap_mem r⟩`. Consider the case `add x x' _ _ ihx ihx'`. Take `⟨n, hn⟩` from `ihx`. Take `⟨m, hm⟩` from `ihx'`.

Use `⟨n + m, ?_⟩` and prove the remaining obligations. Establish `e : (x + x') * (segreVec y c / segreVec y d) ^ (n + m) = x * (segreVec y c / segreVec y d) ^ n * (segreVec y c / segreVec y d) ^ m + x' * (segreVec y c / segreVec y d) ^ m * (segreVec y c / segreVec y d) ^ n` using `by ring`. Rewrite using `[e]`. Conclude with `add_mem (mul_mem hn (pow_mem hu m)) (mul_mem hm (pow_mem hu n))`. Consider the case `mul x x' _ _ ihx ihx'`.

Take `⟨n, hn⟩` from `ihx`. Take `⟨m, hm⟩` from `ihx'`. Use `⟨n + m, ?_⟩` and prove the remaining obligations. Establish `e : (x * x') * (segreVec y c / segreVec y d) ^ (n + m) = x * (segreVec y c / segreVec y d) ^ n * (x' * (segreVec y c / segreVec y d) ^ m)` using `by ring`. Rewrite using `[e]`.

Conclude with `mul_mem hn hm`.
-/
theorem exists_mul_pow_mem [DecidableEq K] (d c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω}
    (hx : x ∈ chartRingOver S (segreJoin y) (segreChart d c)) :
    ∃ n : ℕ, x * (segreVec y c / segreVec y d) ^ n ∈
      chartRingOver S (oneBlock (segreVec y)) (fun _ : Unit => d) := by
  set B := chartRingOver S (oneBlock (segreVec y)) (fun _ : Unit => d)
  have hu : segreVec y c / segreVec y d ∈ B := Algebra.subset_adjoin ⟨⟨(), c⟩, rfl⟩
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨⟨⟩ | k, i⟩, rfl⟩ := hx
    · exact ⟨0, by rw [pow_zero, mul_one]; exact Algebra.subset_adjoin ⟨⟨(), i⟩, rfl⟩⟩
    · refine ⟨1, ?_⟩
      rw [pow_one]
      change y ⟨k, i⟩ / y ⟨k, c k⟩ * (segreVec y c / segreVec y d) ∈ B
      rw [mul_div_assoc', ← segreVec_update y c hc k i]
      exact Algebra.subset_adjoin ⟨⟨(), Function.update c k i⟩, rfl⟩
  | algebraMap r => exact ⟨0, by rw [pow_zero, mul_one]; exact B.algebraMap_mem r⟩
  | add x x' _ _ ihx ihx' =>
    obtain ⟨n, hn⟩ := ihx
    obtain ⟨m, hm⟩ := ihx'
    refine ⟨n + m, ?_⟩
    have e : (x + x') * (segreVec y c / segreVec y d) ^ (n + m) =
        x * (segreVec y c / segreVec y d) ^ n * (segreVec y c / segreVec y d) ^ m +
          x' * (segreVec y c / segreVec y d) ^ m * (segreVec y c / segreVec y d) ^ n := by ring
    rw [e]
    exact add_mem (mul_mem hn (pow_mem hu m)) (mul_mem hm (pow_mem hu n))
  | mul x x' _ _ ihx ihx' =>
    obtain ⟨n, hn⟩ := ihx
    obtain ⟨m, hm⟩ := ihx'
    refine ⟨n + m, ?_⟩
    have e : (x * x') * (segreVec y c / segreVec y d) ^ (n + m) =
        x * (segreVec y c / segreVec y d) ^ n * (x' * (segreVec y c / segreVec y d) ^ m) := by ring
    rw [e]
    exact mul_mem hn hm

/- English proof (translation)
Use extensionality with `s`. Simplify using `only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply, Subalgebra.mem_toSubmodule]`. Prove the components needed by the constructor for the conclusion. Introduce `h c hc`. Use `h (segreChart c c) (segreChart_adm y (segreVec_ne_zero y hc) hc)` as an intermediate fact.

Rewrite `this` using `[prod_segreChart]`. Conclude with `segre_diag_le y c this`. Introduce `h C hC`. Take `⟨d, c, rfl⟩` from `segreChart_eta C`. Rewrite using `[prod_segreChart]`.

Conclude with `chartRingOver_le_segre y d c (h c fun k => hC (Sum.inr k))`.
-/
theorem secOver_segreJoin (β : K → ℤ) : secOver S (segreJoin y) (pullDeg β) = secOver S y β := by
  ext s
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  constructor
  · intro h c hc
    have := h (segreChart c c) (segreChart_adm y (segreVec_ne_zero y hc) hc)
    rw [prod_segreChart] at this
    exact segre_diag_le y c this
  · intro h C hC
    obtain ⟨d, c, rfl⟩ := segreChart_eta C
    rw [prod_segreChart]
    exact chartRingOver_le_segre y d c (h c fun k => hC (Sum.inr k))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h c hc`. Take `⟨u, hu, hsum⟩` from `h (segreChart c c) (segreChart_adm y (segreVec_ne_zero y hc) hc)`. Rewrite `hsum` using `[prod_segreChart]`. Conclude with `⟨u, fun j => segre_diag_le y c (hu j), hsum⟩`.

Introduce `h C hC`. Take `⟨d, c, rfl⟩` from `segreChart_eta C`. Take `⟨u, hu, hsum⟩` from `h c fun k => hC (Sum.inr k)`. Conclude with `⟨u, fun j => chartRingOver_le_segre y d c (hu j), by rw [prod_segreChart]; exact hsum⟩`.
-/
theorem generatesOver_segreJoin (β : K → ℤ) (n : ℕ) (η : Fin n → Ω) :
    GeneratesOver S (segreJoin y) (pullDeg β) η ↔ GeneratesOver S y β η := by
  constructor
  · intro h c hc
    obtain ⟨u, hu, hsum⟩ := h (segreChart c c) (segreChart_adm y (segreVec_ne_zero y hc) hc)
    rw [prod_segreChart] at hsum
    exact ⟨u, fun j => segre_diag_le y c (hu j), hsum⟩
  · intro h C hC
    obtain ⟨d, c, rfl⟩ := segreChart_eta C
    obtain ⟨u, hu, hsum⟩ := h c fun k => hC (Sum.inr k)
    exact ⟨u, fun j => chartRingOver_le_segre y d c (hu j), by rw [prod_segreChart]; exact hsum⟩

/- English proof (translation)
Introduce and unpack `_ ⟨C, hC, P, hP, rfl⟩`. Take `⟨d, c, rfl⟩` from `segreChart_eta C`. Establish `hd : segreVec y d ≠ 0` using `hC (Sum.inl ())`. Establish `hc : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => hC (Sum.inr k)`. Establish `h` using `segreBlock_le (S := S) y d c`.

Use `⟨fun _ => d, fun _ => hd, P.comap (Subalgebra.inclusion h), inferInstance, ?_⟩` and prove the remaining obligations. Use `locIn_eq_of_le _ _ h P ?_` and prove the remaining obligations. Introduce `r`. Take `⟨n, hn⟩` from `exists_mul_pow_mem y d c hc r.2`. Establish `hu : segreVec y c / segreVec y d ∈ chartRingOver S (oneBlock (segreVec y)) (fun _ : Unit => d)` using `Algebra.subset_adjoin ⟨⟨(), c⟩, rfl⟩`.

Establish `hv : segreVec y d / segreVec y c ∈ chartRingOver S (segreJoin y) (segreChart d c)`. Unfold `segreVec`. Rewrite using `[← Finset.prod_div_distrib]`. Conclude with `Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨Sum.inr k, d k⟩, rfl⟩`. Establish `hvu : segreVec y d / segreVec y c * (segreVec y c / segreVec y d) = 1`.

Clear denominators, using `[hd, segreVec_ne_zero y hc]` for the nonvanishing conditions. Use `⟨⟨_, pow_mem hu n⟩, ?_, hn⟩` and prove the remaining obligations. Introduce `hm`. Establish `h1` using `P.mul_mem_left (⟨_, pow_mem hv n⟩ : chartRingOver S (segreJoin y) (segreChart d c)) hm`. Establish `e : (⟨_, pow_mem hv n⟩ : chartRingOver S (segreJoin y) (segreChart d c)) * Subalgebra.inclusion h ⟨_, pow_mem hu n⟩ = 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show (segreVec y d / segreVec y c) ^ n * (segreVec y c / segreVec y d) ^ n = 1`. Rewrite using `[← mul_pow, hvu, one_pow]`. Rewrite `h1` using `[e]`. Conclude with `(Ideal.ne_top_iff_one P).mp hP.ne_top h1`.
-/
theorem modelPts_segreJoin_le [DecidableEq K] :
    modelPts S (segreJoin y) ⊆ modelPts S (oneBlock (segreVec y)) := by
  rintro _ ⟨C, hC, P, hP, rfl⟩
  obtain ⟨d, c, rfl⟩ := segreChart_eta C
  have hd : segreVec y d ≠ 0 := hC (Sum.inl ())
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hC (Sum.inr k)
  have h := segreBlock_le (S := S) y d c
  refine ⟨fun _ => d, fun _ => hd, P.comap (Subalgebra.inclusion h), inferInstance, ?_⟩
  refine locIn_eq_of_le _ _ h P ?_
  intro r
  obtain ⟨n, hn⟩ := exists_mul_pow_mem y d c hc r.2
  have hu : segreVec y c / segreVec y d ∈
      chartRingOver S (oneBlock (segreVec y)) (fun _ : Unit => d) :=
    Algebra.subset_adjoin ⟨⟨(), c⟩, rfl⟩
  have hv : segreVec y d / segreVec y c ∈ chartRingOver S (segreJoin y) (segreChart d c) := by
    unfold segreVec
    rw [← Finset.prod_div_distrib]
    exact Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨Sum.inr k, d k⟩, rfl⟩
  have hvu : segreVec y d / segreVec y c * (segreVec y c / segreVec y d) = 1 := by
    field_simp [hd, segreVec_ne_zero y hc]
  refine ⟨⟨_, pow_mem hu n⟩, ?_, hn⟩
  intro hm
  have h1 := P.mul_mem_left (⟨_, pow_mem hv n⟩ : chartRingOver S (segreJoin y) (segreChart d c)) hm
  have e : (⟨_, pow_mem hv n⟩ : chartRingOver S (segreJoin y) (segreChart d c)) *
      Subalgebra.inclusion h ⟨_, pow_mem hu n⟩ = 1 := by
    apply Subtype.ext
    show (segreVec y d / segreVec y c) ^ n * (segreVec y c / segreVec y d) ^ n = 1
    rw [← mul_pow, hvu, one_pow]
  rw [e] at h1
  exact (Ideal.ne_top_iff_one P).mp hP.ne_top h1

/- English proof (translation)
Introduce `x hx`. Take `⟨n, hn⟩` from `exists_mul_pow_mem y d d (ne_zero_of_segreVec y hd) hx`. Rewrite `hn` using `[div_self hd, one_pow, mul_one]`. Then use the resulting hypothesis.
-/
theorem segre_diag_le_block [DecidableEq K] (d : ∀ k, ι k) (hd : segreVec y d ≠ 0) :
    chartRingOver S (segreJoin y) (segreChart d d) ≤
      chartRingOver S (oneBlock (segreVec y)) (fun _ : Unit => d) := by
  intro x hx
  obtain ⟨n, hn⟩ := exists_mul_pow_mem y d d (ne_zero_of_segreVec y hd) hx
  rwa [div_self hd, one_pow, mul_one] at hn

/- English proof (translation)
Establish `h1` using `segreBlock_le (S := S) y d d`. Establish `h2` using `segre_diag_le_block (S := S) y d hd`. Establish `e : (p.comap (Subalgebra.inclusion h2)).comap (Subalgebra.inclusion h1) = p`. Use extensionality with `x`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap]`.

Rewrite using `[show Subalgebra.inclusion h2 (Subalgebra.inclusion h1 x) = x from Subtype.ext (by simp)]`. Rewrite using `[locIn_eq_of_le _ _ h1 (p.comap (Subalgebra.inclusion h2)) ?_, e]`. Introduce `r`. Use `⟨1, ?_, by simpa using h2 r.2⟩` and prove the remaining obligations. Rewrite using `[map_one]`.

Conclude with `(Ideal.ne_top_iff_one _).mp (Ideal.IsPrime.ne_top inferInstance)`.
-/
theorem locIn_segre_diag [DecidableEq K] (d : ∀ k, ι k) (hd : segreVec y d ≠ 0)
    (p : Ideal (chartRingOver S (oneBlock (segreVec y)) (fun _ : Unit => d))) [p.IsPrime] :
    locIn (chartRingOver S (oneBlock (segreVec y)) (fun _ : Unit => d)) p =
      locIn (chartRingOver S (segreJoin y) (segreChart d d))
        (p.comap (Subalgebra.inclusion (segre_diag_le_block (S := S) y d hd))) := by
  have h1 := segreBlock_le (S := S) y d d
  have h2 := segre_diag_le_block (S := S) y d hd
  have e : (p.comap (Subalgebra.inclusion h2)).comap (Subalgebra.inclusion h1) = p := by
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap]
    rw [show Subalgebra.inclusion h2 (Subalgebra.inclusion h1 x) = x from Subtype.ext (by simp)]
  rw [locIn_eq_of_le _ _ h1 (p.comap (Subalgebra.inclusion h2)) ?_, e]
  intro r
  refine ⟨1, ?_, by simpa using h2 r.2⟩
  rw [map_one]
  exact (Ideal.ne_top_iff_one _).mp (Ideal.IsPrime.ne_top inferInstance)

/- English proof (translation)
Introduce and unpack `_ ⟨c', hc', p, hp, rfl⟩`. Establish `ec : c' = fun _ : Unit => c' ()` using `funext fun u => by cases u; rfl`. Generalize the expression as in `c' () = d at ec`. Substitute `ec` using the available equality. Establish `hd : segreVec y d ≠ 0` using `hc' ()`.

Conclude with `⟨segreChart d d, segreChart_adm y hd (ne_zero_of_segreVec y hd), p.comap (Subalgebra.inclusion (segre_diag_le_block (S := S) y d hd)), inferInstance, locIn_segre_diag y d hd p⟩`.
-/
theorem le_modelPts_segreJoin [DecidableEq K] :
    modelPts S (oneBlock (segreVec y)) ⊆ modelPts S (segreJoin y) := by
  rintro _ ⟨c', hc', p, hp, rfl⟩
  have ec : c' = fun _ : Unit => c' () := funext fun u => by cases u; rfl
  generalize c' () = d at ec
  subst ec
  have hd : segreVec y d ≠ 0 := hc' ()
  exact ⟨segreChart d d, segreChart_adm y hd (ne_zero_of_segreVec y hd),
    p.comap (Subalgebra.inclusion (segre_diag_le_block (S := S) y d hd)), inferInstance,
    locIn_segre_diag y d hd p⟩

end Segre

/- English proof (translation)
Introduce `S _ K _ _ ι _ Ω _ _ y hy`. Use `⟨⟨?_, ?_⟩, secOver_segreJoin y, generatesOver_segreJoin y⟩` and prove the remaining obligations. Introduce and unpack `(⟨⟩ | k)`. Conclude with `⟨fun k => (hy k).choose, segreVec_ne_zero y fun k => (hy k).choose_spec⟩`. Conclude with `hy k`.

Conclude with `Set.Subset.antisymm (modelPts_segreJoin_le y) (le_modelPts_segreJoin y)`.
-/
theorem SegreBase.proof : SegreBase.Statement := by
  intro S _ K _ _ ι _ Ω _ _ y hy
  refine ⟨⟨?_, ?_⟩, secOver_segreJoin y, generatesOver_segreJoin y⟩
  · rintro (⟨⟩ | k)
    · exact ⟨fun k => (hy k).choose, segreVec_ne_zero y fun k => (hy k).choose_spec⟩
    · exact hy k
  · exact Set.Subset.antisymm (modelPts_segreJoin_le y) (le_modelPts_segreJoin y)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
