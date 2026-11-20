import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTracePatternIdempotentExchangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceUnitriangularColumnVanishingIdempotentEqSumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BernsteinZelevinskyDerivativeHarishChandraProducStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTraceIdempotentAndIrreducibleDegreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionCuspidalGreenDegreeEqOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLnStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section
namespace GlobalTheory.GLq.UpperWeight

def cnt {g : ℕ} (L : List (Pc g)) (i : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i)).card

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp [degL]`. Consider the case `cons a L ih => show ∑ j : Fin (L.length + 1), ((a :: L).get j).1 = _`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [List.length_cons, List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ] at ih ⊢`.

Rewrite using `[ih]`. Simplify using `[degL]`.
-/
theorem sum_get_fst {g : ℕ} (L : List (Pc g)) : ∑ j : Fin L.length, (L.get j).1 = degL L := by
  induction L with
  | nil => simp [degL]
  | cons a L ih =>
    show ∑ j : Fin (L.length + 1), ((a :: L).get j).1 = _
    rw [Fin.sum_univ_succ]
    simp only [List.length_cons, List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ,
      List.getElem_cons_succ] at ih ⊢
    rw [ih]; simp [degL]

/- English proof (translation)
Establish `hg0 : (0 : ℝ) < g` using `by exact_mod_cast hg`. Use `set w : Finset (Fin L.length) → ℕ := fun I => ∑ j ∈ I, (L.get j).1 with hw`. Use `set x : ℝ := 1 / (g : ℝ) with hx`. Establish `hx0 : 0 ≤ x` using `by positivity`. Establish `h1 : (∑ i ∈ Finset.range k, (cnt L i : ℝ) * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1))) + cnt L k ≤ ∑ i ∈ Finset.range (k + 1), (cnt L i : ℝ) * (g : ℝ) ^ (k - i)`.

Rewrite using `[Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]`. Establish `hs : ∑ i ∈ Finset.range k, (cnt L i : ℝ) * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1)) ≤ ∑ i ∈ Finset.range k, (cnt L i : ℝ) * (g : ℝ) ^ (k - i)`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Establish `: (0 : ℝ) ≤ (g : ℝ) ^ (k - i - 1)` using `by positivity`. Conclude with `mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg (cnt L i))`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : ∑ i ∈ Finset.range (k + 1), (cnt L i : ℝ) * (g : ℝ) ^ (k - i) = ∑ I : Finset (Fin L.length), if w I ≤ k then (g : ℝ) ^ (k - w I) else 0`. Establish `: ∀ i, (cnt L i : ℝ) = ∑ I : Finset (Fin L.length), if w I = i then (1 : ℝ) else 0`. Introduce `i`. Simplify using `only [cnt, Finset.sum_boole, hw]`.

Repeatedly rewrite using `[this, Finset.sum_mul, ite_mul, one_mul, zero_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_ite_eq]`. Simplify using `[Finset.mem_range, Nat.lt_succ_iff]`.

Establish `h3 : ∀ I : Finset (Fin L.length), (if w I ≤ k then (g : ℝ) ^ (k - w I) else 0) ≤ (g : ℝ) ^ k * x ^ w I`. Introduce `I`. Use `split_ifs with h`. Rewrite using `[pow_sub₀ _ hg0.ne' h, hx, one_div_pow, one_div]`. Check the signs of the components of the expression.

Establish `h4 : ∑ I : Finset (Fin L.length), x ^ w I = ∏ j : Fin L.length, (1 + x ^ (L.get j).1)`. Rewrite using `[Finset.prod_one_add, Finset.powerset_univ]`. Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations. Rewrite using `[hw, Finset.prod_pow_eq_pow_sum]`. Establish `h5 : ∏ j : Fin L.length, (1 + x ^ (L.get j).1) ≤ (1 + x) ^ degL L`.

Rewrite using `[← sum_get_fst, ← Finset.prod_pow_eq_pow_sum]`. Use `Finset.prod_le_prod (fun j _ => by positivity) fun j _ => ?_` and prove the remaining obligations. Establish `hj : 0 < (L.get j).1` using `hpos _ (List.get_mem L j)`. Use `pow_add_pow_le (zero_le_one' ℝ) hx0 hj.ne'` as an intermediate fact. Simplify using `using this`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem comb_bound {g : ℕ} (L : List (Pc g)) (hg : 1 ≤ g) (hpos : ∀ p ∈ L, 0 < p.1) (k : ℕ) :
    (∑ i ∈ Finset.range k, (cnt L i : ℝ) * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1))) + cnt L k
      ≤ (1 + 1 / (g : ℝ)) ^ (degL L) * (g : ℝ) ^ k := by
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  set w : Finset (Fin L.length) → ℕ := fun I => ∑ j ∈ I, (L.get j).1 with hw
  set x : ℝ := 1 / (g : ℝ) with hx
  have hx0 : 0 ≤ x := by positivity

  have h1 : (∑ i ∈ Finset.range k, (cnt L i : ℝ) * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1))) + cnt L k
      ≤ ∑ i ∈ Finset.range (k + 1), (cnt L i : ℝ) * (g : ℝ) ^ (k - i) := by
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
    have hs : ∑ i ∈ Finset.range k, (cnt L i : ℝ) * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1))
        ≤ ∑ i ∈ Finset.range k, (cnt L i : ℝ) * (g : ℝ) ^ (k - i) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have : (0 : ℝ) ≤ (g : ℝ) ^ (k - i - 1) := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg (cnt L i))
    linarith

  have h2 : ∑ i ∈ Finset.range (k + 1), (cnt L i : ℝ) * (g : ℝ) ^ (k - i)
      = ∑ I : Finset (Fin L.length), if w I ≤ k then (g : ℝ) ^ (k - w I) else 0 := by
    have : ∀ i, (cnt L i : ℝ) = ∑ I : Finset (Fin L.length), if w I = i then (1 : ℝ) else 0 := by
      intro i
      simp only [cnt, Finset.sum_boole, hw]
    simp_rw [this, Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range, Nat.lt_succ_iff]

  have h3 : ∀ I : Finset (Fin L.length), (if w I ≤ k then (g : ℝ) ^ (k - w I) else 0) ≤ (g : ℝ) ^ k * x ^ w I := by
    intro I
    split_ifs with h
    · rw [pow_sub₀ _ hg0.ne' h, hx, one_div_pow, one_div]
    · positivity

  have h4 : ∑ I : Finset (Fin L.length), x ^ w I = ∏ j : Fin L.length, (1 + x ^ (L.get j).1) := by
    rw [Finset.prod_one_add, Finset.powerset_univ]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hw, Finset.prod_pow_eq_pow_sum]
  have h5 : ∏ j : Fin L.length, (1 + x ^ (L.get j).1) ≤ (1 + x) ^ degL L := by
    rw [← sum_get_fst, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun j _ => by positivity) fun j _ => ?_
    have hj : 0 < (L.get j).1 := hpos _ (List.get_mem L j)
    have := pow_add_pow_le (zero_le_one' ℝ) hx0 hj.ne'
    simpa using this
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ ∑ I : Finset (Fin L.length), (g : ℝ) ^ k * x ^ w I := Finset.sum_le_sum fun I _ => h3 I
    _ = (g : ℝ) ^ k * ∏ j : Fin L.length, (1 + x ^ (L.get j).1) := by rw [← Finset.mul_sum, h4]
    _ ≤ (g : ℝ) ^ k * (1 + x) ^ degL L := by gcongr
    _ = _ := by rw [mul_comm]

/- English proof (translation)
Take `⟨V, -, hV⟩` from `h`. Introduce `x y`. Rewrite using `[← hV, ← hV]`. Conclude with `FDRep.char_conj V x y`.
-/
theorem isClass_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, -, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

/- English proof (translation)
Introduce `g _ L hg hG ψ hψ N k s hN hk f hm hd hc hsq`. Take `⟨Q, hQ, -, hdeg, hset⟩` from `(GlobalTheory.T.harishChandraSeriesLabel_exists_unique_GLn g L hg hG N).2.2 f hm hd hc hsq`. Use `set τ := hcL (Q.map Prod.snd) N with hτ`. Establish `hser : eSerC L N f = zOf τ`. Unfold `eSerC`.

Rewrite using `[hset, finsum_mem_singleton]`. Establish `hirr : IsIrr τ`. Establish `: τ ∈ {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}` using `by rw [hset]; rfl`. Conclude with `this.1`. Establish `hcl` using `isClass_of_isIrr hirr`.

Take `⟨d, hdpos, hd1⟩` from `(GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g N) (eU g N ψ) τ).2.1 hirr`. Establish `hL : ∀ p ∈ Q.map Prod.snd, IsCusp p.2 ∧ wh ψ p.2 = 1`. Introduce `p hp`. Take `⟨q, hq, rfl⟩` from `List.mem_map.1 hp`. Conclude with `⟨(hQ q hq).1.2.1, GlobalTheory.T.whittakerDimension_cuspidal_greenDegree_eq_one g ψ hψ _ _ (hQ q hq).1.2.1 (hQ q hq).2⟩`.

Establish `hlb` using `fun i (hi : i ≤ N) => GlobalTheory.T.bernsteinZelevinskyDerivative_harishChandraProduct g ψ hψ (Q.map Prod.snd) N i hdeg hi hL`. Establish `hwhU : tr (eU g N ψ) τ = 1` using `(hlb 0 (Nat.zero_le _)).2`. Establish `hkN : k < N` using `by omega`. Use `set TR : ℝ := (∑ i ∈ Finset.range k, (cnt (Q.map Prod.snd) i : ℝ) * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1))) + cnt (Q.map Prod.snd) k with hTR`. Establish `hJ : tr (eJ g N k s ψ) τ = (TR : ℂ)`.

Rewrite using `[GlobalTheory.T.groupAlgebraTrace_patternIdempotent_exchange g ψ hψ N k s hN τ hcl, GlobalTheory.T.trace_unitriangularColumnVanishingIdempotent_eq_sum_derivatives g ψ hψ N k hk hkN τ hcl, (hlb k hkN.le).1, hTR]`. Use `push_cast`. Use `congr 1`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[(hlb i (by simp at hi; omega)).1]`.

Both sides reduce to the same expression. Take `⟨-, hU1, hJ', -⟩` from `GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g N k s ψ`. Take `⟨-, hJ1⟩` from `hJ' hN`. Establish `hb` using `comb_bound (Q.map Prod.snd) (by omega) (fun p hp => (hL p hp).1.1) k`. Rewrite `hb` using `[hdeg]`.

Unfold `wtC`. Rewrite using `[hser, (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree _ (eJ g N k s ψ) τ).2.2, (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree _ (eU g N ψ) τ).2.2, hwhU, hJ, hJ1, hU1, hd1]`. Use `set M := N * (N - 1) / 2`. Use `set a : ℝ := (d : ℝ) / (Fintype.card (Gn g N) : ℝ) with ha`. Use `set m : ℝ := ((g : ℝ) ^ M)⁻¹ with hm'`.

Establish `e1 : (d : ℂ) / (Fintype.card (Gn g N) : ℂ) * (TR : ℂ) = ((a * TR : ℝ) : ℂ)` using `by rw [ha]; push_cast; ring`. Establish `e2 : (d : ℂ) / (Fintype.card (Gn g N) : ℂ) * 1 = ((a : ℝ) : ℂ)` using `by rw [ha]; push_cast; ring`. Establish `e3 : (g : ℂ) ^ k * ((g : ℂ) ^ M)⁻¹ = (((g : ℝ) ^ k * m : ℝ) : ℂ)` using `by rw [hm']; push_cast; ring`. Establish `e4 : ((g : ℂ) ^ M)⁻¹ = ((m : ℝ) : ℂ)` using `by rw [hm']; push_cast; ring`. Rewrite using `[e1, e2, e3, e4, Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re]`.

Establish `hg0 : (0 : ℝ) < g` using `by exact_mod_cast (show 0 < g by omega)`. Establish `hgk : (0 : ℝ) < (g : ℝ) ^ k` using `by positivity`. Establish `hm0 : 0 < m` using `by rw [hm']; positivity`. Establish `ha0 : 0 < a`. Rewrite using `[ha]; apply div_pos (by exact_mod_cast hdpos); exact_mod_cast Fintype.card_pos`.

Establish `hT : TR / (g : ℝ) ^ k ≤ (1 + 1 / (g : ℝ)) ^ N` using `by rw [div_le_iff₀ hgk]; exact hb`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem wtC_eJ_le : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 →
    ∀ (N k s : ℕ), N = k + 2 * s + 1 → 1 ≤ k → ∀ f : (ZMod g)[X], f.Monic → f.natDegree = N → f.coeff 0 ≠ 0 →
    Squarefree f → wtC L (eJ g N k s ψ) f ≤ (1 + 1 / (g : ℝ)) ^ N * wtC L (eU g N ψ) f := by
  intro g _ L hg hG ψ hψ N k s hN hk f hm hd hc hsq
  obtain ⟨Q, hQ, -, hdeg, hset⟩ := (GlobalTheory.T.harishChandraSeriesLabel_exists_unique_GLn g L hg hG N).2.2 f hm hd hc hsq
  set τ := hcL (Q.map Prod.snd) N with hτ
  have hser : eSerC L N f = zOf τ := by
    unfold eSerC; rw [hset, finsum_mem_singleton]
  have hirr : IsIrr τ := by
    have : τ ∈ {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f} := by rw [hset]; rfl
    exact this.1
  have hcl := isClass_of_isIrr hirr
  obtain ⟨d, hdpos, hd1⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g N) (eU g N ψ) τ).2.1 hirr
  have hL : ∀ p ∈ Q.map Prod.snd, IsCusp p.2 ∧ wh ψ p.2 = 1 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact ⟨(hQ q hq).1.2.1, GlobalTheory.T.whittakerDimension_cuspidal_greenDegree_eq_one g ψ hψ _ _ (hQ q hq).1.2.1 (hQ q hq).2⟩
  have hlb := fun i (hi : i ≤ N) => GlobalTheory.T.bernsteinZelevinskyDerivative_harishChandraProduct g ψ hψ (Q.map Prod.snd) N i hdeg hi hL
  have hwhU : tr (eU g N ψ) τ = 1 := (hlb 0 (Nat.zero_le _)).2
  have hkN : k < N := by omega
  set TR : ℝ := (∑ i ∈ Finset.range k, (cnt (Q.map Prod.snd) i : ℝ) * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1)))
    + cnt (Q.map Prod.snd) k with hTR
  have hJ : tr (eJ g N k s ψ) τ = (TR : ℂ) := by
    rw [GlobalTheory.T.groupAlgebraTrace_patternIdempotent_exchange g ψ hψ N k s hN τ hcl, GlobalTheory.T.trace_unitriangularColumnVanishingIdempotent_eq_sum_derivatives g ψ hψ N k hk hkN τ hcl, (hlb k hkN.le).1, hTR]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(hlb i (by simp at hi; omega)).1]
    rfl
  obtain ⟨-, hU1, hJ', -⟩ := GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g N k s ψ
  obtain ⟨-, hJ1⟩ := hJ' hN
  have hb := comb_bound (Q.map Prod.snd) (by omega) (fun p hp => (hL p hp).1.1) k
  rw [hdeg] at hb
  unfold wtC
  rw [hser, (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree _ (eJ g N k s ψ) τ).2.2, (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree _ (eU g N ψ) τ).2.2, hwhU, hJ, hJ1, hU1, hd1]
  set M := N * (N - 1) / 2
  set a : ℝ := (d : ℝ) / (Fintype.card (Gn g N) : ℝ) with ha
  set m : ℝ := ((g : ℝ) ^ M)⁻¹ with hm'
  have e1 : (d : ℂ) / (Fintype.card (Gn g N) : ℂ) * (TR : ℂ) = ((a * TR : ℝ) : ℂ) := by rw [ha]; push_cast; ring
  have e2 : (d : ℂ) / (Fintype.card (Gn g N) : ℂ) * 1 = ((a : ℝ) : ℂ) := by rw [ha]; push_cast; ring
  have e3 : (g : ℂ) ^ k * ((g : ℂ) ^ M)⁻¹ = (((g : ℝ) ^ k * m : ℝ) : ℂ) := by rw [hm']; push_cast; ring
  have e4 : ((g : ℂ) ^ M)⁻¹ = ((m : ℝ) : ℂ) := by rw [hm']; push_cast; ring
  rw [e1, e2, e3, e4, Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re]
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := by positivity
  have hm0 : 0 < m := by rw [hm']; positivity
  have ha0 : 0 < a := by
    rw [ha]; apply div_pos (by exact_mod_cast hdpos); exact_mod_cast Fintype.card_pos
  have hT : TR / (g : ℝ) ^ k ≤ (1 + 1 / (g : ℝ)) ^ N := by rw [div_le_iff₀ hgk]; exact hb
  calc a * TR / ((g : ℝ) ^ k * m) = (a / m) * (TR / (g : ℝ) ^ k) := by rw [div_mul_div_comm, mul_comm ((g : ℝ) ^ k) m]
    _ ≤ (a / m) * (1 + 1 / (g : ℝ)) ^ N := mul_le_mul_of_nonneg_left hT (by positivity)
    _ = (1 + 1 / (g : ℝ)) ^ N * (a / m) := by ring

end GlobalTheory.GLq.UpperWeight
