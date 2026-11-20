import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg.PeakPoly

def coord (n : ℕ) : Option ((Fin n × Fin n) × Bool) → Matrix (Fin n) (Fin n) ℂ → ℂ
  | none, _ => 1
  | some ((i, j), false), g => g i j
  | some ((i, j), true), g => star (g i j)

/- English proof (translation)
Break down `d with _ | ⟨⟨i, j⟩, _ | _⟩` into its components or cases. Conclude with `continuous_const`. Conclude with `continuous_id.matrix_elem i j`. Conclude with `(continuous_id.matrix_elem i j).star`.
-/
theorem continuous_coord (n : ℕ) (d : Option ((Fin n × Fin n) × Bool)) : Continuous (coord n d) := by
  rcases d with _ | ⟨⟨i, j⟩, _ | _⟩
  · exact continuous_const
  · exact continuous_id.matrix_elem i j
  · exact (continuous_id.matrix_elem i j).star

/- English proof (translation)
Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib]`.
-/
theorem prod_expand {ι D X : Type*} [Fintype ι] [DecidableEq ι] [Fintype D]
    (x : D → X → ℂ) (c : ι → D → ℂ) (g : X) :
    ∏ j, ∑ e, c j e * x e g = ∑ t : ι → D, (∏ j, c j (t j)) * ∏ j, x (t j) g := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_mul_distrib]

/- English proof (translation)
Establish `hmem : (fun g => coord n d (a * g)) ∈ Submodule.span ℂ (Set.range (coord n))`. Break down `d with _ | ⟨⟨i, j⟩, _ | _⟩` into its components or cases. Establish `: (fun g : Matrix (Fin n) (Fin n) ℂ => coord n none (a * g)) = coord n none`. Use function extensionality and compare the values at `g`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `Submodule.subset_span ⟨none, rfl⟩`. Establish `: (fun g : Matrix (Fin n) (Fin n) ℂ => coord n (some ((i, j), false)) (a * g)) = ∑ l, a i l • coord n (some ((l, j), false))`. Use function extensionality and compare the values at `g`. Simplify using `[coord, Matrix.mul_apply, Finset.sum_apply]`.

Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)`. Establish `: (fun g : Matrix (Fin n) (Fin n) ℂ => coord n (some ((i, j), true)) (a * g)) = ∑ l, star (a i l) • coord n (some ((l, j), true))`. Use function extensionality and compare the values at `g`. Simplify using `[coord, Matrix.mul_apply, Finset.sum_apply, star_sum, mul_comm]`.

Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)`. Take `⟨T, hT⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem`. Use `⟨T, fun g => ?_⟩` and prove the remaining obligations. Use `congrFun hT g` as an intermediate fact.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this`. Conclude with `this.symm`.
-/
theorem coord_translate (n : ℕ) (a : Matrix (Fin n) (Fin n) ℂ) (d : Option ((Fin n × Fin n) × Bool)) :
    ∃ T : Option ((Fin n × Fin n) × Bool) → ℂ, ∀ g, coord n d (a * g) = ∑ e, T e * coord n e g := by
  have hmem : (fun g => coord n d (a * g)) ∈ Submodule.span ℂ (Set.range (coord n)) := by
    rcases d with _ | ⟨⟨i, j⟩, _ | _⟩
    · have : (fun g : Matrix (Fin n) (Fin n) ℂ => coord n none (a * g)) = coord n none := by
        funext g; rfl
      rw [this]; exact Submodule.subset_span ⟨none, rfl⟩
    · have : (fun g : Matrix (Fin n) (Fin n) ℂ => coord n (some ((i, j), false)) (a * g)) =
          ∑ l, a i l • coord n (some ((l, j), false)) := by
        funext g; simp [coord, Matrix.mul_apply, Finset.sum_apply]
      rw [this]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · have : (fun g : Matrix (Fin n) (Fin n) ℂ => coord n (some ((i, j), true)) (a * g)) =
          ∑ l, star (a i l) • coord n (some ((l, j), true)) := by
        funext g; simp [coord, Matrix.mul_apply, Finset.sum_apply, star_sum, mul_comm]
      rw [this]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  obtain ⟨T, hT⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  refine ⟨T, fun g => ?_⟩
  have := congrFun hT g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  exact this.symm

/- English proof (translation)
Establish `hmem : (fun g => ((peak n g : ℝ) : ℂ)) ∈ Submodule.span ℂ (Set.range (coord n))`. Establish `: (fun g => ((peak n g : ℝ) : ℂ)) = (1 / 2 : ℂ) • coord n none + ∑ i, (1 / (4 * (n : ℂ))) • (coord n (some ((i, i), false)) + coord n (some ((i, i), true)))`. Use function extensionality and compare the values at `g`. Simplify using `only [peak, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, coord]`. Use `push_cast`.

Rewrite using `[Complex.re_eq_add_conj, ← Finset.mul_sum, Finset.sum_add_distrib, Matrix.trace, map_sum]`. Simplify using `only [Matrix.diag, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Use `Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)) ?_` and prove the remaining obligations.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩))`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem`. Use `⟨c, fun g => ?_⟩` and prove the remaining obligations. Use `congrFun hc g` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this`.

Conclude with `this.symm`.
-/
theorem peak_expand (n : ℕ) :
    ∃ c : Option ((Fin n × Fin n) × Bool) → ℂ, ∀ g, ((peak n g : ℝ) : ℂ) = ∑ e, c e * coord n e g := by
  have hmem : (fun g => ((peak n g : ℝ) : ℂ)) ∈ Submodule.span ℂ (Set.range (coord n)) := by
    have : (fun g => ((peak n g : ℝ) : ℂ)) = (1 / 2 : ℂ) • coord n none +
        ∑ i, (1 / (4 * (n : ℂ))) • (coord n (some ((i, i), false)) + coord n (some ((i, i), true))) := by
      funext g
      simp only [peak, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, coord]
      push_cast
      rw [Complex.re_eq_add_conj, ← Finset.mul_sum, Finset.sum_add_distrib, Matrix.trace,
        map_sum]
      simp only [Matrix.diag, Complex.star_def]
      ring
    rw [this]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)) ?_
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.add_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  refine ⟨c, fun g => ?_⟩
  have := congrFun hc g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  exact this.symm

end GlobalTheory.KFinAvg.PeakPoly

namespace GlobalTheory.KFinAvg
open PeakPoly

/- English proof (translation)
Introduce `n m`. Set `e` to `Fintype.equivFin (Fin m → Option ((Fin n × Fin n) × Bool))`. Set `bS : (Fin m → Option ((Fin n × Fin n) × Bool)) → Matrix (Fin n) (Fin n) ℂ → ℂ` to `fun s g => ∏ j, coord n (s j) g`. Take `⟨c0, hc0⟩` from `peak_expand n`. Use `⟨Fintype.card (Fin m → Option ((Fin n × Fin n) × Bool)), fun i => bS (e.symm i), fun i => ∏ j, c0 (e.symm i j), ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i`. Conclude with `continuous_finset_prod _ fun j _ => continuous_coord n _`. Introduce `g`. Establish `h1 : ((peak n g ^ m : ℝ) : ℂ) = ∏ _j : Fin m, ∑ d, c0 d * coord n d g`. Rewrite using `[Complex.ofReal_pow, hc0 g, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.

Rewrite using `[h1, prod_expand (fun d g => coord n d g) (fun _ => c0) g]`. Conclude with `(Equiv.sum_comp e.symm (fun t => (∏ j, c0 (t j)) * ∏ j, coord n (t j) g)).symm`. Introduce `a i choose T hT using fun j => coord_translate n a (e.symm i j)`. Use `⟨fun k => ∏ j, T j (e.symm k j), fun g => ?_⟩` and prove the remaining obligations. Use `show ∏ j, coord n (e.symm i j) (a * g) = _`.

Repeatedly rewrite using `[hT]`. Rewrite using `[prod_expand (fun d g => coord n d g) T g]`. Conclude with `(Equiv.sum_comp e.symm (fun t => (∏ j, T j (t j)) * ∏ j, coord n (t j) g)).symm`.
-/
theorem peak_pow_polynomial : ∀ n m : ℕ, ∃ (N : ℕ) (b : Fin N → Matrix (Fin n) (Fin n) ℂ → ℂ) (c : Fin N → ℂ),
    (∀ j, Continuous (b j)) ∧ (∀ g, ((GlobalTheory.KFinAvg.peak n g ^ m : ℝ) : ℂ) = ∑ j, c j * b j g) ∧
    ∀ (a : Matrix (Fin n) (Fin n) ℂ) (j : Fin N), ∃ d : Fin N → ℂ, ∀ g, b j (a * g) = ∑ i, d i * b i g := by
  intro n m
  classical
  let e := Fintype.equivFin (Fin m → Option ((Fin n × Fin n) × Bool))
  let bS : (Fin m → Option ((Fin n × Fin n) × Bool)) → Matrix (Fin n) (Fin n) ℂ → ℂ :=
    fun s g => ∏ j, coord n (s j) g
  obtain ⟨c0, hc0⟩ := peak_expand n
  refine ⟨Fintype.card (Fin m → Option ((Fin n × Fin n) × Bool)), fun i => bS (e.symm i),
    fun i => ∏ j, c0 (e.symm i j), ?_, ?_, ?_⟩
  · intro i
    exact continuous_finset_prod _ fun j _ => continuous_coord n _
  · intro g
    have h1 : ((peak n g ^ m : ℝ) : ℂ) = ∏ _j : Fin m, ∑ d, c0 d * coord n d g := by
      rw [Complex.ofReal_pow, hc0 g, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [h1, prod_expand (fun d g => coord n d g) (fun _ => c0) g]
    exact (Equiv.sum_comp e.symm (fun t => (∏ j, c0 (t j)) * ∏ j, coord n (t j) g)).symm
  · intro a i
    choose T hT using fun j => coord_translate n a (e.symm i j)
    refine ⟨fun k => ∏ j, T j (e.symm k j), fun g => ?_⟩
    show ∏ j, coord n (e.symm i j) (a * g) = _
    simp_rw [hT]
    rw [prod_expand (fun d g => coord n d g) T g]
    exact (Equiv.sum_comp e.symm (fun t => (∏ j, T j (t j)) * ∏ j, coord n (t j) g)).symm

end GlobalTheory.KFinAvg
