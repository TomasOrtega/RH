import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.PseudoMetrizableAEf
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree.HD

open PI.IwaMeasEx.MH GlobalTheory.CompanionTheory.SW

section Gen

variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
  [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]

/- English proof (translation)
Take `⟨a, ha⟩ : ∃ a : ℝ≥0, μ = a • (Measure.addHaar : Measure A)` from `⟨_, Measure.isAddLeftInvariant_eq_smul μ Measure.addHaar⟩`. Rewrite using `[ha, Measure.map_smul, map_char Measure.addHaar φ, smul_comm]`.
-/
theorem map_char' (μ : Measure A) [μ.IsAddHaarMeasure] (φ : A ≃ₜ+ A) :
    μ.map φ = (addEquivAddHaarChar φ)⁻¹ • μ := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, μ = a • (Measure.addHaar : Measure A) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul μ Measure.addHaar⟩
  rw [ha, Measure.map_smul, map_char Measure.addHaar φ, smul_comm]

/- English proof (translation)
Take `⟨K0, hK0, hK1⟩` from `exists_compact_mem_nhds (0 : A)`. Establish `hUo : IsOpen (interior K0)` using `isOpen_interior`. Establish `hU0 : μ (interior K0) ≠ 0` using `(hUo.measure_pos μ ⟨0, mem_interior_iff_mem_nhds.2 hK1⟩).ne'`. Establish `hUt : μ (interior K0) ≠ ⊤` using `ne_top_of_le_ne_top hK0.measure_lt_top.ne (measure_mono interior_subset)`. Establish `hS : MeasurableSet (φ '' interior K0)` using `(φ.toHomeomorph.isOpenMap _ hUo).measurableSet`.

Establish `hφ : Measurable (φ : A → A)` using `φ.continuous.measurable`. Establish `e : μ.map φ (φ '' interior K0) = μ (interior K0)`. Rewrite using `[Measure.map_apply hφ hS, Set.preimage_image_eq _ φ.injective]`. Rewrite `e` using `[map_char' μ φ, Measure.smul_apply, h _, ENNReal.smul_def, smul_eq_mul, ← mul_assoc]`. Establish `e2 : (((addEquivAddHaarChar φ)⁻¹ : ℝ≥0) : ℝ≥0∞) * θ = 1`.

Use `(ENNReal.mul_left_inj hU0 hUt).1 (e.trans (one_mul _).symm)` as an intermediate fact. Simplify using `using this`. Establish `e3 : (addEquivAddHaarChar φ)⁻¹ * θ = 1` using `by exact_mod_cast e2`. Conclude with `(inv_mul_eq_one₀ (addEquivAddHaarChar_pos φ).ne').1 e3`.
-/
theorem char_of_image (μ : Measure A) [μ.IsAddHaarMeasure] (φ : A ≃ₜ+ A) (θ : ℝ≥0)
    (h : ∀ Y : Set A, μ (φ '' Y) = θ * μ Y) : addEquivAddHaarChar φ = θ := by
  obtain ⟨K0, hK0, hK1⟩ := exists_compact_mem_nhds (0 : A)
  have hUo : IsOpen (interior K0) := isOpen_interior
  have hU0 : μ (interior K0) ≠ 0 := (hUo.measure_pos μ ⟨0, mem_interior_iff_mem_nhds.2 hK1⟩).ne'
  have hUt : μ (interior K0) ≠ ⊤ :=
    ne_top_of_le_ne_top hK0.measure_lt_top.ne (measure_mono interior_subset)
  have hS : MeasurableSet (φ '' interior K0) :=
    (φ.toHomeomorph.isOpenMap _ hUo).measurableSet
  have hφ : Measurable (φ : A → A) := φ.continuous.measurable
  have e : μ.map φ (φ '' interior K0) = μ (interior K0) := by
    rw [Measure.map_apply hφ hS, Set.preimage_image_eq _ φ.injective]
  rw [map_char' μ φ, Measure.smul_apply, h _, ENNReal.smul_def, smul_eq_mul, ← mul_assoc] at e
  have e2 : (((addEquivAddHaarChar φ)⁻¹ : ℝ≥0) : ℝ≥0∞) * θ = 1 := by
    have := (ENNReal.mul_left_inj hU0 hUt).1 (e.trans (one_mul _).symm)
    simpa using this
  have e3 : (addEquivAddHaarChar φ)⁻¹ * θ = 1 := by exact_mod_cast e2
  exact (inv_mul_eq_one₀ (addEquivAddHaarChar_pos φ).ne').1 e3

end Gen

section Ring

variable {B : Type} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

def mulE (u : Bˣ) : B ≃ₜ+ B where
  toFun x := (u : B) * x
  invFun x := ((u⁻¹ : Bˣ) : B) * x
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := mul_add _ _ _
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulE_apply (u : Bˣ) (x : B) : mulE u x = (u : B) * x := rfl

variable [LocallyCompactSpace B] [T2Space B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]

/- English proof (translation)
Establish `: mulE (1 : Bˣ) = ContinuousAddEquiv.refl B`. Use extensionality with `x`. Simplify using `[mulE_apply]`. Rewrite using `[this, addEquivAddHaarChar_refl]`.
-/
theorem char_mulE_one : addEquivAddHaarChar (mulE (1 : Bˣ)) = 1 := by
  have : mulE (1 : Bˣ) = ContinuousAddEquiv.refl B := by
    ext x
    simp [mulE_apply]
  rw [this, addEquivAddHaarChar_refl]

/- English proof (translation)
Establish `: mulE (u * v) = (mulE v).trans (mulE u)`. Use extensionality with `x`. Use `show ((u * v : Bˣ) : B) * x = (u : B) * ((v : B) * x)`. Simplify using `[mul_assoc]`. Rewrite using `[this, addEquivAddHaarChar_trans, mul_comm]`.
-/
theorem char_mulE_mul (u v : Bˣ) :
    addEquivAddHaarChar (mulE (u * v)) = addEquivAddHaarChar (mulE u) * addEquivAddHaarChar (mulE v) := by
  have : mulE (u * v) = (mulE v).trans (mulE u) := by
    ext x
    show ((u * v : Bˣ) : B) * x = (u : B) * ((v : B) * x)
    simp [mul_assoc]
  rw [this, addEquivAddHaarChar_trans, mul_comm]

/- English proof (translation)
Set `e : B ≃ₜ+ B` to `{ toFun := g, invFun := g, left_inv := hinv, right_inv := hinv, map_add' := map_add g, continuous_toFun := hg, continuous_invFun := hg }`. Establish `h2 : (e.symm.trans (mulE u)).trans e = mulE (Units.map (g : B →* B) u)`. Use extensionality with `x`. Use `show g ((u : B) * g x) = g (u : B) * x`. Rewrite using `[map_mul, hinv]`.

Rewrite using `[← h2]`. Conclude with `char_transport e (mulE u)`.
-/
theorem char_conj (g : B →+* B) (hg : Continuous g) (hinv : ∀ x, g (g x) = x) (u : Bˣ) :
    addEquivAddHaarChar (mulE (Units.map (g : B →* B) u)) = addEquivAddHaarChar (mulE u) := by
  let e : B ≃ₜ+ B :=
    { toFun := g, invFun := g, left_inv := hinv, right_inv := hinv, map_add' := map_add g,
      continuous_toFun := hg, continuous_invFun := hg }
  have h2 : (e.symm.trans (mulE u)).trans e = mulE (Units.map (g : B →* B) u) := by
    ext x
    show g ((u : B) * g x) = g (u : B) * x
    rw [map_mul, hinv]
  rw [← h2]
  exact char_transport e (mulE u)

end Ring

section Count

/- English proof (translation)
Establish `h : (Finset.univ.erase l).card = n - 1` using `by simp`. Rewrite using `[← h]`. Use `Finset.card_bij (fun p _ => if p.1.1 = l then p.1.2 else p.1.1) ?_ ?_ ?_` and prove the remaining obligations. Introduce `p hp`. Take `⟨⟨i, j⟩, hij⟩` from `p`.

Establish `hij' : i < j` using `hij`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hp`. Simplify using `only [Finset.mem_erase, Finset.mem_univ, and_true]`. Distinguish the cases in `hi : i = l`. Substitute `hi` using the available equality.

Simplify using `using hij'.ne'`. Break down `hp with hp | hp` into its components or cases. Conclude with `absurd hp hi`. Simplify `hi` using `[hi]`. Introduce `p hp q hq e`.

Take `⟨⟨i, j⟩, hij⟩` from `p`. Take `⟨⟨i', j'⟩, hij2⟩` from `q`. Establish `h1 : i < j` using `hij`. Establish `h2 : i' < j'` using `hij2`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq`.

Simplify using `only at e`. Apply `Subtype.ext` to reduce the goal to its premises. Apply the tactic sequence `by_cases hi : i = l <;> by_cases hi' : i' = l`. Simplify using `only [hi, hi', if_true] at e`. Simplify using `[hi, hi', e]`.

Simplify using `only [hi, hi', if_true, if_false] at e`. Establish `hj' : j' = l` using `hq.resolve_left hi'`. Substitute `hi hj' e` using the available equality. Conclude with `absurd (h1.trans h2) (lt_irrefl _)`. Simplify using `only [hi, hi', if_true, if_false] at e`.

Establish `hj : j = l` using `hp.resolve_left hi`. Substitute `hi' hj e` using the available equality. Conclude with `absurd (h1.trans h2) (lt_irrefl _)`. Simplify using `only [hi, hi', if_false] at e`. Establish `hj : j = l` using `hp.resolve_left hi`.

Establish `hj' : j' = l` using `hq.resolve_left hi'`. Simplify using `[e, hj, hj']`. Introduce `c hc`. Simplify using `only [Finset.mem_erase, Finset.mem_univ, and_true] at hc`. Break down `lt_or_gt_of_ne hc with h | h` into its components or cases.

Conclude with `⟨⟨(c, l), h⟩, by simp, by simp [hc]⟩`. Conclude with `⟨⟨(l, c), h⟩, by simp, by simp⟩`.
-/
theorem card_pairs {n : ℕ} (l : Fin n) :
    (Finset.univ.filter (fun p : {p : Fin n × Fin n // p.1 < p.2} => p.1.1 = l ∨ p.1.2 = l)).card = n - 1 := by
  have h : (Finset.univ.erase l).card = n - 1 := by simp
  rw [← h]
  refine Finset.card_bij (fun p _ => if p.1.1 = l then p.1.2 else p.1.1) ?_ ?_ ?_
  · intro p hp
    obtain ⟨⟨i, j⟩, hij⟩ := p
    have hij' : i < j := hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    by_cases hi : i = l
    · subst hi
      simpa using hij'.ne'
    · rcases hp with hp | hp
      · exact absurd hp hi
      · simpa [hi] using hi
  · intro p hp q hq e
    obtain ⟨⟨i, j⟩, hij⟩ := p
    obtain ⟨⟨i', j'⟩, hij2⟩ := q
    have h1 : i < j := hij
    have h2 : i' < j' := hij2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    simp only at e
    apply Subtype.ext
    by_cases hi : i = l <;> by_cases hi' : i' = l
    · simp only [hi, hi', if_true] at e
      simp [hi, hi', e]
    · simp only [hi, hi', if_true, if_false] at e
      have hj' : j' = l := hq.resolve_left hi'
      subst hi hj' e
      exact absurd (h1.trans h2) (lt_irrefl _)
    · simp only [hi, hi', if_true, if_false] at e
      have hj : j = l := hp.resolve_left hi
      subst hi' hj e
      exact absurd (h1.trans h2) (lt_irrefl _)
    · simp only [hi, hi', if_false] at e
      have hj : j = l := hp.resolve_left hi
      have hj' : j' = l := hq.resolve_left hi'
      simp [e, hj, hj']
  · intro c hc
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hc
    rcases lt_or_gt_of_ne hc with h | h
    · exact ⟨⟨(c, l), h⟩, by simp, by simp [hc]⟩
    · exact ⟨⟨(l, c), h⟩, by simp, by simp⟩

end Count

section Units

def uU {R : Type} [Monoid R] {n : ℕ} (l : Fin n) (r : Rˣ) : Fin n → Rˣ := Function.update 1 l r

def cU {K : Type} [Monoid K] {n : ℕ} (l : Fin n) (s t : Kˣ) : {p : Fin n × Fin n // p.1 < p.2} → Kˣ :=
  fun p => if p.1.2 = l then s else if p.1.1 = l then t else 1

variable {R K : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
  [T2Space R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
  [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [T2Space K] [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]

/- English proof (translation)
Rewrite using `[char_prod, char_pi, char_pi]`. Establish `e1 : ∏ i, addEquivAddHaarChar (mulE (uU l r i)) = θ`. Rewrite using `[Finset.prod_eq_single l]`. Simplify using `[uU, hr]`. Introduce `i _ hi`.

Simplify using `[uU, Function.update_of_ne hi, char_mulE_one]`. Simplify using the standard rewrite rules. Establish `e2 : ∏ p, addEquivAddHaarChar (mulE (cU l s t p)) = θ ^ (n - 1)`. Establish `h : ∀ p : {p : Fin n × Fin n // p.1 < p.2}, addEquivAddHaarChar (mulE (cU l s t p)) = if (p.1.1 = l ∨ p.1.2 = l) then θ else 1`. Introduce `p`.

Distinguish the cases in `h2 : p.1.2 = l`. Simplify using `[cU, h2, hs]`. Distinguish the cases in `h1 : p.1.1 = l`. Simplify using `[cU, h1, h2, ht]`. Simplify using `[cU, h1, h2, char_mulE_one]`.

Simplify using `only [h]`. Rewrite using `[Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, card_pairs]`. Rewrite using `[e1, e2]`. Establish `hn : n = (n - 1) + 1`. Use `l.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `conv_rhs => rw [hn, pow_succ']`.
-/
theorem char_total (r : Rˣ) (s t : Kˣ) (θ : ℝ≥0) (hr : addEquivAddHaarChar (mulE r) = θ)
    (hs : addEquivAddHaarChar (mulE s) = θ) (ht : addEquivAddHaarChar (mulE t) = θ) {n : ℕ} (l : Fin n) :
    addEquivAddHaarChar (prodE (piE fun i => mulE (uU l r i)) (piE fun p => mulE (cU l s t p))) = θ ^ n := by
  rw [char_prod, char_pi, char_pi]
  have e1 : ∏ i, addEquivAddHaarChar (mulE (uU l r i)) = θ := by
    rw [Finset.prod_eq_single l]
    · simp [uU, hr]
    · intro i _ hi
      simp [uU, Function.update_of_ne hi, char_mulE_one]
    · simp
  have e2 : ∏ p, addEquivAddHaarChar (mulE (cU l s t p)) = θ ^ (n - 1) := by
    have h : ∀ p : {p : Fin n × Fin n // p.1 < p.2}, addEquivAddHaarChar (mulE (cU l s t p)) =
        if (p.1.1 = l ∨ p.1.2 = l) then θ else 1 := by
      intro p
      by_cases h2 : p.1.2 = l
      · simp [cU, h2, hs]
      · by_cases h1 : p.1.1 = l
        · simp [cU, h1, h2, ht]
        · simp [cU, h1, h2, char_mulE_one]
    simp only [h]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, card_pairs]
  rw [e1, e2]
  have hn : n = (n - 1) + 1 := by
    have := l.2
    omega
  conv_rhs => rw [hn, pow_succ']

end Units

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

/- English proof (translation)
Rewrite using `[cjM, dMat, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul]`.
-/
theorem cjM_dMat_apply (σ : E →ₐ[F] E) {n : ℕ} (l : Fin n) (s : R ⊗[F] E)
    (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (i j : Fin n) :
    cjM R σ (dMat R l s) y i j =
      sigR R σ (Function.update (1 : Fin n → R ⊗[F] E) l s i) * y i j *
        Function.update (1 : Fin n → R ⊗[F] E) l s j := by
  rw [cjM, dMat, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.mul_diagonal,
    Matrix.diagonal_mul]

/- English proof (translation)
Establish `hI` using `HaarCoord.sigR_sigR (F := F) (E := E) R hinv`. Take `⟨r, hr⟩` from `HaarCoord.fixed_eq_tmul R hinv h2 hδ hσδ ((s : R ⊗[F] E) * sigR R σ (s : R ⊗[F] E)) (by rw [map_mul, hI, mul_comm])`. Take `⟨r', hr'⟩` from `HaarCoord.fixed_eq_tmul R hinv h2 hδ hσδ (((s⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E) * sigR R σ ((s⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) (by rw [map_mul, hI, mul_comm])`. Establish `e : (r * r') ⊗ₜ[F] (1 : E) = (1 : R) ⊗ₜ[F] (1 : E)`. Establish `h3 : (r ⊗ₜ[F] (1 : E)) * (r' ⊗ₜ[F] (1 : E)) = (r * r') ⊗ₜ[F] (1 : E)`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Rewrite using `[← h3, ← hr, ← hr']`. Establish `h4 : sigR R σ (s : R ⊗[F] E) * sigR R σ ((s⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Combine the equalities or inequalities in the displayed calculation.

Establish `e2 : r * r' = 1`. Rewrite using `[← HaarCoord.half_trace_tmul R h2 (r * r'), e, HaarCoord.half_trace_tmul R h2]`. Use `⟨⟨r, r', e2, by rw [mul_comm]; exact e2⟩, hr⟩` and prove the remaining obligations.
-/
theorem exists_norm [CharZero F] {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x)
    (h2 : Module.finrank F E = 2) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ) (s : (R ⊗[F] E)ˣ) :
    ∃ r : Rˣ, (s : R ⊗[F] E) * sigR R σ (s : R ⊗[F] E) = (r : R) ⊗ₜ[F] (1 : E) := by
  have hI := HaarCoord.sigR_sigR (F := F) (E := E) R hinv
  obtain ⟨r, hr⟩ := HaarCoord.fixed_eq_tmul R hinv h2 hδ hσδ ((s : R ⊗[F] E) * sigR R σ (s : R ⊗[F] E))
    (by rw [map_mul, hI, mul_comm])
  obtain ⟨r', hr'⟩ := HaarCoord.fixed_eq_tmul R hinv h2 hδ hσδ
    (((s⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E) * sigR R σ ((s⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E))
    (by rw [map_mul, hI, mul_comm])
  have e : (r * r') ⊗ₜ[F] (1 : E) = (1 : R) ⊗ₜ[F] (1 : E) := by
    have h3 : (r ⊗ₜ[F] (1 : E)) * (r' ⊗ₜ[F] (1 : E)) = (r * r') ⊗ₜ[F] (1 : E) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [← h3, ← hr, ← hr']
    have h4 : sigR R σ (s : R ⊗[F] E) * sigR R σ ((s⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    calc _ = ((s : R ⊗[F] E) * ((s⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) *
          (sigR R σ (s : R ⊗[F] E) * sigR R σ ((s⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) := by ring
      _ = _ := by rw [h4, Units.mul_inv, one_mul]; rfl
  have e2 : r * r' = 1 := by
    rw [← HaarCoord.half_trace_tmul R h2 (r * r'), e, HaarCoord.half_trace_tmul R h2]
  refine ⟨⟨r, r', e2, by rw [mul_comm]; exact e2⟩, hr⟩

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i show algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((z : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i) = ((uU l r i : Rˣ) : R) * (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i))`. Rewrite using `[hz, cjM_dMat_apply]`. Distinguish the cases in `hi : i = l`. Substitute `hi` using the available equality.

Take `⟨r0, hr0⟩` from `HaarCoord.fixed_eq_tmul R hinv h2 hδ hσδ ((y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i) (y.2 i i)`. Establish `e : sigR R σ (s : R ⊗[F] E) * (r0 ⊗ₜ[F] (1 : E)) * (s : R ⊗[F] E) = ((r : R) * r0) ⊗ₜ[F] (1 : E)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Function.update_self, uU]`. Rewrite using `[hr0, e, HaarCoord.half_trace_tmul R h2, HaarCoord.half_trace_tmul R h2]`.

Simplify using `only [uU, Function.update_of_ne hi, Pi.one_apply, map_one, one_mul, mul_one, Units.val_one]`. Use function extensionality and compare the values at `p`. Take `⟨⟨i, j⟩, hp⟩` from `p`. Use `show (z : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j = ((cU l s (Units.map (sigR R σ : R ⊗[F] E →* R ⊗[F] E) s) ⟨(i, j), hp⟩ : (R ⊗[F] E)ˣ) : R ⊗[F] E) * (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j`. Rewrite using `[hz, cjM_dMat_apply]`.

Establish `hij : i ≠ j` using `ne_of_lt hp`. Distinguish the cases in `hj : j = l`. Substitute `hj` using the available equality. Simplify using `[cU, Function.update_of_ne hij, mul_comm]`. Distinguish the cases in `hi : i = l`.

Substitute `hi` using the available equality. Simplify using `[cU, hj, Function.update_of_ne hj]`. Simplify using `[cU, hi, hj, Function.update_of_ne hi, Function.update_of_ne hj]`.
-/
theorem hermCoord_cj [TopologicalSpace R] [CharZero F] {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x)
    (h2 : Module.finrank F E = 2) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ) (s : (R ⊗[F] E)ˣ) (r : Rˣ)
    (hr : (s : R ⊗[F] E) * sigR R σ (s : R ⊗[F] E) = (r : R) ⊗ₜ[F] (1 : E)) {n : ℕ} (l : Fin n)
    (y z : HermR R σ n)
    (hz : (z : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      cjM R σ (dMat R l (s : R ⊗[F] E)) (y : Matrix (Fin n) (Fin n) (R ⊗[F] E))) :
    HaarCoord.hermCoord R σ n z =
      ((fun i => ((uU l r i : Rˣ) : R) * (HaarCoord.hermCoord R σ n y).1 i),
       (fun p => ((cU l s (Units.map (sigR R σ : R ⊗[F] E →* R ⊗[F] E) s) p : (R ⊗[F] E)ˣ) : R ⊗[F] E) *
          (HaarCoord.hermCoord R σ n y).2 p)) := by
  refine Prod.ext ?_ ?_
  · funext i
    show algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((z : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i) =
      ((uU l r i : Rˣ) : R) * (algebraMap F R (1 / 2) *
        Algebra.trace R (R ⊗[F] E) ((y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i))
    rw [hz, cjM_dMat_apply]
    by_cases hi : i = l
    · subst hi
      obtain ⟨r0, hr0⟩ := HaarCoord.fixed_eq_tmul R hinv h2 hδ hσδ
        ((y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i) (y.2 i i)
      have e : sigR R σ (s : R ⊗[F] E) * (r0 ⊗ₜ[F] (1 : E)) * (s : R ⊗[F] E) = ((r : R) * r0) ⊗ₜ[F] (1 : E) := by
        calc _ = ((s : R ⊗[F] E) * sigR R σ (s : R ⊗[F] E)) * (r0 ⊗ₜ[F] (1 : E)) := by ring
          _ = _ := by rw [hr, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      simp only [Function.update_self, uU]
      rw [hr0, e, HaarCoord.half_trace_tmul R h2, HaarCoord.half_trace_tmul R h2]
    · simp only [uU, Function.update_of_ne hi, Pi.one_apply, map_one, one_mul, mul_one, Units.val_one]
  · funext p
    obtain ⟨⟨i, j⟩, hp⟩ := p
    show (z : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j =
      ((cU l s (Units.map (sigR R σ : R ⊗[F] E →* R ⊗[F] E) s) ⟨(i, j), hp⟩ : (R ⊗[F] E)ˣ) : R ⊗[F] E) *
        (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j
    rw [hz, cjM_dMat_apply]
    have hij : i ≠ j := ne_of_lt hp
    by_cases hj : j = l
    · subst hj
      simp [cU, Function.update_of_ne hij, mul_comm]
    · by_cases hi : i = l
      · subst hi
        simp [cU, hj, Function.update_of_ne hj]
      · simp [cU, hi, hj, Function.update_of_ne hi, Function.update_of_ne hj]

end Tens

section Main

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Set `hh` to `hom.homeomorph`. Set `e : (R ⊗[F] E) ≃ₜ+ (Fin d → R)` to `{ toFun := hh, invFun := hh.symm, left_inv := hh.left_inv, right_inv := hh.right_inv, map_add' := fun x y => by`. Use function extensionality and compare the values at `k`. Use `show (Algebra.TensorProduct.basis R b).repr (x + y) k = _`. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Use `continuous_toFun := hh.continuous, continuous_invFun := hh.symm.continuous }`. Establish `hmul : ∀ (y : R ⊗[F] E), e ((t : R ⊗[F] E) * y) = fun k => (r : R) * e y k`. Introduce `y`. Use function extensionality and compare the values at `k`.

Establish `h1 : (t : R ⊗[F] E) * y = (r : R) • y`. Rewrite using `[ht, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]`. Simplify using the standard rewrite rules. Use `show (Algebra.TensorProduct.basis R b).repr ((t : R ⊗[F] E) * y) k = (r : R) * (Algebra.TensorProduct.basis R b).repr y k`. Rewrite using `[h1, map_smul]`.

Simplify using the standard rewrite rules. Establish `h2 : (e.symm.trans (mulE t)).trans e = piE (fun _ : Fin d => mulE r)`. Use extensionality with `x k`. Use `show e ((t : R ⊗[F] E) * e.symm x) k = (r : R) * x k`. Rewrite using `[hmul, e.apply_symm_apply]`.

Rewrite using `[← char_transport e (mulE t), h2, char_pi]`. Simplify using the standard rewrite rules.
-/
theorem char_scal (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
    [IsTopologicalRing (R ⊗[F] E)] [LocallyCompactSpace (R ⊗[F] E)] [SecondCountableTopology (R ⊗[F] E)]
    [T2Space (R ⊗[F] E)] [BorelSpace (R ⊗[F] E)] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (hom : IsHomeomorph fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k)
    (t : (R ⊗[F] E)ˣ) (r : Rˣ) (ht : (t : R ⊗[F] E) = (r : R) ⊗ₜ[F] (1 : E)) :
    addEquivAddHaarChar (mulE t) = addEquivAddHaarChar (mulE r) ^ d := by
  let hh := hom.homeomorph
  let e : (R ⊗[F] E) ≃ₜ+ (Fin d → R) :=
    { toFun := hh, invFun := hh.symm, left_inv := hh.left_inv, right_inv := hh.right_inv,
      map_add' := fun x y => by
        funext k
        show (Algebra.TensorProduct.basis R b).repr (x + y) k = _
        simp
        rfl
      continuous_toFun := hh.continuous, continuous_invFun := hh.symm.continuous }
  have hmul : ∀ (y : R ⊗[F] E), e ((t : R ⊗[F] E) * y) = fun k => (r : R) * e y k := by
    intro y
    funext k
    have h1 : (t : R ⊗[F] E) * y = (r : R) • y := by
      rw [ht, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
      simp
    show (Algebra.TensorProduct.basis R b).repr ((t : R ⊗[F] E) * y) k =
      (r : R) * (Algebra.TensorProduct.basis R b).repr y k
    rw [h1, map_smul]
    simp
  have h2 : (e.symm.trans (mulE t)).trans e = piE (fun _ : Fin d => mulE r) := by
    ext x k
    show e ((t : R ⊗[F] E) * e.symm x) k = (r : R) * x k
    rw [hmul, e.apply_symm_apply]
  rw [← char_transport e (mulE t), h2, char_pi]
  simp

variable {F E}

/- English proof (translation)
Take `⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩` from `TopK.topTens_props F E σ hσ R`. Use `haveI := t1`. Use `haveI := t2`. Use `haveI := t3`. Use `haveI := t4`.

Use `haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩`. Use `haveI : BorelSpace (HermR R σ n) := ⟨rfl⟩`. Use `haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩`. Use `haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _`. Take `⟨hinv, δ, hδ, hσδ⟩` from `HaarCoord.conj_facts hσ`.

Establish `h2 : Module.finrank F E = 2` using `hσ.2.2.1`. Establish `hd : d = 2`. Rewrite using `[← h2, Module.finrank_eq_card_basis b]`. Simplify using the standard rewrite rules. Establish `hI` using `HaarCoord.sigR_sigR (F := F) (E := E) (σ := σ) R hinv`.

Take `⟨hK, -, -⟩` from `coord_measures_haar F E σ hσ R d b lam hlam`. Use `haveI := hK`. Use `haveI := hlam`. Take `⟨r, hr⟩` from `exists_norm R hinv h2 hδ hσδ s`. Use `set t : (R ⊗[F] E)ˣ := Units.map (sigR R σ : R ⊗[F] E →* R ⊗[F] E) s with ht`.

Establish `c1 : addEquivAddHaarChar (mulE s) = θ` using `char_of_image (coordK R b lam) (mulE s) θ hθ`. Establish `c2 : addEquivAddHaarChar (mulE t) = θ`. Rewrite using `[← c1]`. Conclude with `char_conj (sigR R σ) t5 hI s`. Establish `c3 : addEquivAddHaarChar (mulE r) = θ`.

Establish `e1` using `char_scal F E R b (t7 d b) (s * t) r hr`. Rewrite `e1` using `[char_mulE_mul, c1, c2, hd, ← sq]`. Conclude with `((pow_left_inj₀ zero_le zero_le two_ne_zero).1 e1).symm`. Establish `hθ0 : θ ≠ 0`. Rewrite using `[← c1]`.

Conclude with `(addEquivAddHaarChar_pos _).ne'`. Establish `hom` using `HaarCoord.hermCoord_isHomeomorph R hinv h2 hδ hσδ n t5 t6`. Establish `hemb : MeasurableEmbedding (HaarCoord.hermCoord R σ n)` using `(hom.homeomorph).measurableEmbedding`. Establish `hS : MeasurableSet (HaarCoord.hermCoord R σ n '' Y)` using `hemb.measurableSet_image.2 hY`. Set `Ψ` to `prodE (piE fun i => mulE (uU l r i)) (piE fun p => mulE (cU l s t p))`.

Establish `hΨ : Measurable (Ψ : _ → _)` using `Ψ.continuous.measurable`. Establish `key : ∀ y : HermR R σ n, Ψ (HaarCoord.hermCoord R σ n y) = HaarCoord.hermCoord R σ n ⟨cjM R σ (dMat R l (s : R ⊗[F] E)) (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)), cjM_mem R σ hI _ _ y.2⟩` using `fun y => (hermCoord_cj R hinv h2 hδ hσδ s r hr l y _ rfl).symm`. Establish `hpre : cjPre R σ (dMat R l (s : R ⊗[F] E)) Y = HaarCoord.hermCoord R σ n ⁻¹' (Ψ ⁻¹' (HaarCoord.hermCoord R σ n '' Y))`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨z, hz, e⟩`. Rewrite using `[Set.mem_preimage, Set.mem_preimage, key]`. Use `⟨z, hz, ?_⟩` and prove the remaining obligations. Use `congr 1`. Conclude with `Subtype.ext e.symm`.

Rewrite using `[Set.mem_preimage, Set.mem_preimage, key]`. Introduce and unpack `⟨z, hz, e⟩`. Conclude with `⟨z, hz, (congrArg Subtype.val (hom.injective e)).symm⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hpre]`.

Conclude with `hemb.measurable (hΨ hS)`. Use `haveI a3 : (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => coordK R b lam).IsAddHaarMeasure := inferInstance haveI a4 : (Measure.pi fun _ : Fin n => lam).IsAddHaarMeasure := inferInstance haveI a5 : ((Measure.pi fun _ : Fin n => lam).prod (Measure.pi fun _ : {p : Fin n × …`. Establish `hc : coordHerm R σ b lam n = Measure.comap (HaarCoord.hermCoord R σ n) ((Measure.pi fun _ : Fin n => lam).prod (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => coordK R b lam))` using `rfl`. Establish `hm` using `map_char' ((Measure.pi fun _ : Fin n => lam).prod (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => coordK R b lam)) Ψ`. Establish `hch : addEquivAddHaarChar Ψ = θ ^ n` using `char_total r s t θ c3 c1 c2 l`.

Rewrite using `[hc, hemb.comap_apply, hemb.comap_apply, hpre, Set.image_preimage_eq _ hom.surjective, ← Measure.map_apply hΨ hS, hm, hch, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv (pow_ne_zero _ hθ0), ENNReal.coe_pow]`.
-/
theorem scale_ring (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R]
    [T2Space R] [MeasurableSpace R] [BorelSpace R] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : Measure R) (hlam : lam.IsAddHaarMeasure) (s : (R ⊗[F] E)ˣ) (θ : ℝ≥0)
    (hθ : ∀ Y : Set (R ⊗[F] E), (coordK R b lam) ((fun x => (s : R ⊗[F] E) * x) '' Y) = θ * (coordK R b lam) Y)
    (n : ℕ) (l : Fin n) (Y : Set (HermR R σ n)) (hY : MeasurableSet Y) :
    MeasurableSet (cjPre R σ (dMat R l (s : R ⊗[F] E)) Y) ∧
      (coordHerm R σ b lam n) (cjPre R σ (dMat R l (s : R ⊗[F] E)) Y) =
        ((θ : ℝ≥0∞) ^ n)⁻¹ * (coordHerm R σ b lam n) Y := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩ := TopK.topTens_props F E σ hσ R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (HermR R σ n) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _
  obtain ⟨hinv, δ, hδ, hσδ⟩ := HaarCoord.conj_facts hσ
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  have hd : d = 2 := by
    rw [← h2, Module.finrank_eq_card_basis b]
    simp
  have hI := HaarCoord.sigR_sigR (F := F) (E := E) (σ := σ) R hinv
  obtain ⟨hK, -, -⟩ := coord_measures_haar F E σ hσ R d b lam hlam
  haveI := hK
  haveI := hlam

  obtain ⟨r, hr⟩ := exists_norm R hinv h2 hδ hσδ s
  set t : (R ⊗[F] E)ˣ := Units.map (sigR R σ : R ⊗[F] E →* R ⊗[F] E) s with ht
  have c1 : addEquivAddHaarChar (mulE s) = θ := char_of_image (coordK R b lam) (mulE s) θ hθ
  have c2 : addEquivAddHaarChar (mulE t) = θ := by
    rw [← c1]
    exact char_conj (sigR R σ) t5 hI s
  have c3 : addEquivAddHaarChar (mulE r) = θ := by
    have e1 := char_scal F E R b (t7 d b) (s * t) r hr
    rw [char_mulE_mul, c1, c2, hd, ← sq] at e1
    exact ((pow_left_inj₀ zero_le zero_le two_ne_zero).1 e1).symm
  have hθ0 : θ ≠ 0 := by
    rw [← c1]
    exact (addEquivAddHaarChar_pos _).ne'

  have hom := HaarCoord.hermCoord_isHomeomorph R hinv h2 hδ hσδ n t5 t6
  have hemb : MeasurableEmbedding (HaarCoord.hermCoord R σ n) :=
    (hom.homeomorph).measurableEmbedding
  have hS : MeasurableSet (HaarCoord.hermCoord R σ n '' Y) := hemb.measurableSet_image.2 hY
  let Ψ := prodE (piE fun i => mulE (uU l r i)) (piE fun p => mulE (cU l s t p))
  have hΨ : Measurable (Ψ : _ → _) := Ψ.continuous.measurable
  have key : ∀ y : HermR R σ n, Ψ (HaarCoord.hermCoord R σ n y) = HaarCoord.hermCoord R σ n
      ⟨cjM R σ (dMat R l (s : R ⊗[F] E)) (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)),
        cjM_mem R σ hI _ _ y.2⟩ := fun y =>
    (hermCoord_cj R hinv h2 hδ hσδ s r hr l y _ rfl).symm
  have hpre : cjPre R σ (dMat R l (s : R ⊗[F] E)) Y =
      HaarCoord.hermCoord R σ n ⁻¹' (Ψ ⁻¹' (HaarCoord.hermCoord R σ n '' Y)) := by
    ext y
    constructor
    · rintro ⟨z, hz, e⟩
      rw [Set.mem_preimage, Set.mem_preimage, key]
      refine ⟨z, hz, ?_⟩
      congr 1
      exact Subtype.ext e.symm
    · rw [Set.mem_preimage, Set.mem_preimage, key]
      rintro ⟨z, hz, e⟩
      exact ⟨z, hz, (congrArg Subtype.val (hom.injective e)).symm⟩
  refine ⟨?_, ?_⟩
  · rw [hpre]
    exact hemb.measurable (hΨ hS)
  · haveI a3 : (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => coordK R b lam).IsAddHaarMeasure :=
      inferInstance
    haveI a4 : (Measure.pi fun _ : Fin n => lam).IsAddHaarMeasure := inferInstance
    haveI a5 : ((Measure.pi fun _ : Fin n => lam).prod
        (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => coordK R b lam)).IsAddHaarMeasure :=
      inferInstance
    have hc : coordHerm R σ b lam n = Measure.comap (HaarCoord.hermCoord R σ n)
        ((Measure.pi fun _ : Fin n => lam).prod
          (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => coordK R b lam)) := rfl
    have hm := map_char' ((Measure.pi fun _ : Fin n => lam).prod
      (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => coordK R b lam)) Ψ
    have hch : addEquivAddHaarChar Ψ = θ ^ n := char_total r s t θ c3 c1 c2 l
    rw [hc, hemb.comap_apply, hemb.comap_apply, hpre, Set.image_preimage_eq _ hom.surjective,
      ← Measure.map_apply hΨ hS, hm, hch, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
      ENNReal.coe_inv (pow_ne_zero _ hθ0), ENNReal.coe_pow]

end Main

end GlobalTheory.CompanionTheory.AvgFree.HD

open GlobalTheory.CompanionTheory.AvgFree.HD in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ d b v lv hlv s θ hθ n l Y hY`. Take `⟨r1, r2, r3, r4, -⟩` from `GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v`. Use `haveI := r1`. Use `haveI := r2`. Use `haveI := r3`.

Use `haveI := r4`. Use `haveI : BorelSpace (Fv F v) := ⟨rfl⟩`. Conclude with `scale_ring σ hσ (Fv F v) b lv hlv.1 s θ hθ n l Y hY`.
-/
theorem GlobalTheory.CompanionTheory.AvgFree.cjPre_dMat_scale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (s : (Fv F v ⊗[F] E)ˣ) (θ : ℝ≥0), (∀ Y : Set (Fv F v ⊗[F] E), (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) ((fun x => (s : (Fv F v ⊗[F] E)) * x) '' Y) = θ * (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) Y) → ∀ (n : ℕ) (l : Fin n) (Y : Set (HermR (Fv F v) σ n)), MeasurableSet Y → MeasurableSet (cjPre (Fv F v) σ (dMat (Fv F v) l (s : (Fv F v ⊗[F] E))) Y) ∧ (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (cjPre (Fv F v) σ (dMat (Fv F v) l (s : (Fv F v ⊗[F] E))) Y) = ((θ : ℝ≥0∞) ^ n)⁻¹ * (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) Y := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv s θ hθ n l Y hY
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  exact scale_ring σ hσ (Fv F v) b lv hlv.1 s θ hθ n l Y hY
