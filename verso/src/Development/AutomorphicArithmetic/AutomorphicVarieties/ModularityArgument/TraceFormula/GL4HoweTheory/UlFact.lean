import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
import Formalism.PadicSubsetSums.StableGradedCounts.BaseChangeIwahoriFactorization

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

/- English proof (translation)
Introduce `E _ _ _ _ n ϖ hϖ a c ha x hx`. Establish `hlt : valuation E ((ϖ ^ a : Eˣ) : E) < 1`. Rewrite using `[Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]`. Conclude with `zpow_lt_one₀ (by rw [← hϖ]; exact (Valuation.pos_iff _).2 ϖ.ne_zero) uniformizer_lt_one (by omega)`. Set `t : Fin n → Eˣ` to `fun i => ϖ ^ (c * ((i : ℕ) : ℤ))`.

Set `w : Fin n → Fin n → E` to `fun i j => ((t i * (t j)⁻¹ : Eˣ) : E)`. Establish `hw0 : ∀ i j, w i j ≠ 0` using `fun i j => Units.ne_zero _`. Establish `hwi : ∀ i, w i i = 1` using `fun i => by simp [w]`. Establish `hww : ∀ i k j, w i k * w k j = w i j` using `fun i k j => by`. Simplify using `only [w]`.

Rewrite using `[← Units.val_mul]`. Use `congr 1`. Use `group`. Establish `hpow : ∀ i j : Fin n, ((ϖ ^ (a + c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) : Eˣ) : E) = ((ϖ ^ a : Eˣ) : E) * w i j` using `fun i j => by`. Simplify using `only [w, t]`.

Rewrite using `[← Units.val_mul, ← zpow_neg, ← zpow_add, ← zpow_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) E) i j * w i j = (1 : Matrix (Fin n) (Fin n) E) i j` using `fun i j => by`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Rewrite using `[hwi, mul_one]`. Rewrite using `[Matrix.one_apply_ne h, zero_mul]`. Establish `key : ∀ (i j : Fin n) (z : E), valuation E (z * w i j - (1 : Matrix (Fin n) (Fin n) E) i j) ≤ valuation E ((ϖ ^ (a + c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) : Eˣ) : E) ↔ valuation E (z - (1 : Matrix (Fin n) (Fin n) E) i j) ≤ valuation E ((ϖ ^ a : Eˣ) : E)` using `fun i j z => by`. Rewrite using `[hpow, ← hone i j, ← sub_mul, hone, map_mul, map_mul]`.

Conclude with `mul_le_mul_iff_left₀ ((Valuation.pos_iff (valuation E)).2 (hw0 i j))`. Establish `hg : ∀ i j, valuation E ((x : Matrix (Fin n) (Fin n) E) i j / w i j - (1 : Matrix (Fin n) (Fin n) E) i j) ≤ valuation E ((ϖ ^ a : Eˣ) : E)` using `fun i j => (key i j _).1 (by rw [div_mul_cancel₀ _ (hw0 i j)]; exact hx i j)`. Establish `h1 : ∀ i j, valuation E ((1 : Matrix (Fin n) (Fin n) E) i j) ≤ 1` using `fun i j => by`. Rewrite using `[Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hint : ∀ i j, (x : Matrix (Fin n) (Fin n) E) i j / w i j ∈ 𝒪[E]` using `fun i j => by`. Express the relevant statement in the definitionally equal form `valuation E _ ≤ 1`. Rewrite using `[← sub_add_cancel (_ / w i j) ((1 : Matrix (Fin n) (Fin n) E) i j)]`. Conclude with `Valuation.map_add_le _ ((hg i j).trans hlt.le) (h1 i j)`. Set `I : Ideal 𝒪[E]` to `{ carrier := {z | valuation E (z : E) ≤ valuation E ((ϖ ^ a : Eˣ) : E)} add_mem' := fun {y z} h h' => by`.

Rewrite `h`, `h'`, the goal using `[Set.mem_setOf_eq]`. Rewrite using `[Subring.coe_add]`. Conclude with `Valuation.map_add_le _ h h'`. Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := fun r z h => by`.

Rewrite `h`, the goal using `[Set.mem_setOf_eq]`. Rewrite using `[smul_eq_mul, Subring.coe_mul, map_mul]`. Simplify using `using mul_le_mul' (show valuation E (r : E) ≤ 1 from r.2) h }`. Establish `hI : ∀ z : 𝒪[E], z ∈ I ↔ valuation E (z : E) ≤ valuation E ((ϖ ^ a : Eˣ) : E)` using `fun _ => Iff.rfl`. Establish `hIm : I ≤ IsLocalRing.maximalIdeal 𝒪[E]` using `IsLocalRing.le_maximalIdeal fun h => by`.

Establish `: (1 : 𝒪[E]) ∈ I` using `h ▸ Submodule.mem_top`. Rewrite `this` using `[hI]`. Conclude with `absurd (lt_of_le_of_lt this hlt) (by simp)`. Set `g : Matrix (Fin n) (Fin n) 𝒪[E]` to `fun i j => ⟨_, hint i j⟩`. Establish `hgd : ∀ i, g i i - 1 ∈ I` using `fun i => by`.

Use `hg i i` as an intermediate fact. Rewrite `this` using `[Matrix.one_apply_eq]`. Then use the resulting hypothesis. Establish `hgo : ∀ i j, i ≠ j → g i j ∈ I` using `fun i j h => by`. Use `hg i j` as an intermediate fact. Rewrite `this` using `[Matrix.one_apply_ne h, sub_zero]`. Then use the resulting hypothesis.

Take `⟨X, Y, δ, e, x1, x0, -, -, hδ, y1, y0, yL⟩` from `Formalism.IrreducibleCountingLemmas.Z.iwahori_factorization_exists 𝒪[E] I I hIm n g (fun i => by`. Use `Formalism.IrreducibleCountingLemmas.Z.isUnit_sub_of_mem_maximalIdeal isUnit_one (hIm (I.neg_mem (hgd i)))` as an intermediate fact. Simplify using `using this)`. Use the proof step `(fun i j h => hgo i j h.ne) fun i j h => hgo i j h.ne'`. Set `U : Matrix (Fin n) (Fin n) E` to `fun i j => (X i j : E) * w i j`.

Set `B : Matrix (Fin n) (Fin n) E` to `fun i j => ((δ i * Y i j : 𝒪[E]) : E) * w i j`. Establish `hU0 : ∀ i j, j < i → U i j = 0` using `fun i j h => by simp [U, x0 i j h]`. Establish `hU1 : ∀ i, U i i = 1` using `fun i => by simp [U, x1, hwi]`. Establish `hdet : U.det ≠ 0`. Rewrite using `[Matrix.det_of_upperTriangular (fun i j h => hU0 i j h)]`.

Simplify using `[hU1]`. Set `u : GL (Fin n) E` to `Matrix.GeneralLinearGroup.mkOfDetNeZero U hdet`. Establish `hUB : U * B = (x : Matrix (Fin n) (Fin n) E)`. Use extensionality with `i j`. Establish `h2 : (x : Matrix (Fin n) (Fin n) E) i j / w i j = ∑ k, (X i k : E) * δ k * Y k j`.

Use `congrArg (fun z : 𝒪[E] => (z : E)) (e i j)` as an intermediate fact. Simplify `this` using `[g]`. Rewrite using `[← div_mul_cancel₀ ((x : Matrix (Fin n) (Fin n) E) i j) (hw0 i j), h2, Matrix.mul_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [U, B]`.

Rewrite using `[← hww i k j]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hb : ((u⁻¹ * x : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = B`. Rewrite using `[Units.val_mul, ← hUB]`.

Express the relevant statement in the definitionally equal form `(u⁻¹).val * (u.val * B) = B`. Rewrite using `[← mul_assoc, Units.inv_mul, one_mul]`. Use `⟨u, (mem_unipB E).2 ⟨hU0, hU1⟩, u⁻¹ * x, fun i j => ?_, (mul_inv_cancel_left _ _).symm, fun i j h => ?_⟩` and prove the remaining obligations. Rewrite using `[hb]`. Use `(key i j _).2 ?_` and prove the remaining obligations.

Break down `lt_trichotomy i j with h | h | h` into its components or cases. Rewrite using `[y0 i j h, Matrix.one_apply_ne h.ne]`. Simplify using the standard rewrite rules. Substitute `h` using the available equality. Rewrite using `[y1, mul_one, Matrix.one_apply_eq]`.

Establish `: δ i - 1 ∈ I`. Simplify using `using I.add_mem (Ideal.mul_le_left (hδ i)) (hgd i)`. Conclude with `this`. Rewrite using `[Matrix.one_apply_ne h.ne', sub_zero]`. Conclude with `(hI _).1 (I.mul_mem_left _ (yL i j h))`.

Rewrite using `[hb]`. Simplify using `[B, y0 i j h]`.
-/
theorem UpperTheory.V.Z.Tf.L4.ulFact :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ a c : ℤ, 1 ≤ a → ∀ x ∈ howeSet n ϖ a c,
      ∃ u ∈ unipB E (Fin n), ∃ b ∈ howeSet n ϖ a c, x = u * b ∧ ∀ i j : Fin n, i < j → (b : Matrix (Fin n) (Fin n) E) i j = 0 := by
  intro E _ _ _ _ n ϖ hϖ a c ha x hx
  have hlt : valuation E ((ϖ ^ a : Eˣ) : E) < 1 := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ]
    exact zpow_lt_one₀ (by rw [← hϖ]; exact (Valuation.pos_iff _).2 ϖ.ne_zero) uniformizer_lt_one (by omega)
  let t : Fin n → Eˣ := fun i => ϖ ^ (c * ((i : ℕ) : ℤ))
  let w : Fin n → Fin n → E := fun i j => ((t i * (t j)⁻¹ : Eˣ) : E)
  have hw0 : ∀ i j, w i j ≠ 0 := fun i j => Units.ne_zero _
  have hwi : ∀ i, w i i = 1 := fun i => by simp [w]
  have hww : ∀ i k j, w i k * w k j = w i j := fun i k j => by
    simp only [w]
    rw [← Units.val_mul]
    congr 1
    group
  have hpow : ∀ i j : Fin n, ((ϖ ^ (a + c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) : Eˣ) : E) = ((ϖ ^ a : Eˣ) : E) * w i j := fun i j => by
    simp only [w, t]
    rw [← Units.val_mul, ← zpow_neg, ← zpow_add, ← zpow_add]
    congr 2
    ring
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) E) i j * w i j = (1 : Matrix (Fin n) (Fin n) E) i j := fun i j => by
    by_cases h : i = j
    · subst h; rw [hwi, mul_one]
    · rw [Matrix.one_apply_ne h, zero_mul]
  have key : ∀ (i j : Fin n) (z : E), valuation E (z * w i j - (1 : Matrix (Fin n) (Fin n) E) i j) ≤
      valuation E ((ϖ ^ (a + c * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) : Eˣ) : E) ↔
      valuation E (z - (1 : Matrix (Fin n) (Fin n) E) i j) ≤ valuation E ((ϖ ^ a : Eˣ) : E) := fun i j z => by
    rw [hpow, ← hone i j, ← sub_mul, hone, map_mul, map_mul]
    exact mul_le_mul_iff_left₀ ((Valuation.pos_iff (valuation E)).2 (hw0 i j))
  have hg : ∀ i j, valuation E ((x : Matrix (Fin n) (Fin n) E) i j / w i j - (1 : Matrix (Fin n) (Fin n) E) i j) ≤
      valuation E ((ϖ ^ a : Eˣ) : E) := fun i j => (key i j _).1 (by rw [div_mul_cancel₀ _ (hw0 i j)]; exact hx i j)
  have h1 : ∀ i j, valuation E ((1 : Matrix (Fin n) (Fin n) E) i j) ≤ 1 := fun i j => by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have hint : ∀ i j, (x : Matrix (Fin n) (Fin n) E) i j / w i j ∈ 𝒪[E] := fun i j => by
    change valuation E _ ≤ 1
    rw [← sub_add_cancel (_ / w i j) ((1 : Matrix (Fin n) (Fin n) E) i j)]
    exact Valuation.map_add_le _ ((hg i j).trans hlt.le) (h1 i j)
  let I : Ideal 𝒪[E] :=
    { carrier := {z | valuation E (z : E) ≤ valuation E ((ϖ ^ a : Eˣ) : E)}
      add_mem' := fun {y z} h h' => by
        rw [Set.mem_setOf_eq] at h h' ⊢
        rw [Subring.coe_add]
        exact Valuation.map_add_le _ h h'
      zero_mem' := by simp
      smul_mem' := fun r z h => by
        rw [Set.mem_setOf_eq] at h ⊢
        rw [smul_eq_mul, Subring.coe_mul, map_mul]
        simpa using mul_le_mul' (show valuation E (r : E) ≤ 1 from r.2) h }
  have hI : ∀ z : 𝒪[E], z ∈ I ↔ valuation E (z : E) ≤ valuation E ((ϖ ^ a : Eˣ) : E) := fun _ => Iff.rfl
  have hIm : I ≤ IsLocalRing.maximalIdeal 𝒪[E] := IsLocalRing.le_maximalIdeal fun h => by
    have : (1 : 𝒪[E]) ∈ I := h ▸ Submodule.mem_top
    rw [hI] at this
    exact absurd (lt_of_le_of_lt this hlt) (by simp)
  let g : Matrix (Fin n) (Fin n) 𝒪[E] := fun i j => ⟨_, hint i j⟩
  have hgd : ∀ i, g i i - 1 ∈ I := fun i => by
    have := hg i i
    rwa [Matrix.one_apply_eq] at this
  have hgo : ∀ i j, i ≠ j → g i j ∈ I := fun i j h => by
    have := hg i j
    rwa [Matrix.one_apply_ne h, sub_zero] at this
  obtain ⟨X, Y, δ, e, x1, x0, -, -, hδ, y1, y0, yL⟩ := Formalism.IrreducibleCountingLemmas.Z.iwahori_factorization_exists 𝒪[E] I I hIm n g
    (fun i => by
      have := Formalism.IrreducibleCountingLemmas.Z.isUnit_sub_of_mem_maximalIdeal isUnit_one (hIm (I.neg_mem (hgd i)))
      simpa using this)
    (fun i j h => hgo i j h.ne) fun i j h => hgo i j h.ne'
  let U : Matrix (Fin n) (Fin n) E := fun i j => (X i j : E) * w i j
  let B : Matrix (Fin n) (Fin n) E := fun i j => ((δ i * Y i j : 𝒪[E]) : E) * w i j
  have hU0 : ∀ i j, j < i → U i j = 0 := fun i j h => by simp [U, x0 i j h]
  have hU1 : ∀ i, U i i = 1 := fun i => by simp [U, x1, hwi]
  have hdet : U.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular (fun i j h => hU0 i j h)]
    simp [hU1]
  let u : GL (Fin n) E := Matrix.GeneralLinearGroup.mkOfDetNeZero U hdet
  have hUB : U * B = (x : Matrix (Fin n) (Fin n) E) := by
    ext i j
    have h2 : (x : Matrix (Fin n) (Fin n) E) i j / w i j = ∑ k, (X i k : E) * δ k * Y k j := by
      have := congrArg (fun z : 𝒪[E] => (z : E)) (e i j)
      simpa [g] using this
    rw [← div_mul_cancel₀ ((x : Matrix (Fin n) (Fin n) E) i j) (hw0 i j), h2, Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [U, B]
    rw [← hww i k j]
    push_cast
    ring
  have hb : ((u⁻¹ * x : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = B := by
    rw [Units.val_mul, ← hUB]
    change (u⁻¹).val * (u.val * B) = B
    rw [← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨u, (mem_unipB E).2 ⟨hU0, hU1⟩, u⁻¹ * x, fun i j => ?_, (mul_inv_cancel_left _ _).symm, fun i j h => ?_⟩
  · rw [hb]
    refine (key i j _).2 ?_
    rcases lt_trichotomy i j with h | h | h
    · rw [y0 i j h, Matrix.one_apply_ne h.ne]
      simp
    · subst h
      rw [y1, mul_one, Matrix.one_apply_eq]
      have : δ i - 1 ∈ I := by
        simpa using I.add_mem (Ideal.mul_le_left (hδ i)) (hgd i)
      exact this
    · rw [Matrix.one_apply_ne h.ne', sub_zero]
      exact (hI _).1 (I.mul_mem_left _ (yL i j h))
  · rw [hb]
    simp [B, y0 i j h]
