import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.RealPlaceAnalysis.QuotientSettingHolds

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.DerOf

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Unfold `Rd`. Use `congr 1`. Use function extensionality and compare the values at `t`. Conclude with `h _ (indefinite_unitary_mul_mem ε hg (exp_indefinite_unitary_holds n ε X hX t))`.
-/
theorem rd_congr {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : ∀ g, inUJ ε g → f g = f' g)
    {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) : Rd X f g = Rd X f' g := by
  unfold Rd
  congr 1
  funext t
  exact h _ (indefinite_unitary_mul_mem ε hg (exp_indefinite_unitary_holds n ε X hX t))

/- English proof (translation)
Take `⟨h1, h2, -, -⟩` from `complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)`. Unfold `Eab Ec`. Rewrite using `[rd_congr h h1 hg, rd_congr h h2 hg]`.
-/
theorem eab_congr {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : ∀ g, inUJ ε g → f g = f' g)
    (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : Eab ε a b f g = Eab ε a b f' g := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  unfold Eab Ec
  rw [rd_congr h h1 hg, rd_congr h h2 hg]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Jm, sgn, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply]`. Distinguish the cases in `h : a = i ∧ b = j`. Take `⟨rfl, rfl⟩` from `h`. Apply the tactic sequence `cases ε a <;> cases ε b <;> simp`.

Simplify using `[h]`.
-/
theorem J_single_J (a b : Fin n) :
    Jm ε * Matrix.single a b (1 : ℂ) * Jm ε = (sgn ε a b : ℂ) • Matrix.single a b (1 : ℂ) := by
  ext i j
  simp only [Jm, sgn, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    cases ε a <;> cases ε b <;> simp
  · simp [h]

/- English proof (translation)
Simplify using `only [sgn, eq_comm]`.
-/
theorem sgn_comm (a b : Fin n) : sgn ε a b = sgn ε b a := by
  simp only [sgn, eq_comm]

/- English proof (translation)
Unfold `sgn`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem sgn_sq (a b : Fin n) : (sgn ε a b : ℂ) * sgn ε a b = 1 := by
  unfold sgn
  split_ifs <;> simp

/- English proof (translation)
Simplify using `only [cpart1, conjTranspose_single, star_one, J_single_J, sgn_comm (ε := ε) b a]`. Use `sgn_sq (ε := ε) a b` as an intermediate fact. Use `push_cast`. Use `match_scalars`. Take the linear combination `(-1 / 2 : ℂ) * this`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cpart1_swap (a b : Fin n) : cpart1 ε (Matrix.single a b (1 : ℂ)) =
    ((-sgn ε a b : ℝ) : ℂ) • cpart1 ε (Matrix.single b a (1 : ℂ)) := by
  simp only [cpart1, conjTranspose_single, star_one, J_single_J, sgn_comm (ε := ε) b a]
  have := sgn_sq (ε := ε) a b
  push_cast
  match_scalars
  · linear_combination (-1 / 2 : ℂ) * this
  · ring

/- English proof (translation)
Simplify using `only [cpart2, conjTranspose_single, star_one, J_single_J, sgn_comm (ε := ε) b a]`. Use `sgn_sq (ε := ε) a b` as an intermediate fact. Use `match_scalars`. Take the linear combination `(-1 / (2 * Complex.I) : ℂ) * this`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cpart2_swap (a b : Fin n) : cpart2 ε (Matrix.single a b (1 : ℂ)) =
    ((sgn ε a b : ℝ) : ℂ) • cpart2 ε (Matrix.single b a (1 : ℂ)) := by
  simp only [cpart2, conjTranspose_single, star_one, J_single_J, sgn_comm (ε := ε) b a]
  have := sgn_sq (ε := ε) a b
  match_scalars
  · linear_combination (-1 / (2 * Complex.I) : ℂ) * this
  · ring

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {V : Submodule ℂ H}

/- English proof (translation)
Distinguish the cases in `hX : inG ε X`. Use `choose d hd hd' using fun v : V => hV v v.2 X hX`. Use `⟨⟨⟨fun v => ⟨d v, hd v⟩, fun v w => Subtype.ext ?_⟩, fun c v => Subtype.ext ?_⟩, fun _ v => hd' v⟩` and prove the remaining obligations. Use `(hd' (v + w)).unique ?_` and prove the remaining obligations. Simplify using `using (hd' v).fun_add (hd' w)`.

Use `(hd' (c • v)).unique ?_` and prove the remaining obligations. Simplify using `using (hd' v).fun_const_smul c`. Conclude with `⟨0, fun h => absurd h hX⟩`.
-/
theorem exists_D (hV : ∀ v ∈ V, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → ∃ v' ∈ V,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∃ D : Module.End ℂ V, inG ε X → ∀ v : V,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) (D v : H) 0 := by
  by_cases hX : inG ε X
  · choose d hd hd' using fun v : V => hV v v.2 X hX
    refine ⟨⟨⟨fun v => ⟨d v, hd v⟩, fun v w => Subtype.ext ?_⟩, fun c v => Subtype.ext ?_⟩, fun _ v => hd' v⟩
    · refine (hd' (v + w)).unique ?_
      simpa using (hd' v).fun_add (hd' w)
    · refine (hd' (c • v)).unique ?_
      simpa using (hd' v).fun_const_smul c
  · exact ⟨0, fun h => absurd h hX⟩

/- English proof (translation)
Establish `h1` using `(((innerSL ℂ y).comp (σ g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h`. Use `Eq.trans ?_ h1.deriv` and prove the remaining obligations. Unfold `Rd`. Use `congr 1`. Use function extensionality and compare the values at `t`.

Use `hσ.1.2 g hg _ (exp_indefinite_unitary_holds n ε X hX t)` as an intermediate fact. Simplify using `only [this]`. Both sides reduce to the same expression.
-/
theorem rd_coef (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {v v' : H}
    (h : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0) (y : H)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Rd X (fun g => ⟪y, σ g v⟫_ℂ) g = ⟪y, σ g v'⟫_ℂ := by
  have h1 := (((innerSL ℂ y).comp (σ g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h
  refine Eq.trans ?_ h1.deriv
  unfold Rd
  congr 1
  funext t
  have := hσ.1.2 g hg _ (exp_indefinite_unitary_holds n ε X hX t)
  simp only [this]
  rfl

/- English proof (translation)
Establish `h` using `hx.inner ℂ hy`. Establish `hc : (fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • X)) x, σ (NormedSpace.exp ((t : ℂ) • X)) y⟫_ℂ) = fun _ => ⟪x, y⟫_ℂ`. Use function extensionality and compare the values at `t`. Conclude with `LinearIsometry.inner_map_map ⟨(σ (NormedSpace.exp ((t : ℂ) • X))).toLinearMap, hσ.2.1 _ (exp_indefinite_unitary_holds n ε X hX t)⟩ x y`. Rewrite `h` using `[hc]`.

Establish `h0` using `h.unique (hasDerivAt_const (0 : ℝ) _)`. Simplify using `only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1, ContinuousLinearMap.one_apply] at h0`. Take the linear combination `h0`.
-/
theorem skew (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {x x' y y' : H}
    (hx : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) x) x' 0)
    (hy : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) y) y' 0) :
    ⟪x', y⟫_ℂ = -⟪x, y'⟫_ℂ := by
  have h := hx.inner ℂ hy
  have hc : (fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • X)) x, σ (NormedSpace.exp ((t : ℂ) • X)) y⟫_ℂ)
      = fun _ => ⟪x, y⟫_ℂ := by
    funext t
    exact LinearIsometry.inner_map_map
      ⟨(σ (NormedSpace.exp ((t : ℂ) • X))).toLinearMap, hσ.2.1 _ (exp_indefinite_unitary_holds n ε X hX t)⟩ x y
  rw [hc] at h
  have h0 := h.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1, ContinuousLinearMap.one_apply] at h0
  linear_combination h0

/- English proof (translation)
Introduce `n ε H _ _ _ σ V hσ hV hs`. Use `choose D hD using exists_D hV`. Establish `hone : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ)` using `by simp [inUJ]`. Establish `h1 : ∀ v : H, σ 1 v = v` using `fun v => by rw [hσ.1.1]; rfl`. Establish `hc` using `fun a b : Fin n => complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)`.

Establish `hR : ∀ X, inG ε X → ∀ (v : V) (y : H) g, inUJ ε g → Rd X (fun g => ⟪y, σ g v⟫_ℂ) g = ⟪y, σ g (D X v)⟫_ℂ` using `fun X hX v y g hg => rd_coef hσ hX (hD X hX v) y hg`. Use `set E : Fin n → Fin n → Module.End ℂ V := fun a b => D (cpart1 ε (Matrix.single a b 1)) + Complex.I • D (cpart2 ε (Matrix.single a b 1)) with hE`. Establish `hEab : ∀ a b (v : V) (y : H) g, inUJ ε g → Eab ε a b (fun g => ⟪y, σ g v⟫_ℂ) g = ⟪y, σ g (E a b v)⟫_ℂ`. Introduce `a b v y g hg`. Unfold `Eab Ec`.

Rewrite using `[hR _ (hc a b).1 v y g hg, hR _ (hc a b).2.1 v y g hg]`. Simplify using `[hE, inner_add_right, inner_smul_right]`. Establish `hsm : ∀ X (r : ℝ), inG ε X → inG ε ((r : ℂ) • X) → ∀ v : V, (D ((r : ℂ) • X) v : H) = (r : ℂ) • (D X v : H)`. Introduce `X r hX hrX v`. Use `ext_inner_left ℂ fun y => ?_` and prove the remaining obligations.

Use `(rdLin n ε _ _ X X r 0 1 (hs v v.2 y) (hs v v.2 y) hX hX hone).2.1` as an intermediate fact. Rewrite `this` using `[hR _ hX v y 1 hone, hR _ hrX v y 1 hone, h1, h1, ← inner_smul_right]`. Then use the resulting hypothesis. Use `⟨E, ?_, ?_, ?_, fun v y => hs v v.2 y⟩` and prove the remaining obligations. Introduce `a b c d`. Use `LinearMap.ext fun v => Subtype.ext (ext_inner_left ℂ fun y => ?_)` and prove the remaining obligations.

Use `eabGl n ε _ a b c d 1 (hs v v.2 y) hone` as an intermediate fact. Rewrite `this` using `[eab_congr (hEab c d v y) a b hone, eab_congr (hEab a b v y) c d hone]`. Simplify using `only [hEab _ _ _ y 1 hone, h1] at this`. Apply the tactic sequence `split_ifs at this ⊢ <;> simpa [inner_sub_right] using this`. Introduce `a b x y`.

Establish `e1` using `hsm _ (-sgn ε a b) (hc b a).1 (cpart1_swap a b ▸ (hc a b).1) y`. Establish `e2` using `hsm _ (sgn ε a b) (hc b a).2.1 (cpart2_swap a b ▸ (hc a b).2.1) y`. Rewrite `e1` using `[← cpart1_swap]`. Rewrite `e2` using `[← cpart2_swap]`. Establish `s1` using `skew hσ (hc a b).1 (hD _ (hc a b).1 x) (hD _ (hc a b).1 y)`.

Establish `s2` using `skew hσ (hc a b).2.1 (hD _ (hc a b).2.1 x) (hD _ (hc a b).2.1 y)`. Rewrite `s1` using `[e1, inner_smul_right]`. Rewrite `s2` using `[e2, inner_smul_right]`. Simplify using `only [hE, Submodule.coe_inner, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, s1, s2, Complex.conj_I]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Introduce `X hX v`. Use `hD X hX v using 1` and compare the differences between its conclusion and the goal. Use `ext_inner_left ℂ fun y => ?_` and prove the remaining obligations. Use `ecSumV n ε ℂ _ X 1 (hs v v.2 y) hone` as an intermediate fact.

Take `⟨e1, e2⟩` from `(complex_parts_mem_lie_algebra_holds n ε X).2.2.2 hX`. Simplify using `only [eabV_eq, hEab _ _ _ y 1 hone, h1] at this`. Rewrite `this` using `[EcV, e1, e2, rdV_eq, rdV_eq, hR _ hX v y 1 hone, h1]`. Simplify `this.symm` using `[Rd, inner_sum, inner_smul_right]`.
-/
theorem exists_isDer : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H),
    IsURepOn (UJset ε) σ →
    (∀ v ∈ V, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → ∃ v' ∈ V,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0) →
    (∀ v ∈ V, ∀ y : H, SmoothOnG ε (fun g => ⟪y, σ g v⟫_ℂ)) →
    ∃ E : Fin n → Fin n → Module.End ℂ V, IsDer ε σ V E := by
  intro n ε H _ _ _ σ V hσ hV hs
  choose D hD using exists_D hV
  have hone : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]
  have h1 : ∀ v : H, σ 1 v = v := fun v => by rw [hσ.1.1]; rfl
  have hc := fun a b : Fin n => complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  have hR : ∀ X, inG ε X → ∀ (v : V) (y : H) g, inUJ ε g →
      Rd X (fun g => ⟪y, σ g v⟫_ℂ) g = ⟪y, σ g (D X v)⟫_ℂ :=
    fun X hX v y g hg => rd_coef hσ hX (hD X hX v) y hg
  set E : Fin n → Fin n → Module.End ℂ V := fun a b =>
    D (cpart1 ε (Matrix.single a b 1)) + Complex.I • D (cpart2 ε (Matrix.single a b 1)) with hE
  have hEab : ∀ a b (v : V) (y : H) g, inUJ ε g →
      Eab ε a b (fun g => ⟪y, σ g v⟫_ℂ) g = ⟪y, σ g (E a b v)⟫_ℂ := by
    intro a b v y g hg
    unfold Eab Ec
    rw [hR _ (hc a b).1 v y g hg, hR _ (hc a b).2.1 v y g hg]
    simp [hE, inner_add_right, inner_smul_right]
  have hsm : ∀ X (r : ℝ), inG ε X → inG ε ((r : ℂ) • X) → ∀ v : V,
      (D ((r : ℂ) • X) v : H) = (r : ℂ) • (D X v : H) := by
    intro X r hX hrX v
    refine ext_inner_left ℂ fun y => ?_
    have := (rdLin n ε _ _ X X r 0 1 (hs v v.2 y) (hs v v.2 y) hX hX hone).2.1
    rwa [hR _ hX v y 1 hone, hR _ hrX v y 1 hone, h1, h1, ← inner_smul_right] at this
  refine ⟨E, ?_, ?_, ?_, fun v y => hs v v.2 y⟩
  · intro a b c d
    refine LinearMap.ext fun v => Subtype.ext (ext_inner_left ℂ fun y => ?_)
    have := eabGl n ε _ a b c d 1 (hs v v.2 y) hone
    rw [eab_congr (hEab c d v y) a b hone, eab_congr (hEab a b v y) c d hone] at this
    simp only [hEab _ _ _ y 1 hone, h1] at this
    split_ifs at this ⊢ <;> simpa [inner_sub_right] using this
  · intro a b x y
    have e1 := hsm _ (-sgn ε a b) (hc b a).1 (cpart1_swap a b ▸ (hc a b).1) y
    have e2 := hsm _ (sgn ε a b) (hc b a).2.1 (cpart2_swap a b ▸ (hc a b).2.1) y
    rw [← cpart1_swap] at e1
    rw [← cpart2_swap] at e2
    have s1 := skew hσ (hc a b).1 (hD _ (hc a b).1 x) (hD _ (hc a b).1 y)
    have s2 := skew hσ (hc a b).2.1 (hD _ (hc a b).2.1 x) (hD _ (hc a b).2.1 y)
    rw [e1, inner_smul_right] at s1
    rw [e2, inner_smul_right] at s2
    simp only [hE, Submodule.coe_inner, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add,
      Submodule.coe_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, s1, s2,
      Complex.conj_I]
    push_cast
    ring
  · intro X hX v
    convert hD X hX v using 1
    refine ext_inner_left ℂ fun y => ?_
    have := ecSumV n ε ℂ _ X 1 (hs v v.2 y) hone
    obtain ⟨e1, e2⟩ := (complex_parts_mem_lie_algebra_holds n ε X).2.2.2 hX
    simp only [eabV_eq, hEab _ _ _ y 1 hone, h1] at this
    rw [EcV, e1, e2, rdV_eq, rdV_eq, hR _ hX v y 1 hone, h1] at this
    simpa [Rd, inner_sum, inner_smul_right] using this.symm

end GlobalTheory.DerOf
