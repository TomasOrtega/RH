import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.RatFormPosOfIntPos
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

open Matrix in

/- English proof (translation)
Establish `hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)`. Introduce `x hx`. Simplify using `using (Matrix.posDef_iff_dotProduct_mulVec.1 hA).2 hx`. Establish `hcont : Continuous fun x : Fin n → ℝ => x ⬝ᵥ (A *ᵥ x)`. Apply `Continuous.dotProduct continuous_id` to reduce the goal to its premises.

Conclude with `Continuous.matrix_mulVec continuous_const continuous_id`. Establish `hS : IsCompact (Metric.sphere (0 : Fin n → ℝ) 1)` using `isCompact_sphere _ _`. Establish `key : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Metric.sphere (0 : Fin n → ℝ) 1, ε ≤ x ⬝ᵥ (A *ᵥ x)`. Break down `(Metric.sphere (0 : Fin n → ℝ) 1).eq_empty_or_nonempty with h | h` into its components or cases. Conclude with `⟨1, one_pos, by simp [h]⟩`.

Take `⟨x0, hx0, hmin⟩` from `hS.exists_isMinOn h hcont.continuousOn`. Use `⟨_, hpos x0 ?_, fun x hx => hmin hx⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `at hx0`. Take `⟨ε, hε, hb⟩` from `key`.

Use `⟨ε, hε, fun x => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Establish `hn : ‖x‖ ≠ 0` using `norm_ne_zero_iff.2 hx`.

Establish `hu : (‖x‖⁻¹ • x) ∈ Metric.sphere (0 : Fin n → ℝ) 1`. Simplify using `[norm_smul, hn]`. Establish `h1` using `hb _ hu`. Establish `e : (‖x‖⁻¹ • x) ⬝ᵥ (A *ᵥ (‖x‖⁻¹ • x)) = (‖x‖⁻¹) ^ 2 * (x ⬝ᵥ (A *ᵥ x))`. Rewrite using `[Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]`.

Simplify using `[sq, mul_assoc]`. Rewrite `h1` using `[e]`. Establish `h2 : 0 < ‖x‖ ^ 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem posDef_coercive {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : Fin n → ℝ, ε * ‖x‖ ^ 2 ≤ x ⬝ᵥ (A *ᵥ x) := by
  have hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x) := by
    intro x hx
    simpa using (Matrix.posDef_iff_dotProduct_mulVec.1 hA).2 hx
  have hcont : Continuous fun x : Fin n → ℝ => x ⬝ᵥ (A *ᵥ x) := by
    apply Continuous.dotProduct continuous_id
    exact Continuous.matrix_mulVec continuous_const continuous_id
  have hS : IsCompact (Metric.sphere (0 : Fin n → ℝ) 1) := isCompact_sphere _ _
  have key : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Metric.sphere (0 : Fin n → ℝ) 1, ε ≤ x ⬝ᵥ (A *ᵥ x) := by
    rcases (Metric.sphere (0 : Fin n → ℝ) 1).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨x0, hx0, hmin⟩ := hS.exists_isMinOn h hcont.continuousOn
      refine ⟨_, hpos x0 ?_, fun x hx => hmin hx⟩
      rintro rfl
      simp at hx0
  obtain ⟨ε, hε, hb⟩ := key
  refine ⟨ε, hε, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx; simp
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hu : (‖x‖⁻¹ • x) ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    simp [norm_smul, hn]
  have h1 := hb _ hu
  have e : (‖x‖⁻¹ • x) ⬝ᵥ (A *ᵥ (‖x‖⁻¹ • x)) = (‖x‖⁻¹) ^ 2 * (x ⬝ᵥ (A *ᵥ x)) := by
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp [sq, mul_assoc]
  rw [e] at h1
  have h2 : 0 < ‖x‖ ^ 2 := by positivity
  calc ε * ‖x‖ ^ 2 ≤ ((‖x‖⁻¹) ^ 2 * (x ⬝ᵥ (A *ᵥ x))) * ‖x‖ ^ 2 := by gcongr
    _ = x ⬝ᵥ (A *ᵥ x) := by field_simp

open Matrix in

/- English proof (translation)
Introduce `X _ _ _ β hsym hpos c`. Take `⟨n, b⟩ : ∃ n : ℕ, Nonempty (Module.Basis (Fin n) ℤ X)` from `⟨_, ⟨Module.finBasis ℤ X⟩⟩`. Take `⟨b⟩` from `b`. Set `Q : Matrix (Fin n) (Fin n) ℚ` to `Matrix.of fun i j => ((β (b i) (b j) : ℤ) : ℚ)`. Establish `hQs : Q.IsSymm`.

Use extensionality with `i j`. Simplify using `[Q, hsym (b i) (b j)]`. Establish `hval : ∀ v : Fin n → ℤ, β (∑ i, v i • b i) (∑ i, v i • b i) = ∑ i, ∑ j, β (b i) (b j) * v i * v j`. Introduce `v`. Simplify using `only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]`.

Use `Finset.sum_comm.trans ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hne : ∀ v : Fin n → ℤ, v ≠ 0 → (∑ i, v i • b i) ≠ 0`. Introduce `v hv h0`.

Conclude with `hv (funext (Fintype.linearIndependent_iff.1 b.linearIndependent v h0))`. Establish `hQpos : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ i, ∑ j, Q i j * v i * v j`. Introduce `v hv`. Establish `h` using `hpos _ (hne v hv)`. Rewrite `h` using `[hval]`.

Establish `h' : (0 : ℚ) < ((∑ i, ∑ j, β (b i) (b j) * v i * v j : ℤ) : ℚ)` using `by exact_mod_cast h`. Simplify `h'` using `[Q]`. Establish `hA` using `GlobalTheory.CompanionTheory.Ar.Fan.posDef_of_int_pos n Q hQs hQpos`. Take `⟨ε, hε, hco⟩` from `posDef_coercive _ hA`. Take `⟨N, hN⟩` from `exists_nat_ge ((c : ℝ) / ε)`.

Establish `hbound : ∀ v : Fin n → ℤ, β (∑ i, v i • b i) (∑ i, v i • b i) ≤ c → ∀ i, |v i| ≤ (N + 1 : ℤ)`. Introduce `v hv i`. Establish `h1` using `hco (fun i => (v i : ℝ))`. Establish `h2 : (fun i => (v i : ℝ)) ⬝ᵥ ((Q.map (Rat.cast : ℚ → ℝ)) *ᵥ (fun i => (v i : ℝ))) = ((β (∑ i, v i • b i) (∑ i, v i • b i) : ℤ) : ℝ)`. Rewrite using `[hval]`.

Simplify using `only [dotProduct, mulVec, Finset.mul_sum, Int.cast_sum, Int.cast_mul]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[Q]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[h2]`.

Establish `h3 : ((β (∑ i, v i • b i) (∑ i, v i • b i) : ℤ) : ℝ) ≤ c` using `by exact_mod_cast hv`. Establish `h4 : ‖(fun i => (v i : ℝ))‖ ^ 2 ≤ N`. Use `le_trans ?_ hN` and prove the remaining obligations. Rewrite using `[le_div_iff₀ hε]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h5 : |(v i : ℝ)| ≤ ‖(fun i => (v i : ℝ))‖`. Simplify using `using norm_le_pi_norm (fun i => (v i : ℝ)) i`. Establish `h6 : |(v i : ℝ)| ≤ (N : ℝ) + 1`. Use polynomial arithmetic with `[sq_nonneg (‖(fun i => (v i : ℝ))‖ - 1), norm_nonneg (fun i => (v i : ℝ))]`. Conclude with `h6` after adjusting the coercions.

Establish `hfin : (Set.Icc (fun _ : Fin n => -(N + 1 : ℤ)) (fun _ => (N + 1 : ℤ))).Finite` using `Set.finite_Icc _ _`. Use `(hfin.image fun v => ∑ i, v i • b i).subset ?_` and prove the remaining obligations. Introduce `y hy`. Establish `hy' : y = ∑ i, (b.repr y i) • b i` using `(b.sum_repr y).symm`. Use `⟨fun i => b.repr y i, ?_, hy'.symm⟩` and prove the remaining obligations.

Establish `hb2` using `hbound (fun i => b.repr y i) (by rw [← hy']; exact hy)`. Conclude with `⟨fun i => (abs_le.1 (hb2 i)).1, fun i => (abs_le.1 (hb2 i)).2⟩`.
-/
theorem sublevel_finite : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X]
    (β : LinearMap.BilinForm ℤ X), (∀ y z, β y z = β z y) → (∀ y, y ≠ 0 → 0 < β y y) →
    ∀ c : ℤ, {y : X | β y y ≤ c}.Finite := by
  intro X _ _ _ β hsym hpos c
  obtain ⟨n, b⟩ : ∃ n : ℕ, Nonempty (Module.Basis (Fin n) ℤ X) :=
    ⟨_, ⟨Module.finBasis ℤ X⟩⟩
  obtain ⟨b⟩ := b
  let Q : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => ((β (b i) (b j) : ℤ) : ℚ)
  have hQs : Q.IsSymm := by
    ext i j
    simp [Q, hsym (b i) (b j)]
  have hval : ∀ v : Fin n → ℤ, β (∑ i, v i • b i) (∑ i, v i • b i)
      = ∑ i, ∑ j, β (b i) (b j) * v i * v j := by
    intro v
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hne : ∀ v : Fin n → ℤ, v ≠ 0 → (∑ i, v i • b i) ≠ 0 := by
    intro v hv h0
    exact hv (funext (Fintype.linearIndependent_iff.1 b.linearIndependent v h0))
  have hQpos : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ i, ∑ j, Q i j * v i * v j := by
    intro v hv
    have h := hpos _ (hne v hv)
    rw [hval] at h
    have h' : (0 : ℚ) < ((∑ i, ∑ j, β (b i) (b j) * v i * v j : ℤ) : ℚ) := by exact_mod_cast h
    simpa [Q] using h'
  have hA := GlobalTheory.CompanionTheory.Ar.Fan.posDef_of_int_pos n Q hQs hQpos
  obtain ⟨ε, hε, hco⟩ := posDef_coercive _ hA
  obtain ⟨N, hN⟩ := exists_nat_ge ((c : ℝ) / ε)
  have hbound : ∀ v : Fin n → ℤ, β (∑ i, v i • b i) (∑ i, v i • b i) ≤ c →
      ∀ i, |v i| ≤ (N + 1 : ℤ) := by
    intro v hv i
    have h1 := hco (fun i => (v i : ℝ))
    have h2 : (fun i => (v i : ℝ)) ⬝ᵥ ((Q.map (Rat.cast : ℚ → ℝ)) *ᵥ (fun i => (v i : ℝ)))
        = ((β (∑ i, v i • b i) (∑ i, v i • b i) : ℤ) : ℝ) := by
      rw [hval]
      simp only [dotProduct, mulVec, Finset.mul_sum, Int.cast_sum, Int.cast_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp [Q]
      ring
    rw [h2] at h1
    have h3 : ((β (∑ i, v i • b i) (∑ i, v i • b i) : ℤ) : ℝ) ≤ c := by exact_mod_cast hv
    have h4 : ‖(fun i => (v i : ℝ))‖ ^ 2 ≤ N := by
      refine le_trans ?_ hN
      rw [le_div_iff₀ hε]
      linarith
    have h5 : |(v i : ℝ)| ≤ ‖(fun i => (v i : ℝ))‖ := by
      simpa using norm_le_pi_norm (fun i => (v i : ℝ)) i
    have h6 : |(v i : ℝ)| ≤ (N : ℝ) + 1 := by
      nlinarith [sq_nonneg (‖(fun i => (v i : ℝ))‖ - 1), norm_nonneg (fun i => (v i : ℝ))]
    exact_mod_cast h6
  have hfin : (Set.Icc (fun _ : Fin n => -(N + 1 : ℤ)) (fun _ => (N + 1 : ℤ))).Finite :=
    Set.finite_Icc _ _
  refine (hfin.image fun v => ∑ i, v i • b i).subset ?_
  intro y hy
  have hy' : y = ∑ i, (b.repr y i) • b i := (b.sum_repr y).symm
  refine ⟨fun i => b.repr y i, ?_, hy'.symm⟩
  have hb2 := hbound (fun i => b.repr y i) (by rw [← hy']; exact hy)
  exact ⟨fun i => (abs_le.1 (hb2 i)).1, fun i => (abs_le.1 (hb2 i)).2⟩

end GlobalTheory.CompanionTheory.Ar.Fan
