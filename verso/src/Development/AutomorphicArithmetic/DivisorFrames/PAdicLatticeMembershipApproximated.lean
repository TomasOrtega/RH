import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

/- English proof (translation)
Establish `hq0 : 0 < q` using `by linarith`. Establish `hsm : ∀ cf : Fin g → K, (∀ i, ‖cf i‖ ≤ q ^ 2) → ∀ a, ‖∑ i, (h a i - k a i) * cf i‖ ≤ 1`. Introduce `cf hc a`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Establish `h1 : q⁻¹ ^ n ≤ q⁻¹ ^ 2` using `pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hq.le) hn`. Combine the equalities or inequalities in the displayed calculation. Establish `key : ∀ cf : Fin g → K, (∀ i, ‖cf i‖ ≤ q ^ 2) → (cf ∈ Λ ↔ ∀ a, ‖∑ i, k a i * cf i‖ ≤ 1)`. Introduce `cf hc`. Rewrite using `[hΛ]`.

Use `forall_congr' fun a => ?_` and prove the remaining obligations. Establish `e : ∑ i, (h a i - k a i) * cf i = ∑ i, h a i * cf i - ∑ i, k a i * cf i`. Simplify using `[sub_mul, Finset.sum_sub_distrib]`. Establish `hs` using `hsm cf hc a`. Rewrite `hs` using `[e]`.

Prove the components needed by the constructor for the conclusion. Introduce `h1`. Establish `: ∑ i, k a i * cf i = ∑ i, h a i * cf i + -(∑ i, h a i * cf i - ∑ i, k a i * cf i)` using `by ring`. Rewrite using `[this]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 (by rwa [norm_neg]))`.

Introduce `h1`. Establish `: ∑ i, h a i * cf i = ∑ i, k a i * cf i + (∑ i, h a i * cf i - ∑ i, k a i * cf i)` using `by ring`. Rewrite using `[this]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 hs)`. Establish `hb' : ∀ cf ∈ Λ, ∀ i, ‖cf i‖ ≤ q`.

Introduce `cf hc i`. Use `hb cf hc i` as an intermediate fact. Rewrite `this` using `[norm_mul, hπ, inv_mul_le_iff₀ hq0, _root_.mul_one]`. Then use the resulting hypothesis. Prove the components needed by the constructor for the conclusion. Introduce `hc`.

Use `(key cf fun i => (hb' cf hc i).trans ?_).1 hc` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities. Establish `ind : ∀ m : ℕ, ∀ cf : Fin g → K, (∀ i, ‖cf i‖ ≤ q ^ (m + 2)) → (∀ a, ‖∑ i, k a i * cf i‖ ≤ 1) → cf ∈ Λ`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => intro cf hc h1; exact (key cf (by simpa using hc)).2 h1`. Consider the case `succ m ih`. Introduce `cf hc h1`. Establish `h2 : (fun i => π * cf i) ∈ Λ`. Use `ih _ (fun i => ?_) fun a => ?_` and prove the remaining obligations.

Rewrite using `[norm_mul, hπ, inv_mul_le_iff₀ hq0]`. Combine the equalities or inequalities in the displayed calculation. Establish `: ∑ i, k a i * (π * cf i) = π * ∑ i, k a i * cf i`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring`. Rewrite using `[this, norm_mul, hπ, inv_mul_le_iff₀ hq0]`.

Conclude with `(h1 a).trans (by linarith)`. Use `(key cf fun i => ?_).2 h1` and prove the remaining obligations. Establish `h3` using `hb' _ h2 i`. Rewrite `h3` using `[norm_mul, hπ, inv_mul_le_iff₀ hq0]`. Rewrite using `[sq]` and apply the resulting hypothesis.

Take `⟨m, hm⟩` from `pow_unbounded_of_one_lt ‖cf‖ hq`. Use `ind m cf fun i => (norm_le_pi_norm cf i).trans (hm.le.trans ?_)` and prove the remaining obligations. Conclude with `pow_le_pow_right₀ hq.le (by omega)`.
-/
private theorem lattice_membership_stable_under_approximation {K : Type} [NormedField K] [IsUltrametricDist K] {A : Type} {g : ℕ} (π : K) (q : ℝ) (hq : 1 < q)
    (hπ : ‖π‖ = q⁻¹) (n : ℕ) (hn : 2 ≤ n) (h k : A → Fin g → K) (Λ : Set (Fin g → K))
    (hk : ∀ a i, ‖h a i - k a i‖ ≤ q⁻¹ ^ n) (hΛ : ∀ cf, cf ∈ Λ ↔ ∀ a, ‖∑ i, h a i * cf i‖ ≤ 1)
    (hb : ∀ cf ∈ Λ, ∀ i, ‖π * cf i‖ ≤ 1) (cf : Fin g → K) : cf ∈ Λ ↔ ∀ a, ‖∑ i, k a i * cf i‖ ≤ 1 := by
  have hq0 : 0 < q := by linarith
  have hsm : ∀ cf : Fin g → K, (∀ i, ‖cf i‖ ≤ q ^ 2) → ∀ a, ‖∑ i, (h a i - k a i) * cf i‖ ≤ 1 := by
    intro cf hc a
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul]
    have h1 : q⁻¹ ^ n ≤ q⁻¹ ^ 2 :=
      pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hq.le) hn
    calc ‖h a i - k a i‖ * ‖cf i‖ ≤ q⁻¹ ^ 2 * q ^ 2 :=
          mul_le_mul ((hk a i).trans h1) (hc i) (norm_nonneg _) (by positivity)
      _ = 1 := by field_simp
  have key : ∀ cf : Fin g → K, (∀ i, ‖cf i‖ ≤ q ^ 2) → (cf ∈ Λ ↔ ∀ a, ‖∑ i, k a i * cf i‖ ≤ 1) := by
    intro cf hc
    rw [hΛ]
    refine forall_congr' fun a => ?_
    have e : ∑ i, (h a i - k a i) * cf i = ∑ i, h a i * cf i - ∑ i, k a i * cf i := by
      simp [sub_mul, Finset.sum_sub_distrib]
    have hs := hsm cf hc a
    rw [e] at hs
    constructor
    · intro h1
      have : ∑ i, k a i * cf i = ∑ i, h a i * cf i + -(∑ i, h a i * cf i - ∑ i, k a i * cf i) := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 (by rwa [norm_neg]))
    · intro h1
      have : ∑ i, h a i * cf i = ∑ i, k a i * cf i + (∑ i, h a i * cf i - ∑ i, k a i * cf i) := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 hs)
  have hb' : ∀ cf ∈ Λ, ∀ i, ‖cf i‖ ≤ q := by
    intro cf hc i
    have := hb cf hc i
    rwa [norm_mul, hπ, inv_mul_le_iff₀ hq0, _root_.mul_one] at this
  constructor
  · intro hc
    refine (key cf fun i => (hb' cf hc i).trans ?_).1 hc
    nlinarith
  · have ind : ∀ m : ℕ, ∀ cf : Fin g → K, (∀ i, ‖cf i‖ ≤ q ^ (m + 2)) → (∀ a, ‖∑ i, k a i * cf i‖ ≤ 1) → cf ∈ Λ := by
      intro m
      induction m with
      | zero => intro cf hc h1; exact (key cf (by simpa using hc)).2 h1
      | succ m ih =>
        intro cf hc h1
        have h2 : (fun i => π * cf i) ∈ Λ := by
          refine ih _ (fun i => ?_) fun a => ?_
          · rw [norm_mul, hπ, inv_mul_le_iff₀ hq0]
            calc ‖cf i‖ ≤ q ^ (m + 1 + 2) := hc i
              _ = q * q ^ (m + 2) := by ring
          · have : ∑ i, k a i * (π * cf i) = π * ∑ i, k a i * cf i := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
            rw [this, norm_mul, hπ, inv_mul_le_iff₀ hq0]
            exact (h1 a).trans (by linarith)
        refine (key cf fun i => ?_).2 h1
        have h3 := hb' _ h2 i
        rw [norm_mul, hπ, inv_mul_le_iff₀ hq0] at h3
        rwa [sq]
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ‖cf‖ hq
    refine ind m cf fun i => (norm_le_pi_norm cf i).trans (hm.le.trans ?_)
    exact pow_le_pow_right₀ hq.le (by omega)

/- English proof (translation)
Introduce `E _ _ _ H Dw p hp n g h b Λ hn hk hΛ hb cf`. Establish `hnp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹`. Rewrite using `[← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]`. Establish `hq : (1 : ℝ) < p` using `by exact_mod_cast hp.out.one_lt`. Rewrite using `[lattice_membership_stable_under_approximation (p : ℂ_[p]) (p : ℝ) hq hnp n hn h (fun a i => pr Dw (b (Pi.single i 1)) a) Λ hk hΛ hb cf]`.

Use `forall_congr' fun a => ?_` and prove the remaining obligations. Establish `e : pr Dw (b cf) a = ∑ i, pr Dw (b (Pi.single i 1)) a * cf i`. Establish `: cf = ∑ i, cf i • (Pi.single i 1 : Fin g → ℂ_[p])`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Use `conv_lhs => rw [this]`. Simplify using `only [pr, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Rewrite using `[e]`.
-/
theorem UpperTheory.p_adic_lattice_membership_approximated :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (n g : ℕ) (h : Dw.La → Fin g → ℂ_[p]) (b : (Fin g → ℂ_[p]) →ₗ[ℂ_[p]] ℂ_[p] ⊗[ℤ] Dw.La) (Λ : Set (Fin g → ℂ_[p])), 2 ≤ n → (∀ a i, ‖h a i - pr Dw (b (Pi.single i 1)) a‖ ≤ (p : ℝ)⁻¹ ^ n) → (∀ cf, cf ∈ Λ ↔ ∀ a, ‖∑ i, h a i * cf i‖ ≤ 1) → (∀ cf ∈ Λ, ∀ i, ‖(p : ℂ_[p]) * cf i‖ ≤ 1) → ∀ cf, cf ∈ Λ ↔ ∀ a, ‖pr Dw (b cf) a‖ ≤ 1 := by
  intro E _ _ _ H Dw p hp n g h b Λ hn hk hΛ hb cf
  have hnp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]
  have hq : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  rw [lattice_membership_stable_under_approximation (p : ℂ_[p]) (p : ℝ) hq hnp n hn h (fun a i => pr Dw (b (Pi.single i 1)) a) Λ hk hΛ hb cf]
  refine forall_congr' fun a => ?_
  have e : pr Dw (b cf) a = ∑ i, pr Dw (b (Pi.single i 1)) a * cf i := by
    have : cf = ∑ i, cf i • (Pi.single i 1 : Fin g → ℂ_[p]) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [this]
    simp only [pr, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
