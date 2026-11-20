import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.DegeneratingToriPeriodMapEqBaseOfYEqZero
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff

noncomputable section
namespace GlobalTheory.ArcPts.WeightZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

def chr (x : A.X) : Multiplicative (A.X →+ ℂ) →* ℂ where
  toFun l := eTwoPi (l.toAdd x)
  map_one' := AnArc.e_zero
  map_mul' l l' := AnArc.e_add _ _

/- English proof (translation)
Introduce `x y hxy`. Assume the negation of the conclusion as `hne`. Establish `hd : x - y ≠ 0` using `sub_ne_zero.mpr hne`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, (Module.Free.chooseBasis ℤ A.X).repr (x - y) i ≠ 0 := by`. Assume the negation of the conclusion as `hall`.

Simplify using `only [not_exists, not_not] at hall`. Apply `hd` to reduce the goal to its premises. Apply `(Module.Free.chooseBasis ℤ A.X).repr.map_eq_zero_iff.mp` to reduce the goal to its premises. Use extensionality with `j`. Simplify using `using hall j`.

Set `k : ℤ` to `(Module.Free.chooseBasis ℤ A.X).repr (x - y) i`. Set `g : A.X →+ ℂ` to `(Int.castAddHom ℂ).comp ((Module.Free.chooseBasis ℤ A.X).coord i).toAddMonoidHom`. Establish `hg : g (x - y) = k` using `by simp [g, k]`. Establish `hk : (k : ℂ) ≠ 0` using `Int.cast_ne_zero.mpr hi`. Set `l : A.X →+ ℂ` to `(2 * (k : ℂ))⁻¹ • g`.

Establish `hl : l (x - y) = 1 / 2`. Simplify using `only [l, AddMonoidHom.smul_apply, hg, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Establish `h1 : eTwoPi (l x) = eTwoPi (l y)` using `congrArg (fun χ => χ (Multiplicative.ofAdd l)) hxy`. Establish `h2 : eTwoPi (l x) = eTwoPi (l (x - y)) * eTwoPi (l y)`.

Rewrite using `[← AnArc.e_add, map_sub, sub_add_cancel]`. Rewrite `h2` using `[hl, h1]`. Establish `h3 : eTwoPi (1 / 2) = 1` using `mul_right_cancel₀ (AnArc.e_ne_zero (l y)) (h2.symm.trans (one_mul _).symm)`. Establish `h4 : eTwoPi (1 / 2) = -1`. Simplify using `only [eTwoPi]`.

Rewrite using `[show 2 * (Real.pi : ℂ) * Complex.I * (1 / 2) = Real.pi * Complex.I by ring, Complex.exp_pi_mul_I]`. Rewrite `h3` using `[h4]`. Evaluate the numerical expressions using `at h3`.
-/
theorem chr_injective : Function.Injective (chr A) := by
  intro x y hxy
  by_contra hne
  have hd : x - y ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨i, hi⟩ : ∃ i, (Module.Free.chooseBasis ℤ A.X).repr (x - y) i ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hd
    apply (Module.Free.chooseBasis ℤ A.X).repr.map_eq_zero_iff.mp
    ext j
    simpa using hall j
  let k : ℤ := (Module.Free.chooseBasis ℤ A.X).repr (x - y) i
  let g : A.X →+ ℂ := (Int.castAddHom ℂ).comp ((Module.Free.chooseBasis ℤ A.X).coord i).toAddMonoidHom
  have hg : g (x - y) = k := by simp [g, k]
  have hk : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hi
  let l : A.X →+ ℂ := (2 * (k : ℂ))⁻¹ • g
  have hl : l (x - y) = 1 / 2 := by
    simp only [l, AddMonoidHom.smul_apply, hg, smul_eq_mul]
    field_simp
  have h1 : eTwoPi (l x) = eTwoPi (l y) := congrArg (fun χ => χ (Multiplicative.ofAdd l)) hxy
  have h2 : eTwoPi (l x) = eTwoPi (l (x - y)) * eTwoPi (l y) := by
    rw [← AnArc.e_add, map_sub, sub_add_cancel]
  rw [hl, h1] at h2
  have h3 : eTwoPi (1 / 2) = 1 :=
    mul_right_cancel₀ (AnArc.e_ne_zero (l y)) (h2.symm.trans (one_mul _).symm)
  have h4 : eTwoPi (1 / 2) = -1 := by
    simp only [eTwoPi]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 / 2) = Real.pi * Complex.I by ring, Complex.exp_pi_mul_I]
  rw [h4] at h3
  norm_num at h3

/- English proof (translation)
Establish `hli : LinearIndependent ℂ (fun x : A.X => ((chr A x : Multiplicative (A.X →+ ℂ) →* ℂ) : Multiplicative (A.X →+ ℂ) → ℂ))` using `(linearIndependent_monoidHom (Multiplicative (A.X →+ ℂ)) ℂ).comp (chr A) (chr_injective A)`. Set `g : A.X → ℂ` to `fun x => (if x ∈ F then b x else 0) - (if x ∈ G then c x else 0)`. Establish `hsum : ∑ x ∈ F ∪ G, g x • ((chr A x : Multiplicative (A.X →+ ℂ) →* ℂ) : Multiplicative (A.X →+ ℂ) → ℂ) = 0`. Use function extensionality and compare the values at `m`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, g, sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.union_inter_cancel_left, Finset.union_inter_cancel_right]`.

Conclude with `sub_eq_zero.mpr (h (Multiplicative.toAdd m))`. Establish `h0` using `linearIndependent_iff'.mp hli (F ∪ G) g hsum 0 (Finset.mem_union_left _ hF)`. Simplify `h0` using `[g, hF, hG, sub_eq_zero]`.
-/
theorem coeff_zero_eq {F G : Finset A.X} {b c : A.X → ℂ} (hF : 0 ∈ F) (hG : 0 ∈ G)
    (h : ∀ l : A.X →+ ℂ, ∑ x ∈ F, b x * eTwoPi (l x) = ∑ x ∈ G, c x * eTwoPi (l x)) : b 0 = c 0 := by
  classical
  have hli : LinearIndependent ℂ (fun x : A.X =>
      ((chr A x : Multiplicative (A.X →+ ℂ) →* ℂ) : Multiplicative (A.X →+ ℂ) → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative (A.X →+ ℂ)) ℂ).comp (chr A) (chr_injective A)
  let g : A.X → ℂ := fun x => (if x ∈ F then b x else 0) - (if x ∈ G then c x else 0)
  have hsum : ∑ x ∈ F ∪ G, g x • ((chr A x : Multiplicative (A.X →+ ℂ) →* ℂ) :
      Multiplicative (A.X →+ ℂ) → ℂ) = 0 := by
    funext m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, g, sub_mul, ite_mul, zero_mul,
      Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.union_inter_cancel_left,
      Finset.union_inter_cancel_right]
    exact sub_eq_zero.mpr (h (Multiplicative.toAdd m))
  have h0 := linearIndependent_iff'.mp hli (F ∪ G) g hsum 0 (Finset.mem_union_left _ hF)
  simpa [g, hF, hG, sub_eq_zero] using h0

/- English proof (translation)
Rewrite using `[AnArc.exponent, AnArc.q_add, A.be_symm μ α]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exponent_one (α μ : A.X) : A.exponent 1 α μ = A.q (α + μ) - A.q α := by
  rw [AnArc.exponent, AnArc.q_add, A.be_symm μ α]
  push_cast
  ring

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[HahnSeries.coeff_single_mul, AnArc.coeff_FSum, AnArc.coeff_FSum, Finset.mul_sum, sub_neg_eq_add]`. Use `Finset.sum_nbij' (fun μ => α + μ) (fun ν => ν - α) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `μ hμ`. Simplify using `only [AnArc.mem_level, exponent_one A, zero_add, AnArc.q_zero, sub_zero] at hμ ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `ν hν`. Simplify using `only [AnArc.mem_level, exponent_one A, zero_add, AnArc.q_zero, sub_zero] at hν ⊢`. Rewrite using `[show α + (ν - α) = ν by abel]`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `μ _`. Simplify using the standard rewrite rules. Introduce `ν _`. Simplify using the standard rewrite rules. Introduce `μ _`.

Establish `hu : (A.psi α : ℂ) ≠ 0` using `(A.psi α).ne_zero`. Establish `hc : v.2 + A.ct (α + μ) - A.ct α = v.2 + A.ct μ` using `by rw [map_add]; abel`. Simplify using `only [AnArc.term, pow_one, one_smul, zero_add, map_zero, AnArc.e_zero, A.psi_add, A.T_symm α μ, hc]`. Rewrite using `[eq_inv_mul_iff_mul_eq₀ hu]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem FSum_shift (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (v : A.V) :
    A.FSum 1 α th v = HahnSeries.single (-A.q α) ((A.psi α : ℂ)⁻¹) * A.FSum 1 0 (fun z => th (z - A.ct α)) v := by
  ext n
  rw [HahnSeries.coeff_single_mul, AnArc.coeff_FSum, AnArc.coeff_FSum, Finset.mul_sum, sub_neg_eq_add]
  refine Finset.sum_nbij' (fun μ => α + μ) (fun ν => ν - α) ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    simp only [AnArc.mem_level, exponent_one A, zero_add, AnArc.q_zero, sub_zero] at hμ ⊢
    linarith
  · intro ν hν
    simp only [AnArc.mem_level, exponent_one A, zero_add, AnArc.q_zero, sub_zero] at hν ⊢
    rw [show α + (ν - α) = ν by abel]
    linarith
  · intro μ _
    simp
  · intro ν _
    simp
  · intro μ _
    have hu : (A.psi α : ℂ) ≠ 0 := (A.psi α).ne_zero
    have hc : v.2 + A.ct (α + μ) - A.ct α = v.2 + A.ct μ := by rw [map_add]; abel
    simp only [AnArc.term, pow_one, one_smul, zero_add, map_zero, AnArc.e_zero, A.psi_add,
      A.T_symm α μ, hc]
    rw [eq_inv_mul_iff_mul_eq₀ hu]
    ring

/- English proof (translation)
Use `⟨(A.finite_be_le (2 * (n - r.order))).toFinset, fun G hG th v => ?_⟩` and prove the remaining obligations. Establish `hq : ∀ μ, A.exponent 1 0 μ = A.q μ` using `fun μ => by`. Rewrite using `[exponent_one A, zero_add, AnArc.q_zero, sub_zero]`. Establish `hq0 : ∀ μ, 0 ≤ A.q μ` using `fun μ => by`. Establish `h1` using `A.two_mul_q μ`.

Establish `h2` using `A.be_self_nonneg μ`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpwo : (Set.Ici (0 : ℤ)).IsPWO` using `bddBelow_Ici.isWF.isPWO`. Establish `hsupp : (A.FSum 1 0 th v).support ⊆ Set.Ici 0`. Introduce `k hk`.

Rewrite using `[Set.mem_Ici]`. Assume the negation of the conclusion as `hlt`. Conclude with `hk (A.coeff_FSum_eq_zero 1 0 th v (by simpa using not_le.mp hlt))`. Rewrite using `[HahnSeries.coeff_mul_right' hpwo hsupp]`. Simplify using `only [AnArc.coeff_FSum, Finset.mul_sum]`.

Rewrite using `[Finset.sum_sigma']`. Use `Finset.sum_bij_ne_zero (fun a _ _ => a.2) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨⟨i, k⟩, μ⟩ h₁ h₂`. Rewrite `h₁` using `[Finset.mem_sigma, Finset.mem_antidiagonal, AnArc.mem_level, hq]`. Take `⟨⟨-, -, hik⟩, hμ⟩` from `h₁`.

Establish `ho` using `HahnSeries.order_le_of_coeff_ne_zero (left_ne_zero_of_mul h₂)`. Apply `hG` to reduce the goal to its premises. Rewrite using `[Set.Finite.mem_toFinset, Set.mem_ofPred_eq, ← A.two_mul_q]`. Simplify using `only at hμ hik ho ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce and unpack `⟨⟨i, k⟩, μ⟩ h₁ _ ⟨⟨i', k'⟩, μ'⟩ h₁' _ heq`. Simplify using `only at heq`. Substitute `heq` using the available equality. Rewrite `h₁`, `h₁'` using `[Finset.mem_sigma, Finset.mem_antidiagonal, AnArc.mem_level, hq]`. Take `⟨⟨-, -, hik⟩, hμ⟩` from `h₁`.

Take `⟨⟨-, -, hik'⟩, hμ'⟩` from `h₁'`. Simplify using `only at hik hμ hik' hμ'`. Establish `hk : k = k'` using `by rw [← hμ, ← hμ']`. Substitute `hk` using the available equality. Establish `hi : i = i'` using `by omega`.

Substitute `hi` using the available equality. Both sides reduce to the same expression. Introduce `μ _ hne`. Use `⟨⟨(n - A.q μ, A.q μ), μ⟩, ?_, hne, rfl⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_sigma, Finset.mem_antidiagonal, AnArc.mem_level, hq]`.

Conclude with `⟨⟨(HahnSeries.mem_support _ _).mpr (left_ne_zero_of_mul hne), Set.mem_Ici.mpr (hq0 μ), by simp⟩, rfl⟩`. Introduce and unpack `⟨⟨i, k⟩, μ⟩ h₁ _`. Rewrite `h₁` using `[Finset.mem_sigma, Finset.mem_antidiagonal, AnArc.mem_level, hq]`. Take `⟨⟨-, -, hik⟩, hμ⟩` from `h₁`. Simplify using `only at hik hμ ⊢`.

Rewrite using `[show i = n - A.q μ by omega]`.
-/
theorem coeff_mul_FSum (r : ℂ⸨X⸩) (n : ℤ) : ∃ G₀ : Finset A.X, ∀ G, G₀ ⊆ G → ∀ (th : (Fin A.gB → ℂ) → ℂ) (v : A.V),
    (r * A.FSum 1 0 th v).coeff n = ∑ μ ∈ G, r.coeff (n - A.q μ) * A.term 1 0 th μ v := by
  classical
  refine ⟨(A.finite_be_le (2 * (n - r.order))).toFinset, fun G hG th v => ?_⟩
  have hq : ∀ μ, A.exponent 1 0 μ = A.q μ := fun μ => by
    rw [exponent_one A, zero_add, AnArc.q_zero, sub_zero]
  have hq0 : ∀ μ, 0 ≤ A.q μ := fun μ => by
    have h1 := A.two_mul_q μ
    have h2 := A.be_self_nonneg μ
    linarith
  have hpwo : (Set.Ici (0 : ℤ)).IsPWO := bddBelow_Ici.isWF.isPWO
  have hsupp : (A.FSum 1 0 th v).support ⊆ Set.Ici 0 := by
    intro k hk
    rw [Set.mem_Ici]
    by_contra hlt
    exact hk (A.coeff_FSum_eq_zero 1 0 th v (by simpa using not_le.mp hlt))
  rw [HahnSeries.coeff_mul_right' hpwo hsupp]
  simp only [AnArc.coeff_FSum, Finset.mul_sum]
  rw [Finset.sum_sigma']
  refine Finset.sum_bij_ne_zero (fun a _ _ => a.2) ?_ ?_ ?_ ?_
  · rintro ⟨⟨i, k⟩, μ⟩ h₁ h₂
    rw [Finset.mem_sigma, Finset.mem_antidiagonal, AnArc.mem_level, hq] at h₁
    obtain ⟨⟨-, -, hik⟩, hμ⟩ := h₁
    have ho := HahnSeries.order_le_of_coeff_ne_zero (left_ne_zero_of_mul h₂)
    apply hG
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, ← A.two_mul_q]
    simp only at hμ hik ho ⊢
    linarith
  · rintro ⟨⟨i, k⟩, μ⟩ h₁ _ ⟨⟨i', k'⟩, μ'⟩ h₁' _ heq
    simp only at heq
    subst heq
    rw [Finset.mem_sigma, Finset.mem_antidiagonal, AnArc.mem_level, hq] at h₁ h₁'
    obtain ⟨⟨-, -, hik⟩, hμ⟩ := h₁
    obtain ⟨⟨-, -, hik'⟩, hμ'⟩ := h₁'
    simp only at hik hμ hik' hμ'
    have hk : k = k' := by rw [← hμ, ← hμ']
    subst hk
    have hi : i = i' := by omega
    subst hi
    rfl
  · intro μ _ hne
    refine ⟨⟨(n - A.q μ, A.q μ), μ⟩, ?_, hne, rfl⟩
    rw [Finset.mem_sigma, Finset.mem_antidiagonal, AnArc.mem_level, hq]
    exact ⟨⟨(HahnSeries.mem_support _ _).mpr (left_ne_zero_of_mul hne), Set.mem_Ici.mpr (hq0 μ), by simp⟩, rfl⟩
  · rintro ⟨⟨i, k⟩, μ⟩ h₁ _
    rw [Finset.mem_sigma, Finset.mem_antidiagonal, AnArc.mem_level, hq] at h₁
    obtain ⟨⟨-, -, hik⟩, hμ⟩ := h₁
    simp only at hik hμ ⊢
    rw [show i = n - A.q μ by omega]

/- English proof (translation)
Take `⟨m, r, α, th, -, hfe⟩` from `hf`. Take `⟨s, ph, hfe'⟩ : ∃ (s : Fin m → ℂ⸨X⸩) (ph : Fin m → (Fin A.gB → ℂ) → ℂ), ∀ w, f w = ∑ i, s i * A.FSum 1 0 (ph i) w` from `⟨fun i => r i * HahnSeries.single (-A.q (α i)) ((A.psi (α i) : ℂ)⁻¹), fun i z => th i (z - A.ct (α i)), fun w => by`. Rewrite using `[hfe w]`. Conclude with `Finset.sum_congr rfl fun i _ => by simp only [FSum_shift A (α i) (th i) w, mul_assoc]⟩`. Establish `hq : ∀ μ, A.exponent 1 0 μ = A.q μ` using `fun μ => by`.

Rewrite using `[exponent_one A, zero_add, AnArc.q_zero, sub_zero]`. Establish `hexp : ∀ n : ℤ, ∃ G : Finset A.X, 0 ∈ G ∧ A.level 1 0 n ⊆ G ∧ ∀ w : A.V, (f w).coeff n = ∑ μ ∈ G, ∑ i, (s i).coeff (n - A.q μ) * A.term 1 0 (ph i) μ w`. Introduce `n`. Use `choose G₀ hG₀ using fun i => coeff_mul_FSum A (s i) n`. Establish `hsub : ∀ i, G₀ i ⊆ insert 0 (A.level 1 0 n ∪ Finset.univ.biUnion G₀)` using `fun i => (Finset.subset_biUnion_of_mem G₀ (Finset.mem_univ i)).trans (Finset.subset_union_right.trans (Finset.subset_insert _ _))`.

Use `⟨insert 0 (A.level 1 0 n ∪ Finset.univ.biUnion G₀), Finset.mem_insert_self _ _, fun μ hμ => Finset.mem_insert_of_mem (Finset.mem_union_left _ hμ), fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[hfe' w, HahnSeries.coeff_sum, Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => hG₀ i _ (hsub i) (ph i) w`. Establish `hkey : ∀ (z : Fin A.gB → ℂ) (n : ℤ), ∑ i, (s i).coeff n * ph i z = if n = 0 then θ z else 0`. Introduce `z n`.

Take `⟨G, hG0, -, hG⟩` from `hexp n`. Take `⟨F, b, hF0, hb0, hFb⟩` from `h z n`. Establish `hc` using `coeff_zero_eq A (F := F) (G := G) (b := b) (c := fun μ => (A.psi μ : ℂ) * ∑ i, (s i).coeff (n - A.q μ) * ph i (z + A.ct μ)) hF0 hG0 (fun l => by`. Rewrite using `[← hFb l, hG (l, z)]`. Use `Finset.sum_congr rfl fun μ _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [AnArc.term, pow_one, one_smul, zero_add, map_zero, AnArc.e_zero]`. Use the proof step `ring)`. Rewrite using `[← hb0, hc]`.

Simplify using the standard rewrite rules. Use extensionality with `n`. Take `⟨G, -, hlev, hG⟩` from `hexp n`. Establish `hK : ∀ (μ : A.X) (g : (Fin A.gB → ℂ) → ℂ), A.term 1 0 g μ v = A.term 1 0 (fun _ => 1) μ v * g (v.2 + A.ct μ)`. Introduce `μ g`.

Simplify using `only [AnArc.term, mul_one]`. Establish `hterm : ∀ μ, ∑ i, (s i).coeff (n - A.q μ) * A.term 1 0 (ph i) μ v = if A.q μ = n then A.term 1 0 θ μ v else 0`. Introduce `μ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun i _ => by rw [hK μ (ph i)]; ring`. Use `_ = if A.q μ = n then A.term 1 0 θ μ v else 0 := by`. Rewrite using `[hkey, hK μ θ]`. Distinguish the cases in `hμ : A.q μ = n`. Rewrite using `[if_pos (by omega), if_pos hμ]`.

Rewrite using `[if_neg (by omega), if_neg hμ, mul_zero]`. Rewrite using `[hG v, AnArc.coeff_FSum]`. Simplify using `only [hterm]`. Rewrite using `[← Finset.sum_filter]`. Use `congr 1`.

Use extensionality with `μ`. Simplify using `only [Finset.mem_filter, AnArc.mem_level, hq]`. Conclude with `⟨fun hμ => hμ.2, fun hμ => ⟨hlev (by rw [AnArc.mem_level, hq]; exact hμ), hμ⟩⟩`.
-/
theorem eq_FSum {f : A.V → ℂ⸨X⸩} (hf : ArcPts.IsComb A 1 Set.univ f) (θ : (Fin A.gB → ℂ) → ℂ)
    (h : ∀ (z : Fin A.gB → ℂ) (n : ℤ), ∃ (F : Finset A.X) (b : A.X → ℂ), 0 ∈ F ∧ b 0 = (if n = 0 then θ z else 0) ∧
      ∀ l : A.X →+ ℂ, (f (l, z)).coeff n = ∑ x ∈ F, b x * eTwoPi (l x)) (v : A.V) : f v = A.FSum 1 0 θ v := by
  classical
  obtain ⟨m, r, α, th, -, hfe⟩ := hf
  obtain ⟨s, ph, hfe'⟩ : ∃ (s : Fin m → ℂ⸨X⸩) (ph : Fin m → (Fin A.gB → ℂ) → ℂ),
      ∀ w, f w = ∑ i, s i * A.FSum 1 0 (ph i) w :=
    ⟨fun i => r i * HahnSeries.single (-A.q (α i)) ((A.psi (α i) : ℂ)⁻¹), fun i z => th i (z - A.ct (α i)),
      fun w => by
        rw [hfe w]
        exact Finset.sum_congr rfl fun i _ => by simp only [FSum_shift A (α i) (th i) w, mul_assoc]⟩
  have hq : ∀ μ, A.exponent 1 0 μ = A.q μ := fun μ => by
    rw [exponent_one A, zero_add, AnArc.q_zero, sub_zero]
  have hexp : ∀ n : ℤ, ∃ G : Finset A.X, 0 ∈ G ∧ A.level 1 0 n ⊆ G ∧ ∀ w : A.V,
      (f w).coeff n = ∑ μ ∈ G, ∑ i, (s i).coeff (n - A.q μ) * A.term 1 0 (ph i) μ w := by
    intro n
    choose G₀ hG₀ using fun i => coeff_mul_FSum A (s i) n
    have hsub : ∀ i, G₀ i ⊆ insert 0 (A.level 1 0 n ∪ Finset.univ.biUnion G₀) := fun i =>
      (Finset.subset_biUnion_of_mem G₀ (Finset.mem_univ i)).trans
        (Finset.subset_union_right.trans (Finset.subset_insert _ _))
    refine ⟨insert 0 (A.level 1 0 n ∪ Finset.univ.biUnion G₀), Finset.mem_insert_self _ _,
      fun μ hμ => Finset.mem_insert_of_mem (Finset.mem_union_left _ hμ), fun w => ?_⟩
    rw [hfe' w, HahnSeries.coeff_sum, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => hG₀ i _ (hsub i) (ph i) w
  have hkey : ∀ (z : Fin A.gB → ℂ) (n : ℤ), ∑ i, (s i).coeff n * ph i z = if n = 0 then θ z else 0 := by
    intro z n
    obtain ⟨G, hG0, -, hG⟩ := hexp n
    obtain ⟨F, b, hF0, hb0, hFb⟩ := h z n
    have hc := coeff_zero_eq A (F := F) (G := G) (b := b)
      (c := fun μ => (A.psi μ : ℂ) * ∑ i, (s i).coeff (n - A.q μ) * ph i (z + A.ct μ)) hF0 hG0 (fun l => by
        rw [← hFb l, hG (l, z)]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [AnArc.term, pow_one, one_smul, zero_add, map_zero, AnArc.e_zero]
        ring)
    rw [← hb0, hc]
    simp
  ext n
  obtain ⟨G, -, hlev, hG⟩ := hexp n
  have hK : ∀ (μ : A.X) (g : (Fin A.gB → ℂ) → ℂ),
      A.term 1 0 g μ v = A.term 1 0 (fun _ => 1) μ v * g (v.2 + A.ct μ) := by
    intro μ g
    simp only [AnArc.term, mul_one]
  have hterm : ∀ μ, ∑ i, (s i).coeff (n - A.q μ) * A.term 1 0 (ph i) μ v =
      if A.q μ = n then A.term 1 0 θ μ v else 0 := by
    intro μ
    calc ∑ i, (s i).coeff (n - A.q μ) * A.term 1 0 (ph i) μ v
        = A.term 1 0 (fun _ => 1) μ v * ∑ i, (s i).coeff (n - A.q μ) * ph i (v.2 + A.ct μ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [hK μ (ph i)]; ring
      _ = if A.q μ = n then A.term 1 0 θ μ v else 0 := by
          rw [hkey, hK μ θ]
          by_cases hμ : A.q μ = n
          · rw [if_pos (by omega), if_pos hμ]
          · rw [if_neg (by omega), if_neg hμ, mul_zero]
  rw [hG v, AnArc.coeff_FSum]
  simp only [hterm]
  rw [← Finset.sum_filter]
  congr 1
  ext μ
  simp only [Finset.mem_filter, AnArc.mem_level, hq]
  exact ⟨fun hμ => hμ.2, fun hμ => ⟨hlev (by rw [AnArc.mem_level, hq]; exact hμ), hμ⟩⟩

end GlobalTheory.ArcPts.WeightZero
