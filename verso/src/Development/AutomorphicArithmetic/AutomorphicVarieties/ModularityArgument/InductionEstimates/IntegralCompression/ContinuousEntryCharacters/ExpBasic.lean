import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LongWeylSwapsBlockDiagonal

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

/- English proof (translation)
The claim follows from `Fin.sum_univ_four f`.
-/
private theorem sum_fin_four_expand {M : Type} [AddCommMonoid M] (f : Fin (2 + 2) → M) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 :=
  Fin.sum_univ_four f

/- English proof (translation)
The claim follows from `u4.2.2.2.2.2.2.2.1 θ`.
-/
private theorem eb_dg (θ : Fin (2 + 2) → ℝ) :
    (dg θ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) = diagonal fun i => Complex.exp (Complex.I * θ i) :=
  u4.2.2.2.2.2.2.2.1 θ

/- English proof (translation)
Unfold `chi`. Use `congr 2`. Rewrite using `[Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Simplify using `[Pi.single_eq_of_ne hb]`. Simplify using the standard rewrite rules.
-/
private theorem eb_chi_single (j : Fin (2 + 2)) (θ : Fin (2 + 2) → ℝ) :
    chi (Pi.single j 1) θ = Complex.exp (Complex.I * θ j) := by
  unfold chi
  congr 2
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

/- English proof (translation)
Unfold `chi`. Rewrite using `[← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]`. Use `congr 2`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[add_mul]`.
-/
private theorem eb_chi_add (ν ν' : Fin (2 + 2) → ℤ) (θ : Fin (2 + 2) → ℝ) : chi (ν + ν') θ = chi ν θ * chi ν' θ := by
  unfold chi
  rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [add_mul]

/- English proof (translation)
Unfold `chi`. Rewrite using `[← Complex.exp_conj]`. Use `congr 1`. Simplify using `[map_sum]`.
-/
private theorem eb_chi_neg (ν : Fin (2 + 2) → ℤ) (θ : Fin (2 + 2) → ℝ) : chi (-ν) θ = conj (chi ν θ) := by
  unfold chi
  rw [← Complex.exp_conj]
  congr 1
  simp [map_sum]

/- English proof (translation)
Unfold `en`. Rewrite using `[eb_chi_single, Submonoid.coe_mul, eb_dg, mul_diagonal, mul_comm]`.
-/
private theorem eb_right (i j : Fin (2 + 2)) (θ : Fin (2 + 2) → ℝ) (h : U4) :
    en i j (h * dg θ) = chi (Pi.single j 1) θ * en i j h := by
  unfold en
  rw [eb_chi_single, Submonoid.coe_mul, eb_dg, mul_diagonal, mul_comm]

/- English proof (translation)
Unfold `en`. Rewrite using `[eb_chi_single, Submonoid.coe_mul, eb_dg, diagonal_mul]`.
-/
private theorem eb_left (i j : Fin (2 + 2)) (θ : Fin (2 + 2) → ℝ) (h : U4) :
    en i j (dg θ * h) = chi (Pi.single i 1) θ * en i j h := by
  unfold en
  rw [eb_chi_single, Submonoid.coe_mul, eb_dg, diagonal_mul]

/- English proof (translation)
Unfold `en`. Rewrite using `[Submonoid.coe_mul, Matrix.mul_apply]`. Conclude with `(Equiv.sum_comp π fun s => (h : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) i s * (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) s j).symm`.
-/
private theorem eb_mul (π : Equiv.Perm (Fin (2 + 2))) (i j : Fin (2 + 2)) (h k : U4) :
    en i j (h * k) = ∑ s, en i (π s) h * en (π s) j k := by
  unfold en
  rw [Submonoid.coe_mul, Matrix.mul_apply]
  exact (Equiv.sum_comp π fun s => (h : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) i s * (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) s j).symm

/- English proof (translation)
The claim follows from `(continuous_subtype_val (p := fun x => x ∈ unitaryGroup (Fin (2 + 2)) ℂ)).matrix_elem i j`.
-/
private theorem eb_cont (i j : Fin (2 + 2)) : Continuous (en i j) :=
  (continuous_subtype_val (p := fun x => x ∈ unitaryGroup (Fin (2 + 2)) ℂ)).matrix_elem i j

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`. Simplify using the standard rewrite rules.
-/
private theorem eb_pair (j : Fin (2 + 2)) (f : Fin (2 + 2) → ℤ) : ∑ i, (Pi.single j 1 : Fin (2 + 2) → ℤ) i * f i = f j := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single s]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne (π.injective.ne hb)]`. Simplify using the standard rewrite rules.
-/
private theorem eb_pairπ (π : Equiv.Perm (Fin (2 + 2))) (s : Fin (2 + 2)) (f : Fin (2 + 2) → ℤ) :
    ∑ i, (Pi.single (π s) 1 : Fin (2 + 2) → ℤ) (π i) * f i = f s := by
  rw [Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne (π.injective.ne hb)]
  · simp

/- English proof (translation)
Establish `h0 : ∀ u : Fin (2 + 2), (0 : Fin (2 + 2)) ≤ u` using `by decide`. Establish `h1 : ∀ u : Fin (2 + 2), u ≠ 0 → (1 : Fin (2 + 2)) ≤ u` using `by decide`. Distinguish the cases in `hs : s = 0`. Establish `ht : t ≠ 0` using `fun h => hst (hs.trans h.symm)`. Use `hz (h0 s)` as an intermediate fact.

Use `hz (h1 t ht)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `hz (h0 t)` as an intermediate fact. Use `hz (h1 s hs)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem eb_top (z : Fin (2 + 2) → ℤ) (hz : Antitone z) (s t : Fin (2 + 2)) (hst : s ≠ t) : z s + z t ≤ z 0 + z 1 := by
  have h0 : ∀ u : Fin (2 + 2), (0 : Fin (2 + 2)) ≤ u := by decide
  have h1 : ∀ u : Fin (2 + 2), u ≠ 0 → (1 : Fin (2 + 2)) ≤ u := by decide
  by_cases hs : s = 0
  · have ht : t ≠ 0 := fun h => hst (hs.trans h.symm)
    have := hz (h0 s)
    have := hz (h1 t ht)
    omega
  · have := hz (h0 t)
    have := hz (h1 s hs)
    omega

/- English proof (translation)
Use `⟨Fin (2 + 2), inferInstance, 0, fun s => en (π 0) (π s), fun s => en (π s) (π 0), fun s => Pi.single (π s) 1, fun s => ⟨eb_cont _ _, eb_cont _ _⟩, fun h k => eb_mul π _ _ h k, rfl, rfl, rfl, fun s θ h => ⟨eb_right _ _ _ _, eb_left _ _ _ _, eb_left _ _ _ _⟩, fun s w y hy => ?_, fu …` and prove the remaining obligations. Rewrite using `[eb_pair (π s) fun i => y (w i), eb_pair]`. Establish `h0 : ∀ u : Fin (2 + 2), (0 : Fin (2 + 2)) ≤ u` using `by decide`. Simplify using `using hy (h0 (π.symm (w (π s))))`. Use `beta_reduce`.

Rewrite using `[eb_pairπ π s fun i => -(i : ℤ), eb_pairπ π 0 fun i => -(i : ℤ)]`. Use `revert s`. Evaluate the decidable proposition.
-/
private theorem eb_one (π : Equiv.Perm (Fin (2 + 2))) : OExp π (en (π 0) (π 0)) (Pi.single (π 0) 1) := by
  refine ⟨Fin (2 + 2), inferInstance, 0, fun s => en (π 0) (π s), fun s => en (π s) (π 0), fun s => Pi.single (π s) 1,
    fun s => ⟨eb_cont _ _, eb_cont _ _⟩, fun h k => eb_mul π _ _ h k, rfl, rfl, rfl,
    fun s θ h => ⟨eb_right _ _ _ _, eb_left _ _ _ _, eb_left _ _ _ _⟩, fun s w y hy => ?_, fun s hs => ?_⟩
  · rw [eb_pair (π s) fun i => y (w i), eb_pair]
    have h0 : ∀ u : Fin (2 + 2), (0 : Fin (2 + 2)) ≤ u := by decide
    simpa using hy (h0 (π.symm (w (π s))))
  · beta_reduce
    rw [eb_pairπ π s fun i => -(i : ℤ), eb_pairπ π 0 fun i => -(i : ℤ)]
    revert s
    decide

/- English proof (translation)
Use `⟨Fin (2 + 2), inferInstance, 3, fun s k => conj (en (π 3) (π s) k), fun s k => conj (en (π s) (π 3) k), fun s => -Pi.single (π s) 1, fun s => ⟨Complex.continuous_conj.comp (eb_cont _ _), Complex.continuous_conj.comp (eb_cont _ _)⟩, fun h k => ?_, rfl, rfl, rfl, fun s θ h => ?_, f …` and prove the remaining obligations. Simplify using `only [eb_mul π, map_sum, map_mul]`. Simplify using `only [eb_right, eb_left, eb_chi_neg, map_mul, and_self]`. Simplify using `only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]`. Rewrite using `[eb_pair (π s) fun i => y (w i), eb_pair]`.

Establish `h0 : ∀ u : Fin (2 + 2), u ≤ (3 : Fin (2 + 2))` using `by decide`. Simplify using `using hy (h0 (π.symm (w (π s))))`. Simplify using `only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]`. Rewrite using `[eb_pairπ π s fun i => -(i : ℤ), eb_pairπ π 3 fun i => -(i : ℤ)]`. Use `revert s`.

Evaluate the decidable proposition.
-/
private theorem eb_three (π : Equiv.Perm (Fin (2 + 2))) : OExp π (fun k => conj (en (π 3) (π 3) k)) (-Pi.single (π 3) 1) := by
  refine ⟨Fin (2 + 2), inferInstance, 3, fun s k => conj (en (π 3) (π s) k), fun s k => conj (en (π s) (π 3) k),
    fun s => -Pi.single (π s) 1,
    fun s => ⟨Complex.continuous_conj.comp (eb_cont _ _), Complex.continuous_conj.comp (eb_cont _ _)⟩, fun h k => ?_, rfl, rfl, rfl,
    fun s θ h => ?_, fun s w y hy => ?_, fun s hs => ?_⟩
  · simp only [eb_mul π, map_sum, map_mul]
  · simp only [eb_right, eb_left, eb_chi_neg, map_mul, and_self]
  · simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [eb_pair (π s) fun i => y (w i), eb_pair]
    have h0 : ∀ u : Fin (2 + 2), u ≤ (3 : Fin (2 + 2)) := by decide
    simpa using hy (h0 (π.symm (w (π s))))
  · simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [eb_pairπ π s fun i => -(i : ℤ), eb_pairπ π 3 fun i => -(i : ℤ)]
    revert s
    decide

private def ebS : Fin 6 → Fin (2 + 2) := ![0, 0, 0, 1, 1, 2]

private def ebT : Fin 6 → Fin (2 + 2) := ![1, 2, 3, 2, 3, 3]

/- English proof (translation)
Use `⟨Fin 6, inferInstance, 0, fun p k => en (π 0) (π (ebS p)) k * en (π 1) (π (ebT p)) k - en (π 0) (π (ebT p)) k * en (π 1) (π (ebS p)) k, fun p k => en (π (ebS p)) (π 0) k * en (π (ebT p)) (π 1) k - en (π (ebS p)) (π 1) k * en (π (ebT p)) (π 0) k, fun p => Pi.single (π (ebS p)) 1 + …` and prove the remaining obligations. Simplify using `only [eb_mul π, sum_fin_four_expand, Fin.sum_univ_six, ebS, ebT, Matrix.cons_val]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [eb_right, eb_left, eb_chi_add]`. Apply the tactic sequence `refine ⟨?_, ?_, ?_⟩ <;> ring`.

Simplify using `only [Pi.add_apply, add_mul, Finset.sum_add_distrib]`. Rewrite using `[eb_pair (π (ebS p)) fun i => y (w i), eb_pair (π (ebT p)) fun i => y (w i), eb_pair, eb_pair]`. Establish `hne : ∀ p, ebS p ≠ ebT p` using `by decide`. Simplify using `using eb_top _ hy (π.symm (w (π (ebS p)))) (π.symm (w (π (ebT p)))) (π.symm.injective.ne (w.injective.ne (π.injective.ne (hne p))))`. Simplify using `only [Pi.add_apply, add_mul, Finset.sum_add_distrib]`.

Rewrite using `[eb_pairπ π (ebS p) fun i => -(i : ℤ), eb_pairπ π (ebT p) fun i => -(i : ℤ), eb_pairπ π 0 fun i => -(i : ℤ), eb_pairπ π 1 fun i => -(i : ℤ)]`. Use `revert p`. Evaluate the decidable proposition.
-/
private theorem eb_two (π : Equiv.Perm (Fin (2 + 2))) :
    OExp π (fun k => en (π 0) (π 0) k * en (π 1) (π 1) k - en (π 0) (π 1) k * en (π 1) (π 0) k)
      (Pi.single (π 0) 1 + Pi.single (π 1) 1) := by
  refine ⟨Fin 6, inferInstance, 0,
    fun p k => en (π 0) (π (ebS p)) k * en (π 1) (π (ebT p)) k - en (π 0) (π (ebT p)) k * en (π 1) (π (ebS p)) k,
    fun p k => en (π (ebS p)) (π 0) k * en (π (ebT p)) (π 1) k - en (π (ebS p)) (π 1) k * en (π (ebT p)) (π 0) k,
    fun p => Pi.single (π (ebS p)) 1 + Pi.single (π (ebT p)) 1,
    fun p => ⟨((eb_cont _ _).mul (eb_cont _ _)).sub ((eb_cont _ _).mul (eb_cont _ _)),
      ((eb_cont _ _).mul (eb_cont _ _)).sub ((eb_cont _ _).mul (eb_cont _ _))⟩, fun h k => ?_, rfl, rfl, rfl,
    fun p θ h => ?_, fun p w y hy => ?_, fun p hp => ?_⟩
  · simp only [eb_mul π, sum_fin_four_expand, Fin.sum_univ_six, ebS, ebT, Matrix.cons_val]
    ring
  · simp only [eb_right, eb_left, eb_chi_add]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [eb_pair (π (ebS p)) fun i => y (w i), eb_pair (π (ebT p)) fun i => y (w i), eb_pair, eb_pair]
    have hne : ∀ p, ebS p ≠ ebT p := by decide
    simpa using eb_top _ hy (π.symm (w (π (ebS p)))) (π.symm (w (π (ebT p))))
      (π.symm.injective.ne (w.injective.ne (π.injective.ne (hne p))))
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [eb_pairπ π (ebS p) fun i => -(i : ℤ), eb_pairπ π (ebT p) fun i => -(i : ℤ), eb_pairπ π 0 fun i => -(i : ℤ),
      eb_pairπ π 1 fun i => -(i : ℤ)]
    revert p
    decide

/- English proof (translation)
Unfold `chi`. Rewrite using `[eb_dg, det_diagonal, ← Complex.exp_sum, ← Complex.exp_int_mul, ← Finset.mul_sum, ← Finset.mul_sum]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem eb_det_dg (δ : ℤ) (θ : Fin (2 + 2) → ℝ) :
    (dg θ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ = chi (fun _ => δ) θ := by
  unfold chi
  rw [eb_dg, det_diagonal, ← Complex.exp_sum, ← Complex.exp_int_mul, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  ring

/- English proof (translation)
Establish `hc : Continuous fun k : U4 => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ` using `(continuous_subtype_val (p := fun x => x ∈ unitaryGroup (Fin (2 + 2)) ℂ)).matrix_det.zpow₀ δ fun k => Or.inl (Matrix.UnitaryGroup.det_isUnit k).ne_zero`. Establish `hm : ∀ h k : U4, ((h * k : U4) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ = (h : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ * (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ` using `fun h k => by`. Rewrite using `[Submonoid.coe_mul, det_mul, mul_zpow]`. Use `⟨Unit, inferInstance, (), fun _ k => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ, fun _ k => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ, fun _ _ => δ, fun _ => ⟨hc, hc⟩, fun h k => ?_, rfl, rfl, rfl, fun _ θ h => ?_, fun _ w y _ => ?_, fun _ hs => absurd rfl hs⟩` and prove the remaining obligations. Simplify using `only [hm, Finset.univ_unique, Finset.sum_singleton]`.

Simplify using `only [hm, eb_det_dg, and_self, and_true]`. Conclude with `mul_comm _ _`. Conclude with `(Equiv.sum_comp w fun i => δ * y i).le`.
-/
private theorem eb_four (π : Equiv.Perm (Fin (2 + 2))) (δ : ℤ) :
    OExp π (fun k => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ) fun _ => δ := by
  have hc : Continuous fun k : U4 => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ :=
    (continuous_subtype_val (p := fun x => x ∈ unitaryGroup (Fin (2 + 2)) ℂ)).matrix_det.zpow₀ δ fun k =>
      Or.inl (Matrix.UnitaryGroup.det_isUnit k).ne_zero
  have hm : ∀ h k : U4, ((h * k : U4) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ =
      (h : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ * (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ := fun h k => by
    rw [Submonoid.coe_mul, det_mul, mul_zpow]
  refine ⟨Unit, inferInstance, (), fun _ k => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ,
    fun _ k => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ, fun _ _ => δ, fun _ => ⟨hc, hc⟩, fun h k => ?_, rfl, rfl, rfl,
    fun _ θ h => ?_, fun _ w y _ => ?_, fun _ hs => absurd rfl hs⟩
  · simp only [hm, Finset.univ_unique, Finset.sum_singleton]
  · simp only [hm, eb_det_dg, and_self, and_true]
    exact mul_comm _ _
  · exact (Equiv.sum_comp w fun i => δ * y i).le

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

/- English proof (translation)
Introduce `π`. Conclude with `⟨eb_one π, eb_two π, eb_three π, eb_four π⟩`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.expBasic :
    ∀ π : Equiv.Perm (Fin (2 + 2)), OExp π (en (π 0) (π 0)) (Pi.single (π 0) 1) ∧
      OExp π (fun k => en (π 0) (π 0) k * en (π 1) (π 1) k - en (π 0) (π 1) k * en (π 1) (π 0) k) (Pi.single (π 0) 1 + Pi.single (π 1) 1) ∧
      OExp π (fun k => conj (en (π 3) (π 3) k)) (-Pi.single (π 3) 1) ∧ ∀ δ : ℤ, OExp π (fun k => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ) fun _ => δ := by
  intro π
  exact ⟨eb_one π, eb_two π, eb_three π, eb_four π⟩
