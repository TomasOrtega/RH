import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfF
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.NinLamPf
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdCondition

noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨f, fun i => ((h i).unit⁻¹ : (R i)ˣ), funext fun i => (h i).mul_val_inv, funext fun i => (h i).val_inv_mul⟩, rfl⟩`.
-/
theorem pi_isUnit {ι : Type} {R : ι → Type} [∀ i, Monoid (R i)] (f : ∀ i, R i)
    (h : ∀ i, IsUnit (f i)) : IsUnit f :=
  ⟨⟨f, fun i => ((h i).unit⁻¹ : (R i)ˣ), funext fun i => (h i).mul_val_inv,
    funext fun i => (h i).val_inv_mul⟩, rfl⟩

section Gam

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

/- English proof (translation)
Establish `key : ∀ i, ∃ G : PowerSeries O, (W.γA W.gam (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) i = Formalism.MainNotions.DeltaInvariantLattices.Eat E π' i + (W.γA W.gam π' - π') i * G`. Introduce `i`. Establish `hi : (W.γA W.gam (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) i = Polynomial.aeval ((W.γA W.gam π') i) (E i)` using `by show W.γ₀ W.gam (Polynomial.aeval (π' i) (E i)) = _`. Rewrite using `[← Polynomial.aeval_algHom_apply]`. Both sides reduce to the same expression.

Take `⟨G, hG⟩` from `Polynomial.sub_dvd_eval_sub ((W.γA W.gam π') i) (π' i) ((E i).map (algebraMap O (PowerSeries O)))`. Use `⟨G, ?_⟩` and prove the remaining obligations. Rewrite using `[hi, Polynomial.aeval_def, ← Polynomial.eval_map, Pi.sub_apply, ← hG]`. Use `show _ = Polynomial.aeval (π' i) (E i) + _`. Rewrite using `[Polynomial.aeval_def, ← Polynomial.eval_map]`.

Expand and normalize the polynomial expressions, which then agree. Use `choose G hG using key`. Use `⟨1 + (w2 : LetA O n) * π' * G, ?_, ?_⟩` and prove the remaining obligations. Use `pi_isUnit _ fun i => ?_` and prove the remaining obligations. Rewrite using `[PowerSeries.isUnit_iff_constantCoeff]`.

Establish `h0 : PowerSeries.constantCoeff (π' i) = 0`. Rewrite using `[hw0]`. Use `show PowerSeries.constantCoeff ((w0 : LetA O n) i * PowerSeries.X ^ s') = 0`. Rewrite using `[map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]`. Use `show IsUnit (PowerSeries.constantCoeff (1 + (w2 : LetA O n) i * π' i * G i))`.

Rewrite using `[map_add, map_one, map_mul, map_mul, h0, mul_zero, zero_mul, add_zero]`. Conclude with `isUnit_one`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.mul_apply, hG i, hw2]`. Simplify using `only [Pi.add_apply, Pi.mul_apply, Pi.one_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem gam_unit (π' : LetA O n) (E : ZMod n → Polynomial O) {s' : ℕ} (hs' : 1 ≤ s')
    (w2 : (LetA O n)ˣ) (hw2 : W.γA W.gam π' - π' = (w2 : LetA O n) * π' * Formalism.MainNotions.DeltaInvariantLattices.Eat E π')
    (w0 : (LetA O n)ˣ) (hw0 : π' = (w0 : LetA O n) * letπ ^ s') :
    ∃ u : LetA O n, IsUnit u ∧ W.γA W.gam (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') = u * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' := by
  have key : ∀ i, ∃ G : PowerSeries O, (W.γA W.gam (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) i =
      Formalism.MainNotions.DeltaInvariantLattices.Eat E π' i + (W.γA W.gam π' - π') i * G := by
    intro i
    have hi : (W.γA W.gam (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) i =
        Polynomial.aeval ((W.γA W.gam π') i) (E i) := by
      show W.γ₀ W.gam (Polynomial.aeval (π' i) (E i)) = _
      rw [← Polynomial.aeval_algHom_apply]
      rfl
    obtain ⟨G, hG⟩ := Polynomial.sub_dvd_eval_sub ((W.γA W.gam π') i) (π' i)
      ((E i).map (algebraMap O (PowerSeries O)))
    refine ⟨G, ?_⟩
    rw [hi, Polynomial.aeval_def, ← Polynomial.eval_map, Pi.sub_apply, ← hG]
    show _ = Polynomial.aeval (π' i) (E i) + _
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    ring
  choose G hG using key
  refine ⟨1 + (w2 : LetA O n) * π' * G, ?_, ?_⟩
  · refine pi_isUnit _ fun i => ?_
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have h0 : PowerSeries.constantCoeff (π' i) = 0 := by
      rw [hw0]
      show PowerSeries.constantCoeff ((w0 : LetA O n) i * PowerSeries.X ^ s') = 0
      rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]
    show IsUnit (PowerSeries.constantCoeff (1 + (w2 : LetA O n) i * π' i * G i))
    rw [map_add, map_one, map_mul, map_mul, h0, mul_zero, zero_mul, add_zero]
    exact isUnit_one
  · funext i
    rw [Pi.mul_apply, hG i, hw2]
    simp only [Pi.add_apply, Pi.mul_apply, Pi.one_apply]
    ring

/- English proof (translation)
Introduce `δ hδ`. Establish `h1 : W.γA δ (u * Eπ) = u * Eπ` using `by rw [← hu, γA_comm, hEΔ δ hδ]`. Rewrite `h1` using `[map_mul, hEΔ δ hδ]`. Conclude with `sub_eq_zero.1 (hnz _ (by rw [sub_mul, h1, sub_self]))`.
-/
theorem u_mem_AΔ {Eπ u : LetA O n} (hEΔ : Eπ ∈ W.AΔ) (hnz : ∀ a : LetA O n, a * Eπ = 0 → a = 0)
    (hu : W.γA W.gam Eπ = u * Eπ) : u ∈ W.AΔ := by
  intro δ hδ
  have h1 : W.γA δ (u * Eπ) = u * Eπ := by rw [← hu, γA_comm, hEΔ δ hδ]
  rw [map_mul, hEΔ δ hδ] at h1
  exact sub_eq_zero.1 (hnz _ (by rw [sub_mul, h1, sub_self]))

/- English proof (translation)
Introduce `δ hδ`. Establish `h2 : W.γA δ u' * u = 1` using `by rw [← hu δ hδ, ← map_mul, huu, map_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem inv_mem_AΔ {u u' : LetA O n} (hu : u ∈ W.AΔ) (huu : u' * u = 1) : u' ∈ W.AΔ := by
  intro δ hδ
  have h2 : W.γA δ u' * u = 1 := by rw [← hu δ hδ, ← map_mul, huu, map_one]
  calc W.γA δ u' = W.γA δ u' * (u * u') := by rw [mul_comm u u', huu, mul_one]
    _ = (W.γA δ u' * u) * u' := by ring
    _ = u' := by rw [h2, one_mul]

/- English proof (translation)
Introduce `h`. Establish `h1` using `W.q₀_def`. Rewrite `h1` using `[h, mul_zero]`. Establish `h2` using `congrArg (PowerSeries.coeff 1) h1`. Establish `e : (1 + PowerSeries.X : PowerSeries O) ^ PD.p = (((Polynomial.X + 1) ^ PD.p : Polynomial O) : PowerSeries O)`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[map_zero, map_sub, e, Polynomial.coeff_coe, Polynomial.coeff_X_add_one_pow, Nat.choose_one_right, PowerSeries.coeff_one, if_neg one_ne_zero, sub_zero]`. Conclude with `hp h2.symm`.
-/
theorem q0_ne_two_and_ne_q_and_ne_d (hp : ((PD.p : ℕ) : O) ≠ 0) : W.q₀ ≠ 0 := by
  intro h
  have h1 := W.q₀_def
  rw [h, mul_zero] at h1
  have h2 := congrArg (PowerSeries.coeff 1) h1
  have e : (1 + PowerSeries.X : PowerSeries O) ^ PD.p =
      (((Polynomial.X + 1) ^ PD.p : Polynomial O) : PowerSeries O) := by
    push_cast
    ring
  rw [map_zero, map_sub, e, Polynomial.coeff_coe, Polynomial.coeff_X_add_one_pow,
    Nat.choose_one_right, PowerSeries.coeff_one, if_neg one_ne_zero, sub_zero] at h2
  exact hp h2.symm

/- English proof (translation)
Introduce `a ha`. Use function extensionality and compare the values at `i`. Establish `h` using `congrFun ha i`. Establish `hE : Eπ i ≠ 0` using `fun h0 => by`. Use `congrFun hQ i` as an intermediate fact.

Express the relevant statement in the definitionally equal form `W.q₀ = w i * Eπ i at this`. Rewrite `this` using `[h0, mul_zero]`. Conclude with `hq0 this`. Conclude with `(mul_eq_zero.1 h).resolve_right hE`.
-/
theorem Eπ_nzd [IsDomain O] {Eπ : LetA O n} {w : LetA O n} (hQ : W.q = w * Eπ) (hq0 : W.q₀ ≠ 0) :
    ∀ a : LetA O n, a * Eπ = 0 → a = 0 := by
  intro a ha
  funext i
  have h := congrFun ha i
  have hE : Eπ i ≠ 0 := fun h0 => by
    have := congrFun hQ i
    change W.q₀ = w i * Eπ i at this
    rw [h0, mul_zero] at this
    exact hq0 this
  exact (mul_eq_zero.1 h).resolve_right hE

end Gam

end Formalism.MainNotions.N.Ln34.ModelFPf

end
