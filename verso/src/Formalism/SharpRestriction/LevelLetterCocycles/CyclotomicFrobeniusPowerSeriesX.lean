import Formalism.SharpRestriction.LevelLetterCocycles.RingStepsOf
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ExpRescaleCoeff

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

/- English proof (translation)
Rewrite using `[W.φ₀_X, W.q₀_def]`.
-/
theorem cyclotomicFrobeniusPowerSeries_X (W : LocWach PD LL O v n) : W.φ₀ X = (1 + X) ^ PD.p - 1 := by
  rw [W.φ₀_X, W.q₀_def]

/- English proof (translation)
Take `⟨w, hw⟩` from `hR.2.2.1`. Use `⟨Units.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) 0) w, ?_⟩` and prove the remaining obligations. Establish `h0` using `congrFun hw 0`. Rewrite using `[(baseIdOf hR).ι_X]`. Simplify `h0` using `[LocWach.π₀, letπ]`.
-/
theorem glue1 (hR : Ring9 W) :
    ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι X = (w : PowerSeries O) * X ^ (PD.p - 1) := by
  obtain ⟨w, hw⟩ := hR.2.2.1
  refine ⟨Units.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) 0) w, ?_⟩
  have h0 := congrFun hw 0
  rw [(baseIdOf hR).ι_X]
  simpa [LocWach.π₀, letπ] using h0

/- English proof (translation)
Rewrite using `[Polynomial.cyclotomic_prime]`. Establish `hc : (∑ i ∈ Finset.range p, (Polynomial.X : Polynomial R) ^ i).comp (Polynomial.X + 1) = ∑ i ∈ Finset.range p, (Polynomial.X + 1) ^ i`. Simplify using `[Polynomial.comp, Polynomial.eval₂_finset_sum]`. Establish `h` using `geom_sum_mul (Polynomial.X + 1 : Polynomial R) p`. Rewrite `h` using `[add_sub_cancel_right]`.

Rewrite using `[hc, h]`.
-/
theorem cyclo_comp_mul_X {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] :
    (Polynomial.cyclotomic p R).comp (Polynomial.X + 1) * Polynomial.X =
      (Polynomial.X + 1) ^ p - 1 := by
  rw [Polynomial.cyclotomic_prime]
  have hc : (∑ i ∈ Finset.range p, (Polynomial.X : Polynomial R) ^ i).comp (Polynomial.X + 1) =
      ∑ i ∈ Finset.range p, (Polynomial.X + 1) ^ i := by
    simp [Polynomial.comp, Polynomial.eval₂_finset_sum]
  have h := geom_sum_mul (Polynomial.X + 1 : Polynomial R) p
  rw [add_sub_cancel_right] at h
  rw [hc, h]

/- English proof (translation)
Take `⟨w, hw⟩` from `hR.2.2.2.2.1`. Establish `h0` using `congrFun hw 0`. Establish `hq : (baseIdOf hR).ι (baseIdOf hR).Bs.q = W.π₀₁ + PowerSeries.C ((PD.p : ℕ) : O)`. Express the relevant statement in the definitionally equal form `(baseIdOf hR).ι (PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) = _`. Rewrite using `[map_add, (baseIdOf hR).ι_X]`.

Use `congr 1`. Conclude with `(baseIdOf hR).ι.commutes _`. Establish `hcyc : (W.q₀ : PowerSeries O) = (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O)`. Establish `hX : (PowerSeries.X : PowerSeries O) ≠ 0` using `PowerSeries.X_ne_zero`. Apply `mul_left_cancel₀ hX` to reduce the goal to its premises.

Rewrite using `[W.q₀_def]`. Use `congrArg (fun f : Polynomial O => (f : PowerSeries O)) (cyclo_comp_mul_X (R := O) PD.p)` as an intermediate fact. Simplify using `only [Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one] at this`. Rewrite using `[mul_comm, this, add_comm]`. Establish `h0' : W.q₀ = (w : LetA O n) 0 * (W.π₀₁ + PowerSeries.C ((PD.p : ℕ) : O))`.

Simplify `h0` using `[LocWach.q, Formalism.MainNotions.DeltaInvariantLattices.Eat, LocWach.π₀, Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C]`. Set `w0 : (PowerSeries O)ˣ` to `Units.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) 0) w`. Use `⟨w0⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[hq, ← hcyc, h0']`. Express the relevant statement in the definitionally equal form `_ = ((w0⁻¹ : (PowerSeries O)ˣ) : PowerSeries O) * ((w0 : PowerSeries O) * _)`.

Rewrite using `[← mul_assoc, Units.inv_mul, one_mul]`.
-/
theorem glue2 [IsDomain O] (hR : Ring9 W) :
    ∃ w : (PowerSeries O)ˣ, (baseIdOf hR).ι (baseIdOf hR).Bs.q = (w : PowerSeries O) *
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  have h0 := congrFun hw 0
  have hq : (baseIdOf hR).ι (baseIdOf hR).Bs.q = W.π₀₁ + PowerSeries.C ((PD.p : ℕ) : O) := by
    change (baseIdOf hR).ι (PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) = _
    rw [map_add, (baseIdOf hR).ι_X]
    congr 1
    exact (baseIdOf hR).ι.commutes _
  have hcyc : (W.q₀ : PowerSeries O) =
      (((Polynomial.cyclotomic PD.p O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) := by
    have hX : (PowerSeries.X : PowerSeries O) ≠ 0 := PowerSeries.X_ne_zero
    apply mul_left_cancel₀ hX
    rw [W.q₀_def]
    have := congrArg (fun f : Polynomial O => (f : PowerSeries O)) (cyclo_comp_mul_X (R := O) PD.p)
    simp only [Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_sub, Polynomial.coe_pow,
      Polynomial.coe_add, Polynomial.coe_one] at this
    rw [mul_comm, this, add_comm]
  have h0' : W.q₀ = (w : LetA O n) 0 * (W.π₀₁ + PowerSeries.C ((PD.p : ℕ) : O)) := by
    simpa [LocWach.q, Formalism.MainNotions.DeltaInvariantLattices.Eat, LocWach.π₀, Polynomial.aeval_add, Polynomial.aeval_X,
      Polynomial.aeval_C] using h0
  let w0 : (PowerSeries O)ˣ := Units.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) 0) w
  refine ⟨w0⁻¹, ?_⟩
  rw [hq, ← hcyc, h0']
  change _ = ((w0⁻¹ : (PowerSeries O)ˣ) : PowerSeries O) * ((w0 : PowerSeries O) * _)
  rw [← mul_assoc, Units.inv_mul, one_mul]

/- English proof (translation)
Take `⟨E, h0, h1, h2⟩` from `W.lev_π c ζ hζ`. Establish `hE` using `(LevelStatements.Lv.expRescale LL E h0 h1).1`. Rewrite using `[← hE, ← h2]`. Both sides reduce to the same expression.
-/
theorem rhoZ_exp [CharZero LL] (c : ZMod n) (ζ : LL) (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    1 + rhoZ W c ζ X = PowerSeries.C ζ * exp LL := by
  obtain ⟨E, h0, h1, h2⟩ := W.lev_π c ζ hζ
  have hE := (LevelStatements.Lv.expRescale LL E h0 h1).1
  rw [← hE, ← h2]
  rfl

end Formalism.MainNotions.N.Ln03
