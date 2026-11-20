import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPhiBridge
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLenThreeThickLetters

open scoped TensorProduct

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [IsDomain O] [IsDiscreteValuationRing O]

namespace ArcLengthThreeFiltration

open PowerSeries

variable {W : LocWach PD LL O v n} (Br : PhiBridge W)

def ea (a : ZMod n) (F : PowerSeries O) : W.EE :=
  algebraMap (LetA O n) W.EE (letE a * Br.cst F)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Formalism.BasicNotions.letE, Pi.mul_apply, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem letE_mul_self (a : ZMod n) : (letE a : LetA O n) * letE a = letE a := by
  funext i
  simp only [Formalism.BasicNotions.letE, Pi.mul_apply, Pi.single_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `h : Br.cst (F + F') = Br.cst F + Br.cst F'` using `funext fun _ => map_add Br.ι F F'`. Unfold `Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea`. Rewrite using `[h, mul_add, map_add]`.
-/
theorem ea_add (a : ZMod n) (F F' : PowerSeries O) : ea Br a (F + F') = ea Br a F + ea Br a F' := by
  have h : Br.cst (F + F') = Br.cst F + Br.cst F' := funext fun _ => map_add Br.ι F F'
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea
  rw [h, mul_add, map_add]

/- English proof (translation)
Establish `h : Br.cst 0 = 0` using `funext fun _ => map_zero Br.ι`. Unfold `Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea`. Rewrite using `[h, mul_zero, map_zero]`.
-/
theorem ea_zero (a : ZMod n) : ea Br a 0 = 0 := by
  have h : Br.cst 0 = 0 := funext fun _ => map_zero Br.ι
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea
  rw [h, mul_zero, map_zero]

/- English proof (translation)
Establish `h : Br.cst (G * F) = Br.cst G * Br.cst F` using `funext fun _ => map_mul Br.ι G F`. Unfold `Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea`. Rewrite using `[← map_mul, h]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cst_mul_ea (a : ZMod n) (G F : PowerSeries O) :
    algebraMap (LetA O n) W.EE (Br.cst G) * ea Br a F = ea Br a (G * F) := by
  have h : Br.cst (G * F) = Br.cst G * Br.cst F := funext fun _ => map_mul Br.ι G F
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea
  rw [← map_mul, h]
  congr 1
  ring

/- English proof (translation)
Establish `h1 : Br.cst (C x * F) = algebraMap O (LetA O n) x * Br.cst F`. Use function extensionality and compare the values at `i`. Use `show Br.ι (C x * F) = (algebraMap O (LetA O n) x) i * Br.ι F`. Rewrite using `[← PowerSeries.smul_eq_C_mul, map_smul, Algebra.smul_def]`. Both sides reduce to the same expression.

Unfold `Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea`. Rewrite using `[h1, mul_left_comm, map_mul, ← IsScalarTower.algebraMap_apply]`.
-/
theorem ea_C_mul (a : ZMod n) (x : O) (F : PowerSeries O) :
    ea Br a (C x * F) = algebraMap O W.EE x * ea Br a F := by
  have h1 : Br.cst (C x * F) = algebraMap O (LetA O n) x * Br.cst F := by
    funext i
    show Br.ι (C x * F) = (algebraMap O (LetA O n) x) i * Br.ι F
    rw [← PowerSeries.smul_eq_C_mul, map_smul, Algebra.smul_def]
    rfl
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea
  rw [h1, mul_left_comm, map_mul, ← IsScalarTower.algebraMap_apply]

/- English proof (translation)
Establish `h1 : Br.cst (∑ i ∈ s, F i) = ∑ i ∈ s, Br.cst (F i)`. Use function extensionality and compare the values at `j`. Rewrite using `[Finset.sum_apply]`. Conclude with `map_sum Br.ι F s`. Unfold `Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea`.

Rewrite using `[h1, Finset.mul_sum, map_sum]`.
-/
theorem ea_sum (a : ZMod n) {ι : Type*} (s : Finset ι) (F : ι → PowerSeries O) :
    ea Br a (∑ i ∈ s, F i) = ∑ i ∈ s, ea Br a (F i) := by
  have h1 : Br.cst (∑ i ∈ s, F i) = ∑ i ∈ s, Br.cst (F i) := by
    funext j
    rw [Finset.sum_apply]
    exact map_sum Br.ι F s
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea
  rw [h1, Finset.mul_sum, map_sum]

/- English proof (translation)
Unfold `Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea at h`. Establish `h1` using `congrFun (W.EE_inj h) a`. Simplify using `only [Pi.mul_apply, Formalism.BasicNotions.letE, Pi.single_eq_same, one_mul] at h1`. Conclude with `Br.inj h1`.
-/
theorem ea_inj (a : ZMod n) {F F' : PowerSeries O} (h : ea Br a F = ea Br a F') : F = F' := by
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea at h
  have h1 := congrFun (W.EE_inj h) a
  simp only [Pi.mul_apply, Formalism.BasicNotions.letE, Pi.single_eq_same, one_mul] at h1
  exact Br.inj h1

/- English proof (translation)
Take `⟨U, hU⟩` from `Br.range u hu a`. Use `⟨U, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.mul_apply, Formalism.BasicNotions.letE]`. Distinguish the cases in `h : i = a`.

Substitute `h` using the available equality. Simplify using `only [Pi.single_eq_same, one_mul]`. Conclude with `hU`. Simplify using `[Pi.single_apply, h]`.
-/
theorem letE_mul_AΔ (a : ZMod n) {u : LetA O n} (hu : u ∈ W.AΔ) :
    ∃ U : PowerSeries O, letE a * u = letE a * Br.cst U := by
  obtain ⟨U, hU⟩ := Br.range u hu a
  refine ⟨U, ?_⟩
  funext i
  simp only [Pi.mul_apply, Formalism.BasicNotions.letE]
  by_cases h : i = a
  · subst h
    simp only [Pi.single_eq_same, one_mul]
    exact hU
  · simp [Pi.single_apply, h]

/- English proof (translation)
Unfold `Formalism.MainNotions.ArcLiftingSetup.InFr at h`. Take `⟨u, hu, h⟩` from `h`. Take `⟨U, hU⟩` from `letE_mul_AΔ Br a hu`. Use `⟨U, ?_⟩` and prove the remaining obligations. Rewrite using `[h]`.

Unfold `Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea`. Use `congr 1`. Establish `hc : Br.cst (N * U) = Br.cst N * Br.cst U` using `funext fun _ => map_mul Br.ι N U`. Rewrite using `[hc]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem inFr_ea (a : ZMod n) {N D : PowerSeries O} {f : W.EE} (h : InFr W a (Br.cst N) (Br.cst D) f) :
    ∃ U : PowerSeries O, algebraMap (LetA O n) W.EE (Br.cst D) * f = ea Br a (N * U) := by
  unfold Formalism.MainNotions.ArcLiftingSetup.InFr at h
  obtain ⟨u, hu, h⟩ := h
  obtain ⟨U, hU⟩ := letE_mul_AΔ Br a hu
  refine ⟨U, ?_⟩
  rw [h]
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea
  congr 1
  have hc : Br.cst (N * U) = Br.cst N * Br.cst U := funext fun _ => map_mul Br.ι N U
  rw [hc]
  calc (letE a : LetA O n) * Br.cst N * u = Br.cst N * ((letE a : LetA O n) * u) := by ring
    _ = Br.cst N * ((letE a : LetA O n) * Br.cst U) := by rw [hU]
    _ = (letE a : LetA O n) * (Br.cst N * Br.cst U) := by ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem p_zero : Br.P.p 0 = X := rfl

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero`. Unfold `Formalism.MainNotions.ArcLiftingSetup.ps`. Rewrite using `[pow_zero, AlgHom.one_apply]`. Use function extensionality and compare the values at `i`.

Use `show W.π₀₁ + ((PD.p : ℕ) : PowerSeries O) = Br.ι X`. Rewrite using `[Br.ι_X, map_natCast]`. Consider the case `succ s ih`. Unfold `Formalism.MainNotions.ArcLiftingSetup.ps at ih ⊢`. Rewrite using `[pow_succ', AlgHom.mul_apply, ih]`.

Use function extensionality and compare the values at `i`. Use `show W.φ₀ (Br.ι (Br.P.p s)) = Br.ι (Br.P.p (s + 1))`. Rewrite using `[← Br.ι_φ]`. Use `congr 1`. Use `show Br.P.φ ((Br.P.φ : PowerSeries O → PowerSeries O)^[s] X) = (Br.P.φ : PowerSeries O → PowerSeries O)^[s + 1] X`.

Rewrite using `[Function.iterate_succ_apply']`.
-/
theorem ps_cst (s : ℕ) : ps W s = Br.cst (Br.P.p s) := by
  induction s with
  | zero =>
    unfold Formalism.MainNotions.ArcLiftingSetup.ps
    rw [pow_zero, AlgHom.one_apply]
    funext i
    show W.π₀₁ + ((PD.p : ℕ) : PowerSeries O) = Br.ι X
    rw [Br.ι_X, map_natCast]
  | succ s ih =>
    unfold Formalism.MainNotions.ArcLiftingSetup.ps at ih ⊢
    rw [pow_succ', AlgHom.mul_apply, ih]
    funext i
    show W.φ₀ (Br.ι (Br.P.p s)) = Br.ι (Br.P.p (s + 1))
    rw [← Br.ι_φ]
    congr 1
    show Br.P.φ ((Br.P.φ : PowerSeries O → PowerSeries O)^[s] X) = (Br.P.φ : PowerSeries O → PowerSeries O)^[s + 1] X
    rw [Function.iterate_succ_apply']

/- English proof (translation)
Simplify using `only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]`. Rewrite using `[ps_cst Br, ps_cst Br]`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.mul_apply, Pi.pow_apply]`. Use `show Br.ι X ^ F 0 * Br.ι (Br.P.p 1) ^ F 1 = Br.ι (X ^ F 0 * Br.P.p 1 ^ F 1)`.

Rewrite using `[map_mul, map_pow, map_pow]`.
-/
theorem prod_two_levels_eq_const (F : ℕ → ℕ) :
    (∏ s ∈ Finset.range 2, ps W s ^ F s) = Br.cst (X ^ F 0 * Br.P.p 1 ^ F 1) := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  rw [ps_cst Br, ps_cst Br]
  funext i
  simp only [Pi.mul_apply, Pi.pow_apply]
  show Br.ι X ^ F 0 * Br.ι (Br.P.p 1) ^ F 1 = Br.ι (X ^ F 0 * Br.P.p 1 ^ F 1)
  rw [map_mul, map_pow, map_pow]

/- English proof (translation)
Use linear arithmetic over natural numbers and integers.
-/
theorem toNat_split (m : ℕ) (α : ℤ) (h : -(m : ℤ) ≤ α) :
    m + α.toNat = (-α).toNat + (m + α).toNat := by
  omega

end ArcLengthThreeFiltration
end Formalism.MainNotions.N.FrobeniusPowerSeries
