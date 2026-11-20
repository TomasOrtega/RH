import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondAtOfFirstAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueCharPow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralEntriesOfCarriesStandardLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DetIntegralUnitIdeleOfIntegralFinitePartStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharRoot

/- English proof (translation)
Establish `hσ : ∀ z : D.host.E, D.sp.cm.sig (D.sp.cm.sig z) = z` using `fun z => star_star z`. Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul p q => simp [sigR, hσ]`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq]`.
-/
theorem sigR_sigR (D : D7) (w : Formalism.L2.Theta.AE D) :
    sigR (AF D.host.F) D.sp.cm.sig (sigR (AF D.host.F) D.sp.cm.sig w) = w := by
  have hσ : ∀ z : D.host.E, D.sp.cm.sig (D.sp.cm.sig z) = z := fun z => star_star z
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul p q => simp [sigR, hσ]
  | add p q hp hq => rw [map_add, map_add, hp, hq]

/- English proof (translation)
Establish `hσ : ∀ z : D.host.E, D.sp.cm.sig (D.sp.cm.sig z) = z` using `fun z => star_star z`. Establish `htr : ∀ z : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = z + D.sp.cm.sig z`. Introduce `z`. Apply `(D.sp.cm.fixed _).1` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `D.sp.cm.sig _ = _`.

Rewrite using `[map_add, hσ, add_comm]`. Take `⟨t, ht⟩` from `GlobalTheory.Member.exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr (x * Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom x) (by`. Rewrite using `[Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_mul, sigR_sigR, mul_comm])`. Use `⟨t, ?_⟩` and prove the remaining obligations. Use `congrArg Units.val ht using 1` and compare the differences between its conclusion and the goal.

Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
theorem exists_idF_eq_mul_sigR (D : D7) (x : (Formalism.L2.Theta.AE D)ˣ) :
    ∃ t : (AF D.host.F)ˣ, ((idF D t : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = (x : Formalism.L2.Theta.AE D) * sigR (AF D.host.F) D.sp.cm.sig (x : Formalism.L2.Theta.AE D) := by
  have hσ : ∀ z : D.host.E, D.sp.cm.sig (D.sp.cm.sig z) = z := fun z => star_star z
  have htr : ∀ z : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = z + D.sp.cm.sig z := by
    intro z
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add, hσ, add_comm]
  obtain ⟨t, ht⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr
    (x * Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom x) (by
      rw [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_mul, sigR_sigR, mul_comm])
  refine ⟨t, ?_⟩
  convert congrArg Units.val ht using 1
  · rfl
  · rfl

/- English proof (translation)
Take `⟨t, ht⟩` from `exists_idF_eq_mul_sigR D x`. Establish `hxx : x * x = d * idF D t`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul, ht, hd]`. Unfold `IsDetRoot at hR`.

Unfold `Formalism.L2.Theta.mt`. Use `nth_rewrite 1 [hR]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨N, -, -, m, hm, hord⟩` from `GlobalTheory.CharFin.char_finUnit_finite_order D c hcont`. Use `⟨2 * (m * n), by positivity, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_mul, sq, ← map_mul, hxx, map_mul, mul_pow, pow_mul, hord _ hfu, one_pow, one_mul, mul_comm m n, pow_mul, hbase t, one_pow]`.
-/
theorem pow_eq_one_of_isDetRoot (D : D7) (V : HSp D) (g : GA D V) (x : (Formalism.L2.Theta.AE D)ˣ) (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (n : ℕ)
    (hn : 0 < n) (hbase : ∀ t, c (idF D t) ^ n = 1) (hcont : Continuous c) (hR : IsDetRoot V g x)
    (d : (Formalism.L2.Theta.AE D)ˣ) (hd : (d : Formalism.L2.Theta.AE D) = (Formalism.L2.Theta.mt V g).det)
    (hfu : Formalism.L2.Pj.FinUnit d) : ∃ N : ℕ, 0 < N ∧ c x ^ N = 1 := by
  obtain ⟨t, ht⟩ := exists_idF_eq_mul_sigR D x
  have hxx : x * x = d * idF D t := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ht, hd]
    unfold IsDetRoot at hR
    unfold Formalism.L2.Theta.mt
    nth_rewrite 1 [hR]
    ring
  obtain ⟨N, -, -, m, hm, hord⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hcont
  refine ⟨2 * (m * n), by positivity, ?_⟩
  rw [pow_mul, sq, ← map_mul, hxx, map_mul, mul_pow, pow_mul, hord _ hfu, one_pow, one_mul, mul_comm m n, pow_mul, hbase t,
    one_pow]

/- English proof (translation)
Introduce `D V g hg`. Establish `h : infHom V g = 1` using `hg`. Establish `h2` using `congrArg (fun z : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => Matrix.det z.1) h`. Simplify using `only [Units.val_one, Matrix.det_one] at h2`. Rewrite using `[← h2]`.

Unfold `infHom Formalism.L2.Theta.mt Formalism.UG.bc`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem infPart_det_of_mem_GfC : ∀ (D : D7) (V : HSp D) (g : GA D V), g ∈ GfC V →
    infPart D (Formalism.L2.Theta.mt V g).det = 1 := by
  intro D V g hg
  have h : infHom V g = 1 := hg
  have h2 := congrArg (fun z : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => Matrix.det z.1) h
  simp only [Units.val_one, Matrix.det_one] at h2
  rw [← h2]
  unfold infHom Formalism.L2.Theta.mt Formalism.UG.bc
  rw [RingHom.map_det]
  rfl

/- English proof (translation)
Introduce `D V n hn g k hg hk hc`. Take `⟨h1, h2⟩` from `GlobalTheory.T.integral_entries_of_carries_standardLattice D.host.F D.host.E n k hc`. Establish `hu : IsUnit (Formalism.L2.Theta.mt V g).det`. Unfold `Formalism.L2.Theta.mt`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)`.

Take `⟨f1, f2⟩` from `GlobalTheory.T.det_integralUnitIdele_of_integral_finitePart D V n hn g k hk h1 h2 hu.unit hu.unit_spec`. Use `⟨hu.unit, hu.unit_spec, ?_, f1, f2⟩` and prove the remaining obligations. Rewrite using `[hu.unit_spec]`. Conclude with `infPart_det_of_mem_GfC D V g hg`.
-/
theorem finUnit_det_of_carries : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (g : GA D V) (k : GL (Fin n) (EF D)),
    g ∈ GfC V → finM V hn g = k.1 →
    Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat D.host.E n) (Formalism.L2.Col.stdLat D.host.E n) →
    ∃ d : (Formalism.L2.Theta.AE D)ˣ, (d : Formalism.L2.Theta.AE D) = (Formalism.L2.Theta.mt V g).det ∧ Formalism.L2.Pj.FinUnit d := by
  intro D V n hn g k hg hk hc
  obtain ⟨h1, h2⟩ := GlobalTheory.T.integral_entries_of_carries_standardLattice D.host.F D.host.E n k hc
  have hu : IsUnit (Formalism.L2.Theta.mt V g).det := by
    unfold Formalism.L2.Theta.mt
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  obtain ⟨f1, f2⟩ := GlobalTheory.T.det_integralUnitIdele_of_integral_finitePart D V n hn g k hk h1 h2 hu.unit hu.unit_spec
  refine ⟨hu.unit, hu.unit_spec, ?_, f1, f2⟩
  rw [hu.unit_spec]
  exact infPart_det_of_mem_GfC D V g hg

end GlobalTheory.CharRoot

/- English proof (translation)
Introduce `B X I hI hP l Z u a Ch₀ A hA j hj i hi β`. Establish `hc : ChrEq (A.chr (j + 1)) (I.C.mu0 ⟨j, hj⟩ * I.xi a)` using `hA.chr ⟨j, hj⟩`. Take `⟨hG, hF, hR⟩` from `hA.kA i hi β`. Establish `hb` using `hA.base i hi β`. Choose the witnesses or unpack the hypotheses as in `⟨n, hn, hξ⟩ : ∃ n : ℕ, 0 < n ∧ I.xi a ^ n = 1 := by`.

Establish `hx` using `hI.xi_reads a`. Establish `ht : IsOfFinOrder (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K)` using `(I.tup a).2.1.1.1.2`. Take `⟨n, hn, hpow⟩` from `ht.exists_pow_eq_one`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Use extensionality with `y`. Establish `h1` using `hx y`. Simplify using `only [SubgroupClass.coe_pow, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, OneMemClass.coe_one, MonoidHom.one_apply, Units.val_one]`. Rewrite using `[h1, ← map_pow, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hpow]`. Simplify using the standard rewrite rules.

Establish `hpow : ∀ k : ℕ, ChrEq (A.chr (j + 1) ^ (k + 1)) ((I.C.mu0 ⟨j, hj⟩ * I.xi a) ^ (k + 1))`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using hc`. Consider the case `succ k ih`.

Rewrite using `[pow_succ (A.chr (j + 1)) (k + 1), pow_succ _ (k + 1)]`. Conclude with `GlobalTheory.AdelicLiftCompare.chrEq_mul ih hc`. Establish `hbase : ∀ t, A.chr (j + 1) (idF (I.rec7 l Z) t) ^ n = 1`. Introduce `t`. Take `⟨k, rfl⟩ : ∃ k, n = k + 1` from `⟨n - 1, by omega⟩`.

Establish `h1` using `hpow k`. Rewrite `h1` using `[mul_pow, hξ, mul_one]`. Establish `h2` using `GlobalTheory.GridWeil.triv_base h1 (PsiExist.trivOn_pow (I.C.isMu0 ⟨j, hj⟩).triv (k + 1)) t`. Simplify using `using h2`. Establish `hcar : Formalism.L2.Herm.Carries (A.kb i β) (Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) (Formalism.L2.Col.stdLat B.fields.E (B.R.N i))`.

Take `⟨h1, h2⟩` from `hb`. Establish `h` using `h1.lat`. Use `erw [h2] at h`. Conclude with `h`. Take `⟨d, hd, hfu⟩` from `GlobalTheory.CharRoot.finUnit_det_of_carries (I.rec7 l Z) _ _ _ (A.kA i β) (A.kb i β) hG hF hcar`.

Conclude with `GlobalTheory.CharRoot.pow_eq_one_of_isDetRoot (I.rec7 l Z) _ (A.kA i β) (A.xr i β) (A.chr (j + 1)) n hn hbase hc.1.1 hR d hd hfu`.
-/
theorem GlobalTheory.CharRoot.chr_xr_pow_eq_one : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ j, j < B.R.m → ∀ i, i ≤ B.R.m → ∀ β, ∃ n : ℕ, 0 < n ∧ A.chr (j + 1) (A.xr i β) ^ n = 1 := by
  intro B X I hI hP l Z u a Ch₀ A hA j hj i hi β
  have hc : ChrEq (A.chr (j + 1)) (I.C.mu0 ⟨j, hj⟩ * I.xi a) := hA.chr ⟨j, hj⟩
  obtain ⟨hG, hF, hR⟩ := hA.kA i hi β
  have hb := hA.base i hi β

  obtain ⟨n, hn, hξ⟩ : ∃ n : ℕ, 0 < n ∧ I.xi a ^ n = 1 := by
    have hx := hI.xi_reads a
    have ht : IsOfFinOrder (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) := (I.tup a).2.1.1.1.2
    obtain ⟨n, hn, hpow⟩ := ht.exists_pow_eq_one
    refine ⟨n, hn, ?_⟩
    apply Subtype.ext
    ext y
    have h1 := hx y
    simp only [SubgroupClass.coe_pow, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, OneMemClass.coe_one, MonoidHom.one_apply, Units.val_one]
    rw [h1, ← map_pow, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hpow]
    simp

  have hpow : ∀ k : ℕ, ChrEq (A.chr (j + 1) ^ (k + 1)) ((I.C.mu0 ⟨j, hj⟩ * I.xi a) ^ (k + 1)) := by
    intro k
    induction k with
    | zero => simpa using hc
    | succ k ih =>
      rw [pow_succ (A.chr (j + 1)) (k + 1), pow_succ _ (k + 1)]
      exact GlobalTheory.AdelicLiftCompare.chrEq_mul ih hc
  have hbase : ∀ t, A.chr (j + 1) (idF (I.rec7 l Z) t) ^ n = 1 := by
    intro t
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h1 := hpow k
    rw [mul_pow, hξ, mul_one] at h1
    have h2 := GlobalTheory.GridWeil.triv_base h1 (PsiExist.trivOn_pow (I.C.isMu0 ⟨j, hj⟩).triv (k + 1)) t
    simpa using h2

  have hcar : Formalism.L2.Herm.Carries (A.kb i β) (Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) (Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) := by
    obtain ⟨h1, h2⟩ := hb
    have h := h1.lat
    erw [h2] at h
    exact h
  obtain ⟨d, hd, hfu⟩ := GlobalTheory.CharRoot.finUnit_det_of_carries (I.rec7 l Z) _ _ _ (A.kA i β) (A.kb i β) hG hF hcar
  exact GlobalTheory.CharRoot.pow_eq_one_of_isDetRoot (I.rec7 l Z) _ (A.kA i β) (A.xr i β) (A.chr (j + 1)) n hn hbase hc.1.1 hR d hd hfu
