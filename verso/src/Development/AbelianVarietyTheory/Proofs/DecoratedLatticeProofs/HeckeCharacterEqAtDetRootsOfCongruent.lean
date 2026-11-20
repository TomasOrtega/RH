import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIffOfCarries
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleCharacterAtBasePointDetRootRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDetRoot
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.DetNormOneGen
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open Formalism.L2.Pj

namespace GlobalTheory.DetRootApprox

/- English proof (translation)
Set `J : Ideal v.integer` to `{ carrier := {z | v (z : K) ≤ ε} add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq, Subring.coe_add] at ha hb ⊢`. Conclude with `(v.map_add _ _).trans (max_le ha hb)`. Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := fun c z hz => by`.

Simplify using `only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, map_mul] at hz ⊢`. Combine the equalities or inequalities in the displayed calculation. Establish `hint : ∀ r s, v (M r s) ≤ 1`. Introduce `r s`. Use `v.map_add (M r s - (1 : Matrix (Fin n) (Fin n) K) r s) ((1 : Matrix (Fin n) (Fin n) K) r s)` as an intermediate fact.

Rewrite `this` using `[sub_add_cancel]`. Use `this.trans (max_le ((h r s).trans hε) ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases hrs : r = s <;> simp [Matrix.one_apply, hrs]`. Set `M' : Matrix (Fin n) (Fin n) v.integer` to `fun r s => ⟨M r s, hint r s⟩`. Establish `hone : ∀ r s, (((1 : Matrix (Fin n) (Fin n) v.integer) r s : v.integer) : K) = (1 : Matrix (Fin n) (Fin n) K) r s`.

Introduce `r s`. Apply the tactic sequence `by_cases hrs : r = s <;> simp [Matrix.one_apply, hrs]`. Establish `hq : (Ideal.Quotient.mk J).mapMatrix M' = 1`. Use extensionality with `r s`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, ← Matrix.map_one (Ideal.Quotient.mk J) (map_zero _) (map_one _), Matrix.map_apply, Ideal.Quotient.eq]`.

Express the relevant statement in the definitionally equal form `v (((M' r s - (1 : Matrix (Fin n) (Fin n) v.integer) r s : v.integer)) : K) ≤ ε`. Rewrite using `[AddSubgroupClass.coe_sub, hone]`. Conclude with `h r s`. Establish `hd : Ideal.Quotient.mk J M'.det = Ideal.Quotient.mk J 1`. Rewrite using `[RingHom.map_det, hq, Matrix.det_one, map_one]`.

Establish `hmem` using `Ideal.Quotient.eq.mp hd`. Establish `hcoe : ((M'.det : v.integer) : K) = M.det`. Rewrite using `[show ((M'.det : v.integer) : K) = v.integer.subtype M'.det from rfl, RingHom.map_det]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `v (((M'.det - 1 : v.integer)) : K) ≤ ε at hmem`.

Rewrite `hmem` using `[AddSubgroupClass.coe_sub, hcoe, OneMemClass.coe_one]`. Then use the resulting hypothesis.
-/
theorem det_sub_one_le {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (ε : Γ) (hε : ε ≤ 1)
    (h : ∀ r s, v (M r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ ε) : v (M.det - 1) ≤ ε := by
  let J : Ideal v.integer :=
    { carrier := {z | v (z : K) ≤ ε}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Subring.coe_add] at ha hb ⊢
        exact (v.map_add _ _).trans (max_le ha hb)
      zero_mem' := by simp
      smul_mem' := fun c z hz => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, map_mul] at hz ⊢
        calc v (c : K) * v (z : K) ≤ 1 * ε := mul_le_mul' c.2 hz
          _ = ε := one_mul ε }
  have hint : ∀ r s, v (M r s) ≤ 1 := by
    intro r s
    have := v.map_add (M r s - (1 : Matrix (Fin n) (Fin n) K) r s) ((1 : Matrix (Fin n) (Fin n) K) r s)
    rw [sub_add_cancel] at this
    refine this.trans (max_le ((h r s).trans hε) ?_)
    by_cases hrs : r = s <;> simp [Matrix.one_apply, hrs]
  let M' : Matrix (Fin n) (Fin n) v.integer := fun r s => ⟨M r s, hint r s⟩
  have hone : ∀ r s, (((1 : Matrix (Fin n) (Fin n) v.integer) r s : v.integer) : K) = (1 : Matrix (Fin n) (Fin n) K) r s := by
    intro r s
    by_cases hrs : r = s <;> simp [Matrix.one_apply, hrs]
  have hq : (Ideal.Quotient.mk J).mapMatrix M' = 1 := by
    ext r s
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, ← Matrix.map_one (Ideal.Quotient.mk J) (map_zero _) (map_one _),
      Matrix.map_apply, Ideal.Quotient.eq]
    change v (((M' r s - (1 : Matrix (Fin n) (Fin n) v.integer) r s : v.integer)) : K) ≤ ε
    rw [AddSubgroupClass.coe_sub, hone]
    exact h r s
  have hd : Ideal.Quotient.mk J M'.det = Ideal.Quotient.mk J 1 := by
    rw [RingHom.map_det, hq, Matrix.det_one, map_one]
  have hmem := Ideal.Quotient.eq.mp hd
  have hcoe : ((M'.det : v.integer) : K) = M.det := by
    rw [show ((M'.det : v.integer) : K) = v.integer.subtype M'.det from rfl, RingHom.map_det]
    rfl
  change v (((M'.det - 1 : v.integer)) : K) ≤ ε at hmem
  rwa [AddSubgroupClass.coe_sub, hcoe, OneMemClass.coe_one] at hmem

/- English proof (translation)
Establish `hu : IsUnit (algebraMap E (FiniteAdeleRing (𝓞 E) E) (K : E))` using `(IsUnit.mk0 (K : E) (by exact_mod_cast hK.ne')).map _`. Rewrite `hu` using `[FiniteAdeleRing.isUnit_iff]`. Take `⟨h0, hev⟩` from `hu`. Establish `hval : ∀ P : HeightOneSpectrum (𝓞 E), algebraMap E (FiniteAdeleRing (𝓞 E) E) (K : E) P = (K : P.adicCompletion E)`. Introduce `P`.

Rewrite using `[FiniteAdeleRing.algebraMap_apply]`. Apply the tactic sequence `first | exact map_natCast (algebraMap E (P.adicCompletion E)) K | norm_cast | simp | rfl`. Establish `hfin` using `Filter.eventually_cofinite.1 hev`. Establish `hpos : ∀ P : HeightOneSpectrum (𝓞 E), ∃ m : ℕ, WithZero.exp (-(m : ℤ)) < Valued.v ((K : P.adicCompletion E))`. Introduce `P`.

Establish `hne : Valued.v ((K : P.adicCompletion E)) ≠ 0`. Rewrite using `[← hval]`. Conclude with `(Valuation.ne_zero_iff _).2 (h0 P)`. Use `⟨(-(WithZero.log (Valued.v ((K : P.adicCompletion E)))) + 1).toNat, ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [← WithZero.exp_log hne]`.

Rewrite using `[WithZero.exp_lt_exp]`. Use linear arithmetic over natural numbers and integers. Use `choose m hm using hpos`. Take `⟨S, hS⟩ : ∃ S : ℕ, ∀ P ∈ hfin.toFinset, m P ≤ S` from `⟨_, fun P hP => Finset.le_sup (f := m) hP⟩`. Use `⟨S + 1, fun P => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hP : P ∈ hfin.toFinset`. Use `lt_of_le_of_lt (WithZero.exp_le_exp.2 ?_) (hm P)` and prove the remaining obligations. Use `hS P hP` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite `hP` using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not, hval]`.

Use `lt_of_lt_of_eq ?_ hP.symm` and prove the remaining obligations. Rewrite using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_depth (E : Type) [Field E] [NumberField E] (K : ℕ) (hK : 0 < K) :
    ∃ N₀ : ℕ, ∀ P : HeightOneSpectrum (𝓞 E), WithZero.exp (-(N₀ : ℤ)) < Valued.v ((K : P.adicCompletion E)) := by
  have hu : IsUnit (algebraMap E (FiniteAdeleRing (𝓞 E) E) (K : E)) :=
    (IsUnit.mk0 (K : E) (by exact_mod_cast hK.ne')).map _
  rw [FiniteAdeleRing.isUnit_iff] at hu
  obtain ⟨h0, hev⟩ := hu
  have hval : ∀ P : HeightOneSpectrum (𝓞 E), algebraMap E (FiniteAdeleRing (𝓞 E) E) (K : E) P = (K : P.adicCompletion E) := by
    intro P
    rw [FiniteAdeleRing.algebraMap_apply]
    first | exact map_natCast (algebraMap E (P.adicCompletion E)) K | norm_cast | simp | rfl
  have hfin := Filter.eventually_cofinite.1 hev
  have hpos : ∀ P : HeightOneSpectrum (𝓞 E), ∃ m : ℕ, WithZero.exp (-(m : ℤ)) < Valued.v ((K : P.adicCompletion E)) := by
    intro P
    have hne : Valued.v ((K : P.adicCompletion E)) ≠ 0 := by
      rw [← hval]
      exact (Valuation.ne_zero_iff _).2 (h0 P)
    refine ⟨(-(WithZero.log (Valued.v ((K : P.adicCompletion E)))) + 1).toNat, ?_⟩
    conv_rhs => rw [← WithZero.exp_log hne]
    rw [WithZero.exp_lt_exp]
    omega
  choose m hm using hpos
  obtain ⟨S, hS⟩ : ∃ S : ℕ, ∀ P ∈ hfin.toFinset, m P ≤ S := ⟨_, fun P hP => Finset.le_sup (f := m) hP⟩
  refine ⟨S + 1, fun P => ?_⟩
  by_cases hP : P ∈ hfin.toFinset
  · refine lt_of_le_of_lt (WithZero.exp_le_exp.2 ?_) (hm P)
    have := hS P hP
    omega
  · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not, hval] at hP
    refine lt_of_lt_of_eq ?_ hP.symm
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega

/- English proof (translation)
Rewrite using `[GlobalTheory.IdemSupport.mem_intAE_iff, GlobalTheory.Mem.Col2.mem_rInt_iff]`. Both sides reduce to the same expression.
-/
theorem fin_mem_iff (D : D7) (a : AE D) :
    finPart D a ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (adAt D.host.F P (toEAf D a)) ≤ 1 := by
  rw [GlobalTheory.IdemSupport.mem_intAE_iff, GlobalTheory.Mem.Col2.mem_rInt_iff]
  rfl

/- English proof (translation)
Take `⟨e, he, -⟩` from `GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E`. Establish `hu : IsUnit (GlobalTheory.Mem.Col2.afIso D.host.F D.host.E (toEAf D a))`. Rewrite using `[FiniteAdeleRing.isUnit_iff]`. Use `⟨fun P h => ?_, Filter.Eventually.of_forall fun P => h2 P⟩` and prove the remaining obligations. Use `h2 P` as an intermediate fact.

Rewrite `this` using `[show adAt D.host.F P (toEAf D a) = GlobalTheory.Mem.Col2.afIso D.host.F D.host.E (toEAf D a) P from rfl, h]`. Simplify using `at this`. Establish `hu2 : IsUnit (toEAf D a)`. Simplify using `using hu.map (GlobalTheory.Mem.Col2.afIso D.host.F D.host.E).symm`. Establish `hf : IsUnit (finPart D a)`.

Use `hu2.map (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm` as an intermediate fact. Simplify `this` using `[toEAf]`. Establish `hi : IsUnit (infPart D a)` using `by rw [h1]; exact isUnit_one`. Establish `: IsUnit (e a)`. Rewrite using `[Prod.isUnit_iff, (he a).1, (he a).2]`.

Conclude with `⟨hi, hf⟩`. Simplify using `using this.map e.symm`.
-/
theorem isUnit_of_parts (D : D7) (a : AE D) (h1 : infPart D a = 1)
    (h2 : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (adAt D.host.F P (toEAf D a)) = 1) : IsUnit a := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hu : IsUnit (GlobalTheory.Mem.Col2.afIso D.host.F D.host.E (toEAf D a)) := by
    rw [FiniteAdeleRing.isUnit_iff]
    refine ⟨fun P h => ?_, Filter.Eventually.of_forall fun P => h2 P⟩
    have := h2 P
    rw [show adAt D.host.F P (toEAf D a) = GlobalTheory.Mem.Col2.afIso D.host.F D.host.E (toEAf D a) P from rfl, h] at this
    simp at this
  have hu2 : IsUnit (toEAf D a) := by
    simpa using hu.map (GlobalTheory.Mem.Col2.afIso D.host.F D.host.E).symm
  have hf : IsUnit (finPart D a) := by
    have := hu2.map (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm
    simpa [toEAf] using this
  have hi : IsUnit (infPart D a) := by rw [h1]; exact isUnit_one
  have : IsUnit (e a) := by
    rw [Prod.isUnit_iff, (he a).1, (he a).2]
    exact ⟨hi, hf⟩
  simpa using this.map e.symm

end GlobalTheory.DetRootApprox

namespace GlobalTheory.DetRootApprox

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Nat.cast_succ]`. Conclude with `(v.map_add _ _).trans (max_le ih (le_of_eq v.map_one))`.
-/
theorem natCast_le_one {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (n : ℕ) :
    v (n : K) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact (v.map_add _ _).trans (max_le ih (le_of_eq v.map_one))

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D c hc`. Take `⟨N, hN, hker, -⟩` from `GlobalTheory.CharFin.char_finUnit_finite_order D c hc.1`. Take `⟨N₀, hN₀⟩` from `exists_depth D.host.E (2 * N) (by omega)`. Use `⟨N₀, ?_⟩` and prove the remaining obligations. Introduce `V n hn g w hw hcong x hx`.

Establish `hnorm : (Formalism.L2.Theta.mt V w).det * sigR (AF D.host.F) D.sp.cm.sig (Formalism.L2.Theta.mt V w).det = 1`. Use `GlobalTheory.LevelSubgroup.det_norm_one_gen (sigR (AF D.host.F) D.sp.cm.sig) (sigR (AF D.host.F) D.sp.cm.sig) (RingHom.id _) (fun _ => rfl) (JR (AF D.host.F) V.gram) (matHom V w).1 (GlobalTheory.LevelSubgroup.isUnit_det_JR _ (GlobalTheory.LevelSubgroup.gram_det_ne_zero V)) w.2` as an intermediate fact. Simplify using `only [RingHom.coe_id, Matrix.map_id] at this`. Conclude with `this`. Establish `hinf : infPart D (Formalism.L2.Theta.mt V w).det = 1` using `GlobalTheory.CharRoot.infPart_det_of_mem_GfC D V w hw`.

Establish `hloc : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (adAt D.host.F P (toEAf D (Formalism.L2.Theta.mt V w).det) - 1) ≤ WithZero.exp (-(N₀ : ℤ))`. Introduce `P`. Establish `h1` using `det_sub_one_le Valued.v ((finM V hn w).map (adAt D.host.F P)) (WithZero.exp (-(N₀ : ℤ))) (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega) (fun r s => by`. Use `hcong P r s` as an intermediate fact. Rewrite `this` using `[map_sub]`.

Use `this using 3` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first | rfl | (rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp))`. Establish `h2 : ((finM V hn w).map (adAt D.host.F P)).det = adAt D.host.F P (toEAf D (Formalism.L2.Theta.mt V w).det)`. Establish `e1 : (finM V hn w).det = toEAf D (Formalism.L2.Theta.mt V w).det`. Unfold `finM`.

Rewrite using `[Matrix.det_reindex_self, RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[← e1, RingHom.map_det]`. Both sides reduce to the same expression. Rewrite `h1` using `[h2]`.

Conclude with `h1`. Establish `hF2 : (2 : D.host.F) ≠ 0` using `two_ne_zero`. Establish `h2m : (2 : AE D) * algebraMap D.host.F (AE D) (2 : D.host.F)⁻¹ = 1`. Rewrite using `[show (2 : AE D) = algebraMap D.host.F (AE D) 2 from (map_ofNat _ 2).symm, ← map_mul, mul_inv_cancel₀ hF2, map_one]`. Establish `hKne : ((2 * N : ℕ) : D.host.F) ≠ 0` using `by exact_mod_cast (by omega : 2 * N ≠ 0)`.

Establish `hKm : ((2 * N : ℕ) : AE D) * algebraMap D.host.F (AE D) ((2 * N : ℕ) : D.host.F)⁻¹ = 1`. Establish `e0 : ((2 * N : ℕ) : AE D) = algebraMap D.host.F (AE D) ((2 * N : ℕ) : D.host.F)` using `(map_natCast (algebraMap D.host.F (AE D)) (2 * N)).symm`. Rewrite using `[e0, ← map_mul, mul_inv_cancel₀ hKne]`. Conclude with `map_one _`. Take `⟨h2, h2m⟩ : ∃ h2 : AE D, (2 : AE D) * h2 = 1` from `⟨_, h2m⟩`.

Take `⟨hK, hKm⟩ : ∃ hK : AE D, ((2 * N : ℕ) : AE D) * hK = 1` from `⟨_, hKm⟩`. Establish `hNK : (N : AE D) * hK = h2`. Combine the equalities or inequalities in the displayed calculation. Establish `hσ2 : sigR (AF D.host.F) D.sp.cm.sig h2 = h2`. Establish `e1 : sigR (AF D.host.F) D.sp.cm.sig h2 * 2 = 1`.

Use `congrArg (sigR (AF D.host.F) D.sp.cm.sig) h2m` as an intermediate fact. Rewrite `this` using `[map_mul, map_ofNat, map_one]`. Rewrite using `[mul_comm]`. Conclude with `this`. Combine the equalities or inequalities in the displayed calculation.

Generalize the expression as in `hd : (Formalism.L2.Theta.mt V w).det = d at hnorm hinf hloc`. Establish `hrt : (1 + d) * h2 = 1 + (N : AE D) * ((d - 1) * hK)`. Take the linear combination `(-(d - 1)) * hNK + h2m`. Establish `hroot : (1 + d) * h2 = d * sigR (AF D.host.F) D.sp.cm.sig ((1 + d) * h2)`. Rewrite using `[map_mul, map_add, map_one, hσ2]`.

Take the linear combination `(-h2) * hnorm`. Establish `hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (adAt D.host.F P (toEAf D ((d - 1) * hK))) < 1 ∧ Valued.v (adAt D.host.F P (toEAf D ((1 + d) * h2))) = 1`. Introduce `P`. Set `φ` to `(adAt D.host.F P).comp (toEAf D)`. Establish `hφK : φ hK * ((2 * N : ℕ) : P.adicCompletion D.host.E) = 1`.

Use `congrArg φ hKm` as an intermediate fact. Rewrite `this` using `[map_mul, map_natCast, map_one]`. Rewrite using `[mul_comm]`. Conclude with `this`. Establish `hvK : Valued.v (φ hK) * Valued.v ((2 * N : ℕ) : P.adicCompletion D.host.E) = 1`.

Rewrite using `[← map_mul, hφK, map_one]`. Establish `hKpos : Valued.v (φ hK) ≠ 0`. Introduce `h0`. Rewrite `hvK` using `[h0, zero_mul]`. Conclude with `zero_ne_one hvK`.

Establish `ht1 : Valued.v (φ ((d - 1) * hK)) < 1`. Rewrite using `[map_mul, map_mul, map_sub, map_one]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨ht1, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Valued.v (φ ((1 + d) * h2)) = 1`.

Rewrite using `[hrt, map_add, map_one, map_mul, map_natCast]`. Apply `Valuation.map_one_add_of_lt` to reduce the goal to its premises. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hinfr : infPart D ((1 + d) * h2) = 1`.

Use `congrArg (infPart D) h2m` as an intermediate fact. Rewrite `this` using `[map_mul, map_ofNat, map_one]`. Rewrite using `[map_mul, map_add, map_one, hinf]`. Take the linear combination `this`. Establish `hru : IsUnit ((1 + d) * h2)` using `isUnit_of_parts D _ hinfr (fun P => (hv P).2)`.

Establish `hcr : c hru.unit = 1`. Use `hker hru.unit ⟨by rw [IsUnit.unit_spec]; exact hinfr, by rw [IsUnit.unit_spec]; exact (fin_mem_iff D _).2 (fun P => ((hv P).2).le), ?_⟩ ⟨finPart D ((d - 1) * hK), (fin_mem_iff D _).2 (fun P => (hv P).1.le), ?_⟩` and prove the remaining obligations. Use `(fin_mem_iff D _).2 (fun P => ?_)` and prove the remaining obligations. Establish `e1` using `congrArg (fun a => adAt D.host.F P (toEAf D a)) hru.unit.inv_mul`. Simplify using `only [map_mul, map_one, IsUnit.unit_spec] at e1`.

Rewrite `e1` using `[← map_mul, ← map_mul]`. Establish `e2` using `congrArg Valued.v e1`. Rewrite `e2` using `[map_mul, map_one, map_mul, map_mul]`. Establish `h3` using `(hv P).2`. Rewrite `h3` using `[map_mul, map_mul]`.

Rewrite `e2` using `[h3, mul_one]`. Conclude with `e2.le`. Rewrite using `[IsUnit.unit_spec, hrt, map_add, map_one, add_sub_cancel_left, map_mul, map_natCast, nsmul_eq_mul]`. Use `⟨x * hru.unit, ?_, ?_⟩` and prove the remaining obligations. Unfold `IsDetRoot at hx ⊢`.

Establish `hmt : (matHom V (g * w)).1.det = (matHom V g).1.det * d`. Rewrite using `[← hd, map_mul, Units.val_mul, Matrix.det_mul]`. Both sides reduce to the same expression. Rewrite using `[hmt, Units.val_mul, map_mul, IsUnit.unit_spec]`. Take the linear combination `((1 + d) * h2) * hx + ((matHom V g).1.det * sigR (AF D.host.F) D.sp.cm.sig (x : AE D)) * hroot`.

Rewrite using `[map_mul, hcr, mul_one]`.
-/
theorem exists_root_same_value : ∀ (D : D7) (c : (AE D)ˣ →* Circle), IsHeckeChar D c → ∃ N₀ : ℕ, ∀ (V : HSp D) {n : ℕ} (hn : V.rank = n) (g w : GA D V), w ∈ GfC V → (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (r s : Fin n), Valued.v (adAt D.host.F P (finM V hn w r s - (1 : Matrix (Fin n) (Fin n) (EF D)) r s)) ≤ WithZero.exp (-(N₀ : ℤ))) → ∀ x, IsDetRoot V g x → ∃ x₁, IsDetRoot V (g * w) x₁ ∧ c x₁ = c x := by
  intro D c hc
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hc.1
  obtain ⟨N₀, hN₀⟩ := exists_depth D.host.E (2 * N) (by omega)
  refine ⟨N₀, ?_⟩
  intro V n hn g w hw hcong x hx
  have hnorm : (Formalism.L2.Theta.mt V w).det * sigR (AF D.host.F) D.sp.cm.sig (Formalism.L2.Theta.mt V w).det = 1 := by
    have := GlobalTheory.LevelSubgroup.det_norm_one_gen (sigR (AF D.host.F) D.sp.cm.sig) (sigR (AF D.host.F) D.sp.cm.sig)
      (RingHom.id _) (fun _ => rfl) (JR (AF D.host.F) V.gram) (matHom V w).1
      (GlobalTheory.LevelSubgroup.isUnit_det_JR _ (GlobalTheory.LevelSubgroup.gram_det_ne_zero V)) w.2
    simp only [RingHom.coe_id, Matrix.map_id] at this
    exact this
  have hinf : infPart D (Formalism.L2.Theta.mt V w).det = 1 := GlobalTheory.CharRoot.infPart_det_of_mem_GfC D V w hw
  have hloc : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      Valued.v (adAt D.host.F P (toEAf D (Formalism.L2.Theta.mt V w).det) - 1) ≤ WithZero.exp (-(N₀ : ℤ)) := by
    intro P
    have h1 := det_sub_one_le Valued.v ((finM V hn w).map (adAt D.host.F P)) (WithZero.exp (-(N₀ : ℤ)))
      (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega) (fun r s => by
        have := hcong P r s
        rw [map_sub] at this
        convert this using 3
        all_goals first | rfl | (rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp))
    have h2 : ((finM V hn w).map (adAt D.host.F P)).det = adAt D.host.F P (toEAf D (Formalism.L2.Theta.mt V w).det) := by
      have e1 : (finM V hn w).det = toEAf D (Formalism.L2.Theta.mt V w).det := by
        unfold finM
        rw [Matrix.det_reindex_self, RingHom.map_det]
        rfl
      rw [← e1, RingHom.map_det]
      rfl
    rw [h2] at h1
    exact h1

  have hF2 : (2 : D.host.F) ≠ 0 := two_ne_zero
  have h2m : (2 : AE D) * algebraMap D.host.F (AE D) (2 : D.host.F)⁻¹ = 1 := by
    rw [show (2 : AE D) = algebraMap D.host.F (AE D) 2 from (map_ofNat _ 2).symm, ← map_mul,
      mul_inv_cancel₀ hF2, map_one]
  have hKne : ((2 * N : ℕ) : D.host.F) ≠ 0 := by exact_mod_cast (by omega : 2 * N ≠ 0)
  have hKm : ((2 * N : ℕ) : AE D) * algebraMap D.host.F (AE D) ((2 * N : ℕ) : D.host.F)⁻¹ = 1 := by
    have e0 : ((2 * N : ℕ) : AE D) = algebraMap D.host.F (AE D) ((2 * N : ℕ) : D.host.F) :=
      (map_natCast (algebraMap D.host.F (AE D)) (2 * N)).symm
    rw [e0, ← map_mul, mul_inv_cancel₀ hKne]
    exact map_one _
  obtain ⟨h2, h2m⟩ : ∃ h2 : AE D, (2 : AE D) * h2 = 1 := ⟨_, h2m⟩
  obtain ⟨hK, hKm⟩ : ∃ hK : AE D, ((2 * N : ℕ) : AE D) * hK = 1 := ⟨_, hKm⟩
  have hNK : (N : AE D) * hK = h2 := by
    calc (N : AE D) * hK = (N : AE D) * hK * ((2 : AE D) * h2) := by rw [h2m, mul_one]
      _ = (((2 * N : ℕ) : AE D) * hK) * h2 := by push_cast; ring
      _ = h2 := by rw [hKm, one_mul]
  have hσ2 : sigR (AF D.host.F) D.sp.cm.sig h2 = h2 := by
    have e1 : sigR (AF D.host.F) D.sp.cm.sig h2 * 2 = 1 := by
      have := congrArg (sigR (AF D.host.F) D.sp.cm.sig) h2m
      rw [map_mul, map_ofNat, map_one] at this
      rw [mul_comm]
      exact this
    calc sigR (AF D.host.F) D.sp.cm.sig h2 = sigR (AF D.host.F) D.sp.cm.sig h2 * (2 * h2) := by rw [h2m, mul_one]
      _ = (sigR (AF D.host.F) D.sp.cm.sig h2 * 2) * h2 := by ring
      _ = h2 := by rw [e1, one_mul]
  generalize hd : (Formalism.L2.Theta.mt V w).det = d at hnorm hinf hloc
  have hrt : (1 + d) * h2 = 1 + (N : AE D) * ((d - 1) * hK) := by
    linear_combination (-(d - 1)) * hNK + h2m
  have hroot : (1 + d) * h2 = d * sigR (AF D.host.F) D.sp.cm.sig ((1 + d) * h2) := by
    rw [map_mul, map_add, map_one, hσ2]
    linear_combination (-h2) * hnorm

  have hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      Valued.v (adAt D.host.F P (toEAf D ((d - 1) * hK))) < 1 ∧
      Valued.v (adAt D.host.F P (toEAf D ((1 + d) * h2))) = 1 := by
    intro P
    let φ := (adAt D.host.F P).comp (toEAf D)
    have hφK : φ hK * ((2 * N : ℕ) : P.adicCompletion D.host.E) = 1 := by
      have := congrArg φ hKm
      rw [map_mul, map_natCast, map_one] at this
      rw [mul_comm]
      exact this
    have hvK : Valued.v (φ hK) * Valued.v ((2 * N : ℕ) : P.adicCompletion D.host.E) = 1 := by
      rw [← map_mul, hφK, map_one]
    have hKpos : Valued.v (φ hK) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hvK
      exact zero_ne_one hvK
    have ht1 : Valued.v (φ ((d - 1) * hK)) < 1 := by
      rw [map_mul, map_mul, map_sub, map_one]
      calc Valued.v (φ d - 1) * Valued.v (φ hK)
          < Valued.v ((2 * N : ℕ) : P.adicCompletion D.host.E) * Valued.v (φ hK) :=
            mul_lt_mul_of_pos_right (lt_of_le_of_lt (hloc P) (hN₀ P)) (zero_lt_iff.2 hKpos)
        _ = 1 := by rw [mul_comm, hvK]
    refine ⟨ht1, ?_⟩
    change Valued.v (φ ((1 + d) * h2)) = 1
    rw [hrt, map_add, map_one, map_mul, map_natCast]
    apply Valuation.map_one_add_of_lt
    rw [map_mul]
    calc Valued.v ((N : P.adicCompletion D.host.E)) * Valued.v (φ ((d - 1) * hK))
        ≤ 1 * Valued.v (φ ((d - 1) * hK)) := mul_le_mul' (natCast_le_one _ N) le_rfl
      _ < 1 := by rw [one_mul]; exact ht1
  have hinfr : infPart D ((1 + d) * h2) = 1 := by
    have := congrArg (infPart D) h2m
    rw [map_mul, map_ofNat, map_one] at this
    rw [map_mul, map_add, map_one, hinf]
    linear_combination this
  have hru : IsUnit ((1 + d) * h2) := isUnit_of_parts D _ hinfr (fun P => (hv P).2)
  have hcr : c hru.unit = 1 := by
    refine hker hru.unit ⟨by rw [IsUnit.unit_spec]; exact hinfr,
      by rw [IsUnit.unit_spec]; exact (fin_mem_iff D _).2 (fun P => ((hv P).2).le), ?_⟩
      ⟨finPart D ((d - 1) * hK), (fin_mem_iff D _).2 (fun P => (hv P).1.le), ?_⟩
    · refine (fin_mem_iff D _).2 (fun P => ?_)
      have e1 := congrArg (fun a => adAt D.host.F P (toEAf D a)) hru.unit.inv_mul
      simp only [map_mul, map_one, IsUnit.unit_spec] at e1
      rw [← map_mul, ← map_mul] at e1
      have e2 := congrArg Valued.v e1
      rw [map_mul, map_one, map_mul, map_mul] at e2
      have h3 := (hv P).2
      rw [map_mul, map_mul] at h3
      rw [h3, mul_one] at e2
      exact e2.le
    · rw [IsUnit.unit_spec, hrt, map_add, map_one, add_sub_cancel_left, map_mul, map_natCast, nsmul_eq_mul]
  refine ⟨x * hru.unit, ?_, ?_⟩
  · unfold IsDetRoot at hx ⊢
    have hmt : (matHom V (g * w)).1.det =
        (matHom V g).1.det * d := by
      rw [← hd, map_mul, Units.val_mul, Matrix.det_mul]
      rfl
    rw [hmt, Units.val_mul, map_mul, IsUnit.unit_spec]
    linear_combination ((1 + d) * h2) * hx +
      ((matHom V g).1.det * sigR (AF D.host.F) D.sp.cm.sig (x : AE D)) * hroot
  · rw [map_mul, hcr, mul_one]

end GlobalTheory.DetRootApprox
