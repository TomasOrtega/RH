import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

noncomputable section

namespace GlobalTheory.SplitStabFrame

open GlobalTheory.StdFrames GlobalTheory.IdemSupport GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices

variable {D : D7}

set_option maxHeartbeats 400000 in

/- English proof (translation)
Take `⟨e, -, -, h1, h0⟩` from `exists_idem (D := D) {Q}`. Establish `hQ1 : cpt Q e = 1` using `h1 Q (Set.mem_singleton Q)`. Establish `hez : e * z ∈ OA D`. Use `(mem_OA_iff _).2 fun R => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Distinguish the cases in `hR : R = Q`. Rewrite using `[hR, hQ1, one_mul]`. Conclude with `hz`. Rewrite using `[h0 R (Set.notMem_singleton_iff.2 hR), zero_mul]`. Conclude with `zero_mem _`.

Establish `h2 : cpt (cP Q) (sg D (e * z)) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E (cP Q)` using `(mem_OA_iff (sg D (e * z))).1 (GlobalTheory.LevSplit.sigR_int hez) (cP Q)`. Establish `h3 : cpt (cP Q) (sg D (1 - e)) = 0` using `cpt_sg_eq_zero (by rw [cP_cP, map_sub, map_one, hQ1, sub_self])`. Establish `h4 : cpt (cP Q) (sg D e) = 1`. Rewrite `h3` using `[map_sub, map_one, map_sub, map_one, sub_eq_zero]`. Conclude with `h3.symm`.

Rewrite `h2` using `[map_mul, map_mul, h4, one_mul]`. Conclude with `h2`.
-/
theorem cpt_sg_mem {Q : Pl D.host.E} {z : Ef D}
    (hz : cpt Q z ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q) :
    cpt (cP Q) (sg D z) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E (cP Q) := by
  obtain ⟨e, -, -, h1, h0⟩ := exists_idem (D := D) {Q}
  have hQ1 : cpt Q e = 1 := h1 Q (Set.mem_singleton Q)
  have hez : e * z ∈ OA D := by
    refine (mem_OA_iff _).2 fun R => ?_
    rw [map_mul]
    by_cases hR : R = Q
    · rw [hR, hQ1, one_mul]; exact hz
    · rw [h0 R (Set.notMem_singleton_iff.2 hR), zero_mul]; exact zero_mem _
  have h2 : cpt (cP Q) (sg D (e * z)) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E (cP Q) :=
    (mem_OA_iff (sg D (e * z))).1 (GlobalTheory.LevSplit.sigR_int hez) (cP Q)
  have h3 : cpt (cP Q) (sg D (1 - e)) = 0 :=
    cpt_sg_eq_zero (by rw [cP_cP, map_sub, map_one, hQ1, sub_self])
  have h4 : cpt (cP Q) (sg D e) = 1 := by
    rw [map_sub, map_one, map_sub, map_one, sub_eq_zero] at h3
    exact h3.symm
  rw [map_mul, map_mul, h4, one_mul] at h2
  exact h2

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.mul_apply, map_sum]`. Conclude with `sum_mem fun l _ => by rw [map_mul]; exact mul_mem (hA i l) (hB l j)`.
-/
theorem int_mul {Q : Pl D.host.E} {n : ℕ} {A B : Matrix (Fin n) (Fin n) (Ef D)}
    (hA : ∀ i j, cpt Q (A i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q)
    (hB : ∀ i j, cpt Q (B i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q) :
    ∀ i j, cpt Q ((A * B) i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q := by
  intro i j
  rw [Matrix.mul_apply, map_sum]
  exact sum_mem fun l _ => by rw [map_mul]; exact mul_mem (hA i l) (hB l j)

/- English proof (translation)
Introduce `i j` and use `(mem_OA_iff _).1 (h i j) Q`.
-/
theorem int_of_OA {Q : Pl D.host.E} {n : ℕ} {A : Matrix (Fin n) (Fin n) (Ef D)} (h : ∀ i j, A i j ∈ OA D) :
    ∀ i j, cpt Q (A i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q :=
  fun i j => (mem_OA_iff _).1 (h i j) Q

/- English proof (translation)
Introduce `i j` and use `cpt_sg_mem (h j i)`.
-/
theorem int_cT {Q : Pl D.host.E} {n : ℕ} {A : Matrix (Fin n) (Fin n) (Ef D)}
    (h : ∀ i j, cpt Q (A i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q) :
    ∀ i j, cpt (cP Q) (Formalism.UG.cT (sg D) A i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E (cP Q) :=
  fun i j => cpt_sg_mem (h j i)

/- English proof (translation)
Establish `h1 : U' * (Formalism.UG.cT (sg D) Y.val * J * Y.val) = 1` using `by rw [hY, hU]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem inv_eq_of_unitary {n : ℕ} {J U' : Matrix (Fin n) (Fin n) (Ef D)} (hU : U' * J = 1) (Y : GL (Fin n) (Ef D))
    (hY : Formalism.UG.cT (sg D) Y.val * J * Y.val = J) : (Y⁻¹).val = U' * Formalism.UG.cT (sg D) Y.val * J := by
  have h1 : U' * (Formalism.UG.cT (sg D) Y.val * J * Y.val) = 1 := by rw [hY, hU]
  calc (Y⁻¹).val = (U' * (Formalism.UG.cT (sg D) Y.val * J * Y.val)) * (Y⁻¹).val := by rw [h1, Matrix.one_mul]
    _ = U' * Formalism.UG.cT (sg D) Y.val * J * (Y.val * (Y⁻¹).val) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Units.mul_inv, Matrix.mul_one]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[cT_mul']`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = J := by rw [Units.mul_inv, cT_one', Matrix.one_mul, Matrix.mul_one]`.
-/
theorem unitary_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) (Ef D)} (Y : GL (Fin n) (Ef D))
    (hY : Formalism.UG.cT (sg D) Y.val * J * Y.val = J) :
    Formalism.UG.cT (sg D) (Y⁻¹).val * J * (Y⁻¹).val = J := by
  calc Formalism.UG.cT (sg D) (Y⁻¹).val * J * (Y⁻¹).val
        = Formalism.UG.cT (sg D) (Y⁻¹).val * (Formalism.UG.cT (sg D) Y.val * J * Y.val) * (Y⁻¹).val := by rw [hY]
    _ = Formalism.UG.cT (sg D) (Y.val * (Y⁻¹).val) * J * (Y.val * (Y⁻¹).val) := by
        rw [cT_mul']; simp only [Matrix.mul_assoc]
    _ = J := by rw [Units.mul_inv, cT_one', Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Use `set A := (cpt Q).mapMatrix X.val with hAdef`. Establish `hBA : (cpt Q).mapMatrix (X⁻¹).val * A = 1` using `by rw [hAdef, ← map_mul, Units.inv_mul, map_one]`. Establish `hB : (cpt Q).mapMatrix (X⁻¹).val = A⁻¹` using `(Matrix.inv_eq_left_inv hBA).symm`. Set `A' : Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletionIntegers D.host.E Q)` to `fun i j => ⟨A i j, hint i j⟩`. Establish `hA' : (HeightOneSpectrum.adicCompletionIntegers D.host.E Q).subtype.mapMatrix A' = A` using `rfl`.

Establish `hdetA : A.det = cpt Q X.val.det` using `(RingHom.map_det _ _).symm`. Introduce `i j`. Establish `e : cpt Q ((X⁻¹).val i j) = ((cpt Q).mapMatrix (X⁻¹).val) i j` using `rfl`. Rewrite using `[e, hB, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]`. Use `mul_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[hdetA, Ring.inverse_eq_inv', HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hdet, inv_one]`. Rewrite using `[← hA', ← RingHom.map_adjugate]`. Conclude with `(A'.adjugate i j).2`.
-/
theorem inv_int_at {Q : Pl D.host.E} {n : ℕ} (X : GL (Fin n) (Ef D))
    (hint : ∀ i j, cpt Q (X.val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q)
    (hdet : Valued.v (cpt Q X.val.det) = 1) :
    ∀ i j, cpt Q ((X⁻¹).val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q := by
  set A := (cpt Q).mapMatrix X.val with hAdef
  have hBA : (cpt Q).mapMatrix (X⁻¹).val * A = 1 := by rw [hAdef, ← map_mul, Units.inv_mul, map_one]
  have hB : (cpt Q).mapMatrix (X⁻¹).val = A⁻¹ := (Matrix.inv_eq_left_inv hBA).symm
  let A' : Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletionIntegers D.host.E Q) :=
    fun i j => ⟨A i j, hint i j⟩
  have hA' : (HeightOneSpectrum.adicCompletionIntegers D.host.E Q).subtype.mapMatrix A' = A := rfl
  have hdetA : A.det = cpt Q X.val.det := (RingHom.map_det _ _).symm
  intro i j
  have e : cpt Q ((X⁻¹).val i j) = ((cpt Q).mapMatrix (X⁻¹).val) i j := rfl
  rw [e, hB, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
  refine mul_mem ?_ ?_
  · rw [hdetA, Ring.inverse_eq_inv', HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hdet, inv_one]
  · rw [← hA', ← RingHom.map_adjugate]
    exact (A'.adjugate i j).2

/- English proof (translation)
Establish `hXi` using `unitary_inv X hX`. Establish `intPi` using `inv_int_at X hint hdet`. Establish `key : ∀ Y : GL (Fin n) (Ef D), Formalism.UG.cT (sg D) Y.val * J * Y.val = J → (∀ i j, cpt P (Y.val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E P) → ∀ i j, cpt (cP P) ((Y⁻¹).val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E (cP P)`. Introduce `Y hY hYP`. Rewrite using `[inv_eq_of_unitary hUJ Y hY]`.

Conclude with `int_mul (int_mul (int_of_OA hU') (int_cT hYP)) (int_of_OA hJ)`. Establish `hall : ∀ Q : Pl D.host.E, (∀ i j, cpt Q (X.val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q) ∧ ∀ i j, cpt Q ((X⁻¹).val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q`. Introduce `Q`. Distinguish the cases in `h1 : Q = P`. Rewrite using `[h1]`.

Conclude with `⟨hint, intPi⟩`. Distinguish the cases in `h2 : Q = cP P`. Rewrite using `[h2]`. Use `⟨?_, key X hX hint⟩` and prove the remaining obligations. Use `key X⁻¹ hXi intPi` as an intermediate fact.

Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis. Establish `h3` using `hoff Q h1 h2`. Establish `h4 : (cpt Q).mapMatrix (X⁻¹).val = 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h3, Matrix.mul_one]`.

Use `_ = 1 := by rw [← map_mul, Units.inv_mul, map_one]`. Establish `one_int : ∀ i j, (1 : Matrix (Fin n) (Fin n) (Q.adicCompletion D.host.E)) i j ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q`. Introduce `i j`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`.

Conclude with `one_mem _`. Conclude with `zero_mem _`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Establish `: cpt Q (X.val i j) = (1 : Matrix (Fin n) (Fin n) _) i j` using `congrFun (congrFun h3 i) j`. Rewrite using `[this]`.

Conclude with `one_int i j`. Establish `: cpt Q ((X⁻¹).val i j) = (1 : Matrix (Fin n) (Fin n) _) i j` using `congrFun (congrFun h4 i) j`. Rewrite using `[this]`. Conclude with `one_int i j`. Conclude with `⟨fun i j => (mem_OA_iff _).2 fun Q => (hall Q).1 i j, fun i j => (mem_OA_iff _).2 fun Q => (hall Q).2 i j⟩`.
-/
theorem int_of_split {n : ℕ} (J U' : Matrix (Fin n) (Fin n) (Ef D)) (hJ : ∀ i j, J i j ∈ OA D)
    (hU' : ∀ i j, U' i j ∈ OA D) (hUJ : U' * J = 1) (X : GL (Fin n) (Ef D))
    (hX : Formalism.UG.cT (sg D) X.val * J * X.val = J) (P : Pl D.host.E)
    (hint : ∀ i j, cpt P (X.val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E P)
    (hdet : Valued.v (cpt P X.val.det) = 1)
    (hoff : ∀ Q, Q ≠ P → Q ≠ cP P → (cpt Q).mapMatrix X.val = 1) :
    (∀ i j, X.val i j ∈ OA D) ∧ ∀ i j, (X⁻¹).val i j ∈ OA D := by
  have hXi := unitary_inv X hX
  have intPi := inv_int_at X hint hdet
  have key : ∀ Y : GL (Fin n) (Ef D), Formalism.UG.cT (sg D) Y.val * J * Y.val = J →
      (∀ i j, cpt P (Y.val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E P) →
      ∀ i j, cpt (cP P) ((Y⁻¹).val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E (cP P) := by
    intro Y hY hYP
    rw [inv_eq_of_unitary hUJ Y hY]
    exact int_mul (int_mul (int_of_OA hU') (int_cT hYP)) (int_of_OA hJ)
  have hall : ∀ Q : Pl D.host.E,
      (∀ i j, cpt Q (X.val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q) ∧
        ∀ i j, cpt Q ((X⁻¹).val i j) ∈ HeightOneSpectrum.adicCompletionIntegers D.host.E Q := by
    intro Q
    by_cases h1 : Q = P
    · rw [h1]; exact ⟨hint, intPi⟩
    by_cases h2 : Q = cP P
    · rw [h2]
      refine ⟨?_, key X hX hint⟩
      have := key X⁻¹ hXi intPi
      rwa [inv_inv] at this
    · have h3 := hoff Q h1 h2
      have h4 : (cpt Q).mapMatrix (X⁻¹).val = 1 :=
        calc (cpt Q).mapMatrix (X⁻¹).val = (cpt Q).mapMatrix (X⁻¹).val * (cpt Q).mapMatrix X.val := by
              rw [h3, Matrix.mul_one]
          _ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      have one_int : ∀ i j, (1 : Matrix (Fin n) (Fin n) (Q.adicCompletion D.host.E)) i j ∈
          HeightOneSpectrum.adicCompletionIntegers D.host.E Q := by
        intro i j
        rw [Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · have : cpt Q (X.val i j) = (1 : Matrix (Fin n) (Fin n) _) i j := congrFun (congrFun h3 i) j
        rw [this]; exact one_int i j
      · have : cpt Q ((X⁻¹).val i j) = (1 : Matrix (Fin n) (Fin n) _) i j := congrFun (congrFun h4 i) j
        rw [this]; exact one_int i j
  exact ⟨fun i j => (mem_OA_iff _).2 fun Q => (hall Q).1 i j,
    fun i j => (mem_OA_iff _).2 fun Q => (hall Q).2 i j⟩

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `D W β Λ hSD e f P hP hf _ k hS hint hdet`. Take `⟨hJ, U', hU', hUJ⟩` from `unimod_of_isSD hSD`. Establish `hg : Formalism.UG.cT (sg D) (finE W k).val * ratM W.gram * (finE W k).val = ratM W.gram` using `GlobalTheory.LevSplit.finE_mem_UA W k`. Use `set g := finE W k with hgdef`. Set `X : GL (Fin W.rank) (Ef D)` to `β⁻¹ * g * β`.

Establish `hXv : X.val = (β⁻¹).val * g.val * β.val` using `rfl`. Establish `hX : Formalism.UG.cT (sg D) X.val * gramOf W β * X.val = gramOf W β`. Establish `e2 : Formalism.UG.cT (sg D) (β⁻¹).val * Formalism.UG.cT (sg D) β.val = 1`. Rewrite using `[← cT_mul', Units.mul_inv, cT_one']`. Establish `e3 : β.val * (β⁻¹).val = 1` using `Units.mul_inv β`.

Use `show Formalism.UG.cT (sg D) X.val * (Formalism.UG.cT (sg D) β.val * ratM W.gram * β.val) * X.val = Formalism.UG.cT (sg D) β.val * ratM W.gram * β.val`. Rewrite using `[hXv, cT_mul', cT_mul']`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e2, e3]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`.

Use `_ = _ := by rw [hg]`. Establish `hf0 : ∀ Q, Q ≠ P → Q ≠ cP P → cpt Q (toEAf D f) = 0`. Introduce `Q h1 h2`. Establish `h3 : cP Q ≠ P` using `fun h => h2 (by rw [← h, cP_cP])`. Rewrite using `[hf, RingHom.map_add (toEAf D), toEAf_cA, RingHom.map_add (cpt Q), (cpt_of_isIdemAt hP).2 Q h1, cpt_sg_eq_zero ((cpt_of_isIdemAt hP).2 _ h3), add_zero]`.

Establish `hM : ∀ Q, Q ≠ P → Q ≠ cP P → (cpt Q).mapMatrix g.val = 1`. Introduce `Q h1 h2`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Establish `h3` using `congrArg (fun z => cpt Q (toEAf D z)) (hS i j)`. Rewrite `h3` using `[RingHom.map_mul (toEAf D), RingHom.map_mul (cpt Q), hf0 Q h1 h2, zero_mul, Matrix.sub_apply, RingHom.map_sub (toEAf D), RingHom.map_sub (cpt Q)]`.

Rewrite `h3` using `[eq_comm, sub_eq_zero]`. Express the relevant statement in the definitionally equal form `cpt Q (toEAf D (Formalism.L2.Theta.mt W k i j)) = (1 : Matrix (Fin W.rank) (Fin W.rank) _) i j`. Rewrite using `[h3, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hoff : ∀ Q, Q ≠ P → Q ≠ cP P → (cpt Q).mapMatrix X.val = 1`.

Introduce `Q h1 h2`. Rewrite using `[hXv, map_mul, map_mul, hM Q h1 h2, Matrix.mul_one, ← map_mul, Units.inv_mul, map_one]`. Take `⟨h1, h2⟩` from `int_of_split (gramOf W β) U' hJ hU' hUJ X hX P hint hdet hoff`. Set `Mi : Matrix (Fin W.rank) (Fin W.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)` to `fun i j => ⟨_, h1 i j⟩`. Set `Mi' : Matrix (Fin W.rank) (Fin W.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)` to `fun i j => ⟨_, h2 i j⟩`.

Establish `inj : Function.Injective ((Formalism.L2.Herm.intAf D.host.F D.host.E).subtype.mapMatrix (m` using `Fin W.rank)) := by`. Introduce `A B h`. Use extensionality with `i j`. Conclude with `congrFun (congrFun h i) j`. Establish `p1 : Mi * Mi' = 1` using `inj (by rw [map_mul, map_one]; exact Units.mul_inv X)`.

Establish `p2 : Mi' * Mi = 1` using `inj (by rw [map_mul, map_one]; exact Units.inv_mul X)`. Use `⟨⟨Mi, Mi', p1, p2⟩, ?_⟩` and prove the remaining obligations. Establish `hX' : intGL D.host.F D.host.E W.rank ⟨Mi, Mi', p1, p2⟩ = X` using `Units.ext rfl`. Use `show β * intGL D.host.F D.host.E W.rank ⟨Mi, Mi', p1, p2⟩ * β⁻¹ = g`. Rewrite using `[hX']`.

Use `show β * (β⁻¹ * g * β) * β⁻¹ = g`. Rewrite using `[mul_assoc, mul_assoc, mul_inv_cancel, mul_one, ← mul_assoc, mul_inv_cancel, one_mul]`.
-/
theorem finE_mem_St_of_split : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSDFrame W β Λ 1 → ∀ (e f : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → f = e + cA D e → GlobalTheory.IdemSupport.cP P ≠ P → ∀ k : GA D W, SuppF W f k → (∀ a b, GlobalTheory.StdFrames.cpt P ((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) a b) ∈ P.adicCompletionIntegers D.host.E) → Valued.v (GlobalTheory.StdFrames.cpt P ((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D))).det) = 1 → finE W k ∈ St β := by
  intro D W β Λ hSD e f P hP hf _ k hS hint hdet
  obtain ⟨hJ, U', hU', hUJ⟩ := unimod_of_isSD hSD
  have hg : Formalism.UG.cT (sg D) (finE W k).val * ratM W.gram * (finE W k).val = ratM W.gram :=
    GlobalTheory.LevSplit.finE_mem_UA W k
  set g := finE W k with hgdef
  let X : GL (Fin W.rank) (Ef D) := β⁻¹ * g * β
  have hXv : X.val = (β⁻¹).val * g.val * β.val := rfl
  have hX : Formalism.UG.cT (sg D) X.val * gramOf W β * X.val = gramOf W β := by
    have e2 : Formalism.UG.cT (sg D) (β⁻¹).val * Formalism.UG.cT (sg D) β.val = 1 := by
      rw [← cT_mul', Units.mul_inv, cT_one']
    have e3 : β.val * (β⁻¹).val = 1 := Units.mul_inv β
    show Formalism.UG.cT (sg D) X.val * (Formalism.UG.cT (sg D) β.val * ratM W.gram * β.val) * X.val =
      Formalism.UG.cT (sg D) β.val * ratM W.gram * β.val
    rw [hXv, cT_mul', cT_mul']
    calc Formalism.UG.cT (sg D) β.val * (Formalism.UG.cT (sg D) g.val * Formalism.UG.cT (sg D) (β⁻¹).val) *
          (Formalism.UG.cT (sg D) β.val * ratM W.gram * β.val) * ((β⁻¹).val * g.val * β.val)
        = Formalism.UG.cT (sg D) β.val * Formalism.UG.cT (sg D) g.val *
          (Formalism.UG.cT (sg D) (β⁻¹).val * Formalism.UG.cT (sg D) β.val) * ratM W.gram * (β.val * (β⁻¹).val) *
          g.val * β.val := by simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT (sg D) β.val * (Formalism.UG.cT (sg D) g.val * ratM W.gram * g.val) * β.val := by
          rw [e2, e3]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hg]
  have hf0 : ∀ Q, Q ≠ P → Q ≠ cP P → cpt Q (toEAf D f) = 0 := by
    intro Q h1 h2
    have h3 : cP Q ≠ P := fun h => h2 (by rw [← h, cP_cP])
    rw [hf, RingHom.map_add (toEAf D), toEAf_cA, RingHom.map_add (cpt Q), (cpt_of_isIdemAt hP).2 Q h1,
      cpt_sg_eq_zero ((cpt_of_isIdemAt hP).2 _ h3), add_zero]
  have hM : ∀ Q, Q ≠ P → Q ≠ cP P → (cpt Q).mapMatrix g.val = 1 := by
    intro Q h1 h2
    refine Matrix.ext fun i j => ?_
    have h3 := congrArg (fun z => cpt Q (toEAf D z)) (hS i j)
    rw [RingHom.map_mul (toEAf D), RingHom.map_mul (cpt Q), hf0 Q h1 h2, zero_mul, Matrix.sub_apply,
      RingHom.map_sub (toEAf D), RingHom.map_sub (cpt Q)] at h3
    rw [eq_comm, sub_eq_zero] at h3
    change cpt Q (toEAf D (Formalism.L2.Theta.mt W k i j)) = (1 : Matrix (Fin W.rank) (Fin W.rank) _) i j
    rw [h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hoff : ∀ Q, Q ≠ P → Q ≠ cP P → (cpt Q).mapMatrix X.val = 1 := by
    intro Q h1 h2
    rw [hXv, map_mul, map_mul, hM Q h1 h2, Matrix.mul_one, ← map_mul, Units.inv_mul, map_one]
  obtain ⟨h1, h2⟩ := int_of_split (gramOf W β) U' hJ hU' hUJ X hX P hint hdet hoff
  let Mi : Matrix (Fin W.rank) (Fin W.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) := fun i j => ⟨_, h1 i j⟩
  let Mi' : Matrix (Fin W.rank) (Fin W.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) := fun i j => ⟨_, h2 i j⟩
  have inj : Function.Injective ((Formalism.L2.Herm.intAf D.host.F D.host.E).subtype.mapMatrix (m := Fin W.rank)) := by
    intro A B h
    ext i j
    exact congrFun (congrFun h i) j
  have p1 : Mi * Mi' = 1 := inj (by rw [map_mul, map_one]; exact Units.mul_inv X)
  have p2 : Mi' * Mi = 1 := inj (by rw [map_mul, map_one]; exact Units.inv_mul X)
  refine ⟨⟨Mi, Mi', p1, p2⟩, ?_⟩
  have hX' : intGL D.host.F D.host.E W.rank ⟨Mi, Mi', p1, p2⟩ = X := Units.ext rfl
  show β * intGL D.host.F D.host.E W.rank ⟨Mi, Mi', p1, p2⟩ * β⁻¹ = g
  rw [hX']
  show β * (β⁻¹ * g * β) * β⁻¹ = g
  rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one, ← mul_assoc, mul_inv_cancel, one_mul]

end GlobalTheory.SplitStabFrame
