import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaLiftIdempotentForm

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdRead.IntLift

open GlobalTheory.BotClassDict (finQ)
open GlobalTheory.UnitaryMove (ct blockUnit)

/- English proof (translation)
Set `M : Matrix (Fin n) (Fin n) O` to `Matrix.of fun i j => ⟨N i j, hN i j⟩`. Establish `e : N = O.subtype.mapMatrix M` using `rfl`. Rewrite using `[e, ← RingHom.map_adjugate]`. Conclude with `(M.adjugate i j).2`.
-/
theorem adjugate_mem {A : Type} [CommRing A] (O : Subring A) {n : ℕ} (N : Matrix (Fin n) (Fin n) A)
    (hN : ∀ i j, N i j ∈ O) (i j : Fin n) : N.adjugate i j ∈ O := by
  let M : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨N i j, hN i j⟩
  have e : N = O.subtype.mapMatrix M := rfl
  rw [e, ← RingHom.map_adjugate]
  exact (M.adjugate i j).2

/- English proof (translation)
Establish `hP : ∀ i j, (w • N.adjugate) i j ∈ O` using `fun i j => mul_mem hw (adjugate_mem O N hN i j)`. Establish `hPQ : ε • ((w • N.adjugate) * N) = ε • (1 : Matrix (Fin n) (Fin n) A)`. Rewrite using `[Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, smul_smul, mul_assoc, hd]`. Establish `hQP : ε • (N * (w • N.adjugate)) = ε • (1 : Matrix (Fin n) (Fin n) A)`. Rewrite using `[Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, smul_smul, mul_assoc, hd]`.

Generalize the expression as in `w • N.adjugate = P at hP hPQ hQP`. Take `⟨a, b, d⟩` from `blockUnit c hc h1 h2 P N hPQ hQP`. Establish `hf : 1 - ε - c ε ∈ O` using `sub_mem (sub_mem (one_mem _) hε) (hO _ hε)`. Establish `hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) A) i j ∈ O` using `fun i j => by`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h]`.

Use `⟨_, _, a, b, d, fun i j => ⟨?_, ?_⟩, fun i j => ?_⟩` and prove the remaining obligations. Conclude with `add_mem (add_mem (mul_mem hf (hone i j)) (mul_mem hε (hP i j))) (mul_mem (hO _ hε) (hO _ (hN j i)))`. Conclude with `add_mem (add_mem (mul_mem hf (hone i j)) (mul_mem hε (hN i j))) (mul_mem (hO _ hε) (hO _ (hP j i)))`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Take the linear combination `(N i j - (1 : Matrix (Fin n) (Fin n) A) i j) * h1 + (ct c P i j - (1 : Matrix (Fin n) (Fin n) A) i j) * h2`.
-/
theorem exists_block {A : Type} [CommRing A] (c : A →+* A) (hc : ∀ a, c (c a) = a) (O : Subring A) (hO : ∀ a ∈ O, c a ∈ O)
    {ε w : A} (h1 : ε * ε = ε) (h2 : ε * c ε = 0) (hε : ε ∈ O) (hw : w ∈ O) {n : ℕ} (N : Matrix (Fin n) (Fin n) A)
    (hN : ∀ i j, N i j ∈ O) (hd : ε * (w * N.det) = ε) :
    ∃ K K' : Matrix (Fin n) (Fin n) A, K * K' = 1 ∧ K' * K = 1 ∧ ct c K = K' ∧ (∀ i j, K i j ∈ O ∧ K' i j ∈ O) ∧
      ∀ i j, ε * K' i j = ε * N i j := by
  have hP : ∀ i j, (w • N.adjugate) i j ∈ O := fun i j => mul_mem hw (adjugate_mem O N hN i j)
  have hPQ : ε • ((w • N.adjugate) * N) = ε • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, smul_smul, mul_assoc, hd]
  have hQP : ε • (N * (w • N.adjugate)) = ε • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, smul_smul, mul_assoc, hd]
  generalize w • N.adjugate = P at hP hPQ hQP
  obtain ⟨a, b, d⟩ := blockUnit c hc h1 h2 P N hPQ hQP
  have hf : 1 - ε - c ε ∈ O := sub_mem (sub_mem (one_mem _) hε) (hO _ hε)
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) A) i j ∈ O := fun i j => by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  refine ⟨_, _, a, b, d, fun i j => ⟨?_, ?_⟩, fun i j => ?_⟩
  · exact add_mem (add_mem (mul_mem hf (hone i j)) (mul_mem hε (hP i j))) (mul_mem (hO _ hε) (hO _ (hN j i)))
  · exact add_mem (add_mem (mul_mem hf (hone i j)) (mul_mem hε (hN i j))) (mul_mem (hO _ hε) (hO _ (hP j i)))
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (N i j - (1 : Matrix (Fin n) (Fin n) A) i j) * h1 +
      (ct c P i j - (1 : Matrix (Fin n) (Fin n) A) i j) * h2

/- English proof (translation)
The claim follows from `(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective.comp (GlobalTheory.BotFormula.toAfE D).injective`.
-/
theorem toE_injective (D : D7) : Function.Injective (toE D) :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective.comp (GlobalTheory.BotFormula.toAfE D).injective

/- English proof (translation)
Introduce `D e SS he a N hN x hx`. Take `⟨-, hx1, hx2⟩` from `hx`. Establish `hdet : (N.map (toE D)).det = toE D N.det` using `(RingHom.map_det (toE D) _).symm`. Establish `h1` using `CharVal.eps_idem he`. Establish `hxe : finQ D (x : AE D) = 1 - finQ D e + finQ D e * N.det` using `toE_injective D (by`.

Rewrite using `[CharVal.toE_finQ, hx1, hdet, RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_one, CharVal.toE_finQ])`. Establish `hxx : finQ D (x : AE D) * finQ D ((x⁻¹ : (AE D)ˣ) : AE D) = 1`. Rewrite using `[← RingHom.map_mul, Units.mul_inv, RingHom.map_one]`. Establish `hd : finQ D e * (finQ D ((x⁻¹ : (AE D)ˣ) : AE D) * N.det) = finQ D e`. Rewrite `hxx` using `[hxe]`.

Take the linear combination `finQ D e * hxx + (finQ D ((x⁻¹ : (AE D)ˣ) : AE D) * (1 - N.det)) * h1`. Take `⟨K, K', a1, a2, a3, a4, a5⟩` from `exists_block (Formalism.MainNotions.StandardLatticesGL3.sgA D) (GlobalTheory.NormSum.VacMove.sgA_sgA D) (OhE D) (fun _ h => GlobalTheory.NormSum.VacMove.sgA_mem D h) h1 (CharVal.eps_conj he) (CharVal.eps_int he) (CharVal.finQ_int hx2) N hN hd`. Set `u : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)` to `⟨K, K', a1, a2⟩`. Establish `hu : u ∈ Formalism.MainNotions.StandardLatticesGL3.GA D a`. Express the relevant statement in the definitionally equal form `Formalism.UG.cT _ K * _ * K = _`.

Rewrite using `[Matrix.map_one _ (map_zero _) (map_one _), mul_one]`. Conclude with `(congrArg (· * K) a3).trans a2`. Conclude with `⟨⟨u, hu⟩, (GlobalTheory.NormSum.mem_intG _).2 a4, a5⟩`.
-/
theorem exists_lift : ∀ {D : D7} (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS →
  ∀ {a : ℕ} (N : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)), (∀ i j, N i j ∈ OhE D) →
  ∀ x : (AE D)ˣ, IsUnitDet e (N.map (toE D)) x → ∃ k : Formalism.MainNotions.StandardLatticesGL3.GA D a, k ∈ intG D a ∧
    ∀ i j, GlobalTheory.BotClassDict.finQ D e * (((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
      Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j = GlobalTheory.BotClassDict.finQ D e * N i j := by
  intro D e SS he a N hN x hx
  obtain ⟨-, hx1, hx2⟩ := hx
  have hdet : (N.map (toE D)).det = toE D N.det := (RingHom.map_det (toE D) _).symm
  have h1 := CharVal.eps_idem he
  have hxe : finQ D (x : AE D) = 1 - finQ D e + finQ D e * N.det := toE_injective D (by
    rw [CharVal.toE_finQ, hx1, hdet, RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_one, CharVal.toE_finQ])
  have hxx : finQ D (x : AE D) * finQ D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one]
  have hd : finQ D e * (finQ D ((x⁻¹ : (AE D)ˣ) : AE D) * N.det) = finQ D e := by
    rw [hxe] at hxx
    linear_combination finQ D e * hxx + (finQ D ((x⁻¹ : (AE D)ˣ) : AE D) * (1 - N.det)) * h1
  obtain ⟨K, K', a1, a2, a3, a4, a5⟩ := exists_block (Formalism.MainNotions.StandardLatticesGL3.sgA D) (GlobalTheory.NormSum.VacMove.sgA_sgA D) (OhE D)
    (fun _ h => GlobalTheory.NormSum.VacMove.sgA_mem D h) h1 (CharVal.eps_conj he) (CharVal.eps_int he) (CharVal.finQ_int hx2) N hN hd
  let u : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ⟨K, K', a1, a2⟩
  have hu : u ∈ Formalism.MainNotions.StandardLatticesGL3.GA D a := by
    change Formalism.UG.cT _ K * _ * K = _
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one]
    exact (congrArg (· * K) a3).trans a2
  exact ⟨⟨u, hu⟩, (GlobalTheory.NormSum.mem_intG _).2 a4, a5⟩

end GlobalTheory.StdRead.IntLift

end
