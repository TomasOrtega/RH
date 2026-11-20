import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IntegrableOnOfPeriodic
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.EqZeroOfMemFactorial
import Formalism.LocalToGlobal.IndefiniteReal.PHeisThC
import ReciprocityTheory.AdeleApproximation.AdeleIntA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.IsOpenIntSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.Imports
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.IntInterAlt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Topology NumberField.InfinitePlace.Completion
open scoped TensorProduct ComplexConjugate

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pairA_add (a a' : Ainf F) (b b' : Af F) : pairA F (a + a') (b + b') = pairA F a b + pairA F a' b' := rfl

/- English proof (translation)
Rewrite using `[← pairA_add, add_zero, zero_add]`.
-/
theorem pairA_split (a : Ainf F) (b : Af F) : pairA F a b = pairA F a 0 + pairA F 0 b := by
  rw [← pairA_add, add_zero, zero_add]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem algebraMap_AF (q : F) :
    algebraMap F (AF F) q = pairA F (algebraMap F (Ainf F) q) (algebraMap F (Af F) q) := rfl

/- English proof (translation)
Establish `h : IsIntegral ℤ (Algebra.trace ℚ F (y : F))` using `Algebra.isIntegral_trace y.isIntegral_coe`. Take `⟨z, hz⟩` from `IsIntegrallyClosed.isIntegral_iff.mp h`. Conclude with `⟨z, by rw [← hz]; simp⟩`.
-/
theorem trace_int (y : 𝓞 F) : ∃ z : ℤ, Algebra.trace ℚ F (y : F) = z := by
  have h : IsIntegral ℤ (Algebra.trace ℚ F (y : F)) := Algebra.isIntegral_trace y.isIntegral_coe
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨z, by rw [← hz]; simp⟩

/- English proof (translation)
Simplify using `only [invDiff, Set.mem_setOf_eq, one_mul]`. Conclude with `trace_int`.
-/
theorem one_mem_invDiff : (1 : F) ∈ invDiff F := by
  simp only [invDiff, Set.mem_setOf_eq, one_mul]
  exact trace_int

/- English proof (translation)
Rewrite using `[show (2 * Real.pi * Complex.I * n : ℂ) = n * (2 * Real.pi * Complex.I) by ring]`. Conclude with `Complex.exp_int_mul_two_pi_mul_I n`.
-/
theorem exp_two_pi_int (n : ℤ) : Complex.exp (2 * Real.pi * Complex.I * n) = 1 := by
  rw [show (2 * Real.pi * Complex.I * n : ℂ) = n * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

/- English proof (translation)
Use `haveI : DiscreteTopology (X ⧸ H) := QuotientAddGroup.discreteTopology hH`. Establish `hSfin : ((fun y : X => (y : X ⧸ H)) '' K).Finite` using `(hK.image QuotientAddGroup.continuous_mk).finite_of_discrete`. Establish `hord : ∀ y ∈ K, IsOfFinAddOrder (y : X ⧸ H)`. Introduce `y hy`. Take `⟨a, b, hab, he⟩` from `Set.Finite.exists_lt_map_eq_of_forall_mem (f := fun n : ℕ => ((n • y : X) : X ⧸ H)) (fun n => Set.mem_image_of_mem _ (hKs y hy n)) hSfin`.

Take `⟨c, rfl⟩` from `Nat.exists_eq_add_of_lt hab`. Use `isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨c + 1, Nat.succ_pos c, ?_⟩` and prove the remaining obligations. Establish `h2 : (a + (c + 1)) • (y : X ⧸ H) = a • (y : X ⧸ H)`. Rewrite using `[← Nat.add_assoc, ← QuotientAddGroup.mk_nsmul, ← QuotientAddGroup.mk_nsmul]`. Conclude with `he.symm`.

Rewrite `h2` using `[add_nsmul]`. Simplify using `using h2`. Use `⟨∏ q ∈ hSfin.toFinset, addOrderOf q, ?_, ?_⟩` and prove the remaining obligations. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `q hq`.

Take `⟨y, hy, rfl⟩` from `hSfin.mem_toFinset.mp hq`. Conclude with `(hord y hy).addOrderOf_pos`. Introduce `y hy`. Establish `hmem : (y : X ⧸ H) ∈ hSfin.toFinset` using `hSfin.mem_toFinset.mpr ⟨y, hy, rfl⟩`. Establish `h0 : (∏ q ∈ hSfin.toFinset, addOrderOf q) • (y : X ⧸ H) = 0` using `addOrderOf_dvd_iff_nsmul_eq_zero.mp (Finset.dvd_prod_of_mem (fun q => addOrderOf q) hmem)`.

Rewrite `h0` using `[← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]`. Conclude with `h0`.
-/
theorem exists_nsmul_mem_cpt {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (K : Set X) (hK : IsCompact K) (hKs : ∀ y ∈ K, ∀ n : ℕ, n • y ∈ K) (H : AddSubgroup X)
    (hH : IsOpen (H : Set X)) : ∃ m : ℕ, 0 < m ∧ ∀ y ∈ K, m • y ∈ H := by
  classical
  haveI : DiscreteTopology (X ⧸ H) := QuotientAddGroup.discreteTopology hH
  have hSfin : ((fun y : X => (y : X ⧸ H)) '' K).Finite :=
    (hK.image QuotientAddGroup.continuous_mk).finite_of_discrete
  have hord : ∀ y ∈ K, IsOfFinAddOrder (y : X ⧸ H) := by
    intro y hy
    obtain ⟨a, b, hab, he⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
      (f := fun n : ℕ => ((n • y : X) : X ⧸ H)) (fun n => Set.mem_image_of_mem _ (hKs y hy n)) hSfin
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hab
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨c + 1, Nat.succ_pos c, ?_⟩
    have h2 : (a + (c + 1)) • (y : X ⧸ H) = a • (y : X ⧸ H) := by
      rw [← Nat.add_assoc, ← QuotientAddGroup.mk_nsmul, ← QuotientAddGroup.mk_nsmul]
      exact he.symm
    rw [add_nsmul] at h2
    simpa using h2
  refine ⟨∏ q ∈ hSfin.toFinset, addOrderOf q, ?_, ?_⟩
  · apply Finset.prod_pos
    intro q hq
    obtain ⟨y, hy, rfl⟩ := hSfin.mem_toFinset.mp hq
    exact (hord y hy).addOrderOf_pos
  · intro y hy
    have hmem : (y : X ⧸ H) ∈ hSfin.toFinset := hSfin.mem_toFinset.mpr ⟨y, hy, rfl⟩
    have h0 : (∏ q ∈ hSfin.toFinset, addOrderOf q) • (y : X ⧸ H) = 0 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mp (Finset.dvd_prod_of_mem (fun q => addOrderOf q) hmem)
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at h0
    exact h0

end Gen

section Psi

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

/- English proof (translation)
Establish `hb : Function.Bijective (fun τ => Eqv.fEmb D τ)`. Prove the components needed by the constructor for the conclusion. Introduce `τ τ' h`. Simplify using `only at h`. Establish `h' : Eqv.plW D τ = Eqv.plW D τ'` using `by show InfinitePlace.mk (Eqv.fEmb D τ) = InfinitePlace.mk (Eqv.fEmb D τ')`.

Rewrite using `[h]`. Rewrite `h'` using `[Eqv.plW_eq_tauPl, Eqv.plW_eq_tauPl]`. Conclude with `(Formalism.L2.Host.tauPl D).injective h'`. Introduce `φ`. Use `⟨(Formalism.L2.Host.tauPl D).symm (InfinitePlace.mk φ), ?_⟩` and prove the remaining obligations.

Establish `h1` using `Eqv.plW_embedding D ((Formalism.L2.Host.tauPl D).symm (InfinitePlace.mk φ))`. Rewrite `h1` using `[Eqv.plW_symm]`. Establish `hr` using `Eqv.fEmb_isReal D ((Formalism.L2.Host.tauPl D).symm (InfinitePlace.mk φ))`. Use `show Eqv.fEmb D _ = φ`. Break down `InfinitePlace.embedding_mk_eq φ with h2 | h2` into its components or cases.

Rewrite using `[← h1, h2]`. Rewrite `hr` using `[← h1]`. Rewrite using `[← h1, h2]`. Rewrite `hr` using `[h2]`. Conclude with `ComplexEmbedding.isReal_conjugate_iff.mp hr`.

Establish `htr` using `trace_eq_sum_embeddings (K := ℚ) (L := D.host.F) (E := ℂ) (x := x)`. Rewrite using `[show ((Algebra.trace ℚ D.host.F x : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ D.host.F x) from (eq_ratCast _ _).symm, htr]`. Set `e : (D.host.F →+* ℂ) ≃ (D.host.F →ₐ[ℚ] ℂ)` to `RingHom.equivRatAlgHom D.host.F ℂ`. Conclude with `Fintype.sum_bijective (e ∘ fun τ => Eqv.fEmb D τ) (e.bijective.comp hb) _ _ (fun τ => rfl)`.
-/
theorem sum_fEmb (x : D.host.F) : ∑ τ : D.what₂.Tau, Eqv.fEmb D τ x = ((Algebra.trace ℚ D.host.F x : ℚ) : ℂ) := by
  classical
  have hb : Function.Bijective (fun τ => Eqv.fEmb D τ) := by
    constructor
    · intro τ τ' h
      simp only at h
      have h' : Eqv.plW D τ = Eqv.plW D τ' := by
        show InfinitePlace.mk (Eqv.fEmb D τ) = InfinitePlace.mk (Eqv.fEmb D τ')
        rw [h]
      rw [Eqv.plW_eq_tauPl, Eqv.plW_eq_tauPl] at h'
      exact (Formalism.L2.Host.tauPl D).injective h'
    · intro φ
      refine ⟨(Formalism.L2.Host.tauPl D).symm (InfinitePlace.mk φ), ?_⟩
      have h1 := Eqv.plW_embedding D ((Formalism.L2.Host.tauPl D).symm (InfinitePlace.mk φ))
      rw [Eqv.plW_symm] at h1
      have hr := Eqv.fEmb_isReal D ((Formalism.L2.Host.tauPl D).symm (InfinitePlace.mk φ))
      show Eqv.fEmb D _ = φ
      rcases InfinitePlace.embedding_mk_eq φ with h2 | h2
      · rw [← h1, h2]
      · rw [← h1] at hr
        rw [← h1, h2]
        rw [h2] at hr
        exact ComplexEmbedding.isReal_conjugate_iff.mp hr
  have htr := trace_eq_sum_embeddings (K := ℚ) (L := D.host.F) (E := ℂ) (x := x)
  rw [show ((Algebra.trace ℚ D.host.F x : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ D.host.F x) from
    (eq_ratCast _ _).symm, htr]
  let e : (D.host.F →+* ℂ) ≃ (D.host.F →ₐ[ℚ] ℂ) := RingHom.equivRatAlgHom D.host.F ℂ
  exact Fintype.sum_bijective (e ∘ fun τ => Eqv.fEmb D τ) (e.bijective.comp hb) _ _ (fun τ => rfl)

/- English proof (translation)
Take `⟨-, -, hθ⟩` from `hψ`. Establish `h` using `hθ (Eqv.thetaC D) (Eqv.isInfFam_thetaC D) a`. Simplify using `only [Eqv.thetaC_tmul, map_one, mul_one] at h`. Rewrite using `[show ψ (pairA D.host.F a 0) = psiInf D.host.F ψ a from rfl, h]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psi_inf (hψ : IsStdChar D ψ (-1)) (a : Ainf D.host.F) :
    ψ (pairA D.host.F a 0) = Complex.exp (-(2 * Real.pi * Complex.I * ∑ τ, Eqv.gW D (Eqv.plW D τ) a)) := by
  obtain ⟨-, -, hθ⟩ := hψ
  have h := hθ (Eqv.thetaC D) (Eqv.isInfFam_thetaC D) a
  simp only [Eqv.thetaC_tmul, map_one, mul_one] at h
  rw [show ψ (pairA D.host.F a 0) = psiInf D.host.F ψ a from rfl, h]
  congr 1
  push_cast
  ring

/- English proof (translation)
Establish `hrat : ψ (algebraMap D.host.F (AF D.host.F) q) = 1`. Take `⟨⟨-, -, h, -⟩, -⟩` from `hψ`. Conclude with `h q`. Establish `hinf` using `psi_inf hψ (algebraMap D.host.F (Ainf D.host.F) q)`. Simplify using `only [Eqv.gW_algebraMap, sum_fEmb] at hinf`.

Rewrite `hrat` using `[algebraMap_AF, pairA_split, AddChar.map_add_eq_mul, hinf]`. Establish `h2` using `congrArg (fun w => Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.F q : ℚ) : ℂ)) * w) hrat`. Simplify using `only [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul, mul_one] at h2`. Conclude with `h2`.
-/
theorem psi_fin_rat (hψ : IsStdChar D ψ (-1)) (q : D.host.F) :
    ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) q)) =
      Complex.exp (2 * Real.pi * Complex.I * (Algebra.trace ℚ D.host.F q : ℚ)) := by
  have hrat : ψ (algebraMap D.host.F (AF D.host.F) q) = 1 := by
    obtain ⟨⟨-, -, h, -⟩, -⟩ := hψ
    exact h q
  have hinf := psi_inf hψ (algebraMap D.host.F (Ainf D.host.F) q)
  simp only [Eqv.gW_algebraMap, sum_fEmb] at hinf
  rw [algebraMap_AF, pairA_split, AddChar.map_add_eq_mul, hinf] at hrat
  have h2 := congrArg
    (fun w => Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.F q : ℚ) : ℂ)) * w) hrat
  simp only [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul, mul_one] at h2
  exact h2

/- English proof (translation)
Rewrite using `[eq_sub_iff_add_eq, ← pairA_add, add_zero, sub_add_cancel]`.
-/
theorem finite_pairing_sub (X Y : Af D.host.F) :
    pairA D.host.F 0 (X - Y) = pairA D.host.F 0 X - pairA D.host.F 0 Y := by
  rw [eq_sub_iff_add_eq, ← pairA_add, add_zero, sub_add_cancel]

/- English proof (translation)
Rewrite using `[← AddChar.map_add_eq_mul, ← pairA_add, add_zero]`.
-/
theorem psi_pair0_add (a b : Af D.host.F) :
    ψ (pairA D.host.F 0 (a + b)) = ψ (pairA D.host.F 0 a) * ψ (pairA D.host.F 0 b) := by
  rw [← AddChar.map_add_eq_mul, ← pairA_add, add_zero]

/- English proof (translation)
Conclude with `hy`.
-/
theorem mem_Ohat_of_intAf (y : Af D.host.F) (hy : y ∈ intAf D.host.F) : y ∈ Formalism.IndefR.PHeisFC.Ohat D.host.F := by
  exact hy

/- English proof (translation)
Take `⟨G, hGo, -, hG⟩` from `Formalism.IndefR.PHeisTh.psiOpen D.host.F ψ hψ.1`. Set `md : Af D.host.F →+ Af D.host.F` to `AddMonoidHom.mulLeft (algebraMap D.host.F (Af D.host.F) d)`. Set `H : AddSubgroup (Af D.host.F)` to `AddSubgroup.comap md G`. Establish `hHo : IsOpen (H : Set (Af D.host.F))` using `hGo.preimage (continuous_const.mul continuous_id)`. Take `⟨m, hm, hmH⟩` from `exists_nsmul_mem_cpt (Formalism.IndefR.PHeisFC.Ohat D.host.F) (Formalism.IndefR.PHeisFC.isCompact_Ohat D.host.F) (fun y hy n => (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd D.host.F).toAddSubgroup.nsmul_mem hy n) H hHo`.

Establish `hm0 : ((m : ℕ) : 𝓞 D.host.F) ≠ 0` using `Nat.cast_ne_zero.2 hm.ne'`. Take `⟨a, ha⟩` from `ReciprocityTheory.UG.AdeleIntA.exists_approx y (fun v => hy v) _ hm0`. Use `set z : Af D.host.F := algebraMap D.host.F (Af D.host.F) (1 / (m : D.host.F)) * (y - algebraMap D.host.F (Af D.host.F) (a : D.host.F)) with hz`. Establish `hmF : (m : D.host.F) ≠ 0` using `Nat.cast_ne_zero.2 hm.ne'`. Establish `hyz : y = algebraMap D.host.F (Af D.host.F) (a : D.host.F) + m • z`.

Rewrite using `[hz, nsmul_eq_mul, ← mul_assoc, show (m : Af D.host.F) = algebraMap D.host.F (Af D.host.F) (m : D.host.F) by simp, ← map_mul, mul_one_div_cancel hmF, map_one, one_mul]`. Normalize the expressions using the abelian group laws. Establish `hzint : z ∈ Formalism.IndefR.PHeisFC.Ohat D.host.F`. Introduce `v`. Establish `hv` using `ha v`.

Use `show (algebraMap D.host.F (Af D.host.F) (1 / (m : D.host.F)) * (y - algebraMap D.host.F (Af D.host.F) (a : D.host.F))) v ∈ v.adicCompletionIntegers D.host.F`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `e : (algebraMap D.host.F (Af D.host.F) (1 / (m : D.host.F)) * (y - algebraMap D.host.F (Af D.host.F) (a : D.host.F))) v = algebraMap D.host.F (v.adicCompletion D.host.F) (1 / (m : D.host.F)) * (y v - algebraMap D.host.F _ (algebraMap (𝓞 D.host.F) D.host.F a))` using `rfl`. Rewrite using `[e, map_mul]`. Establish `hval : Valued.v (algebraMap D.host.F (v.adicCompletion D.host.F) (1 / (m : D.host.F))) = (v.intValuation ((m : ℕ) : 𝓞 D.host.F))⁻¹`.

Rewrite using `[one_div, map_inv₀, map_inv₀]`. Use `congr 1`. Rewrite using `[show ((m : ℕ) : D.host.F) = algebraMap (𝓞 D.host.F) D.host.F ((m : ℕ) : 𝓞 D.host.F) by simp]`. Conclude with `ReciprocityTheory.UG.AdeleIntA.val_R v _`. Rewrite using `[hval]`.

Establish `hv0 : v.intValuation ((m : ℕ) : 𝓞 D.host.F) ≠ 0` using `v.intValuation_ne_zero _ hm0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hyz, mul_add, psi_pair0_add]`. Establish `h1 : ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) d * algebraMap D.host.F (Af D.host.F) (a : D.host.F))) = 1`. Rewrite using `[← map_mul, psi_fin_rat hψ]`.

Take `⟨n, hn⟩` from `hd a`. Rewrite using `[hn]`. Use `push_cast`. Conclude with `exp_two_pi_int n`. Establish `h2 : ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) d * m • z)) = 1` using `hG _ (hmH z hzint)`.

Rewrite using `[h1, h2, one_mul]`.
-/
theorem psi_invDiff (hψ : IsStdChar D ψ (-1)) (d : D.host.F) (hd : d ∈ invDiff D.host.F) (y : Af D.host.F)
    (hy : y ∈ intAf D.host.F) : ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) d * y)) = 1 := by
  obtain ⟨G, hGo, -, hG⟩ := Formalism.IndefR.PHeisTh.psiOpen D.host.F ψ hψ.1
  let md : Af D.host.F →+ Af D.host.F := AddMonoidHom.mulLeft (algebraMap D.host.F (Af D.host.F) d)
  let H : AddSubgroup (Af D.host.F) := AddSubgroup.comap md G
  have hHo : IsOpen (H : Set (Af D.host.F)) := hGo.preimage (continuous_const.mul continuous_id)
  obtain ⟨m, hm, hmH⟩ := exists_nsmul_mem_cpt (Formalism.IndefR.PHeisFC.Ohat D.host.F)
    (Formalism.IndefR.PHeisFC.isCompact_Ohat D.host.F)
    (fun y hy n => (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.intAd D.host.F).toAddSubgroup.nsmul_mem hy n) H hHo
  have hm0 : ((m : ℕ) : 𝓞 D.host.F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  obtain ⟨a, ha⟩ := ReciprocityTheory.UG.AdeleIntA.exists_approx y (fun v => hy v) _ hm0

  set z : Af D.host.F := algebraMap D.host.F (Af D.host.F) (1 / (m : D.host.F)) *
    (y - algebraMap D.host.F (Af D.host.F) (a : D.host.F)) with hz
  have hmF : (m : D.host.F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hyz : y = algebraMap D.host.F (Af D.host.F) (a : D.host.F) + m • z := by
    rw [hz, nsmul_eq_mul, ← mul_assoc, show (m : Af D.host.F) = algebraMap D.host.F (Af D.host.F) (m : D.host.F) by
      simp, ← map_mul, mul_one_div_cancel hmF, map_one, one_mul]
    abel
  have hzint : z ∈ Formalism.IndefR.PHeisFC.Ohat D.host.F := by
    intro v
    have hv := ha v
    show (algebraMap D.host.F (Af D.host.F) (1 / (m : D.host.F)) *
      (y - algebraMap D.host.F (Af D.host.F) (a : D.host.F))) v ∈ v.adicCompletionIntegers D.host.F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have e : (algebraMap D.host.F (Af D.host.F) (1 / (m : D.host.F)) *
        (y - algebraMap D.host.F (Af D.host.F) (a : D.host.F))) v =
        algebraMap D.host.F (v.adicCompletion D.host.F) (1 / (m : D.host.F)) *
          (y v - algebraMap D.host.F _ (algebraMap (𝓞 D.host.F) D.host.F a)) := rfl
    rw [e, map_mul]
    have hval : Valued.v (algebraMap D.host.F (v.adicCompletion D.host.F) (1 / (m : D.host.F))) =
        (v.intValuation ((m : ℕ) : 𝓞 D.host.F))⁻¹ := by
      rw [one_div, map_inv₀, map_inv₀]
      congr 1
      rw [show ((m : ℕ) : D.host.F) = algebraMap (𝓞 D.host.F) D.host.F ((m : ℕ) : 𝓞 D.host.F) by simp]
      exact ReciprocityTheory.UG.AdeleIntA.val_R v _
    rw [hval]
    have hv0 : v.intValuation ((m : ℕ) : 𝓞 D.host.F) ≠ 0 := v.intValuation_ne_zero _ hm0
    calc (v.intValuation ((m : ℕ) : 𝓞 D.host.F))⁻¹ * Valued.v _
        ≤ (v.intValuation ((m : ℕ) : 𝓞 D.host.F))⁻¹ * v.intValuation ((m : ℕ) : 𝓞 D.host.F) :=
          mul_le_mul' le_rfl hv
      _ = 1 := inv_mul_cancel₀ hv0
  rw [hyz, mul_add, psi_pair0_add]
  have h1 : ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) d *
      algebraMap D.host.F (Af D.host.F) (a : D.host.F))) = 1 := by
    rw [← map_mul, psi_fin_rat hψ]
    obtain ⟨n, hn⟩ := hd a
    rw [hn]; push_cast; exact exp_two_pi_int n
  have h2 : ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) d * m • z)) = 1 :=
    hG _ (hmH z hzint)
  rw [h1, h2, one_mul]

end Psi

section Kernel

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

/- English proof (translation)
Simplify using `only [Formalism.MainNotions.StandardLattice.intAf, ReciprocityTheory.UG.AdeleIntA.IsInt] at hy ⊢`. Conclude with `hy`.
-/
theorem isInt_of_intAf (y : Af D.host.F) (hy : y ∈ intAf D.host.F) : ReciprocityTheory.UG.AdeleIntA.IsInt y := by
  simp only [Formalism.MainNotions.StandardLattice.intAf, ReciprocityTheory.UG.AdeleIntA.IsInt] at hy ⊢
  exact hy

/- English proof (translation)
Simplify using `only [Formalism.MainNotions.StandardLattice.intAf, ReciprocityTheory.UG.AdeleIntA.IsInt] at hy ⊢`. Conclude with `hy`.
-/
theorem intAf_of_isInt (y : Af D.host.F) (hy : ReciprocityTheory.UG.AdeleIntA.IsInt y) : y ∈ intAf D.host.F := by
  simp only [Formalism.MainNotions.StandardLattice.intAf, ReciprocityTheory.UG.AdeleIntA.IsInt] at hy ⊢
  exact hy

/- English proof (translation)
Conclude with `intAf_of_isInt _ (ReciprocityTheory.UG.AdeleIntA.isInt_mul (isInt_of_intAf _ hx) (isInt_of_intAf _ hy))`.
-/
theorem intAf_mul {x y : Af D.host.F} (hx : x ∈ intAf D.host.F) (hy : y ∈ intAf D.host.F) : x * y ∈ intAf D.host.F := by
  exact intAf_of_isInt _ (ReciprocityTheory.UG.AdeleIntA.isInt_mul (isInt_of_intAf _ hx) (isInt_of_intAf _ hy))

/- English proof (translation)
Conclude with `intAf_of_isInt _ (ReciprocityTheory.UG.AdeleIntA.isInt_add (isInt_of_intAf _ hx) (isInt_of_intAf _ hy))`.
-/
theorem intAf_add {x y : Af D.host.F} (hx : x ∈ intAf D.host.F) (hy : y ∈ intAf D.host.F) : x + y ∈ intAf D.host.F := by
  exact intAf_of_isInt _ (ReciprocityTheory.UG.AdeleIntA.isInt_add (isInt_of_intAf _ hx) (isInt_of_intAf _ hy))

/- English proof (translation)
Establish `h` using `ReciprocityTheory.UG.AdeleIntA.isInt_R (K := D.host.F) r`. Rewrite `h` using `[IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F]`. Conclude with `intAf_of_isInt _ h`.
-/
theorem intAf_int (r : 𝓞 D.host.F) : algebraMap D.host.F (Af D.host.F) (r : D.host.F) ∈ intAf D.host.F := by
  have h := ReciprocityTheory.UG.AdeleIntA.isInt_R (K := D.host.F) r
  rw [IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F] at h
  exact intAf_of_isInt _ h

/- English proof (translation)
Simplify using `using intAf_int (D := D) 1`.
-/
theorem one_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := by
  simpa using intAf_int (D := D) 1

/- English proof (translation)
Take `⟨n, d, y, hd, hy, rfl⟩` from `hα`. Rewrite using `[Finset.sum_mul]`. Establish `key : ∀ s : Finset (Fin n), ψ (pairA D.host.F 0 (∑ i ∈ s, algebraMap D.host.F (Af D.host.F) (d i) * y i * x)) = 1`. Introduce `s`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations.

Simplify using `only [Finset.sum_empty]`. Conclude with `ψ.map_zero_eq_one`. Introduce `i s hi ih`. Rewrite using `[Finset.sum_insert hi, psi_pair0_add, ih, mul_one, mul_assoc]`. Conclude with `psi_invDiff hψ (d i) (hd i) _ (intAf_mul (hy i) hx)`.

Conclude with `key Finset.univ`.
-/
theorem invDiffAf_mem (hψ : IsStdChar D ψ (-1)) (α : Af D.host.F) (hα : α ∈ invDiffAf D.host.F)
    (x : Af D.host.F) (hx : x ∈ intAf D.host.F) : ψ (pairA D.host.F 0 (α * x)) = 1 := by
  obtain ⟨n, d, y, hd, hy, rfl⟩ := hα
  rw [Finset.sum_mul]
  have key : ∀ s : Finset (Fin n),
      ψ (pairA D.host.F 0 (∑ i ∈ s, algebraMap D.host.F (Af D.host.F) (d i) * y i * x)) = 1 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp only [Finset.sum_empty]
      exact ψ.map_zero_eq_one
    · intro i s hi ih
      rw [Finset.sum_insert hi, psi_pair0_add, ih, mul_one, mul_assoc]
      exact psi_invDiff hψ (d i) (hd i) _ (intAf_mul (hy i) hx)
  exact key Finset.univ

/- English proof (translation)
Take `⟨u, hu⟩` from `ReciprocityTheory.UG.AdeleIntA.exists_approx_adele (R := 𝓞 D.host.F) α`. Establish `hu' : α - algebraMap D.host.F (Af D.host.F) u ∈ intAf D.host.F` using `intAf_of_isInt _ hu`. Establish `huD : u ∈ invDiff D.host.F`. Introduce `b`. Establish `h1` using `h _ (intAf_int b)`.

Establish `h2` using `psi_invDiff hψ 1 one_mem_invDiff _ (intAf_mul hu' (intAf_int b))`. Rewrite `h2` using `[map_one, one_mul]`. Establish `e : algebraMap D.host.F (Af D.host.F) (u * b) = α * algebraMap D.host.F (Af D.host.F) (b : D.host.F) - (α - algebraMap D.host.F (Af D.host.F) u) * algebraMap D.host.F (Af D.host.F) (b : D.host.F)`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h3 : ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (u * b))) = 1`. Rewrite using `[e, finite_pairing_sub, AddChar.map_sub_eq_div, h1, h2, div_one]`. Rewrite `h3` using `[psi_fin_rat hψ]`. Take `⟨n, hn⟩` from `Complex.exp_eq_one_iff.1 h3`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Establish `hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0`. Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero]`. Establish `: ((Algebra.trace ℚ D.host.F (u * b) : ℚ) : ℂ) = ((n : ℚ) : ℂ)`. Use `hn` as an intermediate fact. Rewrite `this` using `[mul_comm (2 * Real.pi * Complex.I : ℂ)]`.

Use `push_cast`. Conclude with `mul_right_cancel₀ hpi this`. Conclude with `this` after adjusting the coercions. Use `⟨2, ![u, 1], ![1, α - algebraMap D.host.F (Af D.host.F) u], ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`.

Use `fin_cases i`. Conclude with `huD`. Conclude with `one_mem_invDiff`. Introduce `i`. Use `fin_cases i`.

Conclude with `one_intAf`. Conclude with `hu'`. Simplify using `[Fin.sum_univ_two]`.
-/
theorem mem_invDiffAf_of (hψ : IsStdChar D ψ (-1)) (α : Af D.host.F)
    (h : ∀ x ∈ intAf D.host.F, ψ (pairA D.host.F 0 (α * x)) = 1) : α ∈ invDiffAf D.host.F := by
  obtain ⟨u, hu⟩ := ReciprocityTheory.UG.AdeleIntA.exists_approx_adele (R := 𝓞 D.host.F) α
  have hu' : α - algebraMap D.host.F (Af D.host.F) u ∈ intAf D.host.F := intAf_of_isInt _ hu
  have huD : u ∈ invDiff D.host.F := by
    intro b
    have h1 := h _ (intAf_int b)
    have h2 := psi_invDiff hψ 1 one_mem_invDiff _ (intAf_mul hu' (intAf_int b))
    rw [map_one, one_mul] at h2
    have e : algebraMap D.host.F (Af D.host.F) (u * b) =
        α * algebraMap D.host.F (Af D.host.F) (b : D.host.F) -
          (α - algebraMap D.host.F (Af D.host.F) u) * algebraMap D.host.F (Af D.host.F) (b : D.host.F) := by
      rw [map_mul]; ring
    have h3 : ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (u * b))) = 1 := by
      rw [e, finite_pairing_sub, AddChar.map_sub_eq_div, h1, h2, div_one]
    rw [psi_fin_rat hψ] at h3
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h3
    refine ⟨n, ?_⟩
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : ((Algebra.trace ℚ D.host.F (u * b) : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
      have := hn
      rw [mul_comm (2 * Real.pi * Complex.I : ℂ)] at this
      push_cast
      exact mul_right_cancel₀ hpi this
    exact_mod_cast this
  refine ⟨2, ![u, 1], ![1, α - algebraMap D.host.F (Af D.host.F) u], ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact huD
    · exact one_mem_invDiff
  · intro i; fin_cases i
    · exact one_intAf
    · exact hu'
  · simp [Fin.sum_univ_two]

/- English proof (translation)
Take `⟨a, ha, hint⟩` from `(FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F)).isFractional`. Use `⟨a, nonZeroDivisors.ne_zero ha, fun d hd => ?_⟩` and prove the remaining obligations. Establish `h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) ≠ 0`. Introduce `h`. Establish `h2 : (1 : D.host.F) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F)`.

Rewrite using `[FractionalIdeal.mem_one_iff]`. Conclude with `⟨1, map_one _⟩`. Rewrite `h2` using `[h, FractionalIdeal.mem_zero_iff]`. Conclude with `one_ne_zero h2`. Establish `hmem : d ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F)`.

Rewrite using `[FractionalIdeal.mem_dual h1]`. Introduce `y hy`. Rewrite `hy` using `[FractionalIdeal.mem_one_iff]`. Take `⟨y, rfl⟩` from `hy`. Take `⟨z, hz⟩` from `hd y`.

Use `⟨z, ?_⟩` and prove the remaining obligations. Simplify using `only [Algebra.traceForm_apply, algebraMap_int_eq, Int.coe_castRingHom]`. Conclude with `hz.symm`. Take `⟨s, hs⟩` from `hint d hmem`. Use `⟨s, ?_⟩` and prove the remaining obligations.

Rewrite `hs` using `[Algebra.smul_def]`. Conclude with `hs.symm`.
-/
theorem exists_invDiff_bound : ∃ r : 𝓞 D.host.F, r ≠ 0 ∧
    ∀ d ∈ invDiff D.host.F, ∃ s : 𝓞 D.host.F, (r : D.host.F) * d = s := by
  classical
  obtain ⟨a, ha, hint⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F)).isFractional
  refine ⟨a, nonZeroDivisors.ne_zero ha, fun d hd => ?_⟩
  have h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) ≠ 0 := by
    intro h
    have h2 : (1 : D.host.F) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) := by
      rw [FractionalIdeal.mem_one_iff]
      exact ⟨1, map_one _⟩
    rw [h, FractionalIdeal.mem_zero_iff] at h2
    exact one_ne_zero h2
  have hmem : d ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.F)) D.host.F) := by
    rw [FractionalIdeal.mem_dual h1]
    intro y hy
    rw [FractionalIdeal.mem_one_iff] at hy
    obtain ⟨y, rfl⟩ := hy
    obtain ⟨z, hz⟩ := hd y
    refine ⟨z, ?_⟩
    simp only [Algebra.traceForm_apply, algebraMap_int_eq, Int.coe_castRingHom]
    exact hz.symm
  obtain ⟨s, hs⟩ := hint d hmem
  refine ⟨s, ?_⟩
  rw [Algebra.smul_def] at hs
  exact hs.symm

/- English proof (translation)
Take `⟨r, hr0, hr⟩` from `exists_invDiff_bound (D := D)`. Use `Eqv.AdelDual.eq_zero_of_mem_factorial b fun n => ?_` and prove the remaining obligations. Establish `hrF : (r : D.host.F) ≠ 0` using `by exact_mod_cast hr0`. Establish `hc : (r : D.host.F) * (n.factorial : D.host.F) ≠ 0` using `mul_ne_zero hrF (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n))`. Use `set α := b * algebraMap D.host.F (Af D.host.F) (1 / ((r : D.host.F) * n.factorial)) with hα`.

Establish `hαm : α ∈ invDiffAf D.host.F` using `mem_invDiffAf_of hψ α fun x _ => by rw [hα, mul_assoc]; exact h _`. Take `⟨k, d, y, hd, hy, hsum⟩` from `hαm`. Use `⟨algebraMap D.host.F (Af D.host.F) (r : D.host.F) * α, ?_, ?_⟩` and prove the remaining obligations. Apply `mem_Ohat_of_intAf` to reduce the goal to its premises. Rewrite using `[hsum, Finset.mul_sum]`.

Use `Finset.sum_induction _ (· ∈ intAf D.host.F) (fun _ _ => intAf_add) (intAf_of_isInt _ ReciprocityTheory.UG.AdeleIntA.isInt_zero) fun i _ => ?_` and prove the remaining obligations. Take `⟨s, hs⟩` from `hr (d i) (hd i)`. Rewrite using `[← mul_assoc, ← map_mul, hs]`. Conclude with `intAf_mul (intAf_int s) (hy i)`. Rewrite using `[hα, nsmul_eq_mul, show (n.factorial : Af D.host.F) = algebraMap D.host.F (Af D.host.F) (n.factorial : D.host.F) by simp, ← mul_assoc, ← map_mul, mul_comm (n.factorial : D.host.F) (r : D.host.F), mul_left_comm, ← map_mul, mul_one_div_cancel hc, map_one, mul_one]`.
-/
theorem psi_nondeg_fin (hψ : IsStdChar D ψ (-1)) (b : Af D.host.F)
    (h : ∀ y : Af D.host.F, ψ (pairA D.host.F 0 (b * y)) = 1) : b = 0 := by
  obtain ⟨r, hr0, hr⟩ := exists_invDiff_bound (D := D)
  refine Eqv.AdelDual.eq_zero_of_mem_factorial b fun n => ?_
  have hrF : (r : D.host.F) ≠ 0 := by exact_mod_cast hr0
  have hc : (r : D.host.F) * (n.factorial : D.host.F) ≠ 0 :=
    mul_ne_zero hrF (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n))
  set α := b * algebraMap D.host.F (Af D.host.F) (1 / ((r : D.host.F) * n.factorial)) with hα
  have hαm : α ∈ invDiffAf D.host.F := mem_invDiffAf_of hψ α fun x _ => by rw [hα, mul_assoc]; exact h _
  obtain ⟨k, d, y, hd, hy, hsum⟩ := hαm
  refine ⟨algebraMap D.host.F (Af D.host.F) (r : D.host.F) * α, ?_, ?_⟩
  · apply mem_Ohat_of_intAf
    rw [hsum, Finset.mul_sum]
    refine Finset.sum_induction _ (· ∈ intAf D.host.F) (fun _ _ => intAf_add)
      (intAf_of_isInt _ ReciprocityTheory.UG.AdeleIntA.isInt_zero) fun i _ => ?_
    obtain ⟨s, hs⟩ := hr (d i) (hd i)
    rw [← mul_assoc, ← map_mul, hs]
    exact intAf_mul (intAf_int s) (hy i)
  · rw [hα, nsmul_eq_mul, show (n.factorial : Af D.host.F) = algebraMap D.host.F (Af D.host.F) (n.factorial : D.host.F) by
      simp, ← mul_assoc, ← map_mul, mul_comm (n.factorial : D.host.F) (r : D.host.F), mul_left_comm, ← map_mul,
      mul_one_div_cancel hc, map_one, mul_one]

/- English proof (translation)
Use function extensionality and compare the values at `w`. Assume the negation of the conclusion as `hne`. Take `⟨τ0, rfl⟩ : ∃ τ0, Eqv.plW D τ0 = w` from `⟨_, Eqv.plW_symm D w⟩`. Establish `hinj : Function.Injective (Eqv.plW D)`. Introduce `τ τ' h'`.

Rewrite `h'` using `[Eqv.plW_eq_tauPl, Eqv.plW_eq_tauPl]`. Conclude with `(Formalism.L2.Host.tauPl D).injective h'`. Set `s : Ainf D.host.F` to `Pi.single (Eqv.plW D τ0) ((a (Eqv.plW D τ0))⁻¹ * 2⁻¹)`. Establish `hs` using `h s`. Rewrite `hs` using `[psi_inf hψ]`.

Establish `hsum : ∑ τ, Eqv.gW D (Eqv.plW D τ) (a * s) = 2⁻¹`. Rewrite using `[Finset.sum_eq_single τ0]`. Rewrite using `[map_mul, Eqv.gW_apply, Eqv.gW_apply, show s (Eqv.plW D τ0) = (a (Eqv.plW D τ0))⁻¹ * 2⁻¹ from Pi.single_eq_same _ _, ← map_mul, mul_inv_cancel_left₀ hne, map_inv₀, map_ofNat]`. Introduce `τ _ hτ`. Rewrite using `[map_mul, Eqv.gW_apply, Eqv.gW_apply, show s (Eqv.plW D τ) = 0 from Pi.single_eq_of_ne (hinj.ne hτ) _, map_zero, mul_zero]`.

Introduce `h0`. Conclude with `absurd (Finset.mem_univ τ0) h0`. Rewrite `hs` using `[hsum]`. Establish `he : Complex.exp (-(2 * Real.pi * Complex.I * 2⁻¹)) = -1`. Rewrite using `[show -(2 * Real.pi * Complex.I * 2⁻¹ : ℂ) = -(Real.pi * Complex.I) by ring, Complex.exp_neg, Complex.exp_pi_mul_I]`.

Evaluate the numerical expressions. Rewrite `hs` using `[he]`. Evaluate the numerical expressions using `at hs`.
-/
theorem psi_nondeg_inf (hψ : IsStdChar D ψ (-1)) (a : Ainf D.host.F)
    (h : ∀ s : Ainf D.host.F, ψ (pairA D.host.F (a * s) 0) = 1) : a = 0 := by
  classical
  funext w
  by_contra hne
  obtain ⟨τ0, rfl⟩ : ∃ τ0, Eqv.plW D τ0 = w := ⟨_, Eqv.plW_symm D w⟩
  have hinj : Function.Injective (Eqv.plW D) := by
    intro τ τ' h'
    rw [Eqv.plW_eq_tauPl, Eqv.plW_eq_tauPl] at h'
    exact (Formalism.L2.Host.tauPl D).injective h'
  let s : Ainf D.host.F := Pi.single (Eqv.plW D τ0) ((a (Eqv.plW D τ0))⁻¹ * 2⁻¹)
  have hs := h s
  rw [psi_inf hψ] at hs
  have hsum : ∑ τ, Eqv.gW D (Eqv.plW D τ) (a * s) = 2⁻¹ := by
    rw [Finset.sum_eq_single τ0]
    · rw [map_mul, Eqv.gW_apply, Eqv.gW_apply,
        show s (Eqv.plW D τ0) = (a (Eqv.plW D τ0))⁻¹ * 2⁻¹ from Pi.single_eq_same _ _,
        ← map_mul, mul_inv_cancel_left₀ hne, map_inv₀, map_ofNat]
    · intro τ _ hτ
      rw [map_mul, Eqv.gW_apply, Eqv.gW_apply,
        show s (Eqv.plW D τ) = 0 from Pi.single_eq_of_ne (hinj.ne hτ) _, map_zero, mul_zero]
    · intro h0
      exact absurd (Finset.mem_univ τ0) h0
  rw [hsum] at hs
  have he : Complex.exp (-(2 * Real.pi * Complex.I * 2⁻¹)) = -1 := by
    rw [show -(2 * Real.pi * Complex.I * 2⁻¹ : ℂ) = -(Real.pi * Complex.I) by ring, Complex.exp_neg,
      Complex.exp_pi_mul_I]
    norm_num
  rw [he] at hs
  norm_num at hs

/- English proof (translation)
Take `⟨b1, b2⟩` from `b`. Establish `h1 : b1 = 0` using `psi_nondeg_inf hψ b1 fun s => by`. Use `h (pairA D.host.F s 0)` as an intermediate fact. Express the relevant statement in the definitionally equal form `ψ (pairA D.host.F (b1 * s) (b2 * 0)) = 1 at this`. Rewrite `this` using `[mul_zero]`. Then use the resulting hypothesis.

Establish `h2 : b2 = 0` using `psi_nondeg_fin hψ b2 fun y => by`. Use `h (pairA D.host.F 0 y)` as an intermediate fact. Express the relevant statement in the definitionally equal form `ψ (pairA D.host.F (b1 * 0) (b2 * y)) = 1 at this`. Rewrite `this` using `[mul_zero]`. Then use the resulting hypothesis. Substitute `h1` using the available equality.

Substitute `h2` using the available equality. Both sides reduce to the same expression.
-/
theorem psi_nondeg (hψ : IsStdChar D ψ (-1)) (b : AF D.host.F) (h : ∀ y : AF D.host.F, ψ (b * y) = 1) : b = 0 := by
  obtain ⟨b1, b2⟩ := b
  have h1 : b1 = 0 := psi_nondeg_inf hψ b1 fun s => by
    have := h (pairA D.host.F s 0)
    change ψ (pairA D.host.F (b1 * s) (b2 * 0)) = 1 at this
    rwa [mul_zero] at this
  have h2 : b2 = 0 := psi_nondeg_fin hψ b2 fun y => by
    have := h (pairA D.host.F 0 y)
    change ψ (pairA D.host.F (b1 * 0) (b2 * y)) = 1 at this
    rwa [mul_zero] at this
  subst h1
  subst h2
  rfl

end Kernel

section Exist

variable {D : D7}

def Linf (D : D7) : Ainf D.host.F →+ ℝ where
  toFun a := -∑ τ : D.what₂.Tau, (Eqv.gW D (Eqv.plW D τ) a).re
  map_zero' := by simp
  map_add' a b := by simp only [map_add, Complex.add_re, Finset.sum_add_distrib, neg_add]

/- English proof (translation)
Establish `hg : ∀ τ, Continuous fun a : Ainf D.host.F => Eqv.gW D (Eqv.plW D τ) a` using `fun τ => (isometry_extensionEmbedding _).continuous.comp (continuous_apply _)`. Use `show Continuous fun a => -∑ τ : D.what₂.Tau, (Eqv.gW D (Eqv.plW D τ) a).re`. Conclude with `(continuous_finset_sum _ fun τ _ => Complex.continuous_re.comp (hg τ)).neg`.
-/
theorem continuous_Linf : Continuous (Linf D) := by
  have hg : ∀ τ, Continuous fun a : Ainf D.host.F => Eqv.gW D (Eqv.plW D τ) a := fun τ =>
    (isometry_extensionEmbedding _).continuous.comp (continuous_apply _)
  show Continuous fun a => -∑ τ : D.what₂.Tau, (Eqv.gW D (Eqv.plW D τ) a).re
  exact (continuous_finset_sum _ fun τ _ => Complex.continuous_re.comp (hg τ)).neg

/- English proof (translation)
Establish `h : ∀ τ, Eqv.gW D (Eqv.plW D τ) a = (((Eqv.gW D (Eqv.plW D τ) a).re : ℝ) : ℂ)`. Introduce `τ`. Rewrite using `[Eqv.gW_real]`. Simplify using the standard rewrite rules. Use `show ∑ τ, Eqv.gW D (Eqv.plW D τ) a = ((-(-∑ τ : D.what₂.Tau, (Eqv.gW D (Eqv.plW D τ) a).re) : ℝ) : ℂ)`.

Rewrite using `[neg_neg, Complex.ofReal_sum]`. Conclude with `Finset.sum_congr rfl fun τ _ => h τ`.
-/
theorem sum_gW_eq (a : Ainf D.host.F) : ∑ τ : D.what₂.Tau, Eqv.gW D (Eqv.plW D τ) a = ((-(Linf D a) : ℝ) : ℂ) := by
  have h : ∀ τ, Eqv.gW D (Eqv.plW D τ) a = (((Eqv.gW D (Eqv.plW D τ) a).re : ℝ) : ℂ) := by
    intro τ
    rw [Eqv.gW_real]
    simp
  show ∑ τ, Eqv.gW D (Eqv.plW D τ) a = ((-(-∑ τ : D.what₂.Tau, (Eqv.gW D (Eqv.plW D τ) a).re) : ℝ) : ℂ)
  rw [neg_neg, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun τ _ => h τ

/- English proof (translation)
Take `⟨z, hz⟩` from `trace_int b`. Use `⟨-z, ?_⟩` and prove the remaining obligations. Use `show -∑ τ : D.what₂.Tau, (Eqv.gW D (Eqv.plW D τ) (algebraMap D.host.F (Ainf D.host.F) (b : D.host.F))).re = ((-z : ℤ) : ℝ)`. Rewrite using `[show (∑ τ : D.what₂.Tau, (Eqv.gW D (Eqv.plW D τ) (algebraMap D.host.F (Ainf D.host.F) (b : D.host.F))).re) = (∑ τ : D.what₂.Tau, Eqv.fEmb D τ b).re by rw [Complex.re_sum]; simp only [Eqv.gW_algebraMap]]`. Rewrite using `[sum_fEmb, hz]`.

Simplify using the standard rewrite rules.
-/
theorem Linf_int (b : 𝓞 D.host.F) : ∃ n : ℤ, Linf D (algebraMap D.host.F (Ainf D.host.F) (b : D.host.F)) = n := by
  obtain ⟨z, hz⟩ := trace_int b
  refine ⟨-z, ?_⟩
  show -∑ τ : D.what₂.Tau,
      (Eqv.gW D (Eqv.plW D τ) (algebraMap D.host.F (Ainf D.host.F) (b : D.host.F))).re = ((-z : ℤ) : ℝ)
  rw [show (∑ τ : D.what₂.Tau,
      (Eqv.gW D (Eqv.plW D τ) (algebraMap D.host.F (Ainf D.host.F) (b : D.host.F))).re) =
      (∑ τ : D.what₂.Tau, Eqv.fEmb D τ b).re by rw [Complex.re_sum]; simp only [Eqv.gW_algebraMap]]
  rw [sum_fEmb, hz]
  simp

/- English proof (translation)
Establish `hn0 : ((Module.finrank ℚ D.host.F : ℕ) : ℚ) ≠ 0` using `by exact_mod_cast Module.finrank_pos.ne'`. Establish `hq : (Module.finrank ℚ D.host.F • (-(1 / (2 * (Module.finrank ℚ D.host.F : ℚ)))) : ℚ) = -(1 / 2)`. Rewrite using `[nsmul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Use `⟨algebraMap D.host.F (Ainf D.host.F) (algebraMap ℚ D.host.F (-(1 / (2 * (Module.finrank ℚ D.host.F : ℚ))))), ?_⟩` and prove the remaining obligations.

Establish `h` using `congrArg Complex.re (sum_fEmb (D := D) (algebraMap ℚ D.host.F (-(1 / (2 * (Module.finrank ℚ D.host.F : ℚ))))))`. Rewrite `h` using `[Algebra.trace_algebraMap, hq, Complex.re_sum]`. Use `show -∑ τ : D.what₂.Tau, (Eqv.gW D (Eqv.plW D τ) (algebraMap D.host.F (Ainf D.host.F) (algebraMap ℚ D.host.F (-(1 / (2 * (Module.finrank ℚ D.host.F : ℚ))))))).re = 1 / 2`. Simplify using `only [Eqv.gW_algebraMap, h]`. Evaluate the numerical expressions.
-/
theorem exists_Linf_half : ∃ t : Ainf D.host.F, Linf D t = 1 / 2 := by
  have hn0 : ((Module.finrank ℚ D.host.F : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hq : (Module.finrank ℚ D.host.F • (-(1 / (2 * (Module.finrank ℚ D.host.F : ℚ)))) : ℚ) = -(1 / 2) := by
    rw [nsmul_eq_mul]
    field_simp
  refine ⟨algebraMap D.host.F (Ainf D.host.F)
    (algebraMap ℚ D.host.F (-(1 / (2 * (Module.finrank ℚ D.host.F : ℚ))))), ?_⟩
  have h := congrArg Complex.re
    (sum_fEmb (D := D) (algebraMap ℚ D.host.F (-(1 / (2 * (Module.finrank ℚ D.host.F : ℚ))))))
  rw [Algebra.trace_algebraMap, hq, Complex.re_sum] at h
  show -∑ τ : D.what₂.Tau, (Eqv.gW D (Eqv.plW D τ) (algebraMap D.host.F (Ainf D.host.F)
    (algebraMap ℚ D.host.F (-(1 / (2 * (Module.finrank ℚ D.host.F : ℚ))))))).re = 1 / 2
  simp only [Eqv.gW_algebraMap, h]
  norm_num

/- English proof (translation)
Set `F` to `D.host.F`. Set `mk : ℝ →+ AddCircle (1 : ℝ)` to `QuotientAddGroup.mk' _`. Establish `hmk : Continuous mk` using `continuous_quotient_mk'`. Set `fs : AF F →+ Ainf F` to `(fstA F).toRingHom.toAddMonoidHom`. Establish `hfs : Continuous fs` using `continuous_fst`.

Set `g : AF F →+ AddCircle (1 : ℝ)` to `mk.comp ((Linf D).comp fs)`. Establish `hg : Continuous g` using `hmk.comp (continuous_Linf.comp hfs)`. Set `K : AddSubgroup (AF F)` to `(algebraMap F (AF F)).range.toAddSubgroup`. Take `⟨h, hc, hK, hU⟩` from `PI.GaugeCharW.extChar (AF F) K (PI.GaugeCharW.intSub F) (PI.GaugeCharW.isOpen_intSub F PI.GaugeCharW.openInt) g hg (by`. Introduce and unpack `x ⟨a, rfl⟩ hx`.

Take `⟨b, rfl⟩` from `PI.GaugeCharW.intInter F a (fun v => by`. Establish `hv` using `hx v`. Rewrite using `[AlgHom.commutes] at hv)` and apply the resulting hypothesis. Take `⟨n, hn⟩` from `Linf_int (D := D) b`. Establish `e1 : fs (algebraMap F (AF F) (b : F)) = algebraMap F (Ainf F) (b : F)` using `rfl`.

Use `show mk (Linf D (fs (algebraMap F (AF F) (b : F)))) = 0`. Rewrite using `[e1, hn]`. Use `show ((n : ℝ) : AddCircle (1 : ℝ)) = 0`. Rewrite using `[AddCircle.coe_eq_zero_iff]`. Conclude with `⟨n, by simp⟩)`.

Set `ψ : AddChar (AF F) ℂ` to `{ toFun := fun x => ((AddCircle.toCircle (h x) : Circle) : ℂ), map_zero_eq_one' := by simp, map_add_eq_mul' := fun x y => by simp [map_add, AddCircle.toCircle_add] }`. Establish `hval : ∀ t : Ainf F, ψ (pairA F t 0) = Complex.exp (2 * Real.pi * Complex.I * (Linf D t : ℂ))`. Introduce `t`. Establish `hx0 : pairA F t 0 ∈ PI.GaugeCharW.intSub F` using `fun v => by show (0 : Af F) v ∈ _`. Conclude with `zero_mem _`.

Use `show ((AddCircle.toCircle (h (pairA F t 0)) : Circle) : ℂ) = _`. Rewrite using `[hU _ hx0]`. Use `show ((AddCircle.toCircle ((Linf D t : ℝ) : AddCircle (1 : ℝ)) : Circle) : ℂ) = _`. Rewrite using `[AddCircle.toCircle_apply_mk, Circle.coe_exp]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨ψ, ⟨?_, ?_, ?_, ?_⟩, ⟨Eqv.thetaC D, Eqv.isInfFam_thetaC D⟩, fun θ hθ x => ?_⟩` and prove the remaining obligations. Conclude with `continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp hc)`. Introduce `x`.

Conclude with `Circle.norm_coe _`. Introduce `a`. Establish `ha : h (algebraMap F (AF F) a) = 0` using `hK _ ⟨a, rfl⟩`. Use `show ((AddCircle.toCircle (h (algebraMap F (AF F) a)) : Circle) : ℂ) = 1`. Simplify using `[ha]`.

Take `⟨t, ht⟩` from `exists_Linf_half (D := D)`. Use `⟨pairA F t 0, ?_⟩` and prove the remaining obligations. Rewrite using `[hval, ht]`. Establish `: Complex.exp (2 * Real.pi * Complex.I * (((1 / 2 : ℝ)) : ℂ)) = -1`. Rewrite using `[show 2 * Real.pi * Complex.I * (((1 / 2 : ℝ)) : ℂ) = Real.pi * Complex.I by push_cast; ring, Complex.exp_pi_mul_I]`.

Rewrite using `[this]`. Evaluate the numerical expressions. Rewrite using `[Eqv.eq_thetaC D hθ]`. Unfold `psiInf`. Rewrite using `[hval]`.

Use `congr 1`. Establish `e : ∑ ρ, Eqv.thetaC D ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) = ((-(Linf D x) : ℝ) : ℂ)`. Rewrite using `[← sum_gW_eq]`. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Rewrite using `[Eqv.thetaC_tmul, map_one, mul_one]`.

Rewrite using `[e]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_stdChar : ∃ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) := by
  let F := D.host.F
  let mk : ℝ →+ AddCircle (1 : ℝ) := QuotientAddGroup.mk' _
  have hmk : Continuous mk := continuous_quotient_mk'
  let fs : AF F →+ Ainf F := (fstA F).toRingHom.toAddMonoidHom
  have hfs : Continuous fs := continuous_fst
  let g : AF F →+ AddCircle (1 : ℝ) := mk.comp ((Linf D).comp fs)
  have hg : Continuous g := hmk.comp (continuous_Linf.comp hfs)
  let K : AddSubgroup (AF F) := (algebraMap F (AF F)).range.toAddSubgroup
  obtain ⟨h, hc, hK, hU⟩ := PI.GaugeCharW.extChar (AF F) K (PI.GaugeCharW.intSub F)
    (PI.GaugeCharW.isOpen_intSub F PI.GaugeCharW.openInt) g hg (by
      rintro x ⟨a, rfl⟩ hx
      obtain ⟨b, rfl⟩ := PI.GaugeCharW.intInter F a (fun v => by
        have hv := hx v
        rwa [AlgHom.commutes] at hv)
      obtain ⟨n, hn⟩ := Linf_int (D := D) b
      have e1 : fs (algebraMap F (AF F) (b : F)) = algebraMap F (Ainf F) (b : F) := rfl
      show mk (Linf D (fs (algebraMap F (AF F) (b : F)))) = 0
      rw [e1, hn]
      show ((n : ℝ) : AddCircle (1 : ℝ)) = 0
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨n, by simp⟩)
  let ψ : AddChar (AF F) ℂ :=
    { toFun := fun x => ((AddCircle.toCircle (h x) : Circle) : ℂ),
      map_zero_eq_one' := by simp,
      map_add_eq_mul' := fun x y => by simp [map_add, AddCircle.toCircle_add] }
  have hval : ∀ t : Ainf F, ψ (pairA F t 0) = Complex.exp (2 * Real.pi * Complex.I * (Linf D t : ℂ)) := by
    intro t
    have hx0 : pairA F t 0 ∈ PI.GaugeCharW.intSub F := fun v => by
      show (0 : Af F) v ∈ _
      exact zero_mem _
    show ((AddCircle.toCircle (h (pairA F t 0)) : Circle) : ℂ) = _
    rw [hU _ hx0]
    show ((AddCircle.toCircle ((Linf D t : ℝ) : AddCircle (1 : ℝ)) : Circle) : ℂ) = _
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
    congr 1; push_cast; ring
  refine ⟨ψ, ⟨?_, ?_, ?_, ?_⟩, ⟨Eqv.thetaC D, Eqv.isInfFam_thetaC D⟩, fun θ hθ x => ?_⟩
  · exact continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp hc)
  · intro x; exact Circle.norm_coe _
  · intro a
    have ha : h (algebraMap F (AF F) a) = 0 := hK _ ⟨a, rfl⟩
    show ((AddCircle.toCircle (h (algebraMap F (AF F) a)) : Circle) : ℂ) = 1
    simp [ha]
  · obtain ⟨t, ht⟩ := exists_Linf_half (D := D)
    refine ⟨pairA F t 0, ?_⟩
    rw [hval, ht]
    have : Complex.exp (2 * Real.pi * Complex.I * (((1 / 2 : ℝ)) : ℂ)) = -1 := by
      rw [show 2 * Real.pi * Complex.I * (((1 / 2 : ℝ)) : ℂ) = Real.pi * Complex.I by push_cast; ring,
        Complex.exp_pi_mul_I]
    rw [this]; norm_num
  · rw [Eqv.eq_thetaC D hθ]
    unfold psiInf
    rw [hval]
    congr 1
    have e : ∑ ρ, Eqv.thetaC D ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) = ((-(Linf D x) : ℝ) : ℂ) := by
      rw [← sum_gW_eq]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [Eqv.thetaC_tmul, map_one, mul_one]
    rw [e]; push_cast; ring

/- English proof (translation)
Unfold `StdCharExists`. Conclude with `⟨exists_stdChar, fun ψ hψ α => ⟨mem_invDiffAf_of hψ α, fun hα x hx => invDiffAf_mem hψ α hα x hx⟩⟩`.
-/
theorem stdCharExists (D : D7) : StdCharExists D := by
  unfold StdCharExists
  exact ⟨exists_stdChar, fun ψ hψ α => ⟨mem_invDiffAf_of hψ α, fun hα x hx => invDiffAf_mem hψ α hα x hx⟩⟩

end Exist

end Formalism.IndefR.Fin

end
