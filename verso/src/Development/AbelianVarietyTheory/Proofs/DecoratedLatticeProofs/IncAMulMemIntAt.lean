import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatEqMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIncAMulMemIntAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassC0PrimeNotExceptional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf
open ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.UnitAt

variable {D : D7}

/- English proof (translation)
Introduce `a ha`. Establish `hNF : (N : D.host.F) ≠ 0` using `Int.cast_ne_zero.2 fun h => hN (by rw [h, Int.cast_zero]; exact zero_mem _)`. Use `⟨Ideal.mul_mem_left _ _ ha.1, ?_⟩` and prove the remaining obligations. Establish `hc : finPart D (incA D c) = (1 : Af D.host.F) ⊗ₜ[D.host.F] c` using `rfl`. Rewrite using `[map_mul, hc, ← AeUnit.idem_mul_finPart D v ha.1, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`.

Use `GlobalTheory.HostAdeleIso.intAE_mul_mem D ?_ ha.2` and prove the remaining obligations. Use `AddSubgroup.subset_closure ⟨_, AeUnit.inv_smul_singleV_mem v N hN, ⟨N • c, hint⟩, ?_⟩` and prove the remaining obligations. Conclude with `AeUnit.tmul_eq_inv_smul_tmul N hNF _ c`.
-/
theorem incA_mul_mem_intAt {v : Pl D} {c : D.host.E} {N : ℤ} (hN : (N : 𝓞 D.host.F) ∉ v.asIdeal)
    (hint : IsIntegral ℤ (N • c)) : ∀ a ∈ intAt D (· = v), incA D c * a ∈ intAt D (· = v) := by
  intro a ha
  have hNF : (N : D.host.F) ≠ 0 := Int.cast_ne_zero.2 fun h => hN (by rw [h, Int.cast_zero]; exact zero_mem _)
  refine ⟨Ideal.mul_mem_left _ _ ha.1, ?_⟩
  have hc : finPart D (incA D c) = (1 : Af D.host.F) ⊗ₜ[D.host.F] c := rfl
  rw [map_mul, hc, ← AeUnit.idem_mul_finPart D v ha.1, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  refine GlobalTheory.HostAdeleIso.intAE_mul_mem D ?_ ha.2
  refine AddSubgroup.subset_closure ⟨_, AeUnit.inv_smul_singleV_mem v N hN, ⟨N • c, hint⟩, ?_⟩
  exact AeUnit.tmul_eq_inv_smul_tmul N hNF _ c

/- English proof (translation)
Establish `hN : N ≠ 0` using `fun h => hvN (by rw [h, Nat.cast_zero]; exact zero_mem _)`. Establish `hM : M ≠ 0` using `fun h => hvM (by rw [h, Nat.cast_zero]; exact zero_mem _)`. Apply `le_antisymm` to reduce the goal to its premises. Use `AddSubgroup.closure_mono ?_` and prove the remaining obligations. Introduce and unpack `y ⟨α, hα, h0, a, ha, x, hx, rfl⟩`.

Take `⟨b, hb⟩` from `hNI a ha`. Take `⟨h1, h2⟩` from `AlmostAll.smul_inv_mem hvN hα h0`. Use `⟨_, h1, h2, 1, rfl, b • x, L.smul_mem b hx, funext fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[AlmostAll.tmul_eq hN, ← mul_assoc, mul_comm _ a, ← hb, one_mul, Pi.smul_apply, Algebra.smul_def b]`. Use `AddSubgroup.closure_mono ?_` and prove the remaining obligations.

Introduce and unpack `y ⟨α, hα, h0, a, ha, x, hx, rfl⟩`. Take `rfl : a = 1` from `ha`. Take `⟨h1, h2⟩` from `AlmostAll.smul_inv_mem hvM hα h0`. Use `⟨_, h1, h2, (M : D.host.E), hMI, x, hx, funext fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[AlmostAll.tmul_eq hM, one_mul]`.
-/
theorem latA_eq_latV {v : Pl D} {N M : ℕ} (hvN : (N : 𝓞 D.host.F) ∉ v.asIdeal) (hvM : (M : 𝓞 D.host.F) ∉ v.asIdeal)
    (hNI : ∀ a ∈ D.host.AA, ∃ b : 𝓞 D.host.E, algebraMap _ _ b = a * N) (hMI : (M : D.host.E) ∈ D.host.AA)
    (S : HSp D) (L : Lat S) : latA S L (· = v) = latV S L (· = v) := by
  have hN : N ≠ 0 := fun h => hvN (by rw [h, Nat.cast_zero]; exact zero_mem _)
  have hM : M ≠ 0 := fun h => hvM (by rw [h, Nat.cast_zero]; exact zero_mem _)
  apply le_antisymm
  · refine AddSubgroup.closure_mono ?_
    rintro y ⟨α, hα, h0, a, ha, x, hx, rfl⟩
    obtain ⟨b, hb⟩ := hNI a ha
    obtain ⟨h1, h2⟩ := AlmostAll.smul_inv_mem hvN hα h0
    refine ⟨_, h1, h2, 1, rfl, b • x, L.smul_mem b hx, funext fun i => ?_⟩
    rw [AlmostAll.tmul_eq hN, ← mul_assoc, mul_comm _ a, ← hb, one_mul, Pi.smul_apply, Algebra.smul_def b]
  · refine AddSubgroup.closure_mono ?_
    rintro y ⟨α, hα, h0, a, ha, x, hx, rfl⟩
    obtain rfl : a = 1 := ha
    obtain ⟨h1, h2⟩ := AlmostAll.smul_inv_mem hvM hα h0
    refine ⟨_, h1, h2, (M : D.host.E), hMI, x, hx, funext fun i => ?_⟩
    rw [AlmostAll.tmul_eq hM, one_mul]

/- English proof (translation)
Introduce `hN` and use `by obtain ⟨a, b, e⟩ := (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom A) refine (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top ?_ rw [← e] exact add_mem (Ideal.mul_mem_left _ _ (by simpa using hN)) (Ideal.mul_mem_left _ _ (by simpa using hT))`.
-/
theorem notMem_of_coprime {A : Type} [CommRing A] [IsDedekindDomain A] {v : HeightOneSpectrum A} {T N : ℕ}
    (hT : (T : A) ∈ v.asIdeal) (h : Nat.Coprime N T) : (N : A) ∉ v.asIdeal := fun hN => by
  obtain ⟨a, b, e⟩ := (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom A)
  refine (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top ?_
  rw [← e]
  exact add_mem (Ideal.mul_mem_left _ _ (by simpa using hN)) (Ideal.mul_mem_left _ _ (by simpa using hT))

/- English proof (translation)
Establish `hsq : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E)` using `D.host.sqrtMinusD_sq`. Establish `hint : IsIntegral ℤ D.host.sqrtMinusD`. Use `IsIntegral.of_pow two_pos ?_` and prove the remaining obligations. Rewrite using `[hsq]`. Conclude with `(isIntegral_natCast _).neg`.

Establish `hdp : D.host.d.Prime` using `D.host.hyp.2.1`. Establish `hd0 : (D.host.d : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 hdp.ne_zero`. Establish `h0 : D.host.sqrtMinusD ≠ 0` using `fun e => by`. Rewrite `hsq` using `[e]`. Conclude with `hd0 (by simpa using hsq.symm)`.

Establish `hc0 : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Establish `hdT : Nat.Coprime D.host.d T` using `(Nat.coprime_primes hdp hT).2 hd.symm`. Use `⟨fun a ha => ⟨?_, ?_⟩, latA_eq_latV (notMem_of_coprime hv (GlobalTheory.TwV.HalfDiffInt.absNorm_coprime D hT h2 hq hd)) (notMem_of_coprime hv hc) (fun a ha => ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem _) ha) (ReciprocityTh …` and prove the remaining obligations. Use `incA_mul_mem_intAt (N := ((Ideal.absNorm D.host.ccK * D.host.d : ℕ) : ℤ)) (by rw [Int.cast_natCast]; exact notMem_of_coprime hv (Nat.Coprime.mul_left hc hdT)) ?_ a ha` and prove the remaining obligations. Use `hint using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[zsmul_eq_mul, Int.cast_natCast, Nat.cast_mul, Host.xi0]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-hsq`. Use `incA_mul_mem_intAt (N := 1) (by rw [Int.cast_one]; exact (Ideal.ne_top_iff_one _).1 p.v.isPrime.ne_top) ?_ a ha` and prove the remaining obligations. Rewrite using `[one_smul, Host.xi0, inv_div, div_neg, div_one]`.

Conclude with `((isIntegral_natCast _).mul hint).neg`.
-/
theorem unitAA_of_prime {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) {T : ℕ} (hT : T.Prime) (hv : (T : 𝓞 D.host.F) ∈ p.v.asIdeal) (h2 : T ∉ D.host.small) (hq : T ≠ D.host.q)
    (hd : T ≠ D.host.d) (hc : Nat.Coprime (Ideal.absNorm D.host.ccK) T) : p.UnitAA := by
  have hsq : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqrtMinusD_sq
  have hint : IsIntegral ℤ D.host.sqrtMinusD := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hsq]
    exact (isIntegral_natCast _).neg
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hd0 : (D.host.d : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hdp.ne_zero
  have h0 : D.host.sqrtMinusD ≠ 0 := fun e => by
    rw [e] at hsq
    exact hd0 (by simpa using hsq.symm)
  have hc0 : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hdT : Nat.Coprime D.host.d T := (Nat.coprime_primes hdp hT).2 hd.symm
  refine ⟨fun a ha => ⟨?_, ?_⟩, latA_eq_latV (notMem_of_coprime hv (GlobalTheory.TwV.HalfDiffInt.absNorm_coprime D hT h2 hq hd))
    (notMem_of_coprime hv hc) (fun a ha => ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem _) ha) (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D)⟩
  · refine incA_mul_mem_intAt (N := ((Ideal.absNorm D.host.ccK * D.host.d : ℕ) : ℤ))
      (by rw [Int.cast_natCast]; exact notMem_of_coprime hv (Nat.Coprime.mul_left hc hdT)) ?_ a ha
    convert hint using 1
    rw [zsmul_eq_mul, Int.cast_natCast, Nat.cast_mul, Host.xi0]
    field_simp
    linear_combination -hsq
  · refine incA_mul_mem_intAt (N := 1)
      (by rw [Int.cast_one]; exact (Ideal.ne_top_iff_one _).1 p.v.isPrime.ne_top) ?_ a ha
    rw [one_smul, Host.xi0, inv_div, div_neg, div_one]
    exact ((isIntegral_natCast _).mul hint).neg

open GlobalTheory.Mem GlobalTheory.Mem.Col2 in

/- English proof (translation)
Establish `hT : (B.T u).Prime` using `l.pr.T_prime u`. Establish `h1 : Nat.Coprime (B.T u) (B.host.QS * B.host.q * B.host.d)`. Rewrite using `[Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, B.T_cond u, Nat.gcd_one_left]`. Establish `key : ∀ m, m ∣ B.host.QS * B.host.q * B.host.d → B.T u ≠ m` using `fun m hm e => (Nat.Prime.coprime_iff_not_dvd hT).1 h1 (e ▸ hm)`. Use `unitAA_of_prime p hT hv (UpperTheory.Small.not_mem_of_mod B.host (B.T_cond u)) (key _ ?_) (key _ ?_) ?_` and prove the remaining obligations.

Conclude with `Dvd.dvd.mul_right (Dvd.intro_left _ rfl) _`. Conclude with `Dvd.intro_left _ rfl`. Use `show Nat.Coprime (Ideal.absNorm B.host.ccK) _`. Rewrite using `[B.ccK_top, Ideal.absNorm_top]`. Conclude with `Nat.coprime_one_left _`.
-/
theorem unitAA_level {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt (I.rec7 l Z) k)
    (hv : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ p.v.asIdeal) : p.UnitAA := by
  have hT : (B.T u).Prime := l.pr.T_prime u
  have h1 : Nat.Coprime (B.T u) (B.host.QS * B.host.q * B.host.d) := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, B.T_cond u, Nat.gcd_one_left]
  have key : ∀ m, m ∣ B.host.QS * B.host.q * B.host.d → B.T u ≠ m := fun m hm e =>
    (Nat.Prime.coprime_iff_not_dvd hT).1 h1 (e ▸ hm)
  refine unitAA_of_prime p hT hv (UpperTheory.Small.not_mem_of_mod B.host (B.T_cond u)) (key _ ?_) (key _ ?_) ?_
  · exact Dvd.dvd.mul_right (Dvd.intro_left _ rfl) _
  · exact Dvd.intro_left _ rfl
  · show Nat.Coprime (Ideal.absNorm B.host.ccK) _
    rw [B.ccK_top, Ideal.absNorm_top]
    exact Nat.coprime_one_left _

end GlobalTheory.FinPl.UnitAt

end
