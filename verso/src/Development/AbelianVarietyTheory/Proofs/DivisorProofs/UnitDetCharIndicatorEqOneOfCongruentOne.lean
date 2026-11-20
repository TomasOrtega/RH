import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen

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

namespace GlobalTheory.StdRead.CongOneChar

open GlobalTheory.BotClassDict (finQ)
open GlobalTheory.StdRead.CharVal

variable {D : D7}

/- English proof (translation)
Use `AddSubgroup.closure_mono ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨b, hb, t, ht, rfl⟩`. Conclude with `⟨b, h hb, t, ht, rfl⟩`.
-/
theorem hat_mono {I J : Ideal (𝓞 D.host.E)} (h : I ≤ J) {x : Formalism.MainNotions.StandardLatticesGL3.AE D} (hx : x ∈ hatId D I) :
    x ∈ hatId D J := by
  refine AddSubgroup.closure_mono ?_ hx
  rintro _ ⟨b, hb, t, ht, rfl⟩
  exact ⟨b, h hb, t, ht, rfl⟩

/- English proof (translation)
Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨b, -, t, ht, rfl⟩` from `hy`. Conclude with `mul_mem (inc_int b) ht`. Consider the case `zero => exact zero_mem _`.

Consider the case `add a b _ _ ha hb => exact add_mem ha hb`. Consider the case `neg a _ ha => exact neg_mem ha`.
-/
theorem hat_int {I : Ideal (𝓞 D.host.E)} {x : Formalism.MainNotions.StandardLatticesGL3.AE D} (hx : x ∈ hatId D I) : x ∈ OhE D := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, -, t, ht, rfl⟩ := hy
    exact mul_mem (inc_int b) ht
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | neg a _ ha => exact neg_mem ha

/- English proof (translation)
Take `⟨w, -, hw⟩` from `StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_surj z`. Conclude with `⟨finQ D w, by rw [toE_finQ, hw]⟩`.
-/
theorem toE_surj (z : EAf D) : ∃ y, toE D y = z := by
  obtain ⟨w, -, hw⟩ := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_surj z
  exact ⟨finQ D w, by rw [toE_finQ, hw]⟩

/- English proof (translation)
Introduce `_ _ h` and use `(GlobalTheory.BotFormula.toAfE D).injective ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h)`.
-/
theorem toE_inj : Function.Injective (toE D) := fun _ _ h =>
  (GlobalTheory.BotFormula.toAfE D).injective ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h)

/- English proof (translation)
Establish `e : (⟨_, hu⟩ : OhE D) = 1 + ⟨a, ha⟩ * ⟨b, hb⟩` using `Subtype.ext rfl`. Rewrite using `[e, RingHom.map_add, RingHom.map_mul, h0, RingHom.map_one, add_zero]`.
-/
theorem rho_one_add (Q : Formalism.L2.DIV.Pl D.host.E) {a b : Formalism.MainNotions.StandardLatticesGL3.AE D} (ha : a ∈ OhE D) (hb : b ∈ OhE D)
    (hu : 1 + a * b ∈ OhE D) (h0 : rho Q ⟨a, ha⟩ * rho Q ⟨b, hb⟩ = 0) : rho Q ⟨_, hu⟩ = 1 := by
  have e : (⟨_, hu⟩ : OhE D) = 1 + ⟨a, ha⟩ * ⟨b, hb⟩ := Subtype.ext rfl
  rw [e, RingHom.map_add, RingHom.map_mul, h0, RingHom.map_one, add_zero]

/- English proof (translation)
Establish `hU : IsUnit (⟨toE D u, (toE_int_iff u).2 hu⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E)` using `Formalism.L2.DIV.isUnit_of_resS_ne_zero D.sp.cm _ fun Q => h Q`. Take `⟨w, hw⟩` from `hU.exists_right_inv`. Take `⟨v, hv⟩` from `toE_surj (w : EAf D)`. Use `⟨v, (toE_int_iff v).1 (hv ▸ w.2), toE_inj ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.map_mul, RingHom.map_one, hv]`.

Conclude with `congrArg Subtype.val hw`.
-/
theorem exists_inv {u : Formalism.MainNotions.StandardLatticesGL3.AE D} (hu : u ∈ OhE D) (h : ∀ Q : Formalism.L2.DIV.Pl D.host.E, rho Q ⟨u, hu⟩ ≠ 0) :
    ∃ v ∈ OhE D, u * v = 1 := by
  have hU : IsUnit (⟨toE D u, (toE_int_iff u).2 hu⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) :=
    Formalism.L2.DIV.isUnit_of_resS_ne_zero D.sp.cm _ fun Q => h Q
  obtain ⟨w, hw⟩ := hU.exists_right_inv
  obtain ⟨v, hv⟩ := toE_surj (w : EAf D)
  refine ⟨v, (toE_int_iff v).1 (hv ▸ w.2), toE_inj ?_⟩
  rw [RingHom.map_mul, RingHom.map_one, hv]
  exact congrArg Subtype.val hw

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D e 𝔪 hG ν hK k P hP`. Establish `hm1` using `one_sub_eps_mod hG`. Take `⟨S, c, he, hc, h𝔪, -⟩` from `hG`. Establish `hO` using `eps_int he`. Establish `h2` using `eps_conj he`.

Establish `hte` using `toE_finQ e`. Establish `hPO : ∀ i j, P i j ∈ OhE D` using `fun i j => by`. Establish `h1 : (1 : Matrix (Fin k) (Fin k) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j ∈ OhE D`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`.

Conclude with `one_mem _`. Conclude with `zero_mem _`. Establish `h3` using `add_mem (hat_int (hP i j)) h1`. Rewrite `h3` using `[Matrix.sub_apply, sub_add_cancel]`. Then use the resulting hypothesis. Establish `hm` using `GlobalTheory.FunObj.StdDatum.DetCong.det_sub_one_mem_hatId_of P hPO hP`.

Establish `hdet : (P.map (toE D)).det = toE D P.det` using `(RingHom.map_det (toE D) _).symm`. Establish `hmO` using `hat_int hm`. Establish `huO : 1 + finQ D e * (P.det - 1) ∈ OhE D` using `add_mem (one_mem _) (mul_mem hO hmO)`. Take `⟨v, hvO, huv⟩` from `exists_inv huO fun Q => by`. Use `Q.isPrime` as an intermediate fact.

Establish `h0 : rho Q ⟨_, hO⟩ * rho Q ⟨_, hmO⟩ = 0`. Distinguish the cases in `hQ : Q ∈ S`. Establish `hle : 𝔪 ≤ Q.asIdeal`. Rewrite using `[h𝔪]`. Conclude with `(Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Formalism.L2.DIV.Pl D.host.E => w.asIdeal ^ c w) hQ)).trans (Ideal.pow_le_self (hc Q hQ).ne')`.

Take `⟨_, h5⟩` from `rho_hat Q (hat_mono hle hm)`. Rewrite using `[h5, mul_zero]`. Establish `h5 : rho Q ⟨_, hO⟩ = Formalism.L2.DIV.resS D.host.F Q ⟨_, StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he⟩` using `congrArg (Formalism.L2.DIV.resS D.host.F Q) (Subtype.ext hte)`. Rewrite using `[h5, StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.res_off he _ hQ, zero_mul]`. Establish `h6 : rho Q ⟨_, huO⟩ = 1` using `rho_one_add Q hO hmO huO h0`.

Rewrite using `[h6]`. Conclude with `one_ne_zero`. Establish `hm'` using `hat_mul hm (GlobalTheory.FunObj.StdDatum.DetCong.sgA_mem_hatId hm1)`. Rewrite `hm'` using `[map_sub, map_one]`. Establish `hm''` using `GlobalTheory.FunObj.StdDatum.mul_mem_hatId hO hm'`.

Generalize the expression as in `finQ D e = ε at hO h2 hte huO huv hm''`. Generalize the expression as in `P.det = d at hdet huO huv hm''`. Set `y : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ` to `⟨_, _, huv, by rw [mul_comm, huv]⟩`. Establish `hyv : (y : Formalism.MainNotions.StandardLatticesGL3.AE D) = 1 + ε * (d - 1)` using `rfl`. Establish `hyi : ((y⁻¹ : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) = v` using `rfl`.

Take `⟨x, hx, hx1, hx2⟩` from `exists_finIdl y`. Establish `hU : IsUnitDet e (P.map (toE D)) x`. Use `⟨hx.1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hx1, show (y : Formalism.MainNotions.StandardLatticesGL3.AE D) = (1 - ε) + ε * d by rw [hyv]; ring, hdet, RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_one, hte]`. Rewrite using `[hx2, toE_int_iff, hyi]`.

Conclude with `hvO`. Establish `hν : ν x = 1` using `hK x y hx ⟨huO, hvO⟩ (by`. Use `hm'' using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hyv]`. Take the linear combination `(d - 1) * h2)`.

Rewrite using `[unitChar_eq ν e _ hU, hν, inv_one, Circle.coe_one]`.
-/
theorem unitChar_cong : ∀ {D : D7} (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 → ∀ ν : (AE D)ˣ →* Circle, KillsCong ν 𝔪 →
  ∀ {k : ℕ} (P : Matrix (Fin k) (Fin k) (Formalism.MainNotions.StandardLatticesGL3.AE D)), (∀ i j, (P - 1) i j ∈ hatId D 𝔪) →
  unitChar ν e (P.map (toE D)) = 1 := by
  intro D e 𝔪 hG ν hK k P hP
  have hm1 := one_sub_eps_mod hG
  obtain ⟨S, c, he, hc, h𝔪, -⟩ := hG
  have hO := eps_int he
  have h2 := eps_conj he
  have hte := toE_finQ e
  have hPO : ∀ i j, P i j ∈ OhE D := fun i j => by
    have h1 : (1 : Matrix (Fin k) (Fin k) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j ∈ OhE D := by
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _
    have h3 := add_mem (hat_int (hP i j)) h1
    rwa [Matrix.sub_apply, sub_add_cancel] at h3
  have hm := GlobalTheory.FunObj.StdDatum.DetCong.det_sub_one_mem_hatId_of P hPO hP
  have hdet : (P.map (toE D)).det = toE D P.det := (RingHom.map_det (toE D) _).symm
  have hmO := hat_int hm
  have huO : 1 + finQ D e * (P.det - 1) ∈ OhE D := add_mem (one_mem _) (mul_mem hO hmO)
  obtain ⟨v, hvO, huv⟩ := exists_inv huO fun Q => by
    have := Q.isPrime
    have h0 : rho Q ⟨_, hO⟩ * rho Q ⟨_, hmO⟩ = 0 := by
      by_cases hQ : Q ∈ S
      · have hle : 𝔪 ≤ Q.asIdeal := by
          rw [h𝔪]
          exact (Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Formalism.L2.DIV.Pl D.host.E => w.asIdeal ^ c w) hQ)).trans
            (Ideal.pow_le_self (hc Q hQ).ne')
        obtain ⟨_, h5⟩ := rho_hat Q (hat_mono hle hm)
        rw [h5, mul_zero]
      · have h5 : rho Q ⟨_, hO⟩ = Formalism.L2.DIV.resS D.host.F Q ⟨_, StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he⟩ :=
          congrArg (Formalism.L2.DIV.resS D.host.F Q) (Subtype.ext hte)
        rw [h5, StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.res_off he _ hQ, zero_mul]
    have h6 : rho Q ⟨_, huO⟩ = 1 := rho_one_add Q hO hmO huO h0
    rw [h6]
    exact one_ne_zero
  have hm' := hat_mul hm (GlobalTheory.FunObj.StdDatum.DetCong.sgA_mem_hatId hm1)
  rw [map_sub, map_one] at hm'
  have hm'' := GlobalTheory.FunObj.StdDatum.mul_mem_hatId hO hm'
  generalize finQ D e = ε at hO h2 hte huO huv hm''
  generalize P.det = d at hdet huO huv hm''
  let y : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ := ⟨_, _, huv, by rw [mul_comm, huv]⟩
  have hyv : (y : Formalism.MainNotions.StandardLatticesGL3.AE D) = 1 + ε * (d - 1) := rfl
  have hyi : ((y⁻¹ : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) = v := rfl
  obtain ⟨x, hx, hx1, hx2⟩ := exists_finIdl y
  have hU : IsUnitDet e (P.map (toE D)) x := by
    refine ⟨hx.1, ?_, ?_⟩
    · rw [hx1, show (y : Formalism.MainNotions.StandardLatticesGL3.AE D) = (1 - ε) + ε * d by rw [hyv]; ring, hdet, RingHom.map_add, RingHom.map_sub,
        RingHom.map_mul, RingHom.map_one, hte]
    · rw [hx2, toE_int_iff, hyi]
      exact hvO
  have hν : ν x = 1 := hK x y hx ⟨huO, hvO⟩ (by
    convert hm'' using 1
    rw [hyv]
    linear_combination (d - 1) * h2)
  rw [unitChar_eq ν e _ hU, hν, inv_one, Circle.coe_one]

end GlobalTheory.StdRead.CongOneChar
