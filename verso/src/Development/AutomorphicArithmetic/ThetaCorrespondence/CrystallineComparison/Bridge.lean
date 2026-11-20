import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.ContinuousToBdRPlus
import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.IsCrisDRAToBdRPlusIff

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open Reformulated.AutPerF Ideal

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R] [IsDomain R] [ValuationRing R] [CharZero R]
  [IsAlgClosed (FractionRing R)]

structure IsCrisDRF (f : Bcris p R →+* BdR p R) : Prop where
  on0 : ∀ a : AcrisZero p R, f (algebraMap (Acris p R) (Bcris p R) (algebraMap (AcrisZero p R) (Acris p R) a)) =
    algebraMap (BdRPlus p R) (BdR p R) (algebraMap (AinfInv p R) (BdRPlus p R) (a : AinfInv p R))
  bdd : ∀ n : ℕ, ∃ N : ℕ, ∀ x : Acris p R, ∃ (y : BdRPlus p R) (a : Ainf p R),
    f (algebraMap (Acris p R) (Bcris p R) x) = algebraMap (BdRPlus p R) (BdR p R) y ∧
      BdRPlus.eval p R n ((p : BdRPlus p R) ^ N * y) =
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) a)

/- English proof (translation)
Use `⟨fun a => ?_, fun n => ⟨n, fun x => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Bcris.toBdR_algebraMap_acris, Acris.toBdRPlus_algebraMap_zero]`. Take `⟨b, hb⟩` from `AcrisZero.exists_p_pow_mul_eq n (Acris.toRange p R n x)`. Use `⟨Acris.toBdRPlus p R x, b, Bcris.toBdR_algebraMap_acris x, ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg Subtype.val hb`.

Simplify using `only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast, RingHom.coe_rangeRestrict] at h1`. Rewrite using `[map_mul, map_pow, map_natCast, Acris.eval_toBdRPlus, h1]`. Both sides reduce to the same expression.
-/
theorem isCrisDRF_toBdR : IsCrisDRF (Bcris.toBdR p R) := by
  refine ⟨fun a => ?_, fun n => ⟨n, fun x => ?_⟩⟩
  · rw [Bcris.toBdR_algebraMap_acris, Acris.toBdRPlus_algebraMap_zero]
  · obtain ⟨b, hb⟩ := AcrisZero.exists_p_pow_mul_eq n (Acris.toRange p R n x)
    refine ⟨Acris.toBdRPlus p R x, b, Bcris.toBdR_algebraMap_acris x, ?_⟩
    have h1 := congrArg Subtype.val hb
    simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast, RingHom.coe_rangeRestrict] at h1
    rw [map_mul, map_pow, map_natCast, Acris.eval_toBdRPlus, h1]
    rfl

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap (BdRPlus p R) (BdR p R))` using `IsFractionRing.injective _ _`. Take `⟨N, hN⟩` from `hf.bdd n`. Use `set T := (AcrisZero.toQuot p R n).range`. Establish `key : ∀ k : ℕ, ∃ c : Ainf p R, BdRPlus.eval p R n y - BdRPlus.eval p R n (Acris.toBdRPlus p R x) = (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ k * Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) c)`. Introduce `k`.

Take `⟨a0, z, hz⟩` from `Acris.exists_eq_add (N + n + k) x`. Take `⟨yz, az, hyz, haz⟩` from `hN z`. Take `⟨bz, hbz⟩` from `AcrisZero.exists_p_pow_mul_eq n (Acris.toRange p R n z)`. Establish `hbz'` using `congrArg Subtype.val hbz`. Simplify using `only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast, RingHom.coe_rangeRestrict] at hbz'`.

Establish `hy2 : y = algebraMap (AinfInv p R) (BdRPlus p R) (a0 : AinfInv p R) + (p : BdRPlus p R) ^ (N + n + k) * yz`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[← hy, hz]`. Simplify using `only [map_add, map_mul, map_pow, map_natCast]`. Rewrite using `[hf.on0 a0, hyz]`.

Establish `hx2 : Acris.toBdRPlus p R x = algebraMap (AinfInv p R) (BdRPlus p R) (a0 : AinfInv p R) + (p : BdRPlus p R) ^ (N + n + k) * Acris.toBdRPlus p R z`. Rewrite using `[hz, map_add, map_mul, map_pow, map_natCast, Acris.toBdRPlus_algebraMap_zero]`. Use `⟨(p : Ainf p R) ^ n * az - (p : Ainf p R) ^ N * bz, ?_⟩` and prove the remaining obligations. Establish `e1 : BdRPlus.eval p R n ((p : BdRPlus p R) ^ N * yz) = Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) az)` using `haz`. Establish `e2 : (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * BdRPlus.eval p R n (Acris.toBdRPlus p R z) = Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) bz)`.

Rewrite using `[Acris.eval_toBdRPlus, hbz']`. Both sides reduce to the same expression. Rewrite `e1` using `[map_mul, map_pow, map_natCast]`. Rewrite using `[hy2, hx2]`. Simplify using `only [map_add, map_mul, map_pow, map_natCast, map_sub]`.

Rewrite using `[add_sub_add_left_eq_sub, ← mul_sub]`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [e1, e2]`. Establish `hmem : ∀ c : Ainf p R, Ideal.Quotient.mk (AinfInv.kerTheta p R ^ n) (algebraMap (Ainf p R) (AinfInv p R) c) ∈ T` using `fun c => ⟨algebraMap (Ainf p R) (AcrisZero p R) c, rfl⟩`.

Take `⟨c0, hc0⟩` from `key 0`. Rewrite `hc0` using `[pow_zero, one_mul]`. Establish `hH : IsHausdorff (span {(p : T)}) T` using `inferInstance`. Establish `h0 : (⟨_, hmem c0⟩ : T) = 0`. Apply `hH.haus` to reduce the goal to its premises.

Introduce `k`. Take `⟨c, hc⟩` from `key k`. Establish `hx : (⟨_, hmem c0⟩ : T) = ((p : T) ^ k) • (⟨_, hmem c⟩ : T)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [smul_eq_mul, Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast]`.

Rewrite using `[← hc0, hc]`. Rewrite using `[SModEq.zero, hx]`. Conclude with `Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k) Submodule.mem_top`. Establish `h1` using `congrArg Subtype.val h0`. Simplify using `only [ZeroMemClass.coe_zero] at h1`.

Rewrite `h1` using `[← hc0]`. Conclude with `sub_eq_zero.1 h1`.
-/
theorem eval_eq_of_isCrisDRF {f : Bcris p R →+* BdR p R} (hf : IsCrisDRF f) (x : Acris p R) (y : BdRPlus p R)
    (hy : f (algebraMap (Acris p R) (Bcris p R) x) = algebraMap (BdRPlus p R) (BdR p R) y) (n : ℕ) :
    BdRPlus.eval p R n y = BdRPlus.eval p R n (Acris.toBdRPlus p R x) := by
  have hinj : Function.Injective (algebraMap (BdRPlus p R) (BdR p R)) := IsFractionRing.injective _ _
  obtain ⟨N, hN⟩ := hf.bdd n

  set T := (AcrisZero.toQuot p R n).range
  have key : ∀ k : ℕ, ∃ c : Ainf p R, BdRPlus.eval p R n y - BdRPlus.eval p R n (Acris.toBdRPlus p R x) =
      (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ k *
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) c) := by
    intro k
    obtain ⟨a0, z, hz⟩ := Acris.exists_eq_add (N + n + k) x
    obtain ⟨yz, az, hyz, haz⟩ := hN z
    obtain ⟨bz, hbz⟩ := AcrisZero.exists_p_pow_mul_eq n (Acris.toRange p R n z)
    have hbz' := congrArg Subtype.val hbz
    simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast, RingHom.coe_rangeRestrict] at hbz'
    have hy2 : y = algebraMap (AinfInv p R) (BdRPlus p R) (a0 : AinfInv p R) + (p : BdRPlus p R) ^ (N + n + k) * yz := by
      apply hinj
      rw [← hy, hz]
      simp only [map_add, map_mul, map_pow, map_natCast]
      rw [hf.on0 a0, hyz]
    have hx2 : Acris.toBdRPlus p R x =
        algebraMap (AinfInv p R) (BdRPlus p R) (a0 : AinfInv p R) + (p : BdRPlus p R) ^ (N + n + k) * Acris.toBdRPlus p R z := by
      rw [hz, map_add, map_mul, map_pow, map_natCast, Acris.toBdRPlus_algebraMap_zero]
    refine ⟨(p : Ainf p R) ^ n * az - (p : Ainf p R) ^ N * bz, ?_⟩
    have e1 : BdRPlus.eval p R n ((p : BdRPlus p R) ^ N * yz) =
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) az) := haz
    have e2 : (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * BdRPlus.eval p R n (Acris.toBdRPlus p R z) =
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) bz) := by
      rw [Acris.eval_toBdRPlus, hbz']
      rfl
    rw [map_mul, map_pow, map_natCast] at e1
    rw [hy2, hx2]
    simp only [map_add, map_mul, map_pow, map_natCast, map_sub]
    rw [add_sub_add_left_eq_sub, ← mul_sub]
    calc (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ (N + n + k) * (BdRPlus.eval p R n yz - BdRPlus.eval p R n (Acris.toBdRPlus p R z))
        = (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ k *
            ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ N * BdRPlus.eval p R n yz)
              - (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ N * ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * BdRPlus.eval p R n (Acris.toBdRPlus p R z))) := by
          ring
      _ = _ := by rw [e1, e2]

  have hmem : ∀ c : Ainf p R, Ideal.Quotient.mk (AinfInv.kerTheta p R ^ n) (algebraMap (Ainf p R) (AinfInv p R) c) ∈ T :=
    fun c => ⟨algebraMap (Ainf p R) (AcrisZero p R) c, rfl⟩
  obtain ⟨c0, hc0⟩ := key 0
  rw [pow_zero, one_mul] at hc0
  have hH : IsHausdorff (span {(p : T)}) T := inferInstance
  have h0 : (⟨_, hmem c0⟩ : T) = 0 := by
    apply hH.haus
    intro k
    obtain ⟨c, hc⟩ := key k
    have hx : (⟨_, hmem c0⟩ : T) = ((p : T) ^ k) • (⟨_, hmem c⟩ : T) := by
      apply Subtype.ext
      simp only [smul_eq_mul, Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast]
      rw [← hc0, hc]
    rw [SModEq.zero, hx]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k) Submodule.mem_top
  have h1 := congrArg Subtype.val h0
  simp only [ZeroMemClass.coe_zero] at h1
  rw [← hc0] at h1
  exact sub_eq_zero.1 h1

/- English proof (translation)
Rewrite using `[← isCrisDRA_toBdRPlus_iff]`. Introduce `x`. Take `⟨N0, hN0⟩` from `hf.bdd 0`. Take `⟨y, -, hy, -⟩` from `hN0 x`. Rewrite using `[hy]`.

Use `congr 1`. Conclude with `BdRPlus.ext_eval fun n => eval_eq_of_isCrisDRF hf x y hy n`.
-/
theorem eq_toBdR_of_isCrisDRF {f : Bcris p R →+* BdR p R} (hf : IsCrisDRF f) : f = Bcris.toBdR p R := by
  rw [← isCrisDRA_toBdRPlus_iff]
  intro x
  obtain ⟨N0, hN0⟩ := hf.bdd 0
  obtain ⟨y, -, hy, -⟩ := hN0 x
  rw [hy]
  congr 1
  exact BdRPlus.ext_eval fun n => eval_eq_of_isCrisDRF hf x y hy n

/- English proof (translation)
Assemble the required witnesses or components as `⟨eq_toBdR_of_isCrisDRF, fun h => h ▸ isCrisDRF_toBdR⟩`.
-/
theorem isCrisDRF_iff (f : Bcris p R →+* BdR p R) : IsCrisDRF f ↔ f = Bcris.toBdR p R :=
  ⟨eq_toBdR_of_isCrisDRF, fun h => h ▸ isCrisDRF_toBdR⟩

end Formalism.BasicNotions.CmpTie.Incl
