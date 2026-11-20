import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LemGBInImgIff
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.GammaPi0EqPi0MulUnit
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ConstantLeRpowOfThreeLe
import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.AcoordSumVecMul
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

namespace ArcLengthTwoLifting

/- English proof (translation)
Take `⟨y₂, hy₂, hy₂c, rfl⟩` from `hn₂`. Rewrite using `[one_smul]`. Establish `hy₂' : y₂ ∈ W.N T₂ ∧ ∀ δ ∈ W.DelF, W.γD T₂ δ y₂ = y₂` using `hy₂`. Establish `hNl : y₂ ∈ W.Nl T₂ c` using `Submodule.mem_map.2 ⟨y₂, hy₂'.1, by rw [LinearMap.smul_apply, LinearMap.id_apply, hy₂c]⟩`. Take `⟨x₁, hx₁, hx₁F⟩` from `Submodule.mem_map.1 (hk y₂ hNl hy₂'.2)`.

Take `⟨z₁, hz₁N, hz₁⟩` from `Submodule.mem_map.1 hx₁`. Rewrite `hz₁` using `[LinearMap.smul_apply, LinearMap.id_apply]`. Establish `hx₁N : x₁ ∈ W.N T₁` using `by rw [← hz₁]; exact (W.N T₁).smul_mem _ hz₁N`. Establish `hx₁c : (letE c : LetA O n) • x₁ = x₁`. Rewrite using `[← hz₁, smul_smul, Formalism.MainNotions.WachCoordinates.Br.letE_mul_self]`.

Establish `hx₁F' : W.map F x₁ = lA W ^ rr • y₂` using `hx₁F`. Take `⟨-, -, hU⟩` from `lemG_units W hcase hP9 hT₁ hO hOv hinj`. Use `set u : Oˣ := hU.unit with hu`. Establish `hγl : ∀ (δ : W.Gam) (x : W.DD T₁), W.γD T₁ δ ((letE c : LetA O n) • x) = (letE c : LetA O n) • W.γD T₁ δ x`. Introduce `δ x`.

Rewrite using `[← algebraMap_smul W.EE (letE c : LetA O n) x, W.γD_smul, W.γE_ext, algebraMap_smul]`. Use `congr 1`. Conclude with `GS.γA_letE W δ c`. Use `set n₁ : W.DD T₁ := ((u⁻¹ : Oˣ) : O) • ∑ δ ∈ W.DelF, W.γD T₁ δ x₁ with hn₁`. Use `⟨n₁, ⟨n₁, ?_, ?_, (one_smul _ _).symm⟩, ?_⟩` and prove the remaining obligations.

Use `show n₁ ∈ W.N T₁ ∧ ∀ δ ∈ W.DelF, W.γD T₁ δ n₁ = n₁`. Use `⟨?_, fun δ' hδ' => ?_⟩` and prove the remaining obligations. Rewrite using `[hn₁, ← algebraMap_smul (LetA O n)]`. Conclude with `(W.N T₁).smul_mem _ ((W.N T₁).sum_mem fun δ _ => W.N_Γ T₁ δ x₁ hx₁N)`. Rewrite using `[hn₁, map_smul, map_sum]`.

Use `congr 1`. Use `Finset.sum_nbij' (δ' * ·) (δ'⁻¹ * ·) (fun g hg => TypesA.delF_mul W hδ' hg) (fun g hg => TypesA.delF_mul W (TypesA.delF_inv W hδ') hg) (fun g _ => by simp) (fun g _ => by simp) (fun g _ => ?_)` and prove the remaining obligations. Rewrite using `[W.γD_mul]`. Rewrite using `[hn₁, smul_comm, Finset.smul_sum]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun δ _ => ?_` and prove the remaining obligations. Rewrite using `[← hγl, hx₁c]`. Establish `hγ₂ : ∀ δ ∈ W.DelF, W.γD T₂ δ (W.map F x₁) = lA W ^ rr • y₂`. Introduce `δ hδ`. Rewrite using `[hx₁F', TypesA.lA_pow_smul, map_nsmul, hy₂'.2 δ hδ]`.

Rewrite using `[hn₁, ← algebraMap_smul W.EE, map_smul, map_sum]`. Simplify using `only [W.map_γ]`. Rewrite using `[Finset.sum_congr rfl hγ₂, Finset.sum_const, algebraMap_smul, ← Nat.cast_smul_eq_nsmul O, smul_smul]`. Establish `: ((u⁻¹ : Oˣ) : O) * (W.DelF.card : O) = 1`. Rewrite using `[hu]`.

Conclude with `hU.val_inv_mul`. Rewrite using `[this, one_smul]`.
-/
theorem liftΔ [FiniteDimensional Qp LL] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x))
    (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x) (hinj : Function.Injective (algebraMap O LL))
    {T₁ T₂ : LocLat G Qp LL O} (hT₁ : IsCrys PD T₁.ρ) (F : LatHom T₁.L T₂.L) (c : ZMod n) (rr : ℕ)
    (hk : Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr)) (n₂ : W.DD T₂) (hn₂ : InFNc W T₂ c 1 n₂) :
    ∃ n₁, InFNc W T₁ c 1 n₁ ∧ W.map F n₁ = lA W ^ rr • n₂ := by
  classical
  obtain ⟨y₂, hy₂, hy₂c, rfl⟩ := hn₂
  rw [one_smul]
  have hy₂' : y₂ ∈ W.N T₂ ∧ ∀ δ ∈ W.DelF, W.γD T₂ δ y₂ = y₂ := hy₂
  have hNl : y₂ ∈ W.Nl T₂ c :=
    Submodule.mem_map.2 ⟨y₂, hy₂'.1, by rw [LinearMap.smul_apply, LinearMap.id_apply, hy₂c]⟩
  obtain ⟨x₁, hx₁, hx₁F⟩ := Submodule.mem_map.1 (hk y₂ hNl hy₂'.2)
  obtain ⟨z₁, hz₁N, hz₁⟩ := Submodule.mem_map.1 hx₁
  rw [LinearMap.smul_apply, LinearMap.id_apply] at hz₁
  have hx₁N : x₁ ∈ W.N T₁ := by rw [← hz₁]; exact (W.N T₁).smul_mem _ hz₁N
  have hx₁c : (letE c : LetA O n) • x₁ = x₁ := by
    rw [← hz₁, smul_smul, Formalism.MainNotions.WachCoordinates.Br.letE_mul_self]
  have hx₁F' : W.map F x₁ = lA W ^ rr • y₂ := hx₁F
  obtain ⟨-, -, hU⟩ := lemG_units W hcase hP9 hT₁ hO hOv hinj
  set u : Oˣ := hU.unit with hu
  have hγl : ∀ (δ : W.Gam) (x : W.DD T₁),
      W.γD T₁ δ ((letE c : LetA O n) • x) = (letE c : LetA O n) • W.γD T₁ δ x := by
    intro δ x
    rw [← algebraMap_smul W.EE (letE c : LetA O n) x, W.γD_smul, W.γE_ext, algebraMap_smul]
    congr 1
    exact GS.γA_letE W δ c
  set n₁ : W.DD T₁ := ((u⁻¹ : Oˣ) : O) • ∑ δ ∈ W.DelF, W.γD T₁ δ x₁ with hn₁
  refine ⟨n₁, ⟨n₁, ?_, ?_, (one_smul _ _).symm⟩, ?_⟩
  · show n₁ ∈ W.N T₁ ∧ ∀ δ ∈ W.DelF, W.γD T₁ δ n₁ = n₁
    refine ⟨?_, fun δ' hδ' => ?_⟩
    · rw [hn₁, ← algebraMap_smul (LetA O n)]
      exact (W.N T₁).smul_mem _ ((W.N T₁).sum_mem fun δ _ => W.N_Γ T₁ δ x₁ hx₁N)
    · rw [hn₁, map_smul, map_sum]
      congr 1
      refine Finset.sum_nbij' (δ' * ·) (δ'⁻¹ * ·) (fun g hg => TypesA.delF_mul W hδ' hg)
        (fun g hg => TypesA.delF_mul W (TypesA.delF_inv W hδ') hg) (fun g _ => by simp)
        (fun g _ => by simp) (fun g _ => ?_)
      rw [W.γD_mul]
  · rw [hn₁, smul_comm, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [← hγl, hx₁c]
  · have hγ₂ : ∀ δ ∈ W.DelF, W.γD T₂ δ (W.map F x₁) = lA W ^ rr • y₂ := by
      intro δ hδ
      rw [hx₁F', TypesA.lA_pow_smul, map_nsmul, hy₂'.2 δ hδ]
    rw [hn₁, ← algebraMap_smul W.EE, map_smul, map_sum]
    simp only [W.map_γ]
    rw [Finset.sum_congr rfl hγ₂, Finset.sum_const, algebraMap_smul, ← Nat.cast_smul_eq_nsmul O, smul_smul]
    have : ((u⁻¹ : Oˣ) : O) * (W.DelF.card : O) = 1 := by
      rw [hu]
      exact hU.val_inv_mul
    rw [this, one_smul]

/- English proof (translation)
Unfold `dvO`. Use `congr 1`. Use function extensionality and compare the values at `m`. Distinguish the cases in `h : m = k`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`.
-/
theorem dvO_single (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (k : Fin d) : dvO W T e b (Pi.single k 1) = dv W T e b (Pi.single k 1) := by
  unfold dvO
  congr 1
  funext m
  by_cases h : m = k
  · subst h; simp
  · simp [Pi.single_apply, h]

/- English proof (translation)
Unfold `dv`. Simplify using `only [Finset.sum_smul, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem dv_sum (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    {I : Type*} (s : Finset I) (a : I → LL) (c₀ : I → Fin d → LL) :
    dv W T e b (fun m => ∑ i ∈ s, a i * c₀ i m) = ∑ i ∈ s, a i • dv W T e b (c₀ i) := by
  unfold dv
  simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

/- English proof (translation)
Unfold `dv`. Simplify using `only [Finset.smul_sum, smul_smul]`.
-/
theorem dv_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (a : LL) (c₀ : Fin d → LL) : dv W T e b (fun m => a * c₀ m) = a • dv W T e b c₀ := by
  unfold dv
  simp only [Finset.smul_sum, smul_smul]

/- English proof (translation)
Establish `hp` using `P.first_partial_unit_eq_exp`. Take `⟨S, hS⟩` from `sub_dvd_pow_sub_pow (P.p 1) (P.u * PowerSeries.X ^ l) y`. Establish `hdiff : P.p 1 - P.u * PowerSeries.X ^ l = PowerSeries.C (l : O) * P.eps` using `by rw [hp]; ring`. Rewrite `hS` using `[hdiff]`. Establish `hexp : P.p 1 ^ y = P.u ^ y * PowerSeries.X ^ (l * y) + PowerSeries.C (l : O) * (P.eps * S)`.

Rewrite using `[← mul_assoc, ← hS, mul_pow, ← pow_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hexp, map_add, PowerSeries.coeff_C_mul]`. Establish `h0 : PowerSeries.coeff (l * y) (P.u ^ y * PowerSeries.X ^ (l * y)) = PowerSeries.constantCoeff (P.u ^ y)`. Use `PowerSeries.coeff_mul_X_pow (P.u ^ y) (l * y) 0` as an intermediate fact.

Rewrite `this` using `[zero_add, PowerSeries.coeff_zero_eq_constantCoeff]`. Conclude with `this`. Rewrite using `[h0]`. Establish `hu : IsUnit (PowerSeries.constantCoeff (P.u ^ y))` using `(P.hu.pow y).map _`. Assume the negation of the conclusion as `hne`.

Establish `hm : PowerSeries.constantCoeff (P.u ^ y) + (l : O) * PowerSeries.coeff (l * y) (P.eps * S) ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).2 hne`. Establish `hl : (l : O) * PowerSeries.coeff (l * y) (P.eps * S) ∈ IsLocalRing.maximalIdeal O` using `Ideal.mul_mem_right _ _ P.hl`. Use `(IsLocalRing.maximalIdeal O).sub_mem hm hl` as an intermediate fact. Rewrite `this` using `[add_sub_cancel_right]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 this hu`.
-/
theorem coeff_p1_pow_top_isUnit {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {l : ℕ} [Fact l.Prime]
    (P : PhiData O l) (y : ℕ) : IsUnit (PowerSeries.coeff (l * y) (P.p 1 ^ y)) := by
  have hp := P.first_partial_unit_eq_exp
  obtain ⟨S, hS⟩ := sub_dvd_pow_sub_pow (P.p 1) (P.u * PowerSeries.X ^ l) y
  have hdiff : P.p 1 - P.u * PowerSeries.X ^ l = PowerSeries.C (l : O) * P.eps := by rw [hp]; ring
  rw [hdiff] at hS
  have hexp : P.p 1 ^ y = P.u ^ y * PowerSeries.X ^ (l * y) + PowerSeries.C (l : O) * (P.eps * S) := by
    rw [← mul_assoc, ← hS, mul_pow, ← pow_mul]; ring
  rw [hexp, map_add, PowerSeries.coeff_C_mul]
  have h0 : PowerSeries.coeff (l * y) (P.u ^ y * PowerSeries.X ^ (l * y)) =
      PowerSeries.constantCoeff (P.u ^ y) := by
    have := PowerSeries.coeff_mul_X_pow (P.u ^ y) (l * y) 0
    rw [zero_add, PowerSeries.coeff_zero_eq_constantCoeff] at this
    exact this
  rw [h0]
  have hu : IsUnit (PowerSeries.constantCoeff (P.u ^ y)) := (P.hu.pow y).map _
  by_contra hne
  have hm : PowerSeries.constantCoeff (P.u ^ y) + (l : O) * PowerSeries.coeff (l * y) (P.eps * S) ∈
      IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hne
  have hl : (l : O) * PowerSeries.coeff (l * y) (P.eps * S) ∈ IsLocalRing.maximalIdeal O :=
    Ideal.mul_mem_right _ _ P.hl
  have := (IsLocalRing.maximalIdeal O).sub_mem hm hl
  rw [add_sub_cancel_right] at this
  exact (IsLocalRing.mem_maximalIdeal _).1 this hu

open Formalism.MainNotions.UnusedSlot80.SatW in

/- English proof (translation)
Take `⟨hbij, hs, hp⟩` from `hcase`. Take `⟨hring, -⟩` from `(hP9 T hT hs hp).2.2 (finrank_one_of_bij' hbij)`. Take `⟨h3, h6⟩` from `ring_clauses W hring`. Conclude with `isUnit_EE_of_UPi W (UPi_qpow W h3 h6 s)`.
-/
theorem isUnit_ps [FiniteDimensional Qp LL] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (s : ℕ) :
    IsUnit (algebraMap (LetA O n) W.EE (ps W s)) := by
  obtain ⟨hbij, hs, hp⟩ := hcase
  obtain ⟨hring, -⟩ := (hP9 T hT hs hp).2.2 (finrank_one_of_bij' hbij)
  obtain ⟨h3, h6⟩ := ring_clauses W hring
  exact isUnit_EE_of_UPi W (UPi_qpow W h3 h6 s)

/- English proof (translation)
Take `⟨h₀, hh₀⟩` from `GS.φpow_π₀ (W := W) hR 0`. Establish `h1 : W.φA W.π₀ = W.π₀ * qA W * h₀` using `by simpa using hh₀`. Establish `hJJ : Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * G₀) M = W.π₀ ^ M * qA W ^ (2 * G₀)`. Simplify using `only [Formalism.MainNotions.LiftingTheory.JJ, Finset.prod_range_one, Formalism.MainNotions.LiftingTheory.pk, pow_zero, AlgHom.one_apply]`. Both sides reduce to the same expression.

Establish `key : ((W.φA ^ 2) W.π₀) ^ (M + 2 * G₀) = W.π₀ * Λ ^ 2 * (u * W.φA (W.π₀ ^ (2 * G₀) * qA W ^ M * h₀ ^ (M + 2 * G₀)))`. Rewrite using `[pow_two, AlgHom.mul_apply, h1, ← map_pow, show (W.π₀ * qA W * h₀) ^ (M + 2 * G₀) = Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * G₀) M * (W.π₀ ^ (2 * G₀) * qA W ^ M * h₀ ^ (M + 2 * G₀)) by rw [hJJ]; ring, map_mul, hJ]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨M + 2 * G₀, _, ?_, key⟩` and prove the remaining obligations. Apply `GS.quot_mem (W := W) (W.AΔ.mul_mem (TypesA.pi0_mem_ADelta W) (W.AΔ.pow_mem hΛ 2)) hΛu` to reduce the goal to its premises.

Rewrite using `[← key]`. Conclude with `W.AΔ.pow_mem (GS.φpow_mem (W := W) 2 (TypesA.pi0_mem_ADelta W)) _`.
-/
theorem phi_sq_pi0_pow_eq_pi0_lambda_sq (W : LocWach PD LL O v n) (hR : GS.RD W) (Λ : LetA O n) (hΛ : Λ ∈ W.AΔ)
    (hΛu : IsUnit (algebraMap (LetA O n) W.EE (W.π₀ * Λ ^ 2))) (G₀ M : ℕ) (u : LetA O n) (hu : u ∈ W.AΔ)
    (hJ : W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * G₀) M) = W.π₀ * Λ ^ 2 * u) :
    ∃ N : ℕ, ∃ w ∈ W.AΔ, ((W.φA ^ 2) W.π₀) ^ N = W.π₀ * Λ ^ 2 * w := by
  obtain ⟨h₀, hh₀⟩ := GS.φpow_π₀ (W := W) hR 0
  have h1 : W.φA W.π₀ = W.π₀ * qA W * h₀ := by simpa using hh₀
  have hJJ : Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * G₀) M = W.π₀ ^ M * qA W ^ (2 * G₀) := by
    simp only [Formalism.MainNotions.LiftingTheory.JJ, Finset.prod_range_one, Formalism.MainNotions.LiftingTheory.pk, pow_zero, AlgHom.one_apply]
    rfl
  have key : ((W.φA ^ 2) W.π₀) ^ (M + 2 * G₀) =
      W.π₀ * Λ ^ 2 * (u * W.φA (W.π₀ ^ (2 * G₀) * qA W ^ M * h₀ ^ (M + 2 * G₀))) := by
    rw [pow_two, AlgHom.mul_apply, h1, ← map_pow,
      show (W.π₀ * qA W * h₀) ^ (M + 2 * G₀) =
        Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * G₀) M * (W.π₀ ^ (2 * G₀) * qA W ^ M * h₀ ^ (M + 2 * G₀)) by rw [hJJ]; ring,
      map_mul, hJ]
    ring
  refine ⟨M + 2 * G₀, _, ?_, key⟩
  apply GS.quot_mem (W := W) (W.AΔ.mul_mem (TypesA.pi0_mem_ADelta W) (W.AΔ.pow_mem hΛ 2)) hΛu
  rw [← key]
  exact W.AΔ.pow_mem (GS.φpow_mem (W := W) 2 (TypesA.pi0_mem_ADelta W)) _

/- English proof (translation)
Unfold `dv`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single m (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp), Pi.single_eq_same, one_smul]`.
-/
theorem dv_eq_sum_single (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (c₀ : Fin d → LL) : dv W T e b c₀ = ∑ m, c₀ m • dv W T e b (Pi.single m 1) := by
  unfold dv
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_eq_single m (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp), Pi.single_eq_same,
    one_smul]

/- English proof (translation)
The claim follows from `Submodule.map_mono (inf_le_inf_right _ (Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ h))`.
-/
theorem filS_anti (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (a : ZMod n) (s : ℕ) {u u' : ℤ}
    (h : u ≤ u') : FilS W T a s u' ≤ FilS W T a s u :=
  Submodule.map_mono (inf_le_inf_right _ (Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ h))

/- English proof (translation)
Introduce `j`. Establish `h1 : ∑ m, (↑(hthu.unit⁻¹) * G m) * μ m j = ↑(hthu.unit⁻¹) * ∑ m, G m * μ m j`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun m _ => by ring`. Rewrite using `[h1, hcr j]`.

Distinguish the cases in `hj : j = k₀`. Rewrite using `[if_pos hj, if_pos hj]`. Use `hthu.val_inv_mul` as an intermediate fact. Take the linear combination `P * this`. Rewrite using `[if_neg hj, if_neg hj, mul_zero]`.
-/
theorem sum_unit_inv {R : Type*} [CommRing R] {d₁ d : ℕ} (th : R) (hthu : IsUnit th) (G : Fin d₁ → R)
    (μ : Fin d₁ → Fin d → R) (k₀ : Fin d) (P : R)
    (hcr : ∀ j, ∑ m, G m * μ m j = if j = k₀ then P * th else 0) :
    ∀ j, ∑ m, (↑(hthu.unit⁻¹) * G m) * μ m j = if j = k₀ then P else 0 := by
  intro j
  have h1 : ∑ m, (↑(hthu.unit⁻¹) * G m) * μ m j = ↑(hthu.unit⁻¹) * ∑ m, G m * μ m j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [h1, hcr j]
  by_cases hj : j = k₀
  · rw [if_pos hj, if_pos hj]
    have := hthu.val_inv_mul
    linear_combination P * this
  · rw [if_neg hj, if_neg hj, mul_zero]

/- English proof (translation)
Unfold `dvO`. Rewrite using `[dv_eq_sum_single, map_sum]`. Simplify using `only [map_smul, hμ]`. Unfold `dvO`. Rewrite using `[← dv_sum W T₂ e b Finset.univ (fun m => algebraMap O LL (c₁ m)) (fun m k => algebraMap O LL (μ m k)), ← dv_smul]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using `only [← map_mul, ← map_sum, hSig k]`. Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hk, Pi.single_apply]`.
-/
theorem crisMap_dvO (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (e : ℕ)
    {d₁ d : ℕ} (b₁ : Fin d₁ → W.DD T₁) (b : Fin d → W.DD T₂) (μ : Fin d₁ → Fin d → O)
    (hμ : ∀ m, Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dv W T₁ e b₁ (Pi.single m 1)) = dvO W T₂ e b (μ m))
    (c₁ : Fin d₁ → O) (k₀ : Fin d) (P : O) (hSig : ∀ j, ∑ m, c₁ m * μ m j = if j = k₀ then P else 0) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ e b₁ c₁) = algebraMap O LL P • dv W T₂ e b (Pi.single k₀ 1) := by
  unfold dvO
  rw [dv_eq_sum_single, map_sum]
  simp only [map_smul, hμ]
  unfold dvO
  rw [← dv_sum W T₂ e b Finset.univ (fun m => algebraMap O LL (c₁ m)) (fun m k => algebraMap O LL (μ m k)),
    ← dv_smul]
  congr 1
  funext k
  simp only [← map_mul, ← map_sum, hSig k]
  by_cases hk : k = k₀
  · subst hk; simp
  · simp [hk, Pi.single_apply]

end ArcLengthTwoLifting

end Formalism.MainNotions.N.FrobeniusPowerSeries
