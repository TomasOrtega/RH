import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAdelicMatrix
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StrongApproximation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CramerMemAdelicCompletionOfElementSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjIsometryFlagDomainGroupNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFundamentalSetConjFiniteIndexSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexComapPairOfDenseImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicIndefiniteSelfDualTraceFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFullLevelGroupIffCongruenceLcmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruenceDetEqOneOfThreeLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataOfFiniteIndexSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjEqOfPowEqStatement

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UTrans GlobalTheory.UTrans.StrongApprox GlobalTheory.AdLat
open scoped TensorProduct ENNReal

namespace GlobalTheory.EqCovol.SameSpace

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Simplify `hx` using `[mul_assoc]`. Introduce `hk`. Conclude with `⟨_, hk, by simp [mul_assoc]⟩`.
-/
theorem mem_map_conj {A : Type} [Group A] (K : Subgroup A) (h k : A) :
    k ∈ K.map (MulAut.conj h).toMonoidHom ↔ h⁻¹ * k * h ∈ K := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro hk
    exact ⟨_, hk, by simp [mul_assoc]⟩

section Abstract

variable {R : Type} [CommRing R] {n : ℕ} {σ : R →+* R} {G : Matrix (Fin n) (Fin n) R}

/- English proof (translation)
Simplify using `only [hf, dotProduct, mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem hf_eq (x y : Fin n → R) : hf σ G x y = x ⬝ᵥ (G *ᵥ fun i => σ (y i)) := by
  simp only [hf, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Establish `key : ∀ x y, hf σ G (γ *ᵥ x) (γ *ᵥ y) = hf σ (γᵀ * G * γ.map σ) x y` using `fun x y => by`. Establish `: (fun i => σ ((γ *ᵥ y) i)) = γ.map σ *ᵥ fun i => σ (y i)`. Use function extensionality and compare the values at `fun i => RingHom.map_mulVec σ γ y i`. Rewrite using `[hf_eq, hf_eq, this, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x, vecMul_transpose]`. Use `⟨fun h => ?_, fun h x y => by rw [key, h]⟩` and prove the remaining obligations.

Use extensionality with `i j`. Use `h (Pi.single i 1) (Pi.single j 1)` as an intermediate fact. Rewrite `this` using `[key]`. Simplify `this` using `[hf, Pi.single_apply, apply_ite σ]`.
-/
theorem isU_iff {γ : Matrix (Fin n) (Fin n) R} : IsU σ G γ ↔ γᵀ * G * γ.map σ = G := by
  have key : ∀ x y, hf σ G (γ *ᵥ x) (γ *ᵥ y) = hf σ (γᵀ * G * γ.map σ) x y := fun x y => by
    have : (fun i => σ ((γ *ᵥ y) i)) = γ.map σ *ᵥ fun i => σ (y i) :=
      funext fun i => RingHom.map_mulVec σ γ y i
    rw [hf_eq, hf_eq, this, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x, vecMul_transpose]
  refine ⟨fun h => ?_, fun h x y => by rw [key, h]⟩
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [key] at this
  simpa [hf, Pi.single_apply, apply_ite σ] using this

/- English proof (translation)
Introduce `x y` and use `by rw [← mulVec_mulVec, ← mulVec_mulVec, ha, hb]`.
-/
theorem isU_mul {a b : Matrix (Fin n) (Fin n) R} (ha : IsU σ G a) (hb : IsU σ G b) : IsU σ G (a * b) :=
  fun x y => by rw [← mulVec_mulVec, ← mulVec_mulVec, ha, hb]

/- English proof (translation)
Introduce `x y` and use `by rw [← ha, mulVec_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec, one_mulVec]`.
-/
theorem isU_inv {a : GL (Fin n) R} (ha : IsU σ G a.1) : IsU σ G (a⁻¹).1 := fun x y => by
  rw [← ha, mulVec_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec, one_mulVec]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro x y`. Simplify using the standard rewrite rules. Consider the case `succ k ih => rw [pow_succ, Units.val_mul]`. Conclude with `isU_mul ih ha`.
-/
theorem isU_pow {a : GL (Fin n) R} (ha : IsU σ G a.1) (k : ℕ) : IsU σ G (a ^ k).1 := by
  induction k with
  | zero => intro x y; simp
  | succ k ih => rw [pow_succ, Units.val_mul]; exact isU_mul ih ha

/- English proof (translation)
Establish `e` using `congrArg det (isU_iff.1 ha)`. Rewrite `e` using `[det_mul, det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Use `hG.mul_right_cancel ?_` and prove the remaining obligations. Take the linear combination `e`.
-/
theorem det_mul_det (hG : IsUnit G.det) {a : Matrix (Fin n) (Fin n) R} (ha : IsU σ G a) :
    a.det * σ a.det = 1 := by
  have e := congrArg det (isU_iff.1 ha)
  rw [det_mul, det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at e
  refine hG.mul_right_cancel ?_
  linear_combination e

/- English proof (translation)
Rewrite using `[Units.val_mul, Units.val_mul, det_mul, det_mul, mul_right_comm, ← det_mul, Units.inv_mul, det_one, one_mul]`.
-/
theorem det_conj (h k : GL (Fin n) R) : (h⁻¹ * k * h).1.det = k.1.det := by
  rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_right_comm, ← det_mul, Units.inv_mul, det_one, one_mul]

variable (σ G) in

def cong (H : AddSubgroup (Fin n → R)) (M : ℕ) : Subgroup (GL (Fin n) R) where
  carrier := {k | IsU σ G k.1 ∧ k.1.det = 1 ∧ (k⁻¹).1 ∈ stab H ∧ ∃ B ∈ stab H, k.1 = 1 + (M : R) • B}
  one_mem' := ⟨fun x y => by simp, by simp, by simpa using one_mem _, 0, zero_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3, B, hB, e⟩ ⟨hb1, hb2, hb3, C, hC, e'⟩
    refine ⟨isU_mul ha1 hb1, by rw [Units.val_mul, det_mul, ha2, hb2, mul_one], ?_,
      B + C + (M : R) • (B * C), add_mem (add_mem hB hC) (natCast_smul_mem _ (mul_mem hB hC)), ?_⟩
    · rw [_root_.mul_inv_rev, Units.val_mul]; exact mul_mem hb3 ha3
    · rw [Units.val_mul, e, e']
      simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_add]
      abel
  inv_mem' := by
    rintro a ⟨ha1, ha2, ha3, B, hB, e⟩
    refine ⟨isU_inv ha1, ?_, ?_, -((a⁻¹).1 * B), neg_mem (mul_mem ha3 hB), ?_⟩
    · have := congrArg det a.inv_mul
      rwa [det_mul, ha2, mul_one, det_one] at this
    · rw [inv_inv, e]; exact add_mem (one_mem _) (natCast_smul_mem _ hB)
    · rw [← a.inv_mul, e, mul_add, mul_one, Matrix.mul_smul, smul_neg, add_neg_cancel_right]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_cong {H : AddSubgroup (Fin n → R)} {M : ℕ} {k : GL (Fin n) R} : k ∈ cong σ G H M ↔
    IsU σ G k.1 ∧ k.1.det = 1 ∧ (k⁻¹).1 ∈ stab H ∧ ∃ B ∈ stab H, k.1 = 1 + (M : R) • B := Iff.rfl

/- English proof (translation)
Take `⟨h1, h2, h3, B, hB, e⟩` from `hk`. Use `⟨isU_mul (isU_mul (isU_inv hh) h1) hh, by rw [det_conj, h2], ?_, _, hH B hB, ?_⟩` and prove the remaining obligations. Establish `: (h⁻¹ * k * h)⁻¹ = h⁻¹ * k⁻¹ * h` using `by group`. Rewrite using `[this]`. Conclude with `hH _ h3`.

Rewrite using `[Units.val_mul, Units.val_mul, e, mul_add, add_mul, mul_one, Units.inv_mul, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem conj_mem_cong {H H' : AddSubgroup (Fin n → R)} {M : ℕ} {h : GL (Fin n) R} (hh : IsU σ G h.1)
    (hH : ∀ A ∈ stab H', (h⁻¹).1 * A * h.1 ∈ stab H) {k : GL (Fin n) R} (hk : k ∈ cong σ G H' M) :
    h⁻¹ * k * h ∈ cong σ G H M := by
  obtain ⟨h1, h2, h3, B, hB, e⟩ := hk
  refine ⟨isU_mul (isU_mul (isU_inv hh) h1) hh, by rw [det_conj, h2], ?_, _, hH B hB, ?_⟩
  · have : (h⁻¹ * k * h)⁻¹ = h⁻¹ * k⁻¹ * h := by group
    rw [this]; exact hH _ h3
  · rw [Units.val_mul, Units.val_mul, e, mul_add, add_mul, mul_one, Units.inv_mul, Matrix.mul_smul,
      Matrix.smul_mul]

/- English proof (translation)
Introduce `A hA z hz` and use `by rw [← mulVec_mulVec, ← mulVec_mulVec] exact h2 _ (hA _ (h1 z hz))`.
-/
theorem conj_mem_stab {H H' : AddSubgroup (Fin n → R)} {h : GL (Fin n) R}
    (h1 : ∀ z ∈ H, h.1 *ᵥ z ∈ H') (h2 : ∀ z ∈ H', (h⁻¹).1 *ᵥ z ∈ H) :
    ∀ A ∈ stab H', (h⁻¹).1 * A * h.1 ∈ stab H := fun A hA z hz => by
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  exact h2 _ (hA _ (h1 z hz))

/- English proof (translation)
Establish `h1 : ∀ z ∈ H, h.1 *ᵥ z ∈ H'` using `fun z hz => by`. Rewrite using `[← SetLike.mem_coe, ← hH]`. Conclude with `⟨z, hz, rfl⟩`. Establish `h2 : ∀ z ∈ H', (h⁻¹).1 *ᵥ z ∈ H` using `fun z hz => by`. Rewrite `hz` using `[← SetLike.mem_coe, ← hH]`.

Take `⟨w, hw, rfl⟩` from `hz`. Rewrite using `[mulVec_mulVec, Units.inv_mul, one_mulVec]` and apply the resulting hypothesis. Use extensionality with `k`. Rewrite using `[mem_map_conj]`. Use `⟨fun hk => ?_, conj_mem_cong hh (conj_mem_stab h1 h2)⟩` and prove the remaining obligations.

Use `conj_mem_cong (isU_inv hh) (conj_mem_stab (h := h⁻¹) h2 (by simpa using h1)) hk` as an intermediate fact. Simplify `this` using `[mul_assoc]`.
-/
theorem map_conj_cong {H H' : AddSubgroup (Fin n → R)} {M : ℕ} {h : GL (Fin n) R} (hh : IsU σ G h.1)
    (hH : h.1.mulVec '' H = H') : (cong σ G H M).map (MulAut.conj h).toMonoidHom = cong σ G H' M := by
  have h1 : ∀ z ∈ H, h.1 *ᵥ z ∈ H' := fun z hz => by
    rw [← SetLike.mem_coe, ← hH]; exact ⟨z, hz, rfl⟩
  have h2 : ∀ z ∈ H', (h⁻¹).1 *ᵥ z ∈ H := fun z hz => by
    rw [← SetLike.mem_coe, ← hH] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rwa [mulVec_mulVec, Units.inv_mul, one_mulVec]
  ext k
  rw [mem_map_conj]
  refine ⟨fun hk => ?_, conj_mem_cong hh (conj_mem_stab h1 h2)⟩
  have := conj_mem_cong (isU_inv hh) (conj_mem_stab (h := h⁻¹) h2 (by simpa using h1)) hk
  simpa [mul_assoc] using this

/- English proof (translation)
Establish `key : ∀ k ∈ cong σ G H (M * a * b), ∃ C ∈ stab H, (h⁻¹ * k * h).1 = 1 + (M : R) • C`. Introduce and unpack `k ⟨-, -, -, B, hB, e⟩`. Use `⟨_, mul_mem (mul_mem ha hB) hb, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, Units.val_mul, e, mul_add, add_mul, mul_one, Units.inv_mul]`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Nat.cast_mul]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Introduce `k hk`. Rewrite using `[mem_map_conj]`. Use `⟨isU_mul (isU_mul (isU_inv hh) hk.1) hh, by rw [det_conj, hk.2.1], ?_, key k hk⟩` and prove the remaining obligations.

Take `⟨C, hC, e⟩` from `key _ (inv_mem hk)`. Establish `: (h⁻¹ * k * h)⁻¹ = h⁻¹ * k⁻¹ * h` using `by group`. Rewrite using `[this, e]`. Conclude with `add_mem (one_mem _) (natCast_smul_mem _ hC)`.
-/
theorem cong_le_map_conj {H : AddSubgroup (Fin n → R)} {M a b : ℕ} {h : GL (Fin n) R} (hh : IsU σ G h.1)
    (ha : (a : R) • (h⁻¹).1 ∈ stab H) (hb : (b : R) • h.1 ∈ stab H) :
    cong σ G H (M * a * b) ≤ (cong σ G H M).map (MulAut.conj h).toMonoidHom := by
  have key : ∀ k ∈ cong σ G H (M * a * b), ∃ C ∈ stab H, (h⁻¹ * k * h).1 = 1 + (M : R) • C := by
    rintro k ⟨-, -, -, B, hB, e⟩
    refine ⟨_, mul_mem (mul_mem ha hB) hb, ?_⟩
    rw [Units.val_mul, Units.val_mul, e, mul_add, add_mul, mul_one, Units.inv_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Nat.cast_mul]
    congr 2
    ring
  intro k hk
  rw [mem_map_conj]
  refine ⟨isU_mul (isU_mul (isU_inv hh) hk.1) hh, by rw [det_conj, hk.2.1], ?_, key k hk⟩
  obtain ⟨C, hC, e⟩ := key _ (inv_mem hk)
  have : (h⁻¹ * k * h)⁻¹ = h⁻¹ * k⁻¹ * h := by group
  rw [this, e]
  exact add_mem (one_mem _) (natCast_smul_mem _ hC)

/- English proof (translation)
Introduce and unpack `k ⟨h1, h2, h3, B, hB, e⟩`. Conclude with `⟨h1, h2, h3, _, natCast_smul_mem a hB, by rw [e, smul_smul, Nat.cast_mul]⟩`.
-/
theorem cong_mul_le {H : AddSubgroup (Fin n → R)} {M a : ℕ} : cong σ G H (M * a) ≤ cong σ G H M := by
  rintro k ⟨h1, h2, h3, B, hB, e⟩
  exact ⟨h1, h2, h3, _, natCast_smul_mem a hB, by rw [e, smul_smul, Nat.cast_mul]⟩

/- English proof (translation)
Establish `hd` using `det_mul_det hG hg`. Set `z : GL (Fin n) R` to `⟨σ g.1.det • 1, g.1.det • 1, by simp [smul_smul, mul_comm, hd], by simp [smul_smul, mul_comm, hd]⟩`. Establish `hz : ∀ k, z * k = k * z` using `fun k => Units.ext (by simp [z])`. Establish `hd' : σ g.1.det * σ (σ g.1.det) = 1` using `by rw [← map_mul, hd, map_one]`. Use `⟨z * g ^ n, isU_mul (isU_iff.2 ?_) (isU_pow hg n), ?_, fun k => ?_⟩` and prove the remaining obligations.

Establish `: (σ g.1.det • (1 : Matrix (Fin n) (Fin n) R)).map σ = σ (σ g.1.det) • 1`. Use extensionality with `i j`. Simplify using `[one_apply, apply_ite σ]`. Simplify using `[z, this, smul_smul, mul_comm, hd']`. Rewrite using `[Units.val_mul, det_mul, Units.val_pow_eq_pow_val, det_pow]`.

Simplify using `[z, ← mul_pow, mul_comm, hd]`. Rewrite using `[_root_.mul_inv_rev, mul_assoc, mul_assoc, mul_assoc, ← mul_assoc k, ← hz k, mul_assoc z, inv_mul_cancel_left]`.
-/
theorem exists_det_one_conj_eq (hG : IsUnit G.det) {g : GL (Fin n) R} (hg : IsU σ G g.1) :
    ∃ s : GL (Fin n) R, IsU σ G s.1 ∧ s.1.det = 1 ∧ ∀ k, (g ^ n)⁻¹ * k * g ^ n = s⁻¹ * k * s := by
  have hd := det_mul_det hG hg
  let z : GL (Fin n) R := ⟨σ g.1.det • 1, g.1.det • 1, by simp [smul_smul, mul_comm, hd],
    by simp [smul_smul, mul_comm, hd]⟩
  have hz : ∀ k, z * k = k * z := fun k => Units.ext (by simp [z])
  have hd' : σ g.1.det * σ (σ g.1.det) = 1 := by rw [← map_mul, hd, map_one]
  refine ⟨z * g ^ n, isU_mul (isU_iff.2 ?_) (isU_pow hg n), ?_, fun k => ?_⟩
  · have : (σ g.1.det • (1 : Matrix (Fin n) (Fin n) R)).map σ = σ (σ g.1.det) • 1 := by
      ext i j; simp [one_apply, apply_ite σ]
    simp [z, this, smul_smul, mul_comm, hd']
  · rw [Units.val_mul, det_mul, Units.val_pow_eq_pow_val, det_pow]
    simp [z, ← mul_pow, mul_comm, hd]
  · rw [_root_.mul_inv_rev, mul_assoc, mul_assoc, mul_assoc, ← mul_assoc k, ← hz k, mul_assoc z,
      inv_mul_cancel_left]

end Abstract

section Adelic

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

def embGL : GL (Fin n) E →* GL (Fin n) (RA F E) := GeneralLinearGroup.map (emb F)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem embGL_val (γ : GL (Fin n) E) : (embGL F γ).1 = (emb F).mapMatrix γ.1 := rfl

/- English proof (translation)
Take `⟨P, hP⟩` from `Ideal.exists_maximal (𝓞 F)`. Set `v : HeightOneSpectrum (𝓞 F)` to `⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩`. Use `haveI : Nontrivial (FiniteAdeleRing (𝓞 F) F) := ⟨⟨0, 1, fun h => by`. Establish `: (0 : v.adicCompletion F) = 1` using `congrArg (fun a : FiniteAdeleRing (𝓞 F) F => a v) h`. Conclude with `zero_ne_one this⟩⟩`.

Conclude with `Algebra.TensorProduct.includeRight_injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)).injective`.
-/
theorem emb_injective : Function.Injective (emb F : E →+* RA F E) := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  haveI : Nontrivial (FiniteAdeleRing (𝓞 F) F) := ⟨⟨0, 1, fun h => by
    have : (0 : v.adicCompletion F) = 1 := congrArg (fun a : FiniteAdeleRing (𝓞 F) F => a v) h
    exact zero_ne_one this⟩⟩
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)).injective

variable {F} (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)

def sgA : RA F E →+* RA F E := (sg (FiniteAdeleRing (𝓞 F) F) c).toRingHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hermA_eq (x y : Fin n → RA F E) : hermA c G x y = hf (sgA c) ((emb F).mapMatrix G) x y := rfl

/- English proof (translation)
Establish `e : ((emb F).mapMatrix γ)ᵀ * (emb F).mapMatrix G * ((emb F).mapMatrix γ).map (sgA c) = (emb F).mapMatrix (γᵀ * G * γ.map (c : E →+* E))`. Rewrite using `[map_mul, map_mul]`. Both sides reduce to the same expression. Rewrite using `[isU_iff, isU_iff, e]`. Conclude with `(Matrix.map_injective (emb_injective F)).eq_iff`.
-/
theorem isU_emb {γ : Matrix (Fin n) (Fin n) E} :
    IsU (sgA c) ((emb F).mapMatrix G) ((emb F).mapMatrix γ) ↔ IsU (c : E →+* E) G γ := by
  have e : ((emb F).mapMatrix γ)ᵀ * (emb F).mapMatrix G * ((emb F).mapMatrix γ).map (sgA c) =
      (emb F).mapMatrix (γᵀ * G * γ.map (c : E →+* E)) := by
    rw [map_mul, map_mul]; rfl
  rw [isU_iff, isU_iff, e]
  exact (Matrix.map_injective (emb_injective F)).eq_iff

variable [NumberField E] {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG)
  (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)

include hL hsp in

/- English proof (translation)
Establish `h1` using `(hat_rational_points_and_approx F E n L hL hsp).1`. Establish `hME : (M : E) ≠ 0` using `by exact_mod_cast hM.ne'`. Establish `hd : ((emb F).mapMatrix γ.1).det = 1 ↔ γ.1.det = 1`. Rewrite using `[← RingHom.map_det, ← map_one (emb F), (emb_injective F).eq_iff]`. Establish `hst : ∀ A : Matrix (Fin n) (Fin n) E, (emb F).mapMatrix A ∈ stab (hat F (L : Set (Fin n → E))) ↔ ∀ x ∈ L, A *ᵥ x ∈ L` using `fun A => ⟨fun h x hx => by`.

Rewrite using `[← h1, ← emb_mulVec]`. Conclude with `h _ (Translate.fv_mem_hat hx), emb_mem_stab F⟩`. Use `set A : Matrix (Fin n) (Fin n) E := (M : E)⁻¹ • (γ.1 - 1) with hA`. Establish `eA : γ.1 = 1 + (M : E) • A` using `by rw [hA, smul_inv_smul₀ hME, add_sub_cancel]`. Establish `eA' : (emb F).mapMatrix γ.1 = 1 + (M : RA F E) • (emb F).mapMatrix A`.

Rewrite using `[eA, map_add, map_one, emb_smul, map_natCast]`. Establish `eAx : ∀ x, γ.1 *ᵥ x - x = M • (A *ᵥ x)` using `fun x => by`. Rewrite using `[eA, add_mulVec, one_mulVec, add_sub_cancel_left, smul_mulVec, Nat.cast_smul_eq_nsmul]`. Establish `h3 : (∃ B ∈ stab (hat F (L : Set (Fin n → E))), (emb F).mapMatrix γ.1 = 1 + (M : RA F E) • B) ↔ ∀ x ∈ L, A *ᵥ x ∈ L`. Rewrite using `[← hst]`.

Use `⟨?_, fun h => ⟨_, h, eA'⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨B, hB, e⟩`. Rewrite `e` using `[eA', add_right_inj]`. Rewrite using `[(isUnit_nat F hM).smul_left_cancel.1 e]` and apply the resulting hypothesis. Establish `h4 : (∀ x ∈ L, ∃ y ∈ L, γ.1 *ᵥ x - x = M • y) ↔ ∀ x ∈ L, A *ᵥ x ∈ L`.

Use `forall₂_congr fun x _ => ⟨?_, fun h => ⟨_, h, eAx x⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨y, hy, e⟩`. Rewrite `e` using `[eAx, ← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E]`. Rewrite using `[smul_right_injective _ hME e]` and apply the resulting hypothesis. Rewrite using `[mem_cong, ← map_inv, embGL_val, embGL_val, isU_emb, hd, hst, h3, h4]`.

Use `and_congr_right fun _ => and_congr_right fun _ => and_congr_left fun h => ⟨fun h' x => ⟨fun hx => ?_, fun hx => ?_⟩, fun h' x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_add_cancel (γ.1 *ᵥ x) x, eAx]`. Conclude with `add_mem (nsmul_mem (h x hx) M) hx`. Use `h' _ hx` as an intermediate fact. Rewrite `this` using `[mulVec_mulVec, Units.inv_mul, one_mulVec]`. Then use the resulting hypothesis.

Rewrite using `[h', mulVec_mulVec, Units.mul_inv, one_mulVec]`. Conclude with `hx`.
-/
theorem embGL_mem_cong {M : ℕ} (hM : 0 < M) (γ : GL (Fin n) E) :
    embGL F γ ∈ cong (sgA c) ((emb F).mapMatrix G) (hat F (L : Set (Fin n → E))) M ↔
      IsU (c : E →+* E) G γ.1 ∧ γ.1.det = 1 ∧ (∀ x, x ∈ L ↔ γ.1 *ᵥ x ∈ L) ∧
        ∀ x ∈ L, ∃ y ∈ L, γ.1 *ᵥ x - x = M • y := by
  have h1 := (hat_rational_points_and_approx F E n L hL hsp).1
  have hME : (M : E) ≠ 0 := by exact_mod_cast hM.ne'
  have hd : ((emb F).mapMatrix γ.1).det = 1 ↔ γ.1.det = 1 := by
    rw [← RingHom.map_det, ← map_one (emb F), (emb_injective F).eq_iff]
  have hst : ∀ A : Matrix (Fin n) (Fin n) E, (emb F).mapMatrix A ∈ stab (hat F (L : Set (Fin n → E))) ↔
      ∀ x ∈ L, A *ᵥ x ∈ L := fun A => ⟨fun h x hx => by
        rw [← h1, ← emb_mulVec]; exact h _ (Translate.fv_mem_hat hx), emb_mem_stab F⟩
  set A : Matrix (Fin n) (Fin n) E := (M : E)⁻¹ • (γ.1 - 1) with hA
  have eA : γ.1 = 1 + (M : E) • A := by rw [hA, smul_inv_smul₀ hME, add_sub_cancel]
  have eA' : (emb F).mapMatrix γ.1 = 1 + (M : RA F E) • (emb F).mapMatrix A := by
    rw [eA, map_add, map_one, emb_smul, map_natCast]
  have eAx : ∀ x, γ.1 *ᵥ x - x = M • (A *ᵥ x) := fun x => by
    rw [eA, add_mulVec, one_mulVec, add_sub_cancel_left, smul_mulVec, Nat.cast_smul_eq_nsmul]
  have h3 : (∃ B ∈ stab (hat F (L : Set (Fin n → E))), (emb F).mapMatrix γ.1 = 1 + (M : RA F E) • B) ↔
      ∀ x ∈ L, A *ᵥ x ∈ L := by
    rw [← hst]
    refine ⟨?_, fun h => ⟨_, h, eA'⟩⟩
    rintro ⟨B, hB, e⟩
    rw [eA', add_right_inj] at e
    rwa [(isUnit_nat F hM).smul_left_cancel.1 e]
  have h4 : (∀ x ∈ L, ∃ y ∈ L, γ.1 *ᵥ x - x = M • y) ↔ ∀ x ∈ L, A *ᵥ x ∈ L := by
    refine forall₂_congr fun x _ => ⟨?_, fun h => ⟨_, h, eAx x⟩⟩
    rintro ⟨y, hy, e⟩
    rw [eAx, ← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E] at e
    rwa [smul_right_injective _ hME e]
  rw [mem_cong, ← map_inv, embGL_val, embGL_val, isU_emb, hd, hst, h3, h4]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_left fun h => ⟨fun h' x => ⟨fun hx => ?_,
    fun hx => ?_⟩, fun h' x hx => ?_⟩
  · rw [← sub_add_cancel (γ.1 *ᵥ x) x, eAx]
    exact add_mem (nsmul_mem (h x hx) M) hx
  · have := h' _ hx
    rwa [mulVec_mulVec, Units.inv_mul, one_mulVec] at this
  · rw [h', mulVec_mulVec, Units.mul_inv, one_mulVec]
    exact hx

variable (hrk : Module.finrank F E = 2) (hG : IsHerm (c : E →+* E) G)
  (hiso : ∃ z : Fin n → E, z ≠ 0 ∧ hf (c : E →+* E) G z z = 0)

include hL hsp hrk hG hiso in

/- English proof (translation)
Take `⟨γ, h1, h2, h3⟩` from `strong_approximation F E c n G hrk hG hiso L hL hsp s hs hd M hM`. Set `δ : GL (Fin n) E` to `GeneralLinearGroup.mkOfDetNeZero γ (by rw [h2]; exact one_ne_zero)`. Establish `e : ((embGL F δ⁻¹)⁻¹ * s).1 = (emb F).mapMatrix γ * s.1` using `by rw [map_inv, inv_inv]; rfl`. Establish `hdet : ((embGL F δ⁻¹)⁻¹ * s).1.det = 1`. Rewrite using `[e, det_mul, hd, ← RingHom.map_det, h2, map_one, mul_one]`.

Take `⟨B, hB, eB⟩` from `exists_of_cong (H := hat F (L : Set (Fin n → E))) (isUnit_nat F hM) (A := (emb F).mapMatrix γ * s.1 - 1) fun z hz => by`. Take `⟨w, hw, e⟩` from `h3 z hz`. Conclude with `⟨w, hw, by rw [sub_mulVec, one_mulVec]; exact sub_eq_of_eq_add' e⟩`. Establish `eB' : ((embGL F δ⁻¹)⁻¹ * s).1 = 1 + (M : RA F E) • B` using `by rw [e, ← eB, add_sub_cancel]`. Use `⟨δ⁻¹, isU_inv (a := δ) h1, by rw [e]; exact isU_mul ((isU_emb c G).2 h1) hs, hdet, ?_, B, hB, eB'⟩` and prove the remaining obligations.

Use `inv_mulVec_mem_hat F E n L _ c hL hsp ?_ (by rw [hdet, map_one, mul_one])` and prove the remaining obligations. Rewrite using `[eB']`. Conclude with `add_mem (one_mem (stab _)) (natCast_smul_mem _ hB)`.
-/
theorem exists_inv_mul_mem_cong {M : ℕ} (hM : 0 < M) {s : GL (Fin n) (RA F E)}
    (hs : IsU (sgA c) ((emb F).mapMatrix G) s.1) (hd : s.1.det = 1) :
    ∃ γ : GL (Fin n) E, IsU (c : E →+* E) G γ.1 ∧ (embGL F γ)⁻¹ * s ∈
      cong (sgA c) ((emb F).mapMatrix G) (hat F (L : Set (Fin n → E))) M := by
  obtain ⟨γ, h1, h2, h3⟩ := strong_approximation F E c n G hrk hG hiso L hL hsp s hs hd M hM
  let δ : GL (Fin n) E := GeneralLinearGroup.mkOfDetNeZero γ (by rw [h2]; exact one_ne_zero)
  have e : ((embGL F δ⁻¹)⁻¹ * s).1 = (emb F).mapMatrix γ * s.1 := by rw [map_inv, inv_inv]; rfl
  have hdet : ((embGL F δ⁻¹)⁻¹ * s).1.det = 1 := by
    rw [e, det_mul, hd, ← RingHom.map_det, h2, map_one, mul_one]
  obtain ⟨B, hB, eB⟩ := exists_of_cong (H := hat F (L : Set (Fin n → E))) (isUnit_nat F hM)
    (A := (emb F).mapMatrix γ * s.1 - 1) fun z hz => by
      obtain ⟨w, hw, e⟩ := h3 z hz
      exact ⟨w, hw, by rw [sub_mulVec, one_mulVec]; exact sub_eq_of_eq_add' e⟩
  have eB' : ((embGL F δ⁻¹)⁻¹ * s).1 = 1 + (M : RA F E) • B := by rw [e, ← eB, add_sub_cancel]
  refine ⟨δ⁻¹, isU_inv (a := δ) h1, by rw [e]; exact isU_mul ((isU_emb c G).2 h1) hs, hdet, ?_, B, hB, eB'⟩
  refine inv_mulVec_mem_hat F E n L _ c hL hsp ?_ (by rw [hdet, map_one, mul_one])
  rw [eB']
  exact add_mem (one_mem (stab _)) (natCast_smul_mem _ hB)

include hL hsp hrk hG hiso in

/- English proof (translation)
Substitute `hK` using the available equality. Take `⟨a, ha0, ha⟩` from `exists_bound_stab F hL hsp (h⁻¹).1`. Take `⟨b, hb0, hb⟩` from `exists_bound_stab F hL hsp h.1`. Use `GlobalTheory.HL.relIndex_pair_comap_of_dense_image _ _ _ fun s hs => ?_` and prove the remaining obligations. Establish `hs' : IsU (sgA c) ((emb F).mapMatrix G) s.1 ∧ s.1.det = 1`.

Break down `hs with hs | hs` into its components or cases. Rewrite `hs` using `[mem_map_conj]`. Use `⟨?_, (det_conj h s).symm.trans hs.2.1⟩` and prove the remaining obligations. Establish `e : s = h * (h⁻¹ * s * h) * h⁻¹` using `by group`. Rewrite using `[e]`.

Conclude with `isU_mul (isU_mul hh hs.1) (isU_inv hh)`. Conclude with `⟨hs.1, hs.2.1⟩`. Take `⟨γ, -, hγ⟩` from `exists_inv_mul_mem_cong c G hL hsp hrk hG hiso (Nat.mul_pos (Nat.mul_pos hM ha0) hb0) hs'.1 hs'.2`. Conclude with `⟨γ, cong_le_map_conj hh ha hb hγ, cong_mul_le (cong_mul_le hγ)⟩`.
-/
theorem relIndex_comap {M : ℕ} (hM : 0 < M) {h : GL (Fin n) (RA F E)}
    (hh : IsU (sgA c) ((emb F).mapMatrix G) h.1) (K : Subgroup (GL (Fin n) (RA F E)))
    (hK : K = cong (sgA c) ((emb F).mapMatrix G) (hat F (L : Set (Fin n → E))) M) :
    ((K.map (MulAut.conj h).toMonoidHom).comap (embGL F)).relIndex (K.comap (embGL F)) =
      (K.map (MulAut.conj h).toMonoidHom).relIndex K ∧
    (K.comap (embGL F)).relIndex ((K.map (MulAut.conj h).toMonoidHom).comap (embGL F)) =
      K.relIndex (K.map (MulAut.conj h).toMonoidHom) := by
  subst hK
  obtain ⟨a, ha0, ha⟩ := exists_bound_stab F hL hsp (h⁻¹).1
  obtain ⟨b, hb0, hb⟩ := exists_bound_stab F hL hsp h.1
  refine GlobalTheory.HL.relIndex_pair_comap_of_dense_image _ _ _ fun s hs => ?_
  have hs' : IsU (sgA c) ((emb F).mapMatrix G) s.1 ∧ s.1.det = 1 := by
    rcases hs with hs | hs
    · rw [mem_map_conj] at hs
      refine ⟨?_, (det_conj h s).symm.trans hs.2.1⟩
      have e : s = h * (h⁻¹ * s * h) * h⁻¹ := by group
      rw [e]
      exact isU_mul (isU_mul hh hs.1) (isU_inv hh)
    · exact ⟨hs.1, hs.2.1⟩
  obtain ⟨γ, -, hγ⟩ := exists_inv_mul_mem_cong c G hL hsp hrk hG hiso
    (Nat.mul_pos (Nat.mul_pos hM ha0) hb0) hs'.1 hs'.2
  exact ⟨γ, cong_le_map_conj hh ha hb hγ, cong_mul_le (cong_mul_le hγ)⟩

end Adelic

section Covolume

open ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.TrueCx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Establish `h` using `GlobalTheory.SubgroupUnfold.lintegral_fundSet_conj_subgroup E r X P hΨ δ _ _ _ _ (fun _ => 1) hG hp hδ hle hi (isOrth_x0F X) (isOrth_x0F P) (GlobalTheory.MetricWeightTest.exists_fundSet_orth X (isOrth_x0F X)).choose_spec (GlobalTheory.MetricWeightTest.exists_fundSet_orth P (isOrt …`. Rewrite `h` using `[setLIntegral_one, setLIntegral_one]`. Rewrite using `[covol, covol, h, ENNReal.toReal_mul, ENNReal.toReal_natCast, congrArg Finset.card hΨ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem covol_of_le (X P : Data E r) (δ : GL (Fin r) E) (hΨ : P.Ψ = X.Ψ) (hG : P.Gm = X.Gm) (hp : P.p0 = X.p0)
    (hδ : ∀ v w, herm X.Gm (δ.1 *ᵥ v) (δ.1 *ᵥ w) = herm X.Gm v w)
    (hle : P.Γ.map (MulAut.conj δ).toMonoidHom ≤ X.Γ)
    (hi : (P.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ ≠ 0) :
    covol P = covol X * ((P.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ : ℝ) := by
  have h := GlobalTheory.SubgroupUnfold.lintegral_fundSet_conj_subgroup E r X P hΨ δ _ _ _ _ (fun _ => 1) hG hp hδ hle hi
    (isOrth_x0F X) (isOrth_x0F P) (GlobalTheory.MetricWeightTest.exists_fundSet_orth X (isOrth_x0F X)).choose_spec
    (GlobalTheory.MetricWeightTest.exists_fundSet_orth P (isOrth_x0F P)).choose_spec measurable_const
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  rw [setLIntegral_one, setLIntegral_one] at h
  rw [covol, covol, h, ENNReal.toReal_mul, ENNReal.toReal_natCast, congrArg Finset.card hΨ]
  ring

/- English proof (translation)
Use `set f := (MulAut.conj δ).toMonoidHom with hf`. Establish `hinj : Function.Injective f` using `(MulAut.conj δ).injective`. Establish `h1` using `GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero X' X δ hG (by rw [hG]; exact hδ)`. Establish `h2` using `GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero X X' δ⁻¹ hG.symm (GlobalTheory.SubgroupUnfold.isIsom_inv hδ)`. Establish `e : X.Γ.map (MulAut.conj δ⁻¹).toMonoidHom = X.Γ.comap f`.

Use extensionality with `k`. Rewrite using `[mem_map_conj, inv_inv]`. Both sides reduce to the same expression. Rewrite `h2` using `[e]`. Establish `e1 : ∀ K : Subgroup (GL (Fin r) E), K.map (MulAut.conj (1 : GL (Fin r) E)).toMonoidHom = K` using `fun K => by`.

Use extensionality with `k`. Rewrite using `[mem_map_conj]`. Simplify using the standard rewrite rules. Take `⟨P, hPΨ, hPG, hPp, hP⟩` from `GlobalTheory.T.exists_flagDomainData_of_finiteIndex_subgroup E r X' (X.Γ.comap f ⊓ X'.Γ) inf_le_right (by rwa [Subgroup.inf_relIndex_right])`. Establish `e2 : P.Γ.map f = X'.Γ.map f ⊓ X.Γ`.

Rewrite using `[hP, Subgroup.map_inf _ _ _ hinj, Subgroup.map_comap_eq_self_of_surjective (MulAut.conj δ).surjective, inf_comm]`. Establish `a` using `covol_of_le X P δ (hPΨ.trans hΨ) (hPG.trans hG) (hPp.trans hp) hδ (e2 ▸ inf_le_right) (by rwa [← hf, e2, Subgroup.inf_relIndex_right])`. Establish `b` using `covol_of_le X' P 1 hPΨ hPG hPp (by simp) (by rw [e1, hP]; exact inf_le_right) (by rwa [e1, hP, Subgroup.inf_relIndex_right])`. Rewrite `a` using `[← hf, e2, Subgroup.inf_relIndex_right]`. Rewrite `b` using `[e1, hP, Subgroup.inf_relIndex_right, Subgroup.relIndex_comap]`.

Rewrite using `[← a, b]`.
-/
theorem covol_mul_relIndex (X X' : Data E r) (δ : GL (Fin r) E) (hΨ : X'.Ψ = X.Ψ) (hG : X'.Gm = X.Gm)
    (hp : X'.p0 = X.p0) (hδ : ∀ v w, herm X.Gm (δ.1 *ᵥ v) (δ.1 *ᵥ w) = herm X.Gm v w) :
    covol X * ((X'.Γ.map (MulAut.conj δ).toMonoidHom).relIndex X.Γ : ℝ) =
      covol X' * (X.Γ.relIndex (X'.Γ.map (MulAut.conj δ).toMonoidHom) : ℝ) := by
  set f := (MulAut.conj δ).toMonoidHom with hf
  have hinj : Function.Injective f := (MulAut.conj δ).injective
  have h1 := GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero X' X δ hG (by rw [hG]; exact hδ)
  have h2 := GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero X X' δ⁻¹ hG.symm (GlobalTheory.SubgroupUnfold.isIsom_inv hδ)
  have e : X.Γ.map (MulAut.conj δ⁻¹).toMonoidHom = X.Γ.comap f := by
    ext k
    rw [mem_map_conj, inv_inv]; rfl
  rw [e] at h2
  have e1 : ∀ K : Subgroup (GL (Fin r) E), K.map (MulAut.conj (1 : GL (Fin r) E)).toMonoidHom = K := fun K => by
    ext k
    rw [mem_map_conj]; simp
  obtain ⟨P, hPΨ, hPG, hPp, hP⟩ := GlobalTheory.T.exists_flagDomainData_of_finiteIndex_subgroup E r X' (X.Γ.comap f ⊓ X'.Γ) inf_le_right
    (by rwa [Subgroup.inf_relIndex_right])
  have e2 : P.Γ.map f = X'.Γ.map f ⊓ X.Γ := by
    rw [hP, Subgroup.map_inf _ _ _ hinj, Subgroup.map_comap_eq_self_of_surjective (MulAut.conj δ).surjective,
      inf_comm]
  have a := covol_of_le X P δ (hPΨ.trans hΨ) (hPG.trans hG) (hPp.trans hp) hδ (e2 ▸ inf_le_right)
    (by rwa [← hf, e2, Subgroup.inf_relIndex_right])
  have b := covol_of_le X' P 1 hPΨ hPG hPp (by simp) (by rw [e1, hP]; exact inf_le_right)
    (by rwa [e1, hP, Subgroup.inf_relIndex_right])
  rw [← hf, e2, Subgroup.inf_relIndex_right] at a
  rw [e1, hP, Subgroup.inf_relIndex_right, Subgroup.relIndex_comap] at b
  rw [← a, b]

end Covolume

/- English proof (translation)
Introduce `E _ _ _ H l r Y Y' _ _ hΨ hG hξ hp h1 h2 hl hl' hs hs'`. Use `haveI := H.unram`. Use `set F := maximalRealSubfield E`. Use `set c : E ≃ₐ[F] E := IsCMField.complexConj E with hc`. Establish `hM : 3 ≤ l.M'` using `l.three_le.trans (Nat.le_of_dvd (Nat.lcm_pos (by have := l.three_le; omega) l.A_pos) (Nat.dvd_lcm_left _ _))`.

Establish `hM0 : 0 < l.M'` using `by omega`. Establish `hrk : Module.finrank F E = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Establish `hH : IsHerm (c : E →+* E) Y.Gm` using `⟨IsCMField.complexConj_apply_apply E, by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Conclude with `IsCMField.complexConj_ne_one E (AlgEquiv.ext h), Y.Gm_herm, Y.Gm_det⟩`. Establish `hiso : ∃ z : Fin r → E, z ≠ 0 ∧ hf (c : E →+* E) Y.Gm z z = 0` using `GlobalTheory.T.exists_isotropic_indefinite_selfDualTraceForm E H r Y h1 h2 hs`. Establish `hcomap : ∀ Z : Data E r, Z.Gm = Y.Gm → IsLevGrp l Z → IsSelfDualTr Z → (cong (sgA c) ((emb F).mapMatrix Y.Gm) (hat F (Z.Λ : Set (Fin r → E))) l.M').comap (embGL F) = Z.Γ`. Introduce `Z hZ hlZ hsZ`. Use extensionality with `γ`.

Rewrite using `[Subgroup.mem_comap, embGL_mem_cong c Y.Gm Z.Λ_fg Z.Λ_span hM0, GlobalTheory.T.mem_fullLevelGroup_iff_congruence_lcm E H l r Z hlZ hsZ, ← hZ]`. Conclude with `⟨fun h => ⟨⟨h.1, h.2.2.1⟩, h.2.2.2⟩, fun h => ⟨h.1.1, GlobalTheory.T.unitaryCongruence_det_eq_one_of_three_le E r _ Z.Gm Z.Λ γ hM Z.Gm_det Z.Λ_fg Z.Λ_span h.1 h.2, h.1.2, h.2⟩⟩`. Establish `hsd : ∀ Z : Data E r, Z.Gm = Y.Gm → Z.ξ0 = Y.ξ0 → IsSelfDualTr Z → GlobalTheory.SW.SelfD Y Z.Λ`. Introduce `Z hZ hZξ hsZ`. Use `⟨Z.Λ_fg, fun x => (hsZ x).trans (forall₂_congr fun y _ => ?_)⟩` and prove the remaining obligations.

Rewrite using `[GlobalTheory.ThFr.EF_def, hZ, hZξ]`. Apply the tactic sequence `rcases Y.κ0_xi with h | h <;> rw [h]`. Rewrite using `[mul_div_cancel_left₀ _ two_ne_zero]`. Rewrite using `[neg_div, mul_div_cancel_left₀ _ two_ne_zero, neg_neg, neg_mul, map_neg]`. Conclude with `⟨fun ⟨k, hk⟩ => ⟨-k, by rw [Int.cast_neg, ← hk, neg_neg]⟩, fun ⟨k, hk⟩ => ⟨-k, by rw [Int.cast_neg, hk]⟩⟩`.

Take `⟨g, hg, hgU⟩` from `GlobalTheory.Ker.OntoLat.exists_adelic_matrix F c (fun _ => rfl) Y (hsd Y rfl rfl hs) (hsd Y' hG hξ hs')`. Use `replace hgU : IsU (sgA c) ((emb F).mapMatrix Y.Gm) g.1 := hgU`. Establish `hΓ` using `hcomap Y rfl hl hs`. Establish `hΓ'` using `hcomap Y' hG hl' hs'`. Rewrite `hΓ'` using `[← map_conj_cong hgU hg]`.

Generalize the expression as in `hK : cong (sgA c) ((emb F).mapMatrix Y.Gm) (hat F (Y.Λ : Set (Fin r → E))) l.M' = K at hΓ hΓ'`. Take `⟨a1, a2⟩` from `relIndex_comap c Y.Gm Y.Λ_fg Y.Λ_span hrk hH hiso hM0 hgU K hK.symm`. Rewrite `a1`, `a2` using `[hΓ, hΓ']`. Establish `e1 : ∀ K : Subgroup (GL (Fin r) E), K.map (MulAut.conj (1 : GL (Fin r) E)).toMonoidHom = K` using `fun K => by`. Use extensionality with `k`.

Rewrite using `[mem_map_conj]`. Simplify using the standard rewrite rules. Establish `n1` using `GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero Y' Y 1 hG (by simp)`. Establish `n2` using `GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero Y Y' 1 hG.symm (by simp)`. Establish `hcov` using `covol_mul_relIndex Y Y' 1 hΨ hG hp (by simp)`.

Rewrite `n1`, `n2`, `hcov` using `[e1]`. Take `⟨s, hsU, hs1, hsc⟩` from `exists_det_one_conj_eq (by rw [← RingHom.map_det]; exact Y.Gm_det.isUnit.map _) hgU`. Take `⟨γ, hγU, hγ⟩` from `exists_inv_mul_mem_cong c Y.Gm Y.Λ_fg Y.Λ_span hrk hH hiso hM0 hsU hs1`. Rewrite `hγ` using `[hK]`. Establish `e2 : K.map (MulAut.conj (g ^ r)).toMonoidHom = K.map (MulAut.conj (embGL F γ)).toMonoidHom`.

Use extensionality with `k`. Rewrite using `[mem_map_conj, mem_map_conj, hsc]`. Establish `: s⁻¹ * k * s = ((embGL F γ)⁻¹ * s)⁻¹ * ((embGL F γ)⁻¹ * k * embGL F γ) * ((embGL F γ)⁻¹ * s)` using `by group`. Rewrite using `[this, K.mul_mem_cancel_right hγ, K.mul_mem_cancel_left (K.inv_mem hγ)]`. Take `⟨b1, b2⟩` from `relIndex_comap c Y.Gm Y.Λ_fg Y.Λ_span hrk hH hiso hM0 (h := embGL F γ) ((isU_emb c Y.Gm).2 hγU) K hK.symm`.

Establish `e3 : (K.map (MulAut.conj (embGL F γ)).toMonoidHom).comap (embGL F) = Y.Γ.map (MulAut.conj γ).toMonoidHom`. Use extensionality with `k`. Rewrite using `[Subgroup.mem_comap, mem_map_conj, mem_map_conj, ← hΓ, Subgroup.mem_comap, map_mul, map_mul, map_inv]`. Rewrite `b1`, `b2` using `[e3, hΓ]`. Establish `hcov'` using `mul_left_cancel₀ (GlobalTheory.TrueCx.covol_pos Y).ne' (covol_mul_relIndex Y Y γ rfl rfl rfl hγU)`.

Establish `key` using `GlobalTheory.T.relIndex_map_conj_symm_of_relIndex_map_conj_pow_symm _ K g r (by omega) (a1 ▸ n1) (a2 ▸ n2) (by rw [e2, ← b1, ← b2]; exact_mod_cast hcov')`. Rewrite `key` using `[← a1, ← a2]`. Rewrite `hcov` using `[← key]`. Conclude with `mul_right_cancel₀ (Nat.cast_ne_zero.2 n1) hcov`.
-/
theorem covol_eq_of_same_space : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (r : ℕ) (Y Y' : ReciprocityTheory.ChartRestriction.G.FD.Data E r), (∀ p : ℕ, p.Prime → l.GoodAt p) → (∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0) → Y'.Ψ = Y.Ψ → Y'.Gm = Y.Gm → Y'.ξ0 = Y.ξ0 → Y'.p0 = Y.p0 → 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsLevGrp l Y → GlobalTheory.EqCovol.IsLevGrp l Y' → GlobalTheory.EqCovol.IsSelfDualTr Y → GlobalTheory.EqCovol.IsSelfDualTr Y' → GlobalTheory.TrueCx.covol Y = GlobalTheory.TrueCx.covol Y' := by
  intro E _ _ _ H l r Y Y' _ _ hΨ hG hξ hp h1 h2 hl hl' hs hs'
  haveI := H.unram
  set F := maximalRealSubfield E
  set c : E ≃ₐ[F] E := IsCMField.complexConj E with hc
  have hM : 3 ≤ l.M' := l.three_le.trans (Nat.le_of_dvd (Nat.lcm_pos (by have := l.three_le; omega) l.A_pos)
    (Nat.dvd_lcm_left _ _))
  have hM0 : 0 < l.M' := by omega
  have hrk : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hH : IsHerm (c : E →+* E) Y.Gm := ⟨IsCMField.complexConj_apply_apply E, by
    by_contra h
    push Not at h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h), Y.Gm_herm, Y.Gm_det⟩
  have hiso : ∃ z : Fin r → E, z ≠ 0 ∧ hf (c : E →+* E) Y.Gm z z = 0 := GlobalTheory.T.exists_isotropic_indefinite_selfDualTraceForm E H r Y h1 h2 hs
  have hcomap : ∀ Z : Data E r, Z.Gm = Y.Gm → IsLevGrp l Z → IsSelfDualTr Z →
      (cong (sgA c) ((emb F).mapMatrix Y.Gm) (hat F (Z.Λ : Set (Fin r → E))) l.M').comap (embGL F) = Z.Γ := by
    intro Z hZ hlZ hsZ
    ext γ
    rw [Subgroup.mem_comap, embGL_mem_cong c Y.Gm Z.Λ_fg Z.Λ_span hM0, GlobalTheory.T.mem_fullLevelGroup_iff_congruence_lcm E H l r Z hlZ hsZ, ← hZ]
    exact ⟨fun h => ⟨⟨h.1, h.2.2.1⟩, h.2.2.2⟩, fun h => ⟨h.1.1,
      GlobalTheory.T.unitaryCongruence_det_eq_one_of_three_le E r _ Z.Gm Z.Λ γ hM Z.Gm_det Z.Λ_fg Z.Λ_span h.1 h.2, h.1.2, h.2⟩⟩
  have hsd : ∀ Z : Data E r, Z.Gm = Y.Gm → Z.ξ0 = Y.ξ0 → IsSelfDualTr Z → GlobalTheory.SW.SelfD Y Z.Λ := by
    intro Z hZ hZξ hsZ
    refine ⟨Z.Λ_fg, fun x => (hsZ x).trans (forall₂_congr fun y _ => ?_)⟩
    rw [GlobalTheory.ThFr.EF_def, hZ, hZξ]
    rcases Y.κ0_xi with h | h <;> rw [h]
    · rw [mul_div_cancel_left₀ _ two_ne_zero]
    · rw [neg_div, mul_div_cancel_left₀ _ two_ne_zero, neg_neg, neg_mul, map_neg]
      exact ⟨fun ⟨k, hk⟩ => ⟨-k, by rw [Int.cast_neg, ← hk, neg_neg]⟩, fun ⟨k, hk⟩ => ⟨-k, by rw [Int.cast_neg, hk]⟩⟩
  obtain ⟨g, hg, hgU⟩ := GlobalTheory.Ker.OntoLat.exists_adelic_matrix F c (fun _ => rfl) Y (hsd Y rfl rfl hs)
    (hsd Y' hG hξ hs')
  replace hgU : IsU (sgA c) ((emb F).mapMatrix Y.Gm) g.1 := hgU
  have hΓ := hcomap Y rfl hl hs
  have hΓ' := hcomap Y' hG hl' hs'
  rw [← map_conj_cong hgU hg] at hΓ'
  generalize hK : cong (sgA c) ((emb F).mapMatrix Y.Gm) (hat F (Y.Λ : Set (Fin r → E))) l.M' = K at hΓ hΓ'

  obtain ⟨a1, a2⟩ := relIndex_comap c Y.Gm Y.Λ_fg Y.Λ_span hrk hH hiso hM0 hgU K hK.symm
  rw [hΓ, hΓ'] at a1 a2
  have e1 : ∀ K : Subgroup (GL (Fin r) E), K.map (MulAut.conj (1 : GL (Fin r) E)).toMonoidHom = K := fun K => by
    ext k
    rw [mem_map_conj]; simp
  have n1 := GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero Y' Y 1 hG (by simp)
  have n2 := GlobalTheory.ArithIndex.relIndex_map_conj_ne_zero Y Y' 1 hG.symm (by simp)
  have hcov := covol_mul_relIndex Y Y' 1 hΨ hG hp (by simp)
  rw [e1] at n1 n2 hcov

  obtain ⟨s, hsU, hs1, hsc⟩ := exists_det_one_conj_eq
    (by rw [← RingHom.map_det]; exact Y.Gm_det.isUnit.map _) hgU
  obtain ⟨γ, hγU, hγ⟩ := exists_inv_mul_mem_cong c Y.Gm Y.Λ_fg Y.Λ_span hrk hH hiso hM0 hsU hs1
  rw [hK] at hγ
  have e2 : K.map (MulAut.conj (g ^ r)).toMonoidHom = K.map (MulAut.conj (embGL F γ)).toMonoidHom := by
    ext k
    rw [mem_map_conj, mem_map_conj, hsc]
    have : s⁻¹ * k * s = ((embGL F γ)⁻¹ * s)⁻¹ * ((embGL F γ)⁻¹ * k * embGL F γ) * ((embGL F γ)⁻¹ * s) := by
      group
    rw [this, K.mul_mem_cancel_right hγ, K.mul_mem_cancel_left (K.inv_mem hγ)]
  obtain ⟨b1, b2⟩ := relIndex_comap c Y.Gm Y.Λ_fg Y.Λ_span hrk hH hiso hM0 (h := embGL F γ)
    ((isU_emb c Y.Gm).2 hγU) K hK.symm
  have e3 : (K.map (MulAut.conj (embGL F γ)).toMonoidHom).comap (embGL F) =
      Y.Γ.map (MulAut.conj γ).toMonoidHom := by
    ext k
    rw [Subgroup.mem_comap, mem_map_conj, mem_map_conj, ← hΓ, Subgroup.mem_comap, map_mul, map_mul, map_inv]
  rw [e3, hΓ] at b1 b2
  have hcov' := mul_left_cancel₀ (GlobalTheory.TrueCx.covol_pos Y).ne' (covol_mul_relIndex Y Y γ rfl rfl rfl hγU)
  have key := GlobalTheory.T.relIndex_map_conj_symm_of_relIndex_map_conj_pow_symm _ K g r (by omega) (a1 ▸ n1) (a2 ▸ n2)
    (by rw [e2, ← b1, ← b2]; exact_mod_cast hcov')
  rw [← a1, ← a2] at key
  rw [← key] at hcov
  exact mul_right_cancel₀ (Nat.cast_ne_zero.2 n1) hcov

end GlobalTheory.EqCovol.SameSpace
