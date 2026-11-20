import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumStabilizerGaussDecompositionBigCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInversePreservingAdelicLatticeAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowIdempotentAdelicLatticeModPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceZeroAdeleUnitLatticeAtInertPlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.TwoFacCore

/- English proof (translation)
Use `set f := k + ki + 1 + 1 with hf`. Use `set F := f ^ (N₀ + 1) with hFdef`. Use `set G := f ^ N₀ with hG`. Establish `hF : f * G = F` using `by rw [hFdef, hG, pow_succ']`. Establish `hF2 : F ^ 2 = F` using `by rw [hFdef, ← pow_mul, mul_comm]; exact hD`.

Establish `he : (1 - F) ^ 2 = 1 - F` using `by linear_combination hF2`. Use `⟨isUnit_iff_exists_inv.mpr ⟨1 - up * β * (1 - F), ?_⟩, isUnit_iff_exists_inv.mpr ⟨1 + um * β * (1 - F), ?_⟩, ?_⟩` and prove the remaining obligations. Take the linear combination `(-up * β ^ 2) * he - β * (1 - F) * hp`. Take the linear combination `(-um * β ^ 2) * he + β * (1 - F) * hm`. Use `set x := -((1 - β) * h * b) * (1 + k) with hx`.

Use `set s := ∑ i ∈ Finset.range (2 * (N₀ + 1)), x ^ i with hsdef`. Establish `hs : s * (x - 1) = x ^ (2 * (N₀ + 1)) - 1` using `geom_sum_mul x _`. Establish `hn : (1 + k) ^ 2 = k * f` using `by rw [hf]; linear_combination (-1 : Q) * hK`. Establish `hxp : x ^ (2 * (N₀ + 1)) = ((1 - β) * h * b) ^ (2 * (N₀ + 1)) * (k ^ (N₀ + 1) * F)`. Rewrite using `[hx, neg_mul, Even.neg_pow ⟨N₀ + 1, by ring⟩, mul_pow ((1 - β) * h * b) (1 + k), pow_mul (1 + k), hn, mul_pow k f]`.

Establish `hx0 : x ^ (2 * (N₀ + 1)) * (1 - F) = 0`. Rewrite using `[hxp]`. Take the linear combination `(-((1 - β) * h * b) ^ (2 * (N₀ + 1)) * k ^ (N₀ + 1)) * hF2`. Establish `hAA : ((1 + β) + (1 - β) * k) * (h * b * s) = 1 - x ^ (2 * (N₀ + 1))`. Rewrite `hs`, the goal using `[hx]`.

Take the linear combination `(s * β * b) * h2 + s * hb - hs`. Establish `e1 : (1 + k) * ((1 + k) * ki * G) = F`. Rewrite using `[← hF, hf]`. Take the linear combination `(2 + k) * G * hK`. Use `isUnit_iff_exists_inv.mpr ⟨(1 + k) * ki * G * F + h * b * s * (1 - F), ?_⟩` and prove the remaining obligations.

Take the linear combination `F ^ 2 * e1 + (F + 2 - ((1 + k) * (h * b * s) + ((1 + β) + (1 - β) * k) * ((1 + k) * ki * G)) - x ^ (2 * (N₀ + 1))) * hF2 + (1 - F) ^ 2 * hAA - hx0`.
-/
theorem alg {Q : Type*} [CommRing Q] (k ki β b up um h : Q) (N₀ : ℕ) (hK : k * ki = 1) (hb : β * b = 1)
    (h2 : h + h = 1) (hp : (1 + β) * up = 1) (hm : (1 - β) * um = 1)
    (hD : (k + ki + 1 + 1) ^ (2 * (N₀ + 1)) = (k + ki + 1 + 1) ^ (N₀ + 1)) :
    IsUnit (1 + β * (1 - (k + ki + 1 + 1) ^ (N₀ + 1))) ∧ IsUnit (1 - β * (1 - (k + ki + 1 + 1) ^ (N₀ + 1))) ∧
    IsUnit (1 + β * (1 - (k + ki + 1 + 1) ^ (N₀ + 1)) + k * (1 - β * (1 - (k + ki + 1 + 1) ^ (N₀ + 1)))) := by
  set f := k + ki + 1 + 1 with hf
  set F := f ^ (N₀ + 1) with hFdef
  set G := f ^ N₀ with hG
  have hF : f * G = F := by rw [hFdef, hG, pow_succ']
  have hF2 : F ^ 2 = F := by rw [hFdef, ← pow_mul, mul_comm]; exact hD
  have he : (1 - F) ^ 2 = 1 - F := by linear_combination hF2
  refine ⟨isUnit_iff_exists_inv.mpr ⟨1 - up * β * (1 - F), ?_⟩, isUnit_iff_exists_inv.mpr ⟨1 + um * β * (1 - F), ?_⟩, ?_⟩
  · linear_combination (-up * β ^ 2) * he - β * (1 - F) * hp
  · linear_combination (-um * β ^ 2) * he + β * (1 - F) * hm
  set x := -((1 - β) * h * b) * (1 + k) with hx
  set s := ∑ i ∈ Finset.range (2 * (N₀ + 1)), x ^ i with hsdef
  have hs : s * (x - 1) = x ^ (2 * (N₀ + 1)) - 1 := geom_sum_mul x _
  have hn : (1 + k) ^ 2 = k * f := by rw [hf]; linear_combination (-1 : Q) * hK
  have hxp : x ^ (2 * (N₀ + 1)) = ((1 - β) * h * b) ^ (2 * (N₀ + 1)) * (k ^ (N₀ + 1) * F) := by
    rw [hx, neg_mul, Even.neg_pow ⟨N₀ + 1, by ring⟩, mul_pow ((1 - β) * h * b) (1 + k), pow_mul (1 + k), hn, mul_pow k f]
  have hx0 : x ^ (2 * (N₀ + 1)) * (1 - F) = 0 := by
    rw [hxp]; linear_combination (-((1 - β) * h * b) ^ (2 * (N₀ + 1)) * k ^ (N₀ + 1)) * hF2
  have hAA : ((1 + β) + (1 - β) * k) * (h * b * s) = 1 - x ^ (2 * (N₀ + 1)) := by
    rw [hx] at hs ⊢; linear_combination (s * β * b) * h2 + s * hb - hs
  have e1 : (1 + k) * ((1 + k) * ki * G) = F := by
    rw [← hF, hf]; linear_combination (2 + k) * G * hK
  refine isUnit_iff_exists_inv.mpr ⟨(1 + k) * ki * G * F + h * b * s * (1 - F), ?_⟩
  linear_combination F ^ 2 * e1 + (F + 2 - ((1 + k) * (h * b * s) + ((1 + β) + (1 - β) * k) * ((1 + k) * ki * G)) -
    x ^ (2 * (N₀ + 1))) * hF2 + (1 - F) ^ 2 * hAA - hx0

end GlobalTheory.TwoFacCore

noncomputable section
namespace GlobalTheory.TwoFacCore

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Ring

variable {d : ℕ} {S : Type*} [CommRing S] (φ : S →+* Matrix (Fin d) (Fin d) (AE F E))
  (Λ : AddSubgroup (Fin d → AE F E)) (p : ℕ)

def keepT : Subring S where
  carrier := {x | ∀ z ∈ Λ, φ x *ᵥ z ∈ Λ}
  mul_mem' {x y} hx hy z hz := by
    simp only [Set.mem_setOf_eq, map_mul, ← Matrix.mulVec_mulVec] at *
    exact hx _ (hy z hz)
  one_mem' z hz := by simpa using hz
  add_mem' {x y} hx hy z hz := by
    simp only [Set.mem_setOf_eq, map_add, Matrix.add_mulVec] at *
    exact add_mem (hx z hz) (hy z hz)
  zero_mem' z hz := by simp
  neg_mem' {x} hx z hz := by
    simp only [Set.mem_setOf_eq, map_neg, Matrix.neg_mulVec] at *
    exact neg_mem (hx z hz)

def congI : Ideal (keepT φ Λ) where
  carrier := {x | ∀ z ∈ Λ, ∃ y ∈ Λ, φ (x : S) *ᵥ z = p • y}
  add_mem' {x y} hx hy z hz := by
    obtain ⟨a, ha, e1⟩ := hx z hz
    obtain ⟨c, hc, e2⟩ := hy z hz
    refine ⟨a + c, add_mem ha hc, ?_⟩
    rw [AddMemClass.coe_add, map_add, Matrix.add_mulVec, e1, e2, smul_add]
  zero_mem' z hz := ⟨0, zero_mem _, by simp⟩
  smul_mem' c {x} hx z hz := by
    obtain ⟨a, ha, e⟩ := hx z hz
    refine ⟨φ (c : S) *ᵥ a, c.2 a ha, ?_⟩
    rw [smul_eq_mul, MulMemClass.coe_mul, map_mul, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_smul]

/- English proof (translation)
Use `Ideal.Quotient.eq.mpr fun z hz => ⟨0, zero_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[AddSubgroupClass.coe_sub, map_sub, Matrix.sub_mulVec, h z hz, sub_self, smul_zero]`.
-/
theorem mk_eq_of {x y : keepT φ Λ} (h : ∀ z ∈ Λ, φ (x : S) *ᵥ z = φ (y : S) *ᵥ z) :
    Ideal.Quotient.mk (congI φ Λ p) x = Ideal.Quotient.mk (congI φ Λ p) y := by
  refine Ideal.Quotient.eq.mpr fun z hz => ⟨0, zero_mem _, ?_⟩
  rw [AddSubgroupClass.coe_sub, map_sub, Matrix.sub_mulVec, h z hz, sub_self, smul_zero]

/- English proof (translation)
Take `⟨u, hu⟩` from `hx`. Take `⟨t, ht⟩` from `Ideal.Quotient.mk_surjective (I := congI φ Λ p) (↑u⁻¹)`. Establish `h1 : Ideal.Quotient.mk (congI φ Λ p) (x * t) = Ideal.Quotient.mk (congI φ Λ p) 1`. Rewrite using `[map_mul, ← hu, ht, Units.mul_inv, map_one]`. Establish `h2` using `Ideal.Quotient.eq.mp h1`.

Introduce `z hz`. Take `⟨a, ha, e⟩` from `h2 z hz`. Use `⟨φ (t : S) *ᵥ z, t.2 z hz, -a, neg_mem ha, ?_⟩` and prove the remaining obligations. Rewrite `e` using `[AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one, map_sub, map_mul, map_one, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec, sub_eq_iff_eq_add]`. Rewrite using `[smul_neg, e]`.

Normalize the expressions using the abelian group laws.
-/
theorem surj_of_isUnit {x : keepT φ Λ} (hx : IsUnit (Ideal.Quotient.mk (congI φ Λ p) x)) :
    ∀ z ∈ Λ, ∃ y ∈ Λ, ∃ y' ∈ Λ, z = φ (x : S) *ᵥ y + p • y' := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (I := congI φ Λ p) (↑u⁻¹)
  have h1 : Ideal.Quotient.mk (congI φ Λ p) (x * t) = Ideal.Quotient.mk (congI φ Λ p) 1 := by
    rw [map_mul, ← hu, ht, Units.mul_inv, map_one]
  have h2 := Ideal.Quotient.eq.mp h1
  intro z hz
  obtain ⟨a, ha, e⟩ := h2 z hz
  refine ⟨φ (t : S) *ᵥ z, t.2 z hz, -a, neg_mem ha, ?_⟩
  rw [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one, map_sub, map_mul, map_one, Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.one_mulVec, sub_eq_iff_eq_add] at e
  rw [smul_neg, e]; abel

end Ring

end GlobalTheory.TwoFacCore

noncomputable section
namespace GlobalTheory.TwoFacCore

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def SelfAdj (σ : E →ₐ[F] E) {d : ℕ} (J Q : Matrix (Fin d) (Fin d) (AE F E)) : Prop :=
  Qᵀ * J = J * (cA σ).mapMatrix Q

/- English proof (translation)
Simplify using `[SelfAdj]`.
-/
theorem selfAdj_one (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) (AE F E)) : SelfAdj σ J 1 := by
  simp [SelfAdj]

/- English proof (translation)
Unfold `SelfAdj at *`. Rewrite using `[Matrix.transpose_add, Matrix.add_mul, hP, hQ, map_add, Matrix.mul_add]`.
-/
theorem selfAdj_add {σ : E →ₐ[F] E} {d : ℕ} {J P Q : Matrix (Fin d) (Fin d) (AE F E)} (hP : SelfAdj σ J P)
    (hQ : SelfAdj σ J Q) : SelfAdj σ J (P + Q) := by
  unfold SelfAdj at *
  rw [Matrix.transpose_add, Matrix.add_mul, hP, hQ, map_add, Matrix.mul_add]

/- English proof (translation)
Unfold `SelfAdj at *`. Rewrite using `[Matrix.transpose_sub, Matrix.sub_mul, hP, hQ, map_sub, Matrix.mul_sub]`.
-/
theorem selfAdj_sub {σ : E →ₐ[F] E} {d : ℕ} {J P Q : Matrix (Fin d) (Fin d) (AE F E)} (hP : SelfAdj σ J P)
    (hQ : SelfAdj σ J Q) : SelfAdj σ J (P - Q) := by
  unfold SelfAdj at *
  rw [Matrix.transpose_sub, Matrix.sub_mul, hP, hQ, map_sub, Matrix.mul_sub]

/- English proof (translation)
The claim follows from `| 0 => by rw [pow_zero]; exact selfAdj_one σ J | n + 1 => by have ih := selfAdj_pow hQ n unfold SelfAdj at * rw [pow_succ, Matrix.transpose_mul, Matrix.mul_assoc, ih, ← Matrix.mul_assoc, hQ, Matrix.mul_assoc, ← map_mul, ← pow_succ'] rw [pow_succ]`.
-/
theorem selfAdj_pow {σ : E →ₐ[F] E} {d : ℕ} {J Q : Matrix (Fin d) (Fin d) (AE F E)} (hQ : SelfAdj σ J Q) :
    ∀ n : ℕ, SelfAdj σ J (Q ^ n)
  | 0 => by rw [pow_zero]; exact selfAdj_one σ J
  | n + 1 => by
    have ih := selfAdj_pow hQ n
    unfold SelfAdj at *
    rw [pow_succ, Matrix.transpose_mul, Matrix.mul_assoc, ih, ← Matrix.mul_assoc, hQ, Matrix.mul_assoc, ← map_mul,
      ← pow_succ']
    rw [pow_succ]

/- English proof (translation)
Establish `h1 : Kᵀ * J = J * (cA σ).mapMatrix Ki`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : Kiᵀ * J = J * (cA σ).mapMatrix K`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : SelfAdj σ J (K + Ki)`.

Unfold `SelfAdj`. Rewrite using `[Matrix.transpose_add, Matrix.add_mul, h1, h2, map_add, Matrix.mul_add, add_comm]`. Conclude with `selfAdj_add (selfAdj_add h3 (selfAdj_one σ J)) (selfAdj_one σ J)`.
-/
theorem sa_gen {σ : E →ₐ[F] E} {d : ℕ}
    {J K Ki : Matrix (Fin d) (Fin d) (AE F E)} (hK : Kᵀ * J * K.map (cA σ) = J) (hKi : Kiᵀ * J * Ki.map (cA σ) = J)
    (hKK : K * Ki = 1) (hKiK : Ki * K = 1) : SelfAdj σ J (K + Ki + 1 + 1) := by
  have h1 : Kᵀ * J = J * (cA σ).mapMatrix Ki := by
    calc Kᵀ * J = Kᵀ * J * ((cA σ).mapMatrix K * (cA σ).mapMatrix Ki) := by rw [← map_mul, hKK, map_one, Matrix.mul_one]
      _ = J * (cA σ).mapMatrix Ki := by rw [← Matrix.mul_assoc, AlgHom.mapMatrix_apply, hK]
  have h2 : Kiᵀ * J = J * (cA σ).mapMatrix K := by
    calc Kiᵀ * J = Kiᵀ * J * ((cA σ).mapMatrix Ki * (cA σ).mapMatrix K) := by rw [← map_mul, hKiK, map_one, Matrix.mul_one]
      _ = J * (cA σ).mapMatrix K := by rw [← Matrix.mul_assoc, AlgHom.mapMatrix_apply, hKi]
  have h3 : SelfAdj σ J (K + Ki) := by
    unfold SelfAdj
    rw [Matrix.transpose_add, Matrix.add_mul, h1, h2, map_add, Matrix.mul_add, add_comm]
  exact selfAdj_add (selfAdj_add h3 (selfAdj_one σ J)) (selfAdj_one σ J)

end GlobalTheory.TwoFacCore

noncomputable section
namespace GlobalTheory.TwoFacCore

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hcomm : ∀ x ∈ ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E))), ∀ y ∈ ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E))), x * y = y * x`. Introduce `x hx y hy`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy`. Apply the tactic sequence `rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [hKK, hKiK]`. Use `letI : CommRing (Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))) := Algebra.adjoinCommRingOfComm (AE F E) hcomm`.

Set `φ : (Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))) →+* Matrix (Fin d) (Fin d) (AE F E)` to `(Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))).val.toRingHom`. Set `kS : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))` to `⟨K, Algebra.subset_adjoin (by simp)⟩`. Set `kiS : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))` to `⟨Ki, Algebra.subset_adjoin (by simp)⟩`. Set `cS : AE F E → Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))` to `fun c => algebraMap (AE F E) _ c`. Establish `hφk : φ kS = K` using `rfl`.

Establish `hφki : φ kiS = Ki` using `rfl`. Establish `hφc : ∀ c z, φ (cS c) *ᵥ z = c • z`. Introduce `c z`. Use `show (algebraMap (AE F E) (Matrix (Fin d) (Fin d) (AE F E)) c) *ᵥ z = c • z`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]`.

Set `kT : keepT φ Λ` to `⟨kS, fun z hz => hK z hz⟩`. Set `kiT : keepT φ Λ` to `⟨kiS, fun z hz => hKi z hz⟩`. Establish `cmem : ∀ c : AE F E, (∀ z ∈ Λ, c • z ∈ Λ) → cS c ∈ keepT φ Λ` using `fun c hc z hz => by show φ (cS c) *ᵥ z ∈ Λ`. Rewrite using `[hφc]`. Conclude with `hc z hz`.

Set `βT : keepT φ Λ` to `⟨cS β, cmem β fun z hz => (hsc z hz).1⟩`. Set `bT : keepT φ Λ` to `⟨cS b, cmem b fun z hz => (hsc z hz).2.1⟩`. Set `upT : keepT φ Λ` to `⟨cS up, cmem up fun z hz => (hsc z hz).2.2.1⟩`. Set `umT : keepT φ Λ` to `⟨cS um, cmem um fun z hz => (hsc z hz).2.2.2.1⟩`. Set `hT : keepT φ Λ` to `⟨cS h, cmem h fun z hz => (hsc z hz).2.2.2.2⟩`.

Set `mk` to `Ideal.Quotient.mk (congI φ Λ p)`. Establish `hK' : mk kT * mk kiT = 1`. Establish `: mk (kT * kiT) = mk 1` using `mk_eq_of φ Λ p fun z hz => by show (K * Ki) *ᵥ z = (1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z`. Rewrite using `[hKK]`. Simplify `this` using `only [map_mul, map_one]`.

Establish `hsc2 : ∀ (c c' : AE F E) (z : Fin d → AE F E), φ (cS c * cS c') *ᵥ z = (c * c') • z`. Introduce `c c' z`. Rewrite using `[map_mul, ← Matrix.mulVec_mulVec, hφc, hφc, smul_smul]`. Establish `hb' : mk βT * mk bT = 1`. Establish `: mk (βT * bT) = mk 1` using `mk_eq_of φ Λ p fun z hz => by show φ (cS β * cS b) *ᵥ z = (1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z`.

Rewrite using `[hsc2, hb z hz, Matrix.one_mulVec]`. Simplify `this` using `only [map_mul, map_one]`. Establish `hh' : mk hT + mk hT = 1`. Establish `: mk (hT + hT) = mk 1` using `mk_eq_of φ Λ p fun z hz => by show φ (cS h + cS h) *ᵥ z = (1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z`. Rewrite using `[map_add, Matrix.add_mulVec, hφc, ← add_smul, hh z hz, Matrix.one_mulVec]`.

Simplify `this` using `only [map_add, map_one]`. Establish `hp' : (1 + mk βT) * mk upT = 1`. Establish `: mk ((1 + βT) * upT) = mk 1` using `mk_eq_of φ Λ p fun z hz => by show φ ((1 + cS β) * cS up) *ᵥ z = (1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z`. Establish `e : (1 + cS β) * cS up = cS ((1 + β) * up)` using `by simp only [cS, map_add, map_mul, map_one]`. Rewrite using `[e, hφc, hp z hz, Matrix.one_mulVec]`.

Simplify `this` using `only [map_mul, map_add, map_one]`. Establish `hm' : (1 - mk βT) * mk umT = 1`. Establish `: mk ((1 - βT) * umT) = mk 1` using `mk_eq_of φ Λ p fun z hz => by show φ ((1 - cS β) * cS um) *ᵥ z = (1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z`. Establish `e : (1 - cS β) * cS um = cS ((1 - β) * um)` using `by simp only [cS, map_sub, map_mul, map_one]`. Rewrite using `[e, hφc, hm z hz, Matrix.one_mulVec]`.

Simplify `this` using `only [map_mul, map_sub, map_one]`. Set `fT : keepT φ Λ` to `kT + kiT + 1 + 1`. Establish `hφf : φ ((fT : _)) = K + Ki + 1 + 1` using `by show φ (kS + kiS + 1 + 1) = K + Ki + 1 + 1`. Rewrite using `[map_add, map_add, map_add, map_one, hφk, hφki]`. Establish `hD' : (mk kT + mk kiT + 1 + 1) ^ (2 * (N₀ + 1)) = (mk kT + mk kiT + 1 + 1) ^ (N₀ + 1)`.

Establish `e : mk kT + mk kiT + 1 + 1 = mk fT` using `by simp only [fT, map_add, map_one]`. Rewrite using `[e, ← map_pow, ← map_pow]`. Use `Ideal.Quotient.eq.mpr fun z hz => ?_` and prove the remaining obligations. Take `⟨y, hy, ey⟩` from `hD z hz`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations.

Rewrite using `[AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, map_sub, map_pow, map_pow, hφf, Matrix.sub_mulVec]`. Conclude with `ey`. Take `⟨u1, u2, u3⟩` from `alg (mk kT) (mk kiT) (mk βT) (mk bT) (mk upT) (mk umT) (mk hT) N₀ hK' hb' hh' hp' hm' hD'`. Set `YT : keepT φ Λ` to `βT * (1 - fT ^ (N₀ + 1))`. Establish `hφY : φ (YT : _) = Y` using `by show φ (cS β * (1 - (kS + kiS + 1 + 1) ^ (N₀ + 1))) = Y`.

Rewrite using `[map_mul, map_sub, map_one, map_pow, map_add, map_add, map_add, map_one, hφk, hφki, hY, Algebra.smul_def]`. Both sides reduce to the same expression. Establish `eY : mk βT * (1 - (mk kT + mk kiT + 1 + 1) ^ (N₀ + 1)) = mk YT`. Simplify using `only [YT, fT, map_mul, map_sub, map_one, map_pow, map_add]`. Rewrite `u1`, `u2`, `u3` using `[eY]`.

Establish `u1' : IsUnit (mk (1 + YT))` using `by rw [map_add, map_one]; exact u1`. Establish `u2' : IsUnit (mk (1 - YT))` using `by rw [map_sub, map_one]; exact u2`. Establish `u3' : IsUnit (mk (1 + YT + kT * (1 - YT)))`. Rewrite using `[map_add, map_add, map_mul, map_sub, map_one]`. Conclude with `u3`.

Use `⟨fun z hz => hφY ▸ YT.2 z hz, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `s1` using `surj_of_isUnit φ Λ p u1'`. Establish `: φ ((1 + YT : keepT φ Λ) : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))) = 1 + Y` using `by show φ (1 + (YT : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E))))) = 1 + Y`. Rewrite using `[map_add, map_one, hφY]`. Rewrite `s1` using `[this]`. Then use the resulting hypothesis.

Establish `s2` using `surj_of_isUnit φ Λ p u2'`. Establish `: φ ((1 - YT : keepT φ Λ) : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))) = 1 - Y` using `by show φ (1 - (YT : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E))))) = 1 - Y`. Rewrite using `[map_sub, map_one, hφY]`. Rewrite `s2` using `[this]`. Then use the resulting hypothesis. Establish `s3` using `surj_of_isUnit φ Λ p u3'`.

Establish `: φ ((1 + YT + kT * (1 - YT) : keepT φ Λ) : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))) = 1 + Y + K * (1 - Y)` using `by show φ (1 + (YT : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))) + kS * (1 - (YT : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))))) = 1 + Y + K * (1 - Y)`. Rewrite using `[map_add, map_add, map_mul, map_sub, map_one, hφY, hφk]`. Rewrite `s3` using `[this]`. Then use the resulting hypothesis.
-/
theorem units_mod {d : ℕ} (Λ : AddSubgroup (Fin d → AE F E)) (p : ℕ) (K Ki : Matrix (Fin d) (Fin d) (AE F E))
    (β b up um h : AE F E) (N₀ : ℕ) (hKK : K * Ki = 1) (hKiK : Ki * K = 1)
    (hK : ∀ z ∈ Λ, K *ᵥ z ∈ Λ) (hKi : ∀ z ∈ Λ, Ki *ᵥ z ∈ Λ)
    (hsc : ∀ z ∈ Λ, β • z ∈ Λ ∧ b • z ∈ Λ ∧ up • z ∈ Λ ∧ um • z ∈ Λ ∧ h • z ∈ Λ)
    (hb : ∀ z ∈ Λ, (β * b) • z = z) (hh : ∀ z ∈ Λ, (h + h) • z = z) (hp : ∀ z ∈ Λ, ((1 + β) * up) • z = z)
    (hm : ∀ z ∈ Λ, ((1 - β) * um) • z = z)
    (hD : ∀ z ∈ Λ, ∃ y ∈ Λ, ((K + Ki + 1 + 1) ^ (2 * (N₀ + 1))) *ᵥ z - ((K + Ki + 1 + 1) ^ (N₀ + 1)) *ᵥ z = p • y)
    (Y : Matrix (Fin d) (Fin d) (AE F E)) (hY : Y = β • (1 - (K + Ki + 1 + 1) ^ (N₀ + 1))) :
    (∀ z ∈ Λ, Y *ᵥ z ∈ Λ) ∧
    (∀ z ∈ Λ, ∃ y ∈ Λ, ∃ y' ∈ Λ, z = (1 + Y) *ᵥ y + p • y') ∧
    (∀ z ∈ Λ, ∃ y ∈ Λ, ∃ y' ∈ Λ, z = (1 - Y) *ᵥ y + p • y') ∧
    (∀ z ∈ Λ, ∃ y ∈ Λ, ∃ y' ∈ Λ, z = (1 + Y + K * (1 - Y)) *ᵥ y + p • y') := by
  have hcomm : ∀ x ∈ ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E))),
      ∀ y ∈ ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E))), x * y = y * x := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [hKK, hKiK]
  letI : CommRing (Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))) :=
    Algebra.adjoinCommRingOfComm (AE F E) hcomm
  let φ : (Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))) →+*
      Matrix (Fin d) (Fin d) (AE F E) := (Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))).val.toRingHom
  let kS : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E))) :=
    ⟨K, Algebra.subset_adjoin (by simp)⟩
  let kiS : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E))) :=
    ⟨Ki, Algebra.subset_adjoin (by simp)⟩
  let cS : AE F E → Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E))) :=
    fun c => algebraMap (AE F E) _ c
  have hφk : φ kS = K := rfl
  have hφki : φ kiS = Ki := rfl
  have hφc : ∀ c z, φ (cS c) *ᵥ z = c • z := by
    intro c z
    show (algebraMap (AE F E) (Matrix (Fin d) (Fin d) (AE F E)) c) *ᵥ z = c • z
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  let kT : keepT φ Λ := ⟨kS, fun z hz => hK z hz⟩
  let kiT : keepT φ Λ := ⟨kiS, fun z hz => hKi z hz⟩
  have cmem : ∀ c : AE F E, (∀ z ∈ Λ, c • z ∈ Λ) → cS c ∈ keepT φ Λ := fun c hc z hz => by
    show φ (cS c) *ᵥ z ∈ Λ
    rw [hφc]; exact hc z hz
  let βT : keepT φ Λ := ⟨cS β, cmem β fun z hz => (hsc z hz).1⟩
  let bT : keepT φ Λ := ⟨cS b, cmem b fun z hz => (hsc z hz).2.1⟩
  let upT : keepT φ Λ := ⟨cS up, cmem up fun z hz => (hsc z hz).2.2.1⟩
  let umT : keepT φ Λ := ⟨cS um, cmem um fun z hz => (hsc z hz).2.2.2.1⟩
  let hT : keepT φ Λ := ⟨cS h, cmem h fun z hz => (hsc z hz).2.2.2.2⟩
  let mk := Ideal.Quotient.mk (congI φ Λ p)
  have hK' : mk kT * mk kiT = 1 := by
    have : mk (kT * kiT) = mk 1 := mk_eq_of φ Λ p fun z hz => by
      show (K * Ki) *ᵥ z = (1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z
      rw [hKK]
    simpa only [map_mul, map_one] using this
  have hsc2 : ∀ (c c' : AE F E) (z : Fin d → AE F E), φ (cS c * cS c') *ᵥ z = (c * c') • z := by
    intro c c' z
    rw [map_mul, ← Matrix.mulVec_mulVec, hφc, hφc, smul_smul]
  have hb' : mk βT * mk bT = 1 := by
    have : mk (βT * bT) = mk 1 := mk_eq_of φ Λ p fun z hz => by
      show φ (cS β * cS b) *ᵥ z = (1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z
      rw [hsc2, hb z hz, Matrix.one_mulVec]
    simpa only [map_mul, map_one] using this
  have hh' : mk hT + mk hT = 1 := by
    have : mk (hT + hT) = mk 1 := mk_eq_of φ Λ p fun z hz => by
      show φ (cS h + cS h) *ᵥ z = (1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z
      rw [map_add, Matrix.add_mulVec, hφc, ← add_smul, hh z hz, Matrix.one_mulVec]
    simpa only [map_add, map_one] using this
  have hp' : (1 + mk βT) * mk upT = 1 := by
    have : mk ((1 + βT) * upT) = mk 1 := mk_eq_of φ Λ p fun z hz => by
      show φ ((1 + cS β) * cS up) *ᵥ z = (1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z
      have e : (1 + cS β) * cS up = cS ((1 + β) * up) := by simp only [cS, map_add, map_mul, map_one]
      rw [e, hφc, hp z hz, Matrix.one_mulVec]
    simpa only [map_mul, map_add, map_one] using this
  have hm' : (1 - mk βT) * mk umT = 1 := by
    have : mk ((1 - βT) * umT) = mk 1 := mk_eq_of φ Λ p fun z hz => by
      show φ ((1 - cS β) * cS um) *ᵥ z = (1 : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z
      have e : (1 - cS β) * cS um = cS ((1 - β) * um) := by simp only [cS, map_sub, map_mul, map_one]
      rw [e, hφc, hm z hz, Matrix.one_mulVec]
    simpa only [map_mul, map_sub, map_one] using this
  let fT : keepT φ Λ := kT + kiT + 1 + 1
  have hφf : φ ((fT : _)) = K + Ki + 1 + 1 := by
    show φ (kS + kiS + 1 + 1) = K + Ki + 1 + 1
    rw [map_add, map_add, map_add, map_one, hφk, hφki]
  have hD' : (mk kT + mk kiT + 1 + 1) ^ (2 * (N₀ + 1)) = (mk kT + mk kiT + 1 + 1) ^ (N₀ + 1) := by
    have e : mk kT + mk kiT + 1 + 1 = mk fT := by simp only [fT, map_add, map_one]
    rw [e, ← map_pow, ← map_pow]
    refine Ideal.Quotient.eq.mpr fun z hz => ?_
    obtain ⟨y, hy, ey⟩ := hD z hz
    refine ⟨y, hy, ?_⟩
    rw [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, map_sub, map_pow, map_pow, hφf,
      Matrix.sub_mulVec]
    exact ey
  obtain ⟨u1, u2, u3⟩ := alg (mk kT) (mk kiT) (mk βT) (mk bT) (mk upT) (mk umT) (mk hT) N₀ hK' hb' hh' hp' hm' hD'
  let YT : keepT φ Λ := βT * (1 - fT ^ (N₀ + 1))
  have hφY : φ (YT : _) = Y := by
    show φ (cS β * (1 - (kS + kiS + 1 + 1) ^ (N₀ + 1))) = Y
    rw [map_mul, map_sub, map_one, map_pow, map_add, map_add, map_add, map_one, hφk, hφki, hY, Algebra.smul_def]
    rfl
  have eY : mk βT * (1 - (mk kT + mk kiT + 1 + 1) ^ (N₀ + 1)) = mk YT := by
    simp only [YT, fT, map_mul, map_sub, map_one, map_pow, map_add]
  rw [eY] at u1 u2 u3
  have u1' : IsUnit (mk (1 + YT)) := by rw [map_add, map_one]; exact u1
  have u2' : IsUnit (mk (1 - YT)) := by rw [map_sub, map_one]; exact u2
  have u3' : IsUnit (mk (1 + YT + kT * (1 - YT))) := by
    rw [map_add, map_add, map_mul, map_sub, map_one]; exact u3
  refine ⟨fun z hz => hφY ▸ YT.2 z hz, ?_, ?_, ?_⟩
  · have s1 := surj_of_isUnit φ Λ p u1'
    have : φ ((1 + YT : keepT φ Λ) : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))) = 1 + Y := by
      show φ (1 + (YT : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E))))) = 1 + Y
      rw [map_add, map_one, hφY]
    rwa [this] at s1
  · have s2 := surj_of_isUnit φ Λ p u2'
    have : φ ((1 - YT : keepT φ Λ) : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))) = 1 - Y := by
      show φ (1 - (YT : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E))))) = 1 - Y
      rw [map_sub, map_one, hφY]
    rwa [this] at s2
  · have s3 := surj_of_isUnit φ Λ p u3'
    have : φ ((1 + YT + kT * (1 - YT) : keepT φ Λ) : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E))))
        = 1 + Y + K * (1 - Y) := by
      show φ (1 + (YT : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))) +
        kS * (1 - (YT : Algebra.adjoin (AE F E) ({K, Ki} : Set (Matrix (Fin d) (Fin d) (AE F E)))))) = 1 + Y + K * (1 - Y)
      rw [map_add, map_add, map_mul, map_sub, map_one, hφY, hφk]
    rwa [this] at s3

end GlobalTheory.TwoFacCore

noncomputable section
namespace GlobalTheory.TwoFacCore

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]`.
-/
theorem smul_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (c : AE F E) (Q : Matrix (Fin d) (Fin d) (AE F E)) : (c • Q).map (cA σ) = cA σ c • Q.map (cA σ) := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hT v w hin k hk`. Establish `hlat : G.W.L.IsLattice E` using `hT.geo.hW.lat`. Take `⟨h2v, h3, -⟩` from `hT.base.inert v w hin`. Establish `hp0 : 0 < Ideal.absNorm v.asIdeal` using `by omega`. Establish `hpv : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal` using `Ideal.absNorm_mem _`.

Take `⟨β, b, up, um, hβat, hβσ, hsc⟩` from `GlobalTheory.T.exists_traceZero_adele_unit_lattice_at_inert_place F E σ B hT.base (a + a') G.W v w hin`. Establish `hKK : mat k * mat k⁻¹ = 1` using `by show mat (k * k⁻¹) = 1`. Rewrite using `[mul_inv_cancel]`. Both sides reduce to the same expression. Establish `hKiK : mat k⁻¹ * mat k = 1` using `by show mat (k⁻¹ * k) = 1`.

Rewrite using `[inv_mul_cancel]`. Both sides reduce to the same expression. Establish `hKk : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, mat k *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v` using `fun z hz => (hk.2 z hz).1`. Establish `hKik : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, mat k⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v` using `fun z hz => (hk.2 z hz).2`. Establish `hfk : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (mat k + mat k⁻¹ + 1 + 1) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v`.

Introduce `z hz`. Rewrite using `[Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]`. Conclude with `add_mem (add_mem (add_mem (hKk z hz) (hKik z hz)) hz) hz`. Take `⟨N, hN0, hN⟩` from `GlobalTheory.T.exists_pow_idempotent_adelicLattice_mod_prime F E (a + a') G.W hlat v _ hp0 hpv _ hfk`. Take `⟨N₀, rfl⟩ : ∃ N₀, N = N₀ + 1` from `⟨N - 1, by omega⟩`.

Establish `hh : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (algebraMap (AF F) (AE F E) ⅟(2 : AF F)) • z ∈ GlobalTheory.InertSph.latAt G.W v` using `fun z hz => by rw [algebraMap_smul]; exact GlobalTheory.DblVacGauss.invOf_two_smul_mem_latAt G.W v h2v hz`. Establish `hh2 : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (algebraMap (AF F) (AE F E) ⅟(2 : AF F) + algebraMap (AF F) (AE F E) ⅟(2 : AF F)) • z = z`. Introduce `z _`. Rewrite using `[← map_add, ← two_mul, mul_invOf_self', map_one, one_smul]`. Take `⟨hYk, s1, s2, s3⟩` from `units_mod (GlobalTheory.InertSph.latAt G.W v) (Ideal.absNorm v.asIdeal) (mat k) (mat k⁻¹) β b up um (algebraMap (AF F) (AE F E) ⅟(2 : AF F)) N₀ hKK hKiK hKk hKik (fun z hz => ⟨(hsc z hz).1, (hsc z hz).2.1, (hsc z hz).2.2.1, (hsc z hz).2.2.2.1, hh z hz⟩) (fun z hz => (hsc z hz).2. …`.

Use `set Y := β • (1 - (mat k + mat k⁻¹ + 1 + 1) ^ (N₀ + 1)) with hYdef`. Establish `hYat : At (evFin F v) Y`. Introduce `u hu`. Rewrite using `[hYdef, ← smul_assoc, hβat u hu, zero_smul]`. Establish `hKat : At (evFin F v) (mat k - 1)` using `hk.1`.

Establish `keepAdd : ∀ {A C : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)}, (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) → (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, C *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) → ∀ z ∈ GlobalTheory.InertSph.latAt G.W …` using `fun hA hC z hz => by rw [Matrix.add_mulVec]; exact add_mem (hA z hz) (hC z hz)`. Establish `keepSub : ∀ {A C : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)}, (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) → (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, C *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) → ∀ z ∈ GlobalTheory.InertSph.latAt G.W …` using `fun hA hC z hz => by rw [Matrix.sub_mulVec]; exact sub_mem (hA z hz) (hC z hz)`. Establish `keepMul : ∀ {A C : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)}, (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) → (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, C *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) → ∀ z ∈ GlobalTheory.InertSph.latAt G.W …` using `fun hA hC z hz => by rw [← Matrix.mulVec_mulVec]; exact hA _ (hC z hz)`. Establish `keepOne : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (1 : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v` using `fun z hz => by rw [Matrix.one_mulVec]; exact hz`. Use `⟨Y, hYat, hYk, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `hsa : SelfAdj σ (incM F G.W.J) (1 - (mat k + mat k⁻¹ + 1 + 1) ^ (N₀ + 1))` using `selfAdj_sub (selfAdj_one σ _) (selfAdj_pow (sa_gen k.2 (k⁻¹).2 hKK hKiK) _)`. Unfold `SelfAdj at hsa`. Rewrite using `[hYdef, Matrix.transpose_smul, Matrix.smul_mul, hsa, smul_map, hβσ, Matrix.mul_smul, ← AlgHom.mapMatrix_apply, neg_smul, add_neg_cancel]`. Use `GlobalTheory.T.exists_inverse_preserving_adelicLatticeAtPlace F E (a + a') G.W hlat v _ hpv 1 isUnit_one _ ?_ (keepAdd keepOne hYk) s1` and prove the remaining obligations. Rewrite using `[one_smul, add_sub_cancel_left]`.

Conclude with `hYat`. Use `GlobalTheory.T.exists_inverse_preserving_adelicLatticeAtPlace F E (a + a') G.W hlat v _ hpv 1 isUnit_one _ ?_ (keepSub keepOne hYk) s2` and prove the remaining obligations. Introduce `u hu`. Rewrite using `[one_smul, sub_sub_cancel_left, smul_neg, hYat u hu, neg_zero]`. Use `GlobalTheory.T.exists_inverse_preserving_adelicLatticeAtPlace F E (a + a') G.W hlat v _ hpv 2 (isUnit_of_invertible _) _ ?_ (keepAdd (keepAdd keepOne hYk) (keepMul hKk (keepSub keepOne hYk))) s3` and prove the remaining obligations.

Introduce `u hu`. Establish `e : 1 + Y + mat k * (1 - Y) - (2 : AF F) • (1 : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) = Y + (mat k - 1) - mat k * Y`. Rewrite using `[two_smul, Matrix.mul_sub, Matrix.mul_one]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, smul_sub, smul_add, ← Matrix.mul_smul, hYat u hu, hKat u hu, Matrix.mul_zero, add_zero, sub_zero]`.
-/
theorem exists_skew_cayley : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∃ Y : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E),
    At (evFin F v) Y ∧ (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    Yᵀ * incM F G.W.J + incM F G.W.J * Y.map (cA σ) = 0 ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E), (1 + Y) * M = 1 ∧ M * (1 + Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E), (1 - Y) * M = 1 ∧ M * (1 - Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E), (1 + Y + mat k * (1 - Y)) * M = 1 ∧
      M * (1 + Y + mat k * (1 - Y)) = 1 ∧ ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin k hk
  have hlat : G.W.L.IsLattice E := hT.geo.hW.lat
  obtain ⟨h2v, h3, -⟩ := hT.base.inert v w hin
  have hp0 : 0 < Ideal.absNorm v.asIdeal := by omega
  have hpv : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem _
  obtain ⟨β, b, up, um, hβat, hβσ, hsc⟩ := GlobalTheory.T.exists_traceZero_adele_unit_lattice_at_inert_place F E σ B hT.base (a + a') G.W v w hin
  have hKK : mat k * mat k⁻¹ = 1 := by
    show mat (k * k⁻¹) = 1
    rw [mul_inv_cancel]; rfl
  have hKiK : mat k⁻¹ * mat k = 1 := by
    show mat (k⁻¹ * k) = 1
    rw [inv_mul_cancel]; rfl
  have hKk : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, mat k *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v := fun z hz => (hk.2 z hz).1
  have hKik : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, mat k⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v := fun z hz => (hk.2 z hz).2
  have hfk : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (mat k + mat k⁻¹ + 1 + 1) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v := by
    intro z hz
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
    exact add_mem (add_mem (add_mem (hKk z hz) (hKik z hz)) hz) hz
  obtain ⟨N, hN0, hN⟩ := GlobalTheory.T.exists_pow_idempotent_adelicLattice_mod_prime F E (a + a') G.W hlat v _ hp0 hpv _ hfk
  obtain ⟨N₀, rfl⟩ : ∃ N₀, N = N₀ + 1 := ⟨N - 1, by omega⟩
  have hh : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (algebraMap (AF F) (AE F E) ⅟(2 : AF F)) • z ∈ GlobalTheory.InertSph.latAt G.W v :=
    fun z hz => by rw [algebraMap_smul]; exact GlobalTheory.DblVacGauss.invOf_two_smul_mem_latAt G.W v h2v hz
  have hh2 : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v,
      (algebraMap (AF F) (AE F E) ⅟(2 : AF F) + algebraMap (AF F) (AE F E) ⅟(2 : AF F)) • z = z := by
    intro z _
    rw [← map_add, ← two_mul, mul_invOf_self', map_one, one_smul]
  obtain ⟨hYk, s1, s2, s3⟩ := units_mod (GlobalTheory.InertSph.latAt G.W v) (Ideal.absNorm v.asIdeal) (mat k) (mat k⁻¹) β b up um
    (algebraMap (AF F) (AE F E) ⅟(2 : AF F)) N₀ hKK hKiK hKk hKik
    (fun z hz => ⟨(hsc z hz).1, (hsc z hz).2.1, (hsc z hz).2.2.1, (hsc z hz).2.2.2.1, hh z hz⟩)
    (fun z hz => (hsc z hz).2.2.2.2.1) hh2 (fun z hz => (hsc z hz).2.2.2.2.2.1) (fun z hz => (hsc z hz).2.2.2.2.2.2)
    hN _ rfl
  set Y := β • (1 - (mat k + mat k⁻¹ + 1 + 1) ^ (N₀ + 1)) with hYdef
  have hYat : At (evFin F v) Y := by
    intro u hu
    rw [hYdef, ← smul_assoc, hβat u hu, zero_smul]
  have hKat : At (evFin F v) (mat k - 1) := hk.1
  have keepAdd : ∀ {A C : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)},
      (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, C *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (A + C) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v :=
    fun hA hC z hz => by rw [Matrix.add_mulVec]; exact add_mem (hA z hz) (hC z hz)
  have keepSub : ∀ {A C : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)},
      (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, C *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (A - C) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v :=
    fun hA hC z hz => by rw [Matrix.sub_mulVec]; exact sub_mem (hA z hz) (hC z hz)
  have keepMul : ∀ {A C : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)},
      (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      (∀ z ∈ GlobalTheory.InertSph.latAt G.W v, C *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (A * C) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v :=
    fun hA hC z hz => by rw [← Matrix.mulVec_mulVec]; exact hA _ (hC z hz)
  have keepOne : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (1 : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈
      GlobalTheory.InertSph.latAt G.W v := fun z hz => by rw [Matrix.one_mulVec]; exact hz
  refine ⟨Y, hYat, hYk, ?_, ?_, ?_, ?_⟩
  ·
    have hsa : SelfAdj σ (incM F G.W.J) (1 - (mat k + mat k⁻¹ + 1 + 1) ^ (N₀ + 1)) :=
      selfAdj_sub (selfAdj_one σ _) (selfAdj_pow (sa_gen k.2 (k⁻¹).2 hKK hKiK) _)
    unfold SelfAdj at hsa
    rw [hYdef, Matrix.transpose_smul, Matrix.smul_mul, hsa, smul_map, hβσ, Matrix.mul_smul, ← AlgHom.mapMatrix_apply,
      neg_smul, add_neg_cancel]
  · refine GlobalTheory.T.exists_inverse_preserving_adelicLatticeAtPlace F E (a + a') G.W hlat v _ hpv 1 isUnit_one _ ?_ (keepAdd keepOne hYk) s1
    rw [one_smul, add_sub_cancel_left]; exact hYat
  · refine GlobalTheory.T.exists_inverse_preserving_adelicLatticeAtPlace F E (a + a') G.W hlat v _ hpv 1 isUnit_one _ ?_ (keepSub keepOne hYk) s2
    intro u hu
    rw [one_smul, sub_sub_cancel_left, smul_neg, hYat u hu, neg_zero]
  · refine GlobalTheory.T.exists_inverse_preserving_adelicLatticeAtPlace F E (a + a') G.W hlat v _ hpv 2 (isUnit_of_invertible _) _ ?_
      (keepAdd (keepAdd keepOne hYk) (keepMul hKk (keepSub keepOne hYk))) s3
    intro u hu
    have e : 1 + Y + mat k * (1 - Y) - (2 : AF F) • (1 : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) =
        Y + (mat k - 1) - mat k * Y := by
      rw [two_smul, Matrix.mul_sub, Matrix.mul_one]; abel
    rw [e, smul_sub, smul_add, ← Matrix.mul_smul, hYat u hu, hKat u hu, Matrix.mul_zero, add_zero, sub_zero]

end GlobalTheory.TwoFacCore
