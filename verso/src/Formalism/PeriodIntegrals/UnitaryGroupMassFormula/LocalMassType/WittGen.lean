import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.WProof
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.TransitiveOverLocalRings
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.SaturatedSplitLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.IdxStep

noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def cA {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (D : SD σ v) {n m : ℕ}
    (Z : Fin m → Fin n → Fv F v ⊗[F] E) (hZ : ∀ a, IntV v (Z a)) :
    Matrix (Fin n) (Fin m) (v.adicCompletionIntegers F) :=
  Matrix.of fun i a => ⟨D.π₁ (Z a i), ((D.hO _).1 (hZ a i)).1⟩

def cB {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (D : SD σ v) {n m : ℕ}
    (Z : Fin m → Fin n → Fv F v ⊗[F] E) (hZ : ∀ a, IntV v (Z a)) :
    Matrix (Fin n) (Fin m) (v.adicCompletionIntegers F) :=
  Matrix.of fun i a => ⟨D.π₂ (Z a i), ((D.hO _).1 (hZ a i)).2⟩

/- English proof (translation)
Use `set Qm : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQm`. Use `set Qi : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := ((Q⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQi`. Establish `hQQi : Qm * Qi = 1` using `Q.mul_inv`. Establish `hQiQ : Qi * Qm = 1` using `Q.inv_mul`. Establish `memΛ : ∀ y, y ∈ latLoc (E` using `E) v Λ ↔ IntV v (Qi *ᵥ y) := by`.

Introduce `y`. Rewrite using `[hQΛ]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Rewrite using `[mulVec_mulVec, hQiQ, one_mulVec]` and apply the resulting hypothesis.

Introduce `hy`. Conclude with `⟨Qi *ᵥ y, hy, by rw [mulVec_mulVec, hQQi, one_mulVec]⟩`. Use `set A0 := cA D Z0 hZ0 with hA0def`. Use `set B0 := cB D Z0 hZ0 with hB0def`. Use `set A1 := cA D Z hZ with hA1def`.

Use `set B1 := cB D Z hZ with hB1def`. Establish `hgram : A0ᵀ * B0 = A1ᵀ * B1`. Use `Matrix.ext fun a b => Subtype.ext ?_` and prove the remaining obligations. Use `congrArg D.π₂ (hstd a b)` as an intermediate fact. Rewrite `this` using `[D.snd_proj_standard_hermitian_form, D.snd_proj_standard_hermitian_form]`.

Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply]`. Use `push_cast`. Simplify using `only [dotProduct] at this`. Conclude with `this.symm`. Take `⟨k1, hk1u, hk1A, hk1B⟩` from `hC (v.adicCompletionIntegers F) n m A0 A1 B0 B1 hA0 hA1 hB0 hB1 hgram`.

Establish `hdet : IsUnit k1.det` using `(Matrix.isUnit_iff_isUnit_det k1).1 hk1u`. Establish `hki : k1 * k1⁻¹ = 1` using `Matrix.mul_nonsing_inv k1 hdet`. Establish `hik : k1⁻¹ * k1 = 1` using `Matrix.nonsing_inv_mul k1 hdet`. Use `set f := (v.adicCompletionIntegers F).subtype with hf`. Establish `mo : ∀ {M N : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F)}, M * N = 1 → M.map f * N.map f = 1`.

Introduce `M N hMN`. Rewrite using `[← Matrix.map_mul, hMN, Matrix.map_one f (map_zero f) (map_one f)]`. Establish `e1 : (k1⁻¹)ᵀᵀ * k1 = 1` using `by rw [transpose_transpose, hik]`. Establish `e2 : k1ᵀ * (k1⁻¹)ᵀ = 1` using `by rw [← transpose_mul, hik, transpose_one]`. Establish `e3 : (k1⁻¹)ᵀ * k1ᵀ = 1` using `by rw [← transpose_mul, hki, transpose_one]`.

Establish `tm : ∀ M : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F), (M.map f)ᵀ = Mᵀ.map f` using `fun M => (Matrix.transpose_map).symm`. Use `set kstd := D.kS (k1.map f) ((k1⁻¹)ᵀ.map f) with hkstd`. Use `set kstd' := D.kS (k1⁻¹.map f) (k1ᵀ.map f) with hkstd'`. Establish `hkk : kstd * kstd' = 1`. Rewrite using `[hkstd, hkstd', SD.kS_mul, mo hki, mo e3, SD.kS_one]`.

Establish `hk'k : kstd' * kstd = 1` using `mul_eq_one_comm.mp hkk`. Establish `hkU : ∀ x y, stdH σ (kstd *ᵥ x) (kstd *ᵥ y) = stdH σ x y`. Introduce `x y`. Use `D.stdH_kS _ _ ?_ ?_ x y` and prove the remaining obligations. Rewrite using `[tm, mo e1]`.

Rewrite using `[tm, mo e2]`. Establish `hkI : ∀ x, IntV v (kstd *ᵥ x) ↔ IntV v x`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Use `D.intV_kS (k1⁻¹) k1ᵀ hx` as an intermediate fact. Rewrite `this` using `[← hkstd', mulVec_mulVec, hk'k, one_mulVec]`. Then use the resulting hypothesis. Introduce `hx`. Conclude with `D.intV_kS k1 (k1⁻¹)ᵀ hx`. Establish `hkZ : ∀ a, kstd *ᵥ Z0 a = Z a`.

Introduce `a`. Apply `D.extV` to reduce the goal to its premises. Introduce `i`. Rewrite using `[hkstd, SD.fst_proj_split_matrix_mulVec]`. Use `congrArg (fun M => f (M i a)) hk1A` as an intermediate fact.

Simplify using `only [Matrix.mul_apply, map_sum, map_mul] at this`. Simplify using `only [mulVec, dotProduct, Matrix.map_apply]`. Conclude with `this`. Introduce `i`. Establish `hB : (k1⁻¹)ᵀ * B0 = B1`.

Rewrite using `[← hk1B, ← Matrix.mul_assoc, e3, Matrix.one_mul]`. Rewrite using `[hkstd, SD.snd_proj_split_matrix_mulVec]`. Use `congrArg (fun M => f (M i a)) hB` as an intermediate fact. Simplify using `only [Matrix.mul_apply, map_sum, map_mul] at this`. Simplify using `only [mulVec, dotProduct, Matrix.map_apply]`.

Conclude with `this`. Use `set kM := Qm * kstd * Qi with hkM`. Use `set kMi := Qm * kstd' * Qi with hkMi`. Establish `hkMM : kM * kMi = 1`. Rewrite using `[hkM, hkMi]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hQiQ, Matrix.mul_one, hkk, Matrix.mul_one, hQQi]`. Establish `hkMM' : kMi * kM = 1` using `mul_eq_one_comm.mp hkMM`. Set `kG : GL (Fin n) (Fv F v ⊗[F] E)` to `⟨kM, kMi, hkMM, hkMM'⟩`.

Establish `hkx : ∀ x, kM *ᵥ x = Qm *ᵥ (kstd *ᵥ (Qi *ᵥ x))`. Introduce `x`. Rewrite using `[hkM, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]`. Establish `hmem : kG ∈ HR (Fv F v) σ J` using `by show Formalism.UG.cT (sigR (Fv F v) σ) kM * JR (Fv F v) J * kM = JR (Fv F v) J`. Apply `hform_ext (sigR (Fv F v) σ)` to reduce the goal to its premises.

Introduce `x y`. Rewrite using `[← hform_mulVec]`. Use `show hR (Fv F v) σ J (kM *ᵥ x) (kM *ᵥ y) = hR (Fv F v) σ J x y`. Rewrite using `[hkx, hkx, hQh, ← stdH, hkU, stdH, ← hQh, mulVec_mulVec, mulVec_mulVec, hQQi, one_mulVec, one_mulVec]`. Set `kH : HA (Fv F v) σ J` to `(⟨kG, hmem⟩ : HR (Fv F v) σ J)`.

Use `⟨kH, ?_, ?_⟩` and prove the remaining obligations. Introduce `y show y ∈ latLoc (E := E) v Λ ↔ kM *ᵥ y ∈ latLoc (E := E) v Λ`. Rewrite using `[memΛ, memΛ, hkx, mulVec_mulVec, hQiQ, one_mulVec, hkI]`. Introduce `a show kM *ᵥ (Qm *ᵥ Z0 a) = Qm *ᵥ Z a`. Rewrite using `[hkx, show Qi *ᵥ (Qm *ᵥ Z0 a) = Z0 a by rw [mulVec_mulVec, hQiQ, one_mulVec], hkZ a]`.
-/
theorem witt_gen {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}
    {Λ : Set (Fin n → E)} (D : SD σ v) (Q : GL (Fin n) (Fv F v ⊗[F] E))
    (hQΛ : ∀ y, y ∈ latLoc (E := E) v Λ ↔
      ∃ x : Fin n → Fv F v ⊗[F] E, (∀ i, x i ∈ OEv (E := E) v) ∧
        y = (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x)
    (hQh : ∀ x y : Fin n → Fv F v ⊗[F] E,
      hR (Fv F v) σ J ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x)
        ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ y) = ∑ i, sigR (Fv F v) σ (x i) * y i)
    (hC : WCore) {m : ℕ} (Z0 Z : Fin m → Fin n → Fv F v ⊗[F] E)
    (hZ0 : ∀ a, IntV v (Z0 a)) (hZ : ∀ a, IntV v (Z a))
    (hA0 : ∃ L : Matrix (Fin m) (Fin n) (v.adicCompletionIntegers F), L * cA D Z0 hZ0 = 1)
    (hB0 : ∃ L : Matrix (Fin m) (Fin n) (v.adicCompletionIntegers F), L * cB D Z0 hZ0 = 1)
    (hA1 : ∃ L : Matrix (Fin m) (Fin n) (v.adicCompletionIntegers F), L * cA D Z hZ = 1)
    (hB1 : ∃ L : Matrix (Fin m) (Fin n) (v.adicCompletionIntegers F), L * cB D Z hZ = 1)
    (hstd : ∀ a b, stdH σ (Z a) (Z b) = stdH σ (Z0 a) (Z0 b)) :
    ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, ∀ a,
      (HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ
          ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ Z0 a) =
        (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ Z a := by
  classical
  set Qm : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQm
  set Qi : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
    ((Q⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQi
  have hQQi : Qm * Qi = 1 := Q.mul_inv
  have hQiQ : Qi * Qm = 1 := Q.inv_mul
  have memΛ : ∀ y, y ∈ latLoc (E := E) v Λ ↔ IntV v (Qi *ᵥ y) := by
    intro y
    rw [hQΛ]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [mulVec_mulVec, hQiQ, one_mulVec]
    · intro hy
      exact ⟨Qi *ᵥ y, hy, by rw [mulVec_mulVec, hQQi, one_mulVec]⟩
  set A0 := cA D Z0 hZ0 with hA0def
  set B0 := cB D Z0 hZ0 with hB0def
  set A1 := cA D Z hZ with hA1def
  set B1 := cB D Z hZ with hB1def
  have hgram : A0ᵀ * B0 = A1ᵀ * B1 := by
    refine Matrix.ext fun a b => Subtype.ext ?_
    have := congrArg D.π₂ (hstd a b)
    rw [D.snd_proj_standard_hermitian_form, D.snd_proj_standard_hermitian_form] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    push_cast
    simp only [dotProduct] at this
    exact this.symm
  obtain ⟨k1, hk1u, hk1A, hk1B⟩ := hC (v.adicCompletionIntegers F) n m A0 A1 B0 B1 hA0 hA1 hB0 hB1 hgram
  have hdet : IsUnit k1.det := (Matrix.isUnit_iff_isUnit_det k1).1 hk1u
  have hki : k1 * k1⁻¹ = 1 := Matrix.mul_nonsing_inv k1 hdet
  have hik : k1⁻¹ * k1 = 1 := Matrix.nonsing_inv_mul k1 hdet
  set f := (v.adicCompletionIntegers F).subtype with hf
  have mo : ∀ {M N : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F)}, M * N = 1 →
      M.map f * N.map f = 1 := by
    intro M N hMN
    rw [← Matrix.map_mul, hMN, Matrix.map_one f (map_zero f) (map_one f)]
  have e1 : (k1⁻¹)ᵀᵀ * k1 = 1 := by rw [transpose_transpose, hik]
  have e2 : k1ᵀ * (k1⁻¹)ᵀ = 1 := by rw [← transpose_mul, hik, transpose_one]
  have e3 : (k1⁻¹)ᵀ * k1ᵀ = 1 := by rw [← transpose_mul, hki, transpose_one]
  have tm : ∀ M : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F), (M.map f)ᵀ = Mᵀ.map f :=
    fun M => (Matrix.transpose_map).symm
  set kstd := D.kS (k1.map f) ((k1⁻¹)ᵀ.map f) with hkstd
  set kstd' := D.kS (k1⁻¹.map f) (k1ᵀ.map f) with hkstd'
  have hkk : kstd * kstd' = 1 := by
    rw [hkstd, hkstd', SD.kS_mul, mo hki, mo e3, SD.kS_one]
  have hk'k : kstd' * kstd = 1 := mul_eq_one_comm.mp hkk

  have hkU : ∀ x y, stdH σ (kstd *ᵥ x) (kstd *ᵥ y) = stdH σ x y := by
    intro x y
    refine D.stdH_kS _ _ ?_ ?_ x y
    · rw [tm, mo e1]
    · rw [tm, mo e2]

  have hkI : ∀ x, IntV v (kstd *ᵥ x) ↔ IntV v x := by
    intro x
    constructor
    · intro hx
      have := D.intV_kS (k1⁻¹) k1ᵀ hx
      rwa [← hkstd', mulVec_mulVec, hk'k, one_mulVec] at this
    · intro hx
      exact D.intV_kS k1 (k1⁻¹)ᵀ hx

  have hkZ : ∀ a, kstd *ᵥ Z0 a = Z a := by
    intro a
    apply D.extV
    · intro i
      rw [hkstd, SD.fst_proj_split_matrix_mulVec]
      have := congrArg (fun M => f (M i a)) hk1A
      simp only [Matrix.mul_apply, map_sum, map_mul] at this
      simp only [mulVec, dotProduct, Matrix.map_apply]
      exact this
    · intro i
      have hB : (k1⁻¹)ᵀ * B0 = B1 := by
        rw [← hk1B, ← Matrix.mul_assoc, e3, Matrix.one_mul]
      rw [hkstd, SD.snd_proj_split_matrix_mulVec]
      have := congrArg (fun M => f (M i a)) hB
      simp only [Matrix.mul_apply, map_sum, map_mul] at this
      simp only [mulVec, dotProduct, Matrix.map_apply]
      exact this

  set kM := Qm * kstd * Qi with hkM
  set kMi := Qm * kstd' * Qi with hkMi
  have hkMM : kM * kMi = 1 := by
    rw [hkM, hkMi]
    calc Qm * kstd * Qi * (Qm * kstd' * Qi) = Qm * (kstd * (Qi * Qm) * kstd') * Qi := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQiQ, Matrix.mul_one, hkk, Matrix.mul_one, hQQi]
  have hkMM' : kMi * kM = 1 := mul_eq_one_comm.mp hkMM
  let kG : GL (Fin n) (Fv F v ⊗[F] E) := ⟨kM, kMi, hkMM, hkMM'⟩
  have hkx : ∀ x, kM *ᵥ x = Qm *ᵥ (kstd *ᵥ (Qi *ᵥ x)) := by
    intro x; rw [hkM, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have hmem : kG ∈ HR (Fv F v) σ J := by
    show Formalism.UG.cT (sigR (Fv F v) σ) kM * JR (Fv F v) J * kM = JR (Fv F v) J
    apply hform_ext (sigR (Fv F v) σ)
    intro x y
    rw [← hform_mulVec]
    show hR (Fv F v) σ J (kM *ᵥ x) (kM *ᵥ y) = hR (Fv F v) σ J x y
    rw [hkx, hkx, hQh, ← stdH, hkU, stdH, ← hQh, mulVec_mulVec, mulVec_mulVec, hQQi, one_mulVec,
      one_mulVec]
  let kH : HA (Fv F v) σ J := (⟨kG, hmem⟩ : HR (Fv F v) σ J)
  refine ⟨kH, ?_, ?_⟩
  · intro y
    show y ∈ latLoc (E := E) v Λ ↔ kM *ᵥ y ∈ latLoc (E := E) v Λ
    rw [memΛ, memΛ, hkx, mulVec_mulVec, hQiQ, one_mulVec, hkI]
  · intro a
    show kM *ᵥ (Qm *ᵥ Z0 a) = Qm *ᵥ Z a
    rw [hkx, show Qi *ᵥ (Qm *ᵥ Z0 a) = Z0 a by rw [mulVec_mulVec, hQiQ, one_mulVec], hkZ a]

end Gen

end PI.LocMassTypW
