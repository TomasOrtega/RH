import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.WCoreG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.MemSecondProjectionIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.SaturatedSplitLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.IdxStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.IsClosedCongruenceSubgroup

noncomputable section

namespace PI.LocMassTypL

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix
  PI.LocMassTypW
open scoped TensorProduct

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Take `⟨w, hw⟩` from `hu.exists_left_inv`. Establish `hlt` using `PI.LocMassTypM.v_natCast_lt_one v hgv`. Establish `hw1 : Valued.v (w : Fv F v) ≤ 1` using `w.2`.

Establish `e : (w : Fv F v) * (g : Fv F v) = 1`. Use `congrArg (fun x : v.adicCompletionIntegers F => (x : Fv F v)) hw` as an intermediate fact. Simplify using `using this`. Establish `: Valued.v ((w : Fv F v) * (g : Fv F v)) < 1` using `lt_of_le_of_lt (by rw [map_mul]; exact mul_le_of_le_one_left' hw1) hlt`. Rewrite `this` using `[e, map_one]`.

Conclude with `lt_irrefl _ this`.
-/
theorem natCast_mem_max (v : HeightOneSpectrum (𝓞 F)) {g : ℕ} (hgv : (g : 𝓞 F) ∈ v.asIdeal) :
    (g : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨w, hw⟩ := hu.exists_left_inv
  have hlt := PI.LocMassTypM.v_natCast_lt_one v hgv
  have hw1 : Valued.v (w : Fv F v) ≤ 1 := w.2
  have e : (w : Fv F v) * (g : Fv F v) = 1 := by
    have := congrArg (fun x : v.adicCompletionIntegers F => (x : Fv F v)) hw
    simpa using this
  have : Valued.v ((w : Fv F v) * (g : Fv F v)) < 1 :=
    lt_of_le_of_lt (by rw [map_mul]; exact mul_le_of_le_one_left' hw1) hlt
  rw [e, map_one] at this
  exact lt_irrefl _ this

/- English proof (translation)
Establish `hkK` using `hk.1`. Use `set Qm : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQm`. Use `set Qi : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := ((Q⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQi`. Establish `hQQi : Qm * Qi = 1` using `Q.mul_inv`. Establish `hQiQ : Qi * Qm = 1` using `Q.inv_mul`.

Establish `memΛ : ∀ y, y ∈ latLoc (E` using `E) v Λ ↔ IntV v (Qi *ᵥ y) := by`. Introduce `y`. Rewrite using `[hQΛ]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`.

Rewrite using `[mulVec_mulVec, hQiQ, one_mulVec]` and apply the resulting hypothesis. Introduce `hy`. Conclude with `⟨Qi *ᵥ y, hy, by rw [mulVec_mulVec, hQQi, one_mulVec]⟩`. Use `set X0r := ratTup (F := F) (Fv F v) (F0 P) with hX0r`. Use `set Y0 := locF v X0r with hY0`.

Establish `hYdef : locF v (k • X0r) = k • Y0` using `locF_smul σ J v k X0r`. Establish `hPrk : IsPrim v Λ (k • Y0)`. Use `⟨fun a => kv_lat hkK (hPr.1 a), fun c hc => hPr.2 c ?_⟩` and prove the remaining obligations. Establish `e : ∑ a, c a • (k • Y0) a = lin (Fv F v) σ J k (∑ a, c a • Y0 a)`. Rewrite using `[map_sum]`.

Simplify using `only [map_smul, smul_tup]`. Rewrite `hc` using `[e]`. Use `kv_lat (kv_inv hkK) hc` as an intermediate fact. Rewrite `this` using `[lin_inv_lin]`. Then use the resulting hypothesis. Establish `hunit : ∀ x y, hR (Fv F v) σ J ((HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) _) *ᵥ x) ((HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) _) *ᵥ y) = hR (Fv F v) σ J x y`.

Introduce `x y`. Establish `hmem` using `(show HR (Fv F v) σ J from k).2`. Use `show Formalism.UG.hform _ _ _ _ = Formalism.UG.hform _ _ _ _`. Rewrite using `[hform_mulVec]`. Use `congr 1`.

Establish `primT : ∀ W : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, IsPrim v Λ W → ∀ c : Fin (r + 1) → Fv F v ⊗[F] E, IntV v (∑ a, c a • (Qi *ᵥ W a)) → ∀ a, c a ∈ OEv (E` using `E) v := by`. Introduce `W hW c hc`. Apply `hW.2 c` to reduce the goal to its premises. Rewrite using `[memΛ]`. Establish `: Qi *ᵥ (∑ a, c a • W a) = ∑ a, c a • (Qi *ᵥ W a)` using `by show Matrix.mulVecLin Qi (∑ a, c a • W a) = _`.

Rewrite using `[map_sum]`. Simplify using `only [map_smul, Matrix.mulVecLin_apply]`. Rewrite using `[this]` and apply the resulting hypothesis. Use `set Z0 : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun a => Qi *ᵥ Y0 a with hZ0def`. Use `set Z : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun a => Qi *ᵥ (k • Y0) a with hZdef`.

Establish `hZ0 : ∀ a, IntV v (Z0 a)` using `fun a => (memΛ _).1 (hPr.1 a)`. Establish `hZ : ∀ a, IntV v (Z a)` using `fun a => (memΛ _).1 (hPrk.1 a)`. Establish `pZ0` using `primT Y0 hPr`. Establish `pZ` using `primT (k • Y0) hPrk`. Establish `hcong : ∀ a, ∃ y ∈ latLoc (E` using `E) v Λ, (k • Y0) a = Y0 a + sc (E := E) v (g : Fv F v) • y := by`.

Introduce `a`. Take `⟨y, hy, hye⟩` from `hk.2 a`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[← hYdef, ← hye]`. Normalize the expressions using the abelian group laws.

Use `choose yv hyv hyve using hcong`. Use `set Wv : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun a => Qi *ᵥ yv a with hWv`. Establish `hW : ∀ a, IntV v (Wv a)` using `fun a => (memΛ _).1 (hyv a)`. Establish `hZW : ∀ a, Z a = Z0 a + sc (E` using `E) v (g : Fv F v) • Wv a := by`. Introduce `a`.

Simplify using `only [hZdef, hZ0def, hWv]`. Rewrite using `[hyve a, mulVec_add, mulVec_smul]`. Set `A0 : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F)` to `Matrix.of fun i a => ⟨D.π₁ (Z0 a i), ((D.hO _).1 (hZ0 a i)).1⟩`. Set `B0 : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F)` to `Matrix.of fun i a => ⟨D.π₂ (Z0 a i), ((D.hO _).1 (hZ0 a i)).2⟩`. Set `A1 : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F)` to `Matrix.of fun i a => ⟨D.π₁ (Z a i), ((D.hO _).1 (hZ a i)).1⟩`.

Set `B1 : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F)` to `Matrix.of fun i a => ⟨D.π₂ (Z a i), ((D.hO _).1 (hZ a i)).2⟩`. Set `A' : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F)` to `Matrix.of fun i a => ⟨D.π₁ (Wv a i), ((D.hO _).1 (hW a i)).1⟩`. Set `B' : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F)` to `Matrix.of fun i a => ⟨D.π₂ (Wv a i), ((D.hO _).1 (hW a i)).2⟩`. Take `⟨L0, hL0⟩` from `hSat v n (r + 1) A0 (fun t ht => D.sat₁ Z0 pZ0 t ht)`. Take `⟨M1, hM1⟩` from `hSat v n (r + 1) B1 (fun t ht => D.sat₂ Z pZ t ht)`.

Establish `hstd : ∀ a b, stdH σ (Z a) (Z b) = stdH σ (Z0 a) (Z0 b)`. Introduce `a b`. Establish `e1 : stdH σ (Z a) (Z b) = hR (Fv F v) σ J ((k • Y0) a) ((k • Y0) b)`. Rewrite using `[stdH, ← hQh, mulVec_mulVec, mulVec_mulVec, hQQi, one_mulVec, one_mulVec]`. Establish `e2 : stdH σ (Z0 a) (Z0 b) = hR (Fv F v) σ J (Y0 a) (Y0 b)`.

Rewrite using `[stdH, ← hQh, mulVec_mulVec, mulVec_mulVec, hQQi, one_mulVec, one_mulVec]`. Rewrite using `[e1, e2]`. Conclude with `hunit (Y0 a) (Y0 b)`. Establish `hgram : A0ᵀ * B0 = A1ᵀ * B1`. Use `Matrix.ext fun a b => Subtype.ext ?_` and prove the remaining obligations.

Use `congrArg D.π₂ (hstd a b)` as an intermediate fact. Rewrite `this` using `[D.snd_proj_standard_hermitian_form, D.snd_proj_standard_hermitian_form]`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply]`. Use `push_cast`. Simplify using `only [dotProduct] at this`.

Conclude with `this.symm`. Establish `hgc : ((g : v.adicCompletionIntegers F) : Fv F v) = (g : Fv F v)` using `by push_cast; rfl`. Establish `hA1 : A1 = A0 + (g : v.adicCompletionIntegers F) • A'`. Use `Matrix.ext fun i a => Subtype.ext ?_` and prove the remaining obligations. Simplify using `only [A1, A0, A', Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`.

Use `push_cast`. Rewrite using `[hZW a, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, (D.hsc _).1]`. Establish `hB1 : B1 = B0 + (g : v.adicCompletionIntegers F) • B'`. Use `Matrix.ext fun i a => Subtype.ext ?_` and prove the remaining obligations. Simplify using `only [B1, B0, B', Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`.

Use `push_cast`. Rewrite using `[hZW a, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, (D.hsc _).2]`. Take `⟨k1, K', hk1u, hk1A, hk1B, hk1e⟩` from `wCoreG (v.adicCompletionIntegers F) (g : v.adicCompletionIntegers F) (natCast_mem_max v hgv) A0 A1 B0 B1 A' B' L0 M1 hL0 hM1 hgram hA1 hB1`. Establish `hdet : IsUnit k1.det` using `(Matrix.isUnit_iff_isUnit_det k1).1 hk1u`. Establish `hki : k1 * k1⁻¹ = 1` using `Matrix.mul_nonsing_inv k1 hdet`.

Establish `hik : k1⁻¹ * k1 = 1` using `Matrix.nonsing_inv_mul k1 hdet`. Use `set f := (v.adicCompletionIntegers F).subtype with hf`. Establish `mo : ∀ {M N : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F)}, M * N = 1 → M.map f * N.map f = 1`. Introduce `M N hMN`. Rewrite using `[← Matrix.map_mul, hMN, Matrix.map_one f (map_zero f) (map_one f)]`.

Establish `e1 : (k1⁻¹)ᵀᵀ * k1 = 1` using `by rw [transpose_transpose, hik]`. Establish `e2 : k1ᵀ * (k1⁻¹)ᵀ = 1` using `by rw [← transpose_mul, hik, transpose_one]`. Establish `e3 : (k1⁻¹)ᵀ * k1ᵀ = 1` using `by rw [← transpose_mul, hki, transpose_one]`. Establish `tm : ∀ M : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F), (M.map f)ᵀ = Mᵀ.map f` using `fun M => (Matrix.transpose_map).symm`. Use `set kstd := D.kS (k1.map f) ((k1⁻¹)ᵀ.map f) with hkstd`.

Use `set kstd' := D.kS (k1⁻¹.map f) (k1ᵀ.map f) with hkstd'`. Establish `hkk : kstd * kstd' = 1`. Rewrite using `[hkstd, hkstd', SD.kS_mul, mo hki, mo e3, SD.kS_one]`. Establish `hk'k : kstd' * kstd = 1` using `mul_eq_one_comm.mp hkk`. Establish `hkU : ∀ x y, stdH σ (kstd *ᵥ x) (kstd *ᵥ y) = stdH σ x y`.

Introduce `x y`. Use `D.stdH_kS _ _ ?_ ?_ x y` and prove the remaining obligations. Rewrite using `[tm, mo e1]`. Rewrite using `[tm, mo e2]`. Establish `hkI : ∀ x, IntV v (kstd *ᵥ x) ↔ IntV v x`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `D.intV_kS (k1⁻¹) k1ᵀ hx` as an intermediate fact. Rewrite `this` using `[← hkstd', mulVec_mulVec, hk'k, one_mulVec]`. Then use the resulting hypothesis.

Introduce `hx`. Conclude with `D.intV_kS k1 (k1⁻¹)ᵀ hx`. Establish `hkZ : ∀ a, kstd *ᵥ Z0 a = Z a`. Introduce `a`. Apply `D.extV` to reduce the goal to its premises.

Introduce `i`. Rewrite using `[hkstd, SD.fst_proj_split_matrix_mulVec]`. Use `congrArg (fun M => f (M i a)) hk1A` as an intermediate fact. Simplify using `only [Matrix.mul_apply, map_sum, map_mul] at this`. Simplify using `only [mulVec, dotProduct, Matrix.map_apply]`.

Conclude with `this`. Introduce `i`. Establish `hB : (k1⁻¹)ᵀ * B0 = B1`. Rewrite using `[← hk1B, ← Matrix.mul_assoc, e3, Matrix.one_mul]`. Rewrite using `[hkstd, SD.snd_proj_split_matrix_mulVec]`.

Use `congrArg (fun M => f (M i a)) hB` as an intermediate fact. Simplify using `only [Matrix.mul_apply, map_sum, map_mul] at this`. Simplify using `only [mulVec, dotProduct, Matrix.map_apply]`. Conclude with `this`. Use `set K'' : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F) := -(k1⁻¹ * K')ᵀ with hK''`.

Establish `hk1i : (k1⁻¹)ᵀ = 1 + (g : v.adicCompletionIntegers F) • K''`. Establish `h0 : k1⁻¹ = 1 - (g : v.adicCompletionIntegers F) • (k1⁻¹ * K')`. Establish `: k1⁻¹ * k1 = k1⁻¹ + (g : v.adicCompletionIntegers F) • (k1⁻¹ * K')`. Rewrite using `[hk1e, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]`. Rewrite `this` using `[hik]`.

Rewrite using `[this]`. Normalize the expressions using the abelian group laws. Rewrite using `[h0, hK'', Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, smul_neg]`. Normalize the expressions using the abelian group laws. Use `set U := D.kS (K'.map f) (K''.map f) with hU`.

Establish `hkmod : ∀ x, kstd *ᵥ x - x = sc (E` using `E) v (g : Fv F v) • (U *ᵥ x) := by`. Introduce `x`. Apply `D.extV` to reduce the goal to its premises. Introduce `i`. Rewrite using `[Pi.sub_apply, map_sub, hkstd, SD.fst_proj_split_matrix_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, (D.hsc _).1, hU, SD.fst_proj_split_matrix_mulVec, hk1e, Matrix.map_add f (map_add f), Matrix.map_one f (map_zero f) (map_one f), add_mulVec, one_mulVec, Pi.add_apply, add_sub_canc …`.

Simplify using `only [mulVec, dotProduct, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, hf, Subring.coe_subtype]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Introduce `i`.

Rewrite using `[Pi.sub_apply, map_sub, hkstd, SD.snd_proj_split_matrix_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, (D.hsc _).2, hU, SD.snd_proj_split_matrix_mulVec, hk1i, Matrix.map_add f (map_add f), Matrix.map_one f (map_zero f) (map_one f), add_mulVec, one_mulVec, Pi.add_apply, add_sub_canc …`. Simplify using `only [mulVec, dotProduct, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, hf, Subring.coe_subtype]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Use `set kM := Qm * kstd * Qi with hkM`. Use `set kMi := Qm * kstd' * Qi with hkMi`. Establish `hkMM : kM * kMi = 1`. Rewrite using `[hkM, hkMi]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hQiQ, Matrix.mul_one, hkk, Matrix.mul_one, hQQi]`. Establish `hkMM' : kMi * kM = 1` using `mul_eq_one_comm.mp hkMM`. Set `kG : GL (Fin n) (Fv F v ⊗[F] E)` to `⟨kM, kMi, hkMM, hkMM'⟩`. Establish `hkx : ∀ x, kM *ᵥ x = Qm *ᵥ (kstd *ᵥ (Qi *ᵥ x))`.

Introduce `x`. Rewrite using `[hkM, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]`. Establish `hmem : kG ∈ HR (Fv F v) σ J` using `by show Formalism.UG.cT (sigR (Fv F v) σ) kM * JR (Fv F v) J * kM = JR (Fv F v) J`. Apply `hform_ext (sigR (Fv F v) σ)` to reduce the goal to its premises. Introduce `x y`.

Rewrite using `[← hform_mulVec]`. Use `show hR (Fv F v) σ J (kM *ᵥ x) (kM *ᵥ y) = hR (Fv F v) σ J x y`. Rewrite using `[hkx, hkx, hQh, ← stdH, hkU, stdH, ← hQh, mulVec_mulVec, mulVec_mulVec, hQQi, one_mulVec, one_mulVec]`. Set `kH : HA (Fv F v) σ J` to `(⟨kG, hmem⟩ : HR (Fv F v) σ J)`. Establish `hkHK : kH ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v`.

Introduce `y`. Use `show y ∈ latLoc (E := E) v Λ ↔ kM *ᵥ y ∈ latLoc (E := E) v Λ`. Rewrite using `[memΛ, memΛ, hkx, mulVec_mulVec, hQiQ, one_mulVec, hkI]`. Establish `hkHX : kH • X0r = k • X0r`. Apply `locF_injective v` to reduce the goal to its premises.

Rewrite using `[locF_smul σ J v kH X0r, hYdef]`. Use function extensionality and compare the values at `a`. Use `show kM *ᵥ Y0 a = (k • Y0) a`. Rewrite using `[hkx]`. Use `hkZ a` as an intermediate fact.

Simplify using `only [hZ0def, hZdef] at this`. Rewrite using `[this, mulVec_mulVec, hQQi, one_mulVec]`. Establish `hkHg : kH ∈ Formalism.L2.SG.TypedSets.Kgv σ J Λ g v`. Use `(kgv_iff kH).2 ⟨hkHK, fun w hw => ?_⟩` and prove the remaining obligations. Use `⟨Qm *ᵥ (U *ᵥ (Qi *ᵥ w)), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[memΛ, mulVec_mulVec, hQiQ, one_mulVec]`. Conclude with `D.intV_kS K' K'' ((memΛ w).1 hw)`. Use `show kM *ᵥ w - w = _`. Establish `e : Qm *ᵥ (kstd *ᵥ (Qi *ᵥ w)) - w = Qm *ᵥ (kstd *ᵥ (Qi *ᵥ w) - Qi *ᵥ w)`. Rewrite using `[mulVec_sub, show Qm *ᵥ (Qi *ᵥ w) = w by rw [mulVec_mulVec, hQQi, one_mulVec]]`.

Rewrite using `[hkx, e, hkmod, mulVec_smul]`. Use `set s := kH⁻¹ * k with hs`. Establish `hsK : s ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v` using `kv_mul (kv_inv hkHK) hkK`. Establish `hsX : s • X0r = X0r`. Rewrite using `[hs, mul_smul, ← hkHX, inv_smul_smul]`.

Establish `hsS : s ∈ (Ssub (Fv F v) σ J P : Set (HA (Fv F v) σ J))`. Introduce `b`. Use `show lin (Fv F v) σ J s (ratV (F := F) (Fv F v) (F0 P b)) - ratV (F := F) (Fv F v) (F0 P b) ∈ _`. Use `congrFun hsX b` as an intermediate fact. Rewrite `this` using `[smul_tup]`.

Rewrite using `[show ratV (F := F) (Fv F v) (F0 P b) = X0r b from rfl, this, sub_self]`. Conclude with `Submodule.zero_mem _`. Conclude with `⟨hkK, s, s⁻¹ * kH * s, hsS, hsK, kgv_conj hsK hkHg, by rw [hs]; group⟩`.
-/
theorem congruence_lift_of_basis {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}
    {r : ℕ} {P : Frame E n r} {Λ : Set (Fin n → E)} (D : SD σ v) (Q : GL (Fin n) (Fv F v ⊗[F] E))
    (hQΛ : ∀ y, y ∈ latLoc (E := E) v Λ ↔
      ∃ x : Fin n → Fv F v ⊗[F] E, (∀ i, x i ∈ OEv (E := E) v) ∧
        y = (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x)
    (hQh : ∀ x y : Fin n → Fv F v ⊗[F] E,
      hR (Fv F v) σ J ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x)
        ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ y) = ∑ i, sigR (Fv F v) σ (x i) * y i)
    (hSat : SatSplit)
    (hPr : IsPrim v Λ (locF v (ratTup (F := F) (Fv F v) (F0 P)))) {g : ℕ}
    (hgv : (g : 𝓞 F) ∈ v.asIdeal) (k : HA (Fv F v) σ J) (hk : k ∈ K1 σ J v Λ g P) :
    k ∈ Formalism.L2.SG.TypedSets.Knatv σ J Λ P g v := by
  classical
  have hkK := hk.1
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
  set X0r := ratTup (F := F) (Fv F v) (F0 P) with hX0r
  set Y0 := locF v X0r with hY0
  have hYdef : locF v (k • X0r) = k • Y0 := locF_smul σ J v k X0r

  have hPrk : IsPrim v Λ (k • Y0) := by
    refine ⟨fun a => kv_lat hkK (hPr.1 a), fun c hc => hPr.2 c ?_⟩
    have e : ∑ a, c a • (k • Y0) a = lin (Fv F v) σ J k (∑ a, c a • Y0 a) := by
      rw [map_sum]; simp only [map_smul, smul_tup]
    rw [e] at hc
    have := kv_lat (kv_inv hkK) hc
    rwa [lin_inv_lin] at this

  have hunit : ∀ x y, hR (Fv F v) σ J ((HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) _) *ᵥ x)
      ((HA.mat (Fv F v) σ J k : Matrix (Fin n) (Fin n) _) *ᵥ y) = hR (Fv F v) σ J x y := by
    intro x y
    have hmem := (show HR (Fv F v) σ J from k).2
    show Formalism.UG.hform _ _ _ _ = Formalism.UG.hform _ _ _ _
    rw [hform_mulVec]
    congr 1
  have primT : ∀ W : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, IsPrim v Λ W →
      ∀ c : Fin (r + 1) → Fv F v ⊗[F] E, IntV v (∑ a, c a • (Qi *ᵥ W a)) → ∀ a, c a ∈ OEv (E := E) v := by
    intro W hW c hc
    apply hW.2 c
    rw [memΛ]
    have : Qi *ᵥ (∑ a, c a • W a) = ∑ a, c a • (Qi *ᵥ W a) := by
      show Matrix.mulVecLin Qi (∑ a, c a • W a) = _
      rw [map_sum]
      simp only [map_smul, Matrix.mulVecLin_apply]
    rwa [this]
  set Z0 : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun a => Qi *ᵥ Y0 a with hZ0def
  set Z : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun a => Qi *ᵥ (k • Y0) a with hZdef
  have hZ0 : ∀ a, IntV v (Z0 a) := fun a => (memΛ _).1 (hPr.1 a)
  have hZ : ∀ a, IntV v (Z a) := fun a => (memΛ _).1 (hPrk.1 a)
  have pZ0 := primT Y0 hPr
  have pZ := primT (k • Y0) hPrk

  have hcong : ∀ a, ∃ y ∈ latLoc (E := E) v Λ, (k • Y0) a = Y0 a + sc (E := E) v (g : Fv F v) • y := by
    intro a
    obtain ⟨y, hy, hye⟩ := hk.2 a
    refine ⟨y, hy, ?_⟩
    rw [← hYdef, ← hye]; abel
  choose yv hyv hyve using hcong
  set Wv : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun a => Qi *ᵥ yv a with hWv
  have hW : ∀ a, IntV v (Wv a) := fun a => (memΛ _).1 (hyv a)
  have hZW : ∀ a, Z a = Z0 a + sc (E := E) v (g : Fv F v) • Wv a := by
    intro a
    simp only [hZdef, hZ0def, hWv]
    rw [hyve a, mulVec_add, mulVec_smul]

  let A0 : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun i a => ⟨D.π₁ (Z0 a i), ((D.hO _).1 (hZ0 a i)).1⟩
  let B0 : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun i a => ⟨D.π₂ (Z0 a i), ((D.hO _).1 (hZ0 a i)).2⟩
  let A1 : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun i a => ⟨D.π₁ (Z a i), ((D.hO _).1 (hZ a i)).1⟩
  let B1 : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun i a => ⟨D.π₂ (Z a i), ((D.hO _).1 (hZ a i)).2⟩
  let A' : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun i a => ⟨D.π₁ (Wv a i), ((D.hO _).1 (hW a i)).1⟩
  let B' : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun i a => ⟨D.π₂ (Wv a i), ((D.hO _).1 (hW a i)).2⟩
  obtain ⟨L0, hL0⟩ := hSat v n (r + 1) A0 (fun t ht => D.sat₁ Z0 pZ0 t ht)
  obtain ⟨M1, hM1⟩ := hSat v n (r + 1) B1 (fun t ht => D.sat₂ Z pZ t ht)
  have hstd : ∀ a b, stdH σ (Z a) (Z b) = stdH σ (Z0 a) (Z0 b) := by
    intro a b
    have e1 : stdH σ (Z a) (Z b) = hR (Fv F v) σ J ((k • Y0) a) ((k • Y0) b) := by
      rw [stdH, ← hQh, mulVec_mulVec, mulVec_mulVec, hQQi, one_mulVec, one_mulVec]
    have e2 : stdH σ (Z0 a) (Z0 b) = hR (Fv F v) σ J (Y0 a) (Y0 b) := by
      rw [stdH, ← hQh, mulVec_mulVec, mulVec_mulVec, hQQi, one_mulVec, one_mulVec]
    rw [e1, e2]
    exact hunit (Y0 a) (Y0 b)
  have hgram : A0ᵀ * B0 = A1ᵀ * B1 := by
    refine Matrix.ext fun a b => Subtype.ext ?_
    have := congrArg D.π₂ (hstd a b)
    rw [D.snd_proj_standard_hermitian_form, D.snd_proj_standard_hermitian_form] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    push_cast
    simp only [dotProduct] at this
    exact this.symm
  have hgc : ((g : v.adicCompletionIntegers F) : Fv F v) = (g : Fv F v) := by push_cast; rfl
  have hA1 : A1 = A0 + (g : v.adicCompletionIntegers F) • A' := by
    refine Matrix.ext fun i a => Subtype.ext ?_
    simp only [A1, A0, A', Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    rw [hZW a, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, (D.hsc _).1]
  have hB1 : B1 = B0 + (g : v.adicCompletionIntegers F) • B' := by
    refine Matrix.ext fun i a => Subtype.ext ?_
    simp only [B1, B0, B', Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    rw [hZW a, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, (D.hsc _).2]
  obtain ⟨k1, K', hk1u, hk1A, hk1B, hk1e⟩ := wCoreG (v.adicCompletionIntegers F)
    (g : v.adicCompletionIntegers F) (natCast_mem_max v hgv) A0 A1 B0 B1 A' B' L0 M1 hL0 hM1
    hgram hA1 hB1
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

  set K'' : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F) := -(k1⁻¹ * K')ᵀ with hK''
  have hk1i : (k1⁻¹)ᵀ = 1 + (g : v.adicCompletionIntegers F) • K'' := by
    have h0 : k1⁻¹ = 1 - (g : v.adicCompletionIntegers F) • (k1⁻¹ * K') := by
      have : k1⁻¹ * k1 = k1⁻¹ + (g : v.adicCompletionIntegers F) • (k1⁻¹ * K') := by
        rw [hk1e, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
      rw [hik] at this
      rw [this]; abel
    rw [h0, hK'', Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, smul_neg]
    abel
  set U := D.kS (K'.map f) (K''.map f) with hU
  have hkmod : ∀ x, kstd *ᵥ x - x = sc (E := E) v (g : Fv F v) • (U *ᵥ x) := by
    intro x
    apply D.extV
    · intro i
      rw [Pi.sub_apply, map_sub, hkstd, SD.fst_proj_split_matrix_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, (D.hsc _).1,
        hU, SD.fst_proj_split_matrix_mulVec, hk1e, Matrix.map_add f (map_add f), Matrix.map_one f (map_zero f) (map_one f), add_mulVec,
        one_mulVec, Pi.add_apply, add_sub_cancel_left]
      simp only [mulVec, dotProduct, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
        Finset.mul_sum, hf, Subring.coe_subtype]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_natCast]; ring
    · intro i
      rw [Pi.sub_apply, map_sub, hkstd, SD.snd_proj_split_matrix_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, (D.hsc _).2,
        hU, SD.snd_proj_split_matrix_mulVec, hk1i, Matrix.map_add f (map_add f), Matrix.map_one f (map_zero f) (map_one f), add_mulVec,
        one_mulVec, Pi.add_apply, add_sub_cancel_left]
      simp only [mulVec, dotProduct, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
        Finset.mul_sum, hf, Subring.coe_subtype]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_natCast]; ring

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
  have hkHK : kH ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v := by
    intro y
    show y ∈ latLoc (E := E) v Λ ↔ kM *ᵥ y ∈ latLoc (E := E) v Λ
    rw [memΛ, memΛ, hkx, mulVec_mulVec, hQiQ, one_mulVec, hkI]
  have hkHX : kH • X0r = k • X0r := by
    apply locF_injective v
    rw [locF_smul σ J v kH X0r, hYdef]
    funext a
    show kM *ᵥ Y0 a = (k • Y0) a
    rw [hkx]
    have := hkZ a
    simp only [hZ0def, hZdef] at this
    rw [this, mulVec_mulVec, hQQi, one_mulVec]
  have hkHg : kH ∈ Formalism.L2.SG.TypedSets.Kgv σ J Λ g v := by
    refine (kgv_iff kH).2 ⟨hkHK, fun w hw => ?_⟩
    refine ⟨Qm *ᵥ (U *ᵥ (Qi *ᵥ w)), ?_, ?_⟩
    · rw [memΛ, mulVec_mulVec, hQiQ, one_mulVec]
      exact D.intV_kS K' K'' ((memΛ w).1 hw)
    · show kM *ᵥ w - w = _
      have e : Qm *ᵥ (kstd *ᵥ (Qi *ᵥ w)) - w = Qm *ᵥ (kstd *ᵥ (Qi *ᵥ w) - Qi *ᵥ w) := by
        rw [mulVec_sub, show Qm *ᵥ (Qi *ᵥ w) = w by rw [mulVec_mulVec, hQQi, one_mulVec]]
      rw [hkx, e, hkmod, mulVec_smul]

  set s := kH⁻¹ * k with hs
  have hsK : s ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v := kv_mul (kv_inv hkHK) hkK
  have hsX : s • X0r = X0r := by
    rw [hs, mul_smul, ← hkHX, inv_smul_smul]
  have hsS : s ∈ (Ssub (Fv F v) σ J P : Set (HA (Fv F v) σ J)) := by
    intro b
    show lin (Fv F v) σ J s (ratV (F := F) (Fv F v) (F0 P b)) - ratV (F := F) (Fv F v) (F0 P b) ∈ _
    have := congrFun hsX b
    rw [smul_tup] at this
    rw [show ratV (F := F) (Fv F v) (F0 P b) = X0r b from rfl, this, sub_self]
    exact Submodule.zero_mem _
  exact ⟨hkK, s, s⁻¹ * kH * s, hsS, hsK, kgv_conj hsK hkHg, by rw [hs]; group⟩

end Core

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J ψ v r g P Λ T μS0 hyp k hk`. Take `⟨hStd, -, hSD, hUn, -, hgv, -, hEta, hPr, hLat, -⟩` from `hyp`. Take `⟨D⟩` from `exists_SD hS σ J ψ v hStd hUn hEta`. Take `⟨Q, hQΛ, hQh⟩` from `latStd_SD D hStd.2.1 hSD hLat`. Conclude with `congruence_lift_of_basis D Q hQΛ hQh saturated_split_lattice hPr hgv k hk`.
-/
theorem congruence_lift_of_split (hS : SplitR) : CongruenceSubgroupLift := by
  intro F E _ _ _ _ _ σ n J ψ v r g P Λ T μS0 hyp k hk
  obtain ⟨hStd, -, hSD, hUn, -, hgv, -, hEta, hPr, hLat, -⟩ := hyp
  obtain ⟨D⟩ := exists_SD hS σ J ψ v hStd hUn hEta
  obtain ⟨Q, hQΛ, hQh⟩ := latStd_SD D hStd.2.1 hSD hLat
  exact congruence_lift_of_basis D Q hQΛ hQh saturated_split_lattice hPr hgv k hk

end PI.LocMassTypL
