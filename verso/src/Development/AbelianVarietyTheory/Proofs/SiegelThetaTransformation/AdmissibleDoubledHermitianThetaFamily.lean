import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledThetaTestFunctionSesquilinearHeisenbergStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledVacuumEqHermitianCharacterStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.DblAdm

variable {E : Type} [Field E] [NumberField E] {n r : ℕ}

/- English proof (translation)
Take `⟨a, b, e⟩ : IsCoprime (s : ℤ) (M : ℤ)` from `Nat.isCoprime_iff_coprime.2 h`. Conclude with `Lev.cop_iff.2 ⟨a, b * M, Ideal.mul_mem_left _ _ hM, by`. Conclude with `congrArg (Int.cast : ℤ → 𝓞 E) e⟩` after adjusting the coercions.
-/
theorem cop_nat {𝔪 : Ideal (𝓞 E)} {s M : ℕ} (h : s.Coprime M) (hM : (M : 𝓞 E) ∈ 𝔪) :
    IsCoprime (Ideal.span {(s : 𝓞 E)}) 𝔪 := by
  obtain ⟨a, b, e⟩ : IsCoprime (s : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.2 h
  exact Lev.cop_iff.2 ⟨a, b * M, Ideal.mul_mem_left _ _ hM, by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) e⟩

/- English proof (translation)
The claim follows from `TensLat.tens_le (H := (tens Λ' K).comap (AddMonoidHom.mk' (fun y => h * y) (Matrix.mul_add h))) (fun v hv u hu => by change h * vecMulVec v u ∈ tens Λ' K rw [Matrix.mul_vecMulVec] exact TensLat.pure_mem (H v hv) hu) hy`.
-/
theorem mul_mem_tens {Λ Λ' : Lt E n} {K : Lt E r} {h : Matrix (Fin n) (Fin n) E}
    (H : ∀ v ∈ Λ, h *ᵥ v ∈ Λ') {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ K) :
    h * y ∈ tens Λ' K :=
  TensLat.tens_le (H := (tens Λ' K).comap (AddMonoidHom.mk' (fun y => h * y) (Matrix.mul_add h)))
    (fun v hv u hu => by
      change h * vecMulVec v u ∈ tens Λ' K
      rw [Matrix.mul_vecMulVec]
      exact TensLat.pure_mem (H v hv) hu) hy

/- English proof (translation)
The claim follows from `TensLat.tens_le (H := (tens Λ K').comap (AddMonoidHom.mk' (fun y : Matrix (Fin n) (Fin r) E => (a • (y * B) : Matrix (Fin n) (Fin r) E)) fun y y' => by rw [Matrix.add_mul, smul_add])) (fun v hv u hu => by change a • (vecMulVec v u * B) ∈ tens Λ K' rw [Matrix.vecMulVec_mul, ← vecM …`.
-/
theorem mem_tens_mul {Λ : Lt E n} {K K' : Lt E r} {B : Matrix (Fin r) (Fin r) E} {a : E}
    (H : ∀ u ∈ K, a • (u ᵥ* B) ∈ K') {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ K) :
    a • (y * B) ∈ tens Λ K' :=
  TensLat.tens_le (H := (tens Λ K').comap (AddMonoidHom.mk'
    (fun y : Matrix (Fin n) (Fin r) E => (a • (y * B) : Matrix (Fin n) (Fin r) E))
    fun y y' => by rw [Matrix.add_mul, smul_add]))
    (fun v hv u hu => by
      change a • (vecMulVec v u * B) ∈ tens Λ K'
      rw [Matrix.vecMulVec_mul, ← vecMulVec_smul]
      exact TensLat.pure_mem hv (H u hu)) hy

/- English proof (translation)
Simplify `H) hy` using `using mem_tens_mul (B := 1) (by simpa`.
-/
theorem smul_mem_tens {Λ : Lt E n} {K K' : Lt E r} {a : E}
    (H : ∀ u ∈ K, a • u ∈ K') {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ K) :
    a • y ∈ tens Λ K' := by
  simpa using mem_tens_mul (B := 1) (by simpa using H) hy

/- English proof (translation)
Take `⟨N, hN, h⟩` from `TensLat.exists_mul_le hfg hsp`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {N}))`. Use `⟨Ideal.absNorm (Ideal.span {N}), Nat.pos_of_ne_zero (by simpa using hN), fun u hu => ?_⟩` and prove the remaining obligations. Establish `: ((Ideal.absNorm (Ideal.span {N}) : ℕ) : E) = (c : E) * N`. Conclude with `congrArg (fun z : 𝓞 E => (z : E)) hc.symm` after adjusting the coercions.

Rewrite using `[this, mul_smul]`. Conclude with `TensLat.int_smul_mem c.isIntegral_coe (h u hu)`.
-/
theorem exists_nat_mul_le {K K' : Lt E r} (hfg : K.FG)
    (hsp : Submodule.span E (K' : Set (Fin r → E)) = ⊤) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ K, (N : E) • u ∈ K' := by
  obtain ⟨N, hN, h⟩ := TensLat.exists_mul_le hfg hsp
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {N}))
  refine ⟨Ideal.absNorm (Ideal.span {N}), Nat.pos_of_ne_zero (by simpa using hN), fun u hu => ?_⟩
  have : ((Ideal.absNorm (Ideal.span {N}) : ℕ) : E) = (c : E) * N := by
    exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hc.symm
  rw [this, mul_smul]
  exact TensLat.int_smul_mem c.isIntegral_coe (h u hu)

/- English proof (translation)
Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `A.nsmul_mem hy s`.
-/
theorem nat_mem {A : AddSubgroup (Matrix (Fin n) (Fin r) E)} (s : ℕ) {y} (hy : y ∈ A) :
    (s : E) • y ∈ A := by
  rw [Nat.cast_smul_eq_nsmul]; exact A.nsmul_mem hy s

/- English proof (translation)
Take `⟨a, b, hab⟩ : IsCoprime (s : ℤ) (R : ℤ)` from `Nat.isCoprime_iff_coprime.2 h`. Establish `e : y = a • ((s : E) • y) + b • ((R : E) • y)`. Rewrite using `[← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, smul_smul, smul_smul, ← add_smul]`. Establish `: (a : E) * s + b * R = 1` using `by exact_mod_cast congrArg (Int.cast : ℤ → E) hab`. Rewrite using `[this, one_smul]`.

Rewrite using `[e]`. Conclude with `A.add_mem (A.zsmul_mem h1 a) (A.zsmul_mem h2 b)`.
-/
theorem mem_of_cop {A : AddSubgroup (Matrix (Fin n) (Fin r) E)} {s R : ℕ} (h : s.Coprime R) {y}
    (h1 : (s : E) • y ∈ A) (h2 : (R : E) • y ∈ A) : y ∈ A := by
  obtain ⟨a, b, hab⟩ : IsCoprime (s : ℤ) (R : ℤ) := Nat.isCoprime_iff_coprime.2 h
  have e : y = a • ((s : E) • y) + b • ((R : E) • y) := by
    rw [← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, smul_smul, smul_smul, ← add_smul]
    have : (a : E) * s + b * R = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → E) hab
    rw [this, one_smul]
  rw [e]
  exact A.add_mem (A.zsmul_mem h1 a) (A.zsmul_mem h2 b)

/- English proof (translation)
Rewrite using `[eq_top_iff, ← (Pi.basisFun E (Fin r)).span_eq]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `Submodule.subset_span ⟨a, by simp⟩`.
-/
theorem span_stdL : Submodule.span E (stdL E r : Set (Fin r → E)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun E (Fin r)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a, by simp⟩

/- English proof (translation)
Take `⟨m, hm⟩` from `IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_trace (L := ℚ) (F := E) he)`. Rewrite using `[two_mul, map_add, map_add, ← hm, ← mul_one (cexp (π * I * ((Algebra.trace ℚ E t : ℚ) : ℂ))), ← Complex.exp_int_mul_two_pi_mul_I m, ← Complex.exp_add]`. Use `congr 1`. Simplify using `only [eq_intCast]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exp_trace_add {t e : E} (he : IsIntegral ℤ e) :
    cexp (π * I * ((Algebra.trace ℚ E (t + 2 * e) : ℚ) : ℂ)) =
      cexp (π * I * ((Algebra.trace ℚ E t : ℚ) : ℂ)) := by
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (Algebra.isIntegral_trace (L := ℚ) (F := E) he)
  rw [two_mul, map_add, map_add, ← hm, ← mul_one (cexp (π * I * ((Algebra.trace ℚ E t : ℚ) : ℂ))),
    ← Complex.exp_int_mul_two_pi_mul_I m, ← Complex.exp_add]
  congr 1
  simp only [eq_intCast]
  push_cast
  ring

variable [IsCMField E]

/- English proof (translation)
Rewrite using `[TensLat.tens_eq_comap]`. Conclude with `(TensLat.mem_tens_stdL Λ yᵀ).symm`.
-/
theorem colsIn_iff (Λ : Lt E n) (y : Matrix (Fin n) (Fin r) E) :
    ColsIn Λ y ↔ y ∈ tens Λ (stdL E r) := by
  rw [TensLat.tens_eq_comap]
  exact (TensLat.mem_tens_stdL Λ yᵀ).symm

/- English proof (translation)
Establish `: (x * ccT y).trace = ∑ a, herm 1 (xᵀ a) (yᵀ a)`. Simplify using `only [Base.herm_one, Matrix.trace, Matrix.diag, Matrix.mul_apply, ccT, Matrix.transpose_apply, Matrix.map_apply]`. Conclude with `Finset.sum_comm`. Rewrite using `[this]`. Conclude with `IsIntegral.sum _ fun a _ => (hΛ.2.1 _).1 ((colsIn_iff Λ x).2 hx a) _ ((colsIn_iff Λ y).2 hy a)`.
-/
theorem isIntegral_pair {M : ℕ} {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M)
    {x y : Matrix (Fin n) (Fin r) E} (hx : x ∈ tens Λ (stdL E r)) (hy : y ∈ tens Λ (stdL E r)) :
    IsIntegral ℤ (x * ccT y).trace := by
  have : (x * ccT y).trace = ∑ a, herm 1 (xᵀ a) (yᵀ a) := by
    simp only [Base.herm_one, Matrix.trace, Matrix.diag, Matrix.mul_apply, ccT,
      Matrix.transpose_apply, Matrix.map_apply]
    exact Finset.sum_comm
  rw [this]
  exact IsIntegral.sum _ fun a _ =>
    (hΛ.2.1 _).1 ((colsIn_iff Λ x).2 hx a) _ ((colsIn_iff Λ y).2 hy a)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[ccT, cc]`.
-/
theorem ccT_add (x y : Matrix (Fin n) (Fin r) E) : ccT (x + y) = ccT x + ccT y := by
  ext i j; simp [ccT, cc]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[ccT, cc]`.
-/
theorem ccT_nat (s : ℕ) (x : Matrix (Fin n) (Fin r) E) : ccT ((s : E) • x) = (s : E) • ccT x := by
  ext i j; simp [ccT, cc]

/- English proof (translation)
Unfold `heisH`. Use `congr 6`. Simplify using `[Matrix.trace, Matrix.mul_apply, ccT, cc, two_mul]`.
-/
theorem heisH_apply (d b x : Matrix (Fin n) (Fin r) E) (φ : Matrix (Fin n) (Fin r) E → ℂ) :
    heisH d b φ x = φ (x - d) *
      cexp (π * I * ((Algebra.trace ℚ E (b * ccT (x + x - d)).trace : ℚ) : ℂ)) := by
  unfold heisH
  congr 6
  simp [Matrix.trace, Matrix.mul_apply, ccT, cc, two_mul]

/- English proof (translation)
Rewrite using `[Base.ccT_mul, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hu, Matrix.one_mul]`.
-/
theorem trace_unitary {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1)
    (x y : Matrix (Fin n) (Fin r) E) : (h * x * ccT (h * y)).trace = (x * ccT y).trace := by
  rw [Base.ccT_mul, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, hu, Matrix.one_mul]

/- English proof (translation)
Introduce `E _ _ _ n r M hM K K₀ hK hKs hK₀ B β t J _ a P F hP hex hF`. Set `f : Matrix (Fin r) (Fin r) E → (Fin r → E) →ₗ[𝓞 E] (Fin r → E)` to `fun C => (Matrix.vecMulLinear C).restrictScalars (𝓞 E)`. Establish `hS : (stdL E r).FG` using `(Base.stdL_mem_Vset r 1).1`. Take `⟨N, hN, H⟩` from `exists_nat_mul_le (K := K ⊔ (K₀ ⊔ (K₀.map (f B) ⊔ (K.map (f β) ⊔ (K.map (f (ccT β)) ⊔ (stdL E r).map (f β)))))) (hK.sup (hK₀.sup ((hK₀.map _).sup ((hK.map _).sup ((hK.map _).sup (hS.map _)))))) span_stdL`. Take `⟨N', hN', H'⟩` from `exists_nat_mul_le hS hKs`.

Establish `l` using `fun (A A' : Lt E r) u => Submodule.mem_sup_left (S := A) (T := A') (x := u)`. Establish `l'` using `fun (A A' : Lt E r) u => Submodule.mem_sup_right (S := A) (T := A') (x := u)`. Establish `H1 : ∀ u ∈ K, (N : E) • u ∈ stdL E r` using `fun u hu => H _ (l _ _ _ hu)`. Establish `H2 : ∀ u ∈ K₀, (N : E) • u ∈ stdL E r` using `fun u hu => H _ (l' _ _ _ (l _ _ _ hu))`. Establish `H3 : ∀ u ∈ K₀, (N : E) • (u ᵥ* B) ∈ stdL E r` using `fun u hu => H _ (l' _ _ _ (l' _ _ _ (l _ _ _ ⟨u, hu, rfl⟩)))`.

Establish `H4 : ∀ u ∈ K, (N : E) • (u ᵥ* β) ∈ stdL E r` using `fun u hu => H _ (l' _ _ _ (l' _ _ _ (l' _ _ _ (l _ _ _ ⟨u, hu, rfl⟩))))`. Establish `H5 : ∀ u ∈ K, (N : E) • (u ᵥ* ccT β) ∈ stdL E r` using `fun u hu => H _ (l' _ _ _ (l' _ _ _ (l' _ _ _ (l' _ _ _ (l _ _ _ ⟨u, hu, rfl⟩)))))`. Establish `H6 : ∀ u ∈ stdL E r, (N : E) • (u ᵥ* β) ∈ stdL E r` using `fun u hu => H _ (l' _ _ _ (l' _ _ _ (l' _ _ _ (l' _ _ _ (l' _ _ _ ⟨u, hu, rfl⟩)))))`. Use `clear H l l'`. Establish `eR : ∀ y : Matrix (Fin n) (Fin r) E, ((2 * N * N' : ℕ) : E) • y = ((2 * N' : ℕ) : E) • (N : E) • y` using `fun y => by`.

Rewrite using `[smul_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `eR' : ∀ y : Matrix (Fin n) (Fin r) E, ((2 * N * N' : ℕ) : E) • y = ((2 * N : ℕ) : E) • (N' : E) • y` using `fun y => by`.

Rewrite using `[smul_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `ni : ∀ k : ℕ, IsIntegral ℤ (k : E)` using `fun k => by`.

Simplify using `using isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ))`. Use `⟨2 * N * N', ⟨hM, by positivity⟩, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h hh Λ hΛ Λ' hΛ' hm x`. Take `⟨c, hc⟩` from `hex Λ hΛ`. Rewrite using `[hF Λ hΛ c hc, hF Λ' hΛ' (fun k => h * c k) fun k => ⟨mul_mem_tens (fun v hv => (hm v).1 hv) (hc k).1, hP h hh.2 k _ (hc k).2⟩]`.

Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_` and prove the remaining obligations. Establish `e : ∀ z : Matrix (Fin n) (Fin r) E, h * z ∈ tens Λ' K ↔ z ∈ tens Λ K` using `fun z => ⟨fun hz => by`. Use `mul_mem_tens (fun v hv => (Base.moves_ccT hh.1 hm v).1 hv) hz` as an intermediate fact. Rewrite using `[← Matrix.mul_assoc, hh.1, Matrix.one_mul] at this,` and apply the resulting hypothesis. Use `mul_mem_tens fun v hv => (hm v).1 hv⟩`.

Simplify using `only [heisH_apply, ← Matrix.mul_sub, ← Matrix.mul_add, e, Matrix.mul_assoc h _ B, Matrix.mul_assoc h _ β, trace_unitary hh.1]`. Introduce `Λ hΛ x hx`. Take `⟨c, hc⟩` from `hex Λ hΛ`. Rewrite `hx` using `[hF Λ hΛ c hc]`. Take `⟨k, -, hx⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hx`.

Take `⟨k', -, hx⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hx`. Rewrite `hx` using `[heisH_apply]`. Establish `h1 : x - (c k - c k') ∈ tens Λ K`. Assume the negation of the conclusion as `h`. Simplify using `[h] at hx`.

Rewrite using `[colsIn_iff, eR, ← sub_add_cancel x (c k - c k'), smul_add (N : E)]`. Conclude with `nat_mem _ (add_mem (smul_mem_tens H1 h1) (smul_mem_tens H2 (sub_mem (hc k).1 (hc k').1)))`. Introduce `Λ hΛ x y hy`. Take `⟨c, hc⟩` from `hex Λ hΛ`. Rewrite `hy` using `[colsIn_iff]`.

Rewrite using `[hF Λ hΛ c hc, hF Λ hΛ c hc]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_` and prove the remaining obligations. Establish `hb` using `isIntegral_pair hΛ (mem_tens_mul H3 (add_mem (hc k).1 (hc k').1)) hy`. Establish `hR : ((2 * N * N' : ℕ) : E) • y ∈ tens Λ K`. Rewrite using `[eR']`.

Conclude with `nat_mem _ (smul_mem_tens H' hy)`. Rewrite using `[heisH_apply, heisH_apply]`. Generalize the expression as in `(c k + c k') * B = b at hb ⊢`. Generalize the expression as in `c k - c k' = d`. Use `congr 2`.

Rewrite using `[add_sub_right_comm]`. Generalize the expression as in `x - d = z`. Distinguish the cases in `hz : z ∈ tens Λ K`. Rewrite using `[if_pos hz, if_pos (add_mem hz hR)]`. Establish `h1` using `isIntegral_pair hΛ hy (mem_tens_mul H5 hz)`.

Establish `h2` using `isIntegral_pair hΛ (mem_tens_mul H4 hz) hy`. Establish `h3` using `isIntegral_pair hΛ (mem_tens_mul H6 hy) hy`. Rewrite using `[← exp_trace_add (t := (z * β * ccT z).trace) ((ni N').mul ((h1.add h2).add ((ni (2 * N * N')).mul h3)))]`. Use `congr 6`. Simplify using `only [ccT_add, ccT_nat, Base.ccT_mul, Base.ccT_ccT, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hz, if_neg fun h => hz ((AddSubgroup.add_mem_cancel_right _ hR).1 h)]`. Rewrite using `[← exp_trace_add (t := (b * ccT (x + x - d)).trace) ((ni (2 * N')).mul hb), show ∀ w, x + w + (x + w) - d = x + x - d + w + w from fun w => by abel]`. Generalize the expression as in `x + x - d = z`.

Use `congr 4`. Simplify using `only [ccT_add, ccT_nat, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `Λ hΛ Λ' hΛ' ⟨s, hs, hsc, h1, h2⟩ x hx hx'`.

Take `⟨c, hc⟩` from `hex Λ hΛ`. Establish `hsM : s.Coprime M` using `Nat.Coprime.coprime_mul_left_right hsc`. Establish `hsR : s.Coprime (2 * N * N')` using `Nat.Coprime.coprime_mul_right_right hsc`. Establish `hsR' : s.Coprime (N' * (2 * N * N'))` using `Nat.Coprime.mul_right (Nat.Coprime.coprime_mul_left_right hsR) hsR`. Take `⟨j, hj⟩` from `Nat.exists_eq_succ_of_ne_zero (Nat.totient_pos.2 hM).ne'`.

Take `⟨m, hm⟩` from `(Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hs)).1 (Nat.ModEq.pow_totient hsM).symm`. Establish `hm' : ((s ^ M.totient : ℕ) : E) - 1 = M * m`. Rewrite using `[← Nat.cast_mul, ← hm, Nat.cast_sub (Nat.one_le_pow _ _ hs), Nat.cast_one]`. Establish `hp : ∀ k, P k ((((s ^ M.totient : ℕ) : E) • (1 : Matrix (Fin n) (Fin n) E)) * c k)` using `fun k => hP _ ⟨1, one_pos, Nat.coprime_one_left M, (m : E) • 1, fun i i' => by`. Distinguish the cases in `h : i = i'`.

Simplify `ni m` using `[h]`. Simplify `isIntegral_zero, by` using `[h]`. Rewrite using `[Nat.cast_one, one_smul, smul_smul, ← hm', sub_smul, one_smul]⟩ k _ (hc k).2`. Establish `g1 : ∀ k, (((s ^ M.totient : ℕ) : E) • (1 : Matrix (Fin n) (Fin n) E)) * c k ∈ tens Λ K₀` using `fun k => mul_mem_tens (fun v hv => by`. Rewrite using `[Matrix.smul_mulVec, Matrix.one_mulVec]`.

Conclude with `Base.nat_smul_mem _ _ hv) (hc k).1`. Establish `g2 : ∀ k, (((s ^ M.totient : ℕ) : E) • (1 : Matrix (Fin n) (Fin n) E)) * c k ∈ tens Λ' K₀` using `fun k => mul_mem_tens (fun v hv => by`. Rewrite using `[Matrix.smul_mulVec, Matrix.one_mulVec, hj, pow_succ, Nat.cast_mul, mul_smul]`. Conclude with `Base.nat_smul_mem _ _ (h1 v hv)) (hc k).1`. Rewrite using `[hF Λ hΛ _ fun k => ⟨g1 k, hp k⟩, hF Λ' hΛ' _ fun k => ⟨g2 k, hp k⟩]`.

Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_` and prove the remaining obligations. Establish `key : ∀ (A A' : Lt E n) (d : Matrix (Fin n) (Fin r) E), (∀ v ∈ A, (s : E) • v ∈ A') → ColsIn A' (((2 * N * N' : ℕ) : E) • x) → d ∈ tens A' K₀ → x - d ∈ tens A K → x - d ∈ tens A' K`. Introduce `A A' d hA hx hd hz`. Use `mem_of_cop hsR' ?_ ?_` and prove the remaining obligations. Use `mul_mem_tens (h := (s : E) • 1) (Λ' := A') (fun v hv => by` as an intermediate fact.

Rewrite using `[Matrix.smul_mulVec, Matrix.one_mulVec]`. Conclude with `hA v hv) hz`. Rewrite `this` using `[Matrix.smul_mul, Matrix.one_mul]`. Then use the resulting hypothesis. Rewrite using `[Nat.cast_mul, mul_smul, smul_sub]`. Use `smul_mem_tens H' (sub_mem ((colsIn_iff _ _).1 hx) ?_)` and prove the remaining obligations.

Rewrite using `[eR]`. Conclude with `nat_mem _ (smul_mem_tens H2 hd)`. Rewrite using `[heisH_apply, heisH_apply, if_congr ⟨key Λ Λ' _ h1 hx' (sub_mem (g2 k) (g2 k')), key Λ' Λ _ h2 hx (sub_mem (g1 k) (g1 k'))⟩ rfl rfl]`.
-/
theorem admissible_of_sum_translates_quadraticCharacter : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n r M : ℕ), 0 < M → ∀ K K₀ : Lt E r, K.FG → Submodule.span E (K : Set (Fin r → E)) = ⊤ → K₀.FG → ∀ (B β : Matrix (Fin r) (Fin r) E) (t : ℂ) (J : Type) [Fintype J] (a : J → J → ℂ) (P : J → Matrix (Fin n) (Fin r) E → Prop) (F : Fam E n r), (∀ h : Matrix (Fin n) (Fin n) E, (∃ s : ℕ, 0 < s ∧ s.Coprime M ∧ ∃ z : Matrix (Fin n) (Fin n) E, IntM z ∧ (s : E) • (h - 1) = (M : E) • z) → ∀ k y, P k y → P k (h * y)) → (∀ Λ ∈ Vset E n M, ∃ c : J → Matrix (Fin n) (Fin r) E, ∀ k, c k ∈ tens Λ K₀ ∧ P k (c k)) → (∀ Λ ∈ Vset E n M, ∀ c : J → Matrix (Fin n) (Fin r) E, (∀ k, c k ∈ tens Λ K₀ ∧ P k (c k)) → ∀ x, F Λ x = ∑ k, ∑ k', a k k' * heisH (c k - c k') ((c k + c k') * B) (fun x => if x ∈ tens Λ K then t * cexp (π * I * ((Algebra.trace ℚ E (x * β * ccT x).trace : ℚ) : ℂ)) else 0) x) → ∃ R, admitted M R F := by
  intro E _ _ _ n r M hM K K₀ hK hKs hK₀ B β t J _ a P F hP hex hF
  let f : Matrix (Fin r) (Fin r) E → (Fin r → E) →ₗ[𝓞 E] (Fin r → E) := fun C =>
    (Matrix.vecMulLinear C).restrictScalars (𝓞 E)
  have hS : (stdL E r).FG := (Base.stdL_mem_Vset r 1).1
  obtain ⟨N, hN, H⟩ := exists_nat_mul_le (K := K ⊔ (K₀ ⊔ (K₀.map (f B) ⊔ (K.map (f β) ⊔
    (K.map (f (ccT β)) ⊔ (stdL E r).map (f β))))))
    (hK.sup (hK₀.sup ((hK₀.map _).sup ((hK.map _).sup ((hK.map _).sup (hS.map _)))))) span_stdL
  obtain ⟨N', hN', H'⟩ := exists_nat_mul_le hS hKs
  have l := fun (A A' : Lt E r) u => Submodule.mem_sup_left (S := A) (T := A') (x := u)
  have l' := fun (A A' : Lt E r) u => Submodule.mem_sup_right (S := A) (T := A') (x := u)
  have H1 : ∀ u ∈ K, (N : E) • u ∈ stdL E r := fun u hu => H _ (l _ _ _ hu)
  have H2 : ∀ u ∈ K₀, (N : E) • u ∈ stdL E r := fun u hu => H _ (l' _ _ _ (l _ _ _ hu))
  have H3 : ∀ u ∈ K₀, (N : E) • (u ᵥ* B) ∈ stdL E r := fun u hu =>
    H _ (l' _ _ _ (l' _ _ _ (l _ _ _ ⟨u, hu, rfl⟩)))
  have H4 : ∀ u ∈ K, (N : E) • (u ᵥ* β) ∈ stdL E r := fun u hu =>
    H _ (l' _ _ _ (l' _ _ _ (l' _ _ _ (l _ _ _ ⟨u, hu, rfl⟩))))
  have H5 : ∀ u ∈ K, (N : E) • (u ᵥ* ccT β) ∈ stdL E r := fun u hu =>
    H _ (l' _ _ _ (l' _ _ _ (l' _ _ _ (l' _ _ _ (l _ _ _ ⟨u, hu, rfl⟩)))))
  have H6 : ∀ u ∈ stdL E r, (N : E) • (u ᵥ* β) ∈ stdL E r := fun u hu =>
    H _ (l' _ _ _ (l' _ _ _ (l' _ _ _ (l' _ _ _ (l' _ _ _ ⟨u, hu, rfl⟩)))))
  clear H l l'
  have eR : ∀ y : Matrix (Fin n) (Fin r) E,
      ((2 * N * N' : ℕ) : E) • y = ((2 * N' : ℕ) : E) • (N : E) • y := fun y => by
    rw [smul_smul]; congr 1; push_cast; ring
  have eR' : ∀ y : Matrix (Fin n) (Fin r) E,
      ((2 * N * N' : ℕ) : E) • y = ((2 * N : ℕ) : E) • (N' : E) • y := fun y => by
    rw [smul_smul]; congr 1; push_cast; ring
  have ni : ∀ k : ℕ, IsIntegral ℤ (k : E) := fun k => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ))
  refine ⟨2 * N * N', ⟨hM, by positivity⟩, ?_, ?_, ?_, ?_⟩
  · intro h hh Λ hΛ Λ' hΛ' hm x
    obtain ⟨c, hc⟩ := hex Λ hΛ
    rw [hF Λ hΛ c hc, hF Λ' hΛ' (fun k => h * c k) fun k =>
      ⟨mul_mem_tens (fun v hv => (hm v).1 hv) (hc k).1, hP h hh.2 k _ (hc k).2⟩]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
    have e : ∀ z : Matrix (Fin n) (Fin r) E, h * z ∈ tens Λ' K ↔ z ∈ tens Λ K := fun z =>
      ⟨fun hz => by
        have := mul_mem_tens (fun v hv => (Base.moves_ccT hh.1 hm v).1 hv) hz
        rwa [← Matrix.mul_assoc, hh.1, Matrix.one_mul] at this,
      mul_mem_tens fun v hv => (hm v).1 hv⟩
    simp only [heisH_apply, ← Matrix.mul_sub, ← Matrix.mul_add, e, Matrix.mul_assoc h _ B,
      Matrix.mul_assoc h _ β, trace_unitary hh.1]
  · intro Λ hΛ x hx
    obtain ⟨c, hc⟩ := hex Λ hΛ
    rw [hF Λ hΛ c hc] at hx
    obtain ⟨k, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    obtain ⟨k', -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    rw [heisH_apply] at hx
    have h1 : x - (c k - c k') ∈ tens Λ K := by
      by_contra h; simp [h] at hx
    rw [colsIn_iff, eR, ← sub_add_cancel x (c k - c k'), smul_add (N : E)]
    exact nat_mem _ (add_mem (smul_mem_tens H1 h1)
      (smul_mem_tens H2 (sub_mem (hc k).1 (hc k').1)))
  · intro Λ hΛ x y hy
    obtain ⟨c, hc⟩ := hex Λ hΛ
    rw [colsIn_iff] at hy
    rw [hF Λ hΛ c hc, hF Λ hΛ c hc]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
    have hb := isIntegral_pair hΛ (mem_tens_mul H3 (add_mem (hc k).1 (hc k').1)) hy
    have hR : ((2 * N * N' : ℕ) : E) • y ∈ tens Λ K := by
      rw [eR']; exact nat_mem _ (smul_mem_tens H' hy)
    rw [heisH_apply, heisH_apply]
    generalize (c k + c k') * B = b at hb ⊢
    generalize c k - c k' = d
    congr 2
    · rw [add_sub_right_comm]
      generalize x - d = z
      by_cases hz : z ∈ tens Λ K
      · rw [if_pos hz, if_pos (add_mem hz hR)]
        have h1 := isIntegral_pair hΛ hy (mem_tens_mul H5 hz)
        have h2 := isIntegral_pair hΛ (mem_tens_mul H4 hz) hy
        have h3 := isIntegral_pair hΛ (mem_tens_mul H6 hy) hy
        rw [← exp_trace_add (t := (z * β * ccT z).trace)
          ((ni N').mul ((h1.add h2).add ((ni (2 * N * N')).mul h3)))]
        congr 6
        simp only [ccT_add, ccT_nat, Base.ccT_mul, Base.ccT_ccT, Matrix.add_mul, Matrix.mul_add,
          Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
          Matrix.mul_assoc]
        push_cast
        ring
      · rw [if_neg hz, if_neg fun h => hz ((AddSubgroup.add_mem_cancel_right _ hR).1 h)]
    · rw [← exp_trace_add (t := (b * ccT (x + x - d)).trace) ((ni (2 * N')).mul hb),
        show ∀ w, x + w + (x + w) - d = x + x - d + w + w from fun w => by abel]
      generalize x + x - d = z
      congr 4
      simp only [ccT_add, ccT_nat, Matrix.mul_add,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
      push_cast
      ring
  · rintro Λ hΛ Λ' hΛ' ⟨s, hs, hsc, h1, h2⟩ x hx hx'
    obtain ⟨c, hc⟩ := hex Λ hΛ
    have hsM : s.Coprime M := Nat.Coprime.coprime_mul_left_right hsc
    have hsR : s.Coprime (2 * N * N') := Nat.Coprime.coprime_mul_right_right hsc
    have hsR' : s.Coprime (N' * (2 * N * N')) :=
      Nat.Coprime.mul_right (Nat.Coprime.coprime_mul_left_right hsR) hsR
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.totient_pos.2 hM).ne'
    obtain ⟨m, hm⟩ := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hs)).1
      (Nat.ModEq.pow_totient hsM).symm
    have hm' : ((s ^ M.totient : ℕ) : E) - 1 = M * m := by
      rw [← Nat.cast_mul, ← hm, Nat.cast_sub (Nat.one_le_pow _ _ hs), Nat.cast_one]
    have hp : ∀ k, P k ((((s ^ M.totient : ℕ) : E) • (1 : Matrix (Fin n) (Fin n) E)) * c k) :=
      fun k => hP _ ⟨1, one_pos, Nat.coprime_one_left M, (m : E) • 1, fun i i' => by
        by_cases h : i = i'
        · simpa [h] using ni m
        · simpa [h] using isIntegral_zero, by
        rw [Nat.cast_one, one_smul, smul_smul, ← hm', sub_smul, one_smul]⟩ k _ (hc k).2
    have g1 : ∀ k, (((s ^ M.totient : ℕ) : E) • (1 : Matrix (Fin n) (Fin n) E)) * c k ∈
        tens Λ K₀ := fun k => mul_mem_tens (fun v hv => by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]; exact Base.nat_smul_mem _ _ hv) (hc k).1
    have g2 : ∀ k, (((s ^ M.totient : ℕ) : E) • (1 : Matrix (Fin n) (Fin n) E)) * c k ∈
        tens Λ' K₀ := fun k => mul_mem_tens (fun v hv => by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, hj, pow_succ, Nat.cast_mul, mul_smul]
      exact Base.nat_smul_mem _ _ (h1 v hv)) (hc k).1
    rw [hF Λ hΛ _ fun k => ⟨g1 k, hp k⟩, hF Λ' hΛ' _ fun k => ⟨g2 k, hp k⟩]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
    have key : ∀ (A A' : Lt E n) (d : Matrix (Fin n) (Fin r) E), (∀ v ∈ A, (s : E) • v ∈ A') →
        ColsIn A' (((2 * N * N' : ℕ) : E) • x) → d ∈ tens A' K₀ → x - d ∈ tens A K →
        x - d ∈ tens A' K := by
      intro A A' d hA hx hd hz
      refine mem_of_cop hsR' ?_ ?_
      · have := mul_mem_tens (h := (s : E) • 1) (Λ' := A') (fun v hv => by
          rw [Matrix.smul_mulVec, Matrix.one_mulVec]; exact hA v hv) hz
        rwa [Matrix.smul_mul, Matrix.one_mul] at this
      · rw [Nat.cast_mul, mul_smul, smul_sub]
        refine smul_mem_tens H' (sub_mem ((colsIn_iff _ _).1 hx) ?_)
        rw [eR]
        exact nat_mem _ (smul_mem_tens H2 hd)
    rw [heisH_apply, heisH_apply, if_congr ⟨key Λ Λ' _ h1 hx' (sub_mem (g2 k) (g2 k')),
      key Λ' Λ _ h2 hx (sub_mem (g1 k) (g1 k'))⟩ rfl rfl]

/- English proof (translation)
Introduce `E _ _ _ r X n D hn k y hy`. Use `⟨fun y' hy' j => ?_, fun M hM h ⟨s, _, hs, z, hz, e⟩ => ?_⟩` and prove the remaining obligations. Break down `lt_or_ge (j : ℕ) r with hj | hj` into its components or cases. Conclude with `Lev.cong_of_red hy.1 hy'.1 ⟨j, hj⟩`. Conclude with `Lev.cong_trans (hy.2 j hj) (Lev.cong_symm (hy'.2 j hj))`.

Establish `h0 : ∀ u v, Cong X D.𝔪 u v → v ∈ X.Λ → u ∈ Lev.loc D.𝔪 X.Λ` using `fun u v huv hv => by`. Simplify using `using add_mem (Lev.loc_mono Submodule.smul_le_right (Lev.cong_iff.1 huv)) (Lev.le_loc _ hv)`. Establish `h1 : ∀ j, y j ∈ Lev.loc D.𝔪 X.Λ` using `fun j => by`. Break down `lt_or_ge (j : ℕ) r with hj | hj` into its components or cases. Take `⟨k', -, hk'⟩` from `hy.1`.

Conclude with `h0 _ _ (hk' ⟨j, hj⟩) (Submodule.sum_mem _ fun i _ => X.Λ.smul_mem _ (D.β_mem i))`. Conclude with `h0 _ _ (hy.2 j hj) (zero_mem _)`. Establish `h2 : ∀ j, Cong X D.𝔪 ((h * y) j) (y j)` using `fun j => by`. Use `Lev.cong_iff.2 (Lev.loc_loc (cop_nat hs hM) ?_)` and prove the remaining obligations. Establish `: (s : 𝓞 E) • ((h * y) j - y j) = ∑ i, z j i • (M : 𝓞 E) • y i`.

Establish `e' : (s : E) • (h * y - y) = (M : E) • (z * y)`. Rewrite using `[← Matrix.smul_mul, ← e, Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul]`. Use function extensionality and compare the values at `a`. Establish `: (s : E) * ((h * y) j a - y j a) = (M : E) * (z * y) j a` using `congrFun (congrFun e' j) a`. Express the relevant statement in the definitionally equal form `(s : E) * ((h * y) j a - y j a) = (∑ i, z j i • (M : E) • y i) a`.

Rewrite using `[this, Matrix.mul_apply, Finset.sum_apply, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _`. Rewrite using `[this]`. Use `Submodule.sum_mem _ fun i _ => TensLat.int_smul_mem (hz j i) ?_` and prove the remaining obligations. Take `⟨t, ht, hy⟩` from `h1 i`.

Conclude with `⟨t, ht, by rw [smul_comm]; exact Submodule.smul_mem_smul hM hy⟩`. Conclude with `⟨Lev.red_congr (fun i => h2 _) hy.1, fun j hj => Lev.cong_trans (h2 j) (hy.2 j hj)⟩`.
-/
theorem red_rows : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (n : ℕ) (D : Level X) (hn : r ≤ n) (k : GL (Fin r) (𝓞 E ⧸ D.𝔪)) (y : Matrix (Fin n) (Fin r) E), (D.Red (fun i => y (Fin.castLE hn i)) k ∧ ∀ j : Fin n, r ≤ (j : ℕ) → Cong X D.𝔪 (y j) 0) → (∀ y' : Matrix (Fin n) (Fin r) E, (D.Red (fun i => y' (Fin.castLE hn i)) k ∧ ∀ j : Fin n, r ≤ (j : ℕ) → Cong X D.𝔪 (y' j) 0) → ∀ j, Cong X D.𝔪 (y j) (y' j)) ∧ ∀ M : ℕ, (M : 𝓞 E) ∈ D.𝔪 → ∀ h : Matrix (Fin n) (Fin n) E, (∃ s : ℕ, 0 < s ∧ s.Coprime M ∧ ∃ z : Matrix (Fin n) (Fin n) E, IntM z ∧ (s : E) • (h - 1) = (M : E) • z) → (D.Red (fun i => (h * y) (Fin.castLE hn i)) k ∧ ∀ j : Fin n, r ≤ (j : ℕ) → Cong X D.𝔪 ((h * y) j) 0) := by
  intro E _ _ _ r X n D hn k y hy
  refine ⟨fun y' hy' j => ?_, fun M hM h ⟨s, _, hs, z, hz, e⟩ => ?_⟩
  · rcases lt_or_ge (j : ℕ) r with hj | hj
    · exact Lev.cong_of_red hy.1 hy'.1 ⟨j, hj⟩
    · exact Lev.cong_trans (hy.2 j hj) (Lev.cong_symm (hy'.2 j hj))
  have h0 : ∀ u v, Cong X D.𝔪 u v → v ∈ X.Λ → u ∈ Lev.loc D.𝔪 X.Λ := fun u v huv hv => by
    simpa using add_mem (Lev.loc_mono Submodule.smul_le_right (Lev.cong_iff.1 huv))
      (Lev.le_loc _ hv)
  have h1 : ∀ j, y j ∈ Lev.loc D.𝔪 X.Λ := fun j => by
    rcases lt_or_ge (j : ℕ) r with hj | hj
    · obtain ⟨k', -, hk'⟩ := hy.1
      exact h0 _ _ (hk' ⟨j, hj⟩) (Submodule.sum_mem _ fun i _ => X.Λ.smul_mem _ (D.β_mem i))
    · exact h0 _ _ (hy.2 j hj) (zero_mem _)
  have h2 : ∀ j, Cong X D.𝔪 ((h * y) j) (y j) := fun j => by
    refine Lev.cong_iff.2 (Lev.loc_loc (cop_nat hs hM) ?_)
    have : (s : 𝓞 E) • ((h * y) j - y j) = ∑ i, z j i • (M : 𝓞 E) • y i := by
      have e' : (s : E) • (h * y - y) = (M : E) • (z * y) := by
        rw [← Matrix.smul_mul, ← e, Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul]
      funext a
      have : (s : E) * ((h * y) j a - y j a) = (M : E) * (z * y) j a := congrFun (congrFun e' j) a
      change (s : E) * ((h * y) j a - y j a) = (∑ i, z j i • (M : E) • y i) a
      rw [this, Matrix.mul_apply, Finset.sum_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
    rw [this]
    refine Submodule.sum_mem _ fun i _ => TensLat.int_smul_mem (hz j i) ?_
    obtain ⟨t, ht, hy⟩ := h1 i
    exact ⟨t, ht, by rw [smul_comm]; exact Submodule.smul_mem_smul hM hy⟩
  exact ⟨Lev.red_congr (fun i => h2 _) hy.1, fun j hj => Lev.cong_trans (h2 j) (hy.2 j hj)⟩

/- English proof (translation)
Introduce `E _ _ _ r X g bas idx n hs hev D M hM L hL Λ hΛ u hu y hy y' hy' hc`. Establish `half : ∀ v ∈ (Ideal.span {2} * conjI D.𝔪) • L, (2⁻¹ : E) • v ∈ L` using `fun v hv => by`. Rewrite `hv` using `[Submodule.mul_smul]`. Use `Submodule.smul_induction_on hv (fun a ha x hx => ?_) fun x x' hx hx' => ?_` and prove the remaining obligations. Take `⟨b, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`.

Establish `: (2⁻¹ : E) • (b * 2) • x = b • x`. Rewrite using `[Lev.O_smul, Lev.O_smul, smul_smul]`. Use `congr 1`. Rewrite using `[show ((b * 2 : 𝓞 E) : E) = b * 2 from by push_cast; rfl]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this]`. Conclude with `L.smul_mem _ (Submodule.smul_le_right hx)`. Rewrite using `[smul_add]`. Conclude with `add_mem hx hx'`. Establish `hsh : SelfD X (D.sh L)` using `Lev.selfD_idq D.ne_bot D.proper D.cop hL.1`.

Establish `h2 : ∀ w : Matrix (Fin n) (Fin r) E, w = (2⁻¹ : E) • w + (2⁻¹ : E) • w` using `fun w => by`. Rewrite using `[← add_smul]`. Evaluate the numerical expressions. Establish `hzL : y - y' ∈ tens Λ L`. Simplify `Submodule.smul_le_right hv) (sub_mem hy hy')` using `using smul_mem_tens (a := 1) (K' := L) (fun v hv => by simpa`.

Establish `hz : (2⁻¹ : E) • (y - y') ∈ tens Λ (D.sh L)`. Use `(TensLat.mem_tens_iff hΛ _ _).2 fun w hw => Lev.smul_le_idq _ _ _ ?_` and prove the remaining obligations. Use `Lev.mem_of_loc ((TensLat.mem_tens_iff hΛ _ _).1 (smul_mem_tens half (sub_mem hy hy')) w hw) le_rfl ?_` and prove the remaining obligations. Take `⟨s, -, hsM, hsw, -⟩` from `hΛ.2.2`. Take `⟨t, ht, -, htL⟩` from `hL.2`.

Use `Lev.loc_loc D.odd.symm (Lev.loc_loc (cop_nat hsM hM) ?_)` and prove the remaining obligations. Establish `: (s : 𝓞 E) • (2 : 𝓞 E) • TensLat.ctr ((2⁻¹ : E) • (y - y')) w = ∑ k, cc (((s : E) • w) k) • (y k - y' k)`. Use function extensionality and compare the values at `a`. Express the relevant statement in the definitionally equal form `(s : E) * (2 * TensLat.ctr ((2⁻¹ : E) • (y - y')) w a) = _`. Simplify using `only [TensLat.ctr, Finset.sum_apply, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(s : E) * (2 * (cc (w k) * (2⁻¹ * (y k a - y' k a)))) = cc ((s : E) * w k) * (y k a - y' k a)`. Simplify using `only [cc, map_mul, map_natCast]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`.

Use `Submodule.sum_mem _ fun k _ => TensLat.int_smul_mem (Base.isIntegral_cc ((Base.mem_stdL _).1 (hsw w hw) k)) ?_` and prove the remaining obligations. Take `⟨t', ht', h⟩` from `hc k`. Conclude with `⟨t * t', Lev.cop_mul ht.of_mul_right_left ht', by`. Rewrite using `[mul_smul]`. Conclude with `Lev.smul_map_mem LinearMap.id htL h⟩`.

Take `⟨g1, g2, g3, -⟩` from `TensLat.tens_selfDual_semichar_index E r X g bas idx n hs hev D.w D.w_int D.w_tr _ hsh M Λ hΛ`. Establish `e1` using `TensVac.Good.eps_two (A := tens Λ (D.sh L)) hs ⟨g1, g2, g3⟩ hz`. Rewrite `e1` using `[two_smul, ← h2]`. Establish `e2` using `hu.2.2 _ (add_mem hz hz)`. Rewrite `e2` using `[← h2, e1, one_smul]`.

Take `⟨m, hm⟩` from `(TensLat.tens_selfDual hΛ hL.1 _).1 (smul_mem_tens half hy') _ hzL`. Establish `e3 : ∑ k, EF X (y' k) ((y - y') k) = 2 * m`. Rewrite using `[two_mul, ← hm, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Lev.EF_add_left]`.

Conclude with `congrArg (EF X · _) (congrFun (h2 y') k)`. Establish `e4` using `(TensVac.laws idx hs hev y' hu.1).2.2.1 (y - y')`. Rewrite `e4` using `[e2, e3, add_sub_cancel]`. Rewrite using `[e4, show -(π * I * ((2 * m : ℚ) : ℂ)) = ((-m : ℤ) : ℂ) * (2 * π * I) by push_cast; ring, Complex.exp_int_mul_two_pi_mul_I, one_smul]`.
-/
theorem heisG_congr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : Level X) (M : ℕ), (M : 𝓞 E) ∈ D.𝔪 → ∀ L ∈ D.lats, ∀ Λ ∈ Vset E n M, ∀ u : TF n g, IsVac X bas D.w (tens Λ (D.sh L)) u → ∀ y ∈ tens Λ ((Ideal.span {2} * conjI D.𝔪) • L), ∀ y' ∈ tens Λ ((Ideal.span {2} * conjI D.𝔪) • L), (∀ k, Cong X D.𝔪 (y k) (y' k)) → heisG X bas y u = heisG X bas y' u := by
  intro E _ _ _ r X g bas idx n hs hev D M hM L hL Λ hΛ u hu y hy y' hy' hc
  have half : ∀ v ∈ (Ideal.span {2} * conjI D.𝔪) • L, (2⁻¹ : E) • v ∈ L := fun v hv => by
    rw [Submodule.mul_smul] at hv
    refine Submodule.smul_induction_on hv (fun a ha x hx => ?_) fun x x' hx hx' => ?_
    · obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      have : (2⁻¹ : E) • (b * 2) • x = b • x := by
        rw [Lev.O_smul, Lev.O_smul, smul_smul]
        congr 1
        rw [show ((b * 2 : 𝓞 E) : E) = b * 2 from by push_cast; rfl]
        field_simp
      rw [this]
      exact L.smul_mem _ (Submodule.smul_le_right hx)
    · rw [smul_add]; exact add_mem hx hx'
  have hsh : SelfD X (D.sh L) := Lev.selfD_idq D.ne_bot D.proper D.cop hL.1
  have h2 : ∀ w : Matrix (Fin n) (Fin r) E, w = (2⁻¹ : E) • w + (2⁻¹ : E) • w := fun w => by
    rw [← add_smul]; norm_num
  have hzL : y - y' ∈ tens Λ L := by
    simpa using smul_mem_tens (a := 1) (K' := L)
      (fun v hv => by simpa using Submodule.smul_le_right hv) (sub_mem hy hy')
  have hz : (2⁻¹ : E) • (y - y') ∈ tens Λ (D.sh L) := by
    refine (TensLat.mem_tens_iff hΛ _ _).2 fun w hw => Lev.smul_le_idq _ _ _ ?_
    refine Lev.mem_of_loc ((TensLat.mem_tens_iff hΛ _ _).1
      (smul_mem_tens half (sub_mem hy hy')) w hw) le_rfl ?_
    obtain ⟨s, -, hsM, hsw, -⟩ := hΛ.2.2
    obtain ⟨t, ht, -, htL⟩ := hL.2
    refine Lev.loc_loc D.odd.symm (Lev.loc_loc (cop_nat hsM hM) ?_)
    have : (s : 𝓞 E) • (2 : 𝓞 E) • TensLat.ctr ((2⁻¹ : E) • (y - y')) w =
        ∑ k, cc (((s : E) • w) k) • (y k - y' k) := by
      funext a
      change (s : E) * (2 * TensLat.ctr ((2⁻¹ : E) • (y - y')) w a) = _
      simp only [TensLat.ctr, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      change (s : E) * (2 * (cc (w k) * (2⁻¹ * (y k a - y' k a)))) =
        cc ((s : E) * w k) * (y k a - y' k a)
      simp only [cc, map_mul, map_natCast]
      field_simp
    rw [this]
    refine Submodule.sum_mem _ fun k _ => TensLat.int_smul_mem
      (Base.isIntegral_cc ((Base.mem_stdL _).1 (hsw w hw) k)) ?_
    obtain ⟨t', ht', h⟩ := hc k
    exact ⟨t * t', Lev.cop_mul ht.of_mul_right_left ht', by
      rw [mul_smul]; exact Lev.smul_map_mem LinearMap.id htL h⟩
  obtain ⟨g1, g2, g3, -⟩ := TensLat.tens_selfDual_semichar_index E r X g bas idx n hs hev D.w
    D.w_int D.w_tr _ hsh M Λ hΛ
  have e1 := TensVac.Good.eps_two (A := tens Λ (D.sh L)) hs ⟨g1, g2, g3⟩ hz
  rw [two_smul, ← h2] at e1
  have e2 := hu.2.2 _ (add_mem hz hz)
  rw [← h2, e1, one_smul] at e2
  obtain ⟨m, hm⟩ := (TensLat.tens_selfDual hΛ hL.1 _).1 (smul_mem_tens half hy') _ hzL
  have e3 : ∑ k, EF X (y' k) ((y - y') k) = 2 * m := by
    rw [two_mul, ← hm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Lev.EF_add_left]
    exact congrArg (EF X · _) (congrFun (h2 y') k)
  have e4 := (TensVac.laws idx hs hev y' hu.1).2.2.1 (y - y')
  rw [e2, e3, add_sub_cancel] at e4
  rw [e4, show -(π * I * ((2 * m : ℚ) : ℂ)) = ((-m : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
    Complex.exp_int_mul_two_pi_mul_I, one_smul]

variable {g : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

def Rep (D : Level X) (hn : r ≤ n) (k : D.J) (y : Matrix (Fin n) (Fin r) E) : Prop :=
  D.Red (fun i => y (Fin.castLE hn i)) k ∧ ∀ j : Fin n, r ≤ (j : ℕ) → Cong X D.𝔪 (y j) 0

/- English proof (translation)
Unfold `Level.dat at hy ⊢`. Use `split_ifs at hy ⊢ with h`. Conclude with `⟨h.1.choose, ⟨h.1.choose_spec, h.2⟩, rfl⟩`. Simplify using `at hy`.
-/
theorem exists_rep {D : Level X} {hn : r ≤ n} {y : Matrix (Fin n) (Fin r) E}
    (hy : ‖D.dat hn y‖ = 1) : ∃ k, Rep D hn k y ∧ D.dat hn y = (D.lam k : ℂˣ) := by
  unfold Level.dat at hy ⊢
  split_ifs at hy ⊢ with h
  · exact ⟨h.1.choose, ⟨h.1.choose_spec, h.2⟩, rfl⟩
  · simp at hy

/- English proof (translation)
Use `haveI : Finite (𝓞 E ⧸ D.𝔪) := Ideal.finiteQuotientOfFreeOfNeBot D.𝔪 D.ne_bot`. Use `infer_instance`.
-/
theorem finite_J (D : Level X) : Finite D.J := by
  haveI : Finite (𝓞 E ⧸ D.𝔪) := Ideal.finiteQuotientOfFreeOfNeBot D.𝔪 D.ne_bot
  infer_instance

/- English proof (translation)
Use `choose f hf using fun y : s => exists_rep (h1 y y.2)`. Establish `hi : Function.Injective f` using `fun y y' e => Subtype.ext <| h2 _ y.2 _ y'.2 <| (red_rows E r X n D hn (f y) y (hf y).1).1 y' (e ▸ (hf y').1)`. Establish `hb : Function.Bijective f` using `(Fintype.bijective_iff_injective_and_card f).2 ⟨hi, by rw [Fintype.card_coe, hc, Nat.card_eq_fintype_card]⟩`. Use `⟨(Equiv.ofBijective f hb).symm, fun k => ?_⟩` and prove the remaining obligations. Use `hf ((Equiv.ofBijective f hb).symm k)` as an intermediate fact.

Rewrite `this` using `[show f ((Equiv.ofBijective f hb).symm k) = k from (Equiv.ofBijective f hb).apply_symm_apply k]`. Then use the resulting hypothesis.
-/
theorem exists_index {D : Level X} {hn : r ≤ n} [Fintype D.J]
    {s : Finset (Matrix (Fin n) (Fin r) E)} (hc : s.card = Nat.card D.J)
    (h1 : ∀ y ∈ s, ‖D.dat hn y‖ = 1)
    (h2 : ∀ y ∈ s, ∀ y' ∈ s, (∀ k, Cong X D.𝔪 (y k) (y' k)) → y = y') :
    ∃ e : D.J ≃ s, ∀ k, Rep D hn k (e k) ∧ D.dat hn (e k) = (D.lam k : ℂˣ) := by
  choose f hf using fun y : s => exists_rep (h1 y y.2)
  have hi : Function.Injective f := fun y y' e => Subtype.ext <| h2 _ y.2 _ y'.2 <|
    (red_rows E r X n D hn (f y) y (hf y).1).1 y' (e ▸ (hf y').1)
  have hb : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2
    ⟨hi, by rw [Fintype.card_coe, hc, Nat.card_eq_fintype_card]⟩
  refine ⟨(Equiv.ofBijective f hb).symm, fun k => ?_⟩
  have := hf ((Equiv.ofBijective f hb).symm k)
  rwa [show f ((Equiv.ofBijective f hb).symm k) = k from
    (Equiv.ofBijective f hb).apply_symm_apply k] at this

/- English proof (translation)
Establish `sb : ∀ (χ : J → TF n g), (∀ k, IsSB (χ k)) → ∀ s : Finset J, IsSB (∑ k ∈ s, χ k)`. Introduce `χ hχ s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact isSB_zero`. Consider the case `insert a s ha ih`.

Rewrite using `[Finset.sum_insert ha]`. Conclude with `(GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ _ _ _ _ (hχ a) ih).1`. Establish `z` using `fun (φ₁ φ₂ : TF n g) h₁ h₂ => (GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hn φ₁ φ₂ h₁ h₂).2.1`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using z 0 _ isSB_zero (sb ψ hψ t) 0 1`.

Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, ((GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hn _ _ (hφ a) (sb ψ hψ t)).1 _ (sb φ hφ s)).1, ih]`. Use `congr 1`. Use `clear ih`. Proceed by induction on `t using Finset.induction_on with`.

Consider the case `empty => simpa using z _ 0 (hφ a) isSB_zero 1 0`. Consider the case `insert b t hb ih`. Rewrite using `[Finset.sum_insert hb, Finset.sum_insert hb, ((GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hn _ _ (hφ a) (hψ b)).1 _ (sb ψ hψ t)).2, ih]`.
-/
theorem dbl_sum (hs : IsSympl X bas) (hn : Even n) {J : Type} (s t : Finset J)
    {φ ψ : J → TF n g} (hφ : ∀ k, IsSB (φ k)) (hψ : ∀ k, IsSB (ψ k)) :
    dbl X bas idx (∑ k ∈ s, φ k) (∑ k ∈ t, ψ k) =
      ∑ k ∈ s, ∑ k' ∈ t, dbl X bas idx (φ k) (ψ k') := by
  have sb : ∀ (χ : J → TF n g), (∀ k, IsSB (χ k)) → ∀ s : Finset J, IsSB (∑ k ∈ s, χ k) := by
    intro χ hχ s
    induction s using Finset.induction_on with
    | empty => exact isSB_zero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ _ _ _ _ (hχ a) ih).1
  have z := fun (φ₁ φ₂ : TF n g) h₁ h₂ => (GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hn φ₁ φ₂ h₁ h₂).2.1
  induction s using Finset.induction_on with
  | empty => simpa using z 0 _ isSB_zero (sb ψ hψ t) 0 1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      ((GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hn _ _ (hφ a) (sb ψ hψ t)).1 _ (sb φ hφ s)).1, ih]
    congr 1
    clear ih
    induction t using Finset.induction_on with
    | empty => simpa using z _ 0 (hφ a) isSB_zero 1 0
    | insert b t hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb,
        ((GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hn _ _ (hφ a) (hψ b)).1 _ (sb ψ hψ t)).2, ih]

/- English proof (translation)
Rewrite using `[dblT, Matrix.fromCols_mul_fromBlocks, Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols]`. Simplify using `[sub_eq_add_neg, Matrix.add_mul]`.
-/
theorem fromCols_mul_dblT (y y' : Matrix (Fin n) (Fin r) E) :
    (Matrix.fromCols y y' * dblT X).toCols₁ = y - y' ∧
      (Matrix.fromCols y y' * dblT X).toCols₂ = (y + y') * ((X.κ0 / 4) • X.Gm) := by
  rw [dblT, Matrix.fromCols_mul_fromBlocks, Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols]
  simp [sub_eq_add_neg, Matrix.add_mul]

/- English proof (translation)
The claim follows from `Submodule.FG.of_le h' h`.
-/
theorem fg_of_le {K K' : Lt E r} (h : K ≤ K') (h' : K'.FG) : K.FG :=
  Submodule.FG.of_le h' h

/- English proof (translation)
Introduce `E _ _ _ r X g bas idx n hs hev D hn M hM hMm v₀ hv₀ L hL L' hL'`. Use `haveI := finite_J D`. Use `haveI := Fintype.ofFinite D.J`. Establish `lev` using `(level_laws E r X g bas idx n hs hev D hn).2.2.2.1`. Establish `phi` using `GlobalTheory.T.levelTestFunction_finite_sum_equivariant E r X g bas idx n hs hev D hn M hM hMm v₀ hv₀`.

Take `⟨β, t, -, hu⟩` from `GlobalTheory.T.doubledVacuum_eq_hermitian_character E r X g bas idx n hs hev D.w D.w_int D.w_tr _ _ (lev L hL).1 (lev L' hL').1 M hM _ _ (hv₀ L hL) (hv₀ L' hL')`. Establish `mono : ∀ (Λ : Lt E n) {K K' : Lt E r}, K ≤ K' → tens Λ K ≤ tens Λ K'` using `fun Λ K K' h => TensLat.tens_le fun v hv u hu => TensLat.pure_mem hv (h hu)`. Establish `key : ∀ L₁ ∈ D.lats, ∀ Λ ∈ Vset E n M, ∀ c : D.J → Matrix (Fin n) (Fin r) E, (∀ k, c k ∈ tens Λ ((Ideal.span {2} * conjI D.𝔪) • L₁) ∧ Rep D hn k (c k)) → D.phi bas hn v₀ L₁ Λ = ∑ k, ((D.lam k : ℂˣ) : ℂ) • heisG X bas (c k) (unitv (projA X bas D.w (tens Λ (D.sh L₁)) (v₀ L₁)))`. Introduce `L₁ h₁ Λ hΛ c hc`. Take `⟨-, hvac, h3, -⟩` from `phi L₁ h₁ Λ hΛ`.

Take `⟨s, hcard, hy, hsum, -⟩` from `h3 L₁ h₁`. Take `⟨e, he⟩` from `exists_index hcard (fun y h => (hy y h).2.1) fun y h => (hy y h).2.2`. Rewrite using `[hsum, ← Finset.sum_coe_sort, ← e.sum_comp]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[(he k).2]`.

Use `congr 1`. Use `heisG_congr E r X g bas idx n hs hev D M hMm L₁ h₁ Λ hΛ _ hvac _ ?_ _ (hc k).1 ((red_rows E r X n D hn k _ (he k).1).1 _ (hc k).2)` and prove the remaining obligations. Simplify using `using (hy _ (e k).2).1`. Use `admissible_of_sum_translates_quadraticCharacter E n r M hM (D.sh L ⊔ D.sh L') ((Ideal.span {2} * conjI D.𝔪) • (L ⊓ L')) ((lev L hL).1.1.sup (lev L' hL').1.1) ?_ (fg_of_le (Submodule.smul_le_right.trans inf_le_left) hL.1.1) ((X.κ0 / 4) • X.Gm) β t D.J (fun k k' => ((D.lam k : ℂˣ) …` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← TensLat.span_of_selfD X (lev L hL).1]`.

Conclude with `Submodule.span_mono (le_sup_left (a := D.sh L))`. Take `⟨s, hcard, hy, -⟩` from `(phi L hL Λ hΛ).2.2.1 L' hL'`. Take `⟨e, he⟩` from `exists_index hcard (fun y h => (hy y h).2.1) fun y h => (hy y h).2.2`. Conclude with `⟨fun k => e k, fun k => ⟨(hy _ (e k).2).1, (he k).1⟩⟩`. Establish `sb` using `(phi L hL Λ hΛ).2.1.1`.

Establish `sb'` using `(phi L' hL' Λ hΛ).2.1.1`. Establish `hb` using `fun y => (TensVac.laws idx hs hev y sb).1`. Establish `hb'` using `fun y => (TensVac.laws idx hs hev y sb').1`. Rewrite using `[key L hL Λ hΛ c fun k => ⟨mono Λ (smul_mono_right _ inf_le_left) (hc k).1, (hc k).2⟩, key L' hL' Λ hΛ c fun k => ⟨mono Λ (smul_mono_right _ inf_le_right) (hc k).1, (hc k).2⟩, dbl_sum idx hs hev _ _ (fun k => TensVac.sb_smul _ (hb _)) fun k => TensVac.sb_smul _ (hb' _)]`. Simplify using `only [Finset.sum_apply]`.

Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_` and prove the remaining obligations. Rewrite using `[(GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hev _ _ (hb _) (hb' _)).2.1, (GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hev _ _ sb sb').2.2, (fromCols_mul_dblT _ _).1, (fromCols_mul_dblT _ _).2, fun …`. Both sides reduce to the same expression.
-/
theorem adm_dbl_phi_of_isVac : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ L ∈ D.lats, ∀ L' ∈ D.lats, ∃ R, admitted M R fun Λ => dbl X bas idx (D.phi bas hn v₀ L Λ) (D.phi bas hn v₀ L' Λ) := by
  intro E _ _ _ r X g bas idx n hs hev D hn M hM hMm v₀ hv₀ L hL L' hL'
  haveI := finite_J D
  haveI := Fintype.ofFinite D.J
  have lev := (level_laws E r X g bas idx n hs hev D hn).2.2.2.1
  have phi := GlobalTheory.T.levelTestFunction_finite_sum_equivariant E r X g bas idx n hs hev D hn M hM hMm v₀ hv₀
  obtain ⟨β, t, -, hu⟩ := GlobalTheory.T.doubledVacuum_eq_hermitian_character E r X g bas idx n hs hev D.w D.w_int D.w_tr _ _ (lev L hL).1
    (lev L' hL').1 M hM _ _ (hv₀ L hL) (hv₀ L' hL')
  have mono : ∀ (Λ : Lt E n) {K K' : Lt E r}, K ≤ K' → tens Λ K ≤ tens Λ K' := fun Λ K K' h =>
    TensLat.tens_le fun v hv u hu => TensLat.pure_mem hv (h hu)
  have key : ∀ L₁ ∈ D.lats, ∀ Λ ∈ Vset E n M, ∀ c : D.J → Matrix (Fin n) (Fin r) E,
      (∀ k, c k ∈ tens Λ ((Ideal.span {2} * conjI D.𝔪) • L₁) ∧ Rep D hn k (c k)) →
      D.phi bas hn v₀ L₁ Λ = ∑ k, ((D.lam k : ℂˣ) : ℂ) • heisG X bas (c k)
        (unitv (projA X bas D.w (tens Λ (D.sh L₁)) (v₀ L₁))) := by
    intro L₁ h₁ Λ hΛ c hc
    obtain ⟨-, hvac, h3, -⟩ := phi L₁ h₁ Λ hΛ
    obtain ⟨s, hcard, hy, hsum, -⟩ := h3 L₁ h₁
    obtain ⟨e, he⟩ := exists_index hcard (fun y h => (hy y h).2.1) fun y h => (hy y h).2.2
    rw [hsum, ← Finset.sum_coe_sort, ← e.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(he k).2]
    congr 1
    refine heisG_congr E r X g bas idx n hs hev D M hMm L₁ h₁ Λ hΛ _ hvac _ ?_ _ (hc k).1
      ((red_rows E r X n D hn k _ (he k).1).1 _ (hc k).2)
    simpa using (hy _ (e k).2).1
  refine admissible_of_sum_translates_quadraticCharacter E n r M hM (D.sh L ⊔ D.sh L') ((Ideal.span {2} * conjI D.𝔪) • (L ⊓ L'))
    ((lev L hL).1.1.sup (lev L' hL').1.1) ?_
    (fg_of_le (Submodule.smul_le_right.trans inf_le_left) hL.1.1) ((X.κ0 / 4) • X.Gm) β t D.J
    (fun k k' => ((D.lam k : ℂˣ) : ℂ) * conj ((D.lam k' : ℂˣ) : ℂ)) (Rep D hn) _
    (fun h hh k y hy => (red_rows E r X n D hn k y hy).2 M hMm h hh) (fun Λ hΛ => ?_)
    fun Λ hΛ c hc x => ?_
  · rw [eq_top_iff, ← TensLat.span_of_selfD X (lev L hL).1]
    exact Submodule.span_mono (le_sup_left (a := D.sh L))
  · obtain ⟨s, hcard, hy, -⟩ := (phi L hL Λ hΛ).2.2.1 L' hL'
    obtain ⟨e, he⟩ := exists_index hcard (fun y h => (hy y h).2.1) fun y h => (hy y h).2.2
    exact ⟨fun k => e k, fun k => ⟨(hy _ (e k).2).1, (he k).1⟩⟩
  · have sb := (phi L hL Λ hΛ).2.1.1
    have sb' := (phi L' hL' Λ hΛ).2.1.1
    have hb := fun y => (TensVac.laws idx hs hev y sb).1
    have hb' := fun y => (TensVac.laws idx hs hev y sb').1
    rw [key L hL Λ hΛ c fun k => ⟨mono Λ (smul_mono_right _ inf_le_left) (hc k).1, (hc k).2⟩,
      key L' hL' Λ hΛ c fun k =>
        ⟨mono Λ (smul_mono_right _ inf_le_right) (hc k).1, (hc k).2⟩,
      dbl_sum idx hs hev _ _ (fun k => TensVac.sb_smul _ (hb _)) fun k => TensVac.sb_smul _ (hb' _)]
    simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
    rw [(GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hev _ _ (hb _) (hb' _)).2.1,
      (GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hev _ _ sb sb').2.2, (fromCols_mul_dblT _ _).1,
      (fromCols_mul_dblT _ _).2, funext (hu Λ hΛ)]
    rfl

end GlobalTheory.SW.DblAdm
