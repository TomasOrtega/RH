import Mathlib
import Formalism.FlagUnipotentLattices.LatticeDeterminantIndexSq
import Formalism.FlagUnipotentLattices.SignaturePreservingEntryNorms

open Module NumberField nonZeroDivisors Finset

noncomputable section

namespace Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false

/- English proof (translation)
Introduce `V _ _ _ h A Pos hA hP`. Establish `hd : Disjoint A Pos`. Rewrite using `[Submodule.disjoint_def]`. Introduce `x hxA hxP`. Assume the negation of the conclusion as `hx`.

Conclude with `absurd (hA x hxA) (not_le.mpr (hP x hxP hx))`. Conclude with `Submodule.finrank_add_finrank_le_of_disjoint hd`.
-/
theorem signatureBound_statement : SignatureBound := by
  intro V _ _ _ h A Pos hA hP
  have hd : Disjoint A Pos := by
    rw [Submodule.disjoint_def]
    intro x hxA hxP
    by_contra hx
    exact absurd (hA x hxA) (not_le.mpr (hP x hxP hx))
  exact Submodule.finrank_add_finrank_le_of_disjoint hd

/- English proof (translation)
Simplify using `[perpR, Submodule.mem_iInf]`.
-/
theorem s5a4_mem_perpR {K V : Type} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* K}
    (B : V →ₗ[K] V →ₛₗ[σ] K) (A : Submodule K V) (x : V) :
    x ∈ perpR B A ↔ ∀ a ∈ A, B a x = 0 := by
  simp [perpR, Submodule.mem_iInf]

/- English proof (translation)
Introduce `K V _ _ _ σ B U A hAU hc`. Prove the components needed by the constructor for the conclusion. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Establish `: x ∈ U ⊔ perpR B U` using `by rw [hc.sup_eq_top]; trivial`.

Take `⟨u, hu, w, hw, rfl⟩` from `Submodule.mem_sup.mp this`. Use `Submodule.mem_sup.mpr ⟨w, hw, u, ⟨hu, ?_⟩, by abel⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, s5a4_mem_perpR]`. Rewrite `hx`, `hw` using `[s5a4_mem_perpR]`. Introduce `a ha`.

Establish `h1` using `hx a ha`. Rewrite `h1` using `[map_add, hw a (hAU ha), add_zero]`. Conclude with `h1`. Apply `sup_le` to reduce the goal to its premises. Introduce `x hx`.

Rewrite `hx`, the goal using `[s5a4_mem_perpR]`. Conclude with `fun a ha => hx a (hAU ha)`. Conclude with `inf_le_right`. Conclude with `(hc.disjoint.symm).mono_right inf_le_left`.
-/
theorem orthogonal_splitting : PerpSplit := by
  intro K V _ _ _ σ B U A hAU hc
  constructor
  · apply le_antisymm
    · intro x hx
      have : x ∈ U ⊔ perpR B U := by rw [hc.sup_eq_top]; trivial
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp this
      refine Submodule.mem_sup.mpr ⟨w, hw, u, ⟨hu, ?_⟩, by abel⟩
      rw [SetLike.mem_coe, s5a4_mem_perpR]
      rw [s5a4_mem_perpR] at hx hw
      intro a ha
      have h1 := hx a ha
      rw [map_add, hw a (hAU ha), add_zero] at h1
      exact h1
    · apply sup_le
      · intro x hx; rw [s5a4_mem_perpR] at hx ⊢; exact fun a ha => hx a (hAU ha)
      · exact inf_le_right
  · exact (hc.disjoint.symm).mono_right inf_le_left

/- English proof (translation)
Introduce `R _ r Z c hc`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.vecMul_eq_sum, Matrix.det_updateRow_sum, hc]`. Simplify using the standard rewrite rules. Use `congr 1`.

Use extensionality with `i j`. Simplify using `[Matrix.updateRow_apply, Fin.castSucc_ne_last]`. Rewrite using `[Matrix.det_updateCol_add, Matrix.updateCol_eq_self]`. Establish `: Matrix.mulVec Z c = fun k => ∑ i, c i • Z k i`. Use extensionality with `k`.

Simplify using `[Matrix.mulVec, dotProduct, mul_comm]`. Rewrite using `[this, Matrix.det_updateCol_sum, hc]`. Simplify using the standard rewrite rules. Use `congr 1`. Use extensionality with `i j`.

Simplify using `[Matrix.updateCol_apply, Fin.castSucc_ne_last]`.
-/
theorem minor_lifting : MinorLift := by
  intro R _ r Z c hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.vecMul_eq_sum,
      Matrix.det_updateRow_sum, hc]; simp
  · congr 1; ext i j
    simp [Matrix.updateRow_apply, Fin.castSucc_ne_last]
  · rw [Matrix.det_updateCol_add, Matrix.updateCol_eq_self]
    have : Matrix.mulVec Z c = fun k => ∑ i, c i • Z k i := by
      ext k; simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [this, Matrix.det_updateCol_sum, hc]; simp
  · congr 1; ext i j
    simp [Matrix.updateCol_apply, Fin.castSucc_ne_last]

/- English proof (translation)
Introduce `R _ g T c hco h`. Establish `h0 : IsCoprime ((g : ℤ)) ((T : ℤ))` using `Nat.isCoprime_iff_coprime.mpr hco`. Establish `h1 : IsCoprime (g : R) (T : R)`. Use `h0.map (Int.castRingHom R)` as an intermediate fact. Simplify using `using this`.

Conclude with `h1.dvd_of_dvd_mul_right h`.
-/
theorem coprime_divisibility : CoprimeDiv := by
  intro R _ g T c hco h
  have h0 : IsCoprime ((g : ℤ)) ((T : ℤ)) := Nat.isCoprime_iff_coprime.mpr hco
  have h1 : IsCoprime (g : R) (T : R) := by
    have := h0.map (Int.castRingHom R)
    simpa using this
  exact h1.dvd_of_dvd_mul_right h

/- English proof (translation)
Introduce `detTh detLa GG i cardB hB h1 h2`. Rewrite using `[← h2, h1]`. Clear the denominators using the available nonvanishing facts.
-/
theorem lattice_determinant_index_square : LatticeDeterminantIndexSq := by
  intro detTh detLa GG i cardB hB h1 h2
  rw [← h2, h1]; field_simp

/- English proof (translation)
Introduce `K V _ _ _ σ h y₁ y₂ A₁ A₂ y₁' y₂' A₁' A₂' e1 e2 h1 h2 h3 h4`. Establish `l : h (y₁ - A₁) (y₂ - A₂) = h y₁ y₂ + h A₁ A₂`. Simplify using `only [map_sub, LinearMap.sub_apply, h1, h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `r : h (y₁' + A₁') (y₂' + A₂') = h y₁' y₂' + h A₁' A₂'`.

Simplify using `only [map_add, LinearMap.add_apply, h3, h4]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← l, ← r, e1, e2]`.
-/
theorem polarisation_sesquilinear : PolariseSesq := by
  intro K V _ _ _ σ h y₁ y₂ A₁ A₂ y₁' y₂' A₁' A₂' e1 e2 h1 h2 h3 h4
  have l : h (y₁ - A₁) (y₂ - A₂) = h y₁ y₂ + h A₁ A₂ := by
    simp only [map_sub, LinearMap.sub_apply, h1, h2]; ring
  have r : h (y₁' + A₁') (y₂' + A₂') = h y₁' y₂' + h A₁' A₂' := by
    simp only [map_add, LinearMap.add_apply, h3, h4]; ring
  rw [← l, ← r, e1, e2]

/- English proof (translation)
Introduce `K _ r Z c hdet hc`. Use `⟨(∑ b, c b * Z b (Fin.last r)) * Z.det⁻¹, fun b => ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit Z.det` using `isUnit_iff_ne_zero.mpr hdet`. Establish `h1 : Matrix.vecMul c Z = Pi.single (Fin.last r) (∑ b, c b * Z b (Fin.last r))`. Use extensionality with `a`.

Distinguish the cases in `ha : a = Fin.last r`. Substitute `ha` using the available equality. Simplify using `[Matrix.vecMul, dotProduct]`. Simplify using `[Matrix.vecMul, dotProduct, ha, hc a ha]`. Establish `h2 : c = Matrix.vecMul (Matrix.vecMul c Z) Z⁻¹`.

Rewrite using `[Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, Matrix.single_vecMul]`. Simplify using `[Matrix.inv_def, Ring.inverse_eq_inv']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cofactor_line_formula : CofactorLine := by
  intro K _ r Z c hdet hc
  refine ⟨(∑ b, c b * Z b (Fin.last r)) * Z.det⁻¹, fun b => ?_⟩
  have hu : IsUnit Z.det := isUnit_iff_ne_zero.mpr hdet
  have h1 : Matrix.vecMul c Z = Pi.single (Fin.last r) (∑ b, c b * Z b (Fin.last r)) := by
    ext a
    by_cases ha : a = Fin.last r
    · subst ha; simp [Matrix.vecMul, dotProduct]
    · simp [Matrix.vecMul, dotProduct, ha, hc a ha]
  have h2 : c = Matrix.vecMul (Matrix.vecMul c Z) Z⁻¹ := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]
  calc c b = (Matrix.vecMul (Matrix.vecMul c Z) Z⁻¹) b := congrFun h2 b
    _ = _ := by
      rw [h1, Matrix.single_vecMul]
      simp [Matrix.inv_def, Ring.inverse_eq_inv']; ring

/- English proof (translation)
Introduce `N h`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Establish `hJ : Formalism.SLP.GlobalBoundRefinements.J * Formalism.SLP.GlobalBoundRefinements.J = 1`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [Formalism.SLP.GlobalBoundRefinements.J, Matrix.mul_apply, Fin.sum_univ_two]`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc N.conjTranspose, h, hJ]`.
-/
theorem unipotent_upper_inverse : IndefiniteUnitaryInverse := by
  intro N h
  apply Matrix.inv_eq_left_inv
  have hJ : Formalism.SLP.GlobalBoundRefinements.J * Formalism.SLP.GlobalBoundRefinements.J = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Formalism.SLP.GlobalBoundRefinements.J, Matrix.mul_apply, Fin.sum_univ_two]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc N.conjTranspose, h, hJ]

/- English proof (translation)
Introduce `M N hM hN`. Rewrite using `[unipotent_upper_inverse N hN]`. Establish `e : (M * (Formalism.SLP.GlobalBoundRefinements.J * N.conjTranspose * Formalism.SLP.GlobalBoundRefinements.J)) 0 0 = M 0 0 * star (N 0 0) - M 0 1 * star (N 0 1)`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two, Formalism.SLP.GlobalBoundRefinements.J, Matrix.vecMul, dotProduct]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Take `⟨_, hM01, _⟩` from `Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.local_integral_entries_of_signature_preserving M hM`. Take `⟨_, hN01, _⟩` from `Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.local_integral_entries_of_signature_preserving N hN`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem theorem_B_entry_diagonal : ThmBEntryDiag := by
  intro M N hM hN
  rw [unipotent_upper_inverse N hN]
  have e : (M * (Formalism.SLP.GlobalBoundRefinements.J * N.conjTranspose * Formalism.SLP.GlobalBoundRefinements.J)) 0 0 =
      M 0 0 * star (N 0 0) - M 0 1 * star (N 0 1) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.SLP.GlobalBoundRefinements.J, Matrix.vecMul, dotProduct]; ring
  rw [e]
  obtain ⟨_, hM01, _⟩ := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.local_integral_entries_of_signature_preserving M hM
  obtain ⟨_, hN01, _⟩ := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.local_integral_entries_of_signature_preserving N hN
  calc _ ≤ ‖M 0 0 * star (N 0 0)‖ + ‖M 0 1 * star (N 0 1)‖ := norm_sub_le _ _
    _ = _ := by simp [hM01, hN01]

/- English proof (translation)
Introduce `E _ _ g t β J hg hβ hJ h`. Establish `hgE : (g : E) ≠ 0` using `by exact_mod_cast hg.ne'`. Establish `h1` using `Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.denomNormFrac E (β / (g : E) ^ t) J (div_ne_zero hβ (pow_ne_zero _ hgE)) hJ (by`. Introduce `x hx`. Take `⟨y, hy⟩` from `h x hx`.

Conclude with `⟨y, by rw [div_mul_eq_mul_div, hy]; field_simp⟩)`. Establish `hn : Algebra.norm ℚ ((g : E) ^ t) = (g : ℚ) ^ (t * finrank ℚ E)`. Establish `: (g : E) ^ t = algebraMap ℚ E ((g : ℚ) ^ t)` using `by simp`. Rewrite using `[this, Algebra.norm_algebraMap, ← pow_mul]`. Establish `hpos : (0 : ℚ) < (g : ℚ) ^ (t * finrank ℚ E)` using `by positivity`.

Establish `hq : Algebra.norm ℚ (β / (g : E) ^ t) = Algebra.norm ℚ β / (g : ℚ) ^ (t * finrank ℚ E)`. Rewrite using `[eq_div_iff hpos.ne', ← hn, ← map_mul, div_mul_cancel₀ _ (pow_ne_zero _ hgE)]`. Rewrite `h1` using `[hq, abs_div, abs_of_pos hpos, div_mul_eq_mul_div, le_div_iff₀ hpos, one_mul]`. Conclude with `h1`.
-/
theorem hadamard_ideal_bound : HadamardIdeal := by
  intro E _ _ g t β J hg hβ hJ h
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  have h1 := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.denomNormFrac E (β / (g : E) ^ t) J
    (div_ne_zero hβ (pow_ne_zero _ hgE)) hJ (by
      intro x hx; obtain ⟨y, hy⟩ := h x hx
      exact ⟨y, by rw [div_mul_eq_mul_div, hy]; field_simp⟩)
  have hn : Algebra.norm ℚ ((g : E) ^ t) = (g : ℚ) ^ (t * finrank ℚ E) := by
    have : (g : E) ^ t = algebraMap ℚ E ((g : ℚ) ^ t) := by simp
    rw [this, Algebra.norm_algebraMap, ← pow_mul]
  have hpos : (0 : ℚ) < (g : ℚ) ^ (t * finrank ℚ E) := by positivity
  have hq : Algebra.norm ℚ (β / (g : E) ^ t) = Algebra.norm ℚ β / (g : ℚ) ^ (t * finrank ℚ E) := by
    rw [eq_div_iff hpos.ne', ← hn, ← map_mul, div_mul_cancel₀ _ (pow_ne_zero _ hgE)]
  rw [hq, abs_div, abs_of_pos hpos, div_mul_eq_mul_div, le_div_iff₀ hpos, one_mul] at h1
  exact h1

/- English proof (translation)
Introduce `A C _ _ _ φ K S hK hS`. Establish `h1 : Nat.card A = Nat.card φ.range * Nat.card φ.ker`. Rewrite using `[AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker, Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv]`. Establish `: Finite φ.range` using `Set.finite_range φ`. Establish `h2 : Nat.card K ≤ Nat.card φ.ker` using `AddSubgroup.card_le_of_le hK`.

Establish `h3 : Nat.card S ≤ Nat.card φ.range` using `AddSubgroup.card_le_of_le hS`. Rewrite using `[h1, mul_comm]`. Conclude with `Nat.mul_le_mul h3 h2`.
-/
theorem kerImageCard_statement : KerImageCard := by
  intro A C _ _ _ φ K S hK hS
  have h1 : Nat.card A = Nat.card φ.range * Nat.card φ.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv]
  have : Finite φ.range := Set.finite_range φ
  have h2 : Nat.card K ≤ Nat.card φ.ker := AddSubgroup.card_le_of_le hK
  have h3 : Nat.card S ≤ Nat.card φ.range := AddSubgroup.card_le_of_le hS
  rw [h1, mul_comm]; exact Nat.mul_le_mul h3 h2

/- English proof (translation)
Introduce `E _ _ g p`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨y1, h1⟩, ⟨y2, h2⟩, w, hw⟩`. Use `⟨y2, w, 0, ?_⟩` and prove the remaining obligations. Use `ext`.

Simplify using `only`. Rewrite using `[← hw, h2]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[h2]`. Introduce and unpack `⟨c, a₁, a₂, rfl⟩`.

Use `⟨⟨-c + g * a₁, by simp⟩, ⟨c + g * a₂, by simp⟩, a₁ + a₂, ?_⟩` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integer_group_parametrization : ZZgParam := by
  intro E _ _ g p
  constructor
  · rintro ⟨⟨y1, h1⟩, ⟨y2, h2⟩, w, hw⟩
    refine ⟨y2, w, 0, ?_⟩
    ext
    · simp only; rw [← hw, h2]; ring
    · simp [h2]
  · rintro ⟨c, a₁, a₂, rfl⟩
    refine ⟨⟨-c + g * a₁, by simp⟩, ⟨c + g * a₂, by simp⟩, a₁ + a₂, ?_⟩
    push_cast; ring

/- English proof (translation)
Introduce `E _ _ g a b c d P h hg`. Take `⟨⟨x1, h1⟩, ⟨x2, h2⟩, ⟨x3, h3⟩, ⟨x4, h4⟩, _⟩` from `Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.zZgPreserve E g a b c d h`. Conclude with `⟨⟨g, x1, hg, by simp [h1]⟩, ⟨g, x2, hg, by simp [h2]⟩, ⟨g, x3, hg, by simp [h3]⟩, ⟨g, x4, hg, by simp [h4]⟩⟩`.
-/
theorem integer_group_local_parametrization : ZZgLocal := by
  intro E _ _ g a b c d P h hg
  obtain ⟨⟨x1, h1⟩, ⟨x2, h2⟩, ⟨x3, h3⟩, ⟨x4, h4⟩, _⟩ := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.zZgPreserve E g a b c d h
  exact ⟨⟨g, x1, hg, by simp [h1]⟩, ⟨g, x2, hg, by simp [h2]⟩, ⟨g, x3, hg, by simp [h3]⟩,
    ⟨g, x4, hg, by simp [h4]⟩⟩

/- English proof (translation)
Introduce `E _ _ σ T T' g s a c hT hT' hco hs1 hs2 ha hloc`. Establish `hTE : (T : E) ≠ 0` using `by exact_mod_cast hT.ne'`. Establish `hTE' : (T' : E) ≠ 0` using `by exact_mod_cast hT'.ne'`. Establish `key : IsInt ((g : E) ^ 2 * s / ((T : E) * T'))`. Apply `locGlob` to reduce the goal to its premises.

Introduce `P hP`. Distinguish the cases in `hg : (g : 𝓞 E) ∈ P`. Establish `hTT : ((T * T' : ℕ) : 𝓞 E) ∉ P`. Introduce `h`. Establish `hc : IsCoprime ((g : ℤ)) ((T * T' : ℕ) : ℤ)` using `Nat.isCoprime_iff_coprime.mpr hco`.

Take `⟨u, v, huv⟩` from `hc`. Establish `h1 : (1 : 𝓞 E) ∈ P`. Establish `e : (1 : 𝓞 E) = (u : 𝓞 E) * (g : 𝓞 E) + (v : 𝓞 E) * ((T * T' : ℕ) : 𝓞 E)`. Use `congrArg (Int.cast : ℤ → 𝓞 E) huv` as an intermediate fact. Move the coercions through the operations in `at this ⊢`.

Conclude with `this.symm`. Rewrite using `[e]`. Conclude with `P.add_mem (P.mul_mem_left _ hg) (P.mul_mem_left _ h)`. Conclude with `hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1)`. Use `⟨((T * T' : ℕ) : 𝓞 E), hTT, ?_⟩` and prove the remaining obligations.

Establish `: (((T * T' : ℕ) : 𝓞 E) : E) * ((g : E) ^ 2 * s / ((T : E) * T')) = (g : E) * a * σ ((g : E) * a) - (g : E) ^ 2`. Rewrite using `[hs2]`. Use `push_cast`. Simplify using `only [map_mul, map_natCast]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this]`. Establish `h3` using `isInt_mul ha (isInt_map σ ha)`. Establish `h4 : IsInt (-(g : E) ^ 2)` using `⟨-(g : 𝓞 E) ^ 2, by simp⟩`. Establish `h5` using `isInt_add h3 h4`. Simplify `h5` using `[sub_eq_add_neg]`.

Take `⟨y, z, hy, hyz⟩` from `hloc P hP hg`. Establish `hQ : (P.comap (RingOfIntegers.mapRingHom σ)).IsPrime` using `Ideal.comap_isPrime _ _`. Take `⟨y', z', hy', hyz'⟩` from `hloc _ hQ (by simpa [Ideal.mem_comap] using hg)`. Use `⟨y * RingOfIntegers.mapRingHom σ y', fun h => (hP.mem_or_mem h).elim hy hy', ?_⟩` and prove the remaining obligations. Use `⟨(g : 𝓞 E) ^ 2 * z * RingOfIntegers.mapRingHom σ z', ?_⟩` and prove the remaining obligations.

Establish `h2 : ((RingOfIntegers.mapRingHom σ y' : 𝓞 E) : E) * σ c = (T : E) * ((RingOfIntegers.mapRingHom σ z' : 𝓞 E) : E)`. Use `congrArg σ hyz'` as an intermediate fact. Simplify `this` using `[RingOfIntegers.mapRingHom_apply]`. Rewrite using `[hs1]`. Establish `: ((y * RingOfIntegers.mapRingHom σ y' : 𝓞 E) : E) * ((g : E) ^ 2 * ((T' : E) * c * σ c / T) / ((T : E) * T')) = (g : E) ^ 2 * (((y : E) * c) * (((RingOfIntegers.mapRingHom σ y' : 𝓞 E) : E) * σ c)) / (T : E) ^ 2` using `by push_cast; field_simp`.

Rewrite using `[this, hyz, h2]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Take `⟨β, hβ⟩` from `key`. Conclude with `⟨β, by rw [hβ]; field_simp⟩`.
-/
theorem integral_scalar_eq_one : SIntOne := by
  intro E _ _ σ T T' g s a c hT hT' hco hs1 hs2 ha hloc
  have hTE : (T : E) ≠ 0 := by exact_mod_cast hT.ne'
  have hTE' : (T' : E) ≠ 0 := by exact_mod_cast hT'.ne'
  have key : IsInt ((g : E) ^ 2 * s / ((T : E) * T')) := by
    apply locGlob
    intro P hP
    by_cases hg : (g : 𝓞 E) ∈ P
    · have hTT : ((T * T' : ℕ) : 𝓞 E) ∉ P := by
        intro h
        have hc : IsCoprime ((g : ℤ)) ((T * T' : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hco
        obtain ⟨u, v, huv⟩ := hc
        have h1 : (1 : 𝓞 E) ∈ P := by
          have e : (1 : 𝓞 E) = (u : 𝓞 E) * (g : 𝓞 E) + (v : 𝓞 E) * ((T * T' : ℕ) : 𝓞 E) := by
            have := congrArg (Int.cast : ℤ → 𝓞 E) huv
            push_cast at this ⊢; exact this.symm
          rw [e]; exact P.add_mem (P.mul_mem_left _ hg) (P.mul_mem_left _ h)
        exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1)
      refine ⟨((T * T' : ℕ) : 𝓞 E), hTT, ?_⟩
      have : (((T * T' : ℕ) : 𝓞 E) : E) * ((g : E) ^ 2 * s / ((T : E) * T')) =
          (g : E) * a * σ ((g : E) * a) - (g : E) ^ 2 := by
        rw [hs2]; push_cast; simp only [map_mul, map_natCast]; field_simp
      rw [this]
      have h3 := isInt_mul ha (isInt_map σ ha)
      have h4 : IsInt (-(g : E) ^ 2) := ⟨-(g : 𝓞 E) ^ 2, by simp⟩
      have h5 := isInt_add h3 h4
      simpa [sub_eq_add_neg] using h5
    · obtain ⟨y, z, hy, hyz⟩ := hloc P hP hg
      have hQ : (P.comap (RingOfIntegers.mapRingHom σ)).IsPrime := Ideal.comap_isPrime _ _
      obtain ⟨y', z', hy', hyz'⟩ := hloc _ hQ (by simpa [Ideal.mem_comap] using hg)
      refine ⟨y * RingOfIntegers.mapRingHom σ y', fun h => (hP.mem_or_mem h).elim hy hy', ?_⟩
      refine ⟨(g : 𝓞 E) ^ 2 * z * RingOfIntegers.mapRingHom σ z', ?_⟩
      have h2 : ((RingOfIntegers.mapRingHom σ y' : 𝓞 E) : E) * σ c =
          (T : E) * ((RingOfIntegers.mapRingHom σ z' : 𝓞 E) : E) := by
        have := congrArg σ hyz'
        simpa [RingOfIntegers.mapRingHom_apply] using this
      rw [hs1]
      have : ((y * RingOfIntegers.mapRingHom σ y' : 𝓞 E) : E) *
          ((g : E) ^ 2 * ((T' : E) * c * σ c / T) / ((T : E) * T')) =
          (g : E) ^ 2 * (((y : E) * c) * (((RingOfIntegers.mapRingHom σ y' : 𝓞 E) : E) * σ c)) /
            (T : E) ^ 2 := by
        push_cast; field_simp
      rw [this, hyz, h2]; push_cast; field_simp
  obtain ⟨β, hβ⟩ := key
  exact ⟨β, by rw [hβ]; field_simp⟩

/- English proof (translation)
Introduce `ga T T' hT hT'`. Establish `h1 : (Real.sqrt T : ℂ) ≠ 0` using `by exact_mod_cast (Real.sqrt_pos.mpr hT).ne'`. Establish `h2 : (Real.sqrt T' : ℂ) ≠ 0` using `by exact_mod_cast (Real.sqrt_pos.mpr hT').ne'`. Establish `hinv : (Matrix.diagonal ![(Real.sqrt T : ℂ), (Real.sqrt T' : ℂ)])⁻¹ = Matrix.diagonal ![(Real.sqrt T : ℂ)⁻¹, (Real.sqrt T' : ℂ)⁻¹]`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises.

Rewrite using `[Matrix.diagonal_mul_diagonal]`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [h1, h2]`. Rewrite using `[hinv]`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]`. Clear the denominators using the available nonvanishing facts.
-/
theorem diagonal_conjugation : DiagConj := by
  intro ga T T' hT hT'
  have h1 : (Real.sqrt T : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hT).ne'
  have h2 : (Real.sqrt T' : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hT').ne'
  have hinv : (Matrix.diagonal ![(Real.sqrt T : ℂ), (Real.sqrt T' : ℂ)])⁻¹ =
      Matrix.diagonal ![(Real.sqrt T : ℂ)⁻¹, (Real.sqrt T' : ℂ)⁻¹] := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j; fin_cases i <;> fin_cases j <;> simp [h1, h2]
  rw [hinv]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
  field_simp

/- English proof (translation)
Introduce `ch₁ sh₁ ch₂ sh₂ x h1 h2 hc1 hc2 e1 e2 hx hle`. Establish `hy : ch₁ / sh₁ * (ch₂ / sh₂) + 1 / sh₁ * (1 / sh₂) = (ch₁ * ch₂ + 1) / (sh₁ * sh₂)`. Clear the denominators using the available nonvanishing facts. Rewrite `hle` using `[hy]`. Establish `hsq : x ^ 2 ≤ ((ch₁ * ch₂ + 1) / (sh₁ * sh₂)) ^ 2` using `pow_le_pow_left₀ hx hle 2`.

Establish `: ((ch₁ * ch₂ + 1) / (sh₁ * sh₂)) ^ 2 - 1 = ((ch₁ + ch₂) / (sh₁ * sh₂)) ^ 2`. Rewrite using `[div_pow, div_pow]`. Establish `hne : (sh₁ * sh₂) ^ 2 ≠ 0` using `by positivity`. Rewrite using `[div_sub_one hne]`. Use `congr 1`.

Take the linear combination `(ch₂ ^ 2 - 1) * e1 + sh₁ ^ 2 * e2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hypothesis_additivity : HypAdd := by
  intro ch₁ sh₁ ch₂ sh₂ x h1 h2 hc1 hc2 e1 e2 hx hle
  have hy : ch₁ / sh₁ * (ch₂ / sh₂) + 1 / sh₁ * (1 / sh₂) = (ch₁ * ch₂ + 1) / (sh₁ * sh₂) := by
    field_simp
  rw [hy] at hle
  have hsq : x ^ 2 ≤ ((ch₁ * ch₂ + 1) / (sh₁ * sh₂)) ^ 2 := pow_le_pow_left₀ hx hle 2
  have : ((ch₁ * ch₂ + 1) / (sh₁ * sh₂)) ^ 2 - 1 = ((ch₁ + ch₂) / (sh₁ * sh₂)) ^ 2 := by
    rw [div_pow, div_pow]
    have hne : (sh₁ * sh₂) ^ 2 ≠ 0 := by positivity
    rw [div_sub_one hne]
    congr 1
    linear_combination (ch₂ ^ 2 - 1) * e1 + sh₁ ^ 2 * e2
  linarith

/- English proof (translation)
Introduce `K _ t₁ t₂ D₁ D₂ R₁ R₂ h1 h2 hD hR`. Establish `hiff : R₁ = 0 ↔ R₂ = 0`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite `hR` using `[h, mul_zero]`.

Conclude with `(mul_eq_zero.mp hR.symm).resolve_left h2`. Introduce `h`. Rewrite `hR` using `[h, mul_zero]`. Conclude with `(mul_eq_zero.mp hR).resolve_left h1`. Use `⟨hiff, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `h : R₁ = 0`. Rewrite using `[h, hiff.mp h]`. Simplify using the standard rewrite rules. Establish `h' : R₂ ≠ 0` using `fun e => h (hiff.mpr e)`. Rewrite using `[div_eq_div_iff h h']`.

Establish `: t₁ * t₂ * (D₁ * R₂ - D₂ * R₁) = 0` using `by linear_combination t₂ * R₂ * hD - t₂ * D₂ * hR`. Use `(mul_eq_zero.mp this).resolve_left (mul_ne_zero h1 h2)` as an intermediate fact. Take the linear combination `this`.
-/
theorem scalar_extension_bound : ScalarMore := by
  intro K _ t₁ t₂ D₁ D₂ R₁ R₂ h1 h2 hD hR
  have hiff : R₁ = 0 ↔ R₂ = 0 := by
    constructor
    · intro h; rw [h, mul_zero] at hR; exact (mul_eq_zero.mp hR.symm).resolve_left h2
    · intro h; rw [h, mul_zero] at hR; exact (mul_eq_zero.mp hR).resolve_left h1
  refine ⟨hiff, ?_⟩
  by_cases h : R₁ = 0
  · rw [h, hiff.mp h]; simp
  · have h' : R₂ ≠ 0 := fun e => h (hiff.mpr e)
    rw [div_eq_div_iff h h']
    have : t₁ * t₂ * (D₁ * R₂ - D₂ * R₁) = 0 := by linear_combination t₂ * R₂ * hD - t₂ * D₂ * hR
    have := (mul_eq_zero.mp this).resolve_left (mul_ne_zero h1 h2)
    linear_combination this

/- English proof (translation)
Introduce `R _ r Z`. Use `⟨fun b => ?_, (Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.cofactorVec R r Z).2⟩` and prove the remaining obligations. Use `congrFun (congrFun (Matrix.mul_adjugate Z) b) (Fin.last r)` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply]`. Rewrite using `[this]`.

Simplify using `[Matrix.one_apply]`.
-/
theorem cofactor_vector_dual : CofactorVecDual := by
  intro R _ r Z
  refine ⟨fun b => ?_, (Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.cofactorVec R r Z).2⟩
  have := congrFun (congrFun (Matrix.mul_adjugate Z) b) (Fin.last r)
  rw [Matrix.mul_apply] at this
  rw [this]; simp [Matrix.one_apply]

/- English proof (translation)
Introduce `K _ r Z c hD hc1 hc`. Take `⟨hw, hwl⟩` from `Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.cofactorVec K r Z`. Use `set Dr := (Z.submatrix Fin.castSucc Fin.castSucc).det with hDr`. Establish `key : ∀ b, c b = Z.adjugate (Fin.last r) b / Dr`. Set `d : Fin (r + 1) → K` to `fun b => c b - Z.adjugate (Fin.last r) b / Dr`.

Establish `hdl : d (Fin.last r) = 0` using `by simp [d, hc1, hwl, div_self hD]`. Establish `hd : ∀ a, a ≠ Fin.last r → ∑ b, d b * Z b a = 0`. Introduce `a ha`. Establish `h1` using `hw a`. Rewrite `h1` using `[if_neg ha]`.

Simplify using `only [d, sub_mul, Finset.sum_sub_distrib, hc a ha, div_mul_eq_mul_div, ← Finset.sum_div, h1]`. Simplify using the standard rewrite rules. Establish `hz : Matrix.vecMul (fun i : Fin r => d i.castSucc) (Z.submatrix Fin.castSucc Fin.castSucc) = 0`. Use extensionality with `a`. Use `hd a.castSucc (Fin.castSucc_ne_last a)` as an intermediate fact.

Rewrite `this` using `[Fin.sum_univ_castSucc, hdl, zero_mul, add_zero]`. Simplify `this` using `[Matrix.vecMul, dotProduct]`. Establish `h0` using `Matrix.eq_zero_of_vecMul_eq_zero hD hz`. Introduce `b`. Establish `: d b = 0`.

Use `Fin.lastCases hdl (fun i => ?_) b` and prove the remaining obligations. Conclude with `congrFun h0 i`. Conclude with `sub_eq_zero.mp this`. Use `⟨key, ?_⟩` and prove the remaining obligations. Establish `h1` using `hw (Fin.last r)`.

Rewrite `h1` using `[if_pos rfl]`. Simplify using `only [key, div_mul_eq_mul_div, ← Finset.sum_div, h1]`.
-/
theorem unique_lifting_property : UniqueLift := by
  intro K _ r Z c hD hc1 hc
  obtain ⟨hw, hwl⟩ := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.cofactorVec K r Z
  set Dr := (Z.submatrix Fin.castSucc Fin.castSucc).det with hDr
  have key : ∀ b, c b = Z.adjugate (Fin.last r) b / Dr := by
    let d : Fin (r + 1) → K := fun b => c b - Z.adjugate (Fin.last r) b / Dr
    have hdl : d (Fin.last r) = 0 := by simp [d, hc1, hwl, div_self hD]
    have hd : ∀ a, a ≠ Fin.last r → ∑ b, d b * Z b a = 0 := by
      intro a ha
      have h1 := hw a
      rw [if_neg ha] at h1
      simp only [d, sub_mul, Finset.sum_sub_distrib, hc a ha, div_mul_eq_mul_div, ← Finset.sum_div, h1]
      simp
    have hz : Matrix.vecMul (fun i : Fin r => d i.castSucc) (Z.submatrix Fin.castSucc Fin.castSucc) = 0 := by
      ext a
      have := hd a.castSucc (Fin.castSucc_ne_last a)
      rw [Fin.sum_univ_castSucc, hdl, zero_mul, add_zero] at this
      simpa [Matrix.vecMul, dotProduct] using this
    have h0 := Matrix.eq_zero_of_vecMul_eq_zero hD hz
    intro b
    have : d b = 0 := by
      refine Fin.lastCases hdl (fun i => ?_) b
      exact congrFun h0 i
    exact sub_eq_zero.mp this
  refine ⟨key, ?_⟩
  have h1 := hw (Fin.last r)
  rw [if_pos rfl] at h1
  simp only [key, div_mul_eq_mul_div, ← Finset.sum_div, h1]

/- English proof (translation)
Introduce `M f v d hv hd`. Establish `hd0 : 0 < d` using `by rw [hd]; positivity`. Establish `h1 : d ^ ((M : ℝ) - 1 / 2) = d ^ M * d ^ (-(1 / 2) : ℝ)`. Rewrite using `[sub_eq_add_neg, Real.rpow_add hd0, Real.rpow_natCast]`. Rewrite using `[h1, ← mul_assoc]`.

Use `congr 1`. Rewrite using `[hd]`. Establish `hpi` using `Real.pi_pos`. Simplify using `only [div_pow, mul_pow, ← pow_mul]`. Rewrite using `[mul_comm f M]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem mass_ratio_arithmetic : MassRatioArith := by
  intro M f v d hv hd
  have hd0 : 0 < d := by rw [hd]; positivity
  have h1 : d ^ ((M : ℝ) - 1 / 2) = d ^ M * d ^ (-(1 / 2) : ℝ) := by
    rw [sub_eq_add_neg, Real.rpow_add hd0, Real.rpow_natCast]
  rw [h1, ← mul_assoc]; congr 1
  rw [hd]
  have hpi := Real.pi_pos
  simp only [div_pow, mul_pow, ← pow_mul]
  rw [mul_comm f M]
  field_simp

/- English proof (translation)
Introduce `ι s e X h0 h1 he`. Establish `hL : 0 ≤ -Real.log (1 - X)`. Establish `: Real.log (1 - X) ≤ 0` using `Real.log_nonpos (by linarith) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Use `push_cast`.

Rewrite using `[Finset.sum_mul]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `p hp`. Establish `hpow : X ^ e p ≤ X`. Combine the equalities or inequalities in the displayed calculation.

Establish `h2 : Real.log (1 - X) ≤ Real.log (1 - X ^ e p)` using `Real.log_le_log (by linarith) (by linarith)`. Establish `h3 : (1 : ℝ) ≤ e p` using `by exact_mod_cast he p hp`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem euler_product_log_bound : EulerLog := by
  intro ι s e X h0 h1 he
  have hL : 0 ≤ -Real.log (1 - X) := by
    have : Real.log (1 - X) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    linarith
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  have hpow : X ^ e p ≤ X := by
    calc X ^ e p ≤ X ^ 1 := pow_le_pow_of_le_one h0.le h1.le (he p hp)
      _ = X := pow_one X
  have h2 : Real.log (1 - X) ≤ Real.log (1 - X ^ e p) := Real.log_le_log (by linarith) (by linarith)
  have h3 : (1 : ℝ) ≤ e p := by exact_mod_cast he p hp
  nlinarith

/- English proof (translation)
Introduce `f rd hrd`. Establish `h1 : (2 : ℝ) ^ (4 * f) * ((2 : ℝ) ^ (2 * f))⁻¹ * (rd ^ f) ^ 2 = (4 * rd ^ 2) ^ f`. Rewrite using `[pow_mul, pow_mul, ← inv_pow, ← mul_pow, ← pow_mul, mul_comm f 2, pow_mul, ← mul_pow]`. Evaluate the numerical expressions. Rewrite using `[h1]`.

Apply `pow_le_pow_left₀ (by positivity)` to reduce the goal to its premises. Use `Real.pi_gt_three` as an intermediate fact. Establish `h9 : (9 : ℝ) ≤ Real.pi ^ 2` using `by nlinarith`. Use polynomial arithmetic with `[sq_nonneg rd]`.
-/
theorem convex_body_condition : ConvexBodyCond := by
  intro f rd hrd
  have h1 : (2 : ℝ) ^ (4 * f) * ((2 : ℝ) ^ (2 * f))⁻¹ * (rd ^ f) ^ 2 = (4 * rd ^ 2) ^ f := by
    rw [pow_mul, pow_mul, ← inv_pow, ← mul_pow, ← pow_mul, mul_comm f 2, pow_mul, ← mul_pow]
    norm_num
  rw [h1]
  apply pow_le_pow_left₀ (by positivity)
  have := Real.pi_gt_three
  have h9 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
  nlinarith [sq_nonneg rd]

/- English proof (translation)
Introduce `f`. Establish `hN : (2 * f).factorial * 2 ^ f ≤ (2 * f) ^ (2 * f)`. Establish `h1 : (2 * f).factorial = f.factorial * (f + 1).ascFactorial f`. Rewrite using `[Nat.factorial_mul_ascFactorial]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2 : f.factorial ≤ f ^ f` using `Nat.factorial_le_pow f`. Establish `h3 : (f + 1).ascFactorial f ≤ (f + f) ^ f` using `Nat.ascFactorial_le_pow_add f f`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1]`.

Conclude with `Nat.mul_le_mul_right _ (Nat.mul_le_mul h2 h3)`. Use `_ = (2 * f) ^ (2 * f) := by`. Rewrite using `[two_mul f, pow_add, ← two_mul, mul_pow 2 f f]`. Expand and normalize the polynomial expressions, which then agree. Establish `hR : ((2 * f).factorial : ℝ) * 2 ^ f ≤ ((2 * f : ℕ) : ℝ) ^ (2 * f)` using `by exact_mod_cast hN`.

Establish `hpi` using `Real.pi_pos`. Break down `Nat.eq_zero_or_pos f with rfl | hf` into its components or cases. Simplify using the standard rewrite rules. Establish `hpos : (0 : ℝ) < ((2 * f : ℕ) : ℝ) ^ (2 * f)` using `by positivity`. Rewrite using `[div_le_iff₀ hpos, div_pow, div_pow]`.

Establish `h4 : (4 : ℝ) ^ f = 2 ^ f * 2 ^ f` using `by rw [← mul_pow]; norm_num`. Rewrite using `[h4]`. Establish `hpf : (0 : ℝ) < Real.pi ^ f` using `by positivity`. Rewrite using `[div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpf]`. Use polynomial arithmetic with `[pow_pos (show (0 : ℝ) < 2 by norm_num) f]`.
-/
theorem minkowski_constant_bound : MinkConst := by
  intro f
  have hN : (2 * f).factorial * 2 ^ f ≤ (2 * f) ^ (2 * f) := by
    have h1 : (2 * f).factorial = f.factorial * (f + 1).ascFactorial f := by
      rw [Nat.factorial_mul_ascFactorial]; congr 1; ring
    have h2 : f.factorial ≤ f ^ f := Nat.factorial_le_pow f
    have h3 : (f + 1).ascFactorial f ≤ (f + f) ^ f := Nat.ascFactorial_le_pow_add f f
    calc (2 * f).factorial * 2 ^ f ≤ (f ^ f * (f + f) ^ f) * 2 ^ f := by
          rw [h1]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul h2 h3)
      _ = (2 * f) ^ (2 * f) := by
          rw [two_mul f, pow_add, ← two_mul, mul_pow 2 f f]; ring
  have hR : ((2 * f).factorial : ℝ) * 2 ^ f ≤ ((2 * f : ℕ) : ℝ) ^ (2 * f) := by exact_mod_cast hN
  have hpi := Real.pi_pos
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · simp
  have hpos : (0 : ℝ) < ((2 * f : ℕ) : ℝ) ^ (2 * f) := by positivity
  rw [div_le_iff₀ hpos, div_pow, div_pow]
  have h4 : (4 : ℝ) ^ f = 2 ^ f * 2 ^ f := by rw [← mul_pow]; norm_num
  rw [h4]
  have hpf : (0 : ℝ) < Real.pi ^ f := by positivity
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpf]
  nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) f]

/- English proof (translation)
Introduce `f rd hf hrd`. Establish `hf' : (1 : ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hl : 0 ≤ Real.log rd` using `Real.log_nonneg hrd`. Establish `hrd0 : 0 < rd` using `by linarith`. Establish `hlog : Real.log (rd ^ f) = f * Real.log rd` using `Real.log_pow _ _`.

Establish `hA : 0 < 1 + Real.log (rd ^ f)` using `by rw [hlog]; positivity`. Rewrite using `[Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, hlog, Real.log_pow]`. Establish `h4 : Real.log 4 ≤ 2`. Establish `: (4 : ℝ) = 2 ^ 2` using `by norm_num`. Rewrite using `[this, Real.log_pow]`.

Use `Real.log_two_lt_d9` as an intermediate fact. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5 : Real.log (1 + f * Real.log rd) ≤ Real.log f + Real.log rd`. Rewrite using `[← Real.log_mul (by positivity) (by positivity)]`.

Apply `Real.log_le_log (by positivity)` to reduce the goal to its premises. Use `Real.log_le_sub_one_of_pos hrd0` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem logarithm_cube_bound : LogMassBound := by
  intro f rd hf hrd
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hl : 0 ≤ Real.log rd := Real.log_nonneg hrd
  have hrd0 : 0 < rd := by linarith
  have hlog : Real.log (rd ^ f) = f * Real.log rd := Real.log_pow _ _
  have hA : 0 < 1 + Real.log (rd ^ f) := by rw [hlog]; positivity
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, hlog, Real.log_pow]
  have h4 : Real.log 4 ≤ 2 := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast; linarith
  have h5 : Real.log (1 + f * Real.log rd) ≤ Real.log f + Real.log rd := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    have := Real.log_le_sub_one_of_pos hrd0
    nlinarith
  push_cast
  nlinarith

/- English proof (translation)
Introduce `f h2 I hE d hd hI hhE h hIb hEb`. Establish `hL : 0 ≤ Real.log d` using `Real.log_nonneg hd`. Use `set L := 1 + Real.log d with hLdef`. Establish `hL1 : 0 ≤ L` using `by positivity`. Establish `hd0 : 0 ≤ d` using `by linarith`.

Combine the equalities or inequalities in the displayed calculation. Establish `: (4 : ℝ) ^ f = (2 ^ f) ^ 2` using `by rw [← pow_mul, mul_comm, pow_mul]; norm_num`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem logarithm_cube_assembly : MassBoundOfFactorBounds := by
  intro f h2 I hE d hd hI hhE h hIb hEb
  have hL : 0 ≤ Real.log d := Real.log_nonneg hd
  set L := 1 + Real.log d with hLdef
  have hL1 : 0 ≤ L := by positivity
  have hd0 : 0 ≤ d := by linarith
  calc h2 ≤ I * ((2 : ℝ) ^ f * hE) ^ 2 * d ^ 2 := h
    _ ≤ (d * L ^ f) * ((2 : ℝ) ^ f * (d * L ^ (2 * f))) ^ 2 * d ^ 2 := by gcongr
    _ = (4 : ℝ) ^ f * d ^ 5 * L ^ (5 * f) := by
        have : (4 : ℝ) ^ f = (2 ^ f) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [this]; ring

/- English proof (translation)
Introduce `r c`. Proceed by induction on `r with`. Consider the case `zero => simp`. Consider the case `succ r ih`. Rewrite using `[Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_Icc_succ_top (by omega : 1 ≤ r + 1), Finset.prod_Icc_succ_top (by omega : 1 ≤ r + 1), mul_pow, ← Finset.prod_pow, ← mul_assoc, ← Finset.prod_mul_distrib]`.

Use `congr 1`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `a ha`. Rewrite `ha` using `[Finset.mem_Icc]`. Rewrite using `[← pow_add]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem weightProd_statement : WeightProd := by
  intro r c
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_Icc_succ_top (by omega : 1 ≤ r + 1),
      Finset.prod_Icc_succ_top (by omega : 1 ≤ r + 1), mul_pow, ← Finset.prod_pow, ← mul_assoc,
      ← Finset.prod_mul_distrib]
    congr 1
    · apply Finset.prod_congr rfl
      intro a ha
      rw [Finset.mem_Icc] at ha
      rw [← pow_add]; congr 1; omega
    · congr 1; omega

/- English proof (translation)
Introduce `j`. Establish `h1 : Stirling.stirlingSeq (j + 1) ≤ Stirling.stirlingSeq 1` using `Stirling.stirlingSeq'_antitone (Nat.zero_le j)`. Rewrite `h1` using `[Stirling.stirlingSeq_one]`. Unfold `Stirling.stirlingSeq at h1`. Establish `hk : (0 : ℝ) < ((j + 1 : ℕ) : ℝ)` using `by positivity`.

Use `set k : ℝ := ((j + 1 : ℕ) : ℝ) with hkdef`. Establish `he` using `Real.exp_pos 1`. Establish `hfac : ((j + 1).factorial : ℝ) = k * (j.factorial : ℝ)`. Rewrite using `[Nat.factorial_succ, hkdef]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hk1 : (1 : ℝ) ≤ k` using `by rw [hkdef]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)`. Establish `hs2 : 0 < Real.sqrt (2 * k)` using `Real.sqrt_pos.mpr (by positivity)`. Establish `e1 : (Real.exp 1 / k) ^ (j + 1) * (j.factorial : ℝ) = ((j + 1).factorial : ℝ) / (Real.sqrt (2 * k) * (k / Real.exp 1) ^ (j + 1)) * (Real.sqrt (2 * k) / k)`. Rewrite using `[hfac, div_pow, div_pow]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e1]`. Establish `h2 : Real.sqrt (2 * k) / k ≤ Real.sqrt 2`. Rewrite using `[div_le_iff₀ hk, Real.sqrt_mul (by norm_num)]`. Establish `: Real.sqrt k ≤ k`.

Rewrite using `[Real.sqrt_le_left hk.le]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h0` using `Real.sqrt_nonneg 2`. Use the polynomial consequences of the given equalities and inequalities. Establish `h3 : 0 ≤ Real.sqrt (2 * k) / k` using `by positivity`.

Establish `h4 : 0 ≤ Real.exp 1 / Real.sqrt 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul h1 h2 h3 h4` to reduce the goal to its premises. Use `_ = Real.exp 1 := by field_simp`. Use `_ ≤ 3 := by have := Real.exp_one_lt_d9; linarith`.
-/
theorem stabilizer_bound : StBound := by
  intro j
  have h1 : Stirling.stirlingSeq (j + 1) ≤ Stirling.stirlingSeq 1 :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le j)
  rw [Stirling.stirlingSeq_one] at h1
  unfold Stirling.stirlingSeq at h1
  have hk : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  set k : ℝ := ((j + 1 : ℕ) : ℝ) with hkdef
  have he := Real.exp_pos 1
  have hfac : ((j + 1).factorial : ℝ) = k * (j.factorial : ℝ) := by
    rw [Nat.factorial_succ, hkdef]; push_cast; ring
  have hk1 : (1 : ℝ) ≤ k := by rw [hkdef]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)

  have hs2 : 0 < Real.sqrt (2 * k) := Real.sqrt_pos.mpr (by positivity)
  have e1 : (Real.exp 1 / k) ^ (j + 1) * (j.factorial : ℝ) =
      ((j + 1).factorial : ℝ) / (Real.sqrt (2 * k) * (k / Real.exp 1) ^ (j + 1)) * (Real.sqrt (2 * k) / k) := by
    rw [hfac, div_pow, div_pow]; field_simp
  rw [e1]
  have h2 : Real.sqrt (2 * k) / k ≤ Real.sqrt 2 := by
    rw [div_le_iff₀ hk, Real.sqrt_mul (by norm_num)]
    have : Real.sqrt k ≤ k := by
      rw [Real.sqrt_le_left hk.le]
      nlinarith
    have h0 := Real.sqrt_nonneg 2
    nlinarith
  have h3 : 0 ≤ Real.sqrt (2 * k) / k := by positivity
  have h4 : 0 ≤ Real.exp 1 / Real.sqrt 2 := by positivity
  calc _ ≤ Real.exp 1 / Real.sqrt 2 * Real.sqrt 2 := by
        apply mul_le_mul h1 h2 h3 h4
    _ = Real.exp 1 := by field_simp
    _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith

/- English proof (translation)
Introduce `r th st hth hst0 hst`. Establish `h1 : (1 / 2 : ℝ) ^ (2 * r) ≤ th ^ (2 * r)` using `pow_le_pow_left₀ (by norm_num) hth _`. Establish `hp : (0 : ℝ) < (1 / 2 : ℝ) ^ (2 * r)` using `by positivity`. Establish `h2 : (th ^ (2 * r))⁻¹ ≤ ((1 / 2 : ℝ) ^ (2 * r))⁻¹` using `inv_anti₀ hp h1`. Establish `h3 : ((1 / 2 : ℝ) ^ (2 * r))⁻¹ = 2 ^ r * 2 ^ r`.

Rewrite using `[← inv_pow, two_mul, pow_add]`. Evaluate the numerical expressions. Rewrite `h2` using `[h3]`. Establish `h4 : 0 ≤ (th ^ (2 * r))⁻¹` using `by positivity`. Establish `h5 : (0 : ℝ) < 2 ^ r` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem final_constant_formula : ConstFinal := by
  intro r th st hth hst0 hst
  have h1 : (1 / 2 : ℝ) ^ (2 * r) ≤ th ^ (2 * r) := pow_le_pow_left₀ (by norm_num) hth _
  have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ (2 * r) := by positivity
  have h2 : (th ^ (2 * r))⁻¹ ≤ ((1 / 2 : ℝ) ^ (2 * r))⁻¹ := inv_anti₀ hp h1
  have h3 : ((1 / 2 : ℝ) ^ (2 * r))⁻¹ = 2 ^ r * 2 ^ r := by
    rw [← inv_pow, two_mul, pow_add]; norm_num
  rw [h3] at h2
  have h4 : 0 ≤ (th ^ (2 * r))⁻¹ := by positivity
  have h5 : (0 : ℝ) < 2 ^ r := by positivity
  calc ((2 : ℝ) ^ (r + 1))⁻¹ * (th ^ (2 * r))⁻¹ * st
      ≤ ((2 : ℝ) ^ (r + 1))⁻¹ * (2 ^ r * 2 ^ r) * 3 := by gcongr
    _ = 3 * (2 : ℝ) ^ r / 2 := by rw [pow_succ]; field_simp

/- English proof (translation)
Introduce `ι k x dimpi dimpi' deg VV Vd Tc K Pn Pk A B T' hPn hPk hA hB hT' hdeg hd' hx hVV hVd hT v`. Establish `h` using `hT v`. Rewrite `h` using `[hVV, hVd]`. Establish `hTk : Tc v ^ k = B * (deg v * Pn / (dimpi' v * Pk)) / A` using `by field_simp; field_simp at h; linarith`. Rewrite using `[hx, inv_pow, div_pow, hTk]`.

Use `hdeg v` as an intermediate fact. Use `hd' v` as an intermediate fact. Clear the denominators using the available nonvanishing facts.
-/
theorem same_place_constant : SamePlaceConst := by
  intro ι k x dimpi dimpi' deg VV Vd Tc K Pn Pk A B T' hPn hPk hA hB hT' hdeg hd' hx hVV hVd hT v
  have h := hT v
  rw [hVV, hVd] at h
  have hTk : Tc v ^ k = B * (deg v * Pn / (dimpi' v * Pk)) / A := by
    field_simp; field_simp at h; linarith
  rw [hx, inv_pow, div_pow, hTk]
  have := hdeg v; have := hd' v
  field_simp

/- English proof (translation)
Introduce `f r k v cc hf hv hcc hlo hhi`. Use `set w : ℝ := 2 * v with hw`. Establish `hw0 : 0 < w` using `by positivity`. Establish `hF : (0 : ℝ) < f` using `by exact_mod_cast hf`. Establish `hroot : (w ^ ((f : ℝ) / 2)) ^ (1 / (f : ℝ)) = w ^ (1 / 2 : ℝ)`.

Rewrite using `[← Real.rpow_mul hw0.le]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `hs : 0 < w ^ (1 / 2 : ℝ)` using `Real.rpow_pos_of_pos hw0 _`. Establish `h2root : (((2 : ℝ) ^ f)⁻¹) ^ (1 / (f : ℝ)) = 1 / 2`.

Rewrite using `[← Real.rpow_natCast, ← Real.rpow_neg (by norm_num), ← Real.rpow_mul (by norm_num)]`. Establish `: -(f : ℝ) * (1 / (f : ℝ)) = -1` using `by field_simp`. Rewrite using `[this, Real.rpow_neg_one]`. Evaluate the numerical expressions. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Use `Real.rpow_le_rpow (by positivity) hlo (by positivity : (0 : ℝ) ≤ 1 / (f : ℝ))` as an intermediate fact. Rewrite `this` using `[Real.mul_rpow (by positivity) (by positivity), hroot, h2root]`. Rewrite using `[← div_eq_mul_inv, le_div_iff₀ hs]`. Conclude with `this`. Use `Real.rpow_le_rpow hcc.le hhi (by positivity : (0 : ℝ) ≤ 1 / (f : ℝ))` as an intermediate fact.

Rewrite `this` using `[hroot]`. Rewrite using `[← div_eq_mul_inv, div_le_one hs]`. Conclude with `this`. Establish `hN : r * (k + 1) + r * (r - 1) = r * k + r ^ 2`. Consider the cases of `r with`.

Consider the case `zero => simp`. Consider the case `succ n => simp only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hN, Real.mul_rpow (by positivity) (by positivity)]`. Establish `e1 : (w ^ (f * (r * k + r ^ 2))) ^ (1 / (f : ℝ)) = w ^ (r * k) * w ^ ((r : ℝ) ^ 2)`.

Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hw0.le, ← Real.rpow_natCast, ← Real.rpow_add hw0]`. Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `e2 : (cc ^ r) ^ (1 / (f : ℝ)) = (cc ^ (1 / (f : ℝ))) ^ r`.

Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hcc.le, ← Real.rpow_natCast, ← Real.rpow_mul hcc.le, mul_comm]`. Establish `e3 : w ^ ((r : ℝ) ^ 2 + (r : ℝ) / 2) = w ^ ((r : ℝ) ^ 2) * (w ^ (1 / 2 : ℝ)) ^ r`. Rewrite using `[Real.rpow_add hw0, ← Real.rpow_natCast (w ^ (1 / 2 : ℝ)), ← Real.rpow_mul hw0.le]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, e2, e3, mul_pow (cc ^ (1 / (f : ℝ))), inv_pow]`. Establish `hsr : (w ^ (1 / 2 : ℝ)) ^ r ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts.
-/
theorem covolume_splitting : CovSplit := by
  intro f r k v cc hf hv hcc hlo hhi
  set w : ℝ := 2 * v with hw
  have hw0 : 0 < w := by positivity
  have hF : (0 : ℝ) < f := by exact_mod_cast hf
  have hroot : (w ^ ((f : ℝ) / 2)) ^ (1 / (f : ℝ)) = w ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_mul hw0.le]; congr 1; field_simp
  have hs : 0 < w ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hw0 _
  have h2root : (((2 : ℝ) ^ f)⁻¹) ^ (1 / (f : ℝ)) = 1 / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num), ← Real.rpow_mul (by norm_num)]
    have : -(f : ℝ) * (1 / (f : ℝ)) = -1 := by field_simp
    rw [this, Real.rpow_neg_one]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · have := Real.rpow_le_rpow (by positivity) hlo (by positivity : (0 : ℝ) ≤ 1 / (f : ℝ))
    rw [Real.mul_rpow (by positivity) (by positivity), hroot, h2root] at this
    rw [← div_eq_mul_inv, le_div_iff₀ hs]; exact this
  · have := Real.rpow_le_rpow hcc.le hhi (by positivity : (0 : ℝ) ≤ 1 / (f : ℝ))
    rw [hroot] at this
    rw [← div_eq_mul_inv, div_le_one hs]; exact this
  · have hN : r * (k + 1) + r * (r - 1) = r * k + r ^ 2 := by
      cases r with
      | zero => simp
      | succ n => simp only [Nat.add_sub_cancel]; ring
    rw [hN, Real.mul_rpow (by positivity) (by positivity)]
    have e1 : (w ^ (f * (r * k + r ^ 2))) ^ (1 / (f : ℝ)) = w ^ (r * k) * w ^ ((r : ℝ) ^ 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hw0.le, ← Real.rpow_natCast, ← Real.rpow_add hw0]
      congr 1; push_cast; field_simp
    have e2 : (cc ^ r) ^ (1 / (f : ℝ)) = (cc ^ (1 / (f : ℝ))) ^ r := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hcc.le, ← Real.rpow_natCast, ← Real.rpow_mul hcc.le,
        mul_comm]
    have e3 : w ^ ((r : ℝ) ^ 2 + (r : ℝ) / 2) = w ^ ((r : ℝ) ^ 2) * (w ^ (1 / 2 : ℝ)) ^ r := by
      rw [Real.rpow_add hw0, ← Real.rpow_natCast (w ^ (1 / 2 : ℝ)), ← Real.rpow_mul hw0.le]
      congr 2; ring
    rw [e1, e2, e3, mul_pow (cc ^ (1 / (f : ℝ))), inv_pow]
    have hsr : (w ^ (1 / 2 : ℝ)) ^ r ≠ 0 := by positivity
    field_simp

/- English proof (translation)
Introduce `j r T T' g v th dimpi Vd VV Tc hT hT' hg hv hth hVd hVV hTc hdef`. Establish `hpi` using `Real.pi_pos`. Establish `he` using `Real.exp_pos 1`. Establish `hk : (0 : ℝ) < ((j + 1 : ℕ) : ℝ)` using `by positivity`. Establish `hjf : (0 : ℝ) < (j.factorial : ℝ)` using `by exact_mod_cast j.factorial_pos`.

Establish `hM1 : (2 * r + 2) * (2 * r + 1) / 2 = 2 * r ^ 2 + r + (2 * r + 1)`. Establish `: (2 * r + 2) * (2 * r + 1) = 2 * (2 * r ^ 2 + r + (2 * r + 1))` using `by ring`. Rewrite using `[this, Nat.mul_div_cancel_left _ (by norm_num)]`. Establish `hM2 : (2 * r + 1) * (2 * r + 2) / 2 = 2 * r ^ 2 + r + (2 * r + 1)`. Rewrite using `[mul_comm, hM1]`.

Use `set κ : ℝ := (Real.exp 1 / ((j + 1 : ℕ) : ℝ)) ^ (j + 1) * (j.factorial : ℝ) with hκ`. Use `set n0 : ℝ := (Real.exp 1 * Real.pi / (g ^ (2 * r + 2) * T * ((j + 1 : ℕ) : ℝ) * v)) ^ (j + 1) with hn0`. Establish `hn : n0 * (j.factorial : ℝ) / (2 * Real.pi) ^ (j + 1) = κ / (g ^ (2 * r + 2) * T * (2 * v)) ^ (j + 1)`. Rewrite using `[hn0, hκ]`. Simplify using `only [div_pow, mul_pow]`.

Clear the denominators using the available nonvanishing facts. Establish `CP` using `Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.constProduct j r T T' g v n0 κ dimpi Vd VV hT hT' hg hv hVV hn`. Establish `TF` using `Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.tcritForm (j + 1) r T' g v (2 * v) Vd VV Tc hT' hg hv (by positivity) hVd hVV hTc hdef`. Rewrite `CP` using `[hM2]`. Rewrite `TF`, the goal using `[hM1]`.

Use `set w : ℝ := 2 * v with hw`. Establish `hw0 : 0 < w` using `by positivity`. Use `set H : ℝ := w ^ (((2 * r + 1 : ℕ) : ℝ) / 2) with hH`. Establish `hH0 : 0 < H` using `Real.rpow_pos_of_pos hw0 _`. Establish `hHH : H * H = w ^ (2 * r + 1)`.

Rewrite using `[hH, ← Real.rpow_add hw0, ← Real.rpow_natCast]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hH' : w ^ ((r : ℝ) + 1 / 2) = H` using `by rw [hH]; congr 1; push_cast; ring`. Establish `hgp : (g / (Real.pi / v)) ^ (2 * r ^ 2 + r + (2 * r + 1)) * (2 * Real.pi) ^ (2 * r ^ 2 + r + (2 * r + 1)) = g ^ (2 * r ^ 2 + r + (2 * r + 1)) * (w ^ (2 * r ^ 2 + r) * (H * H))`.

Rewrite using `[hHH, ← pow_add, ← mul_pow, ← mul_pow]`. Use `congr 1`. Rewrite using `[hw]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hH']`.

Use `set Q : ℝ := (Tc / T')⁻¹ ^ (j + 1) with hQ`. Use `set G1 : ℝ := (g / (Real.pi / v)) ^ (2 * r ^ 2 + r + (2 * r + 1)) with hG1`. Use `set Pp : ℝ := (2 * Real.pi) ^ (2 * r ^ 2 + r + (2 * r + 1)) with hPp`. Use `set c1 : ℝ := ((2 : ℝ) ^ (r + 1))⁻¹ with hc1`. Use `set c2 : ℝ := (th ^ (2 * r))⁻¹ with hc2`.

Establish `hwb : 0 < w ^ (2 * r ^ 2 + r)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[add_assoc (2 * r * (j + 1)), pow_add w, pow_succ (T * T')]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = c1 * c2 * (T * T') / w ^ (2 * r ^ 2 + r) * (dimpi * (Q * (G1 / H)) * (κ * Pp / (T * T'))) := by`.

Rewrite using `[CP, mul_assoc dimpi, TF]`. Use `_ = c1 * c2 * dimpi * Q * κ * (G1 * Pp) / (w ^ (2 * r ^ 2 + r) * H) := by`. Clear the denominators using the available nonvanishing facts. Use `_ = _ := by`. Rewrite using `[hgp]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem exact_constant_formula : ConstExact := by
  intro j r T T' g v th dimpi Vd VV Tc hT hT' hg hv hth hVd hVV hTc hdef
  have hpi := Real.pi_pos
  have he := Real.exp_pos 1
  have hk : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hjf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast j.factorial_pos
  have hM1 : (2 * r + 2) * (2 * r + 1) / 2 = 2 * r ^ 2 + r + (2 * r + 1) := by
    have : (2 * r + 2) * (2 * r + 1) = 2 * (2 * r ^ 2 + r + (2 * r + 1)) := by ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  have hM2 : (2 * r + 1) * (2 * r + 2) / 2 = 2 * r ^ 2 + r + (2 * r + 1) := by
    rw [mul_comm, hM1]
  set κ : ℝ := (Real.exp 1 / ((j + 1 : ℕ) : ℝ)) ^ (j + 1) * (j.factorial : ℝ) with hκ
  set n0 : ℝ := (Real.exp 1 * Real.pi / (g ^ (2 * r + 2) * T * ((j + 1 : ℕ) : ℝ) * v)) ^ (j + 1) with hn0
  have hn : n0 * (j.factorial : ℝ) / (2 * Real.pi) ^ (j + 1) =
      κ / (g ^ (2 * r + 2) * T * (2 * v)) ^ (j + 1) := by
    rw [hn0, hκ]
    simp only [div_pow, mul_pow]
    field_simp
  have CP := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.constProduct j r T T' g v n0 κ dimpi Vd VV hT hT' hg hv hVV hn
  have TF := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.tcritForm (j + 1) r T' g v (2 * v) Vd VV Tc hT' hg hv (by positivity)
    hVd hVV hTc hdef
  rw [hM2] at CP
  rw [hM1] at TF ⊢
  set w : ℝ := 2 * v with hw
  have hw0 : 0 < w := by positivity
  set H : ℝ := w ^ (((2 * r + 1 : ℕ) : ℝ) / 2) with hH
  have hH0 : 0 < H := Real.rpow_pos_of_pos hw0 _
  have hHH : H * H = w ^ (2 * r + 1) := by
    rw [hH, ← Real.rpow_add hw0, ← Real.rpow_natCast]; congr 1; ring
  have hH' : w ^ ((r : ℝ) + 1 / 2) = H := by rw [hH]; congr 1; push_cast; ring
  have hgp : (g / (Real.pi / v)) ^ (2 * r ^ 2 + r + (2 * r + 1)) *
      (2 * Real.pi) ^ (2 * r ^ 2 + r + (2 * r + 1)) =
      g ^ (2 * r ^ 2 + r + (2 * r + 1)) * (w ^ (2 * r ^ 2 + r) * (H * H)) := by
    rw [hHH, ← pow_add, ← mul_pow, ← mul_pow]; congr 1; rw [hw]; field_simp
  rw [hH']
  set Q : ℝ := (Tc / T')⁻¹ ^ (j + 1) with hQ
  set G1 : ℝ := (g / (Real.pi / v)) ^ (2 * r ^ 2 + r + (2 * r + 1)) with hG1
  set Pp : ℝ := (2 * Real.pi) ^ (2 * r ^ 2 + r + (2 * r + 1)) with hPp
  set c1 : ℝ := ((2 : ℝ) ^ (r + 1))⁻¹ with hc1
  set c2 : ℝ := (th ^ (2 * r))⁻¹ with hc2
  have hwb : 0 < w ^ (2 * r ^ 2 + r) := by positivity
  calc _ = c1 * c2 * (T * T') / w ^ (2 * r ^ 2 + r) *
        (n0 * (T * T') ^ j *
          (dimpi * (Vd / ∏ i ∈ range (j + 1), (i.factorial : ℝ)) * volU (j + 1 + (2 * r + 1)) * volU j /
            (VV / (∏ i ∈ range (j + 1 + (2 * r + 1)), (i.factorial : ℝ)) * volU (j + 1) ^ 2 *
              w ^ (2 * r * (j + 1))))) := by
        rw [add_assoc (2 * r * (j + 1)), pow_add w, pow_succ (T * T')]
        ring
    _ = c1 * c2 * (T * T') / w ^ (2 * r ^ 2 + r) *
        (dimpi * (Q * (G1 / H)) * (κ * Pp / (T * T'))) := by
        rw [CP, mul_assoc dimpi, TF]
    _ = c1 * c2 * dimpi * Q * κ * (G1 * Pp) / (w ^ (2 * r ^ 2 + r) * H) := by
        field_simp
    _ = _ := by
        rw [hgp]; field_simp

/- English proof (translation)
Rewrite using `[hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity)]`. Establish `h : ∀ N : ℕ, ∑ n ∈ range N, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) = 1 - 1 / ((N : ℝ) + 1)`. Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => simp`.

Consider the case `succ N ih`. Rewrite using `[sum_range_succ, ih]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[h]`. Use `(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub 1` as an intermediate fact. Simplify using `using this`.
-/
theorem s5a4_tele : HasSum (fun n : ℕ => 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity)]
  have h : ∀ N : ℕ, ∑ n ∈ range N, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) = 1 - 1 / ((N : ℝ) + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ, ih]; push_cast; field_simp; ring
  simp_rw [h]
  have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub 1
  simpa using this

/- English proof (translation)
Establish `hr0 : (0 : ℝ) ≤ ((n : ℝ) + 2)⁻¹` using `by positivity`. Establish `hr1 : ((n : ℝ) + 2)⁻¹ < 1`. Apply `inv_lt_one_of_one_lt₀` to reduce the goal to its premises. Combine the linear relations using `[(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]`. Establish `h` using `(hasSum_geometric_of_lt_one hr0 hr1).mul_left ((((n : ℝ) + 2)⁻¹) ^ 2)`.

Establish `e1 : (fun i : ℕ => (((n : ℝ) + 2) ^ (i + 2))⁻¹) = fun i : ℕ => (((n : ℝ) + 2)⁻¹) ^ 2 * (((n : ℝ) + 2)⁻¹) ^ i`. Use extensionality with `i`. Rewrite using `[← pow_add, inv_pow, add_comm 2 i]`. Establish `e2 : 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) = (((n : ℝ) + 2)⁻¹) ^ 2 * (1 - ((n : ℝ) + 2)⁻¹)⁻¹`. Establish `h1 : ((n : ℝ) + 2) ≠ 0` using `by positivity`.

Establish `h2 : ((n : ℝ) + 1) ≠ 0` using `by positivity`. Establish `h3 : (1 - ((n : ℝ) + 2)⁻¹) = ((n : ℝ) + 1) / ((n : ℝ) + 2)` using `by field_simp; ring`. Rewrite using `[h3]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, e2]`.

Conclude with `h`.
-/
theorem s5a4_geo (n : ℕ) : HasSum (fun i : ℕ => (((n : ℝ) + 2) ^ (i + 2))⁻¹)
    (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
  have hr0 : (0 : ℝ) ≤ ((n : ℝ) + 2)⁻¹ := by positivity
  have hr1 : ((n : ℝ) + 2)⁻¹ < 1 := by
    apply inv_lt_one_of_one_lt₀; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left ((((n : ℝ) + 2)⁻¹) ^ 2)
  have e1 : (fun i : ℕ => (((n : ℝ) + 2) ^ (i + 2))⁻¹) =
      fun i : ℕ => (((n : ℝ) + 2)⁻¹) ^ 2 * (((n : ℝ) + 2)⁻¹) ^ i := by
    ext i; rw [← pow_add, inv_pow, add_comm 2 i]
  have e2 : 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) =
      (((n : ℝ) + 2)⁻¹) ^ 2 * (1 - ((n : ℝ) + 2)⁻¹)⁻¹ := by
    have h1 : ((n : ℝ) + 2) ≠ 0 := by positivity
    have h2 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h3 : (1 - ((n : ℝ) + 2)⁻¹) = ((n : ℝ) + 1) / ((n : ℝ) + 2) := by field_simp; ring
    rw [h3]; field_simp
  rw [e1, e2]; exact h

/- English proof (translation)
Unfold `TailSum`. Set `g : ℕ × ℕ → ℝ` to `fun p => (((p.1 : ℝ) + 2) ^ (p.2 + 2))⁻¹`. Establish `hg0 : 0 ≤ g` using `fun p => by simp only [g, Pi.zero_apply]; positivity`. Establish `hs : Summable g`. Rewrite using `[summable_prod_of_nonneg hg0]`.

Use `⟨fun n => (s5a4_geo n).summable, ?_⟩` and prove the remaining obligations. Establish `: (fun n : ℕ => ∑' i : ℕ, g (n, i)) = fun n : ℕ => 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))`. Use extensionality with `n`. Conclude with `(s5a4_geo n).tsum_eq`. Rewrite using `[this]`.

Conclude with `s5a4_tele.summable`. Establish `hv : HasSum g 1`. Establish `h1` using `hs.hasSum.prod_fiberwise (fun n => s5a4_geo n)`. Establish `h2` using `hs.hasSum`. Rewrite `h2` using `[h1.unique s5a4_tele]`. Then use the resulting hypothesis.

Establish `hsw : HasSum (fun p : ℕ × ℕ => g p.swap) 1` using `(Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hv`. Use `hsw.prod_fiberwise (fun i => ?_)` and prove the remaining obligations. Establish `hsi : Summable (fun n : ℕ => (((n : ℝ) + 2) ^ (i + 2))⁻¹)` using `hsw.summable.prod_factor i`. Establish `hsi' : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ (i + 2))⁻¹)`. Rewrite using `[← summable_nat_add_iff 1]`.

Establish `e : (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) + 1) ^ (i + 2))⁻¹) = fun n : ℕ => (((n : ℝ) + 2) ^ (i + 2))⁻¹`. Use extensionality with `n`. Use `push_cast`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `hsi`. Use `(hasSum_nat_add_iff' 1).mpr hsi'.hasSum` as an intermediate fact. Simplify using `only [range_one, sum_singleton, Nat.cast_zero, zero_add, one_pow, inv_one] at this`. Establish `e : (fun n : ℕ => g (Prod.swap (i, n))) = fun n : ℕ => ((((n + 1 : ℕ) : ℝ) + 1) ^ (i + 2))⁻¹`.

Use extensionality with `n`. Simplify using `only [g, Prod.swap]`. Use `push_cast`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `this`.
-/
theorem tail_sum_bound : TailSum := by
  unfold TailSum
  let g : ℕ × ℕ → ℝ := fun p => (((p.1 : ℝ) + 2) ^ (p.2 + 2))⁻¹
  have hg0 : 0 ≤ g := fun p => by simp only [g, Pi.zero_apply]; positivity
  have hs : Summable g := by
    rw [summable_prod_of_nonneg hg0]
    refine ⟨fun n => (s5a4_geo n).summable, ?_⟩
    have : (fun n : ℕ => ∑' i : ℕ, g (n, i)) = fun n : ℕ => 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
      ext n; exact (s5a4_geo n).tsum_eq
    rw [this]; exact s5a4_tele.summable
  have hv : HasSum g 1 := by
    have h1 := hs.hasSum.prod_fiberwise (fun n => s5a4_geo n)
    have h2 := hs.hasSum
    rwa [h1.unique s5a4_tele] at h2
  have hsw : HasSum (fun p : ℕ × ℕ => g p.swap) 1 := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hv
  refine hsw.prod_fiberwise (fun i => ?_)
  have hsi : Summable (fun n : ℕ => (((n : ℝ) + 2) ^ (i + 2))⁻¹) := hsw.summable.prod_factor i
  have hsi' : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ (i + 2))⁻¹) := by
    rw [← summable_nat_add_iff 1]
    have e : (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) + 1) ^ (i + 2))⁻¹) =
        fun n : ℕ => (((n : ℝ) + 2) ^ (i + 2))⁻¹ := by
      ext n; push_cast; congr 2; ring
    rw [e]; exact hsi
  have := (hasSum_nat_add_iff' 1).mpr hsi'.hasSum
  simp only [range_one, sum_singleton, Nat.cast_zero, zero_add, one_pow, inv_one] at this
  have e : (fun n : ℕ => g (Prod.swap (i, n))) = fun n : ℕ => ((((n + 1 : ℕ) : ℝ) + 1) ^ (i + 2))⁻¹ := by
    ext n; simp only [g, Prod.swap]; push_cast; congr 2; ring
  rw [e]; exact this

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Conclude with `hx (funext fun i => by_contra fun hi => h ⟨i, hi⟩)`. Establish `e : {y : Fin (M + 1) → K // ∑ i, x i * y i = c} ≃ (Fin M → K)` using `{ toFun := fun y j => y.1 (i0.succAbove j) invFun := fun w => ⟨Fin.insertNth i0 ((c - ∑ j, x (i0.succAbove j) * w j) / x i0) w, by`. Rewrite using `[Fin.sum_univ_succAbove _ i0]`.

Simplify using `only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]`. Clear the denominators using the available nonvanishing facts. Use the proof step `ring⟩`. Use `left_inv := by`. Introduce and unpack `⟨y, hy⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[Fin.insertNth_eq_iff]`. Use `⟨?_, rfl⟩` and prove the remaining obligations. Rewrite `hy` using `[Fin.sum_univ_succAbove _ i0]`.

Rewrite using `[← hy]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `right_inv := by`. Introduce `w`.

Use extensionality with `j`. Simplify using `}`. Rewrite using `[Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]`.
-/
theorem s5a4_fiber_card {K : Type} [Field K] [Fintype K] (M : ℕ) (x : Fin (M + 1) → K)
    (hx : x ≠ 0) (c : K) :
    Nat.card {y : Fin (M + 1) → K // ∑ i, x i * y i = c} = Fintype.card K ^ M := by
  obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := by
    by_contra h; exact hx (funext fun i => by_contra fun hi => h ⟨i, hi⟩)
  have e : {y : Fin (M + 1) → K // ∑ i, x i * y i = c} ≃ (Fin M → K) :=
    { toFun := fun y j => y.1 (i0.succAbove j)
      invFun := fun w => ⟨Fin.insertNth i0 ((c - ∑ j, x (i0.succAbove j) * w j) / x i0) w, by
        rw [Fin.sum_univ_succAbove _ i0]
        simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
        field_simp; ring⟩
      left_inv := by
        rintro ⟨y, hy⟩
        apply Subtype.ext
        simp only
        rw [Fin.insertNth_eq_iff]
        refine ⟨?_, rfl⟩
        rw [Fin.sum_univ_succAbove _ i0] at hy
        rw [← hy]; field_simp; ring
      right_inv := by
        intro w; ext j; simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]

/- English proof (translation)
Introduce `K _ _ M`. Rewrite using `[Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun (a b : Fin (M + 1) → K) => ∑ i, a i * b i = 1)), Nat.card_sigma]`. Establish `h0 : Nat.card {b : Fin (M + 1) → K // ∑ i, (0 : Fin (M + 1) → K) i * b i = 1} = 0`. Establish `: IsEmpty {b : Fin (M + 1) → K // ∑ i, (0 : Fin (M + 1) → K) i * b i = 1}` using `⟨fun b => by have := b.2; simp at this⟩`. Conclude with `Nat.card_of_isEmpty`.

Rewrite using `[← Finset.sum_erase (f := fun a : Fin (M + 1) → K => Nat.card {b : Fin (M + 1) → K // ∑ i, a i * b i = 1}) Finset.univ h0]`. Rewrite using `[Finset.sum_congr rfl (fun x hx => s5a4_fiber_card M x (Finset.ne_of_mem_erase hx) 1)]`. Rewrite using `[Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul, mul_comm]`.
-/
theorem split_sphere_count : SplitSphereCount := by
  intro K _ _ M
  classical
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun (a b : Fin (M + 1) → K) => ∑ i, a i * b i = 1)), Nat.card_sigma]
  have h0 : Nat.card {b : Fin (M + 1) → K // ∑ i, (0 : Fin (M + 1) → K) i * b i = 1} = 0 := by
    have : IsEmpty {b : Fin (M + 1) → K // ∑ i, (0 : Fin (M + 1) → K) i * b i = 1} :=
      ⟨fun b => by have := b.2; simp at this⟩
    exact Nat.card_of_isEmpty
  rw [← Finset.sum_erase (f := fun a : Fin (M + 1) → K => Nat.card {b : Fin (M + 1) → K // ∑ i, a i * b i = 1}) Finset.univ h0]
  rw [Finset.sum_congr rfl (fun x hx => s5a4_fiber_card M x (Finset.ne_of_mem_erase hx) 1)]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, smul_eq_mul, mul_comm]

/- English proof (translation)
Rewrite using `[← Finset.sum_fiberwise (s := Finset.univ) (g := f) (f := fun a => F (f a))]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (g := fun _ => F k) (fun a ha => by rw [(Finset.mem_filter.mp ha).2]), Finset.sum_const, Nat.card_eq_fintype_card, Fintype.card_subtype, nsmul_eq_mul]`.
-/
theorem s5a4_sum_fiber {α κ : Type} [Fintype α] [Fintype κ] (f : α → κ) (F : κ → ℤ) :
    ∑ a, F (f a) = ∑ k, (Nat.card {a // f a = k} : ℤ) * F k := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := f) (f := fun a => F (f a))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_congr rfl (g := fun _ => F k) (fun a ha => by rw [(Finset.mem_filter.mp ha).2]),
    Finset.sum_const, Nat.card_eq_fintype_card, Fintype.card_subtype, nsmul_eq_mul]

/- English proof (translation)
Use `s5a4_sum_fiber f (fun _ => 1)` as an intermediate fact. Simplify using `at this`. Rewrite using `[← this]`.
-/
theorem s5a4_card_fibers {α κ : Type} [Fintype α] [Fintype κ] (f : α → κ) :
    ∑ k, (Nat.card {a // f a = k} : ℤ) = Fintype.card α := by
  have := s5a4_sum_fiber f (fun _ => 1)
  simp at this
  rw [← this]

/- English proof (translation)
Establish `heq : ∀ d' : K, d' ≠ 0 → Nat.card {y : L // Algebra.norm K y = d'} = Nat.card {y : L // Algebra.norm K y = d}`. Introduce `d' hd'`. Take `⟨u, hu⟩` from `FiniteField.norm_surjective K L (d / d')`. Establish `hu0 : u ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hu` using `[Algebra.norm_eq_zero_iff.mpr rfl]`. Conclude with `div_ne_zero hd hd' hu.symm`. Use `Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulLeft₀ u hu0) (fun y => ?_))` and prove the remaining obligations. Use `show Algebra.norm K y = d' ↔ Algebra.norm K (u * y) = d`. Rewrite using `[map_mul, hu]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h]`. Clear the denominators using the available nonvanishing facts. Introduce `h`.

Clear denominators, using `at h` for the nonvanishing conditions. Conclude with `h`. Establish `h0 : Nat.card {y : L // Algebra.norm K y = (0 : K)} = 1`. Rewrite using `[Nat.card_eq_one_iff_unique]`. Use `⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨0, Algebra.norm_eq_zero_iff.mpr rfl⟩⟩⟩` and prove the remaining obligations.

Rewrite using `[Algebra.norm_eq_zero_iff.mp a.2, Algebra.norm_eq_zero_iff.mp b.2]`. Establish `htot` using `s5a4_card_fibers (fun y : L => Algebra.norm K y)`. Rewrite `htot` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K)), h0, Finset.sum_congr rfl (fun k hk => by rw [heq k (Finset.ne_of_mem_erase hk)]), Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Module.card_eq_pow_finrank (K := K) (V := L), h2]`. Establish `hq : 1 < Fintype.card K` using `Fintype.one_lt_card`. Use `set q := Fintype.card K`.

Use `set n := Nat.card {y : L // Algebra.norm K y = d}`. Rewrite `htot` using `[nsmul_eq_mul]`. Move the coercions through the operations in `[Nat.cast_sub hq.le] at htot`. Establish `hq' : ((q : ℤ) - 1) ≠ 0`. Establish `: (1 : ℤ) < q` using `by exact_mod_cast hq`.

Use linear arithmetic over natural numbers and integers. Apply `mul_left_cancel₀ hq'` to reduce the goal to its premises. Take the linear combination `htot`.
-/
theorem s5a4_norm_fiber {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
    (h2 : finrank K L = 2) (d : K) (hd : d ≠ 0) :
    (Nat.card {y : L // Algebra.norm K y = d} : ℤ) = Fintype.card K + 1 := by
  classical
  have heq : ∀ d' : K, d' ≠ 0 →
      Nat.card {y : L // Algebra.norm K y = d'} = Nat.card {y : L // Algebra.norm K y = d} := by
    intro d' hd'
    obtain ⟨u, hu⟩ := FiniteField.norm_surjective K L (d / d')
    have hu0 : u ≠ 0 := by
      rintro rfl; rw [Algebra.norm_eq_zero_iff.mpr rfl] at hu; exact div_ne_zero hd hd' hu.symm
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulLeft₀ u hu0) (fun y => ?_))
    show Algebra.norm K y = d' ↔ Algebra.norm K (u * y) = d
    rw [map_mul, hu]
    constructor
    · intro h; rw [h]; field_simp
    · intro h; field_simp at h; exact h
  have h0 : Nat.card {y : L // Algebra.norm K y = (0 : K)} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨0, Algebra.norm_eq_zero_iff.mpr rfl⟩⟩⟩
    rw [Algebra.norm_eq_zero_iff.mp a.2, Algebra.norm_eq_zero_iff.mp b.2]
  have htot := s5a4_card_fibers (fun y : L => Algebra.norm K y)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K)), h0,
    Finset.sum_congr rfl (fun k hk => by rw [heq k (Finset.ne_of_mem_erase hk)]),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Module.card_eq_pow_finrank (K := K) (V := L), h2] at htot
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  set q := Fintype.card K
  set n := Nat.card {y : L // Algebra.norm K y = d}
  rw [nsmul_eq_mul] at htot
  push_cast [Nat.cast_sub hq.le] at htot
  have hq' : ((q : ℤ) - 1) ≠ 0 := by
    have : (1 : ℤ) < q := by exact_mod_cast hq
    omega
  apply mul_left_cancel₀ hq'
  linear_combination htot

/- English proof (translation)
Set `A : K → ℤ` to `fun c => (Nat.card {x : Fin M → L // ∑ i, Algebra.norm K (x i) = c} : ℤ)`. Establish `e1 : {x : Fin (M + 1) → L // ∑ i, Algebra.norm K (x i) = c} ≃ {p : L × (Fin M → L) // ∑ i, Algebra.norm K (p.2 i) = c - Algebra.norm K p.1}` using `Equiv.subtypeEquiv (Fin.consEquiv (fun _ => L)).symm (fun x => by`. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.consEquiv, Equiv.coe_fn_symm_mk, Fin.tail]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite using `[← h]`. Expand and normalize the polynomial expressions, which then agree. Introduce `h`. Rewrite using `[h]`.

Use the proof step `ring)`. Establish `s1 : (Nat.card {x : Fin (M + 1) → L // ∑ i, Algebra.norm K (x i) = c} : ℤ) = ∑ y : L, A (c - Algebra.norm K y)`. Rewrite using `[Nat.card_congr e1, Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun (a : L) (b : Fin M → L) => ∑ i, Algebra.norm K (b i) = c - Algebra.norm K a)), Nat.card_sigma]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `s2` using `s5a4_sum_fiber (fun y : L => Algebra.norm K y) (fun d => A (c - d))`. Establish `h0 : Nat.card {y : L // Algebra.norm K y = (0 : K)} = 1`. Rewrite using `[Nat.card_eq_one_iff_unique]`. Use `⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨0, Algebra.norm_eq_zero_iff.mpr rfl⟩⟩⟩` and prove the remaining obligations. Rewrite using `[Algebra.norm_eq_zero_iff.mp a.2, Algebra.norm_eq_zero_iff.mp b.2]`.

Establish `s3 : ∑ d : K, A (c - d) = (Fintype.card K : ℤ) ^ (2 * M)`. Establish `hc` using `Equiv.sum_comp (Equiv.subLeft c) A`. Simplify using `only [Equiv.subLeft_apply] at hc`. Rewrite using `[hc]`. Use `s5a4_card_fibers (fun x : Fin M → L => ∑ i, Algebra.norm K (x i))` as an intermediate fact.

Rewrite using `[this, Fintype.card_fun, Fintype.card_fin, Module.card_eq_pow_finrank (K := K) (V := L), h2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[s1, s2, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K)), h0, Finset.sum_congr rfl (fun k hk => by rw [s5a4_norm_fiber h2 k (Finset.ne_of_mem_erase hk)]), ← Finset.mul_sum]`. Rewrite `s3` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K))]`.

Simplify using `only [sub_zero] at s3 ⊢`. Establish `: ∑ x ∈ Finset.univ.erase (0 : K), A (c - x) = (Fintype.card K : ℤ) ^ (2 * M) - A c`. Take the linear combination `s3`. Rewrite using `[this]`. Simplify using `[A]`.
-/
theorem s5a4_herm_rec {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
    (h2 : finrank K L = 2) (M : ℕ) (c : K) :
    (Nat.card {x : Fin (M + 1) → L // ∑ i, Algebra.norm K (x i) = c} : ℤ) =
      (Nat.card {x : Fin M → L // ∑ i, Algebra.norm K (x i) = c} : ℤ) +
      ((Fintype.card K : ℤ) + 1) * ((Fintype.card K : ℤ) ^ (2 * M) -
        (Nat.card {x : Fin M → L // ∑ i, Algebra.norm K (x i) = c} : ℤ)) := by
  classical
  let A : K → ℤ := fun c => (Nat.card {x : Fin M → L // ∑ i, Algebra.norm K (x i) = c} : ℤ)
  have e1 : {x : Fin (M + 1) → L // ∑ i, Algebra.norm K (x i) = c} ≃
      {p : L × (Fin M → L) // ∑ i, Algebra.norm K (p.2 i) = c - Algebra.norm K p.1} :=
    Equiv.subtypeEquiv (Fin.consEquiv (fun _ => L)).symm (fun x => by
      rw [Fin.sum_univ_succ]
      simp only [Fin.consEquiv, Equiv.coe_fn_symm_mk, Fin.tail]
      constructor
      · intro h; rw [← h]; ring
      · intro h; rw [h]; ring)
  have s1 : (Nat.card {x : Fin (M + 1) → L // ∑ i, Algebra.norm K (x i) = c} : ℤ) =
      ∑ y : L, A (c - Algebra.norm K y) := by
    rw [Nat.card_congr e1, Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun (a : L) (b : Fin M → L) => ∑ i, Algebra.norm K (b i) = c - Algebra.norm K a)),
      Nat.card_sigma]
    push_cast; rfl
  have s2 := s5a4_sum_fiber (fun y : L => Algebra.norm K y) (fun d => A (c - d))
  have h0 : Nat.card {y : L // Algebra.norm K y = (0 : K)} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨0, Algebra.norm_eq_zero_iff.mpr rfl⟩⟩⟩
    rw [Algebra.norm_eq_zero_iff.mp a.2, Algebra.norm_eq_zero_iff.mp b.2]
  have s3 : ∑ d : K, A (c - d) = (Fintype.card K : ℤ) ^ (2 * M) := by
    have hc := Equiv.sum_comp (Equiv.subLeft c) A
    simp only [Equiv.subLeft_apply] at hc
    rw [hc]
    have := s5a4_card_fibers (fun x : Fin M → L => ∑ i, Algebra.norm K (x i))
    rw [this, Fintype.card_fun, Fintype.card_fin, Module.card_eq_pow_finrank (K := K) (V := L), h2]
    push_cast; ring
  rw [s1, s2, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K)), h0,
    Finset.sum_congr rfl (fun k hk => by rw [s5a4_norm_fiber h2 k (Finset.ne_of_mem_erase hk)]),
    ← Finset.mul_sum]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K))] at s3
  simp only [sub_zero] at s3 ⊢
  have : ∑ x ∈ Finset.univ.erase (0 : K), A (c - x) = (Fintype.card K : ℤ) ^ (2 * M) - A c := by
    linear_combination s3
  rw [this]; simp [A]

/- English proof (translation)
Introduce `K L _ _ _ _ _ h2 M c hc`. Proceed by induction on `M with`. Consider the case `zero`. Rewrite using `[s5a4_herm_rec h2 0 c]`. Establish `: IsEmpty {x : Fin 0 → L // ∑ i, Algebra.norm K (x i) = c}` using `⟨fun x => by have := x.2; simp at this; exact hc this.symm⟩`.

Rewrite using `[Nat.card_of_isEmpty]`. Simplify using the standard rewrite rules. Consider the case `succ M ih`. Rewrite using `[s5a4_herm_rec h2 (M + 1) c, ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermitian_sphere_count : HermSphereCount := by
  intro K L _ _ _ _ _ h2 M c hc
  induction M with
  | zero =>
    rw [s5a4_herm_rec h2 0 c]
    have : IsEmpty {x : Fin 0 → L // ∑ i, Algebra.norm K (x i) = c} :=
      ⟨fun x => by have := x.2; simp at this; exact hc this.symm⟩
    rw [Nat.card_of_isEmpty]; simp
  | succ M ih =>
    rw [s5a4_herm_rec h2 (M + 1) c, ih]; ring

set_option backward.isDefEq.respectTransparency false in
open NumberField.Units in
/- English proof (translation)
Distinguish the cases in `hc : 2 < orderOf x`. It suffices to derive a contradiction. Rewrite `hc` using `[← orderOf_units, ← orderOf_submonoid]`. Establish `h0` using `NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc (IsPrimitiveRoot.orderOf ((x : 𝓞 F) : F))`. Take `⟨w0⟩ : Nonempty (InfinitePlace F)` from `inferInstance`.

Use `haveI : Nonempty {w : InfinitePlace F // w.IsReal} := ⟨⟨w0, hr w0⟩⟩`. Rewrite `h0` using `[InfinitePlace.nrRealPlaces]`. Conclude with `((@Fintype.card_eq_zero_iff _ (_)).1 h0).false ⟨w0, hr w0⟩`. Establish `hc' : orderOf x ≤ 2` using `not_lt.mp hc interval_cases hi : orderOf x`. Conclude with `absurd ((CommGroup.mem_torsion x).1 hx) (orderOf_eq_zero_iff.mp hi)`.

Conclude with `Or.inl (orderOf_eq_one_iff.1 hi)`. Use `right`. Rewrite `hi` using `[← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)]`. Simplify using `[← Units.val_inj, Units.val_neg, Units.val_one, hi]`.
-/
theorem s5a4_torsion_real {F : Type} [Field F] [NumberField F]
    (hr : ∀ w : InfinitePlace F, w.IsReal) (x : (𝓞 F)ˣ) (hx : x ∈ torsion F) :
    x = 1 ∨ x = -1 := by
  by_cases hc : 2 < orderOf x
  · exfalso
    rw [← orderOf_units, ← orderOf_submonoid] at hc
    have h0 := NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc
      (IsPrimitiveRoot.orderOf ((x : 𝓞 F) : F))
    obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
    haveI : Nonempty {w : InfinitePlace F // w.IsReal} := ⟨⟨w0, hr w0⟩⟩
    rw [InfinitePlace.nrRealPlaces] at h0
    exact ((@Fintype.card_eq_zero_iff _ (_)).1 h0).false ⟨w0, hr w0⟩
  · have hc' : orderOf x ≤ 2 := not_lt.mp hc
    interval_cases hi : orderOf x
    · exact absurd ((CommGroup.mem_torsion x).1 hx) (orderOf_eq_zero_iff.mp hi)
    · exact Or.inl (orderOf_eq_one_iff.1 hi)
    · right
      rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
      simp [← Units.val_inj, Units.val_neg, Units.val_one, hi]

open NumberField.Units in
/- English proof (translation)
Introduce `F _ _ hr`. Use `set S : Subgroup (𝓞 F)ˣ := (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ).range with hS`. Take `⟨θ, hθd⟩ : ∃ θ : (𝓞 F)ˣ →* Multiplicative (Fin (rank F) → ZMod 2), ∀ x, θ x = Multiplicative.ofAdd (fun i => (((basisModTorsion F).repr (Additive.ofMul (x : (𝓞 F)ˣ ⧸ torsion F)) i : ℤ) : ZMod 2))` from `⟨{ toFun := fun x => Multiplicative.ofAdd (fun i => (((basisModTorsion F).repr (Additive.ofMul (x : (𝓞 F)ˣ ⧸ torsion F)) i : ℤ) : ZMod 2)) map_one' := by`. Simplify using `only [QuotientGroup.mk_one, ofMul_one, map_zero, Finsupp.coe_zero, Pi.zero_apply, Int.cast_zero]`. Both sides reduce to the same expression.

Use the proof step `map_mul' := by`. Introduce `x y`. Simplify using `only [QuotientGroup.mk_mul, ofMul_mul, map_add, Finsupp.coe_add, Pi.add_apply, Int.cast_add]`. Use `rfl }, fun _ => rfl⟩`. Establish `hθ : ∀ (x ζ : (𝓞 F)ˣ) (e : Fin (rank F) → ℤ), ζ ∈ torsion F → x = ζ * ∏ i, (fundSystem F i) ^ (e i) → θ x = Multiplicative.ofAdd (fun i => ((e i : ℤ) : ZMod 2))`.

Introduce `x ζ e hζ hx`. Use `fun_eq_repr F hζ hx` as an intermediate fact. Rewrite using `[hθd, ← this]`. Establish `hsurj : Function.Surjective θ`. Introduce `v`.

Use `⟨1 * ∏ i, (fundSystem F i) ^ (((Multiplicative.toAdd v i).val : ℕ) : ℤ), ?_⟩` and prove the remaining obligations. Rewrite using `[hθ _ 1 _ (one_mem _) rfl]`. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Establish `hsq : ∀ a : Multiplicative (Fin (rank F) → ZMod 2), a ^ 2 = 1`. Introduce `a`. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Rewrite using `[sq]`.

Use `show Multiplicative.toAdd a i + Multiplicative.toAdd a i = 0`. Conclude with `CharTwo.add_self_eq_zero _`. Establish `hker : θ.ker = S ⊔ torsion F`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`.

Take `⟨⟨ζ, e⟩, hxe, _⟩` from `exist_unique_eq_mul_prod F x`. Simplify using `only at hxe`. Rewrite `hx` using `[MonoidHom.mem_ker, hθ x ζ e ζ.2 hxe]`. Establish `h2 : ∀ i, (2 : ℤ) ∣ e i`. Introduce `i`.

Use `congrFun (congrArg Multiplicative.toAdd hx) i` as an intermediate fact. Conclude with `(ZMod.intCast_zmod_eq_zero_iff_dvd (e i) 2).mp this`. Use `choose e' he' using h2`. Establish `: x = (∏ i, (fundSystem F i) ^ (e' i)) ^ 2 * ζ`. Rewrite using `[hxe, mul_comm, ← Finset.prod_pow]`.

Use `congr 1`. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[he' i, mul_comm, zpow_mul]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `Subgroup.mul_mem_sup ⟨_, rfl⟩ ζ.2`. Apply `sup_le` to reduce the goal to its premises. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[MonoidHom.mem_ker, powMonoidHom_apply, map_pow, hsq]`. Introduce `ζ hζ`.

Rewrite using `[MonoidHom.mem_ker, hθ ζ ζ (fun _ => 0) hζ (by simp)]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Establish `hST : S ⊓ torsion F = ⊥`. Rewrite using `[eq_bot_iff]`.

Introduce and unpack `x ⟨⟨y, rfl⟩, hx⟩`. Establish `hx' : y ^ 2 ∈ torsion F` using `hx`. Establish `hy : y ∈ torsion F`. Rewrite `hx'`, the goal using `[torsion, CommGroup.mem_torsion]`. Conclude with `hx'.of_pow (by norm_num)`.

Use `show y ^ 2 ∈ (⊥ : Subgroup (𝓞 F)ˣ)`. Rewrite using `[Subgroup.mem_bot]`. Apply the tactic sequence `rcases s5a4_torsion_real hr y hy with h | h <;> simp [h]`. Establish `hT : Nat.card (torsion F) = 2`. Rewrite using `[Nat.card_eq_two_iff]`.

Use `⟨1, ⟨-1, neg_one_mem_torsion⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Establish `h1 : (1 : (𝓞 F)ˣ) = -1` using `congrArg Subtype.val h`. Establish `h2 : ((1 : 𝓞 F) : F) = -1`. Use `congrArg (fun u : (𝓞 F)ˣ => ((u : 𝓞 F) : F)) h1` as an intermediate fact.

Simplify using `using this`. Evaluate the numerical expressions using `at h2`. Apply `Set.eq_univ_of_forall` to reduce the goal to its premises. Introduce `x`. Break down `s5a4_torsion_real hr x.1 x.2 with h | h` into its components or cases.

Use `left`. Conclude with `Subtype.ext h`. Use `right`. Conclude with `Subtype.ext h`. Establish `hrank : rank F + 1 = finrank ℚ F`.

Establish `h1` using `InfinitePlace.card_add_two_mul_card_eq_rank F`. Establish `h2` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F`. Establish `h3 : InfinitePlace.nrComplexPlaces F = 0`. Rewrite using `[InfinitePlace.nrComplexPlaces, Fintype.card_eq_zero_iff]`. Conclude with `⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr w.2) (hr w.1)⟩`.

Establish `h4 : 0 < Fintype.card (InfinitePlace F)` using `Fintype.card_pos`. Rewrite using `[rank]`. Use linear arithmetic over natural numbers and integers. Use `show S.index = _`. Rewrite using `[← Subgroup.relIndex_mul_index (le_sup_left : S ≤ S ⊔ torsion F), Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right, hST, Subgroup.relIndex_bot_left, hT, ← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, …`.
-/
theorem units_square_index : UnitsSquareIndex := by
  intro F _ _ hr
  classical
  set S : Subgroup (𝓞 F)ˣ := (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ).range with hS
  obtain ⟨θ, hθd⟩ : ∃ θ : (𝓞 F)ˣ →* Multiplicative (Fin (rank F) → ZMod 2), ∀ x, θ x =
      Multiplicative.ofAdd (fun i =>
        (((basisModTorsion F).repr (Additive.ofMul (x : (𝓞 F)ˣ ⧸ torsion F)) i : ℤ) : ZMod 2)) :=
   ⟨{ toFun := fun x => Multiplicative.ofAdd (fun i =>
        (((basisModTorsion F).repr (Additive.ofMul (x : (𝓞 F)ˣ ⧸ torsion F)) i : ℤ) : ZMod 2))
      map_one' := by
        simp only [QuotientGroup.mk_one, ofMul_one, map_zero, Finsupp.coe_zero, Pi.zero_apply,
          Int.cast_zero]; rfl
      map_mul' := by
        intro x y
        simp only [QuotientGroup.mk_mul, ofMul_mul, map_add, Finsupp.coe_add, Pi.add_apply,
          Int.cast_add]; rfl }, fun _ => rfl⟩
  have hθ : ∀ (x ζ : (𝓞 F)ˣ) (e : Fin (rank F) → ℤ), ζ ∈ torsion F →
      x = ζ * ∏ i, (fundSystem F i) ^ (e i) →
      θ x = Multiplicative.ofAdd (fun i => ((e i : ℤ) : ZMod 2)) := by
    intro x ζ e hζ hx
    have := fun_eq_repr F hζ hx
    rw [hθd, ← this]
  have hsurj : Function.Surjective θ := by
    intro v
    refine ⟨1 * ∏ i, (fundSystem F i) ^ (((Multiplicative.toAdd v i).val : ℕ) : ℤ), ?_⟩
    rw [hθ _ 1 _ (one_mem _) rfl]
    apply Multiplicative.toAdd.injective
    funext i
    simp
  have hsq : ∀ a : Multiplicative (Fin (rank F) → ZMod 2), a ^ 2 = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    funext i
    rw [sq]
    show Multiplicative.toAdd a i + Multiplicative.toAdd a i = 0
    exact CharTwo.add_self_eq_zero _
  have hker : θ.ker = S ⊔ torsion F := by
    apply le_antisymm
    · intro x hx
      obtain ⟨⟨ζ, e⟩, hxe, _⟩ := exist_unique_eq_mul_prod F x
      simp only at hxe
      rw [MonoidHom.mem_ker, hθ x ζ e ζ.2 hxe] at hx
      have h2 : ∀ i, (2 : ℤ) ∣ e i := by
        intro i
        have := congrFun (congrArg Multiplicative.toAdd hx) i
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd (e i) 2).mp this
      choose e' he' using h2
      have : x = (∏ i, (fundSystem F i) ^ (e' i)) ^ 2 * ζ := by
        rw [hxe, mul_comm, ← Finset.prod_pow]
        congr 1
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [he' i, mul_comm, zpow_mul]; rfl
      rw [this]
      exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ζ.2
    · apply sup_le
      · rintro _ ⟨y, rfl⟩
        rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow, hsq]
      · intro ζ hζ
        rw [MonoidHom.mem_ker, hθ ζ ζ (fun _ => 0) hζ (by simp)]
        simp; rfl
  have hST : S ⊓ torsion F = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨y, rfl⟩, hx⟩
    have hx' : y ^ 2 ∈ torsion F := hx
    have hy : y ∈ torsion F := by
      rw [torsion, CommGroup.mem_torsion] at hx' ⊢
      exact hx'.of_pow (by norm_num)
    show y ^ 2 ∈ (⊥ : Subgroup (𝓞 F)ˣ)
    rw [Subgroup.mem_bot]
    rcases s5a4_torsion_real hr y hy with h | h <;> simp [h]
  have hT : Nat.card (torsion F) = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨1, ⟨-1, neg_one_mem_torsion⟩, ?_, ?_⟩
    · intro h
      have h1 : (1 : (𝓞 F)ˣ) = -1 := congrArg Subtype.val h
      have h2 : ((1 : 𝓞 F) : F) = -1 := by
        have := congrArg (fun u : (𝓞 F)ˣ => ((u : 𝓞 F) : F)) h1
        simpa using this
      norm_num at h2
    · apply Set.eq_univ_of_forall
      intro x
      rcases s5a4_torsion_real hr x.1 x.2 with h | h
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h
  have hrank : rank F + 1 = finrank ℚ F := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
    have h3 : InfinitePlace.nrComplexPlaces F = 0 := by
      rw [InfinitePlace.nrComplexPlaces, Fintype.card_eq_zero_iff]
      exact ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr w.2) (hr w.1)⟩
    have h4 : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
    rw [rank]; omega
  show S.index = _
  rw [← Subgroup.relIndex_mul_index (le_sup_left : S ≤ S ⊔ torsion F), Subgroup.relIndex_sup_left,
    ← Subgroup.inf_relIndex_right, hST, Subgroup.relIndex_bot_left, hT, ← hker, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd,
    Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin, ← hrank, pow_succ,
    mul_comm]

/- English proof (translation)
Introduce `E _ _ cc α α' rr hcc hrr K H hH hK`. Take `⟨d, hd, hden⟩` from `cc.isFractional`. Establish `hd0 : (d : E) ≠ 0`. Use `nonZeroDivisors.ne_zero hd` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Set `φ : 𝓞 E →ₗ[𝓞 E] E` to `LinearMap.toSpanSingleton (𝓞 E) E (d : E)⁻¹`. Establish `hφ : ∀ a : 𝓞 E, φ a = (a : E) * (d : E)⁻¹` using `fun a => by`. Simplify using `[φ, LinearMap.toSpanSingleton_apply, Algebra.smul_def]`. Establish `hφinj : Function.Injective φ.toAddMonoidHom`. Introduce `a b hab`.

Establish `: (a : E) * (d : E)⁻¹ = (b : E) * (d : E)⁻¹` using `by rw [← hφ, ← hφ]; exact hab`. Conclude with `RingOfIntegers.ext (mul_right_cancel₀ (inv_ne_zero hd0) this)`. Set `KS : Submodule (𝓞 E) E` to `{ carrier := {x | IsInt (x * α) ∧ IsInt (x * α')} add_mem' := by`. Introduce and unpack `x y ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩ ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩`. Conclude with `⟨⟨a + b, by rw [add_mul, ← ha, ← hb]; simp⟩, ⟨a' + b', by rw [add_mul, ← ha', ← hb']; simp⟩⟩`.

Use the proof step `zero_mem' := ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c x ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩`. Conclude with `⟨⟨c * a, by rw [Algebra.smul_def, mul_assoc, ← ha]; simp⟩, ⟨c * a', by rw [Algebra.smul_def, mul_assoc, ← ha']; simp⟩⟩ }`. Set `A : Ideal (𝓞 E)` to `(cc : Submodule (𝓞 E) E).comap φ`.

Set `B : Ideal (𝓞 E)` to `((cc : Submodule (𝓞 E) E) ⊓ KS).comap φ`. Establish `hA : ∀ a : 𝓞 E, a ∈ A ↔ (a : E) * (d : E)⁻¹ ∈ cc` using `fun a => by`. Simplify using `only [A, Submodule.mem_comap, hφ, FractionalIdeal.mem_coe]`. Establish `hB : ∀ a : 𝓞 E, a ∈ B ↔ (a : E) * (d : E)⁻¹ ∈ cc ∧ IsInt ((a : E) * (d : E)⁻¹ * α) ∧ IsInt ((a : E) * (d : E)⁻¹ * α')` using `fun a => by`. Simplify using `only [B, Submodule.mem_comap, hφ, Submodule.mem_inf, FractionalIdeal.mem_coe]`.

Both sides reduce to the same expression. Establish `hlift : ∀ x ∈ cc, ∃ a : 𝓞 E, (a : E) * (d : E)⁻¹ = x`. Introduce `x hx`. Take `⟨a, ha⟩` from `hden x hx`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Establish `: (a : E) = (d : E) * x` using `by rw [Algebra.smul_def] at ha; exact ha`. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts. Establish `hBA : B ≤ A` using `fun a ha => (hA a).mpr ((hB a).mp ha).1`. Establish `hmul : B = A * rr`.

Apply `le_antisymm` to reduce the goal to its premises. Take `⟨C, hC⟩` from `Ideal.dvd_iff_le.mpr hBA`. Rewrite using `[hC]`. Apply `Ideal.mul_mono_right` to reduce the goal to its premises. Introduce `c hc`.

Rewrite using `[hrr]`. Introduce `x hx`. Take `⟨a, ha⟩` from `hlift x hx`. Establish `haA : a ∈ A` using `(hA a).mpr (by rw [ha]; exact hx)`. Establish `: a * c ∈ B` using `by rw [hC]; exact Ideal.mul_mem_mul haA hc`.

Take `⟨_, h1, h2⟩` from `(hB _).mp this`. Prove the components needed by the constructor for the conclusion. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Rewrite using `[← ha]`.

Expand and normalize the polynomial expressions, which then agree. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Rewrite using `[← ha]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Ideal.mul_le]`. Introduce `a ha c hc`. Establish `hx` using `(hA a).mp ha`. Take `⟨h1, h2⟩` from `(hrr c).mp hc _ hx`. Use `(hB _).mpr ⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `(hA _).mp (A.mul_mem_right c ha)`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hAne : A ≠ ⊥`. Introduce `h`. Apply `hcc` to reduce the goal to its premises.

Rewrite using `[FractionalIdeal.eq_zero_iff]`. Introduce `x hx`. Take `⟨a, ha⟩` from `hlift x hx`. Establish `haA : a ∈ A` using `(hA a).mpr (by rw [ha]; exact hx)`. Rewrite `haA` using `[h, Ideal.mem_bot]`.

Rewrite using `[← ha, haA]`. Simplify using the standard rewrite rules. Establish `hHm : H = A.toAddSubgroup.map φ.toAddMonoidHom`. Use extensionality with `x`. Rewrite using `[hH, AddSubgroup.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨a, ha⟩` from `hlift x hx`. Conclude with `⟨a, (hA a).mpr (by rw [ha]; exact hx), by rw [← ha]; exact hφ a⟩`. Introduce and unpack `⟨a, ha, rfl⟩`.

Use `(hA a).mp ha` as an intermediate fact. Rewrite `this` using `[← hφ]`. Conclude with `this`. Establish `hKm : K ⊓ H = B.toAddSubgroup.map φ.toAddMonoidHom`. Use extensionality with `x`.

Rewrite using `[AddSubgroup.mem_inf, hH, hK, AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hk, hx⟩`. Take `⟨a, ha⟩` from `hlift x hx`. Conclude with `⟨a, (hB a).mpr (by rw [ha]; exact ⟨hx, hk⟩), by rw [← ha]; exact hφ a⟩`.

Introduce and unpack `⟨a, ha, rfl⟩`. Use `(hB a).mp ha` as an intermediate fact. Rewrite `this` using `[← hφ]`. Conclude with `⟨this.2, this.1⟩`. Rewrite using `[← AddSubgroup.inf_relIndex_right, hKm, hHm, AddSubgroup.relIndex_map_map_of_injective _ _ hφinj]`.

Establish `h1` using `AddSubgroup.relIndex_mul_index (H := B.toAddSubgroup) (K := A.toAddSubgroup) hBA`. Rewrite `h1` using `[← Ideal.absNorm_eq_index, ← Ideal.absNorm_eq_index, hmul, map_mul, mul_comm]`. Conclude with `Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hAne)) (by rw [hmul]; exact h1)`.
-/
theorem radical_image_index : RadImageIndex := by
  intro E _ _ cc α α' rr hcc hrr K H hH hK
  obtain ⟨d, hd, hden⟩ := cc.isFractional
  have hd0 : (d : E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hd
    exact_mod_cast this
  let φ : 𝓞 E →ₗ[𝓞 E] E := LinearMap.toSpanSingleton (𝓞 E) E (d : E)⁻¹
  have hφ : ∀ a : 𝓞 E, φ a = (a : E) * (d : E)⁻¹ := fun a => by
    simp [φ, LinearMap.toSpanSingleton_apply, Algebra.smul_def]
  have hφinj : Function.Injective φ.toAddMonoidHom := by
    intro a b hab
    have : (a : E) * (d : E)⁻¹ = (b : E) * (d : E)⁻¹ := by rw [← hφ, ← hφ]; exact hab
    exact RingOfIntegers.ext (mul_right_cancel₀ (inv_ne_zero hd0) this)
  let KS : Submodule (𝓞 E) E :=
    { carrier := {x | IsInt (x * α) ∧ IsInt (x * α')}
      add_mem' := by
        rintro x y ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩ ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩
        exact ⟨⟨a + b, by rw [add_mul, ← ha, ← hb]; simp⟩, ⟨a' + b', by rw [add_mul, ← ha', ← hb']; simp⟩⟩
      zero_mem' := ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩
      smul_mem' := by
        rintro c x ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩
        exact ⟨⟨c * a, by rw [Algebra.smul_def, mul_assoc, ← ha]; simp⟩,
          ⟨c * a', by rw [Algebra.smul_def, mul_assoc, ← ha']; simp⟩⟩ }
  let A : Ideal (𝓞 E) := (cc : Submodule (𝓞 E) E).comap φ
  let B : Ideal (𝓞 E) := ((cc : Submodule (𝓞 E) E) ⊓ KS).comap φ
  have hA : ∀ a : 𝓞 E, a ∈ A ↔ (a : E) * (d : E)⁻¹ ∈ cc := fun a => by
    simp only [A, Submodule.mem_comap, hφ, FractionalIdeal.mem_coe]
  have hB : ∀ a : 𝓞 E, a ∈ B ↔ (a : E) * (d : E)⁻¹ ∈ cc ∧
      IsInt ((a : E) * (d : E)⁻¹ * α) ∧ IsInt ((a : E) * (d : E)⁻¹ * α') := fun a => by
    simp only [B, Submodule.mem_comap, hφ, Submodule.mem_inf, FractionalIdeal.mem_coe]; rfl
  have hlift : ∀ x ∈ cc, ∃ a : 𝓞 E, (a : E) * (d : E)⁻¹ = x := by
    intro x hx
    obtain ⟨a, ha⟩ := hden x hx
    refine ⟨a, ?_⟩
    have : (a : E) = (d : E) * x := by rw [Algebra.smul_def] at ha; exact ha
    rw [this]; field_simp
  have hBA : B ≤ A := fun a ha => (hA a).mpr ((hB a).mp ha).1
  have hmul : B = A * rr := by
    apply le_antisymm
    · obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hBA
      rw [hC]
      apply Ideal.mul_mono_right
      intro c hc
      rw [hrr]
      intro x hx
      obtain ⟨a, ha⟩ := hlift x hx
      have haA : a ∈ A := (hA a).mpr (by rw [ha]; exact hx)
      have : a * c ∈ B := by rw [hC]; exact Ideal.mul_mem_mul haA hc
      obtain ⟨_, h1, h2⟩ := (hB _).mp this
      constructor
      · convert h1 using 1; push_cast; rw [← ha]; ring
      · convert h2 using 1; push_cast; rw [← ha]; ring
    · rw [Ideal.mul_le]
      intro a ha c hc
      have hx := (hA a).mp ha
      obtain ⟨h1, h2⟩ := (hrr c).mp hc _ hx
      refine (hB _).mpr ⟨?_, ?_, ?_⟩
      · exact (hA _).mp (A.mul_mem_right c ha)
      · convert h1 using 1; push_cast; ring
      · convert h2 using 1; push_cast; ring
  have hAne : A ≠ ⊥ := by
    intro h
    apply hcc
    rw [FractionalIdeal.eq_zero_iff]
    intro x hx
    obtain ⟨a, ha⟩ := hlift x hx
    have haA : a ∈ A := (hA a).mpr (by rw [ha]; exact hx)
    rw [h, Ideal.mem_bot] at haA
    rw [← ha, haA]; simp
  have hHm : H = A.toAddSubgroup.map φ.toAddMonoidHom := by
    ext x
    rw [hH, AddSubgroup.mem_map]
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := hlift x hx
      exact ⟨a, (hA a).mpr (by rw [ha]; exact hx), by rw [← ha]; exact hφ a⟩
    · rintro ⟨a, ha, rfl⟩
      have := (hA a).mp ha
      rw [← hφ] at this; exact this
  have hKm : K ⊓ H = B.toAddSubgroup.map φ.toAddMonoidHom := by
    ext x
    rw [AddSubgroup.mem_inf, hH, hK, AddSubgroup.mem_map]
    constructor
    · rintro ⟨hk, hx⟩
      obtain ⟨a, ha⟩ := hlift x hx
      exact ⟨a, (hB a).mpr (by rw [ha]; exact ⟨hx, hk⟩), by rw [← ha]; exact hφ a⟩
    · rintro ⟨a, ha, rfl⟩
      have := (hB a).mp ha
      rw [← hφ] at this; exact ⟨this.2, this.1⟩
  rw [← AddSubgroup.inf_relIndex_right, hKm, hHm,
    AddSubgroup.relIndex_map_map_of_injective _ _ hφinj]
  have h1 := AddSubgroup.relIndex_mul_index (H := B.toAddSubgroup) (K := A.toAddSubgroup) hBA
  rw [← Ideal.absNorm_eq_index, ← Ideal.absNorm_eq_index, hmul, map_mul, mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hAne))
    (by rw [hmul]; exact h1)

/- English proof (translation)
Use `set P := Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 ⌊X⌋₊) with hP`. Establish `hpos : ∀ t ∈ P, ∀ i, 0 < t i`. Introduce `t ht i`. Use `(Fintype.mem_piFinset.mp ht) i` as an intermediate fact. Conclude with `(Finset.mem_Icc.mp this).1`.

Establish `h1 : ((P.filter (fun t => ((∏ i, t i : ℕ) : ℝ) ≤ X)).card : ℝ) ≤ ∑ t ∈ P, X * ∏ i, ((t i : ℝ))⁻¹`. Rewrite using `[Finset.card_eq_sum_ones, Nat.cast_sum]`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `t ht`.

Take `⟨htP, hle⟩` from `Finset.mem_filter.mp ht`. Establish `hp : (0 : ℝ) < ∏ i, (t i : ℝ)` using `Finset.prod_pos (fun i _ => by exact_mod_cast hpos t htP i)`. Rewrite using `[Finset.prod_inv_distrib, Nat.cast_one, ← div_eq_mul_inv, le_div_iff₀ hp, one_mul]`. Move the coercions through the operations in `at hle`. Conclude with `hle`.

Use `_ ≤ ∑ t ∈ P, X * ∏ i, ((t i : ℝ))⁻¹ := by`. Apply `Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)` to reduce the goal to its premises. Introduce `t _ _`. Establish `: (0 : ℝ) ≤ ∏ i, ((t i : ℝ))⁻¹` using `Finset.prod_nonneg (fun i _ => by positivity)`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h2 : ∑ t ∈ P, X * ∏ i, ((t i : ℝ))⁻¹ = X * (∑ j ∈ Finset.Icc 1 ⌊X⌋₊, ((j : ℝ))⁻¹) ^ n`. Use `Finset.prod_univ_sum (fun _ : Fin n => Finset.Icc 1 ⌊X⌋₊) (fun (_ : Fin n) (j : ℕ) => ((j : ℝ))⁻¹)` as an intermediate fact. Rewrite using `[← Finset.mul_sum, hP, ← this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Establish `h3 : ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, ((j : ℝ))⁻¹ ≤ 1 + Real.log X`. Use `harmonic_floor_le_one_add_log X hX` as an intermediate fact.

Rewrite `this` using `[harmonic_eq_sum_Icc]`. Move the coercions through the operations in `at this`. Conclude with `this`. Establish `h4 : 0 ≤ ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, ((j : ℝ))⁻¹` using `Finset.sum_nonneg (fun j _ => by positivity)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem s5a4_tuple_count (n : ℕ) (X : ℝ) (hX : 1 ≤ X) :
    (((Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 ⌊X⌋₊)).filter
      (fun t => ((∏ i, t i : ℕ) : ℝ) ≤ X)).card : ℝ) ≤ X * (1 + Real.log X) ^ n := by
  classical
  set P := Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 ⌊X⌋₊) with hP
  have hpos : ∀ t ∈ P, ∀ i, 0 < t i := by
    intro t ht i
    have := (Fintype.mem_piFinset.mp ht) i
    exact (Finset.mem_Icc.mp this).1
  have h1 : ((P.filter (fun t => ((∏ i, t i : ℕ) : ℝ) ≤ X)).card : ℝ) ≤
      ∑ t ∈ P, X * ∏ i, ((t i : ℝ))⁻¹ := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    calc ∑ t ∈ P.filter (fun t => ((∏ i, t i : ℕ) : ℝ) ≤ X), ((1 : ℕ) : ℝ)
        ≤ ∑ t ∈ P.filter (fun t => ((∏ i, t i : ℕ) : ℝ) ≤ X), X * ∏ i, ((t i : ℝ))⁻¹ := by
          apply Finset.sum_le_sum
          intro t ht
          obtain ⟨htP, hle⟩ := Finset.mem_filter.mp ht
          have hp : (0 : ℝ) < ∏ i, (t i : ℝ) :=
            Finset.prod_pos (fun i _ => by exact_mod_cast hpos t htP i)
          rw [Finset.prod_inv_distrib, Nat.cast_one, ← div_eq_mul_inv, le_div_iff₀ hp, one_mul]
          push_cast at hle; exact hle
      _ ≤ ∑ t ∈ P, X * ∏ i, ((t i : ℝ))⁻¹ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro t _ _
          have : (0 : ℝ) ≤ ∏ i, ((t i : ℝ))⁻¹ := Finset.prod_nonneg (fun i _ => by positivity)
          nlinarith
  have h2 : ∑ t ∈ P, X * ∏ i, ((t i : ℝ))⁻¹ = X * (∑ j ∈ Finset.Icc 1 ⌊X⌋₊, ((j : ℝ))⁻¹) ^ n := by
    have := Finset.prod_univ_sum (fun _ : Fin n => Finset.Icc 1 ⌊X⌋₊)
      (fun (_ : Fin n) (j : ℕ) => ((j : ℝ))⁻¹)
    rw [← Finset.mul_sum, hP, ← this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h3 : ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, ((j : ℝ))⁻¹ ≤ 1 + Real.log X := by
    have := harmonic_floor_le_one_add_log X hX
    rw [harmonic_eq_sum_Icc] at this
    push_cast at this
    exact this
  have h4 : 0 ≤ ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, ((j : ℝ))⁻¹ := Finset.sum_nonneg (fun j _ => by positivity)
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := by gcongr

/- English proof (translation)
Establish `hN0 : Ideal.absNorm Q ≠ 0` using `Ideal.absNorm_eq_zero_iff.not.mpr hQ0`. Establish `hN1 : Ideal.absNorm Q ≠ 1` using `fun h => hQ.ne_top (Ideal.absNorm_eq_one_iff.mp h)`. Establish `hex : ∀ m : ℕ, m ≠ 0 → (m : 𝓞 K) ∈ Q → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ Q`. Introduce `m`. Proceed by induction on `m using Nat.recOnMul with`.

Consider the case `zero => intro h`. Conclude with `absurd rfl h`. Consider the case `one => intro _ h; exact absurd ((Ideal.eq_top_iff_one Q).mpr (by simpa using h)) hQ.ne_top`. Consider the case `prime p hp => intro _ h`. Conclude with `⟨p, hp, h⟩`.

Consider the case `mul a b iha ihb`. Introduce `hab h`. Rewrite `h` using `[Nat.cast_mul]`. Break down `hQ.mem_or_mem h with h | h` into its components or cases. Conclude with `iha (left_ne_zero_of_mul hab) h`.

Conclude with `ihb (right_ne_zero_of_mul hab) h`. Take `⟨p, hp, hpQ⟩` from `hex _ hN0 (Ideal.absNorm_mem Q)`. Establish `hle : Ideal.span {(p : 𝓞 K)} ≤ Q` using `(Ideal.span_singleton_le_iff_mem Q).mpr hpQ`. Establish `hdvd` using `Ideal.absNorm_dvd_absNorm_of_le hle`. Establish `hnp : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ finrank ℚ K`.

Rewrite using `[Ideal.absNorm_span_singleton]`. Establish `: Algebra.norm ℤ (p : 𝓞 K) = (p : ℤ) ^ finrank ℚ K`. Establish `h` using `Algebra.norm_algebraMap (S := 𝓞 K) (p : ℤ)`. Rewrite `h` using `[RingOfIntegers.rank]`. Simplify using `using h`.

Rewrite using `[this]`. Simplify using `[Int.natAbs_pow]`. Rewrite `hdvd` using `[hnp]`. Take `⟨k, hk, hkeq⟩` from `(Nat.dvd_prime_pow hp).mp hdvd`. Use `⟨p, k, hp, ?_, hk, hpQ, hkeq⟩` and prove the remaining obligations.

Break down `Nat.eq_zero_or_pos k with h | h` into its components or cases. Rewrite `hkeq` using `[h, pow_zero]`. Conclude with `absurd hkeq hN1`. Conclude with `h`.
-/
theorem s5a4_prime_norm {K : Type} [Field K] [NumberField K] (Q : Ideal (𝓞 K)) (hQ : Q.IsPrime)
    (hQ0 : Q ≠ ⊥) : ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ k ≤ finrank ℚ K ∧ (p : 𝓞 K) ∈ Q ∧
      Ideal.absNorm Q = p ^ k := by
  have hN0 : Ideal.absNorm Q ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hQ0
  have hN1 : Ideal.absNorm Q ≠ 1 := fun h => hQ.ne_top (Ideal.absNorm_eq_one_iff.mp h)

  have hex : ∀ m : ℕ, m ≠ 0 → (m : 𝓞 K) ∈ Q → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ Q := by
    intro m
    induction m using Nat.recOnMul with
    | zero => intro h; exact absurd rfl h
    | one => intro _ h; exact absurd ((Ideal.eq_top_iff_one Q).mpr (by simpa using h)) hQ.ne_top
    | prime p hp => intro _ h; exact ⟨p, hp, h⟩
    | mul a b iha ihb =>
      intro hab h
      rw [Nat.cast_mul] at h
      rcases hQ.mem_or_mem h with h | h
      · exact iha (left_ne_zero_of_mul hab) h
      · exact ihb (right_ne_zero_of_mul hab) h
  obtain ⟨p, hp, hpQ⟩ := hex _ hN0 (Ideal.absNorm_mem Q)
  have hle : Ideal.span {(p : 𝓞 K)} ≤ Q := (Ideal.span_singleton_le_iff_mem Q).mpr hpQ
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  have hnp : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ finrank ℚ K := by
    rw [Ideal.absNorm_span_singleton]
    have : Algebra.norm ℤ (p : 𝓞 K) = (p : ℤ) ^ finrank ℚ K := by
      have h := Algebra.norm_algebraMap (S := 𝓞 K) (p : ℤ)
      rw [RingOfIntegers.rank] at h
      simpa using h
    rw [this]; simp [Int.natAbs_pow]
  rw [hnp] at hdvd
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  refine ⟨p, k, hp, ?_, hk, hpQ, hkeq⟩
  rcases Nat.eq_zero_or_pos k with h | h
  · rw [h, pow_zero] at hkeq; exact absurd hkeq hN1
  · exact h

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hco : Nat.Coprime p q` using `(Nat.coprime_primes hp hq).mpr hne`. Establish `hc : IsCoprime (p : ℤ) (q : ℤ)` using `Nat.isCoprime_iff_coprime.mpr hco`. Take `⟨u, v, huv⟩` from `hc`. Establish `h1 : (1 : 𝓞 K) ∈ Q`.

Establish `e : (1 : 𝓞 K) = (u : 𝓞 K) * (p : 𝓞 K) + (v : 𝓞 K) * (q : 𝓞 K)`. Use `congrArg (Int.cast : ℤ → 𝓞 K) huv` as an intermediate fact. Move the coercions through the operations in `at this ⊢`. Conclude with `this.symm`. Rewrite using `[e]`.

Conclude with `Q.add_mem (Q.mul_mem_left _ hpQ) (Q.mul_mem_left _ hqQ)`. Conclude with `hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr h1)`.
-/
theorem s5a4_prime_unique {K : Type} [Field K] [NumberField K] (Q : Ideal (𝓞 K)) (hQ : Q.IsPrime)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpQ : (p : 𝓞 K) ∈ Q) (hqQ : (q : 𝓞 K) ∈ Q) : p = q := by
  by_contra hne
  have hco : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr hco
  obtain ⟨u, v, huv⟩ := hc
  have h1 : (1 : 𝓞 K) ∈ Q := by
    have e : (1 : 𝓞 K) = (u : 𝓞 K) * (p : 𝓞 K) + (v : 𝓞 K) * (q : 𝓞 K) := by
      have := congrArg (Int.cast : ℤ → 𝓞 K) huv
      push_cast at this ⊢; exact this.symm
    rw [e]; exact Q.add_mem (Q.mul_mem_left _ hpQ) (Q.mul_mem_left _ hqQ)
  exact hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr h1)

open UniqueFactorizationMonoid in
/- English proof (translation)
Establish `hp0 : (p : 𝓞 K) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hI : Ideal.span {(p : 𝓞 K)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hp0`. Use `⟨(normalizedFactors (Ideal.span {(p : 𝓞 K)})).toFinset, ?_, ?_⟩` and prove the remaining obligations.

Use `(Multiset.toFinset_card_le _).trans ?_` and prove the remaining obligations. Establish `hnp : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ finrank ℚ K`. Rewrite using `[Ideal.absNorm_span_singleton]`. Establish `: Algebra.norm ℤ (p : 𝓞 K) = (p : ℤ) ^ finrank ℚ K`. Establish `h` using `Algebra.norm_algebraMap (S := 𝓞 K) (p : ℤ)`.

Rewrite `h` using `[RingOfIntegers.rank]`. Simplify using `using h`. Rewrite using `[this]`. Simplify using `[Int.natAbs_pow]`. Establish `h1 : ((normalizedFactors (Ideal.span {(p : 𝓞 K)})).map Ideal.absNorm).prod = p ^ finrank ℚ K`.

Rewrite using `[← hnp, ← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self hI]`. Establish `h2 : p ^ Multiset.card ((normalizedFactors (Ideal.span {(p : 𝓞 K)})).map Ideal.absNorm) ≤ ((normalizedFactors (Ideal.span {(p : 𝓞 K)})).map Ideal.absNorm).prod`. Apply `Multiset.pow_card_le_prod` to reduce the goal to its premises. Introduce `x hx`. Take `⟨Q, hQ, rfl⟩` from `Multiset.mem_map.mp hx`.

Take `⟨hQp, hle⟩` from `(Ideal.mem_normalizedFactors_iff hI).mp hQ`. Establish `hpQ : (p : 𝓞 K) ∈ Q` using `hle (Ideal.mem_span_singleton_self _)`. Establish `hQ0 : Q ≠ ⊥` using `fun h => hp0 (by rw [h] at hpQ; exact hpQ)`. Take `⟨q, k, hq, hk, _, hqQ, hN⟩` from `s5a4_prime_norm Q hQp hQ0`. Rewrite using `[hN, s5a4_prime_unique Q hQp p q hp hq hpQ hqQ]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `h2` using `[h1, Multiset.card_map]`. Conclude with `(Nat.pow_le_pow_iff_right hp.one_lt).mp h2`. Introduce `Q hQ hpQ`. Rewrite using `[Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hI]`.

Conclude with `⟨hQ, (Ideal.span_singleton_le_iff_mem Q).mpr hpQ⟩`.
-/
theorem s5a4_primes_over {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    ∃ s : Finset (Ideal (𝓞 K)), s.card ≤ finrank ℚ K ∧
      ∀ Q : Ideal (𝓞 K), Q.IsPrime → (p : 𝓞 K) ∈ Q → Q ∈ s := by
  classical
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hI : Ideal.span {(p : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hp0
  refine ⟨(normalizedFactors (Ideal.span {(p : 𝓞 K)})).toFinset, ?_, ?_⟩
  · refine (Multiset.toFinset_card_le _).trans ?_
    have hnp : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ finrank ℚ K := by
      rw [Ideal.absNorm_span_singleton]
      have : Algebra.norm ℤ (p : 𝓞 K) = (p : ℤ) ^ finrank ℚ K := by
        have h := Algebra.norm_algebraMap (S := 𝓞 K) (p : ℤ)
        rw [RingOfIntegers.rank] at h
        simpa using h
      rw [this]; simp [Int.natAbs_pow]
    have h1 : ((normalizedFactors (Ideal.span {(p : 𝓞 K)})).map Ideal.absNorm).prod =
        p ^ finrank ℚ K := by
      rw [← hnp, ← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self hI]
    have h2 : p ^ Multiset.card ((normalizedFactors (Ideal.span {(p : 𝓞 K)})).map Ideal.absNorm) ≤
        ((normalizedFactors (Ideal.span {(p : 𝓞 K)})).map Ideal.absNorm).prod := by
      apply Multiset.pow_card_le_prod
      intro x hx
      obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp hx
      obtain ⟨hQp, hle⟩ := (Ideal.mem_normalizedFactors_iff hI).mp hQ
      have hpQ : (p : 𝓞 K) ∈ Q := hle (Ideal.mem_span_singleton_self _)
      have hQ0 : Q ≠ ⊥ := fun h => hp0 (by rw [h] at hpQ; exact hpQ)
      obtain ⟨q, k, hq, hk, _, hqQ, hN⟩ := s5a4_prime_norm Q hQp hQ0
      rw [hN, s5a4_prime_unique Q hQp p q hp hq hpQ hqQ]
      calc q = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ k := Nat.pow_le_pow_right hq.pos hk
    rw [h1, Multiset.card_map] at h2
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h2
  · intro Q hQ hpQ
    rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hI]
    exact ⟨hQ, (Ideal.span_singleton_le_iff_mem Q).mpr hpQ⟩

/- English proof (translation)
Establish `hn : 0 < finrank ℚ K` using `finrank_pos`. Establish `h1 : ∀ p : ℕ, ∃ f : Ideal (𝓞 K) → Fin (finrank ℚ K), p.Prime → ∀ Q Q' : Ideal (𝓞 K), Q.IsPrime → Q'.IsPrime → (p : 𝓞 K) ∈ Q → (p : 𝓞 K) ∈ Q' → f Q = f Q' → Q = Q'`. Introduce `p`. Distinguish the cases in `hp : p.Prime`. Take `⟨s, hs, hmem⟩` from `s5a4_primes_over (K := K) p hp`.

Use `⟨fun Q => if h : Q ∈ s then Fin.castLE hs (s.equivFin ⟨Q, h⟩) else ⟨0, hn⟩, ?_⟩` and prove the remaining obligations. Introduce `_ Q Q' hQ hQ' hpQ hpQ' he`. Simplify using `only [dif_pos (hmem Q hQ hpQ), dif_pos (hmem Q' hQ' hpQ')] at he`. Use `s.equivFin.injective (Fin.castLE_injective hs he)` as an intermediate fact. Conclude with `congrArg Subtype.val this`.

Conclude with `⟨fun _ => ⟨0, hn⟩, fun h => absurd h hp⟩`. Use `choose f hf using h1`. Set `π : Ideal (𝓞 K) → ℕ` to `fun Q => if h : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ Q then h.choose else 0`. Establish `hπ : ∀ (Q : Ideal (𝓞 K)) (p : ℕ), Q.IsPrime → p.Prime → (p : 𝓞 K) ∈ Q → π Q = p`. Introduce `Q p hQ hp hpQ`.

Establish `h : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ Q` using `⟨p, hp, hpQ⟩`. Simplify using `only [π, dif_pos h]`. Conclude with `s5a4_prime_unique Q hQ _ _ h.choose_spec.1 hp h.choose_spec.2 hpQ`. Use `⟨fun Q => f (π Q) Q, ?_⟩` and prove the remaining obligations. Introduce `p hp Q Q' hQ hQ' hpQ hpQ' he`.

Simplify using `only [hπ Q p hQ hp hpQ, hπ Q' p hQ' hp hpQ'] at he`. Conclude with `hf p hp Q Q' hQ hQ' hpQ hpQ' he`.
-/
theorem s5a4_index (K : Type) [Field K] [NumberField K] :
    ∃ ι : Ideal (𝓞 K) → Fin (finrank ℚ K), ∀ p : ℕ, p.Prime → ∀ Q Q' : Ideal (𝓞 K),
      Q.IsPrime → Q'.IsPrime → (p : 𝓞 K) ∈ Q → (p : 𝓞 K) ∈ Q' → ι Q = ι Q' → Q = Q' := by
  classical
  have hn : 0 < finrank ℚ K := finrank_pos
  have h1 : ∀ p : ℕ, ∃ f : Ideal (𝓞 K) → Fin (finrank ℚ K), p.Prime → ∀ Q Q' : Ideal (𝓞 K),
      Q.IsPrime → Q'.IsPrime → (p : 𝓞 K) ∈ Q → (p : 𝓞 K) ∈ Q' → f Q = f Q' → Q = Q' := by
    intro p
    by_cases hp : p.Prime
    · obtain ⟨s, hs, hmem⟩ := s5a4_primes_over (K := K) p hp
      refine ⟨fun Q => if h : Q ∈ s then Fin.castLE hs (s.equivFin ⟨Q, h⟩) else ⟨0, hn⟩, ?_⟩
      intro _ Q Q' hQ hQ' hpQ hpQ' he
      simp only [dif_pos (hmem Q hQ hpQ), dif_pos (hmem Q' hQ' hpQ')] at he
      have := s.equivFin.injective (Fin.castLE_injective hs he)
      exact congrArg Subtype.val this
    · exact ⟨fun _ => ⟨0, hn⟩, fun h => absurd h hp⟩
  choose f hf using h1
  let π : Ideal (𝓞 K) → ℕ := fun Q => if h : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ Q then h.choose else 0
  have hπ : ∀ (Q : Ideal (𝓞 K)) (p : ℕ), Q.IsPrime → p.Prime → (p : 𝓞 K) ∈ Q → π Q = p := by
    intro Q p hQ hp hpQ
    have h : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ Q := ⟨p, hp, hpQ⟩
    simp only [π, dif_pos h]
    exact s5a4_prime_unique Q hQ _ _ h.choose_spec.1 hp h.choose_spec.2 hpQ
  refine ⟨fun Q => f (π Q) Q, ?_⟩
  intro p hp Q Q' hQ hQ' hpQ hpQ' he
  simp only [hπ Q p hQ hp hpQ, hπ Q' p hQ' hp hpQ'] at he
  exact hf p hp Q Q' hQ hQ' hpQ hpQ' he

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons Q s ih`. Establish `ih'` using `ih (fun Q' h => hs Q' (Multiset.mem_cons_of_mem h))`. Take `⟨hQ, hQ0⟩` from `hs Q (Multiset.mem_cons_self Q s)`.

Distinguish the cases in `hi : ι Q = ι P`. Rewrite using `[Multiset.filter_cons_of_pos (p := fun Q => ι Q = ι P) s hi, Multiset.map_cons, Multiset.prod_cons]`. Establish `hN0 : Ideal.absNorm Q ≠ 0` using `Ideal.absNorm_eq_zero_iff.not.mpr hQ0`. Establish `hpr0 : ((s.filter (fun Q => ι Q = ι P)).map Ideal.absNorm).prod ≠ 0`. Apply `Multiset.prod_ne_zero` to reduce the goal to its premises.

Introduce `h0`. Take `⟨Q', hQ', h0'⟩` from `Multiset.mem_map.mp h0`. Conclude with `(hs Q' (Multiset.mem_cons_of_mem (Multiset.mem_filter.mp hQ').1)).2 (Ideal.absNorm_eq_zero_iff.mp h0')`. Rewrite using `[Nat.factorization_mul hN0 hpr0, Finsupp.add_apply, ih']`. Distinguish the cases in `hQP : Q = P`.

Substitute `hQP` using the available equality. Rewrite using `[Multiset.count_cons_self, hk, hp.factorization_pow, Finsupp.single_eq_same]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨q, j, hq, _, _, hqQ, hj⟩` from `s5a4_prime_norm Q hQ hQ0`. Establish `hqp : q ≠ p`.

Introduce and unpack `rfl`. Conclude with `hQP (hι q hq Q P hQ hP hqQ hpP hi)`. Rewrite using `[Multiset.count_cons_of_ne (Ne.symm hQP), hj, hq.factorization_pow, Finsupp.single_eq_of_ne (Ne.symm hqp), zero_add]`. Establish `hQP : Q ≠ P` using `fun h => hi (by rw [h])`. Rewrite using `[Multiset.filter_cons_of_neg (p := fun Q => ι Q = ι P) s hi, Multiset.count_cons_of_ne (Ne.symm hQP), ih']`.
-/
theorem s5a4_val {K : Type} [Field K] [NumberField K] (ι : Ideal (𝓞 K) → Fin (finrank ℚ K))
    (hι : ∀ p : ℕ, p.Prime → ∀ Q Q' : Ideal (𝓞 K),
      Q.IsPrime → Q'.IsPrime → (p : 𝓞 K) ∈ Q → (p : 𝓞 K) ∈ Q' → ι Q = ι Q' → Q = Q')
    (P : Ideal (𝓞 K)) (hP : P.IsPrime) (p k : ℕ) (hp : p.Prime) (hpP : (p : 𝓞 K) ∈ P)
    (hk : Ideal.absNorm P = p ^ k) (s : Multiset (Ideal (𝓞 K)))
    (hs : ∀ Q ∈ s, Q.IsPrime ∧ Q ≠ ⊥) [DecidableEq (Ideal (𝓞 K))] :
    (((s.filter (fun Q => ι Q = ι P)).map Ideal.absNorm).prod).factorization p =
      k * s.count P := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons Q s ih =>
    have ih' := ih (fun Q' h => hs Q' (Multiset.mem_cons_of_mem h))
    obtain ⟨hQ, hQ0⟩ := hs Q (Multiset.mem_cons_self Q s)
    by_cases hi : ι Q = ι P
    · rw [Multiset.filter_cons_of_pos (p := fun Q => ι Q = ι P) s hi, Multiset.map_cons, Multiset.prod_cons]
      have hN0 : Ideal.absNorm Q ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hQ0
      have hpr0 : ((s.filter (fun Q => ι Q = ι P)).map Ideal.absNorm).prod ≠ 0 := by
        apply Multiset.prod_ne_zero
        intro h0
        obtain ⟨Q', hQ', h0'⟩ := Multiset.mem_map.mp h0
        exact (hs Q' (Multiset.mem_cons_of_mem (Multiset.mem_filter.mp hQ').1)).2
          (Ideal.absNorm_eq_zero_iff.mp h0')
      rw [Nat.factorization_mul hN0 hpr0, Finsupp.add_apply, ih']
      by_cases hQP : Q = P
      · subst hQP
        rw [Multiset.count_cons_self, hk, hp.factorization_pow, Finsupp.single_eq_same]; ring
      · obtain ⟨q, j, hq, _, _, hqQ, hj⟩ := s5a4_prime_norm Q hQ hQ0
        have hqp : q ≠ p := by
          rintro rfl
          exact hQP (hι q hq Q P hQ hP hqQ hpP hi)
        rw [Multiset.count_cons_of_ne (Ne.symm hQP), hj, hq.factorization_pow,
          Finsupp.single_eq_of_ne (Ne.symm hqp), zero_add]
    · have hQP : Q ≠ P := fun h => hi (by rw [h])
      rw [Multiset.filter_cons_of_neg (p := fun Q => ι Q = ι P) s hi, Multiset.count_cons_of_ne (Ne.symm hQP), ih']

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih`. Establish `: ∀ i, (((a ::ₘ s).filter (fun a => g a = i)).map f).prod = (if g a = i then f a else 1) * ((s.filter (fun a => g a = i)).map f).prod`. Introduce `i`.

Distinguish the cases in `h : g a = i`. Rewrite using `[Multiset.filter_cons_of_pos (p := fun a => g a = i) s h, Multiset.map_cons, Multiset.prod_cons, if_pos h]`. Rewrite using `[Multiset.filter_cons_of_neg (p := fun a => g a = i) s h, if_neg h, one_mul]`. Simplify using `only [this, Finset.prod_mul_distrib, ih, Finset.prod_ite_eq, Finset.mem_univ, if_true, Multiset.map_cons, Multiset.prod_cons]`.
-/
theorem s5a4_fiber_prod {α : Type} {n : ℕ} (g : α → Fin n) (f : α → ℕ) (s : Multiset α) :
    ∏ i, ((s.filter (fun a => g a = i)).map f).prod = (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have : ∀ i, (((a ::ₘ s).filter (fun a => g a = i)).map f).prod =
        (if g a = i then f a else 1) * ((s.filter (fun a => g a = i)).map f).prod := by
      intro i
      by_cases h : g a = i
      · rw [Multiset.filter_cons_of_pos (p := fun a => g a = i) s h, Multiset.map_cons, Multiset.prod_cons, if_pos h]
      · rw [Multiset.filter_cons_of_neg (p := fun a => g a = i) s h, if_neg h, one_mul]
    simp only [this, Finset.prod_mul_distrib, ih, Finset.prod_ite_eq, Finset.mem_univ, if_true,
      Multiset.map_cons, Multiset.prod_cons]

open UniqueFactorizationMonoid in
/- English proof (translation)
Introduce `K _ _ X hX`. Establish `hfin : {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.Finite` using `(Ideal.finite_setOfPred_absNorm_le ⌊X⌋₊).subset (fun I hI => Nat.le_floor hI.2)`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Take `⟨ι, hι⟩` from `s5a4_index K`. Set `τ : Ideal (𝓞 K) → (Fin (finrank ℚ K) → ℕ)` to `fun I i => (((normalizedFactors I).filter (fun Q => ι Q = i)).map Ideal.absNorm).prod`.

Establish `hprod : ∀ I : Ideal (𝓞 K), I ≠ ⊥ → ∏ i, τ I i = Ideal.absNorm I`. Introduce `I hI`. Simplify using `only [τ]`. Rewrite using `[s5a4_fiber_prod ι (fun Q => Ideal.absNorm Q) (normalizedFactors I)]`. Use `conv_rhs => rw [← Ideal.prod_normalizedFactors_eq_self hI, map_multiset_prod]`.

Establish `hfac : ∀ I : Ideal (𝓞 K), ∀ Q ∈ normalizedFactors I, Q.IsPrime ∧ Q ≠ ⊥`. Introduce `I Q hQ`. Use `prime_of_normalized_factor Q hQ` as an intermediate fact. Conclude with `⟨Ideal.isPrime_of_prime this, this.ne_zero⟩`. Establish `hinj : ∀ I J : Ideal (𝓞 K), I ≠ ⊥ → J ≠ ⊥ → τ I = τ J → I = J`.

Introduce `I J hI hJ h`. Establish `: normalizedFactors I = normalizedFactors J`. Use extensionality with `P`. Distinguish the cases in `hP : P.IsPrime ∧ P ≠ ⊥`. Take `⟨p, k, hp, hk1, _, hpP, hk⟩` from `s5a4_prime_norm P hP.1 hP.2`.

Establish `h1` using `s5a4_val ι hι P hP.1 p k hp hpP hk (normalizedFactors I) (hfac I)`. Establish `h2` using `s5a4_val ι hι P hP.1 p k hp hpP hk (normalizedFactors J) (hfac J)`. Establish `h3 : τ I (ι P) = τ J (ι P)` using `congrFun h _`. Simplify using `only [τ] at h3`. Rewrite `h1` using `[h3, h2]`.

Conclude with `(Nat.eq_of_mul_eq_mul_left hk1 h1).symm`. Rewrite using `[Multiset.count_eq_zero_of_notMem (fun h => hP (hfac I P h)), Multiset.count_eq_zero_of_notMem (fun h => hP (hfac J P h))]`. Rewrite using `[← Ideal.prod_normalizedFactors_eq_self hI, ← Ideal.prod_normalizedFactors_eq_self hJ, this]`. Establish `hcard : hfin.toFinset.card ≤ ((Fintype.piFinset (fun _ : Fin (finrank ℚ K) => Finset.Icc 1 ⌊X⌋₊)).filter (fun t => ((∏ i, t i : ℕ) : ℝ) ≤ X)).card`. Apply `Finset.card_le_card_of_injOn τ` to reduce the goal to its premises.

Introduce `I hI`. Take `⟨hI0, hIX⟩` from `hfin.mem_toFinset.mp hI`. Establish `hN0 : Ideal.absNorm I ≠ 0` using `Ideal.absNorm_eq_zero_iff.not.mpr hI0`. Rewrite using `[Finset.coe_filter, Set.mem_setOf_eq, Fintype.mem_piFinset, hprod I hI0]`. Use `⟨fun i => ?_, hIX⟩` and prove the remaining obligations.

Establish `hd : τ I i ∣ Ideal.absNorm I`. Rewrite using `[← hprod I hI0]`. Conclude with `Finset.dvd_prod_of_mem _ (Finset.mem_univ i)`. Rewrite using `[Finset.mem_Icc]`. Conclude with `⟨Nat.pos_of_ne_zero (fun h0 => hN0 (by rw [h0] at hd; exact Nat.eq_zero_of_zero_dvd hd)), (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hd).trans (Nat.le_floor hIX)⟩`.

Introduce `I hI J hJ h`. Conclude with `hinj I J (hfin.mem_toFinset.mp hI).1 (hfin.mem_toFinset.mp hJ).1 h`. Rewrite using `[Set.ncard_eq_toFinset_card _ hfin]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ideal_count_bound : IdealCountBound := by
  intro K _ _ X hX
  classical
  have hfin : {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.Finite :=
    (Ideal.finite_setOfPred_absNorm_le ⌊X⌋₊).subset (fun I hI => Nat.le_floor hI.2)
  refine ⟨hfin, ?_⟩
  obtain ⟨ι, hι⟩ := s5a4_index K
  let τ : Ideal (𝓞 K) → (Fin (finrank ℚ K) → ℕ) := fun I i =>
    (((normalizedFactors I).filter (fun Q => ι Q = i)).map Ideal.absNorm).prod
  have hprod : ∀ I : Ideal (𝓞 K), I ≠ ⊥ → ∏ i, τ I i = Ideal.absNorm I := by
    intro I hI
    simp only [τ]
    rw [s5a4_fiber_prod ι (fun Q => Ideal.absNorm Q) (normalizedFactors I)]
    conv_rhs => rw [← Ideal.prod_normalizedFactors_eq_self hI, map_multiset_prod]
  have hfac : ∀ I : Ideal (𝓞 K), ∀ Q ∈ normalizedFactors I, Q.IsPrime ∧ Q ≠ ⊥ := by
    intro I Q hQ
    have := prime_of_normalized_factor Q hQ
    exact ⟨Ideal.isPrime_of_prime this, this.ne_zero⟩
  have hinj : ∀ I J : Ideal (𝓞 K), I ≠ ⊥ → J ≠ ⊥ → τ I = τ J → I = J := by
    intro I J hI hJ h
    have : normalizedFactors I = normalizedFactors J := by
      ext P
      by_cases hP : P.IsPrime ∧ P ≠ ⊥
      · obtain ⟨p, k, hp, hk1, _, hpP, hk⟩ := s5a4_prime_norm P hP.1 hP.2
        have h1 := s5a4_val ι hι P hP.1 p k hp hpP hk (normalizedFactors I) (hfac I)
        have h2 := s5a4_val ι hι P hP.1 p k hp hpP hk (normalizedFactors J) (hfac J)
        have h3 : τ I (ι P) = τ J (ι P) := congrFun h _
        simp only [τ] at h3
        rw [h3, h2] at h1
        exact (Nat.eq_of_mul_eq_mul_left hk1 h1).symm
      · rw [Multiset.count_eq_zero_of_notMem (fun h => hP (hfac I P h)),
          Multiset.count_eq_zero_of_notMem (fun h => hP (hfac J P h))]
    rw [← Ideal.prod_normalizedFactors_eq_self hI, ← Ideal.prod_normalizedFactors_eq_self hJ, this]
  have hcard : hfin.toFinset.card ≤ ((Fintype.piFinset (fun _ : Fin (finrank ℚ K) =>
      Finset.Icc 1 ⌊X⌋₊)).filter (fun t => ((∏ i, t i : ℕ) : ℝ) ≤ X)).card := by
    apply Finset.card_le_card_of_injOn τ
    · intro I hI
      obtain ⟨hI0, hIX⟩ := hfin.mem_toFinset.mp hI
      have hN0 : Ideal.absNorm I ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hI0
      rw [Finset.coe_filter, Set.mem_setOf_eq, Fintype.mem_piFinset, hprod I hI0]
      refine ⟨fun i => ?_, hIX⟩
      have hd : τ I i ∣ Ideal.absNorm I := by
        rw [← hprod I hI0]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      rw [Finset.mem_Icc]
      exact ⟨Nat.pos_of_ne_zero (fun h0 => hN0 (by rw [h0] at hd; exact Nat.eq_zero_of_zero_dvd hd)),
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hd).trans (Nat.le_floor hIX)⟩
    · intro I hI J hJ h
      exact hinj I J (hfin.mem_toFinset.mp hI).1 (hfin.mem_toFinset.mp hJ).1 h
  rw [Set.ncard_eq_toFinset_card _ hfin]
  calc ((hfin.toFinset.card : ℕ) : ℝ) ≤ _ := by exact_mod_cast hcard
    _ ≤ _ := s5a4_tuple_count (finrank ℚ K) X hX

/- English proof (translation)
Introduce `E _ _ hc`. Use `set D : ℝ := Real.sqrt |(discr E : ℝ)| with hD`. Establish `hD1 : 1 ≤ D`. Rewrite using `[hD, Real.one_le_sqrt]`. Establish `h0 : discr E ≠ 0` using `discr_ne_zero E`.

Establish `: (1 : ℤ) ≤ |discr E|` using `Int.one_le_abs h0`. Conclude with `this` after adjusting the coercions. Take `⟨hfin, hcount⟩` from `ideal_count_bound E D hD1`. Use `le_trans ?_ hcount` and prove the remaining obligations. Establish `hr2 : finrank ℚ E = 2 * InfinitePlace.nrComplexPlaces E`.

Establish `h1` using `InfinitePlace.card_add_two_mul_card_eq_rank E`. Establish `h3 : InfinitePlace.nrRealPlaces E = 0`. Rewrite using `[InfinitePlace.nrRealPlaces, Fintype.card_eq_zero_iff]`. Conclude with `⟨fun w => (InfinitePlace.not_isComplex_iff_isReal.mpr w.2) (hc w.1)⟩`. Use linear arithmetic over natural numbers and integers.

Establish `hM : (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E * (((finrank ℚ E).factorial : ℝ) / (finrank ℚ E : ℝ) ^ (finrank ℚ E) * D) ≤ D`. Establish `h1` using `minkowski_constant_bound (InfinitePlace.nrComplexPlaces E)`. Rewrite `h1` using `[← hr2]`. Establish `h2 : (2 / Real.pi) ^ InfinitePlace.nrComplexPlaces E ≤ 1`. Apply `pow_le_one₀ (by positivity)` to reduce the goal to its premises.

Rewrite using `[div_le_one Real.pi_pos]`. Conclude with `Real.two_le_pi`. Establish `h3 : (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E * (((finrank ℚ E).factorial : ℝ) / (finrank ℚ E : ℝ) ^ (finrank ℚ E) * D) = ((4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E * ((finrank ℚ E).factorial : ℝ) / (finrank ℚ E : ℝ) ^ (finrank ℚ E)) * D` using `by ring`. Rewrite using `[h3]`. Combine the equalities or inequalities in the displayed calculation.

Apply `mul_le_mul_of_nonneg_right (h1.trans h2) (by linarith)` to reduce the goal to its premises. Use `_ = D := one_mul D`. Use `choose I hI1 hI2 using exists_ideal_in_class_of_norm_le (K := E)`. Establish `hinj : Function.Injective (fun C : ClassGroup (𝓞 E) => ((I C : (Ideal (𝓞 E))⁰) : Ideal (𝓞 E)))`. Introduce `C C' h`.

Establish `: I C = I C'` using `Subtype.ext h`. Rewrite using `[← hI1 C, ← hI1 C', this]`. Establish `hle : Fintype.card (ClassGroup (𝓞 E)) ≤ hfin.toFinset.card`. Rewrite using `[← Finset.card_univ]`. Apply `Finset.card_le_card_of_injOn (fun C : ClassGroup (𝓞 E) => ((I C : (Ideal (𝓞 E))⁰) : Ideal (𝓞 E)))` to reduce the goal to its premises.

Introduce `C _`. Rewrite using `[Finset.mem_coe, hfin.mem_toFinset]`. Conclude with `⟨nonZeroDivisors.ne_zero (I C).2, (hI2 C).trans hM⟩`. Conclude with `hinj.injOn`. Rewrite using `[Set.ncard_eq_toFinset_card _ hfin, classNumber]`.

Conclude with `hle` after adjusting the coercions.
-/
theorem class_number_bound : ClassNumberBound := by
  intro E _ _ hc
  classical
  set D : ℝ := Real.sqrt |(discr E : ℝ)| with hD
  have hD1 : 1 ≤ D := by
    rw [hD, Real.one_le_sqrt]
    have h0 : discr E ≠ 0 := discr_ne_zero E
    have : (1 : ℤ) ≤ |discr E| := Int.one_le_abs h0
    exact_mod_cast this
  obtain ⟨hfin, hcount⟩ := ideal_count_bound E D hD1
  refine le_trans ?_ hcount

  have hr2 : finrank ℚ E = 2 * InfinitePlace.nrComplexPlaces E := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank E
    have h3 : InfinitePlace.nrRealPlaces E = 0 := by
      rw [InfinitePlace.nrRealPlaces, Fintype.card_eq_zero_iff]
      exact ⟨fun w => (InfinitePlace.not_isComplex_iff_isReal.mpr w.2) (hc w.1)⟩
    omega
  have hM : (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E *
      (((finrank ℚ E).factorial : ℝ) / (finrank ℚ E : ℝ) ^ (finrank ℚ E) * D) ≤ D := by
    have h1 := minkowski_constant_bound (InfinitePlace.nrComplexPlaces E)
    rw [← hr2] at h1
    have h2 : (2 / Real.pi) ^ InfinitePlace.nrComplexPlaces E ≤ 1 := by
      apply pow_le_one₀ (by positivity)
      rw [div_le_one Real.pi_pos]; exact Real.two_le_pi
    have h3 : (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E *
      (((finrank ℚ E).factorial : ℝ) / (finrank ℚ E : ℝ) ^ (finrank ℚ E) * D) =
      ((4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E * ((finrank ℚ E).factorial : ℝ) /
        (finrank ℚ E : ℝ) ^ (finrank ℚ E)) * D := by ring
    rw [h3]
    calc _ ≤ 1 * D := by
          apply mul_le_mul_of_nonneg_right (h1.trans h2) (by linarith)
      _ = D := one_mul D
  choose I hI1 hI2 using exists_ideal_in_class_of_norm_le (K := E)
  have hinj : Function.Injective (fun C : ClassGroup (𝓞 E) => ((I C : (Ideal (𝓞 E))⁰) : Ideal (𝓞 E))) := by
    intro C C' h
    have : I C = I C' := Subtype.ext h
    rw [← hI1 C, ← hI1 C', this]
  have hle : Fintype.card (ClassGroup (𝓞 E)) ≤ hfin.toFinset.card := by
    rw [← Finset.card_univ]
    apply Finset.card_le_card_of_injOn (fun C : ClassGroup (𝓞 E) => ((I C : (Ideal (𝓞 E))⁰) : Ideal (𝓞 E)))
    · intro C _
      rw [Finset.mem_coe, hfin.mem_toFinset]
      exact ⟨nonZeroDivisors.ne_zero (I C).2, (hI2 C).trans hM⟩
    · exact hinj.injOn
  rw [Set.ncard_eq_toFinset_card _ hfin, classNumber]
  exact_mod_cast hle

end Formalism.HermitianLatticeCounting.P
