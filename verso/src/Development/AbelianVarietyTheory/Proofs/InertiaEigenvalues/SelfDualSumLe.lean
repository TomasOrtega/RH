import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StdPowMemOfLe

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory.HermNbr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] {r : ℕ}

/- English proof (translation)
Use `set G := ((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O with hG`. Use `set Gi := (((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O with hGi`. Establish `h1 : ∀ x, G (Gi x) = x`. Introduce `x`. Express the relevant statement in the definitionally equal form `(g : Matrix (Fin r) (Fin r) K).mulVec ((((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)).mulVec x) = x`.

Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Establish `h2 : ∀ x, Gi (G x) = x`. Introduce `x`. Express the relevant statement in the definitionally equal form `(((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)).mulVec ((g : Matrix (Fin r) (Fin r) K).mulVec x) = x`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`.

Establish `memG : ∀ x, x ∈ L.map G ↔ Gi x ∈ L`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Rewrite using `[h2]`.

Conclude with `hy`. Introduce `h`. Conclude with `⟨Gi x, h, h1 x⟩`. Establish `hfG : ∀ x y, hf cK J (G x) (G y) = hf cK J x y` using `fun x y => hf_mulVec cK J _ hU x y`. Take `⟨hSD, habs, hidx⟩` from `hL`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Rewrite using `[memG, hSD (Gi x)]`. Prove the components needed by the constructor for the conclusion. Introduce `h y hy`.

Rewrite using `[← h1 x, ← h1 y, hfG]`. Conclude with `h _ ((memG y).1 hy)`. Introduce `h y hy`. Use `h (G y) ((memG _).2 (by rw [h2]; exact hy))` as an intermediate fact. Rewrite `this` using `[← h1 x, hfG]`. Then use the resulting hypothesis.

Introduce `x`. Take `⟨k, hk⟩` from `habs (Gi x)`. Use `⟨k, (memG _).2 ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul]`. Conclude with `hk`.

Establish `hinj : Function.Injective G.toAddMonoidHom` using `fun x y h => by`. Use `congrArg Gi h` as an intermediate fact. Simplify `this` using `[h2]`. Use `set f : (Fin r → K) →ₗ[O] (Fin r → K) := ϖ • LinearMap.id with hf'`. Establish `hcomm : (L.map G).map f = (L.map f).map G`.

Rewrite using `[← Submodule.map_comp, ← Submodule.map_comp]`. Use `congr 1`. Use extensionality with `x`. Simplify using `[hf', hG]`. Establish `e : ∀ P : Submodule O (Fin r → K), (P.map G).toAddSubgroup = P.toAddSubgroup.map G.toAddMonoidHom` using `fun P => by`.

Use extensionality with `x`. Simplify using `[Submodule.mem_map]`. Unfold `idx at hidx ⊢`. Rewrite `hidx`, the goal using `[← hf']`. Rewrite using `[hcomm, e, e, AddSubgroup.relIndex_map_map_of_injective _ _ hinj, hidx]`.
-/
theorem good_map (cK : K ≃+* K) {J : Matrix (Fin r) (Fin r) K} {ϖ : O} {N : ℕ}
    {L : Submodule O (Fin r → K)} (hL : Good cK J ϖ N L) (hϖ : Irreducible ϖ)
    (g : GL (Fin r) K) (hU : ((g : Matrix (Fin r) (Fin r) K).map cK).transpose * J *
      (g : Matrix (Fin r) (Fin r) K) = J) :
    Good cK J ϖ N (L.map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)) := by
  set G := ((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O with hG
  set Gi := (((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O with hGi
  have h1 : ∀ x, G (Gi x) = x := by
    intro x
    change (g : Matrix (Fin r) (Fin r) K).mulVec ((((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)).mulVec x) = x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have h2 : ∀ x, Gi (G x) = x := by
    intro x
    change (((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)).mulVec ((g : Matrix (Fin r) (Fin r) K).mulVec x) = x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have memG : ∀ x, x ∈ L.map G ↔ Gi x ∈ L := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩; rw [h2]; exact hy
    · intro h; exact ⟨Gi x, h, h1 x⟩
  have hfG : ∀ x y, hf cK J (G x) (G y) = hf cK J x y := fun x y => hf_mulVec cK J _ hU x y
  obtain ⟨hSD, habs, hidx⟩ := hL
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [memG, hSD (Gi x)]
    constructor
    · intro h y hy
      rw [← h1 x, ← h1 y, hfG]
      exact h _ ((memG y).1 hy)
    · intro h y hy
      have := h (G y) ((memG _).2 (by rw [h2]; exact hy))
      rwa [← h1 x, hfG] at this
  · intro x
    obtain ⟨k, hk⟩ := habs (Gi x)
    refine ⟨k, (memG _).2 ?_⟩
    rw [map_smul]
    exact hk
  · have hinj : Function.Injective G.toAddMonoidHom := fun x y h => by
      have := congrArg Gi h
      simpa [h2] using this
    set f : (Fin r → K) →ₗ[O] (Fin r → K) := ϖ • LinearMap.id with hf'
    have hcomm : (L.map G).map f = (L.map f).map G := by
      rw [← Submodule.map_comp, ← Submodule.map_comp]
      congr 1
      ext x
      simp [hf', hG]
    have e : ∀ P : Submodule O (Fin r → K),
        (P.map G).toAddSubgroup = P.toAddSubgroup.map G.toAddMonoidHom := fun P => by
      ext x; simp [Submodule.mem_map]
    unfold idx at hidx ⊢
    rw [← hf'] at hidx ⊢
    rw [hcomm, e, e, AddSubgroup.relIndex_map_map_of_injective _ _ hinj, hidx]

end GlobalTheory.HermNbr

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ _ c cK hc hcK _ r n J hJdet hJh hn C hU hne hinj`. Use `set J' := J.map (algebraMap O K) with hJ'`. Establish `hc2 : ∀ x : K, cK (cK x) = x`. Introduce `x`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := O) x`.

Rewrite using `[map_div₀, map_div₀, hcK, hcK, hcK, hcK, hc, hc]`. Establish `hJ'h : J'.transpose.map cK = J'`. Use extensionality with `i j`. Simplify using `only [hJ', Matrix.map_apply, Matrix.transpose_apply, hcK]`. Use `congrFun (congrFun hJh i) j` as an intermediate fact.

Simplify using `only [Matrix.map_apply, Matrix.transpose_apply] at this`. Rewrite using `[this]`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Use `set Q := Nat.card (IsLocalRing.ResidueField O) with hQdef`. Establish `hQ2 : 2 ≤ Q` using `Finite.one_lt_card`.

Use `set L0 : Submodule O (Fin r → K) := Submodule.span O (Set.range (Pi.basisFun K (Fin r))) with hL0def`. Establish `hL0 : GlobalTheory.HermNbr.Good cK J' ϖ (Q ^ r) L0`. Use `⟨GlobalTheory.HermNbr.std_sd c cK hcK hc2 J hJdet, ?_, GlobalTheory.HermNbr.idx_std hϖ⟩` and prove the remaining obligations. Introduce `x`. Use `choose k hk using fun i => GlobalTheory.HermNbr.exists_pow_mul_mem hϖ (x i)`.

Conclude with `⟨_, GlobalTheory.HermNbr.std_pow_mem_of_le hk⟩`. Use `set φ : GL (Fin r) K → Submodule O (Fin r → K) := fun g => L0.map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) with hφ`. Establish `hgood : ∀ g ∈ C, GlobalTheory.HermNbr.Good cK J' ϖ (Q ^ r) (φ g)` using `fun g hg => GlobalTheory.HermNbr.good_map cK hL0 hϖ g (hU g hg)`. Establish `hQr : (2 : ℝ) ≤ Q` using `by exact_mod_cast hQ2`. Establish `hQ0 : (0 : ℝ) < Q` using `by linarith`.

Establish `hQ1 : (0 : ℝ) < (Q : ℝ) - 1` using `by linarith`. Use `set s : ℝ := (n : ℝ) / 2 with hs`. Use `set D : ℝ := (Q : ℝ) ^ r * Q / ((Q : ℝ) - 1) with hD`. Use `set y : ℝ := (Q : ℝ) ^ (-(2 : ℝ)) with hy`. Establish `hs0 : 0 < s`.

Establish `: (5 : ℝ) ≤ n` using `by exact_mod_cast (by omega : 5 ≤ n)`. Rewrite using `[hs]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hD0 : 0 ≤ D` using `by positivity`. Establish `hy0 : 0 < y` using `Real.rpow_pos_of_pos hQ0 _`.

Establish `hy4 : y ≤ 1 / 4`. Rewrite using `[hy, Real.rpow_neg hQ0.le]`. Rewrite using `[show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]`. Rewrite using `[inv_le_comm₀ (by positivity) (by norm_num)]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hρ : D * (Q : ℝ) ^ (-s) ≤ 2 * y`. Establish `hsr : (r : ℝ) + 5 / 2 ≤ s`. Establish `: ((2 * r + 5 : ℕ) : ℝ) ≤ n` using `by exact_mod_cast hn`. Move the coercions through the operations in `at this`. Rewrite using `[hs]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : (Q : ℝ) ^ (-s) ≤ (Q : ℝ) ^ (-((r : ℝ) + 5 / 2))` using `Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)`. Establish `h2 : (Q : ℝ) ^ (-((r : ℝ) + 5 / 2)) = ((Q : ℝ) ^ r)⁻¹ * ((Q : ℝ) ^ (-(2 : ℝ)) * (Q : ℝ) ^ (-(1 / 2 : ℝ)))`. Rewrite using `[← Real.rpow_add hQ0, show -((r : ℝ) + 5 / 2) = -(r : ℝ) + (-(2 : ℝ) + -(1 / 2 : ℝ)) by ring, Real.rpow_add hQ0, Real.rpow_neg hQ0.le, Real.rpow_natCast]`. Establish `h3 : (Q : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)`.

Establish `h4 : (Q : ℝ) / ((Q : ℝ) - 1) ≤ 2`. Rewrite using `[div_le_iff₀ hQ1]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hQr0 : (0 : ℝ) < (Q : ℝ) ^ r` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[h2, hD, hy]`. Clear the denominators using the available nonvanishing facts. Use `_ ≤ 2 * (y * 1) := by`. Apply `mul_le_mul h4 (mul_le_mul_of_nonneg_left h3 hy0.le) (by positivity) (by norm_num)` to reduce the goal to its premises. Use `_ = 2 * y := by ring`.

Establish `hρ1 : D * (Q : ℝ) ^ (-s) < 1` using `by linarith`. Establish `key` using `GlobalTheory.HermNbr.graph_sum {L | GlobalTheory.HermNbr.Good cK J' ϖ (Q ^ r) L} (fun L Λ => Λ.toAddSubgroup.relIndex L.toAddSubgroup) (GlobalTheory.HermNbr.Nbrs cK J' ϖ) Q hQ2 s D hs0 hD0 hρ1 (fun L _ => AddSubgroup.relIndex_self _) (fun L hL Λ hΛ hne hi => by`. Take `⟨L', h1, h2, h3, h4⟩` from `GlobalTheory.HermNbr.step_exists c cK hcK hc2 hJ'h hϖ hL hΛ hne hi`. Conclude with `⟨L', h1, h2, h3, h4⟩)`. Use the proof step `(fun L hL t ht => by`.

Establish `h` using `GlobalTheory.HermNbr.card_nbrs c cK hcK hc2 hJ'h hϖ hL (by positivity) t ht`. Rewrite using `[hD, le_div_iff₀ hQ1]`. Establish `: ((t.card * (Q - 1) : ℕ) : ℝ) ≤ ((Q ^ r * Q : ℕ) : ℝ)` using `by exact_mod_cast h`. Move the coercions through the operations in `[Nat.cast_sub (by omega : 1 ≤ Q)] at this`. Use the proof step `linarith)`.

Use `L0 hL0 (C.image φ)`. Use the proof step `(by`. Introduce `Λ hΛ`. Take `⟨g, hg, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hΛ)`. Conclude with `hgood g hg)`.

Use the proof step `(by`. Introduce `h`. Take `⟨g, hg, hg'⟩` from `Finset.mem_image.1 h`. Conclude with `hne g hg hg')`. Rewrite `key` using `[Finset.sum_image (fun g hg g' hg' h => hinj g hg g' hg' h)]`.

Establish `hsum : ∀ g ∈ C, (((φ g).toAddSubgroup.relIndex L0.toAddSubgroup : ℕ) : ℝ) ^ (-(n : ℝ) / 2) = (((φ g).toAddSubgroup.relIndex L0.toAddSubgroup : ℕ) : ℝ) ^ (-s)`. Introduce `g _`. Rewrite using `[hs, neg_div]`. Rewrite `key` using `[← Finset.sum_congr rfl hsum]`. Use `le_trans key ?_` and prove the remaining obligations.

Use `set ρ := D * (Q : ℝ) ^ (-s)`. Establish `hρ0 : 0 ≤ ρ` using `by positivity`. Rewrite using `[div_le_iff₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem GlobalTheory.HermNbr.selfDual_sum_le : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (c : O ≃+* O) (cK : K ≃+* K), (∀ x, c (c x) = x) → (∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) → (∃ x, IsUnit (c x - x)) → ∀ (r n : ℕ) (J : Matrix (Fin r) (Fin r) O), IsUnit J.det → J.transpose.map c = J → 2 * r + 5 ≤ n → ∀ C : Finset (GL (Fin r) K), (∀ g ∈ C, ((g : Matrix (Fin r) (Fin r) K).map cK).transpose * J.map (algebraMap O K) * (g : Matrix (Fin r) (Fin r) K) = J.map (algebraMap O K)) → (∀ g ∈ C, (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) ≠ Submodule.span O (Set.range (Pi.basisFun K (Fin r)))) → (∀ g ∈ C, ∀ g' ∈ C, (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) = (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g' : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) → g = g') → ∑ g ∈ C, ((((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)).toAddSubgroup.relIndex (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup : ℕ) : ℝ) ^ (-(n : ℝ) / 2) ≤ 8 * (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ (-(2 : ℝ)) := by
  intro O K _ _ _ _ _ _ _ c cK hc hcK _ r n J hJdet hJh hn C hU hne hinj
  classical
  set J' := J.map (algebraMap O K) with hJ'
  have hc2 : ∀ x : K, cK (cK x) = x := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    rw [map_div₀, map_div₀, hcK, hcK, hcK, hcK, hc, hc]
  have hJ'h : J'.transpose.map cK = J' := by
    ext i j
    simp only [hJ', Matrix.map_apply, Matrix.transpose_apply, hcK]
    have := congrFun (congrFun hJh i) j
    simp only [Matrix.map_apply, Matrix.transpose_apply] at this
    rw [this]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  set Q := Nat.card (IsLocalRing.ResidueField O) with hQdef
  have hQ2 : 2 ≤ Q := Finite.one_lt_card
  set L0 : Submodule O (Fin r → K) := Submodule.span O (Set.range (Pi.basisFun K (Fin r))) with hL0def
  have hL0 : GlobalTheory.HermNbr.Good cK J' ϖ (Q ^ r) L0 := by
    refine ⟨GlobalTheory.HermNbr.std_sd c cK hcK hc2 J hJdet, ?_, GlobalTheory.HermNbr.idx_std hϖ⟩
    intro x
    choose k hk using fun i => GlobalTheory.HermNbr.exists_pow_mul_mem hϖ (x i)
    exact ⟨_, GlobalTheory.HermNbr.std_pow_mem_of_le hk⟩
  set φ : GL (Fin r) K → Submodule O (Fin r → K) := fun g =>
    L0.map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) with hφ
  have hgood : ∀ g ∈ C, GlobalTheory.HermNbr.Good cK J' ϖ (Q ^ r) (φ g) := fun g hg =>
    GlobalTheory.HermNbr.good_map cK hL0 hϖ g (hU g hg)

  have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ2
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hQ1 : (0 : ℝ) < (Q : ℝ) - 1 := by linarith
  set s : ℝ := (n : ℝ) / 2 with hs
  set D : ℝ := (Q : ℝ) ^ r * Q / ((Q : ℝ) - 1) with hD
  set y : ℝ := (Q : ℝ) ^ (-(2 : ℝ)) with hy
  have hs0 : 0 < s := by
    have : (5 : ℝ) ≤ n := by exact_mod_cast (by omega : 5 ≤ n)
    rw [hs]; linarith
  have hD0 : 0 ≤ D := by positivity
  have hy0 : 0 < y := Real.rpow_pos_of_pos hQ0 _
  have hy4 : y ≤ 1 / 4 := by
    rw [hy, Real.rpow_neg hQ0.le]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have hρ : D * (Q : ℝ) ^ (-s) ≤ 2 * y := by
    have hsr : (r : ℝ) + 5 / 2 ≤ s := by
      have : ((2 * r + 5 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at this
      rw [hs]; linarith
    have h1 : (Q : ℝ) ^ (-s) ≤ (Q : ℝ) ^ (-((r : ℝ) + 5 / 2)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 : (Q : ℝ) ^ (-((r : ℝ) + 5 / 2)) = ((Q : ℝ) ^ r)⁻¹ * ((Q : ℝ) ^ (-(2 : ℝ)) * (Q : ℝ) ^ (-(1 / 2 : ℝ))) := by
      rw [← Real.rpow_add hQ0, show -((r : ℝ) + 5 / 2) = -(r : ℝ) + (-(2 : ℝ) + -(1 / 2 : ℝ)) by ring,
        Real.rpow_add hQ0, Real.rpow_neg hQ0.le, Real.rpow_natCast]
    have h3 : (Q : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have h4 : (Q : ℝ) / ((Q : ℝ) - 1) ≤ 2 := by
      rw [div_le_iff₀ hQ1]; linarith
    have hQr0 : (0 : ℝ) < (Q : ℝ) ^ r := by positivity
    calc D * (Q : ℝ) ^ (-s) ≤ D * (Q : ℝ) ^ (-((r : ℝ) + 5 / 2)) := mul_le_mul_of_nonneg_left h1 hD0
      _ = (Q : ℝ) / ((Q : ℝ) - 1) * (y * (Q : ℝ) ^ (-(1 / 2 : ℝ))) := by
          rw [h2, hD, hy]; field_simp
      _ ≤ 2 * (y * 1) := by
          apply mul_le_mul h4 (mul_le_mul_of_nonneg_left h3 hy0.le) (by positivity) (by norm_num)
      _ = 2 * y := by ring
  have hρ1 : D * (Q : ℝ) ^ (-s) < 1 := by linarith

  have key := GlobalTheory.HermNbr.graph_sum {L | GlobalTheory.HermNbr.Good cK J' ϖ (Q ^ r) L}
    (fun L Λ => Λ.toAddSubgroup.relIndex L.toAddSubgroup) (GlobalTheory.HermNbr.Nbrs cK J' ϖ) Q hQ2 s D
    hs0 hD0 hρ1 (fun L _ => AddSubgroup.relIndex_self _)
    (fun L hL Λ hΛ hne hi => by
      obtain ⟨L', h1, h2, h3, h4⟩ :=
        GlobalTheory.HermNbr.step_exists c cK hcK hc2 hJ'h hϖ hL hΛ hne hi
      exact ⟨L', h1, h2, h3, h4⟩)
    (fun L hL t ht => by
      have h := GlobalTheory.HermNbr.card_nbrs c cK hcK hc2 hJ'h hϖ hL (by positivity) t ht
      rw [hD, le_div_iff₀ hQ1]
      have : ((t.card * (Q - 1) : ℕ) : ℝ) ≤ ((Q ^ r * Q : ℕ) : ℝ) := by exact_mod_cast h
      push_cast [Nat.cast_sub (by omega : 1 ≤ Q)] at this
      linarith)
    L0 hL0 (C.image φ)
    (by
      intro Λ hΛ
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hΛ)
      exact hgood g hg)
    (by
      intro h
      obtain ⟨g, hg, hg'⟩ := Finset.mem_image.1 h
      exact hne g hg hg')
  rw [Finset.sum_image (fun g hg g' hg' h => hinj g hg g' hg' h)] at key
  have hsum : ∀ g ∈ C, (((φ g).toAddSubgroup.relIndex L0.toAddSubgroup : ℕ) : ℝ) ^ (-(n : ℝ) / 2) =
      (((φ g).toAddSubgroup.relIndex L0.toAddSubgroup : ℕ) : ℝ) ^ (-s) := by
    intro g _; rw [hs, neg_div]
  rw [← Finset.sum_congr rfl hsum] at key
  refine le_trans key ?_
  set ρ := D * (Q : ℝ) ^ (-s)
  have hρ0 : 0 ≤ ρ := by positivity
  rw [div_le_iff₀ (by linarith)]
  nlinarith
