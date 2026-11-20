import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParahoricSchwartzVanishOffTranslates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsumCharDetFixHyperplaneEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

namespace GlobalTheory.ParahoricPure

section
variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] {r t : ℕ}

/- English proof (translation)
Establish `he : (Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)).map (IsLocalRing.residue O) = Matrix.fromRows (1 : Matrix (Fin r) (Fin r) _) (0 : Matrix (Fin t) (Fin r) _)`. Use extensionality with `i j`. Break down `i with i | i` into its components or cases. Simplify using `[Matrix.one_apply, apply_ite (IsLocalRing.residue O)]`. Simplify using the standard rewrite rules.

Establish `hm` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩`. Use `Matrix.map_injective (IsFractionRing.injective O K) hz` as an intermediate fact. Establish `h0 : IsLocalRing.residue O ϖ = 0`.

Rewrite using `[IsLocalRing.residue_eq_zero_iff, hm]`. Conclude with `Ideal.mem_span_singleton_self _`. Rewrite using `[this, ← he]`. Use extensionality with `i j`. Simplify using `[h0]`.

Introduce `h`. Rewrite `h` using `[← he]`. Establish `: ∀ i j, ∃ c : O, c * ϖ = w i j - Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O) i j`. Introduce `i j`. Rewrite using `[← Ideal.mem_span_singleton', ← hm, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]`.

Conclude with `congrFun (congrFun h i) j`. Use `choose c hc using this`. Use `⟨Matrix.of c, ?_⟩` and prove the remaining obligations. Use `congr 1`. Use extensionality with `i j`.

Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]`. Rewrite using `[mul_comm, hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mem_ball_iff {ϖ : O} (hϖ : Irreducible ϖ) (w : Matrix (Fin r ⊕ Fin t) (Fin r) O) :
    (∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, w.map (algebraMap O K) =
      (Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O) + ϖ • z).map (algebraMap O K)) ↔
    w.map (IsLocalRing.residue O) = Matrix.fromRows (1 : Matrix (Fin r) (Fin r) _) (0 : Matrix (Fin t) (Fin r) _) := by
  have he : (Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)).map (IsLocalRing.residue O)
      = Matrix.fromRows (1 : Matrix (Fin r) (Fin r) _) (0 : Matrix (Fin t) (Fin r) _) := by
    ext i j
    rcases i with i | i
    · simp [Matrix.one_apply, apply_ite (IsLocalRing.residue O)]
    · simp
  have hm := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  constructor
  · rintro ⟨z, hz⟩
    have := Matrix.map_injective (IsFractionRing.injective O K) hz
    have h0 : IsLocalRing.residue O ϖ = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, hm]; exact Ideal.mem_span_singleton_self _
    rw [this, ← he]
    ext i j
    simp [h0]
  · intro h
    rw [← he] at h
    have : ∀ i j, ∃ c : O, c * ϖ = w i j - Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O) i j := by
      intro i j
      rw [← Ideal.mem_span_singleton', ← hm, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact congrFun (congrFun h i) j
    choose c hc using this
    refine ⟨Matrix.of c, ?_⟩
    congr 1
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [mul_comm, hc]; ring

omit [IsDomain O] [IsDiscreteValuationRing O] in
/- English proof (translation)
Rewrite using `[Matrix.fromBlocks_map]`. Simplify using `[Matrix.map_one]`.
-/
theorem map_diag {k : Type} [CommRing k] (f : O →+* k) (L : Matrix (Fin r) (Fin r) O) :
    (Matrix.fromBlocks L 0 0 (1 : Matrix (Fin t) (Fin t) O)).map f = Matrix.fromBlocks (L.map f) 0 0 1 := by
  rw [Matrix.fromBlocks_map]
  simp [Matrix.map_one]

/- English proof (translation)
Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, h]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _ |>.1 g.isUnit).ne_zero`.
-/
theorem isUnit_diag (L : Matrix (Fin r) (Fin r) O) (g : GL (Fin r) (IsLocalRing.ResidueField O))
    (h : L.map (IsLocalRing.residue O) = g.val) :
    IsUnit (Matrix.fromBlocks L 0 0 (1 : Matrix (Fin t) (Fin t) O)) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, h]
  exact (Matrix.isUnit_iff_isUnit_det _ |>.1 g.isUnit).ne_zero

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, mem_ball_iff hϖ, Matrix.map_mul, map_diag]`. Use `conv_lhs => rw [← Matrix.fromRows_toRows (w.map (IsLocalRing.residue O)), Matrix.fromBlocks_mul_fromRows]`. Rewrite using `[Matrix.fromRows_ext_iff]`. Simplify using the standard rewrite rules.
-/
theorem diag_mem_ball_iff {ϖ : O} (hϖ : Irreducible ϖ) (L : Matrix (Fin r) (Fin r) O)
    (w : Matrix (Fin r ⊕ Fin t) (Fin r) O) :
    (∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O,
      (Matrix.fromBlocks L 0 0 (1 : Matrix (Fin t) (Fin t) O)).map (algebraMap O K) * w.map (algebraMap O K) =
      (Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O) + ϖ • z).map (algebraMap O K)) ↔
    (L.map (IsLocalRing.residue O) * (w.map (IsLocalRing.residue O)).toRows₁ = 1 ∧
      (w.map (IsLocalRing.residue O)).toRows₂ = 0) := by
  rw [← Matrix.map_mul, mem_ball_iff hϖ, Matrix.map_mul, map_diag]
  conv_lhs => rw [← Matrix.fromRows_toRows (w.map (IsLocalRing.residue O)), Matrix.fromBlocks_mul_fromRows]
  rw [Matrix.fromRows_ext_iff]
  simp

end

/- English proof (translation)
Establish `hm` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ`. Use `set e : Matrix (Fin r ⊕ Fin t) (Fin r) O := Matrix.fromRows 1 0 with he`. Establish `her : e.map (IsLocalRing.residue O) = Matrix.fromRows 1 0` using `(mem_ball_iff (K := K) hϖ e).1 ⟨0, by simp [he]⟩`. Establish `law : ∀ h : GL (Fin r ⊕ Fin t) O, (h.val.map (IsLocalRing.residue O)).toBlocks₂₁ = 0 → ∀ u : (IsLocalRing.ResidueField O)ˣ, (u : IsLocalRing.ResidueField O) = (h.val.map (IsLocalRing.residue O)).toBlocks₁₁.det → ∀ m, Φ (h.val.map (algebraMap O K) * m) = ((ξ u : ℂˣ) : ℂ)⁻¹ * Φ m`. Introduce `h hh u hu m`.

Establish `h1` using `H3 h hh m (e.map (algebraMap O K))`. Establish `h2 : (h.val * e).map (IsLocalRing.residue O) = Matrix.fromRows (h.val.map (IsLocalRing.residue O)).toBlocks₁₁ 0`. Rewrite using `[Matrix.map_mul, her]`. Use `conv_lhs => rw [← Matrix.fromBlocks_toBlocks (h.val.map (IsLocalRing.residue O)), Matrix.fromBlocks_mul_fromRows]`. Simplify using `[hh]`.

Rewrite `h1` using `[H0 e 1 (by simp [her]) (by simp [her]), ← Matrix.map_mul, H0 (h.val * e) u (by simp [h2]) (by simp [h2, hu])]`. Simplify `h1` using `[mul_comm]`. Establish `lawD : ∀ (L : Matrix (Fin r) (Fin r) O) (g : GL (Fin r) (IsLocalRing.ResidueField O)), L.map (IsLocalRing.residue O) = g.val → ∀ m, Φ ((Matrix.fromBlocks L 0 0 (1 : Matrix (Fin t) (Fin t) O)).map (algebraMap O K) * m) = ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * Φ m`. Introduce `L g hg m`. Use `law (isUnit_diag (t := t) L g hg).unit (by rw [IsUnit.unit_spec, map_diag]; simp) (Matrix.GeneralLinearGroup.det g) (by rw [IsUnit.unit_spec, map_diag, hg]; simp) m` as an intermediate fact.

Rewrite `this` using `[IsUnit.unit_spec]`. Then use the resulting hypothesis. Establish `hspan` using `GlobalTheory.parahoric_schwartz_mem_span_translates O K r t ϖ hϖ Φ H2 ?_ ?_`. Use `rotate_left`. Introduce `h ha hb x`. Use `law h ?_ 1 ?_ x` as an intermediate fact.

Simplify using `using this`. Use extensionality with `a b`. Simplify using `only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.map_apply, Matrix.zero_apply]`. Rewrite using `[IsLocalRing.residue_eq_zero_iff, hm]`. Conclude with `hb a b`.

Establish `: (h.val.map (IsLocalRing.residue O)).toBlocks₁₁ = 1`. Use extensionality with `a b`. Use `ha a b` as an intermediate fact. Rewrite `this` using `[← hm, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]`. Simplify using `only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.map_apply, this]`.

Simplify using `[Matrix.one_apply, apply_ite (IsLocalRing.residue O)]`. Simplify using `[this]`. Introduce `a ha lift hl x`. Establish `h0` using `GlobalTheory.finsum_char_det_fix_hyperplane_eq_zero (IsLocalRing.ResidueField O) r ξ⁻¹ (inv_ne_one.2 hξ) a ha`. Rewrite using `[finsum_mem_congr rfl (fun g _ => lawD (lift g) g (hl g) x), ← finsum_mem_mul]`.

Simplify using `only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val] at h0`. Rewrite using `[h0, zero_mul]`. Establish `hsurj : ∀ g : GL (Fin r) (IsLocalRing.ResidueField O), ∃ L : Matrix (Fin r) (Fin r) O, L.map (IsLocalRing.residue O) = g.val`. Introduce `g`. Establish `hs' : ∀ i j, ∃ o : O, IsLocalRing.residue O o = g.val i j` using `fun i j => IsLocalRing.residue_surjective _`.

Use `choose L hL using hs'`. Conclude with `⟨Matrix.of L, by ext i j; exact hL i j⟩`. Use `choose lift hl using hsurj`. Use `letI : Fintype (GL (Fin r) (IsLocalRing.ResidueField O)) := Fintype.ofFinite _`. Set `D : GL (Fin r) (IsLocalRing.ResidueField O) → Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) K` to `fun g => (Matrix.fromBlocks (lift g) 0 0 (1 : Matrix (Fin t) (Fin t) O)).map (algebraMap O K)`.

Set `A : (Matrix (Fin r ⊕ Fin t) (Fin r) K → ℂ) →ₗ[ℂ] (Matrix (Fin r ⊕ Fin t) (Fin r) K → ℂ)` to `∑ g, ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • LinearMap.funLeft ℂ ℂ (fun x => D g * x)`. Establish `hA : ∀ Ψ x, A Ψ x = ∑ g, ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * Ψ (D g * x)`. Introduce `Ψ x`. Simplify using `[A, LinearMap.sum_apply, Finset.sum_apply, LinearMap.funLeft_apply]`. Establish `hAΦ : A Φ = (Fintype.card (GL (Fin r) (IsLocalRing.ResidueField O)) : ℂ) • Φ`.

Use function extensionality and compare the values at `x`. Rewrite using `[hA]`. Simplify using `only [D, lawD _ _ (hl _)]`. Simplify using `[← mul_assoc]`. Establish `key : ∀ y : Matrix (Fin r ⊕ Fin t) (Fin r) K, ∑ g, ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * (if ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, D g * y = (e + ϖ • z).map (algebraMap O K) then 1 else 0) = Φ₀ y`.

Introduce `y`. Distinguish the cases in `hy : ∃ g, ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, D g * y = (e + ϖ • z).map (algebraMap O K)`. Take `⟨g, hg⟩` from `hy`. Choose the witnesses or unpack the hypotheses as in `⟨w, rfl⟩ : ∃ w : Matrix (Fin r ⊕ Fin t) (Fin r) O, y = w.map (algebraMap O K) := by`. Take `⟨z, hz⟩` from `hg`.

Take `⟨U, hU⟩` from `isUnit_diag (t := t) (lift g) g (hl g)`. Use `⟨(U⁻¹).val * (e + ϖ • z), ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.map_mul, ← hz]`. Simplify using `only [D]`. Rewrite using `[← hU, ← Matrix.mul_assoc, ← Matrix.map_mul, Units.inv_mul]`.

Simplify using `[Matrix.map_one]`. Establish `hg'` using `(diag_mem_ball_iff hϖ (lift g) w).1 hg`. Rewrite `hg'` using `[hl]`. Rewrite using `[Finset.sum_eq_single g, if_pos hg, mul_one, H0 w (Matrix.GeneralLinearGroup.det g)⁻¹ hg'.2]`. Simplify using the standard rewrite rules.

Use `congrArg Matrix.det hg'.1` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_one]`. Rewrite using `[Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply]`. Conclude with `(eq_inv_of_mul_eq_one_right this).symm`. Introduce `g' _ hne`.

Rewrite using `[if_neg, mul_zero]`. Introduce `h'`. Establish `h2` using `((diag_mem_ball_iff hϖ (lift g') w).1 h').1`. Rewrite `h2` using `[hl]`. Apply `hne` to reduce the goal to its premises.

Use `ext1`. Conclude with `Matrix.left_inv_eq_left_inv h2 hg'.1`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_eq_zero (fun g _ => by rw [if_neg (fun h => hy ⟨g, h⟩), mul_zero])]`. Assume the negation of the conclusion as `h0`.

Take `⟨w, rfl, h2, h1⟩` from `H1 y (Ne.symm h0)`. Take `⟨g, hg⟩` from `(Matrix.isUnit_iff_isUnit_det _).2 h1`. Use `hy ⟨g⁻¹, (diag_mem_ball_iff hϖ (lift g⁻¹) w).2 ⟨?_, h2⟩⟩` and prove the remaining obligations. Rewrite using `[hl, ← hg, Units.inv_mul]`. Establish `hc : (Fintype.card (GL (Fin r) (IsLocalRing.ResidueField O)) : ℂ) ≠ 0`.

Conclude with `Fintype.card_ne_zero` after adjusting the coercions. Rewrite using `[← Submodule.smul_mem_iff _ hc, ← hAΦ]`. Use `Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap A _)).2 ?_ hspan)` and prove the remaining obligations. Introduce and unpack `Ψ ⟨γ, rfl⟩`. Use `Submodule.subset_span ⟨γ, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `x`. Rewrite using `[hA, ← key]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Simplify using `only [Set.indicator_apply, Set.mem_setOf_eq, Matrix.mul_assoc]`. Reduce the equality to equality of the corresponding arguments.
-/
theorem mem_span_sum (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ)
    (ϖ : O) (hϖ : Irreducible ϖ) (ξ : (IsLocalRing.ResidueField O)ˣ →* ℂˣ) (hξ : ξ ≠ 1)
    (Φ Φ₀ : Matrix (Fin r ⊕ Fin t) (Fin r) K → ℂ)
    (H0 : ∀ (z : Matrix (Fin r ⊕ Fin t) (Fin r) O) (u : (IsLocalRing.ResidueField O)ˣ),
      (z.map (IsLocalRing.residue O)).toRows₂ = 0 →
      (u : IsLocalRing.ResidueField O) = (z.map (IsLocalRing.residue O)).toRows₁.det →
      Φ₀ (z.map (algebraMap O K)) = ((ξ u : ℂˣ) : ℂ)⁻¹)
    (H1 : ∀ m, Φ₀ m ≠ 0 → ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, m = z.map (algebraMap O K) ∧
      (z.map (IsLocalRing.residue O)).toRows₂ = 0 ∧ IsUnit (z.map (IsLocalRing.residue O)).toRows₁.det)
    (H2 : ∃ N : ℕ, (∀ m (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), Φ (m + (ϖ ^ N • z).map (algebraMap O K)) = Φ m) ∧
      ∀ m, Φ m ≠ 0 → ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, algebraMap O K (ϖ ^ N) • m = z.map (algebraMap O K))
    (H3 : ∀ h : GL (Fin r ⊕ Fin t) O, (h.val.map (IsLocalRing.residue O)).toBlocks₂₁ = 0 →
      ∀ m m' : Matrix (Fin r ⊕ Fin t) (Fin r) K,
        Φ (h.val.map (algebraMap O K) * m) * Φ₀ m' = Φ m * Φ₀ (h.val.map (algebraMap O K) * m')) :
    Φ ∈ Submodule.span ℂ {Ψ | ∃ γ : GL (Fin r) K, Ψ = fun m => Φ₀ (m * γ.val)} := by
  classical
  have hm := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  set e : Matrix (Fin r ⊕ Fin t) (Fin r) O := Matrix.fromRows 1 0 with he
  have her : e.map (IsLocalRing.residue O) = Matrix.fromRows 1 0 :=
    (mem_ball_iff (K := K) hϖ e).1 ⟨0, by simp [he]⟩
  have law : ∀ h : GL (Fin r ⊕ Fin t) O, (h.val.map (IsLocalRing.residue O)).toBlocks₂₁ = 0 →
      ∀ u : (IsLocalRing.ResidueField O)ˣ,
        (u : IsLocalRing.ResidueField O) = (h.val.map (IsLocalRing.residue O)).toBlocks₁₁.det →
        ∀ m, Φ (h.val.map (algebraMap O K) * m) = ((ξ u : ℂˣ) : ℂ)⁻¹ * Φ m := by
    intro h hh u hu m
    have h1 := H3 h hh m (e.map (algebraMap O K))
    have h2 : (h.val * e).map (IsLocalRing.residue O) =
        Matrix.fromRows (h.val.map (IsLocalRing.residue O)).toBlocks₁₁ 0 := by
      rw [Matrix.map_mul, her]
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks (h.val.map (IsLocalRing.residue O)), Matrix.fromBlocks_mul_fromRows]
      simp [hh]
    rw [H0 e 1 (by simp [her]) (by simp [her]), ← Matrix.map_mul, H0 (h.val * e) u (by simp [h2]) (by simp [h2, hu])] at h1
    simpa [mul_comm] using h1
  have lawD : ∀ (L : Matrix (Fin r) (Fin r) O) (g : GL (Fin r) (IsLocalRing.ResidueField O)),
      L.map (IsLocalRing.residue O) = g.val → ∀ m,
      Φ ((Matrix.fromBlocks L 0 0 (1 : Matrix (Fin t) (Fin t) O)).map (algebraMap O K) * m) =
        ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * Φ m := by
    intro L g hg m
    have := law (isUnit_diag (t := t) L g hg).unit (by rw [IsUnit.unit_spec, map_diag]; simp)
      (Matrix.GeneralLinearGroup.det g) (by rw [IsUnit.unit_spec, map_diag, hg]; simp) m
    rwa [IsUnit.unit_spec] at this
  have hspan := GlobalTheory.parahoric_schwartz_mem_span_translates O K r t ϖ hϖ Φ H2 ?_ ?_
  rotate_left
  · intro h ha hb x
    have := law h ?_ 1 ?_ x
    · simpa using this
    · ext a b
      simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.map_apply, Matrix.zero_apply]
      rw [IsLocalRing.residue_eq_zero_iff, hm]; exact hb a b
    · have : (h.val.map (IsLocalRing.residue O)).toBlocks₁₁ = 1 := by
        ext a b
        have := ha a b
        rw [← hm, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at this
        simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.map_apply, this]
        simp [Matrix.one_apply, apply_ite (IsLocalRing.residue O)]
      simp [this]
  · intro a ha lift hl x
    have h0 := GlobalTheory.finsum_char_det_fix_hyperplane_eq_zero (IsLocalRing.ResidueField O) r ξ⁻¹ (inv_ne_one.2 hξ) a ha
    rw [finsum_mem_congr rfl (fun g _ => lawD (lift g) g (hl g) x), ← finsum_mem_mul]
    simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val] at h0
    rw [h0, zero_mul]
  have hsurj : ∀ g : GL (Fin r) (IsLocalRing.ResidueField O), ∃ L : Matrix (Fin r) (Fin r) O,
      L.map (IsLocalRing.residue O) = g.val := by
    intro g
    have hs' : ∀ i j, ∃ o : O, IsLocalRing.residue O o = g.val i j :=
      fun i j => IsLocalRing.residue_surjective _
    choose L hL using hs'
    exact ⟨Matrix.of L, by ext i j; exact hL i j⟩
  choose lift hl using hsurj
  letI : Fintype (GL (Fin r) (IsLocalRing.ResidueField O)) := Fintype.ofFinite _
  let D : GL (Fin r) (IsLocalRing.ResidueField O) → Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) K := fun g =>
    (Matrix.fromBlocks (lift g) 0 0 (1 : Matrix (Fin t) (Fin t) O)).map (algebraMap O K)
  let A : (Matrix (Fin r ⊕ Fin t) (Fin r) K → ℂ) →ₗ[ℂ] (Matrix (Fin r ⊕ Fin t) (Fin r) K → ℂ) :=
    ∑ g, ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • LinearMap.funLeft ℂ ℂ (fun x => D g * x)
  have hA : ∀ Ψ x, A Ψ x = ∑ g, ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * Ψ (D g * x) := by
    intro Ψ x
    simp [A, LinearMap.sum_apply, Finset.sum_apply, LinearMap.funLeft_apply]
  have hAΦ : A Φ = (Fintype.card (GL (Fin r) (IsLocalRing.ResidueField O)) : ℂ) • Φ := by
    funext x
    rw [hA]
    simp only [D, lawD _ _ (hl _)]
    simp [← mul_assoc]
  have key : ∀ y : Matrix (Fin r ⊕ Fin t) (Fin r) K,
      ∑ g, ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        (if ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, D g * y = (e + ϖ • z).map (algebraMap O K) then 1 else 0) = Φ₀ y := by
    intro y
    by_cases hy : ∃ g, ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, D g * y = (e + ϖ • z).map (algebraMap O K)
    · obtain ⟨g, hg⟩ := hy
      obtain ⟨w, rfl⟩ : ∃ w : Matrix (Fin r ⊕ Fin t) (Fin r) O, y = w.map (algebraMap O K) := by
        obtain ⟨z, hz⟩ := hg
        obtain ⟨U, hU⟩ := isUnit_diag (t := t) (lift g) g (hl g)
        refine ⟨(U⁻¹).val * (e + ϖ • z), ?_⟩
        rw [Matrix.map_mul, ← hz]
        simp only [D]
        rw [← hU, ← Matrix.mul_assoc, ← Matrix.map_mul, Units.inv_mul]
        simp [Matrix.map_one]
      have hg' := (diag_mem_ball_iff hϖ (lift g) w).1 hg
      rw [hl] at hg'
      rw [Finset.sum_eq_single g, if_pos hg, mul_one,
        H0 w (Matrix.GeneralLinearGroup.det g)⁻¹ hg'.2]
      · simp
      · have := congrArg Matrix.det hg'.1
        rw [Matrix.det_mul, Matrix.det_one] at this
        rw [Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply]
        exact (eq_inv_of_mul_eq_one_right this).symm
      · intro g' _ hne
        rw [if_neg, mul_zero]
        intro h'
        have h2 := ((diag_mem_ball_iff hϖ (lift g') w).1 h').1
        rw [hl] at h2
        apply hne
        ext1
        exact Matrix.left_inv_eq_left_inv h2 hg'.1
      · simp
    · rw [Finset.sum_eq_zero (fun g _ => by rw [if_neg (fun h => hy ⟨g, h⟩), mul_zero])]
      by_contra h0
      obtain ⟨w, rfl, h2, h1⟩ := H1 y (Ne.symm h0)
      obtain ⟨g, hg⟩ := (Matrix.isUnit_iff_isUnit_det _).2 h1
      refine hy ⟨g⁻¹, (diag_mem_ball_iff hϖ (lift g⁻¹) w).2 ⟨?_, h2⟩⟩
      rw [hl, ← hg, Units.inv_mul]
  have hc : (Fintype.card (GL (Fin r) (IsLocalRing.ResidueField O)) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [← Submodule.smul_mem_iff _ hc, ← hAΦ]
  refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap A _)).2 ?_ hspan)
  rintro Ψ ⟨γ, rfl⟩
  refine Submodule.subset_span ⟨γ, ?_⟩
  funext x
  rw [hA, ← key]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Matrix.mul_assoc]
  congr

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `a b`. Conclude with `h _ _ (by simp) b.2`. Introduce `h i j hi _`.

Take `⟨a, rfl⟩` from `finSumFinEquiv.surjective i`. Break down `a with a | a` into its components or cases. Use `a.2` as an intermediate fact. Simplify using `at hi`. Use linear arithmetic over natural numbers and integers.

Conclude with `congrFun (congrFun h a) j`.
-/
theorem lowZero_iff {κ : Type} [Zero κ] {r t : ℕ} (y : Matrix (Fin (r + t)) (Fin r) κ) :
    LowZero r y ↔ Matrix.toRows₂ (y.submatrix finSumFinEquiv id) = 0 := by
  constructor
  · intro h
    ext a b
    exact h _ _ (by simp) b.2
  · intro h i j hi _
    obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
    rcases a with a | a
    · have := a.2
      simp at hi
      omega
    · exact congrFun (congrFun h a) j

/- English proof (translation)
Use extensionality with `a b`. Unfold `topL`. Rewrite using `[dif_pos ⟨by have := a.2; omega, b.2⟩]`. Both sides reduce to the same expression.
-/
theorem topL_eq {κ : Type} [Zero κ] {r t : ℕ} (y : Matrix (Fin (r + t)) (Fin r) κ) :
    topL r y = Matrix.toRows₁ (y.submatrix finSumFinEquiv id) := by
  ext a b
  unfold topL
  rw [dif_pos ⟨by have := a.2; omega, b.2⟩]
  rfl

/- English proof (translation)
Introduce `i j hi hj`. Take `⟨a, rfl⟩` from `finSumFinEquiv.surjective i`. Take `⟨b, rfl⟩` from `finSumFinEquiv.surjective j`. Break down `a with a | a` into its components or cases. Use `a.2` as an intermediate fact.

Simplify using `at hi`. Use linear arithmetic over natural numbers and integers. Break down `b with b | b` into its components or cases. Simplify `congrFun (congrFun h a) b` using `[Matrix.toBlocks₂₁]`. Simplify using `at hj`.
-/
theorem lowZero_of_toBlocks {κ : Type} [Zero κ] {r t : ℕ} (y : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) κ)
    (h : y.toBlocks₂₁ = 0) : LowZero r (y.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) := by
  intro i j hi hj
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
  rcases a with a | a
  · have := a.2
    simp at hi
    omega
  · rcases b with b | b
    · simpa [Matrix.toBlocks₂₁] using congrFun (congrFun h a) b
    · simp at hj

end GlobalTheory.ParahoricPure

namespace GlobalTheory

open ParahoricPure in

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ _ n r hr ϖ hϖ ξ hξ Φ Φ₀ H0 H1 H2 H3`. Take `⟨t, rfl⟩` from `Nat.exists_eq_add_of_le hr`. Set `e : Fin r ⊕ Fin t ≃ Fin (r + t)` to `finSumFinEquiv`. Establish `hs` using `mem_span_sum O K r t ϖ hϖ ξ hξ (fun x => Φ (x.submatrix e.symm id)) (fun x => Φ₀ (x.submatrix e.symm id)) ?_ ?_ ?_ ?_`. Set `R : (Matrix (Fin r ⊕ Fin t) (Fin r) K → ℂ) →ₗ[ℂ] (Matrix (Fin (r + t)) (Fin r) K → ℂ)` to `LinearMap.funLeft ℂ ℂ (fun x => x.submatrix e id)`.

Establish `hR : R (fun x => Φ (x.submatrix e.symm id)) = Φ`. Use function extensionality and compare the values at `x`. Simplify using `[R, LinearMap.funLeft_apply, Matrix.submatrix_submatrix]`. Rewrite using `[← hR]`. Use `Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap R _)).2 ?_ hs)` and prove the remaining obligations.

Introduce and unpack `Ψ ⟨γ, rfl⟩`. Use `Submodule.subset_span ⟨γ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify using `only [R, LinearMap.funLeft_apply]`. Use `congr 1`.

Use extensionality with `i j`. Simplify using `[Matrix.mul_apply]`. Introduce `z u h1 h2`. Use `H0 (z.submatrix e.symm id) u ?_ ?_` and prove the remaining obligations. Rewrite using `[lowZero_iff, ← h1]`.

Use `congr 1`. Use extensionality with `i j`. Simplify using `[e]`. Rewrite using `[topL_eq, h2]`. Use `congr 2`.

Use extensionality with `i j`. Simplify using `[e]`. Introduce `m hm`. Take `⟨z, h1, h2, h3⟩` from `H1 _ hm`. Use `⟨z.submatrix e id, ?_, (lowZero_iff _).1 h2, by rw [topL_eq] at h3; exact h3⟩` and prove the remaining obligations.

Use extensionality with `i j`. Simplify using `using congrFun (congrFun h1 (e i)) j`. Take `⟨N, h1, h2⟩` from `H2`. Use `⟨N, fun m z => h1 (m.submatrix e.symm id) (z.submatrix e.symm id), fun m hm => ?_⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `h2 _ hm`.

Use `⟨z.submatrix e id, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `using congrFun (congrFun hz (e i)) j`. Introduce `h hh m m'`. Set `h' : GL (Fin (r + t)) O` to `Units.map (Matrix.reindexAlgEquiv O O e).toMonoidHom h`.

Establish `hv : h'.val = h.val.submatrix e.symm e.symm` using `rfl`. Establish `hmul : ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, (h.val.map (algebraMap O K) * x).submatrix e.symm id = h'.val.map (algebraMap O K) * x.submatrix e.symm id`. Introduce `x`. Rewrite using `[hv, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv]`. Simplify using `only [hmul]`.

Conclude with `H3 h' (lowZero_of_toBlocks _ hh) _ _`.
-/
theorem parahoric_schwartz_mem_span_datum_translates : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (n r : ℕ), r ≤ n → ∀ ϖ : O, Irreducible ϖ → ∀ ξ : (IsLocalRing.ResidueField O)ˣ →* ℂˣ, ξ ≠ 1 → ∀ Φ Φ₀ : Matrix (Fin n) (Fin r) K → ℂ, (∀ (z : Matrix (Fin n) (Fin r) O) (u : (IsLocalRing.ResidueField O)ˣ), LowZero r (z.map (IsLocalRing.residue O)) → (u : IsLocalRing.ResidueField O) = (topL r (z.map (IsLocalRing.residue O))).det → Φ₀ (z.map (algebraMap O K)) = ((ξ u : ℂˣ) : ℂ)⁻¹) → (∀ m, Φ₀ m ≠ 0 → ∃ z : Matrix (Fin n) (Fin r) O, m = z.map (algebraMap O K) ∧ LowZero r (z.map (IsLocalRing.residue O)) ∧ IsUnit (topL r (z.map (IsLocalRing.residue O))).det) → (∃ N : ℕ, (∀ m (z : Matrix (Fin n) (Fin r) O), Φ (m + (ϖ ^ N • z).map (algebraMap O K)) = Φ m) ∧ ∀ m, Φ m ≠ 0 → ∃ z : Matrix (Fin n) (Fin r) O, algebraMap O K (ϖ ^ N) • m = z.map (algebraMap O K)) → (∀ h : GL (Fin n) O, LowZero r (h.val.map (IsLocalRing.residue O)) → ∀ m m' : Matrix (Fin n) (Fin r) K, Φ (h.val.map (algebraMap O K) * m) * Φ₀ m' = Φ m * Φ₀ (h.val.map (algebraMap O K) * m')) → Φ ∈ Submodule.span ℂ {Ψ | ∃ γ : GL (Fin r) K, Ψ = fun m => Φ₀ (m * γ.val)} := by
  intro O K _ _ _ _ _ _ _ n r hr ϖ hϖ ξ hξ Φ Φ₀ H0 H1 H2 H3
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hr
  let e : Fin r ⊕ Fin t ≃ Fin (r + t) := finSumFinEquiv
  have hs := mem_span_sum O K r t ϖ hϖ ξ hξ (fun x => Φ (x.submatrix e.symm id))
    (fun x => Φ₀ (x.submatrix e.symm id)) ?_ ?_ ?_ ?_
  · let R : (Matrix (Fin r ⊕ Fin t) (Fin r) K → ℂ) →ₗ[ℂ] (Matrix (Fin (r + t)) (Fin r) K → ℂ) :=
      LinearMap.funLeft ℂ ℂ (fun x => x.submatrix e id)
    have hR : R (fun x => Φ (x.submatrix e.symm id)) = Φ := by
      funext x
      simp [R, LinearMap.funLeft_apply, Matrix.submatrix_submatrix]
    rw [← hR]
    refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap R _)).2 ?_ hs)
    rintro Ψ ⟨γ, rfl⟩
    refine Submodule.subset_span ⟨γ, ?_⟩
    funext x
    simp only [R, LinearMap.funLeft_apply]
    congr 1
    ext i j
    simp [Matrix.mul_apply]
  · intro z u h1 h2
    refine H0 (z.submatrix e.symm id) u ?_ ?_
    · rw [lowZero_iff, ← h1]; congr 1; ext i j; simp [e]
    · rw [topL_eq, h2]; congr 2; ext i j; simp [e]
  · intro m hm
    obtain ⟨z, h1, h2, h3⟩ := H1 _ hm
    refine ⟨z.submatrix e id, ?_, (lowZero_iff _).1 h2, by rw [topL_eq] at h3; exact h3⟩
    ext i j
    simpa using congrFun (congrFun h1 (e i)) j
  · obtain ⟨N, h1, h2⟩ := H2
    refine ⟨N, fun m z => h1 (m.submatrix e.symm id) (z.submatrix e.symm id), fun m hm => ?_⟩
    obtain ⟨z, hz⟩ := h2 _ hm
    refine ⟨z.submatrix e id, ?_⟩
    ext i j
    simpa using congrFun (congrFun hz (e i)) j
  · intro h hh m m'
    let h' : GL (Fin (r + t)) O := Units.map (Matrix.reindexAlgEquiv O O e).toMonoidHom h
    have hv : h'.val = h.val.submatrix e.symm e.symm := rfl
    have hmul : ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, (h.val.map (algebraMap O K) * x).submatrix e.symm id =
        h'.val.map (algebraMap O K) * x.submatrix e.symm id := by
      intro x
      rw [hv, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv]
    simp only [hmul]
    exact H3 h' (lowZero_of_toBlocks _ hh) _ _

end GlobalTheory
