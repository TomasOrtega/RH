import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenDecompositionIffShiftedProductsKillComaximaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

noncomputable section
namespace GlobalTheory.UPel.HT.LieLin
open Matrix

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem ringHom_mapMatrix_algebraMap_scalar {B T : Type} [CommRing B] [CommRing T] (f : B →+* T) {n : ℕ} (x : B) :
    f.mapMatrix (algebraMap B (Matrix (Fin n) (Fin n) B) x) = algebraMap T (Matrix (Fin n) (Fin n) T) (f x) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `h : (List.ofFn fun i => matAct M f (c i) - algebraMap T (Module.End T (Fin n → T)) (τ i (c i))) = (List.ofFn fun i => (M (c i)).map f - algebraMap T (Matrix (Fin n) (Fin n) T) (τ i (c i))).map (Matrix.toLinAlgEquiv' (R` using `T) (n := Fin n)) := by`. Rewrite using `[List.map_ofFn]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply, map_sub, AlgEquiv.commutes]`.

Both sides reduce to the same expression. Rewrite using `[h, ← map_list_prod]`. Both sides reduce to the same expression.
-/
theorem list_prod_matrixActionAfterRingHom_sub_apply {O T : Type} [CommRing O] [CommRing T] {n : ℕ} {B : Type} [CommRing B]
    (M : O →+* Matrix (Fin n) (Fin n) B) (f : B →+* T) {a : ℕ} (c : Fin a → O) (τ : Fin a → (O →+* T))
    (v : Fin n → T) :
    (List.ofFn fun i => matAct M f (c i) - algebraMap T (Module.End T (Fin n → T)) (τ i (c i))).prod v =
      (List.ofFn fun i => (M (c i)).map f - algebraMap T (Matrix (Fin n) (Fin n) T) (τ i (c i))).prod *ᵥ v := by
  have h : (List.ofFn fun i => matAct M f (c i) - algebraMap T (Module.End T (Fin n → T)) (τ i (c i))) =
      (List.ofFn fun i => (M (c i)).map f - algebraMap T (Matrix (Fin n) (Fin n) T) (τ i (c i))).map
        (Matrix.toLinAlgEquiv' (R := T) (n := Fin n)) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    simp only [Function.comp_apply, map_sub, AlgEquiv.commutes]
    rfl
  rw [h, ← map_list_prod]
  rfl

/- English proof (translation)
Introduce `p _ D R _ b B _ βB n M T _ f`. Use `set g : R →+* T := f.comp βB with hg`. Use `set τ : Fin D.a → (𝓞 D.F →+* T) := fun i => g.comp (b.t i) with hτ`. Use `set ρ' : T := g b.ρ with hρ'`. Use `set Nh : 𝓞 D.F →+* Matrix (Fin n) (Fin n) T := f.mapMatrix.comp M with hNh`.

Set `Am : T →+* Matrix (Fin n) (Fin n) T` to `algebraMap T (Matrix (Fin n) (Fin n) T)`. Use `set P : (Fin D.a → 𝓞 D.F) → Matrix (Fin n) (Fin n) T := fun c => (List.ofFn fun i => (M (c i)).map f - Am (τ i (c i))).prod with hP`. Use `set Q : Matrix (Fin n) (Fin n) T := Nh D.ω - Am (g ((D.tr : R) - b.ρ)) with hQ`. Establish `hmap : ∀ c, f.mapMatrix (lieMat b βB M c) = P c * Q`. Introduce `c`.

Rewrite using `[lieMat, map_mul, map_list_prod, List.map_ofFn]`. Use `congr 1`. Use `congr 2`. Use function extensionality and compare the values at `i`. Rewrite using `[Function.comp_apply, map_sub, ringHom_mapMatrix_algebraMap_scalar]`.

Both sides reduce to the same expression. Rewrite using `[map_sub, ringHom_mapMatrix_algebraMap_scalar]`. Both sides reduce to the same expression. Establish `hdec : ∀ v, (∃ w : Fin D.a → (Fin n → T), (∀ i, w i ∈ eigSub (matAct M f) (τ i)) ∧ v = ∑ i, w i) ↔ ∀ c, P c *ᵥ v = 0`. Introduce `v`.

Establish `hcomax : ∀ i j, i ≠ j → Ideal.span (Set.range fun x => τ i x - τ j x) = ⊤`. Introduce `i j hij`. Establish `h` using `congrArg (Ideal.map g) (b.comax i j hij)`. Rewrite `h` using `[Ideal.map_span, Ideal.map_top, ← Set.range_comp]`. Use `h using 3` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `x`. Simplify using `[hτ]`. Rewrite using `[GlobalTheory.T.eigenDecomposition_iff_shiftedProducts_kill_comaximal (𝓞 D.F) T (Fin n → T) (matAct M f) D.a τ hcomax v]`. Simplify using `only [list_prod_matrixActionAfterRingHom_sub_apply, hP]`. Both sides reduce to the same expression.

Establish `hω : D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0`. Rewrite using `[← D.tr_eq, ← D.nm_eq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hρ : ρ' * ρ' - (D.tr : T) * ρ' + (D.nm : T) = 0`. Use `congrArg g b.ρ_root` as an intermediate fact.

Simplify using `only [map_add, map_sub, map_mul, map_pow, map_intCast, map_zero] at this`. Rewrite using `[hρ']`. Take the linear combination `this`. Establish `hquad : (Nh D.ω - Am ρ') * Q = 0`. Establish `hX : Nh D.ω * Nh D.ω - Am (D.tr : T) * Nh D.ω + Am (D.nm : T) = 0`.

Use `congrArg Nh hω` as an intermediate fact. Simplify `this` using `[map_intCast]`. Establish `hs : g ((D.tr : R) - b.ρ) = (D.tr : T) - ρ'` using `by simp [hρ']`. Rewrite using `[hQ, hs]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[map_add, map_mul, sub_mul, mul_sub, mul_sub, add_mul, ← Algebra.commutes ((D.tr : T) - ρ') (Nh D.ω)]`. Normalize the expressions using the abelian group laws. Use `_ = Nh D.ω * Nh D.ω - Am (D.tr : T) * Nh D.ω + Am (D.nm : T) := by`. Use `congr 2`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Use `congr 1`. Take the linear combination `-hρ`. Use `_ = 0 := hX`. Establish `hAm : ∀ (x : T) (v : Fin n → T), Am x *ᵥ v = x • v`.

Introduce `x v`. Simplify using `only [Am, Algebra.algebraMap_eq_smul_one]`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.one_apply]`. Establish `hact : ∀ v, matAct M f D.ω v = Nh D.ω *ᵥ v` using `fun v => rfl`.

Establish `hs : g ((D.tr : R) - b.ρ) = (D.tr : T) - ρ'` using `by simp [hρ']`. Establish `hu : IsUnit (ρ' - ((D.tr : T) - ρ'))`. Take `⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = 4 * D.nm - D.tr ^ 2` from `⟨(4 * D.nm - D.tr ^ 2).toNat, Int.toNat_of_nonneg (by have := D.disc_neg; omega)⟩`. Establish `hkp : k.Coprime p`. Rewrite using `[Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out)]`.

Introduce `hd`. Apply `D.disc_p` to reduce the goal to its premises. Establish `: (p : ℤ) ∣ (k : ℤ)` using `Int.natCast_dvd_natCast.2 hd`. Rewrite `this` using `[hk]`. Establish `h2 : D.tr ^ 2 - 4 * D.nm = -(4 * D.nm - D.tr ^ 2)` using `by ring`.

Rewrite using `[h2]`. Conclude with `(dvd_neg).2 this`. Establish `hkT : IsUnit (k : T)`. Use `(b.unit k hkp).map g` as an intermediate fact. Simplify using `using this`.

Establish `hsq : (ρ' - ((D.tr : T) - ρ')) * (ρ' - ((D.tr : T) - ρ')) = -(k : T)`. Establish `: ((k : ℤ) : T) = ((4 * D.nm - D.tr ^ 2 : ℤ) : T)` using `by rw [hk]`. Move the coercions through the operations in `at this`. Rewrite using `[this]`. Take the linear combination `4 * hρ`.

Establish `: IsUnit ((ρ' - ((D.tr : T) - ρ')) * (ρ' - ((D.tr : T) - ρ')))`. Rewrite using `[hsq]`. Conclude with `hkT.neg`. Conclude with `isUnit_of_mul_isUnit_left this`. Prove the components needed by the constructor for the conclusion.

Introduce `hL`. Rewrite using `[lieIdeal, Ideal.span_le]`. Introduce and unpack `x ⟨c, i, j, rfl⟩`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker]`. Establish `he : f (lieMat b βB M c i j) = ((P c * Q) *ᵥ Pi.single j 1) i`.

Rewrite using `[Matrix.mulVec_single_one, ← hmap]`. Both sides reduce to the same expression. Rewrite using `[he, ← Matrix.mulVec_mulVec]`. Use `set w := Q *ᵥ Pi.single j 1 with hw`. Establish `hwe : matAct M f D.ω w = ρ' • w`.

Establish `h0 : ((Nh D.ω - Am ρ') * Q) *ᵥ Pi.single j 1 = 0` using `by rw [hquad, Matrix.zero_mulVec]`. Rewrite `h0` using `[← Matrix.mulVec_mulVec, Matrix.sub_mulVec, hAm, sub_eq_zero]`. Rewrite `*` using `[hact, ← hw]`. Conclude with `h0`. Take `⟨w', hw'⟩` from `hL w hwe`.

Use `(hdec w).1 ⟨w', hw'⟩ c` as an intermediate fact. Rewrite using `[this]`. Both sides reduce to the same expression. Introduce `hI v hv`. Apply `(hdec v).2` to reduce the goal to its premises.

Introduce `c`. Establish `hz : P c * Q = 0`. Use extensionality with `i j`. Use `hI (Ideal.subset_span ⟨c, i, j, rfl⟩)` as an intermediate fact. Rewrite `this` using `[RingHom.mem_ker]`.

Rewrite using `[← hmap]`. Simplify using `using this`. Establish `hQv : Q *ᵥ v = (ρ' - ((D.tr : T) - ρ')) • v`. Rewrite using `[hQ, Matrix.sub_mulVec, hAm, ← hact, hv, hs]`. Express the relevant statement in the definitionally equal form `ρ' • v - ((D.tr : T) - ρ') • v = _`.

Rewrite using `[← sub_smul]`. Establish `h1 : (ρ' - ((D.tr : T) - ρ')) • (P c *ᵥ v) = 0`. Rewrite using `[← Matrix.mulVec_smul, ← hQv, Matrix.mulVec_mulVec, hz, Matrix.zero_mulVec]`. Conclude with `(hu.smul_eq_zero).1 h1`.
-/
theorem lieMod_matAct_iff_lieIdeal_le_ker : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
  (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (T : Type) [CommRing T] (f : B →+* T),
    LieMod (matAct M f) D.ω (f (βB b.ρ)) (fun i => (f.comp βB).comp (b.t i)) ↔ lieIdeal b βB M ≤ RingHom.ker f := by
  intro p _ D R _ b B _ βB n M T _ f
  set g : R →+* T := f.comp βB with hg
  set τ : Fin D.a → (𝓞 D.F →+* T) := fun i => g.comp (b.t i) with hτ
  set ρ' : T := g b.ρ with hρ'
  set Nh : 𝓞 D.F →+* Matrix (Fin n) (Fin n) T := f.mapMatrix.comp M with hNh
  let Am : T →+* Matrix (Fin n) (Fin n) T := algebraMap T (Matrix (Fin n) (Fin n) T)
  set P : (Fin D.a → 𝓞 D.F) → Matrix (Fin n) (Fin n) T :=
    fun c => (List.ofFn fun i => (M (c i)).map f - Am (τ i (c i))).prod with hP
  set Q : Matrix (Fin n) (Fin n) T := Nh D.ω - Am (g ((D.tr : R) - b.ρ)) with hQ

  have hmap : ∀ c, f.mapMatrix (lieMat b βB M c) = P c * Q := by
    intro c
    rw [lieMat, map_mul, map_list_prod, List.map_ofFn]
    congr 1
    · congr 2; funext i; rw [Function.comp_apply, map_sub, ringHom_mapMatrix_algebraMap_scalar]; rfl
    · rw [map_sub, ringHom_mapMatrix_algebraMap_scalar]; rfl
  have hdec : ∀ v, (∃ w : Fin D.a → (Fin n → T), (∀ i, w i ∈ eigSub (matAct M f) (τ i)) ∧ v = ∑ i, w i) ↔
      ∀ c, P c *ᵥ v = 0 := by
    intro v
    have hcomax : ∀ i j, i ≠ j → Ideal.span (Set.range fun x => τ i x - τ j x) = ⊤ := by
      intro i j hij
      have h := congrArg (Ideal.map g) (b.comax i j hij)
      rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
      convert h using 3
      funext x
      simp [hτ]
    rw [GlobalTheory.T.eigenDecomposition_iff_shiftedProducts_kill_comaximal (𝓞 D.F) T (Fin n → T) (matAct M f) D.a τ hcomax v]
    simp only [list_prod_matrixActionAfterRingHom_sub_apply, hP]
    rfl

  have hω : D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hρ : ρ' * ρ' - (D.tr : T) * ρ' + (D.nm : T) = 0 := by
    have := congrArg g b.ρ_root
    simp only [map_add, map_sub, map_mul, map_pow, map_intCast, map_zero] at this
    rw [hρ']; linear_combination this
  have hquad : (Nh D.ω - Am ρ') * Q = 0 := by
    have hX : Nh D.ω * Nh D.ω - Am (D.tr : T) * Nh D.ω + Am (D.nm : T) = 0 := by
      have := congrArg Nh hω
      simpa [map_intCast] using this
    have hs : g ((D.tr : R) - b.ρ) = (D.tr : T) - ρ' := by simp [hρ']
    rw [hQ, hs]
    calc (Nh D.ω - Am ρ') * (Nh D.ω - Am ((D.tr : T) - ρ'))
        = Nh D.ω * Nh D.ω - Am (ρ' + ((D.tr : T) - ρ')) * Nh D.ω + Am (ρ' * ((D.tr : T) - ρ')) := by
          rw [map_add, map_mul, sub_mul, mul_sub, mul_sub, add_mul, ← Algebra.commutes ((D.tr : T) - ρ') (Nh D.ω)]
          abel
      _ = Nh D.ω * Nh D.ω - Am (D.tr : T) * Nh D.ω + Am (D.nm : T) := by
          congr 2
          · congr 2; ring
          · congr 1; linear_combination -hρ
      _ = 0 := hX
  have hAm : ∀ (x : T) (v : Fin n → T), Am x *ᵥ v = x • v := by
    intro x v
    simp only [Am, Algebra.algebraMap_eq_smul_one]
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  have hact : ∀ v, matAct M f D.ω v = Nh D.ω *ᵥ v := fun v => rfl
  have hs : g ((D.tr : R) - b.ρ) = (D.tr : T) - ρ' := by simp [hρ']

  have hu : IsUnit (ρ' - ((D.tr : T) - ρ')) := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = 4 * D.nm - D.tr ^ 2 := ⟨(4 * D.nm - D.tr ^ 2).toNat,
      Int.toNat_of_nonneg (by have := D.disc_neg; omega)⟩
    have hkp : k.Coprime p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out)]
      intro hd
      apply D.disc_p
      have : (p : ℤ) ∣ (k : ℤ) := Int.natCast_dvd_natCast.2 hd
      rw [hk] at this
      have h2 : D.tr ^ 2 - 4 * D.nm = -(4 * D.nm - D.tr ^ 2) := by ring
      rw [h2]; exact (dvd_neg).2 this
    have hkT : IsUnit (k : T) := by
      have := (b.unit k hkp).map g
      simpa using this
    have hsq : (ρ' - ((D.tr : T) - ρ')) * (ρ' - ((D.tr : T) - ρ')) = -(k : T) := by
      have : ((k : ℤ) : T) = ((4 * D.nm - D.tr ^ 2 : ℤ) : T) := by rw [hk]
      push_cast at this
      rw [this]; linear_combination 4 * hρ
    have : IsUnit ((ρ' - ((D.tr : T) - ρ')) * (ρ' - ((D.tr : T) - ρ'))) := by
      rw [hsq]; exact hkT.neg
    exact isUnit_of_mul_isUnit_left this
  constructor
  · intro hL
    rw [lieIdeal, Ideal.span_le]
    rintro x ⟨c, i, j, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have he : f (lieMat b βB M c i j) = ((P c * Q) *ᵥ Pi.single j 1) i := by
      rw [Matrix.mulVec_single_one, ← hmap]
      rfl
    rw [he, ← Matrix.mulVec_mulVec]
    set w := Q *ᵥ Pi.single j 1 with hw
    have hwe : matAct M f D.ω w = ρ' • w := by
      have h0 : ((Nh D.ω - Am ρ') * Q) *ᵥ Pi.single j 1 = 0 := by rw [hquad, Matrix.zero_mulVec]
      rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, hAm, sub_eq_zero] at h0
      rw [hact, ← hw] at *
      exact h0
    obtain ⟨w', hw'⟩ := hL w hwe
    have := (hdec w).1 ⟨w', hw'⟩ c
    rw [this]; rfl
  · intro hI v hv
    apply (hdec v).2
    intro c
    have hz : P c * Q = 0 := by
      ext i j
      have := hI (Ideal.subset_span ⟨c, i, j, rfl⟩)
      rw [RingHom.mem_ker] at this
      rw [← hmap]
      simpa using this
    have hQv : Q *ᵥ v = (ρ' - ((D.tr : T) - ρ')) • v := by
      rw [hQ, Matrix.sub_mulVec, hAm, ← hact, hv, hs]
      change ρ' • v - ((D.tr : T) - ρ') • v = _
      rw [← sub_smul]
    have h1 : (ρ' - ((D.tr : T) - ρ')) • (P c *ᵥ v) = 0 := by
      rw [← Matrix.mulVec_smul, ← hQv, Matrix.mulVec_mulVec, hz, Matrix.zero_mulVec]
    exact (hu.smul_eq_zero).1 h1

end GlobalTheory.UPel.HT.LieLin
