import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

namespace GlobalTheory.FubiniStudyFrame

/- English proof (translation)
Establish `hx : Matrix.vecMul w (c.map σ) ≠ 0`. Introduce `hx`. Apply `hw` to reduce the goal to its premises. Use function extensionality and compare the values at `l`. Use `set r := b.repr (u l)`.

Establish `hl : ∑ k, ((Pi.single l (1 : K) : Fin n → K) k - ∑ j, c k j * r j) • u k = 0`. Establish `e : ∑ k, (∑ j, c k j * r j) • u k = u l`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_smul, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]`. Use `_ = ∑ j, r j • b j := by simp only [hb]`. Use `_ = u l := b.sum_repr (u l)`. Simplify using `only [sub_smul, Finset.sum_sub_distrib, e, Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]`. Establish `h2` using `hrel _ hl`.

Establish `h3 : ∀ j, ∑ k, w k * σ (c k j) = 0` using `fun j => by`. Use `congrFun hx j` as an intermediate fact. Simplify `this` using `[Matrix.vecMul, dotProduct]`. Establish `h4 : ∑ k, σ ((Pi.single l (1 : K) : Fin n → K) k - ∑ j, c k j * r j) * w k = w l - ∑ j, σ (r j) * ∑ k, w k * σ (c k j)`. Simplify using `only [map_sub, map_sum, map_mul, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]`.

Use `congr 1`. Rewrite using `[Finset.sum_eq_single l]`. Simplify using the standard rewrite rules. Introduce `k _ hk`. Simplify using `[Pi.single_apply, hk]`.

Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Rewrite `h2` using `[h4]`. Simplify `h2` using `[h3]`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `h0 : Matrix.vecMul (Matrix.vecMul w (c.map σ)) A = 0`. Rewrite using `[Matrix.vecMul_vecMul]`. Use function extensionality and compare the values at `a`.

Use `hne a` as an intermediate fact. Simplify using `only [Matrix.vecMul, dotProduct, Pi.zero_apply]`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Conclude with `hA (Matrix.exists_vecMul_eq_zero_iff.1 ⟨_, hx, h0⟩)`.
-/
theorem exists_ne_zero_of_rel {K V : Type} [Field K] [AddCommGroup V] [Module K V] {n N : ℕ}
    (σ : K →+* ℂ) (u : Fin n → V) (b : Module.Basis (Fin N) K V) (c : Matrix (Fin n) (Fin N) K)
    (A : Matrix (Fin N) (Fin N) ℂ) (w : Fin n → ℂ) (hw : w ≠ 0)
    (hrel : ∀ lam : Fin n → K, ∑ k, lam k • u k = 0 → ∑ k, σ (lam k) * w k = 0)
    (hb : ∀ j, b j = ∑ k, c k j • u k) (hA : A.det ≠ 0) :
    ∃ a, ∑ k, (c.map σ * A) k a * w k ≠ 0 := by
  classical
  have hx : Matrix.vecMul w (c.map σ) ≠ 0 := by
    intro hx
    apply hw
    funext l
    set r := b.repr (u l)
    have hl : ∑ k, ((Pi.single l (1 : K) : Fin n → K) k - ∑ j, c k j * r j) • u k = 0 := by
      have e : ∑ k, (∑ j, c k j * r j) • u k = u l := by
        calc ∑ k, (∑ j, c k j * r j) • u k = ∑ j, r j • ∑ k, c k j • u k := by
              simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
          _ = ∑ j, r j • b j := by simp only [hb]
          _ = u l := b.sum_repr (u l)
      simp only [sub_smul, Finset.sum_sub_distrib, e, Pi.single_apply, ite_smul, one_smul,
        zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
    have h2 := hrel _ hl
    have h3 : ∀ j, ∑ k, w k * σ (c k j) = 0 := fun j => by
      have := congrFun hx j
      simpa [Matrix.vecMul, dotProduct] using this
    have h4 : ∑ k, σ ((Pi.single l (1 : K) : Fin n → K) k - ∑ j, c k j * r j) * w k =
        w l - ∑ j, σ (r j) * ∑ k, w k * σ (c k j) := by
      simp only [map_sub, map_sum, map_mul, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum,
        Finset.sum_mul]
      congr 1
      · rw [Finset.sum_eq_single l]
        · simp
        · intro k _ hk; simp [Pi.single_apply, hk]
        · simp
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [h4] at h2
    simpa [h3] using h2
  by_contra hne
  push_neg at hne
  have h0 : Matrix.vecMul (Matrix.vecMul w (c.map σ)) A = 0 := by
    rw [Matrix.vecMul_vecMul]
    funext a
    have := hne a
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  exact hA (Matrix.exists_vecMul_eq_zero_iff.1 ⟨_, hx, h0⟩)

/- English proof (translation)
Use `set σ := OfLattice.extEmb τ`. Take `⟨⟨d, hd⟩, hint⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) (Finset.univ.image lam)`. Establish `hk : ∀ k, IsLocalization.IsInteger (𝓞 K) (d • lam k)` using `fun k => hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))`. Use `choose lam' hlam' using hk`. Establish `hσ : ∀ x : 𝓞 K, σ (algebraMap (𝓞 K) K x) = τ x` using `fun x => RingHom.congr_fun (OfLattice.extEmb_comp τ) x`.

Establish `h1 : ∑ k, lam' k • u k = 0`. Establish `: ∀ k, lam' k • u k = d • (lam k • u k)` using `fun k => by`. Rewrite using `[← algebraMap_smul K (lam' k) (u k), hlam' k, Algebra.smul_def, mul_smul, algebraMap_smul]`. Simplify using `only [this, ← Finset.smul_sum, h, smul_zero]`. Establish `h2` using `H lam' h1`.

Establish `h3 : ∀ k, τ (lam' k) = σ (algebraMap (𝓞 K) K d) * σ (lam k)` using `fun k => by`. Rewrite using `[← hσ, hlam' k, Algebra.smul_def, map_mul]`. Simplify using `only [h3, mul_assoc, ← Finset.mul_sum] at h2`. Establish `hd0 : σ (algebraMap (𝓞 K) K d) ≠ 0`. Rewrite using `[map_ne_zero, ne_eq, ← map_zero (algebraMap (𝓞 K) K), (IsFractionRing.injective (𝓞 K) K).eq_iff]`.

Conclude with `nonZeroDivisors.ne_zero hd`. Conclude with `(mul_eq_zero.1 h2).resolve_left hd0`.
-/
theorem rel_field_of_rel_int {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {n : ℕ} (τ : 𝓞 K →+* ℂ) (u : Fin n → V)
    (w : Fin n → ℂ)
    (H : ∀ lam : Fin n → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, τ (lam k) * w k = 0)
    (lam : Fin n → K) (h : ∑ k, lam k • u k = 0) :
    ∑ k, OfLattice.extEmb τ (lam k) * w k = 0 := by
  classical
  set σ := OfLattice.extEmb τ
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (𝓞 K)) (Finset.univ.image lam)
  have hk : ∀ k, IsLocalization.IsInteger (𝓞 K) (d • lam k) := fun k =>
    hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  choose lam' hlam' using hk
  have hσ : ∀ x : 𝓞 K, σ (algebraMap (𝓞 K) K x) = τ x := fun x =>
    RingHom.congr_fun (OfLattice.extEmb_comp τ) x
  have h1 : ∑ k, lam' k • u k = 0 := by
    have : ∀ k, lam' k • u k = d • (lam k • u k) := fun k => by
      rw [← algebraMap_smul K (lam' k) (u k), hlam' k, Algebra.smul_def, mul_smul,
        algebraMap_smul]
    simp only [this, ← Finset.smul_sum, h, smul_zero]
  have h2 := H lam' h1
  have h3 : ∀ k, τ (lam' k) = σ (algebraMap (𝓞 K) K d) * σ (lam k) := fun k => by
    rw [← hσ, hlam' k, Algebra.smul_def, map_mul]
  simp only [h3, mul_assoc, ← Finset.mul_sum] at h2
  have hd0 : σ (algebraMap (𝓞 K) K d) ≠ 0 := by
    rw [map_ne_zero, ne_eq, ← map_zero (algebraMap (𝓞 K) K),
      (IsFractionRing.injective (𝓞 K) K).eq_iff]
    exact nonZeroDivisors.ne_zero hd
  exact (mul_eq_zero.1 h2).resolve_left hd0

end GlobalTheory.FubiniStudyFrame

open GlobalTheory.FubiniStudyFrame in

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ m N X _ p g u b c A _hg hrel hb hA τ i y hy`. Use `set s := fun k => GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g with hs`. Use `set w : Fin (m + 1) → ℂ := fun k => secVal p τ (s k) i y with hw_def`. Establish `hsup` using `ProjSpace.iSup_nonzeroLocus_secPull (ProjSpace.iSup_nonzeroLocus_coord (𝓞 K) m) g`. Establish `hw : w ≠ 0`.

Take `⟨k, hk⟩` from `TopologicalSpace.Opens.mem_iSup.1 (show y.1 (IsLocalRing.closedPoint ℂ) ∈ ⨆ k, nonzeroLocus (s k) by rw [hsup]; trivial)`. Introduce `h0`. Conclude with `(secVal_ne_zero_iff (s k) hy).2 (mem_ptsIn.2 hk) (congrFun h0 k)`. Establish `H : ∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, τ (lam k) * w k = 0`. Introduce `lam h`.

Establish `e` using `congrArg (fun t => secVal p τ t i y) (hrel lam h)`. Simplify `e` using `[map_sum, secVal_smul, Finset.sum_apply, hw_def]`. Take `⟨a, ha⟩` from `exists_ne_zero_of_rel (OfLattice.extEmb τ) u b c (A (OfLattice.extEmb τ)) w hw (rel_field_of_rel_int τ u w H) hb (hA _)`. Use `⟨a, ?_⟩` and prove the remaining obligations. Simplify `ha` using `[Finset.sum_apply, hw_def]`.
-/
theorem GlobalTheory.FubiniStudyFrame.noCommonZero_comb : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (m N : ℕ) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (u : Fin (m + 1) → V) (b : Module.Basis (Fin N) K V) (c : Matrix (Fin (m + 1)) (Fin N) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ),
    g ≫ PSpace.str (𝓞 K) m = p →
    (∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g = 0) →
    (∀ j, b j = ∑ k, c k j • u k) → (∀ σ, (A σ).det ≠ 0) →
    ∀ τ : 𝓞 K →+* ℂ, Weight.NoCommonZero fun a => ∑ k, (c.map (OfLattice.extEmb τ) * A (OfLattice.extEmb τ)) k a • secVal p τ (GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g) := by
  intro K V _ _ _ _ _ _ m N X _ p g u b c A _hg hrel hb hA τ i y hy
  classical
  set s := fun k => GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g with hs
  set w : Fin (m + 1) → ℂ := fun k => secVal p τ (s k) i y with hw_def
  have hsup := ProjSpace.iSup_nonzeroLocus_secPull (ProjSpace.iSup_nonzeroLocus_coord (𝓞 K) m) g
  have hw : w ≠ 0 := by
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show y.1 (IsLocalRing.closedPoint ℂ) ∈ ⨆ k, nonzeroLocus (s k) by rw [hsup]; trivial)
    intro h0
    exact (secVal_ne_zero_iff (s k) hy).2 (mem_ptsIn.2 hk) (congrFun h0 k)
  have H : ∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, τ (lam k) * w k = 0 := by
    intro lam h
    have e := congrArg (fun t => secVal p τ t i y) (hrel lam h)
    simpa [map_sum, secVal_smul, Finset.sum_apply, hw_def] using e
  obtain ⟨a, ha⟩ := exists_ne_zero_of_rel (OfLattice.extEmb τ) u b c (A (OfLattice.extEmb τ)) w hw
    (rel_field_of_rel_int τ u w H) hb (hA _)
  refine ⟨a, ?_⟩
  simpa [Finset.sum_apply, hw_def] using ha
