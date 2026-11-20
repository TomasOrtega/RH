import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds

open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

section Defs

variable {K : Type} [Field K] {σ : Type}

def fockB (f g : MvPolynomial σ K) : K := ∑ m ∈ f.support, f.coeff m * g.coeff m * (mfact m : K)

/- English proof (translation)
Unfold `fockB`. Use `Finset.sum_subset hs fun m _ hm => ?_` and prove the remaining obligations. Simplify using `only [MvPolynomial.mem_support_iff, not_not] at hm`. Rewrite using `[hm, zero_mul, zero_mul]`.
-/
theorem fockB_eq_sum (f g : MvPolynomial σ K) (s : Finset (σ →₀ ℕ)) (hs : f.support ⊆ s) :
    fockB f g = ∑ m ∈ s, f.coeff m * g.coeff m * (mfact m : K) := by
  unfold fockB
  refine Finset.sum_subset hs fun m _ hm => ?_
  simp only [MvPolynomial.mem_support_iff, not_not] at hm
  rw [hm, zero_mul, zero_mul]

def fockBL : MvPolynomial σ K →ₗ[K] MvPolynomial σ K →ₗ[K] K :=
  LinearMap.mk₂ K fockB
    (by
      classical
      intro f f' g
      rw [fockB_eq_sum (f + f') g (f.support ∪ f'.support) support_add,
        fockB_eq_sum f g (f.support ∪ f'.support) Finset.subset_union_left,
        fockB_eq_sum f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [coeff_add]; ring)
    (by
      intro c f g
      rw [fockB_eq_sum (c • f) g f.support (support_smul), fockB, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [coeff_smul, smul_eq_mul]; ring)
    (by
      intro f g g'
      simp only [fockB, coeff_add, mul_add, add_mul, Finset.sum_add_distrib])
    (by
      intro c f g
      simp only [fockB, coeff_smul, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fockBL_apply (f g : MvPolynomial σ K) : fockBL f g = fockB f g := rfl

variable {ι : Type} [Fintype ι] {n : ℕ}

def extNormB (K : Type) [Field K] (lam : ι → DomWeight n) : K :=
  ∏ τ, fockB (extremal K n (lam τ)) (extremal K n (lam τ))

def pairB (lam : ι → DomWeight n) : Pol K ι n →ₗ[K] Pol K ι n →ₗ[K] K :=
  (extNormB K lam)⁻¹ • fockBL

def pairBK (lam : ι → DomWeight n) : VV K lam →ₗ[K] VV K lam →ₗ[K] K :=
  (pairB lam).domRestrict₁₂ (VV K lam) (VV K lam)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pairB_apply (lam : ι → DomWeight n) (F F' : Pol K ι n) :
    pairB lam F F' = (extNormB K lam)⁻¹ * fockB F F' := rfl

/- English proof (translation)
The claim follows from `LinearMap.domRestrict₁₂_apply _ _ _ x y`.
-/
theorem pairBK_apply (lam : ι → DomWeight n) (x y : VV K lam) : pairBK lam x y = pairB lam x.1 y.1 :=
  LinearMap.domRestrict₁₂_apply _ _ _ x y

end Defs

def PairBSymm : Prop :=
  ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (F F' : Pol K ι n),
    pairB lam F F' = pairB lam F' F

def PairBStar : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (F F' : Pol K ι n),
    pairB lam F F' = pairP lam (fun _ => 1) (MvPolynomial.map (starRingEnd K) F) F'

def PairBInvK : Prop :=
  ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (g : ι → GL (Fin n) K)
    (F F' : Pol K ι n), pairB lam (actP lam (invTrK g) F) (actP lam g F') = pairB lam F F'

def PairBInv : Prop :=
  ∀ (E K : Type) [Field E] [Field K] (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → DomWeight n)
    (γ : GL (Fin n) E) (x y : VV K lam), pairBK lam (rhoVr emb lam γ x) (rhoV emb lam γ y) = pairBK lam x y

def PairBNondeg : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n),
    (pairBK (K := K) lam).Nondegenerate

def PairBRat : Prop :=
  ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (K0 : Subfield K) (i j : VVIdx lam),
    pairBK lam (bVV K lam i) (bVV K lam j) ∈ K0

def PairBExtremal : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (B : ι → GL (Fin n) K),
    pairB lam (actP lam (invTrK B) (ten fun τ => extremal K n (lam τ))) (actP lam B (ten fun τ => extremal K n (lam τ))) = 1

def PairBDualStd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (x : Pol K ι n),
    x ∈ VV K lam →
    (x ∈ delStd K lam ↔ ∀ y ∈ nabStd K lam, pairB lam x y ∈ (1 : Submodule (𝓞 K) K)) ∧
    (x ∈ nabStd K lam ↔ ∀ y ∈ delStd K lam, pairB lam x y ∈ (1 : Submodule (𝓞 K) K))

def PairBDualK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)), (∀ τ, Submodule.IsLattice K (M τ)) → ∀ x : VV K lam,
    (x ∈ delK lam (fun τ => dualFr (M τ)) ↔ ∀ y ∈ nabK lam M, pairBK lam x y ∈ (1 : Submodule (𝓞 K) K)) ∧
    (x ∈ nabK lam (fun τ => dualFr (M τ)) ↔ ∀ y ∈ delK lam M, pairBK lam x y ∈ (1 : Submodule (𝓞 K) K))

def PairBDual : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ)
    (emb : ι → E →+* K) (lam : ι → DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L →
    ∀ x : VV K lam,
    (x ∈ delAtr emb lam L ↔ ∀ y ∈ nabAt emb lam L, pairBK lam x y ∈ (1 : Submodule (𝓞 K) K)) ∧
    (x ∈ nabAtr emb lam L ↔ ∀ y ∈ delAt emb lam L, pairBK lam x y ∈ (1 : Submodule (𝓞 K) K))

section Triv

variable {K : Type} [Field K]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pb_fockS_triv {σ : Type} (f g : MvPolynomial σ K) :
    @fockS K _ starRingOfComm σ f g = fockB f g := rfl

variable {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pb_extNorm_triv (lam : ι → DomWeight n) : @extNorm ι _ n K _ starRingOfComm lam = extNormB K lam := rfl

/- English proof (translation)
Simplify using `[gramTw]`.
-/
theorem pb_gramTw_one (lam : ι → DomWeight n) : gramTw lam (fun _ : ι => (1 : Matrix (Fin n) (Fin n) K)) = 1 := by
  simp [gramTw]

/- English proof (translation)
Establish `h : Formalism.GradedWeylDivisibility.blockAct K (fun _ : ι => (1 : Matrix (Fin n) (Fin n) K)ᵀ) = AlgHom.id K (Pol K ι n)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_X, AlgHom.id_apply, Matrix.transpose_one]`. Rewrite using `[Finset.sum_eq_single v.2.1]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[Matrix.one_apply_ne' hb, map_zero, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem pb_blockAct_one_tr (F : Pol K ι n) :
    Formalism.GradedWeylDivisibility.blockAct K (fun _ : ι => (1 : Matrix (Fin n) (Fin n) K)ᵀ) F = F := by
  have h : Formalism.GradedWeylDivisibility.blockAct K (fun _ : ι => (1 : Matrix (Fin n) (Fin n) K)ᵀ) = AlgHom.id K (Pol K ι n) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_X, AlgHom.id_apply, Matrix.transpose_one]
    rw [Finset.sum_eq_single v.2.1]
    · simp
    · intro b _ hb
      rw [Matrix.one_apply_ne' hb, map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h]
  rfl

/- English proof (translation)
Rewrite using `[pairB_apply]`. Simplify using `only [pairP, LinearMap.smul_apply, LinearMap.compl₂_apply, AlgHom.toLinearMap_apply, fockL, LinearMap.mk₂'ₛₗ_apply, pb_gramTw_one, pb_blockAct_one_tr, pb_fockS_triv, pb_extNorm_triv, smul_eq_mul, one_div]`. Both sides reduce to the same expression.
-/
theorem pairP_trivial (lam : ι → DomWeight n) (F F' : Pol K ι n) :
    @pairP K _ ι _ n starRingOfComm lam (fun _ => 1) F F' = pairB lam F F' := by
  rw [pairB_apply]
  simp only [pairP, LinearMap.smul_apply, LinearMap.compl₂_apply, AlgHom.toLinearMap_apply, fockL,
    LinearMap.mk₂'ₛₗ_apply, pb_gramTw_one, pb_blockAct_one_tr, pb_fockS_triv, pb_extNorm_triv, smul_eq_mul,
    one_div]
  rfl

/- English proof (translation)
Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem pb_conjTranspose_triv (A : Matrix (Fin n) (Fin n) K) :
    @Matrix.conjTranspose _ _ K starRingOfComm.toStarAddMonoid.toInvolutiveStar.toStar A = Aᵀ := by
  ext i j
  rfl

end Triv

/- English proof (translation)
Introduce `K _ ι _ n lam F F'`. Rewrite using `[pairB_apply, pairB_apply, fockB_eq_sum F F' (F.support ∪ F'.support) Finset.subset_union_left, fockB_eq_sum F' F (F.support ∪ F'.support) Finset.subset_union_right]`. Use `congr 1`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pairingBSymm_holds : PairBSymm := by
  intro K _ ι _ n lam F F'
  classical
  rw [pairB_apply, pairB_apply, fockB_eq_sum F F' (F.support ∪ F'.support) Finset.subset_union_left,
    fockB_eq_sum F' F (F.support ∪ F'.support) Finset.subset_union_right]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/- English proof (translation)
Introduce `K _ ι _ n lam g F F'`. Rewrite using `[← pairP_trivial, ← pairP_trivial]`. Set `_ : StarRing K` to `starRingOfComm`. Rewrite using `[pairTransport K ι n lam (fun _ => 1) (invTrK g) g F F']`. Establish `hG : (fun τ => ((invTrK g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᴴ * (1 : Matrix (Fin n) (Fin n) K) * ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = fun _ => 1`.

Use function extensionality and compare the values at `τ`. Establish `h1 : ((invTrK g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᴴ = (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)`. Rewrite using `[invTrK_coe]`. Use extensionality with `i j`. Both sides reduce to the same expression.

Rewrite using `[h1, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]`. Rewrite using `[hG]`.
-/
theorem pairingBInvariantK_holds : PairBInvK := by
  intro K _ ι _ n lam g F F'
  rw [← pairP_trivial, ← pairP_trivial]
  let _ : StarRing K := starRingOfComm
  rw [pairTransport K ι n lam (fun _ => 1) (invTrK g) g F F']
  have hG : (fun τ => ((invTrK g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᴴ * (1 : Matrix (Fin n) (Fin n) K) *
      ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = fun _ => 1 := by
    funext τ
    have h1 : ((invTrK g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᴴ =
        (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [invTrK_coe]
      ext i j
      rfl
    rw [h1, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [hG]

/- English proof (translation)
Introduce `E K _ _ ι _ n emb lam γ x y`. Rewrite using `[pairBK_apply, pairBK_apply]`. Conclude with `pairingBInvariantK_holds K ι n lam (embGL emb γ) x.1 y.1`.
-/
theorem pairingBInvariant_holds : PairBInv := by
  intro E K _ _ ι _ n emb lam γ x y
  rw [pairBK_apply, pairBK_apply]
  exact pairingBInvariantK_holds K ι n lam (embGL emb γ) x.1 y.1

/- English proof (translation)
Introduce `K _ _ ι _ n lam`. Establish `h` using `@pairingNondegenerate_holds K _ starRingOfComm _ ι _ n lam (fun _ => 1) (fun _ => by simp)`. Use `show (∀ x, (∀ y, pairBK lam x y = 0) → x = 0) ∧ (∀ y, (∀ x, pairBK lam x y = 0) → y = 0)`. Use `⟨fun x hx => (And.left h) x fun y => ?_, fun y hy => (And.right h) y fun x => ?_⟩` and prove the remaining obligations. Establish `hxy` using `hx y`.

Rewrite `hxy` using `[pairBK_apply, ← pairP_trivial]`. Conclude with `hxy`. Establish `hxy` using `hy x`. Rewrite `hxy` using `[pairBK_apply, ← pairP_trivial]`. Conclude with `hxy`.
-/
theorem pairingBNondegenerate_holds : PairBNondeg := by
  intro K _ _ ι _ n lam
  have h := @pairingNondegenerate_holds K _ starRingOfComm _ ι _ n lam (fun _ => 1) (fun _ => by simp)
  show (∀ x, (∀ y, pairBK lam x y = 0) → x = 0) ∧ (∀ y, (∀ x, pairBK lam x y = 0) → y = 0)
  refine ⟨fun x hx => (And.left h) x fun y => ?_, fun y hy => (And.right h) y fun x => ?_⟩
  · have hxy := hx y
    rw [pairBK_apply, ← pairP_trivial] at hxy
    exact hxy
  · have hxy := hy x
    rw [pairBK_apply, ← pairP_trivial] at hxy
    exact hxy

/- English proof (translation)
Introduce `K _ ι _ n lam K0 i j`. Establish `h` using `@pairingRational_holds K _ starRingOfComm ι _ n lam K0 (fun _ => 1) (fun τ a b => by`. Simplify using `only [Matrix.one_apply]`. Use `split_ifs`. Use `exacts [K0.one_mem, K0.zero_mem]) i j`.

Rewrite using `[pairBK_apply, ← pairP_trivial]`. Conclude with `h`.
-/
theorem pairingBRational_holds : PairBRat := by
  intro K _ ι _ n lam K0 i j
  have h := @pairingRational_holds K _ starRingOfComm ι _ n lam K0 (fun _ => 1)
    (fun τ a b => by
      simp only [Matrix.one_apply]
      split_ifs
      exacts [K0.one_mem, K0.zero_mem]) i j
  rw [pairBK_apply, ← pairP_trivial]
  exact h

/- English proof (translation)
Simplify using `[actP, detTwK_one, trAct_one]`.
-/
private theorem actP_one' {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (F : Pol K ι n) : actP lam (1 : ι → GL (Fin n) K) F = F := by
  simp [actP, detTwK_one, trAct_one]

/- English proof (translation)
Introduce `h0`. Establish `h` using `@pairingExtremal_holds K _ starRingOfComm _ ι _ n lam (fun _ => 1) 1 (fun τ => by simp)`. Rewrite `h` using `[actP_one', pairP_trivial, pairB_apply, h0, inv_zero, zero_mul]`. Conclude with `zero_ne_one h`.
-/
theorem pb_extNormB_ne (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    extNormB K lam ≠ 0 := by
  intro h0
  have h := @pairingExtremal_holds K _ starRingOfComm _ ι _ n lam (fun _ => 1) 1 (fun τ => by simp)
  rw [actP_one', pairP_trivial, pairB_apply, h0, inv_zero, zero_mul] at h
  exact zero_ne_one h

/- English proof (translation)
Introduce `K _ _ ι _ n lam B`. Rewrite using `[pairingBInvariantK_holds K ι n lam B]`. Establish `h` using `@pairingExtremal_holds K _ starRingOfComm _ ι _ n lam (fun _ => 1) 1 (fun τ => by simp)`. Rewrite `h` using `[actP_one', pairP_trivial]`. Conclude with `h`.
-/
theorem pairingBExtremal_holds : PairBExtremal := by
  intro K _ _ ι _ n lam B
  rw [pairingBInvariantK_holds K ι n lam B]
  have h := @pairingExtremal_holds K _ starRingOfComm _ ι _ n lam (fun _ => 1) 1 (fun τ => by simp)
  rw [actP_one', pairP_trivial] at h
  exact h

section Star

variable {K : Type} [Field K] [StarRing K]

/- English proof (translation)
Rewrite using `[fockS_eq_sum _ g f.support (MvPolynomial.support_map_subset ..)]`. Unfold `fockB`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_map, starRingEnd_apply, star_star]`.
-/
theorem pb_fockS_map_star {σ : Type} (f g : MvPolynomial σ K) :
    fockS (MvPolynomial.map (starRingEnd K) f) g = fockB f g := by
  rw [fockS_eq_sum _ g f.support (MvPolynomial.support_map_subset ..)]
  unfold fockB
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map, starRingEnd_apply, star_star]

/- English proof (translation)
Rewrite using `[fockS_eq_sum _ g (MvPolynomial.map (Int.castRingHom K) P).support (Finset.Subset.refl _)]`. Unfold `fockB`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Simplify using `only [MvPolynomial.coeff_map, eq_intCast, star_intCast]`.
-/
theorem pb_fockS_int {σ : Type} (P : MvPolynomial σ ℤ) (g : MvPolynomial σ K) :
    fockS (MvPolynomial.map (Int.castRingHom K) P) g = fockB (MvPolynomial.map (Int.castRingHom K) P) g := by
  rw [fockS_eq_sum _ g (MvPolynomial.map (Int.castRingHom K) P).support (Finset.Subset.refl _)]
  unfold fockB
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [MvPolynomial.coeff_map, eq_intCast, star_intCast]

/- English proof (translation)
Unfold `extremal Formalism.GradedWeylDivisibility.hw Formalism.GradedWeylDivisibility.lpMinor`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, RingHom.map_det]`. Use `congr 2`.

Use extensionality with `p q`. Simplify using the standard rewrite rules.
-/
private theorem extremal_eq_map_intCast (K : Type) [Field K] {N : ℕ} (l : DomWeight N) :
    extremal K N l = MvPolynomial.map (Int.castRingHom K) (extremal ℤ N l) := by
  unfold extremal Formalism.GradedWeylDivisibility.hw Formalism.GradedWeylDivisibility.lpMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext p q
  simp

/- English proof (translation)
Unfold `extNorm extNormB`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[extremal_eq_map_intCast, pb_fockS_int]`.
-/
theorem pb_extNorm_eq {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) : extNorm K lam = extNormB K lam := by
  unfold extNorm extNormB
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [extremal_eq_map_intCast, pb_fockS_int]

end Star

/- English proof (translation)
Introduce `K _ _ ι _ n lam F F'`. Establish `hf : ∀ a b : Pol K ι n, fockL a b = fockS a b` using `fun a b => rfl`. Rewrite using `[pairB_apply]`. Simplify using `only [pairP, LinearMap.smul_apply, LinearMap.compl₂_apply, AlgHom.toLinearMap_apply, hf, pb_gramTw_one, pb_blockAct_one_tr, pb_fockS_map_star, pb_extNorm_eq, smul_eq_mul, one_div]`.
-/
theorem pairingBStar_holds : PairBStar := by
  intro K _ _ ι _ n lam F F'
  have hf : ∀ a b : Pol K ι n, fockL a b = fockS a b := fun a b => rfl
  rw [pairB_apply]
  simp only [pairP, LinearMap.smul_apply, LinearMap.compl₂_apply, AlgHom.toLinearMap_apply, hf,
    pb_gramTw_one, pb_blockAct_one_tr, pb_fockS_map_star, pb_extNorm_eq, smul_eq_mul, one_div]

/- English proof (translation)
Rewrite using `[← pairP_trivial, @pairP_vecP K _ starRingOfComm]`. Simplify using `only [Matrix.one_mulVec]`. Both sides reduce to the same expression.
-/
theorem pairB_vecP {K : Type} [Field K] (φ v : Fin 2 → K) :
    pairB (fun _ : Unit => lamVec) (vecP φ) (vecP v) = φ ⬝ᵥ v := by
  rw [← pairP_trivial, @pairP_vecP K _ starRingOfComm]
  simp only [Matrix.one_mulVec]
  rfl

/- English proof (translation)
Establish `h0 : (lamVec : DomWeight 2).detShift = 0` using `by rfl`. Establish `hd : detTwK (fun _ : Unit => lamVec) h = 1`. Simplify using `[detTwK, detPow, h0]`. Simplify using `only [actP, LinearMap.smul_apply, hd, one_smul, AlgHom.toLinearMap_apply, trAct, vecP, map_sum, map_mul, Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq, Matrix.transpose_apply, Matrix.mulVec, dotProduct, Fin.sum_u …`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem actP_lamVec_vecP {K : Type} [Field K] (h : Unit → GL (Fin 2) K) (w : Fin 2 → K) :
    actP (fun _ : Unit => lamVec) h (vecP w) = vecP ((h () : Matrix (Fin 2) (Fin 2) K) *ᵥ w) := by
  have h0 : (lamVec : DomWeight 2).detShift = 0 := by rfl
  have hd : detTwK (fun _ : Unit => lamVec) h = 1 := by
    simp [detTwK, detPow, h0]
  simp only [actP, LinearMap.smul_apply, hd, one_smul, AlgHom.toLinearMap_apply, trAct, vecP, map_sum, map_mul,
    Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq,
    Matrix.transpose_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, map_add]
  ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨actP_lamVec_vecP (invTrK g) φ, actP_lamVec_vecP g v⟩`.
-/
theorem actP_invTrK_vecP_and_actP_vecP {K : Type} [Field K] (g : Unit → GL (Fin 2) K) (φ v : Fin 2 → K) :
    actP (fun _ => lamVec) (invTrK g) (vecP φ) =
        vecP ((((g ())⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ *ᵥ φ) ∧
      actP (fun _ => lamVec) g (vecP v) = vecP ((g () : Matrix (Fin 2) (Fin 2) K) *ᵥ v) := ⟨actP_lamVec_vecP (invTrK g) φ, actP_lamVec_vecP g v⟩

/- English proof (translation)
Rewrite using `[← pairP_trivial, @pairP_char K _ starRingOfComm]`. Simplify using the standard rewrite rules.
-/
theorem pairB_char {K : Type} [Field K] (e : ℤ) : pairB (fun _ : Unit => lamChar e) (1 : Pol K Unit 1) 1 = 1 := by
  rw [← pairP_trivial, @pairP_char K _ starRingOfComm]
  simp

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((g τ : Matrix (Fin n) (Fin n) K)ᵀ)ᵀ = (g τ : Matrix (Fin n) (Fin n) K)`. Conclude with `Matrix.transpose_transpose _`.
-/
theorem pb_invTrK_invTrK {K : Type} [Field K] {ι : Type} {n : ℕ} (g : ι → GL (Fin n) K) : invTrK (invTrK g) = g := by
  funext τ
  apply Units.ext
  change ((g τ : Matrix (Fin n) (Fin n) K)ᵀ)ᵀ = (g τ : Matrix (Fin n) (Fin n) K)
  exact Matrix.transpose_transpose _

/- English proof (translation)
Establish `h` using `congrArg (fun φ : Module.End K (Pol K ι n) => φ F) ((rhoP lam).map_mul a b)`. Simplify `h` using `[rhoP]`.
-/
private theorem actP_mul' {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (a b : ι → GL (Fin n) K) (F : Pol K ι n) : actP lam (a * b) F = actP lam a (actP lam b F) := by
  have h := congrArg (fun φ : Module.End K (Pol K ι n) => φ F) ((rhoP lam).map_mul a b)
  simpa [rhoP] using h

/- English proof (translation)
Establish `h1` using `pairingBInvariantK_holds K ι n lam (invTrK g)⁻¹ (actP lam g F) F'`. Rewrite `h1` using `[map_inv, pb_invTrK_invTrK, ← actP_mul', inv_mul_cancel, actP_one']`. Conclude with `h1.symm`.
-/
theorem pairB_adj {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (g : ι → GL (Fin n) K)
    (F F' : Pol K ι n) : pairB lam (actP lam g F) F' = pairB lam F (actP lam (invTrK g)⁻¹ F') := by
  have h1 := pairingBInvariantK_holds K ι n lam (invTrK g)⁻¹ (actP lam g F) F'
  rw [map_inv, pb_invTrK_invTrK, ← actP_mul', inv_mul_cancel, actP_one'] at h1
  exact h1.symm

/- English proof (translation)
Rewrite using `[fockS_eq_sum f g f.support (Finset.Subset.refl _), fockB_eq_sum _ g f.support (MvPolynomial.support_map_subset ..)]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_map, starRingEnd_apply]`.
-/
theorem pb_fockS_eq {K : Type} [Field K] [StarRing K] {σ : Type} (f g : MvPolynomial σ K) :
    fockS f g = fockB (MvPolynomial.map (starRingEnd K) f) g := by
  rw [fockS_eq_sum f g f.support (Finset.Subset.refl _),
    fockB_eq_sum _ g f.support (MvPolynomial.support_map_subset ..)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map, starRingEnd_apply]

/- English proof (translation)
Establish `hf : ∀ a b : Pol K ι n, fockL a b = fockS a b` using `fun a b => rfl`. Establish `hs : ∀ (c : K) (a b : Pol K ι n), fockB a (c • b) = c * fockB a b`. Introduce `c a b`. Rewrite using `[← fockBL_apply, ← fockBL_apply, map_smul, smul_eq_mul]`. Establish `hd : detTwK lam G = gramTw lam (fun τ => ((G τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))`.

Unfold `detTwK gramTw detPow`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]`. Rewrite using `[pairB_apply]`. Simplify using `only [pairP, actP, trAct, LinearMap.smul_apply, LinearMap.compl₂_apply, AlgHom.toLinearMap_apply, hf, pb_fockS_eq, pb_extNorm_eq, smul_eq_mul, hs, hd]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pairP_eq_pairB {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (G : ι → GL (Fin n) K) (F F' : Pol K ι n) :
    pairP lam (fun τ => ((G τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) F F' =
      pairB lam (MvPolynomial.map (starRingEnd K) F) (actP lam G F') := by
  have hf : ∀ a b : Pol K ι n, fockL a b = fockS a b := fun a b => rfl
  have hs : ∀ (c : K) (a b : Pol K ι n), fockB a (c • b) = c * fockB a b := by
    intro c a b
    rw [← fockBL_apply, ← fockBL_apply, map_smul, smul_eq_mul]
  have hd : detTwK lam G = gramTw lam (fun τ => ((G τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    unfold detTwK gramTw detPow
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
  rw [pairB_apply]
  simp only [pairP, actP, trAct, LinearMap.smul_apply, LinearMap.compl₂_apply, AlgHom.toLinearMap_apply, hf,
    pb_fockS_eq, pb_extNorm_eq, smul_eq_mul, hs, hd]
  ring

end Formalism.L2.DIV
