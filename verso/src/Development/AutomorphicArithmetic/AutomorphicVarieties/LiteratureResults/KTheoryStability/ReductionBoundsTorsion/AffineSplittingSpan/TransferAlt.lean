import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Transfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.TransferPrism

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismTransfer

open PositivityTheory.KB.SplitAffineSpectral Polynomial

/- English proof (translation)
The claim follows from `| 0, v => rfl | n + 1, v => by rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, h, pow_intertwine T T' L h n]`.
-/
theorem pow_intertwine {V W : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (T : Module.End ℝ V) (T' : Module.End ℝ W) (L : V →ₗ[ℝ] W) (h : ∀ v, T' (L v) = L (T v)) :
    ∀ (n : ℕ) (v : V), (T' ^ n) (L v) = L ((T ^ n) v)
  | 0, v => rfl
  | n + 1, v => by
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, h, pow_intertwine T T' L h n]

/- English proof (translation)
Proceed by induction on `f using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]`. Consider the case `monomial n a`. Simplify using `only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, pow_intertwine T T' L h n, map_smul]`.
-/
theorem aeval_intertwine {V W : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (T : Module.End ℝ V) (T' : Module.End ℝ W) (L : V →ₗ[ℝ] W) (h : ∀ v, T' (L v) = L (T v))
    (f : ℝ[X]) (v : V) : aeval T' f (L v) = L (aeval T f v) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      pow_intertwine T T' L h n, map_smul]

/- English proof (translation)
The claim follows from `| 0, v, hv => hv | n + 1, v, hv => by rw [pow_succ, Module.End.mul_apply] exact pow_mem T S hT n _ (hT v hv)`.
-/
theorem pow_mem {V : Type} [AddCommGroup V] [Module ℝ V] (T : Module.End ℝ V) (S : Submodule ℝ V)
    (hT : ∀ v ∈ S, T v ∈ S) : ∀ (n : ℕ) (v : V), v ∈ S → (T ^ n) v ∈ S
  | 0, v, hv => hv
  | n + 1, v, hv => by
    rw [pow_succ, Module.End.mul_apply]
    exact pow_mem T S hT n _ (hT v hv)

/- English proof (translation)
Proceed by induction on `f using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp only [map_add, LinearMap.add_apply]`. Conclude with `S.add_mem hp hq`. Consider the case `monomial n a`. Simplify using `only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]`.

Conclude with `S.smul_mem a (pow_mem T S hT n v hv)`.
-/
theorem aeval_mem {V : Type} [AddCommGroup V] [Module ℝ V] (T : Module.End ℝ V) (S : Submodule ℝ V)
    (hT : ∀ v ∈ S, T v ∈ S) (f : ℝ[X]) (v : V) (hv : v ∈ S) : aeval T f v ∈ S := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply]; exact S.add_mem hp hq
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact S.smul_mem a (pow_mem T S hT n v hv)

def invSub {P : Type} [Group P] (S : Set P) (m : ℕ) : Submodule ℝ ((Fin m → P) → ℝ) where
  carrier := {F | InvS S F}
  add_mem' {F G} hF hG g hg y := by simp only [Pi.add_apply, hF g hg y, hG g hg y]
  zero_mem' g _ y := rfl
  smul_mem' r F hF g hg y := by simp only [Pi.smul_apply, hF g hg y]

def dcL (Y : Type) (m : ℕ) : ((Fin (m + 1) → Y) → ℝ) →ₗ[ℝ] ((Fin (m + 2) → Y) → ℝ) where
  toFun := dc
  map_add' F G := by
    funext y; simp only [dc, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r F := by
    funext y; simp only [dc, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

def pullL {X Y : Type} (g : X → Y) (m : ℕ) : ((Fin m → Y) → ℝ) →ₗ[ℝ] ((Fin m → X) → ℝ) where
  toFun F x := F fun i => g (x i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end PositivityTheory.KB.SplitAffineSpectral.PrismTransfer

namespace PositivityTheory.KB.SplitAffineSpectral

open PrismTransfer Polynomial

/- English proof (translation)
Introduce `P Q A _ _ _ pr s hs u hu ι hι hran φ hφ m hA q hq`. Take `⟨f, hf1, hfA⟩` from `hA q hq`. Use `⟨f, hf1, fun c hc hcc => ?_⟩` and prove the remaining obligations. Use `set t := s u with ht`. Establish `hker : ∀ k : P, k ∈ (pr.ker : Set P) ↔ pr k = 1` using `fun k => MonoidHom.mem_ker`.

Set `ρ : P → P` to `fun y => y * (s (pr y))⁻¹`. Establish `hρk : ∀ y, ∃ a, ι a = ρ y` using `fun y => (hran _).1 (by simp [ρ, hs])`. Set `ρA : P → A` to `fun y => Classical.choose (hρk y)`. Establish `hρA : ∀ y, ι (ρA y) = ρ y` using `fun y => Classical.choose_spec (hρk y)`. Establish `hιk : ∀ b, pr (ι b) = 1` using `fun b => (hran _).2 ⟨b, rfl⟩`.

Establish `hρmul : ∀ k y, pr k = 1 → ρ (k * y) = k * ρ y`. Introduce `k y hk`. Simplify using `only [ρ, map_mul, hk, one_mul, mul_assoc]`. Establish `hρAmul : ∀ b y, ρA (ι b * y) = b * ρA y`. Introduce `b y`.

Apply `hι` to reduce the goal to its premises. Rewrite using `[map_mul, hρA, hρA, hρmul _ _ (hιk b)]`. Establish `hcomm : ∀ g : Q, s g * t = t * s g`. Introduce `g`. Rewrite using `[ht, ← map_mul, ← map_mul, hu]`.

Establish `hρconj : ∀ y, ρ (t⁻¹ * y * t) = t⁻¹ * ρ y * t`. Introduce `y`. Establish `hp : pr (t⁻¹ * y * t) = pr y`. Rewrite using `[map_mul, map_mul, map_inv, ht, hs, hu, mul_inv_cancel_left]`. Establish `hc' : (s (pr y))⁻¹ * t = t * (s (pr y))⁻¹`.

Rewrite using `[inv_mul_eq_iff_eq_mul, ← mul_assoc, hcomm, mul_assoc, mul_inv_cancel, mul_one]`. Use `show t⁻¹ * y * t * (s (pr (t⁻¹ * y * t)))⁻¹ = t⁻¹ * (y * (s (pr y))⁻¹) * t`. Rewrite using `[hp]`. Simplify using `only [mul_assoc, hc']`. Establish `hρAconj : ∀ y, ρA (t⁻¹ * y * t) = φ (ρA y)`.

Introduce `y`. Apply `hι` to reduce the goal to its premises. Rewrite using `[hρA, hρconj, hφ, hρA]`. Set `cA : (Fin (q + 2) → A) → ℝ` to `fun x => c fun i => ι (x i)`. Establish `hcA : InvS Set.univ cA`.

Introduce `b _ x`. Simplify using `only [cA, map_mul]`. Conclude with `hc (ι b) ((hker _).2 (hιk b)) _`. Establish `hccA : dc cA = 0`. Use function extensionality and compare the values at `x`.

Use `congrFun hcc (fun i => ι (x i))` as an intermediate fact. Simplify `this` using `[dc, cA]`. Take `⟨eA, heA, hfe⟩` from `hfA cA hcA hccA`. Set `T : (n : ℕ) → Module.End ℝ ((Fin n → P) → ℝ)` to `fun n => mapOp (fun y => t⁻¹ * y * t) n`. Establish `hTR : ∀ (n : ℕ) (g : (Fin n → A) → ℝ), T n (pullL ρA n g) = pullL ρA n (mapOp φ n g)`.

Introduce `n g`. Use function extensionality and compare the values at `y`. Simplify using `only [T, mapOp, pullL, LinearMap.coe_mk, AddHom.coe_mk, hρAconj]`. Establish `hTd : ∀ (n : ℕ) (F : (Fin (n + 1) → P) → ℝ), T (n + 2) (dcL P n F) = dcL P n (T (n + 1) F)` using `fun n F => rfl`. Establish `hRd : ∀ (n : ℕ) (g : (Fin (n + 1) → A) → ℝ), pullL ρA (n + 2) (dcL A n g) = dcL P n (pullL ρA (n + 1) g)` using `fun n g => rfl`.

Establish `hpr : c = pullL ρA (q + 2) cA - dc (prism ρ q c)`. Use function extensionality and compare the values at `y`. Establish `h1` using `prism_htpy ρ q c y`. Rewrite `h1` using `[hcc]`. Establish `h0 : prism ρ (q + 1) (fun _ => (0 : ℝ)) y = 0` using `prism_zero ρ (q + 1) y`.

Establish `h2 : pullL ρA (q + 2) cA y = c (ρ ∘ y)`. Simplify using `only [pullL, cA, LinearMap.coe_mk, AddHom.coe_mk, hρA]`. Both sides reduce to the same expression. Simplify using `only [Pi.sub_apply, h2]`. Establish `h3 : (0 : (Fin (q + 3) → P) → ℝ) = fun _ => 0` using `rfl`.

Rewrite `h1` using `[h3, h0]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hprismInv : InvS (pr.ker : Set P) (prism ρ q c)`. Introduce `k hk y`. Rewrite using `[prism_smul ρ k (fun y => hρmul k y ((hker k).1 hk)) q c y]`.

Use `congr 1`. Use function extensionality and compare the values at `z`. Conclude with `hc k hk z`. Establish `hTinv : ∀ (n : ℕ), ∀ F ∈ invSub (pr.ker : Set P) n, T n F ∈ invSub (pr.ker : Set P) n`. Introduce `n F hF k hk y`.

Simplify using `only [T, mapOp, LinearMap.coe_mk, AddHom.coe_mk]`. Establish `hk' : t⁻¹ * k * t ∈ (pr.ker : Set P)`. Rewrite `hk`, the goal using `[hker]`. Rewrite using `[map_mul, map_mul, hk, mul_one, map_inv, inv_mul_cancel]`. Use `hF _ hk' (fun i => t⁻¹ * y i * t)` as an intermediate fact.

Simplify using `only [mul_assoc, mul_inv_cancel_left] at this ⊢`. Conclude with `this`. Use `⟨pullL ρA (q + 1) eA - aeval (T (q + 1)) f (prism ρ q c), ?_, ?_⟩` and prove the remaining obligations. Introduce `k hk y`. Take `⟨b, rfl⟩` from `(hran k).1 ((hker k).1 hk)`.

Establish `h1 : aeval (T (q + 1)) f (prism ρ q c) ∈ invSub (pr.ker : Set P) (q + 1)` using `aeval_mem _ _ (hTinv (q + 1)) f _ hprismInv`. Simplify using `only [Pi.sub_apply]`. Rewrite using `[h1 (ι b) hk y]`. Use `congr 1`. Simplify using `only [pullL, LinearMap.coe_mk, AddHom.coe_mk, hρAmul]`.

Conclude with `heA b trivial _`. Establish `e1 : aeval (T (q + 2)) f c = aeval (T (q + 2)) f (pullL ρA (q + 2) cA) - aeval (T (q + 2)) f (dcL P q (prism ρ q c))` using `by conv_lhs => rw [hpr]`. Rewrite using `[map_sub]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `aeval (T (q + 2)) f c = _`.

Rewrite using `[e1, aeval_intertwine (mapOp φ (q + 2)) (T (q + 2)) (pullL ρA (q + 2)) (hTR (q + 2)), aeval_intertwine (T (q + 1)) (T (q + 2)) (dcL P q) (hTd q), hfe]`. Rewrite using `[show dc eA = dcL A q eA from rfl, hRd]`. Rewrite using `[← map_sub]`. Both sides reduce to the same expression.
-/
theorem transfer : Transfer := by
  intro P Q A _ _ _ pr s hs u hu ι hι hran φ hφ m hA q hq
  obtain ⟨f, hf1, hfA⟩ := hA q hq
  refine ⟨f, hf1, fun c hc hcc => ?_⟩
  set t := s u with ht
  have hker : ∀ k : P, k ∈ (pr.ker : Set P) ↔ pr k = 1 := fun k => MonoidHom.mem_ker

  let ρ : P → P := fun y => y * (s (pr y))⁻¹
  have hρk : ∀ y, ∃ a, ι a = ρ y := fun y => (hran _).1 (by simp [ρ, hs])
  let ρA : P → A := fun y => Classical.choose (hρk y)
  have hρA : ∀ y, ι (ρA y) = ρ y := fun y => Classical.choose_spec (hρk y)
  have hιk : ∀ b, pr (ι b) = 1 := fun b => (hran _).2 ⟨b, rfl⟩
  have hρmul : ∀ k y, pr k = 1 → ρ (k * y) = k * ρ y := by
    intro k y hk; simp only [ρ, map_mul, hk, one_mul, mul_assoc]
  have hρAmul : ∀ b y, ρA (ι b * y) = b * ρA y := by
    intro b y; apply hι; rw [map_mul, hρA, hρA, hρmul _ _ (hιk b)]
  have hcomm : ∀ g : Q, s g * t = t * s g := by
    intro g; rw [ht, ← map_mul, ← map_mul, hu]
  have hρconj : ∀ y, ρ (t⁻¹ * y * t) = t⁻¹ * ρ y * t := by
    intro y
    have hp : pr (t⁻¹ * y * t) = pr y := by
      rw [map_mul, map_mul, map_inv, ht, hs, hu, mul_inv_cancel_left]
    have hc' : (s (pr y))⁻¹ * t = t * (s (pr y))⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcomm, mul_assoc, mul_inv_cancel, mul_one]
    show t⁻¹ * y * t * (s (pr (t⁻¹ * y * t)))⁻¹ = t⁻¹ * (y * (s (pr y))⁻¹) * t
    rw [hp]
    simp only [mul_assoc, hc']
  have hρAconj : ∀ y, ρA (t⁻¹ * y * t) = φ (ρA y) := by
    intro y; apply hι; rw [hρA, hρconj, hφ, hρA]

  let cA : (Fin (q + 2) → A) → ℝ := fun x => c fun i => ι (x i)
  have hcA : InvS Set.univ cA := by
    intro b _ x
    simp only [cA, map_mul]
    exact hc (ι b) ((hker _).2 (hιk b)) _
  have hccA : dc cA = 0 := by
    funext x
    have := congrFun hcc (fun i => ι (x i))
    simpa [dc, cA] using this
  obtain ⟨eA, heA, hfe⟩ := hfA cA hcA hccA

  let T : (n : ℕ) → Module.End ℝ ((Fin n → P) → ℝ) := fun n => mapOp (fun y => t⁻¹ * y * t) n
  have hTR : ∀ (n : ℕ) (g : (Fin n → A) → ℝ),
      T n (pullL ρA n g) = pullL ρA n (mapOp φ n g) := by
    intro n g; funext y; simp only [T, mapOp, pullL, LinearMap.coe_mk, AddHom.coe_mk, hρAconj]
  have hTd : ∀ (n : ℕ) (F : (Fin (n + 1) → P) → ℝ), T (n + 2) (dcL P n F) = dcL P n (T (n + 1) F) :=
    fun n F => rfl
  have hRd : ∀ (n : ℕ) (g : (Fin (n + 1) → A) → ℝ), pullL ρA (n + 2) (dcL A n g) = dcL P n (pullL ρA (n + 1) g) :=
    fun n g => rfl

  have hpr : c = pullL ρA (q + 2) cA - dc (prism ρ q c) := by
    funext y
    have h1 := prism_htpy ρ q c y
    rw [hcc] at h1
    have h0 : prism ρ (q + 1) (fun _ => (0 : ℝ)) y = 0 := prism_zero ρ (q + 1) y
    have h2 : pullL ρA (q + 2) cA y = c (ρ ∘ y) := by
      simp only [pullL, cA, LinearMap.coe_mk, AddHom.coe_mk, hρA]; rfl
    simp only [Pi.sub_apply, h2]
    have h3 : (0 : (Fin (q + 3) → P) → ℝ) = fun _ => 0 := rfl
    rw [h3, h0] at h1
    linarith

  have hprismInv : InvS (pr.ker : Set P) (prism ρ q c) := by
    intro k hk y
    rw [prism_smul ρ k (fun y => hρmul k y ((hker k).1 hk)) q c y]
    congr 1
    funext z
    exact hc k hk z
  have hTinv : ∀ (n : ℕ), ∀ F ∈ invSub (pr.ker : Set P) n, T n F ∈ invSub (pr.ker : Set P) n := by
    intro n F hF k hk y
    simp only [T, mapOp, LinearMap.coe_mk, AddHom.coe_mk]
    have hk' : t⁻¹ * k * t ∈ (pr.ker : Set P) := by
      rw [hker] at hk ⊢
      rw [map_mul, map_mul, hk, mul_one, map_inv, inv_mul_cancel]
    have := hF _ hk' (fun i => t⁻¹ * y i * t)
    simp only [mul_assoc, mul_inv_cancel_left] at this ⊢
    exact this
  refine ⟨pullL ρA (q + 1) eA - aeval (T (q + 1)) f (prism ρ q c), ?_, ?_⟩
  · intro k hk y
    obtain ⟨b, rfl⟩ := (hran k).1 ((hker k).1 hk)
    have h1 : aeval (T (q + 1)) f (prism ρ q c) ∈ invSub (pr.ker : Set P) (q + 1) :=
      aeval_mem _ _ (hTinv (q + 1)) f _ hprismInv
    simp only [Pi.sub_apply]
    rw [h1 (ι b) hk y]
    congr 1
    simp only [pullL, LinearMap.coe_mk, AddHom.coe_mk, hρAmul]
    exact heA b trivial _
  · have e1 : aeval (T (q + 2)) f c =
        aeval (T (q + 2)) f (pullL ρA (q + 2) cA) - aeval (T (q + 2)) f (dcL P q (prism ρ q c)) := by
      conv_lhs => rw [hpr]
      rw [map_sub]
      rfl
    change aeval (T (q + 2)) f c = _
    rw [e1, aeval_intertwine (mapOp φ (q + 2)) (T (q + 2)) (pullL ρA (q + 2)) (hTR (q + 2)),
      aeval_intertwine (T (q + 1)) (T (q + 2)) (dcL P q) (hTd q), hfe]
    rw [show dc eA = dcL A q eA from rfl, hRd]
    rw [← map_sub]
    rfl

end PositivityTheory.KB.SplitAffineSpectral

end
