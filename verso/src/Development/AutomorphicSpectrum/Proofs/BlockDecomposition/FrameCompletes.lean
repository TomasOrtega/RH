import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FrameComplete

open Matrix

section Abstract

variable {A : Type*} [CommRing A] [StarRing A] {ι α β ρ τ : Type*}
  [Fintype ι] [Fintype α] [Fintype β] [Fintype ρ] [Fintype τ]
  [DecidableEq ι] [DecidableEq ρ] [DecidableEq τ]

/- English proof (translation)
Rewrite using `[conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, Matrix.mul_assoc]`.
-/
theorem gram_conj {G : Matrix ι ι A} (hG : Gᴴ = G) (M : Matrix ι α A) (N : Matrix ι β A) :
    (Mᴴ * (G * N))ᴴ = Nᴴ * (G * M) := by
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, Matrix.mul_assoc]

/- English proof (translation)
Use `set c := xᴴ * (G * v) with hc`. Use `set y := Bi * c with hy`. Establish `hec : e • c = c` using `by conv_lhs => rw [hc, ← Matrix.mul_smul, ← Matrix.mul_smul, hv]`. Establish `hBy : B * y = c` using `by rw [hy, ← Matrix.mul_assoc, hB, Matrix.one_mul]`. Establish `h1 : xᴴ * (G * (v - x * y)) = 0`.

Rewrite using `[Matrix.mul_sub, Matrix.mul_sub, ← hc, ← Matrix.mul_assoc G, ← Matrix.mul_assoc, hxx, Matrix.smul_mul, hBy, hec, sub_self]`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `h2 : (v - x * y)ᴴ * (G * x) = 0`. Rewrite using `[← gram_conj hG, h1, conjTranspose_zero]`. Establish `h3 : (v - x * y)ᴴ * (G * v) = vᴴ * (G * v) - yᴴ * c`.

Rewrite using `[conjTranspose_sub, Matrix.sub_mul, conjTranspose_mul, Matrix.mul_assoc, ← hc]`. Rewrite using `[Matrix.mul_sub, Matrix.mul_sub, h3, ← Matrix.mul_assoc G, ← Matrix.mul_assoc _ (G * x), h2, Matrix.zero_mul, sub_zero, ← hBy]`. Conclude with `hq`.
-/
theorem orth_part {G : Matrix ι ι A} (hG : Gᴴ = G) {B Bi : Matrix ρ ρ A} (hB : B * Bi = 1)
    {e : A} {x : Matrix ι ρ A} {v : Matrix ι τ A} (hv : e • v = v)
    (hxx : xᴴ * (G * x) = e • B)
    (hq : vᴴ * (G * v) - (Bi * (xᴴ * (G * v)))ᴴ * (B * (Bi * (xᴴ * (G * v)))) = 0) :
    xᴴ * (G * (v - x * (Bi * (xᴴ * (G * v))))) = 0 ∧
      (v - x * (Bi * (xᴴ * (G * v))))ᴴ * (G * (v - x * (Bi * (xᴴ * (G * v))))) = 0 := by
  set c := xᴴ * (G * v) with hc
  set y := Bi * c with hy
  have hec : e • c = c := by
    conv_lhs => rw [hc, ← Matrix.mul_smul, ← Matrix.mul_smul, hv]
  have hBy : B * y = c := by rw [hy, ← Matrix.mul_assoc, hB, Matrix.one_mul]
  have h1 : xᴴ * (G * (v - x * y)) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, ← hc, ← Matrix.mul_assoc G, ← Matrix.mul_assoc, hxx,
      Matrix.smul_mul, hBy, hec, sub_self]
  refine ⟨h1, ?_⟩
  have h2 : (v - x * y)ᴴ * (G * x) = 0 := by
    rw [← gram_conj hG, h1, conjTranspose_zero]
  have h3 : (v - x * y)ᴴ * (G * v) = vᴴ * (G * v) - yᴴ * c := by
    rw [conjTranspose_sub, Matrix.sub_mul, conjTranspose_mul, Matrix.mul_assoc, ← hc]
  rw [Matrix.mul_sub, Matrix.mul_sub, h3, ← Matrix.mul_assoc G, ← Matrix.mul_assoc _ (G * x), h2,
    Matrix.zero_mul, sub_zero, ← hBy]
  exact hq

/- English proof (translation)
Use `set w₀ : Matrix ι τ A := Gi * (e • L)ᴴ with hw₀`. Establish `hGw : G * w₀ = (e • L)ᴴ` using `by rw [hw₀, ← Matrix.mul_assoc, hGi, Matrix.one_mul]`. Establish `hew : e • w₀ = w₀`. Rewrite using `[hw₀, ← Matrix.mul_smul, conjTranspose_smul, hse, smul_smul, he]`. Establish `h1 : xᴴ * (G * w₀) = 0`.

Rewrite using `[hGw, ← conjTranspose_mul, Matrix.smul_mul, hLx, smul_zero, conjTranspose_zero]`. Establish `h2 : uᴴ * (G * w₀) = e • 1`. Rewrite using `[hGw, ← conjTranspose_mul, Matrix.smul_mul, hLu, smul_smul, he, conjTranspose_smul, hse, conjTranspose_one]`. Establish `h3 : w₀ᴴ * (G * u) = e • 1`. Rewrite using `[← gram_conj hG, h2, conjTranspose_smul, hse, conjTranspose_one]`.

Use `set Q := w₀ᴴ * (G * w₀) with hQ`. Establish `hQh : Qᴴ = Q` using `gram_conj hG w₀ w₀`. Establish `heQ : e • Q = Q` using `by conv_lhs => rw [hQ, ← Matrix.mul_smul, ← Matrix.mul_smul, hew]`. Establish `hP : (h • Q)ᴴ = h • Q` using `by rw [conjTranspose_smul, hsh, hQh]`. Establish `hw : e • (w₀ - u * (h • Q)) = w₀ - u * (h • Q)`.

Rewrite using `[smul_sub, hew, ← Matrix.smul_mul, hu]`. Establish `hxw : xᴴ * (G * (w₀ - u * (h • Q))) = 0`. Rewrite using `[Matrix.mul_sub, Matrix.mul_sub, h1, ← Matrix.mul_assoc G, ← Matrix.mul_assoc _ (G * u), hxu, Matrix.zero_mul, sub_zero]`. Establish `huw : uᴴ * (G * (w₀ - u * (h • Q))) = e • 1`. Rewrite using `[Matrix.mul_sub, Matrix.mul_sub, h2, ← Matrix.mul_assoc G, ← Matrix.mul_assoc _ (G * u), huu, Matrix.zero_mul, sub_zero]`.

Use `⟨w₀ - u * (h • Q), hw, hxw, huw, ?_⟩` and prove the remaining obligations. Establish `h4 : w₀ᴴ * (G * (w₀ - u * (h • Q))) = Q - h • Q`. Rewrite using `[Matrix.mul_sub, Matrix.mul_sub, ← hQ, ← Matrix.mul_assoc G, ← Matrix.mul_assoc _ (G * u), h3, Matrix.smul_mul, Matrix.one_mul, smul_comm, heQ]`. Rewrite using `[conjTranspose_sub, Matrix.sub_mul, h4, conjTranspose_mul, hP, Matrix.mul_assoc, huw, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, heQ, sub_sub, ← add_smul, hh, one_smul, sub_self]`.
-/
theorem exists_dual {G Gi : Matrix ι ι A} (hG : Gᴴ = G) (hGi : G * Gi = 1)
    {e h : A} (he : e * e = e) (hse : star e = e) (hh : h + h = 1) (hsh : star h = h)
    {x : Matrix ι ρ A} {u : Matrix ι τ A} {L : Matrix τ ι A} (hu : e • u = u)
    (hxu : xᴴ * (G * u) = 0) (huu : uᴴ * (G * u) = 0) (hLx : L * x = 0) (hLu : L * u = e • 1) :
    ∃ w : Matrix ι τ A, e • w = w ∧ xᴴ * (G * w) = 0 ∧ uᴴ * (G * w) = e • 1 ∧ wᴴ * (G * w) = 0 := by
  set w₀ : Matrix ι τ A := Gi * (e • L)ᴴ with hw₀
  have hGw : G * w₀ = (e • L)ᴴ := by rw [hw₀, ← Matrix.mul_assoc, hGi, Matrix.one_mul]
  have hew : e • w₀ = w₀ := by
    rw [hw₀, ← Matrix.mul_smul, conjTranspose_smul, hse, smul_smul, he]
  have h1 : xᴴ * (G * w₀) = 0 := by
    rw [hGw, ← conjTranspose_mul, Matrix.smul_mul, hLx, smul_zero, conjTranspose_zero]
  have h2 : uᴴ * (G * w₀) = e • 1 := by
    rw [hGw, ← conjTranspose_mul, Matrix.smul_mul, hLu, smul_smul, he, conjTranspose_smul, hse,
      conjTranspose_one]
  have h3 : w₀ᴴ * (G * u) = e • 1 := by
    rw [← gram_conj hG, h2, conjTranspose_smul, hse, conjTranspose_one]
  set Q := w₀ᴴ * (G * w₀) with hQ
  have hQh : Qᴴ = Q := gram_conj hG w₀ w₀
  have heQ : e • Q = Q := by
    conv_lhs => rw [hQ, ← Matrix.mul_smul, ← Matrix.mul_smul, hew]
  have hP : (h • Q)ᴴ = h • Q := by rw [conjTranspose_smul, hsh, hQh]
  have hw : e • (w₀ - u * (h • Q)) = w₀ - u * (h • Q) := by
    rw [smul_sub, hew, ← Matrix.smul_mul, hu]
  have hxw : xᴴ * (G * (w₀ - u * (h • Q))) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, h1, ← Matrix.mul_assoc G, ← Matrix.mul_assoc _ (G * u), hxu,
      Matrix.zero_mul, sub_zero]
  have huw : uᴴ * (G * (w₀ - u * (h • Q))) = e • 1 := by
    rw [Matrix.mul_sub, Matrix.mul_sub, h2, ← Matrix.mul_assoc G, ← Matrix.mul_assoc _ (G * u), huu,
      Matrix.zero_mul, sub_zero]
  refine ⟨w₀ - u * (h • Q), hw, hxw, huw, ?_⟩
  have h4 : w₀ᴴ * (G * (w₀ - u * (h • Q))) = Q - h • Q := by
    rw [Matrix.mul_sub, Matrix.mul_sub, ← hQ, ← Matrix.mul_assoc G, ← Matrix.mul_assoc _ (G * u), h3,
      Matrix.smul_mul, Matrix.one_mul, smul_comm, heQ]
  rw [conjTranspose_sub, Matrix.sub_mul, h4, conjTranspose_mul, hP, Matrix.mul_assoc, huw,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, heQ, sub_sub, ← add_smul, hh, one_smul, sub_self]

/- English proof (translation)
Apply the tactic sequence `ext (( i | i) | i) ((j | j) | j) <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, conjTranspose_apply]`.
-/
theorem gram_three {G : Matrix ι ι A} {κ₁ κ₂ κ₃ : Type*} [Fintype κ₁] [Fintype κ₂] [Fintype κ₃]
    (x : Matrix ι κ₁ A) (u : Matrix ι κ₂ A) (w : Matrix ι κ₃ A) :
    (fromCols (fromCols x u) w)ᴴ * (G * fromCols (fromCols x u) w) =
      fromBlocks (fromBlocks (xᴴ * (G * x)) (xᴴ * (G * u)) (uᴴ * (G * x)) (uᴴ * (G * u)))
        (fromRows (xᴴ * (G * w)) (uᴴ * (G * w)))
        (fromCols (wᴴ * (G * x)) (wᴴ * (G * u))) (wᴴ * (G * w)) := by
  ext (( i | i) | i) ((j | j) | j) <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, conjTranspose_apply]

end Abstract

def gam {K ρ τ : Type*} [Zero K] [One K] [DecidableEq τ] (b : Matrix ρ ρ K) :
    Matrix ((ρ ⊕ τ) ⊕ τ) ((ρ ⊕ τ) ⊕ τ) K :=
  fromBlocks (fromBlocks b 0 0 0) (fromRows 0 1) (fromCols 0 1) 0

/- English proof (translation)
Apply the tactic sequence `ext ((i | i) | i) ((j | j) | j) <;> simp [gam, Matrix.one_apply, apply_ite f]`.
-/
theorem gam_map {K L ρ τ : Type*} [Semiring K] [Semiring L] [DecidableEq τ] (f : K →+* L)
    (b : Matrix ρ ρ K) : (gam (τ := τ) b).map f = gam (b.map f) := by
  ext ((i | i) | i) ((j | j) | j) <;> simp [gam, Matrix.one_apply, apply_ite f]

/- English proof (translation)
Establish `hinv : ∀ i j, ∑ a, b⁻¹ i a * b a j = if i = j then 1 else 0` using `fun i j => by`. Use `congrFun (congrFun (Matrix.nonsing_inv_mul b (isUnit_iff_ne_zero.2 hb)) i) j` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Use `Matrix.det_ne_zero_of_left_inverse (B := gam (τ := Fin t) b⁻¹) ?_` and prove the remaining obligations. Apply the tactic sequence `ext ((i | i) | i) ((j | j) | j) <;>`.

Simplify using `[gam, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, hinv]`.
-/
theorem gam_det {K : Type*} [Field K] {r t : ℕ} (b : Matrix (Fin r) (Fin r) K) (hb : b.det ≠ 0) :
    (gam (τ := Fin t) b).det ≠ 0 := by
  have hinv : ∀ i j, ∑ a, b⁻¹ i a * b a j = if i = j then 1 else 0 := fun i j => by
    have := congrFun (congrFun (Matrix.nonsing_inv_mul b (isUnit_iff_ne_zero.2 hb)) i) j
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  refine Matrix.det_ne_zero_of_left_inverse (B := gam (τ := Fin t) b⁻¹) ?_
  ext ((i | i) | i) ((j | j) | j) <;>
    simp [gam, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, hinv]

section Involution

variable {A : Type} [CommRing A] {ι ρ τ : Type} [Fintype ι] [Fintype ρ] [Fintype τ]
  [DecidableEq ι] [DecidableEq ρ] [DecidableEq τ]

/- English proof (translation)
Use `letI : StarRing A := { star := σ star_involutive := hσ star_mul := fun a b => by rw [map_mul, mul_comm] star_add := map_add σ }`. Establish `hmap : ∀ {α β : Type} (M : Matrix α β A), (M.map σ)ᵀ = Mᴴ` using `fun M => by`. Use extensionality with `i j`. Both sides reduce to the same expression. Simplify using `only [hmap] at hG hxx hq ⊢`.

Take `⟨hxu, huu⟩` from `orth_part hG hB hv hxx hq`. Use `set u : Matrix ι τ A := v - x * (Bi * (xᴴ * (G * v))) with hu`. Establish `heu : e • u = u`. Establish `hy : e • (x * (Bi * (xᴴ * (G * v)))) = x * (Bi * (xᴴ * (G * v)))`. Rewrite using `[← Matrix.smul_mul, hx]`.

Rewrite using `[hu, smul_sub, hv, hy]`. Establish `hLu : L * u = e • 1`. Rewrite using `[hu, Matrix.mul_sub, hLv, ← Matrix.mul_assoc, hLx, Matrix.zero_mul, sub_zero]`. Take `⟨w, hew, hxw, huw, hww⟩` from `exists_dual hG hGi he (show star e = e from hse) hh (show star h = h from hsh) heu hxu huu hLx hLu`. Use `⟨fromCols (fromCols x u) w, ?_, ?_, fun i j => rfl, fun i j => rfl⟩` and prove the remaining obligations.

Use extensionality with `i ((j | j) | j)`. Simplify using `using congrFun (congrFun hx i) j`. Simplify using `using congrFun (congrFun heu i) j`. Simplify using `using congrFun (congrFun hew i) j`. Establish `hux : uᴴ * (G * x) = 0` using `by rw [← gram_conj hG, hxu, conjTranspose_zero]`.

Establish `hwx : wᴴ * (G * x) = 0` using `by rw [← gram_conj hG, hxw, conjTranspose_zero]`. Establish `hwu : wᴴ * (G * u) = e • 1`. Rewrite using `[← gram_conj hG, huw, conjTranspose_smul, conjTranspose_one]`. Conclude with `congrArg (· • (1 : Matrix τ τ A)) hse`. Rewrite using `[gram_three, hxx, hxu, huu, hxw, huw, hww, hux, hwx, hwu]`.

Apply the tactic sequence `ext ((i | i) | i) ((j | j) | j) <;> simp [gam, Matrix.one_apply]`.
-/
theorem complete_frame (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) {G Gi : Matrix ι ι A}
    (hG : (G.map σ)ᵀ = G) (hGi : G * Gi = 1) {B Bi : Matrix ρ ρ A} (hB : B * Bi = 1)
    {e h : A} (he : e * e = e) (hse : σ e = e) (hh : h + h = 1) (hsh : σ h = h)
    {x : Matrix ι ρ A} {v : Matrix ι τ A} {L : Matrix τ ι A} (hx : e • x = x) (hv : e • v = v)
    (hxx : (x.map σ)ᵀ * (G * x) = e • B)
    (hq : (v.map σ)ᵀ * (G * v) - ((Bi * ((x.map σ)ᵀ * (G * v))).map σ)ᵀ *
      (B * (Bi * ((x.map σ)ᵀ * (G * v)))) = 0)
    (hLx : L * x = 0) (hLv : L * v = e • 1) :
    ∃ N : Matrix ι ((ρ ⊕ τ) ⊕ τ) A, e • N = N ∧ (N.map σ)ᵀ * (G * N) = e • gam B ∧
      (∀ i j, N i (Sum.inl (Sum.inl j)) = x i j) ∧
      ∀ i j, N i (Sum.inl (Sum.inr j)) = (v - x * (Bi * ((x.map σ)ᵀ * (G * v)))) i j := by
  letI : StarRing A :=
    { star := σ
      star_involutive := hσ
      star_mul := fun a b => by rw [map_mul, mul_comm]
      star_add := map_add σ }
  have hmap : ∀ {α β : Type} (M : Matrix α β A), (M.map σ)ᵀ = Mᴴ := fun M => by
    ext i j; rfl
  simp only [hmap] at hG hxx hq ⊢
  obtain ⟨hxu, huu⟩ := orth_part hG hB hv hxx hq
  set u : Matrix ι τ A := v - x * (Bi * (xᴴ * (G * v))) with hu
  have heu : e • u = u := by
    have hy : e • (x * (Bi * (xᴴ * (G * v)))) = x * (Bi * (xᴴ * (G * v))) := by
      rw [← Matrix.smul_mul, hx]
    rw [hu, smul_sub, hv, hy]
  have hLu : L * u = e • 1 := by
    rw [hu, Matrix.mul_sub, hLv, ← Matrix.mul_assoc, hLx, Matrix.zero_mul, sub_zero]
  obtain ⟨w, hew, hxw, huw, hww⟩ :=
    exists_dual hG hGi he (show star e = e from hse) hh (show star h = h from hsh) heu hxu huu hLx hLu
  refine ⟨fromCols (fromCols x u) w, ?_, ?_, fun i j => rfl, fun i j => rfl⟩
  · ext i ((j | j) | j)
    · simpa using congrFun (congrFun hx i) j
    · simpa using congrFun (congrFun heu i) j
    · simpa using congrFun (congrFun hew i) j
  · have hux : uᴴ * (G * x) = 0 := by rw [← gram_conj hG, hxu, conjTranspose_zero]
    have hwx : wᴴ * (G * x) = 0 := by rw [← gram_conj hG, hxw, conjTranspose_zero]
    have hwu : wᴴ * (G * u) = e • 1 := by
      rw [← gram_conj hG, huw, conjTranspose_smul, conjTranspose_one]
      exact congrArg (· • (1 : Matrix τ τ A)) hse
    rw [gram_three, hxx, hxu, huu, hxw, huw, hww, hux, hwx, hwu]
    ext ((i | i) | i) ((j | j) | j) <;> simp [gam, Matrix.one_apply]

end Involution

/- English proof (translation)
Introduce `D r t V b₀ hb e he hse`. Use `⟨gam b₀.1, gam_det _ hb, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨x, v⟩ ⟨L₁, L₂, -, -, h21, h22⟩ ⟨hx, hv, hxx, hq⟩`. Establish `hdet : IsUnit (HSpace.gram V).det` using `isUnit_iff_ne_zero.2 (isHermND_gram V).2`. Establish `hGi : gA V * giA V = 1`.

Use `rat_mul (D := D) (HSpace.gram V) (HSpace.gram V)⁻¹` as an intermediate fact. Rewrite `this` using `[Matrix.mul_nonsing_inv _ hdet]`. Conclude with `this.symm.trans (by simp [rat])`. Establish `hB : rat (D` using `D) b₀.1 * rat b₀.1⁻¹ = 1 := by`. Use `rat_mul (D := D) b₀.1 b₀.1⁻¹` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hb)]`. Conclude with `this.symm.trans (by simp [rat])`. Establish `hh : incA D 2⁻¹ + incA D 2⁻¹ = 1`. Rewrite using `[← map_add, ← two_mul, mul_inv_cancel₀ two_ne_zero, map_one]`. Establish `hsh : cA D (incA D 2⁻¹) = incA D 2⁻¹`.

Rewrite using `[GlobalTheory.DualPairCheck.cA_incA, star_inv₀, star_ofNat]`. Take `⟨N, h1, h2, h3, h4⟩` from `complete_frame (cA D) cA_cA (G := gA V) (Gi := giA V) (adj_gA V) hGi hB he hse hh hsh (x := x) (v := v) (L := L₂) hx hv hxx hq h21 h22`. Use `⟨N, h1, ?_, h3, h4⟩` and prove the remaining obligations. Rewrite using `[gam_map]`. Conclude with `h2`.
-/
theorem frame_completes : ∀ (D : D7) (r t : ℕ) (V : HSp D) (b₀ : HermE D r), b₀.1.det ≠ 0 → ∀ e : AE D, e * e = e → cA D e = e → ∃ Γ : Matrix ((Fin r ⊕ Fin t) ⊕ Fin t) ((Fin r ⊕ Fin t) ⊕ Fin t) D.host.E, Γ.det ≠ 0 ∧ ∀ z : Mx D V.rank r × Mx D V.rank t, Free e z → (e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ ip V z.1 z.1 = e • rat b₀.1 ∧ qv V b₀ z = 0) → ∃ N : Matrix (Fin V.rank) ((Fin r ⊕ Fin t) ⊕ Fin t) (AE D), e • N = N ∧ (HMul.hMul (N.map (cA D))ᵀ (HMul.hMul (gA V) N : Matrix (Fin V.rank) ((Fin r ⊕ Fin t) ⊕ Fin t) (AE D)) : Matrix ((Fin r ⊕ Fin t) ⊕ Fin t) ((Fin r ⊕ Fin t) ⊕ Fin t) (AE D)) = e • Γ.map (incA D) ∧ (∀ i j, N i (Sum.inl (Sum.inl j)) = z.1 i j) ∧ ∀ i j, N i (Sum.inl (Sum.inr j)) = (z.2 - mm z.1 (yv V b₀ z)) i j := by
  intro D r t V b₀ hb e he hse
  refine ⟨gam b₀.1, gam_det _ hb, ?_⟩
  rintro ⟨x, v⟩ ⟨L₁, L₂, -, -, h21, h22⟩ ⟨hx, hv, hxx, hq⟩
  have hdet : IsUnit (HSpace.gram V).det := isUnit_iff_ne_zero.2 (isHermND_gram V).2
  have hGi : gA V * giA V = 1 := by
    have := rat_mul (D := D) (HSpace.gram V) (HSpace.gram V)⁻¹
    rw [Matrix.mul_nonsing_inv _ hdet] at this
    exact this.symm.trans (by simp [rat])
  have hB : rat (D := D) b₀.1 * rat b₀.1⁻¹ = 1 := by
    have := rat_mul (D := D) b₀.1 b₀.1⁻¹
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hb)] at this
    exact this.symm.trans (by simp [rat])
  have hh : incA D 2⁻¹ + incA D 2⁻¹ = 1 := by
    rw [← map_add, ← two_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  have hsh : cA D (incA D 2⁻¹) = incA D 2⁻¹ := by
    rw [GlobalTheory.DualPairCheck.cA_incA, star_inv₀, star_ofNat]
  obtain ⟨N, h1, h2, h3, h4⟩ := complete_frame (cA D) cA_cA (G := gA V) (Gi := giA V) (adj_gA V) hGi
    hB he hse hh hsh (x := x) (v := v) (L := L₂) hx hv hxx hq h21 h22
  refine ⟨N, h1, ?_, h3, h4⟩
  rw [gam_map]
  exact h2

end GlobalTheory.CompanionTheory.FrameComplete
