import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CongruenceDet

open NumberField Matrix in
open scoped nonZeroDivisors in

/- English proof (translation)
Establish `hdet : (scalar (Fin r) μ - g.map (algebraMap E K)).det = 0`. Rewrite using `[← Matrix.eval_charpoly]`. Conclude with `hμ`. Take `⟨u, hu0, hu⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 hdet`. Establish `hug : u ᵥ* g.map (algebraMap E K) = μ • u`.

Rewrite `hu` using `[Matrix.vecMul_sub, sub_eq_zero]`. Rewrite using `[← hu]`. Use extensionality with `i`. Simplify using `[Matrix.scalar_apply, Matrix.vecMul_diagonal, mul_comm]`. Set `ℓE : (Fin r → E) →ₗ[E] K` to `∑ i, u i • ((Algebra.linearMap E K).comp (LinearMap.proj i))`.

Establish `hℓE : ∀ v, ℓE v = u ⬝ᵥ (algebraMap E K ∘ v)`. Introduce `v`. Simplify using `[ℓE, dotProduct]`. Set `ℓ : (Fin r → E) →ₗ[R] K` to `ℓE.restrictScalars R`. Establish `hℓ : ∀ v, ℓ v = u ⬝ᵥ (algebraMap E K ∘ v)` using `hℓE`.

Establish `hMK : (M : K) ≠ 0` using `by exact_mod_cast hM`. Establish `hstep : ∀ v ∈ Λ, ∃ w ∈ Λ, ((μ - 1) / M) * ℓ v = ℓ w`. Introduce `v hv`. Take `⟨w, hw, hgv⟩` from `hg v hv`. Use `⟨w, hw, ?_⟩` and prove the remaining obligations.

Establish `hmap : algebraMap E K ∘ (g *ᵥ v) = g.map (algebraMap E K) *ᵥ (algebraMap E K ∘ v)`. Use function extensionality and compare the values at `k`. Conclude with `RingHom.map_mulVec _ _ _ k`. Establish `h1 : ℓ (g *ᵥ v) = μ * ℓ v`. Rewrite using `[hℓ, hℓ, hmap, Matrix.dotProduct_mulVec, hug, smul_dotProduct, smul_eq_mul]`.

Establish `h2 : ℓ (g *ᵥ v) = ℓ v + M * ℓ w`. Rewrite using `[hgv, map_add, map_nsmul, nsmul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `h1.symm.trans h2`. Set `N : Submodule R K` to `Λ.map ℓ`.

Establish `hN : N ≠ ⊥`. Introduce `hbot`. Establish `hker : Submodule.span E (Λ : Set (Fin r → E)) ≤ LinearMap.ker ℓE`. Rewrite using `[Submodule.span_le]`. Introduce `v hv`.

Establish `: ℓ v ∈ N` using `Submodule.mem_map_of_mem hv`. Rewrite `this` using `[hbot, Submodule.mem_bot]`. Conclude with `this`. Rewrite `hker` using `[hspan]`. Apply `hu0` to reduce the goal to its premises.

Use function extensionality and compare the values at `j`. Use `hker (Submodule.mem_top (x := Pi.single j 1))` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, hℓE]`. Simplify `this` using `[dotProduct, Pi.single_apply]`. Use `isIntegral_of_smul_mem_submodule N hN (hfg.map ℓ) _ ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨v, hv, rfl⟩`. Take `⟨w, hw, hvw⟩` from `hstep v hv`. Rewrite using `[smul_eq_mul, hvw]`. Conclude with `Submodule.mem_map_of_mem hw`.
-/
theorem _root_.GlobalTheory.CongruenceDet.isIntegral_root {R E K : Type} [CommRing R] [Field E]
    [Field K] [CharZero K]
    [Algebra R E] [Algebra R K] [Algebra E K] [IsScalarTower R E K] {r M : ℕ} (hM : M ≠ 0)
    (Λ : Submodule R (Fin r → E)) (g : Matrix (Fin r) (Fin r) E) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hg : ∀ v ∈ Λ, ∃ w ∈ Λ, g *ᵥ v = v + M • w) (μ : K)
    (hμ : (g.map (algebraMap E K)).charpoly.IsRoot μ) :
    IsIntegral R ((μ - 1) / M) := by
  classical
  have hdet : (scalar (Fin r) μ - g.map (algebraMap E K)).det = 0 := by
    rw [← Matrix.eval_charpoly]
    exact hμ
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  have hug : u ᵥ* g.map (algebraMap E K) = μ • u := by
    rw [Matrix.vecMul_sub, sub_eq_zero] at hu
    rw [← hu]
    ext i
    simp [Matrix.scalar_apply, Matrix.vecMul_diagonal, mul_comm]
  let ℓE : (Fin r → E) →ₗ[E] K :=
    ∑ i, u i • ((Algebra.linearMap E K).comp (LinearMap.proj i))
  have hℓE : ∀ v, ℓE v = u ⬝ᵥ (algebraMap E K ∘ v) := by
    intro v
    simp [ℓE, dotProduct]
  let ℓ : (Fin r → E) →ₗ[R] K := ℓE.restrictScalars R
  have hℓ : ∀ v, ℓ v = u ⬝ᵥ (algebraMap E K ∘ v) := hℓE
  have hMK : (M : K) ≠ 0 := by exact_mod_cast hM
  have hstep : ∀ v ∈ Λ, ∃ w ∈ Λ, ((μ - 1) / M) * ℓ v = ℓ w := by
    intro v hv
    obtain ⟨w, hw, hgv⟩ := hg v hv
    refine ⟨w, hw, ?_⟩
    have hmap : algebraMap E K ∘ (g *ᵥ v) = g.map (algebraMap E K) *ᵥ (algebraMap E K ∘ v) := by
      funext k
      exact RingHom.map_mulVec _ _ _ k
    have h1 : ℓ (g *ᵥ v) = μ * ℓ v := by
      rw [hℓ, hℓ, hmap, Matrix.dotProduct_mulVec, hug, smul_dotProduct, smul_eq_mul]
    have h2 : ℓ (g *ᵥ v) = ℓ v + M * ℓ w := by
      rw [hgv, map_add, map_nsmul, nsmul_eq_mul]
    field_simp
    linear_combination h1.symm.trans h2
  let N : Submodule R K := Λ.map ℓ
  have hN : N ≠ ⊥ := by
    intro hbot
    have hker : Submodule.span E (Λ : Set (Fin r → E)) ≤ LinearMap.ker ℓE := by
      rw [Submodule.span_le]
      intro v hv
      have : ℓ v ∈ N := Submodule.mem_map_of_mem hv
      rw [hbot, Submodule.mem_bot] at this
      exact this
    rw [hspan] at hker
    apply hu0
    funext j
    have := hker (Submodule.mem_top (x := Pi.single j 1))
    rw [LinearMap.mem_ker, hℓE] at this
    simpa [dotProduct, Pi.single_apply] using this
  refine isIntegral_of_smul_mem_submodule N hN (hfg.map ℓ) _ ?_
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨w, hw, hvw⟩ := hstep v hv
  rw [smul_eq_mul, hvw]
  exact Submodule.mem_map_of_mem hw

open NumberField Matrix in
open scoped nonZeroDivisors in

/- English proof (translation)
Set `K` to `AlgebraicClosure E`. Use `haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap E K).injective`. Establish `hroots : ∀ μ ∈ (g.map (algebraMap E K)).charpoly.roots, IsIntegral R ((μ - 1) / M)` using `fun μ hμ => _root_.GlobalTheory.CongruenceDet.isIntegral_root hM Λ g hfg hspan hg μ (Polynomial.isRoot_of_mem_roots hμ)`. Establish `hMK : (M : K) ≠ 0` using `by exact_mod_cast hM`. Establish `hMint : IsIntegral R (M : K)`.

Simplify using `using isIntegral_algebraMap (R := R) (A := K) (x := (M : R))`. Establish `hprod : ∀ s : Multiset K, (∀ μ ∈ s, IsIntegral R ((μ - 1) / M)) → IsIntegral R ((s.prod - 1) / M)`. Introduce `s`. Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => intro _`.

Simplify using `using isIntegral_zero`. Consider the case `cons a s ih`. Introduce `hs`. Establish `ha` using `hs a (Multiset.mem_cons_self a s)`. Establish `hb` using `ih (fun μ hμ => hs μ (Multiset.mem_cons_of_mem hμ))`.

Establish `key : ((a ::ₘ s).prod - 1) / M = (a - 1) / M * (M * ((s.prod - 1) / M) + 1) + (s.prod - 1) / M`. Rewrite using `[Multiset.prod_cons, mul_div_cancel₀ _ hMK]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `(ha.mul ((hMint.mul hb).add isIntegral_one)).add hb`.

Establish `h1 : algebraMap E K g.det = (g.map (algebraMap E K)).det`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Establish `hK` using `hprod _ hroots`. Rewrite `hK` using `[← Matrix.det_eq_prod_roots_charpoly, ← h1]`.

Establish `hK' : IsIntegral R (IsScalarTower.toAlgHom R E K ((g.det - 1) / M))`. Simplify `hK` using `[map_div₀, map_sub, map_one, map_natCast]`. Conclude with `(isIntegral_algHom_iff _ (algebraMap E K).injective).1 hK'`.
-/
theorem _root_.GlobalTheory.CongruenceDet.isIntegral_det_sub_one {R E : Type} [CommRing R] [Field E]
    [CharZero E]
    [Algebra R E] {r M : ℕ} (hM : M ≠ 0)
    (Λ : Submodule R (Fin r → E)) (g : Matrix (Fin r) (Fin r) E) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hg : ∀ v ∈ Λ, ∃ w ∈ Λ, g *ᵥ v = v + M • w) :
    IsIntegral R ((g.det - 1) / M) := by
  classical
  let K := AlgebraicClosure E

  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap E K).injective
  have hroots : ∀ μ ∈ (g.map (algebraMap E K)).charpoly.roots, IsIntegral R ((μ - 1) / M) :=
    fun μ hμ => _root_.GlobalTheory.CongruenceDet.isIntegral_root hM Λ g hfg hspan hg μ
      (Polynomial.isRoot_of_mem_roots hμ)
  have hMK : (M : K) ≠ 0 := by exact_mod_cast hM
  have hMint : IsIntegral R (M : K) := by
    simpa using isIntegral_algebraMap (R := R) (A := K) (x := (M : R))
  have hprod : ∀ s : Multiset K, (∀ μ ∈ s, IsIntegral R ((μ - 1) / M)) →
      IsIntegral R ((s.prod - 1) / M) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simpa using isIntegral_zero
    | cons a s ih =>
      intro hs
      have ha := hs a (Multiset.mem_cons_self a s)
      have hb := ih (fun μ hμ => hs μ (Multiset.mem_cons_of_mem hμ))
      have key : ((a ::ₘ s).prod - 1) / M =
          (a - 1) / M * (M * ((s.prod - 1) / M) + 1) + (s.prod - 1) / M := by
        rw [Multiset.prod_cons, mul_div_cancel₀ _ hMK]
        ring
      rw [key]
      exact (ha.mul ((hMint.mul hb).add isIntegral_one)).add hb
  have h1 : algebraMap E K g.det = (g.map (algebraMap E K)).det := by
    rw [RingHom.map_det]
    rfl
  have hK := hprod _ hroots
  rw [← Matrix.det_eq_prod_roots_charpoly, ← h1] at hK
  have hK' : IsIntegral R (IsScalarTower.toAlgHom R E K ((g.det - 1) / M)) := by
    simpa [map_div₀, map_sub, map_one, map_natCast] using hK
  exact (isIntegral_algHom_iff _ (algebraMap E K).injective).1 hK'

open NumberField Matrix in
open scoped nonZeroDivisors in

/- English proof (translation)
Set `c : E →+* E` to `(IsCMField.complexConj E : E →+* E)`. Establish `hherm : ∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y = x ⬝ᵥ (G *ᵥ (c ∘ y))`. Introduce `x y`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.herm _root_.ReciprocityTheory.ChartRestriction.G.FD.cc`. Simplify using `[dotProduct, mulVec, Finset.mul_sum, mul_assoc, c]`.

Establish `hmat : gᵀ * G * g.map c = G`. Use extensionality with `i j`. Use `h (Pi.single i 1) (Pi.single j 1)` as an intermediate fact. Establish `hcs : c ∘ (Pi.single j (1 : E)) = Pi.single j 1`. Use function extensionality and compare the values at `k`.

Apply the tactic sequence `by_cases hk : k = j <;> simp [Pi.single_apply, hk]`. Establish `hgs : c ∘ (g *ᵥ Pi.single j 1) = g.map c *ᵥ (c ∘ Pi.single j 1)`. Use function extensionality and compare the values at `k`. Conclude with `RingHom.map_mulVec _ _ _ k`. Rewrite `this` using `[hherm, hherm, hgs, hcs, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`.

Simplify `this` using `[Matrix.mul_assoc]`. Establish `hdet` using `congrArg Matrix.det hmat`. Rewrite `hdet` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Establish `e : c g.det = IsCMField.complexConj E g.det` using `rfl`. Apply `mul_right_cancel₀ hG` to reduce the goal to its premises.

Rewrite using `[← e]`. Take the linear combination `hdet`.
-/
theorem _root_.GlobalTheory.CongruenceDet.det_mul_conj {E : Type} [Field E] [NumberField E]
    [IsCMField E] {r : ℕ}
    (G g : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (h : ∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (g *ᵥ x) (g *ᵥ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y) :
    g.det * IsCMField.complexConj E g.det = 1 := by
  classical
  let c : E →+* E := (IsCMField.complexConj E : E →+* E)
  have hherm : ∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y = x ⬝ᵥ (G *ᵥ (c ∘ y)) := by
    intro x y
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
    simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc, c]
  have hmat : gᵀ * G * g.map c = G := by
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    have hcs : c ∘ (Pi.single j (1 : E)) = Pi.single j 1 := by
      funext k
      by_cases hk : k = j <;> simp [Pi.single_apply, hk]
    have hgs : c ∘ (g *ᵥ Pi.single j 1) = g.map c *ᵥ (c ∘ Pi.single j 1) := by
      funext k
      exact RingHom.map_mulVec _ _ _ k
    rw [hherm, hherm, hgs, hcs, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    simpa [Matrix.mul_assoc] using this
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det] at hdet
  have e : c g.det = IsCMField.complexConj E g.det := rfl
  apply mul_right_cancel₀ hG
  rw [← e]
  linear_combination hdet

open NumberField Matrix in
open scoped nonZeroDivisors in

/- English proof (translation)
Introduce `E _ _ _ r M Gm Λ γ hG hfg hspan hM hU hγ`. Establish `hM0 : M ≠ 0` using `by omega`. Establish `hUisom : ∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm x y`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab at hU`. Conclude with `hU.1`.

Use `set d := (γ : Matrix (Fin r) (Fin r) E).det with hd`. Establish `hint : IsIntegral ℤ ((d - 1) / M)` using `isIntegral_trans _ (_root_.GlobalTheory.CongruenceDet.isIntegral_det_sub_one hM0 Λ _ hfg hspan hγ)`. Establish `hconj : d * IsCMField.complexConj E d = 1` using `_root_.GlobalTheory.CongruenceDet.det_mul_conj Gm _ hG hUisom`. Establish `hMr : (3 : ℝ) ≤ M` using `by exact_mod_cast hM`. Establish `habs : ∀ φ : E →+* ℂ, ‖φ ((d - 1) / M)‖ ≤ 2 / 3`.

Introduce `φ`. Establish `h1 : ‖φ d‖ = 1`. Use `congrArg φ hconj` as an intermediate fact. Rewrite `this` using `[map_mul, IsCMField.complexEmbedding_complexConj, Complex.mul_conj, map_one]`. Establish `h2 : Complex.normSq (φ d) = 1` using `by exact_mod_cast this`.

Rewrite `h2` using `[Complex.normSq_eq_norm_sq]`. Use polynomial arithmetic with `[norm_nonneg (φ d)]`. Rewrite using `[map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast]`. Establish `h3 : ‖φ d - 1‖ ≤ 2` using `(norm_sub_le _ _).trans (by rw [h1, norm_one]; norm_num)`. Rewrite using `[div_le_iff₀ (by linarith)]`.

Use the polynomial consequences of the given equalities and inequalities. Assume the negation of the conclusion as `hne`. Establish `hx : (d - 1) / M ≠ 0`. Introduce `h0`. Rewrite `h0` using `[div_eq_zero_iff]`.

Break down `h0 with h0 | h0` into its components or cases. Conclude with `hne (sub_eq_zero.1 h0)`. Conclude with `hM0 (by exact_mod_cast h0)`. Take `⟨n, hn⟩` from `IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm ℚ hint)`. Establish `hn0 : n ≠ 0`.

Introduce and unpack `rfl`. Apply `hx` to reduce the goal to its premises. Rewrite `hn` using `[map_zero, eq_comm, Algebra.norm_eq_zero_iff]`. Conclude with `hn`. Establish `hprod` using `Algebra.norm_eq_prod_embeddings ℚ ℂ ((d - 1) / M)`.

Rewrite `hprod` using `[← hn]`. Establish `hle : ‖∏ σ : E →ₐ[ℚ] ℂ, σ ((d - 1) / M)‖ ≤ (2 / 3 : ℝ) ^ Fintype.card (E →ₐ[ℚ] ℂ)`. Rewrite using `[norm_prod, ← Finset.card_univ, ← Finset.prod_const]`. Conclude with `Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun σ _ => habs σ.toRingHom)`. Establish `hcard : 0 < Fintype.card (E →ₐ[ℚ] ℂ)` using `Fintype.card_pos_iff.2 ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ)⟩`.

Establish `hlt : (2 / 3 : ℝ) ^ Fintype.card (E →ₐ[ℚ] ℂ) < 1` using `pow_lt_one₀ (by norm_num) (by norm_num) hcard.ne'`. Rewrite `hle` using `[← hprod]`. Establish `hge : (1 : ℝ) ≤ ‖(algebraMap ℚ ℂ) ((algebraMap ℤ ℚ) n)‖`. Establish `hcast : (algebraMap ℚ ℂ) ((algebraMap ℤ ℚ) n) = (n : ℂ)` using `by simp`. Rewrite using `[hcast, Complex.norm_intCast]`.

Conclude with `Int.one_le_abs hn0` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem _root_.GlobalTheory.CongruenceDet.det_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (Gm : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E), Gm.det ≠ 0 → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → 3 ≤ M → _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ → (∀ v ∈ Λ, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • w) → (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  intro E _ _ _ r M Gm Λ γ hG hfg hspan hM hU hγ
  have hM0 : M ≠ 0 := by omega
  have hUisom : ∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm x y := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab at hU
    exact hU.1
  set d := (γ : Matrix (Fin r) (Fin r) E).det with hd
  have hint : IsIntegral ℤ ((d - 1) / M) :=
    isIntegral_trans _ (_root_.GlobalTheory.CongruenceDet.isIntegral_det_sub_one hM0 Λ _ hfg hspan hγ)
  have hconj : d * IsCMField.complexConj E d = 1 :=
    _root_.GlobalTheory.CongruenceDet.det_mul_conj Gm _ hG hUisom
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have habs : ∀ φ : E →+* ℂ, ‖φ ((d - 1) / M)‖ ≤ 2 / 3 := by
    intro φ
    have h1 : ‖φ d‖ = 1 := by
      have := congrArg φ hconj
      rw [map_mul, IsCMField.complexEmbedding_complexConj, Complex.mul_conj, map_one] at this
      have h2 : Complex.normSq (φ d) = 1 := by exact_mod_cast this
      rw [Complex.normSq_eq_norm_sq] at h2
      nlinarith [norm_nonneg (φ d)]
    rw [map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast]
    have h3 : ‖φ d - 1‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [h1, norm_one]; norm_num)
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  by_contra hne
  have hx : (d - 1) / M ≠ 0 := by
    intro h0
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact hne (sub_eq_zero.1 h0)
    · exact hM0 (by exact_mod_cast h0)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm ℚ hint)
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hx
    rw [map_zero, eq_comm, Algebra.norm_eq_zero_iff] at hn
    exact hn
  have hprod := Algebra.norm_eq_prod_embeddings ℚ ℂ ((d - 1) / M)
  rw [← hn] at hprod
  have hle : ‖∏ σ : E →ₐ[ℚ] ℂ, σ ((d - 1) / M)‖ ≤ (2 / 3 : ℝ) ^ Fintype.card (E →ₐ[ℚ] ℂ) := by
    rw [norm_prod, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun σ _ => habs σ.toRingHom)
  have hcard : 0 < Fintype.card (E →ₐ[ℚ] ℂ) :=
    Fintype.card_pos_iff.2 ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ)⟩
  have hlt : (2 / 3 : ℝ) ^ Fintype.card (E →ₐ[ℚ] ℂ) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) hcard.ne'
  rw [← hprod] at hle
  have hge : (1 : ℝ) ≤ ‖(algebraMap ℚ ℂ) ((algebraMap ℤ ℚ) n)‖ := by
    have hcast : (algebraMap ℚ ℂ) ((algebraMap ℤ ℚ) n) = (n : ℂ) := by simp
    rw [hcast, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hn0
  linarith

end GlobalTheory.CongruenceDet
