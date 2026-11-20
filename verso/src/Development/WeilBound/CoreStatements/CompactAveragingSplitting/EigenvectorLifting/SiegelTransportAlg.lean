import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

namespace PositivityTheory.ThK.SiegelT

open Matrix GlobalTheory.WeilM

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β ν ν' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν]
  [Fintype ν'] [DecidableEq ν']

/- English proof (translation)
Conclude with `Matrix.map_mul (f := c.toRingHom)`.
-/
theorem map_mul' {a b e : Type} [Fintype b] (A : Matrix a b E) (B : Matrix b e E) : (A * B).map c = A.map c * B.map c := by
  exact Matrix.map_mul (f := c.toRingHom)

/- English proof (translation)
Conclude with `Matrix.map_one c (map_zero c) (map_one c)`.
-/
theorem map_one' {a : Type} [DecidableEq a] : (1 : Matrix a a E).map c = 1 := by
  exact Matrix.map_one c (map_zero c) (map_one c)

/- English proof (translation)
Establish `hd : g.det * J.det * (g.map c).det = J.det`. Rewrite using `[← Matrix.det_transpose g, ← Matrix.det_mul, ← Matrix.det_mul, hg]`. Establish `hmap : (g.map c).det = c g.det`. Rewrite using `[AlgHom.map_det]`. Both sides reduce to the same expression.

Establish `h1 : g.det * c g.det = 1`. Apply `hJ.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[mul_one]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨⟨Matrix.nonsingInvUnit g (isUnit_iff_exists_inv.mpr ⟨_, h1⟩), hg⟩, rfl⟩`.
-/
theorem exists_UG {J g : Matrix β β E} (hJ : IsUnit J.det) (hg : gᵀ * J * g.map c = J) :
    ∃ u : UG c J, ((u : GL β E) : Matrix β β E) = g := by
  have hd : g.det * J.det * (g.map c).det = J.det := by
    rw [← Matrix.det_transpose g, ← Matrix.det_mul, ← Matrix.det_mul, hg]
  have hmap : (g.map c).det = c g.det := by
    rw [AlgHom.map_det]; rfl
  have h1 : g.det * c g.det = 1 := by
    apply hJ.mul_left_cancel
    rw [mul_one]
    calc J.det * (g.det * c g.det) = g.det * J.det * (g.map c).det := by rw [hmap]; ring
      _ = J.det := hd
  exact ⟨⟨Matrix.nonsingInvUnit g (isUnit_iff_exists_inv.mpr ⟨_, h1⟩), hg⟩, rfl⟩

omit [DecidableEq α] in

/- English proof (translation)
Unfold `SiegelRule at h ⊢`. Introduce `l hl hinv p t hpt φ hφ`. Establish `hC2 : C2 = ((γ : GL β E) : Matrix β β E) * C1 * s'`. Rewrite using `[hγ, Matrix.mul_assoc, h1, Matrix.mul_one]`. Take `⟨t', ht'⟩ : ∃ t' : GL ν E, (t' : Matrix ν ν E) = s' * (t : Matrix ν' ν' E) * s` from `⟨⟨s' * (t : Matrix ν' ν' E) * s, s' * ((t⁻¹ : GL ν' E) : Matrix ν' ν' E) * s, by`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc s s', h1, Matrix.one_mul, ← Matrix.mul_assoc (t : Matrix ν' ν' E), Units.mul_inv, Matrix.one_mul, h2], by`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc s s', h1, Matrix.one_mul, ← Matrix.mul_assoc ((t⁻¹ : GL ν' E) : Matrix ν' ν' E), Units.inv_mul, Matrix.one_mul, h2]⟩, rfl⟩`. Establish `hinvγ : (((γ : GL β E)⁻¹ : GL β E) : Matrix β β E) * ((γ : GL β E) : Matrix β β E) = 1` using `Units.inv_mul _`.

Establish `hpt' : (((γ⁻¹ * p * γ : UG c JB) : GL β E) : Matrix β β E) * C1 = C1 * (t' : Matrix ν ν E)`. Rewrite using `[ht']`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc _ ((γ : GL β E) : Matrix β β E) C1, hγ]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = (((γ : GL β E)⁻¹ : GL β E) : Matrix β β E) * C2 * ((t : Matrix ν' ν' E) * s) := by`. Rewrite using `[hpt]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = ((((γ : GL β E)⁻¹ : GL β E) : Matrix β β E) * ((γ : GL β E) : Matrix β β E)) * C1 * (s' * (t : Matrix ν' ν' E) * s) := by`.

Rewrite using `[hC2]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = C1 * (s' * (t : Matrix ν' ν' E) * s) := by rw [hinvγ, Matrix.one_mul]`. Establish `hinv1 : ∀ (z : Matrix α ν E), ∀ φ ∈ C.sp κ, (l ∘ₗ om γ) (d.rho ψ (z * C1ᵀ) φ) = (l ∘ₗ om γ) φ`. Introduce `z φ hφ`.

Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hs.impl γ (z * C1ᵀ) φ hφ]`. Establish `hz : actB c γ (z * C1ᵀ) = (z * sᵀ) * C2ᵀ` using `by show z * C1ᵀ * (((γ : GL β E) : Matrix β β E))ᵀ = _`. Rewrite using `[Matrix.mul_assoc, ← Matrix.transpose_mul, hγ, Matrix.transpose_mul, Matrix.mul_assoc]`. Rewrite using `[hz]`. Conclude with `hinv (z * sᵀ) _ (hs.pres γ φ hφ)`.

Establish `key` using `h (l ∘ₗ om γ) (hs.adm γ l hl) hinv1 (γ⁻¹ * p * γ) t' hpt' (om γ⁻¹ φ) (hs.pres γ⁻¹ φ hφ)`. Establish `e1 : om γ (om (γ⁻¹ * p * γ) (om γ⁻¹ φ)) = om p φ`. Establish `hg : γ * (γ⁻¹ * p * γ) * γ⁻¹ = p` using `by group`. Use `conv_rhs => rw [← hg]`. Simplify using `only [map_mul, Module.End.mul_apply]`.

Establish `e2 : om γ (om γ⁻¹ φ) = φ`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Establish `edet : Matrix.GeneralLinearGroup.det t' = Matrix.GeneralLinearGroup.det t`. Use `ext`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, ht', Matrix.mul_assoc, Matrix.det_comm' h2 h1, Matrix.mul_assoc, h1, Matrix.mul_one]`.

Simplify using `only [LinearMap.comp_apply] at key`. Rewrite `key` using `[e1, e2, edet]`. Conclude with `key`.
-/
theorem rule_of_conj [Invertible (2 : R)] {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}
    {κ : Type} [Fintype κ] {d : Darboux (symp c ξ JA JB) κ} {χ : Eˣ →* Circle} {C1 : Matrix β ν E} {C2 : Matrix β ν' E}
    {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)} (hs : IsSplitting C ψ d (actB c) om) (γ : UG c JB) (s : Matrix ν' ν E)
    (s' : Matrix ν ν' E) (h1 : s * s' = 1) (h2 : s' * s = 1) (hγ : ((γ : GL β E) : Matrix β β E) * C1 = C2 * s)
    (h : SiegelRule c C ψ ξ JA JB d χ C1 om) : SiegelRule c C ψ ξ JA JB d χ C2 om := by
  unfold SiegelRule at h ⊢
  intro l hl hinv p t hpt φ hφ
  have hC2 : C2 = ((γ : GL β E) : Matrix β β E) * C1 * s' := by
    rw [hγ, Matrix.mul_assoc, h1, Matrix.mul_one]
  obtain ⟨t', ht'⟩ : ∃ t' : GL ν E, (t' : Matrix ν ν E) = s' * (t : Matrix ν' ν' E) * s :=
    ⟨⟨s' * (t : Matrix ν' ν' E) * s, s' * ((t⁻¹ : GL ν' E) : Matrix ν' ν' E) * s, by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc s s', h1, Matrix.one_mul, ← Matrix.mul_assoc (t : Matrix ν' ν' E), Units.mul_inv,
          Matrix.one_mul, h2], by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc s s', h1, Matrix.one_mul, ← Matrix.mul_assoc ((t⁻¹ : GL ν' E) : Matrix ν' ν' E),
          Units.inv_mul, Matrix.one_mul, h2]⟩, rfl⟩
  have hinvγ : (((γ : GL β E)⁻¹ : GL β E) : Matrix β β E) * ((γ : GL β E) : Matrix β β E) = 1 := Units.inv_mul _
  have hpt' : (((γ⁻¹ * p * γ : UG c JB) : GL β E) : Matrix β β E) * C1 = C1 * (t' : Matrix ν ν E) := by
    rw [ht']
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    calc _ = (((γ : GL β E)⁻¹ : GL β E) : Matrix β β E) * (((p : GL β E) : Matrix β β E) * C2) * s := by
            rw [Matrix.mul_assoc _ ((γ : GL β E) : Matrix β β E) C1, hγ]; simp only [Matrix.mul_assoc]
      _ = (((γ : GL β E)⁻¹ : GL β E) : Matrix β β E) * C2 * ((t : Matrix ν' ν' E) * s) := by
            rw [hpt]; simp only [Matrix.mul_assoc]
      _ = ((((γ : GL β E)⁻¹ : GL β E) : Matrix β β E) * ((γ : GL β E) : Matrix β β E)) * C1 *
            (s' * (t : Matrix ν' ν' E) * s) := by
            rw [hC2]; simp only [Matrix.mul_assoc]
      _ = C1 * (s' * (t : Matrix ν' ν' E) * s) := by rw [hinvγ, Matrix.one_mul]
  have hinv1 : ∀ (z : Matrix α ν E), ∀ φ ∈ C.sp κ, (l ∘ₗ om γ) (d.rho ψ (z * C1ᵀ) φ) = (l ∘ₗ om γ) φ := by
    intro z φ hφ
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hs.impl γ (z * C1ᵀ) φ hφ]
    have hz : actB c γ (z * C1ᵀ) = (z * sᵀ) * C2ᵀ := by
      show z * C1ᵀ * (((γ : GL β E) : Matrix β β E))ᵀ = _
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hγ, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [hz]
    exact hinv (z * sᵀ) _ (hs.pres γ φ hφ)
  have key := h (l ∘ₗ om γ) (hs.adm γ l hl) hinv1 (γ⁻¹ * p * γ) t' hpt' (om γ⁻¹ φ) (hs.pres γ⁻¹ φ hφ)
  have e1 : om γ (om (γ⁻¹ * p * γ) (om γ⁻¹ φ)) = om p φ := by
    have hg : γ * (γ⁻¹ * p * γ) * γ⁻¹ = p := by group
    conv_rhs => rw [← hg]
    simp only [map_mul, Module.End.mul_apply]
  have e2 : om γ (om γ⁻¹ φ) = φ := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have edet : Matrix.GeneralLinearGroup.det t' = Matrix.GeneralLinearGroup.det t := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, ht', Matrix.mul_assoc,
      Matrix.det_comm' h2 h1, Matrix.mul_assoc, h1, Matrix.mul_one]
  simp only [LinearMap.comp_apply] at key
  rw [e1, e2, edet] at key
  exact key

/- English proof (translation)
Establish `mneg : ∀ {a b : Type} (A : Matrix a b E), (-A).map c = -(A.map c)` using `fun A => by ext; simp`. Establish `msub : ∀ {a b : Type} (A B : Matrix a b E), (A - B).map c = A.map c - B.map c` using `fun A B => by ext; simp`. Establish `c1e : m1.map c * ey.map c = 1` using `by rw [← map_mul', h1e, map_one']`. Establish `c1f : m1.map c * fx.map c = 0` using `by rw [← map_mul', h1f]; ext; simp`. Establish `c2e : m2.map c * ey.map c = 0` using `by rw [← map_mul', h2e]; ext; simp`.

Establish `c2f : m2.map c * fx.map c = 1` using `by rw [← map_mul', h2f, map_one']`. Establish `t1e : eyᵀ * m1ᵀ = 1` using `by rw [← Matrix.transpose_mul, h1e, Matrix.transpose_one]`. Establish `t1f : fxᵀ * m1ᵀ = 0` using `by rw [← Matrix.transpose_mul, h1f, Matrix.transpose_zero]`. Establish `t2e : eyᵀ * m2ᵀ = 0` using `by rw [← Matrix.transpose_mul, h2e, Matrix.transpose_zero]`. Establish `t2f : fxᵀ * m2ᵀ = 1` using `by rw [← Matrix.transpose_mul, h2f, Matrix.transpose_one]`.

Establish `c1e' : ∀ {k : Type} (Z : Matrix ν k E), m1.map c * (ey.map c * Z) = Z` using `fun Z => by`. Rewrite using `[← Matrix.mul_assoc, c1e, Matrix.one_mul]`. Establish `c1f' : ∀ {k : Type} (Z : Matrix ν k E), m1.map c * (fx.map c * Z) = 0` using `fun Z => by`. Rewrite using `[← Matrix.mul_assoc, c1f, Matrix.zero_mul]`. Establish `c2e' : ∀ {k : Type} (Z : Matrix ν k E), m2.map c * (ey.map c * Z) = 0` using `fun Z => by`.

Rewrite using `[← Matrix.mul_assoc, c2e, Matrix.zero_mul]`. Establish `c2f' : ∀ {k : Type} (Z : Matrix ν k E), m2.map c * (fx.map c * Z) = Z` using `fun Z => by`. Rewrite using `[← Matrix.mul_assoc, c2f, Matrix.one_mul]`. Establish `t1e' : ∀ {k : Type} (Z : Matrix ν k E), eyᵀ * (m1ᵀ * Z) = Z` using `fun Z => by`. Rewrite using `[← Matrix.mul_assoc, t1e, Matrix.one_mul]`.

Establish `t1f' : ∀ {k : Type} (Z : Matrix ν k E), fxᵀ * (m1ᵀ * Z) = 0` using `fun Z => by`. Rewrite using `[← Matrix.mul_assoc, t1f, Matrix.zero_mul]`. Establish `t2e' : ∀ {k : Type} (Z : Matrix ν k E), eyᵀ * (m2ᵀ * Z) = 0` using `fun Z => by`. Rewrite using `[← Matrix.mul_assoc, t2e, Matrix.zero_mul]`. Establish `t2f' : ∀ {k : Type} (Z : Matrix ν k E), fxᵀ * (m2ᵀ * Z) = Z` using `fun Z => by`.

Rewrite using `[← Matrix.mul_assoc, t2f, Matrix.one_mul]`. Substitute `hJ` using the available equality. Simplify using `only [Matrix.fromBlocks_map, map_one', mneg, msub, map_mul']`. Simplify using `only [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.transpose_one, Matrix.transpose_neg, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_zero]`. Rewrite using `[Matrix.fromBlocks_inj]`.

Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_⟩ <;>`. Apply the tactic sequence `simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_assoc, neg_neg, neg_zero, add_zero, zero_add, sub_zero, zero_sub, c1e, c1f, c2e, c2f, t1e, t1f, …`.
-/
private theorem fromBlocks_transpose_dbl_map_eq_dbl {J : Matrix β β E} {ey fx : Matrix β ν E} {m1 m2 : Matrix ν β E}
    (h1e : m1 * ey = 1) (h1f : m1 * fx = 0) (h2e : m2 * ey = 0) (h2f : m2 * fx = 1)
    (hJ : J = m1ᵀ * m2.map c - m2ᵀ * m1.map c) :
    (fromBlocks 1 (-(fx * m2)) (-(fx * m1)) (fx * m1 - ey * m2) : Matrix (β ⊕ β) (β ⊕ β) E)ᵀ * dbl J *
      (fromBlocks 1 (-(fx * m2)) (-(fx * m1)) (fx * m1 - ey * m2) : Matrix (β ⊕ β) (β ⊕ β) E).map c = dbl J := by
  have mneg : ∀ {a b : Type} (A : Matrix a b E), (-A).map c = -(A.map c) := fun A => by ext; simp
  have msub : ∀ {a b : Type} (A B : Matrix a b E), (A - B).map c = A.map c - B.map c := fun A B => by ext; simp
  have c1e : m1.map c * ey.map c = 1 := by rw [← map_mul', h1e, map_one']
  have c1f : m1.map c * fx.map c = 0 := by rw [← map_mul', h1f]; ext; simp
  have c2e : m2.map c * ey.map c = 0 := by rw [← map_mul', h2e]; ext; simp
  have c2f : m2.map c * fx.map c = 1 := by rw [← map_mul', h2f, map_one']
  have t1e : eyᵀ * m1ᵀ = 1 := by rw [← Matrix.transpose_mul, h1e, Matrix.transpose_one]
  have t1f : fxᵀ * m1ᵀ = 0 := by rw [← Matrix.transpose_mul, h1f, Matrix.transpose_zero]
  have t2e : eyᵀ * m2ᵀ = 0 := by rw [← Matrix.transpose_mul, h2e, Matrix.transpose_zero]
  have t2f : fxᵀ * m2ᵀ = 1 := by rw [← Matrix.transpose_mul, h2f, Matrix.transpose_one]
  have c1e' : ∀ {k : Type} (Z : Matrix ν k E), m1.map c * (ey.map c * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, c1e, Matrix.one_mul]
  have c1f' : ∀ {k : Type} (Z : Matrix ν k E), m1.map c * (fx.map c * Z) = 0 := fun Z => by
    rw [← Matrix.mul_assoc, c1f, Matrix.zero_mul]
  have c2e' : ∀ {k : Type} (Z : Matrix ν k E), m2.map c * (ey.map c * Z) = 0 := fun Z => by
    rw [← Matrix.mul_assoc, c2e, Matrix.zero_mul]
  have c2f' : ∀ {k : Type} (Z : Matrix ν k E), m2.map c * (fx.map c * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, c2f, Matrix.one_mul]
  have t1e' : ∀ {k : Type} (Z : Matrix ν k E), eyᵀ * (m1ᵀ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, t1e, Matrix.one_mul]
  have t1f' : ∀ {k : Type} (Z : Matrix ν k E), fxᵀ * (m1ᵀ * Z) = 0 := fun Z => by
    rw [← Matrix.mul_assoc, t1f, Matrix.zero_mul]
  have t2e' : ∀ {k : Type} (Z : Matrix ν k E), eyᵀ * (m2ᵀ * Z) = 0 := fun Z => by
    rw [← Matrix.mul_assoc, t2e, Matrix.zero_mul]
  have t2f' : ∀ {k : Type} (Z : Matrix ν k E), fxᵀ * (m2ᵀ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, t2f, Matrix.one_mul]
  subst hJ
  simp only [Matrix.fromBlocks_map, map_one', mneg, msub, map_mul']
  simp only [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.transpose_one, Matrix.transpose_neg,
    Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_zero]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_assoc, neg_neg, neg_zero,
      add_zero, zero_add, sub_zero, zero_sub, c1e, c1f, c2e, c2f, t1e, t1f, t2e, t2f, c1e', c1f', c2e', c2f',
      t1e', t1f', t2e', t2f'] <;> abel

/- English proof (translation)
Simplify using `only [diagCols, Matrix.fromBlocks_mul_fromRows, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_neg, add_zero, zero_add]`. Use `congr 1`. Rewrite using `[← hsum]`. Normalize the expressions using the abelian group laws. Normalize the expressions using the abelian group laws.
-/
private theorem fromBlocks_mul_diagCols_eq {ey fx : Matrix β ν E} {m1 m2 : Matrix ν β E} (hsum : ey * m1 + fx * m2 = 1) :
    (fromBlocks 1 (-(fx * m2)) (-(fx * m1)) (fx * m1 - ey * m2) : Matrix (β ⊕ β) (β ⊕ β) E) *
      (diagCols β : Matrix (β ⊕ β) β E) = (fromBlocks ey 0 0 ey : Matrix (β ⊕ β) (ν ⊕ ν) E) * fromRows m1 (-m2) := by
  simp only [diagCols, Matrix.fromBlocks_mul_fromRows, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_neg, add_zero,
    zero_add]
  congr 1
  · rw [← hsum]; abel
  · abel

/- English proof (translation)
Take `⟨hy, Cx, M, hx, hPM, hMP⟩` from `hL`. Take `⟨m1, m2, rfl⟩ : ∃ m1 m2, M = fromRows m1 m2` from `⟨M.toRows₁, M.toRows₂, (Matrix.fromRows_toRows M).symm⟩`. Rewrite `hPM` using `[Matrix.fromCols_mul_fromRows]`. Rewrite `hMP` using `[Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]`. Take `⟨k1e, k1f, k2e, k2f⟩` from `hMP`.

Establish `madd : ∀ {a b : Type} (X Y : Matrix a b E), (X + Y).map c = X.map c + Y.map c` using `fun X Y => by ext; simp`. Establish `hcc : ∀ {a b : Type} (X : Matrix a b E), (X.map c).map c = X` using `fun X => by ext; simp [hc]`. Establish `herm : ∀ {m n : Type} (P : Matrix β m E) (Q : Matrix β n E), Qᵀ * J * P.map c = -((Pᵀ * J * Q.map c).map c)ᵀ`. Introduce `m n P Q`. Use extensionality with `i j`.

Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply, map_sum, map_mul, hc, hsk, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `hJinv : J * J⁻¹ = 1` using `Matrix.mul_nonsing_inv J hJ`. Establish `hPMc : Cy.map c * m1.map c + Cx.map c * m2.map c = 1`. Rewrite using `[← map_mul', ← map_mul', ← madd, hPM, map_one']`. Take `⟨A, hA⟩ : ∃ A : Matrix ν ν E, A = Cyᵀ * J * Cx.map c` from `⟨_, rfl⟩`. Take `⟨Ai, hAi⟩ : ∃ Ai : Matrix ν ν E, Ai = m2.map c * J⁻¹ * m1ᵀ` from `⟨_, rfl⟩`.

Establish `hAAi : A * Ai = 1`. Establish `e1 : Cx.map c * m2.map c = 1 - Cy.map c * m1.map c` using `by rw [← hPMc]; abel`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1]`. Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]`.

Use `_ = 1 := by`. Simplify using `only [hJinv, hy, Matrix.mul_one, Matrix.zero_mul, sub_zero]`. Rewrite using `[← Matrix.transpose_mul, k1e, Matrix.transpose_one]`. Establish `hAiA : Ai * A = 1` using `by first`. Consider the case `exact mul_eq_one_comm.mp hAAi`.

Consider the case `(rw [← Matrix.inv_eq_right_inv hAAi]; exact Matrix.nonsing_inv_mul A (Matrix.isUnit_det_of_right_inverse hAAi))`. Take `⟨f, hf⟩ : ∃ f : Matrix β ν E, f = Cx * Ai.map c` from `⟨_, rfl⟩`. Take `⟨n2, hn2⟩ : ∃ n2 : Matrix ν β E, n2 = A.map c * m2` from `⟨_, rfl⟩`. Establish `hf1 : m1 * f = 0` using `by rw [hf, ← Matrix.mul_assoc, k1f, Matrix.zero_mul]`. Establish `hn2e : n2 * Cy = 0` using `by rw [hn2, Matrix.mul_assoc, k2e, Matrix.mul_zero]`.

Establish `hn2f : n2 * f = 1`. Rewrite using `[hn2, hf, Matrix.mul_assoc, ← Matrix.mul_assoc m2, k2f, Matrix.one_mul, ← map_mul', hAAi, map_one']`. Establish `hsum : Cy * m1 + f * n2 = 1`. Establish `h' : f * n2 = Cx * m2`. Rewrite using `[hf, hn2, Matrix.mul_assoc, ← Matrix.mul_assoc (Ai.map c), ← map_mul', hAiA, map_one', Matrix.one_mul]`.

Rewrite using `[h']`. Conclude with `hPM`. Establish `hfc : f.map c = Cx.map c * Ai` using `by rw [hf, map_mul', hcc]`. Establish `hef : Cyᵀ * J * f.map c = 1` using `by rw [hfc, ← Matrix.mul_assoc, ← hA, hAAi]`. Establish `hfe : fᵀ * J * Cy.map c = -1` using `by rw [herm Cy f, hef, map_one', Matrix.transpose_one]`.

Establish `hff : fᵀ * J * f.map c = 0`. Rewrite using `[hfc, hf, Matrix.transpose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc J (Cx.map c) Ai, ← Matrix.mul_assoc Cxᵀ (J * Cx.map c) Ai, ← Matrix.mul_assoc Cxᵀ J (Cx.map c), hx, Matrix.zero_mul, Matrix.mul_zero]`. Establish `hJform : J = m1ᵀ * n2.map c - n2ᵀ * m1.map c`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hsum, Matrix.transpose_one, map_one', Matrix.one_mul, Matrix.mul_one]`. Use `_ = m1ᵀ * (Cyᵀ * J * Cy.map c) * m1.map c + m1ᵀ * (Cyᵀ * J * f.map c) * n2.map c + n2ᵀ * (fᵀ * J * Cy.map c) * m1.map c + n2ᵀ * (fᵀ * J * f.map c) * n2.map c := by`. Rewrite using `[madd, map_mul', map_mul']`. Simplify using `only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]`.

Normalize the expressions using the abelian group laws. Use `_ = m1ᵀ * n2.map c - n2ᵀ * m1.map c := by`. Rewrite using `[hy, hef, hfe, hff]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, zero_add, add_zero]`. Normalize the expressions using the abelian group laws.

Establish `hdetH : IsUnit (dbl J).det` using `by show IsUnit (Matrix.fromBlocks J 0 0 (-J)).det`. Rewrite using `[Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]`. Conclude with `hJ.mul ((isUnit_neg_one.pow _).mul hJ)`. Take `⟨u, hu⟩` from `exists_UG hdetH (fromBlocks_transpose_dbl_map_eq_dbl k1e hf1 hn2e hn2f hJform)`. Use `⟨u, fromRows m1 (-n2), fromCols Cy (-f), ?_, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [Matrix.fromRows_mul_fromCols, Matrix.mul_neg, Matrix.neg_mul, neg_neg, k1e, hf1, hn2e, hn2f, neg_zero, Matrix.fromBlocks_one]`. Simplify using `only [Matrix.fromCols_mul_fromRows, Matrix.neg_mul, Matrix.mul_neg, neg_neg]`. Conclude with `hsum`. Rewrite using `[hu]`. Conclude with `fromBlocks_mul_diagCols_eq hsum`.
-/
theorem exists_gamma (hc : ∀ z, c (c z) = z) {J : Matrix β β E} (hsk : ∀ i j, c (J j i) = -J i j) (hJ : IsUnit J.det)
    {Cy : Matrix β ν E} (hL : IsLagr c J Cy) :
    ∃ (γ : UG c (dbl J)) (s : Matrix (ν ⊕ ν) β E) (s' : Matrix β (ν ⊕ ν) E), s * s' = 1 ∧ s' * s = 1 ∧
      ((γ : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) * (diagCols β : Matrix (β ⊕ β) β E) =
        (fromBlocks Cy 0 0 Cy : Matrix (β ⊕ β) (ν ⊕ ν) E) * s := by
  obtain ⟨hy, Cx, M, hx, hPM, hMP⟩ := hL
  obtain ⟨m1, m2, rfl⟩ : ∃ m1 m2, M = fromRows m1 m2 := ⟨M.toRows₁, M.toRows₂, (Matrix.fromRows_toRows M).symm⟩
  rw [Matrix.fromCols_mul_fromRows] at hPM
  rw [Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at hMP
  obtain ⟨k1e, k1f, k2e, k2f⟩ := hMP
  have madd : ∀ {a b : Type} (X Y : Matrix a b E), (X + Y).map c = X.map c + Y.map c := fun X Y => by ext; simp
  have hcc : ∀ {a b : Type} (X : Matrix a b E), (X.map c).map c = X := fun X => by ext; simp [hc]
  have herm : ∀ {m n : Type} (P : Matrix β m E) (Q : Matrix β n E),
      Qᵀ * J * P.map c = -((Pᵀ * J * Q.map c).map c)ᵀ := by
    intro m n P Q
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply, map_sum, map_mul, hc,
      hsk, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hJinv : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJ
  have hPMc : Cy.map c * m1.map c + Cx.map c * m2.map c = 1 := by
    rw [← map_mul', ← map_mul', ← madd, hPM, map_one']
  obtain ⟨A, hA⟩ : ∃ A : Matrix ν ν E, A = Cyᵀ * J * Cx.map c := ⟨_, rfl⟩
  obtain ⟨Ai, hAi⟩ : ∃ Ai : Matrix ν ν E, Ai = m2.map c * J⁻¹ * m1ᵀ := ⟨_, rfl⟩
  have hAAi : A * Ai = 1 := by
    have e1 : Cx.map c * m2.map c = 1 - Cy.map c * m1.map c := by rw [← hPMc]; abel
    calc A * Ai = Cyᵀ * J * (Cx.map c * m2.map c) * J⁻¹ * m1ᵀ := by rw [hA, hAi]; simp only [Matrix.mul_assoc]
      _ = Cyᵀ * (J * J⁻¹) * m1ᵀ - Cyᵀ * J * Cy.map c * m1.map c * J⁻¹ * m1ᵀ := by
          rw [e1]; simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by
          simp only [hJinv, hy, Matrix.mul_one, Matrix.zero_mul, sub_zero]
          rw [← Matrix.transpose_mul, k1e, Matrix.transpose_one]
  have hAiA : Ai * A = 1 := by
    first
    | exact mul_eq_one_comm.mp hAAi
    | (rw [← Matrix.inv_eq_right_inv hAAi]; exact Matrix.nonsing_inv_mul A (Matrix.isUnit_det_of_right_inverse hAAi))
  obtain ⟨f, hf⟩ : ∃ f : Matrix β ν E, f = Cx * Ai.map c := ⟨_, rfl⟩
  obtain ⟨n2, hn2⟩ : ∃ n2 : Matrix ν β E, n2 = A.map c * m2 := ⟨_, rfl⟩
  have hf1 : m1 * f = 0 := by rw [hf, ← Matrix.mul_assoc, k1f, Matrix.zero_mul]
  have hn2e : n2 * Cy = 0 := by rw [hn2, Matrix.mul_assoc, k2e, Matrix.mul_zero]
  have hn2f : n2 * f = 1 := by
    rw [hn2, hf, Matrix.mul_assoc, ← Matrix.mul_assoc m2, k2f, Matrix.one_mul, ← map_mul', hAAi, map_one']
  have hsum : Cy * m1 + f * n2 = 1 := by
    have h' : f * n2 = Cx * m2 := by
      rw [hf, hn2, Matrix.mul_assoc, ← Matrix.mul_assoc (Ai.map c), ← map_mul', hAiA, map_one', Matrix.one_mul]
    rw [h']; exact hPM
  have hfc : f.map c = Cx.map c * Ai := by rw [hf, map_mul', hcc]
  have hef : Cyᵀ * J * f.map c = 1 := by rw [hfc, ← Matrix.mul_assoc, ← hA, hAAi]
  have hfe : fᵀ * J * Cy.map c = -1 := by rw [herm Cy f, hef, map_one', Matrix.transpose_one]
  have hff : fᵀ * J * f.map c = 0 := by
    rw [hfc, hf, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc J (Cx.map c) Ai, ← Matrix.mul_assoc Cxᵀ (J * Cx.map c) Ai,
      ← Matrix.mul_assoc Cxᵀ J (Cx.map c), hx, Matrix.zero_mul, Matrix.mul_zero]
  have hJform : J = m1ᵀ * n2.map c - n2ᵀ * m1.map c := by
    calc J = (Cy * m1 + f * n2)ᵀ * J * (Cy * m1 + f * n2).map c := by
          rw [hsum, Matrix.transpose_one, map_one', Matrix.one_mul, Matrix.mul_one]
      _ = m1ᵀ * (Cyᵀ * J * Cy.map c) * m1.map c + m1ᵀ * (Cyᵀ * J * f.map c) * n2.map c +
            n2ᵀ * (fᵀ * J * Cy.map c) * m1.map c + n2ᵀ * (fᵀ * J * f.map c) * n2.map c := by
          rw [madd, map_mul', map_mul']
          simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
          abel
      _ = m1ᵀ * n2.map c - n2ᵀ * m1.map c := by
          rw [hy, hef, hfe, hff]
          simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, zero_add,
            add_zero]
          abel
  have hdetH : IsUnit (dbl J).det := by
    show IsUnit (Matrix.fromBlocks J 0 0 (-J)).det
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    exact hJ.mul ((isUnit_neg_one.pow _).mul hJ)
  obtain ⟨u, hu⟩ := exists_UG hdetH (fromBlocks_transpose_dbl_map_eq_dbl k1e hf1 hn2e hn2f hJform)
  refine ⟨u, fromRows m1 (-n2), fromCols Cy (-f), ?_, ?_, ?_⟩
  · simp only [Matrix.fromRows_mul_fromCols, Matrix.mul_neg, Matrix.neg_mul, neg_neg, k1e, hf1, hn2e, hn2f,
      neg_zero, Matrix.fromBlocks_one]
  · simp only [Matrix.fromCols_mul_fromRows, Matrix.neg_mul, Matrix.mul_neg, neg_neg]; exact hsum
  · rw [hu]; exact fromBlocks_mul_diagCols_eq hsum

end PositivityTheory.ThK.SiegelT
