import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealTangentSpace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DiscriminantTraceBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermEqZeroOfTraceFormVanish

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace DiscreteLatticeMinimum

open NumberField Complex Module RealTangentSpace
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Y : DataX E r}
  (z : Frame Y.Ψ r) (ξ : Fin r → E) [hz : Fact (z ∈ Y.dom)]

noncomputable def Bmap : VT (X := Y.toData) z ξ →ₗ[ℝ] VT (X := Y.toData) z ξ where
  toFun u := VT.mk (MajorantOperators.Bop z u.val) (MajorantOperators.Bop_mem hz.out u.val_mem)
  map_add' u v := VT.ext (by simp [MajorantOperators.Bop_add])
  map_smul' c u := VT.ext (by simp [MajorantOperators.Bop_smul])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Bmap_val (u : VT (X := Y.toData) z ξ) : (Bmap z ξ u).val = MajorantOperators.Bop z u.val := rfl

/- English proof (translation)
Apply `VT.ext` to reduce the goal to its premises. Rewrite using `[Bmap_val, Bmap_val, MajorantOperators.Bop_Bop hz.out]`. Both sides reduce to the same expression.
-/
theorem Bmap_Bmap (u : VT (X := Y.toData) z ξ) : Bmap z ξ (Bmap z ξ u) = (-(Y.k0 ^ 2)) • u := by
  apply VT.ext
  rw [Bmap_val, Bmap_val, MajorantOperators.Bop_Bop hz.out]
  rfl

/- English proof (translation)
Rewrite using `[inner_eq, inner_eq, Bmap_val, Bmap_val, MajorantOperators.gI_Bop_right hz.out]`.
-/
theorem inner_Bmap_right (u v : VT (X := Y.toData) z ξ) :
    inner ℝ u (Bmap z ξ v) = -inner ℝ (Bmap z ξ u) v := by
  rw [inner_eq, inner_eq, Bmap_val, Bmap_val, MajorantOperators.gI_Bop_right hz.out]

/- English proof (translation)
Establish `h : ‖Bmap z ξ u‖ ^ 2 = (Y.k0 * ‖u‖) ^ 2`. Rewrite using `[← real_inner_self_eq_norm_sq, mul_pow, ← real_inner_self_eq_norm_sq, inner_eq, inner_eq, Bmap_val, MajorantOperators.gI_Bop_self hz.out]`. Conclude with `(pow_left_inj₀ (norm_nonneg _) (mul_nonneg Y.minWeight_pos.le (norm_nonneg _)) two_ne_zero).1 h`.
-/
theorem norm_Bmap (u : VT (X := Y.toData) z ξ) : ‖Bmap z ξ u‖ = Y.k0 * ‖u‖ := by
  have h : ‖Bmap z ξ u‖ ^ 2 = (Y.k0 * ‖u‖) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, mul_pow, ← real_inner_self_eq_norm_sq, inner_eq, inner_eq,
      Bmap_val, MajorantOperators.gI_Bop_self hz.out]
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg Y.minWeight_pos.le (norm_nonneg _))
    two_ne_zero).1 h

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `u hu`. Establish `h` using `norm_Bmap z ξ u`. Rewrite `h` using `[hu, norm_zero]`. Establish `h2 : ‖u‖ = 0`.

Break down `mul_eq_zero.1 h.symm with h3 | h3` into its components or cases. Conclude with `absurd h3 Y.minWeight_pos.ne'`. Conclude with `h3`. Conclude with `norm_eq_zero.1 h2`.
-/
theorem Bmap_injective : Function.Injective (Bmap z ξ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  have h := norm_Bmap z ξ u
  rw [hu, norm_zero] at h
  have h2 : ‖u‖ = 0 := by
    rcases mul_eq_zero.1 h.symm with h3 | h3
    · exact absurd h3 Y.minWeight_pos.ne'
    · exact h3
  exact norm_eq_zero.1 h2

noncomputable def Bequiv : VT (X := Y.toData) z ξ ≃ₗ[ℝ] VT (X := Y.toData) z ξ :=
  LinearEquiv.ofBijective (Bmap z ξ) ⟨Bmap_injective z ξ,
    LinearMap.surjective_of_injective (Bmap_injective z ξ)⟩

variable {ξ} (hξ : Y.IsIso ξ)

/- English proof (translation)
Establish `hval : ∀ ν : Y.Λp ξ, inner ℝ y (Bmap z ξ (phi z ξ hξ ν)) = (round (inner ℝ y (Bmap z ξ (phi z ξ hξ ν))) : ℝ)`. Introduce `ν`. Take `⟨m, hm⟩` from `hy _ ((mem_Lat z ξ hξ).mpr ⟨ν, rfl⟩)`. Rewrite using `[hm, round_intCast]`. Set `ψ : Y.Λp ξ →+ ℤ` to `AddMonoidHom.mk' (fun ν => round (inner ℝ y (Bmap z ξ (phi z ξ hξ ν)))) (fun ν ν' => by`.

Take `⟨m1, hm1⟩` from `hy _ ((mem_Lat z ξ hξ).mpr ⟨ν, rfl⟩)`. Take `⟨m2, hm2⟩` from `hy _ ((mem_Lat z ξ hξ).mpr ⟨ν', rfl⟩)`. Use `show round _ = round _ + round _`. Rewrite using `[map_add, map_add, inner_add_right, hm1, hm2, ← Int.cast_add, round_intCast, round_intCast, round_intCast])`. Establish `hψ : ∀ ν, (ψ ν : ℝ) = inner ℝ y (Bmap z ξ (phi z ξ hξ ν))` using `fun ν => (hval ν).symm`.

Establish `hvan : ∀ ν : Y.Λp ξ, (∃ e : E, (ν : Fin r → E) = e • ξ) → ψ ν = 0`. Introduce and unpack `ν ⟨e, he⟩`. Establish `h0 : phi z ξ hξ ν = 0` using `VT.ext (by rw [phi_val, he, ucomp_line z ξ hξ e]; rfl)`. Use `hψ ν` as an intermediate fact. Rewrite `this` using `[h0, map_zero, inner_zero_right]`.

Conclude with `this` after adjusting the coercions. Take `⟨μ, hμ⟩` from `(hermitian_dual_lattice_identity r Y ξ hξ).1 ψ hvan`. Establish `hEF : ∀ ν : Y.Λp ξ, inner ℝ (Bmap z ξ y + Bmap z ξ (phi z ξ hξ μ)) (phi z ξ hξ ν) = 0`. Introduce `ν`. Establish `h1` using `hμ ν`.

Establish `h2 : ((EFf Y.ξ0 Y.Gm μ ν : ℚ) : ℝ) = inner ℝ (Bmap z ξ (phi z ξ hξ μ)) (phi z ξ hξ ν)`. Rewrite using `[inner_eq, Bmap_val, phi_val, phi_val]`. Conclude with `MajorantOperators.EF_eq hz.out hξ.2.1 (LatticeSpanMembership.mem_Λp_iff.mp μ.2).2 (LatticeSpanMembership.mem_Λp_iff.mp ν.2).2`. Establish `h3 : (ψ ν : ℝ) = ((EFf Y.ξ0 Y.Gm μ ν : ℚ) : ℝ)` using `by exact_mod_cast h1`. Rewrite `h3` using `[hψ, inner_Bmap_right, h2]`.

Rewrite using `[inner_add_left]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set w := Bmap z ξ y + Bmap z ξ (phi z ξ hξ μ) with hw`. Establish `hwall : ∀ a ∈ Submodule.span ℝ (Lat z ξ hξ : Set (VT (X` using `Y.toData) z ξ)), inner ℝ w a = 0 := by`. Introduce `a ha`.

Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem a ha`. Take `⟨ν, rfl⟩` from `(mem_Lat z ξ hξ).mp ha`. Conclude with `hEF ν`. Consider the case `zero => exact inner_zero_right _`.

Consider the case `add a b _ _ iha ihb => rw [inner_add_right, iha, ihb, add_zero]`. Consider the case `smul c a _ iha => rw [inner_smul_right, iha, mul_zero]`. Establish `hw0 : w = 0`. Use `hwall w (by rw [span_Lat z ξ hD3 hξ]; exact Submodule.mem_top)` as an intermediate fact. Conclude with `inner_self_eq_zero.mp this`.

Establish `hy0 : y + phi z ξ hξ μ = 0`. Apply `Bmap_injective z ξ` to reduce the goal to its premises. Rewrite using `[map_add, ← hw, hw0, map_zero]`. Establish `: y = phi z ξ hξ (-μ)`. Rewrite using `[map_neg]`.

Conclude with `eq_neg_of_add_eq_zero_left hy0`. Rewrite using `[this]`. Conclude with `(mem_Lat z ξ hξ).mpr ⟨-μ, rfl⟩`.
-/
theorem mem_Lat_of_int (hD3 : IntegerApproximationCount (E := E)) (y : VT (X := Y.toData) z ξ)
    (hy : ∀ a ∈ Lat z ξ hξ, ∃ m : ℤ, inner ℝ y (Bmap z ξ a) = m) : y ∈ Lat z ξ hξ := by
  classical
  have hval : ∀ ν : Y.Λp ξ, inner ℝ y (Bmap z ξ (phi z ξ hξ ν)) =
      (round (inner ℝ y (Bmap z ξ (phi z ξ hξ ν))) : ℝ) := by
    intro ν
    obtain ⟨m, hm⟩ := hy _ ((mem_Lat z ξ hξ).mpr ⟨ν, rfl⟩)
    rw [hm, round_intCast]
  let ψ : Y.Λp ξ →+ ℤ := AddMonoidHom.mk' (fun ν => round (inner ℝ y (Bmap z ξ (phi z ξ hξ ν))))
    (fun ν ν' => by
      obtain ⟨m1, hm1⟩ := hy _ ((mem_Lat z ξ hξ).mpr ⟨ν, rfl⟩)
      obtain ⟨m2, hm2⟩ := hy _ ((mem_Lat z ξ hξ).mpr ⟨ν', rfl⟩)
      show round _ = round _ + round _
      rw [map_add, map_add, inner_add_right, hm1, hm2, ← Int.cast_add, round_intCast, round_intCast,
        round_intCast])
  have hψ : ∀ ν, (ψ ν : ℝ) = inner ℝ y (Bmap z ξ (phi z ξ hξ ν)) := fun ν => (hval ν).symm
  have hvan : ∀ ν : Y.Λp ξ, (∃ e : E, (ν : Fin r → E) = e • ξ) → ψ ν = 0 := by
    rintro ν ⟨e, he⟩
    have h0 : phi z ξ hξ ν = 0 := VT.ext (by rw [phi_val, he, ucomp_line z ξ hξ e]; rfl)
    have := hψ ν
    rw [h0, map_zero, inner_zero_right] at this
    exact_mod_cast this
  obtain ⟨μ, hμ⟩ := (hermitian_dual_lattice_identity r Y ξ hξ).1 ψ hvan
  have hEF : ∀ ν : Y.Λp ξ,
      inner ℝ (Bmap z ξ y + Bmap z ξ (phi z ξ hξ μ)) (phi z ξ hξ ν) = 0 := by
    intro ν
    have h1 := hμ ν
    have h2 : ((EFf Y.ξ0 Y.Gm μ ν : ℚ) : ℝ) =
        inner ℝ (Bmap z ξ (phi z ξ hξ μ)) (phi z ξ hξ ν) := by
      rw [inner_eq, Bmap_val, phi_val, phi_val]
      exact MajorantOperators.EF_eq hz.out hξ.2.1 (LatticeSpanMembership.mem_Λp_iff.mp μ.2).2
        (LatticeSpanMembership.mem_Λp_iff.mp ν.2).2
    have h3 : (ψ ν : ℝ) = ((EFf Y.ξ0 Y.Gm μ ν : ℚ) : ℝ) := by exact_mod_cast h1
    rw [hψ, inner_Bmap_right, h2] at h3
    rw [inner_add_left]
    linarith
  set w := Bmap z ξ y + Bmap z ξ (phi z ξ hξ μ) with hw
  have hwall : ∀ a ∈ Submodule.span ℝ (Lat z ξ hξ : Set (VT (X := Y.toData) z ξ)),
      inner ℝ w a = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨ν, rfl⟩ := (mem_Lat z ξ hξ).mp ha
      exact hEF ν
    | zero => exact inner_zero_right _
    | add a b _ _ iha ihb => rw [inner_add_right, iha, ihb, add_zero]
    | smul c a _ iha => rw [inner_smul_right, iha, mul_zero]
  have hw0 : w = 0 := by
    have := hwall w (by rw [span_Lat z ξ hD3 hξ]; exact Submodule.mem_top)
    exact inner_self_eq_zero.mp this
  have hy0 : y + phi z ξ hξ μ = 0 := by
    apply Bmap_injective z ξ
    rw [map_add, ← hw, hw0, map_zero]
  have : y = phi z ξ hξ (-μ) := by
    rw [map_neg]
    exact eq_neg_of_add_eq_zero_left hy0
  rw [this]
  exact (mem_Lat z ξ hξ).mpr ⟨-μ, rfl⟩

section lattice

variable (ep0 : ℝ) (hns : ∀ x ∈ Y.L', herm Y.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) →
      ∃ τ : Y.Ψ, ep0 ≤ Y.maj z τ (Y.ucomp z ξ (Y.embV x) τ))

include hns in
/- English proof (translation)
Take `⟨μ, rfl⟩` from `(mem_Lat z ξ hξ).mp ha`. Establish `hμ` using `LatticeSpanMembership.mem_Λp_iff.mp μ.2`. Establish `hNA : (Y.NA : E) ≠ 0` using `by exact_mod_cast Y.NA_pos.ne'`. Establish `hNAr : (0 : ℝ) < Y.NA` using `by exact_mod_cast Y.NA_pos`. Take `⟨τ, hτ⟩` from `hns ((Y.NA : E) • (μ : Fin r → E)) (Y.NA_sub _ hμ.1) (by rw [HermitianTraceFormVanishing.herm_smul_left, hμ.2, mul_zero]) (by`.

Introduce `e he`. Apply `ha0` to reduce the goal to its premises. Establish `hμe : (μ : Fin r → E) = ((Y.NA : E)⁻¹ * e) • ξ`. Rewrite using `[mul_smul, ← he, smul_smul, inv_mul_cancel₀ hNA, one_smul]`. Conclude with `VT.ext (by rw [phi_val, hμe, ucomp_line z ξ hξ]; rfl))`.

Establish `hemb : Y.embV ((Y.NA : E) • (μ : Fin r → E)) = (Y.NA : ℝ) • Y.embV μ`. Use function extensionality and compare the values at `τ' b`. Simplify using `[Data.embV, Data.emb]`. Rewrite `hτ` using `[hemb, ucomp_smul, Pi.smul_apply, ← Complex.coe_smul, UnipotentCoefficientShift.maj_smul hz.out]`. Establish `h2` using `maj_le_norm_sq z ξ (phi z ξ hξ μ) τ`.

Rewrite `h2` using `[phi_val]`. Establish `h3 : ep0 ≤ (Y.NA * ‖phi z ξ hξ μ‖) ^ 2`. Rewrite using `[mul_pow]`. Conclude with `le_trans hτ (mul_le_mul_of_nonneg_left h2 (by positivity))`. Establish `h4` using `Real.sqrt_le_sqrt h3`.

Rewrite `h4` using `[Real.sqrt_sq (by positivity)]`. Rewrite using `[div_le_iff₀ hNAr]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem min_norm (a : VT (X := Y.toData) z ξ) (ha : a ∈ Lat z ξ hξ) (ha0 : a ≠ 0) :
    Real.sqrt ep0 / Y.NA ≤ ‖a‖ := by
  obtain ⟨μ, rfl⟩ := (mem_Lat z ξ hξ).mp ha
  have hμ := LatticeSpanMembership.mem_Λp_iff.mp μ.2
  have hNA : (Y.NA : E) ≠ 0 := by exact_mod_cast Y.NA_pos.ne'
  have hNAr : (0 : ℝ) < Y.NA := by exact_mod_cast Y.NA_pos
  obtain ⟨τ, hτ⟩ := hns ((Y.NA : E) • (μ : Fin r → E)) (Y.NA_sub _ hμ.1)
    (by rw [HermitianTraceFormVanishing.herm_smul_left, hμ.2, mul_zero])
    (by
      intro e he
      apply ha0
      have hμe : (μ : Fin r → E) = ((Y.NA : E)⁻¹ * e) • ξ := by
        rw [mul_smul, ← he, smul_smul, inv_mul_cancel₀ hNA, one_smul]
      exact VT.ext (by rw [phi_val, hμe, ucomp_line z ξ hξ]; rfl))
  have hemb : Y.embV ((Y.NA : E) • (μ : Fin r → E)) = (Y.NA : ℝ) • Y.embV μ := by
    funext τ' b
    simp [Data.embV, Data.emb]
  rw [hemb, ucomp_smul, Pi.smul_apply, ← Complex.coe_smul, UnipotentCoefficientShift.maj_smul hz.out] at hτ
  have h2 := maj_le_norm_sq z ξ (phi z ξ hξ μ) τ
  rw [phi_val] at h2
  have h3 : ep0 ≤ (Y.NA * ‖phi z ξ hξ μ‖) ^ 2 := by
    rw [mul_pow]
    exact le_trans hτ (mul_le_mul_of_nonneg_left h2 (by positivity))
  have h4 := Real.sqrt_le_sqrt h3
  rw [Real.sqrt_sq (by positivity)] at h4
  rw [div_le_iff₀ hNAr]
  linarith

include hns in
/- English proof (translation)
Apply `discreteTopology_of_isOpen_singleton_zero` to reduce the goal to its premises. Establish `hε : 0 < Real.sqrt ep0 / Y.NA` using `div_pos (Real.sqrt_pos.mpr hep) (by exact_mod_cast Y.NA_pos)`. Establish `hset : ({0} : Set (Lat z ξ hξ)) = Subtype.val ⁻¹' Metric.ball (0 : VT (X` using `Y.toData) z ξ) (Real.sqrt ep0 / Y.NA) := by`. Use extensionality with `x`. Simplify using `only [Set.mem_singleton_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Simplify using `using hε`. Introduce `hx`. Assume the negation of the conclusion as `hne`.

Use `min_norm z hξ ep0 hns x.1 x.2 (fun h => hne (Subtype.ext h))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hset]`. Conclude with `Metric.isOpen_ball.preimage continuous_subtype_val`.
-/
theorem discrete_Lat (hep : 0 < ep0) : DiscreteTopology (Lat z ξ hξ) := by
  apply discreteTopology_of_isOpen_singleton_zero
  have hε : 0 < Real.sqrt ep0 / Y.NA :=
    div_pos (Real.sqrt_pos.mpr hep) (by exact_mod_cast Y.NA_pos)
  have hset : ({0} : Set (Lat z ξ hξ)) =
      Subtype.val ⁻¹' Metric.ball (0 : VT (X := Y.toData) z ξ) (Real.sqrt ep0 / Y.NA) := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro rfl
      simpa using hε
    · intro hx
      by_contra hne
      have := min_norm z hξ ep0 hns x.1 x.2 (fun h => hne (Subtype.ext h))
      linarith
  rw [hset]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

include hns in
/- English proof (translation)
Use `discrete_Lat z hξ ep0 hns hep` as an intermediate fact. Establish `: IsZLattice ℝ (Lat z ξ hξ)` using `⟨span_Lat z ξ hD3 hξ⟩`. Use `ZLattice.module_free ℝ (Lat z ξ hξ)` as an intermediate fact. Use `ZLattice.module_finite ℝ (Lat z ξ hξ)` as an intermediate fact. Use `set n := finrank ℝ (VT (X := Y.toData) z ξ) with hn`.

Set `bZ` to `Module.Free.chooseBasis ℤ (Lat z ξ hξ)`. Set `bR` to `bZ.ofZLatticeBasis ℝ (Lat z ξ hξ)`. Establish `hspanR : Submodule.span ℤ (Set.range bR) = Lat z ξ hξ` using `bZ.ofZLatticeBasis_span ℝ _`. Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (Lat z ξ hξ)) = n` using `(Module.finrank_eq_card_basis bR).symm`. Set `bF` to `bR.reindex (Fintype.equivFinOfCardEq hcard)`.

Establish `hspanF : Submodule.span ℤ (Set.range bF) = Lat z ξ hξ`. Rewrite using `[Basis.range_reindex]`. Conclude with `hspanR`. Set `e` to `(stdOrthonormalBasis ℝ (VT (X := Y.toData) z ξ)).repr`. Set `b'` to `(bF.map (Bequiv z ξ)).map e.toLinearEquiv`.

Establish `hb'j : ∀ j, b' j = e (Bmap z ξ (bF j))` using `fun j => by`. Simplify using `only [b', Basis.map_apply]`. Both sides reduce to the same expression. Use `set lam := Y.k0 * Real.sqrt ep0 / Y.NA with hlam`. Establish `hlam0 : 0 < lam`.

Establish `h1` using `Y.minWeight_pos`. Establish `h2 : (0 : ℝ) < Y.NA` using `by exact_mod_cast Y.NA_pos`. Establish `h3` using `Real.sqrt_pos.mpr hep`. Check the signs of the components of the expression. Set `f : VT (X` to `Y.toData) z ξ →ₗ[ℤ] EuclideanSpace ℝ (Fin n) := ((e.toLinearEquiv.toLinearMap).comp (Bmap z ξ)).restrictScalars ℤ`.

Establish `hfr : f '' Set.range bF = Set.range b'`. Rewrite using `[← Set.range_comp]`. Conclude with `congrArg Set.range (funext fun j => (hb'j j).symm)`. Establish `hmin : ∀ x ∈ Submodule.span ℤ (Set.range b'), x ≠ 0 → lam ≤ ‖x‖`. Introduce `x hx hx0`.

Rewrite `hx` using `[← hfr, Submodule.span_image, hspanF]`. Take `⟨a, ha, rfl⟩` from `hx`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `hx0 (map_zero f)`.

Establish `hfa : ‖f a‖ = Y.k0 * ‖a‖` using `by show ‖e (Bmap z ξ a)‖ = _`. Rewrite using `[LinearIsometryEquiv.norm_map, norm_Bmap]`. Rewrite using `[hfa, hlam, mul_div_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (min_norm z hξ ep0 hns a ha ha0) Y.minWeight_pos.le`. Take `⟨y, hli, hint, hnorm⟩` from `T0.transference_dual b' lam hlam0 hmin`.

Use `⟨fun i => e.symm (y i), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hli.map' e.symm.toLinearEquiv.toLinearMap e.symm.toLinearEquiv.ker`. Introduce `i`. Apply `mem_Lat_of_int z hξ hD3` to reduce the goal to its premises. Introduce `a ha`.

Rewrite `ha` using `[← hspanF]`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem a ha`. Take `⟨j, rfl⟩` from `ha`. Take `⟨m, hm⟩` from `hint i j`.

Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[← hm, hb'j, ← LinearIsometryEquiv.inner_map_map e, LinearIsometryEquiv.apply_symm_apply]`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add a b _ _ iha ihb`. Take `⟨m1, h1⟩` from `iha`.

Take `⟨m2, h2⟩` from `ihb`. Conclude with `⟨m1 + m2, by rw [map_add, inner_add_right, h1, h2, Int.cast_add]⟩`. Consider the case `smul c a _ iha`. Take `⟨m, h⟩` from `iha`. Use `⟨c * m, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, h, Int.cast_mul]`. Introduce `i`. Rewrite using `[LinearIsometryEquiv.norm_map]`. Conclude with `hnorm i`.
-/
theorem short_basis (hD3 : IntegerApproximationCount (E := E)) (hep : 0 < ep0) :
    ∃ y : Fin (finrank ℝ (VT (X := Y.toData) z ξ)) → VT (X := Y.toData) z ξ,
      LinearIndependent ℝ y ∧ (∀ i, y i ∈ Lat z ξ hξ) ∧
      ∀ i, ‖y i‖ ≤ (finrank ℝ (VT (X := Y.toData) z ξ) : ℝ) ^ 2 /
        (Y.k0 * Real.sqrt ep0 / Y.NA) := by
  classical
  have := discrete_Lat z hξ ep0 hns hep
  have : IsZLattice ℝ (Lat z ξ hξ) := ⟨span_Lat z ξ hD3 hξ⟩
  have := ZLattice.module_free ℝ (Lat z ξ hξ)
  have := ZLattice.module_finite ℝ (Lat z ξ hξ)
  set n := finrank ℝ (VT (X := Y.toData) z ξ) with hn
  let bZ := Module.Free.chooseBasis ℤ (Lat z ξ hξ)
  let bR := bZ.ofZLatticeBasis ℝ (Lat z ξ hξ)
  have hspanR : Submodule.span ℤ (Set.range bR) = Lat z ξ hξ := bZ.ofZLatticeBasis_span ℝ _
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (Lat z ξ hξ)) = n :=
    (Module.finrank_eq_card_basis bR).symm
  let bF := bR.reindex (Fintype.equivFinOfCardEq hcard)
  have hspanF : Submodule.span ℤ (Set.range bF) = Lat z ξ hξ := by
    rw [Basis.range_reindex]
    exact hspanR
  let e := (stdOrthonormalBasis ℝ (VT (X := Y.toData) z ξ)).repr
  let b' := (bF.map (Bequiv z ξ)).map e.toLinearEquiv
  have hb'j : ∀ j, b' j = e (Bmap z ξ (bF j)) := fun j => by
    simp only [b', Basis.map_apply]
    rfl
  set lam := Y.k0 * Real.sqrt ep0 / Y.NA with hlam
  have hlam0 : 0 < lam := by
    have h1 := Y.minWeight_pos
    have h2 : (0 : ℝ) < Y.NA := by exact_mod_cast Y.NA_pos
    have h3 := Real.sqrt_pos.mpr hep
    positivity
  let f : VT (X := Y.toData) z ξ →ₗ[ℤ] EuclideanSpace ℝ (Fin n) :=
    ((e.toLinearEquiv.toLinearMap).comp (Bmap z ξ)).restrictScalars ℤ
  have hfr : f '' Set.range bF = Set.range b' := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun j => (hb'j j).symm)
  have hmin : ∀ x ∈ Submodule.span ℤ (Set.range b'), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    rw [← hfr, Submodule.span_image, hspanF] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hx0 (map_zero f)
    have hfa : ‖f a‖ = Y.k0 * ‖a‖ := by
      show ‖e (Bmap z ξ a)‖ = _
      rw [LinearIsometryEquiv.norm_map, norm_Bmap]
    rw [hfa, hlam, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (min_norm z hξ ep0 hns a ha ha0) Y.minWeight_pos.le
  obtain ⟨y, hli, hint, hnorm⟩ := T0.transference_dual b' lam hlam0 hmin
  refine ⟨fun i => e.symm (y i), ?_, ?_, ?_⟩
  · exact hli.map' e.symm.toLinearEquiv.toLinearMap e.symm.toLinearEquiv.ker
  · intro i
    apply mem_Lat_of_int z hξ hD3
    intro a ha
    rw [← hspanF] at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      obtain ⟨m, hm⟩ := hint i j
      refine ⟨m, ?_⟩
      rw [← hm, hb'j, ← LinearIsometryEquiv.inner_map_map e, LinearIsometryEquiv.apply_symm_apply]
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ iha ihb =>
      obtain ⟨m1, h1⟩ := iha
      obtain ⟨m2, h2⟩ := ihb
      exact ⟨m1 + m2, by rw [map_add, inner_add_right, h1, h2, Int.cast_add]⟩
    | smul c a _ iha =>
      obtain ⟨m, h⟩ := iha
      refine ⟨c * m, ?_⟩
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, h, Int.cast_mul]
  · intro i
    rw [LinearIsometryEquiv.norm_map]
    exact hnorm i

include hns in

/- English proof (translation)
Break down `Nat.eq_zero_or_pos (finrank ℝ (VT (X := Y.toData) z ξ)) with h0 | hpos` into its components or cases. Establish `hsub : Subsingleton (VT (X` using `Y.toData) z ξ) := Module.finrank_zero_iff.mp h0`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[Subsingleton.elim (d - phi z ξ hξ 0) 0, norm_zero, h0]`. Simplify using the standard rewrite rules.

Establish `: Nonempty (Fin (finrank ℝ (VT (X` using `Y.toData) z ξ))) := ⟨⟨0, hpos⟩⟩`. Take `⟨y, hli, hyL, hyn⟩` from `short_basis z hξ ep0 hns hD3 hep`. Set `yb` to `Basis.mk hli (hli.span_eq_top_of_card_eq_finrank (by simp)).ge`. Establish `hyb : ∀ i, yb i = y i` using `fun i => Basis.mk_apply _ _ _`. Use `set c := yb.repr d with hc`.

Use `set p : VT (X := Y.toData) z ξ := ∑ i, (round (c i) : ℤ) • y i with hp`. Establish `hpL : p ∈ Lat z ξ hξ` using `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hyL i)`. Take `⟨μ, hμ⟩` from `(mem_Lat z ξ hξ).mp hpL`. Use `⟨μ, ?_⟩` and prove the remaining obligations. Rewrite using `[hμ]`.

Establish `hd : d = ∑ i, c i • y i` using `by conv_lhs => rw [← yb.sum_repr d]`. Simplify using `only [hyb, hc]`. Establish `hdiff : d - p = ∑ i, (c i - round (c i)) • y i`. Rewrite using `[hd, hp, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[sub_smul, ← Int.cast_smul_eq_zsmul ℝ]`. Rewrite using `[hdiff]`. Establish `hlam0 : 0 < Y.k0 * Real.sqrt ep0 / Y.NA`. Establish `h1` using `Y.minWeight_pos`. Establish `h2 : (0 : ℝ) < Y.NA` using `by exact_mod_cast Y.NA_pos`.

Establish `h3` using `Real.sqrt_pos.mpr hep`. Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_smul, Real.norm_eq_abs]`.

Conclude with `mul_le_mul (abs_sub_round _) (hyn i) (norm_nonneg _) (by norm_num)`. Use `_ = (finrank ℝ (VT (X := Y.toData) z ξ) : ℝ) ^ 3 * Y.NA / (2 * Y.k0 * Real.sqrt ep0) := by`. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Establish `h1` using `Y.minWeight_pos.ne'`. Establish `h2 : (Y.NA : ℝ) ≠ 0` using `by exact_mod_cast Y.NA_pos.ne'`.

Establish `h3` using `(Real.sqrt_pos.mpr hep).ne'`. Clear the denominators using the available nonvanishing facts.
-/
theorem covering (hD3 : IntegerApproximationCount (E := E)) (hep : 0 < ep0) (d : VT (X := Y.toData) z ξ) :
    ∃ μ : Y.Λp ξ, ‖d - phi z ξ hξ μ‖ ≤ (finrank ℝ (VT (X := Y.toData) z ξ) : ℝ) ^ 3 * Y.NA /
      (2 * Y.k0 * Real.sqrt ep0) := by
  classical
  rcases Nat.eq_zero_or_pos (finrank ℝ (VT (X := Y.toData) z ξ)) with h0 | hpos
  · have hsub : Subsingleton (VT (X := Y.toData) z ξ) := Module.finrank_zero_iff.mp h0
    refine ⟨0, ?_⟩
    rw [Subsingleton.elim (d - phi z ξ hξ 0) 0, norm_zero, h0]
    simp
  have : Nonempty (Fin (finrank ℝ (VT (X := Y.toData) z ξ))) := ⟨⟨0, hpos⟩⟩
  obtain ⟨y, hli, hyL, hyn⟩ := short_basis z hξ ep0 hns hD3 hep
  let yb := Basis.mk hli (hli.span_eq_top_of_card_eq_finrank (by simp)).ge
  have hyb : ∀ i, yb i = y i := fun i => Basis.mk_apply _ _ _
  set c := yb.repr d with hc
  set p : VT (X := Y.toData) z ξ := ∑ i, (round (c i) : ℤ) • y i with hp
  have hpL : p ∈ Lat z ξ hξ :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hyL i)
  obtain ⟨μ, hμ⟩ := (mem_Lat z ξ hξ).mp hpL
  refine ⟨μ, ?_⟩
  rw [hμ]
  have hd : d = ∑ i, c i • y i := by
    conv_lhs => rw [← yb.sum_repr d]
    simp only [hyb, hc]
  have hdiff : d - p = ∑ i, (c i - round (c i)) • y i := by
    rw [hd, hp, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_smul, ← Int.cast_smul_eq_zsmul ℝ]
  rw [hdiff]
  have hlam0 : 0 < Y.k0 * Real.sqrt ep0 / Y.NA := by
    have h1 := Y.minWeight_pos
    have h2 : (0 : ℝ) < Y.NA := by exact_mod_cast Y.NA_pos
    have h3 := Real.sqrt_pos.mpr hep
    positivity
  calc ‖∑ i, (c i - round (c i)) • y i‖ ≤ ∑ i, ‖(c i - round (c i)) • y i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (finrank ℝ (VT (X := Y.toData) z ξ)), (1 / 2) *
        ((finrank ℝ (VT (X := Y.toData) z ξ) : ℝ) ^ 2 / (Y.k0 * Real.sqrt ep0 / Y.NA)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (abs_sub_round _) (hyn i) (norm_nonneg _) (by norm_num)
    _ = (finrank ℝ (VT (X := Y.toData) z ξ) : ℝ) ^ 3 * Y.NA / (2 * Y.k0 * Real.sqrt ep0) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h1 := Y.minWeight_pos.ne'
        have h2 : (Y.NA : ℝ) ≠ 0 := by exact_mod_cast Y.NA_pos.ne'
        have h3 := (Real.sqrt_pos.mpr hep).ne'
        field_simp

end lattice

end DiscreteLatticeMinimum

end ReciprocityTheory.ChartRestriction.G.FD
