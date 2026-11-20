import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ZetaReducibleRepEqSubInvAndIsUnit
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeOneOfIsIntegral

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx`.
-/
private theorem norm_le_one_of_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

/- English proof (translation)
Establish `hu : ∀ u : Aˣ, ‖f u‖ = 1`. Introduce `u`. Establish `h1 : ‖f u‖ * ‖f ((u⁻¹ : Aˣ) : A)‖ = 1`. Rewrite using `[← norm_mul, ← map_mul, Units.mul_inv]`. Simplify using the standard rewrite rules.

Establish `h2` using `hle u`. Establish `h3` using `hle (u⁻¹ : Aˣ)`. Establish `h4` using `norm_nonneg (f u)`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨fun u ⟨v, hv⟩ => hv ▸ hu v, ?_⟩` and prove the remaining obligations.

Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible A`. Establish `hl0 : (l : A) ≠ 0`. Introduce `h`. Establish `h' : f l = 0` using `by rw [h, map_zero]`. Establish `: (l : PadicAlgCl l) = 0` using `by simpa using h'`.

Conclude with `(Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this`. Establish `hl : ‖f l‖ < 1`. Establish `: f l = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])` using `by simp`. Rewrite using `[this, norm_algebraMap']`. Conclude with `Padic.norm_p_lt_one`.

Use `⟨‖f ϖ‖, norm_nonneg _, ?_, fun n x hx => ?_⟩` and prove the remaining obligations. Take `⟨n, u, h⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ`. Rewrite `hl` using `[h, map_mul, norm_mul, hu, one_mul, map_pow, norm_pow]`. Assume the negation of the conclusion as `hc`. Conclude with `absurd hl (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))`.

Rewrite `hx` using `[hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton']`. Take `⟨y, rfl⟩` from `hx`. Rewrite using `[map_mul, norm_mul, map_pow, norm_pow]`. Conclude with `mul_le_of_le_one_left (by positivity) (hle y)`.
-/
private theorem dvr_norm {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (f : A →+* PadicAlgCl l) (hle : ∀ x, ‖f x‖ ≤ 1) :
    (∀ u : A, IsUnit u → ‖f u‖ = 1) ∧
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ (n : ℕ) (x : A), x ∈ maximalIdeal A ^ n → ‖f x‖ ≤ q ^ n := by
  have hu : ∀ u : Aˣ, ‖f u‖ = 1 := by
    intro u
    have h1 : ‖f u‖ * ‖f ((u⁻¹ : Aˣ) : A)‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv]; simp
    have h2 := hle u
    have h3 := hle (u⁻¹ : Aˣ)
    have h4 := norm_nonneg (f u)
    nlinarith
  refine ⟨fun u ⟨v, hv⟩ => hv ▸ hu v, ?_⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hl0 : (l : A) ≠ 0 := by
    intro h
    have h' : f l = 0 := by rw [h, map_zero]
    have : (l : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have hl : ‖f l‖ < 1 := by
    have : f l = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  refine ⟨‖f ϖ‖, norm_nonneg _, ?_, fun n x hx => ?_⟩
  · obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
    rw [h, map_mul, norm_mul, hu, one_mul, map_pow, norm_pow] at hl
    by_contra hc
    exact absurd hl (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))
  · rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [map_mul, norm_mul, map_pow, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hle y)

/- English proof (translation)
Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations. Simplify using `[conjBy, mul_assoc]`.
-/
private theorem conjBy_conjBy {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (h k : GL (Fin 3) R) :
    conjBy h (conjBy k r) = conjBy (h * k) r := by
  refine MonoidHom.ext fun g => ?_
  simp [conjBy, mul_assoc]

/- English proof (translation)
Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations. Simplify using `[conjBy]`.
-/
private theorem conjBy_one {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) :
    conjBy 1 r = r := by
  refine MonoidHom.ext fun g => ?_
  simp [conjBy]

/- English proof (translation)
Take `⟨hu, q, hq0, hq1, hq⟩` from `dvr_norm (f : A →+* PadicAlgCl l) hle`. Simplify using `only [RingHom.coe_coe] at hu hq`. Establish `hr : r = conjBy (tor _ t⁻¹) (push f r')`. Rewrite using `[hp, conjBy_conjBy, ← map_mul, inv_mul_cancel, map_one, conjBy_one]`. Take `⟨c1, c2, c3, -, -⟩` from `conjBy_tor (push f r') t⁻¹`.

Rewrite `c1`, `c2`, `c3` using `[← hr]`. Establish `hent : ∀ g a b, (push f r' g).mat a b = f ((r' g).mat a b)` using `fun _ _ _ => rfl`. Establish `hrz : ∀ g a b, (F.rz (PadicAlgCl l) g).mat a b = algebraMap O _ ((r0 F.η F.Ψ g).mat a b)` using `fun _ _ _ => rfl`. Establish `hdiag : ∀ g a, ‖(r g).mat a a - (F.rz (PadicAlgCl l) g).mat a a‖ < 1`. Introduce `g a`.

Establish `h` using `hq 1 _ (by rw [pow_one]; exact hpt.red g a a)`. Rewrite `h` using `[pow_one, Matrix.sub_apply, map_sub, Matrix.map_apply, AlgHom.commutes]`. Rewrite using `[c1, hent, hrz]`. Simplify using `only [wt, sub_self, zpow_zero, Units.val_one, one_mul]`. Conclude with `lt_of_le_of_lt h hq1`.

Establish `hz : ‖zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l))‖ < 1`. Establish `e : zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l)) = ((r g₁).mat 0 0 - (F.rz (PadicAlgCl l) g₁).mat 0 0) + -((r (gstar F.c g₁)).mat 0 0 - (F.rz (PadicAlgCl l) (gstar F.c g₁)).mat 0 0)`. Simplify using `only [zeta, zmat, Matrix.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (hdiag _ _) ?_)` and prove the remaining obligations. Rewrite using `[norm_neg]`. Conclude with `hdiag _ _`. Establish `hz0 : ‖zeta F.c g₁ (F.rz (PadicAlgCl l))‖ = 1`. Establish `h0` using `(zeta_reducible_rep_eq_sub_inv_and_isUnit F.η F.Ψ F.c g₁ ⟨hF.csq, hF.ηc, hF.Ψc, hg.1, hg.2⟩).2`.

Rewrite using `[← hu _ (h0.map (algebraMap O A)), AlgHom.commutes]`. Simplify using `only [zeta, zmat, Matrix.sub_apply, map_sub, hrz]`. Use `⟨fun g => (c2 g).trans (hpt.mult g), c3 _ _ ⟨?_, ?_, ?_⟩, ?_, hz, ?_, hdiag⟩` and prove the remaining obligations. Use extensionality with `a b`. Rewrite using `[hent, hpt.norm.atc]`.

Simplify using `[Matrix.one_apply, apply_ite f]`. Establish `h` using `congrArg f hpt.norm.z12`. Simplify `h` using `only [zmat, Matrix.sub_apply, map_sub, map_zero, hent]`. Establish `h` using `congrArg f hpt.norm.z21`. Simplify `h` using `only [zmat, Matrix.sub_apply, map_sub, map_zero, hent]`.

Use `continuous_matrix fun a b => ?_` and prove the remaining obligations. Simplify using `only [mats, c1, hent]`. Use `continuous_const.mul (continuous_iff_continuousAt.2 fun g => ?_)` and prove the remaining obligations. Rewrite using `[ContinuousAt, Metric.tendsto_nhds]`. Introduce `ε hε`.

Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one hε hq1`. Use `filter_upwards [(hpt.cont n).eventually_eq g] with g' hg'`. Establish `h` using `congrFun (congrFun hg' a) b`. Rewrite `h` using `[Matrix.map_apply, Matrix.map_apply, Ideal.Quotient.eq]`. Rewrite using `[dist_eq_norm, ← map_sub]`.

Conclude with `lt_of_le_of_lt (hq n _ h) hn`. Establish `e : zeta F.c g₁ r = (zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l))) + zeta F.c g₁ (F.rz (PadicAlgCl l))`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hz0]; exact hz.ne), hz0]`. Conclude with `max_eq_right hz.le`.
-/
private theorem aux {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra O (PadicAlgCl l)]
    {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group Γ] [TopologicalSpace Γ]
    (F : Frame O G Γ ι) (hF : F.Ok) (g₁ : Γ) (hg : F.Marked g₁) (r : Γ →* GG 3 (PadicAlgCl l))
    {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra O A]
    (f : A →ₐ[O] PadicAlgCl l) (hle : ∀ x, ‖f x‖ ≤ 1) (t : (PadicAlgCl l)ˣ) (r' : Γ →* GG 3 A)
    (hpt : F.IsPt g₁ r') (hp : push f r' = conjBy (tor _ t) r) :
    HasMult F.η r ∧ Normalised F.c g₁ r ∧ Continuous (mats r) ∧
      ‖zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l))‖ < 1 ∧ ‖zeta F.c g₁ r‖ = 1 ∧
      (∀ g a, ‖(r g).mat a a - (F.rz (PadicAlgCl l) g).mat a a‖ < 1) := by
  obtain ⟨hu, q, hq0, hq1, hq⟩ := dvr_norm (f : A →+* PadicAlgCl l) hle
  simp only [RingHom.coe_coe] at hu hq
  have hr : r = conjBy (tor _ t⁻¹) (push f r') := by
    rw [hp, conjBy_conjBy, ← map_mul, inv_mul_cancel, map_one, conjBy_one]
  obtain ⟨c1, c2, c3, -, -⟩ := conjBy_tor (push f r') t⁻¹
  rw [← hr] at c1 c2 c3
  have hent : ∀ g a b, (push f r' g).mat a b = f ((r' g).mat a b) := fun _ _ _ => rfl
  have hrz : ∀ g a b, (F.rz (PadicAlgCl l) g).mat a b = algebraMap O _ ((r0 F.η F.Ψ g).mat a b) := fun _ _ _ => rfl
  have hdiag : ∀ g a, ‖(r g).mat a a - (F.rz (PadicAlgCl l) g).mat a a‖ < 1 := by
    intro g a
    have h := hq 1 _ (by rw [pow_one]; exact hpt.red g a a)
    rw [pow_one, Matrix.sub_apply, map_sub, Matrix.map_apply, AlgHom.commutes] at h
    rw [c1, hent, hrz]
    simp only [wt, sub_self, zpow_zero, Units.val_one, one_mul]
    exact lt_of_le_of_lt h hq1
  have hz : ‖zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l))‖ < 1 := by
    have e : zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l)) =
        ((r g₁).mat 0 0 - (F.rz (PadicAlgCl l) g₁).mat 0 0) +
          -((r (gstar F.c g₁)).mat 0 0 - (F.rz (PadicAlgCl l) (gstar F.c g₁)).mat 0 0) := by
      simp only [zeta, zmat, Matrix.sub_apply]; ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (hdiag _ _) ?_)
    rw [norm_neg]; exact hdiag _ _
  have hz0 : ‖zeta F.c g₁ (F.rz (PadicAlgCl l))‖ = 1 := by
    have h0 := (zeta_reducible_rep_eq_sub_inv_and_isUnit F.η F.Ψ F.c g₁ ⟨hF.csq, hF.ηc, hF.Ψc, hg.1, hg.2⟩).2
    rw [← hu _ (h0.map (algebraMap O A)), AlgHom.commutes]
    simp only [zeta, zmat, Matrix.sub_apply, map_sub, hrz]
  refine ⟨fun g => (c2 g).trans (hpt.mult g), c3 _ _ ⟨?_, ?_, ?_⟩, ?_, hz, ?_, hdiag⟩
  · ext a b
    rw [hent, hpt.norm.atc]
    simp [Matrix.one_apply, apply_ite f]
  · have h := congrArg f hpt.norm.z12
    simpa only [zmat, Matrix.sub_apply, map_sub, map_zero, hent] using h
  · have h := congrArg f hpt.norm.z21
    simpa only [zmat, Matrix.sub_apply, map_sub, map_zero, hent] using h
  · refine continuous_matrix fun a b => ?_
    simp only [mats, c1, hent]
    refine continuous_const.mul (continuous_iff_continuousAt.2 fun g => ?_)
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hq1
    filter_upwards [(hpt.cont n).eventually_eq g] with g' hg'
    have h := congrFun (congrFun hg' a) b
    rw [Matrix.map_apply, Matrix.map_apply, Ideal.Quotient.eq] at h
    rw [dist_eq_norm, ← map_sub]
    exact lt_of_le_of_lt (hq n _ h) hn
  · have e : zeta F.c g₁ r = (zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l))) + zeta F.c g₁ (F.rz (PadicAlgCl l)) := by
      ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hz0]; exact hz.ne), hz0]
    exact max_eq_right hz.le

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg r hr`. Take `⟨A, hA, hfin, t, r', hpt, hp⟩` from `hr`. Take `⟨h1, h2, h3, h4, h5, h6⟩` from `aux F hF g₁ hg r A.val (fun x => norm_le_one_of_int l _ (isIntegral_trans (A := O) _ ((Algebra.IsIntegral.isIntegral (R := O) x).map A.val))) t r' hpt hp`. Use `⟨h1, h2, h3, h4, h5, h6, fun s => ⟨A, hA, hfin, t * s⁻¹, r', hpt, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[conjBy_conjBy, ← map_mul, inv_mul_cancel_right, hp]`.
-/
theorem UpperTheory.V.UnitaryThreeInertia.isCharZeroPt_basic :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [FaithfulSMul O (PadicAlgCl l)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ g₁, F.Marked g₁ → ∀ (r : Γ →* GG 3 (PadicAlgCl l)), F.IsCharZeroPt g₁ r → HasMult F.η r ∧ Normalised F.c g₁ r ∧ Continuous (mats r) ∧ ‖zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l))‖ < 1 ∧ ‖zeta F.c g₁ r‖ = 1 ∧
      (∀ g a, ‖(r g).mat a a - (F.rz (PadicAlgCl l) g).mat a a‖ < 1) ∧ ∀ t, F.IsCharZeroPt g₁ (conjBy (tor (PadicAlgCl l) t) r) := by
  intro l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg r hr
  obtain ⟨A, hA, hfin, t, r', hpt, hp⟩ := hr
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := aux F hF g₁ hg r A.val (fun x =>
    norm_le_one_of_int l _ (isIntegral_trans (A := O) _ ((Algebra.IsIntegral.isIntegral (R := O) x).map A.val)))
    t r' hpt hp
  refine ⟨h1, h2, h3, h4, h5, h6, fun s => ⟨A, hA, hfin, t * s⁻¹, r', hpt, ?_⟩⟩
  rw [conjBy_conjBy, ← map_mul, inv_mul_cancel_right, hp]
