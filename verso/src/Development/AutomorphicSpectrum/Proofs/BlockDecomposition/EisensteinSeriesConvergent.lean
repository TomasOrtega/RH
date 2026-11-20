import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbBar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegersBoundedEmbeddingsCountStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorBoundByHeightStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticIntegralCoefficientsBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableHeightPowOfPolynomialCountStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvertibleExistsNonzeroMinorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PluckerMinorsDetermineColumnSpaceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePlaceMinorHeightBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMinorHeightBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardCompactEntriesIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormFinitePlaceBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormInfinitePlaceBoundStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
  {J : Type} [Fintype J]

/- English proof (translation)
Simplify using `using absBar_algebraMap F v 1`.
-/
theorem absBar_one (v : Pl F) : absBar F v 1 = 1 := by
  simpa using absBar_algebraMap F v 1

/- English proof (translation)
The claim follows from `Finset.le_sup (f := fun f => absBar F v (τ (u f))) (Finset.mem_univ f)`.
-/
theorem le_supBar (v : Pl F) (τ : E →ₐ[F] FvBar F v) (u : J → E) (f : J) : absBar F v (τ (u f)) ≤ supBar v τ u :=
  Finset.le_sup (f := fun f => absBar F v (τ (u f))) (Finset.mem_univ f)

/- English proof (translation)
Use `le_supBar v τ u f₀` as an intermediate fact. Rewrite `this` using `[hu, map_one, absBar_one]`. Then use the resulting hypothesis.
-/
theorem one_le_supBar (v : Pl F) (τ : E →ₐ[F] FvBar F v) {u : J → E} {f₀ : J} (hu : u f₀ = 1) : 1 ≤ supBar v τ u := by
  have := le_supBar v τ u f₀
  rwa [hu, map_one, absBar_one] at this

/- English proof (translation)
The claim follows from `one_le_mul_of_one_le_of_one_le (one_le_supBar v _ hu) (one_le_supBar v _ hu)`.
-/
theorem one_le_locFin (v : Pl F) {u : J → E} {f₀ : J} (hu : u f₀ = 1) : 1 ≤ locFin σ v u :=
  one_le_mul_of_one_le_of_one_le (one_le_supBar v _ hu) (one_le_supBar v _ hu)

open Classical in
/- English proof (translation)
The claim follows from `Finset.le_sup (f := fun p : EmbOver E w × J => ‖p.1.1 (u p.2)‖₊) (Finset.mem_univ (τ, f))`.
-/
theorem le_supInf (w : InfinitePlace F) (τ : EmbOver E w) (u : J → E) (f : J) :
    ‖τ.1 (u f)‖₊ ≤ Finset.univ.sup fun p : EmbOver E w × J => ‖p.1.1 (u p.2)‖₊ :=
  Finset.le_sup (f := fun p : EmbOver E w × J => ‖p.1.1 (u p.2)‖₊) (Finset.mem_univ (τ, f))

open Classical in
/- English proof (translation)
Take `⟨τ⟩` from `nonempty_embOver (E := E) F w`. Use `le_supInf w τ u f₀` as an intermediate fact. Rewrite `this` using `[hu, map_one, nnnorm_one]`. Then use the resulting hypothesis.
-/
theorem one_le_supInf (w : InfinitePlace F) {u : J → E} {f₀ : J} (hu : u f₀ = 1) :
    1 ≤ Finset.univ.sup fun p : EmbOver E w × J => ‖p.1.1 (u p.2)‖₊ := by
  obtain ⟨τ⟩ := nonempty_embOver (E := E) F w
  have := le_supInf w τ u f₀
  rwa [hu, map_one, nnnorm_one] at this

/- English proof (translation)
The claim follows from `one_le_pow₀ (one_le_supInf w hu)`.
-/
theorem one_le_locInf (w : InfinitePlace F) {u : J → E} {f₀ : J} (hu : u f₀ = 1) : 1 ≤ locInf w u :=
  one_le_pow₀ (one_le_supInf w hu)

/- English proof (translation)
Use `le_absFin F v τ ((1 : Fv F v) ⊗ₜ[F] x)` as an intermediate fact. Simplify using `using this`.
-/
theorem absBar_le_absFin (v : Pl F) (τ : E →ₐ[F] FvBar F v) (x : E) : absBar F v (τ x) ≤ absFin F v ((1 : Fv F v) ⊗ₜ[F] x) := by
  have := le_absFin F v τ ((1 : Fv F v) ⊗ₜ[F] x)
  simpa using this

/- English proof (translation)
Simplify using `[compFin, inclR]`.
-/
theorem compFin_inclR (v : Pl F) (x : E) : compFin F E v (inclR (F := F) (AF F) x) = (1 : Fv F v) ⊗ₜ[F] x := by
  simp [compFin, inclR]

/- English proof (translation)
Use `(eventually_absFin_le_one F (inclR (F := F) (AF F) x)).mono fun v hv τ => ?_` and prove the remaining obligations. Rewrite `hv` using `[compFin_inclR]`. Conclude with `(absBar_le_absFin v τ x).trans hv`.
-/
theorem eventually_abs_le_one (x : E) : ∀ᶠ v : Pl F in cofinite, ∀ τ : E →ₐ[F] FvBar F v, absBar F v (τ x) ≤ 1 := by
  refine (eventually_absFin_le_one F (inclR (F := F) (AF F) x)).mono fun v hv τ => ?_
  rw [compFin_inclR] at hv
  exact (absBar_le_absFin v τ x).trans hv

/- English proof (translation)
Establish `h : ∀ᶠ v : Pl F in cofinite, ∀ f, ∀ τ : E →ₐ[F] FvBar F v, absBar F v (τ (u f)) ≤ 1` using `eventually_all.2 fun f => eventually_abs_le_one (u f)`. Use `(eventually_cofinite.1 h).subset fun v hv hv' => hv ?_` and prove the remaining obligations. Establish `h1 : ∀ τ : E →ₐ[F] FvBar F v, supBar v τ u ≤ 1` using `fun τ => Finset.sup_le fun f _ => hv' f τ`. Conclude with `le_antisymm (by simpa [locFin] using mul_le_mul' (h1 (embBar F E v)) (h1 ((embBar F E v).comp σ))) (one_le_locFin v hu)`.
-/
theorem finite_mulSupport_locFin (σ : E →ₐ[F] E) {u : J → E} {f₀ : J} (hu : u f₀ = 1) :
    (Function.mulSupport fun v : Pl F => locFin σ v u).Finite := by
  have h : ∀ᶠ v : Pl F in cofinite, ∀ f, ∀ τ : E →ₐ[F] FvBar F v, absBar F v (τ (u f)) ≤ 1 :=
    eventually_all.2 fun f => eventually_abs_le_one (u f)
  refine (eventually_cofinite.1 h).subset fun v hv hv' => hv ?_
  have h1 : ∀ τ : E →ₐ[F] FvBar F v, supBar v τ u ≤ 1 := fun τ => Finset.sup_le fun f _ => hv' f τ
  exact le_antisymm (by simpa [locFin] using mul_le_mul' (h1 (embBar F E v)) (h1 ((embBar F E v).comp σ))) (one_le_locFin v hu)

/- English proof (translation)
The claim follows from `one_le_mul_of_one_le_of_one_le (Finset.one_le_prod' fun w _ => one_le_locInf w hu) (one_le_finprod' fun v => one_le_locFin v hu)`.
-/
theorem one_le_vecHt {u : J → E} {f₀ : J} (hu : u f₀ = 1) : 1 ≤ vecHt σ u :=
  one_le_mul_of_one_le_of_one_le (Finset.one_le_prod' fun w _ => one_le_locInf w hu)
    (one_le_finprod' fun v => one_le_locFin v hu)

/- English proof (translation)
Establish `hs` using `finite_mulSupport_locFin σ hu`. Establish `hs2` using `GlobalTheory.Doubling.finite_mulSupport_absEv δ`. Rewrite using `[GlobalTheory.Doubling.absE_apply, vecHt, mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← finprod_mul_distrib hs2 hs]`. Use `mul_le_mul' (Finset.prod_le_prod' fun w _ => ?_) (finprod_le_finprod' (hs2.union hs |>.subset (Function.mulSupport_mul _ _)) (hB.subset (Function.mulSupport_pow _ _)) fun v => ?_)` and prove the remaining obligations. Use `GlobalTheory.T.local_norm_infinite_place_bound F E σ hcm J w (e w) u _ (fun f => compInf F E w (z f)) (Bi w) (fun f => ?_) (fun f => hi w f)` and prove the remaining obligations.

Rewrite using `[hz, map_mul]`. Use `congr 1`. Use `GlobalTheory.T.local_norm_finite_place_bound F E σ hcm J v u _ (fun f => compFin F E v (z f)) (Bf v) (fun f => ?_) (fun f => hf v f)` and prove the remaining obligations. Rewrite using `[hz, map_mul, compFin_inclR]`. Both sides reduce to the same expression.
-/
theorem absE_mul_vecHt_le (hcm : IsCMExt F E σ) (e : ∀ w : InfinitePlace F, EmbOver E w) {u : J → E} {f₀ : J} (hu : u f₀ = 1)
    (δ : (AE F E)ˣ) (z : J → AE F E) (hz : ∀ f, z f = inclR (F := F) (AF F) (u f) * δ.1)
    (Bi : InfinitePlace F → ℝ≥0) (Bf : Pl F → ℝ≥0) (hB : (Function.mulSupport Bf).Finite)
    (hi : ∀ w f, ‖piInf (e w) (z f)‖₊ ≤ Bi w) (hf : ∀ v f, absFin F v (compFin F E v (z f)) ≤ Bf v) :
    absE F E δ * vecHt σ u ≤ (∏ w, Bi w ^ 2) * ∏ᶠ v, Bf v ^ 2 := by
  have hs := finite_mulSupport_locFin σ hu
  have hs2 := GlobalTheory.Doubling.finite_mulSupport_absEv δ
  rw [GlobalTheory.Doubling.absE_apply, vecHt, mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← finprod_mul_distrib hs2 hs]
  refine mul_le_mul' (Finset.prod_le_prod' fun w _ => ?_) (finprod_le_finprod' (hs2.union hs |>.subset (Function.mulSupport_mul _ _))
    (hB.subset (Function.mulSupport_pow _ _)) fun v => ?_)
  · refine GlobalTheory.T.local_norm_infinite_place_bound F E σ hcm J w (e w) u _ (fun f => compInf F E w (z f)) (Bi w) (fun f => ?_) (fun f => hi w f)
    rw [hz, map_mul]
    congr 1
  · refine GlobalTheory.T.local_norm_finite_place_bound F E σ hcm J v u _ (fun f => compFin F E v (z f)) (Bf v) (fun f => ?_) (fun f => hf v f)
    rw [hz, map_mul, compFin_inclR]
    rfl

end GlobalTheory.CompanionTheory.GodementH
end

noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {J : Type} [Fintype J]

/- English proof (translation)
Use `hcm.1` as an intermediate fact. Set `φ : F →+* ℂ` to `τ.comp (algebraMap F E)`. Establish `hr : ComplexEmbedding.IsReal φ` using `InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal (InfinitePlace.mk φ))`. Conclude with `⟨InfinitePlace.mk φ, ⟨τ, (InfinitePlace.embedding_mk_eq_of_isReal hr).symm⟩, rfl⟩`.
-/
theorem exists_embOver (hcm : IsCMExt F E σ) (τ : E →+* ℂ) : ∃ (w : InfinitePlace F) (e : EmbOver E w), e.1 = τ := by
  have := hcm.1
  let φ : F →+* ℂ := τ.comp (algebraMap F E)
  have hr : ComplexEmbedding.IsReal φ := InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal (InfinitePlace.mk φ))
  exact ⟨InfinitePlace.mk φ, ⟨τ, (InfinitePlace.embedding_mk_eq_of_isReal hr).symm⟩, rfl⟩

/- English proof (translation)
Set `R` to `integralClosure ℤ E`. Set `b' : R` to `⟨b, hb⟩`. Set `c' : R` to `⟨c, hc⟩`. Establish `hz : IsIntegral R z`. Use `⟨Polynomial.X ^ 2 + (Polynomial.C (-b') * Polynomial.X + Polynomial.C c'), ?_, ?_⟩` and prove the remaining obligations.

Use `Polynomial.monic_X_pow_add (lt_of_le_of_lt Polynomial.degree_linear_le ?_)` and prove the remaining obligations. Evaluate the numerical expressions. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]`. Express the relevant statement in the definitionally equal form `z ^ 2 + (-b * z + c) = 0`. Take the linear combination `h`.

Conclude with `isIntegral_trans z hz`.
-/
theorem isIntegral_of_quad {z b c : E} (hb : IsIntegral ℤ b) (hc : IsIntegral ℤ c) (h : z ^ 2 - b * z + c = 0) : IsIntegral ℤ z := by
  let R := integralClosure ℤ E
  let b' : R := ⟨b, hb⟩
  let c' : R := ⟨c, hc⟩
  have hz : IsIntegral R z := by
    refine ⟨Polynomial.X ^ 2 + (Polynomial.C (-b') * Polynomial.X + Polynomial.C c'), ?_, ?_⟩
    · refine Polynomial.monic_X_pow_add (lt_of_le_of_lt Polynomial.degree_linear_le ?_)
      norm_num
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
      change z ^ 2 + (-b * z + c) = 0
      linear_combination h
  exact isIntegral_trans z hz

/- English proof (translation)
Take `⟨y₁, y₂, hq, hy⟩` from `GlobalTheory.T.quadratic_integral_coefficients_bound F E σ hcm (u f)`. Establish `hloc : ∀ (v : Pl F), max 1 ‖algebraMap F (Fv F v) y₁‖₊ ≤ locFin σ v u ∧ max 1 ‖algebraMap F (Fv F v) y₂‖₊ ≤ locFin σ v u`. Introduce `v`. Take `⟨h1, h2⟩` from `hy v (embBar F E v)`. Establish `a1` using `le_supBar v (embBar F E v) u f`.

Establish `b1` using `le_supBar v ((embBar F E v).comp σ) u f`. Establish `a2 : 1 ≤ supBar v (embBar F E v) u` using `one_le_supBar v _ hu`. Establish `b2 : 1 ≤ supBar v ((embBar F E v).comp σ) u` using `one_le_supBar v _ hu`. Establish `hl : locFin σ v u = supBar v (embBar F E v) u * supBar v ((embBar F E v).comp σ) u` using `rfl`. Establish `hb1 : absBar F v (embBar F E v (σ (u f))) ≤ supBar v ((embBar F E v).comp σ) u` using `b1`.

Use `⟨max_le (one_le_locFin v hu) ?_, max_le (one_le_locFin v hu) ?_⟩` and prove the remaining obligations. Use `h1.trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[hl]`. Conclude with `a1.trans (le_mul_of_one_le_right' b2)`. Rewrite using `[hl]`.

Conclude with `hb1.trans (le_mul_of_one_le_left' a2)`. Rewrite using `[h2, hl]`. Conclude with `mul_le_mul' a1 hb1`. Establish `hs` using `finite_mulSupport_locFin σ hu`. Establish `hsup : ∀ y : F, (∀ v : Pl F, max 1 ‖algebraMap F (Fv F v) y‖₊ ≤ locFin σ v u) → ∏ᶠ v : Pl F, max 1 ‖algebraMap F (Fv F v) y‖₊ ≤ ∏ᶠ v, locFin σ v u`.

Introduce `y hy`. Establish `hsub : (Function.mulSupport fun v : Pl F => max 1 ‖algebraMap F (Fv F v) y‖₊).Finite`. Use `hs.subset fun v hv hv' => hv ?_` and prove the remaining obligations. Conclude with `le_antisymm ((hy v).trans (le_of_eq hv')) (le_max_left _ _)`. Conclude with `finprod_le_finprod' hsub hs hy`.

Take `⟨m₁, p₁, l₁, i₁⟩` from `GlobalTheory.T.denominator_bound_by_height F y₁`. Take `⟨m₂, p₂, l₂, i₂⟩` from `GlobalTheory.T.denominator_bound_by_height F y₂`. Use `⟨m₁ * m₂, Nat.mul_pos p₁ p₂, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[sq]`. Use `push_cast`.

Conclude with `mul_le_mul' (l₁.trans (hsup _ fun v => (hloc v).1)) (l₂.trans (hsup _ fun v => (hloc v).2))`. Establish `j₁ : IsIntegral ℤ ((m₁ : E) * algebraMap F E y₁)`. Use `i₁.map (IsScalarTower.toAlgHom ℤ F E)` as an intermediate fact. Simplify using `using this`. Establish `j₂ : IsIntegral ℤ ((m₂ : E) * algebraMap F E y₂)`.

Use `i₂.map (IsScalarTower.toAlgHom ℤ F E)` as an intermediate fact. Simplify using `using this`. Establish `n₁ : IsIntegral ℤ (m₁ : E)` using `isIntegral_natCast _`. Establish `n₂ : IsIntegral ℤ (m₂ : E)` using `isIntegral_natCast _`. Use `isIntegral_of_quad (b := (m₂ : E) * ((m₁ : E) * algebraMap F E y₁)) (c := (m₁ : E) ^ 2 * (m₂ : E) * ((m₂ : E) * algebraMap F E y₂)) (n₂.mul j₁) (((n₁.pow 2).mul n₂).mul j₂) ?_` and prove the remaining obligations.

Use `push_cast`. Take the linear combination `((m₁ : E) * m₂) ^ 2 * hq`.
-/
theorem denom_one (hcm : IsCMExt F E σ) {u : J → E} {f₀ : J} (hu : u f₀ = 1) (f : J) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ≥0) ≤ (∏ᶠ v, locFin σ v u) ^ 2 ∧ IsIntegral ℤ ((m : E) * u f) := by
  obtain ⟨y₁, y₂, hq, hy⟩ := GlobalTheory.T.quadratic_integral_coefficients_bound F E σ hcm (u f)
  have hloc : ∀ (v : Pl F), max 1 ‖algebraMap F (Fv F v) y₁‖₊ ≤ locFin σ v u ∧ max 1 ‖algebraMap F (Fv F v) y₂‖₊ ≤ locFin σ v u := by
    intro v
    obtain ⟨h1, h2⟩ := hy v (embBar F E v)
    have a1 := le_supBar v (embBar F E v) u f
    have b1 := le_supBar v ((embBar F E v).comp σ) u f
    have a2 : 1 ≤ supBar v (embBar F E v) u := one_le_supBar v _ hu
    have b2 : 1 ≤ supBar v ((embBar F E v).comp σ) u := one_le_supBar v _ hu
    have hl : locFin σ v u = supBar v (embBar F E v) u * supBar v ((embBar F E v).comp σ) u := rfl
    have hb1 : absBar F v (embBar F E v (σ (u f))) ≤ supBar v ((embBar F E v).comp σ) u := b1
    refine ⟨max_le (one_le_locFin v hu) ?_, max_le (one_le_locFin v hu) ?_⟩
    · refine h1.trans (max_le ?_ ?_)
      · rw [hl]; exact a1.trans (le_mul_of_one_le_right' b2)
      · rw [hl]; exact hb1.trans (le_mul_of_one_le_left' a2)
    · rw [h2, hl]; exact mul_le_mul' a1 hb1
  have hs := finite_mulSupport_locFin σ hu
  have hsup : ∀ y : F, (∀ v : Pl F, max 1 ‖algebraMap F (Fv F v) y‖₊ ≤ locFin σ v u) →
      ∏ᶠ v : Pl F, max 1 ‖algebraMap F (Fv F v) y‖₊ ≤ ∏ᶠ v, locFin σ v u := by
    intro y hy
    have hsub : (Function.mulSupport fun v : Pl F => max 1 ‖algebraMap F (Fv F v) y‖₊).Finite := by
      refine hs.subset fun v hv hv' => hv ?_
      exact le_antisymm ((hy v).trans (le_of_eq hv')) (le_max_left _ _)
    exact finprod_le_finprod' hsub hs hy
  obtain ⟨m₁, p₁, l₁, i₁⟩ := GlobalTheory.T.denominator_bound_by_height F y₁
  obtain ⟨m₂, p₂, l₂, i₂⟩ := GlobalTheory.T.denominator_bound_by_height F y₂
  refine ⟨m₁ * m₂, Nat.mul_pos p₁ p₂, ?_, ?_⟩
  · rw [sq]; push_cast
    exact mul_le_mul' (l₁.trans (hsup _ fun v => (hloc v).1)) (l₂.trans (hsup _ fun v => (hloc v).2))
  · have j₁ : IsIntegral ℤ ((m₁ : E) * algebraMap F E y₁) := by
      have := i₁.map (IsScalarTower.toAlgHom ℤ F E)
      simpa using this
    have j₂ : IsIntegral ℤ ((m₂ : E) * algebraMap F E y₂) := by
      have := i₂.map (IsScalarTower.toAlgHom ℤ F E)
      simpa using this
    have n₁ : IsIntegral ℤ (m₁ : E) := isIntegral_natCast _
    have n₂ : IsIntegral ℤ (m₂ : E) := isIntegral_natCast _
    refine isIntegral_of_quad (b := (m₂ : E) * ((m₁ : E) * algebraMap F E y₁))
      (c := (m₁ : E) ^ 2 * (m₂ : E) * ((m₂ : E) * algebraMap F E y₂)) (n₂.mul j₁) (((n₁.pow 2).mul n₂).mul j₂) ?_
    push_cast
    linear_combination ((m₁ : E) * m₂) ^ 2 * hq

/- English proof (translation)
Use `choose m hm hl hi using denom_one hcm hu`. Use `⟨∏ f, m f, Finset.prod_pos fun f _ => hm f, ?_, fun f => ?_⟩` and prove the remaining obligations. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ f)]`.

Use `push_cast`. Establish `: ((m f : E) * ∏ x ∈ Finset.univ.erase f, (m x : E)) * u f = (∏ x ∈ Finset.univ.erase f, (m x : E)) * ((m f : E) * u f)` using `by ring`. Rewrite using `[this]`. Use `IsIntegral.mul ?_ (hi f)` and prove the remaining obligations. Conclude with `(isIntegral_natCast (R := ℤ) (B := E) (∏ x ∈ Finset.univ.erase f, m x))` after adjusting the coercions.
-/
theorem denom_all (hcm : IsCMExt F E σ) {u : J → E} {f₀ : J} (hu : u f₀ = 1) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ≥0) ≤ (∏ᶠ v, locFin σ v u) ^ (2 * Fintype.card J) ∧ ∀ f, IsIntegral ℤ ((m : E) * u f) := by
  classical
  choose m hm hl hi using denom_one hcm hu
  refine ⟨∏ f, m f, Finset.prod_pos fun f _ => hm f, ?_, fun f => ?_⟩
  · push_cast
    calc ∏ f, (m f : ℝ≥0) ≤ ∏ _f : J, (∏ᶠ v, locFin σ v u) ^ 2 := Finset.prod_le_prod' fun f _ => hl f
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  · rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ f)]
    push_cast
    have : ((m f : E) * ∏ x ∈ Finset.univ.erase f, (m x : E)) * u f = (∏ x ∈ Finset.univ.erase f, (m x : E)) * ((m f : E) * u f) := by ring
    rw [this]
    refine IsIntegral.mul ?_ (hi f)
    exact_mod_cast (isIntegral_natCast (R := ℤ) (B := E) (∏ x ∈ Finset.univ.erase f, m x))

/- English proof (translation)
Take `⟨C₀, hC₀, hlat⟩` from `GlobalTheory.T.integers_bounded_embeddings_count E`. Use `set Jc := Fintype.card J with hJc`. Use `set d := Module.finrank ℚ E with hd`. Use `⟨C₀ ^ Jc, 2 * Jc + (2 * Jc + 1) * d * Jc, pow_pos hC₀ _, fun T hT => ?_⟩` and prove the remaining obligations. Use `set R : ℝ := T ^ (2 * Jc + 1) with hR`.

Establish `hR1 : 1 ≤ R` using `one_le_pow₀ hT`. Take `⟨hLf, hLc⟩` from `hlat R hR1`. Use `set N₀ : ℕ := ⌊T ^ (2 * Jc)⌋₊ with hN₀`. Set `P : Finset (ℕ × (J → 𝓞 E))` to `Finset.Icc 1 N₀ ×ˢ Fintype.piFinset fun _ : J => hLf.toFinset`. Set `φ : ℕ × (J → 𝓞 E) → J → E` to `fun p f => (p.2 f : E) / (p.1 : E)`.

Establish `hsub : {u : J → E | (∃ f₀, u f₀ = 1) ∧ (vecHt σ u : ℝ) ≤ T} ⊆ φ '' (P : Set _)`. Introduce and unpack `u ⟨⟨f₀, hu⟩, huT⟩`. Take `⟨m, hm, hl, hi⟩` from `denom_all hcm hu`. Establish `hHi : 1 ≤ ∏ w : InfinitePlace F, locInf w u` using `Finset.one_le_prod' fun w _ => one_le_locInf w hu`. Establish `hHf : 1 ≤ ∏ᶠ v, locFin σ v u` using `one_le_finprod' fun v => one_le_locFin v hu`.

Establish `hHf' : ((∏ᶠ v, locFin σ v u : ℝ≥0) : ℝ) ≤ T`. Use `le_trans ?_ huT` and prove the remaining obligations. Conclude with `le_mul_of_one_le_left' hHi` after adjusting the coercions. Establish `hHi' : ((∏ w : InfinitePlace F, locInf w u : ℝ≥0) : ℝ) ≤ T`. Use `le_trans ?_ huT` and prove the remaining obligations.

Conclude with `le_mul_of_one_le_right' hHf` after adjusting the coercions. Establish `hmT : (m : ℝ) ≤ T ^ (2 * Jc)`. Establish `h1 : (m : ℝ) ≤ ((∏ᶠ v, locFin σ v u : ℝ≥0) : ℝ) ^ (2 * Jc)` using `by exact_mod_cast hl`. Conclude with `h1.trans (pow_le_pow_left₀ (by positivity) hHf' _)`. Establish `hconj : ∀ (τ : E →+* ℂ) f, ‖τ (u f)‖ ≤ T`.

Introduce `τ f`. Take `⟨w, e, rfl⟩` from `exists_embOver hcm τ`. Establish `h1` using `le_supInf w e u f`. Establish `h2` using `one_le_supInf w (u := u) hu`. Establish `h3 : locInf w u ≤ ∏ w : InfinitePlace F, locInf w u` using `Finset.single_le_prod' (f := fun w : InfinitePlace F => locInf w u) (fun w _ => one_le_locInf w hu) (Finset.mem_univ w)`.

Establish `h4 : ‖e.1 (u f)‖₊ ≤ locInf w u`. Use `h1.trans ?_` and prove the remaining obligations. Rewrite using `[locInf]`. Conclude with `le_self_pow₀ h2 two_ne_zero`. Establish `h5 : (‖e.1 (u f)‖₊ : ℝ) ≤ ((∏ w : InfinitePlace F, locInf w u : ℝ≥0) : ℝ)` using `by exact_mod_cast h4.trans h3`.

Conclude with `h5.trans hHi'`. Use `⟨(m, fun f => ⟨(m : E) * u f, hi f⟩), ?_, ?_⟩` and prove the remaining obligations. Use `Finset.mem_coe.2 (Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hm, Nat.le_floor hmT⟩, Fintype.mem_piFinset.2 fun f => hLf.mem_toFinset.2 fun τ => ?_⟩)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖τ ((m : E) * u f)‖ ≤ R`. Rewrite using `[map_mul, map_natCast, norm_mul, Complex.norm_natCast, hR, pow_succ]`.

Conclude with `mul_le_mul hmT (hconj τ f) (norm_nonneg _) (by positivity)`. Use function extensionality and compare the values at `f`. Establish `: (m : E) ≠ 0` using `by exact_mod_cast hm.ne'`. Express the relevant statement in the definitionally equal form `(m : E) * u f / (m : E) = u f`. Clear the denominators using the available nonvanishing facts.

Establish `hfin : (φ '' (P : Set _)).Finite` using `P.finite_toSet.image φ`. Use `⟨hfin.subset hsub, ?_⟩` and prove the remaining obligations. Establish `h1 : Set.ncard {u : J → E | (∃ f₀, u f₀ = 1) ∧ (vecHt σ u : ℝ) ≤ T} ≤ P.card` using `(Set.ncard_le_ncard hsub hfin).trans ((Set.ncard_image_le P.finite_toSet).trans (Set.ncard_coe_finset P).le)`. Establish `h2 : (P.card : ℝ) ≤ T ^ (2 * Jc) * (C₀ * R ^ d) ^ Jc`. Establish `e1 : P.card = N₀ * hLf.toFinset.card ^ Jc`.

Simplify using `[P, Finset.card_product, Fintype.card_piFinset, hJc]`. Rewrite using `[e1]`. Use `push_cast`. Establish `e2 : (N₀ : ℝ) ≤ T ^ (2 * Jc)` using `Nat.floor_le (by positivity)`. Establish `e3 : (hLf.toFinset.card : ℝ) ≤ C₀ * R ^ d`.

Rewrite using `[← Set.ncard_eq_toFinset_card _ hLf]`. Conclude with `hLc`. Conclude with `mul_le_mul e2 (pow_le_pow_left₀ (by positivity) e3 _) (by positivity) (by positivity)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem count (hcm : IsCMExt F E σ) (J : Type) [Fintype J] : ∃ (C : ℝ) (c : ℕ), 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
    {u : J → E | (∃ f₀, u f₀ = 1) ∧ (vecHt σ u : ℝ) ≤ T}.Finite ∧
    (Set.ncard {u : J → E | (∃ f₀, u f₀ = 1) ∧ (vecHt σ u : ℝ) ≤ T} : ℝ) ≤ C * T ^ c := by
  classical
  obtain ⟨C₀, hC₀, hlat⟩ := GlobalTheory.T.integers_bounded_embeddings_count E
  set Jc := Fintype.card J with hJc
  set d := Module.finrank ℚ E with hd
  refine ⟨C₀ ^ Jc, 2 * Jc + (2 * Jc + 1) * d * Jc, pow_pos hC₀ _, fun T hT => ?_⟩
  set R : ℝ := T ^ (2 * Jc + 1) with hR
  have hR1 : 1 ≤ R := one_le_pow₀ hT
  obtain ⟨hLf, hLc⟩ := hlat R hR1
  set N₀ : ℕ := ⌊T ^ (2 * Jc)⌋₊ with hN₀
  let P : Finset (ℕ × (J → 𝓞 E)) := Finset.Icc 1 N₀ ×ˢ Fintype.piFinset fun _ : J => hLf.toFinset
  let φ : ℕ × (J → 𝓞 E) → J → E := fun p f => (p.2 f : E) / (p.1 : E)
  have hsub : {u : J → E | (∃ f₀, u f₀ = 1) ∧ (vecHt σ u : ℝ) ≤ T} ⊆ φ '' (P : Set _) := by
    rintro u ⟨⟨f₀, hu⟩, huT⟩
    obtain ⟨m, hm, hl, hi⟩ := denom_all hcm hu
    have hHi : 1 ≤ ∏ w : InfinitePlace F, locInf w u := Finset.one_le_prod' fun w _ => one_le_locInf w hu
    have hHf : 1 ≤ ∏ᶠ v, locFin σ v u := one_le_finprod' fun v => one_le_locFin v hu
    have hHf' : ((∏ᶠ v, locFin σ v u : ℝ≥0) : ℝ) ≤ T := by
      refine le_trans ?_ huT
      exact_mod_cast le_mul_of_one_le_left' hHi
    have hHi' : ((∏ w : InfinitePlace F, locInf w u : ℝ≥0) : ℝ) ≤ T := by
      refine le_trans ?_ huT
      exact_mod_cast le_mul_of_one_le_right' hHf
    have hmT : (m : ℝ) ≤ T ^ (2 * Jc) := by
      have h1 : (m : ℝ) ≤ ((∏ᶠ v, locFin σ v u : ℝ≥0) : ℝ) ^ (2 * Jc) := by exact_mod_cast hl
      exact h1.trans (pow_le_pow_left₀ (by positivity) hHf' _)
    have hconj : ∀ (τ : E →+* ℂ) f, ‖τ (u f)‖ ≤ T := by
      intro τ f
      obtain ⟨w, e, rfl⟩ := exists_embOver hcm τ
      have h1 := le_supInf w e u f
      have h2 := one_le_supInf w (u := u) hu
      have h3 : locInf w u ≤ ∏ w : InfinitePlace F, locInf w u :=
        Finset.single_le_prod' (f := fun w : InfinitePlace F => locInf w u) (fun w _ => one_le_locInf w hu) (Finset.mem_univ w)
      have h4 : ‖e.1 (u f)‖₊ ≤ locInf w u := by
        refine h1.trans ?_
        rw [locInf]
        exact le_self_pow₀ h2 two_ne_zero
      have h5 : (‖e.1 (u f)‖₊ : ℝ) ≤ ((∏ w : InfinitePlace F, locInf w u : ℝ≥0) : ℝ) := by exact_mod_cast h4.trans h3
      exact h5.trans hHi'
    refine ⟨(m, fun f => ⟨(m : E) * u f, hi f⟩), ?_, ?_⟩
    · refine Finset.mem_coe.2 (Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hm, Nat.le_floor hmT⟩,
        Fintype.mem_piFinset.2 fun f => hLf.mem_toFinset.2 fun τ => ?_⟩)
      change ‖τ ((m : E) * u f)‖ ≤ R
      rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast, hR, pow_succ]
      exact mul_le_mul hmT (hconj τ f) (norm_nonneg _) (by positivity)
    · funext f
      have : (m : E) ≠ 0 := by exact_mod_cast hm.ne'
      change (m : E) * u f / (m : E) = u f
      field_simp
  have hfin : (φ '' (P : Set _)).Finite := P.finite_toSet.image φ
  refine ⟨hfin.subset hsub, ?_⟩
  have h1 : Set.ncard {u : J → E | (∃ f₀, u f₀ = 1) ∧ (vecHt σ u : ℝ) ≤ T} ≤ P.card :=
    (Set.ncard_le_ncard hsub hfin).trans ((Set.ncard_image_le P.finite_toSet).trans (Set.ncard_coe_finset P).le)
  have h2 : (P.card : ℝ) ≤ T ^ (2 * Jc) * (C₀ * R ^ d) ^ Jc := by
    have e1 : P.card = N₀ * hLf.toFinset.card ^ Jc := by
      simp [P, Finset.card_product, Fintype.card_piFinset, hJc]
    rw [e1]
    push_cast
    have e2 : (N₀ : ℝ) ≤ T ^ (2 * Jc) := Nat.floor_le (by positivity)
    have e3 : (hLf.toFinset.card : ℝ) ≤ C₀ * R ^ d := by
      rw [← Set.ncard_eq_toFinset_card _ hLf]; exact hLc
    exact mul_le_mul e2 (pow_le_pow_left₀ (by positivity) e3 _) (by positivity) (by positivity)
  calc _ ≤ (P.card : ℝ) := by exact_mod_cast h1
    _ ≤ _ := h2
    _ = _ := by rw [hR]; ring

end GlobalTheory.CompanionTheory.GodementH
end

noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
variable {n : ℕ}

/- English proof (translation)
Rewrite using `[mnr, mnr, ← Matrix.det_mul]`. Use `congr 1`.
-/
theorem mnr_mul_det {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι (Fin n) R) (t : Matrix (Fin n) (Fin n) R) (f : Fin n → ι) :
    mnr (M * t) f = mnr M f * t.det := by
  rw [mnr, mnr, ← Matrix.det_mul]; congr 1

end GlobalTheory.CompanionTheory.GodementH
end

noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

abbrev Ix (n : ℕ) : Type := Fin n ⊕ Fin n

def pl (b g : GL (Ix n) E) : Matrix (Ix n) (Fin n) E :=
  ((b⁻¹).1 * (g⁻¹).1 : Matrix (Ix n) (Ix n) E) * (diagCols (Fin n) : Matrix (Ix n) (Fin n) E)

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> simp [incM, diagCols, Matrix.one_apply, apply_ite]`.
-/
theorem incM_diagCols : incM F (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) = diagCols (Fin n) := by
  ext i j
  rcases i with i | i <;> simp [incM, diagCols, Matrix.one_apply, apply_ite]

/- English proof (translation)
The claim follows from `Matrix.map_mul`.
-/
theorem incM_mul {l m o : Type} [Fintype m] (A : Matrix l m E) (B : Matrix m o E) : incM F (A * B) = incM F A * incM F B :=
  Matrix.map_mul

/- English proof (translation)
The claim follows from `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem incM_one {m : Type} [Fintype m] [DecidableEq m] : incM F (1 : Matrix m m E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Rewrite using `[← incM_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, incM_one]`.
-/
theorem incM_inv_mul {m : Type} [Fintype m] [DecidableEq m] (b : GL m E) : incM F (b⁻¹).1 * incM F b.1 = 1 := by
  rw [← incM_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, incM_one]

/- English proof (translation)
Rewrite using `[← incM_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, incM_one]`.
-/
theorem incM_mul_inv {m : Type} [Fintype m] [DecidableEq m] (b : GL m E) : incM F b.1 * incM F (b⁻¹).1 = 1 := by
  rw [← incM_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, incM_one]

/- English proof (translation)
Establish `hg : mat2 γ⁻¹ = incM F (g⁻¹).1`. Establish `: Matrix.GeneralLinearGroup.map (n` using `Ix n) (inclR (F := F) (E := E) (AF F)) g⁻¹ = (γ⁻¹).1 := by`. Rewrite using `[map_inv, hγ]`. Both sides reduce to the same expression. Conclude with `(congrArg Units.val this).symm`.

Establish `h1 : mat2 x * mat2 k⁻¹ = mat2 γ⁻¹ * mat2 p`. Establish `: x * k⁻¹ = γ⁻¹ * p`. Rewrite using `[mul_inv_eq_iff_eq_mul, mul_assoc, ← hy, inv_mul_cancel_left]`. Conclude with `congrArg mat2 this`. Establish `h2 : (incM F b.1).submatrix id Sum.inl = (diagCols (Fin n) : Matrix (Ix n) (Fin n) (AE F E)) * incM F t₀.1`.

Establish `: (incM F b.1).submatrix id Sum.inl = incM F b.1.toCols₁` using `rfl`. Rewrite using `[this, h0, incM_mul, incM_diagCols]`. Establish `h3 : inFrame b x * inFrame b k⁻¹ = incM F (b⁻¹).1 * (mat2 x * mat2 k⁻¹) * incM F b.1`. Unfold `inFrame`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [incM_mul_inv, Matrix.mul_one]; simp only [Matrix.mul_assoc]`. Establish `h4 : ∀ (A : Matrix (Ix n) (Ix n) (AE F E)), (A * incM F b.1).submatrix id Sum.inl = A * (incM F b.1).submatrix id Sum.inl`. Introduce `A`. Use extensionality with `i j`.

Simplify using `[Matrix.mul_apply]`. Rewrite using `[h3, h4, h2, h1, hg, pl, incM_mul, incM_mul, incM_diagCols]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by`.

Establish `hp' : mat2 p * (diagCols (Fin n) : Matrix (Ix n) (Fin n) (AE F E)) = (diagCols (Fin n) : Matrix (Ix n) (Fin n) (AE F E)) * t.1` using `hp`. Rewrite using `[← hp']`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem frame_identity {b g : GL (Ix n) E} {t₀ : GL (Fin n) E} (h0 : b.1.toCols₁ = (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) * (t₀.1 : Matrix (Fin n) (Fin n) E)) {γ x p k : G2 σ Y}
    {t : GL (Fin n) (AE F E)} (hγ : Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) g = γ.1)
    (hp : IsPar p t) (hy : γ * x = p * k) :
    incM F (pl b g) * (t.1 * incM F t₀.1) = ((inFrame b x * inFrame b k⁻¹).submatrix id Sum.inl) := by
  have hg : mat2 γ⁻¹ = incM F (g⁻¹).1 := by
    have : Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) g⁻¹ = (γ⁻¹).1 := by
      rw [map_inv, hγ]; rfl
    exact (congrArg Units.val this).symm
  have h1 : mat2 x * mat2 k⁻¹ = mat2 γ⁻¹ * mat2 p := by
    have : x * k⁻¹ = γ⁻¹ * p := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hy, inv_mul_cancel_left]
    exact congrArg mat2 this
  have h2 : (incM F b.1).submatrix id Sum.inl = (diagCols (Fin n) : Matrix (Ix n) (Fin n) (AE F E)) * incM F t₀.1 := by
    have : (incM F b.1).submatrix id Sum.inl = incM F b.1.toCols₁ := rfl
    rw [this, h0, incM_mul, incM_diagCols]
  have h3 : inFrame b x * inFrame b k⁻¹ = incM F (b⁻¹).1 * (mat2 x * mat2 k⁻¹) * incM F b.1 := by
    unfold inFrame
    calc _ = incM F (b⁻¹).1 * mat2 x * (incM F b.1 * incM F (b⁻¹).1) * mat2 k⁻¹ * incM F b.1 := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [incM_mul_inv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have h4 : ∀ (A : Matrix (Ix n) (Ix n) (AE F E)), (A * incM F b.1).submatrix id Sum.inl = A * (incM F b.1).submatrix id Sum.inl := by
    intro A; ext i j; simp [Matrix.mul_apply]
  rw [h3, h4, h2, h1, hg, pl, incM_mul, incM_mul, incM_diagCols]
  calc _ = incM F (b⁻¹).1 * incM F (g⁻¹).1 * ((diagCols (Fin n) : Matrix (Ix n) (Fin n) (AE F E)) * t.1) * incM F t₀.1 := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        have hp' : mat2 p * (diagCols (Fin n) : Matrix (Ix n) (Fin n) (AE F E)) = (diagCols (Fin n) : Matrix (Ix n) (Fin n) (AE F E)) * t.1 := hp
        rw [← hp']; simp only [Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.GodementH
end

noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

/- English proof (translation)
Simplify using `only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const, Finset.card_univ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_widePullback_of_iteratedLine {ι : Type} [Fintype ι] (N : ℝ≥0) (h : ι → ℝ≥0) (n : ℕ) :
    ∏ w, (N * h w ^ n) ^ 2 = N ^ (2 * Fintype.card ι) * (∏ w, h w) ^ (2 * n) := by
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const, Finset.card_univ]
  ring

/- English proof (translation)
Take `⟨t₀, h0⟩` from `h0`. Use `set bA := Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) b with hbA`. Use `⟨(n.factorial : ℝ≥0) ^ (2 * Fintype.card (InfinitePlace F)) * (heightGL F bA ^ 2) ^ (2 * n), ?_⟩` and prove the remaining obligations. Introduce `γ g hγ f₀ hf₀ x`. Take `⟨p, t, hp, k, hk, hy⟩` from `ha.iwa (γ * x)`.

Establish `hval : a (γ * x) = absE F E (Matrix.GeneralLinearGroup.det t)` using `by rw [hy]; exact ha.val p t hp k hk`. Use `set M := pl b g with hM`. Use `set u : (Fin n → Ix n) → E := fun f => mnr M f / mnr M f₀ with hu`. Establish `hu1 : u f₀ = 1` using `div_self hf₀`. Set `c : Eˣ` to `Matrix.GeneralLinearGroup.det t₀ * Units.mk0 (mnr M f₀) hf₀`.

Set `δ : (AE F E)ˣ` to `Matrix.GeneralLinearGroup.det t * Units.map (inclR (F := F) (AF F)).toMonoidHom c`. Set `X : GL (Ix n) (AE F E)` to `bA⁻¹ * x.1 * bA`. Establish `hX : X.1 = inFrame b x`. Establish `: (bA⁻¹).1 = incM F (b⁻¹).1`. Establish `: bA⁻¹ = Matrix.GeneralLinearGroup.map (n` using `Ix n) (inclR (F := F) (E := E) (AF F)) b⁻¹ := by rw [map_inv]`.

Rewrite using `[this]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(bA⁻¹).1 * x.1.1 * bA.1 = _`. Rewrite using `[this]`. Both sides reduce to the same expression.

Set `κ` to `inFrame b k⁻¹`. Set `z : (Fin n → Ix n) → AE F E` to `fun f => ((X.1 * κ).submatrix f Sum.inl).det`. Establish `hz : ∀ f, z f = inclR (F` using `F) (AF F) (u f) * δ.1 := by`. Introduce `f`. Establish `hid` using `frame_identity h0 hγ hp hy`.

Establish `e1 : z f = mnr ((inFrame b x * inFrame b k⁻¹).submatrix id Sum.inl) f`. Express the relevant statement in the definitionally equal form `((X.1 * κ).submatrix f Sum.inl).det = _`. Rewrite using `[hX]`. Both sides reduce to the same expression. Establish `e2 : mnr (incM F M) f = inclR (F` using `F) (AF F) (mnr M f) := by`.

Rewrite using `[mnr, mnr, RingHom.map_det]`. Both sides reduce to the same expression. Establish `e3 : (t.1 * incM F t₀.1).det = (Matrix.GeneralLinearGroup.det t).1 * inclR (F` using `F) (AF F) t₀.1.det := by`. Rewrite using `[Matrix.det_mul, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Both sides reduce to the same expression.

Rewrite using `[e1, ← hid, mnr_mul_det, e2, e3]`. Establish `e4 : mnr M f = u f * mnr M f₀`. Simplify using `only [hu]`. Clear the denominators using the available nonvanishing facts. Express the relevant statement in the definitionally equal form `_ = _ * ((Matrix.GeneralLinearGroup.det t).1 * inclR (F := F) (AF F) (t₀.1.det * mnr M f₀))`.

Rewrite using `[e4, map_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hδ : absE F E δ = absE F E (Matrix.GeneralLinearGroup.det t)`. Simplify using `only [δ, map_mul]`. Rewrite using `[GlobalTheory.Doubling.absE_inclR, mul_one]`.

Establish `hmain` using `absE_mul_vecHt_le hcm B.emb hu1 δ z hz (fun w => (n.factorial : ℝ≥0) * htInf F w (Formalism.UG.bc (compInf F E w) X) ^ n) (fun v => htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n) ((finite_mulSupport_htFin F X).subset (Function.mulSupport_pow _ _)) (fun w f => GlobalTheory.T.a …`. Rewrite `hmain` using `[hδ]`. Establish `hprod : (∏ w, ((n.factorial : ℝ≥0) * htInf F w (Formalism.UG.bc (compInf F E w) X) ^ n) ^ 2) * ∏ᶠ v, (htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n) ^ 2 = (n.factorial : ℝ≥0) ^ (2 * Fintype.card (InfinitePlace F)) * heightGL F X ^ (2 * n)`. Establish `h1 : ∏ᶠ v, (htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n) ^ 2 = (∏ᶠ v, htFin F v (Formalism.UG.bc (compFin F E v) X)) ^ (2 * n)`. Rewrite using `[finprod_pow (finite_mulSupport_htFin F X)]`.

Simplify using `only [← pow_mul, mul_comm]`. Rewrite using `[exists_widePullback_of_iteratedLine, h1, heightGL, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `hX2 : heightGL F X ≤ heightGL F bA ^ 2 * ht2 x`. Combine the equalities or inequalities in the displayed calculation.

Establish `hfin : absE F E (Matrix.GeneralLinearGroup.det t) * vecHt σ u ≤ (n.factorial : ℝ≥0) ^ (2 * Fintype.card (InfinitePlace F)) * (heightGL F bA ^ 2) ^ (2 * n) * ht2 x ^ (2 * n)`. Use `hmain.trans ?_` and prove the remaining obligations. Rewrite using `[hprod, mul_assoc, ← mul_pow]`. Conclude with `mul_le_mul_right (pow_le_pow_left' hX2 _) _`. Rewrite using `[hval]`.

Conclude with `hfin` after adjusting the coercions.
-/
theorem key_bound (hcm : IsCMExt F E σ) {B : Base F E} {b : GL (Ix n) E} {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ}
    (h0 : ∃ t₀ : GL (Fin n) E, b.1.toCols₁ = (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) * (t₀.1 : Matrix (Fin n) (Fin n) E))
    (hK : IsStdK (σ := σ) (Y := Y) B b K) (ha : IsHgt K a) :
    ∃ C : ℝ≥0, ∀ (γ : G2 σ Y) (g : GL (Ix n) E),
      Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) g = γ.1 →
      ∀ f₀ : Fin n → Ix n, mnr (pl b g) f₀ ≠ 0 → ∀ x : G2 σ Y,
      a (γ * x) * (vecHt σ (fun f => mnr (pl b g) f / mnr (pl b g) f₀) : ℝ) ≤ C * (ht2 x : ℝ) ^ (2 * n) := by
  obtain ⟨t₀, h0⟩ := h0
  set bA := Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) b with hbA
  refine ⟨(n.factorial : ℝ≥0) ^ (2 * Fintype.card (InfinitePlace F)) * (heightGL F bA ^ 2) ^ (2 * n), ?_⟩
  intro γ g hγ f₀ hf₀ x
  obtain ⟨p, t, hp, k, hk, hy⟩ := ha.iwa (γ * x)
  have hval : a (γ * x) = absE F E (Matrix.GeneralLinearGroup.det t) := by rw [hy]; exact ha.val p t hp k hk
  set M := pl b g with hM
  set u : (Fin n → Ix n) → E := fun f => mnr M f / mnr M f₀ with hu
  have hu1 : u f₀ = 1 := div_self hf₀
  let c : Eˣ := Matrix.GeneralLinearGroup.det t₀ * Units.mk0 (mnr M f₀) hf₀
  let δ : (AE F E)ˣ := Matrix.GeneralLinearGroup.det t * Units.map (inclR (F := F) (AF F)).toMonoidHom c
  let X : GL (Ix n) (AE F E) := bA⁻¹ * x.1 * bA
  have hX : X.1 = inFrame b x := by
    have : (bA⁻¹).1 = incM F (b⁻¹).1 := by
      have : bA⁻¹ = Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) b⁻¹ := by rw [map_inv]
      rw [this]; rfl
    change (bA⁻¹).1 * x.1.1 * bA.1 = _
    rw [this]; rfl
  let κ := inFrame b k⁻¹
  let z : (Fin n → Ix n) → AE F E := fun f => ((X.1 * κ).submatrix f Sum.inl).det
  have hz : ∀ f, z f = inclR (F := F) (AF F) (u f) * δ.1 := by
    intro f
    have hid := frame_identity h0 hγ hp hy
    have e1 : z f = mnr ((inFrame b x * inFrame b k⁻¹).submatrix id Sum.inl) f := by
      change ((X.1 * κ).submatrix f Sum.inl).det = _
      rw [hX]; rfl
    have e2 : mnr (incM F M) f = inclR (F := F) (AF F) (mnr M f) := by
      rw [mnr, mnr, RingHom.map_det]; rfl
    have e3 : (t.1 * incM F t₀.1).det = (Matrix.GeneralLinearGroup.det t).1 * inclR (F := F) (AF F) t₀.1.det := by
      rw [Matrix.det_mul, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    rw [e1, ← hid, mnr_mul_det, e2, e3]
    have e4 : mnr M f = u f * mnr M f₀ := by
      simp only [hu]; field_simp
    change _ = _ * ((Matrix.GeneralLinearGroup.det t).1 * inclR (F := F) (AF F) (t₀.1.det * mnr M f₀))
    rw [e4, map_mul, map_mul]
    ring
  have hδ : absE F E δ = absE F E (Matrix.GeneralLinearGroup.det t) := by
    simp only [δ, map_mul]
    rw [GlobalTheory.Doubling.absE_inclR, mul_one]
  have hmain := absE_mul_vecHt_le hcm B.emb hu1 δ z hz
    (fun w => (n.factorial : ℝ≥0) * htInf F w (Formalism.UG.bc (compInf F E w) X) ^ n)
    (fun v => htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n)
    ((finite_mulSupport_htFin F X).subset (Function.mulSupport_pow _ _))
    (fun w f => GlobalTheory.T.archimedean_minor_height_bound F E n (Ix n) w (B.emb w) X κ (((hK k⁻¹).1 (inv_mem hk)).1 w) f Sum.inl)
    (fun v f => GlobalTheory.T.finite_place_minor_height_bound F E n (Ix n) v X κ (fun i j => GlobalTheory.T.standard_compact_entries_integral F E σ n Y B b K hK _ (inv_mem hk) v i j) f Sum.inl)
  rw [hδ] at hmain
  have hprod : (∏ w, ((n.factorial : ℝ≥0) * htInf F w (Formalism.UG.bc (compInf F E w) X) ^ n) ^ 2) *
      ∏ᶠ v, (htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n) ^ 2 =
      (n.factorial : ℝ≥0) ^ (2 * Fintype.card (InfinitePlace F)) * heightGL F X ^ (2 * n) := by
    have h1 : ∏ᶠ v, (htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n) ^ 2 =
        (∏ᶠ v, htFin F v (Formalism.UG.bc (compFin F E v) X)) ^ (2 * n) := by
      rw [finprod_pow (finite_mulSupport_htFin F X)]
      simp only [← pow_mul, mul_comm]
    rw [exists_widePullback_of_iteratedLine, h1, heightGL, mul_pow]
    ring
  have hX2 : heightGL F X ≤ heightGL F bA ^ 2 * ht2 x := by
    calc heightGL F X ≤ heightGL F (bA⁻¹ * x.1) * heightGL F bA := heightGL_mul_le F _ _
      _ ≤ heightGL F bA⁻¹ * heightGL F x.1 * heightGL F bA := mul_le_mul_left (heightGL_mul_le F _ _) _
      _ = _ := by rw [heightGL_inv, ht2]; ring
  have hfin : absE F E (Matrix.GeneralLinearGroup.det t) * vecHt σ u ≤
      (n.factorial : ℝ≥0) ^ (2 * Fintype.card (InfinitePlace F)) * (heightGL F bA ^ 2) ^ (2 * n) * ht2 x ^ (2 * n) := by
    refine hmain.trans ?_
    rw [hprod, mul_assoc, ← mul_pow]
    exact mul_le_mul_right (pow_le_pow_left' hX2 _) _
  rw [hval]
  exact_mod_cast hfin

/- English proof (translation)
Establish `e1 : (g'⁻¹).1 * (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) = (g⁻¹).1 * (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) * c.1`. Use `congrArg (fun A => b.1 * A) h` as an intermediate fact. Simplify `this` using `[pl, ← Matrix.mul_assoc, ← Units.val_mul]`. Establish `e2 : (g * g'⁻¹).1 * (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) = (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) * c.1`. Rewrite using `[Units.val_mul, Matrix.mul_assoc, e1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel]`.

Simplify using the standard rewrite rules. Establish `e3 : mat2 (γ * γ'⁻¹) = incM F (g * g'⁻¹).1`. Establish `: Matrix.GeneralLinearGroup.map (n` using `Ix n) (inclR (F := F) (E := E) (AF F)) (g * g'⁻¹) = (γ * γ'⁻¹).1 := by`. Rewrite using `[map_mul, map_inv, hγ, hγ']`. Both sides reduce to the same expression.

Conclude with `(congrArg Units.val this).symm`. Establish `e4` using `congrArg (incM F) e2`. Rewrite `e4` using `[incM_mul, incM_mul, incM_diagCols]`. Unfold `IsPar`. Rewrite using `[e3]`.

Conclude with `e4`.
-/
theorem isPar_of_pl {b g g' : GL (Ix n) E} {c : GL (Fin n) E} {γ γ' : G2 σ Y}
    (hγ : Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) g = γ.1)
    (hγ' : Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) g' = γ'.1)
    (h : pl b g' = pl b g * c.1) :
    IsPar (γ * γ'⁻¹) (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)) c) := by
  have e1 : (g'⁻¹).1 * (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) = (g⁻¹).1 * (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) * c.1 := by
    have := congrArg (fun A => b.1 * A) h
    simpa [pl, ← Matrix.mul_assoc, ← Units.val_mul] using this
  have e2 : (g * g'⁻¹).1 * (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) = (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) * c.1 := by
    rw [Units.val_mul, Matrix.mul_assoc, e1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel]
    simp
  have e3 : mat2 (γ * γ'⁻¹) = incM F (g * g'⁻¹).1 := by
    have : Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) (g * g'⁻¹) = (γ * γ'⁻¹).1 := by
      rw [map_mul, map_inv, hγ, hγ']; rfl
    exact (congrArg Units.val this).symm
  have e4 := congrArg (incM F) e2
  rw [incM_mul, incM_mul, incM_diagCols] at e4
  unfold IsPar
  rw [e3]
  exact e4

end GlobalTheory.CompanionTheory.GodementH
end

noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n Y r s hB hn hY b K a hb hK ha`. Establish `hcm : IsCMExt F E σ` using `hB.cm`. Take `⟨C, hC⟩` from `key_bound hcm hb.2 hK ha`. Establish `hrat : ∀ q : Cos σ Y, ∃ g : GL (Ix n) E, Matrix.GeneralLinearGroup.map (n` using `Ix n) (inclR (F := F) (E := E) (AF F)) g = (Quotient.out q).1.1 := fun q => by`. Take `⟨g, hg⟩` from `Subgroup.mem_subgroupOf.1 (Quotient.out q).2`.

Conclude with `⟨g, hg⟩`. Use `choose g hg using hrat`. Establish `hnz : ∀ q, ∃ f, mnr (pl b (g q)) f ≠ 0` using `fun q => by`. Establish `hP : ∃ P : Matrix (Fin n) (Ix n) E, P * (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) = 1` using `⟨Matrix.fromCols 1 0, by rw [diagCols, Matrix.fromCols_mul_fromRows]; simp⟩`. Take `⟨P, hP⟩` from `hP`.

Establish `hg1 : ((g q).1 : Matrix (Ix n) (Ix n) E) * ((g q)⁻¹).1 = 1` using `by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `hb1 : (b.1 : Matrix (Ix n) (Ix n) E) * (b⁻¹).1 = 1` using `by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]`. Use `GlobalTheory.T.left_invertible_exists_nonzero_minor E (Ix n) n (pl b (g q)) ((P * ((g q).1 : Matrix (Ix n) (Ix n) E)) * (b.1 : Matrix (Ix n) (Ix n) E)) ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hg1, Matrix.mul_one, hP]`.

Use `choose f₀ hf₀ using hnz`. Set `u : Cos σ Y → (Fin n → Ix n) → E` to `fun q f => mnr (pl b (g q)) f / mnr (pl b (g q)) (f₀ q)`. Establish `hu1 : ∀ q, u q (f₀ q) = 1` using `fun q => div_self (hf₀ q)`. Establish `hinj : Function.Injective u`. Introduce `q q' e`.

Take `⟨c, hc⟩` from `GlobalTheory.T.plucker_minors_determine_column_space E (Ix n) n _ _ _ _ (hf₀ q) (hf₀ q') (fun f => congrFun e f)`. Establish `hp` using `isPar_of_pl (hg q) (hg q') hc`. Establish `: (Quotient.mk _ (Quotient.out q') : Cos σ Y) = Quotient.mk _ (Quotient.out q)` using `cos_eq.2 (Subgroup.subset_closure ⟨_, hp⟩)`. Rewrite `this` using `[Quotient.out_eq, Quotient.out_eq]`. Conclude with `this.symm`.

Take `⟨C₁, c, hC₁, hcount⟩` from `count hcm (Fin n → Ix n) (σ := σ)`. Set `h : Cos σ Y → ℝ` to `fun q => vecHt σ (u q)`. Establish `h1 : ∀ q, 1 ≤ h q` using `fun q => by`. Use `one_le_vecHt (σ := σ) (hu1 q)` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Establish `hcnt : ∀ T : ℝ, 1 ≤ T → {q | h q ≤ T}.Finite ∧ (Set.ncard {q | h q ≤ T} : ℝ) ≤ C₁ * T ^ c`. Introduce `T hT`. Take `⟨hfin, hle⟩` from `hcount T hT`. Establish `hmaps : Set.MapsTo u {q | h q ≤ T} {u : (Fin n → Ix n) → E | (∃ f₀, u f₀ = 1) ∧ (vecHt σ u : ℝ) ≤ T}` using `fun q hq => ⟨⟨f₀ q, hu1 q⟩, hq⟩`. Use `⟨Set.Finite.of_injOn hmaps hinj.injOn hfin, le_trans ?_ hle⟩` and prove the remaining obligations.

Conclude with `Set.ncard_le_ncard_of_injOn u hmaps hinj.injOn hfin` after adjusting the coercions. Establish `a_nonneg : ∀ y, 0 ≤ a y` using `fun y => by`. Take `⟨p, t, hp, k, hk, rfl⟩` from `ha.iwa y`. Rewrite using `[ha.val p t hp k hk]`. Conclude with `NNReal.coe_nonneg _`.

Use `⟨c, fun s' hs' => ?_⟩` and prove the remaining obligations. Establish `hs0 : 0 < s'` using `lt_of_le_of_lt (Nat.cast_nonneg c) hs'`. Establish `hsum : Summable fun q => h q ^ (-s')` using `GlobalTheory.T.summable_height_pow_of_polynomial_count _ h h1 C₁ c hcnt s' hs'`. Establish `hterm : ∀ (x : G2 σ Y) (q : Cos σ Y), a ((Quotient.out q).1 * x) ^ s' ≤ ((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) ^ s' * h q ^ (-s')`. Introduce `x q`.

Establish `hb1` using `hC (Quotient.out q).1 (g q) (hg q) (f₀ q) (hf₀ q) x`. Establish `hpos : 0 < h q` using `lt_of_lt_of_le one_pos (h1 q)`. Establish `hb2 : a ((Quotient.out q).1 * x) ≤ ((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) * (h q)⁻¹`. Rewrite using `[← div_eq_mul_inv, le_div_iff₀ hpos]`. Conclude with `hb1`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hpos.le, Real.rpow_neg hpos.le]`. Use `⟨(C : ℝ) ^ s' * ∑' q, h q ^ (-s'), ⌈2 * n * s'⌉₊, fun x => ?_⟩` and prove the remaining obligations. Establish `hS : Summable fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ s'` using `Summable.of_nonneg_of_le (fun q => Real.rpow_nonneg (a_nonneg _) _) (hterm x) (hsum.mul_left _)`. Use `⟨hS, ?_⟩` and prove the remaining obligations.

Establish `hx1 : (1 : ℝ) ≤ ht2 x` using `by exact_mod_cast one_le_heightGL F x.1`. Establish `hx0 : (0 : ℝ) ≤ ht2 x` using `by positivity`. Establish `hpow : ((ht2 x : ℝ) ^ (2 * n)) ^ s' ≤ (ht2 x : ℝ) ^ ⌈2 * n * s'⌉₊`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hx0, ← Real.rpow_natCast]`. Use `Real.rpow_le_rpow_of_exponent_le hx1 ?_` and prove the remaining obligations.

Use `push_cast`. Conclude with `Nat.le_ceil _`. Establish `hT : 0 ≤ ∑' q, h q ^ (-s')` using `tsum_nonneg fun q => Real.rpow_nonneg (lt_of_lt_of_le one_pos (h1 q)).le _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[tsum_mul_left, Real.mul_rpow (by positivity) (by positivity)]`.

Use `_ ≤ (C : ℝ) ^ s' * (ht2 x : ℝ) ^ ⌈2 * n * s'⌉₊ * ∑' q, h q ^ (-s') := by gcongr`. Use `_ = _ := by ring`.
-/
theorem godement_sum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∃ σ₀ : ℝ, ∀ σ' : ℝ, σ₀ < σ' → ∃ (C : ℝ) (N : ℕ), ∀ x : G2 σ Y, Summable (fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ σ') ∧ ∑' q : Cos σ Y, a ((Quotient.out q).1 * x) ^ σ' ≤ C * (ht2 x : ℝ) ^ N := by
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY b K a hb hK ha
  have hcm : IsCMExt F E σ := hB.cm
  obtain ⟨C, hC⟩ := key_bound hcm hb.2 hK ha
  have hrat : ∀ q : Cos σ Y, ∃ g : GL (Ix n) E,
      Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) g = (Quotient.out q).1.1 := fun q => by
    obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.1 (Quotient.out q).2
    exact ⟨g, hg⟩
  choose g hg using hrat
  have hnz : ∀ q, ∃ f, mnr (pl b (g q)) f ≠ 0 := fun q => by
    have hP : ∃ P : Matrix (Fin n) (Ix n) E, P * (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) = 1 :=
      ⟨Matrix.fromCols 1 0, by rw [diagCols, Matrix.fromCols_mul_fromRows]; simp⟩
    obtain ⟨P, hP⟩ := hP
    have hg1 : ((g q).1 : Matrix (Ix n) (Ix n) E) * ((g q)⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hb1 : (b.1 : Matrix (Ix n) (Ix n) E) * (b⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine GlobalTheory.T.left_invertible_exists_nonzero_minor E (Ix n) n (pl b (g q)) ((P * ((g q).1 : Matrix (Ix n) (Ix n) E)) * (b.1 : Matrix (Ix n) (Ix n) E)) ?_
    calc (P * ((g q).1 : Matrix (Ix n) (Ix n) E)) * (b.1 : Matrix (Ix n) (Ix n) E) * pl b (g q)
        = P * ((g q).1 : Matrix (Ix n) (Ix n) E) * ((b.1 : Matrix (Ix n) (Ix n) E) * (b⁻¹).1) * ((g q)⁻¹).1 *
          (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) := by simp only [pl, Matrix.mul_assoc]
      _ = P * (((g q).1 : Matrix (Ix n) (Ix n) E) * ((g q)⁻¹).1) *
          (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) := by rw [hb1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hg1, Matrix.mul_one, hP]
  choose f₀ hf₀ using hnz
  let u : Cos σ Y → (Fin n → Ix n) → E := fun q f => mnr (pl b (g q)) f / mnr (pl b (g q)) (f₀ q)
  have hu1 : ∀ q, u q (f₀ q) = 1 := fun q => div_self (hf₀ q)
  have hinj : Function.Injective u := by
    intro q q' e
    obtain ⟨c, hc⟩ := GlobalTheory.T.plucker_minors_determine_column_space E (Ix n) n _ _ _ _ (hf₀ q) (hf₀ q') (fun f => congrFun e f)
    have hp := isPar_of_pl (hg q) (hg q') hc
    have : (Quotient.mk _ (Quotient.out q') : Cos σ Y) = Quotient.mk _ (Quotient.out q) :=
      cos_eq.2 (Subgroup.subset_closure ⟨_, hp⟩)
    rw [Quotient.out_eq, Quotient.out_eq] at this
    exact this.symm
  obtain ⟨C₁, c, hC₁, hcount⟩ := count hcm (Fin n → Ix n) (σ := σ)
  let h : Cos σ Y → ℝ := fun q => vecHt σ (u q)
  have h1 : ∀ q, 1 ≤ h q := fun q => by
    have := one_le_vecHt (σ := σ) (hu1 q)
    exact_mod_cast this
  have hcnt : ∀ T : ℝ, 1 ≤ T → {q | h q ≤ T}.Finite ∧ (Set.ncard {q | h q ≤ T} : ℝ) ≤ C₁ * T ^ c := by
    intro T hT
    obtain ⟨hfin, hle⟩ := hcount T hT
    have hmaps : Set.MapsTo u {q | h q ≤ T} {u : (Fin n → Ix n) → E | (∃ f₀, u f₀ = 1) ∧ (vecHt σ u : ℝ) ≤ T} :=
      fun q hq => ⟨⟨f₀ q, hu1 q⟩, hq⟩
    refine ⟨Set.Finite.of_injOn hmaps hinj.injOn hfin, le_trans ?_ hle⟩
    exact_mod_cast Set.ncard_le_ncard_of_injOn u hmaps hinj.injOn hfin
  have a_nonneg : ∀ y, 0 ≤ a y := fun y => by
    obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa y
    rw [ha.val p t hp k hk]; exact NNReal.coe_nonneg _
  refine ⟨c, fun s' hs' => ?_⟩
  have hs0 : 0 < s' := lt_of_le_of_lt (Nat.cast_nonneg c) hs'
  have hsum : Summable fun q => h q ^ (-s') := GlobalTheory.T.summable_height_pow_of_polynomial_count _ h h1 C₁ c hcnt s' hs'
  have hterm : ∀ (x : G2 σ Y) (q : Cos σ Y), a ((Quotient.out q).1 * x) ^ s' ≤
      ((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) ^ s' * h q ^ (-s') := by
    intro x q
    have hb1 := hC (Quotient.out q).1 (g q) (hg q) (f₀ q) (hf₀ q) x
    have hpos : 0 < h q := lt_of_lt_of_le one_pos (h1 q)
    have hb2 : a ((Quotient.out q).1 * x) ≤ ((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) * (h q)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact hb1
    calc _ ≤ (((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) * (h q)⁻¹) ^ s' := Real.rpow_le_rpow (a_nonneg _) hb2 hs0.le
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hpos.le, Real.rpow_neg hpos.le]
  refine ⟨(C : ℝ) ^ s' * ∑' q, h q ^ (-s'), ⌈2 * n * s'⌉₊, fun x => ?_⟩
  have hS : Summable fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ s' :=
    Summable.of_nonneg_of_le (fun q => Real.rpow_nonneg (a_nonneg _) _) (hterm x) (hsum.mul_left _)
  refine ⟨hS, ?_⟩
  have hx1 : (1 : ℝ) ≤ ht2 x := by exact_mod_cast one_le_heightGL F x.1
  have hx0 : (0 : ℝ) ≤ ht2 x := by positivity
  have hpow : ((ht2 x : ℝ) ^ (2 * n)) ^ s' ≤ (ht2 x : ℝ) ^ ⌈2 * n * s'⌉₊ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
    push_cast
    exact Nat.le_ceil _
  have hT : 0 ≤ ∑' q, h q ^ (-s') := tsum_nonneg fun q => Real.rpow_nonneg (lt_of_lt_of_le one_pos (h1 q)).le _
  calc ∑' q : Cos σ Y, a ((Quotient.out q).1 * x) ^ s' ≤ ∑' q, ((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) ^ s' * h q ^ (-s') :=
        hS.tsum_le_tsum (hterm x) (hsum.mul_left _)
    _ = (C : ℝ) ^ s' * ((ht2 x : ℝ) ^ (2 * n)) ^ s' * ∑' q, h q ^ (-s') := by
        rw [tsum_mul_left, Real.mul_rpow (by positivity) (by positivity)]
    _ ≤ (C : ℝ) ^ s' * (ht2 x : ℝ) ^ ⌈2 * n * s'⌉₊ * ∑' q, h q ^ (-s') := by gcongr
    _ = _ := by ring

end GlobalTheory.CompanionTheory.GodementH
end
