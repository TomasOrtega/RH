import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorGoodPoint
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFrameGraphGeneric
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularOffHypersurface
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

/- English proof (translation)
Take `⟨A, O, V, g, hO, hV, hqV, hg, hAg, hYV⟩` from `h`. Use `⟨A, O ∩ g ⁻¹' U, V ∩ U, g, hg.continuousOn.isOpen_inter_preimage hO hU, hV.inter hU, ⟨hqV, hqU⟩, fun y hy => hg y hy.1, fun y hy => hAg y hy.1, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.image_inter_preimage, ← hYV]`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hx, hxV, hxU⟩`. Establish `hx' : x ∈ Y ∩ U` using `by rw [← hYU]; exact ⟨hx, hxU⟩`. Conclude with `⟨⟨hx'.1, hxV⟩, hxU⟩`. Introduce and unpack `⟨⟨hx, hxV⟩, hxU⟩`. Establish `hx' : x ∈ Y' ∩ U` using `by rw [hYU]; exact ⟨hx, hxU⟩`.

Conclude with `⟨hx'.1, hxV, hxU⟩`.
-/
theorem graphChart_of_eq_on_open {n d : ℕ} {Y Y' U : Set (Fin n → ℂ)} {q : Fin n → ℂ}
    (hU : IsOpen U) (hqU : q ∈ U) (hYU : Y' ∩ U = Y ∩ U)
    (h : ∃ (A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
      (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen O ∧ IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ g O ∧
        (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O) :
    ∃ (A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
      (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen O ∧ IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ g O ∧
        (∀ y ∈ O, A (g y) = y) ∧ Y' ∩ V = g '' O := by
  obtain ⟨A, O, V, g, hO, hV, hqV, hg, hAg, hYV⟩ := h
  refine ⟨A, O ∩ g ⁻¹' U, V ∩ U, g, hg.continuousOn.isOpen_inter_preimage hO hU, hV.inter hU, ⟨hqV, hqU⟩,
    fun y hy => hg y hy.1, fun y hy => hAg y hy.1, ?_⟩
  rw [Set.image_inter_preimage, ← hYV]
  ext x
  constructor
  · rintro ⟨hx, hxV, hxU⟩
    have hx' : x ∈ Y ∩ U := by rw [← hYU]; exact ⟨hx, hxU⟩
    exact ⟨⟨hx'.1, hxV⟩, hxU⟩
  · rintro ⟨⟨hx, hxV⟩, hxU⟩
    have hx' : x ∈ Y' ∩ U := by rw [hYU]; exact ⟨hx, hxU⟩
    exact ⟨hx'.1, hxV, hxU⟩

/- English proof (translation)
Establish `hPW : V ≤ W` using `le_sup_left.trans hW.1.2`. Establish `hfW : f ∈ W` using `hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))`. Establish `hq : W.map (Ideal.Quotient.mk V) ∈ (Ideal.span {Ideal.Quotient.mk V f}).minimalPrimes`. Establish `e : Ideal.span {Ideal.Quotient.mk V f} = (Ideal.span {f}).map (Ideal.Quotient.mk V)`. Rewrite using `[Ideal.map_span, Set.image_singleton]`.

Rewrite using `[e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm]`. Conclude with `⟨W, hW, rfl⟩`. Establish `: (W.map (Ideal.Quotient.mk V)).IsPrime` using `hq.1.1`. Establish `: (Ideal.span {Ideal.Quotient.mk V f}).IsPrincipal` using `⟨⟨_, rfl⟩⟩`. Establish `hh : (W.map (Ideal.Quotient.mk V)).height = 1`.

Use `le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq) ?_` and prove the remaining obligations. Rewrite using `[Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]`. Introduce `h0`. Establish `: Ideal.Quotient.mk V f ∈ W.map (Ideal.Quotient.mk V)` using `Ideal.mem_map_of_mem _ hfW`. Rewrite `this` using `[h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hf this`. Establish `: IsDomain (MvPolynomial (Fin n) ℂ ⧸ V)` using `Ideal.Quotient.isDomain V`. Establish `: Algebra.FiniteType ℂ (MvPolynomial (Fin n) ℂ ⧸ V)` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ V) (Ideal.Quotient.mkₐ_surjective ℂ V)`. Establish `: IsNoetherianRing (MvPolynomial (Fin n) ℂ ⧸ V)` using `Algebra.FiniteType.isNoetherianRing ℂ _`. Establish `: FiniteRingKrullDim (MvPolynomial (Fin n) ℂ ⧸ V)` using `finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨fun h => by`.

Establish `h0` using `ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ V)`. Rewrite `h0` using `[h]`. Conclude with `absurd h0 (by simp), hfin⟩`. Take `⟨s, hs⟩` from `ReciprocityTheory.ChartRestriction.G.Geo.DimF.exists_height_of_isMaximal_of_field ℂ (MvPolynomial (Fin n) ℂ ⧸ V)`. Establish `key` using `ReciprocityTheory.ChartRestriction.G.Geo.DimF.dim_quot_add_height (A := MvPolynomial (Fin n) ℂ ⧸ V) (fun M N hM hN => (hs M hM).trans (hs N hN).symm) (W.map (Ideal.Quotient.mk V))`.

Rewrite `key` using `[hh, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPW)]`. Conclude with `key` after adjusting the coercions.
-/
theorem ringKrullDim_quotient_minimalPrime_add_one {n : ℕ} {V W : Ideal (MvPolynomial (Fin n) ℂ)} [hVp : V.IsPrime]
    {f : MvPolynomial (Fin n) ℂ} (hf : f ∉ V) (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes)
    (hfin : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V) ≠ ⊤) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) + 1 = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V) := by
  have hPW : V ≤ W := le_sup_left.trans hW.1.2
  have hfW : f ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hq : W.map (Ideal.Quotient.mk V) ∈ (Ideal.span {Ideal.Quotient.mk V f}).minimalPrimes := by
    have e : Ideal.span {Ideal.Quotient.mk V f} = (Ideal.span {f}).map (Ideal.Quotient.mk V) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm]
    exact ⟨W, hW, rfl⟩
  have : (W.map (Ideal.Quotient.mk V)).IsPrime := hq.1.1
  have : (Ideal.span {Ideal.Quotient.mk V f}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have hh : (W.map (Ideal.Quotient.mk V)).height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro h0
    have : Ideal.Quotient.mk V f ∈ W.map (Ideal.Quotient.mk V) := Ideal.mem_map_of_mem _ hfW
    rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hf this
  have : IsDomain (MvPolynomial (Fin n) ℂ ⧸ V) := Ideal.Quotient.isDomain V
  have : Algebra.FiniteType ℂ (MvPolynomial (Fin n) ℂ ⧸ V) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ V) (Ideal.Quotient.mkₐ_surjective ℂ V)
  have : IsNoetherianRing (MvPolynomial (Fin n) ℂ ⧸ V) := Algebra.FiniteType.isNoetherianRing ℂ _
  have : FiniteRingKrullDim (MvPolynomial (Fin n) ℂ ⧸ V) :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨fun h => by
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ V)
      rw [h] at h0
      exact absurd h0 (by simp), hfin⟩
  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.Geo.DimF.exists_height_of_isMaximal_of_field ℂ (MvPolynomial (Fin n) ℂ ⧸ V)
  have key := ReciprocityTheory.ChartRestriction.G.Geo.DimF.dim_quot_add_height (A := MvPolynomial (Fin n) ℂ ⧸ V)
    (fun M N hM hN => (hs M hM).trans (hs N hN).symm) (W.map (Ideal.Quotient.mk V))
  rw [hh, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPW)] at key
  exact_mod_cast key

/- English proof (translation)
Rewrite using `[ringKrullDim_quotient, Order.krullDim_lt_coe_iff]`. Introduce `l`. Establish `hLP : L ≤ l.head.1.asIdeal` using `fun x hx => l.head.2 (Ideal.mem_sup_left hx)`. Establish `hfP : f ∈ l.head.1.asIdeal` using `l.head.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))`. Take `⟨W, hW, hWP⟩` from `Ideal.exists_minimalPrimes_le hLP`.

Set `W' : PrimeSpectrum R` to `⟨W, hW.1.1⟩`. Establish `hlt : W' < l.head.1` using `lt_of_le_of_ne hWP fun h => hf W hW (by rw [← h] at hfP; exact hfP)`. Establish `h1 : (l.length : ℕ∞) ≤ Order.coheight l.head.1`. Conclude with `Order.length_le_coheight_head (p := l.map Subtype.val (fun _ _ => id))`. Establish `h2 : Order.coheight l.head.1 + 1 ≤ Order.coheight W'` using `Order.coheight_add_one_le hlt`.

Establish `hIci : Set.Ici W' = PrimeSpectrum.zeroLocus (R` using `R) (W : Set R) := by`. Use extensionality with `p`. Conclude with `Iff.rfl`. Establish `h3 : ((Order.coheight W' : ℕ∞) : WithBot ℕ∞) = (d : WithBot ℕ∞)`. Rewrite using `[Order.coheight_eq_krullDim_Ici, hIci, ← ringKrullDim_quotient]`.

Conclude with `hd W hW`. Establish `h3' : Order.coheight W' = (d : ℕ∞)` using `by exact_mod_cast h3`. Establish `h4 : ((l.length + 1 : ℕ) : ℕ∞) ≤ (d : ℕ∞)`. Rewrite using `[← h3']`. Use `push_cast`.

Combine the equalities or inequalities in the displayed calculation. Establish `h5 : l.length + 1 ≤ d` using `by exact_mod_cast h4`. Use linear arithmetic over natural numbers and integers.
-/
theorem ringKrullDim_quotient_sup_span_lt {R : Type*} [CommRing R] {L : Ideal R} {f : R} {d : ℕ}
    (hf : ∀ W ∈ L.minimalPrimes, f ∉ W) (hd : ∀ W ∈ L.minimalPrimes, ringKrullDim (R ⧸ W) = d) :
    ringKrullDim (R ⧸ (L ⊔ Ideal.span {f})) < d := by
  rw [ringKrullDim_quotient, Order.krullDim_lt_coe_iff]
  intro l
  have hLP : L ≤ l.head.1.asIdeal := fun x hx => l.head.2 (Ideal.mem_sup_left hx)
  have hfP : f ∈ l.head.1.asIdeal := l.head.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  obtain ⟨W, hW, hWP⟩ := Ideal.exists_minimalPrimes_le hLP
  let W' : PrimeSpectrum R := ⟨W, hW.1.1⟩
  have hlt : W' < l.head.1 := lt_of_le_of_ne hWP fun h => hf W hW (by rw [← h] at hfP; exact hfP)
  have h1 : (l.length : ℕ∞) ≤ Order.coheight l.head.1 := by
    exact Order.length_le_coheight_head (p := l.map Subtype.val (fun _ _ => id))
  have h2 : Order.coheight l.head.1 + 1 ≤ Order.coheight W' := Order.coheight_add_one_le hlt
  have hIci : Set.Ici W' = PrimeSpectrum.zeroLocus (R := R) (W : Set R) := by
    ext p
    exact Iff.rfl
  have h3 : ((Order.coheight W' : ℕ∞) : WithBot ℕ∞) = (d : WithBot ℕ∞) := by
    rw [Order.coheight_eq_krullDim_Ici, hIci, ← ringKrullDim_quotient]
    exact hd W hW
  have h3' : Order.coheight W' = (d : ℕ∞) := by exact_mod_cast h3
  have h4 : ((l.length + 1 : ℕ) : ℕ∞) ≤ (d : ℕ∞) := by
    rw [← h3']
    push_cast
    calc (l.length : ℕ∞) + 1 ≤ Order.coheight l.head.1 + 1 := by gcongr
      _ ≤ Order.coheight W' := h2
  have h5 : l.length + 1 ≤ d := by exact_mod_cast h4
  omega

/- English proof (translation)
Take `⟨I₀, h, hcard, hhW, hreg⟩` from `hG n e W hW he (EuclideanSpace.basisFun (Fin n) ℂ)`. Set `T : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)` to `((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n))`. Set `S : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)` to `((EuclideanSpace.equiv (Fin n) ℂ : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)))`. Establish `hT : ∀ x i, T x i = x i` using `fun x i => rfl`. Establish `hS : ∀ w i, S w i = w i` using `fun w i => rfl`.

Establish `hST : ∀ x, S (T x) = x` using `fun x => funext fun i => by rw [hS, hT]`. Establish `hTS : ∀ w, T (S w) = w` using `fun w => by ext i; rw [hT, hS]`. Establish `hZ : ∀ x : Fin n → ℂ, x ∈ zeroSet W ↔ T x ∈ zeroSetEuc W`. Introduce `x`. Establish `hx : (fun i => T x i) = x` using `funext fun i => hT x i`.

Simplify using `only [zeroSet, zeroSetEuc, Set.mem_ofPred_eq, hx]`. Use `⟨h, hhW, fun z hz hzh => ?_⟩` and prove the remaining obligations. Establish `hzh' : eval (fun i => T z i) h ≠ 0`. Establish `hx : (fun i => T z i) = z` using `funext fun i => hT z i`. Rewrite using `[hx]` and apply the resulting hypothesis.

Take `⟨Ω, V, g, hΩ, hV, hzV, hg, hproj, hgraph⟩` from `hreg (T z) ((hZ z).mp hz) hzh'`. Set `eI : I₀ ≃ Fin e` to `I₀.equivFinOfCardEq hcard`. Set `Ψ : (Fin e → ℂ) →L[ℂ] (I₀ → ℂ)` to `ContinuousLinearMap.pi fun i : I₀ => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) (eI i)`. Set `A : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ)` to `ContinuousLinearMap.pi fun k : Fin e => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) ((eI.symm k : I₀) : Fin n)`. Establish `hΨ : ∀ y i, Ψ y i = y (eI i)` using `fun y i => rfl`.

Establish `hA : ∀ x k, A x k = x ((eI.symm k : I₀) : Fin n)` using `fun x k => rfl`. Establish `hO : IsOpen (Ψ ⁻¹' Ω)` using `hΩ.preimage Ψ.continuous`. Use `⟨A, Ψ ⁻¹' Ω, T ⁻¹' V, fun y => S (g (Ψ y)), hO, hV.preimage T.continuous, hzV, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn_fin hO (S.differentiable.comp_differentiableOn (hg.comp Ψ.differentiable.differentiableOn fun y hy => hy))`. Introduce `y hy`.

Use extensionality with `k`. Establish `h1` using `congrFun (hproj (Ψ y) hy) (eI.symm k)`. Simplify using `only [frameProj, EuclideanSpace.basisFun_inner] at h1`. Use `show A (S (g (Ψ y))) k = y k`. Rewrite using `[hA, hS, h1, hΨ, Equiv.apply_symm_apply]`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hxZ, hxV⟩`. Establish `hmem : T x ∈ zeroSetEuc W ∩ V` using `⟨(hZ x).mp hxZ, hxV⟩`. Rewrite `hmem` using `[hgraph]`.

Take `⟨w, hw, hgw⟩` from `hmem`. Establish `hΨw : Ψ (fun k => w (eI.symm k)) = w` using `funext fun i => by simp [hΨ]`. Use `⟨fun k => w (eI.symm k), ?_, ?_⟩` and prove the remaining obligations. Use `show Ψ _ ∈ Ω`. Rewrite using `[hΨw]` and apply the resulting hypothesis.

Simplify using `only [hΨw, hgw, hST]`. Introduce and unpack `⟨y, hy, rfl⟩`. Establish `hmem : g (Ψ y) ∈ zeroSetEuc W ∩ V` using `hgraph ▸ Set.mem_image_of_mem g hy`. Use `⟨(hZ _).mpr ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hTS]`.

Conclude with `hmem.1`. Use `show T (S (g (Ψ y))) ∈ V`. Rewrite using `[hTS]`. Conclude with `hmem.2`.
-/
theorem graphChart_of_frameGraphGeneric (hG : FrameGraphGeneric.Statement) {n e : ℕ}
    (W : Ideal (MvPolynomial (Fin n) ℂ)) (hW : W.IsPrime)
    (he : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = e) :
    ∃ h : MvPolynomial (Fin n) ℂ, h ∉ W ∧ ∀ z ∈ zeroSet W, eval z h ≠ 0 →
      ∃ (A : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (V : Set (Fin n → ℂ))
        (g : (Fin e → ℂ) → Fin n → ℂ), IsOpen O ∧ IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ g O ∧
          (∀ y ∈ O, A (g y) = y) ∧ zeroSet W ∩ V = g '' O := by
  obtain ⟨I₀, h, hcard, hhW, hreg⟩ := hG n e W hW he (EuclideanSpace.basisFun (Fin n) ℂ)
  let T : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    ((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n))
  let S : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ) :=
    ((EuclideanSpace.equiv (Fin n) ℂ : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)))
  have hT : ∀ x i, T x i = x i := fun x i => rfl
  have hS : ∀ w i, S w i = w i := fun w i => rfl
  have hST : ∀ x, S (T x) = x := fun x => funext fun i => by rw [hS, hT]
  have hTS : ∀ w, T (S w) = w := fun w => by ext i; rw [hT, hS]
  have hZ : ∀ x : Fin n → ℂ, x ∈ zeroSet W ↔ T x ∈ zeroSetEuc W := by
    intro x
    have hx : (fun i => T x i) = x := funext fun i => hT x i
    simp only [zeroSet, zeroSetEuc, Set.mem_ofPred_eq, hx]
  refine ⟨h, hhW, fun z hz hzh => ?_⟩
  have hzh' : eval (fun i => T z i) h ≠ 0 := by
    have hx : (fun i => T z i) = z := funext fun i => hT z i
    rwa [hx]
  obtain ⟨Ω, V, g, hΩ, hV, hzV, hg, hproj, hgraph⟩ := hreg (T z) ((hZ z).mp hz) hzh'
  let eI : I₀ ≃ Fin e := I₀.equivFinOfCardEq hcard
  let Ψ : (Fin e → ℂ) →L[ℂ] (I₀ → ℂ) :=
    ContinuousLinearMap.pi fun i : I₀ => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) (eI i)
  let A : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ) :=
    ContinuousLinearMap.pi fun k : Fin e =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) ((eI.symm k : I₀) : Fin n)
  have hΨ : ∀ y i, Ψ y i = y (eI i) := fun y i => rfl
  have hA : ∀ x k, A x k = x ((eI.symm k : I₀) : Fin n) := fun x k => rfl
  have hO : IsOpen (Ψ ⁻¹' Ω) := hΩ.preimage Ψ.continuous
  refine ⟨A, Ψ ⁻¹' Ω, T ⁻¹' V, fun y => S (g (Ψ y)), hO, hV.preimage T.continuous, hzV, ?_, ?_, ?_⟩
  · exact IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn_fin hO (S.differentiable.comp_differentiableOn
      (hg.comp Ψ.differentiable.differentiableOn fun y hy => hy))
  · intro y hy
    ext k
    have h1 := congrFun (hproj (Ψ y) hy) (eI.symm k)
    simp only [frameProj, EuclideanSpace.basisFun_inner] at h1
    show A (S (g (Ψ y))) k = y k
    rw [hA, hS, h1, hΨ, Equiv.apply_symm_apply]
  · ext x
    constructor
    · rintro ⟨hxZ, hxV⟩
      have hmem : T x ∈ zeroSetEuc W ∩ V := ⟨(hZ x).mp hxZ, hxV⟩
      rw [hgraph] at hmem
      obtain ⟨w, hw, hgw⟩ := hmem
      have hΨw : Ψ (fun k => w (eI.symm k)) = w := funext fun i => by simp [hΨ]
      refine ⟨fun k => w (eI.symm k), ?_, ?_⟩
      · show Ψ _ ∈ Ω
        rwa [hΨw]
      · simp only [hΨw, hgw, hST]
    · rintro ⟨y, hy, rfl⟩
      have hmem : g (Ψ y) ∈ zeroSetEuc W ∩ V := hgraph ▸ Set.mem_image_of_mem g hy
      refine ⟨(hZ _).mpr ?_, ?_⟩
      · rw [hTS]
        exact hmem.1
      · show T (S (g (Ψ y))) ∈ V
        rw [hTS]
        exact hmem.2

end

end GroundTheory.Heights₂.Heights
