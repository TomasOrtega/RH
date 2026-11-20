import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TraceMulConjIntIffMemOfMulDifferentEqOne
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.InvMulVecEqZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FinrankInt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.CMBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨t, ht, hκ⟩ : ∃ t : ℤ, (t = 1 ∨ t = -1) ∧ X.κ0 = 2 * (t * X.ξ0) := by`. Break down `X.κ0_xi with h | h` into its components or cases. Conclude with `⟨1, Or.inl rfl, by rw [h]; simp⟩`. Conclude with `⟨-1, Or.inr rfl, by rw [h]; simp⟩`. Establish `hd` using `GlobalTheory.trace_xi_mul_conj_int_iff_mem E r X 𝔄 hr h𝔄 hΛ`.

Take `⟨D, e, hp, hq, he⟩` from `SelfDualDatum.exists_datum E H (𝔄 : Submodule (𝓞 E) E) (t * X.ξ0) (FractionalIdeal.fg_of_isUnit _ (IsUnit.mk0 _ h𝔄)) (FractionalIdeal.coeToSubmodule_ne_bot.2 h𝔄) (by`. Use `X.ξ0_im` as an intermediate fact. Rewrite `this` using `[FD.cc]`. Rewrite using `[map_mul, map_intCast, this, mul_neg])`. Use the proof step `(fun τ hτ => by`.

Use `X.κ0_sign ⟨τ, (hΨ τ).2 hτ⟩` as an intermediate fact. Rewrite `this` using `[hκ, map_mul, map_ofNat]`. Simplify using `only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero] at this`. Use the proof step `linarith)`. Use the proof step `(fun x => by`.

Use `Iff.trans ?_ (hd x)` and prove the remaining obligations. Use `forall₂_congr fun y _ => ?_` and prove the remaining obligations. Break down `ht with rfl | rfl` into its components or cases. Simplify using `[FD.cc]`. Simplify using `only [Int.cast_neg, Int.cast_one, neg_mul, _root_.one_mul, map_neg, FD.cc]`.

Conclude with `⟨fun ⟨n, h⟩ => ⟨-n, by rw [Int.cast_neg, ← h, neg_neg]⟩, fun ⟨n, h⟩ => ⟨-n, by rw [h, Int.cast_neg]⟩⟩)`. Use `⟨fun b => match b with | true => D | false => oppDatum D, fun b => match b with | true => e | false => e, fun b => match b with | true => t | false => -t, ⟨hp, hq⟩, ⟨hq, hp⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `(_ | _)`. Apply the tactic sequence `rcases ht with rfl | rfl <;> simp`. Conclude with `ht`.

Introduce and unpack `(_ | _) x y`. Express the relevant statement in the definitionally equal form `D.La at x y`. Express the relevant statement in the definitionally equal form `((-(D.EF x y) : ℤ) : ℚ) = Algebra.trace ℚ E (((-t : ℤ) : E) * X.ξ0 * (e x : E) * FD.cc (e y : E))`. Rewrite using `[Int.cast_neg, he, ← map_neg]`. Use `congr 1`.

Simplify using `[FD.cc]`. Conclude with `he x y`.
-/
theorem exists_pair (H : Host E) {r : ℕ} (X : FD.DataX E r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hr : 0 < r) (h𝔄 : 𝔄 ≠ 0) (hΨ : ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0)
    (hΛ : X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ X.L', v = a • u}) :
    ∃ (D₁ : Bool → Datum H) (e : ∀ b, (D₁ b).La ≃ₗ[𝓞 E] (𝔄 : Submodule (𝓞 E) E)) (s : Bool → ℤ),
      ((D₁ true).p = 1 ∧ (D₁ true).q = 0) ∧ ((D₁ false).p = 0 ∧ (D₁ false).q = 1) ∧ (∀ b, s b = 1 ∨ s b = -1) ∧
      ∀ b x y, (((D₁ b).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (s b * X.ξ0 * (e b x : E) * FD.cc (e b y : E)) := by
  obtain ⟨t, ht, hκ⟩ : ∃ t : ℤ, (t = 1 ∨ t = -1) ∧ X.κ0 = 2 * (t * X.ξ0) := by
    rcases X.κ0_xi with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; simp⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; simp⟩
  have hd := GlobalTheory.trace_xi_mul_conj_int_iff_mem E r X 𝔄 hr h𝔄 hΛ
  obtain ⟨D, e, hp, hq, he⟩ := SelfDualDatum.exists_datum E H (𝔄 : Submodule (𝓞 E) E) (t * X.ξ0)
    (FractionalIdeal.fg_of_isUnit _ (IsUnit.mk0 _ h𝔄)) (FractionalIdeal.coeToSubmodule_ne_bot.2 h𝔄)
    (by
      have := X.ξ0_im
      rw [FD.cc] at this
      rw [map_mul, map_intCast, this, mul_neg])
    (fun τ hτ => by
      have := X.κ0_sign ⟨τ, (hΨ τ).2 hτ⟩
      rw [hκ, map_mul, map_ofNat] at this
      simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero] at this
      linarith)
    (fun x => by
      refine Iff.trans ?_ (hd x)
      refine forall₂_congr fun y _ => ?_
      rcases ht with rfl | rfl
      · simp [FD.cc]
      · simp only [Int.cast_neg, Int.cast_one, neg_mul, _root_.one_mul, map_neg, FD.cc]
        exact ⟨fun ⟨n, h⟩ => ⟨-n, by rw [Int.cast_neg, ← h, neg_neg]⟩, fun ⟨n, h⟩ => ⟨-n, by rw [h, Int.cast_neg]⟩⟩)
  refine ⟨fun b => match b with | true => D | false => oppDatum D,
    fun b => match b with | true => e | false => e, fun b => match b with | true => t | false => -t,
    ⟨hp, hq⟩, ⟨hq, hp⟩, ?_, ?_⟩
  · rintro (_ | _)
    · rcases ht with rfl | rfl <;> simp
    · exact ht
  · rintro (_ | _) x y
    · change D.La at x y
      change ((-(D.EF x y) : ℤ) : ℚ) = Algebra.trace ℚ E (((-t : ℤ) : E) * X.ξ0 * (e x : E) * FD.cc (e y : E))
      rw [Int.cast_neg, he, ← map_neg]
      congr 1
      simp [FD.cc]
    · exact he x y

omit [IsCMField E] in

/- English proof (translation)
Take `⟨a, ha, h0⟩` from `(Submodule.ne_bot_iff _).1 h`. Take `⟨n, hn, hi⟩` from `exists_integral_multiples ℤ ℚ (Finset.univ.image fun i => c i / a)`. Use `⟨n.natAbs, Int.natAbs_pos.2 hn, fun i => ?_⟩` and prove the remaining obligations. Establish `h1` using `𝔄.smul_mem (⟨n • (c i / a), hi _ (by simp)⟩ : 𝓞 E) ha`. Establish `h2 : (n : E) * c i ∈ 𝔄`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `_ = (n • (c i / a)) * a`. Rewrite using `[zsmul_eq_mul, _root_.mul_assoc, div_mul_cancel₀ _ h0]`. Break down `Int.natAbs_eq n with h | h` into its components or cases. Rewrite `h2` using `[h, Int.cast_natCast]`. Then use the resulting hypothesis.

Rewrite `h2` using `[h, Int.cast_neg, Int.cast_natCast, neg_mul]`. Conclude with `𝔄.neg_mem_iff.1 h2`.
-/
theorem exists_nsmul_mem (𝔄 : Submodule (𝓞 E) E) (h : 𝔄 ≠ ⊥) {J : Type} [Fintype J] (c : J → E) :
    ∃ n : ℕ, 0 < n ∧ ∀ i, (n : E) * c i ∈ 𝔄 := by
  classical
  obtain ⟨a, ha, h0⟩ := (Submodule.ne_bot_iff _).1 h
  obtain ⟨n, hn, hi⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image fun i => c i / a)
  refine ⟨n.natAbs, Int.natAbs_pos.2 hn, fun i => ?_⟩
  have h1 := 𝔄.smul_mem (⟨n • (c i / a), hi _ (by simp)⟩ : 𝓞 E) ha
  have h2 : (n : E) * c i ∈ 𝔄 := by
    convert h1 using 1
    change _ = (n • (c i / a)) * a
    rw [zsmul_eq_mul, _root_.mul_assoc, div_mul_cancel₀ _ h0]
  rcases Int.natAbs_eq n with h | h
  · rwa [h, Int.cast_natCast] at h2
  · rw [h, Int.cast_neg, Int.cast_natCast, neg_mul] at h2
    exact 𝔄.neg_mem_iff.1 h2

/- English proof (translation)
Substitute `hX` using the available equality. Take `⟨D₁, e, s, h1, h2, hs, he⟩` from `exists_pair H X 𝔄 hr h𝔄 hΨ hΛ`. Establish `hpure` using `GlobalTheory.PurePer.perFr_pure E r X La x₀.1 lam x₀.2 hl`. Take `⟨hL, hli, -, -, -, hbd, -⟩` from `hl`. Set `σ : Fin p ⊕ Fin q ≃ Fin r` to `(Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))`.

Establish `hσl : ∀ j, q ≤ (σ (.inl j) : ℕ)` using `fun j => by simp [σ]`. Establish `hσr : ∀ j, (σ (.inr j) : ℕ) < q` using `fun j => by simp [σ]`. Establish `hmem : ∀ (a : (𝔄 : Submodule (𝓞 E) E)) j, (a : E) • lam j ∈ X.Λ` using `fun a j => hΛ ▸ Submodule.subset_span ⟨a, a.2, _, hL j, rfl⟩`. Set `m : Fin r → (𝔄 : Submodule (𝓞 E) E) →ₗ[𝓞 E] X.Λ` to `fun j => { toFun := fun a => ⟨_, hmem a j⟩ map_add' := fun a b => Subtype.ext (add_smul _ _ _) map_smul' := fun c a => Subtype.ext (smul_assoc _ _ _) }`. Set `f : ∀ j : Fin p ⊕ Fin q, (D₁ j.isLeft).La →ₗ[𝓞 E] D.La` to `fun j => φ.symm.toLinearMap ∘ₗ m (σ j) ∘ₗ (e _).toLinearMap`.

Establish `hf : ∀ j a, (φ (f j a) : Fin r → E) = (e _ a : E) • lam (σ j)` using `fun j a => by`. Simplify using `[f, m]`. Set `hh : Fin p ⊕ Fin q → 𝓞 E` to `fun j => -(s j.isLeft : 𝓞 E) * ⟨FD.herm X.Gm (lam (σ j)) (lam (σ j)), X.L'_int _ (hL _) _ (hL _)⟩`. Establish `hhh : ∀ j, (hh j : E) = -(s j.isLeft : E) * FD.herm X.Gm (lam (σ j)) (lam (σ j))` using `fun j => by`. Simplify using `only [hh, map_mul, map_neg, map_intCast]`.

Both sides reduce to the same expression. Establish `hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0` using `fun τ => by`. Use `sq_eq_sq_iff_eq_or_eq_neg.1 ?_` and prove the remaining obligations. Rewrite using `[← map_pow, HostModel.coe_sq_eq_neg H.rt_sq, H.sqrt_neg_disc_sq, map_neg, map_natCast]`. Use `⟨⟨D₁, h1, h2, f, ?_, hh, fun j a b => ?_, ?_⟩, fun j τ => ?_⟩` and prove the remaining obligations.

Introduce and unpack `(j | j) a k hk`. Rewrite using `[pm, hf]`. Establish `hk' : ty k (H.rt : E) ≠ H.rt0` using `by simpa using hk`. Conclude with `(hpure _ _ _ _).2 (hp0 ▸ hσl j) (fun h => hk' ((hΨ _).1 h)) (hp0 ▸ hix k hk')`. Rewrite using `[pm, hf]`.

Establish `hk' : ty k (H.rt : E) ≠ -H.rt0` using `by simpa using hk`. Conclude with `(hpure _ _ _ _).1 (hp0 ▸ hσr j) ((hΨ _).2 ((hsq _).resolve_right hk'))`. Apply `Int.cast_injective (α := ℚ)` to reduce the goal to its premises. Rewrite using `[isom, he, hf, hf, map_smul, Submodule.coe_smul, Algebra.smul_def (hh j), ← RingOfIntegers.coe_eq_algebraMap, hhh]`. Use `congr 1`.

Establish `h3 : ∀ (a b : E) (u : Fin r → E), FD.herm X.Gm (a • u) (b • u) = a * FD.cc b * FD.herm X.Gm u u` using `fun a b u => by`. Simplify using `only [FD.herm, FD.cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Rewrite using `[h3]`. Apply the tactic sequence `rcases hs j.isLeft with h | h <;> rw [h] <;> push_cast <;> ring`.

Use `haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩`. Set `B` to `basisOfLinearIndependentOfCardEqFinrank hli (by simp)`. Establish `hB : ∀ j, B j = lam j` using `fun j => by simp [B]`. Set `N : Submodule (𝓞 E) D.La` to `LinearMap.range (∑ j, f j ∘ₗ LinearMap.proj j)`. Establish `hN : ∀ a, a ∈ N ↔ ∃ x : ∀ j : Fin p ⊕ Fin q, (D₁ j.isLeft).La, a = ∑ j, f j (x j)` using `fun a => by`.

Simplify using `only [N, LinearMap.mem_range, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]`. Conclude with `exists_congr fun _ => eq_comm`. Take `⟨S, hS⟩` from `D.fin.fg_top`. Take `⟨n, hn, hc⟩` from `exists_nsmul_mem (𝔄 : Submodule (𝓞 E) E) (FractionalIdeal.coeToSubmodule_ne_bot.2 h𝔄) (fun i : S × Fin r => B.repr (φ i.1 : Fin r → E) i.2)`. Use `⟨n, hn, fun a => (hN _).1 ?_⟩` and prove the remaining obligations.

Establish `: (⊤ : Submodule (𝓞 E) D.La) ≤ N.comap (n • LinearMap.id)`. Rewrite using `[← hS, Submodule.span_le]`. Introduce `a ha`. Use `(hN _).2 ⟨fun j => (e _).symm ⟨_, hc (⟨a, ha⟩, σ j)⟩, φ.injective (Subtype.ext ?_)⟩` and prove the remaining obligations. Rewrite using `[map_sum, AddSubmonoidClass.coe_finsetSum]`.

Simplify using `only [hf, LinearEquiv.apply_symm_apply]`. Rewrite using `[Equiv.sum_comp σ (fun j => ((n : E) * B.repr (φ a : Fin r → E) j) • lam j)]`. Simplify using `only [mul_smul, ← Finset.smul_sum, ← hB, B.sum_repr]`. Simplify using `[Nat.cast_smul_eq_nsmul]`. Conclude with `this Submodule.mem_top`.

Express the relevant statement in the definitionally equal form `‖τ (hh j : E)‖ ≤ _`. Establish `h4 : ‖τ (hh j : E)‖ = ‖τ (FD.herm X.Gm (lam (σ j)) (lam (σ j)))‖`. Rewrite using `[hhh]`. Apply the tactic sequence `rcases hs j.isLeft with h | h <;> rw [h] <;> simp`. Rewrite using `[h4]`.

Distinguish the cases in `hτ : τ ∈ X.Ψ`. Conclude with `hbd _ ⟨τ, hτ⟩`. Use `hbd (σ j) ⟨ComplexEmbedding.conjugate τ, by` as an intermediate fact. Assume the negation of the conclusion as `h`. Conclude with `hτ ((X.cmType τ).2 h)⟩`.

Simplify `this` using `[ComplexEmbedding.conjugate_coe_eq]`.
-/
theorem exists_cmLat (H : Host E) {r p q : ℕ} (Y : FD.Data E r) (x₀ : Y.dom) (X : FD.DataX E r) (hX : X.toData = Y)
    (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hr : 0 < r) (h𝔄 : 𝔄 ≠ 0) (hrk : r = p + q) (hp0 : Y.p0 = q) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0)
    (hΛ : X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ X.L', v = a • u})
    (D : Datum H) {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)
    (φ : D.La ≃ₗ[𝓞 E] Y.Λ)
    (isom : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-Y.ξ0 * FD.herm Y.Gm (φ a : Fin r → E) (φ b)))
    (ix : Fin g → ℕ) (hix : ∀ j, ty j (H.rt : E) ≠ H.rt0 → ix j < q)
    (pm : ∀ a j, Pe a j = perFr Y x₀.1 (φ a : Fin r → E) (ty j) (ix j))
    (La : ℝ) (lam : Fin r → Fin r → E) (hl : FD.LamBasis X La (hX ▸ x₀.1) lam) :
    ∃ Z : CMLat hP p q, ∀ j (τ : E →+* ℂ), ‖τ (Z.hh j : E)‖ ≤ La ^ 2 := by
  classical
  subst hX
  obtain ⟨D₁, e, s, h1, h2, hs, he⟩ := exists_pair H X 𝔄 hr h𝔄 hΨ hΛ
  have hpure := GlobalTheory.PurePer.perFr_pure E r X La x₀.1 lam x₀.2 hl
  obtain ⟨hL, hli, -, -, -, hbd, -⟩ := hl
  let σ : Fin p ⊕ Fin q ≃ Fin r := (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))
  have hσl : ∀ j, q ≤ (σ (.inl j) : ℕ) := fun j => by simp [σ]
  have hσr : ∀ j, (σ (.inr j) : ℕ) < q := fun j => by simp [σ]
  have hmem : ∀ (a : (𝔄 : Submodule (𝓞 E) E)) j, (a : E) • lam j ∈ X.Λ := fun a j =>
    hΛ ▸ Submodule.subset_span ⟨a, a.2, _, hL j, rfl⟩
  let m : Fin r → (𝔄 : Submodule (𝓞 E) E) →ₗ[𝓞 E] X.Λ := fun j =>
    { toFun := fun a => ⟨_, hmem a j⟩
      map_add' := fun a b => Subtype.ext (add_smul _ _ _)
      map_smul' := fun c a => Subtype.ext (smul_assoc _ _ _) }
  let f : ∀ j : Fin p ⊕ Fin q, (D₁ j.isLeft).La →ₗ[𝓞 E] D.La := fun j =>
    φ.symm.toLinearMap ∘ₗ m (σ j) ∘ₗ (e _).toLinearMap
  have hf : ∀ j a, (φ (f j a) : Fin r → E) = (e _ a : E) • lam (σ j) := fun j a => by
    simp [f, m]
  let hh : Fin p ⊕ Fin q → 𝓞 E := fun j =>
    -(s j.isLeft : 𝓞 E) * ⟨FD.herm X.Gm (lam (σ j)) (lam (σ j)), X.L'_int _ (hL _) _ (hL _)⟩
  have hhh : ∀ j, (hh j : E) = -(s j.isLeft : E) * FD.herm X.Gm (lam (σ j)) (lam (σ j)) := fun j => by
    simp only [hh, map_mul, map_neg, map_intCast]
    rfl
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := fun τ => by
    refine sq_eq_sq_iff_eq_or_eq_neg.1 ?_
    rw [← map_pow, HostModel.coe_sq_eq_neg H.rt_sq, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  refine ⟨⟨D₁, h1, h2, f, ?_, hh, fun j a b => ?_, ?_⟩, fun j τ => ?_⟩
  · rintro (j | j) a k hk
    · rw [pm, hf]
      have hk' : ty k (H.rt : E) ≠ H.rt0 := by simpa using hk
      exact (hpure _ _ _ _).2 (hp0 ▸ hσl j) (fun h => hk' ((hΨ _).1 h)) (hp0 ▸ hix k hk')
    · rw [pm, hf]
      have hk' : ty k (H.rt : E) ≠ -H.rt0 := by simpa using hk
      exact (hpure _ _ _ _).1 (hp0 ▸ hσr j) ((hΨ _).2 ((hsq _).resolve_right hk'))
  · apply Int.cast_injective (α := ℚ)
    rw [isom, he, hf, hf, map_smul, Submodule.coe_smul, Algebra.smul_def (hh j), ← RingOfIntegers.coe_eq_algebraMap, hhh]
    congr 1
    have h3 : ∀ (a b : E) (u : Fin r → E), FD.herm X.Gm (a • u) (b • u) = a * FD.cc b * FD.herm X.Gm u u :=
      fun a b u => by
        simp only [FD.herm, FD.cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [h3]
    rcases hs j.isLeft with h | h <;> rw [h] <;> push_cast <;> ring
  · haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
    have hB : ∀ j, B j = lam j := fun j => by simp [B]
    let N : Submodule (𝓞 E) D.La := LinearMap.range (∑ j, f j ∘ₗ LinearMap.proj j)
    have hN : ∀ a, a ∈ N ↔ ∃ x : ∀ j : Fin p ⊕ Fin q, (D₁ j.isLeft).La, a = ∑ j, f j (x j) := fun a => by
      simp only [N, LinearMap.mem_range, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      exact exists_congr fun _ => eq_comm
    obtain ⟨S, hS⟩ := D.fin.fg_top
    obtain ⟨n, hn, hc⟩ := exists_nsmul_mem (𝔄 : Submodule (𝓞 E) E) (FractionalIdeal.coeToSubmodule_ne_bot.2 h𝔄)
      (fun i : S × Fin r => B.repr (φ i.1 : Fin r → E) i.2)
    refine ⟨n, hn, fun a => (hN _).1 ?_⟩
    have : (⊤ : Submodule (𝓞 E) D.La) ≤ N.comap (n • LinearMap.id) := by
      rw [← hS, Submodule.span_le]
      intro a ha
      refine (hN _).2 ⟨fun j => (e _).symm ⟨_, hc (⟨a, ha⟩, σ j)⟩, φ.injective (Subtype.ext ?_)⟩
      rw [map_sum, AddSubmonoidClass.coe_finsetSum]
      simp only [hf, LinearEquiv.apply_symm_apply]
      rw [Equiv.sum_comp σ (fun j => ((n : E) * B.repr (φ a : Fin r → E) j) • lam j)]
      simp only [mul_smul, ← Finset.smul_sum, ← hB, B.sum_repr]
      simp [Nat.cast_smul_eq_nsmul]
    exact this Submodule.mem_top
  · change ‖τ (hh j : E)‖ ≤ _
    have h4 : ‖τ (hh j : E)‖ = ‖τ (FD.herm X.Gm (lam (σ j)) (lam (σ j)))‖ := by
      rw [hhh]
      rcases hs j.isLeft with h | h <;> rw [h] <;> simp
    rw [h4]
    by_cases hτ : τ ∈ X.Ψ
    · exact hbd _ ⟨τ, hτ⟩
    · have := hbd (σ j) ⟨ComplexEmbedding.conjugate τ, by
        by_contra h
        exact hτ ((X.cmType τ).2 h)⟩
      simpa [ComplexEmbedding.conjugate_coe_eq] using this

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c r U hU hr k x₀ W Xx hX 𝔄 h𝔄 hΛ La lam hl`. Take `⟨h1, h2, -⟩` from `hU`. Use `exists_cmLat H (U.X k) x₀ Xx hX 𝔄 hr h𝔄 h1 (h2 k).1 (h2 k).2 hΛ _ W.per (W.φ k) (W.isom k) (fun j => (W.e j).2) (fun j hj => ?_) W.pm_eq La lam hl` and prove the remaining obligations. Conclude with `(W.e j).2.2.trans_eq (if_neg hj)`.
-/
theorem exists_cmLat_unfAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r), IsUnf U → 0 < r → ∀ (k : U.Comp) (x₀ : (U.X k).dom) (W : PullbackSections.UnfAt U k x₀) (Xx : FD.DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → ∀ (La : ℝ) (lam : Fin r → Fin r → E), FD.LamBasis Xx La (hX ▸ x₀.1) lam → ∃ Z : CMLat W.per Dw.p Dw.q, ∀ j (τ : E →+* ℂ), ‖τ (Z.hh j : E)‖ ≤ La ^ 2 := by
  intro E _ _ _ H Dw l Xo c r U hU hr k x₀ W Xx hX 𝔄 h𝔄 hΛ La lam hl
  obtain ⟨h1, h2, -⟩ := hU
  refine exists_cmLat H (U.X k) x₀ Xx hX 𝔄 hr h𝔄 h1 (h2 k).1 (h2 k).2 hΛ _ W.per (W.φ k) (W.isom k)
    (fun j => (W.e j).2) (fun j hj => ?_) W.pm_eq La lam hl
  exact (W.e j).2.2.trans_eq (if_neg hj)

end GlobalTheory.LamT.CMBasis
