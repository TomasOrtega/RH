import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompactUnitaryAdelicImageIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjugatorsDifferByCentralizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostAllPlacesTwistedUnitIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedUnitEqNormAlmostAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteBadPlacesPairs
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LocTriv

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `p _ G Ω hΩ P₁ L _ _ ι c hinj hcent hc`. Take `⟨x₁, t₁, hx₁⟩` from `P₁.trivAf`. Establish `hβ₁inv` using `sh_inv_unit G P₁.β P₁.sym`. Establish `hcc : ∀ x, c (c x) = x` using `fun x => hinj (by`. Rewrite using `[hc, hc, sh_mul', sh_mul', sh_sh, hβ₁inv, P₁.sym]`.

Simplify using `only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one])`. Establish `hcne : ∃ x, c x ≠ x`. Take `⟨τ⟩ : Nonempty (G.F →+* ℂ)` from `inferInstance`. Take `⟨f, -, hf⟩` from `G.hKq.2 τ`. Establish `hconj : IsCMField.complexConj G.F f ≠ f`.

Introduce `h`. Apply `hf` to reduce the goal to its premises. Establish `e` using `IsCMField.complexEmbedding_complexConj G.F τ f`. Rewrite `e` using `[h]`. Conclude with `Complex.conj_eq_iff_im.1 e.symm`.

Take `⟨w, hw⟩` from `(hcent (algebraMap G.F G.C f)).1 (Algebra.commutes f _)`. Use `⟨w, fun h => hconj ?_⟩` and prove the remaining obligations. Establish `e2 : ι (c w) = algebraMap G.F G.C (IsCMField.complexConj G.F f)`. Rewrite using `[hc, hw, sh_algebraMap, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]`. Rewrite `e2` using `[h, hw]`.

Conclude with `((algebraMap G.F G.C).injective e2).symm`. Take `⟨S1, hS1⟩` from `exists_finset_of_eventually (GlobalTheory.OrbFinAf.cptInt p G Ω hΩ)`. Take `⟨S2, hS2⟩` from `exists_finset_of_eventually (GlobalTheory.OrbFinAf.cptInt p G {P₁.toAf x₁ t₁ hx₁ P₁.self} isCompact_singleton)`. Take `⟨S3, hS3⟩` from `GlobalTheory.T.eventually_adic_integral_span_closed_mul_star G.C G.star _ (Module.finBasis ℚ G.C)`. Take `⟨S4, hS4⟩` from `GlobalTheory.T.eventually_integral_conjugators_differ_by_centralizer p G P₁.γ P₁.reg.1 P₁.reg.2 L ι hinj hcent _ (Module.finBasis ℚ G.C)`.

Take `⟨S5, hS5⟩` from `GlobalTheory.T.almost_all_places_twisted_unit_integral G.C L ι hinj _ (Module.finBasis ℚ G.C) _ (Module.finBasis ℚ L)`. Take `⟨S6, hS6⟩` from `GlobalTheory.T.fixed_unit_eq_norm_almost_all_places L c hcc hcne _ (Module.finBasis ℚ L)`. Use `⟨S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6 ∪ (finite_above p).toFinset, ?_⟩` and prove the remaining obligations. Introduce `P hγ hcP hex a ha v hv`. Take `⟨x, t, hx, hxΩ⟩` from `hex`.

Simplify using `only [Finset.mem_union, not_or] at hv`. Take `⟨⟨⟨⟨⟨⟨hv1, hv2⟩, hv3⟩, hv4⟩, hv5⟩, hv6⟩, hvp⟩` from `hv`. Establish `hvp' : v.asIdeal ≠ Ideal.span {(p : ℤ)}` using `fun h => hvp ((Set.Finite.mem_toFinset _).2 h)`. Set `w : AwayP p` to `⟨v, hvp'⟩`. Set `K` to `v.adicCompletion ℚ`.

Set `φ : AfP p ⊗[ℚ] G.C →ₐ[ℚ] K ⊗[ℚ] G.C` to `Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C)`. Set `ιv : K ⊗[ℚ] L →ₐ[ℚ] K ⊗[ℚ] G.C` to `Algebra.TensorProduct.map (AlgHom.id ℚ K) ι`. Set `cv : K ⊗[ℚ] L →ₐ[ℚ] K ⊗[ℚ] L` to `Algebra.TensorProduct.map (AlgHom.id ℚ K) c`. Set `X : (K ⊗[ℚ] G.C)ˣ` to `Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) x`. Set `X₁ : (K ⊗[ℚ] G.C)ˣ` to `Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) x₁`.

Establish `key : ∀ (Q : GlobalTheory.LKDef.DPair G) (y : (AfP p ⊗[ℚ] G.C)ˣ) (s : (AfP p)ˣ) (hy : Triv G (AfP p) Q.β y s), ((((GlobalTheory.OrbFinAf.piV G w (Q.toAf y s hy Q.self) : GlobalTheory.OrbFinAf.Gv G w) : (K ⊗[ℚ] G.C)ˣ × Kˣ).1 : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) = ↑(Units.map (φ : AfP p …`. Introduce `Q y s hy`. Use `show φ (↑y * ((1 : AfP p) ⊗ₜ[ℚ] (Q.γ : G.C)) * ↑y⁻¹) = _`. Rewrite using `[map_mul, map_mul, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]`. Both sides reduce to the same expression.

Establish `hXg : IsIntB v (Module.finBasis ℚ G.C) (↑X * ((1 : K) ⊗ₜ[ℚ] (P₁.γ : G.C)) * ↑X⁻¹)`. Establish `h` using `(hS1 w hv1 ⟨_, hxΩ, rfl⟩).1`. Rewrite `h` using `[key P x t hx, hγ]`. Conclude with `h`. Establish `hX₁g : IsIntB v (Module.finBasis ℚ G.C) (↑X₁ * ((1 : K) ⊗ₜ[ℚ] (P₁.γ : G.C)) * ↑X₁⁻¹)`.

Establish `h` using `(hS2 w hv2 ⟨_, rfl, rfl⟩).1`. Rewrite `h` using `[key P₁ x₁ t₁ hx₁]`. Conclude with `h`. Take `⟨m, hm1, hm2⟩` from `hS4 v hv4 X X₁ hXg hX₁g`. Take `⟨hmul, hstar⟩` from `hS3 v hv3`.

Set `T : Kˣ` to `Units.map (AfP.eval w : AfP p →* K) t`. Set `T₁ : Kˣ` to `Units.map (AfP.eval w : AfP p →* K) t₁`. Set `β₁v : (K ⊗[ℚ] G.C)ˣ` to `Units.map ((Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] K ⊗[ℚ] G.C) : G.C →* K ⊗[ℚ] G.C) P₁.β`. Establish `hiota_a : ιv ((1 : K) ⊗ₜ[ℚ] a) * (β₁v : K ⊗[ℚ] G.C) = (1 : K) ⊗ₜ[ℚ] (P.β : G.C)` using `by show (1 : K) ⊗ₜ[ℚ] ι a * (1 : K) ⊗ₜ[ℚ] (P₁.β : G.C) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, ha, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]`.

Establish `htriv : ∀ (Q : GlobalTheory.LKDef.DPair G) (y : (AfP p ⊗[ℚ] G.C)ˣ) (s : (AfP p)ˣ), Triv G (AfP p) Q.β y s → (↑(Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) y) : K ⊗[ℚ] G.C) * ((1 : K) ⊗ₜ[ℚ] (Q.β : G.C)) * (starT G.star K ↑(Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) y)).unop = a …`. Introduce `Q y s hy`. Establish `hy' : (y : AfP p ⊗[ℚ] G.C) * inC G (AfP p) Q.β * (starT G.star (AfP p) y).unop = algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s` using `hy`. Establish `h` using `congrArg (Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C)) hy'`. Rewrite `h` using `[map_mul, map_mul, map_starT]`.

Establish `e1 : Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (inC G (AfP p) Q.β) = (1 : K) ⊗ₜ[ℚ] (Q.β : G.C)`. Simplify using `[inC, Algebra.TensorProduct.map_tmul]`. Establish `e2 : Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s) = algebraMap K (K ⊗[ℚ] G.C) (AfP.eval w (s : AfP p))`. Simplify using `[Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]`. Rewrite `h` using `[e1, e2]`.

Conclude with `h`. Establish `h1 : (X : K ⊗[ℚ] G.C) * (ιv ((1 : K) ⊗ₜ[ℚ] a) * β₁v) * (starT G.star K X).unop = algebraMap K (K ⊗[ℚ] G.C) (T : K)`. Rewrite using `[hiota_a]`. Conclude with `htriv P x t hx`. Establish `h2 : (X₁ : K ⊗[ℚ] G.C) * β₁v * (starT G.star K X₁).unop = algebraMap K (K ⊗[ℚ] G.C) (T₁ : K)` using `htriv P₁ x₁ t₁ hx₁`.

Establish `hιR : ∀ r : K, ιv (algebraMap K (K ⊗[ℚ] L) r) = algebraMap K (K ⊗[ℚ] G.C) r`. Introduce `r`. Simplify using `[ιv, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]`. Establish `hcm : ιv (cv ↑m) = ↑β₁v * (starT G.star K (ιv ↑m)).unop * ↑β₁v⁻¹` using `map_conj_ext G K ι c P₁.β hc ↑m`. Establish `hcore` using `selfDual_conj_eq_one (R := K) (ιv : K ⊗[ℚ] L →+* K ⊗[ℚ] G.C) hιR (starT G.star K) (cv : K ⊗[ℚ] L →+* K ⊗[ℚ] L) β₁v X X₁ T T₁ ((1 : K) ⊗ₜ[ℚ] a) m hcm h1 h2`.

Simplify using `only [RingHom.coe_coe] at hcore`. Establish `hu'u : ((X₁ : K ⊗[ℚ] G.C) * ιv ↑m⁻¹ * ↑X⁻¹) * ((X : K ⊗[ℚ] G.C) * ιv ↑m * ↑X₁⁻¹) = 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = 1 := by rw [Units.inv_mul, mul_one, ← map_mul, Units.inv_mul, map_one, mul_one, Units.mul_inv]`.

Establish `hshu : (starT G.star K ((X : K ⊗[ℚ] G.C) * ιv ↑m * ↑X₁⁻¹)).unop * (starT G.star K ((X₁ : K ⊗[ℚ] G.C) * ιv ↑m⁻¹ * ↑X⁻¹)).unop = 1`. Rewrite using `[← MulOpposite.unop_mul, ← map_mul, hu'u, map_one, MulOpposite.unop_one]`. Use `set u := (X : K ⊗[ℚ] G.C) * ιv ↑m * ↑X₁⁻¹ with hu`. Use `set u' := (X₁ : K ⊗[ℚ] G.C) * ιv ↑m⁻¹ * ↑X⁻¹ with hu'`. Use `set E := algebraMap K (K ⊗[ℚ] L) (↑T⁻¹ * ↑T₁) * ((1 : K) ⊗ₜ[ℚ] a) * (↑m⁻¹ * cv ↑m⁻¹) with hE`.

Use `set wv := (X₁ : K ⊗[ℚ] G.C) * ιv E * ↑X₁⁻¹ with hwvdef`. Establish `hwv : wv = u' * (starT G.star K u').unop`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hu'u, hshu, one_mul, mul_one]`. Use `_ = u' * (u * wv * (starT G.star K u).unop) * (starT G.star K u').unop := by simp only [mul_assoc]`.

Use `_ = _ := by rw [hcore, mul_one]`. Establish `hwvI : IsIntB v (Module.finBasis ℚ G.C) wv` using `hwv ▸ hmul _ _ hm2 (hstar _ hm2)`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Rewrite `ha` using `[map_zero]`.

Conclude with `(Units.ne_zero _) ha.symm`. Take `⟨Eu, hEu⟩ : ∃ Eu : (K ⊗[ℚ] L)ˣ, (Eu : K ⊗[ℚ] L) = E` from `⟨Units.map (algebraMap K (K ⊗[ℚ] L) : K →* K ⊗[ℚ] L) (T⁻¹ * T₁) * Units.map ((Algebra.TensorProduct.includeRight : L →ₐ[ℚ] K ⊗[ℚ] L) : L →* K ⊗[ℚ] L) (Units.mk0 a ha0) * (m⁻¹ * Units.map (cv : K ⊗[ℚ] L →* K ⊗[ℚ] L) m⁻¹), by`. Simplify using `only [Units.val_mul, Units.coe_map, Units.val_mk0, hE, map_mul]`. Use the proof step `rfl⟩`. Establish `h_a : ((X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹) * wv = 1`.

Rewrite using `[hwvdef, ← hEu]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = 1 := by rw [Units.inv_mul X₁, mul_one, ← map_mul ιv, Units.inv_mul Eu, map_one, mul_one, Units.mul_inv X₁]`. Establish `h_b : wv * ((starT G.star K u).unop * u) = 1`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hu'u, one_mul]`. Simplify using `only [mul_assoc]`. Use `_ = u' * (u * wv * (starT G.star K u).unop) * u := by simp only [mul_assoc]`. Use `_ = 1 := by rw [hcore, mul_one, hu'u]`.

Establish `hwv' : (X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹ = (starT G.star K u).unop * u`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc]`. Use `_ = _ := by rw [h_a, one_mul]`. Establish `hE1 : IsIntB v (Module.finBasis ℚ L) (Eu : K ⊗[ℚ] L)` using `hS5 v hv5 X₁ _ (by rw [hEu]; exact hwvI)`.

Establish `hE2 : IsIntB v (Module.finBasis ℚ L) ((Eu⁻¹ : (K ⊗[ℚ] L)ˣ) : K ⊗[ℚ] L)` using `hS5 v hv5 X₁ _ (by rw [hwv']; exact hmul _ _ (hstar _ hm1) hm1)`. Establish `hca : c a = a` using `hinj (by`. Rewrite using `[hc, ha, Units.val_mul, sh_mul', hβ₁inv, P.sym]`. Simplify using `only [mul_assoc, Units.mul_inv_cancel_left])`. Establish `hcalg : ∀ r : K, cv (algebraMap K (K ⊗[ℚ] L) r) = algebraMap K (K ⊗[ℚ] L) r`.

Introduce `r`. Simplify using `[cv, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]`. Establish `hcinv : cv (cv ↑m⁻¹) = ↑m⁻¹` using `map_invol c hcc _`. Establish `hfix : cv ↑Eu = ↑Eu`. Establish `: cv ((1 : K) ⊗ₜ[ℚ] a) = (1 : K) ⊗ₜ[ℚ] a` using `by show (1 : K) ⊗ₜ[ℚ] c a = _`.

Rewrite using `[hca]`. Rewrite using `[hEu, hE]`. Simplify using `only [map_mul, hcalg, hcinv, this]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨y₀, hy₀⟩` from `hS6 v hv6 Eu hfix hE1 hE2`.

Use `⟨T * T₁⁻¹, m * y₀, ?_⟩` and prove the remaining obligations. Rewrite `hy₀` using `[hEu, hE, map_mul]`. Establish `hm' : (m : K ⊗[ℚ] L) * ↑m⁻¹ = 1` using `Units.mul_inv m`. Establish `hcm' : cv ↑m * cv ↑m⁻¹ = 1` using `by rw [← map_mul, Units.mul_inv, map_one]`. Establish `hT : algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T⁻¹ = 1`.

Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Establish `hT₁ : algebraMap K (K ⊗[ℚ] L) ↑T₁ * algebraMap K (K ⊗[ℚ] L) ↑T₁⁻¹ = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Use `show (1 : K) ⊗ₜ[ℚ] a = algebraMap K (K ⊗[ℚ] L) ↑(T * T₁⁻¹) * (↑(m * y₀) * cv ↑(m * y₀))`. Rewrite using `[Units.val_mul, Units.val_mul, map_mul, map_mul]`.

Take the linear combination `(algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T₁⁻¹ * ↑m * cv ↑m) * hy₀ - ((1 : K) ⊗ₜ[ℚ] a) * hT - ((1 : K) ⊗ₜ[ℚ] a) * algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T⁻¹ * hT₁ - ((1 : K) ⊗ₜ[ℚ] a) * algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T⁻¹ * algebra …`.
-/
theorem ratio_local_norm_dpair : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω →
    ∀ (P₁ : GlobalTheory.LKDef.DPair G) (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L),
    Function.Injective ι → (∀ z : G.C, z * P₁.γ = P₁.γ * z ↔ ∃ w, ι w = z) →
    (∀ x, ι (c x) = P₁.β * sh G (ι x) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) →
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ), ∀ (P : GlobalTheory.LKDef.DPair G), P.γ = P₁.γ → P.c = P₁.c →
      (∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.toAf x t hx P.self ∈ Ω) →
      ∀ a : L, ι a = ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) → ∀ v ∉ S,
        ∃ (r : (v.adicCompletion ℚ)ˣ) (y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ),
          (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] a = algebraMap (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L) (r : v.adicCompletion ℚ) *
            ((y : v.adicCompletion ℚ ⊗[ℚ] L) * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c y) := by
  intro p _ G Ω hΩ P₁ L _ _ ι c hinj hcent hc
  obtain ⟨x₁, t₁, hx₁⟩ := P₁.trivAf
  have hβ₁inv := sh_inv_unit G P₁.β P₁.sym
  have hcc : ∀ x, c (c x) = x := fun x => hinj (by
    rw [hc, hc, sh_mul', sh_mul', sh_sh, hβ₁inv, P₁.sym]
    simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one])
  have hcne : ∃ x, c x ≠ x := by
    obtain ⟨τ⟩ : Nonempty (G.F →+* ℂ) := inferInstance
    obtain ⟨f, -, hf⟩ := G.hKq.2 τ
    have hconj : IsCMField.complexConj G.F f ≠ f := by
      intro h
      apply hf
      have e := IsCMField.complexEmbedding_complexConj G.F τ f
      rw [h] at e
      exact Complex.conj_eq_iff_im.1 e.symm
    obtain ⟨w, hw⟩ := (hcent (algebraMap G.F G.C f)).1 (Algebra.commutes f _)
    refine ⟨w, fun h => hconj ?_⟩
    have e2 : ι (c w) = algebraMap G.F G.C (IsCMField.complexConj G.F f) := by
      rw [hc, hw, sh_algebraMap, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]
    rw [h, hw] at e2
    exact ((algebraMap G.F G.C).injective e2).symm
  obtain ⟨S1, hS1⟩ := exists_finset_of_eventually (GlobalTheory.OrbFinAf.cptInt p G Ω hΩ)
  obtain ⟨S2, hS2⟩ := exists_finset_of_eventually
    (GlobalTheory.OrbFinAf.cptInt p G {P₁.toAf x₁ t₁ hx₁ P₁.self} isCompact_singleton)
  obtain ⟨S3, hS3⟩ := GlobalTheory.T.eventually_adic_integral_span_closed_mul_star G.C G.star _ (Module.finBasis ℚ G.C)
  obtain ⟨S4, hS4⟩ := GlobalTheory.T.eventually_integral_conjugators_differ_by_centralizer p G P₁.γ P₁.reg.1 P₁.reg.2 L ι hinj hcent _ (Module.finBasis ℚ G.C)
  obtain ⟨S5, hS5⟩ := GlobalTheory.T.almost_all_places_twisted_unit_integral G.C L ι hinj _ (Module.finBasis ℚ G.C) _ (Module.finBasis ℚ L)
  obtain ⟨S6, hS6⟩ := GlobalTheory.T.fixed_unit_eq_norm_almost_all_places L c hcc hcne _ (Module.finBasis ℚ L)
  refine ⟨S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6 ∪ (finite_above p).toFinset, ?_⟩
  intro P hγ hcP hex a ha v hv
  obtain ⟨x, t, hx, hxΩ⟩ := hex
  simp only [Finset.mem_union, not_or] at hv
  obtain ⟨⟨⟨⟨⟨⟨hv1, hv2⟩, hv3⟩, hv4⟩, hv5⟩, hv6⟩, hvp⟩ := hv
  have hvp' : v.asIdeal ≠ Ideal.span {(p : ℤ)} := fun h => hvp ((Set.Finite.mem_toFinset _).2 h)
  let w : AwayP p := ⟨v, hvp'⟩
  let K := v.adicCompletion ℚ
  let φ : AfP p ⊗[ℚ] G.C →ₐ[ℚ] K ⊗[ℚ] G.C := Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C)
  let ιv : K ⊗[ℚ] L →ₐ[ℚ] K ⊗[ℚ] G.C := Algebra.TensorProduct.map (AlgHom.id ℚ K) ι
  let cv : K ⊗[ℚ] L →ₐ[ℚ] K ⊗[ℚ] L := Algebra.TensorProduct.map (AlgHom.id ℚ K) c
  let X : (K ⊗[ℚ] G.C)ˣ := Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) x
  let X₁ : (K ⊗[ℚ] G.C)ˣ := Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) x₁
  have key : ∀ (Q : GlobalTheory.LKDef.DPair G) (y : (AfP p ⊗[ℚ] G.C)ˣ) (s : (AfP p)ˣ) (hy : Triv G (AfP p) Q.β y s),
      ((((GlobalTheory.OrbFinAf.piV G w (Q.toAf y s hy Q.self) : GlobalTheory.OrbFinAf.Gv G w) :
        (K ⊗[ℚ] G.C)ˣ × Kˣ).1 : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) =
        ↑(Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) y) * ((1 : K) ⊗ₜ[ℚ] (Q.γ : G.C)) *
          ↑(Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) y)⁻¹ := by
    intro Q y s hy
    show φ (↑y * ((1 : AfP p) ⊗ₜ[ℚ] (Q.γ : G.C)) * ↑y⁻¹) = _
    rw [map_mul, map_mul, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
    rfl
  have hXg : IsIntB v (Module.finBasis ℚ G.C) (↑X * ((1 : K) ⊗ₜ[ℚ] (P₁.γ : G.C)) * ↑X⁻¹) := by
    have h := (hS1 w hv1 ⟨_, hxΩ, rfl⟩).1
    rw [key P x t hx, hγ] at h
    exact h
  have hX₁g : IsIntB v (Module.finBasis ℚ G.C) (↑X₁ * ((1 : K) ⊗ₜ[ℚ] (P₁.γ : G.C)) * ↑X₁⁻¹) := by
    have h := (hS2 w hv2 ⟨_, rfl, rfl⟩).1
    rw [key P₁ x₁ t₁ hx₁] at h
    exact h

  obtain ⟨m, hm1, hm2⟩ := hS4 v hv4 X X₁ hXg hX₁g
  obtain ⟨hmul, hstar⟩ := hS3 v hv3
  let T : Kˣ := Units.map (AfP.eval w : AfP p →* K) t
  let T₁ : Kˣ := Units.map (AfP.eval w : AfP p →* K) t₁
  let β₁v : (K ⊗[ℚ] G.C)ˣ :=
    Units.map ((Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] K ⊗[ℚ] G.C) : G.C →* K ⊗[ℚ] G.C) P₁.β
  have hiota_a : ιv ((1 : K) ⊗ₜ[ℚ] a) * (β₁v : K ⊗[ℚ] G.C) = (1 : K) ⊗ₜ[ℚ] (P.β : G.C) := by
    show (1 : K) ⊗ₜ[ℚ] ι a * (1 : K) ⊗ₜ[ℚ] (P₁.β : G.C) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ha, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  have htriv : ∀ (Q : GlobalTheory.LKDef.DPair G) (y : (AfP p ⊗[ℚ] G.C)ˣ) (s : (AfP p)ˣ), Triv G (AfP p) Q.β y s →
      (↑(Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) y) : K ⊗[ℚ] G.C) * ((1 : K) ⊗ₜ[ℚ] (Q.β : G.C)) *
        (starT G.star K ↑(Units.map (φ : AfP p ⊗[ℚ] G.C →* K ⊗[ℚ] G.C) y)).unop =
        algebraMap K (K ⊗[ℚ] G.C) (AfP.eval w (s : AfP p)) := by
    intro Q y s hy
    have hy' : (y : AfP p ⊗[ℚ] G.C) * inC G (AfP p) Q.β * (starT G.star (AfP p) y).unop =
        algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s := hy
    have h := congrArg (Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C)) hy'
    rw [map_mul, map_mul, map_starT] at h
    have e1 : Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (inC G (AfP p) Q.β) =
        (1 : K) ⊗ₜ[ℚ] (Q.β : G.C) := by
      simp [inC, Algebra.TensorProduct.map_tmul]
    have e2 : Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) s) =
        algebraMap K (K ⊗[ℚ] G.C) (AfP.eval w (s : AfP p)) := by
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
    rw [e1, e2] at h
    exact h
  have h1 : (X : K ⊗[ℚ] G.C) * (ιv ((1 : K) ⊗ₜ[ℚ] a) * β₁v) * (starT G.star K X).unop =
      algebraMap K (K ⊗[ℚ] G.C) (T : K) := by
    rw [hiota_a]; exact htriv P x t hx
  have h2 : (X₁ : K ⊗[ℚ] G.C) * β₁v * (starT G.star K X₁).unop = algebraMap K (K ⊗[ℚ] G.C) (T₁ : K) :=
    htriv P₁ x₁ t₁ hx₁
  have hιR : ∀ r : K, ιv (algebraMap K (K ⊗[ℚ] L) r) = algebraMap K (K ⊗[ℚ] G.C) r := by
    intro r; simp [ιv, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  have hcm : ιv (cv ↑m) = ↑β₁v * (starT G.star K (ιv ↑m)).unop * ↑β₁v⁻¹ := map_conj_ext G K ι c P₁.β hc ↑m
  have hcore := selfDual_conj_eq_one (R := K) (ιv : K ⊗[ℚ] L →+* K ⊗[ℚ] G.C) hιR (starT G.star K) (cv : K ⊗[ℚ] L →+* K ⊗[ℚ] L)
    β₁v X X₁ T T₁ ((1 : K) ⊗ₜ[ℚ] a) m hcm h1 h2
  simp only [RingHom.coe_coe] at hcore

  have hu'u : ((X₁ : K ⊗[ℚ] G.C) * ιv ↑m⁻¹ * ↑X⁻¹) * ((X : K ⊗[ℚ] G.C) * ιv ↑m * ↑X₁⁻¹) = 1 := by
    calc ((X₁ : K ⊗[ℚ] G.C) * ιv ↑m⁻¹ * ↑X⁻¹) * ((X : K ⊗[ℚ] G.C) * ιv ↑m * ↑X₁⁻¹)
        = (X₁ : K ⊗[ℚ] G.C) * (ιv ↑m⁻¹ * ((↑X⁻¹ : K ⊗[ℚ] G.C) * ↑X) * ιv ↑m) * ↑X₁⁻¹ := by
          simp only [mul_assoc]
      _ = 1 := by rw [Units.inv_mul, mul_one, ← map_mul, Units.inv_mul, map_one, mul_one, Units.mul_inv]
  have hshu : (starT G.star K ((X : K ⊗[ℚ] G.C) * ιv ↑m * ↑X₁⁻¹)).unop *
      (starT G.star K ((X₁ : K ⊗[ℚ] G.C) * ιv ↑m⁻¹ * ↑X⁻¹)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, hu'u, map_one, MulOpposite.unop_one]
  set u := (X : K ⊗[ℚ] G.C) * ιv ↑m * ↑X₁⁻¹ with hu
  set u' := (X₁ : K ⊗[ℚ] G.C) * ιv ↑m⁻¹ * ↑X⁻¹ with hu'
  set E := algebraMap K (K ⊗[ℚ] L) (↑T⁻¹ * ↑T₁) * ((1 : K) ⊗ₜ[ℚ] a) * (↑m⁻¹ * cv ↑m⁻¹) with hE
  set wv := (X₁ : K ⊗[ℚ] G.C) * ιv E * ↑X₁⁻¹ with hwvdef
  have hwv : wv = u' * (starT G.star K u').unop := by
    calc wv = (u' * u) * wv * ((starT G.star K u).unop * (starT G.star K u').unop) := by
          rw [hu'u, hshu, one_mul, mul_one]
      _ = u' * (u * wv * (starT G.star K u).unop) * (starT G.star K u').unop := by simp only [mul_assoc]
      _ = _ := by rw [hcore, mul_one]
  have hwvI : IsIntB v (Module.finBasis ℚ G.C) wv := hwv ▸ hmul _ _ hm2 (hstar _ hm2)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact (Units.ne_zero _) ha.symm
  obtain ⟨Eu, hEu⟩ : ∃ Eu : (K ⊗[ℚ] L)ˣ, (Eu : K ⊗[ℚ] L) = E :=
    ⟨Units.map (algebraMap K (K ⊗[ℚ] L) : K →* K ⊗[ℚ] L) (T⁻¹ * T₁) *
      Units.map ((Algebra.TensorProduct.includeRight : L →ₐ[ℚ] K ⊗[ℚ] L) : L →* K ⊗[ℚ] L) (Units.mk0 a ha0) *
        (m⁻¹ * Units.map (cv : K ⊗[ℚ] L →* K ⊗[ℚ] L) m⁻¹), by
      simp only [Units.val_mul, Units.coe_map, Units.val_mk0, hE, map_mul]
      rfl⟩
  have h_a : ((X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹) * wv = 1 := by
    rw [hwvdef, ← hEu]
    calc ((X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹) * ((X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu * ↑X₁⁻¹)
        = (X₁ : K ⊗[ℚ] G.C) * (ιv ↑Eu⁻¹ * ((↑X₁⁻¹ : K ⊗[ℚ] G.C) * ↑X₁) * ιv ↑Eu) * ↑X₁⁻¹ := by
          simp only [mul_assoc]
      _ = 1 := by rw [Units.inv_mul X₁, mul_one, ← map_mul ιv, Units.inv_mul Eu, map_one, mul_one, Units.mul_inv X₁]
  have h_b : wv * ((starT G.star K u).unop * u) = 1 := by
    calc wv * ((starT G.star K u).unop * u) = (u' * u) * wv * (starT G.star K u).unop * u := by
          rw [hu'u, one_mul]; simp only [mul_assoc]
      _ = u' * (u * wv * (starT G.star K u).unop) * u := by simp only [mul_assoc]
      _ = 1 := by rw [hcore, mul_one, hu'u]
  have hwv' : (X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹ = (starT G.star K u).unop * u := by
    calc (X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹
        = ((X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹) * (wv * ((starT G.star K u).unop * u)) := by rw [h_b, mul_one]
      _ = (((X₁ : K ⊗[ℚ] G.C) * ιv ↑Eu⁻¹ * ↑X₁⁻¹) * wv) * ((starT G.star K u).unop * u) := by
          rw [← mul_assoc]
      _ = _ := by rw [h_a, one_mul]
  have hE1 : IsIntB v (Module.finBasis ℚ L) (Eu : K ⊗[ℚ] L) := hS5 v hv5 X₁ _ (by rw [hEu]; exact hwvI)
  have hE2 : IsIntB v (Module.finBasis ℚ L) ((Eu⁻¹ : (K ⊗[ℚ] L)ˣ) : K ⊗[ℚ] L) :=
    hS5 v hv5 X₁ _ (by rw [hwv']; exact hmul _ _ (hstar _ hm1) hm1)
  have hca : c a = a := hinj (by
    rw [hc, ha, Units.val_mul, sh_mul', hβ₁inv, P.sym]
    simp only [mul_assoc, Units.mul_inv_cancel_left])
  have hcalg : ∀ r : K, cv (algebraMap K (K ⊗[ℚ] L) r) = algebraMap K (K ⊗[ℚ] L) r := by
    intro r; simp [cv, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  have hcinv : cv (cv ↑m⁻¹) = ↑m⁻¹ := map_invol c hcc _
  have hfix : cv ↑Eu = ↑Eu := by
    have : cv ((1 : K) ⊗ₜ[ℚ] a) = (1 : K) ⊗ₜ[ℚ] a := by
      show (1 : K) ⊗ₜ[ℚ] c a = _
      rw [hca]
    rw [hEu, hE]
    simp only [map_mul, hcalg, hcinv, this]
    ring
  obtain ⟨y₀, hy₀⟩ := hS6 v hv6 Eu hfix hE1 hE2
  refine ⟨T * T₁⁻¹, m * y₀, ?_⟩
  rw [hEu, hE, map_mul] at hy₀
  have hm' : (m : K ⊗[ℚ] L) * ↑m⁻¹ = 1 := Units.mul_inv m
  have hcm' : cv ↑m * cv ↑m⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hT : algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hT₁ : algebraMap K (K ⊗[ℚ] L) ↑T₁ * algebraMap K (K ⊗[ℚ] L) ↑T₁⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  show (1 : K) ⊗ₜ[ℚ] a = algebraMap K (K ⊗[ℚ] L) ↑(T * T₁⁻¹) * (↑(m * y₀) * cv ↑(m * y₀))
  rw [Units.val_mul, Units.val_mul, map_mul, map_mul]
  linear_combination (algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T₁⁻¹ * ↑m * cv ↑m) * hy₀ -
    ((1 : K) ⊗ₜ[ℚ] a) * hT - ((1 : K) ⊗ₜ[ℚ] a) * algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T⁻¹ * hT₁ -
    ((1 : K) ⊗ₜ[ℚ] a) * algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T⁻¹ *
      algebraMap K (K ⊗[ℚ] L) ↑T₁ * algebraMap K (K ⊗[ℚ] L) ↑T₁⁻¹ * hm' -
    ((1 : K) ⊗ₜ[ℚ] a) * algebraMap K (K ⊗[ℚ] L) ↑T * algebraMap K (K ⊗[ℚ] L) ↑T⁻¹ *
      algebraMap K (K ⊗[ℚ] L) ↑T₁ * algebraMap K (K ⊗[ℚ] L) ↑T₁⁻¹ * ↑m * ↑m⁻¹ * hcm'

end GlobalTheory.LocTriv
