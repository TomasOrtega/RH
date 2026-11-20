import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBaseEqChain
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictPushforwardUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EAComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbCompEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPowerEmbedding

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.ChainParts
open scoped Classical

noncomputable section
namespace GlobalTheory.IdemCoef

/- English proof (translation)
Use `set X : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => M (e j) i with hX`. Set `cf : ι → Fin n → R` to `fun τ k => X⁻¹ (e.symm τ) k`. Establish `h1 : ∀ τ σ, ∑ k, cf τ k * M σ k = if σ = τ then 1 else 0` using `fun τ σ => by`. Use `congrFun (congrFun (Matrix.nonsing_inv_mul X hM) (e.symm τ)) (e.symm σ)` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`.

Simplify using `only [hX, Matrix.of_apply, Equiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq] at this`. Rewrite using `[if_congr eq_comm rfl rfl, ← this]`. Establish `h2 : ∀ i k, ∑ σ, M σ i * cf σ k = if i = k then 1 else 0` using `fun i k => by`. Use `congrFun (congrFun (Matrix.mul_nonsing_inv X hM) i) k` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Matrix.one_apply]`.

Rewrite using `[← this, ← e.sum_comp]`. Simplify using `only [hX, Matrix.of_apply, cf, Equiv.symm_apply_apply]`. Use `⟨cf, h1, fun τ k => ?_⟩` and prove the remaining obligations. Set `I : Ideal R` to `Ideal.span {(p : R)}`. Use `haveI : CharP (R ⧸ I) p := CharP.quotient R p hpR`.

Set `q` to `Ideal.Quotient.mk I`. Establish `hq : ∀ σ k, q (M (φ σ) k) = q (M σ k) ^ p` using `fun σ k => by`. Take `⟨v, hv⟩` from `hc σ k`. Rewrite using `[hv, map_add, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero, map_pow]`. Establish `h3 : ∀ σ, ∑ i, (q (cf (φ τ) i) - q (cf τ i) ^ p) * q (M σ i) = 0` using `fun σ => by`.

Take `⟨σ, rfl⟩` from `Finite.injective_iff_surjective.1 hφ σ`. Establish `a` using `congrArg q (h1 (φ τ) (φ σ))`. Establish `b` using `congrArg (fun x => q x ^ p) (h1 τ σ)`. Simplify using `only [map_sum, map_mul, hφ.eq_iff] at a`. Simplify using `only [map_sum, map_mul, sum_pow_char, mul_pow, ← hq] at b`.

Simplify using `only [sub_mul, Finset.sum_sub_distrib]`. Rewrite using `[a, b]`. Apply the tactic sequence `split_ifs <;> simp [hp.out.ne_zero]`. Establish `h4 : q (cf (φ τ) k) - q (cf τ k) ^ p = 0`. Establish `: ∑ σ, (∑ i, (q (cf (φ τ) i) - q (cf τ i) ^ p) * q (M σ i)) * q (cf σ k) = 0` using `by simp only [h3, zero_mul, Finset.sum_const_zero]`.

Simplify using `only [Finset.sum_mul] at this`. Rewrite `this` using `[Finset.sum_comm]`. Simplify using `only [mul_assoc, ← Finset.mul_sum, ← map_mul, ← map_sum, h2] at this`. Rewrite `this` using `[Finset.sum_eq_single k (fun i _ hi => by rw [if_neg hi, map_zero, mul_zero]) (by simp), if_pos rfl, map_one, mul_one]`. Conclude with `this`.

Rewrite `h4` using `[← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Take `⟨v, hv⟩` from `h4`. Conclude with `⟨v, by rw [← hv]; ring⟩`.
-/
theorem exists_inv_rows {R ι : Type} [CommRing R] [Fintype ι] {n : ℕ} (e : Fin n ≃ ι) (p : ℕ) [hp : Fact p.Prime]
    (hpR : ¬ IsUnit (p : R)) (M : ι → Fin n → R) (hM : IsUnit (Matrix.of fun i j => M (e j) i).det)
    (φ : ι → ι) (hφ : Function.Injective φ) (hc : ∀ σ k, ∃ v : R, M (φ σ) k = M σ k ^ p + p * v) :
    ∃ cf : ι → Fin n → R, (∀ τ σ, ∑ k, cf τ k * M σ k = if σ = τ then 1 else 0) ∧
      ∀ τ k, ∃ v : R, cf (φ τ) k = cf τ k ^ p + p * v := by
  set X : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => M (e j) i with hX
  let cf : ι → Fin n → R := fun τ k => X⁻¹ (e.symm τ) k
  have h1 : ∀ τ σ, ∑ k, cf τ k * M σ k = if σ = τ then 1 else 0 := fun τ σ => by
    have := congrFun (congrFun (Matrix.nonsing_inv_mul X hM) (e.symm τ)) (e.symm σ)
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simp only [hX, Matrix.of_apply, Equiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq] at this
    rw [if_congr eq_comm rfl rfl, ← this]
  have h2 : ∀ i k, ∑ σ, M σ i * cf σ k = if i = k then 1 else 0 := fun i k => by
    have := congrFun (congrFun (Matrix.mul_nonsing_inv X hM) i) k
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this, ← e.sum_comp]
    simp only [hX, Matrix.of_apply, cf, Equiv.symm_apply_apply]
  refine ⟨cf, h1, fun τ k => ?_⟩
  let I : Ideal R := Ideal.span {(p : R)}
  haveI : CharP (R ⧸ I) p := CharP.quotient R p hpR
  let q := Ideal.Quotient.mk I
  have hq : ∀ σ k, q (M (φ σ) k) = q (M σ k) ^ p := fun σ k => by
    obtain ⟨v, hv⟩ := hc σ k
    rw [hv, map_add, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero, map_pow]
  have h3 : ∀ σ, ∑ i, (q (cf (φ τ) i) - q (cf τ i) ^ p) * q (M σ i) = 0 := fun σ => by
    obtain ⟨σ, rfl⟩ := Finite.injective_iff_surjective.1 hφ σ
    have a := congrArg q (h1 (φ τ) (φ σ))
    have b := congrArg (fun x => q x ^ p) (h1 τ σ)
    simp only [map_sum, map_mul, hφ.eq_iff] at a
    simp only [map_sum, map_mul, sum_pow_char, mul_pow, ← hq] at b
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [a, b]
    split_ifs <;> simp [hp.out.ne_zero]
  have h4 : q (cf (φ τ) k) - q (cf τ k) ^ p = 0 := by
    have : ∑ σ, (∑ i, (q (cf (φ τ) i) - q (cf τ i) ^ p) * q (M σ i)) * q (cf σ k) = 0 := by simp only [h3, zero_mul, Finset.sum_const_zero]
    simp only [Finset.sum_mul] at this
    rw [Finset.sum_comm] at this
    simp only [mul_assoc, ← Finset.mul_sum, ← map_mul, ← map_sum, h2] at this
    rw [Finset.sum_eq_single k (fun i _ hi => by rw [if_neg hi, map_zero, mul_zero]) (by simp), if_pos rfl, map_one, mul_one] at this
    exact this
  rw [← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h4
  obtain ⟨v, hv⟩ := h4
  exact ⟨v, by rw [← hv]; ring⟩

/- English proof (translation)
Establish `h` using `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ (b.localizationLocalization ℚ (nonZeroDivisors ℤ) E) (e.trans (RingHom.equivRatAlgHom E ℂ))`. Rewrite `h` using `[Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) E, discr_eq_discr]`. Rewrite using `[show ((discr E : ℤ) : ℂ) = algebraMap ℚ ℂ (algebraMap ℤ ℚ (discr E)) by simp, h]`. Use `congr 2`. Use extensionality with `i j`.

Simplify using `[Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, Module.Basis.localizationLocalization_apply]`.
-/
theorem det_sq_eq_discr (E : Type) [Field E] [NumberField E] {n : ℕ} (b : Module.Basis (Fin n) ℤ (𝓞 E))
    (e : Fin n ≃ (E →+* ℂ)) : (Matrix.of fun i j => e j (b i : E)).det ^ 2 = (discr E : ℂ) := by
  have h := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ
    (b.localizationLocalization ℚ (nonZeroDivisors ℤ) E) (e.trans (RingHom.equivRatAlgHom E ℂ))
  rw [Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) E, discr_eq_discr] at h
  rw [show ((discr E : ℤ) : ℂ) = algebraMap ℚ ℂ (algebraMap ℤ ℚ (discr E)) by simp, h]
  congr 2
  ext i j
  simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, Module.Basis.localizationLocalization_apply]

/- English proof (translation)
Take `⟨g, hg⟩` from `GO.PlWitt.exists_intHom (O := WittVector p (AlgebraicClosure (ZMod p))) τ`. Establish `h : WittVector.frobenius (g x) - g x ^ p ∈ RingHom.ker (WittVector.constantCoeff (p` using `p) (R := AlgebraicClosure (ZMod p))) := by`. Rewrite using `[RingHom.mem_ker, map_sub, map_pow, sub_eq_zero]`. Conclude with `WittVector.coeff_frobenius_charP p (g x) 0`. Rewrite `h` using `[WittVector.ker_constantCoeff, Ideal.mem_span_singleton]`.

Take `⟨w, hw⟩` from `h`. Use `⟨w, ?_⟩` and prove the remaining obligations. Establish `h3` using `congrArg (algebraMap _ (KW p)) hw`. Rewrite `h3` using `[map_sub, map_pow, map_mul, map_natCast, ← SqrtUnif.fractionRing_frobenius_algebraMap, hg]`. Rewrite using `[← h3]`.

Simplify using `only [sgF]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sgF_emb {E : Type} [Field E] [NumberField E] (p : ℕ) [hp : Fact p.Prime] (τ : E →+* KW p) (x : 𝓞 E) :
    ∃ w : WittVector p (AlgebraicClosure (ZMod p)), sgF p (τ x) = τ x ^ p + p * algebraMap _ (KW p) w := by
  obtain ⟨g, hg⟩ := GO.PlWitt.exists_intHom (O := WittVector p (AlgebraicClosure (ZMod p))) τ
  have h : WittVector.frobenius (g x) - g x ^ p ∈ RingHom.ker (WittVector.constantCoeff (p := p) (R := AlgebraicClosure (ZMod p))) := by
    rw [RingHom.mem_ker, map_sub, map_pow, sub_eq_zero]
    exact WittVector.coeff_frobenius_charP p (g x) 0
  rw [WittVector.ker_constantCoeff, Ideal.mem_span_singleton] at h
  obtain ⟨w, hw⟩ := h
  refine ⟨w, ?_⟩
  have h3 := congrArg (algebraMap _ (KW p)) hw
  rw [map_sub, map_pow, map_mul, map_natCast, ← SqrtUnif.fractionRing_frobenius_algebraMap, hg] at h3
  rw [← h3]
  simp only [sgF]
  ring

/- English proof (translation)
Establish `hsurj : ∀ σ' : D.host.E →+* ℂ, ∃ σ : Emb D p, σ' = jc.comp σ` using `fun σ' => by`. Take `⟨g, hg⟩` from `(factEmb D.R D.host).1.2 σ'`. Take `⟨τ, hτ⟩` from `GlobalTheory.UnramEmb.exists_emb_comp_eq D p hun jc g`. Conclude with `⟨τ, by rw [hτ, hg]⟩`. Establish `hbij : Function.Bijective (fun σ : Emb D p => jc.comp σ)` using `⟨fun σ τ h => RingHom.ext fun x => jc.injective (RingHom.congr_fun h x), fun σ' => (hsurj σ').imp fun _ h => h.symm⟩`.

Set `ε : Emb D p ≃ (D.host.E →+* ℂ)` to `Equiv.ofBijective _ hbij`. Use `haveI hfin : Finite (Emb D p) := Finite.of_equiv _ ε.symm`. Use `letI := Fintype.ofFinite (Emb D p)`. Establish `hcard : Nat.card (Emb D p) = Module.finrank ℤ (𝓞 D.host.E)`. Rewrite using `[Nat.card_congr ε, Nat.card_eq_fintype_card, Embeddings.card, RingOfIntegers.rank]`.

Set `b` to `Module.finBasis ℤ (𝓞 D.host.E)`. Set `e : Fin (Module.finrank ℤ (𝓞 D.host.E)) ≃ Emb D p` to `(Finite.equivFinOfCardEq hcard).symm`. Establish `hmem : ∀ (σ : Emb D p) (x : 𝓞 D.host.E), embK c (jc.comp σ) x ∈ c.V W` using `fun σ x => by`. Take `⟨g, hg⟩` from `GO.PlWitt.exists_intHom (O := WittVector p (AlgebraicClosure (ZMod p))) σ`. Conclude with `(hjc (σ x)).2 ⟨g x, hg x⟩`.

Set `ev : Emb D p → (𝓞 D.host.E →+* c.V W)` to `fun σ => (embK c (jc.comp σ)).codRestrict (c.V W).toSubring (hmem σ)`. Set `ι : c.V W →+* ℂ` to `c.F.val.toRingHom.comp (c.V W).subtype`. Establish `hι : Function.Injective ι` using `Subtype.val_injective.comp Subtype.val_injective`. Establish `hev : ∀ σ x, ι (ev σ x) = jc (σ x)` using `fun σ x => rfl`. Establish `hpV : ¬ IsUnit (p : c.V W)` using `fun h => by`.

Take `⟨u, hu⟩` from `h.exists_right_inv`. Establish `h1 : (p : ℂ) * ι u = 1` using `by rw [← map_natCast ι, ← map_mul, hu, map_one]`. Establish `h2 : W.valuation (ι u) ≤ 1` using `(W.valuation_le_one_iff _).2 u.2`. Establish `h3 : W.valuation (p : ℂ) < 1` using `W.mem_nonunits_iff.1 hW`. Establish `h4 : W.valuation (p : ℂ) * W.valuation (ι u) < 1` using `lt_of_le_of_lt (mul_le_of_le_one_right' h2) h3`.

Rewrite `h4` using `[← map_mul, h1, map_one]`. Conclude with `lt_irrefl _ h4`. Establish `hdet : IsUnit (Matrix.of fun i j => ev (e j) (b i)).det`. Establish `h1 : (Matrix.of fun i j => ev (e j) (b i)).det ^ 2 = (discr D.host.E : c.V W)`. Apply `hι` to reduce the goal to its premises.

Rewrite using `[map_pow, RingHom.map_det, map_intCast, ← det_sq_eq_discr D.host.E b (e.trans ε)]`. Both sides reduce to the same expression. Establish `h2 : IsUnit (discr D.host.E : c.V W)`. Establish `hcop : IsCoprime (p : ℤ) (discr D.host.E)` using `(Nat.prime_iff_prime_int.1 hp.out).irreducible.coprime_iff_not_dvd.2 fun hd => hun (Int.natCast_dvd.1 hd)`. Take `⟨u, v, huv⟩` from `hcop`.

Establish `h3 : (u : c.V W) * p + v * (discr D.host.E : c.V W) = 1` using `by exact_mod_cast congrArg (Int.cast : ℤ → c.V W) huv`. Break down `IsLocalRing.isUnit_or_isUnit_of_add_one h3 with h | h` into its components or cases. Conclude with `(hpV (isUnit_of_mul_isUnit_right h)).elim`. Conclude with `isUnit_of_mul_isUnit_right h`. Rewrite `h2` using `[← h1]`.

Conclude with `(isUnit_pow_iff two_ne_zero).1 h2`. Establish `hφ : Function.Injective (phiPow D (p` using `p) 1) := fun τ τ' h => by`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Use `RingHom.congr_fun h x` as an intermediate fact. Simplify using `only [phiPow, pow_one, RingHom.comp_apply] at this`.

Conclude with `(sgF p).injective this`. Establish `hc : ∀ (σ : Emb D p) x, ∃ v : c.V W, ev (phiPow D 1 σ) x = ev σ x ^ p + p * v` using `fun σ x => by`. Take `⟨w, hw⟩` from `sgF_emb p σ x`. Establish `hp0 : (p : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hp.out.ne_zero`. Establish `h1 : ι (ev (phiPow D 1 σ) x) = ι (ev σ x) ^ p + p * jc (algebraMap _ (KW p) w)`.

Rewrite using `[hev, hev, ← map_pow, ← map_natCast jc, ← map_mul, ← map_add, ← hw, phiPow, pow_one]`. Both sides reduce to the same expression. Establish `h2 : jc (algebraMap _ (KW p) w) = (ι (ev (phiPow D 1 σ) x) - ι (ev σ x) ^ p) / p`. Rewrite using `[h1]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `h3 : jc (algebraMap _ (KW p) w) ∈ c.F`. Rewrite using `[h2]`. Conclude with `div_mem (sub_mem (ev (phiPow D 1 σ) x).1.2 (pow_mem (ev σ x).1.2 p)) (natCast_mem _ p)`. Use `⟨⟨⟨_, h3⟩, (hjc _).2 ⟨w, rfl⟩⟩, hι ?_⟩` and prove the remaining obligations.

Rewrite using `[h1, map_add, map_mul, map_pow, map_natCast]`. Both sides reduce to the same expression. Take `⟨cf, h1, h2⟩` from `exists_inv_rows e p hpV (fun σ k => ev σ (b k)) hdet _ hφ (fun σ k => hc σ (b k))`. Conclude with `⟨_, b, ev, cf, hfin, hcard, fun _ _ => rfl, hsurj, h1, h2⟩`.
-/
theorem exists_coef_of_coeff {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l : Level H} (c : Coeff l)
    {p : ℕ} [hp : Fact p.Prime] {W : ValuationSubring ℂ} (hW : (p : ℂ) ∈ W.nonunits)
    (jc : KW p →+* ℂ) (hjc : Pin W jc) (hun : UnramE D p) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (𝓞 D.host.E)) (ev : Emb D p → (𝓞 D.host.E →+* c.V W))
      (cf : Emb D p → Fin n → c.V W),
      Finite (Emb D p) ∧ Nat.card (Emb D p) = n ∧
      (∀ σ x, ((ev σ x : c.V W) : c.F) = embK c (jc.comp σ) x) ∧
      (∀ σ' : D.host.E →+* ℂ, ∃ σ : Emb D p, σ' = jc.comp σ) ∧
      (∀ τ σ : Emb D p, ∑ k, cf τ k * ev σ (b k) = if σ = τ then 1 else 0) ∧
      (∀ τ k, ∃ v : c.V W, cf (phiPow D 1 τ) k = cf τ k ^ p + p * v) := by
  have hsurj : ∀ σ' : D.host.E →+* ℂ, ∃ σ : Emb D p, σ' = jc.comp σ := fun σ' => by
    obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 σ'
    obtain ⟨τ, hτ⟩ := GlobalTheory.UnramEmb.exists_emb_comp_eq D p hun jc g
    exact ⟨τ, by rw [hτ, hg]⟩
  have hbij : Function.Bijective (fun σ : Emb D p => jc.comp σ) :=
    ⟨fun σ τ h => RingHom.ext fun x => jc.injective (RingHom.congr_fun h x),
      fun σ' => (hsurj σ').imp fun _ h => h.symm⟩
  let ε : Emb D p ≃ (D.host.E →+* ℂ) := Equiv.ofBijective _ hbij
  haveI hfin : Finite (Emb D p) := Finite.of_equiv _ ε.symm
  letI := Fintype.ofFinite (Emb D p)
  have hcard : Nat.card (Emb D p) = Module.finrank ℤ (𝓞 D.host.E) := by
    rw [Nat.card_congr ε, Nat.card_eq_fintype_card, Embeddings.card, RingOfIntegers.rank]
  let b := Module.finBasis ℤ (𝓞 D.host.E)
  let e : Fin (Module.finrank ℤ (𝓞 D.host.E)) ≃ Emb D p := (Finite.equivFinOfCardEq hcard).symm
  have hmem : ∀ (σ : Emb D p) (x : 𝓞 D.host.E), embK c (jc.comp σ) x ∈ c.V W := fun σ x => by
    obtain ⟨g, hg⟩ := GO.PlWitt.exists_intHom (O := WittVector p (AlgebraicClosure (ZMod p))) σ
    exact (hjc (σ x)).2 ⟨g x, hg x⟩
  let ev : Emb D p → (𝓞 D.host.E →+* c.V W) := fun σ => (embK c (jc.comp σ)).codRestrict (c.V W).toSubring (hmem σ)
  let ι : c.V W →+* ℂ := c.F.val.toRingHom.comp (c.V W).subtype
  have hι : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  have hev : ∀ σ x, ι (ev σ x) = jc (σ x) := fun σ x => rfl
  have hpV : ¬ IsUnit (p : c.V W) := fun h => by
    obtain ⟨u, hu⟩ := h.exists_right_inv
    have h1 : (p : ℂ) * ι u = 1 := by rw [← map_natCast ι, ← map_mul, hu, map_one]
    have h2 : W.valuation (ι u) ≤ 1 := (W.valuation_le_one_iff _).2 u.2
    have h3 : W.valuation (p : ℂ) < 1 := W.mem_nonunits_iff.1 hW
    have h4 : W.valuation (p : ℂ) * W.valuation (ι u) < 1 := lt_of_le_of_lt (mul_le_of_le_one_right' h2) h3
    rw [← map_mul, h1, map_one] at h4
    exact lt_irrefl _ h4
  have hdet : IsUnit (Matrix.of fun i j => ev (e j) (b i)).det := by
    have h1 : (Matrix.of fun i j => ev (e j) (b i)).det ^ 2 = (discr D.host.E : c.V W) := by
      apply hι
      rw [map_pow, RingHom.map_det, map_intCast, ← det_sq_eq_discr D.host.E b (e.trans ε)]
      rfl
    have h2 : IsUnit (discr D.host.E : c.V W) := by
      have hcop : IsCoprime (p : ℤ) (discr D.host.E) :=
        (Nat.prime_iff_prime_int.1 hp.out).irreducible.coprime_iff_not_dvd.2 fun hd => hun (Int.natCast_dvd.1 hd)
      obtain ⟨u, v, huv⟩ := hcop
      have h3 : (u : c.V W) * p + v * (discr D.host.E : c.V W) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → c.V W) huv
      rcases IsLocalRing.isUnit_or_isUnit_of_add_one h3 with h | h
      · exact (hpV (isUnit_of_mul_isUnit_right h)).elim
      · exact isUnit_of_mul_isUnit_right h
    rw [← h1] at h2
    exact (isUnit_pow_iff two_ne_zero).1 h2
  have hφ : Function.Injective (phiPow D (p := p) 1) := fun τ τ' h => by
    refine RingHom.ext fun x => ?_
    have := RingHom.congr_fun h x
    simp only [phiPow, pow_one, RingHom.comp_apply] at this
    exact (sgF p).injective this
  have hc : ∀ (σ : Emb D p) x, ∃ v : c.V W, ev (phiPow D 1 σ) x = ev σ x ^ p + p * v := fun σ x => by
    obtain ⟨w, hw⟩ := sgF_emb p σ x
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
    have h1 : ι (ev (phiPow D 1 σ) x) = ι (ev σ x) ^ p + p * jc (algebraMap _ (KW p) w) := by
      rw [hev, hev, ← map_pow, ← map_natCast jc, ← map_mul, ← map_add, ← hw, phiPow, pow_one]
      rfl
    have h2 : jc (algebraMap _ (KW p) w) = (ι (ev (phiPow D 1 σ) x) - ι (ev σ x) ^ p) / p := by
      rw [h1]; field_simp; ring
    have h3 : jc (algebraMap _ (KW p) w) ∈ c.F := by
      rw [h2]
      exact div_mem (sub_mem (ev (phiPow D 1 σ) x).1.2 (pow_mem (ev σ x).1.2 p)) (natCast_mem _ p)
    refine ⟨⟨⟨_, h3⟩, (hjc _).2 ⟨w, rfl⟩⟩, hι ?_⟩
    rw [h1, map_add, map_mul, map_pow, map_natCast]
    rfl
  obtain ⟨cf, h1, h2⟩ := exists_inv_rows e p hpV (fun σ k => ev σ (b k)) hdet _ hφ (fun σ k => hc σ (b k))
  exact ⟨_, b, ev, cf, hfin, hcard, fun _ _ => rfl, hsurj, h1, h2⟩

/- English proof (translation)
Introduce `D A N j S κ p _ hp W hW z jc hjc hun`. Conclude with `exists_coef_of_coeff z.Z.i.c hW jc hjc hun`.
-/
theorem exists_coef : ∀ {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime} {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) (jc : KW p →+* ℂ) (hjc : Pin W jc) (hun : UnramE D p), ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (𝓞 D.host.E)) (ev : Emb D p → (𝓞 D.host.E →+* z.Z.i.c.V W))
      (cf : Emb D p → Fin n → z.Z.i.c.V W),
      Finite (Emb D p) ∧ Nat.card (Emb D p) = n ∧
      (∀ σ x, ((ev σ x : z.Z.i.c.V W) : z.Z.i.c.F) = embK z.Z.i.c (jc.comp σ) x) ∧
      (∀ σ' : D.host.E →+* ℂ, ∃ σ : Emb D p, σ' = jc.comp σ) ∧
      (∀ τ σ : Emb D p, ∑ k, cf τ k * ev σ (b k) = if σ = τ then 1 else 0) ∧
      (∀ τ k, ∃ v : z.Z.i.c.V W, cf (phiPow D 1 τ) k = cf τ k ^ p + p * v) := by
  intro D A N j S κ p _ hp W hW z jc hjc hun
  exact exists_coef_of_coeff z.Z.i.c hW jc hjc hun

end GlobalTheory.IdemCoef
