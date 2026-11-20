import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegPhi

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

/- English proof (translation)
Establish `e1 : ∀ q : (Σ k, ι' k) →₀ ℕ, ∑ i, q ⟨k', i⟩ = q.sum (fun r x => if r.1 = k' then x else 0)`. Introduce `q`. Rewrite using `[Finsupp.sum_fintype _ _ (fun r => by simp), Fintype.sum_sigma, Finset.sum_eq_single k' (fun b _ hb => by simp [hb]) (by simp)]`. Simplify using the standard rewrite rules. Establish `e2 : ∑ p : Σ k, ι k, (if κ p.1 = k' then m p else 0) = m.sum (fun p x => if κ p.1 = k' then x else 0)`.

Rewrite using `[Finsupp.sum_fintype _ _ (fun r => by simp)]`. Apply the tactic sequence `rw [e1, e2, Finsupp.sum_mapDomain_index (fun r => by simp) (fun r a b => by split_ifs <;> simp)]`. Simplify using `only [hv]`.
-/
theorem sum_mapDomain_block {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : ∀ p, (v p).1 = κ p.1)
    (m : (Σ k, ι k) →₀ ℕ) (k' : K') :
    ∑ i, (Finsupp.mapDomain v m) ⟨k', i⟩ = ∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0 := by
  have e1 : ∀ q : (Σ k, ι' k) →₀ ℕ, ∑ i, q ⟨k', i⟩ = q.sum (fun r x => if r.1 = k' then x else 0) := by
    intro q
    rw [Finsupp.sum_fintype _ _ (fun r => by simp), Fintype.sum_sigma,
      Finset.sum_eq_single k' (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have e2 : ∑ p : Σ k, ι k, (if κ p.1 = k' then m p else 0) = m.sum (fun p x => if κ p.1 = k' then x else 0) := by
    rw [Finsupp.sum_fintype _ _ (fun r => by simp)]
  rw [e1, e2, Finsupp.sum_mapDomain_index (fun r => by simp) (fun r a b => by split_ifs <;> simp)]
  simp only [hv]

/- English proof (translation)
Introduce `m hm k'`. Rewrite `hm` using `[support_rename_of_injective hb.2.1, Finset.mem_image]`. Take `⟨m0, hm0, rfl⟩` from `hm`. Rewrite using `[sum_mapDomain_block hb.2.2.1]`. Distinguish the cases in `hk : ∃ k, κ k = k'`.

Take `⟨k, rfl⟩` from `hk`. Rewrite using `[hb.1.extend_apply, ← hf m0 hm0 k]`. Simplify using `only [hb.1.eq_iff]`. Rewrite using `[Fintype.sum_sigma, Finset.sum_eq_single k (fun b _ hb' => by simp [hb']) (by simp)]`. Simplify using the standard rewrite rules.

Rewrite using `[Function.extend_apply' _ _ _ hk, Pi.zero_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `p _`. Rewrite using `[if_neg (fun h => hk ⟨p.1, h⟩)]`.
-/
theorem isMultiHomog_rename_block {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v) {f : MRing ι}
    {b : K → ℕ} (hf : IsMultiHomog f b) : IsMultiHomog (rename v f) (Function.extend κ b 0) := by
  intro m hm k'
  rw [support_rename_of_injective hb.2.1, Finset.mem_image] at hm
  obtain ⟨m0, hm0, rfl⟩ := hm
  rw [sum_mapDomain_block hb.2.2.1]
  by_cases hk : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [hb.1.extend_apply, ← hf m0 hm0 k]
    simp only [hb.1.eq_iff]
    rw [Fintype.sum_sigma, Finset.sum_eq_single k (fun b _ hb' => by simp [hb']) (by simp)]
    simp
  · rw [Function.extend_apply' _ _ _ hk, Pi.zero_apply]
    apply Finset.sum_eq_zero
    intro p _
    rw [if_neg (fun h => hk ⟨p.1, h⟩)]

/- English proof (translation)
Simplify using `only [mConeMap]`. Rewrite using `[aeval_rename]`. Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a`. Simplify using the standard rewrite rules.

Consider the case `add p q hp hq`. Simplify using `[hp, hq]`. Consider the case `mul_X p i hp`. Simplify using `[hp, hb.2.2.1 i]`.
-/
theorem mConeMap_rename {Ω : Type} [Field Ω] {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v)
    (y : (Σ k, ι' k) → Ω) (g : MRing ι) : mConeMap y (rename v g) = rename κ (mConeMap (y ∘ v) g) := by
  simp only [mConeMap]
  rw [aeval_rename]
  induction g using MvPolynomial.induction_on with
  | C a =>
    simp
  | add p q hp hq =>
    simp [hp, hq]
  | mul_X p i hp =>
    simp [hp, hb.2.2.1 i]

/- English proof (translation)
Simplify using `only [mConeMap]`. Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a`. Simplify using the standard rewrite rules. Consider the case `add p q hp hq`.

Simplify using `only [map_add, hp, hq]`. Consider the case `mul_X p i hp`. Simplify using `only [map_mul]`. Rewrite using `[hp]`. Simplify using `only [aeval_X, Function.comp_apply, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]`.
-/
theorem mConeMap_comp {Ω Ω' : Type} [Field Ω] [Field Ω'] (φ : Ω →+* Ω') (x : (Σ k, ι k) → Ω) (g : MRing ι) :
    mConeMap (φ ∘ x) g = map φ (mConeMap x g) := by
  simp only [mConeMap]
  induction g using MvPolynomial.induction_on with
  | C a =>
    simp
  | add p q hp hq =>
    simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul]
    rw [hp]
    simp only [aeval_X, Function.comp_apply, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a`. Simplify using the standard rewrite rules. Consider the case `add p q hp hq`. Simplify using `only [map_add, hp, hq]`.

Consider the case `mul_X p i hp`. Simplify using `only [map_mul, hp, aeval_X, Function.comp_apply]`.
-/
theorem aeval_comp_ringHom {Ω Ω' : Type} [Field Ω] [Field Ω'] (φ : Ω →+* Ω') (x : (Σ k, ι k) → Ω) (g : MRing ι) :
    aeval (φ ∘ x) g = φ (aeval x g) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    simp
  | add p q hp hq =>
    simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, aeval_X, Function.comp_apply]

/- English proof (translation)
Rewrite using `[map_rename, eval_rename]`.
-/
theorem eval_rename_block (v : (Σ k, ι k) → Σ k, ι' k) (z : (Σ k, ι' k) → ℂ) (f : MRing ι) :
    eval z (map (Int.castRingHom ℂ) (rename v f)) = eval (z ∘ v) (map (Int.castRingHom ℂ) f) := by
  rw [map_rename, eval_rename]

/- English proof (translation)
Introduce `hmem`. Apply `hn` to reduce the goal to its premises. Rewrite `hmem`, the goal using `[mCoordIdeal, RingHom.mem_ker]`. Rewrite `hmem` using `[mConeMap_rename hb]`. Conclude with `rename_injective κ hb.1 (by rw [hmem, map_zero])`.
-/
theorem rename_notMem {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v)
    {z : (Σ k, ι' k) → ℂ} {h : MRing ι} (hn : h ∉ mCoordIdeal (z ∘ v)) : rename v h ∉ mCoordIdeal z := by
  intro hmem
  apply hn
  rw [mCoordIdeal, RingHom.mem_ker] at hmem ⊢
  rw [mConeMap_rename hb] at hmem
  exact rename_injective κ hb.1 (by rw [hmem, map_zero])

/- English proof (translation)
Unfold `mcPts at hz ⊢`. Simplify using `only [Set.mem_ofPred_eq] at hz ⊢`. Take `⟨hz1, hz2⟩` from `hz`. Use `⟨fun k => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨i', hi'⟩` from `hz1 (κ k)`.

Take `⟨⟨k0, i⟩, hp⟩` from `hb.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩`. Establish `h0` using `hb.2.2.1 ⟨k0, i⟩`. Rewrite `h0` using `[hp]`. Establish `hk0 : k0 = k` using `hb.1 h0.symm`. Substitute `hk0` using the available equality.

Use `⟨i, ?_⟩` and prove the remaining obligations. Use `show z (v ⟨k0, i⟩) ≠ 0`. Rewrite using `[hp]`. Conclude with `hi'`. Rewrite using `[← eval_rename_block v z f]`.

Apply `hz2` to reduce the goal to its premises. Rewrite `hf`, the goal using `[mCoordIdeal, RingHom.mem_ker]`. Rewrite using `[mConeMap_rename hb, hx, mConeMap_comp, hf, map_zero, map_zero]`.
-/
theorem comp_mem_mcPts {Ω Ω' : Type} [Field Ω] [Field Ω'] {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k}
    (hb : IsBlockMap κ v) (φ : Ω →+* Ω') {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (hx : x' ∘ v = φ ∘ x)
    {z : (Σ k, ι' k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x')) : z ∘ v ∈ mcPts (mCoordIdeal x) := by
  unfold mcPts at hz ⊢
  simp only [Set.mem_ofPred_eq] at hz ⊢
  obtain ⟨hz1, hz2⟩ := hz
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i', hi'⟩ := hz1 (κ k)
    obtain ⟨⟨k0, i⟩, hp⟩ := hb.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have h0 := hb.2.2.1 ⟨k0, i⟩
    rw [hp] at h0
    have hk0 : k0 = k := hb.1 h0.symm
    subst hk0
    refine ⟨i, ?_⟩
    show z (v ⟨k0, i⟩) ≠ 0
    rw [hp]
    exact hi'
  · rw [← eval_rename_block v z f]
    apply hz2
    rw [mCoordIdeal, RingHom.mem_ker] at hf ⊢
    rw [mConeMap_rename hb, hx, mConeMap_comp, hf, map_zero, map_zero]

end Forms

/- English proof (translation)
Establish `key : ∀ m ∈ g.support, (m.prod fun p e => (X p.1 : MvPolynomial K Ω) ^ e) = ∏ k, X k ^ d k`. Introduce `m hm`. Rewrite using `[Finsupp.prod_fintype _ _ (fun p => pow_zero _), Fintype.prod_sigma]`. Use `Finset.prod_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[Finset.prod_pow_eq_pow_sum, hg m hm k]`. Use `conv_lhs => rw [g.as_sum]`. Use `conv_rhs => rw [g.as_sum]`. Simplify using `only [map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl (fun m hm => ?_)` and prove the remaining obligations.

Rewrite using `[← key m hm]`. Simplify using `only [mConeMap, aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, algebraMap_int_eq, eq_intCast, map_intCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem isHecke_div_and_resEtaPow_div {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    mConeMap y g = C (aeval y g) * ∏ k, X k ^ d k := by
  have key : ∀ m ∈ g.support, (m.prod fun p e => (X p.1 : MvPolynomial K Ω) ^ e) = ∏ k, X k ^ d k := by
    intro m hm
    rw [Finsupp.prod_fintype _ _ (fun p => pow_zero _), Fintype.prod_sigma]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  simp only [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [← key m hm]
  simp only [mConeMap, aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_mul, map_prod,
    map_pow, algebraMap_int_eq, eq_intCast, map_intCast]
  ring

/- English proof (translation)
Take `⟨d1, g1, h1, hg1, hh1, -, he1, hz1, rfl⟩` from `H1`. Take `⟨d2, g2, h2, hg2, hh2, -, he2, hz2, rfl⟩` from `H2`. Establish `hmem : g1 * h2 - g2 * h1 ∈ mCoordIdeal y`. Rewrite using `[mCoordIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, isHecke_div_and_resEtaPow_div y hg1, isHecke_div_and_resEtaPow_div y hh2, isHecke_div_and_resEtaPow_div y hg2, isHecke_div_and_resEtaPow_div y hh1, he1, he2]`. Simplify using `only [map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Unfold `mcPts at hz`. Take `⟨-, hzP⟩` from `hz`. Establish `h0` using `hzP _ hmem`. Simplify using `only [map_sub, map_mul] at h0`.

Rewrite using `[div_eq_div_iff hz1 hz2]`. Take the linear combination `h0`.
-/
private theorem isPair_and_isPair_of_isTriple {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {v1 v2 : ℂ}
    (H1 : IsValueAt y s z v1) (H2 : IsValueAt y s z v2) : v1 = v2 := by
  obtain ⟨d1, g1, h1, hg1, hh1, -, he1, hz1, rfl⟩ := H1
  obtain ⟨d2, g2, h2, hg2, hh2, -, he2, hz2, rfl⟩ := H2
  have hmem : g1 * h2 - g2 * h1 ∈ mCoordIdeal y := by
    rw [mCoordIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, isHecke_div_and_resEtaPow_div y hg1, isHecke_div_and_resEtaPow_div y hh2, isHecke_div_and_resEtaPow_div y hg2,
      isHecke_div_and_resEtaPow_div y hh1, he1, he2]
    simp only [map_mul]
    ring
  unfold mcPts at hz
  obtain ⟨-, hzP⟩ := hz
  have h0 := hzP _ hmem
  simp only [map_sub, map_mul] at h0
  rw [div_eq_div_iff hz1 hz2]
  linear_combination h0

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv zb s hzb hreg`. Take `⟨d, g, h, hg, hh, hhn, he⟩` from `hreg`. Establish `hb` using `Cv.block`. Establish `hxv : M'.x ∘ Cv.v = Cv.φ ∘ M.x` using `funext Cv.x_eq`. Establish `hz' : zb ∘ Cv.v ∈ mcPts (mCoordIdeal M.x)` using `comp_mem_mcPts hb Cv.φ hxv hzb`.

Establish `hg'` using `isMultiHomog_rename_block hb hg`. Establish `hh'` using `isMultiHomog_rename_block hb hh`. Establish `hhn'` using `rename_notMem hb hhn`. Establish `hae : ∀ f : MRing (baseIdx ι M.blk), aeval M'.x (rename Cv.v f) = Cv.φ (aeval M.x f)`. Introduce `f`.

Rewrite using `[aeval_rename, hxv, aeval_comp_ringHom]`. Establish `he' : aeval M'.x (rename Cv.v g) = Cv.φ s * aeval M'.x (rename Cv.v h)`. Rewrite using `[hae, hae, he, map_mul]`. Use `⟨⟨_, _, _, hg', hh', hhn', he'⟩, ?_⟩` and prove the remaining obligations. Establish `hcast : ∀ (w : (Σ k, baseIdx ι M.blk k) → ℂ) (f : MRing (baseIdx ι M.blk)), eval w (map (Int.castRingHom ℂ) f) = aeval w f`.

Introduce `w f`. Rewrite using `[eval_map, aeval_def, algebraMap_int_eq]`. Establish `hev : eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) h) ≠ 0`. Introduce `h0`. Apply `hhn` to reduce the goal to its premises.

Rewrite using `[mCoordIdeal, RingHom.mem_ker, isHecke_div_and_resEtaPow_div _ hh, ← hcast, h0, map_zero, zero_mul]`. Establish `hax : aeval M.x h ≠ 0`. Introduce `h0`. Establish `hmem : h ∈ mCoordIdeal M.x`. Rewrite using `[mCoordIdeal, RingHom.mem_ker, isHecke_div_and_resEtaPow_div _ hh, h0, map_zero, zero_mul]`.

Establish `hz2` using `hz'`. Unfold `mcPts at hz2`. Conclude with `hev (hz2.2 _ hmem)`. Establish `hv1 : IsValueAt M.x s (zb ∘ Cv.v) (eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) g) / eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) h))` using `⟨d, g, h, hg, hh, hax, he, hev, rfl⟩`. Establish `hv2 : IsValueAt M'.x (Cv.φ s) zb (eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) g) / eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) h))`.

Use `⟨_, _, _, hg', hh', ?_, he', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hae]`. Conclude with `(map_ne_zero Cv.φ).2 hax`. Rewrite using `[eval_rename_block]`. Conclude with `hev`.

Rewrite using `[eval_rename_block, eval_rename_block]`. Establish `hex1 : ∃ v, IsValueAt M.x s (zb ∘ Cv.v) v` using `⟨_, hv1⟩`. Establish `hex2 : ∃ v, IsValueAt M'.x (Cv.φ s) zb v` using `⟨_, hv2⟩`. Unfold `valAt`. Rewrite using `[dif_pos hex1, dif_pos hex2, isPair_and_isPair_of_isTriple hzb hex2.choose_spec hv2, isPair_and_isPair_of_isTriple hz' hex1.choose_spec hv1]`.
-/
theorem regAt_φ_valAt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (zb : (Σ k, baseIdx ι' M'.blk k) → ℂ) (s : M.Ω), zb ∈ mcPts (mCoordIdeal M'.x) → RegAt M.x (mCoordIdeal (zb ∘ Cv.v)) s → RegAt M'.x (mCoordIdeal zb) (Cv.φ s) ∧ valAt M'.x (Cv.φ s) zb = valAt M.x s (zb ∘ Cv.v) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv zb s hzb hreg
  obtain ⟨d, g, h, hg, hh, hhn, he⟩ := hreg
  have hb := Cv.block
  have hxv : M'.x ∘ Cv.v = Cv.φ ∘ M.x := funext Cv.x_eq
  have hz' : zb ∘ Cv.v ∈ mcPts (mCoordIdeal M.x) := comp_mem_mcPts hb Cv.φ hxv hzb
  have hg' := isMultiHomog_rename_block hb hg
  have hh' := isMultiHomog_rename_block hb hh
  have hhn' := rename_notMem hb hhn
  have hae : ∀ f : MRing (baseIdx ι M.blk), aeval M'.x (rename Cv.v f) = Cv.φ (aeval M.x f) := by
    intro f
    rw [aeval_rename, hxv, aeval_comp_ringHom]
  have he' : aeval M'.x (rename Cv.v g) = Cv.φ s * aeval M'.x (rename Cv.v h) := by
    rw [hae, hae, he, map_mul]
  refine ⟨⟨_, _, _, hg', hh', hhn', he'⟩, ?_⟩
  have hcast : ∀ (w : (Σ k, baseIdx ι M.blk k) → ℂ) (f : MRing (baseIdx ι M.blk)),
      eval w (map (Int.castRingHom ℂ) f) = aeval w f := by
    intro w f
    rw [eval_map, aeval_def, algebraMap_int_eq]
  have hev : eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) h) ≠ 0 := by
    intro h0
    apply hhn
    rw [mCoordIdeal, RingHom.mem_ker, isHecke_div_and_resEtaPow_div _ hh, ← hcast, h0, map_zero, zero_mul]
  have hax : aeval M.x h ≠ 0 := by
    intro h0
    have hmem : h ∈ mCoordIdeal M.x := by
      rw [mCoordIdeal, RingHom.mem_ker, isHecke_div_and_resEtaPow_div _ hh, h0, map_zero, zero_mul]
    have hz2 := hz'
    unfold mcPts at hz2
    exact hev (hz2.2 _ hmem)
  have hv1 : IsValueAt M.x s (zb ∘ Cv.v)
      (eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) g) / eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) h)) :=
    ⟨d, g, h, hg, hh, hax, he, hev, rfl⟩
  have hv2 : IsValueAt M'.x (Cv.φ s) zb
      (eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) g) / eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) h)) := by
    refine ⟨_, _, _, hg', hh', ?_, he', ?_, ?_⟩
    · rw [hae]
      exact (map_ne_zero Cv.φ).2 hax
    · rw [eval_rename_block]
      exact hev
    · rw [eval_rename_block, eval_rename_block]
  have hex1 : ∃ v, IsValueAt M.x s (zb ∘ Cv.v) v := ⟨_, hv1⟩
  have hex2 : ∃ v, IsValueAt M'.x (Cv.φ s) zb v := ⟨_, hv2⟩
  unfold valAt
  rw [dif_pos hex1, dif_pos hex2, isPair_and_isPair_of_isTriple hzb hex2.choose_spec hv2, isPair_and_isPair_of_isTriple hz' hex1.choose_spec hv1]

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegPhi
