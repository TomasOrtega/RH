import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingComparisonOfBaseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRingAdicCompletePrimeRegular
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpansionSurjectiveAdditiveLinearStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpansionEqZeroIffCoeffsMemStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

noncomputable section

namespace GlobalTheory.CompanionTheory.TensOne

open TensorProduct

section Generic

variable {R S W C : Type} [CommRing R] [CommRing S] [CommRing W] [CommRing C]
  [Algebra R S] [Algebra R W] [Algebra R C]

/- English proof (translation)
Establish `hp : (p : S ⊗[R] W) = (p : S) ⊗ₜ[R] (1 : W)` using `(map_natCast (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] W) p).symm`. Establish `: (e * (p : S)) ⊗ₜ[R] x = (p : S ⊗[R] W) * (e ⊗ₜ[R] x)`. Rewrite using `[hp, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`.
-/
theorem tmul_mul_natCast_mem (p : ℕ) (e : S) (x : W) :
    (e * (p : S)) ⊗ₜ[R] x ∈ Ideal.span {(p : S ⊗[R] W)} := by
  have hp : (p : S ⊗[R] W) = (p : S) ⊗ₜ[R] (1 : W) :=
    (map_natCast (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] W) p).symm
  have : (e * (p : S)) ⊗ₜ[R] x = (p : S ⊗[R] W) * (e ⊗ₜ[R] x) := by
    rw [hp, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/- English proof (translation)
Establish `hp : (p : S ⊗[R] W) = (1 : S) ⊗ₜ[R] (p : W)` using `(map_natCast (Algebra.TensorProduct.includeRight : W →ₐ[R] S ⊗[R] W).toRingHom p).symm`. Establish `: e ⊗ₜ[R] (x * (p : W)) = (p : S ⊗[R] W) * (e ⊗ₜ[R] x)`. Rewrite using `[hp, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm x]`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`.
-/
theorem tmul_natCast_mul_mem (p : ℕ) (e : S) (x : W) :
    e ⊗ₜ[R] (x * (p : W)) ∈ Ideal.span {(p : S ⊗[R] W)} := by
  have hp : (p : S ⊗[R] W) = (1 : S) ⊗ₜ[R] (p : W) :=
    (map_natCast (Algebra.TensorProduct.includeRight : W →ₐ[R] S ⊗[R] W).toRingHom p).symm
  have : e ⊗ₜ[R] (x * (p : W)) = (p : S ⊗[R] W) * (e ⊗ₜ[R] x) := by
    rw [hp, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm x]
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

def gsum (d : ℕ → S) (w : ℕ →₀ W) : S ⊗[R] W := w.sum fun k x => d k ⊗ₜ[R] x

/- English proof (translation)
The claim follows from `Finsupp.sum_add_index' (fun _ => TensorProduct.tmul_zero _ _) fun _ _ _ => TensorProduct.tmul_add _ _ _`.
-/
theorem gsum_add (d : ℕ → S) (w w' : ℕ →₀ W) :
    (gsum d (w + w') : S ⊗[R] W) = gsum d w + gsum d w' :=
  Finsupp.sum_add_index' (fun _ => TensorProduct.tmul_zero _ _) fun _ _ _ => TensorProduct.tmul_add _ _ _

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp [gsum]⟩`. Consider the case `tmul a x`. Take `⟨s, c, hc⟩` from `hsurj a`. Take `⟨e, he⟩` from `Ideal.mem_span_singleton'.1 hc`.

Use `⟨∑ k ∈ s, Finsupp.single k (c k • x), ?_⟩` and prove the remaining obligations. Establish `h1 : (gsum d (∑ k ∈ s, Finsupp.single k (c k • x)) : S ⊗[R] W) = (∑ k ∈ s, algebraMap R S (c k) * d k) ⊗ₜ[R] x`. Rewrite using `[gsum, ← Finsupp.sum_finset_sum_index (fun _ => TensorProduct.tmul_zero _ _) (fun _ _ _ => TensorProduct.tmul_add _ _ _), TensorProduct.sum_tmul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.sum_single_index (h := fun k x => d k ⊗ₜ[R] x) (TensorProduct.tmul_zero _ _), ← Algebra.smul_def, TensorProduct.smul_tmul]`.

Rewrite using `[h1, ← TensorProduct.sub_tmul, ← he]`. Conclude with `tmul_mul_natCast_mem p e x`. Consider the case `add x y hx hy`. Take `⟨w, hw⟩` from `hx`. Take `⟨w', hw'⟩` from `hy`.

Use `⟨w + w', ?_⟩` and prove the remaining obligations. Establish `: x + y - gsum d (w + w') = (x - gsum d w) + (y - gsum d w')`. Rewrite using `[gsum_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `add_mem hw hw'`.
-/
theorem exists_gsum (p : ℕ) (d : ℕ → S)
    (hsurj : ∀ a : S, ∃ (s : Finset ℕ) (c : ℕ → R), a - ∑ k ∈ s, algebraMap R S (c k) * d k ∈ Ideal.span {(p : S)})
    (z : S ⊗[R] W) : ∃ w : ℕ →₀ W, z - gsum d w ∈ Ideal.span {(p : S ⊗[R] W)} := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp [gsum]⟩
  | tmul a x =>
    obtain ⟨s, c, hc⟩ := hsurj a
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hc
    refine ⟨∑ k ∈ s, Finsupp.single k (c k • x), ?_⟩
    have h1 : (gsum d (∑ k ∈ s, Finsupp.single k (c k • x)) : S ⊗[R] W) =
        (∑ k ∈ s, algebraMap R S (c k) * d k) ⊗ₜ[R] x := by
      rw [gsum, ← Finsupp.sum_finset_sum_index (fun _ => TensorProduct.tmul_zero _ _)
        (fun _ _ _ => TensorProduct.tmul_add _ _ _), TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finsupp.sum_single_index (h := fun k x => d k ⊗ₜ[R] x) (TensorProduct.tmul_zero _ _), ← Algebra.smul_def,
        TensorProduct.smul_tmul]
    rw [h1, ← TensorProduct.sub_tmul, ← he]
    exact tmul_mul_natCast_mem p e x
  | add x y hx hy =>
    obtain ⟨w, hw⟩ := hx
    obtain ⟨w', hw'⟩ := hy
    refine ⟨w + w', ?_⟩
    have : x + y - gsum d (w + w') = (x - gsum d w) + (y - gsum d w') := by
      rw [gsum_add]; ring
    rw [this]
    exact add_mem hw hw'

/- English proof (translation)
Take `⟨w, hw⟩` from `exists_gsum p d hsurj z`. Establish `hL : Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) (z - gsum d w) = 0`. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 hw`. Rewrite using `[← hy, map_mul, map_natCast, hC, mul_zero]`. Rewrite `hL` using `[map_sub, hz, zero_sub, neg_eq_zero, gsum, Finsupp.sum, map_sum]`.

Establish `hsum : ∑ k ∈ w.support, f (d k) * g (w k) = 0`. Rewrite using `[← hL]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.lift_tmul]`. Establish `hk` using `hK _ _ hsum`.

Establish `hG : (gsum d w : S ⊗[R] W) ∈ Ideal.span {(p : S ⊗[R] W)}`. Use `Ideal.sum_mem _ fun k hks => ?_` and prove the remaining obligations. Take `⟨u, v, huv⟩` from `Ideal.mem_span_pair.1 (hk k hks)`. Take `⟨e, he⟩` from `Ideal.mem_span_singleton'.1 (hv k)`. Establish `h1 : d k ⊗ₜ[R] (u * algebraMap R W r0) = (e * (p : S)) ⊗ₜ[R] u`.

Rewrite using `[he, mul_comm u, ← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul]`. Express the relevant statement in the definitionally equal form `d k ⊗ₜ[R] (w k) ∈ _`. Rewrite using `[← huv, TensorProduct.tmul_add, h1]`. Conclude with `add_mem (tmul_mul_natCast_mem p e u) (tmul_natCast_mul_mem p (d k) v)`. Use `add_mem hw hG` as an intermediate fact.

Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem generic (p : ℕ) (d : ℕ → S) (r0 : R) (f : S →ₐ[R] C) (g : W →ₐ[R] C)
    (hsurj : ∀ a : S, ∃ (s : Finset ℕ) (c : ℕ → R), a - ∑ k ∈ s, algebraMap R S (c k) * d k ∈ Ideal.span {(p : S)})
    (hv : ∀ k, algebraMap R S r0 * d k ∈ Ideal.span {(p : S)})
    (hK : ∀ (s : Finset ℕ) (w : ℕ → W), ∑ k ∈ s, f (d k) * g (w k) = 0 →
      ∀ k ∈ s, w k ∈ Ideal.span {algebraMap R W r0, (p : W)})
    (hC : (p : C) = 0) (z : S ⊗[R] W)
    (hz : Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) z = 0) :
    z ∈ Ideal.span {(p : S ⊗[R] W)} := by
  obtain ⟨w, hw⟩ := exists_gsum p d hsurj z
  have hL : Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) (z - gsum d w) = 0 := by
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hw
    rw [← hy, map_mul, map_natCast, hC, mul_zero]
  rw [map_sub, hz, zero_sub, neg_eq_zero, gsum, Finsupp.sum, map_sum] at hL
  have hsum : ∑ k ∈ w.support, f (d k) * g (w k) = 0 := by
    rw [← hL]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.TensorProduct.lift_tmul]
  have hk := hK _ _ hsum
  have hG : (gsum d w : S ⊗[R] W) ∈ Ideal.span {(p : S ⊗[R] W)} := by
    refine Ideal.sum_mem _ fun k hks => ?_
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 (hk k hks)
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (hv k)
    have h1 : d k ⊗ₜ[R] (u * algebraMap R W r0) = (e * (p : S)) ⊗ₜ[R] u := by
      rw [he, mul_comm u, ← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul]
    change d k ⊗ₜ[R] (w k) ∈ _
    rw [← huv, TensorProduct.tmul_add, h1]
    exact add_mem (tmul_mul_natCast_mem p e u) (tmul_natCast_mul_mem p (d k) v)
  have := add_mem hw hG
  rwa [sub_add_cancel] at this

end Generic

section Specific

variable {l : ℕ} [Fact l.Prime]

def base : PAlg l where
  A := Ob l
  s := RingHom.id _
  perf := inferInstance
  compl := GlobalTheory.CompanionTheory.TiltCompl.complete_tf.1
  tf := GlobalTheory.CompanionTheory.TiltCompl.complete_tf.2

/- English proof (translation)
The claim follows from `Function.bijective_id`.
-/
theorem isBase_base : IsBase l (base (l := l)) := Function.bijective_id

def d (k : ℕ) : Acris l := AdicCompletion.of _ _ (ACris.dpowZero (xi0_mem (l := l)) k)

/- English proof (translation)
Rewrite using `[d, cris_of]`. Use `congrArg (A.mkAcr n) (Subtype.ext ?_)` and prove the remaining obligations. Conclude with `awayW_dpw A.s k (ACris.isUnit_natCast (K := ℂ_[l]) (p := l) k.factorial_ne_zero) (xi0 l)`.
-/
theorem cris_d (A : PAlg l) (n k : ℕ) : A.cris n (d k) = A.dxi n k := by
  rw [d, cris_of]
  refine congrArg (A.mkAcr n) (Subtype.ext ?_)
  exact awayW_dpw A.s k (ACris.isUnit_natCast (K := ℂ_[l]) (p := l) k.factorial_ne_zero) (xi0 l)

/- English proof (translation)
The claim follows from `wmap_id x`.
-/
theorem sW_base (x : Ainf l) : (base (l := l)).sW x = x := wmap_id x

/- English proof (translation)
Establish `h1` using `(base (l := l)).aTo1_coeff (WittVector.teichmuller l a)`. Rewrite `h1` using `[WittVector.teichmuller_coeff_zero]`. Establish `h2` using `(base (l := l)).cris_algebraMap 1 (WittVector.teichmuller l a)`. Rewrite `h2` using `[sW_base]`. Rewrite using `[h1]`.

Conclude with `h2`.
-/
theorem cris_teich (a : Ob l) :
    (base (l := l)).cris 1 (algebraMap (Ainf l) (Acris l) (WittVector.teichmuller l a)) =
      (base (l := l)).aTo1 a := by
  have h1 := (base (l := l)).aTo1_coeff (WittVector.teichmuller l a)
  rw [WittVector.teichmuller_coeff_zero] at h1
  have h2 := (base (l := l)).cris_algebraMap 1 (WittVector.teichmuller l a)
  rw [sW_base] at h2
  rw [h1]
  exact h2

/- English proof (translation)
Use `(RingHom.mem_ker).2 h` as an intermediate fact. Rewrite `this` using `[((GlobalTheory.T.period_ring_comparison_of_base base isBase_base).2 1).2, pow_one]`. Then use the resulting hypothesis.
-/
theorem mem_of_cris (a : Acris l) (h : (base (l := l)).cris 1 a = 0) : a ∈ Ideal.span {(l : Acris l)} := by
  have := (RingHom.mem_ker).2 h
  rwa [((GlobalTheory.T.period_ring_comparison_of_base base isBase_base).2 1).2, pow_one] at this

/- English proof (translation)
Take `⟨c, hc⟩` from `(GlobalTheory.T.expansion_surjective_additive_linear (base (l := l))).1 ((base (l := l)).cris 1 a)`. Use `⟨c.support, fun k => WittVector.teichmuller l (c k), mem_of_cris _ ?_⟩` and prove the remaining obligations. Establish `e : (base (l` using `l)).expand c = ∑ k ∈ c.support, (base (l := l)).aTo1 (c k) * (base (l := l)).dxi 1 (l * k) := rfl`. Rewrite using `[map_sub, ← hc, e, sub_eq_zero, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, cris_teich, cris_d]`.
-/
theorem hsurj (a : Acris l) : ∃ (s : Finset ℕ) (c : ℕ → Ainf l),
    a - ∑ k ∈ s, algebraMap (Ainf l) (Acris l) (c k) * d (l * k) ∈ Ideal.span {(l : Acris l)} := by
  obtain ⟨c, hc⟩ := (GlobalTheory.T.expansion_surjective_additive_linear (base (l := l))).1 ((base (l := l)).cris 1 a)
  refine ⟨c.support, fun k => WittVector.teichmuller l (c k), mem_of_cris _ ?_⟩
  have e : (base (l := l)).expand c =
      ∑ k ∈ c.support, (base (l := l)).aTo1 (c k) * (base (l := l)).dxi 1 (l * k) := rfl
  rw [map_sub, ← hc, e, sub_eq_zero, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, cris_teich, cris_d]

def r0 : Ainf l := WittVector.teichmuller l (pFlat l ^ l)

/- English proof (translation)
Use `mem_of_cris _ ?_` and prove the remaining obligations. Rewrite using `[map_mul, r0, cris_teich, cris_d]`. Conclude with `(GlobalTheory.T.expansion_surjective_additive_linear (base (l := l))).2.2.2 k`.
-/
theorem hv (k : ℕ) : algebraMap (Ainf l) (Acris l) (r0 (l := l)) * d k ∈ Ideal.span {(l : Acris l)} := by
  refine mem_of_cris _ ?_
  rw [map_mul, r0, cris_teich, cris_d]
  exact (GlobalTheory.T.expansion_surjective_additive_linear (base (l := l))).2.2.2 k

/- English proof (translation)
Establish `hexp : A.expand (Finsupp.indicator s fun k _ => (w k).coeff 0) = 0`. Rewrite using `[expand, Finsupp.sum_of_support_subset _ (Finsupp.support_indicator_subset _ _) _ (by simp), ← h]`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.indicator_of_mem hk, aTo1_coeff, cris_d, mul_comm]`. Establish `hk` using `(GlobalTheory.T.expansion_eq_zero_iff_coeffs_mem A _).1 hexp k`.

Rewrite `hk` using `[Finsupp.indicator_of_mem hks]`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.1 hk`. Establish `hr : algebraMap (Ainf l) A.W r0 = WittVector.teichmuller l (A.pi ^ l)`. Express the relevant statement in the definitionally equal form `A.sW _ = _`. Rewrite using `[r0, sW, WittVector.map_teichmuller, map_pow]`.

Both sides reduce to the same expression. Establish `hz : (w k - WittVector.teichmuller l b * algebraMap (Ainf l) A.W r0).coeff 0 = 0`. Rewrite using `[← WittVector.constantCoeff_apply, map_sub, map_mul, hr]`. Simplify using `only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]`. Rewrite using `[hb, sub_self]`.

Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.1 ((A.mem_span_l_iff _).2 hz)`. Conclude with `Ideal.mem_span_pair.2 ⟨WittVector.teichmuller l b, t, by rw [ht]; ring⟩`.
-/
theorem hK (A : PAlg l) (s : Finset ℕ) (w : ℕ → A.W)
    (h : ∑ k ∈ s, A.cris 1 (d (l * k)) * A.toAcr 1 (w k) = 0) (k : ℕ) (hks : k ∈ s) :
    w k ∈ Ideal.span {algebraMap (Ainf l) A.W r0, (l : A.W)} := by
  have hexp : A.expand (Finsupp.indicator s fun k _ => (w k).coeff 0) = 0 := by
    rw [expand, Finsupp.sum_of_support_subset _ (Finsupp.support_indicator_subset _ _) _ (by simp), ← h]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finsupp.indicator_of_mem hk, aTo1_coeff, cris_d, mul_comm]
  have hk := (GlobalTheory.T.expansion_eq_zero_iff_coeffs_mem A _).1 hexp k
  rw [Finsupp.indicator_of_mem hks] at hk
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hk
  have hr : algebraMap (Ainf l) A.W r0 = WittVector.teichmuller l (A.pi ^ l) := by
    change A.sW _ = _
    rw [r0, sW, WittVector.map_teichmuller, map_pow]
    rfl
  have hz : (w k - WittVector.teichmuller l b * algebraMap (Ainf l) A.W r0).coeff 0 = 0 := by
    rw [← WittVector.constantCoeff_apply, map_sub, map_mul, hr]
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    rw [hb, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 ((A.mem_span_l_iff _).2 hz)
  exact Ideal.mem_span_pair.2 ⟨WittVector.teichmuller l b, t, by rw [ht]; ring⟩

/- English proof (translation)
Use `A.pow_l_acr 1` as an intermediate fact. Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis.
-/
theorem natCast_acr (A : PAlg l) : (l : A.Acr 1) = 0 := by
  have := A.pow_l_acr 1
  rwa [pow_one] at this

/- English proof (translation)
Introduce `l _ A z hz`. Conclude with `generic (R := Ainf l) (S := Acris l) (W := A.W) (C := A.Acr 1) l (fun k => d (l * k)) r0 (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr 1)) (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr 1)) hsurj (fun k => hv _) (fun s w h k hk => hK A s w h k hk) (natCast_acr A) z hz`.
-/
theorem main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (z : TensorProduct (Ainf l) (Acris l) A.W),
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr 1))
      (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr 1)) (fun _ _ => Commute.all _ _) z = 0 →
    z ∈ Ideal.span {(l : TensorProduct (Ainf l) (Acris l) A.W)} := by
  intro l _ A z hz
  exact generic (R := Ainf l) (S := Acris l) (W := A.W) (C := A.Acr 1) l (fun k => d (l * k)) r0
    (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr 1)) (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr 1))
    hsurj (fun k => hv _) (fun s w h k hk => hK A s w h k hk) (natCast_acr A) z hz

end Specific

end GlobalTheory.CompanionTheory.TensOne
