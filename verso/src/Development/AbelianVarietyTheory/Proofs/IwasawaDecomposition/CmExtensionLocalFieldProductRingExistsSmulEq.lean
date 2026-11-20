import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveSeqNormOne

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeWittLoc

open Matrix Formalism.UG

/- English proof (translation)
Set `r : Fin n → S` to `fun j => ∑ i, s (w i) * J i j`. Establish `hr : ∀ z, r ⬝ᵥ z = hform s J w z` using `fun z => by`. Simplify using `only [r, dotProduct, hform, Finset.sum_mul]`. Conclude with `Finset.sum_comm`. Set `P : Matrix (Fin n) (Fin n) S` to `vecMulVec w r`.

Establish `hPP : P * P = hform s J w w • P`. Use extensionality with `i j`. Rewrite using `[← hr]`. Simplify using `only [P, Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`.

Establish `hPJ : cT s P * J = J * P`. Use extensionality with `i j`. Establish `h1 : s (r i) = ∑ k, J i k * w k`. Simplify using `only [r, map_sum, map_mul, hs, hJ]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`.

Simplify using `only [P, cT, Matrix.mul_apply, vecMulVec_apply, transpose_apply, map_apply, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [r, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`. Use `_ = _ := by`.

Rewrite using `[h1, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`. Use `⟨1 - c • P, 1 - s c • P, ?_, ?_, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, smul_mul_smul_comm, hPP, smul_smul, mul_comm (s c) c, ← hc, add_smul]`. Normalize the expressions using the abelian group laws.

Establish `: cT s (1 - c • P) = 1 - s c • cT s P`. Use extensionality with `i j`. Simplify using `[cT, Matrix.one_apply, eq_comm]`. Rewrite using `[this, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, hPJ, Matrix.one_mul, Matrix.mul_one]`. Rewrite using `[sub_mulVec, one_mulVec, smul_mulVec, ← hr, ← smul_smul]`.

Use `congr 2`. Use function extensionality and compare the values at `i`. Simplify using `only [P, mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`.
-/
theorem exists_quasiReflection {S : Type} [CommRing S] (s : S →+* S) (hs : ∀ a, s (s a) = a) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, s (J j i) = J i j) (w : Fin n → S) (c : S)
    (hc : c + s c = c * s c * hform s J w w) :
    ∃ g g' : Matrix (Fin n) (Fin n) S, g' * g = 1 ∧ cT s g * J = J * g' ∧
      ∀ z, g *ᵥ z = z - (c * hform s J w z) • w := by
  let r : Fin n → S := fun j => ∑ i, s (w i) * J i j
  have hr : ∀ z, r ⬝ᵥ z = hform s J w z := fun z => by
    simp only [r, dotProduct, hform, Finset.sum_mul]
    exact Finset.sum_comm
  let P : Matrix (Fin n) (Fin n) S := vecMulVec w r
  have hPP : P * P = hform s J w w • P := by
    ext i j
    rw [← hr]
    simp only [P, Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hPJ : cT s P * J = J * P := by
    ext i j
    have h1 : s (r i) = ∑ k, J i k * w k := by
      simp only [r, map_sum, map_mul, hs, hJ]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [P, cT, Matrix.mul_apply, vecMulVec_apply, transpose_apply, map_apply, map_mul]
    calc ∑ k, s (w k) * s (r i) * J k j = s (r i) * r j := by
          simp only [r, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = _ := by
          rw [h1, Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring
  refine ⟨1 - c • P, 1 - s c • P, ?_, ?_, fun z => ?_⟩
  · rw [sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, smul_mul_smul_comm, hPP, smul_smul,
      mul_comm (s c) c, ← hc, add_smul]
    abel
  · have : cT s (1 - c • P) = 1 - s c • cT s P := by
      ext i j
      simp [cT, Matrix.one_apply, eq_comm]
    rw [this, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, hPJ, Matrix.one_mul,
      Matrix.mul_one]
  · rw [sub_mulVec, one_mulVec, smul_mulVec, ← hr, ← smul_smul]
    congr 2
    funext i
    simp only [P, mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Establish `hsym : ∀ a b, s (hform s J a b) = hform s J b a` using `fun a b => by`. Simplify using `only [hform, map_sum, map_mul, hs, hJ]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`. Establish `hl : ∀ z, hform s J (x - s v • y) z = hform s J x z - v * hform s J y z` using `fun z => by`.

Simplify using `only [hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, hs, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`. Establish `hrr : ∀ z, hform s J z (x - s v • y) = hform s J z x - s v * hform s J z y` using `fun z => by`. Simplify using `only [hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.

Take `⟨c, hc⟩` from `hD.exists_left_inv`. Establish `hβ : s β = β` using `by rw [← hx, hsym]`. Establish `hc' : s c * (β - s v * hform s J x y) = 1`. Use `congrArg s hc` as an intermediate fact. Rewrite `this` using `[map_mul, map_sub, map_mul, hsym, hβ, map_one]`. Then use the resulting hypothesis.

Take `⟨g, g', h1, h2, h3⟩` from `exists_quasiReflection s hs J hJ (x - s v • y) c (by`. Rewrite using `[hl, hrr, hrr, hx, hy]`. Take the linear combination `(-c) * hc' - s c * hc - c * s c * β * hv)`. Establish `h4 : g * g' = 1` using `mul_eq_one_comm.1 h1`. Use `⟨⟨v • g, s v • g', ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_mul_smul_comm, hv, h4, one_smul]`. Rewrite using `[smul_mul_smul_comm, mul_comm, hv, h1, one_smul]`. Establish `: cT s (v • g) = s v • cT s g`. Use extensionality with `i j`. Simplify using `[cT]`.

Use `show cT s (v • g) * J * (v • g) = J`. Rewrite using `[this, Matrix.smul_mul, smul_mul_smul_comm, h2, Matrix.mul_assoc, h1, mul_comm, hv, one_smul, Matrix.mul_one]`. Use `show (v • g) *ᵥ x = y`. Rewrite using `[smul_mulVec, h3, hl, hx, hc, one_smul, sub_sub_cancel, smul_smul, hv, one_smul]`.
-/
theorem exists_unitary {S : Type} [CommRing S] (s : S →+* S) (hs : ∀ a, s (s a) = a) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, s (J j i) = J i j) (x y : Fin n → S) (β v : S)
    (hx : hform s J x x = β) (hy : hform s J y y = β) (hv : v * s v = 1)
    (hD : IsUnit (β - v * hform s J y x)) :
    ∃ γ : GL (Fin n) S, cT s γ.1 * J * γ.1 = J ∧ γ.1 *ᵥ x = y := by
  have hsym : ∀ a b, s (hform s J a b) = hform s J b a := fun a b => by
    simp only [hform, map_sum, map_mul, hs, hJ]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hl : ∀ z, hform s J (x - s v • y) z = hform s J x z - v * hform s J y z := fun z => by
    simp only [hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, hs,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hrr : ∀ z, hform s J z (x - s v • y) = hform s J z x - s v * hform s J z y := fun z => by
    simp only [hform, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨c, hc⟩ := hD.exists_left_inv
  have hβ : s β = β := by rw [← hx, hsym]
  have hc' : s c * (β - s v * hform s J x y) = 1 := by
    have := congrArg s hc
    rwa [map_mul, map_sub, map_mul, hsym, hβ, map_one] at this
  obtain ⟨g, g', h1, h2, h3⟩ := exists_quasiReflection s hs J hJ (x - s v • y) c (by
    rw [hl, hrr, hrr, hx, hy]
    linear_combination (-c) * hc' - s c * hc - c * s c * β * hv)
  have h4 : g * g' = 1 := mul_eq_one_comm.1 h1
  refine ⟨⟨v • g, s v • g', ?_, ?_⟩, ?_, ?_⟩
  · rw [smul_mul_smul_comm, hv, h4, one_smul]
  · rw [smul_mul_smul_comm, mul_comm, hv, h1, one_smul]
  · have : cT s (v • g) = s v • cT s g := by
      ext i j
      simp [cT]
    show cT s (v • g) * J * (v • g) = J
    rw [this, Matrix.smul_mul, smul_mul_smul_comm, h2, Matrix.mul_assoc, h1, mul_comm, hv, one_smul,
      Matrix.mul_one]
  · show (v • g) *ᵥ x = y
    rw [smul_mulVec, h3, hl, hx, hc, one_smul, sub_sub_cancel, smul_smul, hv, one_smul]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Use `choose m hm hmem using fun k => exists_max_ideal_of_mem_nonunits (h k)`. Take `⟨k, l, hkl, he⟩` from `Finite.exists_ne_map_eq_of_infinite (fun k => (⟨m k, hm k⟩ : MaximalSpectrum S))`. Establish `he' : m k = m l` using `congrArg MaximalSpectrum.asIdeal he`.

Establish `h1` using `hmem l`. Rewrite `h1` using `[← he']`. Establish `h2 : (v k - v l) * t ∈ m k`. Use `(m k).sub_mem h1 (hmem k)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Establish `h3 : t ∈ m k` using `((m k).unit_mul_mem_iff_mem (hv k l hkl)).1 h2`. Establish `h4 : β ∈ m k`. Use `(m k).add_mem (hmem k) ((m k).mul_mem_left (v k) h3)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.

Conclude with `(hm k).ne_top ((m k).eq_top_of_isUnit_mem h4 hβ)`.
-/
theorem exists_isUnit_sub {S : Type} [CommRing S] [Finite (MaximalSpectrum S)] (v : ℕ → S)
    (hv : ∀ k l, k ≠ l → IsUnit (v k - v l)) (β t : S) (hβ : IsUnit β) :
    ∃ k, IsUnit (β - v k * t) := by
  by_contra h
  push Not at h
  choose m hm hmem using fun k => exists_max_ideal_of_mem_nonunits (h k)
  obtain ⟨k, l, hkl, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k => (⟨m k, hm k⟩ : MaximalSpectrum S))
  have he' : m k = m l := congrArg MaximalSpectrum.asIdeal he
  have h1 := hmem l
  rw [← he'] at h1
  have h2 : (v k - v l) * t ∈ m k := by
    have := (m k).sub_mem h1 (hmem k)
    convert this using 1
    ring
  have h3 : t ∈ m k := ((m k).unit_mul_mem_iff_mem (hv k l hkl)).1 h2
  have h4 : β ∈ m k := by
    have := (m k).add_mem (hmem k) ((m k).mul_mem_left (v k) h3)
    rwa [sub_add_cancel] at this
  exact (hm k).ne_top ((m k).eq_top_of_isUnit_mem h4 hβ)

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one`. Consider the case `exact _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one`. Consider the case `(apply _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one ..)`.
-/
theorem exists_normOne {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ a : ℕ → E, Function.Injective a ∧ ∀ k, a k * σ (a k) = 1 := by
  first
  | exact @_root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one
  | exact _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one
  | (apply _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InjectiveSeqNormOne.exists_injective_seq_norm_one ..)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ hR' M J hJ β x y hβ hx hy`. Use `hR'.1` as an intermediate fact. Establish `: IsArtinianRing (R ⊗[F] E)` using `IsArtinianRing.of_finite R (R ⊗[F] E)`. Take `⟨a, ha, hn⟩` from `exists_normOne hcm`. Take `⟨k, hk⟩` from `exists_isUnit_sub (fun k => inclR R (a k)) (fun k l hkl => by`.

Rewrite using `[← map_sub]`. Conclude with `(IsUnit.mk0 _ (sub_ne_zero.2 (ha.ne hkl))).map _)`. Use the proof step `(algebraMap R (R ⊗[F] E) β) (hR R σ J (y 0) (x 0)) (hβ.map _)`. Take `⟨γ, h1, h2⟩` from `exists_unitary (sigR R σ) (GlobalTheory.SelfDualLatticeCompare.sigR_sigR R hcm) (JR R J) (fun i j => by show (1 : R) ⊗ₜ[F] σ (J j i) = (1 : R) ⊗ₜ[F] J i j`. Rewrite using `[hJ.1])`.

Use the proof step `(x 0) (y 0) (algebraMap R (R ⊗[F] E) β) (inclR R (a k))`. Use the proof step `(by rw [← hx]; exact GlobalTheory.SelfDualLatticeCompare.hR_self R hcm hJ _)`. Use the proof step `(by rw [← hy]; exact GlobalTheory.SelfDualLatticeCompare.hR_self R hcm hJ _)`. Use the proof step `(by show inclR R (a k) * inclR R (σ (a k)) = 1`. Rewrite using `[← map_mul, hn, map_one])`.

Use `hk`. Use `⟨(⟨γ, h1⟩ : HR R σ J), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Take `rfl : i = 0` from `Subsingleton.elim _ _`. Conclude with `h2`.
-/
theorem exists_smul_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (β : R) (x y : (Fin 1 → Fin M → R ⊗[F] E)), IsUnit β → qR R σ J (x 0) = β → qR R σ J (y 0) = β → ∃ g : HA R σ J, g • x = y := by
  intro F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ hR' M J hJ β x y hβ hx hy
  have := hR'.1
  have : IsArtinianRing (R ⊗[F] E) := IsArtinianRing.of_finite R (R ⊗[F] E)
  obtain ⟨a, ha, hn⟩ := exists_normOne hcm
  obtain ⟨k, hk⟩ := exists_isUnit_sub (fun k => inclR R (a k))
    (fun k l hkl => by
      rw [← map_sub]
      exact (IsUnit.mk0 _ (sub_ne_zero.2 (ha.ne hkl))).map _)
    (algebraMap R (R ⊗[F] E) β) (hR R σ J (y 0) (x 0)) (hβ.map _)
  obtain ⟨γ, h1, h2⟩ := exists_unitary (sigR R σ) (GlobalTheory.SelfDualLatticeCompare.sigR_sigR R hcm) (JR R J)
    (fun i j => by
      show (1 : R) ⊗ₜ[F] σ (J j i) = (1 : R) ⊗ₜ[F] J i j
      rw [hJ.1])
    (x 0) (y 0) (algebraMap R (R ⊗[F] E) β) (inclR R (a k))
    (by rw [← hx]; exact GlobalTheory.SelfDualLatticeCompare.hR_self R hcm hJ _)
    (by rw [← hy]; exact GlobalTheory.SelfDualLatticeCompare.hR_self R hcm hJ _)
    (by
      show inclR R (a k) * inclR R (σ (a k)) = 1
      rw [← map_mul, hn, map_one])
    hk
  refine ⟨(⟨γ, h1⟩ : HR R σ J), ?_⟩
  funext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  exact h2

end GlobalTheory.GaugeWittLoc
