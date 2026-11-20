import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeIsDomainIsIntegrallyClos
open IsLocalRing

namespace GlobalTheory

namespace IndEtaleNormal

open Polynomial

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]

/- English proof (translation)
Use `choose idx hidx using hcov`. Take `⟨M, hM⟩` from `Finset.exists_le (T.image idx)`. Conclude with `⟨M, fun t ht => hmono (hM _ (Finset.mem_image_of_mem idx ht)) (hidx t)⟩`.
-/
lemma exists_mem_of_finset (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i) (T : Finset S) : ∃ i, ∀ t ∈ T, t ∈ Si i := by
  classical
  choose idx hidx using hcov
  obtain ⟨M, hM⟩ := Finset.exists_le (T.image idx)
  exact ⟨M, fun t ht => hmono (hM _ (Finset.mem_image_of_mem idx ht)) (hidx t)⟩

/- English proof (translation)
Establish `: NoZeroDivisors S`. Use `⟨fun {x y} hxy => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `exists_mem_of_finset Si hmono hcov {x, y}`. Establish `hx : x ∈ Si i` using `hi x (by simp)`. Establish `hy : y ∈ Si i` using `hi y (by simp)`.

Use `haveI := hdom i`. Establish `h0 : (⟨x, hx⟩ : Si i) * ⟨y, hy⟩ = 0` using `Subtype.ext (by simpa using hxy)`. Break down `mul_eq_zero.mp h0 with h | h` into its components or cases. Conclude with `Or.inl (congrArg Subtype.val h)`. Conclude with `Or.inr (congrArg Subtype.val h)`.

Conclude with `NoZeroDivisors.to_isDomain S`.
-/
lemma isDomain [Nontrivial S] (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i) (hdom : ∀ i, IsDomain (Si i)) : IsDomain S := by
  classical
  have : NoZeroDivisors S := by
    refine ⟨fun {x y} hxy => ?_⟩
    obtain ⟨i, hi⟩ := exists_mem_of_finset Si hmono hcov {x, y}
    have hx : x ∈ Si i := hi x (by simp)
    have hy : y ∈ Si i := hi y (by simp)
    haveI := hdom i
    have h0 : (⟨x, hx⟩ : Si i) * ⟨y, hy⟩ = 0 := Subtype.ext (by simpa using hxy)
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  exact NoZeroDivisors.to_isDomain S

/- English proof (translation)
Rewrite using `[isIntegrallyClosed_iff (FractionRing S)]`. Introduce `x hx`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := S) x`. Take `⟨p, hpm, hp⟩` from `hx`. Take `⟨i, hi⟩` from `exists_mem_of_finset Si hmono hcov (insert a (insert b p.coeffs))`.

Use `haveI := (hic i).1`. Use `haveI := (hic i).2`. Establish `ha : a ∈ Si i` using `hi a (by simp)`. Establish `hb' : b ∈ Si i` using `hi b (by simp)`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`.

Use `set g : Si i →+* FractionRing S := (algebraMap S (FractionRing S)).comp (algebraMap (Si i) S) with hg_def`. Establish `hg : Function.Injective g` using `(IsFractionRing.injective S (FractionRing S)).comp Subtype.val_injective`. Set `φ : FractionRing (Si i) →+* FractionRing S` to `IsFractionRing.lift hg`. Establish `hφ : ∀ c : Si i, φ (algebraMap (Si i) (FractionRing (Si i)) c) = g c` using `fun c => IsFractionRing.lift_algebraMap hg c`. Establish `hlift : p ∈ Polynomial.lifts (algebraMap (Si i) S)`.

Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`. Distinguish the cases in `hn : p.coeff n = 0`. Conclude with `⟨0, by simp [hn]⟩`. Conclude with `⟨⟨p.coeff n, hi _ (by simp [Polynomial.coeff_mem_coeffs hn])⟩, rfl⟩`.

Take `⟨q, hq, -, hqm⟩` from `Polynomial.lifts_and_degree_eq_and_monic hlift hpm`. Use `set y : FractionRing (Si i) := algebraMap (Si i) (FractionRing (Si i)) ⟨a, ha⟩ / algebraMap (Si i) (FractionRing (Si i)) ⟨b, hb'⟩ with hy_def`. Establish `hφy : φ y = algebraMap S (FractionRing S) a / algebraMap S (FractionRing S) b`. Rewrite using `[hy_def, map_div₀, hφ, hφ]`. Both sides reduce to the same expression.

Establish `hyint : IsIntegral (Si i) y`. Use `⟨q, hqm, φ.injective ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.hom_eval₂, map_zero, hφy]`. Establish `: φ.comp (algebraMap (Si i) (FractionRing (Si i))) = g` using `RingHom.ext hφ`. Rewrite using `[this, hg_def, ← Polynomial.eval₂_map, hq]`.

Conclude with `hp`. Take `⟨c, hc⟩` from `(isIntegrallyClosed_iff (FractionRing (Si i))).mp (hic i).2 hyint`. Use `⟨(c : S), ?_⟩` and prove the remaining obligations. Rewrite using `[← hφy, ← hc, hφ]`. Both sides reduce to the same expression.
-/
lemma isIntegrallyClosed [IsDomain S] (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i)
    (hic : ∀ i, IsDomain (Si i) ∧ IsIntegrallyClosed (Si i)) : IsIntegrallyClosed S := by
  classical
  rw [isIntegrallyClosed_iff (FractionRing S)]
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  obtain ⟨p, hpm, hp⟩ := hx
  obtain ⟨i, hi⟩ := exists_mem_of_finset Si hmono hcov (insert a (insert b p.coeffs))
  haveI := (hic i).1
  haveI := (hic i).2
  have ha : a ∈ Si i := hi a (by simp)
  have hb' : b ∈ Si i := hi b (by simp)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set g : Si i →+* FractionRing S := (algebraMap S (FractionRing S)).comp (algebraMap (Si i) S)
    with hg_def
  have hg : Function.Injective g :=
    (IsFractionRing.injective S (FractionRing S)).comp Subtype.val_injective
  let φ : FractionRing (Si i) →+* FractionRing S := IsFractionRing.lift hg
  have hφ : ∀ c : Si i, φ (algebraMap (Si i) (FractionRing (Si i)) c) = g c := fun c =>
    IsFractionRing.lift_algebraMap hg c
  have hlift : p ∈ Polynomial.lifts (algebraMap (Si i) S) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : p.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
    · exact ⟨⟨p.coeff n, hi _ (by simp [Polynomial.coeff_mem_coeffs hn])⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hpm
  set y : FractionRing (Si i) := algebraMap (Si i) (FractionRing (Si i)) ⟨a, ha⟩ /
    algebraMap (Si i) (FractionRing (Si i)) ⟨b, hb'⟩ with hy_def
  have hφy : φ y = algebraMap S (FractionRing S) a / algebraMap S (FractionRing S) b := by
    rw [hy_def, map_div₀, hφ, hφ]
    rfl
  have hyint : IsIntegral (Si i) y := by
    refine ⟨q, hqm, φ.injective ?_⟩
    rw [Polynomial.hom_eval₂, map_zero, hφy]
    have : φ.comp (algebraMap (Si i) (FractionRing (Si i))) = g :=
      RingHom.ext hφ
    rw [this, hg_def, ← Polynomial.eval₂_map, hq]
    exact hp
  obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff (FractionRing (Si i))).mp (hic i).2 hyint
  refine ⟨(c : S), ?_⟩
  rw [← hφy, ← hc, hφ]
  rfl

end IndEtaleNormal

/- English proof (translation)
Introduce `R S _ _ _ _ _ _ h`. Take `⟨ι, _, _, _, Si, hmono, hcov, hloc⟩` from `h`. Establish `hic : ∀ i, IsDomain (Si i) ∧ IsIntegrallyClosed (Si i)`. Introduce `i`. Take `⟨A, _, _, _, q, _, ⟨e⟩⟩` from `hloc i`.

Take `⟨h1, h2⟩` from `etale_localization_atPrime_isDomain_isIntegrallyClosed R A q`. Conclude with `⟨MulEquiv.isDomain (Localization.AtPrime q) e.symm.toMulEquiv, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩`. Use `haveI := IndEtaleNormal.isDomain Si hmono hcov (fun i => (hic i).1)`. Conclude with `⟨inferInstance, IndEtaleNormal.isIntegrallyClosed Si hmono hcov hic⟩`.
-/
theorem indEtale_isDomain_isIntegrallyClosed :
    ∀ (R S : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing S] [Algebra R S]
      [Nontrivial S], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
        (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧
        ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A)
          (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) →
      IsDomain S ∧ IsIntegrallyClosed S := by
  intro R S _ _ _ _ _ _ h
  obtain ⟨ι, _, _, _, Si, hmono, hcov, hloc⟩ := h
  have hic : ∀ i, IsDomain (Si i) ∧ IsIntegrallyClosed (Si i) := by
    intro i
    obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hloc i
    obtain ⟨h1, h2⟩ := etale_localization_atPrime_isDomain_isIntegrallyClosed R A q
    exact ⟨MulEquiv.isDomain (Localization.AtPrime q) e.symm.toMulEquiv,
      IsIntegrallyClosed.of_equiv e.toRingEquiv⟩
  haveI := IndEtaleNormal.isDomain Si hmono hcov (fun i => (hic i).1)
  exact ⟨inferInstance, IndEtaleNormal.isIntegrallyClosed Si hmono hcov hic⟩

end GlobalTheory
