import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexBlockLevel

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

namespace GlobalTheory.NormRatio

/- English proof (translation)
Introduce `D 𝔪 h𝔪 hcop a a' R hR hRu`. Take `⟨ρ, hρ⟩` from `GlobalTheory.T.exists_reduction_maxLevel_unitary_mod_ideal D 𝔪 h𝔪 a`. Establish `hker : ∀ k : ↥(intG D a), ρ k = 1 ↔ CongOne D 𝔪 (k : Formalism.MainNotions.StandardLatticesGL3.GA D a)`. Introduce `k`. Prove the components needed by the constructor for the conclusion.

Introduce `h i j`. Establish `h1` using `(hρ k i j (((1 : Matrix (Fin a) (Fin a) (𝓞 D.host.E)) i j))).1 (by`. Rewrite using `[h]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hij])`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify `h1` using `[Matrix.sub_apply]`.

Simplify `h1` using `[Matrix.sub_apply, Matrix.one_apply_ne hij]`. Introduce `h`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Use `((hρ k i j (((1 : Matrix (Fin a) (Fin a) (𝓞 D.host.E)) i j))).2 ?_).trans ?_` and prove the remaining obligations.

Establish `h1` using `h i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify `h1` using `[Matrix.sub_apply]`. Simplify `h1` using `[Matrix.sub_apply, Matrix.one_apply_ne hij]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hij]`. Establish `hsurj : Function.Surjective ρ`.

Introduce `g'`. Use `choose g hg using fun i j => Ideal.Quotient.mk_surjective (I := 𝔪) (((g' : GL (Fin a) (𝓞 D.host.E ⧸ 𝔪)) : Matrix (Fin a) (Fin a) (𝓞 D.host.E ⧸ 𝔪)) i j)`. Establish `hgm : (Matrix.of g).map (Ideal.Quotient.mk 𝔪) = ((g' : GL (Fin a) (𝓞 D.host.E ⧸ 𝔪)) : Matrix (Fin a) (Fin a) (𝓞 D.host.E ⧸ 𝔪))`. Use extensionality with `i j`. Simplify using `[hg]`.

Take `⟨k, hk, hk'⟩` from `GlobalTheory.T.exists_maxLevel_unitary_congr_mod_ideal D 𝔪 h𝔪 hcop a (Matrix.of g) (by rw [hgm]; exact Matrix.isUnits_det_units g')`. Simplify using `only [Matrix.of_apply] at hk'`. Use `⟨⟨k, hk⟩, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`.

Conclude with `((hρ ⟨k, hk⟩ i j (g i j)).2 (hk' i j)).trans (hg i j)`. Set `f : R → GL (Fin a) (𝓞 D.host.E ⧸ 𝔪)` to `fun r => ρ ⟨r.1, hR r.1 r.2⟩`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr⟩ ⟨r', hr'⟩ h`.

Establish `h1 : ρ (⟨r, hR r hr⟩⁻¹ * ⟨r', hR r' hr'⟩) = 1`. Rewrite using `[map_mul, map_inv]`. Conclude with `inv_mul_eq_one.2 h`. Establish `h2 : CongOne D 𝔪 (r⁻¹ * r')` using `(hker _).1 h1`. Establish `h3 : CongOne D 𝔪 (r'⁻¹ * r')`.

Rewrite using `[inv_mul_cancel]`. Conclude with `(hker 1).1 (map_one ρ)`. Take `⟨r₀, -, hu⟩` from `hRu r' (hR r' hr')`. Conclude with `Subtype.ext ((hu r ⟨hr, h2⟩).trans (hu r' ⟨hr', h3⟩).symm)`. Introduce `g'`.

Take `⟨k, rfl⟩` from `hsurj g'`. Take `⟨r, ⟨hr, hc⟩, -⟩` from `hRu k.1 k.2`. Use `⟨⟨r, hr⟩, ?_⟩` and prove the remaining obligations. Establish `h1 : ρ (⟨r, hR r hr⟩⁻¹ * k) = 1` using `(hker _).2 hc`. Rewrite `h1` using `[map_mul, map_inv]`.

Conclude with `(inv_mul_eq_one.1 h1)`. Establish `hcard : R.card = Nat.card (GL (Fin a) (𝓞 D.host.E ⧸ 𝔪))`. Rewrite using `[← Nat.card_eq_finsetCard, Nat.card_congr (Equiv.ofBijective f hf)]`. Rewrite using `[hcard, GlobalTheory.T.card_GL_ringOfIntegers_quotient_prod_factors _ 𝔪 h𝔪 a, GlobalTheory.StdLoc.absNorm_eq_prod h𝔪, ← Finset.prod_pow, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, locNorm]`. Use `Finset.prod_congr rfl fun w hw => ?_` and prove the remaining obligations.

Establish `hq : (Ideal.absNorm w : ℝ) ≠ 0`. Establish `hw0 : w ≠ ⊥` using `fun h => by`. Rewrite `hw` using `[h]`. Conclude with `zero_notMem_normalizedFactors _ (Multiset.mem_toFinset.1 hw)`. Conclude with `(Ideal.absNorm_eq_zero_iff.not.2 hw0)` after adjusting the coercions.

Use `set q : ℝ := (Ideal.absNorm w : ℝ)`. Use `set c := (normalizedFactors 𝔪).count w`. Establish `e : (q ^ c) ^ (a * (a + a')) = q ^ (c * a ^ 2) * q ^ (c * a * a')`. Rewrite using `[← pow_mul, ← pow_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, mul_inv, ← mul_assoc, mul_comm (q ^ (c * a ^ 2)) _, mul_assoc, mul_assoc, mul_inv_cancel_left₀ (pow_ne_zero _ hq)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_transversal_mul : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (a a' : ℕ) (R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D a)),
  (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) →
    (R.card : ℝ) * ((Ideal.absNorm 𝔪 : ℝ) ^ (a * (a + a')))⁻¹ = locNorm D 𝔪 a a' := by
  intro D 𝔪 h𝔪 hcop a a' R hR hRu
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_reduction_maxLevel_unitary_mod_ideal D 𝔪 h𝔪 a

  have hker : ∀ k : ↥(intG D a), ρ k = 1 ↔ CongOne D 𝔪 (k : Formalism.MainNotions.StandardLatticesGL3.GA D a) := by
    intro k
    constructor
    · intro h i j
      have h1 := (hρ k i j (((1 : Matrix (Fin a) (Fin a) (𝓞 D.host.E)) i j))).1 (by
        rw [h]
        by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.one_apply_ne hij])
      by_cases hij : i = j
      · subst hij; simpa [Matrix.sub_apply] using h1
      · simpa [Matrix.sub_apply, Matrix.one_apply_ne hij] using h1
    · intro h
      apply Units.ext
      ext i j
      refine ((hρ k i j (((1 : Matrix (Fin a) (Fin a) (𝓞 D.host.E)) i j))).2 ?_).trans ?_
      · have h1 := h i j
        by_cases hij : i = j
        · subst hij; simpa [Matrix.sub_apply] using h1
        · simpa [Matrix.sub_apply, Matrix.one_apply_ne hij] using h1
      · by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.one_apply_ne hij]
  have hsurj : Function.Surjective ρ := by
    intro g'
    choose g hg using fun i j => Ideal.Quotient.mk_surjective (I := 𝔪)
      (((g' : GL (Fin a) (𝓞 D.host.E ⧸ 𝔪)) : Matrix (Fin a) (Fin a) (𝓞 D.host.E ⧸ 𝔪)) i j)
    have hgm : (Matrix.of g).map (Ideal.Quotient.mk 𝔪) =
        ((g' : GL (Fin a) (𝓞 D.host.E ⧸ 𝔪)) : Matrix (Fin a) (Fin a) (𝓞 D.host.E ⧸ 𝔪)) := by
      ext i j; simp [hg]
    obtain ⟨k, hk, hk'⟩ := GlobalTheory.T.exists_maxLevel_unitary_congr_mod_ideal D 𝔪 h𝔪 hcop a (Matrix.of g) (by rw [hgm]; exact Matrix.isUnits_det_units g')
    simp only [Matrix.of_apply] at hk'
    refine ⟨⟨k, hk⟩, ?_⟩
    apply Units.ext
    ext i j
    exact ((hρ ⟨k, hk⟩ i j (g i j)).2 (hk' i j)).trans (hg i j)

  let f : R → GL (Fin a) (𝓞 D.host.E ⧸ 𝔪) := fun r => ρ ⟨r.1, hR r.1 r.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨r, hr⟩ ⟨r', hr'⟩ h
      have h1 : ρ (⟨r, hR r hr⟩⁻¹ * ⟨r', hR r' hr'⟩) = 1 := by
        rw [map_mul, map_inv]; exact inv_mul_eq_one.2 h
      have h2 : CongOne D 𝔪 (r⁻¹ * r') := (hker _).1 h1
      have h3 : CongOne D 𝔪 (r'⁻¹ * r') := by
        rw [inv_mul_cancel]
        exact (hker 1).1 (map_one ρ)
      obtain ⟨r₀, -, hu⟩ := hRu r' (hR r' hr')
      exact Subtype.ext ((hu r ⟨hr, h2⟩).trans (hu r' ⟨hr', h3⟩).symm)
    · intro g'
      obtain ⟨k, rfl⟩ := hsurj g'
      obtain ⟨r, ⟨hr, hc⟩, -⟩ := hRu k.1 k.2
      refine ⟨⟨r, hr⟩, ?_⟩
      have h1 : ρ (⟨r, hR r hr⟩⁻¹ * k) = 1 := (hker _).2 hc
      rw [map_mul, map_inv] at h1
      exact (inv_mul_eq_one.1 h1)
  have hcard : R.card = Nat.card (GL (Fin a) (𝓞 D.host.E ⧸ 𝔪)) := by
    rw [← Nat.card_eq_finsetCard, Nat.card_congr (Equiv.ofBijective f hf)]
  rw [hcard, GlobalTheory.T.card_GL_ringOfIntegers_quotient_prod_factors _ 𝔪 h𝔪 a, GlobalTheory.StdLoc.absNorm_eq_prod h𝔪, ← Finset.prod_pow, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, locNorm]
  refine Finset.prod_congr rfl fun w hw => ?_
  have hq : (Ideal.absNorm w : ℝ) ≠ 0 := by
    have hw0 : w ≠ ⊥ := fun h => by
      rw [h] at hw; exact zero_notMem_normalizedFactors _ (Multiset.mem_toFinset.1 hw)
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hw0)
  set q : ℝ := (Ideal.absNorm w : ℝ)
  set c := (normalizedFactors 𝔪).count w
  have e : (q ^ c) ^ (a * (a + a')) = q ^ (c * a ^ 2) * q ^ (c * a * a') := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  rw [e, mul_inv, ← mul_assoc, mul_comm (q ^ (c * a ^ 2)) _, mul_assoc, mul_assoc, mul_inv_cancel_left₀ (pow_ne_zero _ hq)]
  ring

end GlobalTheory.NormRatio
