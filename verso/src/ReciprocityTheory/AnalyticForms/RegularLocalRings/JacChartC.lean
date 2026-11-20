import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartB
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

namespace ReciprocityTheory.AnForm.R.JacobianCriterionAlt

open MvPolynomial IsLocalRing

noncomputable section

variable {n : ℕ}

/- English proof (translation)
Take `⟨hloc, hnoeth⟩` from `locRing_isLocalRing_isNoetherian' K p hp`. Establish `hcot` using `finrank_cot_eq p K`. Establish `hrank : c ≤ Module.finrank ℂ (jacS K p)`. Set `v : Fin c → jacS K p` to `fun i => ⟨gradP p (F i), Submodule.subset_span ⟨F i, hF i, rfl⟩⟩`. Establish `hv : LinearIndependent ℂ v` using `LinearIndependent.of_comp (jacS K p).subtype hlin`.

Simplify using `using hv.fintype_card_le_finrank`. Establish `hcotle : Module.finrank (ResidueField (locR K p)) (CotangentSpace (locR K p)) ≤ n - c`. Use linear arithmetic over natural numbers and integers. Establish `hdimle : ringKrullDim (locR K p) ≤ ((n - c : ℕ) : WithBot ℕ∞)`. Use `(ringKrullDim_le_spanFinrank_maximalIdeal _).trans ?_` and prove the remaining obligations.

Rewrite using `[spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]`. Conclude with `hcotle` after adjusting the coercions. Take `⟨𝔮, h𝔮min, h𝔮P, h𝔮c⟩` from `hq`. Establish `h𝔮prime : 𝔮.IsPrime` using `h𝔮min.1.1`. Establish `hK𝔮 : K ≤ 𝔮` using `h𝔮min.1.2`.

Use `set Pb : Ideal (MvPolynomial (Fin n) ℂ ⧸ 𝔮) := (ptI p).map (Ideal.Quotient.mk 𝔮) with hPb`. Establish `hker : RingHom.ker (Ideal.Quotient.mk 𝔮) ≤ ptI p` using `by rw [Ideal.mk_ker]; exact h𝔮P`. Establish `hPbprime : Pb.IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker`. Establish `hPmax : (ptI p).IsMaximal` using `RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, eval_C _⟩)`. Establish `hPbmax : Pb.IsMaximal` using `(Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective hPmax).resolve_left hPbprime.ne_top`.

Establish `hheight` using `ReciprocityTheory.CA.height_add_height_maximal_quotient_field ℂ n 𝔮 Pb`. Establish `hmemPb : ∀ s, Ideal.Quotient.mk 𝔮 s ∈ Pb ↔ s ∈ ptI p`. Introduce `s`. Rewrite using `[hPb, Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr h𝔮P]`. Set `gq : MvPolynomial (Fin n) ℂ →+* Localization.AtPrime Pb` to `(algebraMap _ (Localization.AtPrime Pb)).comp (Ideal.Quotient.mk 𝔮)`.

Establish `hunits : ∀ y : (ptI p).primeCompl, IsUnit (gq y)` using `fun y => IsLocalization.map_units (Localization.AtPrime Pb) (⟨Ideal.Quotient.mk 𝔮 y, fun h => y.2 ((hmemPb y).mp h)⟩ : Pb.primeCompl)`. Set `φ : localization₂ p →+* Localization.AtPrime Pb` to `IsLocalization.lift (M := (ptI p).primeCompl) hunits`. Establish `hφ : Function.Surjective φ`. Introduce `t`. Take `⟨⟨x, y⟩, rfl⟩` from `IsLocalization.mk'_surjective Pb.primeCompl t`.

Take `⟨x', rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨y', hy'⟩` from `Ideal.Quotient.mk_surjective (y : MvPolynomial (Fin n) ℂ ⧸ 𝔮)`. Establish `hy'P : y' ∉ ptI p` using `fun h => y.2 (hy' ▸ (hmemPb y').mpr h)`. Use `⟨IsLocalization.mk' (localization₂ p) x' (⟨y', hy'P⟩ : (ptI p).primeCompl), ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocalization.lift_mk'_spec]`.

Simplify using `only [gq, RingHom.coe_comp, Function.comp_apply, hy']`. Rewrite using `[IsLocalization.mk'_spec']`. Establish `hφK : ∀ a ∈ Ideal.map (algebraMap _ (localization₂ p)) K, φ a = 0`. Introduce `a ha`. Establish `: Ideal.map (algebraMap _ (localization₂ p)) K ≤ RingHom.ker φ`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `k hk`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker]`. Simplify using `only [φ, IsLocalization.lift_eq, gq, RingHom.coe_comp, Function.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr (hK𝔮 hk), map_zero]`. Conclude with `this ha`.

Establish `hφB : Function.Surjective (Ideal.Quotient.lift _ φ hφK)` using `Ideal.Quotient.lift_surjective_of_surjective _ _ hφ`. Establish `hle` using `ringKrullDim_le_of_surjective _ hφB`. Rewrite `hle` using `[IsLocalization.AtPrime.ringKrullDim_eq_height Pb (Localization.AtPrime Pb)]`. Establish `hqfin : 𝔮.height ≠ ⊤` using `ne_top_of_le_ne_top (ENat.natCast_ne_top c) h𝔮c`. Take `⟨k, hk⟩` from `ENat.ne_top_iff_exists.mp hqfin`.

Establish `hPbfin : Pb.height ≠ ⊤`. Introduce `h`. Rewrite `hheight` using `[h, add_top]`. Conclude with `ENat.top_ne_natCast n hheight`. Take `⟨m, hm⟩` from `ENat.ne_top_iff_exists.mp hPbfin`.

Establish `hkm : k + m = n` using `by rw [← hk, ← hm] at hheight; exact_mod_cast hheight`. Establish `hkc : k ≤ c` using `by rw [← hk] at h𝔮c; exact_mod_cast h𝔮c`. Rewrite `hle` using `[← hm]`. Establish `hdimge : ((n - c : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (locR K p)`. Use `le_trans ?_ hle` and prove the remaining obligations.

Use `show (((n - c : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ ((m : ℕ∞) : WithBot ℕ∞)`. Conclude with `WithBot.coe_le_coe.mpr (Nat.cast_le.mpr (by omega))`. Establish `hdim` using `le_antisymm hdimle hdimge`. Use `⟨?_, hdim⟩` and prove the remaining obligations. Apply `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` to reduce the goal to its premises.

Rewrite using `[spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, hdim]`. Conclude with `hcotle` after adjusting the coercions.
-/
theorem isRegularLocalRing_of_jacobian' (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hp : ∀ h ∈ K, eval p h = 0) {c : ℕ} (F : Fin c → MvPolynomial (Fin n) ℂ) (hF : ∀ i, F i ∈ K)
    (hlin : LinearIndependent ℂ (fun i => gradP p (F i)))
    (hq : ∃ 𝔮 ∈ K.minimalPrimes, 𝔮 ≤ ptI p ∧ 𝔮.height ≤ c) :
    IsRegularLocalRing (locR K p) ∧ ringKrullDim (locR K p) = ((n - c : ℕ) : WithBot ℕ∞) := by
  obtain ⟨hloc, hnoeth⟩ := locRing_isLocalRing_isNoetherian' K p hp
  have hcot := finrank_cot_eq p K
  have hrank : c ≤ Module.finrank ℂ (jacS K p) := by
    let v : Fin c → jacS K p := fun i => ⟨gradP p (F i), Submodule.subset_span ⟨F i, hF i, rfl⟩⟩
    have hv : LinearIndependent ℂ v := LinearIndependent.of_comp (jacS K p).subtype hlin
    simpa using hv.fintype_card_le_finrank
  have hcotle : Module.finrank (ResidueField (locR K p)) (CotangentSpace (locR K p)) ≤ n - c := by
    omega
  have hdimle : ringKrullDim (locR K p) ≤ ((n - c : ℕ) : WithBot ℕ∞) := by
    refine (ringKrullDim_le_spanFinrank_maximalIdeal _).trans ?_
    rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    exact_mod_cast hcotle
  obtain ⟨𝔮, h𝔮min, h𝔮P, h𝔮c⟩ := hq
  have h𝔮prime : 𝔮.IsPrime := h𝔮min.1.1
  have hK𝔮 : K ≤ 𝔮 := h𝔮min.1.2
  set Pb : Ideal (MvPolynomial (Fin n) ℂ ⧸ 𝔮) := (ptI p).map (Ideal.Quotient.mk 𝔮) with hPb
  have hker : RingHom.ker (Ideal.Quotient.mk 𝔮) ≤ ptI p := by rw [Ideal.mk_ker]; exact h𝔮P
  have hPbprime : Pb.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hPmax : (ptI p).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, eval_C _⟩)
  have hPbmax : Pb.IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective hPmax).resolve_left
      hPbprime.ne_top
  have hheight := ReciprocityTheory.CA.height_add_height_maximal_quotient_field ℂ n 𝔮 Pb
  have hmemPb : ∀ s, Ideal.Quotient.mk 𝔮 s ∈ Pb ↔ s ∈ ptI p := by
    intro s; rw [hPb, Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr h𝔮P]
  let gq : MvPolynomial (Fin n) ℂ →+* Localization.AtPrime Pb :=
    (algebraMap _ (Localization.AtPrime Pb)).comp (Ideal.Quotient.mk 𝔮)
  have hunits : ∀ y : (ptI p).primeCompl, IsUnit (gq y) := fun y =>
    IsLocalization.map_units (Localization.AtPrime Pb)
      (⟨Ideal.Quotient.mk 𝔮 y, fun h => y.2 ((hmemPb y).mp h)⟩ : Pb.primeCompl)
  let φ : localization₂ p →+* Localization.AtPrime Pb :=
    IsLocalization.lift (M := (ptI p).primeCompl) hunits
  have hφ : Function.Surjective φ := by
    intro t
    obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective Pb.primeCompl t
    obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y', hy'⟩ := Ideal.Quotient.mk_surjective (y : MvPolynomial (Fin n) ℂ ⧸ 𝔮)
    have hy'P : y' ∉ ptI p := fun h => y.2 (hy' ▸ (hmemPb y').mpr h)
    refine ⟨IsLocalization.mk' (localization₂ p) x' (⟨y', hy'P⟩ : (ptI p).primeCompl), ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    simp only [gq, RingHom.coe_comp, Function.comp_apply, hy']
    rw [IsLocalization.mk'_spec']
  have hφK : ∀ a ∈ Ideal.map (algebraMap _ (localization₂ p)) K, φ a = 0 := by
    intro a ha
    have : Ideal.map (algebraMap _ (localization₂ p)) K ≤ RingHom.ker φ := by
      rw [Ideal.map_le_iff_le_comap]
      intro k hk
      rw [Ideal.mem_comap, RingHom.mem_ker]
      simp only [φ, IsLocalization.lift_eq, gq, RingHom.coe_comp, Function.comp_apply,
        Ideal.Quotient.eq_zero_iff_mem.mpr (hK𝔮 hk), map_zero]
    exact this ha
  have hφB : Function.Surjective (Ideal.Quotient.lift _ φ hφK) :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hφ
  have hle := ringKrullDim_le_of_surjective _ hφB
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height Pb (Localization.AtPrime Pb)] at hle
  have hqfin : 𝔮.height ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top c) h𝔮c
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hqfin
  have hPbfin : Pb.height ≠ ⊤ := by
    intro h; rw [h, add_top] at hheight; exact ENat.top_ne_natCast n hheight
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hPbfin
  have hkm : k + m = n := by rw [← hk, ← hm] at hheight; exact_mod_cast hheight
  have hkc : k ≤ c := by rw [← hk] at h𝔮c; exact_mod_cast h𝔮c
  rw [← hm] at hle
  have hdimge : ((n - c : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (locR K p) := by
    refine le_trans ?_ hle
    show (((n - c : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ ((m : ℕ∞) : WithBot ℕ∞)
    exact WithBot.coe_le_coe.mpr (Nat.cast_le.mpr (by omega))
  have hdim := le_antisymm hdimle hdimge
  refine ⟨?_, hdim⟩
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, hdim]
  exact_mod_cast hcotle

end

end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
