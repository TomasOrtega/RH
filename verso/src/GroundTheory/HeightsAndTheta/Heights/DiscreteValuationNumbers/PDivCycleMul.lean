import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

section General

variable {A : Type*} [CommRing A]

/- English proof (translation)
Take `⟨q, hqQ, hqW⟩` from `Set.not_subset.mp h`. Rewrite using `[LocalizedModule.subsingleton_iff]`. Introduce `m`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective m`. Use `⟨q, hqW, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Q.mul_mem_right a hqQ`.
-/
theorem localizedQuot_subsingleton_of_not_le (Q W : Ideal A) [W.IsPrime] (h : ¬ Q ≤ W) :
    Subsingleton (LocalizedModule W.primeCompl (A ⧸ Q)) := by
  obtain ⟨q, hqQ, hqW⟩ := Set.not_subset.mp h
  rw [LocalizedModule.subsingleton_iff]
  intro m
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
  refine ⟨q, hqW, ?_⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Q.mul_mem_right a hqQ

/- English proof (translation)
Establish `hle : P ⊔ Ideal.span {x * y} ≤ P ⊔ Ideal.span {x}` using `sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self x))) P`. Set `g₁ : (A ⧸ (P ⊔ Ideal.span {y})) →ₗ[A] A ⧸ (P ⊔ Ideal.span {x * y})` to `Submodule.mapQ _ _ (LinearMap.mulLeft A x) (fun a ha => by`. Take `⟨p, hp, r, hr, rfl⟩` from `Submodule.mem_sup.mp ha`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hr`. Use `show x * (p + c * y) ∈ P ⊔ Ideal.span {x * y}`.

Establish `e : x * (p + c * y) = x * p + c * (x * y)` using `by ring`. Rewrite using `[e]`. Conclude with `Submodule.add_mem_sup (P.mul_mem_left _ hp) (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩))`. Set `g₂ : (A ⧸ (P ⊔ Ideal.span {x * y})) →ₗ[A] A ⧸ (P ⊔ Ideal.span {x})` to `Submodule.mapQ _ _ LinearMap.id (fun a ha => hle ha)`. Establish `hinj : Function.Injective g₁`.

Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `z hz`. Proceed by induction on `z using Submodule.Quotient.induction_on with | _ a => ?_`. Rewrite `hz` using `[LinearMap.mem_ker]`. Simplify using `only [g₁, Submodule.mapQ_apply, LinearMap.mulLeft_apply, Submodule.Quotient.mk_eq_zero] at hz`.

Simplify using `only [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]`. Take `⟨p, hp, r, hr, hpr⟩` from `Submodule.mem_sup.mp hz`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hr`. Establish `hm : x * (a - c * y) ∈ P`. Establish `e : x * (a - c * y) = p` using `by linear_combination hpr.symm`.

Rewrite using `[e]`. Conclude with `hp`. Establish `ha : a - c * y ∈ P` using `(‹P.IsPrime›.mem_or_mem hm).resolve_left hx`. Establish `e : a = (a - c * y) + c * y` using `by ring`. Rewrite using `[e]`.

Conclude with `Submodule.add_mem_sup ha (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩)`. Establish `hsurj : Function.Surjective g₂`. Introduce `z`. Proceed by induction on `z using Submodule.Quotient.induction_on with | _ a => ?_`. Conclude with `⟨Submodule.Quotient.mk a, rfl⟩`.

Establish `hex : Function.Exact g₁ g₂`. Introduce `z`. Proceed by induction on `z using Submodule.Quotient.induction_on with | _ a => ?_`. Simplify using `only [g₂, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero, Set.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce `ha`. Take `⟨p, hp, r, hr, rfl⟩` from `Submodule.mem_sup.mp ha`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hr`. Use `⟨Submodule.Quotient.mk c, ?_⟩` and prove the remaining obligations. Simplify using `only [g₁, Submodule.mapQ_apply, LinearMap.mulLeft_apply]`.

Rewrite using `[Submodule.Quotient.eq]`. Establish `e : x * c - (p + c * x) = -p` using `by ring`. Rewrite using `[e]`. Conclude with `Submodule.mem_sup_left (P.neg_mem hp)`. Introduce and unpack `⟨z, hz⟩`.

Proceed by induction on `z using Submodule.Quotient.induction_on with | _ c => ?_`. Simplify using `only [g₁, Submodule.mapQ_apply, LinearMap.mulLeft_apply] at hz`. Rewrite `hz` using `[Submodule.Quotient.eq]`. Establish `e : a = -(x * c - a) + c * x` using `by ring`. Rewrite using `[e]`.

Conclude with `Submodule.add_mem _ (Submodule.neg_mem _ (hle hz)) (Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩))`. Conclude with `Module.length_eq_add_of_exact (R := Localization.AtPrime W) (LocalizedModule.map W.primeCompl g₁) (LocalizedModule.map W.primeCompl g₂) (LocalizedModule.map_injective _ _ hinj) (LocalizedModule.map_surjective _ _ hsurj) (LocalizedModule.map_exact _ _ _ hex)`.
-/
theorem length_localizedQuot_sup_span_mul (P W : Ideal A) [P.IsPrime] [W.IsPrime] {x : A} (y : A)
    (hx : x ∉ P) :
    Module.length (Localization.AtPrime W)
        (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {x * y}))) =
      Module.length (Localization.AtPrime W)
          (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {y}))) +
        Module.length (Localization.AtPrime W)
          (LocalizedModule W.primeCompl (A ⧸ (P ⊔ Ideal.span {x}))) := by
  have hle : P ⊔ Ideal.span {x * y} ≤ P ⊔ Ideal.span {x} :=
    sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self x))) P
  let g₁ : (A ⧸ (P ⊔ Ideal.span {y})) →ₗ[A] A ⧸ (P ⊔ Ideal.span {x * y}) :=
    Submodule.mapQ _ _ (LinearMap.mulLeft A x) (fun a ha => by
      obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      show x * (p + c * y) ∈ P ⊔ Ideal.span {x * y}
      have e : x * (p + c * y) = x * p + c * (x * y) := by ring
      rw [e]
      exact Submodule.add_mem_sup (P.mul_mem_left _ hp) (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩))
  let g₂ : (A ⧸ (P ⊔ Ideal.span {x * y})) →ₗ[A] A ⧸ (P ⊔ Ideal.span {x}) :=
    Submodule.mapQ _ _ LinearMap.id (fun a ha => hle ha)
  have hinj : Function.Injective g₁ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    induction z using Submodule.Quotient.induction_on with | _ a => ?_
    rw [LinearMap.mem_ker] at hz
    simp only [g₁, Submodule.mapQ_apply, LinearMap.mulLeft_apply,
      Submodule.Quotient.mk_eq_zero] at hz
    simp only [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    obtain ⟨p, hp, r, hr, hpr⟩ := Submodule.mem_sup.mp hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have hm : x * (a - c * y) ∈ P := by
      have e : x * (a - c * y) = p := by linear_combination hpr.symm
      rw [e]; exact hp
    have ha : a - c * y ∈ P := (‹P.IsPrime›.mem_or_mem hm).resolve_left hx
    have e : a = (a - c * y) + c * y := by ring
    rw [e]
    exact Submodule.add_mem_sup ha (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩)
  have hsurj : Function.Surjective g₂ := by
    intro z
    induction z using Submodule.Quotient.induction_on with | _ a => ?_
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  have hex : Function.Exact g₁ g₂ := by
    intro z
    induction z using Submodule.Quotient.induction_on with | _ a => ?_
    simp only [g₂, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
      Set.mem_range]
    constructor
    · intro ha
      obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      refine ⟨Submodule.Quotient.mk c, ?_⟩
      simp only [g₁, Submodule.mapQ_apply, LinearMap.mulLeft_apply]
      rw [Submodule.Quotient.eq]
      have e : x * c - (p + c * x) = -p := by ring
      rw [e]
      exact Submodule.mem_sup_left (P.neg_mem hp)
    · rintro ⟨z, hz⟩
      induction z using Submodule.Quotient.induction_on with | _ c => ?_
      simp only [g₁, Submodule.mapQ_apply, LinearMap.mulLeft_apply] at hz
      rw [Submodule.Quotient.eq] at hz
      have e : a = -(x * c - a) + c * x := by ring
      rw [e]
      exact Submodule.add_mem _ (Submodule.neg_mem _ (hle hz))
        (Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩))
  exact Module.length_eq_add_of_exact (R := Localization.AtPrime W)
    (LocalizedModule.map W.primeCompl g₁) (LocalizedModule.map W.primeCompl g₂)
    (LocalizedModule.map_injective _ _ hinj) (LocalizedModule.map_surjective _ _ hsurj)
    (LocalizedModule.map_exact _ _ _ hex)

/- English proof (translation)
Establish `: IsNoetherianRing (Localization.AtPrime W)` using `IsLocalization.isNoetherianRing W.primeCompl _ inferInstance`. Establish `hI : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈ (J.map (algebraMap A (Localization.AtPrime W))).minimalPrimes`. Rewrite using `[IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W) J, Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]`. Conclude with `hW`. Establish `: IsArtinianRing (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W)))` using `IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hI`.

Establish `: IsArtinian (Localization.AtPrime W) (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W)))` using `isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := J.map (algebraMap A (Localization.AtPrime W))))`. Establish `: IsNoetherian (Localization.AtPrime W) (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W)))` using `isNoetherian_quotient _`. Use `IsLocalization.linearMap_compatibleSMul W.primeCompl` as an intermediate fact. Set `e` to `(IsLocalizedModule.linearEquiv W.primeCompl (J.toLocalizedQuotient' (Localization.AtPrime W) W.primeCompl (Algebra.linearMap A (Localization.AtPrime W))) (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ J))).restrictScalars (Localization.AtPrime W)`. Rewrite using `[← e.length_eq, Ideal.localized'_eq_map]`.

Conclude with `Module.length_ne_top`.
-/
theorem length_localizedQuot_ne_top [IsNoetherianRing A] (J W : Ideal A) [W.IsPrime]
    (hW : W ∈ J.minimalPrimes) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) ≠ ⊤ := by
  have : IsNoetherianRing (Localization.AtPrime W) :=
    IsLocalization.isNoetherianRing W.primeCompl _ inferInstance
  have hI : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈
      (J.map (algebraMap A (Localization.AtPrime W))).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W) J,
      Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
    exact hW
  have : IsArtinianRing (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W))) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hI
  have : IsArtinian (Localization.AtPrime W)
      (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W))) :=
    isArtinian_of_surjective_algebraMap
      (Ideal.Quotient.mk_surjective (I := J.map (algebraMap A (Localization.AtPrime W))))
  have : IsNoetherian (Localization.AtPrime W)
      (Localization.AtPrime W ⧸ J.map (algebraMap A (Localization.AtPrime W))) :=
    isNoetherian_quotient _
  have := IsLocalization.linearMap_compatibleSMul W.primeCompl
  let e := (IsLocalizedModule.linearEquiv W.primeCompl
    (J.toLocalizedQuotient' (Localization.AtPrime W) W.primeCompl
      (Algebra.linearMap A (Localization.AtPrime W)))
    (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ J))).restrictScalars (Localization.AtPrime W)
  rw [← e.length_eq, Ideal.localized'_eq_map]
  exact Module.length_ne_top

/- English proof (translation)
Establish `hWp : W.IsPrime` using `hW.1.1`. Establish `hxW : x ∈ W` using `hW.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))`. Establish `hPW : P ≤ W` using `le_sup_left.trans hW.1.2`. Use `⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr (W.mul_mem_right y hxW))⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `Q ⟨hQp, hQ⟩ hQW`.

Establish `hPQ : P ≤ Q` using `le_sup_left.trans hQ`. Break down `hQp.mem_or_mem (hQ (Ideal.mem_sup_right (Ideal.subset_span rfl))) with hxQ | hyQ` into its components or cases. Conclude with `hW.2 ⟨hQp, sup_le hPQ ((Ideal.span_singleton_le_iff_mem _).mpr hxQ)⟩ hQW`. Assume the negation of the conclusion as `hWQ`. Establish `hlt : Q < W` using `lt_of_le_of_ne hQW (fun h => hWQ h.ge)`.

Establish `hPQlt : P < Q` using `lt_of_le_of_ne hPQ (fun h => hy (h ▸ hyQ))`. Establish `hker : RingHom.ker (Ideal.Quotient.mk P) = P` using `Ideal.mk_ker`. Establish `hQ' : (Q.map (Ideal.Quotient.mk P)).IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hker.le.trans hPQ)`. Establish `hW' : (W.map (Ideal.Quotient.mk P)).IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hker.le.trans hPW)`. Establish `h0 : (⊥ : Ideal (A ⧸ P)).IsPrime` using `Ideal.isPrime_bot`.

Establish `hcQ : (Q.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = Q`. Rewrite using `[Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hPQ]`. Establish `hcW : (W.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = W`. Rewrite using `[Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hPW]`. Establish `hcP : (⊥ : Ideal (A ⧸ P)).comap (Ideal.Quotient.mk P) = P`.

Rewrite using `[← RingHom.ker_eq_comap_bot, hker]`. Establish `h1 : (⊥ : Ideal (A ⧸ P)) < Q.map (Ideal.Quotient.mk P)` using `lt_of_le_of_ne bot_le (fun h => hPQlt.ne (hcP.symm.trans ((congrArg (Ideal.comap (Ideal.Quotient.mk P)) h).trans hcQ)))`. Establish `h2 : Q.map (Ideal.Quotient.mk P) < W.map (Ideal.Quotient.mk P)` using `lt_of_le_of_ne (Ideal.map_mono hQW) (fun h => hlt.ne (hcQ.symm.trans ((congrArg (Ideal.comap (Ideal.Quotient.mk P)) h).trans hcW)))`. Establish `hb` using `Ideal.height_add_one_le_of_lt_of_isPrime h1`. Establish `hc` using `Ideal.height_add_one_le_of_lt_of_isPrime h2`.

Establish `hk` using `Ideal.map_height_le_one_of_mem_minimalPrimes hW`. Establish `h2le : (2 : ℕ∞) ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Conclude with `absurd h2le (by norm_num)`.
-/
theorem mem_minimalPrimes_sup_span_mul [IsNoetherianRing A] {P W : Ideal A} [P.IsPrime] {x y : A}
    (hy : y ∉ P) (hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes) :
    W ∈ (P ⊔ Ideal.span {x * y}).minimalPrimes := by
  have hWp : W.IsPrime := hW.1.1
  have hxW : x ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  refine ⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr (W.mul_mem_right y hxW))⟩, ?_⟩
  rintro Q ⟨hQp, hQ⟩ hQW
  have hPQ : P ≤ Q := le_sup_left.trans hQ
  rcases hQp.mem_or_mem (hQ (Ideal.mem_sup_right (Ideal.subset_span rfl))) with hxQ | hyQ
  · exact hW.2 ⟨hQp, sup_le hPQ ((Ideal.span_singleton_le_iff_mem _).mpr hxQ)⟩ hQW
  by_contra hWQ
  have hlt : Q < W := lt_of_le_of_ne hQW (fun h => hWQ h.ge)
  have hPQlt : P < Q := lt_of_le_of_ne hPQ (fun h => hy (h ▸ hyQ))
  have hker : RingHom.ker (Ideal.Quotient.mk P) = P := Ideal.mk_ker
  have hQ' : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hker.le.trans hPQ)
  have hW' : (W.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hker.le.trans hPW)
  have h0 : (⊥ : Ideal (A ⧸ P)).IsPrime := Ideal.isPrime_bot
  have hcQ : (Q.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = Q := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      hker, sup_eq_left.mpr hPQ]
  have hcW : (W.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = W := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      hker, sup_eq_left.mpr hPW]
  have hcP : (⊥ : Ideal (A ⧸ P)).comap (Ideal.Quotient.mk P) = P := by
    rw [← RingHom.ker_eq_comap_bot, hker]
  have h1 : (⊥ : Ideal (A ⧸ P)) < Q.map (Ideal.Quotient.mk P) :=
    lt_of_le_of_ne bot_le (fun h => hPQlt.ne
      (hcP.symm.trans ((congrArg (Ideal.comap (Ideal.Quotient.mk P)) h).trans hcQ)))
  have h2 : Q.map (Ideal.Quotient.mk P) < W.map (Ideal.Quotient.mk P) :=
    lt_of_le_of_ne (Ideal.map_mono hQW) (fun h => hlt.ne
      (hcQ.symm.trans ((congrArg (Ideal.comap (Ideal.Quotient.mk P)) h).trans hcW)))
  have hb := Ideal.height_add_one_le_of_lt_of_isPrime h1
  have hc := Ideal.height_add_one_le_of_lt_of_isPrime h2
  have hk := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have h2le : (2 : ℕ∞) ≤ 1 :=
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (⊥ : Ideal (A ⧸ P)).height + 1 + 1 := by gcongr; positivity
      _ ≤ (Q.map (Ideal.Quotient.mk P)).height + 1 := by gcongr
      _ ≤ 1 := hc.trans hk
  exact absurd h2le (by norm_num)

end General

section Forms

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

/- English proof (translation)
Unfold `divCycle`. Distinguish the cases in `hfW : P ⊔ Ideal.span {f} ≤ W`. Establish `hm : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes` using `⟨⟨hW.1.1, hfW⟩, fun Q hQ hQW => hW.2 ⟨hQ.1, hle.trans hQ.2⟩ hQW⟩`. Rewrite using `[dif_pos ⟨hm, hrel⟩]`. Rewrite using `[dif_neg (fun h => hfW h.1.1.2)]`.

Unfold `multAt`. Rewrite using `[Module.length_eq_zero_iff.mpr (localizedQuot_subsingleton_of_not_le _ W hfW)]`. Both sides reduce to the same expression.
-/
theorem divCycle_eq_toNat_multAt {P : Ideal (MRing ι R)} (f g : MRing ι R)
    {W : Ideal (MRing ι R)} [W.IsPrime] (hW : W ∈ (P ⊔ Ideal.span {g}).minimalPrimes)
    (hrel : IsRelevant W) (hle : P ⊔ Ideal.span {g} ≤ P ⊔ Ideal.span {f}) :
    divCycle P f W = ((multAt (P ⊔ Ideal.span {f}) W).toNat : ℤ) := by
  unfold divCycle
  by_cases hfW : P ⊔ Ideal.span {f} ≤ W
  · have hm : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes :=
      ⟨⟨hW.1.1, hfW⟩, fun Q hQ hQW => hW.2 ⟨hQ.1, hle.trans hQ.2⟩ hQW⟩
    rw [dif_pos ⟨hm, hrel⟩]
  · rw [dif_neg (fun h => hfW h.1.1.2)]
    unfold multAt
    rw [Module.length_eq_zero_iff.mpr (localizedQuot_subsingleton_of_not_le _ W hfW)]
    rfl

end Forms

/- English proof (translation)
Introduce `R _ _ K _ ι _ P x y hP hx hy`. Use function extensionality and compare the values at `W`. Establish `hxy : x * y ∉ P` using `fun h => (hP.mem_or_mem h).elim hx hy`. Distinguish the cases in `hrel : IsRelevant W`. Use `swap`.

Simplify using `only [Pi.add_apply]`. Unfold `divCycle`. Rewrite using `[dif_neg (fun h => hrel h.2), dif_neg (fun h => hrel h.2), dif_neg (fun h => hrel h.2), add_zero]`. Distinguish the cases in `hm : W ∈ (P ⊔ Ideal.span {x * y}).minimalPrimes`. Establish `hW : W.IsPrime` using `hm.1.1`.

Establish `hxle : P ⊔ Ideal.span {x * y} ≤ P ⊔ Ideal.span {x}` using `sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self x))) P`. Establish `hyle : P ⊔ Ideal.span {x * y} ≤ P ⊔ Ideal.span {y}` using `sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mul_mem_left _ x (Ideal.mem_span_singleton_self y))) P`. Simplify using `only [Pi.add_apply]`. Rewrite using `[divCycle_eq_toNat_multAt (x * y) (x * y) hm hrel le_rfl, divCycle_eq_toNat_multAt x (x * y) hm hrel hxle, divCycle_eq_toNat_multAt y (x * y) hm hrel hyle]`. Establish `htop` using `length_localizedQuot_ne_top _ W hm`.

Establish `hadd` using `length_localizedQuot_sup_span_mul P W y hx`. Unfold `multAt`. Rewrite `htop`, the goal using `[hadd]`. Rewrite using `[ENat.toNat_add (WithTop.add_ne_top.mp htop).1 (WithTop.add_ne_top.mp htop).2]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Pi.add_apply]`. Unfold `divCycle`. Establish `hnx : ¬ W ∈ (P ⊔ Ideal.span {x}).minimalPrimes` using `fun h => hm (mem_minimalPrimes_sup_span_mul hy h)`. Establish `hny : ¬ W ∈ (P ⊔ Ideal.span {y}).minimalPrimes` using `fun h => hm (mul_comm y x ▸ mem_minimalPrimes_sup_span_mul hx h)`.

Rewrite using `[dif_neg (fun h => hm h.1), dif_neg (fun h => hnx h.1), dif_neg (fun h => hny h.1), add_zero]`.
-/
theorem DivCycleMul.proof : DivCycleMul.Statement := by
  intro R _ _ K _ ι _ P x y hP hx hy
  funext W
  have hxy : x * y ∉ P := fun h => (hP.mem_or_mem h).elim hx hy
  by_cases hrel : IsRelevant W
  swap
  · simp only [Pi.add_apply]
    unfold divCycle
    rw [dif_neg (fun h => hrel h.2), dif_neg (fun h => hrel h.2), dif_neg (fun h => hrel h.2),
      add_zero]
  by_cases hm : W ∈ (P ⊔ Ideal.span {x * y}).minimalPrimes
  · have hW : W.IsPrime := hm.1.1
    have hxle : P ⊔ Ideal.span {x * y} ≤ P ⊔ Ideal.span {x} :=
      sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self x))) P
    have hyle : P ⊔ Ideal.span {x * y} ≤ P ⊔ Ideal.span {y} :=
      sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.mul_mem_left _ x (Ideal.mem_span_singleton_self y))) P
    simp only [Pi.add_apply]
    rw [divCycle_eq_toNat_multAt (x * y) (x * y) hm hrel le_rfl,
      divCycle_eq_toNat_multAt x (x * y) hm hrel hxle,
      divCycle_eq_toNat_multAt y (x * y) hm hrel hyle]
    have htop := length_localizedQuot_ne_top _ W hm
    have hadd := length_localizedQuot_sup_span_mul P W y hx
    unfold multAt
    rw [hadd] at htop ⊢
    rw [ENat.toNat_add (WithTop.add_ne_top.mp htop).1 (WithTop.add_ne_top.mp htop).2]
    push_cast
    ring
  · simp only [Pi.add_apply]
    unfold divCycle
    have hnx : ¬ W ∈ (P ⊔ Ideal.span {x}).minimalPrimes :=
      fun h => hm (mem_minimalPrimes_sup_span_mul hy h)
    have hny : ¬ W ∈ (P ⊔ Ideal.span {y}).minimalPrimes :=
      fun h => hm (mul_comm y x ▸ mem_minimalPrimes_sup_span_mul hx h)
    rw [dif_neg (fun h => hm h.1), dif_neg (fun h => hnx h.1), dif_neg (fun h => hny h.1), add_zero]

end GroundTheory.Heights₂.Heights.NumbersDVR
