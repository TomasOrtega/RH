import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuadraticPowerCharacterSplitPlacesValuesInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits

noncomputable section

namespace GlobalTheory.UnrEuler.ConjVal

open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors TensorProduct
open Formalism.L2.Host (aboveF)
open GlobalTheory.CuspRep (conjSrc conjLoc conjFin conjLoc_spec conjPl_conjSrc conjSrc_injective)
open GlobalTheory.Mem.Chr (ConjPl)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `e : conjI σ (J : FractionalIdeal (𝓞 E)⁰ E) = (J.map (conjO σ) : Ideal (𝓞 E))` using `FractionalIdeal.extended_coeIdeal_eq_map _ _ _`. Establish `hJ' : J.map (conjO σ) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.1 (e ▸ conjI_ne_zero σ (FractionalIdeal.coeIdeal_ne_zero.2 hJ))`. Rewrite using `[e, FractionalIdeal.count_coe E _ hJ', FractionalIdeal.count_coe E _ hJ]`. Use `congr 1`. Establish `hm : Associates.mk J ≠ 0` using `by rwa [ne_eq, Associates.mk_eq_zero]`.

Establish `hm' : Associates.mk (J.map (conjO σ)) ≠ 0` using `by rwa [ne_eq, Associates.mk_eq_zero]`. Establish `key : ∀ k : ℕ, k ≤ (Associates.mk v'.asIdeal).count (Associates.mk (J.map (conjO σ))).factors ↔ k ≤ (Associates.mk v.asIdeal).count (Associates.mk J).factors`. Introduce `k`. Rewrite using `[← Associates.prime_pow_dvd_iff_le hm' v'.associates_irreducible, ← Associates.prime_pow_dvd_iff_le hm v.associates_irreducible, ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.map_le_if …`. Establish `: (v'.asIdeal ^ k).comap (conjO σ) = v.asIdeal ^ k`.

Use extensionality with `x`. Rewrite using `[Ideal.mem_comap, ← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E), ← HeightOneSpectrum.valuation_of_algebraMap (K := E), ← h, ← hc]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)`.
-/
theorem count_map {σ : E →ₐ[F] E} {c : E ≃+* E} (hc : ∀ x, σ x = c x) {v v' : HeightOneSpectrum (𝓞 E)}
    (h : ConjPl c v v') {J : Ideal (𝓞 E)} (hJ : J ≠ 0) :
    FractionalIdeal.count E v' (conjI σ (J : FractionalIdeal (𝓞 E)⁰ E)) =
      FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E) := by
  classical
  have e : conjI σ (J : FractionalIdeal (𝓞 E)⁰ E) = (J.map (conjO σ) : Ideal (𝓞 E)) :=
    FractionalIdeal.extended_coeIdeal_eq_map _ _ _
  have hJ' : J.map (conjO σ) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.1 (e ▸ conjI_ne_zero σ (FractionalIdeal.coeIdeal_ne_zero.2 hJ))
  rw [e, FractionalIdeal.count_coe E _ hJ', FractionalIdeal.count_coe E _ hJ]
  congr 1
  have hm : Associates.mk J ≠ 0 := by rwa [ne_eq, Associates.mk_eq_zero]
  have hm' : Associates.mk (J.map (conjO σ)) ≠ 0 := by rwa [ne_eq, Associates.mk_eq_zero]
  have key : ∀ k : ℕ, k ≤ (Associates.mk v'.asIdeal).count (Associates.mk (J.map (conjO σ))).factors ↔
      k ≤ (Associates.mk v.asIdeal).count (Associates.mk J).factors := by
    intro k
    rw [← Associates.prime_pow_dvd_iff_le hm' v'.associates_irreducible,
      ← Associates.prime_pow_dvd_iff_le hm v.associates_irreducible,
      ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd,
      Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
    have : (v'.asIdeal ^ k).comap (conjO σ) = v.asIdeal ^ k := by
      ext x
      rw [Ideal.mem_comap, ← HeightOneSpectrum.intValuation_le_pow_iff_mem,
        ← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E),
        ← HeightOneSpectrum.valuation_of_algebraMap (K := E), ← h, ← hc]
      rfl
    rw [this]
  exact le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)

/- English proof (translation)
Take `⟨a, J, ha, hJ⟩` from `FractionalIdeal.exists_eq_spanSingleton_mul 𝔠`. Establish `ha' : Ideal.span {a} ≠ 0` using `by rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Establish `hA` using `(FractionalIdeal.coeIdeal_ne_zero (K := E)).2 ha'`. Establish `e : ((Ideal.span {a} : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) * 𝔠 = J`. Rewrite using `[hJ, FractionalIdeal.coeIdeal_span_singleton, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ (by simpa using ha), FractionalIdeal.spanSingleton_one, one_mul]`.

Establish `hJ0 : J ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.1 (e ▸ mul_ne_zero hA h0)`. Establish `h1` using `count_map hc h hJ0`. Rewrite `h1` using `[← e, conjI, FractionalIdeal.extended_mul, FractionalIdeal.count_mul E _ hA h0]`. Use `erw [FractionalIdeal.count_mul E _ (conjI_ne_zero σ hA) (conjI_ne_zero σ h0), count_map hc h ha'] at h1`. Conclude with `add_left_cancel h1`.
-/
theorem count_conjI {σ : E →ₐ[F] E} {c : E ≃+* E} (hc : ∀ x, σ x = c x) {v v' : HeightOneSpectrum (𝓞 E)}
    (h : ConjPl c v v') {𝔠 : FractionalIdeal (𝓞 E)⁰ E} (h0 : 𝔠 ≠ 0) :
    FractionalIdeal.count E v' (conjI σ 𝔠) = FractionalIdeal.count E v 𝔠 := by
  obtain ⟨a, J, ha, hJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul 𝔠
  have ha' : Ideal.span {a} ≠ 0 := by rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hA := (FractionalIdeal.coeIdeal_ne_zero (K := E)).2 ha'
  have e : ((Ideal.span {a} : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) * 𝔠 = J := by
    rw [hJ, FractionalIdeal.coeIdeal_span_singleton, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton,
      mul_inv_cancel₀ (by simpa using ha), FractionalIdeal.spanSingleton_one, one_mul]
  have hJ0 : J ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.1 (e ▸ mul_ne_zero hA h0)
  have h1 := count_map hc h hJ0
  rw [← e, conjI, FractionalIdeal.extended_mul, FractionalIdeal.count_mul E _ hA h0] at h1
  erw [FractionalIdeal.count_mul E _ (conjI_ne_zero σ hA) (conjI_ne_zero σ h0), count_map hc h ha'] at h1
  exact add_left_cancel h1

/- English proof (translation)
Rewrite using `[coe_locIdele, coe_locIdele, RingHom.map_add, RingHom.map_sub, RingHom.map_one, SplitVal.sigR_extZero, SplitVal.sigR_extZero, RingHom.map_one]`. Use `congr 2`. Rewrite using `[RingEquiv.eq_symm_apply, GlobalTheory.DefU.ClassFin.finAdEquiv_sigR σ c hc, RingEquiv.apply_symm_apply]`. Use `FiniteAdeleRing.ext _ fun u => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `conjLoc c u (Neutral.B1.finiteSingle E (conjSrc c w) x (conjSrc c u)) = _`.

Distinguish the cases in `e : u = w`. Substitute `e` using the available equality. Rewrite using `[finSingle_self, finSingle_self]`. Both sides reduce to the same expression. Rewrite using `[finSingle_ne e, finSingle_ne ((conjSrc_injective c).ne e), map_one]`.
-/
theorem sigR_locIdele {σ : E →ₐ[F] E} {c : E ≃+* E} (hc : ∀ x, σ x = c x) (w : HeightOneSpectrum (𝓞 E))
    (x : ((conjSrc c w).adicCompletion E)ˣ) :
    sigR (AF F) σ (locIdele F (conjSrc c w) x : AF F ⊗[F] E) =
      locIdele F w (Units.map (conjLoc c w).toMonoidHom x) := by
  classical
  rw [coe_locIdele, coe_locIdele, RingHom.map_add, RingHom.map_sub, RingHom.map_one, SplitVal.sigR_extZero,
    SplitVal.sigR_extZero, RingHom.map_one]
  congr 2
  rw [RingEquiv.eq_symm_apply, GlobalTheory.DefU.ClassFin.finAdEquiv_sigR σ c hc, RingEquiv.apply_symm_apply]
  refine FiniteAdeleRing.ext _ fun u => ?_
  change conjLoc c u (Neutral.B1.finiteSingle E (conjSrc c w) x (conjSrc c u)) = _
  by_cases e : u = w
  · subst e
    rw [finSingle_self, finSingle_self]
    rfl
  · rw [finSingle_ne e, finSingle_ne ((conjSrc_injective c).ne e), map_one]

/- English proof (translation)
Establish `e : Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (locIdele F (conjSrc c w) x)) = locIdele F (conjSrc c w) x * locIdele F w (Units.map (conjLoc c w).toMonoidHom x)` using `Units.ext (by`. Rewrite using `[Units.val_mul, ← sigR_locIdele hc]`. Conclude with `GlobalTheory.Doubling.algebraMap_norm_eq hE _)`. Establish `k` using `hν (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (locIdele F (conjSrc c w) x))`. Rewrite `k` using `[e, map_mul]`.

Use `eq_inv_of_mul_eq_one_right ?_` and prove the remaining obligations. Conclude with `(map_mul Circle.toUnits _ _).symm.trans ((congrArg Circle.toUnits k).trans (map_one _))`.
-/
theorem locChar_conjLoc {σ : E →ₐ[F] E} (hE : IsCMExt F E σ) {c : E ≃+* E} (hc : ∀ x, σ x = c x) {ν : Chr F E}
    (hν : ∀ x : (AF F)ˣ, ν (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) x) = 1)
    (w : HeightOneSpectrum (𝓞 E)) (x : ((conjSrc c w).adicCompletion E)ˣ) :
    locChar ν w (Units.map (conjLoc c w).toMonoidHom x) = (locChar ν (conjSrc c w) x)⁻¹ := by
  have e : Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E)
      (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (locIdele F (conjSrc c w) x)) =
      locIdele F (conjSrc c w) x * locIdele F w (Units.map (conjLoc c w).toMonoidHom x) :=
    Units.ext (by
      rw [Units.val_mul, ← sigR_locIdele hc]
      exact GlobalTheory.Doubling.algebraMap_norm_eq hE _)
  have k := hν (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (locIdele F (conjSrc c w) x))
  rw [e, map_mul] at k
  refine eq_inv_of_mul_eq_one_right ?_
  exact (map_mul Circle.toUnits _ _).symm.trans ((congrArg Circle.toUnits k).trans (map_one _))

/- English proof (translation)
Establish `h1` using `Formalism.L2.Host.unif_spec (conjSrc c w)`. Establish `h3 : val ν (conjSrc c w) = locChar ν (conjSrc c w) (Formalism.L2.Host.atFin _ (Formalism.L2.Host.unif (conjSrc c w)))` using `rfl`. Rewrite using `[h3]`. Generalize the expression as in `Formalism.L2.Host.atFin _ (Formalism.L2.Host.unif (conjSrc c w)) = x at h1`. Establish `h4 : Formalism.L2.Host.IsUnifAt w (Units.map (conjLoc c w).toMonoidHom x)` using `((conjLoc_spec c w).2.2 x).trans h1`.

Rewrite using `[← hw.locChar_eq_val h4, locChar_conjLoc hE hc hν]`.
-/
theorem val_eq_inv {σ : E →ₐ[F] E} (hE : IsCMExt F E σ) {c : E ≃+* E} (hc : ∀ x, σ x = c x) {ν : Chr F E}
    (hν : ∀ x : (AF F)ˣ, ν (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) x) = 1)
    {w : HeightOneSpectrum (𝓞 E)} (hw : UnrAt ν w) : val ν w = (val ν (conjSrc c w))⁻¹ := by
  have h1 := Formalism.L2.Host.unif_spec (conjSrc c w)
  have h3 : val ν (conjSrc c w) = locChar ν (conjSrc c w) (Formalism.L2.Host.atFin _ (Formalism.L2.Host.unif (conjSrc c w))) := rfl
  rw [h3]
  generalize Formalism.L2.Host.atFin _ (Formalism.L2.Host.unif (conjSrc c w)) = x at h1
  have h4 : Formalism.L2.Host.IsUnifAt w (Units.map (conjLoc c w).toMonoidHom x) :=
    ((conjLoc_spec c w).2.2 x).trans h1
  rw [← hw.locChar_eq_val h4, locChar_conjLoc hE hc hν]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hE ν hν 𝔠 h0 hu`. Establish `hσ : ∀ x, σ (σ x) = x` using `fun x => by`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hE.2.2.2, hE.2.2.2, star_star]`.

Set `c : E ≃+* E` to `RingEquiv.ofBijective (σ : E →+* E) (Function.Involutive.bijective hσ)`. Establish `hc : ∀ x, σ x = c x` using `fun _ => rfl`. Establish `hinv : Function.Involutive (conjSrc c)` using `fun w => by`. Use `(GlobalTheory.CuspRep.eq_conjSrc fun x => ?_).symm` and prove the remaining obligations. Rewrite using `[← conjPl_conjSrc c w, ← hc, ← hc, hσ]`.

Unfold `idealVal`. Rewrite using `[← finprod_inv_distrib, ← finprod_comp_equiv (hinv.toPerm _)]`. Use `finprod_congr fun w => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `val ν (conjSrc c w) ^ FractionalIdeal.count E (conjSrc c w) (conjI σ 𝔠) = _`. Establish `h1` using `conjPl_conjSrc c (conjSrc c w)`.

Rewrite `h1` using `[hinv w]`. Rewrite using `[count_conjI hc h1 h0]`. Distinguish the cases in `hw : FractionalIdeal.count E w 𝔠 = 0`. Simplify using `[hw]`. Rewrite using `[val_eq_inv hE hc hν (hu w hw), inv_zpow, inv_inv]`.
-/
theorem idealVal_conjI : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ ν : Chr F E, (∀ x : (AF F)ˣ, ν (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) x) = 1) → ∀ 𝔠 : FractionalIdeal (𝓞 E)⁰ E, 𝔠 ≠ 0 → (∀ w : HeightOneSpectrum (𝓞 E), FractionalIdeal.count E w 𝔠 ≠ 0 → UnrAt ν w) → idealVal ν (conjI σ 𝔠) = (idealVal ν 𝔠)⁻¹ := by
  intro F E _ _ _ _ _ σ hE ν hν 𝔠 h0 hu
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hE.2.2.2, hE.2.2.2, star_star]
  let c : E ≃+* E := RingEquiv.ofBijective (σ : E →+* E) (Function.Involutive.bijective hσ)
  have hc : ∀ x, σ x = c x := fun _ => rfl
  have hinv : Function.Involutive (conjSrc c) := fun w => by
    refine (GlobalTheory.CuspRep.eq_conjSrc fun x => ?_).symm
    rw [← conjPl_conjSrc c w, ← hc, ← hc, hσ]
  unfold idealVal
  rw [← finprod_inv_distrib, ← finprod_comp_equiv (hinv.toPerm _)]
  refine finprod_congr fun w => ?_
  change val ν (conjSrc c w) ^ FractionalIdeal.count E (conjSrc c w) (conjI σ 𝔠) = _
  have h1 := conjPl_conjSrc c (conjSrc c w)
  rw [hinv w] at h1
  rw [count_conjI hc h1 h0]
  by_cases hw : FractionalIdeal.count E w 𝔠 = 0
  · simp [hw]
  rw [val_eq_inv hE hc hν (hu w hw), inv_zpow, inv_inv]

end GlobalTheory.UnrEuler.ConjVal
