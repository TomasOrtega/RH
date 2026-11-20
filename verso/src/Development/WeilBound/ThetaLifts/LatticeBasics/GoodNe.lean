import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterAtUniformizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterOfIdeleClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeValueNotFiniteOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPrimeDegreeOne

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
  {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

/- English proof (translation)
Assemble the required witnesses or components as `⟨(h.chars.heckeα.1.div' h.chars.heckeβ.1 :), fun x => by rw [Chars.ν, MonoidHom.div_apply, h.chars.heckeα.2 x, h.chars.heckeβ.2 x, div_one]⟩`.
-/
theorem isHecke_nu (h : IsTriple B G X om om') : IsHecke F E X.ν :=
  ⟨(h.chars.heckeα.1.div' h.chars.heckeβ.1 :), fun x => by
    rw [Chars.ν, MonoidHom.div_apply, h.chars.heckeα.2 x, h.chars.heckeβ.2 x, div_one]⟩

/- English proof (translation)
Introduce `z hz`. Use `show (((X.α z / X.β z : Circle)) : ℂ) = _`. Rewrite using `[Circle.coe_div, h.chars.expα z hz, h.chars.expβ z hz, ← Finset.prod_div_distrib]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `hne : piInf (B.emb w) z ≠ 0` using `(z.isUnit.map (piInf (B.emb w))).ne_zero`.

Rewrite using `[zpow_sub₀ (div_ne_zero hne (by exact_mod_cast (norm_ne_zero_iff.2 hne)))]`.
-/
theorem hasExp_nu (h : IsTriple B G X om om') : HasExp B.emb X.ν (fun w => B.mα w - B.mβ w) := by
  intro z hz
  show (((X.α z / X.β z : Circle)) : ℂ) = _
  rw [Circle.coe_div, h.chars.expα z hz, h.chars.expβ z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hne : piInf (B.emb w) z ≠ 0 := (z.isUnit.map (piInf (B.emb w))).ne_zero
  rw [zpow_sub₀ (div_ne_zero hne (by exact_mod_cast (norm_ne_zero_iff.2 hne)))]

/- English proof (translation)
Use `(GlobalTheory.KFinLoc.split_or_inert F E σ B hB v).resolve_right ?_` and prove the remaining obligations. Introduce and unpack `⟨w, hw⟩`. Establish `hw' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal` using `hw`. Establish `hu : w.under (𝓞 F) = v` using `(HeightOneSpectrum.ext (v.isMaximal.eq_of_le (w.under (𝓞 F)).isPrime.ne_top (Ideal.map_le_iff_le_comap.1 hw'.le))).symm`. Take `⟨p, hp, hN, -⟩` from `GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully F E w (hu ▸ hv)`.

Rewrite `hN` using `[← hw', Ideal.absNorm_algebraMap, ← Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E, hB.cm.2.2.1]`. Conclude with `Nat.Prime.not_prime_pow le_rfl (hN ▸ hp)`.
-/
theorem nonempty_emb_of_splitsFully (hB : B.IsGood σ) {v : Pl F} (hv : SplitsFully E v) : Nonempty (E →ₐ[F] Fv F v) := by
  refine (GlobalTheory.KFinLoc.split_or_inert F E σ B hB v).resolve_right ?_
  rintro ⟨w, hw⟩
  have hw' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal := hw
  have hu : w.under (𝓞 F) = v := (HeightOneSpectrum.ext (v.isMaximal.eq_of_le (w.under (𝓞 F)).isPrime.ne_top
    (Ideal.map_le_iff_le_comap.1 hw'.le))).symm
  obtain ⟨p, hp, hN, -⟩ := GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully F E w (hu ▸ hv)
  rw [← hw', Ideal.absNorm_algebraMap, ← Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E, hB.cm.2.2.1] at hN
  exact Nat.Prime.not_prime_pow le_rfl (hN ▸ hp)

/- English proof (translation)
Introduce `hpow`. Establish `hW : splitPrime t ∉ above E (X.T : Set (Pl F))` using `fun hmem => hv.1 (by simpa [above, splitPrime_under] using hmem)`. Establish `hunr : UnrAt X.ν (splitPrime t)`. Rewrite using `[Chars.ν, div_eq_mul_inv]`. Conclude with `(h.chars.unrα _ hW).mul (h.chars.unrβ _ hW).inv`.

Rewrite `hpow` using `[GlobalTheory.ChrWUnif.chrW_unifAt F E X.ν v t hunr]`. Take `⟨H, hloc, hinf⟩` from `GlobalTheory.HeckeBridge.exists_hchar F E σ h.base.cm X.ν (isHecke_nu h)`. Establish `hval : val X.ν (splitPrime t) = H.val (splitPrime t)` using `(hloc _ _).symm`. Take `⟨p, hp, hN, hsq⟩` from `GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully F E (splitPrime t) (by rw [splitPrime_under]; exact hv.2)`. Use `GlobalTheory.CMSplitValue.not_isOfFinOrder_val F E σ h.base.cm h.base.galois B.emb H _ (hinf _ _ (hasExp_nu h)) (fun w => ?_) p hp _ hN hsq ?_` and prove the remaining obligations.

Use `h.geo.kappa w` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[← hval]`. Conclude with `isOfFinOrder_iff_zpow_eq_one.2 ⟨k, hk, hpow⟩`.
-/
theorem nu_pow_ne_one (h : IsTriple B G X om om') {v : Pl F} (hv : X.Good v) (t : E →ₐ[F] Fv F v) {k : ℤ} (hk : k ≠ 0) :
    chrW X.ν t (unifAt v) ^ k ≠ 1 := by
  intro hpow
  have hW : splitPrime t ∉ above E (X.T : Set (Pl F)) := fun hmem => hv.1 (by simpa [above, splitPrime_under] using hmem)
  have hunr : UnrAt X.ν (splitPrime t) := by
    rw [Chars.ν, div_eq_mul_inv]
    exact (h.chars.unrα _ hW).mul (h.chars.unrβ _ hW).inv
  rw [GlobalTheory.ChrWUnif.chrW_unifAt F E X.ν v t hunr] at hpow
  obtain ⟨H, hloc, hinf⟩ := GlobalTheory.HeckeBridge.exists_hchar F E σ h.base.cm X.ν (isHecke_nu h)
  have hval : val X.ν (splitPrime t) = H.val (splitPrime t) := (hloc _ _).symm
  obtain ⟨p, hp, hN, hsq⟩ := GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully F E (splitPrime t)
    (by rw [splitPrime_under]; exact hv.2)
  refine GlobalTheory.CMSplitValue.not_isOfFinOrder_val F E σ h.base.cm h.base.galois B.emb H _ (hinf _ _ (hasExp_nu h))
    (fun w => ?_) p hp _ hN hsq ?_
  · have := h.geo.kappa w
    omega
  · rw [← hval]
    exact isOfFinOrder_iff_zpow_eq_one.2 ⟨k, hk, hpow⟩

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ hv` and use `⟨nonempty_emb_of_splitsFully h.base hv.2, fun t e => nu_pow_ne_one h hv t one_ne_zero (by rw [e, zpow_one])⟩`.
-/
theorem goodNe : GoodNe := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ hv =>
  ⟨nonempty_emb_of_splitsFully h.base hv.2, fun t e => nu_pow_ne_one h hv t one_ne_zero (by rw [e, zpow_one])⟩

end GlobalTheory.ThK.Dbl

end
