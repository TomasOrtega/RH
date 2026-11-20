import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsBasicOpenCover
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Monomial
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WMultB

namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory MvPolynomial

noncomputable section

variable {W : Scheme.{0}}

open Classical in

def ordAlong (G : W.IdealSheafData) (C : Set W) : ℕ :=
  if h : IsIrreducible C then
    (Module.length (W.presheaf.stalk h.genericPoint)
      (W.presheaf.stalk h.genericPoint ⧸ FinalTheorems.stalkId G h.genericPoint)).toNat
  else 0

/- English proof (translation)
Establish `hU : IsAffineOpen U.1` using `U.2`. Set `yU : U.1` to `⟨y, hy⟩`. Set `algY : Algebra Γ(W, U.1) (W.presheaf.stalk y)` to `TopCat.Presheaf.algebra_section_stalk W.presheaf yU`. Establish `hlocY : IsLocalization.AtPrime (W.presheaf.stalk y) (hU.primeIdealOf yU).asIdeal` using `hU.isLocalization_stalk yU`. Use `set Py := hU.primeIdealOf yU with hPy`.

Use `set f' : Fin n → W.presheaf.stalk y := fun i => W.presheaf.germ U.1 y hy (f i) with hf'`. Take `⟨U', g, hyU', hg, hGU'⟩` from `hG y`. Use `set γ : W.presheaf.stalk y := W.presheaf.germ U'.1 y hyU' g with hγ`. Establish `hGy : FinalTheorems.stalkId G y = Ideal.span {γ}`. Rewrite using `[WMult.stalkId_eq_map_germ G y U' hyU', hGU', Ideal.map_span, Set.image_singleton]`.

Establish `hγ0 : γ ≠ 0`. Introduce `h0`. Establish `hU' : IsAffineOpen U'.1` using `U'.2`. Set `: Algebra Γ(W, U'.1) (W.presheaf.stalk y)` to `TopCat.Presheaf.algebra_section_stalk W.presheaf (⟨y, hyU'⟩ : U'.1)`. Use `hU'.isLocalization_stalk ⟨y, hyU'⟩` as an intermediate fact.

Take `⟨⟨c, hc⟩, hcg⟩` from `(IsLocalization.map_eq_zero_iff (M := (hU'.primeIdealOf ⟨y, hyU'⟩).asIdeal.primeCompl) (S := W.presheaf.stalk y) g).mp h0`. Establish `hc0 : c = 0` using `(mul_right_mem_nonZeroDivisors_eq_zero_iff hg).mp hcg`. Conclude with `hc (by rw [hc0]; exact Ideal.zero_mem _)`. Establish `hrad : (∏ i ∈ J, f' i) ∈ (Ideal.span {γ}).radical`. Rewrite using `[Ideal.radical_eq_sInf, Ideal.mem_sInf]`.

Introduce and unpack `Q ⟨hQγ, hQ⟩`. Use `hQ` as an intermediate fact. Set `P : PrimeSpectrum Γ(W, U.1)` to `⟨Q.comap (W.presheaf.germ U.1 y hy).hom, inferInstance⟩`. Establish `h1 : hU.fromSpec P ∈ (G.support : Set W)`. Rewrite using `[WMult.mem_support_fromSpec_iff G U hU]`.

Use `show G.ideal U ≤ Q.comap (W.presheaf.germ U.1 y hy).hom`. Rewrite using `[← Ideal.map_le_iff_le_comap, ← WMult.stalkId_eq_map_germ G y U hy, hGy]`. Conclude with `hQγ`. Establish `h2` using `hGZ h1`. Rewrite `h2` using `[WMult.mem_support_fromSpec_iff Z U hU]`.

Establish `h3 : FinalTheorems.stalkId Z y ≤ Q`. Rewrite using `[WMult.stalkId_eq_map_germ Z y U hy]`. Conclude with `Ideal.map_le_iff_le_comap.mpr h2`. Rewrite `h3` using `[hZy]`. Conclude with `h3 (Ideal.mem_span_singleton_self _)`.

Take `⟨u, m, hmJ, hγu⟩` from `eq_unit_mul_monomial f' hrsp.1 hrsp.2 J hγ0 hrad`. Establish `hord : ∀ i ∈ J, ordAlong G (σ i) = m i`. Introduce `i hi`. Take `⟨hCc, hyC, hirr, hηU, hηf⟩` from `hσ i hi`. Establish `hCm : Maximal (fun C => IsIrreducible C ∧ C ⊆ (Z.support : Set W)) (σ i)` using `hCc`.

Establish `hCcl : IsClosed (σ i)`. Establish `h` using `hCm.eq_of_subset ⟨hirr.closure, closure_minimal hCm.1.2 Z.support.isClosed⟩ subset_closure`. Rewrite using `[h]`. Conclude with `isClosed_closure`. Establish `hgen : IsGenericPoint hirr.genericPoint (σ i)`.

Use `hirr.isGenericPoint_genericPoint_closure` as an intermediate fact. Rewrite `this` using `[hCcl.closure_eq]`. Then use the resulting hypothesis. Use `set η := hirr.genericPoint with hη`. Establish `hηy : η ⤳ y` using `hgen.specializes hyC`. Set `Pη` to `hU.primeIdealOf ⟨η, hηU⟩`.

Establish `hfromη : hU.fromSpec Pη = η` using `hU.fromSpec_primeIdealOf ⟨η, hηU⟩`. Establish `hfromy : hU.fromSpec Py = y` using `hU.fromSpec_primeIdealOf yU`. Establish `emb` using `hU.fromSpec.isOpenEmbedding`. Establish `hspec : ∀ P Q : PrimeSpectrum Γ(W, U.1), hU.fromSpec P ⤳ hU.fromSpec Q ↔ P ≤ Q`. Introduce `P Q`.

Rewrite using `[PrimeSpectrum.le_iff_specializes]`. Conclude with `emb.isInducing.specializes_iff`. Establish `hle : Pη ≤ Py` using `(hspec _ _).mp (by rw [hfromη, hfromy]; exact hηy)`. Establish `hfη : f i ∈ Pη.asIdeal`. Establish `h' : η ∈ W.zeroLocus {f i} ∩ U.1` using `⟨hηf, hηU⟩`.

Rewrite `h'` using `[← hU.fromSpec_image_zeroLocus]`. Take `⟨Q, hQ, hQη⟩` from `h'`. Rewrite `hQη` using `[← hfromη]`. Use `emb.injective hQη` as an intermediate fact. Substitute `this` using the available equality.

Conclude with `(PrimeSpectrum.mem_zeroLocus _ _).mp hQ (Set.mem_singleton _)`. Establish `hpi : Prime (f' i)` using `prime_of_regular_params f' hrsp.1 hrsp.2 i`. Establish `hQi : (Ideal.span {f' i}).IsPrime` using `(Ideal.span_singleton_prime hpi.ne_zero).mpr hpi`. Set `Pi : PrimeSpectrum Γ(W, U.1)` to `⟨(Ideal.span {f' i}).comap (algebraMap Γ(W, U.1) (W.presheaf.stalk y)), inferInstance⟩`. Establish `hdisj : Disjoint (Py.asIdeal.primeCompl : Set Γ(W, U.1)) Pη.asIdeal` using `Set.disjoint_left.mpr fun x hx hx' => hx ((show Pη.asIdeal ≤ Py.asIdeal from hle) hx')`.

Establish `hPiη : Pi ≤ Pη` using `by show (Ideal.span {f' i}).comap (algebraMap Γ(W, U.1) (W.presheaf.stalk y)) ≤ Pη.asIdeal`. Combine the equalities or inequalities in the displayed calculation. Apply `Ideal.comap_mono` to reduce the goal to its premises. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `Ideal.mem_map_of_mem _ hfη`.

Use `_ = Pη.asIdeal := IsLocalization.under_map_of_isPrime_disjoint Py.asIdeal.primeCompl (W.presheaf.stalk y) Pη.isPrime hdisj`. Establish `hζZ : hU.fromSpec Pi ∈ (Z.support : Set W)`. Rewrite using `[WMult.mem_support_fromSpec_iff Z U hU]`. Use `show Z.ideal U ≤ (Ideal.span {f' i}).comap (W.presheaf.germ U.1 y hy).hom`. Rewrite using `[← Ideal.map_le_iff_le_comap, ← WMult.stalkId_eq_map_germ Z y U hy, hZy, Ideal.span_le, Set.singleton_subset_iff]`.

Conclude with `Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem _ hi)`. Establish `hζη : hU.fromSpec Pi ⤳ η` using `by rw [← hfromη]; exact (hspec _ _).mpr hPiη`. Establish `hcl : closure {η} = σ i` using `hgen`. Establish `hsub : σ i ⊆ closure {hU.fromSpec Pi}`. Introduce `z hz`.

Rewrite `hz` using `[← hcl]`. Conclude with `specializes_iff_closure_subset.mp hζη hz`. Establish `hirrζ : IsIrreducible (closure {hU.fromSpec Pi})` using `isIrreducible_singleton.closure`. Establish `hsubZ : closure {hU.fromSpec Pi} ⊆ (Z.support : Set W)` using `closure_minimal (Set.singleton_subset_iff.mpr hζZ) Z.support.isClosed`. Establish `hCeq : σ i = closure {hU.fromSpec Pi}` using `hCm.eq_of_subset ⟨hirrζ, hsubZ⟩ hsub`.

Establish `hηζ : η ⤳ hU.fromSpec Pi`. Rewrite using `[specializes_iff_mem_closure, hcl, hCeq]`. Conclude with `subset_closure (Set.mem_singleton _)`. Establish `hηPi : Pη ≤ Pi` using `(hspec _ _).mp (by rw [hfromη]; exact hηζ)`. Establish `hPeq : Pη.asIdeal = (Ideal.span {f' i}).comap (algebraMap Γ(W, U.1) (W.presheaf.stalk y))` using `congrArg PrimeSpectrum.asIdeal (le_antisymm hηPi hPiη)`.

Set `T` to `Localization.AtPrime (Ideal.span {f' i})`. Establish `hT : IsLocalization.AtPrime T ((Ideal.span {f' i}).comap (algebraMap Γ(W, U.1) (W.presheaf.stalk y)))` using `IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (M := Py.asIdeal.primeCompl) (S := W.presheaf.stalk y) (T := T) (Ideal.span {f' i})`. Establish `hT' : IsLocalization Pη.asIdeal.primeCompl T`. Establish `hsm : Pη.asIdeal.primeCompl = (Ideal.comap (algebraMap Γ(W, U.1) (W.presheaf.stalk y)) (Ideal.span {f' i})).primeCompl`. Use extensionality with `x`.

Rewrite using `[Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hPeq]`. Rewrite using `[hsm]`. Conclude with `hT`. Set `ηU : U.1` to `⟨η, hηU⟩`. Set `algη : Algebra Γ(W, U.1) (W.presheaf.stalk η)` to `TopCat.Presheaf.algebra_section_stalk W.presheaf ηU`.

Establish `hlocη : IsLocalization.AtPrime (W.presheaf.stalk η) Pη.asIdeal` using `hU.isLocalization_stalk ηU`. Set `φ : W.presheaf.stalk η ≃ₐ[Γ(W, U.1)] T` to `IsLocalization.algEquiv Pη.asIdeal.primeCompl _ _`. Set `algYη : Algebra (W.presheaf.stalk y) (W.presheaf.stalk η)` to `(φ.symm.toRingEquiv.toRingHom.comp (algebraMap (W.presheaf.stalk y) T)).toAlgebra`. Establish `hlocYη : IsLocalization.AtPrime (W.presheaf.stalk η) (Ideal.span {f' i})` using `(IsLocalization.isLocalization_iff_of_ringEquiv (M := (Ideal.span {f' i}).primeCompl) (S := T) φ.symm.toRingEquiv).mp inferInstance`. Establish `hgerm : ∀ a : Γ(W, U.1), W.presheaf.germ U.1 η hηU a = algebraMap (W.presheaf.stalk y) (W.presheaf.stalk η) (W.presheaf.germ U.1 y hy a)`.

Use `by`. Introduce `a`. Establish `h1` using `(φ.symm.commutes a).symm`. Rewrite `h1` using `[IsScalarTower.algebraMap_apply Γ(W, U.1) (W.presheaf.stalk y) T]`. Conclude with `h1`.

Establish `hGη : FinalTheorems.stalkId G η = Ideal.span {algebraMap (W.presheaf.stalk y) (W.presheaf.stalk η) γ}`. Rewrite using `[WMult.stalkId_eq_map_germ G η U hηU]`. Establish `hcomp : (W.presheaf.germ U.1 η hηU).hom = (algebraMap (W.presheaf.stalk y) (W.presheaf.stalk η)).comp (W.presheaf.germ U.1 y hy).hom` using `RingHom.ext fun a => hgerm a`. Rewrite using `[hcomp, ← Ideal.map_map, ← WMult.stalkId_eq_map_germ G y U hy, hGy, Ideal.map_span, Set.image_singleton]`. Establish `hordS` using `WMult.ord_isLocalization_eq_exponent f' hrsp.1 hrsp.2 J u m i hi (W.presheaf.stalk η)`.

Establish `hlen : Module.length (W.presheaf.stalk η) (W.presheaf.stalk η ⧸ FinalTheorems.stalkId G η) = (m i : ℕ∞)`. Rewrite using `[hGη, hγu]`. Conclude with `hordS`. Unfold `ordAlong`. Rewrite using `[dif_pos hirr, ← hη, hlen]`.

Conclude with `ENat.toNat_natCast (m i)`. Rewrite using `[hGy, hγu]`. Establish `hprod : ∏ i ∈ J, f' i ^ m i = ∏ i ∈ J, f' i ^ ordAlong G (σ i)` using `Finset.prod_congr rfl fun i hi => by rw [hord i hi]`. Rewrite using `[hprod]`. Conclude with `Ideal.span_singleton_mul_left_unit u.isUnit _`.
-/
theorem stalkId_eq_monomial [IsNoetherian W] {Z G : W.IdealSheafData} (hG : FinalTheorems.EffCartier G)
    (hGZ : (G.support : Set W) ⊆ Z.support) (y : W) (U : W.affineOpens) (hy : y ∈ U.1) {n : ℕ}
    (f : Fin n → Γ(W, U.1)) (J : Finset (Fin n)) [IsRegularLocalRing (W.presheaf.stalk y)]
    (hrsp : FinalTheorems.Rsp (W.presheaf.stalk y) n (fun i => W.presheaf.germ U.1 y hy (f i)))
    (hZy : FinalTheorems.stalkId Z y = Ideal.span {∏ i ∈ J, W.presheaf.germ U.1 y hy (f i)})
    (σ : Fin n → Set W) (hσ : ∀ i ∈ J, IsBranch (Z.support : Set W) (f i) y (σ i)) :
    FinalTheorems.stalkId G y =
      Ideal.span {∏ i ∈ J, W.presheaf.germ U.1 y hy (f i) ^ ordAlong G (σ i)} := by
  classical
  have hU : IsAffineOpen U.1 := U.2
  let yU : U.1 := ⟨y, hy⟩
  let algY : Algebra Γ(W, U.1) (W.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk W.presheaf yU
  have hlocY : IsLocalization.AtPrime (W.presheaf.stalk y) (hU.primeIdealOf yU).asIdeal :=
    hU.isLocalization_stalk yU
  set Py := hU.primeIdealOf yU with hPy
  set f' : Fin n → W.presheaf.stalk y := fun i => W.presheaf.germ U.1 y hy (f i) with hf'

  obtain ⟨U', g, hyU', hg, hGU'⟩ := hG y
  set γ : W.presheaf.stalk y := W.presheaf.germ U'.1 y hyU' g with hγ
  have hGy : FinalTheorems.stalkId G y = Ideal.span {γ} := by
    rw [WMult.stalkId_eq_map_germ G y U' hyU', hGU', Ideal.map_span, Set.image_singleton]
  have hγ0 : γ ≠ 0 := by
    intro h0
    have hU' : IsAffineOpen U'.1 := U'.2
    let : Algebra Γ(W, U'.1) (W.presheaf.stalk y) :=
      TopCat.Presheaf.algebra_section_stalk W.presheaf (⟨y, hyU'⟩ : U'.1)
    have := hU'.isLocalization_stalk ⟨y, hyU'⟩
    obtain ⟨⟨c, hc⟩, hcg⟩ := (IsLocalization.map_eq_zero_iff
      (M := (hU'.primeIdealOf ⟨y, hyU'⟩).asIdeal.primeCompl) (S := W.presheaf.stalk y) g).mp h0
    have hc0 : c = 0 := (mul_right_mem_nonZeroDivisors_eq_zero_iff hg).mp hcg
    exact hc (by rw [hc0]; exact Ideal.zero_mem _)

  have hrad : (∏ i ∈ J, f' i) ∈ (Ideal.span {γ}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro Q ⟨hQγ, hQ⟩
    have := hQ
    let P : PrimeSpectrum Γ(W, U.1) := ⟨Q.comap (W.presheaf.germ U.1 y hy).hom, inferInstance⟩
    have h1 : hU.fromSpec P ∈ (G.support : Set W) := by
      rw [WMult.mem_support_fromSpec_iff G U hU]
      show G.ideal U ≤ Q.comap (W.presheaf.germ U.1 y hy).hom
      rw [← Ideal.map_le_iff_le_comap, ← WMult.stalkId_eq_map_germ G y U hy, hGy]
      exact hQγ
    have h2 := hGZ h1
    rw [WMult.mem_support_fromSpec_iff Z U hU] at h2
    have h3 : FinalTheorems.stalkId Z y ≤ Q := by
      rw [WMult.stalkId_eq_map_germ Z y U hy]; exact Ideal.map_le_iff_le_comap.mpr h2
    rw [hZy] at h3
    exact h3 (Ideal.mem_span_singleton_self _)
  obtain ⟨u, m, hmJ, hγu⟩ := eq_unit_mul_monomial f' hrsp.1 hrsp.2 J hγ0 hrad

  have hord : ∀ i ∈ J, ordAlong G (σ i) = m i := by
    intro i hi
    obtain ⟨hCc, hyC, hirr, hηU, hηf⟩ := hσ i hi
    have hCm : Maximal (fun C => IsIrreducible C ∧ C ⊆ (Z.support : Set W)) (σ i) := hCc
    have hCcl : IsClosed (σ i) := by
      have h := hCm.eq_of_subset ⟨hirr.closure, closure_minimal hCm.1.2 Z.support.isClosed⟩
        subset_closure
      rw [h]; exact isClosed_closure
    have hgen : IsGenericPoint hirr.genericPoint (σ i) := by
      have := hirr.isGenericPoint_genericPoint_closure
      rwa [hCcl.closure_eq] at this
    set η := hirr.genericPoint with hη
    have hηy : η ⤳ y := hgen.specializes hyC
    let Pη := hU.primeIdealOf ⟨η, hηU⟩
    have hfromη : hU.fromSpec Pη = η := hU.fromSpec_primeIdealOf ⟨η, hηU⟩
    have hfromy : hU.fromSpec Py = y := hU.fromSpec_primeIdealOf yU
    have emb := hU.fromSpec.isOpenEmbedding
    have hspec : ∀ P Q : PrimeSpectrum Γ(W, U.1), hU.fromSpec P ⤳ hU.fromSpec Q ↔ P ≤ Q := by
      intro P Q
      rw [PrimeSpectrum.le_iff_specializes]
      exact emb.isInducing.specializes_iff
    have hle : Pη ≤ Py := (hspec _ _).mp (by rw [hfromη, hfromy]; exact hηy)
    have hfη : f i ∈ Pη.asIdeal := by
      have h' : η ∈ W.zeroLocus {f i} ∩ U.1 := ⟨hηf, hηU⟩
      rw [← hU.fromSpec_image_zeroLocus] at h'
      obtain ⟨Q, hQ, hQη⟩ := h'
      rw [← hfromη] at hQη
      have := emb.injective hQη
      subst this
      exact (PrimeSpectrum.mem_zeroLocus _ _).mp hQ (Set.mem_singleton _)
    have hpi : Prime (f' i) := prime_of_regular_params f' hrsp.1 hrsp.2 i
    have hQi : (Ideal.span {f' i}).IsPrime := (Ideal.span_singleton_prime hpi.ne_zero).mpr hpi
    let Pi : PrimeSpectrum Γ(W, U.1) :=
      ⟨(Ideal.span {f' i}).comap (algebraMap Γ(W, U.1) (W.presheaf.stalk y)), inferInstance⟩
    have hdisj : Disjoint (Py.asIdeal.primeCompl : Set Γ(W, U.1)) Pη.asIdeal :=
      Set.disjoint_left.mpr fun x hx hx' => hx ((show Pη.asIdeal ≤ Py.asIdeal from hle) hx')
    have hPiη : Pi ≤ Pη := by
      show (Ideal.span {f' i}).comap (algebraMap Γ(W, U.1) (W.presheaf.stalk y)) ≤ Pη.asIdeal
      calc _ ≤ (Pη.asIdeal.map (algebraMap Γ(W, U.1) (W.presheaf.stalk y))).comap
              (algebraMap Γ(W, U.1) (W.presheaf.stalk y)) := by
            apply Ideal.comap_mono
            rw [Ideal.span_le, Set.singleton_subset_iff]
            exact Ideal.mem_map_of_mem _ hfη
        _ = Pη.asIdeal := IsLocalization.under_map_of_isPrime_disjoint Py.asIdeal.primeCompl
              (W.presheaf.stalk y) Pη.isPrime hdisj
    have hζZ : hU.fromSpec Pi ∈ (Z.support : Set W) := by
      rw [WMult.mem_support_fromSpec_iff Z U hU]
      show Z.ideal U ≤ (Ideal.span {f' i}).comap (W.presheaf.germ U.1 y hy).hom
      rw [← Ideal.map_le_iff_le_comap, ← WMult.stalkId_eq_map_germ Z y U hy, hZy, Ideal.span_le,
        Set.singleton_subset_iff]
      exact Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem _ hi)
    have hζη : hU.fromSpec Pi ⤳ η := by rw [← hfromη]; exact (hspec _ _).mpr hPiη
    have hcl : closure {η} = σ i := hgen
    have hsub : σ i ⊆ closure {hU.fromSpec Pi} := by
      intro z hz
      rw [← hcl] at hz
      exact specializes_iff_closure_subset.mp hζη hz
    have hirrζ : IsIrreducible (closure {hU.fromSpec Pi}) := isIrreducible_singleton.closure
    have hsubZ : closure {hU.fromSpec Pi} ⊆ (Z.support : Set W) :=
      closure_minimal (Set.singleton_subset_iff.mpr hζZ) Z.support.isClosed
    have hCeq : σ i = closure {hU.fromSpec Pi} := hCm.eq_of_subset ⟨hirrζ, hsubZ⟩ hsub
    have hηζ : η ⤳ hU.fromSpec Pi := by
      rw [specializes_iff_mem_closure, hcl, hCeq]
      exact subset_closure (Set.mem_singleton _)
    have hηPi : Pη ≤ Pi := (hspec _ _).mp (by rw [hfromη]; exact hηζ)
    have hPeq : Pη.asIdeal =
        (Ideal.span {f' i}).comap (algebraMap Γ(W, U.1) (W.presheaf.stalk y)) :=
      congrArg PrimeSpectrum.asIdeal (le_antisymm hηPi hPiη)

    let T := Localization.AtPrime (Ideal.span {f' i})
    have hT : IsLocalization.AtPrime T
        ((Ideal.span {f' i}).comap (algebraMap Γ(W, U.1) (W.presheaf.stalk y))) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (M := Py.asIdeal.primeCompl) (S := W.presheaf.stalk y) (T := T) (Ideal.span {f' i})
    have hT' : IsLocalization Pη.asIdeal.primeCompl T := by
      have hsm : Pη.asIdeal.primeCompl =
          (Ideal.comap (algebraMap Γ(W, U.1) (W.presheaf.stalk y)) (Ideal.span {f' i})).primeCompl := by
        ext x; rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hPeq]
      rw [hsm]; exact hT
    let ηU : U.1 := ⟨η, hηU⟩
    let algη : Algebra Γ(W, U.1) (W.presheaf.stalk η) :=
      TopCat.Presheaf.algebra_section_stalk W.presheaf ηU
    have hlocη : IsLocalization.AtPrime (W.presheaf.stalk η) Pη.asIdeal :=
      hU.isLocalization_stalk ηU
    let φ : W.presheaf.stalk η ≃ₐ[Γ(W, U.1)] T := IsLocalization.algEquiv Pη.asIdeal.primeCompl _ _
    let algYη : Algebra (W.presheaf.stalk y) (W.presheaf.stalk η) :=
      (φ.symm.toRingEquiv.toRingHom.comp (algebraMap (W.presheaf.stalk y) T)).toAlgebra
    have hlocYη : IsLocalization.AtPrime (W.presheaf.stalk η) (Ideal.span {f' i}) :=
      (IsLocalization.isLocalization_iff_of_ringEquiv (M := (Ideal.span {f' i}).primeCompl)
        (S := T) φ.symm.toRingEquiv).mp inferInstance
    have hgerm : ∀ a : Γ(W, U.1), W.presheaf.germ U.1 η hηU a =
        algebraMap (W.presheaf.stalk y) (W.presheaf.stalk η) (W.presheaf.germ U.1 y hy a) :=
by
      intro a
      have h1 := (φ.symm.commutes a).symm
      rw [IsScalarTower.algebraMap_apply Γ(W, U.1) (W.presheaf.stalk y) T] at h1
      exact h1
    have hGη : FinalTheorems.stalkId G η =
        Ideal.span {algebraMap (W.presheaf.stalk y) (W.presheaf.stalk η) γ} := by
      rw [WMult.stalkId_eq_map_germ G η U hηU]
      have hcomp : (W.presheaf.germ U.1 η hηU).hom =
          (algebraMap (W.presheaf.stalk y) (W.presheaf.stalk η)).comp
            (W.presheaf.germ U.1 y hy).hom :=
        RingHom.ext fun a => hgerm a
      rw [hcomp, ← Ideal.map_map, ← WMult.stalkId_eq_map_germ G y U hy, hGy, Ideal.map_span,
        Set.image_singleton]
    have hordS := WMult.ord_isLocalization_eq_exponent f' hrsp.1 hrsp.2 J u m i hi
      (W.presheaf.stalk η)
    have hlen : Module.length (W.presheaf.stalk η) (W.presheaf.stalk η ⧸ FinalTheorems.stalkId G η) =
        (m i : ℕ∞) := by
      rw [hGη, hγu]; exact hordS
    unfold ordAlong
    rw [dif_pos hirr, ← hη, hlen]
    exact ENat.toNat_natCast (m i)
  rw [hGy, hγu]
  have hprod : ∏ i ∈ J, f' i ^ m i = ∏ i ∈ J, f' i ^ ordAlong G (σ i) :=
    Finset.prod_congr rfl fun i hi => by rw [hord i hi]
  rw [hprod]
  exact Ideal.span_singleton_mul_left_unit u.isUnit _

section Chart

variable {s : W ⟶ Spec (.of ℂ)}

/- English proof (translation)
Substitute `hpt` using the available equality. Establish `hψ : ∀ g, P.stalkEquiv x hx hcl (W.presheaf.germ P.V x hx (P.secHom g)) = algebraMap _ (locRing P.K (P.coord x hx)) g` using `P.stalkEquiv_germ x hx hcl`. Establish `: IsDomain (W.presheaf.stalk x)` using `isDomain_of_isRegularLocalRing`. Set `σ' : Fin e → Set W` to `fun l => (S.σ l).elim ∅ fun k => (c k : Set W)`. Establish `hσ' : ∀ l ∈ S.J, IsBranch (Z.support : Set W) (P.secHom (S.r l)) x (σ' l)`.

Introduce `l hl`. Take `⟨k, hk, hb⟩` from `hσ l hl`. Use `show IsBranch _ _ x ((S.σ l).elim ∅ fun k => (c k : Set W))`. Rewrite using `[hk]`. Conclude with `hb`.

Establish `hmain : FinalTheorems.stalkId G x = Ideal.span {∏ l ∈ S.J, W.presheaf.germ P.V x hx (P.secHom (S.r l)) ^ ordAlong G (σ' l)}` using `stalkId_eq_monomial (U := P.affOpen) hG hGZ x hx (fun l => P.secHom (S.r l)) S.J (WMult.rsp_of_sncData P Z x hx hcl hdim S) (WMult.stalkId_eq_span_of_sncData P Z x hx hcl S) σ' hσ'`. Rewrite `hmain` using `[ha]`. Take `⟨v, hv⟩` from `Ideal.span_singleton_eq_span_singleton.mp hmain`. Use `⟨P.stalkEquiv x hx hcl ↑v⁻¹, (Units.isUnit v⁻¹).map _, ?_⟩` and prove the remaining obligations. Establish `hv' : W.presheaf.germ P.V x hx (P.secHom a) = (∏ l ∈ S.J, W.presheaf.germ P.V x hx (P.secHom (S.r l)) ^ ordAlong G (σ' l)) * ↑v⁻¹`.

Rewrite using `[← hv, mul_assoc, Units.mul_inv, mul_one]`. Establish `hprod : P.stalkEquiv x hx hcl (∏ l ∈ S.J, W.presheaf.germ P.V x hx (P.secHom (S.r l)) ^ ordAlong G (σ' l)) = ∏ l ∈ S.J, algebraMap _ (locRing P.K (P.coord x hx)) (S.r l) ^ (S.σ l).elim 0 fun k => ordAlong G (c k)`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun l hl => ?_` and prove the remaining obligations. Take `⟨k, hk, -⟩` from `hσ l hl`.

Rewrite using `[map_pow]`. Use `show P.stalkEquiv x hx hcl (W.presheaf.germ P.V x hx (P.secHom (S.r l))) ^ ordAlong G ((S.σ l).elim ∅ fun k => (c k : Set W)) = _`. Rewrite using `[hψ, hk]`. Both sides reduce to the same expression. Rewrite using `[← hψ a, hv', map_mul, hprod]`.

Conclude with `mul_comm _ _`.
-/
theorem monomial_chart [IsNoetherian W] [LocallyOfFiniteType s] {Z G : W.IdealSheafData}
    (hG : FinalTheorems.EffCartier G) (hGZ : (G.support : Set W) ⊆ Z.support) (P : AffPres s) {rc : ℕ}
    (c : Fin rc ≃ comps (Z.support : Set W)) (e : ℕ) (x : W) (hx : x ∈ P.V)
    (hcl : IsClosed ({x} : Set W)) [IsRegularLocalRing (W.presheaf.stalk x)]
    (hdim : ringKrullDim (W.presheaf.stalk x) = e) {pt : Fin P.n → ℂ} (hpt : P.coord x hx = pt)
    (S : SncData P.K (P.bdIdeal Z) pt e rc)
    (hσ : ∀ l ∈ S.J, ∃ k, S.σ l = some k ∧
      IsBranch (Z.support : Set W) (P.secHom (S.r l)) x (c k))
    (a : MvPolynomial (Fin P.n) ℂ)
    (ha : FinalTheorems.stalkId G x = Ideal.span {W.presheaf.germ P.V x hx (P.secHom a)}) :
    ∃ u : locRing P.K pt, IsUnit u ∧
      algebraMap _ (locRing P.K pt) a =
        u * ∏ l ∈ S.J, algebraMap _ (locRing P.K pt) (S.r l) ^
          (S.σ l).elim 0 fun k => ordAlong G (c k) := by
  classical
  subst hpt
  have hψ : ∀ g, P.stalkEquiv x hx hcl (W.presheaf.germ P.V x hx (P.secHom g)) =
      algebraMap _ (locRing P.K (P.coord x hx)) g :=
    P.stalkEquiv_germ x hx hcl
  have : IsDomain (W.presheaf.stalk x) := isDomain_of_isRegularLocalRing
  let σ' : Fin e → Set W := fun l => (S.σ l).elim ∅ fun k => (c k : Set W)
  have hσ' : ∀ l ∈ S.J, IsBranch (Z.support : Set W) (P.secHom (S.r l)) x (σ' l) := by
    intro l hl
    obtain ⟨k, hk, hb⟩ := hσ l hl
    show IsBranch _ _ x ((S.σ l).elim ∅ fun k => (c k : Set W))
    rw [hk]
    exact hb
  have hmain : FinalTheorems.stalkId G x = Ideal.span {∏ l ∈ S.J,
      W.presheaf.germ P.V x hx (P.secHom (S.r l)) ^ ordAlong G (σ' l)} :=
    stalkId_eq_monomial (U := P.affOpen) hG hGZ x hx (fun l => P.secHom (S.r l)) S.J
      (WMult.rsp_of_sncData P Z x hx hcl hdim S) (WMult.stalkId_eq_span_of_sncData P Z x hx hcl S)
      σ' hσ'
  rw [ha] at hmain
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hmain
  refine ⟨P.stalkEquiv x hx hcl ↑v⁻¹, (Units.isUnit v⁻¹).map _, ?_⟩
  have hv' : W.presheaf.germ P.V x hx (P.secHom a) =
      (∏ l ∈ S.J, W.presheaf.germ P.V x hx (P.secHom (S.r l)) ^ ordAlong G (σ' l)) * ↑v⁻¹ := by
    rw [← hv, mul_assoc, Units.mul_inv, mul_one]
  have hprod : P.stalkEquiv x hx hcl
      (∏ l ∈ S.J, W.presheaf.germ P.V x hx (P.secHom (S.r l)) ^ ordAlong G (σ' l)) =
      ∏ l ∈ S.J, algebraMap _ (locRing P.K (P.coord x hx)) (S.r l) ^
          (S.σ l).elim 0 fun k => ordAlong G (c k) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun l hl => ?_
    obtain ⟨k, hk, -⟩ := hσ l hl
    rw [map_pow]
    show P.stalkEquiv x hx hcl (W.presheaf.germ P.V x hx (P.secHom (S.r l))) ^
      ordAlong G ((S.σ l).elim ∅ fun k => (c k : Set W)) = _
    rw [hψ, hk]
    rfl
  rw [← hψ a, hv', map_mul, hprod]
  exact mul_comm _ _

end Chart

end

end ReciprocityTheory.AnForm.R
