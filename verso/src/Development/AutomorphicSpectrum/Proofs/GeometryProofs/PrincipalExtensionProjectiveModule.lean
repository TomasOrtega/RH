import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.IdealNormPrincipalInExtension
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Basis

/- English proof (translation)
Use `haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite _ _`. Use `haveI : Module.Flat R M := IsDedekindDomain.flat_iff_torsion_eq_bot.2 (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)`. Conclude with `Module.Flat.projective_of_finitePresentation`.
-/
theorem projective_of_torsionFree {R M : Type} [CommRing R] [IsDedekindDomain R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.IsTorsionFree R M] : Module.Projective R M := by
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite _ _
  haveI : Module.Flat R M := IsDedekindDomain.flat_iff_torsion_eq_bot.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  exact Module.Flat.projective_of_finitePresentation

/- English proof (translation)
Establish `h` using `Submodule.finrank_quotient_add_finrank I`. Establish `h0 : Module.finrank R (R ⧸ I) = 0`. Rewrite using `[Module.finrank_eq_zero_iff]`. Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`. Introduce `x`.

Use `⟨a, ha0, ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective I x`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `I.mul_mem_right y ha`. Rewrite `h` using `[h0, zero_add, Module.finrank_self]`.

Conclude with `h`.
-/
theorem finrank_ideal {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (hI : I ≠ ⊥) :
    Module.finrank R I = 1 := by
  have h := Submodule.finrank_quotient_add_finrank I
  have h0 : Module.finrank R (R ⧸ I) = 0 := by
    rw [Module.finrank_eq_zero_iff]
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    intro x
    refine ⟨a, ha0, ?_⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective I x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact I.mul_mem_right y ha
  rw [h0, zero_add, Module.finrank_self] at h
  exact h

/- English proof (translation)
Proceed by induction on `g with`. Consider the case `zero`. Introduce `B _ _ _ _ hB`. Establish `hs : Subsingleton B`. Use `subsingleton_of_forall_eq 0 fun x => ?_` and prove the remaining obligations.

Take `⟨a, ha, hax⟩` from `Module.finrank_eq_zero_iff.1 hB x`. Conclude with `(smul_eq_zero.1 hax).resolve_left ha`. Use `⟨Empty, inferInstance, Empty.elim, fun i => i.elim, by simp, fun i => i.elim, ?_⟩` and prove the remaining obligations. Conclude with `Subsingleton.elim _ _`. Consider the case `succ g ih`.

Introduce `B _ _ _ _ hB`. Use `haveI : Module.Projective R B := projective_of_torsionFree`. Use `haveI : Nontrivial B := by`. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`.

Rewrite `hB` using `[Module.finrank_zero_of_subsingleton]`. Use linear arithmetic over natural numbers and integers. Take `⟨x, hx⟩` from `exists_ne (0 : B)`. Take `⟨f, hf⟩` from `Module.Projective.exists_dual_ne_zero R hx`. Set `J : Ideal R` to `LinearMap.range f`.

Establish `hJ : J ≠ ⊥` using `fun h => hf (by`. Establish `: f x ∈ J` using `⟨x, rfl⟩`. Rewrite `this` using `[h]`. Simplify using `using this)`. Use `haveI : Module.Projective R J := projective_of_torsionFree`.

Take `⟨s, hs⟩` from `LinearMap.exists_rightInverse_of_surjective f.rangeRestrict (LinearMap.range_rangeRestrict f)`. Establish `hrank : Module.finrank R (LinearMap.ker f) = g`. Establish `h1` using `Submodule.finrank_quotient_add_finrank (LinearMap.ker f)`. Rewrite `h1` using `[f.quotKerEquivRange.finrank_eq, hB]`. Establish `h2 : Module.finrank R (LinearMap.range f) = 1` using `finrank_ideal J hJ`.

Use linear arithmetic over natural numbers and integers. Take `⟨ι, _, I, b, hc, hI, hsup⟩` from `ih (LinearMap.ker f) hrank`. Set `I' : Option ι → Ideal R` to `fun o => o.elim J I`. Set `b' : ∀ o, I' o →ₗ[R] B` to `fun o => match o with`. Consider the case `none => s`.

Consider the case `some i => (LinearMap.ker f).subtype ∘ₗ b i`. Use `⟨Option ι, inferInstance, I', b', by simp [hc], ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `(_ | i)`. Conclude with `hJ`. Conclude with `hI i`.

Use `set T : Submodule R B := ⨆ o, LinearMap.range (b' o) with hT`. Establish `hker : (⨆ i, LinearMap.range (b i)) ≤ T.comap (LinearMap.ker f).subtype`. Use `iSup_le fun i => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `Submodule.mem_iSup_of_mem (some i) ⟨a, rfl⟩`.

Rewrite `hker` using `[hsup]`. Rewrite using `[eq_top_iff]`. Introduce `z _`. Establish `hz : f (z - s (f.rangeRestrict z)) = 0`. Establish `h3 : f.rangeRestrict (s (f.rangeRestrict z)) = f.rangeRestrict z` using `LinearMap.congr_fun hs _`.

Establish `h4 : f (s (f.rangeRestrict z)) = f z` using `congrArg Subtype.val h3`. Rewrite using `[map_sub, h4, sub_self]`. Establish `h5 : z - s (f.rangeRestrict z) ∈ T` using `hker (Submodule.mem_top (x := (⟨_, hz⟩ : LinearMap.ker f)))`. Establish `h6 : s (f.rangeRestrict z) ∈ T` using `Submodule.mem_iSup_of_mem none ⟨f.rangeRestrict z, rfl⟩`. Simplify using `using T.add_mem h5 h6`.
-/
theorem exists_ideal_cover {R : Type} [CommRing R] [IsDedekindDomain R] (g : ℕ) :
    ∀ (B : Type) [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.IsTorsionFree R B],
      Module.finrank R B = g →
      ∃ (ι : Type) (_ : Fintype ι) (I : ι → Ideal R) (b : ∀ i, I i →ₗ[R] B),
        Fintype.card ι = g ∧ (∀ i, I i ≠ ⊥) ∧ ⨆ i, LinearMap.range (b i) = ⊤ := by
  induction g with
  | zero =>
    intro B _ _ _ _ hB
    have hs : Subsingleton B := by
      refine subsingleton_of_forall_eq 0 fun x => ?_
      obtain ⟨a, ha, hax⟩ := Module.finrank_eq_zero_iff.1 hB x
      exact (smul_eq_zero.1 hax).resolve_left ha
    refine ⟨Empty, inferInstance, Empty.elim, fun i => i.elim, by simp, fun i => i.elim, ?_⟩
    exact Subsingleton.elim _ _
  | succ g ih =>
    intro B _ _ _ _ hB
    haveI : Module.Projective R B := projective_of_torsionFree
    haveI : Nontrivial B := by
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      rw [Module.finrank_zero_of_subsingleton] at hB
      omega
    obtain ⟨x, hx⟩ := exists_ne (0 : B)
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero R hx
    let J : Ideal R := LinearMap.range f
    have hJ : J ≠ ⊥ := fun h => hf (by
      have : f x ∈ J := ⟨x, rfl⟩
      rw [h] at this
      simpa using this)
    haveI : Module.Projective R J := projective_of_torsionFree
    obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict
      (LinearMap.range_rangeRestrict f)
    have hrank : Module.finrank R (LinearMap.ker f) = g := by
      have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
      rw [f.quotKerEquivRange.finrank_eq, hB] at h1
      have h2 : Module.finrank R (LinearMap.range f) = 1 := finrank_ideal J hJ
      omega
    obtain ⟨ι, _, I, b, hc, hI, hsup⟩ := ih (LinearMap.ker f) hrank
    let I' : Option ι → Ideal R := fun o => o.elim J I
    let b' : ∀ o, I' o →ₗ[R] B := fun o => match o with
      | none => s
      | some i => (LinearMap.ker f).subtype ∘ₗ b i
    refine ⟨Option ι, inferInstance, I', b', by simp [hc], ?_, ?_⟩
    · rintro (_ | i)
      · exact hJ
      · exact hI i
    · set T : Submodule R B := ⨆ o, LinearMap.range (b' o) with hT
      have hker : (⨆ i, LinearMap.range (b i)) ≤ T.comap (LinearMap.ker f).subtype := by
        refine iSup_le fun i => ?_
        rintro _ ⟨a, rfl⟩
        exact Submodule.mem_iSup_of_mem (some i) ⟨a, rfl⟩
      rw [hsup] at hker
      rw [eq_top_iff]
      intro z _
      have hz : f (z - s (f.rangeRestrict z)) = 0 := by
        have h3 : f.rangeRestrict (s (f.rangeRestrict z)) = f.rangeRestrict z :=
          LinearMap.congr_fun hs _
        have h4 : f (s (f.rangeRestrict z)) = f z := congrArg Subtype.val h3
        rw [map_sub, h4, sub_self]
      have h5 : z - s (f.rangeRestrict z) ∈ T :=
        hker (Submodule.mem_top (x := (⟨_, hz⟩ : LinearMap.ker f)))
      have h6 : s (f.rangeRestrict z) ∈ T :=
        Submodule.mem_iSup_of_mem none ⟨f.rangeRestrict z, rfl⟩
      simpa using T.add_mem h5 h6

/- English proof (translation)
Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Rewrite `hc` using `[Ideal.span_singleton_zero]`. Conclude with `pow_ne_zero h hI hc`. Establish `hcK : (c : K) ≠ 0` using `fun h0 => hc0 (RingOfIntegers.ext h0)`.

Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Rewrite `hz` using `[zero_pow hh]`. Conclude with `hcK ((map_eq_zero _).mp hz.symm)`. Establish `hint : IsIntegral ℤ z`.

Use `IsIntegral.of_pow (Nat.pos_of_ne_zero hh) ?_` and prove the remaining obligations. Rewrite using `[hz]`. Conclude with `(c.2 : IsIntegral ℤ (c : K)).map (IsScalarTower.toAlgHom ℤ K K')`. Set `y : 𝓞 K'` to `⟨z, hint⟩`. Establish `hyz : (y : K') = z` using `rfl`.

Establish `hy0 : y ≠ 0` using `fun h0 => hz0 (by rw [← hyz, h0]; rfl)`. Establish `hyc : y ^ h = algebraMap (𝓞 K) (𝓞 K') c`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Conclude with `(map_pow (algebraMap (𝓞 K') K') y h).trans hz`. Establish `hspan : Ideal.span {y} ^ h = (I.map (algebraMap (𝓞 K) (𝓞 K'))) ^ h`.

Rewrite using `[Ideal.span_singleton_pow, hyc, ← Ideal.map_pow, hc, Ideal.map_span, Set.image_singleton]`. Establish `hs0 : Ideal.span {y} ≠ ⊥` using `by simpa using hy0`. Use `⟨y, hy0, (GlobalTheory.CompanionTheory.Lines.ideal_eq_of_pow_eq hh hs0 ?_ hspan).symm⟩` and prove the remaining obligations. Introduce `h0`. Rewrite `hspan` using `[h0, ← Ideal.zero_eq_bot, zero_pow hh]`.

Conclude with `pow_ne_zero h hs0 hspan`.
-/
theorem span_of_root (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra K K'] (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (h : ℕ) (hh : h ≠ 0) (c : 𝓞 K)
    (hc : I ^ h = Ideal.span {c}) (z : K') (hz : z ^ h = algebraMap K K' (c : K)) :
    ∃ y : 𝓞 K', y ≠ 0 ∧ I.map (algebraMap (𝓞 K) (𝓞 K')) = Ideal.span {y} := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_zero] at hc
    exact pow_ne_zero h hI hc
  have hcK : (c : K) ≠ 0 := fun h0 => hc0 (RingOfIntegers.ext h0)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hh] at hz
    exact hcK ((map_eq_zero _).mp hz.symm)
  have hint : IsIntegral ℤ z := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hh) ?_
    rw [hz]
    exact (c.2 : IsIntegral ℤ (c : K)).map (IsScalarTower.toAlgHom ℤ K K')
  let y : 𝓞 K' := ⟨z, hint⟩
  have hyz : (y : K') = z := rfl
  have hy0 : y ≠ 0 := fun h0 => hz0 (by rw [← hyz, h0]; rfl)
  have hyc : y ^ h = algebraMap (𝓞 K) (𝓞 K') c := by
    apply RingOfIntegers.ext
    exact (map_pow (algebraMap (𝓞 K') K') y h).trans hz
  have hspan : Ideal.span {y} ^ h = (I.map (algebraMap (𝓞 K) (𝓞 K'))) ^ h := by
    rw [Ideal.span_singleton_pow, hyc, ← Ideal.map_pow, hc, Ideal.map_span, Set.image_singleton]
  have hs0 : Ideal.span {y} ≠ ⊥ := by simpa using hy0
  refine ⟨y, hy0, (GlobalTheory.CompanionTheory.Lines.ideal_eq_of_pow_eq hh hs0 ?_ hspan).symm⟩
  intro h0
  rw [h0, ← Ideal.zero_eq_bot, zero_pow hh] at hspan
  exact pow_ne_zero h hs0 hspan

/- English proof (translation)
Use `choose h c hh hc using fun i => GlobalTheory.UnRep.exists_pow_eq_span_singleton L (J i) (hJ i)`. Set `q : ι → Polynomial L` to `fun i => Polynomial.X ^ h i - Polynomial.C (c i : L)`. Set `p : Polynomial L` to `∏ i, q i`. Establish `hq0 : ∀ i, q i ≠ 0` using `fun i => Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero (hh i)) _`. Establish `hp0 : p ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => hq0 i`.

Use `haveI : FiniteDimensional ℚ p.SplittingField := FiniteDimensional.trans ℚ L p.SplittingField`. Use `haveI : NumberField p.SplittingField := NumberField.mk`. Establish `hroot : ∀ i, ∃ z : p.SplittingField, z ^ h i = algebraMap L p.SplittingField (c i : L)`. Introduce `i`. Establish `hdvd : (q i).map (algebraMap L p.SplittingField) ∣ p.map (algebraMap L p.SplittingField)` using `Polynomial.map_dvd _ (Finset.dvd_prod_of_mem q (Finset.mem_univ i))`.

Establish `hsp` using `(Polynomial.SplittingField.splits p).of_dvd (Polynomial.map_ne_zero hp0) hdvd`. Establish `hdeg : (q i).degree ≠ 0`. Rewrite using `[Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero (hh i))]`. Conclude with `hh i` after adjusting the coercions. Take `⟨z, hz⟩` from `hsp.exists_eval_eq_zero (by rwa [Polynomial.degree_map])`.

Conclude with `⟨z, by simpa [q, sub_eq_zero] using hz⟩`. Use `choose z hz using hroot`. Use `choose y hy using fun i => span_of_root L p.SplittingField (J i) (hJ i) (h i) (hh i) (c i) (hc i) (z i) (hz i)`. Conclude with `⟨p.SplittingField, inferInstance, inferInstance, inferInstance, y, hy⟩`.
-/
theorem exists_extension_principal {ι : Type} [Fintype ι] (L : Type) [Field L] [NumberField L]
    (J : ι → Ideal (𝓞 L)) (hJ : ∀ i, J i ≠ ⊥) :
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (y : ι → 𝓞 L'),
      ∀ i, y i ≠ 0 ∧ (J i).map (algebraMap (𝓞 L) (𝓞 L')) = Ideal.span {y i} := by
  classical
  choose h c hh hc using fun i => GlobalTheory.UnRep.exists_pow_eq_span_singleton L (J i) (hJ i)
  let q : ι → Polynomial L := fun i => Polynomial.X ^ h i - Polynomial.C (c i : L)
  let p : Polynomial L := ∏ i, q i
  have hq0 : ∀ i, q i ≠ 0 := fun i => Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero (hh i)) _
  have hp0 : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hq0 i
  haveI : FiniteDimensional ℚ p.SplittingField := FiniteDimensional.trans ℚ L p.SplittingField
  haveI : NumberField p.SplittingField := NumberField.mk
  have hroot : ∀ i, ∃ z : p.SplittingField, z ^ h i = algebraMap L p.SplittingField (c i : L) := by
    intro i
    have hdvd : (q i).map (algebraMap L p.SplittingField) ∣ p.map (algebraMap L p.SplittingField) :=
      Polynomial.map_dvd _ (Finset.dvd_prod_of_mem q (Finset.mem_univ i))
    have hsp := (Polynomial.SplittingField.splits p).of_dvd
      (Polynomial.map_ne_zero hp0) hdvd
    have hdeg : (q i).degree ≠ 0 := by
      rw [Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero (hh i))]
      exact_mod_cast hh i
    obtain ⟨z, hz⟩ := hsp.exists_eval_eq_zero (by rwa [Polynomial.degree_map])
    exact ⟨z, by simpa [q, sub_eq_zero] using hz⟩
  choose z hz using hroot
  choose y hy using fun i => span_of_root L p.SplittingField (J i) (hJ i) (h i) (hh i) (c i) (hc i)
    (z i) (hz i)
  exact ⟨p.SplittingField, inferInstance, inferInstance, inferInstance, y, hy⟩

/- English proof (translation)
Establish `hx' : x ∈ Submodule.span R' (φ '' (I : Set R))` using `hx`. Proceed by induction on `hx' using Submodule.span_induction with`. Consider the case `mem x h`. Take `⟨a', ha', rfl⟩` from `h`. Use `⟨io (b ⟨a', ha'⟩), fun a => ?_⟩` and prove the remaining obligations.

Establish `h1 : (a : R) • (⟨a', ha'⟩ : I) = a' • a` using `Subtype.ext (by simp [mul_comm])`. Establish `h2 : (a : R) • b ⟨a', ha'⟩ = a' • b a`. Rewrite using `[← b.map_smul, ← b.map_smul, h1]`. Combine the equalities or inequalities in the displayed calculation. Consider the case `zero => exact ⟨0, fun a => by simp⟩`.

Consider the case `add u v _ _ hu hv`. Take `⟨e₁, h₁⟩` from `hu (by assumption)`. Take `⟨e₂, h₂⟩` from `hv (by assumption)`. Conclude with `⟨e₁ + e₂, fun a => by rw [smul_add, h₁, h₂, add_smul]⟩`. Consider the case `smul r u _ hu`.

Take `⟨e, h⟩` from `hu (by assumption)`. Conclude with `⟨r • e, fun a => by rw [smul_comm, h, smul_smul, smul_eq_mul]⟩`.
-/
theorem exists_image_element {R R' B B' : Type} [CommRing R] [CommRing R'] [AddCommGroup B]
    [Module R B] [AddCommGroup B'] [Module R' B'] (φ : R →+* R') (I : Ideal R) (b : I →ₗ[R] B)
    (io : B →ₛₗ[φ] B') (x : R') (hx : x ∈ I.map φ) :
    ∃ e : B', ∀ a : I, φ a • e = x • io (b a) := by
  have hx' : x ∈ Submodule.span R' (φ '' (I : Set R)) := hx
  induction hx' using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a', ha', rfl⟩ := h
    refine ⟨io (b ⟨a', ha'⟩), fun a => ?_⟩
    have h1 : (a : R) • (⟨a', ha'⟩ : I) = a' • a := Subtype.ext (by simp [mul_comm])
    have h2 : (a : R) • b ⟨a', ha'⟩ = a' • b a := by
      rw [← b.map_smul, ← b.map_smul, h1]
    calc φ a • io (b ⟨a', ha'⟩) = io ((a : R) • b ⟨a', ha'⟩) := (io.map_smulₛₗ _ _).symm
      _ = io (a' • b a) := by rw [h2]
      _ = φ a' • io (b a) := io.map_smulₛₗ _ _
  | zero => exact ⟨0, fun a => by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨e₁, h₁⟩ := hu (by assumption)
    obtain ⟨e₂, h₂⟩ := hv (by assumption)
    exact ⟨e₁ + e₂, fun a => by rw [smul_add, h₁, h₂, add_smul]⟩
  | smul r u _ hu =>
    obtain ⟨e, h⟩ := hu (by assumption)
    exact ⟨r • e, fun a => by rw [smul_comm, h, smul_smul, smul_eq_mul]⟩

/- English proof (translation)
Use `choose e he using fun i => exists_image_element φ (I i) (b i) io (y i) (by rw [hy i]; exact Ideal.mem_span_singleton_self _)`. Use `⟨e, ?_⟩` and prove the remaining obligations. Use `set S := Submodule.span R' (Set.range e) with hS`. Establish `hle : (⨆ i, LinearMap.range (b i)) ≤ S.comap io`. Use `iSup_le fun i => ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, rfl⟩`. Establish `hmem : φ a ∈ (I i).map φ` using `Ideal.mem_map_of_mem φ a.2`. Rewrite `hmem` using `[hy i, Ideal.mem_span_singleton']`. Take `⟨r, hr⟩` from `hmem`. Establish `h1` using `he i a`.

Rewrite `h1` using `[← hr, mul_comm, mul_smul]`. Establish `h2 : r • e i = io (b i a)` using `smul_right_injective B' (hy0 i) h1`. Express the relevant statement in the definitionally equal form `io (b i a) ∈ S`. Rewrite using `[← h2]`. Conclude with `S.smul_mem r (Submodule.subset_span ⟨i, rfl⟩)`.

Rewrite `hle` using `[hsup]`. Rewrite using `[eq_top_iff, ← hspan]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `hle (Submodule.mem_top (x := x))`.
-/
theorem exists_spanning {R R' B B' ι : Type} [CommRing R] [CommRing R'] [IsDomain R']
    [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R' B'] [Module.IsTorsionFree R' B']
    (φ : R →+* R') (I : ι → Ideal R) (b : ∀ i, I i →ₗ[R] B)
    (hsup : ⨆ i, LinearMap.range (b i) = ⊤) (io : B →ₛₗ[φ] B')
    (hspan : Submodule.span R' (Set.range io) = ⊤) (y : ι → R') (hy0 : ∀ i, y i ≠ 0)
    (hy : ∀ i, (I i).map φ = Ideal.span {y i}) :
    ∃ e : ι → B', Submodule.span R' (Set.range e) = ⊤ := by
  choose e he using fun i => exists_image_element φ (I i) (b i) io (y i)
    (by rw [hy i]; exact Ideal.mem_span_singleton_self _)
  refine ⟨e, ?_⟩
  set S := Submodule.span R' (Set.range e) with hS
  have hle : (⨆ i, LinearMap.range (b i)) ≤ S.comap io := by
    refine iSup_le fun i => ?_
    rintro _ ⟨a, rfl⟩
    have hmem : φ a ∈ (I i).map φ := Ideal.mem_map_of_mem φ a.2
    rw [hy i, Ideal.mem_span_singleton'] at hmem
    obtain ⟨r, hr⟩ := hmem
    have h1 := he i a
    rw [← hr, mul_comm, mul_smul] at h1
    have h2 : r • e i = io (b i a) := smul_right_injective B' (hy0 i) h1
    change io (b i a) ∈ S
    rw [← h2]
    exact S.smul_mem r (Submodule.subset_span ⟨i, rfl⟩)
  rw [hsup] at hle
  rw [eq_top_iff, ← hspan]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, rfl⟩
  exact hle (Submodule.mem_top (x := x))

/- English proof (translation)
Set `f : (ι → R) →ₗ[R] M` to `Fintype.linearCombination R e`. Establish `hr : LinearMap.range f = ⊤`. Rewrite using `[Fintype.range_linearCombination, hs]`. Establish `h1` using `Submodule.finrank_quotient_add_finrank (LinearMap.ker f)`. Rewrite `h1` using `[f.quotKerEquivRange.finrank_eq, hr, finrank_top, Module.finrank_pi, hc]`.

Establish `h0 : Module.finrank R (LinearMap.ker f) = 0` using `by omega`. Establish `hk : LinearMap.ker f = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Take `⟨a, ha, hax⟩` from `Module.finrank_eq_zero_iff.1 h0 ⟨x, hx⟩`.

Establish `h2 : a • x = 0` using `congrArg Subtype.val hax`. Conclude with `(smul_eq_zero.1 h2).resolve_left ha`. Use `Fintype.linearIndependent_iff.2 fun c hcz i => ?_` and prove the remaining obligations. Establish `hmem : c ∈ LinearMap.ker f`. Simplify `hcz` using `[f, Fintype.linearCombination_apply]`.

Rewrite `hmem` using `[hk, Submodule.mem_bot]`. Conclude with `congrFun hmem i`.
-/
theorem linearIndependent_of_span_card {R M ι : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Fintype ι] (e : ι → M)
    (hs : Submodule.span R (Set.range e) = ⊤) (hc : Fintype.card ι = Module.finrank R M) :
    LinearIndependent R e := by
  classical
  let f : (ι → R) →ₗ[R] M := Fintype.linearCombination R e
  have hr : LinearMap.range f = ⊤ := by
    rw [Fintype.range_linearCombination, hs]
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
  rw [f.quotKerEquivRange.finrank_eq, hr, finrank_top, Module.finrank_pi, hc] at h1
  have h0 : Module.finrank R (LinearMap.ker f) = 0 := by omega
  have hk : LinearMap.ker f = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, ha, hax⟩ := Module.finrank_eq_zero_iff.1 h0 ⟨x, hx⟩
    have h2 : a • x = 0 := congrArg Subtype.val hax
    exact (smul_eq_zero.1 h2).resolve_left ha
  refine Fintype.linearIndependent_iff.2 fun c hcz i => ?_
  have hmem : c ∈ LinearMap.ker f := by
    simpa [f, Fintype.linearCombination_apply] using hcz
  rw [hk, Submodule.mem_bot] at hmem
  exact congrFun hmem i

/- English proof (translation)
Introduce `L _ _ B _ _ _ _ I hI`. Use `haveI : Module.IsTorsionFree (𝓞 L) B := Module.Flat.isTorsionFree`. Take `⟨ι, _, J, b, hc, hJ, hsup⟩` from `exists_ideal_cover (Module.finrank (𝓞 L) B) B rfl`. Take `⟨L', _, _, _, y, hy⟩` from `exists_extension_principal L (fun o : Option ι => o.elim I J) (by rintro (_ | i); exacts [hI, hJ i])`. Use `⟨L', inferInstance, inferInstance, inferInstance, y none, (hy none).2, ?_⟩` and prove the remaining obligations.

Introduce `B' _ _ _ _ io hspan hrk`. Use `haveI : Module.IsTorsionFree (𝓞 L') B' := Module.Flat.isTorsionFree`. Take `⟨e, he⟩` from `exists_spanning (algebraMap (𝓞 L) (𝓞 L')) J b hsup io hspan (fun i => y (some i)) (fun i => (hy (some i)).1) (fun i => (hy (some i)).2)`. Establish `hli : LinearIndependent (𝓞 L') e` using `linearIndependent_of_span_card e he (hc.trans hrk.symm)`. Set `ε : Fin (Module.finrank (𝓞 L') B') ≃ ι` to `(Fintype.equivFinOfCardEq (hc.trans hrk.symm)).symm`.

Use `⟨e ∘ ε, hli.comp _ ε.injective, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.range_comp, ε.surjective.range_eq, Set.image_univ, he]`.
-/
theorem exists_basis_after_extension : ∀ (L : Type) [Field L] [NumberField L] (B : Type) [AddCommGroup B] [Module (𝓞 L) B] [Module.Finite (𝓞 L) B] [Module.Projective (𝓞 L) B] (I : Ideal (𝓞 L)), I ≠ ⊥ → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (y : 𝓞 L'), I.map (algebraMap (𝓞 L) (𝓞 L')) = Ideal.span {y} ∧ ∀ (B' : Type) [AddCommGroup B'] [Module (𝓞 L') B'] [Module.Finite (𝓞 L') B'] [Module.Projective (𝓞 L') B'] (io : B →ₛₗ[algebraMap (𝓞 L) (𝓞 L')] B'), Submodule.span (𝓞 L') (Set.range io) = ⊤ → Module.finrank (𝓞 L') B' = Module.finrank (𝓞 L) B → ∃ e : Fin (Module.finrank (𝓞 L') B') → B', LinearIndependent (𝓞 L') e ∧ Submodule.span (𝓞 L') (Set.range e) = ⊤ := by
  intro L _ _ B _ _ _ _ I hI
  haveI : Module.IsTorsionFree (𝓞 L) B := Module.Flat.isTorsionFree
  obtain ⟨ι, _, J, b, hc, hJ, hsup⟩ := exists_ideal_cover (Module.finrank (𝓞 L) B) B rfl
  obtain ⟨L', _, _, _, y, hy⟩ := exists_extension_principal L (fun o : Option ι => o.elim I J)
    (by rintro (_ | i); exacts [hI, hJ i])
  refine ⟨L', inferInstance, inferInstance, inferInstance, y none, (hy none).2, ?_⟩
  intro B' _ _ _ _ io hspan hrk
  haveI : Module.IsTorsionFree (𝓞 L') B' := Module.Flat.isTorsionFree
  obtain ⟨e, he⟩ := exists_spanning (algebraMap (𝓞 L) (𝓞 L')) J b hsup io hspan
    (fun i => y (some i)) (fun i => (hy (some i)).1) (fun i => (hy (some i)).2)
  have hli : LinearIndependent (𝓞 L') e :=
    linearIndependent_of_span_card e he (hc.trans hrk.symm)
  let ε : Fin (Module.finrank (𝓞 L') B') ≃ ι :=
    (Fintype.equivFinOfCardEq (hc.trans hrk.symm)).symm
  refine ⟨e ∘ ε, hli.comp _ ε.injective, ?_⟩
  rw [Set.range_comp, ε.surjective.range_eq, Set.image_univ, he]

end GlobalTheory.CompanionTheory.Ar.Basis
