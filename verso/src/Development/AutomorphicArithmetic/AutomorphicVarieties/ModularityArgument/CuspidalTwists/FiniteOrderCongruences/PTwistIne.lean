import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.TwistIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceEqOfContEmbCompEq
import ReciprocityTheory.GaloisValuations.Global

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix Pointwise

namespace UpperTheory.V.Cu2

namespace TwistIne

/- English proof (translation)
Introduce `hdA`. Take `⟨u, v, huv⟩` from `(Nat.prime_iff_prime_int.mp hl).coprime_iff_not_dvd.2 hd`. Establish `e : (1 : Ω) = (u : Ω) * (l : Ω) + (v : Ω) * (d : Ω)`. Use `congrArg (Int.cast : ℤ → Ω) huv` as an intermediate fact. Move the coercions through the operations in `at this`.

Conclude with `this.symm`. Establish `h1 : ∀ (a : ℤ) (x : Ω), A.valuation x < 1 → A.valuation ((a : Ω) * x) < 1` using `fun a x hx => by`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (intCast_mem A a))) hx`. Use `Valuation.map_add_lt A.valuation (h1 u _ hA) (h1 v _ hdA)` as an intermediate fact.

Rewrite `this` using `[← e, map_one]`. Conclude with `lt_irrefl _ this`.
-/
private theorem not_lt_of_not_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {l : ℕ} (hl : l.Prime)
    (hA : A.valuation (l : Ω) < 1) {d : ℤ} (hd : ¬ (l : ℤ) ∣ d) : ¬ A.valuation (d : Ω) < 1 := by
  intro hdA
  obtain ⟨u, v, huv⟩ := (Nat.prime_iff_prime_int.mp hl).coprime_iff_not_dvd.2 hd
  have e : (1 : Ω) = (u : Ω) * (l : Ω) + (v : Ω) * (d : Ω) := by
    have := congrArg (Int.cast : ℤ → Ω) huv
    push_cast at this
    exact this.symm
  have h1 : ∀ (a : ℤ) (x : Ω), A.valuation x < 1 → A.valuation ((a : Ω) * x) < 1 := fun a x hx => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (intCast_mem A a))) hx
  have := Valuation.map_add_lt A.valuation (h1 u _ hA) (h1 v _ hdA)
  rw [← e, map_one] at this
  exact lt_irrefl _ this

/- English proof (translation)
Establish `hc : Fintype.card (K →+* ℂ) = 2` using `by rw [Embeddings.card, hK]`. Establish `hne : τ ≠ ComplexEmbedding.conjugate τ` using `fun h => IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h.symm)`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `h3 : ({e, τ, ComplexEmbedding.conjugate τ} : Finset (K →+* ℂ)).card = 3`.

Rewrite using `[Finset.card_insert_of_notMem (by simp [h.1, h.2]), Finset.card_pair hne]`. Use `Finset.card_le_univ ({e, τ, ComplexEmbedding.conjugate τ} : Finset (K →+* ℂ))` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem emb_two {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    (τ e : K →+* ℂ) : e = τ ∨ e = ComplexEmbedding.conjugate τ := by
  classical
  have hc : Fintype.card (K →+* ℂ) = 2 := by rw [Embeddings.card, hK]
  have hne : τ ≠ ComplexEmbedding.conjugate τ := fun h =>
    IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h.symm)
  by_contra h
  push Not at h
  have h3 : ({e, τ, ComplexEmbedding.conjugate τ} : Finset (K →+* ℂ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h.1, h.2]), Finset.card_pair hne]
  have := Finset.card_le_univ ({e, τ, ComplexEmbedding.conjugate τ} : Finset (K →+* ℂ))
  omega

/- English proof (translation)
Establish `: IsAlgClosure K' Ω` using `⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K'⟩`. Establish `: Algebra.IsQuadraticExtension ℚ K'` using `{ toFree := inferInstance, finrank_eq_two' := hdeg }`. Establish `: Normal ℚ K'` using `Algebra.IsQuadraticExtension.normal ℚ K'`. Establish `: IsGalois ℚ Ω` using `IsAlgClosure.isGalois ℚ Ω`. Assume the negation of the conclusion as `hne`.

Take `⟨g, hg⟩ : ∃ g : G ℚ Ω, g ∉ K'.fixingSubgroup` from `by by_contra! h`. Establish `h2` using `IntermediateField.finrank_eq_fixingSubgroup_index (L := K')`. Rewrite `h2` using `[show K'.fixingSubgroup = ⊤ from eq_top_iff.2 fun g _ => h g, Subgroup.index_top, hdeg]`. Evaluate the numerical expressions using `at h2`. Set `r : K' ≃ₐ[ℚ] K'` to `g.restrictNormal K'`.

Establish `hr' : ∀ x : K', algebraMap K' Ω (r x) = g (algebraMap K' Ω x)` using `fun x => AlgEquiv.restrictNormal_commutes g K' x`. Establish `hkey : ∀ y : K', j' (algebraMap K' (w.adicCompletion K') y) = j (algebraMap K' (w.adicCompletion K') (r y))`. Set `ψ : K' →+* Qbar l` to `j.comp (algebraMap K' (w.adicCompletion K'))`. Set `ψ' : K' →+* Qbar l` to `j'.comp (algebraMap K' (w.adicCompletion K'))`. Set `ψr : K' →+* Qbar l` to `ψ.comp (r : K' →+* K')`.

Establish `h12 : ψ ≠ ψ'`. Introduce `h`. Apply `hne` to reduce the goal to its premises. Apply `DFunLike.coe_injective` to reduce the goal to its premises. Use `(HeightOneSpectrum.denseRange_algebraMap K' w).equalizer hj hj' ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `k`. Conclude with `DFunLike.congr_fun h k`. Establish `h13 : ψ ≠ ψr`. Introduce `h`. Apply `hg` to reduce the goal to its premises.

Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Establish `e` using `ψ.injective (show ψ ⟨x, hx⟩ = ψ (r ⟨x, hx⟩) from DFunLike.congr_fun h ⟨x, hx⟩)`. Establish `e2` using `hr' ⟨x, hx⟩`. Rewrite `e2` using `[← e]`.

Conclude with `e2.symm`. Assume the negation of the conclusion as `hne3`. Establish `h23 : ψ' ≠ ψr` using `fun h => hne3 fun y => DFunLike.congr_fun h y`. Establish `inj : ∀ φ φ' : K' →+* Qbar l, φ.toRatAlgHom = φ'.toRatAlgHom → φ = φ'` using `fun φ φ' h => by`. Use extensionality with `x`.

Conclude with `DFunLike.congr_fun h x`. Set `f : Fin 3 → (K' →ₐ[ℚ] Qbar l)` to `![ψ.toRatAlgHom, ψ'.toRatAlgHom, ψr.toRatAlgHom]`. Establish `hf : Function.Injective f`. Introduce `i k hik`. Apply the tactic sequence `fin_cases i <;> fin_cases k <;> first`.

Consider the case `rfl`. Consider the case `exact absurd (inj _ _ hik) h12 | exact absurd (inj _ _ hik).symm h12`. Consider the case `exact absurd (inj _ _ hik) h13 | exact absurd (inj _ _ hik).symm h13`. Consider the case `exact absurd (inj _ _ hik) h23 | exact absurd (inj _ _ hik).symm h23`. Establish `h3` using `Nat.card_le_card_of_injective f hf`.

Establish `h4` using `card_algHom_le_finrank ℚ K' (Qbar l)`. Rewrite `h3` using `[Nat.card_eq_fintype_card, Fintype.card_fin]`. Rewrite `h4` using `[hdeg]`. Use linear arithmetic over natural numbers and integers. Establish `hval : ∀ y : Ω, (g⁻¹ • A).valuation y < 1 ↔ A.valuation (g y) < 1` using `fun y => by`.

Rewrite using `[ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff', ValuationSubring.mem_inv_pointwise_smul_iff, ValuationSubring.mem_inv_pointwise_smul_iff, AlgEquiv.smul_def, AlgEquiv.smul_def, map_inv₀, map_eq_zero_iff _ g.injective]`. Establish `hB1 : (g⁻¹ • A).valuation (l : Ω) < 1`. Rewrite using `[hval, map_natCast]`. Conclude with `hA`. Establish `hBt : g⁻¹ • A ≠ ⊤` using `fun h => ((UpperTheory.V.Base.places K' Ω l _).2.1 h).2 hB1`.

Take `⟨w', hw'⟩` from `(UpperTheory.V.Base.places K' Ω l _).1 hBt`. Establish `hne' : w' ≠ w`. Introduce `e`. Substitute `e` using the available equality. Take `⟨h, hh⟩` from `ReciprocityTheory.Gal.exists_smul_eq_of_isPlaceOver (F := K') hw hw'`.

Apply `hg` to reduce the goal to its premises. Establish `e1 : (resQ K' h) • A = h • A`. Use extensionality with `x`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]`. Both sides reduce to the same expression.

Establish `hD : g * resQ K' h ∈ Dec (F` using `ℚ) A := by show (g * resQ K' h) • A = A`. Rewrite using `[mul_smul, e1, hh, smul_inv_smul]`. Establish `hm : resQ K' h ∈ K'.fixingSubgroup` using `(K'.mem_fixingSubgroup_iff _).2 fun x hx => h.commutes ⟨x, hx⟩`. Conclude with `(Subgroup.mul_mem_cancel_right _ hm).1 (hsplit A hA hD)`. Establish `hcop` using `Ideal.IsMaximal.coprime_of_ne w.isMaximal w'.isMaximal fun e => hne' (HeightOneSpectrum.ext e.symm)`.

Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hcop)`. Establish `h1` using `norm_lt_one_of_contEmb w j' hj' a ha`. Establish `hbB : A.valuation (g (algebraMap K' Ω (b : K'))) < 1` using `(hval _).1 ((hw' b).2 hb)`. Establish `hint : IsIntegral ℤ (r (b : K'))` using `(NumberField.RingOfIntegers.isIntegral_coe b).map ((r : K' →ₐ[ℚ] K').restrictScalars ℤ)`. Set `rb : 𝓞 K'` to `⟨r (b : K'), hint⟩`.

Establish `hrb : rb ∈ w.asIdeal` using `(hw rb).1 (by`. Rewrite using `[show algebraMap K' Ω ((rb : 𝓞 K') : K') = g (algebraMap K' Ω (b : K')) from hr' _]`. Conclude with `hbB)`. Establish `h2` using `norm_lt_one_of_contEmb w j hj rb hrb`. Establish `h2' : ‖j' (algebraMap K' (w.adicCompletion K') (algebraMap (𝓞 K') K' b))‖ < 1`.

Rewrite using `[hkey]`. Conclude with `h2`. Establish `h4` using `IsUltrametricDist.norm_add_le_max (j' (algebraMap K' (w.adicCompletion K') (algebraMap (𝓞 K') K' a))) (j' (algebraMap K' (w.adicCompletion K') (algebraMap (𝓞 K') K' b)))`. Rewrite `h4` using `[← map_add, ← map_add, ← map_add, hab, map_one, map_one, map_one, norm_one]`. Conclude with `absurd (h4.trans_lt (max_lt h1 h2')) (lt_irrefl _)`.
-/
theorem emb_unique {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    (K' : IntermediateField ℚ Ω) [NumberField K'] (hdeg : Module.finrank ℚ K' = 2)
    (hsplit : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ K'.fixingSubgroup)
    (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) (w : HeightOneSpectrum (𝓞 K'))
    (hw : Formalism.ConjugateSelfDual.IsPlaceOver A w) (j j' : w.adicCompletion K' →+* Qbar l) (hj : Continuous j) (hj' : Continuous j') :
    j = j' := by
  have : IsAlgClosure K' Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K'⟩
  have : Algebra.IsQuadraticExtension ℚ K' := { toFree := inferInstance, finrank_eq_two' := hdeg }
  have : Normal ℚ K' := Algebra.IsQuadraticExtension.normal ℚ K'
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g : G ℚ Ω, g ∉ K'.fixingSubgroup := by
    by_contra! h
    have h2 := IntermediateField.finrank_eq_fixingSubgroup_index (L := K')
    rw [show K'.fixingSubgroup = ⊤ from eq_top_iff.2 fun g _ => h g, Subgroup.index_top, hdeg] at h2
    norm_num at h2
  let r : K' ≃ₐ[ℚ] K' := g.restrictNormal K'
  have hr' : ∀ x : K', algebraMap K' Ω (r x) = g (algebraMap K' Ω x) := fun x =>
    AlgEquiv.restrictNormal_commutes g K' x

  have hkey : ∀ y : K', j' (algebraMap K' (w.adicCompletion K') y) = j (algebraMap K' (w.adicCompletion K') (r y)) := by
    let ψ : K' →+* Qbar l := j.comp (algebraMap K' (w.adicCompletion K'))
    let ψ' : K' →+* Qbar l := j'.comp (algebraMap K' (w.adicCompletion K'))
    let ψr : K' →+* Qbar l := ψ.comp (r : K' →+* K')
    have h12 : ψ ≠ ψ' := by
      intro h
      apply hne
      apply DFunLike.coe_injective
      refine (HeightOneSpectrum.denseRange_algebraMap K' w).equalizer hj hj' ?_
      funext k
      exact DFunLike.congr_fun h k
    have h13 : ψ ≠ ψr := by
      intro h
      apply hg
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have e := ψ.injective (show ψ ⟨x, hx⟩ = ψ (r ⟨x, hx⟩) from DFunLike.congr_fun h ⟨x, hx⟩)
      have e2 := hr' ⟨x, hx⟩
      rw [← e] at e2
      exact e2.symm
    by_contra hne3
    have h23 : ψ' ≠ ψr := fun h => hne3 fun y => DFunLike.congr_fun h y
    have inj : ∀ φ φ' : K' →+* Qbar l, φ.toRatAlgHom = φ'.toRatAlgHom → φ = φ' := fun φ φ' h => by
      ext x
      exact DFunLike.congr_fun h x
    let f : Fin 3 → (K' →ₐ[ℚ] Qbar l) := ![ψ.toRatAlgHom, ψ'.toRatAlgHom, ψr.toRatAlgHom]
    have hf : Function.Injective f := by
      intro i k hik
      fin_cases i <;> fin_cases k <;> first
        | rfl
        | exact absurd (inj _ _ hik) h12 | exact absurd (inj _ _ hik).symm h12
        | exact absurd (inj _ _ hik) h13 | exact absurd (inj _ _ hik).symm h13
        | exact absurd (inj _ _ hik) h23 | exact absurd (inj _ _ hik).symm h23
    have h3 := Nat.card_le_card_of_injective f hf
    have h4 := card_algHom_le_finrank ℚ K' (Qbar l)
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h3
    rw [hdeg] at h4
    omega

  have hval : ∀ y : Ω, (g⁻¹ • A).valuation y < 1 ↔ A.valuation (g y) < 1 := fun y => by
    rw [ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff', ValuationSubring.mem_inv_pointwise_smul_iff,
      ValuationSubring.mem_inv_pointwise_smul_iff, AlgEquiv.smul_def, AlgEquiv.smul_def, map_inv₀,
      map_eq_zero_iff _ g.injective]
  have hB1 : (g⁻¹ • A).valuation (l : Ω) < 1 := by
    rw [hval, map_natCast]
    exact hA
  have hBt : g⁻¹ • A ≠ ⊤ := fun h => ((UpperTheory.V.Base.places K' Ω l _).2.1 h).2 hB1
  obtain ⟨w', hw'⟩ := (UpperTheory.V.Base.places K' Ω l _).1 hBt
  have hne' : w' ≠ w := by
    intro e
    subst e
    obtain ⟨h, hh⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_isPlaceOver (F := K') hw hw'
    apply hg
    have e1 : (resQ K' h) • A = h • A := by
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      rfl
    have hD : g * resQ K' h ∈ Dec (F := ℚ) A := by
      show (g * resQ K' h) • A = A
      rw [mul_smul, e1, hh, smul_inv_smul]
    have hm : resQ K' h ∈ K'.fixingSubgroup :=
      (K'.mem_fixingSubgroup_iff _).2 fun x hx => h.commutes ⟨x, hx⟩
    exact (Subgroup.mul_mem_cancel_right _ hm).1 (hsplit A hA hD)
  have hcop := Ideal.IsMaximal.coprime_of_ne w.isMaximal w'.isMaximal fun e => hne' (HeightOneSpectrum.ext e.symm)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hcop)
  have h1 := norm_lt_one_of_contEmb w j' hj' a ha
  have hbB : A.valuation (g (algebraMap K' Ω (b : K'))) < 1 := (hval _).1 ((hw' b).2 hb)
  have hint : IsIntegral ℤ (r (b : K')) :=
    (NumberField.RingOfIntegers.isIntegral_coe b).map ((r : K' →ₐ[ℚ] K').restrictScalars ℤ)
  let rb : 𝓞 K' := ⟨r (b : K'), hint⟩
  have hrb : rb ∈ w.asIdeal := (hw rb).1 (by
    rw [show algebraMap K' Ω ((rb : 𝓞 K') : K') = g (algebraMap K' Ω (b : K')) from hr' _]
    exact hbB)
  have h2 := norm_lt_one_of_contEmb w j hj rb hrb
  have h2' : ‖j' (algebraMap K' (w.adicCompletion K') (algebraMap (𝓞 K') K' b))‖ < 1 := by
    rw [hkey]
    exact h2
  have h4 := IsUltrametricDist.norm_add_le_max
    (j' (algebraMap K' (w.adicCompletion K') (algebraMap (𝓞 K') K' a)))
    (j' (algebraMap K' (w.adicCompletion K') (algebraMap (𝓞 K') K' b)))
  rw [← map_add, ← map_add, ← map_add, hab, map_one, map_one, map_one, norm_one] at h4
  exact absurd (h4.trans_lt (max_lt h1 h2')) (lt_irrefl _)

end TwistIne

open TwistIne in
/- English proof (translation)
Introduce `Ω _ _ _ l _ ι K' _ hdeg htc hdisc hsplit cc κ₀ hT A hA`. Use `htc` as an intermediate fact. Establish `: IsAlgClosure K' Ω` using `⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K'⟩`. Take `⟨art, Y, a, τ, hart, -, hL, ha1, ha0, hYu⟩` from `hT.alg`. Establish `hAt : A ≠ ⊤` using `fun h => ((UpperTheory.V.Base.places K' Ω l A).2.1 h).2 hA`.

Take `⟨w, hw⟩` from `(UpperTheory.V.Base.places K' Ω l A).1 hAt`. Establish `hdw : ((discr K' : ℤ) : 𝓞 K') ∉ w.asIdeal`. Introduce `hd`. Establish `h1 : A.valuation ((discr K' : ℤ) : Ω) < 1` using `by simpa using (hw _).2 hd`. Conclude with `not_lt_of_not_dvd A (Fact.out : l.Prime) hA hdisc h1`.

Establish `hYw` using `hYu w hdw`. Take `⟨μ, hμ, hM⟩` from `hart.exists_isLAdicOf ι (GlobalTheory.Published.CharAboveModel.absPow_isAlgPos K' 1)`. Establish `hμe : μ = cycBar K' Ω l ^ 1` using `GlobalTheory.Published.CharAboveModel.eq_cyc_pow hart hμ hM`. Rewrite `hμe` using `[pow_one]`. Substitute `hμe` using the available equality.

Establish `hval : ∀ σ ∈ Ine (F` using `K') A, ∃ x : (w.adicCompletion K')ˣ, ((κ₀ σ : (Qbar l)ˣ) : Qbar l) = locPow ι a w (x : w.adicCompletion K') ∧ ((cycBar K' Ω l σ : (Qbar l)ˣ) : Qbar l) = locPow ι (fun _ => ((1 : ℕ) : ℤ)) w (x : w.adicCompletion K') := by`. Introduce `σ hσ`. Take `⟨x, hx, e⟩` from `(hart.ine w A hw (toAb K' Ω σ)).2 ⟨σ, hσ, rfl⟩`. Use `⟨x, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hL.loc x σ e, hYw x hx, Units.val_one, map_one, one_mul]`.

Rewrite using `[hM.loc x σ e, (GlobalTheory.HeckeGal.Model.absPow_isAbsPow K' ((1 : ℕ) : ℝ)).1 w x hx, Units.val_one, map_one, one_mul]`. Use `haveI : Subsingleton {j : w.adicCompletion K' →+* Qbar l // Continuous j} := ⟨fun j j' => Subtype.ext (emb_unique K' hdeg hsplit A hA w hw j.1 j'.1 j.2 j'.2)⟩`. Break down `isEmpty_or_nonempty {j : w.adicCompletion K' →+* Qbar l // Continuous j} with hJ | hJ` into its components or cases. Use `right`. Introduce `σ hσ`.

Take `⟨x, h1, -⟩` from `hval σ hσ`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[h1, Units.val_one]`. Unfold `locPow`. Conclude with `finprod_of_isEmpty _`.

Take `⟨j0⟩` from `hJ`. Establish `hlp : ∀ (n : (K' →+* ℂ) → ℤ) (y : w.adicCompletion K'), locPow ι n w y = j0.1 y ^ n ((ι.toRingHom.comp j0.1).comp (algebraMap K' (w.adicCompletion K')))` using `fun n y => by haveI : Unique {j : w.adicCompletion K' →+* Qbar l // Continuous j} := uniqueOfSubsingleton j0`. Unfold `locPow`. Rewrite using `[finprod_unique, Subsingleton.elim (default : {j : w.adicCompletion K' →+* Qbar l // Continuous j}) j0]`. Break down `emb_two hdeg τ ((ι.toRingHom.comp j0.1).comp (algebraMap K' (w.adicCompletion K'))) with he | he` into its components or cases.

Use `left`. Introduce `σ hσ`. Take `⟨x, h1, h2⟩` from `hval σ hσ`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_inv_eq_inv_val, h1, h2, hlp, hlp, he, ha1]`.

Simplify using the standard rewrite rules. Use `right`. Introduce `σ hσ`. Take `⟨x, h1, -⟩` from `hval σ hσ`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[h1, hlp, he, ha0, zpow_zero, Units.val_one]`.
-/
theorem twistIne : TwistIne := by
  intro Ω _ _ _ l _ ι K' _ hdeg htc hdisc hsplit cc κ₀ hT A hA
  have := htc
  have : IsAlgClosure K' Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K'⟩
  obtain ⟨art, Y, a, τ, hart, -, hL, ha1, ha0, hYu⟩ := hT.alg
  have hAt : A ≠ ⊤ := fun h => ((UpperTheory.V.Base.places K' Ω l A).2.1 h).2 hA
  obtain ⟨w, hw⟩ := (UpperTheory.V.Base.places K' Ω l A).1 hAt
  have hdw : ((discr K' : ℤ) : 𝓞 K') ∉ w.asIdeal := by
    intro hd
    have h1 : A.valuation ((discr K' : ℤ) : Ω) < 1 := by simpa using (hw _).2 hd
    exact not_lt_of_not_dvd A (Fact.out : l.Prime) hA hdisc h1
  have hYw := hYu w hdw
  obtain ⟨μ, hμ, hM⟩ := hart.exists_isLAdicOf ι (GlobalTheory.Published.CharAboveModel.absPow_isAlgPos K' 1)
  have hμe : μ = cycBar K' Ω l ^ 1 := GlobalTheory.Published.CharAboveModel.eq_cyc_pow hart hμ hM
  rw [pow_one] at hμe
  subst hμe
  have hval : ∀ σ ∈ Ine (F := K') A, ∃ x : (w.adicCompletion K')ˣ,
      ((κ₀ σ : (Qbar l)ˣ) : Qbar l) = locPow ι a w (x : w.adicCompletion K') ∧
        ((cycBar K' Ω l σ : (Qbar l)ˣ) : Qbar l) = locPow ι (fun _ => ((1 : ℕ) : ℤ)) w (x : w.adicCompletion K') := by
    intro σ hσ
    obtain ⟨x, hx, e⟩ := (hart.ine w A hw (toAb K' Ω σ)).2 ⟨σ, hσ, rfl⟩
    refine ⟨x, ?_, ?_⟩
    · rw [hL.loc x σ e, hYw x hx, Units.val_one, map_one, one_mul]
    · rw [hM.loc x σ e, (GlobalTheory.HeckeGal.Model.absPow_isAbsPow K' ((1 : ℕ) : ℝ)).1 w x hx, Units.val_one, map_one, one_mul]
  haveI : Subsingleton {j : w.adicCompletion K' →+* Qbar l // Continuous j} :=
    ⟨fun j j' => Subtype.ext (emb_unique K' hdeg hsplit A hA w hw j.1 j'.1 j.2 j'.2)⟩
  rcases isEmpty_or_nonempty {j : w.adicCompletion K' →+* Qbar l // Continuous j} with hJ | hJ
  · right
    intro σ hσ
    obtain ⟨x, h1, -⟩ := hval σ hσ
    apply Units.ext
    rw [h1, Units.val_one]
    unfold locPow
    exact finprod_of_isEmpty _
  · obtain ⟨j0⟩ := hJ
    have hlp : ∀ (n : (K' →+* ℂ) → ℤ) (y : w.adicCompletion K'), locPow ι n w y =
        j0.1 y ^ n ((ι.toRingHom.comp j0.1).comp (algebraMap K' (w.adicCompletion K'))) := fun n y => by
      haveI : Unique {j : w.adicCompletion K' →+* Qbar l // Continuous j} := uniqueOfSubsingleton j0
      unfold locPow
      rw [finprod_unique, Subsingleton.elim (default : {j : w.adicCompletion K' →+* Qbar l // Continuous j}) j0]
    rcases emb_two hdeg τ ((ι.toRingHom.comp j0.1).comp (algebraMap K' (w.adicCompletion K'))) with he | he
    · left
      intro σ hσ
      obtain ⟨x, h1, h2⟩ := hval σ hσ
      apply Units.ext
      rw [Units.val_inv_eq_inv_val, h1, h2, hlp, hlp, he, ha1]
      simp
    · right
      intro σ hσ
      obtain ⟨x, h1, -⟩ := hval σ hσ
      apply Units.ext
      rw [h1, hlp, he, ha0, zpow_zero, Units.val_one]

end UpperTheory.V.Cu2

end
