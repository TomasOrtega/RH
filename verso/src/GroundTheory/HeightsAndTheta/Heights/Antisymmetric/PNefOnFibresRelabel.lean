import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.StatementsNefRelabel
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

section RingEquivTransport

variable {A A' : Type*} [CommRing A] [CommRing A'] (σ : A ≃+* A')

/- English proof (translation)
Rewrite using `[← Ideal.mem_comap, Ideal.comap_map_of_bijective σ σ.bijective]`.
-/
theorem mem_map_ringEquiv_iff (I : Ideal A) (x : A) : σ x ∈ I.map σ ↔ x ∈ I := by
  rw [← Ideal.mem_comap, Ideal.comap_map_of_bijective σ σ.bijective]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hV`. Rewrite using `[← Ideal.comap_map_of_bijective σ σ.bijective (I := V)]`. Conclude with `Ideal.comap_isPrime σ (V.map σ)`. Introduce `hV`.

Conclude with `Ideal.map_isPrime_of_equiv σ`.
-/
theorem isPrime_map_ringEquiv_iff (V : Ideal A) : (V.map σ).IsPrime ↔ V.IsPrime := by
  constructor
  · intro hV
    rw [← Ideal.comap_map_of_bijective σ σ.bijective (I := V)]
    exact Ideal.comap_isPrime σ (V.map σ)
  · intro hV
    exact Ideal.map_isPrime_of_equiv σ

/- English proof (translation)
Introduce `I J hIJ` and use `by rw [← Ideal.comap_map_of_bijective σ σ.bijective (I := I), hIJ, Ideal.comap_map_of_bijective σ σ.bijective]`.
-/
theorem map_ringEquiv_injective : Function.Injective (Ideal.map σ : Ideal A → Ideal A') :=
  fun I J hIJ => by
    rw [← Ideal.comap_map_of_bijective σ σ.bijective (I := I), hIJ,
      Ideal.comap_map_of_bijective σ σ.bijective]

/- English proof (translation)
The claim follows from `(ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv V (V.map σ) σ rfl)).symm`.
-/
theorem ringKrullDim_quotient_map (V : Ideal A) :
    ringKrullDim (A' ⧸ V.map σ) = ringKrullDim (A ⧸ V) :=
  (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv V (V.map σ) σ rfl)).symm

/- English proof (translation)
The claim follows from `((Ideal.quotientEquiv I (I.map σ) σ rfl).toAddEquiv.toIntLinearEquiv.length_eq).symm`.
-/
theorem length_int_quotient_map (I : Ideal A) :
    Module.length ℤ (A' ⧸ I.map σ) = Module.length ℤ (A ⧸ I) :=
  ((Ideal.quotientEquiv I (I.map σ) σ rfl).toAddEquiv.toIntLinearEquiv.length_eq).symm

/- English proof (translation)
Use `Ideal.minimalPrimes_map_of_surjective (f := (σ : A →+* A')) σ.surjective I` as an intermediate fact. Rewrite `this` using `[RingHom.ker_coe_equiv, sup_bot_eq]`. Conclude with `this`.
-/
theorem minimalPrimes_map_ringEquiv (I : Ideal A) :
    (I.map σ).minimalPrimes = Ideal.map σ '' I.minimalPrimes := by
  have := Ideal.minimalPrimes_map_of_surjective (f := (σ : A →+* A')) σ.surjective I
  rw [RingHom.ker_coe_equiv, sup_bot_eq] at this
  exact this

/- English proof (translation)
The claim follows from `Ideal.mem_primeCompl_iff.2 fun hs => Ideal.mem_primeCompl_iff.1 s.2 ((mem_map_ringEquiv_iff σ V s).1 hs)`.
-/
theorem map_mem_primeCompl (V : Ideal A) [V.IsPrime] [(V.map σ).IsPrime] (s : V.primeCompl) :
    σ s ∈ (V.map σ).primeCompl :=
  Ideal.mem_primeCompl_iff.2 fun hs => Ideal.mem_primeCompl_iff.1 s.2 ((mem_map_ringEquiv_iff σ V s).1 hs)

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[Submonoid.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, rfl⟩`. Conclude with `map_mem_primeCompl σ V ⟨s, hs⟩`.

Introduce `hx`. Use `⟨σ.symm x, Ideal.mem_primeCompl_iff.2 fun h' => Ideal.mem_primeCompl_iff.1 hx ?_, by simp⟩` and prove the remaining obligations. Simplify using `using (mem_map_ringEquiv_iff σ V (σ.symm x)).2 h'`.
-/
theorem primeCompl_map_ringEquiv (V : Ideal A) [V.IsPrime] [(V.map σ).IsPrime] :
    V.primeCompl.map σ.toMonoidHom = (V.map σ).primeCompl := by
  ext x
  rw [Submonoid.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact map_mem_primeCompl σ V ⟨s, hs⟩
  · intro hx
    refine ⟨σ.symm x, Ideal.mem_primeCompl_iff.2 fun h' => Ideal.mem_primeCompl_iff.1 hx ?_, by simp⟩
    simpa using (mem_map_ringEquiv_iff σ V (σ.symm x)).2 h'

def locRingEquiv (V : Ideal A) [V.IsPrime] [(V.map σ).IsPrime] :
    Localization.AtPrime V ≃+* Localization.AtPrime (V.map σ) :=
  IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime V) (Localization.AtPrime (V.map σ)) σ
    (primeCompl_map_ringEquiv σ V)

/- English proof (translation)
Rewrite using `[Localization.mk_eq_mk'_apply, Localization.mk_eq_mk'_apply, locRingEquiv, IsLocalization.ringEquivOfRingEquiv_mk']`.
-/
theorem locRingEquiv_mk (V : Ideal A) [V.IsPrime] [(V.map σ).IsPrime] (a : A) (t : V.primeCompl) :
    locRingEquiv σ V (Localization.mk a t) = Localization.mk (σ a) ⟨σ t, map_mem_primeCompl σ V t⟩ := by
  rw [Localization.mk_eq_mk'_apply, Localization.mk_eq_mk'_apply, locRingEquiv,
    IsLocalization.ringEquivOfRingEquiv_mk']

def quotEquivMap (J : Ideal A) : A ⧸ J ≃+* A' ⧸ J.map σ :=
  Ideal.quotientEquiv J (J.map σ) σ rfl

/- English proof (translation)
Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul]`. Both sides reduce to the same expression.
-/
theorem quotEquivMap_smul (J : Ideal A) (a : A) (m : A ⧸ J) :
    quotEquivMap σ J (a • m) = σ a • quotEquivMap σ J m := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

section LocLength

variable (J V : Ideal A) [V.IsPrime] [(V.map σ).IsPrime]

def locQuotMap :
    LocalizedModule V.primeCompl (A ⧸ J) → LocalizedModule (V.map σ).primeCompl (A' ⧸ J.map σ) :=
  fun x => x.liftOn (fun p => LocalizedModule.mk (quotEquivMap σ J p.1)
      ⟨σ p.2, map_mem_primeCompl σ V p.2⟩) (by
    rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
    rw [LocalizedModule.mk_eq]
    refine ⟨⟨σ u, map_mem_primeCompl σ V u⟩, ?_⟩
    have := congrArg (quotEquivMap σ J) hu
    simpa only [Submonoid.smul_def, quotEquivMap_smul] using this)

/- English proof (translation)
Rewrite using `[locQuotMap, LocalizedModule.liftOn_mk]`.
-/
theorem locQuotMap_mk (m : A ⧸ J) (s : V.primeCompl) :
    locQuotMap σ J V (LocalizedModule.mk m s) =
      LocalizedModule.mk (quotEquivMap σ J m) ⟨σ s, map_mem_primeCompl σ V s⟩ := by
  rw [locQuotMap, LocalizedModule.liftOn_mk]

def locQuotSemilinear :
    LocalizedModule V.primeCompl (A ⧸ J) →ₛₗ[(locRingEquiv σ V : Localization.AtPrime V →+*
      Localization.AtPrime (V.map σ))] LocalizedModule (V.map σ).primeCompl (A' ⧸ J.map σ) where
  toFun := locQuotMap σ J V
  map_add' x y := by
    induction x using LocalizedModule.induction_on with | h m s => ?_
    induction y using LocalizedModule.induction_on with | h m' s' => ?_
    rw [LocalizedModule.mk_add_mk, locQuotMap_mk, locQuotMap_mk, locQuotMap_mk,
      LocalizedModule.mk_add_mk]
    simp only [Submonoid.smul_def, map_add, quotEquivMap_smul]
    congr 1
    ext
    simp
  map_smul' r x := by
    induction r using Localization.induction_on with | H p => ?_
    obtain ⟨a, t⟩ := p
    induction x using LocalizedModule.induction_on with | h m s => ?_
    show locQuotMap σ J V _ = (locRingEquiv σ V (Localization.mk a t)) • locQuotMap σ J V _
    rw [LocalizedModule.mk_smul_mk, locQuotMap_mk, locQuotMap_mk, locRingEquiv_mk,
      LocalizedModule.mk_smul_mk, quotEquivMap_smul]
    congr 1
    ext
    simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem locQuotSemilinear_apply (x : LocalizedModule V.primeCompl (A ⧸ J)) :
    locQuotSemilinear σ J V x = locQuotMap σ J V x := rfl

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Proceed by induction on `x using LocalizedModule.induction_on with | h m s => ?_`. Rewrite `hx` using `[locQuotSemilinear_apply, locQuotMap_mk, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]`. Take `⟨u, hu⟩` from `hx`.

Rewrite `hu` using `[smul_zero, smul_zero, one_smul, Submonoid.smul_def]`. Establish `hu' : σ.symm u ∈ V.primeCompl` using `Ideal.mem_primeCompl_iff.2 fun h' => Ideal.mem_primeCompl_iff.1 u.2 (by simpa using (mem_map_ringEquiv_iff σ V _).2 h')`. Rewrite using `[← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]`. Use `⟨⟨σ.symm u, hu'⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_zero, smul_zero, one_smul, Submonoid.smul_def]`.

Apply `(quotEquivMap σ J).injective` to reduce the goal to its premises. Rewrite using `[quotEquivMap_smul, map_zero, RingEquiv.apply_symm_apply]`. Conclude with `hu`.
-/
theorem locQuotSemilinear_injective : Function.Injective (locQuotSemilinear σ J V) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using LocalizedModule.induction_on with | h m s => ?_
  rw [locQuotSemilinear_apply, locQuotMap_mk, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hx
  obtain ⟨u, hu⟩ := hx
  rw [smul_zero, smul_zero, one_smul, Submonoid.smul_def] at hu
  have hu' : σ.symm u ∈ V.primeCompl := Ideal.mem_primeCompl_iff.2 fun h' =>
    Ideal.mem_primeCompl_iff.1 u.2 (by simpa using (mem_map_ringEquiv_iff σ V _).2 h')
  rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
  refine ⟨⟨σ.symm u, hu'⟩, ?_⟩
  rw [smul_zero, smul_zero, one_smul, Submonoid.smul_def]
  apply (quotEquivMap σ J).injective
  rw [quotEquivMap_smul, map_zero, RingEquiv.apply_symm_apply]
  exact hu

/- English proof (translation)
Introduce `x`. Proceed by induction on `x using LocalizedModule.induction_on with | h m s => ?_`. Establish `hs : σ.symm s ∈ V.primeCompl` using `Ideal.mem_primeCompl_iff.2 fun h' => Ideal.mem_primeCompl_iff.1 s.2 (by simpa using (mem_map_ringEquiv_iff σ V _).2 h')`. Use `⟨LocalizedModule.mk ((quotEquivMap σ J).symm m) ⟨σ.symm s, hs⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[locQuotSemilinear_apply, locQuotMap_mk, RingEquiv.apply_symm_apply]`.

Use `congr 1`. Use `ext`. Simplify using the standard rewrite rules.
-/
theorem locQuotSemilinear_surjective : Function.Surjective (locQuotSemilinear σ J V) := by
  intro x
  induction x using LocalizedModule.induction_on with | h m s => ?_
  have hs : σ.symm s ∈ V.primeCompl := Ideal.mem_primeCompl_iff.2 fun h' =>
    Ideal.mem_primeCompl_iff.1 s.2 (by simpa using (mem_map_ringEquiv_iff σ V _).2 h')
  refine ⟨LocalizedModule.mk ((quotEquivMap σ J).symm m) ⟨σ.symm s, hs⟩, ?_⟩
  rw [locQuotSemilinear_apply, locQuotMap_mk, RingEquiv.apply_symm_apply]
  congr 1
  ext
  simp

/- English proof (translation)
Establish `: RingHomSurjective (locRingEquiv σ V : Localization.AtPrime V →+* Localization.AtPrime (V.map σ))` using `⟨(locRingEquiv σ V).surjective⟩`. Apply `WithBot.coe_injective` to reduce the goal to its premises. Rewrite using `[Module.coe_length, Module.coe_length]`. Conclude with `(Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective (locQuotSemilinear σ J V) ⟨locQuotSemilinear_injective σ J V, locQuotSemilinear_surjective σ J V⟩)).symm`.
-/
theorem length_localizedModule_quotient_map :
    Module.length (Localization.AtPrime (V.map σ))
        (LocalizedModule (V.map σ).primeCompl (A' ⧸ J.map σ)) =
      Module.length (Localization.AtPrime V) (LocalizedModule V.primeCompl (A ⧸ J)) := by
  have : RingHomSurjective (locRingEquiv σ V : Localization.AtPrime V →+*
      Localization.AtPrime (V.map σ)) := ⟨(locRingEquiv σ V).surjective⟩
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact (Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective
    (locQuotSemilinear σ J V) ⟨locQuotSemilinear_injective σ J V,
      locQuotSemilinear_surjective σ J V⟩)).symm

end LocLength

end RingEquivTransport

/- English proof (translation)
Substitute `e` using the available equality. Establish `: q = p` using `funext fun x => propext (hpq x)`. Substitute `this` using the available equality. Both sides reduce to the same expression.
-/
theorem choose_eq_cast {α β : Type} (e : α = β) {p : α → Prop} {q : β → Prop}
    (hp : ∃ x, p x) (hq : ∃ y, q y) (hpq : ∀ x, q (cast e x) ↔ p x) :
    Classical.choose hq = cast e (Classical.choose hp) := by
  subst e
  have : q = p := funext fun x => propext (hpq x)
  subst this
  rfl

section Relabel

set_option linter.unusedSectionVars false

variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))

def relabelRingEquiv : MRing ι ≃+* MRing ι' :=
  (MvPolynomial.renameEquiv ℤ (relabelBlocks ε h)).toRingEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem relabelRingEquiv_apply (f : MRing ι) :
    relabelRingEquiv ε h f = rename (relabelBlocks ε h) f := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem relabelRingEquiv_symm_apply (f : MRing ι') :
    (relabelRingEquiv ε h).symm f = rename (relabelBlocks ε h).symm f := rfl

/- English proof (translation)
Rewrite using `[relabelRingEquiv_apply, rename_X]`. Both sides reduce to the same expression.
-/
theorem relabelRingEquiv_X (k : K) (i : ι k) :
    relabelRingEquiv ε h (X ⟨k, i⟩) = X ⟨ε k, cast (h k) i⟩ := by
  rw [relabelRingEquiv_apply, rename_X]
  rfl

/- English proof (translation)
Rewrite using `[← relabelRingEquiv_X, mem_map_ringEquiv_iff]`.
-/
theorem X_mem_map_relabel_iff (V : Ideal (MRing ι)) (k : K) (i : ι k) :
    (X ⟨ε k, cast (h k) i⟩ : MRing ι') ∈ V.map (relabelRingEquiv ε h) ↔ (X ⟨k, i⟩ : MRing ι) ∈ V := by
  rw [← relabelRingEquiv_X, mem_map_ringEquiv_iff]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hV k`. Take `⟨i, hi⟩` from `hV (ε k)`. Use `⟨cast (h k).symm i, fun hmem => hi ?_⟩` and prove the remaining obligations. Use `(X_mem_map_relabel_iff ε h V k _).2 hmem` as an intermediate fact.

Simplify using `using this`. Introduce `hV k'`. Take `⟨k, rfl⟩` from `ε.surjective k'`. Take `⟨i, hi⟩` from `hV k`. Conclude with `⟨cast (h k) i, fun hmem => hi ((X_mem_map_relabel_iff ε h V k i).1 hmem)⟩`.
-/
theorem isRelevant_map_relabel_iff (V : Ideal (MRing ι)) :
    IsRelevant (V.map (relabelRingEquiv ε h)) ↔ IsRelevant V := by
  constructor
  · intro hV k
    obtain ⟨i, hi⟩ := hV (ε k)
    refine ⟨cast (h k).symm i, fun hmem => hi ?_⟩
    have := (X_mem_map_relabel_iff ε h V k _).2 hmem
    simpa using this
  · intro hV k'
    obtain ⟨k, rfl⟩ := ε.surjective k'
    obtain ⟨i, hi⟩ := hV k
    exact ⟨cast (h k) i, fun hmem => hi ((X_mem_map_relabel_iff ε h V k i).1 hmem)⟩

/- English proof (translation)
Introduce `m hm k'`. Rewrite `hm` using `[relabelRingEquiv_apply, support_rename_of_injective (relabelBlocks ε h).injective, Finset.mem_image]`. Take `⟨m₀, hm₀, rfl⟩` from `hm`. Take `⟨k, rfl⟩` from `ε.surjective k'`. Simplify using `only`.

Rewrite using `[ε.symm_apply_apply, ← hf m₀ hm₀ k, ← (Equiv.cast (h k)).sum_comp]`. Conclude with `Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_apply (relabelBlocks ε h).injective m₀ ⟨k, i⟩`.
-/
theorem isMultiHomog_relabel {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d) :
    IsMultiHomog (relabelRingEquiv ε h f) (fun k' => d (ε.symm k')) := by
  classical
  intro m hm k'
  rw [relabelRingEquiv_apply, support_rename_of_injective (relabelBlocks ε h).injective,
    Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  obtain ⟨k, rfl⟩ := ε.surjective k'
  dsimp only
  rw [ε.symm_apply_apply, ← hf m₀ hm₀ k, ← (Equiv.cast (h k)).sum_comp]
  exact Finset.sum_congr rfl fun i _ =>
    Finsupp.mapDomain_apply (relabelBlocks ε h).injective m₀ ⟨k, i⟩

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[relabelRingEquiv_symm_apply, support_rename_of_injective (relabelBlocks ε h).symm.injective, Finset.mem_image]`. Take `⟨m₀, hm₀, rfl⟩` from `hm`. Simplify using `only`. Rewrite using `[← hg m₀ hm₀ (ε k), ← (Equiv.cast (h k)).sum_comp]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `Finsupp.mapDomain_apply (relabelBlocks ε h).symm.injective m₀ (relabelBlocks ε h ⟨k, i⟩)` as an intermediate fact. Rewrite `this` using `[Equiv.symm_apply_apply]`. Conclude with `this`.
-/
theorem isMultiHomog_relabel_symm {g : MRing ι'} {d : K' → ℕ} (hg : IsMultiHomog g d) :
    IsMultiHomog ((relabelRingEquiv ε h).symm g) (fun k => d (ε k)) := by
  classical
  intro m hm k
  rw [relabelRingEquiv_symm_apply, support_rename_of_injective (relabelBlocks ε h).symm.injective,
    Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  dsimp only
  rw [← hg m₀ hm₀ (ε k), ← (Equiv.cast (h k)).sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := Finsupp.mapDomain_apply (relabelBlocks ε h).symm.injective m₀ (relabelBlocks ε h ⟨k, i⟩)
  rw [Equiv.symm_apply_apply] at this
  exact this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨S, hS, hVS⟩`. Use `⟨(relabelRingEquiv ε h).symm '' S, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Take `⟨d, hd⟩` from `hS g hg`.

Conclude with `⟨_, isMultiHomog_relabel_symm ε h hd⟩`. Rewrite using `[← Ideal.map_span, ← hVS, Ideal.map_symm, Ideal.comap_map_of_bijective _ (relabelRingEquiv ε h).bijective]`. Introduce and unpack `⟨S, hS, rfl⟩`. Use `⟨relabelRingEquiv ε h '' S, ?_, Ideal.map_span _ _⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`.

Take `⟨d, hd⟩` from `hS f hf`. Conclude with `⟨_, isMultiHomog_relabel ε h hd⟩`.
-/
theorem isMultiHomogIdeal_map_relabel_iff (V : Ideal (MRing ι)) :
    IsMultiHomogIdeal (V.map (relabelRingEquiv ε h)) ↔ IsMultiHomogIdeal V := by
  constructor
  · rintro ⟨S, hS, hVS⟩
    refine ⟨(relabelRingEquiv ε h).symm '' S, ?_, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨d, hd⟩ := hS g hg
      exact ⟨_, isMultiHomog_relabel_symm ε h hd⟩
    · rw [← Ideal.map_span, ← hVS, Ideal.map_symm,
        Ideal.comap_map_of_bijective _ (relabelRingEquiv ε h).bijective]
  · rintro ⟨S, hS, rfl⟩
    refine ⟨relabelRingEquiv ε h '' S, ?_, Ideal.map_span _ _⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨d, hd⟩ := hS f hf
    exact ⟨_, isMultiHomog_relabel ε h hd⟩

/- English proof (translation)
Unfold `IsMultiProjPrime`. Rewrite using `[isPrime_map_ringEquiv_iff, isMultiHomogIdeal_map_relabel_iff, isRelevant_map_relabel_iff]`.
-/
theorem isMultiProjPrime_map_relabel_iff (V : Ideal (MRing ι)) :
    IsMultiProjPrime (V.map (relabelRingEquiv ε h)) ↔ IsMultiProjPrime V := by
  unfold IsMultiProjPrime
  rw [isPrime_map_ringEquiv_iff, isMultiHomogIdeal_map_relabel_iff, isRelevant_map_relabel_iff]

/- English proof (translation)
Establish `hC : (V.map (relabelRingEquiv ε h)).comap (C : ℤ →+* MRing ι') = V.comap (C : ℤ →+* MRing ι)`. Use extensionality with `n`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, ← mem_map_ringEquiv_iff (relabelRingEquiv ε h) V, relabelRingEquiv_apply, rename_C]`. Simplify using `only [charOf, hC]`.
-/
theorem charOf_map_relabel (V : Ideal (MRing ι)) :
    charOf (V.map (relabelRingEquiv ε h)) = charOf V := by
  have hC : (V.map (relabelRingEquiv ε h)).comap (C : ℤ →+* MRing ι') =
      V.comap (C : ℤ →+* MRing ι) := by
    ext n
    rw [Ideal.mem_comap, Ideal.mem_comap, ← mem_map_ringEquiv_iff (relabelRingEquiv ε h) V,
      relabelRingEquiv_apply, rename_C]
  simp only [charOf, hC]

/- English proof (translation)
Establish `hsup : V.map (relabelRingEquiv ε h) ⊔ Ideal.span {relabelRingEquiv ε h s} = (V ⊔ Ideal.span {s}).map (relabelRingEquiv ε h)`. Rewrite using `[Ideal.map_sup, Ideal.map_span, Set.image_singleton]`. Use extensionality with `W'`. Simplify using `only [divSupp, Set.mem_ofPred_eq, Set.mem_image, hsup, minimalPrimes_map_ringEquiv]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨W, hW, rfl⟩, hrel⟩`. Conclude with `⟨W, ⟨hW, (isRelevant_map_relabel_iff ε h W).1 hrel⟩, rfl⟩`. Introduce and unpack `⟨W, ⟨hW, hrel⟩, rfl⟩`. Conclude with `⟨⟨W, hW, rfl⟩, (isRelevant_map_relabel_iff ε h W).2 hrel⟩`.
-/
theorem divSupp_map_relabel (V : Ideal (MRing ι)) (s : MRing ι) :
    divSupp (V.map (relabelRingEquiv ε h)) (relabelRingEquiv ε h s) =
      Ideal.map (relabelRingEquiv ε h) '' divSupp V s := by
  have hsup : V.map (relabelRingEquiv ε h) ⊔ Ideal.span {relabelRingEquiv ε h s} =
      (V ⊔ Ideal.span {s}).map (relabelRingEquiv ε h) := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  ext W'
  simp only [divSupp, Set.mem_ofPred_eq, Set.mem_image, hsup, minimalPrimes_map_ringEquiv]
  constructor
  · rintro ⟨⟨W, hW, rfl⟩, hrel⟩
    exact ⟨W, ⟨hW, (isRelevant_map_relabel_iff ε h W).1 hrel⟩, rfl⟩
  · rintro ⟨W, ⟨hW, hrel⟩, rfl⟩
    exact ⟨⟨W, hW, rfl⟩, (isRelevant_map_relabel_iff ε h W).2 hrel⟩

/- English proof (translation)
Unfold `multAt`. Distinguish the cases in `hV : V.IsPrime`. Establish `hV' : (V.map (relabelRingEquiv ε h)).IsPrime` using `(isPrime_map_ringEquiv_iff (relabelRingEquiv ε h) V).2 hV`. Rewrite using `[dif_pos hV, dif_pos hV']`. Conclude with `congrArg ENat.toNat (length_localizedModule_quotient_map (relabelRingEquiv ε h) J V)`.

Establish `hV' : ¬ (V.map (relabelRingEquiv ε h)).IsPrime` using `fun h' => hV ((isPrime_map_ringEquiv_iff (relabelRingEquiv ε h) V).1 h')`. Rewrite using `[dif_neg hV, dif_neg hV']`.
-/
theorem multAt_map_relabel (J V : Ideal (MRing ι)) :
    multAt (J.map (relabelRingEquiv ε h)) (V.map (relabelRingEquiv ε h)) = multAt J V := by
  unfold multAt
  by_cases hV : V.IsPrime
  · have hV' : (V.map (relabelRingEquiv ε h)).IsPrime :=
      (isPrime_map_ringEquiv_iff (relabelRingEquiv ε h) V).2 hV
    rw [dif_pos hV, dif_pos hV']
    exact congrArg ENat.toNat (length_localizedModule_quotient_map (relabelRingEquiv ε h) J V)
  · have hV' : ¬ (V.map (relabelRingEquiv ε h)).IsPrime :=
      fun h' => hV ((isPrime_map_ringEquiv_iff (relabelRingEquiv ε h) V).1 h')
    rw [dif_neg hV, dif_neg hV']

/- English proof (translation)
Establish `hc : (hV' (ε k)).choose = cast (h k) (hV k).choose` using `choose_eq_cast (h k) (hV k) (hV' (ε k)) fun i => not_congr (X_mem_map_relabel_iff ε h V k i)`. Rewrite using `[relabelRingEquiv_X, hc]`.
-/
theorem relabel_X_choose (V : Ideal (MRing ι)) (hV : IsRelevant V)
    (hV' : IsRelevant (V.map (relabelRingEquiv ε h))) (k : K) :
    relabelRingEquiv ε h (X ⟨k, (hV k).choose⟩) = X ⟨ε k, (hV' (ε k)).choose⟩ := by
  have hc : (hV' (ε k)).choose = cast (h k) (hV k).choose :=
    choose_eq_cast (h k) (hV k) (hV' (ε k)) fun i => not_congr (X_mem_map_relabel_iff ε h V k i)
  rw [relabelRingEquiv_X, hc]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `V a`. Distinguish the cases in `hV : IsRelevant V`. Establish `hV'` using `(isRelevant_map_relabel_iff ε h V).2 hV`.

Simplify using `only [geoNum, dif_pos hV, dif_pos hV']`. Establish `hrange : (Set.range fun k' => (X ⟨k', (hV' k').choose⟩ : MRing ι') - 1) = relabelRingEquiv ε h '' Set.range fun k => (X ⟨k, (hV k).choose⟩ : MRing ι) - 1`. Use extensionality with `x`. Simplify using `only [Set.mem_range, Set.mem_image, exists_exists_eq_and]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨k', rfl⟩`. Take `⟨k, rfl⟩` from `ε.surjective k'`. Conclude with `⟨k, by rw [map_sub, map_one, relabel_X_choose ε h V hV hV' k]⟩`. Introduce and unpack `⟨k, rfl⟩`. Conclude with `⟨ε k, by rw [map_sub, map_one, relabel_X_choose ε h V hV hV' k]⟩`.

Rewrite using `[hrange, ← Ideal.map_span, ← Ideal.map_sup, length_int_quotient_map]`. Establish `hV' : ¬ IsRelevant (V.map (relabelRingEquiv ε h))` using `fun h' => hV ((isRelevant_map_relabel_iff ε h V).1 h')`. Simplify using `only [geoNum, dif_neg hV, dif_neg hV']`. Consider the case `succ n ih`. Introduce `V a`.

Distinguish the cases in `hV : IsRelevant V`. Establish `hV'` using `(isRelevant_map_relabel_iff ε h V).2 hV`. Simplify using `only [geoNum, dif_pos hV, dif_pos hV']`. Use `Fintype.sum_equiv ε _ _ fun k => ?_` and prove the remaining obligations. Rewrite using `[← relabel_X_choose ε h V hV hV' k, divSupp_map_relabel, finsum_mem_image ((map_ringEquiv_injective (relabelRingEquiv ε h)).injOn)]`.

Establish `hsup : V.map (relabelRingEquiv ε h) ⊔ Ideal.span {relabelRingEquiv ε h (X ⟨k, (hV k).choose⟩)} = (V ⊔ Ideal.span {(X ⟨k, (hV k).choose⟩ : MRing ι)}).map (relabelRingEquiv ε h)`. Rewrite using `[Ideal.map_sup, Ideal.map_span, Set.image_singleton]`. Rewrite using `[hsup]`. Use `congr 1`. Use `finsum_mem_congr rfl fun W _ => ?_` and prove the remaining obligations.

Rewrite using `[multAt_map_relabel, ← ih W (Fin.init a)]`. Both sides reduce to the same expression. Establish `hV' : ¬ IsRelevant (V.map (relabelRingEquiv ε h))` using `fun h' => hV ((isRelevant_map_relabel_iff ε h V).1 h')`. Simplify using `only [geoNum, dif_neg hV, dif_neg hV']`.
-/
theorem geoNum_relabel (n : ℕ) : ∀ (V : Ideal (MRing ι)) (a : Fin n → K' → ℤ),
    geoNum n V (fun j => a j ∘ ε) = geoNum n (V.map (relabelRingEquiv ε h)) a := by
  induction n with
  | zero =>
    intro V a
    by_cases hV : IsRelevant V
    · have hV' := (isRelevant_map_relabel_iff ε h V).2 hV
      simp only [geoNum, dif_pos hV, dif_pos hV']
      have hrange : (Set.range fun k' => (X ⟨k', (hV' k').choose⟩ : MRing ι') - 1) =
          relabelRingEquiv ε h '' Set.range fun k => (X ⟨k, (hV k).choose⟩ : MRing ι) - 1 := by
        ext x
        simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and]
        constructor
        · rintro ⟨k', rfl⟩
          obtain ⟨k, rfl⟩ := ε.surjective k'
          exact ⟨k, by rw [map_sub, map_one, relabel_X_choose ε h V hV hV' k]⟩
        · rintro ⟨k, rfl⟩
          exact ⟨ε k, by rw [map_sub, map_one, relabel_X_choose ε h V hV hV' k]⟩
      rw [hrange, ← Ideal.map_span, ← Ideal.map_sup, length_int_quotient_map]
    · have hV' : ¬ IsRelevant (V.map (relabelRingEquiv ε h)) :=
        fun h' => hV ((isRelevant_map_relabel_iff ε h V).1 h')
      simp only [geoNum, dif_neg hV, dif_neg hV']
  | succ n ih =>
    intro V a
    by_cases hV : IsRelevant V
    · have hV' := (isRelevant_map_relabel_iff ε h V).2 hV
      simp only [geoNum, dif_pos hV, dif_pos hV']
      refine Fintype.sum_equiv ε _ _ fun k => ?_
      rw [← relabel_X_choose ε h V hV hV' k, divSupp_map_relabel,
        finsum_mem_image ((map_ringEquiv_injective (relabelRingEquiv ε h)).injOn)]
      have hsup : V.map (relabelRingEquiv ε h) ⊔
          Ideal.span {relabelRingEquiv ε h (X ⟨k, (hV k).choose⟩)} =
          (V ⊔ Ideal.span {(X ⟨k, (hV k).choose⟩ : MRing ι)}).map (relabelRingEquiv ε h) := by
        rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
      rw [hsup]
      congr 1
      refine finsum_mem_congr rfl fun W _ => ?_
      rw [multAt_map_relabel, ← ih W (Fin.init a)]
      rfl
    · have hV' : ¬ IsRelevant (V.map (relabelRingEquiv ε h)) :=
        fun h' => hV ((isRelevant_map_relabel_iff ε h V).1 h')
      simp only [geoNum, dif_neg hV, dif_neg hV']

/- English proof (translation)
Establish `key : ∀ f : MRing ι, rename ε (mConeMap (y ∘ relabelBlocks ε h) f) = mConeMap y (relabelRingEquiv ε h f)`. Introduce `f`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C n => simp [mConeMap]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.

Consider the case `mul_X p q hp`. Rewrite using `[map_mul, map_mul, map_mul, hp]`. Take `⟨k, i⟩` from `q`. Rewrite using `[relabelRingEquiv_X]`. Simplify using `only [mConeMap, aeval_X, map_mul, rename_C, rename_X, Function.comp_apply]`.

Both sides reduce to the same expression. Use extensionality with `f`. Simplify using `only [mCoordIdeal, RingHom.mem_ker, Ideal.mem_comap, ← key]`. Conclude with `(map_eq_zero_iff _ (rename_injective ε ε.injective)).symm`.
-/
theorem mCoordIdeal_relabel {Ω : Type} [Field Ω] (y : (Σ k', ι' k') → Ω) :
    mCoordIdeal (y ∘ relabelBlocks ε h) = (mCoordIdeal y).comap (relabelRingEquiv ε h) := by
  have key : ∀ f : MRing ι, rename ε (mConeMap (y ∘ relabelBlocks ε h) f) =
      mConeMap y (relabelRingEquiv ε h f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C n => simp [mConeMap]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p q hp =>
      rw [map_mul, map_mul, map_mul, hp]
      obtain ⟨k, i⟩ := q
      rw [relabelRingEquiv_X]
      simp only [mConeMap, aeval_X, map_mul, rename_C, rename_X, Function.comp_apply]
      rfl
  ext f
  simp only [mCoordIdeal, RingHom.mem_ker, Ideal.mem_comap, ← key]
  exact (map_eq_zero_iff _ (rename_injective ε ε.injective)).symm

/- English proof (translation)
Establish `hcard : Fintype.card K = Fintype.card K'` using `Fintype.card_congr ε`. Prove the components needed by the constructor for the conclusion. Introduce `H W' hW' hPW' hch hdim`. Establish `hWW' : (W'.comap (relabelRingEquiv ε h)).map (relabelRingEquiv ε h) = W'` using `Ideal.map_comap_of_surjective _ (relabelRingEquiv ε h).surjective W'`. Rewrite `hW'`, `hch`, `hdim`, the goal using `[← hWW']`.

Use `H (W'.comap (relabelRingEquiv ε h)) ((isMultiProjPrime_map_relabel_iff ε h _).1 hW') (Ideal.map_le_iff_le_comap.1 hPW') (by rwa [charOf_map_relabel] at hch) (by rw [ringKrullDim_quotient_map] at hdim; rw [hdim, hcard])` as an intermediate fact. Conclude with `this.trans_eq (geoNum_relabel ε h 1 _ fun _ => a)`. Introduce `H W hW hPW hch hdim`. Use `H (W.map (relabelRingEquiv ε h)) ((isMultiProjPrime_map_relabel_iff ε h W).2 hW) (Ideal.map_mono hPW) (by rwa [charOf_map_relabel]) (by rw [ringKrullDim_quotient_map, hdim, hcard])` as an intermediate fact. Conclude with `this.trans_eq (geoNum_relabel ε h 1 W fun _ => a).symm`.
-/
theorem nefOnFibres_map_relabel (P : Ideal (MRing ι)) (a : K' → ℤ) :
    NefOnFibres P (a ∘ ε) ↔ NefOnFibres (P.map (relabelRingEquiv ε h)) a := by
  have hcard : Fintype.card K = Fintype.card K' := Fintype.card_congr ε
  constructor
  · intro H W' hW' hPW' hch hdim
    have hWW' : (W'.comap (relabelRingEquiv ε h)).map (relabelRingEquiv ε h) = W' :=
      Ideal.map_comap_of_surjective _ (relabelRingEquiv ε h).surjective W'
    rw [← hWW'] at hW' hch hdim ⊢
    have := H (W'.comap (relabelRingEquiv ε h))
      ((isMultiProjPrime_map_relabel_iff ε h _).1 hW') (Ideal.map_le_iff_le_comap.1 hPW')
      (by rwa [charOf_map_relabel] at hch)
      (by rw [ringKrullDim_quotient_map] at hdim; rw [hdim, hcard])
    exact this.trans_eq (geoNum_relabel ε h 1 _ fun _ => a)
  · intro H W hW hPW hch hdim
    have := H (W.map (relabelRingEquiv ε h)) ((isMultiProjPrime_map_relabel_iff ε h W).2 hW)
      (Ideal.map_mono hPW) (by rwa [charOf_map_relabel])
      (by rw [ringKrullDim_quotient_map, hdim, hcard])
    exact this.trans_eq (geoNum_relabel ε h 1 W fun _ => a).symm

end Relabel

/- English proof (translation)
Introduce `K K' _ _ ι ι' _ _ ε h Ω _ y a`. Rewrite using `[nefOnFibres_map_relabel ε h, mCoordIdeal_relabel ε h y, Ideal.map_comap_of_surjective _ (relabelRingEquiv ε h).surjective]`.
-/
theorem NefOnFibresRelabel.proof : NefOnFibresRelabel.Statement := by
  intro K K' _ _ ι ι' _ _ ε h Ω _ y a
  rw [nefOnFibres_map_relabel ε h, mCoordIdeal_relabel ε h y,
    Ideal.map_comap_of_surjective _ (relabelRingEquiv ε h).surjective]

end GroundTheory.Heights₂.Heights
