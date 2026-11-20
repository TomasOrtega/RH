import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.BaseExistsPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.MaxNotMemMinimalPrimes

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h p hp`. Rewrite using `[← hp.radical_le_iff (I := I), h, hp.radical_le_iff]`. Introduce `h`. Rewrite using `[Ideal.radical_eq_sInf I, Ideal.radical_eq_sInf J]`.

Use `congr 1`. Use extensionality with `p`. Simplify using `only [Set.mem_setOf_eq]`. Conclude with `⟨fun ⟨h1, h2⟩ => ⟨(h p h2).mp h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(h p h2).mpr h1, h2⟩⟩`.
-/
private theorem cut_rad_iff {R : Type} [CommRing R] (I J : Ideal R) :
    I.radical = J.radical ↔ ∀ p : Ideal R, p.IsPrime → (I ≤ p ↔ J ≤ p) := by
  constructor
  · intro h p hp
    rw [← hp.radical_le_iff (I := I), h, hp.radical_le_iff]
  · intro h
    rw [Ideal.radical_eq_sInf I, Ideal.radical_eq_sInf J]
    congr 1
    ext p
    simp only [Set.mem_setOf_eq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨(h p h2).mp h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(h p h2).mpr h1, h2⟩⟩

/- English proof (translation)
Establish `e : PrimeSpectrum.zeroLocus (I : Set R) = PrimeSpectrum.zeroLocus (J : Set R)`. Rewrite using `[← PrimeSpectrum.zeroLocus_radical, h, PrimeSpectrum.zeroLocus_radical]`. Rewrite using `[ringKrullDim_quotient, ringKrullDim_quotient, e]`.
-/
private theorem cut_dim_congr {R : Type} [CommRing R] {I J : Ideal R} (h : I.radical = J.radical) :
    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ J) := by
  have e : PrimeSpectrum.zeroLocus (I : Set R) = PrimeSpectrum.zeroLocus (J : Set R) := by
    rw [← PrimeSpectrum.zeroLocus_radical, h, PrimeSpectrum.zeroLocus_radical]
  rw [ringKrullDim_quotient, ringKrullDim_quotient, e]

/- English proof (translation)
Use `haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr h`. Use `haveI : IsLocalRing (R ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective`. Establish `h1` using `ringKrullDim_ne_top (R := R ⧸ I)`. Establish `h2` using `ringKrullDim_ne_bot (R := R ⧸ I)`. Generalize the expression as in `ringKrullDim (R ⧸ I) = d at h1 h2 ⊢`.

Proceed by induction on `d using WithBot.recBotCoe with`. Consider the case `bot => exact absurd rfl h2`. Consider the case `coe d`. Proceed by induction on `d using ENat.recTopCoe with`. Consider the case `top => exact absurd rfl h1`.

Consider the case `coe n => exact ⟨n, rfl⟩`.
-/
private theorem cut_dim_nat {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {I : Ideal R} (h : I ≠ ⊤) : ∃ n : ℕ, ringKrullDim (R ⧸ I) = n := by
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr h
  haveI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have h1 := ringKrullDim_ne_top (R := R ⧸ I)
  have h2 := ringKrullDim_ne_bot (R := R ⧸ I)
  generalize ringKrullDim (R ⧸ I) = d at h1 h2 ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact absurd rfl h2
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd rfl h1
    | coe n => exact ⟨n, rfl⟩

/- English proof (translation)
Rewrite using `[ReciprocityTheory.CA.ringKrullDim_quotient_eq_quotient_comap_of_isIntegral (A := A)]`. Apply `cut_dim_congr` to reduce the goal to its premises. Rewrite using `[cut_rad_iff]`. Introduce `p hp`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `le_trans Ideal.le_comap_map h`. Introduce `hJ haveI := hp`. Take `⟨Q, -, hQ, hQp⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal R) (by simp [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective A R)])`. Establish `hle : J.map (algebraMap A R) ≤ Q` using `Ideal.map_le_iff_le_comap.mpr (hQp ▸ hJ)`.

Conclude with `hQp ▸ Ideal.comap_mono hle`.
-/
private theorem cut_dim_map {A R : Type} [CommRing A] [CommRing R] [Algebra A R]
    [Algebra.IsIntegral A R] [FaithfulSMul A R] (J : Ideal A) :
    ringKrullDim (R ⧸ J.map (algebraMap A R)) = ringKrullDim (A ⧸ J) := by
  rw [ReciprocityTheory.CA.ringKrullDim_quotient_eq_quotient_comap_of_isIntegral (A := A)]
  apply cut_dim_congr
  rw [cut_rad_iff]
  intro p hp
  constructor
  · intro h
    exact le_trans Ideal.le_comap_map h
  · intro hJ
    haveI := hp
    obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal R)
      (by simp [← RingHom.ker_eq_comap_bot,
        (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective A R)])
    have hle : J.map (algebraMap A R) ≤ Q := Ideal.map_le_iff_le_comap.mpr (hQp ▸ hJ)
    exact hQp ▸ Ideal.comap_mono hle

/- English proof (translation)
Establish `hm : (maximalIdeal R).radical = maximalIdeal R` using `(maximalIdeal.isMaximal R).isPrime.radical`. Rewrite using `[← hm, cut_rad_iff]`. Introduce `p hp`. Prove the components needed by the constructor for the conclusion. Introduce `hIp haveI : Ring.KrullDimLE 0 (R ⧸ I) := Ring.krullDimLE_iff.mpr (by simp [h]) haveI := hp haveI hpm : (p.map (Ideal.Quotient.mk I)).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker]) haveI hmax : (p.map (Ideal.Quotient.mk I)).IsMaxima …`.

Establish `hpc : p = (p.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I)`. Rewrite using `[Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hIp]`. Establish `hpmax : p.IsMaximal`. Rewrite using `[hpc]`. Conclude with `Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective`.

Rewrite using `[IsLocalRing.eq_maximalIdeal hpmax]`. Introduce `hmp`. Conclude with `(IsLocalRing.le_maximalIdeal hI).trans hmp`.
-/
private theorem cut_rad_max {R : Type} [CommRing R] [IsLocalRing R] {I : Ideal R} (hI : I ≠ ⊤)
    (h : ringKrullDim (R ⧸ I) = 0) : I.radical = maximalIdeal R := by
  have hm : (maximalIdeal R).radical = maximalIdeal R := (maximalIdeal.isMaximal R).isPrime.radical
  rw [← hm, cut_rad_iff]
  intro p hp
  constructor
  · intro hIp
    haveI : Ring.KrullDimLE 0 (R ⧸ I) := Ring.krullDimLE_iff.mpr (by simp [h])
    haveI := hp
    haveI hpm : (p.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    haveI hmax : (p.map (Ideal.Quotient.mk I)).IsMaximal := hpm.isMaximal'
    have hpc : p = (p.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.mpr hIp]
    have hpmax : p.IsMaximal := by
      rw [hpc]
      exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    rw [IsLocalRing.eq_maximalIdeal hpmax]
  · intro hmp
    exact (IsLocalRing.le_maximalIdeal hI).trans hmp

/- English proof (translation)
Introduce and unpack `rfl`. Use `haveI : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl`. Rewrite `h` using `[ringKrullDim_eq_bot_of_subsingleton, WithBot.bot_add]`. Conclude with `hk h.symm`.
-/
private theorem cut_ne_top {R : Type} [CommRing R] {I : Ideal R} {k : WithBot ℕ∞}
    (h : ringKrullDim (R ⧸ I) + 1 = k) (hk : k ≠ ⊥) : I ≠ ⊤ := by
  rintro rfl
  haveI : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  rw [ringKrullDim_eq_bot_of_subsingleton, WithBot.bot_add] at h
  exact hk h.symm

/- English proof (translation)
Introduce `A R _ _ _ _ _ _ _ _ _ _ hCM`. Use `haveI : IsNoetherianRing A := hCM.1`. Use `haveI : IsNoetherianRing R := isNoetherian_of_tower A inferInstance`. Establish `hRA : ringKrullDim R = ringKrullDim A` using `ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (FaithfulSMul.algebraMap_injective A R)`. Take `⟨N, hN, -⟩` from `hCM.2`.

Establish `hxs_ne : ∀ xs : List A, (∀ x ∈ xs, x ∈ maximalIdeal A) → Ideal.ofList xs ≠ ⊤`. Introduce `xs hxs`. Conclude with `ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top (Ideal.span_le.mpr fun y hy => hxs y hy)`. Establish `hsup_ne : ∀ b c : Ideal R, b ≠ ⊤ → c ≠ ⊤ → b ⊔ c ≠ ⊤` using `fun b c hb hc => ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top (sup_le (IsLocalRing.le_maximalIdeal hb) (IsLocalRing.le_maximalIdeal hc))`. Establish `key : ∀ d : ℕ, ∀ (xs : List A) (b c : Ideal R), (∀ x ∈ xs, x ∈ maximalIdeal A) → ringKrullDim (A ⧸ Ideal.ofList xs) + xs.length = ringKrullDim A → (b ⊓ c).radical = ((Ideal.ofList xs).map (algebraMap A R)).radical → b ≠ ⊤ → c ≠ ⊤ → ringKrullDim (R ⧸ (b ⊔ c)) < ringKrullDim (R ⧸ b …`.

Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `xs b c hxs hdim hrad hb hc hlt1 hlt2 hd`. Establish `hbc` using `hsup_ne b c hb hc`.

Establish `hd0 : ringKrullDim (R ⧸ (b ⊔ c)) = 0` using `by rw [hd, Nat.cast_zero]`. Establish `hmax` using `cut_rad_max hbc hd0`. Assume the negation of the conclusion as `hcon`. Take `⟨a, ha⟩` from `cut_dim_nat (hxs_ne xs hxs)`. Establish `hdim' : a + xs.length = N`.

Establish `h'` using `hdim`. Rewrite `h'` using `[ha, hN]`. Conclude with `h'` after adjusting the coercions. Establish `hcon' : ¬ N ≤ 0 + 1 + xs.length`. Introduce `h'`.

Apply `hcon` to reduce the goal to its premises. Rewrite using `[hRA, hN]`. Conclude with `h'` after adjusting the coercions. Establish `h2 : 2 ≤ ringKrullDim (A ⧸ Ideal.ofList xs)`. Rewrite using `[ha]`.

Conclude with `(by omega : 2 ≤ a)` after adjusting the coercions. Conclude with `base hCM xs b c hxs hdim h2 hrad hmax (by rwa [hd0] at hlt1) (by rwa [hd0] at hlt2)`. Consider the case `succ d ih`. Introduce `xs b c hxs hdim hrad hb hc hlt1 hlt2 hd`. Establish `hpos_bc : 0 < ringKrullDim (R ⧸ (b ⊔ c))`.

Rewrite using `[hd]`. Conclude with `Nat.succ_pos d` after adjusting the coercions. Establish `hpos_b : 0 < ringKrullDim (R ⧸ b)` using `hpos_bc.trans hlt1`. Establish `hpos_c : 0 < ringKrullDim (R ⧸ c)` using `hpos_bc.trans hlt2`. Establish `hpos_J : 0 < ringKrullDim (R ⧸ (Ideal.ofList xs).map (algebraMap A R))`.

Establish `e1 : ringKrullDim (R ⧸ (Ideal.ofList xs).map (algebraMap A R)) = ringKrullDim (R ⧸ (b ⊓ c))` using `cut_dim_congr hrad.symm`. Establish `e2 : ringKrullDim (R ⧸ (b ⊔ c)) ≤ ringKrullDim (R ⧸ (b ⊓ c))` using `ringKrullDim_le_of_surjective (Ideal.Quotient.factor (inf_le_sup : b ⊓ c ≤ b ⊔ c)) (Ideal.Quotient.factor_surjective inf_le_sup)`. Rewrite using `[e1]`. Conclude with `hpos_bc.trans_le e2`. Take `⟨x, hxm, hx⟩` from `drop (A := A) ({b ⊔ c, b, c, (Ideal.ofList xs).map (algebraMap A R)} : Finset (Ideal R)) (by`.

Introduce `I hI`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hI`. Break down `hI with rfl | rfl | rfl | rfl` into its components or cases. Use `exacts [hpos_bc, hpos_b, hpos_c, hpos_J])`. Establish `hxbc` using `hx (b ⊔ c) (by simp)`.

Establish `hxb` using `hx b (by simp)`. Establish `hxc` using `hx c (by simp)`. Establish `hxJ` using `hx ((Ideal.ofList xs).map (algebraMap A R)) (by simp)`. Take `⟨kb, hkb⟩` from `cut_dim_nat hb`. Take `⟨kc, hkc⟩` from `cut_dim_nat hc`.

Establish `hb' : b ⊔ Ideal.span {algebraMap A R x} ≠ ⊤` using `cut_ne_top hxb (by rw [hkb]; simp)`. Establish `hc' : c ⊔ Ideal.span {algebraMap A R x} ≠ ⊤` using `cut_ne_top hxc (by rw [hkc]; simp)`. Take `⟨kb', hkb'⟩` from `cut_dim_nat hb'`. Take `⟨kc', hkc'⟩` from `cut_dim_nat hc'`. Establish `hbcs : (b ⊔ Ideal.span {algebraMap A R x}) ⊔ (c ⊔ Ideal.span {algebraMap A R x}) = (b ⊔ c) ⊔ Ideal.span {algebraMap A R x}` using `(sup_sup_distrib_right b c _).symm`.

Take `⟨e, he⟩` from `cut_dim_nat (hsup_ne _ _ hb' hc')`. Rewrite `hxbc` using `[← hbcs, he, hd]`. Rewrite `hxb` using `[hkb', hkb]`. Rewrite `hxc` using `[hkc', hkc]`. Rewrite `hlt1` using `[hd, hkb]`.

Rewrite `hlt2` using `[hd, hkc]`. Establish `ne : e + 1 = d + 1` using `by exact_mod_cast hxbc`. Establish `nb : kb' + 1 = kb` using `by exact_mod_cast hxb`. Establish `nc : kc' + 1 = kc` using `by exact_mod_cast hxc`. Establish `lb : d + 1 < kb` using `by exact_mod_cast hlt1`.

Establish `lc : d + 1 < kc` using `by exact_mod_cast hlt2`. Establish `hxs' : ∀ y ∈ x :: xs, y ∈ maximalIdeal A`. Introduce `y hy`. Break down `List.mem_cons.mp hy with rfl | hy` into its components or cases. Conclude with `hxm`.

Conclude with `hxs y hy`. Establish `hJ' : (Ideal.ofList (x :: xs)).map (algebraMap A R) = (Ideal.ofList xs).map (algebraMap A R) ⊔ Ideal.span {algebraMap A R x}`. Rewrite using `[Ideal.ofList_cons, Ideal.map_sup, Ideal.map_span, Set.image_singleton, sup_comm]`. Take `⟨a, ha⟩` from `cut_dim_nat (hxs_ne xs hxs)`. Take `⟨a', ha'⟩` from `cut_dim_nat (hxs_ne (x :: xs) hxs')`.

Rewrite `hxJ` using `[← hJ', cut_dim_map, cut_dim_map, ha, ha']`. Establish `na : a' + 1 = a` using `by exact_mod_cast hxJ`. Establish `hdimN : a + xs.length = N`. Establish `h'` using `hdim`. Rewrite `h'` using `[ha, hN]`.

Conclude with `h'` after adjusting the coercions. Establish `hdim' : ringKrullDim (A ⧸ Ideal.ofList (x :: xs)) + (x :: xs).length = ringKrullDim A`. Rewrite using `[ha', hN, List.length_cons]`. Conclude with `(by omega : a' + (xs.length + 1) = N)` after adjusting the coercions. Establish `hrad' : ((b ⊔ Ideal.span {algebraMap A R x}) ⊓ (c ⊔ Ideal.span {algebraMap A R x})).radical = ((Ideal.ofList (x :: xs)).map (algebraMap A R)).radical`.

Rewrite using `[hJ', cut_rad_iff]`. Introduce `p hp`. Establish `hr` using `(cut_rad_iff _ _).mp hrad p hp`. Rewrite `hr` using `[hp.inf_le]`. Rewrite using `[hp.inf_le, sup_le_iff, sup_le_iff, sup_le_iff]`.

The claim follows by propositional logic. Establish `h1' : ringKrullDim (R ⧸ ((b ⊔ Ideal.span {algebraMap A R x}) ⊔ (c ⊔ Ideal.span {algebraMap A R x}))) < ringKrullDim (R ⧸ (b ⊔ Ideal.span {algebraMap A R x}))`. Rewrite using `[he, hkb']`. Conclude with `(by omega : e < kb')` after adjusting the coercions. Establish `h2' : ringKrullDim (R ⧸ ((b ⊔ Ideal.span {algebraMap A R x}) ⊔ (c ⊔ Ideal.span {algebraMap A R x}))) < ringKrullDim (R ⧸ (c ⊔ Ideal.span {algebraMap A R x}))`.

Rewrite using `[he, hkc']`. Conclude with `(by omega : e < kc')` after adjusting the coercions. Establish `hfin` using `ih (x :: xs) _ _ hxs' hdim' hrad' hb' hc' h1' h2' (by rw [he]; exact_mod_cast (by omega : e = d))`. Establish `heq : ((d : WithBot ℕ∞) + 1 + ((x :: xs).length : WithBot ℕ∞)) = ((d + 1 : ℕ) : WithBot ℕ∞) + 1 + (xs.length : WithBot ℕ∞)`. Rewrite using `[List.length_cons]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← heq]`. Conclude with `hfin`. Introduce `xs b c hxs hdim hrad hb hc hlt1 hlt2`.

Take `⟨d, hd⟩` from `cut_dim_nat (hsup_ne b c hb hc)`. Rewrite using `[hd]`. Conclude with `key d xs b c hxs hdim hrad hb hc hlt1 hlt2 hd`.
-/
theorem UpperTheory.V.AlgebraTools.Conn.cut :
    ∀ {A R : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [CommRing R] [IsLocalRing R] [IsDomain R] [Algebra A R] [Module.Finite A R] [FaithfulSMul A R] [IsAdicComplete (maximalIdeal A) A], ReciprocityTheory.CA.IsCM A → ∀ (xs : List A) (b c : Ideal R),
      (∀ x ∈ xs, x ∈ maximalIdeal A) → ringKrullDim (A ⧸ Ideal.ofList xs) + xs.length = ringKrullDim A →
      (b ⊓ c).radical = ((Ideal.ofList xs).map (algebraMap A R)).radical → b ≠ ⊤ → c ≠ ⊤ →
      ringKrullDim (R ⧸ (b ⊔ c)) < ringKrullDim (R ⧸ b) → ringKrullDim (R ⧸ (b ⊔ c)) < ringKrullDim (R ⧸ c) →
      ringKrullDim R ≤ ringKrullDim (R ⧸ (b ⊔ c)) + 1 + xs.length := by
  classical
  intro A R _ _ _ _ _ _ _ _ _ _ hCM
  haveI : IsNoetherianRing A := hCM.1
  haveI : IsNoetherianRing R := isNoetherian_of_tower A inferInstance
  have hRA : ringKrullDim R = ringKrullDim A :=
    ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (FaithfulSMul.algebraMap_injective A R)
  obtain ⟨N, hN, -⟩ := hCM.2
  have hxs_ne : ∀ xs : List A, (∀ x ∈ xs, x ∈ maximalIdeal A) → Ideal.ofList xs ≠ ⊤ := by
    intro xs hxs
    exact ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top (Ideal.span_le.mpr fun y hy => hxs y hy)
  have hsup_ne : ∀ b c : Ideal R, b ≠ ⊤ → c ≠ ⊤ → b ⊔ c ≠ ⊤ := fun b c hb hc =>
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
      (sup_le (IsLocalRing.le_maximalIdeal hb) (IsLocalRing.le_maximalIdeal hc))
  have key : ∀ d : ℕ, ∀ (xs : List A) (b c : Ideal R), (∀ x ∈ xs, x ∈ maximalIdeal A) →
      ringKrullDim (A ⧸ Ideal.ofList xs) + xs.length = ringKrullDim A →
      (b ⊓ c).radical = ((Ideal.ofList xs).map (algebraMap A R)).radical → b ≠ ⊤ → c ≠ ⊤ →
      ringKrullDim (R ⧸ (b ⊔ c)) < ringKrullDim (R ⧸ b) →
      ringKrullDim (R ⧸ (b ⊔ c)) < ringKrullDim (R ⧸ c) →
      ringKrullDim (R ⧸ (b ⊔ c)) = d → ringKrullDim R ≤ d + 1 + xs.length := by
    intro d
    induction d with
    | zero =>
      intro xs b c hxs hdim hrad hb hc hlt1 hlt2 hd
      have hbc := hsup_ne b c hb hc
      have hd0 : ringKrullDim (R ⧸ (b ⊔ c)) = 0 := by rw [hd, Nat.cast_zero]
      have hmax := cut_rad_max hbc hd0
      by_contra hcon
      obtain ⟨a, ha⟩ := cut_dim_nat (hxs_ne xs hxs)
      have hdim' : a + xs.length = N := by
        have h' := hdim
        rw [ha, hN] at h'
        exact_mod_cast h'
      have hcon' : ¬ N ≤ 0 + 1 + xs.length := by
        intro h'
        apply hcon
        rw [hRA, hN]
        exact_mod_cast h'
      have h2 : 2 ≤ ringKrullDim (A ⧸ Ideal.ofList xs) := by
        rw [ha]
        exact_mod_cast (by omega : 2 ≤ a)
      exact base hCM xs b c hxs hdim h2 hrad hmax (by rwa [hd0] at hlt1) (by rwa [hd0] at hlt2)
    | succ d ih =>
      intro xs b c hxs hdim hrad hb hc hlt1 hlt2 hd
      have hpos_bc : 0 < ringKrullDim (R ⧸ (b ⊔ c)) := by
        rw [hd]
        exact_mod_cast Nat.succ_pos d
      have hpos_b : 0 < ringKrullDim (R ⧸ b) := hpos_bc.trans hlt1
      have hpos_c : 0 < ringKrullDim (R ⧸ c) := hpos_bc.trans hlt2
      have hpos_J : 0 < ringKrullDim (R ⧸ (Ideal.ofList xs).map (algebraMap A R)) := by
        have e1 : ringKrullDim (R ⧸ (Ideal.ofList xs).map (algebraMap A R)) = ringKrullDim (R ⧸ (b ⊓ c)) :=
          cut_dim_congr hrad.symm
        have e2 : ringKrullDim (R ⧸ (b ⊔ c)) ≤ ringKrullDim (R ⧸ (b ⊓ c)) :=
          ringKrullDim_le_of_surjective (Ideal.Quotient.factor (inf_le_sup : b ⊓ c ≤ b ⊔ c))
            (Ideal.Quotient.factor_surjective inf_le_sup)
        rw [e1]
        exact hpos_bc.trans_le e2
      obtain ⟨x, hxm, hx⟩ := drop (A := A) ({b ⊔ c, b, c, (Ideal.ofList xs).map (algebraMap A R)} : Finset (Ideal R))
        (by
          intro I hI
          simp only [Finset.mem_insert, Finset.mem_singleton] at hI
          rcases hI with rfl | rfl | rfl | rfl
          exacts [hpos_bc, hpos_b, hpos_c, hpos_J])
      have hxbc := hx (b ⊔ c) (by simp)
      have hxb := hx b (by simp)
      have hxc := hx c (by simp)
      have hxJ := hx ((Ideal.ofList xs).map (algebraMap A R)) (by simp)
      obtain ⟨kb, hkb⟩ := cut_dim_nat hb
      obtain ⟨kc, hkc⟩ := cut_dim_nat hc
      have hb' : b ⊔ Ideal.span {algebraMap A R x} ≠ ⊤ := cut_ne_top hxb (by rw [hkb]; simp)
      have hc' : c ⊔ Ideal.span {algebraMap A R x} ≠ ⊤ := cut_ne_top hxc (by rw [hkc]; simp)
      obtain ⟨kb', hkb'⟩ := cut_dim_nat hb'
      obtain ⟨kc', hkc'⟩ := cut_dim_nat hc'
      have hbcs : (b ⊔ Ideal.span {algebraMap A R x}) ⊔ (c ⊔ Ideal.span {algebraMap A R x}) =
          (b ⊔ c) ⊔ Ideal.span {algebraMap A R x} := (sup_sup_distrib_right b c _).symm
      obtain ⟨e, he⟩ := cut_dim_nat (hsup_ne _ _ hb' hc')
      rw [← hbcs, he, hd] at hxbc
      rw [hkb', hkb] at hxb
      rw [hkc', hkc] at hxc
      rw [hd, hkb] at hlt1
      rw [hd, hkc] at hlt2
      have ne : e + 1 = d + 1 := by exact_mod_cast hxbc
      have nb : kb' + 1 = kb := by exact_mod_cast hxb
      have nc : kc' + 1 = kc := by exact_mod_cast hxc
      have lb : d + 1 < kb := by exact_mod_cast hlt1
      have lc : d + 1 < kc := by exact_mod_cast hlt2
      have hxs' : ∀ y ∈ x :: xs, y ∈ maximalIdeal A := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hxm
        · exact hxs y hy
      have hJ' : (Ideal.ofList (x :: xs)).map (algebraMap A R) =
          (Ideal.ofList xs).map (algebraMap A R) ⊔ Ideal.span {algebraMap A R x} := by
        rw [Ideal.ofList_cons, Ideal.map_sup, Ideal.map_span, Set.image_singleton, sup_comm]
      obtain ⟨a, ha⟩ := cut_dim_nat (hxs_ne xs hxs)
      obtain ⟨a', ha'⟩ := cut_dim_nat (hxs_ne (x :: xs) hxs')
      rw [← hJ', cut_dim_map, cut_dim_map, ha, ha'] at hxJ
      have na : a' + 1 = a := by exact_mod_cast hxJ
      have hdimN : a + xs.length = N := by
        have h' := hdim
        rw [ha, hN] at h'
        exact_mod_cast h'
      have hdim' : ringKrullDim (A ⧸ Ideal.ofList (x :: xs)) + (x :: xs).length = ringKrullDim A := by
        rw [ha', hN, List.length_cons]
        exact_mod_cast (by omega : a' + (xs.length + 1) = N)
      have hrad' : ((b ⊔ Ideal.span {algebraMap A R x}) ⊓ (c ⊔ Ideal.span {algebraMap A R x})).radical =
          ((Ideal.ofList (x :: xs)).map (algebraMap A R)).radical := by
        rw [hJ', cut_rad_iff]
        intro p hp
        have hr := (cut_rad_iff _ _).mp hrad p hp
        rw [hp.inf_le] at hr
        rw [hp.inf_le, sup_le_iff, sup_le_iff, sup_le_iff]
        tauto
      have h1' : ringKrullDim (R ⧸ ((b ⊔ Ideal.span {algebraMap A R x}) ⊔ (c ⊔ Ideal.span {algebraMap A R x}))) <
          ringKrullDim (R ⧸ (b ⊔ Ideal.span {algebraMap A R x})) := by
        rw [he, hkb']
        exact_mod_cast (by omega : e < kb')
      have h2' : ringKrullDim (R ⧸ ((b ⊔ Ideal.span {algebraMap A R x}) ⊔ (c ⊔ Ideal.span {algebraMap A R x}))) <
          ringKrullDim (R ⧸ (c ⊔ Ideal.span {algebraMap A R x})) := by
        rw [he, hkc']
        exact_mod_cast (by omega : e < kc')
      have hfin := ih (x :: xs) _ _ hxs' hdim' hrad' hb' hc' h1' h2' (by rw [he]; exact_mod_cast (by omega : e = d))
      have heq : ((d : WithBot ℕ∞) + 1 + ((x :: xs).length : WithBot ℕ∞)) =
          ((d + 1 : ℕ) : WithBot ℕ∞) + 1 + (xs.length : WithBot ℕ∞) := by
        rw [List.length_cons]
        push_cast
        ring
      rw [← heq]
      exact hfin
  intro xs b c hxs hdim hrad hb hc hlt1 hlt2
  obtain ⟨d, hd⟩ := cut_dim_nat (hsup_ne b c hb hc)
  rw [hd]
  exact key d xs b c hxs hdim hrad hb hc hlt1 hlt2 hd
