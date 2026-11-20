import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AbStruct
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.W

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Establish `hmax : (Ideal.span {(l : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hl).irreducible`. Establish `h0 : Ideal.span {(l : ℤ)} ≠ ⊥` using `by simpa using hl.ne_zero`. Establish `hsum` using `Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(l : ℤ)}) (𝓞 F)`. Rewrite `hsum` using `[RingOfIntegers.rank]`.

Establish `hover : ∀ v : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}, v.1.asIdeal ∈ (Ideal.span {(l : ℤ)}).primesOver (𝓞 F)` using `fun v => by`. Use `⟨v.1.isPrime, ⟨hmax.eq_of_le (Ideal.comap_ne_top _ v.1.isPrime.ne_top) ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]`. Simplify using `using v.2`. Set `e : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal} → (Ideal.span {(l : ℤ)}).primesOver (𝓞 F)` to `fun v => ⟨v.1.asIdeal, hover v⟩`.

Establish `he : Function.Bijective e`. Use `⟨fun a b h => Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h)), fun q => ?_⟩` and prove the remaining obligations. Take `⟨q, h1, h2⟩` from `q`. Use `⟨⟨⟨q, h1, Ideal.ne_bot_of_liesOver_of_ne_bot h0 q⟩, ?_⟩, rfl⟩` and prove the remaining obligations. Establish `: (l : ℤ) ∈ q.under ℤ` using `h2.over ▸ Ideal.mem_span_singleton_self _`.

Simplify using `using this`. Rewrite using `[← hsum, ← finsum_eq_sum_of_fintype]`. Conclude with `finsum_eq_of_bijective e he fun _ => rfl`.
-/
private theorem lc_sum (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F] :
    ∑ᶠ v : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}, ReciprocityTheory.Gal.locDeg v.1 = Module.finrank ℚ F := by
  classical
  have hl : l.Prime := Fact.out
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hl).irreducible
  have h0 : Ideal.span {(l : ℤ)} ≠ ⊥ := by simpa using hl.ne_zero
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(l : ℤ)}) (𝓞 F)
  rw [RingOfIntegers.rank] at hsum
  have hover : ∀ v : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal},
      v.1.asIdeal ∈ (Ideal.span {(l : ℤ)}).primesOver (𝓞 F) := fun v => by
    refine ⟨v.1.isPrime, ⟨hmax.eq_of_le (Ideal.comap_ne_top _ v.1.isPrime.ne_top) ?_⟩⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simpa using v.2
  let e : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal} → (Ideal.span {(l : ℤ)}).primesOver (𝓞 F) :=
    fun v => ⟨v.1.asIdeal, hover v⟩
  have he : Function.Bijective e := by
    refine ⟨fun a b h => Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h)), fun q => ?_⟩
    obtain ⟨q, h1, h2⟩ := q
    refine ⟨⟨⟨q, h1, Ideal.ne_bot_of_liesOver_of_ne_bot h0 q⟩, ?_⟩, rfl⟩
    have : (l : ℤ) ∈ q.under ℤ := h2.over ▸ Ideal.mem_span_singleton_self _
    simpa using this
  rw [← hsum, ← finsum_eq_sum_of_fintype]
  exact finsum_eq_of_bijective e he fun _ => rfl

/- English proof (translation)
Take `⟨-, -, π, a, m, hπ, ha, hm, hmu, hIa, hsa, hIs, hu⟩` from `Loc.abStruct φ hφ`. Set `b : G →* Multiplicative ((Fin φ.range.index → ℤ_[l]) × ℤ_[l])` to `(MulEquiv.prodMultiplicative _ _).symm.toMonoidHom.comp (π.prod a)`. Establish `hb : ∀ g x, b g = Multiplicative.ofAdd x ↔ π g = Multiplicative.ofAdd x.1 ∧ a g = Multiplicative.ofAdd x.2` using `fun g x => Prod.ext_iff`. Use `⟨⟨b, hπ.prodMk ha, fun x => ?_, fun x => ⟨?_, fun hx => ?_⟩, fun C _ _ hC χ hχ h1 g hg => ?_, m, hm, fun g hg => (hmu g hg).2.2⟩⟩` and prove the remaining obligations. Take `⟨g0, h0⟩` from `hsa (Multiplicative.ofAdd x.toAdd.2)`.

Take `⟨g1, h1, h2, -⟩` from `hIs (Multiplicative.ofAdd x.toAdd.1 * (π g0)⁻¹) 1`. Use `⟨g1 * g0, (hb _ x.toAdd).2 ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[map_mul, h2, inv_mul_cancel_right]`. Rewrite using `[map_mul, hIa g1 h1, one_mul, h0]`. Introduce and unpack `⟨g, hg, h⟩`.

Use `((hb g x).1 h).2` as an intermediate fact. Rewrite `this` using `[hIa g ((hI g).2 hg)]`. Conclude with `this.symm`. Take `⟨g, h1, h2, -⟩` from `hIs (Multiplicative.ofAdd x.1) 1`. Conclude with `⟨g, (hI g).1 h1, (hb g x).2 ⟨h2, by rw [hIa g h1, hx]; rfl⟩⟩`.

Take `⟨hg1, hg2⟩` from `(hb g 0).1 hg`. Take `⟨h, hh⟩` from `QuotientGroup.mk'_surjective _ (m g : TopologicalAbelianization G)`. Establish `hmem : h ∈ muG l G`. Use `Subgroup.mem_comap.2 ?_` and prove the remaining obligations. Rewrite using `[hh]`.

Conclude with `(m g).2`. Take `⟨p1, p2, p3⟩` from `hmu h hmem`. Establish `hmh : m h = m g` using `Subtype.ext (p3.trans hh)`. Use `hu C hC χ hχ (g * h⁻¹) (by rw [map_mul, map_inv, p1, hg1]; simp) (by rw [map_mul, map_inv, p2, hg2]; simp) (by rw [map_mul, map_inv, hmh, mul_inv_cancel])` as an intermediate fact. Establish `h3 : χ h = 1` using `h1 hmem`.

Rewrite `this` using `[map_mul, map_inv, h3, inv_one, mul_one]`. Conclude with `this`.
-/
private theorem lc_ab {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G →* Formalism.BasicNotions.Loc.GQ l) (hφ : Topology.IsOpenEmbedding φ) (I : Subgroup G)
    (hI : ∀ g, φ g ∈ Loc.Iq l ↔ g ∈ I) : Nonempty (LocAb l G I φ.range.index) := by
  obtain ⟨-, -, π, a, m, hπ, ha, hm, hmu, hIa, hsa, hIs, hu⟩ := Loc.abStruct φ hφ
  let b : G →* Multiplicative ((Fin φ.range.index → ℤ_[l]) × ℤ_[l]) :=
    (MulEquiv.prodMultiplicative _ _).symm.toMonoidHom.comp (π.prod a)
  have hb : ∀ g x, b g = Multiplicative.ofAdd x ↔ π g = Multiplicative.ofAdd x.1 ∧ a g = Multiplicative.ofAdd x.2 :=
    fun g x => Prod.ext_iff
  refine ⟨⟨b, hπ.prodMk ha, fun x => ?_, fun x => ⟨?_, fun hx => ?_⟩, fun C _ _ hC χ hχ h1 g hg => ?_, m, hm,
    fun g hg => (hmu g hg).2.2⟩⟩
  · obtain ⟨g0, h0⟩ := hsa (Multiplicative.ofAdd x.toAdd.2)
    obtain ⟨g1, h1, h2, -⟩ := hIs (Multiplicative.ofAdd x.toAdd.1 * (π g0)⁻¹) 1
    refine ⟨g1 * g0, (hb _ x.toAdd).2 ⟨?_, ?_⟩⟩
    · rw [map_mul, h2, inv_mul_cancel_right]
    · rw [map_mul, hIa g1 h1, one_mul, h0]
  · rintro ⟨g, hg, h⟩
    have := ((hb g x).1 h).2
    rw [hIa g ((hI g).2 hg)] at this
    exact this.symm
  · obtain ⟨g, h1, h2, -⟩ := hIs (Multiplicative.ofAdd x.1) 1
    exact ⟨g, (hI g).1 h1, (hb g x).2 ⟨h2, by rw [hIa g h1, hx]; rfl⟩⟩
  · obtain ⟨hg1, hg2⟩ := (hb g 0).1 hg
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective _ (m g : TopologicalAbelianization G)
    have hmem : h ∈ muG l G := by
      refine Subgroup.mem_comap.2 ?_
      rw [hh]; exact (m g).2
    obtain ⟨p1, p2, p3⟩ := hmu h hmem
    have hmh : m h = m g := Subtype.ext (p3.trans hh)
    have := hu C hC χ hχ (g * h⁻¹) (by rw [map_mul, map_inv, p1, hg1]; simp) (by rw [map_mul, map_inv, p2, hg2]; simp)
      (by rw [map_mul, map_inv, hmh, mul_inv_cancel])
    have h3 : χ h = 1 := h1 hmem
    rw [map_mul, map_inv, h3, inv_one, mul_one] at this
    exact this

/- English proof (translation)
Introduce `_ _ l _ L Ω _ _ _ _ _ _ s`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective`. Use `⟨fun v => ReciprocityTheory.Gal.locDeg v.1, lc_sum l (Lp L), fun v => ?_⟩` and prove the remaining obligations. Take `⟨v, hv⟩` from `v`. Establish `hA` using `s.hA v`.

Establish `hsp` using `s.split v (Or.inl hv)`. Express the relevant statement in the definitionally equal form `Nonempty (LocAb l (Dec (F := L) (s.A v)) ((Ine (F := L) (s.A v)).subgroupOf (Dec (F := L) (s.A v))) (ReciprocityTheory.Gal.locDeg v))`. Generalize the expression as in `s.A v = A at hA hsp`. Take `⟨j, rfl⟩` from `(Loc.decEmb (F := Lp L) (Ω := Ω) (v := l)).1 A v hA hv`. Take `⟨-, φ', -, a2, a3, -, -, a6⟩` from `(Loc.decEmb (F := Lp L) (Ω := Ω) (v := l)).2 j`.

Take `⟨-, φ, b1, -, b3, b4, -, -⟩` from `(Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j`. Establish `hr : φ'.range = φ.range`. Use extensionality with `σ`. Use `⟨?_, fun h => (a3 σ).2 fun x => ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨g, rfl⟩`.

Take `⟨g', hg'⟩` from `hsp g.2`. Use `(b3 _).2 fun x => ?_` and prove the remaining obligations. Rewrite using `[a2, ← hg']`. Conclude with `congrArg j (g'.commutes x)`. Rewrite using `[IsScalarTower.algebraMap_apply (Lp L) L Ω]`.

Conclude with `(b3 σ).1 h _`. Rewrite using `[← a6 v hA, hr]`. Conclude with `lc_ab φ b1 _ fun g => (b4 g).trans Subgroup.mem_subgroupOf.symm`.
-/
theorem UpperTheory.V.W.locCFT :
    GlobalTheory.Published.GlobalArtinReciprocity → Pa.CohP → LocCFTAll := by
  intro _ _ l _ L Ω _ _ _ _ _ _ s
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  refine ⟨fun v => ReciprocityTheory.Gal.locDeg v.1, lc_sum l (Lp L), fun v => ?_⟩
  obtain ⟨v, hv⟩ := v
  have hA := s.hA v
  have hsp := s.split v (Or.inl hv)
  change Nonempty (LocAb l (Dec (F := L) (s.A v)) ((Ine (F := L) (s.A v)).subgroupOf (Dec (F := L) (s.A v)))
    (ReciprocityTheory.Gal.locDeg v))
  generalize s.A v = A at hA hsp
  obtain ⟨j, rfl⟩ := (Loc.decEmb (F := Lp L) (Ω := Ω) (v := l)).1 A v hA hv
  obtain ⟨-, φ', -, a2, a3, -, -, a6⟩ := (Loc.decEmb (F := Lp L) (Ω := Ω) (v := l)).2 j
  obtain ⟨-, φ, b1, -, b3, b4, -, -⟩ := (Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j
  have hr : φ'.range = φ.range := by
    ext σ
    refine ⟨?_, fun h => (a3 σ).2 fun x => ?_⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨g', hg'⟩ := hsp g.2
      refine (b3 _).2 fun x => ?_
      rw [a2, ← hg']
      exact congrArg j (g'.commutes x)
    · rw [IsScalarTower.algebraMap_apply (Lp L) L Ω]
      exact (b3 σ).1 h _
  rw [← a6 v hA, hr]
  exact lc_ab φ b1 _ fun g => (b4 g).trans Subgroup.mem_subgroupOf.symm
