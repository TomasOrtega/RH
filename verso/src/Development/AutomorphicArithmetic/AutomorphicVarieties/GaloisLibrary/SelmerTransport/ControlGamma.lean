import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.H2SubsingletonTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GammaGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DecInf
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

/- English proof (translation)
Establish `hne : (Ideal.span {(p : (⊥ : Subring Ω))}) ≠ ⊤`. Rewrite using `[Ne, Ideal.span_singleton_eq_top]`. Introduce `hu`. Take `⟨v, hv⟩` from `hu.exists_right_inv`. Take `⟨n, hn⟩` from `Subring.mem_bot.1 v.2`.

Establish `h1 : ((p : ℤ) * n : ℤ) = 1`. Use `congrArg Subtype.val hv` as an intermediate fact. Simplify using `only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one] at this`. Rewrite `this` using `[← hn]`. Conclude with `this` after adjusting the coercions.

Use `Int.isUnit_iff_natAbs_eq.1 (IsUnit.of_mul_eq_one _ h1)` as an intermediate fact. Simplify using `at this`. Conclude with `hp.one_lt.ne' this`. Take `⟨W, -, hW⟩` from `Ideal.image_subset_nonunits_valuationSubring _ hne`. Conclude with `⟨W, (ValuationSubring.mem_nonunits_iff W).1 (hW ⟨p, Ideal.mem_span_singleton_self _, by simp⟩)⟩`.
-/
private theorem exists_val (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ W : ValuationSubring Ω, W.valuation (p : Ω) < 1 := by
  have hne : (Ideal.span {(p : (⊥ : Subring Ω))}) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    obtain ⟨n, hn⟩ := Subring.mem_bot.1 v.2
    have h1 : ((p : ℤ) * n : ℤ) = 1 := by
      have := congrArg Subtype.val hv
      simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one] at this
      rw [← hn] at this
      exact_mod_cast this
    have := Int.isUnit_iff_natAbs_eq.1 (IsUnit.of_mul_eq_one _ h1)
    simp at this
    exact hp.one_lt.ne' this
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
  exact ⟨W, (ValuationSubring.mem_nonunits_iff W).1 (hW ⟨p, Ideal.mem_span_singleton_self _, by simp⟩)⟩

/- English proof (translation)
Take `⟨κ, γ, -, -, hk, -, hcl, hfin⟩` from `gammaGen k Ω l V hV hg hχ`. Use `haveI : ((cycU l V).subgroupOf V).Normal := hk ▸ inferInstance`. Use `(kerResCyc O (G k Ω) (QO l O) _ ((contTw k Ω l).2.2 O ψ n hψo) (cycU l V) V (cycU_le l V) γ.1 γ.2 hcl).2 ?_` and prove the remaining obligations. Introduce `m _`. Establish `hall : ∀ m' : QO l O, m' ∈ H0U (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU l V)`.

Introduce `m' u`. Establish `h1 : ψ u.1 = 1` using `hψ u.2.1`. Establish `h2 : cycZ k Ω l u.1 = 1` using `u.2.2`. Establish `h3 : (ψ * chiO k Ω l O ^ n) u.1 = 1`. Simplify using `[chiO, h1, h2]`.

Use `show (((ψ * chiO k Ω l O ^ n) u.1 : Oˣ) : O) • m' = m'`. Rewrite using `[h3, Units.val_one, one_smul]`. Establish `ha : (((ψ * chiO k Ω l O ^ n) γ.1 : Oˣ) : O) - 1 ≠ 0`. Introduce `h0`. Establish `h1 : ψ γ.1 = 1` using `hψ γ.2`.

Establish `h2 : (ψ * chiO k Ω l O ^ n) γ.1 = 1` using `Units.ext (sub_eq_zero.1 h0)`. Establish `h3 : Units.map (algebraMap ℤ_[l] O).toMonoidHom (cycZ k Ω l γ.1 ^ n) = 1`. Rewrite using `[map_zpow]`. Simplify `h2` using `[chiO, h1]`. Establish `h4 : cycZ k Ω l γ.1 ^ n = 1` using `Units.map_injective (f := (algebraMap ℤ_[l] O).toMonoidHom) (dvrFacts l O).1 (h3.trans (map_one _).symm)`.

Conclude with `hfin (isOfFinOrder_iff_zpow_eq_one.2 ⟨n, hn, h4⟩)`. Take `⟨m', hm'⟩` from `(qoFacts l O).2.2.1 _ ha m`. Use `⟨m', hall m', ?_⟩` and prove the remaining obligations. Use `show (((ψ * chiO k Ω l O ^ n) γ.1 : Oˣ) : O) • m' - m' = m`. Rewrite using `[← hm', sub_smul, one_smul]`.
-/
private theorem inj_cyc (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ)
    [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] (ψ : G k Ω →* Oˣ) (n : ℤ) (hn : n ≠ 0) (hψo : IsOpen (ψ.ker : Set (G k Ω)))
    (V : Subgroup (G k Ω)) (hV : IsClosed (V : Set (G k Ω))) (hg : V ≤ gamU l ⊤) (hψ : V ≤ ψ.ker)
    (hχ : ¬ V ≤ (cycZ k Ω l).ker) :
    Function.Injective (resU (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU_le l V)) := by
  obtain ⟨κ, γ, -, -, hk, -, hcl, hfin⟩ := gammaGen k Ω l V hV hg hχ
  haveI : ((cycU l V).subgroupOf V).Normal := hk ▸ inferInstance
  refine (kerResCyc O (G k Ω) (QO l O) _ ((contTw k Ω l).2.2 O ψ n hψo) (cycU l V) V (cycU_le l V) γ.1 γ.2 hcl).2 ?_
  intro m _
  have hall : ∀ m' : QO l O, m' ∈ H0U (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU l V) := by
    intro m' u
    have h1 : ψ u.1 = 1 := hψ u.2.1
    have h2 : cycZ k Ω l u.1 = 1 := u.2.2
    have h3 : (ψ * chiO k Ω l O ^ n) u.1 = 1 := by
      simp [chiO, h1, h2]
    show (((ψ * chiO k Ω l O ^ n) u.1 : Oˣ) : O) • m' = m'
    rw [h3, Units.val_one, one_smul]
  have ha : (((ψ * chiO k Ω l O ^ n) γ.1 : Oˣ) : O) - 1 ≠ 0 := by
    intro h0
    have h1 : ψ γ.1 = 1 := hψ γ.2
    have h2 : (ψ * chiO k Ω l O ^ n) γ.1 = 1 := Units.ext (sub_eq_zero.1 h0)
    have h3 : Units.map (algebraMap ℤ_[l] O).toMonoidHom (cycZ k Ω l γ.1 ^ n) = 1 := by
      rw [map_zpow]
      simpa [chiO, h1] using h2
    have h4 : cycZ k Ω l γ.1 ^ n = 1 :=
      Units.map_injective (f := (algebraMap ℤ_[l] O).toMonoidHom) (dvrFacts l O).1 (h3.trans (map_one _).symm)
    exact hfin (isOfFinOrder_iff_zpow_eq_one.2 ⟨n, hn, h4⟩)
  obtain ⟨m', hm'⟩ := (qoFacts l O).2.2.1 _ ha m
  refine ⟨m', hall m', ?_⟩
  show (((ψ * chiO k Ω l O ^ n) γ.1 : Oˣ) : O) • m' - m' = m
  rw [← hm', sub_smul, one_smul]

/- English proof (translation)
Unfold `selEig`. Rewrite using `[eig_one]`. Conclude with `⟨fun h g => congrArg Subtype.val (h g), fun h g => Subtype.ext (h g)⟩`.
-/
private theorem mem_selEig_one {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [IsTopologicalGroup G] [DiscreteTopology M]
    (ρ : Representation R G M) (U' : Subgroup G) [U'.Normal] {𝒟 : Set (Subgroup G)} (h𝒟 : ConjStable 𝒟)
    (U : Subgroup G) (x : LocSel ρ U' 𝒟) : x ∈ selEig ρ U' h𝒟 U 1 ↔ x.1 ∈ invariantsUnderSubgroupH1 ρ U U' := by
  unfold selEig
  rw [eig_one]
  exact ⟨fun h g => congrArg Subtype.val (h g), fun h g => Subtype.ext (h g)⟩

/- English proof (translation)
Introduce `k Ω _ _ _ _ _ l hl O _ _ _ _ _ U _ hU hg ψ n hψ hn`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective`. Establish `hψo : IsOpen (ψ.ker : Set (G k Ω))` using `Subgroup.isOpen_mono hψ hU`. Establish `hUc : IsClosed (U : Set (G k Ω))` using `U.isClosed_of_isOpen hU`. Establish `hnt : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ¬ U ⊓ Dec (F` using `k) A ≤ (cycZ k Ω l).ker := by`.

Introduce `A hA h`. Take `⟨g, hgm, hf⟩` from `decInf k Ω l U hU A hA`. Conclude with `hf (by rw [MonoidHom.mem_ker.1 (h hgm)]; exact IsOfFinOrder.one)`. Establish `hχ : ¬ U ≤ (cycZ k Ω l).ker`. Take `⟨A, hA⟩` from `exists_val Ω l hl.out`.

Conclude with `fun h => hnt A hA (inf_le_left.trans h)`. Use `⟨fun a b hab => Subtype.ext (inj_cyc k Ω l O ψ n hn hψo U hUc hg hψ hχ (congrArg Subtype.val hab)), le_antisymm ?_ ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `(mem_selEig_one _ _ _ _ _).2 (restriction_mem_invariant_H1 _ (cycU_le l U) y.1)`. Introduce `x hx`.

Establish `hx1 : x.1 ∈ invariantsUnderSubgroupH1 (twist₂ l (ψ * chiO k Ω l O ^ n)) U (cycU l U)` using `(mem_selEig_one _ _ _ _ _).1 hx`. Take `⟨κ, γ, hκ, hs, hk, -⟩` from `gammaGen k Ω l U hUc hg hχ`. Take `⟨y, hy⟩` from `resZl l O (G k Ω) (QO l O) _ ((contTw k Ω l).2.2 O ψ n hψo) (qoFacts l O).2.1 (cycU l U) U (cycU_le l U) hUc κ hκ hs hk hx1`. Establish `hz : ∀ D ∈ shaFam k Ω l, ∀ (W : Subgroup (G k Ω)) (h : W ≤ cycU l U ⊓ D) (h' : W ≤ U), resU (twist₂ l (ψ * chiO k Ω l O ^ n)) h' y = 0`. Introduce `D hD W h h'`.

Establish `h0` using `mem_locSel.1 x.2 D hD`. Rewrite `h0` using `[← hy, resU_resU]`. Use `congrArg (fun t => resU (twist₂ l (ψ * chiO k Ω l O ^ n)) h t) h0` as an intermediate fact. Rewrite `this` using `[resU_resU, map_zero]`. Then use the resulting hypothesis. Establish `hdec : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → resU (twist₂ l (ψ * chiO k Ω l O ^ n)) (inf_le_left : U ⊓ Dec (F` using `k) A ≤ U) y = 0 := by`.

Introduce `A hA`. Apply `inj_cyc k Ω l O ψ n hn hψo (U ⊓ Dec (F := k) A) (hUc.inter (isClosed_Dec A)) (inf_le_left.trans hg) (inf_le_left.trans hψ) (hnt A hA)` to reduce the goal to its premises. Rewrite using `[resU_resU, map_zero]`. Conclude with `hz _ (Or.inl ⟨A, hA, rfl⟩) (cycU l (U ⊓ Dec (F := k) A)) (fun g hg => ⟨⟨hg.1.1, hg.2⟩, hg.1.2⟩) _`. Use `⟨⟨y, mem_locSel.2 ?_⟩, Subtype.ext hy⟩` and prove the remaining obligations.

Introduce and unpack `D (⟨A, hA, rfl⟩ | ⟨A, rfl⟩)`. Conclude with `hdec A hA`. Distinguish the cases in `hA : A.valuation (l : Ω) < 1`. Use `congrArg (fun t => resU (twist₂ l (ψ * chiO k Ω l O ^ n)) (inf_le_inf_left U (Ine_le_Dec (F := k) A)) t) (hdec A hA)` as an intermediate fact. Rewrite `this` using `[resU_resU, map_zero]`. Then use the resulting hypothesis.

Conclude with `hz _ (Or.inr ⟨A, rfl⟩) (U ⊓ Ine (F := k) A) (fun g hg => ⟨⟨hg.1, (places k Ω l A).2.2.2 hA hg.2⟩, hg.2⟩) _`.
-/
theorem UpperTheory.V.Base.controlGamma :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (U : Subgroup (G k Ω)) [U.Normal], IsOpen (U : Set (G k Ω)) → U ≤ gamU l ⊤ → ∀ (ψ : G k Ω →* Oˣ) (n : ℤ), U ≤ ψ.ker → n ≠ 0 →
      Function.Injective (selRes (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU_le l U) (shaFam k Ω l)) ∧
      LinearMap.range (selRes (twist₂ l (ψ * chiO k Ω l O ^ n)) (cycU_le l U) (shaFam k Ω l)) =
        shaEig (twist₂ l (ψ * chiO k Ω l O ^ n)) l (cycU l U) U 1 := by
  intro k Ω _ _ _ _ _ l hl O _ _ _ _ _ U _ hU hg ψ n hψ hn
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  have hψo : IsOpen (ψ.ker : Set (G k Ω)) := Subgroup.isOpen_mono hψ hU
  have hUc : IsClosed (U : Set (G k Ω)) := U.isClosed_of_isOpen hU
  have hnt : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ¬ U ⊓ Dec (F := k) A ≤ (cycZ k Ω l).ker := by
    intro A hA h
    obtain ⟨g, hgm, hf⟩ := decInf k Ω l U hU A hA
    exact hf (by rw [MonoidHom.mem_ker.1 (h hgm)]; exact IsOfFinOrder.one)
  have hχ : ¬ U ≤ (cycZ k Ω l).ker := by
    obtain ⟨A, hA⟩ := exists_val Ω l hl.out
    exact fun h => hnt A hA (inf_le_left.trans h)
  refine ⟨fun a b hab => Subtype.ext
    (inj_cyc k Ω l O ψ n hn hψo U hUc hg hψ hχ (congrArg Subtype.val hab)), le_antisymm ?_ ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact (mem_selEig_one _ _ _ _ _).2 (restriction_mem_invariant_H1 _ (cycU_le l U) y.1)
  · intro x hx
    have hx1 : x.1 ∈ invariantsUnderSubgroupH1 (twist₂ l (ψ * chiO k Ω l O ^ n)) U (cycU l U) := (mem_selEig_one _ _ _ _ _).1 hx
    obtain ⟨κ, γ, hκ, hs, hk, -⟩ := gammaGen k Ω l U hUc hg hχ
    obtain ⟨y, hy⟩ := resZl l O (G k Ω) (QO l O) _ ((contTw k Ω l).2.2 O ψ n hψo) (qoFacts l O).2.1
      (cycU l U) U (cycU_le l U) hUc κ hκ hs hk hx1
    have hz : ∀ D ∈ shaFam k Ω l, ∀ (W : Subgroup (G k Ω)) (h : W ≤ cycU l U ⊓ D) (h' : W ≤ U),
        resU (twist₂ l (ψ * chiO k Ω l O ^ n)) h' y = 0 := by
      intro D hD W h h'
      have h0 := mem_locSel.1 x.2 D hD
      rw [← hy, resU_resU] at h0
      have := congrArg (fun t => resU (twist₂ l (ψ * chiO k Ω l O ^ n)) h t) h0
      rwa [resU_resU, map_zero] at this
    have hdec : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
        resU (twist₂ l (ψ * chiO k Ω l O ^ n)) (inf_le_left : U ⊓ Dec (F := k) A ≤ U) y = 0 := by
      intro A hA
      apply inj_cyc k Ω l O ψ n hn hψo (U ⊓ Dec (F := k) A) (hUc.inter (isClosed_Dec A)) (inf_le_left.trans hg)
        (inf_le_left.trans hψ) (hnt A hA)
      rw [resU_resU, map_zero]
      exact hz _ (Or.inl ⟨A, hA, rfl⟩) (cycU l (U ⊓ Dec (F := k) A)) (fun g hg => ⟨⟨hg.1.1, hg.2⟩, hg.1.2⟩) _
    refine ⟨⟨y, mem_locSel.2 ?_⟩, Subtype.ext hy⟩
    rintro D (⟨A, hA, rfl⟩ | ⟨A, rfl⟩)
    · exact hdec A hA
    · by_cases hA : A.valuation (l : Ω) < 1
      · have := congrArg (fun t => resU (twist₂ l (ψ * chiO k Ω l O ^ n)) (inf_le_inf_left U (Ine_le_Dec (F := k) A)) t)
          (hdec A hA)
        rwa [resU_resU, map_zero] at this
      · exact hz _ (Or.inr ⟨A, rfl⟩) (U ⊓ Ine (F := k) A)
          (fun g hg => ⟨⟨hg.1, (places k Ω l A).2.2.2 hA hg.2⟩, hg.2⟩) _
