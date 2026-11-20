import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArtinLit
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(W.GDet.repAlg (W.diagRep χ) k[X] _).det = _`. Rewrite using `[← Matrix.det_diagonal]`. Use `congr 1`. Use extensionality with `i j : 2`. Apply the tactic sequence `by_cases h : i = j <;> simp [W.GDet.repAlg, W.diagRep, Matrix.one_apply, Matrix.diagonal_apply, h]`.
-/
private theorem re_chi {n : ℕ} {k H : Type} [CommRing k] [Group H] (χ : Fin n → H →* kˣ) (g : H) :
    (W.GDet.ofRep (W.diagRep χ)).chi (MonoidAlgebra.single g 1) = ∏ i, (X - C (χ i g : k)) := by
  change (W.GDet.repAlg (W.diagRep χ) k[X] _).det = _
  rw [← Matrix.det_diagonal]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [W.GDet.repAlg, W.diagRep, Matrix.one_apply, Matrix.diagonal_apply, h]

/- English proof (translation)
Use `⟨fun i => (-1) ^ (i + 1 : ℕ) * ((q : k) ^ ((i + 1) * i / 2 : ℕ))⁻¹ * P.coeff (n - (i + 1)), ?_⟩` and prove the remaining obligations. Rewrite using `[Hi.heckePol, ← Finset.sum_range_reflect]`. Use `conv_lhs => rw [P.as_sum_range_C_mul_X_pow, hn]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hj' : j ≤ n` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)`.

Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hj'`. Rewrite using `[show j + d + 1 - 1 - j = d by omega, show j + d - d = j by omega]`. Use `congr 2`. Break down `d with _ | d` into its components or cases. Use `hm.coeff_natDegree` as an intermediate fact.

Rewrite `this` using `[hn]`. Simplify using `using this`. Rewrite using `[dif_pos ⟨by omega, by omega⟩]`. Simplify using `only [Nat.add_sub_cancel]`. Establish `h1 : ((-1 : k) ^ (d + 1)) * (-1) ^ (d + 1) = 1` using `by rw [← mul_pow]; simp`.

Establish `h2 : (q : k) ^ ((d + 1) * d / 2) * ((q : k) ^ ((d + 1) * d / 2))⁻¹ = 1` using `mul_inv_cancel₀ (pow_ne_zero _ hq)`. Take the linear combination `(-P.coeff j) * h2 - P.coeff j * ((q : k) ^ ((d + 1) * d / 2) * ((q : k) ^ ((d + 1) * d / 2))⁻¹) * h1`.
-/
private theorem re_hecke {k : Type} [Field k] {n q : ℕ} (hq : (q : k) ≠ 0) (P : k[X]) (hm : P.Monic)
    (hn : P.natDegree = n) : ∃ b : Fin n → k,
      P = heckePol n q fun j => if h : 0 < j ∧ j - 1 < n then b ⟨j - 1, h.2⟩ else 1 := by
  refine ⟨fun i => (-1) ^ (i + 1 : ℕ) * ((q : k) ^ ((i + 1) * i / 2 : ℕ))⁻¹ * P.coeff (n - (i + 1)), ?_⟩
  rw [Hi.heckePol, ← Finset.sum_range_reflect]
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow, hn]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj'
  rw [show j + d + 1 - 1 - j = d by omega, show j + d - d = j by omega]
  congr 2
  rcases d with _ | d
  · have := hm.coeff_natDegree
    rw [hn] at this
    simpa using this
  · rw [dif_pos ⟨by omega, by omega⟩]
    simp only [Nat.add_sub_cancel]
    have h1 : ((-1 : k) ^ (d + 1)) * (-1) ^ (d + 1) = 1 := by rw [← mul_pow]; simp
    have h2 : (q : k) ^ ((d + 1) * d / 2) * ((q : k) ^ ((d + 1) * d / 2))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hq)
    linear_combination (-P.coeff j) * h2 - P.coeff j * ((q : k) ^ ((d + 1) * d / 2) * ((q : k) ^ ((d + 1) * d / 2))⁻¹) * h1

open scoped Pointwise in
/- English proof (translation)
Take `⟨g, rfl⟩` from `exists_smul_eq_of_isPlaceOver (F := E) hA hB`. Establish `hm : ∀ x, g x ∈ g • A ↔ x ∈ A` using `fun x => ValuationSubring.smul_mem_pointwise_smul_iff`. Establish `h0 : IsFrob (F` using `E) A q (g⁻¹ * τ * g) := by`. Use `⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1 : τ • g • A = g • A` using `hτ.1 show (g⁻¹ * τ * g) • A = A`.

Rewrite using `[mul_smul, mul_smul, h1, inv_smul_smul]`. Establish `h1` using `hτ.2 (g x) (by rwa [ValuationSubring.valuation_le_one_iff, hm, ← ValuationSubring.valuation_le_one_iff])`. Establish `e : τ (g x) - g x ^ q = g ((g⁻¹ * τ * g) x - x ^ q)`. Rewrite using `[map_sub, map_pow, AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply]`. Rewrite `h1` using `[e, valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ g.injective, ← valuation_lt_one_iff']`. Then use the resulting hypothesis.

Establish `h2` using `hχ A hA _ (inv_mul_mem_Ine_of_isFrob hσ h0)`. Rewrite `h2` using `[map_mul, map_inv, inv_mul_eq_one, map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]`. Conclude with `h2.symm`.
-/
private theorem re_frob {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (χ : G E Ω →* M) {w : HeightOneSpectrum (𝓞 E)}
    (hχ : ∀ A, IsPlaceOver A w → ∀ s ∈ Ine (F := E) A, χ s = 1) {q : ℕ} {A B : ValuationSubring Ω}
    (hA : IsPlaceOver A w) (hB : IsPlaceOver B w) {σ τ : G E Ω} (hσ : IsFrob A q σ) (hτ : IsFrob B q τ) :
    χ τ = χ σ := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := E) hA hB
  have hm : ∀ x, g x ∈ g • A ↔ x ∈ A := fun x => ValuationSubring.smul_mem_pointwise_smul_iff
  have h0 : IsFrob (F := E) A q (g⁻¹ * τ * g) := by
    refine ⟨?_, fun x hx => ?_⟩
    · have h1 : τ • g • A = g • A := hτ.1
      show (g⁻¹ * τ * g) • A = A
      rw [mul_smul, mul_smul, h1, inv_smul_smul]
    · have h1 := hτ.2 (g x) (by rwa [ValuationSubring.valuation_le_one_iff, hm,
        ← ValuationSubring.valuation_le_one_iff])
      have e : τ (g x) - g x ^ q = g ((g⁻¹ * τ * g) x - x ^ q) := by
        rw [map_sub, map_pow, AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply]
      rwa [e, valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ g.injective,
        ← valuation_lt_one_iff'] at h1
  have h2 := hχ A hA _ (inv_mul_mem_Ine_of_isFrob hσ h0)
  rw [map_mul, map_inv, inv_mul_eq_one, map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul] at h2
  exact h2.symm

/- English proof (translation)
Use `haveI : CompactSpace (Dec (F := E) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact`. Use `haveI : Finite (Dec (F := E) A ⧸ ψ.ker) := ψ.ker.quotient_finite_of_isOpen hψ`. Use `haveI : Finite ψ.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ψ).toEquiv`. Set `ι` to `Subgroup.inclusion (Weil_le_Dec h)`. Assume the negation of the conclusion as `hne`.

Establish `h1 : ψ.rangeRestrict (ι (x * y⁻¹)) ≠ 1` using `fun h1 => hne (by`. Establish `h2 : ψ (ι (x * y⁻¹)) = 1` using `congrArg Subtype.val h1`. Rewrite using `[map_mul, map_inv, map_mul, map_inv, mul_inv_eq_one] at h2)` and apply the resulting hypothesis. Take `⟨φ, hφ⟩` from `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity ψ.range ℂ h1`. Establish `hs : GlobalTheory.WeilDeligne.IsSmooth (ψ.comp ι)` using `hψ.preimage (f := Subgroup.inclusion (Ine_le_Dec (F := E) A)) (continuous_inclusion (Ine_le_Dec (F := E) A))`.

Take `⟨χ, -, hχ⟩` from `ha.factor (φ.comp (ψ.rangeRestrict.comp ι)) (hs.of_le fun σ hσ => by`. Establish `: ψ.rangeRestrict (ι σ) = 1` using `Subtype.ext hσ`. Simplify using `only [MonoidHom.comp_apply, this, map_one])`. Apply `hφ` to reduce the goal to its premises. Establish `h3` using `DFunLike.congr_fun hχ (x * y⁻¹)`.

Rewrite `h3` using `[MonoidHom.comp_apply χ, map_mul a, map_inv a, hxy, mul_inv_cancel, map_one]`. Conclude with `h3`.
-/
private theorem re_art {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a) {M : Type} [CommGroup M]
    (ψ : Dec (F := E) A →* M) (hψ : IsOpen (ψ.ker : Set (Dec (F := E) A))) {x y : Weil h} (hxy : a x = a y) :
    ψ (Subgroup.inclusion (Weil_le_Dec h) x) = ψ (Subgroup.inclusion (Weil_le_Dec h) y) := by
  haveI : CompactSpace (Dec (F := E) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  haveI : Finite (Dec (F := E) A ⧸ ψ.ker) := ψ.ker.quotient_finite_of_isOpen hψ
  haveI : Finite ψ.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  let ι := Subgroup.inclusion (Weil_le_Dec h)
  by_contra hne
  have h1 : ψ.rangeRestrict (ι (x * y⁻¹)) ≠ 1 := fun h1 => hne (by
    have h2 : ψ (ι (x * y⁻¹)) = 1 := congrArg Subtype.val h1
    rwa [map_mul, map_inv, map_mul, map_inv, mul_inv_eq_one] at h2)
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity ψ.range ℂ h1
  have hs : GlobalTheory.WeilDeligne.IsSmooth (ψ.comp ι) :=
    hψ.preimage (f := Subgroup.inclusion (Ine_le_Dec (F := E) A)) (continuous_inclusion (Ine_le_Dec (F := E) A))
  obtain ⟨χ, -, hχ⟩ := ha.factor (φ.comp (ψ.rangeRestrict.comp ι)) (hs.of_le fun σ hσ => by
    have : ψ.rangeRestrict (ι σ) = 1 := Subtype.ext hσ
    simp only [MonoidHom.comp_apply, this, map_one])
  apply hφ
  have h3 := DFunLike.congr_fun hχ (x * y⁻¹)
  rw [MonoidHom.comp_apply χ, map_mul a, map_inv a, hxy, mul_inv_cancel, map_one] at h3
  exact h3

/- English proof (translation)
Use `haveI : FaithfulSMul ℤ_[l] c.O := by`. Rewrite using `[faithfulSMul_iff_algebraMap_injective]`. Introduce `x y hxy`. Establish `h1 : algebraMap ℤ_[l] (PadicAlgCl l) x = algebraMap ℤ_[l] (PadicAlgCl l) y` using `congrArg Subtype.val hxy`. Rewrite `h1` using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l], IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] _ y]`.

Conclude with `Subtype.ext ((algebraMap ℚ_[l] (PadicAlgCl l)).injective h1)`. Use `haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := inferInstance`. Establish `hc : Continuous fun g => ‖((ε g : ℤ_[l]ˣ) : ℤ_[l]) - 1‖` using `by fun_prop`. Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((isOpen_lt hc continuous_const (g := fun _ => 1)).mem_nhds (by simp)) fun g hg => ?_)` and prove the remaining obligations. Establish `h1 : ((ε g : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈ maximalIdeal ℤ_[l]` using `PadicInt.mem_nonunits.2 hg`.

Establish `h2` using `(residue_eq_zero_iff _).2 (map_nonunit (algebraMap ℤ_[l] c.O) _ h1)`. Rewrite `h2` using `[map_sub, map_sub, map_one, map_one, sub_eq_zero]`. Conclude with `Units.ext h2`.
-/
private theorem re_eps {l : ℕ} [Fact l.Prime] (c : Coef l) {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (ε : H →* ℤ_[l]ˣ) (hε : Continuous ε) :
    IsOpen (((Units.map ((algebraMap c.O (ResidueField c.O)).comp (algebraMap ℤ_[l] c.O)).toMonoidHom).comp ε).ker : Set H) := by
  haveI : FaithfulSMul ℤ_[l] c.O := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    have h1 : algebraMap ℤ_[l] (PadicAlgCl l) x = algebraMap ℤ_[l] (PadicAlgCl l) y := congrArg Subtype.val hxy
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l], IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] _ y] at h1
    exact Subtype.ext ((algebraMap ℚ_[l] (PadicAlgCl l)).injective h1)
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := inferInstance
  have hc : Continuous fun g => ‖((ε g : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ := by fun_prop
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
    (Filter.mem_of_superset ((isOpen_lt hc continuous_const (g := fun _ => 1)).mem_nhds (by simp)) fun g hg => ?_)
  have h1 : ((ε g : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈ maximalIdeal ℤ_[l] := PadicInt.mem_nonunits.2 hg
  have h2 := (residue_eq_zero_iff _).2 (map_nonunit (algebraMap ℤ_[l] c.O) _ h1)
  rw [map_sub, map_sub, map_one, map_one, sub_eq_zero] at h2
  exact Units.ext h2

/- English proof (translation)
Introduce `hN l _ L Ω _ _ _ _ _ _ s n _ V Q c m τ₀ r`. Establish `H1 : ∀ w : (hset Q τ₀).Wp, ∃ b : Fin n → c.O, ∀ (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) σ → r.Dbar.chi (MonoidAlgebra.single (V.pr σ⁻¹) 1) = heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then residue c.O (b ⟨j - 1, h.2⟩) else 1`. Introduce and unpack `⟨w, hw, -⟩`. Take `⟨A, hA⟩` from `exists_isPlaceOver Ω w`. Take `⟨φ, hφ⟩` from `exists_isFrob hA`.

Establish `hl : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal` using `fun hl => hw (V.sub (Or.inl (by`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ w.asIdeal`. Rewrite using `[map_natCast])))` and apply the resulting hypothesis. Establish `hq : ((normV w : ℕ) : ResidueField c.O) ≠ 0`. Establish `h1` using `(cycZ L Ω l φ).isUnit.map ((residue c.O).comp (algebraMap ℤ_[l] c.O))`.

Rewrite `h1` using `[cycZ_of_isFrob hl hA hφ, map_natCast]`. Conclude with `h1.ne_zero`. Establish `hI : ∀ B, IsPlaceOver B w → ∀ t ∈ Ine (F` using `L) B, V.pr t = 1 := fun B hB t ht => by`. Use `Subtype.ext ((QuotientGroup.eq_one_iff _).2 ?_)` and prove the remaining obligations. Use `Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)` and prove the remaining obligations.

Simplify using `only [Set.mem_iUnion]`. Use `⟨w.under (𝓞 (Lp L)), hw, B, fun x => ?_, ht.1, ht.2⟩` and prove the remaining obligations. Rewrite using `[IsScalarTower.algebraMap_apply (Lp L) L Ω]`. Conclude with `hB (algebraMap (𝓞 (Lp L)) (𝓞 L) x)`. Take `⟨b, hb⟩` from `re_hecke (n := n) hq (∏ i, (X - C (r.chib i (V.pr φ⁻¹) : ResidueField c.O))) (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _) (by rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]; simp)`.

Use `choose b' hb' using fun i => residue_surjective (b i)`. Use `⟨b', fun B σ hB hσ => ?_⟩` and prove the remaining obligations. Simplify using `only [hb']`. Rewrite using `[← hb]`. Use `(re_chi r.chib (V.pr σ⁻¹)).trans (Finset.prod_congr rfl fun i _ => ?_)` and prove the remaining obligations.

Use `re_frob ((r.chib i).comp V.pr) (fun B hB t ht => (congrArg (r.chib i) (hI B hB t ht)).trans (map_one _)) hA hB hφ hσ` as an intermediate fact. Rewrite `this` using `[← inv_inj, ← map_inv, ← map_inv]`. Conclude with `congrArg (fun u : (ResidueField c.O)ˣ => X - C (u : ResidueField c.O)) this`. Establish `H2 : ∀ (v : V.frame.Vl) (j : Fin n), ∃ b : c.O, ∀ (x : Weil (s.hw v.1)) (g : Dec (F` using `L) (s.A v.1)), (g : G L Ω) = (x : G L Ω) → artOf (s.hw v.1) x = unif _ → ((∏ i with i ≤ j, r.psib v i g * (hset Q τ₀).epsV (ResidueField c.O) v g ^ (i : ℕ) : (ResidueField c.O)ˣ) : ResidueField c.O) = residue c.O b := by`. Introduce `v j`.

Establish `ha : IsLocalArtin (s.hw v.1) (artOf (s.hw v.1))` using `Classical.epsilon_spec (UpperTheory.V.Loc.localArtinReciprocity hN (s.hw v.1))`. Take `⟨y, hy⟩` from `ha.surj (unif _)`. Take `⟨b, hb⟩` from `residue_surjective (R := c.O) ((∏ i with i ≤ j, r.psib v i (Subgroup.inclusion (Weil_le_Dec (s.hw v.1)) y) * (hset Q τ₀).epsV (ResidueField c.O) v (Subgroup.inclusion (Weil_le_Dec (s.hw v.1)) y) ^ (i : ℕ) : (ResidueField c.O)ˣ) : ResidueField c.O)`. Use `⟨b, fun x g hg hx => ?_⟩` and prove the remaining obligations. Take `rfl : g = Subgroup.inclusion (Weil_le_Dec (s.hw v.1)) x` from `Subtype.ext hg`.

Rewrite using `[hb]`. Use `congr 1`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `e1` using `re_art ha (r.psib v i) (r.psib_open v i) (hx.trans hy.symm)`. Establish `e2` using `re_art ha ((hset Q τ₀).epsV (ResidueField c.O) v) (re_eps c ((cycZ L Ω l).comp (Dec (F := L) (s.A v.1)).subtype) ((continuous_cycZ L Ω l).comp continuous_subtype_val)) (hx.trans hy.symm)`.

Conclude with `congrArg₂ (fun u t : (ResidueField c.O)ˣ => u * t ^ (i : ℕ)) e1 e2`. Use `choose b1 hb1 using H1`. Use `choose b2 hb2 using H2`. Conclude with `⟨Sum.elim (fun x => b1 x.1 x.2) (fun x => b2 x.1 x.2), ⟨hb1, hb2⟩⟩`.
-/
theorem UpperTheory.V.Hi.resEx :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), ∀ r : Resid V.frame c.O n, ∃ a, IsRes Q r τ₀ a := by
  intro hN l _ L Ω _ _ _ _ _ _ s n _ V Q c m τ₀ r
  have H1 : ∀ w : (hset Q τ₀).Wp, ∃ b : Fin n → c.O, ∀ (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 →
      IsFrob B (normV w.1) σ → r.Dbar.chi (MonoidAlgebra.single (V.pr σ⁻¹) 1) =
      heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then residue c.O (b ⟨j - 1, h.2⟩) else 1 := by
    rintro ⟨w, hw, -⟩
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨φ, hφ⟩ := exists_isFrob hA
    have hl : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal := fun hl => hw (V.sub (Or.inl (by
      change algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ w.asIdeal
      rwa [map_natCast])))
    have hq : ((normV w : ℕ) : ResidueField c.O) ≠ 0 := by
      have h1 := (cycZ L Ω l φ).isUnit.map ((residue c.O).comp (algebraMap ℤ_[l] c.O))
      rw [cycZ_of_isFrob hl hA hφ, map_natCast] at h1
      exact h1.ne_zero
    have hI : ∀ B, IsPlaceOver B w → ∀ t ∈ Ine (F := L) B, V.pr t = 1 := fun B hB t ht => by
      refine Subtype.ext ((QuotientGroup.eq_one_iff _).2 ?_)
      refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
      simp only [Set.mem_iUnion]
      refine ⟨w.under (𝓞 (Lp L)), hw, B, fun x => ?_, ht.1, ht.2⟩
      rw [IsScalarTower.algebraMap_apply (Lp L) L Ω]
      exact hB (algebraMap (𝓞 (Lp L)) (𝓞 L) x)
    obtain ⟨b, hb⟩ := re_hecke (n := n) hq (∏ i, (X - C (r.chib i (V.pr φ⁻¹) : ResidueField c.O)))
      (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _)
      (by rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]; simp)
    choose b' hb' using fun i => residue_surjective (b i)
    refine ⟨b', fun B σ hB hσ => ?_⟩
    simp only [hb']
    rw [← hb]
    refine (re_chi r.chib (V.pr σ⁻¹)).trans (Finset.prod_congr rfl fun i _ => ?_)
    have := re_frob ((r.chib i).comp V.pr) (fun B hB t ht =>
      (congrArg (r.chib i) (hI B hB t ht)).trans (map_one _)) hA hB hφ hσ
    rw [← inv_inj, ← map_inv, ← map_inv] at this
    exact congrArg (fun u : (ResidueField c.O)ˣ => X - C (u : ResidueField c.O)) this
  have H2 : ∀ (v : V.frame.Vl) (j : Fin n), ∃ b : c.O, ∀ (x : Weil (s.hw v.1)) (g : Dec (F := L) (s.A v.1)),
      (g : G L Ω) = (x : G L Ω) → artOf (s.hw v.1) x = unif _ →
      ((∏ i with i ≤ j, r.psib v i g * (hset Q τ₀).epsV (ResidueField c.O) v g ^ (i : ℕ) : (ResidueField c.O)ˣ) :
        ResidueField c.O) = residue c.O b := by
    intro v j
    have ha : IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) := Classical.epsilon_spec (UpperTheory.V.Loc.localArtinReciprocity hN (s.hw v.1))
    obtain ⟨y, hy⟩ := ha.surj (unif _)
    obtain ⟨b, hb⟩ := residue_surjective (R := c.O) ((∏ i with i ≤ j,
      r.psib v i (Subgroup.inclusion (Weil_le_Dec (s.hw v.1)) y) *
      (hset Q τ₀).epsV (ResidueField c.O) v (Subgroup.inclusion (Weil_le_Dec (s.hw v.1)) y) ^ (i : ℕ) :
        (ResidueField c.O)ˣ) : ResidueField c.O)
    refine ⟨b, fun x g hg hx => ?_⟩
    obtain rfl : g = Subgroup.inclusion (Weil_le_Dec (s.hw v.1)) x := Subtype.ext hg
    rw [hb]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    have e1 := re_art ha (r.psib v i) (r.psib_open v i) (hx.trans hy.symm)
    have e2 := re_art ha ((hset Q τ₀).epsV (ResidueField c.O) v)
      (re_eps c ((cycZ L Ω l).comp (Dec (F := L) (s.A v.1)).subtype)
        ((continuous_cycZ L Ω l).comp continuous_subtype_val)) (hx.trans hy.symm)
    exact congrArg₂ (fun u t : (ResidueField c.O)ˣ => u * t ^ (i : ℕ)) e1 e2
  choose b1 hb1 using H1
  choose b2 hb2 using H2
  exact ⟨Sum.elim (fun x => b1 x.1 x.2) (fun x => b2 x.1 x.2), ⟨hb1, hb2⟩⟩
