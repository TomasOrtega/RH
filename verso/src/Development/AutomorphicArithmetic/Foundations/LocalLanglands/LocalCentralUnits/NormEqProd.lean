import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.DiscreteGroups.GlobalIrreducibility.LTw
import Development.DiscreteGroups.GlobalIrreducibility.DzTwFin
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.WDBasic
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TwTame
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TameArt
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ResBase
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.NameLaws
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.FinrankK

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

/- English proof (translation)
Set `f : ℤ_[g]ˣ →* (ZMod g)ˣ` to `Units.map (PadicInt.toZMod (p := g)).toMonoidHom`. Establish `hloc : IsLocalHom (PadicInt.toZMod (p` using `g)) := ⟨fun a ha => by`. Assume the negation of the conclusion as `hna`. Establish `h1 : a ∈ IsLocalRing.maximalIdeal ℤ_[g]` using `hna`. Rewrite `h1` using `[← PadicInt.ker_toZMod, RingHom.mem_ker]`.

Rewrite `ha` using `[h1]`. Conclude with `not_isUnit_zero ha⟩`. Establish `hf : Function.Surjective f` using `IsLocalRing.surjective_units_map_of_local_ringHom (PadicInt.toZMod (p := g)) (ZMod.ringHom_surjective _) hloc`. Set `φ : ℤ_[g]ˣ →* (w.adicCompletion E)ˣ` to `Units.map ((i.toRingHom.comp (algebraMap ℤ_[g] ℚ_[g])).toMonoidHom)`. Set `c : ℤ_[g]ˣ →* ℂˣ` to `χ.comp φ`.

Establish `hker : f.ker ≤ c.ker`. Introduce `u hu`. Establish `h0 : PadicInt.toZMod ((u : ℤ_[g]) - 1) = 0`. Establish `h1 : f u = 1` using `hu`. Establish `h2 : PadicInt.toZMod (u : ℤ_[g]) = 1` using `congrArg Units.val h1`.

Rewrite using `[map_sub, h2, map_one, sub_self]`. Establish `h3 : (u : ℤ_[g]) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[g]`. Rewrite using `[← PadicInt.ker_toZMod, RingHom.mem_ker]`. Conclude with `h0`. Establish `h4 : ‖(u : ℤ_[g]) - 1‖ < 1` using `PadicInt.mem_nonunits.1 h3`.

Use `ht (φ u) ?_` and prove the remaining obligations. Establish `h5 : ((φ u : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 = i (((u : ℤ_[g]) - 1 : ℤ_[g]) : ℚ_[g])` using `by show i ((u : ℤ_[g]) : ℚ_[g]) - 1 = _`. Rewrite using `[PadicInt.coe_sub, map_sub, PadicInt.coe_one, map_one]`. Rewrite using `[h5]`. Conclude with `(DiscreteGroups.sglob.DzIso.valuation_lt_iff i hi _).2 (by rwa [← PadicInt.norm_def])`.

Use `⟨MonoidHom.liftOfSurjective f hf ⟨c, hker⟩, fun u x hx => ?_⟩` and prove the remaining obligations. Establish `hxu : x = φ u` using `Units.ext hx`. Rewrite using `[hxu]`. Conclude with `(MonoidHom.liftOfRightInverse_comp_apply f _ (Function.rightInverse_surjInv hf) ⟨c, hker⟩ u).symm`.
-/
private theorem exists_red {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (ht : TameChar χ) :
    ∃ χ₀ : (ZMod g)ˣ →* ℂˣ, ∀ (u : ℤ_[g]ˣ) (x : (w.adicCompletion E)ˣ),
      (x : w.adicCompletion E) = i ((u : ℤ_[g]) : ℚ_[g]) →
      χ x = χ₀ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom u) := by
  let f : ℤ_[g]ˣ →* (ZMod g)ˣ := Units.map (PadicInt.toZMod (p := g)).toMonoidHom
  have hloc : IsLocalHom (PadicInt.toZMod (p := g)) := ⟨fun a ha => by
    by_contra hna
    have h1 : a ∈ IsLocalRing.maximalIdeal ℤ_[g] := hna
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at h1
    rw [h1] at ha
    exact not_isUnit_zero ha⟩
  have hf : Function.Surjective f :=
    IsLocalRing.surjective_units_map_of_local_ringHom (PadicInt.toZMod (p := g)) (ZMod.ringHom_surjective _) hloc
  let φ : ℤ_[g]ˣ →* (w.adicCompletion E)ˣ :=
    Units.map ((i.toRingHom.comp (algebraMap ℤ_[g] ℚ_[g])).toMonoidHom)
  let c : ℤ_[g]ˣ →* ℂˣ := χ.comp φ
  have hker : f.ker ≤ c.ker := by
    intro u hu
    have h0 : PadicInt.toZMod ((u : ℤ_[g]) - 1) = 0 := by
      have h1 : f u = 1 := hu
      have h2 : PadicInt.toZMod (u : ℤ_[g]) = 1 := congrArg Units.val h1
      rw [map_sub, h2, map_one, sub_self]
    have h3 : (u : ℤ_[g]) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[g] := by
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
      exact h0
    have h4 : ‖(u : ℤ_[g]) - 1‖ < 1 := PadicInt.mem_nonunits.1 h3
    refine ht (φ u) ?_
    have h5 : ((φ u : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 = i (((u : ℤ_[g]) - 1 : ℤ_[g]) : ℚ_[g]) := by
      show i ((u : ℤ_[g]) : ℚ_[g]) - 1 = _
      rw [PadicInt.coe_sub, map_sub, PadicInt.coe_one, map_one]
    rw [h5]
    exact (DiscreteGroups.sglob.DzIso.valuation_lt_iff i hi _).2 (by rwa [← PadicInt.norm_def])
  refine ⟨MonoidHom.liftOfSurjective f hf ⟨c, hker⟩, fun u x hx => ?_⟩
  have hxu : x = φ u := Units.ext hx
  rw [hxu]
  exact (MonoidHom.liftOfRightInverse_comp_apply f _ (Function.rightInverse_surjInv hf) ⟨c, hker⟩ u).symm

/- English proof (translation)
Establish `hg : 2 ≤ g` using `(Fact.out : g.Prime).two_le`. Use `haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (by omega))`. Rewrite using `[FiniteField.algebraMap_norm_eq_pow, hK, Nat.card_zmod]`. Simplify using `only [Units.val_pow_eq_pow_val]`. Rewrite using `[Finset.prod_pow_eq_pow_sum, Nat.geomSum_eq hg]`.
-/
private theorem norm_eq_prod {g : ℕ} [Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Nat.card K = g ^ n) (hn : 0 < n) (z : Kˣ) :
    algebraMap (ZMod g) K (Algebra.norm (ZMod g) (z : K)) = ∏ j ∈ Finset.range n, ((z ^ g ^ j : Kˣ) : K) := by
  have hg : 2 ≤ g := (Fact.out : g.Prime).two_le
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (by omega))
  rw [FiniteField.algebraMap_norm_eq_pow, hK, Nat.card_zmod]
  simp only [Units.val_pow_eq_pow_val]
  rw [Finset.prod_pow_eq_pow_sum, Nat.geomSum_eq hg]

/- English proof (translation)
Establish `hdet : ∀ k : GL (Fin n) ℤ_[g], χ (GeneralLinearGroup.det (GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k))) = χ₀ (GeneralLinearGroup.det (GlobalTheory.GLp.red g n k))`. Introduce `k`. Rewrite using `[hl (GeneralLinearGroup.det k) _ ?_]`. Use `congr 1`. Use `Units.ext ?_` and prove the remaining obligations.

Use `show PadicInt.toZMod ((k : Matrix (Fin n) (Fin n) ℤ_[g]).det) = ((GlobalTheory.GLp.red g n k : Matrix (Fin n) (Fin n) (ZMod g))).det`. Conclude with `RingHom.map_det _ _`. Use `show (i.toRingHom.mapMatrix ((algebraMap ℤ_[g] ℚ_[g]).mapMatrix (k : Matrix (Fin n) (Fin n) ℤ_[g]))).det = i.toRingHom ((algebraMap ℤ_[g] ℚ_[g]) (k : Matrix (Fin n) (Fin n) ℤ_[g]).det)`. Rewrite using `[RingHom.map_det, RingHom.map_det]`. Take `⟨φ, hφ0, hφ⟩` from `hσ`.

Use `⟨φ, hφ0, fun k v => ?_⟩` and prove the remaining obligations. Use `show φ ((((detChar (Fin n) χ₀ (GlobalTheory.GLp.red g n k)) : ℂˣ) : ℂ) • τ.ρ (GlobalTheory.GLp.red g n k) v) = (((detChar (Fin n) χ (GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k))) : ℂˣ) : ℂ) • σ.ρ (GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k) …`. Rewrite using `[map_smul, hφ k v, detChar_apply, detChar_apply, hdet k, MonoidHom.comp_apply]`.
-/
private theorem inflates_tw {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E) {n : ℕ} (σ : IrrRep (GL (Fin n) (w.adicCompletion E))) (τ : FDRep ℂ (Gn g n))
    (χ₀ : (ZMod g)ˣ →* ℂˣ) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχs : IsSmoothChar χ)
    (hl : ∀ (u : ℤ_[g]ˣ) (x : (w.adicCompletion E)ˣ), (x : w.adicCompletion E) = i ((u : ℤ_[g]) : ℚ_[g]) →
      χ x = χ₀ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom u))
    (hσ : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ) :
    GlobalTheory.SerSys.TameGen.Inflates
      ((irrTwist σ (detChar (Fin n) χ) (hχs.detChar (n := Fin n))).ρ.comp (GeneralLinearGroup.map i.toRingHom))
      (DiscreteGroups.sglob.DzTw.twFD τ χ₀) := by
  have hdet : ∀ k : GL (Fin n) ℤ_[g],
      χ (GeneralLinearGroup.det (GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k))) =
        χ₀ (GeneralLinearGroup.det (GlobalTheory.GLp.red g n k)) := by
    intro k
    rw [hl (GeneralLinearGroup.det k) _ ?_]
    · congr 1
      refine Units.ext ?_
      show PadicInt.toZMod ((k : Matrix (Fin n) (Fin n) ℤ_[g]).det) =
        ((GlobalTheory.GLp.red g n k : Matrix (Fin n) (Fin n) (ZMod g))).det
      exact RingHom.map_det _ _
    · show (i.toRingHom.mapMatrix ((algebraMap ℤ_[g] ℚ_[g]).mapMatrix (k : Matrix (Fin n) (Fin n) ℤ_[g]))).det =
        i.toRingHom ((algebraMap ℤ_[g] ℚ_[g]) (k : Matrix (Fin n) (Fin n) ℤ_[g]).det)
      rw [RingHom.map_det, RingHom.map_det]
  obtain ⟨φ, hφ0, hφ⟩ := hσ
  refine ⟨φ, hφ0, fun k v => ?_⟩
  show φ ((((detChar (Fin n) χ₀ (GlobalTheory.GLp.red g n k)) : ℂˣ) : ℂ) • τ.ρ (GlobalTheory.GLp.red g n k) v) =
    (((detChar (Fin n) χ (GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k))) : ℂˣ) : ℂ) •
      σ.ρ (GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k)) (φ v)
  rw [map_smul, hφ k v, detChar_apply, detChar_apply, hdet k, MonoidHom.comp_apply]

end UpperTheory.Zero.LLC

open UpperTheory.Zero.LLC in
/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h a ha g _ i hi y hy hdz V hV χ hχ ht`. Use `haveI : CharZero (w.adicCompletion E) := charZero_of_injective_ringHom (f := i.toRingHom) i.injective`. Take `⟨⟨ω₀, -, hω₀, -⟩, htw, h1, -⟩` from `clBasic (w.adicCompletion E) y`. Take `⟨⟨ω₁, -, -, huniq⟩, -⟩` from `clBasic (w.adicCompletion E) (y.tw χ hχ)`. Take `⟨hd, -, -, hmul, hcen⟩` from `htw χ hχ`.

Establish `hB` using `wDBasic E Ω A w h V`. Take `⟨-, -, -, hirr, -, -, -, hine, hT⟩` from `hB`. Take `⟨hTd, hTi, hTe, -, -, -, hTt, -⟩` from `hT (χ.comp a) (ha.smooth hχ)`. Establish `hI : IsIrrWD (V.lpTwist (χ.comp a) (ha.smooth hχ))` using `hTi hV.irr`. Use `⟨hI, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hTd, hV.dim, hd]`. Conclude with `hTt (fun σ hσ => (tameArt E Ω A w h a ha χ hχ).1 ht σ hσ) hV.tame`. Introduce `ω hω σ`. Establish `e1 : ω = ω₀ * χ ^ y.1` using `(huniq ω hω).trans (huniq _ (hcen ω₀ hω₀)).symm`. Rewrite using `[hTe, hV.central ω₀ hω₀ σ, hV.dim, e1]`.

Simplify using the standard rewrite rules. Introduce `g' _ i' hi' n hn D R hR θ hθ τ hτ hN σ hσ hinf`. Take `⟨χ₀, hχ₀⟩` from `exists_red i' hi' χ ht`. Establish `hrank : Module.finrank (ZMod g') D.K = n` using `((resEx E Ω A w h g' i' hi' n hn D).2 R hR).rank`. Establish `hK : Nat.card D.K = g' ^ n` using `by haveI : Module.Finite (ZMod g') D.K := Module.finite_of_finrank_pos (by omega)`.

Rewrite using `[Module.natCard_eq_pow_finrank (K := ZMod g'), Nat.card_zmod, hrank]`. Establish `hχi : IsSmoothChar χ⁻¹` using `IsSmoothChar.inv hχ`. Establish `hl : ∀ (u : ℤ_[g']ˣ) (x : (w.adicCompletion E)ˣ), (x : w.adicCompletion E) = i' ((u : ℤ_[g']) : ℚ_[g']) → χ⁻¹ x = χ₀⁻¹ (Units.map (PadicInt.toZMod (p` using `g')).toMonoidHom u) := by`. Introduce `u x hx`. Rewrite using `[MonoidHom.inv_apply, MonoidHom.inv_apply, hχ₀ u x hx]`.

Establish `hcl : cls (irrTwist σ (detChar (Fin n) χ⁻¹) (hχi.detChar (n` using `Fin n))) = y := by`. Establish `e1 : cls (irrTwist σ (detChar (Fin n) χ⁻¹) (hχi.detChar (n` using `Fin n))) = (cls σ).tw χ⁻¹ hχi := Sigma.ext rfl (heq_of_eq (clTwist_cl σ _ _).symm)`. Establish `e2 : ∀ (c : (w.adicCompletion E)ˣ →* ℂˣ) (hc : IsSmoothChar c), c = 1 → y.tw c hc = y`. Introduce and unpack `c hc rfl`. Conclude with `h1 hc`.

Establish `hs : IsSmoothChar (χ * χ⁻¹)` using `IsSmoothChar.mul hχ hχi`. Rewrite using `[e1, hσ, hmul χ⁻¹ hχi hs]`. Conclude with `e2 _ hs (mul_inv_cancel χ)`. Establish `hty` using `hV.type g' i' hi' n hn D R hR (θ * DiscreteGroups.sglob.DzType.nmChar D.K χ₀⁻¹) (DiscreteGroups.sglob.DzTw.isRegularChar_mul D.K χ₀⁻¹ hθ) (DiscreteGroups.sglob.DzTw.twFD τ χ₀⁻¹) (DiscreteGroups.sglob.DzTw.isCusp_twFD τ χ₀⁻¹ hτ) (DiscreteGroups.sglob.DzTw.char_twFD D.K hK hn χ₀⁻¹ …`. Use `⟨((wDBasic E Ω A w h _).2.2.2.1 hI).1, fun t => ?_⟩` and prove the remaining obligations.

Establish `hval : χ (a (ineIncl h t)) = DiscreteGroups.sglob.DzType.nmChar D.K χ₀ (R t)`. Take `⟨u, hu, hun⟩` from `resBase E Ω A w h a ha g' i' hi' n hn D R hR t`. Rewrite using `[hχ₀ u _ hu]`. Use `show χ₀ _ = χ₀ _`. Use `congr 1`.

Use `Units.ext ((algebraMap (ZMod g') D.K).injective ?_)` and prove the remaining obligations. Use `show algebraMap (ZMod g') D.K (PadicInt.toZMod (u : ℤ_[g'])) = algebraMap (ZMod g') D.K (Algebra.norm (ZMod g') (R t : D.K))`. Rewrite using `[hun, norm_eq_prod hK hn]`. Establish `hpoint : ∀ j : ℕ, ((θ * DiscreteGroups.sglob.DzType.nmChar D.K χ₀⁻¹) (R t ^ g' ^ j) * (χ.comp a) (ineIncl h t) : ℂˣ) = θ (R t ^ g' ^ j)`. Introduce `j`.

Establish `e3 : DiscreteGroups.sglob.DzType.nmChar D.K χ₀⁻¹ (R t ^ g' ^ j) * DiscreteGroups.sglob.DzType.nmChar D.K χ₀ (R t) = 1`. Establish `e4 : DiscreteGroups.sglob.DzType.nmChar D.K χ₀⁻¹ = (DiscreteGroups.sglob.DzType.nmChar D.K χ₀)⁻¹` using `rfl`. Establish `e5 : DiscreteGroups.sglob.DzType.nmChar D.K χ₀ (R t ^ g' ^ j) = DiscreteGroups.sglob.DzType.nmChar D.K χ₀ (R t)`. Rewrite using `[map_pow, ← MonoidHom.pow_apply, DiscreteGroups.sglob.DzTw.nmChar_pow]`. Rewrite using `[e4, MonoidHom.inv_apply, e5, inv_mul_cancel]`.

Rewrite using `[MonoidHom.mul_apply, MonoidHom.comp_apply, hval, mul_assoc, e3, mul_one]`. Establish `hm2` using `hine t ((Finset.range n).val.map fun j => (θ * DiscreteGroups.sglob.DzType.nmChar D.K χ₀⁻¹) (R t ^ g' ^ j)) (by`. Simplify using `only [bind_pure_comp, Multiset.fmap_def, Multiset.map_map]`. Conclude with `hty.2 t)`. Rewrite using `[hm2.2.2 (χ.comp a) (ha.smooth hχ), Multiset.map_map]`.

Use `congrArg Multiset.prod (Multiset.map_congr rfl fun j _ => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[hpoint j]`.
-/
theorem UpperTheory.Zero.LLC.parTw : UpperTheory.Zero.LLC.ParTw := by
  intro E Ω _ _ _ _ _ A w h a ha g _ i hi y hy hdz V hV χ hχ ht
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_ringHom (f := i.toRingHom) i.injective
  obtain ⟨⟨ω₀, -, hω₀, -⟩, htw, h1, -⟩ := clBasic (w.adicCompletion E) y
  obtain ⟨⟨ω₁, -, -, huniq⟩, -⟩ := clBasic (w.adicCompletion E) (y.tw χ hχ)
  obtain ⟨hd, -, -, hmul, hcen⟩ := htw χ hχ
  have hB := wDBasic E Ω A w h V
  obtain ⟨-, -, -, hirr, -, -, -, hine, hT⟩ := hB
  obtain ⟨hTd, hTi, hTe, -, -, -, hTt, -⟩ := hT (χ.comp a) (ha.smooth hχ)
  have hI : IsIrrWD (V.lpTwist (χ.comp a) (ha.smooth hχ)) := hTi hV.irr
  refine ⟨hI, ?_, ?_, ?_, ?_⟩
  · rw [hTd, hV.dim, hd]
  · exact hTt (fun σ hσ => (tameArt E Ω A w h a ha χ hχ).1 ht σ hσ) hV.tame
  · intro ω hω σ
    have e1 : ω = ω₀ * χ ^ y.1 := (huniq ω hω).trans (huniq _ (hcen ω₀ hω₀)).symm
    rw [hTe, hV.central ω₀ hω₀ σ, hV.dim, e1]
    simp
  · intro g' _ i' hi' n hn D R hR θ hθ τ hτ hN σ hσ hinf
    obtain ⟨χ₀, hχ₀⟩ := exists_red i' hi' χ ht
    have hrank : Module.finrank (ZMod g') D.K = n := ((resEx E Ω A w h g' i' hi' n hn D).2 R hR).rank
    have hK : Nat.card D.K = g' ^ n := by
      haveI : Module.Finite (ZMod g') D.K := Module.finite_of_finrank_pos (by omega)
      rw [Module.natCard_eq_pow_finrank (K := ZMod g'), Nat.card_zmod, hrank]
    have hχi : IsSmoothChar χ⁻¹ := IsSmoothChar.inv hχ
    have hl : ∀ (u : ℤ_[g']ˣ) (x : (w.adicCompletion E)ˣ), (x : w.adicCompletion E) = i' ((u : ℤ_[g']) : ℚ_[g']) →
        χ⁻¹ x = χ₀⁻¹ (Units.map (PadicInt.toZMod (p := g')).toMonoidHom u) := by
      intro u x hx
      rw [MonoidHom.inv_apply, MonoidHom.inv_apply, hχ₀ u x hx]
    have hcl : cls (irrTwist σ (detChar (Fin n) χ⁻¹) (hχi.detChar (n := Fin n))) = y := by
      have e1 : cls (irrTwist σ (detChar (Fin n) χ⁻¹) (hχi.detChar (n := Fin n))) = (cls σ).tw χ⁻¹ hχi :=
        Sigma.ext rfl (heq_of_eq (clTwist_cl σ _ _).symm)
      have e2 : ∀ (c : (w.adicCompletion E)ˣ →* ℂˣ) (hc : IsSmoothChar c), c = 1 → y.tw c hc = y := by
        rintro c hc rfl
        exact h1 hc
      have hs : IsSmoothChar (χ * χ⁻¹) := IsSmoothChar.mul hχ hχi
      rw [e1, hσ, hmul χ⁻¹ hχi hs]
      exact e2 _ hs (mul_inv_cancel χ)
    have hty := hV.type g' i' hi' n hn D R hR (θ * DiscreteGroups.sglob.DzType.nmChar D.K χ₀⁻¹)
      (DiscreteGroups.sglob.DzTw.isRegularChar_mul D.K χ₀⁻¹ hθ) (DiscreteGroups.sglob.DzTw.twFD τ χ₀⁻¹)
      (DiscreteGroups.sglob.DzTw.isCusp_twFD τ χ₀⁻¹ hτ) (DiscreteGroups.sglob.DzTw.char_twFD D.K hK hn χ₀⁻¹ θ τ hN)
      (irrTwist σ (detChar (Fin n) χ⁻¹) (hχi.detChar (n := Fin n))) hcl
      (inflates_tw i' σ τ χ₀⁻¹ χ⁻¹ hχi hl hinf)
    refine ⟨((wDBasic E Ω A w h _).2.2.2.1 hI).1, fun t => ?_⟩
    have hval : χ (a (ineIncl h t)) = DiscreteGroups.sglob.DzType.nmChar D.K χ₀ (R t) := by
      obtain ⟨u, hu, hun⟩ := resBase E Ω A w h a ha g' i' hi' n hn D R hR t
      rw [hχ₀ u _ hu]
      show χ₀ _ = χ₀ _
      congr 1
      refine Units.ext ((algebraMap (ZMod g') D.K).injective ?_)
      show algebraMap (ZMod g') D.K (PadicInt.toZMod (u : ℤ_[g'])) = algebraMap (ZMod g') D.K (Algebra.norm (ZMod g') (R t : D.K))
      rw [hun, norm_eq_prod hK hn]
    have hpoint : ∀ j : ℕ, ((θ * DiscreteGroups.sglob.DzType.nmChar D.K χ₀⁻¹) (R t ^ g' ^ j) * (χ.comp a) (ineIncl h t) : ℂˣ) = θ (R t ^ g' ^ j) := by
      intro j
      have e3 : DiscreteGroups.sglob.DzType.nmChar D.K χ₀⁻¹ (R t ^ g' ^ j) * DiscreteGroups.sglob.DzType.nmChar D.K χ₀ (R t) = 1 := by
        have e4 : DiscreteGroups.sglob.DzType.nmChar D.K χ₀⁻¹ = (DiscreteGroups.sglob.DzType.nmChar D.K χ₀)⁻¹ := rfl
        have e5 : DiscreteGroups.sglob.DzType.nmChar D.K χ₀ (R t ^ g' ^ j) = DiscreteGroups.sglob.DzType.nmChar D.K χ₀ (R t) := by
          rw [map_pow, ← MonoidHom.pow_apply, DiscreteGroups.sglob.DzTw.nmChar_pow]
        rw [e4, MonoidHom.inv_apply, e5, inv_mul_cancel]
      rw [MonoidHom.mul_apply, MonoidHom.comp_apply, hval, mul_assoc, e3, mul_one]
    have hm2 := hine t ((Finset.range n).val.map fun j => (θ * DiscreteGroups.sglob.DzType.nmChar D.K χ₀⁻¹) (R t ^ g' ^ j))
      (by
        simp only [bind_pure_comp, Multiset.fmap_def, Multiset.map_map]
        exact hty.2 t)
    rw [hm2.2.2 (χ.comp a) (ha.smooth hχ), Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun j _ => ?_)
    simp only [Function.comp_apply]
    rw [hpoint j]
