import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilPairingEqCmIntegerOfPureType
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomFamilyOfPureTypeComplexTriple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.PureHom

open PureTriple

/- English proof (translation)
Introduce `E _ _ _ H ρ A B p q hρ hA hB n hn ψ hψ`. Establish `hT : ThetaUnifAV` using `thetaUnifAV_all`. Establish `hL : Out.Laws` using `abelianSchemeLaws_all.1`. Establish `hid : spMap (RingHom.id ℂ) = 𝟙 _` using `Spec.map_id _`. Establish `hdA` using `hA ℂ (RingHom.id ℂ) Function.injective_id`.

Establish `hdB` using `hB ℂ (RingHom.id ℂ) Function.injective_id`. Rewrite `hdA`, `hdB` using `[hid]`. Simplify using `only [RingHom.id_apply] at hdA hdB`. Establish `hsq : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ^ 2 = -(H.d : ℂ)` using `fun τ => by`. Rewrite using `[← map_pow, H.rt_sq, map_neg, map_natCast]`.

Establish `key : ∀ (T : PAT H (Sp ℂ)) (a b : ℕ), (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = ρ → LieMult T.t.act (𝟙 (Sp ℂ)) τ a) ∧ (τ H.rt ≠ ρ → LieMult T.t.act (𝟙 (Sp ℂ)) τ b)) → ∃ a' b' : ℕ, a' + b' = a + b ∧ ∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ a') ∧ (τ H.rt ≠ H.rt0 → LieMult …`. Introduce `T a b hd`. Distinguish the cases in `h0 : ρ = H.rt0`. Conclude with `⟨a, b, rfl, h0 ▸ hd⟩`. Establish `h1` using `(sq_eq_sq_iff_eq_or_eq_neg.1 (hρ.trans H.sqrt_neg_disc_sq.symm)).resolve_left h0`.

Establish `h2 : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ≠ H.rt0 → τ H.rt = ρ` using `fun τ h => ((sq_eq_sq_iff_eq_or_eq_neg.1 ((hsq τ).trans H.sqrt_neg_disc_sq.symm)).resolve_left h).trans h1.symm`. Conclude with `⟨b, a, add_comm b a, fun τ => ⟨fun h => (hd τ).2 fun h' => h0 (h'.symm.trans h), fun h => (hd τ).1 (h2 τ h)⟩⟩`. Take `⟨pA, qA, hpqA, hdetA⟩` from `key A 1 0 hdA`. Take `⟨pB, qB, hpqB, hdetB⟩` from `key B p q hdB`. Take `⟨gA, tyA, htyA⟩` from `AllClasses.exists_isTypeFn H pA qA`.

Take `⟨gB, tyB, htyB⟩` from `AllClasses.exists_isTypeFn H pB qB`. Take `⟨uA, HA, χA, -, hAH, -⟩` from `PureType.exists_isThetaUnif hT A.pol`. Take `⟨uB, HB, χB, -, hBH, -⟩` from `PureType.exists_isThetaUnif hT B.pol`. Take `⟨DA, PeA, FA, hpA, hqA, hPA, hFA, -, hactA⟩` from `exists_datum_period hT hL A htyA hdetA uA hAH`. Take `⟨DB, PeB, FB, hpB, hqB, hPB, hFB, -, hactB⟩` from `exists_datum_period hT hL B htyB hdetB uB hBH`.

Take `⟨-, -, -, -, -, hA2, -⟩` from `GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT A.pol _ uA HA χA hAH`. Take `⟨-, -, -, -, hB1, hB2, -⟩` from `GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT B.pol _ uB HB χB hBH`. Use `choose Ψ hΨ hΨΛ using fun i => (HomLinear.exists_linear_of_isMonHom A.t.G B.t.G A.ab B.ab _ _ _ _ uA uB hB1 hB2 (ψ i) (hψ i).isMonHom).imp fun _ h => And.intro h.1 h.2.1`. Set `GA : 𝓞 E → (Fin A.pol.g → ℂ) →ₗ[ℂ] (Fin A.pol.g → ℂ)` to `fun s => FA.toLinearMap ∘ₗ diagMul tyA (s : E) ∘ₗ FA.symm.toLinearMap`. Set `GB : 𝓞 E → (Fin B.pol.g → ℂ) →ₗ[ℂ] (Fin B.pol.g → ℂ)` to `fun s => FB.toLinearMap ∘ₗ diagMul tyB (s : E) ∘ₗ FB.symm.toLinearMap`.

Establish `hGA : ∀ s z, uA.ex (GA s z) = uA.ex z ≫ A.t.act.act s` using `fun s z => by`. Establish `e` using `hactA s (FA.symm z)`. Rewrite `e` using `[FA.apply_symm_apply]`. Conclude with `e`. Establish `hGB : ∀ s z, uB.ex (GB s z) = uB.ex z ≫ B.t.act.act s` using `fun s z => by`.

Establish `e` using `hactB s (FB.symm z)`. Rewrite `e` using `[FB.apply_symm_apply]`. Conclude with `e`. Establish `hGPA : ∀ s a, GA s (FA (PeA a)) = FA (PeA (s • a))` using `fun s a => by`. Simplify using `only [GA, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using `only [diagMul, LinearMap.coe_mk, AddHom.coe_mk, hPA.1]`. Establish `hGPB : ∀ s b, GB s (FB (PeB b)) = FB (PeB (s • b))` using `fun s b => by`. Simplify using `only [GB, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using `only [diagMul, LinearMap.coe_mk, AddHom.coe_mk, hPB.1]`. Establish `hGAc : ∀ r s z, GA r (GA s z) = GA s (GA r z)` using `fun r s z => by`. Simplify using `only [GA, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using `only [diagMul, LinearMap.coe_mk, AddHom.coe_mk]`. Expand and normalize the polynomial expressions, which then agree. Establish `hGBinj : ∀ r : 𝓞 E, r ≠ 0 → ∀ z, GB r z = 0 → z = 0` using `fun r hr z hz => by`.

Establish `hr' : (r : E) ≠ 0` using `by exact_mod_cast hr`. Establish `e : diagMul tyB (r : E) (FB.symm z) = 0`. Use `congrArg FB.symm hz` as an intermediate fact. Simplify `this` using `[GB]`. Establish `e' : FB.symm z = 0` using `funext fun k => by`.

Use `congrFun e k` as an intermediate fact. Simplify using `only [diagMul, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, mul_eq_zero] at this`. Conclude with `this.resolve_left ((map_ne_zero (tyB k)).2 hr')`. Simplify using `using congrArg FB e'`. Establish `hcomm : ∀ i s z, Ψ i (GA s z) = GB s (Ψ i z)`.

Introduce `i s z`. Use `haveI := (hψ i).isMonHom`. Use `haveI := A.t.act.hom s`. Establish `e` using `linear_lift_unique uA uB hA2 hB1 (A.t.act.act s ≫ ψ i) (F := Ψ i ∘ₗ GA s) (F' := GB s ∘ₗ Ψ i) (fun z => by rw [LinearMap.comp_apply, hΨ, hGA, Category.assoc]) (fun z => by rw [LinearMap.comp_apply, hGB, hΨ, (hψ i).comm, Category.assoc])`. Conclude with `LinearMap.congr_fun e z`.

Use `DA.fin` as an intermediate fact. Use `DA.proj` as an intermediate fact. Use `DB.fin` as an intermediate fact. Use `DB.proj` as an intermediate fact. Establish `hrkA : Module.finrank (𝓞 E) DA.La = 1` using `by rw [DA.rank, hpA, hqA, hpqA]`.

Use `haveI : Nontrivial DA.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [hrkA]; exact one_pos)`. Take `⟨a, ha⟩` from `exists_ne (0 : DA.La)`. Establish `hb : ∀ i, ∃ b : DB.La, Ψ i (FA (PeA a)) = FB (PeB b)` using `fun i => by`. Establish `hm : Ψ i (FA (PeA a)) ∈ uB.Λ` using `hΨΛ i _ ((hFA _).2 ⟨a, rfl⟩)`. Take `⟨b, hb⟩` from `AddMonoidHom.mem_range.1 ((hFB (FB.symm _)).1 (by rwa [FB.apply_symm_apply]))`.

Conclude with `⟨b, by rw [hb, FB.apply_symm_apply]⟩`. Use `choose b hb using hb`. Establish `hrkB : Module.finrank (𝓞 E) DB.La = p + q` using `by rw [DB.rank, hpB, hqB, hpqB]`. Establish `hni : ¬ LinearIndependent (𝓞 E) b` using `fun hi => by`. Use `hi.fintype_card_le_finrank` as an intermediate fact.

Rewrite `this` using `[Fintype.card_fin, hrkB]`. Use linear arithmetic over natural numbers and integers. Take `⟨x, hx, i₀, hi₀⟩` from `Fintype.not_linearIndependent_iff.1 hni`. Use `⟨x, fun h => hi₀ (by rw [h]; rfl), ?_⟩` and prove the remaining obligations. Set `Θ : (Fin A.pol.g → ℂ) →ₗ[ℂ] (Fin B.pol.g → ℂ)` to `∑ i, Ψ i ∘ₗ GA (x i)`.

Establish `hΘ : ∀ z, Θ z = ∑ i, Ψ i (GA (x i) z)` using `fun z => by`. Simplify using `only [Θ, LinearMap.sum_apply, LinearMap.comp_apply]`. Establish `hΘa : Θ (FA (PeA a)) = 0`. Rewrite using `[hΘ]`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hcomm, hb, hGPB]`. Use `_ = 0 := by rw [← map_sum, ← map_sum, hx, map_zero, map_zero]`. Establish `hΘc : ∀ s z, Θ (GA s z) = GB s (Θ z)` using `fun s z => by`. Rewrite using `[hΘ, hΘ, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hGAc, hcomm]`. Establish `hΘl : ∀ a', Θ (FA (PeA a')) = 0` using `fun a' => by`. Take `⟨r, s, hr, e⟩` from `CMLat.exists_smul_eq_smul hrkA ha a'`. Use `hGBinj r hr _ ?_` and prove the remaining obligations.

Rewrite using `[← hΘc, hGPA, e, ← hGPA, hΘc, hΘa, map_zero]`. Establish `hΘ0 : Θ.restrictScalars ℝ = 0`. Use `LinearMap.ext_on uA.full fun z hz => ?_` and prove the remaining obligations. Take `⟨a', ha'⟩` from `AddMonoidHom.mem_range.1 ((hFA (FA.symm z)).1 (by rwa [FA.apply_symm_apply]))`. Establish `ez : z = FA (PeA a')` using `by rw [ha', FA.apply_symm_apply]`.

Rewrite using `[ez]`. Conclude with `hΘl a'`. Establish `hΘz : ∀ z, Θ z = 0` using `fun z => LinearMap.congr_fun hΘ0 z`. Establish `hs : Smooth A.t.G.hom` using `A.ab.smooth`. Establish `hp : IsProper B.t.G.hom` using `B.ab.proper`.

Establish `hr : IsReduced A.t.G.left` using `isReduced_of_smooth_complex _ A.t.G.hom hs`. Use `ComplexPoints.over_hom_ext_of_complexPoints fun y => ?_` and prove the remaining obligations. Take `⟨z, rfl⟩` from `uA.ex_onto y`. Establish `hpr : ∀ s : Finset (Fin n), uA.ex z ≫ ∏ i ∈ s, (A.t.act.act (x i) ≫ ψ i) = uB.ex (∑ i ∈ s, Ψ i (GA (x i) z))`. Introduce `s`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.prod_empty, Finset.sum_empty, comp_one]`. Conclude with `((uB.ker 0).2 uB.Λ.zero_mem).symm`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.sum_insert hj, comp_mul, ih, uB.ex_add, hΨ, hGA, Category.assoc]`.

Rewrite using `[hpr, ← hΘ, hΘz, comp_one]`. Conclude with `(uB.ker 0).2 uB.Λ.zero_mem`.
-/
theorem exists_prod_act_comp_eq_one_of_pure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : ℂ) (A B : PAT H (Sp ℂ)) (p q : ℕ), ρ ^ 2 = -(H.d : ℂ) →
    HasType H A.t.act ρ 1 0 → HasType H B.t.act ρ p q → ∀ (n : ℕ), p + q < n → ∀ ψ : Fin n → (A.t.G ⟶ B.t.G),
    (∀ i, Serre.IsLinearHom A.t.act B.t.act (ψ i)) →
    ∃ x : Fin n → 𝓞 E, x ≠ 0 ∧ ∏ i, (A.t.act.act (x i) ≫ ψ i) = 1 := by
  intro E _ _ _ H ρ A B p q hρ hA hB n hn ψ hψ
  have hT : ThetaUnifAV := thetaUnifAV_all
  have hL : Out.Laws := abelianSchemeLaws_all.1
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := Spec.map_id _
  have hdA := hA ℂ (RingHom.id ℂ) Function.injective_id
  have hdB := hB ℂ (RingHom.id ℂ) Function.injective_id
  rw [hid] at hdA hdB
  simp only [RingHom.id_apply] at hdA hdB
  have hsq : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ^ 2 = -(H.d : ℂ) := fun τ => by
    rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have key : ∀ (T : PAT H (Sp ℂ)) (a b : ℕ), (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = ρ → LieMult T.t.act (𝟙 (Sp ℂ)) τ a) ∧
      (τ H.rt ≠ ρ → LieMult T.t.act (𝟙 (Sp ℂ)) τ b)) → ∃ a' b' : ℕ, a' + b' = a + b ∧
      ∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ a') ∧
        (τ H.rt ≠ H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ b') := by
    intro T a b hd
    by_cases h0 : ρ = H.rt0
    · exact ⟨a, b, rfl, h0 ▸ hd⟩
    · have h1 := (sq_eq_sq_iff_eq_or_eq_neg.1 (hρ.trans H.sqrt_neg_disc_sq.symm)).resolve_left h0
      have h2 : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ≠ H.rt0 → τ H.rt = ρ := fun τ h =>
        ((sq_eq_sq_iff_eq_or_eq_neg.1 ((hsq τ).trans H.sqrt_neg_disc_sq.symm)).resolve_left h).trans h1.symm
      exact ⟨b, a, add_comm b a, fun τ => ⟨fun h => (hd τ).2 fun h' => h0 (h'.symm.trans h),
        fun h => (hd τ).1 (h2 τ h)⟩⟩
  obtain ⟨pA, qA, hpqA, hdetA⟩ := key A 1 0 hdA
  obtain ⟨pB, qB, hpqB, hdetB⟩ := key B p q hdB
  obtain ⟨gA, tyA, htyA⟩ := AllClasses.exists_isTypeFn H pA qA
  obtain ⟨gB, tyB, htyB⟩ := AllClasses.exists_isTypeFn H pB qB
  obtain ⟨uA, HA, χA, -, hAH, -⟩ := PureType.exists_isThetaUnif hT A.pol
  obtain ⟨uB, HB, χB, -, hBH, -⟩ := PureType.exists_isThetaUnif hT B.pol
  obtain ⟨DA, PeA, FA, hpA, hqA, hPA, hFA, -, hactA⟩ := exists_datum_period hT hL A htyA hdetA uA hAH
  obtain ⟨DB, PeB, FB, hpB, hqB, hPB, hFB, -, hactB⟩ := exists_datum_period hT hL B htyB hdetB uB hBH
  obtain ⟨-, -, -, -, -, hA2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT A.pol _ uA HA χA hAH
  obtain ⟨-, -, -, -, hB1, hB2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT B.pol _ uB HB χB hBH
  choose Ψ hΨ hΨΛ using fun i => (HomLinear.exists_linear_of_isMonHom A.t.G B.t.G A.ab B.ab _ _ _ _ uA uB hB1 hB2
    (ψ i) (hψ i).isMonHom).imp fun _ h => And.intro h.1 h.2.1
  let GA : 𝓞 E → (Fin A.pol.g → ℂ) →ₗ[ℂ] (Fin A.pol.g → ℂ) := fun s =>
    FA.toLinearMap ∘ₗ diagMul tyA (s : E) ∘ₗ FA.symm.toLinearMap
  let GB : 𝓞 E → (Fin B.pol.g → ℂ) →ₗ[ℂ] (Fin B.pol.g → ℂ) := fun s =>
    FB.toLinearMap ∘ₗ diagMul tyB (s : E) ∘ₗ FB.symm.toLinearMap
  have hGA : ∀ s z, uA.ex (GA s z) = uA.ex z ≫ A.t.act.act s := fun s z => by
    have e := hactA s (FA.symm z)
    rw [FA.apply_symm_apply] at e
    exact e
  have hGB : ∀ s z, uB.ex (GB s z) = uB.ex z ≫ B.t.act.act s := fun s z => by
    have e := hactB s (FB.symm z)
    rw [FB.apply_symm_apply] at e
    exact e
  have hGPA : ∀ s a, GA s (FA (PeA a)) = FA (PeA (s • a)) := fun s a => by
    simp only [GA, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    congr 1
    funext k
    simp only [diagMul, LinearMap.coe_mk, AddHom.coe_mk, hPA.1]
  have hGPB : ∀ s b, GB s (FB (PeB b)) = FB (PeB (s • b)) := fun s b => by
    simp only [GB, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    congr 1
    funext k
    simp only [diagMul, LinearMap.coe_mk, AddHom.coe_mk, hPB.1]
  have hGAc : ∀ r s z, GA r (GA s z) = GA s (GA r z) := fun r s z => by
    simp only [GA, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    congr 1
    funext k
    simp only [diagMul, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  have hGBinj : ∀ r : 𝓞 E, r ≠ 0 → ∀ z, GB r z = 0 → z = 0 := fun r hr z hz => by
    have hr' : (r : E) ≠ 0 := by exact_mod_cast hr
    have e : diagMul tyB (r : E) (FB.symm z) = 0 := by
      have := congrArg FB.symm hz
      simpa [GB] using this
    have e' : FB.symm z = 0 := funext fun k => by
      have := congrFun e k
      simp only [diagMul, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, mul_eq_zero] at this
      exact this.resolve_left ((map_ne_zero (tyB k)).2 hr')
    simpa using congrArg FB e'
  have hcomm : ∀ i s z, Ψ i (GA s z) = GB s (Ψ i z) := by
    intro i s z
    haveI := (hψ i).isMonHom
    haveI := A.t.act.hom s
    have e := linear_lift_unique uA uB hA2 hB1 (A.t.act.act s ≫ ψ i) (F := Ψ i ∘ₗ GA s) (F' := GB s ∘ₗ Ψ i)
      (fun z => by rw [LinearMap.comp_apply, hΨ, hGA, Category.assoc])
      (fun z => by rw [LinearMap.comp_apply, hGB, hΨ, (hψ i).comm, Category.assoc])
    exact LinearMap.congr_fun e z
  have := DA.fin
  have := DA.proj
  have := DB.fin
  have := DB.proj
  have hrkA : Module.finrank (𝓞 E) DA.La = 1 := by rw [DA.rank, hpA, hqA, hpqA]
  haveI : Nontrivial DA.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [hrkA]; exact one_pos)
  obtain ⟨a, ha⟩ := exists_ne (0 : DA.La)
  have hb : ∀ i, ∃ b : DB.La, Ψ i (FA (PeA a)) = FB (PeB b) := fun i => by
    have hm : Ψ i (FA (PeA a)) ∈ uB.Λ := hΨΛ i _ ((hFA _).2 ⟨a, rfl⟩)
    obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.1 ((hFB (FB.symm _)).1 (by rwa [FB.apply_symm_apply]))
    exact ⟨b, by rw [hb, FB.apply_symm_apply]⟩
  choose b hb using hb
  have hrkB : Module.finrank (𝓞 E) DB.La = p + q := by rw [DB.rank, hpB, hqB, hpqB]
  have hni : ¬ LinearIndependent (𝓞 E) b := fun hi => by
    have := hi.fintype_card_le_finrank
    rw [Fintype.card_fin, hrkB] at this
    omega
  obtain ⟨x, hx, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hni
  refine ⟨x, fun h => hi₀ (by rw [h]; rfl), ?_⟩
  let Θ : (Fin A.pol.g → ℂ) →ₗ[ℂ] (Fin B.pol.g → ℂ) := ∑ i, Ψ i ∘ₗ GA (x i)
  have hΘ : ∀ z, Θ z = ∑ i, Ψ i (GA (x i) z) := fun z => by
    simp only [Θ, LinearMap.sum_apply, LinearMap.comp_apply]
  have hΘa : Θ (FA (PeA a)) = 0 := by
    rw [hΘ]
    calc ∑ i, Ψ i (GA (x i) (FA (PeA a))) = ∑ i, FB (PeB (x i • b i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hcomm, hb, hGPB]
      _ = 0 := by rw [← map_sum, ← map_sum, hx, map_zero, map_zero]
  have hΘc : ∀ s z, Θ (GA s z) = GB s (Θ z) := fun s z => by
    rw [hΘ, hΘ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hGAc, hcomm]
  have hΘl : ∀ a', Θ (FA (PeA a')) = 0 := fun a' => by
    obtain ⟨r, s, hr, e⟩ := CMLat.exists_smul_eq_smul hrkA ha a'
    refine hGBinj r hr _ ?_
    rw [← hΘc, hGPA, e, ← hGPA, hΘc, hΘa, map_zero]
  have hΘ0 : Θ.restrictScalars ℝ = 0 := by
    refine LinearMap.ext_on uA.full fun z hz => ?_
    obtain ⟨a', ha'⟩ := AddMonoidHom.mem_range.1 ((hFA (FA.symm z)).1 (by rwa [FA.apply_symm_apply]))
    have ez : z = FA (PeA a') := by rw [ha', FA.apply_symm_apply]
    rw [ez]
    exact hΘl a'
  have hΘz : ∀ z, Θ z = 0 := fun z => LinearMap.congr_fun hΘ0 z
  have hs : Smooth A.t.G.hom := A.ab.smooth
  have hp : IsProper B.t.G.hom := B.ab.proper
  have hr : IsReduced A.t.G.left := isReduced_of_smooth_complex _ A.t.G.hom hs
  refine ComplexPoints.over_hom_ext_of_complexPoints fun y => ?_
  obtain ⟨z, rfl⟩ := uA.ex_onto y
  have hpr : ∀ s : Finset (Fin n), uA.ex z ≫ ∏ i ∈ s, (A.t.act.act (x i) ≫ ψ i) =
      uB.ex (∑ i ∈ s, Ψ i (GA (x i) z)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, comp_one]; exact ((uB.ker 0).2 uB.Λ.zero_mem).symm
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, comp_mul, ih, uB.ex_add, hΨ, hGA, Category.assoc]
  rw [hpr, ← hΘ, hΘz, comp_one]
  exact (uB.ker 0).2 uB.Λ.zero_mem

end GlobalTheory.CM.PureHom
end
