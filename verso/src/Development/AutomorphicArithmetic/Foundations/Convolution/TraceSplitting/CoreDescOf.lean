import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.T

/- English proof (translation)
Establish `hc` using `GLnLocal.isCompact_integralGL (x.adicCompletion K) n`. Establish `ho` using `GLnLocal.isOpen_integralGL (x.adicCompletion K) n`. Set `P : TopologicalSpace.PositiveCompacts (Gw n x)` to `⟨⟨_, hc⟩, by`. Express the relevant statement in the definitionally equal form `(interior (GLnLocal.integralGL (x.adicCompletion K) n : Set (Gw n x))).Nonempty`. Rewrite using `[ho.interior_eq]`.

Conclude with `⟨1, one_mem _⟩⟩`. Conclude with `⟨Measure.haarMeasure P, inferInstance, Measure.haarMeasure_self⟩`.
-/
theorem haar_norm (K : Type) [Field K] [NumberField K] (n : ℕ) (x : Pl K) [MeasurableSpace (Gw n x)] [BorelSpace (Gw n x)] :
    ∃ mm : Measure (Gw n x), mm.IsHaarMeasure ∧ mm (GLnLocal.integralGL (x.adicCompletion K) n) = 1 := by
  have hc := GLnLocal.isCompact_integralGL (x.adicCompletion K) n
  have ho := GLnLocal.isOpen_integralGL (x.adicCompletion K) n
  let P : TopologicalSpace.PositiveCompacts (Gw n x) := ⟨⟨_, hc⟩, by
    change (interior (GLnLocal.integralGL (x.adicCompletion K) n : Set (Gw n x))).Nonempty
    rw [ho.interior_eq]; exact ⟨1, one_mem _⟩⟩
  exact ⟨Measure.haarMeasure P, inferInstance, Measure.haarMeasure_self⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE _ μF _ θ hθ V Λ t hV hVθ hAt hOffA v w hv τ' hτ'`. Take `⟨S, q, w₀, hvS, hqS, hq, hunr, hsph, hS'⟩` from `hPS F E σ hσ hp n hn μE V Λ t hV hAt v`. Establish `hne` using `(hPl F E hp).2.2.1`. Take `⟨T, hTS, hmk, htyped, hrank, c, f₀, UF, hUF, hL⟩` from `hTy F E σ hσ hp n hn μE V hV q w₀ hq S hqS hunr hsph (Function.update (fun u => (hne u).some) v w)`. Establish `hw : T.mk' v = w` using `by rw [hmk, Function.update_self]`.

Use `clear hmk`. Substitute `hw` using the available equality. Take `⟨u, hu, hu0⟩` from `(Submodule.ne_bot_iff _).1 htyped`. Take `⟨m, hm, D, s, hs, νE, iE, νF, iF, b, a, aE, aF, hposition, harch, hAE, hAF, hpair, hua⟩` from `hPI F E σ hσ hp n hn μE μF u hu0`. Use `letI : ∀ x : Pl E, MeasurableSpace (Gw n x) := fun _ => borel _`.

Use `haveI : ∀ x : Pl E, BorelSpace (Gw n x) := fun _ => ⟨rfl⟩`. Use `letI : ∀ x : Pl F, MeasurableSpace (Gw n x) := fun _ => borel _`. Use `haveI : ∀ x : Pl F, BorelSpace (Gw n x) := fun _ => ⟨rfl⟩`. Establish `hmE : ∀ x : Pl E, ∃ mm : Measure (Gw n x), mm.IsHaarMeasure` using `fun x => (haar_norm E n x).imp fun _ h => h.1`. Establish `hmF : ∀ x : Pl F, ∃ mm : Measure (Gw n x), mm.IsHaarMeasure ∧ mm (GLnLocal.integralGL (x.adicCompletion F) n) = 1` using `fun x => haar_norm F n x`.

Use `choose mE hmE using hmE`. Use `choose mF hmF using hmF`. Establish `hτ : ∀ x : Pl E, ∃ τ : SmIrr (Gw n x), Occurs μE V x τ` using `fun x => by haveI := hmE x`. Conclude with `(hOcc E n μE V x (mE x) hV).1`. Use `choose τ₁ hτ₁ using hτ`.

Choose the witnesses or unpack the hypotheses as in `⟨τ, hτ, hτw⟩ : ∃ τ : ∀ x : Pl E, SmIrr (Gw n x), (∀ x, Occurs μE V x (τ x)) ∧ τ (T.mk' v).1 = τ' := by`. Use `⟨Function.update τ₁ (T.mk' v).1 τ', fun x => ?_, Function.update_self ..⟩` and prove the remaining obligations. Distinguish the cases in `h : x = (T.mk' v).1`. Substitute `h` using the available equality. Rewrite using `[Function.update_self]`.

Conclude with `hτ'`. Rewrite using `[Function.update_of_ne h]`. Conclude with `hτ₁ x`. Substitute `hτw` using the available equality. Take `⟨ν, hν⟩` from `hGood n hn`.

Take `⟨x, cE, Z₀, hx, hcE, hZ₀, hZ0, hE⟩` from `hTE F E σ hσ hp n hn m hm μE θ hθ D s hs hposition νE νF b a aE aF harch q w₀ hq T V hV hVθ hrank ⟨u, hu, hua⟩ mE hmE τ hτ ν hν.1.antitone`. Take `⟨κ, hκ, hG⟩` from `hGM F E σ hσ hp n hn μE μF θ hθ q w₀ hq νE νF aE aF 1 one_pos hAE hAF hpair`. Use `set SF : Set (Pl F) := {y | y ∈ S ∨ y = q} with hSF`. Use `set SE : Set (Pl E) := {y | y.under (𝓞 F) ∈ SF} with hSE`. Take `⟨ι, _, V₀, τ₀, bF, Z, hι, hF⟩` from `hSum F E σ n (Module.finrank F E) hn μF νF mF hmF aF q w₀ S UF ν hν.1.antitone (fun V₀ => ∃ Λ' t', At μF SF V₀ Λ' t' ∧ Λ = bcInf Λ' ∧ ∀ y ∉ SE, t y = bcSat t' y) x hx`.

Establish `hvsp : v ∈ T.sp` using `Finset.mem_filter.2 ⟨hTS ▸ hvS, hv⟩`. Take `⟨τv, r, hr, hiso, htr, hlev⟩` from `hPull F E n v (T.mk' v) (hv _) (mF v) (mE _) (hmF v).1 (hmE _) (τ _)`. Take `⟨hCO, hfix, hφ⟩` from `hlev (T.J _) (UF v) (T.co _) (hUF v hvsp)`. Establish `hunit : ∀ y ∈ T.sp, _` using `fun y hy => hUnit E n μE V hV (T.mk' y).1 (mE _) (hmE _) (τ _) (T.J _) (hτ _) (T.co _) (by`. Use `(Submodule.ne_bot_iff _).2 ⟨u, ⟨hu.1, ?_⟩, hu0⟩` and prove the remaining obligations.

Establish `h1 : u ∈ eigL μE (T.mk' y).1 (T.J _) (T.χ _)` using `(Submodule.mem_iInf _).1 hu.2 _`. Rewrite `h1` using `[T.triv y (Finset.mem_filter.1 hy).2 (T.mk' y)]`. Establish `h2` using `T.chr (T.mk' y).1`. Rewrite `h2` using `[T.triv y (Finset.mem_filter.1 hy).2 (T.mk' y)]`. Rewrite using `[(hEig E n μE _ _ _ (T.co _) h2).2.1] at h1)` and apply the resulting hypothesis.

Establish `hsu : ∀ y : Pl F, ∃ z : ℂ, y ∈ T.sp → z ≠ 0 ∧ HasTrace (mE _) (τ (T.mk' y).1).ρ ((T.J (T.mk' y).1 : Set (Gw n (T.mk' y).1)).indicator 1) z` using `fun y => by`. Distinguish the cases in `hy : y ∈ T.sp`. Take `⟨z, hz⟩` from `(hunit y hy).2.2.2`. Conclude with `⟨z, fun _ => hz⟩`. Conclude with `⟨0, fun h => absurd h hy⟩`.

Use `choose su hsu using hsu`. Set `ψ₁ : ∀ y : Pl F, Gw n (T.mk' y).1 → ℂ` to `fun y => (T.J (T.mk' y).1 : Set (Gw n (T.mk' y).1)).indicator 1`. Take `⟨L₁, hfit₁, -, hL₁s, hL₁n⟩` from `hL ψ₁ fun y hy => ⟨(hunit y hy).2.1, (hunit y hy).2.2.1⟩`. Establish `hL₁S : L₁.S = S` using `hfit₁.S_eq.trans hTS`. Establish `hs₁ : ∀ i (y : Pl F), ∃ z : ℂ, y ∈ S → HasTrace (mF y) (τ₀ i y).ρ (L₁.f y) z` using `fun i y => by`.

Distinguish the cases in `hy : y ∈ S`. Use `haveI := (hmF y).1`. Establish `ht` using `L₁.test y (hL₁S ▸ hy)`. Take `⟨z, hz⟩` from `(hOcc F n μF (V₀ i) y (mF y) (hι i).1).2.2 _ ((hι i).2.2.2 y) (L₁.f y) ⟨ht.2.2.1, ht.2.2.2⟩`. Conclude with `⟨z, fun _ => hz⟩`.

Conclude with `⟨0, fun h => absurd h hy⟩`. Use `choose s₁ hs₁ using hs₁`. Use `haveI := (hmF v).1`. Take `⟨i, hi⟩` from `hAbs F n v (mF v) (UF v) hCO ι (fun i => τ₀ i v) (fun i => (κ * ∏ y ∈ S, c y) * bF i * ∏ y ∈ S.erase v, s₁ i y) Z τv (cE * r * ∏ y ∈ T.sp.erase v, su y) Z₀ (mul_ne_zero (mul_ne_zero hcE hr) (Finset.prod_ne_zero_iff.2 fun y hy => (hsu y (Finset.mem_of_mem_erase hy)).1)) hZ₀ hZ0 (f …`. Introduce `φ s₀ sF hφt hφi hs₀ hsF`.

Take `⟨ψv, hψt, hψi, rfl⟩` from `hφ φ hφt hφi`. Take `⟨L, hfit, hLc, hLs, hLn⟩` from `hL (Function.update ψ₁ v ψv) fun y hy => by`. Distinguish the cases in `h : y = v`. Substitute `h` using the available equality. Rewrite using `[Function.update_self]`.

Conclude with `⟨hψt, hψi⟩`. Rewrite using `[Function.update_of_ne h]`. Conclude with `⟨(hunit y hy).2.1, (hunit y hy).2.2.1⟩`. Establish `hLS : L.S = S` using `hfit.S_eq.trans hTS`. Take `⟨𝔢, 𝔣, h𝔢, h𝔣, hgeo⟩` from `hG L ν hν`.

Establish `heS : 𝔢.S = SE` using `Set.ext fun y => by rw [h𝔢.2.2.1, hLS]; rfl`. Establish `hfS : 𝔣.S = SF` using `Set.ext fun y => by rw [h𝔣.2.2.1, hLS]; rfl`. Take `⟨hAt', hc1, hc2⟩` from `hS' 𝔢.S fun y => by rw [h𝔢.2.2.1, hLS]`. Establish `hoff : OffFam F n 𝔢.S 𝔣.S Λ t`. Rewrite using `[heS, hfS]`.

Conclude with `hOffA SF ((S.finite_toSet.union (Set.finite_singleton q)).subset fun y hy => hy)`. Use `filter_upwards [hCI F E n _ hn hp.pos μE μF θ 𝔢 𝔣 _ hgeo Λ t hc1 hc2 hoff x hx] with j hj`. Rewrite using `[hOne E n _ hn μE θ 𝔢 V Λ t hV hVθ hAt' x j, hE L _ hfit _ 𝔢 h𝔢 (Function.update su v (r * s₀)) (fun y hy => by`. Distinguish the cases in `h : y = v`. Substitute `h` using the available equality.

Rewrite using `[Function.update_self, Function.update_self]`. Conclude with `htr _ _ hs₀`. Rewrite using `[Function.update_of_ne h, Function.update_of_ne h]`. Conclude with `(hsu y hy).2) j, heS, hfS,`. Use `hF L 𝔣 hLS (fun y hy => (hLc y hy).2) h𝔣 (fun i => Function.update (s₁ i) v (sF i)) (fun i y hy => by`.

Distinguish the cases in `h : y = v`. Substitute `h` using the available equality. Rewrite using `[Function.update_self, hLs y hvsp, Function.update_self]`. Conclude with `hsF i`. Rewrite using `[Function.update_of_ne h]`.

Establish `e : L.f y = L₁.f y`. Distinguish the cases in `hy' : GM.Split E y`. Establish `hys : y ∈ T.sp` using `Finset.mem_filter.2 ⟨hTS ▸ hy, hy'⟩`. Rewrite using `[hLs y hys, hL₁s y hys, Function.update_of_ne h]`. Rewrite using `[hLn y hy hy', hL₁n y hy hy']`.

Rewrite using `[e]`. Conclude with `hs₁ i y hy) j, hLS, Finset.prod_congr rfl fun y hy => (hLc y hy).1,`. Use the proof step `Finset.prod_update_of_mem hvsp, Finset.mul_sum] at hj`. Simplify using `only [Finset.prod_update_of_mem hvS, Finset.sdiff_singleton_eq_erase] at hj`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨Λ', t', hA, hΛ, ht⟩` from `(hι i).2.1`. Establish `hSFf : SF.Finite` using `(S.finite_toSet.union (Set.finite_singleton q)).subset fun y hy => hy`. Use `⟨V₀ i, Λ', t', (hι i).1, ⟨SF, hSFf, hA⟩, hΛ, ?_, τ₀ i v, (hι i).2.2.2 v, hiso _ hi⟩` and prove the remaining obligations. Take `⟨𝔢, -, h𝔢, -⟩` from `hG L₁ ν hν`. Establish `heS : 𝔢.S = SE` using `Set.ext fun y => by rw [h𝔢.2.2.1, hL₁S]; rfl`.

Conclude with `Filter.mem_of_superset (heS ▸ 𝔢.finS : SE.Finite).compl_mem_cofinite fun y hy => ht y hy`.
-/
theorem coreDesc_of (hAbs : AbsLast) (hPull : PullBack) (hUnit : UnitTrace) (hOne : OneTerm) (hSum : SideSum) (hPS : PickS)
    (hPI : PickInf) (hTy : TyEx) (hTE : TermE) (hGood : GoodEx) (hPl : Places) (hOcc : OccursBasics)
    (hEig : EigBasic) (hCI : CI) (hGM : GM.GM) : CoreDesc := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE _ μF _ θ hθ V Λ t hV hVθ hAt hOffA v w hv τ' hτ'
  obtain ⟨S, q, w₀, hvS, hqS, hq, hunr, hsph, hS'⟩ := hPS F E σ hσ hp n hn μE V Λ t hV hAt v
  have hne := (hPl F E hp).2.2.1
  obtain ⟨T, hTS, hmk, htyped, hrank, c, f₀, UF, hUF, hL⟩ := hTy F E σ hσ hp n hn μE V hV q w₀ hq S hqS hunr hsph
    (Function.update (fun u => (hne u).some) v w)
  have hw : T.mk' v = w := by rw [hmk, Function.update_self]
  clear hmk
  subst hw
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).1 htyped
  obtain ⟨m, hm, D, s, hs, νE, iE, νF, iF, b, a, aE, aF, hposition, harch, hAE, hAF, hpair, hua⟩ :=
    hPI F E σ hσ hp n hn μE μF u hu0
  letI : ∀ x : Pl E, MeasurableSpace (Gw n x) := fun _ => borel _
  haveI : ∀ x : Pl E, BorelSpace (Gw n x) := fun _ => ⟨rfl⟩
  letI : ∀ x : Pl F, MeasurableSpace (Gw n x) := fun _ => borel _
  haveI : ∀ x : Pl F, BorelSpace (Gw n x) := fun _ => ⟨rfl⟩
  have hmE : ∀ x : Pl E, ∃ mm : Measure (Gw n x), mm.IsHaarMeasure := fun x => (haar_norm E n x).imp fun _ h => h.1
  have hmF : ∀ x : Pl F, ∃ mm : Measure (Gw n x), mm.IsHaarMeasure ∧ mm (GLnLocal.integralGL (x.adicCompletion F) n) = 1 :=
    fun x => haar_norm F n x
  choose mE hmE using hmE
  choose mF hmF using hmF
  have hτ : ∀ x : Pl E, ∃ τ : SmIrr (Gw n x), Occurs μE V x τ := fun x => by
    haveI := hmE x
    exact (hOcc E n μE V x (mE x) hV).1
  choose τ₁ hτ₁ using hτ
  obtain ⟨τ, hτ, hτw⟩ : ∃ τ : ∀ x : Pl E, SmIrr (Gw n x), (∀ x, Occurs μE V x (τ x)) ∧ τ (T.mk' v).1 = τ' := by
    refine ⟨Function.update τ₁ (T.mk' v).1 τ', fun x => ?_, Function.update_self ..⟩
    by_cases h : x = (T.mk' v).1
    · subst h; rw [Function.update_self]; exact hτ'
    · rw [Function.update_of_ne h]; exact hτ₁ x
  subst hτw
  obtain ⟨ν, hν⟩ := hGood n hn
  obtain ⟨x, cE, Z₀, hx, hcE, hZ₀, hZ0, hE⟩ := hTE F E σ hσ hp n hn m hm μE θ hθ D s hs hposition νE νF b a aE aF harch q w₀ hq T V hV
    hVθ hrank ⟨u, hu, hua⟩ mE hmE τ hτ ν hν.1.antitone
  obtain ⟨κ, hκ, hG⟩ := hGM F E σ hσ hp n hn μE μF θ hθ q w₀ hq νE νF aE aF 1 one_pos hAE hAF hpair
  set SF : Set (Pl F) := {y | y ∈ S ∨ y = q} with hSF
  set SE : Set (Pl E) := {y | y.under (𝓞 F) ∈ SF} with hSE
  obtain ⟨ι, _, V₀, τ₀, bF, Z, hι, hF⟩ := hSum F E σ n (Module.finrank F E) hn μF νF mF hmF aF q w₀ S UF ν hν.1.antitone
    (fun V₀ => ∃ Λ' t', At μF SF V₀ Λ' t' ∧ Λ = bcInf Λ' ∧ ∀ y ∉ SE, t y = bcSat t' y) x hx
  have hvsp : v ∈ T.sp := Finset.mem_filter.2 ⟨hTS ▸ hvS, hv⟩
  obtain ⟨τv, r, hr, hiso, htr, hlev⟩ := hPull F E n v (T.mk' v) (hv _) (mF v) (mE _) (hmF v).1 (hmE _) (τ _)
  obtain ⟨hCO, hfix, hφ⟩ := hlev (T.J _) (UF v) (T.co _) (hUF v hvsp)
  have hunit : ∀ y ∈ T.sp, _ := fun y hy => hUnit E n μE V hV (T.mk' y).1 (mE _) (hmE _) (τ _) (T.J _) (hτ _) (T.co _) (by
    refine (Submodule.ne_bot_iff _).2 ⟨u, ⟨hu.1, ?_⟩, hu0⟩
    have h1 : u ∈ eigL μE (T.mk' y).1 (T.J _) (T.χ _) := (Submodule.mem_iInf _).1 hu.2 _
    rw [T.triv y (Finset.mem_filter.1 hy).2 (T.mk' y)] at h1
    have h2 := T.chr (T.mk' y).1
    rw [T.triv y (Finset.mem_filter.1 hy).2 (T.mk' y)] at h2
    rwa [(hEig E n μE _ _ _ (T.co _) h2).2.1] at h1)
  have hsu : ∀ y : Pl F, ∃ z : ℂ, y ∈ T.sp → z ≠ 0 ∧ HasTrace (mE _) (τ (T.mk' y).1).ρ
      ((T.J (T.mk' y).1 : Set (Gw n (T.mk' y).1)).indicator 1) z := fun y => by
    by_cases hy : y ∈ T.sp
    · obtain ⟨z, hz⟩ := (hunit y hy).2.2.2
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose su hsu using hsu
  let ψ₁ : ∀ y : Pl F, Gw n (T.mk' y).1 → ℂ := fun y => (T.J (T.mk' y).1 : Set (Gw n (T.mk' y).1)).indicator 1
  obtain ⟨L₁, hfit₁, -, hL₁s, hL₁n⟩ := hL ψ₁ fun y hy => ⟨(hunit y hy).2.1, (hunit y hy).2.2.1⟩
  have hL₁S : L₁.S = S := hfit₁.S_eq.trans hTS
  have hs₁ : ∀ i (y : Pl F), ∃ z : ℂ, y ∈ S → HasTrace (mF y) (τ₀ i y).ρ (L₁.f y) z := fun i y => by
    by_cases hy : y ∈ S
    · haveI := (hmF y).1
      have ht := L₁.test y (hL₁S ▸ hy)
      obtain ⟨z, hz⟩ := (hOcc F n μF (V₀ i) y (mF y) (hι i).1).2.2 _ ((hι i).2.2.2 y) (L₁.f y) ⟨ht.2.2.1, ht.2.2.2⟩
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose s₁ hs₁ using hs₁
  haveI := (hmF v).1
  obtain ⟨i, hi⟩ := hAbs F n v (mF v) (UF v) hCO ι (fun i => τ₀ i v)
    (fun i => (κ * ∏ y ∈ S, c y) * bF i * ∏ y ∈ S.erase v, s₁ i y) Z τv (cE * r * ∏ y ∈ T.sp.erase v, su y) Z₀
    (mul_ne_zero (mul_ne_zero hcE hr) (Finset.prod_ne_zero_iff.2 fun y hy => (hsu y (Finset.mem_of_mem_erase hy)).1))
    hZ₀ hZ0 (fun i => (hι i).2.2.1) (hfix (hunit v hvsp).1) (by
      intro φ s₀ sF hφt hφi hs₀ hsF
      obtain ⟨ψv, hψt, hψi, rfl⟩ := hφ φ hφt hφi
      obtain ⟨L, hfit, hLc, hLs, hLn⟩ := hL (Function.update ψ₁ v ψv) fun y hy => by
        by_cases h : y = v
        · subst h; rw [Function.update_self]; exact ⟨hψt, hψi⟩
        · rw [Function.update_of_ne h]; exact ⟨(hunit y hy).2.1, (hunit y hy).2.2.1⟩
      have hLS : L.S = S := hfit.S_eq.trans hTS
      obtain ⟨𝔢, 𝔣, h𝔢, h𝔣, hgeo⟩ := hG L ν hν
      have heS : 𝔢.S = SE := Set.ext fun y => by rw [h𝔢.2.2.1, hLS]; rfl
      have hfS : 𝔣.S = SF := Set.ext fun y => by rw [h𝔣.2.2.1, hLS]; rfl
      obtain ⟨hAt', hc1, hc2⟩ := hS' 𝔢.S fun y => by rw [h𝔢.2.2.1, hLS]
      have hoff : OffFam F n 𝔢.S 𝔣.S Λ t := by
        rw [heS, hfS]
        exact hOffA SF ((S.finite_toSet.union (Set.finite_singleton q)).subset fun y hy => hy)
      filter_upwards [hCI F E n _ hn hp.pos μE μF θ 𝔢 𝔣 _ hgeo Λ t hc1 hc2 hoff x hx] with j hj
      rw [hOne E n _ hn μE θ 𝔢 V Λ t hV hVθ hAt' x j,
        hE L _ hfit _ 𝔢 h𝔢 (Function.update su v (r * s₀)) (fun y hy => by
          by_cases h : y = v
          · subst h; rw [Function.update_self, Function.update_self]; exact htr _ _ hs₀
          · rw [Function.update_of_ne h, Function.update_of_ne h]; exact (hsu y hy).2) j, heS, hfS,
        hF L 𝔣 hLS (fun y hy => (hLc y hy).2) h𝔣 (fun i => Function.update (s₁ i) v (sF i)) (fun i y hy => by
          by_cases h : y = v
          · subst h
            rw [Function.update_self, hLs y hvsp, Function.update_self]; exact hsF i
          · rw [Function.update_of_ne h]
            have e : L.f y = L₁.f y := by
              by_cases hy' : GM.Split E y
              · have hys : y ∈ T.sp := Finset.mem_filter.2 ⟨hTS ▸ hy, hy'⟩
                rw [hLs y hys, hL₁s y hys, Function.update_of_ne h]
              · rw [hLn y hy hy', hL₁n y hy hy']
            rw [e]; exact hs₁ i y hy) j, hLS, Finset.prod_congr rfl fun y hy => (hLc y hy).1,
        Finset.prod_update_of_mem hvsp, Finset.mul_sum] at hj
      simp only [Finset.prod_update_of_mem hvS, Finset.sdiff_singleton_eq_erase] at hj
      calc _ = cE * (Z₀.map (· ^ j)).sum * (r * s₀ * ∏ y ∈ T.sp.erase v, su y) := by ring
        _ = _ := hj
        _ = _ := Finset.sum_congr rfl fun i _ => by ring)
  obtain ⟨Λ', t', hA, hΛ, ht⟩ := (hι i).2.1
  have hSFf : SF.Finite := (S.finite_toSet.union (Set.finite_singleton q)).subset fun y hy => hy
  refine ⟨V₀ i, Λ', t', (hι i).1, ⟨SF, hSFf, hA⟩, hΛ, ?_, τ₀ i v, (hι i).2.2.2 v, hiso _ hi⟩
  obtain ⟨𝔢, -, h𝔢, -⟩ := hG L₁ ν hν
  have heS : 𝔢.S = SE := Set.ext fun y => by rw [h𝔢.2.2.1, hL₁S]; rfl
  exact Filter.mem_of_superset (heS ▸ 𝔢.finS : SE.Finite).compl_mem_cofinite fun y hy => ht y hy

end UpperTheory.ConvolutionTheory.T
