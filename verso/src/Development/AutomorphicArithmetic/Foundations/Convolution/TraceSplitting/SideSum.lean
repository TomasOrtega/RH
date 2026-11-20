import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.ListProdStable
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.ExistsPowerSums
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursBasics
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.AmpFin

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical

/- English proof (translation)
Take `⟨hfd, rfl⟩` from `h`. Establish `hr : LinearMap.range (c • A) = LinearMap.range A` using `LinearMap.range_smul _ _ hc`. Establish `key : ∀ W : Submodule ℂ V, W = LinearMap.range A → ∀ h' : ∀ v ∈ W, (c • A) v ∈ W, LinearMap.trace ℂ W ((c • A).restrict h') = c * LinearMap.trace ℂ (LinearMap.range A) (A.restrict (p` using `LinearMap.range A) (q := LinearMap.range A) fun v _ => LinearMap.mem_range_self A v) := by`. Introduce and unpack `W rfl h'`. Establish `: (c • A).restrict h' = c • A.restrict (p` using `LinearMap.range A) (q := LinearMap.range A) (fun v _ => LinearMap.mem_range_self A v) := by`.

Use extensionality with `v`. Both sides reduce to the same expression. Rewrite using `[this, map_smul, smul_eq_mul]`. Conclude with `⟨hr ▸ hfd, key _ hr _⟩`.
-/
private theorem trace_range_smul {V : Type} [AddCommGroup V] [Module ℂ V] (A : V →ₗ[ℂ] V) {c s : ℂ} (hc : c ≠ 0)
    (h : HasFinTrace A s) : HasFinTrace (c • A) (c * s) := by
  obtain ⟨hfd, rfl⟩ := h
  have hr : LinearMap.range (c • A) = LinearMap.range A := LinearMap.range_smul _ _ hc
  have key : ∀ W : Submodule ℂ V, W = LinearMap.range A → ∀ h' : ∀ v ∈ W, (c • A) v ∈ W,
      LinearMap.trace ℂ W ((c • A).restrict h') = c * LinearMap.trace ℂ (LinearMap.range A)
        (A.restrict (p := LinearMap.range A) (q := LinearMap.range A) fun v _ => LinearMap.mem_range_self A v) := by
    rintro W rfl h'
    have : (c • A).restrict h' = c • A.restrict (p := LinearMap.range A) (q := LinearMap.range A)
        (fun v _ => LinearMap.mem_range_self A v) := by
      ext v
      rfl
    rw [this, map_smul, smul_eq_mul]
  exact ⟨hr ▸ hfd, key _ hr _⟩

/- English proof (translation)
Take `⟨A, hA, hT⟩` from `h`. Establish `hr : (d.toReal : ℂ) ≠ 0`. Conclude with `(ENNReal.toReal_pos h0 ht).ne'` after adjusting the coercions. Use `⟨((d.toReal : ℂ))⁻¹ • A, fun v l => ?_, trace_range_smul A (inv_ne_zero hr) hT⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hA v l`.

Use `⟨(integrable_smul_measure h0 ht).1 h1, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, map_smul, h2, integral_smul_measure, smul_eq_mul, Complex.real_smul, inv_mul_cancel_left₀ hr]`.
-/
private theorem hasTrace_of_smul {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    {m : Measure G} {ρ : Representation ℂ G V} {f : G → ℂ} {s : ℂ} {d : ENNReal} (h0 : d ≠ 0) (ht : d ≠ ⊤)
    (h : HasTrace (d • m) ρ f s) : HasTrace m ρ f (((d.toReal : ℂ))⁻¹ * s) := by
  obtain ⟨A, hA, hT⟩ := h
  have hr : (d.toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos h0 ht).ne'
  refine ⟨((d.toReal : ℂ))⁻¹ • A, fun v l => ?_, trace_range_smul A (inv_ne_zero hr) hT⟩
  obtain ⟨h1, h2⟩ := hA v l
  refine ⟨(integrable_smul_measure h0 ht).1 h1, ?_⟩
  rw [LinearMap.smul_apply, map_smul, h2, integral_smul_measure, smul_eq_mul, Complex.real_smul, inv_mul_cancel_left₀ hr]

/- English proof (translation)
Take `⟨A, hA, hfd, -⟩` from `h`. Establish `hr : ((m (I : Set G)).toReal : ℂ) ≠ 0`. Conclude with `(ENNReal.toReal_pos h0 ht).ne'` after adjusting the coercions. Establish `hfix : ∀ v ∈ fixedVectors ρ I, A v = ((m (I : Set G)).toReal : ℂ) • v`. Introduce `v hv`.

Rewrite using `[← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]`. Introduce `l`. Rewrite using `[map_sub, sub_eq_zero, (hA v l).2, map_smul, smul_eq_mul]`. Establish `e : (fun g => (I : Set G).indicator (1 : G → ℂ) g * l (ρ g v)) = (I : Set G).indicator fun _ => l v`. Use function extensionality and compare the values at `g`.

Distinguish the cases in `hg : g ∈ (I : Set G)`. Establish `: ρ g v = v` using `hv g hg`. Simplify using `[hg, this]`. Simplify using `[hg]`. Rewrite using `[e, integral_indicator hIm, setIntegral_const, measureReal_def, Complex.real_smul]`.

Establish `hle : fixedVectors ρ I ≤ LinearMap.range A`. Introduce `v hv`. Use `⟨((m (I : Set G)).toReal : ℂ)⁻¹ • v, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, hfix v hv, smul_smul, inv_mul_cancel₀ hr, one_smul]`. Conclude with `Submodule.finiteDimensional_of_le hle`.
-/
private theorem fd_of_trace {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    {m : Measure G} {ρ : Representation ℂ G V} {I : Subgroup G} {s : ℂ} (hIm : MeasurableSet (I : Set G))
    (h0 : m I ≠ 0) (ht : m I ≠ ⊤) (h : HasTrace m ρ ((I : Set G).indicator 1) s) :
    FiniteDimensional ℂ (fixedVectors ρ I) := by
  obtain ⟨A, hA, hfd, -⟩ := h
  have hr : ((m (I : Set G)).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos h0 ht).ne'
  have hfix : ∀ v ∈ fixedVectors ρ I, A v = ((m (I : Set G)).toReal : ℂ) • v := by
    intro v hv
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero, (hA v l).2, map_smul, smul_eq_mul]
    have e : (fun g => (I : Set G).indicator (1 : G → ℂ) g * l (ρ g v)) = (I : Set G).indicator fun _ => l v := by
      funext g
      by_cases hg : g ∈ (I : Set G)
      · have : ρ g v = v := hv g hg
        simp [hg, this]
      · simp [hg]
    rw [e, integral_indicator hIm, setIntegral_const, measureReal_def, Complex.real_smul]
  have hle : fixedVectors ρ I ≤ LinearMap.range A := by
    intro v hv
    refine ⟨((m (I : Set G)).toReal : ℂ)⁻¹ • v, ?_⟩
    rw [map_smul, hfix v hv, smul_smul, inv_mul_cancel₀ hr, one_smul]
  exact Submodule.finiteDimensional_of_le hle

/- English proof (translation)
Take `⟨hc, ho⟩` from `(UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test K n w).1`. Establish `hcl : IsClosed ((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w))` using `Subgroup.isClosed_of_isOpen _ ho`. Use `⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`.

Distinguish the cases in `hx : x ∈ ((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w))`. Use `filter_upwards [ho.mem_nhds hx] with y hy`. Rewrite using `[Set.indicator_of_mem hy, Set.indicator_of_mem hx]`. Both sides reduce to the same expression. Use `filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy`.

Rewrite using `[Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]`.
-/
private theorem test_ind {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) :
    Test (((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w)).indicator (1 : Gw n w → ℂ)) := by
  obtain ⟨hc, ho⟩ := (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test K n w).1
  have hcl : IsClosed ((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w)) :=
    Subgroup.isClosed_of_isOpen _ ho
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ ((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w))
  · filter_upwards [ho.mem_nhds hx] with y hy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    rfl
  · filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

/- English proof (translation)
Take `⟨hc, ho⟩` from `(UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test K n w).1`. Establish `hpos : m (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) ≠ 0` using `(ho.measure_pos m ⟨1, one_mem _⟩).ne'`. Establish `htop : m (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) ≠ ⊤` using `hc.measure_lt_top.ne`. Establish `hfd` using `fd_of_trace ho.measurableSet hpos htop h₀`. Use `set d : ENNReal := (m (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)))⁻¹ with hd`.

Establish `hd0 : d ≠ 0` using `ENNReal.inv_ne_zero.2 htop`. Establish `hdt : d ≠ ⊤` using `ENNReal.inv_ne_top.2 hpos`. Use `haveI : (d • m).IsHaarMeasure := Measure.IsHaarMeasure.smul m hd0 hdt`. Establish `h1 : (d • m) (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) = 1`. Rewrite using `[Measure.smul_apply, smul_eq_mul, hd, ENNReal.inv_mul_cancel hpos htop]`.

Take `⟨Z, hZ0, -, hZ⟩` from `UpperTheory.ConvolutionTheory.C.iwPow K n w (d • m) h1 σ ν hν hfd`. Conclude with `⟨_, Z, hZ0, fun j => hasTrace_of_smul hd0 hdt (hZ j)⟩`.
-/
private theorem iw_pow_at {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) [MeasurableSpace (Gw n w)]
    [BorelSpace (Gw n w)] (m : Measure (Gw n w)) [m.IsHaarMeasure] (σ : SmIrr (Gw n w)) (ν : Fin n → ℤ) (hν : Antitone ν)
    {s₀ : ℂ} (h₀ : HasTrace m σ.ρ (((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w)).indicator 1) s₀) :
    ∃ (c : ℂ) (Z : Multiset ℂ), 0 ∉ Z ∧ ∀ j : ℕ, HasTrace m σ.ρ ((GM.iwCoset w (j • ν)).indicator 1) (c * (Z.map (· ^ j)).sum) := by
  obtain ⟨hc, ho⟩ := (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test K n w).1
  have hpos : m (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) ≠ 0 :=
    (ho.measure_pos m ⟨1, one_mem _⟩).ne'
  have htop : m (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) ≠ ⊤ := hc.measure_lt_top.ne
  have hfd := fd_of_trace ho.measurableSet hpos htop h₀
  set d : ENNReal := (m (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)))⁻¹ with hd
  have hd0 : d ≠ 0 := ENNReal.inv_ne_zero.2 htop
  have hdt : d ≠ ⊤ := ENNReal.inv_ne_top.2 hpos
  haveI : (d • m).IsHaarMeasure := Measure.IsHaarMeasure.smul m hd0 hdt
  have h1 : (d • m) (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) = 1 := by
    rw [Measure.smul_apply, smul_eq_mul, hd, ENNReal.inv_mul_cancel hpos htop]
  obtain ⟨Z, hZ0, -, hZ⟩ := UpperTheory.ConvolutionTheory.C.iwPow K n w (d • m) h1 σ ν hν hfd
  exact ⟨_, Z, hZ0, fun j => hasTrace_of_smul hd0 hdt (hZ j)⟩

/- English proof (translation)
Substitute `h2 h3` using the available equality. Establish `: ∀ (ν' : Measure (archGroup K n)) (_ : ν'.IsHaarMeasure) (_ : ν' = ν) , Oinf μ ν' 𝔞.a₀ = Oinf μ ν 𝔞.a₀`. Introduce `ν' _ h`. Substitute `h` using the available equality. Both sides reduce to the same expression.

Conclude with `congrArg (· ∘L prj (fixF μ 𝔞.U)) (this 𝔞.ν 𝔞.haar h1)`.
-/
private theorem amp_A_eq {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (a : TI K n)
    (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)) (h1 : 𝔞.ν = ν) (h2 : 𝔞.a₀ = a) (h3 : 𝔞.U = U) :
    𝔞.A = Oinf μ ν a ∘L prj (fixF μ U) := by
  subst h2 h3
  have : ∀ (ν' : Measure (archGroup K n)) (_ : ν'.IsHaarMeasure) (_ : ν' = ν) , Oinf μ ν' 𝔞.a₀ = Oinf μ ν 𝔞.a₀ := by
    intro ν' _ h; subst h; rfl
  exact congrArg (· ∘L prj (fixF μ 𝔞.U)) (this 𝔞.ν 𝔞.haar h1)

/- English proof (translation)
Use `UpperTheory.trOn_eq_mul_of_eq_smul_on_subspace H ⊥ B B 0 inferInstance (fun v hv => by` as an intermediate fact. Rewrite using `[(Submodule.mem_bot ℂ).1 hv]`. Use the proof step `simp)`. Simplify using `using this`.
-/
private theorem trOn_bot' {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (B : H →L[ℂ] H) :
    trOn (⊥ : Submodule ℂ H) B = 0 := by
  have := UpperTheory.trOn_eq_mul_of_eq_smul_on_subspace H ⊥ B B 0 inferInstance (fun v hv => by
    rw [(Submodule.mem_bot ℂ).1 hv]; simp)
  simpa using this

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ σ n l hn μ _ ν _ _ _ m hm a q w₀ S UF e he p x hx`. Use `haveI hmH : ∀ v, (m v).IsHaarMeasure := fun v => (hm v).1`. Distinguish the cases in `hex : ∃ (L : GM.Loc σ n q w₀) (𝔣 : Side (Twist.id μ) l), L.S = S ∧ (∀ v ∈ S, L.UF v = UF v) ∧ GM.IsSideF L ν a e 𝔣`. Use `swap`. Use `⟨Empty, inferInstance, fun i => i.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim, ?_⟩` and prove the remaining obligations.

Introduce `L 𝔣 h1 h2 h3`. Conclude with `absurd ⟨L, 𝔣, h1, h2, h3⟩ hex`. Take `⟨L₀, 𝔣₀, hS₀, hU₀, hF₀⟩` from `hex`. Take `⟨κ, -, hT⟩` from `UpperTheory.ConvolutionTheory.C.termF F E σ n l hn μ ν m hm`. Establish `hfin` using `(UpperTheory.ConvolutionTheory.T.ampFin F n hn μ 𝔣₀.toAmp).1 x hx`.

Use `set P : Set (Submodule ℂ (LL μ)) := {V | IsSummand μ V ∧ eigIn V 𝔣₀.toAmp.A x ≠ ⊥ ∧ p V} with hP`. Establish `hPfin : P.Finite` using `hfin.subset fun V h => ⟨h.1, h.2.1⟩`. Establish `hτ : ∀ V : P, ∃ τ : ∀ v : Pl F, SmIrr (Gw n v), ∀ v, Occurs μ V.1 v (τ v)` using `fun V => by`. Use `fun v => (UpperTheory.ConvolutionTheory.C.occursBasics F n μ V.1 v (m v) V.2.1).1` as an intermediate fact. Use `choose τ hτ using this`.

Conclude with `⟨τ, hτ⟩`. Use `choose τ hτ using hτ`. Establish `hZ : ∀ V : P, ∃ (c : ℂ) (Z : Multiset ℂ), 0 ∉ Z ∧ ∀ j : ℕ, HasTrace (m q) (τ V q).ρ ((GM.iwCoset q (j • e)).indicator 1) (c * (Z.map (· ^ j)).sum)` using `fun V => by`. Take `⟨s₀, hs₀⟩` from `(UpperTheory.ConvolutionTheory.C.occursBasics F n μ V.1 q (m q) V.2.1).2.2 (τ V q) (hτ V q) _ (test_ind q)`. Conclude with `iw_pow_at q (m q) (τ V q) e he hs₀`.

Use `choose c Z hZ0 hZ using hZ`. Establish `hN` using `fun V : P => hT a q w₀ S V.1 (τ V) x V.2.1 hx (fun v _ => hτ V v)`. Use `choose N hN using hN`. Use `letI : Fintype P := hPfin.fintype`. Use `⟨P, inferInstance, fun V => V.1, τ, fun V => κ * x * N V * c V, Z, fun V => ⟨V.2.1, V.2.2.2, hZ0 V, hτ V⟩, ?_⟩` and prove the remaining obligations.

Introduce `L 𝔣 hS hU hF s hs j`. Establish `hUF : L.UF = L₀.UF`. Use function extensionality and compare the values at `v`. Distinguish the cases in `hv : v ∈ S`. Rewrite using `[hU v hv, hU₀ v hv]`.

Distinguish the cases in `hq : v = q`. Substitute `hq` using the available equality. Rewrite using `[L.at_q.2.2.2, L₀.at_q.2.2.2]`. Rewrite using `[(L.off v (hS ▸ hv) hq).2.2.2, (L₀.off v (hS₀ ▸ hv) hq).2.2.2]`. Establish `hA : 𝔣.toAmp.A = 𝔣₀.toAmp.A`.

Take `⟨h1, h2, -, h3, -, -⟩` from `hF`. Take `⟨h1', h2', -, h3', -, -⟩` from `hF₀`. Rewrite using `[amp_A_eq 𝔣.toAmp ν a _ h1 h2 h3, amp_A_eq 𝔣₀.toAmp ν a _ h1' h2' h3', hUF]`. Establish `hid : ∀ V : Submodule ℂ (LL μ), V.map ((Twist.id μ).U : LL μ →ₗ[ℂ] LL μ) = V` using `fun V => by`. Establish `: ((Twist.id μ).U : LL μ →ₗ[ℂ] LL μ) = LinearMap.id` using `LinearMap.ext fun _ => rfl`.

Rewrite using `[this, Submodule.map_id]`. Establish `hsum : 𝔣.tr p x j = ∑ᶠ V ∈ P, trOn (eigIn V 𝔣.toAmp.A x) ((𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∘L (Twist.id μ).U)`. Unfold `Side.tr`. Use `finsum_mem_inter_support_eq _ _ _ ?_` and prove the remaining obligations. Use extensionality with `V`.

Simplify using `only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.mem_support, hP]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, -, h3⟩, h4⟩`. Use `⟨⟨h1, fun h => h4 ?_, h3⟩, h4⟩` and prove the remaining obligations. Rewrite using `[hA, h, trOn_bot']`.

Introduce and unpack `⟨⟨h1, -, h3⟩, h4⟩`. Conclude with `⟨⟨h1, hid V, h3⟩, h4⟩`. Rewrite using `[hsum, ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]`. Use `Finset.sum_congr rfl fun V _ => ?_` and prove the remaining obligations. Rewrite using `[(hN V).2 L e 𝔣 hS he hF j _ (s V) (hZ V j) (hs V)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.ConvolutionTheory.T.sideSum :
    UpperTheory.ConvolutionTheory.T.SideSum := by
  intro F E _ _ _ _ _ _ σ n l hn μ _ ν _ _ _ m hm a q w₀ S UF e he p x hx
  haveI hmH : ∀ v, (m v).IsHaarMeasure := fun v => (hm v).1
  by_cases hex : ∃ (L : GM.Loc σ n q w₀) (𝔣 : Side (Twist.id μ) l), L.S = S ∧ (∀ v ∈ S, L.UF v = UF v) ∧ GM.IsSideF L ν a e 𝔣
  swap
  · refine ⟨Empty, inferInstance, fun i => i.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim, ?_⟩
    intro L 𝔣 h1 h2 h3
    exact absurd ⟨L, 𝔣, h1, h2, h3⟩ hex
  obtain ⟨L₀, 𝔣₀, hS₀, hU₀, hF₀⟩ := hex
  obtain ⟨κ, -, hT⟩ := UpperTheory.ConvolutionTheory.C.termF F E σ n l hn μ ν m hm
  have hfin := (UpperTheory.ConvolutionTheory.T.ampFin F n hn μ 𝔣₀.toAmp).1 x hx
  set P : Set (Submodule ℂ (LL μ)) := {V | IsSummand μ V ∧ eigIn V 𝔣₀.toAmp.A x ≠ ⊥ ∧ p V} with hP
  have hPfin : P.Finite := hfin.subset fun V h => ⟨h.1, h.2.1⟩
  have hτ : ∀ V : P, ∃ τ : ∀ v : Pl F, SmIrr (Gw n v), ∀ v, Occurs μ V.1 v (τ v) := fun V => by
    have := fun v => (UpperTheory.ConvolutionTheory.C.occursBasics F n μ V.1 v (m v) V.2.1).1
    choose τ hτ using this
    exact ⟨τ, hτ⟩
  choose τ hτ using hτ
  have hZ : ∀ V : P, ∃ (c : ℂ) (Z : Multiset ℂ), 0 ∉ Z ∧ ∀ j : ℕ,
      HasTrace (m q) (τ V q).ρ ((GM.iwCoset q (j • e)).indicator 1) (c * (Z.map (· ^ j)).sum) := fun V => by
    obtain ⟨s₀, hs₀⟩ := (UpperTheory.ConvolutionTheory.C.occursBasics F n μ V.1 q (m q) V.2.1).2.2 (τ V q) (hτ V q) _ (test_ind q)
    exact iw_pow_at q (m q) (τ V q) e he hs₀
  choose c Z hZ0 hZ using hZ
  have hN := fun V : P => hT a q w₀ S V.1 (τ V) x V.2.1 hx (fun v _ => hτ V v)
  choose N hN using hN
  letI : Fintype P := hPfin.fintype
  refine ⟨P, inferInstance, fun V => V.1, τ, fun V => κ * x * N V * c V, Z, fun V => ⟨V.2.1, V.2.2.2, hZ0 V, hτ V⟩, ?_⟩
  intro L 𝔣 hS hU hF s hs j
  have hUF : L.UF = L₀.UF := by
    funext v
    by_cases hv : v ∈ S
    · rw [hU v hv, hU₀ v hv]
    by_cases hq : v = q
    · subst hq
      rw [L.at_q.2.2.2, L₀.at_q.2.2.2]
    · rw [(L.off v (hS ▸ hv) hq).2.2.2, (L₀.off v (hS₀ ▸ hv) hq).2.2.2]
  have hA : 𝔣.toAmp.A = 𝔣₀.toAmp.A := by
    obtain ⟨h1, h2, -, h3, -, -⟩ := hF
    obtain ⟨h1', h2', -, h3', -, -⟩ := hF₀
    rw [amp_A_eq 𝔣.toAmp ν a _ h1 h2 h3, amp_A_eq 𝔣₀.toAmp ν a _ h1' h2' h3', hUF]
  have hid : ∀ V : Submodule ℂ (LL μ), V.map ((Twist.id μ).U : LL μ →ₗ[ℂ] LL μ) = V := fun V => by
    have : ((Twist.id μ).U : LL μ →ₗ[ℂ] LL μ) = LinearMap.id := LinearMap.ext fun _ => rfl
    rw [this, Submodule.map_id]
  have hsum : 𝔣.tr p x j = ∑ᶠ V ∈ P, trOn (eigIn V 𝔣.toAmp.A x) ((𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∘L (Twist.id μ).U) := by
    unfold Side.tr
    refine finsum_mem_inter_support_eq _ _ _ ?_
    ext V
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.mem_support, hP]
    constructor
    · rintro ⟨⟨h1, -, h3⟩, h4⟩
      refine ⟨⟨h1, fun h => h4 ?_, h3⟩, h4⟩
      rw [hA, h, trOn_bot']
    · rintro ⟨⟨h1, -, h3⟩, h4⟩
      exact ⟨⟨h1, hid V, h3⟩, h4⟩
  rw [hsum, ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun V _ => ?_
  rw [(hN V).2 L e 𝔣 hS he hF j _ (s V) (hZ V j) (hs V)]
  ring
