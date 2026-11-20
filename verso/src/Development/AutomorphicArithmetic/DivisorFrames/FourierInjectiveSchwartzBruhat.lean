import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceCharacterAnnihilatorCompact
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

/- English proof (translation)
Establish `hl : IsLocallyConstant (fun p : V × V => (f (p.1 + p.2), f p.1))` using `(h1.comp_continuous (continuous_fst.add continuous_snd)).prodMk (h1.comp_continuous continuous_fst)`. Establish `ho : IsOpen ((fun p : V × V => (f (p.1 + p.2), f p.1)) ⁻¹' {q | q.1 = q.2})` using `hl _`. Take `⟨u, v, -, hv, hu, h0, huv⟩` from `generalized_tube_lemma (s := tsupport f) (t := {(0 : V)}) h2 isCompact_singleton ho (by rintro ⟨x, y⟩ ⟨-, hy⟩; simp at hy; simp [hy])`. Use `⟨v, hv.mem_nhds (h0 rfl), fun M hM x m hm => ?_⟩` and prove the remaining obligations. Establish `key : ∀ x ∈ tsupport f, ∀ m ∈ M, f (x + m) = f x` using `fun x hx m hm => huv (Set.mk_mem_prod (hu hx) (hM hm))`.

Distinguish the cases in `hx : x ∈ tsupport f`. Conclude with `key x hx m hm`. Distinguish the cases in `hx' : x + m ∈ tsupport f`. Use `key _ hx' (-m) (M.neg_mem hm)` as an intermediate fact. Simplify using `using this.symm`.

Rewrite using `[image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']`.
-/
private theorem locally_constant_invariant_subgroup {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] {f : V → ℂ}
    (h1 : IsLocallyConstant f) (h2 : HasCompactSupport f) :
    ∃ U ∈ 𝓝 (0 : V), ∀ M : AddSubgroup V, (M : Set V) ⊆ U → ∀ x, ∀ m ∈ M, f (x + m) = f x := by
  have hl : IsLocallyConstant (fun p : V × V => (f (p.1 + p.2), f p.1)) :=
    (h1.comp_continuous (continuous_fst.add continuous_snd)).prodMk (h1.comp_continuous continuous_fst)
  have ho : IsOpen ((fun p : V × V => (f (p.1 + p.2), f p.1)) ⁻¹' {q | q.1 = q.2}) := hl _
  obtain ⟨u, v, -, hv, hu, h0, huv⟩ := generalized_tube_lemma (s := tsupport f) (t := {(0 : V)}) h2
    isCompact_singleton ho (by rintro ⟨x, y⟩ ⟨-, hy⟩; simp at hy; simp [hy])
  refine ⟨v, hv.mem_nhds (h0 rfl), fun M hM x m hm => ?_⟩
  have key : ∀ x ∈ tsupport f, ∀ m ∈ M, f (x + m) = f x := fun x hx m hm =>
    huv (Set.mk_mem_prod (hu hx) (hM hm))
  by_cases hx : x ∈ tsupport f
  · exact key x hx m hm
  by_cases hx' : x + m ∈ tsupport f
  · have := key _ hx' (-m) (M.neg_mem hm)
    simpa using this.symm
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

/- English proof (translation)
Rewrite using `[← integral_indicator hNo.measurableSet]`. Establish `h1` using `integral_add_right_eq_self (μ := μ) ((N : Set V).indicator χ) n`. Establish `h : ∀ y, (N : Set V).indicator χ (y + n) = χ n * (N : Set V).indicator χ y`. Introduce `y`. Distinguish the cases in `hy : y ∈ N`.

Rewrite using `[Set.indicator_of_mem (show y ∈ (N : Set V) from hy), Set.indicator_of_mem (show y + n ∈ (N : Set V) from N.add_mem hy hn), ha, mul_comm]`. Establish `: y + n ∉ N` using `fun h => hy (by simpa using N.sub_mem h hn)`. Rewrite using `[Set.indicator_of_notMem (show y ∉ (N : Set V) from hy), Set.indicator_of_notMem (show y + n ∉ (N : Set V) from this), mul_zero]`. Rewrite `h1` using `[h, integral_const_mul]`. Establish `: (χ n - 1) * ∫ x, (N : Set V).indicator χ x ∂μ = 0` using `by rw [sub_mul, h1]; ring`.

Conclude with `(mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hn1)`.
-/
private theorem abs_orth {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → ℂ)
    (ha : ∀ y y', χ (y + y') = χ y * χ y') (N : AddSubgroup V) (hNo : IsOpen (N : Set V))
    (n : V) (hn : n ∈ N) (hn1 : χ n ≠ 1) : ∫ y in (N : Set V), χ y ∂μ = 0 := by
  rw [← integral_indicator hNo.measurableSet]
  have h1 := integral_add_right_eq_self (μ := μ) ((N : Set V).indicator χ) n
  have h : ∀ y, (N : Set V).indicator χ (y + n) = χ n * (N : Set V).indicator χ y := by
    intro y
    by_cases hy : y ∈ N
    · rw [Set.indicator_of_mem (show y ∈ (N : Set V) from hy), Set.indicator_of_mem (show y + n ∈ (N : Set V) from N.add_mem hy hn), ha, mul_comm]
    · have : y + n ∉ N := fun h => hy (by simpa using N.sub_mem h hn)
      rw [Set.indicator_of_notMem (show y ∉ (N : Set V) from hy), Set.indicator_of_notMem (show y + n ∉ (N : Set V) from this), mul_zero]
  simp_rw [h, integral_const_mul] at h1
  have : (χ n - 1) * ∫ x, (N : Set V).indicator χ x ∂μ = 0 := by rw [sub_mul, h1]; ring
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hn1)

/- English proof (translation)
Take `⟨U, hU, hinv⟩` from `locally_constant_invariant_subgroup h1 h2`. Take `⟨N, hNo, hNc, hNU⟩` from `H U hU`. Set `M : AddSubgroup V` to `{ carrier := {s | ∀ t ∈ N, B t s = 1} zero_mem' := fun t _ => h0 t add_mem' := fun {a b} h h' t ht => by rw [ha', h t ht, h' t ht, one_mul] neg_mem' := fun {a} h t ht => by`. Use `ha' t a (-a)` as an intermediate fact. Rewrite `this` using `[add_neg_cancel, h0, h t ht, one_mul]`.

Conclude with `this.symm }`. Establish `hi` using `hinv M hNU`. Establish `hNpos : 0 < μ.real N` using `ENNReal.toReal_pos (hNo.measure_pos μ ⟨0, N.zero_mem⟩).ne' hNc.measure_lt_top.ne`. Establish `hNne : (μ.real N : ℂ) ≠ 0` using `by exact_mod_cast hNpos.ne'`. Establish `hg : ∀ s, ∫ t in (N : Set V), B t s ∂μ = (M : Set V).indicator (fun _ => (μ.real N : ℂ)) s`.

Introduce `s`. Distinguish the cases in `hs : s ∈ M`. Rewrite using `[Set.indicator_of_mem (by exact hs), setIntegral_congr_fun hNo.measurableSet (g := fun _ => (1 : ℂ)) (fun t ht => hs t ht)]`. Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_of_notMem (by exact hs)]`.

Establish `hs' : ¬ ∀ t ∈ N, B t s = 1` using `hs`. Use `push Not at hs'`. Take `⟨n, hn, hn1⟩` from `hs'`. Conclude with `abs_orth μ (fun t => B t s) (fun y y' => ha y y' s) N hNo n hn hn1`. Establish `hgc : Continuous fun s => ∫ t in (N : Set V), B t s ∂μ` using `continuous_parametric_integral_of_continuous (f := fun s t => B t s) (hB.comp (f := fun p : V × V => (p.2, p.1)) (by fun_prop)) hNc`.

Establish `hMo : IsOpen (M : Set V)`. Establish `: (M : Set V) = (fun s => ∫ t in (N : Set V), B t s ∂μ) ⁻¹' {0}ᶜ`. Use extensionality with `s`. Distinguish the cases in `hs : s ∈ M`. Simplify using `[hg, hs, hNpos.ne']`.

Simplify using `[hg, hs]`. Rewrite using `[this]`. Conclude with `isOpen_compl_singleton.preimage hgc`. Use function extensionality and compare the values at `z`. Establish `e1 : ∫ t in (N : Set V), ∫ s, f s * B t (s + -z) ∂μ ∂μ = 0`.

Establish `: ∀ t, ∫ s, f s * B t (s + -z) ∂μ = 0` using `fun t => by`. Repeatedly rewrite using `[ha', ← mul_assoc]`. Rewrite using `[integral_mul_const, hF, zero_mul]`. Simplify using `[this]`. Establish `hint : Integrable (Function.uncurry fun t s => f s * B t (s + -z)) ((μ.restrict N).prod μ)`.

Establish `hc : Continuous (Function.uncurry fun t s => f s * B t (s + -z))` using `(h1.continuous.comp continuous_snd).mul (hB.comp (f := fun p : V × V => (p.1, p.2 + -z)) (by fun_prop))`. Establish `h3 : IntegrableOn (Function.uncurry fun t s => f s * B t (s + -z)) ((N : Set V) ×ˢ tsupport f) (μ.prod μ)` using `hc.continuousOn.integrableOn_compact (hNc.prod h2)`. Establish `h4 : IntegrableOn (Function.uncurry fun t s => f s * B t (s + -z)) ((N : Set V) ×ˢ Set.univ) (μ.prod μ)`. Use `h3.of_forall_diff_eq_zero (hNo.measurableSet.prod MeasurableSet.univ) ?_` and prove the remaining obligations. Introduce and unpack `⟨t, s⟩ ⟨⟨ht, -⟩, h⟩`.

Establish `: s ∉ tsupport f` using `fun hs => h ⟨ht, hs⟩`. Simplify using `[Function.uncurry, image_eq_zero_of_notMem_tsupport this]`. Rewrite `h4` using `[IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ]`. Conclude with `h4`. Rewrite `e1` using `[integral_integral_swap hint]`.

Rewrite `e1` using `[integral_const_mul, hg]`. Establish `e2 : ∀ s, f s * (M : Set V).indicator (fun _ => (μ.real N : ℂ)) (s + -z) = (M : Set V).indicator (fun _ => f z * (μ.real N : ℂ)) (s + -z)`. Introduce `s`. Distinguish the cases in `hs : s + -z ∈ M`. Rewrite using `[Set.indicator_of_mem (by exact hs), Set.indicator_of_mem (by exact hs), ← hi z _ hs]`.

Use `congr 2`. Normalize the expressions using the abelian group laws. Rewrite using `[Set.indicator_of_notMem (by exact hs), Set.indicator_of_notMem (by exact hs), mul_zero]`. Establish `hI : Integrable (fun s => f s * (M : Set V).indicator (fun _ => (μ.real N : ℂ)) (s + -z)) μ`. Use `hint.integral_prod_right` as an intermediate fact.

Simplify `this` using `only [Function.uncurry, integral_const_mul, hg]`. Rewrite `e1`, `hI` using `[e2]`. Assume the negation of the conclusion as `hz`. Establish `hz' : f z * (μ.real N : ℂ) ≠ 0` using `mul_ne_zero hz hNne`. Rewrite `e1` using `[integral_add_right_eq_self (μ := μ) ((M : Set V).indicator (fun _ => f z * (μ.real N : ℂ))) (-z), integral_indicator_const _ hMo.measurableSet]`.

Establish `hI' : Integrable ((M : Set V).indicator (fun _ => f z * (μ.real N : ℂ))) μ`. Use `hI.comp_add_right z` as an intermediate fact. Simplify using `using this`. Rewrite `hI'` using `[integrable_indicator_iff hMo.measurableSet, integrableOn_const_iff]`. Establish `hfin : μ M < ⊤` using `hI'.resolve_left (by simpa using hz')`.

Establish `hMpos : 0 < μ.real M` using `ENNReal.toReal_pos (hMo.measure_pos μ ⟨0, M.zero_mem⟩).ne' hfin.ne`. Conclude with `hz' ((smul_eq_zero.1 e1).resolve_left hMpos.ne')`.
-/
private theorem abs_inj {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (B : V → V → ℂ)
    (hB : Continuous (fun p : V × V => B p.1 p.2))
    (ha : ∀ x x' y, B (x + x') y = B x y * B x' y) (ha' : ∀ x y y', B x (y + y') = B x y * B x y')
    (h0 : ∀ x, B x 0 = 1)
    (H : ∀ U ∈ 𝓝 (0 : V), ∃ N : AddSubgroup V, IsOpen (N : Set V) ∧ IsCompact (N : Set V) ∧
      ∀ s, (∀ t ∈ N, B t s = 1) → s ∈ U)
    (f : V → ℂ) (h1 : IsLocallyConstant f) (h2 : HasCompactSupport f)
    (hF : ∀ t, ∫ s, f s * B t s ∂μ = 0) : f = 0 := by
  classical
  obtain ⟨U, hU, hinv⟩ := locally_constant_invariant_subgroup h1 h2
  obtain ⟨N, hNo, hNc, hNU⟩ := H U hU
  let M : AddSubgroup V :=
    { carrier := {s | ∀ t ∈ N, B t s = 1}
      zero_mem' := fun t _ => h0 t
      add_mem' := fun {a b} h h' t ht => by rw [ha', h t ht, h' t ht, one_mul]
      neg_mem' := fun {a} h t ht => by
        have := ha' t a (-a)
        rw [add_neg_cancel, h0, h t ht, one_mul] at this
        exact this.symm }
  have hi := hinv M hNU
  have hNpos : 0 < μ.real N := ENNReal.toReal_pos (hNo.measure_pos μ ⟨0, N.zero_mem⟩).ne' hNc.measure_lt_top.ne
  have hNne : (μ.real N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hg : ∀ s, ∫ t in (N : Set V), B t s ∂μ = (M : Set V).indicator (fun _ => (μ.real N : ℂ)) s := by
    intro s
    by_cases hs : s ∈ M
    · rw [Set.indicator_of_mem (by exact hs), setIntegral_congr_fun hNo.measurableSet (g := fun _ => (1 : ℂ))
        (fun t ht => hs t ht)]
      simp
    · rw [Set.indicator_of_notMem (by exact hs)]
      have hs' : ¬ ∀ t ∈ N, B t s = 1 := hs
      push Not at hs'
      obtain ⟨n, hn, hn1⟩ := hs'
      exact abs_orth μ (fun t => B t s) (fun y y' => ha y y' s) N hNo n hn hn1
  have hgc : Continuous fun s => ∫ t in (N : Set V), B t s ∂μ :=
    continuous_parametric_integral_of_continuous (f := fun s t => B t s)
      (hB.comp (f := fun p : V × V => (p.2, p.1)) (by fun_prop)) hNc
  have hMo : IsOpen (M : Set V) := by
    have : (M : Set V) = (fun s => ∫ t in (N : Set V), B t s ∂μ) ⁻¹' {0}ᶜ := by
      ext s
      by_cases hs : s ∈ M
      · simp [hg, hs, hNpos.ne']
      · simp [hg, hs]
    rw [this]
    exact isOpen_compl_singleton.preimage hgc
  funext z
  have e1 : ∫ t in (N : Set V), ∫ s, f s * B t (s + -z) ∂μ ∂μ = 0 := by
    have : ∀ t, ∫ s, f s * B t (s + -z) ∂μ = 0 := fun t => by
      simp_rw [ha', ← mul_assoc]
      rw [integral_mul_const, hF, zero_mul]
    simp [this]
  have hint : Integrable (Function.uncurry fun t s => f s * B t (s + -z)) ((μ.restrict N).prod μ) := by
    have hc : Continuous (Function.uncurry fun t s => f s * B t (s + -z)) :=
      (h1.continuous.comp continuous_snd).mul (hB.comp (f := fun p : V × V => (p.1, p.2 + -z)) (by fun_prop))
    have h3 : IntegrableOn (Function.uncurry fun t s => f s * B t (s + -z)) ((N : Set V) ×ˢ tsupport f) (μ.prod μ) :=
      hc.continuousOn.integrableOn_compact (hNc.prod h2)
    have h4 : IntegrableOn (Function.uncurry fun t s => f s * B t (s + -z)) ((N : Set V) ×ˢ Set.univ) (μ.prod μ) := by
      refine h3.of_forall_diff_eq_zero (hNo.measurableSet.prod MeasurableSet.univ) ?_
      rintro ⟨t, s⟩ ⟨⟨ht, -⟩, h⟩
      have : s ∉ tsupport f := fun hs => h ⟨ht, hs⟩
      simp [Function.uncurry, image_eq_zero_of_notMem_tsupport this]
    rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at h4
    exact h4
  rw [integral_integral_swap hint] at e1
  simp_rw [integral_const_mul, hg] at e1
  have e2 : ∀ s, f s * (M : Set V).indicator (fun _ => (μ.real N : ℂ)) (s + -z) =
      (M : Set V).indicator (fun _ => f z * (μ.real N : ℂ)) (s + -z) := by
    intro s
    by_cases hs : s + -z ∈ M
    · rw [Set.indicator_of_mem (by exact hs), Set.indicator_of_mem (by exact hs), ← hi z _ hs]
      congr 2; abel
    · rw [Set.indicator_of_notMem (by exact hs), Set.indicator_of_notMem (by exact hs), mul_zero]
  have hI : Integrable (fun s => f s * (M : Set V).indicator (fun _ => (μ.real N : ℂ)) (s + -z)) μ := by
    have := hint.integral_prod_right
    simpa only [Function.uncurry, integral_const_mul, hg] using this
  simp_rw [e2] at e1 hI
  by_contra hz
  have hz' : f z * (μ.real N : ℂ) ≠ 0 := mul_ne_zero hz hNne
  rw [integral_add_right_eq_self (μ := μ) ((M : Set V).indicator (fun _ => f z * (μ.real N : ℂ))) (-z),
    integral_indicator_const _ hMo.measurableSet] at e1
  have hI' : Integrable ((M : Set V).indicator (fun _ => f z * (μ.real N : ℂ))) μ := by
    have := hI.comp_add_right z
    simpa using this
  rw [integrable_indicator_iff hMo.measurableSet, integrableOn_const_iff] at hI'
  have hfin : μ M < ⊤ := hI'.resolve_left (by simpa using hz')
  have hMpos : 0 < μ.real M := ENNReal.toReal_pos (hMo.measure_pos μ ⟨0, M.zero_mem⟩).ne' hfin.ne
  exact hz' ((smul_eq_zero.1 e1).resolve_left hMpos.ne')

/- English proof (translation)
Introduce `F E _ _ _ _ _ v ψ hc hψ _ _ m _ T hT hF`. Use `haveI := GlobalTheory.LocTateInt.isTopologicalRing_Ev (E := E) v`. Use `haveI := GlobalTheory.LocTateInt.t2Space_Fv_tensor (E := E) v`. Use `haveI := GlobalTheory.LocTateInt.locallyCompactSpace_Ev (E := E) v`. Use `haveI := GlobalTheory.LocTateInt.secondCountable_Ev (E := E) v`.

Use `haveI := GlobalTheory.LocTateInt.isModuleTopology_Ev (E := E) v`. Use `haveI : (𝓝[≠] (0 : Fv F v)).NeBot := by`. Use `letI := Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))`. Conclude with `NormedField.nhdsNE_neBot 0`. Use `abs_inj m (fun t s => ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * s))) ?_ ?_ ?_ ?_ ?_ T hT.1 hT.2 hF` and prove the remaining obligations.

Conclude with `hc.comp ((IsModuleTopology.continuous_of_linearMap _).comp continuous_mul)`. Introduce `x x' y`. Simplify using `only [add_mul, map_add, AddChar.map_add_eq_mul]`. Introduce `x x' y`. Simplify using `only [mul_add, map_add, AddChar.map_add_eq_mul]`.

Introduce `x`. Simplify using the standard rewrite rules. Introduce `U hU`. Take `⟨h0c, h0o⟩` from `isCompact_isOpen_intLoc (E := E) v`. Establish `hK` using `GlobalTheory.TraceAnnCompact.isCompact_trace_ann v ψ hc hψ _ (h0o.mem_nhds (intLoc F E v).zero_mem)`.

Establish `hev` using `hK.eventually_forall_of_forall_eventually (x₀ := (0 : Fv F v)) (P := fun a y => a • y ∈ U) (fun y _ => (continuous_smul (M := Fv F v) (X := Fv F v ⊗[F] E)).continuousAt.preimage_mem_nhds (by simpa using hU))`. Take `⟨a, ha, ha0⟩` from `((hev.filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))).and self_mem_nhdsWithin).exists`. Establish `ha0' : a ≠ 0` using `ha0`. Use `⟨(intLoc F E v).toAddSubgroup.comap (DistribSMul.toAddMonoidHom _ a), ?_, ?_, fun s hs => ?_⟩` and prove the remaining obligations. Conclude with `h0o.preimage (continuous_const_smul a)`.

Conclude with `(Homeomorph.smulOfNeZero a ha0').isCompact_preimage.2 h0c`. Use `ha (a⁻¹ • s) fun t ht => by` as an intermediate fact. Establish `h` using `hs (a⁻¹ • t) (by show a • a⁻¹ • t ∈ intLoc F E v`. Rewrite using `[smul_inv_smul₀ ha0']`. Conclude with `ht)`.

Rewrite `h` using `[smul_mul_assoc, ← mul_smul_comm]`. Then use the resulting hypothesis. Rewrite `this` using `[smul_inv_smul₀ ha0']`. Then use the resulting hypothesis.
-/
theorem UpperTheory.fourier_injective_schwartz_bruhat :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
        ∀ [MeasurableSpace (Fv F v ⊗[F] E)] [BorelSpace (Fv F v ⊗[F] E)] (m : Measure (Fv F v ⊗[F] E)) [m.IsAddHaarMeasure], ∀ T ∈ SB (Fv F v ⊗[F] E), (∀ t, four v ψ m T t = 0) → T = 0 := by
  intro F E _ _ _ _ _ v ψ hc hψ _ _ m _ T hT hF
  haveI := GlobalTheory.LocTateInt.isTopologicalRing_Ev (E := E) v
  haveI := GlobalTheory.LocTateInt.t2Space_Fv_tensor (E := E) v
  haveI := GlobalTheory.LocTateInt.locallyCompactSpace_Ev (E := E) v
  haveI := GlobalTheory.LocTateInt.secondCountable_Ev (E := E) v
  haveI := GlobalTheory.LocTateInt.isModuleTopology_Ev (E := E) v
  haveI : (𝓝[≠] (0 : Fv F v)).NeBot := by
    letI := Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
    exact NormedField.nhdsNE_neBot 0
  refine abs_inj m (fun t s => ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * s))) ?_ ?_ ?_ ?_ ?_ T hT.1 hT.2 hF
  · exact hc.comp ((IsModuleTopology.continuous_of_linearMap _).comp continuous_mul)
  · intro x x' y
    simp only [add_mul, map_add, AddChar.map_add_eq_mul]
  · intro x x' y
    simp only [mul_add, map_add, AddChar.map_add_eq_mul]
  · intro x
    simp
  · intro U hU
    obtain ⟨h0c, h0o⟩ := isCompact_isOpen_intLoc (E := E) v
    have hK := GlobalTheory.TraceAnnCompact.isCompact_trace_ann v ψ hc hψ _ (h0o.mem_nhds (intLoc F E v).zero_mem)
    have hev := hK.eventually_forall_of_forall_eventually (x₀ := (0 : Fv F v)) (P := fun a y => a • y ∈ U)
      (fun y _ => (continuous_smul (M := Fv F v) (X := Fv F v ⊗[F] E)).continuousAt.preimage_mem_nhds
        (by simpa using hU))
    obtain ⟨a, ha, ha0⟩ := ((hev.filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))).and self_mem_nhdsWithin).exists
    have ha0' : a ≠ 0 := ha0
    refine ⟨(intLoc F E v).toAddSubgroup.comap (DistribSMul.toAddMonoidHom _ a), ?_, ?_, fun s hs => ?_⟩
    · exact h0o.preimage (continuous_const_smul a)
    · exact (Homeomorph.smulOfNeZero a ha0').isCompact_preimage.2 h0c
    · have := ha (a⁻¹ • s) fun t ht => by
        have h := hs (a⁻¹ • t) (by
          show a • a⁻¹ • t ∈ intLoc F E v
          rw [smul_inv_smul₀ ha0']; exact ht)
        rwa [smul_mul_assoc, ← mul_smul_comm] at h
      rwa [smul_inv_smul₀ ha0'] at this
