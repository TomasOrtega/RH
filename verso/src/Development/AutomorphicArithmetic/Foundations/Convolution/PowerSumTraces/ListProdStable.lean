import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OfinProd
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactorAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OlocEx
import Development.AutomorphicArithmetic.TwistedTraces.UiwPowCompEqOfAntitone
import Development.AutomorphicArithmetic.TwistedTraces.IwahoriCompactOpenAndIwCosetIndicatorTest
import Development.AutomorphicArithmetic.TwistedTraces.EigenspaceCompLevelProjectionEqInfFixed
import Development.AutomorphicArithmetic.TwistedTraces.EigenspaceInfSphericalLeClosedInvariant
import Development.AutomorphicArithmetic.TwistedTraces.TrOnEqMulOfEqSmulOnSubspace
import Development.AutomorphicArithmetic.TwistedTraces.LocalHeckeOperatorMemOfClosedInvariant
import Development.AutomorphicArithmetic.TwistedTraces.ExistsPosConstProdLocalHeckeOperators
import Development.AutomorphicArithmetic.TwistedTraces.FiniteDimensionalEigenspaceInfFixedCompactOpen

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C
open scoped Classical

/- English proof (translation)
Use `⟨S.card, Fin.cons q fun i => (S.equivFin.symm i).1, rfl, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `Fin.cons_injective_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨i, hi⟩`. Conclude with `hq (hi ▸ (S.equivFin.symm i).2)`. Introduce `i j h`.

Conclude with `S.equivFin.symm.injective (Subtype.ext h)`. Use extensionality with `v`. Simplify using `only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(h | ⟨i, h⟩)`.

Conclude with `Or.inl h.symm`. Conclude with `Or.inr (h ▸ (S.equivFin.symm i).2)`. Introduce and unpack `(h | h)`. Conclude with `Or.inl h.symm`. Conclude with `Or.inr ⟨S.equivFin ⟨v, h⟩, by simp⟩`.

Introduce `s`. Simplify using `only [Fin.cons_succ]`. Rewrite using `[Equiv.prod_comp S.equivFin.symm (fun v : S => s v)]`. Conclude with `Finset.prod_coe_sort S s`.
-/
private theorem exists_enum {α : Type} (q : α) (S : Finset α) (hq : q ∉ S) :
    ∃ (r : ℕ) (w : Fin (r + 1) → α), w 0 = q ∧ Function.Injective w ∧ Finset.univ.image w = insert q S ∧
      ∀ s : α → ℂ, ∏ i : Fin r, s (w i.succ) = ∏ v ∈ S, s v := by
  refine ⟨S.card, Fin.cons q fun i => (S.equivFin.symm i).1, rfl, ?_, ?_, ?_⟩
  · refine Fin.cons_injective_iff.2 ⟨?_, ?_⟩
    · rintro ⟨i, hi⟩
      exact hq (hi ▸ (S.equivFin.symm i).2)
    · intro i j h
      exact S.equivFin.symm.injective (Subtype.ext h)
  · ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Fin.exists_fin_succ, Fin.cons_zero,
      Fin.cons_succ]
    constructor
    · rintro (h | ⟨i, h⟩)
      · exact Or.inl h.symm
      · exact Or.inr (h ▸ (S.equivFin.symm i).2)
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr ⟨S.equivFin ⟨v, h⟩, by simp⟩
  · intro s
    simp only [Fin.cons_succ]
    rw [Equiv.prod_comp S.equivFin.symm (fun v : S => s v)]
    exact Finset.prod_coe_sort S s

/- English proof (translation)
The claim follows from `Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure V hv)`.
-/
private theorem prj_self {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) {v : H} (hv : v ∈ V) : prj V v = v :=
  Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure V hv)

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => intro v hv`. Simplify using `using hv`. Consider the case `cons T l ih`. Introduce `v hv`.

Rewrite using `[List.prod_cons]`. Conclude with `h T (by simp) _ (ih (fun T' hT' => h T' (by simp [hT'])) v hv)`.
-/
private theorem list_prod_stable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Z : Submodule ℂ H) (l : List (H →L[ℂ] H)) (h : ∀ T ∈ l, ∀ v ∈ Z, T v ∈ Z) : ∀ v ∈ Z, l.prod v ∈ Z := by
  induction l with
  | nil => intro v hv; simpa using hv
  | cons T l ih =>
    intro v hv
    rw [List.prod_cons]
    exact h T (by simp) _ (ih (fun T' hT' => h T' (by simp [hT'])) v hv)

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
Introduce `F E _ _ _ _ _ _ σ n l hn μ _ ν _ _ _ m hm`. Use `haveI hmH : ∀ v, (m v).IsHaarMeasure := fun v => (hm v).1`. Take `⟨κ, hκ, hR⟩` from `UpperTheory.exists_pos_const_prod_localHeckeOperators F n hn μ ν`. Use `⟨κ, hκ, ?_⟩` and prove the remaining obligations. Introduce `a q w₀ S V τ x hV hx hocc`.

Distinguish the cases in `hq : q ∈ S`. Use `⟨if eigIn V (Oinf μ ν a) x ⊓ sphOff μ (insert q S) ≠ ⊥ then 1 else 0, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `split_ifs with h <;> simp [h]`. Introduce `L e 𝔣 hS`. Conclude with `absurd (hS ▸ hq) L.q_not`.

Take `⟨r, w, rfl, hw, himg, hprod⟩` from `exists_enum q S hq`. Rewrite `hocc`, the goal using `[← himg]`. Establish `hmemP : ∀ i, w i ∈ Finset.univ.image w` using `fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)`. Establish `hmemS : ∀ i : Fin r, w i.succ ∈ S`. Introduce `i`.

Establish `h` using `hmemP i.succ`. Rewrite `h` using `[himg]`. Break down `Finset.mem_insert.1 h with h | h` into its components or cases. Conclude with `absurd (hw h) (Fin.succ_ne_zero i)`. Conclude with `h`.

Establish `hocc' : ∀ i, Occurs μ V (w i) (τ (w i))` using `fun i => hocc _ (hmemP i)`. Use `set Z := eigIn V (Oinf μ ν a) x ⊓ sphOff μ (Finset.univ.image w) with hZdef`. Establish `key : ∀ (L : Loc σ n (w 0) w₀) (e : Fin n → ℤ) (𝔣 : Side (Twist.id μ) l), L.S = S → IsSideF L ν a e 𝔣 → eigIn V 𝔣.toAmp.A x = Z ⊓ ⨅ i, fixL μ (w i) (L.UF (w i))`. Introduce `L e 𝔣 hS hF`. Take `⟨hν, ha, -, hU, -, -⟩` from `hF`.

Establish `hlev : levF L.UF = levOn (Finset.univ.image w) L.UF`. Unfold `levOn`. Use `congr 1`. Use function extensionality and compare the values at `v`. Use `split_ifs with h`.

Both sides reduce to the same expression. Rewrite `h` using `[himg, Finset.mem_insert, not_or]`. Conclude with `(L.off v (hS ▸ h.2) h.1).2.2.2`. Rewrite using `[amp_A_eq 𝔣.toAmp ν a _ hν ha (hU.trans hlev), UpperTheory.eigenspace_comp_levelProjection_eq_inf_fixed F n hn μ ν V a x _ L.UF hx.ne']`. Use `congr 1`.

Use `le_antisymm (le_iInf fun i => iInf₂_le (w i) (hmemP i)) (le_iInf₂ fun v hv => ?_)` and prove the remaining obligations. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hv`. Conclude with `iInf_le _ i`. Distinguish the cases in `hZ : Z = ⊥`. Use `⟨0, by simp [hZ], ?_⟩` and prove the remaining obligations.

Introduce `L e 𝔣 hS he hF j sq s hsq hs`. Establish `hW : eigIn V 𝔣.toAmp.A x = ⊥` using `by rw [key L e 𝔣 hS hF, hZ, bot_inf_eq]`. Establish `h0 : ∀ B : LL μ →L[ℂ] LL μ, trOn (⊥ : Submodule ℂ (LL μ)) B = 0`. Introduce `B`. Use `UpperTheory.trOn_eq_mul_of_eq_smul_on_subspace (LL μ) ⊥ B B 0 inferInstance (fun v hv => by` as an intermediate fact.

Rewrite using `[(Submodule.mem_bot ℂ).1 hv]`. Use the proof step `simp)`. Simplify using `using this`. Rewrite using `[hW, h0]`. Simplify using the standard rewrite rules.

Take `⟨hZV, hZc, hZs⟩` from `UpperTheory.eigenspace_inf_spherical_le_closed_invariant F n hn μ ν V a x (Finset.univ.image w) hV`. Take `⟨N, hN, hfac⟩` from `UpperTheory.ConvolutionTheory.C.summandFactor F n μ V Z (r + 1) w (fun i => τ (w i)) hV hw hocc' hZV hZ hZc (fun i g v hv => hZs (w i) (hmemP i) g v hv) (fun U hU => UpperTheory.finiteDimensional_eigenspace_inf_fixed_compactOpen F n hn μ ν V a x (r + 1) w hV hx.ne' hw U hU)`. Use `⟨N, by simp [hN, hZ], ?_⟩` and prove the remaining obligations. Introduce `L e 𝔣 hS he hF j sq s hsq hs`. Establish `hW` using `key L e 𝔣 hS hF`.

Take `⟨hν, ha, -, hU, hg, hUq⟩` from `hF`. Establish `hiw` using `fun ν' => (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test F n (w 0)).2.2 ν'`. Establish `htest : ∀ i, Test (L.f (w i))`. Use `Fin.cases ?_ fun i => ?_` and prove the remaining obligations. Rewrite using `[L.at_q.2.1]`.

Conclude with `(hiw 0).1`. Establish `h` using `L.test _ (hS ▸ hmemS i)`. Conclude with `⟨h.2.2.1, h.2.2.2⟩`. Establish `hTex : ∀ i, ∃ T, IsOloc μ (w i) (m (w i)) (L.f (w i)) T` using `fun i => (UpperTheory.ConvolutionTheory.C.olocEx F n μ (w i) (m (w i)) _ (htest i)).exists`. Use `choose T hT using hTex`.

Take `⟨T₀, hT₀⟩` from `(UpperTheory.ConvolutionTheory.C.olocEx F n μ (w 0) (m (w 0)) _ (hiw (j • e)).1).exists`. Establish `hoff : ∀ v, v ∉ Set.range w → L.f v = (GLnLocal.integralGL (v.adicCompletion F) n : Set (Gw n v)).indicator 1`. Introduce `v hv`. Establish `h : v ∉ Finset.univ.image w` using `fun h => by`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 h`.

Conclude with `hv ⟨i, rfl⟩`. Rewrite `h` using `[himg, Finset.mem_insert, not_or]`. Conclude with `(L.off v (hS ▸ h.2) h.1).2.1`. Establish `hRR` using `hR a (r + 1) w (fun i => m (w i)) L.f T 𝔣.g hw (fun i => hm (w i)) htest hoff hT hg`. Set `Tc : Fin (r + 1) → LL μ →L[ℂ] LL μ` to `Fin.cons T₀ fun i => T i.succ`.

Set `φc : ∀ i, Gw n (w i) → ℂ` to `Fin.cons ((iwCoset (w 0) (j • e)).indicator 1) fun i => L.f (w i.succ)`. Set `sc : Fin (r + 1) → ℂ` to `Fin.cons sq fun i => s (w i.succ)`. Establish `hCO : ∀ i, CO (L.UF (w i))`. Use `Fin.cases ?_ fun i => ?_` and prove the remaining obligations. Rewrite using `[L.at_q.2.2.2]`.

Conclude with `(UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test F n (w 0)).1`. Establish `h` using `L.lev _ (hS ▸ hmemS i)`. Conclude with `(UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test F n (w i.succ)).2.1 _ h.2.2.1 h.2.2.2`. Establish `hfin` using `UpperTheory.finiteDimensional_eigenspace_inf_fixed_compactOpen F n hn μ ν V a x (r + 1) w hV hx.ne' hw (fun i => L.UF (w i)) hCO`. Establish `hf` using `hfac (fun i => L.UF (w i)) (fun i => m (w i)) φc Tc sc hCO (fun i => hmH _) (by`.

Use `Fin.cases ?_ fun i => ?_` and prove the remaining obligations. Conclude with `(hiw _).1`. Conclude with `htest i.succ)`. Use the proof step `(by`. Use `Fin.cases ?_ fun i => ?_` and prove the remaining obligations.

Introduce `u hu g`. Rewrite `hu` using `[L.at_q.2.2.2]`. Conclude with `(hiw _).2 u hu g`. Conclude with `(L.inv _ (hS ▸ hmemS i)).2)`. Use the proof step `(by`.

Use `Fin.cases ?_ fun i => ?_` and prove the remaining obligations. Conclude with `hT₀`. Conclude with `hT i.succ)`. Use the proof step `(by`. Use `Fin.cases ?_ fun i => ?_` and prove the remaining obligations.

Conclude with `hsq`. Conclude with `hs _ (hmemS i))`. Establish `hstep : (Uiw μ (w 0) e ^ j) ∘L T 0 = T₀` using `UpperTheory.Uiw_pow_comp_eq_of_antitone F n μ (w 0) (m (w 0)) e j (T 0) T₀ he (L.at_q.2.1 ▸ hT 0) hT₀`. Establish `hB : ∀ v ∈ Z ⊓ ⨅ i, fixL μ (w i) (L.UF (w i)), ((𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∘L (Twist.id μ).U) v = ((κ : ℂ) * (x : ℂ)) • (List.ofFn Tc).prod v`. Introduce `v hv`.

Establish `hv1 : v ∈ Z` using `hv.1`. Establish `hTp : (List.ofFn T).prod v ∈ Z`. Use `list_prod_stable Z _ (fun T' hT' u hu => ?_) v hv1` and prove the remaining obligations. Take `⟨i, rfl⟩` from `(List.mem_ofFn' _ _).1 hT'`. Conclude with `UpperTheory.localHeckeOperator_mem_of_closed_invariant F n μ (w i) (m (w i)) (L.f (w i)) (T i) Z hZc (fun g u hu => hZs (w i) (hmemP i) g u hu) (hT i) u hu`.

Establish `hO : Oinf μ ν a ((List.ofFn T).prod v) = (x : ℂ) • (List.ofFn T).prod v` using `Module.End.mem_eigenspace_iff.1 hTp.1.2`. Establish `hsph : v ∈ sphOff μ (Finset.univ.image w)` using `hv1.2`. Establish `hRg : Rop μ 𝔣.g v = (κ : ℂ) • ((x : ℂ) • (List.ofFn T).prod v)`. Establish `h1 : Rop μ 𝔣.g = RR μ 𝔣.g` using `rfl`. Rewrite using `[h1, hRR]`.

Simplify using `only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, prj_self _ hsph, hO]`. Establish `hc : (List.ofFn Tc).prod = T₀ * (List.ofFn fun i : Fin r => T i.succ).prod`. Rewrite using `[List.ofFn_succ, List.prod_cons]`. Both sides reduce to the same expression. Establish `hd : (List.ofFn T).prod = T 0 * (List.ofFn fun i : Fin r => T i.succ).prod`.

Rewrite using `[List.ofFn_succ, List.prod_cons]`. Establish `hid : (Twist.id μ).U v = v` using `rfl`. Establish `hstep' : ∀ y, (𝔣.Uq 0 ^ j) (T 0 y) = T₀ y` using `fun y => by`. Rewrite using `[hUq, ← hstep]`. Both sides reduce to the same expression.

Simplify using `only [ContinuousLinearMap.comp_apply, hid, hRg, map_smul, hc, hd, ContinuousLinearMap.mul_apply, hstep', smul_smul]`. Rewrite using `[hW, UpperTheory.trOn_eq_mul_of_eq_smul_on_subspace _ _ _ _ _ hfin hB, hf, Fin.prod_univ_succ]`. Establish `h1 : ∏ i : Fin r, sc i.succ = ∏ v ∈ S, s v` using `hprod s`. Establish `h2 : sc 0 = sq` using `rfl`. Rewrite using `[h1, h2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.ConvolutionTheory.C.termF :
    UpperTheory.ConvolutionTheory.C.TermF := by
  intro F E _ _ _ _ _ _ σ n l hn μ _ ν _ _ _ m hm
  haveI hmH : ∀ v, (m v).IsHaarMeasure := fun v => (hm v).1
  obtain ⟨κ, hκ, hR⟩ := UpperTheory.exists_pos_const_prod_localHeckeOperators F n hn μ ν
  refine ⟨κ, hκ, ?_⟩
  intro a q w₀ S V τ x hV hx hocc
  by_cases hq : q ∈ S
  · refine ⟨if eigIn V (Oinf μ ν a) x ⊓ sphOff μ (insert q S) ≠ ⊥ then 1 else 0, ?_, ?_⟩
    · split_ifs with h <;> simp [h]
    · intro L e 𝔣 hS
      exact absurd (hS ▸ hq) L.q_not
  obtain ⟨r, w, rfl, hw, himg, hprod⟩ := exists_enum q S hq
  rw [← himg] at hocc ⊢
  have hmemP : ∀ i, w i ∈ Finset.univ.image w := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hmemS : ∀ i : Fin r, w i.succ ∈ S := by
    intro i
    have h := hmemP i.succ
    rw [himg] at h
    rcases Finset.mem_insert.1 h with h | h
    · exact absurd (hw h) (Fin.succ_ne_zero i)
    · exact h
  have hocc' : ∀ i, Occurs μ V (w i) (τ (w i)) := fun i => hocc _ (hmemP i)
  set Z := eigIn V (Oinf μ ν a) x ⊓ sphOff μ (Finset.univ.image w) with hZdef
  have key : ∀ (L : Loc σ n (w 0) w₀) (e : Fin n → ℤ) (𝔣 : Side (Twist.id μ) l), L.S = S → IsSideF L ν a e 𝔣 →
      eigIn V 𝔣.toAmp.A x = Z ⊓ ⨅ i, fixL μ (w i) (L.UF (w i)) := by
    intro L e 𝔣 hS hF
    obtain ⟨hν, ha, -, hU, -, -⟩ := hF
    have hlev : levF L.UF = levOn (Finset.univ.image w) L.UF := by
      unfold levOn
      congr 1
      funext v
      split_ifs with h
      · rfl
      · rw [himg, Finset.mem_insert, not_or] at h
        exact (L.off v (hS ▸ h.2) h.1).2.2.2
    rw [amp_A_eq 𝔣.toAmp ν a _ hν ha (hU.trans hlev), UpperTheory.eigenspace_comp_levelProjection_eq_inf_fixed F n hn μ ν V a x _ L.UF hx.ne']
    congr 1
    refine le_antisymm (le_iInf fun i => iInf₂_le (w i) (hmemP i)) (le_iInf₂ fun v hv => ?_)
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
    exact iInf_le _ i
  by_cases hZ : Z = ⊥
  · refine ⟨0, by simp [hZ], ?_⟩
    intro L e 𝔣 hS he hF j sq s hsq hs
    have hW : eigIn V 𝔣.toAmp.A x = ⊥ := by rw [key L e 𝔣 hS hF, hZ, bot_inf_eq]
    have h0 : ∀ B : LL μ →L[ℂ] LL μ, trOn (⊥ : Submodule ℂ (LL μ)) B = 0 := by
      intro B
      have := UpperTheory.trOn_eq_mul_of_eq_smul_on_subspace (LL μ) ⊥ B B 0 inferInstance (fun v hv => by
        rw [(Submodule.mem_bot ℂ).1 hv]; simp)
      simpa using this
    rw [hW, h0]
    simp
  obtain ⟨hZV, hZc, hZs⟩ := UpperTheory.eigenspace_inf_spherical_le_closed_invariant F n hn μ ν V a x (Finset.univ.image w) hV
  obtain ⟨N, hN, hfac⟩ := UpperTheory.ConvolutionTheory.C.summandFactor F n μ V Z (r + 1) w (fun i => τ (w i)) hV hw hocc' hZV hZ hZc
    (fun i g v hv => hZs (w i) (hmemP i) g v hv)
    (fun U hU => UpperTheory.finiteDimensional_eigenspace_inf_fixed_compactOpen F n hn μ ν V a x (r + 1) w hV hx.ne' hw U hU)
  refine ⟨N, by simp [hN, hZ], ?_⟩
  intro L e 𝔣 hS he hF j sq s hsq hs
  have hW := key L e 𝔣 hS hF
  obtain ⟨hν, ha, -, hU, hg, hUq⟩ := hF
  have hiw := fun ν' => (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test F n (w 0)).2.2 ν'
  have htest : ∀ i, Test (L.f (w i)) := by
    refine Fin.cases ?_ fun i => ?_
    · rw [L.at_q.2.1]; exact (hiw 0).1
    · have h := L.test _ (hS ▸ hmemS i)
      exact ⟨h.2.2.1, h.2.2.2⟩
  have hTex : ∀ i, ∃ T, IsOloc μ (w i) (m (w i)) (L.f (w i)) T :=
    fun i => (UpperTheory.ConvolutionTheory.C.olocEx F n μ (w i) (m (w i)) _ (htest i)).exists
  choose T hT using hTex
  obtain ⟨T₀, hT₀⟩ := (UpperTheory.ConvolutionTheory.C.olocEx F n μ (w 0) (m (w 0)) _ (hiw (j • e)).1).exists
  have hoff : ∀ v, v ∉ Set.range w →
      L.f v = (GLnLocal.integralGL (v.adicCompletion F) n : Set (Gw n v)).indicator 1 := by
    intro v hv
    have h : v ∉ Finset.univ.image w := fun h => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      exact hv ⟨i, rfl⟩
    rw [himg, Finset.mem_insert, not_or] at h
    exact (L.off v (hS ▸ h.2) h.1).2.1
  have hRR := hR a (r + 1) w (fun i => m (w i)) L.f T 𝔣.g hw (fun i => hm (w i)) htest hoff hT hg
  let Tc : Fin (r + 1) → LL μ →L[ℂ] LL μ := Fin.cons T₀ fun i => T i.succ
  let φc : ∀ i, Gw n (w i) → ℂ := Fin.cons ((iwCoset (w 0) (j • e)).indicator 1) fun i => L.f (w i.succ)
  let sc : Fin (r + 1) → ℂ := Fin.cons sq fun i => s (w i.succ)
  have hCO : ∀ i, CO (L.UF (w i)) := by
    refine Fin.cases ?_ fun i => ?_
    · rw [L.at_q.2.2.2]; exact (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test F n (w 0)).1
    · have h := L.lev _ (hS ▸ hmemS i)
      exact (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test F n (w i.succ)).2.1 _ h.2.2.1 h.2.2.2
  have hfin := UpperTheory.finiteDimensional_eigenspace_inf_fixed_compactOpen F n hn μ ν V a x (r + 1) w hV hx.ne' hw (fun i => L.UF (w i)) hCO
  have hf := hfac (fun i => L.UF (w i)) (fun i => m (w i)) φc Tc sc hCO (fun i => hmH _)
    (by
      refine Fin.cases ?_ fun i => ?_
      · exact (hiw _).1
      · exact htest i.succ)
    (by
      refine Fin.cases ?_ fun i => ?_
      · intro u hu g
        rw [L.at_q.2.2.2] at hu
        exact (hiw _).2 u hu g
      · exact (L.inv _ (hS ▸ hmemS i)).2)
    (by
      refine Fin.cases ?_ fun i => ?_
      · exact hT₀
      · exact hT i.succ)
    (by
      refine Fin.cases ?_ fun i => ?_
      · exact hsq
      · exact hs _ (hmemS i))
  have hstep : (Uiw μ (w 0) e ^ j) ∘L T 0 = T₀ :=
    UpperTheory.Uiw_pow_comp_eq_of_antitone F n μ (w 0) (m (w 0)) e j (T 0) T₀ he (L.at_q.2.1 ▸ hT 0) hT₀
  have hB : ∀ v ∈ Z ⊓ ⨅ i, fixL μ (w i) (L.UF (w i)),
      ((𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∘L (Twist.id μ).U) v = ((κ : ℂ) * (x : ℂ)) • (List.ofFn Tc).prod v := by
    intro v hv
    have hv1 : v ∈ Z := hv.1
    have hTp : (List.ofFn T).prod v ∈ Z := by
      refine list_prod_stable Z _ (fun T' hT' u hu => ?_) v hv1
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hT'
      exact UpperTheory.localHeckeOperator_mem_of_closed_invariant F n μ (w i) (m (w i)) (L.f (w i)) (T i) Z hZc (fun g u hu => hZs (w i) (hmemP i) g u hu)
        (hT i) u hu
    have hO : Oinf μ ν a ((List.ofFn T).prod v) = (x : ℂ) • (List.ofFn T).prod v :=
      Module.End.mem_eigenspace_iff.1 hTp.1.2
    have hsph : v ∈ sphOff μ (Finset.univ.image w) := hv1.2
    have hRg : Rop μ 𝔣.g v = (κ : ℂ) • ((x : ℂ) • (List.ofFn T).prod v) := by
      have h1 : Rop μ 𝔣.g = RR μ 𝔣.g := rfl
      rw [h1, hRR]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, prj_self _ hsph, hO]
    have hc : (List.ofFn Tc).prod = T₀ * (List.ofFn fun i : Fin r => T i.succ).prod := by
      rw [List.ofFn_succ, List.prod_cons]
      rfl
    have hd : (List.ofFn T).prod = T 0 * (List.ofFn fun i : Fin r => T i.succ).prod := by
      rw [List.ofFn_succ, List.prod_cons]
    have hid : (Twist.id μ).U v = v := rfl
    have hstep' : ∀ y, (𝔣.Uq 0 ^ j) (T 0 y) = T₀ y := fun y => by
      rw [hUq, ← hstep]
      rfl
    simp only [ContinuousLinearMap.comp_apply, hid, hRg, map_smul, hc, hd, ContinuousLinearMap.mul_apply, hstep',
      smul_smul]
  rw [hW, UpperTheory.trOn_eq_mul_of_eq_smul_on_subspace _ _ _ _ _ hfin hB, hf, Fin.prod_univ_succ]
  have h1 : ∏ i : Fin r, sc i.succ = ∏ v ∈ S, s v := hprod s
  have h2 : sc 0 = sq := rfl
  rw [h1, h2]
  ring
