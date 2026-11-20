import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensEProd
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.FixLev
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.L1
open scoped ComplexConjugate Classical InnerProductSpace

section Abs

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

/- English proof (translation)
Take `⟨-, -, -, -, -, hmul, hone, -⟩` from `UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥`. Establish `heig : ∀ w, ∀ x ∈ J w, rhoF μ (AdelicGLn.localEmbedding w x) f = χ w x • f` using `fun w x hx => by`. Use `hf w` as an intermediate fact. Simplify using `only [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus] at this`. Simplify `this x hx` using `[rhoL]`.

Proceed by induction on `R using Finset.induction_on with`. Consider the case `empty`. Introduce `g _ h1 h2`. Establish `hfix : f ∈ fixF μ (levOn P fun _ => ⊥)`. Rewrite using `[UpperTheory.ConvolutionTheory.C.fixLev K n μ P]`.

Use `Submodule.mem_inf.2 ⟨?_, ?_⟩` and prove the remaining obligations. Use `Submodule.mem_iInf _ |>.2 fun v => Submodule.mem_iInf _ |>.2 fun hv => ?_` and prove the remaining obligations. Use `((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 f).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨e1, e2⟩` from `hP v hv`.

Use `heig v x (by rw [e1]; exact hx)` as an intermediate fact. Rewrite using `[this, e2]`. Simplify using the standard rewrite rules. Use `Submodule.mem_iInf _ |>.2 fun v => Submodule.mem_iInf _ |>.2 fun hv => ?_` and prove the remaining obligations. Use `((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 f).2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[Subgroup.mem_bot.1 hx, map_one, hone]`. Both sides reduce to the same expression. Establish `hg : g ∈ levOn P (fun _ => ⊥)`. Introduce `v`.

Distinguish the cases in `hv : v ∈ P`. Simplify using `only [hv, if_true]`. Conclude with `Subgroup.mem_bot.2 (h1 v hv (Finset.notMem_empty v))`. Simplify using `only [hv, if_false]`. Conclude with `h2 v hv`.

Simplify using `using ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 f).1 hfix g hg`. Consider the case `insert a R ha ih`. Introduce `g h0 h1 h2`. Take `⟨-, e1, e2, -, -⟩` from `UpperTheory.ConvolutionTheory.Tf.locEmb K n a`. Use `set x := finAt a (finEmb K n g) with hx`.

Use `set g' := (AdelicGLn.localEmbedding a x)⁻¹ * g with hg'`. Establish `hc : ∀ w, w ≠ a → finAt w (finEmb K n g') = finAt w (finEmb K n g)` using `fun w hw => by`. Rewrite using `[hg', map_mul, finAt_mul, map_inv, finAt_inv, e2 w hw]`. Simplify using the standard rewrite rules. Establish `hca : finAt a (finEmb K n g') = 1`.

Rewrite using `[hg', map_mul, finAt_mul, map_inv, finAt_inv, e1]`. Simplify using `[hx]`. Establish `key` using `ih g' (fun w hw => by`. Establish `hwa : w ≠ a` using `fun h => ha (h ▸ hw)`. Rewrite using `[hc w hwa]`.

Conclude with `h0 w (Finset.mem_insert_of_mem hw))`. Use the proof step `(fun w hw hwR => by`. Distinguish the cases in `hwa : w = a`. Substitute `hwa` using the available equality. Conclude with `hca`.

Rewrite using `[hc w hwa]`. Conclude with `h1 w hw (by simp [hwa, hwR]))`. Use the proof step `(fun w hw => by`. Distinguish the cases in `hwa : w = a`. Substitute `hwa` using the available equality.

Rewrite using `[hca]`. Conclude with `one_mem _`. Rewrite using `[hc w hwa]`. Conclude with `h2 w hw)`. Establish `hgg : g = AdelicGLn.localEmbedding a x * g'` using `by simp [hg']`.

Establish `hprod : ∏ w ∈ R, χ w (finAt w (finEmb K n g')) = ∏ w ∈ R, χ w (finAt w (finEmb K n g))` using `Finset.prod_congr rfl fun w hw => by`. Rewrite using `[hc w fun h => ha (h ▸ hw)]`. Establish `hstep : rhoF μ g f = rhoF μ (AdelicGLn.localEmbedding a x) (rhoF μ g' f)` using `by conv_lhs => rw [hgg, hmul]`. Both sides reduce to the same expression. Rewrite using `[hstep, key, hprod, map_smul, heig a x (h0 a (Finset.mem_insert_self a R)), smul_smul, Finset.prod_insert ha, mul_comm]`.
-/
private theorem rho_typed (J : ∀ w : Pl K, Subgroup (Gw n w)) (χ : ∀ w : Pl K, Gw n w → ℂ) (f : LL μ)
    (hf : ∀ w, f ∈ eigL μ w (J w) (χ w)) (P : Finset (Pl K))
    (hP : ∀ w ∉ P, J w = GLnLocal.integralGL (w.adicCompletion K) n ∧ χ w = 1) (R : Finset (Pl K)) :
    ∀ g : AdelicGLn.FiniteAdelicGL K n, (∀ w ∈ R, finAt w (finEmb K n g) ∈ J w) →
      (∀ w ∈ P, w ∉ R → finAt w (finEmb K n g) = 1) →
      (∀ w ∉ P, finAt w (finEmb K n g) ∈ GLnLocal.integralGL (w.adicCompletion K) n) →
      rhoF μ g f = (∏ w ∈ R, χ w (finAt w (finEmb K n g))) • f := by
  obtain ⟨-, -, -, -, -, hmul, hone, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥
  have heig : ∀ w, ∀ x ∈ J w, rhoF μ (AdelicGLn.localEmbedding w x) f = χ w x • f := fun w x hx => by
    have := hf w
    simp only [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus] at this
    simpa [rhoL] using this x hx
  induction R using Finset.induction_on with
  | empty =>
    intro g _ h1 h2
    have hfix : f ∈ fixF μ (levOn P fun _ => ⊥) := by
      rw [UpperTheory.ConvolutionTheory.C.fixLev K n μ P]
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · refine Submodule.mem_iInf _ |>.2 fun v => Submodule.mem_iInf _ |>.2 fun hv => ?_
        refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 f).2 ?_
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨e1, e2⟩ := hP v hv
        have := heig v x (by rw [e1]; exact hx)
        rw [this, e2]
        simp
      · refine Submodule.mem_iInf _ |>.2 fun v => Submodule.mem_iInf _ |>.2 fun hv => ?_
        refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 f).2 ?_
        rintro _ ⟨x, hx, rfl⟩
        rw [Subgroup.mem_bot.1 hx, map_one, hone]
        rfl
    have hg : g ∈ levOn P (fun _ => ⊥) := by
      intro v
      by_cases hv : v ∈ P
      · simp only [hv, if_true]
        exact Subgroup.mem_bot.2 (h1 v hv (Finset.notMem_empty v))
      · simp only [hv, if_false]
        exact h2 v hv
    simpa using ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 f).1 hfix g hg
  | insert a R ha ih =>
    intro g h0 h1 h2
    obtain ⟨-, e1, e2, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K n a
    set x := finAt a (finEmb K n g) with hx
    set g' := (AdelicGLn.localEmbedding a x)⁻¹ * g with hg'
    have hc : ∀ w, w ≠ a → finAt w (finEmb K n g') = finAt w (finEmb K n g) := fun w hw => by
      rw [hg', map_mul, finAt_mul, map_inv, finAt_inv, e2 w hw]
      simp
    have hca : finAt a (finEmb K n g') = 1 := by
      rw [hg', map_mul, finAt_mul, map_inv, finAt_inv, e1]
      simp [hx]
    have key := ih g' (fun w hw => by
        have hwa : w ≠ a := fun h => ha (h ▸ hw)
        rw [hc w hwa]
        exact h0 w (Finset.mem_insert_of_mem hw))
      (fun w hw hwR => by
        by_cases hwa : w = a
        · subst hwa; exact hca
        · rw [hc w hwa]
          exact h1 w hw (by simp [hwa, hwR]))
      (fun w hw => by
        by_cases hwa : w = a
        · subst hwa; rw [hca]; exact one_mem _
        · rw [hc w hwa]; exact h2 w hw)
    have hgg : g = AdelicGLn.localEmbedding a x * g' := by simp [hg']
    have hprod : ∏ w ∈ R, χ w (finAt w (finEmb K n g')) = ∏ w ∈ R, χ w (finAt w (finEmb K n g)) :=
      Finset.prod_congr rfl fun w hw => by
        rw [hc w fun h => ha (h ▸ hw)]
    have hstep : rhoF μ g f = rhoF μ (AdelicGLn.localEmbedding a x) (rhoF μ g' f) := by
      conv_lhs => rw [hgg, hmul]
      rfl
    rw [hstep, key, hprod, map_smul, heig a x (h0 a (Finset.mem_insert_self a R)), smul_smul,
      Finset.prod_insert ha, mul_comm]

end Abs

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
The claim follows from `HeightOneSpectrum.ext w.2.over.symm`.
-/
private theorem under_over' {v : Pl F} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

/- English proof (translation)
Use extensionality with `i j`. Both sides reduce to the same expression.
-/
private theorem cmp_atFin' {v : Pl F} (w : PlacesOver E v) (g : AdelicGLn.AdelicGL E n) :
    GM.cmp w (mapGL n (atFin v) g) = finAt w.1 g := by
  ext i j
  rfl

/- English proof (translation)
Use `(Set.finite_range (Subtype.val : PlacesOver E v → Pl E)).subset ?_` and prove the remaining obligations. Introduce and unpack `w rfl`. Conclude with `⟨⟨w, ⟨rfl⟩⟩, rfl⟩`.
-/
private theorem fin_above' (v : Pl F) : {w : Pl E | w.under (𝓞 F) = v}.Finite := by
  refine (Set.finite_range (Subtype.val : PlacesOver E v → Pl E)).subset ?_
  rintro w rfl
  exact ⟨⟨w, ⟨rfl⟩⟩, rfl⟩

/- English proof (translation)
Establish `h1` using `h.2.2 1 J.one_mem 1 J.one_mem`. Establish `h2 : χ 1 ≠ 0` using `fun h0 => by`. Use `h.2.1 1 J.one_mem` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify using `at this`.

Rewrite `h1` using `[mul_one]`. Conclude with `(mul_eq_left₀ h2).1 h1.symm`.
-/
private theorem chr_one {G : Type} [Group G] [TopologicalSpace G] {J : Subgroup G} {χ : G → ℂ} (h : IsChr J χ) : χ 1 = 1 := by
  have h1 := h.2.2 1 J.one_mem 1 J.one_mem
  have h2 : χ 1 ≠ 0 := fun h0 => by
    have := h.2.1 1 J.one_mem
    rw [h0] at this
    simp at this
  rw [mul_one] at h1
  exact (mul_eq_left₀ h2).1 h1.symm

/- English proof (translation)
Establish `easy : (∀ u : PlacesOver E v, GM.cmp u x ∈ T.J u.1) → (∀ u : PlacesOver E v, T.χ u.1 = 1) → (∀ u : PlacesOver E v, GM.cmp u x ∈ T.J u.1) ∧ ∏ᶠ u : PlacesOver E v, (T.J u.1 : Set (Gw n u.1)).indicator (T.χ u.1) (GM.cmp u x) = 1` using `fun h1 h2 => by`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Rewrite using `[finprod_eq_prod_of_fintype]`. Use `Finset.prod_eq_one fun u _ => ?_` and prove the remaining obligations. Rewrite using `[Set.indicator_of_mem (by exact h1 u), h2 u]`.

Both sides reduce to the same expression. Distinguish the cases in `hvq : v = q`. Substitute `hvq` using the available equality. Use `easy (fun u => ?_) (T.triv v hq)` and prove the remaining obligations. Rewrite using `[T.at_q u]`.

Conclude with `(L.at_q.2.2.1 x).1 hx u`. Distinguish the cases in `hvS : v ∈ T.S`. Distinguish the cases in `hs : GM.Split E v`. Establish `hsp : v ∈ T.sp` using `Finset.mem_filter.2 ⟨hvS, hs⟩`. Conclude with `easy (((hF.split v hsp).2 x).1 hx) (T.triv v hs)`.

Establish `hvL : v ∈ L.S` using `hF.S_eq ▸ hvS`. Establish `hinv` using `(L.inv v hvL).1 x hx 1`. Rewrite `hinv` using `[mul_one, hF.nonsplit v hvS hs]`. Unfold `GM.prodFn at hinv`. Rewrite `hinv` using `[finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype]`.

Establish `h1 : ∏ u : PlacesOver E v, (T.J u.1 : Set (Gw n u.1)).indicator (fun y => conj (T.χ u.1 y)) (GM.cmp u 1) = 1`. Use `Finset.prod_eq_one fun u _ => ?_` and prove the remaining obligations. Rewrite using `[map_one, Set.indicator_of_mem (by exact one_mem _), chr_one (T.chr u.1)]`. Simplify using the standard rewrite rules. Rewrite `hinv` using `[h1]`.

Establish `hm : ∀ u : PlacesOver E v, GM.cmp u x ∈ T.J u.1` using `fun u => by`. Assume the negation of the conclusion as `hc`. Establish `: ∏ u : PlacesOver E v, (T.J u.1 : Set (Gw n u.1)).indicator (fun y => conj (T.χ u.1 y)) (GM.cmp u x) = 0` using `Finset.prod_eq_zero (Finset.mem_univ u) (Set.indicator_of_notMem (by exact hc) _)`. Rewrite `hinv` using `[this]`. Conclude with `zero_ne_one hinv`.

Use `⟨hm, ?_⟩` and prove the remaining obligations. Rewrite using `[finprod_eq_prod_of_fintype]`. Establish `h2 : conj (∏ u : PlacesOver E v, (T.J u.1 : Set (Gw n u.1)).indicator (T.χ u.1) (GM.cmp u x)) = 1`. Rewrite using `[map_prod, ← hinv]`. Use `Finset.prod_congr rfl fun u _ => ?_` and prove the remaining obligations.

Rewrite using `[Set.indicator_of_mem (by exact hm u)]`. Conclude with `(Set.indicator_of_mem (s := (T.J u.1 : Set (Gw n u.1))) (hm u) fun y => conj (T.χ u.1 y)).symm`. Establish `h3` using `congrArg (starRingEnd ℂ) h2`. Simplify using `using h3`. Establish `hvL : v ∉ L.S` using `fun h => hvS (hF.S_eq ▸ h)`.

Establish `hu : x ∈ unitSet E n v`. Rewrite using `[← (L.off v hvL hvq).2.2.1]`. Conclude with `hx`. Establish `hoff : ∀ u : PlacesOver E v, T.J u.1 = GLnLocal.integralGL (u.1.adicCompletion E) n ∧ T.χ u.1 = 1` using `fun u => T.off u.1 (by rwa [under_over']) (by rwa [under_over'])`. Use `easy (fun u => ?_) fun u => (hoff u).2` and prove the remaining obligations.

Rewrite using `[(hoff u).1]`. Conclude with `hu u`.
-/
private theorem at_place {σ : E ≃ₐ[F] E} {q : Pl F} {w₀ : PlacesOver E q} (hq : GM.Split E q)
    (T : Ty σ n q w₀) (L : GM.Loc σ n q w₀) {ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ} (hF : T.Fits L ψ) (v : Pl F)
    (x : GL (Fin n) (CompletionsOver E v)) (hx : x ∈ L.UE v) :
    (∀ u : PlacesOver E v, GM.cmp u x ∈ T.J u.1) ∧
      ∏ᶠ u : PlacesOver E v, (T.J u.1 : Set (Gw n u.1)).indicator (T.χ u.1) (GM.cmp u x) = 1 := by
  have easy : (∀ u : PlacesOver E v, GM.cmp u x ∈ T.J u.1) → (∀ u : PlacesOver E v, T.χ u.1 = 1) →
      (∀ u : PlacesOver E v, GM.cmp u x ∈ T.J u.1) ∧
      ∏ᶠ u : PlacesOver E v, (T.J u.1 : Set (Gw n u.1)).indicator (T.χ u.1) (GM.cmp u x) = 1 := fun h1 h2 => by
    refine ⟨h1, ?_⟩
    rw [finprod_eq_prod_of_fintype]
    refine Finset.prod_eq_one fun u _ => ?_
    rw [Set.indicator_of_mem (by exact h1 u), h2 u]
    rfl
  by_cases hvq : v = q
  · subst hvq
    refine easy (fun u => ?_) (T.triv v hq)
    rw [T.at_q u]
    exact (L.at_q.2.2.1 x).1 hx u
  by_cases hvS : v ∈ T.S
  · by_cases hs : GM.Split E v
    · have hsp : v ∈ T.sp := Finset.mem_filter.2 ⟨hvS, hs⟩
      exact easy (((hF.split v hsp).2 x).1 hx) (T.triv v hs)
    · have hvL : v ∈ L.S := hF.S_eq ▸ hvS
      have hinv := (L.inv v hvL).1 x hx 1
      rw [mul_one, hF.nonsplit v hvS hs] at hinv
      unfold GM.prodFn at hinv
      rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype] at hinv
      have h1 : ∏ u : PlacesOver E v, (T.J u.1 : Set (Gw n u.1)).indicator (fun y => conj (T.χ u.1 y)) (GM.cmp u 1) = 1 := by
        refine Finset.prod_eq_one fun u _ => ?_
        rw [map_one, Set.indicator_of_mem (by exact one_mem _), chr_one (T.chr u.1)]
        simp
      rw [h1] at hinv
      have hm : ∀ u : PlacesOver E v, GM.cmp u x ∈ T.J u.1 := fun u => by
        by_contra hc
        have : ∏ u : PlacesOver E v, (T.J u.1 : Set (Gw n u.1)).indicator (fun y => conj (T.χ u.1 y)) (GM.cmp u x) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ u) (Set.indicator_of_notMem (by exact hc) _)
        rw [this] at hinv
        exact zero_ne_one hinv
      refine ⟨hm, ?_⟩
      rw [finprod_eq_prod_of_fintype]
      have h2 : conj (∏ u : PlacesOver E v, (T.J u.1 : Set (Gw n u.1)).indicator (T.χ u.1) (GM.cmp u x)) = 1 := by
        rw [map_prod, ← hinv]
        refine Finset.prod_congr rfl fun u _ => ?_
        rw [Set.indicator_of_mem (by exact hm u)]
        exact (Set.indicator_of_mem (s := (T.J u.1 : Set (Gw n u.1))) (hm u) fun y => conj (T.χ u.1 y)).symm
      have h3 := congrArg (starRingEnd ℂ) h2
      simpa using h3
  · have hvL : v ∉ L.S := fun h => hvS (hF.S_eq ▸ h)
    have hu : x ∈ unitSet E n v := by
      rw [← (L.off v hvL hvq).2.2.1]
      exact hx
    have hoff : ∀ u : PlacesOver E v, T.J u.1 = GLnLocal.integralGL (u.1.adicCompletion E) n ∧ T.χ u.1 = 1 := fun u =>
      T.off u.1 (by rwa [under_over']) (by rwa [under_over'])
    refine easy (fun u => ?_) fun u => (hoff u).2
    rw [(hoff u).1]
    exact hu u

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n q w₀ hq μ _ T L ψ hF f hf`. Establish `hfw : ∀ w, f ∈ eigL μ w (T.J w) (T.χ w)` using `(Submodule.mem_iInf _).1 hf`. Use `((UpperTheory.ConvolutionTheory.Tf.commPrj E n μ _).2.1 f).2 fun g hg => ?_` and prove the remaining obligations. Establish `hX : ∀ v : Pl F, mapGL n (atFin v) (finEmb E n g) ∈ L.UE v` using `fun v => Subgroup.mem_iInf.1 hg v`. Establish `hloc` using `fun v : Pl F => at_place hq T L hF v _ (hX v)`.

Establish `hJ : ∀ w : Pl E, finAt w (finEmb E n g) ∈ T.J w` using `fun w => by`. Use `(hloc (w.under (𝓞 F))).1 ⟨w, ⟨rfl⟩⟩` as an intermediate fact. Rewrite `this` using `[cmp_atFin']`. Then use the resulting hypothesis. Establish `hfin : {w : Pl E | w.under (𝓞 F) ∈ insert q T.S}.Finite`. Use `((insert q T.S).finite_toSet.biUnion fun v _ => fin_above' (E := E) v).subset ?_` and prove the remaining obligations.

Introduce `w hw`. Conclude with `Set.mem_biUnion (x := w.under (𝓞 F)) hw rfl`. Use `set P : Finset (Pl E) := hfin.toFinset with hPdef`. Establish `hP : ∀ w ∉ P, T.J w = GLnLocal.integralGL (w.adicCompletion E) n ∧ T.χ w = 1` using `fun w hw => by`. Establish `: w.under (𝓞 F) ∉ insert q T.S` using `fun h => hw (hfin.mem_toFinset.2 h)`.

Rewrite `this` using `[Finset.mem_insert, not_or]`. Conclude with `T.off w this.2 this.1`. Establish `hr` using `rho_typed μ T.J T.χ f hfw P hP P g (fun w _ => hJ w) (fun w h1 h2 => absurd h1 h2) (fun w hw => by rw [← (hP w hw).1]; exact hJ w)`. Establish `hone : ∏ w ∈ P, T.χ w (finAt w (finEmb E n g)) = 1`. Establish `ht` using `UpperTheory.ConvolutionTheory.Tf.tensEProd F E n (fun w => (T.J w : Set (Gw n w)).indicator (T.χ w)) (by`.

Use `Filter.eventually_cofinite.2 (hfin.subset fun w hw => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Apply `hw` to reduce the goal to its premises. Establish `hwP : w ∉ P` using `fun h => hc (hfin.mem_toFinset.1 h)`. Take `⟨e1, e2⟩` from `hP w hwP`.

Simplify using `only [e1, e2]) (finEmb E n g)`. Establish `hl : ∀ v : Pl F, GM.prodFn (v` using `v) (fun w => (T.J w.1 : Set (Gw n w.1)).indicator (T.χ w.1)) (mapGL n (atFin v) (finEmb E n g)) = 1 := fun v => (hloc v).2`. Simplify using `only [hl, finprod_one] at ht`. Rewrite `ht` using `[finprod_eq_prod_of_mulSupport_subset (s := P)]`. Rewrite using `[ht]`.

Conclude with `Finset.prod_congr rfl fun w _ => (Set.indicator_of_mem (by exact hJ w) _).symm`. Introduce `w hw`. Assume the negation of the conclusion as `hc`. Apply `hw` to reduce the goal to its premises. Take `⟨e1, e2⟩` from `hP w (by simpa using hc)`.

Simplify using `only [Set.indicator_of_mem (show finAt w (finEmb E n g) ∈ (T.J w : Set (Gw n w)) from hJ w), e2]`. Both sides reduce to the same expression. Rewrite using `[hr, hone, one_smul]`.
-/
theorem UpperTheory.typed_vectors_le_fixed_of_fits_level :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ)
        (q : Pl F) (w₀ : PlacesOver E q), GM.Split E q → ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
        (T : Ty σ n q w₀) (L : GM.Loc σ n q w₀) (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ), T.Fits L ψ →
        T.typed μ ≤ fixF μ (GM.levE L.UE) := by
  intro F E _ _ _ _ _ σ n q w₀ hq μ _ T L ψ hF f hf
  have hfw : ∀ w, f ∈ eigL μ w (T.J w) (T.χ w) := (Submodule.mem_iInf _).1 hf
  refine ((UpperTheory.ConvolutionTheory.Tf.commPrj E n μ _).2.1 f).2 fun g hg => ?_
  have hX : ∀ v : Pl F, mapGL n (atFin v) (finEmb E n g) ∈ L.UE v := fun v => Subgroup.mem_iInf.1 hg v
  have hloc := fun v : Pl F => at_place hq T L hF v _ (hX v)
  have hJ : ∀ w : Pl E, finAt w (finEmb E n g) ∈ T.J w := fun w => by
    have := (hloc (w.under (𝓞 F))).1 ⟨w, ⟨rfl⟩⟩
    rwa [cmp_atFin'] at this
  have hfin : {w : Pl E | w.under (𝓞 F) ∈ insert q T.S}.Finite := by
    refine ((insert q T.S).finite_toSet.biUnion fun v _ => fin_above' (E := E) v).subset ?_
    intro w hw
    exact Set.mem_biUnion (x := w.under (𝓞 F)) hw rfl
  set P : Finset (Pl E) := hfin.toFinset with hPdef
  have hP : ∀ w ∉ P, T.J w = GLnLocal.integralGL (w.adicCompletion E) n ∧ T.χ w = 1 := fun w hw => by
    have : w.under (𝓞 F) ∉ insert q T.S := fun h => hw (hfin.mem_toFinset.2 h)
    rw [Finset.mem_insert, not_or] at this
    exact T.off w this.2 this.1
  have hr := rho_typed μ T.J T.χ f hfw P hP P g (fun w _ => hJ w) (fun w h1 h2 => absurd h1 h2)
    (fun w hw => by rw [← (hP w hw).1]; exact hJ w)
  have hone : ∏ w ∈ P, T.χ w (finAt w (finEmb E n g)) = 1 := by
    have ht := UpperTheory.ConvolutionTheory.Tf.tensEProd F E n (fun w => (T.J w : Set (Gw n w)).indicator (T.χ w))
      (by
        refine Filter.eventually_cofinite.2 (hfin.subset fun w hw => ?_)
        by_contra hc
        apply hw
        have hwP : w ∉ P := fun h => hc (hfin.mem_toFinset.1 h)
        obtain ⟨e1, e2⟩ := hP w hwP
        simp only [e1, e2]) (finEmb E n g)
    have hl : ∀ v : Pl F, GM.prodFn (v := v) (fun w => (T.J w.1 : Set (Gw n w.1)).indicator (T.χ w.1))
        (mapGL n (atFin v) (finEmb E n g)) = 1 := fun v => (hloc v).2
    simp only [hl, finprod_one] at ht
    rw [finprod_eq_prod_of_mulSupport_subset (s := P)] at ht
    · rw [ht]
      exact Finset.prod_congr rfl fun w _ => (Set.indicator_of_mem (by exact hJ w) _).symm
    · intro w hw
      by_contra hc
      apply hw
      obtain ⟨e1, e2⟩ := hP w (by simpa using hc)
      simp only [Set.indicator_of_mem (show finAt w (finEmb E n g) ∈ (T.J w : Set (Gw n w)) from hJ w), e2]
      rfl
  rw [hr, hone, one_smul]
