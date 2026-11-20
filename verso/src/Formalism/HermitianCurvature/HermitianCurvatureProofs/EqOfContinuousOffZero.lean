import Formalism.HermitianCurvature.CompositeFormulaLevelZero

open MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

/- English proof (translation)
Establish `h : {z : ℂ | 0 ≤ z} = {z : ℂ | 0 ≤ z.re} ∩ {z : ℂ | z.im = 0}`. Use extensionality with `z`. Simplify using `only [Set.mem_setOf_eq, Set.mem_inter_iff, Complex.le_def, Complex.zero_re, Complex.zero_im]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨h1, h2.symm⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, h2.symm⟩`. Rewrite using `[h]`. Conclude with `(isClosed_le continuous_const Complex.continuous_re).inter (isClosed_eq Complex.continuous_im continuous_const)`.
-/
theorem isClosed_nonneg_complex : IsClosed {z : ℂ | 0 ≤ z} := by
  have h : {z : ℂ | 0 ≤ z} = {z : ℂ | 0 ≤ z.re} ∩ {z : ℂ | z.im = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Complex.le_def, Complex.zero_re, Complex.zero_im]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
  rw [h]
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_eq Complex.continuous_im continuous_const)

/- English proof (translation)
Establish `hre : ∀ a, f a = ((f a).re : ℂ)` using `fun a => by`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Simplify using `only [Complex.ofReal_im]`. Conclude with `((Complex.le_def.mp (h a)).2).symm`.

Establish `hf : (fun a => f a) = fun a => ((f a).re : ℂ)` using `funext hre`. Rewrite using `[hf]`. Use `first`. Consider the case `rw [integral_complex_ofReal]`. Consider the case `rw [integral_ofReal]`.

Consider the case `rw [← RCLike.ofReal_eq_complex_ofReal, integral_ofReal]`. Conclude with `Complex.zero_le_real.mpr (integral_nonneg fun a => (Complex.le_def.mp (h a)).1)`.
-/
theorem integral_nonneg_complex {α : Type*} [MeasurableSpace α] (ν : Measure α) (f : α → ℂ)
    (h : ∀ a, 0 ≤ f a) : 0 ≤ ∫ a, f a ∂ν := by
  have hre : ∀ a, f a = ((f a).re : ℂ) := fun a => by
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]
      exact ((Complex.le_def.mp (h a)).2).symm
  have hf : (fun a => f a) = fun a => ((f a).re : ℂ) := funext hre
  rw [hf]
  first
  | rw [integral_complex_ofReal]
  | rw [integral_ofReal]
  | rw [← RCLike.ofReal_eq_complex_ofReal, integral_ofReal]
  exact Complex.zero_le_real.mpr (integral_nonneg fun a => (Complex.le_def.mp (h a)).1)

/- English proof (translation)
Unfold `fsv`. Conclude with `((continuous_const.mul continuous_id).sub (continuous_const.mul Complex.continuous_conj)).cexp`.
-/
theorem continuous_fsv (s : ℂ) : Continuous (fsv s) := by
  unfold fsv
  exact ((continuous_const.mul continuous_id).sub
    (continuous_const.mul Complex.continuous_conj)).cexp

/- English proof (translation)
Establish `hcl : IsClosed {t | 0 ≤ φ t}` using `isClosed_nonneg_complex.preimage hc`. Establish `hsub : ({(0 : ℂ)}ᶜ : Set ℂ) ⊆ {t | 0 ≤ φ t}` using `fun t ht => h t ht`. Establish `hcl2` using `hcl.closure_subset_iff.mpr hsub`. Rewrite `hcl2` using `[(dense_compl_singleton (0 : ℂ)).closure_eq]`. Introduce `t`.

Conclude with `hcl2 (Set.mem_univ t)`.
-/
theorem nonneg_of_continuous {φ : ℂ → ℂ} (hc : Continuous φ) (h : ∀ t, t ≠ 0 → 0 ≤ φ t) :
    ∀ t, 0 ≤ φ t := by
  have hcl : IsClosed {t | 0 ≤ φ t} := isClosed_nonneg_complex.preimage hc
  have hsub : ({(0 : ℂ)}ᶜ : Set ℂ) ⊆ {t | 0 ≤ φ t} := fun t ht => h t ht
  have hcl2 := hcl.closure_subset_iff.mpr hsub
  rw [(dense_compl_singleton (0 : ℂ)).closure_eq] at hcl2
  intro t
  exact hcl2 (Set.mem_univ t)

/- English proof (translation)
The claim follows from `hf.ext_on (dense_compl_singleton (0 : ℂ)) hg (fun t ht => h t ht)`.
-/
theorem eq_of_continuous_off_zero {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ t, t ≠ 0 → f t = g t) : f = g := hf.ext_on (dense_compl_singleton (0 : ℂ)) hg (fun t ht => h t ht)

/- English proof (translation)
Introduce `j`. Break down `eq_or_ne j l with rfl | hj` into its components or cases. Simplify using `using ht`. Rewrite using `[Function.update_of_ne hj]`. Conclude with `hc j`.
-/
theorem update_mem_OmX {m : ℕ} {c : Fin m → ℂ} (hc : c ∈ OmX m) (l : Fin m) {t : ℂ} (ht : t ≠ 0) :
    Function.update c l t ∈ OmX m := by
  intro j
  rcases eq_or_ne j l with rfl | hj
  · simpa using ht
  · rw [Function.update_of_ne hj]
    exact hc j

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `i hi c hc x hx`. Establish `hi' : i = Fin.last P.r` using `Fin.ext (by simpa using hi)`.

Substitute `hi'` using the available equality. Rewrite using `[(hTI w hw x x hx hx c hc).2]`. Conclude with `integral_nonneg_complex μ _ (fun g => hTN w hw x hx c hc (Matrix.of g))`. Consider the case `succ n ih`. Introduce `i hi c hc x hx`.

Establish `hlt : i.val < P.r` using `by omega`. Take `⟨l, rfl⟩ : ∃ l : Fin P.r, l.castSucc = i` from `⟨⟨i.val, hlt⟩, Fin.ext rfl⟩`. Take `⟨φ, hφc, hφ, -, hint⟩` from `hSD w hw l x x hx hx c hc`. Rewrite using `[← hint]`. Apply `integral_nonneg_complex` to reduce the goal to its premises.

Apply `nonneg_of_continuous hφc` to reduce the goal to its premises. Introduce `t ht`. Rewrite using `[hφ t ht]`. Unfold `ph`. Apply `mul_nonneg` to reduce the goal to its premises.

Conclude with `Complex.zero_le_real.mpr (by positivity)`. Establish `hn : (l.succ).val + n = P.r`. Simplify using `only [Fin.coe_castSucc] at hi`. Simplify using `only [Fin.val_succ]`. Use linear arithmetic over natural numbers and integers.

Conclude with `ih l.succ hn _ (update_mem_OmX hc l ht) _ (hSI w hw l x hx)`.
-/
theorem nonneg_all_levels {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S]
    [DecidableEq S] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (hTI : TopIdent (S := S) P z z' π π' μ L st K l0) (hTN : TopDensNonneg (S := S) P z z' π π' L st K l0)
    (hSI : SliceIn (S := S) P z z' π π' L st K l0) (hSD : StepDens (S := S) P z z' π π' μ L st K l0)
    (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w) :
    ∀ (n : ℕ) (i : Fin (P.r + 1)), i.val + n = P.r → ∀ c ∈ OmX P.r,
      ∀ x : Ix S → RadSp P.k P.r z z' π π', InK (K i) x → 0 ≤ RRform L st μ i w x x c := by
  intro n
  induction n with
  | zero =>
    intro i hi c hc x hx
    have hi' : i = Fin.last P.r := Fin.ext (by simpa using hi)
    subst hi'
    rw [(hTI w hw x x hx hx c hc).2]
    exact integral_nonneg_complex μ _ (fun g => hTN w hw x hx c hc (Matrix.of g))
  | succ n ih =>
    intro i hi c hc x hx
    have hlt : i.val < P.r := by omega
    obtain ⟨l, rfl⟩ : ∃ l : Fin P.r, l.castSucc = i := ⟨⟨i.val, hlt⟩, Fin.ext rfl⟩
    obtain ⟨φ, hφc, hφ, -, hint⟩ := hSD w hw l x x hx hx c hc
    rw [← hint]
    apply integral_nonneg_complex
    apply nonneg_of_continuous hφc
    intro t ht
    rw [hφ t ht]
    unfold ph
    apply mul_nonneg
    · exact Complex.zero_le_real.mpr (by positivity)
    · have hn : (l.succ).val + n = P.r := by
        simp only [Fin.coe_castSucc] at hi
        simp only [Fin.val_succ]
        omega
      exact ih l.succ hn _ (update_mem_OmX hc l ht) _ (hSI w hw l x hx)

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' μ L st K l0`. Introduce `hTI hTN hTT hSI hSD hST hFS w hw`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y hx hy c hc`. Use `⟨(hTI w hw x y hx hy c hc).1, ?_, ?_⟩` and prove the remaining obligations.

Introduce `s Wv Wv' h1 h2`. Take `⟨hK, hD⟩` from `hTT w hw s Wv Wv' h1 h2 x y hx hy c hc`. Rewrite using `[(hTI w hw _ y hK hy c hc).2]`. Use `congr 1`. Use function extensionality and compare the values at `g`.

Rewrite using `[hD]`. Conclude with `nonneg_all_levels (S := S) P z z' π π' μ L st K l0 hTI hTN hSI hSD w hw 0 (Fin.last P.r) (by simp) c hc x hx`. Introduce `l x y hx hy c hc`. Take `⟨φ, hφc, hφ, hC, -⟩` from `hSD w hw l x y hx hy c hc`. Use `⟨φ, hφc, hφ, hC, ?_⟩` and prove the remaining obligations.

Introduce `s Wv Wv' h1 h2`. Take `⟨hK, hT⟩` from `hST w hw l s Wv Wv' h1 h2 x y hx hy c hc`. Take `⟨ψ, hψc, hψ, -, hψint⟩` from `hSD w hw l _ y hK hy c hc`. Rewrite using `[← hψint]`. Use `congr 1`.

Apply `eq_of_continuous_off_zero ((continuous_fsv s).mul hφc) hψc` to reduce the goal to its premises. Introduce `t ht`. Use `show fsv s t * φ t = ψ t`. Rewrite using `[hψ t ht, hT t ht, hφ t ht]`. Introduce `i c hc`.

Use `⟨hFS w hw i c hc, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Establish `hxK : InK (K i) x` using `fun a => (Submodule.mem_pi.mp hx) a (Set.mem_univ a)`. Conclude with `nonneg_all_levels (S := S) P z z' π π' μ L st K l0 hTI hTN hSI hSD w hw (P.r - i.val) i (by omega) c hc x hxK`.
-/
theorem thmPFromStepsAll : ThmPFromStepsAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' μ L st K l0
  intro hTI hTN hTT hSI hSD hST hFS w hw
  refine ⟨?_, ?_, ?_⟩
  · intro x y hx hy c hc
    refine ⟨(hTI w hw x y hx hy c hc).1, ?_, ?_⟩
    · intro s Wv Wv' h1 h2
      obtain ⟨hK, hD⟩ := hTT w hw s Wv Wv' h1 h2 x y hx hy c hc
      rw [(hTI w hw _ y hK hy c hc).2]
      congr 1
      funext g
      rw [hD]
    · exact nonneg_all_levels (S := S) P z z' π π' μ L st K l0 hTI hTN hSI hSD w hw 0
        (Fin.last P.r) (by simp) c hc x hx
  · intro l x y hx hy c hc
    obtain ⟨φ, hφc, hφ, hC, -⟩ := hSD w hw l x y hx hy c hc
    refine ⟨φ, hφc, hφ, hC, ?_⟩
    intro s Wv Wv' h1 h2
    obtain ⟨hK, hT⟩ := hST w hw l s Wv Wv' h1 h2 x y hx hy c hc
    obtain ⟨ψ, hψc, hψ, -, hψint⟩ := hSD w hw l _ y hK hy c hc
    rw [← hψint]
    congr 1
    apply eq_of_continuous_off_zero ((continuous_fsv s).mul hφc) hψc
    intro t ht
    show fsv s t * φ t = ψ t
    rw [hψ t ht, hT t ht, hφ t ht]
  · intro i c hc
    refine ⟨hFS w hw i c hc, ?_⟩
    intro x hx
    have hxK : InK (K i) x := fun a => (Submodule.mem_pi.mp hx) a (Set.mem_univ a)
    exact nonneg_all_levels (S := S) P z z' π π' μ L st K l0 hTI hTN hSI hSD w hw (P.r - i.val) i
      (by omega) c hc x hxK

end Formalism.FourierDecayAlt.P5
