import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupStructuresPermConjInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceTransposePow

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.DSId.PermK

open GlobalTheory.Dec.FormF

variable {n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules.
-/
lemma comp_symm {α : Type} (f : Fin n → α) (s : Equiv.Perm (Fin n)) : (f ∘ s) ∘ s.symm = f := by
  funext x
  simp

/- English proof (translation)
Establish `h'` using `GlobalTheory.Dec.FormF.K_perm s.symm h`. Rewrite `h'` using `[PermK.comp_symm]`. Then use the resulting hypothesis.
-/
lemma K_back {ε : Fin n → Bool} (s : Equiv.Perm (Fin n)) {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ Kset (ε ∘ s)) :
    g.submatrix s.symm s.symm ∈ Kset ε := by
  have h' := GlobalTheory.Dec.FormF.K_perm s.symm h
  rwa [PermK.comp_symm] at h'

/- English proof (translation)
Establish `h'` using `GlobalTheory.Dec.FormF.UJ_perm s.symm h`. Rewrite `h'` using `[PermK.comp_symm]`. Then use the resulting hypothesis.
-/
lemma UJ_back {ε : Fin n → Bool} (s : Equiv.Perm (Fin n)) {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ UJset (ε ∘ s)) :
    g.submatrix s.symm s.symm ∈ UJset ε := by
  have h' := GlobalTheory.Dec.FormF.UJ_perm s.symm h
  rwa [PermK.comp_symm] at h'

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hlt`. Break down `lt_trichotomy a b with hab | rfl | hab` into its components or cases. Conclude with `hab`. Conclude with `absurd hlt (lt_irrefl _)`.

Conclude with `absurd (hs b a hab h.symm) (not_lt.mpr hlt.le)`. Introduce `hab`. Conclude with `hs a b hab h`.
-/
lemma lt_iff {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)} (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b)
    {a b : Fin n} (h : ε (s a) = ε (s b)) : s a < s b ↔ a < b := by
  constructor
  · intro hlt
    rcases lt_trichotomy a b with hab | rfl | hab
    · exact hab
    · exact absurd hlt (lt_irrefl _)
    · exact absurd (hs b a hab h.symm) (not_lt.mpr hlt.le)
  · intro hab
    exact hs a b hab h

/- English proof (translation)
Introduce `a b hab he`. Establish `he' : ε (s (s.symm a)) = ε (s (s.symm b))` using `he`. Conclude with `(PermK.lt_iff hs he').1 (by simpa using hab)`.
-/
lemma mono_symm {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)} (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) :
    ∀ a b, a < b → (ε ∘ s) (s.symm a) = (ε ∘ s) (s.symm b) → s.symm a < s.symm b := by
  intro a b hab he
  have he' : ε (s (s.symm a)) = ε (s (s.symm b)) := he
  exact (PermK.lt_iff hs he').1 (by simpa using hab)

/- English proof (translation)
Use `Finset.card_equiv s (fun b => ?_)` and prove the remaining obligations. Simplify using `only [mem_filter, mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨(PermK.lt_iff hs h2.symm).2 h1, h2⟩`.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨(PermK.lt_iff hs h2.symm).1 h1, h2⟩`.
-/
private lemma card_infinitePlace_eq_f {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) (a : Fin n) :
    (univ.filter fun b => a < b ∧ ε (s b) = ε (s a)).card =
      (univ.filter fun c => s a < c ∧ ε c = ε (s a)).card := by
  refine Finset.card_equiv s (fun b => ?_)
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(PermK.lt_iff hs h2.symm).2 h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(PermK.lt_iff hs h2.symm).1 h1, h2⟩

/- English proof (translation)
Use `Finset.card_equiv s (fun b => ?_)` and prove the remaining obligations. Simplify using `only [mem_filter, mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨(PermK.lt_iff hs h2).2 h1, h2⟩`.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨(PermK.lt_iff hs h2).1 h1, h2⟩`.
-/
private lemma card_quotient_comap_sq_eq_card_quotient_of_involution {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) (a : Fin n) :
    (univ.filter fun b => b < a ∧ ε (s b) = ε (s a)).card =
      (univ.filter fun c => c < s a ∧ ε c = ε (s a)).card := by
  refine Finset.card_equiv s (fun b => ?_)
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(PermK.lt_iff hs h2).2 h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(PermK.lt_iff hs h2).1 h1, h2⟩

/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `only [Formalism.REAL.rhoC, Function.comp_apply]`. Rewrite using `[card_infinitePlace_eq_f hs a, card_quotient_comap_sq_eq_card_quotient_of_involution hs a]`.
-/
lemma rhoC_perm {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)} (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) :
    rhoC (ε ∘ s) = rhoC ε ∘ s := by
  funext a
  simp only [Formalism.REAL.rhoC, Function.comp_apply]
  rw [card_infinitePlace_eq_f hs a, card_quotient_comap_sq_eq_card_quotient_of_involution hs a]

/- English proof (translation)
Unfold `vNormSq`. Rewrite using `[PermK.rhoC_perm hs]`. Establish `e : μ ∘ s + (2 : ℝ) • (Formalism.REAL.rhoC ε ∘ s) = (μ + (2 : ℝ) • Formalism.REAL.rhoC ε) ∘ s`. Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Simplify using `only [Formalism.REAL.nsq, Formalism.REAL.dot, Function.comp_apply]`. Conclude with `Equiv.sum_comp s (fun a => (μ + (2 : ℝ) • Formalism.REAL.rhoC ε) a * (μ + (2 : ℝ) • Formalism.REAL.rhoC ε) a)`.
-/
lemma vNormSq_perm {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)} (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b)
    (μ : Fin n → ℝ) : vNormSq (ε ∘ s) (μ ∘ s) = vNormSq ε μ := by
  unfold vNormSq
  rw [PermK.rhoC_perm hs]
  have e : μ ∘ s + (2 : ℝ) • (Formalism.REAL.rhoC ε ∘ s) = (μ + (2 : ℝ) • Formalism.REAL.rhoC ε) ∘ s := by
    funext a
    simp
  rw [e]
  simp only [Formalism.REAL.nsq, Formalism.REAL.dot, Function.comp_apply]
  exact Equiv.sum_comp s (fun a => (μ + (2 : ℝ) • Formalism.REAL.rhoC ε) a * (μ + (2 : ℝ) • Formalism.REAL.rhoC ε) a)

/- English proof (translation)
Unfold `CDom at h ⊢`. Take `⟨c, hc, hsum⟩` from `h`. Use `⟨fun a b => c (s a) (s b), fun a b hab => ?_, ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hc _ _ hab`. Conclude with `⟨(PermK.lt_iff hs h2).1 h1, h2⟩`.

Use function extensionality and compare the values at `x`. Establish `hx` using `congrFun hsum (s x)`. Simplify using `only [Pi.sub_apply, Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx ⊢`. Rewrite using `[hx]`. Use `symm`.

Use `Fintype.sum_equiv s _ _ (fun a => ?_)` and prove the remaining obligations. Use `Fintype.sum_equiv s _ _ (fun b => ?_)` and prove the remaining obligations. Simplify using `[Formalism.REAL.root, Pi.single_apply]`.
-/
lemma cdom_perm {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)} (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b)
    {μ Λ : Fin n → ℝ} (h : CDom ε μ Λ) : CDom (ε ∘ s) (μ ∘ s) (Λ ∘ s) := by
  unfold CDom at h ⊢
  obtain ⟨c, hc, hsum⟩ := h
  refine ⟨fun a b => c (s a) (s b), fun a b hab => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hc _ _ hab
    exact ⟨(PermK.lt_iff hs h2).1 h1, h2⟩
  · funext x
    have hx := congrFun hsum (s x)
    simp only [Pi.sub_apply, Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx ⊢
    rw [hx]
    symm
    refine Fintype.sum_equiv s _ _ (fun a => ?_)
    refine Fintype.sum_equiv s _ _ (fun b => ?_)
    simp [Formalism.REAL.root, Pi.single_apply]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Introduce `θ hθ`. Establish `hmem` using `PermK.K_back s hθ`. Use `beta_reduce`. Rewrite `hmem`, the goal using `[Matrix.submatrix_diagonal_equiv]`. Establish `key` using `h (θ ∘ s.symm) hmem`.

Establish `hsum : (∑ a, μ a * (θ ∘ s.symm) a) = ∑ a, (μ ∘ s) a * θ a` using `Fintype.sum_equiv s.symm _ _ (fun a => by simp)`. Rewrite using `[← hsum]`. Conclude with `key`.
-/
lemma wt_perm {ε : Fin n → Bool} (s : Equiv.Perm (Fin n)) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {μ : Fin n → ℝ} {v : H} (h : IsWtOn (Kset ε) σ μ v) :
    IsWtOn (Kset (ε ∘ s)) (fun g => σ (g.submatrix s.symm s.symm)) (μ ∘ s) v := by
  intro θ hθ
  have hmem := PermK.K_back s hθ
  beta_reduce
  rw [Matrix.submatrix_diagonal_equiv] at hmem ⊢
  have key := h (θ ∘ s.symm) hmem
  have hsum : (∑ a, μ a * (θ ∘ s.symm) a) = ∑ a, (μ ∘ s) a * θ a :=
    Fintype.sum_equiv s.symm _ _ (fun a => by simp)
  rw [← hsum]
  exact key

/- English proof (translation)
Unfold `IsKStableOn`. Prove the components needed by the constructor for the conclusion. Introduce `H' g hg v hv`. Use `H' (g.submatrix s s) (GlobalTheory.Dec.FormF.K_perm s hg) v hv` as an intermediate fact. Simplify `this` using `[Matrix.submatrix_submatrix]`.

Introduce `H' g hg v hv`. Conclude with `H' _ (PermK.K_back s hg) v hv`.
-/
lemma stable_perm {ε : Fin n → Bool} (s : Equiv.Perm (Fin n)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (S : Submodule ℂ H) :
    IsKStableOn (ε ∘ s) (fun g => σ (g.submatrix s.symm s.symm)) S ↔ IsKStableOn ε σ S := by
  unfold IsKStableOn
  constructor
  · intro H' g hg v hv
    have := H' (g.submatrix s s) (GlobalTheory.Dec.FormF.K_perm s hg) v hv
    simpa [Matrix.submatrix_submatrix] using this
  · intro H' g hg v hv
    exact H' _ (PermK.K_back s hg) v hv

/- English proof (translation)
Unfold `IsKTypeOf at h ⊢`. Take `⟨hfd, hst, hirr, ⟨v, hvS, hv0, hwt⟩, hdom⟩` from `h`. Use `⟨hfd, (PermK.stable_perm s σ S).2 hst, fun S' hle hS' => hirr S' hle ((PermK.stable_perm s σ S').1 hS'), ⟨v, hvS, hv0, PermK.wt_perm s hwt⟩, ?_⟩` and prove the remaining obligations. Introduce `μ' w hwS hw0 hw`. Establish `hw'` using `PermK.wt_perm s.symm hw`.

Rewrite `hw'` using `[PermK.comp_symm]`. Simplify using `only [Equiv.symm_symm, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id] at hw'`. Establish `hc` using `PermK.cdom_perm hs (hdom (μ' ∘ s.symm) w hwS hw0 hw')`. Establish `e : (μ' ∘ s.symm) ∘ s = μ'`. Use function extensionality and compare the values at `a`.

Simplify using the standard rewrite rules. Rewrite `hc` using `[e]`. Then use the resulting hypothesis.
-/
lemma ktype_perm {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)} (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b)
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {μ : Fin n → ℝ} {S : Submodule ℂ H} (h : IsKTypeOf ε σ μ S) :
    IsKTypeOf (ε ∘ s) (fun g => σ (g.submatrix s.symm s.symm)) (μ ∘ s) S := by
  unfold IsKTypeOf at h ⊢
  obtain ⟨hfd, hst, hirr, ⟨v, hvS, hv0, hwt⟩, hdom⟩ := h
  refine ⟨hfd, (PermK.stable_perm s σ S).2 hst,
    fun S' hle hS' => hirr S' hle ((PermK.stable_perm s σ S').1 hS'), ⟨v, hvS, hv0, PermK.wt_perm s hwt⟩, ?_⟩
  intro μ' w hwS hw0 hw
  have hw' := PermK.wt_perm s.symm hw
  rw [PermK.comp_symm] at hw'
  simp only [Equiv.symm_symm, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id] at hw'
  have hc := PermK.cdom_perm hs (hdom (μ' ∘ s.symm) w hwS hw0 hw')
  have e : (μ' ∘ s.symm) ∘ s = μ' := by
    funext a
    simp
  rwa [e] at hc

/- English proof (translation)
Unfold `IsSqIntIrr IsURepOn Formalism.QuantumDeterminants.IsCRepOn IsIrredOn IsSqIntOn at h ⊢`. Take `⟨hc, hn, ⟨⟨h1, hmul⟩, hiso, hcont⟩, hirr, hsq⟩` from `h`. Use `⟨hc, hn, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Simplify `h1` using `[Matrix.submatrix_one_equiv]`. Introduce `a ha b hb beta_reduce`.

Rewrite using `[← Matrix.submatrix_mul_equiv _ _ _ s.symm _]`. Conclude with `hmul _ (PermK.UJ_back s ha) _ (PermK.UJ_back s hb)`. Introduce `g hg w`. Conclude with `hiso _ (PermK.UJ_back s hg) w`. Introduce `w`.

Conclude with `(hcont w).comp (continuous_id.matrix_submatrix _ _).continuousOn (fun g hg => PermK.UJ_back s hg)`. Introduce `S hS hst`. Apply `hirr S hS` to reduce the goal to its premises. Introduce `g hg w hw`. Use `hst (g.submatrix s s) (GlobalTheory.Dec.FormF.UJ_perm s hg) w hw` as an intermediate fact.

Simplify `this` using `[Matrix.submatrix_submatrix]`. Introduce `v w`. Conclude with `((GlobalTheory.T.unitaryGroup_structures_perm_conj_invariant _ ε s).2 (fun x => ⟪w, σ x v⟫_ℂ) 2).1.mp (hsq v w)`.
-/
lemma sqIntIrr_perm {ε : Fin n → Bool} (s : Equiv.Perm (Fin n))
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : IsSqIntIrr ε σ) :
    IsSqIntIrr (ε ∘ s) (fun g => σ (g.submatrix s.symm s.symm)) := by
  unfold IsSqIntIrr IsURepOn Formalism.QuantumDeterminants.IsCRepOn IsIrredOn IsSqIntOn at h ⊢
  obtain ⟨hc, hn, ⟨⟨h1, hmul⟩, hiso, hcont⟩, hirr, hsq⟩ := h
  refine ⟨hc, hn, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · simpa [Matrix.submatrix_one_equiv] using h1
  · intro a ha b hb
    beta_reduce
    rw [← Matrix.submatrix_mul_equiv _ _ _ s.symm _]
    exact hmul _ (PermK.UJ_back s ha) _ (PermK.UJ_back s hb)
  · intro g hg w
    exact hiso _ (PermK.UJ_back s hg) w
  · intro w
    exact (hcont w).comp (continuous_id.matrix_submatrix _ _).continuousOn (fun g hg => PermK.UJ_back s hg)
  · intro S hS hst
    apply hirr S hS
    intro g hg w hw
    have := hst (g.submatrix s s) (GlobalTheory.Dec.FormF.UJ_perm s hg) w hw
    simpa [Matrix.submatrix_submatrix] using this
  · intro v w
    exact ((GlobalTheory.T.unitaryGroup_structures_perm_conj_invariant _ ε s).2 (fun x => ⟪w, σ x v⟫_ℂ) 2).1.mp (hsq v w)

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons p w ih`. Use function extensionality and compare the values at `g`. Simplify using `only [Formalism.REAL.Eword, List.map_cons]`.

Rewrite using `[ih]`. Establish `h` using `GlobalTheory.Dec.FormF.Eab_perm (ε ∘ s) s.symm (s p.1) (s p.2) (Formalism.REAL.Eword ε (w.map fun p => (s p.1, s p.2)) f) g`. Rewrite `h` using `[PermK.comp_symm, Equiv.symm_apply_apply, Equiv.symm_apply_apply]`. Conclude with `h`.
-/
private lemma eword_comp_perm_submatrix (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (f : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (w : List (Fin n × Fin n)) :
    Formalism.REAL.Eword (ε ∘ s) w (fun x => f (x.submatrix s.symm s.symm)) =
      fun g => Formalism.REAL.Eword ε (w.map fun p => (s p.1, s p.2)) f (g.submatrix s.symm s.symm) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    funext g
    simp only [Formalism.REAL.Eword, List.map_cons]
    rw [ih]
    have h := GlobalTheory.Dec.FormF.Eab_perm (ε ∘ s) s.symm (s p.1) (s p.2)
      (Formalism.REAL.Eword ε (w.map fun p => (s p.1, s p.2)) f) g
    rw [PermK.comp_symm, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h
    exact h

/- English proof (translation)
Unfold `gelf`. Simplify using `only [eword_comp_perm_submatrix ε s f]`. Use `Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl _) s) _ _ (fun a => ?_)` and prove the remaining obligations. Establish `hw : (cycWord a).map (fun p => (s p.1, s p.2)) = cycWord (Equiv.arrowCongr (Equiv.refl _) s a)`. Simplify using `[cycWord, List.map_ofFn, Function.comp_def, Equiv.arrowCongr_apply]`.

Rewrite using `[hw]`.
-/
private lemma gelf_comp_perm_submatrix (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (m : ℕ)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    gelf (ε ∘ s) m (fun x => f (x.submatrix s.symm s.symm)) g = gelf ε m f (g.submatrix s.symm s.symm) := by
  unfold gelf
  simp only [eword_comp_perm_submatrix ε s f]
  refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl _) s) _ _ (fun a => ?_)
  have hw : (cycWord a).map (fun p => (s p.1, s p.2)) = cycWord (Equiv.arrowCongr (Equiv.refl _) s a) := by
    simp [cycWord, List.map_ofFn, Function.comp_def, Equiv.arrowCongr_apply]
  rw [hw]

/- English proof (translation)
Set `_ : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ)` to `Matrix.normedAddCommGroup`. Set `_ : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ)` to `Matrix.normedSpace`. Unfold `Formalism.REAL.SmoothOnG at h ⊢`. Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, hfF⟩` from `h _ (PermK.UJ_back s hg₀)`.

Set `L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ` to `LinearMap.toContinuousLinearMap (Matrix.reindexLinearEquiv ℝ ℂ s s).toLinearMap`. Establish `hL : ∀ x, L x = x.submatrix s.symm s.symm` using `fun x => rfl`. Use `⟨L ⁻¹' U, fun x => F (L x), hU.preimage L.continuous, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show L g₀ ∈ U`. Rewrite using `[hL]`.

Conclude with `hgU`. Conclude with `hF.comp_continuousLinearMap L`. Introduce `x hx hxJ`. Establish `hx' : x.submatrix s.symm s.symm ∈ U`. Rewrite using `[← hL]`.

Conclude with `hx`. Use `beta_reduce`. Rewrite using `[hL]`. Conclude with `hfF _ hx' (PermK.UJ_back s hxJ)`.
-/
private lemma smoothOnG_comp_perm_submatrix {ε : Fin n → Bool} (s : Equiv.Perm (Fin n)) {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : Formalism.REAL.SmoothOnG ε f) : Formalism.REAL.SmoothOnG (ε ∘ s) (fun x => f (x.submatrix s.symm s.symm)) := by
  let _ : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
  let _ : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
  unfold Formalism.REAL.SmoothOnG at h ⊢
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := h _ (PermK.UJ_back s hg₀)
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.reindexLinearEquiv ℝ ℂ s s).toLinearMap
  have hL : ∀ x, L x = x.submatrix s.symm s.symm := fun x => rfl
  refine ⟨L ⁻¹' U, fun x => F (L x), hU.preimage L.continuous, ?_, ?_, ?_⟩
  · show L g₀ ∈ U
    rw [hL]
    exact hgU
  · exact hF.comp_continuousLinearMap L
  · intro x hx hxJ
    have hx' : x.submatrix s.symm s.symm ∈ U := by
      rw [← hL]
      exact hx
    beta_reduce
    rw [hL]
    exact hfF _ hx' (PermK.UJ_back s hxJ)

/- English proof (translation)
Unfold `IsZEigen at h ⊢`. Use `⟨smoothOnG_comp_perm_submatrix s h.1, fun m g hg => ?_⟩` and prove the remaining obligations. Rewrite using `[gelf_comp_perm_submatrix ε s f m g]`. Conclude with `h.2 m _ (PermK.UJ_back s hg)`.
-/
private lemma isZEigen_comp_perm_submatrix {ε : Fin n → Bool} (s : Equiv.Perm (Fin n)) {χ : Fin n → ℂ}
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : IsZEigen ε χ f) :
    IsZEigen (ε ∘ s) χ (fun x => f (x.submatrix s.symm s.symm)) := by
  unfold IsZEigen at h ⊢
  refine ⟨smoothOnG_comp_perm_submatrix s h.1, fun m g hg => ?_⟩
  rw [gelf_comp_perm_submatrix ε s f m g]
  exact h.2 m _ (PermK.UJ_back s hg)

/- English proof (translation)
Unfold `IsKFin`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨S, h1, h2, h3⟩`. Conclude with `⟨S, h1, h2, (PermK.stable_perm s σ S).1 h3⟩`. Introduce and unpack `⟨S, h1, h2, h3⟩`.

Conclude with `⟨S, h1, h2, (PermK.stable_perm s σ S).2 h3⟩`.
-/
private lemma isKFin_comp_perm_submatrix_iff {ε : Fin n → Bool} (s : Equiv.Perm (Fin n)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (v : H) : IsKFin (ε ∘ s) (fun g => σ (g.submatrix s.symm s.symm)) v ↔ IsKFin ε σ v := by
  unfold IsKFin
  constructor
  · rintro ⟨S, h1, h2, h3⟩
    exact ⟨S, h1, h2, (PermK.stable_perm s σ S).1 h3⟩
  · rintro ⟨S, h1, h2, h3⟩
    exact ⟨S, h1, h2, (PermK.stable_perm s σ S).2 h3⟩

/- English proof (translation)
Unfold `HasInfChar at h ⊢`. Introduce `v w hv hw`. Conclude with `isZEigen_comp_perm_submatrix s (h v w ((isKFin_comp_perm_submatrix_iff s σ v).1 hv) ((isKFin_comp_perm_submatrix_iff s σ w).1 hw))`.
-/
private lemma hasInfChar_comp_perm {ε : Fin n → Bool} (s : Equiv.Perm (Fin n)) {χ : Fin n → ℂ}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : HasInfChar ε χ σ) :
    HasInfChar (ε ∘ s) χ (fun g => σ (g.submatrix s.symm s.symm)) := by
  unfold HasInfChar at h ⊢
  intro v w hv hw
  exact isZEigen_comp_perm_submatrix s (h v w ((isKFin_comp_perm_submatrix_iff s σ v).1 hv) ((isKFin_comp_perm_submatrix_iff s σ w).1 hw))

/- English proof (translation)
Introduce `n ε s H _ _ σ hs`. Establish `hs'` using `PermK.mono_symm hs`. Use `⟨fun μ S => ⟨PermK.ktype_perm hs, fun h => ?_⟩, fun μ => PermK.vNormSq_perm hs μ, PermK.rhoC_perm hs, ⟨PermK.sqIntIrr_perm s, fun h => ?_⟩, fun χ => ⟨fun h => ?_, hasInfChar_comp_perm s⟩⟩` and prove the remaining obligations. Establish `h2` using `PermK.ktype_perm hs' h`. Rewrite `h2` using `[PermK.comp_symm, PermK.comp_symm]`.

Simplify `h2` using `only [Equiv.symm_symm, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]`. Establish `h2` using `PermK.sqIntIrr_perm s.symm h`. Rewrite `h2` using `[PermK.comp_symm]`. Simplify `h2` using `only [Equiv.symm_symm, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]`. Establish `h2` using `hasInfChar_comp_perm s.symm h`.

Rewrite `h2` using `[PermK.comp_symm]`. Simplify `h2` using `only [Equiv.symm_symm, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]`.
-/
theorem permKType : ∀ (n : ℕ) (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), (∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) → (∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S ↔ IsKTypeOf (ε ∘ s) (fun g => σ (g.submatrix s.symm s.symm)) (μ ∘ s) S) ∧ (∀ μ : Fin n → ℝ, vNormSq (ε ∘ s) (μ ∘ s) = vNormSq ε μ) ∧ rhoC (ε ∘ s) = rhoC ε ∘ s ∧ (IsSqIntIrr ε σ ↔ IsSqIntIrr (ε ∘ s) (fun g => σ (g.submatrix s.symm s.symm))) ∧ ∀ χ : Fin n → ℂ, (HasInfChar (ε ∘ s) χ (fun g => σ (g.submatrix s.symm s.symm)) ↔ HasInfChar ε χ σ) := by
  intro n ε s H _ _ σ hs
  have hs' := PermK.mono_symm hs
  refine ⟨fun μ S => ⟨PermK.ktype_perm hs, fun h => ?_⟩, fun μ => PermK.vNormSq_perm hs μ, PermK.rhoC_perm hs,
    ⟨PermK.sqIntIrr_perm s, fun h => ?_⟩, fun χ => ⟨fun h => ?_, hasInfChar_comp_perm s⟩⟩
  · have h2 := PermK.ktype_perm hs' h
    rw [PermK.comp_symm, PermK.comp_symm] at h2
    simpa only [Equiv.symm_symm, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id] using h2
  · have h2 := PermK.sqIntIrr_perm s.symm h
    rw [PermK.comp_symm] at h2
    simpa only [Equiv.symm_symm, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id] using h2
  · have h2 := hasInfChar_comp_perm s.symm h
    rw [PermK.comp_symm] at h2
    simpa only [Equiv.symm_symm, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id] using h2

end GlobalTheory.DSId.PermK
