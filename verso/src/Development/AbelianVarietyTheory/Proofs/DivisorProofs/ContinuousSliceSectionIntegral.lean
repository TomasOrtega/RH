import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

/- English proof (translation)
Introduce `k _ _ _ _ a d Φ hΦ s hs hsl huniq`. Take `⟨⟨hlc, hcpt⟩, hrk⟩` from `hΦ`. Establish `hcl : IsClosed (Function.support Φ)`. Establish `: Function.support Φ = (Φ ⁻¹' {0})ᶜ` using `by ext; simp`. Rewrite using `[this, isClosed_compl_iff]`.

Conclude with `hlc.isOpen_fiber 0`. Establish `hS : tsupport Φ ⊆ {Y | Y.rank = a}`. Introduce `Y hY`. Rewrite `hY` using `[tsupport, hcl.closure_eq]`. Assume the negation of the conclusion as `h`.

Conclude with `hY (hrk Y h)`. Use `set f : Matrix (Fin a) (Fin d) k → GL (Fin a) k × Matrix (Fin a) (Fin d) k := fun Y => (s Y, ((s Y)⁻¹).val * Y) with hf`. Establish `hfc : ContinuousOn f (tsupport Φ)`. Establish `hs'` using `hs.mono hS`. Use `ContinuousOn.prodMk hs' ?_` and prove the remaining obligations.

Conclude with `(Continuous.matrix_mul continuous_fst continuous_snd).comp_continuousOn ((Units.continuous_val.comp_continuousOn hs'.inv).prodMk continuousOn_id)`. Establish `hA : IsCompact (f '' tsupport Φ)` using `hcpt.image_of_continuousOn hfc`. Use `set n : Set ((GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k) := {p | Φ (p.1.1.val * p.2.val * p.1.2) = Φ (p.1.1.val * p.1.2)} with hn`. Establish `hno : IsOpen n`. Establish `h1 : IsLocallyConstant (fun p : (GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k => Φ (p.1.1.val * p.2.val * p.1.2))` using `hlc.comp_continuous (by fun_prop)`.

Establish `h2 : IsLocallyConstant (fun p : (GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k => Φ (p.1.1.val * p.1.2))` using `hlc.comp_continuous (by fun_prop)`. Conclude with `(h1.prodMk h2) {q | q.1 = q.2}`. Establish `hsub : (f '' tsupport Φ) ×ˢ ({1} : Set (GL (Fin a) k)) ⊆ n`. Introduce and unpack `⟨⟨g, Z⟩, x⟩ ⟨_, hx⟩`. Simplify using `only [Set.mem_singleton_iff] at hx`.

Substitute `hx` using the available equality. Simplify using `[hn]`. Take `⟨u, v, -, hv, hAu, h1v, huv⟩` from `generalized_tube_lemma hA isCompact_singleton hno hsub`. Establish `key : ∀ (h : GL (Fin a) k) (Z : Matrix (Fin a) (Fin d) k), Z ∈ slice k a d → Φ (h.val * Z) ≠ 0 → (h, Z) ∈ f '' tsupport Φ`. Introduce `h Z hZ hne`.

Establish `hY : h.val * Z ∈ tsupport Φ` using `subset_tsupport _ hne`. Establish `hr` using `hS hY`. Establish `e : (s (h.val * Z))⁻¹ * h = 1`. Apply `huniq Z _ hZ` to reduce the goal to its premises. Use `hsl _ hr` as an intermediate fact.

Simplify `this` using `[Units.val_mul, Matrix.mul_assoc]`. Establish `e' : s (h.val * Z) = h`. Use `congrArg (fun t => s (h.val * Z) * t) e` as an intermediate fact. Simplify `this.symm` using `[mul_assoc]`. Use `⟨h.val * Z, hY, ?_⟩` and prove the remaining obligations.

Simplify using `only [hf, e', Prod.mk.injEq, true_and]`. Rewrite using `[← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]`. Use `⟨v ∩ v⁻¹, Filter.inter_mem (hv.mem_nhds (h1v rfl)) ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hv.inv).mem_nhds (by simpa using h1v rfl)`. Introduce and unpack `x ⟨hxv, hxv'⟩ g Z hZ`.

Distinguish the cases in `h0 : Φ (g.val * Z) ≠ 0`. Conclude with `huv (Set.mk_mem_prod (hAu (key g Z hZ h0)) hxv)`. Distinguish the cases in `h0' : Φ (g.val * x.val * Z) ≠ 0`. Establish `hm : (g * x, Z) ∈ f '' tsupport Φ` using `key (g * x) Z hZ (by simpa [Units.val_mul] using h0')`. Use `huv (Set.mk_mem_prod (hAu hm) (show x⁻¹ ∈ v from hxv'))` as an intermediate fact.

Simplify using `only [hn, Set.mem_setOf_eq] at this`. Rewrite `this` using `[Units.val_mul, Matrix.mul_assoc g.val x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]`. Rewrite using `[this]`. Use `push_neg at h0 h0'`. Rewrite using `[h0, h0']`.
-/
theorem nhds_one_slice_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ fullRankSB k a d →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice k a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice k a d → g.val * Z ∈ slice k a d → g = 1) →
    ∃ U ∈ nhds (1 : GL (Fin a) k), ∀ x ∈ U, ∀ (g : GL (Fin a) k), ∀ Z ∈ slice k a d,
      Φ (g.val * x.val * Z) = Φ (g.val * Z) := by
  intro k _ _ _ _ a d Φ hΦ s hs hsl huniq
  obtain ⟨⟨hlc, hcpt⟩, hrk⟩ := hΦ

  have hcl : IsClosed (Function.support Φ) := by
    have : Function.support Φ = (Φ ⁻¹' {0})ᶜ := by ext; simp
    rw [this, isClosed_compl_iff]; exact hlc.isOpen_fiber 0
  have hS : tsupport Φ ⊆ {Y | Y.rank = a} := by
    intro Y hY
    rw [tsupport, hcl.closure_eq] at hY
    by_contra h; exact hY (hrk Y h)
  set f : Matrix (Fin a) (Fin d) k → GL (Fin a) k × Matrix (Fin a) (Fin d) k :=
    fun Y => (s Y, ((s Y)⁻¹).val * Y) with hf
  have hfc : ContinuousOn f (tsupport Φ) := by
    have hs' := hs.mono hS
    refine ContinuousOn.prodMk hs' ?_
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_continuousOn
      ((Units.continuous_val.comp_continuousOn hs'.inv).prodMk continuousOn_id)
  have hA : IsCompact (f '' tsupport Φ) := hcpt.image_of_continuousOn hfc
  set n : Set ((GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k) :=
    {p | Φ (p.1.1.val * p.2.val * p.1.2) = Φ (p.1.1.val * p.1.2)} with hn
  have hno : IsOpen n := by
    have h1 : IsLocallyConstant (fun p : (GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k =>
        Φ (p.1.1.val * p.2.val * p.1.2)) :=
      hlc.comp_continuous (by fun_prop)
    have h2 : IsLocallyConstant (fun p : (GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k =>
        Φ (p.1.1.val * p.1.2)) :=
      hlc.comp_continuous (by fun_prop)
    exact (h1.prodMk h2) {q | q.1 = q.2}
  have hsub : (f '' tsupport Φ) ×ˢ ({1} : Set (GL (Fin a) k)) ⊆ n := by
    rintro ⟨⟨g, Z⟩, x⟩ ⟨_, hx⟩
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp [hn]
  obtain ⟨u, v, -, hv, hAu, h1v, huv⟩ := generalized_tube_lemma hA isCompact_singleton hno hsub

  have key : ∀ (h : GL (Fin a) k) (Z : Matrix (Fin a) (Fin d) k), Z ∈ slice k a d → Φ (h.val * Z) ≠ 0 →
      (h, Z) ∈ f '' tsupport Φ := by
    intro h Z hZ hne
    have hY : h.val * Z ∈ tsupport Φ := subset_tsupport _ hne
    have hr := hS hY
    have e : (s (h.val * Z))⁻¹ * h = 1 := by
      apply huniq Z _ hZ
      have := hsl _ hr
      simpa [Units.val_mul, Matrix.mul_assoc] using this
    have e' : s (h.val * Z) = h := by
      have := congrArg (fun t => s (h.val * Z) * t) e
      simpa [mul_assoc] using this.symm
    refine ⟨h.val * Z, hY, ?_⟩
    simp only [hf, e', Prod.mk.injEq, true_and]
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  refine ⟨v ∩ v⁻¹, Filter.inter_mem (hv.mem_nhds (h1v rfl)) ?_, ?_⟩
  · exact (hv.inv).mem_nhds (by simpa using h1v rfl)
  rintro x ⟨hxv, hxv'⟩ g Z hZ
  by_cases h0 : Φ (g.val * Z) ≠ 0
  · exact huv (Set.mk_mem_prod (hAu (key g Z hZ h0)) hxv)
  by_cases h0' : Φ (g.val * x.val * Z) ≠ 0
  · have hm : (g * x, Z) ∈ f '' tsupport Φ := key (g * x) Z hZ (by simpa [Units.val_mul] using h0')
    have := huv (Set.mk_mem_prod (hAu hm) (show x⁻¹ ∈ v from hxv'))
    simp only [hn, Set.mem_setOf_eq] at this
    rw [Units.val_mul, Matrix.mul_assoc g.val x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one] at this
    rw [this]
  push_neg at h0 h0'
  rw [h0, h0']

end GlobalTheory.RankFibreKer
