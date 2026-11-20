import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PNoLogSt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PSliceUA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.ExpChar
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSlice
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUniqueness

open LieSumUnipotentSlice PositivityTheory.Rg.Rs.SliceClasses in

/- English proof (translation)
Introduce `E _ _ _ r s hr hs U hU hFG hSI hReg φ hφU c hc`. Establish `hD` using `dict_holds`. Establish `hFin` using `finTr_holds`. Take `⟨F₀, hCT, F, hFspan, hFne, hFeig⟩` from `hc`. Establish `hAφ` using `hU.2 φ hφU`.

Take `⟨κ, -, rfl⟩` from `((hD E (r + s)).2.2.2 φ hAφ r hr (by omega)).2 F₀ hCT`. Take `⟨cs, hcs⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.1 hFspan`. Take `⟨b, hb⟩ : ∃ b : ℝ → ℂ, b = fun t => cs t * κ` from `⟨_, rfl⟩`. Establish `hFval : ∀ g, F g = ∑ t ∈ cs.support, b t * An.ctn r φ.1 (aT E (r + s) r t * g)`. Introduce `g`.

Rewrite using `[← hcs, Finsupp.sum, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, hb, mul_assoc]`. Take `⟨S, hSU, hSgen⟩` from `hFG`. Establish `hregψ : ∀ ψ ∈ U, ∀ τ : E →+* ℂ, ∃ m, HasInfCharGL (Submodule.span ℂ {ψ}) τ m ∧ m.Nodup`.

Introduce `ψ hψ τ`. Take `⟨m, ⟨hcard, hm⟩, hnd⟩` from `hReg τ`. Conclude with `⟨m, ⟨hcard, fun u χ hχ => hm u χ ((Submodule.span_singleton_le_iff_mem ψ U).2 hψ hχ)⟩, hnd⟩`. Establish `hdec : ∀ ψ ∈ S, ∃ (C : Finset ℂ) (G : ℂ → GA E (r + s) → ℂ), An.ctn r ψ.1 = ∑ c ∈ C, G c ∧ ∀ c ∈ C, ∀ (t : ℝ) g, G c (aT E (r + s) r t * g) = Complex.exp (c * t) * G c g` using `fun ψ hψ => hNL E (r + s) r ψ (hU.2 ψ (hSU hψ)) (hSI ψ (hSU hψ)) (hregψ ψ (hSU hψ)) hr (by omega)`. Use `choose! Cs Gs hsum hGeig using hdec`.

Take `⟨τs, a, ha⟩` from `SliceUB2.lagrange (insert c (S.biUnion Cs)) c`. Establish `ha1 : ∑ t ∈ τs, a t * Complex.exp (c * t) = 1`. Rewrite using `[ha c (Finset.mem_insert_self _ _), if_pos rfl]`. Take `⟨T, hT⟩` from `exists_strictHenselian_absolutely_closed_local_ring U hU.2 r τs a`. Establish `hTval : ∀ ψ ∈ U, ∀ g, (T ψ).1 g = ∑ t ∈ τs, a t * An.ctn r ψ.1 (aT E (r + s) r t * g)`.

Introduce `ψ hψ g`. Rewrite using `[hT ψ hψ, Aop_apply, ctSm_val r (hU.2 ψ hψ)]`. Establish `hequiv : ∀ o, ∀ ψ ∈ U, T (act o ψ) = act o (T ψ)`. Introduce `o ψ hψ`. Rewrite using `[hT _ (hU.1 o ψ hψ), hT ψ hψ, ctSm_act r (hU.2 ψ hψ) o (hU.2 _ (hU.1 o ψ hψ)), Aop_act]`.

Establish `hgen : ∀ ψ ∈ S, ∀ g, (T ψ).1 g = ∑ c' ∈ Cs ψ, (if c' = c then 1 else 0) * Gs ψ c' g`. Introduce `ψ hψ g`. Rewrite using `[hTval ψ (hSU hψ), hsum ψ hψ]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_apply, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun c' hc' => by rw [hGeig ψ hψ c' hc']`. Use `_ = ∑ c' ∈ Cs ψ, (∑ t ∈ τs, a t * Complex.exp (c' * t)) * Gs ψ c' g := by`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c' _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun t _ => by ring`. Use `_ = ∑ c' ∈ Cs ψ, (if c' = c then 1 else 0) * Gs ψ c' g := by`. Use `Finset.sum_congr rfl fun c' hc' => ?_` and prove the remaining obligations. Rewrite using `[ha c' (Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨ψ, hψ, hc'⟩))]`.

Set `W : Submodule ℂ (Sm E (r + s))` to `{ carrier := {ψ | ψ ∈ U ∧ ∀ (t : ℝ) g, (T ψ).1 (aT E (r + s) r t * g) = Complex.exp (c * t) * (T ψ).1 g} add_mem' := fun {φ ψ} hφ hψ => ⟨U.add_mem hφ.1 hψ.1, fun t g => by`. Simplify using `only [map_add, Submodule.coe_add, Pi.add_apply, hφ.2 t g, hψ.2 t g, mul_add]⟩`. Use the proof step `zero_mem' := ⟨U.zero_mem, fun t g => by simp⟩`. Use the proof step `smul_mem' := fun b φ hφ => ⟨U.smul_mem b hφ.1, fun t g => by`. Simplify using `only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hφ.2 t g]`.

Use the proof step `ring⟩ }`. Establish `hWst : IsStable W`. Introduce and unpack `o ψ ⟨hψ, he⟩`. Use `⟨hU.1 o ψ hψ, fun t g => ?_⟩` and prove the remaining obligations. Establish `e1 : ltS (aT E (r + s) r t) (T ψ) = Complex.exp (c * t) • T ψ` using `Subtype.ext (funext fun g => he t g)`.

Establish `e2` using `congrArg (fun G : Sm E (r + s) => G.1 g) (congrArg (act o) e1)`. Simplify using `only [← ltS_act, map_smul] at e2`. Rewrite using `[hequiv o ψ hψ]`. Conclude with `e2`. Establish `hSW : (↑S : Set (Sm E (r + s))) ⊆ W`.

Introduce `ψ hψ`. Use `⟨hSU hψ, fun t g => ?_⟩` and prove the remaining obligations. Rewrite using `[hgen ψ hψ, hgen ψ hψ, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c' hc' => ?_` and prove the remaining obligations. Rewrite using `[hGeig ψ hψ c' hc']`.

Use `split_ifs with h`. Substitute `h` using the available equality. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Establish `hUW : U ≤ W` using `hSgen W hWst hSW`.

Establish `heig : ∀ ψ ∈ U, ∀ (t : ℝ) g, (T ψ).1 (aT E (r + s) r t * g) = Complex.exp (c * t) * (T ψ).1 g` using `fun ψ hψ => (hUW hψ).2`. Establish `hTφ : T φ ≠ 0`. Introduce `h0`. Establish `hz : ∀ g, ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g) = 0`. Introduce `g`.

Rewrite using `[← hTval φ hφU g, h0]`. Both sides reduce to the same expression. Apply `hFne` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Establish `hcomm : ∀ t t' : ℝ, aT E (r + s) r t' * (aT E (r + s) r t * g) = aT E (r + s) r t * (aT E (r + s) r t' * g)`.

Introduce `t t'`. Rewrite using `[← mul_assoc, ← mul_assoc, ← aT_add, ← aT_add, add_comm t' t]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun t' _ => by rw [hFeig t' g]; ring`.

Use `_ = ∑ t ∈ cs.support, b t * ∑ t' ∈ τs, a t' * An.ctn r φ.1 (aT E (r + s) r t' * (aT E (r + s) r t * g)) := by`. Repeatedly rewrite using `[hFval, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_` and prove the remaining obligations. Rewrite using `[hcomm]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = 0 := by simp [hz]`. Establish `hsplit : ∀ ψ ∈ U, ∀ (t : ℝ) g, (T ψ).1 (splitCentre E (r + s) t * g) = (T ψ).1 g`. Introduce `ψ hψ t g`. Rewrite using `[hTval ψ hψ, hTval ψ hψ]`.

Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[← mul_assoc, ← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm t (aT E (r + s) r u), mul_assoc, ctn_splitCentre (hSI ψ hψ)]`. Establish `hsc : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ z : ℂ, ∀ ψ ∈ U, cap τ u ψ = z • ψ`. Introduce `τ u`.

Take `⟨m, ⟨-, hm⟩, -⟩` from `hReg τ`. Conclude with `⟨_, hm u⟩`. Use `⟨T, ⟨hequiv, ⟨φ, hφU, hTφ⟩, ?_, ?_, ?_⟩, hTφ⟩` and prove the remaining obligations. Introduce `ψ hψ x g`. Rewrite using `[hTval ψ hψ, hTval ψ hψ]`.

Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Take `⟨y, hy⟩` from `aT_mul_unip (r + s) r t x`. Use `congr 1`. Rewrite using `[← mul_assoc, hy, mul_assoc, ctn_unip (hU.2 ψ hψ)]`. Introduce `ψ hψ k g m₂`.

Take `⟨χ, hχA, hχ⟩` from `(F_slicesU U hU.1 hU.2 hsc T hequiv τs a hTval ψ hψ k g).1 m₂`. Use `⟨χ, hχA, hχ, fun t m₁ => ?_, fun r₁ h1 h2 c₁ hc₁ => ⟨ψ, hψ, exp_left hD hFin hr hs ψ (hU.2 ψ hψ) τs a (T ψ).1 (hTval ψ hψ) χ hχA m₂ _ hχ r₁ h1 h2 c₁ hc₁⟩⟩` and prove the remaining obligations. Establish `e : lev (Ad E) r s (splitCentre E r t * m₁, m₂) = aT E (r + s) r t * lev (Ad E) r s (m₁, m₂)`. Rewrite using `[show ((splitCentre E r t * m₁, m₂) : GA E r × GA E s) = (splitCentre E r t, 1) * (m₁, m₂) by simp, map_mul, splitCentre_eq_aT, lev_aT_left r s r le_rfl]`. Rewrite using `[hχ, hχ, e, mul_assoc, heig ψ hψ]`.

Introduce `ψ hψ k g m₁`. Take `⟨χ, hχA, hχ⟩` from `(F_slicesU U hU.1 hU.2 hsc T hequiv τs a hTval ψ hψ k g).2 m₁`. Use `⟨χ, hχA, hχ, fun t m₂ => ?_, fun r₂ h1 h2 c₂ hc₂ => ⟨ψ, hψ, exp_right hD hFin hr hs ψ (hU.2 ψ hψ) τs a (T ψ).1 (hTval ψ hψ) c (heig ψ hψ) χ hχA m₁ _ hχ r₂ h1 h2 c₂ hc₂⟩⟩` and prove the remaining obligations. Establish `e : lev (Ad E) r s (m₁, splitCentre E s t * m₂) = splitCentre E (r + s) t * (aT E (r + s) r (-t) * lev (Ad E) r s (m₁, m₂))`. Rewrite using `[show ((m₁, splitCentre E s t * m₂) : GA E r × GA E s) = (1, splitCentre E s t) * (m₁, m₂) by simp, map_mul, splitCentre_eq_aT, lev_aT_right r s s le_rfl, splitCentre_eq_aT, mul_assoc]`.

Rewrite using `[hχ, hχ, e, mul_assoc, hsplit ψ hψ, mul_assoc, heig ψ hψ]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sliceU_of_noLog2 (hNL : NoLog) : SliceU := by
  intro E _ _ _ r s hr hs U hU hFG hSI hReg φ hφU c hc
  have hD := dict_holds
  have hFin := finTr_holds
  obtain ⟨F₀, hCT, F, hFspan, hFne, hFeig⟩ := hc
  have hAφ := hU.2 φ hφU
  obtain ⟨κ, -, rfl⟩ := ((hD E (r + s)).2.2.2 φ hAφ r hr (by omega)).2 F₀ hCT
  obtain ⟨cs, hcs⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hFspan
  obtain ⟨b, hb⟩ : ∃ b : ℝ → ℂ, b = fun t => cs t * κ := ⟨_, rfl⟩
  have hFval : ∀ g, F g = ∑ t ∈ cs.support, b t * An.ctn r φ.1 (aT E (r + s) r t * g) := by
    intro g
    rw [← hcs, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, hb, mul_assoc]

  obtain ⟨S, hSU, hSgen⟩ := hFG
  have hregψ : ∀ ψ ∈ U, ∀ τ : E →+* ℂ, ∃ m, HasInfCharGL (Submodule.span ℂ {ψ}) τ m ∧ m.Nodup := by
    intro ψ hψ τ
    obtain ⟨m, ⟨hcard, hm⟩, hnd⟩ := hReg τ
    exact ⟨m, ⟨hcard, fun u χ hχ => hm u χ ((Submodule.span_singleton_le_iff_mem ψ U).2 hψ hχ)⟩, hnd⟩
  have hdec : ∀ ψ ∈ S, ∃ (C : Finset ℂ) (G : ℂ → GA E (r + s) → ℂ), An.ctn r ψ.1 = ∑ c ∈ C, G c ∧
      ∀ c ∈ C, ∀ (t : ℝ) g, G c (aT E (r + s) r t * g) = Complex.exp (c * t) * G c g := fun ψ hψ =>
    hNL E (r + s) r ψ (hU.2 ψ (hSU hψ)) (hSI ψ (hSU hψ)) (hregψ ψ (hSU hψ)) hr (by omega)
  choose! Cs Gs hsum hGeig using hdec
  obtain ⟨τs, a, ha⟩ := SliceUB2.lagrange (insert c (S.biUnion Cs)) c
  have ha1 : ∑ t ∈ τs, a t * Complex.exp (c * t) = 1 := by
    rw [ha c (Finset.mem_insert_self _ _), if_pos rfl]

  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring U hU.2 r τs a
  have hTval : ∀ ψ ∈ U, ∀ g, (T ψ).1 g = ∑ t ∈ τs, a t * An.ctn r ψ.1 (aT E (r + s) r t * g) := by
    intro ψ hψ g
    rw [hT ψ hψ, Aop_apply, ctSm_val r (hU.2 ψ hψ)]
  have hequiv : ∀ o, ∀ ψ ∈ U, T (act o ψ) = act o (T ψ) := by
    intro o ψ hψ
    rw [hT _ (hU.1 o ψ hψ), hT ψ hψ, ctSm_act r (hU.2 ψ hψ) o (hU.2 _ (hU.1 o ψ hψ)), Aop_act]

  have hgen : ∀ ψ ∈ S, ∀ g, (T ψ).1 g = ∑ c' ∈ Cs ψ, (if c' = c then 1 else 0) * Gs ψ c' g := by
    intro ψ hψ g
    rw [hTval ψ (hSU hψ), hsum ψ hψ]
    calc ∑ t ∈ τs, a t * (∑ c' ∈ Cs ψ, Gs ψ c') (aT E (r + s) r t * g)
        = ∑ t ∈ τs, ∑ c' ∈ Cs ψ, a t * (Complex.exp (c' * t) * Gs ψ c' g) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.sum_apply, Finset.mul_sum]
          exact Finset.sum_congr rfl fun c' hc' => by rw [hGeig ψ hψ c' hc']
      _ = ∑ c' ∈ Cs ψ, (∑ t ∈ τs, a t * Complex.exp (c' * t)) * Gs ψ c' g := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c' _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun t _ => by ring
      _ = ∑ c' ∈ Cs ψ, (if c' = c then 1 else 0) * Gs ψ c' g := by
          refine Finset.sum_congr rfl fun c' hc' => ?_
          rw [ha c' (Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨ψ, hψ, hc'⟩))]

  let W : Submodule ℂ (Sm E (r + s)) :=
    { carrier := {ψ | ψ ∈ U ∧ ∀ (t : ℝ) g, (T ψ).1 (aT E (r + s) r t * g) = Complex.exp (c * t) * (T ψ).1 g}
      add_mem' := fun {φ ψ} hφ hψ => ⟨U.add_mem hφ.1 hψ.1, fun t g => by
        simp only [map_add, Submodule.coe_add, Pi.add_apply, hφ.2 t g, hψ.2 t g, mul_add]⟩
      zero_mem' := ⟨U.zero_mem, fun t g => by simp⟩
      smul_mem' := fun b φ hφ => ⟨U.smul_mem b hφ.1, fun t g => by
        simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hφ.2 t g]
        ring⟩ }
  have hWst : IsStable W := by
    rintro o ψ ⟨hψ, he⟩
    refine ⟨hU.1 o ψ hψ, fun t g => ?_⟩
    have e1 : ltS (aT E (r + s) r t) (T ψ) = Complex.exp (c * t) • T ψ := Subtype.ext (funext fun g => he t g)
    have e2 := congrArg (fun G : Sm E (r + s) => G.1 g) (congrArg (act o) e1)
    simp only [← ltS_act, map_smul] at e2
    rw [hequiv o ψ hψ]
    exact e2
  have hSW : (↑S : Set (Sm E (r + s))) ⊆ W := by
    intro ψ hψ
    refine ⟨hSU hψ, fun t g => ?_⟩
    rw [hgen ψ hψ, hgen ψ hψ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' hc' => ?_
    rw [hGeig ψ hψ c' hc']
    split_ifs with h
    · subst h
      ring
    · simp
  have hUW : U ≤ W := hSgen W hWst hSW
  have heig : ∀ ψ ∈ U, ∀ (t : ℝ) g, (T ψ).1 (aT E (r + s) r t * g) = Complex.exp (c * t) * (T ψ).1 g :=
    fun ψ hψ => (hUW hψ).2

  have hTφ : T φ ≠ 0 := by
    intro h0
    have hz : ∀ g, ∑ t ∈ τs, a t * An.ctn r φ.1 (aT E (r + s) r t * g) = 0 := by
      intro g
      rw [← hTval φ hφU g, h0]
      rfl
    apply hFne
    funext g
    have hcomm : ∀ t t' : ℝ, aT E (r + s) r t' * (aT E (r + s) r t * g) =
        aT E (r + s) r t * (aT E (r + s) r t' * g) := by
      intro t t'
      rw [← mul_assoc, ← mul_assoc, ← aT_add, ← aT_add, add_comm t' t]
    calc F g = (∑ t' ∈ τs, a t' * Complex.exp (c * t')) * F g := by rw [ha1, one_mul]
      _ = ∑ t' ∈ τs, a t' * F (aT E (r + s) r t' * g) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun t' _ => by rw [hFeig t' g]; ring
      _ = ∑ t ∈ cs.support, b t * ∑ t' ∈ τs, a t' * An.ctn r φ.1 (aT E (r + s) r t' * (aT E (r + s) r t * g)) := by
          simp_rw [hFval, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
          rw [hcomm]
          ring
      _ = 0 := by simp [hz]
  have hsplit : ∀ ψ ∈ U, ∀ (t : ℝ) g, (T ψ).1 (splitCentre E (r + s) t * g) = (T ψ).1 g := by
    intro ψ hψ t g
    rw [hTval ψ hψ, hTval ψ hψ]
    refine Finset.sum_congr rfl fun u _ => ?_
    congr 1
    rw [← mul_assoc, ← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm t (aT E (r + s) r u), mul_assoc,
      ctn_splitCentre (hSI ψ hψ)]
  have hsc : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ z : ℂ, ∀ ψ ∈ U, cap τ u ψ = z • ψ := by
    intro τ u
    obtain ⟨m, ⟨-, hm⟩, -⟩ := hReg τ
    exact ⟨_, hm u⟩
  refine ⟨T, ⟨hequiv, ⟨φ, hφU, hTφ⟩, ?_, ?_, ?_⟩, hTφ⟩
  · intro ψ hψ x g
    rw [hTval ψ hψ, hTval ψ hψ]
    refine Finset.sum_congr rfl fun t _ => ?_
    obtain ⟨y, hy⟩ := aT_mul_unip (r + s) r t x
    congr 1
    rw [← mul_assoc, hy, mul_assoc, ctn_unip (hU.2 ψ hψ)]
  · intro ψ hψ k g m₂
    obtain ⟨χ, hχA, hχ⟩ := (F_slicesU U hU.1 hU.2 hsc T hequiv τs a hTval ψ hψ k g).1 m₂
    refine ⟨χ, hχA, hχ, fun t m₁ => ?_, fun r₁ h1 h2 c₁ hc₁ =>
      ⟨ψ, hψ, exp_left hD hFin hr hs ψ (hU.2 ψ hψ) τs a (T ψ).1 (hTval ψ hψ) χ hχA m₂ _ hχ r₁ h1 h2 c₁ hc₁⟩⟩
    have e : lev (Ad E) r s (splitCentre E r t * m₁, m₂) = aT E (r + s) r t * lev (Ad E) r s (m₁, m₂) := by
      rw [show ((splitCentre E r t * m₁, m₂) : GA E r × GA E s) = (splitCentre E r t, 1) * (m₁, m₂) by simp,
        map_mul, splitCentre_eq_aT, lev_aT_left r s r le_rfl]
    rw [hχ, hχ, e, mul_assoc, heig ψ hψ]
  · intro ψ hψ k g m₁
    obtain ⟨χ, hχA, hχ⟩ := (F_slicesU U hU.1 hU.2 hsc T hequiv τs a hTval ψ hψ k g).2 m₁
    refine ⟨χ, hχA, hχ, fun t m₂ => ?_, fun r₂ h1 h2 c₂ hc₂ =>
      ⟨ψ, hψ, exp_right hD hFin hr hs ψ (hU.2 ψ hψ) τs a (T ψ).1 (hTval ψ hψ) c (heig ψ hψ) χ hχA m₁ _ hχ
        r₂ h1 h2 c₂ hc₂⟩⟩
    have e : lev (Ad E) r s (m₁, splitCentre E s t * m₂) =
        splitCentre E (r + s) t * (aT E (r + s) r (-t) * lev (Ad E) r s (m₁, m₂)) := by
      rw [show ((m₁, splitCentre E s t * m₂) : GA E r × GA E s) = (1, splitCentre E s t) * (m₁, m₂) by simp,
        map_mul, splitCentre_eq_aT, lev_aT_right r s s le_rfl, splitCentre_eq_aT, mul_assoc]
    rw [hχ, hχ, e, mul_assoc, hsplit ψ hψ, mul_assoc, heig ψ hψ]
    congr 2
    push_cast
    ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUniqueness

end
