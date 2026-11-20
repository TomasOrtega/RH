import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepA
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.SdNormCpow
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepD
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsUnitaryAbsPow

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Rs

/- English proof (translation)
Introduce `hR hJ hInf hIA hSI hSA hSH hG E _ _ _ r s hr hs V V₁ V₂ z₁ z₂ hV hV₁ hV₂ hemb τ hτ hsum hre a₁ d₁ a₂ d₂ π₁ π₂ hu₁ hn₁ h₁ hu₂ hn₂ h₂`. Establish `hr₁ : d₁ * a₁ = r` using `by obtain ⟨h, -⟩ := h₁; simpa using h`. Establish `hs₂ : d₂ * a₂ = s` using `by obtain ⟨h, -⟩ := h₂; simpa using h`. Establish `hd₁ : 0 < d₁` using `Nat.pos_of_ne_zero fun h => by subst h; omega`. Establish `hd₂ : 0 < d₂` using `Nat.pos_of_ne_zero fun h => by subst h; omega`.

Establish `ha₁ : 1 ≤ a₁` using `Nat.pos_of_ne_zero fun h => by subst h; omega`. Establish `ha₂ : 1 ≤ a₂` using `Nat.pos_of_ne_zero fun h => by subst h; omega`. Establish `hexp` using `StrStepC.sat_expand hSI hSA hSH V V₁ V₂ z₁ z₂ hV hV₁ hV₂ hemb π₁ π₂ ha₁ ha₂ hu₁ hn₁ hu₂ hn₂ h₁ h₂`. Establish `hp₀` using `StrStepC.perm_of hR π₁ π₂ ha₁ ha₂ (fun i : Fin d₁ => z₁ - (s : ℂ) / 2 + (spehExp d₁ i : ℂ)) (fun j : Fin d₂ => z₂ + (r : ℂ) / 2 + (spehExp d₂ j : ℂ)) (hexp.mono fun w ⟨BV, B₁, B₂, _, h1, h2, e, hh⟩ => ⟨BV, B₁, B₂, h1, h2, e, hh⟩)`. Break down `StrStepD.match_left ha₁ ha₂ π₁ π₂ hn₁ hn₂ _ _ hp₀ ⟨d₁ - 1, by omega⟩ with ⟨i', hi'⟩ | ⟨j, hj, hcls⟩` into its components or cases.

It suffices to derive a contradiction. Establish `h` using `congrArg Complex.re hi'`. Establish `hi : ((d₁ - 1 : ℕ) : ℝ) = d₁ - 1` using `by rw [Nat.cast_sub (by omega)]; simp`. Simplify using `only [spehExp, Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.conj_re, Complex.ofReal_re, Complex.div_ofNat_re, Complex.natCast_re, hi] at h`. Establish `: (0 : ℝ) ≤ (i' : ℕ)` using `Nat.cast_nonneg _`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `him : z₁.im = z₂.im`. Establish `h` using `congrArg Complex.im hj`. Simplify `h` using `[spehExp, map_ofNat, Complex.div_ofNat_im]`. Establish `hsim` using `congrArg Complex.im hsum`.

Simplify using `only [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero, Complex.zero_im] at hsim`. Establish `h1im : z₁.im = 0`. Establish `: ((r : ℝ) + s) * z₁.im = 0` using `by rw [← him] at hsim; linarith`. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Establish `: (0 : ℝ) < r` using `by exact_mod_cast hr`.

Establish `: (0 : ℝ) ≤ s` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h`. Establish `h2im : z₂.im = 0` using `him ▸ h1im`. Take `⟨ha, hh⟩` from `Sigma.mk.inj_iff.1 hcls`.

Substitute `ha` using the available equality. Establish `hmk : CG.mk π₁ = CG.mk π₂` using `eq_of_heq hh`. Establish `hiso : π₁.Iso π₂` using `Quotient.exact hmk`. Substitute `hr₁ hs₂` using the available equality. Take `⟨c₁, hc₁d⟩ : ∃ c : ℝ, c = z₁.re - ((d₂ * a₁ : ℕ) : ℝ) / 2` from `⟨_, rfl⟩`.

Take `⟨c₂, hc₂d⟩ : ∃ c : ℝ, c = z₂.re + ((d₁ * a₁ : ℕ) : ℝ) / 2` from `⟨_, rfl⟩`. Establish `hc₁ : ((c₁ : ℝ) : ℂ) = z₁ - ((d₂ * a₁ : ℕ) : ℂ) / 2`. Apply the tactic sequence `apply Complex.ext <;> simp [hc₁d, h1im]`. Establish `hc₂ : ((c₂ : ℝ) : ℂ) = z₂ + ((d₁ * a₁ : ℕ) : ℂ) / 2`. Apply the tactic sequence `apply Complex.ext <;> simp [hc₂d, h2im]`.

Take `⟨m, hm, hnd, hint⟩` from `hτ`. Take `⟨m₁, m₂, hm₁, hm₂, hme⟩` from `hInf E _ _ V V₁ V₂ z₁ z₂ hV hV₁ hV₂ hemb τ m hm`. Take `⟨m₀, hm₀, hme₁⟩` from `hIA E _ a₁ d₁ V₁ π₁ hV₁ h₁ τ m₁ hm₁`. Take `⟨m₀', hm₀', hme₂⟩` from `hIA E _ a₁ d₂ V₂ π₂ hV₂ h₂ τ m₂ hm₂`. Establish `hm₀e : m₀' = m₀` using `hm₀'.unique (hiso.hasInfChar hm₀)`.

Establish `hform : m = (∑ i : Fin d₁, m₀.map (· + (spehExp d₁ i : ℂ))).map (· + ((c₁ : ℝ) : ℂ)) + (∑ j : Fin d₂, m₀.map (· + (spehExp d₂ j : ℂ))).map (· + ((c₂ : ℝ) : ℂ))`. Rewrite using `[hme, hme₁, hme₂, hm₀e, hc₁, hc₂]`. Establish `hne : m₀ ≠ 0`. Introduce and unpack `rfl`. Establish `h` using `hm.1`.

Rewrite `h` using `[hform]`. Simplify using `at h`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨hdisj, hintS⟩` from `StrStepD.of_infChar m m₀ c₁ c₂ hform hne hnd hint`. Establish `hexp' : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ BV B₁ B₂ : Multiset ℂˣ, SatV V w BV ∧ (CG.mk π₁).HasSat w B₁ ∧ (CG.mk π₂).HasSat w B₂ ∧ BV.map (fun b : ℂˣ => (b : ℂ)) = (∑ i : Fin d₁, B₁.map fun b : ℂˣ => (b : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((c₁ + spehE …`.

Use `hexp.mono fun w ⟨BV, B₁, B₂, h0, h1, h2, e, hh⟩ => ⟨BV, B₁, B₂, h0, h1, h2, ?_, hh⟩` and prove the remaining obligations. Rewrite using `[e]`. Simplify using `only [Complex.ofReal_add, hc₁, hc₂]`. Establish `hp` using `StrStepC.perm_of hR π₁ π₂ ha₁ ha₁ (fun i : Fin d₁ => ((c₁ + spehExp d₁ i : ℝ) : ℂ)) (fun j : Fin d₂ => ((c₂ + spehExp d₂ j : ℝ) : ℂ)) (hexp'.mono fun w ⟨BV, B₁, B₂, _, h1, h2, e, hh⟩ => ⟨BV, B₁, B₂, h1, h2, e, hh⟩)`. Establish `hneg : ∀ u ∈ StrStepD.strSet c₁ c₂ d₁ d₂, -u ∈ StrStepD.strSet c₁ c₂ d₁ d₂`.

Introduce `u hu`. Break down `StrStepD.mem_strSet.1 hu with ⟨i, rfl⟩ | ⟨j, rfl⟩` into its components or cases. Break down `StrStepD.match_left ha₁ ha₁ π₁ π₂ hn₁ hn₂ _ _ hp i with ⟨i', e⟩ | ⟨j, e, -⟩` into its components or cases. Establish `h` using `congrArg Complex.re e`. Simplify using `only [Complex.ofReal_re, Complex.neg_re, Complex.conj_re] at h`.

Conclude with `StrStepD.mem_strSet.2 (Or.inl ⟨i', by linarith⟩)`. Establish `h` using `congrArg Complex.re e`. Simplify using `only [Complex.ofReal_re, Complex.neg_re, Complex.conj_re] at h`. Conclude with `StrStepD.mem_strSet.2 (Or.inr ⟨j, by linarith⟩)`. Break down `StrStepD.match_right ha₁ ha₁ π₁ π₂ hn₁ hn₂ _ _ hp j with ⟨j', e⟩ | ⟨i, e, -⟩` into its components or cases.

Establish `h` using `congrArg Complex.re e`. Simplify using `only [Complex.ofReal_re, Complex.neg_re, Complex.conj_re] at h`. Conclude with `StrStepD.mem_strSet.2 (Or.inr ⟨j', by linarith⟩)`. Establish `h` using `congrArg Complex.re e`. Simplify using `only [Complex.ofReal_re, Complex.neg_re, Complex.conj_re] at h`.

Conclude with `StrStepD.mem_strSet.2 (Or.inl ⟨i, by linarith⟩)`. Use `GlobalTheory.Published.JacquetShalikaModel.infinite_places (E := E)` as an intermediate fact. Take `⟨w, BV, B₁, B₂, hBV, hs₁, hs₂, e, -⟩` from `hexp'.exists`. Establish `hB₂ : B₂ = B₁`. Rewrite `hs₂` using `[← hmk]`.

Conclude with `hs₂.unique hs₁`. Rewrite `e` using `[hB₂]`. Establish `hq : 1 < Ideal.absNorm w.asIdeal` using `NumberField.HeightOneSpectrum.one_lt_absNorm w`. Establish `hM : ∀ z, z ∈ BV.map (fun b : ℂˣ => (b : ℂ)) ↔ ∃ x ∈ StrStepD.strSet c₁ c₂ d₁ d₂, ∃ β ∈ B₁.map (fun b : ℂˣ => (b : ℂ)), z = β * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(x : ℂ))`. Introduce `z`.

Rewrite using `[e, ← StrStepD.mem_sat]`. Simplify using `only [Multiset.map_map, Function.comp_def, Complex.ofReal_add]`. Establish `hgap : ∀ z : ℂ, ‖z‖ < (Ideal.absNorm w.asIdeal : ℝ) ^ (-(1 / 2) : ℝ) → (BV.map fun b : ℂˣ => (b : ℂ)).count z ≤ (BV.map fun b : ℂˣ => (b : ℂ)).count ((Ideal.absNorm w.asIdeal : ℂ) * z)` using `fun z hz => hG E _ V hV w BV hBV z hz`. Establish `hbound : ∀ β ∈ B₁.map (fun b : ℂˣ => (b : ℂ)), (Ideal.absNorm w.asIdeal : ℝ) ^ (-(1 / 2) : ℝ) < ‖β‖ ∧ ‖β‖ < (Ideal.absNorm w.asIdeal : ℝ) ^ (1 / 2 : ℝ)`. Introduce `β hβ`.

Take `⟨b, hb, rfl⟩` from `Multiset.mem_map.1 hβ`. Conclude with `hJ E a₁ (CG.mk π₁) ((CG.isUnitary_mk π₁).2 hu₁) w B₁ hs₁ b hb`. Choose the witnesses or unpack the hypotheses as in `⟨α, hα⟩ : ∃ α, α ∈ B₁.map (fun b : ℂˣ => (b : ℂ)) := by`. Take `⟨b, hb⟩` from `Multiset.card_pos_iff_exists_mem.1 (by rw [hs₁.card]; omega)`. Conclude with `⟨_, Multiset.mem_map_of_mem _ hb⟩`.

Establish `hP : ∀ u ∈ StrStepD.strSet c₁ c₂ d₁ d₂, 1 ≤ u → u - 1 ∈ StrStepD.strSet c₁ c₂ d₁ d₂` using `fun u hu hu1 => StrStepA.step_down _ hq _ hbound hα _ hintS _ hM hgap hu hu1`. Establish `hlin : (d₁ : ℝ) * c₁ + d₂ * c₂ = 0`. Establish `hsre` using `congrArg Complex.re hsum`. Simplify using `only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, h1im, h2im, mul_zero, sub_zero, Complex.zero_re] at hsre`. Establish `ha : (0 : ℝ) < a₁` using `by exact_mod_cast ha₁`.

Establish `: (a₁ : ℝ) * (d₁ * c₁ + d₂ * c₂) = 0`. Rewrite using `[hc₁d, hc₂d]`. Move the coercions through the operations in `at hsre ⊢`. Take the linear combination `hsre`. Break down `mul_eq_zero.1 this with h | h` into its components or cases.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h`. Establish `hc₁n : c₁ < 0` using `by rw [hc₁d]; linarith`. Establish `hc₂p : 0 < c₂`. Establish `: (0 : ℝ) < d₁` using `by exact_mod_cast hd₁`.

Establish `: (0 : ℝ) < d₂` using `by exact_mod_cast hd₂`. Use the polynomial consequences of the given equalities and inequalities. Establish `hadj` using `StrStepA.adjacent c₁ c₂ d₁ d₂ hd₁ hd₂ (StrStepD.strSet c₁ c₂ d₁ d₂) (fun x => Iff.rfl) hdisj hintS hneg hP (by linarith)`. Establish `hc₁v : c₁ = -(d₂ : ℝ) / 2`. Establish `h : ((d₁ : ℝ) + d₂) * (c₁ + d₂ / 2) = 0` using `by linear_combination hlin - (d₂ : ℝ) * hadj`.

Break down `mul_eq_zero.1 h with h | h` into its components or cases. Establish `: (0 : ℝ) < d₁` using `by exact_mod_cast hd₁`. Establish `: (0 : ℝ) ≤ d₂` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hc₂v : c₂ = (d₁ : ℝ) / 2` using `by linarith`. Move the coercions through the operations in `at hc₁d hc₂d`. Use `⟨by rw [hmk], ?_, ?_⟩` and prove the remaining obligations. Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules.

Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `[h1im]`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `[h2im]`.
-/
theorem stringStep_of : GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.JacquetShalikaBound → InfInd2 → InfAsc →
    SatInd2 → SatAsc → SatHerm → Gap → StringStep := by
  intro hR hJ hInf hIA hSI hSA hSH hG E _ _ _ r s hr hs V V₁ V₂ z₁ z₂ hV hV₁ hV₂ hemb τ hτ hsum hre
    a₁ d₁ a₂ d₂ π₁ π₂ hu₁ hn₁ h₁ hu₂ hn₂ h₂

  have hr₁ : d₁ * a₁ = r := by obtain ⟨h, -⟩ := h₁; simpa using h
  have hs₂ : d₂ * a₂ = s := by obtain ⟨h, -⟩ := h₂; simpa using h
  have hd₁ : 0 < d₁ := Nat.pos_of_ne_zero fun h => by subst h; omega
  have hd₂ : 0 < d₂ := Nat.pos_of_ne_zero fun h => by subst h; omega
  have ha₁ : 1 ≤ a₁ := Nat.pos_of_ne_zero fun h => by subst h; omega
  have ha₂ : 1 ≤ a₂ := Nat.pos_of_ne_zero fun h => by subst h; omega

  have hexp := StrStepC.sat_expand hSI hSA hSH V V₁ V₂ z₁ z₂ hV hV₁ hV₂ hemb π₁ π₂ ha₁ ha₂ hu₁ hn₁ hu₂ hn₂ h₁ h₂
  have hp₀ := StrStepC.perm_of hR π₁ π₂ ha₁ ha₂ (fun i : Fin d₁ => z₁ - (s : ℂ) / 2 + (spehExp d₁ i : ℂ))
    (fun j : Fin d₂ => z₂ + (r : ℂ) / 2 + (spehExp d₂ j : ℂ))
    (hexp.mono fun w ⟨BV, B₁, B₂, _, h1, h2, e, hh⟩ => ⟨BV, B₁, B₂, h1, h2, e, hh⟩)

  rcases StrStepD.match_left ha₁ ha₂ π₁ π₂ hn₁ hn₂ _ _ hp₀ ⟨d₁ - 1, by omega⟩ with ⟨i', hi'⟩ | ⟨j, hj, hcls⟩
  · exfalso
    have h := congrArg Complex.re hi'
    have hi : ((d₁ - 1 : ℕ) : ℝ) = d₁ - 1 := by rw [Nat.cast_sub (by omega)]; simp
    simp only [spehExp, Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.conj_re, Complex.ofReal_re,
      Complex.div_ofNat_re, Complex.natCast_re, hi] at h
    have : (0 : ℝ) ≤ (i' : ℕ) := Nat.cast_nonneg _
    linarith
  have him : z₁.im = z₂.im := by
    have h := congrArg Complex.im hj
    simpa [spehExp, map_ofNat, Complex.div_ofNat_im] using h
  have hsim := congrArg Complex.im hsum
  simp only [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
    Complex.zero_im] at hsim
  have h1im : z₁.im = 0 := by
    have : ((r : ℝ) + s) * z₁.im = 0 := by rw [← him] at hsim; linarith
    rcases mul_eq_zero.1 this with h | h
    · have : (0 : ℝ) < r := by exact_mod_cast hr
      have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
      linarith
    · exact h
  have h2im : z₂.im = 0 := him ▸ h1im
  obtain ⟨ha, hh⟩ := Sigma.mk.inj_iff.1 hcls
  subst ha
  have hmk : CG.mk π₁ = CG.mk π₂ := eq_of_heq hh
  have hiso : π₁.Iso π₂ := Quotient.exact hmk
  subst hr₁ hs₂

  obtain ⟨c₁, hc₁d⟩ : ∃ c : ℝ, c = z₁.re - ((d₂ * a₁ : ℕ) : ℝ) / 2 := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂d⟩ : ∃ c : ℝ, c = z₂.re + ((d₁ * a₁ : ℕ) : ℝ) / 2 := ⟨_, rfl⟩
  have hc₁ : ((c₁ : ℝ) : ℂ) = z₁ - ((d₂ * a₁ : ℕ) : ℂ) / 2 := by
    apply Complex.ext <;> simp [hc₁d, h1im]
  have hc₂ : ((c₂ : ℝ) : ℂ) = z₂ + ((d₁ * a₁ : ℕ) : ℂ) / 2 := by
    apply Complex.ext <;> simp [hc₂d, h2im]

  obtain ⟨m, hm, hnd, hint⟩ := hτ
  obtain ⟨m₁, m₂, hm₁, hm₂, hme⟩ := hInf E _ _ V V₁ V₂ z₁ z₂ hV hV₁ hV₂ hemb τ m hm
  obtain ⟨m₀, hm₀, hme₁⟩ := hIA E _ a₁ d₁ V₁ π₁ hV₁ h₁ τ m₁ hm₁
  obtain ⟨m₀', hm₀', hme₂⟩ := hIA E _ a₁ d₂ V₂ π₂ hV₂ h₂ τ m₂ hm₂
  have hm₀e : m₀' = m₀ := hm₀'.unique (hiso.hasInfChar hm₀)
  have hform : m = (∑ i : Fin d₁, m₀.map (· + (spehExp d₁ i : ℂ))).map (· + ((c₁ : ℝ) : ℂ)) +
      (∑ j : Fin d₂, m₀.map (· + (spehExp d₂ j : ℂ))).map (· + ((c₂ : ℝ) : ℂ)) := by
    rw [hme, hme₁, hme₂, hm₀e, hc₁, hc₂]
  have hne : m₀ ≠ 0 := by
    rintro rfl
    have h := hm.1
    rw [hform] at h
    simp at h
    linarith
  obtain ⟨hdisj, hintS⟩ := StrStepD.of_infChar m m₀ c₁ c₂ hform hne hnd hint

  have hexp' : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ BV B₁ B₂ : Multiset ℂˣ, SatV V w BV ∧
      (CG.mk π₁).HasSat w B₁ ∧ (CG.mk π₂).HasSat w B₂ ∧
      BV.map (fun b : ℂˣ => (b : ℂ)) =
        (∑ i : Fin d₁, B₁.map fun b : ℂˣ =>
          (b : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((c₁ + spehExp d₁ i : ℝ) : ℂ))) +
          ∑ j : Fin d₂, B₂.map (fun b : ℂˣ =>
            (b : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-((c₂ + spehExp d₂ j : ℝ) : ℂ))) ∧
      BV.map (fun b => (star b)⁻¹) = BV ∧ B₁.map (fun b => (star b)⁻¹) = B₁ ∧
        B₂.map (fun b => (star b)⁻¹) = B₂ := by
    refine hexp.mono fun w ⟨BV, B₁, B₂, h0, h1, h2, e, hh⟩ => ⟨BV, B₁, B₂, h0, h1, h2, ?_, hh⟩
    rw [e]
    simp only [Complex.ofReal_add, hc₁, hc₂]
  have hp := StrStepC.perm_of hR π₁ π₂ ha₁ ha₁ (fun i : Fin d₁ => ((c₁ + spehExp d₁ i : ℝ) : ℂ))
    (fun j : Fin d₂ => ((c₂ + spehExp d₂ j : ℝ) : ℂ))
    (hexp'.mono fun w ⟨BV, B₁, B₂, _, h1, h2, e, hh⟩ => ⟨BV, B₁, B₂, h1, h2, e, hh⟩)
  have hneg : ∀ u ∈ StrStepD.strSet c₁ c₂ d₁ d₂, -u ∈ StrStepD.strSet c₁ c₂ d₁ d₂ := by
    intro u hu
    rcases StrStepD.mem_strSet.1 hu with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rcases StrStepD.match_left ha₁ ha₁ π₁ π₂ hn₁ hn₂ _ _ hp i with ⟨i', e⟩ | ⟨j, e, -⟩
      · have h := congrArg Complex.re e
        simp only [Complex.ofReal_re, Complex.neg_re, Complex.conj_re] at h
        exact StrStepD.mem_strSet.2 (Or.inl ⟨i', by linarith⟩)
      · have h := congrArg Complex.re e
        simp only [Complex.ofReal_re, Complex.neg_re, Complex.conj_re] at h
        exact StrStepD.mem_strSet.2 (Or.inr ⟨j, by linarith⟩)
    · rcases StrStepD.match_right ha₁ ha₁ π₁ π₂ hn₁ hn₂ _ _ hp j with ⟨j', e⟩ | ⟨i, e, -⟩
      · have h := congrArg Complex.re e
        simp only [Complex.ofReal_re, Complex.neg_re, Complex.conj_re] at h
        exact StrStepD.mem_strSet.2 (Or.inr ⟨j', by linarith⟩)
      · have h := congrArg Complex.re e
        simp only [Complex.ofReal_re, Complex.neg_re, Complex.conj_re] at h
        exact StrStepD.mem_strSet.2 (Or.inl ⟨i, by linarith⟩)

  have := GlobalTheory.Published.JacquetShalikaModel.infinite_places (E := E)
  obtain ⟨w, BV, B₁, B₂, hBV, hs₁, hs₂, e, -⟩ := hexp'.exists
  have hB₂ : B₂ = B₁ := by
    rw [← hmk] at hs₂
    exact hs₂.unique hs₁
  rw [hB₂] at e
  have hq : 1 < Ideal.absNorm w.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hM : ∀ z, z ∈ BV.map (fun b : ℂˣ => (b : ℂ)) ↔ ∃ x ∈ StrStepD.strSet c₁ c₂ d₁ d₂,
      ∃ β ∈ B₁.map (fun b : ℂˣ => (b : ℂ)), z = β * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(x : ℂ)) := by
    intro z
    rw [e, ← StrStepD.mem_sat]
    simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_add]
  have hgap : ∀ z : ℂ, ‖z‖ < (Ideal.absNorm w.asIdeal : ℝ) ^ (-(1 / 2) : ℝ) →
      (BV.map fun b : ℂˣ => (b : ℂ)).count z ≤
        (BV.map fun b : ℂˣ => (b : ℂ)).count ((Ideal.absNorm w.asIdeal : ℂ) * z) :=
    fun z hz => hG E _ V hV w BV hBV z hz
  have hbound : ∀ β ∈ B₁.map (fun b : ℂˣ => (b : ℂ)), (Ideal.absNorm w.asIdeal : ℝ) ^ (-(1 / 2) : ℝ) < ‖β‖ ∧
      ‖β‖ < (Ideal.absNorm w.asIdeal : ℝ) ^ (1 / 2 : ℝ) := by
    intro β hβ
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hβ
    exact hJ E a₁ (CG.mk π₁) ((CG.isUnitary_mk π₁).2 hu₁) w B₁ hs₁ b hb
  obtain ⟨α, hα⟩ : ∃ α, α ∈ B₁.map (fun b : ℂˣ => (b : ℂ)) := by
    obtain ⟨b, hb⟩ := Multiset.card_pos_iff_exists_mem.1 (by rw [hs₁.card]; omega)
    exact ⟨_, Multiset.mem_map_of_mem _ hb⟩
  have hP : ∀ u ∈ StrStepD.strSet c₁ c₂ d₁ d₂, 1 ≤ u → u - 1 ∈ StrStepD.strSet c₁ c₂ d₁ d₂ :=
    fun u hu hu1 => StrStepA.step_down _ hq _ hbound hα _ hintS _ hM hgap hu hu1

  have hlin : (d₁ : ℝ) * c₁ + d₂ * c₂ = 0 := by
    have hsre := congrArg Complex.re hsum
    simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, h1im, h2im, mul_zero,
      sub_zero, Complex.zero_re] at hsre
    have ha : (0 : ℝ) < a₁ := by exact_mod_cast ha₁
    have : (a₁ : ℝ) * (d₁ * c₁ + d₂ * c₂) = 0 := by
      rw [hc₁d, hc₂d]
      push_cast at hsre ⊢
      linear_combination hsre
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  have hc₁n : c₁ < 0 := by rw [hc₁d]; linarith
  have hc₂p : 0 < c₂ := by
    have : (0 : ℝ) < d₁ := by exact_mod_cast hd₁
    have : (0 : ℝ) < d₂ := by exact_mod_cast hd₂
    nlinarith
  have hadj := StrStepA.adjacent c₁ c₂ d₁ d₂ hd₁ hd₂ (StrStepD.strSet c₁ c₂ d₁ d₂) (fun x => Iff.rfl) hdisj hintS
    hneg hP (by linarith)
  have hc₁v : c₁ = -(d₂ : ℝ) / 2 := by
    have h : ((d₁ : ℝ) + d₂) * (c₁ + d₂ / 2) = 0 := by linear_combination hlin - (d₂ : ℝ) * hadj
    rcases mul_eq_zero.1 h with h | h
    · have : (0 : ℝ) < d₁ := by exact_mod_cast hd₁
      have : (0 : ℝ) ≤ d₂ := Nat.cast_nonneg _
      linarith
    · linarith
  have hc₂v : c₂ = (d₁ : ℝ) / 2 := by linarith
  push_cast at hc₁d hc₂d
  refine ⟨by rw [hmk], ?_, ?_⟩
  · apply Complex.ext
    · simp
      linarith
    · simp [h1im]
  · apply Complex.ext
    · simp
      linarith
    · simp [h2im]

end PositivityTheory.Rg.Rs

end
