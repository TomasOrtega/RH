import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
import Development.AbelianVarietyTheory.Definitions.Foundations.MultipliableAndSgNeZero

noncomputable section

open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.KZ.SiegelModel

open GlobalTheory.Sieg GlobalTheory.Sieg.Model

/- English proof (translation)
The claim follows from `isOpen_lt continuous_const Complex.continuous_im`.
-/
theorem isOpen_Hs : IsOpen Hs :=
  isOpen_lt continuous_const Complex.continuous_im

/- English proof (translation)
Establish `hI : Complex.I ∈ Hs` using `by simp [Hs]`. Establish `hloc : nhdsWithin Complex.I (Hs \ {Complex.I}) = nhdsWithin Complex.I {Complex.I}ᶜ` using `nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hI))`. Establish `hne : (nhdsWithin Complex.I (Hs \ {Complex.I})).NeBot`. Rewrite using `[hloc]`. Use `infer_instance`.

Use `hne.mono ?_` and prove the remaining obligations. Unfold `Filter.codiscreteWithin`. Conclude with `le_iSup₂ (f := fun x (_ : x ∈ Hs) => nhdsWithin x (Hs \ {x})) Complex.I hI`.
-/
theorem neBot_Hs : (Filter.codiscreteWithin Hs).NeBot := by
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have hloc : nhdsWithin Complex.I (Hs \ {Complex.I}) = nhdsWithin Complex.I {Complex.I}ᶜ :=
    nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hI))
  have hne : (nhdsWithin Complex.I (Hs \ {Complex.I})).NeBot := by
    rw [hloc]
    infer_instance
  refine hne.mono ?_
  unfold Filter.codiscreteWithin
  exact le_iSup₂ (f := fun x (_ : x ∈ Hs) => nhdsWithin x (Hs \ {x})) Complex.I hI

/- English proof (translation)
The claim follows from `Filter.Germ.coe_eq.2 (Filter.mem_of_superset (Filter.self_mem_codiscreteWithin Hs) fun z hz => h z hz)`.
-/
theorem germ_eq_of_eqOn {φ ψ : ℂ → ℂ} (h : ∀ z ∈ Hs, φ z = ψ z) : (φ : Mero) = (ψ : Mero) :=
  Filter.Germ.coe_eq.2 (Filter.mem_of_superset (Filter.self_mem_codiscreteWithin Hs) fun z hz => h z hz)

/- English proof (translation)
Unfold `sgC`. Rewrite using `[UpperHalfPlane.ofComplex_apply]`.
-/
theorem sgC_coe (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : sgC c x τ = sg c x τ := by
  unfold sgC
  rw [UpperHalfPlane.ofComplex_apply]

/- English proof (translation)
Introduce `h0`. Rewrite `h0` using `[← Filter.Germ.coe_zero]`. Establish `hev` using `Filter.Germ.coe_eq.1 h0`. Use `neBot_Hs` as an intermediate fact. Take `⟨z, hz0, hzH⟩` from `(hev.and (Filter.self_mem_codiscreteWithin Hs)).exists`.

Establish `hsg` using `(multipliable_and_sg_ne_zero h ⟨z, hzH⟩).2.2`. Apply `hsg` to reduce the goal to its premises. Establish `e : sgC c x z = sg c x ⟨z, hzH⟩` using `sgC_coe c x ⟨z, hzH⟩`. Rewrite using `[← e]`. Conclude with `hz0`.
-/
theorem germ_sgC_ne_zero {c : ℕ} {x : Fin 2 → ℚ} (h : admitted c x) : ((sgC c x : ℂ → ℂ) : Mero) ≠ 0 := by
  intro h0
  rw [← Filter.Germ.coe_zero] at h0
  have hev := Filter.Germ.coe_eq.1 h0
  have := neBot_Hs
  obtain ⟨z, hz0, hzH⟩ := (hev.and (Filter.self_mem_codiscreteWithin Hs)).exists
  have hsg := (multipliable_and_sg_ne_zero h ⟨z, hzH⟩).2.2
  apply hsg
  have e : sgC c x z = sg c x ⟨z, hzH⟩ := sgC_coe c x ⟨z, hzH⟩
  rw [← e]
  exact hz0

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε)

/- English proof (translation)
Use `neBot_Hs` as an intermediate fact. Conclude with `T.an.injective`.
-/
theorem an_injective : Function.Injective T.an := by
  have := neBot_Hs
  exact T.an.injective

/- English proof (translation)
Establish `hex : ∃ f : T.K, T.an f = ((sgC c x : ℂ → ℂ) : Mero)` using `⟨f, hf⟩`. Unfold `siegel`. Rewrite using `[dif_pos hex]`. Conclude with `an_injective T (hex.choose_spec.trans hf.symm)`.
-/
theorem siegel_eq {c : ℕ} {x : Fin 2 → ℚ} {f : T.K} (hf : T.an f = ((sgC c x : ℂ → ℂ) : Mero)) :
    siegel T c x = f := by
  have hex : ∃ f : T.K, T.an f = ((sgC c x : ℂ → ℂ) : Mero) := ⟨f, hf⟩
  unfold siegel
  rw [dif_pos hex]
  exact an_injective T (hex.choose_spec.trans hf.symm)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hne`. Distinguish the cases in `hex : ∃ f : T.K, T.an f = ((sgC c x : ℂ → ℂ) : Mero)`. Take `⟨f, hf⟩` from `hex`. Rewrite using `[siegel_eq T hf]`.

Conclude with `hf`. Conclude with `absurd (by unfold siegel; exact dif_neg hex) hne`. Introduce `hmem h0`. Rewrite `hmem` using `[h0, map_zero]`. Conclude with `germ_sgC_ne_zero h hmem.symm`.
-/
theorem siegel_ne_zero_iff {c : ℕ} {x : Fin 2 → ℚ} (h : admitted c x) :
    siegel T c x ≠ 0 ↔ T.an (siegel T c x) = ((sgC c x : ℂ → ℂ) : Mero) := by
  constructor
  · intro hne
    by_cases hex : ∃ f : T.K, T.an f = ((sgC c x : ℂ → ℂ) : Mero)
    · obtain ⟨f, hf⟩ := hex
      rw [siegel_eq T hf]
      exact hf
    · exact absurd (by unfold siegel; exact dif_neg hex) hne
  · intro hmem h0
    rw [h0, map_zero] at hmem
    exact germ_sgC_ne_zero h hmem.symm

/- English proof (translation)
Establish `ht : ee (pt x τ) ≠ 1`. Introduce `h1`. Take `⟨h0, n, hn⟩` from `ee_eq_one (a := x 0) (b := x 1) τ h1`. Conclude with `hx ⟨⟨0, by rw [h0]; simp⟩, ⟨n, hn⟩⟩`. Establish `hne : (1 : ℂ) - ee (pt x τ) ≠ 0` using `sub_ne_zero.2 (Ne.symm ht)`.

Establish `hfac : ∀ m : ℕ, cthFac 1 (ee τ) (ee (pt x τ)) (m + 1) = 1`. Introduce `m`. Take `⟨h1, h2⟩` from `ne_one_of_not_int hx τ (m + 1)`. Simplify using `only [cthFac, one_pow, pow_one]`. Conclude with `div_self (mul_ne_zero h1 h2)`.

Simplify using `[sg, cth, hfac, hne]`.
-/
theorem sg_one {x : Fin 2 → ℚ}
    (hx : ¬ (x 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ x 1 ∈ Set.range ((↑) : ℤ → ℚ))) (τ : ℍ) : sg 1 x τ = 1 := by
  have ht : ee (pt x τ) ≠ 1 := by
    intro h1
    obtain ⟨h0, n, hn⟩ := ee_eq_one (a := x 0) (b := x 1) τ h1
    exact hx ⟨⟨0, by rw [h0]; simp⟩, ⟨n, hn⟩⟩
  have hne : (1 : ℂ) - ee (pt x τ) ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
  have hfac : ∀ m : ℕ, cthFac 1 (ee τ) (ee (pt x τ)) (m + 1) = 1 := by
    intro m
    obtain ⟨h1, h2⟩ := ne_one_of_not_int hx τ (m + 1)
    simp only [cthFac, one_pow, pow_one]
    exact div_self (mul_ne_zero h1 h2)
  simp [sg, cth, hfac, hne]

/- English proof (translation)
Use `siegel_eq T ?_` and prove the remaining obligations. Rewrite using `[map_one, ← Filter.Germ.coe_one]`. Use `germ_eq_of_eqOn fun z hz => ?_` and prove the remaining obligations. Establish `e : sgC 1 x z = sg 1 x ⟨z, hz⟩` using `sgC_coe 1 x ⟨z, hz⟩`. Rewrite using `[Pi.one_apply, e, sg_one hx]`.
-/
theorem siegel_one {x : Fin 2 → ℚ}
    (hx : ¬ (x 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ x 1 ∈ Set.range ((↑) : ℤ → ℚ))) : siegel T 1 x = 1 := by
  refine siegel_eq T ?_
  rw [map_one, ← Filter.Germ.coe_one]
  refine germ_eq_of_eqOn fun z hz => ?_
  have e : sgC 1 x z = sg 1 x ⟨z, hz⟩ := sgC_coe 1 x ⟨z, hz⟩
  rw [Pi.one_apply, e, sg_one hx]

/- English proof (translation)
Rewrite using `[UpperHalfPlane.coe_specialLinearGroup_apply]`. Simplify using `[mob, ent, ofSL]`.
-/
theorem mob_ofSL (γ : SL(2, ℤ)) (τ : ℍ) : mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [mob, ent, ofSL]

/- English proof (translation)
Use `(siegel_eq T ?_).symm` and prove the remaining obligations. Rewrite using `[T.an_sl _ _ _ hmem]`. Use `germ_eq_of_eqOn fun z hz => ?_` and prove the remaining obligations. Establish `e1 : mob (ofSL γ) z = ((γ • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ)` using `mob_ofSL γ ⟨z, hz⟩`. Establish `e2 : sgC c (act x γ) z = sg c (act x γ) ⟨z, hz⟩` using `sgC_coe c (act x γ) ⟨z, hz⟩`.

Use `show sgC c x (mob (ofSL γ) z) = sgC c (act x γ) z`. Rewrite using `[e1, sgC_coe, hγ, e2]`.
-/
theorem sl_siegel {c : ℕ} {x : Fin 2 → ℚ} (γ : SL(2, ℤ))
    (hmem : T.an (siegel T c x) = ((sgC c x : ℂ → ℂ) : Mero))
    (hγ : ∀ τ : ℍ, sg c x (γ • τ) = sg c (act x γ) τ) :
    T.sl (ofSL γ) (siegel T c x) = siegel T c (act x γ) := by
  refine (siegel_eq T ?_).symm
  rw [T.an_sl _ _ _ hmem]
  refine germ_eq_of_eqOn fun z hz => ?_
  have e1 : mob (ofSL γ) z = ((γ • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) := mob_ofSL γ ⟨z, hz⟩
  have e2 : sgC c (act x γ) z = sg c (act x γ) ⟨z, hz⟩ := sgC_coe c (act x γ) ⟨z, hz⟩
  show sgC c x (mob (ofSL γ) z) = sgC c (act x γ) z
  rw [e1, sgC_coe, hγ, e2]

/- English proof (translation)
Establish `hγz : ∀ (γ : SL(2, ℤ)) (z : ℂ) (hz : z ∈ Hs), sgC c x (mob (ofSL γ) z) = sg c (act x γ) ⟨z, hz⟩`. Introduce `γ z hz`. Rewrite using `[mob_ofSL γ ⟨z, hz⟩, sgC_coe, hmod]`. Establish `hlev' : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs, sgC c x (mob (ofSL γ) z) = sgC c x z`. Introduce `γ hγ z hz`.

Rewrite using `[hγz γ z hz, hlev γ hγ, ← sgC_coe]`. Establish `hexp' : ∀ γ : SL(2, ℤ), ∃ (a : ℤ → Ω) (n0 : ℤ), (∀ n < n0, a n = 0) ∧ ∀ z ∈ Hs, HasSum (fun n : ℤ => ε (a n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z / M)) (sgC c x (mob (ofSL γ) z))`. Introduce `γ`. Take `⟨a, n0, ha, hs⟩` from `hexp γ`. Use `⟨a, n0, ha, fun z hz => ?_⟩` and prove the remaining obligations.

Rewrite using `[hγz γ z hz]`. Conclude with `hs ⟨z, hz⟩`. Take `⟨f, hf⟩` from `T.mem_q (sgC c x) M hM hd hlev' hexp'`. Rewrite using `[siegel_eq T hf]`. Conclude with `hf`.
-/
theorem an_siegel {c : ℕ} {x : Fin 2 → ℚ} (M : ℕ) (hM : 0 < M) (hd : DifferentiableOn ℂ (sgC c x) Hs)
    (hmod : ∀ (γ : SL(2, ℤ)) (τ : ℍ), sg c x (γ • τ) = sg c (act x γ) τ)
    (hlev : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, sg c (act x γ) τ = sg c x τ)
    (hexp : ∀ γ : SL(2, ℤ), ∃ (a : ℤ → Ω) (n0 : ℤ), (∀ n < n0, a n = 0) ∧ ∀ τ : ℍ,
      HasSum (fun n : ℤ => ε (a n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) (sg c (act x γ) τ)) :
    T.an (siegel T c x) = ((sgC c x : ℂ → ℂ) : Mero) := by

  have hγz : ∀ (γ : SL(2, ℤ)) (z : ℂ) (hz : z ∈ Hs), sgC c x (mob (ofSL γ) z) = sg c (act x γ) ⟨z, hz⟩ := by
    intro γ z hz
    rw [mob_ofSL γ ⟨z, hz⟩, sgC_coe, hmod]
  have hlev' : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs, sgC c x (mob (ofSL γ) z) = sgC c x z := by
    intro γ hγ z hz
    rw [hγz γ z hz, hlev γ hγ, ← sgC_coe]
  have hexp' : ∀ γ : SL(2, ℤ), ∃ (a : ℤ → Ω) (n0 : ℤ), (∀ n < n0, a n = 0) ∧ ∀ z ∈ Hs,
      HasSum (fun n : ℤ => ε (a n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z / M))
        (sgC c x (mob (ofSL γ) z)) := by
    intro γ
    obtain ⟨a, n0, ha, hs⟩ := hexp γ
    refine ⟨a, n0, ha, fun z hz => ?_⟩
    rw [hγz γ z hz]
    exact hs ⟨z, hz⟩
  obtain ⟨f, hf⟩ := T.mem_q (sgC c x) M hM hd hlev' hexp'
  rw [siegel_eq T hf]
  exact hf

/- English proof (translation)
Use `siegel_eq T (f := 0) ?_` and prove the remaining obligations. Rewrite using `[map_zero, ← Filter.Germ.coe_zero]`. Use `germ_eq_of_eqOn fun z _ => ?_` and prove the remaining obligations. Simplify using `[sgC, sg, cth, pt, ee]`.
-/
theorem siegel_zero_index {c : ℕ} : siegel T c 0 = 0 := by
  refine siegel_eq T (f := 0) ?_
  rw [map_zero, ← Filter.Germ.coe_zero]
  refine germ_eq_of_eqOn fun z _ => ?_
  simp [sgC, sg, cth, pt, ee]

end GlobalTheory.KZ.SiegelModel
