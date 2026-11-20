import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleCochainsInjectiveShortExact

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

/- English proof (translation)
Introduce `R _ I hI S hS n`. Establish `hd` using `(HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS`. Establish `hv : ∀ {Y : Cx R} (φ : S.X₁ ⟶ Y) (z : Cochain Y I n) (p q : ℤ) (hpq : p + n = q), ((Cochain.ofHom φ).comp z (zero_add n)).v p q hpq = φ.f p ≫ z.v p q hpq`. Introduce `Y φ z p q hpq`. Rewrite using `[Cochain.zero_cochain_comp_v, Cochain.ofHom_v]`.

Establish `hv2 : ∀ {Y : Cx R} (φ : S.X₂ ⟶ Y) (z : Cochain Y I n) (p q : ℤ) (hpq : p + n = q), ((Cochain.ofHom φ).comp z (zero_add n)).v p q hpq = φ.f p ≫ z.v p q hpq`. Introduce `Y φ z p q hpq`. Rewrite using `[Cochain.zero_cochain_comp_v, Cochain.ofHom_v]`. Establish `hm : ∀ p, Mono (S.f.f p)` using `fun p => (hd p).mono_f`. Establish `he : ∀ p, Epi (S.g.f p)` using `fun p => (hd p).epi_g`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a`. Use `⟨Cochain.mk (fun p q h => haveI := hm p; haveI := hI q Injective.factorThru (a.v p q h) (S.f.f p)), ?_⟩` and prove the remaining obligations. Apply `Cochain.ext` to reduce the goal to its premises. Introduce `p q hpq`.

Rewrite using `[hv, Cochain.mk_v]`. Use `hm p` as an intermediate fact. Use `hI q` as an intermediate fact. Conclude with `Injective.comp_factorThru _ _`. Introduce `b hb`.

Use `⟨Cochain.mk (fun p q h => haveI := (hd p).epi_g (hd p).exact.desc (b.v p q h) (by` and prove the remaining obligations. Use `congrArg (fun z => z.v p q h) hb` as an intermediate fact. Simplify using `only [hv] at this`. Conclude with `this)), ?_⟩`. Apply `Cochain.ext` to reduce the goal to its premises.

Introduce `p q hpq`. Rewrite using `[hv2]`. Use `haveI := (hd p).epi_g`. Conclude with `(hd p).exact.g_desc _ _`. Introduce `c hc`.

Apply `Cochain.ext` to reduce the goal to its premises. Introduce `p q hpq`. Use `congrArg (fun z => z.v p q hpq) hc` as an intermediate fact. Simplify using `only [hv2, Cochain.zero_v] at this`. Establish `hep` using `he p`.

Rewrite using `[Cochain.zero_v]`. Conclude with `(cancel_epi (S.g.f p)).1 (by simpa using this)`.
-/
theorem LateralTheory.EtaleFoundations.etale_simplicial_cochain_short_exact_sequence_holds : LateralTheory.EtaleFoundations.EtaleCochainsInjectiveShortExact := by
  intro R _ I hI S hS n
  have hd := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS
  have hv : ∀ {Y : Cx R} (φ : S.X₁ ⟶ Y) (z : Cochain Y I n) (p q : ℤ) (hpq : p + n = q),
      ((Cochain.ofHom φ).comp z (zero_add n)).v p q hpq = φ.f p ≫ z.v p q hpq := by
    intro Y φ z p q hpq
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  have hv2 : ∀ {Y : Cx R} (φ : S.X₂ ⟶ Y) (z : Cochain Y I n) (p q : ℤ) (hpq : p + n = q),
      ((Cochain.ofHom φ).comp z (zero_add n)).v p q hpq = φ.f p ≫ z.v p q hpq := by
    intro Y φ z p q hpq
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  have hm : ∀ p, Mono (S.f.f p) := fun p => (hd p).mono_f
  have he : ∀ p, Epi (S.g.f p) := fun p => (hd p).epi_g
  refine ⟨?_, ?_, ?_⟩
  · intro a
    refine ⟨Cochain.mk (fun p q h => haveI := hm p; haveI := hI q
      Injective.factorThru (a.v p q h) (S.f.f p)), ?_⟩
    apply Cochain.ext
    intro p q hpq
    rw [hv, Cochain.mk_v]
    have := hm p; have := hI q
    exact Injective.comp_factorThru _ _
  · intro b hb
    refine ⟨Cochain.mk (fun p q h => haveI := (hd p).epi_g
      (hd p).exact.desc (b.v p q h) (by
        have := congrArg (fun z => z.v p q h) hb
        simp only [hv] at this; exact this)), ?_⟩
    apply Cochain.ext
    intro p q hpq
    rw [hv2]
    haveI := (hd p).epi_g
    exact (hd p).exact.g_desc _ _
  · intro c hc
    apply Cochain.ext
    intro p q hpq
    have := congrArg (fun z => z.v p q hpq) hc
    simp only [hv2, Cochain.zero_v] at this
    have hep := he p
    rw [Cochain.zero_v]
    exact (cancel_epi (S.g.f p)).1 (by simpa using this)
