import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteLocalHeightTerm

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

/- English proof (translation)
Use `first`. Consider the case `exact finsum_sum_comm s (fun a b => f b a) hf`. Consider the case `(classical`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`.

Consider the case `insert b s hb ih`. Simplify using `only [Finset.sum_insert hb]`. Rewrite using `[finsum_add_distrib (hf b (Finset.mem_insert_self b s)) ((s.finite_toSet.biUnion fun b' hb' => hf b' (Finset.mem_insert_of_mem hb')).subset (Function.support_finset_sum)), ih fun b' hb' => hf b' (Finset.mem_insert_of_mem hb')])`.
-/
theorem finsum_finset_sum_comm' {α β : Type*} (s : Finset β) (f : β → α → ℝ)
    (hf : ∀ b ∈ s, (Function.support (f b)).Finite) :
    ∑ᶠ a, ∑ b ∈ s, f b a = ∑ b ∈ s, ∑ᶠ a, f b a := by
  first
    | exact finsum_sum_comm s (fun a b => f b a) hf
    | (classical
       induction s using Finset.induction_on with
       | empty => simp
       | insert b s hb ih =>
         simp only [Finset.sum_insert hb]
         rw [finsum_add_distrib (hf b (Finset.mem_insert_self b s))
           ((s.finite_toSet.biUnion fun b' hb' => hf b' (Finset.mem_insert_of_mem hb')).subset
             (Function.support_finset_sum)), ih fun b' hb' => hf b' (Finset.mem_insert_of_mem hb')])

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

/- English proof (translation)
Take `⟨hFne, hFx⟩` from `d.fZ_and_substituted_ne_zero hd h x hx c F hF`. Take `⟨κ, hκ, hs⟩` from `d.substituted_factorization_exists hd h x hx c F hF`. Establish `hfin` using `d.finite_local_height_term hd h x hx c F κ hκ hF hFne hFx hs`. Establish `harch` using `d.archimedean_local_height_term hd h x hx c F κ hκ hF hFne hs`. Rewrite using `[(d.height_substituted_eq_finsum hd h x hx c F hF).2]`.

Use `set G : FinitePlace K → ℝ := fun v => Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v F) - Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v (d.translatedForm x F)) + Real.log (v κ) with hG`. Establish `hg : (fun la => d.localHeightAtPrime h (d.wx x) c la * logNorm la) = fun la => G (FinitePlace.equivHeightOneSpectrum.symm la)`. Use function extensionality and compare the values at `la`. Rewrite using `[hfin la]`. Both sides reduce to the same expression.

Establish `s1` using `ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite F hFne`. Establish `s2` using `ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite _ hFx`. Establish `s3 : (Function.support fun v : FinitePlace K => Real.log (v κ)).Finite`. Use `(FinitePlace.hasFiniteMulSupport hκ).subset fun v hv => ?_` and prove the remaining obligations. Introduce `h1`.

Apply `hv` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[show v κ = 1 from h1, Real.log_one]`. Establish `sG : (Function.support G).Finite` using `((s1.union s2).union s3).subset (by`. Introduce `v hv`.

Assume the negation of the conclusion as `hn`. Apply `hv` to reduce the goal to its premises. Simplify using `only [Set.mem_union, Function.mem_support, not_or, not_not] at hn`. Simplify using `only [hG, hn.1.1, hn.1.2, hn.2]`. Use the proof step `ring)`.

Establish `hsumG : ∑ᶠ la, d.localHeightAtPrime h (d.wx x) c la * logNorm la = ∑ᶠ v, G v`. Rewrite using `[hg]`. Conclude with `finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hg]`.

Conclude with `(sG.image FinitePlace.equivHeightOneSpectrum).subset (by`. Introduce `la hla; exact ⟨FinitePlace.equivHeightOneSpectrum.symm la, hla, by simp⟩)`. Rewrite using `[hsumG, hG, finsum_add_distrib ((s1.union s2).subset (Function.support_sub _ _)) s3, finsum_sub_distrib s1 s2]`. Establish `hpf : (∑ᶠ v : FinitePlace K, Real.log (v κ)) + ∑ σ : K →+* ℂ, Real.log ‖σ κ‖ = 0` using `by classical`. Establish `hm` using `FinitePlace.hasFiniteMulSupport hκ`.

Use `set U := hm.toFinset`. Establish `hsub1 : Function.mulSupport (fun v : FinitePlace K => v κ) ⊆ U`. Introduce `v hv`. Conclude with `hm.mem_toFinset.mpr hv`. Establish `hsub2 : Function.support (fun v : FinitePlace K => Real.log (v κ)) ⊆ U`.

Introduce `v hv`. Apply `hsub1` to reduce the goal to its premises. Introduce `h1`. Apply `hv` to reduce the goal to its premises. Simplify using `only`.

Rewrite using `[show v κ = 1 from h1, Real.log_one]`. Establish `hprod` using `FinitePlace.prod_eq_inv_abs_norm hκ`. Rewrite `hprod` using `[finprod_eq_prod_of_mulSupport_subset _ hsub1]`. Rewrite using `[finsum_eq_sum_of_support_subset _ hsub2, ReciprocityTheory.MultiplicativeHeights.sum_log_norm_embedding_eq κ hκ, ← Real.log_prod fun v _ => (FinitePlace.pos_iff.mpr hκ).ne', hprod]`. Use `push_cast`.

Rewrite using `[Real.log_inv]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcard : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K`. Rewrite using `[NumberField.Embeddings.card]`. Establish `hn : (0 : ℝ) < Module.finrank ℚ K` using `by exact_mod_cast Module.finrank_pos`.

Unfold `meanK ReciprocityTheory.MultiplicativeHeights.h0`. Repeatedly rewrite using `[harch]`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]`. Clear the denominators using the available nonvanishing facts. Combine the linear relations using `[hpf]`.
-/
theorem height_decomposition_local_terms (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    (Function.support fun la => d.localHeightAtPrime h (d.wx x) c la * logNorm la).Finite ∧
    (∑ᶠ la, d.localHeightAtPrime h (d.wx x) c la * logNorm la) / (Module.finrank ℚ K : ℝ) +
      meanK (d.localHeightAtEmbedding (d.wx x) c) +
      ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (d.nPMM h c (d.wx x c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p) =
      ReciprocityTheory.MultiplicativeHeights.h0 F + d.delc c * (harmonic d.N : ℝ) / 2 := by
  obtain ⟨hFne, hFx⟩ := d.fZ_and_substituted_ne_zero hd h x hx c F hF
  obtain ⟨κ, hκ, hs⟩ := d.substituted_factorization_exists hd h x hx c F hF
  have hfin := d.finite_local_height_term hd h x hx c F κ hκ hF hFne hFx hs
  have harch := d.archimedean_local_height_term hd h x hx c F κ hκ hF hFne hs
  rw [(d.height_substituted_eq_finsum hd h x hx c F hF).2]
  set G : FinitePlace K → ℝ := fun v => Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v F) -
    Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v (d.translatedForm x F)) + Real.log (v κ) with hG
  have hg : (fun la => d.localHeightAtPrime h (d.wx x) c la * logNorm la) =
      fun la => G (FinitePlace.equivHeightOneSpectrum.symm la) := by
    funext la; rw [hfin la]; rfl
  have s1 := ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite F hFne
  have s2 := ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite _ hFx
  have s3 : (Function.support fun v : FinitePlace K => Real.log (v κ)).Finite := by
    refine (FinitePlace.hasFiniteMulSupport hκ).subset fun v hv => ?_
    intro h1; apply hv; simp only; rw [show v κ = 1 from h1, Real.log_one]
  have sG : (Function.support G).Finite := ((s1.union s2).union s3).subset (by
    intro v hv; by_contra hn; apply hv
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
    simp only [hG, hn.1.1, hn.1.2, hn.2]; ring)
  have hsumG : ∑ᶠ la, d.localHeightAtPrime h (d.wx x) c la * logNorm la = ∑ᶠ v, G v := by
    rw [hg]; exact finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm
  refine ⟨?_, ?_⟩
  · rw [hg]
    exact (sG.image FinitePlace.equivHeightOneSpectrum).subset (by
      intro la hla; exact ⟨FinitePlace.equivHeightOneSpectrum.symm la, hla, by simp⟩)
  rw [hsumG, hG, finsum_add_distrib ((s1.union s2).subset (Function.support_sub _ _)) s3,
    finsum_sub_distrib s1 s2]
  have hpf : (∑ᶠ v : FinitePlace K, Real.log (v κ)) + ∑ σ : K →+* ℂ, Real.log ‖σ κ‖ = 0 := by
    classical
    have hm := FinitePlace.hasFiniteMulSupport hκ
    set U := hm.toFinset
    have hsub1 : Function.mulSupport (fun v : FinitePlace K => v κ) ⊆ U := by
      intro v hv; exact hm.mem_toFinset.mpr hv
    have hsub2 : Function.support (fun v : FinitePlace K => Real.log (v κ)) ⊆ U := by
      intro v hv; apply hsub1; intro h1; apply hv; simp only; rw [show v κ = 1 from h1, Real.log_one]
    have hprod := FinitePlace.prod_eq_inv_abs_norm hκ
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub1] at hprod
    rw [finsum_eq_sum_of_support_subset _ hsub2, ReciprocityTheory.MultiplicativeHeights.sum_log_norm_embedding_eq κ hκ,
      ← Real.log_prod fun v _ => (FinitePlace.pos_iff.mpr hκ).ne', hprod]
    push_cast
    rw [Real.log_inv]; ring
  have hcard : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K := by
    rw [NumberField.Embeddings.card]
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  unfold meanK ReciprocityTheory.MultiplicativeHeights.h0
  simp_rw [harch]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, hcard]
  field_simp
  linarith [hpf]

/- English proof (translation)
Establish `hc` using `fun c => d.height_decomposition_local_terms hd h hI2be x hx c (F c) (hF c)`. Establish `hla : ∀ la, d.NlaMM h (d.wx x) la * logNorm la = ∑ c, d.localHeightAtPrime h (d.wx x) c la * logNorm la`. Introduce `la`. Simplify using `only [NlaMM, localHeightAtPrime, Finset.sum_mul]`. Establish `hsg : d.NsgMM (d.wx x) = fun sg => ∑ c, d.localHeightAtEmbedding (d.wx x) c sg`.

Use function extensionality and compare the values at `sg`. Both sides reduce to the same expression. Establish `hmean : meanK (fun sg => ∑ c, d.localHeightAtEmbedding (d.wx x) c sg) = ∑ c, meanK (d.localHeightAtEmbedding (d.wx x) c)`. Simplify using `only [meanK, Finset.sum_div]`. Rewrite using `[Finset.sum_comm]`.

Unfold `HgtMM mahlerMeasureHeight`. Simplify using `only [hla]`. Rewrite using `[finsum_finset_sum_comm' Finset.univ (fun c la => d.localHeightAtPrime h (d.wx x) c la * logNorm la) (fun c _ => (hc c).1)]`. Rewrite using `[hsg, hmean, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun c _ => (hc c).2, Finset.sum_add_distrib]`. Simplify using `only [del, Nat.cast_sum, Finset.sum_mul, Finset.sum_div]`.
-/
theorem height_minMax_eq_sum_heights (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (F : ι → KTp K d.D d.N)
    (hF : ∀ c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F c) = d.fZ h c) :
    d.HgtMM h (d.wx x) = ∑ c, ReciprocityTheory.MultiplicativeHeights.h0 (F c) + d.del * (harmonic d.N : ℝ) / 2 := by
  have hc := fun c => d.height_decomposition_local_terms hd h hI2be x hx c (F c) (hF c)
  have hla : ∀ la, d.NlaMM h (d.wx x) la * logNorm la = ∑ c, d.localHeightAtPrime h (d.wx x) c la * logNorm la := by
    intro la
    simp only [NlaMM, localHeightAtPrime, Finset.sum_mul]
  have hsg : d.NsgMM (d.wx x) = fun sg => ∑ c, d.localHeightAtEmbedding (d.wx x) c sg := by
    funext sg
    rfl
  have hmean : meanK (fun sg => ∑ c, d.localHeightAtEmbedding (d.wx x) c sg) = ∑ c, meanK (d.localHeightAtEmbedding (d.wx x) c) := by
    simp only [meanK, Finset.sum_div]
    rw [Finset.sum_comm]
  unfold HgtMM mahlerMeasureHeight
  simp only [hla]
  rw [finsum_finset_sum_comm' Finset.univ (fun c la => d.localHeightAtPrime h (d.wx x) c la * logNorm la) (fun c _ => (hc c).1)]
  rw [hsg, hmean, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl fun c _ => (hc c).2, Finset.sum_add_distrib]
  simp only [del, Nat.cast_sum, Finset.sum_mul, Finset.sum_div]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
