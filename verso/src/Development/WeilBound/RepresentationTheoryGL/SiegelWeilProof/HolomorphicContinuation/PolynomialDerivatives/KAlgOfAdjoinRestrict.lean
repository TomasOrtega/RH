import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.MonomialMemSupported

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.Core

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

/- English proof (translation)
Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨ij, rfl⟩` from `hx`. Conclude with `⟨KopL ε ij.1 ij.2, Algebra.subset_adjoin ⟨ij, rfl⟩, fun v => rfl⟩`. Consider the case `algebraMap r`.

Conclude with `⟨algebraMap ℂ _ r, Subalgebra.algebraMap_mem _ r, fun v => by simp [Algebra.algebraMap_eq_smul_one]⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨w₁, h₁, e₁⟩` from `hx`. Take `⟨w₂, h₂, e₂⟩` from `hy`. Conclude with `⟨w₁ + w₂, Subalgebra.add_mem _ h₁ h₂, fun v => by simp [e₁, e₂]⟩`.

Consider the case `mul x y _ _ hx hy`. Take `⟨w₁, h₁, e₁⟩` from `hx`. Take `⟨w₂, h₂, e₂⟩` from `hy`. Use `⟨w₁ * w₂, Subalgebra.mul_mem _ h₁ h₂, fun v => ?_⟩` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply]`.

Rewrite using `[e₂, ← e₁ (y v)]`.
-/
theorem kAlg_of_adjoin_restrict (ε : Fin m → Bool) (V : Submodule ℂ (PX m n))
    (hK : ∀ ij : Fin n × Fin n, ∀ f ∈ V, KopL ε ij.1 ij.2 f ∈ V) (y : Module.End ℂ V)
    (hy : y ∈ Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (KopL ε ij.1 ij.2).restrict (hK ij))) :
    ∃ w ∈ kAlg ε, ∀ v : V, w v = (y v : PX m n) := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨ij, rfl⟩ := hx
    exact ⟨KopL ε ij.1 ij.2, Algebra.subset_adjoin ⟨ij, rfl⟩, fun v => rfl⟩
  | algebraMap r =>
    exact ⟨algebraMap ℂ _ r, Subalgebra.algebraMap_mem _ r, fun v => by simp [Algebra.algebraMap_eq_smul_one]⟩
  | add x y _ _ hx hy =>
    obtain ⟨w₁, h₁, e₁⟩ := hx
    obtain ⟨w₂, h₂, e₂⟩ := hy
    exact ⟨w₁ + w₂, Subalgebra.add_mem _ h₁ h₂, fun v => by simp [e₁, e₂]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨w₁, h₁, e₁⟩ := hx
    obtain ⟨w₂, h₂, e₂⟩ := hy
    refine ⟨w₁ * w₂, Subalgebra.mul_mem _ h₁ h₂, fun v => ?_⟩
    simp only [Module.End.mul_apply]
    rw [e₂, ← e₁ (y v)]

/- English proof (translation)
Introduce `m n ε c hc Λ hΛ p`. Take `⟨B, hBbox, hBrep, hBcomm⟩` from `hRep m n ε c hc Λ hΛ`. Take `⟨hherm, hpos, hadj, hKbox, -⟩` from `hFF m n ε c hc`. Use `set R : Finset (Fin m → ℕ) := p.support.image (rdeg ε) with hR`. Use `set V := box (n := n) ε (R : Set (Fin m → ℕ)) with hV`.

Use `haveI : FiniteDimensional ℂ V := box_finiteDimensional ε R`. Establish `hKV : ∀ ij : Fin n × Fin n, ∀ f ∈ V, KopL ε ij.1 ij.2 f ∈ V` using `fun ij f hf => hKbox ij.1 ij.2 _ f hf`. Establish `hBV : ∀ f ∈ V, B f ∈ V` using `fun f hf => hBbox _ f hf`. Establish `hBF : ∀ f ∈ F1 ε, B f ∈ F1 ε` using `fun f hf => by`. Use `hBbox Set.univ f (first_family_le_box ε hf)` as an intermediate fact.

Conclude with `box_le_first_family ε _ this`. Set `T : Fin n × Fin n → Module.End ℂ V` to `fun ij => (KopL ε ij.1 ij.2).restrict (hKV ij)`. Set `x : Module.End ℂ V` to `B.restrict hBV`. Establish `key : x ∈ Algebra.adjoin ℂ (Set.range T)`. Use `hBi V (fun v w => fform c (v : PX m n) w) (fun v w₁ w₂ => by simp [fform_add_right]) (fun v w r => by simp [fform_smul_right]) (fun v w => hherm _ _) (fun v hv => hpos _ (by simpa using hv)) (Fin n × Fin n) T (fun ij => ⟨(ij.2, ij.1), fun v w => hadj ij.1 ij.2 v w⟩) x ?_` and prove the remaining obligations.

Introduce `t ht`. Take `⟨q, hq⟩` from `V.exists_isCompl`. Set `t' : Module.End ℂ (PX m n)` to `V.subtype ∘ₗ t ∘ₗ V.linearProjOfIsCompl q hq`. Establish `ht' : ∀ f (hf : f ∈ V), t' f = (t ⟨f, hf⟩ : PX m n)` using `fun f hf => by`. Establish `e0` using `Submodule.linearProjOfIsCompl_apply_left hq ⟨f, hf⟩`.

Simplify using `only [t', LinearMap.comp_apply, Submodule.coe_subtype]`. Conclude with `congrArg (fun v => ((t v : V) : PX m n)) e0`. Establish `h1 : ∀ f ∈ box ε (R : Set (Fin m → ℕ)), t' f ∈ box ε (R : Set (Fin m → ℕ))` using `fun f hf => by`. Rewrite using `[ht' f hf]`. Conclude with `(t ⟨f, hf⟩).2`.

Establish `h2 : ∀ i j, ∀ f ∈ box ε (R : Set (Fin m → ℕ)), t' (KopL ε i j f) = KopL ε i j (t' f)`. Introduce `i j f hf`. Establish `e` using `congrArg Subtype.val (LinearMap.congr_fun (ht (i, j)) ⟨f, hf⟩)`. Simplify using `only [Module.End.mul_apply, LinearMap.restrict_apply, LinearMap.restrict_coe_apply, T] at e`. Rewrite using `[ht' _ (hKV (i, j) f hf), ht' f hf]`.

Conclude with `e`. Take `⟨w, hw, hwt⟩` from `hEL m n ε c hc R t' h1 h2`. Take `⟨-, hBw⟩` from `adjoin_first_operators_preserves_family ε c B hBF hBcomm w hw`. Use `LinearMap.ext fun v => Subtype.ext ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, x, LinearMap.restrict_coe_apply]`.

Establish `hv1 : (t v : PX m n) = w v` using `by rw [← hwt v v.2, ht' v v.2]`. Establish `hv2 : (t (B.restrict hBV v) : PX m n) = w (B v)`. Rewrite using `[← hwt (B v) (hBV v v.2), ht' (B v) (hBV v v.2)]`. Both sides reduce to the same expression. Rewrite using `[hv1, hv2, hBw v (box_le_first_family ε _ v.2)]`.

Take `⟨w, hw, hwB⟩` from `kAlg_of_adjoin_restrict ε V hKV x key`. Use `⟨w, hw, ?_⟩` and prove the remaining obligations. Establish `hterm : ∀ s ∈ p.support, Λ (monomial s (p.coeff s)) = contr c (w (monomial s (p.coeff s)))`. Introduce `s hs`. Take `⟨e, h1, h2⟩` from `monomial_split ε s (p.coeff s)`.

Establish `hsub : ({rdeg ε s} : Set (Fin m → ℕ)) ⊆ (R : Set (Fin m → ℕ))`. Introduce `r hr`. Rewrite `hr` using `[Set.mem_singleton_iff]`. Rewrite using `[hr, hR, Finset.coe_image]`. Conclude with `Set.mem_image_of_mem _ hs`.

Establish `h1V : (monomial (s.filter (inF1 ε)) 1 : PX m n) ∈ V` using `box_mono ε hsub h1`. Rewrite using `[e, hBrep _ (box_le_first_family ε _ h1) _ h2, compact_algebra_mul_second_family ε w hw _ _ h2]`. Use `congr 2`. Conclude with `(hwB ⟨_, h1V⟩).symm`. Establish `eL : Λ p = ∑ s ∈ p.support, Λ (monomial s (p.coeff s))`.

Rewrite using `[← map_sum]`. Use `congr 1`. Conclude with `p.as_sum`. Establish `eR : contr c (w p) = ∑ s ∈ p.support, contr c (w (monomial s (p.coeff s)))` using `by show contrL c (w p) = ∑ s ∈ p.support, contrL c (w (monomial s (p.coeff s)))`. Rewrite using `[← map_sum (contrL c), ← map_sum w]`.

Use `congr 2`. Conclude with `p.as_sum`. Rewrite using `[eL, eR]`. Conclude with `Finset.sum_congr rfl hterm`.
-/
theorem coreLC_of' (hBi : Bicomm) (hEL : EquivLift) (hRep : RepB) (hFF : FormFacts) : CoreLC := by
  intro m n ε c hc Λ hΛ p
  classical
  obtain ⟨B, hBbox, hBrep, hBcomm⟩ := hRep m n ε c hc Λ hΛ
  obtain ⟨hherm, hpos, hadj, hKbox, -⟩ := hFF m n ε c hc
  set R : Finset (Fin m → ℕ) := p.support.image (rdeg ε) with hR
  set V := box (n := n) ε (R : Set (Fin m → ℕ)) with hV
  haveI : FiniteDimensional ℂ V := box_finiteDimensional ε R
  have hKV : ∀ ij : Fin n × Fin n, ∀ f ∈ V, KopL ε ij.1 ij.2 f ∈ V := fun ij f hf => hKbox ij.1 ij.2 _ f hf
  have hBV : ∀ f ∈ V, B f ∈ V := fun f hf => hBbox _ f hf
  have hBF : ∀ f ∈ F1 ε, B f ∈ F1 ε := fun f hf => by
    have := hBbox Set.univ f (first_family_le_box ε hf)
    exact box_le_first_family ε _ this
  let T : Fin n × Fin n → Module.End ℂ V := fun ij => (KopL ε ij.1 ij.2).restrict (hKV ij)
  let x : Module.End ℂ V := B.restrict hBV
  have key : x ∈ Algebra.adjoin ℂ (Set.range T) := by
    refine hBi V (fun v w => fform c (v : PX m n) w) (fun v w₁ w₂ => by simp [fform_add_right])
      (fun v w r => by simp [fform_smul_right]) (fun v w => hherm _ _)
      (fun v hv => hpos _ (by simpa using hv)) (Fin n × Fin n) T
      (fun ij => ⟨(ij.2, ij.1), fun v w => hadj ij.1 ij.2 v w⟩) x ?_
    intro t ht
    obtain ⟨q, hq⟩ := V.exists_isCompl
    let t' : Module.End ℂ (PX m n) := V.subtype ∘ₗ t ∘ₗ V.linearProjOfIsCompl q hq
    have ht' : ∀ f (hf : f ∈ V), t' f = (t ⟨f, hf⟩ : PX m n) := fun f hf => by
      have e0 := Submodule.linearProjOfIsCompl_apply_left hq ⟨f, hf⟩
      simp only [t', LinearMap.comp_apply, Submodule.coe_subtype]
      exact congrArg (fun v => ((t v : V) : PX m n)) e0
    have h1 : ∀ f ∈ box ε (R : Set (Fin m → ℕ)), t' f ∈ box ε (R : Set (Fin m → ℕ)) := fun f hf => by
      rw [ht' f hf]; exact (t ⟨f, hf⟩).2
    have h2 : ∀ i j, ∀ f ∈ box ε (R : Set (Fin m → ℕ)), t' (KopL ε i j f) = KopL ε i j (t' f) := by
      intro i j f hf
      have e := congrArg Subtype.val (LinearMap.congr_fun (ht (i, j)) ⟨f, hf⟩)
      simp only [Module.End.mul_apply, LinearMap.restrict_apply, LinearMap.restrict_coe_apply, T] at e
      rw [ht' _ (hKV (i, j) f hf), ht' f hf]
      exact e
    obtain ⟨w, hw, hwt⟩ := hEL m n ε c hc R t' h1 h2
    obtain ⟨-, hBw⟩ := adjoin_first_operators_preserves_family ε c B hBF hBcomm w hw
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp only [Module.End.mul_apply, x, LinearMap.restrict_coe_apply]
    have hv1 : (t v : PX m n) = w v := by rw [← hwt v v.2, ht' v v.2]
    have hv2 : (t (B.restrict hBV v) : PX m n) = w (B v) := by
      rw [← hwt (B v) (hBV v v.2), ht' (B v) (hBV v v.2)]; rfl
    rw [hv1, hv2, hBw v (box_le_first_family ε _ v.2)]
  obtain ⟨w, hw, hwB⟩ := kAlg_of_adjoin_restrict ε V hKV x key
  refine ⟨w, hw, ?_⟩
  have hterm : ∀ s ∈ p.support, Λ (monomial s (p.coeff s)) = contr c (w (monomial s (p.coeff s))) := by
    intro s hs
    obtain ⟨e, h1, h2⟩ := monomial_split ε s (p.coeff s)
    have hsub : ({rdeg ε s} : Set (Fin m → ℕ)) ⊆ (R : Set (Fin m → ℕ)) := by
      intro r hr
      rw [Set.mem_singleton_iff] at hr
      rw [hr, hR, Finset.coe_image]
      exact Set.mem_image_of_mem _ hs
    have h1V : (monomial (s.filter (inF1 ε)) 1 : PX m n) ∈ V := box_mono ε hsub h1
    rw [e, hBrep _ (box_le_first_family ε _ h1) _ h2, compact_algebra_mul_second_family ε w hw _ _ h2]
    congr 2
    exact (hwB ⟨_, h1V⟩).symm
  have eL : Λ p = ∑ s ∈ p.support, Λ (monomial s (p.coeff s)) := by
    rw [← map_sum]; congr 1; exact p.as_sum
  have eR : contr c (w p) = ∑ s ∈ p.support, contr c (w (monomial s (p.coeff s))) := by
    show contrL c (w p) = ∑ s ∈ p.support, contrL c (w (monomial s (p.coeff s)))
    rw [← map_sum (contrL c), ← map_sum w]; congr 2; exact p.as_sum
  rw [eL, eR]
  exact Finset.sum_congr rfl hterm

end PositivityTheory.Rg.Sw.LC.Core
