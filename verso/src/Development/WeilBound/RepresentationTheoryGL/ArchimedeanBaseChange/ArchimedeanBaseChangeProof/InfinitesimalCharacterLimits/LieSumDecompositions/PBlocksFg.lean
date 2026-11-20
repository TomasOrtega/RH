import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgE

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))}
  {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}

/- English proof (translation)
The claim follows from `Submodule.span_le.2 (by rintro _ ⟨κ, rfl⟩; exact hV (.cpt κ) φ hφ)`.
-/
theorem orbSpan_le {a : ℕ} {V : Submodule ℂ (Sm E a)} (hV : IsStable V) {φ : Sm E a} (hφ : φ ∈ V) :
    GlobalTheory.CuspRep.LocEx.orbSpan φ ≤ V :=
  Submodule.span_le.2 (by rintro _ ⟨κ, rfl⟩; exact hV (.cpt κ) φ hφ)

/- English proof (translation)
Establish `hx` using `exp_one hexp hβ`. Take `⟨n, b, q, hb, -, he⟩` from `hx`. Establish `h : ∀ i, ∃ Fi : Finset (Sm E r), (↑Fi : Set (Sm E r)) ⊆ BlockDerivatives.lsF r s (T β) 1 1 ∧ b i ∈ Submodule.span ℂ (↑Fi : Set (Sm E r))` using `fun i => Submodule.mem_span_finite_of_mem_span (hb i)`. Use `choose Fi hFi hbFi using h`. Use `⟨Finset.univ.biUnion Fi, ?_, fun m₂ => ?_⟩` and prove the remaining obligations.

Introduce `ℓ hℓ`. Take `⟨i, -, hi⟩` from `Finset.mem_biUnion.1 (Finset.mem_coe.1 hℓ)`. Conclude with `BlockDerivatives.lsF_sub_LS hβ 1 1 (hFi i hi)`. Rewrite using `[left_slice_eq_sum (T β) b q he m₂]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Conclude with `Submodule.span_mono (fun x hx => Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hx⟩)) (hbFi i)`.
-/
theorem stepA_left (hexp : HExp U T) {β : Sm E (r + s)} (hβ : β ∈ U) :
    ∃ F : Finset (Sm E r), (↑F : Set (Sm E r)) ⊆ BlockDerivatives.LS U T ∧
      ∀ m₂, sl0 m₂ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E r)) := by
  classical
  have hx := exp_one hexp hβ
  obtain ⟨n, b, q, hb, -, he⟩ := hx
  have h : ∀ i, ∃ Fi : Finset (Sm E r), (↑Fi : Set (Sm E r)) ⊆ BlockDerivatives.lsF r s (T β) 1 1 ∧
      b i ∈ Submodule.span ℂ (↑Fi : Set (Sm E r)) := fun i => Submodule.mem_span_finite_of_mem_span (hb i)
  choose Fi hFi hbFi using h
  refine ⟨Finset.univ.biUnion Fi, ?_, fun m₂ => ?_⟩
  · intro ℓ hℓ
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hℓ)
    exact BlockDerivatives.lsF_sub_LS hβ 1 1 (hFi i hi)
  · rw [left_slice_eq_sum (T β) b q he m₂]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    exact Submodule.span_mono (fun x hx => Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hx⟩))
      (hbFi i)

/- English proof (translation)
Establish `hx` using `exp_one hexp hβ`. Take `⟨n, b, q, -, hq, he⟩` from `hx`. Use `⟨Finset.univ.image q, ?_, fun m₁ => ?_⟩` and prove the remaining obligations. Introduce `ℓ hℓ`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hℓ)`.

Conclude with `BlockDerivatives.rsF_sub_RS hβ 1 1 (hq i)`. Rewrite using `[right_slice_eq_sum (T β) b q he m₁]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem q (Finset.mem_univ i))))`.
-/
theorem stepA_right (hexp : HExp U T) {β : Sm E (r + s)} (hβ : β ∈ U) :
    ∃ F : Finset (Sm E s), (↑F : Set (Sm E s)) ⊆ BlockDerivatives.RS U T ∧
      ∀ m₁, sl1 m₁ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E s)) := by
  classical
  have hx := exp_one hexp hβ
  obtain ⟨n, b, q, -, hq, he⟩ := hx
  refine ⟨Finset.univ.image q, ?_, fun m₁ => ?_⟩
  · intro ℓ hℓ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hℓ)
    exact BlockDerivatives.rsF_sub_RS hβ 1 1 (hq i)
  · rw [right_slice_eq_sum (T β) b q he m₁]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem q (Finset.mem_univ i))))

/- English proof (translation)
Establish `hfd : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan φ)` using `(hU.2 φ hφ).kfin`. Establish `hfg'` using `(Submodule.fg_iff_finiteDimensional _).2 hfd`. Take `⟨B, hB⟩` from `hfg'`. Establish `hBU : ∀ β ∈ B, β ∈ U` using `fun β hβ => orbSpan_le hU.1 hφ (hB ▸ Submodule.subset_span (Finset.mem_coe.2 hβ))`. Establish `hc` using `collect (α := Sm E (r + s)) (β := Sm E r) B (BlockDerivatives.LS U T) (fun (β : Sm E (r + s)) (F : Finset (Sm E r)) => ∀ m₂, sl0 m₂ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E r))) (fun β F F' hFF' h m₂ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h m₂)) (fun β hβ => stepA_lef …`.

Take `⟨F, hF, hQ⟩` from `hc`. Use `⟨F, hF, fun κ m₂ => ?_⟩` and prove the remaining obligations. Establish `hmem : act (.cpt κ) φ ∈ Submodule.span ℂ (↑B : Set (Sm E (r + s)))` using `hB ▸ Submodule.subset_span ⟨κ, rfl⟩`. Establish `hle : Submodule.span ℂ (↑B : Set (Sm E (r + s))) ≤ (Submodule.span ℂ (↑F : Set (Sm E r))).comap (sl0 m₂ ∘ₗ T)` using `Submodule.span_le.2 fun β hβ => hQ β (Finset.mem_coe.1 hβ) m₂`. Conclude with `hle hmem`.
-/
theorem stepB_left (hU : IsAutSt U) (hexp : HExp U T) {φ : Sm E (r + s)} (hφ : φ ∈ U) :
    ∃ F : Finset (Sm E r), (↑F : Set (Sm E r)) ⊆ BlockDerivatives.LS U T ∧
      ∀ (κ : Kinf E (r + s)) (m₂ : GA E s), sl0 m₂ (T (act (.cpt κ) φ)) ∈ Submodule.span ℂ (↑F : Set (Sm E r)) := by
  classical
  have hfd : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan φ) := (hU.2 φ hφ).kfin
  have hfg' := (Submodule.fg_iff_finiteDimensional _).2 hfd
  obtain ⟨B, hB⟩ := hfg'
  have hBU : ∀ β ∈ B, β ∈ U := fun β hβ =>
    orbSpan_le hU.1 hφ (hB ▸ Submodule.subset_span (Finset.mem_coe.2 hβ))
  have hc := collect (α := Sm E (r + s)) (β := Sm E r) B (BlockDerivatives.LS U T)
    (fun (β : Sm E (r + s)) (F : Finset (Sm E r)) => ∀ m₂, sl0 m₂ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E r)))
    (fun β F F' hFF' h m₂ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h m₂))
    (fun β hβ => stepA_left hexp (hBU β hβ))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun κ m₂ => ?_⟩
  have hmem : act (.cpt κ) φ ∈ Submodule.span ℂ (↑B : Set (Sm E (r + s))) :=
    hB ▸ Submodule.subset_span ⟨κ, rfl⟩
  have hle : Submodule.span ℂ (↑B : Set (Sm E (r + s))) ≤
      (Submodule.span ℂ (↑F : Set (Sm E r))).comap (sl0 m₂ ∘ₗ T) :=
    Submodule.span_le.2 fun β hβ => hQ β (Finset.mem_coe.1 hβ) m₂
  exact hle hmem

/- English proof (translation)
Establish `hfd : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan φ)` using `(hU.2 φ hφ).kfin`. Establish `hfg'` using `(Submodule.fg_iff_finiteDimensional _).2 hfd`. Take `⟨B, hB⟩` from `hfg'`. Establish `hBU : ∀ β ∈ B, β ∈ U` using `fun β hβ => orbSpan_le hU.1 hφ (hB ▸ Submodule.subset_span (Finset.mem_coe.2 hβ))`. Establish `hc` using `collect (α := Sm E (r + s)) (β := Sm E s) B (BlockDerivatives.RS U T) (fun (β : Sm E (r + s)) (F : Finset (Sm E s)) => ∀ m₁, sl1 m₁ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E s))) (fun β F F' hFF' h m₁ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h m₁)) (fun β hβ => stepA_rig …`.

Take `⟨F, hF, hQ⟩` from `hc`. Use `⟨F, hF, fun κ m₁ => ?_⟩` and prove the remaining obligations. Establish `hmem : act (.cpt κ) φ ∈ Submodule.span ℂ (↑B : Set (Sm E (r + s)))` using `hB ▸ Submodule.subset_span ⟨κ, rfl⟩`. Establish `hle : Submodule.span ℂ (↑B : Set (Sm E (r + s))) ≤ (Submodule.span ℂ (↑F : Set (Sm E s))).comap (sl1 m₁ ∘ₗ T)` using `Submodule.span_le.2 fun β hβ => hQ β (Finset.mem_coe.1 hβ) m₁`. Conclude with `hle hmem`.
-/
theorem stepB_right (hU : IsAutSt U) (hexp : HExp U T) {φ : Sm E (r + s)} (hφ : φ ∈ U) :
    ∃ F : Finset (Sm E s), (↑F : Set (Sm E s)) ⊆ BlockDerivatives.RS U T ∧
      ∀ (κ : Kinf E (r + s)) (m₁ : GA E r), sl1 m₁ (T (act (.cpt κ) φ)) ∈ Submodule.span ℂ (↑F : Set (Sm E s)) := by
  classical
  have hfd : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan φ) := (hU.2 φ hφ).kfin
  have hfg' := (Submodule.fg_iff_finiteDimensional _).2 hfd
  obtain ⟨B, hB⟩ := hfg'
  have hBU : ∀ β ∈ B, β ∈ U := fun β hβ =>
    orbSpan_le hU.1 hφ (hB ▸ Submodule.subset_span (Finset.mem_coe.2 hβ))
  have hc := collect (α := Sm E (r + s)) (β := Sm E s) B (BlockDerivatives.RS U T)
    (fun (β : Sm E (r + s)) (F : Finset (Sm E s)) => ∀ m₁, sl1 m₁ (T β) ∈ Submodule.span ℂ (↑F : Set (Sm E s)))
    (fun β F F' hFF' h m₁ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h m₁))
    (fun β hβ => stepA_right hexp (hBU β hβ))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun κ m₁ => ?_⟩
  have hmem : act (.cpt κ) φ ∈ Submodule.span ℂ (↑B : Set (Sm E (r + s))) :=
    hB ▸ Submodule.subset_span ⟨κ, rfl⟩
  have hle : Submodule.span ℂ (↑B : Set (Sm E (r + s))) ≤
      (Submodule.span ℂ (↑F : Set (Sm E s))).comap (sl1 m₁ ∘ₗ T) :=
    Submodule.span_le.2 fun β hβ => hQ β (Finset.mem_coe.1 hβ) m₁
  exact hle hmem

/- English proof (translation)
Establish `h1 : act (.fin l) ψ₀ = ψ₀` using `hl`. Establish `h2` using `hT.equiv (.fin l) ψ₀ hψ₀`. Rewrite `h2` using `[h1]`. Establish `h3` using `congrArg (fun F : Sm E (r + s) => F.1 y) h2`. Rewrite `h3` using `[act_fin_eq, rt_apply, yp_one_fin]`.

Conclude with `h3.symm`.
-/
theorem right_inv_of_stab (_hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) {ψ₀ : Sm E (r + s)} (hψ₀ : ψ₀ ∈ U)
    {l : GL (Fin (r + s)) (Af E)} (hl : l ∈ JFinTr.stabFin ψ₀) (y : GA E (r + s)) :
    (T ψ₀).1 (y * finGL E (r + s) l) = (T ψ₀).1 y := by
  have h1 : act (.fin l) ψ₀ = ψ₀ := hl
  have h2 := hT.equiv (.fin l) ψ₀ hψ₀
  rw [h1] at h2
  have h3 := congrArg (fun F : Sm E (r + s) => F.1 y) h2
  rw [act_fin_eq, rt_apply, yp_one_fin] at h3
  exact h3.symm

/- English proof (translation)
Establish `hL : IsOpen ((JFinTr.stabFin ψ₀ : Subgroup (GL (Fin (r + s)) (Af E))) : Set (GL (Fin (r + s)) (Af E)))` using `(hU.2 ψ₀ hψ₀).level`. Establish `hcov` using `cover (r := r) (s := s) (JFinTr.stabFin ψ₀) hL`. Take `⟨Tf, hTf⟩` from `hcov`. Establish `hc` using `collect (α := GL (Fin (r + s)) (Af E)) (β := Sm E r) Tf (BlockDerivatives.LS U T) (fun (t : GL (Fin (r + s)) (Af E)) (F : Finset (Sm E r)) => ∀ (κ : Kinf E (r + s)) (m₂ : GA E s), sl0 m₂ (T (act (.cpt κ) (act (.fin t) ψ₀))) ∈ Submodule.span ℂ (↑F : Set (Sm E r))) (fun t F F' hFF' …`. Take `⟨F, hF, hQ⟩` from `hc`.

Use `⟨F, hF, fun W hW hFW k g m₂ => ?_⟩` and prove the remaining obligations. Take `⟨x, a, b, t, l, ht, hl, rfl⟩` from `hTf g`. Rewrite using `[T_rt_yp hU.1 hT.equiv k _ hψ₀, slice_decomp_left (T ψ₀) (hT.unipInv ψ₀ hψ₀) l (right_inv_of_stab hU hT hψ₀ hl) k x a b t m₂]`. Use `hW (.fin a) _ ?_` and prove the remaining obligations. Rewrite using `[← T_rt_yp hU.1 hT.equiv k t hψ₀, rt_yp_eq]`.

Conclude with `Submodule.span_le.2 hFW (hQ t ht k _)`.
-/
theorem stepC_left (hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) (hexp : HExp U T) {ψ₀ : Sm E (r + s)}
    (hψ₀ : ψ₀ ∈ U) :
    ∃ F : Finset (Sm E r), (↑F : Set (Sm E r)) ⊆ BlockDerivatives.LS U T ∧ ∀ W : Submodule ℂ (Sm E r), IsStable W →
      (↑F : Set (Sm E r)) ⊆ W → ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₂ : GA E s),
        sl0 m₂ (T (rt E (r + s) (BlockDerivatives.yp k g) ψ₀)) ∈ W := by
  classical
  have hL : IsOpen ((JFinTr.stabFin ψ₀ : Subgroup (GL (Fin (r + s)) (Af E))) : Set (GL (Fin (r + s)) (Af E))) :=
    (hU.2 ψ₀ hψ₀).level
  have hcov := cover (r := r) (s := s) (JFinTr.stabFin ψ₀) hL
  obtain ⟨Tf, hTf⟩ := hcov
  have hc := collect (α := GL (Fin (r + s)) (Af E)) (β := Sm E r) Tf (BlockDerivatives.LS U T)
    (fun (t : GL (Fin (r + s)) (Af E)) (F : Finset (Sm E r)) => ∀ (κ : Kinf E (r + s)) (m₂ : GA E s),
      sl0 m₂ (T (act (.cpt κ) (act (.fin t) ψ₀))) ∈ Submodule.span ℂ (↑F : Set (Sm E r)))
    (fun t F F' hFF' h κ m₂ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h κ m₂))
    (fun t _ => stepB_left hU hexp (hU.1 (.fin t) ψ₀ hψ₀))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun W hW hFW k g m₂ => ?_⟩
  obtain ⟨x, a, b, t, l, ht, hl, rfl⟩ := hTf g
  rw [T_rt_yp hU.1 hT.equiv k _ hψ₀,
    slice_decomp_left (T ψ₀) (hT.unipInv ψ₀ hψ₀) l (right_inv_of_stab hU hT hψ₀ hl) k x a b t m₂]
  refine hW (.fin a) _ ?_
  rw [← T_rt_yp hU.1 hT.equiv k t hψ₀, rt_yp_eq]
  exact Submodule.span_le.2 hFW (hQ t ht k _)

/- English proof (translation)
Establish `hL : IsOpen ((JFinTr.stabFin ψ₀ : Subgroup (GL (Fin (r + s)) (Af E))) : Set (GL (Fin (r + s)) (Af E)))` using `(hU.2 ψ₀ hψ₀).level`. Establish `hcov` using `cover (r := r) (s := s) (JFinTr.stabFin ψ₀) hL`. Take `⟨Tf, hTf⟩` from `hcov`. Establish `hc` using `collect (α := GL (Fin (r + s)) (Af E)) (β := Sm E s) Tf (BlockDerivatives.RS U T) (fun (t : GL (Fin (r + s)) (Af E)) (F : Finset (Sm E s)) => ∀ (κ : Kinf E (r + s)) (m₁ : GA E r), sl1 m₁ (T (act (.cpt κ) (act (.fin t) ψ₀))) ∈ Submodule.span ℂ (↑F : Set (Sm E s))) (fun t F F' hFF' …`. Take `⟨F, hF, hQ⟩` from `hc`.

Use `⟨F, hF, fun W hW hFW k g m₁ => ?_⟩` and prove the remaining obligations. Take `⟨x, a, b, t, l, ht, hl, rfl⟩` from `hTf g`. Rewrite using `[T_rt_yp hU.1 hT.equiv k _ hψ₀, slice_decomp_right (T ψ₀) (hT.unipInv ψ₀ hψ₀) l (right_inv_of_stab hU hT hψ₀ hl) k x a b t m₁]`. Use `hW (.fin b) _ ?_` and prove the remaining obligations. Rewrite using `[← T_rt_yp hU.1 hT.equiv k t hψ₀, rt_yp_eq]`.

Conclude with `Submodule.span_le.2 hFW (hQ t ht k _)`.
-/
theorem stepC_right (hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) (hexp : HExp U T) {ψ₀ : Sm E (r + s)}
    (hψ₀ : ψ₀ ∈ U) :
    ∃ F : Finset (Sm E s), (↑F : Set (Sm E s)) ⊆ BlockDerivatives.RS U T ∧ ∀ W : Submodule ℂ (Sm E s), IsStable W →
      (↑F : Set (Sm E s)) ⊆ W → ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₁ : GA E r),
        sl1 m₁ (T (rt E (r + s) (BlockDerivatives.yp k g) ψ₀)) ∈ W := by
  classical
  have hL : IsOpen ((JFinTr.stabFin ψ₀ : Subgroup (GL (Fin (r + s)) (Af E))) : Set (GL (Fin (r + s)) (Af E))) :=
    (hU.2 ψ₀ hψ₀).level
  have hcov := cover (r := r) (s := s) (JFinTr.stabFin ψ₀) hL
  obtain ⟨Tf, hTf⟩ := hcov
  have hc := collect (α := GL (Fin (r + s)) (Af E)) (β := Sm E s) Tf (BlockDerivatives.RS U T)
    (fun (t : GL (Fin (r + s)) (Af E)) (F : Finset (Sm E s)) => ∀ (κ : Kinf E (r + s)) (m₁ : GA E r),
      sl1 m₁ (T (act (.cpt κ) (act (.fin t) ψ₀))) ∈ Submodule.span ℂ (↑F : Set (Sm E s)))
    (fun t F F' hFF' h κ m₁ => Submodule.span_mono (Finset.coe_subset.2 hFF') (h κ m₁))
    (fun t _ => stepB_right hU hexp (hU.1 (.fin t) ψ₀ hψ₀))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun W hW hFW k g m₁ => ?_⟩
  obtain ⟨x, a, b, t, l, ht, hl, rfl⟩ := hTf g
  rw [T_rt_yp hU.1 hT.equiv k _ hψ₀,
    slice_decomp_right (T ψ₀) (hT.unipInv ψ₀ hψ₀) l (right_inv_of_stab hU hT hψ₀ hl) k x a b t m₁]
  refine hW (.fin b) _ ?_
  rw [← T_rt_yp hU.1 hT.equiv k t hψ₀, rt_yp_eq]
  exact Submodule.span_le.2 hFW (hQ t ht k _)

/- English proof (translation)
Take `⟨S₀, hS₀U, hS₀⟩` from `id hfg`. Establish `hc` using `collect (α := Sm E (r + s)) (β := Sm E r) S₀ (BlockDerivatives.LS U T) (fun (ψ₀ : Sm E (r + s)) (F : Finset (Sm E r)) => ∀ W : Submodule ℂ (Sm E r), IsStable W → (↑F : Set (Sm E r)) ⊆ W → ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₂ : GA E s), sl0 m₂ (T (rt E (r + s) …`. Take `⟨F, hF, hQ⟩` from `hc`. Use `⟨F, hF, fun W hW hFW => ?_⟩` and prove the remaining obligations. Establish `hUM : U ≤ Mleft U T W` using `hS₀ _ (Mleft_stable hU hT hexp W hW) fun ψ₀ hψ₀ => ⟨hS₀U hψ₀, hQ ψ₀ hψ₀ W hW hFW⟩`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `ℓ ⟨ψ, hψ, k, g, hℓ⟩`. Take `⟨m₂, rfl⟩` from `lsF_yp (T ψ) k g ℓ hℓ`. Rewrite using `[← T_rt_yp hU.1 hT.equiv k g hψ]`. Conclude with `(hUM hψ).2 k g m₂`.
-/
theorem LS_fg (hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) (hfg : FinGen U) (hexp : HExp U T) :
    ∃ S₁ : Finset (Sm E r), (↑S₁ : Set (Sm E r)) ⊆ BlockDerivatives.LS U T ∧
      ∀ W : Submodule ℂ (Sm E r), IsStable W → (↑S₁ : Set (Sm E r)) ⊆ W → BlockDerivatives.LS U T ≤ W := by
  classical
  obtain ⟨S₀, hS₀U, hS₀⟩ := id hfg
  have hc := collect (α := Sm E (r + s)) (β := Sm E r) S₀ (BlockDerivatives.LS U T)
    (fun (ψ₀ : Sm E (r + s)) (F : Finset (Sm E r)) => ∀ W : Submodule ℂ (Sm E r), IsStable W → (↑F : Set (Sm E r)) ⊆ W →
      ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₂ : GA E s),
        sl0 m₂ (T (rt E (r + s) (BlockDerivatives.yp k g) ψ₀)) ∈ W)
    (fun ψ₀ F F' hFF' h W hW hW' => h W hW ((Finset.coe_subset.2 hFF').trans hW'))
    (fun ψ₀ hψ₀ => stepC_left hU hT hexp (hS₀U hψ₀))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun W hW hFW => ?_⟩
  have hUM : U ≤ Mleft U T W :=
    hS₀ _ (Mleft_stable hU hT hexp W hW) fun ψ₀ hψ₀ => ⟨hS₀U hψ₀, hQ ψ₀ hψ₀ W hW hFW⟩
  refine Submodule.span_le.2 ?_
  rintro ℓ ⟨ψ, hψ, k, g, hℓ⟩
  obtain ⟨m₂, rfl⟩ := lsF_yp (T ψ) k g ℓ hℓ
  rw [← T_rt_yp hU.1 hT.equiv k g hψ]
  exact (hUM hψ).2 k g m₂

/- English proof (translation)
Take `⟨S₀, hS₀U, hS₀⟩` from `id hfg`. Establish `hc` using `collect (α := Sm E (r + s)) (β := Sm E s) S₀ (BlockDerivatives.RS U T) (fun (ψ₀ : Sm E (r + s)) (F : Finset (Sm E s)) => ∀ W : Submodule ℂ (Sm E s), IsStable W → (↑F : Set (Sm E s)) ⊆ W → ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₁ : GA E r), sl1 m₁ (T (rt E (r + s) …`. Take `⟨F, hF, hQ⟩` from `hc`. Use `⟨F, hF, fun W hW hFW => ?_⟩` and prove the remaining obligations. Establish `hUM : U ≤ Mright U T W` using `hS₀ _ (Mright_stable hU hT hexp W hW) fun ψ₀ hψ₀ => ⟨hS₀U hψ₀, hQ ψ₀ hψ₀ W hW hFW⟩`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `ℓ ⟨ψ, hψ, k, g, hℓ⟩`. Take `⟨m₁, rfl⟩` from `rsF_yp (T ψ) k g ℓ hℓ`. Rewrite using `[← T_rt_yp hU.1 hT.equiv k g hψ]`. Conclude with `(hUM hψ).2 k g m₁`.
-/
theorem RS_fg (hU : IsAutSt U) {c : ℂ} (hT : IsSliceMap U c T) (hfg : FinGen U) (hexp : HExp U T) :
    ∃ S₁ : Finset (Sm E s), (↑S₁ : Set (Sm E s)) ⊆ BlockDerivatives.RS U T ∧
      ∀ W : Submodule ℂ (Sm E s), IsStable W → (↑S₁ : Set (Sm E s)) ⊆ W → BlockDerivatives.RS U T ≤ W := by
  classical
  obtain ⟨S₀, hS₀U, hS₀⟩ := id hfg
  have hc := collect (α := Sm E (r + s)) (β := Sm E s) S₀ (BlockDerivatives.RS U T)
    (fun (ψ₀ : Sm E (r + s)) (F : Finset (Sm E s)) => ∀ W : Submodule ℂ (Sm E s), IsStable W → (↑F : Set (Sm E s)) ⊆ W →
      ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₁ : GA E r),
        sl1 m₁ (T (rt E (r + s) (BlockDerivatives.yp k g) ψ₀)) ∈ W)
    (fun ψ₀ F F' hFF' h W hW hW' => h W hW ((Finset.coe_subset.2 hFF').trans hW'))
    (fun ψ₀ hψ₀ => stepC_right hU hT hexp (hS₀U hψ₀))
  obtain ⟨F, hF, hQ⟩ := hc
  refine ⟨F, hF, fun W hW hFW => ?_⟩
  have hUM : U ≤ Mright U T W :=
    hS₀ _ (Mright_stable hU hT hexp W hW) fun ψ₀ hψ₀ => ⟨hS₀U hψ₀, hQ ψ₀ hψ₀ W hW hFW⟩
  refine Submodule.span_le.2 ?_
  rintro ℓ ⟨ψ, hψ, k, g, hℓ⟩
  obtain ⟨m₁, rfl⟩ := rsF_yp (T ψ) k g ℓ hℓ
  rw [← T_rt_yp hU.1 hT.equiv k g hψ]
  exact (hUM hψ).2 k g m₁

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
