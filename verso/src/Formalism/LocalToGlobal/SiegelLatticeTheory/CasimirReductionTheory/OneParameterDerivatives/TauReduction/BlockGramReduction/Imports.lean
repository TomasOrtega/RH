import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow

set_option autoImplicit false

noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.Tau

/- English proof (translation)
Introduce `K _ _ n j M B b hM hBM hli hbB hBspan`. Establish `hBfg : B.FG` using `by haveI := isNoetherian_of_fg_of_noetherian M hM`. Establish `h1 : (B.comap M.subtype).FG` using `IsNoetherian.noetherian _`. Establish `h2` using `h1.map M.subtype`. Rewrite `h2` using `[Submodule.map_comap_subtype, inf_eq_right.mpr hBM]`. Then use the resulting hypothesis.

Take `⟨s, hs⟩` from `hBfg`. Establish `hcoef : ∀ g ∈ s, ∃ c : Fin j → K, ∑ a, c a • b a = g` using `fun g hg => (Submodule.mem_span_range_iff_exists_fun K).mp (hBspan (hs ▸ Submodule.subset_span hg))`. Use `choose! c hc using hcoef`. Take `⟨y, hy0, hy⟩` from `exists_integral_multiples ℤ ℚ ((s ×ˢ Finset.univ).image (fun p : (Fin n → K) × Fin j => c p.1 p.2))`. Establish `hyg : ∀ g ∈ s, (y : ℤ) • g ∈ Submodule.span (𝓞 K) (Set.range b)`.

Introduce `g hg`. Rewrite using `[← hc g hg, Finset.smul_sum]`. Use `Submodule.sum_mem _ fun a _ => ?_` and prove the remaining obligations. Establish `hint : IsIntegral ℤ (y • c g a)` using `hy _ (Finset.mem_image.mpr ⟨(g, a), Finset.mem_product.mpr ⟨hg, Finset.mem_univ a⟩, rfl⟩)`. Establish `e : (y : ℤ) • (c g a • b a) = (⟨y • c g a, hint⟩ : 𝓞 K) • b a`.

Rewrite using `[← smul_assoc]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`. Establish `hyB : ∀ v ∈ B, (y : ℤ) • v ∈ Submodule.span (𝓞 K) (Set.range b)`.

Rewrite using `[← hs]`. Introduce `v hv`. Use `Submodule.span_induction (fun g hg => hyg g hg) (by simp) (fun u w _ _ hu hw => by rw [smul_add]; exact add_mem hu hw) (fun o u _ hu => by rw [smul_comm]; exact Submodule.smul_mem _ o hu) hv` and prove the remaining obligations. Use `haveI : Module.Finite (𝓞 K) B := Module.Finite.iff_fg.mpr ⟨s, hs⟩`. Use `haveI : Module.Finite ℤ (B ⧸ (Submodule.span (𝓞 K) (Set.range b)).comap B.subtype) := Module.Finite.trans (𝓞 K) _`.

Apply `Module.finite_of_fg_torsion` to reduce the goal to its premises. Introduce `q`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective ((Submodule.span (𝓞 K) (Set.range b)).comap B.subtype) q`. Use `⟨⟨y, mem_nonZeroDivisors_of_ne_zero hy0⟩, ?_⟩` and prove the remaining obligations. Use `show (y : ℤ) • (Submodule.Quotient.mk (p := (Submodule.span (𝓞 K) (Set.range b)).comap B.subtype) v) = 0`.

Establish `hz` using `map_zsmul (Submodule.mkQ ((Submodule.span (𝓞 K) (Set.range b)).comap B.subtype)) y v`. Rewrite `hz` using `[Submodule.mkQ_apply, Submodule.mkQ_apply]`. Rewrite using `[← hz, Submodule.Quotient.mk_eq_zero]`. Conclude with `hyB v v.2`.
-/
theorem t2 : ExistsBoundedBasis := by
  intro K _ _ n j M B b hM hBM hli hbB hBspan
  classical
  have hBfg : B.FG := by
    haveI := isNoetherian_of_fg_of_noetherian M hM
    have h1 : (B.comap M.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map M.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hBM] at h2
  obtain ⟨s, hs⟩ := hBfg
  have hcoef : ∀ g ∈ s, ∃ c : Fin j → K, ∑ a, c a • b a = g := fun g hg =>
    (Submodule.mem_span_range_iff_exists_fun K).mp (hBspan (hs ▸ Submodule.subset_span hg))
  choose! c hc using hcoef
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    ((s ×ˢ Finset.univ).image (fun p : (Fin n → K) × Fin j => c p.1 p.2))
  have hyg : ∀ g ∈ s, (y : ℤ) • g ∈ Submodule.span (𝓞 K) (Set.range b) := by
    intro g hg
    rw [← hc g hg, Finset.smul_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    have hint : IsIntegral ℤ (y • c g a) :=
      hy _ (Finset.mem_image.mpr ⟨(g, a), Finset.mem_product.mpr ⟨hg, Finset.mem_univ a⟩, rfl⟩)
    have e : (y : ℤ) • (c g a • b a) = (⟨y • c g a, hint⟩ : 𝓞 K) • b a := by
      rw [← smul_assoc]
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hyB : ∀ v ∈ B, (y : ℤ) • v ∈ Submodule.span (𝓞 K) (Set.range b) := by
    rw [← hs]
    intro v hv
    refine Submodule.span_induction (fun g hg => hyg g hg) (by simp)
      (fun u w _ _ hu hw => by rw [smul_add]; exact add_mem hu hw)
      (fun o u _ hu => by rw [smul_comm]; exact Submodule.smul_mem _ o hu) hv
  haveI : Module.Finite (𝓞 K) B := Module.Finite.iff_fg.mpr ⟨s, hs⟩
  haveI : Module.Finite ℤ (B ⧸ (Submodule.span (𝓞 K) (Set.range b)).comap B.subtype) :=
    Module.Finite.trans (𝓞 K) _
  apply Module.finite_of_fg_torsion
  intro q
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective ((Submodule.span (𝓞 K) (Set.range b)).comap B.subtype) q
  refine ⟨⟨y, mem_nonZeroDivisors_of_ne_zero hy0⟩, ?_⟩
  show (y : ℤ) • (Submodule.Quotient.mk (p := (Submodule.span (𝓞 K) (Set.range b)).comap B.subtype) v) = 0
  have hz := map_zsmul (Submodule.mkQ ((Submodule.span (𝓞 K) (Set.range b)).comap B.subtype)) y v
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at hz
  rw [← hz, Submodule.Quotient.mk_eq_zero]
  exact hyB v v.2

end Formalism.L2.SG.Pf.Tau
