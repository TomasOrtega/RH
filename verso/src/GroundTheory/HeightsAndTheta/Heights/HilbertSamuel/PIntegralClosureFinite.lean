import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNmSectionsRational
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNmSectionsFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Establish `hgen : ∀ g : MRing ι, IsMultiHomog g d → aeval y g * t ∈ secM y (d + e)`. Introduce `g hg`. Express the relevant statement in the definitionally equal form `t ∈ Submodule.span ℤ _ at ht`. Express the relevant statement in the definitionally equal form `_ ∈ Submodule.span ℤ _`. Proceed by induction on `ht using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨h, hh, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨g * h, ProjLine.mhMul hg hh, by rw [map_mul]⟩`. Consider the case `zero => simp`. Consider the case `add x z _ _ hx hz => rw [mul_add]`.

Conclude with `add_mem hx hz`. Consider the case `smul n x _ hx => rw [mul_smul_comm]`. Conclude with `Submodule.smul_mem _ _ hx`. Express the relevant statement in the definitionally equal form `s ∈ Submodule.span ℤ _ at hs`. Proceed by induction on `hs using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨g, hg, rfl⟩` from `hx`. Conclude with `hgen g hg`. Consider the case `zero => simp`. Consider the case `add x z _ _ hx hz => rw [add_mul]`.

Conclude with `add_mem hx hz`. Consider the case `smul n x _ hx => rw [smul_mul_assoc]`. Conclude with `zsmul_mem hx n`.
-/
theorem secM_mul_mem (y : (Σ k, ι k) → Ω) {d e : K → ℕ} {s t : Ω} (hs : s ∈ secM y d)
    (ht : t ∈ secM y e) : s * t ∈ secM y (d + e) := by
  have hgen : ∀ g : MRing ι, IsMultiHomog g d → aeval y g * t ∈ secM y (d + e) := by
    intro g hg
    change t ∈ Submodule.span ℤ _ at ht
    change _ ∈ Submodule.span ℤ _
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * h, ProjLine.mhMul hg hh, by rw [map_mul]⟩
    | zero => simp
    | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
    | smul n x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
  change s ∈ Submodule.span ℤ _ at hs
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact hgen g hg
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul n x _ hx => rw [smul_mul_assoc]; exact zsmul_mem hx n

/- English proof (translation)
Unfold `IntegralClosureFinite.Statement KH.NormalizationBoundedIndexStatement`. Unfold `NmSectionsRational.Statement at hR`. Unfold `NmSectionsFinite.Statement at hF`. Introduce `K _ ι _ Ω _ _ y a ha hy hbir hnorm`. Take `⟨τ₀, hτ₀⟩` from `hR K ι Ω y a ha hy hbir hnorm`.

Take `⟨J, _, d, e, τ₁, he, hgen⟩` from `hF K ι Ω y a ha hy hbir τ₀`. Use `choose m hm1 hme using fun j => hτ₀ (d j) (he j).1 (e j) (he j).2.2`. Use `⟨∏ j, m j, τ₁, Nat.one_le_iff_ne_zero.mpr (Finset.prod_pos fun j _ => hm1 j).ne', ?_⟩` and prove the remaining obligations. Introduce `τ hτ s hs`. Take `⟨r, hr, rfl⟩` from `hgen τ hτ s hs`.

Rewrite using `[Finset.mul_sum]`. Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Establish `hsplit : (∏ i, m i : ℕ) = (∏ i ∈ Finset.univ.erase j, m i) * m j` using `(Finset.prod_erase_mul _ _ (Finset.mem_univ j)).symm`. Establish `hdeg : (fun k => τ * a k) = (fun k => (τ - d j) * a k) + (fun k => d j * a k)`. Use function extensionality and compare the values at `k`.

Simplify using `only [Pi.add_apply]`. Rewrite using `[← add_mul, Nat.sub_add_cancel (le_trans (he j).2.1 hτ)]`. Establish `hval : ((∏ i, m i : ℕ) : Ω) * (r j * e j) = ((∏ i ∈ Finset.univ.erase j, m i : ℕ) : ℤ) • (r j * ((m j : Ω) * e j))`. Rewrite using `[hsplit, zsmul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hval, hdeg]`. Conclude with `zsmul_mem (secM_mul_mem y (hr j) (hme j)) _`.
-/
theorem IntegralClosureFinite.proof (hR : NmSectionsRational.Statement) (hF : NmSectionsFinite.Statement) :
    IntegralClosureFinite.Statement := by
  unfold IntegralClosureFinite.Statement KH.NormalizationBoundedIndexStatement
  unfold NmSectionsRational.Statement at hR
  unfold NmSectionsFinite.Statement at hF
  intro K _ ι _ Ω _ _ y a ha hy hbir hnorm
  obtain ⟨τ₀, hτ₀⟩ := hR K ι Ω y a ha hy hbir hnorm
  obtain ⟨J, _, d, e, τ₁, he, hgen⟩ := hF K ι Ω y a ha hy hbir τ₀
  choose m hm1 hme using fun j => hτ₀ (d j) (he j).1 (e j) (he j).2.2
  classical
  refine ⟨∏ j, m j, τ₁, Nat.one_le_iff_ne_zero.mpr (Finset.prod_pos fun j _ => hm1 j).ne', ?_⟩
  intro τ hτ s hs
  obtain ⟨r, hr, rfl⟩ := hgen τ hτ s hs
  rw [Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  have hsplit : (∏ i, m i : ℕ) = (∏ i ∈ Finset.univ.erase j, m i) * m j :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ j)).symm
  have hdeg : (fun k => τ * a k) = (fun k => (τ - d j) * a k) + (fun k => d j * a k) := by
    funext k
    simp only [Pi.add_apply]
    rw [← add_mul, Nat.sub_add_cancel (le_trans (he j).2.1 hτ)]
  have hval : ((∏ i, m i : ℕ) : Ω) * (r j * e j) =
      ((∏ i ∈ Finset.univ.erase j, m i : ℕ) : ℤ) • (r j * ((m j : Ω) * e j)) := by
    rw [hsplit, zsmul_eq_mul]
    push_cast
    ring
  rw [hval, hdeg]
  exact zsmul_mem (secM_mul_mem y (hr j) (hme j)) _

end GroundTheory.Heights₂.Heights.HilbertSamuel
