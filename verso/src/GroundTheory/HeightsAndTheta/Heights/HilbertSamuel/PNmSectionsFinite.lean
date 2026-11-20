import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNmSectionsFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntegralClosureFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace NmSectionsFinite

variable {K : Type} [Fintype K] {ι : K → Type} [∀ κ, Fintype (ι κ)] {Ω : Type} [Field Ω]

noncomputable def expo (d : K → ℕ) : K →₀ ℕ := Finsupp.equivFunOnFinite.symm d

/- English proof (translation)
The claim follows from `Finsupp.coe_equivFunOnFinite_symm d`.
-/
@[simp] theorem coe_expo (d : K → ℕ) : ⇑(expo d) = d := Finsupp.coe_equivFunOnFinite_symm d

/- English proof (translation)
Rewrite using `[Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Fintype.sum_sigma]`. Simplify using `[Finsupp.single_apply]`.
-/
theorem mapDomain_fst_apply (μ : (Σ κ, ι κ) →₀ ℕ) (κ : K) :
    μ.mapDomain Sigma.fst κ = ∑ i, μ ⟨κ, i⟩ := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Fintype.sum_sigma]
  simp [Finsupp.single_apply]

omit [Fintype K] [∀ κ, Fintype (ι κ)] in

/- English proof (translation)
Rewrite using `[mConeMap, aeval_monomial, aeval_monomial, monomial_eq, Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]`. Simplify using `only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, MvPolynomial.algebraMap_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mConeMap_monomial (y : (Σ κ, ι κ) → Ω) (μ : (Σ κ, ι κ) →₀ ℕ) (r : ℤ) :
    mConeMap y (monomial μ r) = monomial (μ.mapDomain Sigma.fst) (aeval y (monomial μ r)) := by
  rw [mConeMap, aeval_monomial, aeval_monomial, monomial_eq,
    Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow,
    MvPolynomial.algebraMap_apply]
  ring

/- English proof (translation)
Use `conv_lhs => rw [g.as_sum]`. Use `conv_rhs => rw [g.as_sum]`. Rewrite using `[map_sum, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun μ hμ => ?_` and prove the remaining obligations. Rewrite using `[mConeMap_monomial]`.

Establish `hμd : μ.mapDomain Sigma.fst = expo d`. Use extensionality with `κ`. Rewrite using `[mapDomain_fst_apply, coe_expo, hg μ hμ κ]`. Rewrite using `[hμd]`.
-/
theorem mConeMap_of_homog (y : (Σ κ, ι κ) → Ω) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    mConeMap y g = monomial (expo d) (aeval y g) := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [mConeMap_monomial]
  have hμd : μ.mapDomain Sigma.fst = expo d := by
    ext κ
    rw [mapDomain_fst_apply, coe_expo, hg μ hμ κ]
  rw [hμd]

def formRing (y : (Σ κ, ι κ) → Ω) : Subalgebra ℤ (MvPolynomial K Ω) where
  carrier := {F | ∀ m : K →₀ ℕ, coeff m F ∈ secM y ⇑m}
  mul_mem' := by
    classical
    intro F G hF hG m
    rw [coeff_mul]
    refine sum_mem fun x hx => ?_
    have hm : ⇑x.1 + ⇑x.2 = ⇑m := by rw [← Finsupp.coe_add, (Finset.HasAntidiagonal.mem_antidiagonal.mp hx)]
    rw [← hm]
    exact secM_mul_mem y (hF x.1) (hG x.2)
  add_mem' := by
    intro F G hF hG m
    rw [coeff_add]
    exact add_mem (hF m) (hG m)
  algebraMap_mem' := by
    classical
    intro n m
    rw [MvPolynomial.algebraMap_apply, coeff_C]
    split_ifs with h
    · subst h
      have h1 : (1 : Ω) ∈ secM y ⇑(0 : K →₀ ℕ) :=
        Submodule.subset_span ⟨1, ProjLine.isMultiHomog_one, map_one _⟩
      have := zsmul_mem h1 n
      simpa using this
    · exact zero_mem _

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C n`. Rewrite using `[← MvPolynomial.algebraMap_eq, AlgHom.commutes]`. Conclude with `Subalgebra.algebraMap_mem _ n`. Consider the case `add p q hp hq => rw [map_add]`.

Conclude with `add_mem hp hq`. Consider the case `mul_X p q hp`. Rewrite using `[map_mul]`. Use `Subalgebra.mul_mem _ hp fun m => ?_` and prove the remaining obligations. Rewrite using `[mConeMap, aeval_X, coeff_C_mul, coeff_X]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Use `Submodule.subset_span ⟨X q, ?_, by simp⟩` and prove the remaining obligations. Use `ProjLine.isMultiHomog_X (ι := ι) q using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `κ`.

Simplify using `[Finsupp.single_apply, eq_comm]`. Simplify using the standard rewrite rules.
-/
theorem mConeMap_mem_formRing (y : (Σ κ, ι κ) → Ω) (f : MRing ι) : mConeMap y f ∈ formRing y := by
  classical
  induction f using MvPolynomial.induction_on with
  | C n =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    exact Subalgebra.algebraMap_mem _ n
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p q hp =>
    rw [map_mul]
    refine Subalgebra.mul_mem _ hp fun m => ?_
    rw [mConeMap, aeval_X, coeff_C_mul, coeff_X]
    split_ifs with h
    · subst h
      refine Submodule.subset_span ⟨X q, ?_, by simp⟩
      convert ProjLine.isMultiHomog_X (ι := ι) q using 1
      funext κ
      simp [Finsupp.single_apply, eq_comm]
    · simp

/- English proof (translation)
Express the relevant statement in the definitionally equal form `v ∈ Submodule.span ℤ _ at hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨g, hg, rfl⟩` from `hx`. Conclude with `⟨g, mConeMap_of_homog y hg⟩`.

Consider the case `zero => simp`. Consider the case `add x z _ _ hx hz => rw [map_add]`. Conclude with `add_mem hx hz`. Consider the case `smul n x _ hx => rw [map_zsmul]`. Conclude with `zsmul_mem hx n`.
-/
theorem monomial_mem_range (y : (Σ κ, ι κ) → Ω) {d : K → ℕ} {v : Ω} (hv : v ∈ secM y d) :
    monomial (expo d) v ∈ (mConeMap y).range := by
  change v ∈ Submodule.span ℤ _ at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact ⟨g, mConeMap_of_homog y hg⟩
  | zero => simp
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul n x _ hx => rw [map_zsmul]; exact zsmul_mem hx n

/- English proof (translation)
Unfold `NmSectionsFinite.Statement`. Introduce `K _ ι _ Ω _ y a ha hy hbir τ₂`. Take `⟨k, c, -, hc0, hc⟩` from `h K ι Ω y a ha hy hbir`. Use `set R := (mConeMap y).range`. Establish `: IsNoetherianRing R` using `isNoetherianRing_of_surjective (MRing ι) R (mConeMap y).rangeRestrict.toRingHom (mConeMap y).rangeRestrict_surjective`.

Use `set G : Set (MvPolynomial K Ω) := {F | ∃ τ, τ₂ ≤ τ ∧ ∃ s ∈ chartLatNm y (fun κ => (a κ : ℤ)) τ, F = monomial (expo fun κ => τ * a κ) s}`. Use `set u : MvPolynomial K Ω := monomial (expo fun κ => k * a κ) (aeval y c)`. Establish `hinj : Function.Injective (LinearMap.mulLeft R u)`. Introduce `F F' hF`. Simplify using `only [LinearMap.mulLeft_apply] at hF`.

Conclude with `mul_left_cancel₀ (by simpa [u] using hc0) hF`. Establish `hmap : (Submodule.span R G).map (LinearMap.mulLeft R u) ≤ Submodule.span R {1}`. Rewrite using `[Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨F, ⟨τ, -, s, hs, rfl⟩, rfl⟩`. Rewrite using `[LinearMap.mulLeft_apply, monomial_mul]`.

Establish `hdeg : expo (fun κ => k * a κ) + expo (fun κ => τ * a κ) = expo fun κ => (τ + k) * a κ`. Use extensionality with `κ`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hdeg]`.

Take `⟨g, hg⟩` from `monomial_mem_range y (hc τ s hs)`. Rewrite using `[SetLike.mem_coe, Submodule.mem_span_singleton]`. Conclude with `⟨⟨_, g, rfl⟩, by rw [Subalgebra.smul_def, smul_eq_mul, mul_one]; exact hg⟩`. Establish `hfg : (Submodule.span R G).FG`. Use `Submodule.fg_of_fg_map_injective _ hinj ?_` and prove the remaining obligations.

Use `isNoetherian_of_fg_of_noetherian (Submodule.span R {(1 : MvPolynomial K Ω)}) (Submodule.fg_span_singleton 1)` as an intermediate fact. Use `isNoetherian_of_le hmap` as an intermediate fact. Conclude with `Module.Finite.iff_fg.mp inferInstance`. Take `⟨t, htG, hspan⟩` from `(Submodule.fg_span_iff_fg_span_finset_subset G).mp hfg`. Use `choose d hd e he hte using fun j : t => htG j.2`.

Use `⟨t, inferInstance, d, e, max τ₂ (Finset.univ.sup d), fun j => ⟨hd j, le_max_of_le_right (Finset.le_sup (Finset.mem_univ j)), he j⟩, ?_⟩` and prove the remaining obligations. Introduce `τ hτ s hs`. Establish `hdτ : ∀ j, d j ≤ τ` using `fun j => le_trans (le_max_of_le_right (Finset.le_sup (Finset.mem_univ j))) hτ`. Establish `hmem : monomial (expo fun κ => τ * a κ) s ∈ Submodule.span R (t : Set (MvPolynomial K Ω))`. Rewrite using `[← hspan]`.

Conclude with `Submodule.subset_span ⟨τ, le_trans (le_max_left _ _) hτ, s, hs, rfl⟩`. Take `⟨f, -, hf⟩` from `Submodule.mem_span_finset.mp hmem`. Establish `hR : ∀ F, ((f F : R) : MvPolynomial K Ω) ∈ formRing y`. Introduce `F`. Take `⟨g, hg⟩` from `(f F).2`.

Rewrite using `[← hg]`. Conclude with `mConeMap_mem_formRing y g`. Use `⟨fun j => coeff (expo fun κ => (τ - d j) * a κ) ((f j : R) : MvPolynomial K Ω), fun j => ?_, ?_⟩` and prove the remaining obligations. Simplify using `using hR j (expo fun κ => (τ - d j) * a κ)`. Establish `hc'` using `congrArg (coeff (expo fun κ => τ * a κ)) hf`.

Rewrite `hc'` using `[coeff_monomial, if_pos rfl]`. Rewrite using `[← hc', coeff_sum, ← Finset.sum_coe_sort t]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Subalgebra.smul_def, smul_eq_mul]`. Use `set p := ((f j : R) : MvPolynomial K Ω)`.

Rewrite using `[hte j]`. Rewrite using `[coeff_mul_monomial', if_pos]`. Use `congr 2`. Use extensionality with `κ`. Simplify using `[Nat.sub_mul]`.

Introduce `κ`. Simplify using `using Nat.mul_le_mul_right (a κ) (hdτ j)`.
-/
theorem proof (h : KH.CondStatement) : NmSectionsFinite.Statement := by
  unfold NmSectionsFinite.Statement
  intro K _ ι _ Ω _ y a ha hy hbir τ₂
  classical
  obtain ⟨k, c, -, hc0, hc⟩ := h K ι Ω y a ha hy hbir
  set R := (mConeMap y).range
  have : IsNoetherianRing R :=
    isNoetherianRing_of_surjective (MRing ι) R (mConeMap y).rangeRestrict.toRingHom
      (mConeMap y).rangeRestrict_surjective

  set G : Set (MvPolynomial K Ω) := {F | ∃ τ, τ₂ ≤ τ ∧ ∃ s ∈ chartLatNm y (fun κ => (a κ : ℤ)) τ,
    F = monomial (expo fun κ => τ * a κ) s}
  set u : MvPolynomial K Ω := monomial (expo fun κ => k * a κ) (aeval y c)
  have hinj : Function.Injective (LinearMap.mulLeft R u) := by
    intro F F' hF
    simp only [LinearMap.mulLeft_apply] at hF
    exact mul_left_cancel₀ (by simpa [u] using hc0) hF
  have hmap : (Submodule.span R G).map (LinearMap.mulLeft R u) ≤ Submodule.span R {1} := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨F, ⟨τ, -, s, hs, rfl⟩, rfl⟩
    rw [LinearMap.mulLeft_apply, monomial_mul]
    have hdeg : expo (fun κ => k * a κ) + expo (fun κ => τ * a κ) = expo fun κ => (τ + k) * a κ := by
      ext κ; simp; ring
    rw [hdeg]
    obtain ⟨g, hg⟩ := monomial_mem_range y (hc τ s hs)
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    exact ⟨⟨_, g, rfl⟩, by rw [Subalgebra.smul_def, smul_eq_mul, mul_one]; exact hg⟩
  have hfg : (Submodule.span R G).FG := by
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    have := isNoetherian_of_fg_of_noetherian (Submodule.span R {(1 : MvPolynomial K Ω)})
      (Submodule.fg_span_singleton 1)
    have := isNoetherian_of_le hmap
    exact Module.Finite.iff_fg.mp inferInstance
  obtain ⟨t, htG, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset G).mp hfg
  choose d hd e he hte using fun j : t => htG j.2
  refine ⟨t, inferInstance, d, e, max τ₂ (Finset.univ.sup d), fun j => ⟨hd j,
    le_max_of_le_right (Finset.le_sup (Finset.mem_univ j)), he j⟩, ?_⟩
  intro τ hτ s hs
  have hdτ : ∀ j, d j ≤ τ := fun j =>
    le_trans (le_max_of_le_right (Finset.le_sup (Finset.mem_univ j))) hτ
  have hmem : monomial (expo fun κ => τ * a κ) s ∈ Submodule.span R (t : Set (MvPolynomial K Ω)) := by
    rw [← hspan]
    exact Submodule.subset_span ⟨τ, le_trans (le_max_left _ _) hτ, s, hs, rfl⟩
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hmem
  have hR : ∀ F, ((f F : R) : MvPolynomial K Ω) ∈ formRing y := by
    intro F
    obtain ⟨g, hg⟩ := (f F).2
    rw [← hg]
    exact mConeMap_mem_formRing y g
  refine ⟨fun j => coeff (expo fun κ => (τ - d j) * a κ) ((f j : R) : MvPolynomial K Ω), fun j => ?_, ?_⟩
  · simpa using hR j (expo fun κ => (τ - d j) * a κ)
  · have hc' := congrArg (coeff (expo fun κ => τ * a κ)) hf
    rw [coeff_monomial, if_pos rfl] at hc'
    rw [← hc', coeff_sum, ← Finset.sum_coe_sort t]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subalgebra.smul_def, smul_eq_mul]
    set p := ((f j : R) : MvPolynomial K Ω)
    rw [hte j]
    rw [coeff_mul_monomial', if_pos]
    · congr 2
      ext κ
      simp [Nat.sub_mul]
    · intro κ
      simpa using Nat.mul_le_mul_right (a κ) (hdτ j)

end NmSectionsFinite

end GroundTheory.Heights₂.Heights.HilbertSamuel
