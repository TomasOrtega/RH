import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

namespace GlobalTheory.JointDiag

/- English proof (translation)
Proceed by induction on `q using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `monomial n c`. Simplify using `only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Module.End.pow_restrict, LinearMap.restrict_apply, Submodule.coe_smul]`. Rewrite using `[Module.End.pow_restrict n hW]`.

Both sides reduce to the same expression.
-/
theorem aeval_restrict_coe {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (W : Submodule K V) (hW : ∀ x ∈ W, T x ∈ W) (q : K[X]) (y : W) :
    ((aeval (T.restrict hW) q y : W) : V) = aeval T q (y : V) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Module.End.pow_restrict,
      LinearMap.restrict_apply, Submodule.coe_smul]
    rw [Module.End.pow_restrict n hW]
    rfl

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Conclude with `LinearMap.ker_id`. Introduce `a s ha ih`. Rewrite using `[Finset.prod_insert ha, ← sup_ker_aeval_eq_ker_aeval_mul_of_coprime, ih, Finset.iSup_insert]`.

Use `congr 1`. Rewrite using `[Module.End.eigenspace_def, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]`. Conclude with `IsCoprime.prod_right fun i hi => (pairwise_coprime_X_sub_C (K := K) (s := id) Function.injective_id) (fun h => ha (h ▸ hi))`.
-/
theorem ker_prod {K M : Type} [Field K] [AddCommGroup M] [Module K M]
    (f : Module.End K M) (s : Finset K) :
    LinearMap.ker (aeval f (∏ r ∈ s, (X - C r))) = ⨆ r ∈ s, f.eigenspace r := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
    exact LinearMap.ker_id
  · intro a s ha ih
    rw [Finset.prod_insert ha, ← sup_ker_aeval_eq_ker_aeval_mul_of_coprime, ih, Finset.iSup_insert]
    · congr 1
      rw [Module.End.eigenspace_def, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
    · exact IsCoprime.prod_right fun i hi =>
        (pairwise_coprime_X_sub_C (K := K) (s := id) Function.injective_id) (fun h => ha (h ▸ hi))

/- English proof (translation)
Establish `hne : p ≠ 0` using `hs.ne_zero`. Set `s : Finset K` to `⟨p.roots, nodup_roots hs⟩`. Establish `hprod : ∏ r ∈ s, (X - C r) = (p.roots.map (X - C ·)).prod` using `rfl`. Establish `hc : p.leadingCoeff ≠ 0` using `leadingCoeff_ne_zero.mpr hne`. Establish `hker : LinearMap.ker (aeval f (∏ r ∈ s, (X - C r))) = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `h1` using `LinearMap.congr_fun h0 x`. Rewrite `h1` using `[hp.eq_prod_roots, ← hprod, map_mul, aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply, LinearMap.zero_apply, smul_eq_zero]`. Conclude with `h1.resolve_left hc`.

Rewrite `hker` using `[ker_prod]`. Rewrite using `[eq_top_iff, ← hker]`. Conclude with `iSup₂_le fun r _ => le_iSup (fun μ => f.eigenspace μ) r`.
-/
theorem iSup_eigenspace_eq_top_of_aeval {K M : Type} [Field K] [AddCommGroup M] [Module K M]
    (f : Module.End K M) (p : K[X]) (hs : p.Separable) (hp : p.Splits) (h0 : aeval f p = 0) :
    ⨆ μ, f.eigenspace μ = ⊤ := by
  classical
  have hne : p ≠ 0 := hs.ne_zero
  let s : Finset K := ⟨p.roots, nodup_roots hs⟩
  have hprod : ∏ r ∈ s, (X - C r) = (p.roots.map (X - C ·)).prod := rfl
  have hc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hne
  have hker : LinearMap.ker (aeval f (∏ r ∈ s, (X - C r))) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 := LinearMap.congr_fun h0 x
    rw [hp.eq_prod_roots, ← hprod, map_mul, aeval_C, Module.End.mul_apply,
      Module.algebraMap_end_apply, LinearMap.zero_apply, smul_eq_zero] at h1
    exact h1.resolve_left hc
  rw [ker_prod] at hker
  rw [eq_top_iff, ← hker]
  exact iSup₂_le fun r _ => le_iSup (fun μ => f.eigenspace μ) r

/- English proof (translation)
Introduce `K V ι _ _ _ _ T W hc hW hp`. Set `S : ι → Module.End K W` to `fun a => (T a).restrict (hW a)`. Establish `hS0 : ∀ a, ∃ p : K[X], p.Separable ∧ p.Splits ∧ aeval (S a) p = 0`. Introduce `a`. Take `⟨p, hs, hsp, hx⟩` from `hp a`.

Use `⟨p, hs, hsp, LinearMap.ext fun y => Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[aeval_restrict_coe]`. Simplify using `using hx y y.2`. Establish `hmax : ∀ a μ, (S a).maxGenEigenspace μ = (S a).eigenspace μ`. Introduce `a μ`.

Take `⟨p, hs, _, h0⟩` from `hS0 a`. Conclude with `(Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.squarefree h0).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ`. Establish `hdiag : ∀ a, ⨆ μ, (S a).maxGenEigenspace μ = ⊤`. Introduce `a`. Take `⟨p, hs, hsp, h0⟩` from `hS0 a`.

Repeatedly rewrite using `[hmax]`. Conclude with `iSup_eigenspace_eq_top_of_aeval (S a) p hs hsp h0`. Establish `hcomm : Pairwise fun i j => Commute (S i) (S j)` using `fun i j _ => LinearMap.restrict_commute (hc i j) (hW i) (hW j)`. Establish `htop` using `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute S hcomm hdiag`. Rewrite `htop` using `[hmax]`.

Establish `hle : Submodule.map W.subtype (⨆ χ : ι → K, ⨅ a, (S a).eigenspace (χ a)) ≤ ⨆ ev : ι → K, ((⨅ a, LinearMap.ker (T a - ev a • LinearMap.id)) ⊓ W)`. Rewrite using `[Submodule.map_iSup]`. Use `iSup_mono fun χ => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `⟨?_, y.2⟩` and prove the remaining obligations.

Rewrite `hy`, the goal using `[SetLike.mem_coe]`. Rewrite using `[Submodule.mem_iInf]`. Introduce `a`. Establish `h` using `Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hy a)`. Establish `h'` using `congrArg Subtype.val h`.

Simplify using `only [S, LinearMap.restrict_apply, Submodule.coe_smul] at h'`. Rewrite using `[LinearMap.mem_ker, Submodule.subtype_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, h', sub_self]`. Introduce `x hx`. Establish `hmem : (⟨x, hx⟩ : W) ∈ ⨆ χ : ι → K, ⨅ a, (S a).eigenspace (χ a)`. Rewrite using `[htop]`.

Discharge the goal by the elementary cases of `trivial`. Conclude with `hle ⟨⟨x, hx⟩, hmem, rfl⟩`.
-/
theorem le_iSup_jointEigenspace_inf : ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (T : ι → Module.End K V) (W : Submodule K V), (∀ a c, Commute (T a) (T c)) → (∀ a, ∀ x ∈ W, T a x ∈ W) → (∀ a, ∃ p : K[X], p.Separable ∧ p.Splits ∧ ∀ x ∈ W, Polynomial.aeval (T a) p x = 0) → W ≤ ⨆ ev : ι → K, ((⨅ a, LinearMap.ker (T a - ev a • LinearMap.id)) ⊓ W) := by
  intro K V ι _ _ _ _ T W hc hW hp
  let S : ι → Module.End K W := fun a => (T a).restrict (hW a)
  have hS0 : ∀ a, ∃ p : K[X], p.Separable ∧ p.Splits ∧ aeval (S a) p = 0 := by
    intro a
    obtain ⟨p, hs, hsp, hx⟩ := hp a
    refine ⟨p, hs, hsp, LinearMap.ext fun y => Subtype.ext ?_⟩
    rw [aeval_restrict_coe]
    simpa using hx y y.2
  have hmax : ∀ a μ, (S a).maxGenEigenspace μ = (S a).eigenspace μ := by
    intro a μ
    obtain ⟨p, hs, _, h0⟩ := hS0 a
    exact (Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.squarefree h0).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have hdiag : ∀ a, ⨆ μ, (S a).maxGenEigenspace μ = ⊤ := by
    intro a
    obtain ⟨p, hs, hsp, h0⟩ := hS0 a
    simp_rw [hmax]
    exact iSup_eigenspace_eq_top_of_aeval (S a) p hs hsp h0
  have hcomm : Pairwise fun i j => Commute (S i) (S j) := fun i j _ =>
    LinearMap.restrict_commute (hc i j) (hW i) (hW j)
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute S hcomm hdiag
  simp_rw [hmax] at htop
  have hle : Submodule.map W.subtype (⨆ χ : ι → K, ⨅ a, (S a).eigenspace (χ a)) ≤
      ⨆ ev : ι → K, ((⨅ a, LinearMap.ker (T a - ev a • LinearMap.id)) ⊓ W) := by
    rw [Submodule.map_iSup]
    refine iSup_mono fun χ => ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨?_, y.2⟩
    rw [SetLike.mem_coe] at hy ⊢
    rw [Submodule.mem_iInf]
    intro a
    have h := Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hy a)
    have h' := congrArg Subtype.val h
    simp only [S, LinearMap.restrict_apply, Submodule.coe_smul] at h'
    rw [LinearMap.mem_ker, Submodule.subtype_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, h', sub_self]
  intro x hx
  have hmem : (⟨x, hx⟩ : W) ∈ ⨆ χ : ι → K, ⨅ a, (S a).eigenspace (χ a) := by
    rw [htop]; trivial
  exact hle ⟨⟨x, hx⟩, hmem, rfl⟩

end GlobalTheory.JointDiag
