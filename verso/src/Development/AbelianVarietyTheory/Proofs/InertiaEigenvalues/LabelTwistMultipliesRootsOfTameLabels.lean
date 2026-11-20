import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

namespace GlobalTheory.TwistLabel

/- English proof (translation)
Take `⟨x, hx⟩` from `Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar g))`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx`. Assume the negation of the conclusion as `h0`. Establish `h1 : t 0 * t x = t 0 * t 1` using `by rw [← map_mul, ← map_mul, zero_mul, zero_mul]`. Conclude with `hx.2 (ht x 1 hx.1 one_ne_zero (mul_left_cancel₀ h0 h1))`.
-/
theorem teich_zero' {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : t 0 = 0 := by
  classical
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar g))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  by_contra h0
  have h1 : t 0 * t x = t 0 * t 1 := by rw [← map_mul, ← map_mul, zero_mul, zero_mul]
  exact hx.2 (ht x 1 hx.1 one_ne_zero (mul_left_cancel₀ h0 h1))

/- English proof (translation)
Establish `h0` using `teich_zero' t ht`. Establish `hne : ∀ x, x ≠ 0 → t x ≠ 0` using `fun x hx => ((IsUnit.mk0 x hx).map t).ne_zero`. Introduce `x y h`. Distinguish the cases in `hx : x = 0`. Assume the negation of the conclusion as `hxy`.

Conclude with `hne y (fun hy => hxy (hx.trans hy.symm)) (by rw [← h, hx, h0])`. Distinguish the cases in `hy : y = 0`. Conclude with `absurd (by rw [h, hy, h0]) (hne x hx)`. Conclude with `ht x y hx hy h`.
-/
theorem teich_injective' {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : Function.Injective t := by
  have h0 := teich_zero' t ht
  have hne : ∀ x, x ≠ 0 → t x ≠ 0 := fun x hx => ((IsUnit.mk0 x hx).map t).ne_zero
  intro x y h
  by_cases hx : x = 0
  · by_contra hxy
    exact hne y (fun hy => hxy (hx.trans hy.symm)) (by rw [← h, hx, h0])
  · by_cases hy : y = 0
    · exact absurd (by rw [h, hy, h0]) (hne x hx)
    · exact ht x y hx hy h

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s IH`. Rewrite using `[Multiset.map_cons, Multiset.prod_cons, mul_scaleRoots', X_sub_C_scaleRoots, IH, Multiset.map_cons, Multiset.prod_cons]`. Rewrite using `[leadingCoeff_X_sub_C, one_mul, ne_eq, leadingCoeff_eq_zero]`.

Conclude with `(monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C _).ne_zero`.
-/
theorem prod_scaleRoots {α : Type*} (s : Multiset α) (f : α → ℂ) (c : ℂ) :
    ((s.map fun x => X - C (f x)).prod).scaleRoots c = (s.map fun x => X - C (f x * c)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s IH =>
    rw [Multiset.map_cons, Multiset.prod_cons, mul_scaleRoots', X_sub_C_scaleRoots, IH,
      Multiset.map_cons, Multiset.prod_cons]
    rw [leadingCoeff_X_sub_C, one_mul, ne_eq, leadingCoeff_eq_zero]
    exact (monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C _).ne_zero

/- English proof (translation)
Rewrite using `[show (s.map fun x => X - C (f x)) = (s.map f).map (fun a => X - C a) by rw [Multiset.map_map]; rfl]`. Conclude with `roots_multiset_prod_X_sub_C _`.
-/
theorem roots_prod_map {α : Type*} (s : Multiset α) (f : α → ℂ) :
    ((s.map fun x => X - C (f x)).prod).roots = s.map f := by
  rw [show (s.map fun x => X - C (f x)) = (s.map f).map (fun a => X - C a) by rw [Multiset.map_map]; rfl]
  exact roots_multiset_prod_X_sub_C _

end GlobalTheory.TwistLabel

open GlobalTheory.TwistLabel in
/- English proof (translation)
Introduce `D hT _ hDep hGen k w hw L χ u hL hχ hχl`. Use `haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩`. Take `⟨γ, hγ, hG⟩` from `hGen`. Establish `hLP` using `hT.1`. Establish `hγI : γ k w ∈ Ine (F` using `D.host.E) (D.nd.plOm.1 w) := (hγ.2 k w hw).1`.

Establish `hdim : D.naut.lpDim (D.naut.lpChar L χ) = D.naut.lpDim L` using `D.naut.lpDim_char L χ hχ`. Establish `hχdeg : (D.naut.items₂ k w χ).natDegree = D.naut.lpDim χ` using `by rw [hχl, natDegree_X_sub_C, hχ]`. Establish `hχtame : TameLP D χ` using `((hDep k w hw χ).2).1 hχdeg`. Establish `hLtame : TameLP D L` using `((hDep k w hw L).2).1 hL`. Establish `hLχtame : TameLP D (D.naut.lpChar L χ)`.

Introduce `σ hσ hwσ`. Establish `h1` using `hχtame σ hσ hwσ`. Rewrite `h1` using `[hχ, pow_one]`. Establish `h2` using `((hLP w L L χ χ 0 hχ hχ).2.2.2.2.2 σ hσ).2 1 (by rw [h1, map_one])`. Rewrite using `[h2, hLtame σ hσ hwσ, scaleRoots_one, hdim]`.

Establish `hfull : (D.naut.items₂ k w (D.naut.lpChar L χ)).natDegree = D.naut.lpDim L`. Rewrite using `[← hdim]`. Conclude with `((hDep k w hw _).2).2 hLχtame`. Use `⟨hfull, ?_⟩` and prove the remaining obligations. Use `set u' := algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)) with hu'`.

Establish `hrχ : Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w χ) = {u'}`. Rewrite using `[hχl, Formalism.CyclotomicNorms.rootsBar, Polynomial.map_sub, map_X, map_C, roots_X_sub_C]`. Establish `hχγ : D.naut.inePol χ (γ k w) = X - C (D.ntypes.teichC k u')`. Rewrite using `[hG k w hw χ hχdeg, hrχ]`. Simplify using the standard rewrite rules.

Establish `hsc` using `((hLP w L L χ χ 0 hχ hχ).2.2.2.2.2 (γ k w) hγI).2 _ hχγ`. Rewrite `hsc` using `[hG k w hw L hL, prod_scaleRoots, hG k w hw _ (hfull.trans hdim.symm)]`. Establish `hr` using `congrArg Polynomial.roots hsc`. Rewrite `hr` using `[roots_prod_map, roots_prod_map]`. Establish `hinj` using `teich_injective' (D.ntypes.teichC k) (D.ntypes.teichC_inj k)`.

Apply `Multiset.map_injective hinj` to reduce the goal to its premises. Rewrite using `[hr, Multiset.map_map]`. Apply `Multiset.map_congr rfl` to reduce the goal to its premises. Introduce `x _`. Simplify using `[Function.comp, map_mul]`.
-/
theorem main : ∀ D : D7, SumRepresentations.tie0 D → IneRep D → LabDepth D → LabGen D → LabChar D := by
  intro D hT _ hDep hGen k w hw L χ u hL hχ hχl
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨γ, hγ, hG⟩ := hGen
  have hLP := hT.1
  have hγI : γ k w ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) := (hγ.2 k w hw).1
  have hdim : D.naut.lpDim (D.naut.lpChar L χ) = D.naut.lpDim L := D.naut.lpDim_char L χ hχ
  have hχdeg : (D.naut.items₂ k w χ).natDegree = D.naut.lpDim χ := by rw [hχl, natDegree_X_sub_C, hχ]
  have hχtame : TameLP D χ := ((hDep k w hw χ).2).1 hχdeg
  have hLtame : TameLP D L := ((hDep k w hw L).2).1 hL
  have hLχtame : TameLP D (D.naut.lpChar L χ) := by
    intro σ hσ hwσ
    have h1 := hχtame σ hσ hwσ
    rw [hχ, pow_one] at h1
    have h2 := ((hLP w L L χ χ 0 hχ hχ).2.2.2.2.2 σ hσ).2 1 (by rw [h1, map_one])
    rw [h2, hLtame σ hσ hwσ, scaleRoots_one, hdim]
  have hfull : (D.naut.items₂ k w (D.naut.lpChar L χ)).natDegree = D.naut.lpDim L := by
    rw [← hdim]; exact ((hDep k w hw _).2).2 hLχtame
  refine ⟨hfull, ?_⟩
  set u' := algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)) with hu'
  have hrχ : Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w χ) = {u'} := by
    rw [hχl, Formalism.CyclotomicNorms.rootsBar, Polynomial.map_sub, map_X, map_C, roots_X_sub_C]
  have hχγ : D.naut.inePol χ (γ k w) = X - C (D.ntypes.teichC k u') := by
    rw [hG k w hw χ hχdeg, hrχ]; simp
  have hsc := ((hLP w L L χ χ 0 hχ hχ).2.2.2.2.2 (γ k w) hγI).2 _ hχγ
  rw [hG k w hw L hL, prod_scaleRoots, hG k w hw _ (hfull.trans hdim.symm)] at hsc
  have hr := congrArg Polynomial.roots hsc
  rw [roots_prod_map, roots_prod_map] at hr
  have hinj := teich_injective' (D.ntypes.teichC k) (D.ntypes.teichC_inj k)
  apply Multiset.map_injective hinj
  rw [hr, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro x _
  simp [Function.comp, map_mul]
