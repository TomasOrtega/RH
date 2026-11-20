import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAddCharComponentTrivialIntegersEventually
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.PsiProd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F]

def intFin (y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) : Af F :=
  RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
    (fun v => ⟨(y v).1, (y v).2⟩)

/- English proof (translation)
The claim follows from `RestrictedProduct.isEmbedding_structureMap.continuous`.
-/
theorem continuous_intFin : Continuous (intFin (F := F)) :=
  RestrictedProduct.isEmbedding_structureMap.continuous

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalV_intFin (y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F))
    (w : HeightOneSpectrum (𝓞 F)) : evalV F w (intFin y) = (y w : Fv F w) := rfl

/- English proof (translation)
Use `GlobalTheory.AdelicU.af_ext fun w => ?_` and prove the remaining obligations. Rewrite using `[map_nsmul, evalV_intFin, evalV_intFin]`. Both sides reduce to the same expression.
-/
theorem intFin_nsmul (n : ℕ) (y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) :
    intFin (n • y) = n • intFin y := by
  refine GlobalTheory.AdelicU.af_ext fun w => ?_
  rw [map_nsmul, evalV_intFin, evalV_intFin]
  rfl

/- English proof (translation)
Set `ι : (∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) → AF F` to `fun y => LinearMap.inr F (Ainf F) (Af F) (intFin y)`. Establish `hι : Continuous ι` using `continuous_const.prodMk continuous_intFin`. Establish `hopen : IsOpen {y | ‖ψ (ι y) - 1‖ < 1 / 2}` using `isOpen_lt ((hψ.comp hι).sub continuous_const).norm continuous_const`. Establish `h0 : (0 : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) ∈ {y | ‖ψ (ι y) - 1‖ < 1 / 2}`. Establish `: ι 0 = 0`.

Establish `h : intFin (0 : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) = 0`. Simplify using `using intFin_nsmul (F := F) 0 0`. Use `show LinearMap.inr F (Ainf F) (Af F) (intFin 0) = (0 : AF F)`. Rewrite using `[h, map_zero]`. Both sides reduce to the same expression.

Simplify using `[this, AddChar.map_zero_eq_one]`. Take `⟨I, u, hu, hsub⟩` from `isOpen_pi_iff.1 hopen 0 h0`. Use `⟨I, fun y hy => GlobalTheory.eq_one_of_forall_norm_pow_sub_one_lt _ fun n => ?_⟩` and prove the remaining obligations. Establish `hmem : n • y ∈ (I : Set _).pi u`. Introduce `a ha`.

Establish `: (n • y) a = 0` using `by rw [Pi.smul_apply, hy a ha, smul_zero]`. Rewrite using `[this]`. Conclude with `(hu a ha).2`. Establish `e : (ι (n • y) : AF F) = n • (ι y : AF F)` using `by show LinearMap.inr F (Ainf F) (Af F) (intFin (n • y)) = _`. Rewrite using `[intFin_nsmul, map_nsmul]`.

Both sides reduce to the same expression. Establish `h` using `hsub hmem`. Simplify using `only [Set.mem_setOf_eq] at h`. Rewrite `h` using `[e, AddChar.map_nsmul_eq_pow]`. Then use the resulting hypothesis.
-/
theorem exists_finset_trivial (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) :
    ∃ I : Finset (HeightOneSpectrum (𝓞 F)), ∀ y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F),
      (∀ v ∈ I, y v = 0) → ψ (LinearMap.inr F (Ainf F) (Af F) (intFin y)) = 1 := by
  let ι : (∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) → AF F := fun y =>
    LinearMap.inr F (Ainf F) (Af F) (intFin y)
  have hι : Continuous ι := continuous_const.prodMk continuous_intFin
  have hopen : IsOpen {y | ‖ψ (ι y) - 1‖ < 1 / 2} :=
    isOpen_lt ((hψ.comp hι).sub continuous_const).norm continuous_const
  have h0 : (0 : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) ∈ {y | ‖ψ (ι y) - 1‖ < 1 / 2} := by
    have : ι 0 = 0 := by
      have h : intFin (0 : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) = 0 := by
        simpa using intFin_nsmul (F := F) 0 0
      show LinearMap.inr F (Ainf F) (Af F) (intFin 0) = (0 : AF F)
      rw [h, map_zero]
      rfl
    simp [this, AddChar.map_zero_eq_one]
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hopen 0 h0
  refine ⟨I, fun y hy => GlobalTheory.eq_one_of_forall_norm_pow_sub_one_lt _ fun n => ?_⟩
  have hmem : n • y ∈ (I : Set _).pi u := by
    intro a ha
    have : (n • y) a = 0 := by rw [Pi.smul_apply, hy a ha, smul_zero]
    rw [this]; exact (hu a ha).2
  have e : (ι (n • y) : AF F) = n • (ι y : AF F) := by
    show LinearMap.inr F (Ainf F) (Af F) (intFin (n • y)) = _
    rw [intFin_nsmul, map_nsmul]
    rfl
  have h := hsub hmem
  simp only [Set.mem_setOf_eq] at h
  rwa [e, AddChar.map_nsmul_eq_pow] at h

end GlobalTheory.PsiProd

namespace GlobalTheory.PsiProd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [AddChar.map_zero_eq_one]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]`.
-/
theorem addChar_sum {A ι : Type} [AddCommMonoid A] (χ : AddChar A ℂ) (s : Finset ι) (f : ι → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/- English proof (translation)
Set `y : ∀ u : HeightOneSpectrum (𝓞 F), ↥(u.adicCompletionIntegers F)` to `Pi.single v ⟨a, ha⟩`. Establish `hy : ∀ u ∈ I, y u = 0` using `fun u hu => Pi.single_eq_of_ne (by rintro rfl; exact hv hu) _`. Establish `hfin : intFin y = GlobalTheory.AdelicU.singleFin v a`. Use `GlobalTheory.AdelicU.af_ext fun w => ?_` and prove the remaining obligations. Rewrite using `[evalV_intFin]`.

Distinguish the cases in `e : w = v`. Substitute `e` using the available equality. Rewrite using `[GlobalTheory.AdelicU.evalV_singleFin_self]`. Simplify using `[y]`. Rewrite using `[GlobalTheory.AdelicU.evalV_singleFin_ne e]`.

Simplify using `[y, Pi.single_eq_of_ne e]`. Use `hI y hy` as an intermediate fact. Rewrite `this` using `[hfin]`. Conclude with `this`.
-/
theorem psiAt_eq_one_of_integral {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (I : Finset (HeightOneSpectrum (𝓞 F)))
    (hI : ∀ y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F),
      (∀ v ∈ I, y v = 0) → ψ (LinearMap.inr F (Ainf F) (Af F) (intFin y)) = 1)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ I) (a : Fv F v) (ha : a ∈ v.adicCompletionIntegers F) :
    GlobalTheory.LatVac.psiAt ψ v a = 1 := by
  classical
  let y : ∀ u : HeightOneSpectrum (𝓞 F), ↥(u.adicCompletionIntegers F) := Pi.single v ⟨a, ha⟩
  have hy : ∀ u ∈ I, y u = 0 := fun u hu => Pi.single_eq_of_ne (by rintro rfl; exact hv hu) _
  have hfin : intFin y = GlobalTheory.AdelicU.singleFin v a := by
    refine GlobalTheory.AdelicU.af_ext fun w => ?_
    rw [evalV_intFin]
    by_cases e : w = v
    · subst e
      rw [GlobalTheory.AdelicU.evalV_singleFin_self]
      simp [y]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne e]
      simp [y, Pi.single_eq_of_ne e]
  have := hI y hy
  rw [hfin] at this
  exact this

/- English proof (translation)
Introduce `F _ _ ψ hψ x`. Take `⟨I, hI⟩` from `exists_finset_trivial ψ hψ`. Use `set xf : Af F := sndA F x with hxf`. Establish `hT : {v : HeightOneSpectrum (𝓞 F) | evalV F v xf ∉ v.adicCompletionIntegers F}.Finite` using `Filter.eventually_cofinite.1 xf.2`. Set `S : Finset (HeightOneSpectrum (𝓞 F))` to `I ∪ hT.toFinset`.

Establish `hev : ∀ v, evFin F v x = evalV F v xf` using `fun v => rfl`. Establish `hsupp : (Function.mulSupport fun v : Pl F => GlobalTheory.LatVac.psiAt ψ v (evFin F v x)) ⊆ (S : Set _)`. Introduce `v hv`. Assume the negation of the conclusion as `hvS`. Apply `hv` to reduce the goal to its premises.

Simplify using `only [S, Finset.coe_union, Set.mem_union, Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or, not_not] at hvS`. Use `show GlobalTheory.LatVac.psiAt ψ v (evFin F v x) = 1`. Rewrite using `[hev]`. Conclude with `psiAt_eq_one_of_integral ψ I hI v hvS.1 _ hvS.2`. Use `⟨(S.finite_toSet).subset hsupp, ?_⟩` and prove the remaining obligations.

Set `j : Af F →ₗ[F] AF F` to `LinearMap.inr F (Ainf F) (Af F)`. Set `χ : AddChar (Af F) ℂ` to `ψ.compAddMonoidHom j.toAddMonoidHom`. Establish `hχ : ∀ a, χ a = ψ (j a)` using `fun a => rfl`. Establish `hloc : ∀ v (a : Fv F v), GlobalTheory.LatVac.psiAt ψ v a = χ (GlobalTheory.AdelicU.singleFin v a)` using `fun v a => rfl`. Establish `hx : x = pairA F (fstA F x) 0 + j xf`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show x.1 = x.1 + (0 : Ainf F)`. Rewrite using `[add_zero]`. Use `show x.2 = (0 : Af F) + x.2`. Rewrite using `[zero_add]`.

Set `r : ∀ w : HeightOneSpectrum (𝓞 F), ↥(w.adicCompletionIntegers F)` to `fun w => if hw : w ∈ S then 0 else ⟨evalV F w xf, by`. Establish `: w ∉ hT.toFinset` using `fun h => hw (Finset.mem_union_right _ h)`. Simplify using `using this⟩`. Establish `hr : ∀ v ∈ I, r v = 0` using `fun v hv => dif_pos (Finset.mem_union_left _ hv)`. Establish `hdec : xf = ∑ v ∈ S, GlobalTheory.AdelicU.singleFin v (evalV F v xf) + intFin r`.

Use `GlobalTheory.AdelicU.af_ext fun w => ?_` and prove the remaining obligations. Rewrite using `[map_add, map_sum, evalV_intFin]`. Distinguish the cases in `hw : w ∈ S`. Rewrite using `[Finset.sum_eq_single w (fun b _ hb => GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hb) _) (fun h => absurd hw h), GlobalTheory.AdelicU.evalV_singleFin_self]`. Simplify using `[r, hw]`.

Rewrite using `[Finset.sum_eq_zero (fun b hb => GlobalTheory.AdelicU.evalV_singleFin_ne (by rintro rfl; exact hw hb) _)]`. Simplify using `[r, hw]`. Establish `hrr : χ (intFin r) = 1` using `hI r hr`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset _ hsupp]`. Use `conv_lhs => rw [hx]`.

Rewrite using `[AddChar.map_add_eq_mul]`. Use `congr 1`. Rewrite using `[← hχ, hdec, AddChar.map_add_eq_mul, hrr, mul_one, addChar_sum]`. Conclude with `Finset.prod_congr rfl fun v _ => by rw [hloc, hev]`.
-/
theorem psi_prod : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ x : AF F,
    (Function.mulSupport fun v : Pl F => GlobalTheory.LatVac.psiAt ψ v (evFin F v x)).Finite ∧
    ψ x = ψ (pairA F (fstA F x) 0) * ∏ᶠ v : Pl F, GlobalTheory.LatVac.psiAt ψ v (evFin F v x) := by
  intro F _ _ ψ hψ x
  classical
  obtain ⟨I, hI⟩ := exists_finset_trivial ψ hψ
  set xf : Af F := sndA F x with hxf
  have hT : {v : HeightOneSpectrum (𝓞 F) | evalV F v xf ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 xf.2
  let S : Finset (HeightOneSpectrum (𝓞 F)) := I ∪ hT.toFinset
  have hev : ∀ v, evFin F v x = evalV F v xf := fun v => rfl
  have hsupp : (Function.mulSupport fun v : Pl F => GlobalTheory.LatVac.psiAt ψ v (evFin F v x)) ⊆ (S : Set _) := by
    intro v hv
    by_contra hvS
    apply hv
    simp only [S, Finset.coe_union, Set.mem_union, Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
      not_or, not_not] at hvS
    show GlobalTheory.LatVac.psiAt ψ v (evFin F v x) = 1
    rw [hev]
    exact psiAt_eq_one_of_integral ψ I hI v hvS.1 _ hvS.2
  refine ⟨(S.finite_toSet).subset hsupp, ?_⟩
  let j : Af F →ₗ[F] AF F := LinearMap.inr F (Ainf F) (Af F)
  let χ : AddChar (Af F) ℂ := ψ.compAddMonoidHom j.toAddMonoidHom
  have hχ : ∀ a, χ a = ψ (j a) := fun a => rfl
  have hloc : ∀ v (a : Fv F v), GlobalTheory.LatVac.psiAt ψ v a = χ (GlobalTheory.AdelicU.singleFin v a) := fun v a => rfl
  have hx : x = pairA F (fstA F x) 0 + j xf := by
    refine Prod.ext ?_ ?_
    · show x.1 = x.1 + (0 : Ainf F)
      rw [add_zero]
    · show x.2 = (0 : Af F) + x.2
      rw [zero_add]
  let r : ∀ w : HeightOneSpectrum (𝓞 F), ↥(w.adicCompletionIntegers F) := fun w =>
    if hw : w ∈ S then 0 else ⟨evalV F w xf, by
      have : w ∉ hT.toFinset := fun h => hw (Finset.mem_union_right _ h)
      simpa using this⟩
  have hr : ∀ v ∈ I, r v = 0 := fun v hv => dif_pos (Finset.mem_union_left _ hv)
  have hdec : xf = ∑ v ∈ S, GlobalTheory.AdelicU.singleFin v (evalV F v xf) + intFin r := by
    refine GlobalTheory.AdelicU.af_ext fun w => ?_
    rw [map_add, map_sum, evalV_intFin]
    by_cases hw : w ∈ S
    · rw [Finset.sum_eq_single w (fun b _ hb => GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hb) _)
        (fun h => absurd hw h), GlobalTheory.AdelicU.evalV_singleFin_self]
      simp [r, hw]
    · rw [Finset.sum_eq_zero (fun b hb => GlobalTheory.AdelicU.evalV_singleFin_ne (by rintro rfl; exact hw hb) _)]
      simp [r, hw]
  have hrr : χ (intFin r) = 1 := hI r hr
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  conv_lhs => rw [hx]
  rw [AddChar.map_add_eq_mul]
  congr 1
  rw [← hχ, hdec, AddChar.map_add_eq_mul, hrr, mul_one, addChar_sum]
  exact Finset.prod_congr rfl fun v _ => by rw [hloc, hev]

end GlobalTheory.PsiProd
