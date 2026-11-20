import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelSpecTensorPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentVanishingFiniteAlgebraStatement
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

/- English proof (translation)
Take `⟨S, hS⟩` from `Module.Finite.fg_top (R := A) (M := A')`. Use `⟨⟨Finset.univ.image (fun r : ι → S => PiTensorProduct.tprod A (fun i => (r i : A'))), ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]`. Introduce and unpack `_ ⟨m, rfl⟩`. Establish `hm : ∀ i, m i ∈ Submodule.span A (S : Set A')` using `fun i => hS ▸ Submodule.mem_top`.

Use `choose c hc using fun i => (Submodule.mem_span_finset).1 (hm i)`. Establish `hm' : m = fun i => ∑ s ∈ S, c i s • s` using `funext fun i => ((hc i).2).symm`. Rewrite using `[hm', MultilinearMap.map_sum_finset]`. Use `Submodule.sum_mem _ fun r hr => ?_` and prove the remaining obligations. Rewrite using `[MultilinearMap.map_smul_univ]`.

Use `Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Rewrite using `[Finset.coe_image]`. Use `⟨fun i => ⟨r i, Fintype.mem_piFinset.1 hr i⟩, by simp, rfl⟩` and prove the remaining obligations.
-/
theorem finite_piTensorProduct_const (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Module.Finite A A']
    (ι : Type) [Fintype ι] : Module.Finite A (PiTensorProduct A fun _ : ι => A') := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := A')
  refine ⟨⟨Finset.univ.image (fun r : ι → S => PiTensorProduct.tprod A (fun i => (r i : A'))), ?_⟩⟩
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  have hm : ∀ i, m i ∈ Submodule.span A (S : Set A') := fun i => hS ▸ Submodule.mem_top
  choose c hc using fun i => (Submodule.mem_span_finset).1 (hm i)
  have hm' : m = fun i => ∑ s ∈ S, c i s • s := funext fun i => ((hc i).2).symm
  rw [hm', MultilinearMap.map_sum_finset]
  refine Submodule.sum_mem _ fun r hr => ?_
  rw [MultilinearMap.map_smul_univ]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  rw [Finset.coe_image]
  refine ⟨fun i => ⟨r i, Fintype.mem_piFinset.1 hr i⟩, by simp, rfl⟩

/- English proof (translation)
Introduce `q _ n hyp A _ _ hSH hq A' _ _ hfin k s i hs hsn`. Take `⟨_, e, -, -⟩` from `GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k`. Establish `hT` using `GlobalTheory.T.tateTwistCohomology_laurent_vanishing_finite_algebra q n hyp A hSH hq (PiTensorProduct A fun _ : Fin (k + 1) => A') (finite_piTensorProduct_const A A' (Fin (k + 1))) s i hs hsn`. Use `haveI : Subsingleton (Ht q (disc.obj (yoneda.obj (Spec (CommRingCat.of (LaurentPolynomial (PiTensorProduct A fun _ : Fin (k + 1) => A')))))) s i) := hT`. Set `f` to `disc.mapIso e`.

Establish `inj : Function.Injective (pull (ZMod q) f.hom (tw q i) s)` using `fun x y h => by`. Establish `h'` using `congrArg (pull (ZMod q) f.inv (tw q i) s) h`. Rewrite `h'` using `[← pull_comp, ← pull_comp, Iso.inv_hom_id, pull_id, pull_id]`. Then use the resulting hypothesis. Conclude with `inj.subsingleton`.
-/
theorem level_vanish : ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
  ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (s i : ℤ), 2 ≤ s → s < n →
  Subsingleton (Ht q (disc.obj ((cech (laurentHom A A')).obj (op ⦋k⦌))) s i) := by
  intro q _ n hyp A _ _ hSH hq A' _ _ hfin k s i hs hsn
  obtain ⟨_, e, -, -⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  have hT := GlobalTheory.T.tateTwistCohomology_laurent_vanishing_finite_algebra q n hyp A hSH hq (PiTensorProduct A fun _ : Fin (k + 1) => A')
    (finite_piTensorProduct_const A A' (Fin (k + 1))) s i hs hsn
  haveI : Subsingleton (Ht q (disc.obj (yoneda.obj (Spec (CommRingCat.of
    (LaurentPolynomial (PiTensorProduct A fun _ : Fin (k + 1) => A')))))) s i) := hT
  let f := disc.mapIso e
  have inj : Function.Injective (pull (ZMod q) f.hom (tw q i) s) := fun x y h => by
    have h' := congrArg (pull (ZMod q) f.inv (tw q i) s) h
    rwa [← pull_comp, ← pull_comp, Iso.inv_hom_id, pull_id, pull_id] at h'
  exact inj.subsingleton

end GlobalTheory.EtC.GmStep
