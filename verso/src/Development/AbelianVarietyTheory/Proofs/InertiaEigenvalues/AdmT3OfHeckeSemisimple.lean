import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentImageStableOfEquivariant

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.EigRed

open Formalism.MainNotions.IntegralHeckeForms

/- English proof (translation)
Introduce `D E hI hA hS hss i hi j hj b x hxB hxm ev hev`. Assume the negation of the conclusion as `hno`. Apply `hxm` to reduce the goal to its premises. Establish `hcomm` using `((hA i hi b).2 j hj).1`. Establish `hM` using `(hI i hi j hj b).2.2.2.1`.

Establish `hx` using `hss i hi j hj b hxB.2`. Take `⟨f, hf, hfx⟩` from `(Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx`. Use `mem_smul_of_sum_eigenvectors (ι := {p : ℕ × PlE D.host // HkIdx i p.1 p.2}) _ _ (fun p => hkO D.nexp i j b p.1.1 p.1.2) (fun p z hz => ?_) (fun p => ev p.1.1 p.1.2) f.support (fun a => f a) x (fun a _ => ?_) ?_ hxB (fun p => hev _ _ p.2)` and prove the remaining obligations. Conclude with `⟨hM _ _ p.2 ⟨z, hz.1, rfl⟩, idempotentImage_stable_of_equivariant D.nexp i j b _ (fun g => hcomm g _ _ p.2) z hz.2⟩`. Distinguish the cases in `h0 : f a = 0`.

Conclude with `Or.inl h0`. Use `right`. Establish `hex : eG D.nexp i j b (f a) = f a`. Take `⟨y, -, hy⟩` from `(hf a).2`. Rewrite using `[← hy, eG_idem]`.

Establish `heig : ∀ k P, HkIdx i k P → D.nexp.hkF i j b k P (f a) = a k P • f a`. Introduce `k P hk`. Establish `h1` using `(hf a).1`. Simplify using `only [Eigsp, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h1`. Conclude with `h1 k P hk`.

Take `⟨s, hs1, hs2, hs3⟩` from `hS i j b _ a h0 hex (fun k P h1 h2 h3 h4 => heig k P ⟨h1, h2, h3, h4⟩)`. Use `⟨fun p => D.ntw.hEig i s p.1.1 p.1.2, fun p => ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `D.nexp.hkF i j b _ _ _ = _`. Rewrite using `[heig _ _ p.2, ← hs3 _ _ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2, algebraMap_smul]`. Assume the negation of the conclusion as `hu`.

Use `hno ⟨s, hs1, hs2, fun k P hk => ?_⟩` and prove the remaining obligations. Conclude with `fun h => hu ⟨⟨(k, P), hk⟩, h⟩`. Conclude with `hfx.symm`.
-/
theorem admT3_of_semisimple_good : ∀ (D : D7) (E : IntegralHeckeForms.XD D), IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E → IntegralHeckeForms.GroupAlgebraIntegrality D.nexp → D.nexp.sig_all → HkSS D → IntegralHeckeForms.GoodLatticePoints D.nexp := by
  intro D E hI hA hS hss i hi j hj b x hxB hxm ev hev
  by_contra hno
  apply hxm
  have hcomm := ((hA i hi b).2 j hj).1
  have hM := (hI i hi j hj b).2.2.2.1
  have hx := hss i hi j hj b hxB.2
  obtain ⟨f, hf, hfx⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx
  refine mem_smul_of_sum_eigenvectors (ι := {p : ℕ × PlE D.host // HkIdx i p.1 p.2}) _ _
    (fun p => hkO D.nexp i j b p.1.1 p.1.2) (fun p z hz => ?_) (fun p => ev p.1.1 p.1.2) f.support
    (fun a => f a) x (fun a _ => ?_) ?_ hxB (fun p => hev _ _ p.2)
  · exact ⟨hM _ _ p.2 ⟨z, hz.1, rfl⟩, idempotentImage_stable_of_equivariant D.nexp i j b _ (fun g => hcomm g _ _ p.2) z hz.2⟩
  · by_cases h0 : f a = 0
    · exact Or.inl h0
    right
    have hex : eG D.nexp i j b (f a) = f a := by
      obtain ⟨y, -, hy⟩ := (hf a).2
      rw [← hy, eG_idem]
    have heig : ∀ k P, HkIdx i k P → D.nexp.hkF i j b k P (f a) = a k P • f a := by
      intro k P hk
      have h1 := (hf a).1
      simp only [Eigsp, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h1
      exact h1 k P hk
    obtain ⟨s, hs1, hs2, hs3⟩ := hS i j b _ a h0 hex
      (fun k P h1 h2 h3 h4 => heig k P ⟨h1, h2, h3, h4⟩)
    refine ⟨fun p => D.ntw.hEig i s p.1.1 p.1.2, fun p => ?_, ?_⟩
    · change D.nexp.hkF i j b _ _ _ = _
      rw [heig _ _ p.2, ← hs3 _ _ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2, algebraMap_smul]
    · by_contra hu
      refine hno ⟨s, hs1, hs2, fun k P hk => ?_⟩
      exact fun h => hu ⟨⟨(k, P), hk⟩, h⟩
  · exact hfx.symm

end GlobalTheory.EigRed
