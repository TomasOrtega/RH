import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotSmIndCongr

open NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LFun.SphComp

/- English proof (translation)
Introduce `E _ _ _ m π w B hB σ hσ`. Take `⟨f, hf0, hf⟩` from `hσ`. Take `⟨x, hx⟩` from `hB.exists_vec`. Establish `hinj : Function.Injective f`. Rewrite using `[← LinearMap.ker_eq_bot]`.

Use `(((GlobalTheory.CuspRep.isIrreducible_iff σ.ρ).1 σ.irred).2 _ fun g u hu => ?_).resolve_right fun h => hf0 ?_` and prove the remaining obligations. Rewrite `hu`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[hf, hu, map_zero]`. Conclude with `LinearMap.ext fun u => by`. Establish `: u ∈ LinearMap.ker f` using `h ▸ Submodule.mem_top`.

Simplify using `using this`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv0, hvK⟩ : ∃ v : σ.V, v ≠ 0 ∧ ∀ k ∈ (GlobalTheory.LFun.KGL w m : Set _), σ.ρ k v = v := by`. Use `GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup ((GlobalTheory.CuspRep.finRep E m).comp (GlobalTheory.CuspRep.locGL E m w)) σ.ρ σ.irred (fun i : GlobalTheory.CuspRep.LocSph.Maps π w σ => i.1) (fun i g u => i.2.2 g u) _ (x : GlobalTheory.CuspRep.Sm E m) (fun h => hx.1 (Subtyp …` and prove the remaining obligations. Conclude with `congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk)`. Rewrite using `[GlobalTheory.CuspRep.LocSph.iSup_range_eq π w σ ⟨f, hf0, hf⟩]`.

Conclude with `x.2`. Establish `hfv : f v ≠ 0` using `fun h => hv0 (hinj (h.trans (map_zero f).symm))`. Establish `hs : GlobalTheory.LFun.IsSatVecGL w σ.ρ v B` using `GlobalTheory.LFun.IsSatVecGL.of_map f hf hinj (hB.2 _ (GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← hf, hvK k hk]) hfv)`. Conclude with `(GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ (Fin m) σ.V σ.ρ B).1 (GlobalTheory.LFun.SatCompare.hasSatakeGL_of_isSatVecGL ⟨σ.smooth, σ.irred⟩ hs)`.
-/
theorem hasSatake_of_isLocComp : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ} (π : GlobalTheory.CuspRep.CuspSub E m) {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}, GlobalTheory.LFun.HasSatGL w (π.locRep w) B → ∀ {σ : GlobalTheory.CuspRep.SmIrr (GL (Fin m) (w.adicCompletion E))}, π.IsLocComp w σ → ∃ α : Fin m → ℂˣ, Finset.univ.val.map α = B ∧ GlobalTheory.SmGL.HasSatake σ.ρ α := by
  intro E _ _ _ m π w B hB σ hσ
  obtain ⟨f, hf0, hf⟩ := hσ
  obtain ⟨x, hx⟩ := hB.exists_vec

  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    refine (((GlobalTheory.CuspRep.isIrreducible_iff σ.ρ).1 σ.irred).2 _ fun g u hu => ?_).resolve_right fun h => hf0 ?_
    · rw [LinearMap.mem_ker] at hu ⊢; rw [hf, hu, map_zero]
    · exact LinearMap.ext fun u => by
        have : u ∈ LinearMap.ker f := h ▸ Submodule.mem_top
        simpa using this

  obtain ⟨v, hv0, hvK⟩ : ∃ v : σ.V, v ≠ 0 ∧ ∀ k ∈ (GlobalTheory.LFun.KGL w m : Set _), σ.ρ k v = v := by
    refine GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup ((GlobalTheory.CuspRep.finRep E m).comp (GlobalTheory.CuspRep.locGL E m w)) σ.ρ
      σ.irred (fun i : GlobalTheory.CuspRep.LocSph.Maps π w σ => i.1) (fun i g u => i.2.2 g u) _ (x : GlobalTheory.CuspRep.Sm E m)
      (fun h => hx.1 (Subtype.ext h)) (fun k hk => ?_) ?_
    · exact congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk)
    · rw [GlobalTheory.CuspRep.LocSph.iSup_range_eq π w σ ⟨f, hf0, hf⟩]; exact x.2
  have hfv : f v ≠ 0 := fun h => hv0 (hinj (h.trans (map_zero f).symm))
  have hs : GlobalTheory.LFun.IsSatVecGL w σ.ρ v B := GlobalTheory.LFun.IsSatVecGL.of_map f hf hinj
    (hB.2 _ (GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← hf, hvK k hk]) hfv)
  exact (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ (Fin m) σ.V σ.ρ B).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_of_isSatVecGL ⟨σ.smooth, σ.irred⟩ hs)

end GlobalTheory.LFun.SphComp
