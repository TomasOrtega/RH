import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RatPtsEquiv

/- English proof (translation)
Introduce `D V n hn`. Substitute `hn` using the available equality. Establish `hinj : Function.Injective (incA D)` using `Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)`. Establish `hm : ∀ δ : ↥(UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr rfl) (finCongr rfl))), bc (incA D) δ.1 ∈ HR (AF D.host.F) D.sp.cm.sig V.gram`. Introduce `δ`.

Establish `hδ' : cT (sigD D : D.host.E →+* D.host.E) δ.1.1 * V.gram * δ.1.1 = V.gram` using `δ.2`. Establish `h2` using `congrArg (fun M => M.map (incA D)) hδ'`. Simplify using `only [Matrix.map_mul] at h2`. Conclude with `h2`. Set `φ : ↥(UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr rfl) (finCongr rfl))) →* ↥(GQ V)` to `{ toFun := fun δ => ⟨⟨bc (incA D) δ.1, hm δ⟩, Subgroup.mem_subgroupOf.2 ⟨δ.1, δ.2, rfl⟩⟩ map_one' := by`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `map_one (bc (incA D))`. Use the proof step `map_mul' := by`. Introduce `a b`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `map_mul (bc (incA D)) a.1 b.1 }`. Establish `hφ : Function.Bijective φ`. Prove the components needed by the constructor for the conclusion.

Introduce `a b h`. Establish `h1 : (bc (incA D) a.1 : GL (Fin V.rank) _) = bc (incA D) b.1` using `congrArg (fun x => x.1.1) h`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Use `congrArg (fun x : GL (Fin V.rank) _ => x.1 i j) h1` as an intermediate fact. Conclude with `hinj this`. Introduce `γ`. Take `⟨δ, hδ, e⟩` from `Subgroup.mem_subgroupOf.1 γ.2`. Conclude with `⟨⟨δ, hδ⟩, Subtype.ext (Subtype.ext e)⟩`.

Use `⟨(MulEquiv.ofBijective φ hφ).symm, fun γ => ?_⟩` and prove the remaining obligations. Use `set δ := (MulEquiv.ofBijective φ hφ).symm γ with hδ`. Establish `hγ : γ = φ δ`. Rewrite using `[hδ]`. Conclude with `((MulEquiv.ofBijective φ hφ).apply_symm_apply γ).symm`.

Rewrite using `[hγ]`. Simplify using `only [finM, finCongr_refl, Matrix.reindex_refl_refl]`. Both sides reduce to the same expression.
-/
theorem rat_equiv : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n), ∃ r : ↥(GQ V) ≃* ↥(UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn))), ∀ γ, finM V hn γ.1 = (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (r γ).1).1 := by
  intro D V n hn
  subst hn
  have hinj : Function.Injective (incA D) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
  have hm : ∀ δ : ↥(UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr rfl) (finCongr rfl))),
      bc (incA D) δ.1 ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    intro δ
    have hδ' : cT (sigD D : D.host.E →+* D.host.E) δ.1.1 * V.gram * δ.1.1 = V.gram := δ.2
    have h2 := congrArg (fun M => M.map (incA D)) hδ'
    simp only [Matrix.map_mul] at h2
    exact h2
  let φ : ↥(UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr rfl) (finCongr rfl))) →* ↥(GQ V) :=
    { toFun := fun δ => ⟨⟨bc (incA D) δ.1, hm δ⟩, Subgroup.mem_subgroupOf.2 ⟨δ.1, δ.2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext
        exact map_one (bc (incA D))
      map_mul' := by
        intro a b
        apply Subtype.ext; apply Subtype.ext
        exact map_mul (bc (incA D)) a.1 b.1 }
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b h
      have h1 : (bc (incA D) a.1 : GL (Fin V.rank) _) = bc (incA D) b.1 := congrArg (fun x => x.1.1) h
      apply Subtype.ext; apply Units.ext
      refine Matrix.ext fun i j => ?_
      have := congrArg (fun x : GL (Fin V.rank) _ => x.1 i j) h1
      exact hinj this
    · intro γ
      obtain ⟨δ, hδ, e⟩ := Subgroup.mem_subgroupOf.1 γ.2
      exact ⟨⟨δ, hδ⟩, Subtype.ext (Subtype.ext e)⟩
  refine ⟨(MulEquiv.ofBijective φ hφ).symm, fun γ => ?_⟩
  set δ := (MulEquiv.ofBijective φ hφ).symm γ with hδ
  have hγ : γ = φ δ := by
    rw [hδ]; exact ((MulEquiv.ofBijective φ hφ).apply_symm_apply γ).symm
  rw [hγ]
  simp only [finM, finCongr_refl, Matrix.reindex_refl_refl]
  rfl

end GlobalTheory.RatPtsEquiv
