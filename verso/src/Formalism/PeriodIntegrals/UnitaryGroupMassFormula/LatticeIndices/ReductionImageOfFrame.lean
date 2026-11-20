import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImABwdEps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicImageOfResidueFrame

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def StFrameA (p : TypX X) : Prop :=
  ∃ π : Op X p →+* ZMod (gOf p), Function.Surjective π ∧
    RingHom.ker π = Ideal.span {((gOf p : ℕ) : Op X p)} ∧
  ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧
    ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
      (∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
        - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p) ∧
      ∃ c, ∀ x : K, LocCong X p x ↔
        (glRed π c)⁻¹ * glRed π (ψ x) * glRed π c ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k

/- English proof (translation)
Take `⟨π, hπ, hker, K, hKc, ψ, hψ, hP, c, hc⟩` from `h`. Establish `: Fact (gOf p).Prime` using `⟨gOf_prime X p⟩`. Use `set ρ₀ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)) := (MulAut.conj (glRed π c)⁻¹).toMonoidHom.comp ((glRed π).comp ψ) with hρ₀`. Establish `hval : ∀ x : K, ρ₀ x = (glRed π c)⁻¹ * glRed π (ψ x) * glRed π c`. Introduce `x`.

Simplify using `[hρ₀]`. Establish `hk₀ : ∀ x : K, ρ₀ x = 1 ↔ (x : HAp X p) ∈ KgX X p`. Introduce `x`. Rewrite using `[hρ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, MonoidHom.comp_apply, glRed_eq_one_iff, hker]`. Conclude with `hP x`.

Establish `hon : Function.Surjective ρ₀`. Establish `h` using `(MulEquiv.surjective (MulAut.conj (glRed π c)⁻¹)).comp ((glRed_surjective π hπ (isUnit_of_map π hπ)).comp hψ)`. Conclude with `h`. Use `⟨K, hKc, ρ₀, hon, hk₀, (nuG (ZMod (gOf p)) D.R.rS D.R.k).comap ρ₀, ?_, ?_, 1, ?_⟩` and prove the remaining obligations. Use extensionality with `y`.

Rewrite using `[stImAloc_holds X hb p]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Use `⟨?_, (hc x).2 ((hval x) ▸ hx)⟩` and prove the remaining obligations. Rewrite using `[← hKc]`.

Conclude with `x.2`. Introduce and unpack `⟨hy, hcy⟩`. Establish `hyK : y ∈ K` using `by rw [← hKc] at hy; exact hy`. Use `⟨⟨y, hyK⟩, ?_, rfl⟩` and prove the remaining obligations. Use `show ρ₀ ⟨y, hyK⟩ ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k`.

Rewrite using `[hval]`. Conclude with `(hc ⟨y, hyK⟩).1 hcy`. Introduce `x hx show ρ₀ x ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k`. Rewrite using `[MonoidHom.mem_ker.mp hx]`. Conclude with `one_mem _`.

Rewrite using `[Subgroup.map_comap_eq_self_of_surjective hon]`. Use extensionality with `z`. Simplify using the standard rewrite rules.
-/
theorem reduction_image_of_frame (p : TypX X) (h : StFrameA X p) : LevelReductionImage X hb p := by
  obtain ⟨π, hπ, hker, K, hKc, ψ, hψ, hP, c, hc⟩ := h
  have : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  set ρ₀ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)) :=
    (MulAut.conj (glRed π c)⁻¹).toMonoidHom.comp ((glRed π).comp ψ) with hρ₀
  have hval : ∀ x : K, ρ₀ x = (glRed π c)⁻¹ * glRed π (ψ x) * glRed π c := by
    intro x; simp [hρ₀]
  have hk₀ : ∀ x : K, ρ₀ x = 1 ↔ (x : HAp X p) ∈ KgX X p := by
    intro x
    rw [hρ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      MonoidHom.comp_apply, glRed_eq_one_iff, hker]
    exact hP x
  have hon : Function.Surjective ρ₀ := by
    have h := (MulEquiv.surjective (MulAut.conj (glRed π c)⁻¹)).comp
      ((glRed_surjective π hπ (isUnit_of_map π hπ)).comp hψ)
    exact h
  refine ⟨K, hKc, ρ₀, hon, hk₀, (nuG (ZMod (gOf p)) D.R.rS D.R.k).comap ρ₀, ?_, ?_, 1, ?_⟩
  · ext y
    rw [stImAloc_holds X hb p]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, (hc x).2 ((hval x) ▸ hx)⟩
      rw [← hKc]; exact x.2
    · rintro ⟨hy, hcy⟩
      have hyK : y ∈ K := by rw [← hKc] at hy; exact hy
      refine ⟨⟨y, hyK⟩, ?_, rfl⟩
      show ρ₀ ⟨y, hyK⟩ ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k
      rw [hval]; exact (hc ⟨y, hyK⟩).1 hcy
  · intro x hx
    show ρ₀ x ∈ nuG (ZMod (gOf p)) D.R.rS D.R.k
    rw [MonoidHom.mem_ker.mp hx]; exact one_mem _
  · rw [Subgroup.map_comap_eq_self_of_surjective hon]
    ext z; simp

end MassDataIdxSteps
