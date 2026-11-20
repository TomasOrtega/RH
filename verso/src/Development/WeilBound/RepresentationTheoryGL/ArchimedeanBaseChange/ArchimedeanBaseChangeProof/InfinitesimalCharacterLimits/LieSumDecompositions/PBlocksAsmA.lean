import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksCapE

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

/- English proof (translation)
Set `f` to `T ∘ₗ U.subtype`. Set `g` to `T' ∘ₗ U.subtype`. Establish `hle : LinearMap.ker f ≤ LinearMap.ker g` using `fun x hx => h x.1 x.2 hx`. Set `g₀` to `(LinearMap.ker f).liftQ g hle`. Set `h₀ : LinearMap.range f →ₗ[ℂ] N` to `g₀ ∘ₗ f.quotKerEquivRange.symm.toLinearMap`.

Take `⟨P, hP⟩` from `LinearMap.exists_extend h₀`. Use `⟨P, fun ψ hψ => ?_⟩` and prove the remaining obligations. Establish `e1 : P (T ψ) = h₀ ⟨f ⟨ψ, hψ⟩, LinearMap.mem_range_self f _⟩` using `LinearMap.congr_fun hP (⟨f ⟨ψ, hψ⟩, LinearMap.mem_range_self f _⟩ : LinearMap.range f)`. Rewrite using `[e1]`. Express the relevant statement in the definitionally equal form `g₀ (f.quotKerEquivRange.symm ⟨f ⟨ψ, hψ⟩, _⟩) = _`.

Rewrite using `[LinearMap.quotKerEquivRange_symm_apply_image]`. Both sides reduce to the same expression.
-/
theorem factor {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (U : Submodule ℂ M)
    (T : M →ₗ[ℂ] N) (T' : M →ₗ[ℂ] N) (h : ∀ ψ ∈ U, T ψ = 0 → T' ψ = 0) :
    ∃ P : N →ₗ[ℂ] N, ∀ ψ ∈ U, P (T ψ) = T' ψ := by
  let f := T ∘ₗ U.subtype
  let g := T' ∘ₗ U.subtype
  have hle : LinearMap.ker f ≤ LinearMap.ker g := fun x hx => h x.1 x.2 hx
  let g₀ := (LinearMap.ker f).liftQ g hle
  let h₀ : LinearMap.range f →ₗ[ℂ] N := g₀ ∘ₗ f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨P, hP⟩ := LinearMap.exists_extend h₀
  refine ⟨P, fun ψ hψ => ?_⟩
  have e1 : P (T ψ) = h₀ ⟨f ⟨ψ, hψ⟩, LinearMap.mem_range_self f _⟩ :=
    LinearMap.congr_fun hP (⟨f ⟨ψ, hψ⟩, LinearMap.mem_range_self f _⟩ : LinearMap.range f)
  rw [e1]
  change g₀ (f.quotKerEquivRange.symm ⟨f ⟨ψ, hψ⟩, _⟩) = _
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ}

/- English proof (translation)
Use `Subtype.ext (funext fun x => ?_)` and prove the remaining obligations. Take `⟨u, m, k, g, rfl⟩` from `ParabolicProjection.exists_decomp x`. Rewrite using `[mul_assoc, h₁, h₂]`. Conclude with `h k g m`.
-/
theorem eq_of_levi {F₁ F₂ : Sm E (r + s)}
    (h₁ : ∀ (x : BlockIx (r + s) r → Ad E) g, F₁.1 (unip x * g) = F₁.1 g)
    (h₂ : ∀ (x : BlockIx (r + s) r → Ad E) g, F₂.1 (unip x * g) = F₂.1 g)
    (h : ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m : GA E r × GA E s),
      F₁.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
        F₂.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) : F₁ = F₂ := by
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨u, m, k, g, rfl⟩ := ParabolicProjection.exists_decomp x
  rw [mul_assoc, h₁, h₂]
  exact h k g m

/- English proof (translation)
The claim follows from `eq_of_levi hF (fun _ _ => rfl) h`.
-/
theorem eq_zero_of_levi {F : Sm E (r + s)} (hF : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g)
    (h : ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m : GA E r × GA E s),
      F.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) = 0) : F = 0 :=
  eq_of_levi hF (fun _ _ => rfl) h

/- English proof (translation)
Introduce and unpack `o _ ⟨φ, hφ, rfl⟩`. Conclude with `⟨act o φ, hL o φ hφ, by`. Express the relevant statement in the definitionally equal form `z (act o φ) = act o (z φ)`. Rewrite using `[← Module.End.mul_apply, (hz o).eq, Module.End.mul_apply]⟩`.
-/
theorem isStable_map {a : ℕ} {L : Submodule ℂ (Sm E a)} (hL : IsStable L) {z : Module.End ℂ (Sm E a)}
    (hz : ∀ o : Op E a, Commute z (act o)) : IsStable (L.map z) := by
  rintro o _ ⟨φ, hφ, rfl⟩
  exact ⟨act o φ, hL o φ hφ, by
    change z (act o φ) = act o (z φ)
    rw [← Module.End.mul_apply, (hz o).eq, Module.End.mul_apply]⟩

/- English proof (translation)
Use `⟨S₁.image z, fun x hx => ?_, fun W hW hSW => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hx)`. Conclude with `Submodule.mem_map_of_mem (hS₁ hy)`. Establish `hst : IsStable (W.comap z)` using `fun o φ hφ => by`. Express the relevant statement in the definitionally equal form `z (act o φ) ∈ W`.

Rewrite using `[← Module.End.mul_apply, (hz o).eq, Module.End.mul_apply]`. Conclude with `hW o _ hφ`. Establish `hle` using `hgen (W.comap z) hst fun y hy => hSW (Finset.mem_coe.2 (Finset.mem_image_of_mem z hy))`. Introduce and unpack `_ ⟨φ, hφ, rfl⟩`. Conclude with `hle hφ`.
-/
theorem finGen_map {a : ℕ} {L : Submodule ℂ (Sm E a)} {z : Module.End ℂ (Sm E a)}
    (hz : ∀ o : Op E a, Commute z (act o)) (S₁ : Finset (Sm E a)) (hS₁ : (↑S₁ : Set (Sm E a)) ⊆ L)
    (hgen : ∀ W : Submodule ℂ (Sm E a), IsStable W → (↑S₁ : Set (Sm E a)) ⊆ W → L ≤ W) : FinGen (L.map z) := by
  classical
  refine ⟨S₁.image z, fun x hx => ?_, fun W hW hSW => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    exact Submodule.mem_map_of_mem (hS₁ hy)
  · have hst : IsStable (W.comap z) := fun o φ hφ => by
      change z (act o φ) ∈ W
      rw [← Module.End.mul_apply, (hz o).eq, Module.End.mul_apply]
      exact hW o _ hφ
    have hle := hgen (W.comap z) hst fun y hy => hSW (Finset.mem_coe.2 (Finset.mem_image_of_mem z hy))
    rintro _ ⟨φ, hφ, rfl⟩
    exact hle hφ

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

end
