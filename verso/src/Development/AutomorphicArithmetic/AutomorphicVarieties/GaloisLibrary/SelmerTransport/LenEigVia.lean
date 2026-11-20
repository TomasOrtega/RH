import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenEigLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenEigEq

open ReciprocityTheory.Gal UpperTheory.V.Base

/- English proof (translation)
Introduce `O W Q N _ _ _ _ _ _ _ _ _ π p hp hfix`. Establish `hker : p.ker ≤ MonoidHom.ker π` using `fun g hg => (MonoidHom.mem_ker).mpr (LinearMap.ext (hfix g ((MonoidHom.mem_ker).mp hg)))`. Set `e` to `QuotientGroup.quotientKerEquivOfSurjective p hp`. Set `π' : Representation O Q N` to `(QuotientGroup.lift p.ker π hker).comp e.symm.toMonoidHom`. Establish `hπ' : ∀ g, π' (p g) = π g`.

Introduce `g`. Establish `he : e.symm (p g) = (g : W ⧸ p.ker)`. Rewrite using `[MulEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Use `show QuotientGroup.lift p.ker π hker (e.symm (p g)) = π g`.

Rewrite using `[he, QuotientGroup.lift_mk]`. Establish `heig : ∀ ψ : Q →* Oˣ, eig π (ψ.comp p) = eig π' ψ`. Introduce `ψ`. Use extensionality with `x`. Simplify using `only [mem_eig]`.

Prove the components needed by the constructor for the conclusion. Introduce `h q`. Take `⟨g, rfl⟩` from `hp q`. Rewrite using `[hπ']`. Conclude with `h g`.

Introduce `h g`. Rewrite using `[← hπ']`. Conclude with `h (p g)`. Establish `hsum : ∑ ψ : Q →* Oˣ, Module.length O (eig π (ψ.comp p)) = ∑ ψ : Q →* Oˣ, Module.length O (eig π' ψ)` using `Finset.sum_congr rfl fun ψ _ => congrArg (fun S : Submodule O N => Module.length O S) (heig ψ)`. Rewrite using `[hsum]`.

Conclude with `⟨lenEigLe O Q N π', fun hu => (lenEigEq O Q N π' hu).1⟩`.
-/
theorem UpperTheory.V.Base.lenEigVia :
    ∀ (O W Q N : Type) [CommRing O] [IsDomain O] [Group W] [CommGroup Q] [Finite Q] [HasEnoughRootsOfUnity O (Monoid.exponent Q)]
      [Fintype (Q →* Oˣ)] [AddCommGroup N] [Module O N] (π : Representation O W N) (p : W →* Q), Function.Surjective p →
      (∀ g, p g = 1 → ∀ x, π g x = x) →
      Module.length O N ≤ ∑ ψ : Q →* Oˣ, Module.length O (eig π (ψ.comp p)) ∧
      (IsUnit (Nat.card Q : O) → Module.length O N = ∑ ψ : Q →* Oˣ, Module.length O (eig π (ψ.comp p))) := by
  intro O W Q N _ _ _ _ _ _ _ _ _ π p hp hfix
  have hker : p.ker ≤ MonoidHom.ker π := fun g hg =>
    (MonoidHom.mem_ker).mpr (LinearMap.ext (hfix g ((MonoidHom.mem_ker).mp hg)))
  let e := QuotientGroup.quotientKerEquivOfSurjective p hp
  let π' : Representation O Q N := (QuotientGroup.lift p.ker π hker).comp e.symm.toMonoidHom
  have hπ' : ∀ g, π' (p g) = π g := by
    intro g
    have he : e.symm (p g) = (g : W ⧸ p.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift p.ker π hker (e.symm (p g)) = π g
    rw [he, QuotientGroup.lift_mk]
  have heig : ∀ ψ : Q →* Oˣ, eig π (ψ.comp p) = eig π' ψ := by
    intro ψ
    ext x
    simp only [mem_eig]
    constructor
    · intro h q
      obtain ⟨g, rfl⟩ := hp q
      rw [hπ']
      exact h g
    · intro h g
      rw [← hπ']
      exact h (p g)
  have hsum : ∑ ψ : Q →* Oˣ, Module.length O (eig π (ψ.comp p))
      = ∑ ψ : Q →* Oˣ, Module.length O (eig π' ψ) :=
    Finset.sum_congr rfl fun ψ _ =>
      congrArg (fun S : Submodule O N => Module.length O S) (heig ψ)
  rw [hsum]
  exact ⟨lenEigLe O Q N π', fun hu => (lenEigEq O Q N π' hu).1⟩
