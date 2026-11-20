import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducibleStatement

open CategoryTheory ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.FinRep

variable {Γ : Type} [Group Γ] [Fintype Γ]

def leftRep (N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ)) : Representation ℂ Γ N where
  toFun g :=
    { toFun := fun n => MonoidAlgebra.of ℂ Γ g • n
      map_add' := smul_add _
      map_smul' := fun c n => smul_comm _ c n }
  map_one' := by
    ext n
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro n
    change MonoidAlgebra.of ℂ Γ (g * h) • n = MonoidAlgebra.of ℂ Γ g • MonoidAlgebra.of ℂ Γ h • n
    rw [map_mul, mul_smul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem leftRep_apply (N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ)) (g : Γ) (n : N) :
    leftRep N g n = MonoidAlgebra.of ℂ Γ g • n := rfl

/- English proof (translation)
Proceed by induction on `x using MonoidAlgebra.induction_on with`. Consider the case `of g => simp [Representation.asAlgebraHom_of, leftRep_apply]`. Consider the case `add a b ha hb => simp [map_add, add_smul, ha, hb]`. Consider the case `smul c a ha => simp [map_smul, ha]`.
-/
theorem asAlgebraHom_leftRep (N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ))
    (x : MonoidAlgebra ℂ Γ) (n : N) : Representation.asAlgebraHom (leftRep N) x n = x • n := by
  induction x using MonoidAlgebra.induction_on with
  | of g => simp [Representation.asAlgebraHom_of, leftRep_apply]
  | add a b ha hb => simp [map_add, add_smul, ha, hb]
  | smul c a ha => simp [map_smul, ha]

instance finiteDimensional_leftIdeal (N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ)) :
    FiniteDimensional ℂ N :=
  inferInstanceAs (FiniteDimensional ℂ (N.restrictScalars ℂ))

/- English proof (translation)
Use `⟨IsSimpleModule.nontrivial (MonoidAlgebra ℂ Γ) N, fun W hW => ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ (x : MonoidAlgebra ℂ Γ), ∀ w ∈ W, x • w ∈ W`. Introduce `x w hw`. Rewrite using `[← asAlgebraHom_leftRep]`. Proceed by induction on `x using MonoidAlgebra.induction_on with`.

Consider the case `of g => simpa [Representation.asAlgebraHom_of] using hW g w hw`. Consider the case `add a b ha hb => simpa [map_add] using W.add_mem ha hb`. Consider the case `smul c a ha => simpa [map_smul] using W.smul_mem c ha`. Set `W' : Submodule (MonoidAlgebra ℂ Γ) N` to `{ carrier := W add_mem' := W.add_mem zero_mem' := W.zero_mem smul_mem' := fun x w hw => hmem x w hw }`. Break down `IsSimpleOrder.eq_bot_or_eq_top W' with h | h` into its components or cases.

Use `left`. Use extensionality with `w`. Use `congrArg (fun S : Submodule (MonoidAlgebra ℂ Γ) N => w ∈ S) h` as an intermediate fact. Simplify `this` using `[W']`. Use `right`.

Use extensionality with `w`. Use `congrArg (fun S : Submodule (MonoidAlgebra ℂ Γ) N => w ∈ S) h` as an intermediate fact. Simplify `this` using `[W']`.
-/
theorem isIrr_leftRep (N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ))
    [IsSimpleModule (MonoidAlgebra ℂ Γ) N] : IsIrr (leftRep N) := by
  refine ⟨IsSimpleModule.nontrivial (MonoidAlgebra ℂ Γ) N, fun W hW => ?_⟩
  have hmem : ∀ (x : MonoidAlgebra ℂ Γ), ∀ w ∈ W, x • w ∈ W := by
    intro x w hw
    rw [← asAlgebraHom_leftRep]
    induction x using MonoidAlgebra.induction_on with
    | of g => simpa [Representation.asAlgebraHom_of] using hW g w hw
    | add a b ha hb => simpa [map_add] using W.add_mem ha hb
    | smul c a ha => simpa [map_smul] using W.smul_mem c ha
  let W' : Submodule (MonoidAlgebra ℂ Γ) N :=
    { carrier := W
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := fun x w hw => hmem x w hw }
  rcases IsSimpleOrder.eq_bot_or_eq_top W' with h | h
  · left
    ext w
    have := congrArg (fun S : Submodule (MonoidAlgebra ℂ Γ) N => w ∈ S) h
    simpa [W'] using this
  · right
    ext w
    have := congrArg (fun S : Submodule (MonoidAlgebra ℂ Γ) N => w ∈ S) h
    simpa [W'] using this

/- English proof (translation)
Introduce `Γ _ _ x hx`. Establish `hsimple : ∀ N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ), IsSimpleModule (MonoidAlgebra ℂ Γ) N → ∀ n ∈ N, x * n = 0`. Introduce `N hN n hn`. Establish `hS : Simple (FDRep.of (leftRep N))` using `(GlobalTheory.T.simple_iff_irreducible.1 Γ (FDRep.of (leftRep N))).2 (by`. Simplify using `using isIrr_leftRep N)`.

Establish `h0` using `hx _ hS`. Establish `h1 : Representation.asAlgebraHom (leftRep N) x = 0`. Simplify using `using h0`. Establish `h2` using `asAlgebraHom_leftRep N x ⟨n, hn⟩`. Rewrite `h2` using `[h1]`.

Establish `h3` using `congrArg Subtype.val h2`. Simplify using `using h3.symm`. Set `J : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ)` to `{ carrier := {n | ∀ a, x * (a * n) = 0} add_mem' := fun {u v} hu hv a => by`. Rewrite using `[mul_add, mul_add, hu a, hv a, add_zero]`. Use the proof step `zero_mem' := fun a => by simp`.

Use the proof step `smul_mem' := fun c n hn a => by`. Simplify `hn (a * c) }` using `[mul_assoc]`. Establish `hJ : (⊤ : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ)) ≤ J`. Rewrite using `[← IsSemisimpleModule.sSup_simples_eq_top (R := MonoidAlgebra ℂ Γ)]`. Use `sSup_le fun N hN n hn a => ?_` and prove the remaining obligations.

Conclude with `hsimple N hN _ (by simpa using N.smul_mem a hn)`. Establish `h1 : (1 : MonoidAlgebra ℂ Γ) ∈ J` using `hJ Submodule.mem_top`. Simplify using `using h1 1`.
-/
theorem sepIrr : ReciprocityTheory.Ty.Fin.St.SepIrr := by
  intro Γ _ _ x hx
  have hsimple : ∀ N : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ),
      IsSimpleModule (MonoidAlgebra ℂ Γ) N → ∀ n ∈ N, x * n = 0 := by
    intro N hN n hn
    have hS : Simple (FDRep.of (leftRep N)) :=
      (GlobalTheory.T.simple_iff_irreducible.1 Γ (FDRep.of (leftRep N))).2 (by
        simpa using isIrr_leftRep N)
    have h0 := hx _ hS
    have h1 : Representation.asAlgebraHom (leftRep N) x = 0 := by
      simpa using h0
    have h2 := asAlgebraHom_leftRep N x ⟨n, hn⟩
    rw [h1] at h2
    have h3 := congrArg Subtype.val h2
    simpa using h3.symm
  let J : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ) :=
    { carrier := {n | ∀ a, x * (a * n) = 0}
      add_mem' := fun {u v} hu hv a => by
        rw [mul_add, mul_add, hu a, hv a, add_zero]
      zero_mem' := fun a => by simp
      smul_mem' := fun c n hn a => by
        simpa [mul_assoc] using hn (a * c) }
  have hJ : (⊤ : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ)) ≤ J := by
    rw [← IsSemisimpleModule.sSup_simples_eq_top (R := MonoidAlgebra ℂ Γ)]
    refine sSup_le fun N hN n hn a => ?_
    exact hsimple N hN _ (by simpa using N.smul_mem a hn)
  have h1 : (1 : MonoidAlgebra ℂ Γ) ∈ J := hJ Submodule.mem_top
  simpa using h1 1

end GlobalTheory.CompanionTheory.FinRep
