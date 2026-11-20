import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Thick

/- English proof (translation)
Introduce `O _ R _ I γ p X q κ ι U S T`. Establish `htop : InU (⊤ : X.Opens) T` using `fun x _ => trivial`. Establish `hinf : ∀ V W : X.Opens, InU (V ⊓ W) T ↔ InU V T ∧ InU W T`. Introduce `V W`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `⟨fun x hx => (h hx).1, fun x hx => (h hx).2⟩`. Introduce `h x hx`. Conclude with `⟨h.1 hx, h.2 hx⟩`. Proceed by induction on `S using Finset.induction_on with`.

Consider the case `empty => simpa using htop`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.iInf_insert]`. Use `(hinf _ _).trans ?_` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩ α hα`. Break down `Finset.mem_insert.1 hα with rfl | hα` into its components or cases. Conclude with `h1`. Conclude with `ih.1 h2 α hα`. Introduce `h`.

Conclude with `⟨h a (Finset.mem_insert_self a s), ih.2 fun α hα => h α (Finset.mem_insert_of_mem hα)⟩`.
-/
theorem inU_iInf_finset : ∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {ι : Type} (U : ι → X.Opens) (S : Finset ι) (T : Thick (nlFun γ p X q κ)), InU (⨅ α ∈ S, U α) T ↔ ∀ α ∈ S, InU (U α) T := by
  intro O _ R _ I γ p X q κ ι U S T
  classical
  have htop : InU (⊤ : X.Opens) T := fun x _ => trivial
  have hinf : ∀ V W : X.Opens, InU (V ⊓ W) T ↔ InU V T ∧ InU W T := by
    intro V W
    constructor
    · intro h
      exact ⟨fun x hx => (h hx).1, fun x hx => (h hx).2⟩
    · intro h x hx
      exact ⟨h.1 hx, h.2 hx⟩
  induction S using Finset.induction_on with
  | empty => simpa using htop
  | insert a s ha ih =>
    rw [Finset.iInf_insert]
    refine (hinf _ _).trans ?_
    constructor
    · rintro ⟨h1, h2⟩ α hα
      rcases Finset.mem_insert.1 hα with rfl | hα
      · exact h1
      · exact ih.1 h2 α hα
    · intro h
      exact ⟨h a (Finset.mem_insert_self a s), ih.2 fun α hα => h α (Finset.mem_insert_of_mem hα)⟩

end GlobalTheory.CompanionTheory.Thick
