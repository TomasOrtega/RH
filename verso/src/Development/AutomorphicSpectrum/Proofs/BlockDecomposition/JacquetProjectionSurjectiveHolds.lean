import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionHeckeHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetVectorLiftDominantStatement

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

/- English proof (translation)
Introduce `G _ _ _ D V _ _ π hadm t ht U hU w hw`. Establish `hA2` using `GlobalTheory.T.jacquet_projection_hecke_holds G D V π hadm.1 t ht.1 U hU`. Take `⟨j, v₀, hv₀⟩` from `GlobalTheory.T.jacquet_vector_lift_dominant G D V π hadm.1 t ht w hw`. Use `haveI : FiniteDimensional ℂ (fixed π D.J) := hadm.2 D.J D.isOpen_J D.isCompact_J`. Set `L : fixed π D.J →ₗ[ℂ] Jacquet π D.N` to `(Submodule.mkQ _).comp (Submodule.subtype _)`.

Establish `hL : ∀ v : fixed π D.J, L v = D.proj π (v : V)` using `fun _ => rfl`. Set `I : Submodule ℂ (Jacquet π D.N)` to `LinearMap.range L`. Use `haveI : FiniteDimensional ℂ I := LinearMap.finiteDimensional_range L`. Set `A : Module.End ℂ (Jacquet π D.N)` to `D.piN π t`. Establish `hinj : Function.Injective A`.

Introduce `x y hxy`. Establish `h : ∀ z, D.piN π t⁻¹ (A z) = z`. Introduce `z`. Express the relevant statement in the definitionally equal form `D.piN π t⁻¹ (D.piN π t z) = z`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`.

Simplify using the standard rewrite rules. Rewrite using `[← h x, ← h y, hxy]`. Establish `hmaps : ∀ x ∈ I, A x ∈ I`. Introduce and unpack `_ ⟨v, rfl⟩`. Conclude with `⟨U v, by rw [hL, hL]; exact hA2 v⟩`.

Set `A' : I →ₗ[ℂ] I` to `A.restrict hmaps`. Establish `hinj' : Function.Injective A'`. Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises.

Conclude with `congrArg Subtype.val hxy`. Establish `hsurj : Function.Surjective A'` using `LinearMap.injective_iff_surjective.1 hinj'`. Establish `hback : ∀ x, A x ∈ I → x ∈ I`. Introduce `x hx`. Take `⟨i, hi⟩` from `hsurj ⟨A x, hx⟩`.

Establish `: A (i : Jacquet π D.N) = A x` using `congrArg Subtype.val hi`. Rewrite using `[← hinj this]`. Conclude with `i.2`. Establish `hpow : ∀ (n : ℕ) x, D.piN π (t ^ n) x ∈ I → x ∈ I`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => intro x hx`. Simplify using `using hx`. Consider the case `succ n ih`. Introduce `x hx`.

Apply `ih` to reduce the goal to its premises. Apply `hback` to reduce the goal to its premises. Rewrite `hx` using `[pow_succ', map_mul, Module.End.mul_apply]`. Conclude with `hx`. Take `⟨v, hv⟩` from `hpow j w ⟨v₀, by rw [hL]; exact hv₀⟩`.

Conclude with `⟨v, by rw [← hL]; exact hv⟩`.
-/
theorem jacquet_projection_surjective : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G), ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π → ∀ t : D.T, D.IsStrDom t → ∀ U : Module.End ℂ (fixed π D.J), PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U → ∀ w ∈ fixed (D.piN π) D.JT, ∃ v : fixed π D.J, D.proj π (v : V) = w := by
  intro G _ _ _ D V _ _ π hadm t ht U hU w hw
  have hA2 := GlobalTheory.T.jacquet_projection_hecke_holds G D V π hadm.1 t ht.1 U hU
  obtain ⟨j, v₀, hv₀⟩ := GlobalTheory.T.jacquet_vector_lift_dominant G D V π hadm.1 t ht w hw
  haveI : FiniteDimensional ℂ (fixed π D.J) := hadm.2 D.J D.isOpen_J D.isCompact_J
  let L : fixed π D.J →ₗ[ℂ] Jacquet π D.N := (Submodule.mkQ _).comp (Submodule.subtype _)
  have hL : ∀ v : fixed π D.J, L v = D.proj π (v : V) := fun _ => rfl
  let I : Submodule ℂ (Jacquet π D.N) := LinearMap.range L
  haveI : FiniteDimensional ℂ I := LinearMap.finiteDimensional_range L
  let A : Module.End ℂ (Jacquet π D.N) := D.piN π t
  have hinj : Function.Injective A := by
    intro x y hxy
    have h : ∀ z, D.piN π t⁻¹ (A z) = z := by
      intro z
      change D.piN π t⁻¹ (D.piN π t z) = z
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [← h x, ← h y, hxy]
  have hmaps : ∀ x ∈ I, A x ∈ I := by
    rintro _ ⟨v, rfl⟩
    exact ⟨U v, by rw [hL, hL]; exact hA2 v⟩
  let A' : I →ₗ[ℂ] I := A.restrict hmaps
  have hinj' : Function.Injective A' := by
    intro x y hxy
    apply Subtype.ext
    apply hinj
    exact congrArg Subtype.val hxy
  have hsurj : Function.Surjective A' := LinearMap.injective_iff_surjective.1 hinj'
  have hback : ∀ x, A x ∈ I → x ∈ I := by
    intro x hx
    obtain ⟨i, hi⟩ := hsurj ⟨A x, hx⟩
    have : A (i : Jacquet π D.N) = A x := congrArg Subtype.val hi
    rw [← hinj this]
    exact i.2
  have hpow : ∀ (n : ℕ) x, D.piN π (t ^ n) x ∈ I → x ∈ I := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      apply ih
      apply hback
      rw [pow_succ', map_mul, Module.End.mul_apply] at hx
      exact hx
  obtain ⟨v, hv⟩ := hpow j w ⟨v₀, by rw [hL]; exact hv₀⟩
  exact ⟨v, by rw [← hL]; exact hv⟩

end GlobalTheory.CompanionTheory.Cass
