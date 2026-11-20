import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanEqTopOfSpanResidueEqTop

namespace GlobalTheory.TraceConjugacy

open Matrix

/- English proof (translation)
Break down `Nat.eq_zero_or_pos a with rfl | ha` into its components or cases. Conclude with `⟨1, fun x => Subsingleton.elim _ _⟩`. Take `⟨s, hs⟩` from `φ.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hφ)`. Establish `hs' : ∀ X, φ (s X) = X` using `fun X => LinearMap.congr_fun hs X`. Set `θ : Matrix (Fin a) (Fin a) O →ₗ[O] Matrix (Fin a) (Fin a) O` to `φ'.toLinearMap ∘ₗ s`.

Establish `hθ : ∀ X, θ X = φ' (s X)` using `fun X => rfl`. Set `T : Matrix (Fin a) (Fin a) O →ₗ[O] Matrix (Fin a) (Fin a) O` to `{ toFun := fun X => Matrix.of fun i j => (X * θ (Matrix.single j i 1)).trace map_add' := fun X Y => by ext i j; simp [add_mul] map_smul' := fun c X => by ext i j; simp }`. Establish `hT : ∀ x, T (φ' x) = φ x`. Introduce `x`. Use extensionality with `i j`.

Express the relevant statement in the definitionally equal form `(φ' x * θ (Matrix.single j i 1)).trace = _`. Rewrite using `[hθ, ← map_mul, ← htr, map_mul, hs', Matrix.trace_mul_single]`. Simplify using the standard rewrite rules. Establish `hTinj : Function.Injective T` using `OrzechProperty.injective_of_surjective_endomorphism T fun X => ⟨φ' (s X), by rw [hT, hs']⟩`. Establish `hfac : ∀ x, θ (φ x) = φ' x` using `fun x => hTinj (by rw [hθ, hT, hT, hs'])`.

Establish `hmul : ∀ X Y, θ X * θ Y = θ (X * Y)`. Introduce `X Y`. Rewrite using `[hθ, hθ, ← map_mul, ← hfac, map_mul, hs', hs']`. Set `o : Fin a` to `⟨0, ha⟩`. Establish `h1 : ∑ y, θ (Matrix.single o o 1) y y = 1`.

Use `htr (s (Matrix.single o o 1))` as an intermediate fact. Rewrite `this` using `[hs', Matrix.trace_single_eq_same]`. Conclude with `this.symm`. Take `⟨y, -, hy⟩` from `IsLocalRing.exists_of_isUnit_sum (show IsUnit (∑ y, θ (Matrix.single o o 1) y y) by`. Rewrite using `[h1]`.

Conclude with `isUnit_one)`. Set `U : Matrix (Fin a) (Fin a) O` to `Matrix.of fun x i => θ (Matrix.single i o 1) x y`. Set `V : Matrix (Fin a) (Fin a) O` to `Matrix.of fun j x => θ (Matrix.single o j 1) y x`. Establish `hVU : V * U = θ (Matrix.single o o 1) y y • (1 : Matrix (Fin a) (Fin a) O)`. Use extensionality with `j i`.

Establish `: (V * U) j i = (θ (Matrix.single o j 1) * θ (Matrix.single i o 1)) y y`. Simplify using `[Matrix.mul_apply, U, V]`. Rewrite using `[this, hmul]`. Distinguish the cases in `hij : j = i`. Substitute `hij` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[Matrix.single_mul_single_of_ne _ _ _ _ hij]`. Simplify using `[hij]`. Establish `hU : IsUnit U`. Rewrite using `[Matrix.isUnit_iff_isUnit_det]`.

Use `congrArg Matrix.det hVU` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one]`. Conclude with `isUnit_of_mul_isUnit_right (this ▸ hy.pow _)`. Use `⟨hU.unit, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec, ← hfac]`.

Use extensionality with `x i`. Establish `h2 : (θ (φ z) * U) x i = (θ (φ z) * θ (Matrix.single i o 1)) x y`. Simplify using `[Matrix.mul_apply, U]`. Establish `h3 : φ z * Matrix.single i o (1 : O) = ∑ k, φ z k i • Matrix.single k o (1 : O)`. Use extensionality with `p q`.

Distinguish the cases in `hq : q = o`. Substitute `hq` using the available equality. Simplify using `[Matrix.sum_apply, Matrix.single_apply]`. Rewrite using `[Matrix.mul_single_apply_of_ne _ _ _ _ _ hq]`. Simplify using `[Matrix.sum_apply, Matrix.single_apply, Ne.symm hq]`.

Rewrite using `[h2, hmul, h3, map_sum, Matrix.sum_apply, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Matrix.smul_apply, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression.
-/
theorem exists_conj_of_surjective {O A : Type} [CommRing O] [IsLocalRing O] [Ring A] [Algebra O A]
    {a : ℕ} (φ φ' : A →ₐ[O] Matrix (Fin a) (Fin a) O) (hφ : Function.Surjective φ)
    (htr : ∀ x, (φ x).trace = (φ' x).trace) :
    ∃ U : GL (Fin a) O, ∀ x, φ' x * (U : Matrix (Fin a) (Fin a) O) = U * φ x := by
  classical
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨1, fun x => Subsingleton.elim _ _⟩
  obtain ⟨s, hs⟩ := φ.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hφ)
  have hs' : ∀ X, φ (s X) = X := fun X => LinearMap.congr_fun hs X
  let θ : Matrix (Fin a) (Fin a) O →ₗ[O] Matrix (Fin a) (Fin a) O := φ'.toLinearMap ∘ₗ s
  have hθ : ∀ X, θ X = φ' (s X) := fun X => rfl
  let T : Matrix (Fin a) (Fin a) O →ₗ[O] Matrix (Fin a) (Fin a) O :=
    { toFun := fun X => Matrix.of fun i j => (X * θ (Matrix.single j i 1)).trace
      map_add' := fun X Y => by ext i j; simp [add_mul]
      map_smul' := fun c X => by ext i j; simp }
  have hT : ∀ x, T (φ' x) = φ x := by
    intro x
    ext i j
    change (φ' x * θ (Matrix.single j i 1)).trace = _
    rw [hθ, ← map_mul, ← htr, map_mul, hs', Matrix.trace_mul_single]
    simp
  have hTinj : Function.Injective T :=
    OrzechProperty.injective_of_surjective_endomorphism T fun X =>
      ⟨φ' (s X), by rw [hT, hs']⟩
  have hfac : ∀ x, θ (φ x) = φ' x := fun x => hTinj (by rw [hθ, hT, hT, hs'])
  have hmul : ∀ X Y, θ X * θ Y = θ (X * Y) := by
    intro X Y
    rw [hθ, hθ, ← map_mul, ← hfac, map_mul, hs', hs']
  let o : Fin a := ⟨0, ha⟩
  have h1 : ∑ y, θ (Matrix.single o o 1) y y = 1 := by
    have := htr (s (Matrix.single o o 1))
    rw [hs', Matrix.trace_single_eq_same] at this
    exact this.symm
  obtain ⟨y, -, hy⟩ := IsLocalRing.exists_of_isUnit_sum (show IsUnit (∑ y, θ (Matrix.single o o 1) y y) by
    rw [h1]; exact isUnit_one)
  let U : Matrix (Fin a) (Fin a) O := Matrix.of fun x i => θ (Matrix.single i o 1) x y
  let V : Matrix (Fin a) (Fin a) O := Matrix.of fun j x => θ (Matrix.single o j 1) y x
  have hVU : V * U = θ (Matrix.single o o 1) y y • (1 : Matrix (Fin a) (Fin a) O) := by
    ext j i
    have : (V * U) j i = (θ (Matrix.single o j 1) * θ (Matrix.single i o 1)) y y := by
      simp [Matrix.mul_apply, U, V]
    rw [this, hmul]
    by_cases hij : j = i
    · subst hij
      simp
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ hij]
      simp [hij]
  have hU : IsUnit U := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have := congrArg Matrix.det hVU
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
    exact isUnit_of_mul_isUnit_right (this ▸ hy.pow _)
  refine ⟨hU.unit, fun z => ?_⟩
  rw [IsUnit.unit_spec, ← hfac]
  ext x i
  have h2 : (θ (φ z) * U) x i = (θ (φ z) * θ (Matrix.single i o 1)) x y := by
    simp [Matrix.mul_apply, U]
  have h3 : φ z * Matrix.single i o (1 : O) = ∑ k, φ z k i • Matrix.single k o (1 : O) := by
    ext p q
    by_cases hq : q = o
    · subst hq
      simp [Matrix.sum_apply, Matrix.single_apply]
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hq]
      simp [Matrix.sum_apply, Matrix.single_apply, Ne.symm hq]
  rw [h2, hmul, h3, map_sum, Matrix.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Matrix.smul_apply, smul_eq_mul, mul_comm]
  rfl

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top`. Consider the case `exact _root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top`. Consider the case `(apply _root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top ..)`.
-/
theorem span_eq_top_of_residue {O ι : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
    (M : ι → Matrix (Fin a) (Fin a) O)
    (h : Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => (M g).map (IsLocalRing.residue O)) = ⊤) :
    Submodule.span O (Set.range M) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top
  | exact _root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top
  | (apply _root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top ..)

/- English proof (translation)
Establish `hspan : Submodule.span O (Set.range fun g => ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O)) = ⊤`. Use `span_eq_top_of_residue _ ?_` and prove the remaining obligations. Establish `h0` using `GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub _ h`. Establish `h1 : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (Formalism.MainNotions.N.mapRep (IsLocalRing.residue O) ρ) = fun g => ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).map (IsLocalRing.residue O)`. Use function extensionality and compare the values at `g`.

Both sides reduce to the same expression. Rewrite `h0` using `[h1]`. Then use the resulting hypothesis. Set `φ : MonoidAlgebra O Γ →ₐ[O] Matrix (Fin a) (Fin a) O` to `MonoidAlgebra.lift O (Matrix (Fin a) (Fin a) O) Γ ((Units.coeHom (Matrix (Fin a) (Fin a) O)).comp ρ)`. Set `φ' : MonoidAlgebra O Γ →ₐ[O] Matrix (Fin a) (Fin a) O` to `MonoidAlgebra.lift O (Matrix (Fin a) (Fin a) O) Γ ((Units.coeHom (Matrix (Fin a) (Fin a) O)).comp ρ')`. Establish `hφ : ∀ g c, φ (MonoidAlgebra.single g c) = c • (ρ g : Matrix (Fin a) (Fin a) O)` using `fun g c => by simp [φ]`.

Establish `hφ' : ∀ g c, φ' (MonoidAlgebra.single g c) = c • (ρ' g : Matrix (Fin a) (Fin a) O)` using `fun g c => by simp [φ']`. Establish `hsurj : Function.Surjective φ`. Establish `: LinearMap.range φ.toLinearMap = ⊤`. Rewrite using `[eq_top_iff, ← hspan, Submodule.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`.

Conclude with `⟨MonoidAlgebra.single g 1, by simpa using hφ g 1⟩`. Conclude with `LinearMap.range_eq_top.1 this`. Establish `htr' : ∀ x, (φ x).trace = (φ' x).trace`. Introduce `x`. Proceed by induction on `x using MonoidAlgebra.induction_linear with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, map_add, Matrix.trace_add, Matrix.trace_add, hx, hy]`. Consider the case `single g c => rw [hφ, hφ', Matrix.trace_smul, Matrix.trace_smul, htr]`. Take `⟨U, hU⟩` from `exists_conj_of_surjective φ φ' hsurj htr'`. Use `⟨U, fun g => Units.ext ?_⟩` and prove the remaining obligations.

Use `hU (MonoidAlgebra.single g 1)` as an intermediate fact. Rewrite `this` using `[hφ, hφ', one_smul, one_smul]`. Then use the resulting hypothesis.
-/
theorem exists_conj_of_trace_eq_local {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ]
    {a : ℕ} (ρ ρ' : Γ →* GL (Fin a) O)
    (h : Formalism.MainNotions.N.AbsIrrSub (Formalism.MainNotions.N.mapRep (IsLocalRing.residue O) ρ) ⊤)
    (htr : ∀ g, ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace =
      ((ρ' g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace) :
    ∃ U : GL (Fin a) O, ∀ g, ρ' g * U = U * ρ g := by
  classical
  have hspan : Submodule.span O
      (Set.range fun g => ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O)) = ⊤ :=
    by
    refine span_eq_top_of_residue _ ?_
    have h0 := GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub _ h
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (Formalism.MainNotions.N.mapRep (IsLocalRing.residue O) ρ) = fun g =>
        ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).map (IsLocalRing.residue O) := by
      funext g
      rfl
    rwa [h1] at h0
  let φ : MonoidAlgebra O Γ →ₐ[O] Matrix (Fin a) (Fin a) O :=
    MonoidAlgebra.lift O (Matrix (Fin a) (Fin a) O) Γ ((Units.coeHom (Matrix (Fin a) (Fin a) O)).comp ρ)
  let φ' : MonoidAlgebra O Γ →ₐ[O] Matrix (Fin a) (Fin a) O :=
    MonoidAlgebra.lift O (Matrix (Fin a) (Fin a) O) Γ ((Units.coeHom (Matrix (Fin a) (Fin a) O)).comp ρ')
  have hφ : ∀ g c, φ (MonoidAlgebra.single g c) = c • (ρ g : Matrix (Fin a) (Fin a) O) :=
    fun g c => by simp [φ]
  have hφ' : ∀ g c, φ' (MonoidAlgebra.single g c) = c • (ρ' g : Matrix (Fin a) (Fin a) O) :=
    fun g c => by simp [φ']
  have hsurj : Function.Surjective φ := by
    have : LinearMap.range φ.toLinearMap = ⊤ := by
      rw [eq_top_iff, ← hspan, Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact ⟨MonoidAlgebra.single g 1, by simpa using hφ g 1⟩
    exact LinearMap.range_eq_top.1 this
  have htr' : ∀ x, (φ x).trace = (φ' x).trace := by
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, Matrix.trace_add, Matrix.trace_add, hx, hy]
    | single g c => rw [hφ, hφ', Matrix.trace_smul, Matrix.trace_smul, htr]
  obtain ⟨U, hU⟩ := exists_conj_of_surjective φ φ' hsurj htr'
  refine ⟨U, fun g => Units.ext ?_⟩
  have := hU (MonoidAlgebra.single g 1)
  rwa [hφ, hφ', one_smul, one_smul] at this

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ ρ ρ' h htr` and use `exists_conj_of_trace_eq_local ρ ρ' h htr`.
-/
theorem exists_conj_of_trace_eq :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Γ : Type) [Group Γ] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) O), Formalism.MainNotions.N.AbsIrrSub (Formalism.MainNotions.N.mapRep (IsLocalRing.residue O) ρ) ⊤ → (∀ g, ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace = ((ρ' g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace) → ∃ U : GL (Fin a) O, ∀ g, ρ' g * U = U * ρ g :=
  fun _ _ _ _ _ _ _ ρ ρ' h htr => exists_conj_of_trace_eq_local ρ ρ' h htr

end GlobalTheory.TraceConjugacy
