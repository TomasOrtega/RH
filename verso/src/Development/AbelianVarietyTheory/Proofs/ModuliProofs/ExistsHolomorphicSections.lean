import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOpenPartialHomeomorphAnalytic
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Imports

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.EtaleFamily

/- English proof (translation)
Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => simpa only [MvPolynomial.eval₂Hom_C] using hφ a`. Consider the case `add P Q hP hQ => simp only [map_add]`. Conclude with `hP.add hQ`. Consider the case `mul_X P i hP`.

Simplify using `only [map_mul, MvPolynomial.eval₂Hom_X']`. Conclude with `hP.mul (hu i)`.
-/
theorem analyticAt_eval₂Hom {E R J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CommRing R]
    (φ : E → (R →+* ℂ)) (u : E → J → ℂ) (w : E) (hφ : ∀ a, AnalyticAt ℂ (fun z => φ z a) w)
    (hu : ∀ i, AnalyticAt ℂ (fun z => u z i) w) (q : MvPolynomial J R) :
    AnalyticAt ℂ (fun z => MvPolynomial.eval₂Hom (φ z) (u z) q) w := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa only [MvPolynomial.eval₂Hom_C] using hφ a
  | add P Q hP hQ => simp only [map_add]; exact hP.add hQ
  | mul_X P i hP =>
    simp only [map_mul, MvPolynomial.eval₂Hom_X']
    exact hP.mul (hu i)

/- English proof (translation)
Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => simpa using hasDerivAt_const (0 : ℂ) (φ a)`. Consider the case `add P Q hP hQ`. Simplify using `only [map_add, add_mul, Finset.sum_add_distrib]`. Conclude with `hP.add hQ`.

Consider the case `mul_X P i hP`. Establish `hX : HasDerivAt (fun t : ℂ => y i + t * v i) (v i) 0`. Simplify using `using ((hasDerivAt_id (0 : ℂ)).mul_const (v i)).const_add (y i)`. Establish `h` using `hP.mul hX`. Simplify using `only [map_mul, MvPolynomial.eval₂Hom_X', Pi.add_apply, Pi.smul_apply, smul_eq_mul]`.

Use `HasDerivAt.congr_deriv h ?_` and prove the remaining obligations. Establish `h1 : ∀ j, MvPolynomial.eval₂Hom φ y (MvPolynomial.pderiv j (P * MvPolynomial.X i)) * v j = MvPolynomial.eval₂Hom φ y (MvPolynomial.pderiv j P) * v j * y i + if i = j then MvPolynomial.eval₂Hom φ y P * v j else 0`. Introduce `j`. Rewrite using `[MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using `[hij, Pi.single_eq_of_ne hij]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.sum_mul]`. Simplify using the standard rewrite rules.
-/
theorem hasDerivAt_eval₂Hom_line {R J : Type*} [CommRing R] [Fintype J]
    (φ : R →+* ℂ) (q : MvPolynomial J R) (y v : J → ℂ) :
    HasDerivAt (fun t : ℂ => MvPolynomial.eval₂Hom φ (y + t • v) q)
      (∑ i, MvPolynomial.eval₂Hom φ y (MvPolynomial.pderiv i q) * v i) 0 := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const (0 : ℂ) (φ a)
  | add P Q hP hQ =>
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    exact hP.add hQ
  | mul_X P i hP =>
    have hX : HasDerivAt (fun t : ℂ => y i + t * v i) (v i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (v i)).const_add (y i)
    have h := hP.mul hX
    simp only [map_mul, MvPolynomial.eval₂Hom_X', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine HasDerivAt.congr_deriv h ?_
    have h1 : ∀ j, MvPolynomial.eval₂Hom φ y (MvPolynomial.pderiv j (P * MvPolynomial.X i)) * v j =
        MvPolynomial.eval₂Hom φ y (MvPolynomial.pderiv j P) * v j * y i +
        if i = j then MvPolynomial.eval₂Hom φ y P * v j else 0 := by
      intro j
      rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
      by_cases hij : i = j
      · subst hij; simp; ring
      · simp [hij, Pi.single_eq_of_ne hij]; ring
    simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.sum_mul]
    simp

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.AnalyticLineDerivative.main`. Consider the case `exact _root_.GlobalTheory.AnalyticLineDerivative.main`. Consider the case `(apply _root_.GlobalTheory.AnalyticLineDerivative.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.AnalyticLineDerivative.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.AnalyticLineDerivative.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.AnalyticLineDerivative.main ..)`.
-/
theorem exists_local_inverse {E S J σ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [CommRing S] [Fintype J] [Fintype σ] [DecidableEq σ]
    (χ : E → (S →+* ℂ)) (rel : σ → MvPolynomial J S) (c : σ → J) (hc : Function.Bijective c)
    (z₀ : E) (u₀ : J → ℂ) (hχ : ∀ a, AnalyticAt ℂ (fun z => χ z a) z₀)
    (hdet : (Matrix.of fun s r : σ =>
      MvPolynomial.eval₂Hom (χ z₀) u₀ (MvPolynomial.pderiv (c s) (rel r))).det ≠ 0) :
    ∃ Φ : OpenPartialHomeomorph (E × (J → ℂ)) (E × (σ → ℂ)),
      (∀ w, Φ w = (w.1, fun r => MvPolynomial.eval₂Hom (χ w.1) w.2 (rel r))) ∧
      (z₀, u₀) ∈ Φ.source ∧ AnalyticOnNhd ℂ Φ.symm Φ.target := by
  first
  | exact @_root_.GlobalTheory.AnalyticLineDerivative.main
  | exact _root_.GlobalTheory.AnalyticLineDerivative.main
  | (apply _root_.GlobalTheory.AnalyticLineDerivative.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AnalyticLineDerivative.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AnalyticLineDerivative.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AnalyticLineDerivative.main ..)

/- English proof (translation)
Introduce `m g A R _ _ ψ B φ b₀ e hψ hB hb₀ hφ he`. Use `letI : Algebra (MvPolynomial (Fin g) A) R := ψ.toAlgebra`. Use `haveI : Algebra.Etale (MvPolynomial (Fin g) A) R := hψ`. Take `⟨J, τ, _, _, P, hP⟩` from `(Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.1 ‹Algebra.Etale (MvPolynomial (Fin g) A) R›).out`. Use `letI := Fintype.ofFinite J`.

Use `letI := Fintype.ofFinite τ`. Establish `hcard : Fintype.card τ = Fintype.card J`. Use `P.card_relations_le_card_vars_of_isFinite` as an intermediate fact. Simplify using `only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card] at this hP`. Use linear arithmetic over natural numbers and integers.

Establish `hbij : Function.Bijective P.map` using `(Fintype.bijective_iff_injective_and_card _).2 ⟨P.map_inj, hcard⟩`. Set `π : MvPolynomial J (MvPolynomial (Fin g) A) →+* R` to `MvPolynomial.eval₂Hom ψ P.val`. Establish `hπeq : ∀ a, π a = MvPolynomial.aeval P.val a` using `fun a => rfl`. Establish `hπ : Function.Surjective π` using `P.aeval_val_surjective`. Set `χ : (Fin m → ℂ) × (Fin g → ℂ) → (MvPolynomial (Fin g) A →+* ℂ)` to `fun q => MvPolynomial.eval₂Hom (φ q.1) q.2`.

Establish `hχ : ∀ q : (Fin m → ℂ) × (Fin g → ℂ), q.1 ∈ B → ∀ a, AnalyticAt ℂ (fun z => χ z a) q`. Introduce `q hq a`. Use `analyticAt_eval₂Hom (fun z : (Fin m → ℂ) × (Fin g → ℂ) => φ z.1) (fun z => z.2) q (fun c => ?_) (fun i => ?_) a` and prove the remaining obligations. Conclude with `AnalyticAt.comp (g := fun b => φ b c) (f := fun w : (Fin m → ℂ) × (Fin g → ℂ) => w.1) (GlobalTheory.SCV.analyticAt_of_differentiableOn (hφ c) (hB.mem_nhds hq)) analyticAt_fst`. Conclude with `((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) i).comp (ContinuousLinearMap.snd ℂ (Fin m → ℂ) (Fin g → ℂ))).analyticAt _`.

Establish `hevj : ∀ (b : Fin m → ℂ) (x : R →+* ℂ), (∀ a, x (ψ (MvPolynomial.C a)) = φ b a) → MvPolynomial.eval₂Hom (χ (b, fun i => x (ψ (MvPolynomial.X i)))) (fun i => x (P.val i)) = x.comp π`. Introduce `b x hx`. Use `MvPolynomial.ringHom_ext' ?_ ?_` and prove the remaining obligations. Use `MvPolynomial.ringHom_ext ?_ ?_` and prove the remaining obligations. Introduce `a`.

Simplify using `[χ, π, hx]`. Introduce `a`. Simplify using `[χ, π]`. Introduce `i`. Simplify using `[π]`.

Establish `hker : ∀ a, π a = 0 ↔ a ∈ Ideal.span (Set.range P.relation)`. Introduce `a`. Rewrite using `[P.span_range_relation_eq_ker]`. Rewrite using `[P.ker_eq_ker_aeval_val]`. Both sides reduce to the same expression.

Take `⟨Φ, hΦ, hpS, hsymm⟩` from `exists_local_inverse χ P.relation P.map hbij (b₀, fun i => e (ψ (MvPolynomial.X i))) (fun i => e (P.val i)) (hχ _ hb₀) (by`. Rewrite using `[hevj b₀ e he]`. Establish `h1` using `(P.jacobian_isUnit.map e).ne_zero`. Rewrite `h1` using `[P.jacobian_eq_jacobiMatrix_det, P.algebraMap_apply, ← hπeq]`. Establish `h2` using `(e.comp π).map_det P.jacobiMatrix`.

Establish `h3 : (e.comp π).mapMatrix P.jacobiMatrix = Matrix.of fun s r : τ => (e.comp π) (MvPolynomial.pderiv (P.map s) (P.relation r))`. Use extensionality with `s r`. Simplify using `[P.jacobiMatrix_apply]`. Rewrite using `[← h3, ← h2]`. Conclude with `h1)`.

Establish `hfst : ∀ q, (q, 0) ∈ Φ.target → (Φ.symm (q, 0)).1 = q`. Introduce `q hq`. Use `Φ.right_inv hq` as an intermediate fact. Rewrite `this` using `[hΦ]`. Conclude with `congrArg Prod.fst this`.

Establish `hex : ∀ q : (Fin m → ℂ) × (Fin g → ℂ), ∃ x : R →+* ℂ, (q, 0) ∈ Φ.target → x.comp π = MvPolynomial.eval₂Hom (χ q) (Φ.symm (q, 0)).2`. Introduce `q`. Distinguish the cases in `hq : (q, 0) ∈ Φ.target`. Establish `hle : RingHom.ker π ≤ RingHom.ker (MvPolynomial.eval₂Hom (χ q) (Φ.symm (q, 0)).2)`. Introduce `a ha`.

Establish `: Ideal.span (Set.range P.relation) ≤ RingHom.ker (MvPolynomial.eval₂Hom (χ q) (Φ.symm (q, 0)).2)`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨r, rfl⟩`. Establish `h1` using `Φ.right_inv hq`. Rewrite `h1` using `[hΦ, hfst q hq]`.

Conclude with `congrFun (congrArg Prod.snd h1) r`. Conclude with `this ((hker a).1 ha)`. Conclude with `⟨π.liftOfSurjective hπ ⟨_, hle⟩, fun _ => RingHom.ext fun c => RingHom.liftOfRightInverse_comp_apply π _ (Function.rightInverse_surjInv hπ) ⟨_, hle⟩ c⟩`. Conclude with `⟨e, fun h => absurd h hq⟩`. Use `choose s hs using hex`.

Set `eqv` to `(Fintype.equivFin (Fin g ⊕ J))`. Set `κ : (Fin m → ℂ) × (Fin (Fintype.card (Fin g ⊕ J)) → ℂ) → ((Fin m → ℂ) × (Fin g → ℂ)) × (J → ℂ)` to `fun y => ((y.1, fun i => y.2 (eqv (Sum.inl i))), fun i => y.2 (eqv (Sum.inr i)))`. Establish `hκ : Continuous κ` using `by fun_prop`. Set `f : Fin (Fintype.card (Fin g ⊕ J)) → R` to `fun j => Sum.elim (fun i => ψ (MvPolynomial.X i)) P.val (eqv.symm j)`. Establish `hκf : ∀ (b : Fin m → ℂ) (x : R →+* ℂ), κ (b, fun j => x (f j)) = ((b, fun i => x (ψ (MvPolynomial.X i))), fun i => x (P.val i))`.

Introduce `b x`. Simplify using `[κ, f]`. Establish `hNo : IsOpen {q : (Fin m → ℂ) × (Fin g → ℂ) | q.1 ∈ B ∧ (q, 0) ∈ Φ.target}` using `(hB.preimage continuous_fst).inter (Φ.open_target.preimage (continuous_id.prodMk continuous_const))`. Use `⟨{q | q.1 ∈ B ∧ (q, 0) ∈ Φ.target}, s, _, f, {y | y.1 ∈ B ∧ κ y ∈ Φ.source}, hNo, (hB.preimage continuous_fst).inter (Φ.open_source.preimage hκ), ⟨hb₀, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hκf]`.

Conclude with `hpS`. Introduce `a`. Take `⟨c, rfl⟩` from `hπ a`. Use `DifferentiableOn.congr (f := fun q => MvPolynomial.eval₂Hom (χ q) (Φ.symm (q, 0)).2 c) ?_ ?_` and prove the remaining obligations. Introduce `q hq`.

Use `(AnalyticAt.differentiableAt ?_).differentiableWithinAt` and prove the remaining obligations. Establish `h1 : AnalyticAt ℂ (fun z : (Fin m → ℂ) × (Fin g → ℂ) => Φ.symm (z, 0)) q` using `AnalyticAt.comp (f := fun z : (Fin m → ℂ) × (Fin g → ℂ) => (z, (0 : τ → ℂ))) (hsymm _ hq.2) (analyticAt_id.prod analyticAt_const)`. Use `analyticAt_eval₂Hom χ (fun z => (Φ.symm (z, 0)).2) q (hχ q hq.1) (fun i => ?_) c` and prove the remaining obligations. Conclude with `AnalyticAt.comp (f := fun z : (Fin m → ℂ) × (Fin g → ℂ) => Φ.symm (z, 0)) (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : J => ℂ) i).comp (ContinuousLinearMap.snd ℂ ((Fin m → ℂ) × (Fin g → ℂ)) (J → ℂ))).analyticAt _) h1`. Introduce `q hq`.

Conclude with `DFunLike.congr_fun (hs q hq.2) c`. Introduce `q hq`. Use `⟨hq.1, fun a => ?_, fun i => ?_⟩` and prove the remaining obligations. Simplify `DFunLike.congr_fun (hs q hq.2) (MvPolynomial.C (MvPolynomial.C a))` using `[π, χ]`. Simplify `DFunLike.congr_fun (hs q hq.2) (MvPolynomial.C (MvPolynomial.X i))` using `[π, χ]`.

Introduce and unpack `b x hx ⟨hb, hO⟩`. Rewrite `hO` using `[hκf]`. Establish `hΦx : Φ ((b, fun i => x (ψ (MvPolynomial.X i))), fun i => x (P.val i)) = ((b, fun i => x (ψ (MvPolynomial.X i))), 0)`. Rewrite using `[hΦ]`. Use `Prod.ext rfl (funext fun r => ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `MvPolynomial.eval₂Hom (χ (b, fun i => x (ψ (MvPolynomial.X i)))) (fun i => x (P.val i)) (P.relation r) = 0`. Rewrite using `[hevj b x hx, RingHom.comp_apply, (hker _).2 (Ideal.subset_span ⟨r, rfl⟩), map_zero]`. Establish `ht` using `Φ.map_source hO`. Rewrite `ht` using `[hΦx]`. Use `⟨⟨hb, ht⟩, ?_⟩` and prove the remaining obligations.

Establish `h1` using `hs _ ht`. Rewrite `h1` using `[← hΦx, Φ.left_inv hO, hevj b x hx]`. Use extensionality with `a`. Take `⟨c, rfl⟩` from `hπ a`. Conclude with `DFunLike.congr_fun h1 c`.
-/
theorem exists_holomorphic_sections :
    ∀ (m g : ℕ) (A R : Type) [CommRing A] [CommRing R] (ψ : MvPolynomial (Fin g) A →+* R) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)) (b₀ : Fin m → ℂ) (e : R →+* ℂ), ψ.Etale → IsOpen B → b₀ ∈ B → (∀ a, DifferentiableOn ℂ (fun b => φ b a) B) → (∀ a, e (ψ (MvPolynomial.C a)) = φ b₀ a) → ∃ (N : Set ((Fin m → ℂ) × (Fin g → ℂ))) (σ : (Fin m → ℂ) × (Fin g → ℂ) → (R →+* ℂ)) (n : ℕ) (f : Fin n → R) (O : Set ((Fin m → ℂ) × (Fin n → ℂ))), IsOpen N ∧ IsOpen O ∧ (b₀, fun j => e (f j)) ∈ O ∧ (∀ a, DifferentiableOn ℂ (fun q => σ q a) N) ∧ (∀ q ∈ N, q.1 ∈ B ∧ (∀ a, σ q (ψ (MvPolynomial.C a)) = φ q.1 a) ∧ ∀ i, σ q (ψ (MvPolynomial.X i)) = q.2 i) ∧ ∀ (b : Fin m → ℂ) (x : R →+* ℂ), (∀ a, x (ψ (MvPolynomial.C a)) = φ b a) → (b, fun j => x (f j)) ∈ O → (b, fun i => x (ψ (MvPolynomial.X i))) ∈ N ∧ σ (b, fun i => x (ψ (MvPolynomial.X i))) = x := by
  intro m g A R _ _ ψ B φ b₀ e hψ hB hb₀ hφ he
  classical
  letI : Algebra (MvPolynomial (Fin g) A) R := ψ.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin g) A) R := hψ
  obtain ⟨J, τ, _, _, P, hP⟩ := (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.1
    ‹Algebra.Etale (MvPolynomial (Fin g) A) R›).out
  letI := Fintype.ofFinite J
  letI := Fintype.ofFinite τ
  have hcard : Fintype.card τ = Fintype.card J := by
    have := P.card_relations_le_card_vars_of_isFinite
    simp only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card] at this hP
    omega
  have hbij : Function.Bijective P.map :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨P.map_inj, hcard⟩
  let π : MvPolynomial J (MvPolynomial (Fin g) A) →+* R := MvPolynomial.eval₂Hom ψ P.val
  have hπeq : ∀ a, π a = MvPolynomial.aeval P.val a := fun a => rfl
  have hπ : Function.Surjective π := P.aeval_val_surjective
  let χ : (Fin m → ℂ) × (Fin g → ℂ) → (MvPolynomial (Fin g) A →+* ℂ) :=
    fun q => MvPolynomial.eval₂Hom (φ q.1) q.2
  have hχ : ∀ q : (Fin m → ℂ) × (Fin g → ℂ), q.1 ∈ B → ∀ a, AnalyticAt ℂ (fun z => χ z a) q := by
    intro q hq a
    refine analyticAt_eval₂Hom (fun z : (Fin m → ℂ) × (Fin g → ℂ) => φ z.1) (fun z => z.2) q
      (fun c => ?_) (fun i => ?_) a
    · exact AnalyticAt.comp (g := fun b => φ b c) (f := fun w : (Fin m → ℂ) × (Fin g → ℂ) => w.1)
        (GlobalTheory.SCV.analyticAt_of_differentiableOn (hφ c) (hB.mem_nhds hq)) analyticAt_fst
    · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) i).comp
        (ContinuousLinearMap.snd ℂ (Fin m → ℂ) (Fin g → ℂ))).analyticAt _
  have hevj : ∀ (b : Fin m → ℂ) (x : R →+* ℂ), (∀ a, x (ψ (MvPolynomial.C a)) = φ b a) →
      MvPolynomial.eval₂Hom (χ (b, fun i => x (ψ (MvPolynomial.X i)))) (fun i => x (P.val i))
        = x.comp π := by
    intro b x hx
    refine MvPolynomial.ringHom_ext' ?_ ?_
    · refine MvPolynomial.ringHom_ext ?_ ?_
      · intro a; simp [χ, π, hx]
      · intro a; simp [χ, π]
    · intro i; simp [π]
  have hker : ∀ a, π a = 0 ↔ a ∈ Ideal.span (Set.range P.relation) := by
    intro a
    rw [P.span_range_relation_eq_ker]
    rw [P.ker_eq_ker_aeval_val]
    rfl
  obtain ⟨Φ, hΦ, hpS, hsymm⟩ := exists_local_inverse χ P.relation P.map hbij
    (b₀, fun i => e (ψ (MvPolynomial.X i))) (fun i => e (P.val i)) (hχ _ hb₀) (by
      rw [hevj b₀ e he]
      have h1 := (P.jacobian_isUnit.map e).ne_zero
      rw [P.jacobian_eq_jacobiMatrix_det, P.algebraMap_apply, ← hπeq] at h1
      have h2 := (e.comp π).map_det P.jacobiMatrix
      have h3 : (e.comp π).mapMatrix P.jacobiMatrix = Matrix.of fun s r : τ =>
          (e.comp π) (MvPolynomial.pderiv (P.map s) (P.relation r)) := by
        ext s r
        simp [P.jacobiMatrix_apply]
      rw [← h3, ← h2]
      exact h1)
  have hfst : ∀ q, (q, 0) ∈ Φ.target → (Φ.symm (q, 0)).1 = q := by
    intro q hq
    have := Φ.right_inv hq
    rw [hΦ] at this
    exact congrArg Prod.fst this
  have hex : ∀ q : (Fin m → ℂ) × (Fin g → ℂ), ∃ x : R →+* ℂ, (q, 0) ∈ Φ.target →
      x.comp π = MvPolynomial.eval₂Hom (χ q) (Φ.symm (q, 0)).2 := by
    intro q
    by_cases hq : (q, 0) ∈ Φ.target
    · have hle : RingHom.ker π ≤
          RingHom.ker (MvPolynomial.eval₂Hom (χ q) (Φ.symm (q, 0)).2) := by
        intro a ha
        have : Ideal.span (Set.range P.relation) ≤
            RingHom.ker (MvPolynomial.eval₂Hom (χ q) (Φ.symm (q, 0)).2) := by
          rw [Ideal.span_le]
          rintro _ ⟨r, rfl⟩
          have h1 := Φ.right_inv hq
          rw [hΦ, hfst q hq] at h1
          exact congrFun (congrArg Prod.snd h1) r
        exact this ((hker a).1 ha)
      exact ⟨π.liftOfSurjective hπ ⟨_, hle⟩, fun _ => RingHom.ext fun c =>
        RingHom.liftOfRightInverse_comp_apply π _ (Function.rightInverse_surjInv hπ) ⟨_, hle⟩ c⟩
    · exact ⟨e, fun h => absurd h hq⟩
  choose s hs using hex
  let eqv := (Fintype.equivFin (Fin g ⊕ J))
  let κ : (Fin m → ℂ) × (Fin (Fintype.card (Fin g ⊕ J)) → ℂ) →
      ((Fin m → ℂ) × (Fin g → ℂ)) × (J → ℂ) :=
    fun y => ((y.1, fun i => y.2 (eqv (Sum.inl i))), fun i => y.2 (eqv (Sum.inr i)))
  have hκ : Continuous κ := by fun_prop
  let f : Fin (Fintype.card (Fin g ⊕ J)) → R :=
    fun j => Sum.elim (fun i => ψ (MvPolynomial.X i)) P.val (eqv.symm j)
  have hκf : ∀ (b : Fin m → ℂ) (x : R →+* ℂ), κ (b, fun j => x (f j)) =
      ((b, fun i => x (ψ (MvPolynomial.X i))), fun i => x (P.val i)) := by
    intro b x
    simp [κ, f]
  have hNo : IsOpen {q : (Fin m → ℂ) × (Fin g → ℂ) | q.1 ∈ B ∧ (q, 0) ∈ Φ.target} :=
    (hB.preimage continuous_fst).inter
      (Φ.open_target.preimage (continuous_id.prodMk continuous_const))
  refine ⟨{q | q.1 ∈ B ∧ (q, 0) ∈ Φ.target}, s, _, f, {y | y.1 ∈ B ∧ κ y ∈ Φ.source}, hNo,
    (hB.preimage continuous_fst).inter (Φ.open_source.preimage hκ), ⟨hb₀, ?_⟩, ?_, ?_, ?_⟩
  · rw [hκf]; exact hpS
  · intro a
    obtain ⟨c, rfl⟩ := hπ a
    refine DifferentiableOn.congr
      (f := fun q => MvPolynomial.eval₂Hom (χ q) (Φ.symm (q, 0)).2 c) ?_ ?_
    · intro q hq
      refine (AnalyticAt.differentiableAt ?_).differentiableWithinAt
      have h1 : AnalyticAt ℂ (fun z : (Fin m → ℂ) × (Fin g → ℂ) => Φ.symm (z, 0)) q :=
        AnalyticAt.comp (f := fun z : (Fin m → ℂ) × (Fin g → ℂ) => (z, (0 : τ → ℂ)))
          (hsymm _ hq.2) (analyticAt_id.prod analyticAt_const)
      refine analyticAt_eval₂Hom χ (fun z => (Φ.symm (z, 0)).2) q (hχ q hq.1) (fun i => ?_) c
      exact AnalyticAt.comp (f := fun z : (Fin m → ℂ) × (Fin g → ℂ) => Φ.symm (z, 0))
        (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : J => ℂ) i).comp
        (ContinuousLinearMap.snd ℂ ((Fin m → ℂ) × (Fin g → ℂ)) (J → ℂ))).analyticAt _) h1
    · intro q hq
      exact DFunLike.congr_fun (hs q hq.2) c
  · intro q hq
    refine ⟨hq.1, fun a => ?_, fun i => ?_⟩
    · simpa [π, χ] using DFunLike.congr_fun (hs q hq.2) (MvPolynomial.C (MvPolynomial.C a))
    · simpa [π, χ] using DFunLike.congr_fun (hs q hq.2) (MvPolynomial.C (MvPolynomial.X i))
  · rintro b x hx ⟨hb, hO⟩
    rw [hκf] at hO
    have hΦx : Φ ((b, fun i => x (ψ (MvPolynomial.X i))), fun i => x (P.val i)) =
        ((b, fun i => x (ψ (MvPolynomial.X i))), 0) := by
      rw [hΦ]
      refine Prod.ext rfl (funext fun r => ?_)
      change MvPolynomial.eval₂Hom (χ (b, fun i => x (ψ (MvPolynomial.X i))))
        (fun i => x (P.val i)) (P.relation r) = 0
      rw [hevj b x hx, RingHom.comp_apply, (hker _).2 (Ideal.subset_span ⟨r, rfl⟩), map_zero]
    have ht := Φ.map_source hO
    rw [hΦx] at ht
    refine ⟨⟨hb, ht⟩, ?_⟩
    have h1 := hs _ ht
    rw [← hΦx, Φ.left_inv hO, hevj b x hx] at h1
    ext a
    obtain ⟨c, rfl⟩ := hπ a
    exact DFunLike.congr_fun h1 c

end GlobalTheory.EtaleFamily
