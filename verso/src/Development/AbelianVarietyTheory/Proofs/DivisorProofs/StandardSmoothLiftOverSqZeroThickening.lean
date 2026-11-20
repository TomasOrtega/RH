import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

open MvPolynomial in
/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p j hp`. Simplify using `only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, map_X, pderiv_X]`.

Use `congr 1`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, Ne.symm h]`.
-/
theorem mvPolynomial_map_pderiv_lift {κ R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (i : κ)
    (f : MvPolynomial κ R) :
    MvPolynomial.map π (pderiv i f) = pderiv i (MvPolynomial.map π f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, map_X, pderiv_X]
    congr 1
    by_cases h : i = j
    · subst h; simp
    · simp [Pi.single_apply, Ne.symm h]

/- English proof (translation)
Take `⟨u, hu⟩` from `hx.exists_right_inv`. Take `⟨y, rfl⟩` from `hp u`. Establish `hn : x * y - 1 ∈ K` using `hker _ (by simp [hu])`. Establish `hsq : (x * y - 1) * (x * y - 1) = 0`. Establish `: (x * y - 1) * (x * y - 1) ∈ K ^ 2` using `by rw [pow_two]; exact Ideal.mul_mem_mul hn hn`.

Rewrite `this` using `[hK]`. Simplify using `using this`. Establish `hnil : IsNilpotent (x * y - 1)` using `⟨2, by rw [pow_two, hsq]⟩`. Establish `: IsUnit (x * y)` using `by simpa using hnil.isUnit_one_add`. Conclude with `isUnit_of_mul_isUnit_left this`.
-/
theorem isUnit_of_isUnit_map_of_sqZero_ker {A A₀ : Type} [CommRing A] [CommRing A₀] (p : A →+* A₀)
    (hp : Function.Surjective p) (K : Ideal A) (hK : K ^ 2 = 0) (hker : ∀ a, p a = 0 → a ∈ K)
    (x : A) (hx : IsUnit (p x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := hx.exists_right_inv
  obtain ⟨y, rfl⟩ := hp u
  have hn : x * y - 1 ∈ K := hker _ (by simp [hu])
  have hsq : (x * y - 1) * (x * y - 1) = 0 := by
    have : (x * y - 1) * (x * y - 1) ∈ K ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hn hn
    rw [hK] at this; simpa using this
  have hnil : IsNilpotent (x * y - 1) := ⟨2, by rw [pow_two, hsq]⟩
  have : IsUnit (x * y) := by simpa using hnil.isUnit_one_add
  exact isUnit_of_mul_isUnit_left this

open MvPolynomial in

/- English proof (translation)
Introduce `R R₀ _ _ I hI π hπ hk B₀ _ _ hB₀`. Take `⟨κ, τ, _, _, ⟨P⟩⟩` from `hB₀.out`. Establish `: Fintype τ` using `Fintype.ofFinite τ`. Establish `hmap : Function.Surjective (MvPolynomial.map (σ` using `κ) π) := MvPolynomial.map_surjective π hπ`. Set `v : τ → MvPolynomial κ R` to `fun j => Function.surjInv hmap (P.relation j)`.

Establish `hv : ∀ j, MvPolynomial.map π (v j) = P.relation j` using `fun j => Function.surjInv_eq hmap _`. Set `J : Ideal (MvPolynomial κ R)` to `Ideal.span (Set.range v)`. Set `φ : MvPolynomial κ R →+* B₀` to `(aeval P.val).toRingHom.comp (MvPolynomial.map π)`. Establish `hφ : ∀ f, φ f = aeval P.val (MvPolynomial.map π f)` using `fun _ => rfl`. Establish `hJ : J ≤ RingHom.ker φ`.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Simplify using `[RingHom.mem_ker, hφ, hv, Algebra.Presentation.aeval_val_relation]`. Set `p : (MvPolynomial κ R ⧸ J) →+* B₀` to `Ideal.Quotient.lift J φ hJ`. Establish `hp : ∀ f, p (Ideal.Quotient.mk J f) = φ f` using `fun _ => rfl`.

Establish `halg : ∀ r : R, p (algebraMap R _ r) = algebraMap R₀ B₀ (π r)`. Introduce `r`. Rewrite using `[IsScalarTower.algebraMap_apply R (MvPolynomial κ R) (MvPolynomial κ R ⧸ J)]`. Simplify using `[Ideal.Quotient.algebraMap_eq, hp, hφ]`. Establish `hsemi : SemiHom π p`.

Introduce `r b`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, halg]`. Establish `hsurj : Function.Surjective p`. Introduce `b`. Take `⟨g, rfl⟩` from `P.aeval_val_surjective b`.

Take `⟨f, rfl⟩` from `hmap g`. Conclude with `⟨Ideal.Quotient.mk J f, rfl⟩`. Establish `hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R (MvPolynomial κ R ⧸ J))`. Introduce `b`. Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective b`.

Prove the components needed by the constructor for the conclusion. Introduce `h0`. Rewrite `h0` using `[hp, hφ]`. Establish `hmem : MvPolynomial.map π f ∈ Ideal.span (Set.range P.relation)`. Rewrite using `[P.span_range_relation_eq_ker]`.

Use `first`. Consider the case `exact h0`. Consider the case `exact RingHom.mem_ker.mpr h0`. Consider the case `(rw [Algebra.Generators.ker_eq_ker_aeval_val]; exact h0)`. Take `⟨c, hc⟩` from `(Ideal.mem_span_range_iff_exists_fun).1 hmem`.

Set `c' : τ → MvPolynomial κ R` to `fun j => Function.surjInv hmap (c j)`. Establish `hc' : ∀ j, MvPolynomial.map π (c' j) = c j` using `fun j => Function.surjInv_eq hmap _`. Establish `hg : f - ∑ j, c' j * v j ∈ RingHom.ker (MvPolynomial.map (σ` using `κ) π) := by`. Rewrite using `[RingHom.mem_ker, map_sub, map_sum, ← hc]`. Simplify using `[hc', hv]`.

Rewrite `hg` using `[MvPolynomial.ker_map, hk]`. Establish `hs : ∑ j, c' j * v j ∈ J` using `Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)`. Establish `: Ideal.Quotient.mk J f = Ideal.Quotient.mk J (f - ∑ j, c' j * v j)`. Rewrite using `[map_sub, Ideal.Quotient.eq_zero_iff_mem.2 hs, sub_zero]`. Rewrite using `[this]`.

Establish `hmm` using `Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hg`. Rewrite `hmm` using `[Ideal.map_map]`. Then use the resulting hypothesis. Introduce `hb`. Establish `: I.map (algebraMap R (MvPolynomial κ R ⧸ J)) ≤ RingHom.ker p`. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `x hx`. Simplify using `only [Ideal.mem_comap, RingHom.mem_ker, halg]`. Establish `: π x = 0` using `by rw [← RingHom.mem_ker, hk]; exact hx`. Simplify using `[this]`. Conclude with `this hb`.

Set `Q` to `Algebra.PreSubmersivePresentation.naive (v := v) P.map P.map_inj`. Establish `hjac : p Q.jacobian = P.jacobian`. Rewrite using `[Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]`. Establish `h1 : ∀ f : MvPolynomial κ R, algebraMap Q.Ring (MvPolynomial κ R ⧸ Ideal.span (Set.range v)) f = Ideal.Quotient.mk J f` using `fun _ => rfl`. Rewrite using `[h1, hp, hφ, Algebra.Generators.algebraMap_apply]`.

Use `congr 1`. Rewrite using `[RingHom.map_det]`. Use `congrArg Matrix.det (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.PreSubmersivePresentation.jacobiMatrix_apply]`. Use `show MvPolynomial.map π (pderiv (P.map i) (v j)) = pderiv (P.map i) (P.relation j)`.

Rewrite using `[mvPolynomial_map_pderiv_lift, hv]`. Establish `hunit : IsUnit Q.jacobian`. Use `isUnit_of_isUnit_map_of_sqZero_ker p hsurj (I.map (algebraMap R _)) ?_ (fun a ha => (hker a).1 ha) _ (by rw [hjac]; exact P.jacobian_isUnit)` and prove the remaining obligations. Rewrite using `[← Ideal.map_pow, hI]`. Simplify using the standard rewrite rules.

Set `Q' : Algebra.SubmersivePresentation R (MvPolynomial κ R ⧸ J) κ τ` to `{ Q with jacobian_isUnit := hunit }`. Use `Q'.isStandardSmooth` as an intermediate fact. Conclude with `⟨_, inferInstance, inferInstance, p, hsemi, hsurj, hker, inferInstance⟩`.
-/
theorem standardSmooth_lift_of_sqZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀], Algebra.IsStandardSmooth R₀ B₀ → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  intro R R₀ _ _ I hI π hπ hk B₀ _ _ hB₀
  obtain ⟨κ, τ, _, _, ⟨P⟩⟩ := hB₀.out
  classical
  have : Fintype τ := Fintype.ofFinite τ
  have hmap : Function.Surjective (MvPolynomial.map (σ := κ) π) := MvPolynomial.map_surjective π hπ
  let v : τ → MvPolynomial κ R := fun j => Function.surjInv hmap (P.relation j)
  have hv : ∀ j, MvPolynomial.map π (v j) = P.relation j := fun j => Function.surjInv_eq hmap _
  let J : Ideal (MvPolynomial κ R) := Ideal.span (Set.range v)
  let φ : MvPolynomial κ R →+* B₀ := (aeval P.val).toRingHom.comp (MvPolynomial.map π)
  have hφ : ∀ f, φ f = aeval P.val (MvPolynomial.map π f) := fun _ => rfl
  have hJ : J ≤ RingHom.ker φ := by
    rw [Ideal.span_le]; rintro _ ⟨j, rfl⟩
    simp [RingHom.mem_ker, hφ, hv, Algebra.Presentation.aeval_val_relation]
  let p : (MvPolynomial κ R ⧸ J) →+* B₀ := Ideal.Quotient.lift J φ hJ
  have hp : ∀ f, p (Ideal.Quotient.mk J f) = φ f := fun _ => rfl
  have halg : ∀ r : R, p (algebraMap R _ r) = algebraMap R₀ B₀ (π r) := by
    intro r
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial κ R) (MvPolynomial κ R ⧸ J)]
    simp [Ideal.Quotient.algebraMap_eq, hp, hφ]
  have hsemi : SemiHom π p := by
    intro r b
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, halg]
  have hsurj : Function.Surjective p := by
    intro b
    obtain ⟨g, rfl⟩ := P.aeval_val_surjective b
    obtain ⟨f, rfl⟩ := hmap g
    exact ⟨Ideal.Quotient.mk J f, rfl⟩
  have hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R (MvPolynomial κ R ⧸ J)) := by
    intro b
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
    constructor
    · intro h0
      rw [hp, hφ] at h0
      have hmem : MvPolynomial.map π f ∈ Ideal.span (Set.range P.relation) := by
        rw [P.span_range_relation_eq_ker]
        first
          | exact h0
          | exact RingHom.mem_ker.mpr h0
          | (rw [Algebra.Generators.ker_eq_ker_aeval_val]; exact h0)
      obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hmem
      let c' : τ → MvPolynomial κ R := fun j => Function.surjInv hmap (c j)
      have hc' : ∀ j, MvPolynomial.map π (c' j) = c j := fun j => Function.surjInv_eq hmap _
      have hg : f - ∑ j, c' j * v j ∈ RingHom.ker (MvPolynomial.map (σ := κ) π) := by
        rw [RingHom.mem_ker, map_sub, map_sum, ← hc]
        simp [hc', hv]
      rw [MvPolynomial.ker_map, hk] at hg
      have hs : ∑ j, c' j * v j ∈ J :=
        Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
      have : Ideal.Quotient.mk J f = Ideal.Quotient.mk J (f - ∑ j, c' j * v j) := by
        rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.2 hs, sub_zero]
      rw [this]
      have hmm := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hg
      rwa [Ideal.map_map] at hmm
    · intro hb
      have : I.map (algebraMap R (MvPolynomial κ R ⧸ J)) ≤ RingHom.ker p := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        simp only [Ideal.mem_comap, RingHom.mem_ker, halg]
        have : π x = 0 := by rw [← RingHom.mem_ker, hk]; exact hx
        simp [this]
      exact this hb
  let Q := Algebra.PreSubmersivePresentation.naive (v := v) P.map P.map_inj
  have hjac : p Q.jacobian = P.jacobian := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
      Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    have h1 : ∀ f : MvPolynomial κ R, algebraMap Q.Ring (MvPolynomial κ R ⧸ Ideal.span (Set.range v)) f =
        Ideal.Quotient.mk J f := fun _ => rfl
    rw [h1, hp, hφ, Algebra.Generators.algebraMap_apply]
    congr 1
    rw [RingHom.map_det]
    refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    show MvPolynomial.map π (pderiv (P.map i) (v j)) = pderiv (P.map i) (P.relation j)
    rw [mvPolynomial_map_pderiv_lift, hv]
  have hunit : IsUnit Q.jacobian := by
    refine isUnit_of_isUnit_map_of_sqZero_ker p hsurj (I.map (algebraMap R _)) ?_ (fun a ha => (hker a).1 ha) _
      (by rw [hjac]; exact P.jacobian_isUnit)
    rw [← Ideal.map_pow, hI]; simp
  let Q' : Algebra.SubmersivePresentation R (MvPolynomial κ R ⧸ J) κ τ :=
    { Q with jacobian_isUnit := hunit }
  have := Q'.isStandardSmooth
  exact ⟨_, inferInstance, inferInstance, p, hsemi, hsurj, hker, inferInstance⟩

end GlobalTheory.Obs
