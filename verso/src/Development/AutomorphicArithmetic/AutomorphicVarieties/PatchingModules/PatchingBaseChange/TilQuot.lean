import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.KerMapPowerSeriesQuotient

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

/- English proof (translation)
Take `⟨s, rfl⟩` from `hJ`. Establish `hc : ∀ n, ∃ c : A → A, Function.support c ⊆ ↑s ∧ ∑ a ∈ s, c a • a = PowerSeries.coeff n f` using `fun n => Submodule.mem_span_finset.mp (h n)`. Use `choose c _ hc using hc`. Establish `hf : f = ∑ a ∈ s, PowerSeries.C a * PowerSeries.mk (fun n => c n a)`. Use extensionality with `n`.

Rewrite using `[map_sum]`. Simplify using `only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]`. Rewrite using `[← hc n]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul, mul_comm]`.

Rewrite using `[hf]`. Use `Ideal.sum_mem _ fun a ha => Ideal.mul_mem_right _ _ ?_` and prove the remaining obligations. Conclude with `Ideal.mem_map_of_mem _ (Ideal.subset_span ha)`.
-/
private theorem mem_map_C_of_forall_coeff_mem_of_fg {A : Type} [CommRing A] (J : Ideal A) (hJ : J.FG) (f : PowerSeries A)
    (h : ∀ n, PowerSeries.coeff n f ∈ J) : f ∈ J.map PowerSeries.C := by
  obtain ⟨s, rfl⟩ := hJ
  have hc : ∀ n, ∃ c : A → A, Function.support c ⊆ ↑s ∧ ∑ a ∈ s, c a • a = PowerSeries.coeff n f :=
    fun n => Submodule.mem_span_finset.mp (h n)
  choose c _ hc using hc
  have hf : f = ∑ a ∈ s, PowerSeries.C a * PowerSeries.mk (fun n => c n a) := by
    ext n
    rw [map_sum]
    simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    rw [← hc n]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_eq_mul, mul_comm]
  rw [hf]
  refine Ideal.sum_mem _ fun a ha => Ideal.mul_mem_right _ _ ?_
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ha)

/- English proof (translation)
Introduce `O O' _ _ _ R _ _ I hI`. Use `set φ := Algebra.TensorProduct.map (AlgHom.id O' O') (Ideal.Quotient.mkₐ O I) with hφ`. Establish `hsurj : Function.Surjective φ` using `Algebra.TensorProduct.map_surjective _ _ (fun x => ⟨x, rfl⟩) (Ideal.Quotient.mkₐ_surjective O I)`. Establish `hker : RingHom.ker φ = I.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R)`. Establish `e` using `Algebra.TensorProduct.lTensor_ker (A := O') (Ideal.Quotient.mkₐ O I) (Ideal.Quotient.mkₐ_surjective O I)`.

Establish `hk : RingHom.ker (Ideal.Quotient.mkₐ O I) = I`. Use extensionality with `x`. Simplify using `[RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]`. Rewrite `e` using `[hk]`. Rewrite using `[← e]`.

Both sides reduce to the same expression. Establish `hcoeff : ∀ (f : Til O O' R) (n : ℕ), PowerSeries.coeff n (Til.map O' (Ideal.Quotient.mkₐ O I) f : PowerSeries (O' ⊗[O] (R ⧸ I))) = φ (PowerSeries.coeff n (f : PowerSeries (O' ⊗[O] R)))` using `fun f n => PowerSeries.coeff_map _ _ _`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `f`. Use `⟨(PowerSeries.mk fun n => (hsurj (PowerSeries.coeff n (f : PowerSeries (O' ⊗[O] (R ⧸ I))))).choose : PowerSeries (O' ⊗[O] R)), ?_⟩` and prove the remaining obligations.

Apply `PowerSeries.ext` to reduce the goal to its premises. Introduce `n`. Use `(hcoeff _ n).trans ?_` and prove the remaining obligations. Use `erw [PowerSeries.coeff_mk]`. Conclude with `(hsurj _).choose_spec`.

Establish `hι : I.map (Til.ι O O' R) = (RingHom.ker φ).map (Til.C O O' R)`. Rewrite using `[hker]`. Conclude with `(Ideal.map_map _ _).symm`. Rewrite using `[hι]`. Use extensionality with `f`.

Rewrite using `[RingHom.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `hf`. Establish `h : ∀ n, PowerSeries.coeff n (f : PowerSeries (O' ⊗[O] R)) ∈ RingHom.ker φ`. Introduce `n`.

Rewrite using `[RingHom.mem_ker, ← hcoeff, hf]`. Conclude with `map_zero _`. Establish `hJ : (RingHom.ker φ).FG`. Rewrite using `[hker]`. Conclude with `hI.map _`.

Conclude with `mem_map_C_of_forall_coeff_mem_of_fg _ hJ f h`. Introduce `hf`. Use `(Ideal.map_le_iff_le_comap.mpr ?_ : (RingHom.ker φ).map (Til.C O O' R) ≤ RingHom.ker (Til.map O' (Ideal.Quotient.mkₐ O I))) hf` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker]`.

Apply `PowerSeries.ext` to reduce the goal to its premises. Introduce `n`. Rewrite using `[hcoeff]`. Express the relevant statement in the definitionally equal form `φ (PowerSeries.coeff n (PowerSeries.C x : PowerSeries (O' ⊗[O] R))) = PowerSeries.coeff n (0 : PowerSeries (O' ⊗[O] (R ⧸ I)))`. Rewrite using `[PowerSeries.coeff_C, map_zero]`.

Use `split_ifs`. Conclude with `RingHom.mem_ker.mp hx`. Conclude with `map_zero _`.
-/
theorem UpperTheory.V.Pa.BC.til_quot :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (R : Type) [CommRing R] [Algebra O R] (I : Ideal R), I.FG → Function.Surjective (Til.map O' (Ideal.Quotient.mkₐ O I)) ∧ RingHom.ker (Til.map O' (Ideal.Quotient.mkₐ O I)) = I.map (Til.ι O O' R) := by
  intro O O' _ _ _ R _ _ I hI
  set φ := Algebra.TensorProduct.map (AlgHom.id O' O') (Ideal.Quotient.mkₐ O I) with hφ
  have hsurj : Function.Surjective φ :=
    Algebra.TensorProduct.map_surjective _ _ (fun x => ⟨x, rfl⟩) (Ideal.Quotient.mkₐ_surjective O I)
  have hker : RingHom.ker φ = I.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) := by
    have e := Algebra.TensorProduct.lTensor_ker (A := O') (Ideal.Quotient.mkₐ O I)
      (Ideal.Quotient.mkₐ_surjective O I)
    have hk : RingHom.ker (Ideal.Quotient.mkₐ O I) = I := by
      ext x
      simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rw [hk] at e
    rw [← e]
    rfl
  have hcoeff : ∀ (f : Til O O' R) (n : ℕ),
      PowerSeries.coeff n (Til.map O' (Ideal.Quotient.mkₐ O I) f : PowerSeries (O' ⊗[O] (R ⧸ I)))
        = φ (PowerSeries.coeff n (f : PowerSeries (O' ⊗[O] R))) :=
    fun f n => PowerSeries.coeff_map _ _ _
  refine ⟨?_, ?_⟩
  · intro f
    refine ⟨(PowerSeries.mk fun n =>
      (hsurj (PowerSeries.coeff n (f : PowerSeries (O' ⊗[O] (R ⧸ I))))).choose : PowerSeries (O' ⊗[O] R)), ?_⟩
    apply PowerSeries.ext
    intro n
    refine (hcoeff _ n).trans ?_
    erw [PowerSeries.coeff_mk]
    exact (hsurj _).choose_spec
  · have hι : I.map (Til.ι O O' R) = (RingHom.ker φ).map (Til.C O O' R) := by
      rw [hker]
      exact (Ideal.map_map _ _).symm
    rw [hι]
    ext f
    rw [RingHom.mem_ker]
    constructor
    · intro hf
      have h : ∀ n, PowerSeries.coeff n (f : PowerSeries (O' ⊗[O] R)) ∈ RingHom.ker φ := by
        intro n
        rw [RingHom.mem_ker, ← hcoeff, hf]
        exact map_zero _
      have hJ : (RingHom.ker φ).FG := by
        rw [hker]
        exact hI.map _
      exact mem_map_C_of_forall_coeff_mem_of_fg _ hJ f h
    · intro hf
      refine (Ideal.map_le_iff_le_comap.mpr ?_ : (RingHom.ker φ).map (Til.C O O' R)
        ≤ RingHom.ker (Til.map O' (Ideal.Quotient.mkₐ O I))) hf
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker]
      apply PowerSeries.ext
      intro n
      rw [hcoeff]
      change φ (PowerSeries.coeff n (PowerSeries.C x : PowerSeries (O' ⊗[O] R)))
        = PowerSeries.coeff n (0 : PowerSeries (O' ⊗[O] (R ⧸ I)))
      rw [PowerSeries.coeff_C, map_zero]
      split_ifs
      · exact RingHom.mem_ker.mp hx
      · exact map_zero _
