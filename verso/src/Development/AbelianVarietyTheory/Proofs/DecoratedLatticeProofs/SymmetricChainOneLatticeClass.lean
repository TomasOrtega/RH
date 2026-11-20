import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecAuxiliaryBasisVectorSumFinApply

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.SymChain.LatClass
open GlobalTheory.SymChain GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
The claim follows from `(h _).2 le_rfl`.
-/
theorem valuation_lt_one_of_unif {ϖ : kˣ} (h : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) : valuation k (ϖ : k) < 1 :=
  (h _).2 le_rfl

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Establish `h1` using `valuation_lt_one_of_unif h`. Use `⟨Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 h1, fun a b hab => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_or]`. Establish `ha : valuation k (a : k) < 1` using `Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hn.1`.

Establish `hb : valuation k (b : k) < 1` using `Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hn.2`. Establish `e : (ϖ : k) = (a : k) * b` using `congrArg Subtype.val hab`. Establish `h0 : 0 < valuation k (ϖ : k)` using `by simp [zero_lt_iff]`. Establish `: valuation k (ϖ : k) < valuation k (ϖ : k)`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `lt_irrefl _ this`.
-/
theorem irreducible_of_unif {ϖ : kˣ} (h : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) :
    Irreducible (⟨(ϖ : k), (valuation_lt_one_of_unif h).le⟩ : 𝒪[k]) := by
  have h1 := valuation_lt_one_of_unif h
  refine ⟨Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 h1, fun a b hab => ?_⟩
  by_contra hn
  rw [not_or] at hn
  have ha : valuation k (a : k) < 1 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hn.1
  have hb : valuation k (b : k) < 1 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hn.2
  have e : (ϖ : k) = (a : k) * b := congrArg Subtype.val hab
  have h0 : 0 < valuation k (ϖ : k) := by simp [zero_lt_iff]
  have : valuation k (ϖ : k) < valuation k (ϖ : k) := by
    calc valuation k (ϖ : k) = valuation k (a : k) * valuation k (b : k) := by rw [e, map_mul]
      _ ≤ valuation k (ϖ : k) * valuation k (b : k) := mul_le_mul_left ((h _).1 ha) _
      _ < valuation k (ϖ : k) * 1 := mul_lt_mul_of_pos_left hb h0
      _ = _ := mul_one _
  exact lt_irrefl _ this

section
variable {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[mem_chainLat, mem_latOf_typeFrame, mem_stdLat, hp]`. Use `and_congr Iff.rfl (forall_congr' fun i => ?_)` and prove the remaining obligations. Establish `h0 : ((ϖ : k) ^ (i.val + 1)) ≠ 0` using `pow_ne_zero _ ϖ.ne_zero`. Establish `hv : 0 < valuation k ((ϖ : k) ^ (i.val + 1))` using `by simp [zero_lt_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`. Rewrite using `[ha, map_mul]`. Conclude with `mul_le_of_le_one_left' a.2`. Introduce `h`.

Use `⟨⟨y (.inr i) / (ϖ : k) ^ (i.val + 1), ?_⟩, by simp [div_mul_cancel₀ _ h0]⟩` and prove the remaining obligations. Rewrite using `[Valuation.mem_integer_iff, map_div₀]`. Conclude with `(div_le_one₀ hv).2 h`.
-/
theorem chainLat_eq_latOf (ϖ : kˣ) (p : 𝒪[k]) (hp : (p : k) = ϖ) (o : ι ≃ n ⊕ Fin c) :
    chainLat p c (stdLat k n) = latOf (typeFrame ϖ o).bas := by
  ext y
  rw [mem_chainLat, mem_latOf_typeFrame, mem_stdLat, hp]
  refine and_congr Iff.rfl (forall_congr' fun i => ?_)
  have h0 : ((ϖ : k) ^ (i.val + 1)) ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  have hv : 0 < valuation k ((ϖ : k) ^ (i.val + 1)) := by simp [zero_lt_iff]
  constructor
  · rintro ⟨a, ha⟩
    rw [ha, map_mul]
    exact mul_le_of_le_one_left' a.2
  · intro h
    refine ⟨⟨y (.inr i) / (ϖ : k) ^ (i.val + 1), ?_⟩, by simp [div_mul_cancel₀ _ h0]⟩
    rw [Valuation.mem_integer_iff, map_div₀]
    exact (div_le_one₀ hv).2 h

end

section
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Use extensionality with `v`. Rewrite using `[mem_act_iff_inv, ← mulVec_mem_latOf u, mulVec_mulVec, Units.mul_inv, one_mulVec]`.
-/
theorem act_latOf (u g : GL Y k) : act u (latOf g) = latOf (u * g) := by
  ext v
  rw [mem_act_iff_inv, ← mulVec_mem_latOf u, mulVec_mulVec, Units.mul_inv, one_mulVec]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Establish `h1 : g'.val *ᵥ Pi.single j 1 ∈ latOf g'`. Use `(mulVec_mem_latOf g' (g := 1) (y := Pi.single j 1)).2 (mem_latOf_one.2 fun l => by` as an intermediate fact. Rewrite using `[Pi.single_apply]`.

Use `split_ifs`. Use `exacts [one_mem _, zero_mem _])`. Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis. Use `h _ h1 i` as an intermediate fact. Rewrite `this` using `[mulVec_mulVec, mulVec_mulVec, mulVec_single_one]`. Then use the resulting hypothesis.

Introduce `h y hy i`. Establish `: (g⁻¹).val *ᵥ (x *ᵥ y) = ((g⁻¹).val * x * g'.val) *ᵥ ((g'⁻¹).val *ᵥ y)`. Simplify using `[mulVec_mulVec, Matrix.mul_assoc]`. Rewrite using `[this]`. Conclude with `sum_mem fun l _ => mul_mem (h i l) (hy l)`.
-/
theorem mapsInto_latOf_iff (g : GL Y k) (g' : GL Y' k) (x : Matrix Y Y' k) :
    MapsInto x (latOf g') (latOf g) ↔ IntM ((g⁻¹).val * x * g'.val) := by
  constructor
  · intro h i j
    have h1 : g'.val *ᵥ Pi.single j 1 ∈ latOf g' := by
      have := (mulVec_mem_latOf g' (g := 1) (y := Pi.single j 1)).2 (mem_latOf_one.2 fun l => by
        rw [Pi.single_apply]; split_ifs
        exacts [one_mem _, zero_mem _])
      rwa [mul_one] at this
    have := h _ h1 i
    rwa [mulVec_mulVec, mulVec_mulVec, mulVec_single_one] at this
  · intro h y hy i
    have : (g⁻¹).val *ᵥ (x *ᵥ y) = ((g⁻¹).val * x * g'.val) *ᵥ ((g'⁻¹).val *ᵥ y) := by
      simp [mulVec_mulVec, Matrix.mul_assoc]
    rw [this]
    exact sum_mem fun l _ => mul_mem (h i l) (hy l)

end

/- English proof (translation)
Introduce `j c H h hf`. Establish `h1` using `valuation_lt_one_of_unif S.unif`. Set `p : 𝒪[k]` to `⟨(S.ϖ : k), h1.le⟩`. Set `o` to `stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1) (by omega)`. Set `o'` to `stdOrd (Fin κ) t (l := s + 1) j (c + 1 + 1) (by omega)`.

Establish `e` using `chainLat_eq_latOf S.ϖ p rfl o`. Establish `e'` using `chainLat_eq_latOf S.ϖ p rfl o'`. Establish `hΦ : ∀ x, (S.T t).Phi j (c + 1) (by omega) x = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1)) (((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x).submatrix (ixSucc _ t j) id)` using `fun _ => rfl`. Take `⟨r, hr, u, hu, hh⟩` from `(oneCoset (n := XIx (Fin κ) t (j + 1)) (c := c + 1) (by omega) (irreducible_of_unif S.unif) S.cond hν (stdLat k (XIx (Fin κ) t j))).1 (S.μ (j + 1)) ((S.T t).Phi j (c + 1) (by omega)) ((Chain.ofType_regular _ _ _ _ _).1 j (c + 1) _) (by`. Introduce `x hx`.

Express the relevant statement in the definitionally equal form `MapsInto x (chainLat p _ _) (chainLat p _ _)`. Rewrite using `[e, e', mapsInto_latOf_iff]`. Rewrite `hx` using `[hΦ]`. Introduce `a b`. Simplify `TypeDatum.intM_of_Phi_ne_zero _ _ hx ((ixSucc _ t j).symm (o.symm a)) (o'.symm b)) (by` using `[LatFrame.coords, typeFrame]`.

Introduce `x y hy`. Express the relevant statement in the definitionally equal form `MapsInto y (chainLat p _ _) (chainLat p _ _) at hy`. Rewrite `hy` using `[e, e', mapsInto_latOf_iff]`. Rewrite using `[hΦ, hΦ]`. Establish `: ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') (x + (S.ϖ : k) • y)).submatrix (ixSucc _ t j) id = ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x).submatrix (ixSucc _ t j) id + (S.ϖ : k) • ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') y).submatrix (ixSucc _ t j) id`.

Simplify using `only [LatFrame.coords, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]`. Both sides reduce to the same expression. Use `(congrArg _ this).trans (TypeDatum.Phi_add _ (S.tame _) _ fun a b => ?_)` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, smul_eq_mul, map_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 (hy _ _)) 1 h (act_one _) hf`.

Use `⟨r, hr, u, mem_stabLat_iff.2 ?_, hh⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `act u (chainLat p _ _) = chainLat p _ _ at hu`. Rewrite `hu` using `[e, act_latOf]`. Conclude with `hu`.
-/
theorem oneClass_symChain (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (s κ : ℕ) (S : SymData k s κ)
    (t : Type) [Fintype t] [DecidableEq t] : S.OneClass t ν := by
  intro j c H h hf
  have h1 := valuation_lt_one_of_unif S.unif
  let p : 𝒪[k] := ⟨(S.ϖ : k), h1.le⟩
  let o := stdOrd (Fin κ) t (l := s + 1) (j + 1) (c + 1) (by omega)
  let o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1 + 1) (by omega)
  have e := chainLat_eq_latOf S.ϖ p rfl o
  have e' := chainLat_eq_latOf S.ϖ p rfl o'
  have hΦ : ∀ x, (S.T t).Phi j (c + 1) (by omega) x = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      (((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x).submatrix (ixSucc _ t j) id) := fun _ => rfl
  obtain ⟨r, hr, u, hu, hh⟩ := (oneCoset (n := XIx (Fin κ) t (j + 1)) (c := c + 1) (by omega)
    (irreducible_of_unif S.unif) S.cond hν (stdLat k (XIx (Fin κ) t j))).1 (S.μ (j + 1))
    ((S.T t).Phi j (c + 1) (by omega)) ((Chain.ofType_regular _ _ _ _ _).1 j (c + 1) _) (by
      intro x hx
      change MapsInto x (chainLat p _ _) (chainLat p _ _)
      rw [e, e', mapsInto_latOf_iff]
      rw [hΦ] at hx
      intro a b
      simpa [LatFrame.coords, typeFrame] using
        TypeDatum.intM_of_Phi_ne_zero _ _ hx ((ixSucc _ t j).symm (o.symm a)) (o'.symm b)) (by
      intro x y hy
      change MapsInto y (chainLat p _ _) (chainLat p _ _) at hy
      rw [e, e', mapsInto_latOf_iff] at hy
      rw [hΦ, hΦ]
      have : ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') (x + (S.ϖ : k) • y)).submatrix (ixSucc _ t j) id =
          ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x).submatrix (ixSucc _ t j) id +
          (S.ϖ : k) • ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') y).submatrix (ixSucc _ t j) id := by
        simp only [LatFrame.coords, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
        rfl
      refine (congrArg _ this).trans (TypeDatum.Phi_add _ (S.tame _) _ fun a b => ?_)
      rw [Matrix.smul_apply, smul_eq_mul, map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 (hy _ _)) 1 h (act_one _) hf
  refine ⟨r, hr, u, mem_stabLat_iff.2 ?_, hh⟩
  change act u (chainLat p _ _) = chainLat p _ _ at hu
  rw [e, act_latOf] at hu
  exact hu

end GlobalTheory.SymChain.LatClass
