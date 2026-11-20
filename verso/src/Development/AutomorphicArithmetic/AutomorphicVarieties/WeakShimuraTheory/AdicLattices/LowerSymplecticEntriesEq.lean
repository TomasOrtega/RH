import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.CompanionTheory
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Lat

namespace UpperTheory.V.Ws.Lat

/- English proof (translation)
Take `⟨hg, hd, hu⟩` from `h`. Establish `e32` using `congrFun (congrFun hg 3) 2`. Establish `e31` using `congrFun (congrFun hg 3) 1`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, hd, Fin.rev] at e32 e31`. Establish `a` using `hu 1 2 (by decide)`.

Establish `b` using `hu 0 1 (by decide)`. Establish `c` using `hu 0 2 (by decide)`. Rewrite `e32` using `[a, c]`. Rewrite `e31` using `[b]`. Prove the components needed by the constructor for the conclusion.

Take the linear combination `e32`. Take the linear combination `e31`.
-/
private theorem lower_symplectic_entries_eq {R : Type} [CommRing R] {X : M4 R} (h : IsLow X) : X 3 2 = -X 1 0 ∧ X 3 1 = X 2 0 - X 1 0 * X 2 1 := by
  obtain ⟨hg, hd, hu⟩ := h
  have e32 := congrFun (congrFun hg 3) 2
  have e31 := congrFun (congrFun hg 3) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, hd, Fin.rev] at e32 e31
  have a := hu 1 2 (by decide)
  have b := hu 0 1 (by decide)
  have c := hu 0 2 (by decide)
  rw [a, c] at e32
  rw [b] at e31
  constructor
  · linear_combination e32
  · linear_combination e31

/- English proof (translation)
Establish `hA` using `hw (-wAl) (by simp [nM])`. Establish `hB` using `hw (-wBe) (by simp [nM])`. Establish `hP` using `hw (-wPs) (by simp [nM])`. Establish `hT` using `hw (-wTh) (by simp [nM])`. Simplify using `[nCo, wAl, wBe, wPs, wTh, wv] at hA hB hP hT`.

Take `⟨l1, l2⟩` from `lower_symplectic_entries_eq h`. Take `⟨_, hd, hu⟩` from `h`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [wt, lamW, muW, wv, hd, hu]`. Conclude with `hA`. Conclude with `hP`.

Conclude with `hB`. Conclude with `hT`. Rewrite using `[l2]`. Establish `h1 : (t.1 : K) ≠ 0` using `t.1.ne_zero`. Establish `e : (↑t.2)⁻¹ * ((↑(X 2 0 - X 1 0 * X 2 1 : V) : K)) = (↑t.2)⁻¹ * ↑(X 2 0) - ((↑t.1)⁻¹ * ↑(X 1 0)) * (↑t.1 * (↑t.2)⁻¹ * ↑(X 2 1))`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `sub_mem hP (mul_mem hA hB)`. Rewrite using `[l1]`.

Use `push_cast`. Rewrite using `[mul_neg]`. Conclude with `neg_mem hA`.
-/
private theorem lowMem {K : Type} [Field K] (V : ValuationSubring K) (t : Kˣ × Kˣ) {X : M4 V} (h : IsLow X)
    (hw : ∀ w ∈ nM, (wv t w : K) * ((nCo X w : V) : K) ∈ V) (i j : Fin 4) : (wv t (wt i j) : K) * (X i j : K) ∈ V := by
  have hA := hw (-wAl) (by simp [nM])
  have hB := hw (-wBe) (by simp [nM])
  have hP := hw (-wPs) (by simp [nM])
  have hT := hw (-wTh) (by simp [nM])
  simp [nCo, wAl, wBe, wPs, wTh, wv] at hA hB hP hT
  obtain ⟨l1, l2⟩ := lower_symplectic_entries_eq h
  obtain ⟨_, hd, hu⟩ := h
  fin_cases i <;> fin_cases j <;> simp [wt, lamW, muW, wv, hd, hu]
  · exact hA
  · exact hP
  · exact hB
  · exact hT
  · rw [l2]
    have h1 : (t.1 : K) ≠ 0 := t.1.ne_zero
    have e : (↑t.2)⁻¹ * ((↑(X 2 0 - X 1 0 * X 2 1 : V) : K))
        = (↑t.2)⁻¹ * ↑(X 2 0) - ((↑t.1)⁻¹ * ↑(X 1 0)) * (↑t.1 * (↑t.2)⁻¹ * ↑(X 2 1)) := by
      push_cast
      field_simp
    rw [e]
    exact sub_mem hP (mul_mem hA hB)
  · rw [l1]
    push_cast
    rw [mul_neg]
    exact neg_mem hA

end UpperTheory.V.Ws.Lat

/- English proof (translation)
Introduce `ι Γ K _ _ V t P hl hr hn`. Simplify using `only [ValuationSubring.valuation_le_one_iff] at hr hn`. Take `⟨-, -, -, -, -, -, -, -, hmul, hone, -⟩` from `grp K`. Set `r : Γ → M4 V` to `fun g => Matrix.of fun i j => ⟨_, hr g i j⟩`. Establish `hrm : ∀ g, (r g).map V.subtype = tconj t ((P.r g).map V.subtype)` using `fun g => rfl`.

Establish `inj : Function.Injective fun X : M4 V => X.map V.subtype` using `Matrix.map_injective V.subtype_injective`. Establish `h1 : (1 : M4 V).map V.subtype = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Use `⟨⟨⟨⟨r, inj ?_⟩, fun g h => inj ?_⟩, fun v => Matrix.of fun i j => ⟨_, lowMem V t (hl v) (hn v) i j⟩⟩, fun g => rfl, fun v => rfl⟩` and prove the remaining obligations. Use `show (r 1).map V.subtype = (1 : M4 V).map V.subtype`. Rewrite using `[hrm, map_one, h1, hone]`.

Use `show (r (g * h)).map V.subtype = (r g * r h).map V.subtype`. Rewrite using `[Matrix.map_mul, hrm, hrm, hrm, map_mul, Matrix.map_mul, hmul]`.
-/
theorem UpperTheory.V.Ws.Lat.tcEx :
    ∀ {ι Γ K : Type} [Group Γ] [Field K] (V : ValuationSubring K) (t : Kˣ × Kˣ) (P : PD ι Γ V), (∀ v, IsLow (P.n v)) →
      (∀ g i j, V.valuation ((wv t (wt i j) : K) * (P.r g i j : K)) ≤ 1) →
      (∀ v, ∀ w ∈ nM, V.valuation ((wv t w : K) * ((nCo (P.n v) w : V) : K)) ≤ 1) → ∃ P' : PD ι Γ V, TConj V.subtype t P P' := by
  intro ι Γ K _ _ V t P hl hr hn
  simp only [ValuationSubring.valuation_le_one_iff] at hr hn
  obtain ⟨-, -, -, -, -, -, -, -, hmul, hone, -⟩ := grp K
  let r : Γ → M4 V := fun g => Matrix.of fun i j => ⟨_, hr g i j⟩
  have hrm : ∀ g, (r g).map V.subtype = tconj t ((P.r g).map V.subtype) := fun g => rfl
  have inj : Function.Injective fun X : M4 V => X.map V.subtype := Matrix.map_injective V.subtype_injective
  have h1 : (1 : M4 V).map V.subtype = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨⟨⟨r, inj ?_⟩, fun g h => inj ?_⟩, fun v => Matrix.of fun i j => ⟨_, lowMem V t (hl v) (hn v) i j⟩⟩,
    fun g => rfl, fun v => rfl⟩
  · show (r 1).map V.subtype = (1 : M4 V).map V.subtype
    rw [hrm, map_one, h1, hone]
  · show (r (g * h)).map V.subtype = (r g * r h).map V.subtype
    rw [Matrix.map_mul, hrm, hrm, hrm, map_mul, Matrix.map_mul, hmul]
