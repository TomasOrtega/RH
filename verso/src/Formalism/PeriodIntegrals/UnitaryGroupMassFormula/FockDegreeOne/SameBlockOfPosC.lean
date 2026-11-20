import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.RedDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.FockInnerEqSumRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.RaisingLoweringSplit

noncomputable section

open Matrix FockH1Action MvPolynomial FockRaiseLowInner

namespace PI.FockOneDegW

/- English proof (translation)
Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp_all [posC, sameBlock]`.
-/
theorem sameBlock_of_posC {p q : ℕ} {a b : Ix p q} (h : posC a b) : sameBlock a b := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [posC, sameBlock]

/- English proof (translation)
Introduce `x y hxy`. Simplify using `only [Eab, Matrix.single_apply]`. Use `split_ifs with h'`. Take `⟨rfl, rfl⟩` from `h'`. Conclude with `absurd h hxy`.

Both sides reduce to the same expression.
-/
theorem isKC_Eab {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  intro x y hxy
  simp only [Eab, Matrix.single_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'
    exact absurd h hxy
  · rfl

def harmSub (hS : HarmSub) (p q r s : ℕ) : Submodule ℂ (Pol p q r s) where
  carrier := {P | Harm2 P}
  zero_mem' := (hS p q r s).1
  add_mem' := fun ha hb => (hS p q r s).2.1 _ _ ha hb
  smul_mem' := fun c _ h => (hS p q r s).2.2 c _ h

def innerL {σ : Type} (x : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] ℂ where
  toFun Q := fockInner x Q
  map_add' Q Q' := fockInner_add_right x Q Q'
  map_smul' c Q := by simp [fockInner_smul_right]

/- English proof (translation)
Establish `: FiniteDimensional ℂ N` using `Submodule.finiteDimensional_of_le hNV.le`. Use `set k := Module.finrank ℂ N`. Set `b` to `Module.finBasis ℂ N`. Set `Φ : MvPolynomial σ ℂ →ₗ[ℂ] (Fin k → ℂ)` to `LinearMap.pi (fun i => innerL ((b i : N) : MvPolynomial σ ℂ))`. Set `Ψ` to `Φ.domRestrict V`.

Establish `h1` using `LinearMap.finrank_range_add_finrank_ker Ψ`. Establish `h2 : Module.finrank ℂ (LinearMap.range Ψ) ≤ k`. Use `Submodule.finrank_le (LinearMap.range Ψ)` as an intermediate fact. Simplify `this` using `[Module.finrank_fin_fun]`. Establish `h3 : k < Module.finrank ℂ V` using `Submodule.finrank_lt_finrank_of_lt hNV`.

Establish `h4 : LinearMap.ker Ψ ≠ ⊥`. Introduce `h`. Rewrite `h1` using `[h, finrank_bot]`. Use linear arithmetic over natural numbers and integers. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h4`.

Use `⟨(x : MvPolynomial σ ℂ), x.2, fun h => hx0 (Subtype.ext h), fun n hn => ?_⟩` and prove the remaining obligations. Establish `hx' : ∀ i, fockInner ((b i : N) : MvPolynomial σ ℂ) (x : MvPolynomial σ ℂ) = 0`. Introduce `i`. Use `congrFun (LinearMap.mem_ker.mp hx) i` as an intermediate fact. Simplify `this` using `[Ψ, Φ, innerL]`.

Establish `hsum` using `b.sum_repr ⟨n, hn⟩`. Establish `hn' : n = ∑ i, (b.repr ⟨n, hn⟩ i) • ((b i : N) : MvPolynomial σ ℂ)` using `by conv_lhs => rw [show n = ((⟨n, hn⟩ : N) : MvPolynomial σ ℂ) from rfl, ← hsum]`. Rewrite using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul]`. Rewrite using `[hn', fockInner_sum_left]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[fockInner_smul_left, hx' i, mul_zero]`.
-/
theorem exists_orth {σ : Type} {V N : Submodule ℂ (MvPolynomial σ ℂ)} [FiniteDimensional ℂ V]
    (hNV : N < V) : ∃ c ∈ V, c ≠ 0 ∧ ∀ n ∈ N, fockInner n c = 0 := by
  classical
  have : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le hNV.le
  set k := Module.finrank ℂ N
  let b := Module.finBasis ℂ N
  let Φ : MvPolynomial σ ℂ →ₗ[ℂ] (Fin k → ℂ) := LinearMap.pi (fun i => innerL ((b i : N) : MvPolynomial σ ℂ))
  let Ψ := Φ.domRestrict V
  have h1 := LinearMap.finrank_range_add_finrank_ker Ψ
  have h2 : Module.finrank ℂ (LinearMap.range Ψ) ≤ k := by
    have := Submodule.finrank_le (LinearMap.range Ψ)
    simpa [Module.finrank_fin_fun] using this
  have h3 : k < Module.finrank ℂ V := Submodule.finrank_lt_finrank_of_lt hNV
  have h4 : LinearMap.ker Ψ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h1
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h4
  refine ⟨(x : MvPolynomial σ ℂ), x.2, fun h => hx0 (Subtype.ext h), fun n hn => ?_⟩
  have hx' : ∀ i, fockInner ((b i : N) : MvPolynomial σ ℂ) (x : MvPolynomial σ ℂ) = 0 := by
    intro i
    have := congrFun (LinearMap.mem_ker.mp hx) i
    simpa [Ψ, Φ, innerL] using this
  have hsum := b.sum_repr ⟨n, hn⟩
  have hn' : n = ∑ i, (b.repr ⟨n, hn⟩ i) • ((b i : N) : MvPolynomial σ ℂ) := by
    conv_lhs => rw [show n = ((⟨n, hn⟩ : N) : MvPolynomial σ ℂ) from rfl, ← hsum]
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
  rw [hn', fockInner_sum_left]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [fockInner_smul_left, hx' i, mul_zero]

/- English proof (translation)
Set `V : Submodule ℂ (Pol p q r s)` to `W ⊓ harmSub hS p q r s`. Set `N : Submodule ℂ (Pol p q r s)` to `V ⊓ LinearMap.ker (homogeneousComponent e : Pol p q r s →ₗ[ℂ] Pol p q r s)`. Use `haveI : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le inf_le_left`. Establish `hVst : ∀ a b : Ix p q, sameBlock a b → ∀ u ∈ V, fockAct1 p q r s (Eab a b) u ∈ V`. Introduce `a b hab u hu`.

Conclude with `⟨hWK _ (isKC_Eab hab) u hu.1, hKh p q r s a b hab u hu.2⟩`. Establish `hNst : ∀ a b : Ix p q, sameBlock a b → ∀ u ∈ N, fockAct1 p q r s (Eab a b) u ∈ N`. Introduce `a b hab u hu`. Use `⟨hVst a b hab u hu.1, ?_⟩` and prove the remaining obligations. Establish `h0 : homogeneousComponent e u = 0` using `hu.2`.

Use `show homogeneousComponent e (fockAct1 p q r s (Eab a b) u) = 0`. Rewrite using `[hKc p q r s a b hab e u, h0, map_zero]`. Set `C : Submodule ℂ (Pol p q r s)` to `{ carrier := {c | c ∈ V ∧ ∀ n ∈ N, fockInner n c = 0} add_mem' := by`. Introduce and unpack `x y ⟨hx, hx'⟩ ⟨hy, hy'⟩`. Use `⟨V.add_mem hx hy, fun n hn => ?_⟩` and prove the remaining obligations.

Rewrite using `[fockInner_add_right, hx' n hn, hy' n hn, add_zero]`. Use the proof step `zero_mem' := ⟨V.zero_mem, fun n _ => fockInner_zero_right n⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c x ⟨hx, hx'⟩`. Use `⟨V.smul_mem c hx, fun n hn => ?_⟩` and prove the remaining obligations.

Rewrite using `[fockInner_smul_right, hx' n hn, mul_zero] }`. Establish `hPV : P ∈ V` using `⟨hPW, hH⟩`. Establish `hPN : P ∉ N` using `fun h => he h.2`. Establish `hNV : N < V` using `lt_of_le_of_ne inf_le_left (fun h => hPN (h ▸ hPV))`. Take `⟨c0, hc0V, hc0, hc0N⟩` from `exists_orth hNV`.

Establish `hCne : C ≠ ⊥`. Introduce `h`. Establish `: c0 ∈ C` using `⟨hc0V, hc0N⟩`. Rewrite `this` using `[h, Submodule.mem_bot]`. Conclude with `hc0 this`.

Use `haveI : FiniteDimensional ℂ C := Submodule.finiteDimensional_of_le (show C ≤ V from fun x hx => hx.1)`. Establish `hCst : ∀ a b : Ix p q, sameBlock a b → ∀ u ∈ C, fockAct1 p q r s (Eab a b) u ∈ C`. Introduce `a b hab u hu`. Use `⟨hVst a b hab u hu.1, fun n hn => ?_⟩` and prove the remaining obligations. Rewrite using `[hA p q r s a b hab n u]`.

Establish `hba : sameBlock b a`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]`. Conclude with `hu.2 _ (hNst b a hba n hn)`. Take `⟨ν, v, hvC, hv0, hvhw⟩` from `hE p q r s C inferInstance hCne hCst`. Establish `hνμ : ν = μ` using `hWhw ν v hvC.1.1 ⟨hv0, hvhw⟩`.

Substitute `hνμ` using the available equality. Establish `hve : homogeneousComponent e v ≠ 0`. Introduce `h`. Establish `hvN : v ∈ N` using `⟨hvC.1, h⟩`. Use `hvC.2 v hvN` as an intermediate fact.

Conclude with `hv0 ((hI _ v v v 0).2.2.2.2.1 this)`. Establish `hwt : ∀ a : Ix p q, fockAct1 p q r s (Eab a a) v = ((ν a : ℚ) : ℂ) • v`. Introduce `a`. Use `(Submodule.mem_iInf _).mp hvhw.1 a` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`.

Simplify using `using this`. Establish `hraise : ∀ a b : Ix p q, posC a b → fockAct1 p q r s (Eab a b) v = 0`. Introduce `a b hab`. Establish `h1` using `(Submodule.mem_iInf _).mp hvhw.2 a`. Establish `h2` using `(Submodule.mem_iInf _).mp h1 b`.

Establish `h3` using `(Submodule.mem_iInf _).mp h2 hab`. Conclude with `LinearMap.mem_ker.mp h3`. Establish `hsame : ∀ a : Ix p q, sameBlock a a`. Apply the tactic sequence `intro a; rcases a with a | a <;> simp [sameBlock]`. Establish `hHW : IsHW (fockAct1 p q r s) ν (homogeneousComponent e v)`.

Use `⟨hve, ?_, ?_⟩` and prove the remaining obligations. Use `(Submodule.mem_iInf _).mpr fun a => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, ← hKc p q r s a a (hsame a) e v, hwt a, map_smul, LinearMap.smul_apply, LinearMap.id_apply, sub_self]`. Use `(Submodule.mem_iInf _).mpr fun a => (Submodule.mem_iInf _).mpr fun b => (Submodule.mem_iInf _).mpr fun hab => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, ← hKc p q r s a b (sameBlock_of_posC hab) e v, hraise a b hab, map_zero]`.

Establish `hhom : homogeneousComponent e v ∈ homog (Ix p q × Ix r s) e` using `(mem_homogeneousSubmodule _ _).mpr (homogeneousComponent_isHomogeneous e v)`. Conclude with `hT p q r s ν e _ hhom hHW (hHc p q r s e v hvC.1.2)`.
-/
theorem key_of (hI : InnerFacts) (hKc : KHc) (hKh : KHarm) (hHc : HcHarm) (hS : HarmSub)
    (hA : KAdj) (hE : HwExist) (hT : HwHarmDeg)
    {p q r s : ℕ} (μ : Ix p q → ℚ) (W : Submodule ℂ (Pol p q r s)) [FiniteDimensional ℂ W]
    (hWK : KStable (fockAct1 p q r s) W)
    (hWhw : ∀ (ν : Ix p q → ℚ) (w : Pol p q r s), w ∈ W → IsHW (fockAct1 p q r s) ν w → ν = μ)
    (P : Pol p q r s) (hPW : P ∈ W) (hH : Harm2 P) (e : ℕ)
    (he : homogeneousComponent e P ≠ 0) :
    (e : ℚ) = degW (cPair r s) μ := by
  classical
  let V : Submodule ℂ (Pol p q r s) := W ⊓ harmSub hS p q r s
  let N : Submodule ℂ (Pol p q r s) :=
    V ⊓ LinearMap.ker (homogeneousComponent e : Pol p q r s →ₗ[ℂ] Pol p q r s)
  haveI : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le inf_le_left
  have hVst : ∀ a b : Ix p q, sameBlock a b → ∀ u ∈ V, fockAct1 p q r s (Eab a b) u ∈ V := by
    intro a b hab u hu
    exact ⟨hWK _ (isKC_Eab hab) u hu.1, hKh p q r s a b hab u hu.2⟩
  have hNst : ∀ a b : Ix p q, sameBlock a b → ∀ u ∈ N, fockAct1 p q r s (Eab a b) u ∈ N := by
    intro a b hab u hu
    refine ⟨hVst a b hab u hu.1, ?_⟩
    have h0 : homogeneousComponent e u = 0 := hu.2
    show homogeneousComponent e (fockAct1 p q r s (Eab a b) u) = 0
    rw [hKc p q r s a b hab e u, h0, map_zero]
  let C : Submodule ℂ (Pol p q r s) :=
    { carrier := {c | c ∈ V ∧ ∀ n ∈ N, fockInner n c = 0}
      add_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨V.add_mem hx hy, fun n hn => ?_⟩
        rw [fockInner_add_right, hx' n hn, hy' n hn, add_zero]
      zero_mem' := ⟨V.zero_mem, fun n _ => fockInner_zero_right n⟩
      smul_mem' := by
        rintro c x ⟨hx, hx'⟩
        refine ⟨V.smul_mem c hx, fun n hn => ?_⟩
        rw [fockInner_smul_right, hx' n hn, mul_zero] }
  have hPV : P ∈ V := ⟨hPW, hH⟩
  have hPN : P ∉ N := fun h => he h.2
  have hNV : N < V := lt_of_le_of_ne inf_le_left (fun h => hPN (h ▸ hPV))
  obtain ⟨c0, hc0V, hc0, hc0N⟩ := exists_orth hNV
  have hCne : C ≠ ⊥ := by
    intro h
    have : c0 ∈ C := ⟨hc0V, hc0N⟩
    rw [h, Submodule.mem_bot] at this
    exact hc0 this
  haveI : FiniteDimensional ℂ C :=
    Submodule.finiteDimensional_of_le (show C ≤ V from fun x hx => hx.1)
  have hCst : ∀ a b : Ix p q, sameBlock a b → ∀ u ∈ C, fockAct1 p q r s (Eab a b) u ∈ C := by
    intro a b hab u hu
    refine ⟨hVst a b hab u hu.1, fun n hn => ?_⟩
    rw [hA p q r s a b hab n u]
    have hba : sameBlock b a := by
      rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]
    exact hu.2 _ (hNst b a hba n hn)
  obtain ⟨ν, v, hvC, hv0, hvhw⟩ := hE p q r s C inferInstance hCne hCst
  have hνμ : ν = μ := hWhw ν v hvC.1.1 ⟨hv0, hvhw⟩
  subst hνμ

  have hve : homogeneousComponent e v ≠ 0 := by
    intro h
    have hvN : v ∈ N := ⟨hvC.1, h⟩
    have := hvC.2 v hvN
    exact hv0 ((hI _ v v v 0).2.2.2.2.1 this)
  have hwt : ∀ a : Ix p q, fockAct1 p q r s (Eab a a) v = ((ν a : ℚ) : ℂ) • v := by
    intro a
    have := (Submodule.mem_iInf _).mp hvhw.1 a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    simpa using this
  have hraise : ∀ a b : Ix p q, posC a b → fockAct1 p q r s (Eab a b) v = 0 := by
    intro a b hab
    have h1 := (Submodule.mem_iInf _).mp hvhw.2 a
    have h2 := (Submodule.mem_iInf _).mp h1 b
    have h3 := (Submodule.mem_iInf _).mp h2 hab
    exact LinearMap.mem_ker.mp h3
  have hsame : ∀ a : Ix p q, sameBlock a a := by
    intro a; rcases a with a | a <;> simp [sameBlock]
  have hHW : IsHW (fockAct1 p q r s) ν (homogeneousComponent e v) := by
    refine ⟨hve, ?_, ?_⟩
    · refine (Submodule.mem_iInf _).mpr fun a => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, ← hKc p q r s a a (hsame a) e v, hwt a,
        map_smul, LinearMap.smul_apply, LinearMap.id_apply, sub_self]
    · refine (Submodule.mem_iInf _).mpr fun a => (Submodule.mem_iInf _).mpr fun b =>
        (Submodule.mem_iInf _).mpr fun hab => ?_
      rw [LinearMap.mem_ker, ← hKc p q r s a b (sameBlock_of_posC hab) e v, hraise a b hab, map_zero]
  have hhom : homogeneousComponent e v ∈ homog (Ix p q × Ix r s) e :=
    (mem_homogeneousSubmodule _ _).mpr (homogeneousComponent_isHomogeneous e v)
  exact hT p q r s ν e _ hhom hHW (hHc p q r s e v hvC.1.2)

/- English proof (translation)
Introduce `hT p q r s μ P hP0 hOT hH`. Take `⟨W, hWfd, hPW, hWK, hWhw⟩` from `hOT`. Establish `key` using `fun e he => key_of hI hKc hKh hHc hS hA hE hT μ W hWK hWhw P hPW hH e he`. Choose the witnesses or unpack the hypotheses as in `⟨e, he⟩ : ∃ e, homogeneousComponent e P ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hP0 (FockRaiseLowGrade.eq_zero_of_hc P h)`. Use `⟨e, key e he, ?_⟩` and prove the remaining obligations. Establish `hother : ∀ e', e' ≠ e → homogeneousComponent e' P = 0`. Introduce `e' hne`.

Assume the negation of the conclusion as `h`. Establish `h1` using `key e' h`. Rewrite `h1` using `[← key e he]`. Conclude with `hne (by exact_mod_cast h1)`. Establish `hPe : P = homogeneousComponent e P`.

Establish `: P - homogeneousComponent e P = 0`. Apply `FockRaiseLowGrade.eq_zero_of_hc` to reduce the goal to its premises. Introduce `e'`. Rewrite using `[map_sub, FockRaiseLowGrade.hc_hc]`. Distinguish the cases in `h : e' = e`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, hother e' h, sub_zero]`. Conclude with `sub_eq_zero.mp this`. Rewrite using `[hPe]`.

Conclude with `(mem_homogeneousSubmodule _ _).mpr (homogeneousComponent_isHomogeneous e P)`.
-/
theorem reduction_of (hI : InnerFacts) (hKc : KHc) (hKh : KHarm) (hHc : HcHarm) (hS : HarmSub)
    (hA : KAdj) (hE : HwExist) : Reduction := by
  intro hT p q r s μ P hP0 hOT hH
  obtain ⟨W, hWfd, hPW, hWK, hWhw⟩ := hOT
  have key := fun e he => key_of hI hKc hKh hHc hS hA hE hT μ W hWK hWhw P hPW hH e he
  obtain ⟨e, he⟩ : ∃ e, homogeneousComponent e P ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP0 (FockRaiseLowGrade.eq_zero_of_hc P h)
  refine ⟨e, key e he, ?_⟩
  have hother : ∀ e', e' ≠ e → homogeneousComponent e' P = 0 := by
    intro e' hne
    by_contra h
    have h1 := key e' h
    rw [← key e he] at h1
    exact hne (by exact_mod_cast h1)
  have hPe : P = homogeneousComponent e P := by
    have : P - homogeneousComponent e P = 0 := by
      apply FockRaiseLowGrade.eq_zero_of_hc
      intro e'
      rw [map_sub, FockRaiseLowGrade.hc_hc]
      by_cases h : e' = e
      · subst h; simp
      · rw [if_neg h, hother e' h, sub_zero]
    exact sub_eq_zero.mp this
  rw [hPe]
  exact (mem_homogeneousSubmodule _ _).mpr (homogeneousComponent_isHomogeneous e P)

end PI.FockOneDegW
