import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

/- English proof (translation)
Introduce `h`. Establish `h1 : -(a : ℂ) = a` using `by simpa using congrArg Units.val h`. Establish `h2 : (a : ℂ) = 0` using `by linear_combination (-1 / 2 : ℂ) * h1`. Conclude with `a.ne_zero h2`.
-/
private theorem neg_ne_self_unit (a : ℂˣ) : -a ≠ a := by
  intro h
  have h1 : -(a : ℂ) = a := by simpa using congrArg Units.val h
  have h2 : (a : ℂ) = 0 := by linear_combination (-1 / 2 : ℂ) * h1
  exact a.ne_zero h2

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `A hA _`. Establish `: A = 0` using `Multiset.card_eq_zero.1 (Nat.le_zero.1 hA)`. Conclude with `⟨0, by simp [this]⟩`.

Consider the case `succ n ih`. Introduce `A hA hs`. Distinguish the cases in `h0 : A = 0`. Conclude with `⟨0, by simp [h0]⟩`. Take `⟨a, ha⟩` from `Multiset.exists_mem_of_ne_zero h0`.

Establish `hna : -a ∈ A`. Rewrite using `[← hs]`. Conclude with `Multiset.mem_map_of_mem _ ha`. Take `⟨A₁, rfl⟩` from `Multiset.exists_cons_of_mem ha`. Establish `hna₁ : -a ∈ A₁` using `(Multiset.mem_cons.1 hna).resolve_left (neg_ne_self_unit a)`.

Take `⟨C, rfl⟩` from `Multiset.exists_cons_of_mem hna₁`. Establish `hC : C.map (fun x => -x) = C`. Rewrite `hs` using `[Multiset.map_cons, Multiset.map_cons, neg_neg, Multiset.cons_swap]`. Conclude with `(Multiset.cons_inj_right _).1 ((Multiset.cons_inj_right _).1 hs)`. Establish `hc : C.card ≤ n`.

Simplify using `only [Multiset.card_cons] at hA`. Use linear arithmetic over natural numbers and integers. Take `⟨B', hB'⟩` from `ih C hc hC`. Use `⟨a ::ₘ B', ?_⟩` and prove the remaining obligations. Rewrite using `[Multiset.map_cons, Multiset.cons_add, Multiset.add_cons, ← hB']`.
-/
private theorem half_of_neg_stable (n : ℕ) : ∀ A : Multiset ℂˣ, A.card ≤ n → A.map (fun x => -x) = A →
    ∃ B' : Multiset ℂˣ, A = B' + B'.map fun b => -b := by
  induction n with
  | zero =>
    intro A hA _
    have : A = 0 := Multiset.card_eq_zero.1 (Nat.le_zero.1 hA)
    exact ⟨0, by simp [this]⟩
  | succ n ih =>
    intro A hA hs
    by_cases h0 : A = 0
    · exact ⟨0, by simp [h0]⟩
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero h0
    have hna : -a ∈ A := by
      rw [← hs]
      exact Multiset.mem_map_of_mem _ ha
    obtain ⟨A₁, rfl⟩ := Multiset.exists_cons_of_mem ha
    have hna₁ : -a ∈ A₁ := (Multiset.mem_cons.1 hna).resolve_left (neg_ne_self_unit a)
    obtain ⟨C, rfl⟩ := Multiset.exists_cons_of_mem hna₁
    have hC : C.map (fun x => -x) = C := by
      rw [Multiset.map_cons, Multiset.map_cons, neg_neg, Multiset.cons_swap] at hs
      exact (Multiset.cons_inj_right _).1 ((Multiset.cons_inj_right _).1 hs)
    have hc : C.card ≤ n := by
      simp only [Multiset.card_cons] at hA
      omega
    obtain ⟨B', hB'⟩ := ih C hc hC
    refine ⟨a ::ₘ B', ?_⟩
    rw [Multiset.map_cons, Multiset.cons_add, Multiset.add_cons, ← hB']

/- English proof (translation)
Introduce `A B _ _ hs hq`. Take `⟨B', hB'⟩` from `half_of_neg_stable _ A le_rfl hs`. Use `⟨B', ?_, hB'⟩` and prove the remaining obligations. Establish `h : B'.map (· ^ 2) + B'.map (· ^ 2) = B + B`. Rewrite using `[← hq, hB', Multiset.map_add, Multiset.map_map]`.

Use `congr 1`. Conclude with `Multiset.map_congr rfl fun x _ => by simp`. Use extensionality with `x`. Use `congrArg (Multiset.count x) h` as an intermediate fact. Simplify using `only [Multiset.count_add] at this`.

Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.signMs :
    SignMs := by
  intro A B _ _ hs hq
  obtain ⟨B', hB'⟩ := half_of_neg_stable _ A le_rfl hs
  refine ⟨B', ?_, hB'⟩
  have h : B'.map (· ^ 2) + B'.map (· ^ 2) = B + B := by
    rw [← hq, hB', Multiset.map_add, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun x _ => by simp
  ext x
  have := congrArg (Multiset.count x) h
  simp only [Multiset.count_add] at this
  omega
