import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import ReciprocityTheory.DualLattices.PrimeHopfOrderOfAddEquiv
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

section

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X Y : Type} [AddCommGroup X] [Fintype X] [DecidableEq X]
  [AddCommGroup Y] [Fintype Y] [DecidableEq Y]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
/- English proof (translation)
Establish `h : ∀ a b : Y, f (a + b) - f a - f b ∈ pInt R p` using `hf`. Use `show ∀ a b : X, f (e (a + b)) - f (e a) - f (e b) ∈ pInt R p`. Introduce `a b`. Rewrite using `[map_add]`. Conclude with `h (e a) (e b)`.
-/
lemma comp_mem_addFun (p : ℕ) (e : X ≃+ Y) {f : Y → C} (hf : f ∈ addFun R p Y) :
    (fun x => f (e x)) ∈ addFun R p X := by
  have h : ∀ a b : Y, f (a + b) - f a - f b ∈ pInt R p := hf
  show ∀ a b : X, f (e (a + b)) - f (e a) - f (e b) ∈ pInt R p
  intro a b
  rw [map_add]
  exact h (e a) (e b)

/- English proof (translation)
Use extensionality with `g`. Rewrite using `[Submodule.mem_map_equiv]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h3` using `h1 _ h`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Rewrite using `[pbE_symm_apply]`. Simplify using the standard rewrite rules. Introduce `h`.

Use `h2 g h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `y`. Conclude with `pbE_symm_apply e g y`.
-/
private theorem map_pbE_eq_of_addEquiv (e : X ≃+ Y) (SX : Submodule R (X → C)) (SY : Submodule R (Y → C))
    (h1 : ∀ f ∈ SY, (fun x => f (e x)) ∈ SX) (h2 : ∀ g ∈ SX, (fun y => g (e.symm y)) ∈ SY) :
    SY.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = SX := by
  ext g
  rw [Submodule.mem_map_equiv]
  constructor
  · intro h
    have h3 := h1 _ h
    convert h3 using 1
    funext x
    rw [pbE_symm_apply]
    simp
  · intro h
    convert h2 g h using 1
    funext y
    exact pbE_symm_apply e g y

/- English proof (translation)
Conclude with `map_pbE_eq_of_addEquiv e _ _ (fun f hf => comp_mem_addFun p e hf) (fun g hg => comp_mem_addFun p e.symm hg)`.
-/
lemma map_addFun (p : ℕ) (e : X ≃+ Y) :
    (addFun R p Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = addFun R p X := by
  exact map_pbE_eq_of_addEquiv e _ _ (fun f hf => comp_mem_addFun p e hf) (fun g hg => comp_mem_addFun p e.symm hg)

/- English proof (translation)
Use `map_pbE_eq_of_addEquiv e _ _ ?_ ?_` and prove the remaining obligations. Introduce `f hf`. Establish `h : ∀ y : Y, ∃ r : R, algebraMap R C r = f y` using `hf`. Use `show ∀ x : X, ∃ r : R, algebraMap R C r = f (e x)`. Conclude with `fun x => h (e x)`.

Introduce `g hg`. Establish `h : ∀ x : X, ∃ r : R, algebraMap R C r = g x` using `hg`. Use `show ∀ y : Y, ∃ r : R, algebraMap R C r = g (e.symm y)`. Conclude with `fun y => h (e.symm y)`.
-/
lemma map_intFun (e : X ≃+ Y) :
    (intFun R Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = intFun R X := by
  refine map_pbE_eq_of_addEquiv e _ _ ?_ ?_
  · intro f hf
    have h : ∀ y : Y, ∃ r : R, algebraMap R C r = f y := hf
    show ∀ x : X, ∃ r : R, algebraMap R C r = f (e x)
    exact fun x => h (e x)
  · intro g hg
    have h : ∀ x : X, ∃ r : R, algebraMap R C r = g x := hg
    show ∀ y : Y, ∃ r : R, algebraMap R C r = g (e.symm y)
    exact fun y => h (e.symm y)

/- English proof (translation)
Use `map_pbE_eq_of_addEquiv e _ _ ?_ ?_` and prove the remaining obligations. Introduce `f hf`. Simplify using `only [pFun, Submodule.mem_pi, Set.mem_univ, true_implies] at hf ⊢`. Conclude with `fun x => hf (e x)`. Introduce `g hg`.

Simplify using `only [pFun, Submodule.mem_pi, Set.mem_univ, true_implies] at hg ⊢`. Conclude with `fun y => hg (e.symm y)`.
-/
lemma map_pFun (p : ℕ) (e : X ≃+ Y) :
    (pFun R p Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = pFun R p X := by
  refine map_pbE_eq_of_addEquiv e _ _ ?_ ?_
  · intro f hf
    simp only [pFun, Submodule.mem_pi, Set.mem_univ, true_implies] at hf ⊢
    exact fun x => hf (e x)
  · intro g hg
    simp only [pFun, Submodule.mem_pi, Set.mem_univ, true_implies] at hg ⊢
    exact fun y => hg (e.symm y)

/- English proof (translation)
Use `show Submodule.map _ (M ⊓ addFun R p Y) = _ ⊓ addFun R p X`. Rewrite using `[Submodule.map_inf, map_addFun]`. Conclude with `(pbE (C := C) (R := R) e).injective`.
-/
lemma map_afFun (p : ℕ) (e : X ≃+ Y) (M : Submodule R (Y → C)) :
    (afFun p M).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) =
      afFun p (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) := by
  show Submodule.map _ (M ⊓ addFun R p Y) = _ ⊓ addFun R p X
  rw [Submodule.map_inf, map_addFun]
  exact (pbE (C := C) (R := R) e).injective

/- English proof (translation)
Use `show Submodule.map _ (intFun R Y ⊓ addFun R p Y) = intFun R X ⊓ addFun R p X`. Rewrite using `[Submodule.map_inf, map_intFun, map_addFun]`. Conclude with `(pbE (C := C) (R := R) e).injective`.
-/
lemma map_linFun (p : ℕ) (e : X ≃+ Y) :
    (linFun R p Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = linFun R p X := by
  show Submodule.map _ (intFun R Y ⊓ addFun R p Y) = intFun R X ⊓ addFun R p X
  rw [Submodule.map_inf, map_intFun, map_addFun]
  exact (pbE (C := C) (R := R) e).injective

/- English proof (translation)
Use `⟨Submodule.Quotient.equiv _ _ (φ.submoduleMap L) ?_⟩` and prove the remaining obligations. Use extensionality with `⟨w, hw⟩`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨v, hv⟩, hvA, hvw⟩`. Establish `hw' : φ v = w` using `congrArg Subtype.val hvw`.

Simplify using `only [Submodule.mem_comap, Submodule.subtype_apply] at hvA ⊢`. Conclude with `⟨v, hvA, hw'⟩`. Introduce `h`. Simplify using `only [Submodule.mem_comap, Submodule.subtype_apply] at h`. Take `⟨v, hvA, rfl⟩` from `h`.

Take `⟨v', hv'L, hv'⟩` from `hw`. Establish `hvv : v' = v` using `φ.injective hv'`. Substitute `hvv` using the available equality. Conclude with `⟨⟨v', hv'L⟩, hvA, rfl⟩`.
-/
private theorem nonempty_quotient_linearEquiv_map {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (φ : V ≃ₗ[R] W) (L A : Submodule R V) :
    Nonempty ((↥L ⧸ Submodule.comap L.subtype A) ≃ₗ[R]
      (↥(L.map (φ : V →ₗ[R] W)) ⧸ Submodule.comap (L.map (φ : V →ₗ[R] W)).subtype (A.map (φ : V →ₗ[R] W)))) := by
  refine ⟨Submodule.Quotient.equiv _ _ (φ.submoduleMap L) ?_⟩
  ext ⟨w, hw⟩
  constructor
  · rintro ⟨⟨v, hv⟩, hvA, hvw⟩
    have hw' : φ v = w := congrArg Subtype.val hvw
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hvA ⊢
    exact ⟨v, hvA, hw'⟩
  · intro h
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at h
    obtain ⟨v, hvA, rfl⟩ := h
    obtain ⟨v', hv'L, hv'⟩ := hw
    have hvv : v' = v := φ.injective hv'
    subst hvv
    exact ⟨⟨v', hv'L⟩, hvA, rfl⟩

/- English proof (translation)
Take `⟨f⟩` from `nonempty_quotient_linearEquiv_map (pbE (C := C) (R := R) e) (linFun R p Y) (afFun p M ⊔ pFun R p Y)`. Rewrite `f` using `[map_linFun, Submodule.map_sup, map_afFun, map_pFun]`. Conclude with `⟨f⟩`.
-/
lemma afQuot_equiv (p : ℕ) (e : X ≃+ Y) (M : Submodule R (Y → C)) :
    Nonempty (AFQuot p M ≃ₗ[R]
      AFQuot p (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)))) := by
  obtain ⟨f⟩ := nonempty_quotient_linearEquiv_map (pbE (C := C) (R := R) e) (linFun R p Y) (afFun p M ⊔ pFun R p Y)
  rw [map_linFun, Submodule.map_sup, map_afFun, map_pFun] at f
  exact ⟨f⟩

end

/- English proof (translation)
The claim follows from `have : Module.Finite (ZMod p) N := Module.Finite.of_finite ⟨_, ⟨(Module.finBasis (ZMod p) N).equivFun.symm.toAddEquiv⟩⟩`.
-/
lemma exists_coord (p : ℕ) [Fact p.Prime] (N : Type) [AddCommGroup N] [Finite N]
    [Module (ZMod p) N] : ∃ n : ℕ, Nonempty ((Fin n → ZMod p) ≃+ N) :=
  have : Module.Finite (ZMod p) N := Module.Finite.of_finite
  ⟨_, ⟨(Module.finBasis (ZMod p) N).equivFun.symm.toAddEquiv⟩⟩

/- English proof (translation)
Establish `hinv : invFun M (⊥ : AddSubgroup N) = M`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(show g ∈ M ∧ ∀ x k : N, k ∈ (⊥ : AddSubgroup N) → g (x + k) = g x from h).1`.

Introduce `h show g ∈ M ∧ ∀ x k : N, k ∈ (⊥ : AddSubgroup N) → g (x + k) = g x`. Use `⟨h, ?_⟩` and prove the remaining obligations. Introduce `x k hk`. Rewrite `hk` using `[AddSubgroup.mem_bot]`. Substitute `hk` using the available equality.

Simplify using the standard rewrite rules. Use `show invFun M ⊥ ≤ Subalgebra.toSubmodule (Algebra.adjoin R (afFun p (invFun M ⊥) : Set (N → C)))`. Rewrite using `[hinv]`. Establish `hsp : Submodule.span R S ≤ Subalgebra.toSubmodule (Algebra.adjoin R (afFun p M : Set (N → C)))`. Rewrite using `[Submodule.span_le]`.

Introduce `s hs`. Take `⟨α, rfl⟩` from `hgen s hs`. Conclude with `(Subalgebra.mem_toSubmodule _).mpr (Subalgebra.prod_mem _ (fun j _ => Subalgebra.pow_mem _ (Algebra.subset_adjoin (hy j)) _))`. Introduce `g hg`. Rewrite `hg` using `[hS]`.

Conclude with `hsp hg`.
-/
private theorem genAF_bot_of_span_monomials {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
    {N : Type} [AddCommGroup N] (p : ℕ) {ι : Type} [Fintype ι] (M : Submodule R (N → C))
    (y : ι → N → C) (hy : ∀ j, y j ∈ afFun p M) (S : Set (N → C))
    (hS : M = Submodule.span R S) (hgen : ∀ s ∈ S, ∃ α : ι → ℕ, s = ∏ j, y j ^ α j) :
    GenAF p M ⊥ := by
  have hinv : invFun M (⊥ : AddSubgroup N) = M := by
    ext g
    constructor
    · intro h
      exact (show g ∈ M ∧ ∀ x k : N, k ∈ (⊥ : AddSubgroup N) → g (x + k) = g x from h).1
    · intro h
      show g ∈ M ∧ ∀ x k : N, k ∈ (⊥ : AddSubgroup N) → g (x + k) = g x
      refine ⟨h, ?_⟩
      intro x k hk
      rw [AddSubgroup.mem_bot] at hk
      subst hk
      simp
  show invFun M ⊥ ≤ Subalgebra.toSubmodule (Algebra.adjoin R (afFun p (invFun M ⊥) : Set (N → C)))
  rw [hinv]
  have hsp : Submodule.span R S ≤ Subalgebra.toSubmodule (Algebra.adjoin R (afFun p M : Set (N → C))) := by
    rw [Submodule.span_le]
    intro s hs
    obtain ⟨α, rfl⟩ := hgen s hs
    exact (Subalgebra.mem_toSubmodule _).mpr
      (Subalgebra.prod_mem _ (fun j _ => Subalgebra.pow_mem _ (Algebra.subset_adjoin (hy j)) _))
  intro g hg
  rw [hS] at hg
  exact hsp hg

/- English proof (translation)
Introduce `p _ C _ _ _ v R _ _ hvR hp N _ _ _ hN AA cA cN hA hC`. Use `letI : Module (ZMod p) N := AddCommGroup.zmodModule hN`. Take `⟨n, ⟨e⟩⟩` from `exists_coord p N`. Establish `hcard : Fintype.card (Fin n → ZMod p) = Fintype.card N` using `Fintype.card_congr e.toEquiv`. Take `⟨f⟩` from `afQuot_equiv (C := C) (R := R) p e AA.carrier`.

Establish `hA' : HasLen v R (AFQuot p (hopfPull e AA).carrier) cA`. Take `⟨m, c, ⟨g⟩, hc⟩` from `hA`. Conclude with `⟨m, c, ⟨f.symm.trans g⟩, hc⟩`. Establish `hC' : HasColen R v (hopfPull e AA).carrier cN` using `hasColen_map v e _ _ hC`. Take `⟨hle, heq⟩` from `hcoord p C v R hvR hp (Fin n) (hopfPull e AA) cA cN hA' hC'`.

Rewrite `hle`, `heq` using `[hcard]`. Use `⟨hle, fun hE => ?_⟩` and prove the remaining obligations. Take `⟨x, hxj, hspan⟩` from `heq hE`. Use `genAF_bot_of_span_monomials p AA.carrier (fun j z => x j (e.symm z)) ?_ ((⇑(pbE (C := C) (R := R) e.symm)) '' Set.range (fun (α : Fin n → ZMod p) (y : Fin n → ZMod p) => ∏ j, x j y ^ (α j).val)) ?_ ?_` and prove the remaining obligations. Introduce `j`.

Establish `hx' : x j ∈ (afFun p AA.carrier).map (pbE (C` using `C) (R := R) e : (N → C) →ₗ[R] ((Fin n → ZMod p) → C)) := by`. Rewrite using `[map_afFun]`. Conclude with `hxj j`. Establish `h2` using `(Submodule.mem_map_equiv _).mp hx'`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `z`. Rewrite using `[pbE_symm_apply]`. Establish `h1` using `Submodule.map_span (pbE (C := C) (R := R) e.symm : ((Fin n → ZMod p) → C) →ₗ[R] (N → C)) (Set.range fun (α : Fin n → ZMod p) (y : Fin n → ZMod p) => ∏ j, x j y ^ (α j).val)`. Rewrite `h1` using `[← hspan]`. Rewrite using `[← map_pbE_symm e AA.carrier]`.

Conclude with `h1`. Introduce and unpack `s ⟨_, ⟨α, rfl⟩, rfl⟩`. Use `⟨fun j => (α j).val, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Rewrite using `[Finset.prod_apply]`.

Both sides reduce to the same expression.
-/
theorem cnt_of (hcoord : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) = cN ^ 2 → ∃ x : ι → (ι → ZMod p) → C, (∀ j, x j ∈ afFun p AA.carrier) ∧ AA.carrier = Submodule.span R (Set.range fun (α : ι → ZMod p) (y : ι → ZMod p) => ∏ j, x j y ^ (α j).val))) :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card N * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card N * (p - 1)) = cN ^ 2 → GenAF p AA.carrier ⊥) := by
  intro p _ C _ _ _ v R _ _ hvR hp N _ _ _ hN AA cA cN hA hC
  letI : Module (ZMod p) N := AddCommGroup.zmodModule hN
  obtain ⟨n, ⟨e⟩⟩ := exists_coord p N
  have hcard : Fintype.card (Fin n → ZMod p) = Fintype.card N := Fintype.card_congr e.toEquiv
  obtain ⟨f⟩ := afQuot_equiv (C := C) (R := R) p e AA.carrier
  have hA' : HasLen v R (AFQuot p (hopfPull e AA).carrier) cA := by
    obtain ⟨m, c, ⟨g⟩, hc⟩ := hA
    exact ⟨m, c, ⟨f.symm.trans g⟩, hc⟩
  have hC' : HasColen R v (hopfPull e AA).carrier cN := hasColen_map v e _ _ hC
  obtain ⟨hle, heq⟩ := hcoord p C v R hvR hp (Fin n) (hopfPull e AA) cA cN hA' hC'
  rw [hcard] at hle heq
  refine ⟨hle, fun hE => ?_⟩
  obtain ⟨x, hxj, hspan⟩ := heq hE
  refine genAF_bot_of_span_monomials p AA.carrier (fun j z => x j (e.symm z)) ?_
    ((⇑(pbE (C := C) (R := R) e.symm)) '' Set.range
      (fun (α : Fin n → ZMod p) (y : Fin n → ZMod p) => ∏ j, x j y ^ (α j).val)) ?_ ?_
  · intro j
    have hx' : x j ∈ (afFun p AA.carrier).map
        (pbE (C := C) (R := R) e : (N → C) →ₗ[R] ((Fin n → ZMod p) → C)) := by
      rw [map_afFun]
      exact hxj j
    have h2 := (Submodule.mem_map_equiv _).mp hx'
    convert h2 using 1
    funext z
    rw [pbE_symm_apply]
  · have h1 := Submodule.map_span (pbE (C := C) (R := R) e.symm : ((Fin n → ZMod p) → C) →ₗ[R] (N → C))
      (Set.range fun (α : Fin n → ZMod p) (y : Fin n → ZMod p) => ∏ j, x j y ^ (α j).val)
    rw [← hspan] at h1
    rw [← map_pbE_symm e AA.carrier]
    exact h1
  · rintro s ⟨_, ⟨α, rfl⟩, rfl⟩
    refine ⟨fun j => (α j).val, ?_⟩
    funext z
    rw [Finset.prod_apply]
    rfl

end PositivityTheory.HtPt.Ra
