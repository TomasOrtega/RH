import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLatAtIffHat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.LatSandwich

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Use `choose! n hn hn' using h`. Use `⟨∏ t ∈ s, n t, Finset.prod_pos fun t ht => hn t ht, fun m hm => ?_⟩` and prove the remaining obligations. Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem n (Finset.mem_coe.1 hx)`.

Rewrite using `[hk, mul_comm, mul_smul]`. Conclude with `M.nsmul_mem (hn' x (Finset.mem_coe.1 hx)) k`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul a x _ hx => rw [smul_comm]`. Conclude with `M.smul_mem a hx`.
-/
theorem exists_nsmul_le {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (s : Finset W) (M : Submodule (𝓞 E) W)
    (h : ∀ x ∈ s, ∃ k : ℕ, 0 < k ∧ k • x ∈ M) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ Submodule.span (𝓞 E) (s : Set W), k • x ∈ M := by
  classical
  choose! n hn hn' using h
  refine ⟨∏ t ∈ s, n t, Finset.prod_pos fun t ht => hn t ht, fun m hm => ?_⟩
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (Finset.mem_coe.1 hx)
    rw [hk, mul_comm, mul_smul]
    exact M.nsmul_mem (hn' x (Finset.mem_coe.1 hx)) k
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact M.smul_mem a hx

/- English proof (translation)
Establish `hal : IsAlgebraic ℤ z` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic z)`. Take `⟨y, hy, hi⟩` from `hal.exists_integral_multiple`. Use `⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩` and prove the remaining obligations. Establish `hc : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E)` using `(Int.cast_natCast _).symm`. Rewrite `hi` using `[zsmul_eq_mul]`.

Break down `Int.natAbs_eq y with e | e` into its components or cases. Rewrite using `[hc, ← e]`. Conclude with `hi`. Rewrite using `[hc, show ((y.natAbs : ℤ)) = -y by omega, Int.cast_neg, neg_mul]; exact hi.neg`.
-/
theorem exists_nat_mul_isIntegral (z : E) : ∃ k : ℕ, 0 < k ∧ IsIntegral ℤ ((k : E) * z) := by
  have hal : IsAlgebraic ℤ z :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, hi⟩ := hal.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  have hc : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E) := (Int.cast_natCast _).symm
  rw [zsmul_eq_mul] at hi
  rcases Int.natAbs_eq y with e | e
  · rw [hc, ← e]; exact hi
  · rw [hc, show ((y.natAbs : ℤ)) = -y by omega, Int.cast_neg, neg_mul]; exact hi.neg

/- English proof (translation)
Simplify using `only [Formalism.L2.Pj.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]`. Use `forall_congr' fun i => ⟨?_, fun h => ⟨⟨x i, h⟩, rfl⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`. Rewrite using `[← hy]`. Conclude with `RingOfIntegers.isIntegral_coe y`.
-/
theorem mem_stdLat_iff {n : ℕ} (x : Fin n → E) : x ∈ Formalism.L2.Pj.stdLat E n ↔ ∀ i, IsIntegral ℤ (x i) := by
  simp only [Formalism.L2.Pj.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  refine forall_congr' fun i => ⟨?_, fun h => ⟨⟨x i, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact RingOfIntegers.isIntegral_coe y

/- English proof (translation)
Take `⟨k, hk, h⟩` from `exists_nsmul_le (Finset.univ.image fun i => Pi.single i (v i)) (Formalism.L2.Pj.stdLat E n) (by`. Simplify using `only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff]`. Introduce `i`. Take `⟨k, hk, hi⟩` from `exists_nat_mul_isIntegral (v i)`. Use `⟨k, hk, (mem_stdLat_iff _).2 fun j => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `e : j = i`. Substitute `e` using the available equality. Simplify `hi` using `[nsmul_eq_mul]`. Simplify using `[Pi.single_eq_of_ne e, isIntegral_zero])`. Use `⟨k, hk, h v ?_⟩` and prove the remaining obligations.

Establish `hs : ∑ i, Pi.single i (v i) ∈ Submodule.span (𝓞 E) ((Finset.univ.image fun i => Pi.single i (v i) : Finset (Fin n → E)) : Set (Fin n → E))` using `Submodule.sum_mem _ fun i _ => Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem (fun i => Pi.single i (v i)) (Finset.mem_univ i)))`. Rewrite `hs` using `[Finset.univ_sum_single v]`. Then use the resulting hypothesis.
-/
theorem exists_nsmul_mem_stdLat {n : ℕ} (v : Fin n → E) : ∃ k : ℕ, 0 < k ∧ k • v ∈ Formalism.L2.Pj.stdLat E n := by
  classical
  obtain ⟨k, hk, h⟩ := exists_nsmul_le (Finset.univ.image fun i => Pi.single i (v i)) (Formalism.L2.Pj.stdLat E n) (by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff]
    intro i
    obtain ⟨k, hk, hi⟩ := exists_nat_mul_isIntegral (v i)
    refine ⟨k, hk, (mem_stdLat_iff _).2 fun j => ?_⟩
    by_cases e : j = i
    · subst e
      simpa [nsmul_eq_mul] using hi
    · simp [Pi.single_eq_of_ne e, isIntegral_zero])
  refine ⟨k, hk, h v ?_⟩
  have hs : ∑ i, Pi.single i (v i) ∈ Submodule.span (𝓞 E) ((Finset.univ.image fun i => Pi.single i (v i) : Finset (Fin n → E)) : Set (Fin n → E)) :=
    Submodule.sum_mem _ fun i _ => Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem (fun i => Pi.single i (v i)) (Finset.mem_univ i)))
  rwa [Finset.univ_sum_single v] at hs

/- English proof (translation)
Establish `hv : v ∈ Submodule.span E (Λ : Set (Fin n → E))` using `by rw [hsp]; exact Submodule.mem_top`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_pos, by rwa [one_smul]⟩`. Consider the case `zero => exact ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨a, ha, hy⟩` from `hy`. Take `⟨b, hb, hz⟩` from `hz`. Use `⟨a * b, Nat.mul_pos ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `Λ.nsmul_mem hy _`. Rewrite using `[mul_smul]`. Conclude with `Λ.nsmul_mem hz _`. Consider the case `smul a y _ hy`.

Take `⟨m, hm, hy⟩` from `hy`. Take `⟨c, hc, hi⟩` from `exists_nat_mul_isIntegral a`. Use `⟨c * m, Nat.mul_pos hc hm, ?_⟩` and prove the remaining obligations. Establish `h` using `Λ.smul_mem (⟨(c : E) * a, hi⟩ : 𝓞 E) hy`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `j`. Express the relevant statement in the definitionally equal form `(c * m) • (a * y j) = ((c : E) * a) * (m • y j)`. Simplify using `only [nsmul_eq_mul, Nat.cast_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_nsmul_mem_of_span {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (v : Fin n → E) : ∃ k : ℕ, 0 < k ∧ k • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hsp]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_pos, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hy⟩ := hy
    obtain ⟨b, hb, hz⟩ := hz
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.nsmul_mem hy _
    · rw [mul_smul]; exact Λ.nsmul_mem hz _
  | smul a y _ hy =>
    obtain ⟨m, hm, hy⟩ := hy
    obtain ⟨c, hc, hi⟩ := exists_nat_mul_isIntegral a
    refine ⟨c * m, Nat.mul_pos hc hm, ?_⟩
    have h := Λ.smul_mem (⟨(c : E) * a, hi⟩ : 𝓞 E) hy
    convert h using 1
    funext j
    change (c * m) • (a * y j) = ((c : E) * a) * (m • y j)
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring

end GlobalTheory.LatSandwich

namespace GlobalTheory.LatSandwich

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Take `⟨T, hT⟩` from `hfg`. Take `⟨d, hd, hup⟩` from `exists_nsmul_le T (Formalism.L2.Pj.stdLat E n) fun x _ => exists_nsmul_mem_stdLat x`. Take `⟨d', hd', hlo⟩` from `exists_nsmul_le (Finset.univ.image fun i : Fin n => (Pi.single i 1 : Fin n → E)) Λ fun x _ => exists_nsmul_mem_of_span Λ hsp x`. Use `⟨d * d', Nat.mul_pos hd hd', fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_smul_eq_nsmul, mul_smul]`.

Use `Λ.nsmul_mem (hlo x ?_) d` and prove the remaining obligations. Establish `hint` using `(mem_stdLat_iff x).1 hx`. Establish `hs : ∑ i, (⟨x i, hint i⟩ : 𝓞 E) • (Pi.single i 1 : Fin n → E) ∈ Submodule.span (𝓞 E) ((Finset.univ.image fun i : Fin n => (Pi.single i 1 : Fin n → E) : Finset (Fin n → E)) : Set (Fin n → E))` using `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem (fun i : Fin n => (Pi.single i 1 : Fin n → E)) (Finset.mem_univ i))))`. Establish `e : ∑ i, (⟨x i, hint i⟩ : 𝓞 E) • (Pi.single i 1 : Fin n → E) = x` using `by conv_rhs => rw [← Finset.univ_sum_single x]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Express the relevant statement in the definitionally equal form `x j * (Pi.single j 1 : Fin n → E) j = _`. Simplify using the standard rewrite rules.

Express the relevant statement in the definitionally equal form `x i * (Pi.single i 1 : Fin n → E) j = _`. Simplify using `[Pi.single_eq_of_ne h]`. Rewrite `hs` using `[e]`. Then use the resulting hypothesis. Rewrite using `[Nat.cast_smul_eq_nsmul, mul_comm, mul_smul]`. Conclude with `nsmul_mem (hup x (hT ▸ hx)) d'`.
-/
theorem sandwich_of_fg {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG)
    (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ a : ℕ, 0 < a ∧ (∀ x ∈ Formalism.L2.Pj.stdLat E n, (a : 𝓞 E) • x ∈ Λ) ∧
      ∀ x ∈ Λ, (a : 𝓞 E) • x ∈ Formalism.L2.Pj.stdLat E n := by
  classical
  obtain ⟨T, hT⟩ := hfg
  obtain ⟨d, hd, hup⟩ := exists_nsmul_le T (Formalism.L2.Pj.stdLat E n) fun x _ => exists_nsmul_mem_stdLat x
  obtain ⟨d', hd', hlo⟩ := exists_nsmul_le (Finset.univ.image fun i : Fin n => (Pi.single i 1 : Fin n → E)) Λ
    fun x _ => exists_nsmul_mem_of_span Λ hsp x
  refine ⟨d * d', Nat.mul_pos hd hd', fun x hx => ?_, fun x hx => ?_⟩
  · rw [Nat.cast_smul_eq_nsmul, mul_smul]
    refine Λ.nsmul_mem (hlo x ?_) d
    have hint := (mem_stdLat_iff x).1 hx
    have hs : ∑ i, (⟨x i, hint i⟩ : 𝓞 E) • (Pi.single i 1 : Fin n → E) ∈ Submodule.span (𝓞 E)
        ((Finset.univ.image fun i : Fin n => (Pi.single i 1 : Fin n → E) : Finset (Fin n → E)) : Set (Fin n → E)) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem (fun i : Fin n => (Pi.single i 1 : Fin n → E)) (Finset.mem_univ i))))
    have e : ∑ i, (⟨x i, hint i⟩ : 𝓞 E) • (Pi.single i 1 : Fin n → E) = x := by
      conv_rhs => rw [← Finset.univ_sum_single x]
      refine Finset.sum_congr rfl fun i _ => ?_
      funext j
      by_cases h : j = i
      · subst h
        change x j * (Pi.single j 1 : Fin n → E) j = _
        simp
      · change x i * (Pi.single i 1 : Fin n → E) j = _
        simp [Pi.single_eq_of_ne h]
    rwa [e] at hs
  · rw [Nat.cast_smul_eq_nsmul, mul_comm, mul_smul]
    exact nsmul_mem (hup x (hT ▸ hx)) d'

end GlobalTheory.LatSandwich

namespace GlobalTheory.LatSandwich

/- English proof (translation)
Introduce `D V Λ hΛ`. Establish `e : Λ = V.L0.map (V.frame.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap`. Use extensionality with `x`. Rewrite using `[hΛ, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Use `⟨V.frame.equivFun.symm x, ?_, V.frame.equivFun.apply_symm_apply x⟩` and prove the remaining obligations. Rewrite using `[V.frame.equivFun_symm_apply]`. Conclude with `hx`. Introduce and unpack `⟨y, hy, rfl⟩`.

Express the relevant statement in the definitionally equal form `∑ i, V.frame.equivFun y i • V.frame i ∈ V.L0`. Rewrite using `[V.frame.sum_equivFun]`. Conclude with `hy`. Use `sandwich_of_fg Λ (e ▸ V.standardTuple_isLattice.fg.map _) ?_` and prove the remaining obligations. Establish `hs : (Λ : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V)`.

Rewrite using `[e]`. Both sides reduce to the same expression. Rewrite using `[hs, ← Submodule.map_span, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]`.
-/
theorem sandwich : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (∀ x, x ∈ Λ ↔ x ∈ L0c D V) →
    ∃ a : ℕ, 0 < a ∧ (∀ x ∈ Formalism.L2.Pj.stdLat D.host.E V.rank, (a : 𝓞 D.host.E) • x ∈ Λ) ∧
      ∀ x ∈ Λ, (a : 𝓞 D.host.E) • x ∈ Formalism.L2.Pj.stdLat D.host.E V.rank := by
  intro D V Λ hΛ
  have e : Λ = V.L0.map (V.frame.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap := by
    ext x
    rw [hΛ, Submodule.mem_map]
    constructor
    · intro hx
      refine ⟨V.frame.equivFun.symm x, ?_, V.frame.equivFun.apply_symm_apply x⟩
      rw [V.frame.equivFun_symm_apply]
      exact hx
    · rintro ⟨y, hy, rfl⟩
      change ∑ i, V.frame.equivFun y i • V.frame i ∈ V.L0
      rw [V.frame.sum_equivFun]
      exact hy
  refine sandwich_of_fg Λ (e ▸ V.standardTuple_isLattice.fg.map _) ?_
  have hs : (Λ : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := by
    rw [e]; rfl
  rw [hs, ← Submodule.map_span, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]

end GlobalTheory.LatSandwich
