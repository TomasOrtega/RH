import Formalism.MahlerMeasure.MahlerMeasureProofs.TheoremM
import Formalism.MahlerMeasure.MahlerMeasureProofs.FockBlocks
import Formalism.MahlerMeasure.MahlerMeasureProofs.RemoveS

namespace Formalism.CountingSumsFrames

open Formalism.GM Formalism.GM.TM

open M MvPolynomial Finset

def TieOps : Prop :=
  ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r]
    (LL : Letters N) (T : TieData) (a : ℕ) (E κ : ℝ) (n : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL → 1 ≤ E →
    (∀ i, T.S (LL.setTies T n) i ≤ n i) → (∀ x, (LL.setTies T n).deg x ≤ 2 * a) → (∀ i, T.z i ≤ 2 * a) →
    ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ →
    HypP p (LL.setTies T n) ρ ⌈κ / (N + 2)⌉₊ → HypW p (r := r) (LL.setTies T n) ⌈κ / (N + 2)⌉₊ →
    (∀ i, GramDeterminantGradedHypothesis p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ κ) →
    ∀ (nb : Fin T.t → (Fin r → ℤ) → ℕ)
      (f : ∀ i w, Fin (nb i w) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
      (U V : ∀ i w, Matrix (Fin (nb i w)) (Fin (nb i w)) ℚ_[p]) (dg : ∀ i w, Fin (nb i w) → ℚ_[p])
      (fw : ∀ i : Fin T.t, (Fin r → ℤ) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]),
      (∀ i w, LinearIndependent ℤ_[p] (f i w) ∧
        Submodule.span ℤ_[p] (Set.range (f i w)) =
          MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) →
      (∀ i w, (∀ x y, ‖U i w x y‖ ≤ 1) ∧ (∀ x y, ‖V i w x y‖ ≤ 1) ∧ ‖(U i w).det‖ = 1 ∧ ‖(V i w).det‖ = 1 ∧
        (Matrix.of fun x y => (p : ℚ_[p]) ^ (⌈κ⌉₊) *
          tieGam p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (T.z i) (n i) (f i w x) (f i w y)) =
          U i w * Matrix.diagonal (dg i w) * V i w) →
      (∀ i w, fw i w ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ∧
        (MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≠ ⊥ → fw i w ≠ 0)) →
      ∀ i : Fin T.t, ∃ (Tm πm : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
        (K : ℕ), (K : ℝ) ≤ C₂ * κ ∧
        (∀ y ∈ Y p (r := r) (LL.setTies T n) T.J T.thr, Tm y ∈ Y p (r := r) (LL.setTies T n) T.J T.thr) ∧
        (∀ y ∈ YZ p (r := r) (LL.setTies T n) T.J T.thr,
          ((p : ℚ_[p]) ^ K) • Tm y ∈ IntPol p (Fin N × Fin r)) ∧
        (∀ u ∈ Y p (r := r) (LL.setTies T n) T.J (T.thrUpTo i), ∀ u' ∈ Y p (r := r) (LL.setTies T n) T.J T.thr,
          fockN p (LL.setTies T n) (T.phi p (LL.setTies T n) i u) (Tm u') =
            (p : ℚ_[p]) ^ ⌊E⌋₊ * fockN p (LL.setTies T n) (πm u) u') ∧
        (∀ j : Fin T.t, i < j → ∀ u ∈ Y p (r := r) (LL.setTies T n) T.J (T.thrUpTo i),
          πm (T.phi p (LL.setTies T n) j u) = T.phi p (LL.setTies T n) j (πm u)) ∧
        ((Module.finrank ℚ_[p] (Y p (r := r) (LL.setTies T n) T.J T.thr) -
            Module.finrank ℚ_[p] ((Y p (r := r) (LL.setTies T n) T.J T.thr ⊓
              LinearMap.ker (πm - LinearMap.id) : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))) : ℕ) : ℝ) ≤
          ∑ᶠ w, ((univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card : ℝ) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) : ℝ)

def YPartner : Prop :=
  ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) (a : ℕ) (κ : ℝ),
    2 ≤ r → ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ → HypP p LL ρ ⌈κ / (N + 2)⌉₊ →
    ∀ z ∈ YZ p (r := r) LL J M,
      (∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), x ∈ YZ p (r := r) LL J M → z = c • x → IsUnit c) →
      ∃ z'' ∈ YZ p (r := r) LL J M, ∃ K₀ : ℕ, (K₀ : ℝ) ≤ C₃ * κ ∧
        (p : ℝ) ^ (-(K₀ : ℤ)) ≤ ‖fockN p LL z z''‖

section Peel

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [LinearOrder ι]

def lcomp (φ : ι → V →ₗ[K] V) (l : List ι) : V →ₗ[K] V :=
  l.foldr (fun i acc => φ i ∘ₗ acc) LinearMap.id

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lcomp_nil (φ : ι → V →ₗ[K] V) : lcomp φ [] = LinearMap.id := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lcomp_cons (φ : ι → V →ₗ[K] V) (i : ι) (l : List ι) : lcomp φ (i :: l) = φ i ∘ₗ lcomp φ l := rfl

/- English proof (translation)
The claim follows from `| [], _, u, hu => hu | i :: l, h, u, hu => by rw [lcomp_cons, LinearMap.comp_apply] exact h i List.mem_cons_self _ (lcomp_keep φ C l (fun j hj => h j (List.mem_cons_of_mem _ hj)) u hu)`.
-/
theorem lcomp_keep (φ : ι → V →ₗ[K] V) (C : Set V) :
    ∀ l : List ι, (∀ j ∈ l, ∀ u ∈ C, φ j u ∈ C) → ∀ u ∈ C, lcomp φ l u ∈ C
  | [], _, u, hu => hu
  | i :: l, h, u, hu => by
    rw [lcomp_cons, LinearMap.comp_apply]
    exact h i List.mem_cons_self _ (lcomp_keep φ C l (fun j hj => h j (List.mem_cons_of_mem _ hj)) u hu)

/- English proof (translation)
The claim follows from `| [], _, _, u, _ => rfl | i :: l, hk, hc, u, hu => by rw [lcomp_cons, LinearMap.comp_apply, LinearMap.comp_apply] have hk' : ∀ j ∈ l, ∀ u ∈ C, φ j u ∈ C := fun j hj => hk j (List.mem_cons_of_mem _ hj) have hc' : ∀ j ∈ l, ∀ u ∈ C, π (φ j u) = φ j (π u) := fun j hj => hc j (List.me …`.
-/
theorem lcomp_comm (φ : ι → V →ₗ[K] V) (π : V →ₗ[K] V) (C : Set V) :
    ∀ l : List ι, (∀ j ∈ l, ∀ u ∈ C, φ j u ∈ C) → (∀ j ∈ l, ∀ u ∈ C, π (φ j u) = φ j (π u)) →
      ∀ u ∈ C, π (lcomp φ l u) = lcomp φ l (π u)
  | [], _, _, u, _ => rfl
  | i :: l, hk, hc, u, hu => by
    rw [lcomp_cons, LinearMap.comp_apply, LinearMap.comp_apply]
    have hk' : ∀ j ∈ l, ∀ u ∈ C, φ j u ∈ C := fun j hj => hk j (List.mem_cons_of_mem _ hj)
    have hc' : ∀ j ∈ l, ∀ u ∈ C, π (φ j u) = φ j (π u) := fun j hj => hc j (List.mem_cons_of_mem _ hj)
    rw [hc i List.mem_cons_self _ (lcomp_keep φ C l hk' u hu), lcomp_comm φ π C l hk' hc' u hu]

/- English proof (translation)
The claim follows from `| [], _, u, _, _, y, _ => by simp [lcomp_nil] | i :: l, hl, u, hu, hfix, y, hy => by rw [List.pairwise_cons] at hl rw [lcomp_cons, lcomp_cons, LinearMap.comp_apply, LinearMap.comp_apply] have hX : lcomp φ l u ∈ C i := lcomp_keep φ (C i) l (fun j hj => hkeep i j (hl.1 j hj)) u (hY …`.
-/
theorem peel (B : V → V → K) (φ Ts π : ι → V →ₗ[K] V) (c : ι → K) (C : ι → Set V) (Y : Set V)
    (hYC : ∀ i, Y ⊆ C i) (hTY : ∀ i, ∀ y ∈ Y, Ts i y ∈ Y)
    (hkeep : ∀ i j, i < j → ∀ u ∈ C i, φ j u ∈ C i)
    (hcomm : ∀ i j, i < j → ∀ u ∈ C i, π i (φ j u) = φ j (π i u))
    (hadj : ∀ i, ∀ u ∈ C i, ∀ u' ∈ Y, B (φ i u) (Ts i u') = c i * B (π i u) u') :
    ∀ l : List ι, l.Pairwise (· < ·) → ∀ u ∈ Y, (∀ i ∈ l, π i u = u) → ∀ y ∈ Y,
      B (lcomp φ l u) (lcomp Ts l y) = (l.map c).prod * B u y
  | [], _, u, _, _, y, _ => by simp [lcomp_nil]
  | i :: l, hl, u, hu, hfix, y, hy => by
    rw [List.pairwise_cons] at hl
    rw [lcomp_cons, lcomp_cons, LinearMap.comp_apply, LinearMap.comp_apply]
    have hX : lcomp φ l u ∈ C i :=
      lcomp_keep φ (C i) l (fun j hj => hkeep i j (hl.1 j hj)) u (hYC i hu)
    have hZ : lcomp Ts l y ∈ Y := lcomp_keep Ts Y l (fun j _ => hTY j) y hy
    rw [hadj i _ hX _ hZ]
    rw [lcomp_comm φ (π i) (C i) l (fun j hj => hkeep i j (hl.1 j hj)) (fun j hj => hcomm i j (hl.1 j hj)) u
      (hYC i hu)]
    rw [hfix i List.mem_cons_self]
    rw [peel B φ Ts π c C Y hYC hTY hkeep hcomm hadj l hl.2 u hu (fun j hj => hfix j (List.mem_cons_of_mem _ hj))
      y hy]
    simp [mul_assoc]

end Peel

section Lat

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
The claim follows from `Module.IsTorsionFree.of_smul_eq_zero fun a x h => by by_cases ha : a = 0 · exact Or.inl ha · right apply Subtype.ext have h' : (a • (x : MvPolynomial σ ℚ_[p])) = 0 := by have := congrArg Subtype.val h simpa using this rw [← algebraMap_smul ℚ_[p] a (x : MvPolynomial σ ℚ_[p]), smul …`.
-/
theorem intPol_torsionFree {σ : Type} (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) : Module.IsTorsionFree ℤ_[p] L :=
  Module.IsTorsionFree.of_smul_eq_zero fun a x h => by
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      apply Subtype.ext
      have h' : (a • (x : MvPolynomial σ ℚ_[p])) = 0 := by
        have := congrArg Subtype.val h
        simpa using this
      rw [← algebraMap_smul ℚ_[p] a (x : MvPolynomial σ ℚ_[p]), smul_eq_zero] at h'
      rcases h' with h' | h'
      · exact absurd (PadicInt.ext (h'.trans PadicInt.coe_zero.symm)) ha
      · simpa using h'

/- English proof (translation)
Use `set L : Submodule ℤ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) := S.restrictScalars ℤ_[p] ⊓ PolZ p r LL with hLdef`. Establish `hLeq : L = S.restrictScalars ℤ_[p] ⊓ IntPol p (Fin N × Fin r)`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `inf_le_inf_left _ inf_le_right`. Introduce `x hx`.

Conclude with `Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hx).1, Submodule.mem_inf.mpr ⟨hS (Submodule.mem_inf.mp hx).1, (Submodule.mem_inf.mp hx).2⟩⟩`. Establish `: Module.Finite ℤ_[p] L` using `Module.Finite.iff_fg.mpr (Submodule.FG.of_le (polZ_fg LL) inf_le_right)`. Use `intPol_torsionFree L` as an intermediate fact. Take `⟨k, b⟩` from `Module.basisOfFiniteTypeTorsionFree' (R := ℤ_[p]) (M := L)`. Establish `hk : Module.finrank ℤ_[p] L = k`.

Rewrite using `[Module.finrank_eq_card_basis b, Fintype.card_fin]`. Rewrite using `[hk]`. Use `(finrank_of_lattice_basis S (fun i => (b i : MvPolynomial (Fin N × Fin r) ℚ_[p])) (b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)) ?_).symm` and prove the remaining obligations. Rewrite using `[← hLeq]`. Establish `: Set.range (fun i => (b i : MvPolynomial (Fin N × Fin r) ℚ_[p])) = L.subtype '' Set.range b`.

Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]`.
-/
theorem finrank_lattice {N r : ℕ} (LL : Letters N) (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hS : S ≤ Pol p r LL) :
    Module.finrank ℤ_[p] (S.restrictScalars ℤ_[p] ⊓ PolZ p r LL : Submodule ℤ_[p] _) = Module.finrank ℚ_[p] S := by
  set L : Submodule ℤ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) := S.restrictScalars ℤ_[p] ⊓ PolZ p r LL with hLdef
  have hLeq : L = S.restrictScalars ℤ_[p] ⊓ IntPol p (Fin N × Fin r) := by
    apply le_antisymm
    · exact inf_le_inf_left _ inf_le_right
    · intro x hx
      exact Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hx).1,
        Submodule.mem_inf.mpr ⟨hS (Submodule.mem_inf.mp hx).1, (Submodule.mem_inf.mp hx).2⟩⟩
  have : Module.Finite ℤ_[p] L := Module.Finite.iff_fg.mpr (Submodule.FG.of_le (polZ_fg LL) inf_le_right)
  have := intPol_torsionFree L
  obtain ⟨k, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ_[p]) (M := L)
  have hk : Module.finrank ℤ_[p] L = k := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  rw [hk]
  refine (finrank_of_lattice_basis S (fun i => (b i : MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)) ?_).symm
  rw [← hLeq]
  have : Set.range (fun i => (b i : MvPolynomial (Fin N × Fin r) ℚ_[p])) = L.subtype '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]

/- English proof (translation)
Set `bnd : Fin N × Fin r →₀ ℕ` to `Finsupp.equivFunOnFinite.symm (fun _ => LL.total)`. Establish `hfin : ({m | MultiDeg LL m} : Set (Fin N × Fin r →₀ ℕ)).Finite`. Use `(Set.finite_Iic bnd).subset ?_` and prove the remaining obligations. Introduce `m hm`. Rewrite using `[Set.mem_Iic, Finsupp.le_def]`.

Introduce `a`. Establish `h1 : m a ≤ ∑ c, m (a.1, c)` using `Finset.single_le_sum (f := fun c => m (a.1, c)) (fun _ _ => Nat.zero_le _) (mem_univ a.2)`. Establish `h2 : LL.deg a.1 ≤ LL.total` using `Finset.single_le_sum (f := fun i => LL.deg i) (fun _ _ => Nat.zero_le _) (mem_univ a.1)`. Establish `h3 : bnd a = LL.total` using `by simp [bnd]`. Rewrite using `[h3]`.

Rewrite `h1` using `[hm a.1]`. Use linear arithmetic over natural numbers and integers. Establish `hle : Pol p r LL ≤ Submodule.span ℚ_[p] ((fun m => (monomial m (1 : ℚ_[p]) : MvPolynomial (Fin N × Fin r) ℚ_[p])) '' {m | MultiDeg LL m})`. Introduce `x hx`. Rewrite `hx` using `[Pol, mem_restrictSupport_iff]`.

Rewrite using `[x.as_sum]`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Establish `: monomial m (x.coeff m) = x.coeff m • (monomial m (1 : ℚ_[p]))`. Rewrite using `[MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hx (Finset.mem_coe.mpr hm), rfl⟩)`. Establish `: FiniteDimensional ℚ_[p] (Submodule.span ℚ_[p] ((fun m => (monomial m (1 : ℚ_[p]) : MvPolynomial (Fin N × Fin r) ℚ_[p])) '' {m | MultiDeg LL m}))` using `FiniteDimensional.span_of_finite ℚ_[p] (hfin.image _)`. Conclude with `Submodule.finiteDimensional_of_le hle`.
-/
theorem pol_finiteDimensional {N r : ℕ} (LL : Letters N) : FiniteDimensional ℚ_[p] (Pol p r LL) := by
  classical
  let bnd : Fin N × Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => LL.total)
  have hfin : ({m | MultiDeg LL m} : Set (Fin N × Fin r →₀ ℕ)).Finite := by
    refine (Set.finite_Iic bnd).subset ?_
    intro m hm
    rw [Set.mem_Iic, Finsupp.le_def]
    intro a
    have h1 : m a ≤ ∑ c, m (a.1, c) :=
      Finset.single_le_sum (f := fun c => m (a.1, c)) (fun _ _ => Nat.zero_le _) (mem_univ a.2)
    have h2 : LL.deg a.1 ≤ LL.total :=
      Finset.single_le_sum (f := fun i => LL.deg i) (fun _ _ => Nat.zero_le _) (mem_univ a.1)
    have h3 : bnd a = LL.total := by simp [bnd]
    rw [h3]
    rw [hm a.1] at h1
    omega
  have hle : Pol p r LL ≤ Submodule.span ℚ_[p] ((fun m => (monomial m (1 : ℚ_[p]) : MvPolynomial (Fin N × Fin r) ℚ_[p])) ''
      {m | MultiDeg LL m}) := by
    intro x hx
    rw [Pol, mem_restrictSupport_iff] at hx
    rw [x.as_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    have : monomial m (x.coeff m) = x.coeff m • (monomial m (1 : ℚ_[p])) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hx (Finset.mem_coe.mpr hm), rfl⟩)
  have : FiniteDimensional ℚ_[p] (Submodule.span ℚ_[p] ((fun m => (monomial m (1 : ℚ_[p]) :
      MvPolynomial (Fin N × Fin r) ℚ_[p])) '' {m | MultiDeg LL m})) :=
    FiniteDimensional.span_of_finite ℚ_[p] (hfin.image _)
  exact Submodule.finiteDimensional_of_le hle

end Lat

section Codim

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Establish `hle : ∀ {S T : Submodule K V} [FiniteDimensional K T], S ≤ T → Module.finrank K S ≤ Module.finrank K T` using `fun h => LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective h)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.inf_empty, inf_top_eq]`. Simplify using the standard rewrite rules.

Consider the case `@insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.inf_insert]`. Establish `e : (Y ⊓ (A a ⊓ s.inf A) : Submodule K V) = (Y ⊓ A a) ⊓ (Y ⊓ s.inf A)`. Rewrite using `[inf_inf_distrib_left]`. Rewrite using `[e]`.

Use `haveI : FiniteDimensional K ↥(Y ⊓ A a) := Submodule.finiteDimensional_of_le inf_le_left`. Use `haveI : FiniteDimensional K ↥(Y ⊓ s.inf A) := Submodule.finiteDimensional_of_le inf_le_left`. Establish `h1` using `Submodule.finrank_sup_add_finrank_inf_eq (Y ⊓ A a) (Y ⊓ s.inf A)`. Establish `h2 : Module.finrank K ↥((Y ⊓ A a) ⊔ (Y ⊓ s.inf A)) ≤ Module.finrank K Y` using `hle (sup_le inf_le_left inf_le_left)`. Establish `h3 : Module.finrank K ↥(Y ⊓ A a) ≤ Module.finrank K Y` using `hle inf_le_left`.

Establish `h4 : Module.finrank K ↥(Y ⊓ s.inf A) ≤ Module.finrank K Y` using `hle inf_le_left`. Use linear arithmetic over natural numbers and integers.
-/
theorem codim_inf_le [DecidableEq ι] (Y : Submodule K V) [FiniteDimensional K Y] (A : ι → Submodule K V) :
    ∀ s : Finset ι, Module.finrank K Y - Module.finrank K (Y ⊓ s.inf A : Submodule K V) ≤
      ∑ i ∈ s, (Module.finrank K Y - Module.finrank K (Y ⊓ A i : Submodule K V)) := by
  have hle : ∀ {S T : Submodule K V} [FiniteDimensional K T], S ≤ T →
      Module.finrank K S ≤ Module.finrank K T :=
    fun h => LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective h)
  intro s
  induction s using Finset.induction_on with
  | empty => rw [Finset.inf_empty, inf_top_eq]; simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.inf_insert]
    have e : (Y ⊓ (A a ⊓ s.inf A) : Submodule K V) = (Y ⊓ A a) ⊓ (Y ⊓ s.inf A) := by
      rw [inf_inf_distrib_left]
    rw [e]
    haveI : FiniteDimensional K ↥(Y ⊓ A a) := Submodule.finiteDimensional_of_le inf_le_left
    haveI : FiniteDimensional K ↥(Y ⊓ s.inf A) := Submodule.finiteDimensional_of_le inf_le_left
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Y ⊓ A a) (Y ⊓ s.inf A)
    have h2 : Module.finrank K ↥((Y ⊓ A a) ⊔ (Y ⊓ s.inf A)) ≤ Module.finrank K Y :=
      hle (sup_le inf_le_left inf_le_left)
    have h3 : Module.finrank K ↥(Y ⊓ A a) ≤ Module.finrank K Y := hle inf_le_left
    have h4 : Module.finrank K ↥(Y ⊓ s.inf A) ≤ Module.finrank K Y := hle inf_le_left
    omega

end Codim

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open Formalism.GM Formalism.GM.TM M MvPolynomial Finset

section Stab
variable {k σ : Type} [Field k]

def stabAlg (W : Submodule k (MvPolynomial σ k)) : Subalgebra k (Module.End k (MvPolynomial σ k)) where
  carrier := {T | ∀ x ∈ W, T x ∈ W}
  mul_mem' := by intro a b ha hb x hx; exact ha _ (hb x hx)
  add_mem' := by intro a b ha hb x hx; exact W.add_mem (ha x hx) (hb x hx)
  algebraMap_mem' := by intro c x hx; rw [Module.algebraMap_end_apply]; exact W.smul_mem c hx

/- English proof (translation)
Unfold `FockB.Ops at hT`. Proceed by induction on `hT using Algebra.adjoin_induction`. Name the introduced variables `T' hT'`. Simplify using `only [FockB.atoms, Set.mem_setOf_eq] at hT'`. Take `⟨u, hu, rfl | rfl⟩` from `hT'`.

Introduce `z hz`. Rewrite `hz` using `[MvPolynomial.mem_restrictSupport_iff]`. Use `show X u * z ∈ restrictSupport k Q`. Rewrite using `[MvPolynomial.as_sum z, Finset.mul_sum]`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations.

Rewrite using `[X, monomial_mul, one_mul, MvPolynomial.mem_restrictSupport_iff]`. Use `(Finset.coe_subset.mpr support_monomial_subset).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.coe_singleton, Set.singleton_subset_iff]`. Use `hQ m _ (fun w hw => ?_) (hz hm)` and prove the remaining obligations. Establish `: u ≠ w` using `fun h => hw (h ▸ hu)`.

Simplify using `[Finsupp.single_apply, this]`. Introduce `z hz`. Rewrite `hz` using `[MvPolynomial.mem_restrictSupport_iff]`. Use `show pderiv u z ∈ restrictSupport k Q`. Rewrite using `[MvPolynomial.as_sum z, map_sum]`.

Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Rewrite using `[pderiv_monomial, MvPolynomial.mem_restrictSupport_iff]`. Use `(Finset.coe_subset.mpr support_monomial_subset).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.coe_singleton, Set.singleton_subset_iff]`. Use `hQ m _ (fun w hw => ?_) (hz hm)` and prove the remaining obligations.

Establish `: u ≠ w` using `fun h => hw (h ▸ hu)`. Simplify using `[Finsupp.single_apply, this]`. Name the introduced variables `c`. Introduce `z hz`. Rewrite using `[Module.algebraMap_end_apply]`.

Conclude with `Submodule.smul_mem _ _ hz`. Name the introduced variables `ihx ihy`. Introduce `z hz`. Rewrite using `[LinearMap.add_apply]`. Conclude with `Submodule.add_mem _ (ihx z hz) (ihy z hz)`.

Name the introduced variables `ihx ihy`. Introduce `z hz`. Conclude with `ihx _ (ihy z hz)`.
-/
theorem ops_keep_supp (S : Set σ) (Q : Set (σ →₀ ℕ))
    (hQ : ∀ m m' : σ →₀ ℕ, (∀ v, v ∉ S → m v = m' v) → m ∈ Q → m' ∈ Q)
    {T : Module.End k (MvPolynomial σ k)} (hT : T ∈ FockB.Ops S) :
    ∀ x ∈ restrictSupport k Q, T x ∈ restrictSupport k Q := by
  unfold FockB.Ops at hT
  induction hT using Algebra.adjoin_induction
  · rename_i T' hT'
    simp only [FockB.atoms, Set.mem_setOf_eq] at hT'
    obtain ⟨u, hu, rfl | rfl⟩ := hT'
    · intro z hz
      rw [MvPolynomial.mem_restrictSupport_iff] at hz
      show X u * z ∈ restrictSupport k Q
      rw [MvPolynomial.as_sum z, Finset.mul_sum]
      refine Submodule.sum_mem _ fun m hm => ?_
      rw [X, monomial_mul, one_mul, MvPolynomial.mem_restrictSupport_iff]
      refine (Finset.coe_subset.mpr support_monomial_subset).trans ?_
      rw [Finset.coe_singleton, Set.singleton_subset_iff]
      refine hQ m _ (fun w hw => ?_) (hz hm)
      have : u ≠ w := fun h => hw (h ▸ hu)
      simp [Finsupp.single_apply, this]
    · intro z hz
      rw [MvPolynomial.mem_restrictSupport_iff] at hz
      show pderiv u z ∈ restrictSupport k Q
      rw [MvPolynomial.as_sum z, map_sum]
      refine Submodule.sum_mem _ fun m hm => ?_
      rw [pderiv_monomial, MvPolynomial.mem_restrictSupport_iff]
      refine (Finset.coe_subset.mpr support_monomial_subset).trans ?_
      rw [Finset.coe_singleton, Set.singleton_subset_iff]
      refine hQ m _ (fun w hw => ?_) (hz hm)
      have : u ≠ w := fun h => hw (h ▸ hu)
      simp [Finsupp.single_apply, this]
  · rename_i c
    intro z hz
    rw [Module.algebraMap_end_apply]
    exact Submodule.smul_mem _ _ hz
  · rename_i ihx ihy
    intro z hz
    rw [LinearMap.add_apply]
    exact Submodule.add_mem _ (ihx z hz) (ihy z hz)
  · rename_i ihx ihy
    intro z hz
    exact ihx _ (ihy z hz)
end Stab

section Keep
variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Unfold `fockN`. Rewrite using `[fock_smul_right, mul_div_assoc]`.
-/
theorem fockN_smul_right' {N r : ℕ} (LL : Letters N) (c : ℚ_[p]) (F G : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    fockN p LL F (c • G) = c * fockN p LL F G := by
  unfold fockN
  rw [fock_smul_right, mul_div_assoc]

/- English proof (translation)
Use `le_antisymm le_top (le_sSup ⟨?_, fun c d x _ => Submodule.mem_top⟩)` and prove the remaining obligations. Introduce `x _`. Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `m _`. Conclude with `(le_top : ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ ⊤)`.
-/
theorem ycond_top {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) : YCond p (r := r) LL j (⊤ : WithTop ℤ) = ⊤ := by
  refine le_antisymm le_top (le_sSup ⟨?_, fun c d x _ => Submodule.mem_top⟩)
  intro x _
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro m _
  exact (le_top : ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ ⊤)

/- English proof (translation)
Apply `inf_le_inf_left` to reduce the goal to its premises. Apply `le_iInf` to reduce the goal to its premises. Introduce `k`. Use `(iInf_le _ k).trans ?_` and prove the remaining obligations. Unfold `TieData.thrUpTo`.

Use `split_ifs`. Conclude with `le_rfl`. Rewrite using `[ycond_top]`. Conclude with `le_top`.
-/
theorem y_le_thrUpTo {N r : ℕ} [NeZero r] (LL : Letters N) (T : TieData) (i : Fin T.t) :
    Y p (r := r) LL T.J T.thr ≤ Y p (r := r) LL T.J (T.thrUpTo i) := by
  apply inf_le_inf_left
  apply le_iInf
  intro k
  refine (iInf_le _ k).trans ?_
  unfold TieData.thrUpTo
  split_ifs
  · exact le_rfl
  · rw [ycond_top]; exact le_top

/- English proof (translation)
Unfold `glAct FockB.Ops`. Use `Subalgebra.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Use `split_ifs with hi hv`. Establish `h1 : (LinearMap.mulLeft ℚ_[p] (X (i, c)) : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈ Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | (v.1 : ℕ) < j})` using `Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, c), hi, Or.inl rfl⟩)`. Establish `h2 : ((pderiv (R` using `ℚ_[p]) (i, d) : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈ Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | (v.1 : ℕ) < j}) := Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, d), hi, Or.inr rfl⟩)`.

Conclude with `Subalgebra.mul_mem _ h1 h2`. Establish `h1 : (LinearMap.mulLeft ℚ_[p] (X (i, d)) : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈ Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | (v.1 : ℕ) < j})` using `Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, d), hi, Or.inl rfl⟩)`. Establish `h2 : ((pderiv (R` using `ℚ_[p]) (i, c) : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈ Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | (v.1 : ℕ) < j}) := Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, c), hi, Or.inr rfl⟩)`. Conclude with `Subalgebra.neg_mem _ (Subalgebra.mul_mem _ h1 h2)`. Conclude with `Subalgebra.zero_mem _`.
-/
theorem glAct_mem {N r : ℕ} (LL : Letters N) (j : ℕ) (c d : Fin r) :
    (glAct p LL j c d : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈
      FockB.Ops {v : Fin N × Fin r | (v.1 : ℕ) < j} := by
  unfold glAct FockB.Ops
  refine Subalgebra.sum_mem _ fun i _ => ?_
  split_ifs with hi hv
  · have h1 : (LinearMap.mulLeft ℚ_[p] (X (i, c)) : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈
        Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | (v.1 : ℕ) < j}) :=
      Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, c), hi, Or.inl rfl⟩)
    have h2 : ((pderiv (R := ℚ_[p]) (i, d) : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈ Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | (v.1 : ℕ) < j}) :=
      Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, d), hi, Or.inr rfl⟩)
    exact Subalgebra.mul_mem _ h1 h2
  · have h1 : (LinearMap.mulLeft ℚ_[p] (X (i, d)) : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈
        Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | (v.1 : ℕ) < j}) :=
      Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, d), hi, Or.inl rfl⟩)
    have h2 : ((pderiv (R := ℚ_[p]) (i, c) : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈ Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | (v.1 : ℕ) < j}) :=
      Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, c), hi, Or.inr rfl⟩)
    exact Subalgebra.neg_mem _ (Subalgebra.mul_mem _ h1 h2)
  · exact Subalgebra.zero_mem _

/- English proof (translation)
Unfold `TieData.phi`. Rewrite using `[dif_pos h]`. Unfold `tiePhiAt`. Use `FockB.ops_mono ?_ (FockB.tiePhi_mem (zv := ((⟨T.pos j, by omega⟩ : Fin N), (0 : Fin r))) (sv := ((⟨T.pos j, by omega⟩ : Fin N), (0 : Fin r))) _ _ _)` and prove the remaining obligations. Introduce `v hv`.

Simplify using `only [FockB.V, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hv`. Simplify using `only [Set.mem_ofPred_eq]`. Break down `hv with (⟨c, rfl⟩ | ⟨c, rfl⟩) | rfl | rfl` into its components or cases. Use `left`. Both sides reduce to the same expression.

Use `right`. Both sides reduce to the same expression. Use `left`. Both sides reduce to the same expression. Use `left`.

Both sides reduce to the same expression.
-/
theorem phi_mem {N r : ℕ} [NeZero r] (LL : Letters N) (T : TieData) (j : Fin T.t) (h : T.pos j + 1 < N) :
    (T.phi p LL j : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈
      FockB.Ops {v : Fin N × Fin r | (v.1 : ℕ) = T.pos j ∨ (v.1 : ℕ) = T.pos j + 1} := by
  unfold TieData.phi
  rw [dif_pos h]
  unfold tiePhiAt
  refine FockB.ops_mono ?_ (FockB.tiePhi_mem (zv := ((⟨T.pos j, by omega⟩ : Fin N), (0 : Fin r)))
    (sv := ((⟨T.pos j, by omega⟩ : Fin N), (0 : Fin r))) _ _ _)
  intro v hv
  simp only [FockB.V, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  simp only [Set.mem_ofPred_eq]
  rcases hv with (⟨c, rfl⟩ | ⟨c, rfl⟩) | rfl | rfl
  · left; rfl
  · right; rfl
  · left; rfl
  · left; rfl

/- English proof (translation)
Rewrite using `[Pol, mem_restrictSupport_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h i`. Conclude with `ProjS.eulL_of_support _ _ _ (fun m hm => h (Finset.mem_coe.mpr hm) i)`. Introduce `h m hm i`.

Establish `hc` using `congrArg (coeff m) (h i)`. Rewrite `hc` using `[ProjS.coeff_eulL, coeff_smul, smul_eq_mul]`. Establish `hne : coeff m x ≠ 0` using `mem_support_iff.mp hm`. Establish `h2 : (∑ c, (m (i, c) : ℚ_[p])) = (LL.deg i : ℚ_[p])` using `mul_left_cancel₀ hne (hc.trans (mul_comm _ _))`. Conclude with `h2` after adjusting the coercions.
-/
theorem pol_iff_eul {N r : ℕ} (LL : Letters N) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    x ∈ Pol p r LL ↔ ∀ i : Fin N, ProjS.eulL (fun c : Fin r => (i, c)) x = ((LL.deg i : ℕ) : ℚ_[p]) • x := by
  rw [Pol, mem_restrictSupport_iff]
  constructor
  · intro h i
    exact ProjS.eulL_of_support _ _ _ (fun m hm => h (Finset.mem_coe.mpr hm) i)
  · intro h m hm i
    have hc := congrArg (coeff m) (h i)
    rw [ProjS.coeff_eulL, coeff_smul, smul_eq_mul] at hc
    have hne : coeff m x ≠ 0 := mem_support_iff.mp hm
    have h2 : (∑ c, (m (i, c) : ℚ_[p])) = (LL.deg i : ℚ_[p]) :=
      mul_left_cancel₀ hne (hc.trans (mul_comm _ _))
    exact_mod_cast h2

end Keep

section Keep2
variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => simpa using hg`. Consider the case `succ l ih`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Use `show ProjS.eulL t ((∑ d, X (w d) * X (e d)) * (tieE w e ^ l) g) = _`.

Rewrite using `[h _ _ ih]`. Use `push_cast`. Rewrite using `[add_assoc]`. Both sides reduce to the same expression.
-/
theorem eulL_E_pow {σ : Type} {r : ℕ} (t w e : Fin r → σ) (h : ∀ (g : MvPolynomial σ ℚ_[p]) (α : ℚ_[p]),
    ProjS.eulL t g = α • g → ProjS.eulL t ((∑ d, X (w d) * X (e d)) * g) = (α + 1) • ((∑ d, X (w d) * X (e d)) * g))
    (g : MvPolynomial σ ℚ_[p]) (α : ℚ_[p]) (hg : ProjS.eulL t g = α • g) (l : ℕ) :
    ProjS.eulL t ((tieE w e ^ l) g) = (α + l) • (tieE w e ^ l) g := by
  induction l with
  | zero => simpa using hg
  | succ l ih =>
    rw [pow_succ', Module.End.mul_apply]
    show ProjS.eulL t ((∑ d, X (w d) * X (e d)) * (tieE w e ^ l) g) = _
    rw [h _ _ ih]
    push_cast; rw [add_assoc]; rfl

/- English proof (translation)
Introduce `x hx`. Rewrite `hx`, the goal using `[pol_iff_eul]`. Introduce `i`. Use `set a : Fin N := ⟨T.pos j, by omega⟩ with ha`. Use `set b : Fin N := ⟨T.pos j + 1, h⟩ with hb`.

Establish `hab : a ≠ b` using `by intro h'; have := congrArg Fin.val h'; simp [a, b] at this`. Establish `hw : Function.Injective (fun c : Fin r => (a, c))` using `fun c d h' => (Prod.mk.inj h').2`. Establish `he : Function.Injective (fun c : Fin r => (b, c))` using `fun c d h' => (Prod.mk.inj h').2`. Establish `hwe : ∀ c d : Fin r, (a, c) ≠ (b, d)` using `fun c d h' => hab (Prod.mk.inj h').1`. Establish `hphi : T.phi p LL j = tiePhi (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) (LL.deg a) (LL.deg b) (T.z j)`.

Unfold `TieData.phi`. Rewrite using `[dif_pos h]`. Both sides reduce to the same expression. Distinguish the cases in `hia : i = a`. Substitute `hia` using the available equality.

Rewrite using `[hphi]`. Unfold `tiePhi`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum, map_smul]`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_comm]`. Use `congr 1`. Establish `hF` using `ProjS.eulL_tieF_pow (fun c : Fin r => (a, c)) hw (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) (fun c => Or.inl ⟨⟨c, rfl⟩, fun d h' => hwe d c h'⟩) x _ (hx a) l`. Establish `hE` using `eulL_E_pow (fun c : Fin r => (a, c)) (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) (fun g α hg => ProjS.eulL_w_S_mul hw hwe g α hg) _ _ hF l`. Rewrite using `[hE]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hib : i = b`. Substitute `hib` using the available equality. Rewrite using `[hphi]`.

Unfold `tiePhi`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum, map_smul]`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm]`.

Use `congr 1`. Establish `hF` using `ProjS.eulL_tieF_pow (fun c : Fin r => (b, c)) he (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) (fun c => Or.inr ⟨fun d h' => hwe c d h'.symm, ⟨c, rfl⟩⟩) x _ (hx b) l`. Establish `hE` using `eulL_E_pow (fun c : Fin r => (b, c)) (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) (fun g α hg => ProjS.eulL_e_S_mul he hwe g α hg) _ _ hF l`. Rewrite using `[hE]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hdisj : Disjoint {v : Fin N × Fin r | (v.1 : ℕ) = T.pos j ∨ (v.1 : ℕ) = T.pos j + 1} {v | v.1 = i}`. Rewrite using `[Set.disjoint_left]`. Introduce and unpack `v hv1 hv2`. Simplify using `only [Set.mem_ofPred_eq] at hv1 hv2`.

Break down `hv1 with h1 | h1` into its components or cases. Conclude with `hia (by rw [← hv2]; exact Fin.ext h1)`. Conclude with `hib (by rw [← hv2]; exact Fin.ext h1)`. Establish `hc` using `FockB.ops_apply_comm hdisj (phi_mem LL T j h) (FockB.eulL_mem (S := {v : Fin N × Fin r | v.1 = i}) (fun c : Fin r => (i, c)) (fun c => rfl)) x`. Rewrite using `[← hc, hx i, map_smul]`.
-/
theorem phi_pol {N r : ℕ} [NeZero r] (LL : Letters N) (T : TieData) (j : Fin T.t) (h : T.pos j + 1 < N) :
    ∀ x ∈ Pol p r LL, T.phi p LL j x ∈ Pol p r LL := by
  intro x hx
  rw [pol_iff_eul] at hx ⊢
  intro i
  set a : Fin N := ⟨T.pos j, by omega⟩ with ha
  set b : Fin N := ⟨T.pos j + 1, h⟩ with hb
  have hab : a ≠ b := by intro h'; have := congrArg Fin.val h'; simp [a, b] at this
  have hw : Function.Injective (fun c : Fin r => (a, c)) := fun c d h' => (Prod.mk.inj h').2
  have he : Function.Injective (fun c : Fin r => (b, c)) := fun c d h' => (Prod.mk.inj h').2
  have hwe : ∀ c d : Fin r, (a, c) ≠ (b, d) := fun c d h' => hab (Prod.mk.inj h').1
  have hphi : T.phi p LL j = tiePhi (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c)) (LL.deg a) (LL.deg b) (T.z j) := by
    unfold TieData.phi; rw [dif_pos h]; rfl
  by_cases hia : i = a
  · subst hia
    rw [hphi]
    unfold tiePhi
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum, map_smul]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_comm]
    congr 1
    have hF := ProjS.eulL_tieF_pow (fun c : Fin r => (a, c)) hw (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c))
      (fun c => Or.inl ⟨⟨c, rfl⟩, fun d h' => hwe d c h'⟩) x _ (hx a) l
    have hE := eulL_E_pow (fun c : Fin r => (a, c)) (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c))
      (fun g α hg => ProjS.eulL_w_S_mul hw hwe g α hg) _ _ hF l
    rw [hE]; congr 1; ring
  by_cases hib : i = b
  · subst hib
    rw [hphi]
    unfold tiePhi
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum, map_smul]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_comm]
    congr 1
    have hF := ProjS.eulL_tieF_pow (fun c : Fin r => (b, c)) he (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c))
      (fun c => Or.inr ⟨fun d h' => hwe c d h'.symm, ⟨c, rfl⟩⟩) x _ (hx b) l
    have hE := eulL_E_pow (fun c : Fin r => (b, c)) (fun c : Fin r => (a, c)) (fun c : Fin r => (b, c))
      (fun g α hg => ProjS.eulL_e_S_mul he hwe g α hg) _ _ hF l
    rw [hE]; congr 1; ring
  · have hdisj : Disjoint {v : Fin N × Fin r | (v.1 : ℕ) = T.pos j ∨ (v.1 : ℕ) = T.pos j + 1} {v | v.1 = i} := by
      rw [Set.disjoint_left]
      rintro v hv1 hv2
      simp only [Set.mem_ofPred_eq] at hv1 hv2
      rcases hv1 with h1 | h1
      · exact hia (by rw [← hv2]; exact Fin.ext h1)
      · exact hib (by rw [← hv2]; exact Fin.ext h1)
    have hc := FockB.ops_apply_comm hdisj (phi_mem LL T j h)
      (FockB.eulL_mem (S := {v : Fin N × Fin r | v.1 = i}) (fun c : Fin r => (i, c)) (fun c => rfl)) x
    rw [← hc, hx i, map_smul]

/- English proof (translation)
Unfold `YCond`. Use `set F := {S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) | S ≤ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} ∧ GlStable p LL j S} with hF`. Establish `hle : sSup F ≤ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt}` using `sSup_le fun S hS => hS.1`. Establish `hst : GlStable p LL j (sSup F)`. Introduce `c d`.

Establish `: sSup F ≤ (sSup F).comap (glAct p LL j c d)` using `sSup_le fun S hS x hx => le_sSup hS (hS.2 c d x hx)`. Conclude with `fun x hx => this hx`. Establish `hmap : (sSup F).map T ∈ F`. Use `⟨Submodule.map_le_iff_le_comap.mpr (fun x hx => hw x (hle hx)), ?_⟩` and prove the remaining obligations. Introduce `c d y hy`.

Take `⟨x, hx, rfl⟩` from `Submodule.mem_map.mp hy`. Rewrite using `[← hc]`. Conclude with `Submodule.mem_map_of_mem (hst c d x hx)`. Introduce `x hx`. Conclude with `le_sSup hmap (Submodule.mem_map_of_mem hx)`.
-/
theorem ycond_keep {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ)
    (T : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hc : ∀ c d x, T (glAct p LL j c d x) = glAct p LL j c d (T x))
    (hw : ∀ x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt},
      T x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt}) :
    ∀ x ∈ YCond p (r := r) LL j Mt, T x ∈ YCond p (r := r) LL j Mt := by
  unfold YCond
  set F := {S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) |
    S ≤ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} ∧ GlStable p LL j S}
    with hF
  have hle : sSup F ≤ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} :=
    sSup_le fun S hS => hS.1
  have hst : GlStable p LL j (sSup F) := by
    intro c d
    have : sSup F ≤ (sSup F).comap (glAct p LL j c d) :=
      sSup_le fun S hS x hx => le_sSup hS (hS.2 c d x hx)
    exact fun x hx => this hx
  have hmap : (sSup F).map T ∈ F := by
    refine ⟨Submodule.map_le_iff_le_comap.mpr (fun x hx => hw x (hle hx)), ?_⟩
    intro c d y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    rw [← hc]
    exact Submodule.mem_map_of_mem (hst c d x hx)
  intro x hx
  exact le_sSup hmap (Submodule.mem_map_of_mem hx)

/- English proof (translation)
Take `⟨hmono, hpos, _⟩` from `hadm`. Take `⟨h, _, _⟩` from `hpos j`. Establish `hpij : T.pos i < T.pos j` using `hmono hij`. Introduce `u hu`. Establish `hu1` using `(Submodule.mem_inf.mp hu).1`.

Establish `hu2` using `(Submodule.mem_inf.mp hu).2`. Use `Submodule.mem_inf.mpr ⟨phi_pol LL T j h u hu1, ?_⟩` and prove the remaining obligations. Rewrite `hu2`, the goal using `[Submodule.mem_iInf]`. Introduce `k`. Establish `hk2` using `hu2 k`.

Simplify using `only [TieData.thrUpTo] at hk2 ⊢`. Use `split_ifs at hk2 ⊢ with hk`. Establish `hdisj : Disjoint {v : Fin N × Fin r | (v.1 : ℕ) = T.pos j ∨ (v.1 : ℕ) = T.pos j + 1} {v : Fin N × Fin r | (v.1 : ℕ) < T.J k}`. Rewrite using `[Set.disjoint_left]`. Introduce and unpack `v hv1 hv2`.

Simplify using `only [Set.mem_ofPred_eq] at hv1 hv2`. Use linear arithmetic over natural numbers and integers. Use `ycond_keep LL (T.J k) (T.thr k) (T.phi p LL j) (fun c d x => ?_) (fun x hx => ?_) u hk2` and prove the remaining obligations. Conclude with `FockB.ops_apply_comm hdisj (phi_mem LL T j h) (glAct_mem LL (T.J k) c d) x`. Use `ops_keep_supp _ _ (fun m m' hmm' hm => ?_) (phi_mem LL T j h) x hx` and prove the remaining obligations.

Establish `: wt LL (T.J k) 0 m = wt LL (T.J k) 0 m'`. Unfold `wt`. Use `Finset.sum_congr rfl fun i' _ => ?_` and prove the remaining obligations. Use `split_ifs with hi`. Rewrite using `[hmm' (i', 0) (by simp only [Set.mem_ofPred_eq]; omega)]`.

Rewrite using `[hmm' (i', 0) (by simp only [Set.mem_ofPred_eq]; omega)]`. Both sides reduce to the same expression. Simplify using `only [Set.mem_ofPred_eq] at hm ⊢`. Rewrite using `[← this]`. Conclude with `hm`.

Rewrite using `[ycond_top]`. Conclude with `Submodule.mem_top`.
-/
theorem phi_keeps {N r : ℕ} [NeZero r] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i j : Fin T.t)
    (hij : i < j) : ∀ u ∈ Y p (r := r) LL T.J (T.thrUpTo i), T.phi p LL j u ∈ Y p (r := r) LL T.J (T.thrUpTo i) := by
  obtain ⟨hmono, hpos, _⟩ := hadm
  obtain ⟨h, _, _⟩ := hpos j
  have hpij : T.pos i < T.pos j := hmono hij
  intro u hu
  have hu1 := (Submodule.mem_inf.mp hu).1
  have hu2 := (Submodule.mem_inf.mp hu).2
  refine Submodule.mem_inf.mpr ⟨phi_pol LL T j h u hu1, ?_⟩
  rw [Submodule.mem_iInf] at hu2 ⊢
  intro k
  have hk2 := hu2 k
  simp only [TieData.thrUpTo] at hk2 ⊢
  split_ifs at hk2 ⊢ with hk
  · have hdisj : Disjoint {v : Fin N × Fin r | (v.1 : ℕ) = T.pos j ∨ (v.1 : ℕ) = T.pos j + 1}
        {v : Fin N × Fin r | (v.1 : ℕ) < T.J k} := by
      rw [Set.disjoint_left]
      rintro v hv1 hv2
      simp only [Set.mem_ofPred_eq] at hv1 hv2
      omega
    refine ycond_keep LL (T.J k) (T.thr k) (T.phi p LL j) (fun c d x => ?_) (fun x hx => ?_) u hk2
    · exact FockB.ops_apply_comm hdisj (phi_mem LL T j h) (glAct_mem LL (T.J k) c d) x
    · refine ops_keep_supp _ _ (fun m m' hmm' hm => ?_) (phi_mem LL T j h) x hx
      have : wt LL (T.J k) 0 m = wt LL (T.J k) 0 m' := by
        unfold wt
        refine Finset.sum_congr rfl fun i' _ => ?_
        split_ifs with hi
        · rw [hmm' (i', 0) (by simp only [Set.mem_ofPred_eq]; omega)]
        · rw [hmm' (i', 0) (by simp only [Set.mem_ofPred_eq]; omega)]
        · rfl
      simp only [Set.mem_ofPred_eq] at hm ⊢
      rw [← this]; exact hm
  · rw [ycond_top]; exact Submodule.mem_top

end Keep2

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open Formalism.GM Formalism.GM.TM M MvPolynomial Finset

/- English proof (translation)
Take `⟨C₂, hC₂, hT⟩` from `hTie`. Take `⟨C₃, hC₃, hY⟩` from `hYP`. Use `⟨max 1 (max C₂ C₃), le_max_left _ _, ?_⟩` and prove the remaining obligations. Introduce `C hC p _ N r _ _ LL T a E κ n ρ h2p hr hρ hadm hE hS hdeg hz hκ hHP hHW hL4 nb f U V dg fw h1 h2 h3`. Establish `hops` using `hT p N r LL T a E κ n ρ h2p hr hρ hadm hE hS hdeg hz hκ hHP hHW hL4 nb f U V dg fw h1 h2 h3`.

Use `choose Tm πm Kf hK hTY hTint hadj hcomm hrank using hops`. Establish `hadm' : T.Admissible (LL.setTies T n)` using `hadm`. Use `set LL' := LL.setTies T n with hLL'`. Use `set Ysp : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) := Y p (r := r) LL' T.J T.thr with hYsp`. Use `set W : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) := Ysp ⊓ (Finset.univ : Finset (Fin T.t)).inf (fun i => LinearMap.ker (πm i - LinearMap.id)) with hW`.

Establish `hYpol : Ysp ≤ Pol p r LL'` using `inf_le_left`. Establish `hWY : W ≤ Ysp` using `inf_le_left`. Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).pos`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`. Establish `hlg` using `lg_nonneg p a r hr`.

Establish `hκ0 : 0 ≤ κ` using `le_trans (by positivity) hκ`. Establish `hCC₂ : C₂ ≤ C` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC`. Establish `hCC₃ : C₃ ≤ C` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC`. Establish `hsat : ∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), c ≠ 0 → x ∈ YZ p (r` using `r) LL' T.J T.thr → c • x ∈ W.restrictScalars ℤ_[p] ⊓ PolZ p r LL' → x ∈ W.restrictScalars ℤ_[p] ⊓ PolZ p r LL' := by`. Introduce `c x hc hx hcx`.

Use `Submodule.mem_inf.mpr ⟨?_, (Submodule.mem_inf.mp hx).2⟩` and prove the remaining obligations. Establish `hxY : x ∈ Ysp` using `(Submodule.mem_inf.mp hx).1`. Establish `hcW : c • x ∈ W` using `(Submodule.mem_inf.mp hcx).1`. Use `show x ∈ W`. Use `Submodule.mem_inf.mpr ⟨hxY, ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.mem_finsetInf]`. Introduce `i _`. Establish `hci` using `(Submodule.mem_finsetInf.mp (Submodule.mem_inf.mp hcW).2) i (Finset.mem_univ i)`. Rewrite `hci`, the goal using `[LinearMap.mem_ker]`. Rewrite `hci` using `[← algebraMap_smul ℚ_[p] c x, map_smul, smul_eq_zero]`.

Break down `hci with h | h` into its components or cases. Conclude with `absurd (PadicInt.ext (h.trans PadicInt.coe_zero.symm)) hc`. Conclude with `h`. Establish `hL1Y : W.restrictScalars ℤ_[p] ⊓ PolZ p r LL' ≤ YZ p (r` using `r) LL' T.J T.thr := inf_le_inf_right (PolZ p r LL') (show W.restrictScalars ℤ_[p] ≤ Ysp.restrictScalars ℤ_[p] from fun x hx => hWY hx)`. Use `⟨W.restrictScalars ℤ_[p] ⊓ PolZ p r LL', hL1Y, hsat, ?_, ?_⟩` and prove the remaining obligations.

Introduce `u hu hprim`. Establish `huY : u ∈ YZ p (r` using `r) LL' T.J T.thr := hL1Y hu`. Establish `hprimY : ∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), x ∈ YZ p (r` using `r) LL' T.J T.thr → u = c • x → IsUnit c := by`. Introduce `c x hx hux`. Distinguish the cases in `hc : c = 0`.

It suffices to derive a contradiction. Establish `hu0 : u = 0` using `by rw [hux, hc, zero_smul]`. Use `hprim 0 0 (Submodule.zero_mem _) (by rw [hu0, smul_zero])` as an intermediate fact. Conclude with `not_isUnit_zero this`. Conclude with `hprim c x (hsat c x hc hx (hux ▸ hu)) hux`.

Take `⟨z'', hz'', K₀, hK₀, hnorm⟩` from `hY p N r LL' T.J T.thr ρ a κ hr hκ hHP u huY hprimY`. Use `set e := ⌊E⌋₊ with he`. Set `Ts : Fin T.t → MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]` to `fun i => ((p : ℚ_[p]) ^ (Kf i)) • Tm i`. Establish `hTsZ : ∀ i, ∀ y ∈ YZ p (r` using `r) LL' T.J T.thr, Ts i y ∈ YZ p (r := r) LL' T.J T.thr := by`. Introduce `i y hy`.

Establish `hyY : y ∈ Ysp` using `(Submodule.mem_inf.mp hy).1`. Establish `h1 : Ts i y ∈ Ysp` using `Ysp.smul_mem _ (hTY i y hyY)`. Conclude with `Submodule.mem_inf.mpr ⟨h1, Submodule.mem_inf.mpr ⟨hYpol h1, hTint i y hy⟩⟩`. Establish `hTsY : ∀ i, ∀ y ∈ (Ysp : Set (MvPolynomial (Fin N × Fin r) ℚ_[p])), Ts i y ∈ Ysp` using `fun i y hy => Ysp.smul_mem _ (hTY i y hy)`. Use `set u' := lcomp Ts (List.finRange T.t) z'' with hu'`.

Establish `hu'Z : u' ∈ YZ p (r` using `r) LL' T.J T.thr := lcomp_keep Ts (YZ p (r := r) LL' T.J T.thr : Set _) (List.finRange T.t) (fun j _ => hTsZ j) z'' hz''`. Use `⟨u', hu'Z, ?_⟩` and prove the remaining obligations. Establish `hfix : ∀ i ∈ List.finRange T.t, πm i u = u`. Introduce `i _`. Establish `huW : u ∈ W` using `(Submodule.mem_inf.mp hu).1`.

Use `(Submodule.mem_finsetInf.mp (Submodule.mem_inf.mp huW).2) i (Finset.mem_univ i)` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`. Conclude with `this`. Establish `hpeel` using `peel (fockN p LL') (T.phi p LL') Ts πm (fun i => (p : ℚ_[p]) ^ (Kf i + e)) (fun i => (Y p (r := r) LL' T.J (T.thrUpTo i) : Set (MvPolynomial (Fin N × Fin r) ℚ_[p]))) (Ysp : Set (MvPolynomial (Fin N × Fin r) ℚ_[p])) (fun i => fun x hx => y_le_thrUpTo LL' T i hx) hTsY (fun i j hij …`. Rewrite using `[fockN_smul_right', hadj i u hu u' hu', pow_add]`.

Use the proof step `ring)`. Use the proof step `(List.finRange T.t) (List.pairwise_lt_finRange T.t) u (hWY (Submodule.mem_inf.mp hu).1) hfix z''`. Use the proof step `(Submodule.mem_inf.mp hz'').1`. Establish `hphis : T.phis p (r` using `r) LL' = lcomp (T.phi p (r := r) LL') (List.finRange T.t) := rfl`. Rewrite using `[hphis, hpeel]`.

Establish `hS' : (∑ i, ((Kf i + e : ℕ) : ℝ)) ≤ (T.t : ℝ) * (E + C * κ)`. Establish `hb : ∀ i, ((Kf i + e : ℕ) : ℝ) ≤ E + C * κ`. Introduce `i`. Use `push_cast`. Establish `h1` using `hK i`.

Establish `h2 : (e : ℝ) ≤ E` using `Nat.floor_le (by linarith)`. Establish `h3 : C₂ * κ ≤ C * κ` using `mul_le_mul_of_nonneg_right hCC₂ hκ0`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Establish `hK0' : (K₀ : ℝ) ≤ C * κ` using `hK₀.trans (mul_le_mul_of_nonneg_right hCC₃ hκ0)`.

Establish `hD : (((∑ i, (Kf i + e)) + K₀ : ℕ) : ℤ) ≤ ⌊(T.t : ℝ) * (E + C * κ) + C * κ⌋`. Apply `Int.le_floor.mpr` to reduce the goal to its premises. Establish `: (((∑ i, (Kf i + e)) + K₀ : ℕ) : ℝ) = (∑ i, ((Kf i + e : ℕ) : ℝ)) + K₀` using `by push_cast; rfl`. Rewrite using `[Int.cast_natCast, this]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hprod : ((List.finRange T.t).map (fun i => (p : ℚ_[p]) ^ (Kf i + e))).prod = (p : ℚ_[p]) ^ (∑ i, (Kf i + e))`. Rewrite using `[← Fin.prod_univ_def, Finset.prod_pow_eq_pow_sum]`. Rewrite using `[hprod, norm_mul, norm_pow, Padic.norm_p]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Nat.cast_add, neg_add, zpow_add₀ (ne_of_gt hp0), zpow_neg, zpow_natCast, inv_pow]`.

Use `_ ≤ (p : ℝ)⁻¹ ^ (∑ i, (Kf i + e)) * ‖fockN p LL' u z''‖ := mul_le_mul_of_nonneg_left hnorm (by positivity)`. Use `haveI := pol_finiteDimensional (p := p) (r := r) LL'`. Use `haveI : FiniteDimensional ℚ_[p] Ysp := Submodule.finiteDimensional_of_le hYpol`. Establish `e1 : Module.finrank ℤ_[p] (YZ p (r` using `r) LL' T.J T.thr) = Module.finrank ℚ_[p] Ysp := finrank_lattice LL' Ysp hYpol`. Establish `e2 : Module.finrank ℤ_[p] (W.restrictScalars ℤ_[p] ⊓ PolZ p r LL' : Submodule ℤ_[p] _) = Module.finrank ℚ_[p] W` using `finrank_lattice LL' W (hWY.trans hYpol)`.

Rewrite using `[e1, e2]`. Establish `hc` using `codim_inf_le Ysp (fun i => LinearMap.ker (πm i - LinearMap.id)) univ`. Use `(Nat.cast_le.mpr hc).trans ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_sum]`. Conclude with `Finset.sum_le_sum fun i _ => hrank i`.
-/
theorem partnerM_of_parts (hTie : TieOps) (hYP : YPartner) : PartnerM := by
  obtain ⟨C₂, hC₂, hT⟩ := hTie
  obtain ⟨C₃, hC₃, hY⟩ := hYP
  refine ⟨max 1 (max C₂ C₃), le_max_left _ _, ?_⟩
  intro C hC p _ N r _ _ LL T a E κ n ρ h2p hr hρ hadm hE hS hdeg hz hκ hHP hHW hL4 nb f U V dg fw h1 h2 h3
  have hops := hT p N r LL T a E κ n ρ h2p hr hρ hadm hE hS hdeg hz hκ hHP hHW hL4 nb f U V dg fw h1 h2 h3
  choose Tm πm Kf hK hTY hTint hadj hcomm hrank using hops
  have hadm' : T.Admissible (LL.setTies T n) := hadm
  set LL' := LL.setTies T n with hLL'
  set Ysp : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) := Y p (r := r) LL' T.J T.thr with hYsp
  set W : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
    Ysp ⊓ (Finset.univ : Finset (Fin T.t)).inf (fun i => LinearMap.ker (πm i - LinearMap.id)) with hW
  have hYpol : Ysp ≤ Pol p r LL' := inf_le_left
  have hWY : W ≤ Ysp := inf_le_left
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlg := lg_nonneg p a r hr
  have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ
  have hCC₂ : C₂ ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hCC₃ : C₃ ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have hsat : ∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), c ≠ 0 →
      x ∈ YZ p (r := r) LL' T.J T.thr → c • x ∈ W.restrictScalars ℤ_[p] ⊓ PolZ p r LL' →
      x ∈ W.restrictScalars ℤ_[p] ⊓ PolZ p r LL' := by
    intro c x hc hx hcx
    refine Submodule.mem_inf.mpr ⟨?_, (Submodule.mem_inf.mp hx).2⟩
    have hxY : x ∈ Ysp := (Submodule.mem_inf.mp hx).1
    have hcW : c • x ∈ W := (Submodule.mem_inf.mp hcx).1
    show x ∈ W
    refine Submodule.mem_inf.mpr ⟨hxY, ?_⟩
    rw [Submodule.mem_finsetInf]
    intro i _
    have hci := (Submodule.mem_finsetInf.mp (Submodule.mem_inf.mp hcW).2) i (Finset.mem_univ i)
    rw [LinearMap.mem_ker] at hci ⊢
    rw [← algebraMap_smul ℚ_[p] c x, map_smul, smul_eq_zero] at hci
    rcases hci with h | h
    · exact absurd (PadicInt.ext (h.trans PadicInt.coe_zero.symm)) hc
    · exact h
  have hL1Y : W.restrictScalars ℤ_[p] ⊓ PolZ p r LL' ≤ YZ p (r := r) LL' T.J T.thr :=
    inf_le_inf_right (PolZ p r LL') (show W.restrictScalars ℤ_[p] ≤ Ysp.restrictScalars ℤ_[p] from fun x hx => hWY hx)
  refine ⟨W.restrictScalars ℤ_[p] ⊓ PolZ p r LL', hL1Y, hsat, ?_, ?_⟩
  ·
    intro u hu hprim
    have huY : u ∈ YZ p (r := r) LL' T.J T.thr := hL1Y hu
    have hprimY : ∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), x ∈ YZ p (r := r) LL' T.J T.thr →
        u = c • x → IsUnit c := by
      intro c x hx hux
      by_cases hc : c = 0
      · exfalso
        have hu0 : u = 0 := by rw [hux, hc, zero_smul]
        have := hprim 0 0 (Submodule.zero_mem _) (by rw [hu0, smul_zero])
        exact not_isUnit_zero this
      · exact hprim c x (hsat c x hc hx (hux ▸ hu)) hux
    obtain ⟨z'', hz'', K₀, hK₀, hnorm⟩ := hY p N r LL' T.J T.thr ρ a κ hr hκ hHP u huY hprimY
    set e := ⌊E⌋₊ with he
    let Ts : Fin T.t → MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
      fun i => ((p : ℚ_[p]) ^ (Kf i)) • Tm i
    have hTsZ : ∀ i, ∀ y ∈ YZ p (r := r) LL' T.J T.thr, Ts i y ∈ YZ p (r := r) LL' T.J T.thr := by
      intro i y hy
      have hyY : y ∈ Ysp := (Submodule.mem_inf.mp hy).1
      have h1 : Ts i y ∈ Ysp := Ysp.smul_mem _ (hTY i y hyY)
      exact Submodule.mem_inf.mpr ⟨h1, Submodule.mem_inf.mpr ⟨hYpol h1, hTint i y hy⟩⟩
    have hTsY : ∀ i, ∀ y ∈ (Ysp : Set (MvPolynomial (Fin N × Fin r) ℚ_[p])), Ts i y ∈ Ysp :=
      fun i y hy => Ysp.smul_mem _ (hTY i y hy)
    set u' := lcomp Ts (List.finRange T.t) z'' with hu'
    have hu'Z : u' ∈ YZ p (r := r) LL' T.J T.thr :=
      lcomp_keep Ts (YZ p (r := r) LL' T.J T.thr : Set _) (List.finRange T.t) (fun j _ => hTsZ j) z'' hz''
    refine ⟨u', hu'Z, ?_⟩
    have hfix : ∀ i ∈ List.finRange T.t, πm i u = u := by
      intro i _
      have huW : u ∈ W := (Submodule.mem_inf.mp hu).1
      have := (Submodule.mem_finsetInf.mp (Submodule.mem_inf.mp huW).2) i (Finset.mem_univ i)
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
      exact this
    have hpeel := peel (fockN p LL') (T.phi p LL') Ts πm (fun i => (p : ℚ_[p]) ^ (Kf i + e))
      (fun i => (Y p (r := r) LL' T.J (T.thrUpTo i) : Set (MvPolynomial (Fin N × Fin r) ℚ_[p])))
      (Ysp : Set (MvPolynomial (Fin N × Fin r) ℚ_[p]))
      (fun i => fun x hx => y_le_thrUpTo LL' T i hx) hTsY
      (fun i j hij => phi_keeps LL' T hadm' i j hij)
      (fun i j hij => hcomm i j hij)
      (fun i u hu u' hu' => by
        show fockN p LL' (T.phi p LL' i u) (((p : ℚ_[p]) ^ (Kf i)) • Tm i u') = _
        rw [fockN_smul_right', hadj i u hu u' hu', pow_add]; ring)
      (List.finRange T.t) (List.pairwise_lt_finRange T.t) u (hWY (Submodule.mem_inf.mp hu).1) hfix z''
      (Submodule.mem_inf.mp hz'').1
    have hphis : T.phis p (r := r) LL' = lcomp (T.phi p (r := r) LL') (List.finRange T.t) := rfl
    rw [hphis, hpeel]
    have hS' : (∑ i, ((Kf i + e : ℕ) : ℝ)) ≤ (T.t : ℝ) * (E + C * κ) := by
      have hb : ∀ i, ((Kf i + e : ℕ) : ℝ) ≤ E + C * κ := by
        intro i; push_cast
        have h1 := hK i
        have h2 : (e : ℝ) ≤ E := Nat.floor_le (by linarith)
        have h3 : C₂ * κ ≤ C * κ := mul_le_mul_of_nonneg_right hCC₂ hκ0
        linarith
      calc (∑ i, ((Kf i + e : ℕ) : ℝ)) ≤ ∑ _i : Fin T.t, (E + C * κ) := Finset.sum_le_sum fun i _ => hb i
        _ = (T.t : ℝ) * (E + C * κ) := by simp; ring
    have hK0' : (K₀ : ℝ) ≤ C * κ := hK₀.trans (mul_le_mul_of_nonneg_right hCC₃ hκ0)
    have hD : (((∑ i, (Kf i + e)) + K₀ : ℕ) : ℤ) ≤ ⌊(T.t : ℝ) * (E + C * κ) + C * κ⌋ := by
      apply Int.le_floor.mpr
      have : (((∑ i, (Kf i + e)) + K₀ : ℕ) : ℝ) = (∑ i, ((Kf i + e : ℕ) : ℝ)) + K₀ := by push_cast; rfl
      rw [Int.cast_natCast, this]
      linarith
    have hprod : ((List.finRange T.t).map (fun i => (p : ℚ_[p]) ^ (Kf i + e))).prod =
        (p : ℚ_[p]) ^ (∑ i, (Kf i + e)) := by
      rw [← Fin.prod_univ_def, Finset.prod_pow_eq_pow_sum]
    rw [hprod, norm_mul, norm_pow, Padic.norm_p]
    calc (p : ℝ) ^ (-⌊(T.t : ℝ) * (E + C * κ) + C * κ⌋)
        ≤ (p : ℝ) ^ (-((((∑ i, (Kf i + e)) + K₀ : ℕ)) : ℤ)) := zpow_le_zpow_right₀ hp1.le (by omega)
      _ = (p : ℝ)⁻¹ ^ (∑ i, (Kf i + e)) * (p : ℝ) ^ (-(K₀ : ℤ)) := by
        rw [Nat.cast_add, neg_add, zpow_add₀ (ne_of_gt hp0), zpow_neg, zpow_natCast, inv_pow]
      _ ≤ (p : ℝ)⁻¹ ^ (∑ i, (Kf i + e)) * ‖fockN p LL' u z''‖ :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
  ·
    haveI := pol_finiteDimensional (p := p) (r := r) LL'
    haveI : FiniteDimensional ℚ_[p] Ysp := Submodule.finiteDimensional_of_le hYpol
    have e1 : Module.finrank ℤ_[p] (YZ p (r := r) LL' T.J T.thr) = Module.finrank ℚ_[p] Ysp :=
      finrank_lattice LL' Ysp hYpol
    have e2 : Module.finrank ℤ_[p] (W.restrictScalars ℤ_[p] ⊓ PolZ p r LL' : Submodule ℤ_[p] _) =
        Module.finrank ℚ_[p] W := finrank_lattice LL' W (hWY.trans hYpol)
    rw [e1, e2]
    have hc := codim_inf_le Ysp (fun i => LinearMap.ker (πm i - LinearMap.id)) univ
    refine (Nat.cast_le.mpr hc).trans ?_
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum fun i _ => hrank i

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open Formalism.GM Formalism.GM.TM M MvPolynomial Finset

section XD
variable {k σ : Type} [Field k]

/- English proof (translation)
Introduce `x hx`. Rewrite `hx` using `[MvPolynomial.mem_restrictSupport_iff]`. Rewrite using `[MvPolynomial.as_sum x, map_sum, Finset.mul_sum]`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Establish `hmQ : m ∈ Q` using `hx hm`.

Rewrite using `[pderiv_monomial, X, monomial_mul, one_mul]`. Distinguish the cases in `hv : m v = 0`. Rewrite using `[hv, Nat.cast_zero, mul_zero, map_zero]`. Conclude with `Submodule.zero_mem _`. Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`.

Use `(Finset.coe_subset.mpr support_monomial_subset).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.coe_singleton, Set.singleton_subset_iff]`. Conclude with `h m hmQ (Nat.one_le_iff_ne_zero.mpr hv)`.
-/
theorem XD_keep (u v : σ) (Q Q' : Set (σ →₀ ℕ))
    (h : ∀ m ∈ Q, 1 ≤ m v → Finsupp.single u 1 + (m - Finsupp.single v 1) ∈ Q') :
    ∀ x ∈ restrictSupport k Q, X u * pderiv v x ∈ restrictSupport k Q' := by
  intro x hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx
  rw [MvPolynomial.as_sum x, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hmQ : m ∈ Q := hx hm
  rw [pderiv_monomial, X, monomial_mul, one_mul]
  by_cases hv : m v = 0
  · rw [hv, Nat.cast_zero, mul_zero, map_zero]
    exact Submodule.zero_mem _
  · rw [MvPolynomial.mem_restrictSupport_iff]
    refine (Finset.coe_subset.mpr support_monomial_subset).trans ?_
    rw [Finset.coe_singleton, Set.singleton_subset_iff]
    exact h m hmQ (Nat.one_le_iff_ne_zero.mpr hv)

/- English proof (translation)
Rewrite using `[Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, Finsupp.single_apply]`. Apply the tactic sequence `split_ifs <;> subst_vars <;> omega`.
-/
theorem shift_apply [DecidableEq σ] (m : σ →₀ ℕ) (u v w : σ) (hv : 1 ≤ m v) :
    ((((Finsupp.single u 1 + (m - Finsupp.single v 1) : σ →₀ ℕ)) w : ℕ) : ℤ) =
      (m w : ℤ) + (if u = w then 1 else 0) - (if v = w then 1 else 0) := by
  rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> subst_vars <;> omega

end XD

section Gl
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

/- English proof (translation)
Introduce `x hx`. Unfold `glAct`. Rewrite using `[LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : (i : ℕ) < j`.

Distinguish the cases in `hvi : LL.vec i = true`. Simplify using `only [if_pos hi, if_pos hvi]`. Conclude with `XD_keep (i, c) (i, d) Q Q' (fun m hm h1 => hv i hi hvi m hm h1) x hx`. Simplify using `only [if_pos hi, if_neg hvi, LinearMap.neg_apply]`. Use `Submodule.neg_mem _ ?_` and prove the remaining obligations.

Establish `hf : LL.vec i = false` using `by simpa using hvi`. Conclude with `XD_keep (i, d) (i, c) Q Q' (fun m hm h1 => hc i hi hf m hm h1) x hx`. Simplify using `only [if_neg hi, LinearMap.zero_apply]`. Conclude with `Submodule.zero_mem _`.
-/
theorem glAct_keep (LL : Letters N) (j : ℕ) (c d : Fin r) (Q Q' : Set (Fin N × Fin r →₀ ℕ))
    (hv : ∀ i : Fin N, (i : ℕ) < j → LL.vec i = true → ∀ m ∈ Q, 1 ≤ m (i, d) →
      Finsupp.single (i, c) 1 + (m - Finsupp.single (i, d) 1) ∈ Q')
    (hc : ∀ i : Fin N, (i : ℕ) < j → LL.vec i = false → ∀ m ∈ Q, 1 ≤ m (i, c) →
      Finsupp.single (i, d) 1 + (m - Finsupp.single (i, c) 1) ∈ Q') :
    ∀ x ∈ restrictSupport ℚ_[p] Q, glAct p LL j c d x ∈ restrictSupport ℚ_[p] Q' := by
  intro x hx
  unfold glAct
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : (i : ℕ) < j
  · by_cases hvi : LL.vec i = true
    · simp only [if_pos hi, if_pos hvi]
      exact XD_keep (i, c) (i, d) Q Q' (fun m hm h1 => hv i hi hvi m hm h1) x hx
    · simp only [if_pos hi, if_neg hvi, LinearMap.neg_apply]
      refine Submodule.neg_mem _ ?_
      have hf : LL.vec i = false := by simpa using hvi
      exact XD_keep (i, d) (i, c) Q Q' (fun m hm h1 => hc i hi hf m hm h1) x hx
  · simp only [if_neg hi, LinearMap.zero_apply]
    exact Submodule.zero_mem _

/- English proof (translation)
Establish `key : ∀ (i : Fin N) (a b : Fin r) (m : Fin N × Fin r →₀ ℕ), MultiDeg LL m → 1 ≤ m (i, b) → MultiDeg LL (Finsupp.single (i, a) 1 + (m - Finsupp.single (i, b) 1))`. Introduce `i a b m hm hb i'`. Establish `h` using `hm i'`. Establish `: ((∑ c', ((Finsupp.single (i, a) 1 + (m - Finsupp.single (i, b) 1) : Fin N × Fin r →₀ ℕ)) (i', c') : ℕ) : ℤ) = ((∑ c', m (i', c') : ℕ) : ℤ)`. Rewrite using `[Nat.cast_sum, Nat.cast_sum]`.

Rewrite using `[Finset.sum_congr rfl (fun c' _ => shift_apply m (i, a) (i, b) (i', c') hb)]`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_add_distrib]`. Distinguish the cases in `hi : i = i'`. Substitute `hi` using the available equality. Simplify using `[Prod.mk.injEq]`.

Simplify using `[Prod.mk.injEq, hi]`. Use `Nat.cast_injective this` as an intermediate fact. Rewrite using `[this, h]`. Conclude with `glAct_keep LL j c d _ _ (fun i _ _ m hm hb => key i c d m hm hb) (fun i _ _ m hm hb => key i d c m hm hb)`.
-/
theorem glAct_pol (LL : Letters N) (j : ℕ) (c d : Fin r) :
    ∀ x ∈ Pol p r LL, glAct p LL j c d x ∈ Pol p r LL := by
  have key : ∀ (i : Fin N) (a b : Fin r) (m : Fin N × Fin r →₀ ℕ), MultiDeg LL m → 1 ≤ m (i, b) →
      MultiDeg LL (Finsupp.single (i, a) 1 + (m - Finsupp.single (i, b) 1)) := by
    intro i a b m hm hb i'
    have h := hm i'
    have : ((∑ c', ((Finsupp.single (i, a) 1 + (m - Finsupp.single (i, b) 1) : Fin N × Fin r →₀ ℕ)) (i', c') : ℕ) : ℤ) =
        ((∑ c', m (i', c') : ℕ) : ℤ) := by
      rw [Nat.cast_sum, Nat.cast_sum]
      rw [Finset.sum_congr rfl (fun c' _ => shift_apply m (i, a) (i, b) (i', c') hb)]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      by_cases hi : i = i'
      · subst hi
        simp [Prod.mk.injEq]
      · simp [Prod.mk.injEq, hi]
    have := Nat.cast_injective this
    rw [this, h]
  exact glAct_keep LL j c d _ _ (fun i _ _ m hm hb => key i c d m hm hb) (fun i _ _ m hm hb => key i d c m hm hb)

/- English proof (translation)
Unfold `wt`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem wt_eq (LL : Letters N) (j : ℕ) (c : Fin r) (m : Fin N × Fin r →₀ ℕ) :
    wt LL j c m = ∑ i : Fin N, (if (i : ℕ) < j then (if LL.vec i then (1 : ℤ) else -1) else 0) * (m (i, c) : ℤ) := by
  unfold wt
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Establish `e1 : ∀ e : Fin r, (∑ x : Fin N, (if (x : ℕ) < j then (if LL.vec x then (1 : ℤ) else -1) else 0) * (if (i, e) = (x, c') then (1 : ℤ) else 0)) = (if LL.vec i then (1 : ℤ) else -1) * (if e = c' then 1 else 0)`. Introduce `e`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[hi]`. Introduce `b _ hb`.

Simplify using `[Ne.symm hb]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`. Prove the components needed by the constructor for the conclusion. Introduce `hv hm1`.

Establish `hs` using `fun w => shift_apply m (i, c) (i, d) w hm1`. Rewrite using `[wt_eq, wt_eq]`. Simplify using `only [hs, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, e1, hv]`. Apply the tactic sequence `try simp`. Apply the tactic sequence `try (split_ifs <;> ring)`.

Introduce `hv hm1`. Establish `hs` using `fun w => shift_apply m (i, d) (i, c) w hm1`. Rewrite using `[wt_eq, wt_eq]`. Simplify using `only [hs, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, e1, hv]`. Apply the tactic sequence `try simp`.

Apply the tactic sequence `try (split_ifs <;> ring)`.
-/
theorem wt_shift (LL : Letters N) (j : ℕ) (c d c' : Fin r) (i : Fin N) (hi : (i : ℕ) < j)
    (m : Fin N × Fin r →₀ ℕ) :
    (LL.vec i = true → 1 ≤ m (i, d) → wt LL j c' (Finsupp.single (i, c) 1 + (m - Finsupp.single (i, d) 1) : Fin N × Fin r →₀ ℕ) =
      wt LL j c' m + (if c = c' then 1 else 0) - (if d = c' then 1 else 0)) ∧
    (LL.vec i = false → 1 ≤ m (i, c) → wt LL j c' (Finsupp.single (i, d) 1 + (m - Finsupp.single (i, c) 1) : Fin N × Fin r →₀ ℕ) =
      wt LL j c' m + (if c = c' then 1 else 0) - (if d = c' then 1 else 0)) := by
  have e1 : ∀ e : Fin r, (∑ x : Fin N, (if (x : ℕ) < j then (if LL.vec x then (1 : ℤ) else -1) else 0) *
      (if (i, e) = (x, c') then (1 : ℤ) else 0)) = (if LL.vec i then (1 : ℤ) else -1) * (if e = c' then 1 else 0) := by
    intro e
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ i) h
  constructor
  · intro hv hm1
    have hs := fun w => shift_apply m (i, c) (i, d) w hm1
    rw [wt_eq, wt_eq]
    simp only [hs, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, e1, hv]
    try simp
    try (split_ifs <;> ring)
  · intro hv hm1
    have hs := fun w => shift_apply m (i, d) (i, c) w hm1
    rw [wt_eq, wt_eq]
    simp only [hs, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, e1, hv]
    try simp
    try (split_ifs <;> ring)

end Gl

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open Formalism.GM Formalism.GM.TM M MvPolynomial Finset

section Wt
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

/- English proof (translation)
Proceed by induction on `x using MvPolynomial.induction_on'`. Name the introduced variables `n a`. Rewrite using `[pderiv_monomial, X, monomial_mul, one_mul, coeff_monomial, coeff_monomial]`. Distinguish the cases in `hn : n v = 0`. Simplify using `only [hn, Nat.cast_zero, mul_zero, ite_self] split_ifs with h`.

Substitute `h` using the available equality. Simplify using `[hn]`. Simplify using the standard rewrite rules. Establish `hsum : Finsupp.single v 1 + (n - Finsupp.single v 1) = n`. Use extensionality with `w`.

Simplify using `only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]`. Use `split_ifs with h`. Substitute `h` using the available equality. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.

Rewrite using `[hsum]`. Use `split_ifs with h`. Substitute `h` using the available equality. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

Name the introduced variables `f g hf hg`. Simplify using `only [map_add, mul_add, coeff_add, hf, hg]`.
-/
private theorem coeff_XD_lemma (v : Fin N × Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (m : Fin N × Fin r →₀ ℕ) : coeff m (X v * pderiv v x) = (m v : ℚ_[p]) * coeff m x := by
  induction x using MvPolynomial.induction_on'
  · rename_i n a
    rw [pderiv_monomial, X, monomial_mul, one_mul, coeff_monomial, coeff_monomial]
    by_cases hn : n v = 0
    · simp only [hn, Nat.cast_zero, mul_zero, ite_self]
      split_ifs with h
      · subst h; simp [hn]
      · simp
    · have hsum : Finsupp.single v 1 + (n - Finsupp.single v 1) = n := by
        ext w
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs with h
        · subst h; omega
        · simp
      rw [hsum]
      split_ifs with h
      · subst h; ring
      · simp
  · rename_i f g hf hg
    simp only [map_add, mul_add, coeff_add, hf, hg]

/- English proof (translation)
Unfold `glAct`. Rewrite using `[LinearMap.sum_apply, coeff_sum, wt_eq, Int.cast_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : (i : ℕ) < j`. Distinguish the cases in `hv : LL.vec i = true`.

Simplify using `only [if_pos h, if_pos hv] show coeff m (X (i, c) * pderiv (i, c) x) = _`. Rewrite using `[coeff_XD_lemma]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [if_pos h, if_neg hv, LinearMap.neg_apply, coeff_neg] show -coeff m (X (i, c) * pderiv (i, c) x) = _`.

Rewrite using `[coeff_XD_lemma]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [if_neg h]`. Simplify using the standard rewrite rules.
-/
theorem coeff_cartan (LL : Letters N) (j : ℕ) (c : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (m : Fin N × Fin r →₀ ℕ) : coeff m (glAct p LL j c c x) = ((wt LL j c m : ℤ) : ℚ_[p]) * coeff m x := by
  unfold glAct
  rw [LinearMap.sum_apply, coeff_sum, wt_eq, Int.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) < j
  · by_cases hv : LL.vec i = true
    · simp only [if_pos h, if_pos hv]
      show coeff m (X (i, c) * pderiv (i, c) x) = _
      rw [coeff_XD_lemma]
      push_cast
      ring
    · simp only [if_pos h, if_neg hv, LinearMap.neg_apply, coeff_neg]
      show -coeff m (X (i, c) * pderiv (i, c) x) = _
      rw [coeff_XD_lemma]
      push_cast
      ring
  · simp only [if_neg h]
    simp

/- English proof (translation)
Unfold `WtSpC at hx`. Rewrite `hx` using `[MvPolynomial.mem_restrictSupport_iff]`. Use extensionality with `m`. Rewrite using `[coeff_cartan, coeff_smul, smul_eq_mul]`. Distinguish the cases in `hm : coeff m x = 0`.

Rewrite using `[hm, mul_zero, mul_zero]`. Establish `h2 : ∀ c ∈ univ, wt LL j c m = μ c` using `hx (MvPolynomial.mem_support_iff.mpr hm)`. Rewrite using `[h2 c (Finset.mem_univ c)]`.
-/
theorem cartan_eig (LL : Letters N) (j : ℕ) (μ : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : x ∈ WtSpC p LL j univ μ) (c : Fin r) : glAct p LL j c c x = ((μ c : ℤ) : ℚ_[p]) • x := by
  unfold WtSpC at hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx
  ext m
  rw [coeff_cartan, coeff_smul, smul_eq_mul]
  by_cases hm : coeff m x = 0
  · rw [hm, mul_zero, mul_zero]
  · have h2 : ∀ c ∈ univ, wt LL j c m = μ c := hx (MvPolynomial.mem_support_iff.mpr hm)
    rw [h2 c (Finset.mem_univ c)]

/- English proof (translation)
Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `m hm`. Simplify using `only [Finset.mem_coe, MvPolynomial.mem_support_iff] at hm`. Establish `h1` using `congrArg (coeff m) hy`. Rewrite `h1` using `[coeff_cartan, coeff_smul, smul_eq_mul]`.

Establish `h2 : ((wt LL j c m : ℤ) : ℚ_[p]) = ((k : ℤ) : ℚ_[p])` using `mul_right_cancel₀ hm h1`. Use `show wt LL j c m = k`. Conclude with `h2` after adjusting the coercions.
-/
theorem eig_supp (LL : Letters N) (j : ℕ) (c : Fin r) (k : ℤ) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hy : glAct p LL j c c y = ((k : ℤ) : ℚ_[p]) • y) :
    y ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | wt LL j c m = k} := by
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  simp only [Finset.mem_coe, MvPolynomial.mem_support_iff] at hm
  have h1 := congrArg (coeff m) hy
  rw [coeff_cartan, coeff_smul, smul_eq_mul] at h1
  have h2 : ((wt LL j c m : ℤ) : ℚ_[p]) = ((k : ℤ) : ℚ_[p]) := mul_right_cancel₀ hm h1
  show wt LL j c m = k
  exact_mod_cast h2

/- English proof (translation)
Introduce `x hx`. Establish `heig : ∀ c, glAct p LL j c c (T x) = ((μ c : ℤ) : ℚ_[p]) • T x`. Introduce `c`. Rewrite using `[← hT, cartan_eig LL j μ x hx c, map_smul]`. Unfold `WtSpC`.

Rewrite using `[MvPolynomial.mem_restrictSupport_iff]`. Introduce `m hm`. Simplify using `only [Set.mem_setOf_eq]`. Introduce `c _`. Use `eig_supp LL j c (μ c) (T x) (heig c)` as an intermediate fact.

Rewrite `this` using `[MvPolynomial.mem_restrictSupport_iff]`. Conclude with `this hm`.
-/
theorem comm_wtsp (LL : Letters N) (j : ℕ) (T : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hT : ∀ c x, T (glAct p LL j c c x) = glAct p LL j c c (T x)) (μ : Fin r → ℤ) :
    ∀ x ∈ WtSpC p LL j univ μ, T x ∈ WtSpC p LL j univ μ := by
  intro x hx
  have heig : ∀ c, glAct p LL j c c (T x) = ((μ c : ℤ) : ℚ_[p]) • T x := by
    intro c
    rw [← hT, cartan_eig LL j μ x hx c, map_smul]
  unfold WtSpC
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  simp only [Set.mem_setOf_eq]
  intro c _
  have := eig_supp LL j c (μ c) (T x) (heig c)
  rw [MvPolynomial.mem_restrictSupport_iff] at this
  exact this hm

/- English proof (translation)
Introduce `x hx`. Rewrite using `[x.as_sum, map_sum]`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Establish `hmon : glAct p LL j 0 0 (monomial m (coeff m x)) = ((wt LL j 0 m : ℤ) : ℚ_[p]) • monomial m (coeff m x)`. Use extensionality with `m'`.

Rewrite using `[coeff_cartan, coeff_smul, coeff_monomial, smul_eq_mul]`. Use `split_ifs with h`. Rewrite using `[h]`. Simplify using the standard rewrite rules. Establish `h1 : glAct p LL j 0 0 (T (monomial m (coeff m x))) = ((wt LL j 0 m : ℤ) : ℚ_[p]) • T (monomial m (coeff m x))`.

Rewrite using `[← hT, hmon, map_smul]`. Establish `h2` using `eig_supp LL j 0 _ _ h1`. Rewrite `h2`, the goal using `[mem_restrictSupport_iff]`. Introduce `m' hm'`. Establish `h3 : wt LL j 0 m' = wt LL j 0 m` using `h2 hm'`.

Rewrite `hx` using `[mem_restrictSupport_iff]`. Establish `h4` using `hx (Finset.mem_coe.mpr hm)`. Simplify using `only [Set.mem_ofPred_eq] at h4 ⊢`. Rewrite using `[h3]`. Conclude with `h4`.
-/
theorem comm_preserves_weight_le [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ)
    (T : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hT : ∀ x, T (glAct p LL j 0 0 x) = glAct p LL j 0 0 (T x)) :
    ∀ x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt},
      T x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
  intro x hx
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hmon : glAct p LL j 0 0 (monomial m (coeff m x)) = ((wt LL j 0 m : ℤ) : ℚ_[p]) • monomial m (coeff m x) := by
    ext m'
    rw [coeff_cartan, coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs with h
    · rw [h]
    · simp
  have h1 : glAct p LL j 0 0 (T (monomial m (coeff m x))) = ((wt LL j 0 m : ℤ) : ℚ_[p]) • T (monomial m (coeff m x)) := by
    rw [← hT, hmon, map_smul]
  have h2 := eig_supp LL j 0 _ _ h1
  rw [mem_restrictSupport_iff] at h2 ⊢
  intro m' hm'
  have h3 : wt LL j 0 m' = wt LL j 0 m := h2 hm'
  rw [mem_restrictSupport_iff] at hx
  have h4 := hx (Finset.mem_coe.mpr hm)
  simp only [Set.mem_ofPred_eq] at h4 ⊢
  rw [h3]; exact h4

def shiftW {r : ℕ} (μ : Fin r → ℤ) (c d : Fin r) : Fin r → ℤ :=
  fun c' => μ c' + (if c = c' then 1 else 0) - (if d = c' then 1 else 0)

/- English proof (translation)
Unfold `WtSpC`. Apply `glAct_keep` to reduce the goal to its premises. Introduce `i hi hvi m hm h1`. Simplify using `only [Set.mem_setOf_eq] at hm ⊢`. Introduce `c' _`.

Unfold `shiftW`. Rewrite using `[(wt_shift LL j c d c' i hi m).1 hvi h1, hm c' (Finset.mem_univ c')]`. Introduce `i hi hvi m hm h1`. Simplify using `only [Set.mem_setOf_eq] at hm ⊢`. Introduce `c' _`.

Unfold `shiftW`. Rewrite using `[(wt_shift LL j c d c' i hi m).2 hvi h1, hm c' (Finset.mem_univ c')]`.
-/
theorem glAct_wtsp (LL : Letters N) (j : ℕ) (c d : Fin r) (μ : Fin r → ℤ) :
    ∀ x ∈ WtSpC p LL j univ μ, glAct p LL j c d x ∈ WtSpC p LL j univ (shiftW μ c d) := by
  unfold WtSpC
  apply glAct_keep
  · intro i hi hvi m hm h1
    simp only [Set.mem_setOf_eq] at hm ⊢
    intro c' _
    unfold shiftW
    rw [(wt_shift LL j c d c' i hi m).1 hvi h1, hm c' (Finset.mem_univ c')]
  · intro i hi hvi m hm h1
    simp only [Set.mem_setOf_eq] at hm ⊢
    intro c' _
    unfold shiftW
    rw [(wt_shift LL j c d c' i hi m).2 hvi h1, hm c' (Finset.mem_univ c')]

/- English proof (translation)
Establish `hc0 : ¬ c = 0`. Introduce and unpack `rfl`. Establish `h1 : (d : ℕ) < ((0 : Fin r) : ℕ)` using `hdc`. Simplify using `at h1`. Apply `glAct_keep` to reduce the goal to its premises.

Introduce `i hi hvi m hm h1`. Simplify using `only [Set.mem_setOf_eq] at hm ⊢`. Rewrite using `[(wt_shift LL j c d 0 i hi m).1 hvi h1, if_neg hc0]`. Apply the tactic sequence `exact le_trans (WithTop.coe_le_coe.mpr (by split_ifs <;> omega)) hm`. Introduce `i hi hvi m hm h1`.

Simplify using `only [Set.mem_setOf_eq] at hm ⊢`. Rewrite using `[(wt_shift LL j c d 0 i hi m).2 hvi h1, if_neg hc0]`. Apply the tactic sequence `exact le_trans (WithTop.coe_le_coe.mpr (by split_ifs <;> omega)) hm`.
-/
theorem lower_action_preserves_weight_le [NeZero r] (LL : Letters N) (j : ℕ) (c d : Fin r) (hdc : d < c) (Mt : WithTop ℤ) :
    ∀ x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt},
      glAct p LL j c d x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
  have hc0 : ¬ c = 0 := by
    rintro rfl
    have h1 : (d : ℕ) < ((0 : Fin r) : ℕ) := hdc
    simp at h1
  apply glAct_keep
  · intro i hi hvi m hm h1
    simp only [Set.mem_setOf_eq] at hm ⊢
    rw [(wt_shift LL j c d 0 i hi m).1 hvi h1, if_neg hc0]
    exact le_trans (WithTop.coe_le_coe.mpr (by split_ifs <;> omega)) hm
  · intro i hi hvi m hm h1
    simp only [Set.mem_setOf_eq] at hm ⊢
    rw [(wt_shift LL j c d 0 i hi m).2 hvi h1, if_neg hc0]
    exact le_trans (WithTop.coe_le_coe.mpr (by split_ifs <;> omega)) hm

end Wt

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open Formalism.GM Formalism.GM.TM M MvPolynomial Finset

section Comm
variable {k σ : Type} [Field k]

/- English proof (translation)
Establish `hX : ∀ (l i : σ) (n : σ), pderiv l (pderiv i (X n : MvPolynomial σ k)) = 0`. Introduce `l i n`. Distinguish the cases in `h : n = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[pderiv_X_of_ne h, map_zero]`. Apply `MvPolynomial.induction_on g` to reduce the goal to its premises. Introduce `a`. Simplify using the standard rewrite rules. Introduce `p q hp hq`.

Simplify using `only [map_add, hp, hq]`. Introduce `p n hp`. Simplify using `only [Derivation.leibniz, smul_eq_mul, map_add, hp, hX, mul_zero, zero_add, add_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem pderiv_pderiv_lemma [DecidableEq σ] (i j : σ) (g : MvPolynomial σ k) :
    pderiv i (pderiv j g) = pderiv j (pderiv i g) := by
  have hX : ∀ (l i : σ) (n : σ), pderiv l (pderiv i (X n : MvPolynomial σ k)) = 0 := by
    intro l i n
    by_cases h : n = i
    · subst h; simp
    · rw [pderiv_X_of_ne h, map_zero]
  apply MvPolynomial.induction_on g
  · intro a; simp
  · intro p q hp hq; simp only [map_add, hp, hq]
  · intro p n hp
    simp only [Derivation.leibniz, smul_eq_mul, map_add, hp, hX, mul_zero, zero_add, add_zero]
    ring

/- English proof (translation)
Establish `hXa : ∀ a b : σ, pderiv b (X a : MvPolynomial σ k) = if a = b then 1 else 0`. Introduce `a b`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg h, pderiv_X_of_ne h]`. Simplify using `only [Derivation.leibniz, smul_eq_mul, hXa]`. Rewrite using `[pderiv_pderiv_lemma v v' g]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem comm_XD [DecidableEq σ] (u v u' v' : σ) (g : MvPolynomial σ k) :
    X u * pderiv v (X u' * pderiv v' g) - X u' * pderiv v' (X u * pderiv v g) =
      (if u' = v then X u * pderiv v' g else 0) - (if u = v' then X u' * pderiv v g else 0) := by
  have hXa : ∀ a b : σ, pderiv b (X a : MvPolynomial σ k) = if a = b then 1 else 0 := by
    intro a b
    by_cases h : a = b
    · subst h; simp
    · rw [if_neg h, pderiv_X_of_ne h]
  simp only [Derivation.leibniz, smul_eq_mul, hXa]
  rw [pderiv_pderiv_lemma v v' g]
  split_ifs <;> ring

end Comm

section Terms
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

noncomputable def tm (LL : Letters N) (j : ℕ) (i : Fin N) (c d : Fin r) :
    Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  if (i : ℕ) < j then
    (if LL.vec i then (LinearMap.mulLeft ℚ_[p] (X (i, c))) ∘ₗ (pderiv (i, d)).toLinearMap
     else -((LinearMap.mulLeft ℚ_[p] (X (i, d))) ∘ₗ (pderiv (i, c)).toLinearMap))
  else 0

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem glAct_eq_sum (LL : Letters N) (j : ℕ) (c d : Fin r) :
    glAct p LL j c d = ∑ i : Fin N, tm (p := p) LL j i c d := rfl

/- English proof (translation)
Unfold `tm FockB.Ops`. Use `split_ifs with hi hv`. Establish `h1 : (LinearMap.mulLeft ℚ_[p] (X (i, c)) : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈ Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | v.1 = i})` using `Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, c), rfl, Or.inl rfl⟩)`. Establish `h2 : ((pderiv (R` using `ℚ_[p]) (i, d) : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈ Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | v.1 = i}) := Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, d), rfl, Or.inr rfl⟩)`. Conclude with `Subalgebra.mul_mem _ h1 h2`.

Establish `h1 : (LinearMap.mulLeft ℚ_[p] (X (i, d)) : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈ Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | v.1 = i})` using `Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, d), rfl, Or.inl rfl⟩)`. Establish `h2 : ((pderiv (R` using `ℚ_[p]) (i, c) : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈ Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | v.1 = i}) := Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, c), rfl, Or.inr rfl⟩)`. Conclude with `Subalgebra.neg_mem _ (Subalgebra.mul_mem _ h1 h2)`. Conclude with `Subalgebra.zero_mem _`.
-/
theorem tm_mem (LL : Letters N) (j : ℕ) (i : Fin N) (c d : Fin r) :
    tm (p := p) LL j i c d ∈ FockB.Ops {v : Fin N × Fin r | v.1 = i} := by
  unfold tm FockB.Ops
  split_ifs with hi hv
  · have h1 : (LinearMap.mulLeft ℚ_[p] (X (i, c)) : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈
        Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | v.1 = i}) :=
      Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, c), rfl, Or.inl rfl⟩)
    have h2 : ((pderiv (R := ℚ_[p]) (i, d) : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈ Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | v.1 = i}) :=
      Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, d), rfl, Or.inr rfl⟩)
    exact Subalgebra.mul_mem _ h1 h2
  · have h1 : (LinearMap.mulLeft ℚ_[p] (X (i, d)) : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈
        Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | v.1 = i}) :=
      Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, d), rfl, Or.inl rfl⟩)
    have h2 : ((pderiv (R := ℚ_[p]) (i, c) : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈ Algebra.adjoin ℚ_[p] (FockB.atoms {v : Fin N × Fin r | v.1 = i}) :=
      Algebra.subset_adjoin (by simp only [FockB.atoms, Set.mem_setOf_eq]; exact ⟨(i, c), rfl, Or.inr rfl⟩)
    exact Subalgebra.neg_mem _ (Subalgebra.mul_mem _ h1 h2)
  · exact Subalgebra.zero_mem _

/- English proof (translation)
Establish `hcomm : ∀ u v u' v' : Fin N × Fin r, u.1 = i → v.1 = i → u'.1 = i' → v'.1 = i' → X u * pderiv v (X u' * pderiv v' y) = X u' * pderiv v' (X u * pderiv v y)`. Introduce `u v u' v' hu hv hu' hv'`. Establish `h1 : u' ≠ v` using `fun h => hii (by rw [← hv, ← h, hu'])`. Establish `h2 : u ≠ v'` using `fun h => hii (by rw [← hu, h, hv'])`. Use `comm_XD (k := ℚ_[p]) u v u' v' y` as an intermediate fact.

Rewrite `this` using `[if_neg h1, if_neg h2, sub_zero, sub_eq_zero]`. Conclude with `this`. Establish `hform : ∀ (l : Fin N) (e f : Fin r), ∃ (α : ℚ_[p]) (u v : Fin r), ∀ z, tm (p` using `p) LL j l e f z = α • (X (l, u) * pderiv (l, v) z) := by`. Introduce `l e f`. Distinguish the cases in `hl : (l : ℕ) < j`.

Distinguish the cases in `hv : LL.vec l = true`. Use `⟨1, e, f, fun z => ?_⟩` and prove the remaining obligations. Simplify using `only [tm, if_pos hl, if_pos hv, one_smul]`. Both sides reduce to the same expression. Use `⟨-1, f, e, fun z => ?_⟩` and prove the remaining obligations.

Simplify using `only [tm, if_pos hl, if_neg hv, neg_one_smul]`. Both sides reduce to the same expression. Use `⟨0, e, f, fun z => ?_⟩` and prove the remaining obligations. Simplify using `only [tm, if_neg hl, zero_smul]`. Both sides reduce to the same expression.

Take `⟨α, u, v, hα⟩` from `hform i c d`. Take `⟨β, u', v', hβ⟩` from `hform i' a b`. Simplify using `only [hα, hβ, Derivation.map_smul, map_smul, mul_smul_comm, smul_smul]`. Rewrite using `[mul_comm β α, hcomm (i, u) (i, v) (i', u') (i', v') rfl rfl rfl rfl]`.
-/
theorem tm_comm_ne (LL : Letters N) (j : ℕ) (i i' : Fin N) (hii : i ≠ i') (c d a b : Fin r)
    (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    tm (p := p) LL j i c d (tm (p := p) LL j i' a b y) = tm (p := p) LL j i' a b (tm (p := p) LL j i c d y) := by
  have hcomm : ∀ u v u' v' : Fin N × Fin r, u.1 = i → v.1 = i → u'.1 = i' → v'.1 = i' →
      X u * pderiv v (X u' * pderiv v' y) = X u' * pderiv v' (X u * pderiv v y) := by
    intro u v u' v' hu hv hu' hv'
    have h1 : u' ≠ v := fun h => hii (by rw [← hv, ← h, hu'])
    have h2 : u ≠ v' := fun h => hii (by rw [← hu, h, hv'])
    have := comm_XD (k := ℚ_[p]) u v u' v' y
    rw [if_neg h1, if_neg h2, sub_zero, sub_eq_zero] at this
    exact this
  have hform : ∀ (l : Fin N) (e f : Fin r), ∃ (α : ℚ_[p]) (u v : Fin r),
      ∀ z, tm (p := p) LL j l e f z = α • (X (l, u) * pderiv (l, v) z) := by
    intro l e f
    by_cases hl : (l : ℕ) < j
    · by_cases hv : LL.vec l = true
      · refine ⟨1, e, f, fun z => ?_⟩
        simp only [tm, if_pos hl, if_pos hv, one_smul]
        rfl
      · refine ⟨-1, f, e, fun z => ?_⟩
        simp only [tm, if_pos hl, if_neg hv, neg_one_smul]
        rfl
    · refine ⟨0, e, f, fun z => ?_⟩
      simp only [tm, if_neg hl, zero_smul]
      rfl
  obtain ⟨α, u, v, hα⟩ := hform i c d
  obtain ⟨β, u', v', hβ⟩ := hform i' a b
  simp only [hα, hβ, Derivation.map_smul, map_smul, mul_smul_comm, smul_smul]
  rw [mul_comm β α, hcomm (i, u) (i, v) (i', u') (i', v') rfl rfl rfl rfl]

/- English proof (translation)
Establish `key` using `comm_XD (k := ℚ_[p]) (i, c) (i, d) (i, a) (i, b) y`. Establish `key2` using `comm_XD (k := ℚ_[p]) (i, d) (i, c) (i, b) (i, a) y`. Distinguish the cases in `hij : (i : ℕ) < j`. Distinguish the cases in `hv : LL.vec i = true`. Simplify using `only [tm, if_pos hij, if_pos hv] show X (i, c) * pderiv (i, d) (X (i, a) * pderiv (i, b) y) - X (i, a) * pderiv (i, b) (X (i, c) * pderiv (i, d) y) = (if d = a then X (i, c) * pderiv (i, b) y else 0) - (if b = c then X (i, a) * pderiv (i, d) y else 0)`.

Rewrite using `[key]`. Apply the tactic sequence `rcases eq_or_ne d a with hda | hda <;> rcases eq_or_ne b c with hbc | hbc`. Substitute `hda` using the available equality. Substitute `hbc` using the available equality. Simplify using the standard rewrite rules.

Substitute `hda` using the available equality. Simplify using `[hbc, hbc.symm]`. Substitute `hbc` using the available equality. Simplify using `[hda, hda.symm]`. Simplify using `[hda, hbc, hda.symm, hbc.symm]`.

Simplify using `only [tm, if_pos hij, if_neg hv] show -(X (i, d) * pderiv (i, c) (-(X (i, b) * pderiv (i, a) y))) - -(X (i, b) * pderiv (i, a) (-(X (i, d) * pderiv (i, c) y))) = (if d = a then -(X (i, b) * pderiv (i, c) y) else 0) - (if b = c then -(X (i, d) * pderiv (i, a) y) else 0)`. Simplify using `only [map_neg, mul_neg, neg_neg]`. Rewrite using `[key2]`. Apply the tactic sequence `rcases eq_or_ne d a with hda | hda <;> rcases eq_or_ne b c with hbc | hbc`. Substitute `hda` using the available equality.

Substitute `hbc` using the available equality. Simplify using `[sub_neg_eq_add, neg_add_eq_sub]`. Substitute `hda` using the available equality. Simplify using `[hbc, hbc.symm, sub_neg_eq_add, neg_add_eq_sub]`. Substitute `hbc` using the available equality.

Simplify using `[hda, hda.symm, sub_neg_eq_add, neg_add_eq_sub]`. Simplify using `[hda, hbc, hda.symm, hbc.symm]`. Simplify using `only [tm, if_neg hij]`. Simplify using the standard rewrite rules.
-/
theorem tm_comm_eq (LL : Letters N) (j : ℕ) (i : Fin N) (c d a b : Fin r)
    (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    tm (p := p) LL j i c d (tm (p := p) LL j i a b y) - tm (p := p) LL j i a b (tm (p := p) LL j i c d y) =
      (if d = a then tm (p := p) LL j i c b y else 0) - (if b = c then tm (p := p) LL j i a d y else 0) := by
  have key := comm_XD (k := ℚ_[p]) (i, c) (i, d) (i, a) (i, b) y
  have key2 := comm_XD (k := ℚ_[p]) (i, d) (i, c) (i, b) (i, a) y
  by_cases hij : (i : ℕ) < j
  · by_cases hv : LL.vec i = true
    · simp only [tm, if_pos hij, if_pos hv]
      show X (i, c) * pderiv (i, d) (X (i, a) * pderiv (i, b) y) -
          X (i, a) * pderiv (i, b) (X (i, c) * pderiv (i, d) y) =
        (if d = a then X (i, c) * pderiv (i, b) y else 0) - (if b = c then X (i, a) * pderiv (i, d) y else 0)
      rw [key]
      rcases eq_or_ne d a with hda | hda <;> rcases eq_or_ne b c with hbc | hbc
      · subst hda; subst hbc; simp
      · subst hda; simp [hbc, hbc.symm]
      · subst hbc; simp [hda, hda.symm]
      · simp [hda, hbc, hda.symm, hbc.symm]
    · simp only [tm, if_pos hij, if_neg hv]
      show -(X (i, d) * pderiv (i, c) (-(X (i, b) * pderiv (i, a) y))) -
          -(X (i, b) * pderiv (i, a) (-(X (i, d) * pderiv (i, c) y))) =
        (if d = a then -(X (i, b) * pderiv (i, c) y) else 0) - (if b = c then -(X (i, d) * pderiv (i, a) y) else 0)
      simp only [map_neg, mul_neg, neg_neg]
      rw [key2]
      rcases eq_or_ne d a with hda | hda <;> rcases eq_or_ne b c with hbc | hbc
      · subst hda; subst hbc; simp [sub_neg_eq_add, neg_add_eq_sub]
      · subst hda; simp [hbc, hbc.symm, sub_neg_eq_add, neg_add_eq_sub]
      · subst hbc; simp [hda, hda.symm, sub_neg_eq_add, neg_add_eq_sub]
      · simp [hda, hbc, hda.symm, hbc.symm]
  · simp only [tm, if_neg hij]
    simp

/- English proof (translation)
Simplify using `only [glAct_eq_sum, LinearMap.sum_apply, map_sum]`. Rewrite using `[Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun o n => tm (p := p) LL j n c d (tm (p := p) LL j o a b x)), ← Finset.sum_sub_distrib]`. Establish `hrow : ∀ i : Fin N, (∑ i', tm (p` using `p) LL j i c d (tm (p := p) LL j i' a b x)) - ∑ i', tm (p := p) LL j i' a b (tm (p := p) LL j i c d x) = (if d = a then tm (p := p) LL j i c b x else 0) - (if b = c then tm (p := p) LL j i a d x else 0) := by`. Introduce `i`. Rewrite using `[← Finset.sum_sub_distrib, Finset.sum_eq_single i, tm_comm_eq]`.

Introduce `i' _ hi'`. Rewrite using `[tm_comm_ne LL j i i' (Ne.symm hi') c d a b x, sub_self]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`. Rewrite using `[Finset.sum_congr rfl (fun i _ => hrow i)]`.

Apply the tactic sequence `split_ifs <;> simp [Finset.sum_sub_distrib]`.
-/
theorem glAct_comm (LL : Letters N) (j : ℕ) (c d a b : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL j c d (glAct p LL j a b x) - glAct p LL j a b (glAct p LL j c d x) =
      (if d = a then glAct p LL j c b x else 0) - (if b = c then glAct p LL j a d x else 0) := by
  simp only [glAct_eq_sum, LinearMap.sum_apply, map_sum]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun o n => tm (p := p) LL j n c d (tm (p := p) LL j o a b x)), ← Finset.sum_sub_distrib]
  have hrow : ∀ i : Fin N, (∑ i', tm (p := p) LL j i c d (tm (p := p) LL j i' a b x)) -
      ∑ i', tm (p := p) LL j i' a b (tm (p := p) LL j i c d x) =
      (if d = a then tm (p := p) LL j i c b x else 0) - (if b = c then tm (p := p) LL j i a d x else 0) := by
    intro i
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i, tm_comm_eq]
    · intro i' _ hi'
      rw [tm_comm_ne LL j i i' (Ne.symm hi') c d a b x, sub_self]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [Finset.sum_congr rfl (fun i _ => hrow i)]
  split_ifs <;> simp [Finset.sum_sub_distrib]

end Terms

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open Formalism.GM Formalism.GM.TM M MvPolynomial Finset

section Gen
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Introduce `x`. Establish `hPP : ∀ z, P (P z) = P z` using `fun z => by simpa using LinearMap.congr_fun hP z`. Take `⟨y, hy⟩` from `hr _ (LinearMap.mem_range_self P x)`. Establish `h2 : x - P x ∈ LinearMap.ker P` using `by rw [LinearMap.mem_ker, map_sub, hPP, sub_self]`. Establish `h3` using `hk _ h2`.

Rewrite `h3` using `[LinearMap.mem_ker]`. Simplify using `only [map_sub] at h3`. Rewrite `h3` using `[sub_eq_zero]`. Rewrite using `[h3, ← hy, hPP]`.
-/
theorem comm_of_stable (P Q : V →ₗ[K] V) (hP : P ∘ₗ P = P) (hr : ∀ x ∈ LinearMap.range P, Q x ∈ LinearMap.range P)
    (hk : ∀ x ∈ LinearMap.ker P, Q x ∈ LinearMap.ker P) : ∀ x, P (Q x) = Q (P x) := by
  intro x
  have hPP : ∀ z, P (P z) = P z := fun z => by simpa using LinearMap.congr_fun hP z
  obtain ⟨y, hy⟩ := hr _ (LinearMap.mem_range_self P x)
  have h2 : x - P x ∈ LinearMap.ker P := by rw [LinearMap.mem_ker, map_sub, hPP, sub_self]
  have h3 := hk _ h2
  rw [LinearMap.mem_ker] at h3
  simp only [map_sub] at h3
  rw [sub_eq_zero] at h3
  rw [h3, ← hy, hPP]

end Gen

section Rep
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

/- English proof (translation)
Rewrite using `[ProjS.eulL_of_support t 1 (X (t c)) ?_, Nat.cast_one, one_smul]`. Introduce `m hm`. Rewrite `hm` using `[support_X, Finset.mem_singleton]`. Substitute `hm` using the available equality. Rewrite using `[Finset.sum_eq_single c]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[Finsupp.single_apply, if_neg (fun h => hb (ht h).symm)]`. Simplify using the standard rewrite rules.
-/
theorem eulX {σ : Type} {s : ℕ} (t : Fin s → σ) (ht : Function.Injective t) (c : Fin s) :
    ProjS.eulL t (X (t c) : MvPolynomial σ ℚ_[p]) = X (t c) := by
  classical
  rw [ProjS.eulL_of_support t 1 (X (t c)) ?_, Nat.cast_one, one_smul]
  intro m hm
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hb; rw [Finsupp.single_apply, if_neg (fun h => hb (ht h).symm)]
  · simp

/- English proof (translation)
Rewrite using `[ProjS.eulL_mul, eulX t ht, ProjS.eulL_pderiv_mem t ht d g]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eul_XD {σ : Type} {s : ℕ} (t : Fin s → σ) (ht : Function.Injective t) (c d : Fin s)
    (g : MvPolynomial σ ℚ_[p]) :
    ProjS.eulL t (X (t c) * pderiv (t d) g) = X (t c) * pderiv (t d) (ProjS.eulL t g) := by
  rw [ProjS.eulL_mul, eulX t ht, ProjS.eulL_pderiv_mem t ht d g]; ring

/- English proof (translation)
Establish `ht : Function.Injective (fun c : Fin r => (i0, c))` using `fun a b h => (Prod.mk.inj h).2`. Rewrite using `[glAct_eq_sum, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i = i0`. Substitute `hi` using the available equality.

Unfold `tm`. Use `split_ifs with h1 h2`. Simplify using `only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]`. Conclude with `eul_XD (fun c : Fin r => (i, c)) ht c d x`. Simplify using `only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, map_neg]`.

Rewrite using `[eul_XD (fun c : Fin r => (i, c)) ht d c x]`. Simplify using the standard rewrite rules. Establish `hdisj : Disjoint {v : Fin N × Fin r | v.1 = i} {v : Fin N × Fin r | v.1 = i0}`. Rewrite using `[Set.disjoint_left]`. Introduce and unpack `v h1 h2`.

Simplify using `only [Set.mem_ofPred_eq] at h1 h2`. Conclude with `hi (h1 ▸ h2)`. Conclude with `(FockB.ops_apply_comm hdisj (tm_mem LL j i c d) (FockB.eulL_mem (S := {v : Fin N × Fin r | v.1 = i0}) (fun c : Fin r => (i0, c)) (fun c => rfl)) x).symm`.
-/
theorem eul_glAct (LL : Letters N) (j : ℕ) (i0 : Fin N) (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    ProjS.eulL (fun c : Fin r => (i0, c)) (glAct p LL j c d x) = glAct p LL j c d (ProjS.eulL (fun c : Fin r => (i0, c)) x) := by
  have ht : Function.Injective (fun c : Fin r => (i0, c)) := fun a b h => (Prod.mk.inj h).2
  rw [glAct_eq_sum, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = i0
  · subst hi
    unfold tm
    split_ifs with h1 h2
    · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
      exact eul_XD (fun c : Fin r => (i, c)) ht c d x
    · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, map_neg]
      rw [eul_XD (fun c : Fin r => (i, c)) ht d c x]
    · simp
  · have hdisj : Disjoint {v : Fin N × Fin r | v.1 = i} {v : Fin N × Fin r | v.1 = i0} := by
      rw [Set.disjoint_left]; rintro v h1 h2
      simp only [Set.mem_ofPred_eq] at h1 h2; exact hi (h1 ▸ h2)
    exact (FockB.ops_apply_comm hdisj (tm_mem LL j i c d)
      (FockB.eulL_mem (S := {v : Fin N × Fin r | v.1 = i0}) (fun c : Fin r => (i0, c)) (fun c => rfl)) x).symm

/- English proof (translation)
Introduce `x hx`. Unfold `IsoC at hx ⊢`. Rewrite `hx`, the goal using `[Submodule.mem_sInf]`. Introduce `S hS`. Conclude with `hS.2 c (Finset.mem_univ _) d (Finset.mem_univ _) x (hx S hS)`.
-/
theorem isoC_glStable (LL : Letters N) (j : ℕ) (la : Fin r → ℤ) (c d : Fin r) :
    ∀ x ∈ IsoC p LL j univ la, glAct p LL j c d x ∈ IsoC p LL j univ la := by
  intro x hx
  unfold IsoC at hx ⊢
  rw [Submodule.mem_sInf] at hx ⊢
  intro S hS
  exact hS.2 c (Finset.mem_univ _) d (Finset.mem_univ _) x (hx S hS)

/- English proof (translation)
The claim follows from `le_sInf fun _ hS => hS.1`.
-/
theorem hwc_le_isoC (LL : Letters N) (j : ℕ) (la : Fin r → ℤ) :
    HWC p LL j univ la ≤ IsoC p LL j univ la :=
  le_sInf fun _ hS => hS.1

/- English proof (translation)
Establish `: IsoC p LL j univ la ≤ IsoC p LL j univ la ⊓ (IsoC p LL j univ la).comap Q`. Use `sInf_le ⟨fun x hx => ⟨hwc_le_isoC LL j la hx, hwc_le_isoC LL j la (hh x hx)⟩, ?_⟩` and prove the remaining obligations. Introduce `c _ d _ x hx`. Use `⟨isoC_glStable LL j la c d x hx.1, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Q (glAct p LL j c d x) ∈ IsoC p LL j univ la`.

Rewrite using `[hc]`. Conclude with `isoC_glStable LL j la c d _ hx.2`. Conclude with `fun x hx => (this hx).2`.
-/
theorem isoC_keep (LL : Letters N) (j : ℕ) (la : Fin r → ℤ)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hc : ∀ c d x, Q (glAct p LL j c d x) = glAct p LL j c d (Q x))
    (hh : ∀ x ∈ HWC p LL j univ la, Q x ∈ HWC p LL j univ la) :
    ∀ x ∈ IsoC p LL j univ la, Q x ∈ IsoC p LL j univ la := by
  have : IsoC p LL j univ la ≤ IsoC p LL j univ la ⊓ (IsoC p LL j univ la).comap Q := by
    refine sInf_le ⟨fun x hx => ⟨hwc_le_isoC LL j la hx, hwc_le_isoC LL j la (hh x hx)⟩, ?_⟩
    intro c _ d _ x hx
    refine ⟨isoC_glStable LL j la c d x hx.1, ?_⟩
    change Q (glAct p LL j c d x) ∈ IsoC p LL j univ la
    rw [hc]
    exact isoC_glStable LL j la c d _ hx.2
  exact fun x hx => (this hx).2

/- English proof (translation)
Take `⟨hPP, hran, hker⟩` from `hP`. Establish `hsup : ∀ S : Set (Fin r → ℤ), ∀ x ∈ (⨆ (la : Fin r → ℤ) (_ : la ∈ S), IsoC p LL j univ la), Q x ∈ (⨆ (la : Fin r → ℤ) (_ : la ∈ S), IsoC p LL j univ la)`. Introduce `S`. Establish `: (⨆ (la : Fin r → ℤ) (_ : la ∈ S), IsoC p LL j univ la) ≤ (⨆ (la : Fin r → ℤ) (_ : la ∈ S), IsoC p LL j univ la).comap Q`. Use `iSup₂_le fun la hla => ?_` and prove the remaining obligations.

Introduce `x hx`. Conclude with `(le_iSup₂ (f := fun la (_ : la ∈ S) => IsoC p LL j univ la) la hla) (hQ la x hx)`. Conclude with `fun x hx => this hx`. Use `comm_of_stable P Q hPP ?_ ?_` and prove the remaining obligations. Rewrite using `[hran]`.

Conclude with `hsup T`. Rewrite using `[hker]`. Conclude with `hsup Tᶜ`.
-/
theorem typeProj_comm (LL : Letters N) (j : ℕ) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j univ T P)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hQ : ∀ la, ∀ x ∈ IsoC p LL j univ la, Q x ∈ IsoC p LL j univ la) : ∀ x, P (Q x) = Q (P x) := by
  obtain ⟨hPP, hran, hker⟩ := hP
  have hsup : ∀ S : Set (Fin r → ℤ), ∀ x ∈ (⨆ (la : Fin r → ℤ) (_ : la ∈ S), IsoC p LL j univ la),
      Q x ∈ (⨆ (la : Fin r → ℤ) (_ : la ∈ S), IsoC p LL j univ la) := by
    intro S
    have : (⨆ (la : Fin r → ℤ) (_ : la ∈ S), IsoC p LL j univ la) ≤
        (⨆ (la : Fin r → ℤ) (_ : la ∈ S), IsoC p LL j univ la).comap Q := by
      refine iSup₂_le fun la hla => ?_
      intro x hx
      exact (le_iSup₂ (f := fun la (_ : la ∈ S) => IsoC p LL j univ la) la hla) (hQ la x hx)
    exact fun x hx => this hx
  refine comm_of_stable P Q hPP ?_ ?_
  · rw [hran]; exact hsup T
  · rw [hker]; exact hsup Tᶜ

end Rep

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open Formalism.GM Formalism.GM.TM M MvPolynomial Finset

section Proj
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

/- English proof (translation)
Introduce `x hx`. Rewrite `hx`, the goal using `[mem_restrictSupport_iff]`. Introduce `m hm`. Apply `hx` to reduce the goal to its premises. Rewrite `hm`, the goal using `[Finset.mem_coe, mem_support_iff]`.

Rewrite `hm` using `[ProjS.coeff_eulL]`. Conclude with `left_ne_zero_of_mul hm`.
-/
theorem eul_keep_supp {σ : Type} {s : ℕ} (t : Fin s → σ) (Q : Set (σ →₀ ℕ)) :
    ∀ x ∈ restrictSupport ℚ_[p] Q, ProjS.eulL t x ∈ restrictSupport ℚ_[p] Q := by
  intro x hx
  rw [mem_restrictSupport_iff] at hx ⊢
  intro m hm
  apply hx
  rw [Finset.mem_coe, mem_support_iff] at hm ⊢
  rw [ProjS.coeff_eulL] at hm
  exact left_ne_zero_of_mul hm

/- English proof (translation)
Introduce `x hx`. Take `⟨hw, hk⟩` from `Submodule.mem_inf.mp hx`. Use `Submodule.mem_inf.mpr ⟨eul_keep_supp _ _ x hw, ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker] at hk ⊢`. Introduce `c d hcd`.

Rewrite using `[← eul_glAct, hk c d hcd, map_zero]`.
-/
theorem eul_hwc (LL : Letters N) (j : ℕ) (i0 : Fin N) (la : Fin r → ℤ) :
    ∀ x ∈ HWC p LL j univ la, ProjS.eulL (fun c : Fin r => (i0, c)) x ∈ HWC p LL j univ la := by
  intro x hx
  obtain ⟨hw, hk⟩ := Submodule.mem_inf.mp hx
  refine Submodule.mem_inf.mpr ⟨eul_keep_supp _ _ x hw, ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hk ⊢
  intro c d hcd
  rw [← eul_glAct, hk c d hcd, map_zero]

/- English proof (translation)
The claim follows from `typeProj_comm LL j T P hP _ (fun la => isoC_glStable LL j la c d)`.
-/
theorem typeProj_glAct (LL : Letters N) (j : ℕ) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j univ T P) (c d : Fin r) :
    ∀ x, P (glAct p LL j c d x) = glAct p LL j c d (P x) :=
  typeProj_comm LL j T P hP _ (fun la => isoC_glStable LL j la c d)

/- English proof (translation)
The claim follows from `typeProj_comm LL j T P hP _ (fun la => isoC_keep LL j la _ (fun c d x => eul_glAct LL j i0 c d x) (eul_hwc LL j i0 la))`.
-/
theorem typeProj_eul (LL : Letters N) (j : ℕ) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j univ T P) (i0 : Fin N) :
    ∀ x, P (ProjS.eulL (fun c : Fin r => (i0, c)) x) = ProjS.eulL (fun c : Fin r => (i0, c)) (P x) :=
  typeProj_comm LL j T P hP _ (fun la => isoC_keep LL j la _ (fun c d x => eul_glAct LL j i0 c d x)
    (eul_hwc LL j i0 la))

/- English proof (translation)
Introduce `x hx`. Rewrite `hx`, the goal using `[pol_iff_eul]`. Introduce `i`. Rewrite using `[← typeProj_eul LL j T P hP i, hx i, map_smul]`.
-/
theorem typeProj_pol (LL : Letters N) (j : ℕ) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j univ T P) : ∀ x ∈ Pol p r LL, P x ∈ Pol p r LL := by
  intro x hx
  rw [pol_iff_eul] at hx ⊢
  intro i
  rw [← typeProj_eul LL j T P hP i, hx i, map_smul]

/- English proof (translation)
Unfold `YCond`. Introduce `x hx`. Establish `: sSup {S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) | S ≤ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} ∧ GlStable p LL j S} ≤ (sSup {S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) | S ≤ restrictSupport ℚ_[p] {m : Fin …` using `sSup_le fun S hS x hx => le_sSup hS (hS.2 c d x hx)`. Conclude with `this hx`.
-/
theorem ycond_glStable [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ) (c d : Fin r) :
    ∀ x ∈ YCond p (r := r) LL j Mt, glAct p LL j c d x ∈ YCond p (r := r) LL j Mt := by
  unfold YCond
  intro x hx
  have : sSup {S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) |
      S ≤ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} ∧ GlStable p LL j S} ≤
      (sSup {S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) |
      S ≤ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} ∧ GlStable p LL j S}).comap
        (glAct p LL j c d) :=
    sSup_le fun S hS x hx => le_sSup hS (hS.2 c d x hx)
  exact this hx

/- English proof (translation)
The claim follows from `sSup_le fun _ hS => hS.1`.
-/
theorem ycond_le_supp [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ) :
    YCond p (r := r) LL j Mt ≤ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} :=
  sSup_le fun _ hS => hS.1

/- English proof (translation)
The claim follows from `ycond_keep LL j Mt P (typeProj_glAct LL j T P hP) (comm_preserves_weight_le LL j Mt P (typeProj_glAct LL j T P hP 0 0))`.
-/
theorem typeProj_ycond [NeZero r] (LL : Letters N) (j : ℕ) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j univ T P) (Mt : WithTop ℤ) :
    ∀ x ∈ YCond p (r := r) LL j Mt, P x ∈ YCond p (r := r) LL j Mt :=
  ycond_keep LL j Mt P (typeProj_glAct LL j T P hP) (comm_preserves_weight_le LL j Mt P (typeProj_glAct LL j T P hP 0 0))

/- English proof (translation)
Use `set Lo : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) := sInf {S | HWC p LL j univ la ≤ S ∧ ∀ c d : Fin r, d < c → ∀ x ∈ S, glAct p LL j c d x ∈ S} with hLo`. Establish `hHLo : HWC p LL j univ la ≤ Lo` using `le_sInf fun _ hS => hS.1`. Establish `hlow : ∀ c d : Fin r, d < c → ∀ x ∈ Lo, glAct p LL j c d x ∈ Lo`. Introduce `c d hdc x hx`. Rewrite `hx`, the goal using `[hLo, Submodule.mem_sInf]`.

Introduce `S hS`. Conclude with `hS.2 c d hdc x (hx S hS)`. Establish `hLoW : Lo ≤ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ ((la 0 : ℤ) : WithTop ℤ)}`. Use `sInf_le ⟨?_, fun c d hdc => lower_action_preserves_weight_le LL j c d hdc _⟩` and prove the remaining obligations. Introduce `x hx`.

Establish `hw` using `(Submodule.mem_inf.mp hx).1`. Rewrite `hw` using `[WtSpC, mem_restrictSupport_iff]`. Rewrite using `[mem_restrictSupport_iff]`. Introduce `m hm`. Use `hw hm 0 (Finset.mem_univ _)` as an intermediate fact.

Simplify using `only [Set.mem_ofPred_eq]`. Rewrite using `[this]`. Establish `hgl : ∀ c d : Fin r, ∀ x ∈ Lo, glAct p LL j c d x ∈ Lo` using `by set L' : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) := Lo ⊓ ⨅ (c : Fin r) (d : Fin r), Lo.comap (glAct p LL j c d) with hL'`. Establish `hmemL' : ∀ x, x ∈ L' ↔ x ∈ Lo ∧ ∀ c d, glAct p LL j c d x ∈ Lo`. Introduce `x`.

Simplify using `only [hL', Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]`. Establish `hle : Lo ≤ L'`. Use `sInf_le ⟨?_, ?_⟩` and prove the remaining obligations. Introduce `h hh`. Rewrite using `[hmemL']`.

Use `⟨hHLo hh, fun c d => ?_⟩` and prove the remaining obligations. Break down `lt_trichotomy c d with hcd | hcd | hcd` into its components or cases. Establish `hk` using `(Submodule.mem_inf.mp hh).2`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker] at hk`. Rewrite using `[hk c d ⟨Finset.mem_univ _, Finset.mem_univ _, hcd⟩]`.

Conclude with `Lo.zero_mem`. Substitute `hcd` using the available equality. Rewrite using `[cartan_eig LL j la h (Submodule.mem_inf.mp hh).1 c]`. Conclude with `Lo.smul_mem _ (hHLo hh)`. Conclude with `hlow c d hcd h (hHLo hh)`.

Introduce `a b hba x hx`. Rewrite `hx`, the goal using `[hmemL']`. Use `⟨hlow a b hba x hx.1, fun c d => ?_⟩` and prove the remaining obligations. Establish `hcomm` using `glAct_comm LL j c d a b x`. Establish `e : glAct p LL j c d (glAct p LL j a b x) = glAct p LL j a b (glAct p LL j c d x) + ((if d = a then glAct p LL j c b x else 0) - (if b = c then glAct p LL j a d x else 0))`.

Rewrite using `[← hcomm]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Use `Lo.add_mem (hlow a b hba _ (hx.2 c d)) (Lo.sub_mem ?_ ?_)` and prove the remaining obligations. Use `split_ifs`.

Conclude with `hx.2 c b`. Conclude with `Lo.zero_mem`. Use `split_ifs`. Conclude with `hx.2 a d`. Conclude with `Lo.zero_mem`.

Introduce `c d x hx`. Conclude with `((hmemL' x).mp (hle hx)).2 c d`. Establish `hIso : IsoC p LL j univ la ≤ Lo` using `sInf_le ⟨hHLo, fun c _ d _ x hx => hgl c d x hx⟩`. Use `le_sSup ⟨?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Establish `h1` using `hLoW (hIso hx)`. Rewrite `h1`, the goal using `[mem_restrictSupport_iff]`. Introduce `m hm`. Conclude with `le_trans (h1 hm) hla`. Introduce `c d x hx`.

Conclude with `isoC_glStable LL j la c d x hx`.
-/
theorem isoC_le_ycond [NeZero r] (LL : Letters N) (j : ℕ) (la : Fin r → ℤ) (Mt : WithTop ℤ)
    (hla : ((la 0 : ℤ) : WithTop ℤ) ≤ Mt) : IsoC p LL j univ la ≤ YCond p (r := r) LL j Mt := by
  set Lo : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
    sInf {S | HWC p LL j univ la ≤ S ∧ ∀ c d : Fin r, d < c → ∀ x ∈ S, glAct p LL j c d x ∈ S} with hLo
  have hHLo : HWC p LL j univ la ≤ Lo := le_sInf fun _ hS => hS.1
  have hlow : ∀ c d : Fin r, d < c → ∀ x ∈ Lo, glAct p LL j c d x ∈ Lo := by
    intro c d hdc x hx
    rw [hLo, Submodule.mem_sInf] at hx ⊢
    intro S hS
    exact hS.2 c d hdc x (hx S hS)
  have hLoW : Lo ≤ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ ((la 0 : ℤ) : WithTop ℤ)} := by
    refine sInf_le ⟨?_, fun c d hdc => lower_action_preserves_weight_le LL j c d hdc _⟩
    intro x hx
    have hw := (Submodule.mem_inf.mp hx).1
    rw [WtSpC, mem_restrictSupport_iff] at hw
    rw [mem_restrictSupport_iff]
    intro m hm
    have := hw hm 0 (Finset.mem_univ _)
    simp only [Set.mem_ofPred_eq]
    rw [this]
  have hgl : ∀ c d : Fin r, ∀ x ∈ Lo, glAct p LL j c d x ∈ Lo := by
    set L' : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
      Lo ⊓ ⨅ (c : Fin r) (d : Fin r), Lo.comap (glAct p LL j c d) with hL'
    have hmemL' : ∀ x, x ∈ L' ↔ x ∈ Lo ∧ ∀ c d, glAct p LL j c d x ∈ Lo := by
      intro x
      simp only [hL', Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
    have hle : Lo ≤ L' := by
      refine sInf_le ⟨?_, ?_⟩
      · intro h hh
        rw [hmemL']
        refine ⟨hHLo hh, fun c d => ?_⟩
        rcases lt_trichotomy c d with hcd | hcd | hcd
        · have hk := (Submodule.mem_inf.mp hh).2
          simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hk
          rw [hk c d ⟨Finset.mem_univ _, Finset.mem_univ _, hcd⟩]
          exact Lo.zero_mem
        · subst hcd
          rw [cartan_eig LL j la h (Submodule.mem_inf.mp hh).1 c]
          exact Lo.smul_mem _ (hHLo hh)
        · exact hlow c d hcd h (hHLo hh)
      · intro a b hba x hx
        rw [hmemL'] at hx ⊢
        refine ⟨hlow a b hba x hx.1, fun c d => ?_⟩
        have hcomm := glAct_comm LL j c d a b x
        have e : glAct p LL j c d (glAct p LL j a b x) = glAct p LL j a b (glAct p LL j c d x) +
            ((if d = a then glAct p LL j c b x else 0) - (if b = c then glAct p LL j a d x else 0)) := by
          rw [← hcomm]; abel
        rw [e]
        refine Lo.add_mem (hlow a b hba _ (hx.2 c d)) (Lo.sub_mem ?_ ?_)
        · split_ifs
          · exact hx.2 c b
          · exact Lo.zero_mem
        · split_ifs
          · exact hx.2 a d
          · exact Lo.zero_mem
    intro c d x hx
    exact ((hmemL' x).mp (hle hx)).2 c d
  have hIso : IsoC p LL j univ la ≤ Lo :=
    sInf_le ⟨hHLo, fun c _ d _ x hx => hgl c d x hx⟩
  refine le_sSup ⟨?_, ?_⟩
  · intro x hx
    have h1 := hLoW (hIso hx)
    rw [mem_restrictSupport_iff] at h1 ⊢
    intro m hm
    exact le_trans (h1 hm) hla
  · intro c d x hx
    exact isoC_glStable LL j la c d x hx

end Proj

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open Formalism.GM Formalism.GM.TM M MvPolynomial Finset

section Comp
variable {K σ : Type} [Field K]

open Classical in

noncomputable def compP (Pr : (σ →₀ ℕ) → Prop) (x : MvPolynomial σ K) : MvPolynomial σ K :=
  ∑ m ∈ x.support, if Pr m then monomial m (coeff m x) else 0

open Classical in
/- English proof (translation)
Unfold `compP`. Rewrite using `[coeff_sum, Finset.sum_eq_single m]`. Apply the tactic sequence `by_cases h : Pr m <;> simp [h, coeff_monomial]`. Introduce `b _ hbm`. Apply the tactic sequence `by_cases h : Pr b <;> simp [h, coeff_monomial, hbm]`.

Introduce `hm`. Rewrite `hm` using `[MvPolynomial.mem_support_iff, not_not]`. Apply the tactic sequence `by_cases h : Pr m <;> simp [h, hm]`.
-/
theorem coeff_compP (Pr : (σ →₀ ℕ) → Prop) (x : MvPolynomial σ K) (m : σ →₀ ℕ) :
    coeff m (compP Pr x) = if Pr m then coeff m x else 0 := by
  classical
  unfold compP
  rw [coeff_sum, Finset.sum_eq_single m]
  · by_cases h : Pr m <;> simp [h, coeff_monomial]
  · intro b _ hbm
    by_cases h : Pr b <;> simp [h, coeff_monomial, hbm]
  · intro hm
    rw [MvPolynomial.mem_support_iff, not_not] at hm
    by_cases h : Pr m <;> simp [h, hm]

/- English proof (translation)
Use extensionality with `m`. Simplify using `only [coeff_compP]`. Apply the tactic sequence `by_cases h1 : Pr m <;> by_cases h2 : Qr m <;> simp [h1, h2]`.
-/
theorem compP_and (Pr Qr : (σ →₀ ℕ) → Prop) (x : MvPolynomial σ K) :
    compP (fun m => Pr m ∧ Qr m) x = compP Pr (compP Qr x) := by
  ext m
  simp only [coeff_compP]
  by_cases h1 : Pr m <;> by_cases h2 : Qr m <;> simp [h1, h2]

/- English proof (translation)
Use extensionality with `m`. Simplify using `[coeff_compP]`.
-/
theorem compP_true (x : MvPolynomial σ K) : compP (fun _ => True) x = x := by
  ext m
  simp [coeff_compP]

/- English proof (translation)
Take `rfl : Pr = Qr` from `funext fun m => propext (h m)`. Both sides reduce to the same expression.
-/
theorem compP_congr (Pr Qr : (σ →₀ ℕ) → Prop) (h : ∀ m, Pr m ↔ Qr m) (x : MvPolynomial σ K) :
    compP Pr x = compP Qr x := by
  obtain rfl : Pr = Qr := funext fun m => propext (h m)
  rfl

/- English proof (translation)
Introduce `x hx k`. It suffices to establish `key : ∀ t : Finset ℤ, ∀ x ∈ S, (∀ m ∈ x.support, f m ∈ t) → ∀ k : ℤ, compP (fun m => f m = k) x ∈ S from key (x.support.image f) x hx (fun m hm => Finset.mem_image_of_mem f hm) k`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`.

Introduce `x _ hsupp k`. Establish `hx0 : x = 0`. Use extensionality with `m`. Assume the negation of the conclusion as `hne`. Use `hsupp m (MvPolynomial.mem_support_iff.mpr hne)` as an intermediate fact.

Simplify using `at this`. Establish `h0 : compP (fun m => f m = k) x = 0`. Use extensionality with `m`. Rewrite using `[coeff_compP, hx0]`. Simplify using the standard rewrite rules.

Rewrite using `[h0]`. Conclude with `S.zero_mem`. Consider the case `@insert a t ha ih`. Introduce `x hx hsupp`. Establish `hyS : H x - ((a : ℤ) : K) • x ∈ S` using `S.sub_mem (hS x hx) (S.smul_mem _ hx)`.

Establish `hy : ∀ m, coeff m (H x - ((a : ℤ) : K) • x) = (((f m : ℤ) : K) - ((a : ℤ) : K)) * coeff m x`. Introduce `m`. Rewrite using `[coeff_sub, coeff_smul, smul_eq_mul, hH]`. Expand and normalize the polynomial expressions, which then agree. Establish `hysupp : ∀ m ∈ (H x - ((a : ℤ) : K) • x).support, f m ∈ t`.

Introduce `m hm`. Rewrite `hm` using `[MvPolynomial.mem_support_iff, hy]`. Establish `hxm : coeff m x ≠ 0` using `right_ne_zero_of_mul hm`. Establish `hfa : f m ≠ a`. Introduce `h`.

Apply `hm` to reduce the goal to its premises. Rewrite using `[h, sub_self, zero_mul]`. Use `hsupp m (MvPolynomial.mem_support_iff.mpr hxm)` as an intermediate fact. Rewrite `this` using `[Finset.mem_insert]`. Conclude with `this.resolve_left hfa`.

Establish `hne : ∀ k : ℤ, k ≠ a → compP (fun m => f m = k) x ∈ S`. Introduce `k hk`. Establish `hka : ((k : ℤ) : K) - ((a : ℤ) : K) ≠ 0`. Rewrite using `[sub_ne_zero]`. Conclude with `hk` after adjusting the coercions.

Establish `hrel : compP (fun m => f m = k) x = (((k : ℤ) : K) - ((a : ℤ) : K))⁻¹ • compP (fun m => f m = k) (H x - ((a : ℤ) : K) • x)`. Use extensionality with `m`. Simplify using `only [coeff_smul, smul_eq_mul, coeff_compP, hy]`. Distinguish the cases in `h : f m = k`. Rewrite using `[if_pos h, if_pos h, h, inv_mul_cancel_left₀ hka]`.

Rewrite using `[if_neg h, if_neg h, mul_zero]`. Rewrite using `[hrel]`. Conclude with `S.smul_mem _ (ih _ hyS hysupp k)`. Introduce `k`. Distinguish the cases in `hk : k = a`.

Rewrite using `[hk]`. Establish `hdec : compP (fun m => f m = a) x = x - ∑ k' ∈ t, compP (fun m => f m = k') x`. Use extensionality with `m`. Simplify using `only [coeff_sub, coeff_sum, coeff_compP]`. Distinguish the cases in `hc : coeff m x = 0`.

Simplify using `[hc]`. Establish `hm` using `hsupp m (MvPolynomial.mem_support_iff.mpr hc)`. Rewrite `hm` using `[Finset.mem_insert]`. Distinguish the cases in `hfk : f m = a`. Rewrite using `[if_pos hfk, Finset.sum_eq_zero, sub_zero]`.

Introduce `k' hk'`. Conclude with `if_neg (fun h => ha (by rw [← hfk, h]; exact hk'))`. Rewrite using `[if_neg hfk, Finset.sum_eq_single (f m), if_pos rfl, sub_self]`. Introduce `b _ hb`. Rewrite using `[if_neg (Ne.symm hb)]`.

Introduce `hn`. Conclude with `absurd (hm.resolve_left hfk) hn`. Rewrite using `[hdec]`. Use `S.sub_mem hx (S.sum_mem fun k' hk' => hne k' ?_)` and prove the remaining obligations. Introduce and unpack `rfl`.

Conclude with `ha hk'`. Conclude with `hne k hk`.
-/
theorem vdm (H : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) (f : (σ →₀ ℕ) → ℤ) [CharZero K]
    (hH : ∀ x m, coeff m (H x) = ((f m : ℤ) : K) * coeff m x) (S : Submodule K (MvPolynomial σ K))
    (hS : ∀ x ∈ S, H x ∈ S) : ∀ x ∈ S, ∀ k : ℤ, compP (fun m => f m = k) x ∈ S := by
  intro x hx k
  suffices key : ∀ t : Finset ℤ, ∀ x ∈ S, (∀ m ∈ x.support, f m ∈ t) →
      ∀ k : ℤ, compP (fun m => f m = k) x ∈ S from
    key (x.support.image f) x hx (fun m hm => Finset.mem_image_of_mem f hm) k
  intro t
  induction t using Finset.induction_on with
  | empty =>
    intro x _ hsupp k
    have hx0 : x = 0 := by
      ext m
      by_contra hne
      have := hsupp m (MvPolynomial.mem_support_iff.mpr hne)
      simp at this
    have h0 : compP (fun m => f m = k) x = 0 := by
      ext m
      rw [coeff_compP, hx0]
      simp
    rw [h0]
    exact S.zero_mem
  | @insert a t ha ih =>
    intro x hx hsupp
    have hyS : H x - ((a : ℤ) : K) • x ∈ S := S.sub_mem (hS x hx) (S.smul_mem _ hx)
    have hy : ∀ m, coeff m (H x - ((a : ℤ) : K) • x) = (((f m : ℤ) : K) - ((a : ℤ) : K)) * coeff m x := by
      intro m
      rw [coeff_sub, coeff_smul, smul_eq_mul, hH]
      ring
    have hysupp : ∀ m ∈ (H x - ((a : ℤ) : K) • x).support, f m ∈ t := by
      intro m hm
      rw [MvPolynomial.mem_support_iff, hy] at hm
      have hxm : coeff m x ≠ 0 := right_ne_zero_of_mul hm
      have hfa : f m ≠ a := by
        intro h
        apply hm
        rw [h, sub_self, zero_mul]
      have := hsupp m (MvPolynomial.mem_support_iff.mpr hxm)
      rw [Finset.mem_insert] at this
      exact this.resolve_left hfa
    have hne : ∀ k : ℤ, k ≠ a → compP (fun m => f m = k) x ∈ S := by
      intro k hk
      have hka : ((k : ℤ) : K) - ((a : ℤ) : K) ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast hk
      have hrel : compP (fun m => f m = k) x =
          (((k : ℤ) : K) - ((a : ℤ) : K))⁻¹ • compP (fun m => f m = k) (H x - ((a : ℤ) : K) • x) := by
        ext m
        simp only [coeff_smul, smul_eq_mul, coeff_compP, hy]
        by_cases h : f m = k
        · rw [if_pos h, if_pos h, h, inv_mul_cancel_left₀ hka]
        · rw [if_neg h, if_neg h, mul_zero]
      rw [hrel]
      exact S.smul_mem _ (ih _ hyS hysupp k)
    intro k
    by_cases hk : k = a
    · rw [hk]
      have hdec : compP (fun m => f m = a) x = x - ∑ k' ∈ t, compP (fun m => f m = k') x := by
        ext m
        simp only [coeff_sub, coeff_sum, coeff_compP]
        by_cases hc : coeff m x = 0
        · simp [hc]
        · have hm := hsupp m (MvPolynomial.mem_support_iff.mpr hc)
          rw [Finset.mem_insert] at hm
          by_cases hfk : f m = a
          · rw [if_pos hfk, Finset.sum_eq_zero, sub_zero]
            intro k' hk'
            exact if_neg (fun h => ha (by rw [← hfk, h]; exact hk'))
          · rw [if_neg hfk, Finset.sum_eq_single (f m), if_pos rfl, sub_self]
            · intro b _ hb
              rw [if_neg (Ne.symm hb)]
            · intro hn
              exact absurd (hm.resolve_left hfk) hn
      rw [hdec]
      refine S.sub_mem hx (S.sum_mem fun k' hk' => hne k' ?_)
      rintro rfl
      exact ha hk'
    · exact hne k hk

end Comp

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open Formalism.GM Formalism.GM.TM M MvPolynomial Finset

section HW
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

/- English proof (translation)
Establish `key : ∀ s : Finset (Fin r), ∀ x ∈ S, compP (fun m => ∀ c ∈ s, wt LL j c m = μ c) x ∈ S`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `x hx`.

Rewrite using `[compP_congr (fun m => ∀ c ∈ (∅ : Finset (Fin r)), wt LL j c m = μ c) (fun _ => True) (fun m => by simp), compP_true]`. Conclude with `hx`. Consider the case `@insert a s ha ih`. Introduce `x hx`. Rewrite using `[compP_congr (fun m => ∀ c ∈ insert a s, wt LL j c m = μ c) (fun m => wt LL j a m = μ a ∧ ∀ c ∈ s, wt LL j c m = μ c) (fun m => by simp), compP_and]`.

Conclude with `vdm (glAct p LL j a a) (wt LL j a) (fun y m => coeff_cartan LL j a y m) S (hS a) _ (ih x hx) (μ a)`. Introduce `x hx`. Rewrite using `[compP_congr (fun m => ∀ c, wt LL j c m = μ c) (fun m => ∀ c ∈ (Finset.univ : Finset (Fin r)), wt LL j c m = μ c) (fun m => by simp)]`. Conclude with `key Finset.univ x hx`.
-/
theorem wcomp_mem (LL : Letters N) (j : ℕ) (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hS : ∀ c, ∀ x ∈ S, glAct p LL j c c x ∈ S) (μ : Fin r → ℤ) :
    ∀ x ∈ S, compP (fun m => ∀ c, wt LL j c m = μ c) x ∈ S := by
  have key : ∀ s : Finset (Fin r), ∀ x ∈ S, compP (fun m => ∀ c ∈ s, wt LL j c m = μ c) x ∈ S := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro x hx
      rw [compP_congr (fun m => ∀ c ∈ (∅ : Finset (Fin r)), wt LL j c m = μ c) (fun _ => True)
        (fun m => by simp), compP_true]
      exact hx
    | @insert a s ha ih =>
      intro x hx
      rw [compP_congr (fun m => ∀ c ∈ insert a s, wt LL j c m = μ c)
        (fun m => wt LL j a m = μ a ∧ ∀ c ∈ s, wt LL j c m = μ c) (fun m => by simp), compP_and]
      exact vdm (glAct p LL j a a) (wt LL j a) (fun y m => coeff_cartan LL j a y m) S (hS a) _ (ih x hx) (μ a)
  intro x hx
  rw [compP_congr (fun m => ∀ c, wt LL j c m = μ c) (fun m => ∀ c ∈ (Finset.univ : Finset (Fin r)), wt LL j c m = μ c)
    (fun m => by simp)]
  exact key Finset.univ x hx

/- English proof (translation)
Set `bnd : Fin N × Fin r →₀ ℕ` to `Finsupp.equivFunOnFinite.symm (fun _ => LL.total)`. Use `(Set.finite_Iic bnd).subset ?_` and prove the remaining obligations. Introduce `m hm`. Rewrite using `[Set.mem_Iic, Finsupp.le_def]`. Introduce `a`.

Establish `h1 : m a ≤ ∑ c, m (a.1, c)` using `Finset.single_le_sum (f := fun c => m (a.1, c)) (fun _ _ => Nat.zero_le _) (mem_univ a.2)`. Establish `h2 : LL.deg a.1 ≤ LL.total` using `Finset.single_le_sum (f := fun i => LL.deg i) (fun _ _ => Nat.zero_le _) (mem_univ a.1)`. Establish `h3 : bnd a = LL.total` using `by simp [bnd]`. Rewrite using `[h3]`. Rewrite `h1` using `[hm a.1]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem multiDeg_finite (LL : Letters N) : ({m | MultiDeg (r := r) LL m} : Set (Fin N × Fin r →₀ ℕ)).Finite := by
  classical
  let bnd : Fin N × Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => LL.total)
  refine (Set.finite_Iic bnd).subset ?_
  intro m hm
  rw [Set.mem_Iic, Finsupp.le_def]
  intro a
  have h1 : m a ≤ ∑ c, m (a.1, c) :=
    Finset.single_le_sum (f := fun c => m (a.1, c)) (fun _ _ => Nat.zero_le _) (mem_univ a.2)
  have h2 : LL.deg a.1 ≤ LL.total :=
    Finset.single_le_sum (f := fun i => LL.deg i) (fun _ _ => Nat.zero_le _) (mem_univ a.1)
  have h3 : bnd a = LL.total := by simp [bnd]
  rw [h3]
  rw [hm a.1] at h1
  omega

/- English proof (translation)
Set `wv : (Fin N × Fin r →₀ ℕ) → (Fin r → ℤ)` to `fun m c => wt LL j c m`. Set `Wt : Set (Fin r → ℤ)` to `{μ | ∃ y ∈ S, y ≠ 0 ∧ y ∈ WtSpC p LL j univ μ}`. Establish `hWfin : Wt.Finite`. Use `((multiDeg_finite (r := r) LL).image wv).subset ?_` and prove the remaining obligations. Introduce and unpack `μ ⟨y, hyS, hy0, hyW⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m, m ∈ y.support := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hy0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))`. Establish `hP` using `hSP hyS`.

Rewrite `hP` using `[Pol, mem_restrictSupport_iff]`. Rewrite `hyW` using `[WtSpC, mem_restrictSupport_iff]`. Use `⟨m, hP (Finset.mem_coe.mpr hm), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `c`. Conclude with `hyW (Finset.mem_coe.mpr hm) c (Finset.mem_univ c)`.

Choose the witnesses or unpack the hypotheses as in `⟨m0, hm0⟩ : ∃ m, m ∈ x.support := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hx0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))`. Establish `hne : (hWfin.toFinset).Nonempty`.

Use `⟨wv m0, hWfin.mem_toFinset.mpr ⟨_, wcomp_mem LL j S (fun c => hS c c) (wv m0) x hx, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `h0`. Use `congrArg (coeff m0) h0` as an intermediate fact. Rewrite `this` using `[coeff_compP, if_pos (fun c => rfl), coeff_zero]`. Conclude with `(mem_support_iff.mp hm0) this`.

Rewrite using `[WtSpC, mem_restrictSupport_iff]`. Introduce `m hm c _`. Rewrite `hm` using `[Finset.mem_coe, mem_support_iff, coeff_compP]`. Use `split_ifs at hm with h`. Conclude with `h c`.

Conclude with `absurd rfl hm`. Take `⟨μ, hμ, hmax⟩` from `Finset.exists_max_image hWfin.toFinset (fun μ : Fin r → ℤ => -∑ c : Fin r, ((c : ℕ) : ℤ) * μ c) hne`. Take `⟨y, hyS, hy0, hyW⟩` from `hWfin.mem_toFinset.mp hμ`. Use `⟨y, hyS, hy0, μ, Submodule.mem_inf.mpr ⟨hyW, ?_⟩⟩` and prove the remaining obligations. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker]`.

Introduce and unpack `c d ⟨_, _, hcd⟩`. Assume the negation of the conclusion as `hz`. Establish `hmem : shiftW μ c d ∈ hWfin.toFinset` using `hWfin.mem_toFinset.mpr ⟨_, hS c d y hyS, hz, glAct_wtsp LL j c d μ y hyW⟩`. Establish `h1` using `hmax _ hmem`. Establish `h2 : (-∑ c' : Fin r, ((c' : ℕ) : ℤ) * shiftW μ c d c') = (-∑ c' : Fin r, ((c' : ℕ) : ℤ) * μ c') + (((d : ℕ) : ℤ) - ((c : ℕ) : ℤ))`.

Simplify using `only [shiftW, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : ((c : ℕ) : ℤ) < ((d : ℕ) : ℤ)` using `by exact_mod_cast hcd`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_hw (LL : Letters N) (j : ℕ) (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hSP : S ≤ Pol p r LL) (hS : ∀ c d, ∀ x ∈ S, glAct p LL j c d x ∈ S) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : x ∈ S) (hx0 : x ≠ 0) : ∃ h ∈ S, h ≠ 0 ∧ ∃ μ, h ∈ HWC p LL j univ μ := by
  classical
  let wv : (Fin N × Fin r →₀ ℕ) → (Fin r → ℤ) := fun m c => wt LL j c m
  let Wt : Set (Fin r → ℤ) := {μ | ∃ y ∈ S, y ≠ 0 ∧ y ∈ WtSpC p LL j univ μ}
  have hWfin : Wt.Finite := by
    refine ((multiDeg_finite (r := r) LL).image wv).subset ?_
    rintro μ ⟨y, hyS, hy0, hyW⟩
    obtain ⟨m, hm⟩ : ∃ m, m ∈ y.support := by
      by_contra hc; push Not at hc
      exact hy0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
    have hP := hSP hyS
    rw [Pol, mem_restrictSupport_iff] at hP
    rw [WtSpC, mem_restrictSupport_iff] at hyW
    refine ⟨m, hP (Finset.mem_coe.mpr hm), ?_⟩
    funext c
    exact hyW (Finset.mem_coe.mpr hm) c (Finset.mem_univ c)
  obtain ⟨m0, hm0⟩ : ∃ m, m ∈ x.support := by
    by_contra hc; push Not at hc
    exact hx0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
  have hne : (hWfin.toFinset).Nonempty := by
    refine ⟨wv m0, hWfin.mem_toFinset.mpr ⟨_, wcomp_mem LL j S (fun c => hS c c) (wv m0) x hx, ?_, ?_⟩⟩
    · intro h0
      have := congrArg (coeff m0) h0
      rw [coeff_compP, if_pos (fun c => rfl), coeff_zero] at this
      exact (mem_support_iff.mp hm0) this
    · rw [WtSpC, mem_restrictSupport_iff]
      intro m hm c _
      rw [Finset.mem_coe, mem_support_iff, coeff_compP] at hm
      split_ifs at hm with h
      · exact h c
      · exact absurd rfl hm
  obtain ⟨μ, hμ, hmax⟩ := Finset.exists_max_image hWfin.toFinset (fun μ : Fin r → ℤ => -∑ c : Fin r, ((c : ℕ) : ℤ) * μ c) hne
  obtain ⟨y, hyS, hy0, hyW⟩ := hWfin.mem_toFinset.mp hμ
  refine ⟨y, hyS, hy0, μ, Submodule.mem_inf.mpr ⟨hyW, ?_⟩⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  rintro c d ⟨_, _, hcd⟩
  by_contra hz
  have hmem : shiftW μ c d ∈ hWfin.toFinset :=
    hWfin.mem_toFinset.mpr ⟨_, hS c d y hyS, hz, glAct_wtsp LL j c d μ y hyW⟩
  have h1 := hmax _ hmem
  have h2 : (-∑ c' : Fin r, ((c' : ℕ) : ℤ) * shiftW μ c d c') = (-∑ c' : Fin r, ((c' : ℕ) : ℤ) * μ c') + (((d : ℕ) : ℤ) - ((c : ℕ) : ℤ)) := by
    simp only [shiftW, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  have h3 : ((c : ℕ) : ℤ) < ((d : ℕ) : ℤ) := by exact_mod_cast hcd
  linarith

/- English proof (translation)
Establish `hPP : ∀ x, P (P x) = P x` using `fun x => LinearMap.congr_fun hP.1 x`. Use `set S0 := S ⊓ LinearMap.ker P with hS0`. Establish `hS0 : ∀ y ∈ S0, y = 0`. Introduce `y hy`. Assume the negation of the conclusion as `hy0`.

Take `⟨h, hh, hh0, μ, hμ⟩` from `exists_hw LL j S0 (inf_le_left.trans hSP) (fun c d z hz => by`. Take `⟨hz1, hz2⟩` from `Submodule.mem_inf.mp hz`. Use `Submodule.mem_inf.mpr ⟨hS c d z hz1, ?_⟩` and prove the remaining obligations. Rewrite `hz2`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[typeProj_glAct LL j T P hP c d z, hz2, map_zero]) y hy hy0`.

Establish `hT'` using `hT h (Submodule.mem_inf.mp hh).1 hh0 μ hμ`. Establish `hran : h ∈ LinearMap.range P`. Rewrite using `[hP.2.1]`. Conclude with `(le_iSup₂ (f := fun la (_ : la ∈ T) => IsoC p LL j univ la) μ hT') (hwc_le_isoC LL j μ hμ)`. Take `⟨z, hz⟩` from `hran`.

Establish `: P h = h` using `by rw [← hz, hPP]`. Establish `h0 : P h = 0` using `LinearMap.mem_ker.mp (Submodule.mem_inf.mp hh).2`. Conclude with `hh0 (this.symm.trans h0)`. Introduce `x hx`. Use `hS0 (x - P x) (Submodule.mem_inf.mpr ⟨S.sub_mem hx (hPS x hx), by` as an intermediate fact.

Rewrite using `[LinearMap.mem_ker, map_sub, hPP, sub_self]⟩)`. Conclude with `(sub_eq_zero.mp this).symm`.
-/
theorem proj_fix (LL : Letters N) (j : ℕ) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j univ T P) (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hSP : S ≤ Pol p r LL) (hS : ∀ c d, ∀ x ∈ S, glAct p LL j c d x ∈ S) (hPS : ∀ x ∈ S, P x ∈ S)
    (hT : ∀ h ∈ S, h ≠ 0 → ∀ μ, h ∈ HWC p LL j univ μ → μ ∈ T) : ∀ x ∈ S, P x = x := by
  have hPP : ∀ x, P (P x) = P x := fun x => LinearMap.congr_fun hP.1 x
  set S0 := S ⊓ LinearMap.ker P with hS0
  have hS0 : ∀ y ∈ S0, y = 0 := by
    intro y hy
    by_contra hy0
    obtain ⟨h, hh, hh0, μ, hμ⟩ := exists_hw LL j S0 (inf_le_left.trans hSP) (fun c d z hz => by
      obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.mp hz
      refine Submodule.mem_inf.mpr ⟨hS c d z hz1, ?_⟩
      rw [LinearMap.mem_ker] at hz2 ⊢
      rw [typeProj_glAct LL j T P hP c d z, hz2, map_zero]) y hy hy0
    have hT' := hT h (Submodule.mem_inf.mp hh).1 hh0 μ hμ
    have hran : h ∈ LinearMap.range P := by
      rw [hP.2.1]
      exact (le_iSup₂ (f := fun la (_ : la ∈ T) => IsoC p LL j univ la) μ hT') (hwc_le_isoC LL j μ hμ)
    obtain ⟨z, hz⟩ := hran
    have : P h = h := by rw [← hz, hPP]
    have h0 : P h = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hh).2
    exact hh0 (this.symm.trans h0)
  intro x hx
  have := hS0 (x - P x) (Submodule.mem_inf.mpr ⟨S.sub_mem hx (hPS x hx), by
    rw [LinearMap.mem_ker, map_sub, hPP, sub_self]⟩)
  exact (sub_eq_zero.mp this).symm

end HW

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open Formalism.GM Formalism.GM.TM M MvPolynomial Finset

section E1
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

/- English proof (translation)
Unfold `glAct`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : (i : ℕ) < j`. Rewrite using `[if_pos h, if_pos (lt_min h i.isLt)]`. Rewrite using `[if_neg h, if_neg (fun h' => h (lt_of_lt_of_le h' (min_le_left _ _)))]`.
-/
theorem glAct_min (LL : Letters N) (j : ℕ) (c d : Fin r) : glAct p LL j c d = glAct p LL (min j N) c d := by
  unfold glAct
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) < j
  · rw [if_pos h, if_pos (lt_min h i.isLt)]
  · rw [if_neg h, if_neg (fun h' => h (lt_of_lt_of_le h' (min_le_left _ _)))]

/- English proof (translation)
Use function extensionality and compare the values at `m`. Unfold `wt`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : (i : ℕ) < j`. Rewrite using `[if_pos h, if_pos (lt_min h i.isLt)]`.

Rewrite using `[if_neg h, if_neg (fun h' => h (lt_of_lt_of_le h' (min_le_left _ _)))]`.
-/
theorem wt_min (LL : Letters N) (j : ℕ) (c : Fin r) : wt LL j c = wt LL (min j N) c := by
  funext m
  unfold wt
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) < j
  · rw [if_pos h, if_pos (lt_min h i.isLt)]
  · rw [if_neg h, if_neg (fun h' => h (lt_of_lt_of_le h' (min_le_left _ _)))]

/- English proof (translation)
Unfold `YCond GlStable`. Establish `h1 : glAct p (r` using `r) LL j = glAct p LL (min j N) := funext fun c => funext fun d => glAct_min LL j c d`. Rewrite using `[h1, wt_min LL j 0]`.
-/
theorem ycond_min [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ) :
    YCond p (r := r) LL j Mt = YCond p (r := r) LL (min j N) Mt := by
  unfold YCond GlStable
  have h1 : glAct p (r := r) LL j = glAct p LL (min j N) := funext fun c => funext fun d => glAct_min LL j c d
  rw [h1, wt_min LL j 0]

/- English proof (translation)
Take `⟨P, rfl⟩` from `LinearMap.mem_range.mp hx`. Simplify using `only [AlgHom.toLinearMap_apply, mapAlgHom_apply, coeff_map]`. Conclude with `PadicInt.norm_le_one _`.
-/
theorem intPol_norm {σ : Type} (x : MvPolynomial σ ℚ_[p]) (hx : x ∈ IntPol p σ) (m : σ →₀ ℕ) :
    ‖coeff m x‖ ≤ 1 := by
  obtain ⟨P, rfl⟩ := LinearMap.mem_range.mp hx
  simp only [AlgHom.toLinearMap_apply, mapAlgHom_apply, coeff_map]
  exact PadicInt.norm_le_one _

/- English proof (translation)
Establish `hzI : z ∈ IntPol p (Fin N × Fin r)` using `(Submodule.mem_inf.mp (Submodule.mem_inf.mp hz).2).2`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `hlt : ∀ m, ‖coeff m z‖ < 1` using `fun m => lt_of_le_of_ne (intPol_norm z hzI m) (hc m)`. Establish `hp0 : (p : ℚ_[p]) ≠ 0` using `by exact_mod_cast (Fact.out : p.Prime).ne_zero`.

Use `set x := (p : ℚ_[p])⁻¹ • z with hx`. Establish `hxI : x ∈ IntPol p (Fin N × Fin r)`. Use `mem_intPol_of_norm _ fun m => ?_` and prove the remaining obligations. Rewrite using `[hx, coeff_smul, smul_eq_mul, norm_mul, norm_inv, Padic.norm_p, inv_inv]`. Establish `h1` using `(Padic.norm_le_pow_iff_norm_lt_pow_add_one (coeff m z) (-1)).mpr (by simpa using hlt m)`.

Establish `hp : (0 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).pos`. Rewrite `h1` using `[zpow_neg_one]`. Combine the equalities or inequalities in the displayed calculation. Establish `hxY : x ∈ YZ p (r` using `r) LL J M := by`. Establish `hzY` using `(Submodule.mem_inf.mp hz).1`.

Establish `hzP` using `(Submodule.mem_inf.mp (Submodule.mem_inf.mp hz).2).1`. Use `Submodule.mem_inf.mpr ⟨?_, Submodule.mem_inf.mpr ⟨?_, hxI⟩⟩` and prove the remaining obligations. Conclude with `(Y p LL J M).smul_mem _ hzY`. Conclude with `(Pol p r LL).smul_mem _ hzP`. Establish `hzx : z = (p : ℤ_[p]) • x`.

Rewrite using `[hx, ← algebraMap_smul ℚ_[p] (p : ℤ_[p]), smul_smul]`. Simplify using `[hp0]`. Establish `hu` using `hprim _ x hxY hzx`. Rewrite `hu` using `[PadicInt.isUnit_iff, PadicInt.norm_p]`. Establish `: (1 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`.

Use `inv_lt_one_of_one_lt₀ this` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem prim_unit_coeff [NeZero r] (LL : Letters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (z : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hz : z ∈ YZ p (r := r) LL J M)
    (hprim : ∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), x ∈ YZ p (r := r) LL J M → z = c • x → IsUnit c) :
    ∃ m, ‖coeff m z‖ = 1 := by
  have hzI : z ∈ IntPol p (Fin N × Fin r) := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hz).2).2
  by_contra hc
  push Not at hc
  have hlt : ∀ m, ‖coeff m z‖ < 1 := fun m => lt_of_le_of_ne (intPol_norm z hzI m) (hc m)
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  set x := (p : ℚ_[p])⁻¹ • z with hx
  have hxI : x ∈ IntPol p (Fin N × Fin r) := by
    refine mem_intPol_of_norm _ fun m => ?_
    rw [hx, coeff_smul, smul_eq_mul, norm_mul, norm_inv, Padic.norm_p, inv_inv]
    have h1 := (Padic.norm_le_pow_iff_norm_lt_pow_add_one (coeff m z) (-1)).mpr (by simpa using hlt m)
    have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    rw [zpow_neg_one] at h1
    calc (p : ℝ) * ‖coeff m z‖ ≤ p * (p : ℝ)⁻¹ := mul_le_mul_of_nonneg_left h1 hp.le
      _ = 1 := mul_inv_cancel₀ hp.ne'
  have hxY : x ∈ YZ p (r := r) LL J M := by
    have hzY := (Submodule.mem_inf.mp hz).1
    have hzP := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hz).2).1
    refine Submodule.mem_inf.mpr ⟨?_, Submodule.mem_inf.mpr ⟨?_, hxI⟩⟩
    · exact (Y p LL J M).smul_mem _ hzY
    · exact (Pol p r LL).smul_mem _ hzP
  have hzx : z = (p : ℤ_[p]) • x := by
    rw [hx, ← algebraMap_smul ℚ_[p] (p : ℤ_[p]), smul_smul]
    simp [hp0]
  have hu := hprim _ x hxY hzx
  rw [PadicInt.isUnit_iff, PadicInt.norm_p] at hu
  have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have := inv_lt_one_of_one_lt₀ this
  linarith

end E1

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open Formalism.GM Formalism.GM.TM M MvPolynomial Finset

section E2
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

/- English proof (translation)
Unfold `fock`. Rewrite using `[Finset.sum_eq_single m0]`. Rewrite using `[coeff_monomial, if_pos rfl, mul_one]`. Introduce `b _ hb`. Rewrite using `[coeff_monomial, if_neg (Ne.symm hb)]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `h`. Conclude with `absurd hm0 h`.
-/
theorem fock_monomial {σ : Type} (z : MvPolynomial σ ℚ_[p]) (m0 : σ →₀ ℕ) (hm0 : m0 ∈ z.support) :
    fock p z (monomial m0 1) = coeff m0 z * (m0.prod fun _ k => (k.factorial : ℚ_[p])) := by
  classical
  unfold fock
  rw [Finset.sum_eq_single m0]
  · rw [coeff_monomial, if_pos rfl, mul_one]
  · intro b _ hb; rw [coeff_monomial, if_neg (Ne.symm hb)]; ring
  · intro h; exact absurd hm0 h

/- English proof (translation)
Establish `hne : coeff m0 z ≠ 0` using `by intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc`. Establish `hmem : m0 ∈ z.support` using `mem_support_iff.mpr hne`. Unfold `fockN`. Rewrite using `[fock_monomial z m0 hmem]`. Establish `hF : (m0.prod fun _ k => (k.factorial : ℚ_[p])) = ∏ v : Fin N × Fin r, ((m0 v).factorial : ℚ_[p])` using `Finsupp.prod_fintype _ _ (fun _ => by simp)`.

Establish `hdiv : ∀ i : Fin N, ∃ D : ℕ, (LL.deg i).factorial = (∏ c : Fin r, (m0 (i, c)).factorial) * D`. Introduce `i`. Rewrite using `[← hm0 i]`. Conclude with `Nat.prod_factorial_dvd_factorial_sum _ _`. Use `choose D hD using hdiv`.

Establish `hprod : (∏ i, ((LL.deg i).factorial : ℚ_[p])) = (∏ v : Fin N × Fin r, ((m0 v).factorial : ℚ_[p])) * ((∏ i, D i : ℕ) : ℚ_[p])`. Rewrite using `[Fintype.prod_prod_type, Nat.cast_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hD i]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[hF, hprod]`. Establish `hF0 : (∏ v : Fin N × Fin r, ((m0 v).factorial : ℚ_[p])) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun v _ => by exact_mod_cast (Nat.factorial_pos _).ne'`. Establish `hD0 : ((∏ i, D i : ℕ) : ℚ_[p]) ≠ 0`. Establish `: (∏ i, D i) ≠ 0`.

Introduce `h0`. Take `⟨i, _, hi⟩` from `Finset.prod_eq_zero_iff.mp h0`. Use `hD i` as an intermediate fact. Rewrite `this` using `[hi, mul_zero]`. Conclude with `(Nat.factorial_pos _).ne' this`.

Conclude with `this` after adjusting the coercions. Rewrite using `[mul_comm (∏ v : Fin N × Fin r, ((m0 v).factorial : ℚ_[p])) _, mul_div_mul_comm, div_self hF0, mul_one, norm_div, hc]`. Establish `hle : ‖((∏ i, D i : ℕ) : ℚ_[p])‖ ≤ 1`. Use `Padic.norm_int_le_one (p := p) ((∏ i, D i : ℕ) : ℤ)` as an intermediate fact. Simplify using `using this`.

Establish `hpos : 0 < ‖((∏ i, D i : ℕ) : ℚ_[p])‖` using `norm_pos_iff.mpr hD0`. Rewrite using `[le_div_iff₀ hpos, one_mul]`. Conclude with `hle`.
-/
theorem fockN_monomial_ge (LL : Letters N) (z : MvPolynomial (Fin N × Fin r) ℚ_[p]) (m0 : Fin N × Fin r →₀ ℕ)
    (hm0 : MultiDeg LL m0) (hc : ‖coeff m0 z‖ = 1) : 1 ≤ ‖fockN p LL z (monomial m0 1)‖ := by
  classical
  have hne : coeff m0 z ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  have hmem : m0 ∈ z.support := mem_support_iff.mpr hne
  unfold fockN
  rw [fock_monomial z m0 hmem]
  have hF : (m0.prod fun _ k => (k.factorial : ℚ_[p])) = ∏ v : Fin N × Fin r, ((m0 v).factorial : ℚ_[p]) :=
    Finsupp.prod_fintype _ _ (fun _ => by simp)
  have hdiv : ∀ i : Fin N, ∃ D : ℕ, (LL.deg i).factorial = (∏ c : Fin r, (m0 (i, c)).factorial) * D := by
    intro i
    rw [← hm0 i]
    exact Nat.prod_factorial_dvd_factorial_sum _ _
  choose D hD using hdiv
  have hprod : (∏ i, ((LL.deg i).factorial : ℚ_[p])) =
      (∏ v : Fin N × Fin r, ((m0 v).factorial : ℚ_[p])) * ((∏ i, D i : ℕ) : ℚ_[p]) := by
    rw [Fintype.prod_prod_type, Nat.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hD i]; push_cast; rfl
  rw [hF, hprod]
  have hF0 : (∏ v : Fin N × Fin r, ((m0 v).factorial : ℚ_[p])) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ => by exact_mod_cast (Nat.factorial_pos _).ne'
  have hD0 : ((∏ i, D i : ℕ) : ℚ_[p]) ≠ 0 := by
    have : (∏ i, D i) ≠ 0 := by
      intro h0
      obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp h0
      have := hD i; rw [hi, mul_zero] at this; exact (Nat.factorial_pos _).ne' this
    exact_mod_cast this
  rw [mul_comm (∏ v : Fin N × Fin r, ((m0 v).factorial : ℚ_[p])) _, mul_div_mul_comm, div_self hF0, mul_one, norm_div, hc]
  have hle : ‖((∏ i, D i : ℕ) : ℚ_[p])‖ ≤ 1 := by
    have := Padic.norm_int_le_one (p := p) ((∏ i, D i : ℕ) : ℤ)
    simpa using this
  have hpos : 0 < ‖((∏ i, D i : ℕ) : ℚ_[p])‖ := norm_pos_iff.mpr hD0
  rw [le_div_iff₀ hpos, one_mul]
  exact hle

end E2

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open Formalism.GM Formalism.GM.TM M MvPolynomial Finset

section E3

/- English proof (translation)
The claim follows from `| [], j, hj, _ => by simp at hj | a :: l, j, hj, u => by rw [lcomp_cons, LinearMap.comp_apply] rcases List.mem_cons.mp hj with rfl | hj' · exact hPP j _ · rw [hcomm j a, lcomp_fix P hPP hcomm l j hj' u]`.
-/
theorem lcomp_fix {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [LinearOrder ι] (P : ι → V →ₗ[K] V)
    (hPP : ∀ j x, P j (P j x) = P j x) (hcomm : ∀ j j' x, P j (P j' x) = P j' (P j x)) :
    ∀ l : List ι, ∀ j ∈ l, ∀ u, P j (lcomp P l u) = lcomp P l u
  | [], j, hj, _ => by simp at hj
  | a :: l, j, hj, u => by
    rw [lcomp_cons, LinearMap.comp_apply]
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact hPP j _
    · rw [hcomm j a, lcomp_fix P hPP hcomm l j hj' u]

/- English proof (translation)
The claim follows from `| [], u => rfl | a :: l, u => by rw [lcomp_cons, LinearMap.comp_apply, ← hsa a z, hz a, lcomp_fock P hsa z hz l u]`.
-/
theorem lcomp_fock {p : ℕ} [Fact p.Prime] {σ : Type} {ι : Type*} [LinearOrder ι]
    (P : ι → MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
    (hsa : ∀ j F G, fock p (P j F) G = fock p F (P j G)) (z : MvPolynomial σ ℚ_[p]) (hz : ∀ j, P j z = z) :
    ∀ l : List ι, ∀ u, fock p z (lcomp P l u) = fock p z u
  | [], u => rfl
  | a :: l, u => by
    rw [lcomp_cons, LinearMap.comp_apply, ← hsa a z, hz a, lcomp_fock P hsa z hz l u]

/- English proof (translation)
The claim follows from `| [], u, hu => by simpa [lcomp_nil] using hu | a :: l, u, hu => by have ih := lcomp_int LL e1 P hpol hint l u hu have e : ((p : ℚ_[p]) ^ (e1 * (a :: l).length)) • lcomp P (a :: l) u = ((p : ℚ_[p]) ^ e1) • P a (((p : ℚ_[p]) ^ (e1 * l.length)) • lcomp P l u) := by rw [lcomp_cons, L …`.
-/
theorem lcomp_int {p : ℕ} [Fact p.Prime] {N r : ℕ} {ι : Type*} [LinearOrder ι] (LL : Letters N) (e1 : ℕ)
    (P : ι → MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hpol : ∀ j, ∀ x ∈ Pol p r LL, P j x ∈ Pol p r LL)
    (hint : ∀ j, ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ e1) • P j F ∈ IntPol p (Fin N × Fin r)) :
    ∀ l : List ι, ∀ u ∈ PolZ p r LL, ((p : ℚ_[p]) ^ (e1 * l.length)) • lcomp P l u ∈ PolZ p r LL
  | [], u, hu => by simpa [lcomp_nil] using hu
  | a :: l, u, hu => by
    have ih := lcomp_int LL e1 P hpol hint l u hu
    have e : ((p : ℚ_[p]) ^ (e1 * (a :: l).length)) • lcomp P (a :: l) u =
        ((p : ℚ_[p]) ^ e1) • P a (((p : ℚ_[p]) ^ (e1 * l.length)) • lcomp P l u) := by
      rw [lcomp_cons, LinearMap.comp_apply, map_smul, smul_smul, ← pow_add, List.length_cons]
      congr 2; ring
    rw [e]
    refine Submodule.mem_inf.mpr ⟨?_, hint a _ ih⟩
    exact (Pol p r LL).smul_mem _ (hpol a _ (Submodule.mem_inf.mp ih).1)

/- English proof (translation)
Use `⟨2, by norm_num, ?_⟩` and prove the remaining obligations. Introduce `p _ N r _ _ LL q J M ρ a κ hr hκ hHP z hz hprim`. Take `⟨hP1, hP2⟩` from `hHP`. Use `set e1 := ⌈κ / (N + 2)⌉₊ with he1`. Set `Tj : Fin (N + 1) → Set (Fin r → ℤ)` to `fun j => {la | ∀ k, min (J k) N = (j : ℕ) → ((la 0 : ℤ) : WithTop ℤ) ≤ M k}`.

Establish `hex : ∀ j : Fin (N + 1), ∃ P, IsTypeProj p LL j univ (Tj j) P ∧ (∀ F G, fock p (P F) G = fock p F (P G)) ∧ ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r)` using `fun j => hP1 j (Nat.lt_succ_iff.mp j.isLt) univ (Or.inl rfl) (Tj j) (fun la la' h => by rw [show la = la' from funext fun c => h c (mem_univ c)])`. Use `choose P hPt hPsa hPint using hex`. Establish `hPP : ∀ j x, P j (P j x) = P j x` using `fun j x => LinearMap.congr_fun (hPt j).1 x`. Establish `hcomm : ∀ j j' x, P j (P j' x) = P j' (P j x)`. Introduce `j j' x`.

Break down `le_total (j : ℕ) (j' : ℕ) with h | h` into its components or cases. Conclude with `LinearMap.congr_fun (hP2 j j' univ univ (Tj j) (Tj j') (P j) (P j') h subset_rfl (Or.inl rfl) (Or.inl rfl) (hPt j) (hPt j')) x`. Conclude with `(LinearMap.congr_fun (hP2 j' j univ univ (Tj j') (Tj j) (P j') (P j) h subset_rfl (Or.inl rfl) (Or.inl rfl) (hPt j') (hPt j)) x).symm`. Establish `hPpol : ∀ j, ∀ x ∈ Pol p r LL, P j x ∈ Pol p r LL` using `fun j => typeProj_pol LL j (Tj j) (P j) (hPt j)`. Establish `hfixY : ∀ j : Fin (N + 1), ∀ x ∈ Y p (r` using `r) LL J M, P j x = x := by`.

Introduce `j`. Use `set S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) := Pol p r LL ⊓ ⨅ (k : Fin q) (_ : min (J k) N = (j : ℕ)), YCond p (r := r) LL j (M k) with hSdef`. Establish `hmemS : ∀ x, x ∈ S ↔ x ∈ Pol p r LL ∧ ∀ k, min (J k) N = (j : ℕ) → x ∈ YCond p (r` using `r) LL j (M k) := by`. Introduce `x`. Simplify using `only [hSdef, Submodule.mem_inf, Submodule.mem_iInf]`.

Establish `hfix` using `proj_fix LL j (Tj j) (P j) (hPt j) S inf_le_left (fun c d x hx => by`. Rewrite `hx`, the goal using `[hmemS]`. Conclude with `⟨glAct_pol LL j c d x hx.1, fun k hk => ycond_glStable LL j (M k) c d x (hx.2 k hk)⟩)`. Use the proof step `(fun x hx => by`. Rewrite `hx`, the goal using `[hmemS]`.

Conclude with `⟨hPpol j x hx.1, fun k hk => typeProj_ycond LL j (Tj j) (P j) (hPt j) (M k) x (hx.2 k hk)⟩)`. Use the proof step `(fun h hh hh0 μ hμ => by`. Rewrite `hh` using `[hmemS]`. Introduce `k hk`. Establish `h1` using `ycond_le_supp LL j (M k) (hh.2 k hk)`.

Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m, m ∈ h.support := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hh0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))`. Rewrite `h1` using `[mem_restrictSupport_iff]`.

Establish `h2` using `h1 (Finset.mem_coe.mpr hm)`. Establish `h3` using `(Submodule.mem_inf.mp hμ).1`. Rewrite `h3` using `[WtSpC, mem_restrictSupport_iff]`. Establish `h4` using `h3 (Finset.mem_coe.mpr hm) 0 (Finset.mem_univ _)`. Simplify using `only [Set.mem_ofPred_eq] at h2`.

Rewrite `h2` using `[h4]`. Conclude with `h2)`. Introduce `x hx`. Apply `hfix` to reduce the goal to its premises. Rewrite using `[hmemS]`.

Use `⟨(Submodule.mem_inf.mp hx).1, fun k hk => ?_⟩` and prove the remaining obligations. Use `(Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hx).2 k` as an intermediate fact. Rewrite `this` using `[ycond_min, hk]`. Conclude with `this`. Establish `hranY : ∀ j : Fin (N + 1), ∀ u, P j u = u → ∀ k, min (J k) N = (j : ℕ) → u ∈ YCond p (r` using `r) LL (J k) (M k) := by`.

Introduce `j u hu k hk`. Rewrite using `[ycond_min, hk]`. Establish `h1 : u ∈ LinearMap.range (P j)` using `⟨u, hu⟩`. Rewrite `h1` using `[(hPt j).2.1]`. Conclude with `(iSup₂_le fun la hla => isoC_le_ycond LL j la (M k) (hla k hk)) h1`.

Take `⟨m0, hm0⟩` from `prim_unit_coeff LL J M z hz hprim`. Establish `hzY : z ∈ Y p (r` using `r) LL J M := (Submodule.mem_inf.mp hz).1`. Establish `hzP : z ∈ Pol p r LL` using `(Submodule.mem_inf.mp (Submodule.mem_inf.mp hz).2).1`. Establish `hm0mem : m0 ∈ z.support`. Rewrite using `[mem_support_iff]`.

Introduce `h`. Rewrite `hm0` using `[h, norm_zero]`. Conclude with `zero_ne_one hm0`. Establish `hmd : MultiDeg LL m0`. Rewrite `hzP` using `[Pol, mem_restrictSupport_iff]`.

Conclude with `hzP (Finset.mem_coe.mpr hm0mem)`. Establish `hmonZ : (monomial m0 (1 : ℚ_[p])) ∈ PolZ p r LL` using `by classical`. Use `Submodule.mem_inf.mpr ⟨?_, mem_intPol_of_norm _ fun m => ?_⟩` and prove the remaining obligations. Use `show monomial m0 (1 : ℚ_[p]) ∈ Pol p r LL`. Rewrite using `[Pol, mem_restrictSupport_iff]`.

Introduce `m hm`. Rewrite `hm` using `[Finset.mem_coe]`. Rewrite using `[Finset.mem_singleton.mp (support_monomial_subset hm)]`. Conclude with `hmd`. Apply the tactic sequence `rw [coeff_monomial]; split_ifs <;> simp`.

Use `set u := lcomp P (List.finRange (N + 1)) (monomial m0 (1 : ℚ_[p])) with hu`. Establish `hufix : ∀ j, P j u = u` using `fun j => lcomp_fix P hPP hcomm _ j (List.mem_finRange j) _`. Establish `hint` using `lcomp_int LL e1 P hPpol hPint (List.finRange (N + 1)) _ hmonZ`. Rewrite `hint` using `[List.length_finRange]`. Use `⟨((p : ℚ_[p]) ^ (e1 * (N + 1))) • u, ?_, e1 * (N + 1), ?_, ?_⟩` and prove the remaining obligations.

Use `Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hint).1, ?_⟩, hint⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_iInf]`. Introduce `k`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Conclude with `hranY ⟨min (J k) N, by omega⟩ u (hufix _) k rfl`.

Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`. Establish `hlg1 : 1 ≤ lgV2 p a r`. Unfold `lgV2`. Establish `: (1 : ℝ) ≤ 8 * (a : ℝ) + r`. Establish `: (2 : ℝ) ≤ r` using `by exact_mod_cast hr`.

Establish `: (0 : ℝ) ≤ a` using `Nat.cast_nonneg a`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Real.logb_nonneg hp1 this` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hr2 : (4 : ℝ) ≤ (r : ℝ) ^ 2`.

Establish `: (2 : ℝ) ≤ r` using `by exact_mod_cast hr`. Use the polynomial consequences of the given equalities and inequalities. Establish `hN : (0 : ℝ) ≤ N` using `Nat.cast_nonneg N`. Establish `hκN : (N : ℝ) + 1 ≤ κ`. Establish `h1 : ((N : ℝ) + 2) * 4 ≤ ((N : ℝ) + 2) * (r : ℝ) ^ 2` using `mul_le_mul_of_nonneg_left hr2 (by positivity)`.

Establish `h2 : ((N : ℝ) + 2) * (r : ℝ) ^ 2 ≤ ((N : ℝ) + 2) * (r : ℝ) ^ 2 * lgV2 p a r` using `le_mul_of_one_le_right (by positivity) hlg1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hκ0 : 0 ≤ κ` using `by linarith`. Establish `hce : (e1 : ℝ) < κ / (N + 2) + 1` using `Nat.ceil_lt_add_one (by positivity)`. Establish `h3 : κ / (N + 2) * (N + 1) ≤ κ`.

Rewrite using `[div_mul_eq_mul_div, div_le_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[fockN_smul_right', norm_mul, norm_pow, Padic.norm_p]`.

Establish `hf : fockN p LL z u = fockN p LL z (monomial m0 1)`. Unfold `fockN`. Rewrite using `[hu, lcomp_fock P hPsa z (fun j => hfixY j z hzY)]`. Rewrite using `[hf]`. Establish `hge` using `fockN_monomial_ge LL z m0 hmd hm0`.

Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).pos`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[zpow_neg, zpow_natCast, inv_pow, mul_one]`. Use `_ ≤ (p : ℝ)⁻¹ ^ (e1 * (N + 1)) * ‖fockN p LL z (monomial m0 1)‖ := mul_le_mul_of_nonneg_left hge (by positivity)`.
-/
theorem partner_condition : YPartner := by
  refine ⟨2, by norm_num, ?_⟩
  intro p _ N r _ _ LL q J M ρ a κ hr hκ hHP z hz hprim
  obtain ⟨hP1, hP2⟩ := hHP
  set e1 := ⌈κ / (N + 2)⌉₊ with he1
  let Tj : Fin (N + 1) → Set (Fin r → ℤ) := fun j =>
    {la | ∀ k, min (J k) N = (j : ℕ) → ((la 0 : ℤ) : WithTop ℤ) ≤ M k}
  have hex : ∀ j : Fin (N + 1), ∃ P, IsTypeProj p LL j univ (Tj j) P ∧ (∀ F G, fock p (P F) G = fock p F (P G)) ∧
      ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r) :=
    fun j => hP1 j (Nat.lt_succ_iff.mp j.isLt) univ (Or.inl rfl) (Tj j)
      (fun la la' h => by rw [show la = la' from funext fun c => h c (mem_univ c)])
  choose P hPt hPsa hPint using hex
  have hPP : ∀ j x, P j (P j x) = P j x := fun j x => LinearMap.congr_fun (hPt j).1 x
  have hcomm : ∀ j j' x, P j (P j' x) = P j' (P j x) := by
    intro j j' x
    rcases le_total (j : ℕ) (j' : ℕ) with h | h
    · exact LinearMap.congr_fun (hP2 j j' univ univ (Tj j) (Tj j') (P j) (P j') h subset_rfl (Or.inl rfl)
        (Or.inl rfl) (hPt j) (hPt j')) x
    · exact (LinearMap.congr_fun (hP2 j' j univ univ (Tj j') (Tj j) (P j') (P j) h subset_rfl (Or.inl rfl)
        (Or.inl rfl) (hPt j') (hPt j)) x).symm
  have hPpol : ∀ j, ∀ x ∈ Pol p r LL, P j x ∈ Pol p r LL := fun j => typeProj_pol LL j (Tj j) (P j) (hPt j)

  have hfixY : ∀ j : Fin (N + 1), ∀ x ∈ Y p (r := r) LL J M, P j x = x := by
    intro j
    set S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
      Pol p r LL ⊓ ⨅ (k : Fin q) (_ : min (J k) N = (j : ℕ)), YCond p (r := r) LL j (M k) with hSdef
    have hmemS : ∀ x, x ∈ S ↔ x ∈ Pol p r LL ∧ ∀ k, min (J k) N = (j : ℕ) → x ∈ YCond p (r := r) LL j (M k) := by
      intro x; simp only [hSdef, Submodule.mem_inf, Submodule.mem_iInf]
    have hfix := proj_fix LL j (Tj j) (P j) (hPt j) S inf_le_left
      (fun c d x hx => by
        rw [hmemS] at hx ⊢
        exact ⟨glAct_pol LL j c d x hx.1, fun k hk => ycond_glStable LL j (M k) c d x (hx.2 k hk)⟩)
      (fun x hx => by
        rw [hmemS] at hx ⊢
        exact ⟨hPpol j x hx.1, fun k hk => typeProj_ycond LL j (Tj j) (P j) (hPt j) (M k) x (hx.2 k hk)⟩)
      (fun h hh hh0 μ hμ => by
        rw [hmemS] at hh
        intro k hk
        have h1 := ycond_le_supp LL j (M k) (hh.2 k hk)
        obtain ⟨m, hm⟩ : ∃ m, m ∈ h.support := by
          by_contra hc; push Not at hc
          exact hh0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
        rw [mem_restrictSupport_iff] at h1
        have h2 := h1 (Finset.mem_coe.mpr hm)
        have h3 := (Submodule.mem_inf.mp hμ).1
        rw [WtSpC, mem_restrictSupport_iff] at h3
        have h4 := h3 (Finset.mem_coe.mpr hm) 0 (Finset.mem_univ _)
        simp only [Set.mem_ofPred_eq] at h2
        rw [h4] at h2
        exact h2)
    intro x hx
    apply hfix
    rw [hmemS]
    refine ⟨(Submodule.mem_inf.mp hx).1, fun k hk => ?_⟩
    have := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hx).2 k
    rw [ycond_min, hk] at this
    exact this

  have hranY : ∀ j : Fin (N + 1), ∀ u, P j u = u → ∀ k, min (J k) N = (j : ℕ) →
      u ∈ YCond p (r := r) LL (J k) (M k) := by
    intro j u hu k hk
    rw [ycond_min, hk]
    have h1 : u ∈ LinearMap.range (P j) := ⟨u, hu⟩
    rw [(hPt j).2.1] at h1
    exact (iSup₂_le fun la hla => isoC_le_ycond LL j la (M k) (hla k hk)) h1

  obtain ⟨m0, hm0⟩ := prim_unit_coeff LL J M z hz hprim
  have hzY : z ∈ Y p (r := r) LL J M := (Submodule.mem_inf.mp hz).1
  have hzP : z ∈ Pol p r LL := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hz).2).1
  have hm0mem : m0 ∈ z.support := by
    rw [mem_support_iff]; intro h; rw [h, norm_zero] at hm0; exact zero_ne_one hm0
  have hmd : MultiDeg LL m0 := by
    rw [Pol, mem_restrictSupport_iff] at hzP; exact hzP (Finset.mem_coe.mpr hm0mem)
  have hmonZ : (monomial m0 (1 : ℚ_[p])) ∈ PolZ p r LL := by
    classical
    refine Submodule.mem_inf.mpr ⟨?_, mem_intPol_of_norm _ fun m => ?_⟩
    · show monomial m0 (1 : ℚ_[p]) ∈ Pol p r LL
      rw [Pol, mem_restrictSupport_iff]
      intro m hm
      rw [Finset.mem_coe] at hm
      rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
      exact hmd
    · rw [coeff_monomial]; split_ifs <;> simp
  set u := lcomp P (List.finRange (N + 1)) (monomial m0 (1 : ℚ_[p])) with hu
  have hufix : ∀ j, P j u = u := fun j => lcomp_fix P hPP hcomm _ j (List.mem_finRange j) _
  have hint := lcomp_int LL e1 P hPpol hPint (List.finRange (N + 1)) _ hmonZ
  rw [List.length_finRange] at hint
  refine ⟨((p : ℚ_[p]) ^ (e1 * (N + 1))) • u, ?_, e1 * (N + 1), ?_, ?_⟩
  · refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hint).1, ?_⟩, hint⟩
    rw [Submodule.mem_iInf]
    intro k
    refine Submodule.smul_mem _ _ ?_
    exact hranY ⟨min (J k) N, by omega⟩ u (hufix _) k rfl
  ·
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hlg1 : 1 ≤ lgV2 p a r := by
      unfold lgV2
      have : (1 : ℝ) ≤ 8 * (a : ℝ) + r := by
        have : (2 : ℝ) ≤ r := by exact_mod_cast hr
        have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
        linarith
      have := Real.logb_nonneg hp1 this
      linarith
    have hr2 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ r := by exact_mod_cast hr
      nlinarith
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hκN : (N : ℝ) + 1 ≤ κ := by
      have h1 : ((N : ℝ) + 2) * 4 ≤ ((N : ℝ) + 2) * (r : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hr2 (by positivity)
      have h2 : ((N : ℝ) + 2) * (r : ℝ) ^ 2 ≤ ((N : ℝ) + 2) * (r : ℝ) ^ 2 * lgV2 p a r :=
        le_mul_of_one_le_right (by positivity) hlg1
      linarith
    have hκ0 : 0 ≤ κ := by linarith
    have hce : (e1 : ℝ) < κ / (N + 2) + 1 := Nat.ceil_lt_add_one (by positivity)
    have h3 : κ / (N + 2) * (N + 1) ≤ κ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    push_cast
    calc (e1 : ℝ) * (N + 1) ≤ (κ / (N + 2) + 1) * (N + 1) := mul_le_mul_of_nonneg_right hce.le (by positivity)
      _ = κ / (N + 2) * (N + 1) + (N + 1) := by ring
      _ ≤ 2 * κ := by linarith
  ·
    rw [fockN_smul_right', norm_mul, norm_pow, Padic.norm_p]
    have hf : fockN p LL z u = fockN p LL z (monomial m0 1) := by
      unfold fockN
      rw [hu, lcomp_fock P hPsa z (fun j => hfixY j z hzY)]
    rw [hf]
    have hge := fockN_monomial_ge LL z m0 hmd hm0
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    calc (p : ℝ) ^ (-((e1 * (N + 1) : ℕ) : ℤ)) = (p : ℝ)⁻¹ ^ (e1 * (N + 1)) * 1 := by
          rw [zpow_neg, zpow_natCast, inv_pow, mul_one]
      _ ≤ (p : ℝ)⁻¹ ^ (e1 * (N + 1)) * ‖fockN p LL z (monomial m0 1)‖ :=
          mul_le_mul_of_nonneg_left hge (by positivity)

end E3

end Formalism.CountingSumsFrames

namespace Formalism.CountingSumsFrames

open Formalism.GM Formalism.GM.TM

/- English proof (translation)
The claim follows from `partnerM_of_parts hTie partner_condition`.
-/
theorem partnerM_of_tieOps (hTie : TieOps) : PartnerM := partnerM_of_parts hTie partner_condition

end Formalism.CountingSumsFrames
