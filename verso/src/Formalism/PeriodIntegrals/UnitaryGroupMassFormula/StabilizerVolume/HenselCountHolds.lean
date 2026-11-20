import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.HenselCount

noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology

section Hensel

variable {V X : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]

def hlev (Λ0 : AddSubgroup V) (H : AddSubgroup X) (G : V → X) (y : V) (h : X) : Set V :=
  {Z | Z ∈ Λ0 ∧ G (y + Z) - h ∈ H}

/- English proof (translation)
Take `⟨f, hf⟩ : ∃ f : V → X, ∀ Z, f Z = G (y + Z) - h` from `⟨_, fun _ => rfl⟩`. Establish `memS : ∀ m Z, Z ∈ hlev (Λ 0) (H m) G y h ↔ Z ∈ Λ 0 ∧ f Z ∈ H m`. Introduce `m Z`. Rewrite using `[hf]`. Both sides reduce to the same expression.

Establish `hHa : ∀ m, H (m + 1) ≤ H m` using `fun m => by`. Rewrite using `[← hD, ← hD]`. Conclude with `AddSubgroup.map_mono (hΛa (Nat.le_succ m))`. Establish `hΛ0 : ∀ m, Λ m ≤ Λ 0` using `fun m => hΛa (Nat.zero_le m)`. Establish `hDm : ∀ m, ∀ W ∈ Λ m, D W ∈ H m` using `fun m W hW => by`.

Rewrite using `[← hD]`. Conclude with `AddSubgroup.mem_map_of_mem D hW`. Establish `hstep : ∀ m, ∀ Z ∈ Λ 0, ∀ W ∈ Λ m, f (Z + W) - f Z - D W ∈ H (m + 1)`. Introduce `m Z hZ W hW`. Establish `e` using `hG m Z hZ W hW`.

Establish `: f (Z + W) - f Z - D W = G (y + Z + W) - G (y + Z) - D W`. Rewrite using `[hf, hf, ← add_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `e`.

Establish `hinv : ∀ m, ∀ Z ∈ hlev (Λ 0) (H m) G y h, ∀ W ∈ Λ m, Z + W ∈ hlev (Λ 0) (H m) G y h`. Introduce `m Z hZ W hW`. Rewrite `hZ`, the goal using `[memS]`. Use `⟨(Λ 0).add_mem hZ.1 (hΛ0 m hW), ?_⟩` and prove the remaining obligations. Establish `e` using `hstep m Z hZ.1 W hW`.

Establish `: f (Z + W) = (f (Z + W) - f Z - D W) + f Z + D W` using `by abel`. Rewrite using `[this]`. Conclude with `(H m).add_mem ((H m).add_mem (hHa m e) hZ.2) (hDm m W hW)`. Establish `hopen : ∀ m, IsOpen (hlev (Λ 0) (H m) G y h)`. Introduce `m`.

Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce `Z hZ`. Use `⟨(fun u => -Z + u) ⁻¹' (Λ m : Set V), ?_, (hΛo m).preimage (continuous_const.add continuous_id), ?_⟩` and prove the remaining obligations. Introduce `u hu`. Use `hinv m Z hZ _ hu` as an intermediate fact.

Establish `e : Z + (-Z + u) = u` using `by abel`. Rewrite `this` using `[e]`. Conclude with `this`. Use `show -Z + Z ∈ Λ m`. Rewrite using `[neg_add_cancel]`.

Conclude with `(Λ m).zero_mem`. Establish `hsub : ∀ m, hlev (Λ 0) (H (m + 1)) G y h ⊆ hlev (Λ 0) (H m) G y h`. Introduce `m Z hZ`. Rewrite `hZ`, the goal using `[memS]`. Conclude with `⟨hZ.1, hHa m hZ.2⟩`.

Proceed by induction on `n with`. Consider the case `zero`. Establish `hS0 : hlev (Λ 0) (H 0) G y h = (Λ 0 : Set V)`. Use extensionality with `Z`. Rewrite using `[memS]`.

Use `⟨And.left, fun hZ => ⟨hZ, ?_⟩⟩` and prove the remaining obligations. Establish `e` using `hstep 0 0 (Λ 0).zero_mem Z hZ`. Establish `h0 : f 0 ∈ H 0`. Establish `: f 0 = -(h - G y)` using `by rw [hf, add_zero]; abel`. Rewrite using `[this]`.

Conclude with `(H 0).neg_mem hh`. Establish `: f Z = (f (0 + Z) - f 0 - D Z) + f 0 + D Z` using `by rw [zero_add]; abel`. Rewrite using `[this]`. Conclude with `(H 0).add_mem ((H 0).add_mem (hHa 0 e) h0) (hDm 0 Z hZ)`. Rewrite using `[hS0]`.

Consider the case `succ m ih => haveI : DiscreteTopology (X ⧸ H (m + 1)) := QuotientAddGroup.discreteTopology (hHo (m + 1)) set C : Set (X ⧸ H (m + 1)) := (QuotientAddGroup.mk : X → X ⧸ H (m + 1)) '' (H m : Set X) with hC`. Establish `hCf : C.Finite` using `((hHc m).image QuotientAddGroup.continuous_mk).finite_of_discrete`. Use `haveI : Fintype C := hCf.fintype`. Establish `hxc : ∀ c : C, ∃ u ∈ H m, (u : X ⧸ H (m + 1)) = c` using `fun c => c.2`. Use `choose x hxm hxq using hxc`.

Establish `htc : ∀ c : C, ∃ W ∈ Λ m, D W = x c`. Introduce `c`. Use `hxm c` as an intermediate fact. Rewrite `this` using `[← hD]`. Conclude with `AddSubgroup.mem_map.1 this`.

Use `choose t htm htD using htc`. Establish `hcov : ∀ u ∈ H m, ∃ c : C, -x c + u ∈ H (m + 1)`. Introduce `u hu`. Use `⟨⟨(u : X ⧸ H (m + 1)), u, hu, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← QuotientAddGroup.eq, hxq]`.

Establish `hinj : ∀ c d : C, -x c + x d ∈ H (m + 1) → c = d`. Introduce `c d hcd`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hxq c, ← hxq d]`. Conclude with `QuotientAddGroup.eq.2 hcd`.

Establish `hne : Nonempty C` using `⟨(hcov 0 (H m).zero_mem).choose⟩`. Establish `hAi : ∀ c Z, Z ∈ (fun Z => -t c + Z) ⁻¹' hlev (Λ 0) (H (m + 1)) G y h → -x c + f Z ∈ H (m + 1)`. Introduce `c Z hZ`. Establish `hZ'` using `(memS _ _).1 hZ`. Establish `e` using `hstep m (-t c + Z) hZ'.1 (t c) (htm c)`.

Establish `e2 : -t c + Z + t c = Z` using `by abel`. Rewrite `e` using `[e2, htD]`. Establish `: -x c + f Z = (f Z - f (-t c + Z) - x c) + f (-t c + Z)` using `by abel`. Rewrite using `[this]`. Conclude with `(H (m + 1)).add_mem e hZ'.2`.

Establish `hμ : μ (hlev (Λ 0) (H m) G y h) = (Fintype.card C : ENNReal) * μ (hlev (Λ 0) (H (m + 1)) G y h)`. Establish `hU : hlev (Λ 0) (H m) G y h = ⋃ c : C, (fun Z => -t c + Z) ⁻¹' hlev (Λ 0) (H (m + 1)) G y h`. Use extensionality with `Z`. Simplify using `only [Set.mem_iUnion, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion.

Introduce `hZ`. Establish `hZ'` using `(memS _ _).1 hZ`. Take `⟨c, hc⟩` from `hcov (f Z) hZ'.2`. Use `⟨c, (memS _ _).2 ⟨(Λ 0).add_mem ((Λ 0).neg_mem (hΛ0 m (htm c))) hZ'.1, ?_⟩⟩` and prove the remaining obligations. Establish `e` using `hstep m (-t c + Z) ((Λ 0).add_mem ((Λ 0).neg_mem (hΛ0 m (htm c))) hZ'.1) (t c) (htm c)`.

Establish `e2 : -t c + Z + t c = Z` using `by abel`. Rewrite `e` using `[e2, htD]`. Establish `: f (-t c + Z) = -(f Z - f (-t c + Z) - x c) + (-x c + f Z)` using `by abel`. Rewrite using `[this]`. Conclude with `(H (m + 1)).add_mem ((H (m + 1)).neg_mem e) hc`.

Introduce and unpack `⟨c, hc⟩`. Use `hinv m _ (hsub m hc) (t c) (htm c)` as an intermediate fact. Establish `e2 : -t c + Z + t c = Z` using `by abel`. Rewrite `this` using `[e2]`. Then use the resulting hypothesis. Rewrite using `[hU, measure_iUnion, tsum_fintype]`.

Simplify using `only [measure_preimage_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Introduce `c d hcd`. Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce `Z hc hd`. Apply `hcd` to reduce the goal to its premises.

Apply `hinj` to reduce the goal to its premises. Establish `a1` using `hAi c Z hc`. Establish `a2` using `hAi d Z hd`. Establish `: -x c + x d = (-x c + f Z) - (-x d + f Z)` using `by abel`. Rewrite using `[this]`.

Conclude with `(H (m + 1)).sub_mem a1 a2`. Introduce `c`. Conclude with `((hopen (m + 1)).preimage (continuous_const.add continuous_id)).measurableSet`. Establish `hν : ν (H m) = (Fintype.card C : ENNReal) * ν (H (m + 1))`. Establish `hU : (H m : Set X) = ⋃ c : C, (fun u => -x c + u) ⁻¹' (H (m + 1) : Set X)`.

Use extensionality with `u`. Simplify using `only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `hu`. Conclude with `hcov u hu`.

Introduce and unpack `⟨c, hc⟩`. Establish `: u = x c + (-x c + u)` using `by abel`. Rewrite using `[this]`. Conclude with `(H m).add_mem (hxm c) (hHa m hc)`. Rewrite using `[hU, measure_iUnion, tsum_fintype]`.

Simplify using `only [measure_preimage_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Introduce `c d hcd`. Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce `u hc hd`. Apply `hcd` to reduce the goal to its premises.

Apply `hinj` to reduce the goal to its premises. Simplify using `only [Set.mem_preimage, SetLike.mem_coe] at hc hd`. Establish `: -x c + x d = (-x c + u) - (-x d + u)` using `by abel`. Rewrite using `[this]`. Conclude with `(H (m + 1)).sub_mem hc hd`.

Introduce `c`. Conclude with `((hHo (m + 1)).preimage (continuous_const.add continuous_id)).measurableSet`. Establish `hc0 : (Fintype.card C : ENNReal) ≠ 0`. Conclude with `(Fintype.card_ne_zero : Fintype.card C ≠ 0)` after adjusting the coercions. Establish `hct : (Fintype.card C : ENNReal) ≠ ⊤` using `ENNReal.natCast_ne_top _`.

Apply `(ENNReal.mul_right_inj hc0 hct).1` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hensel_main (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set V))
    (hΛa : Antitone Λ) (hHo : ∀ n, IsOpen (H n : Set X)) (hHc : ∀ n, IsCompact (H n : Set X))
    (D : V →+ X) (hD : ∀ n, (Λ n).map D = H n) (G : V → X) (y : V)
    (hG : ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1))
    (h : X) (hh : h - G y ∈ H 0) (n : ℕ) :
    μ (hlev (Λ 0) (H n) G y h) * ν (H 0) = μ (Λ 0) * ν (H n) := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : V → X, ∀ Z, f Z = G (y + Z) - h := ⟨_, fun _ => rfl⟩
  have memS : ∀ m Z, Z ∈ hlev (Λ 0) (H m) G y h ↔ Z ∈ Λ 0 ∧ f Z ∈ H m := by
    intro m Z; rw [hf]; rfl
  have hHa : ∀ m, H (m + 1) ≤ H m := fun m => by
    rw [← hD, ← hD]; exact AddSubgroup.map_mono (hΛa (Nat.le_succ m))
  have hΛ0 : ∀ m, Λ m ≤ Λ 0 := fun m => hΛa (Nat.zero_le m)
  have hDm : ∀ m, ∀ W ∈ Λ m, D W ∈ H m := fun m W hW => by
    rw [← hD]; exact AddSubgroup.mem_map_of_mem D hW

  have hstep : ∀ m, ∀ Z ∈ Λ 0, ∀ W ∈ Λ m, f (Z + W) - f Z - D W ∈ H (m + 1) := by
    intro m Z hZ W hW
    have e := hG m Z hZ W hW
    have : f (Z + W) - f Z - D W = G (y + Z + W) - G (y + Z) - D W := by
      rw [hf, hf, ← add_assoc]; abel
    rw [this]; exact e

  have hinv : ∀ m, ∀ Z ∈ hlev (Λ 0) (H m) G y h, ∀ W ∈ Λ m, Z + W ∈ hlev (Λ 0) (H m) G y h := by
    intro m Z hZ W hW
    rw [memS] at hZ ⊢
    refine ⟨(Λ 0).add_mem hZ.1 (hΛ0 m hW), ?_⟩
    have e := hstep m Z hZ.1 W hW
    have : f (Z + W) = (f (Z + W) - f Z - D W) + f Z + D W := by abel
    rw [this]
    exact (H m).add_mem ((H m).add_mem (hHa m e) hZ.2) (hDm m W hW)
  have hopen : ∀ m, IsOpen (hlev (Λ 0) (H m) G y h) := by
    intro m
    rw [isOpen_iff_forall_mem_open]
    intro Z hZ
    refine ⟨(fun u => -Z + u) ⁻¹' (Λ m : Set V), ?_,
      (hΛo m).preimage (continuous_const.add continuous_id), ?_⟩
    · intro u hu
      have := hinv m Z hZ _ hu
      have e : Z + (-Z + u) = u := by abel
      rw [e] at this; exact this
    · show -Z + Z ∈ Λ m
      rw [neg_add_cancel]; exact (Λ m).zero_mem
  have hsub : ∀ m, hlev (Λ 0) (H (m + 1)) G y h ⊆ hlev (Λ 0) (H m) G y h := by
    intro m Z hZ
    rw [memS] at hZ ⊢
    exact ⟨hZ.1, hHa m hZ.2⟩
  induction n with
  | zero =>
    have hS0 : hlev (Λ 0) (H 0) G y h = (Λ 0 : Set V) := by
      ext Z
      rw [memS]
      refine ⟨And.left, fun hZ => ⟨hZ, ?_⟩⟩
      have e := hstep 0 0 (Λ 0).zero_mem Z hZ
      have h0 : f 0 ∈ H 0 := by
        have : f 0 = -(h - G y) := by rw [hf, add_zero]; abel
        rw [this]; exact (H 0).neg_mem hh
      have : f Z = (f (0 + Z) - f 0 - D Z) + f 0 + D Z := by rw [zero_add]; abel
      rw [this]
      exact (H 0).add_mem ((H 0).add_mem (hHa 0 e) h0) (hDm 0 Z hZ)
    rw [hS0]
  | succ m ih =>

    haveI : DiscreteTopology (X ⧸ H (m + 1)) := QuotientAddGroup.discreteTopology (hHo (m + 1))
    set C : Set (X ⧸ H (m + 1)) := (QuotientAddGroup.mk : X → X ⧸ H (m + 1)) '' (H m : Set X)
      with hC
    have hCf : C.Finite := ((hHc m).image QuotientAddGroup.continuous_mk).finite_of_discrete
    haveI : Fintype C := hCf.fintype
    have hxc : ∀ c : C, ∃ u ∈ H m, (u : X ⧸ H (m + 1)) = c := fun c => c.2
    choose x hxm hxq using hxc
    have htc : ∀ c : C, ∃ W ∈ Λ m, D W = x c := by
      intro c
      have := hxm c
      rw [← hD] at this
      exact AddSubgroup.mem_map.1 this
    choose t htm htD using htc
    have hcov : ∀ u ∈ H m, ∃ c : C, -x c + u ∈ H (m + 1) := by
      intro u hu
      refine ⟨⟨(u : X ⧸ H (m + 1)), u, hu, rfl⟩, ?_⟩
      rw [← QuotientAddGroup.eq, hxq]
    have hinj : ∀ c d : C, -x c + x d ∈ H (m + 1) → c = d := by
      intro c d hcd
      apply Subtype.ext
      rw [← hxq c, ← hxq d]
      exact QuotientAddGroup.eq.2 hcd
    have hne : Nonempty C := ⟨(hcov 0 (H m).zero_mem).choose⟩

    have hAi : ∀ c Z, Z ∈ (fun Z => -t c + Z) ⁻¹' hlev (Λ 0) (H (m + 1)) G y h →
        -x c + f Z ∈ H (m + 1) := by
      intro c Z hZ
      have hZ' := (memS _ _).1 hZ
      have e := hstep m (-t c + Z) hZ'.1 (t c) (htm c)
      have e2 : -t c + Z + t c = Z := by abel
      rw [e2, htD] at e
      have : -x c + f Z = (f Z - f (-t c + Z) - x c) + f (-t c + Z) := by abel
      rw [this]
      exact (H (m + 1)).add_mem e hZ'.2
    have hμ : μ (hlev (Λ 0) (H m) G y h) =
        (Fintype.card C : ENNReal) * μ (hlev (Λ 0) (H (m + 1)) G y h) := by
      have hU : hlev (Λ 0) (H m) G y h =
          ⋃ c : C, (fun Z => -t c + Z) ⁻¹' hlev (Λ 0) (H (m + 1)) G y h := by
        ext Z
        simp only [Set.mem_iUnion, Set.mem_preimage]
        constructor
        · intro hZ
          have hZ' := (memS _ _).1 hZ
          obtain ⟨c, hc⟩ := hcov (f Z) hZ'.2
          refine ⟨c, (memS _ _).2 ⟨(Λ 0).add_mem ((Λ 0).neg_mem (hΛ0 m (htm c))) hZ'.1, ?_⟩⟩
          have e := hstep m (-t c + Z) ((Λ 0).add_mem ((Λ 0).neg_mem (hΛ0 m (htm c))) hZ'.1)
            (t c) (htm c)
          have e2 : -t c + Z + t c = Z := by abel
          rw [e2, htD] at e
          have : f (-t c + Z) = -(f Z - f (-t c + Z) - x c) + (-x c + f Z) := by abel
          rw [this]
          exact (H (m + 1)).add_mem ((H (m + 1)).neg_mem e) hc
        · rintro ⟨c, hc⟩
          have := hinv m _ (hsub m hc) (t c) (htm c)
          have e2 : -t c + Z + t c = Z := by abel
          rwa [e2] at this
      rw [hU, measure_iUnion, tsum_fintype]
      · simp only [measure_preimage_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      · intro c d hcd
        rw [Function.onFun, Set.disjoint_left]
        intro Z hc hd
        apply hcd
        apply hinj
        have a1 := hAi c Z hc
        have a2 := hAi d Z hd
        have : -x c + x d = (-x c + f Z) - (-x d + f Z) := by abel
        rw [this]; exact (H (m + 1)).sub_mem a1 a2
      · intro c
        exact ((hopen (m + 1)).preimage (continuous_const.add continuous_id)).measurableSet
    have hν : ν (H m) = (Fintype.card C : ENNReal) * ν (H (m + 1)) := by
      have hU : (H m : Set X) = ⋃ c : C, (fun u => -x c + u) ⁻¹' (H (m + 1) : Set X) := by
        ext u
        simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
        constructor
        · intro hu; exact hcov u hu
        · rintro ⟨c, hc⟩
          have : u = x c + (-x c + u) := by abel
          rw [this]; exact (H m).add_mem (hxm c) (hHa m hc)
      rw [hU, measure_iUnion, tsum_fintype]
      · simp only [measure_preimage_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      · intro c d hcd
        rw [Function.onFun, Set.disjoint_left]
        intro u hc hd
        apply hcd
        apply hinj
        simp only [Set.mem_preimage, SetLike.mem_coe] at hc hd
        have : -x c + x d = (-x c + u) - (-x d + u) := by abel
        rw [this]; exact (H (m + 1)).sub_mem hc hd
      · intro c
        exact ((hHo (m + 1)).preimage (continuous_const.add continuous_id)).measurableSet
    have hc0 : (Fintype.card C : ENNReal) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card C ≠ 0)
    have hct : (Fintype.card C : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    apply (ENNReal.mul_right_inj hc0 hct).1
    calc (Fintype.card C : ENNReal) * (μ (hlev (Λ 0) (H (m + 1)) G y h) * ν (H 0))
        = μ (hlev (Λ 0) (H m) G y h) * ν (H 0) := by rw [hμ, mul_assoc]
      _ = μ (Λ 0) * ν (H m) := ih
      _ = (Fintype.card C : ENNReal) * (μ (Λ 0) * ν (H (m + 1))) := by rw [hν]; ring

end Hensel

/- English proof (translation)
Introduce `V X _ _ _ _ _ _ _ _ _ _ μ ν _ _ Λ H hΛo _ hΛa hHo hHc D hD G y hG n h hh`. Conclude with `hensel_main μ ν Λ H hΛo hΛa hHo hHc D hD G y hG h hh n`.
-/
theorem henselCount_holds : HenselCount := by
  intro V X _ _ _ _ _ _ _ _ _ _ μ ν _ _ Λ H hΛo _ hΛa hHo hHc D hD G y hG n h hh
  exact hensel_main μ ν Λ H hΛo hΛa hHo hHc D hD G y hG h hh n

end PI.VolStabS
