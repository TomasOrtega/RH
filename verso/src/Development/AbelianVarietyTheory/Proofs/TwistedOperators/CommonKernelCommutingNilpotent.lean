import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

namespace GlobalTheory

noncomputable def jointNullChain {V : Type} [AddCommGroup V] [Module ℂ V] (T : ℕ → Module.End ℂ V)
    (S : Submodule ℂ V) : ℕ → Submodule ℂ V
  | 0 => S
  | m + 1 => jointNullChain T S m ⊓ LinearMap.ker (T m)

/- English proof (translation)
Introduce `V _ _ T S hfin hne hstab hcomm hnil`. Use `set Z := jointNullChain T S with hZ`. Establish `hsucc : ∀ m, Z (m + 1) = Z m ⊓ LinearMap.ker (T m)` using `fun m => rfl`. Establish `hanti : Antitone Z` using `antitone_nat_of_succ_le (fun m => by rw [hsucc]; exact inf_le_left)`. Establish `hleS : ∀ m, Z m ≤ S` using `fun m => hanti (Nat.zero_le m)`.

Establish `hst : ∀ m l, ∀ v ∈ Z m, T l v ∈ Z m`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => exact fun l v hv => hstab l v hv`. Consider the case `succ m ih`.

Introduce `l v hv`. Rewrite `hv`, the goal using `[hsucc]`. Use `⟨ih l v hv.1, ?_⟩` and prove the remaining obligations. Establish `h0 : T m v = 0` using `hv.2`. Use `show T m (T l v) = 0`.

Use `LinearMap.congr_fun (hcomm m l).eq v` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`. Rewrite using `[this, h0, map_zero]`. Establish `hstpow : ∀ m l i, ∀ v ∈ Z m, (T l ^ i) v ∈ Z m`. Introduce `m l i`.

Proceed by induction on `i with`. Consider the case `zero => intro v hv`. Simplify using `using hv`. Consider the case `succ i ih`. Introduce `v hv`.

Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `hst m l _ (ih v hv)`. Establish `hkill : ∀ m, ∀ k < m, ∀ v ∈ Z m, T k v = 0`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => intro k hk`. Use linear arithmetic over natural numbers and integers. Consider the case `succ m ih`. Introduce `k hk v hv`. Rewrite `hv` using `[hsucc]`.

Break down `Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk` into its components or cases. Conclude with `ih k hk v hv.1`. Substitute `hk` using the available equality. Conclude with `hv.2`. Establish `hnebot : ∀ m, Z m ≠ ⊥`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => exact hne`. Consider the case `succ m ih`. Take `⟨w, hw, hw0⟩` from `Submodule.ne_bot_iff _ |>.mp ih`.

Establish `hex : ∃ N : ℕ, (T m ^ N) w = 0` using `hnil m w (hleS m hw)`. Use `set N0 := Nat.find hex with hN0`. Establish `hN0spec : (T m ^ N0) w = 0` using `Nat.find_spec hex`. Establish `hN0pos : N0 ≠ 0`. Introduce `h`.

Rewrite `hN0spec` using `[h, pow_zero, Module.End.one_apply]`. Conclude with `hw0 hN0spec`. Take `⟨i, hi⟩ : ∃ i, N0 = i + 1` from `⟨N0 - 1, by omega⟩`. Establish `hne0 : (T m ^ i) w ≠ 0` using `Nat.find_min hex (by omega)`. Rewrite using `[Submodule.ne_bot_iff]`.

Use `⟨(T m ^ i) w, ?_, hne0⟩` and prove the remaining obligations. Rewrite using `[hsucc]`. Use `⟨hstpow m m i w hw, ?_⟩` and prove the remaining obligations. Use `show T m ((T m ^ i) w) = 0`. Rewrite using `[← Module.End.mul_apply, ← pow_succ', ← hi, hN0spec]`.

Establish `hfinZ : ∀ m, FiniteDimensional ℂ (Z m)` using `fun m => Submodule.finiteDimensional_of_le (hleS m)`. Set `f : ℕ → ℕ` to `fun m => Module.finrank ℂ (Z m)`. Establish `hexc : ∃ c, ∃ m, f m = c` using `⟨_, 0, rfl⟩`. Take `⟨M, hM⟩` from `Nat.find_spec hexc`. Establish `hmin : ∀ m, Nat.find hexc ≤ f m` using `fun m => Nat.find_min' hexc ⟨m, rfl⟩`.

Take `⟨w, hw, hw0⟩` from `Submodule.ne_bot_iff _ |>.mp (hnebot M)`. Use `⟨w, hleS M hw, hw0, fun k => ?_⟩` and prove the remaining obligations. Break down `lt_or_ge k M with hk | hk` into its components or cases. Conclude with `hkill M k hk w hw`. Establish `hle : Z (k + 1) ≤ Z M` using `hanti (by omega)`.

Establish `heq : Z (k + 1) = Z M` using `by haveI := hfinZ M`. Apply `Submodule.eq_of_le_of_finrank_eq hle` to reduce the goal to its premises. Establish `h1` using `hmin (k + 1)`. Establish `h2 : f (k + 1) ≤ f M` using `Submodule.finrank_mono hle`. Establish `h3 : f M = Nat.find hexc` using `hM`.

Use `show f (k + 1) = f M`. Use linear arithmetic over natural numbers and integers. Conclude with `hkill (k + 1) k (Nat.lt_succ_self k) w (heq ▸ hw)`.
-/
theorem exists_common_null_of_commute_locallyNilpotent :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : ℕ → Module.End ℂ V) (S : Submodule ℂ V),
      FiniteDimensional ℂ S → S ≠ ⊥ → (∀ k, ∀ v ∈ S, T k v ∈ S) →
      (∀ k l, Commute (T k) (T l)) → (∀ k, ∀ v ∈ S, ∃ N : ℕ, (T k ^ N) v = 0) →
      ∃ v ∈ S, v ≠ 0 ∧ ∀ k, T k v = 0 := by
  intro V _ _ T S hfin hne hstab hcomm hnil
  set Z := jointNullChain T S with hZ
  have hsucc : ∀ m, Z (m + 1) = Z m ⊓ LinearMap.ker (T m) := fun m => rfl
  have hanti : Antitone Z := antitone_nat_of_succ_le (fun m => by rw [hsucc]; exact inf_le_left)
  have hleS : ∀ m, Z m ≤ S := fun m => hanti (Nat.zero_le m)
  have hst : ∀ m l, ∀ v ∈ Z m, T l v ∈ Z m := by
    intro m
    induction m with
    | zero => exact fun l v hv => hstab l v hv
    | succ m ih =>
      intro l v hv
      rw [hsucc] at hv ⊢
      refine ⟨ih l v hv.1, ?_⟩
      have h0 : T m v = 0 := hv.2
      show T m (T l v) = 0
      have := LinearMap.congr_fun (hcomm m l).eq v
      simp only [Module.End.mul_apply] at this
      rw [this, h0, map_zero]
  have hstpow : ∀ m l i, ∀ v ∈ Z m, (T l ^ i) v ∈ Z m := by
    intro m l i
    induction i with
    | zero => intro v hv; simpa using hv
    | succ i ih =>
      intro v hv
      rw [pow_succ', Module.End.mul_apply]
      exact hst m l _ (ih v hv)
  have hkill : ∀ m, ∀ k < m, ∀ v ∈ Z m, T k v = 0 := by
    intro m
    induction m with
    | zero => intro k hk; omega
    | succ m ih =>
      intro k hk v hv
      rw [hsucc] at hv
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · exact ih k hk v hv.1
      · subst hk; exact hv.2
  have hnebot : ∀ m, Z m ≠ ⊥ := by
    intro m
    induction m with
    | zero => exact hne
    | succ m ih =>
      obtain ⟨w, hw, hw0⟩ := Submodule.ne_bot_iff _ |>.mp ih
      have hex : ∃ N : ℕ, (T m ^ N) w = 0 := hnil m w (hleS m hw)
      classical
      set N0 := Nat.find hex with hN0
      have hN0spec : (T m ^ N0) w = 0 := Nat.find_spec hex
      have hN0pos : N0 ≠ 0 := by
        intro h
        rw [h, pow_zero, Module.End.one_apply] at hN0spec
        exact hw0 hN0spec
      obtain ⟨i, hi⟩ : ∃ i, N0 = i + 1 := ⟨N0 - 1, by omega⟩
      have hne0 : (T m ^ i) w ≠ 0 := Nat.find_min hex (by omega)
      rw [Submodule.ne_bot_iff]
      refine ⟨(T m ^ i) w, ?_, hne0⟩
      rw [hsucc]
      refine ⟨hstpow m m i w hw, ?_⟩
      show T m ((T m ^ i) w) = 0
      rw [← Module.End.mul_apply, ← pow_succ', ← hi, hN0spec]
  have hfinZ : ∀ m, FiniteDimensional ℂ (Z m) := fun m => Submodule.finiteDimensional_of_le (hleS m)
  let f : ℕ → ℕ := fun m => Module.finrank ℂ (Z m)
  have hexc : ∃ c, ∃ m, f m = c := ⟨_, 0, rfl⟩
  classical
  obtain ⟨M, hM⟩ := Nat.find_spec hexc
  have hmin : ∀ m, Nat.find hexc ≤ f m := fun m => Nat.find_min' hexc ⟨m, rfl⟩
  obtain ⟨w, hw, hw0⟩ := Submodule.ne_bot_iff _ |>.mp (hnebot M)
  refine ⟨w, hleS M hw, hw0, fun k => ?_⟩
  rcases lt_or_ge k M with hk | hk
  · exact hkill M k hk w hw
  · have hle : Z (k + 1) ≤ Z M := hanti (by omega)
    have heq : Z (k + 1) = Z M := by
      haveI := hfinZ M
      apply Submodule.eq_of_le_of_finrank_eq hle
      have h1 := hmin (k + 1)
      have h2 : f (k + 1) ≤ f M := Submodule.finrank_mono hle
      have h3 : f M = Nat.find hexc := hM
      show f (k + 1) = f M
      omega
    exact hkill (k + 1) k (Nat.lt_succ_self k) w (heq ▸ hw)

end GlobalTheory
