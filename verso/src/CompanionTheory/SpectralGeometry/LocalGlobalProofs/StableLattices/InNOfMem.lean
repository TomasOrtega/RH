import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

noncomputable section

namespace GlobalTheory.CompanionTheory.HCdecomp

open Formalism.REAL (GlRel)
open CompanionTheory.D.LK

variable {n : ℕ}

section Mod

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def NV (E : Fin n → Fin n → Module.End ℂ V) : Submodule ℂ V :=
  ⨆ i : Pos n, LinearMap.range (E i.1.1 i.1.2)

/- English proof (translation)
The claim follows from `Submodule.mem_iSup_of_mem (⟨(a, b), h⟩ : Pos n) ⟨w, rfl⟩`.
-/
theorem mem_NV (E : Fin n → Fin n → Module.End ℂ V) {a b : Fin n} (h : a < b) (w : V) :
    E a b w ∈ NV E :=
  Submodule.mem_iSup_of_mem (⟨(a, b), h⟩ : Pos n) ⟨w, rfl⟩

/- English proof (translation)
Use `Submodule.iSup_induction _ (motive := fun y => InN (allT n) E y) hy ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `i _ ⟨w, rfl⟩`. Use `⟨Pi.single i w, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[cpt]`.

Introduce `j _ hj`. Simplify using `[Pi.single_eq_of_ne hj]`. Simplify using the standard rewrite rules. Conclude with `⟨0, by simp⟩`. Introduce and unpack `x y ⟨w, rfl⟩ ⟨w', rfl⟩`.

Use `⟨w + w', ?_⟩` and prove the remaining obligations. Simplify using `[cpt, Finset.sum_add_distrib]`.
-/
theorem inN_of_mem (E : Fin n → Fin n → Module.End ℂ V) {y : V} (hy : y ∈ NV E) :
    InN (allT n) E y := by
  classical
  refine Submodule.iSup_induction _ (motive := fun y => InN (allT n) E y) hy ?_ ?_ ?_
  · rintro i _ ⟨w, rfl⟩
    refine ⟨Pi.single i w, ?_⟩
    rw [Finset.sum_eq_single i]
    · simp [cpt]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  · exact ⟨0, by simp⟩
  · rintro x y ⟨w, rfl⟩ ⟨w', rfl⟩
    refine ⟨w + w', ?_⟩
    simp [cpt, Finset.sum_add_distrib]

def JJ (E : Fin n → Fin n → Module.End ℂ V) : Submodule ℂ (Module.End ℂ V) where
  carrier := {T | ∀ x, T x ∈ NV E}
  add_mem' ha hb x := (NV E).add_mem (ha x) (hb x)
  zero_mem' _ := (NV E).zero_mem
  smul_mem' c _ h x := (NV E).smul_mem c (h x)

/- English proof (translation)
Introduce `x` and use `h (S x)`.
-/
theorem JJ_mul (E : Fin n → Fin n → Module.End ℂ V) {T : Module.End ℂ V} (h : T ∈ JJ E)
    (S : Module.End ℂ V) : T * S ∈ JJ E := fun x => h (S x)

def HH (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ V := ∑ c : Fin n, ((c : ℕ) : ℂ) • E c c

/- English proof (translation)
Establish `h : ∀ c : Fin n, ((c : ℕ) : ℂ) • E c c * E a b - E a b * ((c : ℕ) : ℂ) • E c c = (if c = a then ((a : ℕ) : ℂ) • E a b else 0) - (if c = b then ((b : ℕ) : ℂ) • E a b else 0)`. Introduce `c`. Rewrite using `[smul_mul_assoc, mul_smul_comm, ← smul_sub, hE c c a b, smul_sub]`. Use `congr 1`. Use `split_ifs with h`.

Substitute `h` using the available equality. Both sides reduce to the same expression. Simplify using the standard rewrite rules. Distinguish the cases in `h : b = c`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`. Rewrite using `[HH, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Simplify using `only [h, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_smul]`.
-/
theorem HH_comm {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (a b : Fin n) :
    HH E * E a b - E a b * HH E = (((a : ℕ) : ℂ) - ((b : ℕ) : ℂ)) • E a b := by
  have h : ∀ c : Fin n, ((c : ℕ) : ℂ) • E c c * E a b - E a b * ((c : ℕ) : ℂ) • E c c =
      (if c = a then ((a : ℕ) : ℂ) • E a b else 0) - (if c = b then ((b : ℕ) : ℂ) • E a b else 0) := by
    intro c
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, hE c c a b, smul_sub]
    congr 1
    · split_ifs with h
      · subst h; rfl
      · simp
    · by_cases h : b = c
      · subst h; simp
      · simp [h, Ne.symm h]
  rw [HH, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [h, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_smul]

def adH (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Module.End ℂ V) :=
  LinearMap.mulLeft ℂ (HH E) - LinearMap.mulRight ℂ (HH E)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem adH_apply (E : Fin n → Fin n → Module.End ℂ V) (T : Module.End ℂ V) :
    adH E T = HH E * T - T * HH E := rfl

/- English proof (translation)
Simplify using `only [adH_apply]`. Use `noncomm_ring`.
-/
theorem adH_mul (E : Fin n → Fin n → Module.End ℂ V) (S T : Module.End ℂ V) :
    adH E (S * T) = adH E S * T + S * adH E T := by
  simp only [adH_apply]; noncomm_ring

/- English proof (translation)
Use `Submodule.iSup_induction _ (motive := fun y => HH E y ∈ NV E) hy ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `i _ ⟨w, rfl⟩`. Establish `h` using `LinearMap.congr_fun (HH_comm hE i.1.1 i.1.2) w`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h`. Rewrite using `[sub_eq_iff_eq_add.mp h]`.

Conclude with `(NV E).add_mem ((NV E).smul_mem _ (mem_NV E i.2 _)) (mem_NV E i.2 _)`. Simplify using the standard rewrite rules. Introduce `x y hx hy`. Rewrite using `[map_add]`. Conclude with `(NV E).add_mem hx hy`.
-/
theorem HH_NV {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) {y : V} (hy : y ∈ NV E) :
    HH E y ∈ NV E := by
  refine Submodule.iSup_induction _ (motive := fun y => HH E y ∈ NV E) hy ?_ ?_ ?_
  · rintro i _ ⟨w, rfl⟩
    have h := LinearMap.congr_fun (HH_comm hE i.1.1 i.1.2) w
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
    rw [sub_eq_iff_eq_add.mp h]
    exact (NV E).add_mem ((NV E).smul_mem _ (mem_NV E i.2 _)) (mem_NV E i.2 _)
  · simp
  · intro x y hx hy
    rw [map_add]; exact (NV E).add_mem hx hy

/- English proof (translation)
Introduce `T hT x`. Conclude with `(NV E).sub_mem (HH_NV hE (hT x)) (hT _)`.
-/
theorem adH_JJ {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) :
    JJ E ≤ (JJ E).comap (adH E) := by
  intro T hT x
  exact (NV E).sub_mem (HH_NV hE (hT x)) (hT _)

def PP (E : Fin n → Fin n → Module.End ℂ V) : Submodule ℂ (Module.End ℂ V) :=
  Submodule.span ℂ {T | ∃ k : ℕ, adH E T = ((k : ℂ) + 1) • T}

/- English proof (translation)
Proceed by induction on `hT using Submodule.span_induction with`. Consider the case `mem T h`. Take `⟨k, hk⟩` from `h`. Use `Submodule.subset_span ⟨k + m, ?_⟩` and prove the remaining obligations. Rewrite using `[adH_mul, hk, hS, smul_mul_assoc, mul_smul_comm, ← add_smul]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [add_mul]`.

Conclude with `(PP E).add_mem hx hy`. Consider the case `smul c x _ hx => rw [smul_mul_assoc]`. Conclude with `(PP E).smul_mem c hx`.
-/
theorem congruenceCondition_mul {E : Fin n → Fin n → Module.End ℂ V} {T S : Module.End ℂ V} (hT : T ∈ PP E)
    {m : ℕ} (hS : adH E S = (m : ℂ) • S) : T * S ∈ PP E := by
  induction hT using Submodule.span_induction with
  | mem T h =>
    obtain ⟨k, hk⟩ := h
    refine Submodule.subset_span ⟨k + m, ?_⟩
    rw [adH_mul, hk, hS, smul_mul_assoc, mul_smul_comm, ← add_smul]
    congr 1; push_cast; ring
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact (PP E).add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact (PP E).smul_mem c hx

/- English proof (translation)
Proceed by induction on `b using FreeAlgebra.induction with`. Consider the case `grade0 r`. Rewrite using `[AlgHom.commutes, adH_apply, Algebra.commutes, sub_self]`. Consider the case `grade1 c`. Simplify using `only [evd, FreeAlgebra.lift_ι_apply, adH_apply, HH_comm hE, sub_self, zero_smul]`.

Consider the case `mul a b ha hb => rw [map_mul, adH_mul, ha, hb]`. Simplify using the standard rewrite rules. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]`.
-/
theorem adH_evd {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (b : FreeAlgebra ℂ (Fin n)) :
    adH E (evd (fun c => E c c) b) = 0 := by
  induction b using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes, adH_apply, Algebra.commutes, sub_self]
  | grade1 c =>
    simp only [evd, FreeAlgebra.lift_ι_apply, adH_apply, HH_comm hE, sub_self, zero_smul]
  | mul a b ha hb => rw [map_mul, adH_mul, ha, hb]; simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]

/- English proof (translation)
Use `set D : Module.End ℂ (Module.End ℂ V ⧸ JJ E) := (JJ E).mapQ (JJ E) (adH E) (adH_JJ hE) with hD`. Establish `hd` using `iSupIndep_def.mp (Module.End.eigenspaces_iSupIndep D) 0`. Establish `h1 : (JJ E).mkQ t ∈ D.eigenspace 0`. Rewrite using `[Module.End.mem_eigenspace_iff, zero_smul, hD, Submodule.mkQ_apply, Submodule.mapQ_apply, ht]`. Both sides reduce to the same expression.

Establish `h2 : (JJ E).mkQ p ∈ ⨆ j, ⨆ (_ : j ≠ (0 : ℂ)), D.eigenspace j` using `by clear h`. Proceed by induction on `hp using Submodule.span_induction with`. Consider the case `mem T h`. Take `⟨k, hk⟩` from `h`. Use `Submodule.mem_iSup_of_mem ((k : ℂ) + 1) (Submodule.mem_iSup_of_mem (Nat.cast_add_one_ne_zero k) ?_)` and prove the remaining obligations.

Rewrite using `[Module.End.mem_eigenspace_iff, hD, Submodule.mkQ_apply, Submodule.mapQ_apply, hk]`. Both sides reduce to the same expression. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c hx`. Establish `h3 : (JJ E).mkQ t = (JJ E).mkQ p` using `(Submodule.Quotient.eq _).mpr h`. Rewrite `h2` using `[← h3]`. Use `(Submodule.disjoint_def.mp hd) _ h1 h2` as an intermediate fact.

Conclude with `(Submodule.Quotient.mk_eq_zero _).mp this`.
-/
theorem mem_JJ_of {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) {t p : Module.End ℂ V}
    (ht : adH E t = 0) (hp : p ∈ PP E) (h : t - p ∈ JJ E) : t ∈ JJ E := by
  set D : Module.End ℂ (Module.End ℂ V ⧸ JJ E) := (JJ E).mapQ (JJ E) (adH E) (adH_JJ hE) with hD
  have hd := iSupIndep_def.mp (Module.End.eigenspaces_iSupIndep D) 0
  have h1 : (JJ E).mkQ t ∈ D.eigenspace 0 := by
    rw [Module.End.mem_eigenspace_iff, zero_smul, hD, Submodule.mkQ_apply, Submodule.mapQ_apply, ht]
    rfl
  have h2 : (JJ E).mkQ p ∈ ⨆ j, ⨆ (_ : j ≠ (0 : ℂ)), D.eigenspace j := by
    clear h
    induction hp using Submodule.span_induction with
    | mem T h =>
      obtain ⟨k, hk⟩ := h
      refine Submodule.mem_iSup_of_mem ((k : ℂ) + 1) (Submodule.mem_iSup_of_mem
        (Nat.cast_add_one_ne_zero k) ?_)
      rw [Module.End.mem_eigenspace_iff, hD, Submodule.mkQ_apply, Submodule.mapQ_apply, hk]
      rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have h3 : (JJ E).mkQ t = (JJ E).mkQ p := (Submodule.Quotient.eq _).mpr h
  rw [← h3] at h2
  have := (Submodule.disjoint_def.mp hd) _ h1 h2
  exact (Submodule.Quotient.mk_eq_zero _).mp this

/- English proof (translation)
Simplify using `[ev]`.
-/
theorem ev_ι (E : Fin n → Fin n → Module.End ℂ V) (p : Fin n × Fin n) :
    ev E (FreeAlgebra.ι ℂ p) = E p.1 p.2 := by
  simp [ev]

end Mod

inductive Low : FreeAlgebra ℂ (Fin n × Fin n) → Prop
  | one : Low 1
  | mul (u) (p : Fin n × Fin n) : Low u → p.2 ≤ p.1 → Low (u * FreeAlgebra.ι ℂ p)
  | add (u v) : Low u → Low v → Low (u + v)
  | smul (c : ℂ) (u) : Low u → Low (c • u)

/- English proof (translation)
Simplify using `using Low.smul (0 : ℂ) (1 : FreeAlgebra ℂ (Fin n × Fin n)) Low.one`.
-/
theorem Low.zero : Low (0 : FreeAlgebra ℂ (Fin n × Fin n)) := by
  simpa using Low.smul (0 : ℂ) (1 : FreeAlgebra ℂ (Fin n × Fin n)) Low.one

/- English proof (translation)
Proceed by induction on `hu with`. Consider the case `one => exact ⟨1, fun V _ _ E _ => by simp⟩`. Consider the case `mul u p _ hp ih`. Take `⟨b, hb⟩` from `ih`. Take `⟨i, j⟩` from `p`.

Establish `key : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → adH E (E i j) = (((i : ℕ) - (j : ℕ) : ℕ) : ℂ) • E i j`. Introduce `V _ _ E hE`. Rewrite using `[adH_apply, HH_comm hE, Nat.cast_sub hp]`. Break down `eq_or_lt_of_le hp with h | h` into its components or cases. Simplify using `only at h`.

Substitute `h` using the available equality. Use `⟨b * FreeAlgebra.ι ℂ j, fun V _ _ E hE => ?_⟩` and prove the remaining obligations. Use `congruenceCondition_mul (hb V E hE) (key V E hE)` as an intermediate fact. Rewrite using `[map_mul, map_mul, ev_ι]`. Simplify `this` using `[evd, sub_mul]`.

Use `⟨0, fun V _ _ E hE => ?_⟩` and prove the remaining obligations. Establish `h1` using `congruenceCondition_mul (hb V E hE) (key V E hE)`. Establish `h2 : evd (fun c => E c c) b * E i j ∈ PP E`. Use `Submodule.subset_span ⟨(i : ℕ) - (j : ℕ) - 1, ?_⟩` and prove the remaining obligations. Rewrite using `[adH_mul, adH_evd hE, key V E hE, zero_mul, zero_add, mul_smul_comm]`.

Use `congr 1`. Establish `h' : (j : ℕ) < (i : ℕ)` using `h`. Establish `: (i : ℕ) - (j : ℕ) = (i : ℕ) - (j : ℕ) - 1 + 1` using `by omega`. Conclude with `congrArg (Nat.cast : ℕ → ℂ) this` after adjusting the coercions. Establish `h3` using `(PP E).add_mem h1 h2`.

Rewrite using `[map_mul, ev_ι, map_zero, sub_zero]`. Simplify `h3` using `[sub_mul]`. Consider the case `add u v _ _ hu hv`. Take `⟨b, hb⟩` from `hu`. Take `⟨b', hb'⟩` from `hv`.

Use `⟨b + b', fun V _ _ E hE => ?_⟩` and prove the remaining obligations. Use `(PP E).add_mem (hb V E hE) (hb' V E hE)` as an intermediate fact. Rewrite using `[map_add, map_add]`. Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.

Consider the case `smul c u _ hu`. Take `⟨b, hb⟩` from `hu`. Use `⟨c • b, fun V _ _ E hE => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, ← smul_sub]`. Conclude with `(PP E).smul_mem c (hb V E hE)`.
-/
theorem Low.mul' {u : FreeAlgebra ℂ (Fin n × Fin n)} (hu : Low u) :
    ∃ b : FreeAlgebra ℂ (Fin n), ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ev E u - evd (fun c => E c c) b ∈ PP E := by
  induction hu with
  | one => exact ⟨1, fun V _ _ E _ => by simp⟩
  | mul u p _ hp ih =>
    obtain ⟨b, hb⟩ := ih
    obtain ⟨i, j⟩ := p
    have key : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (E : Fin n → Fin n → Module.End ℂ V), GlRel E →
        adH E (E i j) = (((i : ℕ) - (j : ℕ) : ℕ) : ℂ) • E i j := by
      intro V _ _ E hE
      rw [adH_apply, HH_comm hE, Nat.cast_sub hp]
    rcases eq_or_lt_of_le hp with h | h
    · simp only at h
      subst h
      refine ⟨b * FreeAlgebra.ι ℂ j, fun V _ _ E hE => ?_⟩
      have := congruenceCondition_mul (hb V E hE) (key V E hE)
      rw [map_mul, map_mul, ev_ι]
      simpa [evd, sub_mul] using this
    · refine ⟨0, fun V _ _ E hE => ?_⟩
      have h1 := congruenceCondition_mul (hb V E hE) (key V E hE)
      have h2 : evd (fun c => E c c) b * E i j ∈ PP E := by
        refine Submodule.subset_span ⟨(i : ℕ) - (j : ℕ) - 1, ?_⟩
        rw [adH_mul, adH_evd hE, key V E hE, zero_mul, zero_add, mul_smul_comm]
        congr 1
        have h' : (j : ℕ) < (i : ℕ) := h
        have : (i : ℕ) - (j : ℕ) = (i : ℕ) - (j : ℕ) - 1 + 1 := by omega
        exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) this
      have h3 := (PP E).add_mem h1 h2
      rw [map_mul, ev_ι, map_zero, sub_zero]
      simpa [sub_mul] using h3
  | add u v _ _ hu hv =>
    obtain ⟨b, hb⟩ := hu
    obtain ⟨b', hb'⟩ := hv
    refine ⟨b + b', fun V _ _ E hE => ?_⟩
    have := (PP E).add_mem (hb V E hE) (hb' V E hE)
    rw [map_add, map_add]
    convert this using 1; abel
  | smul c u _ hu =>
    obtain ⟨b, hb⟩ := hu
    refine ⟨c • b, fun V _ _ E hE => ?_⟩
    rw [map_smul, map_smul, ← smul_sub]
    exact (PP E).smul_mem c (hb V E hE)

def Red (a : FreeAlgebra ℂ (Fin n × Fin n)) : Prop :=
  ∃ u, Low u ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ev E a - ev E u ∈ JJ E

/- English proof (translation)
Take `⟨u, hu, h⟩` from `h`. Take `⟨u', hu', h'⟩` from `h'`. Use `⟨u + u', Low.add _ _ hu hu', fun V _ _ E hE => ?_⟩` and prove the remaining obligations. Use `(JJ E).add_mem (h V E hE) (h' V E hE)` as an intermediate fact. Rewrite using `[map_add, map_add]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.
-/
theorem Red.add {a a' : FreeAlgebra ℂ (Fin n × Fin n)} (h : Red a) (h' : Red a') : Red (a + a') := by
  obtain ⟨u, hu, h⟩ := h
  obtain ⟨u', hu', h'⟩ := h'
  refine ⟨u + u', Low.add _ _ hu hu', fun V _ _ E hE => ?_⟩
  have := (JJ E).add_mem (h V E hE) (h' V E hE)
  rw [map_add, map_add]
  convert this using 1; abel

/- English proof (translation)
Take `⟨u, hu, h⟩` from `h`. Use `⟨c • u, Low.smul _ _ hu, fun V _ _ E hE => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, ← smul_sub]`. Conclude with `(JJ E).smul_mem c (h V E hE)`.
-/
theorem Red.smul (c : ℂ) {a : FreeAlgebra ℂ (Fin n × Fin n)} (h : Red a) : Red (c • a) := by
  obtain ⟨u, hu, h⟩ := h
  refine ⟨c • u, Low.smul _ _ hu, fun V _ _ E hE => ?_⟩
  rw [map_smul, map_smul, ← smul_sub]
  exact (JJ E).smul_mem c (h V E hE)

/- English proof (translation)
Assemble the required witnesses or components as `⟨u, hu, fun V _ _ E _ => by simp⟩`.
-/
theorem Red.of_low {u : FreeAlgebra ℂ (Fin n × Fin n)} (hu : Low u) : Red u :=
  ⟨u, hu, fun V _ _ E _ => by simp⟩

/- English proof (translation)
Take `⟨u, hu, h⟩` from `h`. Conclude with `⟨u, hu, fun V _ _ E hE => he V E hE ▸ h V E hE⟩`.
-/
theorem Red.congr {a a' : FreeAlgebra ℂ (Fin n × Fin n)} (h : Red a)
    (he : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ev E a' = ev E a) : Red a' := by
  obtain ⟨u, hu, h⟩ := h
  exact ⟨u, hu, fun V _ _ E hE => he V E hE ▸ h V E hE⟩

/- English proof (translation)
Take `⟨u, hu, h⟩` from `h`. Use `⟨_, Low.mul u p hu hp, fun V _ _ E hE => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, ← sub_mul]`. Conclude with `JJ_mul E (h V E hE) _`.
-/
theorem Red.mul_low {a : FreeAlgebra ℂ (Fin n × Fin n)} (h : Red a) (p : Fin n × Fin n)
    (hp : p.2 ≤ p.1) : Red (a * FreeAlgebra.ι ℂ p) := by
  obtain ⟨u, hu, h⟩ := h
  refine ⟨_, Low.mul u p hu hp, fun V _ _ E hE => ?_⟩
  rw [map_mul, map_mul, ← sub_mul]
  exact JJ_mul E (h V E hE) _

/- English proof (translation)
Proceed by induction on `hu with`. Consider the case `one`. Introduce `p`. Break down `le_or_gt p.2 p.1 with h | h` into its components or cases. Conclude with `Red.of_low (Low.mul _ p Low.one h)`.

Use `⟨0, Low.zero, fun V _ _ E _ => ?_⟩` and prove the remaining obligations. Rewrite using `[one_mul, map_zero, sub_zero, ev_ι]`. Conclude with `fun x => mem_NV E h x`. Consider the case `mul u y _ hy ih`. Introduce `p`.

Establish `h1 : Red (if y.2 = p.1 then u * FreeAlgebra.ι ℂ (y.1, p.2) else 0)` using `by split_ifs`. Conclude with `ih _`. Conclude with `Red.of_low Low.zero`. Establish `h2 : Red (if p.2 = y.1 then u * FreeAlgebra.ι ℂ (p.1, y.2) else 0)` using `by split_ifs`. Conclude with `ih _`.

Conclude with `Red.of_low Low.zero`. Use `((((ih p).mul_low y hy).add h1).add (h2.smul (-1))).congr fun V _ _ E hE => ?_` and prove the remaining obligations. Establish `h` using `sub_eq_iff_eq_add.mp (hE y.1 y.2 p.1 p.2)`. Simplify using `only [map_add, map_mul, ev_ι, map_smul, apply_ite (ev E), map_zero, mul_assoc, h]`. Apply the tactic sequence `split_ifs <;> simp [mul_add, mul_sub] <;> abel`.

Consider the case `add u v _ _ hu hv => intro p`. Rewrite using `[add_mul]`. Conclude with `(hu p).add (hv p)`. Consider the case `smul c u _ hu => intro p`. Rewrite using `[smul_mul_assoc]`.

Conclude with `(hu p).smul c`.
-/
theorem Low.red_mul {u : FreeAlgebra ℂ (Fin n × Fin n)} (hu : Low u) :
    ∀ p : Fin n × Fin n, Red (u * FreeAlgebra.ι ℂ p) := by
  induction hu with
  | one =>
    intro p
    rcases le_or_gt p.2 p.1 with h | h
    · exact Red.of_low (Low.mul _ p Low.one h)
    · refine ⟨0, Low.zero, fun V _ _ E _ => ?_⟩
      rw [one_mul, map_zero, sub_zero, ev_ι]
      exact fun x => mem_NV E h x
  | mul u y _ hy ih =>
    intro p
    have h1 : Red (if y.2 = p.1 then u * FreeAlgebra.ι ℂ (y.1, p.2) else 0) := by
      split_ifs
      · exact ih _
      · exact Red.of_low Low.zero
    have h2 : Red (if p.2 = y.1 then u * FreeAlgebra.ι ℂ (p.1, y.2) else 0) := by
      split_ifs
      · exact ih _
      · exact Red.of_low Low.zero
    refine ((((ih p).mul_low y hy).add h1).add (h2.smul (-1))).congr fun V _ _ E hE => ?_
    have h := sub_eq_iff_eq_add.mp (hE y.1 y.2 p.1 p.2)
    simp only [map_add, map_mul, ev_ι, map_smul, apply_ite (ev E), map_zero, mul_assoc, h]
    split_ifs <;> simp [mul_add, mul_sub] <;> abel
  | add u v _ _ hu hv => intro p; rw [add_mul]; exact (hu p).add (hv p)
  | smul c u _ hu => intro p; rw [smul_mul_assoc]; exact (hu p).smul c

/- English proof (translation)
Take `⟨u, hu, h⟩` from `h`. Take `⟨u', hu', h'⟩` from `hu.red_mul p`. Use `⟨u', hu', fun V _ _ E hE => ?_⟩` and prove the remaining obligations. Use `(JJ E).add_mem (JJ_mul E (h V E hE) (ev E (FreeAlgebra.ι ℂ p))) (h' V E hE)` as an intermediate fact. Rewrite `this`, the goal using `[map_mul]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[sub_mul]`. Normalize the expressions using the abelian group laws.
-/
theorem Red.mul_ι {a : FreeAlgebra ℂ (Fin n × Fin n)} (h : Red a) (p : Fin n × Fin n) :
    Red (a * FreeAlgebra.ι ℂ p) := by
  obtain ⟨u, hu, h⟩ := h
  obtain ⟨u', hu', h'⟩ := hu.red_mul p
  refine ⟨u', hu', fun V _ _ E hE => ?_⟩
  have := (JJ E).add_mem (JJ_mul E (h V E hE) (ev E (FreeAlgebra.ι ℂ p))) (h' V E hE)
  rw [map_mul] at this ⊢
  convert this using 1
  rw [sub_mul]; abel

/- English proof (translation)
Establish `: ∀ z, Red z → Red (z * a)`. Proceed by induction on `a using FreeAlgebra.induction with`. Consider the case `grade0 r`. Introduce `z hz`. Rewrite using `[← Algebra.commutes, ← Algebra.smul_def]`.

Conclude with `hz.smul r`. Consider the case `grade1 p => exact fun z hz => hz.mul_ι p`. Consider the case `mul a b ha hb => intro z hz`. Rewrite using `[← mul_assoc]`. Conclude with `hb _ (ha _ hz)`.

Consider the case `add a b ha hb => intro z hz`. Rewrite using `[mul_add]`. Conclude with `(ha _ hz).add (hb _ hz)`. Simplify using `using this 1 (Red.of_low Low.one)`.
-/
theorem red_all (a : FreeAlgebra ℂ (Fin n × Fin n)) : Red a := by
  have : ∀ z, Red z → Red (z * a) := by
    induction a using FreeAlgebra.induction with
    | grade0 r =>
      intro z hz
      rw [← Algebra.commutes, ← Algebra.smul_def]
      exact hz.smul r
    | grade1 p => exact fun z hz => hz.mul_ι p
    | mul a b ha hb => intro z hz; rw [← mul_assoc]; exact hb _ (ha _ hz)
    | add a b ha hb => intro z hz; rw [mul_add]; exact (ha _ hz).add (hb _ hz)
  simpa using this 1 (Red.of_low Low.one)

/- English proof (translation)
Introduce `n a ha`. Take `⟨u, hu, h⟩` from `red_all a`. Take `⟨b, hb⟩` from `hu.mul'`. Use `⟨b, fun V _ _ E hE x => inN_of_mem E ?_⟩` and prove the remaining obligations. Establish `h0 : adH E (ev E a - evd (fun c => E c c) b) = 0`.

Rewrite using `[map_sub, adH_evd hE, sub_zero, adH_apply, sub_eq_zero]`. Conclude with `(Commute.sum_left _ _ _ fun c _ => (ha V E hE c).smul_left _).eq`. Use `mem_JJ_of hE h0 (hb V E hE) (by simpa using h V E hE)` as an intermediate fact. Conclude with `this x`.
-/
theorem hcdec : CompanionTheory.D.LK.HCdec := by
  intro n a ha
  obtain ⟨u, hu, h⟩ := red_all a
  obtain ⟨b, hb⟩ := hu.mul'
  refine ⟨b, fun V _ _ E hE x => inN_of_mem E ?_⟩
  have h0 : adH E (ev E a - evd (fun c => E c c) b) = 0 := by
    rw [map_sub, adH_evd hE, sub_zero, adH_apply, sub_eq_zero]
    exact (Commute.sum_left _ _ _ fun c _ => (ha V E hE c).smul_left _).eq
  have := mem_JJ_of hE h0 (hb V E hE) (by simpa using h V E hE)
  exact this x

end GlobalTheory.CompanionTheory.HCdecomp
