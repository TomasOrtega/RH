import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction

noncomputable section

namespace GlobalTheory.SpanRing

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

variable {Γ X A : Type} [Group Γ] [CommRing A] {n : ℕ}
  (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A))

def gens : Set (X → Matrix (Fin n) (Fin n) A) :=
  {a | ∃ f ∈ T, ∃ h : Γ, a = fun x => f x • mat (rep x) h}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, f, h, hf, rfl⟩`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.subset_span ⟨f k, hf k, h k, rfl⟩`. Introduce `ha`. Take `⟨m, c, g, rfl⟩` from `Submodule.mem_span_set'.1 ha`.

Use `choose f hf h hh using fun k => (g k).2`. Use `⟨m, fun k => c k • f k, h, fun k => T.smul_mem (hf k) _, ?_⟩` and prove the remaining obligations. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hh k]`. Use function extensionality and compare the values at `x`.

Simplify using `[mul_smul]`.
-/
theorem inRing_iff_mem_span (a : X → Matrix (Fin n) (Fin n) A) :
    InRing T rep a ↔ a ∈ Submodule.span A (gens T rep) := by
  constructor
  · rintro ⟨m, f, h, hf, rfl⟩
    exact Submodule.sum_mem _ fun k _ => Submodule.subset_span ⟨f k, hf k, h k, rfl⟩
  · intro ha
    obtain ⟨m, c, g, rfl⟩ := Submodule.mem_span_set'.1 ha
    choose f hf h hh using fun k => (g k).2
    refine ⟨m, fun k => c k • f k, h, fun k => T.smul_mem (hf k) _, ?_⟩
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hh k]
    funext x
    simp [mul_smul]

def ringR : Subalgebra A (X → Matrix (Fin n) (Fin n) A) :=
  (Submodule.span A (gens T rep)).toSubalgebra
    (Submodule.subset_span ⟨1, T.one_mem, 1, by funext x; simp [mat]⟩) (by
      intro a b ha hb
      have : Submodule.span A (gens T rep) * Submodule.span A (gens T rep) ≤
          Submodule.span A (gens T rep) := by
        rw [Submodule.span_mul_span]
        apply Submodule.span_mono
        rintro _ ⟨_, ⟨f, hf, h, rfl⟩, _, ⟨f', hf', h', rfl⟩, rfl⟩
        refine ⟨f * f', T.mul_mem hf hf', h * h', ?_⟩
        funext x
        simp [mat, mul_smul, smul_comm (f x) (f' x)]
      exact this (Submodule.mul_mem_mul ha hb))

variable {Γ X A : Type} [Group Γ] [CommRing A] {n : ℕ}
  (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) in
/- English proof (translation)
Use `show a ∈ Submodule.span A (_root_.GlobalTheory.SpanRing.gens T rep) ↔ _`. Unfold `_root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing`. Rewrite using `[Submodule.mem_span_set']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, c, g, rfl⟩ choose F hF h hg using fun k => (g k).2`.

Use `⟨m, fun k => c k • F k, h, fun k => T.smul_mem (hF k) (c k), ?_⟩` and prove the remaining obligations. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hg k]`. Use function extensionality and compare the values at `x`. Simplify using `[mul_smul]`.

Introduce and unpack `⟨m, F, h, hF, rfl⟩`. Conclude with `⟨m, fun _ => 1, fun k => ⟨_, F k, hF k, h k, rfl⟩, by simp⟩`.
-/
theorem _root_.GlobalTheory.SpanRing.mem_ringR (a : X → Matrix (Fin n) (Fin n) A) :
    a ∈ _root_.GlobalTheory.SpanRing.ringR T rep ↔ _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep a := by
  show a ∈ Submodule.span A (_root_.GlobalTheory.SpanRing.gens T rep) ↔ _
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing
  rw [Submodule.mem_span_set']
  constructor
  · rintro ⟨m, c, g, rfl⟩
    choose F hF h hg using fun k => (g k).2
    refine ⟨m, fun k => c k • F k, h, fun k => T.smul_mem (hF k) (c k), ?_⟩
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hg k]
    funext x
    simp [mul_smul]
  · rintro ⟨m, F, h, hF, rfl⟩
    exact ⟨m, fun _ => 1, fun k => ⟨_, F k, hF k, h k, rfl⟩, by simp⟩

variable {T rep}

variable {Γ X A : Type} [Group Γ] [CommRing A] {n : ℕ}
  (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) in
variable {T rep} in
/- English proof (translation)
The claim follows from `(_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1 (_root_.GlobalTheory.SpanRing.ringR T rep).one_mem`.
-/
theorem _root_.GlobalTheory.SpanRing.inRing_one : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep 1 :=
  (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1 (_root_.GlobalTheory.SpanRing.ringR T rep).one_mem

variable {Γ X A : Type} [Group Γ] [CommRing A] {n : ℕ}
  (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) in
variable {T rep} in
/- English proof (translation)
The claim follows from `(_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1 (add_mem ((_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 ha) ((_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 hb))`.
-/
theorem _root_.GlobalTheory.SpanRing.inRing_add {a b : X → Matrix (Fin n) (Fin n) A}
    (ha : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep a) (hb : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep b) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep (a + b) :=
  (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1
    (add_mem ((_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 ha)
      ((_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 hb))

variable {Γ X A : Type} [Group Γ] [CommRing A] {n : ℕ}
  (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) in
variable {T rep} in
/- English proof (translation)
The claim follows from `(_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1 (sub_mem ((_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 ha) ((_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 hb))`.
-/
theorem _root_.GlobalTheory.SpanRing.inRing_sub {a b : X → Matrix (Fin n) (Fin n) A}
    (ha : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep a) (hb : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep b) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep (a - b) :=
  (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1
    (sub_mem ((_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 ha)
      ((_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 hb))

variable {Γ X A : Type} [Group Γ] [CommRing A] {n : ℕ}
  (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) in
variable {T rep} in
/- English proof (translation)
The claim follows from `(_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1 (mul_mem ((_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 ha) ((_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 hb))`.
-/
theorem _root_.GlobalTheory.SpanRing.inRing_mul {a b : X → Matrix (Fin n) (Fin n) A}
    (ha : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep a) (hb : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep b) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep (a * b) :=
  (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1
    (mul_mem ((_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 ha)
      ((_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 hb))

variable {Γ X A : Type} [Group Γ] [CommRing A] {n : ℕ}
  (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) in
variable {T rep} in
/- English proof (translation)
The claim follows from `(_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1 (Subalgebra.smul_mem _ ((_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 ha) c)`.
-/
theorem _root_.GlobalTheory.SpanRing.inRing_smul (c : A) {a : X → Matrix (Fin n) (Fin n) A}
    (ha : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep a) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep (c • a) :=
  (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1
    (Subalgebra.smul_mem _ ((_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 ha) c)

variable {Γ X A : Type} [Group Γ] [CommRing A] {n : ℕ}
  (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) in
variable {T rep} in
/- English proof (translation)
The claim follows from `(_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1 (Subalgebra.sum_mem _ fun k hk => (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 (ha k hk))`.
-/
theorem _root_.GlobalTheory.SpanRing.inRing_sum {ι : Type} (s : Finset ι)
    {a : ι → X → Matrix (Fin n) (Fin n) A}
    (ha : ∀ k ∈ s, _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep (a k)) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep (∑ k ∈ s, a k) :=
  (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1
    (Subalgebra.sum_mem _ fun k hk =>
      (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).2 (ha k hk))

variable {Γ X A : Type} [Group Γ] [CommRing A] {n : ℕ}
  (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) in
variable {T rep} in
/- English proof (translation)
The claim follows from `(_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1 (Submodule.subset_span ⟨1, T.one_mem, h, by funext x; simp⟩)`.
-/
theorem _root_.GlobalTheory.SpanRing.inRing_mat (h : Γ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep (fun x => _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (rep x) h) :=
  (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1
    (Submodule.subset_span ⟨1, T.one_mem, h, by funext x; simp⟩)

variable {Γ X A : Type} [Group Γ] [CommRing A] {n : ℕ}
  (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) in
variable {T rep} in

/- English proof (translation)
Take `⟨m, f, h, hf, rfl⟩` from `ha`. Simplify using `only [Finset.sum_apply]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨h k, rfl⟩)`.
-/
theorem _root_.GlobalTheory.SpanRing.eval_mem_span {a : X → Matrix (Fin n) (Fin n) A}
    (ha : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep a) (x : X) :
    a x ∈ Submodule.span A (Set.range (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (rep x))) := by
  obtain ⟨m, f, h, hf, rfl⟩ := ha
  simp only [Finset.sum_apply]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨h k, rfl⟩)

variable {Γ X A : Type} [Group Γ] [CommRing A] {n : ℕ}
  (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) in
variable {T rep} in

/- English proof (translation)
Proceed by induction on `hM using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨g, rfl⟩` from `hy`. Conclude with `⟨_, _root_.GlobalTheory.SpanRing.inRing_mat g, rfl⟩`. Consider the case `zero`.

Conclude with `⟨0, (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1 (_root_.GlobalTheory.SpanRing.ringR T rep).zero_mem, rfl⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨a, ha, hax⟩` from `hy`. Take `⟨b, hb, hbx⟩` from `hz`. Conclude with `⟨a + b, _root_.GlobalTheory.SpanRing.inRing_add ha hb, by simp [hax, hbx]⟩`.

Consider the case `smul c y _ hy`. Take `⟨a, ha, hax⟩` from `hy`. Conclude with `⟨c • a, _root_.GlobalTheory.SpanRing.inRing_smul c ha, by simp [hax]⟩`.
-/
theorem _root_.GlobalTheory.SpanRing.exists_inRing_eval (x : X) {M : Matrix (Fin n) (Fin n) A}
    (hM : M ∈ Submodule.span A (Set.range (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (rep x)))) :
    ∃ a, _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep a ∧ a x = M := by
  induction hM using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, rfl⟩ := hy
    exact ⟨_, _root_.GlobalTheory.SpanRing.inRing_mat g, rfl⟩
  | zero =>
    exact ⟨0, (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1
      (_root_.GlobalTheory.SpanRing.ringR T rep).zero_mem, rfl⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hax⟩ := hy
    obtain ⟨b, hb, hbx⟩ := hz
    exact ⟨a + b, _root_.GlobalTheory.SpanRing.inRing_add ha hb, by simp [hax, hbx]⟩
  | smul c y _ hy =>
    obtain ⟨a, ha, hax⟩ := hy
    exact ⟨c • a, _root_.GlobalTheory.SpanRing.inRing_smul c ha, by simp [hax]⟩

variable (T rep)

def spanRingCornerIdealModule (π : X) (e : X → Matrix (Fin n) (Fin n) A) : Submodule A (X → Matrix (Fin n) (Fin n) A) :=
  Submodule.span A {s | ∃ j ∈ T, j π = 0 ∧ ∃ a, InRing T rep a ∧ s = fun x => j x • (e x * a x * e x)}

variable {Γ X A : Type} [Group Γ] [CommRing A] {n : ℕ}
  (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) in
variable {T rep} in
variable (T rep) in
/- English proof (translation)
Unfold `_root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InMatrixCongruenceModule`. Rewrite using `[_root_.GlobalTheory.SpanRing.spanRingCornerIdealModule, Submodule.mem_span_set']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, c, g, rfl⟩ choose J hJ hJπ a ha hg using fun k => (g k).2`. Use `⟨m, fun k => c k • J k, a, fun k => ⟨T.smul_mem (hJ k) (c k), by simp [hJπ k], ha k⟩, ?_⟩` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hg k]`. Use function extensionality and compare the values at `x`. Simplify using `[mul_smul]`. Introduce and unpack `⟨m, J, a, h, rfl⟩`.

Conclude with `⟨m, fun _ => 1, fun k => ⟨_, J k, (h k).1, (h k).2.1, a k, (h k).2.2, rfl⟩, by simp⟩`.
-/
theorem _root_.GlobalTheory.SpanRing.mem_spanRingCornerIdealModule_iff (π : X) (e s : X → Matrix (Fin n) (Fin n) A) :
    s ∈ _root_.GlobalTheory.SpanRing.spanRingCornerIdealModule T rep π e ↔ _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InMatrixCongruenceModule T rep π e s := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InMatrixCongruenceModule
  rw [_root_.GlobalTheory.SpanRing.spanRingCornerIdealModule, Submodule.mem_span_set']
  constructor
  · rintro ⟨m, c, g, rfl⟩
    choose J hJ hJπ a ha hg using fun k => (g k).2
    refine ⟨m, fun k => c k • J k, a,
      fun k => ⟨T.smul_mem (hJ k) (c k), by simp [hJπ k], ha k⟩, ?_⟩
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hg k]
    funext x
    simp [mul_smul]
  · rintro ⟨m, J, a, h, rfl⟩
    exact ⟨m, fun _ => 1,
      fun k => ⟨_, J k, (h k).1, (h k).2.1, a k, (h k).2.2, rfl⟩, by simp⟩

variable {T rep}

variable {Γ X A : Type} [Group Γ] [CommRing A] {n : ℕ}
  (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) in
variable {T rep} in
variable (T rep) in
variable {T rep} in
/- English proof (translation)
Take `⟨m, j, a, h, rfl⟩` from `hs`. Simplify using `only [Finset.sum_apply]`. Conclude with `Finset.sum_eq_zero fun k _ => by simp [(h k).2.1]`.
-/
theorem _root_.GlobalTheory.SpanRing.InMatrixCongruenceModule.eval_eq_zero {π : X}
    {e s : X → Matrix (Fin n) (Fin n) A} (hs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InMatrixCongruenceModule T rep π e s) :
    s π = 0 := by
  obtain ⟨m, j, a, h, rfl⟩ := hs
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero fun k _ => by simp [(h k).2.1]

variable {Γ X A : Type} [Group Γ] [CommRing A] {n : ℕ}
  (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) in
variable {T rep} in
/- English proof (translation)
Establish `h1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep (fun x => f x • _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (rep x) 1)` using `(_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1 (Submodule.subset_span ⟨f, hf, 1, rfl⟩)`. Use `_root_.GlobalTheory.SpanRing.inRing_mul h1 hb using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Simplify using `[_root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat, smul_mul_assoc]`.
-/
private theorem inRing_pointwise_smul_of_mem {f : X → A} (hf : f ∈ T)
    {b : X → Matrix (Fin n) (Fin n) A} (hb : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep b) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep (fun x => f x • b x) := by
  have h1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep
      (fun x => f x • _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (rep x) 1) :=
    (_root_.GlobalTheory.SpanRing.mem_ringR T rep _).1
      (Submodule.subset_span ⟨f, hf, 1, rfl⟩)
  convert _root_.GlobalTheory.SpanRing.inRing_mul h1 hb using 1
  funext x
  simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat, smul_mul_assoc]

variable {Γ X A : Type} [Group Γ] [CommRing A] {n : ℕ}
  (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) in
variable {T rep} in
variable (T rep) in
variable {T rep} in
/- English proof (translation)
Take `⟨m, j, a, h, rfl⟩` from `hs`. Use `_root_.GlobalTheory.SpanRing.inRing_sum Finset.univ fun k _ => ?_` and prove the remaining obligations. Conclude with `inRing_pointwise_smul_of_mem (h k).1 (_root_.GlobalTheory.SpanRing.inRing_mul (_root_.GlobalTheory.SpanRing.inRing_mul he (h k).2.2) he)`.
-/
theorem _root_.GlobalTheory.SpanRing.InMatrixCongruenceModule.inRing {π : X}
    {e s : X → Matrix (Fin n) (Fin n) A} (he : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep e)
    (hs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InMatrixCongruenceModule T rep π e s) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InRing T rep s := by
  obtain ⟨m, j, a, h, rfl⟩ := hs
  refine _root_.GlobalTheory.SpanRing.inRing_sum Finset.univ fun k _ => ?_
  exact inRing_pointwise_smul_of_mem (h k).1
    (_root_.GlobalTheory.SpanRing.inRing_mul (_root_.GlobalTheory.SpanRing.inRing_mul he (h k).2.2) he)

variable {Γ X A : Type} [Group Γ] [CommRing A] {n : ℕ}
  (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) in
variable {T rep} in
variable (T rep) in
variable {T rep} in
/- English proof (translation)
Establish `hex : e x * e x = e x` using `congrFun he x`. Take `⟨m, j, a, h, rfl⟩` from `hs`. Simplify using `only [Finset.sum_apply]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [mul_smul_comm, ← mul_assoc, hex]`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [smul_mul_assoc, mul_assoc, hex]`.
-/
theorem _root_.GlobalTheory.SpanRing.InMatrixCongruenceModule.corner {π : X}
    {e s : X → Matrix (Fin n) (Fin n) A} (he : e * e = e)
    (hs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.InMatrixCongruenceModule T rep π e s) (x : X) :
    e x * s x = s x ∧ s x * e x = s x := by
  have hex : e x * e x = e x := congrFun he x
  obtain ⟨m, j, a, h, rfl⟩ := hs
  simp only [Finset.sum_apply]
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [mul_smul_comm, ← mul_assoc, hex]
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [smul_mul_assoc, mul_assoc, hex]

end GlobalTheory.SpanRing

end
