import Formalism.LocalToGlobal.KernelLattices.KerStd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK

noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.KS

open Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker
open Formalism.L2.AlgTh (lamF flat vecE)
open Formalism.L2.Th1.GD (InMul)

variable {D : D7} {X : Fields} (s : Seam D X)

section Maps

variable {a b : ℕ}

def mat (x : HomE X.E a b) : Matrix (Fin b) (Fin a) D.host.E := fun i j => s.iE (x (Pi.single j 1) i)

def unmat (A : Matrix (Fin b) (Fin a) D.host.E) : HomE X.E a b := Matrix.toLin' (A.map s.iE.symm)

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Simplify using `[mat, unmat, Matrix.toLin'_apply]`.
-/
theorem mat_unmat (A : Matrix (Fin b) (Fin a) D.host.E) : mat s (unmat s A) = A := by
  funext i j
  simp [mat, unmat, Matrix.toLin'_apply]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `h : x y = ∑ j, y j • x (Pi.single j 1)` using `by conv_lhs => rw [← Finset.univ_sum_single y]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← map_smul]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hk]`. Use `show ∑ j, s.iE (x (Pi.single j 1) i) * s.iE (y j) = s.iE (x y i)`. Rewrite using `[h, Finset.sum_apply, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, map_mul, mul_comm]`.
-/
theorem mat_mulVec (x : HomE X.E a b) (y : Sp X.E a) : (mat s x).mulVec (s.vec y) = s.vec (x y) := by
  funext i
  have h : x y = ∑ j, y j • x (Pi.single j 1) := by
    conv_lhs => rw [← Finset.univ_sum_single y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_smul]
    congr 1
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  show ∑ j, s.iE (x (Pi.single j 1) i) * s.iE (y j) = s.iE (x y i)
  rw [h, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_comm]

def phi (δ : ℂ) : HomE X.E a b →+ TaylorLogMetric.VC D a b where
  toFun x := fun τ i j => δ * TaylorLogMetric.embT D τ (s.iE (x (Pi.single j 1) i))
  map_zero' := by funext τ i j; simp
  map_add' x y := by funext τ i j; simp [mul_add]

def opM (e : D.host.E) : TaylorLogMetric.VC D a b →+ TaylorLogMetric.VC D a b where
  toFun v := fun τ i j => TaylorLogMetric.embT D τ e * v τ i j
  map_zero' := by funext τ i j; simp
  map_add' x y := by funext τ i j; simp [mul_add]

def emV : Matrix (Fin b) (Fin a) D.host.E →+ TaylorLogMetric.VC D a b where
  toFun A := fun τ i j => TaylorLogMetric.embT D τ (A i j)
  map_zero' := by funext τ i j; simp
  map_add' x y := by funext τ i j; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem embV_eq (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (A : Matrix (Fin b) (Fin a) D.host.E) :
    TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) A = emV A := rfl

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Use `show TaylorLogMetric.embT D τ e * (w * v τ i j) = w * (TaylorLogMetric.embT D τ e * v τ i j)`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem opM_smul (e : D.host.E) (w : ℂ) (v : TaylorLogMetric.VC D a b) : opM e (w • v) = w • opM e v := by
  funext τ i j
  show TaylorLogMetric.embT D τ e * (w * v τ i j) = w * (TaylorLogMetric.embT D τ e * v τ i j)
  ring

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Use `show TaylorLogMetric.embT D τ (e * A i j) = _`. Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem emV_smulE (e : D.host.E) (A : Matrix (Fin b) (Fin a) D.host.E) : emV (e • A) = opM e (emV A) := by
  funext τ i j
  show TaylorLogMetric.embT D τ (e * A i j) = _
  rw [map_mul]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Use `show TaylorLogMetric.embT D τ (r • A i j) = _`. Rewrite using `[Algebra.smul_def, map_mul]`. Both sides reduce to the same expression.
-/
theorem emV_smulO (r : 𝓞 D.host.E) (A : Matrix (Fin b) (Fin a) D.host.E) : emV (r • A) = opM (r : D.host.E) (emV A) := by
  funext τ i j
  show TaylorLogMetric.embT D τ (r • A i j) = _
  rw [Algebra.smul_def, map_mul]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Use `show δ * TaylorLogMetric.embT D τ (s.iE (e * x (Pi.single j 1) i)) = TaylorLogMetric.embT D τ (s.iE e) * (δ * _)`. Rewrite using `[map_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem phi_smulE (δ : ℂ) (e : X.E) (x : HomE X.E a b) : phi s δ (e • x) = opM (s.iE e) (phi s δ x) := by
  funext τ i j
  show δ * TaylorLogMetric.embT D τ (s.iE (e * x (Pi.single j 1) i)) = TaylorLogMetric.embT D τ (s.iE e) * (δ * _)
  rw [map_mul, map_mul]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Use `show δ * TaylorLogMetric.embT D τ (s.iE (r • x (Pi.single j 1) i)) = TaylorLogMetric.embT D τ (s.iE (r : X.E)) * (δ * _)`. Rewrite using `[Algebra.smul_def, map_mul, map_mul]`. Use `show δ * (TaylorLogMetric.embT D τ (s.iE (r : X.E)) * _) = _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem phi_smulO (δ : ℂ) (r : 𝓞 X.E) (x : HomE X.E a b) : phi s δ (r • x) = opM (s.iE (r : X.E)) (phi s δ x) := by
  funext τ i j
  show δ * TaylorLogMetric.embT D τ (s.iE (r • x (Pi.single j 1) i)) = TaylorLogMetric.embT D τ (s.iE (r : X.E)) * (δ * _)
  rw [Algebra.smul_def, map_mul, map_mul]
  show δ * (TaylorLogMetric.embT D τ (s.iE (r : X.E)) * _) = _
  ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem phi_eq (δ : ℂ) (x : HomE X.E a b) : phi s δ x = δ • emV (mat s x) := rfl

end Maps

section Per

variable {a b : ℕ} (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))

def aaX : Submodule (𝓞 X.E) X.E :=
  Submodule.span (𝓞 X.E) {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0, r = s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t)}

/- English proof (translation)
Proceed by induction on `hv using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨w, hw, A, hA, rfl⟩` from `hx`. Use `AddSubgroup.subset_closure ⟨w, hw, r • A, Submodule.smul_mem _ _ hA, ?_⟩` and prove the remaining obligations. Rewrite using `[embV_eq, embV_eq, opM_smul, emV_smulO]`.

Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ h1 h2 => rw [map_add]`. Conclude with `add_mem h1 h2`. Consider the case `neg x _ h => rw [map_neg]`.

Conclude with `neg_mem h`.
-/
theorem La_stable (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (r : 𝓞 D.host.E) {v : TaylorLogMetric.VC D a b} (hv : v ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L') :
    opM (r : D.host.E) v ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L' := by
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨w, hw, r • A, Submodule.smul_mem _ _ hA, ?_⟩
    rw [embV_eq, embV_eq, opM_smul, emV_smulO]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | neg x _ h => rw [map_neg]; exact neg_mem h

/- English proof (translation)
Use `Submodule.subset_span ?_` and prove the remaining obligations. Introduce `y hy`. Take `⟨y₀, hy₀, rfl⟩` from `(s.mem_lat N y).1 hy`. Rewrite using `[mat_mulVec]`. Conclude with `(s.mem_lat N' _).2 ⟨x y₀, hx y₀ hy₀, rfl⟩`.
-/
theorem mat_mem_hom {x : HomE X.E a b} (hx : x ∈ homO N N') : mat s x ∈ TaylorLogMetric.homL D (s.lat N) (s.lat N') := by
  refine Submodule.subset_span ?_
  intro y hy
  obtain ⟨y₀, hy₀, rfl⟩ := (s.mem_lat N y).1 hy
  rw [mat_mulVec]
  exact (s.mem_lat N' _).2 ⟨x y₀, hx y₀ hy₀, rfl⟩

/- English proof (translation)
Introduce `y hy`. Establish `h1` using `hA (s.vec y) ((s.mem_lat N _).2 ⟨y, hy, rfl⟩)`. Rewrite `h1` using `[← mat_unmat s A, mat_mulVec]`. Take `⟨z, hz, hzz⟩` from `(s.mem_lat N' _).1 h1`. Establish `: z = unmat s A y`.

Use function extensionality and compare the values at `i`. Conclude with `s.iE.injective (congrFun hzz i)`. Rewrite using `[← this]`. Conclude with `hz`.
-/
theorem unmat_mem_hom {A : Matrix (Fin b) (Fin a) D.host.E} (hA : ∀ x ∈ s.lat N, A.mulVec x ∈ s.lat N') : unmat s A ∈ homO N N' := by
  intro y hy
  have h1 := hA (s.vec y) ((s.mem_lat N _).2 ⟨y, hy, rfl⟩)
  rw [← mat_unmat s A, mat_mulVec] at h1
  obtain ⟨z, hz, hzz⟩ := (s.mem_lat N' _).1 h1
  have : z = unmat s A y := by
    funext i
    exact s.iE.injective (congrFun hzz i)
  rw [← this]
  exact hz

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Use `show δ * TaylorLogMetric.embT D τ (s.iE (s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t) * x (Pi.single j 1) i)) = (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) * TaylorLogMetric.embT D τ (t * s.iE (x (Pi.single j 1) i))`. Rewrite using `[map_mul, RingEquiv.apply_symm_apply, map_mul, map_mul, map_mul]`. Establish `h` using `embOnK D τ (c : D.host.K)`. Establish `h' : TaylorLogMetric.embT D τ (((c : D.host.K) : D.host.E)) = D.host.φ₀ (((c : D.host.K) : D.host.E))` using `h`.

Rewrite using `[h']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gen_eq (c : 𝓞 D.host.K) (t : D.host.E) (x : HomE X.E a b) :
    phi s δ (s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t) • x) =
      (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) • emV (t • mat s x) := by
  funext τ i j
  show δ * TaylorLogMetric.embT D τ (s.iE (s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t) * x (Pi.single j 1) i)) =
    (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) * TaylorLogMetric.embT D τ (t * s.iE (x (Pi.single j 1) i))
  rw [map_mul, RingEquiv.apply_symm_apply, map_mul, map_mul, map_mul]
  have h := embOnK D τ (c : D.host.K)
  have h' : TaylorLogMetric.embT D τ (((c : D.host.K) : D.host.E)) = D.host.φ₀ (((c : D.host.K) : D.host.E)) := h
  rw [h']
  ring

/- English proof (translation)
Establish `key : ∀ r ∈ aaX s cc, ∀ x ∈ homO N N', phi s δ (r • x) ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N')`. Introduce `r hr`. Proceed by induction on `hr using Submodule.span_induction with`. Consider the case `mem r h`. Take `⟨c, hc, t, ht, rfl⟩` from `h`.

Introduce `x hx`. Rewrite using `[gen_eq]`. Conclude with `AddSubgroup.subset_closure ⟨_, AddSubgroup.subset_closure ⟨c, hc, rfl⟩, t • mat s x, Submodule.subset_span ⟨t, ht, mat s x, mat_mem_hom s N N' hx, rfl⟩, rfl⟩`. Consider the case `zero => intro x _`. Rewrite using `[zero_smul, map_zero]`.

Conclude with `zero_mem _`. Consider the case `add r r' _ _ h1 h2 => intro x hx`. Rewrite using `[add_smul, map_add]`. Conclude with `add_mem (h1 x hx) (h2 x hx)`. Consider the case `smul ρ r _ h`.

Introduce `x hx`. Take `⟨ρ', hρ'⟩` from `(s.int_iff (ρ : X.E)).2 ⟨ρ, rfl⟩`. Rewrite using `[smul_assoc, phi_smulO, ← hρ']`. Conclude with `La_stable cc δ _ _ ρ' (h x hx)`. Proceed by induction on `hz using Submodule.span_induction with`.

Consider the case `mem z h`. Take `⟨r, hr, x, hx, rfl⟩` from `h`. Conclude with `key r hr x hx`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ h1 h2 => rw [map_add]`. Conclude with `add_mem h1 h2`. Consider the case `smul ρ z _ h`. Take `⟨ρ', hρ'⟩` from `(s.int_iff (ρ : X.E)).2 ⟨ρ, rfl⟩`. Rewrite using `[phi_smulO, ← hρ']`.

Conclude with `La_stable cc δ _ _ ρ' h`.
-/
theorem phi_mem_La {z : HomE X.E a b} (hz : z ∈ perO (aaX s cc) N N') :
    phi s δ z ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') := by
  have key : ∀ r ∈ aaX s cc, ∀ x ∈ homO N N', phi s δ (r • x) ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem r h =>
      obtain ⟨c, hc, t, ht, rfl⟩ := h
      intro x hx
      rw [gen_eq]
      exact AddSubgroup.subset_closure ⟨_, AddSubgroup.subset_closure ⟨c, hc, rfl⟩, t • mat s x,
        Submodule.subset_span ⟨t, ht, mat s x, mat_mem_hom s N N' hx, rfl⟩, rfl⟩
    | zero => intro x _; rw [zero_smul, map_zero]; exact zero_mem _
    | add r r' _ _ h1 h2 => intro x hx; rw [add_smul, map_add]; exact add_mem (h1 x hx) (h2 x hx)
    | smul ρ r _ h =>
      intro x hx
      obtain ⟨ρ', hρ'⟩ := (s.int_iff (ρ : X.E)).2 ⟨ρ, rfl⟩
      rw [smul_assoc, phi_smulO, ← hρ']
      exact La_stable cc δ _ _ ρ' (h x hx)
  induction hz using Submodule.span_induction with
  | mem z h =>
    obtain ⟨r, hr, x, hx, rfl⟩ := h
    exact key r hr x hx
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | smul ρ z _ h =>
    obtain ⟨ρ', hρ'⟩ := (s.int_iff (ρ : X.E)).2 ⟨ρ, rfl⟩
    rw [phi_smulO, ← hρ']
    exact La_stable cc δ _ _ ρ' h

def imS : AddSubgroup (TaylorLogMetric.VC D a b) := (perO (aaX s cc) N N').toAddSubgroup.map (phi s δ)

/- English proof (translation)
Take `⟨z, hz, rfl⟩` from `hv`. Take `⟨ρ, hρ⟩` from `(s.int_iff (s.iE.symm (r : D.host.E))).1 ⟨r, by simp⟩`. Use `⟨ρ • z, Submodule.smul_mem _ _ hz, ?_⟩` and prove the remaining obligations. Rewrite using `[phi_smulO]`. Establish `: s.iE ((ρ : 𝓞 X.E) : X.E) = (r : D.host.E)`.

Establish `h2 : ((ρ : 𝓞 X.E) : X.E) = s.iE.symm (r : D.host.E)` using `hρ`. Rewrite using `[h2, RingEquiv.apply_symm_apply]`. Rewrite using `[this]`.
-/
theorem imS_stable (r : 𝓞 D.host.E) {v : TaylorLogMetric.VC D a b} (hv : v ∈ imS s cc δ N N') : opM (r : D.host.E) v ∈ imS s cc δ N N' := by
  obtain ⟨z, hz, rfl⟩ := hv
  obtain ⟨ρ, hρ⟩ := (s.int_iff (s.iE.symm (r : D.host.E))).1 ⟨r, by simp⟩
  refine ⟨ρ • z, Submodule.smul_mem _ _ hz, ?_⟩
  rw [phi_smulO]
  have : s.iE ((ρ : 𝓞 X.E) : X.E) = (r : D.host.E) := by
    have h2 : ((ρ : 𝓞 X.E) : X.E) = s.iE.symm (r : D.host.E) := hρ
    rw [h2, RingEquiv.apply_symm_apply]
  rw [this]

/- English proof (translation)
Establish `key4 : ∀ c ∈ cc, ∀ t ∈ D.host.AA0, ∀ A ∈ TaylorLogMetric.homL D (s.lat N) (s.lat N'), (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) • emV (t • A) ∈ imS s cc δ N N'`. Introduce `c hc t ht A hA`. Proceed by induction on `hA using Submodule.span_induction with`. Consider the case `mem A h`. Use `⟨s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t) • unmat s A, Submodule.subset_span ⟨_, Submodule.subset_span ⟨c, hc, t, ht, rfl⟩, unmat s A, unmat_mem_hom s N N' h, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[gen_eq, mat_unmat]`. Consider the case `zero => rw [smul_zero, map_zero, smul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ h1 h2 => rw [smul_add, map_add, smul_add]`. Conclude with `add_mem h1 h2`.

Consider the case `smul ρ A _ h`. Rewrite using `[smul_comm, emV_smulO, ← opM_smul]`. Conclude with `imS_stable s cc δ N N' ρ h`. Establish `key3 : ∀ c ∈ cc, ∀ A ∈ TaylorLogMetric.YYl D (s.lat N) (s.lat N'), (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) • emV A ∈ imS s cc δ N N'`. Introduce `c hc A hA`.

Proceed by induction on `hA using Submodule.span_induction with`. Consider the case `mem A h`. Take `⟨t, ht, A₀, hA₀, rfl⟩` from `h`. Conclude with `key4 c hc t ht A₀ hA₀`. Consider the case `zero => rw [map_zero, smul_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ h1 h2 => rw [map_add, smul_add]`. Conclude with `add_mem h1 h2`. Consider the case `smul ρ A _ h`. Rewrite using `[emV_smulO, ← opM_smul]`.

Conclude with `imS_stable s cc δ N N' ρ h`. Establish `key2 : ∀ w ∈ TaylorLogMetric.lamOf D cc δ, ∀ A ∈ TaylorLogMetric.YYl D (s.lat N) (s.lat N'), w • emV A ∈ imS s cc δ N N'`. Introduce `w hw`. Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem w h`.

Take `⟨c, hc, rfl⟩` from `h`. Conclude with `key3 c hc`. Consider the case `zero => intro A _`. Rewrite using `[zero_smul]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ h1 h2 => intro A hA`. Rewrite using `[add_smul]`. Conclude with `add_mem (h1 A hA) (h2 A hA)`. Consider the case `neg x _ h => intro A hA`. Rewrite using `[neg_smul]`.

Conclude with `neg_mem (h A hA)`. Unfold `TaylorLogMetric.La`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨w, hw, A, hA, rfl⟩`. Conclude with `key2 w hw A hA`.
-/
theorem La_le : TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') ≤ imS s cc δ N N' := by
  have key4 : ∀ c ∈ cc, ∀ t ∈ D.host.AA0, ∀ A ∈ TaylorLogMetric.homL D (s.lat N) (s.lat N'),
      (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) • emV (t • A) ∈ imS s cc δ N N' := by
    intro c hc t ht A hA
    induction hA using Submodule.span_induction with
    | mem A h =>
      refine ⟨s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t) • unmat s A,
        Submodule.subset_span ⟨_, Submodule.subset_span ⟨c, hc, t, ht, rfl⟩, unmat s A, unmat_mem_hom s N N' h, rfl⟩, ?_⟩
      rw [gen_eq, mat_unmat]
    | zero => rw [smul_zero, map_zero, smul_zero]; exact zero_mem _
    | add x y _ _ h1 h2 => rw [smul_add, map_add, smul_add]; exact add_mem h1 h2
    | smul ρ A _ h =>
      rw [smul_comm, emV_smulO, ← opM_smul]
      exact imS_stable s cc δ N N' ρ h
  have key3 : ∀ c ∈ cc, ∀ A ∈ TaylorLogMetric.YYl D (s.lat N) (s.lat N'),
      (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) • emV A ∈ imS s cc δ N N' := by
    intro c hc A hA
    induction hA using Submodule.span_induction with
    | mem A h =>
      obtain ⟨t, ht, A₀, hA₀, rfl⟩ := h
      exact key4 c hc t ht A₀ hA₀
    | zero => rw [map_zero, smul_zero]; exact zero_mem _
    | add x y _ _ h1 h2 => rw [map_add, smul_add]; exact add_mem h1 h2
    | smul ρ A _ h =>
      rw [emV_smulO, ← opM_smul]
      exact imS_stable s cc δ N N' ρ h
  have key2 : ∀ w ∈ TaylorLogMetric.lamOf D cc δ, ∀ A ∈ TaylorLogMetric.YYl D (s.lat N) (s.lat N'), w • emV A ∈ imS s cc δ N N' := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w h =>
      obtain ⟨c, hc, rfl⟩ := h
      exact key3 c hc
    | zero => intro A _; rw [zero_smul]; exact zero_mem _
    | add x y _ _ h1 h2 => intro A hA; rw [add_smul]; exact add_mem (h1 A hA) (h2 A hA)
    | neg x _ h => intro A hA; rw [neg_smul]; exact neg_mem (h A hA)
  unfold TaylorLogMetric.La
  rw [AddSubgroup.closure_le]
  rintro _ ⟨w, hw, A, hA, rfl⟩
  exact key2 w hw A hA

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Conclude with `phi_mem_La s cc δ N N' hz`. Conclude with `La_le s cc δ N N'`.
-/
theorem phi_per : imS s cc δ N N' = TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact phi_mem_La s cc δ N N' hz
  · exact La_le s cc δ N N'

end Per

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use function extensionality and compare the values at `τ i j`. Establish `h1` using `congrFun (congrFun (congrFun h (s.iT.symm τ)) i) j`. Establish `h2 : δ * s.σ₀ (X.emb (s.iT.symm τ) (x (Pi.single j 1) i)) = z (s.iT.symm τ, i, j)` using `h1`.

Rewrite `h2` using `[hok.1, Equiv.apply_symm_apply]`. Conclude with `h2`. Introduce `h`. Use function extensionality and compare the values at `τ i j`. Establish `h1` using `congrFun (congrFun (congrFun h (s.iT τ)) i) j`.

Establish `h2 : δ * TaylorLogMetric.embT D (s.iT τ) (s.iE (x (Pi.single j 1) i)) = z (s.iT.symm (s.iT τ), i, j)` using `h1`. Rewrite `h2` using `[← hok.1, Equiv.symm_apply_apply]`. Conclude with `h2`.
-/
theorem embH_iff (hok : s.Ok) (δ : ℂ) {a b : ℕ} (x : HomE X.E a b) (z : DVar X.Tau a b → ℂ) :
    embH (X.embC s.σ₀) δ x = flat X.Tau a b z ↔ phi s δ x = s.flatV a b z := by
  constructor
  · intro h
    funext τ i j
    have h1 := congrFun (congrFun (congrFun h (s.iT.symm τ)) i) j
    have h2 : δ * s.σ₀ (X.emb (s.iT.symm τ) (x (Pi.single j 1) i)) = z (s.iT.symm τ, i, j) := h1
    rw [hok.1, Equiv.apply_symm_apply] at h2
    exact h2
  · intro h
    funext τ i j
    have h1 := congrFun (congrFun (congrFun h (s.iT τ)) i) j
    have h2 : δ * TaylorLogMetric.embT D (s.iT τ) (s.iE (x (Pi.single j 1) i)) = z (s.iT.symm (s.iT τ), i, j) := h1
    rw [← hok.1, Equiv.symm_apply_apply] at h2
    exact h2

/- English proof (translation)
Introduce `D X s cc δ B χ cD a b N N' hok`. Use extensionality with `z`. Establish `h1 : z ∈ lamF (ambOf s B χ cD) N N' ↔ ∃ x ∈ perO (aaX s cc) N N', embH (X.embC s.σ₀) δ x = flat X.Tau a b z` using `Iff.rfl`. Establish `h2 : z ∈ s.laF B.tor (s.lat N) (s.lat N') ↔ s.flatV a b z ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N')` using `Iff.rfl`. Rewrite using `[h1, h2, ← phi_per]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, h⟩`. Conclude with `⟨x, hx, (embH_iff s hok δ x z).1 h⟩`. Introduce and unpack `⟨x, hx, h⟩`. Conclude with `⟨x, hx, (embH_iff s hok δ x z).2 h⟩`.
-/
theorem lamTie : LamTie := by
  intro D X s cc δ B χ cD a b N N' hok
  ext z
  have h1 : z ∈ lamF (ambOf s B χ cD) N N' ↔ ∃ x ∈ perO (aaX s cc) N N', embH (X.embC s.σ₀) δ x = flat X.Tau a b z := Iff.rfl
  have h2 : z ∈ s.laF B.tor (s.lat N) (s.lat N') ↔ s.flatV a b z ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') := Iff.rfl
  rw [h1, h2, ← phi_per]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, (embH_iff s hok δ x z).1 h⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, (embH_iff s hok δ x z).2 h⟩

section Frame

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

def unitM {a b : ℕ} (e : D.host.E) (β : Fin b) (α : Fin a) : Matrix (Fin b) (Fin a) D.host.E :=
  fun i j => if i = β ∧ j = α then e else 0

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show ∑ j, (if i = β ∧ j = α then e else 0) * y j = _`. Distinguish the cases in `hi : i = β`. Simplify using `[hi]`. Simplify using `[hi]`.
-/
theorem unitM_mulVec {a b : ℕ} (e : D.host.E) (β : Fin b) (α : Fin a) (y : Fin a → D.host.E) :
    (unitM e β α).mulVec y = fun i => if i = β then e * y α else 0 := by
  funext i
  show ∑ j, (if i = β ∧ j = α then e else 0) * y j = _
  by_cases hi : i = β
  · simp [hi]
  · simp [hi]

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Use `show ω * ((n : ℂ) * (if i = β ∧ j = α then s.σ₀ (X.emb (s.iT.symm τ) r) else 0)) = ω * TaylorLogMetric.embT D τ (if i = β ∧ j = α then (n : D.host.E) * s.iE r else 0)`. Distinguish the cases in `h : i = β ∧ j = α`. Rewrite using `[if_pos h, if_pos h, hok.1, Equiv.apply_symm_apply, map_mul, map_natCast]`. Rewrite using `[if_neg h, if_neg h, map_zero, mul_zero]`.
-/
theorem flatV_vecE (hok : s.Ok) {a b : ℕ} (n : ℕ) (ω : ℂ) (r : X.E) (β : Fin b) (α : Fin a) :
    s.flatV a b (ω • ((n : ℂ) • vecE s.σ₀ r β α)) = ω • emV (unitM ((n : D.host.E) * s.iE r) β α) := by
  funext τ i j
  show ω * ((n : ℂ) * (if i = β ∧ j = α then s.σ₀ (X.emb (s.iT.symm τ) r) else 0)) =
    ω * TaylorLogMetric.embT D τ (if i = β ∧ j = α then (n : D.host.E) * s.iE r else 0)
  by_cases h : i = β ∧ j = α
  · rw [if_pos h, if_pos h, hok.1, Equiv.apply_symm_apply, map_mul, map_natCast]
  · rw [if_neg h, if_neg h, map_zero, mul_zero]

/- English proof (translation)
Take `⟨s₁, hs₁, -, h1b⟩` from `hN`. Take `⟨s₂, hs₂, h2a, -⟩` from `hN'`. Use `⟨s₂ * s₁, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Break down `(Nat.Prime.dvd_mul hp.out).1 h with h | h` into its components or cases.

Conclude with `(Nat.Prime.coprime_iff_not_dvd hp.out).1 hs₂.symm h`. Conclude with `(Nat.Prime.coprime_iff_not_dvd hp.out).1 hs₁.symm h`. Introduce `r β α ω hω`. Rewrite using `[lamTie D X s cc δ B χ cD a b N N' hok]`. Use `show s.flatV a b (ω • (((s₂ * s₁ : ℕ) : ℂ) • vecE s.σ₀ (r : X.E) β α)) ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N')`.

Rewrite using `[flatV_vecE s hok]`. Use `AddSubgroup.subset_closure ⟨ω, (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B ω).1 hω, _, Submodule.subset_span ⟨1, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.int_mem_inverse_half_different isIntegral_one, _, Submodule.subset_span ?_, (one_smu …` and prove the remaining obligations. Introduce `y hy`. Rewrite using `[unitM_mulVec]`. Take `⟨r', hr'⟩` from `(s.int_iff (r : X.E)).2 ⟨r, rfl⟩`.

Establish `hy1` using `h1b y hy`. Unfold `StandardLatticesGL3.stdL at hy1`. Rewrite `hy1` using `[Submodule.mem_pi]`. Take `⟨u, hu⟩` from `Submodule.mem_one.1 (hy1 α (Set.mem_univ _))`. Establish `hv : (fun i => if i = β then s.iE (r : X.E) * ((s₁ : D.host.E) * y α) else 0 : Fin b → D.host.E) ∈ StandardLatticesGL3.stdL D b`.

Unfold `StandardLatticesGL3.stdL`. Rewrite using `[Submodule.mem_pi]`. Introduce `i _`. Distinguish the cases in `hi : i = β`. Rewrite using `[if_pos hi]`.

Use `Submodule.mem_one.2 ⟨r' * u, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hr', hu]`. Both sides reduce to the same expression. Rewrite using `[if_neg hi]`. Conclude with `zero_mem _`.

Establish `h3` using `h2a _ hv`. Establish `e : (fun i => if i = β then ((s₂ * s₁ : ℕ) : D.host.E) * s.iE (r : X.E) * y α else 0 : Fin b → D.host.E) = (s₂ : D.host.E) • (fun i => if i = β then s.iE (r : X.E) * ((s₁ : D.host.E) * y α) else 0 : Fin b → D.host.E)`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = β`. Simplify using `only [Pi.smul_apply, if_pos hi, smul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Pi.smul_apply, if_neg hi, smul_zero]`. Rewrite using `[e]`. Conclude with `h3`.
-/
theorem inMul_std (hok : s.Ok) {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (p : ℕ) [hp : Fact p.Prime]
    (hN : s.StdAtP p N) (hN' : s.StdAtP p N') :
    ∃ n₀ : ℕ, ¬ p ∣ n₀ ∧ ∀ (r : 𝓞 X.E) (β : Fin b) (α : Fin a),
      InMul B.L (lamF (ambOf s B χ cD) N N') ((n₀ : ℂ) • vecE (ambOf s B χ cD).σ₀ (r : X.E) β α) := by
  obtain ⟨s₁, hs₁, -, h1b⟩ := hN
  obtain ⟨s₂, hs₂, h2a, -⟩ := hN'
  refine ⟨s₂ * s₁, ?_, ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hp.out).1 h with h | h
    · exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 hs₂.symm h
    · exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 hs₁.symm h
  · intro r β α ω hω
    rw [lamTie D X s cc δ B χ cD a b N N' hok]
    show s.flatV a b (ω • (((s₂ * s₁ : ℕ) : ℂ) • vecE s.σ₀ (r : X.E) β α)) ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N')
    rw [flatV_vecE s hok]
    refine AddSubgroup.subset_closure ⟨ω, (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B ω).1 hω, _,
      Submodule.subset_span ⟨1, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.int_mem_inverse_half_different isIntegral_one, _, Submodule.subset_span ?_, (one_smul _ _).symm⟩, rfl⟩
    intro y hy
    rw [unitM_mulVec]
    obtain ⟨r', hr'⟩ := (s.int_iff (r : X.E)).2 ⟨r, rfl⟩
    have hy1 := h1b y hy
    unfold StandardLatticesGL3.stdL at hy1
    rw [Submodule.mem_pi] at hy1
    obtain ⟨u, hu⟩ := Submodule.mem_one.1 (hy1 α (Set.mem_univ _))
    have hv : (fun i => if i = β then s.iE (r : X.E) * ((s₁ : D.host.E) * y α) else 0 : Fin b → D.host.E) ∈ StandardLatticesGL3.stdL D b := by
      unfold StandardLatticesGL3.stdL
      rw [Submodule.mem_pi]
      intro i _
      by_cases hi : i = β
      · rw [if_pos hi]
        refine Submodule.mem_one.2 ⟨r' * u, ?_⟩
        rw [map_mul, hr', hu]
        rfl
      · rw [if_neg hi]
        exact zero_mem _
    have h3 := h2a _ hv
    have e : (fun i => if i = β then ((s₂ * s₁ : ℕ) : D.host.E) * s.iE (r : X.E) * y α else 0 : Fin b → D.host.E) =
        (s₂ : D.host.E) • (fun i => if i = β then s.iE (r : X.E) * ((s₁ : D.host.E) * y α) else 0 : Fin b → D.host.E) := by
      funext i
      by_cases hi : i = β
      · simp only [Pi.smul_apply, if_pos hi, smul_eq_mul]
        push_cast
        ring
      · simp only [Pi.smul_apply, if_neg hi, smul_zero]
    rw [e]
    exact h3

/- English proof (translation)
Introduce `τ τ' h`. Apply `s.iT.injective` to reduce the goal to its premises. Apply `embInj D` to reduce the goal to its premises. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `y`.

Establish `h1` using `congrArg (fun f : X.E →+* ℂ => f (s.iE.symm y)) h`. Establish `h2 : s.σ₀ (X.emb τ (s.iE.symm y)) = s.σ₀ (X.emb τ' (s.iE.symm y))` using `h1`. Rewrite `h2` using `[hok.1, hok.1, RingEquiv.apply_symm_apply]`. Conclude with `h2`.
-/
theorem embC_injective (hok : s.Ok) : Function.Injective (X.embC (ambOf s B χ cD).σ₀) := by
  intro τ τ' h
  apply s.iT.injective
  apply embInj D
  apply RingHom.ext
  intro y
  have h1 := congrArg (fun f : X.E →+* ℂ => f (s.iE.symm y)) h
  have h2 : s.σ₀ (X.emb τ (s.iE.symm y)) = s.σ₀ (X.emb τ' (s.iE.symm y)) := h1
  rw [hok.1, hok.1, RingEquiv.apply_symm_apply] at h2
  exact h2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem thF_eq {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) :
    Formalism.L2.AlgTh.thF (ambOf s B χ cD) N N' = fun z => B.eNat χ a b (s.lat N) (s.lat N') (s.flatV a b z) := rfl

/- English proof (translation)
The claim follows from `hF X (ambOf s B χ cD) a b N N' B.L p ι hdisc (embC_injective s B χ cD hok) (fun τ => hc (s.iT τ)) (inMul_std s B χ cD hok N N' p hN hN')`.
-/
theorem frame_std (hF : Formalism.L2.AlgTh.KerFrame) (hok : s.Ok) {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (hN : s.StdAtP p N) (hN' : s.StdAtP p N')
    (hdisc : ¬ (p : ℤ) ∣ NumberField.discr X.E) (hc : ∀ τ, ‖ι (cD τ)‖ ≤ 1) :
    ∃ (J : Type) (_ : Fintype J) (v : J → DVar X.Tau a b → ℂ) (M : J → DVar X.Tau a b → ℂ_[p]),
      (∀ j, InMul B.L (lamF (ambOf s B χ cD) N N') (v j)) ∧ (∀ j k, ‖M j k‖ ≤ 1) ∧
      ∀ i k, Formalism.L2.Th1.GD.frameM (ι : ℂ →+* ℂ_[p]) v M i k = if i = k then ι ((ambOf s B χ cD : Amb X).cD k.1) else 0 :=
  hF X (ambOf s B χ cD) a b N N' B.L p ι hdisc (embC_injective s B χ cD hok) (fun τ => hc (s.iT τ))
    (inMul_std s B χ cD hok N N' p hN hN')

end Frame

end Formalism.L2.Ker.KS
