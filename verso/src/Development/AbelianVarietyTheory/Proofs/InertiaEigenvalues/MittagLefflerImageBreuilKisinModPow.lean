import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteBreuilKisinQuotientPrimePowXPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.ImageTower

variable {S A : Type} [CommRing S] [CommRing A] (e : S →+* A) (p : ℕ) {d : ℕ} {d' : ℕ → ℕ}
  (R : ∀ n, Matrix (Fin d) (Fin (d' n)) A)

def Img (n m : ℕ) : Set (Fin d → A) :=
  {w | ∃ s : Fin (d' m) → S, ∀ i, (p : A) ^ n ∣ (w - R m *ᵥ fun j => e (s j)) i}

variable {e p R}

/- English proof (translation)
Take `⟨s, hs⟩` from `hw`. Use `⟨s, fun i => ?_⟩` and prove the remaining obligations. Establish `: (x - R m *ᵥ fun j => e (s j)) i = (x - w) i + (w - R m *ᵥ fun j => e (s j)) i`. Simplify using `only [Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `dvd_add (h i) (hs i)`.
-/
theorem mem_of_dvd {n m : ℕ} {w x : Fin d → A} (hw : w ∈ Img e p R n m)
    (h : ∀ i, (p : A) ^ n ∣ (x - w) i) : x ∈ Img e p R n m := by
  obtain ⟨s, hs⟩ := hw
  refine ⟨s, fun i => ?_⟩
  have : (x - R m *ᵥ fun j => e (s j)) i = (x - w) i + (w - R m *ᵥ fun j => e (s j)) i := by
    simp only [Pi.sub_apply]; ring
  rw [this]; exact dvd_add (h i) (hs i)

/- English proof (translation)
Take `⟨s, hs⟩` from `hw`. Take `⟨t, ht⟩` from `hx`. Use `⟨s + t, fun i => ?_⟩` and prove the remaining obligations. Establish `he : (fun j => e ((s + t) j)) = (fun j => e (s j)) + fun j => e (t j)`. Use function extensionality and compare the values at `j`.

Simplify using the standard rewrite rules. Rewrite using `[he, mulVec_add]`. Establish `: (w + x - ((R m *ᵥ fun j => e (s j)) + R m *ᵥ fun j => e (t j))) i = (w - R m *ᵥ fun j => e (s j)) i + (x - R m *ᵥ fun j => e (t j)) i`. Simplify using `only [Pi.sub_apply, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `dvd_add (hs i) (ht i)`.
-/
theorem add_mem {n m : ℕ} {w x : Fin d → A} (hw : w ∈ Img e p R n m) (hx : x ∈ Img e p R n m) :
    w + x ∈ Img e p R n m := by
  obtain ⟨s, hs⟩ := hw
  obtain ⟨t, ht⟩ := hx
  refine ⟨s + t, fun i => ?_⟩
  have he : (fun j => e ((s + t) j)) = (fun j => e (s j)) + fun j => e (t j) := by
    funext j; simp
  rw [he, mulVec_add]
  have : (w + x - ((R m *ᵥ fun j => e (s j)) + R m *ᵥ fun j => e (t j))) i =
      (w - R m *ᵥ fun j => e (s j)) i + (x - R m *ᵥ fun j => e (t j)) i := by
    simp only [Pi.sub_apply, Pi.add_apply]; ring
  rw [this]; exact dvd_add (hs i) (ht i)

/- English proof (translation)
Assemble the required witnesses or components as `⟨s, fun i => by simp⟩`.
-/
theorem image_mem (n m : ℕ) (s : Fin (d' m) → S) : (R m *ᵥ fun j => e (s j)) ∈ Img e p R n m :=
  ⟨s, fun i => by simp⟩

/- English proof (translation)
Simplify using `only [mulVec, dotProduct]`. Conclude with `Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (h i j) _`.
-/
theorem dvd_mulVec' {κ ι : Type} [Fintype ι] {q : A} (D : Matrix κ ι A) (h : ∀ i j, q ∣ D i j)
    (v : ι → A) (i : κ) : q ∣ (D *ᵥ v) i := by
  simp only [mulVec, dotProduct]
  exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (h i j) _

/- English proof (translation)
Introduce and unpack `w ⟨s, hs⟩`. Use `⟨Y m *ᵥ s, fun i => ?_⟩` and prove the remaining obligations. Establish `he : (fun j => e ((Y m *ᵥ s) j)) = (Y m).map e *ᵥ fun j => e (s j)`. Use function extensionality and compare the values at `j`. Conclude with `RingHom.map_mulVec e (Y m) s j`.

Rewrite using `[he, mulVec_mulVec]`. Establish `: (w - (R m * (Y m).map e) *ᵥ fun j => e (s j)) i = (w - R (m + 1) *ᵥ fun j => e (s j)) i - ((R m * (Y m).map e - R (m + 1)) *ᵥ fun j => e (s j)) i`. Simplify using `only [sub_mulVec, Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `dvd_sub (hs i) ((pow_dvd_pow _ hnm).trans (dvd_mulVec' _ (h1 m) _ i))`.
-/
theorem img_succ_sub (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) S)
    (h1 : ∀ n i j, (p : A) ^ n ∣ (R n * (Y n).map e - R (n + 1)) i j) {n m : ℕ} (hnm : n ≤ m) :
    Img e p R n (m + 1) ⊆ Img e p R n m := by
  rintro w ⟨s, hs⟩
  refine ⟨Y m *ᵥ s, fun i => ?_⟩
  have he : (fun j => e ((Y m *ᵥ s) j)) = (Y m).map e *ᵥ fun j => e (s j) := by
    funext j; exact RingHom.map_mulVec e (Y m) s j
  rw [he, mulVec_mulVec]
  have : (w - (R m * (Y m).map e) *ᵥ fun j => e (s j)) i =
      (w - R (m + 1) *ᵥ fun j => e (s j)) i -
        ((R m * (Y m).map e - R (m + 1)) *ᵥ fun j => e (s j)) i := by
    simp only [sub_mulVec, Pi.sub_apply]; ring
  rw [this]
  exact dvd_sub (hs i) ((pow_dvd_pow _ hnm).trans (dvd_mulVec' _ (h1 m) _ i))

/- English proof (translation)
Proceed by induction on `m', hm using Nat.le_induction with`. Consider the case `base => exact le_rfl`. Consider the case `succ k hk ih => exact (img_succ_sub Y h1 (hnm.trans hk)).trans ih`.
-/
theorem img_anti (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) S)
    (h1 : ∀ n i j, (p : A) ^ n ∣ (R n * (Y n).map e - R (n + 1)) i j) {n m m' : ℕ} (hnm : n ≤ m)
    (hm : m ≤ m') : Img e p R n m' ⊆ Img e p R n m := by
  induction m', hm using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact (img_succ_sub Y h1 (hnm.trans hk)).trans ih

/- English proof (translation)
Introduce and unpack `w ⟨s, hs⟩`. Conclude with `⟨s, fun i => (pow_dvd_pow _ hkn).trans (hs i)⟩`.
-/
theorem img_mod {k n m : ℕ} (hkn : k ≤ n) : Img e p R n m ⊆ Img e p R k m := by
  rintro w ⟨s, hs⟩; exact ⟨s, fun i => (pow_dvd_pow _ hkn).trans (hs i)⟩

/- English proof (translation)
Set `J : Ideal S` to `Ideal.span {(p : S) ^ n} ⊔ Ideal.span {u ^ c}`. Set `T : ℕ → Set (Fin (d' n) → S ⧸ J)` to `fun m => {q | ∃ s : Fin (d' n) → S, (fun j => Ideal.Quotient.mk J (s j)) = q ∧ (R n *ᵥ fun j => e (s j)) ∈ Img e p R n m}`. Establish `key : ∀ m m', n ≤ m → n ≤ m' → T m ⊆ T m' → Img e p R n m ⊆ Img e p R n m'`. Introduce `m m' hm hm' hT w hw`. Take `⟨s, hs⟩` from `img_anti Y h1 le_rfl hm hw`.

Establish `hRs : (R n *ᵥ fun j => e (s j)) ∈ Img e p R n m` using `mem_of_dvd hw fun i => dvd_sub_comm.1 (hs i)`. Take `⟨s', hq, hs'⟩` from `hT ⟨s, rfl, hRs⟩`. Establish `hj : ∀ j, ∃ a b : S, s j = s' j + (p : S) ^ n * a + u ^ c * b`. Introduce `j`. Establish `hqj : Ideal.Quotient.mk J (s' j) = Ideal.Quotient.mk J (s j)` using `congrFun hq j`.

Establish `hmem : s' j - s j ∈ J` using `Ideal.Quotient.eq.1 hqj`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.1 hmem`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton.1 hy`. Take `⟨b, rfl⟩` from `Ideal.mem_span_singleton.1 hz`. Conclude with `⟨-a, -b, by linear_combination hyz⟩`.

Use `choose a b hab using hj`. Take `⟨t, ht⟩` from `hc m' hm' b`. Establish `hsum : ((R n *ᵥ fun j => e (s' j)) + R n *ᵥ fun j => e (u ^ c * b j)) ∈ Img e p R n m'` using `add_mem hs' (mem_of_dvd (image_mem n m' t) ht)`. Establish `hRs' : (R n *ᵥ fun j => e (s j)) ∈ Img e p R n m'`. Use `mem_of_dvd hsum fun i => ?_` and prove the remaining obligations.

Establish `hv : (fun j => e (s j)) = (fun j => e (s' j)) + (p : A) ^ n • (fun j => e (a j)) + fun j => e (u ^ c * b j)`. Use function extensionality and compare the values at `j`. Rewrite using `[hab j]`. Simplify using the standard rewrite rules. Rewrite using `[hv, mulVec_add, mulVec_add, mulVec_smul]`.

Establish `: ((R n *ᵥ fun j => e (s' j)) + (p : A) ^ n • (R n *ᵥ fun j => e (a j)) + (R n *ᵥ fun j => e (u ^ c * b j)) - ((R n *ᵥ fun j => e (s' j)) + R n *ᵥ fun j => e (u ^ c * b j))) i = (p : A) ^ n * (R n *ᵥ fun j => e (a j)) i`. Simplify using `only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `dvd_mul_right _ _`.

Conclude with `mem_of_dvd hRs' hs`. Establish `hanti : Antitone fun k => T (n + k)`. Introduce and unpack `k k' hkk q ⟨s, rfl, hs⟩`. Conclude with `⟨s, rfl, img_anti Y h1 (Nat.le_add_right n k) (by omega) hs⟩`. Take `⟨k₀, hk₀⟩` from `WellFoundedLT.antitone_chain_condition hanti`.

Use `⟨n + k₀, by omega, fun m hm => le_antisymm (img_anti Y h1 (by omega) hm) ?_⟩` and prove the remaining obligations. Establish `hTe : T (n + k₀) = T m`. Use `hk₀ (m - n) (by omega)` as an intermediate fact. Rewrite `this` using `[Nat.add_sub_cancel' (by omega : n ≤ m)]`. Then use the resulting hypothesis. Conclude with `key _ _ (by omega) (by omega) hTe.le`.
-/
theorem img_stable (u : S) (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) S)
    (h1 : ∀ n i j, (p : A) ^ n ∣ (R n * (Y n).map e - R (n + 1)) i j)
    (n c : ℕ) [Finite (S ⧸ (Ideal.span {(p : S) ^ n} ⊔ Ideal.span {u ^ c}))]
    (hc : ∀ m, n ≤ m → ∀ s : Fin (d' n) → S, ∃ s' : Fin (d' m) → S, ∀ i,
      (p : A) ^ n ∣ ((R n *ᵥ fun j => e (u ^ c * s j)) - R m *ᵥ fun j => e (s' j)) i) :
    ∃ m₀, n ≤ m₀ ∧ ∀ m, m₀ ≤ m → Img e p R n m = Img e p R n m₀ := by
  let J : Ideal S := Ideal.span {(p : S) ^ n} ⊔ Ideal.span {u ^ c}
  let T : ℕ → Set (Fin (d' n) → S ⧸ J) := fun m =>
    {q | ∃ s : Fin (d' n) → S, (fun j => Ideal.Quotient.mk J (s j)) = q ∧
      (R n *ᵥ fun j => e (s j)) ∈ Img e p R n m}
  have key : ∀ m m', n ≤ m → n ≤ m' → T m ⊆ T m' → Img e p R n m ⊆ Img e p R n m' := by
    intro m m' hm hm' hT w hw
    obtain ⟨s, hs⟩ := img_anti Y h1 le_rfl hm hw
    have hRs : (R n *ᵥ fun j => e (s j)) ∈ Img e p R n m :=
      mem_of_dvd hw fun i => dvd_sub_comm.1 (hs i)
    obtain ⟨s', hq, hs'⟩ := hT ⟨s, rfl, hRs⟩
    have hj : ∀ j, ∃ a b : S, s j = s' j + (p : S) ^ n * a + u ^ c * b := by
      intro j
      have hqj : Ideal.Quotient.mk J (s' j) = Ideal.Quotient.mk J (s j) := congrFun hq j
      have hmem : s' j - s j ∈ J := Ideal.Quotient.eq.1 hqj
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.1 hy
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 hz
      exact ⟨-a, -b, by linear_combination hyz⟩
    choose a b hab using hj
    obtain ⟨t, ht⟩ := hc m' hm' b
    have hsum : ((R n *ᵥ fun j => e (s' j)) + R n *ᵥ fun j => e (u ^ c * b j)) ∈ Img e p R n m' :=
      add_mem hs' (mem_of_dvd (image_mem n m' t) ht)
    have hRs' : (R n *ᵥ fun j => e (s j)) ∈ Img e p R n m' := by
      refine mem_of_dvd hsum fun i => ?_
      have hv : (fun j => e (s j)) = (fun j => e (s' j)) + (p : A) ^ n • (fun j => e (a j)) +
          fun j => e (u ^ c * b j) := by
        funext j; rw [hab j]; simp
      rw [hv, mulVec_add, mulVec_add, mulVec_smul]
      have : ((R n *ᵥ fun j => e (s' j)) + (p : A) ^ n • (R n *ᵥ fun j => e (a j)) +
          (R n *ᵥ fun j => e (u ^ c * b j)) - ((R n *ᵥ fun j => e (s' j)) +
            R n *ᵥ fun j => e (u ^ c * b j))) i = (p : A) ^ n * (R n *ᵥ fun j => e (a j)) i := by
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [this]; exact dvd_mul_right _ _
    exact mem_of_dvd hRs' hs
  have hanti : Antitone fun k => T (n + k) := by
    rintro k k' hkk q ⟨s, rfl, hs⟩
    exact ⟨s, rfl, img_anti Y h1 (Nat.le_add_right n k) (by omega) hs⟩
  obtain ⟨k₀, hk₀⟩ := WellFoundedLT.antitone_chain_condition hanti
  refine ⟨n + k₀, by omega, fun m hm => le_antisymm (img_anti Y h1 (by omega) hm) ?_⟩
  have hTe : T (n + k₀) = T m := by
    have := hk₀ (m - n) (by omega)
    rwa [Nat.add_sub_cancel' (by omega : n ≤ m)] at this
  exact key _ _ (by omega) (by omega) hTe.le

/- English proof (translation)
Establish `hst : ∀ n, ∃ m₀, n ≤ m₀ ∧ ∀ m, m₀ ≤ m → Img e p R n m = Img e p R n m₀` using `fun n => by`. Take `⟨c, hc⟩` from `h2 n`. Use `haveI := hfin n c`. Conclude with `img_stable u Y h1 n c hc`. Use `choose m₀ hnm₀ hm₀ using hst`.

Establish `lift : ∀ n x, x ∈ Img e p R n (m₀ n) → ∃ y, y ∈ Img e p R (n + 1) (m₀ (n + 1)) ∧ ∀ i, (p : A) ^ n ∣ (y - x) i`. Introduce `n x hx`. Rewrite `hx` using `[← hm₀ n (max (m₀ n) (m₀ (n + 1))) (le_max_left _ _)]`. Take `⟨s, hs⟩` from `hx`. Use `⟨_, ?_, fun i => dvd_sub_comm.1 (hs i)⟩` and prove the remaining obligations.

Rewrite using `[← hm₀ (n + 1) (max (m₀ n) (m₀ (n + 1))) (le_max_right _ _)]`. Conclude with `image_mem _ _ s`. Use `choose! L hL hLd using lift`. Introduce `n`. Use `⟨m₀ n, hnm₀ n, fun s => ?_⟩` and prove the remaining obligations.

Use `set x₀ := R (m₀ n) *ᵥ fun j => e (s j) with hx₀def`. Establish `hx₀ : x₀ ∈ Img e p R n (m₀ n)` using `image_mem _ _ s`. Set `w : ℕ → Fin d → A` to `fun k => Nat.rec x₀ (fun k y => L (n + k) y) k`. Establish `hw0 : w 0 = x₀` using `rfl`. Establish `hws : ∀ k, w (k + 1) = L (n + k) (w k)` using `fun _ => rfl`.

Establish `hmem : ∀ k, w k ∈ Img e p R (n + k) (m₀ (n + k))`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact hx₀`. Consider the case `succ k ih => rw [hws]`.

Conclude with `hL _ _ ih`. Establish `htel : ∀ k j i, (p : A) ^ (n + k) ∣ (w (k + j) - w k) i`. Introduce `k j`. Proceed by induction on `j with`. Consider the case `zero => intro i`.

Simplify using the standard rewrite rules. Consider the case `succ j ih`. Introduce `i`. Establish `: (w (k + (j + 1)) - w k) i = (w (k + j + 1) - w (k + j)) i + (w (k + j) - w k) i`. Rewrite using `[← add_assoc]`.

Simplify using `only [Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, hws]`. Conclude with `dvd_add ((pow_dvd_pow _ (by omega)).trans (hLd _ _ (hmem _) i)) (ih i)`. Establish `hcau : ∀ i, ∃ v : A, ∀ k, (p : A) ^ k ∣ w k i - v`.

Introduce `i`. Take `⟨v, hv⟩` from `IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {(p : A)}) A) (f := fun k => w k i) (by`. Introduce `a b hab`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le hab`.

Establish `h' : (p : A) ^ a ∣ w (a + j) i - w a i` using `(pow_dvd_pow _ (by omega)).trans (htel a j i)`. Conclude with `dvd_sub_comm.1 h')`. Use `⟨v, fun k => ?_⟩` and prove the remaining obligations. Use `hv k` as an intermediate fact. Rewrite `this` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Then use the resulting hypothesis.

Use `choose V hV using hcau`. Use `⟨V, fun i => ?_, fun k => ?_⟩` and prove the remaining obligations. Establish `h1'` using `htel 0 n i`. Rewrite `h1'` using `[Nat.add_zero, Nat.zero_add, hw0]`. Establish `: (V - x₀) i = (V i - w n i) + (w n - x₀) i` using `by simp only [Pi.sub_apply]; ring`.

Rewrite using `[this]`. Conclude with `dvd_add (dvd_sub_comm.1 (hV i n)) h1'`. Establish `hk : w k ∈ Img e p R k k` using `img_anti Y h1 le_rfl (le_trans (by omega) (hnm₀ (n + k))) (img_mod (by omega) (hmem k))`. Conclude with `mem_of_dvd hk fun i => dvd_sub_comm.1 (hV i k)`.
-/
theorem ml (u : S) (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) S)
    (h1 : ∀ n i j, (p : A) ^ n ∣ (R n * (Y n).map e - R (n + 1)) i j)
    (hfin : ∀ n c, Finite (S ⧸ (Ideal.span {(p : S) ^ n} ⊔ Ideal.span {u ^ c})))
    [IsAdicComplete (Ideal.span {(p : A)}) A]
    (h2 : ∀ n, ∃ c : ℕ, ∀ m, n ≤ m → ∀ s : Fin (d' n) → S, ∃ s' : Fin (d' m) → S, ∀ i,
      (p : A) ^ n ∣ ((R n *ᵥ fun j => e (u ^ c * s j)) - R m *ᵥ fun j => e (s' j)) i) :
    ∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (d' m) → S, ∃ v : Fin d → A,
      (∀ i, (p : A) ^ n ∣ (v - R m *ᵥ fun j => e (s j)) i) ∧
      ∀ k, ∃ s' : Fin (d' k) → S, ∀ i, (p : A) ^ k ∣ (v - R k *ᵥ fun j => e (s' j)) i := by
  have hst : ∀ n, ∃ m₀, n ≤ m₀ ∧ ∀ m, m₀ ≤ m → Img e p R n m = Img e p R n m₀ := fun n => by
    obtain ⟨c, hc⟩ := h2 n
    haveI := hfin n c
    exact img_stable u Y h1 n c hc
  choose m₀ hnm₀ hm₀ using hst
  have lift : ∀ n x, x ∈ Img e p R n (m₀ n) →
      ∃ y, y ∈ Img e p R (n + 1) (m₀ (n + 1)) ∧ ∀ i, (p : A) ^ n ∣ (y - x) i := by
    intro n x hx
    rw [← hm₀ n (max (m₀ n) (m₀ (n + 1))) (le_max_left _ _)] at hx
    obtain ⟨s, hs⟩ := hx
    refine ⟨_, ?_, fun i => dvd_sub_comm.1 (hs i)⟩
    rw [← hm₀ (n + 1) (max (m₀ n) (m₀ (n + 1))) (le_max_right _ _)]
    exact image_mem _ _ s
  choose! L hL hLd using lift
  intro n
  refine ⟨m₀ n, hnm₀ n, fun s => ?_⟩
  set x₀ := R (m₀ n) *ᵥ fun j => e (s j) with hx₀def
  have hx₀ : x₀ ∈ Img e p R n (m₀ n) := image_mem _ _ s
  let w : ℕ → Fin d → A := fun k => Nat.rec x₀ (fun k y => L (n + k) y) k
  have hw0 : w 0 = x₀ := rfl
  have hws : ∀ k, w (k + 1) = L (n + k) (w k) := fun _ => rfl
  have hmem : ∀ k, w k ∈ Img e p R (n + k) (m₀ (n + k)) := by
    intro k; induction k with
    | zero => exact hx₀
    | succ k ih => rw [hws]; exact hL _ _ ih
  have htel : ∀ k j i, (p : A) ^ (n + k) ∣ (w (k + j) - w k) i := by
    intro k j; induction j with
    | zero => intro i; simp
    | succ j ih =>
      intro i
      have : (w (k + (j + 1)) - w k) i = (w (k + j + 1) - w (k + j)) i + (w (k + j) - w k) i := by
        rw [← add_assoc]; simp only [Pi.sub_apply]; ring
      rw [this, hws]
      exact dvd_add ((pow_dvd_pow _ (by omega)).trans (hLd _ _ (hmem _) i)) (ih i)
  have hcau : ∀ i, ∃ v : A, ∀ k, (p : A) ^ k ∣ w k i - v := by
    intro i
    obtain ⟨v, hv⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {(p : A)}) A) (f := fun k => w k i) (by
      intro a b hab
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hab
      have h' : (p : A) ^ a ∣ w (a + j) i - w a i := (pow_dvd_pow _ (by omega)).trans (htel a j i)
      exact dvd_sub_comm.1 h')
    refine ⟨v, fun k => ?_⟩
    have := hv k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at this
  choose V hV using hcau
  refine ⟨V, fun i => ?_, fun k => ?_⟩
  · have h1' := htel 0 n i
    rw [Nat.add_zero, Nat.zero_add, hw0] at h1'
    have : (V - x₀) i = (V i - w n i) + (w n - x₀) i := by simp only [Pi.sub_apply]; ring
    rw [this]; exact dvd_add (dvd_sub_comm.1 (hV i n)) h1'
  · have hk : w k ∈ Img e p R k k :=
      img_anti Y h1 le_rfl (le_trans (by omega) (hnm₀ (n + k))) (img_mod (by omega) (hmem k))
    exact mem_of_dvd hk fun i => dvd_sub_comm.1 (hV i k)

end GlobalTheory.ImageTower

/- English proof (translation)
Use `PerfectRing.ofSurjective _ _ fun x => ?_` and prove the remaining obligations. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := OCb l) x`. Take `⟨a, rfl⟩` from `(bijective_frobenius (OCb l) l).2 a`. Take `⟨b, rfl⟩` from `(bijective_frobenius (OCb l) l).2 b`. Conclude with `⟨algebraMap _ _ a / algebraMap _ _ b, by simp [frobenius_def]⟩`.
-/
theorem GlobalTheory.ImageTower.perfectRing_Cb' (l : ℕ) [Fact l.Prime] : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  obtain ⟨a, rfl⟩ := (bijective_frobenius (OCb l) l).2 a
  obtain ⟨b, rfl⟩ := (bijective_frobenius (OCb l) l).2 b
  exact ⟨algebraMap _ _ a / algebraMap _ _ b, by simp [frobenius_def]⟩

/- English proof (translation)
Introduce `l _ K bk d d' R Y h1 h2`. Use `haveI : PerfectRing (Cb l) l := GlobalTheory.ImageTower.perfectRing_Cb' l`. Use `haveI : IsAdicComplete (Ideal.span {(l : WCb l)}) (WCb l) := WittVector.isAdicCompleteIdealSpanP`. Conclude with `GlobalTheory.ImageTower.ml (e := bk.evW) (p := l) (R := R) X Y h1 (fun n c => GlobalTheory.T.finite_breuilKisin_quotient_prime_pow_X_pow l K bk n c) h2`.
-/
theorem GlobalTheory.BKLim.mittagLeffler_image : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (d' : ℕ → ℕ) (R : ∀ n, Matrix (Fin d) (Fin (d' n)) (WCb l)) (Y : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) (bk.S)), (∀ n i j, (l : WCb l) ^ n ∣ (R n * (Y n).map bk.evW - R (n + 1)) i j) → (∀ n, ∃ c : ℕ, ∀ m, n ≤ m → ∀ s : Fin (d' n) → bk.S, ∃ s' : Fin (d' m) → bk.S, ∀ i, (l : WCb l) ^ n ∣ ((R n *ᵥ fun j => bk.evW (X ^ c * s j)) - R m *ᵥ fun j => bk.evW (s' j)) i) → ∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i := by
  intro l _ K bk d d' R Y h1 h2
  haveI : PerfectRing (Cb l) l := GlobalTheory.ImageTower.perfectRing_Cb' l
  haveI : IsAdicComplete (Ideal.span {(l : WCb l)}) (WCb l) := WittVector.isAdicCompleteIdealSpanP
  exact GlobalTheory.ImageTower.ml (e := bk.evW) (p := l) (R := R) X Y h1 (fun n c => GlobalTheory.T.finite_breuilKisin_quotient_prime_pow_X_pow l K bk n c) h2
