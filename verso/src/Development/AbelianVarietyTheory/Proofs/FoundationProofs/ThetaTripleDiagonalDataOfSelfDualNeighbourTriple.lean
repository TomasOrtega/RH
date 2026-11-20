import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGeneratorCmDifferentIdealScaledStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLatticeStatement

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TriangleRows

def cv (D : D7) {n : ℕ} (y : Fin n → D.host.E) : Fin n → D.host.E := fun j => D.host.conj (y j)

def IC (D : D7) (cc : Ideal (𝓞 D.host.K)) {n : ℕ} (L : Lat D n) : Lat D n :=
  Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L, v = t • fun j => D.host.conj (y j)}

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [cv, Pi.add_apply, map_add]`.
-/
theorem cv_add (x y : Fin n → D.host.E) : cv D (x + y) = cv D x + cv D y := by
  funext j; simp only [cv, Pi.add_apply, map_add]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Rewrite using `[← algebraMap_smul D.host.E a x]`. Simplify using `only [cv, Pi.smul_apply, smul_eq_mul, map_mul, sgO_coe]`.
-/
theorem cv_smul (a : 𝓞 D.host.E) (x : Fin n → D.host.E) :
    cv D (a • x) = ((sgO D a : 𝓞 D.host.E) : D.host.E) • cv D x := by
  funext j
  rw [← algebraMap_smul D.host.E a x]
  simp only [cv, Pi.smul_apply, smul_eq_mul, map_mul, sgO_coe]

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨t, ht, y, hy, rfl⟩`.
-/
theorem smul_cv_mem {L : Lat D n} {t : D.host.E} (ht : t ∈ Iid D cc) {y : Fin n → D.host.E} (hy : y ∈ L) :
    t • cv D y ∈ IC D cc L := Submodule.subset_span ⟨t, ht, y, hy, rfl⟩

/- English proof (translation)
The claim follows from `Submodule.span_mono fun _ ⟨t, ht, y, hy, e⟩ => ⟨t, ht, y, h hy, e⟩`.
-/
theorem IC_mono {L L' : Lat D n} (h : L ≤ L') : IC D cc L ≤ IC D cc L' :=
  Submodule.span_mono fun _ ⟨t, ht, y, hy, e⟩ => ⟨t, ht, y, h hy, e⟩

/- English proof (translation)
Take `⟨a, rfl⟩` from `he`. Rewrite using `[mul_comm, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ _ ht`.
-/
theorem mul_int {t e : D.host.E} (ht : t ∈ Iid D cc) (he : IntE D e) : t * e ∈ Iid D cc := by
  obtain ⟨a, rfl⟩ := he
  rw [mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ ht

/- English proof (translation)
The claim follows from `(((sd_iff D L).1 hL).2.2 x).1 hx y hy`.
-/
theorem int_hE {L : Lat D n} (hL : SD D L) {x y : Fin n → D.host.E} (hx : x ∈ L) (hy : y ∈ L) :
    IntE D (hE D x y) := (((sd_iff D L).1 hL).2.2 x).1 hx y hy

/- English proof (translation)
Simplify using `only [cv, hE, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem pair_cv (t : D.host.E) (y w : Fin n → D.host.E) : ∑ j, (t • cv D y) j * w j = t * hE D w y := by
  simp only [cv, hE, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Proceed by induction on `hr using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨t, ht, y, hy, rfl⟩` from `hv`. Express the relevant statement in the definitionally equal form `∑ j, (t • cv D y) j * w j ∈ _`. Rewrite using `[pair_cv]`.

Conclude with `mul_int ht (int_hE hL hw hy)`. Consider the case `zero => simp`. Consider the case `add u v _ _ hu hv`. Simplify using `only [Pi.add_apply, add_mul, Finset.sum_add_distrib]`. Conclude with `add_mem hu hv`.

Consider the case `smul a v _ hv`. Simplify using `only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum]`. Conclude with `Submodule.smul_mem _ _ hv`.
-/
theorem pair_mem {L : Lat D n} (hL : SD D L) {r w : Fin n → D.host.E} (hr : r ∈ IC D cc L) (hw : w ∈ L) :
    ∑ j, r j * w j ∈ Iid D cc := by
  induction hr using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨t, ht, y, hy, rfl⟩ := hv
    change ∑ j, (t • cv D y) j * w j ∈ _
    rw [pair_cv]
    exact mul_int ht (int_hE hL hw hy)
  | zero => simp
  | add u v _ _ hu hv =>
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    exact add_mem hu hv
  | smul a v _ hv =>
    simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum]
    exact Submodule.smul_mem _ _ hv

/- English proof (translation)
Establish `h` using `smul_cv_mem ht (hb _ (hσ p hp))`. Rewrite `h` using `[cv_smul, sgO_sgO, smul_smul, mul_comm]`. Rewrite using `[Algebra.smul_def]`. Conclude with `h`.
-/
theorem P_smul_cv {M : Lat D n} {P : Ideal (𝓞 D.host.E)} (hσ : ∀ a ∈ P, sgO D a ∈ P) {b : Fin n → D.host.E}
    (hb : ∀ p ∈ P, p • b ∈ M) {p : 𝓞 D.host.E} (hp : p ∈ P) {t : D.host.E} (ht : t ∈ Iid D cc) :
    (p • t) • cv D b ∈ IC D cc M := by
  have h := smul_cv_mem ht (hb _ (hσ p hp))
  rw [cv_smul, sgO_sgO, smul_smul, mul_comm] at h
  rw [Algebra.smul_def]
  exact h

/- English proof (translation)
Proceed by induction on `hr using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨t, ht, y, hy, rfl⟩` from `hv`. Take `⟨m, hm, w, hw, rfl⟩` from `Submodule.mem_sup.1 hy`. Take `⟨o, rfl⟩` from `Submodule.mem_span_singleton.1 hw`.

Take `⟨a, ha⟩` from `hg (sgO D o • t) (Submodule.smul_mem _ _ ht)`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `h1 : (sgO D o • t - a • t₀) • cv D b ∈ IC D cc M`. Use `Submodule.smul_induction_on (p := fun s => s • cv D b ∈ IC D cc M) ha ?_ ?_` and prove the remaining obligations. Introduce `p hp s hs`.

Conclude with `P_smul_cv hσ hb hp hs`. Introduce `u v hu hv`. Rewrite using `[add_smul]`. Conclude with `add_mem hu hv`. Establish `h2` using `add_mem (smul_cv_mem ht hm) h1`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `t • cv D (m + o • b) - _ = _`. Rewrite using `[cv_add, cv_smul, smul_add, smul_smul, sub_smul, Algebra.smul_def (sgO D o) t, mul_comm t, add_sub_assoc]`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add u v _ _ hu hv`.

Take `⟨a, ha⟩` from `hu`. Take `⟨a', ha'⟩` from `hv`. Use `⟨a + a', ?_⟩` and prove the remaining obligations. Use `add_mem ha ha' using 1` and compare the differences between its conclusion and the goal. Rewrite using `[add_smul, add_smul]`.

Normalize the expressions using the abelian group laws. Consider the case `smul c v _ hv`. Take `⟨a, ha⟩` from `hv`. Use `⟨c * a, ?_⟩` and prove the remaining obligations. Use `Submodule.smul_mem _ c ha using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[smul_sub, mul_smul, smul_assoc]`.
-/
theorem decomp {M : Lat D n} {P : Ideal (𝓞 D.host.E)} (hσ : ∀ a ∈ P, sgO D a ∈ P) {b : Fin n → D.host.E}
    (hb : ∀ p ∈ P, p • b ∈ M) {t₀ : D.host.E}
    (hg : ∀ t ∈ Iid D cc, ∃ a : 𝓞 D.host.E, t - a • t₀ ∈ P • Iid D cc) {r : Fin n → D.host.E}
    (hr : r ∈ IC D cc (M ⊔ Submodule.span (𝓞 D.host.E) {b})) :
    ∃ a : 𝓞 D.host.E, r - (a • t₀) • cv D b ∈ IC D cc M := by
  induction hr using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨t, ht, y, hy, rfl⟩ := hv
    obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hw
    obtain ⟨a, ha⟩ := hg (sgO D o • t) (Submodule.smul_mem _ _ ht)
    refine ⟨a, ?_⟩
    have h1 : (sgO D o • t - a • t₀) • cv D b ∈ IC D cc M := by
      refine Submodule.smul_induction_on (p := fun s => s • cv D b ∈ IC D cc M) ha ?_ ?_
      · intro p hp s hs; exact P_smul_cv hσ hb hp hs
      · intro u v hu hv; rw [add_smul]; exact add_mem hu hv
    have h2 := add_mem (smul_cv_mem ht hm) h1
    convert h2 using 1
    change t • cv D (m + o • b) - _ = _
    rw [cv_add, cv_smul, smul_add, smul_smul, sub_smul, Algebra.smul_def (sgO D o) t, mul_comm t, add_sub_assoc]
  | zero => exact ⟨0, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha⟩ := hu
    obtain ⟨a', ha'⟩ := hv
    refine ⟨a + a', ?_⟩
    convert add_mem ha ha' using 1
    rw [add_smul, add_smul]; abel
  | smul c v _ hv =>
    obtain ⟨a, ha⟩ := hv
    refine ⟨c * a, ?_⟩
    convert Submodule.smul_mem _ c ha using 1
    rw [smul_sub, mul_smul, smul_assoc]

def Pt (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) : (Fin N' → Fin N → D.host.E) →+ VC D N N' where
  toFun z := pt D (tor0 D cc δ) δ (Matrix.of z)
  map_zero' := by funext τ i j; simp [pt, embV, tor0]
  map_add' z w := by funext τ i j; simp [pt, embV, tor0, mul_add]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Pt_apply (δ : ℂ) {N N' : ℕ} (z : Fin N' → Fin N → D.host.E) (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    Pt D cc δ N N' z τ i j = δ * embT D τ (z i j) := rfl

def Row (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N : ℕ} (N' : ℕ) (t₀ : D.host.E) (b : Fin N → D.host.E)
    (i : Fin N') : 𝓞 D.host.E →+ VC D N N' where
  toFun a := Pt D cc δ N N' (Pi.single i ((a • t₀) • cv D b))
  map_zero' := by simp
  map_add' a a' := by rw [add_smul, add_smul, Pi.single_add, map_add]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Row_apply (δ : ℂ) {N N' : ℕ} (t₀ : D.host.E) (b : Fin N → D.host.E) (i : Fin N') (a : 𝓞 D.host.E) :
    Row D cc δ N' t₀ b i a = Pt D cc δ N N' (Pi.single i ((a • t₀) • cv D b)) := rfl

/- English proof (translation)
Simplify using `only [Row_apply, ← map_sum]`. Rewrite using `[Finset.univ_sum_single (fun i => (a i • t₀) • cv D b)]`.
-/
theorem sum_Row (δ : ℂ) {N N' : ℕ} (t₀ : D.host.E) (b : Fin N → D.host.E) (a : Fin N' → 𝓞 D.host.E) :
    ∑ i, Row D cc δ N' t₀ b i (a i) = Pt D cc δ N N' (fun i => (a i • t₀) • cv D b) := by
  simp only [Row_apply, ← map_sum]
  rw [Finset.univ_sum_single (fun i => (a i • t₀) • cv D b)]

/- English proof (translation)
Simplify using `[Hf]`.
-/
theorem Hf_zero_left (T : Tor D) {N N' : ℕ} (y : VC D N N') : Hf D T 0 y = 0 := by simp [Hf]

/- English proof (translation)
Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `only [Hf, Row_apply, Pt_apply]`. Use `congr 1`. Use `Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Establish `e : embT D τ (algebraMap (𝓞 D.host.E) D.host.E (sgO D a)) = (starRingEnd ℂ) (embT D τ (algebraMap (𝓞 D.host.E) D.host.E a))` using `embT_conj D τ a`. Simplify using `only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]`. Simplify using `only [Algebra.smul_def, map_mul, map_one, e]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `[Pi.single_eq_of_ne hk]`. Simplify using `only [Hf, Row_apply, Pt_apply]`. Rewrite using `[Finset.sum_eq_zero, zero_div]`. Use `fun τ _ => Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `[Pi.single_eq_of_ne h]`. Simplify using `[Pi.single_eq_of_ne hk]`.
-/
theorem Hf_Row (δ : ℂ) {N N' : ℕ} (t₀ : D.host.E) (b x : Fin N → D.host.E) (i j : Fin N') (a a' : 𝓞 D.host.E) :
    Hf D (tor0 D cc δ) (Row D cc δ N' t₀ x i a') (Row D cc δ N' t₀ b j a) =
      if i = j then Hf D (tor0 D cc δ) (Row D cc δ N' t₀ x i (a' * sgO D a)) (Row D cc δ N' t₀ b i 1) else 0 := by
  split_ifs with h
  · subst h
    simp only [Hf, Row_apply, Pt_apply]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    by_cases hk : k = i
    · subst hk
      have e : embT D τ (algebraMap (𝓞 D.host.E) D.host.E (sgO D a)) =
          (starRingEnd ℂ) (embT D τ (algebraMap (𝓞 D.host.E) D.host.E a)) := embT_conj D τ a
      simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_mul, map_one, e]
      ring
    · simp [Pi.single_eq_of_ne hk]
  · simp only [Hf, Row_apply, Pt_apply]
    rw [Finset.sum_eq_zero, zero_div]
    refine fun τ _ => Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    by_cases hk : k = i
    · subst hk
      simp [Pi.single_eq_of_ne h]
    · simp [Pi.single_eq_of_ne hk]

/- English proof (translation)
Take `⟨h1, h2, -, h4⟩` from `GlobalTheory.T.thetaLattice_image_rationalHomLattice D cc δ hδ N N'`. Rewrite using `[h2]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, e⟩`. Establish `: Matrix.of z = w` using `h1 e`.

Substitute `this` using the available equality. Conclude with `(h4 L hL _).1 hw`. Introduce `h`. Conclude with `⟨Matrix.of z, (h4 L hL _).2 h, rfl⟩`.
-/
theorem Pt_mem {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} {L : Lat D N} (hL : SD D L) (z : Fin N' → Fin N → D.host.E) :
    Pt D cc δ N N' z ∈ La D (tor0 D cc δ) L (stdL D N') ↔ ∀ i, z i ∈ IC D cc L := by
  obtain ⟨h1, h2, -, h4⟩ := GlobalTheory.T.thetaLattice_image_rationalHomLattice D cc δ hδ N N'
  rw [h2]
  constructor
  · rintro ⟨w, hw, e⟩
    have : Matrix.of z = w := h1 e
    subst this
    exact (h4 L hL _).1 hw
  · intro h
    exact ⟨Matrix.of z, (h4 L hL _).2 h, rfl⟩

/- English proof (translation)
Take `⟨w, -, e⟩` from `((GlobalTheory.T.thetaLattice_image_rationalHomLattice D cc δ hδ N N').2.1 L _ v).1 hv`. Conclude with `⟨w, e⟩`.
-/
theorem exists_Pt {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} {L : Lat D N} {v : VC D N N'}
    (hv : v ∈ La D (tor0 D cc δ) L (stdL D N')) : ∃ z, v = Pt D cc δ N N' z := by
  obtain ⟨w, -, e⟩ := ((GlobalTheory.T.thetaLattice_image_rationalHomLattice D cc δ hδ N N').2.1 L _ v).1 hv
  exact ⟨w, e⟩

/- English proof (translation)
Use `(Pt_mem hδ hL _).2 fun k => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Rewrite using `[Pi.single_eq_same]` and apply the resulting hypothesis. Rewrite using `[Pi.single_eq_of_ne hk]`.

Conclude with `zero_mem _`.
-/
theorem single_mem {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} {L : Lat D N} (hL : SD D L) (i : Fin N')
    {r : Fin N → D.host.E} (hr : r ∈ IC D cc L) :
    Pt D cc δ N N' (Pi.single i r) ∈ La D (tor0 D cc δ) L (stdL D N') := by
  refine (Pt_mem hδ hL _).2 fun k => ?_
  by_cases hk : k = i
  · subst hk; rwa [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hk]; exact zero_mem _

/- English proof (translation)
Introduce `z hz`. Take `⟨w, rfl⟩` from `exists_Pt hδ hz`. Use `choose a ha using fun i => decomp hσ hb hg ((Pt_mem hδ hB w).1 hz i)`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[sum_Row, ← map_sub]`.

Conclude with `⟨(Pt_mem hδ h₁ _).2 fun i => IC_mono m₁ (ha i), (Pt_mem hδ h₂ _).2 fun i => IC_mono m₂ (ha i)⟩`.
-/
theorem reduce {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} {M L₁ L₂ : Lat D N} {P : Ideal (𝓞 D.host.E)}
    (hσ : ∀ a ∈ P, sgO D a ∈ P) {b : Fin N → D.host.E} (hb : ∀ p ∈ P, p • b ∈ M) {t₀ : D.host.E}
    (hg : ∀ t ∈ Iid D cc, ∃ a : 𝓞 D.host.E, t - a • t₀ ∈ P • Iid D cc)
    (hB : SD D (M ⊔ Submodule.span (𝓞 D.host.E) {b})) (h₁ : SD D L₁) (h₂ : SD D L₂) (m₁ : M ≤ L₁) (m₂ : M ≤ L₂) :
    ∀ z ∈ La D (tor0 D cc δ) (M ⊔ Submodule.span (𝓞 D.host.E) {b}) (stdL D N'), ∃ a : Fin N' → 𝓞 D.host.E,
      z - ∑ i, Row D cc δ N' t₀ b i (a i) ∈
        La D (tor0 D cc δ) L₁ (stdL D N') ⊓ La D (tor0 D cc δ) L₂ (stdL D N') := by
  intro z hz
  obtain ⟨w, rfl⟩ := exists_Pt hδ hz
  choose a ha using fun i => decomp hσ hb hg ((Pt_mem hδ hB w).1 hz i)
  refine ⟨a, ?_⟩
  rw [sum_Row, ← map_sub]
  exact ⟨(Pt_mem hδ h₁ _).2 fun i => IC_mono m₁ (ha i), (Pt_mem hδ h₂ _).2 fun i => IC_mono m₂ (ha i)⟩

/- English proof (translation)
Introduce `D cc δ hcc hδ N N' P hP hσ A B C ⟨hA, hB, hC, M, b, x, eA, eB, eC, hp, hθ⟩`. Take `⟨t₀, ht₀, hg, hq⟩` from `GlobalTheory.T.exists_generator_cmDifferentIdealScaled D cc hcc P hP`. Establish `mA : M ≤ A` using `eA ▸ le_sup_left`. Establish `mB : M ≤ B` using `eB ▸ le_sup_left`. Establish `mC : M ≤ C` using `eC ▸ le_sup_left`.

Establish `bA : b + x ∈ A` using `eA ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`. Establish `bB : b ∈ B` using `eB ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`. Establish `bC : x ∈ C` using `eC ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`. Establish `hat : ∀ a : 𝓞 D.host.E, a • t₀ ∈ Iid D cc` using `fun a => Submodule.smul_mem _ _ ht₀`. Establish `hsm : ∀ (p : 𝓞 D.host.E) (u v : Fin N → D.host.E), p • hE D u v = hE D (p • u) v` using `fun p u v => by`.

Rewrite using `[← algebraMap_smul D.host.E p u, hE_smul_left, Algebra.smul_def]`. Use `⟨Row D cc δ N' t₀ b, Row D cc δ N' t₀ x, fun i => { toFun := fun s => Hf D (tor0 D cc δ) (Row D cc δ N' t₀ x i s) (Row D cc δ N' t₀ b i 1) map_zero' := by rw [map_zero, Hf_zero_left] map_add' := fun s s' => by rw [map_add, Hf_add_left] }, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j a a'`. Conclude with `Hf_Row δ t₀ b x i j a a'`. Introduce `i a`.

Use `⟨single_mem hδ hB i (smul_cv_mem (hat a) bB), single_mem hδ hC i (smul_cv_mem (hat a) bC), ?_⟩` and prove the remaining obligations. Rewrite using `[Row_apply, Row_apply, ← map_add, ← Pi.single_add, ← smul_add, ← cv_add]`. Conclude with `single_mem hδ hA i (smul_cv_mem (hat a) bA)`. Introduce `i p hpP`. Establish `h1` using `P_smul_cv hσ (fun p h => (hp p h).1) hpP ht₀`.

Establish `h2` using `P_smul_cv hσ (fun p h => (hp p h).2) hpP ht₀`. Conclude with `⟨⟨single_mem hδ hA i (IC_mono mA h1), single_mem hδ hC i (IC_mono mC h1)⟩, ⟨single_mem hδ hA i (IC_mono mA h2), single_mem hδ hB i (IC_mono mB h2)⟩⟩`. Substitute `eB` using the available equality. Conclude with `reduce hδ hσ (fun p h => (hp p h).1) hg hB hA hC mA mC`. Substitute `eC` using the available equality.

Conclude with `reduce hδ hσ (fun p h => (hp p h).2) hg hC hA hB mA mB`. Introduce `a ha i`. Rewrite `ha` using `[sum_Row]`. Establish `h1` using `pair_mem hA ((Pt_mem hδ hA _).1 ha i) bA`. Rewrite `h1` using `[pair_cv, hE_add_left, mul_add]`.

Establish `h2` using `sub_mem h1 (mul_int (hat (a i)) (int_hE hB bB bB))`. Rewrite `h2` using `[add_sub_cancel_left, smul_mul_assoc]`. Use `hq (hE D x b) (fun h => hθ (conj_hE D x b ▸ h.conj)) (fun p hpP => ?_) _ h2` and prove the remaining obligations. Rewrite using `[hsm]`. Conclude with `int_hE hB (mB (hp p hpP).2) bB`.

Introduce `a ha i`. Rewrite `ha` using `[sum_Row]`. Establish `h1` using `pair_mem hB ((Pt_mem hδ hB _).1 ha i) bB`. Rewrite `h1` using `[pair_cv, smul_mul_assoc]`. Use `hq (hE D b x) hθ (fun p hpP => ?_) _ h1` and prove the remaining obligations.

Rewrite using `[hsm]`. Conclude with `int_hE hC (mC (hp p hpP).1) bC`.
-/
theorem triDat_rows : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 → ∀ (N N' : ℕ)
    (P : Ideal (𝓞 D.host.E)), P.IsMaximal → (∀ a ∈ P, sgO D a ∈ P) → ∀ A B C : Lat D N, Tri D P A B C →
    TriDat D (tor0 D cc δ) (La D (tor0 D cc δ) A (stdL D N')) (La D (tor0 D cc δ) B (stdL D N'))
      (La D (tor0 D cc δ) C (stdL D N')) P N' := by
  intro D cc δ hcc hδ N N' P hP hσ A B C ⟨hA, hB, hC, M, b, x, eA, eB, eC, hp, hθ⟩
  obtain ⟨t₀, ht₀, hg, hq⟩ := GlobalTheory.T.exists_generator_cmDifferentIdealScaled D cc hcc P hP
  have mA : M ≤ A := eA ▸ le_sup_left
  have mB : M ≤ B := eB ▸ le_sup_left
  have mC : M ≤ C := eC ▸ le_sup_left
  have bA : b + x ∈ A := eA ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have bB : b ∈ B := eB ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have bC : x ∈ C := eC ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hat : ∀ a : 𝓞 D.host.E, a • t₀ ∈ Iid D cc := fun a => Submodule.smul_mem _ _ ht₀
  have hsm : ∀ (p : 𝓞 D.host.E) (u v : Fin N → D.host.E), p • hE D u v = hE D (p • u) v := fun p u v => by
    rw [← algebraMap_smul D.host.E p u, hE_smul_left, Algebra.smul_def]
  refine ⟨Row D cc δ N' t₀ b, Row D cc δ N' t₀ x, fun i =>
    { toFun := fun s => Hf D (tor0 D cc δ) (Row D cc δ N' t₀ x i s) (Row D cc δ N' t₀ b i 1)
      map_zero' := by rw [map_zero, Hf_zero_left]
      map_add' := fun s s' => by rw [map_add, Hf_add_left] }, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j a a'
    exact Hf_Row δ t₀ b x i j a a'
  · intro i a
    refine ⟨single_mem hδ hB i (smul_cv_mem (hat a) bB), single_mem hδ hC i (smul_cv_mem (hat a) bC), ?_⟩
    rw [Row_apply, Row_apply, ← map_add, ← Pi.single_add, ← smul_add, ← cv_add]
    exact single_mem hδ hA i (smul_cv_mem (hat a) bA)
  · intro i p hpP
    have h1 := P_smul_cv hσ (fun p h => (hp p h).1) hpP ht₀
    have h2 := P_smul_cv hσ (fun p h => (hp p h).2) hpP ht₀
    exact ⟨⟨single_mem hδ hA i (IC_mono mA h1), single_mem hδ hC i (IC_mono mC h1)⟩,
      ⟨single_mem hδ hA i (IC_mono mA h2), single_mem hδ hB i (IC_mono mB h2)⟩⟩
  · subst eB
    exact reduce hδ hσ (fun p h => (hp p h).1) hg hB hA hC mA mC
  · subst eC
    exact reduce hδ hσ (fun p h => (hp p h).2) hg hC hA hB mA mB
  · intro a ha i
    rw [sum_Row] at ha
    have h1 := pair_mem hA ((Pt_mem hδ hA _).1 ha i) bA
    rw [pair_cv, hE_add_left, mul_add] at h1
    have h2 := sub_mem h1 (mul_int (hat (a i)) (int_hE hB bB bB))
    rw [add_sub_cancel_left, smul_mul_assoc] at h2
    refine hq (hE D x b) (fun h => hθ (conj_hE D x b ▸ h.conj)) (fun p hpP => ?_) _ h2
    rw [hsm]; exact int_hE hB (mB (hp p hpP).2) bB
  · intro a ha i
    rw [sum_Row] at ha
    have h1 := pair_mem hB ((Pt_mem hδ hB _).1 ha i) bB
    rw [pair_cv, smul_mul_assoc] at h1
    refine hq (hE D b x) hθ (fun p hpP => ?_) _ h1
    rw [hsm]; exact int_hE hC (mC (hp p hpP).1) bC

end GlobalTheory.TriangleRows
