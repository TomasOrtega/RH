import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.BranchingSystems

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

/- English proof (translation)
Introduce `hx`. Substitute `hx` using the available equality. Break down `le_or_gt j i.castSucc with hj | hj` into its components or cases. Establish `h3` using `hL.antitone hj`. Use linear arithmetic over natural numbers and integers.

Establish `hj' : i.succ ≤ j` using `Fin.castSucc_lt_iff_succ_le.mp hj`. Establish `h3` using `hL.antitone hj'`. Use linear arithmetic over natural numbers and integers.
-/
theorem between {n : ℕ} {L : Fin (n + 1) → ℤ} (hL : StrictAnti L) (i : Fin n) {x : ℤ}
    (h1 : L i.succ < x) (h2 : x < L i.castSucc) (j : Fin (n + 1)) : x ≠ L j := by
  intro hx
  subst hx
  rcases le_or_gt j i.castSucc with hj | hj
  · have h3 := hL.antitone hj
    omega
  · have hj' : i.succ ≤ j := Fin.castSucc_lt_iff_succ_le.mp hj
    have h3 := hL.antitone hj'
    omega

section Comb

variable {n : ℕ} {L : Fin (n + 1) → ℤ} {P : (Fin n → ℤ) → Prop}

/- English proof (translation)
Proceed by induction on `t, ht using Int.le_induction with`. Consider the case `base => intro _`. Conclude with `h0`. Consider the case `succ t ht ih`. Introduce `hv`.

Establish `hP` using `ih (fun t' h1 h2 => hv t' h1 (by omega))`. Establish `h2` using `hR _ hP i (by simpa using hv t ht (by omega))`. Simplify using `using h2`.
-/
theorem runUp (hR : ∀ M, P M → ∀ i, (∀ j, M i ≠ L j) → P (Function.update M i (M i + 1)))
    (M : Fin n → ℤ) (i : Fin n) (t0 : ℤ) (h0 : P (Function.update M i t0)) (t : ℤ) (ht : t0 ≤ t) :
    (∀ t', t0 ≤ t' → t' < t → ∀ j, t' ≠ L j) → P (Function.update M i t) := by
  induction t, ht using Int.le_induction with
  | base => intro _; exact h0
  | succ t ht ih =>
    intro hv
    have hP := ih (fun t' h1 h2 => hv t' h1 (by omega))
    have h2 := hR _ hP i (by simpa using hv t ht (by omega))
    simpa using h2

/- English proof (translation)
Proceed by induction on `t, ht using Int.le_induction_down with`. Consider the case `base => intro _`. Conclude with `h0`. Consider the case `pred t ht ih`. Introduce `hv`.

Establish `hP` using `ih (fun t' h1 h2 => hv t' (by omega) h2)`. Establish `h2` using `hD _ hP i (by simpa using hv (t - 1) le_rfl (by omega))`. Simplify using `using h2`.
-/
theorem runDown (hD : ∀ M, P M → ∀ i, (∀ j, M i - 1 ≠ L j) → P (Function.update M i (M i - 1)))
    (M : Fin n → ℤ) (i : Fin n) (t0 : ℤ) (h0 : P (Function.update M i t0)) (t : ℤ) (ht : t ≤ t0) :
    (∀ t', t ≤ t' → t' < t0 → ∀ j, t' ≠ L j) → P (Function.update M i t) := by
  induction t, ht using Int.le_induction_down with
  | base => intro _; exact h0
  | pred t ht ih =>
    intro hv
    have hP := ih (fun t' h1 h2 => hv t' (by omega) h2)
    have h2 := hD _ hP i (by simpa using hv (t - 1) le_rfl (by omega))
    simpa using h2

structure Sys {n : ℕ} (L : Fin (n + 1) → ℤ) (P : (Fin n → ℤ) → Prop) : Prop where
  anti : StrictAnti L
  inj : ∀ M, P M → Function.Injective M
  top : P (fun j => L j.castSucc)
  up : ∀ M, P M → ∀ i, (∀ j, M i ≠ L j) → P (Function.update M i (M i + 1))
  down : ∀ M, P M → ∀ i, (∀ j, M i - 1 ≠ L j) → P (Function.update M i (M i - 1))
  fin : ∀ M i, {t : ℤ | P (Function.update M i t)}.Finite

/- English proof (translation)
Establish `key : ∀ s : Finset (Fin n), P (fun j => if j ∈ s then M j else L j.castSucc)`. Introduce `s`. Use `Finset.induction_on s (by simpa using h.top) ?_` and prove the remaining obligations. Introduce `a s ha ih`. Establish `e : (fun j => if j ∈ insert a s then M j else L j.castSucc) = Function.update (fun j => if j ∈ s then M j else L j.castSucc) a (M a)`.

Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = a`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hj, Function.update_of_ne hj]`.

Rewrite using `[e]`. Establish `h0 : P (Function.update (fun j => if j ∈ s then M j else L j.castSucc) a (L a.castSucc))`. Establish `e2 : Function.update (fun j => if j ∈ s then M j else L j.castSucc) a (L a.castSucc) = (fun j => if j ∈ s then M j else L j.castSucc)`. Rewrite using `[Function.update_eq_self_iff]`. Simplify using `[ha]`.

Rewrite using `[e2]`. Conclude with `ih`. Establish `hMa` using `hM a`. Conclude with `runDown h.down _ a (L a.castSucc) h0 (M a) hMa.2 (fun t' h1 h2 j => between h.anti a (by omega) h2 j)`. Simplify using `using key Finset.univ`.
-/
theorem Sys.box (h : Sys L P) (M : Fin n → ℤ) (hM : Box L M) : P M := by
  have key : ∀ s : Finset (Fin n), P (fun j => if j ∈ s then M j else L j.castSucc) := by
    intro s
    refine Finset.induction_on s (by simpa using h.top) ?_
    intro a s ha ih
    have e : (fun j => if j ∈ insert a s then M j else L j.castSucc) =
        Function.update (fun j => if j ∈ s then M j else L j.castSucc) a (M a) := by
      funext j
      by_cases hj : j = a
      · subst hj
        simp
      · simp [hj, Function.update_of_ne hj]
    rw [e]
    have h0 : P (Function.update (fun j => if j ∈ s then M j else L j.castSucc) a (L a.castSucc)) := by
      have e2 : Function.update (fun j => if j ∈ s then M j else L j.castSucc) a (L a.castSucc) =
          (fun j => if j ∈ s then M j else L j.castSucc) := by
        rw [Function.update_eq_self_iff]
        simp [ha]
      rw [e2]
      exact ih
    have hMa := hM a
    exact runDown h.down _ a (L a.castSucc) h0 (M a) hMa.2
      (fun t' h1 h2 j => between h.anti a (by omega) h2 j)
  simpa using key Finset.univ

/- English proof (translation)
Introduce `h0`. Distinguish the cases in `hz : (i : ℕ) = 0`. Establish `hall : ∀ t, M i + 1 ≤ t → P (Function.update M i t)` using `fun t ht => runUp h.up M i _ h0 t ht (fun t' a _ j e => by`. Establish `: L j ≤ L i.castSucc` using `h.anti.antitone (by rw [Fin.le_def]; simp [hz])`. Use the proof step `omega)`.

Conclude with `(Set.infinite_of_injective_forall_mem (f := fun s : ℕ => M i + 1 + (s : ℤ)) (fun a b e => by simpa using e) (fun s => hall _ (by omega))) (h.fin M i)`. Set `i' : Fin n` to `⟨i - 1, by omega⟩`. Establish `e1 : i'.succ = i.castSucc`. Use `ext`. Simplify using `[i']`.

Use linear arithmetic over natural numbers and integers. Establish `b1` using `(hM i').1`. Rewrite `b1` using `[e1, ← hi]`. Establish `h1` using `runUp h.up M i _ h0 (M i') (by omega) (fun t' a b => between h.anti i' (by rw [e1]; omega) (by have := (hM i').2; omega))`. Establish `hne : i' ≠ i`.

Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `[i'] at this`. Use linear arithmetic over natural numbers and integers. Conclude with `hne (h.inj _ h1 (by simp [Function.update_of_ne hne]))`.
-/
theorem Sys.noUp (h : Sys L P) (M : Fin n → ℤ) (hM : Box L M) (i : Fin n) (hi : M i = L i.castSucc) :
    ¬ P (Function.update M i (M i + 1)) := by
  intro h0
  by_cases hz : (i : ℕ) = 0
  · have hall : ∀ t, M i + 1 ≤ t → P (Function.update M i t) := fun t ht =>
      runUp h.up M i _ h0 t ht (fun t' a _ j e => by
        have : L j ≤ L i.castSucc := h.anti.antitone (by rw [Fin.le_def]; simp [hz])
        omega)
    exact (Set.infinite_of_injective_forall_mem (f := fun s : ℕ => M i + 1 + (s : ℤ))
      (fun a b e => by simpa using e) (fun s => hall _ (by omega))) (h.fin M i)
  · let i' : Fin n := ⟨i - 1, by omega⟩
    have e1 : i'.succ = i.castSucc := by
      ext
      simp [i']
      omega
    have b1 := (hM i').1
    rw [e1, ← hi] at b1
    have h1 := runUp h.up M i _ h0 (M i') (by omega)
      (fun t' a b => between h.anti i' (by rw [e1]; omega) (by have := (hM i').2; omega))
    have hne : i' ≠ i := by
      intro e
      have := congrArg Fin.val e
      simp [i'] at this
      omega
    exact hne (h.inj _ h1 (by simp [Function.update_of_ne hne]))

/- English proof (translation)
Introduce `h0`. Distinguish the cases in `hz : (i : ℕ) + 1 = n`. Establish `hall : ∀ t, t ≤ M i - 1 → P (Function.update M i t)` using `fun t ht => runDown h.down M i _ h0 t ht (fun t' _ b j e => by`. Establish `: L i.succ ≤ L j` using `h.anti.antitone (by`. Rewrite using `[Fin.le_def]`.

Use `j.2` as an intermediate fact. Simplify using the standard rewrite rules. Use the proof step `omega)`. Use the proof step `omega)`. Conclude with `(Set.infinite_of_injective_forall_mem (f := fun s : ℕ => M i - 1 - (s : ℤ)) (fun a b e => by simpa using e) (fun s => hall _ (by omega))) (h.fin M i)`.

Set `i' : Fin n` to `⟨i + 1, by have := i.2; omega⟩`. Establish `e1 : i'.castSucc = i.succ`. Use `ext`. Simplify using `[i']`. Establish `b1` using `(hM i').2`.

Rewrite `b1` using `[e1]`. Establish `h1` using `runDown h.down M i _ h0 (M i') (by omega) (fun t' a b => between h.anti i' (by have := (hM i').1; omega) (by rw [e1]; omega))`. Establish `hne : i' ≠ i`. Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact.

Simplify using `[i'] at this`. Conclude with `hne (h.inj _ h1 (by simp [Function.update_of_ne hne]))`.
-/
theorem Sys.noDown (h : Sys L P) (M : Fin n → ℤ) (hM : Box L M) (i : Fin n) (hi : M i = L i.succ + 1) :
    ¬ P (Function.update M i (M i - 1)) := by
  intro h0
  by_cases hz : (i : ℕ) + 1 = n
  · have hall : ∀ t, t ≤ M i - 1 → P (Function.update M i t) := fun t ht =>
      runDown h.down M i _ h0 t ht (fun t' _ b j e => by
        have : L i.succ ≤ L j := h.anti.antitone (by
          rw [Fin.le_def]
          have := j.2
          simp
          omega)
        omega)
    exact (Set.infinite_of_injective_forall_mem (f := fun s : ℕ => M i - 1 - (s : ℤ))
      (fun a b e => by simpa using e) (fun s => hall _ (by omega))) (h.fin M i)
  · let i' : Fin n := ⟨i + 1, by have := i.2; omega⟩
    have e1 : i'.castSucc = i.succ := by
      ext
      simp [i']
    have b1 := (hM i').2
    rw [e1] at b1
    have h1 := runDown h.down M i _ h0 (M i') (by omega)
      (fun t' a b => between h.anti i' (by have := (hM i').1; omega) (by rw [e1]; omega))
    have hne : i' ≠ i := by
      intro e
      have := congrArg Fin.val e
      simp [i'] at this
    exact hne (h.inj _ h1 (by simp [Function.update_of_ne hne]))

end Comb

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[shf]`. Simplify using `[shf, Function.update_of_ne h]`.
-/
theorem shf_update {n : ℕ} (β : ℂ) (M : Fin n → ℤ) (i : Fin n) (t : ℤ) :
    Function.update (shf β M) i (β + (t : ℂ)) = shf β (Function.update M i t) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [shf]
  · simp [shf, Function.update_of_ne h]

/- English proof (translation)
Rewrite using `[← shf_update]`. Simplify using `[shf]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shf_up {n : ℕ} (β : ℂ) (M : Fin n → ℤ) (i : Fin n) :
    Function.update (shf β M) i (shf β M i + 1) = shf β (Function.update M i (M i + 1)) := by
  rw [← shf_update]
  simp [shf]
  ring

/- English proof (translation)
Rewrite using `[← shf_update]`. Simplify using `[shf]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shf_down {n : ℕ} (β : ℂ) (M : Fin n → ℤ) (i : Fin n) :
    Function.update (shf β M) i (shf β M i - 1) = shf β (Function.update M i (M i - 1)) := by
  rw [← shf_update]
  simp [shf]
  ring

/- English proof (translation)
Introduce `a b hab`. Establish `h` using `hL hab`. Use `⟨(L a - L b - 1).toNat, ?_⟩` and prove the remaining obligations. Simplify using `only [shf]`. Establish `e : ((L a - L b - 1).toNat : ℤ) = L a - L b - 1` using `Int.toNat_of_nonneg (by omega)`.

Establish `e2 : (((L a - L b - 1).toNat : ℕ) : ℂ) = ((L a - L b - 1 : ℤ) : ℂ)` using `by exact_mod_cast e`. Rewrite using `[e2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sdec_shf {n : ℕ} (β : ℂ) {L : Fin n → ℤ} (hL : StrictAnti L) : SDec (shf β L) := by
  intro a b hab
  have h := hL hab
  refine ⟨(L a - L b - 1).toNat, ?_⟩
  simp only [shf]
  have e : ((L a - L b - 1).toNat : ℤ) = L a - L b - 1 := Int.toNat_of_nonneg (by omega)
  have e2 : (((L a - L b - 1).toNat : ℕ) : ℂ) = ((L a - L b - 1 : ℤ) : ℂ) := by exact_mod_cast e
  rw [e2]
  push_cast
  ring

section Cap

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/- English proof (translation)
Take `⟨w, hw⟩` from `Infinite.exists_notMem_finset (Finset.univ.image fun j : Fin n => -(shf β M j))`. Establish `hc : (∏ j ∈ Finset.univ.erase i, (w + shf β M j)) ≠ 0`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `j _ h0`. Apply `hw` to reduce the goal to its premises.

Rewrite using `[Finset.mem_image]`. Conclude with `⟨j, Finset.mem_univ _, by linear_combination -h0⟩`. Establish `hf : ∀ t : ℤ, cpol (shf β (Function.update M i t)) w = (w + β + (t : ℂ)) * ∏ j ∈ Finset.univ.erase i, (w + shf β M j)`. Introduce `t`. Unfold `cpol`.

Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]`. Use `congr 1`. Simplify using `[shf]`. Expand and normalize the polynomial expressions, which then agree. Apply `Finset.prod_congr rfl` to reduce the goal to its premises.

Introduce `j hj`. Establish `hne : j ≠ i` using `Finset.ne_of_mem_erase hj`. Simplify using `[shf, Function.update_of_ne hne]`. Use `Set.Finite.subset (Set.Finite.preimage (f := fun t : ℤ => cpol (shf β (Function.update M i t)) w) ?_ (Module.End.finite_hasEigenvalue (qdet E w))) ?_` and prove the remaining obligations. Introduce `a _ b _ e`.

Simplify using `only [hf] at e`. Establish `e1` using `mul_right_cancel₀ hc e`. Establish `e2 : (a : ℂ) = b` using `by linear_combination e1`. Conclude with `e2` after adjusting the coercions. Introduce `t ht`.

Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot ht`. Conclude with `Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr (mem_CapSp.mp hv w), hv0⟩`.
-/
theorem fin_cap {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (β : ℂ) (M : Fin n → ℤ) (i : Fin n) :
    {t : ℤ | CapSp E (shf β (Function.update M i t)) ≠ ⊥}.Finite := by
  obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (Finset.univ.image fun j : Fin n => -(shf β M j))
  have hc : (∏ j ∈ Finset.univ.erase i, (w + shf β M j)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j _ h0
    apply hw
    rw [Finset.mem_image]
    exact ⟨j, Finset.mem_univ _, by linear_combination -h0⟩
  have hf : ∀ t : ℤ, cpol (shf β (Function.update M i t)) w =
      (w + β + (t : ℂ)) * ∏ j ∈ Finset.univ.erase i, (w + shf β M j) := by
    intro t
    unfold cpol
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp [shf]; ring
    · apply Finset.prod_congr rfl
      intro j hj
      have hne : j ≠ i := Finset.ne_of_mem_erase hj
      simp [shf, Function.update_of_ne hne]
  refine Set.Finite.subset (Set.Finite.preimage
    (f := fun t : ℤ => cpol (shf β (Function.update M i t)) w) ?_
    (Module.End.finite_hasEigenvalue (qdet E w))) ?_
  · intro a _ b _ e
    simp only [hf] at e
    have e1 := mul_right_cancel₀ hc e
    have e2 : (a : ℂ) = b := by linear_combination e1
    exact_mod_cast e2
  · intro t ht
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ht
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (mem_CapSp.mp hv w), hv0⟩

/- English proof (translation)
Establish `gl' : GlRel (subA E)` using `(hSR (Module.End ℂ V) n E H.gl).1`. Establish `hinj : ∀ M : Fin n → ℤ, CapSp (subA E) (shf β M) ≠ ⊥ → Function.Injective (shf β M)` using `fun M hM => (hCS V n (subA E) _ gl' hM).1`. Use `⟨H.anti, ?_, ?_, ?_, ?_, fun M i => fin_cap (subA E) β M i⟩` and prove the remaining obligations. Introduce `M hM a b hab`. Conclude with `hinj M hM (by simp [shf, hab])`.

Use `H.irr.1` as an intermediate fact. Take `⟨ν, v, -, hv0, hHW, -⟩` from `hSM V (n + 1) E H.gl ⊤ (fun _ _ _ _ => Submodule.mem_top) top_ne_bot`. Establish `hvL : v ∈ CapSp E (shf β L)` using `mem_CapSp.mpr fun w => H.cap w v`. Establish `hne : CapSp E (shf β L) ≠ ⊥` using `fun e => hv0 (by rw [e] at hvL; simpa using hvL)`. Establish `hν` using `(hCS V (n + 1) E _ H.gl hne).2 (sdec_shf β H.anti) ν v hvL hv0 hHW`.

Establish `hHW' : IsHW (subA E) (fun k => ν k.castSucc) v` using `⟨fun a => hHW.1 a.castSucc, fun a b hab => hHW.2 _ _ (Fin.castSucc_lt_castSucc_iff.mpr hab)⟩`. Establish `hmem : v ∈ CapSp (subA E) (shf β fun j => L j.castSucc)`. Rewrite using `[mem_CapSp]`. Introduce `w`. Rewrite using `[quantumDetHighestWeight_holds V n (subA E) _ v gl' hHW' w]`.

Use `congr 1`. Unfold `cpol`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `k _`. Rewrite using `[hν]`.

Simplify using `[shf]`. Introduce `e`. Rewrite `hmem` using `[e]`. Conclude with `hv0 (by simpa using hmem)`. Introduce `M hM i hj`.

Use `hR V n E (shf β L) H.gl H.cap (shf β M) (hinj M hM) hM i (fun j e => hj j (by simpa [shf] using e))` as an intermediate fact. Rewrite `this` using `[shf_up]`. Then use the resulting hypothesis. Introduce `M hM i hj`. Use `hLo V n E (shf β L) H.gl H.cap (shf β M) (hinj M hM) hM i (fun j e => hj j (by` as an intermediate fact. Simplify using `only [shf] at e`.

Establish `e2 : ((M i - 1 : ℤ) : ℂ) = (L j : ℂ)`. Use `push_cast`. Take the linear combination `e`. Conclude with `e2))` after adjusting the coercions. Rewrite `this` using `[shf_down]`. Then use the resulting hypothesis.
-/
theorem sys_of (hSM : ExistsSingMax) (hCS : CapSing) (hSR : SubRel) (hR : RaiseNZ) (hLo : LowerNZ)
    {n : ℕ} {E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V} {β : ℂ} {L : Fin (n + 1) → ℤ}
    (H : Hyp E β L) : Sys L (fun M => CapSp (subA E) (shf β M) ≠ ⊥) := by
  have gl' : GlRel (subA E) := (hSR (Module.End ℂ V) n E H.gl).1
  have hinj : ∀ M : Fin n → ℤ, CapSp (subA E) (shf β M) ≠ ⊥ → Function.Injective (shf β M) :=
    fun M hM => (hCS V n (subA E) _ gl' hM).1
  refine ⟨H.anti, ?_, ?_, ?_, ?_, fun M i => fin_cap (subA E) β M i⟩
  · intro M hM a b hab
    exact hinj M hM (by simp [shf, hab])
  · have := H.irr.1
    obtain ⟨ν, v, -, hv0, hHW, -⟩ := hSM V (n + 1) E H.gl ⊤ (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
    have hvL : v ∈ CapSp E (shf β L) := mem_CapSp.mpr fun w => H.cap w v
    have hne : CapSp E (shf β L) ≠ ⊥ := fun e => hv0 (by rw [e] at hvL; simpa using hvL)
    have hν := (hCS V (n + 1) E _ H.gl hne).2 (sdec_shf β H.anti) ν v hvL hv0 hHW
    have hHW' : IsHW (subA E) (fun k => ν k.castSucc) v :=
      ⟨fun a => hHW.1 a.castSucc, fun a b hab => hHW.2 _ _ (Fin.castSucc_lt_castSucc_iff.mpr hab)⟩
    have hmem : v ∈ CapSp (subA E) (shf β fun j => L j.castSucc) := by
      rw [mem_CapSp]
      intro w
      rw [quantumDetHighestWeight_holds V n (subA E) _ v gl' hHW' w]
      congr 1
      unfold cpol
      apply Finset.prod_congr rfl
      intro k _
      rw [hν]
      simp [shf]
    intro e
    rw [e] at hmem
    exact hv0 (by simpa using hmem)
  · intro M hM i hj
    have := hR V n E (shf β L) H.gl H.cap (shf β M) (hinj M hM) hM i
      (fun j e => hj j (by simpa [shf] using e))
    rwa [shf_up] at this
  · intro M hM i hj
    have := hLo V n E (shf β L) H.gl H.cap (shf β M) (hinj M hM) hM i (fun j e => hj j (by
      simp only [shf] at e
      have e2 : ((M i - 1 : ℤ) : ℂ) = (L j : ℂ) := by
        push_cast
        linear_combination e
      exact_mod_cast e2))
    rwa [shf_down] at this

end Cap

end Formalism.FourierDecayAlt.P.BranchingSystems

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr BranchingSystems

/- English proof (translation)
Introduce `hSM hCS hSt hSR hCU hVD hR hLo V _ _ _ n E β L H`. Establish `S` using `sys_of hSM hCS hSR hR hLo H`. Take `⟨gl', hcov, hvec, -, hyy, hnn⟩` from `hSR (Module.End ℂ V) n E H.gl`. Use `⟨fun M hM => S.box M hM, ?_⟩` and prove the remaining obligations. Use `set V' : Submodule ℂ V := ⨆ (M : Fin n → ℤ) (_ : Box L M), CapSp (subA E) (shf β M) with hV'`.

Establish `hle : ∀ M, Box L M → CapSp (subA E) (shf β M) ≤ V'` using `fun M hM => le_iSup₂ (f := fun (M : Fin n → ℤ) (_ : Box L M) => CapSp (subA E) (shf β M)) M hM`. Establish `hstab : Stab E V'`. Introduce `a b`. It suffices to establish `h : V' ≤ V'.comap (E a b) from fun v hv => h hv`. Use `iSup₂_le fun M hM v hv => ?_` and prove the remaining obligations.

Rewrite using `[Submodule.mem_comap]`. Establish `hMinj : Function.Injective (shf β M)` using `(hCS V n (subA E) _ gl' (S.box M hM)).1`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `b using Fin.lastCases with`.

Consider the case `last => exact hle M hM ((hSt V n (subA E) _ gl').2 _ hnn v hv)`. Consider the case `cast x`. Take `⟨Φ, h1, h2, -⟩` from `hVD V n (subA E) (yK E) gl' hvec hyy (shf β M) hMinj v hv`. Express the relevant statement in the definitionally equal form `yK E x v ∈ V'`. Rewrite using `[← h1 x]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `h3` using `h2 i x`. Rewrite `h3` using `[shf_down]`. Distinguish the cases in `hi : M i = L i.succ + 1`. Use `not_not.mp (S.noDown M hM i hi)` as an intermediate fact.

Rewrite `h3` using `[this]`. Rewrite using `[(Submodule.mem_bot ℂ).mp h3]`. Conclude with `Submodule.zero_mem _`. Use `hle _ ?_ h3` and prove the remaining obligations. Introduce `j`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Use `hM j` as an intermediate fact. Simplify using `only [Function.update_self]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Function.update_of_ne hj]`. Conclude with `hM j`. Consider the case `cast y`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`.

Take `⟨Ψ, h1, h2, -⟩` from `hCU V n (subA E) (etaK E) gl' hcov (shf β M) hMinj v hv`. Express the relevant statement in the definitionally equal form `etaK E y v ∈ V'`. Rewrite using `[← h1 y]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `h3` using `h2 i y`.

Rewrite `h3` using `[shf_up]`. Distinguish the cases in `hi : M i = L i.castSucc`. Use `not_not.mp (S.noUp M hM i hi)` as an intermediate fact. Rewrite `h3` using `[this]`. Rewrite using `[(Submodule.mem_bot ℂ).mp h3]`.

Conclude with `Submodule.zero_mem _`. Use `hle _ ?_ h3` and prove the remaining obligations. Introduce `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Use `hM j` as an intermediate fact. Simplify using `only [Function.update_self]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Function.update_of_ne hj]`. Conclude with `hM j`.

Consider the case `cast x => exact hle M hM ((hSt V n (subA E) _ gl').1 y x v hv)`. Break down `H.irr.2 V' hstab with h | h` into its components or cases. It suffices to derive a contradiction. Establish `hB : Box L (fun j => L j.castSucc)` using `fun j => ⟨H.anti (Fin.castSucc_lt_succ), le_rfl⟩`. Conclude with `S.top (le_bot_iff.mp (h ▸ hle _ hB))`.

Conclude with `h`.
-/
theorem qr_decomp_of : Qr.ExistsSingMax → Qr.CapSing → Qr.CapStab → Qr.SubRel → Qr.CovUp → Qr.VecDown →
    Qr.RaiseNZ → Qr.LowerNZ → Qr.Decomp := by
  intro hSM hCS hSt hSR hCU hVD hR hLo V _ _ _ n E β L H
  have S := sys_of hSM hCS hSR hR hLo H
  obtain ⟨gl', hcov, hvec, -, hyy, hnn⟩ := hSR (Module.End ℂ V) n E H.gl
  refine ⟨fun M hM => S.box M hM, ?_⟩
  set V' : Submodule ℂ V := ⨆ (M : Fin n → ℤ) (_ : Box L M), CapSp (subA E) (shf β M) with hV'
  have hle : ∀ M, Box L M → CapSp (subA E) (shf β M) ≤ V' := fun M hM =>
    le_iSup₂ (f := fun (M : Fin n → ℤ) (_ : Box L M) => CapSp (subA E) (shf β M)) M hM
  have hstab : Stab E V' := by
    intro a b
    suffices h : V' ≤ V'.comap (E a b) from fun v hv => h hv
    refine iSup₂_le fun M hM v hv => ?_
    rw [Submodule.mem_comap]
    have hMinj : Function.Injective (shf β M) := (hCS V n (subA E) _ gl' (S.box M hM)).1
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => exact hle M hM ((hSt V n (subA E) _ gl').2 _ hnn v hv)
      | cast x =>
        obtain ⟨Φ, h1, h2, -⟩ := hVD V n (subA E) (yK E) gl' hvec hyy (shf β M) hMinj v hv
        change yK E x v ∈ V'
        rw [← h1 x]
        refine Submodule.sum_mem _ fun i _ => ?_
        have h3 := h2 i x
        rw [shf_down] at h3
        by_cases hi : M i = L i.succ + 1
        · have := not_not.mp (S.noDown M hM i hi)
          rw [this] at h3
          rw [(Submodule.mem_bot ℂ).mp h3]
          exact Submodule.zero_mem _
        · refine hle _ ?_ h3
          intro j
          by_cases hj : j = i
          · subst hj
            have := hM j
            simp only [Function.update_self]
            omega
          · rw [Function.update_of_ne hj]
            exact hM j
    | cast y =>
      induction b using Fin.lastCases with
      | last =>
        obtain ⟨Ψ, h1, h2, -⟩ := hCU V n (subA E) (etaK E) gl' hcov (shf β M) hMinj v hv
        change etaK E y v ∈ V'
        rw [← h1 y]
        refine Submodule.sum_mem _ fun i _ => ?_
        have h3 := h2 i y
        rw [shf_up] at h3
        by_cases hi : M i = L i.castSucc
        · have := not_not.mp (S.noUp M hM i hi)
          rw [this] at h3
          rw [(Submodule.mem_bot ℂ).mp h3]
          exact Submodule.zero_mem _
        · refine hle _ ?_ h3
          intro j
          by_cases hj : j = i
          · subst hj
            have := hM j
            simp only [Function.update_self]
            omega
          · rw [Function.update_of_ne hj]
            exact hM j
      | cast x => exact hle M hM ((hSt V n (subA E) _ gl').1 y x v hv)
  rcases H.irr.2 V' hstab with h | h
  · exfalso
    have hB : Box L (fun j => L j.castSucc) := fun j => ⟨H.anti (Fin.castSucc_lt_succ), le_rfl⟩
    exact S.top (le_bot_iff.mp (h ▸ hle _ hB))
  · exact h

end Formalism.FourierDecayAlt.P
