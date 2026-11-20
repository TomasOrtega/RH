import Mathlib

open TensorProduct

namespace UpperTheory.V.Loc.Thick

/- English proof (translation)
Break down `N with _ | k` into its components or cases. Use `haveI : Subsingleton R := subsingleton_of_zero_eq_one (by simpa using isUnit_zero_iff.1 (by simpa using hN))`. Conclude with `Subsingleton.elim _ _`. Set `U : Matrix n n R` to `∑ i ∈ Finset.range (k + 1), M ^ i * M' ^ (k + 1 - i)`. Establish `h1 : M * U = U * M'`.

Establish `e1 : M * U = ∑ i ∈ Finset.range (k + 1), M ^ (i + 1) * M' ^ (k + 1 + 1 - (i + 1))`. Simplify using `only [U, Finset.mul_sum, ← mul_assoc, ← pow_succ', Nat.add_sub_add_right]`. Establish `e2 : U * M' = ∑ i ∈ Finset.range (k + 1), M ^ i * M' ^ (k + 1 + 1 - i)`. Simplify using `only [U, Finset.sum_mul, mul_assoc, ← pow_succ]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations.

Use `Finset.mem_range.1 hi` as an intermediate fact. Use `congr 2`. Use linear arithmetic over natural numbers and integers. Establish `e3` using `(Finset.sum_range_succ' (fun i => M ^ i * M' ^ (k + 1 + 1 - i)) (k + 1)).symm.trans (Finset.sum_range_succ (fun i => M ^ i * M' ^ (k + 1 + 1 - i)) (k + 1))`. Simplify using `only [hM, pow_zero, one_mul, Nat.sub_zero, pow_succ M' (k + 1), hM', Nat.add_sub_cancel_left, pow_one] at e3`.

Rewrite using `[e1, e2]`. Conclude with `add_right_cancel e3`. Establish `h2 : p.mapMatrix U = p.mapMatrix (((k + 1 : ℕ) : R) • (1 : Matrix n n R))`. Establish `: ∀ i ∈ Finset.range (k + 1), p.mapMatrix (M ^ i * M' ^ (k + 1 - i)) = 1`. Introduce `i hi`.

Use `Finset.mem_range.1 hi` as an intermediate fact. Rewrite using `[map_mul, map_pow, h, ← map_pow, ← map_mul, ← pow_add, show i + (k + 1 - i) = k + 1 by omega, hM', map_one]`. Rewrite using `[map_sum, Finset.sum_congr rfl this, Nat.cast_smul_eq_nsmul, map_nsmul, map_one]`. Simplify using the standard rewrite rules. Establish `h3 : IsUnit U.det`.

Establish `e : p (U.det - ((k + 1 : ℕ) : R) ^ Fintype.card n) = 0`. Rewrite using `[map_sub, RingHom.map_det, h2, ← RingHom.map_det, Matrix.det_smul, Matrix.det_one, mul_one, sub_self]`. Use `(hp _ e).isUnit_add_right_of_commute (hN.pow (Fintype.card n)) (Commute.all _ _)` as an intermediate fact. Simplify using `using this`. Establish `h4 : M = U * M' * U⁻¹`.

Rewrite using `[← h1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h3, Matrix.mul_one]`. Rewrite using `[h4, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h3, Matrix.one_mul]`.
-/
theorem trace_eq {R R' n : Type} [CommRing R] [CommRing R'] [Fintype n] [DecidableEq n] (p : R →+* R')
    (hp : ∀ a, p a = 0 → IsNilpotent a) (N : ℕ) (hN : IsUnit (N : R)) (M M' : Matrix n n R)
    (hM : M ^ N = 1) (hM' : M' ^ N = 1) (h : p.mapMatrix M = p.mapMatrix M') : M.trace = M'.trace := by
  rcases N with _ | k
  · haveI : Subsingleton R := subsingleton_of_zero_eq_one (by simpa using isUnit_zero_iff.1 (by simpa using hN))
    exact Subsingleton.elim _ _
  let U : Matrix n n R := ∑ i ∈ Finset.range (k + 1), M ^ i * M' ^ (k + 1 - i)
  have h1 : M * U = U * M' := by
    have e1 : M * U = ∑ i ∈ Finset.range (k + 1), M ^ (i + 1) * M' ^ (k + 1 + 1 - (i + 1)) := by
      simp only [U, Finset.mul_sum, ← mul_assoc, ← pow_succ', Nat.add_sub_add_right]
    have e2 : U * M' = ∑ i ∈ Finset.range (k + 1), M ^ i * M' ^ (k + 1 + 1 - i) := by
      simp only [U, Finset.sum_mul, mul_assoc, ← pow_succ]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      congr 2
      omega
    have e3 := (Finset.sum_range_succ' (fun i => M ^ i * M' ^ (k + 1 + 1 - i)) (k + 1)).symm.trans
      (Finset.sum_range_succ (fun i => M ^ i * M' ^ (k + 1 + 1 - i)) (k + 1))
    simp only [hM, pow_zero, one_mul, Nat.sub_zero, pow_succ M' (k + 1), hM', Nat.add_sub_cancel_left,
      pow_one] at e3
    rw [e1, e2]
    exact add_right_cancel e3
  have h2 : p.mapMatrix U = p.mapMatrix (((k + 1 : ℕ) : R) • (1 : Matrix n n R)) := by
    have : ∀ i ∈ Finset.range (k + 1), p.mapMatrix (M ^ i * M' ^ (k + 1 - i)) = 1 := by
      intro i hi
      have := Finset.mem_range.1 hi
      rw [map_mul, map_pow, h, ← map_pow, ← map_mul, ← pow_add, show i + (k + 1 - i) = k + 1 by omega, hM', map_one]
    rw [map_sum, Finset.sum_congr rfl this, Nat.cast_smul_eq_nsmul, map_nsmul, map_one]
    simp
  have h3 : IsUnit U.det := by
    have e : p (U.det - ((k + 1 : ℕ) : R) ^ Fintype.card n) = 0 := by
      rw [map_sub, RingHom.map_det, h2, ← RingHom.map_det, Matrix.det_smul, Matrix.det_one, mul_one, sub_self]
    have := (hp _ e).isUnit_add_right_of_commute (hN.pow (Fintype.card n)) (Commute.all _ _)
    simpa using this
  have h4 : M = U * M' * U⁻¹ := by
    rw [← h1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h3, Matrix.mul_one]
  rw [h4, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h3, Matrix.one_mul]

variable {Q E B : Type} [Field Q] [Field E] [CommRing B] [Algebra Q E] [Algebra Q B] [Algebra E B]
  [IsScalarTower Q E B] (π : B →ₐ[E] E)

/- English proof (translation)
Use `haveI : IsNoetherianRing B := isNoetherian_of_tower E inferInstance`. Establish `hn : IsNilpotent (RingHom.ker π)` using `(Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)).2 fun a ha => hπ a ha`. Establish `h1 : ¬ J ≤ RingHom.ker π * J`. Introduce `h`. Take `⟨k, hk⟩` from `hn`.

Establish `: ∀ i, J ≤ RingHom.ker π ^ i * J`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih => exact ih.trans (by rw [pow_succ, mul_assoc]; exact Ideal.mul_mono_right h)`.

Conclude with `hJ (by simpa [hk] using this k)`. Take `⟨t, ht, ht'⟩` from `Set.not_subset.1 h1`. Take `⟨f, hf1, hf⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem (p := (RingHom.ker π * J).restrictScalars E) ht' inferInstance`. Establish `hf0 : ∀ x ∈ RingHom.ker π * J, f x = 0` using `fun x hx => (Submodule.mem_bot E).1 (hf ▸ Submodule.mem_map_of_mem hx)`. Establish `hm : ∀ j ∈ J, ∀ a, f (a * j) = π a * f j`.

Introduce `j hj a`. Use `hf0 ((a - algebraMap E B (π a)) * j) (Ideal.mul_mem_mul (by simp [RingHom.mem_ker]) hj)` as an intermediate fact. Rewrite `this` using `[sub_mul, map_sub, ← Algebra.smul_def, map_smul, sub_eq_zero]`. Conclude with `this`. Set `J' : Ideal B` to `{ carrier := {j | j ∈ J ∧ f j = 0} zero_mem' := ⟨J.zero_mem, map_zero f⟩ add_mem' := fun ha hb => ⟨J.add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2, add_zero]⟩ smul_mem' := fun c j hj => ⟨J.smul_mem c hj.1, by rw [smul_eq_mul, hm j hj.1, hj.2, mul_zero]⟩ }`.

Use `⟨J', t, (f t)⁻¹ • f, lt_of_le_of_ne (fun j hj => hj.1) fun h => hf1 (show t ∈ J' from h ▸ ht).2, ht, by simp [hf1], fun j hj a => by simp [hm j hj a, mul_left_comm], fun j hj h => ⟨hj, by simpa [hf1] using h⟩⟩` and prove the remaining obligations.
-/
theorem step [Module.Finite E B] (hπ : ∀ a, π a = 0 → IsNilpotent a) (J : Ideal B) (hJ : J ≠ ⊥) :
    ∃ (J' : Ideal B) (t : B) (f : B →ₗ[E] E), J' < J ∧ t ∈ J ∧ f t = 1 ∧ (∀ j ∈ J, ∀ a, f (a * j) = π a * f j) ∧
      ∀ j ∈ J, f j = 0 → j ∈ J' := by
  haveI : IsNoetherianRing B := isNoetherian_of_tower E inferInstance
  have hn : IsNilpotent (RingHom.ker π) :=
    (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)).2 fun a ha => hπ a ha
  have h1 : ¬ J ≤ RingHom.ker π * J := by
    intro h
    obtain ⟨k, hk⟩ := hn
    have : ∀ i, J ≤ RingHom.ker π ^ i * J := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => exact ih.trans (by rw [pow_succ, mul_assoc]; exact Ideal.mul_mono_right h)
    exact hJ (by simpa [hk] using this k)
  obtain ⟨t, ht, ht'⟩ := Set.not_subset.1 h1
  obtain ⟨f, hf1, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
    (p := (RingHom.ker π * J).restrictScalars E) ht' inferInstance
  have hf0 : ∀ x ∈ RingHom.ker π * J, f x = 0 := fun x hx =>
    (Submodule.mem_bot E).1 (hf ▸ Submodule.mem_map_of_mem hx)
  have hm : ∀ j ∈ J, ∀ a, f (a * j) = π a * f j := by
    intro j hj a
    have := hf0 ((a - algebraMap E B (π a)) * j) (Ideal.mul_mem_mul (by simp [RingHom.mem_ker]) hj)
    rw [sub_mul, map_sub, ← Algebra.smul_def, map_smul, sub_eq_zero] at this
    exact this
  let J' : Ideal B :=
    { carrier := {j | j ∈ J ∧ f j = 0}
      zero_mem' := ⟨J.zero_mem, map_zero f⟩
      add_mem' := fun ha hb => ⟨J.add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2, add_zero]⟩
      smul_mem' := fun c j hj => ⟨J.smul_mem c hj.1, by rw [smul_eq_mul, hm j hj.1, hj.2, mul_zero]⟩ }
  refine ⟨J', t, (f t)⁻¹ • f, lt_of_le_of_ne (fun j hj => hj.1) fun h => hf1 (show t ∈ J' from h ▸ ht).2, ht,
    by simp [hf1], fun j hj a => by simp [hm j hj a, mul_left_comm], fun j hj h => ⟨hj, by simpa [hf1] using h⟩⟩

structure Red {X X' : Type} [AddCommGroup X] [Module B X] [Module Q X] [AddCommGroup X'] [Module E X'] [Module Q X']
    (p : X →ₗ[Q] X') (Λ : (B →ₗ[E] E) → X →ₗ[Q] X') : Prop where
  surj : Function.Surjective p
  smul : ∀ a x, p (a • x) = π a • p x
  ker : ∀ x, p x = 0 → x ∈ (RingHom.ker π • ⊤ : Submodule B X)
  form : ∀ (f : B →ₗ[E] E) j, (∀ a, f (a * j) = π a * f j) → ∀ x, Λ f (j • x) = f j • p x

variable {π}

section

variable {X X' : Type} [AddCommGroup X] [Module B X] [Module Q X] [AddCommGroup X'] [Module E X'] [Module Q X']
  {p : X →ₗ[Q] X'} {Λ : (B →ₗ[E] E) → X →ₗ[Q] X'}

omit [Algebra Q E] [Algebra Q B] [IsScalarTower Q E B] in
/- English proof (translation)
Establish `h1 : ∃ z, p z = Λ f y ∧ y - t • z ∈ (J' • ⊤ : Submodule B X)`. Use `Submodule.smul_induction_on hy (fun j hj w _ => ⟨algebraMap E B (f j) • w, ?_, ?_⟩) ?_` and prove the remaining obligations. Rewrite using `[h.smul, h.form f j (hf j hj)]`. Simplify using the standard rewrite rules. Rewrite using `[smul_smul, ← sub_smul]`.

Use `Submodule.smul_mem_smul (hJ _ (J.sub_mem hj (J.mul_mem_right _ ht)) ?_) trivial` and prove the remaining obligations. Rewrite using `[map_sub, mul_comm, hf t ht, hft]`. Simplify using the standard rewrite rules. Introduce and unpack `a b ⟨z, h1, h2⟩ ⟨w, h3, h4⟩`. Use `⟨z + w, by rw [map_add, map_add, h1, h3], ?_⟩` and prove the remaining obligations.

Use `Submodule.add_mem _ h2 h4 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[smul_add]`. Normalize the expressions using the abelian group laws. Take `⟨z, h1, h2⟩` from `h1`. Establish `h3 : t • (z - x) ∈ (J' • ⊤ : Submodule B X)`.

Use `Submodule.smul_induction_on (p := fun w => t • w ∈ (J' • ⊤ : Submodule B X)) (h.ker (z - x) (by rw [map_sub, h1, hx, sub_self])) (fun j hj w _ => ?_) fun a b ha hb => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`. Use `Submodule.smul_mem_smul (hJ _ (J.mul_mem_right _ ht) ?_) trivial` and prove the remaining obligations. Rewrite using `[mul_comm, hf t ht, RingHom.mem_ker.1 hj, zero_mul]`. Rewrite using `[smul_add]`.

Conclude with `Submodule.add_mem _ ha hb`. Use `Submodule.add_mem _ h2 h3 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[smul_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem Red.desc (h : Red π p Λ) {J J' : Ideal B} {t : B} {f : B →ₗ[E] E} (ht : t ∈ J)
    (hft : f t = 1) (hf : ∀ j ∈ J, ∀ a, f (a * j) = π a * f j) (hJ : ∀ j ∈ J, f j = 0 → j ∈ J')
    {y : X} (hy : y ∈ (J • ⊤ : Submodule B X)) {x : X} (hx : p x = Λ f y) :
    y - t • x ∈ (J' • ⊤ : Submodule B X) := by
  have h1 : ∃ z, p z = Λ f y ∧ y - t • z ∈ (J' • ⊤ : Submodule B X) := by
    refine Submodule.smul_induction_on hy (fun j hj w _ => ⟨algebraMap E B (f j) • w, ?_, ?_⟩) ?_
    · rw [h.smul, h.form f j (hf j hj)]; simp
    · rw [smul_smul, ← sub_smul]
      refine Submodule.smul_mem_smul (hJ _ (J.sub_mem hj (J.mul_mem_right _ ht)) ?_) trivial
      rw [map_sub, mul_comm, hf t ht, hft]; simp
    · rintro a b ⟨z, h1, h2⟩ ⟨w, h3, h4⟩
      refine ⟨z + w, by rw [map_add, map_add, h1, h3], ?_⟩
      convert Submodule.add_mem _ h2 h4 using 1
      rw [smul_add]; abel
  obtain ⟨z, h1, h2⟩ := h1
  have h3 : t • (z - x) ∈ (J' • ⊤ : Submodule B X) := by
    refine Submodule.smul_induction_on (p := fun w => t • w ∈ (J' • ⊤ : Submodule B X))
      (h.ker (z - x) (by rw [map_sub, h1, hx, sub_self])) (fun j hj w _ => ?_) fun a b ha hb => ?_
    · rw [smul_smul]
      refine Submodule.smul_mem_smul (hJ _ (J.mul_mem_right _ ht) ?_) trivial
      rw [mul_comm, hf t ht, RingHom.mem_ker.1 hj, zero_mul]
    · rw [smul_add]; exact Submodule.add_mem _ ha hb
  convert Submodule.add_mem _ h2 h3 using 1
  rw [smul_sub]; abel

omit [Algebra Q E] [Algebra Q B] [IsScalarTower Q E B] in

/- English proof (translation)
Use `haveI : IsArtinianRing B := isArtinian_of_tower E inferInstance`. Establish `hs : ∀ J : Ideal B, ∀ y ∈ S, y ∈ (J • ⊤ : Submodule B X) → ∃ c, y - φ c ∈ T`. Introduce `J`. Proceed by induction on `J using WellFoundedLT.induction with`. Consider the case `ind J ih`.

Introduce `y hy hyJ`. Distinguish the cases in `hJ : J = ⊥`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite `hyJ` using `[hJ, Submodule.bot_smul, Submodule.mem_bot]`. Simplify using `[hyJ]`.

Take `⟨J', t, f, hlt, ht, hft, hf, hJ'⟩` from `step π hπ J hJ`. Take `⟨c', hc', -⟩` from `h _ ((hΛ f J hf y hyJ).1 hy)`. Take `⟨z, hz, e⟩` from `hT _ hc'`. Take `⟨c, rfl⟩` from `hC.surj c'`. Take `⟨d, hd⟩` from `ih J' hlt (y - t • (φ c + z)) (S.sub_mem hy (S.smul_mem _ (S.add_mem (hφS c) (hTS hz)))) (hX.desc ht hft hf hJ' hyJ (by rw [map_add, hφ, e]; abel))`.

Use `⟨d + t • c, ?_⟩` and prove the remaining obligations. Use `T.add_mem hd (T.smul_mem t hz) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_add, map_smul, smul_add]`. Normalize the expressions using the abelian group laws. Establish `hi : ∀ J : Ideal B, ∀ c ∈ (J • ⊤ : Submodule B C), φ c ∈ T → c = 0`.

Introduce `J`. Proceed by induction on `J using WellFoundedLT.induction with`. Consider the case `ind J ih`. Introduce `c hc hcT`. Distinguish the cases in `hJ : J = ⊥`.

Rewrite `hc` using `[hJ, Submodule.bot_smul, Submodule.mem_bot]`. Then use the resulting hypothesis. Take `⟨J', t, f, hlt, ht, hft, hf, hJ'⟩` from `step π hπ J hJ`. Establish `e : Λ f (φ c) = φ' (Γ f c) ∧ φ c ∈ (J • ⊤ : Submodule B X)`. Use `Submodule.smul_induction_on (p := fun c => Λ f (φ c) = φ' (Γ f c) ∧ φ c ∈ (J • ⊤ : Submodule B X)) hc (fun j hj w _ => ⟨?_, ?_⟩) fun a b ha hb => ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, hX.form f j (hf j hj), hC.form f j (hf j hj), map_smul, hφ]`.

Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem_smul hj trivial`. Simplify using `only [map_add, ha.1, hb.1]`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ ha.2 hb.2`.

Establish `e2 : Γ f c = 0` using `(h 0 S'.zero_mem).unique (by rw [← e.1, zero_sub]; exact T'.neg_mem ((hΛ f J hf _ e.2).2 hcT)) (by simp)`. Use `ih J' hlt c ?_ hcT` and prove the remaining obligations. Simplify using `using hC.desc ht hft hf hJ' hc (x := 0) (by rw [e2, map_zero])`. Introduce `y hy`. Take `⟨c, hc⟩` from `hs ⊤ y hy (by simp)`.

Use `⟨c, hc, fun d hd => sub_eq_zero.1 (hi ⊤ _ (by simp) ?_)⟩` and prove the remaining obligations. Use `T.sub_mem hc hd using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem lift_param [Module.Finite E B] (hπ : ∀ a, π a = 0 → IsNilpotent a)
    {C C' : Type} [AddCommGroup C] [Module B C] [Module Q C] [AddCommGroup C'] [Module E C'] [Module Q C']
    {q : C →ₗ[Q] C'} {Γ : (B →ₗ[E] E) → C →ₗ[Q] C'} (hX : Red π p Λ) (hC : Red π q Γ)
    (φ : C →ₗ[B] X) (φ' : C' →ₗ[E] X') (hφ : ∀ c, p (φ c) = φ' (q c))
    (S T : Submodule B X) (S' T' : Submodule E X') (hTS : T ≤ S) (hφS : ∀ c, φ c ∈ S)
    (hT : ∀ y ∈ T', ∃ x ∈ T, p x = y)
    (hΛ : ∀ (f : B →ₗ[E] E) (J : Ideal B), (∀ j ∈ J, ∀ a, f (a * j) = π a * f j) →
      ∀ y ∈ (J • ⊤ : Submodule B X), (y ∈ S → Λ f y ∈ S') ∧ (y ∈ T → Λ f y ∈ T'))
    (h : ∀ y ∈ S', ∃! c, y - φ' c ∈ T') : ∀ y ∈ S, ∃! c, y - φ c ∈ T := by
  haveI : IsArtinianRing B := isArtinian_of_tower E inferInstance
  have hs : ∀ J : Ideal B, ∀ y ∈ S, y ∈ (J • ⊤ : Submodule B X) → ∃ c, y - φ c ∈ T := by
    intro J
    induction J using WellFoundedLT.induction with
    | ind J ih =>
    intro y hy hyJ
    by_cases hJ : J = ⊥
    · refine ⟨0, ?_⟩
      rw [hJ, Submodule.bot_smul, Submodule.mem_bot] at hyJ
      simp [hyJ]
    obtain ⟨J', t, f, hlt, ht, hft, hf, hJ'⟩ := step π hπ J hJ
    obtain ⟨c', hc', -⟩ := h _ ((hΛ f J hf y hyJ).1 hy)
    obtain ⟨z, hz, e⟩ := hT _ hc'
    obtain ⟨c, rfl⟩ := hC.surj c'
    obtain ⟨d, hd⟩ := ih J' hlt (y - t • (φ c + z))
      (S.sub_mem hy (S.smul_mem _ (S.add_mem (hφS c) (hTS hz))))
      (hX.desc ht hft hf hJ' hyJ (by rw [map_add, hφ, e]; abel))
    refine ⟨d + t • c, ?_⟩
    convert T.add_mem hd (T.smul_mem t hz) using 1
    rw [map_add, map_smul, smul_add]; abel
  have hi : ∀ J : Ideal B, ∀ c ∈ (J • ⊤ : Submodule B C), φ c ∈ T → c = 0 := by
    intro J
    induction J using WellFoundedLT.induction with
    | ind J ih =>
    intro c hc hcT
    by_cases hJ : J = ⊥
    · rwa [hJ, Submodule.bot_smul, Submodule.mem_bot] at hc
    obtain ⟨J', t, f, hlt, ht, hft, hf, hJ'⟩ := step π hπ J hJ
    have e : Λ f (φ c) = φ' (Γ f c) ∧ φ c ∈ (J • ⊤ : Submodule B X) := by
      refine Submodule.smul_induction_on
        (p := fun c => Λ f (φ c) = φ' (Γ f c) ∧ φ c ∈ (J • ⊤ : Submodule B X)) hc
        (fun j hj w _ => ⟨?_, ?_⟩) fun a b ha hb => ⟨?_, ?_⟩
      · rw [map_smul, hX.form f j (hf j hj), hC.form f j (hf j hj), map_smul, hφ]
      · rw [map_smul]; exact Submodule.smul_mem_smul hj trivial
      · simp only [map_add, ha.1, hb.1]
      · rw [map_add]; exact Submodule.add_mem _ ha.2 hb.2
    have e2 : Γ f c = 0 := (h 0 S'.zero_mem).unique
      (by rw [← e.1, zero_sub]; exact T'.neg_mem ((hΛ f J hf _ e.2).2 hcT)) (by simp)
    refine ih J' hlt c ?_ hcT
    simpa using hC.desc ht hft hf hJ' hc (x := 0) (by rw [e2, map_zero])
  intro y hy
  obtain ⟨c, hc⟩ := hs ⊤ y hy (by simp)
  refine ⟨c, hc, fun d hd => sub_eq_zero.1 (hi ⊤ _ (by simp) ?_)⟩
  convert T.sub_mem hc hd using 1
  rw [map_sub]; abel

omit [Algebra Q E] [Algebra Q B] [IsScalarTower Q E B] in
/- English proof (translation)
Use `choose x hx using fun i => h.surj (y i)`. Conclude with `⟨x, funext hx⟩`. Use `smul a x := funext fun i => h.smul a (x i)`. Use `ker x hx := by classical`. Rewrite using `[← Finset.univ_sum_single x]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Use `Submodule.smul_induction_on (p := fun w => (Pi.single i w : n → X) ∈ (RingHom.ker π • ⊤ : Submodule B (n → X))) (h.ker (x i) (congrFun hx i)) (fun j hj w _ => ?_) fun a b ha hb => ?_` and prove the remaining obligations. Rewrite using `[Pi.single_smul]`. Conclude with `Submodule.smul_mem_smul hj trivial`. Rewrite using `[Pi.single_add]`.

Conclude with `Submodule.add_mem _ ha hb`. Use `form f j hf x := funext fun i => h.form f j hf (x i)`.
-/
theorem Red.pi (h : Red π p Λ) (n : Type) [Fintype n] : Red π (p.compLeft n) fun f => (Λ f).compLeft n where
  surj y := by
    choose x hx using fun i => h.surj (y i)
    exact ⟨x, funext hx⟩
  smul a x := funext fun i => h.smul a (x i)
  ker x hx := by
    classical
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    refine Submodule.smul_induction_on
      (p := fun w => (Pi.single i w : n → X) ∈ (RingHom.ker π • ⊤ : Submodule B (n → X)))
      (h.ker (x i) (congrFun hx i)) (fun j hj w _ => ?_) fun a b ha hb => ?_
    · rw [Pi.single_smul]; exact Submodule.smul_mem_smul hj trivial
    · rw [Pi.single_add]; exact Submodule.add_mem _ ha hb
  form f j hf x := funext fun i => h.form f j hf (x i)

variable [IsScalarTower Q B X] [IsScalarTower Q E X']

omit [IsScalarTower Q E B] in
/- English proof (translation)
The claim follows from `LinearMap.rTensor_surjective P h.surj smul a x := by induction x using TensorProduct.induction_on with | zero => simp | tmul v b => simp only [smul_tmul', LinearMap.rTensor_tmul, h.smul] | add x y hx hy => simp only [smul_add, map_add, hx, hy] ker x hx := by obtain ⟨y, rfl⟩ := (r …`.
-/
theorem Red.tensor (h : Red π p Λ) (P : Type) [AddCommGroup P] [Module Q P] :
    Red π (p.rTensor P) fun f => (Λ f).rTensor P where
  surj := LinearMap.rTensor_surjective P h.surj
  smul a x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp only [smul_tmul', LinearMap.rTensor_tmul, h.smul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  ker x hx := by
    obtain ⟨y, rfl⟩ := (rTensor_exact P (LinearMap.exact_subtype_ker_map p) h.surj x).1 hx
    clear hx
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [LinearMap.rTensor_tmul]
      refine Submodule.smul_induction_on
        (p := fun w => w ⊗ₜ[Q] b ∈ (RingHom.ker π • ⊤ : Submodule B (X ⊗[Q] P)))
        (h.ker v v.2) (fun j hj w _ => ?_) fun a b ha hb => ?_
      · rw [← smul_tmul']; exact Submodule.smul_mem_smul hj trivial
      · rw [add_tmul]; exact Submodule.add_mem _ ha hb
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  form f j hf x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp only [smul_tmul', LinearMap.rTensor_tmul, h.form f j hf]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

omit [Algebra Q E] [Algebra Q B] [IsScalarTower Q E B] [IsScalarTower Q B X] [IsScalarTower Q E X'] in
/- English proof (translation)
Use `Submodule.smul_induction_on (p := fun y => Λ f (g y) = g' (Λ f y)) hy (fun j hj w _ => ?_) fun a b ha hb => ?_` and prove the remaining obligations. Rewrite using `[map_smul, h.form f j (hf j hj), h.form f j (hf j hj), map_smul, hg]`. Simplify using `only [map_add, ha, hb]`.
-/
theorem Red.comm (h : Red π p Λ) (g : X →ₗ[B] X) (g' : X' →ₗ[E] X') (hg : ∀ x, p (g x) = g' (p x))
    {f : B →ₗ[E] E} {J : Ideal B} (hf : ∀ j ∈ J, ∀ a, f (a * j) = π a * f j)
    {y : X} (hy : y ∈ (J • ⊤ : Submodule B X)) : Λ f (g y) = g' (Λ f y) := by
  refine Submodule.smul_induction_on (p := fun y => Λ f (g y) = g' (Λ f y)) hy (fun j hj w _ => ?_)
    fun a b ha hb => ?_
  · rw [map_smul, h.form f j (hf j hj), h.form f j (hf j hj), map_smul, hg]
  · simp only [map_add, ha, hb]

end

variable (Q π) in
/- English proof (translation)
Assemble the required witnesses or components as `⟨algebraMap E B y, by simp⟩ smul a x := by simp ker x hx := by have := Submodule.smul_mem_smul (I := RingHom.ker π) (N := (⊤ : Submodule B B)) (r := x) (n := 1) hx trivial simpa using this form f j hf x := by change f (j * x) = f j * π x rw [mul_comm j, hf, mul_comm]`.
-/
theorem red_self : Red π (π.toLinearMap.restrictScalars Q) fun f => f.restrictScalars Q where
  surj y := ⟨algebraMap E B y, by simp⟩
  smul a x := by simp
  ker x hx := by
    have := Submodule.smul_mem_smul (I := RingHom.ker π) (N := (⊤ : Submodule B B)) (r := x) (n := 1) hx trivial
    simpa using this
  form f j hf x := by
    change f (j * x) = f j * π x
    rw [mul_comm j, hf, mul_comm]

section Sm

variable {A V : Type} [CommRing A] [Algebra Q A] [AddCommGroup V] [Module A V] [Module Q V] [IsScalarTower Q A V]
  {F P : Type} [Field F] [Algebra Q F] [CommRing P] [Algebra Q P] [Algebra F P] [IsScalarTower Q F P]

variable (V P) in

noncomputable def sm : A ⊗[Q] F →ₗ[Q] Module.End Q (V ⊗[Q] P) :=
  (TensorProduct.homTensorHomMap (RingHom.id Q) V P V P).comp
    (TensorProduct.map (Algebra.lsmul Q Q V : A →ₐ[Q] Module.End Q V).toLinearMap
      (Algebra.lsmul Q Q P : F →ₐ[Q] Module.End Q P).toLinearMap)

/- English proof (translation)
Simplify using `[sm]`.
-/
theorem sm_tmul (a : A) (k : F) (v : V) (b : P) : sm V P (a ⊗ₜ[Q] k) (v ⊗ₜ[Q] b) = (a • v) ⊗ₜ[Q] (k • b) := by
  simp [sm]

/- English proof (translation)
Proceed by induction on `c using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [add_mul, map_add, LinearMap.add_apply, hx, hy]`. Consider the case `tmul a k`. Proceed by induction on `d using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [mul_add, map_add, LinearMap.add_apply, hx, hy]`. Consider the case `tmul a' k'`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul v b => simp only [Algebra.TensorProduct.tmul_mul_tmul, sm_tmul, mul_smul]`.
-/
theorem sm_mul (c d : A ⊗[Q] F) (y : V ⊗[Q] P) : sm V P (c * d) y = sm V P c (sm V P d y) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add, LinearMap.add_apply, hx, hy]
  | tmul a k =>
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [mul_add, map_add, LinearMap.add_apply, hx, hy]
  | tmul a' k' =>
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b => simp only [Algebra.TensorProduct.tmul_mul_tmul, sm_tmul, mul_smul]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, smul_add, hx, hy]`. Consider the case `tmul v b => simp only [sm_tmul, one_smul, smul_tmul']`.
-/
theorem sm_left (a : A) (y : V ⊗[Q] P) : sm V P (a ⊗ₜ[Q] (1 : F)) y = a • y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul v b => simp only [sm_tmul, one_smul, smul_tmul']

/- English proof (translation)
Rewrite using `[Algebra.TensorProduct.one_def, sm_left, one_smul]`.
-/
theorem sm_one (y : V ⊗[Q] P) : sm V P (1 : A ⊗[Q] F) y = y := by
  rw [Algebra.TensorProduct.one_def, sm_left, one_smul]

/- English proof (translation)
Rewrite using `[Algebra.smul_def, sm_mul, Algebra.TensorProduct.algebraMap_apply, sm_left]`. Both sides reduce to the same expression.
-/
theorem sm_smul (a : A) (c : A ⊗[Q] F) (y : V ⊗[Q] P) : sm V P (a • c) y = a • sm V P c y := by
  rw [Algebra.smul_def, sm_mul, Algebra.TensorProduct.algebraMap_apply, sm_left]
  rfl

/- English proof (translation)
Proceed by induction on `c using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]`. Consider the case `tmul a k`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul v b => simp only [sm_tmul, AlgebraTensorModule.map_tmul, map_smul, hu]`.
-/
theorem act_sm (g : V →ₗ[A] V) (u : P →ₗ[Q] P) (hu : ∀ (k : F) b, u (k • b) = k • u b) (c : A ⊗[Q] F)
    (y : V ⊗[Q] P) :
    AlgebraTensorModule.map g u (sm V P c y) = sm V P c (AlgebraTensorModule.map g u y) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul a k =>
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b => simp only [sm_tmul, AlgebraTensorModule.map_tmul, map_smul, hu]

/- English proof (translation)
Take `⟨y, rfl⟩` from `hy`. Proceed by induction on `c using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, LinearMap.add_apply]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `tmul a k`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `tmul v b => exact ⟨(a • v) ⊗ₜ ⟨k • b.1, hΦ k _ b.2⟩, by simp [sm_tmul]⟩`.
-/
theorem sm_mem_range (Φ : Submodule Q P) (hΦ : ∀ (k : F), ∀ b ∈ Φ, k • b ∈ Φ) (c : A ⊗[Q] F) {y : V ⊗[Q] P}
    (hy : y ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[A] V) Φ.subtype)) :
    sm V P c y ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[A] V) Φ.subtype) := by
  obtain ⟨y, rfl⟩ := hy
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hy
  | tmul a k =>
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
  | tmul v b => exact ⟨(a • v) ⊗ₜ ⟨k • b.1, hΦ k _ b.2⟩, by simp [sm_tmul]⟩

noncomputable def par (F : Type) [Field F] [Algebra Q F] [Algebra F P] [IsScalarTower Q F P] {ι : Type} [Fintype ι]
    (x : ι → V ⊗[Q] P) : (ι → A ⊗[Q] F) →ₗ[A] V ⊗[Q] P where
  toFun c := ∑ a, sm V P (c a) (x a)
  map_add' c d := by simp only [Pi.add_apply, map_add, LinearMap.add_apply, Finset.sum_add_distrib]
  map_smul' a c := by simp only [Pi.smul_apply, sm_smul, Finset.smul_sum, RingHom.id_apply]

variable {A' V' : Type} [CommRing A'] [Algebra Q A'] [AddCommGroup V'] [Module A' V'] [Module Q V']
  [IsScalarTower Q A' V']

/- English proof (translation)
Proceed by induction on `c using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]`. Consider the case `tmul a k`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul v b => simp only [sm_tmul, LinearMap.rTensor_tmul, hp]`.
-/
theorem rTensor_sm (q : A →ₗ[Q] A') (p : V →ₗ[Q] V') (hp : ∀ a v, p (a • v) = q a • p v) (c : A ⊗[Q] F)
    (y : V ⊗[Q] P) : p.rTensor P (sm V P c y) = sm V' P (q.rTensor F c) (p.rTensor P y) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul a k =>
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b => simp only [sm_tmul, LinearMap.rTensor_tmul, hp]

omit [Algebra Q P] in
/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul v b => simp only [AlgebraTensorModule.map_tmul, LinearMap.rTensor_tmul, hp]`.
-/
theorem rTensor_act [Module Q P] (p : V →ₗ[Q] V') (g : V →ₗ[A] V) (g' : V' →ₗ[A'] V')
    (hp : ∀ v, p (g v) = g' (p v)) (u : P →ₗ[Q] P) (y : V ⊗[Q] P) :
    p.rTensor P (AlgebraTensorModule.map g u y) = AlgebraTensorModule.map g' u (p.rTensor P y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b => simp only [AlgebraTensorModule.map_tmul, LinearMap.rTensor_tmul, hp]

/- English proof (translation)
Take `⟨y, rfl⟩` from `hy`. Use `⟨p.rTensor _ y, ?_⟩` and prove the remaining obligations. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.

Consider the case `tmul v b => simp`.
-/
theorem rTensor_mem_range (p : V →ₗ[Q] V') (Φ : Submodule Q P) {y : V ⊗[Q] P}
    (hy : y ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[A] V) Φ.subtype)) :
    p.rTensor P y ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V' →ₗ[A'] V') Φ.subtype) := by
  obtain ⟨y, rfl⟩ := hy
  refine ⟨p.rTensor _ y, ?_⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b => simp

end Sm

end UpperTheory.V.Loc.Thick
