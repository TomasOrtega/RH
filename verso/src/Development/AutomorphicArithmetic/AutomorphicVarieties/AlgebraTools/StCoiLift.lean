import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InvAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqLagIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IdemLiftComplete

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

section aux

variable {B E : Type} [CommRing B] [Ring E] [Algebra B E]

/- English proof (translation)
Establish `h : (J • (⊤ : Submodule B E)).map f ≤ J • ⊤`. Rewrite using `[Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl le_top`. Conclude with `h ⟨x, hx, rfl⟩`.
-/
private theorem scl_map_mem (J : Ideal B) (f : E →ₗ[B] E) {x : E} (hx : x ∈ J • (⊤ : Submodule B E)) :
    f x ∈ J • (⊤ : Submodule B E) := by
  have h : (J • (⊤ : Submodule B E)).map f ≤ J • ⊤ := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact h ⟨x, hx, rfl⟩

/- English proof (translation)
Conclude with `IsHausdorff.haus' (I := I) x (fun N => SModEq.zero.2 (hx N))`.
-/
private theorem scl_haus (I : Ideal B) [IsAdicComplete I E] {x : E}
    (hx : ∀ N : ℕ, x ∈ I ^ N • (⊤ : Submodule B E)) : x = 0 := by
  exact IsHausdorff.haus' (I := I) x (fun N => SModEq.zero.2 (hx N))

/- English proof (translation)
Establish `h0 : ∀ N : ℕ, f e - e ∈ I ^ N • (⊤ : Submodule B E)`. Introduce `N`. Take `⟨w, hw, hew⟩` from `h N`. Establish `h1` using `scl_map_mem (I ^ N) f hew`. Establish `h2 : f e - e = f (e - w) - (e - w)`.

Rewrite using `[map_sub, hw]`. Normalize the expressions using the abelian group laws. Rewrite using `[h2]`. Conclude with `Submodule.sub_mem _ h1 hew`. Conclude with `sub_eq_zero.1 (scl_haus I h0)`.
-/
private theorem scl_fix (I : Ideal B) [IsAdicComplete I E] (f : E →ₗ[B] E) {e : E}
    (h : ∀ N : ℕ, ∃ w, f w = w ∧ e - w ∈ I ^ N • (⊤ : Submodule B E)) : f e = e := by
  have h0 : ∀ N : ℕ, f e - e ∈ I ^ N • (⊤ : Submodule B E) := by
    intro N
    obtain ⟨w, hw, hew⟩ := h N
    have h1 := scl_map_mem (I ^ N) f hew
    have h2 : f e - e = f (e - w) - (e - w) := by
      rw [map_sub, hw]
      abel
    rw [h2]
    exact Submodule.sub_mem _ h1 hew
  exact sub_eq_zero.1 (scl_haus I h0)

/- English proof (translation)
Establish `h` using `T.st_mul (T.st 1) 1`. Rewrite `h` using `[mul_one, T.st_st, mul_one]`. Conclude with `h.symm`.
-/
private theorem scl_st_one (T : TrInv B E) : T.st 1 = 1 := by
  have h := T.st_mul (T.st 1) 1
  rw [mul_one, T.st_st, mul_one] at h
  exact h.symm

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, scl_st_one]`. Consider the case `succ n ih => rw [pow_succ, T.st_mul, hz, ih, ← pow_succ', pow_succ]`.
-/
private theorem scl_st_pow (T : TrInv B E) {z : E} (hz : T.st z = z) (n : ℕ) : T.st (z ^ n) = z ^ n := by
  induction n with
  | zero => rw [pow_zero, scl_st_one]
  | succ n ih => rw [pow_succ, T.st_mul, hz, ih, ← pow_succ', pow_succ]

/- English proof (translation)
Proceed by induction on `q using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq]`. Consider the case `monomial n b => rw [aeval_monomial, ← Algebra.smul_def, map_smul, scl_st_pow T hz]`.
-/
private theorem scl_st_aeval (T : TrInv B E) {z : E} (hz : T.st z = z) (q : B[X]) :
    T.st (aeval z q) = aeval z q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | monomial n b => rw [aeval_monomial, ← Algebra.smul_def, map_smul, scl_st_pow T hz]

/- English proof (translation)
Establish `hmul : ∀ (N : ℕ) (x y : E), x ∈ I • (⊤ : Submodule B E) → y ∈ I ^ N • (⊤ : Submodule B E) → x * y ∈ I ^ (N + 1) • (⊤ : Submodule B E)`. Introduce `N x y hx hy`. Establish `hmap : (I • (⊤ : Submodule B E)).map (LinearMap.mulRight B y) ≤ I ^ (N + 1) • ⊤`. Rewrite using `[Submodule.map_smul'', pow_succ', Submodule.mul_smul]`. Apply `Submodule.smul_mono le_rfl` to reduce the goal to its premises.

Introduce and unpack `_ ⟨z, -, rfl⟩`. Conclude with `scl_map_mem (I ^ N) (LinearMap.mulLeft B z) hy`. Conclude with `hmap ⟨x, hx, rfl⟩`. Establish `hg1 : g ∈ I • (⊤ : Submodule B E)`. Establish `h` using `scl_map_mem I (LinearMap.mulLeft B g) hM`.

Rewrite `h` using `[LinearMap.mulLeft_apply, ← pow_succ', hg.pow_succ_eq]`. Then use the resulting hypothesis. Establish `hall : ∀ N : ℕ, g ∈ I ^ N • (⊤ : Submodule B E)`. Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => simp`.

Consider the case `succ N ih`. Establish `h` using `hmul N g g hg1 ih`. Rewrite `h` using `[hg.eq]`. Then use the resulting hypothesis. Conclude with `scl_haus I hall`.
-/
private theorem scl_idem_zero (I : Ideal B) [IsAdicComplete I E] {g : E} (hg : IsIdempotentElem g) {M : ℕ}
    (hM : g ^ M ∈ I • (⊤ : Submodule B E)) : g = 0 := by
  have hmul : ∀ (N : ℕ) (x y : E), x ∈ I • (⊤ : Submodule B E) → y ∈ I ^ N • (⊤ : Submodule B E) →
      x * y ∈ I ^ (N + 1) • (⊤ : Submodule B E) := by
    intro N x y hx hy
    have hmap : (I • (⊤ : Submodule B E)).map (LinearMap.mulRight B y) ≤ I ^ (N + 1) • ⊤ := by
      rw [Submodule.map_smul'', pow_succ', Submodule.mul_smul]
      apply Submodule.smul_mono le_rfl
      rintro _ ⟨z, -, rfl⟩
      exact scl_map_mem (I ^ N) (LinearMap.mulLeft B z) hy
    exact hmap ⟨x, hx, rfl⟩
  have hg1 : g ∈ I • (⊤ : Submodule B E) := by
    have h := scl_map_mem I (LinearMap.mulLeft B g) hM
    rwa [LinearMap.mulLeft_apply, ← pow_succ', hg.pow_succ_eq] at h
  have hall : ∀ N : ℕ, g ∈ I ^ N • (⊤ : Submodule B E) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have h := hmul N g g hg1 ih
      rwa [hg.eq] at h
  exact scl_haus I hall

/- English proof (translation)
Establish `hr0 : ∀ x ∈ I • (⊤ : Submodule B E), r x = 0`. Introduce `x hx`. Use `Submodule.smul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `a ha n _`. Rewrite using `[map_smul, ← algebraMap_smul F a (r n), RingHom.mem_ker.1 (hI ha), zero_smul]`.

Introduce `x y hx hy`. Rewrite using `[map_add, hx, hy, add_zero]`. Take `⟨c, hc⟩ : ∃ c : B, c * 2 = 1` from `⟨((h2.unit⁻¹ : Bˣ) : B), h2.val_inv_mul⟩`. Set `u : E` to `c • (y + T.st y)`. Establish `hsu : T.st u = u`.

Simplify using `only [u, map_smul, map_add, T.st_st, add_comm]`. Establish `hru : r u = r y`. Simplify using `only [u, map_smul, map_add, hst, hyt]`. Rewrite using `[← two_smul B (r y), smul_smul, hc, one_smul]`. Set `z : E` to `e * u * e`.

Establish `hsz : T.st z = z`. Simplify using `only [z, T.st_mul, hse, hsu, mul_assoc]`. Establish `hrz : r z = r y`. Simplify using `only [z, map_mul, hru, hey]`. Establish `hez : e * z = z` using `by simp only [z, ← mul_assoc, he.eq]`.

Establish `hze : z * e = z` using `by simp only [z, mul_assoc, he.eq]`. Use `clear_value z`. Choose the witnesses or unpack the hypotheses as in `⟨M, hM⟩ : ∃ M, (z * z - z) ^ M ∈ I • (⊤ : Submodule B E) := by`. Apply `hk` to reduce the goal to its premises. Rewrite using `[map_sub, map_mul, hrz, hy.eq, sub_self]`.

Take `⟨f, hf, happ⟩` from `idem_lift_complete I z M hM`. Establish `hw : ∀ q : B[X], z + (z * z - z) * aeval z q = aeval z (X + (X ^ 2 - X) * q)`. Introduce `q`. Simplify using `[pow_two]`. Establish `hwl : ∀ q : B[X], aeval z (X + (X ^ 2 - X) * q) = z * aeval z (1 + (X - 1) * q)`.

Introduce `q`. Rewrite using `[show (X + (X ^ 2 - X) * q : B[X]) = X * (1 + (X - 1) * q) by ring, map_mul, aeval_X]`. Establish `hwr : ∀ q : B[X], aeval z (X + (X ^ 2 - X) * q) = aeval z (1 + (X - 1) * q) * z`. Introduce `q`. Rewrite using `[show (X + (X ^ 2 - X) * q : B[X]) = (1 + (X - 1) * q) * X by ring, map_mul, aeval_X]`.

Establish `hfix : ∀ g : E →ₗ[B] E, (∀ q : B[X], g (aeval z (X + (X ^ 2 - X) * q)) = aeval z (X + (X ^ 2 - X) * q)) → g f = f`. Introduce `g hg`. Apply `scl_fix I g` to reduce the goal to its premises. Introduce `N`. Take `⟨q, hq⟩` from `happ N`.

Conclude with `⟨_, hg q, by rwa [hw] at hq⟩`. Use `⟨f, hf, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hfix T.st (fun q => scl_st_aeval T hsz _)`. Conclude with `hfix (LinearMap.mulLeft B e) (fun q => by`. Rewrite using `[LinearMap.mulLeft_apply, hwl, ← mul_assoc, hez])`.

Conclude with `hfix (LinearMap.mulRight B e) (fun q => by`. Rewrite using `[LinearMap.mulRight_apply, hwr, mul_assoc, hze])`. Take `⟨q, hq⟩` from `happ 1`. Rewrite `hq` using `[pow_one]`. Establish `h0` using `hr0 _ hq`.

Rewrite `h0` using `[map_sub, sub_eq_zero]`. Establish `h3 : r ((z * z - z) * aeval z q) = 0`. Rewrite using `[map_mul, map_sub, map_mul, hrz, hy.eq, sub_self, zero_mul]`. Rewrite using `[h0, map_add, h3, add_zero, hrz]`.
-/
private theorem scl_step (T : TrInv B E) (I : Ideal B) [IsAdicComplete I E] {F : Type} [CommRing F] [Algebra B F]
    {ι : Type} [Fintype ι] [DecidableEq ι] (r : E →ₐ[B] Matrix ι ι F) (h2 : IsUnit (2 : B))
    (hI : I ≤ RingHom.ker (algebraMap B F))
    (hk : ∀ x, r x = 0 → ∃ M : ℕ, x ^ M ∈ I • (⊤ : Submodule B E)) (hst : ∀ x, r (T.st x) = (r x)ᵀ)
    {e y : E} (he : IsIdempotentElem e) (hse : T.st e = e) (hy : IsIdempotentElem (r y)) (hyt : (r y)ᵀ = r y)
    (hey : r e * r y * r e = r y) :
    ∃ f : E, IsIdempotentElem f ∧ T.st f = f ∧ e * f = f ∧ f * e = f ∧ r f = r y := by
  classical
  have hr0 : ∀ x ∈ I • (⊤ : Submodule B E), r x = 0 := by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha n _
      rw [map_smul, ← algebraMap_smul F a (r n), RingHom.mem_ker.1 (hI ha), zero_smul]
    · intro x y hx hy
      rw [map_add, hx, hy, add_zero]
  obtain ⟨c, hc⟩ : ∃ c : B, c * 2 = 1 := ⟨((h2.unit⁻¹ : Bˣ) : B), h2.val_inv_mul⟩
  let u : E := c • (y + T.st y)
  have hsu : T.st u = u := by
    simp only [u, map_smul, map_add, T.st_st, add_comm]
  have hru : r u = r y := by
    simp only [u, map_smul, map_add, hst, hyt]
    rw [← two_smul B (r y), smul_smul, hc, one_smul]
  let z : E := e * u * e
  have hsz : T.st z = z := by
    simp only [z, T.st_mul, hse, hsu, mul_assoc]
  have hrz : r z = r y := by
    simp only [z, map_mul, hru, hey]
  have hez : e * z = z := by simp only [z, ← mul_assoc, he.eq]
  have hze : z * e = z := by simp only [z, mul_assoc, he.eq]
  clear_value z
  obtain ⟨M, hM⟩ : ∃ M, (z * z - z) ^ M ∈ I • (⊤ : Submodule B E) := by
    apply hk
    rw [map_sub, map_mul, hrz, hy.eq, sub_self]
  obtain ⟨f, hf, happ⟩ := idem_lift_complete I z M hM
  have hw : ∀ q : B[X], z + (z * z - z) * aeval z q = aeval z (X + (X ^ 2 - X) * q) := by
    intro q
    simp [pow_two]
  have hwl : ∀ q : B[X], aeval z (X + (X ^ 2 - X) * q) = z * aeval z (1 + (X - 1) * q) := by
    intro q
    rw [show (X + (X ^ 2 - X) * q : B[X]) = X * (1 + (X - 1) * q) by ring, map_mul, aeval_X]
  have hwr : ∀ q : B[X], aeval z (X + (X ^ 2 - X) * q) = aeval z (1 + (X - 1) * q) * z := by
    intro q
    rw [show (X + (X ^ 2 - X) * q : B[X]) = (1 + (X - 1) * q) * X by ring, map_mul, aeval_X]
  have hfix : ∀ g : E →ₗ[B] E, (∀ q : B[X], g (aeval z (X + (X ^ 2 - X) * q)) = aeval z (X + (X ^ 2 - X) * q)) →
      g f = f := by
    intro g hg
    apply scl_fix I g
    intro N
    obtain ⟨q, hq⟩ := happ N
    exact ⟨_, hg q, by rwa [hw] at hq⟩
  refine ⟨f, hf, ?_, ?_, ?_, ?_⟩
  · exact hfix T.st (fun q => scl_st_aeval T hsz _)
  · exact hfix (LinearMap.mulLeft B e) (fun q => by
      rw [LinearMap.mulLeft_apply, hwl, ← mul_assoc, hez])
  · exact hfix (LinearMap.mulRight B e) (fun q => by
      rw [LinearMap.mulRight_apply, hwr, mul_assoc, hze])
  · obtain ⟨q, hq⟩ := happ 1
    rw [pow_one] at hq
    have h0 := hr0 _ hq
    rw [map_sub, sub_eq_zero] at h0
    have h3 : r ((z * z - z) * aeval z q) = 0 := by
      rw [map_mul, map_sub, map_mul, hrz, hy.eq, sub_self, zero_mul]
    rw [h0, map_add, h3, add_zero, hrz]

end aux

/- English proof (translation)
Introduce `B E _ _ _ T I _ F _ _ ι _ _ r h2 hI hk hst hex`. Use `choose y hy using hex`. Establish `hyi : ∀ i, IsIdempotentElem (r (y i))`. Introduce `i`. Rewrite using `[IsIdempotentElem, hy i, Matrix.single_mul_single_same, mul_one]`.

Establish `hyt : ∀ i, (r (y i))ᵀ = r (y i)`. Introduce `i`. Rewrite using `[hy i, Matrix.transpose_single]`. Establish `hsum : ∀ (ep : ι → E) (s : Finset ι), (∀ i ∈ s, IsIdempotentElem (ep i)) → (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ep i * ep j = 0) → IsIdempotentElem (∑ i ∈ s, ep i) ∧ ∀ j ∈ s, (∑ i ∈ s, ep i) * ep j = ep j ∧ ep j * (∑ i ∈ s, ep i) = ep j`. Introduce `ep s hid hor`.

Establish `hl : ∀ j ∈ s, (∑ i ∈ s, ep i) * ep j = ep j`. Introduce `j hj`. Rewrite using `[Finset.sum_mul, Finset.sum_eq_single j]`. Conclude with `(hid j hj).eq`. Introduce `i hi hij`.

Conclude with `hor i hi j hj hij`. Introduce `h`. Conclude with `absurd hj h`. Establish `hr : ∀ j ∈ s, ep j * (∑ i ∈ s, ep i) = ep j`. Introduce `j hj`.

Rewrite using `[Finset.mul_sum, Finset.sum_eq_single j]`. Conclude with `(hid j hj).eq`. Introduce `i hi hij`. Conclude with `hor j hj i hi (Ne.symm hij)`. Introduce `h`.

Conclude with `absurd hj h`. Use `⟨?_, fun j hj => ⟨hl j hj, hr j hj⟩⟩` and prove the remaining obligations. Use `show (∑ i ∈ s, ep i) * (∑ i ∈ s, ep i) = ∑ i ∈ s, ep i`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl hl`.

Establish `key : ∀ s : Finset ι, ∃ ep : ι → E, (∀ i ∈ s, IsIdempotentElem (ep i) ∧ T.st (ep i) = ep i ∧ r (ep i) = Matrix.single i i 1) ∧ (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ep i * ep j = 0)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨fun _ => 0, by simp, by simp⟩`. Consider the case `insert a s ha ih`.

Take `⟨ep, hp, ho⟩` from `ih`. Establish `hne : ∀ j ∈ s, j ≠ a` using `fun j hj h => ha (h ▸ hj)`. Take `⟨hSid, hSj⟩` from `hsum ep s (fun i hi => (hp i hi).1) ho`. Establish `he : IsIdempotentElem (1 - ∑ i ∈ s, ep i)` using `hSid.one_sub`. Establish `hse : T.st (1 - ∑ i ∈ s, ep i) = 1 - ∑ i ∈ s, ep i`.

Rewrite using `[map_sub, scl_st_one, map_sum]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl (fun i hi => (hp i hi).2.1)`. Establish `hre : r (1 - ∑ i ∈ s, ep i) = 1 - ∑ i ∈ s, Matrix.single i i (1 : F)`. Rewrite using `[map_sub, map_one, map_sum]`.

Use `congr 1`. Conclude with `Finset.sum_congr rfl (fun i hi => (hp i hi).2.2)`. Establish `hl : (1 - ∑ i ∈ s, Matrix.single i i (1 : F)) * Matrix.single a a 1 = Matrix.single a a 1`. Rewrite using `[sub_mul, one_mul, Finset.sum_mul, Finset.sum_eq_zero, sub_zero]`. Introduce `i hi`.

Conclude with `Matrix.single_mul_single_of_ne _ _ _ _ (hne i hi) _`. Establish `hr : Matrix.single a a (1 : F) * (1 - ∑ i ∈ s, Matrix.single i i (1 : F)) = Matrix.single a a 1`. Rewrite using `[mul_sub, mul_one, Finset.mul_sum, Finset.sum_eq_zero, sub_zero]`. Introduce `i hi`. Conclude with `Matrix.single_mul_single_of_ne _ _ _ _ (hne i hi).symm _`.

Establish `hey : r (1 - ∑ i ∈ s, ep i) * r (y a) * r (1 - ∑ i ∈ s, ep i) = r (y a)`. Rewrite using `[hre, hy a, hl, hr]`. Take `⟨f, hf, hsf, hef, hfe, hrf⟩` from `scl_step T I r h2 hI hk hst he hse (hyi a) (hyt a) hey`. Establish `hej : ∀ j ∈ s, (1 - ∑ i ∈ s, ep i) * ep j = 0`. Introduce `j hj`.

Rewrite using `[sub_mul, one_mul, (hSj j hj).1, sub_self]`. Establish `hje : ∀ j ∈ s, ep j * (1 - ∑ i ∈ s, ep i) = 0`. Introduce `j hj`. Rewrite using `[mul_sub, mul_one, (hSj j hj).2, sub_self]`. Establish `hfj : ∀ j ∈ s, f * ep j = 0`.

Introduce `j hj`. Rewrite using `[← hfe, mul_assoc, hej j hj, mul_zero]`. Establish `hjf : ∀ j ∈ s, ep j * f = 0`. Introduce `j hj`. Rewrite using `[← hef, ← mul_assoc, hje j hj, zero_mul]`.

Use `⟨Function.update ep a f, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Break down `Finset.mem_insert.1 hi with hia | his` into its components or cases. Rewrite using `[hia, Function.update_self, ← hy a]`. Conclude with `⟨hf, hsf, hrf⟩`.

Rewrite using `[Function.update_of_ne (hne i his)]`. Conclude with `hp i his`. Introduce `i hi j hj hij`. Apply the tactic sequence `rcases Finset.mem_insert.1 hi with hia | his <;> rcases Finset.mem_insert.1 hj with hja | hjs`. Conclude with `absurd (hia.trans hja.symm) hij`.

Rewrite using `[hia, Function.update_self, Function.update_of_ne (hne j hjs)]`. Conclude with `hfj j hjs`. Rewrite using `[hja, Function.update_self, Function.update_of_ne (hne i his)]`. Conclude with `hjf i his`. Rewrite using `[Function.update_of_ne (hne i his), Function.update_of_ne (hne j hjs)]`.

Conclude with `ho i his j hjs hij`. Take `⟨ep, hp, ho⟩` from `key Finset.univ`. Take `⟨hSid, -⟩` from `hsum ep Finset.univ (fun i _ => (hp i (Finset.mem_univ i)).1) ho`. Establish `hone : ∑ i : ι, Matrix.single i i (1 : F) = 1`. Use extensionality with `a b`.

Rewrite using `[Matrix.one_apply, Matrix.sum_apply]`. Simplify using `only [Matrix.single_apply]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `only [h, if_false]`. Use `Finset.sum_eq_zero (fun x _ => ?_)` and prove the remaining obligations. Rewrite using `[if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `h rfl`.

Establish `hr0 : r (1 - ∑ i, ep i) = 0`. Rewrite using `[map_sub, map_one, map_sum, sub_eq_zero]`. Rewrite using `[Finset.sum_congr rfl (fun i _ => (hp i (Finset.mem_univ i)).2.2), hone]`. Take `⟨M, hM⟩` from `hk _ hr0`. Establish `h0` using `scl_idem_zero I hSid.one_sub hM`.

Use `⟨ep, ?_, fun i => (hp i (Finset.mem_univ i)).2.1, fun i => (hp i (Finset.mem_univ i)).2.2⟩` and prove the remaining obligations. Conclude with `{ idem := fun i => (hp i (Finset.mem_univ i)).1 ortho := fun i j hij => ho i (Finset.mem_univ i) j (Finset.mem_univ j) hij complete := (sub_eq_zero.1 h0).symm }`.
-/
theorem UpperTheory.V.AlgebraTools.st_coi_lift :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) (I : Ideal B) [IsAdicComplete I E] {F : Type} [CommRing F] [Algebra B F] {ι : Type} [Fintype ι] [DecidableEq ι] (r : E →ₐ[B] Matrix ι ι F), IsUnit (2 : B) → I ≤ RingHom.ker (algebraMap B F) → (∀ x, r x = 0 → ∃ M : ℕ, x ^ M ∈ I • (⊤ : Submodule B E)) → (∀ x, r (T.st x) = (r x)ᵀ) → (∀ i, ∃ y, r y = single i i 1) → ∃ ep : ι → E, CompleteOrthogonalIdempotents ep ∧ (∀ i, T.st (ep i) = ep i) ∧ ∀ i, r (ep i) = single i i 1 := by
  intro B E _ _ _ T I _ F _ _ ι _ _ r h2 hI hk hst hex
  classical
  choose y hy using hex
  have hyi : ∀ i, IsIdempotentElem (r (y i)) := by
    intro i
    rw [IsIdempotentElem, hy i, Matrix.single_mul_single_same, mul_one]
  have hyt : ∀ i, (r (y i))ᵀ = r (y i) := by
    intro i
    rw [hy i, Matrix.transpose_single]
  have hsum : ∀ (ep : ι → E) (s : Finset ι), (∀ i ∈ s, IsIdempotentElem (ep i)) →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ep i * ep j = 0) →
      IsIdempotentElem (∑ i ∈ s, ep i) ∧
        ∀ j ∈ s, (∑ i ∈ s, ep i) * ep j = ep j ∧ ep j * (∑ i ∈ s, ep i) = ep j := by
    intro ep s hid hor
    have hl : ∀ j ∈ s, (∑ i ∈ s, ep i) * ep j = ep j := by
      intro j hj
      rw [Finset.sum_mul, Finset.sum_eq_single j]
      · exact (hid j hj).eq
      · intro i hi hij
        exact hor i hi j hj hij
      · intro h
        exact absurd hj h
    have hr : ∀ j ∈ s, ep j * (∑ i ∈ s, ep i) = ep j := by
      intro j hj
      rw [Finset.mul_sum, Finset.sum_eq_single j]
      · exact (hid j hj).eq
      · intro i hi hij
        exact hor j hj i hi (Ne.symm hij)
      · intro h
        exact absurd hj h
    refine ⟨?_, fun j hj => ⟨hl j hj, hr j hj⟩⟩
    show (∑ i ∈ s, ep i) * (∑ i ∈ s, ep i) = ∑ i ∈ s, ep i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hl
  have key : ∀ s : Finset ι, ∃ ep : ι → E,
      (∀ i ∈ s, IsIdempotentElem (ep i) ∧ T.st (ep i) = ep i ∧ r (ep i) = Matrix.single i i 1) ∧
        (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ep i * ep j = 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ => 0, by simp, by simp⟩
    | insert a s ha ih =>
      obtain ⟨ep, hp, ho⟩ := ih
      have hne : ∀ j ∈ s, j ≠ a := fun j hj h => ha (h ▸ hj)
      obtain ⟨hSid, hSj⟩ := hsum ep s (fun i hi => (hp i hi).1) ho
      have he : IsIdempotentElem (1 - ∑ i ∈ s, ep i) := hSid.one_sub
      have hse : T.st (1 - ∑ i ∈ s, ep i) = 1 - ∑ i ∈ s, ep i := by
        rw [map_sub, scl_st_one, map_sum]
        congr 1
        exact Finset.sum_congr rfl (fun i hi => (hp i hi).2.1)
      have hre : r (1 - ∑ i ∈ s, ep i) = 1 - ∑ i ∈ s, Matrix.single i i (1 : F) := by
        rw [map_sub, map_one, map_sum]
        congr 1
        exact Finset.sum_congr rfl (fun i hi => (hp i hi).2.2)
      have hl : (1 - ∑ i ∈ s, Matrix.single i i (1 : F)) * Matrix.single a a 1 = Matrix.single a a 1 := by
        rw [sub_mul, one_mul, Finset.sum_mul, Finset.sum_eq_zero, sub_zero]
        intro i hi
        exact Matrix.single_mul_single_of_ne _ _ _ _ (hne i hi) _
      have hr : Matrix.single a a (1 : F) * (1 - ∑ i ∈ s, Matrix.single i i (1 : F)) = Matrix.single a a 1 := by
        rw [mul_sub, mul_one, Finset.mul_sum, Finset.sum_eq_zero, sub_zero]
        intro i hi
        exact Matrix.single_mul_single_of_ne _ _ _ _ (hne i hi).symm _
      have hey : r (1 - ∑ i ∈ s, ep i) * r (y a) * r (1 - ∑ i ∈ s, ep i) = r (y a) := by
        rw [hre, hy a, hl, hr]
      obtain ⟨f, hf, hsf, hef, hfe, hrf⟩ :=
        scl_step T I r h2 hI hk hst he hse (hyi a) (hyt a) hey
      have hej : ∀ j ∈ s, (1 - ∑ i ∈ s, ep i) * ep j = 0 := by
        intro j hj
        rw [sub_mul, one_mul, (hSj j hj).1, sub_self]
      have hje : ∀ j ∈ s, ep j * (1 - ∑ i ∈ s, ep i) = 0 := by
        intro j hj
        rw [mul_sub, mul_one, (hSj j hj).2, sub_self]
      have hfj : ∀ j ∈ s, f * ep j = 0 := by
        intro j hj
        rw [← hfe, mul_assoc, hej j hj, mul_zero]
      have hjf : ∀ j ∈ s, ep j * f = 0 := by
        intro j hj
        rw [← hef, ← mul_assoc, hje j hj, zero_mul]
      refine ⟨Function.update ep a f, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.1 hi with hia | his
        · rw [hia, Function.update_self, ← hy a]
          exact ⟨hf, hsf, hrf⟩
        · rw [Function.update_of_ne (hne i his)]
          exact hp i his
      · intro i hi j hj hij
        rcases Finset.mem_insert.1 hi with hia | his <;> rcases Finset.mem_insert.1 hj with hja | hjs
        · exact absurd (hia.trans hja.symm) hij
        · rw [hia, Function.update_self, Function.update_of_ne (hne j hjs)]
          exact hfj j hjs
        · rw [hja, Function.update_self, Function.update_of_ne (hne i his)]
          exact hjf i his
        · rw [Function.update_of_ne (hne i his), Function.update_of_ne (hne j hjs)]
          exact ho i his j hjs hij
  obtain ⟨ep, hp, ho⟩ := key Finset.univ
  obtain ⟨hSid, -⟩ := hsum ep Finset.univ (fun i _ => (hp i (Finset.mem_univ i)).1) ho
  have hone : ∑ i : ι, Matrix.single i i (1 : F) = 1 := by
    ext a b
    rw [Matrix.one_apply, Matrix.sum_apply]
    simp only [Matrix.single_apply]
    by_cases h : a = b
    · subst h
      simp
    · simp only [h, if_false]
      refine Finset.sum_eq_zero (fun x _ => ?_)
      rw [if_neg]
      rintro ⟨rfl, rfl⟩
      exact h rfl
  have hr0 : r (1 - ∑ i, ep i) = 0 := by
    rw [map_sub, map_one, map_sum, sub_eq_zero]
    rw [Finset.sum_congr rfl (fun i _ => (hp i (Finset.mem_univ i)).2.2), hone]
  obtain ⟨M, hM⟩ := hk _ hr0
  have h0 := scl_idem_zero I hSid.one_sub hM
  refine ⟨ep, ?_, fun i => (hp i (Finset.mem_univ i)).2.1, fun i => (hp i (Finset.mem_univ i)).2.2⟩
  exact
    { idem := fun i => (hp i (Finset.mem_univ i)).1
      ortho := fun i j hij => ho i (Finset.mem_univ i) j (Finset.mem_univ j) hij
      complete := (sub_eq_zero.1 h0).symm }
