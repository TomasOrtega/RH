import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section LocDAux
variable {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]

/- English proof (translation)
Establish `key : (1 : S) = b ^ N * a ^ N + (∑ i ∈ Finset.range N, (a * b) ^ i) * (1 - a * b)`. Rewrite using `[geom_sum_mul_neg, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `hx : x = φ (b ^ N) (φ (a ^ N) x) + φ (∑ i ∈ Finset.range N, (a * b) ^ i) (φ (1 - a * b) x)`. Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← LinearMap.add_apply, ← map_add, ← key]`.

Simplify using the standard rewrite rules. Rewrite using `[hx]`. Conclude with `P.add_mem (hP _ (R.pow_mem hb N) _ hN) (hP _ (R.sum_mem fun i _ => R.pow_mem (R.mul_mem ha hb) i) _ h1)`.
-/
private lemma geo_mem {W : Type} [AddCommGroup W] [Module ℂ W] (φ : S →+* Module.End ℂ W)
    (R : Subalgebra ℂ S) (P : Submodule ℂ W) (hP : ∀ s ∈ R, ∀ x ∈ P, φ s x ∈ P) {a b : S}
    (ha : a ∈ R) (hb : b ∈ R) (x : W) (h1 : φ (1 - a * b) x ∈ P) (N : ℕ)
    (hN : φ (a ^ N) x ∈ P) : x ∈ P := by
  have key : (1 : S) = b ^ N * a ^ N + (∑ i ∈ Finset.range N, (a * b) ^ i) * (1 - a * b) := by
    rw [geom_sum_mul_neg, mul_pow]; ring
  have hx : x = φ (b ^ N) (φ (a ^ N) x) +
      φ (∑ i ∈ Finset.range N, (a * b) ^ i) (φ (1 - a * b) x) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      ← LinearMap.add_apply, ← map_add, ← key]
    simp
  rw [hx]
  exact P.add_mem (hP _ (R.pow_mem hb N) _ hN)
    (hP _ (R.sum_mem fun i _ => R.pow_mem (R.mul_mem ha hb) i) _ h1)

private def pwR (act : S →ₐ[ℂ] Module.End ℂ E) (ι : Type) : S →+* Module.End ℂ (ι → E) where
  toFun s := LinearMap.pi fun t => act s ∘ₗ LinearMap.proj t
  map_one' := LinearMap.ext fun c => funext fun t => by simp
  map_mul' s s' := LinearMap.ext fun c => funext fun t => by simp
  map_zero' := LinearMap.ext fun c => funext fun t => by simp
  map_add' s s' := LinearMap.ext fun c => funext fun t => by simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma pwR_apply (act : S →ₐ[ℂ] Module.End ℂ E) (ι : Type) (s : S) (c : ι → E) (t : ι) :
    pwR act ι s c t = act s (c t) := rfl

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]`.
-/
private lemma act_comm (act : S →ₐ[ℂ] Module.End ℂ E) (s s' : S) (x : E) :
    act s (act s' x) = act s' (act s x) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

variable {κ : Type} [LinearOrder κ]

/- English proof (translation)
Simplify using `[kos, acx, Submodule.mem_pi]`.
-/
private lemma kos_mem_C (act : S →ₐ[ℂ] Module.End ℂ E) (M : Submodule ℂ E) (r : κ → S) (n : ℤ)
    (c : Finset κ → E) :
    c ∈ (kos act M r).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then M else ⊥ : Submodule ℂ E) := by
  simp [kos, acx, Submodule.mem_pi]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Simplify using `only [pwR_apply, wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum, map_zsmul, act_comm act s]`.
-/
private lemma wd_pw (act : S →ₐ[ℂ] Module.End ℂ E) (r : κ → S) (s : S) (y : Finset κ → E) :
    wd (fun l => act (r l)) (pwR act _ s y) = pwR act _ s (wd (fun l => act (r l)) y) := by
  funext t
  simp only [pwR_apply, wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, map_sum, map_zsmul, act_comm act s]

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `hx`. Use `⟨pwR act _ s y, ?_, wd_pw act r s y⟩` and prove the remaining obligations. Rewrite `hy`, the goal using `[SetLike.mem_coe, kos_mem_C]`. Introduce `t`. Use `hy t` as an intermediate fact.

Rewrite using `[pwR_apply]`. Use `split_ifs at this ⊢ with h`. Conclude with `hSt s hs _ this`. Simplify using `only [Submodule.mem_bot] at this ⊢`. Rewrite using `[this, map_zero]`.
-/
private lemma kos_B_stab (act : S →ₐ[ℂ] Module.End ℂ E) (R : Subalgebra ℂ S) (M : Submodule ℂ E)
    (r : κ → S) (hSt : Stab act R M) (n : ℤ) (s : S) (hs : s ∈ R) (x : Finset κ → E)
    (hx : x ∈ (kos act M r).B n) : pwR act _ s x ∈ (kos act M r).B n := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨pwR act _ s y, ?_, wd_pw act r s y⟩
  rw [SetLike.mem_coe, kos_mem_C] at hy ⊢
  intro t
  have := hy t
  rw [pwR_apply]
  split_ifs at this ⊢ with h
  · exact hSt s hs _ this
  · simp only [Submodule.mem_bot] at this ⊢
    rw [this, map_zero]

/- English proof (translation)
Establish `hle : sm act M T ≤ (sm act M T).comap (act s)`. Use `iSup₂_le fun t ht => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨m, hm, rfl⟩`. Rewrite using `[Submodule.mem_comap, act_comm]`. Conclude with `(le_iSup₂_of_le (f := fun t _ => M.map (act t)) t ht le_rfl : _ ≤ sm act M T) ⟨_, hSt s hs m hm, rfl⟩`.

Conclude with `hle hx`.
-/
private lemma sm_stab (act : S →ₐ[ℂ] Module.End ℂ E) (R : Subalgebra ℂ S) (M : Submodule ℂ E)
    (T : Set S) (hSt : Stab act R M) (s : S) (hs : s ∈ R) (x : E) (hx : x ∈ sm act M T) :
    act s x ∈ sm act M T := by
  have hle : sm act M T ≤ (sm act M T).comap (act s) := by
    refine iSup₂_le fun t ht => ?_
    rintro _ ⟨m, hm, rfl⟩
    rw [Submodule.mem_comap, act_comm]
    exact (le_iSup₂_of_le (f := fun t _ => M.map (act t)) t ht le_rfl : _ ≤ sm act M T)
      ⟨_, hSt s hs m hm, rfl⟩
  exact hle hx

/- English proof (translation)
Use `choose n hn using fun i => hloc (f i) (hf i)`. Use `⟨∑ i, n i, fun i => ?_⟩` and prove the remaining obligations. Establish `h : ∑ i, n i = (∑ i, n i - n i) + n i` using `(Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))).symm`. Rewrite using `[h, pow_add, map_mul, Module.End.mul_apply]`. Conclude with `hSt _ (R.pow_mem ha _) _ (hn i)`.
-/
private lemma unif_pow (act : S →ₐ[ℂ] Module.End ℂ E) (R : Subalgebra ℂ S) (M M' : Submodule ℂ E)
    (hSt : Stab act R M) {a : S} (ha : a ∈ R) (hloc : ∀ m ∈ M', ∃ N : ℕ, act (a ^ N) m ∈ M)
    {ι : Type} [Fintype ι] (f : ι → E) (hf : ∀ i, f i ∈ M') :
    ∃ N : ℕ, ∀ i, act (a ^ N) (f i) ∈ M := by
  choose n hn using fun i => hloc (f i) (hf i)
  refine ⟨∑ i, n i, fun i => ?_⟩
  have h : ∑ i, n i = (∑ i, n i - n i) + n i := (Nat.sub_add_cancel
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))).symm
  rw [h, pow_add, map_mul, Module.End.mul_apply]
  exact hSt _ (R.pow_mem ha _) _ (hn i)

/- English proof (translation)
Establish `hP : ∀ k : ℕ, ∀ m ∈ M', act ((v ^ k : Sˣ) : S) m ∈ M' ∧ act (((v ^ k)⁻¹ : Sˣ) : S) m ∈ M'`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro m hm`. Simplify using `using hm`.

Consider the case `succ k ih`. Introduce `m hm`. Prove the components needed by the constructor for the conclusion. Rewrite using `[pow_succ, Units.val_mul, map_mul, Module.End.mul_apply]`. Conclude with `(ih _ (hv m hm).1).1`.

Rewrite using `[pow_succ, mul_inv_rev, Units.val_mul, map_mul, Module.End.mul_apply]`. Conclude with `(hv _ (ih m hm).2).2`. Use `le_antisymm ?_ fun m hm => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨m, hm, rfl⟩`. Conclude with `(hP k m hm).1`.

Use `⟨_, (hP k m hm).2, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `act ((v ^ k : Sˣ) : S) (act (((v ^ k)⁻¹ : Sˣ) : S) m) = m`. Rewrite using `[← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one]`. Both sides reduce to the same expression.
-/
private lemma map_unit_eq (act : S →ₐ[ℂ] Module.End ℂ E) (M' : Submodule ℂ E) (v : Sˣ)
    (hv : ∀ m ∈ M', act v m ∈ M' ∧ act (v⁻¹ : Sˣ) m ∈ M') (k : ℕ) :
    M'.map (act ((v ^ k : Sˣ) : S)) = M' := by
  have hP : ∀ k : ℕ, ∀ m ∈ M', act ((v ^ k : Sˣ) : S) m ∈ M' ∧ act (((v ^ k)⁻¹ : Sˣ) : S) m ∈ M' := by
    intro k
    induction k with
    | zero => intro m hm; simpa using hm
    | succ k ih =>
      intro m hm
      constructor
      · rw [pow_succ, Units.val_mul, map_mul, Module.End.mul_apply]
        exact (ih _ (hv m hm).1).1
      · rw [pow_succ, mul_inv_rev, Units.val_mul, map_mul, Module.End.mul_apply]
        exact (hv _ (ih m hm).2).2
  refine le_antisymm ?_ fun m hm => ?_
  · rintro _ ⟨m, hm, rfl⟩
    exact (hP k m hm).1
  · refine ⟨_, (hP k m hm).2, ?_⟩
    change act ((v ^ k : Sˣ) : S) (act (((v ^ k)⁻¹ : Sˣ) : S) m) = m
    rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one]
    rfl

end LocDAux

/- English proof (translation)
Introduce `hRS hH S E _ _ _ _ act κ _ _ R M M' r v a b l0 d hSt hr ha hb hl0 hMM hloc hv`. Use `⟨fun hKE m hm c hc => ?_, fun m hm hsm => ?_⟩` and prove the remaining obligations. Establish `hcC` using `hc.1`. Establish `hcD : wd (fun l => act (r l)) c = 0` using `hc.2`. Set `u : κ → Sˣ` to `fun _ => v`.

Set `z : κ → S` to `fun l => r l * v`. Establish `hrz : ∀ l, r l = z l * ((u l)⁻¹ : Sˣ)`. Introduce `l`. Simplify using `[z, u, mul_assoc]`. Establish `hmap : ∀ L : Finset κ, M'.map (act ((∏ l ∈ L, u l : Sˣ) : S)) = M'`.

Introduce `L`. Simplify using `only [u, Finset.prod_const]`. Conclude with `map_unit_eq act M' v hv _`. Establish `hT : kosT act M' u z = kos act M' z`. Unfold `kosT kos`.

Simplify using `only [hmap]`. Establish `hR` using `fun n c => hRS S E act κ M' u r z hrz n c`. Establish `hcC'` using `(kos_mem_C act M r m c).1 hcC`. Establish `hcZ' : c ∈ (kos act M' r).Z m`. Use `⟨(kos_mem_C act M' r m c).2 fun t => ?_, hc.2⟩` and prove the remaining obligations.

Use `hcC' t` as an intermediate fact. Use `split_ifs at this ⊢ with h`. Conclude with `hMM this`. Conclude with `this`. Establish `hinv : unsc act u (unsc act u⁻¹ c) = c` using `(hR m c).2.2.2.2`.

Establish `hZ : unsc act u⁻¹ c ∈ (kosT act M' u z).Z m` using `(hR m (unsc act u⁻¹ c)).2.1.2 (by rw [hinv]; exact hcZ')`. Establish `hB : unsc act u⁻¹ c ∈ (kosT act M' u z).B m`. Rewrite `hZ`, the goal using `[hT]`. Conclude with `hKE m hm hZ`. Establish `hcB : c ∈ (kos act M' r).B m`.

Use `(hR m (unsc act u⁻¹ c)).2.2.1.1 hB` as an intermediate fact. Rewrite `this` using `[hinv]`. Then use the resulting hypothesis. Take `⟨y, hy, hyc⟩` from `hcB`. Establish `hy'` using `(kos_mem_C act M' r (m - 1) y).1 hy`. Establish `hyM : ∀ L, y L ∈ M'`.

Introduce `L`. Use `hy' L` as an intermediate fact. Use `split_ifs at this with h`. Conclude with `this`. Rewrite `this` using `[Submodule.mem_bot]`.

Rewrite using `[this]`. Conclude with `M'.zero_mem`. Take `⟨N, hN⟩` from `unif_pow act R M M' hSt ha hloc y hyM`. Use `geo_mem (pwR act _) R ((kos act M r).B m) (fun s hs x hx => kos_B_stab act R M r hSt m s hs x hx) ha hb c ?_ N ?_` and prove the remaining obligations. Rewrite using `[← hl0]`.

Use `hH S E act κ R M r hSt m c hc (r l0) ⟨Pi.single l0 1, fun l => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : l = l0`. Substitute `h` using the available equality. Simplify using `using R.one_mem`. Simplify `R.zero_mem` using `[Pi.single_apply, h]`.

Simplify using `[Pi.single_apply]`. Use `⟨pwR act _ (a ^ N) y, (kos_mem_C act M r (m - 1) _).2 fun t => ?_, ?_⟩` and prove the remaining obligations. Use `hy' t` as an intermediate fact. Rewrite using `[pwR_apply]`. Use `split_ifs at this ⊢ with h`.

Conclude with `hN t`. Rewrite `this`, the goal using `[Submodule.mem_bot]`. Rewrite using `[this, map_zero]`. Establish `e` using `wd_pw act r (a ^ N) y`. Express the relevant statement in the definitionally equal form `wd (fun l => act (r l)) (pwR act _ (a ^ N) y) = pwR act _ (a ^ N) c`.

Rewrite using `[e]`. Rewrite using `[← hyc]`. Both sides reduce to the same expression. Set `T : Set S` to `Set.range r`. Set `Pn : Submodule ℂ E` to `{ carrier := {x | ∃ N : ℕ, act (a ^ N) x ∈ sm act M T} add_mem' := by`.

Introduce and unpack `x y ⟨N₁, h₁⟩ ⟨N₂, h₂⟩`. Use `⟨N₁ + N₂, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Rewrite using `[add_comm, pow_add, map_mul, Module.End.mul_apply]`.

Conclude with `sm_stab act R M T hSt _ (R.pow_mem ha _) _ h₁`. Rewrite using `[pow_add, map_mul, Module.End.mul_apply]`. Conclude with `sm_stab act R M T hSt _ (R.pow_mem ha _) _ h₂`. Use the proof step `zero_mem' := ⟨0, by simp⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `k x ⟨N, h⟩`. Use `⟨N, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ k h }`. Establish `hle : sm act M' (Set.range fun l => r l * v) ≤ Pn`.

Use `iSup₂_le fun t ht => ?_` and prove the remaining obligations. Take `⟨l, rfl⟩` from `ht`. Introduce and unpack `_ ⟨m', hm', rfl⟩`. Take `⟨N, hN⟩` from `hloc _ (hv m' hm').1`. Use `⟨N, ?_⟩` and prove the remaining obligations.

Establish `e : act (a ^ N) (act (r l * v) m') = act (r l) (act (a ^ N) (act v m'))`. Rewrite using `[map_mul, Module.End.mul_apply, act_comm act (a ^ N) (r l)]`. Rewrite using `[e]`. Conclude with `(le_iSup₂_of_le (f := fun t _ => M.map (act t)) (r l) ⟨l, rfl⟩ le_rfl : _ ≤ sm act M T) ⟨_, hN, rfl⟩`. Take `⟨N, hN⟩` from `hle hsm`.

Use `geo_mem act.toRingHom R (sm act M T) (fun s hs x hx => sm_stab act R M T hSt s hs x hx) ha hb m ?_ N hN` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `act (1 - a * b) m ∈ sm act M T`. Rewrite using `[← hl0]`. Conclude with `(le_iSup₂_of_le (f := fun t _ => M.map (act t)) (r l0) ⟨l0, rfl⟩ le_rfl : _ ≤ sm act M T) ⟨_, hm, rfl⟩`.
-/
theorem UpperTheory.Gal.productCup_of_system.locD_of :
    RS → Htpy → LocD := by
  intro hRS hH S E _ _ _ _ act κ _ _ R M M' r v a b l0 d hSt hr ha hb hl0 hMM hloc hv
  refine ⟨fun hKE m hm c hc => ?_, fun m hm hsm => ?_⟩
  · have hcC := hc.1
    have hcD : wd (fun l => act (r l)) c = 0 := hc.2

    let u : κ → Sˣ := fun _ => v
    let z : κ → S := fun l => r l * v
    have hrz : ∀ l, r l = z l * ((u l)⁻¹ : Sˣ) := by
      intro l
      simp [z, u, mul_assoc]
    have hmap : ∀ L : Finset κ, M'.map (act ((∏ l ∈ L, u l : Sˣ) : S)) = M' := by
      intro L
      simp only [u, Finset.prod_const]
      exact map_unit_eq act M' v hv _
    have hT : kosT act M' u z = kos act M' z := by
      unfold kosT kos
      simp only [hmap]
    have hR := fun n c => hRS S E act κ M' u r z hrz n c
    have hcC' := (kos_mem_C act M r m c).1 hcC
    have hcZ' : c ∈ (kos act M' r).Z m := by
      refine ⟨(kos_mem_C act M' r m c).2 fun t => ?_, hc.2⟩
      have := hcC' t
      split_ifs at this ⊢ with h
      · exact hMM this
      · exact this
    have hinv : unsc act u (unsc act u⁻¹ c) = c := (hR m c).2.2.2.2
    have hZ : unsc act u⁻¹ c ∈ (kosT act M' u z).Z m :=
      (hR m (unsc act u⁻¹ c)).2.1.2 (by rw [hinv]; exact hcZ')
    have hB : unsc act u⁻¹ c ∈ (kosT act M' u z).B m := by
      rw [hT] at hZ ⊢
      exact hKE m hm hZ
    have hcB : c ∈ (kos act M' r).B m := by
      have := (hR m (unsc act u⁻¹ c)).2.2.1.1 hB
      rwa [hinv] at this
    obtain ⟨y, hy, hyc⟩ := hcB
    have hy' := (kos_mem_C act M' r (m - 1) y).1 hy
    have hyM : ∀ L, y L ∈ M' := by
      intro L
      have := hy' L
      split_ifs at this with h
      · exact this
      · rw [Submodule.mem_bot] at this
        rw [this]
        exact M'.zero_mem
    obtain ⟨N, hN⟩ := unif_pow act R M M' hSt ha hloc y hyM
    refine geo_mem (pwR act _) R ((kos act M r).B m)
      (fun s hs x hx => kos_B_stab act R M r hSt m s hs x hx) ha hb c ?_ N ?_
    · rw [← hl0]
      refine hH S E act κ R M r hSt m c hc (r l0) ⟨Pi.single l0 1, fun l => ?_, ?_⟩
      · by_cases h : l = l0
        · subst h
          simpa using R.one_mem
        · simpa [Pi.single_apply, h] using R.zero_mem
      · simp [Pi.single_apply]
    · refine ⟨pwR act _ (a ^ N) y, (kos_mem_C act M r (m - 1) _).2 fun t => ?_, ?_⟩
      · have := hy' t
        rw [pwR_apply]
        split_ifs at this ⊢ with h
        · exact hN t
        · rw [Submodule.mem_bot] at this ⊢
          rw [this, map_zero]
      · have e := wd_pw act r (a ^ N) y
        change wd (fun l => act (r l)) (pwR act _ (a ^ N) y) = pwR act _ (a ^ N) c
        rw [e]
        rw [← hyc]
        rfl
  · let T : Set S := Set.range r
    let Pn : Submodule ℂ E :=
      { carrier := {x | ∃ N : ℕ, act (a ^ N) x ∈ sm act M T}
        add_mem' := by
          rintro x y ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
          refine ⟨N₁ + N₂, ?_⟩
          rw [map_add]
          refine Submodule.add_mem _ ?_ ?_
          · rw [add_comm, pow_add, map_mul, Module.End.mul_apply]
            exact sm_stab act R M T hSt _ (R.pow_mem ha _) _ h₁
          · rw [pow_add, map_mul, Module.End.mul_apply]
            exact sm_stab act R M T hSt _ (R.pow_mem ha _) _ h₂
        zero_mem' := ⟨0, by simp⟩
        smul_mem' := by
          rintro k x ⟨N, h⟩
          refine ⟨N, ?_⟩
          rw [map_smul]
          exact Submodule.smul_mem _ k h }
    have hle : sm act M' (Set.range fun l => r l * v) ≤ Pn := by
      refine iSup₂_le fun t ht => ?_
      obtain ⟨l, rfl⟩ := ht
      rintro _ ⟨m', hm', rfl⟩
      obtain ⟨N, hN⟩ := hloc _ (hv m' hm').1
      refine ⟨N, ?_⟩
      have e : act (a ^ N) (act (r l * v) m') = act (r l) (act (a ^ N) (act v m')) := by
        rw [map_mul, Module.End.mul_apply, act_comm act (a ^ N) (r l)]
      rw [e]
      exact (le_iSup₂_of_le (f := fun t _ => M.map (act t)) (r l) ⟨l, rfl⟩ le_rfl :
        _ ≤ sm act M T) ⟨_, hN, rfl⟩
    obtain ⟨N, hN⟩ := hle hsm
    refine geo_mem act.toRingHom R (sm act M T)
      (fun s hs x hx => sm_stab act R M T hSt s hs x hx) ha hb m ?_ N hN
    change act (1 - a * b) m ∈ sm act M T
    rw [← hl0]
    exact (le_iSup₂_of_le (f := fun t _ => M.map (act t)) (r l0) ⟨l0, rfl⟩ le_rfl :
      _ ≤ sm act M T) ⟨_, hm, rfl⟩
