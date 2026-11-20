import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RestPair

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Simplify using `only [pp, List.map_append, List.prod_append, Module.End.mul_apply]`.
-/
theorem pp_append (E : GLOps n K V) (mu : Fin n → ℤ) (l1 l2 : List (Fin n × Fin n)) (T : ℕ) (x : V) :
    pp E mu (l1 ++ l2) T x = pp E mu l1 T (pp E mu l2 T x) := by
  simp only [pp, List.map_append, List.prod_append, Module.End.mul_apply]

/- English proof (translation)
Simplify using `only [pp, List.map_cons, List.prod_cons, Module.End.mul_apply]`.
-/
theorem pp_cons (E : GLOps n K V) (mu : Fin n → ℤ) (ab : Fin n × Fin n) (l : List (Fin n × Fin n)) (T : ℕ) (x : V) :
    pp E mu (ab :: l) T x = ppFac E mu ab.1 ab.2 T (pp E mu l T x) := by
  simp only [pp, List.map_cons, List.prod_cons, Module.End.mul_apply]

end

/- English proof (translation)
Simplify using `only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero]`. Use `first`. Consider the case `simp only [Module.End.one_apply]`. Consider the case `simp only [LinearMap.one_apply]`.
-/
private theorem mem_weightSp_iff_forall_diag {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (ν : Fin n → ℤ) (y : V) :
    y ∈ weightSp E ν ↔ ∀ c, E c c y = (ν c : K) • y := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, sub_eq_zero]
  first
  | simp only [Module.End.one_apply]
  | simp only [LinearMap.one_apply]

/- English proof (translation)
Rewrite `hy`, the goal using `[mem_weightSp_iff_forall_diag]`. Introduce `c`. Establish `h` using `congrArg (fun f : Module.End K V => f y) (hE.1 c c a b)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, hy c, map_smul] at h`. Rewrite `h` using `[sub_eq_iff_eq_add]`.

Rewrite using `[h]`. Distinguish the cases in `hca : c = a`. Substitute `hca` using the available equality. Distinguish the cases in `hcb : c = b`. Substitute `hcb` using the available equality.

Simplify using `only [eq_self_iff_true, if_true]`. Use `push_cast`. Use `first`. Consider the case `module`. Consider the case `(simp [add_smul, sub_smul])`.

Establish `hbc : ¬ b = c` using `fun h => hcb h.symm`. Simplify using `only [eq_self_iff_true, if_true, if_neg hbc, if_neg hcb, LinearMap.zero_apply, sub_zero]`. Use `push_cast`. Use `first`. Consider the case `module`.

Consider the case `(simp [add_smul, sub_smul]; abel)`. Distinguish the cases in `hcb : c = b`. Substitute `hcb` using the available equality. Simplify using `only [eq_self_iff_true, if_true, if_neg hca, LinearMap.zero_apply, zero_sub]`. Use `push_cast`.

Use `first`. Consider the case `module`. Consider the case `(simp [add_smul, sub_smul]; abel)`. Establish `hbc : ¬ b = c` using `fun h => hcb h.symm`. Simplify using `only [if_neg hca, if_neg hbc, if_neg hcb, LinearMap.zero_apply, sub_zero, zero_add]`.

Use `push_cast`. Use `first`. Consider the case `module`. Consider the case `simp`.
-/
private theorem glRep_apply_mem_weightSp_shift {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (a b : Fin n) (ν : Fin n → ℤ) (y : V)
    (hy : y ∈ weightSp E ν) :
    E a b y ∈ weightSp E (fun c => ν c + ((if c = a then 1 else 0) - (if c = b then 1 else 0))) := by
  rw [mem_weightSp_iff_forall_diag] at hy ⊢
  intro c
  have h := congrArg (fun f : Module.End K V => f y) (hE.1 c c a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hy c, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  by_cases hca : c = a
  · subst hca
    by_cases hcb : c = b
    · subst hcb
      simp only [eq_self_iff_true, if_true]
      push_cast
      first
      | module
      | (simp [add_smul, sub_smul])
    · have hbc : ¬ b = c := fun h => hcb h.symm
      simp only [eq_self_iff_true, if_true, if_neg hbc, if_neg hcb, LinearMap.zero_apply, sub_zero]
      push_cast
      first
      | module
      | (simp [add_smul, sub_smul]; abel)
  · by_cases hcb : c = b
    · subst hcb
      simp only [eq_self_iff_true, if_true, if_neg hca, LinearMap.zero_apply, zero_sub]
      push_cast
      first
      | module
      | (simp [add_smul, sub_smul]; abel)
    · have hbc : ¬ b = c := fun h => hcb h.symm
      simp only [if_neg hca, if_neg hbc, if_neg hcb, LinearMap.zero_apply, sub_zero, zero_add]
      push_cast
      first
      | module
      | simp

/- English proof (translation)
Proceed by induction on `k generalizing ν y with`. Consider the case `zero => simpa using hy`. Consider the case `succ k ih`. Rewrite using `[pow_succ, Module.End.mul_apply]`. Establish `h1` using `ih _ _ (glRep_apply_mem_weightSp_shift E hE a b ν y hy)`.

Use `h1 using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `c`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem glRep_pow_apply_mem_weightSp_shift {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (a b : Fin n) (k : ℕ) (ν : Fin n → ℤ) (y : V)
    (hy : y ∈ weightSp E ν) :
    (E a b ^ k) y ∈ weightSp E
      (fun c => ν c + (k : ℤ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0))) := by
  induction k generalizing ν y with
  | zero => simpa using hy
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply]
    have h1 := ih _ _ (glRep_apply_mem_weightSp_shift E hE a b ν y hy)
    convert h1 using 2
    funext c
    push_cast
    ring

/- English proof (translation)
Unfold `ppFac`. Use `first`. Consider the case `rw [LinearMap.sum_apply]`. Consider the case `rw [LinearMap.coe_sum, Finset.sum_apply]`. Consider the case `rw [LinearMap.coe_fn_sum, Finset.sum_apply]`.

Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Simplify using `only [divPowE, LinearMap.smul_apply, Module.End.mul_apply, map_smul]`. Use `Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_))` and prove the remaining obligations. Establish `h1` using `glRep_pow_apply_mem_weightSp_shift E hE a b k ν y hy`. Establish `h2` using `glRep_pow_apply_mem_weightSp_shift E hE b a k _ _ h1`.

Use `h2 using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `c`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ppFac_apply_mem_weightSp_of_mem {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ) (a b : Fin n) (T : ℕ) (ν : Fin n → ℤ)
    (y : V) (hy : y ∈ weightSp E ν) : ppFac E mu a b T y ∈ weightSp E ν := by
  unfold ppFac
  first
  | rw [LinearMap.sum_apply]
  | rw [LinearMap.coe_sum, Finset.sum_apply]
  | rw [LinearMap.coe_fn_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  simp only [divPowE, LinearMap.smul_apply, Module.End.mul_apply, map_smul]
  refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_))
  have h1 := glRep_pow_apply_mem_weightSp_shift E hE a b k ν y hy
  have h2 := glRep_pow_apply_mem_weightSp_shift E hE b a k _ _ h1
  convert h2 using 2
  funext c
  ring

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simpa [pp] using hy`. Consider the case `cons ab l ih`. Rewrite using `[pp_cons]`. Conclude with `ppFac_apply_mem_weightSp_of_mem E hE mu ab.1 ab.2 T ν _ ih`.
-/
private theorem pp_apply_mem_weightSp_of_mem {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ) (l : List (Fin n × Fin n)) (T : ℕ)
    (ν : Fin n → ℤ) (y : V) (hy : y ∈ weightSp E ν) : pp E mu l T y ∈ weightSp E ν := by
  induction l with
  | nil => simpa [pp] using hy
  | cons ab l ih =>
    rw [pp_cons]
    exact ppFac_apply_mem_weightSp_of_mem E hE mu ab.1 ab.2 T ν _ ih

/- English proof (translation)
Consider the cases of `h with`. Consider the case `swap l1 l2 a b c d hac had hbc hbd`. Simplify using `only [pp_append, pp_cons, ppFac_eq]`. Use `congr 1`. Conclude with `LinearMap.congr_fun (hC K V n E hE a b c d hac had hbc hbd _ _ T).eq _`.

Consider the case `braid l1 l2 a b c hab hbc`. Simplify using `only [pp_append, pp_cons, ppFac_eq]`. Use `congr 1`. Establish `h1` using `hmu a b hab`. Establish `h2` using `hmu b c hbc`.

Establish `h3` using `hmu a c (hab.trans hbc)`. Establish `hab2 : (a : ℕ) < b` using `hab`. Establish `hbc2 : (b : ℕ) < c` using `hbc`. Establish `e1 : ((mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu b + ((b : ℤ) - (a : ℤ))` using `Int.toNat_of_nonneg (by omega)`. Establish `e2 : ((mu b - mu c + ((c : ℤ) - (b : ℤ))).toNat : ℤ) = mu b - mu c + ((c : ℤ) - (b : ℤ))` using `Int.toNat_of_nonneg (by omega)`.

Establish `e3 : ((mu a - mu c + ((c : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu c + ((c : ℤ) - (a : ℤ))` using `Int.toNat_of_nonneg (by omega)`. Establish `hu : (mu a - mu c + ((c : ℤ) - (a : ℤ))).toNat = (mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat + (mu b - mu c + ((c : ℤ) - (b : ℤ))).toNat`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hu]`. Conclude with `hY ((b : ℕ) - a - 1) ((c : ℕ) - b - 1) K V n E hE a b c hab.ne (hab.trans hbc).ne hbc.ne mu _ _ (by omega) (by omega) T hT _ (pp_apply_mem_weightSp_of_mem E hE mu l2 T mu x hx)`.

Consider the case `braid' l1 l2 a b c hab hbc`. Simplify using `only [pp_append, pp_cons, ppFac_eq]`. Use `congr 1`. Establish `h1` using `hmu a b hab`. Establish `h2` using `hmu b c hbc`.

Establish `h3` using `hmu a c (hab.trans hbc)`. Establish `hab2 : (a : ℕ) < b` using `hab`. Establish `hbc2 : (b : ℕ) < c` using `hbc`. Establish `e1 : ((mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu b + ((b : ℤ) - (a : ℤ))` using `Int.toNat_of_nonneg (by omega)`. Establish `e2 : ((mu b - mu c + ((c : ℤ) - (b : ℤ))).toNat : ℤ) = mu b - mu c + ((c : ℤ) - (b : ℤ))` using `Int.toNat_of_nonneg (by omega)`.

Establish `e3 : ((mu a - mu c + ((c : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu c + ((c : ℤ) - (a : ℤ))` using `Int.toNat_of_nonneg (by omega)`. Establish `hu : (mu a - mu c + ((c : ℤ) - (a : ℤ))).toNat = (mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat + (mu b - mu c + ((c : ℤ) - (b : ℤ))).toNat`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hu]`. Conclude with `(hY ((b : ℕ) - a - 1) ((c : ℕ) - b - 1) K V n E hE a b c hab.ne (hab.trans hbc).ne hbc.ne mu _ _ (by omega) (by omega) T hT _ (pp_apply_mem_weightSp_of_mem E hE mu l2 T mu x hx)).symm`.
-/
theorem pp_step (hC : RestComm) (hY : RestYB) {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ)
    (hmu : ∀ a b : Fin n, a < b → 1 ≤ mu a - mu b + ((b : ℤ) - (a : ℤ))) (T : ℕ) (hT : Module.finrank K V ≤ T)
    {l l' : List (Fin n × Fin n)} (h : Step n l l') (x : V) (hx : x ∈ weightSp E mu) :
    pp E mu l T x = pp E mu l' T x := by
  cases h with
  | swap l1 l2 a b c d hac had hbc hbd =>
    simp only [pp_append, pp_cons, ppFac_eq]
    congr 1
    exact LinearMap.congr_fun (hC K V n E hE a b c d hac had hbc hbd _ _ T).eq _
  | braid l1 l2 a b c hab hbc =>
    simp only [pp_append, pp_cons, ppFac_eq]
    congr 1
    have h1 := hmu a b hab
    have h2 := hmu b c hbc
    have h3 := hmu a c (hab.trans hbc)
    have hab2 : (a : ℕ) < b := hab
    have hbc2 : (b : ℕ) < c := hbc
    have e1 : ((mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu b + ((b : ℤ) - (a : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have e2 : ((mu b - mu c + ((c : ℤ) - (b : ℤ))).toNat : ℤ) = mu b - mu c + ((c : ℤ) - (b : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have e3 : ((mu a - mu c + ((c : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu c + ((c : ℤ) - (a : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have hu : (mu a - mu c + ((c : ℤ) - (a : ℤ))).toNat =
        (mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat + (mu b - mu c + ((c : ℤ) - (b : ℤ))).toNat := by
      omega
    rw [hu]
    exact hY ((b : ℕ) - a - 1) ((c : ℕ) - b - 1) K V n E hE a b c hab.ne (hab.trans hbc).ne hbc.ne
      mu _ _ (by omega) (by omega) T hT _ (pp_apply_mem_weightSp_of_mem E hE mu l2 T mu x hx)
  | braid' l1 l2 a b c hab hbc =>
    simp only [pp_append, pp_cons, ppFac_eq]
    congr 1
    have h1 := hmu a b hab
    have h2 := hmu b c hbc
    have h3 := hmu a c (hab.trans hbc)
    have hab2 : (a : ℕ) < b := hab
    have hbc2 : (b : ℕ) < c := hbc
    have e1 : ((mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu b + ((b : ℤ) - (a : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have e2 : ((mu b - mu c + ((c : ℤ) - (b : ℤ))).toNat : ℤ) = mu b - mu c + ((c : ℤ) - (b : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have e3 : ((mu a - mu c + ((c : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu c + ((c : ℤ) - (a : ℤ)) :=
      Int.toNat_of_nonneg (by omega)
    have hu : (mu a - mu c + ((c : ℤ) - (a : ℤ))).toNat =
        (mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat + (mu b - mu c + ((c : ℤ) - (b : ℤ))).toNat := by
      omega
    rw [hu]
    exact (hY ((b : ℕ) - a - 1) ((c : ℕ) - b - 1) K V n E hE a b c hab.ne (hab.trans hbc).ne hbc.ne
      mu _ _ (by omega) (by omega) T hT _ (pp_apply_mem_weightSp_of_mem E hE mu l2 T mu x hx)).symm

/- English proof (translation)
Introduce `K V _ _ _ _ _ n E hE mu hmu ord hord T hT x hx a b hab`. Take `⟨l, hl⟩` from `hN n ord hord a b hab`. Establish `key : ∀ l', Relation.ReflTransGen (Step n) ord l' → pp E mu ord T x = pp E mu l' T x`. Introduce `l' hl'`. Proceed by induction on `hl' with`.

Consider the case `refl => rfl`. Consider the case `tail _ hs ih => rw [ih, pp_step hC hY E hE mu hmu T hT hs x hx]`. Establish `hlt : a < b`. Rewrite using `[Fin.lt_iff_val_lt_val]`. Use linear arithmetic over natural numbers and integers.

Establish `h1` using `hmu a b hlt`. Establish `hba : ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) = 1` using `by omega`. Establish `key2 : ((mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu b + 1`. Rewrite using `[Int.toNat_of_nonneg (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[key _ hl, pp_cons, ppFac_eq]`. Conclude with `hK K V n E hE a b hlt.ne mu _ key2 T hT _ (pp_apply_mem_weightSp_of_mem E hE mu l T mu x hx)`.
-/
theorem raising_kill_of_interface (hN : RestConn) (hC : RestComm) (hY : RestYB) (hK : RestKill) : SimpleRaisingKillsExtremalProjector := by
  intro K V _ _ _ _ _ n E hE mu hmu ord hord T hT x hx a b hab
  obtain ⟨l, hl⟩ := hN n ord hord a b hab
  have key : ∀ l', Relation.ReflTransGen (Step n) ord l' → pp E mu ord T x = pp E mu l' T x := by
    intro l' hl'
    induction hl' with
    | refl => rfl
    | tail _ hs ih => rw [ih, pp_step hC hY E hE mu hmu T hT hs x hx]
  have hlt : a < b := by
    rw [Fin.lt_iff_val_lt_val]
    omega
  have h1 := hmu a b hlt
  have hba : ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) = 1 := by omega
  have key2 : ((mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat : ℤ) = mu a - mu b + 1 := by
    rw [Int.toNat_of_nonneg (by linarith)]
    linarith
  rw [key _ hl, pp_cons, ppFac_eq]
  exact hK K V n E hE a b hlt.ne mu _ key2 T hT _ (pp_apply_mem_weightSp_of_mem E hE mu l T mu x hx)

end Formalism.MainNotions.G.ExtremalProjector
