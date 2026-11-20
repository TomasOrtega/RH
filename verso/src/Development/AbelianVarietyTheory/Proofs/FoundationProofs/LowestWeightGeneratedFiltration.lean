import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FockGrade

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Establish `h1` using `congrArg (fun f : Module.End ℂ V => f x) (h (Eab a b) (Eab c d))`. Simplify using `only [map_sub, LinearMap.sub_apply, Module.End.mul_apply] at h1`. Establish `e1 : act (Eab a b * Eab c d) x = if b = c then act (Eab a d) x else 0` using `by split_ifs with hbc`. Substitute `hbc` using the available equality. Simplify using `[Eab, Matrix.single_mul_single_same]`.

Simplify using `[Eab, Matrix.single_mul_single_of_ne _ _ _ _ hbc]`. Establish `e2 : act (Eab c d * Eab a b) x = if d = a then act (Eab c b) x else 0` using `by split_ifs with hbc`. Substitute `hbc` using the available equality. Simplify using `[Eab, Matrix.single_mul_single_same]`. Simplify using `[Eab, Matrix.single_mul_single_of_ne _ _ _ _ hbc]`.

Rewrite using `[← e1, ← e2, add_sub_assoc, h1]`. Normalize the expressions using the abelian group laws.
-/
theorem act_Eab_comm {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) (a b c d : Ix p q) (x : V) :
    act (Eab a b) (act (Eab c d) x) = act (Eab c d) (act (Eab a b) x) +
      (if b = c then act (Eab a d) x else 0) - (if d = a then act (Eab c b) x else 0) := by
  have h1 := congrArg (fun f : Module.End ℂ V => f x) (h (Eab a b) (Eab c d))
  simp only [map_sub, LinearMap.sub_apply, Module.End.mul_apply] at h1
  have e1 : act (Eab a b * Eab c d) x = if b = c then act (Eab a d) x else 0 := by
    split_ifs with hbc
    · subst hbc; simp [Eab, Matrix.single_mul_single_same]
    · simp [Eab, Matrix.single_mul_single_of_ne _ _ _ _ hbc]
  have e2 : act (Eab c d * Eab a b) x = if d = a then act (Eab c b) x else 0 := by
    split_ifs with hbc
    · subst hbc; simp [Eab, Matrix.single_mul_single_same]
    · simp [Eab, Matrix.single_mul_single_of_ne _ _ _ _ hbc]
  rw [← e1, ← e2, add_sub_assoc, h1]; abel

def layer (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (W : Submodule ℂ V) (m : ℕ) : Submodule ℂ V :=
  Nat.rec W (fun _ N => ⨆ ab : Fin p × Fin q, N.map (act (Eab (Sum.inl ab.1) (Sum.inr ab.2)))) m

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem layer_succ (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (W : Submodule ℂ V) (m : ℕ) :
    layer act W (m + 1) =
      ⨆ ab : Fin p × Fin q, (layer act W m).map (act (Eab (Sum.inl ab.1) (Sum.inr ab.2))) := rfl

/- English proof (translation)
The claim follows from `Submodule.mem_iSup_of_mem (a, b) (Submodule.mem_map_of_mem hy)`.
-/
theorem raise_mem {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {W : Submodule ℂ V} {m : ℕ} (a : Fin p) (b : Fin q)
    {y : V} (hy : y ∈ layer act W m) : act (Eab (Sum.inl a) (Sum.inr b)) y ∈ layer act W (m + 1) :=
  Submodule.mem_iSup_of_mem (a, b) (Submodule.mem_map_of_mem hy)

/- English proof (translation)
Use `iSup_le fun ab => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `h _ _ y hy`.
-/
theorem layer_succ_le {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {W : Submodule ℂ V} {m : ℕ} {S : Submodule ℂ V}
    (h : ∀ a b, ∀ y ∈ layer act W m, act (Eab (Sum.inl a) (Sum.inr b)) y ∈ S) : layer act W (m + 1) ≤ S := by
  refine iSup_le fun ab => ?_
  rintro _ ⟨y, hy, rfl⟩
  exact h _ _ y hy

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact hW`. Consider the case `succ m ih => rw [layer_succ]`. Use `infer_instance`.
-/
theorem layer_finite {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {W : Submodule ℂ V} (hW : FiniteDimensional ℂ W)
    (m : ℕ) : FiniteDimensional ℂ (layer act W m) := by
  induction m with
  | zero => exact hW
  | succ m ih => rw [layer_succ]; infer_instance

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro a b hab y hy`. Conclude with `hK _ (GlobalTheory.FockTensor.isKC_Eab hab) y hy`. Consider the case `succ m ih`. Introduce `a b hab`.

Establish `: layer act W (m + 1) ≤ (layer act W (m + 1)).comap (act (Eab a b))`. Use `layer_succ_le fun i j y hy => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_comap, act_Eab_comm h]`. Use `sub_mem (add_mem (raise_mem _ _ (ih a b hab y hy)) ?_) ?_` and prove the remaining obligations. Use `split_ifs with hb`.

Substitute `hb` using the available equality. Break down `a with a | a` into its components or cases. Conclude with `raise_mem _ _ hy`. Conclude with `absurd hab (by simp [sameBlock])`. Conclude with `zero_mem _`.

Use `split_ifs with hb`. Substitute `hb` using the available equality. Break down `b with b | b` into its components or cases. Conclude with `absurd hab (by simp [sameBlock])`. Conclude with `raise_mem _ _ hy`.

Conclude with `zero_mem _`. Conclude with `fun y hy => this hy`.
-/
theorem layer_compact {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) {W : Submodule ℂ V}
    (hK : KStable act W) (m : ℕ) : ∀ a b, sameBlock a b → ∀ y ∈ layer act W m,
      act (Eab a b) y ∈ layer act W m := by
  induction m with
  | zero => intro a b hab y hy; exact hK _ (GlobalTheory.FockTensor.isKC_Eab hab) y hy
  | succ m ih =>
    intro a b hab
    have : layer act W (m + 1) ≤ (layer act W (m + 1)).comap (act (Eab a b)) := by
      refine layer_succ_le fun i j y hy => ?_
      rw [Submodule.mem_comap, act_Eab_comm h]
      refine sub_mem (add_mem (raise_mem _ _ (ih a b hab y hy)) ?_) ?_
      · split_ifs with hb
        · subst hb
          rcases a with a | a
          · exact raise_mem _ _ hy
          · exact absurd hab (by simp [sameBlock])
        · exact zero_mem _
      · split_ifs with hb
        · subst hb
          rcases b with b | b
          · exact absurd hab (by simp [sameBlock])
          · exact raise_mem _ _ hy
        · exact zero_mem _
    exact fun y hy => this hy

/- English proof (translation)
Establish `: (⨆ m, layer act W m) ≤ (⨆ m, layer act W m).comap f` using `iSup_le fun m y hy => hf m y hy`. Conclude with `fun y hy => this hy`.
-/
theorem sup_stable_of {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {W : Submodule ℂ V} {f : Module.End ℂ V}
    (hf : ∀ m, ∀ y ∈ layer act W m, f y ∈ ⨆ m, layer act W m) :
    ∀ y ∈ ⨆ m, layer act W m, f y ∈ ⨆ m, layer act W m := by
  have : (⨆ m, layer act W m) ≤ (⨆ m, layer act W m).comap f := iSup_le fun m y hy => hf m y hy
  exact fun y hy => this hy

/- English proof (translation)
Establish `hk : ∀ a b, sameBlock a b → ∀ y ∈ ⨆ m, layer act W m, act (Eab a b) y ∈ ⨆ m, layer act W m` using `fun a b hab => sup_stable_of fun m y hy => Submodule.mem_iSup_of_mem m (layer_compact h hK m a b hab y hy)`. Establish `hr : ∀ a b, ∀ y ∈ ⨆ m, layer act W m, act (Eab (Sum.inl a) (Sum.inr b)) y ∈ ⨆ m, layer act W m` using `fun a b => sup_stable_of fun m y hy => Submodule.mem_iSup_of_mem (m + 1) (raise_mem a b hy)`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b`. Conclude with `hk _ _ trivial`. Conclude with `hr _ _`.

Use `sup_stable_of fun m => ?_` and prove the remaining obligations. Proceed by induction on `m with`. Consider the case `zero => intro y hy`. Rewrite using `[hL y hy b a]`. Conclude with `zero_mem _`.

Consider the case `succ m ih`. Establish `: layer act W (m + 1) ≤ (⨆ m, layer act W m).comap (act (Eab (Sum.inr a) (Sum.inl b)))`. Use `layer_succ_le fun i j y hy => ?_` and prove the remaining obligations. Establish `hy' : y ∈ ⨆ m, layer act W m` using `Submodule.mem_iSup_of_mem m hy`. Rewrite using `[Submodule.mem_comap, act_Eab_comm h]`.

Use `sub_mem (add_mem (hr _ _ _ (ih y hy)) ?_) ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `hk (Sum.inr a) (Sum.inr j) trivial _ hy'`. Conclude with `zero_mem _`. Use `split_ifs`.

Conclude with `hk (Sum.inl i) (Sum.inl b) trivial _ hy'`. Conclude with `zero_mem _`. Conclude with `fun y hy => this hy`. Conclude with `hk _ _ trivial`.
-/
theorem sup_stable {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) {W : Submodule ℂ V}
    (hK : KStable act W) (hL : ∀ e ∈ W, KilledByLower act e) (a b : Ix p q) :
    ∀ y ∈ ⨆ m, layer act W m, act (Eab a b) y ∈ ⨆ m, layer act W m := by
  have hk : ∀ a b, sameBlock a b → ∀ y ∈ ⨆ m, layer act W m, act (Eab a b) y ∈ ⨆ m, layer act W m :=
    fun a b hab => sup_stable_of fun m y hy => Submodule.mem_iSup_of_mem m (layer_compact h hK m a b hab y hy)
  have hr : ∀ a b, ∀ y ∈ ⨆ m, layer act W m,
      act (Eab (Sum.inl a) (Sum.inr b)) y ∈ ⨆ m, layer act W m :=
    fun a b => sup_stable_of fun m y hy => Submodule.mem_iSup_of_mem (m + 1) (raise_mem a b hy)
  rcases a with a | a <;> rcases b with b | b
  · exact hk _ _ trivial
  · exact hr _ _
  · refine sup_stable_of fun m => ?_
    induction m with
    | zero => intro y hy; rw [hL y hy b a]; exact zero_mem _
    | succ m ih =>
      have : layer act W (m + 1) ≤ (⨆ m, layer act W m).comap (act (Eab (Sum.inr a) (Sum.inl b))) := by
        refine layer_succ_le fun i j y hy => ?_
        have hy' : y ∈ ⨆ m, layer act W m := Submodule.mem_iSup_of_mem m hy
        rw [Submodule.mem_comap, act_Eab_comm h]
        refine sub_mem (add_mem (hr _ _ _ (ih y hy)) ?_) ?_
        · split_ifs
          · exact hk (Sum.inr a) (Sum.inr j) trivial _ hy'
          · exact zero_mem _
        · split_ifs
          · exact hk (Sum.inl i) (Sum.inl b) trivial _ hy'
          · exact zero_mem _
      exact fun y hy => this hy
  · exact hk _ _ trivial

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => intro x hx`. Simplify using `using hc x hx`. Consider the case `succ m ih`. Establish `: layer act W (m + 1) ≤ LinearMap.ker ((∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i))) - (c + ((m + 1 : ℕ) : ℂ)) • (LinearMap.id : V →ₗ[ℂ] V))`.

Use `layer_succ_le fun a b y hy => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sum_apply, sub_eq_zero]`. Establish `e : ∀ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) (act (Eab (Sum.inl a) (Sum.inr b)) y) = act (Eab (Sum.inl a) (Sum.inr b)) (act (Eab (Sum.inl i) (Sum.inl i)) y) + (if i = a then act (Eab (Sum.inl a) (Sum.inr b)) y else 0)`. Introduce `i`. Rewrite using `[act_Eab_comm h]`.

Distinguish the cases in `hi : i = a`. Substitute `hi` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hi]`. Simplify using `only [e, Finset.sum_add_distrib, ← map_sum, ih y hy]`.

Simplify using `[add_smul, add_assoc]`. Introduce `x hx`. Establish `h2` using `this hx`. Rewrite `h2` using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sum_apply, sub_eq_zero]`. Simplify using `using h2`.
-/
theorem layer_eigen {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) {W : Submodule ℂ V} {c : ℂ}
    (hc : ∀ e ∈ W, ∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) e = c • e) (m : ℕ) :
    ∀ x ∈ layer act W m, ∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) x = (c + m) • x := by
  induction m with
  | zero => intro x hx; simpa using hc x hx
  | succ m ih =>
    have : layer act W (m + 1) ≤ LinearMap.ker ((∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i))) -
        (c + ((m + 1 : ℕ) : ℂ)) • (LinearMap.id : V →ₗ[ℂ] V)) := by
      refine layer_succ_le fun a b y hy => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sum_apply, sub_eq_zero]
      have e : ∀ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) (act (Eab (Sum.inl a) (Sum.inr b)) y) =
          act (Eab (Sum.inl a) (Sum.inr b)) (act (Eab (Sum.inl i) (Sum.inl i)) y) +
            (if i = a then act (Eab (Sum.inl a) (Sum.inr b)) y else 0) := by
        intro i
        rw [act_Eab_comm h]
        by_cases hi : i = a
        · subst hi; simp
        · simp [hi]
      simp only [e, Finset.sum_add_distrib, ← map_sum, ih y hy]
      simp [add_smul, add_assoc]
    intro x hx
    have h2 := this hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sum_apply, sub_eq_zero] at h2
    simpa using h2

/- English proof (translation)
Introduce `p q V _ _ act h W c hW hK hL hc`. Use `⟨layer act W, rfl, layer_finite hW, le_antisymm ?_ ?_, layer_eigen h hc⟩` and prove the remaining obligations. Use `iSup_le fun m => le_sInf fun S hS => ?_` and prove the remaining obligations. Proceed by induction on `m with`. Consider the case `zero => exact hS.1`.

Consider the case `succ m ih => exact layer_succ_le fun a b y hy => hS.2 _ _ (ih hy)`. Use `sInf_le ⟨fun x hx => Submodule.mem_iSup_of_mem 0 hx, fun Z y hy => ?_⟩` and prove the remaining obligations. Establish `hZ : Z = ∑ a, ∑ b, Z a b • Eab a b` using `by conv_lhs => rw [Matrix.matrix_eq_sum_single Z]`. Simplify using `[Eab, Matrix.smul_single]`. Rewrite using `[hZ]`.

Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (sup_stable h hK hL a b y hy)`.
-/
theorem exists_grading : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (W : Submodule ℂ V) (c : ℂ), FiniteDimensional ℂ W → KStable act W → (∀ e ∈ W, KilledByLower act e) → (∀ e ∈ W, ∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) e = c • e) → ∃ N : ℕ → Submodule ℂ V, N 0 = W ∧ (∀ m, FiniteDimensional ℂ (N m)) ∧ (⨆ m, N m) = genSub act (W : Set V) ∧ ∀ m : ℕ, ∀ x ∈ N m, ∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) x = (c + m) • x := by
  intro p q V _ _ act h W c hW hK hL hc
  refine ⟨layer act W, rfl, layer_finite hW, le_antisymm ?_ ?_, layer_eigen h hc⟩
  · refine iSup_le fun m => le_sInf fun S hS => ?_
    induction m with
    | zero => exact hS.1
    | succ m ih => exact layer_succ_le fun a b y hy => hS.2 _ _ (ih hy)
  · refine sInf_le ⟨fun x hx => Submodule.mem_iSup_of_mem 0 hx, fun Z y hy => ?_⟩
    have hZ : Z = ∑ a, ∑ b, Z a b • Eab a b := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
      simp [Eab, Matrix.smul_single]
    rw [hZ]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ _ (sup_stable h hK hL a b y hy)

end GlobalTheory.FockGrade
