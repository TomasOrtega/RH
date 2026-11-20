import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInOfIsPowDeg
import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.RawDegreeForms

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DegCompare

open GlobalTheory.PsiInPull GlobalTheory.PsiInPow

section Generic

variable {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (z : Z)

/- English proof (translation)
Use `choose V hVU hvV s hs using fun v : U => H v.1 v.2`. Establish `hm : ∀ v, f z ∈ V v` using `fun v => hz _ (fun h0 => (h0.le (hvV v) : v.1 ∈ (⊥ : Y.Opens)))`. Take `⟨a, ha, -⟩` from `Y.sheaf.existsUnique_gluing' V U (fun v => homOfLE (hVU v)) (fun y hy => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hvV ⟨y, hy⟩⟩) s (fun v w => gs_injective f z hz (V v ⊓ V w) ⟨hm v, hm w⟩ ((gs_res f z inf_le_left ⟨hm v, hm w⟩ _).trans ((hs v).trans ((hs w).symm.trans (gs_res f …`. Use `⟨a, ?_⟩` and prove the remaining obligations. Conclude with `(gs_res f z (hVU ⟨_, hU⟩) (hm ⟨_, hU⟩) a).symm.trans ((congrArg (gs f z _) (ha ⟨_, hU⟩)).trans (hs _))`.
-/
theorem exists_fn_of_locally [IsReduced Y] (hz : ∀ U : Y.Opens, U ≠ ⊥ → f z ∈ U) (t : Z.presheaf.stalk z)
    (U : Y.Opens) (hU : f z ∈ U)
    (H : ∀ v ∈ U, ∃ V : Y.Opens, V ≤ U ∧ v ∈ V ∧ ∃ s : Γ(Y, V), gs f z V s = t) :
    ∃ r : Γ(Y, U), gs f z U r = t := by
  choose V hVU hvV s hs using fun v : U => H v.1 v.2
  have hm : ∀ v, f z ∈ V v := fun v => hz _ (fun h0 => (h0.le (hvV v) : v.1 ∈ (⊥ : Y.Opens)))
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' V U (fun v => homOfLE (hVU v))
    (fun y hy => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hvV ⟨y, hy⟩⟩) s
    (fun v w => gs_injective f z hz (V v ⊓ V w) ⟨hm v, hm w⟩
      ((gs_res f z inf_le_left ⟨hm v, hm w⟩ _).trans ((hs v).trans ((hs w).symm.trans
        (gs_res f z inf_le_right ⟨hm v, hm w⟩ _).symm))))
  refine ⟨a, ?_⟩
  exact (gs_res f z (hVU ⟨_, hU⟩) (hm ⟨_, hU⟩) a).symm.trans ((congrArg (gs f z _) (ha ⟨_, hU⟩)).trans (hs _))

variable {L : LB X} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)

/- English proof (translation)
The claim follows from `(gs_unit f z (LB.wchart L φ j ⊓ LB.wchart L φ j') ⟨hj, hj'⟩ _).trans (congrArg Units.val (gm_linComb L φ ε f z j j' hj hj'))`.
-/
theorem gs_trans {j j' : K → L.ι} (hj : f z ∈ LB.wchart L φ j) (hj' : f z ∈ LB.wchart L φ j') :
    gs f z (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j').val = (trF φ ε f z j j').val :=
  (gs_unit f z (LB.wchart L φ j ⊓ LB.wchart L φ j') ⟨hj, hj'⟩ _).trans (congrArg Units.val (gm_linComb L φ ε f z j j' hj hj'))

/- English proof (translation)
Establish `glue : ∀ j : K → L.ι, ∃ a : Γ(Y, LB.wchart L φ j), f z ∈ LB.wchart L φ j → gs f z (LB.wchart L φ j) a = t j`. Introduce `j`. Distinguish the cases in `hj : f z ∈ LB.wchart L φ j`. Use `swap`. Conclude with `⟨0, fun h => (hj h).elim⟩`.

Use `(exists_fn_of_locally f z hz (t j) _ hj fun v hv => ?_).imp fun _ h _ => h` and prove the remaining obligations. Take `⟨j', V, hV, hvV, s, hs⟩` from `H v`. Establish `hm : f z ∈ V` using `hz _ (fun h0 => (h0.le hvV : v ∈ (⊥ : Y.Opens)))`. Establish `l₁ : LB.wchart L φ j ⊓ V ≤ LB.wchart L φ j ⊓ LB.wchart L φ j'` using `inf_le_inf_left _ hV`. Use `⟨LB.wchart L φ j ⊓ V, inf_le_left, ⟨hv, hvV⟩, (Y.presheaf.map (homOfLE l₁).op).hom ((LB.LinComb L φ ε).g j j').val * (Y.presheaf.map (homOfLE inf_le_right).op).hom s, ?_⟩` and prove the remaining obligations.

Use `(gs_mul f z (LB.wchart L φ j ⊓ V) ⟨hj, hm⟩ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (ht j j' hj (hV hm)).symm)` and prove the remaining obligations. Conclude with `(gs_res f z l₁ ⟨hj, hm⟩ _).trans (gs_trans f z φ ε hj (hV hm))`. Conclude with `(gs_res f z inf_le_right ⟨hj, hm⟩ _).trans hs`. Use `choose a ha using glue`. Use `⟨⟨a, fun j j' => ?_⟩, ha⟩` and prove the remaining obligations.

Distinguish the cases in `hm : f z ∈ LB.wchart L φ j ⊓ LB.wchart L φ j'`. Use `gs_injective f z hz (LB.wchart L φ j ⊓ LB.wchart L φ j') hm ?_` and prove the remaining obligations. Use `(gs_res f z inf_le_left hm _).trans (((ha j hm.1).trans (ht j j' hm.1 hm.2)).trans ((gs_mul f z _ hm _ _).trans (congrArg₂ (· * ·) (gs_trans f z φ ε hm.1 hm.2) ((gs_res f z inf_le_right hm _).trans (ha j' hm.2)))).symm)` and prove the remaining obligations. Conclude with `fn_ext fun y hy => (hm (hz _ fun h0 => (h0.le hy : y ∈ (⊥ : Y.Opens)))).elim`.
-/
theorem exists_sec_of_locally [IsReduced Y] (hz : ∀ U : Y.Opens, U ≠ ⊥ → f z ∈ U)
    (t : (K → L.ι) → Z.presheaf.stalk z)
    (ht : ∀ j j', f z ∈ LB.wchart L φ j → f z ∈ LB.wchart L φ j' → t j = (trF φ ε f z j j').val * t j')
    (H : ∀ v : Y, ∃ (j : K → L.ι) (V : Y.Opens), V ≤ LB.wchart L φ j ∧ v ∈ V ∧ ∃ s : Γ(Y, V), gs f z V s = t j) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ j, f z ∈ LB.wchart L φ j → gs f z (LB.wchart L φ j) (s.f j) = t j := by
  have glue : ∀ j : K → L.ι, ∃ a : Γ(Y, LB.wchart L φ j),
      f z ∈ LB.wchart L φ j → gs f z (LB.wchart L φ j) a = t j := by
    intro j
    by_cases hj : f z ∈ LB.wchart L φ j
    swap
    · exact ⟨0, fun h => (hj h).elim⟩
    refine (exists_fn_of_locally f z hz (t j) _ hj fun v hv => ?_).imp fun _ h _ => h
    obtain ⟨j', V, hV, hvV, s, hs⟩ := H v
    have hm : f z ∈ V := hz _ (fun h0 => (h0.le hvV : v ∈ (⊥ : Y.Opens)))
    have l₁ : LB.wchart L φ j ⊓ V ≤ LB.wchart L φ j ⊓ LB.wchart L φ j' := inf_le_inf_left _ hV
    refine ⟨LB.wchart L φ j ⊓ V, inf_le_left, ⟨hv, hvV⟩,
      (Y.presheaf.map (homOfLE l₁).op).hom ((LB.LinComb L φ ε).g j j').val *
        (Y.presheaf.map (homOfLE inf_le_right).op).hom s, ?_⟩
    refine (gs_mul f z (LB.wchart L φ j ⊓ V) ⟨hj, hm⟩ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (ht j j' hj (hV hm)).symm)
    · exact (gs_res f z l₁ ⟨hj, hm⟩ _).trans (gs_trans f z φ ε hj (hV hm))
    · exact (gs_res f z inf_le_right ⟨hj, hm⟩ _).trans hs
  choose a ha using glue
  refine ⟨⟨a, fun j j' => ?_⟩, ha⟩
  by_cases hm : f z ∈ LB.wchart L φ j ⊓ LB.wchart L φ j'
  · refine gs_injective f z hz (LB.wchart L φ j ⊓ LB.wchart L φ j') hm ?_
    refine (gs_res f z inf_le_left hm _).trans (((ha j hm.1).trans (ht j j' hm.1 hm.2)).trans
      ((gs_mul f z _ hm _ _).trans (congrArg₂ (· * ·) (gs_trans f z φ ε hm.1 hm.2)
        ((gs_res f z inf_le_right hm _).trans (ha j' hm.2)))).symm)
  · exact fn_ext fun y hy => (hm (hz _ fun h0 => (h0.le hy : y ∈ (⊥ : Y.Opens)))).elim

/- English proof (translation)
Use `choose I hI using fun k => exists_chart hL (φ k v)`. Conclude with `⟨I, Set.mem_iInter.2 hI⟩`.
-/
theorem exists_wchart (hL : L.IsLB) (v : Y) : ∃ j, v ∈ LB.wchart L φ j := by
  choose I hI using fun k => exists_chart hL (φ k v)
  exact ⟨I, Set.mem_iInter.2 hI⟩

/- English proof (translation)
Simplify using `only [gs_eq f z U h, map_pow]`.
-/
theorem gs_pow (U : Y.Opens) (h : f z ∈ U) (a : Γ(Y, U)) (n : ℕ) : gs f z U (a ^ n) = gs f z U a ^ n := by
  simp only [gs_eq f z U h, map_pow]

/- English proof (translation)
Establish `loc : ∀ v : Y, ∃ (j' : K → L.ι) (V : Y.Opens), V ≤ LB.wchart L φ j' ∧ v ∈ V ∧ ∃ (m : ℕ) (s : Γ(Y, V)), gs f z V s = gs f z ⊤ b ^ m * (trF φ ε f z j' j).val`. Introduce `v`. Take `⟨j', hj'⟩` from `exists_wchart φ hL v`. Take `⟨_, ⟨V, hV, rfl⟩, hvV, hVj⟩` from `Y.isBasis_affineOpens.exists_subset_of_mem_open hj' (LB.wchart L φ j').isOpen`. Establish `hm : f z ∈ V` using `hz _ (fun h0 => (h0.le hvV : v ∈ (⊥ : Y.Opens)))`.

Set `b' : Γ(Y, V)` to `(Y.presheaf.map (homOfLE le_top).op).hom b`. Establish `e : Y.basicOpen b' = V ⊓ Y.basicOpen b` using `Y.basicOpen_res _ _`. Establish `hm' : f z ∈ Y.basicOpen b'` using `e.ge ⟨hm, hzb⟩`. Establish `l : Y.basicOpen b' ≤ LB.wchart L φ j' ⊓ LB.wchart L φ j` using `e.le.trans (inf_le_inf hVj hb)`. Take `⟨n, y, hy⟩` from `exists_eq_pow_mul_of_isAffineOpen Y V hV b' ((Y.presheaf.map (homOfLE l).op).hom ((LB.LinComb L φ ε).g j' j).val)`.

Use `⟨j', V, hVj, hvV, n, y, ?_⟩` and prove the remaining obligations. Use `(gs_res f z (Y.basicOpen_le b') hm' y).symm.trans ((congrArg (gs f z _) hy).trans ((gs_mul f z _ hm' _ _).trans (congrArg₂ (· * ·) ?_ ?_)))` and prove the remaining obligations. Conclude with `(gs_pow f z _ hm' _ _).trans (congrArg (· ^ n) ((gs_res f z (Y.basicOpen_le b') hm' b').trans (gs_res f z le_top hm b)))`. Conclude with `(gs_res f z l hm' _).trans (gs_trans f z φ ε (hVj hm) (hb hzb))`. Use `choose I V hV hvV m s hs using loc`.

Take `⟨T, hT⟩` from `(isCompact_univ (X := Y)).elim_finite_subcover (fun v => (V v : Set Y)) (fun v => (V v).isOpen) (fun v _ => Set.mem_iUnion.2 ⟨v, hvV v⟩)`. Take `⟨σ, hσ⟩` from `exists_sec_of_locally f z φ ε hz (fun j' => gs f z ⊤ b ^ (T.sup m) * (trF φ ε f z j' j).val) (fun j₁ j₂ h₁ h₂ => by`. Rewrite using `[← trF_trans hL φ ε f z h₁ h₂ (hb hzb), Units.val_mul, mul_left_comm])`. Use the proof step `(fun v => by`. Take `⟨w, hw, hvw⟩` from `Set.mem_iUnion₂.1 (hT (Set.mem_univ v))`.

Establish `hm : f z ∈ V w` using `hz _ (fun h0 => (h0.le (hvV w) : w ∈ (⊥ : Y.Opens)))`. Use `⟨I w, V w, hV w, hvw, (Y.presheaf.map (homOfLE le_top).op).hom b ^ (T.sup m - m w) * s w, ?_⟩` and prove the remaining obligations. Rewrite using `[gs_mul f z _ hm, gs_pow f z _ hm, gs_res f z le_top hm, hs, ← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel (Finset.le_sup hw)])`. Use `⟨T.sup m, σ, (hσ j (hb hzb)).trans ?_⟩` and prove the remaining obligations. Rewrite using `[mul_eq_left.1 (trF_trans hL φ ε f z (hb hzb) (hb hzb) (hb hzb)), Units.val_one, _root_.mul_one]`.
-/
theorem exists_sec_pow [IsAffine Y] [IsReduced Y] (hz : ∀ U : Y.Opens, U ≠ ⊥ → f z ∈ U) (hL : L.IsLB)
    (b : Γ(Y, ⊤)) (j : K → L.ι) (hb : Y.basicOpen b ≤ LB.wchart L φ j) (hzb : f z ∈ Y.basicOpen b) :
    ∃ (m : ℕ) (s : LB.Sec (LB.LinComb L φ ε)), gs f z (LB.wchart L φ j) (s.f j) = gs f z ⊤ b ^ m := by
  have loc : ∀ v : Y, ∃ (j' : K → L.ι) (V : Y.Opens), V ≤ LB.wchart L φ j' ∧ v ∈ V ∧ ∃ (m : ℕ) (s : Γ(Y, V)),
      gs f z V s = gs f z ⊤ b ^ m * (trF φ ε f z j' j).val := by
    intro v
    obtain ⟨j', hj'⟩ := exists_wchart φ hL v
    obtain ⟨_, ⟨V, hV, rfl⟩, hvV, hVj⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hj'
      (LB.wchart L φ j').isOpen
    have hm : f z ∈ V := hz _ (fun h0 => (h0.le hvV : v ∈ (⊥ : Y.Opens)))
    let b' : Γ(Y, V) := (Y.presheaf.map (homOfLE le_top).op).hom b
    have e : Y.basicOpen b' = V ⊓ Y.basicOpen b := Y.basicOpen_res _ _
    have hm' : f z ∈ Y.basicOpen b' := e.ge ⟨hm, hzb⟩
    have l : Y.basicOpen b' ≤ LB.wchart L φ j' ⊓ LB.wchart L φ j := e.le.trans (inf_le_inf hVj hb)
    obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen Y V hV b'
      ((Y.presheaf.map (homOfLE l).op).hom ((LB.LinComb L φ ε).g j' j).val)
    refine ⟨j', V, hVj, hvV, n, y, ?_⟩
    refine (gs_res f z (Y.basicOpen_le b') hm' y).symm.trans ((congrArg (gs f z _) hy).trans
      ((gs_mul f z _ hm' _ _).trans (congrArg₂ (· * ·) ?_ ?_)))
    · exact (gs_pow f z _ hm' _ _).trans (congrArg (· ^ n)
        ((gs_res f z (Y.basicOpen_le b') hm' b').trans (gs_res f z le_top hm b)))
    · exact (gs_res f z l hm' _).trans (gs_trans f z φ ε (hVj hm) (hb hzb))
  choose I V hV hvV m s hs using loc
  obtain ⟨T, hT⟩ := (isCompact_univ (X := Y)).elim_finite_subcover (fun v => (V v : Set Y)) (fun v => (V v).isOpen)
    (fun v _ => Set.mem_iUnion.2 ⟨v, hvV v⟩)
  obtain ⟨σ, hσ⟩ := exists_sec_of_locally f z φ ε hz
    (fun j' => gs f z ⊤ b ^ (T.sup m) * (trF φ ε f z j' j).val)
    (fun j₁ j₂ h₁ h₂ => by
      rw [← trF_trans hL φ ε f z h₁ h₂ (hb hzb), Units.val_mul, mul_left_comm])
    (fun v => by
      obtain ⟨w, hw, hvw⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ v))
      have hm : f z ∈ V w := hz _ (fun h0 => (h0.le (hvV w) : w ∈ (⊥ : Y.Opens)))
      refine ⟨I w, V w, hV w, hvw, (Y.presheaf.map (homOfLE le_top).op).hom b ^ (T.sup m - m w) * s w, ?_⟩
      rw [gs_mul f z _ hm, gs_pow f z _ hm, gs_res f z le_top hm, hs, ← _root_.mul_assoc, ← pow_add,
        Nat.sub_add_cancel (Finset.le_sup hw)])
  refine ⟨T.sup m, σ, (hσ j (hb hzb)).trans ?_⟩
  rw [mul_eq_left.1 (trF_trans hL φ ε f z (hb hzb) (hb hzb) (hb hzb)), Units.val_one, _root_.mul_one]

/- English proof (translation)
Set `Q : Ideal Γ(Y, ⊤)` to `{ carrier := {c | ∃ (N : Type) (_ : Fintype N) (a : N → Γ(Y, ⊤)) (s : N → LB.Sec (LB.LinComb L φ ε)), (∀ n, a n ∈ J) ∧ ∀ j, f z ∈ LB.wchart L φ j → gs f z ⊤ c * t j = ∑ n, gs f z ⊤ (a n) * gs f z (LB.wchart L φ j) ((s n).f j)} zero_mem' := ⟨PEmpty, inferInstance, PEmpty.elim, PEm …`. Rewrite using `[gs_eq f z ⊤ trivial, map_zero, map_zero, zero_mul, Fintype.sum_empty]⟩`. Use the proof step `add_mem' := by`. Introduce and unpack `c c' ⟨N, _, a, s, ha, e⟩ ⟨N', _, a', s', ha', e'⟩`. Apply the tactic sequence `refine ⟨N ⊕ N', inferInstance, Sum.elim a a', Sum.elim s s', fun n => by cases n <;> simp [ha, ha'], fun j hj => ?_⟩`.

Rewrite using `[gs_add f z ⊤ trivial, add_mul, e j hj, e' j hj, Fintype.sum_sum_type]`. Both sides reduce to the same expression. Use the proof step `smul_mem' := by`. Introduce and unpack `c c' ⟨N, _, a, s, ha, e⟩`. Use `⟨N, inferInstance, fun n => c * a n, s, fun n => J.mul_mem_left _ (ha n), fun j hj => ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_eq_mul, gs_mul f z ⊤ trivial, _root_.mul_assoc, e j hj, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun n _ => by rw [gs_mul f z ⊤ trivial, _root_.mul_assoc] }`. Establish `key : ∀ v : Y, ∃ c ∈ Q, v ∈ Y.basicOpen c`. Introduce `v`. Take `⟨j, hj⟩` from `exists_wchart φ hL v`.

Take `⟨b, hb, hvb⟩` from `(isAffineOpen_top Y).exists_basicOpen_le (V := LB.wchart L φ j) ⟨v, hj⟩ trivial`. Establish `hzb : f z ∈ Y.basicOpen b` using `hz _ (fun h0 => (h0.le hvb : v ∈ (⊥ : Y.Opens)))`. Take `⟨r, hr, er⟩` from `H j _ ((isAffineOpen_top Y).basicOpen b) hb hzb`. Use `(isAffineOpen_top Y).isLocalization_basicOpen b` as an intermediate fact. Take `⟨⟨⟨a, ha⟩, ⟨_, n, rfl⟩⟩, e2⟩` from `(IsLocalization.mem_map_algebraMap_iff (Submonoid.powers b) Γ(Y, Y.basicOpen b) (I := J) (z := r)).1 hr`.

Establish `e3` using `congrArg (gs f z (Y.basicOpen b)) e2`. Establish `e4 : ∀ c, gs f z (Y.basicOpen b) (algebraMap Γ(Y, ⊤) _ c) = gs f z ⊤ c` using `fun c => gs_res f z (Y.basicOpen_le b) hzb c`. Rewrite `e3` using `[gs_mul f z _ hzb, er, e4, e4, gs_pow f z ⊤ trivial]`. Take `⟨m, s, hs⟩` from `exists_sec_pow f z φ ε hz hL b j hb hzb`. Use `⟨b * b ^ (n + m), Q.mul_mem_left _ ⟨PUnit, inferInstance, fun _ => a, fun _ => s, fun _ => ha, fun j' hj' => ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Fintype.sum_unique, sec_trans s f z hj' (hb hzb), hs, ht j' j hj' (hb hzb), gs_pow f z ⊤ trivial, ← e3]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← pow_succ', Scheme.basicOpen_pow _ _ (Nat.succ_pos _)]`. Conclude with `hvb`. Establish `hQ : Ideal.span (Q : Set Γ(Y, ⊤)) = ⊤`.

Use `((isAffineOpen_top Y).self_le_iSup_basicOpen_iff).1 fun v _ => ?_` and prove the remaining obligations. Take `⟨c, hc, hvc⟩` from `key v`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨c, hc⟩, hvc⟩`. Rewrite `hQ` using `[Ideal.span_eq]`. Take `⟨N, _, a, s, ha, e⟩ : (1 : Γ(Y, ⊤)) ∈ Q` from `hQ ▸ Submodule.mem_top`.

Use `⟨Fintype.card N, fun n => a ((Fintype.equivFin N).symm n), fun n => s ((Fintype.equivFin N).symm n), fun n => ha _, fun j hj => ?_⟩` and prove the remaining obligations. Use `e j hj` as an intermediate fact. Rewrite `this` using `[gs_eq f z ⊤ trivial, map_one, map_one, _root_.one_mul]`. Rewrite using `[this]`. Conclude with `((Fintype.equivFin N).symm.sum_comp fun n => gs f z ⊤ (a n) * gs f z (LB.wchart L φ j) ((s n).f j)).symm`.
-/
theorem exists_comb_of_locally [IsAffine Y] [IsReduced Y] (hz : ∀ U : Y.Opens, U ≠ ⊥ → f z ∈ U) (hL : L.IsLB)
    (t : (K → L.ι) → Z.presheaf.stalk z)
    (ht : ∀ j j', f z ∈ LB.wchart L φ j → f z ∈ LB.wchart L φ j' → t j = (trF φ ε f z j j').val * t j')
    (J : Ideal Γ(Y, ⊤))
    (H : ∀ (j : K → L.ι) (V : Y.Opens), IsAffineOpen V → V ≤ LB.wchart L φ j → f z ∈ V →
      ∃ r ∈ J.map (Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom, gs f z V r = t j) :
    ∃ (m : ℕ) (a : Fin m → Γ(Y, ⊤)) (s : Fin m → LB.Sec (LB.LinComb L φ ε)), (∀ n, a n ∈ J) ∧
      ∀ j, f z ∈ LB.wchart L φ j → t j = ∑ n, gs f z ⊤ (a n) * gs f z (LB.wchart L φ j) ((s n).f j) := by
  let Q : Ideal Γ(Y, ⊤) :=
    { carrier := {c | ∃ (N : Type) (_ : Fintype N) (a : N → Γ(Y, ⊤)) (s : N → LB.Sec (LB.LinComb L φ ε)),
        (∀ n, a n ∈ J) ∧ ∀ j, f z ∈ LB.wchart L φ j →
          gs f z ⊤ c * t j = ∑ n, gs f z ⊤ (a n) * gs f z (LB.wchart L φ j) ((s n).f j)}
      zero_mem' := ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, fun n => n.elim, fun j _ => by
        rw [gs_eq f z ⊤ trivial, map_zero, map_zero, zero_mul, Fintype.sum_empty]⟩
      add_mem' := by
        rintro c c' ⟨N, _, a, s, ha, e⟩ ⟨N', _, a', s', ha', e'⟩
        refine ⟨N ⊕ N', inferInstance, Sum.elim a a', Sum.elim s s', fun n => by cases n <;> simp [ha, ha'],
          fun j hj => ?_⟩
        rw [gs_add f z ⊤ trivial, add_mul, e j hj, e' j hj, Fintype.sum_sum_type]
        rfl
      smul_mem' := by
        rintro c c' ⟨N, _, a, s, ha, e⟩
        refine ⟨N, inferInstance, fun n => c * a n, s, fun n => J.mul_mem_left _ (ha n), fun j hj => ?_⟩
        rw [smul_eq_mul, gs_mul f z ⊤ trivial, _root_.mul_assoc, e j hj, Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by rw [gs_mul f z ⊤ trivial, _root_.mul_assoc] }
  have key : ∀ v : Y, ∃ c ∈ Q, v ∈ Y.basicOpen c := by
    intro v
    obtain ⟨j, hj⟩ := exists_wchart φ hL v
    obtain ⟨b, hb, hvb⟩ := (isAffineOpen_top Y).exists_basicOpen_le (V := LB.wchart L φ j) ⟨v, hj⟩ trivial
    have hzb : f z ∈ Y.basicOpen b := hz _ (fun h0 => (h0.le hvb : v ∈ (⊥ : Y.Opens)))
    obtain ⟨r, hr, er⟩ := H j _ ((isAffineOpen_top Y).basicOpen b) hb hzb
    have := (isAffineOpen_top Y).isLocalization_basicOpen b
    obtain ⟨⟨⟨a, ha⟩, ⟨_, n, rfl⟩⟩, e2⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers b) Γ(Y, Y.basicOpen b) (I := J) (z := r)).1 hr
    have e3 := congrArg (gs f z (Y.basicOpen b)) e2
    have e4 : ∀ c, gs f z (Y.basicOpen b) (algebraMap Γ(Y, ⊤) _ c) = gs f z ⊤ c := fun c =>
      gs_res f z (Y.basicOpen_le b) hzb c
    rw [gs_mul f z _ hzb, er, e4, e4, gs_pow f z ⊤ trivial] at e3
    obtain ⟨m, s, hs⟩ := exists_sec_pow f z φ ε hz hL b j hb hzb
    refine ⟨b * b ^ (n + m), Q.mul_mem_left _ ⟨PUnit, inferInstance, fun _ => a, fun _ => s, fun _ => ha,
      fun j' hj' => ?_⟩, ?_⟩
    · rw [Fintype.sum_unique, sec_trans s f z hj' (hb hzb), hs, ht j' j hj' (hb hzb), gs_pow f z ⊤ trivial, ← e3]
      ring
    · rw [← pow_succ', Scheme.basicOpen_pow _ _ (Nat.succ_pos _)]
      exact hvb
  have hQ : Ideal.span (Q : Set Γ(Y, ⊤)) = ⊤ := by
    refine ((isAffineOpen_top Y).self_le_iSup_basicOpen_iff).1 fun v _ => ?_
    obtain ⟨c, hc, hvc⟩ := key v
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨c, hc⟩, hvc⟩
  rw [Ideal.span_eq] at hQ
  obtain ⟨N, _, a, s, ha, e⟩ : (1 : Γ(Y, ⊤)) ∈ Q := hQ ▸ Submodule.mem_top
  refine ⟨Fintype.card N, fun n => a ((Fintype.equivFin N).symm n), fun n => s ((Fintype.equivFin N).symm n),
    fun n => ha _, fun j hj => ?_⟩
  have := e j hj
  rw [gs_eq f z ⊤ trivial, map_one, map_one, _root_.one_mul] at this
  rw [this]
  exact ((Fintype.equivFin N).symm.sum_comp
    fun n => gs f z ⊤ (a n) * gs f z (LB.wchart L φ j) ((s n).f j)).symm

end Generic

variable {R : Type} [CommRing R] [IsDomain R]

def toRaw (D : DegPre R) : IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg R where
  P := D.P
  rig := D.rig
  rig_gen := D.rig_gen
  cube := D.cub
  sym := D.sym
  sym_gen := D.sym_gen
  sym_rig := D.sym_rig
  X := D.X
  c := D.c
  c_add := D.c_add
  ψ := D.psi
  ψ_gen := D.psi_gen

def ofRaw (D : IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg R) : DegPre R where
  P := D.P
  rig := D.rig
  rig_gen := D.rig_gen
  cub := D.cube
  sym := D.sym
  sym_gen := D.sym_gen
  sym_rig := D.sym_rig
  X := D.X
  c := D.c
  c_add := D.c_add
  psi := D.ψ
  psi_gen := D.ψ_gen

def rawEquiv (R : Type) [CommRing R] [IsDomain R] : DegPre R ≃ IndefiniteRowSideFullHecke.CompleteLocalNormalRings.RawDeg R where
  toFun := toRaw
  invFun := ofRaw
  left_inv _ := rfl
  right_inv _ := rfl

variable (D : DegPre R)

/- English proof (translation)
The claim follows from `D.tau a b`.
-/
example (a b : D.X) : LB.Gen (LB.LinComb D.P.L
    (Sum.elim (Sum.elim (Sum.elim (fun _ : PUnit => D.xK (a + b)) (fun _ : PUnit => D.xK a))
        (fun _ : PUnit => D.xK b)) (fun _ : PUnit => (toUnit (TK R)).left ≫ eSec D.P.A))
      (Sum.elim (Sum.elim (Sum.elim (fun _ => -1) (fun _ => - -1)) (fun _ => - -1)) (fun _ => -1))) := D.tau a b

section Values

variable {D} {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J : (Z ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
include hJ

/- English proof (translation)
The claim follows from `(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))`.
-/
theorem val_tau (a b : D.X) : val (D.tau a b) r z J =
    val (D.psi (a + b)) r z J * (val (D.psi a) r z J)⁻¹ * (val (D.psi b) r z J)⁻¹ * (val D.rigK r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

/- English proof (translation)
Rewrite using `[val_tau r hJ, val_tau r hJ, add_comm b a, mul_right_comm (val (D.psi (a + b)) _ z J)]`.
-/
theorem val_tau_symm (a b : D.X) : val (D.tau a b) r z J = val (D.tau b a) r z J := by
  rw [val_tau r hJ, val_tau r hJ, add_comm b a, mul_right_comm (val (D.psi (a + b)) _ z J)]

/- English proof (translation)
Establish `e0 : D.xK (a + b) = IndefiniteRowSideFullHecke.CompleteLocalNormalRings.laφ D.P.A ((toRaw D).cK a) ((toRaw D).cK b) 0` using `congrArg (fun q : TK R ⟶ D.P.A => q.left) ((toRaw D).cT_add (IndefiniteRowSideFullHecke.CompleteLocalNormalRings.genPt R) a b)`. Establish `hm` using `hJ.mem (IndefiniteRowSideFullHecke.CompleteLocalNormalRings.laφ D.P.A ((toRaw D).cK a) ((toRaw D).cK b)) r`. Establish `hq : ∀ {A A' : Type} [CommGroup A] [CommGroup A'] (φ : A →* A') (a b c d : A), φ (a * b⁻¹ * c⁻¹ * d⁻¹) = φ a * (φ b)⁻¹ * (φ c)⁻¹ * (φ d)⁻¹`. Introduce `A A' _ _ φ a b c d`. Simplify using `only [map_mul, map_inv]`.

Rewrite using `[val_tau r hJ]`. Use `(hq _ _ _ _ _).trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ (congrArg (·⁻¹) ?_)) (congrArg (·⁻¹) ?_)) (congrArg (·⁻¹) ?_))` and prove the remaining obligations. Conclude with `(gm_res r z _ hm _).trans (val_of (D.psi (a + b)) r z J _ (fun _ => congrArg (fun q => J (r ≫ q)) e0)).symm`. Conclude with `gm_res r z _ hm _`. Conclude with `gm_res r z _ hm _`.

Conclude with `gm_res r z _ hm _`.
-/
theorem val_τ (a b : D.X) : val ((toRaw D).τ a b) r z J = val (D.tau a b) r z J := by
  have e0 : D.xK (a + b) = IndefiniteRowSideFullHecke.CompleteLocalNormalRings.laφ D.P.A ((toRaw D).cK a) ((toRaw D).cK b) 0 :=
    congrArg (fun q : TK R ⟶ D.P.A => q.left) ((toRaw D).cT_add (IndefiniteRowSideFullHecke.CompleteLocalNormalRings.genPt R) a b)
  have hm := hJ.mem (IndefiniteRowSideFullHecke.CompleteLocalNormalRings.laφ D.P.A ((toRaw D).cK a) ((toRaw D).cK b)) r
  have hq : ∀ {A A' : Type} [CommGroup A] [CommGroup A'] (φ : A →* A') (a b c d : A),
      φ (a * b⁻¹ * c⁻¹ * d⁻¹) = φ a * (φ b)⁻¹ * (φ c)⁻¹ * (φ d)⁻¹ := by
    intro A A' _ _ φ a b c d
    simp only [map_mul, map_inv]
  rw [val_tau r hJ]
  refine (hq _ _ _ _ _).trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ (congrArg (·⁻¹) ?_))
    (congrArg (·⁻¹) ?_)) (congrArg (·⁻¹) ?_))
  · exact (gm_res r z _ hm _).trans (val_of (D.psi (a + b)) r z J _ (fun _ => congrArg (fun q => J (r ≫ q)) e0)).symm
  · exact gm_res r z _ hm _
  · exact gm_res r z _ hm _
  · exact gm_res r z _ hm _

end Values

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem psiEven_iff : D.PsiEven ↔ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ ((toRaw D).ψ (-χ))
      (LB.pullGen D.P.L (IndefiniteRowSideFullHecke.CompleteLocalNormalRings.symφ D.P.A) IndefiniteRowSideFullHecke.CompleteLocalNormalRings.symε (toRaw D).sym ((toRaw D).cK χ).left))
    ((toRaw D).ψ χ) := Iff.rfl

/- English proof (translation)
Use `forall₃_congr fun a a' b => ⟨fun H => corr_of_val D.P.isLB fun y J hJ => ?_, fun H => corr_of_val D.P.isLB fun y J hJ => ?_⟩` and prove the remaining obligations. Use `(val_mul hJ _ _ _).symm.trans ((val_corr hJ H (𝟙 _)).trans (val_mul hJ _ _ _))` as an intermediate fact. Conclude with `((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_τ (𝟙 _) hJ _ _) rfl)).trans (this.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_τ (𝟙 _) hJ _ _) (val_τ (𝟙 _) hJ _ _))).symm)`. Use `(val_mul hJ _ _ _).symm.trans ((val_corr hJ H (𝟙 _)).trans (val_mul hJ _ _ _))` as an intermediate fact. Conclude with `((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_τ (𝟙 _) hJ _ _).symm rfl)).trans (this.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_τ (𝟙 _) hJ _ _).symm (val_τ (𝟙 _) hJ _ _).symm)).symm)`.
-/
theorem tauBimult_iff_left : D.TauBimult ↔ ∀ χ₁ χ₂ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ ((toRaw D).τ (χ₁ + χ₂) χ)
      (IndefiniteRowSideFullHecke.CompleteLocalNormalRings.cubeAt D.P.A (toRaw D).cube ((toRaw D).cK χ₁) ((toRaw D).cK χ₂) ((toRaw D).cK χ)))
    (LB.mulGen D.P.L _ _ _ _ ((toRaw D).τ χ₁ χ) ((toRaw D).τ χ₂ χ)) := by
  refine forall₃_congr fun a a' b => ⟨fun H => corr_of_val D.P.isLB fun y J hJ => ?_,
    fun H => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  · have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ H (𝟙 _)).trans (val_mul hJ _ _ _))
    exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_τ (𝟙 _) hJ _ _) rfl)).trans (this.trans
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_τ (𝟙 _) hJ _ _) (val_τ (𝟙 _) hJ _ _))).symm)
  · have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ H (𝟙 _)).trans (val_mul hJ _ _ _))
    exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_τ (𝟙 _) hJ _ _).symm rfl)).trans (this.trans
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_τ (𝟙 _) hJ _ _).symm (val_τ (𝟙 _) hJ _ _).symm)).symm)

/- English proof (translation)
Establish `cub : ∀ (a a' b : D.X) (y : (TK R).left) (J), Good D.P.L y J → val (IndefiniteRowSideFullHecke.CompleteLocalNormalRings.cubeAt D.P.A (toRaw D).cube ((toRaw D).cK b) ((toRaw D).cK a) ((toRaw D).cK a')) (𝟙 _) y J = val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a …` using `fun a a' b y J hJ => by`. Establish `C : IsCub (cubV D.cub (T` using `TK R) y J) := isCub_cubV D.cub hJ`. Conclude with `(val_cub D.cub (𝟙 (TK R)) hJ _ _ _).trans (((C.s01 _ _ _).trans (C.s12 _ _ _)).trans (val_cub D.cub (𝟙 (TK R)) hJ _ _ _).symm)`. Establish `sw : ∀ (a b : D.X) (y : (TK R).left) (J), Good D.P.L y J → val ((toRaw D).τ b a) (𝟙 _) y J = val (D.tau a b) (𝟙 _) y J` using `fun a b y J hJ => (val_τ (𝟙 _) hJ _ _).trans (val_tau_symm (𝟙 _) hJ _ _)`. Use `⟨fun H b a a' => corr_of_val D.P.isLB fun y J hJ => ?_, fun H a a' b => corr_of_val D.P.isLB fun y J hJ => ?_⟩` and prove the remaining obligations.

Use `(val_mul hJ _ _ _).symm.trans ((val_corr hJ (H a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))` as an intermediate fact. Conclude with `((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (sw _ _ y J hJ) (cub a a' b y J hJ))).trans (this.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (sw _ _ y J hJ) (sw _ _ y J hJ))).symm)`. Use `(val_mul hJ _ _ _).symm.trans ((val_corr hJ (H b a a') (𝟙 _)).trans (val_mul hJ _ _ _))` as an intermediate fact. Conclude with `((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (sw _ _ y J hJ).symm (cub a a' b y J hJ).symm)).trans (this.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (sw _ _ y J hJ).symm (sw _ _ y J hJ).symm)).symm)`.
-/
theorem tauBimult_iff_right : D.TauBimult ↔ ∀ χ χ₁ χ₂, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ ((toRaw D).τ χ (χ₁ + χ₂))
      (IndefiniteRowSideFullHecke.CompleteLocalNormalRings.cubeAt D.P.A (toRaw D).cube ((toRaw D).cK χ) ((toRaw D).cK χ₁) ((toRaw D).cK χ₂)))
    (LB.mulGen D.P.L _ _ _ _ ((toRaw D).τ χ χ₁) ((toRaw D).τ χ χ₂)) := by
  have cub : ∀ (a a' b : D.X) (y : (TK R).left) (J), Good D.P.L y J →
      val (IndefiniteRowSideFullHecke.CompleteLocalNormalRings.cubeAt D.P.A (toRaw D).cube ((toRaw D).cK b) ((toRaw D).cK a) ((toRaw D).cK a')) (𝟙 _) y J =
      val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) y J := fun a a' b y J hJ => by
    have C : IsCub (cubV D.cub (T := TK R) y J) := isCub_cubV D.cub hJ
    exact (val_cub D.cub (𝟙 (TK R)) hJ _ _ _).trans (((C.s01 _ _ _).trans (C.s12 _ _ _)).trans
      (val_cub D.cub (𝟙 (TK R)) hJ _ _ _).symm)
  have sw : ∀ (a b : D.X) (y : (TK R).left) (J), Good D.P.L y J →
      val ((toRaw D).τ b a) (𝟙 _) y J = val (D.tau a b) (𝟙 _) y J := fun a b y J hJ =>
    (val_τ (𝟙 _) hJ _ _).trans (val_tau_symm (𝟙 _) hJ _ _)
  refine ⟨fun H b a a' => corr_of_val D.P.isLB fun y J hJ => ?_,
    fun H a a' b => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  · have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (H a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
    exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (sw _ _ y J hJ) (cub a a' b y J hJ))).trans (this.trans
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (sw _ _ y J hJ) (sw _ _ y J hJ))).symm)
  · have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (H b a a') (𝟙 _)).trans (val_mul hJ _ _ _))
    exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (sw _ _ y J hJ).symm (cub a a' b y J hJ).symm)).trans
      (this.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (sw _ _ y J hJ).symm (sw _ _ y J hJ).symm)).symm)

/- English proof (translation)
Simplify using `only [gs_eq f z U h, map_sum]`.
-/
theorem gs_sum {Y Z : Scheme.{0}} (f : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : f z ∈ U) {N : Type} [Fintype N]
    (a : N → Γ(Y, U)) : gs f z U (∑ n, a n) = ∑ n, gs f z U (a n) := by
  simp only [gs_eq f z U h, map_sum]

/- English proof (translation)
The claim follows from `(gs_res (𝟙 Z) z e h ((f.app U).hom a)).trans (gs_pull (𝟙 Z) f z U (e h) a)`.
-/
theorem gs_appLE {Y Z : Scheme.{0}} (f : Z ⟶ Y) (z : Z) {U : Y.Opens} {V : Z.Opens} (e : V ≤ f ⁻¹ᵁ U) (h : z ∈ V)
    (a : Γ(Y, U)) : gs (𝟙 Z) z V ((f.appLE U V e).hom a) = gs f z U a :=
  (gs_res (𝟙 Z) z e h ((f.app U).hom a)).trans (gs_pull (𝟙 Z) f z U (e h) a)

/- English proof (translation)
Establish `hss : Subsingleton (Spec (CommRingCat.of (FractionRing R)))` using `inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Take `⟨z⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R)))` from `inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))`. Establish `hw : ∀ j : PUnit → D.P.L.ι, jK R z ∈ LB.wchart D.P.L (fun _ : PUnit => (D.c χ).left) j → z ∈ LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j` using `fun j hj => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hj k`.

Take `⟨m, a, s, ha, e⟩` from `exists_comb_of_locally (Y := Spec (CommRingCat.of R)) (jK R) z (fun _ : PUnit => (D.c χ).left) (fun _ => -1) (jK_mem z) D.P.isLB (fun j => (gm (𝟙 _) z (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) ((D.psi χ).s j)).val) (fun j j' hj hj' => congrArg Units.val (gen_trans (D.psi_gen …`. Take `⟨r, hr, er⟩` from `gs_of_psiIn D χ J H (j PUnit.unit) V hV (hle.trans (LB.wchart_le D.P.L (fun _ : PUnit => (D.c χ).left) j PUnit.unit)) z hz`. Use `⟨r, ?_, er⟩` and prove the remaining obligations. Rewrite using `[Ideal.map_map]`. Use `hr using 2` and compare the differences between its conclusion and the goal.

Use extensionality with `a`. Conclude with `res_toOpen le_top a)`. Establish `hsurj : Function.Surjective (DegPre.toOpen (R` using `R) ⊤) := by`. Introduce `x`. Use `⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x, ?_⟩` and prove the remaining obligations.

Simplify using `[DegPre.toOpen]`. Use `choose a' ha' ea' using fun n => (Ideal.mem_map_iff_of_surjective _ hsurj).1 (ha n)`. Use `⟨m, a', s, ha', fun j => fn_ext fun y hy => ?_⟩` and prove the remaining obligations. Take `rfl : y = z` from `Subsingleton.elim (α := Spec (CommRingCat.of (FractionRing R))) y z`. Establish `hj : jK R y ∈ LB.wchart D.P.L (fun _ : PUnit => (D.c χ).left) j` using `Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k`.

Use `((gs_unit _ _ _ hy _).trans (e j hj)).trans (Eq.trans ?_ (gs_appLE (jK R) y _ hy _).symm)` and prove the remaining obligations. Use `Eq.trans (Finset.sum_congr rfl fun n _ => ?_) (gs_sum (jK R) y _ hj _).symm` and prove the remaining obligations. Use `Eq.trans (congrArg₂ (· * ·) ?_ rfl) (gs_mul (jK R) y _ hj _ _).symm` and prove the remaining obligations. Rewrite using `[← ea' n]`. Conclude with `(gs_res (jK R) y le_top hj _).symm.trans (congrArg (gs (jK R) y _) (res_toOpen le_top (a' n)))`.

Introduce and unpack `⟨m, a, s, ha, e⟩`. Use `psiIn_of_gs D χ J fun q V _ hle z hz => ?_` and prove the remaining obligations. Establish `l : V ≤ LB.wchart D.P.L (fun _ : PUnit => (D.c χ).left) (fun _ => q)` using `fun y hy => Set.mem_iInter.2 fun _ => hle hy`. Establish `hy : z ∈ LB.wchart D.P.L (fun _ : PUnit => D.xK χ) (fun _ => q)` using `Set.mem_iInter.2 fun _ => hle hz`. Use `⟨∑ n, DegPre.toOpen V (a n) * ((Spec (CommRingCat.of R)).presheaf.map (homOfLE l).op).hom ((s n).f (fun _ => q)), Ideal.sum_mem _ fun n _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (ha n)), ?_⟩` and prove the remaining obligations.

Use `Eq.trans ?_ (((gs_unit _ _ _ hy _).symm.trans (congrArg (gs (𝟙 _) z _) (e fun _ => q))).trans (gs_appLE (jK R) z _ hy _)).symm` and prove the remaining obligations. Use `Eq.trans (congrArg (gs (jK R) z V) ?_) (gs_res (jK R) z l hz _)` and prove the remaining obligations. Use `Eq.trans (Finset.sum_congr rfl fun n _ => ?_) (map_sum _ _ _).symm` and prove the remaining obligations. Conclude with `(congrArg₂ (· * ·) (res_toOpen l (a n)).symm rfl).trans (map_mul _ _ _).symm`.
-/
theorem psiIn_iff (χ : D.X) (J : Ideal R) : D.PsiIn χ J ↔ (toRaw D).ψMem J χ := by
  have hss : Subsingleton (Spec (CommRingCat.of (FractionRing R))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  constructor
  · intro H
    obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) :=
      inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
    have hw : ∀ j : PUnit → D.P.L.ι, jK R z ∈ LB.wchart D.P.L (fun _ : PUnit => (D.c χ).left) j →
        z ∈ LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j := fun j hj =>
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hj k
    obtain ⟨m, a, s, ha, e⟩ := exists_comb_of_locally (Y := Spec (CommRingCat.of R)) (jK R) z
      (fun _ : PUnit => (D.c χ).left) (fun _ => -1) (jK_mem z) D.P.isLB
      (fun j => (gm (𝟙 _) z (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) ((D.psi χ).s j)).val)
      (fun j j' hj hj' => congrArg Units.val (gen_trans (D.psi_gen χ) (𝟙 _) z (hw j hj) (hw j' hj')))
      (J.map (DegPre.toOpen ⊤)) (fun j V hV hle hz => by
        obtain ⟨r, hr, er⟩ := gs_of_psiIn D χ J H (j PUnit.unit) V hV
          (hle.trans (LB.wchart_le D.P.L (fun _ : PUnit => (D.c χ).left) j PUnit.unit)) z hz
        refine ⟨r, ?_, er⟩
        rw [Ideal.map_map]
        convert hr using 2
        ext a
        exact res_toOpen le_top a)
    have hsurj : Function.Surjective (DegPre.toOpen (R := R) ⊤) := by
      intro x
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x, ?_⟩
      simp [DegPre.toOpen]
    choose a' ha' ea' using fun n => (Ideal.mem_map_iff_of_surjective _ hsurj).1 (ha n)
    refine ⟨m, a', s, ha', fun j => fn_ext fun y hy => ?_⟩
    obtain rfl : y = z := Subsingleton.elim (α := Spec (CommRingCat.of (FractionRing R))) y z
    have hj : jK R y ∈ LB.wchart D.P.L (fun _ : PUnit => (D.c χ).left) j :=
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
    refine ((gs_unit _ _ _ hy _).trans (e j hj)).trans (Eq.trans ?_ (gs_appLE (jK R) y _ hy _).symm)
    refine Eq.trans (Finset.sum_congr rfl fun n _ => ?_) (gs_sum (jK R) y _ hj _).symm
    refine Eq.trans (congrArg₂ (· * ·) ?_ rfl) (gs_mul (jK R) y _ hj _ _).symm
    rw [← ea' n]
    exact (gs_res (jK R) y le_top hj _).symm.trans (congrArg (gs (jK R) y _) (res_toOpen le_top (a' n)))
  · rintro ⟨m, a, s, ha, e⟩
    refine psiIn_of_gs D χ J fun q V _ hle z hz => ?_
    have l : V ≤ LB.wchart D.P.L (fun _ : PUnit => (D.c χ).left) (fun _ => q) := fun y hy =>
      Set.mem_iInter.2 fun _ => hle hy
    have hy : z ∈ LB.wchart D.P.L (fun _ : PUnit => D.xK χ) (fun _ => q) := Set.mem_iInter.2 fun _ => hle hz
    refine ⟨∑ n, DegPre.toOpen V (a n) *
      ((Spec (CommRingCat.of R)).presheaf.map (homOfLE l).op).hom ((s n).f (fun _ => q)),
      Ideal.sum_mem _ fun n _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (ha n)), ?_⟩
    refine Eq.trans ?_ (((gs_unit _ _ _ hy _).symm.trans (congrArg (gs (𝟙 _) z _) (e fun _ => q))).trans
      (gs_appLE (jK R) z _ hy _)).symm
    refine Eq.trans (congrArg (gs (jK R) z V) ?_) (gs_res (jK R) z l hz _)
    refine Eq.trans (Finset.sum_congr rfl fun n _ => ?_) (map_sum _ _ _).symm
    exact (congrArg₂ (· * ·) (res_toOpen l (a n)).symm rfl).trans (map_mul _ _ _).symm

/- English proof (translation)
Establish `e : ∀ n : ℕ, {χ : D.X | ¬ D.PsiIn χ (I ^ n)} = {χ | ¬ (toRaw D).ψMem (I ^ n) χ}` using `fun n => Set.ext fun χ => not_congr (psiIn_iff D χ _)`. Conclude with `⟨fun ⟨a, b, c, d⟩ => ⟨(psiEven_iff D).1 a, (tauBimult_iff_left D).1 b, (tauBimult_iff_right D).1 b, fun χ h => (psiIn_iff D χ I).1 (c χ h), fun n => e n ▸ d n⟩, fun h => ⟨(psiEven_iff D).2 h.even, (tauBimult_iff_left D).2 h.mul_left, fun χ k => (psiIn_iff D χ I).2 (h.mem χ k), fu …`.
-/
theorem isDeg_iff (I : Ideal R) : (D.PsiEven ∧ D.TauBimult ∧ (∀ χ : D.X, χ ≠ 0 → D.PsiIn χ I) ∧
    ∀ n : ℕ, {χ : D.X | ¬ D.PsiIn χ (I ^ n)}.Finite) ↔ (toRaw D).IsDeg I := by
  have e : ∀ n : ℕ, {χ : D.X | ¬ D.PsiIn χ (I ^ n)} = {χ | ¬ (toRaw D).ψMem (I ^ n) χ} := fun n =>
    Set.ext fun χ => not_congr (psiIn_iff D χ _)
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨(psiEven_iff D).1 a, (tauBimult_iff_left D).1 b, (tauBimult_iff_right D).1 b,
      fun χ h => (psiIn_iff D χ I).1 (c χ h), fun n => e n ▸ d n⟩,
    fun h => ⟨(psiEven_iff D).2 h.even, (tauBimult_iff_left D).2 h.mul_left,
      fun χ k => (psiIn_iff D χ I).2 (h.mem χ k), fun n => (e n).symm ▸ h.tendsto n⟩⟩

def degDataEquiv (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) : DegData R I ≃ IndefiniteRowSideFullHecke.CompleteLocalNormalRings.DegData R I where
  toFun D := ⟨toRaw D.toPre, (isDeg_iff D.toPre I).1 ⟨D.psi_even, D.tau_bimult, D.psi_pos, D.psi_tendsto⟩⟩
  invFun D :=
    have h := (isDeg_iff (ofRaw D.toRawDeg) I).2 D.isDeg
    ⟨ofRaw D.toRawDeg, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end GlobalTheory.DegCompare
