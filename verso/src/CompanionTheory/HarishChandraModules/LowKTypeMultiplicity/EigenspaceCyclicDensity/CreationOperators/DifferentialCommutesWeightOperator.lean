import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport

open Finset

noncomputable section

namespace CompanionTheory.D.LK

open Car Formalism.REAL
open CompanionTheory.D.DSIC (KRel)

variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def al (i : Pos n) (c : Fin n) : ℝ := (if i.1.1 = c then 1 else 0) - (if i.1.2 = c then 1 else 0)

/- English proof (translation)
Simplify using `only [wt, al, filter_insert]`. Establish `h1 : ∀ p : Pos n → Prop, ∀ [DecidablePred p], i ∉ A.filter p` using `fun p _ hh => h (mem_filter.1 hh).1`. Apply the tactic sequence `split_ifs <;> (try simp only [card_insert_of_notMem (h1 _)]) <;> push_cast <;> ring`.
-/
theorem wt_insert {i : Pos n} {A : Finset (Pos n)} (h : i ∉ A) (c : Fin n) : wt (insert i A) c = wt A c + al i c := by
  simp only [wt, al, filter_insert]
  have h1 : ∀ p : Pos n → Prop, ∀ [DecidablePred p], i ∉ A.filter p := fun p _ hh => h (mem_filter.1 hh).1
  split_ifs <;> (try simp only [card_insert_of_notMem (h1 _)]) <;> push_cast <;> ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Ft_apply (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (c : Fin n) (x : Cn n V)
    (A : Finset (Pos n)) : Ft ε E c x A = E c c (x A) + (wt (A.filter (cpt ε)) c : ℂ) • x A := rfl

/- English proof (translation)
Use function extensionality and compare the values at `A`. Simplify using `only [Ft_apply, ann_apply, Pi.sub_apply, Pi.smul_apply]`. Distinguish the cases in `h : i ∈ A`. Simplify using `[h]`. Rewrite using `[if_neg h, if_neg h, filter_insert, if_pos hi, wt_insert (fun hh => h (mem_filter.1 hh).1), map_smul]`.

Use `push_cast`. Use `module`.
-/
theorem Ft_ann {ε : Fin n → Bool} (E : Fin n → Fin n → Module.End ℂ V) (c : Fin n) {i : Pos n} (hi : cpt ε i)
    (x : Cn n V) : Ft ε E c (ann i x) = ann i (Ft ε E c x) - (al i c : ℂ) • ann i x := by
  funext A
  simp only [Ft_apply, ann_apply, Pi.sub_apply, Pi.smul_apply]
  by_cases h : i ∈ A
  · simp [h]
  · rw [if_neg h, if_neg h, filter_insert, if_pos hi, wt_insert (fun hh => h (mem_filter.1 hh).1), map_smul]
    push_cast
    module

/- English proof (translation)
Use function extensionality and compare the values at `A`. Simplify using `only [Ft_apply, cre_apply, Pi.add_apply, Pi.smul_apply]`. Distinguish the cases in `h : i ∈ A`. Establish `e : A.filter (cpt ε) = insert i ((A.erase i).filter (cpt ε))` using `by conv_lhs => rw [← insert_erase h, filter_insert, if_pos hi]`. Rewrite using `[if_pos h, if_pos h, e, wt_insert (fun hh => notMem_erase i A (mem_filter.1 hh).1), map_smul]`.

Use `push_cast`. Use `module`. Simplify using `[h]`.
-/
theorem Ft_cre {ε : Fin n → Bool} (E : Fin n → Fin n → Module.End ℂ V) (c : Fin n) {i : Pos n} (hi : cpt ε i)
    (x : Cn n V) : Ft ε E c (cre i x) = cre i (Ft ε E c x) + (al i c : ℂ) • cre i x := by
  funext A
  simp only [Ft_apply, cre_apply, Pi.add_apply, Pi.smul_apply]
  by_cases h : i ∈ A
  · have e : A.filter (cpt ε) = insert i ((A.erase i).filter (cpt ε)) := by
      conv_lhs => rw [← insert_erase h, filter_insert, if_pos hi]
    rw [if_pos h, if_pos h, e, wt_insert (fun hh => notMem_erase i A (mem_filter.1 hh).1), map_smul]
    push_cast
    module
  · simp [h]

/- English proof (translation)
Introduce `n ε₀ ε V _ _ E h0 hE c`. Use `Commute.add_right (Commute.sum_right _ _ _ fun i _ => ?_) (Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => Commute.sum_right _ _ _ fun k _ => ?_)` and prove the remaining obligations. Use `split_ifs with hi`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Establish `e : ∀ y : Cn n V, Ft ε₀ E c (lift n (E i.1.1 i.1.2) y) = lift n (E i.1.1 i.1.2) (Ft ε₀ E c y) + (al i c : ℂ) • lift n (E i.1.1 i.1.2) y`.

Introduce `y`. Use function extensionality and compare the values at `A`. Use `congrArg (fun T : Module.End ℂ V => T (y A)) (hE c c i.1.1 i.1.2 rfl hi)` as an intermediate fact. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at this`. Simplify using `only [Ft_apply, lift_apply, Pi.add_apply, Pi.smul_apply, map_add, map_smul, sub_eq_iff_eq_add.1 this, al]`.

Establish `hne` using `i.2.ne`. Distinguish the cases in `h1 : c = i.1.1`. Substitute `h1` using the available equality. Simplify using `[hne.symm]`. Use `module`.

Distinguish the cases in `h2 : i.1.2 = c`. Substitute `h2` using the available equality. Simplify using `[hne, hne.symm]`. Use `module`. Simplify using `[h1, h2, Ne.symm h1]`.

Simplify using `only [Module.End.mul_apply]`. Rewrite using `[e, Ft_ann E c (h0 _ _ hi), map_sub, map_smul, sub_add_cancel]`. Conclude with `Commute.zero_right _`. Use `split_ifs with ht`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Establish `hk` using `Tri.cptk (ε := ε) ht`. Simplify using `only [Module.End.mul_apply]`. Rewrite using `[Ft_cre E c (h0 _ _ hk), Ft_ann E c (h0 _ _ ht.2.1), Ft_ann E c (h0 _ _ ht.1)]`. Establish `: (al k c : ℂ) = al i c + al j c`. Rewrite using `[← Complex.ofReal_add]`.

Simplify using `only [al, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_sub, map_smul, this]`. Use `module`.

Conclude with `Commute.zero_right _`.
-/
theorem differential_commutes_weight_operator : ∀ (n : ℕ) (ε₀ ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), (∀ a b, ε a = ε b → ε₀ a = ε₀ b) → KRel ε E →
    ∀ c, Commute (Ft ε₀ E c) (bd ε E) := by
  intro n ε₀ ε V _ _ E h0 hE c
  refine Commute.add_right (Commute.sum_right _ _ _ fun i _ => ?_) (Commute.sum_right _ _ _ fun i _ =>
    Commute.sum_right _ _ _ fun j _ => Commute.sum_right _ _ _ fun k _ => ?_)
  · split_ifs with hi
    · refine LinearMap.ext fun x => ?_
      have e : ∀ y : Cn n V, Ft ε₀ E c (lift n (E i.1.1 i.1.2) y) =
          lift n (E i.1.1 i.1.2) (Ft ε₀ E c y) + (al i c : ℂ) • lift n (E i.1.1 i.1.2) y := by
        intro y
        funext A
        have := congrArg (fun T : Module.End ℂ V => T (y A)) (hE c c i.1.1 i.1.2 rfl hi)
        simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
        simp only [Ft_apply, lift_apply, Pi.add_apply, Pi.smul_apply, map_add, map_smul, sub_eq_iff_eq_add.1 this, al]
        have hne := i.2.ne
        by_cases h1 : c = i.1.1
        · subst h1; simp [hne.symm]; module
        · by_cases h2 : i.1.2 = c
          · subst h2; simp [hne, hne.symm]; module
          · simp [h1, h2, Ne.symm h1]
      simp only [Module.End.mul_apply]
      rw [e, Ft_ann E c (h0 _ _ hi), map_sub, map_smul, sub_add_cancel]
    · exact Commute.zero_right _
  · split_ifs with ht
    · refine LinearMap.ext fun x => ?_
      have hk := Tri.cptk (ε := ε) ht
      simp only [Module.End.mul_apply]
      rw [Ft_cre E c (h0 _ _ hk), Ft_ann E c (h0 _ _ ht.2.1), Ft_ann E c (h0 _ _ ht.1)]
      have : (al k c : ℂ) = al i c + al j c := by
        rw [← Complex.ofReal_add]; simp only [al, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2]; congr 1; ring
      simp only [map_sub, map_smul, this]
      module
    · exact Commute.zero_right _

/- English proof (translation)
Proceed by induction on `a using FreeAlgebra.induction with`. Consider the case `grade0 r => intro x`. Simplify using `[Module.algebraMap_end_apply]`. Consider the case `grade1 c => intro x`. Simplify using `[h]`.

Consider the case `mul a b ha hb => intro x`. Simplify using `only [map_mul, Module.End.mul_apply, ha, hb]`. Consider the case `add a b ha hb => intro x`. Simplify using `only [map_add, LinearMap.add_apply, ha, hb]`.
-/
theorem free_inter {ι : Type} (φ : V →ₗ[ℂ] W) (S : ι → Module.End ℂ V) (T : ι → Module.End ℂ W)
    (h : ∀ i x, φ (S i x) = T i (φ x)) (a : FreeAlgebra ℂ ι) :
    ∀ x, φ (FreeAlgebra.lift ℂ S a x) = FreeAlgebra.lift ℂ T a (φ x) := by
  induction a using FreeAlgebra.induction with
  | grade0 r => intro x; simp [Module.algebraMap_end_apply]
  | grade1 c => intro x; simp [h]
  | mul a b ha hb => intro x; simp only [map_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb => intro x; simp only [map_add, LinearMap.add_apply, ha, hb]

/- English proof (translation)
The claim follows from `free_inter φ _ _ (fun p x => by split_ifs <;> simp [h]) a x`.
-/
theorem evK_inter {ε : Fin n → Bool} (φ : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b x, φ (E a b x) = F a b (φ x)) (a : FreeAlgebra ℂ (Fin n × Fin n))
    (x : V) : φ (evK ε E a x) = evK ε F a (φ x) :=
  free_inter φ _ _ (fun p x => by split_ifs <;> simp [h]) a x

/- English proof (translation)
The claim follows from `free_inter (LinearMap.proj (R := ℂ) (φ := fun _ => V) A) _ _ (fun _ _ => rfl) b x`.
-/
theorem evd_Ft_apply (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (b : FreeAlgebra ℂ (Fin n))
    (x : Cn n V) (A : Finset (Pos n)) :
    evd (Ft ε E) b x A = evd (fun c => E c c + (wt (A.filter (cpt ε)) c : ℂ) • 1) b (x A) :=
  free_inter (LinearMap.proj (R := ℂ) (φ := fun _ => V) A) _ _ (fun _ _ => rfl) b x

/- English proof (translation)
The claim follows from `free_inter (lift n φ) _ _ (fun c y => by funext A; simp [Ft_apply, h]) b x`.
-/
theorem lift_evd {ε : Fin n → Bool} (φ : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b x, φ (E a b x) = F a b (φ x)) (b : FreeAlgebra ℂ (Fin n))
    (x : Cn n V) : lift n φ (evd (Ft ε E) b x) = evd (Ft ε F) b (lift n φ x) :=
  free_inter (lift n φ) _ _ (fun c y => by funext A; simp [Ft_apply, h]) b x

/- English proof (translation)
Introduce `A hA` and use `hx A fun h0 => hA (h A h0)`.
-/
theorem sup_of_supp {ε : Fin n → Bool} {B : Finset (Pos n)} {j : ℕ} {x : Cn n V} {y : Cn n W} (hx : Sup ε B j x)
    (h : ∀ A, x A = 0 → y A = 0) : Sup ε B j y := fun A hA => hx A fun h0 => hA (h A h0)

/- English proof (translation)
Introduce `A hA` and use `by by_cases h : x A = 0 · exact hy A fun h' => hA (by simp [h, h']) · exact hx A h`.
-/
theorem Sup.sub {ε : Fin n → Bool} {B : Finset (Pos n)} {j : ℕ} {x y : Cn n V} (hx : Sup ε B j x) (hy : Sup ε B j y) :
    Sup ε B j (x - y) := fun A hA => by
  by_cases h : x A = 0
  · exact hy A fun h' => hA (by simp [h, h'])
  · exact hx A h

/- English proof (translation)
Introduce `n ε₀ ε a b h0 hab V _ _ E hE B j`. Proceed by induction on `j generalizing V with`. Consider the case `zero`. Introduce `x hx _ _`. Take `⟨w, hw⟩` from `(hab V E hE).2 (x B)`.

Establish `hxB : ∀ A, A ≠ B → x A = 0` using `fun A hA => by`. Assume the negation of the conclusion as `h`. Take `⟨e1, e2⟩` from `hx A h`. Use `hA (e1 ▸ (filter_true_of_mem fun i hi hc => ?_).symm)` and prove the remaining obligations. Conclude with `notMem_empty i (card_eq_zero.1 e2 ▸ mem_filter.2 ⟨hi, hc⟩)`.

Distinguish the cases in `hB : x B = 0`. Establish `: x = 0` using `funext fun A => by`. Distinguish the cases in `h : A = B`. Rewrite using `[h, hB]`. Both sides reduce to the same expression.

Conclude with `hxB A h`. Substitute `this` using the available equality. Conclude with `⟨0, fun A hA => absurd rfl hA, by simp⟩`. Establish `hBn : ∀ i ∈ B, ¬cpt ε₀ i` using `fun i hi => (mem_filter.1 ((hx B hB).1.symm ▸ hi :)).2`. Establish `hBc : B.filter (cpt ε₀) = ∅` using `filter_false_of_mem hBn`.

Set `w' : Cn n V` to `fun A => ∑ i : Pos n, if cpt ε₀ i ∧ A = insert i B then sg i B • w i else 0`. Establish `hw' : Sup ε₀ B (0 + 1) w'`. Introduce `A hA`. Take `⟨i, -, hi⟩` from `exists_ne_zero_of_sum_ne_zero hA`. Take `⟨h1, rfl⟩ : cpt ε₀ i ∧ A = insert i B` from `by by_contra h; exact hi (if_neg h)`.

Rewrite using `[filter_insert, if_neg (not_not.2 h1), filter_true_of_mem hBn, filter_insert, if_pos h1, hBc]`. Simplify using the standard rewrite rules. Use `⟨w', hw', funext fun A => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hA : A = B`. Substitute `hA` using the available equality.

Rewrite using `[Pi.sub_apply, lift_apply, evd_Ft_apply, hBc]`. Establish `e : (fun c => E c c + (wt (∅ : Finset (Pos n)) c : ℂ) • (1 : Module.End ℂ V)) = fun c => E c c`. Use function extensionality and compare the values at `c`. Simplify using `[wt]`. Rewrite using `[e, hw, bd_apply, Finset.sum_eq_zero (s := univ) (f := fun i => ∑ j : Pos n, ∑ k : Pos n, if Tri ε₀ i j k then cre k (ann j (ann i w')) A else 0), add_zero]`.

Use `Finset.sum_congr rfl fun i _ => ?_ split_ifs with hi` and prove the remaining obligations. Establish `hiA : i ∉ A` using `fun h => hBn i h hi`. Rewrite using `[ann_apply, if_neg hiA]`. Use `congr 1`. Simplify using `only [w']`.

Rewrite using `[Finset.sum_eq_single i, if_pos ⟨hi, rfl⟩, smul_smul, sg_mul_self, one_smul]`. Introduce `k _ hk`. Use `if_neg fun h => ?_` and prove the remaining obligations. Break down `mem_insert.1 (h.2 ▸ mem_insert_self i A) with h' | h'` into its components or cases. Conclude with `hk h'.symm`.

Conclude with `hiA h'`. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Use `fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_ split_ifs with ht` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Conclude with `hBn k (tri_ne h).1 ht.cptk`. Both sides reduce to the same expression. Rewrite using `[Pi.sub_apply, lift_apply, evd_Ft_apply, hxB A hA, map_zero, map_zero, sub_zero]`. Assume the negation of the conclusion as `h`. Take `⟨e1, e2⟩` from `sup_bd E hw' (Ne.symm h)`.

Use `hA (e1 ▸ (filter_true_of_mem fun i hi hc => ?_).symm)` and prove the remaining obligations. Conclude with `notMem_empty i (card_eq_zero.1 (by omega : (A.filter (cpt ε₀)).card = 0) ▸ mem_filter.2 ⟨hi, hc⟩)`. Consider the case `succ j ih`. Introduce `x hx hr hbx`. Take `⟨Y, _, _, EY, π, hY, hs, hπ, hac⟩` from `hC n ε₀ V E hE`.

Establish `hK : ∀ a b, ∀ y ∈ LinearMap.ker π, EY a b y ∈ LinearMap.ker π`. Introduce `a b y hy`. Rewrite `hy`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[hπ, hy, map_zero]`. Set `EK : Fin n → Fin n → Module.End ℂ (LinearMap.ker π)` to `fun a b => (EY a b).restrict (hK a b)`.

Establish `hι : ∀ a b y, (LinearMap.ker π).subtype (EK a b y) = EY a b ((LinearMap.ker π).subtype y)` using `fun _ _ _ => rfl`. Establish `hEK : KRel ε₀ EK`. Introduce `a b c d h1 h2`. Use extensionality with `y`. Use `LinearMap.congr_fun (hY a b c d h1 h2) (y : Y)` as an intermediate fact.

Apply the tactic sequence `split_ifs at this ⊢ <;> simpa [EK] using this`. Set `x' : Cn n Y` to `fun A => if x A = 0 then 0 else (hs (x A)).choose`. Establish `hz : ∀ A, x A = 0 → x' A = 0` using `fun A h => if_pos h`. Establish `hx' : Sup ε₀ B (j + 1) x'` using `sup_of_supp hx hz`. Establish `hr' : Ref ε₀ ε x'` using `fun A hA => hr A fun h => hA (hz A h)`.

Establish `hπx : lift n π x' = x`. Use function extensionality and compare the values at `A`. Distinguish the cases in `hA : x A = 0`. Simplify using `[x', hA]`. Simplify using `only [lift_apply, x', if_neg hA]`.

Conclude with `(hs (x A)).choose_spec`. Establish `hy : ∀ A, bd ε₀ EY x' A ∈ LinearMap.ker π`. Introduce `A`. Use `congrFun (lift_bd (ε := ε₀) π EY E (fun i _ => hπ _ _) x') A` as an intermediate fact. Rewrite `this` using `[hπx, hbx]`.

Conclude with `this`. Take `⟨s1, -, s3, -⟩` from `differential_bounded_support n ε₀ Y EY`. Take `⟨-, -, s3', -⟩` from `differential_bounded_support n ε Y EY`. Set `y : Cn n (LinearMap.ker π)` to `fun A => ⟨_, hy A⟩`. Establish `hιy : lift n (LinearMap.ker π).subtype y = bd ε₀ EY x'` using `rfl`.

Establish `hyd : Sup ε₀ B j y` using `sup_of_supp (s1 B j x' hx') fun A hA => Subtype.ext hA`. Establish `hyr : Ref ε₀ ε y` using `fun A hA => (s3' ε₀ x' h0 hr').2 A fun h => hA (Subtype.ext (by rw [← (s3' ε₀ x' h0 hr').1] at h; exact h))`. Establish `hyb : bd ε₀ EK y = 0`. Use `lift_bd (ε := ε₀) _ EK EY (fun i _ => hι _ _) y` as an intermediate fact. Rewrite `this` using `[hιy, show bd ε₀ EY (bd ε₀ EY x') = 0 from LinearMap.congr_fun (hS n ε₀ Y EY hY) x']`.

Use function extensionality and compare the values at `A`. Conclude with `Subtype.ext (congrFun this A)`. Take `⟨w, hw, hDw⟩` from `ih _ EK hEK y hyd hyr hyb`. Establish `hpush` using `congrArg (lift n (LinearMap.ker π).subtype) hDw`. Establish `hl : ∀ {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (φ : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W), (∀ a b x, φ (E a b x) = F a b (φ x)) → ∀ z : Cn n V, lift n φ (lift n (evK ε₀ E a) z) = lift n (evK ε₀ F a) ( …` using `fun φ E F h z => funext fun A => evK_inter φ E F h a _`.

Rewrite `hpush` using `[map_sub, hl _ EK EY hι, lift_evd _ EK EY hι, lift_bd (ε := ε₀) _ EK EY (fun i _ => hι _ _), hιy]`. Establish `c1 : bd ε₀ EY (lift n (evK ε₀ EY a) x') = lift n (evK ε₀ EY a) (bd ε₀ EY x')`. Rewrite using `[(s3' ε₀ x' h0 hr').1, (s3' ε₀ _ h0 fun A hA => hr' A fun h => hA (by simp [h])).1]`. Conclude with `(lift_bd _ EY EY (fun i hi z => (LinearMap.congr_fun ((hab Y EY hY).1 i hi).eq z).symm) x').symm`. Establish `c2 : bd ε₀ EY (evd (Ft ε₀ EY) b x') = evd (Ft ε₀ EY) b (bd ε₀ EY x')` using `free_inter (bd ε₀ EY) _ _ (fun c z => (LinearMap.congr_fun (differential_commutes_weight_operator n ε₀ ε₀ Y EY (fun _ _ h => h) hY c).eq z).symm) b x'`.

Take `⟨t, ht, hbt⟩` from `hac B j (lift n (evK ε₀ EY a) x' - evd (Ft ε₀ EY) b x' - lift n (LinearMap.ker π).subtype w) (((sup_of_supp hx' fun A h => by simp [h]).sub (sup_of_supp hx' fun A h => by rw [evd_Ft_apply, h, map_zero])).sub (sup_of_supp hw fun A h => by simp [h])) (by rw [map_sub, map_sub, c1, c …`. Use `⟨lift n π t, sup_of_supp ht fun A h => by simp [h], ?_⟩` and prove the remaining obligations. Establish `h2 : lift n π (lift n (LinearMap.ker π).subtype w) = 0`. Use function extensionality and compare the values at `A`. Conclude with `(w A).2`.

Rewrite using `[← lift_bd π EY E (fun i _ => hπ _ _), hbt, map_sub, map_sub, h2, hl π EY E hπ, lift_evd π EY E hπ, hπx, sub_zero]`.
-/
theorem genCO_of (hS : BdSq) (hC : Cover2) : GenCO := by
  intro n ε₀ ε a b h0 hab V _ _ E hE B j
  induction j generalizing V with
  | zero =>
    intro x hx _ _
    obtain ⟨w, hw⟩ := (hab V E hE).2 (x B)
    have hxB : ∀ A, A ≠ B → x A = 0 := fun A hA => by
      by_contra h
      obtain ⟨e1, e2⟩ := hx A h
      refine hA (e1 ▸ (filter_true_of_mem fun i hi hc => ?_).symm)
      exact notMem_empty i (card_eq_zero.1 e2 ▸ mem_filter.2 ⟨hi, hc⟩)
    by_cases hB : x B = 0
    · have : x = 0 := funext fun A => by
        by_cases h : A = B
        · rw [h, hB]; rfl
        · exact hxB A h
      subst this
      exact ⟨0, fun A hA => absurd rfl hA, by simp⟩
    have hBn : ∀ i ∈ B, ¬cpt ε₀ i := fun i hi => (mem_filter.1 ((hx B hB).1.symm ▸ hi :)).2
    have hBc : B.filter (cpt ε₀) = ∅ := filter_false_of_mem hBn
    let w' : Cn n V := fun A => ∑ i : Pos n, if cpt ε₀ i ∧ A = insert i B then sg i B • w i else 0
    have hw' : Sup ε₀ B (0 + 1) w' := by
      intro A hA
      obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero hA
      obtain ⟨h1, rfl⟩ : cpt ε₀ i ∧ A = insert i B := by by_contra h; exact hi (if_neg h)
      rw [filter_insert, if_neg (not_not.2 h1), filter_true_of_mem hBn, filter_insert, if_pos h1, hBc]
      simp
    refine ⟨w', hw', funext fun A => ?_⟩
    by_cases hA : A = B
    · subst hA
      rw [Pi.sub_apply, lift_apply, evd_Ft_apply, hBc]
      have e : (fun c => E c c + (wt (∅ : Finset (Pos n)) c : ℂ) • (1 : Module.End ℂ V)) = fun c => E c c := by
        funext c; simp [wt]
      rw [e, hw, bd_apply, Finset.sum_eq_zero (s := univ) (f := fun i => ∑ j : Pos n, ∑ k : Pos n,
        if Tri ε₀ i j k then cre k (ann j (ann i w')) A else 0), add_zero]
      · refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs with hi
        · have hiA : i ∉ A := fun h => hBn i h hi
          rw [ann_apply, if_neg hiA]
          congr 1
          simp only [w']
          rw [Finset.sum_eq_single i, if_pos ⟨hi, rfl⟩, smul_smul, sg_mul_self, one_smul]
          · intro k _ hk
            refine if_neg fun h => ?_
            rcases mem_insert.1 (h.2 ▸ mem_insert_self i A) with h' | h'
            · exact hk h'.symm
            · exact hiA h'
          · simp
        · rfl
      · refine fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
        split_ifs with ht
        · by_contra h
          exact hBn k (tri_ne h).1 ht.cptk
        · rfl
    · rw [Pi.sub_apply, lift_apply, evd_Ft_apply, hxB A hA, map_zero, map_zero, sub_zero]
      by_contra h
      obtain ⟨e1, e2⟩ := sup_bd E hw' (Ne.symm h)
      refine hA (e1 ▸ (filter_true_of_mem fun i hi hc => ?_).symm)
      exact notMem_empty i (card_eq_zero.1 (by omega : (A.filter (cpt ε₀)).card = 0) ▸ mem_filter.2 ⟨hi, hc⟩)
  | succ j ih =>
    intro x hx hr hbx
    obtain ⟨Y, _, _, EY, π, hY, hs, hπ, hac⟩ := hC n ε₀ V E hE
    have hK : ∀ a b, ∀ y ∈ LinearMap.ker π, EY a b y ∈ LinearMap.ker π := by
      intro a b y hy
      rw [LinearMap.mem_ker] at hy ⊢
      rw [hπ, hy, map_zero]
    let EK : Fin n → Fin n → Module.End ℂ (LinearMap.ker π) := fun a b => (EY a b).restrict (hK a b)
    have hι : ∀ a b y, (LinearMap.ker π).subtype (EK a b y) = EY a b ((LinearMap.ker π).subtype y) :=
      fun _ _ _ => rfl
    have hEK : KRel ε₀ EK := by
      intro a b c d h1 h2
      ext y
      have := LinearMap.congr_fun (hY a b c d h1 h2) (y : Y)
      split_ifs at this ⊢ <;> simpa [EK] using this
    classical
    let x' : Cn n Y := fun A => if x A = 0 then 0 else (hs (x A)).choose
    have hz : ∀ A, x A = 0 → x' A = 0 := fun A h => if_pos h
    have hx' : Sup ε₀ B (j + 1) x' := sup_of_supp hx hz
    have hr' : Ref ε₀ ε x' := fun A hA => hr A fun h => hA (hz A h)
    have hπx : lift n π x' = x := by
      funext A
      by_cases hA : x A = 0
      · simp [x', hA]
      · simp only [lift_apply, x', if_neg hA]
        exact (hs (x A)).choose_spec
    have hy : ∀ A, bd ε₀ EY x' A ∈ LinearMap.ker π := by
      intro A
      have := congrFun (lift_bd (ε := ε₀) π EY E (fun i _ => hπ _ _) x') A
      rw [hπx, hbx] at this
      exact this
    obtain ⟨s1, -, s3, -⟩ := differential_bounded_support n ε₀ Y EY
    obtain ⟨-, -, s3', -⟩ := differential_bounded_support n ε Y EY
    let y : Cn n (LinearMap.ker π) := fun A => ⟨_, hy A⟩
    have hιy : lift n (LinearMap.ker π).subtype y = bd ε₀ EY x' := rfl
    have hyd : Sup ε₀ B j y := sup_of_supp (s1 B j x' hx') fun A hA => Subtype.ext hA
    have hyr : Ref ε₀ ε y := fun A hA =>
      (s3' ε₀ x' h0 hr').2 A fun h => hA (Subtype.ext (by rw [← (s3' ε₀ x' h0 hr').1] at h; exact h))
    have hyb : bd ε₀ EK y = 0 := by
      have := lift_bd (ε := ε₀) _ EK EY (fun i _ => hι _ _) y
      rw [hιy, show bd ε₀ EY (bd ε₀ EY x') = 0 from LinearMap.congr_fun (hS n ε₀ Y EY hY) x'] at this
      funext A
      exact Subtype.ext (congrFun this A)
    obtain ⟨w, hw, hDw⟩ := ih _ EK hEK y hyd hyr hyb
    have hpush := congrArg (lift n (LinearMap.ker π).subtype) hDw
    have hl : ∀ {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (φ : V →ₗ[ℂ] W)
        (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W),
        (∀ a b x, φ (E a b x) = F a b (φ x)) → ∀ z : Cn n V,
        lift n φ (lift n (evK ε₀ E a) z) = lift n (evK ε₀ F a) (lift n φ z) :=
      fun φ E F h z => funext fun A => evK_inter φ E F h a _
    rw [map_sub, hl _ EK EY hι, lift_evd _ EK EY hι, lift_bd (ε := ε₀) _ EK EY (fun i _ => hι _ _), hιy] at hpush
    have c1 : bd ε₀ EY (lift n (evK ε₀ EY a) x') = lift n (evK ε₀ EY a) (bd ε₀ EY x') := by
      rw [(s3' ε₀ x' h0 hr').1, (s3' ε₀ _ h0 fun A hA => hr' A fun h => hA (by simp [h])).1]
      exact (lift_bd _ EY EY (fun i hi z => (LinearMap.congr_fun ((hab Y EY hY).1 i hi).eq z).symm) x').symm
    have c2 : bd ε₀ EY (evd (Ft ε₀ EY) b x') = evd (Ft ε₀ EY) b (bd ε₀ EY x') :=
      free_inter (bd ε₀ EY) _ _
        (fun c z => (LinearMap.congr_fun (differential_commutes_weight_operator n ε₀ ε₀ Y EY (fun _ _ h => h) hY c).eq z).symm) b x'
    obtain ⟨t, ht, hbt⟩ := hac B j
      (lift n (evK ε₀ EY a) x' - evd (Ft ε₀ EY) b x' - lift n (LinearMap.ker π).subtype w)
      (((sup_of_supp hx' fun A h => by simp [h]).sub
        (sup_of_supp hx' fun A h => by rw [evd_Ft_apply, h, map_zero])).sub (sup_of_supp hw fun A h => by simp [h]))
      (by rw [map_sub, map_sub, c1, c2, hpush, sub_self])
    refine ⟨lift n π t, sup_of_supp ht fun A h => by simp [h], ?_⟩
    have h2 : lift n π (lift n (LinearMap.ker π).subtype w) = 0 := by
      funext A
      exact (w A).2
    rw [← lift_bd π EY E (fun i _ => hπ _ _), hbt, map_sub, map_sub, h2, hl π EY E hπ, lift_evd π EY E hπ, hπx,
      sub_zero]

end CompanionTheory.D.LK
