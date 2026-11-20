import Formalism.SharpRestriction.GrowthBounds.RootWeights.HighestWeightLatticeOfFirstPart

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

/- English proof (translation)
Unfold `IsGLRep at hE`. Establish `h` using `LinearMap.congr_fun (hE.1 a b c d) x`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h`. Establish `key : E a b (E c d x) = E c d (E a b x) + ((if b = c then E a d else 0) x - (if d = a then E c b else 0) x)`. Rewrite using `[← h]`.

Normalize the expressions using the abelian group laws. Rewrite using `[key]`. Apply the tactic sequence `split_ifs <;> (try simp only [LinearMap.zero_apply, sub_zero, add_zero, zero_sub]) <;> abel`.
-/
theorem gl_rep_commutation_apply {E : GLOps n (KK O) V} (hE : IsGLRep E) (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) + (if b = c then E a d x else 0) - (if d = a then E c b x else 0) := by
  unfold IsGLRep at hE
  have h := LinearMap.congr_fun (hE.1 a b c d) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have key : E a b (E c d x) = E c d (E a b x) +
      ((if b = c then E a d else 0) x - (if d = a then E c b else 0) x) := by
    rw [← h]; abel
  rw [key]
  split_ifs <;> (try simp only [LinearMap.zero_apply, sub_zero, add_zero, zero_sub]) <;> abel

/- English proof (translation)
Simplify using `only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hx ⊢`. Introduce `c`. Rewrite using `[gl_rep_commutation_apply hE c c a b x, hx c, map_smul]`. Simplify using `only [Pi.add_apply, rootW, Pi.sub_apply, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> subst_vars <;> (try simp only [Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_zero, add_smul, sub_smul, one_smul, zero_smul, smul_zero, sub_zero, add_zero, zero_add, zero_sub]) <;> (try abel) <;> (try simp_all)`.
-/
theorem gl_rep_operator_weight_shift {E : GLOps n (KK O) V} (hE : IsGLRep E) {mu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E mu)
    (a b : Fin n) : E a b x ∈ weightSp E (mu + rootW a b) := by
  classical
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero] at hx ⊢
  intro c
  rw [gl_rep_commutation_apply hE c c a b x, hx c, map_smul]
  simp only [Pi.add_apply, rootW, Pi.sub_apply, Pi.single_apply]
  split_ifs <;> subst_vars <;>
    (try simp only [Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_zero, add_smul, sub_smul, one_smul,
      zero_smul, smul_zero, sub_zero, add_zero, zero_add, zero_sub]) <;> (try abel) <;> (try simp_all)

/- English proof (translation)
Set `C : V → Prop` to `fun y => ∃ (F : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V), (∀ mu ∈ F, Pr mu ∧ f mu ∈ weightSp E mu) ∧ y = ∑ mu ∈ F, f mu`. Establish `hmem : ∀ mu, ∀ y ∈ ⨆ (_ : Pr mu), weightSp E mu, C y`. Introduce `mu y hy`. Simplify using `only [C]`. Distinguish the cases in `hP : Pr mu`.

Use `⟨{mu}, fun _ => y, ?_, by simp⟩` and prove the remaining obligations. Introduce `nu hnu`. Rewrite `hnu` using `[Finset.mem_singleton]`. Substitute `hnu` using the available equality. Rewrite `hy` using `[iSup_pos hP]`.

Conclude with `⟨hP, hy⟩`. Rewrite `hy` using `[iSup_neg hP]`. Use `⟨∅, fun _ => 0, by simp, ?_⟩` and prove the remaining obligations. Simplify using `[(Submodule.mem_bot _).mp hy]`. Establish `hzero : C 0` using `⟨∅, fun _ => 0, by simp, by simp⟩`.

Establish `hadd : ∀ y z, C y → C z → C (y + z)`. Introduce `y z hy hz`. Simplify using `only [C] at hy hz ⊢`. Take `⟨F1, f1, h1, rfl⟩` from `hy`. Take `⟨F2, f2, h2, rfl⟩` from `hz`.

Use `⟨F1 ∪ F2, fun mu => (if mu ∈ F1 then f1 mu else 0) + (if mu ∈ F2 then f2 mu else 0), ?_, ?_⟩` and prove the remaining obligations. Introduce `mu hmu`. Establish `hPr : Pr mu`. Break down `Finset.mem_union.mp hmu with h | h` into its components or cases. Conclude with `(h1 mu h).1`.

Conclude with `(h2 mu h).1`. Use `⟨hPr, Submodule.add_mem _ ?_ ?_⟩` and prove the remaining obligations. Use `split_ifs with h`. Conclude with `(h1 mu h).2`. Conclude with `Submodule.zero_mem _`.

Use `split_ifs with h`. Conclude with `(h2 mu h).2`. Conclude with `Submodule.zero_mem _`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.union_inter_cancel_left, Finset.union_inter_cancel_right]`. Use `first`.

Consider the case `exact Submodule.iSup_induction (motive := C) _ hx hmem hzero hadd`. Consider the case `exact Submodule.iSup_induction (C := C) _ hx hmem hzero hadd`.
-/
theorem mem_weight_sup_exists_finset_sum (E : GLOps n (KK O) V) (Pr : (Fin n → ℤ) → Prop) {x : V}
    (hx : x ∈ ⨆ mu, ⨆ (_ : Pr mu), weightSp E mu) :
    ∃ (F : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V), (∀ mu ∈ F, Pr mu ∧ f mu ∈ weightSp E mu) ∧
      x = ∑ mu ∈ F, f mu := by
  classical
  let C : V → Prop := fun y => ∃ (F : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V),
    (∀ mu ∈ F, Pr mu ∧ f mu ∈ weightSp E mu) ∧ y = ∑ mu ∈ F, f mu
  have hmem : ∀ mu, ∀ y ∈ ⨆ (_ : Pr mu), weightSp E mu, C y := by
    intro mu y hy
    dsimp only [C]
    by_cases hP : Pr mu
    · refine ⟨{mu}, fun _ => y, ?_, by simp⟩
      intro nu hnu
      rw [Finset.mem_singleton] at hnu
      subst hnu
      rw [iSup_pos hP] at hy
      exact ⟨hP, hy⟩
    · rw [iSup_neg hP] at hy
      refine ⟨∅, fun _ => 0, by simp, ?_⟩
      simp [(Submodule.mem_bot _).mp hy]
  have hzero : C 0 := ⟨∅, fun _ => 0, by simp, by simp⟩
  have hadd : ∀ y z, C y → C z → C (y + z) := by
    intro y z hy hz
    dsimp only [C] at hy hz ⊢
    obtain ⟨F1, f1, h1, rfl⟩ := hy
    obtain ⟨F2, f2, h2, rfl⟩ := hz
    refine ⟨F1 ∪ F2, fun mu => (if mu ∈ F1 then f1 mu else 0) + (if mu ∈ F2 then f2 mu else 0), ?_, ?_⟩
    · intro mu hmu
      have hPr : Pr mu := by
        rcases Finset.mem_union.mp hmu with h | h
        · exact (h1 mu h).1
        · exact (h2 mu h).1
      refine ⟨hPr, Submodule.add_mem _ ?_ ?_⟩
      · split_ifs with h
        · exact (h1 mu h).2
        · exact Submodule.zero_mem _
      · split_ifs with h
        · exact (h2 mu h).2
        · exact Submodule.zero_mem _
    · rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
        Finset.union_inter_cancel_left, Finset.union_inter_cancel_right]
  first
  | exact Submodule.iSup_induction (motive := C) _ hx hmem hzero hadd
  | exact Submodule.iSup_induction (C := C) _ hx hmem hzero hadd

/- English proof (translation)
Establish `hwt : ∀ (a : Fin n) (mu : Fin n → ℤ) (y : V), y ∈ weightSp E mu → E a a y = ((mu a : ℤ) : KK O) • y`. Introduce `a mu y hy`. Simplify using `only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hy`. Conclude with `hy a`. Establish `key : ∀ (F : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V), (∀ mu ∈ F, mu ≠ nu) → (∀ mu ∈ F, f mu ∈ weightSp E mu) → ∑ mu ∈ F, f mu ∈ weightSp E nu → ∑ mu ∈ F, f mu = 0`.

Introduce `F`. Proceed by induction on `F using Finset.induction_on with`. Consider the case `empty => intro f _ _ _`. Simplify using the standard rewrite rules. Consider the case `insert mu0 F hmu0 ih`.

Introduce `f hF hw hs`. Establish `hne : mu0 ≠ nu` using `hF mu0 (Finset.mem_insert_self _ _)`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, mu0 a ≠ nu a := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hne (funext h)`. Set `g : (Fin n → ℤ) → V` to `fun mu => (((mu a : ℤ) : KK O) - ((mu0 a : ℤ) : KK O)) • f mu`. Establish `hES : ∑ mu ∈ insert mu0 F, E a a (f mu) = ∑ mu ∈ insert mu0 F, ((mu a : ℤ) : KK O) • f mu` using `Finset.sum_congr rfl (fun mu hmu => hwt a mu (f mu) (hw mu hmu))`. Establish `hkey : (((nu a : ℤ) : KK O) - ((mu0 a : ℤ) : KK O)) • ∑ mu ∈ insert mu0 F, f mu = ∑ mu ∈ F, g mu`. Establish `h1 : E a a (∑ mu ∈ insert mu0 F, f mu) = ((nu a : ℤ) : KK O) • ∑ mu ∈ insert mu0 F, f mu` using `hwt a nu _ hs`.

Rewrite using `[sub_smul, ← h1, map_sum, hES]`. Simplify using `only [g, sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[Finset.sum_insert hmu0, Finset.sum_insert hmu0, smul_add, Finset.smul_sum]`. Normalize the expressions using the abelian group laws. Establish `hg : ∀ mu ∈ F, g mu ∈ weightSp E mu` using `fun mu hmu => Submodule.smul_mem _ _ (hw mu (Finset.mem_insert_of_mem hmu))`.

Establish `hF' : ∀ mu ∈ F, mu ≠ nu` using `fun mu hmu => hF mu (Finset.mem_insert_of_mem hmu)`. Establish `hmemnu : ∑ mu ∈ F, g mu ∈ weightSp E nu`. Rewrite using `[← hkey]`. Conclude with `Submodule.smul_mem _ _ hs`. Establish `h0` using `ih g hF' hg hmemnu`.

Rewrite `h0` using `[← hkey]`. Establish `hc : (((nu a : ℤ) : KK O) - ((mu0 a : ℤ) : KK O)) ≠ 0`. Rewrite using `[sub_ne_zero]`. Conclude with `fun h => ha (Int.cast_injective h).symm`. Conclude with `(smul_eq_zero.mp h0).resolve_left hc`.

Take `⟨F, f, hf, rfl⟩` from `mem_weight_sup_exists_finset_sum E Pr hx2`. Conclude with `key F f (fun mu hmu h => hn (h ▸ (hf mu hmu).1)) (fun mu hmu => (hf mu hmu).2) hx`.
-/
theorem weight_support_sum_eq_zero [CharZero (KK O)] (E : GLOps n (KK O) V) (Pr : (Fin n → ℤ) → Prop) {nu : Fin n → ℤ} {x : V}
    (hx : x ∈ weightSp E nu) (hx2 : x ∈ ⨆ mu, ⨆ (_ : Pr mu), weightSp E mu) (hn : ¬ Pr nu) : x = 0 := by
  classical
  have hwt : ∀ (a : Fin n) (mu : Fin n → ℤ) (y : V), y ∈ weightSp E mu → E a a y = ((mu a : ℤ) : KK O) • y := by
    intro a mu y hy
    simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero] at hy
    exact hy a
  have key : ∀ (F : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V), (∀ mu ∈ F, mu ≠ nu) →
      (∀ mu ∈ F, f mu ∈ weightSp E mu) → ∑ mu ∈ F, f mu ∈ weightSp E nu → ∑ mu ∈ F, f mu = 0 := by
    intro F
    induction F using Finset.induction_on with
    | empty => intro f _ _ _; simp
    | insert mu0 F hmu0 ih =>
      intro f hF hw hs
      have hne : mu0 ≠ nu := hF mu0 (Finset.mem_insert_self _ _)
      obtain ⟨a, ha⟩ : ∃ a, mu0 a ≠ nu a := by
        by_contra h
        push_neg at h
        exact hne (funext h)
      let g : (Fin n → ℤ) → V := fun mu => (((mu a : ℤ) : KK O) - ((mu0 a : ℤ) : KK O)) • f mu
      have hES : ∑ mu ∈ insert mu0 F, E a a (f mu) = ∑ mu ∈ insert mu0 F, ((mu a : ℤ) : KK O) • f mu :=
        Finset.sum_congr rfl (fun mu hmu => hwt a mu (f mu) (hw mu hmu))
      have hkey : (((nu a : ℤ) : KK O) - ((mu0 a : ℤ) : KK O)) • ∑ mu ∈ insert mu0 F, f mu = ∑ mu ∈ F, g mu := by
        have h1 : E a a (∑ mu ∈ insert mu0 F, f mu) = ((nu a : ℤ) : KK O) • ∑ mu ∈ insert mu0 F, f mu :=
          hwt a nu _ hs
        rw [sub_smul, ← h1, map_sum, hES]
        simp only [g, sub_smul, Finset.sum_sub_distrib]
        rw [Finset.sum_insert hmu0, Finset.sum_insert hmu0, smul_add, Finset.smul_sum]
        abel
      have hg : ∀ mu ∈ F, g mu ∈ weightSp E mu := fun mu hmu =>
        Submodule.smul_mem _ _ (hw mu (Finset.mem_insert_of_mem hmu))
      have hF' : ∀ mu ∈ F, mu ≠ nu := fun mu hmu => hF mu (Finset.mem_insert_of_mem hmu)
      have hmemnu : ∑ mu ∈ F, g mu ∈ weightSp E nu := by
        rw [← hkey]
        exact Submodule.smul_mem _ _ hs
      have h0 := ih g hF' hg hmemnu
      rw [← hkey] at h0
      have hc : (((nu a : ℤ) : KK O) - ((mu0 a : ℤ) : KK O)) ≠ 0 := by
        rw [sub_ne_zero]
        exact fun h => ha (Int.cast_injective h).symm
      exact (smul_eq_zero.mp h0).resolve_left hc
  obtain ⟨F, f, hf, rfl⟩ := mem_weight_sup_exists_finset_sum E Pr hx2
  exact key F f (fun mu hmu h => hn (h ▸ (hf mu hmu).1)) (fun mu hmu => (hf mu hmu).2) hx

/- English proof (translation)
Introduce `x hx`. Unfold `Umon at hu`. Proceed by induction on `hu using Submonoid.closure_induction generalizing x with`. Consider the case `mem g hg`. Take `⟨ab, rfl⟩` from `hg`.

Conclude with `hW ab.1 ab.2 x hx`. Consider the case `one => simpa using hx`. Consider the case `mul g g' _ _ ihg ihg'`. Conclude with `ihg _ (ihg' x hx)`.
-/
theorem stable_enveloping_monoid_mem {E : GLOps n (KK O) V} {W : Submodule (KK O) V} (hW : ∀ a b, ∀ y ∈ W, E a b y ∈ W)
    {u : Module.End (KK O) V} (hu : u ∈ Umon E) : ∀ x ∈ W, u x ∈ W := by
  intro x hx
  unfold Umon at hu
  induction hu using Submonoid.closure_induction generalizing x with
  | mem g hg =>
    obtain ⟨ab, rfl⟩ := hg
    exact hW ab.1 ab.2 x hx
  | one => simpa using hx
  | mul g g' _ _ ihg ihg' =>
    exact ihg _ (ihg' x hx)

/- English proof (translation)
Establish `hI'` using `hI`. Unfold `IsIrrHW at hI'`. Apply `eq_top_iff.mpr` to reduce the goal to its premises. Rewrite using `[← hI'.2.2.2, Submodule.span_le]`. Introduce and unpack `x ⟨u, hu, rfl⟩`.

Conclude with `stable_enveloping_monoid_mem hW hu v hv`.
-/
theorem irreducible_stable_contains_eq_top {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v)
    {W : Submodule (KK O) V} (hW : ∀ a b, ∀ y ∈ W, E a b y ∈ W) (hv : v ∈ W) : W = ⊤ := by
  have hI' := hI
  unfold IsIrrHW at hI'
  apply eq_top_iff.mpr
  rw [← hI'.2.2.2, Submodule.span_le]
  rintro x ⟨u, hu, rfl⟩
  exact stable_enveloping_monoid_mem hW hu v hv

/- English proof (translation)
Establish `hI'` using `hI`. Unfold `IsIrrHW IsGLRep at hI'`. Take `⟨W, hWf, hvW, hWst⟩` from `hI'.1.2.1 v`. Establish `hW : W = ⊤` using `irreducible_stable_contains_eq_top hI hWst hvW`. Substitute `hW` using the available equality.

Conclude with `LinearEquiv.finiteDimensional Submodule.topEquiv`.
-/
theorem irreducible_highest_weight_findim {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) :
    FiniteDimensional (KK O) V := by
  have hI' := hI
  unfold IsIrrHW IsGLRep at hI'
  obtain ⟨W, hWf, hvW, hWst⟩ := hI'.1.2.1 v
  have hW : W = ⊤ := irreducible_stable_contains_eq_top hI hWst hvW
  subst hW
  exact LinearEquiv.finiteDimensional Submodule.topEquiv

def loweringOperatorMonoid (E : GLOps n (KK O) V) : Submonoid (Module.End (KK O) V) :=
  Submonoid.closure {g | ∃ a b : Fin n, b < a ∧ g = E a b}

/- English proof (translation)
Establish `hI'` using `hI`. Unfold `IsIrrHW IsHWV at hI'`. Take `⟨hE, _, ⟨_, hvw, hraise⟩, _⟩` from `hI'`. Establish `hvw' : ∀ a, E a a v = ((lam a : ℤ) : KK O) • v`. Simplify using `only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hvw`.

Conclude with `hvw`. Establish `hvS : ∀ u ∈ loweringOperatorMonoid E, u v ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v}` using `fun u hu => Submodule.subset_span ⟨u, hu, rfl⟩`. Establish `hv1 : v ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v}` using `hvS 1 (Submonoid.one_mem _)`. Establish `hlow : ∀ c d : Fin n, d < c → ∀ y ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v}, E c d y ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v}`. Introduce `c d hdc y hy`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨u, hu, rfl⟩` from `hz`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨E c d * u, Submonoid.mul_mem _ ?_ hu, rfl⟩` and prove the remaining obligations.

Unfold `loweringOperatorMonoid`. Conclude with `Submonoid.subset_closure ⟨c, d, hdc, rfl⟩`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hz`.

Consider the case `smul r y _ hy => rw [map_smul]`. Conclude with `Submodule.smul_mem _ r hy`. Establish `hall : ∀ u ∈ loweringOperatorMonoid E, ∀ a b, E a b (u v) ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v}`. Introduce `u hu`. Unfold `loweringOperatorMonoid at hu`.

Proceed by induction on `hu using Submonoid.closure_induction_left with`. Consider the case `one`. Introduce `a b`. Rewrite using `[Module.End.one_apply]`. Break down `lt_trichotomy a b with hab | rfl | hab` into its components or cases.

Rewrite using `[hraise a b hab]`. Conclude with `Submodule.zero_mem _`. Rewrite using `[hvw' a]`. Conclude with `Submodule.smul_mem _ _ hv1`. Conclude with `hlow a b hab v hv1`.

Consider the case `mul_left g hg u' _ ih`. Introduce `a b`. Take `⟨c, d, hdc, rfl⟩` from `hg`. Rewrite using `[Module.End.mul_apply, gl_rep_commutation_apply hE a b c d]`. Use `Submodule.sub_mem _ (Submodule.add_mem _ (hlow c d hdc _ (ih a b)) ?_) ?_` and prove the remaining obligations.

Use `split_ifs`. Conclude with `ih a d`. Conclude with `Submodule.zero_mem _`. Use `split_ifs`. Conclude with `ih c b`.

Conclude with `Submodule.zero_mem _`. Establish `hstab : ∀ a b, ∀ y ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v}, E a b y ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v}`. Introduce `a b y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`.

Take `⟨u, hu, rfl⟩` from `hz`. Conclude with `hall u hu a b`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hz`.

Consider the case `smul r y _ hy => rw [map_smul]`. Conclude with `Submodule.smul_mem _ r hy`. Conclude with `irreducible_stable_contains_eq_top hI hstab hv1`.
-/
theorem irreducible_lowering_span_top {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) :
    Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v} = ⊤ := by
  classical
  have hI' := hI
  unfold IsIrrHW IsHWV at hI'
  obtain ⟨hE, _, ⟨_, hvw, hraise⟩, _⟩ := hI'
  have hvw' : ∀ a, E a a v = ((lam a : ℤ) : KK O) • v := by
    simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero] at hvw
    exact hvw
  have hvS : ∀ u ∈ loweringOperatorMonoid E, u v ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v} := fun u hu => Submodule.subset_span ⟨u, hu, rfl⟩
  have hv1 : v ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v} := hvS 1 (Submonoid.one_mem _)
  have hlow : ∀ c d : Fin n, d < c → ∀ y ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v}, E c d y ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v} := by
    intro c d hdc y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, hu, rfl⟩ := hz
      apply Submodule.subset_span
      refine ⟨E c d * u, Submonoid.mul_mem _ ?_ hu, rfl⟩
      unfold loweringOperatorMonoid
      exact Submonoid.subset_closure ⟨c, d, hdc, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [map_smul]; exact Submodule.smul_mem _ r hy
  have hall : ∀ u ∈ loweringOperatorMonoid E, ∀ a b, E a b (u v) ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v} := by
    intro u hu
    unfold loweringOperatorMonoid at hu
    induction hu using Submonoid.closure_induction_left with
    | one =>
      intro a b
      rw [Module.End.one_apply]
      rcases lt_trichotomy a b with hab | rfl | hab
      · rw [hraise a b hab]
        exact Submodule.zero_mem _
      · rw [hvw' a]
        exact Submodule.smul_mem _ _ hv1
      · exact hlow a b hab v hv1
    | mul_left g hg u' _ ih =>
      intro a b
      obtain ⟨c, d, hdc, rfl⟩ := hg
      rw [Module.End.mul_apply, gl_rep_commutation_apply hE a b c d]
      refine Submodule.sub_mem _ (Submodule.add_mem _ (hlow c d hdc _ (ih a b)) ?_) ?_
      · split_ifs
        · exact ih a d
        · exact Submodule.zero_mem _
      · split_ifs
        · exact ih c b
        · exact Submodule.zero_mem _
  have hstab : ∀ a b, ∀ y ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v}, E a b y ∈ Submodule.span (KK O) {x | ∃ u ∈ loweringOperatorMonoid E, x = u v} := by
    intro a b y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, hu, rfl⟩ := hz
      exact hall u hu a b
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [map_smul]; exact Submodule.smul_mem _ r hy
  exact irreducible_stable_contains_eq_top hI hstab hv1

end hw

end Formalism.MainNotions.G.GLWeightTheory
