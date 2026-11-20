import Formalism.SharpRestriction.GrowthBounds.RootWeights.EnvelopingMonoidPreservesStable

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def restrictOperators (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a b, ∀ z ∈ W, E a b z ∈ W) : GLOps n K W :=
  fun a b => (E a b).restrict (hW a b)

def IsRestrictionOfAlt (W : Submodule K V) (u : Module.End K W) (u' : Module.End K V) : Prop :=
  ∀ z : W, (u z : V) = u' z

/- English proof (translation)
Introduce `_` and use `rfl`.
-/
theorem restriction_compat_operator (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a b, ∀ z ∈ W, E a b z ∈ W) (a b : Fin n) :
    IsRestrictionOfAlt W (restrictOperators E W hW a b) (E a b) := fun _ => rfl

/- English proof (translation)
Introduce `_` and use `rfl`.
-/
theorem restriction_compat_one (W : Submodule K V) : IsRestrictionOfAlt W 1 1 := fun _ => rfl

/- English proof (translation)
Introduce `z` and use `by rw [Module.End.mul_apply, Module.End.mul_apply, h1, h2]`.
-/
theorem restriction_compat_mul {W : Submodule K V} {u v : Module.End K W} {u' v' : Module.End K V}
    (h1 : IsRestrictionOfAlt W u u') (h2 : IsRestrictionOfAlt W v v') : IsRestrictionOfAlt W (u * v) (u' * v') := fun z => by
  rw [Module.End.mul_apply, Module.End.mul_apply, h1, h2]

/- English proof (translation)
Introduce `z` and use `by rw [LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul, h1]`.
-/
theorem restriction_compat_smul {W : Submodule K V} {u : Module.End K W} {u' : Module.End K V} (c : K)
    (h1 : IsRestrictionOfAlt W u u') : IsRestrictionOfAlt W (c • u) (c • u') := fun z => by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul, h1]

/- English proof (translation)
Introduce `z` and use `by rw [LinearMap.sub_apply, LinearMap.sub_apply, Submodule.coe_sub, h1, h2]`.
-/
theorem restriction_compat_sub {W : Submodule K V} {u v : Module.End K W} {u' v' : Module.End K V}
    (h1 : IsRestrictionOfAlt W u u') (h2 : IsRestrictionOfAlt W v v') : IsRestrictionOfAlt W (u - v) (u' - v') := fun z => by
  rw [LinearMap.sub_apply, LinearMap.sub_apply, Submodule.coe_sub, h1, h2]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using restriction_compat_one W`. Consider the case `succ k ih => rw [pow_succ, pow_succ]`. Conclude with `restriction_compat_mul ih h1`.
-/
theorem restriction_compat_pow {W : Submodule K V} {u : Module.End K W} {u' : Module.End K V}
    (h1 : IsRestrictionOfAlt W u u') (k : ℕ) : IsRestrictionOfAlt W (u ^ k) (u' ^ k) := by
  induction k with
  | zero => simpa using restriction_compat_one W
  | succ k ih => rw [pow_succ, pow_succ]; exact restriction_compat_mul ih h1

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simpa using restriction_compat_one W`. Consider the case `cons a l ih => rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]`. Conclude with `restriction_compat_mul (h a) ih`.
-/
theorem restriction_compat_list_prod {W : Submodule K V} (l : List ℕ) (f : ℕ → Module.End K W) (f' : ℕ → Module.End K V)
    (h : ∀ j, IsRestrictionOfAlt W (f j) (f' j)) : IsRestrictionOfAlt W (l.map f).prod (l.map f').prod := by
  induction l with
  | nil => simpa using restriction_compat_one W
  | cons a l ih => rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]; exact restriction_compat_mul (h a) ih

/- English proof (translation)
Proceed by induction on `hu using Submonoid.closure_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩` into its components or cases. Conclude with `⟨divPowE E a b k, Submonoid.subset_closure (Or.inl ⟨a, b, k, hab, rfl⟩), restriction_compat_smul _ (restriction_compat_pow (restriction_compat_operator E W hW a b) k)⟩`. Conclude with `⟨binomE E a k, Submonoid.subset_closure (Or.inr ⟨a, k, rfl⟩), restriction_compat_smul _ (restriction_compat_list_prod _ _ _ fun j => restriction_compat_sub (restriction_compat_operator E W hW a a) (restriction_compat_smul _ (restriction_compat_one W)))⟩`.

Consider the case `one => exact ⟨1, Submonoid.one_mem _, restriction_compat_one W⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨x', hx', hxc⟩` from `hx`. Take `⟨y', hy', hyc⟩` from `hy`. Conclude with `⟨x' * y', Submonoid.mul_mem _ hx' hy', restriction_compat_mul hxc hyc⟩`.
-/
theorem integral_enveloping_lifts (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a b, ∀ z ∈ W, E a b z ∈ W)
    (u : Module.End K W) (hu : u ∈ UZmon (restrictOperators E W hW)) : ∃ u' ∈ UZmon E, IsRestrictionOfAlt W u u' := by
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
    · exact ⟨divPowE E a b k, Submonoid.subset_closure (Or.inl ⟨a, b, k, hab, rfl⟩),
        restriction_compat_smul _ (restriction_compat_pow (restriction_compat_operator E W hW a b) k)⟩
    · exact ⟨binomE E a k, Submonoid.subset_closure (Or.inr ⟨a, k, rfl⟩),
        restriction_compat_smul _ (restriction_compat_list_prod _ _ _ fun j =>
          restriction_compat_sub (restriction_compat_operator E W hW a a) (restriction_compat_smul _ (restriction_compat_one W)))⟩
  | one => exact ⟨1, Submonoid.one_mem _, restriction_compat_one W⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx', hxc⟩ := hx
    obtain ⟨y', hy', hyc⟩ := hy
    exact ⟨x' * y', Submonoid.mul_mem _ hx' hy', restriction_compat_mul hxc hyc⟩

/- English proof (translation)
Proceed by induction on `hu using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨ab, rfl⟩` from `hx`. Conclude with `⟨restrictOperators E W hW ab.1 ab.2, Submonoid.subset_closure ⟨ab, rfl⟩, restriction_compat_operator E W hW ab.1 ab.2⟩`. Consider the case `one => exact ⟨1, Submonoid.one_mem _, restriction_compat_one W⟩`.

Consider the case `mul x y _ _ hx hy`. Take `⟨x', hx', hxc⟩` from `hx`. Take `⟨y', hy', hyc⟩` from `hy`. Conclude with `⟨x' * y', Submonoid.mul_mem _ hx' hy', restriction_compat_mul hxc hyc⟩`.
-/
theorem enveloping_monoid_restricts (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a b, ∀ z ∈ W, E a b z ∈ W)
    (u' : Module.End K V) (hu : u' ∈ Umon E) : ∃ u ∈ Umon (restrictOperators E W hW), IsRestrictionOfAlt W u u' := by
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨ab, rfl⟩ := hx
    exact ⟨restrictOperators E W hW ab.1 ab.2, Submonoid.subset_closure ⟨ab, rfl⟩, restriction_compat_operator E W hW ab.1 ab.2⟩
  | one => exact ⟨1, Submonoid.one_mem _, restriction_compat_one W⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx', hxc⟩ := hx
    obtain ⟨y', hy', hyc⟩ := hy
    exact ⟨x' * y', Submonoid.mul_mem _ hx' hy', restriction_compat_mul hxc hyc⟩

/- English proof (translation)
Rewrite using `[mem_weightSpace_iff_diag_action, mem_weightSpace_iff_diag_action]`. Use `forall_congr' fun a => ?_` and prove the remaining obligations. Rewrite using `[Subtype.ext_iff, Submodule.coe_smul]`. Both sides reduce to the same expression.
-/
theorem restricted_weightSpace_iff (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a b, ∀ z ∈ W, E a b z ∈ W)
    (mu : Fin n → ℤ) (z : W) : z ∈ weightSp (restrictOperators E W hW) mu ↔ (z : V) ∈ weightSp E mu := by
  rw [mem_weightSpace_iff_diag_action, mem_weightSpace_iff_diag_action]
  refine forall_congr' fun a => ?_
  rw [Subtype.ext_iff, Submodule.coe_smul]
  rfl

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `z`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h` using `LinearMap.congr_fun (hrel a b c d) (z : V)`. Establish `hl : (((restrictOperators E W hW a b * restrictOperators E W hW c d - restrictOperators E W hW c d * restrictOperators E W hW a b) z : W) : V) = (E a b * E c d - E c d * E a b) (z : V)` using `restriction_compat_sub (restriction_compat_mul (restriction_compat_operator E W hW a b) (restriction_compat_operator E W hW c d)) (restriction_compat_mul (restriction_compat_operator E W hW c d) (restriction_compat_operator E W hW a b)) z`.

Rewrite using `[hl, h]`. Establish `h0 : IsRestrictionOfAlt W 0 0` using `fun _ => rfl`. Use `(restriction_compat_sub (u := if b = c then restrictOperators E W hW a d else 0) (v := if d = a then restrictOperators E W hW c b else 0) ?_ ?_ z).symm` and prove the remaining obligations. Use `split_ifs`. Conclude with `restriction_compat_operator E W hW a d`.

Conclude with `h0`. Use `split_ifs`. Conclude with `restriction_compat_operator E W hW c b`. Conclude with `h0`.
-/
theorem restricted_operators_gl_relation {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (W : Submodule K V) (hW : ∀ a b, ∀ z ∈ W, E a b z ∈ W) (a b c d : Fin n) :
    restrictOperators E W hW a b * restrictOperators E W hW c d - restrictOperators E W hW c d * restrictOperators E W hW a b =
      (if b = c then restrictOperators E W hW a d else 0) - (if d = a then restrictOperators E W hW c b else 0) := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  have h := LinearMap.congr_fun (hrel a b c d) (z : V)
  have hl : (((restrictOperators E W hW a b * restrictOperators E W hW c d - restrictOperators E W hW c d * restrictOperators E W hW a b) z : W) : V)
      = (E a b * E c d - E c d * E a b) (z : V) :=
    restriction_compat_sub (restriction_compat_mul (restriction_compat_operator E W hW a b) (restriction_compat_operator E W hW c d))
      (restriction_compat_mul (restriction_compat_operator E W hW c d) (restriction_compat_operator E W hW a b)) z
  rw [hl, h]
  have h0 : IsRestrictionOfAlt W 0 0 := fun _ => rfl
  refine (restriction_compat_sub (u := if b = c then restrictOperators E W hW a d else 0)
    (v := if d = a then restrictOperators E W hW c b else 0) ?_ ?_ z).symm
  · split_ifs
    · exact restriction_compat_operator E W hW a d
    · exact h0
  · split_ifs
    · exact restriction_compat_operator E W hW c b
    · exact h0

/- English proof (translation)
Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨u, hu, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨E a b * u, Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu, rfl⟩`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem generated_subrep_stable (E : GLOps n K V) (h : V) (a b : Fin n) (z : V) (hz : z ∈ generatedSubrep E h) :
    E a b z ∈ generatedSubrep E h := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    exact Submodule.subset_span ⟨E a b * u, Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨1, Submonoid.one_mem _, rfl⟩`.
-/
theorem mem_generated_subrep_self (E : GLOps n K V) (h : V) : h ∈ generatedSubrep E h :=
  Submodule.subset_span ⟨1, Submonoid.one_mem _, rfl⟩

/- English proof (translation)
Proceed by induction on `hu using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨ab, rfl⟩` from `hx`. Introduce `mu z hz`. Conclude with `⟨_, operator_shifts_weight_by_root hrel ab.1 ab.2 mu z hz⟩`.

Consider the case `one => intro mu z hz; exact ⟨mu, by simpa using hz⟩`. Consider the case `mul x y _ _ hx hy`. Introduce `mu z hz`. Take `⟨mu1, h1⟩` from `hy mu z hz`. Take `⟨mu2, h2⟩` from `hx mu1 _ h1`.

Conclude with `⟨mu2, by rw [Module.End.mul_apply]; exact h2⟩`.
-/
theorem enveloping_word_maps_weight {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (u : Module.End K V) (hu : u ∈ Umon E) : ∀ (mu : Fin n → ℤ) (x : V), x ∈ weightSp E mu →
      ∃ mu', u x ∈ weightSp E mu' := by
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨ab, rfl⟩ := hx
    intro mu z hz
    exact ⟨_, operator_shifts_weight_by_root hrel ab.1 ab.2 mu z hz⟩
  | one => intro mu z hz; exact ⟨mu, by simpa using hz⟩
  | mul x y _ _ hx hy =>
    intro mu z hz
    obtain ⟨mu1, h1⟩ := hy mu z hz
    obtain ⟨mu2, h2⟩ := hx mu1 _ h1
    exact ⟨mu2, by rw [Module.End.mul_apply]; exact h2⟩

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨z, hz⟩ _`. Establish `key : ∀ (x : V) (hx : x ∈ generatedSubrep E h), (⟨x, hx⟩ : generatedSubrep E h) ∈ Submodule.span K {x : generatedSubrep E h | ∃ u ∈ Umon (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h)), x = u ⟨h, mem_generated_subrep_self E h⟩}`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨u', hu', rfl⟩` from `hx`. Take `⟨u, hu, hc⟩` from `enveloping_monoid_restricts E _ (generated_subrep_stable E h) u' hu'`. Conclude with `Submodule.subset_span ⟨u, hu, Subtype.ext (hc ⟨h, mem_generated_subrep_self E h⟩).symm⟩`. Consider the case `zero => exact Submodule.zero_mem _`.

Consider the case `add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy`. Consider the case `smul c x hx ihx => exact Submodule.smul_mem _ c ihx`. Conclude with `key z hz`.
-/
theorem restricted_generated_by_hwv (E : GLOps n K V) (h : V) :
    Submodule.span K {x : generatedSubrep E h | ∃ u ∈ Umon (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h)),
      x = u ⟨h, mem_generated_subrep_self E h⟩} = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨z, hz⟩ _
  have key : ∀ (x : V) (hx : x ∈ generatedSubrep E h), (⟨x, hx⟩ : generatedSubrep E h) ∈
      Submodule.span K {x : generatedSubrep E h | ∃ u ∈ Umon (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h)),
        x = u ⟨h, mem_generated_subrep_self E h⟩} := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u', hu', rfl⟩ := hx
      obtain ⟨u, hu, hc⟩ := enveloping_monoid_restricts E _ (generated_subrep_stable E h) u' hu'
      exact Submodule.subset_span ⟨u, hu, Subtype.ext (hc ⟨h, mem_generated_subrep_self E h⟩).symm⟩
    | zero => exact Submodule.zero_mem _
    | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
    | smul c x hx ihx => exact Submodule.smul_mem _ c ihx
  exact key z hz

/- English proof (translation)
Establish `hh'` using `(mem_highestWeight_iff E lam h).1 hh`. Establish `hrel` using `restricted_operators_gl_relation hE.1 (generatedSubrep E h) (generated_subrep_stable E h)`. Establish `hw : (⟨h, mem_generated_subrep_self E h⟩ : generatedSubrep E h) ∈ weightSp (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h)) lam` using `(restricted_weightSpace_iff E _ _ lam _).2 hh'.1`. Use `⟨⟨hrel, fun x => ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩, ?_⟩, hlam, ⟨fun hc => h0 (congrArg Subtype.val hc), hw, fun a b hab => Subtype.ext (hh'.2 a b hab)⟩, restricted_generated_by_hwv E h⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← restricted_generated_by_hwv E h]`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨u, hu, rfl⟩`. Take `⟨mu', hmu'⟩` from `enveloping_word_maps_weight hrel u hu lam _ hw`. Conclude with `Submodule.mem_iSup_of_mem mu' hmu'`.
-/
theorem generated_restriction_irreducible [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) (lam : Fin n → ℤ)
    (hlam : Dominant lam) (h : V) (hh : h ∈ highestWeightVectors E lam) (h0 : h ≠ 0) :
    IsIrrHW (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h)) lam ⟨h, mem_generated_subrep_self E h⟩ := by
  have hh' := (mem_highestWeight_iff E lam h).1 hh
  have hrel := restricted_operators_gl_relation hE.1 (generatedSubrep E h) (generated_subrep_stable E h)
  have hw : (⟨h, mem_generated_subrep_self E h⟩ : generatedSubrep E h) ∈
      weightSp (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h)) lam :=
    (restricted_weightSpace_iff E _ _ lam _).2 hh'.1
  refine ⟨⟨hrel, fun x => ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩, ?_⟩, hlam,
    ⟨fun hc => h0 (congrArg Subtype.val hc), hw, fun a b hab => Subtype.ext (hh'.2 a b hab)⟩,
    restricted_generated_by_hwv E h⟩
  rw [eq_top_iff, ← restricted_generated_by_hwv E h]
  refine Submodule.span_le.2 ?_
  rintro x ⟨u, hu, rfl⟩
  obtain ⟨mu', hmu'⟩ := enveloping_word_maps_weight hrel u hu lam _ hw
  exact Submodule.mem_iSup_of_mem mu' hmu'

end

/- English proof (translation)
Proceed by induction on `hu using Submonoid.closure_induction with`. Consider the case `mem x hx => exact hM x hx`. Consider the case `one => intro z hz`. Simplify using `using hz`. Consider the case `mul x y _ _ hx hy => intro z hz`.

Rewrite using `[Module.End.mul_apply]`. Conclude with `hx _ (hy z hz)`.
-/
theorem integral_enveloping_preserves_lattice {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {n : ℕ}
    {V : Type} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    (E : GLOps n (KK O) V) (M : Submodule O V) (hM : UZStable (O := O) E M)
    (u : Module.End (KK O) V) (hu : u ∈ UZmon E) : ∀ x ∈ M, u x ∈ M := by
  induction hu using Submonoid.closure_induction with
  | mem x hx => exact hM x hx
  | one => intro z hz; simpa using hz
  | mul x y _ _ hx hy => intro z hz; rw [Module.End.mul_apply]; exact hx _ (hy z hz)

/- English proof (translation)
Introduce `p n' O _ _ _ S hG n _ V _ _ _ _ _ E hE M hM lam hlam π hπ h hhM hhHW hh0 c y hy hyp`. Establish `hIrr` using `generated_restriction_irreducible hE lam hlam h hhHW hh0`. Establish `hT` using `(h12 p n' O S hG n lam (generatedSubrep E h) (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h)) ⟨h, mem_generated_subrep_self E h⟩ hIrr).1`. Establish `hp0 : (p : KK O) ≠ 0`. Introduce `h0`.

Apply `S.p_ne` to reduce the goal to its premises. Apply `IsFractionRing.injective O (KK O)` to reduce the goal to its premises. Rewrite using `[map_natCast, map_zero]`. Conclude with `h0`. Establish `hpc : (p : KK O) ^ c ≠ 0` using `zpow_ne_zero _ hp0`.

Establish `hx : (((p : KK O) ^ c)⁻¹ • (⟨y, hy⟩ : generatedSubrep E h)) ∈ Nabla (O` using `O) (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h)) lam ⟨h, mem_generated_subrep_self E h⟩ := by`. Introduce `u hu`. Take `⟨u', hu', hc⟩` from `integral_enveloping_lifts E _ _ u hu`. Take `⟨o, ho⟩` from `hyp u' hu'`. Use `⟨o, ?_⟩` and prove the remaining obligations.

Establish `hmem : u' y ∈ generatedSubrep E h`. Use `(u ⟨y, hy⟩).2` as an intermediate fact. Rewrite `this` using `[hc ⟨y, hy⟩]`. Then use the resulting hypothesis. Take `⟨a', ha', r, hr, hsum⟩` from `Submodule.mem_sup.1 (hB (KK O) V n E hE lam h hhHW hmem)`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 ha'`.

Establish `hker : (⨆ mu ∈ {mu : Fin n → ℤ | mu ≠ lam}, (weightSp E mu ⊓ generatedSubrep E h)) ≤ LinearMap.ker π` using `iSup₂_le fun mu hmu z hz => LinearMap.mem_ker.2 (hπ.2 mu hmu z hz.1)`. Establish `hπr : π r = 0` using `LinearMap.mem_ker.1 (hker hr)`. Establish `hπh : π h = h` using `hπ.1 h ((mem_highestWeight_iff E lam h).1 hhHW).1`. Establish `hπu : π (u' y) = a • h` using `by rw [← hsum, map_add, map_smul, hπh, hπr, add_zero]`. Establish `hr' : r = u' y - ((p : KK O) ^ c * algebraMap O (KK O) o) • h`.

Rewrite using `[← ho, hπu, ← hsum]`. Normalize the expressions using the abelian group laws. Establish `hle : (⨆ mu ∈ {mu : Fin n → ℤ | mu ≠ lam}, (weightSp E mu ⊓ generatedSubrep E h)) ≤ (otherWts (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h)) lam).map (generatedSubrep E h).subtype` using `iSup₂_le fun mu hmu z hz => ⟨⟨z, hz.2⟩, Submodule.mem_iSup_of_mem mu (Submodule.mem_iSup_of_mem hmu ((restricted_weightSpace_iff E _ _ mu _).2 hz.1)), rfl⟩`. Take `⟨w, hw, hwr⟩` from `hle hr`. Establish `hwr' : (w : V) = r` using `hwr`.

Establish `hfin : u (((p : KK O) ^ c)⁻¹ • (⟨y, hy⟩ : generatedSubrep E h)) - (algebraMap O (KK O) o) • (⟨h, mem_generated_subrep_self E h⟩ : generatedSubrep E h) = ((p : KK O) ^ c)⁻¹ • w`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[map_smul, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul, hc, hwr', hr', smul_sub, smul_smul, ← mul_assoc, inv_mul_cancel₀ hpc, one_mul]`. Rewrite using `[hfin]`. Conclude with `Submodule.smul_mem _ _ hw`.

Establish `hDel` using `hT _ hx`. Establish `hDM : ∀ w ∈ Delta (O` using `O) (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h)) (⟨h, mem_generated_subrep_self E h⟩ : generatedSubrep E h), (w : V) ∈ M := by`. Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem z hz`.

Take `⟨u, hu, rfl⟩` from `hz`. Take `⟨u', hu', hc⟩` from `integral_enveloping_lifts E _ _ u hu`. Rewrite using `[hc]`. Conclude with `integral_enveloping_preserves_lattice E M hM.1 u' hu' h hhM`. Consider the case `zero => exact M.zero_mem`.

Consider the case `add z1 z2 _ _ h1 h2 => rw [Submodule.coe_add]`. Conclude with `M.add_mem h1 h2`. Consider the case `smul o z _ hz => rw [Submodule.coe_smul_of_tower]`. Conclude with `M.smul_mem o hz`. Use `⟨_, hDM _ hDel, ?_⟩` and prove the remaining obligations.

Establish `hcoef : (p : KK O) ^ (c - ((N0 n * deF p n (ellWt lam) : ℕ) : ℤ)) * ((p : KK O) ^ (N0 n * deF p n (ellWt lam)) * ((p : KK O) ^ c)⁻¹) = 1`. Rewrite using `[zpow_sub₀ hp0, zpow_natCast]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Submodule.coe_smul_of_tower, Submodule.coe_smul, ← algebraMap_smul (KK O) ((p : O) ^ (N0 n * deF p n (ellWt lam))), smul_smul, smul_smul, map_pow, map_natCast, mul_assoc, hcoef, one_smul]`.
-/
theorem generated_lattice_corollary_of_thm (D : Formalism.BasicNotions.D7) (h12 : NablaDeltaComparisonField D) (hB : GeneratedMultipleOfHWV) : GeneratedLatticeCorollary := by
  intro p n' O _ _ _ S hG n _ V _ _ _ _ _ E hE M hM lam hlam π hπ h hhM hhHW hh0 c y hy hyp
  have hIrr := generated_restriction_irreducible hE lam hlam h hhHW hh0
  have hT := (h12 p n' O S hG n lam (generatedSubrep E h) (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h))
    ⟨h, mem_generated_subrep_self E h⟩ hIrr).1
  have hp0 : (p : KK O) ≠ 0 := by
    intro h0
    apply S.p_ne
    apply IsFractionRing.injective O (KK O)
    rw [map_natCast, map_zero]; exact h0
  have hpc : (p : KK O) ^ c ≠ 0 := zpow_ne_zero _ hp0
  have hx : (((p : KK O) ^ c)⁻¹ • (⟨y, hy⟩ : generatedSubrep E h)) ∈
      Nabla (O := O) (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h)) lam ⟨h, mem_generated_subrep_self E h⟩ := by
    intro u hu
    obtain ⟨u', hu', hc⟩ := integral_enveloping_lifts E _ _ u hu
    obtain ⟨o, ho⟩ := hyp u' hu'
    refine ⟨o, ?_⟩
    have hmem : u' y ∈ generatedSubrep E h := by
      have := (u ⟨y, hy⟩).2
      rwa [hc ⟨y, hy⟩] at this
    obtain ⟨a', ha', r, hr, hsum⟩ := Submodule.mem_sup.1 (hB (KK O) V n E hE lam h hhHW hmem)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 ha'
    have hker : (⨆ mu ∈ {mu : Fin n → ℤ | mu ≠ lam}, (weightSp E mu ⊓ generatedSubrep E h)) ≤ LinearMap.ker π :=
      iSup₂_le fun mu hmu z hz => LinearMap.mem_ker.2 (hπ.2 mu hmu z hz.1)
    have hπr : π r = 0 := LinearMap.mem_ker.1 (hker hr)
    have hπh : π h = h := hπ.1 h ((mem_highestWeight_iff E lam h).1 hhHW).1
    have hπu : π (u' y) = a • h := by rw [← hsum, map_add, map_smul, hπh, hπr, add_zero]
    have hr' : r = u' y - ((p : KK O) ^ c * algebraMap O (KK O) o) • h := by
      rw [← ho, hπu, ← hsum]; abel
    have hle : (⨆ mu ∈ {mu : Fin n → ℤ | mu ≠ lam}, (weightSp E mu ⊓ generatedSubrep E h)) ≤
        (otherWts (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h)) lam).map (generatedSubrep E h).subtype :=
      iSup₂_le fun mu hmu z hz => ⟨⟨z, hz.2⟩,
        Submodule.mem_iSup_of_mem mu (Submodule.mem_iSup_of_mem hmu ((restricted_weightSpace_iff E _ _ mu _).2 hz.1)), rfl⟩
    obtain ⟨w, hw, hwr⟩ := hle hr
    have hwr' : (w : V) = r := hwr
    have hfin : u (((p : KK O) ^ c)⁻¹ • (⟨y, hy⟩ : generatedSubrep E h)) -
        (algebraMap O (KK O) o) • (⟨h, mem_generated_subrep_self E h⟩ : generatedSubrep E h) = ((p : KK O) ^ c)⁻¹ • w := by
      apply Subtype.ext
      rw [map_smul, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul, hc, hwr', hr',
        smul_sub, smul_smul, ← mul_assoc, inv_mul_cancel₀ hpc, one_mul]
    rw [hfin]
    exact Submodule.smul_mem _ _ hw
  have hDel := hT _ hx
  have hDM : ∀ w ∈ Delta (O := O) (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h))
      (⟨h, mem_generated_subrep_self E h⟩ : generatedSubrep E h), (w : V) ∈ M := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, hu, rfl⟩ := hz
      obtain ⟨u', hu', hc⟩ := integral_enveloping_lifts E _ _ u hu
      rw [hc]
      exact integral_enveloping_preserves_lattice E M hM.1 u' hu' h hhM
    | zero => exact M.zero_mem
    | add z1 z2 _ _ h1 h2 => rw [Submodule.coe_add]; exact M.add_mem h1 h2
    | smul o z _ hz => rw [Submodule.coe_smul_of_tower]; exact M.smul_mem o hz
  refine ⟨_, hDM _ hDel, ?_⟩
  have hcoef : (p : KK O) ^ (c - ((N0 n * deF p n (ellWt lam) : ℕ) : ℤ)) *
      ((p : KK O) ^ (N0 n * deF p n (ellWt lam)) * ((p : KK O) ^ c)⁻¹) = 1 := by
    rw [zpow_sub₀ hp0, zpow_natCast]
    field_simp
  rw [Submodule.coe_smul_of_tower, Submodule.coe_smul, ← algebraMap_smul (KK O) ((p : O) ^ (N0 n * deF p n (ellWt lam))),
    smul_smul, smul_smul, map_pow, map_natCast, mul_assoc, hcoef, one_smul]

end Formalism.MainNotions.G.GLWeightTheory
