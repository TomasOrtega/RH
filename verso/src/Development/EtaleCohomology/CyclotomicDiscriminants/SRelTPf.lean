import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
import Development.EtaleCohomology.CyclotomicDiscriminants.SZcTPf
import Development.EtaleCohomology.CyclotomicDiscriminants.SChainPf

noncomputable section
namespace LateralTheory.Q.SRelT
open UpperTheory.V.ZK

def Gen (M : Type) [AddCommGroup M] (r : ℕ) : Prop :=
  ∃ (F : Type) (_ : AddCommGroup F), Module.Free ℤ F ∧ Module.Finite ℤ F ∧ Module.finrank ℤ F ≤ r ∧
    ∃ f : F →+ M, Function.Surjective f

/- English proof (translation)
Take `⟨F, _, h1, h2, h3, f, hf⟩` from `h`. Conclude with `⟨F, inferInstance, h1, h2, h3, g.comp f, hg.comp hf⟩`.
-/
theorem Gen.surj {M N : Type} [AddCommGroup M] [AddCommGroup N] {r : ℕ} (h : Gen M r) (g : M →+ N)
    (hg : Function.Surjective g) : Gen N r := by
  obtain ⟨F, _, h1, h2, h3, f, hf⟩ := h
  exact ⟨F, inferInstance, h1, h2, h3, g.comp f, hg.comp hf⟩

/- English proof (translation)
Take `⟨F, _, h1, h2, h3, f, hf⟩` from `h`. Conclude with `⟨F, inferInstance, h1, h2, h3.trans hs, f, hf⟩`.
-/
theorem Gen.mono {M : Type} [AddCommGroup M] {r s : ℕ} (h : Gen M r) (hs : r ≤ s) : Gen M s := by
  obtain ⟨F, _, h1, h2, h3, f, hf⟩ := h
  exact ⟨F, inferInstance, h1, h2, h3.trans hs, f, hf⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨PUnit, inferInstance, inferInstance, inferInstance, (Module.finrank_zero_of_subsingleton).le, 0, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩`.
-/
theorem gen_zero {M : Type} [AddCommGroup M] [Subsingleton M] : Gen M 0 :=
  ⟨PUnit, inferInstance, inferInstance, inferInstance, (Module.finrank_zero_of_subsingleton).le, 0, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨ℤ, inferInstance, inferInstance, inferInstance, by simp, Int.castAddHom _, ZMod.intCast_surjective⟩`.
-/
theorem gen_zmod (q : ℕ) : Gen (ZMod q) 1 :=
  ⟨ℤ, inferInstance, inferInstance, inferInstance, by simp, Int.castAddHom _, ZMod.intCast_surjective⟩

/- English proof (translation)
Take `⟨F, _, a1, a2, a3, φ, hφ⟩` from `h1`. Take `⟨E, _, b1, b2, b3, ψ, hψ⟩` from `h3`. Set `g'` to `g.toIntLinearMap`. Set `E' : Submodule ℤ E` to `(LinearMap.range g').comap ψ.toIntLinearMap`. Set `u : E' →ₗ[ℤ] LinearMap.range g'` to `LinearMap.codRestrict _ (ψ.toIntLinearMap ∘ₗ E'.subtype) fun x => x.2`.

Take `⟨w, hw⟩` from `Module.projective_lifting_property g'.rangeRestrict u g'.surjective_rangeRestrict`. Use `⟨F × E', inferInstance, inferInstance, inferInstance, ?_, (f.comp φ).coprod w.toAddMonoidHom, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.finrank_prod]`. Use `Submodule.finrank_le E'` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Introduce `m`. Take `⟨x, hx⟩` from `hψ (g m)`. Establish `hx' : x ∈ E'` using `⟨m, hx.symm⟩`. Establish `e : g (w ⟨x, hx'⟩) = ψ x` using `congrArg Subtype.val (LinearMap.congr_fun hw ⟨x, hx'⟩)`. Take `⟨y, hy⟩` from `hfg (m - w ⟨x, hx'⟩) (by rw [map_sub, e, hx, sub_self])`.

Take `⟨z, rfl⟩` from `hφ y`. Conclude with `⟨(z, ⟨x, hx'⟩), by simp [hy]⟩`.
-/
theorem Gen.ext {M1 M2 M3 : Type} [AddCommGroup M1] [AddCommGroup M2] [AddCommGroup M3] {a b : ℕ}
    (f : M1 →+ M2) (g : M2 →+ M3) (hfg : ∀ x, g x = 0 → ∃ y, f y = x) (h1 : Gen M1 a) (h3 : Gen M3 b) :
    Gen M2 (a + b) := by
  obtain ⟨F, _, a1, a2, a3, φ, hφ⟩ := h1
  obtain ⟨E, _, b1, b2, b3, ψ, hψ⟩ := h3
  let g' := g.toIntLinearMap
  let E' : Submodule ℤ E := (LinearMap.range g').comap ψ.toIntLinearMap
  let u : E' →ₗ[ℤ] LinearMap.range g' :=
    LinearMap.codRestrict _ (ψ.toIntLinearMap ∘ₗ E'.subtype) fun x => x.2
  obtain ⟨w, hw⟩ := Module.projective_lifting_property g'.rangeRestrict u g'.surjective_rangeRestrict
  refine ⟨F × E', inferInstance, inferInstance, inferInstance, ?_, (f.comp φ).coprod w.toAddMonoidHom, ?_⟩
  · rw [Module.finrank_prod]
    have := Submodule.finrank_le E'
    omega
  · intro m
    obtain ⟨x, hx⟩ := hψ (g m)
    have hx' : x ∈ E' := ⟨m, hx.symm⟩
    have e : g (w ⟨x, hx'⟩) = ψ x := congrArg Subtype.val (LinearMap.congr_fun hw ⟨x, hx'⟩)
    obtain ⟨y, hy⟩ := hfg (m - w ⟨x, hx'⟩) (by rw [map_sub, e, hx, sub_self])
    obtain ⟨z, rfl⟩ := hφ y
    exact ⟨(z, ⟨x, hx'⟩), by simp [hy]⟩

/- English proof (translation)
Take `⟨F, _, h1, h2, h3, f, hf⟩` from `h`. Use `choose y hy using fun i => hf (x i)`. Establish `hn : ¬ LinearIndependent ℤ y` using `fun hi => by`. Use `hi.fintype_card_le_finrank` as an intermediate fact. Simplify using `at this`.

Use linear arithmetic over natural numbers and integers. Rewrite `hn` using `[Fintype.not_linearIndependent_iff]`. Take `⟨n, hn, t, ht⟩` from `hn`. Establish `key : ∀ (s : ℕ) (n : Fin (r + 1) → ℤ), (n t).natAbs = s → n t ≠ 0 → ∑ i, n i • y i = 0 → ∃ (n : Fin (r + 1) → ℤ) (t : Fin (r + 1)), ¬ (l : ℤ) ∣ n t ∧ ∑ i, n i • y i = 0`. Introduce `s`.

Proceed by induction on `s using Nat.strong_induction_on with`. Consider the case `_ s ih`. Introduce `n hs h0 hn`. Distinguish the cases in `hd : ∀ i, (l : ℤ) ∣ n i`. Use `choose m hm using hd`.

Establish `hm0 : m t ≠ 0` using `fun h => h0 (by rw [hm, h, mul_zero])`. Use `ih (m t).natAbs ?_ m rfl hm0 ?_` and prove the remaining obligations. Rewrite using `[← hs, hm, Int.natAbs_mul, Int.natAbs_natCast]`. Use `Int.natAbs_pos.2 hm0` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `: (l : ℤ) • ∑ i, m i • y i = 0`. Rewrite using `[Finset.smul_sum, ← hn]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hm, mul_smul]`. Conclude with `(smul_eq_zero.1 this).resolve_left (by omega)`. Use `push Not at hd`.

Take `⟨i, hi⟩` from `hd`. Conclude with `⟨n, i, hi, hn⟩`. Take `⟨m, t, h1, h2⟩` from `key _ n rfl ht hn`. Use `⟨m, t, h1, ?_⟩` and prove the remaining obligations. Use `congrArg f h2` as an intermediate fact.

Simplify `this` using `[map_sum, hy]`.
-/
theorem Gen.rel {M : Type} [AddCommGroup M] {r : ℕ} (h : Gen M r) (l : ℕ) (hl : 2 ≤ l) (x : Fin (r + 1) → M) :
    ∃ (n : Fin (r + 1) → ℤ) (t : Fin (r + 1)), ¬ (l : ℤ) ∣ n t ∧ ∑ i, n i • x i = 0 := by
  obtain ⟨F, _, h1, h2, h3, f, hf⟩ := h
  choose y hy using fun i => hf (x i)
  have hn : ¬ LinearIndependent ℤ y := fun hi => by
    have := hi.fintype_card_le_finrank
    simp at this
    omega
  rw [Fintype.not_linearIndependent_iff] at hn
  obtain ⟨n, hn, t, ht⟩ := hn
  have key : ∀ (s : ℕ) (n : Fin (r + 1) → ℤ), (n t).natAbs = s → n t ≠ 0 → ∑ i, n i • y i = 0 →
      ∃ (n : Fin (r + 1) → ℤ) (t : Fin (r + 1)), ¬ (l : ℤ) ∣ n t ∧ ∑ i, n i • y i = 0 := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro n hs h0 hn
      by_cases hd : ∀ i, (l : ℤ) ∣ n i
      · choose m hm using hd
        have hm0 : m t ≠ 0 := fun h => h0 (by rw [hm, h, mul_zero])
        refine ih (m t).natAbs ?_ m rfl hm0 ?_
        · rw [← hs, hm, Int.natAbs_mul, Int.natAbs_natCast]
          have := Int.natAbs_pos.2 hm0
          nlinarith
        · have : (l : ℤ) • ∑ i, m i • y i = 0 := by
            rw [Finset.smul_sum, ← hn]
            exact Finset.sum_congr rfl fun i _ => by rw [hm, mul_smul]
          exact (smul_eq_zero.1 this).resolve_left (by omega)
      · push Not at hd
        obtain ⟨i, hi⟩ := hd
        exact ⟨n, i, hi, hn⟩
  obtain ⟨m, t, h1, h2⟩ := key _ n rfl ht hn
  refine ⟨m, t, h1, ?_⟩
  have := congrArg f h2
  simpa [map_sum, hy] using this

/- English proof (translation)
Use `⟨fun j => ∑ i ∈ Finset.range j.val, F i, fun j => ?_⟩` and prove the remaining obligations. Establish `hq : ∑ i ∈ Finset.range q, F i = 0`. Rewrite using `[← hF, Finset.sum_range fun i => F i]`. Take `⟨q, rfl⟩ : ∃ p, q = p + 1` from `Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)`. Conclude with `Finset.sum_congr rfl fun i _ => congrArg F (ZMod.natCast_zmod_val (n := q + 1) i)`.

Establish `hj : ∑ i ∈ Finset.range (j + 1).val, F i = ∑ i ∈ Finset.range (j.val + 1), F i`. Establish `h1 : (j + 1).val = (j.val + 1) % q`. Rewrite using `[← ZMod.val_natCast]`. Simplify using the standard rewrite rules. Establish `h2` using `ZMod.val_lt j`.

Break down `Nat.lt_or_ge (j.val + 1) q with h | h` into its components or cases. Rewrite using `[h1, Nat.mod_eq_of_lt h]`. Establish `: j.val + 1 = q` using `by omega`. Rewrite using `[h1, this, hq]`. Simplify using the standard rewrite rules.

Simplify using `only []`. Rewrite using `[hj, Finset.sum_range_succ]`. Simplify using the standard rewrite rules.
-/
theorem exists_prim {k : Type} [CommRing k] {q : ℕ} [NeZero q] (F : ZMod q → k) (hF : ∑ j, F j = 0) :
    ∃ E : ZMod q → k, ∀ j, E (j + 1) - E j = F j := by
  refine ⟨fun j => ∑ i ∈ Finset.range j.val, F i, fun j => ?_⟩
  have hq : ∑ i ∈ Finset.range q, F i = 0 := by
    rw [← hF, Finset.sum_range fun i => F i]
    obtain ⟨q, rfl⟩ : ∃ p, q = p + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
    exact Finset.sum_congr rfl fun i _ => congrArg F (ZMod.natCast_zmod_val (n := q + 1) i)
  have hj : ∑ i ∈ Finset.range (j + 1).val, F i = ∑ i ∈ Finset.range (j.val + 1), F i := by
    have h1 : (j + 1).val = (j.val + 1) % q := by
      rw [← ZMod.val_natCast]; simp
    have h2 := ZMod.val_lt j
    rcases Nat.lt_or_ge (j.val + 1) q with h | h
    · rw [h1, Nat.mod_eq_of_lt h]
    · have : j.val + 1 = q := by omega
      rw [h1, this, hq]; simp
  simp only []
  rw [hj, Finset.sum_range_succ]; simp

open CategoryTheory Limits groupHomology

section Cat
variable {k G : Type} [CommRing k] [Group G]

/- English proof (translation)
The claim follows from `Gen.ext S.f.hom.toAddMonoidHom S.g.hom.toAddMonoidHom ((ShortComplex.moduleCat_exact_iff S).1 h) h1 h3`.
-/
theorem gen_exact (S : ShortComplex (ModuleCat k)) (h : S.Exact) {a b : ℕ} (h1 : Gen S.X₁ a) (h3 : Gen S.X₃ b) :
    Gen S.X₂ (a + b) :=
  Gen.ext S.f.hom.toAddMonoidHom S.g.hom.toAddMonoidHom ((ShortComplex.moduleCat_exact_iff S).1 h) h1 h3

/- English proof (translation)
The claim follows from `h.surj f.hom.toAddMonoidHom ((ModuleCat.epi_iff_surjective f).1 inferInstance)`.
-/
theorem gen_epi {M N : ModuleCat k} (f : M ⟶ N) [Epi f] {a : ℕ} (h : Gen M a) : Gen N a :=
  h.surj f.hom.toAddMonoidHom ((ModuleCat.epi_iff_surjective f).1 inferInstance)

/- English proof (translation)
The claim follows from `gen_exact _ (mapShortComplex₃_exact h (i := n + 1) (j := n) rfl) h1 h3`.
-/
theorem gen_les (S : ShortComplex (Rep k G)) (h : S.ShortExact) (n : ℕ) {a b : ℕ}
    (h1 : Gen (groupHomology S.X₂ (n + 1)) a) (h3 : Gen (groupHomology S.X₁ n) b) :
    Gen (groupHomology S.X₃ (n + 1)) (a + b) :=
  gen_exact _ (mapShortComplex₃_exact h (i := n + 1) (j := n) rfl) h1 h3

/- English proof (translation)
Apply `(forget₂ _ (ModuleCat k)).reflects_exact_of_faithful` to reduce the goal to its premises. Rewrite using `[ShortComplex.moduleCat_exact_iff]`. Conclude with `h`.
-/
theorem rep_exact (S : ShortComplex (Rep k G)) (h : ∀ x, S.g.hom x = 0 → ∃ y, S.f.hom y = x) : S.Exact := by
  apply (forget₂ _ (ModuleCat k)).reflects_exact_of_faithful
  rw [ShortComplex.moduleCat_exact_iff]
  exact h

/- English proof (translation)
Establish `: Epi s` using `(Rep.epi_iff_surjective s).2 hs`. Establish `: Mono i` using `(Rep.mono_iff_injective i).2 hi`. Establish `E2 : (ShortComplex.mk T s w2).Exact` using `rep_exact _ e2`. Establish `: Epi (kernel.lift s T w2)` using `E2.epi_kernelLift`. Establish `S1 : (ShortComplex.mk (kernel.ι s) s (kernel.condition s)).ShortExact` using `{ exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel s) }`.

Establish `w3 : i ≫ kernel.lift s T w2 = 0`. Rewrite using `[← cancel_mono (kernel.ι s)]`. Simplify using `[w1]`. Establish `S2 : (ShortComplex.mk i (kernel.lift s T w2) w3).ShortExact` using `{ exact := rep_exact _ fun x hx => e1 x (by`. Establish `hx' : (kernel.lift s T w2).hom x = 0` using `hx`.

Rewrite using `[← kernel.lift_ι s T w2, Rep.hom_comp]`. Simplify using `[hx']) }`. Use `⟨fun a b h1 h2 => gen_les _ S1 0 h1 ?_, fun n a b c h1 h2 h3 => gen_les _ S1 (n + 1) h1 (gen_les _ S2 n h2 h3)⟩` and prove the remaining obligations. Conclude with `gen_epi (groupHomology.map (MonoidHom.id G) (kernel.lift s T w2) 0) h2`.
-/
theorem four (A W : Rep k G) (i : A ⟶ W) (T : W ⟶ W) (s : W ⟶ A) (w1 : i ≫ T = 0) (w2 : T ≫ s = 0)
    (hi : Function.Injective i.hom) (hs : Function.Surjective s.hom)
    (e1 : ∀ x, T.hom x = 0 → ∃ y, i.hom y = x) (e2 : ∀ x, s.hom x = 0 → ∃ y, T.hom y = x) :
    (∀ a b, Gen (groupHomology W 1) a → Gen (groupHomology W 0) b → Gen (groupHomology A 1) (a + b)) ∧
    ∀ n a b c, Gen (groupHomology W (n + 2)) a → Gen (groupHomology W (n + 1)) b → Gen (groupHomology A n) c →
      Gen (groupHomology A (n + 2)) (a + (b + c)) := by
  have : Epi s := (Rep.epi_iff_surjective s).2 hs
  have : Mono i := (Rep.mono_iff_injective i).2 hi
  have E2 : (ShortComplex.mk T s w2).Exact := rep_exact _ e2
  have : Epi (kernel.lift s T w2) := E2.epi_kernelLift
  have S1 : (ShortComplex.mk (kernel.ι s) s (kernel.condition s)).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel s) }
  have w3 : i ≫ kernel.lift s T w2 = 0 := by
    rw [← cancel_mono (kernel.ι s)]; simp [w1]
  have S2 : (ShortComplex.mk i (kernel.lift s T w2) w3).ShortExact :=
    { exact := rep_exact _ fun x hx => e1 x (by
        have hx' : (kernel.lift s T w2).hom x = 0 := hx
        rw [← kernel.lift_ι s T w2, Rep.hom_comp]
        simp [hx']) }
  refine ⟨fun a b h1 h2 => gen_les _ S1 0 h1 ?_, fun n a b c h1 h2 h3 => gen_les _ S1 (n + 1) h1 (gen_les _ S2 n h2 h3)⟩
  exact gen_epi (groupHomology.map (MonoidHom.id G) (kernel.lift s T w2) 0) h2

end Cat

section Perm
variable (k : Type) [CommRing k] {G : Type} [Group G] {q : ℕ} [NeZero q] (p : G →* Multiplicative (ZMod q))

def tr : Representation k G (ZMod q → k) where
  toFun g := LinearMap.funLeft k k fun j => j + Multiplicative.toAdd (p g)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [add_assoc]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tr_apply (g : G) (F : ZMod q → k) (j : ZMod q) : tr k p g F j = F (j + Multiplicative.toAdd (p g)) := rfl

def trIso (hp : Function.Surjective p) : Rep.of (tr k p) ≅ Rep.coind p.ker.subtype (Rep.trivial k p.ker k) :=
  Rep.mkIso <| .mk (LinearEquiv.ofBijective
    (LinearMap.codRestrict (Representation.coindV p.ker.subtype (Representation.trivial k p.ker k))
      (LinearMap.funLeft k k fun h : G => Multiplicative.toAdd (p h)) fun F => (Representation.mem_coindV _ _ _).2 fun g h => by
      have : p g = 1 := g.2
      simp [this]) <| by
      constructor
      · intro F F' h
        funext j
        obtain ⟨g, hg⟩ := hp (Multiplicative.ofAdd j)
        have : F (Multiplicative.toAdd (p g)) = F' (Multiplicative.toAdd (p g)) := congrFun (congrArg Subtype.val h) g
        simpa [hg] using this
      · intro f
        choose σ hσ using hp
        refine ⟨fun j => f.1 (σ (Multiplicative.ofAdd j)), Subtype.ext (funext fun h => ?_)⟩
        have := f.2 ⟨σ (p h) * h⁻¹, by simp [MonoidHom.mem_ker, hσ]⟩ h
        show f.1 (σ (p h)) = f.1 h
        simpa using this)
    fun g => by
      refine LinearMap.ext fun F => Subtype.ext (funext fun h => ?_)
      show F (Multiplicative.toAdd (p h) + Multiplicative.toAdd (p g)) = F (Multiplicative.toAdd (p (h * g)))
      simp

/- English proof (translation)
Conclude with `gen_epi ((indIso p.ker (Rep.trivial k p.ker k) n).symm ≪≫ (functor k G n).mapIso (Rep.indCoindIso (Rep.trivial k p.ker k) ≪≫ (trIso k p hp).symm)).hom h`.
-/
theorem gen_tr [Finite G] (hp : Function.Surjective p) (n a : ℕ)
    (h : Gen (groupHomology (Rep.trivial k p.ker k) n) a) : Gen (groupHomology (Rep.of (tr k p)) n) a := by
  classical
  exact gen_epi ((indIso p.ker (Rep.trivial k p.ker k) n).symm ≪≫
    (functor k G n).mapIso (Rep.indCoindIso (Rep.trivial k p.ker k) ≪≫ (trIso k p hp).symm)).hom h

/- English proof (translation)
Set `i : k →ₗ[k] (ZMod q → k)` to `LinearMap.pi fun _ => LinearMap.id`. Set `T : (ZMod q → k) →ₗ[k] (ZMod q → k)` to `LinearMap.funLeft k k (fun j => j + 1) - LinearMap.id`. Set `s : (ZMod q → k) →ₗ[k] k` to `∑ j, LinearMap.proj j`. Establish `hs : ∀ F, s F = ∑ j, F j` using `fun F => by simp [s]`. Establish `hT : ∀ F j, T F j = F (j + 1) - F j` using `fun _ _ => rfl`.

Establish `hi : ∀ a j, i a j = a` using `fun _ _ => rfl`. Establish `hsh : ∀ (F : ZMod q → k) (c : ZMod q), ∑ j, F (j + c) = ∑ j, F j` using `fun F c => Equiv.sum_comp (Equiv.addRight c) F`. Use `four (Rep.trivial k G k) (Rep.of (tr k p)) (Rep.ofHom ⟨i, fun g => LinearMap.ext fun _ => rfl⟩) (Rep.ofHom ⟨T, fun g => LinearMap.ext fun F => funext fun j => by show T (tr k p g F) j = tr k p g (T F) j` as an intermediate fact. Simplify using `only [hT, tr_apply, add_right_comm]⟩)`. Use the proof step `(Rep.ofHom ⟨s, fun g => LinearMap.ext fun F => by show s (tr k p g F) = s F`.

Simplify using `only [hs, tr_apply, hsh]⟩)`. Use the proof step `(by`. Use extensionality with `j`. Use `show T (i 1) j = 0`. Rewrite using `[hT, hi, hi, sub_self])`.

Use the proof step `(Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun F => by show s (T F) = 0`. Simplify using `only [hs, hT, Finset.sum_sub_distrib, hsh, sub_self])))`. Use the proof step `(fun a b h => congrFun h 0)`. Use the proof step `(fun a => ⟨Pi.single 0 a, by show s (Pi.single 0 a) = a`. Simplify using `[hs]⟩)`.

Use the proof step `(fun F hF => ⟨F 0, funext fun j => by`. Establish `h1 : ∀ j, F (j + 1) = F j` using `fun j => sub_eq_zero.1 (congrFun hF j)`. Establish `h2 : ∀ m : ℕ, F m = F 0` using `fun m => by`. Proceed by induction on `m with`. Consider the case `zero => simp`.

Consider the case `succ m ih => rw [Nat.cast_succ, h1, ih]`. Use `show F 0 = F j`. Rewrite using `[← h2 j.val, ZMod.natCast_zmod_val]⟩)`. Use the proof step `(fun F hF => by`. Take `⟨E, hE⟩` from `exists_prim F ((hs F).symm.trans hF)`.

Conclude with `⟨E, funext hE⟩)`. Conclude with `⟨fun a b h1 h2 => this.1 a b (gen_tr k p hp _ _ h1) (gen_tr k p hp _ _ h2), fun n a b c h1 h2 h3 => this.2 n a b c (gen_tr k p hp _ _ h1) (gen_tr k p hp _ _ h2) h3⟩`.
-/
theorem step [Finite G] (hp : Function.Surjective p) :
    (∀ a b, Gen (groupHomology (Rep.trivial k p.ker k) 1) a → Gen (groupHomology (Rep.trivial k p.ker k) 0) b →
      Gen (groupHomology (Rep.trivial k G k) 1) (a + b)) ∧
    ∀ n a b c, Gen (groupHomology (Rep.trivial k p.ker k) (n + 2)) a →
      Gen (groupHomology (Rep.trivial k p.ker k) (n + 1)) b → Gen (groupHomology (Rep.trivial k G k) n) c →
      Gen (groupHomology (Rep.trivial k G k) (n + 2)) (a + (b + c)) := by
  let i : k →ₗ[k] (ZMod q → k) := LinearMap.pi fun _ => LinearMap.id
  let T : (ZMod q → k) →ₗ[k] (ZMod q → k) := LinearMap.funLeft k k (fun j => j + 1) - LinearMap.id
  let s : (ZMod q → k) →ₗ[k] k := ∑ j, LinearMap.proj j
  have hs : ∀ F, s F = ∑ j, F j := fun F => by simp [s]
  have hT : ∀ F j, T F j = F (j + 1) - F j := fun _ _ => rfl
  have hi : ∀ a j, i a j = a := fun _ _ => rfl
  have hsh : ∀ (F : ZMod q → k) (c : ZMod q), ∑ j, F (j + c) = ∑ j, F j := fun F c =>
    Equiv.sum_comp (Equiv.addRight c) F
  have := four (Rep.trivial k G k) (Rep.of (tr k p))
    (Rep.ofHom ⟨i, fun g => LinearMap.ext fun _ => rfl⟩)
    (Rep.ofHom ⟨T, fun g => LinearMap.ext fun F => funext fun j => by
      show T (tr k p g F) j = tr k p g (T F) j
      simp only [hT, tr_apply, add_right_comm]⟩)
    (Rep.ofHom ⟨s, fun g => LinearMap.ext fun F => by
      show s (tr k p g F) = s F
      simp only [hs, tr_apply, hsh]⟩)
    (by
      ext j
      show T (i 1) j = 0
      rw [hT, hi, hi, sub_self])
    (Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun F => by
      show s (T F) = 0
      simp only [hs, hT, Finset.sum_sub_distrib, hsh, sub_self])))
    (fun a b h => congrFun h 0)
    (fun a => ⟨Pi.single 0 a, by
      show s (Pi.single 0 a) = a
      simp [hs]⟩)
    (fun F hF => ⟨F 0, funext fun j => by
      have h1 : ∀ j, F (j + 1) = F j := fun j => sub_eq_zero.1 (congrFun hF j)
      have h2 : ∀ m : ℕ, F m = F 0 := fun m => by
        induction m with
        | zero => simp
        | succ m ih => rw [Nat.cast_succ, h1, ih]
      show F 0 = F j
      rw [← h2 j.val, ZMod.natCast_zmod_val]⟩)
    (fun F hF => by
      obtain ⟨E, hE⟩ := exists_prim F ((hs F).symm.trans hF)
      exact ⟨E, funext hE⟩)
  exact ⟨fun a b h1 h2 => this.1 a b (gen_tr k p hp _ _ h1) (gen_tr k p hp _ _ h2),
    fun n a b c h1 h2 h3 => this.2 n a b c (gen_tr k p hp _ _ h1) (gen_tr k p hp _ _ h2) h3⟩

end Perm

/- English proof (translation)
The claim follows from `gen_epi (H0IsoOfIsTrivial (Rep.trivial (ZMod r) G (ZMod r))).inv (gen_zmod r)`.
-/
theorem groupHomology_zero_zmod_trivial_rep_generated_by_one (r : ℕ) (G : Type) [Group G] : Gen (groupHomology (Rep.trivial (ZMod r) G (ZMod r)) 0) 1 :=
  gen_epi (H0IsoOfIsTrivial (Rep.trivial (ZMod r) G (ZMod r))).inv (gen_zmod r)

/- English proof (translation)
Use `ModuleCat.subsingleton_of_isZero (isZero_groupHomology_succ_of_subsingleton (Rep.trivial k G k) n)` as an intermediate fact. Conclude with `gen_zero`.
-/
theorem gen_triv (k G : Type) [CommRing k] [Group G] [Subsingleton G] (n : ℕ) :
    Gen (groupHomology (Rep.trivial k G k) (n + 1)) 0 := by
  have := ModuleCat.subsingleton_of_isZero (isZero_groupHomology_succ_of_subsingleton (Rep.trivial k G k) n)
  exact gen_zero

/- English proof (translation)
Establish `: Subsingleton p.ker`. Rewrite using `[(MonoidHom.ker_eq_bot_iff p).2 hp.1]`. Use `infer_instance`. Establish `hs` using `step (ZMod r) p hp.2`. Proceed by induction on `n using Nat.twoStepInduction with`.

Consider the case `zero => exact groupHomology_zero_zmod_trivial_rep_generated_by_one r G`. Consider the case `one => exact hs.1 0 1 (gen_triv _ _ 0) (groupHomology_zero_zmod_trivial_rep_generated_by_one r _)`. Consider the case `more n ih _ => exact hs.2 n 0 0 1 (gen_triv _ _ _) (gen_triv _ _ _) ih`.
-/
theorem gen_cyc (r : ℕ) {G : Type} [Group G] [Finite G] {q : ℕ} [NeZero q] (p : G →* Multiplicative (ZMod q))
    (hp : Function.Bijective p) (n : ℕ) : Gen (groupHomology (Rep.trivial (ZMod r) G (ZMod r)) n) 1 := by
  have : Subsingleton p.ker := by
    rw [(MonoidHom.ker_eq_bot_iff p).2 hp.1]; infer_instance
  have hs := step (ZMod r) p hp.2
  induction n using Nat.twoStepInduction with
  | zero => exact groupHomology_zero_zmod_trivial_rep_generated_by_one r G
  | one => exact hs.1 0 1 (gen_triv _ _ 0) (groupHomology_zero_zmod_trivial_rep_generated_by_one r _)
  | more n ih _ => exact hs.2 n 0 0 1 (gen_triv _ _ _) (gen_triv _ _ _) ih

/- English proof (translation)
Set `p : Cq q × Cq q →* Cq q` to `MonoidHom.fst _ _`. Establish `hp : Function.Surjective p` using `Prod.fst_surjective`. Establish `hb : Function.Bijective ((MonoidHom.snd (Cq q) (Cq q)).comp p.ker.subtype)`. Prove the components needed by the constructor for the conclusion. Introduce `x y h`.

Conclude with `Subtype.ext (Prod.ext (Eq.trans x.2 (Eq.symm y.2)) h)`. Introduce `c`. Conclude with `⟨⟨(1, c), rfl⟩, rfl⟩`. Proceed by induction on `e with`. Consider the case `zero => exact groupHomology_zero_zmod_trivial_rep_generated_by_one r _`.

Consider the case `succ e ih`. Conclude with `((step (ZMod r) p hp).2 (2 * e) 1 1 _ (gen_cyc r _ hb _) (gen_cyc r _ hb _) ih).mono (by omega)`.
-/
theorem gen_two (r q : ℕ) [NeZero q] (e : ℕ) :
    Gen (groupHomology (Rep.trivial (ZMod r) (Cq q × Cq q) (ZMod r)) (2 * e)) (2 * e + 1) := by
  let p : Cq q × Cq q →* Cq q := MonoidHom.fst _ _
  have hp : Function.Surjective p := Prod.fst_surjective
  have hb : Function.Bijective ((MonoidHom.snd (Cq q) (Cq q)).comp p.ker.subtype) := by
    constructor
    · intro x y h
      exact Subtype.ext (Prod.ext (Eq.trans x.2 (Eq.symm y.2)) h)
    · intro c
      exact ⟨⟨(1, c), rfl⟩, rfl⟩
  induction e with
  | zero => exact groupHomology_zero_zmod_trivial_rep_generated_by_one r _
  | succ e ih =>
    exact ((step (ZMod r) p hp).2 (2 * e) 1 1 _ (gen_cyc r _ hb _) (gen_cyc r _ hb _) ih).mono (by omega)

/- English proof (translation)
Rewrite using `[inhomogeneousChains.d_def]`. Establish `: (inhomogeneousChains.d (Rep.trivial k G k) m).hom = bd k G m`. Use `Finsupp.lhom_ext' fun g => LinearMap.ext_ring ?_` and prove the remaining obligations. Use `inhomogeneousChains.d_single (A := Rep.trivial k G k) m g 1` as an intermediate fact. Simplify `this` using `[bd]`.

Conclude with `LinearMap.congr_fun this z`.
-/
theorem d_eq_bd (k G : Type) [CommRing k] [Group G] (m : ℕ) (z : Ch k G (m + 1)) :
    (inhomogeneousChains (Rep.trivial k G k)).d (m + 1) m z = bd k G m z := by
  rw [inhomogeneousChains.d_def]
  have : (inhomogeneousChains.d (Rep.trivial k G k) m).hom = bd k G m := by
    refine Finsupp.lhom_ext' fun g => LinearMap.ext_ring ?_
    have := inhomogeneousChains.d_single (A := Rep.trivial k G k) m g 1
    simpa [bd] using this
  exact LinearMap.congr_fun this z

/- English proof (translation)
Set `A` to `Rep.trivial k G k`. Set `c : Fin (r + 1) → cycles A (m + 1)` to `fun t => cyclesMk (A := A) (m + 1) m (by simp) (z t) ((d_eq_bd k G m _).trans (hz t))`. Establish `hc : ∀ t, iCycles A (m + 1) (c t) = z t` using `fun t => iCycles_mk _ _ _`. Take `⟨n, t, h1, h2⟩` from `h.rel l hl fun t => π A (m + 1) (c t)`. Use `⟨n, t, h1, ?_⟩` and prove the remaining obligations.

Establish `ex` using `ShortComplex.exact_of_g_is_cokernel (ShortComplex.mk _ _ ((inhomogeneousChains A).toCycles_comp_homologyπ (m + 2) (m + 1))) ((inhomogeneousChains A).homologyIsCokernel (m + 2) (m + 1) (by simp))`. Take `⟨y, hy⟩` from `(ShortComplex.moduleCat_exact_iff _).1 ex (∑ i, n i • c i) (by`. Use `Eq.trans ?_ h2` and prove the remaining obligations. Use `show (π A (m + 1)).hom (∑ i, n i • c i) = ∑ i, n i • (π A (m + 1)).hom (c i)`. Simplify using `only [map_sum, map_zsmul])`.

Use `⟨y, ?_⟩` and prove the remaining obligations. Rewrite using `[← d_eq_bd, ← HomologicalComplex.toCycles_i]`. Establish `hy' : (toCycles A (m + 2) (m + 1)).hom y = ∑ i, n i • c i` using `hy`. Use `show (iCycles A (m + 1)).hom ((toCycles A (m + 2) (m + 1)).hom y) = _`. Rewrite using `[hy', map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, Int.cast_smul_eq_zsmul]`. Conclude with `congrArg _ (hc i)`.
-/
theorem rel_bd (k G : Type) [CommRing k] [Group G] (m r l : ℕ) (hl : 2 ≤ l)
    (h : Gen (groupHomology (Rep.trivial k G k) (m + 1)) r) (z : Fin (r + 1) → Ch k G (m + 1)) (hz : ∀ t, Cyc (z t)) :
    ∃ (n : Fin (r + 1) → ℤ) (t : Fin (r + 1)), ¬ (l : ℤ) ∣ n t ∧ Bd (∑ i, (n i : k) • z i) := by
  let A := Rep.trivial k G k
  let c : Fin (r + 1) → cycles A (m + 1) := fun t =>
    cyclesMk (A := A) (m + 1) m (by simp) (z t) ((d_eq_bd k G m _).trans (hz t))
  have hc : ∀ t, iCycles A (m + 1) (c t) = z t := fun t => iCycles_mk _ _ _
  obtain ⟨n, t, h1, h2⟩ := h.rel l hl fun t => π A (m + 1) (c t)
  refine ⟨n, t, h1, ?_⟩
  have ex := ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk _ _ ((inhomogeneousChains A).toCycles_comp_homologyπ (m + 2) (m + 1)))
    ((inhomogeneousChains A).homologyIsCokernel (m + 2) (m + 1) (by simp))
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 ex (∑ i, n i • c i) (by
    refine Eq.trans ?_ h2
    show (π A (m + 1)).hom (∑ i, n i • c i) = ∑ i, n i • (π A (m + 1)).hom (c i)
    simp only [map_sum, map_zsmul])
  refine ⟨y, ?_⟩
  rw [← d_eq_bd, ← HomologicalComplex.toCycles_i]
  have hy' : (toCycles A (m + 2) (m + 1)).hom y = ∑ i, n i • c i := hy
  show (iCycles A (m + 1)).hom ((toCycles A (m + 2) (m + 1)).hom y) = _
  rw [hy', map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Int.cast_smul_eq_zsmul]
  exact congrArg _ (hc i)

/- English proof (translation)
Introduce `l ν e hl`. Take `⟨n, t, h1, h2⟩` from `rel_bd (ZMod (l ^ ν)) (Cq (l ^ ν) × Cq (l ^ ν)) (2 * e + 1) (2 * e + 3) l hl.out.two_le (gen_two (l ^ ν) (l ^ ν) (e + 1)) (fun t => cm (ZMod (l ^ ν)) (dt (l ^ ν) t) _ (zc (l ^ ν) e)) (fun t => by`. Establish `h0 : bd _ _ _ (zc (l ^ ν) e) = 0` using `LateralTheory.Q.SZcT.SZc_of (l ^ ν) e`. Unfold `Cyc`. Rewrite using `[(LateralTheory.Q.SChainPf.SChain_of _).2.1, h0, map_zero])`.

Use `⟨fun t => (n t : ZMod (l ^ ν)), t, ?_, h2⟩` and prove the remaining obligations. Rewrite using `[ZMod.coe_int_isUnit_iff_isCoprime, Nat.cast_pow]`. Conclude with `((Nat.prime_iff_prime_int.1 hl.out).irreducible.coprime_iff_not_dvd.2 h1).pow_left`.
-/
theorem SRel_of : SRel := by
  intro l ν e hl
  obtain ⟨n, t, h1, h2⟩ := rel_bd (ZMod (l ^ ν)) (Cq (l ^ ν) × Cq (l ^ ν)) (2 * e + 1) (2 * e + 3) l hl.out.two_le
    (gen_two (l ^ ν) (l ^ ν) (e + 1))
    (fun t => cm (ZMod (l ^ ν)) (dt (l ^ ν) t) _ (zc (l ^ ν) e)) (fun t => by
      have h0 : bd _ _ _ (zc (l ^ ν) e) = 0 := LateralTheory.Q.SZcT.SZc_of (l ^ ν) e
      unfold Cyc
      rw [(LateralTheory.Q.SChainPf.SChain_of _).2.1, h0, map_zero])
  refine ⟨fun t => (n t : ZMod (l ^ ν)), t, ?_, h2⟩
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Nat.cast_pow]
  exact ((Nat.prime_iff_prime_int.1 hl.out).irreducible.coprime_iff_not_dvd.2 h1).pow_left

end LateralTheory.Q.SRelT
end
