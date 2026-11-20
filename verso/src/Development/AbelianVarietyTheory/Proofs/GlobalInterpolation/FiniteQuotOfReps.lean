import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.ChainTheta

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

section Fin

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `hk0 : Ideal.span {(k : 𝓞 E)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hk.ne'` after adjusting the coercions. Take `⟨e, B, hB, hkB⟩` from `WfDvdMonoid.max_power_factor hk0 P.irreducible`. Use `⟨e, fun j hj => ?_⟩` and prove the remaining obligations.

Establish `hB' : ¬ B ≤ P.asIdeal` using `fun h => hB (Ideal.dvd_iff_le.2 h)`. Take `⟨t, htB, htP⟩` from `SetLike.not_le_iff_exists.1 hB'`. Use `⟨t, htP, ?_⟩` and prove the remaining obligations. Establish `h1 : t * j ∈ Ideal.span {(k : 𝓞 E)}`. Rewrite using `[hkB, mul_comm t j]`.

Conclude with `Ideal.mul_mem_mul hj htB`. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton'.1 h1`. Conclude with `⟨r, by rw [← hr, mul_comm]⟩`.
-/
theorem exists_pow_loc (P : HeightOneSpectrum (𝓞 E)) (k : ℕ) (hk : 0 < k) :
    ∃ e : ℕ, ∀ j ∈ P.asIdeal ^ e, ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ ∃ r : 𝓞 E, t * j = (k : 𝓞 E) * r := by
  have hk0 : Ideal.span {(k : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hk.ne'
  obtain ⟨e, B, hB, hkB⟩ := WfDvdMonoid.max_power_factor hk0 P.irreducible
  refine ⟨e, fun j hj => ?_⟩
  have hB' : ¬ B ≤ P.asIdeal := fun h => hB (Ideal.dvd_iff_le.2 h)
  obtain ⟨t, htB, htP⟩ := SetLike.not_le_iff_exists.1 hB'
  refine ⟨t, htP, ?_⟩
  have h1 : t * j ∈ Ideal.span {(k : 𝓞 E)} := by
    rw [hkB, mul_comm t j]
    exact Ideal.mul_mem_mul hj htB
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h1
  exact ⟨r, by rw [← hr, mul_comm]⟩

/- English proof (translation)
Establish `ha : ∀ x ∈ M, ∃ m ∈ M₀, ∃ y ∈ M, x = m + (k : 𝓞 E) • y`. Introduce `x hx`. Use `choose e he using fun P : HeightOneSpectrum (𝓞 E) => exists_pow_loc P k hk`. Set `I : Ideal (𝓞 E)` to `M₀.comap (LinearMap.toSpanSingleton (𝓞 E) H x)`. Establish `hI : ∀ s : 𝓞 E, s ∈ I ↔ s • x ∈ M₀` using `fun s => by`.

Simplify using `[I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]`. Establish `hco : IsCoprime I (∏ P ∈ S, P.asIdeal ^ e P)`. Use `IsCoprime.prod_right fun P hP => IsCoprime.pow_right ?_` and prove the remaining obligations. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Assume the negation of the conclusion as `hne`.

Take `⟨s, hs, hsx⟩` from `h2 x hx P hP`. Establish `h4 : P.asIdeal = I ⊔ P.asIdeal` using `P.isMaximal.eq_of_le hne le_sup_right`. Conclude with `hs (h4 ▸ (Ideal.mem_sup_left ((hI s).2 hsx)))`. Take `⟨s, hs, j, hj, hsj⟩` from `Ideal.isCoprime_iff_exists.1 hco`. Establish `hj' : ∀ P ∈ S, j ∈ P.asIdeal ^ e P` using `fun P hP => (Finset.inf_le hP : (S.inf fun P => P.asIdeal ^ e P) ≤ _) (Ideal.prod_le_inf hj)`.

Take `⟨y, hy, hky⟩` from `h3 x hx j fun P hP => he P j (hj' P hP)`. Use `⟨s • x, (hI s).1 hs, y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[hky, ← add_smul, hsj, one_smul]`. Establish `: Module.Finite (𝓞 E) M₀` using `Module.Finite.iff_fg.2 hfg`. Establish `hk0 : Ideal.span {(k : 𝓞 E)} ≠ ⊥`.

Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hk.ne'` after adjusting the coercions. Establish `: Finite (𝓞 E ⧸ Ideal.span {(k : 𝓞 E)})` using `Ideal.finiteQuotientOfFreeOfNeBot _ hk0`. Establish `: Finite (↥M₀ ⧸ (Ideal.span {(k : 𝓞 E)} • (⊤ : Submodule (𝓞 E) ↥M₀)))` using `Submodule.finite_quotient_smul _ Module.Finite.fg_top`. Set `Q` to `↥M₀ ⧸ (Ideal.span {(k : 𝓞 E)} • (⊤ : Submodule (𝓞 E) ↥M₀))`.

Set `rep : Q → H` to `fun z => ((Function.surjInv (Submodule.Quotient.mk_surjective _) z : ↥M₀) : H)`. Use `⟨Set.range rep, Set.finite_range rep, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨m, hm, y, hy, rfl⟩` from `ha x hx`. Use `⟨rep (Submodule.Quotient.mk ⟨m, hm⟩), ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations. Take `⟨r0, hrep, h5⟩ : ∃ r0 : ↥M₀, rep (Submodule.Quotient.mk ⟨m, hm⟩) = (r0 : H) ∧ r0 - ⟨m, hm⟩ ∈ Ideal.span {(k : 𝓞 E)} • (⊤ : Submodule (𝓞 E) ↥M₀)` from `⟨_, rfl, (Submodule.Quotient.eq _).1 (Function.surjInv_eq _ _)⟩`.

Rewrite `h5` using `[Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Take `⟨w, -, hw⟩` from `h5`. Establish `h6 : rep (Submodule.Quotient.mk ⟨m, hm⟩) - m = (k : 𝓞 E) • (w : H)`. Establish `h7` using `congrArg (Subtype.val) hw`. Rewrite `h7` using `[Submodule.coe_smul, AddSubgroupClass.coe_sub]`.

Rewrite using `[hrep]`. Conclude with `h7.symm`. Use `⟨y - (w : H), M.sub_mem hy (h1 w.2), ?_⟩` and prove the remaining obligations. Rewrite using `[smul_sub, ← h6]`. Normalize the expressions using the abelian group laws.
-/
theorem semilocal_reps {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (M₀ M : Submodule (𝓞 E) H) (hfg : M₀.FG) (h1 : M₀ ≤ M)
    (h2 : ∀ x ∈ M, ∀ P ∈ S, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ M₀) (k : ℕ) (hk : 0 < k)
    (h3 : ∀ x ∈ M, ∀ j : 𝓞 E, (∀ P ∈ S, ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ ∃ r : 𝓞 E, t * j = (k : 𝓞 E) * r) →
      ∃ y ∈ M, (k : 𝓞 E) • y = j • x) :
    ∃ F : Set H, F.Finite ∧ ∀ x ∈ M, ∃ f ∈ F, ∃ y ∈ M, x = f + (k : 𝓞 E) • y := by
  classical

  have ha : ∀ x ∈ M, ∃ m ∈ M₀, ∃ y ∈ M, x = m + (k : 𝓞 E) • y := by
    intro x hx
    choose e he using fun P : HeightOneSpectrum (𝓞 E) => exists_pow_loc P k hk
    let I : Ideal (𝓞 E) := M₀.comap (LinearMap.toSpanSingleton (𝓞 E) H x)
    have hI : ∀ s : 𝓞 E, s ∈ I ↔ s • x ∈ M₀ := fun s => by
      simp [I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
    have hco : IsCoprime I (∏ P ∈ S, P.asIdeal ^ e P) := by
      refine IsCoprime.prod_right fun P hP => IsCoprime.pow_right ?_
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      obtain ⟨s, hs, hsx⟩ := h2 x hx P hP
      have h4 : P.asIdeal = I ⊔ P.asIdeal := P.isMaximal.eq_of_le hne le_sup_right
      exact hs (h4 ▸ (Ideal.mem_sup_left ((hI s).2 hsx)))
    obtain ⟨s, hs, j, hj, hsj⟩ := Ideal.isCoprime_iff_exists.1 hco
    have hj' : ∀ P ∈ S, j ∈ P.asIdeal ^ e P := fun P hP =>
      (Finset.inf_le hP : (S.inf fun P => P.asIdeal ^ e P) ≤ _) (Ideal.prod_le_inf hj)
    obtain ⟨y, hy, hky⟩ := h3 x hx j fun P hP => he P j (hj' P hP)
    refine ⟨s • x, (hI s).1 hs, y, hy, ?_⟩
    rw [hky, ← add_smul, hsj, one_smul]

  have : Module.Finite (𝓞 E) M₀ := Module.Finite.iff_fg.2 hfg
  have hk0 : Ideal.span {(k : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hk.ne'
  have : Finite (𝓞 E ⧸ Ideal.span {(k : 𝓞 E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hk0
  have : Finite (↥M₀ ⧸ (Ideal.span {(k : 𝓞 E)} • (⊤ : Submodule (𝓞 E) ↥M₀))) :=
    Submodule.finite_quotient_smul _ Module.Finite.fg_top
  let Q := ↥M₀ ⧸ (Ideal.span {(k : 𝓞 E)} • (⊤ : Submodule (𝓞 E) ↥M₀))
  let rep : Q → H := fun z => ((Function.surjInv (Submodule.Quotient.mk_surjective _) z : ↥M₀) : H)
  refine ⟨Set.range rep, Set.finite_range rep, fun x hx => ?_⟩
  obtain ⟨m, hm, y, hy, rfl⟩ := ha x hx
  refine ⟨rep (Submodule.Quotient.mk ⟨m, hm⟩), ⟨_, rfl⟩, ?_⟩
  obtain ⟨r0, hrep, h5⟩ : ∃ r0 : ↥M₀, rep (Submodule.Quotient.mk ⟨m, hm⟩) = (r0 : H) ∧
      r0 - ⟨m, hm⟩ ∈ Ideal.span {(k : 𝓞 E)} • (⊤ : Submodule (𝓞 E) ↥M₀) :=
    ⟨_, rfl, (Submodule.Quotient.eq _).1 (Function.surjInv_eq _ _)⟩
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h5
  obtain ⟨w, -, hw⟩ := h5
  have h6 : rep (Submodule.Quotient.mk ⟨m, hm⟩) - m = (k : 𝓞 E) • (w : H) := by
    have h7 := congrArg (Subtype.val) hw
    rw [Submodule.coe_smul, AddSubgroupClass.coe_sub] at h7
    rw [hrep]
    exact h7.symm
  refine ⟨y - (w : H), M.sub_mem hy (h1 w.2), ?_⟩
  rw [smul_sub, ← h6]
  abel

/- English proof (translation)
Unfold `mulLat`. Rewrite using `[Submodule.mem_map]`. Both sides reduce to the same expression.
-/
theorem mem_mulLat' {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (c : ℕ) (M : Submodule (𝓞 E) H) (w : H) :
    w ∈ mulLat c M ↔ ∃ y ∈ M, (c : 𝓞 E) • y = w := by
  unfold mulLat
  rw [Submodule.mem_map]
  rfl

/- English proof (translation)
Establish `: Finite ↥(F ∩ (M : Set H))` using `(hF.inter_of_left _).to_subtype`. Set `φ : ↥(F ∩ (M : Set H)) → (↥(mulLat c M) ⧸ (mulLat (c * k) M).comap (mulLat c M).subtype)` to `fun f => Submodule.Quotient.mk ⟨(c : 𝓞 E) • (f : H), (mem_mulLat' c M _).2 ⟨f, f.2.2, rfl⟩⟩`. Use `Finite.of_surjective φ fun z => ?_` and prove the remaining obligations. Take `⟨⟨w, hw⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Take `⟨x, hx, rfl⟩` from `(mem_mulLat' c M w).1 hw`.

Take `⟨f, hf, y, hy, hxy⟩` from `hFM x hx`. Establish `hfM : f ∈ M`. Establish `: f = x - (k : 𝓞 E) • y` using `by rw [hxy]; abel`. Rewrite using `[this]`. Conclude with `M.sub_mem hx (M.smul_mem _ hy)`.

Use `⟨⟨f, hf, hfM⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.Quotient.eq, Submodule.mem_comap]`. Use `show (c : 𝓞 E) • f - (c : 𝓞 E) • x ∈ mulLat (c * k) M`. Use `(mem_mulLat' _ M _).2 ⟨-y, M.neg_mem hy, ?_⟩` and prove the remaining obligations. Rewrite using `[hxy, Nat.cast_mul, smul_add, smul_neg, mul_smul]`.

Normalize the expressions using the abelian group laws.
-/
theorem finite_quot_of_reps {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (M : Submodule (𝓞 E) H) (c k : ℕ) (F : Set H) (hF : F.Finite)
    (hFM : ∀ x ∈ M, ∃ f ∈ F, ∃ y ∈ M, x = f + (k : 𝓞 E) • y) :
    Finite (↥(mulLat c M) ⧸ (mulLat (c * k) M).comap (mulLat c M).subtype) := by
  have : Finite ↥(F ∩ (M : Set H)) := (hF.inter_of_left _).to_subtype
  let φ : ↥(F ∩ (M : Set H)) → (↥(mulLat c M) ⧸ (mulLat (c * k) M).comap (mulLat c M).subtype) := fun f =>
    Submodule.Quotient.mk ⟨(c : 𝓞 E) • (f : H), (mem_mulLat' c M _).2 ⟨f, f.2.2, rfl⟩⟩
  refine Finite.of_surjective φ fun z => ?_
  obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨x, hx, rfl⟩ := (mem_mulLat' c M w).1 hw
  obtain ⟨f, hf, y, hy, hxy⟩ := hFM x hx
  have hfM : f ∈ M := by
    have : f = x - (k : 𝓞 E) • y := by rw [hxy]; abel
    rw [this]
    exact M.sub_mem hx (M.smul_mem _ hy)
  refine ⟨⟨f, hf, hfM⟩, ?_⟩
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  show (c : 𝓞 E) • f - (c : 𝓞 E) • x ∈ mulLat (c * k) M
  refine (mem_mulLat' _ M _).2 ⟨-y, M.neg_mem hy, ?_⟩
  rw [hxy, Nat.cast_mul, smul_add, smul_neg, mul_smul]
  abel

variable [StarRing E] {a b : ℕ}

def homG (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) : Submodule (𝓞 E) (HomE E a b) where
  carrier := {x | ∀ y ∈ N, x y ∈ N'}
  add_mem' := fun hx hx' y hy => add_mem (hx y hy) (hx' y hy)
  zero_mem' := fun _ _ => zero_mem _
  smul_mem' := fun r _ hx y hy => Submodule.smul_mem _ r (hx y hy)

/- English proof (translation)
Take `⟨G, hG⟩` from `hN.fg`. Establish `: Module.Finite (𝓞 E) ↥N'` using `Module.Finite.iff_fg.2 hN'.fg`. Set `ev : ↥(homG N N') →ₗ[𝓞 E] (↥G → ↥N')` to `{ toFun := fun x g => ⟨x.1 g.1, x.2 g.1 (hG ▸ Submodule.subset_span g.2)⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hinj : Function.Injective ev`. Introduce `x x' h`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `hspan : Submodule.span E (G : Set (Sp E a)) = ⊤`. Rewrite using `[eq_top_iff, ← hN.span_eq_top, Submodule.span_le, ← hG]`. Conclude with `fun y hy => Submodule.span_subset_span (𝓞 E) E _ hy`. Use `LinearMap.ext_on hspan fun g hg => ?_` and prove the remaining obligations.

Conclude with `congrArg Subtype.val (congrFun h ⟨g, hg⟩)`. Establish `: Module.Finite (𝓞 E) ↥(homG N N')` using `Module.Finite.of_injective ev hinj`. Conclude with `Module.Finite.iff_fg.1 this`.
-/
theorem homG_fg (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (hN : Submodule.IsLattice E N)
    (hN' : Submodule.IsLattice E N') : (homG N N').FG := by
  obtain ⟨G, hG⟩ := hN.fg
  have : Module.Finite (𝓞 E) ↥N' := Module.Finite.iff_fg.2 hN'.fg
  let ev : ↥(homG N N') →ₗ[𝓞 E] (↥G → ↥N') :=
    { toFun := fun x g => ⟨x.1 g.1, x.2 g.1 (hG ▸ Submodule.subset_span g.2)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    intro x x' h
    apply Subtype.ext
    have hspan : Submodule.span E (G : Set (Sp E a)) = ⊤ := by
      rw [eq_top_iff, ← hN.span_eq_top, Submodule.span_le, ← hG]
      exact fun y hy => Submodule.span_subset_span (𝓞 E) E _ hy
    refine LinearMap.ext_on hspan fun g hg => ?_
    exact congrArg Subtype.val (congrFun h ⟨g, hg⟩)
  have : Module.Finite (𝓞 E) ↥(homG N N') := Module.Finite.of_injective ev hinj
  exact Module.Finite.iff_fg.1 this

/- English proof (translation)
Introduce `x hx P _ y hy`. Take `⟨s, hs, hsy⟩` from `(mem_locP P N y).1 hy`. Use `(mem_locP P N' _).2 ⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.map_smul_of_tower]`. Conclude with `hx _ hsy`.
-/
theorem homG_le (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) :
    homG N N' ≤ homAt S N N' := by
  intro x hx P _ y hy
  obtain ⟨s, hs, hsy⟩ := (mem_locP P N y).1 hy
  refine (mem_locP P N' _).2 ⟨s, hs, ?_⟩
  rw [← LinearMap.map_smul_of_tower]
  exact hx _ hsy

/- English proof (translation)
Take `⟨G, hG⟩` from `hN`. Establish `h1 : ∀ g : Sp E a, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ (g ∈ G → s • x g ∈ N')`. Introduce `g`. Distinguish the cases in `hg : g ∈ G`. Take `⟨s, hs, h⟩` from `(mem_locP P N' _).1 (hx P hP g (le_locP P N (hG ▸ Submodule.subset_span hg)))`.

Conclude with `⟨s, hs, fun _ => h⟩`. Conclude with `⟨1, one_notMem P, fun h => absurd h hg⟩`. Use `choose s hs hsx using h1`. Use `⟨∏ g ∈ G, s g, fun h => ?_, ?_⟩` and prove the remaining obligations. Take `⟨g, _, hg⟩` from `(Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 h`.

Conclude with `hs g hg`. Introduce `y hy`. Rewrite `hy` using `[← hG]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem g hg`.

Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem s hg`. Use `show (∏ g ∈ G, s g) • x g ∈ N'`. Rewrite using `[hc, mul_comm, mul_smul]`. Conclude with `N'.smul_mem _ (hsx g hg)`. Consider the case `zero => rw [map_zero]`.

Conclude with `N'.zero_mem`. Consider the case `add y y' _ _ h h' => rw [map_add]`. Conclude with `N'.add_mem h h'`. Consider the case `smul r y _ h => rw [LinearMap.map_smul_of_tower]`. Conclude with `N'.smul_mem _ h`.
-/
theorem homAt_clear (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (hN : N.FG)
    (x : HomE E a b) (hx : x ∈ homAt S N N') (P : HeightOneSpectrum (𝓞 E)) (hP : P ∈ S) :
    ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ homG N N' := by
  classical
  obtain ⟨G, hG⟩ := hN
  have h1 : ∀ g : Sp E a, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ (g ∈ G → s • x g ∈ N') := by
    intro g
    by_cases hg : g ∈ G
    · obtain ⟨s, hs, h⟩ := (mem_locP P N' _).1 (hx P hP g (le_locP P N (hG ▸ Submodule.subset_span hg)))
      exact ⟨s, hs, fun _ => h⟩
    · exact ⟨1, one_notMem P, fun h => absurd h hg⟩
  choose s hs hsx using h1
  refine ⟨∏ g ∈ G, s g, fun h => ?_, ?_⟩
  · obtain ⟨g, _, hg⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 h
    exact hs g hg
  · intro y hy
    rw [← hG] at hy
    induction hy using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem s hg
      show (∏ g ∈ G, s g) • x g ∈ N'
      rw [hc, mul_comm, mul_smul]
      exact N'.smul_mem _ (hsx g hg)
    | zero => rw [map_zero]; exact N'.zero_mem
    | add y y' _ _ h h' => rw [map_add]; exact N'.add_mem h h'
    | smul r y _ h => rw [LinearMap.map_smul_of_tower]; exact N'.smul_mem _ h

/- English proof (translation)
Establish `hk0 : (k : E) ≠ 0` using `by exact_mod_cast hk.ne'`. Use `⟨(((j : 𝓞 E) : E) / (k : E)) • x, ?_, ?_⟩` and prove the remaining obligations. Introduce `P hP n hn`. Take `⟨t, ht, r, hr⟩` from `hj P hP`. Use `indexBasic_smul_locP P.asIdeal N' ht ?_` and prove the remaining obligations.

Establish `h1 : t • ((((j : 𝓞 E) : E) / (k : E)) • x) n = r • x n`. Establish `h2 : ((t : 𝓞 E) : E) * ((j : 𝓞 E) : E) = (k : E) * ((r : 𝓞 E) : E)` using `by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hr`. Rewrite using `[LinearMap.smul_apply, ← algebraMap_smul E t, ← algebraMap_smul E r, smul_smul]`. Use `congr 1`. Use `show ((t : 𝓞 E) : E) * (((j : 𝓞 E) : E) / (k : E)) = ((r : 𝓞 E) : E)`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[h2, mul_comm]`. Rewrite using `[h1]`. Conclude with `Submodule.smul_mem _ r (hx P hP n hn)`. Rewrite using `[← algebraMap_smul E (k : 𝓞 E), ← algebraMap_smul E j, smul_smul]`.

Use `congr 1`. Use `show (((k : ℕ) : 𝓞 E) : E) * (((j : 𝓞 E) : E) / (k : E)) = ((j : 𝓞 E) : E)`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem homAt_div (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (k : ℕ) (hk : 0 < k)
    (x : HomE E a b) (hx : x ∈ homAt S N N') (j : 𝓞 E)
    (hj : ∀ P ∈ S, ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ ∃ r : 𝓞 E, t * j = (k : 𝓞 E) * r) :
    ∃ y ∈ homAt S N N', (k : 𝓞 E) • y = j • x := by
  have hk0 : (k : E) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨(((j : 𝓞 E) : E) / (k : E)) • x, ?_, ?_⟩
  · intro P hP n hn
    obtain ⟨t, ht, r, hr⟩ := hj P hP
    refine indexBasic_smul_locP P.asIdeal N' ht ?_
    have h1 : t • ((((j : 𝓞 E) : E) / (k : E)) • x) n = r • x n := by
      have h2 : ((t : 𝓞 E) : E) * ((j : 𝓞 E) : E) = (k : E) * ((r : 𝓞 E) : E) := by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hr
      rw [LinearMap.smul_apply, ← algebraMap_smul E t, ← algebraMap_smul E r, smul_smul]
      congr 1
      show ((t : 𝓞 E) : E) * (((j : 𝓞 E) : E) / (k : E)) = ((r : 𝓞 E) : E)
      field_simp
      rw [h2, mul_comm]
    rw [h1]
    exact Submodule.smul_mem _ r (hx P hP n hn)
  · rw [← algebraMap_smul E (k : 𝓞 E), ← algebraMap_smul E j, smul_smul]
    congr 1
    show (((k : ℕ) : 𝓞 E) : E) * (((j : 𝓞 E) : E) / (k : E)) = ((j : 𝓞 E) : E)
    push_cast
    field_simp

/- English proof (translation)
Introduce `N N' c c' hN hN' _ hc'`. Take `⟨F, hF, hFM⟩` from `semilocal_reps Sall (homG N N') (homAt Sall N N') (homG_fg N N' hN.1 hN'.1) (homG_le Sall N N') (fun x hx P hP => homAt_clear Sall N N' hN.1.fg x hx P hP) c' hc' (fun x hx j hj => homAt_div Sall N N' c' hc' x hx j hj)`. Conclude with `finite_quot_of_reps _ c c' F hF hFM`.
-/
theorem latFin (X : Fields) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) : LatFin (X := X) a b Sall := by
  intro N N' c c' hN hN' _ hc'
  obtain ⟨F, hF, hFM⟩ := semilocal_reps Sall (homG N N') (homAt Sall N N') (homG_fg N N' hN.1 hN'.1) (homG_le Sall N N')
    (fun x hx P hP => homAt_clear Sall N N' hN.1.fg x hx P hP) c' hc' (fun x hx j hj => homAt_div Sall N N' c' hc' x hx j hj)
  exact finite_quot_of_reps _ c c' F hF hFM

end Fin

end GlobalTheory.ChainTheta
