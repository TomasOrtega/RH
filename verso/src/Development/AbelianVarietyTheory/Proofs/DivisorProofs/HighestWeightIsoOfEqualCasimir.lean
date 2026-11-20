import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KHighestEqSmulOfMinusKilled
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqrtNsqLeOfAbsLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOrthSucc

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.LowGen

variable {p q : ℕ}

/- English proof (translation)
Simplify using `[hwSub, wtSub, Submodule.mem_iInf, sub_eq_zero]`.
-/
theorem mem_hwSub {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (μ : Ix p q → ℚ) (x : V) : x ∈ hwSub act μ ↔
      (∀ a, act (Eab a a) x = ((μ a : ℚ) : ℂ) • x) ∧ ∀ a b, posC a b → act (Eab a b) x = 0 := by
  simp [hwSub, wtSub, Submodule.mem_iInf, sub_eq_zero]

/- English proof (translation)
Introduce `y hy`. Rewrite `hy`, the goal using `[genSub, Submodule.mem_sInf]`. Conclude with `fun N hN => hN.2 Z y (hy N hN)`.
-/
theorem genSub_stable {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (S : Set V) (Z : Mat p q) : ∀ y ∈ genSub act S, act Z y ∈ genSub act S := by
  intro y hy
  rw [genSub, Submodule.mem_sInf] at hy ⊢
  exact fun N hN => hN.2 Z y (hy N hN)

/- English proof (translation)
Rewrite using `[genSub, Submodule.mem_sInf]`. Conclude with `fun N hN => hN.1 rfl`.
-/
theorem mem_genSub_self {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (u : V) : u ∈ genSub act {u} := by
  rw [genSub, Submodule.mem_sInf]
  exact fun N hN => hN.1 rfl

/- English proof (translation)
The claim follows from `sInf_le ⟨Set.singleton_subset_iff.2 hu, hN⟩`.
-/
theorem genSub_le {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    {u : V} {N : Submodule ℂ V} (hu : u ∈ N) (hN : ∀ Z, ∀ y ∈ N, act Z y ∈ N) : genSub act {u} ≤ N :=
  sInf_le ⟨Set.singleton_subset_iff.2 hu, hN⟩

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.FiltrationEquivalenceRelation.main`. Consider the case `exact _root_.GlobalTheory.FiltrationEquivalenceRelation.main`. Consider the case `(apply _root_.GlobalTheory.FiltrationEquivalenceRelation.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.FiltrationEquivalenceRelation.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.FiltrationEquivalenceRelation.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.FiltrationEquivalenceRelation.main ..)`.
-/
theorem gen_irred_adm {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (hlie : IsLieAct act) (ip : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (herm : ∀ x y, star (ip x y) = ip y x) (pos : ∀ x, x ≠ 0 → 0 < (ip x x).re)
    (hadj : ∀ Z x y, ip (act Z x) y = ip x (act (adjZ Z) y))
    {lam : Ix p q → ℚ} (hl : IsParam lam) (hg1 : GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1))
    (hg2 : GapGt lam (((p + q : ℕ) : ℝ) - 1)) (u : V)
    (hfin : ∃ W : Submodule ℂ V, FiniteDimensional ℂ W ∧ u ∈ W ∧ KStable act W)
    (hu : u ∈ hwSub act (blattner lam))
    (hc : casimir act u = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u) :
    (∀ Q : Submodule ℂ V, Q ≤ genSub act {u} → (∀ Z, ∀ y ∈ Q, act Z y ∈ Q) → u ∉ Q → Q = ⊥) ∧
    ∀ μ, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ ∀ x ∈ genSub act {u}, x ∈ hwSub act μ → x ∈ S := by
  first
  | exact @_root_.GlobalTheory.FiltrationEquivalenceRelation.main
  | exact _root_.GlobalTheory.FiltrationEquivalenceRelation.main
  | (apply _root_.GlobalTheory.FiltrationEquivalenceRelation.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiltrationEquivalenceRelation.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiltrationEquivalenceRelation.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiltrationEquivalenceRelation.main ..)

def prodAct {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (a' : Mat p q →ₗ[ℂ] Module.End ℂ V') :
    Mat p q →ₗ[ℂ] Module.End ℂ (V × V') where
  toFun Z := (a Z).prodMap (a' Z)
  map_add' Y Z := by ext <;> simp
  map_smul' c Z := by ext <;> simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem prodAct_apply {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (a' : Mat p q →ₗ[ℂ] Module.End ℂ V') (Z : Mat p q) (x : V × V') :
    prodAct a a' Z x = (a Z x.1, a' Z x.2) := rfl

def prodForm {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (b' : V' →ₗ⋆[ℂ] V' →ₗ[ℂ] ℂ) : (V × V') →ₗ⋆[ℂ] (V × V') →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => b x.1 y.1 + b' x.2 y.2)
    (fun x y z => by simp; ring) (fun c x y => by simp; ring) (fun x y z => by simp; ring)
    (fun c x y => by simp; ring)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem prodForm_apply {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (b' : V' →ₗ⋆[ℂ] V' →ₗ[ℂ] ℂ) (x y : V × V') :
    prodForm b b' x y = b x.1 y.1 + b' x.2 y.2 := rfl

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Conclude with `(M.pos x hx).le`.
-/
theorem ip_nonneg (M : UGKMod p q) (x : M.M.V) : 0 ≤ (M.ip x x).re := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (M.pos x hx).le

/- English proof (translation)
Use `(gen_irred_adm (prodAct M.M.act M'.M.act) ?_ (prodForm M.ip M'.ip) ?_ ?_ ?_ hl hg1 hg2 (u, u') ?_ ?_ ?_).1` and prove the remaining obligations. Introduce `X Y`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Simplify using `only [prodAct_apply, M.M.lie X Y, M'.M.lie X Y, LinearMap.sub_apply, Module.End.mul_apply]`. Both sides reduce to the same expression.

Introduce `x y`. Rewrite using `[prodForm_apply, prodForm_apply, star_add, M.herm, M'.herm]`. Introduce `x hx`. Rewrite using `[prodForm_apply, Complex.add_re]`. Establish `h1` using `ip_nonneg M x.1`.

Establish `h2` using `ip_nonneg M' x.2`. Distinguish the cases in `h : x.1 = 0`. Use `M'.pos x.2 fun h' => hx (Prod.ext h h')` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `M.pos x.1 h` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `Z x y`. Simplify using `only [prodForm_apply, prodAct_apply, M.adj, M'.adj]`. Take `⟨W, hW, huW, hst⟩` from `M.M.kfin u`. Take `⟨W', hW', huW', hst'⟩` from `M'.M.kfin u'`.

Conclude with `⟨W.prod W', Module.Finite.of_fg (Submodule.FG.prod (Submodule.FG.of_finite) (Submodule.FG.of_finite)), ⟨huW, huW'⟩, fun X hX w hw => ⟨hst X hX _ hw.1, hst' X hX _ hw.2⟩⟩`. Rewrite `hu`, `hu'`, the goal using `[mem_hwSub]`. Conclude with `⟨fun a => Prod.ext (hu.1 a) (hu'.1 a), fun a b h => Prod.ext (hu.2 a b h) (hu'.2 a b h)⟩`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Prod.smul_fst, ← hc]`.

Simplify using `[casimir, Prod.fst_sum]`. Rewrite using `[Prod.smul_snd, ← hc']`. Simplify using `[casimir, Prod.snd_sum]`.
-/
theorem diag_irred {lam : Ix p q → ℚ} (hl : IsParam lam) (hg1 : GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1))
    (hg2 : GapGt lam (((p + q : ℕ) : ℝ) - 1)) (M M' : UGKMod p q) (u : M.M.V) (u' : M'.M.V)
    (hu : u ∈ hwSub M.M.act (blattner lam)) (hu' : u' ∈ hwSub M'.M.act (blattner lam))
    (hc : casimir M.M.act u = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u)
    (hc' : casimir M'.M.act u' = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u') :
    ∀ Q : Submodule ℂ (M.M.V × M'.M.V), Q ≤ genSub (prodAct M.M.act M'.M.act) {(u, u')} →
      (∀ Z, ∀ y ∈ Q, prodAct M.M.act M'.M.act Z y ∈ Q) → (u, u') ∉ Q → Q = ⊥ := by
  refine (gen_irred_adm (prodAct M.M.act M'.M.act) ?_ (prodForm M.ip M'.ip) ?_ ?_ ?_ hl hg1 hg2 (u, u')
    ?_ ?_ ?_).1
  · intro X Y
    refine LinearMap.ext fun x => ?_
    simp only [prodAct_apply, M.M.lie X Y, M'.M.lie X Y, LinearMap.sub_apply, Module.End.mul_apply]
    rfl
  · intro x y
    rw [prodForm_apply, prodForm_apply, star_add, M.herm, M'.herm]
  · intro x hx
    rw [prodForm_apply, Complex.add_re]
    have h1 := ip_nonneg M x.1
    have h2 := ip_nonneg M' x.2
    by_cases h : x.1 = 0
    · have := M'.pos x.2 fun h' => hx (Prod.ext h h')
      linarith
    · have := M.pos x.1 h
      linarith
  · intro Z x y
    simp only [prodForm_apply, prodAct_apply, M.adj, M'.adj]
  · obtain ⟨W, hW, huW, hst⟩ := M.M.kfin u
    obtain ⟨W', hW', huW', hst'⟩ := M'.M.kfin u'
    exact ⟨W.prod W', Module.Finite.of_fg (Submodule.FG.prod (Submodule.FG.of_finite) (Submodule.FG.of_finite)), ⟨huW, huW'⟩,
      fun X hX w hw => ⟨hst X hX _ hw.1, hst' X hX _ hw.2⟩⟩
  · rw [mem_hwSub] at hu hu' ⊢
    exact ⟨fun a => Prod.ext (hu.1 a) (hu'.1 a), fun a b h => Prod.ext (hu.2 a b h) (hu'.2 a b h)⟩
  · refine Prod.ext ?_ ?_
    · rw [Prod.smul_fst, ← hc]
      simp [casimir, Prod.fst_sum]
    · rw [Prod.smul_snd, ← hc']
      simp [casimir, Prod.snd_sum]

/- English proof (translation)
Introduce `_ _ p q lam hl hg1 hg2 M M' u u' hu hu' hc hc' hirr`. Prove the components needed by the constructor for the conclusion. Use `set N := genSub (prodAct M.M.act M'.M.act) {(u, u')} with hN`. Establish `hNs` using `genSub_stable (prodAct M.M.act M'.M.act) {(u, u')}`. Establish `hw : (u, u') ∈ N` using `mem_genSub_self _ _`.

Set `π : N →ₗ[ℂ] M'.M.V` to `LinearMap.snd ℂ _ _ ∘ₗ N.subtype`. Establish `hinj : Function.Injective π`. Establish `h` using `diag_irred hl hg1 hg2 M M' u u' hu.2 hu'.2 hc hc' (N ⊓ LinearMap.ker (LinearMap.snd ℂ _ _)) inf_le_left (fun Z y hy => ⟨hNs Z y hy.1, by`. Establish `h2 : y.2 = 0` using `hy.2`. Express the relevant statement in the definitionally equal form `M'.M.act Z y.2 = 0`.

Rewrite using `[h2, map_zero]⟩) (fun h => hu'.1 h.2)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `: (x : M.M.V × M'.M.V) ∈ N ⊓ LinearMap.ker (LinearMap.snd ℂ _ _)` using `⟨x.2, hx⟩`. Rewrite `this` using `[h]`.

Conclude with `Subtype.ext this`. Establish `hsurj : Function.Surjective π`. Break down `hirr.2 (LinearMap.range π) (by` into its components or cases. Introduce and unpack `Z _ ⟨x, rfl⟩`. Conclude with `⟨⟨_, hNs Z x x.2⟩, rfl⟩) with h | h`.

Establish `: u' ∈ LinearMap.range π` using `⟨⟨_, hw⟩, rfl⟩`. Rewrite `this` using `[h]`. Conclude with `absurd this hu'.1`. Conclude with `LinearMap.range_eq_top.1 h`. Set `φ` to `LinearEquiv.ofBijective π ⟨hinj, hsurj⟩`.

Set `e : M'.M.V →ₗ[ℂ] M.M.V` to `(LinearMap.fst ℂ _ _ ∘ₗ N.subtype) ∘ₗ φ.symm.toLinearMap`. Establish `he : ∀ x : N, e (x : M.M.V × M'.M.V).2 = (x : M.M.V × M'.M.V).1` using `fun x => congrArg (fun y : N => (y : M.M.V × M'.M.V).1) (φ.symm_apply_apply x)`. Establish `heZ : ∀ Z x, e (M'.M.act Z x) = M.M.act Z (e x)`. Introduce `Z x`. Take `⟨y, rfl⟩` from `hsurj x`.

Establish `h1` using `he ⟨_, hNs Z y y.2⟩`. Establish `h2` using `he y`. Conclude with `h1.trans (congrArg (M.M.act Z) h2.symm)`. Establish `heu : e u' = u` using `he ⟨_, hw⟩`. Use `⟨e, ?_, heZ, heu, le_antisymm ?_ (genSub_le ⟨u', heu⟩ ?_)⟩` and prove the remaining obligations.

Break down `hirr.2 (LinearMap.ker e) (fun Z y hy => by` into its components or cases. Rewrite `hy`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[heZ, hy, map_zero]) with h | h`. Conclude with `LinearMap.ker_eq_bot.1 h`. Establish `: u' ∈ LinearMap.ker e` using `h ▸ Submodule.mem_top`.

Rewrite `this` using `[LinearMap.mem_ker, heu]`. Conclude with `absurd this hu.1`. Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨y, rfl⟩` from `hsurj x`. Establish `h1 : N ≤ (genSub M.M.act {u}).comap (LinearMap.fst ℂ _ _)` using `genSub_le (mem_genSub_self _ u) fun Z z hz => genSub_stable _ _ Z _ hz`.

Conclude with `(he y).symm ▸ h1 y.2`. Introduce and unpack `Z _ ⟨x, rfl⟩`. Conclude with `⟨_, heZ Z x⟩`. Introduce `μ`. Take `⟨S, hS, hS'⟩` from `(gen_irred_adm M'.M.act M'.M.lie M'.ip M'.herm M'.pos M'.adj hl hg1 hg2 u' (M'.M.kfin u') hu'.2 hc').2 μ`.

Establish `htop : genSub M'.M.act {u'} = ⊤`. Break down `hirr.2 _ (genSub_stable M'.M.act {u'}) with h | h` into its components or cases. Use `mem_genSub_self M'.M.act u'` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `absurd this hu'.1`.

Conclude with `h`. Conclude with `Submodule.finiteDimensional_of_le (S₂ := S) fun x hx => hS' x (htop ▸ Submodule.mem_top) hx`.
-/
theorem gen_iso_of_lowest_type : admQ7 → admQ8 → ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1) → GapGt lam (((p + q : ℕ) : ℝ) - 1) → ∀ (M M' : UGKMod p q) (u : M.M.V) (u' : M'.M.V), IsHW M.M.act (blattner lam) u → IsHW M'.M.act (blattner lam) u' → casimir M.M.act u = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u → casimir M'.M.act u' = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u' → IrrGK M'.M → (∃ e : M'.M.V →ₗ[ℂ] M.M.V, Function.Injective e ∧ (∀ Z x, e (M'.M.act Z x) = M.M.act Z (e x)) ∧ e u' = u ∧ LinearMap.range e = genSub M.M.act {u}) ∧ AdmGK M'.M := by
  intro _ _ p q lam hl hg1 hg2 M M' u u' hu hu' hc hc' hirr
  constructor
  · set N := genSub (prodAct M.M.act M'.M.act) {(u, u')} with hN
    have hNs := genSub_stable (prodAct M.M.act M'.M.act) {(u, u')}
    have hw : (u, u') ∈ N := mem_genSub_self _ _
    let π : N →ₗ[ℂ] M'.M.V := LinearMap.snd ℂ _ _ ∘ₗ N.subtype
    have hinj : Function.Injective π := by
      have h := diag_irred hl hg1 hg2 M M' u u' hu.2 hu'.2 hc hc' (N ⊓ LinearMap.ker (LinearMap.snd ℂ _ _))
        inf_le_left (fun Z y hy => ⟨hNs Z y hy.1, by
          have h2 : y.2 = 0 := hy.2
          change M'.M.act Z y.2 = 0
          rw [h2, map_zero]⟩) (fun h => hu'.1 h.2)
      rw [injective_iff_map_eq_zero]
      intro x hx
      have : (x : M.M.V × M'.M.V) ∈ N ⊓ LinearMap.ker (LinearMap.snd ℂ _ _) := ⟨x.2, hx⟩
      rw [h] at this
      exact Subtype.ext this
    have hsurj : Function.Surjective π := by
      rcases hirr.2 (LinearMap.range π) (by
        rintro Z _ ⟨x, rfl⟩
        exact ⟨⟨_, hNs Z x x.2⟩, rfl⟩) with h | h
      · have : u' ∈ LinearMap.range π := ⟨⟨_, hw⟩, rfl⟩
        rw [h] at this
        exact absurd this hu'.1
      · exact LinearMap.range_eq_top.1 h
    let φ := LinearEquiv.ofBijective π ⟨hinj, hsurj⟩
    let e : M'.M.V →ₗ[ℂ] M.M.V := (LinearMap.fst ℂ _ _ ∘ₗ N.subtype) ∘ₗ φ.symm.toLinearMap
    have he : ∀ x : N, e (x : M.M.V × M'.M.V).2 = (x : M.M.V × M'.M.V).1 := fun x =>
      congrArg (fun y : N => (y : M.M.V × M'.M.V).1) (φ.symm_apply_apply x)
    have heZ : ∀ Z x, e (M'.M.act Z x) = M.M.act Z (e x) := by
      intro Z x
      obtain ⟨y, rfl⟩ := hsurj x
      have h1 := he ⟨_, hNs Z y y.2⟩
      have h2 := he y
      exact h1.trans (congrArg (M.M.act Z) h2.symm)
    have heu : e u' = u := he ⟨_, hw⟩
    refine ⟨e, ?_, heZ, heu, le_antisymm ?_ (genSub_le ⟨u', heu⟩ ?_)⟩
    · rcases hirr.2 (LinearMap.ker e) (fun Z y hy => by
        rw [LinearMap.mem_ker] at hy ⊢
        rw [heZ, hy, map_zero]) with h | h
      · exact LinearMap.ker_eq_bot.1 h
      · have : u' ∈ LinearMap.ker e := h ▸ Submodule.mem_top
        rw [LinearMap.mem_ker, heu] at this
        exact absurd this hu.1
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := hsurj x
      have h1 : N ≤ (genSub M.M.act {u}).comap (LinearMap.fst ℂ _ _) :=
        genSub_le (mem_genSub_self _ u) fun Z z hz => genSub_stable _ _ Z _ hz
      exact (he y).symm ▸ h1 y.2
    · rintro Z _ ⟨x, rfl⟩
      exact ⟨_, heZ Z x⟩
  · intro μ
    obtain ⟨S, hS, hS'⟩ := (gen_irred_adm M'.M.act M'.M.lie M'.ip M'.herm M'.pos M'.adj hl hg1 hg2 u'
      (M'.M.kfin u') hu'.2 hc').2 μ
    have htop : genSub M'.M.act {u'} = ⊤ := by
      rcases hirr.2 _ (genSub_stable M'.M.act {u'}) with h | h
      · have := mem_genSub_self M'.M.act u'
        rw [h] at this
        exact absurd this hu'.1
      · exact h
    exact Submodule.finiteDimensional_of_le (S₂ := S) fun x hx => hS' x (htop ▸ Submodule.mem_top) hx

end GlobalTheory.LowGen
