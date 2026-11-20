import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqSumBallFn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BallFnSubMemOfRadial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BallFnMemAndOneMemOfSubMem

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix Topology
open scoped OnePoint

namespace GlobalTheory.LocGL

namespace ProjLine

section General

variable {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup X]
  [Module ℂ X] {σ : Representation ℂ G W} {π : Representation ℂ G V}

def quot (S : Subrepresentation π) : Representation ℂ G (V ⧸ S.toSubmodule) :=
  π.quotient _ fun g _ hv => S.apply_mem_toSubmodule g hv

def quotMk (S : Subrepresentation π) : π.IntertwiningMap (quot S) := ⟨S.toSubmodule.mkQ, fun _ => rfl⟩

/- English proof (translation)
Establish `ha` using `isAtom_range hσ f hf`. Use `⟨hσ, f, hf, fun S hS => (h S).elim (fun e => (ha.le_iff.1 e).resolve_left hS.1) fun e => ?_⟩` and prove the remaining obligations. Conclude with `absurd (hS.2 _ (e ▸ lt_top_iff_ne_top.2 h0)) ha.1`.
-/
theorem isSocle_of_le (hσ : σ.IsIrreducible) (f : σ.IntertwiningMap π) (hf : Function.Injective f) (h0 : f.range ≠ ⊤)
    (h : ∀ S : Subrepresentation π, S ≤ f.range ∨ S = ⊤) : IsSocle σ π := by
  have ha := isAtom_range hσ f hf
  refine ⟨hσ, f, hf, fun S hS => (h S).elim (fun e => (ha.le_iff.1 e).resolve_left hS.1) fun e => ?_⟩
  exact absurd (hS.2 _ (e ▸ lt_top_iff_ne_top.2 h0)) ha.1

/- English proof (translation)
Establish `hk : (quotMk L).ker = L` using `SetLike.ext fun v => Submodule.Quotient.mk_eq_zero _`. Use `⟨?_, quotMk L, L.toSubmodule.mkQ_surjective, fun S hS => ?_⟩` and prove the remaining obligations. Establish `h1 : L.toSubmodule ≠ ⊤` using `fun e => h0 (Subrepresentation.toSubmodule_injective e)`. Use `Submodule.Quotient.nontrivial_iff.2 h1` as an intermediate fact. Establish `: Nontrivial (Subrepresentation (quot L))` using `⟨⊥, ⊤, fun e => bot_ne_top (α := Submodule ℂ (V ⧸ L.toSubmodule)) (congrArg Subrepresentation.toSubmodule e)⟩`.

Use `⟨fun T => ?_⟩` and prove the remaining obligations. Set `T' : Subrepresentation π` to `⟨T.toSubmodule.comap L.toSubmodule.mkQ, fun g v hv => T.apply_mem_toSubmodule g hv⟩`. Use `(h T').imp (fun e => eq_bot_iff.2 fun y hy => ?_) fun e => eq_top_iff.2 fun y _ => ?_` and prove the remaining obligations. Take `⟨v, rfl⟩` from `L.toSubmodule.mkQ_surjective y`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 (e hy)`.

Take `⟨v, rfl⟩` from `L.toSubmodule.mkQ_surjective y`. Establish `: v ∈ T'` using `e ▸ trivial`. Conclude with `this`. Rewrite using `[hk]`. Conclude with `((hS.le_iff.1 ((h S).resolve_right hS.1)).resolve_left h0).symm`.
-/
theorem isCosocle_quot {L : Subrepresentation π} (h0 : L ≠ ⊤) (h : ∀ S : Subrepresentation π, S ≤ L ∨ S = ⊤) :
    IsCosocle (quot L) π := by
  have hk : (quotMk L).ker = L := SetLike.ext fun v => Submodule.Quotient.mk_eq_zero _
  refine ⟨?_, quotMk L, L.toSubmodule.mkQ_surjective, fun S hS => ?_⟩
  · have h1 : L.toSubmodule ≠ ⊤ := fun e => h0 (Subrepresentation.toSubmodule_injective e)
    have := Submodule.Quotient.nontrivial_iff.2 h1
    have : Nontrivial (Subrepresentation (quot L)) := ⟨⊥, ⊤, fun e =>
      bot_ne_top (α := Submodule ℂ (V ⧸ L.toSubmodule)) (congrArg Subrepresentation.toSubmodule e)⟩
    refine ⟨fun T => ?_⟩
    let T' : Subrepresentation π := ⟨T.toSubmodule.comap L.toSubmodule.mkQ, fun g v hv => T.apply_mem_toSubmodule g hv⟩
    refine (h T').imp (fun e => eq_bot_iff.2 fun y hy => ?_) fun e => eq_top_iff.2 fun y _ => ?_
    · obtain ⟨v, rfl⟩ := L.toSubmodule.mkQ_surjective y
      exact (Submodule.Quotient.mk_eq_zero _).2 (e hy)
    · obtain ⟨v, rfl⟩ := L.toSubmodule.mkQ_surjective y
      have : v ∈ T' := e ▸ trivial
      exact this
  · rw [hk]
    exact ((hS.le_iff.1 ((h S).resolve_right hS.1)).resolve_left h0).symm

variable [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Establish `key : ∀ (c : ℂ) g, (ofChar χ).dual g (c • LinearMap.id) = ((χ g)⁻¹ * c : ℂ) • LinearMap.id` using `fun c g => LinearMap.ext fun v => by show c • ofChar χ g⁻¹ v = _`. Simplify using `[mul_left_comm, mul_assoc]`. Set `f : (ofChar χ⁻¹).IntertwiningMap (contra (ofChar χ))` to `{ toFun := fun c => ⟨c • LinearMap.id, mem_smoothPart_of_nhds (Filter.mem_of_superset (hχ.mem_nhds (one_mem _)) fun g hg => by`. Establish `hg' : χ g = 1` using `hg`. Rewrite using `[Set.mem_ofPred_eq, key, hg']`.

Use the proof step `simp)⟩`. Use the proof step `map_add' := fun c d => Subtype.ext (add_smul _ _ _)`. Use the proof step `map_smul' := fun c d => Subtype.ext (mul_smul _ _ _)`. Use the proof step `isIntertwining' := fun g => LinearMap.ext fun c => Subtype.ext (Eq.trans (by simp) (key c g).symm) }`. Use `⟨equivOfBijective f ⟨fun c d h => ?_, fun l => ⟨l.1 1, Subtype.ext (LinearMap.ext fun v => ?_)⟩⟩⟩` and prove the remaining obligations.

Simplify `congrArg (fun l => l.1 1) h` using `[f]`. Use `show l.1 1 • v = l.1 v`. Rewrite using `[smul_eq_mul, mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]`.
-/
theorem nonempty_equiv_contra_ofChar {χ : G →* ℂˣ} (hχ : IsSmoothChar χ) :
    Nonempty ((ofChar χ⁻¹).Equiv (contra (ofChar χ))) := by
  have key : ∀ (c : ℂ) g, (ofChar χ).dual g (c • LinearMap.id) = ((χ g)⁻¹ * c : ℂ) • LinearMap.id := fun c g =>
    LinearMap.ext fun v => by
      show c • ofChar χ g⁻¹ v = _
      simp [mul_left_comm, mul_assoc]
  let f : (ofChar χ⁻¹).IntertwiningMap (contra (ofChar χ)) :=
    { toFun := fun c => ⟨c • LinearMap.id, mem_smoothPart_of_nhds (Filter.mem_of_superset (hχ.mem_nhds (one_mem _))
        fun g hg => by
          have hg' : χ g = 1 := hg
          rw [Set.mem_ofPred_eq, key, hg']
          simp)⟩
      map_add' := fun c d => Subtype.ext (add_smul _ _ _)
      map_smul' := fun c d => Subtype.ext (mul_smul _ _ _)
      isIntertwining' := fun g => LinearMap.ext fun c => Subtype.ext (Eq.trans (by simp) (key c g).symm) }
  refine ⟨equivOfBijective f ⟨fun c d h => ?_, fun l => ⟨l.1 1, Subtype.ext (LinearMap.ext fun v => ?_)⟩⟩⟩
  · simpa [f] using congrArg (fun l => l.1 1) h
  · show l.1 1 • v = l.1 v
    rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

/- English proof (translation)
Set `l : π.IntertwiningMap (ofChar χ)` to `⟨(Φ (f 1)).1, fun g => LinearMap.ext fun v => by`. Establish `h1` using `congrArg (fun y => (Φ y).1 v) (f.isIntertwining _ _ g⁻¹ 1)`. Establish `h2` using `congrArg (fun y => y.1 v) (Φ.toIntertwiningMap.isIntertwining _ _ g⁻¹ (f 1))`. Establish `h3 : ofChar χ⁻¹ g⁻¹ 1 = (χ g : ℂ) • (1 : ℂ)` using `by simp`. Simplify using `only [h3, map_smul] at h1`.

Rewrite `h2` using `[contra_apply, inv_inv]`. Conclude with `h2.symm.trans h1.symm⟩`. Establish `hl : l.toLinearMap ≠ 0` using `fun e => one_ne_zero (hf (Φ.toLinearEquiv.injective ((Subtype.ext e : Φ (f 1) = 0).trans (by simp))))`. Establish `hs : Function.Surjective l` using `LinearMap.range_eq_top.1 (Module.Dual.range_eq_top_of_ne_zero hl)`. Use `⟨isIrreducible_ofChar χ, l, hs, fun S hS => ?_⟩` and prove the remaining obligations.

Set `A : Subrepresentation (contra π)` to `⟨S.toSubmodule.dualAnnihilator.comap (smoothPart π.dual).subtype, fun g m hm => (Submodule.mem_dualAnnihilator _).2 fun v hv => (Submodule.mem_dualAnnihilator _).1 hm _ (S.apply_mem_toSubmodule g⁻¹ hv)⟩`. Establish `hA : A ≠ ⊥`. Establish `h1 : S.toSubmodule ≠ ⊤` using `fun e => hS.1 (Subrepresentation.toSubmodule_injective e)`. Use `Submodule.Quotient.nontrivial_iff.2 h1` as an intermediate fact. Take `⟨y, hy⟩` from `exists_ne (0 : V ⧸ S.toSubmodule)`.

Establish `hq : IsSmooth (quot S)` using `(IsSubquotient.of_surjective (quotMk S) S.toSubmodule.mkQ_surjective).isSmooth hπ`. Take `⟨J, hJ, hJc, hJU⟩` from `hG _ ((hq y).mem_nhds (by simp))`. Take `⟨l₀, hl₀⟩` from `Module.Projective.exists_dual_ne_zero ℂ hy`. Take `⟨m, hm, hm'⟩` from `DualAverage.exists_invariant_form G _ _ hq J hJc l₀`. Set `m' : smoothPart π.dual` to `⟨m ∘ₗ S.toSubmodule.mkQ, mem_smoothPart_of_nhds (Filter.mem_of_superset (hJ.mem_nhds (one_mem _)) fun g hg => LinearMap.ext fun v => hm _ (inv_mem hg) (S.toSubmodule.mkQ v))⟩`.

Introduce `e`. Establish `h2 : m' ∈ A` using `(Submodule.mem_dualAnnihilator _).2 fun v hv => by show m (Submodule.Quotient.mk v) = 0`. Rewrite using `[(Submodule.Quotient.mk_eq_zero _).2 hv, map_zero]`. Rewrite `h2` using `[e]`. Take `⟨v, rfl⟩` from `S.toSubmodule.mkQ_surjective y`.

Conclude with `hl₀ ((hm' _ fun g hg => hJU hg).symm.trans (congrArg (fun y => y.1 v) (show m' = 0 from h2)))`. Establish `h1 : Φ (f 1) ∈ A` using `h ((subrepIso Φ).symm A) (by simpa using hA) ⟨1, rfl⟩`. Conclude with `((hS.le_iff.1 fun v hv => (Submodule.mem_dualAnnihilator _).1 h1 v hv).resolve_left (isCoatom_ker (isIrreducible_ofChar χ) l hs).1).symm`.
-/
theorem isCosocle_of_contra [T2Space G]
    (hG : ∀ U ∈ 𝓝 (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧ IsCompact (J : Set G) ∧ (J : Set G) ⊆ U)
    (hπ : IsSmooth π) {ρ : Representation ℂ G X} (Φ : ρ.Equiv (contra π)) {χ : G →* ℂˣ}
    (f : (ofChar χ⁻¹).IntertwiningMap ρ) (hf : Function.Injective f)
    (h : ∀ S : Subrepresentation ρ, S ≠ ⊥ → f.range ≤ S) : IsCosocle (ofChar χ) π := by
  let l : π.IntertwiningMap (ofChar χ) := ⟨(Φ (f 1)).1, fun g => LinearMap.ext fun v => by
    have h1 := congrArg (fun y => (Φ y).1 v) (f.isIntertwining _ _ g⁻¹ 1)
    have h2 := congrArg (fun y => y.1 v) (Φ.toIntertwiningMap.isIntertwining _ _ g⁻¹ (f 1))
    have h3 : ofChar χ⁻¹ g⁻¹ 1 = (χ g : ℂ) • (1 : ℂ) := by simp
    simp only [h3, map_smul] at h1
    rw [contra_apply, inv_inv] at h2
    exact h2.symm.trans h1.symm⟩
  have hl : l.toLinearMap ≠ 0 := fun e => one_ne_zero (hf (Φ.toLinearEquiv.injective
    ((Subtype.ext e : Φ (f 1) = 0).trans (by simp))))
  have hs : Function.Surjective l := LinearMap.range_eq_top.1 (Module.Dual.range_eq_top_of_ne_zero hl)
  refine ⟨isIrreducible_ofChar χ, l, hs, fun S hS => ?_⟩
  let A : Subrepresentation (contra π) := ⟨S.toSubmodule.dualAnnihilator.comap (smoothPart π.dual).subtype,
    fun g m hm => (Submodule.mem_dualAnnihilator _).2 fun v hv =>
      (Submodule.mem_dualAnnihilator _).1 hm _ (S.apply_mem_toSubmodule g⁻¹ hv)⟩
  have hA : A ≠ ⊥ := by
    have h1 : S.toSubmodule ≠ ⊤ := fun e => hS.1 (Subrepresentation.toSubmodule_injective e)
    have := Submodule.Quotient.nontrivial_iff.2 h1
    obtain ⟨y, hy⟩ := exists_ne (0 : V ⧸ S.toSubmodule)
    have hq : IsSmooth (quot S) := (IsSubquotient.of_surjective (quotMk S) S.toSubmodule.mkQ_surjective).isSmooth hπ
    obtain ⟨J, hJ, hJc, hJU⟩ := hG _ ((hq y).mem_nhds (by simp))
    obtain ⟨l₀, hl₀⟩ := Module.Projective.exists_dual_ne_zero ℂ hy
    obtain ⟨m, hm, hm'⟩ := DualAverage.exists_invariant_form G _ _ hq J hJc l₀
    let m' : smoothPart π.dual := ⟨m ∘ₗ S.toSubmodule.mkQ, mem_smoothPart_of_nhds (Filter.mem_of_superset
      (hJ.mem_nhds (one_mem _)) fun g hg => LinearMap.ext fun v => hm _ (inv_mem hg) (S.toSubmodule.mkQ v))⟩
    intro e
    have h2 : m' ∈ A := (Submodule.mem_dualAnnihilator _).2 fun v hv => by
      show m (Submodule.Quotient.mk v) = 0
      rw [(Submodule.Quotient.mk_eq_zero _).2 hv, map_zero]
    rw [e] at h2
    obtain ⟨v, rfl⟩ := S.toSubmodule.mkQ_surjective y
    exact hl₀ ((hm' _ fun g hg => hJU hg).symm.trans (congrArg (fun y => y.1 v) (show m' = 0 from h2)))
  have h1 : Φ (f 1) ∈ A := h ((subrepIso Φ).symm A) (by simpa using hA) ⟨1, rfl⟩
  exact ((hS.le_iff.1 fun v hv => (Submodule.mem_dualAnnihilator _).1 h1 v hv).resolve_left
    (isCoatom_ker (isIrreducible_ofChar χ) l hs).1).symm

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨R', hR, hR'⟩ : ∃ R' : k, valuation k r ≤ valuation k R' ∧ valuation k R ≤ valuation k R'` from `(le_total (valuation k r) (valuation k R)).elim (fun h => ⟨R, h, le_rfl⟩) fun h => ⟨r, le_rfl, h⟩`. Take `⟨T, -, -, hT⟩` from `exists_eq_sum_ballFn hr hR`. Establish `h3` using `hT (F - F ∞ • fun _ => 1) (by simp) (fun x hx => by simp [hF' x (hR'.trans_lt hx)]) fun x b hb => by simp [hF x b hb]`. Establish `h4 : F - F ∞ • (fun _ => 1) ∈ S` using `h3 ▸ S.sum_mem fun a _ => S.smul_mem _ (hS.ballFn_mem one_ne_zero h1 a hr)`. Simplify using `using S.add_mem h4 (S.smul_mem (F ∞) h2)`.
-/
theorem Stable.mem_of_ballFn {S : Submodule ℂ (OnePoint k → ℂ)} (hS : Stable S) (h1 : ballFn (0 : k) 1 ∈ S)
    (h2 : (fun _ => (1 : ℂ)) ∈ S) {F : OnePoint k → ℂ} {r R : k} (hr : r ≠ 0)
    (hF : ∀ x b : k, valuation k b ≤ valuation k r → F ((x + b : k) : OnePoint k) = F x)
    (hF' : ∀ x : k, valuation k R < valuation k x → F x = F ∞) : F ∈ S := by
  obtain ⟨R', hR, hR'⟩ : ∃ R' : k, valuation k r ≤ valuation k R' ∧ valuation k R ≤ valuation k R' :=
    (le_total (valuation k r) (valuation k R)).elim (fun h => ⟨R, h, le_rfl⟩) fun h => ⟨r, le_rfl, h⟩
  obtain ⟨T, -, -, hT⟩ := exists_eq_sum_ballFn hr hR
  have h3 := hT (F - F ∞ • fun _ => 1) (by simp) (fun x hx => by simp [hF' x (hR'.trans_lt hx)])
    fun x b hb => by simp [hF x b hb]
  have h4 : F - F ∞ • (fun _ => 1) ∈ S :=
    h3 ▸ S.sum_mem fun a _ => S.smul_mem _ (hS.ballFn_mem one_ne_zero h1 a hr)
  simpa using S.add_mem h4 (S.smul_mem (F ∞) h2)

variable [DecidableEq k]

variable (k) in

def funRep : Representation ℂ (GL (Fin 2) k) (OnePoint k → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ (g⁻¹ • ·)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_smul]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem funRep_apply (g : GL (Fin 2) k) (F : OnePoint k → ℂ) (x : OnePoint k) :
    funRep k g F x = F (g⁻¹ • x) := rfl

/- English proof (translation)
Establish `h : {g | funRep k g F = F} ∈ 𝓝 (1 : GL (Fin 2) k)⁻¹` using `IsOpen.mem_nhds hF (by simp)`. Use `filter_upwards [continuous_inv.continuousAt.preimage_mem_nhds h] with g hg x`. Simplify using `using congrFun hg x`.
-/
theorem eventually_smul {F : OnePoint k → ℂ} (hF : F ∈ smoothPart (funRep k)) :
    ∀ᶠ g in 𝓝 (1 : GL (Fin 2) k), ∀ x, F (g • x) = F x := by
  have h : {g | funRep k g F = F} ∈ 𝓝 (1 : GL (Fin 2) k)⁻¹ := IsOpen.mem_nhds hF (by simp)
  filter_upwards [continuous_inv.continuousAt.preimage_mem_nhds h] with g hg x
  simpa using congrFun hg x

/- English proof (translation)
Set `u : k → GL (Fin 2) k` to `fun b => ⟨!![1, b; 0, 1], !![1, -b; 0, 1], by simp [one_fin_two], by simp [one_fin_two]⟩`. Set `l : k → GL (Fin 2) k` to `fun b => ⟨!![1, 0; b, 1], !![1, 0; -b, 1], by simp [one_fin_two], by simp [one_fin_two]⟩`. Establish `hu : Continuous u` using `Units.continuous_iff.2 ⟨(by fun_prop : Continuous fun b : k => !![1, b; 0, 1]), (by fun_prop : Continuous fun b : k => !![1, -b; 0, 1])⟩`. Establish `hl : Continuous l` using `Units.continuous_iff.2 ⟨(by fun_prop : Continuous fun b : k => !![1, 0; b, 1]), (by fun_prop : Continuous fun b : k => !![1, 0; -b, 1])⟩`. Take `⟨r, hr, h1⟩` from `exists_vball_subset ((hu.tendsto' 0 1 (Units.ext one_fin_two.symm)).eventually (eventually_smul hF))`.

Take `⟨s, hs, h2⟩` from `exists_vball_subset ((hl.tendsto' 0 1 (Units.ext one_fin_two.symm)).eventually (eventually_smul hF))`. Use `⟨⟨r, hr, fun x b hb => ?_⟩, s⁻¹, fun x hx => ?_⟩` and prove the remaining obligations. Simplify `h1 b hb x` using `[u, OnePoint.smul_some_eq_ite]`. Establish `hx0 : x ≠ 0` using `by rintro rfl; simp at hx`. Establish `h3 : valuation k x⁻¹ ≤ valuation k s`.

Rewrite `hx`, the goal using `[map_inv₀]`. Conclude with `inv_le_of_inv_le₀ (zero_lt_iff.2 (by simpa using hs)) hx.le`. Simplify `h2 _ h3 ∞` using `[l, OnePoint.smul_infty_eq_ite, hx0]`.
-/
theorem exists_radii {F : OnePoint k → ℂ} (hF : F ∈ smoothPart (funRep k)) :
    (∃ r : k, r ≠ 0 ∧ ∀ x b : k, valuation k b ≤ valuation k r → F ((x + b : k) : OnePoint k) = F x) ∧
      ∃ R : k, ∀ x : k, valuation k R < valuation k x → F x = F ∞ := by
  let u : k → GL (Fin 2) k := fun b => ⟨!![1, b; 0, 1], !![1, -b; 0, 1], by simp [one_fin_two], by simp [one_fin_two]⟩
  let l : k → GL (Fin 2) k := fun b => ⟨!![1, 0; b, 1], !![1, 0; -b, 1], by simp [one_fin_two], by simp [one_fin_two]⟩
  have hu : Continuous u := Units.continuous_iff.2
    ⟨(by fun_prop : Continuous fun b : k => !![1, b; 0, 1]), (by fun_prop : Continuous fun b : k => !![1, -b; 0, 1])⟩
  have hl : Continuous l := Units.continuous_iff.2
    ⟨(by fun_prop : Continuous fun b : k => !![1, 0; b, 1]), (by fun_prop : Continuous fun b : k => !![1, 0; -b, 1])⟩
  obtain ⟨r, hr, h1⟩ := exists_vball_subset ((hu.tendsto' 0 1 (Units.ext one_fin_two.symm)).eventually
    (eventually_smul hF))
  obtain ⟨s, hs, h2⟩ := exists_vball_subset ((hl.tendsto' 0 1 (Units.ext one_fin_two.symm)).eventually
    (eventually_smul hF))
  refine ⟨⟨r, hr, fun x b hb => ?_⟩, s⁻¹, fun x hx => ?_⟩
  · simpa [u, OnePoint.smul_some_eq_ite] using h1 b hb x
  · have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    have h3 : valuation k x⁻¹ ≤ valuation k s := by
      rw [map_inv₀] at hx ⊢
      exact inv_le_of_inv_le₀ (zero_lt_iff.2 (by simpa using hs)) hx.le
    simpa [l, OnePoint.smul_infty_eq_ite, hx0] using h2 _ h3 ∞

def funs (S : Subrepresentation (smoothRep (funRep k))) : Submodule ℂ (OnePoint k → ℂ) :=
  S.toSubmodule.map (smoothPart (funRep k)).subtype

/- English proof (translation)
Establish `key : ∀ F ∈ funs S, ∀ (g : GL (Fin 2) k) (F' : OnePoint k → ℂ), (∀ x, F' x = F (g • x)) → F' ∈ funs S`. Introduce and unpack `_ ⟨F, hF, rfl⟩ g F' h`. Conclude with `⟨_, S.apply_mem_toSubmodule g⁻¹ hF, funext fun x => ((h x).trans (by rw [← inv_inv g]; rfl)).symm⟩`. Use `⟨fun F hF a b ha F' h1 h2 => key F hF (GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, 1] (by simpa using ha)) F' fun x => ?_, fun F hF F' h1 h2 h3 => key F hF (GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp)) F' fun x => ?_⟩` and prove the remaining obligations. Proceed by induction on `x using OnePoint.rec with`.

Consider the case `infty => simp [h1, OnePoint.smul_infty_eq_ite]`. Consider the case `coe x => simp [h2, OnePoint.smul_some_eq_ite]`. Proceed by induction on `x using OnePoint.rec with`. Consider the case `infty => simp [h1, OnePoint.smul_infty_eq_ite]`. Consider the case `coe x`.

Distinguish the cases in `hx : x = 0`. Simplify using `[hx, h2, OnePoint.smul_some_eq_ite]`. Simplify using `[hx, h3, OnePoint.smul_some_eq_ite]`.
-/
theorem stable_funs (S : Subrepresentation (smoothRep (funRep k))) : Stable (funs S) := by
  have key : ∀ F ∈ funs S, ∀ (g : GL (Fin 2) k) (F' : OnePoint k → ℂ), (∀ x, F' x = F (g • x)) → F' ∈ funs S := by
    rintro _ ⟨F, hF, rfl⟩ g F' h
    exact ⟨_, S.apply_mem_toSubmodule g⁻¹ hF, funext fun x => ((h x).trans (by rw [← inv_inv g]; rfl)).symm⟩
  refine ⟨fun F hF a b ha F' h1 h2 => key F hF (GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, 1] (by simpa using ha))
    F' fun x => ?_, fun F hF F' h1 h2 h3 => key F hF (GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp))
    F' fun x => ?_⟩
  · induction x using OnePoint.rec with
    | infty => simp [h1, OnePoint.smul_infty_eq_ite]
    | coe x => simp [h2, OnePoint.smul_some_eq_ite]
  · induction x using OnePoint.rec with
    | infty => simp [h1, OnePoint.smul_infty_eq_ite]
    | coe x =>
      by_cases hx : x = 0
      · simp [hx, h2, OnePoint.smul_some_eq_ite]
      · simp [hx, h3, OnePoint.smul_some_eq_ite]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `exists_uniformizer k`. Take `⟨F₁, h1, e1⟩` from `(stable_funs S).1 F hF 1 a one_ne_zero (fun x => x.elim (F ∞) fun y => F ((1 * y + a : k) : OnePoint k)) rfl fun _ => rfl`. Set `H : Subgroup (GL (Fin 2) k)` to `KO k (Fin 2) ⊓ MulAction.stabilizer _ (∞ : OnePoint k) ⊓ MulAction.stabilizer _ ((0 : k) : OnePoint k)`. Establish `hH : ∀ g, g ∈ H ↔ g ∈ KO k (Fin 2) ∧ g.val 1 0 = 0 ∧ g.val 0 1 = 0` using `fun g => by`. Simplify using `only [H, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, OnePoint.smul_infty_eq_self_iff, and_assoc]`.

Use `and_congr_right fun _ => and_congr_right fun h => ?_` and prove the remaining obligations. Establish `h2 : g.val 1 1 ≠ 0` using `fun e => g.det_ne_zero (by simp [det_fin_two, h, e])`. Simplify using `[OnePoint.smul_some_eq_ite, h2]`. Establish `hc : IsCompact (H : Set (GL (Fin 2) k))`. Use `(SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).2` as an intermediate fact.

Use `(SplitFlip.isCompact_KO (k := k) (n := Fin 2)).inter_right ((isClosed_eq (Units.continuous_val.matrix_elem 1 0) (continuous_const (y := (0 : k)))).inter (isClosed_eq (Units.continuous_val.matrix_elem 0 1) (continuous_const (y := (0 : k))))) using 1` and compare the differences between its conclusion and the goal. Conclude with `Set.ext hH`. Establish `hs : IsSmooth S.toRepresentation` using `(IsSubquotient.of_injective (σ := S.toRepresentation) ⟨S.toSubmodule.subtype, fun _ => rfl⟩ Subtype.val_injective).isSmooth (isSmooth_smoothRep _)`. Set `ev : OnePoint k → S.toSubmodule →ₗ[ℂ] ℂ` to `fun x => LinearMap.proj x ∘ₗ (smoothPart (funRep k)).subtype ∘ₗ S.toSubmodule.subtype`. Take `⟨v, hv, e⟩` from `IwahoriOnto.exists_fixed_map_eq hs hc (ev (0 : k) - ev ∞) ⟨F₁, h1⟩ fun g hg => by show F₁.1 (g⁻¹ • _) - F₁.1 (g⁻¹ • _) = F₁.1 _ - F₁.1 _`.

Rewrite using `[(inv_mem hg).1.2, (inv_mem hg).2]`. Establish `e2 : v.1.1 (0 : k) - v.1.1 ∞ = F a - F ∞` using `e.trans (by show F₁.1 _ - F₁.1 _ = _`. Rewrite using `[show F₁.1 = _ from e1]`. Use the proof step `simp)`. Take `⟨⟨r, hr, h2⟩, h3⟩` from `exists_radii v.1.2`.

Use `Stable.ballFn_mem_and_one_mem_of_sub_mem k _ (stable_funs S) ϖ hϖ (ballFn_sub_mem_of_radial k _ (stable_funs S) v.1.1 ⟨v.1, v.2, rfl⟩ (fun u x hu => ?_) ⟨r, hr, fun x hx => by simpa using h2 0 x hx⟩ h3 (fun h => ha (by rw [← sub_eq_zero, ← e2, h, sub_self])) ϖ hϖ)` and prove the remaining obligations. Establish `hu0 : u ≠ 0` using `by rintro rfl; simp at hu`. Set `t : Fin 2 → kˣ` to `![Units.mk0 u hu0, 1]`. Apply the tactic sequence `have ht : diagT k (Fin 2) t ∈ H := (hH _).2 ⟨iwahori_le_KO k _ (diagT_mem_iwahori fun i => by fin_cases i <;> simp [t, hu]), by simp [val_diagT], by simp [val_diagT]⟩`. Establish `h4` using `congrArg (fun y => y.1.1 x) (IndDual.mem_fixed_iff.1 hv _ (inv_mem ht))`.

Use `Eq.trans (congrArg v.1.1 ?_) h4` and prove the remaining obligations. Simplify using `[OnePoint.smul_some_eq_ite, val_diagT, t]`.
-/
theorem ballFn_mem_funs {S : Subrepresentation (smoothRep (funRep k))} {F : OnePoint k → ℂ} (hF : F ∈ funs S) {a : k}
    (ha : F a ≠ F ∞) : ballFn (0 : k) 1 ∈ funs S ∧ (fun _ => (1 : ℂ)) ∈ funs S := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  obtain ⟨F₁, h1, e1⟩ := (stable_funs S).1 F hF 1 a one_ne_zero
    (fun x => x.elim (F ∞) fun y => F ((1 * y + a : k) : OnePoint k)) rfl fun _ => rfl
  let H : Subgroup (GL (Fin 2) k) := KO k (Fin 2) ⊓ MulAction.stabilizer _ (∞ : OnePoint k) ⊓
    MulAction.stabilizer _ ((0 : k) : OnePoint k)
  have hH : ∀ g, g ∈ H ↔ g ∈ KO k (Fin 2) ∧ g.val 1 0 = 0 ∧ g.val 0 1 = 0 := fun g => by
    simp only [H, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, OnePoint.smul_infty_eq_self_iff, and_assoc]
    refine and_congr_right fun _ => and_congr_right fun h => ?_
    have h2 : g.val 1 1 ≠ 0 := fun e => g.det_ne_zero (by simp [det_fin_two, h, e])
    simp [OnePoint.smul_some_eq_ite, h2]
  have hc : IsCompact (H : Set (GL (Fin 2) k)) := by
    have := (SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).2
    convert (SplitFlip.isCompact_KO (k := k) (n := Fin 2)).inter_right
      ((isClosed_eq (Units.continuous_val.matrix_elem 1 0) (continuous_const (y := (0 : k)))).inter
        (isClosed_eq (Units.continuous_val.matrix_elem 0 1) (continuous_const (y := (0 : k))))) using 1
    exact Set.ext hH
  have hs : IsSmooth S.toRepresentation := (IsSubquotient.of_injective (σ := S.toRepresentation)
    ⟨S.toSubmodule.subtype, fun _ => rfl⟩ Subtype.val_injective).isSmooth (isSmooth_smoothRep _)
  let ev : OnePoint k → S.toSubmodule →ₗ[ℂ] ℂ := fun x =>
    LinearMap.proj x ∘ₗ (smoothPart (funRep k)).subtype ∘ₗ S.toSubmodule.subtype
  obtain ⟨v, hv, e⟩ := IwahoriOnto.exists_fixed_map_eq hs hc (ev (0 : k) - ev ∞) ⟨F₁, h1⟩ fun g hg => by
    show F₁.1 (g⁻¹ • _) - F₁.1 (g⁻¹ • _) = F₁.1 _ - F₁.1 _
    rw [(inv_mem hg).1.2, (inv_mem hg).2]
  have e2 : v.1.1 (0 : k) - v.1.1 ∞ = F a - F ∞ := e.trans (by
    show F₁.1 _ - F₁.1 _ = _
    rw [show F₁.1 = _ from e1]
    simp)
  obtain ⟨⟨r, hr, h2⟩, h3⟩ := exists_radii v.1.2
  refine Stable.ballFn_mem_and_one_mem_of_sub_mem k _ (stable_funs S) ϖ hϖ (ballFn_sub_mem_of_radial k _ (stable_funs S) v.1.1 ⟨v.1, v.2, rfl⟩
    (fun u x hu => ?_) ⟨r, hr, fun x hx => by simpa using h2 0 x hx⟩ h3
    (fun h => ha (by rw [← sub_eq_zero, ← e2, h, sub_self])) ϖ hϖ)
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  let t : Fin 2 → kˣ := ![Units.mk0 u hu0, 1]
  have ht : diagT k (Fin 2) t ∈ H := (hH _).2 ⟨iwahori_le_KO k _ (diagT_mem_iwahori fun i => by
    fin_cases i <;> simp [t, hu]), by simp [val_diagT], by simp [val_diagT]⟩
  have h4 := congrArg (fun y => y.1.1 x) (IndDual.mem_fixed_iff.1 hv _ (inv_mem ht))
  refine Eq.trans (congrArg v.1.1 ?_) h4
  simp [OnePoint.smul_some_eq_ite, val_diagT, t]

/- English proof (translation)
Use `or_iff_not_imp_left.2 fun h => eq_top_iff.2 fun F _ => ?_` and prove the remaining obligations. Use `push Not at h`. Take `⟨F₀, h0, x, hx⟩` from `h`. Proceed by induction on `x using OnePoint.rec with`. Consider the case `infty => exact absurd rfl hx`.

Consider the case `coe a`. Take `⟨h1, h2⟩` from `ballFn_mem_funs ⟨F₀, h0, rfl⟩ hx`. Take `⟨⟨r, hr, h3⟩, R, h4⟩` from `exists_radii F.2`. Take `⟨F', h5, e⟩` from `(stable_funs S).mem_of_ballFn h1 h2 hr h3 h4`. Conclude with `(Subtype.ext e : F' = F) ▸ h5`.
-/
theorem const_or_eq_top (S : Subrepresentation (smoothRep (funRep k))) :
    (∀ F ∈ S, ∀ x, F.1 x = F.1 ∞) ∨ S = ⊤ := by
  refine or_iff_not_imp_left.2 fun h => eq_top_iff.2 fun F _ => ?_
  push Not at h
  obtain ⟨F₀, h0, x, hx⟩ := h
  induction x using OnePoint.rec with
  | infty => exact absurd rfl hx
  | coe a =>
    obtain ⟨h1, h2⟩ := ballFn_mem_funs ⟨F₀, h0, rfl⟩ hx
    obtain ⟨⟨r, hr, h3⟩, R, h4⟩ := exists_radii F.2
    obtain ⟨F', h5, e⟩ := (stable_funs S).mem_of_ballFn h1 h2 hr h3 h4
    exact (Subtype.ext e : F' = F) ▸ h5

/- English proof (translation)
Use `(SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).2` as an intermediate fact. Take `⟨J, hJ, hU, -⟩` from `exists_open_normalised_subgroup_subset k (Fin 2) {g | g.val 0 0 ≠ 0} ((isOpen_ne_fun (Units.continuous_val.matrix_elem 0 0) continuous_const).mem_nhds (by simp))`. Set `F : OnePoint k → ℂ` to `fun x => if x ∈ MulAction.orbit J (∞ : OnePoint k) then 1 else 0`. Establish `hF : F ∈ smoothPart (funRep k)` using `mem_smoothPart_of_nhds (Filter.mem_of_superset (hJ.mem_nhds (one_mem _)) fun g hg => funext fun x => if_congr (Set.mem_smul_set_iff_inv_smul_mem.symm.trans (Set.ext_iff.1 (MulAction.smul_orbit (⟨g, hg⟩ : J) (∞ : OnePoint k)) x)) rfl rfl)`. Establish `h0 : F (0 : k) ≠ F ∞`.

Simplify using `only [F, MulAction.mem_orbit_self, if_true]`. Rewrite using `[if_neg]`. Conclude with `zero_ne_one`. Introduce and unpack `⟨g, hg⟩`. Establish `h1 : g.1.val 0 0 ≠ 0` using `hU g.2`.

Establish `h2 : g.1 • (∞ : OnePoint k) = (0 : k)` using `hg`. Rewrite `h2` using `[OnePoint.smul_infty_eq_ite]`. Apply the tactic sequence `split_ifs at h2 with h <;> simp_all`. Take `⟨E, -, e⟩` from `(stable_funs ⊤).ballFn_mem one_ne_zero (ballFn_mem_funs (S := ⊤) ⟨⟨F, hF⟩, trivial, rfl⟩ h0).1 a hr`. Conclude with `e ▸ E.2`.
-/
theorem ballFn_mem_smoothPart (a : k) {r : k} (hr : r ≠ 0) : ballFn a r ∈ smoothPart (funRep k) := by
  classical
  have := (SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).2
  obtain ⟨J, hJ, hU, -⟩ := exists_open_normalised_subgroup_subset k (Fin 2) {g | g.val 0 0 ≠ 0}
    ((isOpen_ne_fun (Units.continuous_val.matrix_elem 0 0) continuous_const).mem_nhds (by simp))
  let F : OnePoint k → ℂ := fun x => if x ∈ MulAction.orbit J (∞ : OnePoint k) then 1 else 0
  have hF : F ∈ smoothPart (funRep k) := mem_smoothPart_of_nhds (Filter.mem_of_superset (hJ.mem_nhds (one_mem _))
    fun g hg => funext fun x => if_congr (Set.mem_smul_set_iff_inv_smul_mem.symm.trans
      (Set.ext_iff.1 (MulAction.smul_orbit (⟨g, hg⟩ : J) (∞ : OnePoint k)) x)) rfl rfl)
  have h0 : F (0 : k) ≠ F ∞ := by
    simp only [F, MulAction.mem_orbit_self, if_true]
    rw [if_neg]
    · exact zero_ne_one
    · rintro ⟨g, hg⟩
      have h1 : g.1.val 0 0 ≠ 0 := hU g.2
      have h2 : g.1 • (∞ : OnePoint k) = (0 : k) := hg
      rw [OnePoint.smul_infty_eq_ite] at h2
      split_ifs at h2 with h <;> simp_all
  obtain ⟨E, -, e⟩ := (stable_funs ⊤).ballFn_mem one_ne_zero
    (ballFn_mem_funs (S := ⊤) ⟨⟨F, hF⟩, trivial, rfl⟩ h0).1 a hr
  exact e ▸ E.2

def pts : (Σ _ : Fin 2, Fin 1) ≃ Fin 2 := stdBlocks (fun _ => 1) (by simp)

/- English proof (translation)
The claim follows from `Fin.ext ((stdBlocks_val (fun _ => 1) _ a i).trans (by simp))`.
-/
theorem pts_apply (a : Fin 2) (i : Fin 1) : pts ⟨a, i⟩ = a :=
  Fin.ext ((stdBlocks_val (fun _ => 1) _ a i).trans (by simp))

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Rewrite using `[OnePoint.smul_infty_eq_self_iff, mem_parab_iff]`. Simplify using `only [pts_apply]`. Use `⟨fun h => h 1 0 0 0 (by simp), fun h a b _ _ hab => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp at hab`. Conclude with `h`.
-/
theorem mem_parab_pts {g : GL (Fin 2) k} : g ∈ parab k pts ↔ g • (∞ : OnePoint k) = ∞ := by
  rw [OnePoint.smul_infty_eq_self_iff, mem_parab_iff]
  simp only [pts_apply]
  refine ⟨fun h => h 1 0 0 0 (by simp), fun h a b _ _ hab => ?_⟩
  fin_cases a <;> fin_cases b <;> simp at hab
  exact h

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Proceed by induction on `x using OnePoint.rec with`. Consider the case `infty => exact ⟨1, by simp⟩`. Consider the case `coe x => exact ⟨(GeneralLinearGroup.mkOfDetNeZero !![x, 1; 1, 0] (by simp))⁻¹, by simp [OnePoint.smul_infty_eq_ite]⟩`.
-/
theorem exists_smul_infty (x : OnePoint k) : ∃ g : GL (Fin 2) k, g⁻¹ • (∞ : OnePoint k) = x := by
  induction x using OnePoint.rec with
  | infty => exact ⟨1, by simp⟩
  | coe x => exact ⟨(GeneralLinearGroup.mkOfDetNeZero !![x, 1; 1, 0] (by simp))⁻¹, by simp [OnePoint.smul_infty_eq_ite]⟩

omit [DecidableEq k] in

/- English proof (translation)
Establish `: GeneralLinearGroup.det (leviEmb k pts (leviProj k pts p)) = GeneralLinearGroup.det (p : GL (Fin 2) k)` using `by rw [det_leviEmb, det_parab]`. Simplify using `[detLevi, this, mul_assoc, mul_left_comm (deltaHalf k _ (leviProj k pts p) : ℂ)]`.
-/
theorem law_detLevi (η : kˣ →* ℂˣ) (p : parab k pts) (c : ℂ) :
    twist (ofChar (detLevi pts η)) (deltaHalf k _) (leviProj k pts p) c = (detChar (Fin 2) η p : ℂ) * c := by
  have : GeneralLinearGroup.det (leviEmb k pts (leviProj k pts p)) =
      GeneralLinearGroup.det (p : GL (Fin 2) k) := by rw [det_leviEmb, det_parab]
  simp [detLevi, this, mul_assoc, mul_left_comm (deltaHalf k _ (leviProj k pts p) : ℂ)]

/- English proof (translation)
Establish `hU : ∀ᶠ g in 𝓝 (1 : GL (Fin 2) k), detChar (Fin 2) η g = 1` using `hη.detChar.mem_nhds (one_mem _)`. Set `f : (twist (smoothRep (funRep k)) (detChar _ η)).IntertwiningMap (parInd pts (ofChar (detLevi pts η)))` to `{ toFun := fun F => ⟨⟨fun g => (detChar (Fin 2) η g : ℂ) * F.1 (g⁻¹ • ∞), fun p g => by`. Use `Eq.trans ?_ (law_detLevi η p _).symm` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[_root_.mul_inv_rev, mul_smul, mem_parab_pts.1 (inv_mem p.2), map_mul, Units.val_mul, mul_assoc]⟩,`.

Use `mem_smoothPart_of_nhds (by filter_upwards [hU, IsOpen.mem_nhds F.2 (by simp)] with g h1 h2`. Use `Subtype.ext (funext fun x => ?_)` and prove the remaining obligations. Use `show (detChar (Fin 2) η (x * g) : ℂ) * F.1 ((x * g)⁻¹ • ∞) = (detChar (Fin 2) η x : ℂ) * F.1 (x⁻¹ • ∞)`. Rewrite using `[map_mul, h1, mul_one, _root_.mul_inv_rev, mul_smul]`. Conclude with `congrArg _ (congrFun h2 _))⟩`.

Use the proof step `map_add' := fun F F' => Subtype.ext (Subtype.ext (funext fun x => mul_add _ _ _))`. Use the proof step `map_smul' := fun c F => Subtype.ext (Subtype.ext (funext fun x => mul_left_comm _ _ _))`. Use the proof step `isIntertwining' := fun g => LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => by show (detChar (Fin 2) η x : ℂ) * ((detChar (Fin 2) η g : ℂ) * F.1 (g⁻¹ • x⁻¹ • ∞)) = (detChar (Fin 2) η (x * g) : ℂ) * F.1 ((x * g)⁻¹ • ∞)`. Rewrite using `[map_mul, _root_.mul_inv_rev, mul_smul, Units.val_mul, mul_assoc])) }`. Use `⟨equivOfBijective f ⟨(injective_iff_map_eq_zero _).2 fun F h => Subtype.ext (funext fun x => ?_), fun φ => ?_⟩⟩` and prove the remaining obligations.

Take `⟨g, rfl⟩` from `exists_smul_infty x`. Conclude with `(mul_eq_zero.1 (congrArg (fun φ => φ.1.1 g) h)).resolve_left (Units.ne_zero _)`. Use `choose s hs using exists_smul_infty (k := k)`. Set `F : OnePoint k → ℂ` to `fun x => (detChar (Fin 2) η (s x) : ℂ)⁻¹ * φ.1.1 (s x)`. Establish `hF : ∀ g : GL (Fin 2) k, F (g⁻¹ • ∞) = (detChar (Fin 2) η g : ℂ)⁻¹ * φ.1.1 g` using `fun g => by`.

Establish `h1 : s (g⁻¹ • ∞) * g⁻¹ ∈ parab k pts` using `mem_parab_pts.2 (by`. Rewrite using `[mul_smul, smul_eq_iff_eq_inv_smul, hs])`. Establish `h2` using `(φ.1.2 ⟨_, h1⟩ g).trans (law_detLevi η _ _)`. Simplify using `only [inv_mul_cancel_right, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val] at h2`. Simplify using `only [F, h2]`.

Clear the denominators using the available nonvanishing facts. Use `⟨⟨F, mem_smoothPart_of_nhds ?_⟩, Subtype.ext (Subtype.ext (funext fun g => ?_))⟩` and prove the remaining obligations. Use `filter_upwards [hU, IsOpen.mem_nhds φ.2 (by simp)] with g h1 h2`. Use function extensionality and compare the values at `x`. Take `⟨y, rfl⟩` from `exists_smul_infty x`.

Rewrite using `[funRep_apply, ← mul_smul, ← _root_.mul_inv_rev, hF, hF, map_mul, h1, mul_one]`. Conclude with `congrArg _ (congrArg (fun φ => φ.1 y) h2)`. Use `show (detChar (Fin 2) η g : ℂ) * F (g⁻¹ • ∞) = _`. Rewrite using `[hF, mul_inv_cancel_left₀ (Units.ne_zero _)]`.
-/
theorem nonempty_equiv_parInd {η : kˣ →* ℂˣ} (hη : IsSmoothChar η) :
    Nonempty ((twist (smoothRep (funRep k)) (detChar _ η)).Equiv (parInd pts (ofChar (detLevi pts η)))) := by
  have hU : ∀ᶠ g in 𝓝 (1 : GL (Fin 2) k), detChar (Fin 2) η g = 1 := hη.detChar.mem_nhds (one_mem _)
  let f : (twist (smoothRep (funRep k)) (detChar _ η)).IntertwiningMap (parInd pts (ofChar (detLevi pts η))) :=
    { toFun := fun F => ⟨⟨fun g => (detChar (Fin 2) η g : ℂ) * F.1 (g⁻¹ • ∞), fun p g => by
          refine Eq.trans ?_ (law_detLevi η p _).symm
          beta_reduce
          rw [_root_.mul_inv_rev, mul_smul, mem_parab_pts.1 (inv_mem p.2), map_mul, Units.val_mul, mul_assoc]⟩,
        mem_smoothPart_of_nhds (by
          filter_upwards [hU, IsOpen.mem_nhds F.2 (by simp)] with g h1 h2
          refine Subtype.ext (funext fun x => ?_)
          show (detChar (Fin 2) η (x * g) : ℂ) * F.1 ((x * g)⁻¹ • ∞) = (detChar (Fin 2) η x : ℂ) * F.1 (x⁻¹ • ∞)
          rw [map_mul, h1, mul_one, _root_.mul_inv_rev, mul_smul]
          exact congrArg _ (congrFun h2 _))⟩
      map_add' := fun F F' => Subtype.ext (Subtype.ext (funext fun x => mul_add _ _ _))
      map_smul' := fun c F => Subtype.ext (Subtype.ext (funext fun x => mul_left_comm _ _ _))
      isIntertwining' := fun g => LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => by
        show (detChar (Fin 2) η x : ℂ) * ((detChar (Fin 2) η g : ℂ) * F.1 (g⁻¹ • x⁻¹ • ∞)) =
          (detChar (Fin 2) η (x * g) : ℂ) * F.1 ((x * g)⁻¹ • ∞)
        rw [map_mul, _root_.mul_inv_rev, mul_smul, Units.val_mul, mul_assoc])) }
  refine ⟨equivOfBijective f ⟨(injective_iff_map_eq_zero _).2 fun F h => Subtype.ext (funext fun x => ?_), fun φ => ?_⟩⟩
  · obtain ⟨g, rfl⟩ := exists_smul_infty x
    exact (mul_eq_zero.1 (congrArg (fun φ => φ.1.1 g) h)).resolve_left (Units.ne_zero _)
  · choose s hs using exists_smul_infty (k := k)
    let F : OnePoint k → ℂ := fun x => (detChar (Fin 2) η (s x) : ℂ)⁻¹ * φ.1.1 (s x)
    have hF : ∀ g : GL (Fin 2) k, F (g⁻¹ • ∞) = (detChar (Fin 2) η g : ℂ)⁻¹ * φ.1.1 g := fun g => by
      have h1 : s (g⁻¹ • ∞) * g⁻¹ ∈ parab k pts := mem_parab_pts.2 (by
        rw [mul_smul, smul_eq_iff_eq_inv_smul, hs])
      have h2 := (φ.1.2 ⟨_, h1⟩ g).trans (law_detLevi η _ _)
      simp only [inv_mul_cancel_right, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val] at h2
      simp only [F, h2]
      field_simp
    refine ⟨⟨F, mem_smoothPart_of_nhds ?_⟩, Subtype.ext (Subtype.ext (funext fun g => ?_))⟩
    · filter_upwards [hU, IsOpen.mem_nhds φ.2 (by simp)] with g h1 h2
      funext x
      obtain ⟨y, rfl⟩ := exists_smul_infty x
      rw [funRep_apply, ← mul_smul, ← _root_.mul_inv_rev, hF, hF, map_mul, h1, mul_one]
      exact congrArg _ (congrArg (fun φ => φ.1 y) h2)
    · show (detChar (Fin 2) η g : ℂ) * F (g⁻¹ • ∞) = _
      rw [hF, mul_inv_cancel_left₀ (Units.ne_zero _)]

omit [DecidableEq k] in

/- English proof (translation)
Set `f : (detRep (Fin 2) η).IntertwiningMap (twist (smoothRep (funRep k)) (detChar _ η))` to `{ toFun := fun c => ⟨fun _ => c, mem_smoothPart_of_nhds (Filter.Eventually.of_forall fun _ => rfl)⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl isIntertwining' := fun g => LinearMap.ext fun c => Subtype.ext (funext fun x => ofChar_apply _ _ _) }`. Take `⟨ϖ, hϖ⟩` from `exists_uniformizer k`. Set `E : k → smoothPart (funRep k)` to `fun a => ⟨ballFn a ϖ, ballFn_mem_smoothPart a ϖ.ne_zero⟩`. Establish `h1 : ¬ (1 : ValueGroupWithZero k) ≤ valuation k (ϖ : k)` using `hϖ ▸ uniformizer_lt_one.not_ge`. Establish `key : ∀ a b : ℂ, a • E 0 + b • E 1 ∈ f.range.toSubmodule → a = 0 ∧ b = 0`.

Introduce and unpack `a b ⟨c, hc⟩`. Establish `h : ∀ x, c = a * ballFn (0 : k) ϖ x + b * ballFn (1 : k) ϖ x` using `fun x => congrArg (fun F => F.1 x) hc`. Establish `h2` using `h ∞`. Establish `h3` using `h (0 : k)`. Establish `h4` using `h (1 : k)`.

Simplify using `[ballFn_coe, h1] at h2 h3 h4`. Conclude with `⟨h3.symm.trans h2, h4.symm.trans h2⟩`. Use `⟨_, _, _, _, f, nonempty_equiv_parInd hη, fun c d h => congrArg (fun F => F.1 ∞) h, fun h => ?_, fun S => (const_or_eq_top (subrepTwist _ _ S)).imp (fun h F hF => ⟨F.1 ∞, Subtype.ext (funext fun x => (h F hF x).symm)⟩) fun h => (subrepTwist _ _).injective (h.trans (map_top _).sym …` and prove the remaining obligations. Conclude with `one_ne_zero (key 1 0 (by rw [h]; trivial)).1`. Establish `h2` using `key (L (Submodule.Quotient.mk (E 1))) (-L (Submodule.Quotient.mk (E 0))) (by`.

Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← L.map_eq_zero_iff]`. Rewrite using `[Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]`. Use the proof step `ring)`. Rewrite `h2` using `[L.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]`. Conclude with `one_ne_zero (key 0 1 (by rw [zero_smul, one_smul, zero_add]; exact h2.1)).2`.
-/
theorem exists_line {η : kˣ →* ℂˣ} (hη : IsSmoothChar η) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (π : Representation ℂ (GL (Fin 2) k) V)
      (f : (detRep (Fin 2) η).IntertwiningMap π), Nonempty (π.Equiv (parInd pts (ofChar (detLevi pts η)))) ∧
      Function.Injective f ∧ f.range ≠ ⊤ ∧ (∀ S : Subrepresentation π, S ≤ f.range ∨ S = ⊤) ∧
      IsEmpty ((V ⧸ f.range.toSubmodule) ≃ₗ[ℂ] ℂ) := by
  classical
  let f : (detRep (Fin 2) η).IntertwiningMap (twist (smoothRep (funRep k)) (detChar _ η)) :=
    { toFun := fun c => ⟨fun _ => c, mem_smoothPart_of_nhds (Filter.Eventually.of_forall fun _ => rfl)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      isIntertwining' := fun g => LinearMap.ext fun c => Subtype.ext (funext fun x => ofChar_apply _ _ _) }
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  let E : k → smoothPart (funRep k) := fun a => ⟨ballFn a ϖ, ballFn_mem_smoothPart a ϖ.ne_zero⟩
  have h1 : ¬ (1 : ValueGroupWithZero k) ≤ valuation k (ϖ : k) := hϖ ▸ uniformizer_lt_one.not_ge
  have key : ∀ a b : ℂ, a • E 0 + b • E 1 ∈ f.range.toSubmodule → a = 0 ∧ b = 0 := by
    rintro a b ⟨c, hc⟩
    have h : ∀ x, c = a * ballFn (0 : k) ϖ x + b * ballFn (1 : k) ϖ x := fun x => congrArg (fun F => F.1 x) hc
    have h2 := h ∞
    have h3 := h (0 : k)
    have h4 := h (1 : k)
    simp [ballFn_coe, h1] at h2 h3 h4
    exact ⟨h3.symm.trans h2, h4.symm.trans h2⟩
  refine ⟨_, _, _, _, f, nonempty_equiv_parInd hη, fun c d h => congrArg (fun F => F.1 ∞) h, fun h => ?_,
    fun S => (const_or_eq_top (subrepTwist _ _ S)).imp
      (fun h F hF => ⟨F.1 ∞, Subtype.ext (funext fun x => (h F hF x).symm)⟩)
      fun h => (subrepTwist _ _).injective (h.trans (map_top _).symm), ⟨fun L => ?_⟩⟩
  · exact one_ne_zero (key 1 0 (by rw [h]; trivial)).1
  · have h2 := key (L (Submodule.Quotient.mk (E 1))) (-L (Submodule.Quotient.mk (E 0))) (by
      rw [← Submodule.Quotient.mk_eq_zero, ← L.map_eq_zero_iff]
      rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul, map_add, map_smul, map_smul,
        smul_eq_mul, smul_eq_mul]
      ring)
    rw [L.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at h2
    exact one_ne_zero (key 0 1 (by rw [zero_smul, one_smul, zero_add]; exact h2.1)).2

omit [DecidableEq k] in

/- English proof (translation)
Take `rfl` from `funext hx`. Establish `key : ∀ g y, piTensor (fun a => detRep (Fin 1) (θ a)) g y = (Θ g : ℂ) • y`. Introduce `g y`. Proceed by induction on `y using PiTensorProduct.induction_on with`. Consider the case `add x y hx hy => rw [map_add, hx, hy, smul_add]`.

Consider the case `smul_tprod c x`. Rewrite using `[map_smul, smul_comm, piTensor_tprod, hΘ, Units.coe_prod, ← MultilinearMap.map_smul_univ]`. Simplify using `[detRep]`. Set `φ : (ofChar Θ).Equiv (piTensor fun a => detRep (Fin 1) (θ a))` to `.mk (PiTensorProduct.constantBaseRingEquiv (Fin 2) ℂ).toLinearEquiv.symm fun g => LinearMap.ext fun c => by`. Simplify using `only [LinearMap.comp_apply]`.

Rewrite using `[key, ofChar_apply, ← smul_eq_mul, map_smul]`. Conclude with `⟨rfl, ⟨(parIndEquiv pts φ).trans (multiProdEquiv pts fun a => equivRep (IrrRep.det (Fin 1) (θ a) (hθ a)))⟩⟩`.
-/
theorem exists_equiv_prodIrr {θ : Fin 2 → kˣ →* ℂˣ} (hθ : ∀ a, IsSmoothChar (θ a)) {x : Fin 2 → IrrGL k}
    (hx : ∀ a, x a = IrrGL.ofChar (θ a) (hθ a)) {Θ : Levi k (fun _ : Fin 2 => Fin 1) →* ℂˣ}
    (hΘ : ∀ g, Θ g = ∏ a, θ a (GeneralLinearGroup.det (g a))) :
    ∃ hd : ∑ a, (x a).1 = 2, Nonempty ((parInd pts (ofChar Θ)).Equiv (prodIrr x hd)) := by
  obtain rfl := funext hx
  have key : ∀ g y, piTensor (fun a => detRep (Fin 1) (θ a)) g y = (Θ g : ℂ) • y := by
    intro g y
    induction y using PiTensorProduct.induction_on with
    | add x y hx hy => rw [map_add, hx, hy, smul_add]
    | smul_tprod c x =>
      rw [map_smul, smul_comm, piTensor_tprod, hΘ, Units.coe_prod, ← MultilinearMap.map_smul_univ]
      simp [detRep]
  let φ : (ofChar Θ).Equiv (piTensor fun a => detRep (Fin 1) (θ a)) :=
    .mk (PiTensorProduct.constantBaseRingEquiv (Fin 2) ℂ).toLinearEquiv.symm fun g => LinearMap.ext fun c => by
      simp only [LinearMap.comp_apply]
      rw [key, ofChar_apply, ← smul_eq_mul, map_smul]
  exact ⟨rfl, ⟨(parIndEquiv pts φ).trans (multiProdEquiv pts fun a => equivRep (IrrRep.det (Fin 1) (θ a) (hθ a)))⟩⟩

end ProjLine

open ProjLine

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {χ : kˣ →* ℂˣ}

/- English proof (translation)
Rewrite using `[detLevi_apply, Fin.prod_univ_two, modExp_fin _ (fun _ => by simp), modExp_fin _ (fun _ => by simp)]`. Evaluate the numerical expressions.
-/
theorem detLevi_pts (η : kˣ →* ℂˣ) (g : Levi k fun _ : Fin 2 => Fin 1) :
    detLevi pts η g = (η * absPow k (-(1 / 2))) (GeneralLinearGroup.det (g 0)) *
      (η * absPow k (1 / 2)) (GeneralLinearGroup.det (g 1)) := by
  rw [detLevi_apply, Fin.prod_univ_two, modExp_fin _ (fun _ => by simp), modExp_fin _ (fun _ => by simp)]
  norm_num

/- English proof (translation)
Establish `h` using `exists_equiv_prodIrr (θ := fun a => χ * absPow k (a : ℕ)) (fun _ => hχ.mul (isSmoothChar_absPow _)) (x := (Segment.ofChar χ hχ 2 two_pos).term) (fun _ => IrrGL.tw_ofChar _ _ hχ (isSmoothChar_absPow _)) (Θ := detLevi pts (χ * absPow k (1 / 2))) fun g => by`. Rewrite using `[detLevi_pts, Fin.prod_univ_two, mul_assoc χ, mul_assoc χ, ← absPow_add, ← absPow_add]`. Evaluate the numerical expressions. Conclude with `h`.
-/
theorem exists_equiv_segment_two (hχ : IsSmoothChar χ) :
    ∃ hd : ∑ a, ((Segment.ofChar χ hχ 2 two_pos).term a).1 = 2,
      Nonempty ((parInd pts (ofChar (detLevi pts (χ * absPow k (1 / 2))))).Equiv
        (prodIrr (Segment.ofChar χ hχ 2 two_pos).term hd)) := by
  have h := exists_equiv_prodIrr (θ := fun a => χ * absPow k (a : ℕ)) (fun _ => hχ.mul (isSmoothChar_absPow _))
    (x := (Segment.ofChar χ hχ 2 two_pos).term) (fun _ => IrrGL.tw_ofChar _ _ hχ (isSmoothChar_absPow _))
    (Θ := detLevi pts (χ * absPow k (1 / 2))) fun g => by
      rw [detLevi_pts, Fin.prod_univ_two, mul_assoc χ, mul_assoc χ, ← absPow_add, ← absPow_add]
      norm_num
  exact h

/- English proof (translation)
Take `⟨hd, ⟨ψ⟩⟩` from `exists_equiv_segment_two hχ`. Take `⟨V, _, _, π, f, ⟨φ⟩, hf, h0, h, -⟩` from `exists_line (hχ.mul (isSmoothChar_absPow (1 / 2)))`. Conclude with `⟨hd, (isSocle_of_le (isIrreducible_ofChar _) f hf h0 h).of_equiv (.refl _) (φ.trans ψ)⟩`.
-/
theorem isZSeg_detRep_two (hχ : IsSmoothChar χ) :
    IsZSeg (Segment.ofChar χ hχ 2 two_pos) (detRep (Fin 2) (χ * absPow k (1 / 2))) := by
  obtain ⟨hd, ⟨ψ⟩⟩ := exists_equiv_segment_two hχ
  obtain ⟨V, _, _, π, f, ⟨φ⟩, hf, h0, h, -⟩ := exists_line (hχ.mul (isSmoothChar_absPow (1 / 2)))
  exact ⟨hd, (isSocle_of_le (isIrreducible_ofChar _) f hf h0 h).of_equiv (.refl _) (φ.trans ψ)⟩

/- English proof (translation)
Take `⟨hd, ⟨ψ⟩⟩` from `exists_equiv_segment_two hχ`. Take `⟨V, _, _, π, f, ⟨φ⟩, -, h0, h, h1⟩` from `exists_line (hχ.mul (isSmoothChar_absPow (1 / 2)))`. Conclude with `⟨_, _, _, quot f.range, ⟨hd, (isCosocle_quot h0 h).of_equiv (.refl _) (φ.trans ψ)⟩, fun _ => ⟨fun e => h1.false e.toLinearEquiv⟩⟩`.
-/
theorem exists_isLSeg_two (hχ : IsSmoothChar χ) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (π : Representation ℂ (GL (Fin 2) k) V),
      IsLSeg (Segment.ofChar χ hχ 2 two_pos) π ∧ ∀ ψ : GL (Fin 2) k →* ℂˣ, IsEmpty (π.Equiv (ofChar ψ)) := by
  obtain ⟨hd, ⟨ψ⟩⟩ := exists_equiv_segment_two hχ
  obtain ⟨V, _, _, π, f, ⟨φ⟩, -, h0, h, h1⟩ := exists_line (hχ.mul (isSmoothChar_absPow (1 / 2)))
  exact ⟨_, _, _, quot f.range, ⟨hd, (isCosocle_quot h0 h).of_equiv (.refl _) (φ.trans ψ)⟩,
    fun _ => ⟨fun e => h1.false e.toLinearEquiv⟩⟩

/- English proof (translation)
Establish `hΘ : IsSmoothChar (detLevi pts η⁻¹)⁻¹` using `((hη.inv.detChar.comp _ (continuous_leviEmb k pts)).mul (isSmoothChar_deltaHalf k).inv).inv`. Take `⟨V, _, _, π, f, ⟨φ⟩, hf, -, h, -⟩` from `exists_line hη.inv`. Take `⟨a⟩` from `nonempty_equiv_contra_ofChar hΘ`. Rewrite `a` using `[inv_inv]`. Take `⟨b⟩` from `(IndDual.inductionContragredient k).nonempty_equiv pts ((isSmooth_ofChar_iff _).2 hΘ)`.

Use `isCosocle_of_contra (fun U hU => ?_) (isSmooth_parInd _ _) ((φ.trans (parIndEquiv pts a)).trans b) f hf fun S hS => (h S).elim (fun e => ((isAtom_range (isIrreducible_ofChar _) f hf).le_iff.1 e).resolve_left hS ▸ le_rfl) fun e => e ▸ le_top` and prove the remaining obligations. Take `⟨J, hJ, h1, h2, -⟩` from `exists_open_normalised_subgroup_subset k (Fin 2) U hU`. Conclude with `⟨J, hJ, SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen hJ) h2, h1⟩`.
-/
theorem isCosocle_detRep_two {η : kˣ →* ℂˣ} (hη : IsSmoothChar η) :
    IsCosocle (detRep (Fin 2) η) (parInd pts (ofChar (detLevi pts η⁻¹)⁻¹)) := by
  have hΘ : IsSmoothChar (detLevi pts η⁻¹)⁻¹ :=
    ((hη.inv.detChar.comp _ (continuous_leviEmb k pts)).mul (isSmoothChar_deltaHalf k).inv).inv
  obtain ⟨V, _, _, π, f, ⟨φ⟩, hf, -, h, -⟩ := exists_line hη.inv
  obtain ⟨a⟩ := nonempty_equiv_contra_ofChar hΘ
  rw [inv_inv] at a
  obtain ⟨b⟩ := (IndDual.inductionContragredient k).nonempty_equiv pts ((isSmooth_ofChar_iff _).2 hΘ)
  refine isCosocle_of_contra (fun U hU => ?_) (isSmooth_parInd _ _) ((φ.trans (parIndEquiv pts a)).trans b) f hf
    fun S hS => (h S).elim
      (fun e => ((isAtom_range (isIrreducible_ofChar _) f hf).le_iff.1 e).resolve_left hS ▸ le_rfl) fun e => e ▸ le_top
  obtain ⟨J, hJ, h1, h2, -⟩ := exists_open_normalised_subgroup_subset k (Fin 2) U hU
  exact ⟨J, hJ, SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen hJ) h2, h1⟩

/- English proof (translation)
Take `⟨hd, ⟨ψ⟩⟩` from `exists_equiv_prodIrr (θ := ![χ * absPow k 1, χ]) (Fin.forall_fin_two.2 ⟨hχ.mul (isSmoothChar_absPow _), hχ⟩) (x := ![(IrrGL.ofChar χ hχ).nu 1, IrrGL.ofChar χ hχ]) (Fin.forall_fin_two.2 ⟨IrrGL.tw_ofChar _ _ hχ (isSmoothChar_absPow _), rfl⟩) (Θ := (detLevi pts (χ * absPow k (1 / 2) …`. Establish `h1 : (χ * absPow k (1 / 2))⁻¹ * absPow k (-(1 / 2)) = (χ * absPow k 1)⁻¹`. Rewrite using `[absPow_neg, ← mul_inv, mul_assoc, ← absPow_add, add_halves]`. Rewrite using `[MonoidHom.inv_apply, detLevi_pts, Fin.prod_univ_two, h1, mul_inv χ (absPow k (1 / 2)), inv_mul_cancel_right]`. Simplify using `[mul_comm]`.

Use `⟨2, _, hd, ⟨![Segment.single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1), Segment.single _ (IrrGL.isCusp_ofChar χ hχ)], ⟨?_, fun i j hij => ?_⟩, Fin.forall_fin_two.2 ⟨(single_spec ((IrrGL.isCusp_ofChar χ hχ).nu 1)).2.1, (single_spec (IrrGL.isCusp_ofChar χ hχ)).2.1⟩⟩, (isCosocle_detRep_tw …` and prove the remaining obligations. Rewrite using `[add_comm]`. Both sides reduce to the same expression. Take `⟨rfl, rfl⟩ : i = 0 ∧ j = 1` from `by omega`. Conclude with `(single_precedes χ hχ).2`.
-/
theorem isL_detRep_two (hχ : IsSmoothChar χ) :
    IsL ({Segment.single _ (IrrGL.isCusp_ofChar χ hχ)} + {Segment.single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1)})
      (detRep (Fin 2) (χ * absPow k (1 / 2))) := by
  obtain ⟨hd, ⟨ψ⟩⟩ := exists_equiv_prodIrr (θ := ![χ * absPow k 1, χ])
    (Fin.forall_fin_two.2 ⟨hχ.mul (isSmoothChar_absPow _), hχ⟩)
    (x := ![(IrrGL.ofChar χ hχ).nu 1, IrrGL.ofChar χ hχ])
    (Fin.forall_fin_two.2 ⟨IrrGL.tw_ofChar _ _ hχ (isSmoothChar_absPow _), rfl⟩)
    (Θ := (detLevi pts (χ * absPow k (1 / 2))⁻¹)⁻¹) fun g => by
      have h1 : (χ * absPow k (1 / 2))⁻¹ * absPow k (-(1 / 2)) = (χ * absPow k 1)⁻¹ := by
        rw [absPow_neg, ← mul_inv, mul_assoc, ← absPow_add, add_halves]
      rw [MonoidHom.inv_apply, detLevi_pts, Fin.prod_univ_two, h1, mul_inv χ (absPow k (1 / 2)), inv_mul_cancel_right]
      simp [mul_comm]
  refine ⟨2, _, hd, ⟨![Segment.single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1), Segment.single _ (IrrGL.isCusp_ofChar χ hχ)],
    ⟨?_, fun i j hij => ?_⟩, Fin.forall_fin_two.2 ⟨(single_spec ((IrrGL.isCusp_ofChar χ hχ).nu 1)).2.1,
      (single_spec (IrrGL.isCusp_ofChar χ hχ)).2.1⟩⟩,
    (isCosocle_detRep_two (hχ.mul (isSmoothChar_absPow _))).of_equiv (.refl _) ψ⟩
  · rw [add_comm]
    rfl
  · obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 1 := by omega
    exact (single_precedes χ hχ).2

/- English proof (translation)
Assemble the required witnesses or components as `⟨isZSeg_detRep_two hχ, exists_isLSeg_two hχ, isL_detRep_two hχ⟩`.
-/
theorem segment_two_spec (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    IsZSeg (Segment.ofChar χ hχ 2 two_pos) (detRep (Fin 2) (χ * absPow k (1 / 2))) ∧
    (∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (π : Representation ℂ (GL (Fin 2) k) V),
      IsLSeg (Segment.ofChar χ hχ 2 two_pos) π ∧ ∀ ψ : GL (Fin 2) k →* ℂˣ, IsEmpty (π.Equiv (ofChar ψ))) ∧
    IsL ({Segment.single _ (IrrGL.isCusp_ofChar χ hχ)} + {Segment.single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1)})
      (detRep (Fin 2) (χ * absPow k (1 / 2))) :=
  ⟨isZSeg_detRep_two hχ, exists_isLSeg_two hχ, isL_detRep_two hχ⟩

end GlobalTheory.LocGL
