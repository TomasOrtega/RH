import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory

namespace GlobalTheory.SmGL.SwapBlocks

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Substitute `h` using the available equality. Take `rfl : σ = σ'` from `MonoidHom.ext fun g => hσ g.1 g.2 g.2`. Conclude with `⟨Representation.Equiv.refl _⟩`.
-/
theorem smInd_equiv_of_eq [TopologicalSpace G] [IsTopologicalGroup G] {H H' : Subgroup G} (h : H = H')
    (σ : Representation ℂ H V) (σ' : Representation ℂ H' V)
    (hσ : ∀ g (hg : g ∈ H) (hg' : g ∈ H'), σ ⟨g, hg⟩ = σ' ⟨g, hg'⟩) :
    Nonempty ((smInd H σ).Equiv (smInd H' σ')) := by
  subst h
  obtain rfl : σ = σ' := MonoidHom.ext fun g => hσ g.1 g.2 g.2
  exact ⟨Representation.Equiv.refl _⟩

end General

section Blocks

variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[val_emb₂, val_emb₂]`. Use extensionality with `i j`. Take `⟨i, rfl⟩` from `e.surjective i`. Take `⟨j, rfl⟩` from `e.surjective j`.

Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> simp`.
-/
theorem emb₂_swap (e : a ⊕ b ≃ n) (g : GL a R × GL b R) :
    emb₂ R e g = emb₂ R ((Equiv.sumComm b a).trans e) (g.2, g.1) := by
  apply Units.ext
  rw [val_emb₂, val_emb₂]
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp

end Blocks

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

end Local

open ValuativeRel MeasureTheory in
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] in
/- English proof (translation)
Substitute `h` using the available equality. Take `rfl : σ = σ'` from `MonoidHom.ext fun p => hσ p p.2 p.2`. Conclude with `⟨Representation.Equiv.refl _⟩`.
-/
private theorem nonempty_equiv_smInd_of_eq [TopologicalSpace G] [IsTopologicalGroup G]
    {W : Type} [AddCommGroup W] [Module ℂ W] {H H' : Subgroup G} (h : H = H')
    (σ : Representation ℂ H W) (σ' : Representation ℂ H' W)
    (hσ : ∀ (g : G) (hg : g ∈ H) (hg' : g ∈ H'), σ ⟨g, hg⟩ = σ' ⟨g, hg'⟩) :
    Nonempty ((_root_.GlobalTheory.PRep.smInd H σ).Equiv (_root_.GlobalTheory.PRep.smInd H' σ')) := by
  subst h
  obtain rfl : σ = σ' := MonoidHom.ext fun p => hσ p p.2 p.2
  exact ⟨Representation.Equiv.refl _⟩

open ValuativeRel MeasureTheory in
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
/- English proof (translation)
Use extensionality with `g`. Rewrite using `[_root_.GlobalTheory.SmGL.mem_parabLower_two, _root_.GlobalTheory.SmGL.mem_parab_two]`. Simplify using the standard rewrite rules.
-/
private theorem parabLower_eq_parab_sumComm (e : a ⊕ b ≃ n) :
    _root_.GlobalTheory.SmGL.parabLower R (_root_.GlobalTheory.SmGL.two e) =
      _root_.GlobalTheory.SmGL.parab R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e)) := by
  ext g
  rw [_root_.GlobalTheory.SmGL.mem_parabLower_two, _root_.GlobalTheory.SmGL.mem_parab_two]
  simp

open ValuativeRel MeasureTheory in
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `Matrix.GeneralLinearGroup.ext fun i j => ?_` and prove the remaining obligations. Consider the cases of `x`. Express the relevant statement in the definitionally equal form `_ = ((_root_.GlobalTheory.SmGL.leviProjLower R (_root_.GlobalTheory.SmGL.two e) p true : GL b R) : Matrix b b R) i j`. Rewrite using `[_root_.GlobalTheory.SmGL.leviProj_apply, _root_.GlobalTheory.SmGL.leviProjLower_apply]`.

Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `_ = ((_root_.GlobalTheory.SmGL.leviProjLower R (_root_.GlobalTheory.SmGL.two e) p false : GL a R) : Matrix a a R) i j`. Rewrite using `[_root_.GlobalTheory.SmGL.leviProj_apply, _root_.GlobalTheory.SmGL.leviProjLower_apply]`. Both sides reduce to the same expression.
-/
private theorem leviProj_sumComm_eq_swap_leviProjLower (e : a ⊕ b ≃ n)
    (p : _root_.GlobalTheory.SmGL.parabLower R (_root_.GlobalTheory.SmGL.two e))
    (hp : (p : GL n R) ∈
      _root_.GlobalTheory.SmGL.parab R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e))) :
    _root_.GlobalTheory.SmGL.leviProj R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e)) ⟨p, hp⟩ =
      _root_.GlobalTheory.SmGL.leviTwo R b a
        ((_root_.GlobalTheory.SmGL.leviTwo R a b).symm
          (_root_.GlobalTheory.SmGL.leviProjLower R (_root_.GlobalTheory.SmGL.two e) p)).swap := by
  funext x
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  cases x
  · change _ = ((_root_.GlobalTheory.SmGL.leviProjLower R (_root_.GlobalTheory.SmGL.two e) p true : GL b R) :
      Matrix b b R) i j
    rw [_root_.GlobalTheory.SmGL.leviProj_apply, _root_.GlobalTheory.SmGL.leviProjLower_apply]
    rfl
  · change _ = ((_root_.GlobalTheory.SmGL.leviProjLower R (_root_.GlobalTheory.SmGL.two e) p false : GL a R) :
      Matrix a a R) i j
    rw [_root_.GlobalTheory.SmGL.leviProj_apply, _root_.GlobalTheory.SmGL.leviProjLower_apply]
    rfl

open ValuativeRel MeasureTheory in
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
/- English proof (translation)
Rewrite using `[MonoidHom.inv_apply, _root_.GlobalTheory.SmGL.deltaHalf_two, _root_.GlobalTheory.SmGL.deltaHalf_two, neg_div, neg_div, _root_.GlobalTheory.SmGL.absPow_neg, _root_.GlobalTheory.SmGL.absPow_neg]`. Simplify using `only [Prod.fst_swap, Prod.snd_swap, MonoidHom.inv_apply, mul_inv, inv_inv]`. Conclude with `mul_comm _ _`.
-/
private theorem deltaHalf_inv_leviTwo_eq_deltaHalf_swap (g : GL a k × GL b k) :
    (_root_.GlobalTheory.SmGL.deltaHalf k (_root_.GlobalTheory.SmGL.Two a b))⁻¹ (_root_.GlobalTheory.SmGL.leviTwo k a b g) =
      _root_.GlobalTheory.SmGL.deltaHalf k (_root_.GlobalTheory.SmGL.Two b a) (_root_.GlobalTheory.SmGL.leviTwo k b a g.swap) := by
  rw [MonoidHom.inv_apply, _root_.GlobalTheory.SmGL.deltaHalf_two,
    _root_.GlobalTheory.SmGL.deltaHalf_two, neg_div, neg_div, _root_.GlobalTheory.SmGL.absPow_neg,
    _root_.GlobalTheory.SmGL.absPow_neg]
  simp only [Prod.fst_swap, Prod.snd_swap, MonoidHom.inv_apply, mul_inv, inv_inv]
  exact mul_comm _ _

open ValuativeRel MeasureTheory in
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] in
/- English proof (translation)
Unfold `_root_.GlobalTheory.PRep.jacquet`. Simplify using `only [MonoidHom.coe_mk, OneHom.coe_mk]`. Use `congr 1`. Rewrite using `[h]`.
-/
private theorem jacquet_apply_eq_of_eq {M M' : Type} [Group M] [Group M']
    (π : Representation ℂ G V) (N : Subgroup G) (s : M →* G) (s' : M' →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G))
    (hs' : ∀ m, s' m ∈ Subgroup.normalizer (N : Set G)) {x : M} {x' : M'} (h : s x = s' x') :
    _root_.GlobalTheory.PRep.jacquet π N s hs x = _root_.GlobalTheory.PRep.jacquet π N s' hs' x' := by
  unfold _root_.GlobalTheory.PRep.jacquet
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  congr 1
  rw [h]

open ValuativeRel MeasureTheory in
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] in
/- English proof (translation)
Substitute `hN` using the available equality. Establish `h : (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s hs) χ).comp φ = (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s' hs') χ').comp φ'`. Use `MonoidHom.ext fun x => LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `only [MonoidHom.comp_apply, _root_.GlobalTheory.SmGL.twist_apply, hχ, jacquet_apply_eq_of_eq π N s s' hs hs' (hφ x)]`. Rewrite using `[h]`.

Conclude with `⟨Representation.Equiv.refl _⟩`.
-/
private theorem nonempty_equiv_twist_jacquet_comp {M M' K : Type} [Group M] [Group M'] [Group K]
    (π : Representation ℂ G V) {N N' : Subgroup G} (hN : N = N') (s : M →* G) (s' : M' →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G))
    (hs' : ∀ m, s' m ∈ Subgroup.normalizer (N' : Set G)) (φ : K →* M) (φ' : K →* M')
    (hφ : ∀ x, s (φ x) = s' (φ' x)) (χ : M →* ℂˣ) (χ' : M' →* ℂˣ)
    (hχ : ∀ x, χ (φ x) = χ' (φ' x)) :
    Nonempty (Representation.Equiv
      ((_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s hs) χ).comp φ)
      ((_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N' s' hs') χ').comp φ')) := by
  subst hN
  have h : (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s hs) χ).comp φ =
      (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s' hs') χ').comp φ' := by
    refine MonoidHom.ext fun x => LinearMap.ext fun v => ?_
    simp only [MonoidHom.comp_apply, _root_.GlobalTheory.SmGL.twist_apply, hχ,
      jacquet_apply_eq_of_eq π N s s' hs hs' (hφ x)]
  rw [h]
  exact ⟨Representation.Equiv.refl _⟩

open ValuativeRel MeasureTheory in
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
/- English proof (translation)
Use extensionality with `g`. Rewrite using `[_root_.GlobalTheory.SmGL.mem_unipRadLower, _root_.GlobalTheory.SmGL.mem_unipRad, parabLower_eq_parab_sumComm]`. Use `and_congr_right fun _ => ?_` and prove the remaining obligations. Simplify using `only [Bool.forall_bool]`. Conclude with `and_comm`.
-/
private theorem unipRadLower_eq_unipRad_sumComm (e : a ⊕ b ≃ n) :
    _root_.GlobalTheory.SmGL.unipRadLower R (_root_.GlobalTheory.SmGL.two e) =
      _root_.GlobalTheory.SmGL.unipRad R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e)) := by
  ext g
  rw [_root_.GlobalTheory.SmGL.mem_unipRadLower, _root_.GlobalTheory.SmGL.mem_unipRad,
    parabLower_eq_parab_sumComm]
  refine and_congr_right fun _ => ?_
  simp only [Bool.forall_bool]
  exact and_comm

open ValuativeRel MeasureTheory in
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
/- English proof (translation)
Apply the tactic sequence `rcases u with u | u <;> rcases v with v | v`. Rewrite using `[← _root_.GlobalTheory.SmGL.two_false e u, ← _root_.GlobalTheory.SmGL.two_false e v, _root_.GlobalTheory.SmGL.leviEmb_apply_same]`. Both sides reduce to the same expression. Rewrite using `[← _root_.GlobalTheory.SmGL.two_false e u, ← _root_.GlobalTheory.SmGL.two_true e v, _root_.GlobalTheory.SmGL.leviEmb_apply_ne _ _ _ (by decide : false ≠ true)]`. Both sides reduce to the same expression.

Rewrite using `[← _root_.GlobalTheory.SmGL.two_true e u, ← _root_.GlobalTheory.SmGL.two_false e v, _root_.GlobalTheory.SmGL.leviEmb_apply_ne _ _ _ (by decide : true ≠ false)]`. Both sides reduce to the same expression. Rewrite using `[← _root_.GlobalTheory.SmGL.two_true e u, ← _root_.GlobalTheory.SmGL.two_true e v, _root_.GlobalTheory.SmGL.leviEmb_apply_same]`. Both sides reduce to the same expression.
-/
private theorem leviEmb_leviTwo_apply_eq_fromBlocks (e : a ⊕ b ≃ n) (g : GL a R × GL b R) (u v : a ⊕ b) :
    (_root_.GlobalTheory.SmGL.leviEmb R (_root_.GlobalTheory.SmGL.two e) (_root_.GlobalTheory.SmGL.leviTwo R a b g) :
        Matrix n n R) (e u) (e v) =
      Matrix.fromBlocks (g.1 : Matrix a a R) 0 0 (g.2 : Matrix b b R) u v := by
  rcases u with u | u <;> rcases v with v | v
  · rw [← _root_.GlobalTheory.SmGL.two_false e u, ← _root_.GlobalTheory.SmGL.two_false e v,
      _root_.GlobalTheory.SmGL.leviEmb_apply_same]
    rfl
  · rw [← _root_.GlobalTheory.SmGL.two_false e u, ← _root_.GlobalTheory.SmGL.two_true e v,
      _root_.GlobalTheory.SmGL.leviEmb_apply_ne _ _ _ (by decide : false ≠ true)]
    rfl
  · rw [← _root_.GlobalTheory.SmGL.two_true e u, ← _root_.GlobalTheory.SmGL.two_false e v,
      _root_.GlobalTheory.SmGL.leviEmb_apply_ne _ _ _ (by decide : true ≠ false)]
    rfl
  · rw [← _root_.GlobalTheory.SmGL.two_true e u, ← _root_.GlobalTheory.SmGL.two_true e v,
      _root_.GlobalTheory.SmGL.leviEmb_apply_same]
    rfl

open ValuativeRel MeasureTheory in
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
/- English proof (translation)
Use `Matrix.GeneralLinearGroup.ext fun i j => ?_` and prove the remaining obligations. Take `⟨u, rfl⟩` from `e.surjective i`. Take `⟨v, rfl⟩` from `e.surjective j`. Establish `hu : e u = ((Equiv.sumComm b a).trans e) u.swap` using `by simp`. Establish `hv : e v = ((Equiv.sumComm b a).trans e) v.swap` using `by simp`.

Rewrite using `[leviEmb_leviTwo_apply_eq_fromBlocks, hu, hv, leviEmb_leviTwo_apply_eq_fromBlocks]`. Apply the tactic sequence `rcases u with u | u <;> rcases v with v | v <;> rfl`.
-/
private theorem leviEmb_leviTwo_eq_leviEmb_sumComm_swap (e : a ⊕ b ≃ n) (g : GL a R × GL b R) :
    _root_.GlobalTheory.SmGL.leviEmb R (_root_.GlobalTheory.SmGL.two e) (_root_.GlobalTheory.SmGL.leviTwo R a b g) =
      _root_.GlobalTheory.SmGL.leviEmb R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e))
        (_root_.GlobalTheory.SmGL.leviTwo R b a g.swap) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  obtain ⟨u, rfl⟩ := e.surjective i
  obtain ⟨v, rfl⟩ := e.surjective j
  have hu : e u = ((Equiv.sumComm b a).trans e) u.swap := by simp
  have hv : e v = ((Equiv.sumComm b a).trans e) v.swap := by simp
  rw [leviEmb_leviTwo_apply_eq_fromBlocks, hu, hv, leviEmb_leviTwo_apply_eq_fromBlocks]
  rcases u with u | u <;> rcases v with v | v <;> rfl

open ValuativeRel MeasureTheory in

/- English proof (translation)
Introduce `k _ _ _ _ a b n _ _ _ _ _ _ e V _ _`. Use `⟨fun ρ => ?_, fun π => ?_⟩` and prove the remaining obligations. Unfold `_root_.GlobalTheory.SmGL.ind₂Lower _root_.GlobalTheory.SmGL.ind₂ _root_.GlobalTheory.SmGL.parIndLower _root_.GlobalTheory.SmGL.parInd`. Use `nonempty_equiv_smInd_of_eq (parabLower_eq_parab_sumComm k e) _ _ fun g hg hg' => LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `only [MonoidHom.comp_apply, _root_.GlobalTheory.SmGL.twist_apply, MulEquiv.coe_toMonoidHom]`.

Rewrite using `[leviProj_sumComm_eq_swap_leviProjLower k e ⟨g, hg⟩ hg', ← deltaHalf_inv_leviTwo_eq_deltaHalf_swap]`. Simplify using the standard rewrite rules. Unfold `_root_.GlobalTheory.SmGL.jac₂Lower _root_.GlobalTheory.SmGL.jac₂ _root_.GlobalTheory.SmGL.jacLower _root_.GlobalTheory.SmGL.jac _root_.GlobalTheory.SmGL.jacU`. Rewrite using `[MonoidHom.comp_assoc]`. Use `nonempty_equiv_twist_jacquet_comp π (unipRadLower_eq_unipRad_sumComm k e) _ _ _ _ _ _ (fun x => leviEmb_leviTwo_eq_leviEmb_sumComm_swap k e x) _ _ fun x => ?_` and prove the remaining obligations.

Simplify using `only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]`. Rewrite using `[MonoidHom.inv_apply, show (MulEquiv.prodComm x : GL b k × GL a k) = x.swap from rfl, ← deltaHalf_inv_leviTwo_eq_deltaHalf_swap, MonoidHom.inv_apply, inv_inv]`.
-/
theorem _root_.GlobalTheory.SmGL.SwapBlocks.lower_equiv_upper_swap : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b n : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n] (e : a ⊕ b ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V], (∀ ρ : Representation ℂ (GL a k × GL b k) V, Nonempty ((_root_.GlobalTheory.SmGL.ind₂Lower e ρ).Equiv (_root_.GlobalTheory.SmGL.ind₂ ((Equiv.sumComm b a).trans e) (ρ.comp (MulEquiv.prodComm : GL b k × GL a k ≃* GL a k × GL b k).toMonoidHom)))) ∧ ∀ π : Representation ℂ (GL n k) V, Nonempty ((_root_.GlobalTheory.SmGL.jac₂Lower e π).Equiv ((_root_.GlobalTheory.SmGL.jac₂ ((Equiv.sumComm b a).trans e) π).comp (MulEquiv.prodComm : GL a k × GL b k ≃* GL b k × GL a k).toMonoidHom)) := by
  intro k _ _ _ _ a b n _ _ _ _ _ _ e V _ _
  refine ⟨fun ρ => ?_, fun π => ?_⟩
  · unfold _root_.GlobalTheory.SmGL.ind₂Lower _root_.GlobalTheory.SmGL.ind₂
      _root_.GlobalTheory.SmGL.parIndLower _root_.GlobalTheory.SmGL.parInd
    refine nonempty_equiv_smInd_of_eq (parabLower_eq_parab_sumComm k e) _ _
      fun g hg hg' => LinearMap.ext fun v => ?_
    simp only [MonoidHom.comp_apply, _root_.GlobalTheory.SmGL.twist_apply,
      MulEquiv.coe_toMonoidHom]
    rw [leviProj_sumComm_eq_swap_leviProjLower k e ⟨g, hg⟩ hg', ← deltaHalf_inv_leviTwo_eq_deltaHalf_swap]
    simp
  · unfold _root_.GlobalTheory.SmGL.jac₂Lower _root_.GlobalTheory.SmGL.jac₂ _root_.GlobalTheory.SmGL.jacLower
      _root_.GlobalTheory.SmGL.jac _root_.GlobalTheory.SmGL.jacU
    rw [MonoidHom.comp_assoc]
    refine nonempty_equiv_twist_jacquet_comp π (unipRadLower_eq_unipRad_sumComm k e) _ _ _ _
      _ _ (fun x => leviEmb_leviTwo_eq_leviEmb_sumComm_swap k e x) _ _ fun x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [MonoidHom.inv_apply, show (MulEquiv.prodComm x : GL b k × GL a k) = x.swap from rfl,
      ← deltaHalf_inv_leviTwo_eq_deltaHalf_swap, MonoidHom.inv_apply, inv_inv]

end GlobalTheory.SmGL.SwapBlocks
