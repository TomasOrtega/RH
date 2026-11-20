import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLiftAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntertwiningMapNeZeroOfIsotypicIrreducibleStatement
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocProj

/- English proof (translation)
Introduce `L _ _ _ n π s τ i T hi hic hT hTS hTeq f hf hf0`. Take `⟨hdec, hcomm, huniq⟩` from `GlobalTheory.SplitAdelic.main L n s`. Use `choose lift hlift using fun A => (huniq A).exists`. Establish `hlu : ∀ A x, TrivOutside {s.v} x → s.loc n x = A → x = lift A` using `fun A x hx e => (huniq A).unique ⟨hx, e⟩ (hlift A)`. Establish `tmul : ∀ {x y : GAf L n}, TrivOutside {s.v} x → TrivOutside {s.v} y → TrivOutside {s.v} (x * y)`.

Introduce `x y hx hy v hv`. Use `show ((x.1 * y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1`. Rewrite using `[Units.val_mul, Matrix.map_mul, hx v hv, hy v hv, mul_one]`. Establish `tone : TrivOutside {s.v} (1 : GAf L n)`. Introduce `v _`.

Use `show ((1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1`. Rewrite using `[Units.val_one]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`. Set `lh : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GAf L n` to `{ toFun := lift map_one' := (hlu _ _ tone (map_one _)).symm map_mul' := fun A B => (hlu _ _ (tmul (hlift A).1 (hlift B).1) (by rw [map_mul, (hlift A).2, (hlift B).2])).symm }`. Establish `hlh : ∀ x, TrivOutside {s.v} x → lh (s.loc n x) = x` using `fun x hx => (hlu _ x hx rfl).symm`.

Set `ρ : Representation ℂ (GAf L n) π.S` to `{ toFun := fun g => (NG.rt L n g).restrict (fun f hf => π.stable g f hf) map_one' := by`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `f`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`.

Simplify using `[NG.rt]`. Use the proof step `map_mul' := fun a b => by`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `f`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `x`. Simplify using `[NG.rt, mul_assoc] }`. Establish `hρ : ∀ g (f : π.S), ((ρ g f : π.S) : GAf L n → ℂ) = NG.rt L n g f` using `fun _ _ => rfl`. Establish `hρirr : ρ.IsIrreducible`. Use `{ exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun P => ?_ }` and prove the remaining obligations.

Take `⟨g, hg, hg0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot π.ne`. Establish `h1 : (⟨g, hg⟩ : π.S) ∈ (⊤ : Subrepresentation ρ).toSubmodule` using `Submodule.mem_top`. Rewrite `h1` using `[← h]`. Conclude with `hg0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h1))`. Establish `hle : P.toSubmodule.map π.S.subtype ≤ π.S`.

Introduce and unpack `_ ⟨p, -, rfl⟩`. Conclude with `p.2`. Establish `hst : ∀ h, ∀ g ∈ P.toSubmodule.map π.S.subtype, NG.rt L n h g ∈ P.toSubmodule.map π.S.subtype`. Introduce and unpack `h _ ⟨p, hp, rfl⟩`. Conclude with `⟨ρ h p, P.apply_mem_toSubmodule h hp, rfl⟩`.

Break down `π.irr _ hle hst with h | h` into its components or cases. Use `left`. Apply `Subrepresentation.ext` to reduce the goal to its premises. Use `show P.toSubmodule = ⊥`. Rewrite using `[eq_bot_iff]`.

Introduce `p hp`. Establish `: (p : GAf L n → ℂ) ∈ P.toSubmodule.map π.S.subtype` using `⟨p, hp, rfl⟩`. Rewrite `this` using `[h, Submodule.mem_bot]`. Conclude with `(Submodule.mem_bot ℂ).2 (Subtype.ext this)`. Use `right`.

Apply `Subrepresentation.ext` to reduce the goal to its premises. Use `show P.toSubmodule = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `p _`. Establish `: (p : GAf L n → ℂ) ∈ P.toSubmodule.map π.S.subtype` using `by rw [h]; exact p.2`.

Take `⟨q, hq, e'⟩` from `this`. Rewrite `hq` using `[show q = p from Subtype.ext e']`. Then use the resulting hypothesis. Set `mi : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GL (Fin n) (s.w.adicCompletion L)` to `Matrix.GeneralLinearGroup.map i.toRingHom`. Establish `hmi : ∀ B, mi (Matrix.GeneralLinearGroup.map i.symm.toRingHom B) = B` using `fun B => Units.ext (Matrix.ext fun a b => i.apply_symm_apply _)`. Set `σ : Representation ℂ (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) τ.V` to `τ.ρ.comp mi`.

Establish `hσirr : σ.IsIrreducible`. Establish `hτ` using `τ.irr`. Use `{ exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun P => ?_ }` and prove the remaining obligations. Take `⟨P1, P2, hne⟩` from `hτ.exists_pair_ne`. Apply `hne` to reduce the goal to its premises.

Establish `e1 : P1 = ⊥ ∨ P1 = ⊤` using `hτ.eq_bot_or_eq_top P1`. Establish `e2 : P2 = ⊥ ∨ P2 = ⊤` using `hτ.eq_bot_or_eq_top P2`. Establish `htop : (⊥ : Subrepresentation τ.ρ) = ⊤`. Apply `Subrepresentation.ext` to reduce the goal to its premises. Establish `h'` using `congrArg Subrepresentation.toSubmodule h`.

Conclude with `h'`. Apply the tactic sequence `rcases e1 with rfl | rfl <;> rcases e2 with rfl | rfl <;> simp [htop]`. Set `P' : Subrepresentation τ.ρ` to `⟨P.toSubmodule, fun g v hv => by`. Use `P.apply_mem_toSubmodule (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) hv` as an intermediate fact. Express the relevant statement in the definitionally equal form `τ.ρ (mi _) v ∈ P.toSubmodule at this`.

Rewrite using `[hmi] at this⟩` and apply the resulting hypothesis. Break down `hτ.eq_bot_or_eq_top P' with h | h` into its components or cases. Use `left`. Apply `Subrepresentation.ext` to reduce the goal to its premises. Establish `h'` using `congrArg Subrepresentation.toSubmodule h`.

Conclude with `h'`. Use `right`. Apply `Subrepresentation.ext` to reduce the goal to its premises. Establish `h'` using `congrArg Subrepresentation.toSubmodule h`. Conclude with `h'`.

Establish `hV : ∃ a : τ.V, a ≠ 0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨P1, P2, hne⟩` from `τ.irr.exists_pair_ne`. Apply `hne` to reduce the goal to its premises.

Apply `Subrepresentation.ext` to reduce the goal to its premises. Use extensionality with `a`. Simplify using `[hcon a, P1.toSubmodule.zero_mem, P2.toSubmodule.zero_mem]`. Set `f0 : σ.IntertwiningMap (ρ.comp lh)` to `{ toLinearMap := LinearMap.codRestrict π.S T hTS isIntertwining' := fun A => by`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `a`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show T (τ.ρ (mi A) a) = NG.rt L n (lh A) (T a)`. Use `hTeq (lh A) (hlift A).1 a` as an intermediate fact. Rewrite using `[show s.loc n (lh A) = A from (hlift A).2] at this }` and apply the resulting hypothesis.

Establish `hf0' : f0 ≠ 0`. Take `⟨a, ha⟩` from `hV`. Introduce `h`. Apply `ha` to reduce the goal to its premises. Apply `hT` to reduce the goal to its premises.

Establish `: (f0 a : GAf L n → ℂ) = 0` using `by rw [h]; rfl`. Simplify `this` using `[f0]`. Establish `hc : ∀ g, ∃ u, ∀ y, Commute ((lh u)⁻¹ * g) (lh y)`. Introduce `g`. Take `⟨x, y', hx, hy', rfl⟩` from `hdec g`.

Use `⟨s.loc n x, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[hlh x hx, inv_mul_cancel_left]`. Conclude with `(hcomm _ _ (hlift y).1 hy').symm`. Establish `hU : ∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (σ' : Representation ℂ _ W'), σ'.IsIrreducible → ∀ f' : σ'.IntertwiningMap (ρ.comp lh), f' ≠ 0 → Nonempty (σ.Equiv σ')`. Introduce `W' _ _ σ' hσ' f' hf'`.

Conclude with `(GlobalTheory.CuspRep.CompUniq.isotypic _ _ _ _ W' ρ lh σ σ' hρirr hσirr hσ' hc f0 hf0').2 f' hf'`. Establish `hsum` using `(GlobalTheory.CuspRep.CompUniq.isotypic _ _ _ _ τ.V ρ lh σ σ hρirr hσirr hσirr hc f0 hf0').1`. Establish `hfne : (⟨f, hf⟩ : π.S) ≠ 0` using `fun h => hf0 (congrArg Subtype.val h)`. Take `⟨p0, hp0⟩` from `GlobalTheory.T.exists_intertwiningMap_ne_zero_of_isotypic_irreducible _ _ _ (ρ.comp lh) σ hσirr hsum hU ⟨f, hf⟩ hfne`. Take `⟨p, hp⟩` from `LinearMap.exists_extend p0.toLinearMap`.

Establish `hpS : ∀ g (hg : g ∈ π.S), p g = p0 ⟨g, hg⟩` using `fun g hg => by`. Use `LinearMap.congr_fun hp ⟨g, hg⟩` as an intermediate fact. Conclude with `this`. Use `⟨p, by rw [hpS f hf]; exact hp0, fun x hx f' hf' => ?_⟩` and prove the remaining obligations. Rewrite using `[hpS _ (π.stable x f' hf'), hpS f' hf']`.

Establish `e1 : (⟨NG.rt L n x f', π.stable x f' hf'⟩ : π.S) = (ρ.comp lh) (s.loc n x) ⟨f', hf'⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show NG.rt L n x f' = NG.rt L n (lh (s.loc n x)) f'`. Rewrite using `[hlh x hx]`. Rewrite using `[e1]`.

Conclude with `LinearMap.congr_fun (p0.isIntertwining' (s.loc n x)) ⟨f', hf'⟩`.
-/
theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)), Continuous i → (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) → Function.Injective T → (∀ a, T a ∈ π.S) → (∀ x : GAf L n, TrivOutside {s.v} (x : GA L n) → ∀ a, T (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T a)) → ∀ f ∈ π.S, f ≠ 0 → ∃ p : (GAf L n → ℂ) →ₗ[ℂ] τ.V, p f ≠ 0 ∧ ∀ x : GAf L n, TrivOutside {s.v} (x : GA L n) → ∀ f' ∈ π.S, p (NG.rt L n x f') = τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) (p f') := by
  intro L _ _ _ n π s τ i T hi hic hT hTS hTeq f hf hf0
  classical
  obtain ⟨hdec, hcomm, huniq⟩ := GlobalTheory.SplitAdelic.main L n s
  choose lift hlift using fun A => (huniq A).exists
  have hlu : ∀ A x, TrivOutside {s.v} x → s.loc n x = A → x = lift A := fun A x hx e =>
    (huniq A).unique ⟨hx, e⟩ (hlift A)
  have tmul : ∀ {x y : GAf L n}, TrivOutside {s.v} x → TrivOutside {s.v} y → TrivOutside {s.v} (x * y) := by
    intro x y hx hy v hv
    show ((x.1 * y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1
    rw [Units.val_mul, Matrix.map_mul, hx v hv, hy v hv, mul_one]
  have tone : TrivOutside {s.v} (1 : GAf L n) := by
    intro v _
    show ((1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1
    rw [Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  let lh : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GAf L n :=
    { toFun := lift
      map_one' := (hlu _ _ tone (map_one _)).symm
      map_mul' := fun A B => (hlu _ _ (tmul (hlift A).1 (hlift B).1)
        (by rw [map_mul, (hlift A).2, (hlift B).2])).symm }
  have hlh : ∀ x, TrivOutside {s.v} x → lh (s.loc n x) = x := fun x hx => (hlu _ x hx rfl).symm
  let ρ : Representation ℂ (GAf L n) π.S :=
    { toFun := fun g => (NG.rt L n g).restrict (fun f hf => π.stable g f hf)
      map_one' := by
        apply LinearMap.ext; intro f; apply Subtype.ext; funext x
        simp [NG.rt]
      map_mul' := fun a b => by
        apply LinearMap.ext; intro f; apply Subtype.ext; funext x
        simp [NG.rt, mul_assoc] }
  have hρ : ∀ g (f : π.S), ((ρ g f : π.S) : GAf L n → ℂ) = NG.rt L n g f := fun _ _ => rfl
  have hρirr : ρ.IsIrreducible := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun P => ?_ }
    · obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne
      have h1 : (⟨g, hg⟩ : π.S) ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
      rw [← h] at h1
      exact hg0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h1))
    · have hle : P.toSubmodule.map π.S.subtype ≤ π.S := by
        rintro _ ⟨p, -, rfl⟩
        exact p.2
      have hst : ∀ h, ∀ g ∈ P.toSubmodule.map π.S.subtype, NG.rt L n h g ∈ P.toSubmodule.map π.S.subtype := by
        rintro h _ ⟨p, hp, rfl⟩
        exact ⟨ρ h p, P.apply_mem_toSubmodule h hp, rfl⟩
      rcases π.irr _ hle hst with h | h
      · left
        apply Subrepresentation.ext
        show P.toSubmodule = ⊥
        rw [eq_bot_iff]
        intro p hp
        have : (p : GAf L n → ℂ) ∈ P.toSubmodule.map π.S.subtype := ⟨p, hp, rfl⟩
        rw [h, Submodule.mem_bot] at this
        exact (Submodule.mem_bot ℂ).2 (Subtype.ext this)
      · right
        apply Subrepresentation.ext
        show P.toSubmodule = ⊤
        rw [eq_top_iff]
        intro p _
        have : (p : GAf L n → ℂ) ∈ P.toSubmodule.map π.S.subtype := by rw [h]; exact p.2
        obtain ⟨q, hq, e'⟩ := this
        rwa [show q = p from Subtype.ext e'] at hq
  let mi : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GL (Fin n) (s.w.adicCompletion L) :=
    Matrix.GeneralLinearGroup.map i.toRingHom
  have hmi : ∀ B, mi (Matrix.GeneralLinearGroup.map i.symm.toRingHom B) = B := fun B =>
    Units.ext (Matrix.ext fun a b => i.apply_symm_apply _)
  let σ : Representation ℂ (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) τ.V := τ.ρ.comp mi
  have hσirr : σ.IsIrreducible := by
    have hτ := τ.irr
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun P => ?_ }
    · obtain ⟨P1, P2, hne⟩ := hτ.exists_pair_ne
      apply hne
      have e1 : P1 = ⊥ ∨ P1 = ⊤ := hτ.eq_bot_or_eq_top P1
      have e2 : P2 = ⊥ ∨ P2 = ⊤ := hτ.eq_bot_or_eq_top P2
      have htop : (⊥ : Subrepresentation τ.ρ) = ⊤ := by
        apply Subrepresentation.ext
        have h' := congrArg Subrepresentation.toSubmodule h
        exact h'
      rcases e1 with rfl | rfl <;> rcases e2 with rfl | rfl <;> simp [htop]
    · let P' : Subrepresentation τ.ρ := ⟨P.toSubmodule, fun g v hv => by
        have := P.apply_mem_toSubmodule (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) hv
        change τ.ρ (mi _) v ∈ P.toSubmodule at this
        rwa [hmi] at this⟩
      rcases hτ.eq_bot_or_eq_top P' with h | h
      · left; apply Subrepresentation.ext; have h' := congrArg Subrepresentation.toSubmodule h; exact h'
      · right; apply Subrepresentation.ext; have h' := congrArg Subrepresentation.toSubmodule h; exact h'
  have hV : ∃ a : τ.V, a ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨P1, P2, hne⟩ := τ.irr.exists_pair_ne
    apply hne
    apply Subrepresentation.ext
    ext a
    simp [hcon a, P1.toSubmodule.zero_mem, P2.toSubmodule.zero_mem]
  let f0 : σ.IntertwiningMap (ρ.comp lh) :=
    { toLinearMap := LinearMap.codRestrict π.S T hTS
      isIntertwining' := fun A => by
        apply LinearMap.ext; intro a; apply Subtype.ext
        show T (τ.ρ (mi A) a) = NG.rt L n (lh A) (T a)
        have := hTeq (lh A) (hlift A).1 a
        rwa [show s.loc n (lh A) = A from (hlift A).2] at this }
  have hf0' : f0 ≠ 0 := by
    obtain ⟨a, ha⟩ := hV
    intro h
    apply ha
    apply hT
    have : (f0 a : GAf L n → ℂ) = 0 := by rw [h]; rfl
    simpa [f0] using this
  have hc : ∀ g, ∃ u, ∀ y, Commute ((lh u)⁻¹ * g) (lh y) := by
    intro g
    obtain ⟨x, y', hx, hy', rfl⟩ := hdec g
    refine ⟨s.loc n x, fun y => ?_⟩
    rw [hlh x hx, inv_mul_cancel_left]
    exact (hcomm _ _ (hlift y).1 hy').symm
  have hU : ∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (σ' : Representation ℂ _ W'), σ'.IsIrreducible →
      ∀ f' : σ'.IntertwiningMap (ρ.comp lh), f' ≠ 0 → Nonempty (σ.Equiv σ') := by
    intro W' _ _ σ' hσ' f' hf'
    exact (GlobalTheory.CuspRep.CompUniq.isotypic _ _ _ _ W' ρ lh σ σ' hρirr hσirr hσ' hc f0 hf0').2 f' hf'
  have hsum := (GlobalTheory.CuspRep.CompUniq.isotypic _ _ _ _ τ.V ρ lh σ σ hρirr hσirr hσirr hc f0 hf0').1
  have hfne : (⟨f, hf⟩ : π.S) ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  obtain ⟨p0, hp0⟩ := GlobalTheory.T.exists_intertwiningMap_ne_zero_of_isotypic_irreducible _ _ _ (ρ.comp lh) σ hσirr hsum hU ⟨f, hf⟩ hfne
  obtain ⟨p, hp⟩ := LinearMap.exists_extend p0.toLinearMap
  have hpS : ∀ g (hg : g ∈ π.S), p g = p0 ⟨g, hg⟩ := fun g hg => by
    have := LinearMap.congr_fun hp ⟨g, hg⟩
    exact this
  refine ⟨p, by rw [hpS f hf]; exact hp0, fun x hx f' hf' => ?_⟩
  rw [hpS _ (π.stable x f' hf'), hpS f' hf']
  have e1 : (⟨NG.rt L n x f', π.stable x f' hf'⟩ : π.S) = (ρ.comp lh) (s.loc n x) ⟨f', hf'⟩ := by
    apply Subtype.ext
    show NG.rt L n x f' = NG.rt L n (lh (s.loc n x)) f'
    rw [hlh x hx]
  rw [e1]
  exact LinearMap.congr_fun (p0.isIntertwining' (s.loc n x)) ⟨f', hf'⟩

end GlobalTheory.LocProj
