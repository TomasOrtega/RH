import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapExactMiddle

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.TopSteps

def cocExtRep {k G V W : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (Z : G → W →ₗ[k] V) (h1 : ∀ w, Z 1 w = 0)
    (hm : ∀ σ τ w, Z (σ * τ) w = ρ σ (Z τ w) + Z σ w) : Representation k G (V × W) where
  toFun σ := ((ρ σ).coprod (Z σ)).prod (LinearMap.snd k V W)
  map_one' := by
    refine LinearMap.ext fun x => ?_
    simp [h1]
  map_mul' σ τ := by
    refine LinearMap.ext fun x => ?_
    simp [hm, add_assoc]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cocExtRep_apply {k G V W : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] (ρ : Representation k G V) (Z : G → W →ₗ[k] V) (h1 : ∀ w, Z 1 w = 0)
    (hm : ∀ σ τ w, Z (σ * τ) w = ρ σ (Z τ w) + Z σ w) (σ : G) (x : V × W) :
    cocExtRep ρ Z h1 hm σ x = (ρ σ x.1 + Z σ x.2, x.2) := rfl

/- English proof (translation)
Establish `hpa : ∀ x, p (a x) = 0` using `fun x => (hx (a x)).2 ⟨x, rfl⟩`. Establish `hpσ : ∀ σ y, p (E.ρ σ y) = p y`. Introduce `σ y`. Rewrite using `[hp σ y]`. Simplify using `[chr]`.

Establish `hdec : ∀ y, ∃ x, a x = y - p y 0 • e`. Introduce `y`. Use `(hx _).1 ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i 0]`.

Simplify using `[he]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Apply `hi` to reduce the goal to its premises. Establish `h` using `hz 1`. Rewrite `h` using `[map_one]`.

Express the relevant statement in the definitionally equal form `e = e + a (z 1) at h`. Rewrite using `[map_zero]`. Combine the equalities or inequalities in the displayed calculation. Introduce `σ τ`. Apply `hi` to reduce the goal to its premises.

Establish `h1 : E.ρ (σ * τ) e = E.ρ σ (E.ρ τ e)` using `by rw [map_mul]; rfl`. Establish `key : e + a (z (σ * τ)) = e + (a (A.ρ σ (z τ)) + a (z σ))`. Rewrite using `[← hz (σ * τ), h1, hz τ, map_add, hz σ, ← ha σ (z τ)]`. Normalize the expressions using the abelian group laws. Rewrite using `[map_add]`.

Conclude with `add_left_cancel key`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective a (LinearMap.ker_eq_bot.mpr hi)`. Establish `hga : ∀ x, g (a x) = x` using `fun x => by`. Simplify using `using LinearMap.congr_fun hg x`. Take `⟨r, hr⟩ : ∃ r : (Fin E.m → k) →ₗ[k] (Fin A.m → k), ∀ y, r y = g (y - p y 0 • e)` from `⟨g ∘ₗ (LinearMap.id - ((LinearMap.proj (0 : Fin 1)).comp p).smulRight e), fun y => by simp⟩`.

Establish `har : ∀ y, a (r y) = y - p y 0 • e`. Introduce `y`. Take `⟨x, hx'⟩` from `hdec y`. Rewrite using `[hr, ← hx', hga]`. Use `⟨r, fun x => ?_, ?_, fun σ y => ?_⟩` and prove the remaining obligations.

Rewrite using `[hr, hpa]`. Simplify using `[hga]`. Rewrite using `[hr, he]`. Simplify using the standard rewrite rules. Apply `hi` to reduce the goal to its premises.

Establish `h1 : a (r (E.ρ σ y)) = E.ρ σ y - p y 0 • e` using `by rw [har, hpσ]`. Establish `h2 : a (A.ρ σ (r y) + p y 0 • z σ) = E.ρ σ y - p y 0 • e`. Rewrite using `[map_add, map_smul, ha σ (r y), har, map_sub, map_smul, hz σ, smul_add]`. Normalize the expressions using the abelian group laws. Rewrite using `[h1, h2]`.
-/
theorem ext_coords {k G : Type} [Field k] [Group G] (A E : Ob k G) (z : G → Fin A.m → k)
    (a : (Fin A.m → k) →ₗ[k] (Fin E.m → k)) (p : (Fin E.m → k) →ₗ[k] (Fin 1 → k)) (e : Fin E.m → k)
    (ha : IsHom A E a) (hp : IsHom E (chr 1) p) (hi : Function.Injective a) (hx : Function.Exact a p)
    (he : p e = fun _ => 1) (hz : ∀ σ, E.ρ σ e = e + a (z σ)) :
    z 1 = 0 ∧ (∀ σ τ, z (σ * τ) = A.ρ σ (z τ) + z σ) ∧
    ∃ r : (Fin E.m → k) →ₗ[k] (Fin A.m → k), (∀ x, r (a x) = x) ∧ r e = 0 ∧
      ∀ σ y, r (E.ρ σ y) = A.ρ σ (r y) + p y 0 • z σ := by
  have hpa : ∀ x, p (a x) = 0 := fun x => (hx (a x)).2 ⟨x, rfl⟩
  have hpσ : ∀ σ y, p (E.ρ σ y) = p y := by
    intro σ y
    rw [hp σ y]
    simp [chr]
  have hdec : ∀ y, ∃ x, a x = y - p y 0 • e := by
    intro y
    refine (hx _).1 ?_
    funext i
    rw [Subsingleton.elim i 0]
    simp [he]
  refine ⟨?_, ?_, ?_⟩
  · apply hi
    have h := hz 1
    rw [map_one] at h
    change e = e + a (z 1) at h
    rw [map_zero]
    calc a (z 1) = (e + a (z 1)) - e := by abel
      _ = 0 := by rw [← h, sub_self]
  · intro σ τ
    apply hi
    have h1 : E.ρ (σ * τ) e = E.ρ σ (E.ρ τ e) := by rw [map_mul]; rfl
    have key : e + a (z (σ * τ)) = e + (a (A.ρ σ (z τ)) + a (z σ)) := by
      rw [← hz (σ * τ), h1, hz τ, map_add, hz σ, ← ha σ (z τ)]
      abel
    rw [map_add]
    exact add_left_cancel key
  · obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective a (LinearMap.ker_eq_bot.mpr hi)
    have hga : ∀ x, g (a x) = x := fun x => by
      simpa using LinearMap.congr_fun hg x
    obtain ⟨r, hr⟩ : ∃ r : (Fin E.m → k) →ₗ[k] (Fin A.m → k), ∀ y, r y = g (y - p y 0 • e) :=
      ⟨g ∘ₗ (LinearMap.id - ((LinearMap.proj (0 : Fin 1)).comp p).smulRight e), fun y => by simp⟩
    have har : ∀ y, a (r y) = y - p y 0 • e := by
      intro y
      obtain ⟨x, hx'⟩ := hdec y
      rw [hr, ← hx', hga]
    refine ⟨r, fun x => ?_, ?_, fun σ y => ?_⟩
    · rw [hr, hpa]
      simp [hga]
    · rw [hr, he]
      simp
    · apply hi
      have h1 : a (r (E.ρ σ y)) = E.ρ σ y - p y 0 • e := by rw [har, hpσ]
      have h2 : a (A.ρ σ (r y) + p y 0 • z σ) = E.ρ σ y - p y 0 • e := by
        rw [map_add, map_smul, ha σ (r y), har, map_sub, map_smul, hz σ, smul_add]
        abel
      rw [h1, h2]

/- English proof (translation)
Take `⟨E, ι, hι⟩` from `exists_ob (cocExtRep ρ (fun σ => (LinearMap.proj (R := k) (φ := fun _ : Fin 1 => k) 0).smulRight (w σ)) (fun t => by simp [h1]) (fun σ τ t => by simp [hm, smul_add]))`. Conclude with `⟨E, ι, fun σ x t => by rw [← hι, cocExtRep_apply]; simp⟩`.
-/
private theorem exists_ob_extension_of_cocycle {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [Module.Finite k V] (ρ : Representation k G V) (w : G → V) (h1 : w 1 = 0)
    (hm : ∀ σ τ, w (σ * τ) = ρ σ (w τ) + w σ) :
    ∃ (E : Ob k G) (ι : (V × (Fin 1 → k)) ≃ₗ[k] (Fin E.m → k)),
      ∀ σ x t, E.ρ σ (ι (x, t)) = ι (ρ σ x + t 0 • w σ, t) := by
  obtain ⟨E, ι, hι⟩ := exists_ob (cocExtRep ρ
    (fun σ => (LinearMap.proj (R := k) (φ := fun _ : Fin 1 => k) 0).smulRight (w σ))
    (fun t => by simp [h1]) (fun σ τ t => by simp [hm, smul_add]))
  exact ⟨E, ι, fun σ x t => by rw [← hι, cocExtRep_apply]; simp⟩

/- English proof (translation)
Establish `h0 : IsHom A B 0`. Introduce `σ y`. Simplify using the standard rewrite rules. Simplify using `using F.map_smul A B 0 0 hA hB h0 i x`.
-/
private theorem map_zero_apply_eq_zero {k G : Type} [Field k] [Group G] {l n : ℕ} {R : RingPG k l}
    (F : DFun R n G) (A B : Ob k G) (hA : F.Obj A) (hB : F.Obj B) (i : ZMod n) (x : Vc k A.m) :
    F.map A B 0 i x = 0 := by
  have h0 : IsHom A B 0 := by
    intro σ y
    simp
  simpa using F.map_smul A B 0 0 hA hB h0 i x

/- English proof (translation)
Rewrite using `[F.map_comp A B C f g hA hB hC hf hg i]`. Both sides reduce to the same expression.
-/
private theorem map_map_eq_map_comp {k G : Type} [Field k] [Group G] {l n : ℕ} {R : RingPG k l}
    (F : DFun R n G) (A B C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k))
    (g : (Fin B.m → k) →ₗ[k] (Fin C.m → k)) (hA : F.Obj A) (hB : F.Obj B) (hC : F.Obj C)
    (hf : IsHom A B f) (hg : IsHom B C g) (i : ZMod n) (x : Vc k A.m) :
    F.map B C g i (F.map A B f i x) = F.map A C (g ∘ₗ f) i x := by
  rw [F.map_comp A B C f g hA hB hC hf hg i]
  rfl

/- English proof (translation)
Introduce `σ x`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hf σ x, hg σ (f x)]`.
-/
private theorem isHom_comp' {k G : Type} [Field k] [Group G] {A B C : Ob k G}
    {f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)} {g : (Fin B.m → k) →ₗ[k] (Fin C.m → k)}
    (hf : IsHom A B f) (hg : IsHom B C g) : IsHom A C (g ∘ₗ f) := by
  intro σ x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hf σ x, hg σ (f x)]

/- English proof (translation)
Use `(hx _).1 ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i 0]`. Simplify using `[he]`.
-/
private theorem exists_preimage_sub_smul_of_exact {k G : Type} [Field k] [Group G] (A E : Ob k G)
    (a : (Fin A.m → k) →ₗ[k] (Fin E.m → k)) (p : (Fin E.m → k) →ₗ[k] (Fin 1 → k)) (e : Fin E.m → k)
    (hx : Function.Exact a p) (he : p e = fun _ => 1) (y : Fin E.m → k) :
    ∃ x, a x = y - p y 0 • e := by
  refine (hx _).1 ?_
  funext i
  rw [Subsingleton.elim i 0]
  simp [he]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i 0, h]`.
-/
private theorem fin_one_funext_of_apply_zero_eq {k : Type} [Field k] (u v : Fin 1 → k) (h : u 0 = v 0) : u = v := by
  funext i
  rw [Subsingleton.elim i 0, h]

/- English proof (translation)
Rewrite using `[hp σ y]`. Simplify using `[chr]`.
-/
private theorem apply_rho_eq_of_isHom_trivial_character {k G : Type} [Field k] [Group G] (E : Ob k G)
    (p : (Fin E.m → k) →ₗ[k] (Fin 1 → k)) (hp : IsHom E (chr 1) p) (σ : G) (y : Fin E.m → k) :
    p (E.ρ σ y) = p y := by
  rw [hp σ y]
  simp [chr]

/- English proof (translation)
Simplify using `[chr]`.
-/
private theorem chr_one_rho_apply_eq {k G : Type} [Field k] [Group G] (σ : G) (v : Fin 1 → k) :
    (chr (1 : G →* kˣ)).ρ σ v = v := by
  simp [chr]

/- English proof (translation)
Take `⟨E, a, p, e, ε, hE, ha, hp, hai, hx, he, hz, hε⟩` from `h`. Take `⟨E', a', p', e', ε', hE', ha', hp', hai', hx', he', hz', hε'⟩` from `h'`. Take `⟨hz1, hzm, -⟩` from `ext_coords A E z a p e ha hp hai hx he hz`. Take `⟨hz1', hzm', -⟩` from `ext_coords A E' z' a' p' e' ha' hp' hai' hx' he' hz'`. Establish `hAo : F.Obj A` using `F.obj_sub A E a ha hai hE`.

Establish `h1o : F.Obj (chr 1)` using `F.obj_one`. Establish `hpσ : ∀ σ y, p (E.ρ σ y) = p y` using `apply_rho_eq_of_isHom_trivial_character E p hp`. Establish `hpσ' : ∀ σ y, p' (E'.ρ σ y) = p' y` using `apply_rho_eq_of_isHom_trivial_character E' p' hp'`. Establish `hpa : ∀ x, p (a x) = 0` using `fun x => (hx (a x)).2 ⟨x, rfl⟩`. Establish `hpa' : ∀ x, p' (a' x) = 0` using `fun x => (hx' (a' x)).2 ⟨x, rfl⟩`.

Establish `hpt : ∀ x (t : Fin 1 → k), p (a x + t 0 • e) = t` using `fun x t => fin_one_funext_of_apply_zero_eq _ _ (by simp [hpa, he])`. Establish `hpt' : ∀ x (t : Fin 1 → k), p' (a' x + t 0 • e') = t` using `fun x t => fin_one_funext_of_apply_zero_eq _ _ (by simp [hpa', he'])`. Establish `hEρ : ∀ σ x (t : Fin 1 → k), E.ρ σ (a x + t 0 • e) = a (A.ρ σ x + t 0 • z σ) + t 0 • e`. Introduce `σ x t`. Simplify using `only [map_add, map_smul, hz σ, _root_.smul_add]`.

Rewrite using `[ha σ x]`. Normalize the expressions using the abelian group laws. Establish `hEρ' : ∀ σ x (t : Fin 1 → k), E'.ρ σ (a' x + t 0 • e') = a' (A.ρ σ x + t 0 • z' σ) + t 0 • e'`. Introduce `σ x t`. Simplify using `only [map_add, map_smul, hz' σ, _root_.smul_add]`.

Rewrite using `[ha' σ x]`. Normalize the expressions using the abelian group laws. Take `⟨P, ιP, hιP⟩` from `exists_ob (E.ρ.prod E'.ρ)`. Establish `hPρ : ∀ σ y y', P.ρ σ (ιP (y, y')) = ιP (E.ρ σ y, E'.ρ σ y')`. Introduce `σ y y'`.

Rewrite using `[← hιP]`. Both sides reduce to the same expression. Take `⟨iL, hiL⟩ : ∃ f : (Fin E.m → k) →ₗ[k] (Fin P.m → k), ∀ y, f y = ιP (y, 0)` from `⟨ιP.toLinearMap ∘ₗ LinearMap.inl k _ _, fun y => rfl⟩`. Take `⟨iR, hiR⟩ : ∃ f : (Fin E'.m → k) →ₗ[k] (Fin P.m → k), ∀ y, f y = ιP (0, y)` from `⟨ιP.toLinearMap ∘ₗ LinearMap.inr k _ _, fun y => rfl⟩`. Take `⟨π1, hπ1⟩ : ∃ f : (Fin P.m → k) →ₗ[k] (Fin E.m → k), ∀ y y', f (ιP (y, y')) = y` from `⟨LinearMap.fst k _ _ ∘ₗ ιP.symm.toLinearMap, fun y y' => by simp⟩`.

Take `⟨δ, hδ⟩ : ∃ f : (Fin P.m → k) →ₗ[k] (Fin 1 → k), ∀ y y', f (ιP (y, y')) = p y - p' y'` from `⟨(p ∘ₗ LinearMap.fst k _ _ - p' ∘ₗ LinearMap.snd k _ _) ∘ₗ ιP.symm.toLinearMap, fun y y' => by simp⟩`. Take `⟨S, ιS, hιS⟩` from `exists_ob_extension_of_cocycle (A.ρ.prod A.ρ) (fun σ => (z σ, z' σ)) (by simp [hz1, hz1']) (fun σ τ => by simp [hzm, hzm'])`. Establish `hSρ : ∀ σ x x' (t : Fin 1 → k), S.ρ σ (ιS ((x, x'), t)) = ιS ((A.ρ σ x + t 0 • z σ, A.ρ σ x' + t 0 • z' σ), t)`. Introduce `σ x x' t`. Rewrite using `[hιS]`.

Both sides reduce to the same expression. Take `⟨E₂, ι₂, hι₂⟩` from `exists_ob_extension_of_cocycle A.ρ (c • z + z') (by simp [hz1, hz1']) (fun σ τ => by`. Simplify using `only [Pi.add_apply, Pi.smul_apply, hzm, hzm', map_add, map_smul, _root_.smul_add]`. Use the proof step `abel)`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ f : (Fin S.m → k) →ₗ[k] (Fin P.m → k), ∀ (x x' : Fin A.m → k) (t : Fin 1 → k), f (ιS ((x, x'), t)) = ιP (a x + t 0 • e, a' x' + t 0 • e') := by`.

Use `⟨ιP.toLinearMap ∘ₗ ((a ∘ₗ LinearMap.fst k (Fin A.m → k) (Fin A.m → k) ∘ₗ LinearMap.fst k ((Fin A.m → k) × (Fin A.m → k)) (Fin 1 → k) + ((LinearMap.proj (R := k) (φ := fun _ : Fin 1 => k) 0) ∘ₗ LinearMap.snd k ((Fin A.m → k) × (Fin A.m → k)) (Fin 1 → k)).smulRight e).prod (a' ∘ₗ L …` and prove the remaining obligations. Introduce `x x' t`. Simplify using the standard rewrite rules. Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : ∃ f : (Fin S.m → k) →ₗ[k] (Fin E₂.m → k), ∀ (x x' : Fin A.m → k) (t : Fin 1 → k), f (ιS ((x, x'), t)) = ι₂ (c • x + x', t) := by`. Use `⟨ι₂.toLinearMap ∘ₗ ((c • (LinearMap.fst k (Fin A.m → k) (Fin A.m → k) ∘ₗ LinearMap.fst k ((Fin A.m → k) × (Fin A.m → k)) (Fin 1 → k)) + LinearMap.snd k (Fin A.m → k) (Fin A.m → k) ∘ₗ LinearMap.fst k ((Fin A.m → k) × (Fin A.m → k)) (Fin 1 → k)).prod (LinearMap.snd k ((Fin A.m → k) …` and prove the remaining obligations.

Introduce `x x' t`. Simplify using the standard rewrite rules. Take `⟨αS, hαS⟩ : ∃ f : (Fin A.m → k) →ₗ[k] (Fin S.m → k), ∀ x, f x = ιS ((x, 0), 0)` from `⟨ιS.toLinearMap ∘ₗ LinearMap.inl k _ _ ∘ₗ LinearMap.inl k _ _, fun x => rfl⟩`. Take `⟨βS, hβS⟩ : ∃ f : (Fin A.m → k) →ₗ[k] (Fin S.m → k), ∀ x, f x = ιS ((0, x), 0)` from `⟨ιS.toLinearMap ∘ₗ LinearMap.inl k _ _ ∘ₗ LinearMap.inr k _ _, fun x => rfl⟩`. Take `⟨a₂, ha₂⟩ : ∃ f : (Fin A.m → k) →ₗ[k] (Fin E₂.m → k), ∀ x, f x = ι₂ (x, 0)` from `⟨ι₂.toLinearMap ∘ₗ LinearMap.inl k _ _, fun x => rfl⟩`.

Take `⟨p₂, hp₂⟩ : ∃ f : (Fin E₂.m → k) →ₗ[k] (Fin 1 → k), ∀ x t, f (ι₂ (x, t)) = t` from `⟨LinearMap.snd k _ _ ∘ₗ ι₂.symm.toLinearMap, fun x t => by simp⟩`. Establish `hiLH : IsHom E P iL`. Introduce `σ y`. Rewrite using `[hiL, hiL, hPρ, map_zero]`. Establish `hiRH : IsHom E' P iR`.

Introduce `σ y`. Rewrite using `[hiR, hiR, hPρ, map_zero]`. Establish `hπ1H : IsHom P E π1`. Introduce `σ w`. Take `⟨⟨y, y'⟩, rfl⟩` from `ιP.surjective w`.

Rewrite using `[hPρ, hπ1, hπ1]`. Establish `hδH : IsHom P (chr 1) δ`. Introduce `σ w`. Take `⟨⟨y, y'⟩, rfl⟩` from `ιP.surjective w`. Rewrite using `[hPρ, hδ, hδ, hpσ, hpσ', chr_one_rho_apply_eq]`.

Establish `hjH : IsHom S P j`. Introduce `σ s`. Take `⟨⟨⟨x, x'⟩, t⟩, rfl⟩` from `ιS.surjective s`. Rewrite using `[hSρ, hj, hj, hPρ, hEρ, hEρ']`. Establish `hqH : IsHom S E₂ q`.

Introduce `σ s`. Take `⟨⟨⟨x, x'⟩, t⟩, rfl⟩` from `ιS.surjective s`. Rewrite using `[hSρ, hq, hq, hι₂]`. Use `congr 2`. Simplify using `only [Pi.add_apply, Pi.smul_apply, map_add, map_smul, _root_.smul_add, smul_smul, mul_comm c (t 0)]`.

Normalize the expressions using the abelian group laws. Establish `hαH : IsHom A S αS`. Introduce `σ x`. Rewrite using `[hαS, hαS, hSρ]`. Simplify using the standard rewrite rules.

Establish `hβH : IsHom A S βS`. Introduce `σ x`. Rewrite using `[hβS, hβS, hSρ]`. Simplify using the standard rewrite rules. Establish `ha₂H : IsHom A E₂ a₂`.

Introduce `σ x`. Rewrite using `[ha₂, ha₂, hι₂]`. Simplify using the standard rewrite rules. Establish `hp₂H : IsHom E₂ (chr 1) p₂`. Introduce `σ w`.

Take `⟨⟨x, t⟩, rfl⟩` from `ι₂.surjective w`. Rewrite using `[hι₂, hp₂, hp₂, chr_one_rho_apply_eq]`. Establish `hPo : F.Obj P`. Use `F.obj_sum E E' P iL iR hiLH hiRH ?_ hE hE'` and prove the remaining obligations. Introduce `w`.

Take `⟨⟨y, y'⟩, rfl⟩` from `ιP.surjective w`. Use `⟨(y, y'), ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.coprod_apply, hiL, hiR, ← map_add, Prod.mk_add_mk, add_zero, zero_add]`. Establish `hjinj : Function.Injective j`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `s hs`. Take `⟨⟨⟨x, x'⟩, t⟩, rfl⟩` from `ιS.surjective s`. Rewrite `hs` using `[hj]`. Establish `hs'` using `ιP.injective (hs.trans (map_zero ιP).symm)`. Establish `h1 : a x + t 0 • e = 0` using `by simpa using congrArg Prod.fst hs'`.

Establish `h2 : a' x' + t 0 • e' = 0` using `by simpa using congrArg Prod.snd hs'`. Establish `ht : t = 0`. Combine the equalities or inequalities in the displayed calculation. Substitute `ht` using the available equality. Establish `hx0 : x = 0` using `hai (by simpa using h1)`.

Establish `hx0' : x' = 0` using `hai' (by simpa using h2)`. Substitute `hx0 hx0'` using the available equality. Simplify using the standard rewrite rules. Establish `hjδ : Function.Exact j δ`. Introduce `w`.

Take `⟨⟨y, y'⟩, rfl⟩` from `ιP.surjective w`. Rewrite using `[hδ, sub_eq_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `hyy`. Take `⟨x, hx1⟩` from `exists_preimage_sub_smul_of_exact A E a p e hx he y`.

Take `⟨x', hx1'⟩` from `exists_preimage_sub_smul_of_exact A E' a' p' e' hx' he' y'`. Use `⟨ιS ((x, x'), p y), ?_⟩` and prove the remaining obligations. Rewrite using `[hj, hx1, hx1', hyy]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨s, hs⟩`.

Take `⟨⟨⟨x, x'⟩, t⟩, rfl⟩` from `ιS.surjective s`. Rewrite `hs` using `[hj]`. Take `⟨hs1, hs2⟩` from `Prod.mk.inj (ιP.injective hs)`. Rewrite using `[← hs1, ← hs2, hpt, hpt']`. Establish `hδsurj : Function.Surjective δ`.

Introduce `v`. Use `⟨ιP (v 0 • e, 0), ?_⟩` and prove the remaining obligations. Rewrite using `[hδ, map_zero, sub_zero, map_smul, he]`. Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i 0]`.

Simplify using the standard rewrite rules. Establish `hqsurj : Function.Surjective q`. Introduce `w`. Take `⟨⟨x, t⟩, rfl⟩` from `ι₂.surjective w`. Conclude with `⟨ιS ((0, x), t), by rw [hq, smul_zero, zero_add]⟩`.

Establish `hSo : F.Obj S` using `F.obj_sub S P j hjH hjinj hPo`. Establish `hE₂o : F.Obj E₂` using `F.obj_quot S E₂ q hqH hqsurj hSo`. Establish `ha₂inj : Function.Injective a₂`. Introduce `x y hxy`. Rewrite `hxy` using `[ha₂, ha₂]`.

Conclude with `(Prod.mk.inj (ι₂.injective hxy)).1`. Establish `ha₂ex : Function.Exact a₂ p₂`. Introduce `w`. Take `⟨⟨x, t⟩, rfl⟩` from `ι₂.surjective w`. Rewrite using `[hp₂]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `⟨x, ha₂ x⟩`. Introduce and unpack `⟨y, hy⟩`. Rewrite `hy` using `[ha₂]`.

Conclude with `(Prod.mk.inj (ι₂.injective hy)).2.symm`. Establish `hρe : ∀ σ, E₂.ρ σ (ι₂ (0, fun _ => 1)) = ι₂ (0, fun _ => 1) + a₂ ((c • z + z') σ)`. Introduce `σ`. Rewrite using `[hι₂, ha₂, ← map_add]`. Simplify using the standard rewrite rules.

Establish `hX : ∀ i, F.map P (chr 1) δ i (F.map E P iL i (ε i) + F.map E' P iR i (ε' i)) = 0`. Introduce `i`. Establish `hδl : δ ∘ₗ iL = p` using `LinearMap.ext fun y => by`. Rewrite using `[LinearMap.comp_apply, hiL, hδ, map_zero, sub_zero]`. Establish `hδr : δ ∘ₗ iR = (-1 : k) • p'` using `LinearMap.ext fun y => by`.

Rewrite using `[LinearMap.comp_apply, hiR, hδ, map_zero, zero_sub, LinearMap.smul_apply, neg_one_smul]`. Rewrite using `[map_add, map_map_eq_map_comp F E P (chr 1) iL δ hE hPo h1o hiLH hδH, map_map_eq_map_comp F E' P (chr 1) iR δ hE' hPo h1o hiRH hδH, hδl, hδr, F.map_smul E' (chr 1) p' (-1) hE' h1o hp', (hε i).1, (hε' i).1]`. Simplify using the standard rewrite rules. Establish `hlift : ∀ i, ∃ s, F.map S P j i s = F.map E P iL i (ε i) + F.map E' P iR i (ε' i)` using `fun i => (DFun.map_exact_middle F S P (chr 1) j δ hPo hjH hδH hjinj hδsurj hjδ i _).1 (hX i)`. Use `choose εS hεS using hlift`.

Establish `hjα : j ∘ₗ αS = iL ∘ₗ a` using `LinearMap.ext fun x => by`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hαS, hj, hiL]`. Simplify using the standard rewrite rules. Establish `hjβ : j ∘ₗ βS = iR ∘ₗ a'` using `LinearMap.ext fun x => by`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hβS, hj, hiR]`.

Simplify using the standard rewrite rules. Establish `hqα : q ∘ₗ αS = c • a₂` using `LinearMap.ext fun x => by`. Rewrite using `[LinearMap.comp_apply, hαS, hq, LinearMap.smul_apply, ha₂, ← map_smul]`. Simplify using the standard rewrite rules. Establish `hqβ : q ∘ₗ βS = a₂` using `LinearMap.ext fun x => by`.

Rewrite using `[LinearMap.comp_apply, hβS, hq, ha₂, smul_zero, zero_add]`. Establish `hπl : π1 ∘ₗ iL = LinearMap.id` using `LinearMap.ext fun y => by`. Rewrite using `[LinearMap.comp_apply, hiL, hπ1, LinearMap.id_apply]`. Establish `hπr : π1 ∘ₗ iR = 0` using `LinearMap.ext fun y => by`. Rewrite using `[LinearMap.comp_apply, hiR, hπ1, LinearMap.zero_apply]`.

Establish `hpq : p₂ ∘ₗ q = p ∘ₗ (π1 ∘ₗ j)` using `LinearMap.ext fun s => by`. Take `⟨⟨⟨x, x'⟩, t⟩, rfl⟩` from `ιS.surjective s`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, hq, hp₂, hj, hπ1, hpt]`. Establish `rhsφ : ∀ i, F.map S P j i (F.map A S αS i (b i) + F.map A S βS i (b' i)) = F.map E P iL i (F.map A E a i (b i)) + F.map E' P iR i (F.map A E' a' i (b' i))`. Introduce `i`.

Rewrite using `[map_add, map_map_eq_map_comp F A S P αS j hAo hSo hPo hαH hjH, map_map_eq_map_comp F A S P βS j hAo hSo hPo hβH hjH, hjα, hjβ, map_map_eq_map_comp F A E P a iL hAo hE hPo ha hiLH, map_map_eq_map_comp F A E' P a' iR hAo hE' hPo ha' hiRH]`. Establish `rhsγ : ∀ i, F.map S P j i (F.map A S αS i (g i) + F.map A S βS i (g' i)) = F.map E P iL i (F.map A E a i (g i)) + F.map E' P iR i (F.map A E' a' i (g' i))`. Introduce `i`. Rewrite using `[map_add, map_map_eq_map_comp F A S P αS j hAo hSo hPo hαH hjH, map_map_eq_map_comp F A S P βS j hAo hSo hPo hβH hjH, hjα, hjβ, map_map_eq_map_comp F A E P a iL hAo hE hPo ha hiLH, map_map_eq_map_comp F A E' P a' iR hAo hE' hPo ha' hiRH]`. Establish `hSφ : ∀ i, (F.D S).φ i (εS (i - 1)) - εS i = F.map A S αS i (b i) + F.map A S βS i (b' i)`.

Introduce `i`. Apply `F.map_inj S P j hSo hPo hjH hjinj i` to reduce the goal to its premises. Rewrite using `[map_sub, F.map_φ S P j hSo hPo hjH, hεS, hεS, rhsφ, map_add, (hε i).2.1, (hε' i).2.1, map_sub, map_sub, F.map_φ E P iL hE hPo hiLH, F.map_φ E' P iR hE' hPo hiRH]`. Normalize the expressions using the abelian group laws. Establish `hSγ : ∀ i, (F.D S).γ i (εS i) - εS i = F.map A S αS i (g i) + F.map A S βS i (g' i)`.

Introduce `i`. Apply `F.map_inj S P j hSo hPo hjH hjinj i` to reduce the goal to its premises. Rewrite using `[map_sub, F.map_γ S P j hSo hPo hjH, hεS, rhsγ, map_add, (hε i).2.2, (hε' i).2.2, map_sub, map_sub, F.map_γ E P iL hE hPo hiLH, F.map_γ E' P iR hE' hPo hiRH]`. Normalize the expressions using the abelian group laws. Use `⟨E₂, a₂, p₂, ι₂ (0, fun _ => 1), fun i => F.map S E₂ q i (εS i), hE₂o, ha₂H, hp₂H, ha₂inj, ha₂ex, hp₂ _ _, hρe, fun i => ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations.

Simplify using `only`. Rewrite using `[map_map_eq_map_comp F S E₂ (chr 1) q p₂ hSo hE₂o h1o hqH hp₂H, hpq, ← map_map_eq_map_comp F S E (chr 1) (π1 ∘ₗ j) p hSo hE h1o (isHom_comp' hjH hπ1H) hp, ← map_map_eq_map_comp F S P E j π1 hSo hPo hE hjH hπ1H, hεS, map_add, map_map_eq_map_comp F E P E iL π1 hE hPo hE hiLH hπ1H, …`. Simplify using `only`. Establish `h` using `congrArg (F.map S E₂ q i) (hSφ i)`. Rewrite `h` using `[map_sub, F.map_φ S E₂ q hSo hE₂o hqH, map_add, map_map_eq_map_comp F A S E₂ αS q hAo hSo hE₂o hαH hqH, map_map_eq_map_comp F A S E₂ βS q hAo hSo hE₂o hβH hqH, hqα, hqβ, F.map_smul A E₂ a₂ c hAo hE₂o ha₂H]`.

Rewrite using `[h, Pi.add_apply, Pi.smul_apply, map_add, LinearMap.map_smul_of_tower]`. Simplify using `only`. Establish `h` using `congrArg (F.map S E₂ q i) (hSγ i)`. Rewrite `h` using `[map_sub, F.map_γ S E₂ q hSo hE₂o hqH, map_add, map_map_eq_map_comp F A S E₂ αS q hAo hSo hE₂o hαH hqH, map_map_eq_map_comp F A S E₂ βS q hAo hSo hE₂o hβH hqH, hqα, hqβ, F.map_smul A E₂ a₂ c hAo hE₂o ha₂H]`. Rewrite using `[h, Pi.add_apply, Pi.smul_apply, map_add, LinearMap.map_smul_of_tower]`.
-/
theorem Repr.smul_add {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) (A : Ob k G) (c : k) (z z' : G → Fin A.m → k)
    (b g b' g' : ZMod n → Vc k A.m) (h : Repr F A z b g) (h' : Repr F A z' b' g') :
    Repr F A (c • z + z') (c • b + b') (c • g + g') := by
  obtain ⟨E, a, p, e, ε, hE, ha, hp, hai, hx, he, hz, hε⟩ := h
  obtain ⟨E', a', p', e', ε', hE', ha', hp', hai', hx', he', hz', hε'⟩ := h'
  obtain ⟨hz1, hzm, -⟩ := ext_coords A E z a p e ha hp hai hx he hz
  obtain ⟨hz1', hzm', -⟩ := ext_coords A E' z' a' p' e' ha' hp' hai' hx' he' hz'
  have hAo : F.Obj A := F.obj_sub A E a ha hai hE
  have h1o : F.Obj (chr 1) := F.obj_one
  have hpσ : ∀ σ y, p (E.ρ σ y) = p y := apply_rho_eq_of_isHom_trivial_character E p hp
  have hpσ' : ∀ σ y, p' (E'.ρ σ y) = p' y := apply_rho_eq_of_isHom_trivial_character E' p' hp'
  have hpa : ∀ x, p (a x) = 0 := fun x => (hx (a x)).2 ⟨x, rfl⟩
  have hpa' : ∀ x, p' (a' x) = 0 := fun x => (hx' (a' x)).2 ⟨x, rfl⟩
  have hpt : ∀ x (t : Fin 1 → k), p (a x + t 0 • e) = t := fun x t =>
    fin_one_funext_of_apply_zero_eq _ _ (by simp [hpa, he])
  have hpt' : ∀ x (t : Fin 1 → k), p' (a' x + t 0 • e') = t := fun x t =>
    fin_one_funext_of_apply_zero_eq _ _ (by simp [hpa', he'])
  have hEρ : ∀ σ x (t : Fin 1 → k), E.ρ σ (a x + t 0 • e) = a (A.ρ σ x + t 0 • z σ) + t 0 • e := by
    intro σ x t
    simp only [map_add, map_smul, hz σ, _root_.smul_add]
    rw [ha σ x]
    abel
  have hEρ' : ∀ σ x (t : Fin 1 → k), E'.ρ σ (a' x + t 0 • e') = a' (A.ρ σ x + t 0 • z' σ) + t 0 • e' := by
    intro σ x t
    simp only [map_add, map_smul, hz' σ, _root_.smul_add]
    rw [ha' σ x]
    abel
  obtain ⟨P, ιP, hιP⟩ := exists_ob (E.ρ.prod E'.ρ)
  have hPρ : ∀ σ y y', P.ρ σ (ιP (y, y')) = ιP (E.ρ σ y, E'.ρ σ y') := by
    intro σ y y'
    rw [← hιP]
    rfl
  obtain ⟨iL, hiL⟩ : ∃ f : (Fin E.m → k) →ₗ[k] (Fin P.m → k), ∀ y, f y = ιP (y, 0) :=
    ⟨ιP.toLinearMap ∘ₗ LinearMap.inl k _ _, fun y => rfl⟩
  obtain ⟨iR, hiR⟩ : ∃ f : (Fin E'.m → k) →ₗ[k] (Fin P.m → k), ∀ y, f y = ιP (0, y) :=
    ⟨ιP.toLinearMap ∘ₗ LinearMap.inr k _ _, fun y => rfl⟩
  obtain ⟨π1, hπ1⟩ : ∃ f : (Fin P.m → k) →ₗ[k] (Fin E.m → k), ∀ y y', f (ιP (y, y')) = y :=
    ⟨LinearMap.fst k _ _ ∘ₗ ιP.symm.toLinearMap, fun y y' => by simp⟩
  obtain ⟨δ, hδ⟩ : ∃ f : (Fin P.m → k) →ₗ[k] (Fin 1 → k), ∀ y y', f (ιP (y, y')) = p y - p' y' :=
    ⟨(p ∘ₗ LinearMap.fst k _ _ - p' ∘ₗ LinearMap.snd k _ _) ∘ₗ ιP.symm.toLinearMap, fun y y' => by simp⟩
  obtain ⟨S, ιS, hιS⟩ := exists_ob_extension_of_cocycle (A.ρ.prod A.ρ) (fun σ => (z σ, z' σ))
    (by simp [hz1, hz1']) (fun σ τ => by simp [hzm, hzm'])
  have hSρ : ∀ σ x x' (t : Fin 1 → k), S.ρ σ (ιS ((x, x'), t)) =
      ιS ((A.ρ σ x + t 0 • z σ, A.ρ σ x' + t 0 • z' σ), t) := by
    intro σ x x' t
    rw [hιS]
    rfl
  obtain ⟨E₂, ι₂, hι₂⟩ := exists_ob_extension_of_cocycle A.ρ (c • z + z') (by simp [hz1, hz1'])
    (fun σ τ => by
      simp only [Pi.add_apply, Pi.smul_apply, hzm, hzm', map_add, map_smul, _root_.smul_add]
      abel)
  obtain ⟨j, hj⟩ : ∃ f : (Fin S.m → k) →ₗ[k] (Fin P.m → k), ∀ (x x' : Fin A.m → k) (t : Fin 1 → k),
      f (ιS ((x, x'), t)) = ιP (a x + t 0 • e, a' x' + t 0 • e') := by
    refine ⟨ιP.toLinearMap ∘ₗ
      ((a ∘ₗ LinearMap.fst k (Fin A.m → k) (Fin A.m → k) ∘ₗ
            LinearMap.fst k ((Fin A.m → k) × (Fin A.m → k)) (Fin 1 → k) +
          ((LinearMap.proj (R := k) (φ := fun _ : Fin 1 => k) 0) ∘ₗ
            LinearMap.snd k ((Fin A.m → k) × (Fin A.m → k)) (Fin 1 → k)).smulRight e).prod
        (a' ∘ₗ LinearMap.snd k (Fin A.m → k) (Fin A.m → k) ∘ₗ
            LinearMap.fst k ((Fin A.m → k) × (Fin A.m → k)) (Fin 1 → k) +
          ((LinearMap.proj (R := k) (φ := fun _ : Fin 1 => k) 0) ∘ₗ
            LinearMap.snd k ((Fin A.m → k) × (Fin A.m → k)) (Fin 1 → k)).smulRight e')) ∘ₗ
      ιS.symm.toLinearMap, ?_⟩
    intro x x' t
    simp
  obtain ⟨q, hq⟩ : ∃ f : (Fin S.m → k) →ₗ[k] (Fin E₂.m → k), ∀ (x x' : Fin A.m → k) (t : Fin 1 → k),
      f (ιS ((x, x'), t)) = ι₂ (c • x + x', t) := by
    refine ⟨ι₂.toLinearMap ∘ₗ
      ((c • (LinearMap.fst k (Fin A.m → k) (Fin A.m → k) ∘ₗ
            LinearMap.fst k ((Fin A.m → k) × (Fin A.m → k)) (Fin 1 → k)) +
          LinearMap.snd k (Fin A.m → k) (Fin A.m → k) ∘ₗ
            LinearMap.fst k ((Fin A.m → k) × (Fin A.m → k)) (Fin 1 → k)).prod
        (LinearMap.snd k ((Fin A.m → k) × (Fin A.m → k)) (Fin 1 → k))) ∘ₗ ιS.symm.toLinearMap, ?_⟩
    intro x x' t
    simp
  obtain ⟨αS, hαS⟩ : ∃ f : (Fin A.m → k) →ₗ[k] (Fin S.m → k), ∀ x, f x = ιS ((x, 0), 0) :=
    ⟨ιS.toLinearMap ∘ₗ LinearMap.inl k _ _ ∘ₗ LinearMap.inl k _ _, fun x => rfl⟩
  obtain ⟨βS, hβS⟩ : ∃ f : (Fin A.m → k) →ₗ[k] (Fin S.m → k), ∀ x, f x = ιS ((0, x), 0) :=
    ⟨ιS.toLinearMap ∘ₗ LinearMap.inl k _ _ ∘ₗ LinearMap.inr k _ _, fun x => rfl⟩
  obtain ⟨a₂, ha₂⟩ : ∃ f : (Fin A.m → k) →ₗ[k] (Fin E₂.m → k), ∀ x, f x = ι₂ (x, 0) :=
    ⟨ι₂.toLinearMap ∘ₗ LinearMap.inl k _ _, fun x => rfl⟩
  obtain ⟨p₂, hp₂⟩ : ∃ f : (Fin E₂.m → k) →ₗ[k] (Fin 1 → k), ∀ x t, f (ι₂ (x, t)) = t :=
    ⟨LinearMap.snd k _ _ ∘ₗ ι₂.symm.toLinearMap, fun x t => by simp⟩
  have hiLH : IsHom E P iL := by
    intro σ y
    rw [hiL, hiL, hPρ, map_zero]
  have hiRH : IsHom E' P iR := by
    intro σ y
    rw [hiR, hiR, hPρ, map_zero]
  have hπ1H : IsHom P E π1 := by
    intro σ w
    obtain ⟨⟨y, y'⟩, rfl⟩ := ιP.surjective w
    rw [hPρ, hπ1, hπ1]
  have hδH : IsHom P (chr 1) δ := by
    intro σ w
    obtain ⟨⟨y, y'⟩, rfl⟩ := ιP.surjective w
    rw [hPρ, hδ, hδ, hpσ, hpσ', chr_one_rho_apply_eq]
  have hjH : IsHom S P j := by
    intro σ s
    obtain ⟨⟨⟨x, x'⟩, t⟩, rfl⟩ := ιS.surjective s
    rw [hSρ, hj, hj, hPρ, hEρ, hEρ']
  have hqH : IsHom S E₂ q := by
    intro σ s
    obtain ⟨⟨⟨x, x'⟩, t⟩, rfl⟩ := ιS.surjective s
    rw [hSρ, hq, hq, hι₂]
    congr 2
    simp only [Pi.add_apply, Pi.smul_apply, map_add, map_smul, _root_.smul_add, smul_smul, mul_comm c (t 0)]
    abel
  have hαH : IsHom A S αS := by
    intro σ x
    rw [hαS, hαS, hSρ]
    simp
  have hβH : IsHom A S βS := by
    intro σ x
    rw [hβS, hβS, hSρ]
    simp
  have ha₂H : IsHom A E₂ a₂ := by
    intro σ x
    rw [ha₂, ha₂, hι₂]
    simp
  have hp₂H : IsHom E₂ (chr 1) p₂ := by
    intro σ w
    obtain ⟨⟨x, t⟩, rfl⟩ := ι₂.surjective w
    rw [hι₂, hp₂, hp₂, chr_one_rho_apply_eq]
  have hPo : F.Obj P := by
    refine F.obj_sum E E' P iL iR hiLH hiRH ?_ hE hE'
    intro w
    obtain ⟨⟨y, y'⟩, rfl⟩ := ιP.surjective w
    refine ⟨(y, y'), ?_⟩
    rw [LinearMap.coprod_apply, hiL, hiR, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have hjinj : Function.Injective j := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    obtain ⟨⟨⟨x, x'⟩, t⟩, rfl⟩ := ιS.surjective s
    rw [hj] at hs
    have hs' := ιP.injective (hs.trans (map_zero ιP).symm)
    have h1 : a x + t 0 • e = 0 := by simpa using congrArg Prod.fst hs'
    have h2 : a' x' + t 0 • e' = 0 := by simpa using congrArg Prod.snd hs'
    have ht : t = 0 := by
      calc t = p (a x + t 0 • e) := (hpt x t).symm
        _ = 0 := by rw [h1, map_zero]
    subst ht
    have hx0 : x = 0 := hai (by simpa using h1)
    have hx0' : x' = 0 := hai' (by simpa using h2)
    subst hx0 hx0'
    simp
  have hjδ : Function.Exact j δ := by
    intro w
    obtain ⟨⟨y, y'⟩, rfl⟩ := ιP.surjective w
    rw [hδ, sub_eq_zero]
    constructor
    · intro hyy
      obtain ⟨x, hx1⟩ := exists_preimage_sub_smul_of_exact A E a p e hx he y
      obtain ⟨x', hx1'⟩ := exists_preimage_sub_smul_of_exact A E' a' p' e' hx' he' y'
      refine ⟨ιS ((x, x'), p y), ?_⟩
      rw [hj, hx1, hx1', hyy]
      simp
    · rintro ⟨s, hs⟩
      obtain ⟨⟨⟨x, x'⟩, t⟩, rfl⟩ := ιS.surjective s
      rw [hj] at hs
      obtain ⟨hs1, hs2⟩ := Prod.mk.inj (ιP.injective hs)
      rw [← hs1, ← hs2, hpt, hpt']
  have hδsurj : Function.Surjective δ := by
    intro v
    refine ⟨ιP (v 0 • e, 0), ?_⟩
    rw [hδ, map_zero, sub_zero, map_smul, he]
    funext i
    rw [Subsingleton.elim i 0]
    simp
  have hqsurj : Function.Surjective q := by
    intro w
    obtain ⟨⟨x, t⟩, rfl⟩ := ι₂.surjective w
    exact ⟨ιS ((0, x), t), by rw [hq, smul_zero, zero_add]⟩
  have hSo : F.Obj S := F.obj_sub S P j hjH hjinj hPo
  have hE₂o : F.Obj E₂ := F.obj_quot S E₂ q hqH hqsurj hSo
  have ha₂inj : Function.Injective a₂ := by
    intro x y hxy
    rw [ha₂, ha₂] at hxy
    exact (Prod.mk.inj (ι₂.injective hxy)).1
  have ha₂ex : Function.Exact a₂ p₂ := by
    intro w
    obtain ⟨⟨x, t⟩, rfl⟩ := ι₂.surjective w
    rw [hp₂]
    constructor
    · rintro rfl
      exact ⟨x, ha₂ x⟩
    · rintro ⟨y, hy⟩
      rw [ha₂] at hy
      exact (Prod.mk.inj (ι₂.injective hy)).2.symm
  have hρe : ∀ σ, E₂.ρ σ (ι₂ (0, fun _ => 1)) = ι₂ (0, fun _ => 1) + a₂ ((c • z + z') σ) := by
    intro σ
    rw [hι₂, ha₂, ← map_add]
    simp
  have hX : ∀ i, F.map P (chr 1) δ i (F.map E P iL i (ε i) + F.map E' P iR i (ε' i)) = 0 := by
    intro i
    have hδl : δ ∘ₗ iL = p := LinearMap.ext fun y => by
      rw [LinearMap.comp_apply, hiL, hδ, map_zero, sub_zero]
    have hδr : δ ∘ₗ iR = (-1 : k) • p' := LinearMap.ext fun y => by
      rw [LinearMap.comp_apply, hiR, hδ, map_zero, zero_sub, LinearMap.smul_apply, neg_one_smul]
    rw [map_add, map_map_eq_map_comp F E P (chr 1) iL δ hE hPo h1o hiLH hδH,
      map_map_eq_map_comp F E' P (chr 1) iR δ hE' hPo h1o hiRH hδH, hδl, hδr,
      F.map_smul E' (chr 1) p' (-1) hE' h1o hp', (hε i).1, (hε' i).1]
    simp
  have hlift : ∀ i, ∃ s, F.map S P j i s = F.map E P iL i (ε i) + F.map E' P iR i (ε' i) :=
    fun i => (DFun.map_exact_middle F S P (chr 1) j δ hPo hjH hδH hjinj hδsurj hjδ i _).1 (hX i)
  choose εS hεS using hlift
  have hjα : j ∘ₗ αS = iL ∘ₗ a := LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hαS, hj, hiL]
    simp
  have hjβ : j ∘ₗ βS = iR ∘ₗ a' := LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hβS, hj, hiR]
    simp
  have hqα : q ∘ₗ αS = c • a₂ := LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, hαS, hq, LinearMap.smul_apply, ha₂, ← map_smul]
    simp
  have hqβ : q ∘ₗ βS = a₂ := LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, hβS, hq, ha₂, smul_zero, zero_add]
  have hπl : π1 ∘ₗ iL = LinearMap.id := LinearMap.ext fun y => by
    rw [LinearMap.comp_apply, hiL, hπ1, LinearMap.id_apply]
  have hπr : π1 ∘ₗ iR = 0 := LinearMap.ext fun y => by
    rw [LinearMap.comp_apply, hiR, hπ1, LinearMap.zero_apply]
  have hpq : p₂ ∘ₗ q = p ∘ₗ (π1 ∘ₗ j) := LinearMap.ext fun s => by
    obtain ⟨⟨⟨x, x'⟩, t⟩, rfl⟩ := ιS.surjective s
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, hq, hp₂, hj, hπ1, hpt]
  have rhsφ : ∀ i, F.map S P j i (F.map A S αS i (b i) + F.map A S βS i (b' i)) =
      F.map E P iL i (F.map A E a i (b i)) + F.map E' P iR i (F.map A E' a' i (b' i)) := by
    intro i
    rw [map_add, map_map_eq_map_comp F A S P αS j hAo hSo hPo hαH hjH, map_map_eq_map_comp F A S P βS j hAo hSo hPo hβH hjH,
      hjα, hjβ, map_map_eq_map_comp F A E P a iL hAo hE hPo ha hiLH, map_map_eq_map_comp F A E' P a' iR hAo hE' hPo ha' hiRH]
  have rhsγ : ∀ i, F.map S P j i (F.map A S αS i (g i) + F.map A S βS i (g' i)) =
      F.map E P iL i (F.map A E a i (g i)) + F.map E' P iR i (F.map A E' a' i (g' i)) := by
    intro i
    rw [map_add, map_map_eq_map_comp F A S P αS j hAo hSo hPo hαH hjH, map_map_eq_map_comp F A S P βS j hAo hSo hPo hβH hjH,
      hjα, hjβ, map_map_eq_map_comp F A E P a iL hAo hE hPo ha hiLH, map_map_eq_map_comp F A E' P a' iR hAo hE' hPo ha' hiRH]
  have hSφ : ∀ i, (F.D S).φ i (εS (i - 1)) - εS i = F.map A S αS i (b i) + F.map A S βS i (b' i) := by
    intro i
    apply F.map_inj S P j hSo hPo hjH hjinj i
    rw [map_sub, F.map_φ S P j hSo hPo hjH, hεS, hεS, rhsφ, map_add, (hε i).2.1, (hε' i).2.1, map_sub, map_sub,
      F.map_φ E P iL hE hPo hiLH, F.map_φ E' P iR hE' hPo hiRH]
    abel
  have hSγ : ∀ i, (F.D S).γ i (εS i) - εS i = F.map A S αS i (g i) + F.map A S βS i (g' i) := by
    intro i
    apply F.map_inj S P j hSo hPo hjH hjinj i
    rw [map_sub, F.map_γ S P j hSo hPo hjH, hεS, rhsγ, map_add, (hε i).2.2, (hε' i).2.2, map_sub, map_sub,
      F.map_γ E P iL hE hPo hiLH, F.map_γ E' P iR hE' hPo hiRH]
    abel
  refine ⟨E₂, a₂, p₂, ι₂ (0, fun _ => 1), fun i => F.map S E₂ q i (εS i), hE₂o, ha₂H, hp₂H, ha₂inj,
    ha₂ex, hp₂ _ _, hρe, fun i => ⟨?_, ?_, ?_⟩⟩
  · dsimp only
    rw [map_map_eq_map_comp F S E₂ (chr 1) q p₂ hSo hE₂o h1o hqH hp₂H, hpq,
      ← map_map_eq_map_comp F S E (chr 1) (π1 ∘ₗ j) p hSo hE h1o (isHom_comp' hjH hπ1H) hp,
      ← map_map_eq_map_comp F S P E j π1 hSo hPo hE hjH hπ1H, hεS, map_add,
      map_map_eq_map_comp F E P E iL π1 hE hPo hE hiLH hπ1H, map_map_eq_map_comp F E' P E iR π1 hE' hPo hE hiRH hπ1H,
      hπl, hπr, F.map_id E hE i, map_zero_apply_eq_zero F E' E hE' hE, LinearMap.id_apply, add_zero, (hε i).1]
  · dsimp only
    have h := congrArg (F.map S E₂ q i) (hSφ i)
    rw [map_sub, F.map_φ S E₂ q hSo hE₂o hqH, map_add, map_map_eq_map_comp F A S E₂ αS q hAo hSo hE₂o hαH hqH,
      map_map_eq_map_comp F A S E₂ βS q hAo hSo hE₂o hβH hqH, hqα, hqβ, F.map_smul A E₂ a₂ c hAo hE₂o ha₂H] at h
    rw [h, Pi.add_apply, Pi.smul_apply, map_add, LinearMap.map_smul_of_tower]
  · dsimp only
    have h := congrArg (F.map S E₂ q i) (hSγ i)
    rw [map_sub, F.map_γ S E₂ q hSo hE₂o hqH, map_add, map_map_eq_map_comp F A S E₂ αS q hAo hSo hE₂o hαH hqH,
      map_map_eq_map_comp F A S E₂ βS q hAo hSo hE₂o hβH hqH, hqα, hqβ, F.map_smul A E₂ a₂ c hAo hE₂o ha₂H] at h
    rw [h, Pi.add_apply, Pi.smul_apply, map_add, LinearMap.map_smul_of_tower]

end GlobalTheory.TopSteps
